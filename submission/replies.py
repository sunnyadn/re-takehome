"""Reading one model reply: what it said, what of that is a Lean step, and
the cheaper forms of a step it wrote too heavy."""

from __future__ import annotations
import json
import re
import textwrap
from typing import Any, Sequence
from submission.contract import strip_fences
from submission.framework import declaration_name, normalise_steps


# Measured on p10: a model that reasons returns its draft inside `<think>`
# tags, and the ten `#eval` lines it tried there are not its answer.
THINKING = re.compile(r"<think>.*?(?:</think>|\Z)", re.S | re.I)


# Measured twice, and the second measurement is the one that counts: asking
# OpenRouter directly, qwen honours a forced tool call and gpt-oss ignores it
# without error, but the same request through the harness answers HTTP 404,
# `no endpoints found that support the provided tool_choice`, which marks the
# budget incomplete and ends the problem. A tool call is read if one arrives
# and never asked for.
def tool_lines(calls: Sequence[Any]) -> str:
    """The strings a tool call carried, if the model made one."""

    for call in calls or ():
        body = (call or {}).get("function", {}).get("arguments")
        try:
            fields = json.loads(body) if isinstance(body, str) else body
        except ValueError:
            continue
        for value in (fields or {}).values():
            if isinstance(value, list) and all(isinstance(v, str) for v in value):
                return "\n".join(value)
    return ""


def spoken(reply: str) -> str:
    """What the model said, without the thinking it said it in."""

    return THINKING.sub("", reply).strip()


BUDGET_RETRY = "__budget__"


def is_probe(block: str) -> bool:
    """A reply that only computes something is a probe, not a step."""

    lines = [l for l in block.splitlines() if l.strip()]
    return bool(lines) and all(l.strip().startswith(("#eval", "#check", "#print"))
                               for l in lines)


# A step is tactic text, except a whole auxiliary declaration, which §4 allows
# and which is the only way to state a fact two theorems share.
STEP_BAN = re.compile(r"^\s*(import|example|axiom)\b|```|native_decide|admit", re.M)


# Measured: `#eval (List.range 100).find? p` prints `some 19`, which is the
# right answer computed the right way and was being discarded as not a numeral.
PRINTED = re.compile(r"\A(?:Option\.)?some\s+(-?\d+)\Z|\A(-?\d+)\Z")


def printed_numbers(messages: Sequence[Any]) -> list[str]:
    """What `#eval` printed, in order, as numbers."""

    out = []
    for m in messages:
        if isinstance(m, dict) and m.get("severity") in ("info", "information"):
            found = PRINTED.match(str(m.get("data", "")).strip())
            if found:
                out.append(found.group(1) or found.group(2))
    return out


FENCED = re.compile(r"```(?:lean4?)?\s*\n(.*?)```", re.DOTALL | re.IGNORECASE)


# What a Lean tactic line can start with. Measured on p08: qwen answers in
# prose as often as in Lean, and prose spliced into the file is a wasted check.
OPENERS = (
    "have", "let", "set", "show", "intro", "intros", "induction", "cases",
    "rcases", "obtain", "refine", "exact", "apply", "constructor", "use",
    "rfl", "simp", "simp_all", "simp_only", "norm_num", "norm_cast", "push_cast",
    "omega", "decide", "linarith", "nlinarith", "positivity", "polyrith", "ring",
    "ring_nf", "field_simp", "gcongr", "bound", "aesop", "tauto", "trivial",
    "interval_cases", "by_contra", "push_neg", "rw", "rwa", "subst", "subst_vars",
    "unfold", "calc", "left", "right", "exfalso", "contradiction", "specialize",
    "all_goals", "any_goals", "first", "repeat", "conv", "zify", "rify", "qify",
    "nth_rewrite", "change", "convert", "ext", "funext", "split", "split_ifs",
    "theorem", "lemma", "private", "set_option", "#eval", "#check", "#print",
    "·", "|", "<;>", "sorry", "skip", "-",
)


def lean_lines(text: str) -> str:
    """The longest run of lines that could be Lean, prose dropped."""

    runs, current = [], []
    for line in text.split("\n"):
        body = line.strip()
        opens = body.startswith(OPENERS) or (line.startswith((" ", "\t")) and bool(current))
        if body and opens:
            current.append(line)
        elif not body and current:
            current.append(line)
        else:
            runs.append(current)
            current = []
    runs.append(current)
    best = max(runs, key=lambda r: len([l for l in r if l.strip()]), default=[])
    return textwrap.dedent("\n".join(best)).strip()


def screen_step(reply: str, allow_sorry: bool = False) -> str:
    """A step is tactic lines. Prose around them is dropped, not spliced.
    On the board a `sorry` is a subgoal being posted, so the board allows it."""

    blocks = [b for b in FENCED.findall(reply) if b.strip()]
    raw = strip_fences(blocks[-1] if blocks else reply)
    block = normalise_steps(lean_lines(raw) if not blocks else raw)
    # A lone `by` on the first line is the model framing its block, not a step.
    # Measured on p09: `strip()` dedented only the first line after it, and 13
    # of one model's 34 replies reached Lean as `unexpected token 'have'`.
    lines = block.split("\n")
    if lines and lines[0].strip() == "by":
        lines = lines[1:]
    block = textwrap.dedent("\n".join(lines)).strip()
    if not block or STEP_BAN.search(block):
        return ""
    # A `sorry` is a placeholder for a goal that gets its own turn: a branch of
    # an `induction ... with`, or the body of a lemma being introduced. Anywhere
    # else it is the model closing the goal it was asked to prove.
    if (re.search(r"\bsorry\b", block) and not allow_sorry and "with" not in block
            and "|" not in block and not declaration_name(block)):
        return ""
    # A step that does nothing still enters the file and every later prompt.
    if all(l.strip() in ("", "skip") for l in block.splitlines()):
        return ""
    return block


HEAVY = ("nlinarith", "polyrith", "decide", "interval_cases")


LIGHTER = ("linarith", "norm_num", "positivity", "simp", "omega", "ring")


HINTED = re.compile(r"\b(nlinarith|linarith|positivity|norm_num)\s*\[([^\]]*)\]")


def lighter_forms(text: str) -> list[str]:
    """Cheaper spellings of the same file, cheapest first.

    A hint list is what makes a certificate large, so it is trimmed before the
    tactic itself is traded down."""

    out: list[str] = []
    for m in HINTED.finditer(text):
        hints = [h.strip() for h in m.group(2).split(",") if h.strip()]
        if len(hints) > 1:
            for hint in hints:
                out.append(text[:m.start()] + f"{m.group(1)} [{hint}]" + text[m.end():])
        if hints:
            out.append(text[:m.start()] + m.group(1) + text[m.end():])
    for heavy in HEAVY:
        start = 0
        while (at := text.find(heavy, start)) != -1:
            for light in LIGHTER:
                out.append(text[:at] + light + text[at + len(heavy):])
            start = at + len(heavy)
    return out
