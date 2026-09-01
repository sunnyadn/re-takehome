"""FRAMEWORK.md as code: one file, one cursor, Lean adjudicates.

The cursor is the topmost lone `sorry` line, rendered as `skip` so Lean prints
its goal. Everything here is a text transform; the model supplies the steps.
"""

from __future__ import annotations

import re
from typing import Any, Sequence

# `first` takes the first alternative that does not fail, and `norm_num` can
# succeed by rewriting without closing; `done` turns that into a failure so the
# block keeps searching. Never emit an alternative without it.
from submission.agent import COCKTAIL, wrap_tactic

# A placeholder is a whole line. A term-position `:= sorry` (an answer slot) is
# not one, and `skip` would not typecheck there anyway.
PLACEHOLDER = re.compile(r"^([ \t]*)sorry[ \t]*$", re.M)

ANSWER_SLOT = re.compile(r"^\s*abbrev\s+([A-Za-z_][\w']*)\s*:[^:=]*:=\s*sorry\s*$", re.M)
PROOF_HEAD = re.compile(r"^\s*(theorem|lemma)\s+([A-Za-z_][\w']*)", re.M)
IMPORT_LINE = re.compile(r"^\s*import\s", re.M)


def placeholders(text: str) -> list[re.Match[str]]:
    """Every open goal, in file order. The cursor sits on one of them."""

    return list(PLACEHOLDER.finditer(text))


def cursor(text: str, index: int = 0) -> re.Match[str] | None:
    """The placeholder the cursor is on, the topmost unless told otherwise."""

    found = placeholders(text)
    return found[min(max(index, 0), len(found) - 1)] if found else None


def is_done(text: str) -> bool:
    return cursor(text) is None


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def render(text: str, index: int = 0) -> tuple[str, int]:
    """The file to send, and the 1-based line the `skip` sits on (0 if none).

    Only the cursor becomes `skip`; the other placeholders stay `sorry`, so Lean
    reports one open goal and it is the one being worked on."""

    match = cursor(text, index)
    if match is None:
        return text, 0
    swapped = text[: match.start()] + f"{match.group(1)}skip" + text[match.end():]
    return swapped, line_of(text, match.start())


def reindent(block: str, indent: str) -> str:
    """Shift a block so its shallowest line sits at `indent`, keeping shape."""

    lines = [l for l in block.replace("\t", "  ").split("\n")]
    body = [l for l in lines if l.strip()]
    if not body:
        return ""
    base = min(len(l) - len(l.lstrip()) for l in body)
    return "\n".join(indent + l[base:] if l.strip() else "" for l in lines)


TAIL_SORRY = re.compile(r"(:=\s*by|=>|·|\|)[ \t]*sorry[ \t]*$", re.M)


def normalise_steps(block: str) -> str:
    """Put every `sorry` on its own line so the cursor scan can find it."""

    def split(match: re.Match[str]) -> str:
        line = match.string[match.string.rfind("\n", 0, match.start()) + 1: match.start()]
        indent = line[: len(line) - len(line.lstrip())]
        return f"{match.group(1)}\n{indent}  sorry"

    return TAIL_SORRY.sub(split, block.replace("\t", "  ")).rstrip()


def replace_cursor(text: str, block: str, *, index: int = 0,
                   trailing: bool = True) -> tuple[str, tuple[int, int]]:
    """Put a step where the cursor is, leaving a placeholder for what follows."""

    match = cursor(text, index)
    if match is None:
        raise ValueError("no cursor to replace")
    indent = match.group(1)
    body = reindent(normalise_steps(block), indent)
    if trailing:
        body = f"{body}\n{indent}sorry"
    new = text[: match.start()] + body + text[match.end():]
    start = line_of(text, match.start())
    return new, (start, start + body.count("\n"))


def insert_preamble(text: str, block: str) -> str:
    """Probes and `set_option` go above the theorem, never inside the proof."""

    ends = [m.end() for m in IMPORT_LINE.finditer(text)]
    at = text.find("\n", ends[-1]) + 1 if ends else 0
    return text[:at] + block.rstrip() + "\n\n" + text[at:]


def answer_slots(text: str) -> tuple[str, ...]:
    return tuple(ANSWER_SLOT.findall(text))


def fill_answer(text: str, name: str, value: str) -> str:
    """Replace one `abbrev name ... := sorry` slot with a literal."""

    pattern = re.compile(rf"^(\s*abbrev\s+{re.escape(name)}\s*:[^:=]*:=\s*)sorry\s*$", re.M)
    return pattern.sub(rf"\g<1>{value}", text)


def root_names(text: str) -> tuple[str, ...]:
    return tuple(m.group(2) for m in PROOF_HEAD.finditer(text))


# Measured: Lean writes "No goals to be solved" for a leftover tactic and
# "no goals to be solved" elsewhere, so every match here is case-folded.
UNSOLVED = "unsolved goals"
NO_GOALS = "no goals to be solved"
# A step Lean refused for want of budget is not a wrong step, and Lean names the
# option to raise. Measured on p06_pow_mod: 7 ^ 2026 fails in 88ms on recursion
# depth, not on heartbeats.
BUDGETS = ("maximum number of heartbeats", "maximum recursion depth",
           "exceeds the threshold")


def message_text(message: Any) -> str:
    data = message.get("data", "") if isinstance(message, dict) else ""
    return data if isinstance(data, str) else str(data)


def classify(messages: Sequence[Any]) -> tuple[list[Any], list[Any], list[Any], list[Any]]:
    """Progress, surplus placeholder, too expensive, real failure."""

    progress, surplus, expensive, failures = [], [], [], []
    for m in messages:
        if not isinstance(m, dict) or m.get("severity") != "error":
            continue
        text = message_text(m).lower()
        if UNSOLVED in text:
            progress.append(m)
        elif NO_GOALS in text:
            surplus.append(m)
        elif any(b in text for b in BUDGETS):
            expensive.append(m)
        else:
            failures.append(m)
    return progress, surplus, expensive, failures


def message_line(message: Any) -> int | None:
    pos = message.get("pos") if isinstance(message, dict) else None
    line = pos.get("line") if isinstance(pos, dict) else None
    return line if isinstance(line, int) else None


def in_span(message: Any, span: tuple[int, int]) -> bool:
    line = message_line(message)
    return line is not None and span[0] <= line <= span[1]


def goal_text(message: Any) -> str:
    """Everything an `unsolved goals` error carries: cases, hypotheses, goals.

    Measured on p09: one message holds every open goal, so cutting at the first
    turnstile hands the model two goals spliced together and no hypotheses."""

    text = message_text(message)
    head, _, body = text.partition("\n")
    return (body or text).strip() if UNSOLVED in head.lower() else text.strip()


def cursor_goal(messages: Sequence[Any], cursor_line: int) -> str:
    """The active goal.

    Lean attributes the message to the `skip` sometimes and to the enclosing
    declaration otherwise, so the cursor's own line is a preference, not a key."""

    open_goals = classify(messages)[0]
    for m in open_goals:
        if message_line(m) == cursor_line:
            return goal_text(m)
    return goal_text(open_goals[0]) if open_goals else ""


def message_end_line(message: Any) -> int | None:
    pos = message.get("endPos") if isinstance(message, dict) else None
    line = pos.get("line") if isinstance(pos, dict) else None
    return line if isinstance(line, int) else None


def reopen(text: str, line: int) -> str:
    """Give a goal with nowhere to work a placeholder at the end of its block.

    A tactic closes the goal in front of it, so goals opened by a split are
    reached one placeholder at a time, in order."""

    lines = text.split("\n")
    at = min(max(line, 1), len(lines))
    while at > 1 and not lines[at - 1].strip():
        at -= 1
    body = lines[at - 1]
    indent = body[: len(body) - len(body.lstrip())] or "  "
    lines.insert(at, f"{indent}sorry")
    return "\n".join(lines)


def drop_lines(text: str, lines: Sequence[int]) -> str:
    """Delete 1-based lines, which is how a surplus placeholder is removed."""

    kill = set(lines)
    kept = [l for i, l in enumerate(text.split("\n"), start=1) if i not in kill]
    return "\n".join(kept)


def sweep_body(cocktail: Sequence[str] = COCKTAIL) -> str:
    """The whole cocktail as one `first`, every alternative forced to close."""

    return "first\n" + "\n".join(f"| {wrap_tactic(t)}" for t in cocktail)


def any_goals_sweep(cocktail: Sequence[str] = COCKTAIL) -> str:
    """`all_goals` rolls everything back if one goal survives; `any_goals` keeps."""

    return "any_goals (" + " | ".join(wrap_tactic(t) for t in cocktail) + ")"


FIRST_BLOCK = re.compile(r"^([ \t]*)first[ \t]*\n((?:[ \t]*\|.*(?:\n|$))+)", re.M)
ALTERNATIVE = re.compile(r"^[ \t]*\|[ \t]*\((.*);[ \t]*done\)[ \t]*$", re.M)


def first_blocks(text: str) -> list[re.Match[str]]:
    """Search blocks left in a finished proof, slowest first thing to compile."""

    return list(FIRST_BLOCK.finditer(text))


def alternatives(block: str) -> list[str]:
    return ALTERNATIVE.findall(block)


def collapse(text: str, match: re.Match[str], tactic: str) -> str:
    """Put one alternative where the whole search block was."""

    return text[: match.start()] + f"{match.group(1)}{tactic}\n" + text[match.end():]


def axiom_probe(text: str, names: Sequence[str]) -> str:
    """`#print axioms` for every graded name; an allowlist, never a blocklist."""

    lines = "\n".join(f"#print axioms {n}" for n in names)
    return f"{text.rstrip()}\n\n{lines}\n" if lines else text


def step_spans(text: str) -> list[tuple[int, int, str]]:
    """Every top-level step of every proof body, as 1-based line spans."""

    lines = text.split("\n")
    out: list[tuple[int, int, str]] = []
    i = 0
    while i < len(lines):
        if not lines[i].rstrip().endswith(":= by"):
            i += 1
            continue
        j = i + 1
        while j < len(lines) and (not lines[j].strip() or lines[j].startswith(" ")):
            j += 1
        body = [(n, l) for n, l in enumerate(lines[i + 1:j], start=i + 2) if l.strip()]
        if body:
            base = min(len(l) - len(l.lstrip()) for _, l in body)
            starts = [n for n, l in body if len(l) - len(l.lstrip()) == base]
            for k, start in enumerate(starts):
                end = (starts[k + 1] - 1) if k + 1 < len(starts) else body[-1][0]
                out.append((start, end, lines[start - 1].strip()))
        i = j
    return out


def have_spans(text: str) -> list[tuple[int, int, str]]:
    """The steps §4 may delete: facts, never the moves that shaped the goal."""

    return [s for s in step_spans(text) if s[2].startswith("have ")]


DECLARATION = re.compile(r"^\s*(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z_][\w']*)")


def declaration_name(block: str) -> str:
    """The name a block declares at the top level, if it declares one.

    A fact two theorems share cannot live inside either one's proof."""

    for line in block.split("\n"):
        if line.strip():
            found = DECLARATION.match(line)
            return found.group(1) if found else ""
    return ""


def unwrap_own(block: str, names: Sequence[str]) -> str:
    """A block that restates the graded theorem is its body, wrongly framed.

    Measured on p09: with reasoning off the writer opens with the theorem header
    and, told the name is taken, opens with the same line minus `theorem`."""

    for name in names:
        head = re.compile(rf"\A\s*(?:private\s+)?(?:theorem|lemma)?\s*{re.escape(name)}\b"
                          r"[^\n]*?:=\s*by[ \t]*\n")
        found = head.match(block)
        if found:
            return reindent(block[found.end():], "")
    return block


HAVE_BODY = re.compile(r"^(\s*have\b.*?:=\s*)(\S.*)$", re.M)
UNKNOWN_NAME = re.compile(r"[Uu]nknown (identifier|constant)|environment does not contain")


def hand_to_search(block: str) -> str:
    """Rule 1 of the framework, applied mechanically.

    A `have` whose body names something Lean does not know is a fact stated
    correctly with the wrong lemma; `exact?` names it or nothing does."""

    return HAVE_BODY.sub(r"\1by exact?", block)
