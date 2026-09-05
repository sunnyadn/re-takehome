"""Files built to ask Lean one question, and readers for its answers."""

from __future__ import annotations
import json
import os
from pathlib import Path
import re
import subprocess
from typing import Any, Sequence
from submission.cells import enclosing
from submission.techniques import blank_techniques
from submission.framework import (classify, goal_text, line_of, message_line, message_text, message_span, placeholders)

from submission.board.types import (Board, Goal, HAVE_HEAD, binder_names, hypotheses, owner, split_top, target_of)
from submission.board.text import split_statement


# A check is cut at a few times what the current file costs, never the harness's
# 120s: the slow-step guard refuses anything adding SLOW_STEP_MS anyway, and a
# timeout also forces a container restart (measured putnam_2018_a1: 36..82s each).
CHECK_TIMEOUT_FLOOR_S = 30


CHECK_TIMEOUT_CAP_S = 120


def check_timeout_s(base_ms: int) -> int:
    return min(CHECK_TIMEOUT_CAP_S, max(CHECK_TIMEOUT_FLOOR_S, (3 * base_ms + 20_000) // 1000))


UNITS = {"B": 1, "KiB": 2 ** 10, "MiB": 2 ** 20, "GiB": 2 ** 30, "KB": 10 ** 3, "MB": 10 ** 6, "GB": 10 ** 9}


def container_memory_bytes(name: str) -> int | None:
    """One `docker stats` reading for the container, None when unavailable."""
    try:
        out = subprocess.run(["docker", "stats", "--no-stream", "--format", "{{.MemUsage}}", name],
                             capture_output=True, text=True, timeout=20).stdout
    except (OSError, subprocess.SubprocessError):
        return None
    m = re.match(r"\s*([\d.]+)\s*([KMG]i?B|B)", out)
    return int(float(m.group(1)) * UNITS[m.group(2)]) if m else None


# `skip` succeeds where no goal is left, so a placeholder under a step that
# closed its goal was silent and took the enclosing block's goal for its own
# (measured on rmo_2000_6: every step for `⊢ 10 ≤ n` went to a dead line 34
# lines above it, nine times over). `focus` fails there: "no goals to be solved".
PROBE = "focus skip"


def dump_check(text: str, focus: Any, check: Any) -> None:
    """Every rendered file and its verdict, when VM_DUMP_DIR is set (debugging)."""
    where = os.environ.get("VM_DUMP_DIR")
    if not where:
        return
    os.makedirs(where, exist_ok=True)
    n = len(os.listdir(where)) // 2
    Path(where, f"{n:04d}.lean").write_text(text)
    Path(where, f"{n:04d}.json").write_text(json.dumps({
        "focus": focus, "ms": check.duration_ms, "accepted": check.accepted,
        "timed_out": check.timed_out,
        "messages": [{"severity": m.get("severity"), "line": (m.get("pos") or {}).get("line"),
                      "data": str(m.get("data"))[:400]} for m in check.messages]}, ensure_ascii=False, indent=1))


def render_all(text: str) -> str:
    """Every placeholder as the probe, so one check prints every goal and
    names every placeholder with no goal behind it."""

    out, shift = text, 0
    for match in placeholders(text):
        start, end = match.start() + shift, match.end() + shift
        out = out[:start] + f"{match.group(1)}{PROBE}" + out[end:]
        shift += len(PROBE) - (match.end() - match.start() - len(match.group(1)))
    return out


def read_board(text: str, messages: Sequence[dict[str, Any]], accepted: bool) -> Board:
    """Each placeholder takes the tightest `unsolved goals` span holding it."""

    spans = [(m, message_span(m)) for m in classify(messages)[0]]
    stated = statements(messages)
    goals = []
    for match in placeholders(text):
        line = line_of(text, match.start())
        fits = [(s[1] - s[0], goal_text(m)) for m, s in spans if s and s[0] <= line <= s[1]]
        held = enclosing(text, line)
        shown = min(fits, key=lambda f: f[0])[1] if fits else ""
        goals.append(Goal(line, match.group(1), owner(text, line), shown,
                          name_premises(stated.get(line, ""), shown), held.id if held else 0))
    return Board(text, goals, list(messages), accepted)


CLOSER_TAG = re.compile(r"^closer (\d+)$")


# Tactics that evaluate a closed statement; none of them uses a hypothesis
# from the context, so every hypothesis is proved at the values, not assumed.
WITNESS_CLOSERS = ("norm_num", "decide", "simp",
                   "norm_num [Finset.mem_insert, Finset.mem_singleton]",
                   "simp; norm_num", "norm_num; decide")


# Lean states the goal itself: every hypothesis in scope as a binder, numerals
# typed so the text elaborates again on its own.
EXTRACT = "set_option pp.numericTypes true in extract_goal"


EXTRACTED = re.compile(r"theorem\s+[\w'.]*extracted_\d+\s*(.*)", re.S)


# Measured on the graded image: Lean's severity string is `info`.
INFO = ("info", "information")


def extract_file(text: str, goals: Sequence[Goal]) -> str:
    """The file with these goals' placeholders asking Lean to state them."""
    lines = blank_techniques(render_all(text)).split("\n")
    for g in goals:
        lines[g.line - 1] = g.indent + EXTRACT
    return "\n".join(lines)


APPLY_PROBE = "set_option maxHeartbeats 40000 in apply?"


TRY_THIS_STEP = re.compile(r"Try this:\s*(?:\[apply\]\s*)?(exact|refine)\s+(.+)", re.S)


def apply_file(text: str, goal: Goal) -> str:
    """The file with this goal asking Mathlib what unifies with it."""
    lines = blank_techniques(render_all(text)).split("\n")
    lines[goal.line - 1] = goal.indent + APPLY_PROBE
    return "\n".join(lines)


def read_suggestions(messages: Sequence[dict[str, Any]], line: int) -> list[tuple[str, str]]:
    """`apply?`'s answers at this line: (exact|refine, term), Lean's order."""
    out = []
    for m in messages:
        if m.get("severity") not in INFO or message_line(m) != line:
            continue
        for found in TRY_THIS_STEP.finditer(message_text(m)):
            term = " ".join(found.group(2).split())
            if (found.group(1), term) not in out:
                out.append((found.group(1), term))
    return out


def have_extract_file(lines: Sequence[str], at: Sequence[int]) -> tuple[str, dict[int, int]]:
    """The file with these `have`s' bodies replaced by a request to state the
    claim; the map from each have's line index to the line Lean answers on."""
    out, where, shift, i = [], {}, 0, 0
    marks = set(at)
    text_lines = render_all("\n".join(lines)).split("\n")
    while i < len(text_lines):
        ln = text_lines[i]
        out.append(ln)
        head = HAVE_HEAD.match(ln) if i in marks else None
        if not head:
            i += 1
            continue
        depth = len(head.group(1))
        j = i + 1
        while j < len(text_lines) and (not text_lines[j].strip()
                                       or len(text_lines[j]) - len(text_lines[j].lstrip()) > depth):
            j += 1
        out.append(" " * (depth + 2) + EXTRACT)
        where[i] = len(out)
        i = j
    return "\n".join(out), where


def statements(messages: Sequence[Any]) -> dict[int, str]:
    """Line -> the statement `extract_goal` printed there, binders and target."""
    out: dict[int, str] = {}
    for m in messages:
        if not isinstance(m, dict) or m.get("severity") not in INFO:
            continue
        found, line = EXTRACTED.search(message_text(m)), message_line(m)
        if found and line is not None:
            body = found.group(1)
            out[line] = " ".join(body.rsplit(":=", 1)[0].split())
    return out


NUMERAL_TYPE = re.compile(r"\((\d+) : ℕ\)")


def name_premises(stmt: str, goal_text: str) -> str:
    """An inaccessible hypothesis (`a✝`) comes back from `extract_goal` as an arrow
    premise. Named as a binder, the link passes it (`‹_›`) and a block sees the goal
    it was written for (measured on rmo_2000_6: 10 link failures in two runs)."""
    parsed = split_statement(stmt) if stmt else None
    if not parsed or "⊢" not in goal_text:
        return stmt
    groups, target = parsed
    shown = " ".join(goal_text.rsplit("⊢", 1)[-1].split())

    def same(a: str, b: str) -> bool:
        return NUMERAL_TYPE.sub(r"\1", a).strip() == NUMERAL_TYPE.sub(r"\1", b).strip()

    premises: list[str] = []
    rest = target
    while not same(rest, shown):
        cut = split_top(rest, " → ")
        if cut is None:
            return stmt
        premises.append(cut[0].strip())
        rest = cut[1].strip()
    if not premises:
        return stmt
    named = [f"(vm_p{i + 1} : {prem})" for i, prem in enumerate(premises)]
    return " ".join(groups + named) + f" : {rest}"


UNKNOWN_NAME_QUOTED = re.compile(r"(?:[Uu]nknown (?:constant|identifier)|environment does not contain) `([^`]+)`")


# Lean lists, for each misspelt library name, the declarations whose last
# component shares its tokens, with their types. One CommandElabM pass over
# the environment; nothing is assumed about which names exist.
NAME_PROBE = """open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let wanted : List String := [{names}]
  let names := env.constants.toList.filterMap fun (n, _) =>
    if n.isInternal then none else some (n, n.toString)
  for w in wanted do
    let toks := (((w.splitOn ".").flatMap (·.splitOn "_")).filter (fun t => t.length > 1)).eraseDups
    let tail := (w.splitOn ".").getLast!
    let need := if toks.length ≤ 2 then toks.length else toks.length - 1
    let mut hits : Array (Nat × Nat × Name) := #[]
    for (n, s) in names do
      let hit := toks.foldl (fun acc t => if (s.splitOn t).length > 1 then acc + 1 else acc) 0
      if hit ≥ need then
        let bonus := if (s.splitOn tail).length > 1 then 2 else 0
        hits := hits.push (hit + bonus, s.length, n)
    let sorted := hits.qsort (fun a b => decide (a.1 > b.1) || (a.1 == b.1 && decide (a.2.1 < b.2.1)))
    let mut out := s!"{{w}} is not a name. Nearest that exist:"
    for (_, _, n) in sorted.toList.take 5 do
      if let some ci := env.find? n then
        let ty ← liftTermElabM (Meta.ppExpr ci.type)
        out := out ++ s!"\\n  {{n}} : {{ty}}"
    logInfo out
"""


# The goal's own vocabulary, asked of the environment: every constant whose
# name carries two or more of the goal's tokens, best first, with its type.
# Measured in the image: 1 to 3 s a query; [Coprime, divisors, mul] returns
# Nat.Coprime.divisors_mul first, [Nat, pow, mod, add] Nat.pow_mod and Nat.pow_add.
LIBRARY_PROBE = """open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let toks : List String := [{tokens}]
  let skip := ["_proof_", "._", "match_", "proof_", ".eq_", ".rec", ".casesOn", ".noConfusion", ".sizeOf", ".injEq", ".inj", ".below", ".brecOn", ".binductionOn", "Decidable", ".mk", "inst", "Lex"]
  let mut hits : Array (Nat × Nat × Name) := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    let s := n.toString
    if skip.any (fun k => (s.splitOn k).length > 1) then continue
    let low := s.toLower
    let hit := toks.foldl (fun acc t => if (low.splitOn t).length > 1 then acc + 1 else acc) 0
    if hit ≥ 2 then hits := hits.push (hit, s.length, n)
  let sorted := hits.qsort (fun a b => decide (a.1 > b.1) || (a.1 == b.1 && decide (a.2.1 < b.2.1)))
  let mut out := "Library for this goal:"
  for (_, _, n) in sorted.toList.take {limit} do
    if let some ci := env.find? n then
      let ty ← liftTermElabM (Meta.ppExpr ci.type)
      let t := ((toString ty).replace "\\n" " ").take 160
      out := out ++ s!"\\n  {{n}} : {{t}}"
  logInfo out
"""


LIBRARY_LIMIT = 12


# Notation to the word Mathlib spells it with in a name.
NOTATION_TOKENS = (("∣", "dvd"), ("%", "mod"), ("^", "pow"), ("∑", "sum"), ("∏", "prod"),
                   ("!", "factorial"), ("√", "sqrt"), ("⌊", "floor"), ("⌈", "ceil"), ("≡", "modeq"),
                   ("ℕ", "nat"), ("ℤ", "int"), ("ℚ", "rat"), ("ℝ", "real"), ("≤", "le"), ("<", "lt"))


IDENTIFIER = re.compile(r"\b(?:[A-Z][A-Za-z]+(?:\.[A-Za-z][A-Za-z0-9]*)*|[a-z][A-Za-z]*[A-Z][A-Za-z]*|[a-z]{4,})\b")


NOT_TOKENS = {"type", "prop", "sort", "true", "false", "with", "have", "show", "this", "then", "else", "card"}


# Too common to rank a name on their own; they go last and only fill the list.
WEAK_TOKENS = {"le", "lt", "nat", "int", "rat", "real"}


def goal_tokens(goal_text: str) -> list[str]:
    """The words of the goal a library name could carry: each identifier's
    components, then the notation's names, the type's name last; at most 6."""
    target = goal_text.split("⊢", 1)[1] if "⊢" in goal_text else goal_text
    hyps = "\n".join(v for v in hypotheses(goal_text).values())
    words: list[str] = []
    late: list[str] = []
    for text in (target, hyps):
        for m in IDENTIFIER.findall(text):
            for part in m.split("."):
                low = part.lower()
                if len(low) > 2 and low not in NOT_TOKENS and low not in words:
                    words.append(low)
        for sym, word in NOTATION_TOKENS:
            if sym in text and word not in words and word not in late:
                (late if word in WEAK_TOKENS else words).append(word)
    return (words + late)[:6]


def library_file(prefix: str, tokens: Sequence[str]) -> str:
    quoted = ", ".join('"' + t.replace('"', "") + '"' for t in tokens)
    return prefix.rstrip("\n") + "\n\n" + LIBRARY_PROBE.format(tokens=quoted, limit=LIBRARY_LIMIT)


def read_library(messages: Sequence[dict[str, Any]]) -> str:
    for m in messages:
        data = str(m.get("data", ""))
        if m.get("severity") in INFO and data.startswith("Library for this goal:"):
            lines = [l for l in data.split("\n")[1:] if l.strip()]
            return "\n".join(l.strip()[:200] for l in lines)
    return ""


def library_names(messages: Sequence[dict[str, Any]], goal_text: str) -> list[str]:
    """Unknown names in Lean's messages that look like library declarations:
    dotted or underscored, and not a variable or hypothesis of the goal."""
    local = set(hypotheses(goal_text))
    out: list[str] = []
    for m in messages:
        for name in UNKNOWN_NAME_QUOTED.findall(str(m.get("data", ""))):
            head = name.split(".")[0]
            if ("." in name or "_" in name) and head not in local and not name.startswith("h") \
                    and name not in out:
                out.append(name)
    return out[:3]


def name_probe_file(prefix: str, names: Sequence[str]) -> str:
    quoted = ", ".join('"' + n.replace('"', "") + '"' for n in names)
    return prefix.rstrip("\n") + "\n\n" + NAME_PROBE.format(names=quoted)


def read_name_probe(messages: Sequence[dict[str, Any]]) -> str:
    """Each name's answer, one candidate per line, types cut so a long instance
    chain does not crowd the feedback."""
    parts = []
    for m in messages:
        data = str(m.get("data", ""))
        if m.get("severity") in INFO and "Nearest that exist" in data:
            lines = [l for l in data.split("\n") if l.strip()]
            parts.append("\n".join(l[:200] for l in lines))
    return "\n\n".join(parts)


def witness_file(prefix: str, groups: Sequence[str], values: dict[str, str],
                 target: str) -> str:
    """One `example`: the binders the auditor assigned stay binders, pinned to
    the values; every other binder is a hypothesis to prove there, and the
    target must fail. Only evaluation closes it, so a pass is a refutation."""
    keep, hyps = [], []
    for g in groups:
        names = binder_names(g)
        if names and all(n in values for n in names):
            keep.append("(" + g[1:-1] + ")")
        else:
            parts = split_top(g[1:-1], ":")
            hyps.append((parts[1] if parts else g[1:-1]).strip())
    fixed = " ".join(f"(w_{n} : {n} = ({v}))" for n, v in values.items())
    body = " ∧ ".join([f"({h})" for h in hyps] + [f"¬ ({target})"])
    binders = " ".join([*keep, fixed]).strip()
    return (prefix.rstrip() + f"\n\nexample {binders} : {body} := by\n  subst_vars\n  first\n"
            + "".join(f"  | ({t}; done)\n" for t in WITNESS_CLOSERS))


def audit_prompt(stmt: str, definitions: str) -> str:
    parts = ["A goal inside a Lean 4 proof, exactly as Lean states it: every "
             f"hypothesis in scope is a binder, the target follows the last colon.\n{stmt}"]
    if definitions.strip():
        parts.append(f"Definitions in scope:\n{definitions.strip()[:1500]}")
    parts.append(
        "Is the target a consequence of the hypotheses? If not, give one "
        "counterexample: a Lean term for every variable binder (leave the "
        'hypothesis binders out), as {"counterexample": {"x": "..."}}. Use small '
        "concrete values and check every hypothesis by hand before answering. "
        'If the target does follow, answer {"holds": true}.')
    return "\n\n".join(parts)


def read_witness(reply: str) -> dict[str, str] | None:
    """The values a reply names, or None (holds / unreadable)."""
    found = re.search(r"\{.*\}", reply, re.S)
    try:
        given = json.loads(found.group(0)).get("counterexample") if found else None
    except (ValueError, AttributeError):
        return None
    if not isinstance(given, dict) or not given:
        return None
    return {str(n): str(v).strip() for n, v in given.items()}


def tagged_closers(cocktail: Sequence[str]) -> str:
    """The cocktail as one `first`, each alternative announcing itself, so the
    check that closes the goal also says which closer did it."""
    return "first\n" + "\n".join(f'| (trace "closer {i}"; {t}; done)'
                                  for i, t in enumerate(cocktail))


def fired_closer(messages: Sequence[Any], span: tuple[int, int],
                 cocktail: Sequence[str]) -> str | None:
    """The alternative that closed the goal: the last tag reported inside the
    block, whether or not Lean kept the tags of the alternatives that failed."""
    hits = []
    for m in messages:
        if not isinstance(m, dict) or m.get("severity") not in INFO:
            continue
        tag = CLOSER_TAG.match(str(m.get("data", "")).strip())
        line = message_line(m)
        if tag and line is not None and span[0] <= line <= span[1]:
            hits.append((line, int(tag.group(1))))
    return cocktail[max(hits)[1]] if hits else None


EXISTS = re.compile(r"^∃\s+(?:\(\s*)?([\w' ]+?)(?:\s*:\s*([^,)]+))?\)?\s*,\s*(.*)$", re.S)


MEMBER = re.compile(r"^(\d+)\s*∈\s*\{\s*(\w+)\s*\|\s*(.*)\}$", re.S)


def existential(goal_text: str) -> tuple[list[str], str] | None:
    """`∃ a b, body` or `N ∈ {n | ∃ a b, body}` with ℕ binders and a body that
    binds nothing more and names no hypothesis: what evaluation can search."""

    target = target_of(goal_text)
    m = MEMBER.match(target)
    if m:
        value, var, target = m.groups()
        target = re.sub(rf"(?<![\w'.]){re.escape(var)}(?![\w'])", value, target.strip())
    names: list[str] = []
    while True:
        m = EXISTS.match(target.strip())
        if not m:
            break
        binders, typ, target = m.groups()
        if typ and typ.strip() != "ℕ":
            return None
        names += binders.split()
    if not names or len(names) > 3:
        return None
    if re.search(r"[∀∃λ→]|\bfun\b", target) or not target.strip():
        return None
    if any(re.search(rf"(?<![\w'.]){re.escape(n)}(?![\w'])", target) for n in hypotheses(goal_text)):
        return None
    return names, target.strip()


WITNESS_BOUND = 40


def witness_search_file(prefix: str, names: Sequence[str], body: str) -> str:
    """A Lean `#eval` that walks the binders over 0..WITNESS_BOUND-1 and keeps the
    first 3 tuples whose body decides true."""

    loops = "".join(f"{'  ' * (i + 1)}for {n} in List.range {WITNESS_BOUND} do\n"
                    for i, n in enumerate(names))
    pad = "  " * (len(names) + 1)
    tuple_ = ", ".join(names)
    return (prefix.rstrip("\n") + "\n\n#eval Id.run do\n  let mut found : List (List Nat) := []\n"
            + loops + f"{pad}if found.length < 3 ∧ decide ({body}) then\n"
            + f"{pad}  found := found ++ [[{tuple_}]]\n  return found\n")


def read_witnesses(messages: Sequence[dict[str, Any]]) -> list[list[str]]:
    for m in messages:
        data = str(m.get("data", "")).strip()
        if m.get("severity") in INFO and data.startswith("[["):
            return [[v.strip() for v in row.split(",")] for row in re.findall(r"\[([\d, ]+)\]", data)]
    return []


def searched_clean(messages: Sequence[dict[str, Any]]) -> bool:
    """The walk ran to the end and printed no tuple: `[]`, as an info message."""
    return any(m.get("severity") in INFO and str(m.get("data", "")).strip() == "[]"
               for m in messages)


PROP_SIGNS = re.compile(r"[=<≤>≥≠∣∧∨¬↔]|\bPrime\b|\bCoprime\b|\bEven\b|\bOdd\b")


def counterexample_search(groups: Sequence[str], target: str) -> tuple[list[str], str] | None:
    """The stated goal as a decidable search: every ℕ binder ranges, every
    hypothesis binder filters, the target is negated. None if a binder is
    neither (a real, a function, a quantified fact), which evaluation cannot walk."""
    names, hyps = [], []
    for g in groups:
        parts = split_top(g[1:-1], ":")
        if len(parts) != 2:
            return None
        typ = parts[1].strip()
        if typ == "ℕ":
            names += parts[0].split()
        elif PROP_SIGNS.search(typ) and not re.search(r"[∀∃λ→]|\bfun\b", typ):
            hyps.append(typ)
        else:
            return None
    if not names or len(names) > 3 or re.search(r"[∀∃λ→]|\bfun\b", target):
        return None
    body = " ∧ ".join([f"({h})" for h in hyps] + [f"¬ ({target.strip()})"])
    return names, body


def is_closed(goal_text: str) -> bool:
    """A goal whose target names none of its hypotheses and binds nothing: a
    closed proposition, decided by evaluation alone. Measured on rmo_2000_6:
    `use 2; use 5` left `⊢ 0 < 5 ∧ 2000 ∣ 8 * 5 ^ 4 ∧ 10 = 2 * 5` under proved
    facts about numerals, and "no hypotheses at all" missed it."""
    target = target_of(goal_text)
    if not target or re.search(r"[∀∃λ]|\bfun\b", target) or not re.search(r"\d", target):
        return False
    return not any(re.search(rf"(?<![\w'.]){re.escape(n)}(?![\w'])", target)
                   for n in hypotheses(goal_text))

