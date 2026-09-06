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
from submission.contract import NAT_POW_LINE
from submission.sweep import COCKTAIL, DECL_START, PROOF_DECL, wrap_tactic
from submission.techniques import PREAMBLE_END

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
    """Probes, `set_option` and hoisted lemmas go below the whole header (imports,
    the instance line, the technique tactics), never inside the proof."""

    ends = [m.end() for m in IMPORT_LINE.finditer(text)]
    for line in (NAT_POW_LINE, PREAMBLE_END):
        i = text.find("\n" + line + "\n")
        if i >= 0:
            ends.append(i + len(line) + 1)
    at = text.find("\n", max(ends)) + 1 if ends else 0
    return text[:at] + block.rstrip() + "\n\n" + text[at:]


def answer_slots(text: str) -> tuple[str, ...]:
    return tuple(ANSWER_SLOT.findall(text))


CLOSED_HEAD = re.compile(r"^[ \t]*(?:theorem|lemma)\s+[A-Za-z_][\w']*\s*:\s*(.+?)\s*:=\s*by\s*$", re.M)
OPEN_TOKENS = re.compile(r"[∀∃∑∏λ→↔∧∨¬]|\bfun\b|\bIs[A-Z]|\bSet\b|\bFinset\b|\{")


def statement_probes(text: str, names: Sequence[str]) -> list[str]:
    """`#eval` of the closed side of a binder-free `theorem t : term = name`
    (or `name = term`), one per slot the statement fixes this way. Measured on
    p06: both models failed to write the `#eval` and the slot stayed `sorry`."""

    out: list[str] = []
    for name in names:
        for m in CLOSED_HEAD.finditer(text):
            sides = [x.strip() for x in m.group(1).split(" = ")]
            if len(sides) != 2 or name not in sides:
                continue
            term = sides[1] if sides[0] == name else sides[0]
            if OPEN_TOKENS.search(term) or re.search(rf"\b{re.escape(name)}\b", term):
                continue
            out.append(f"#eval ({term})")
            break
    return out


def fill_answer(text: str, name: str, value: str) -> str:
    """Replace one `abbrev name ... := sorry` slot with a literal."""

    pattern = re.compile(rf"^(\s*abbrev\s+{re.escape(name)}\s*:[^:=]*:=\s*)sorry\s*$", re.M)
    return pattern.sub(rf"\g<1>{value}", text)


# A definition slot states the answer as a term. Measured on putnam_2018_a1:
# `abbrev ... : Set (ℤ × ℤ) := by / sorry`, which the cursor took for a goal and
# wrote `exact?` into, where there is no goal to search.
DEFINITION = re.compile(
    r"^([ \t]*abbrev\s+([A-Za-z_][\w']*)\s*:\s*)(.+?)(\s*:=\s*by[ \t]*\n[ \t]*sorry[ \t]*)$",
    re.M)


def definition_slots(text: str) -> tuple[tuple[str, str], ...]:
    """Each name still waiting for a value, with the type it must have."""

    return tuple((m.group(2), m.group(3).strip()) for m in DEFINITION.finditer(text))


def fill_definition(text: str, name: str, term: str) -> str:
    """Put a term where a definition slot is; it is a value, never a proof."""

    def swap(match: re.Match[str]) -> str:
        return f"{match.group(1)}{match.group(3)} := {term.strip()}" \
            if match.group(2) == name else match.group(0)

    return DEFINITION.sub(swap, text)


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


def _at(message: Any, key: str, field: str) -> int | None:
    """Positions are file coordinates: FileCoordinates (agent.py) maps what
    Lean reports for the import-stripped body onto the file once, at the
    boundary, so no reader carries an offset of its own."""

    pos = message.get(key) if isinstance(message, dict) else None
    found = pos.get(field) if isinstance(pos, dict) else None
    return found if isinstance(found, int) else None


def message_line(message: Any) -> int | None:
    return _at(message, "pos", "line")


def message_column(message: Any) -> int | None:
    return _at(message, "pos", "column")


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
    """The active goal: the tightest reported span that holds the cursor.

    Lean attributes an unfinished branch to the branch and the goal at the
    cursor to the whole declaration, so the first message is often the wrong
    one and only containment tells them apart."""

    open_goals = classify(messages)[0]
    holding = [(m, message_span(m)) for m in open_goals]
    fits = [(span[1] - span[0], goal_text(m)) for m, span in holding
            if span and span[0] <= cursor_line <= span[1]]
    if fits:
        return min(fits, key=lambda f: f[0])[1]
    return goal_text(open_goals[0]) if open_goals else ""


def message_end_line(message: Any) -> int | None:
    return _at(message, "endPos", "line")


def message_span(message: Any) -> tuple[int, int] | None:
    start = message_line(message)
    if start is None:
        return None
    end = message_end_line(message)
    return (start, end if end is not None and end >= start else start)


def unreachable(messages: Sequence[Any], text: str,
                cursor_line: int) -> tuple[int, int] | None:
    """A goal no placeholder can reach, and where to put one.

    Measured on p09: `· intro h` leaves the bullet's goal open with a span of
    its own, while the declaration's span holds the goal at the cursor. A goal
    whose span holds neither is one the cursor can never get back to."""

    at = [(line_of(text, m.start()), len(m.group(1))) for m in placeholders(text)]
    for message in classify(messages)[0]:
        span = message_span(message)
        column = message_column(message)
        if span is None or column is None:
            continue
        if span[0] <= cursor_line <= span[1]:
            continue
        # A placeholder inside the span belongs to the branch, and so does the
        # one this returns, which lands a line past the span indented under it.
        # Without that second case the same goal is reopened on every check.
        if any(span[0] <= line <= span[1] or (line == span[1] + 1 and indent > column)
               for line, indent in at):
            continue
        return span[1], column + 2
    return None


def reopen(text: str, line: int, column: int | None = None) -> str:
    """Give a goal with nowhere to work a placeholder at the end of its block.

    A tactic closes the goal in front of it, so goals opened by a split are
    reached one placeholder at a time, in order."""

    lines = text.split("\n")
    at = min(max(line, 1), len(lines))
    while at > 1 and not lines[at - 1].strip():
        at -= 1
    body = lines[at - 1]
    indent = (" " * column if column is not None
              else body[: len(body) - len(body.lstrip())] or "  ")
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


def graded_theorems(challenge: str) -> int:
    """How many proofs are graded together. An answer slot is not one of them."""

    return sum(1 for line in challenge.splitlines() if PROOF_DECL.match(line))


def declaration_name(block: str) -> str:
    """The name a block declares at the top level, if it declares one.

    A fact two theorems share cannot live inside either one's proof."""

    for line in block.split("\n"):
        if line.strip():
            found = DECLARATION.match(line)
            return found.group(1) if found else ""
    return ""


CASE_TAG = re.compile(r"^case (\S+)\s*$", re.M)


def split_cursor(text: str, goal: str, index: int = 0) -> str:
    """One placeholder per goal, so each of them gets a turn of its own.

    A tactic that splits leaves several goals behind one `sorry`, and Lean then
    reports them all at the declaration. Tags are used only if there is one per
    goal; mixing the two forms in one split is what breaks."""

    goals = goal.count("⊢")
    tags = CASE_TAG.findall(goal)
    if goals < 2 or any(f"case {t} =>" in text for t in tags):
        return ""
    if len(tags) == goals:
        block = "\n".join(f"case {t} =>\n  sorry" for t in tags)
    else:
        block = "\n".join("· sorry" for _ in range(goals))
    return replace_cursor(text, block, index=index, trailing=False)[0]


def unwrap_own(block: str, names: Sequence[str]) -> str:
    """A block that restates the graded theorem is its body, wrongly framed.

    Measured on p09: with reasoning off the writer opens with the theorem header
    and, told the name is taken, opens with the same line minus `theorem`. A
    statement long enough to wrap kept its header off this path, and the whole
    re-declaration went to Lean as new: 481 turns of one run were that."""

    for name in names:
        head = re.compile(rf"\A\s*(?:private\s+)?(?:theorem|lemma)?\s*{re.escape(name)}\b"
                          r"[\s\S]*?:=\s*by[ \t]*\n")
        found = head.match(block)
        if found:
            return reindent(block[found.end():], "")
    return block


DECL_HEAD = re.compile(r"\A(.*?:=[ \t]*by)\b", re.S)


def as_goal(block: str) -> str:
    """The lemma's statement, with its proof handed back to the cursor.

    Measured on p09: the writer states the right lemma and proves it wrong in
    one shot. The statement is the part worth keeping; a `sorry` under it is a
    goal like any other."""

    found = DECL_HEAD.match(block)
    return f"{found.group(1)}\n  sorry" if found else ""


def prefixes(block: str) -> list[str]:
    """The block cut back one top-level step at a time, longest first.

    Measured on p09: every reply is a whole proof and one wrong lemma name
    throws away the nine lines that were right. A check costs 60ms and a reply
    costs seconds, so the cheap thing asks which prefix Lean will take."""

    lines = block.split("\n")
    body = [l for l in lines if l.strip()]
    if len(body) < 2:
        return []
    base = min(len(l) - len(l.lstrip()) for l in body)
    starts = [i for i, l in enumerate(lines)
              if l.strip() and len(l) - len(l.lstrip()) == base]
    return ["\n".join(lines[:at]).rstrip() for at in reversed(starts[1:])]


def proof_span(text: str, name: str) -> tuple[int, int] | None:
    """From a proof's header line to the line before the next column-0 text."""

    for found in PROOF_HEAD.finditer(text):
        if found.group(2) != name:
            continue
        start = text.rfind("\n", 0, found.start(1)) + 1
        at = text.find("\n", found.end()) + 1
        while 0 < at < len(text):
            line = text[at:text.find("\n", at) if text.find("\n", at) >= 0 else len(text)]
            if line.strip() and not line[0].isspace():
                break
            at = text.find("\n", at) + 1 if text.find("\n", at) >= 0 else len(text)
        return start, at if at > 0 else len(text)
    return None


def open_names(text: str) -> tuple[str, ...]:
    """Every proof that still holds a placeholder."""

    holes = [p.start() for p in placeholders(text)]
    named = []
    for name in root_names(text):
        span = proof_span(text, name)
        if span and any(span[0] <= h < span[1] for h in holes):
            named.append(name)
    return tuple(named)


def restate(text: str, name: str) -> tuple[str, int]:
    """The file with `name`'s proof cut back to its statement over one `sorry`,
    and that placeholder's index; (text, -1) when there is no such proof."""

    span = proof_span(text, name)
    head = DECL_HEAD.match(text[span[0]:span[1]]) if span else None
    if not head:
        return text, -1
    fresh = text[:span[0]] + head.group(1) + "\n  sorry\n\n" + text[span[1]:].lstrip("\n")
    return fresh, len([p for p in placeholders(fresh) if p.start() < span[0]])


def proof_body(block: str, name: str) -> str:
    """What a reply restating `name` says under its header."""

    body = unwrap_own(block, (name,))
    if body != block:
        return body
    head = DECL_HEAD.match(block)
    return reindent(block[head.end():], "") if head else block


def insert_above(text: str, name: str, block: str) -> str:
    """The block just above `name`'s declaration and its doc comment, so it sees
    every lemma already in the file. `insert_preamble` put a hoisted lemma above
    the lemma it cited: `Unknown identifier` twice in one p09 run."""

    found = next((m for m in PROOF_HEAD.finditer(text) if m.group(2) == name), None)
    if found is None:
        return insert_preamble(text, block)
    at = text.rfind("\n", 0, found.start(1)) + 1
    while at > 0:
        prev_start = text.rfind("\n", 0, at - 1) + 1
        prev = text[prev_start:at - 1]
        if not prev.strip() or DECL_START.match(prev):
            break
        at = prev_start
    return text[:at] + block.rstrip() + "\n\n" + text[at:]


def enclosing_name(text: str, index: int = 0) -> str:
    """The declaration the cursor is inside, which the writer keeps restating.

    Measured on p09: once a shared lemma is in the file, every reply about it
    comes back as the whole `theorem ... := by ...`, and the name is taken."""

    at = cursor(text, index)
    if at is None:
        return ""
    heads = [m for m in PROOF_HEAD.finditer(text) if m.start() < at.start()]
    return heads[-1].group(2) if heads else ""


def drop_own(block: str, names: Sequence[str]) -> str:
    """Keep the lemma a reply adds and drop the graded theorem it restates.

    Measured on p09: the writer states `p09_aux_mod` and then rewrites `p09_a`
    under it. Only the first is new; the second is `already been declared`."""

    lines = block.split("\n")
    for i, line in enumerate(lines):
        found = DECLARATION.match(line)
        if found and found.group(1) in names:
            return "\n".join(lines[:i]).rstrip()
    return block


HAVE_BODY = re.compile(r"^(\s*have\b.*?:=\s*)(\S.*)$", re.M)
UNKNOWN_NAME = re.compile(r"[Uu]nknown (identifier|constant)|environment does not contain")


def hand_to_search(block: str) -> str:
    """A `have` stated right and proved wrong: `exact?` names the lemma or nothing does.

    Measured on p09: a multi-line `have ... := by` left its old body dangling
    under the new one-line proof, and Lean answered with a syntax error."""

    lines, out, i = block.split("\n"), [], 0
    while i < len(lines):
        line = lines[i]
        i += 1
        found = HAVE_BODY.match(line)
        if not found:
            out.append(line)
            continue
        out.append(f"{found.group(1)}by exact?")
        depth = len(line) - len(line.lstrip())
        while i < len(lines) and (not lines[i].strip()
                                  or len(lines[i]) - len(lines[i].lstrip()) > depth):
            i += 1
    return "\n".join(out)
