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


def cursor(text: str) -> re.Match[str] | None:
    """The topmost placeholder line, which is the active goal."""

    return PLACEHOLDER.search(text)


def is_done(text: str) -> bool:
    return cursor(text) is None


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def render(text: str) -> tuple[str, int]:
    """The file to send, and the 1-based line the `skip` sits on (0 if none)."""

    match = cursor(text)
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


def replace_cursor(text: str, block: str, *, trailing: bool = True) -> tuple[str, tuple[int, int]]:
    """Put a step where the cursor is, leaving a placeholder for what follows."""

    match = cursor(text)
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


UNSOLVED = "unsolved goals"
HEARTBEAT = "maximum number of heartbeats"
NO_GOALS = "no goals to be solved"


def message_text(message: Any) -> str:
    data = message.get("data", "") if isinstance(message, dict) else ""
    return data if isinstance(data, str) else str(data)


def classify(messages: Sequence[Any]) -> tuple[list[Any], list[Any], list[Any], list[Any]]:
    """Progress, surplus placeholder, too expensive, real failure."""

    progress, surplus, expensive, failures = [], [], [], []
    for m in messages:
        if not isinstance(m, dict) or m.get("severity") != "error":
            continue
        text = message_text(m)
        if UNSOLVED in text:
            progress.append(m)
        elif NO_GOALS in text:
            surplus.append(m)
        elif HEARTBEAT in text:
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
    """The goal an `unsolved goals` error carries, after the last turnstile."""

    text = message_text(message)
    return text.split("⊢", 1)[1].strip() if "⊢" in text else ""


def cursor_goal(messages: Sequence[Any], cursor_line: int) -> str:
    """The active goal: the `unsolved goals` message sitting on the `skip`."""

    for m in classify(messages)[0]:
        if message_line(m) == cursor_line:
            return goal_text(m)
    return ""


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
