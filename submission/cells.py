"""Cells: a marked block in the one file the models read becomes its own
declaration (`theorem vm_cell_N <statement> := by …`) in the file Lean checks
and the comparator compiles; one declaration, one budget. See docs/CELLS.md."""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Sequence

from submission.framework import (DECL_HEAD, PLACEHOLDER, PROOF_HEAD, proof_span,
                                  line_of)

MARK = re.compile(r"^([ \t]*)-- cell (\d+)[ \t]*$")
BUDGET_ASK = re.compile(r"^set_option maxHeartbeats (\d+) in\b")
# One placeholder asks Lean two things: state this goal (info) and report it
# as open (error). `*` keeps every hypothesis (measured: plain extract_goal
# dropped `h_mem : 6 < 7`, and steps using it failed); numerals are typed.
CELL_PROBE = "(set_option pp.numericTypes true in extract_goal *); focus skip"
LEMMA = "vm_cell_"


def marker(indent: str, cell_id: int) -> str:
    return f"{indent}-- cell {cell_id}"


def strip_markers(text: str) -> str:
    return "\n".join(l for l in text.split("\n") if not MARK.match(l))


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip())


@dataclass
class Span:
    """A marked block: marker line, last line (1-based, inclusive), indent."""

    id: int
    start: int
    end: int
    indent: int
    children: list["Span"] = field(default_factory=list)

    def holds(self, line: int) -> bool:
        return self.start <= line <= self.end


def spans(text: str) -> list[Span]:
    """Every marked span, outermost first, children nested. A marker with no
    block under it is not a span."""

    lines = text.split("\n")
    flat: list[Span] = []
    for i, line in enumerate(lines, start=1):
        found = MARK.match(line)
        if not found:
            continue
        indent = len(found.group(1))
        end = i
        for j in range(i + 1, len(lines) + 1):
            ln = lines[j - 1]
            if ln.strip() and _indent(ln) < indent:
                break
            if ln.strip():
                end = j
        if end > i:
            flat.append(Span(int(found.group(2)), i, end, indent))
    roots: list[Span] = []
    stack: list[Span] = []
    for s in flat:
        while stack and not stack[-1].holds(s.start):
            stack.pop()
        (stack[-1].children if stack else roots).append(s)
        stack.append(s)
    return roots


def all_spans(text: str) -> list[Span]:
    out: list[Span] = []

    def walk(items: Sequence[Span]) -> None:
        for s in items:
            out.append(s)
            walk(s.children)
    walk(spans(text))
    return out


def enclosing(text: str, line: int) -> Span | None:
    """The innermost span holding the line, the marker line included."""

    best = None
    for s in all_spans(text):
        if s.holds(line) and (best is None or s.start > best.start):
            best = s
    return best


def reset_cell(text: str, span: Span) -> str:
    """The cell's block gone, its goal back as one placeholder."""

    lines = text.split("\n")
    return "\n".join(lines[:span.start - 1] + [" " * span.indent + "sorry"] + lines[span.end:])


def dissolve(text: str, cell_id: int) -> str:
    """The marker gone: the block stays where it is, part of what encloses it."""

    return "\n".join(l for l in text.split("\n")
                     if not (MARK.match(l) and int(MARK.match(l).group(2)) == cell_id))


BINDER_GROUP = re.compile(r"\(([^():]+?) : ")


def explicit_binders(statement: str) -> list[tuple[str, str]]:
    """(name, type) for every explicit binder of a statement, in order."""

    depth, groups, cur = 0, [], ""
    for ch in statement:
        if depth == 0 and ch == ":":
            break
        if ch == "(":
            depth += 1
            if depth == 1:
                cur = ""
                continue
        elif ch == ")":
            depth -= 1
            if depth == 0:
                groups.append(cur)
                continue
        if depth >= 1:
            cur += ch
    out: list[tuple[str, str]] = []
    for g in groups:
        if " : " in g:
            names, typ = g.split(" : ", 1)
            out += [(n, typ.strip()) for n in names.split()]
    return out


def explicit_names(statement: str) -> list[str]:
    return [n for n, _ in explicit_binders(statement)]


DATA_TYPE = re.compile(r"^(?:ℕ|ℤ|ℚ|ℝ|ℂ|Prop|Type\b.*|Sort\b.*|Fin\b.*|Finset\b.*|Set\b.*|List\b.*|Multiset\b.*"
                       r"|[ℕℤℚℝℂ] → .*|.* × .*)$")
PROP_TOKEN = re.compile(r"[∀∃=<≤>≥≠∣∈¬∧∨↔→]|\bPrime\b|\bAntitone\b|\bMonotone\b|\bIs[A-Z]")


def link(cell_id: int, statement: str) -> str:
    """The parent's call of a cell: data binders by name and hypotheses by
    their type (`‹_›`, which cannot pick the wrong one once the data is
    fixed), then all by name, then apply/assumption. Measured on rmo_2000_6:
    apply/assumption alone assigned `?a := b` from `hb : 0 < b` 356 times."""

    binders = explicit_binders(statement)
    if not binders:
        return f"exact {LEMMA}{cell_id}"
    typed = " ".join(n if DATA_TYPE.match(t) and not PROP_TOKEN.search(t.replace("ℕ → ℝ", "")) else "‹_›"
                     for n, t in binders)
    named = " ".join(n for n, _ in binders)
    return (f"first | (exact {LEMMA}{cell_id} {typed}) | (exact {LEMMA}{cell_id} {named}) "
            f"| (apply {LEMMA}{cell_id} <;> assumption)")


class Cells:
    """Statements by cell id, for the whole run; ids never repeat."""

    def __init__(self) -> None:
        self.statements: dict[int, str] = {}
        self.next_id = 1

    def new(self, statement: str) -> int:
        cell_id = self.next_id
        self.next_id += 1
        self.statements[cell_id] = statement
        return cell_id


@dataclass
class Rendered:
    text: str
    lines: list[int]                 # rendered line (0-based) -> file line (1-based)
    region: tuple[int, int] | None   # file lines of the focused unit


def render_check(text: str, cells: Cells, focus: int | str | None = None,
                 probes: bool = True) -> Rendered:
    """Every marked span as a declaration before its proof, children first, a
    link (`apply vm_cell_N <;> assumption`) where it stood; with a focus (cell
    id or proof name) everything else is a stub; probes off = delivered file."""

    lines = text.split("\n")
    out: list[tuple[str, int]] = []
    region: tuple[int, int] | None = None
    proofs = [(name, proof_span(text, name)) for name in PROOF_HEAD_names(text)]
    proofs = [(n, (line_of(text, s[0]), line_of(text, max(s[1] - 1, s[0]))))
              for n, s in proofs if s]
    tree = spans(text)

    def placeholder(line_no: int, ln: str) -> str:
        found = PLACEHOLDER.match(ln)
        if found and probes:
            return f"{found.group(1)}{CELL_PROBE}"
        return ln

    def body_lines(a: int, b: int, children: Sequence[Span], shift: int) -> list[tuple[str, int]]:
        """File lines a..b with each child span replaced by its link."""
        got: list[tuple[str, int]] = []
        i = a
        kids = sorted(children, key=lambda s: s.start)
        while i <= b:
            kid = next((k for k in kids if k.start == i), None)
            if kid:
                got.append((" " * max(kid.indent - shift, 0) + link(kid.id, cells.statements.get(kid.id, "")), kid.start))
                i = kid.end + 1
                continue
            ln = lines[i - 1]
            if ln.strip():
                ln = ln[shift:] if _indent(ln) >= shift else ln.lstrip()
                ln = placeholder(i, ln)
            got.append((ln, i))
            i += 1
        return got

    def emit_cell(s: Span, focused: bool) -> None:
        stmt = cells.statements.get(s.id, "")
        head = f"theorem {LEMMA}{s.id} {stmt} := by"
        # A block that asks for a heartbeat budget gets it on its own declaration
        # (the tactic-level option never bound anything; measured in v4.32).
        asked = BUDGET_ASK.match(lines[s.start].strip()) if s.start < len(lines) else None
        if asked:
            out.append((f"set_option maxHeartbeats {asked.group(1)} in", s.start))
        out.append((head, s.start))
        if focused:
            out.extend(body_lines(s.start + 1, s.end, s.children, s.indent - 2))
        else:
            out.append(("  sorry", s.start))
        out.append(("", s.end))

    def emit_all(items: Sequence[Span], focus_id: int | None) -> None:
        # Children first: a parent's link names them.
        for s in sorted(items, key=lambda s: s.start, reverse=True):
            emit_all(s.children, focus_id)
            emit_cell(s, focus is None or s.id == focus_id)

    focus_id = focus if isinstance(focus, int) else None
    i = 1
    while i <= len(lines):
        proof = next(((n, ab) for n, ab in proofs if ab[0] == i), None)
        if proof is None:
            out.append((lines[i - 1], i))
            i += 1
            continue
        name, (a, b) = proof
        inside = [s for s in tree if a <= s.start <= b]
        emit_all(inside, focus_id)
        head_text = "\n".join(lines[a - 1:b])
        head = DECL_HEAD.match(head_text)
        head_len = head.group(1).count("\n") + 1 if head else 1
        own = focus is None or focus == name
        if focus_id is not None:
            own = False
            region_span = next((s for s in all_spans(text) if s.id == focus_id), None)
            if region_span is not None and a <= region_span.start <= b:
                region = (region_span.start, region_span.end)
        elif focus == name:
            region = (a, b)
        if own or not head:
            out.extend(body_lines(a, b, inside, 0))
        else:
            for k in range(a, a + head_len):
                out.append((lines[k - 1], k))
            out.append(("  sorry", a + head_len - 1))
            for k in range(a + head_len, b + 1):
                if not lines[k - 1].strip():
                    out.append(("", k))
        i = b + 1
    return Rendered("\n".join(t for t, _ in out), [n for _, n in out], region)


def PROOF_HEAD_names(text: str) -> list[str]:
    return [m.group(2) for m in PROOF_HEAD.finditer(text)]


def remap(messages: Sequence[dict[str, Any]], lines: Sequence[int]) -> list[dict[str, Any]]:
    """Messages moved from rendered lines back to file lines."""

    out = []
    for m in messages:
        if not isinstance(m, dict):
            out.append(m)
            continue
        m = dict(m)
        for key in ("pos", "endPos"):
            pos = m.get(key)
            if isinstance(pos, dict) and isinstance(pos.get("line"), int):
                at = pos["line"]
                m[key] = dict(pos, line=lines[at - 1] if 1 <= at <= len(lines) else at)
        out.append(m)
    return out


def modular(text: str, cells: Cells) -> str:
    """The delivered form: cells as declarations, no probes, no markers."""

    return render_check(text, cells, focus=None, probes=False).text
