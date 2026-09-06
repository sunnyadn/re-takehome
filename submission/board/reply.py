"""Reading a model's reply as the edits it proposes."""

from __future__ import annotations
import re
from typing import Sequence
from submission.framework import (DECLARATION, as_goal, normalise_steps, open_names, prefixes, proof_body, root_names)
from submission.replies import is_probe, screen_step

from submission.board.types import (OPENERS, CLOSERS, Board, Edit, Goal, HAVE_HEAD, HAVE_NAME, INTRO_LIKE, split_top)


LITERAL_MEMBER = re.compile(r"(\([^()]*\)|[A-Za-z_][\w']*) ∈ (\{[^{}|]*\})(?! :)")


def ascribe_literals(stmt: str) -> str:
    """A set literal after `∈` ascribed from the member's binder type: `(a, b) ∈
    {…}` with `(a b : ℤ)` becomes `(a, b) ∈ ({…} : Set (ℤ × ℤ))`. Lean drops the
    ascription when it prints a goal and cannot elaborate the literal without it."""

    types: dict[str, str] = {}
    for grp in re.findall(r"\(([^():]+) : ([^()]+(?:\([^()]*\)[^()]*)*)\)", stmt):
        for n in grp[0].split():
            types[n] = grp[1].strip()

    def fix(m: re.Match[str]) -> str:
        member, lit = m.group(1), m.group(2)
        names = re.findall(r"[A-Za-z_][\w']*", member)
        kinds = [types.get(n) for n in names]
        if not names or any(k is None for k in kinds):
            return m.group(0)
        typ = kinds[0] if len(kinds) == 1 else "(" + " × ".join(kinds) + ")"
        return f"{member} ∈ ({lit} : Set {typ})"
    return LITERAL_MEMBER.sub(fix, stmt)


def claim_of(have_statement: str) -> str:
    """The proposition in `have h : P`; "" when there is no top-level colon."""
    parts = split_top(have_statement, ":")
    return parts[1].strip() if parts and parts[0].startswith("have") else ""


SET_LITERAL = re.compile(r"^\(?\s*\{(.*)\}\s*(?::.*?)?\)?\s*$", re.S)


def set_elements(term: str) -> list[list[str]] | None:
    """The tuples of an explicit finite set literal, or None for any other term."""
    found = SET_LITERAL.match(term.strip())
    if not found or "|" in found.group(1):
        return None
    items, depth, buf = [], 0, ""
    for ch in found.group(1):
        if ch == "," and depth == 0:
            items.append(buf.strip()); buf = ""
            continue
        depth += (ch in OPENERS) - (ch in CLOSERS)
        buf += ch
    if buf.strip():
        items.append(buf.strip())
    out = []
    for it in items:
        inner = it.strip()
        if inner[:1] in "(⟨" and inner[-1:] in ")⟩":
            inner = inner[1:-1]
        parts, depth, buf = [], 0, ""
        for ch in inner:
            if ch == "," and depth == 0:
                parts.append(buf.strip()); buf = ""
                continue
            depth += (ch in OPENERS) - (ch in CLOSERS)
            buf += ch
        parts.append(buf.strip())
        out.append(parts)
    return out


MINE_CAP = 6


HAVE_ANY = re.compile(r"^\s*(have\b.*?)\s*:=")


def mine_statements(block: str, known: dict[str, str], withdrawn: Sequence[str]) -> list[str]:
    """The `have name : P` heads of a rejected block, in order, as facts to
    post with `sorry`: a reply is read for what it states, not only run as a
    script that stops at its first error. Measured on putnam_2018_a1 (v7.74):
    30 replies called the divisor technique and none reached Lean, every call
    sitting below the first error of a long reply. Statements below an intro-
    like line, already on the board, withdrawn, or reusing a name are left out."""
    out, seen, grown = [], set(known.values()), False
    base = min((len(l) - len(l.lstrip()) for l in normalise_steps(block).split("\n") if l.strip()),
               default=0)
    for line in normalise_steps(block).split("\n"):
        if not line.strip() or len(line) - len(line.lstrip()) != base:
            continue
        if INTRO_LIKE.match(line):
            grown = True
        head = HAVE_ANY.match(line)
        name = HAVE_NAME.match(line)
        if grown or not head or not name:
            continue
        claim = " ".join(claim_of(head.group(1)).split())
        if not claim or claim in known or claim in withdrawn or name.group(1) in seen:
            continue
        seen.add(name.group(1))
        out.append(f"{head.group(1)} := by")
        if len(out) >= MINE_CAP:
            break
    return out


def salvage(reply: str) -> str:
    """A reply cut mid-statement, less the statement it was cut in. Measured on
    rmo_2001_2: 37 of 70 step replies from one model ended at the token cap."""

    text = reply + ("\n```" if reply.count("```") % 2 else "")
    cuts = prefixes(screen_step(text, allow_sorry=True))
    return cuts[0] if cuts else ""


HAVE_OPEN = re.compile(r"^(\s*)(have|suffices|show|obtain)\b")


def fold_heads(block: str) -> str:
    """A statement split over several lines, joined onto its first line, so
    that every reader of the board (audit, lift, withdraw, restate) sees it.
    Lean does not mind the line length."""
    lines, out, i = block.split("\n"), [], 0
    while i < len(lines):
        line = lines[i]
        head = HAVE_OPEN.match(line)
        if head and ":=" not in line:
            depth, j, joined = len(head.group(1)), i + 1, line.rstrip()
            while j < len(lines) and lines[j].strip() and \
                    len(lines[j]) - len(lines[j].lstrip()) > depth:
                joined += " " + lines[j].strip()
                if ":=" in lines[j]:
                    j += 1
                    break
                j += 1
            if ":=" in joined:
                out.append(joined)
                i = j
                continue
        out.append(line)
        i += 1
    return "\n".join(out)


BIG_OPERATOR_IN = re.compile(r"([∑∏]\s*(?:\([^()]*\)|[^\s,()]+))\s+in\s+")


def dialect(block: str) -> str:
    """Spellings the models learned that Lean 4 Mathlib does not read: `∑ x in
    s` is `∑ x ∈ s`, and a tactic line does not end in a comma. Lexical only;
    a comma inside an open bracket or continuing a list on the next line stays."""
    lines = BIG_OPERATOR_IN.sub(r"\1 ∈ ", block).split("\n")
    for i, line in enumerate(lines):
        body = line.rstrip()
        if not body.endswith(",") or "--" in body:
            continue
        balanced = sum(body.count(c) for c in OPENERS) == sum(body.count(c) for c in CLOSERS)
        nxt = lines[i + 1] if i + 1 < len(lines) else ""
        continues = nxt.strip() and len(nxt) - len(nxt.lstrip()) > len(line) - len(line.lstrip())
        if balanced and not continues:
            lines[i] = body[:-1]
    return "\n".join(lines)


CASE_LINE = re.compile(r"^(\s*)case\s+([\w.]+)\s*=>\s*$")


def unwrap(block: str, text: str, goal: Goal) -> str:
    """A reply that opens by rewriting the context the goal sits in (its `case`
    tag, the `have` it is the body of) loses that opening; the body is the step."""
    lines = text.split("\n")
    above = [l for l in lines[:goal.line - 1] if l.strip()
             and len(l) - len(l.lstrip()) < len(goal.indent)]
    context = {" ".join(l.split()) for l in above}
    out = block.split("\n")
    while out and out[0].strip():
        first = " ".join(out[0].split())
        head = CASE_LINE.match(out[0]) or HAVE_HEAD.match(out[0])
        if not head or first not in context:
            break
        depth = len(out[0]) - len(out[0].lstrip())
        rest = out[1:]
        inner = min((len(l) - len(l.lstrip()) for l in rest if l.strip()), default=depth)
        if inner <= depth:
            break
        out = [l[inner - depth:] if l.strip() else l for l in rest]
    return "\n".join(out)


def interpret(reply: str, board: Board, goal: Goal, graded: Sequence[str]) -> list[Edit]:
    """Read a reply once, as proofs of whatever it names."""

    block = dialect(screen_step(reply, allow_sorry=True))
    if not block:
        return []
    if is_probe(block):
        return [Edit("probe", block)]
    lines, edits, plain, current = block.split("\n"), [], [], None
    for line in lines + [None]:
        head = DECLARATION.match(line) if line is not None else None
        if line is not None and not head:
            (current[1] if current else plain).append(line)
            continue
        if current:
            name = current[0]
            raw = "\n".join([current[2]] + current[1])
            if name in open_names(board.text):
                edits.append(Edit("prove", proof_body(raw, name), name))
            elif name in root_names(board.text) or name in graded:
                edits.append(Edit("drop", "", name))
            else:
                edits.append(Edit("hoist", proof_body(raw, name), name, as_goal(raw) or raw))
        current = [head.group(1), [], line] if head else None
    plain_body = "\n".join(plain).strip()
    if plain_body:
        edits.insert(0, Edit("step", plain_body))
    return edits

