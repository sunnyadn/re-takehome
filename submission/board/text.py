"""Reading and rewriting the Lean text the board holds."""

from __future__ import annotations
import re
from typing import Sequence
from submission.cells import marker, strip_markers
from submission.techniques import strip_techniques, without_techniques
from submission.framework import (DECLARATION, DECL_HEAD, line_of, normalise_steps, placeholders, proof_span, reindent, root_names)

from submission.board.types import (OPENERS, CLOSERS, Goal, HAVE_HEAD, HAVE_NAME, INTRO_LIKE, groups, hypotheses, owner)
from submission.board.reply import claim_of, fold_heads, unwrap


# A goal whose statement the model wrote, as opposed to one Lean derived from an
# `intro` or `rcases`. Measured: auditing every new goal was 48% of the wall
# clock under the lock, and every false statement caught was a `have`.
STATED_HEAD = re.compile(r"^(\s*)((?:have|suffices|show|obtain)\b.*?)\s*:=\s*by\s*$")


def split_statement(stmt: str) -> tuple[list[str], str] | None:
    """Binder groups and target of a stated goal; None if it reads unusually."""
    groups, depth, buf = [], 0, ""
    for i, ch in enumerate(stmt):
        if depth == 0 and ch == ":":
            return groups, stmt[i + 1:].strip()
        if depth == 0 and not ch.isspace() and ch not in OPENERS:
            return None
        depth += (ch in OPENERS) - (ch in CLOSERS)
        buf += ch
        if depth == 0 and ch in CLOSERS:
            groups.append(buf.strip())
            buf = ""
    return None


def enclosing_have(lines: Sequence[str], goal: Goal) -> tuple[int | None, re.Match | None]:
    """The nearest shallower line above the goal, and its `have ... := by` head."""
    i = goal.line - 1
    above = next((j for j in range(i - 1, -1, -1) if lines[j].strip()
                  and len(lines[j]) - len(lines[j].lstrip()) < len(goal.indent)), None)
    return above, (HAVE_HEAD.match(lines[above]) if above is not None else None)


def drop_declaration(text: str, decl: str) -> str:
    """The file without one declaration (its head, its proof, its doc comment)."""
    span = proof_span(text, decl)
    if not span:
        return text
    start = text.rfind("\n\n", 0, span[0])
    start = 0 if start < 0 else start + 2
    return text[:start] + text[span[1]:]


def shed_unreferenced(text: str, graded: Sequence[str]) -> tuple[str, list[str]]:
    """The file without the open declarations nothing else uses: a helper a
    model proposed and never called must not hold a finished proof back.
    Measured on p09 (v7.95): both graded theorems closed, a shared lemma with
    a sorry stayed, and the run worked it for 10 more minutes."""
    shed: list[str] = []
    while True:
        open_decls = {owner(text, line_of(text, m.start())) for m in placeholders(text)}
        for decl in root_names(text):
            span = proof_span(text, decl)
            if decl in graded or decl not in open_decls or not span:
                continue
            head = text.rfind("\n\n", 0, span[0])
            rest = strip_techniques(text[:max(head, 0)] + text[span[1]:])
            if re.search(rf"\b{re.escape(decl)}\b", rest):
                continue
            text = drop_declaration(text, decl)
            shed.append(decl)
            break
        else:
            return text, shed


def is_stated(lines: Sequence[str], goal: Goal) -> bool:
    """Whether the goal is the body of a statement the model wrote."""
    i = goal.line - 1
    above = next((j for j in range(i - 1, -1, -1) if lines[j].strip()
                  and len(lines[j]) - len(lines[j].lstrip()) < len(goal.indent)), None)
    if above is None:
        return False
    if STATED_HEAD.match(lines[above]):
        return True
    # A declaration's own root goal (the placeholder right under its head) is a
    # statement the model wrote when the declaration was hoisted; a goal deeper
    # in a graded theorem's body is not.
    return DECLARATION.match(lines[above]) is not None and above == i - 1


def enclosing_chain(lines: Sequence[str], goal: Goal) -> list[tuple[int, re.Match]]:
    """Every `have ... := by` the goal sits inside, nearest first."""
    chain, probe = [], goal
    while True:
        above, head = enclosing_have(lines, probe)
        if not head:
            return chain
        chain.append((above, head))
        probe = Goal(above + 1, head.group(1), goal.decl, goal.text)


def context_grows(lines: Sequence[str], chain: Sequence[tuple[int, re.Match]], depth: int,
                  goal: Goal) -> bool:
    """Whether a line in the bodies the goal sits in, above it and inside the
    `have` at `chain[depth - 1]`, adds hypotheses. A fact posted below such a
    line may be true only under them, and Lean cannot say so once it is moved
    above the `have`: measured on rmo_2000_2, `y^3 < (x+2)^3` was posted under
    `intro hxle : x ≤ 8`, lifted above `h1`, then refuted at (9, 11) and the
    right route withdrawn with it."""
    for i in range(depth - 1, -1, -1):
        outer, _ = chain[i]
        inner_line, inner_indent = ((chain[i - 1][0], len(chain[i - 1][1].group(1))) if i > 0
                                    else (goal.line - 1, len(goal.indent)))
        for l in lines[outer + 1:inner_line]:
            if l.strip() and len(l) - len(l.lstrip()) == inner_indent and INTRO_LIKE.match(l):
                return True
    return False


def split_facts(block: str) -> tuple[list[str], str]:
    """The `have ... := by sorry` statements at the top level of a block, and
    the block without them. A statement below an `intro`-like line of the
    block stays in the block: it may hold only under what that line named."""
    lines = normalise_steps(block).split("\n")
    body = [l for l in lines if l.strip()]
    base = min((len(l) - len(l.lstrip()) for l in body), default=0)
    facts, rest, i, grown = [], [], 0, False
    while i < len(lines):
        line = lines[i]
        head = HAVE_HEAD.match(line)
        nxt = lines[i + 1] if i + 1 < len(lines) else ""
        grown = grown or (len(line) - len(line.lstrip()) == base and bool(INTRO_LIKE.match(line)))
        if head and not grown and len(head.group(1)) == base and nxt.strip() == "sorry" \
                and len(nxt) - len(nxt.lstrip()) > base:
            facts.append(f"{line.strip()}\n  sorry")
            i += 2
            continue
        rest.append(line)
        i += 1
    return facts, "\n".join(rest).strip("\n")


def restates(block: str, claims: Sequence[str]) -> bool:
    """Whether a block posts, at its own top level, a `have` whose claim is one
    of these. A repeat inside a new claim's body is an alias, not a post."""
    gone = {" ".join(c.split()) for c in claims}
    lines = [l for l in block.split("\n") if l.strip()]
    top = min((len(l) - len(l.lstrip()) for l in lines), default=0)
    for line in lines:
        if len(line) - len(line.lstrip()) != top:
            continue
        head = HAVE_HEAD.match(line) or re.match(r"^(\s*)(have\b.*?)\s*:=", line)
        if head and " ".join(claim_of(head.group(2).strip()).split()) in gone:
            return True
    return False


def proved_facts(text: str, goal: Goal) -> dict[str, str]:
    """Claim -> name for every proved `have` (no placeholder in its block) that
    is in scope at the goal: above it, and its block not yet closed."""
    lines = text.split("\n")
    out: dict[str, str] = {}
    for i in range(goal.line - 1):
        head = HAVE_HEAD.match(lines[i])
        name = HAVE_NAME.match(lines[i]) if head else None
        if not (head and name) or len(head.group(1)) > len(goal.indent):
            continue
        depth = len(head.group(1))
        j = i + 1
        while j < len(lines) and (not lines[j].strip()
                                  or len(lines[j]) - len(lines[j].lstrip()) > depth):
            j += 1
        between = [l for l in lines[j:goal.line - 1] if l.strip()]
        if any(len(l) - len(l.lstrip()) < depth for l in between):
            continue
        if not any(l.strip() == "sorry" for l in lines[i + 1:j]):
            out[" ".join(claim_of(head.group(2).strip()).split())] = name.group(1)
    return out


def stated_facts(text: str, decl: str) -> dict[str, str]:
    """Claim -> name for every `have` already inside a declaration's proof."""
    span = proof_span(text, decl)
    out: dict[str, str] = {}
    for line in (text[span[0]:span[1]] if span else "").split("\n"):
        head = HAVE_HEAD.match(line)
        name = HAVE_NAME.match(line) if head else None
        if head and name:
            out[" ".join(claim_of(head.group(2).strip()).split())] = name.group(1)
    return out


def withdraw(text: str, goal: Goal) -> tuple[str, str]:
    """The file with the `have` enclosing this goal, and the rest of its block,
    cut back to one `sorry`; the withdrawn statement second. ("", "") when the
    nearest shallower line above the goal is not a `have ... := by`."""
    lines = text.split("\n")
    i = goal.line - 1
    above, head = enclosing_have(lines, goal)
    if not head:
        return "", ""
    indent = head.group(1)
    end = i + 1
    while end < len(lines) and (not lines[end].strip()
                                or len(lines[end]) - len(lines[end].lstrip()) >= len(indent)):
        end += 1
    while end - 1 > i and not lines[end - 1].strip():
        end -= 1
    return "\n".join(lines[:above] + [indent + "sorry"] + lines[end:]), head.group(2).strip()


def withdraw_only(text: str, goal: Goal) -> tuple[str, str]:
    """Like `withdraw`, but only the `have` and its own body go; what follows
    in the block stays. The block keeps a `sorry` if nothing else is left."""
    lines = text.split("\n")
    above, head = enclosing_have(lines, goal)
    if not head:
        return "", ""
    indent = head.group(1)
    end = above + 1
    while end < len(lines) and (not lines[end].strip()
                                or len(lines[end]) - len(lines[end].lstrip()) > len(indent)):
        end += 1
    rest = lines[end:]
    keeps = rest and rest[0].strip() and len(rest[0]) - len(rest[0].lstrip()) == len(indent)
    middle = [] if keeps else [indent + "sorry"]
    return "\n".join(lines[:above] + middle + rest), head.group(2).strip()


def settled_inside(text: str, goal: Goal) -> int:
    """Proved facts around the goal: `have`s with no placeholder left inside the
    nearest enclosing `have` (walking out through `case` and bullet lines), or
    inside the declaration when no `have` encloses it. What a withdrawal or a
    restart would throw away."""
    lines = text.split("\n")
    i, depth = goal.line - 1, len(goal.indent)
    start, top = None, 0
    while i > 0:
        i -= 1
        line = lines[i]
        if not line.strip():
            continue
        d = len(line) - len(line.lstrip())
        if d >= depth:
            continue
        depth = d
        if HAVE_HEAD.match(line) or DECL_HEAD.match(line) or d == 0:
            start, top = i, d
            break
    if start is None:
        return 0
    end = start + 1
    while end < len(lines) and (not lines[end].strip()
                                or len(lines[end]) - len(lines[end].lstrip()) > top):
        end += 1
    count = 0
    for k in range(start + 1, end):
        m = HAVE_HEAD.match(lines[k])
        if not m or k + 1 == goal.line:
            continue
        j, d = k + 1, len(m.group(1))
        body = []
        while j < end and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip()) > d):
            body.append(lines[j]); j += 1
        if body and not any(l.strip() in ("sorry", "skip") for l in body):
            count += 1
    return count


def inflated(before: str, after: str) -> float:
    """How much larger the hypotheses both goals share became, when the growth
    is one new bracketed expression repeated 3 times or more: a rewrite that
    unfolds a variable everywhere. Unfolding a set literal is not repetition."""
    old, new = hypotheses(before), hypotheses(after)
    shared = [n for n in old if n in new]
    was = sum(len(old[n]) for n in shared)
    now_text = "\n".join(new[n] for n in shared)
    old_text = "\n".join(old[n] for n in shared)
    if was < 40:
        return 1.0
    fresh = [g for g in set(groups(now_text)) if g not in old_text]
    if not any(now_text.count(g) >= 3 for g in fresh):
        return 1.0
    return len(now_text) / was


def put(text: str, goal: Goal, block: str, trailing: bool = True,
        cell_id: int | None = None) -> tuple[str, tuple[int, int]]:
    """The block where the goal's placeholder is (under a cell marker when it
    gets one), and the lines it now covers."""

    lines = text.split("\n")
    body = reindent(normalise_steps(fold_heads(unwrap(block, text, goal))), goal.indent)
    if trailing:
        body = f"{body}\n{goal.indent}sorry"
    if cell_id is not None:
        body = f"{marker(goal.indent, cell_id)}\n{body}"
    lines[goal.line - 1] = body
    return "\n".join(lines), (goal.line, goal.line + body.count("\n"))


def view(source: str, decl: str) -> tuple[str, int]:
    """The file as the model should read it: every statement in full, and only
    the body of the declaration being worked on. The `skip` line is recomputed.
    Measured on p09: the last 8000 chars of the file cut the shared lemma's
    statement off the top, and the model cited a lemma it could not see."""

    out, kept_lines = [], 0
    for name in root_names(source):
        span = proof_span(source, name)
        if not span or name == decl:
            continue
        body = source[span[0]:span[1]]
        head = DECL_HEAD.match(body)
        if not head or "skip" in body or "sorry" in body:
            continue
        lines = len([l for l in body[head.end():].split("\n") if l.strip()])
        out.append((span, f"{head.group(1)}\n  -- proved, {lines} lines elided\n\n"))
    for (start, end), replacement in sorted(out, reverse=True):
        source = source[:start] + replacement + source[end:]
    source, _ = without_techniques(strip_markers(source))
    at = next((i for i, l in enumerate(source.split("\n"), start=1) if l.strip() == "skip"), 0)
    return source, at

