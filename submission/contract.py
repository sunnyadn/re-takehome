"""What the grader accepts, and the shape the file has to be in.

The predicates decide whether a candidate would score at all: banned
constructs, a drifted statement, a forbidden axiom, an unfilled answer slot.
The rest is the surgery that gets the challenge into that shape, and the
reading of what Lean and the harness say back."""

from __future__ import annotations

import copy
import dataclasses
import re
from typing import Any, Sequence

from re_harness import LLMCallError
from re_harness.llm import REFUSED_BEFORE_GENERATION
from re_harness.lean import numeric_answers_are_literals
from submission.config import FEEDBACK_CHARS
from submission.techniques import PREAMBLE_MARK, preamble


NAT_POW_LINE = "attribute [instance 2000] instPowNat"


NUMERAL_EXPONENT = re.compile(r"\^ (\d+)(?![\d.])")


STATEMENT = re.compile(r"((?:theorem|lemma)\s+[\w'.]+)(.*?)(:=[ \t]*by\b)", re.S)


def type_exponents(text: str) -> str:
    """`x ^ 2` becomes `x ^ (2 : ℕ)` in every theorem statement. Under the
    challenge's own imports the numeral exponent elaborates through core's
    `instPowNat`; under `import Mathlib` a default instance routes it through
    `Monoid.npow`, and the comparator then sees two different statements."""

    return STATEMENT.sub(lambda m: m.group(1) + NUMERAL_EXPONENT.sub(r"^ (\1 : ℕ)", m.group(2))
                         + m.group(3), text)


def normalise_imports(source: str, fallback: str) -> str:
    """The challenge's own imports, kept, plus `import Mathlib` for the tactics.

    Measured on rmo_2000_6 (2026-09-03): a proof the REPL and `lake build`
    both accepted scored 0, "Challenge and solution theorem statement do not
    match", because `import Mathlib` alone made `a ^ 2` elaborate through
    `Monoid.npow` where the challenge's `import Mathlib.Data.Nat.Basic` used
    `instPowNat`. With the original imports kept, `instPowNat` raised above
    the default instance and numeral exponents typed, the comparator passes."""

    lines = source.splitlines()
    imports: list[str] = []
    for line in lines:
        if line.lstrip().startswith("import ") and line.strip() not in imports:
            imports.append(line.strip())
    body = "\n".join(line for line in lines if not line.lstrip().startswith("import ")).strip()
    if not body:
        return fallback
    if "import Mathlib" not in imports:
        imports.append("import Mathlib")
    if any(i != "import Mathlib" for i in imports):
        if NAT_POW_LINE not in body:
            body = NAT_POW_LINE + "\n\n" + body
        body = type_exponents(body)
    return "\n".join(imports) + "\n\n" + body + "\n"


def with_preamble(text: str) -> str:
    """The technique tactics (techniques.py), defined once after the header
    of a normalised file: imports, then the instance line if any."""
    if PREAMBLE_MARK in text:
        return text
    lines = text.split("\n")
    k = max((i for i, l in enumerate(lines) if l.startswith("import ") or l == NAT_POW_LINE), default=-1)
    return "\n".join(lines[:k + 1] + ["", preamble()] + lines[k + 1:])


FENCE_LINE = re.compile(r"^\s*```.*$", re.MULTILINE)


def strip_fences(block: str) -> str:
    """Remove fence lines a capture swallowed.

    One leftover backtick rejects the whole file."""

    return FENCE_LINE.sub("", block)


BANNED = re.compile(r"\b(sorry|sorryAx|admit|native_decide|unsafe)\b|^\s*axiom\s", re.MULTILINE)


NAT_ANSWER_SLOT = re.compile(r"^\s*abbrev\s+([A-Za-z_][\w']*)\s*:\s*\u2115\s*:=", re.MULTILINE)


DECL = re.compile(r"^\s*(?:theorem|lemma|abbrev|def)\s+([A-Za-z_][\w']*)", re.MULTILINE)


AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")


PERMITTED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


def banned_constructs(source: str) -> list[str]:
    """The Comparator permits only propext, Classical.choice and Quot.sound, so
    these compile against the REPL and still score zero."""

    return sorted({m.group(0).strip() for m in BANNED.finditer(source)})


def declared_names(challenge: str) -> tuple[str, ...]:
    """Every declaration the Comparator will look at."""

    return tuple(dict.fromkeys(DECL.findall(challenge)))


def statement_headers(source: str) -> dict[str, str]:
    """Each declaration's text up to its `:=`, whitespace normalised.

    Editing a header scores zero however well the proof compiles."""

    headers: dict[str, str] = {}
    name = None
    buffer: list[str] = []
    for line in source.splitlines():
        match = DECL.match(line)
        if match:
            if name and name not in headers:
                headers[name] = " ".join(" ".join(buffer).split())
            name, buffer = match.group(1), []
        if name is None or line.lstrip().startswith("--"):
            continue
        head, sep, _rest = line.partition(":=")
        buffer.append(head)
        if sep:
            headers[name] = " ".join(" ".join(buffer).split())
            name, buffer = None, []
    return headers


def statement_drift(challenge: str, candidate: str) -> list[str]:
    """Names the candidate dropped or reworded."""

    # the header the agent writes is the challenge's after normalise_imports
    # (typed numeral exponents under narrow imports), so compare against that
    original = statement_headers(normalise_imports(challenge, challenge))
    now = statement_headers(candidate)
    faults = []
    for name, header in original.items():
        if name not in now:
            faults.append(f"{name} is missing, the grader needs it byte-identical")
        elif now[name] != header:
            faults.append(f"{name} was reworded, restore it exactly as the challenge has it")
    return faults


def forbidden_axioms(messages: Sequence[dict[str, Any]]) -> list[str]:
    """Read `#print axioms` output. A denylist cannot work here, because
    `native_decide` and `bv_decide` mint a fresh axiom name per computation."""

    bad: set[str] = set()
    for m in messages:
        for _decl, axioms in AXIOM_LINE.findall(str(m.get("data", ""))):
            bad |= {a.strip() for a in axioms.split(",") if a.strip()} - PERMITTED_AXIOMS
    return sorted(bad)


def answer_names(challenge: str) -> tuple[str, ...]:
    """Nat answer slots, which must end up as plain decimal literals."""

    return tuple(NAT_ANSWER_SLOT.findall(challenge))


def scoring_faults(source: str, names: Sequence[str], challenge: str = "") -> list[str]:
    """What the Comparator would reject even though Lean accepted the file."""

    faults = [f"remove {c}, the grader rejects it" for c in banned_constructs(source)]
    if challenge:
        faults.extend(statement_drift(challenge, source))
    if names:
        _, errors = numeric_answers_are_literals(source, tuple(names))
        faults.extend(errors)
    return faults


def grade(source: str, check: Any, names: Sequence[str],
          challenge: str) -> tuple[list[str], int]:
    """What the grader would hold against this file, and how much."""

    faults = scoring_faults(source, names, challenge)
    faults += [f"{a} is not a permitted axiom, the grader rejects it"
               for a in forbidden_axioms(check.messages)]
    return faults, len(error_messages(check.messages)) + len(faults)


IMPORT_HEAD = re.compile(r"^\s*import\s")


def import_lines(source: str) -> int:
    return sum(1 for l in source.splitlines() if IMPORT_HEAD.match(l))


class FileCoordinates:
    """The one place Lean's positions meet the file. The REPL client strips
    every import line before Lean sees the source, and Lean numbers the body
    it received from 1; each reported line moves down by the number of import
    lines so every reader works in file coordinates."""

    def __init__(self, inner: Any) -> None:
        self._inner = inner

    def __getattr__(self, name: str) -> Any:
        return getattr(self._inner, name)

    async def check_file(self, source: str, timeout_s: Any = None) -> Any:
        check = await self._inner.check_file(source, timeout_s=timeout_s)
        shift = import_lines(source)
        if not shift or not check.messages:
            return check
        moved = []
        for m in check.messages:
            m = dict(m)
            for key in ("pos", "endPos"):
                at = m.get(key)
                if isinstance(at, dict) and isinstance(at.get("line"), int):
                    m[key] = dict(at, line=at["line"] + shift)
            moved.append(m)
        if dataclasses.is_dataclass(check):
            return dataclasses.replace(check, messages=moved)
        check = copy.copy(check)
        check.messages = moved
        return check


def in_file_coordinates(services: Any) -> Any:
    if not isinstance(services.lean, FileCoordinates):
        services.lean = FileCoordinates(services.lean)
    return services


HTTP_STATUS = re.compile(r"OpenRouter returned HTTP (\d{3})")


def refused_before_generation(exc: LLMCallError) -> bool:
    """Whether the provider refused this call before generating anything.

    The harness reports the status only in the message. A retry is safe."""

    found = HTTP_STATUS.search(str(exc))
    return bool(found) and int(found.group(1)) in REFUSED_BEFORE_GENERATION


def error_messages(messages: Sequence[dict[str, Any]]) -> list[str]:
    return [
        str(m.get("data", "")).strip()
        for m in messages
        if m.get("severity") == "error"
    ]


def format_messages(messages: Sequence[dict[str, Any]]) -> str:
    """Keep the earliest diagnostics, since later ones usually cascade."""

    chunks = [
        f"{m.get('severity')} at {m.get('pos')}: {str(m.get('data', '')).strip()}"
        for m in messages
        if m.get("severity") in ("error", "warning")
    ]
    return "\n\n".join(chunks)[:FEEDBACK_CHARS] if chunks else ""

