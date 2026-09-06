"""What a turn carries between the parts of the agent: the file it is looking
at, and the last thing said about a goal."""

from __future__ import annotations
import re
from dataclasses import dataclass, field
from typing import Any
from submission.framework import placeholders


@dataclass
class Feedback:
    """What to tell the next model, and who earned it."""

    author: str
    text: str
    kind: str = "rejected"

    def lead(self, model: str) -> str:
        if self.kind == "probe":
            return "The probe you asked for printed"
        if self.kind == "empty":
            return ("Your last reply contained no Lean. Reply with one ```lean block "
                    "of tactic lines and nothing else. What Lean last said was")
        if self.kind == "cut":
            return ("Your last reply ran out of tokens before its code block ended, so "
                    "none of it could be used. You are writing a whole proof; write the "
                    "next step and stop. What Lean last said was")
        if self.kind == "withdrawn":
            return "A decomposition posted at this goal was taken back"
        if self.kind == "drift":
            return ("These facts compiled but left the goal standing, so they have been "
                    "removed. Reshape the goal or close it directly. They were")
        if self.author == model:
            return "Your last step was rejected and has been removed. Lean said"
        return f"A {self.author} attempt on this goal was rejected. Lean said"


@dataclass
class State:
    """The proof and what the last check said about it."""

    text: str
    goal: str = ""
    line: int = 0
    messages: list[dict[str, Any]] = field(default_factory=list)
    accepted: bool = False
    focus: int = 0
    goals: int = 0


def stalled(before: State, after: State) -> bool:
    """A step that grew the file and left the proof state exactly as it was."""

    return (bool(before.goal) and after.goal == before.goal
            and after.text != before.text
            and len(placeholders(after.text)) >= len(placeholders(before.text)))


VACUOUS = re.compile(r"^\S[^:]*:\s*(?:True|Type)\s*$", re.M)
