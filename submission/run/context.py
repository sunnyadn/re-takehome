"""What one problem's run settles before the board opens.

Everything here is fixed for the run, or is an object the parts share by
reference. Each part of the run takes this and reads what it needs, so no
part carries a constructor of nine arguments."""

from __future__ import annotations
from typing import Any

from re_harness import Problem, Services
from submission.agent import (Ledger, answer_names, declared_names,
                              normalise_imports, with_preamble)
from submission.cells import Cells
from submission.framework import root_names
from submission.board.types import Notes


class Run:
    def __init__(self, problem: Problem, services: Services, cfg: Any,
                 events: list[dict[str, Any]]) -> None:
        self.problem, self.services, self.cfg, self.events = problem, services, cfg, events
        self.ledger = Ledger()
        self.models = list(cfg.lines)
        # The two views of the problem the grader has: the answer slots it
        # fills in, and the declarations it compiles.
        self.names = answer_names(problem.challenge)
        self.graded = declared_names(problem.challenge)
        # The file every branch starts from, and the first thing in it that
        # is graded. `text` is rewritten during setup and fixed after that.
        self.text = with_preamble(normalise_imports(problem.challenge, problem.challenge))
        self.first_graded = next(iter(root_names(self.text)), "")
        self.cells = Cells()
        self.notes = Notes()
