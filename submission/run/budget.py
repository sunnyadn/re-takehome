"""What the run can still afford: the clock, the money, and each probe kind's
share of the clock. Depends on nothing else in the run."""

from __future__ import annotations
import time
from typing import Any

from submission.agent import BUDGET_HEADROOM
from submission.run.context import Run

# What the harness's own Lean probes may take of the wall clock so far: the
# environment scans (names, the vocabulary scan, apply?) and the leaf blocks,
# each at this share, after a grace period. Measured on a 4-core pod
# (rmo_2000_6, v7.85): 425 checks, Lean 2443 s of 2642 s, of which names 689 s,
# apply? and the scan 478 s, leaves 466 s; 91 model calls in 44 minutes.
PROBE_SHARE = 0.15
RETRY_SHARE = 0.05
PROBE_GRACE_S = 60.0


class Budget:
    def __init__(self, run: Run) -> None:
        self.cfg, self.ledger, self.events = run.cfg, run.ledger, run.events
        self.started = time.monotonic()
        self.deadline = self.started + run.cfg.last_turn_start_s
        self.probe_spent = {"scan": 0.0, "leaf": 0.0, "retry": 0.0}
        # Set while a leaf block is being judged: those checks get the cap
        # timeout, and a slow step inside one is not held against it.
        self.heavy_leaf = False

    def elapsed(self) -> float:
        return time.monotonic() - self.started

    def time_left(self) -> float:
        return self.deadline - time.monotonic()

    def can_ask(self) -> bool:
        return self.ledger.spent_usd < BUDGET_HEADROOM * self.cfg.budget_usd

    def spent(self, kind: str, seconds: float) -> None:
        self.probe_spent[kind] += seconds

    def affordable(self, kind: str) -> bool:
        """Whether this probe kind is still inside its share of the clock."""
        elapsed = self.elapsed()
        share = RETRY_SHARE if kind == "retry" else PROBE_SHARE
        if self.probe_spent[kind] <= PROBE_GRACE_S or self.probe_spent[kind] <= share * elapsed:
            return True
        self.events.append({"stage": "probe_skipped", "kind": kind,
                            "spent_s": round(self.probe_spent[kind]), "elapsed_s": round(elapsed)})
        return False
