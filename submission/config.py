"""How one run is configured, and the local mirror of what it has spent.

`Config` is the part an applicant would change: which models get a line, the
budget, the clock, and the two research switches."""

from __future__ import annotations

import os
from dataclasses import dataclass, field
from typing import Any, Sequence

from re_harness.config import HarnessSettings
from re_harness.models import ALLOWED_MODELS, MODEL_A, MODEL_B


# A refused call releases its reservation, so repeating it is free and the
# problem stays winnable. Without this a single 429 ends the problem.
RETRY_BACKOFF_S = (5.0, 20.0, 60.0)


FEEDBACK_CHARS = 6000


# Stop launching while a round still fits, since overshooting the ledger
# scores zero however good the proof is.
BUDGET_HEADROOM = 0.9


def _env_models(name: str, default: Sequence[str]) -> tuple[str, ...]:
    raw = os.environ.get(name, "").strip()
    if not raw:
        return tuple(default)
    models = tuple(part.strip() for part in raw.split(",") if part.strip())
    if not models or any(m not in ALLOWED_MODELS for m in models):
        raise ValueError(f"{name} must be a comma-separated list of {sorted(ALLOWED_MODELS)}")
    return models


@dataclass(frozen=True)
class Config:
    """Which models get a line. One model listed twice is the solo control."""

    lines: tuple[str, ...] = (MODEL_A, MODEL_B)
    budget_usd: float = 1.00
    time_limit_s: float = 28800.0
    # Research switch: VM_AUDIT=off lets every statement in unaudited (the
    # ablation arm of the writeup). The judged configuration is the default.
    audit: bool = True
    # `VM_LEAVES=off` skips the shape-built tactic blocks (the ablation that
    # measures the hand-written layer's share). The judged configuration is on.
    leaves: bool = True
    # The worker hands the agent time_limit minus this, then hard-cancels.
    verify_reserve_s: float = 120.0
    # A cancelled call closes the ledger and scores the problem zero, so no
    # turn may start inside this window. A fixed margin was beaten by 2.4x.
    stop_margin_floor_s: float = 900.0
    stop_margin_fraction: float = 0.1

    @classmethod
    def from_env(cls) -> "Config":
        settings = HarnessSettings.from_env(n_workers=1)
        return cls(
            lines=_env_models("VM_LINES", (MODEL_A, MODEL_B)),
            audit=os.environ.get("VM_AUDIT", "on").strip().lower() not in ("off", "0", "false"),
            leaves=os.environ.get("VM_LEAVES", "on").strip().lower() not in ("off", "0", "false"),
            budget_usd=settings.budget_usd,
            time_limit_s=settings.time_limit_s,
            verify_reserve_s=float(settings.verify_reserve_s),
        )

    @property
    def agent_deadline_s(self) -> float:
        """Mirror of the worker's own deadline arithmetic."""

        reserve = min(self.verify_reserve_s, self.time_limit_s * 0.25)
        return max(60.0, self.time_limit_s - reserve)

    @property
    def stop_margin_s(self) -> float:
        """Wide enough for a turn already in flight, never a quarter of the run.

        Without the cap the 8-hour floor swallowed 47% of a 30-minute run."""

        want = max(self.stop_margin_floor_s, self.stop_margin_fraction * self.time_limit_s)
        return min(want, 0.25 * self.time_limit_s)

    @property
    def last_turn_start_s(self) -> float:
        """No turn may start after this, so none is in flight at the cancel."""

        deadline = self.agent_deadline_s
        return max(30.0, deadline - min(self.stop_margin_s, deadline * 0.5))


@dataclass
class Ledger:
    """Local mirror of spend, which Services does not expose, plus a turn log."""

    spent_usd: float = 0.0
    events: list[dict[str, Any]] = field(default_factory=list)

    def record(self, usage: Any) -> float:
        # llm.complete validates usage.cost before returning, so this is total.
        cost = float(usage["cost"])
        self.spent_usd += cost
        return cost

