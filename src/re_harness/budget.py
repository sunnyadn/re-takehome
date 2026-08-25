"""Thread-safe, fail-closed per-problem spend accounting."""

from __future__ import annotations

import threading
import uuid
import math
from dataclasses import dataclass


class BudgetExceeded(RuntimeError):
    pass


class BudgetAccountingError(RuntimeError):
    pass


@dataclass(frozen=True)
class BudgetSnapshot:
    limit_usd: float
    spent_usd: float
    reserved_usd: float
    accounting_complete: bool

    @property
    def within_limit(self) -> bool:
        return (
            self.accounting_complete
            and self.reserved_usd == 0
            and self.spent_usd <= self.limit_usd
        )


class BudgetLedger:
    def __init__(self, limit_usd: float):
        if not math.isfinite(limit_usd) or limit_usd <= 0:
            raise ValueError("budget limit must be positive")
        self.limit_usd = float(limit_usd)
        self._spent = 0.0
        self._reservations: dict[str, float] = {}
        self._complete = True
        self._lock = threading.Lock()

    def reserve(self, amount_usd: float) -> str:
        if not math.isfinite(amount_usd) or amount_usd < 0:
            raise ValueError("reservation cannot be negative")
        with self._lock:
            if not self._complete:
                raise BudgetAccountingError("budget accounting is incomplete; calls are disabled")
            committed = self._spent + sum(self._reservations.values())
            if committed + amount_usd > self.limit_usd:
                raise BudgetExceeded(
                    f"call could exceed ${self.limit_usd:.2f} problem budget "
                    f"(${committed:.6f} committed, ${amount_usd:.6f} requested)"
                )
            reservation_id = uuid.uuid4().hex
            self._reservations[reservation_id] = amount_usd
            return reservation_id

    def settle(self, reservation_id: str, actual_usd: float) -> BudgetSnapshot:
        if not math.isfinite(actual_usd) or actual_usd < 0:
            raise BudgetAccountingError("provider returned negative cost")
        with self._lock:
            if reservation_id not in self._reservations:
                raise BudgetAccountingError("unknown budget reservation")
            self._reservations.pop(reservation_id)
            self._spent += float(actual_usd)
            return self._snapshot_unlocked()

    def release(self, reservation_id: str) -> None:
        with self._lock:
            self._reservations.pop(reservation_id, None)

    def mark_unknown(self, reservation_id: str) -> BudgetSnapshot:
        with self._lock:
            self._reservations.pop(reservation_id, None)
            self._complete = False
            return self._snapshot_unlocked()

    def snapshot(self) -> BudgetSnapshot:
        with self._lock:
            return self._snapshot_unlocked()

    def _snapshot_unlocked(self) -> BudgetSnapshot:
        return BudgetSnapshot(
            limit_usd=self.limit_usd,
            spent_usd=self._spent,
            reserved_usd=sum(self._reservations.values()),
            accounting_complete=self._complete,
        )
