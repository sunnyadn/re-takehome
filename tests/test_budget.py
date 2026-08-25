from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor

import pytest

from re_harness.budget import BudgetAccountingError, BudgetExceeded, BudgetLedger


def test_reservations_prevent_concurrent_overspend():
    ledger = BudgetLedger(1.0)

    def reserve():
        try:
            return ledger.reserve(0.6)
        except BudgetExceeded:
            return None

    with ThreadPoolExecutor(max_workers=2) as pool:
        reservations = list(pool.map(lambda _: reserve(), range(2)))
    assert sum(value is not None for value in reservations) == 1
    assert ledger.snapshot().reserved_usd == pytest.approx(0.6)


def test_actual_cost_is_authoritative_and_unknown_fails_closed():
    ledger = BudgetLedger(1.0)
    first = ledger.reserve(0.2)
    snapshot = ledger.settle(first, 0.3)
    assert snapshot.spent_usd == pytest.approx(0.3)
    second = ledger.reserve(0.1)
    snapshot = ledger.mark_unknown(second)
    assert not snapshot.accounting_complete
    assert not snapshot.within_limit
    with pytest.raises(BudgetAccountingError):
        ledger.reserve(0.01)


def test_settle_can_record_provider_overshoot():
    ledger = BudgetLedger(1.0)
    reservation = ledger.reserve(0.2)
    snapshot = ledger.settle(reservation, 1.1)
    assert snapshot.spent_usd == pytest.approx(1.1)
    assert not snapshot.within_limit

