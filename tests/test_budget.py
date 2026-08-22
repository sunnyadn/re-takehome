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


def test_unbilled_release_keeps_the_ledger_open():
    ledger = BudgetLedger(1.0)
    snapshot = ledger.release_unbilled(ledger.reserve(0.4))
    assert snapshot.reserved_usd == 0
    assert snapshot.spent_usd == 0
    assert snapshot.unbilled_usd == pytest.approx(0.4)
    assert snapshot.accounting_complete
    ledger.reserve(0.9)


def test_unbilled_releases_alone_can_exhaust_the_budget():
    ledger = BudgetLedger(1.0)
    assert ledger.release_unbilled(ledger.reserve(0.6)).accounting_complete
    snapshot = ledger.release_unbilled(ledger.reserve(0.5))
    assert snapshot.spent_usd == 0
    assert snapshot.unbilled_usd == pytest.approx(1.1)
    assert not snapshot.accounting_complete
    with pytest.raises(BudgetAccountingError):
        ledger.reserve(0.01)


def test_spend_after_an_unbilled_release_still_trips_the_limit():
    ledger = BudgetLedger(1.0)
    assert ledger.release_unbilled(ledger.reserve(0.9)).accounting_complete
    snapshot = ledger.settle(ledger.reserve(0.2), 0.2)
    assert snapshot.spent_usd == pytest.approx(0.2)
    assert not snapshot.accounting_complete
    assert not snapshot.within_limit


def test_unbilled_release_rejects_an_unknown_reservation():
    ledger = BudgetLedger(1.0)
    with pytest.raises(BudgetAccountingError):
        ledger.release_unbilled("not-a-reservation")
    assert ledger.snapshot().unbilled_usd == 0
