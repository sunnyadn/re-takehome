# DRAFT PR body v5 - not pushed. Needs Sunny's approval.

Repo: VerifiedMechanisms/re-takehome
Branch: sunnyadn/re-takehome:keep-ledger-open-on-rate-limit
Title: Keep the budget ledger open when a request is refused before generation

---

Follow-up to #1, independent of #3.

`AGENT_API.md` says a transport failure closes the ledger. A 429 isn't one but is treated like one, and nothing reopens it, so the first rate limit on a problem scores it 0.

You picked 429 as the case to pin in `test_http_error_fails_budget_closed`, so I won't pretend I found an oversight. It's a spec change and you can reject it as one.

80 concurrent calls pinned to a rate-limited provider gave 69 refusals and 11 successes. The 11 reported $0.000053680, the per-key meter moved by $0.000053680, and none of the 69 bodies carried a `usage` key. Pinning needs `provider.order`, so that ran against the API directly on the same key.

One provider on one day, which is why the code checks each body for a cost instead of trusting the status.

Charging the reservation was my first attempt, since a ledger that can only over-report looks safer. `RULES.md` says you cross-check transcripts against the key's usage ledger, so that would have manufactured the discrepancy you use to catch problems.
