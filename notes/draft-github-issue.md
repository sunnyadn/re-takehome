# DRAFT v2 - not posted. Needs Sunny's approval.

Repo: github.com/VerifiedMechanisms/re-takehome

**Title:** AGENT_API.md contradicts the ledger's fail-closed behaviour on HTTP errors

---

Once a request has been sent, any failure closes that problem's budget ledger for
good, so a transient provider 429 scores 0 even when the Comparator would accept
`solution.lean`. `tests/test_llm.py::test_http_error_fails_budget_closed` pins
this, so I take the behaviour as deliberate. The docs describe something else.

**Mechanism.** `LLMClient.complete` calls `budget.mark_unknown()` on all three
post-send failure paths, HTTP errors included. That sets `_complete = False`,
`BudgetLedger.reserve` then rejects every later reservation before the request
goes out, and nothing resets the flag. `evaluator.py` requires
`accounting_complete` for `budget_ok`, and `worker.py` reports `cost_unknown`.

The existing test returns 429 to every request, so it cannot separate "ledger
closed" from "provider still down". Same setup with 429 then 200:

```
call 1 -> LLMCallError: HTTP 429, accounting_complete=False, spent=$0.0
call 2 -> BudgetAccountingError: calls are disabled   (blocked before send)
```

The ledger stays shut after the provider recovers.

**The mismatch.** `docs/AGENT_API.md` says to catch `LLMCallError` and "decide
explicitly whether another request is worthwhile", then explains that "a
transport failure makes spend uncertain and closes the ledger". Singling out
transport failures implies an HTTP error response leaves that decision open. It
does not. There is no post-send failure for which that advice is actionable.

**Frequency.** Across 127 `openai/gpt-oss-120b` calls over the sample set,
7 returned HTTP 429, every one a `queue_timeout` from the upstream shared pool,
with successful calls to the same model immediately before and after. One run
per problem at judging time makes that a meaningful share of the holdout.

**Question.** Does `accounting_complete` gate the score you record? `RULES.md`
says you re-verify every solution yourselves and that anything the harness
reports about itself is orientation only, which would leave a passing
`solution.lean` scoring despite a closed ledger. The shipped evaluator says
otherwise.

A 429 carrying an error body is a known-zero-cost failure rather than an
uncertain one, so `release()` rather than `mark_unknown()` would fit that branch
and keep the invariant intact. `BudgetLedger.release` already exists and is
currently unused. Happy to send that patch if you want it.
