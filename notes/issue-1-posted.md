Working through the take-home I ran into this a few times, and I would rather ask than guess at the intent.

Once a request has been sent, any failure closes that problem's budget ledger for good, so a transient provider 429 scores 0 even when the Comparator would accept `solution.lean`. `tests/test_llm.py::test_http_error_fails_budget_closed` pins that, so I take it as deliberate. The docs describe something else.

`LLMClient.complete` calls `budget.mark_unknown()` on all three post-send failure paths, HTTP errors included. That sets `_complete = False`, `BudgetLedger.reserve` then rejects every later reservation before the request goes out, and nothing resets the flag. `evaluator.py` requires `accounting_complete` for `budget_ok`, and `worker.py` reports `cost_unknown`.

Your test returns 429 to every request, so it cannot separate a closed ledger from a provider that is still down. Same setup with 429 then 200:

```
call 1 -> LLMCallError: HTTP 429, accounting_complete=False, spent=$0.0
call 2 -> BudgetAccountingError: calls are disabled   (blocked before send)
```

The ledger stays shut after the provider recovers.

The mismatch is in `docs/AGENT_API.md`. It says to catch `LLMCallError` and "decide explicitly whether another request is worthwhile", then explains that "a transport failure makes spend uncertain and closes the ledger". Singling out transport failures reads as though an HTTP error response leaves that decision open, and there is no post-send failure where it does.

This fires often enough to matter. Across 127 `openai/gpt-oss-120b` calls over the sample set, 7 came back 429, all `queue_timeout` from the upstream shared pool, with successful calls to the same model either side of each one. At one run per problem, that is a real share of a holdout.

The question I actually want answered is whether `accounting_complete` gates the score you record. `RULES.md` says you re-verify every solution yourselves and that anything the harness reports about itself is orientation only, which would leave a passing `solution.lean` scoring despite a closed ledger. The shipped evaluator says the opposite.

One narrowing, if you want it. A 429 carrying an error body is a known-zero-cost failure rather than an uncertain one, so that branch could call `release()` instead of `mark_unknown()` and keep the invariant intact. `BudgetLedger.release` is already there and currently unused. Happy to send that patch.
