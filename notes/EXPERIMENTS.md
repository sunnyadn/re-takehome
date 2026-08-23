# Experiment log

Raw material for the Part 2 writeup. Every number here comes from a run whose
artifacts are on the PVE pods under `/shared/outputs/<run>/`.

Shared conditions unless noted: sample set of 16, one problem at a time,
`VM_TIME_LIMIT_S=1800`, `VM_BUDGET_USD=0.35`. These are exploration caps, not
judging caps (`28800` / `1.00`). All three conditions use the same scaffold in
`submission/agent.py` and differ only in which model is bound to which role, so
no condition benefits from a better harness than another.

## Round 1, 2026-08-20

| condition | roles | score | spend | ledger closures |
| --------- | ----- | ----- | ----- | --------------- |
| `qwen_solo` | all Qwen | **8/16** | $0.2966 | 1 |
| `gptoss_solo` | all GPT-OSS | **5/16** | $0.0593 | 4 |
| `collab_v1` | plan Qwen, formalize GPT-OSS, repair GPT-OSS then Qwen | **8/16** | $0.1736 | 3 |

### Per problem

| problem | collab_v1 | qwen_solo | gptoss_solo |
| ------- | --------- | --------- | ----------- |
| p01_linear | pass | pass | pass |
| p02_frac_cancel | pass | pass | *closed* |
| p03_sq_ge_two_ab | pass | pass | pass |
| p04_sum_sq | pass | pass | pass |
| p05_gcd_mersenne | **pass** | fail | fail |
| p06_pow_mod | fail | **pass** | **pass** |
| p07_least_divisible | fail | **pass** | *closed* |
| p08_sum_products | pass | pass | pass |
| p09_imo1964 | *closed* | **pass** | fail |
| p10_factorial_pow | **pass** | fail | *closed* |
| putnam_2018_a1 | **pass** | fail | fail |
| putnam_2020_a2 | fail | fail | fail |
| rmo_2000_2 | *closed* | fail | *closed* |
| rmo_2000_3 | fail | *closed* | fail |
| rmo_2000_6 | *closed* | fail | fail |
| rmo_2001_2 | fail | fail | fail |

## Finding 1: collaboration ties the better solo, but not because nothing happened

`collab_v1` and `qwen_solo` both score 8, yet they **disagree on six problems**.
Collaboration wins p05, p10 and putnam_2018_a1. Qwen solo wins p06, p07 and p09.
The tie is a coincidence of counts, not evidence that the second model
contributes nothing.

The sharper number is the **union**. Eleven of sixteen problems are solved by at
least one condition, and five are solved by none. An oracle choosing the best
condition per problem would score 11/16 against a best-single-condition 8/16.

So complementarity between the two models is real and worth three points, and
**the v1 coordination design fails to harvest any of it**. A fixed role pipeline
forces one model's approach on every problem. That is the thing to fix, and it
points at a simpler design rather than a more complex one: let both models
attempt independently and let the Lean compiler arbitrate, since verification is
cheap, objective, and already in the loop.

## Finding 2: the two models differ ~10x in call reliability

Pooled over all three runs, counting every OpenRouter call:

| model | calls | errors | rate |
| ----- | ----- | ------ | ---- |
| `qwen/qwen3.5-flash-02-23` | 180 | 1 | 0.56% |
| `openai/gpt-oss-120b` | 127 | 7 | 5.51% |

Fisher exact, one sided, p = 0.0098. Every error was HTTP 429 `queue_timeout`
from an upstream shared pool.

**Correction, 2026-08-21.** An earlier version of this note blamed AkashML.
That was wrong. Reading the `provider` field OpenRouter returns on every
response, our gpt-oss traffic is spread across CoreWeave (53 calls),
DeepInfra (19) and AkashML (14), so `provider.allow_fallbacks: False` prevents
failover after an error but does not pin us to one provider across requests.
The 429s came from CoreWeave (10) and AkashML (3), none from DeepInfra, though
19 calls is far too few to rank them. Nine of the twenty providers serving this
model sit under the harness price ceiling, and with `require_parameters: True`
all nine accept the parameters we send, so no legitimate parameter choice
steers routing toward a more reliable one. Provider identity is not a lever we
have. Our own call volume is.

This supersedes the round-1 reading of a single run, where 0/38 against 3/50 was
not significant and the honest position was that no difference had been shown.
With 307 calls it has been shown.

It matters because any error permanently closes that problem's budget ledger
(see `notes/PLAN.md`), so a call failure costs the whole problem, not the call.

## Finding 3: closures truncate attempts, they do not destroy finished proofs

Running the Comparator directly on the saved `solution.lean` of every closed
problem, in all three conditions, none would have passed at the moment it died.
Banked points lost to 429: **zero**.

That understates the cost, though. Two of the four closures in `gptoss_solo` hit
on **call one of one**, p02_frac_cancel among them, and p02 is a problem the
other two conditions solve in about sixty seconds. Truncation on an easy problem
is a lost point in expectation even though nothing finished was destroyed.

The honest summary is that the hazard costs attempts, and attempts convert to
points at a rate that depends on how easy the problem is.

## Round 2, launched 2026-08-21

New agent design in `submission/agent.py`. Two independent lines of attack, one
per model, interleaved under a shared clock, first line the Lean compiler
accepts wins. The one coordination rule is that a line whose error signature
stops moving is handed to the other model, inheriting its candidate and its
plan. Candidates are normalised to `import Mathlib` (safe per O1).

Three conditions, all at `VM_TIME_LIMIT_S=3600` and `VM_BUDGET_USD=0.35`, all on
the same scaffold, running concurrently on one dedicated node each.

| run | lines | isolates |
| --- | ----- | -------- |
| `v2_collab` | Qwen + GPT-OSS | the collaboration |
| `v2_qwen2` | Qwen + Qwen | two attempts, no model diversity |
| `v2_gptoss2` | GPT-OSS + GPT-OSS | same, other model |

The two-lines-of-one-model controls are the point. Both spend the same number of
attempts as the collaboration, so a win for `v2_collab` over them is a win for
model diversity rather than for extra compute. Round 1 could not separate those.

The cap moved from 1800s to 3600s because round 1 truncated four problems at
1800s, and v2 does roughly twice the work per problem. All three round-2
conditions share the new cap, so they stay comparable with each other. They are
**not** comparable with round 1 on wall-clock-limited problems.

`judge_check.sh` passes on v2, 1/1, $0.000584.

Offline control-flow tests (fake LLM and fake Lean, no network) confirm: a line
that wins on its first check stops the run at two calls, a stalled line does
hand off to the other model, an `LLMCallError` stops cleanly while keeping the
best candidate, and a single-line config degrades to a plain solo with no
handoffs.

## Round 2 was contaminated by our own concurrency. Results void.

Scores came out `v2_collab` 6/16, `v2_qwen2` 8/16, `v2_gptoss2` 3/16, which looks
like the new design losing badly. It is not. Ten of `v2_collab`'s sixteen
problems and thirteen of `v2_gptoss2`'s ended `cost_unknown`.

| run | gpt-oss calls | 429s | rate |
| --- | ------------- | ---- | ---- |
| round 1, gpt-oss running alone | 127 | 7 | 5.5% |
| `v2_collab`, concurrent with `v2_gptoss2` | 48 | 10 | 20.8% |
| `v2_gptoss2`, concurrent with `v2_collab` | 64 | 13 | 20.3% |

Qwen stayed at 0 errors in 226 calls through the same window, so this is not a
general outage. Running two gpt-oss-consuming campaigns at once on one key
roughly quadrupled the failure rate, and the design comparison is worthless
because only one of the three conditions was insulated from it. Re-running the
gpt-oss conditions one at a time.

The clean number that survives is `v2_qwen2` at **8/16 with 0 errors in 226
calls**. Pooled Qwen reliability is now 1 error in 406 calls, 0.25%.

**This mistake is the most useful thing round 2 produced.** The judging command
allows `--n-workers` to schedule problems concurrently, and every concurrent
problem would be hitting gpt-oss through the same key. An agent that leans on
gpt-oss self-saturates exactly the way this run did, and we have now measured
what that costs. It is a far stronger argument for keeping gpt-oss usage light
than the baseline flakiness argument, because it is a property of our own design
under the grader's own scheduling rather than a matter of provider luck.

## Next

- Redesign the coordination layer around the union result rather than around a
  fixed pipeline.
- Never run two gpt-oss-consuming conditions at the same time on one key.
- Classify the five never-solved problems by failure layer, wrong mathematics
  versus correct mathematics that will not formalise. Part 2 needs this and it
  is the only way to know which model fills which gap.
- Add stall detection, stop spending calls once the error signature stops moving.
- Add a free no-LLM tactic search, since `services.lean.check_file` does not
  touch the budget ledger and remains available after the LLM channel closes.

## 2026-08-22 — three silent-zero paths found and fixed

Sunny told me to read PR #4 in the take-home repo (another candidate pushed a
765-line research doc to the upstream repo by mistake and closed it in 35s).
Read critically. Two of its kit claims were verifiable and one was wrong.

**Verified in the kit, and we were exposed to all three:**

1. **Deadline cancel = 0 points.** `worker.py:92-98` wraps `agent.solve` in
   `asyncio.wait_for`. A cancel mid-call raises through `LLMClient`'s
   `except BaseException` -> `mark_unknown` -> ledger closed -> `cost_unknown`
   -> 0, however good the checkpoint. Our `agent_deadline_s` was an exact
   mirror of the worker's kill time (zero margin) and `agent.py:191,194` only
   checked `time_left() <= 0` before starting a turn, so with 1s left we would
   start a call whose gpt-oss median is 68s and p90 is 303s.
   **All 10 llm_error events in the shipped baseline corpus are CancelledError,
   i.e. this is the landmine that actually fires.**
   Fix: `last_turn_start_s` = worker deadline minus 900s (slowest measured call
   471s + Lean check 120s). At judging settings 28680 -> 27780.

2. **Axiom whitelist.** `lean.py:316` permits only `propext`,
   `Classical.choice`, `Quot.sound`. So `native_decide` (Lean.ofReduceBool),
   `sorry` and `axiom` compile against the REPL and still score 0. Our guard
   was prompt text only. Fix: lexical `banned_constructs()`.

3. **Numeric answers must be decimal literals** (`lean.py:343`). Known, now
   wired in: `answer_names()` regexes `abbrev NAME : Nat :=` slots out of the
   challenge (correctly excludes PutnamBench `Set (Z x Z)` abbrevs) and the
   harness's own `numeric_answers_are_literals` runs before we declare a win.
   Verified: `abbrev p06_answer := 7 * 7` now fails, `:= 49` passes.

Win condition changed from "Lean accepted" to "Lean accepted and no scoring
fault". Faults feed back into the repair prompt and into the stall signature,
so a stuck line hands off.

**Their claim that is wrong, do not propagate it.** Section 1.3 says the httpx
default `read=180.0` would close the ledger on slow gpt-oss calls. Measured
against the same baseline corpus they cite: 24 gpt-oss calls exceeded 180s, up
to 471s, and **every one of them succeeded**. There is not a single read
timeout in the corpus. httpx `read` bounds the gap between received bytes, not
total elapsed. Config constant -> runtime behaviour is not a valid inference
(same class of error as [[source-read-is-not-a-run]]).

**Also changed:** gpt-oss now runs at `effort: high` (model card AIME 2025
80.0 medium -> 92.5 high); qwen stays medium.

Nothing was taken from their architecture, literature review, or experiment
design. Part 2 must be written independently.

## 2026-08-22 — deterministic tactic sweep: 4/16 for zero tokens

Motivated by three independent literature findings that the symbolic layer, not
the model, carries most of the measured gain (DSP ablation: removing the
automated provers costs 9.0pp vs 5.3pp for removing the informal draft; Lyra:
error feedback alone +0.4pp, +5.3pp with a tool layer under it; APOLLO on o4-mini:
Syntax Refiner + AutoSolver alone take 7.0% to 20.5%).

`RULES.md` allows generic tactic libraries explicitly, and the Lean container is
local, so this costs no tokens and touches no network.

**Result: 4/16 (p01, p02, p04, p05) with zero LLM spend.** For scale, the shipped
baselines are qwen 7/16 and gpt-oss 8/16. `judge_check` on p01 now passes at
**$0.000000**, down from $0.000570.

Five of the 16 are skipped by construction: their `abbrev NAME : Nat := sorry`
answer slot survives, so `has_sorry` makes the file unacceptable no matter how
good the proof is. Those need the model to supply a literal first.

### Four bugs, each hidden behind the last

Worth recording because the first three all produce results that look like
"tactics do not work on these problems".

1. **Bare `;` truncates the `first` block.** `first | a | field_simp; ring | c`
   does not parse as three alternatives, and everything after the semicolon is
   lost, including alternatives that would have closed the goal. Symptom: three
   Lean checks completing in 0.1s total, and `unknown tactic`. Fix: parenthesise
   every multi-tactic alternative. Caught by the implausible timing, not by the
   error text.
2. **One unknown tactic kills the whole cocktail.** `unfold_let` no longer exists
   in this Mathlib, and its presence made every alternative fail to elaborate.
   Fix: `usable_cocktail()` probes each tactic against the live REPL once and
   drops what Lean does not know, which also makes the sweep survive Mathlib
   version drift.
3. **⭐ The silent one. `first` takes the first alternative that does not fail,
   not the first that closes the goal.** `norm_num`, `ring`, `norm_cast` and
   `push_cast; ring` succeed by rewriting without finishing, so `first` stopped
   there and never reached `linarith`. This produced a plausible-looking
   `unsolved goals` error and a plausible-looking score of 1/16. Fix: every
   alternative becomes `(tactic; done)`. **1/16 -> 4/16.**
   Measured directly: `linarith` alone solves p01, and `first | norm_num |
   linarith` does not.
4. **A non-fatal red herring.** The remaining failures all report
   `typeclass instance problem is stuck: Preorder ?m`. Bisection showed
   prepending any single cocktail tactic before a known-good one does not break
   it, so `first` recovers and the message is a diagnostic from a discarded
   alternative, not the cause. The remaining failures are genuine.

p03 (`a^2 + b^2 >= 2*a*b`) needs `nlinarith [sq_nonneg (a - b)]`. The hint names
the problem's own variables, which is per-problem special-casing and banned by
`RULES.md` Conduct, so that one is left to the models.

### Why this matters for Part 2

A zero-token deterministic baseline reaches **4/16**, against 7/16 and 8/16 for
the two models working alone. Roughly half of what either model "achieves" on
this sample is reachable with no model at all. Any claim about collaboration has
to be measured against this floor, not against zero.
