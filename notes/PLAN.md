# Verified Mechanisms take-home — working plan

Status file. Updated as work proceeds. Not part of the submission deliverable,
though `notes/EXPERIMENTS.md` feeds the writeup.

## The ask

Two fixed models via OpenRouter, no other network:

- Model A `qwen/qwen3.5-flash-02-23`
- Model B `openai/gpt-oss-120b`

**Part one** — build a coordination layer that makes A and B collaborate to turn
`problem.md` + `challenge.lean` (statement with `sorry`) into a Lean 4 file the
`leanprover/comparator` accepts. Scored mechanically on a private holdout of
~12 problems, 1 point each, **$1 and 8h wall-clock per problem**, either cap
exceeded scores 0.

**Part two** — an empirical writeup (1-10 pages, appendix excluded) on whether
the collaboration actually beats either model alone, and what one model
contributes that the other lacks. Per-problem results, confounders addressed,
transcripts as evidence. Clarity is graded.

Deadline **2026-08-30 EOD AoE = 2026-08-31 06:00 Calgary**.
Submit repo link + PDF via their Google form; editable until deadline.

## Environment

**All Lean work runs on the PVE cluster, not the laptop.** The pinned Lean image
is `linux/amd64` only (no arm64 variant in the manifest) and Sunny's Air is
arm64, so locally every Lean process runs under emulation. Measured 2026-08-20:
the same Comparator job takes ~22s natively on the cluster and does not finish
inside the 180s timeout on the Air. This is a correctness problem, not a comfort
one — local timings are meaningless and local timeouts are spurious.

- Code editing, unit tests, reading transcripts: the Air.
- Everything that touches Lean (`smoke_test`, `judge_check`, all runs): PVE.
- PVE k8s (`~/.kube/libcuda.yaml`, ns `sunny`), privileged docker-in-docker pod
  `lean-runner-N` on its own autoscaled node. Validated 2026-08-20: the
  autoscaler brings up a 4C/8G node in ~45s. Pod requests are set to 6Gi
  specifically so it cannot land on `node-a`, which hosts sembr/qdrant/rsshub.
- Image health on cluster: Lean 4.32.0, Mathlib `81a5d25`, comparator `07bc4ea`.
- Both models reachable, key works. Observed cost is small: a trivial call is
  ~$6e-5 (A) / ~$1e-5 (B). The $1 cap is loose; **wall-clock and Lean check
  latency are the binding constraints**, not money.

## Harness facts that constrain the design

Read from `src/re_harness/`. These are not negotiable — judges run their own copy.

1. **REPL != Comparator.** `services.lean.check_file` strips every `import` line
   and runs the body against a warm `import Mathlib` env. The Comparator compiles
   the real file with its real imports in a fresh container. A candidate can pass
   the REPL and fail judging.
   **O1 resolved 2026-08-20 by direct Comparator runs on the cluster:** a
   solution may widen the imports. A challenge importing only
   `Mathlib.Data.Nat.Basic` with a solution importing all of `Mathlib` passes;
   the same-imports control passes; and a solution that restates the theorem
   (`n + 0 = n` weakened to `n = n`) is rejected, confirming the Comparator
   really does compare statements. So normalising every candidate to
   `import Mathlib` closes the REPL/Comparator gap safely. Cost: the Comparator
   build goes from ~0.5s to ~22s, well inside its 180s timeout.
2. **One transport failure zeroes the problem.** Any `LLMCallError` calls
   `budget.mark_unknown()`, which sets `accounting_complete=False`, which makes
   `budget_ok` false in the evaluator — 0 points even with a correct proof.
   So: on `LLMCallError`, checkpoint the best candidate and return immediately.
3. **Reservation, not actual spend, gates admission.** Each call reserves
   `bytes*in_ceiling + max_tokens*out_ceiling` times 1.10 up front. A late call
   with a large `max_tokens` raises `BudgetExceeded` even when real spend is tiny.
   Keep `max_tokens` tight and shrink it as the ledger fills.
4. **No ledger in `Services`.** Sum `response.usage["cost"]` ourselves. Read
   `VM_TIME_LIMIT_S` from env for the clock; the agent gets
   `time_limit - min(verify_reserve_s, 0.25*time_limit)`.
5. **Lean checks serialize** per problem (one REPL behind an `RLock`), so
   parallel candidate generation still has a serial verification bottleneck.
6. **Numeric answers** must be `abbrev NAME : ℕ := <decimal literal>`, checked by
   regex outside Lean. No arithmetic in the body.
7. `--n-workers` schedules different *problems*, never parallelism inside one.

## Design

One scaffold, parameterised by which model plays which role. Solo conditions are
the same code with both roles bound to the same model. This is deliberate: it
removes the "collab just has a better harness than solo" confound.

Roles:

- **Planner** — problem.md + challenge.lean -> informal proof, plus the concrete
  value for any `abbrev ... := sorry` answer slot.
- **Formalizer** — plan + challenge -> complete Lean file.
- **Repairer** — Lean errors + current file -> revised file. On repeated failure
  with the same error signature, escalate to the *other* model.

The cross-model escalation is the one real coordination mechanism, and it is
simple enough to explain in a paragraph. The brief says twice that a simple
design they can understand beats a complicated one that scores marginally better.

## Experiment design (Part two)

Five conditions, matched budget and attempt count, same scaffold:

| # | Planner | Formalizer | Repairer | Isolates |
| - | ------- | ---------- | -------- | -------- |
| 1 | A | A | A | Qwen solo |
| 2 | B | B | B | GPT-OSS solo |
| 3 | A | A | A+A | scaffold-only control (structure without model diversity) |
| 4 | B | B | B+B | same, other model |
| 5 | A | B | A/B | the collaboration |

Conditions 3 and 4 are the point: without them a win for 5 over 1 and 2 could be
the role structure rather than the two models. Both role assignments for 5
(A-plans/B-formalizes and the reverse) if the money allows.

Money plan of the $50: ~$8 dev and debugging, ~$15-25 for the campaigns at a
*reduced* per-problem cap (matched across conditions — matching each other
matters for the science, matching the judge's $1 does not), ~$12 reserve for
final full-cap verification and re-runs.

## Sequence

1. Env up, `judge_check.sh` green with a working agent. Crash insurance first. **<- current**
2. Answer O1 (import normalization) with a real Comparator run.
3. Solo baselines on the 16 samples. This is both a smoke test of the key and
   the Part-two solo data. `baselines/simple_agent.py` + `BASELINE_MODEL` already
   gives solo conditions — do not rebuild it.
4. Design the collaboration from what the solos actually fail at.
5. Build and tune the coordination layer.
6. Full five-condition campaign on PVE.
7. Writeup, repo cleanup, `judge_check.sh`, Sunny reviews, submit early.

## Results

### collab_v1, 2026-08-20 (planner A, formalizer B, repair cycle B then A)

Caps were lowered for exploration, `VM_TIME_LIMIT_S=1800` and `VM_BUDGET_USD=0.35`,
so these are not judging conditions. **8/16, $0.1736 total.** Money is nowhere
near binding, roughly a cent per problem against a $1 cap.

Passed: p01 p02 p03 p04 p05 p08 p10 putnam_2018_a1.
Failed on the mathematics: p06 p07 putnam_2020_a2 rmo_2000_3 rmo_2001_2.
Ended early on a closed ledger: p09 rmo_2000_2 rmo_2000_6.

### The 429 hazard (dominant operational risk)

`openai/gpt-oss-120b` returned HTTP 429 on 3 of 50 calls, all `queue_timeout`
from the upstream shared pool at provider AkashML. `qwen` returned 0 errors in
38 calls, but 0/38 against 3/50 is not significant (Fisher p ≈ 0.26), so the
claim to make is about the absolute gpt-oss rate, not about Qwen being safer.

The failures are **not** a sustained outage window. gpt-oss succeeded ten times
in a row immediately after the 22:09 failure and again 90s after the 22:27 one.
Treat it as approximately independent per call. That means the lever is call
count, not timing.

Verified by direct experiment (`notes/`, mock transport): after any
`LLMCallError` the ledger sets `accounting_complete=False` permanently, and the
next call is refused before the request is sent even though the server would
have answered 200. The evaluator then scores the problem 0 regardless of the
proof. Retry, backoff and provider failover are all unavailable, the last
because the harness hardcodes `provider.allow_fallbacks: False`.

Cost of the three closures on this run was **zero actual points**. Running the
Comparator directly on their saved solutions, p09 and rmo_2000_2 fail and
rmo_2000_6 still contains `sorry`. They lost remaining repair attempts, not
banked proofs. It stays a real tail risk though: p10 needed ten gpt-oss calls
and had roughly a 46% chance of dying before finishing.

Design rule this implies. With r the per-call failure rate and k the gpt-oss
calls per problem, collaboration only pays when

    P(solve | collab) / P(solve | Qwen solo)  >  (1 / (1 - r))^k

which at r = 0.06 demands +6% at k=1, +20% at k=3, +38% at k=5, +88% at k=10.
Two consequences, both cheap. Put the reliable path on the critical path so a
checkpointed candidate exists before any risky call, and cap k.

Open with them: a GitHub issue draft is in `notes/draft-github-issue.md`,
unposted, pending Sunny's approval. Their answer decides whether
`accounting_complete` gates the real score, which changes how hard k must be
capped.

## Open questions

- **O1** Does the Comparator accept changed imports? (blocks the normalization step)
- **O2** What does each model's failure mode actually look like — bad math, or
  bad Lean? Drives role assignment. Answer from step 3 transcripts.
- **O3** Is best-of-n sampling with the leftover budget worth more than deeper
  repair? Wall-clock, not money, decides this.
