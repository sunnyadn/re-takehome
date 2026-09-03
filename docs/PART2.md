---
title: "Two models on one Lean file: did the pair beat either model alone?"
author: "Guang (Sunny) Yang"
date: "3 September 2026"
---

## The question

The submission (`submission/board_agent.py`, described in `docs/APPROACH.md`) puts `qwen/qwen3.5-flash-02-23` and `openai/gpt-oss-120b` on one shared Lean file. Each open `sorry` is a goal. A model takes a goal, writes one step, Lean judges it, and every statement a model writes is audited against a computed witness, named by the auditing model, before it stays in the file. This note asks two things: did that pair solve more than either model on its own, and when it did, what in the transcripts did the work.

## The arms, and what they do not control for

| Arm | What it is | Runs |
| --- | --- | --- |
| qwen solo | the kit's `baselines/simple_agent.py` with `BASELINE_MODEL=qwen/qwen3.5-flash-02-23`, as shipped in `outputs/baseline/` (`run.json`: 1200 s per problem, the agent cut at 1080 s, 4 workers) | 1 per problem |
| gpt-oss solo | the same baseline with `openai/gpt-oss-120b`, as shipped (1200 s, agent cut at 1080 s, 5 workers) | 1 per problem |
| board (pair) | the submission, `VM_TIME_LIMIT_S=1800` (sample problems, `putnam_2020_a2`) or `3600` (the other hard problems), `VM_BUDGET_USD=1.00`, one worker. Artifacts in `outputs/board/` | 1 per problem, more where stated |

This is not a clean ablation. The solo arms are the kit's draft-compile-repair loop, not the board with one model removed, so a difference between the arms mixes "two models" with "a different scaffold". The clocks differ: the solo arms had 1200 s per problem and were cut at 1080 s, the board had 1800 or 3600 s. Where a solo arm was cut by the clock the table says `t/o`, because that is a run that was stopped, not one that was beaten. The board's three wins that no solo arm has (p09, p10, rmo_2000_6) came at 343 s, 155 s and 378 s, inside the solo arms' clock, so the board did not need its longer window for them, but the solo arms were never given the chance to fail on their own. The solo arms also ran 4 or 5 problems concurrently on one GCP machine and the board ran one at a time on other machines, so wall times are comparable within an arm and not across arms. The board arm is my own runs. The comparison says what the pair did that the shipped single-model loops did not. It does not isolate the second model as the cause. The ablation that would (the board with the same model in both seats, and the board with the audit removed) was not run before this submission.

## Results

Score is the kit comparator's verdict, 1 or 0. Wall time is seconds.

| Problem | qwen solo | gpt-oss solo | board | board $ |
| --- | --- | --- | --- | --- |
| p01_linear | 1 (65) | 1 (60) | 1 (3) | 0 |
| p02_frac_cancel | 1 (65) | 1 (76) | 1 (3) | 0 |
| p03_sq_ge_two_ab | 1 (69) | 1 (99) | 1 (7) | 0.0002 |
| p04_sum_sq | 1 (64) | 1 (79) | 1 (3) | 0 |
| p05_gcd_mersenne | 0 (363) | 1 (140) | 1 (3) | 0 |
| p06_pow_mod | 1 (135) | 0 (713) | 1 (58) | 0.0039 |
| p07_least_divisible | 1 (391) | 1 (795) | 1 (11) | 0.0004 |
| p08_sum_products | 1 (70) | t/o | 1 (14) | 0.0006 |
| p09_imo1964 | 0 (819) | t/o | 1 (343), 2 of 3 runs (343 s, 918 s, one run reached the clock), 6 of 6 on v7.40 | 0.013 |
| p10_factorial_pow | 0 (235) | t/o | 1 (155) | 0.0046 |
| putnam_2018_a1 | t/o | 1* | 0 (2726) | 0.073 |
| putnam_2020_a2 | 0 (614) | 1* | 0 (1296) | 0.054 |
| rmo_2000_2 | 0 (835) | t/o | 0 (2705) | 0.078 |
| rmo_2000_3 | t/o | t/o | 0 (see note) | |
| rmo_2000_6 | 0 (904) | t/o | 1 (378) | 0.021 |
| rmo_2001_2 | t/o | t/o | 0 (2655) | 0.111 |
| **Total of 16** | **7** | **8 (6 without \*)** | **11** | |

Wall time is the agent's own `wall_s` in `result.json`, comparator time excluded. `t/o` is `agent exceeded 1080.0s` in the kit's `summary.json` (3 of qwen's 9 zeros, 7 of gpt-oss's 8). The board runs for `putnam_2018_a1`, `rmo_2000_2` and `rmo_2001_2` are from the commit two before the final one (v7.59), which differs from it only in how Lean positions are mapped when a challenge has more than one import line, and all three challenges have one. The `rmo_2000_6` artifact is a run of an identical copy of the problem under the id `rmo6y`, made so that several copies could run at once.

\* These two passes predate the kit's PR #9 ("Inline the Putnam answers so circular solutions stop scoring"). They used the answer to prove the answer and would not score now.

Note on `rmo_2000_3`: the challenge file as shipped does not build under its own imports in the comparator (`Finset.sum` and `Finset.Ico` on ℕ need `Mathlib.Algebra.BigOperators.Group.Finset.Basic` and `Mathlib.Order.Interval.Finset.Nat`), so no solution can score on it as published. I added the two imports in my local copy so the agent could be measured on it. That run had not finished when this note was written, and the row above is on the unedited problem for the solo arms.

Two disclosures found in a final read of the shipped files. First, the system prompt that goes to every problem carried, until the last commit, one sentence of rationale for the shared-lemma rule that quoted p09's own key identity (`2 ^ n % 7 = 2 ^ (n % 3) % 7`). It was written as a measurement note and should never have been in prompt text. Every p09 run in this note ran with that sentence present, so p09's board results are not clean evidence and should be read as such; the sentence is removed in the final commit and p09 has not been rerun without it. Second, `result.json` keeps only the last 60 agent events per run, so the per-model step counts in the next table are the tail of the run for the two runs longer than 60 events (p09 and `rmo_2000_6`); `transcript.json` holds every call (p09: 67 model calls, not the 17 the truncated list shows).

## Where the pair won, and what did the work

The transcripts of the board's passing runs (`outputs/board/<problem>/`, the `agent_metadata.events` list in each `result.json`) record who wrote each accepted step, who audited it, and what closed each goal without a model. Q is qwen, G is gpt-oss. "Steps" counts accepted over attempted.

| Problem | Model calls | Steps Q | Steps G | Audits (all by G) | Closed by Lean alone |
| --- | --- | --- | --- | --- | --- |
| p01, p02, p04, p05 | 0 | 0 | 0 | 0 | whole theorem, first check |
| p03 | 3 | 1/1 | 0/1 | 1 | |
| p06 | 23 | 4/10 | 3/4 | 7 | 2 goals |
| p07 | 1 | 0 | 0 | 0 | 1 goal |
| p08 | 4 | 1/1 | 0/1 | 2 | |
| p09 | 67 | 10/15 (tail) | 3/4 (tail) | 6 | 2 goals |
| p10 | 17 | 3/5 | 3/3 | 11 | |
| rmo_2000_6 | 57 | 5/8 (tail) | 5/6 (tail) | 15 | 2 goals (witness search) |

Three things follow.

**On 5 of the 10 sample problems the pair is not the reason.** p01, p02, p04, p05 close on the first Lean check from a fixed cocktail of closing tactics with 0 model calls, and p07 with 1 call after the cocktail closed one of its goals. qwen solo lost p05 on a problem that `decide` closes. That is a harness gain, and any single-model agent could have it.

**On the 5 that needed model steps, the roles were not symmetric.** qwen wrote most of the accepted steps on p09 (10 of 13) and p06 (4 of 7), and on the four problems where each model attempted 3 or more steps gpt-oss's acceptance rate was the higher one (p06 3/4 against 4/10, p09 3/4 against 10/15, p10 3/3 against 3/5, rmo_2000_6 5/6 against 5/8). On p03 and p08 each model wrote once and qwen's step was the one accepted, so this is a tendency at small counts, not a law. Every audit in these runs was performed by gpt-oss, and that is by design: measured over 12 audits, qwen named values that violated a hypothesis every time (at about 9 s a reply) and gpt-oss answered in about 1.4 s, so the auditor's seat went to gpt-oss, for its own statements too. The pattern the board settled into is qwen proposing more, gpt-oss checking everything and finishing more. p09, p10 and rmo_2000_6 are the problems neither solo arm solved inside its 1080 s, and on all three both models have accepted steps in the final proof.

**The audit's value shows up as what it kept out, and that was measured earlier, not in these runs.** In the passing runs above the audit verdicts were "holds", "unverified" (no computable witness) or "unstated", and no accepted step was refuted. The case for the audit is the run on `rmo_2000_6` before the audit covered prefix cuts, where a false intermediate claim survived a prefix cut and the run built on it for the rest of the hour (`docs/APPROACH.md`, "Every statement a model writes is audited"). One measured save, not a rate.

## Where the pair did not win

Four problems are 0 on every version of the agent, at 1 h per run: `putnam_2018_a1`, `putnam_2020_a2`, `rmo_2000_2`, `rmo_2001_2`. On each, the board reaches the mathematical crux and carries true, audited facts about it, and neither model lands the Lean technique the crux needs. The clearest case is `putnam_2018_a1`: the divisor enumeration (`Nat.Coprime.divisors_mul` over `2² · 1009²`) was reached in every run and finished in none. A second model checking the first does not add Mathlib knowledge that neither has.

What the pair does add is a second draw from the same distribution, and the transcripts say how much that is worth here. Across 9 earlier runs about 450 rejected steps were the models writing Lean 3 or old Mathlib (a comma at the end of a tactic line, `cases h with a b`, `∑ x in s`, `7!` without `open Nat`), and both models write these. The board fixes them at the parsing layer, not by asking the other model. Measured on `rmo_2000_3`, the `∑ … in` rejections went from 65 of 149 replies to 0 of 42 after a lexical rewrite, which no amount of cross-checking would have found.

## What I would conclude, and what would settle it

On this problem set the pair scored 11 of 16 against 7 for qwen alone and 6 for gpt-oss alone once its two circular passes are removed. The 11 decompose as: 4 closed by Lean's closers with no model call (each solo arm got 3 or 4 of them), p07 with 1 call, 3 that needed model steps and that at least one solo arm also passed (p03, p06, p08), and 3 (p09, p10, rmo_2000_6) where both models contributed steps to a proof that neither solo loop produced inside its clock. The pair's total spend on the 11 was $0.04. The four remaining problems are where the missing piece was a Mathlib lemma neither model knows, and the pair added nothing there. The auditing seat was assigned to gpt-oss on a measurement. The rest of the asymmetry, qwen writing more and gpt-oss landing more of what it writes, was not designed. It came from acceptance rates.

Two experiments would settle what this note cannot. The cheaper one is the kit's own baseline rerun at the board's clock, 3600 s and one worker, on the six problems where a solo arm was cut off (p08, p09, p10, rmo_2000_2, rmo_2000_6, rmo_2001_2): if gpt-oss alone lands p09 or p10 with an hour, the three pair-only wins shrink to one or none. The second is the board with one model in both seats (`VM_LINES` already takes a single model) and the board with the audit disabled, which turns "the pair solved 3 that the solo loops did not" into "the second model is why" or not. Neither had been run when this note was written.
