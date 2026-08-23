# Literature and industry evidence for Part 2

Standing rule: nothing here is a citation until the primary source has been read
in full ([[read-full-paper-before-discussing]]). Tags below record how strong the
current evidence is, not permission to cite.
FT = full text read by the research agent · AB = abstract verbatim · PP = paraphrase, unverified.

## The finding that most affects our design

Compute-matched evidence splits by **mechanism**, not by "multi-model vs single":

- **Independent allocation across models, union taken by a verifier — POSITIVE.**
  OSCA, arXiv:2410.22480, NAACL 2025. A "configuration" explicitly includes which
  model to use; mixes GPT-4o/Gemini/DeepSeek and Qwen2/Llama3/DeepSeek. Claims
  better accuracy than the best single configuration at 128x less compute on code
  generation, 25x on reasoning, 3x on SWE-Bench. [FT, but the 128x is an
  abstract-level claim the agent could not reconcile with its table extraction]
- **Interactive coordination (debate, critique, orchestration) — NEGATIVE.**
  "Capable language models can outgrow the benefits of collaboration", Nature
  Machine Intelligence 8:1157-1172 (2026-07-24), DOI 10.1038/s42256-026-01268-y.
  260 configurations, 6 benchmarks, 5 architectures, 3 model families, matched
  per-system reasoning-token budgets. [FT]

**Our architecture sits on the positive side of that split** (two independent
lines, compiler takes the union). **Our one coordination rule — stall-triggered
handoff — sits on the negative side.** It is one rule and it has an on/off
switch, so it must be ablated and reported honestly either way.

## The prediction we should pre-register against ourselves

Nature MI reports a **~45% capability-saturation threshold**: single-agent
baselines above ~45% predict zero-to-negative multi-agent gains, sign matched in
94% of 16 SWE-bench Verified and Terminal-Bench configurations.

**Kit baselines: gpt-oss 8/16 = 50%, qwen 7/16 = 44%.** Our stronger model is
already above the threshold, so the published prior predicts **no coordination
gain at matched compute on this problem set**. Say this in Part 2 before showing
our own numbers.

Their heterogeneity sub-study is the closest published analogue to our exact
question: 13 heterogeneous configurations on BrowseComp-Plus, mixing within and
across families, found no evidence that model mixing bypasses the threshold.
Centralized heterogeneous underperformed the strong-model homogeneous baseline by
a mean of 12.6 pp; decentralized gained 2.0 pp, attributed to the stronger
constituent model alone.

## The null hypothesis, in our exact domain

DeepSeek-Prover-V2, arXiv:2504.21801, miniF2F-test, CoT, Lean 4 compiler as
verifier. 671B: pass@1 61.9% -> pass@32 82.4% -> pass@1024 86.6% -> pass@8192
88.9%. [FT, Table 1]

Concave in log k: +20.5pp for the first 32x, +4.2pp for the next 32x, +2.3pp for
the last 8x. **This sets the whole trade.** Splitting a budget between two models
costs the concave top of the strong model's curve and buys the other model's
disjoint coverage. At high k the last 8x is worth 2.3pp so splitting is nearly
free; at low k the curve is steep and splitting is expensive. We need to work out
where $1 and 8 hours puts us on that curve before claiming anything.

Also from that table: the gap between 7B and 671B *widens* with sample budget,
i.e. the stronger model has better sample efficiency. Cuts against splitting.

Repeated sampling generally: Large Language Monkeys, arXiv:2407.21787. Coverage
log-linear over four orders of magnitude. [FT] Caveat that matters to us,
verbatim: the scaling law fits *worst* on MiniF2F-MATH, the Lean dataset. Do not
assume clean log-linearity in our domain.

## What does not transfer, and why

Discount every gain measured under an LLM judge. MoA (arXiv:2406.04692, 65.1 vs
57.5 on AlpacaEval 2.0), ColMAD (arXiv:2510.20963), and most of the debate
literature are scored on free-form answers where **selection** is the bottleneck.
The Lean comparator removes that bottleneck for free, so those gains do not port.

Majority voting and self-consistency (arXiv:2402.05120, arXiv:2203.11171) are the
wrong comparison class entirely: with a perfect verifier, voting is strictly
dominated by pass@k coverage. File as not applicable.

Oracle-union numbers are real but uncontrolled: arXiv:2510.21513 reports union vs
best single of +83% (Defects4J), +19% (LiveCodeBench), +15% (HumanEval-Java), each
model generating 10 outputs independently, so the ensemble spent strictly more
compute. **But the transfer caveat cuts our way**: their selection apparatus
exists because they cannot verify, and a compiler deletes that problem, so the
oracle union is realizable for us if we can pay for both models' samples.

## Negative and matched-compute results worth citing

- Smit et al., ICML 2024, arXiv:2311.17371. MAD does not reliably beat
  self-consistency or ensembling; reads as tuning-sensitive. Best peer-reviewed
  negative in the classic debate literature. [PP]
- Wang et al., ACL 2024, arXiv:2402.18272. A single agent with strong prompts
  matches the best discussion approach; multi-agent wins only when the prompt has
  no demonstrations. [PP]
- Chen et al., arXiv:2403.02419. Vote and Filter-Vote are **non-monotonic** in
  number of LM calls: more calls help easy queries and hurt hard ones. [AB]
- Tran & Kiela, arXiv:2604.02460. Single-agent matches or beats multi-agent at
  equal reasoning-token budget across three model families. Also flags artifacts
  in API-based budget control that inflate apparent MAS gains. Unreviewed. [AB]
- Self-MoA, arXiv:2502.00674. Aggregating only the top model beats mixing, by
  6.6% on AlpacaEval and 3.8% across MMLU/CRUX/MATH. [AB]

## Methodology, and what n=16 actually buys

AI Agents That Matter, arXiv:2407.01502. Simple baselines Pareto-dominate
Reflexion/LDB/LATS on HumanEval at 50x lower cost. Report an accuracy-vs-cost
Pareto curve, not a point. [PP]

Adding Error Bars to Evals, arXiv:2411.00640 (Miller, Anthropic). Paired
differences for two-model comparison, variance reduction, power. Read S2-S3
before quoting any formula. [AB]

Computed for our n, and independently checkable:

- One problem = **6.25 pp**. We cannot report a "3 pp improvement".
- Clopper-Pearson 95% CI at 8/16 is [24.7%, 75.3%], 50.7 pp wide. Unpaired
  comparison at this n is uninformative.
- **Go paired.** Exact McNemar, all flips one way: b=4 -> p=0.125, b=5 -> 0.0625,
  **b=6 -> 0.031**, b=7 -> 0.016. We need **6 problems solved by the duo and not
  by the solo arm, with zero going the other way**, to clear p<0.05. That is ~40%
  of the set.
- Precedent: the Nature MI threshold validation was itself n=16 and reported a
  sign-match rate, not a significance test. Their SWE-bench runs used 20-instance
  subsets and they flag it themselves.

**Reporting shape for Part 2**: coverage-vs-dollars curve per arm on a log x-axis,
per-problem paired outcome table, exact McNemar, Clopper-Pearson at full width,
and an explicit sentence that n=16 cannot resolve effects below 2-3 problems.

## Gap the search could not close

No peer-reviewed study isolating exactly **two** models, union coverage, total
compute held constant, in formal theorem proving. OSCA is closest on allocation
(compute-matched, but code/reasoning and more than 2 configs); the Nature MI
heterogeneity sub-study is closest on coordination (13 configs, matched compute,
but BrowseComp-Plus). Say so rather than stretching either citation.

## Our own error taxonomy, measured (2026-08-22)

Counted from the shipped baseline corpus with one consistent classifier.
**Count errors per check, not per instance.** The two views disagree sharply and
the per-instance view is misleading.

Per error instance (n=4274): no goals 59.2%, unknown name 14.6%, unsolved goals
6.9%, type mismatch 5.7%, arith failed 4.7%. The "no goals" mass is almost
entirely qwen (2525 of 2530) and comes from a handful of candidates emitting
hundreds each.

Per failed Lean check (284 of 318 checks had at least one error):

| category | in this % of failed checks | is the ONLY error class |
| --- | --- | --- |
| unsolved goals | 48.9% | 13.4% |
| arith tactic failed | 35.2% | 9.2% |
| unknown name (hallucinated) | 32.0% | 2.5% |
| type mismatch | 25.0% | 0.7% |
| no goals | 19.0% | 2.5% |
| syntax | 15.8% | 7.0% |
| resource limit | 8.1% | 2.5% |

**Two conclusions that change what is worth building.**

1. `no goals` is 59% of instances but only 19% of failed checks. It is not the
   high-leverage target it looks like from the instance count.
2. **No category is the sole error in more than 13.4% of failed checks.** Failed
   candidates are broadly broken, not one fix away. Solving hallucinated names
   outright would clear only 2.5% of failed checks, which is consistent with the
   literature (retrieval buys +1.1pp on a fine-tuned model, REAL-Prover
   arXiv:2505.20613). The dominant classes, unsolved goals and failed arithmetic
   tactics, are capability limits, not mechanical ones.

For reference, arXiv:2606.05632 puts unknown-identifier at 5.6% of miniF2F
failures and 9.3% on miniCTX. Ours at 14.6% of instances is higher but the same
order, so our models are not outliers on this axis.

## The gap worth claiming in Part 2

Verbatim from the survey: prompted small general models in a Lean repair loop are
measured nowhere. Every depth-positive Lean repair result uses a frontier model
(Gemini 2.5 Pro, o3/o4-mini, Claude Sonnet 4.5) or a fine-tuned prover; the one
clean small-general-model result with a matched budget and a placebo control
(arXiv:2607.26117, Qwen2.5-Coder 1.5B/3B/7B, MBPP+) finds the opposite, that
blind resampling Pareto-dominates feedback repair below 7B.

**Our two models sit exactly in that unmeasured regime.**

**Therefore add a placebo arm.** Same loop, same budget, error trace replaced by a
content-free "that failed, try again". If our loop's advantage over blind
resampling does not survive the placebo, that is the finding, and it is a more
honest answer to "does collaboration help" than any duo-vs-solo table.

Supporting numbers from that paper, matched budget, McNemar + Holm:
placebo minus resample = -6.1pp (p=0.006) at 1.5B, -6.9pp (p<0.001) at 3B, tie at
7B. Conditioning on its own failed code pushes near-identical retries from 2-14%
up to 33-68%.

## Prompt labelling, acted on

arXiv:2608.13571 prepends an *unlabelled* failed chain and loses 34.8pp
(73.9 -> 39.1) on the stratum the first model failed, McNemar p=0.0078, n=23,
never improving on any query. Olausson (ICLR 2024) attaches a *labelled* failing
program plus its execution error and gains. Reflexion (NeurIPS 2023) isolates the
same variable within one model: verbalized reflection beats raw trajectory memory
by 8 points absolute. The variable is how the failure is presented, not whether it
is present.

Our repair prompt said "Current file" and "Lean compiler output", which is
neutral. Changed to "This file was submitted to Lean and rejected" and "Lean
rejected it with". Free, and on the right side of the only direct A/B available.

## Parameter check against the literature

- **Repair depth.** 2-3 rounds is where every measured setting flattens. APOLLO
  (arXiv:2505.05758) Figure 5 specifically: general-purpose models gain almost
  everything between recursion depth 0 and 1 then plateau, while fine-tuned
  provers keep climbing. Do not import depth settings from prover papers.
- **Our stall rule is on the safe side.** arXiv:2608.18084 sweeps a stagnation
  threshold: switching too early is the expensive error (K/12 costs 12pp *and*
  more calls than K/4). Our patient error-signature rule is the right shape.
- **Budget.** That survey prices cheap models under $0.01 per attempt, so $1 per
  problem is roughly k=100. We are spending about $0.12, i.e. k=12. Published
  decomposition agents run 20-55x our budget per problem, so full decomposition is
  out of reach; the affordable slice is APOLLO's deterministic Syntax Refiner plus
  AutoSolver, which took o4-mini from 7.0% to 20.5% on miniF2F-test before any LLM
  re-invocation.

## Industry evidence (2026-08-22)

**No shipped product publishes evidence that splitting work across two models beats
one good model on quality.** Every head-to-head shows parity or slightly worse
quality at materially lower cost. Splitting is a cost and latency technique.

1. **Cognition 2x2, n=3000 sessions, FrontierCode 1.1** — the only properly
   controlled single-variable experiment in this space.
   https://cognition.com/blog/making-fable-cheaper-than-opus
   Fable 5 alone 60.8 @ $4.03 vs Fable 5 + Sidekick 60.7 @ $1.86.
   Opus 4.8 alone 55.4 @ $3.06 vs Opus 4.8 + Sidekick 54.6 @ $2.04.
   Both arms the split is slightly worse (-0.1pp, -0.8pp) at 54% and 33% less
   cost. Vendor's own framing is a cost claim, never a quality claim.
   Vendor benchmark, no independent reproduction, no CIs.
2. **The verifier loop beats the role split by roughly 10x.** From Aider's own
   committed leaderboard data, `pass_rate_1` -> `pass_rate_2`: one grader-informed
   retry is worth **+29 to +43pp**. The entire cross-model role split is worth
   **0 to 7pp**, mostly inside the noise floor (1 sigma about 3pp at n=225).
   Anthropic's multi-agent write-up corroborates the compute-not-diversity
   reading: their own variance decomposition says token usage alone explains 80%
   of the variance.
3. **Production splits are always strong-to-cheap downgrades, never peers.** Of
   357 Aider model configs, the 105 naming a distinct editor model are unanimously
   downgrades (o3 -> gpt-4.1, opus -> sonnet, gemini-pro -> flash). **Zero pair two
   peers of comparable strength.** Aider's shipped default editor is the *same*
   model. And Sonnet+Sonnet (+3.1pp) beat Sonnet+DeepSeek (+1.5pp) in their 2024
   data. **Our two models are peers (7/16 and 8/16), so the production pattern
   does not describe our situation.**
4. **The one cost-matched positive**: Aider R1 (architect) + Sonnet (editor)
   64.0% vs Sonnet alone 51.6% at 0.92x cost, z=2.68. But against R1, the stronger
   member, the gain is +7.1pp at 2.45x cost, inside noise. Run once, never
   replicated. https://aider.chat/2025/01/24/r1-sonnet.html
   Nearest cost-matched pair on the polyglot board favours the single model:
   gpt-5 solo 86.7% @ $17.69 vs o3+gpt-4.1 architect 78.2% @ $17.55.
5. **Two vendors walked a split back.** Cognition shipped SWE-1.5-as-primary plus
   Sonnet 4.5 as consultant and abandoned it, verbatim: "the gap between it and
   Sonnet 4.5 was too wide in exactly the places that mattered for this setup:
   knowing when to escalate, knowing what to ask." Their generalizable lesson is
   the sentence to quote: **the quality ceiling is set by the primary model, and a
   split cannot raise it.**
6. **Nobody holds cost fixed.** Not Aider, Cursor, Copilot, Cognition, or any
   router vendor. And no published comparison of a split against the obvious
   cost-matched competitor: **best-of-N with one model against a verifier.** That
   gap is itself reportable.

### Why this decides the Part 2 thesis

Every industry rationale for splitting is **cost**. Our scoring function does not
price cost at all: $1 is a cap, not a metric, and we are currently using about
12% of it. **The entire industry case for multi-model splitting is worth zero
points here.** Combined with Nature MI's matched-compute negative on interactive
coordination and its ~45% saturation threshold (our stronger model is at 50%),
three independent lines converge on the same prediction.

## Measured model settings (2026-08-22, this harness, this key)

**gpt-oss-120b `reasoning.effort: high` is unusable and would have cost us
points.** It spends the entire token budget on reasoning and returns empty
content, at every cap up to the harness maximum, on a hard problem:

| effort | max_tokens | reasoning tok | content chars | finish | cost | secs |
| --- | --- | --- | --- | --- | --- | --- |
| medium | 8000 | 2065 | 2880 | stop | $0.0007 | 148 |
| high | 8000 | 5541 | **0** | length | $0.0014 | 160 |
| high | 16000 | 10573 | **0** | length | $0.0027 | 355 |
| high | 24000 | 15766 | **0** | length | $0.0041 | 435 |
| high | 32000 | 23278 | **0** | length | $0.0055 | 592 |
| medium | 16000 | 1724 | 2974 | stop | $0.0007 | 72 |

**Corrected after being challenged on whether the cap was simply too small.** It
was, and the right statement is narrower. Going above the harness ceiling to
max_tokens 60000 on the same problem: reasoning 42606, content 946 chars, still
`length`, 1175s, $0.0102. So high does eventually start emitting a proof, at
about 42k reasoning tokens, which is above the 32k the harness allows.

The escape hatch is closed: `reasoning.max_tokens`, which would cap reasoning and
leave room for content, is **rejected by gpt-oss with HTTP 400** (5/5 attempts at
both 8000 and 16000). This model takes `effort` only.

Control on the same problem and cap: medium @32000 gives reasoning 4358, content
3314 chars, `stop`, 145s, $0.0013. So the difference is effort, not the cap.

On the easy problem p01, high @16000 works (3582 reasoning, 165 chars, stop), so
the reasoning length is problem-dependent.

**Accurate claim**: high effort cannot complete a hard problem within the
harness's 32k output ceiling, and there is no way to bound its reasoning to make
room. Separately, even unbounded it took 19.6 minutes and $0.0102 for one
unfinished call, so 8 hours would buy about 24 of them. Kept at medium.

**qwen thinking is off, and `effort` is not the switch.** On p09, max_tokens 16000:

| reasoning field sent | reasoning tokens |
| --- | --- |
| `{"effort": "medium"}` (what we ship) | 0 |
| `{"effort": "high"}` | 0 |
| `{"enabled": true}` | 0 |
| `{"max_tokens": 8000}` | **1438** |
| `{"enabled": true, "max_tokens": 8000}` | 659 |

Only `reasoning.max_tokens` turns it on. **Do not flip this without an A/B on
solve rate** — the gpt-oss high result above is what happens when a plausible
capability upgrade is taken on faith.

## The finding that indicts our repair loop, and what replaces it

arXiv:2606.05632 classified 56,443 failures across 14 models. **gpt-oss-120b's
refine@32 minus pass@32 is exactly 0.0 on miniF2F and 0.0 on miniCTX.** Feeding
the error text back as plain prose buys this model nothing. Our repair loop is
exactly that shape.

What is measured to work is an **interactive tool loop**: goal state, Mathlib
lookup, and a symbolic tactic layer under the LLM.
- Lyra (TMLR, arXiv:2309.15806) Table 2 separates the two: error feedback alone
  moves GPT-4 42.6 -> 43.0 on miniF2F-test and *down* on valid (50.4 -> 46.7);
  stacked on a tool layer it moves 45.9 -> 51.2.
- DSP (ICLR 2023) ablation: removing the informal draft costs 5.3pp, removing the
  automated provers costs **9.0pp**. The symbolic layer was the bigger lever even
  in 2022.
- APOLLO on o4-mini: Syntax Refiner alone 7.4%, AutoSolver alone 7.0%, the two
  together **20.5%**, all three modules 46.7%. Strongly superadditive.
- COPRA (COLM 2024): GPT-4 at 60 independent samples 15.98% vs the same 60 queries
  inside a state-carrying loop with execution feedback and Mathlib retrieval
  **26.63%**.

### gpt-oss-120b's measured failure fingerprint, and ours

arXiv:2606.05632, gpt-oss-120b column: type mismatch **27.8% (highest of 14
models)**, unsolved goals 19.5%, hallucinated identifier **15.1% (highest)**,
syntax **2.3% (lowest)**, generation failure **1.4% (lowest)**.

**Our own measurement independently agrees**: on our gpt-oss baseline errors,
type mismatch is the top category (158 of 472) with unsolved goals next (121).

Consequence: **do not copy APOLLO's module order.** Its Syntax Refiner exists for
Lean-3-isms that gpt-oss-120b does not emit (it is the *least* syntax-error-prone
model in that table). Our budget belongs on the classes that are actually ours.

### Verified on our own cluster, 2026-08-22

All five through the harness's own `check_file`, which sends arbitrary source to a
warm `import Mathlib` REPL. Offline, no network, and `RULES.md` explicitly permits
generic tactic libraries.

| probe | result |
| --- | --- |
| `by first \| omega \| simp \| aesop` | accepted, zero LLM tokens |
| `exact?` | returns `Try this: exact Nat.add_comm a b` |
| `#print axioms` on a clean proof | `'t2' depends on axioms: [propext]` |
| `#print axioms` on `native_decide` | **REPL says accepted=True**, axioms line exposes `t3._native.native_decide.ax_1` |
| `#print axioms` on `sorry` | `'t4' depends on axioms: [sorryAx]` |

**Row 4 is the silent zero.** The REPL accepts the file and the Comparator would
reject it. A lexical denylist cannot close this in general, because `native_decide`
and `bv_decide` mint a fresh axiom name per computation, so the name is not
enumerable in advance. Replaced with an allowlist: append `#print axioms <name>`
for every declaration parsed out of the challenge, and require the reported set to
be a subset of {propext, Classical.choice, Quot.sound}. `judge_check` still passes
1/1 at real judging settings with the probe appended.

Network limit checked: `RULES.md` allows only openrouter.ai at run time, so
`#leansearch` and `#loogle` (which call out to a service) are **out**. `exact?`,
`apply?`, `simp?`, `aesop`, `grind`, `omega`, `norm_num`, `nlinarith` are local and
fine.
