# Design: where things live

## The system in four lines

One Lean file is the board. Every open `sorry` on it is a goal. Two workers
take goals, and for each one they try the cheap things first and ask a model
last. Lean decides what is allowed to stay.

## What the two workers actually share

Measured, because it decides how much of the rest matters. With both workers
running against a fake Lean that really suspends, the greatest number of Lean
checks in flight at once is **one**.

That is not an accident of the test. There is one Lean container per problem,
so checks cannot overlap however the board is arranged. **The second worker
exists to overlap model latency, not Lean.** Everything the board lock does
follows from that: it is protecting a resource that was serial to begin with.

A test now says so, and fails if a check ever escapes the lock.

## The parts

| Part | Owns | Answers |
| --- | --- | --- |
| `Runtime` | Lean, the two models, the clock, the ledger, the probe budget | what did this cost, how long is left |
| `Board` | the file, its open goals, the branches, forking and pruning | what is open, what did we try instead |
| `Notes` | one record per goal | has this goal been down this route already |
| `Cells` | statements by cell id, for the whole run | what was this cell supposed to prove |
| `Delivery` | the best file so far, the checkpoint, the final shape | what would we hand in if killed now |

Below those sit the modules with no state at all, which are already right and
are not touched: `framework.py` and `cells.py` for reading and rewriting Lean
text, and `leaves.py`, `techniques.py`, `conjecture.py`, `sampling.py` for
turning the shape of a goal into a tactic block.

## The test: given a bug report, which file

| Report | Now | After |
| --- | --- | --- |
| "the leaf sweep ran twice on the same goal" | somewhere in `solve` | `Notes` |
| "we handed in a file the comparator rejected" | somewhere in `solve` | `Delivery` |
| "one problem burned ninety cents" | somewhere in `solve` | `Runtime` |
| "cell 12 lost its statement on reset" | somewhere in `solve` | `Cells` |

"Somewhere in `solve`" is literal. `solve` is 1604 lines holding 39 locals
shared among 40 nested functions, down from 53 since the goal records were
collapsed into one.

## The ladder is three gates, not eight steps

An earlier draft of this document proposed a tuple of step objects walked in
order. That was wrong, and the reason is worth keeping.

The free steps do not have one gate each. They have three, and the grouping is
a measured policy rather than an accident:

| Gate | Covers | Why grouped |
| --- | --- | --- |
| `recalled` | recall | a statement proved once is replayed once |
| `swept` | cocktail, leaf, witness, generalise | one round of cheap attempts per goal, not four |
| `searched` + `tries >= SEARCH_AFTER` | library search, consult | `apply?` and the name scan measured 19% of wall clock, under the lock |

Give each step its own gate and the four under `swept` become one: the first
to run sets the flag and the other three never fire again. The grouping is the
design. It is also not flat: `generalise_sweep` calls `library_sweep` on a
*different* goal, at a line above where `library_sweep` is defined.

So the ladder stays written out. What a reader needs is not an abstraction
over it but the table above, which says what is tried, in what order, and what
stops each thing from being tried twice.

Adding a step is still cheap, in the place the grouping puts it. The gap
measured today is induction over the naturals: `y2021_div_pow` took 932
seconds and `y2023_cubes` did not close. That step belongs under `swept`, so
it is one function and one more `or` in that chain, plus a field on the record.

## Where a model gets asked

Three places, and only one of them is obvious:

1. the plan, twice, with the board handed back while both calls are in flight
2. the step, with the board handed back the same way
3. **the audit**, which runs inside the lock, with `AUDIT_WAIT_S` at 120 seconds

The third is easy to miss and this document previously got it wrong. Every
edit that is accepted goes through `apply`, `apply` reaches `audit`, and
`audit` asks the other model whether the statement is true. That call is made
with the board held. It has never been observed to hit its timeout, across 53
runs, but the shape is real and a reader should not have to discover it.

## Staging

Each stage is worth having alone, and each is checked before the next.

1. **One record per goal** in place of fifteen tables keyed by the goal key.
   Done, and the six board-loop hashes are identical.
2. **`Runtime`.** Safe, and the largest single reduction left.
3. **`Board`.** Possible, with two landmines named below that must be handled
   first, and its own unit tests for fork, prune and re-find.
4. ~~Steps as a tuple.~~ Withdrawn, for the reason in the ladder section.
5. **`Delivery`**, and `solve` becomes its entry.

## How each stage is checked, and what the check cannot see

Ten of the sixteen sample problems close with no model call, so their runs are
deterministic: the ordered `lean_check` source hashes and the final
`solution.lean` match or they do not, in seconds, with none of the variance a
score-only sweep has.

The instrument's reach was measured rather than assumed. Four of the ten never
enter the board loop:

| `solved_by` | Problems |
| --- | --- |
| `deterministic_sweep` | p01_linear, p02_frac_cancel, p04_sum_sq, p05_gcd_mersenne |
| `board_loop` | p06_pow_mod, putnam_2018_a1, putnam_2020_a2, rmo_2000_2, rmo_2000_3, rmo_2000_6 |

Six runs exercise the loop. They cover goal bookkeeping, the free steps,
commits and delivery. They do not cover forking, the audit, or two workers
contending, and no recording can: the fake Lean in the fixtures has no `await`
in its body, so awaiting it never yields and the second worker is never
scheduled. `YieldingLean` is the opt-in fixture that does suspend. It is not
the default because three stall tests drive their clock off the *number* of
`time.monotonic` calls, so an extra suspension point moves their simulated
time by 200 seconds and they stop testing what they say they test.

## Landmines, named rather than left to be found

* `generalise_sweep` rebinds `text` as a local with no `nonlocal`. Today that
  shadowing is invisible. Promote `text` to an attribute on any object and
  that line starts overwriting the import prefix every later `consult` and
  `witness_sweep` builds, and the fallback `commit` uses when a board goes
  unsound. Silent, delayed, with no test between it and the judge.
* `cocktail` is a 40th shared local, assigned after every closure that reads
  it is defined, and read by the cocktail sweep. It works because the workers
  start later. It belongs to none of the five parts.
* `framework.py` imports from `agent.py` above it, and the cycle is broken
  only by a function-local import in `agent.py`. Hoisting that import to
  module scope breaks the graded entry point at import time.
* `board_agent.py:3078` is a bare `if True:` from an earlier reshape.

Two module names resolve from strings and stay: `submission.agent:create_agent`,
which is what the judge's bare `python run.py` loads, and
`submission.board_agent:create_agent`.

## Corrections to earlier drafts of this document

| Claim | Correction |
| --- | --- |
| Nine rungs, then eight | Seven free steps behind three gates |
| Seventeen goal-keyed tables, twenty elsewhere | Fifteen |
| The bottom layers are pure | `cells.Cells` holds mutable run-scoped state |
| Each layer knows only those below | `framework.py` imports from `agent.py` |
| Ten locals mutated through `nonlocal` | Eight belong to `solve` |
| Paid steps release the lock | The audit asks a model with the lock held |
| The steps become a uniform tuple | They share three gates and one calls another across goals |
| The hash check covers the refactor | Six of sixteen problems, and no recording can show contention |
