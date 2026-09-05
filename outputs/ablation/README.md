# The leaves-off ablation cited in docs/PART2.md

The final commit with `VM_LEAVES=off` (the shape-built tactic blocks of `submission/leaves.py` skipped, everything else unchanged), `VM_TIME_LIMIT_S=1800` for the sample problems and `3600` for the others, `VM_BUDGET_USD=1.00`, one worker, the same 4-core machine as `outputs/board/`. One run per problem. `rmo_2001_2` had not finished and `rmo_2000_3` was not run when the note was submitted.

Each run directory holds `run.json`, `summary.json` and the problem's `result.json`, `transcript.json`, `solution.lean` and `worker-config.json`. The per-check `events.jsonl` and `checkpoint.json` are left out for size.
