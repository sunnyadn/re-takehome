# The ablation matrix cited in docs/PART2.md

Commit v7.91 (the shipped code of 3 September), `VM_TIME_LIMIT_S=1800`, `VM_BUDGET_USD=1.00`, one worker, on the same 4-core machine as `outputs/board/`. Three problems, two runs per cell, run as copies of the sample problems so that the lanes could run in parallel (`p09m*` is `p09_imo1964`, `p10m*` is `p10_factorial_pow`, `rmo6m*` is `rmo_2000_6`).

| directory | arm |
| --- | --- |
| `pair/` | both models, the audit on (the submission as it runs) |
| `qwen-both-seats/` | `qwen/qwen3.5-flash-02-23` in both seats |
| `gpt-oss-both-seats/` | `openai/gpt-oss-120b` in both seats |
| `no-audit/` | both models, the audit off |

Each run directory holds `run.json`, `summary.json` and the problem's `result.json`, `transcript.json`, `solution.lean` and `worker-config.json`. The per-check `events.jsonl` and `checkpoint.json` are left out for size (47 MB across the 24 runs).
