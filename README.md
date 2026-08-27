# Verified Mechanisms Take-Home Harness

This repository contains the infrastructure for the Verified Mechanisms
research engineer take-home assignment. The applicant is responsible for
implementing an agent in Python. The harness provides the surrounding runtime:
OpenRouter access, per-problem budget accounting, durable logs, concurrent
problem scheduling, Dockerized Lean checking, and final Comparator scoring.

Lean, Mathlib, compiled Mathlib artifacts, the JSON REPL, `lean4export`, and
Comparator are supplied through a pinned Docker image. Applicants do not need a
host Lean, Lake, or Mathlib installation.

## Requirements

- Docker Engine or Docker Desktop
- Python 3.11 or newer
- Approximately 20 GB of free disk space
- At least 8 GB of RAM for one worker

Each additional worker may require roughly 5 GB of additional memory. Linux,
WSL2, Intel Macs, and Apple Silicon Macs are supported.

## Setup

Run the setup script from the repository root:

```bash
bash scripts/setup.sh
```

Create a local environment file and add the OpenRouter API key:

```bash
cp .env.example .env
```

The `.env` file is ignored by Git. During judging, exported environment
variables take precedence over values in `.env`.

## Implementing the Agent

Applicants implement `SubmissionAgent.solve` in `submission/agent.py`.

```python
async def solve(problem: Problem, services: Services) -> AgentResult:
    ...
```

The harness supplies three services:

- `await services.llm.complete(...)` for restricted, budgeted, logged
  OpenRouter calls
- `await services.lean.check_file(source)` for checking a complete Lean file in
  the networkless Lean container
- `services.checkpoint(source)` for preserving a candidate solution during a
  long run

The agent may use any internal design that remains problem-agnostic and follows
the assignment rules. See `docs/AGENT_API.md` for the full interface.

## Running the Harness

Run the default submission agent with:

```bash
.venv/bin/python run.py --problems sample-problems --out outputs
```

Each invocation creates a fresh run directory:

```text
outputs/submission/<run-name>/
```

The run name is generated from the current UTC timestamp.

To resume a previous run for the selected agent:

```bash
.venv/bin/python run.py \
  --problems sample-problems \
  --out outputs \
  --resume latest
```

You may also resume a specific run name:

```bash
.venv/bin/python run.py \
  --problems sample-problems \
  --out outputs \
  --resume 20260819T120000Z
```

## Reference Baseline

A minimal reference agent is available in `baselines/simple_agent.py`. It uses a
single model-driven repair loop with Lean feedback and stops when a candidate
passes the Lean REPL check.

Run it with:

```bash
.venv/bin/python run.py \
  --problems sample-problems \
  --out outputs \
  --agent baselines.simple_agent:create_agent
```

Baseline runs are written under:

```text
outputs/baseline/<run-name>/
```

The baseline can be configured with:

- `BASELINE_MODEL`
- `BASELINE_MAX_TURNS`
- `BASELINE_MAX_TOKENS`
- `BASELINE_TEMPERATURE`

## Parallel Execution

Use `--n-workers` to run independent problems concurrently:

```bash
.venv/bin/python run.py \
  --problems sample-problems \
  --out outputs \
  --n-workers 2
```

Each worker receives its own process, budget ledger, deadline, output
directory, and Lean container. The value of `--n-workers` does not create
additional model calls within a single problem.

## Checks

Run the no-key smoke test:

```bash
bash scripts/smoke_test.sh
```

Before submitting, run the judging contract check:

```bash
bash scripts/judge_check.sh
```

## Output Artifacts

For each problem, the runner writes:

- `solution.lean`
- `result.json`
- `transcript.json`
- `events.jsonl`
- `checkpoint.json`
- `worker-config.json`

The run directory also contains:

- `run.json`
- `summary.json`

The `events.jsonl` file is append-only and flushed incrementally. The
`transcript.json` file is derived from those events and contains the full LLM
requests, responses, token usage, costs, timings, and errors with secrets
redacted.

To rescore saved solutions, pass the concrete run directory:

```bash
bash scripts/rescore.sh outputs/submission/20260819T120000Z
```

## Scoring

A problem receives one point when all of the following conditions hold:

- Comparator accepts every required declaration.
- Numeric answer declarations, when present, have valid literal bodies.
- Actual OpenRouter spend is at most `$1.00`.
- The problem finishes within its deadline.

Model participation is reported in `result.json`. It is reviewed separately
from the mechanical one-point score.

See `RULES.md` for the complete assignment rules.

## Repository Structure

| Path | Purpose |
| --- | --- |
| `RULES.md` | Assignment rules, budgets, and judging behavior |
| `submission/agent.py` | Applicant implementation |
| `baselines/` | Reference agent implementations |
| `src/re_harness/` | Runner, services, accounting, logs, and evaluator |
| `sample-problems/` | Public problems and versioned manifest |
| `docker/` | Source for the Lean runtime image |
| `docs/` | Agent API, setup, artifacts, and security model |
| `scripts/` | Setup, smoke test, rescore, and judging checks |
