#!/usr/bin/env bash
# Run the applicant's default agent under the same one-problem contract as judging.
set -euo pipefail
cd "$(dirname "$0")/.."
# p01_linear is closed by the agent's deterministic tactic sweep with zero model
# calls, so it exercises none of the LLM path this script exists to protect.
PROBLEM="${JUDGE_CHECK_PROBLEM:-p06_pow_mod}"
test -x .venv/bin/python || { echo "Run bash scripts/setup.sh first." >&2; exit 1; }
.venv/bin/python - <<'PY'
from re_harness.config import HarnessSettings
if not HarnessSettings.from_env(n_workers=1).api_key:
    raise SystemExit("Set OPENROUTER_API_KEY in .env or the environment")
PY

WORK=$(mktemp -d "${TMPDIR:-/tmp}/re-takehome-judge.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/problems/$PROBLEM" "$WORK/outputs"
cp "sample-problems/$PROBLEM/problem.md" "sample-problems/$PROBLEM/challenge.lean" \
  "$WORK/problems/$PROBLEM/"
.venv/bin/python - "$WORK/problems/manifest.json" "$PROBLEM" <<'PY'
import json, sys
from pathlib import Path
source = json.loads(Path("sample-problems/manifest.json").read_text())
source["set"] = "judge-check"
source["problems"] = [p for p in source["problems"] if p["id"] == sys.argv[2]]
Path(sys.argv[1]).write_text(json.dumps(source, indent=2) + "\n")
PY

VM_TIME_LIMIT_S=28800 VM_BUDGET_USD=1.00 .venv/bin/python run.py \
  --problems "$WORK/problems" --out "$WORK/outputs" --n-workers 1

.venv/bin/python - "$WORK/outputs" "$PROBLEM" <<'PY'
import json, sys
from pathlib import Path
root = Path(sys.argv[1])
candidates = sorted((root / "submission").glob("*"))
if len(candidates) != 1 or not candidates[0].is_dir():
    raise SystemExit(f"Expected exactly one timestamped submission run under {root}")
out = candidates[0]
required = [
    out / "run.json", out / "summary.json",
    out / sys.argv[2] / "solution.lean",
    out / sys.argv[2] / "result.json",
    out / sys.argv[2] / "transcript.json",
    out / sys.argv[2] / "events.jsonl",
]
missing = [str(path) for path in required if not path.exists()]
if missing:
    raise SystemExit("Missing contract artifacts: " + ", ".join(missing))
result = json.loads((out / sys.argv[2] / "result.json").read_text())
transcript = json.loads((out / sys.argv[2] / "transcript.json").read_text())
assert isinstance(transcript.get("calls"), list), "transcript calls must be a list"
assert result.get("passed") is True, f"{sys.argv[2]} did not pass: {result.get('status')}"
# A problem the deterministic sweep can close would pass every assertion above
# without ever calling a model, which is how this check was silently vacuous.
assert transcript["calls"], "no model was called, so the LLM path went unchecked"
assert result["budget"]["spent_usd"] > 0, "no spend recorded, so accounting went unchecked"
assert result["budget"]["accounting_complete"] is True, "budget accounting did not close"
assert result["models_used"], "result.json recorded no models_used"
print(f"judge_check PASSED: {out}")
PY
