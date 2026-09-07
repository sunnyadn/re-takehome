"""The board's vocabulary, and the functions that read and build its Lean.

`types` holds the containers and the methods that mutate them; `reply` reads a
model's answer, `text` reads and rewrites the Lean the board holds, `probes`
builds files that ask Lean one question. Those three take what they need and
return a value. The run's own state lives in `submission/run/`, in the
containers `types` defines. Two functions here do reach outside:
`container_memory_bytes` shells out to docker, and `dump_check` writes files
when VM_DUMP_DIR is set."""
