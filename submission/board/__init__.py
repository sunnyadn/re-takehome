"""The board's pure layer: no state, no I/O, no lock.

`types` is the vocabulary, `reply` reads a model's answer, `text` reads and
rewrites the Lean the board holds, `probes` builds files that ask Lean one
question. `submission/board_agent.py` above them is the part that has state."""
