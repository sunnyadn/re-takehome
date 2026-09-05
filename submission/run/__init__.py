"""The parts of one run that hold state, in strict dependency order.

`budget` depends on nothing, `delivery` and `asking` on `budget`, `branches`
on those, `ladder` above them, `loop` on all of it. `submission/board/` below
is the layer with no state at all, and `submission/board_agent.py` is the
fifty lines that wire these together and run the problem."""
