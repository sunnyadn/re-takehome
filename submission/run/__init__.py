"""One run of one problem, in the order the parts depend on each other.

    context -> budget -> delivery -> blackboard -> asking -> ladder -> loop

Each imports only from its left. This is where the run's state lives.
`submission/board/` below holds the functions they call; `board_agent.py`
above holds `solve`, the spine that wires these seven together."""
