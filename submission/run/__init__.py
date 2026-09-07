"""One run of one problem, in the order the parts depend on each other.

    context -> budget -> delivery -> blackboard -> asking -> ladder -> loop

Each imports only from its left. The order is the imports, not the state:
`run.notes` is one dictionary and four of these parts write it.
`submission/board/` below holds what they call and the containers they hold;
`board_agent.py` above holds `solve`, the spine that wires these seven."""
