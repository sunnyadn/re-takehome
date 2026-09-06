"""The entry point the harness resolves.

The program is `submission/board_agent.py` and its parts are in
`submission/run/`. What the agents here share sits beside this file:
`config` for how a run is set up, `contract` for what the grader accepts,
`sweep` for the first attempt that costs nothing."""

from __future__ import annotations

from submission.board_agent import BoardAgent, create_agent as board_agent


def create_agent() -> BoardAgent:
    """The graded entry point: the goal board."""

    return board_agent()
