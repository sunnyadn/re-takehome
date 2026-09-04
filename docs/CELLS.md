# B — goal-local checking (cells)

## Why
One declaration = one heartbeat budget (200000), one REPL memory footprint, and every
check re-elaborates the whole theorem. Measured: rmo_2001_2's divisor leaf needs ~170k
heartbeats alone (fails at 150k, passes at 200k in a fresh theorem) so any earlier step on
the board starves it (h98: 5 leaf tries, all `maximum number of heartbeats (200000)`);
p10's board grows ~300 MB per check (renews); check time grows with file length.

## Model
- Cell(id, statement, text, children, parent, kind ∈ {graded, shared, goal}).
  `text` is a complete small declaration: `theorem vm_cell_k <binders> : <target> := by …`.
  Graded cells' text is the challenge theorem itself; shared cells are hoisted lemmas.
- Tree = dict of cells + order; `bid` for branches; `goals` = open goals of all cells,
  each Goal carrying (cell, line-in-cell, indent, text).
- Check unit = header(challenge minus graded bodies, answers filled) + techniques +
  stubs (`:= by sorry`) of every cell this one links to + candidate text. Messages are
  mapped back to cell-local lines by the header length.
- Split: after an accepted check, `extract_goal` at each new placeholder; a statement
  that re-elaborates on its own becomes a child cell and its placeholder in the parent is
  frozen as a link (`apply vm_cell_k <;> assumption`, fallback `exact vm_cell_k _ ‹_› …`).
  A statement that does not re-elaborate (measured: set/finset literals lose `: Set _`)
  stays inline in the parent — today's behaviour.
- Model view = tree rendered as one file, children inlined at their placeholders (the
  view the models already see). Edits land in the goal's cell.
- Delivery = children before parents, one lemma per cell, links kept; inline goals stay
  inside their parent's body. Comparator: each declaration has its own budget.
- Withdraw = drop a subtree; shed = drop unreferenced shared cells; fork/OR branches (G)
  later = several attempts on one cell.

## Measured in the image (2026-09-04)
`extract_goal` without `*` drops hypotheses unrelated to the goal's variables (`h_mem : 6 < 7`
went missing and every step using it failed); the probe uses `extract_goal *`.

extract_goal statements re-elaborate for: intro (renames `a✝` → `a`), rintro ⟨m, hm⟩,
rcases alternatives, constructor (mp/mpr), induction (ih), Finset sums, ℝ with ↑ casts,
Set-builder `{n | …}`, IsLeast. Not: `(a, b) ∈ ({…} : Set (ℤ × ℤ))` (ascription lost →
`Insert (ℤ × ℤ) ?m` stuck); pp.analyze does not help. `apply c <;> assumption` and
`exact c _ ‹_›` both connect parent to child.

## Acceptance
rmo_2001_2 ≥ 4/5 on win, p10 < 200 s, reg 12/12, judge PASSED, all existing tests.
