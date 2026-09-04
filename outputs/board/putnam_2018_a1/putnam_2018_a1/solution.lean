import Mathlib

-- techniques defined for this file

-- `divisor_cases h` (h : d ∣ N over ℕ or ℤ) puts one goal per divisor of N, d
-- replaced by it (over ℤ: hx : d = ±m per case). N's factorisation is read off
-- its type: numerals are factored here, variables are prime atoms (Nat.Prime in
-- context). `divisor_cases h : N = e` / `divisor_cases h for x : N = e` spell it.
syntax "divisor_split" ident " : " term : tactic
set_option linter.unusedVariables false in
macro_rules
  | `(tactic| divisor_split $h : $a * $b) => `(tactic| (
      obtain ⟨d₁, d₂, h₁, h₂, hd⟩ := Nat.dvd_mul.mp $h
      first | subst hd | rw [← hd] at *
      (divisor_split h₂ : $b) <;> (divisor_split h₁ : $a)))
  | `(tactic| divisor_split $h : $a ^ $k) => `(tactic| (
      rw [Nat.dvd_prime_pow (by norm_num)] at $h:ident
      obtain ⟨i, hi, hd⟩ := $h
      subst hd
      interval_cases i))
  | `(tactic| divisor_split $h : $a) => `(tactic| (
      have hp : Nat.Prime $a := by first | assumption | norm_num
      rcases (Nat.dvd_prime hp).mp $h with hd | hd <;> subst hd))

syntax "divisor_cases" ident : tactic
syntax "divisor_cases" ident " : " term : tactic
syntax "divisor_cases" ident " for " term " : " term : tactic
macro_rules
  | `(tactic| divisor_cases $h : $l = $r) => `(tactic| first
      | (rw [show $l = $r by norm_num] at $h:ident; divisor_split $h : $r)
      | divisor_cases $h)
  | `(tactic| divisor_cases $h : $e) => `(tactic| first | divisor_split $h : $e | divisor_cases $h)
  | `(tactic| divisor_cases $h for $x : $l = $r) => `(tactic| (
      have hn : ($x).natAbs ∣ $r := by
        have hh := Int.natAbs_dvd_natAbs.mpr $h
        rw [show (($l : ℤ)).natAbs = $r by norm_num] at hh
        exact hh
      have hx := Int.natAbs_eq $x
      generalize hm : ($x).natAbs = m at hn hx
      (divisor_split hn : $r) <;> (rcases hx with hx | hx) <;> norm_num at hx))

-- `divisor_cases h` alone: the factorisation is read off h's type (numerals
-- factored here, variables kept as prime atoms) and ℤ is routed through natAbs.
section DivisorCases
open Lean Elab Tactic Meta

partial def numValue (e : Expr) : Option Nat :=
  if let some n := e.nat? then some n
  else if e.isAppOfArity ``HMul.hMul 6 then do
    let a ← numValue (e.getArg! 4); let b ← numValue (e.getArg! 5); some (a * b)
  else if e.isAppOfArity ``HPow.hPow 6 then do
    let a ← numValue (e.getArg! 4); let k ← numValue (e.getArg! 5); some (a ^ k)
  else if e.isAppOfArity ``Nat.cast 3 || e.isAppOfArity ``Int.ofNat 1 then numValue e.appArg!
  else none

partial def factorSyntax (e : Expr) : MetaM (TSyntax `term) := do
  let e ← instantiateMVars e
  if let some n := numValue e then
    let rec fac (n p : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
      if n ≤ 1 then acc.reverse
      else if p * p > n then ((n, 1) :: acc).reverse
      else if n % p == 0 then
        let rec cnt (n k : Nat) : Nat × Nat := if n % p == 0 then cnt (n / p) (k + 1) else (n, k)
        let (m, k) := cnt n 0
        fac m (p + 1) ((p, k) :: acc)
      else fac n (p + 1) acc
    let ps := fac n 2 []
    let parts ← ps.mapM fun (p, k) => do
      let pl := Syntax.mkNumLit (toString p)
      if k == 1 then pure (pl : TSyntax `term)
      else `($pl ^ $(Syntax.mkNumLit (toString k)))
    match parts with
    | [] => `(1)
    | p :: rest => rest.foldlM (fun acc q => `($acc * $q)) p
  else if e.isAppOfArity ``HMul.hMul 6 then
    let a ← factorSyntax (e.getArg! 4); let b ← factorSyntax (e.getArg! 5)
    `($a * $b)
  else if e.isAppOfArity ``HPow.hPow 6 then
    let a ← factorSyntax (e.getArg! 4)
    if let some k := (e.getArg! 5).nat? then `($a ^ $(Syntax.mkNumLit (toString k)))
    else throwError "divisor_cases: exponent is not a numeral"
  else if e.isFVar then
    pure (mkIdent (← e.fvarId!.getUserName))
  else if e.isAppOfArity ``Nat.cast 3 || e.isAppOfArity ``Int.ofNat 1 then
    factorSyntax e.appArg!
  else throwError "divisor_cases: cannot read a prime factorisation off {e}"

elab_rules : tactic
  | `(tactic| divisor_cases $h:ident) => withMainContext do
  let decl ← getLocalDeclFromUserName h.getId
  let ty ← whnfR (← instantiateMVars decl.type)
  unless ty.isAppOfArity ``Dvd.dvd 4 do throwError "divisor_cases: {h} is not a divisibility"
  let α := ty.getArg! 0
  let x := ty.getArg! 2
  let n := ty.getArg! 3
  let r ← factorSyntax n
  let l ← Lean.PrettyPrinter.delab n
  if α.isConstOf ``Int then
    let xs ← Lean.PrettyPrinter.delab x
    evalTactic (← `(tactic| divisor_cases $h for $xs : $l = $r))
  else
    -- A divisor that is not a variable (`m - p - q`) is named first, so that
    -- each case keeps `hcase : m - p - q = <divisor>` (measured: `rw [← hd] at *`
    -- rewrote hd into a triviality and left every other hypothesis untouched).
    unless x.isFVar do
      let xs ← Lean.PrettyPrinter.delab x
      let dc := mkIdent (Name.mkSimple "dcase")
      let hc := mkIdent (Name.mkSimple "hcase")
      evalTactic (← `(tactic| generalize $hc : $xs = $dc at $h:ident))
    evalTactic (← `(tactic| first | divisor_split $h : $r | divisor_cases $h : $l = $r))

end DivisorCases

-- `prime_facts`: `2 ≤ p` for every `Nat.Prime p` in the context, however the hypothesis is named.
-- `solve_sub`: a hypothesis `m - t₁ - ... = D` over ℕ (either way round, however named): `m` is
-- replaced by `t₁ + ... + d` and `d = D` substituted, so the truncated subtraction is gone.
section LeafMeta
open Lean Elab Tactic Meta

elab "prime_facts" : tactic => withMainContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ty.isAppOfArity ``Nat.Prime 1 then
      let val ← mkAppM ``Nat.Prime.two_le #[decl.toExpr]
      let goal ← getMainGoal
      let g ← goal.assert (Name.mkSimple s!"hge_{decl.userName.eraseMacroScopes}") (← inferType val) val
      let (_, g) ← g.intro1P
      replaceMainGoal [g]

elab "solve_sub" : tactic => withMainContext do
  let some (m, terms, d) ← (do
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 0).isConstOf ``Nat then
          for (side, other) in [(ty.getArg! 1, ty.getArg! 2), (ty.getArg! 2, ty.getArg! 1)] do
            let mut lhs := side
            let mut ts : Array Expr := #[]
            while lhs.isAppOfArity ``HSub.hSub 6 do
              ts := ts.push (lhs.getArg! 5)
              lhs := lhs.getArg! 4
            if lhs.isFVar && !ts.isEmpty then
              return some (lhs, ts.reverse, other)
      return none)
    | throwError "solve_sub: no hypothesis `m - ... = D`"
  let ms ← PrettyPrinter.delab m
  let ds ← PrettyPrinter.delab d
  let tss ← terms.mapM fun e => (liftMetaM (PrettyPrinter.delab e) : TacticM Term)
  let rest := tss.extract 1 tss.size
  let sum ← rest.foldlM (fun acc t => `($acc + $t)) tss[0]!
  let sub ← tss.foldlM (fun acc t => `($acc - $t)) ms
  let sumd ← `($sum + d_sub)
  let subd ← tss.foldlM (fun acc t => `($acc - $t)) sumd
  evalTactic (← `(tactic| (
    have hpos_sub : 0 < $sub := by first | omega | positivity | nlinarith
    obtain ⟨d_sub, hd_sub⟩ : ∃ d, $ms = $sum + d := ⟨$sub, by omega⟩
    subst hd_sub
    have hcancel : $subd = d_sub := by omega
    simp only [hcancel] at *
    have hd_val : d_sub = $ds := by omega
    subst hd_val)))
end LeafMeta

-- `pow_squeeze y n E` (a hypothesis y ^ n = ...): E ^ n < y ^ n < (E + 1) ^ n (or ≤ below) by
-- omega/nlinarith, then Nat.pow_le/lt_pow_iff_left and omega, which also closes False when
-- the squeeze is strict; `with h` first replaces the variable of `h : c ≤ x` by c + k inside
-- those proofs.
syntax "pow_squeeze" term:max term:max term:max (" with " ident)? : tactic
macro_rules
  | `(tactic| pow_squeeze $y $n $lo) => `(tactic| (
      have hn : ($n : ℕ) ≠ 0 := by norm_num
      have hhi : $y ^ $n < ($lo + 1) ^ $n := by
        first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)
      have h2 := (Nat.pow_lt_pow_iff_left hn).1 hhi
      first
        | (have hlo : ($lo : ℕ) ^ $n < $y ^ $n := by
             first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)
           have h1 := (Nat.pow_lt_pow_iff_left hn).1 hlo
           omega)
        | (have hlo : ($lo : ℕ) ^ $n ≤ $y ^ $n := by
             first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)
           have h1 := (Nat.pow_le_pow_iff_left hn).1 hlo
           omega)))
  | `(tactic| pow_squeeze $y $n $lo with $h) => `(tactic| (
      have hn : ($n : ℕ) ≠ 0 := by norm_num
      have hhi : $y ^ $n < ($lo + 1) ^ $n := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le $h
        subst hk
        first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)
      have h2 := (Nat.pow_lt_pow_iff_left hn).1 hhi
      first
        | (have hlo : ($lo : ℕ) ^ $n < $y ^ $n := by
             obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le $h
             subst hk
             first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)
           have h1 := (Nat.pow_lt_pow_iff_left hn).1 hlo
           omega)
        | (have hlo : ($lo : ℕ) ^ $n ≤ $y ^ $n := by
             obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le $h
             subst hk
             first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)
           have h1 := (Nat.pow_le_pow_iff_left hn).1 hlo
           omega)))

-- `nat_sub_exact`: every `a - b : ℕ` in a hypothesis gets `b ≤ a` when omega or nlinarith
-- proves it, and the hypotheses are cast to ℤ with those facts, so the subtraction is exact.
section NatSubExact
open Lean Elab Tactic Meta

partial def natSubs (e : Expr) (acc : Array (Expr × Expr)) : Array (Expr × Expr) :=
  let acc := if e.isAppOfArity ``HSub.hSub 6 && (e.getArg! 0).isConstOf ``Nat then
    acc.push (e.getArg! 4, e.getArg! 5) else acc
  match e with
  | .app f a => natSubs a (natSubs f acc)
  | .lam _ _ b _ | .forallE _ _ b _ => natSubs b acc
  | .mdata _ b => natSubs b acc
  | _ => acc

elab "nat_sub_exact" : tactic => withMainContext do
  let mut pairs : Array (Expr × Expr) := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    pairs := natSubs (← instantiateMVars decl.type) pairs
  pairs := natSubs (← instantiateMVars (← getMainTarget)) pairs
  let mut names : Array Ident := #[]
  let mut i := 0
  for (a, b) in pairs do
    let sa ← PrettyPrinter.delab a
    let sb ← PrettyPrinter.delab b
    let nm := mkIdent (Name.mkSimple s!"hsub{i}")
    i := i + 1
    try
      evalTactic (← `(tactic| have $nm : $sb ≤ $sa := by first | omega | nlinarith))
      names := names.push nm
    catch _ => pure ()
  if names.isEmpty then throwError "nat_sub_exact: no subtraction made exact"
  let args ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:ident)
  evalTactic (← `(tactic| zify [$args,*] at *))
end NatSubExact

-- `pow_bounds y n`: bounds on y ^ n in the context (on y ^ n itself, or on the right side of
-- a hypothesis `y ^ n = P`) become bounds on y, then omega.
syntax "pow_bounds" term:max term:max : tactic
macro_rules
  | `(tactic| pow_bounds $y $n) => `(tactic| (
      have hn : ($n : ℕ) ≠ 0 := by norm_num
      try have hb₁ := (Nat.pow_le_pow_iff_left hn).1 ‹(_ : ℕ) ^ $n ≤ $y ^ $n›
      try have hb₂ := (Nat.pow_le_pow_iff_left hn).1 ‹$y ^ $n ≤ (_ : ℕ) ^ $n›
      try have hb₃ := (Nat.pow_lt_pow_iff_left hn).1 ‹(_ : ℕ) ^ $n < $y ^ $n›
      try have hb₄ := (Nat.pow_lt_pow_iff_left hn).1 ‹$y ^ $n < (_ : ℕ) ^ $n›
      try have hc₁ := (Nat.pow_le_pow_iff_left hn).1 (le_of_le_of_eq ‹(_ : ℕ) ^ $n ≤ _› ‹$y ^ $n = _›.symm)
      try have hc₂ := (Nat.pow_le_pow_iff_left hn).1 (le_of_eq_of_le ‹$y ^ $n = _› ‹_ ≤ (_ : ℕ) ^ $n›)
      try have hc₃ := (Nat.pow_lt_pow_iff_left hn).1 (lt_of_lt_of_eq ‹(_ : ℕ) ^ $n < _› ‹$y ^ $n = _›.symm)
      try have hc₄ := (Nat.pow_lt_pow_iff_left hn).1 (lt_of_eq_of_lt ‹$y ^ $n = _› ‹_ < (_ : ℕ) ^ $n›)
      omega))

-- `bounded_cases x N`: x ≤ N (omega, nlinarith, or from x ^ 2 / x ^ 3 = numeral), then every value.
syntax "bounded_cases" ident term:max : tactic
macro_rules
  | `(tactic| bounded_cases $x $n) => `(tactic| (
      have hb : $x ≤ $n := by first
        | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)
        | (apply Nat.lt_succ_iff.mp; apply (Nat.pow_lt_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1
           first | omega | (norm_num at *; omega) | (norm_num at *; done))
        | (apply Nat.lt_succ_iff.mp; apply (Nat.pow_lt_pow_iff_left (by norm_num : (3 : ℕ) ≠ 0)).1
           first | omega | (norm_num at *; omega) | (norm_num at *; done))
      interval_cases $x <;> first | omega | (norm_num at *; done) | nlinarith | simp_all))
-- end of techniques


theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ ({(673, 1358114), (674, 340033), (1009, 2018),
      (2018, 1009), (340033, 674), (1358114, 673)} : Set (ℤ × ℤ))) := by
  constructor
  case mp =>
    intro h_eq
    have h_denom_ne_zero : (a : ℚ) ≠ 0 ∧ (b : ℚ) ≠ 0 := by
      simp; omega
    have h_clear_denom : 3 * a * b = 2018 * (a + b) := by
      field_simp [h_denom_ne_zero.1, h_denom_ne_zero.2] at h_eq
      norm_cast at h_eq
      ring_nf at h_eq ⊢
      omega
    have h_factored : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := by
      linarith
    have h_X_pos : 3 * a - 2018 > 0 := by
      nlinarith
    have h_Y_pos : 3 * b - 2018 > 0 := by
      nlinarith
    have h_divisors : 3 * a - 2018 ∣ 2018 ^ 2 := by
      have h_mul : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := h_factored
      have h_left_dvd : (3 * a - 2018) ∣ (3 * a - 2018) * (3 * b - 2018) := dvd_mul_right _ _
      rw [h_mul] at h_left_dvd
      exact h_left_dvd
    have h_a_in_set : (a, b) ∈ ({(673, 1358114), (674, 340033), (1009, 2018), (2018, 1009), (340033, 674), (1358114, 673)} : Set (ℤ × ℤ)) := by
      set_option maxHeartbeats 60000 in (divisor_cases h_divisors <;> (first | (solve_sub; first | (simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton] at *; first | omega | (simp_all <;> omega)) | omega | (norm_num at *; done) | nlinarith | (simp_all; done) | (norm_num [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton] at *; done) | (norm_num [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton] at *; omega)) | (first | (simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton] at *; first | omega | (simp_all <;> omega)) | omega | (norm_num at *; done) | nlinarith | (simp_all; done) | (norm_num [Finset.mem_insert] at *; done) | (norm_num [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton] at *; omega))))


    exact h_a_in_set
  case mpr =>
    rintro h_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h_mem
    rcases h_mem with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
