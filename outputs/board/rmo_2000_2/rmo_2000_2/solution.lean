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
    evalTactic (← `(tactic| first | divisor_split $h : $r | divisor_cases $h : $l = $r))

end DivisorCases

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


theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h5 : (x + 2) ^ 3 ≤ y ^ 3 := by
    rcases Nat.lt_or_ge x 10 with hlt | hge
    · interval_cases x <;> first | omega | (bounded_cases y 13)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hge
      subst hk
      first | omega | nlinarith | (ring_nf at *; omega) | (ring_nf at *; nlinarith)
  have h6 : y ^ 3 < (x + 3) ^ 3 := by
    ring_nf; omega
  have h7 : x ≥ 3 → y = x + 2 := by
    intro hge
    set_option maxHeartbeats 60000 in
    pow_bounds y 3
  have h8 : x = 1 ∨ x = 2 ∨ x ≥ 3 := by
    omega
  have h9 : x ≠ 1 := by
    aesop
  have h10 : x ≠ 2 := by
    aesop
  have h11 : x = 9 := by
    have h13 : y = x + 2 := by
      have h14 : x ≥ 3 := by
        omega
      exact h7 h14
    rw [h13] at h5
    ring_nf at h5
    have h_eq : (x + 2) ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      simpa [h13] using h
    set_option maxHeartbeats 60000 in
    nat_sub_exact
    first | omega | (norm_num at *; done) | nlinarith | (simp_all; done) | (simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton] at *; omega)
  have h12 : y = 11 := by
    omega
  exact ⟨h11, h12⟩

