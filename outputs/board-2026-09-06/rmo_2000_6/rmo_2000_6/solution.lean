import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib

attribute [instance 2000] instPowNat

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
-- Unhygienic so that each case's `hx : d = ±m` and `hm` can be named by what
-- follows (measured: hygienic `hx✝` left h_factor unrewritten in every case).
set_option hygiene false in
macro_rules
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

-- `pow_cycle a m k n` (numerals a m k with a ^ k % m = 1): a ^ n % m cycles with period k;
-- every case of n % k is finished by norm_num and omega (a ^ n generalised to an atom).
syntax "pow_cycle" num num num ident : tactic
macro_rules
  | `(tactic| pow_cycle $a $m $k $n) => `(tactic| (
      have hcyc : $a ^ $k % $m = 1 := by norm_num
      have hpow : $a ^ $n % $m = $a ^ ($n % $k) % $m := by
        conv_lhs => rw [← Nat.div_add_mod $n $k, pow_add, pow_mul]
        rw [Nat.mul_mod, Nat.pow_mod, hcyc, one_pow, ← Nat.mul_mod, one_mul]
      have hlt : $n % $k < $k := Nat.mod_lt _ (by norm_num)
      generalize hr : $n % $k = r at hpow hlt
      interval_cases r <;> norm_num at hpow <;> (try simp only [Nat.ModEq] at *) <;>
        first | omega | (generalize $a ^ $n = x at *; omega) | (generalize $a ^ $n = x at *; split_ifs at * <;> omega)))

-- `sum_induct k`: an identity between sums over `range (k + 1)` (or `Icc 0 k`) by induction
-- on k. The step is mechanical: every sum over `range (j + 1)` in sight is peeled at both
-- ends as facts, `2 ^ (k + 1 - x)` under a binder becomes `2 ^ (k - x) * 2` and the factor
-- leaves the sum, Pascal splits `choose (a + 1) (x + 1)`, the new sums are peeled once more,
-- and omega closes the linear system over the sums.
section SumInduct
open Lean Elab Tactic Meta

elab "sum_peel_facts" : tactic => withMainContext do
  let g ← getMainGoal
  let mut targets : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then
      targets := targets.push (← instantiateMVars d.type)
  let rec visit (e : Expr) (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
    let mut acc := acc
    if e.isAppOfArity ``Finset.sum 5 then
      let args := e.getAppArgs
      let s := args[3]!
      let f := args[4]!
      if s.isAppOfArity ``Finset.range 1 then
        let n := s.appArg!
        if n.isAppOfArity ``HAdd.hAdd 6 then
          let k := n.getAppArgs[4]!
          let one := n.getAppArgs[5]!
          if one.nat? == some 1 || one.rawNatLit? == some 1 then
            if !(acc.any fun p => p.1 == f && p.2 == k) then
              acc := acc.push (f, k)
    match e with
    | .app a b => acc ← visit a acc; acc ← visit b acc
    | .lam _ t b _ => acc ← visit t acc; acc ← visit b acc
    | .forallE _ t b _ => acc ← visit t acc; acc ← visit b acc
    | .letE _ t v b _ => acc ← visit t acc; acc ← visit v acc; acc ← visit b acc
    | .mdata _ b => acc ← visit b acc
    | .proj _ _ b => acc ← visit b acc
    | _ => pure ()
    return acc
  let mut found : Array (Expr × Expr) := #[]
  for t in targets do
    found ← visit t found
  let mut hyps : Array Hypothesis := #[]
  for (f, k) in found do
    if f.hasLooseBVars || k.hasLooseBVars then continue
    try
      let v1 ← mkAppM ``Finset.sum_range_succ #[f, k]
      let v2 ← mkAppM ``Finset.sum_range_succ' #[f, k]
      hyps := hyps.push { userName := `peel, type := ← inferType v1, value := v1 }
      hyps := hyps.push { userName := `peel, type := ← inferType v2, value := v2 }
    catch _ => pure ()
  let (_, g') ← g.assertHypotheses hyps
  replaceMainGoal [g']
end SumInduct

syntax "sum_induct" ident : tactic
macro_rules
  | `(tactic| sum_induct $k) => `(tactic| (
      (try simp only [← Nat.range_succ_eq_Icc_zero] at *)
      induction $k:ident with
      | zero => first | simp | (simp; omega) | decide | norm_num
      | succ k ih =>
        sum_peel_facts
        (try simp (disch := simp only [Finset.mem_range] at *; omega) only [Nat.succ_sub, pow_succ] at *)
        (try simp only [mul_right_comm, ← Finset.sum_mul] at *)
        (try simp only [← Nat.add_assoc, Nat.succ_eq_add_one, Nat.sub_self, Nat.add_sub_cancel_left,
                        Nat.add_sub_cancel, pow_zero, pow_one, one_mul, mul_one, Nat.choose_zero_right] at *)
        (try simp only [Nat.choose_succ_succ, Finset.sum_add_distrib] at *)
        (try simp only [Nat.succ_eq_add_one, ← Nat.add_assoc] at *)
        sum_peel_facts
        (try simp only [Nat.choose_succ_succ, Finset.sum_add_distrib, Nat.succ_eq_add_one, ← Nat.add_assoc] at *)
        first | omega | linarith | (ring_nf at *; omega)))

-- `ico_blocks m`: a sum over `Ico a (g (m + 1))` equals the sum over j < m + 1 of the
-- block sums over `Ico (g j) (g (j + 1))`, for g monotone with a ≤ g 1 (omega/nlinarith side
-- goals): induction on m, the last block peeled off and joined by `sum_Ico_consecutive`.
syntax "ico_blocks" ident : tactic
macro_rules
  | `(tactic| ico_blocks $m) => `(tactic| (
      induction $m:ident with
      | zero => simp
      | succ k ih =>
        first
          | (rw [Finset.sum_Ico_succ_top (by omega), ← ih]
             rw [Finset.sum_Ico_consecutive _ (by nlinarith) (by nlinarith)])
          | (rw [Finset.sum_Ico_succ_top (by omega), ← ih]
             rw [Finset.sum_Ico_consecutive _ (by omega) (by omega)])
          | (symm; rw [Finset.sum_Ico_succ_top (by omega), ih]
             rw [Finset.sum_Ico_consecutive _ (by nlinarith) (by nlinarith)])))

-- `prime_to_bases p h`: from `h : m ∣ E` (m a numeral p divides, E a product of powers
-- of at most two atoms) prove `p ∣ <the atoms' product>` or `p ∣ <the atom>`: Euclid's lemma
-- down the product, `Nat.Prime.dvd_of_dvd_pow` at each base.
syntax "prime_to_bases " num ppSpace term : tactic
macro_rules
  | `(tactic| prime_to_bases $p $h) => `(tactic| (
      have vm_h : $p ∣ _ := Nat.dvd_trans (by norm_num) $h
      repeat' (rcases (Nat.Prime.dvd_mul (by norm_num)).1 vm_h with vm_h | vm_h)
      all_goals first
        | exact vm_h
        | exact Nat.Prime.dvd_of_dvd_pow (by norm_num) vm_h
        | exact Dvd.dvd.mul_right vm_h _
        | exact Dvd.dvd.mul_left vm_h _
        | exact Dvd.dvd.mul_right (Nat.Prime.dvd_of_dvd_pow (by norm_num) vm_h) _
        | exact Dvd.dvd.mul_left (Nat.Prime.dvd_of_dvd_pow (by norm_num) vm_h) _))

-- `vm_sum_div_block`: a sum of x i / i over `Ico a b`, x positive and antitone, is at most
-- the block's length times its first term (each term ≤ x a / a).
private theorem vm_sum_div_block (x : ℕ → ℝ) (hpos : ∀ n, 0 < x n) (hanti : Antitone x) (a b : ℕ) (ha : 0 < a) :
    ∑ i ∈ Finset.Ico a b, x i / (i : ℝ) ≤ ((b - a : ℕ) : ℝ) * (x a / (a : ℝ)) := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hstep : ∀ i ∈ Finset.Ico a b, x i / (i : ℝ) ≤ x a / (a : ℝ) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi' : (a : ℝ) ≤ i := by exact_mod_cast hi.1
    calc x i / (i : ℝ) ≤ x a / (i : ℝ) := div_le_div_of_nonneg_right (hanti hi.1) (by linarith)
      _ ≤ x a / (a : ℝ) := div_le_div_of_nonneg_left (hpos _).le hapos hi'
  calc ∑ i ∈ Finset.Ico a b, x i / (i : ℝ) ≤ ∑ i ∈ Finset.Ico a b, x a / (a : ℝ) := Finset.sum_le_sum hstep
    _ = ((b - a : ℕ) : ℝ) * (x a / (a : ℝ)) := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
-- end of techniques


theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b} 10) := by
  set_option maxHeartbeats 400000 in (refine And.intro (by refine ⟨(by try simp only [Set.mem_setOf_eq]; first | exact ⟨1, 10, by norm_num⟩ | exact ⟨2, 5, by norm_num⟩ | exact ⟨5, 2, by norm_num⟩ | exact ⟨10, 1, by norm_num⟩), (by intro vm_n vm_hn; obtain ⟨a, b, vm_c0, vm_c1, vm_c2, vm_c3⟩ := vm_hn; subst vm_c3; have hp2 : 2 ∣ a * b := (by prime_to_bases 2 vm_c2); have hp5 : 5 ∣ a * b := (by prime_to_bases 5 vm_c2); have hrad : 10 ∣ a * b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hp2 hp5; exact le_trans (by norm_num) (Nat.le_of_dvd (by positivity) hrad))⟩) (by refine ⟨(by try simp only [Set.mem_setOf_eq]; first | exact ⟨1, 10, by norm_num⟩ | exact ⟨2, 5, by norm_num⟩ | exact ⟨5, 2, by norm_num⟩ | exact ⟨10, 1, by norm_num⟩), (by intro vm_n vm_hn; obtain ⟨a, b, vm_c0, vm_c1, vm_c2, vm_c3⟩ := vm_hn; subst vm_c3; have hp2 : 2 ∣ a * b := (by prime_to_bases 2 vm_c2); have hp5 : 5 ∣ a * b := (by prime_to_bases 5 vm_c2); have hrad : 10 ∣ a * b := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hp2 hp5; exact le_trans (by norm_num) (Nat.le_of_dvd (by positivity) hrad))⟩))
