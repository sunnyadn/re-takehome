"""Proof techniques as Lean tactics: defined once in the solution file's
preamble, callable by either model, checked in the harness image. Each entry
is the Lean source and the one line the models see."""
from __future__ import annotations

# Measured on putnam_2018_a1 (d ∣ 2² · 1009²) and rmo_2001_2 (d ∣ 5 · p · q, p q
# prime): both boards reached the divisor enumeration and neither model finished it.
DIVISOR_CASES = ("""-- `divisor_cases h` (h : d ∣ N over ℕ or ℤ) puts one goal per divisor of N, d
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

end DivisorCases""",
                 "`divisor_cases h` (h : d ∣ N, over ℕ or ℤ, N a numeral or a product of numerals and "
                 "prime variables with Nat.Prime in context, such as 2018 ^ 2 or 5 * p * q): one goal per "
                 "divisor with d replaced by it (over ℤ, `hx : d = m` or `hx : d = -m` in each case). "
                 "For `h : a * b = N` first `have hd : a ∣ N := Dvd.intro _ h`. Never `decide` a divisor set.")

TECHNIQUES: tuple[tuple[str, str], ...] = (DIVISOR_CASES,)

PREAMBLE_MARK = "-- techniques defined for this file"
PREAMBLE_END = "-- end of techniques"


def preamble() -> str:
    """The Lean block that goes after the imports of every solution file."""
    return PREAMBLE_MARK + "\n\n" + "\n\n".join(src for src, _ in TECHNIQUES) + "\n" + PREAMBLE_END + "\n"


def technique_card() -> str:
    """What the models are told about the tactics this file defines."""
    return "Tactics defined in this file, usable anywhere in it:\n" + "\n".join(
        f"- {note}" for _, note in TECHNIQUES)
