/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ERealFunction
open scoped InnerProductSpace
open Real

namespace ERealFunction

noncomputable section

-- Proof sketch: rewrite the real inner product as multiplication and convert the indexed supremum
-- from `conjugate_apply` into `sSup` over the range.
/-- On `ℝ`, evaluating `conjugate f` at `u` gives the scalar supremum formula
`sup_x (ux - f(x))`. -/
@[simp] theorem conjugate_apply_real (f : ℝ → EReal) (u : ℝ) :
    f∗ u = sSup (Set.range fun x : ℝ ↦ ((u * x : ℝ) : EReal) - f x) := sorry

/-- The function `x ↦ 1 / x` on `(0,+∞)` and `+∞` on `(-∞,0]`. -/
noncomputable def reciprocalBarrier : ℝ → EReal :=
  fun x ↦ if 0 < x then ((1 / x : ℝ) : EReal) else ⊤

/-- The negative Burg entropy `x ↦ -log x` on `(0,+∞)` and `+∞` on `(-∞,0]`. -/
noncomputable def negativeBurgEntropy : ℝ → EReal :=
  fun x ↦ if 0 < x then ((-Real.log x : ℝ) : EReal) else ⊤

/-- The negative Fermi--Dirac entropy on `ℝ`, finite on `[0,1]` and `+∞` outside. -/
noncomputable def negativeFermiDiracEntropy : ℝ → EReal :=
  fun x ↦
    if 0 < x ∧ x < 1 then
      ((x * Real.log x + (1 - x) * Real.log (1 - x) : ℝ) : EReal)
    else if x = 0 ∨ x = 1 then
      0
    else
      ⊤

/-- The Bose--Einstein entropy on `ℝ`, finite on `[0,+∞)` and `+∞` on `(-∞,0)`. -/
noncomputable def boseEinsteinEntropy : ℝ → EReal :=
  fun x ↦
    if 0 < x then
      ((x * Real.log x - (x + 1) * Real.log (x + 1) : ℝ) : EReal)
    else if x = 0 then
      0
    else
      ⊤

/-- The negative Boltzmann--Shannon entropy, appearing as the conjugate of `exp`. -/
noncomputable def negativeBoltzmannShannonEntropy : ℝ → EReal :=
  fun u ↦
    if 0 < u then
      ((u * Real.log u - u : ℝ) : EReal)
    else if u = 0 then
      0
    else
      ⊤

/-- The logistic loss function, written as an `EReal`-valued map on `ℝ`. -/
noncomputable def logisticLoss : ℝ → EReal :=
  (fun u : ℝ ↦ Real.log (1 + Real.exp (-u))).toEReal.asEReal

-- Proof sketch: optimize the scalar function `x ↦ ux - |x|^p / p`; the maximizer satisfies the
-- usual Hölder-conjugate relation, yielding the closed form with exponent
-- `Real.conjExponent p`.
/-- Example 13.2 (1): clause (i). For `p ∈ ]1,+∞[`, the conjugate of `x ↦ |x|^p / p` is
`u ↦ |u|^{p*} / p*`, where `p* = Real.conjExponent p = p / (p - 1)`. -/
theorem conjugate_absRpowDivided
    (p : ℝ) (hp : 1 < p) (u : ℝ) :
    ((fun x : ℝ ↦ (|x| ^ p) / p).toEReal.asEReal)∗ u =
      ((fun x : ℝ ↦ (|x| ^ Real.conjExponent p) / Real.conjExponent p).toEReal.asEReal) u := sorry

-- Proof sketch: maximize `ux - 1 / x` over `x > 0`; the optimizer is `x = 1 / √(-u)` when
-- `u ≤ 0`, and for `u > 0` the supremum is `+∞`.
/-- Example 13.2 (2): clause (ii). The conjugate of `x ↦ 1/x` on `(0,+∞)` is
`u ↦ -2√(-u)` on `(-∞,0]` and `+∞` on `(0,+∞)`. -/
theorem conjugate_reciprocalBarrier (u : ℝ) :
    reciprocalBarrier∗ u =
      if u ≤ 0 then ((-2 * Real.sqrt (-u) : ℝ) : EReal) else ⊤ := sorry

-- Proof sketch: maximize `ux + log x` over `x > 0`; the critical point occurs at `x = -1 / u`
-- for `u < 0`, while `u ≥ 0` forces the supremum to be `+∞`.
/-- Example 13.2 (3): clause (iii). The conjugate of the negative Burg entropy is
`u ↦ -log(-u) - 1` on `(-∞,0)` and `+∞` on `[0,+∞)`. -/
theorem conjugate_negativeBurgEntropy (u : ℝ) :
    negativeBurgEntropy∗ u =
      if u < 0 then ((-Real.log (-u) - 1 : ℝ) : EReal) else ⊤ := sorry

-- Proof sketch: solve the optimality equation for `ux - cosh x` using the inverse hyperbolic
-- sine, then substitute the maximizer back into the objective.
/-- Example 13.2 (4): clause (iv). The conjugate of `cosh` is
`u ↦ u arsinh(u) - √(u^2 + 1)`. -/
theorem conjugate_cosh (u : ℝ) :
    (cosh.toEReal.asEReal)∗ u =
      ((u * Real.arsinh u - Real.sqrt (u ^ 2 + 1) : ℝ) : EReal) := sorry

-- Proof sketch: maximize `ux - e^x`; for `u > 0` the optimizer is `x = log u`, while `u = 0`
-- gives value `0` in the extended-real convention and `u < 0` yields `+∞`.
/-- Example 13.2 (5): clause (v). The conjugate of `exp` is the negative
Boltzmann--Shannon entropy. -/
theorem conjugate_exp (u : ℝ) :
    (exp.toEReal.asEReal)∗ u = negativeBoltzmannShannonEntropy u := sorry

-- Proof sketch: optimize `ux - f(x)` on `[0,1]`; the stationarity equation produces the logistic
-- parametrization and the resulting supremum equals `log(1 + e^u)`.
/-- Example 13.2 (6): clause (vi), first part. The conjugate of the negative Fermi--Dirac entropy
is `u ↦ log(1 + e^u)`. -/
theorem conjugate_negativeFermiDiracEntropy (u : ℝ) :
    negativeFermiDiracEntropy∗ u = (Real.log (1 + Real.exp u) : EReal) := sorry

-- Proof sketch: reflect the explicit formula from the previous clause by sending `u` to `-u`;
-- the resulting expression is exactly the logistic loss.
/-- Example 13.2 (7): clause (vi), second part. The reflected conjugate `f^{*∨}` of the negative
Fermi--Dirac entropy is the logistic loss. -/
theorem conjugate_negativeFermiDiracEntropy_reflection :
    (negativeFermiDiracEntropy∗)ᵛ = logisticLoss := sorry

-- Proof sketch: maximize `ux - [x log x - (x + 1) log (x + 1)]` on `[0,+∞)`; the optimizer
-- satisfies `e^u = x / (x + 1)`, which is possible exactly for `u < 0`.
/-- Example 13.2 (8): clause (vii). The conjugate of the Bose--Einstein entropy is
`u ↦ -log(1 - e^u)` on `(-∞,0)` and `+∞` on `[0,+∞)`. -/
theorem conjugate_boseEinsteinEntropy (u : ℝ) :
    boseEinsteinEntropy∗ u =
      if u < 0 then ((-Real.log (1 - Real.exp u) : ℝ) : EReal) else ⊤ := sorry

-- Proof sketch: maximize `ux - √(1 + x^2)`; the optimizer exists exactly for `|u| ≤ 1`, and
-- substituting it gives `-√(1 - u^2)`, while `|u| > 1` leads to `+∞`.
/-- Example 13.2 (9): clause (viii). The conjugate of `x ↦ √(1 + x^2)` is
`u ↦ -√(1 - u^2)` on `[-1,1]` and `+∞` outside that interval. -/
theorem conjugate_sqrtOneAddSq (u : ℝ) :
    ((fun x : ℝ ↦ Real.sqrt (1 + x ^ 2)).toEReal.asEReal)∗ u =
      if |u| ≤ 1 then ((-Real.sqrt (1 - u ^ 2) : ℝ) : EReal) else ⊤ := sorry

end

end ERealFunction
