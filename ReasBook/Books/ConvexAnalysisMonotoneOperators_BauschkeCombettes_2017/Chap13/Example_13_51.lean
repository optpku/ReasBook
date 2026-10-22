/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_50

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ERealFunction

universe u

namespace ERealFunction

section FenchelMoreau

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

private theorem absPowerDivided_zero (p : ℝ) (hp : 1 < p) :
    |(0 : ℝ)| ^ p / p = 0 := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  simp [Real.zero_rpow hp_pos.ne']

private theorem absPowerDivided_nonneg (p : ℝ) (hp : 1 < p) (t : ℝ) :
    0 ≤ |t| ^ p / p := by
  exact div_nonneg (Real.rpow_nonneg (abs_nonneg t) p) (le_of_lt (lt_trans zero_lt_one hp))

private theorem toEReal_absPowerDivided_zero (p : ℝ) (hp : 1 < p) :
    (((fun t : ℝ ↦ |t| ^ p / p).toEReal) 0 : EReal) = 0 := by
  have hzero : (((|(0 : ℝ)| ^ p / p : ℝ)) : EReal) = 0 := by
    exact_mod_cast absPowerDivided_zero p hp
  simpa [Function.toEReal_apply] using hzero

private theorem toEReal_absPowerDivided_nonneg (p : ℝ) (hp : 1 < p) (t : ℝ) :
    (((fun s : ℝ ↦ |s| ^ p / p).toEReal) 0 : EReal) ≤
      (((fun s : ℝ ↦ |s| ^ p / p).toEReal) t : EReal) := by
  have hnonneg : (0 : EReal) ≤ (((|t| ^ p / p : ℝ)) : EReal) := by
    exact_mod_cast absPowerDivided_nonneg p hp t
  have hzero : (0 : ℝ) ^ p / p = 0 := by
    simpa using absPowerDivided_zero p hp
  simpa [Function.toEReal_apply, hzero] using hnonneg

-- Proof sketch: start from Example 9.36, which places `t ↦ |t|^p` in `Γ₀(ℝ)` for `p > 1`, then
-- apply the positive scalar-multiplication stability of `Γ₀(ℝ)` to divide by the positive number
-- `p`.
/-- The scalar integrand `t ↦ |t|^p / p` belongs to `Γ₀(ℝ)` for every exponent `p > 1`. -/
theorem absPowerDivided_mem_gammaZero
    (p : ℝ) (hp : 1 < p) :
    (fun t : ℝ ↦ |t| ^ p / p).toEReal ∈ Γ₀(ℝ) := sorry

-- Proof sketch: apply Proposition 9.40(ii) to the scalar `Γ₀(ℝ)` integrand
-- `t ↦ |t|^p / p`, using that it vanishes at `0` and is everywhere nonnegative.
/-- On any measure space, the integral functional
`X ↦ ∫ ω, |X ω|^p / p ∂P` belongs to `Γ₀(L²((Ω,\mathcal F,P);\mathbb R))` for `p > 1`. -/
theorem integralFunctional_absPowerDivided_mem_gammaZero
    (p : ℝ) (hp : 1 < p) :
    integralFunctional P ((fun t : ℝ ↦ |t| ^ p / p).toEReal) ∈ Γ₀(Ω →₂[P] ℝ) := by
  simpa using
    integralFunctional_mem_gammaZero P ((fun t : ℝ ↦ |t| ^ p / p).toEReal)
      (absPowerDivided_mem_gammaZero p hp)
      (Or.inr ⟨toEReal_absPowerDivided_zero p hp, toEReal_absPowerDivided_nonneg p hp⟩)

variable [P.IsComplete] [SigmaFinite P]

-- Proof sketch: rewrite the canonical packaged conjugate `gammaZeroConjugate` of the scalar
-- integrand via Example 13.2(i).
/-- The canonical `Γ₀(ℝ)`-valued conjugate of `t ↦ |t|^p / p` is the concrete conjugate-power
integrand `u ↦ |u|^(p*) / p*`. -/
@[simp] theorem gammaZeroConjugate_absPowerDivided
    (p : ℝ) (hp : 1 < p) :
    gammaZeroConjugate ((fun t : ℝ ↦ |t| ^ p / p).toEReal) (absPowerDivided_mem_gammaZero p hp) =
      (fun t : ℝ ↦ |t| ^ p.conjExponent / p.conjExponent).toEReal := by
  ext u
  simpa [gammaZeroConjugate_apply] using conjugate_absRpowDivided p hp u

-- Proof sketch: specialize Proposition 13.50(ii) to the scalar integrand
-- `t ↦ |t|^p / p`, then rewrite the canonical conjugate integrand `gammaZeroConjugate` via the
-- scalar bridge above.
/-- Example 13.51: on a complete sigma-finite measure space, if
`f(X) = ∫ ω, |X ω|^p / p ∂P` on `L²((Ω,\mathcal F,P);\mathbb R)` with `p ∈ ]1,+∞[`, then
`f* (X) = ∫ ω, |X ω|^{p*} / p* ∂P`, where `p* = p.conjExponent = p / (p - 1)`. -/
theorem
    fenchelConjugate_integralFunctional_absPowerDivided_eq_integralFunctional_conjExponent
    (p : ℝ) (hp : 1 < p) :
    ((integralFunctional P ((fun t : ℝ ↦ |t| ^ p / p).toEReal)).asEReal)∗ =
      (integralFunctional P
        ((fun t : ℝ ↦ |t| ^ p.conjExponent / p.conjExponent).toEReal)).asEReal := by
  simpa [gammaZeroConjugate_absPowerDivided p hp] using
    conjugate_integralFunctional_eq_integralFunctional_gammaZeroConjugate
      ((fun t : ℝ ↦ |t| ^ p / p).toEReal) (absPowerDivided_mem_gammaZero p hp)
      (Or.inr ⟨toEReal_absPowerDivided_zero p hp, toEReal_absPowerDivided_nonneg p hp⟩)

end FenchelMoreau

end ERealFunction
