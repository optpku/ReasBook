/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_40
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal InnerProductSpace

universe u v

namespace ERealFunction

section FenchelMoreau

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]

/- Helper recall: clause (i) for the integral functional
`f = integralFunctional φ` is exactly Proposition 9.40. -/
recall integralFunctional_mem_gammaZero

variable (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H] in
private theorem gammaZeroConjugate_finite_or_nonneg
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))) :
    μ Set.univ < ∞ ∨
      ((gammaZeroConjugate φ hφ 0 : EReal) = 0 ∧
        ∀ z : H, (gammaZeroConjugate φ hφ 0 : EReal) ≤ (gammaZeroConjugate φ hφ z : EReal)) := by
  rcases hfinite_or_nonneg with hfinite | ⟨hzero, hmin⟩
  · exact Or.inl hfinite
  · have hmin' : ∀ z : H, φ.asEReal 0 ≤ φ.asEReal z := by
        simpa [Function.asEReal_apply] using hmin
    have hzero' : φ.asEReal 0 = 0 := by
      simpa [Function.asEReal_apply] using hzero
    refine Or.inr ⟨?_, ?_⟩
    · simpa [gammaZeroConjugate_apply] using
        conjugate_zero_eq_zero_of_minimum_at_zero φ.asEReal hmin' hzero'
    · intro z
      simpa [gammaZeroConjugate_apply] using
        conjugate_zero_le_conjugate_of_minimum_at_zero φ.asEReal hmin' hzero' z

-- Proof sketch: apply Proposition 9.40 to the conjugate integrand `gammaZeroConjugate φ hφ`. If
-- `μ` is finite, the finite-measure branch is immediate. Otherwise use Corollary 13.38 to get
-- `φ* ∈ Γ₀(H)` and show directly from the conjugate supremum formula that `(φ*)(0) = 0 ≤ φ*(z)`
-- for every `z`.
/-- Proposition 13.50 (1): clause (i) for
`g = integralFunctional (gammaZeroConjugate φ hφ)`. Under the same hypotheses, the integral
functional induced by the Fenchel conjugate `φ*` belongs to `Γ₀(L²((Ω,\mathcal F,\mu); H))`. -/
theorem integralFunctional_gammaZeroConjugate_mem_gammaZero
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))) :
    integralFunctional μ (gammaZeroConjugate φ hφ) ∈ Γ₀(Ω →₂[μ] H) := by
  simpa using
    integralFunctional_mem_gammaZero μ (gammaZeroConjugate φ hφ)
      (gammaZeroConjugate_mem_gammaZero hφ)
      (gammaZeroConjugate_finite_or_nonneg φ hφ hfinite_or_nonneg)

-- Proof sketch: apply the complete sigma-finite integral conjugation theorem to the canonical
-- `EReal`-valued coercion of `integralFunctional φ`, then identify the conjugate integrand as
-- `gammaZeroConjugate φ hφ`.
/-- Proposition 13.50 (2): if the measure is complete and sigma-finite, then the Fenchel conjugate
of the integral functional induced by `φ` is the integral functional induced by the Fenchel
conjugate integrand `φ*`. -/
theorem conjugate_integralFunctional_eq_integralFunctional_gammaZeroConjugate
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    [μ.IsComplete] [SigmaFinite μ] :
    ((integralFunctional μ φ).asEReal)∗ =
      (integralFunctional μ (gammaZeroConjugate φ hφ)).asEReal := sorry

-- Proof sketch: extensionality reduces the packaged `Γ₀` equality to the `EReal` owner statement
-- above, and `gammaZeroConjugate_apply` rewrites the left-hand side back to the Fenchel conjugate.
/-- Companion bridge: the canonical `Γ₀`-valued conjugate of `integralFunctional φ` is the
integral functional induced by the Fenchel conjugate integrand `φ*`. -/
theorem gammaZeroConjugate_integralFunctional_eq_integralFunctional_gammaZeroConjugate
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    [μ.IsComplete] [SigmaFinite μ] :
    gammaZeroConjugate (integralFunctional μ φ)
        (integralFunctional_mem_gammaZero μ φ hφ hfinite_or_nonneg) =
      integralFunctional μ (gammaZeroConjugate φ hφ) := by
  ext x
  simpa using
    congrFun
      (conjugate_integralFunctional_eq_integralFunctional_gammaZeroConjugate
        φ hφ hfinite_or_nonneg) x

end FenchelMoreau

end ERealFunction
