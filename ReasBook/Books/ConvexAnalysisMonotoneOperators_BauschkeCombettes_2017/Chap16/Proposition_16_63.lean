/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_50
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Theorem_16_29

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [μ.IsComplete] [SigmaFinite μ]

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.63 identifies the subdifferential of the source-level integral
  functional `integralFunctional μ φ` with the `L²` fields that lie almost everywhere in the
  pointwise subdifferential of `φ`.
- `core/canonical`: the owner objects are `integralFunctional μ φ`, `gammaZeroConjugate`, and the
  subdifferential/Fenchel--Young equivalence from Theorem 16.29.
- `bridge/view`: Proposition 13.50 rewrites the conjugate of the integral functional back to an
  integral functional, while the companion membership lemma below packages the set equality in the
  direct `u ∈ (∂ ·) x` form used downstream.
-/

-- Proof sketch: Proposition 13.50 identifies the Fenchel conjugate of `integralFunctional φ`
-- with the integral functional induced by `gammaZeroConjugate φ hφ`, while Proposition 9.40 gives
-- the required `Γ₀` membership. Applying Theorem 16.29 to `integralFunctional φ` and then using
-- the pointwise Fenchel--Young inequality from Proposition 13.15 shows that equality in the
-- integrated Fenchel--Young identity holds exactly when `u ω ∈ (∂ φ) (x ω)` almost everywhere.
/-- Proposition 16.63: if `φ ∈ Γ₀(H)` and either (i) `μ Set.univ < ∞` or (ii) `φ` attains its
minimum value `0` at the origin, then at every point of the effective domain of the integral
functional induced by `φ`, the subdifferential consists exactly of those `L²` fields whose values
belong almost everywhere to the pointwise subdifferential of `φ`. The `Γ₀`-membership clause is
the existing theorem `integralFunctional_mem_gammaZero`. -/
theorem subdifferential_integralFunctional_eq_ae_subdifferential
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ⊤ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    {x : Ω →₂[μ] H} (hx : x ∈ effectiveDomain (integralFunctional μ φ)) :
    (∂ integralFunctional μ φ) x =
      {u : Ω →₂[μ] H | ∀ᵐ ω ∂μ, u ω ∈ (∂ φ) (x ω)} := sorry

/-- Companion bridge: membership in the subdifferential of the integral functional is equivalent to
almost-everywhere pointwise subdifferential membership. -/
theorem mem_subdifferential_integralFunctional_iff_ae_mem_subdifferential
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ⊤ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    {x u : Ω →₂[μ] H} (hx : x ∈ effectiveDomain (integralFunctional μ φ)) :
    u ∈ (∂ integralFunctional μ φ) x ↔
      ∀ᵐ ω ∂μ, u ω ∈ (∂ φ) (x ω) := by
  rw [subdifferential_integralFunctional_eq_ae_subdifferential φ hφ hfinite_or_nonneg hx]
  simp

end SubdifferentialCalculus

end

end ERealFunction
