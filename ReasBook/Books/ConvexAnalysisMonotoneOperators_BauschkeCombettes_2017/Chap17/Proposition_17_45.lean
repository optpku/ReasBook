/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_27
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Corollary_17_44

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.45 identifies singleton subdifferentials with differentiability
  and the corresponding gradient.
- `core/canonical`: the owner abstraction is `HasGradientAt`, together with the chapter-level
  singleton-subdifferential criterion from Proposition 17.31 upgraded by Corollary 17.44.
- `bridge/view`: the unpacked pair `DifferentiableAt` and `∇ ... x = u` is the companion
  specification of `HasGradientAt`.
-/

-- Proof sketch: at an interior effective-domain point, Proposition 16.27 identifies the source
-- continuity condition needed by Proposition 17.31 with `x ∈ interior (effectiveDomain f)`. Thus
-- a singleton subdifferential yields a Gâteaux derivative with gradient `u`, and Corollary 17.44
-- upgrades that to the Fréchet-gradient owner `HasGradientAt`. Conversely, a Fréchet gradient
-- gives the corresponding Gâteaux derivative, and Proposition 17.31 identifies the singleton
-- subdifferential with that gradient.
/-- Proposition 17.45: on a finite-dimensional real Hilbert space, the subdifferential of a
function in `Γ₀(H)` at an interior point of its effective domain is the singleton `{u}` if and
only if the finite representative of `f` has gradient `u` there. -/
theorem subdifferential_eq_singleton_iff_hasGradientAt_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) (u : H) :
    (∂ f) x = ({u} : Set H) ↔
      HasGradientAt (fun y ↦ (f y : EReal).toReal) u x := by
  let g : H → ℝ := fun y ↦ (f y : EReal).toReal
  change (∂ f) x = ({u} : Set H) ↔ HasGradientAt g u x
  constructor
  · intro hsub
    have hxcont : ContinuousAtOnEffectiveDomain f x := by
      simpa [interior_effectiveDomain_eq_setOf_continuousAtOnEffectiveDomain_of_mem_gammaZero hf]
        using hx
    have hgateaux : HasGateauxDerivativeAt g (toDualMap ℝ H u) x := by
      simpa [g] using
        hasGateauxDerivativeAt_of_subdifferential_eq_singleton_of_continuousAtOnEffectiveDomain
          f hxcont hsub
    have hdiff : DifferentiableAt ℝ g x := by
      exact (gateauxDifferentiableAt_iff_frechetDifferentiableAt_of_mem_gammaZero hf hx).mp
        ⟨_, hgateaux⟩
    have hgrad : HasGradientAt g (∇ g x) x := hdiff.hasGradientAt
    have hgateaux_grad : HasGateauxDerivativeAt g (toDualMap ℝ H (∇ g x)) x :=
      hgrad.hasFDerivAt.hasGateauxDerivativeAt
    have hsub_grad : (∂ f) x = ({∇ g x} : Set H) :=
      subdifferential_eq_singleton_of_hasGateauxDerivativeAt f (interior_subset hx) _ hgateaux_grad
    have hu : ∇ g x = u := by
      have hsingletons : ({∇ g x} : Set H) = ({u} : Set H) := by
        rw [← hsub_grad, hsub]
      exact Set.singleton_injective hsingletons
    simpa [hu] using hgrad
  · intro hgrad
    have hgateaux : HasGateauxDerivativeAt g (toDualMap ℝ H u) x := by
      simpa [g] using hgrad.hasFDerivAt.hasGateauxDerivativeAt
    exact subdifferential_eq_singleton_of_hasGateauxDerivativeAt
      f (interior_subset hx) u hgateaux

/-- Unpacked `DifferentiableAt` and gradient characterization of Proposition 17.45. -/
theorem subdifferential_eq_singleton_iff_differentiableAt_and_eq_gradient_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) (u : H) :
    (∂ f) x = ({u} : Set H) ↔
      DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x ∧
        ∇ (fun y ↦ (f y : EReal).toReal) x = u := by
  let g : H → ℝ := fun y ↦ (f y : EReal).toReal
  change (∂ f) x = ({u} : Set H) ↔ DifferentiableAt ℝ g x ∧ ∇ g x = u
  constructor
  · intro hsub
    have hgrad : HasGradientAt g u x := by
      simpa [g] using
        (subdifferential_eq_singleton_iff_hasGradientAt_of_mem_gammaZero hf hx u).mp hsub
    exact ⟨hgrad.differentiableAt, hgrad.gradient⟩
  · rintro ⟨hdiff, hu⟩
    have hgrad : HasGradientAt g u x := by
      simpa [hu] using hdiff.hasGradientAt
    exact (subdifferential_eq_singleton_iff_hasGradientAt_of_mem_gammaZero hf hx u).mpr <| by
      simpa [g] using hgrad

end DifferentiabilityOfConvexFunctions

end ERealFunction
