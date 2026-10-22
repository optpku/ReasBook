/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Corollary_17_42

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient InnerProductSpace Topology

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: for a function in `Γ₀(H)`, Fréchet differentiability on
-- `interior (effectiveDomain f)` gives a genuine gradient field there because the set is open.
-- Use the convex-analysis continuity theorem for gradients of differentiable convex functions on
-- the interior of the effective domain.
/-- Corollary 17.43: if `f ∈ Γ₀(H)` is Fréchet differentiable on `interior (effectiveDomain f)`,
then its gradient is continuous on `interior (effectiveDomain f)`. -/
theorem gradient_continuousOn_interior_effectiveDomain_of_mem_gammaZero_of_differentiableOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hdiff : DifferentiableOn ℝ (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f))) :
    ContinuousOn (∇ fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) := by
  let g : H → ℝ := fun x ↦ (f x : EReal).toReal
  let D : Set H := interior (effectiveDomain f)
  have hdiff' : DifferentiableOn ℝ g D := by
    simpa [g, D] using hdiff
  have hgrad : HasGateauxDerivativeOn g (fun x ↦ toDual ℝ H (∇ g x)) D := by
    intro x hx
    have hx_nhds : D ∈ 𝓝 x := by
      simpa [D] using isOpen_interior.mem_nhds hx
    exact
      (hdiff'.hasGradientAt hx_nhds).hasFDerivAt.hasFDerivWithinAt.hasGateauxDerivativeWithinAt
        hx_nhds
  intro x hx
  change x ∈ D at hx
  have hx_nhds : D ∈ 𝓝 x := by
    simpa [D] using isOpen_interior.mem_nhds hx
  exact
    (frechetDifferentiableAt_iff_gradientField_continuousWithinAt_of_mem_gammaZero_of_hasGateauxDerivativeOn
      hf (by simp [D]) (by simpa [D] using interior_subset) (∇ g) hgrad
      hx).mp ((hdiff' x hx).differentiableAt hx_nhds)

end DifferentiabilityOfConvexFunctions

end ERealFunction
