/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Corollary_17_42

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: this is the specialization of Corollary 17.42 to the open set
-- `D = interior (effectiveDomain f)`.
/-- Corollary 17.40: if `f ∈ Γ₀(H)` and `gradf` represents the Gâteaux gradient of
`x ↦ (f x : EReal).toReal` on `interior (effectiveDomain f)`, then `gradf` is strong-to-weak
continuous on `interior (effectiveDomain f)`. -/
theorem gradientField_strongToWeakContinuousOn_interior_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal) (fun x ↦ toDual ℝ H (gradf x))
        (interior (effectiveDomain f))) :
    Continuous (fun x : interior (effectiveDomain f) ↦ toWeakSpace ℝ H (gradf x)) := by
  simpa using
    gradientField_strongToWeakContinuousOn_of_mem_gammaZero_of_hasGateauxDerivativeOn
      hf isOpen_interior interior_subset gradf hgrad

end DifferentiabilityOfConvexFunctions

end ERealFunction
