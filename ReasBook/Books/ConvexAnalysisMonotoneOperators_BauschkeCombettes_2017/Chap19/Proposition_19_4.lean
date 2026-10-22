/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_27
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Corollary_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Proposition 19.4 is the textbook uniqueness consequence for primal solutions of
  the composite Fenchel dual pair.
- `core/canonical`: the owner results are
  `argmin_add_comp_eq_conjugateSubdifferential_inter_preimage_of_dual_solution` and
  `subdifferential_eq_singleton_of_hasGateauxDerivativeAt`.
- `bridge/view`: the present theorem composes those owners to turn the dual optimality system into
  the singleton primal-solution conclusion. -/

-- Proof sketch: Corollary 19.2 identifies the primal minimizer set with
-- `∂ f^*(-L^* v) ∩ L⁻¹(∂ g^*(v))`. Apply Proposition 17.31 (1) to the conjugate `f*` at
-- `-L^* v`; the Gâteaux derivative hypothesis makes `∂ f^*(-L^* v)` the singleton `{xstar}`.
-- Therefore every primal minimizer lies in `{xstar}`, so the primal problem has at most one
-- solution and any solution is `xstar`.
/-- Proposition 19.4: if `f ∈ Γ₀(ℋ)` and `g ∈ Γ₀(𝒦)`, if the primal infimum of
`x ↦ f x + g (L x)` equals the negative minimum of the dual objective
`v ↦ f^*(-L^* v) + g^*(v)`, and if `v` is a dual solution at which `f^*` has Gâteaux gradient
`xstar` at `-L^* v`, then every primal solution is `xstar`. -/
theorem eq_of_mem_argmin_add_comp_of_dual_solution_and_hasGateauxDerivativeAt_conjugate
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (v : K) (xstar : H)
    (hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L)
    (hv : v ∈ Argmin (compositeDualObjective f g L))
    (hgrad :
      HasGateauxDerivativeAt
        (fun y : H ↦ (f∗[hf] y : EReal).toReal)
        (toDual ℝ H xstar) (-L.adjoint v))
    (x : H) (hx : x ∈ Argmin (compositePrimalObjective f g L)) :
    x = xstar := by
  have hx_sub : x ∈ (∂ (f∗[hf])) (-L.adjoint v) := by
    rw [argmin_add_comp_eq_conjugateSubdifferential_inter_preimage_of_dual_solution
      hf hg L v hstrong hv] at hx
    exact hx.1
  have hv_dom : -L.adjoint v ∈ effectiveDomain (f∗[hf]) := by
    exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero
      (gammaZeroConjugate_mem_gammaZero hf) ⟨x, hx_sub⟩
  have hsub :
      (∂ (f∗[hf])) (-L.adjoint v) = ({xstar} : Set H) :=
    subdifferential_eq_singleton_of_hasGateauxDerivativeAt
      (f∗[hf]) hv_dom xstar (by
        simpa using hgrad)
  simpa [hsub] using hx_sub

/-- Set-valued reformulation of Proposition 19.4: the primal minimizer set is contained in the
singleton `{xstar}`. -/
theorem argmin_add_comp_subset_singleton_of_dual_solution_and_hasGateauxDerivativeAt_conjugate
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (v : K) (xstar : H)
    (hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L)
    (hv : v ∈ Argmin (compositeDualObjective f g L))
    (hgrad :
      HasGateauxDerivativeAt
        (fun y : H ↦ (f∗[hf] y : EReal).toReal)
        (toDual ℝ H xstar) (-L.adjoint v)) :
    Argmin (compositePrimalObjective f g L) ⊆ ({xstar} : Set H) := by
  intro x hx
  simpa using
    eq_of_mem_argmin_add_comp_of_dual_solution_and_hasGateauxDerivativeAt_conjugate
      hf hg L v xstar hstrong hv hgrad x hx

end PrimalSolutionsViaDualSolutions

end ERealFunction
