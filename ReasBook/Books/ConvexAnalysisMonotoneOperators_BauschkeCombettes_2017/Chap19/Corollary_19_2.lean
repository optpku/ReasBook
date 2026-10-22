/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Theorem_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: for any `x`, combine dual optimality of `v` with the strong-duality equality to
-- rewrite clause (i) of Theorem 19.1 as `x ∈ Argmin (f + g ∘ L)`. Then use the equivalence
-- between clause (i) and clause (iii) from `primal_dual_solution_tfae_for_composite_objective`,
-- whose conjugate terms already use the canonical packaged owners `f∗[hf]` and `g∗[hg]`, and
-- conclude the set equality by extensionality.
/-- Corollary 19.2: if `f ∈ Γ₀(ℋ)` and `g ∈ Γ₀(𝒦)`, if the primal infimum of `x ↦ f x + g (L x)`
is the negative of the minimum of the dual objective `v ↦ f^*(-L^* v) + g^*(v)`, and if `v` is a
dual solution, then the primal solution set is `∂ f^*(-L^* v) ∩ L⁻¹(∂ g^*(v))`, represented by
the canonical `Γ₀` conjugates `f∗[hf]` and `g∗[hg]`. -/
theorem argmin_add_comp_eq_conjugateSubdifferential_inter_preimage_of_dual_solution
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (v : K)
    (hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L)
    (hv : v ∈ Argmin (compositeDualObjective f g L)) :
    Argmin (compositePrimalObjective f g L) =
      (∂ (f∗[hf])) (-L.adjoint v) ∩
        L ⁻¹' ((∂ (g∗[hg])) v) := by
  ext x
  have h13 :=
    List.TFAE.out (primal_dual_solution_tfae_for_composite_objective hf hg L x v) 0 2
  constructor
  · intro hx
    exact h13.mp ⟨hx, hv, hstrong⟩
  · intro hx
    exact (h13.mpr hx).1

end PrimalSolutionsViaDualSolutions

end ERealFunction
