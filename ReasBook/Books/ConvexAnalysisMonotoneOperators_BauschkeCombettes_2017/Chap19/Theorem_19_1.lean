/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_19
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Corollary_16_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Theorem 19.1 is the textbook primal-dual optimality system for the composite
  objective `x ↦ f x + g (L x)`.
- `core/canonical`: the perturbation-level owner theorem is
  `primal_dual_solution_tfae_for_perturbation_function` together with the composite perturbation
  bridge `compositePerturbationFunction`.
- `bridge/view`: Proposition 19.20 translates the perturbation owner back to the composite
  objective, while Corollary 16.30 rewrites the `g`-subgradient condition as the conjugate
  subdifferential condition.
-/

-- Proof sketch: specialize the perturbation-level owner theorem to
-- `compositePerturbationFunction f g L`, then use Proposition 19.20 to rewrite its primal and
-- dual clauses into the source composite objective. The nonempty-domain hypothesis needed to
-- place the composite perturbation in `Γ₀(H × K)` remains internal to that bridge step rather
-- than part of the source-facing TFAE. Finally, apply Corollary 16.30 to convert
-- `v ∈ ∂ g (L x)` into `L x ∈ ∂ g^*(v)`, yielding the intersection/preimage form of clause (iii).
/-- Theorem 19.1: for `f ∈ Γ₀(ℋ)` and `g ∈ Γ₀(𝒦)`, the following are equivalent for `x ∈ ℋ`
and `v ∈ 𝒦`: (i) `x` minimizes `z ↦ f z + g (L z)`, `v`
minimizes
`w ↦ f^*(-L^* w) + g^*(w)`, and the primal infimum equals the negative of the dual infimum;
(ii) `-L^* v ∈ ∂ f(x)` and `v ∈ ∂ g(Lx)`; (iii)
`x ∈ ∂ f^*(-L^* v) ∩ L⁻¹(∂ g^*(v))`, with `f^*` and `g^*` represented by `f∗[hf]`
and `g∗[hg]`. -/
theorem primal_dual_solution_tfae_for_composite_objective
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (x : H) (v : K) :
    List.TFAE
      [x ∈ Argmin (compositePrimalObjective f g L) ∧
          v ∈ Argmin (compositeDualObjective f g L) ∧
          compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L,
        -L.adjoint v ∈ (∂ f) x ∧
          v ∈ (∂ g) (L x),
        x ∈ (∂ (f∗[hf])) (-L.adjoint v) ∩
          L ⁻¹' ((∂ (g∗[hg])) v)] := sorry

end PrimalSolutionsViaDualSolutions

end ERealFunction
