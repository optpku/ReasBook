/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section ParametricDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: Proposition 19.15 gives the equivalence of clauses (i)-(iv). For clause (v), use
-- `lagrangian_isSaddlePointOn_iff` to rewrite the saddle-point condition as equality with the
-- fiberwise supremum and infimum, then apply Proposition 19.17(ii) and (iv) to identify those two
-- extremal values with `F (x, 0)` and `-F^*(0, v)`.
/-- Corollary 19.19: for `F ∈ Γ₀(ℋ ⊕ 𝒦)` and `(x, v) ∈ ℋ × 𝒦`, the following are equivalent:
(i) `x` is a primal solution, `v` is a dual solution, and strong duality holds;
(ii) `F(x, 0) + F^*(0, v) = 0`; (iii) `(0, v) ∈ ∂ F(x, 0)`; (iv) `(x, 0) ∈ ∂ F^*(0, v)`;
(v) `(x, v)` is a saddle point of `ℒ[F]`, with `F^*` represented by `F∗[hF]`. -/
theorem primal_dual_solution_and_lagrangian_saddlePoint_tfae
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    List.TFAE
      [x ∈ Argmin (perturbationPrimalObjective F) ∧
          v ∈ Argmin (perturbationDualObjective F) ∧
          sInf (Set.range (perturbationPrimalObjective F)) =
            -sInf (Set.range (perturbationDualObjective F)),
        (F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = 0,
        ((0 : H), v) ∈ (∂ F) (x, 0),
        (x, (0 : K)) ∈ (∂ (F∗[hF])) (0, v),
        IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K) (ℒ[F]) x v] := sorry

end ParametricDuality

end ERealFunction
