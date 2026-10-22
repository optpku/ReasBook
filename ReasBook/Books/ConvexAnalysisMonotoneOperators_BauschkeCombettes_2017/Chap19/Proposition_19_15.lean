/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_67
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Theorem_16_29
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Definition_19_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section ParametricDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: clause (i) rewrites primal and dual optimality as attainment of the primal and
-- dual infima, so together with the strong-duality identity it becomes
-- `F(x, 0) + F^*(0, v) = 0`. The remaining equivalences are the Fenchel--Young and
-- conjugate-subdifferential equivalences from Theorem 16.29 applied to `F` on `H × K` at
-- `(x, 0)` and `(0, v)`.
/-- Proposition 19.15: for `F ∈ Γ₀(ℋ × 𝒦)` and `(x, v) ∈ ℋ × 𝒦`, the following are equivalent:
(i) `x` is a primal solution, `v` is a dual solution, and strong duality holds;
(ii) `F(x, 0) + F^*(0, v) = 0`; (iii) `(0, v) ∈ ∂ F(x, 0)`; (iv) `(x, 0) ∈ ∂ F^*(0, v)`, with
`F^*` represented by `F∗[hF]`. -/
theorem primal_dual_solution_tfae_for_perturbation_function
    (F : H × K → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × K)) (x : H) (v : K) :
    List.TFAE
      [x ∈ Argmin (perturbationPrimalObjective F) ∧
          v ∈ Argmin (perturbationDualObjective F) ∧
          sInf (Set.range (perturbationPrimalObjective F)) =
            -sInf (Set.range (perturbationDualObjective F)),
        (F (x, 0) : EReal) + (F∗[hF] (0, v) : EReal) = 0,
        ((0 : H), v) ∈ (∂ F) (x, 0),
        (x, (0 : K)) ∈ (∂ (F∗[hF])) (0, v)] := sorry

end ParametricDuality

end

end ERealFunction
