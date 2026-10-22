/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Definition_19_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Definition_19_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Definition_19_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Corollary_19_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped InnerProductSpace Pointwise

universe u v

namespace ERealFunction

variable {H : Type u} {G : Type v}

attribute [local instance] Classical.propDecidable

section Basic

variable [Add G]

private theorem inequalityConstraintPerturbation_value_mem_Ioi_bot
    (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G) (p : H × G) :
    ((f p.1 : EReal) + (ι[K] (R p.1 + p.2) : EReal)) ∈ Set.Ioi (⊥ : EReal) := sorry

/-- The perturbation function attached to the inequality constraint `R x ∈ K`, written through the
canonical indicator owner as `(x, y) ↦ f x + ι[K] (R x + y)`. -/
def inequalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G) :
    H × G → Set.Ioi (⊥ : EReal) :=
  fun p ↦
    ⟨(f p.1 : EReal) + (ι[K] (R p.1 + p.2) : EReal),
      inequalityConstraintPerturbation_value_mem_Ioi_bot f R K p⟩

/-- Evaluating the inequality-constraint perturbation gives the canonical indicator formula
`f x + ι[K] (R x + y)`. -/
@[simp] theorem inequalityConstraintPerturbation_apply
    (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G) (x : H) (y : G) :
    (inequalityConstraintPerturbation f R K (x, y) : EReal) =
      (f x : EReal) + (ι[K] (R x + y) : EReal) :=
  rfl

-- Proof sketch: unfold `inequalityConstraintPerturbation` and simplify the `if`-branch selected
-- by the hypothesis `R x + y ∈ K`, so the indicator term vanishes.
/-- On the feasible branch `R x + y ∈ K`, the inequality-constraint perturbation equals `f x`. -/
@[simp] theorem inequalityConstraintPerturbation_apply_of_mem
    (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G) {x : H} {y : G}
    (hxy : R x + y ∈ K) :
    inequalityConstraintPerturbation f R K (x, y) = f x := sorry

-- Proof sketch: unfold `inequalityConstraintPerturbation` and simplify the complementary
-- indicator branch selected by `R x + y ∉ K`.
/-- Off the feasible branch `R x + y ∉ K`, the inequality-constraint perturbation is `+∞`. -/
@[simp] theorem inequalityConstraintPerturbation_apply_of_not_mem
    (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G) {x : H} {y : G}
    (hxy : R x + y ∉ K) :
    inequalityConstraintPerturbation f R K (x, y) = ⟨⊤, by simp⟩ := sorry

section Primal

variable [AddZeroClass G]

-- Proof sketch: evaluate `perturbationPrimalObjective` at `0 ∈ G` and note that
-- `R x + 0 ∈ K` is equivalent to `R x ∈ K`.
/-- Proposition 19.25 (2): the primal objective of the inequality-constraint perturbation is
`f(x)` on the feasible set `{x | R x ∈ K}` and `+∞` outside it, so the primal problem is to
minimize `f` subject to `R x ∈ K`. -/
theorem perturbationPrimalObjective_inequalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G) :
    perturbationPrimalObjective (inequalityConstraintPerturbation f R K) =
      fun x : H ↦ if R x ∈ K then (f x : EReal) else ⊤ := sorry

end Primal

end Basic

section Regularity

variable [SeminormedAddCommGroup H] [NormedSpace ℝ H]
variable [SeminormedAddCommGroup G] [NormedSpace ℝ G]

-- Proof sketch: the perturbation splits as `f(x) + ι_K (R x + y)`. The feasibility hypothesis
-- makes it proper, continuity of `R` and closedness of `K` give lower semicontinuity of the
-- indicator term, and convexity of `K` together with `R.IsConvexWithRespectTo K` yields convexity
-- of its epigraph-style constraint set.
/-- Proposition 19.25 (1): if `f ∈ Γ₀(H)`, if `K` is closed and convex, if `R` is continuous and
convex with respect to `K`, and if `K ∩ R (dom f)` is nonempty, then the associated inequality-
constraint perturbation belongs to `Γ₀(H × G)`. -/
theorem inequalityConstraintPerturbation_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (R : H → G) (K : Set G)
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty) :
    inequalityConstraintPerturbation f R K ∈ Γ₀(H × G) := sorry

end Regularity

section DualFormula

variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]

-- Proof sketch: compute `perturbationDualObjective` of the perturbation as `F^*(0, v)`,
-- separate the supremum over `x` from the cone-indicator contribution in `y`, and identify
-- the latter with the
-- indicator of the polar cone `Kᵒ⊖`.
/-- Proposition 19.25 (3): if `K` is a nonempty cone, then the dual objective of the
inequality-constraint perturbation is the function that equals
`sup_x (-⟪R x, v⟫ - f x)` on `Kᵒ⊖` and `+∞` outside `Kᵒ⊖`. -/
theorem perturbationDualObjective_inequalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G)
    (hK_nonempty : K.Nonempty) (hK_cone : IsCone K) :
    perturbationDualObjective (inequalityConstraintPerturbation f R K) =
      fun v : G ↦
        if v ∈ Kᵒ⊖ then
          ⨆ x : H, -((⟪R x, v⟫_ℝ : ℝ) : EReal) - (f x : EReal)
        else ⊤ := sorry

-- Proof sketch: unfold `lagrangian` as the infimum over `y`, then split according to whether
-- `x ∈ effectiveDomain f`. For `x` in the effective domain, rewrite the remaining infimum over the
-- feasible fiber as the indicator of the polar cone, giving the three branches of the displayed
-- formula.
/-- Proposition 19.25 (4): if `K` is a nonempty cone, then the Lagrangian of the
inequality-constraint perturbation is `+∞` off `dom f`, equals `f(x) + ⟪R x, v⟫` when
`x ∈ dom f` and `v ∈ Kᵒ⊖`, and equals `-∞` when `x ∈ dom f` but `v ∉ Kᵒ⊖`. -/
theorem lagrangian_inequalityConstraintPerturbation
    (f : H → Set.Ioi (⊥ : EReal)) (R : H → G) (K : Set G)
    (hK_nonempty : K.Nonempty) (hK_cone : IsCone K) (x : H) (v : G) :
    ℒ[inequalityConstraintPerturbation f R K] x v =
      if hx : x ∈ effectiveDomain f then
        if hv : v ∈ Kᵒ⊖ then
          (f x : EReal) + (⟪R x, v⟫_ℝ : EReal)
        else ⊥
      else ⊤ := sorry

end DualFormula

section ParametricDuality

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: first combine clause (1) with Corollary 19.19 to rewrite the saddle-point
-- condition as `F (x̄, 0) + F^*(0, v̄) = 0`. Then substitute the explicit primal and dual formulas
-- from clauses (2) and (3), which yields the four explicit saddle-point optimality conditions.
/-- Proposition 19.25 (5): a pair `(x̄, v̄)` is a saddle point of the Lagrangian attached to the
inequality-constraint perturbation if and only if it satisfies the corresponding saddle-point
optimality system: `x̄ ∈ dom f`, `R x̄ ∈ K`, `v̄ ∈ Kᵒ⊖`, and `x̄` minimizes
`x ↦ f(x) + ⟪R x, v̄⟫`. -/
theorem inequalityConstraintPerturbation_isSaddlePointOn_iff
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (R : H → G) (K : Set G)
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    (xbar : H) (vbar : G) :
    IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
      (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar ↔
        xbar ∈ effectiveDomain f ∧
          R xbar ∈ K ∧
          vbar ∈ Kᵒ⊖ ∧
          xbar ∈ Argmin (fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := sorry

-- Proof sketch: under the saddle-point characterization from clause (5), evaluate the infimum
-- condition at `x̄` to get `f(x̄) ≤ f(x̄) + ⟪R x̄, v̄⟫`, while the primal feasibility and polar
-- feasibility imply `⟪R x̄, v̄⟫ ≤ 0`. Hence the inner product vanishes, and Corollary 19.19 yields
-- that `x̄` is a primal solution.
/-- Proposition 19.25 (6): any saddle point of the Lagrangian attached to the inequality-
constraint perturbation satisfies the complementary-slackness identity `⟪R x̄, v̄⟫ = 0`, and its
first component is a primal solution. -/
theorem
    inner_eq_zero_and_mem_argmin_perturbationPrimalObjective_of_inequalityConstraintPerturbation_isSaddlePoint
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (R : H → G) (K : Set G)
    (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hR_cont : Continuous R) (hR_convex : R.IsConvexWithRespectTo ℝ K)
    (hfeas : (K ∩ R '' effectiveDomain f).Nonempty)
    {xbar : H} {vbar : G}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
        (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar) :
    ⟪R xbar, vbar⟫_ℝ = 0 ∧
      xbar ∈ Argmin (perturbationPrimalObjective (inequalityConstraintPerturbation f R K)) := sorry

end ParametricDuality

end ERealFunction
