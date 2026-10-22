/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_35
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Remark_2_41_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι] {μ L : ℝ}

/- Primary domain: exact proximal-gradient inequalities for smooth minimax problems on a real
Hilbert space.

Owner declarations sampled for this refinement:
* `SmoothMinimaxProblem` in `Definition_2_38` owns the feasible set and component family;
* `SmoothMinimaxProblem.lowerRegularizedModel_le_objective` in `Text_2_4` gives the canonical
  lower comparison between the objective and the lower regularized affine model;
* `SmoothMinimaxProblem.objective_le_upperRegularizedModel` in `Text_2_4` gives the canonical
  upper comparison at the exact-step point;
* `regularizedMaxTypeObjective_strongConvexOn_univ` in `Remark_2_41_1` and
  `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem` provide the quadratic-growth owner step for
  the regularized affine model, after restricting the whole-space strong-convexity owner to the
  feasible set.

Accordingly the primitive data here are the minimax owner object `problem`, the base point `xBar`,
the positive curvature parameter `γ`, and the feasible minimizer data for the owner regularized
affine model.
The reduced-gradient expression `γ • (xBar - xPlus)` is derived from that owner step and is not a
separate public wrapper.
-/

namespace SmoothMinimaxProblem

/-- Theorem 2.42: for a smooth minimax problem on a real Hilbert space, if `L ≤ γ`, `x ∈ Q`, and
`xPlus`
minimizes
the owner quadratically regularized max-type affine model
`quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar`
over the feasible set, then the objective is bounded below by the value at `xPlus`, the affine
term induced by `γ • (xBar - xPlus)`, the quadratic correction `(2γ)⁻¹ ‖γ • (xBar - xPlus)‖²`,
and the strong-convexity term `(μ / 2) ‖x - xBar‖²`. -/
-- Proof sketch: compare `problem x` with the lower regularized affine model at `x` via
-- `lowerRegularizedModel_le_objective`, compare `problem xPlus` with the upper regularized model
-- at `xPlus` via `objective_le_upperRegularizedModel`, and use strong convexity of the owner
-- regularized affine model together with `hxPlus` to get quadratic growth from `xPlus` to `x`.
-- Expanding `‖x - xPlus‖² - ‖x - xBar‖²` yields the reduced-gradient form.
theorem objective_lower_bound_of_isMinOn_regularizedAffineApproximation
    (problem : SmoothMinimaxProblem E ι μ L) (xBar : E)
    {γ : NNRealˣ} {x xPlus : E} (hLγ : L ≤ (γ : ℝ))
    (hx : x ∈ problem.feasibleSet)
    (hxPlus_mem : xPlus ∈ problem.feasibleSet)
    (hxPlus :
      IsMinOn
        (quadraticallyRegularizedObjective
          (problem.affineApproximation xBar) γ xBar)
        problem.feasibleSet xPlus) :
    problem x ≥
        problem xPlus +
          inner ℝ ((γ : ℝ) • (xBar - xPlus)) (x - xBar) +
          (1 / (2 * (γ : ℝ))) * ‖(γ : ℝ) • (xBar - xPlus)‖ ^ (2 : ℕ) +
        (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  let modelγ :=
    quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar
  let g := reducedGradientOf (γ : ℝ) xBar xPlus
  let correction := (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ)
  have hlower :=
    lowerRegularizedModel_le_objective problem xBar x
  -- The upper model comparison identifies the exact-step value with the `γ`-regularized model.
  have hupper :
      problem xPlus ≤ modelγ xPlus := by
    calc
      problem xPlus ≤
          quadraticallyRegularizedObjective (problem.affineApproximation xBar) L xBar xPlus :=
        objective_le_upperRegularizedModel problem xBar xPlus
      _ ≤ modelγ xPlus := by
        simp [modelγ, quadraticallyRegularizedObjective_apply]
        nlinarith [hLγ, sq_nonneg ‖xPlus - xBar‖]
  have hstrong :
      StrongConvexOn Set.univ (γ : ℝ) modelγ := by
    change StrongConvexOn Set.univ (γ : ℝ)
      (quadraticallyRegularizedObjective
        (maxTypeAffineApproximation problem.components xBar) γ xBar)
    exact
      regularizedMaxTypeObjective_strongConvexOn_univ problem.components xBar γ
  -- Restrict the ambient strong-convexity owner to the feasible set before applying quadratic growth.
  have hstrong_feasible :
      StrongConvexOn problem.feasibleSet (γ : ℝ) modelγ := by
    refine ⟨problem.feasible_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    simpa using hstrong.2 (by simp) (by simp) ha hb hab
  have hgrowth :
      modelγ x ≥
        modelγ xPlus +
          ((γ : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) :=
    hstrong_feasible.quadratic_growth_of_isMinOn_of_mem hxPlus_mem hxPlus x hx
  -- Rewrite the quadratic-growth term as a completed square centered at the reduced-gradient step.
  have hmodel :
      problem xPlus + ((γ : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) =
        quadraticallyRegularizedObjective
          (affineModelAt (fun _ : E ↦ problem xPlus + correction) (fun _ ↦ g) xBar)
          (γ : ℝ)
          xBar
          x := by
    have hcompleted :=
      quadraticallyRegularizedObjective_affineModelAt_eq_completedSquare
        (fun _ : E ↦ problem xPlus + correction) g xBar x γ
    have hxPlus_eq : xBar - ((γ : ℝ)⁻¹) • g = xPlus := by
      have hγ : (γ : ℝ) ≠ 0 := by
        exact (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))).ne'
      dsimp [g, reducedGradientOf]
      rw [smul_smul, inv_mul_cancel₀ hγ, one_smul]
      abel
    rw [hcompleted, hxPlus_eq]
    simp only [g, correction]
    ring
  -- Chain the lower model bound, quadratic growth, and the completed-square expansion.
  calc
    problem x ≥
        quadraticallyRegularizedObjective (problem.affineApproximation xBar) μ xBar x := hlower
    _ =
        modelγ x -
          ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
            simp [modelγ, quadraticallyRegularizedObjective_apply]
    _ ≥
        modelγ xPlus +
          ((γ : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
            gcongr
    _ ≥
        problem xPlus +
          ((γ : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
            gcongr
    _ =
        (quadraticallyRegularizedObjective
            (affineModelAt (fun _ : E ↦ problem xPlus + correction) (fun _ ↦ g) xBar)
            (γ : ℝ)
            xBar
            x) -
          ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
            rw [← hmodel]
    _ =
        problem xPlus +
          inner ℝ ((γ : ℝ) • (xBar - xPlus)) (x - xBar) +
          (1 / (2 * (γ : ℝ))) * ‖(γ : ℝ) • (xBar - xPlus)‖ ^ (2 : ℕ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
            simp [quadraticallyRegularizedObjective_apply, affineModelAt_apply, g, correction,
              reducedGradientOf]
            ring

end SmoothMinimaxProblem

end
