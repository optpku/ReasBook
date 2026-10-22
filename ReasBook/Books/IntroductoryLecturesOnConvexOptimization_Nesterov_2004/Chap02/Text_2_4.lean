/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {m : ℕ} {μ L : ℝ}

namespace SmoothMinimaxProblem

/- Text 2.4 also yields the canonical owner inequalities for a smooth minimax problem and its
quadratically regularized affine models.

Sampled owner declarations before drafting:
* `SmoothMinimaxProblem` in `Definition_2_38.lean`, which owns the feasible set and the max-type
  objective;
* `SmoothMinimaxProblem.affineApproximation` in `Definition_2_38.lean`, which owns the affine
  max-type model at `xBar`;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17.lean`, which adds the centered
  quadratic penalty to that affine model;
* `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47.lean`, which shows that the constrained source item factors through this owner.

Best owner abstraction:
* `problem : SmoothMinimaxProblem E ι μ L`.

Primitive data:
* the minimax owner `problem`;
* the base point `xBar`.

Derived API:
* the `μ`- and `L`-regularized affine models at `xBar`;
* the constrained optimal value `sInf (problem '' problem.feasibleSet)`;
* the regularized model values obtained by taking infima over `problem.feasibleSet`.

The four comparison theorems below are the clean canonical owner form of the sandwich estimates in
Text 2.4. They are kept as separate atomic statements because the source gives distinct pointwise
and optimal-value bounds, and later files reuse these owner inequalities directly. -/

section

variable (problem : SmoothMinimaxProblem E ι μ L) (xBar : E)

local notation "modelValue" =>
  fun γ ↦
    sInf
      ((quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar) ''
        problem.feasibleSet)

local notation "valueFunction" =>
  sInf (problem '' problem.feasibleSet)

/-- Helper for Text 2.4: the affine approximation of a smooth minimax problem is continuous,
because it is the finite maximum of continuous first-order Taylor models. -/
theorem affineApproximation_continuous :
    Continuous (problem.affineApproximation xBar) := by
  classical
  -- Each first-order Taylor model is affine, hence continuous, and finite maxima preserve continuity.
  change Continuous (maxTypeAffineApproximation problem.components xBar)
  have hcont :
      Continuous
        (fun x : E ↦
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : ι ↦ firstOrderTaylorModelAt (problem.components i) xBar x)) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty fun i _ ↦ by
      simpa [firstOrderTaylorModelAt_apply] using
        continuous_const.add
          ((innerSL ℝ (gradient (problem.components i) xBar)).continuous.comp
            (continuous_id.sub continuous_const))
  simpa [maxTypeAffineApproximation_apply_firstOrderTaylorModelAt] using hcont

/-- Helper for Text 2.4: the quadratically regularized affine approximation is continuous on the
ambient space. -/
theorem regularizedAffineApproximation_continuous
    (γ : ℝ) :
    Continuous
      (quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar) := by
  -- Add the continuous quadratic penalty to the continuous affine max-type model.
  simpa [quadraticallyRegularizedObjective_apply] using
    (problem.affineApproximation_continuous xBar).add
      (continuous_const.mul (((continuous_id.sub continuous_const).norm).pow (2 : ℕ)))

/-- Helper for Text 2.4: a positive quadratic regularization makes the affine model bounded below
on the feasible set. -/
theorem regularizedAffineApproximation_image_bddBelow
    (γ : NNRealˣ) :
    BddBelow
      ((quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar) ''
        problem.feasibleSet) := by
  classical
  let i0 : ι := Classical.choice inferInstance
  let g0 : E := gradient (problem.components i0) xBar
  let c : ℝ := problem.components i0 xBar - ‖g0‖ ^ (2 : ℕ) / (2 * (γ : ℝ))
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  refine ⟨c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hcomponent_le :
      firstOrderTaylorModelAt (problem.components i0) xBar x ≤
        problem.affineApproximation xBar x := by
    -- One Taylor component is bounded above by the finite maximum defining the affine model.
    rw [SmoothMinimaxProblem.affineApproximation, maxTypeAffineApproximation_apply_firstOrderTaylorModelAt]
    exact Finset.le_sup' (fun j : ι ↦ firstOrderTaylorModelAt (problem.components j) xBar x)
      (by simp)
  have hquad :
      -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) ≤
        inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
    inner_add_quadratic_lower_bound (γ : ℝ) hγ g0 (x - xBar)
  have hlower :
      c ≤
        quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar x := by
    -- Lower-bound the regularized model by one affine component plus the positive quadratic term.
    have hbase_raw :
        problem.components i0 xBar + -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) ≤
          problem.components i0 xBar +
            (inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left hquad (problem.components i0 xBar)
    have hbase :
        c ≤
          problem.components i0 xBar +
            inner ℝ g0 (x - xBar) +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
      -- Route correction: normalize the added lower bound algebraically before comparing with the
      -- affine Taylor component.
      calc
        c = problem.components i0 xBar + -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) := by
          dsimp [c]
          ring
        _ ≤
            problem.components i0 xBar +
              (inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ)) := hbase_raw
        _ =
            problem.components i0 xBar +
              inner ℝ g0 (x - xBar) +
              ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
                ring
    calc
      c ≤
          problem.components i0 xBar +
            inner ℝ g0 (x - xBar) +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := hbase
      _ =
          firstOrderTaylorModelAt (problem.components i0) xBar x +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
              simp [g0]
      _ ≤
          problem.affineApproximation xBar x +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_right hcomponent_le (((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ))
      _ =
          quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar x := by
            simp [quadraticallyRegularizedObjective_apply]
  exact hlower

/-- Helper for Text 2.4: a positive regularized affine model of a smooth minimax problem has a
unique feasible minimizer. -/
theorem existsUnique_isMinOn_regularizedAffineApproximation
    (γ : NNRealˣ) :
    ∃! xPlus : E,
      xPlus ∈ problem.feasibleSet ∧
        IsMinOn
          (quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar)
          problem.feasibleSet
          xPlus := by
  let regularizedModel :=
    quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  have hstrong_univ :
      StrongConvexOn Set.univ (γ : ℝ) regularizedModel := by
    -- The centered quadratic term provides the strong convexity modulus `γ`.
    simpa [regularizedModel, SmoothMinimaxProblem.affineApproximation] using
      regularizedMaxTypeObjective_strongConvexOn_univ problem.components xBar γ
  have hstrong :
      StrongConvexOn problem.feasibleSet (γ : ℝ) regularizedModel := by
    -- Restrict the ambient strong-convexity estimate to the feasible set.
    rw [strongConvexOn_iff_convex] at hstrong_univ ⊢
    exact hstrong_univ.subset (by simp) problem.feasible_convex
  obtain ⟨xPlus, hxPlus, hmin⟩ :=
    exists_isMinOn_of_isClosed_of_complete_of_bddBelow
      problem.feasible_closed
      problem.feasible_nonempty
      (problem.regularizedAffineApproximation_continuous xBar (γ : ℝ)).continuousOn
      hstrong
      hγ
      (problem.regularizedAffineApproximation_image_bddBelow xBar γ)
  refine ⟨xPlus, ⟨hxPlus, hmin⟩, ?_⟩
  intro y hy
  -- Strict convexity upgrades existence to uniqueness of the feasible minimizer.
  exact
    (hstrong.strictConvexOn hγ).eq_of_isMinOn
      hy.2
      hmin
      hy.1
      hxPlus

/-- Helper for Text 2.4: an attained minimizer of the regularized affine model realizes the real
infimum `modelValue`. -/
lemma regularizedModelValue_eq_of_isMinOn
    {γ : ℝ} {x : E}
    (hx : x ∈ problem.feasibleSet)
    (hmin :
      IsMinOn
        (quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar)
        problem.feasibleSet
        x) :
    modelValue γ =
      quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar x := by
  let regularizedModel :=
    quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar
  have hglb : IsGLB (regularizedModel '' problem.feasibleSet) (regularizedModel x) :=
    hmin.isGLB hx
  -- The minimizing value is exactly the infimum of the model-image set.
  change sInf (regularizedModel '' problem.feasibleSet) = regularizedModel x
  simpa using hglb.csInf_eq ⟨regularizedModel x, ⟨x, hx, rfl⟩⟩

/-- Text 2.4 (2): the `μ`-regularized affine model at `xBar` is a global lower quadratic model
for the minimax objective. -/
-- Proof sketch: apply the lower tangent quadratic bound to each component of the minimax family,
-- pass to the finite maximum defining `problem`, and rewrite the resulting affine model as
-- `problem.affineApproximation xBar`.
theorem lowerRegularizedModel_le_objective
    (x : E) :
    quadraticallyRegularizedObjective (problem.affineApproximation xBar) μ xBar x ≤
      problem x := by
  -- Rewrite the owner lower quadratic bound into the regularized affine-model notation.
  simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation,
    SmoothMinimaxProblem.objective, ge_iff_le] using
    (maxTypeObjective_quadratic_bounds_of_components_mem
      problem.components μ L problem.components_mem x xBar).1

/-- Text 2.4 (3): the minimax objective is bounded above by the `L`-regularized affine model at
`xBar`. -/
-- Proof sketch: apply the upper tangent quadratic bound to each component of the minimax family,
-- pass to the finite maximum defining `problem`, and rewrite the resulting affine model as
-- `problem.affineApproximation xBar`.
theorem objective_le_upperRegularizedModel
    (x : E) :
    problem x ≤
      quadraticallyRegularizedObjective (problem.affineApproximation xBar) L xBar x := by
  -- Rewrite the owner upper quadratic bound into the regularized affine-model notation.
  simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation,
    SmoothMinimaxProblem.objective] using
    (maxTypeObjective_quadratic_bounds_of_components_mem
      problem.components μ L problem.components_mem x xBar).2

/-- Text 2.4 (4): the optimal value of the `μ`-regularized affine model is bounded above by the
optimal value of the minimax objective. -/
-- Proof sketch: apply `lowerRegularizedModel_le_objective` pointwise on `problem.feasibleSet`,
-- then pass to infima over that feasible set using existence and uniqueness of the minimizer of
-- `problem`.
theorem lowerRegularizedModelValue_le_optimalValue
    :
    modelValue μ ≤ valueFunction := by
  classical
  let i0 : ι := Classical.choice inferInstance
  have hμ_pos : 0 < μ := (mem_S11_iff.mp (problem.components_mem i0)).mu_pos
  let γμ : NNRealˣ :=
    Units.mk0 (Real.toNNReal μ) (ne_of_gt (by rwa [Real.toNNReal_pos]))
  have hγμ : (γμ : ℝ) = μ := by
    simp [γμ, Real.toNNReal_of_nonneg hμ_pos.le]
  obtain ⟨xμ, hxμ, hminμ_units⟩ :=
    ExistsUnique.exists (problem.existsUnique_isMinOn_regularizedAffineApproximation xBar γμ)
  have hminμ :
      IsMinOn
        (quadraticallyRegularizedObjective (problem.affineApproximation xBar) μ xBar)
        problem.feasibleSet
        xμ := by
    -- Rewrite the unit-valued curvature back to the scalar `μ`.
    simpa [hγμ] using hminμ_units
  have hmodel_eq :
      modelValue μ =
        quadraticallyRegularizedObjective (problem.affineApproximation xBar) μ xBar xμ := by
    exact regularizedModelValue_eq_of_isMinOn (problem := problem) (xBar := xBar) hxμ hminμ
  have hobjective_nonempty : (problem '' problem.feasibleSet).Nonempty := by
    rcases problem.feasible_nonempty with ⟨x, hx⟩
    exact ⟨problem x, ⟨x, hx, rfl⟩⟩
  rw [hmodel_eq]
  rw [isMinOn_iff] at hminμ
  refine le_csInf hobjective_nonempty ?_
  rintro _ ⟨x, hx, rfl⟩
  -- Compare the attained lower model value with each feasible objective value.
  exact le_trans (hminμ x hx) (problem.lowerRegularizedModel_le_objective xBar x)

/-- Text 2.4 (5): the optimal value of the minimax objective is bounded above by the optimal value
of the `L`-regularized affine model. -/
-- Proof sketch: apply `objective_le_upperRegularizedModel` pointwise on `problem.feasibleSet`,
-- then pass to infima over that feasible set using existence and uniqueness of the minimizer of
-- `problem`.
theorem optimalValue_le_upperRegularizedModelValue
    :
    valueFunction ≤ modelValue L := by
  have hupper_nonempty :
      ((quadraticallyRegularizedObjective (problem.affineApproximation xBar) L xBar) ''
        problem.feasibleSet).Nonempty := by
    rcases problem.feasible_nonempty with ⟨x, hx⟩
    exact ⟨_, ⟨x, hx, rfl⟩⟩
  refine le_csInf hupper_nonempty ?_
  rintro _ ⟨x, hx, rfl⟩
  -- Bound the optimal value by each feasible objective value, then by the upper regularized model.
  exact le_trans
    (csInf_le (problem.objective_image_bddBelow) ⟨x, hx, rfl⟩)
    (problem.objective_le_upperRegularizedModel xBar x)

end

end SmoothMinimaxProblem

namespace SmoothFunctionalConstraintsMinimizationProblem

/- Text 2.4 lies in the constrained smooth minimax bridge/view domain for Chapter 2.

Sampled owner declarations before drafting:
* `SmoothFunctionalConstraintsMinimizationProblem` in `Definition_2_44.lean`, which owns the
  ambient set `Q`, the objective `f₀`, and the constraint family `fᵢ`;
* `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47.lean`, which is the fixed-`t` bridge to the canonical owner
  `SmoothMinimaxProblem`;
* `SmoothMinimaxProblem.affineApproximation` in `Definition_2_38.lean`, which owns the affine
  max-type local model;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17.lean`, which owns the centered
  quadratic regularization of that affine model.

Best owner abstraction:
* source-facing: the constrained exact-step subproblem for the fixed-`t` bridge problem;
* core/canonical: the owner regularized affine model
  `quadraticallyRegularizedObjective
    ((problem.toParametricSmoothMinimaxProblem t).affineApproximation xBar)
    γ
    xBar`;
* bridge/view: `problem.toParametricSmoothMinimaxProblem t`.

Primitive data:
* the constrained problem `problem`;
* the scalar parameter `t`;
* the base point `xBar`;
* the regularization parameter `γ`.

Derived API:
* existence and uniqueness of the constrained exact step for the fixed-`t` regularized affine
  model.

The source-facing constrained statement is therefore kept on the
`toParametricSmoothMinimaxProblem` bridge rather than by introducing a second chosen-point owner
or an existential wrapper around the exact step. -/

section

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
variable (t : ℝ) (xBar : E)

/-- Text 2.4 (1): for every fixed parameter `t` and every positive regularization parameter `γ`,
the quadratically regularized affine model of the fixed-`t` parametric problem has a unique
minimizer on the ambient set `Q`; equivalently, the constrained gradient mapping is well defined.
-/
-- Proof sketch: pass to the fixed-`t` smooth minimax owner, apply the owner existence/uniqueness
-- theorem for the regularized affine model, and rewrite the feasible set back to `Q`.
theorem existsUnique_isMinOn_regularizedAffineApproximation
    (γ : NNRealˣ) :
    ∃! xPlus : E,
      xPlus ∈ problem.ambientSet ∧
        IsMinOn
          (quadraticallyRegularizedObjective
            ((problem.toParametricSmoothMinimaxProblem t).affineApproximation xBar)
            γ
            xBar)
          problem.ambientSet
          xPlus := by
  -- Reuse the fixed-`t` smooth minimax owner theorem and rewrite its feasible set back to `Q`.
  simpa using
    SmoothMinimaxProblem.existsUnique_isMinOn_regularizedAffineApproximation
      (problem := problem.toParametricSmoothMinimaxProblem t)
      (xBar := xBar)
      γ

end

end SmoothFunctionalConstraintsMinimizationProblem
