/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_47
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_48

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

open scoped RegularizedModelValueRootNotation

section

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)

local notation "parametricProblem" => problem.toParametricSmoothMinimaxProblem

local notation "modelValue" =>
  problem.regularizedModelValue

local notation "parametricOptimalValue" =>
  fun t ↦ sInf ((parametricProblem t) '' problem.ambientSet)

/-
Primary domain: Chapter 2 parameter updates for the constrained max-type value function and the
associated quadratically regularized local-model values.

Owner abstractions sampled before refining:
- `SmoothFunctionalConstraintsMinimizationProblem` from `Definition_2_44.lean`;
- `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` from
  `Definition_2_47.lean`;
- `SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue` from
  `Definition_2_47.lean`;
- `SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValueRoot` from
  `Definition_2_48.lean`;
- the constrained optimal-value bridge theorems in `Remark_2_47_1.lean`;
- the owner secant estimate pattern `ConvexOn.secant_lower_bound_left_shift` from
  `Proposition_2_26.lean`.

Source/core/bridge triage:
- source-facing: the two Lemma 2.24 comparison statements;
- core/canonical:
  the fixed-`t` owner `problem.toParametricSmoothMinimaxProblem t : SmoothMinimaxProblem ...`;
- bridge/view: the explicit `toLagrangianProblem` / component-family presentation.

The best owner abstraction here is therefore `parametricProblem t`, together with its derived
regularized affine-model value. The local notation `modelValue` therefore recalls the owner
declaration `problem.regularizedModelValue`, and the local notation `parametricOptimalValue`
follows the bridge surface already used in `Remark_2_47_1` rather than rebuilding separate
objective/feasible-set wrappers.
Primitive data are only `problem`, the owner update `(xBar, t) ↦ t★[problem; xBar](t)`, and the
scalar comparison hypotheses not already owned upstream. The `μ`- and `L`-model values and the
constrained optimal-value function
`t ↦ sInf ((parametricProblem t) '' problem.ambientSet)` remain derived API, so this file states
the lemma directly in those owner terms instead of keeping a parallel scalar-function parameter or
a wrapper root package.
-/

variable {xBar : E} {tBar κ : ℝ}

/-- Lemma 2.24 (1): if the owner `μ`-model value at `(tBar, xBar)` dominates `(1 - κ)` times the
owner `L`-model value, if the owner constrained value at `tBar` is positive, and if
`τ ↦ modelValue τ xBar μ` is convex and has a root not smaller than `tBar`, then the selected
owner least root lies strictly above the reference parameter `tBar`. -/
-- Proof sketch: use
-- `problem.parametricProblemOptimalValue_le_upperRegularizedModelValue tBar xBar` together with
-- positivity of `parametricOptimalValue tBar` to get positivity of the owner `L`-model value.
-- Combine that with `hcomparison` and `κ < 1` to deduce positivity of the owner `μ`-model
-- value. Then apply `problem.regularizedModelValueRoot_mem_of_convexOn xBar tBar` to see that the
-- selected update is an actual root above `tBar`; equality `t★[problem; xBar](tBar) = tBar`
-- would force `modelValue tBar xBar μ = 0`, contradicting the derived positivity.
theorem referenceParameter_lt_regularizedModelValueRoot
    (hκ : κ < 1)
    (hcomparison : modelValue tBar xBar μ ≥ (1 - κ) * modelValue tBar xBar L)
    (hvalue_pos : 0 < parametricOptimalValue tBar)
    (hmu_convex : ConvexOn ℝ Set.univ (fun τ ↦ modelValue τ xBar μ))
    (hmu_root : ∃ τ : ℝ, tBar ≤ τ ∧ modelValue τ xBar μ = 0) :
    tBar < t★[problem; xBar](tBar) := by
  have hparametric_upper :
      parametricOptimalValue tBar ≤ modelValue tBar xBar L := by
    let p := parametricProblem tBar
    have hupper_nonempty :
        ((quadraticallyRegularizedObjective (p.affineApproximation xBar) L xBar) ''
          problem.ambientSet).Nonempty := by
      rcases problem.ambient_nonempty with ⟨x, hx⟩
      exact ⟨_, ⟨x, hx, rfl⟩⟩
    refine le_csInf hupper_nonempty ?_
    rintro _ ⟨x, hx, rfl⟩
    have hobj_le : sInf (p '' problem.ambientSet) ≤ p x := by
      exact csInf_le p.objective_image_bddBelow ⟨x, hx, rfl⟩
    have hupper :
        p x ≤ quadraticallyRegularizedObjective (p.affineApproximation xBar) L xBar x := by
      -- Use the canonical upper quadratic bound for the fixed-`t` max-type owner.
      simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation,
        SmoothMinimaxProblem.objective] using
        (maxTypeObjective_quadratic_bounds_of_components_mem
          p.components μ L p.components_mem x xBar).2
    simpa
      [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue,
        SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem_feasibleSet,
        p]
      using le_trans hobj_le hupper
  -- First compare the constrained value with the `L`-model value at the reference parameter.
  have hmodelValueL_pos : 0 < modelValue tBar xBar L := by
    exact lt_of_lt_of_le hvalue_pos hparametric_upper
  have hfactor_pos : 0 < 1 - κ := by
    linarith
  -- The source comparison then forces positivity of the `μ`-model value at the same point.
  have hreferenceModel_pos : 0 < modelValue tBar xBar μ := by
    have hscaled_pos : 0 < (1 - κ) * modelValue tBar xBar L := by
      exact mul_pos hfactor_pos hmodelValueL_pos
    exact lt_of_lt_of_le hscaled_pos hcomparison
  -- The selected update is a root above `tBar`; equality would contradict the derived positivity.
  have hroot_mem :=
    problem.regularizedModelValueRoot_mem_of_convexOn xBar tBar hmu_convex hmu_root
  have hroot_ne : tBar ≠ t★[problem; xBar](tBar) := by
    intro hroot_eq
    have hzero_at_tBar : modelValue tBar xBar μ = 0 := by
      exact (congrArg (fun s ↦ modelValue s xBar μ) hroot_eq).trans hroot_mem.2
    exact (ne_of_gt hreferenceModel_pos) hzero_at_tBar
  exact lt_of_le_of_ne hroot_mem.1 hroot_ne

/-- Helper for Lemma 2.24: the quadratically regularized affine model of the fixed-`t` parametric
problem is bounded below on the ambient set when the regularization parameter is positive. -/
private theorem parametric_regularizedAffineApproximation_image_bddBelow
    (t : ℝ) (xBar : E) (γ : NNRealˣ) :
    BddBelow
      ((quadraticallyRegularizedObjective
          ((parametricProblem t).affineApproximation xBar)
          γ
          xBar) '' problem.ambientSet) := by
  let p := parametricProblem t
  let i0 : Fin (m + 1) := 0
  let g0 : E := gradient (p.components i0) xBar
  let c : ℝ := p.components i0 xBar - ‖g0‖ ^ (2 : ℕ) / (2 * (γ : ℝ))
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  refine ⟨c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hcomponent_le :
      firstOrderTaylorModelAt (p.components i0) xBar x ≤
        p.affineApproximation xBar x := by
    -- One Taylor component is bounded above by the finite maximum defining the affine model.
    rw
      [SmoothMinimaxProblem.affineApproximation,
        maxTypeAffineApproximation_apply_firstOrderTaylorModelAt]
    exact Finset.le_sup' (fun j : Fin (m + 1) ↦ firstOrderTaylorModelAt (p.components j) xBar x)
      (by simp)
  have hquad :
      -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) ≤
        inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
    exact SmoothMinimaxProblem.inner_add_quadratic_lower_bound (γ : ℝ) hγ g0 (x - xBar)
  have hbase_raw :
      p.components i0 xBar + -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) ≤
        p.components i0 xBar +
          (inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ)) := by
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hquad (p.components i0 xBar)
  have hbase :
      c ≤
        p.components i0 xBar +
          inner ℝ g0 (x - xBar) +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
    -- Normalize the completed-square lower bound before comparing with the affine model.
    calc
      c = p.components i0 xBar + -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) := by
        dsimp [c]
        ring
      _ ≤
          p.components i0 xBar +
            (inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ)) := hbase_raw
      _ =
          p.components i0 xBar +
            inner ℝ g0 (x - xBar) +
              ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
                ring
  calc
    c ≤
        p.components i0 xBar +
          inner ℝ g0 (x - xBar) +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := hbase
    _ =
        firstOrderTaylorModelAt (p.components i0) xBar x +
          ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
            simp [g0]
    _ ≤
        p.affineApproximation xBar x +
          ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right hcomponent_le (((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ))
    _ =
        quadraticallyRegularizedObjective (p.affineApproximation xBar) γ xBar x := by
          simp [quadraticallyRegularizedObjective_apply]

/-- Helper for Lemma 2.24: the constrained optimal value of the fixed-`t` parametric problem is
bounded above by the `L`-regularized affine model value at `xBar`. -/
private theorem parametricProblemOptimalValue_le_upperRegularizedModelValue
    (t : ℝ) (xBar : E) :
    parametricOptimalValue t ≤ modelValue t xBar L := by
  let p := parametricProblem t
  have hupper_nonempty :
      ((quadraticallyRegularizedObjective (p.affineApproximation xBar) L xBar) ''
        problem.ambientSet).Nonempty := by
    rcases problem.ambient_nonempty with ⟨x, hx⟩
    exact ⟨_, ⟨x, hx, rfl⟩⟩
  refine le_csInf hupper_nonempty ?_
  rintro _ ⟨x, hx, rfl⟩
  have hobj_le : sInf (p '' problem.ambientSet) ≤ p x := by
    exact csInf_le p.objective_image_bddBelow ⟨x, hx, rfl⟩
  have hupper :
      p x ≤ quadraticallyRegularizedObjective (p.affineApproximation xBar) L xBar x := by
    -- Use the canonical upper quadratic bound for the fixed-`t` max-type owner.
    simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation,
      SmoothMinimaxProblem.objective] using
      (maxTypeObjective_quadratic_bounds_of_components_mem
        p.components μ L p.components_mem x xBar).2
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue,
    SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem_feasibleSet, p]
    using le_trans hobj_le hupper

/-- Helper for Lemma 2.24: the `μ`-regularized affine model value of the fixed-`t` parametric
problem is bounded above by its constrained optimal value. -/
private theorem lowerRegularizedModelValue_le_parametricProblemOptimalValue
    (t : ℝ) (xBar : E) :
    modelValue t xBar μ ≤ parametricOptimalValue t := by
  let p := parametricProblem t
  let i0 : Fin (m + 1) := 0
  have hμ_pos : 0 < μ := by
    exact (mem_S11_iff.mp (p.components_mem i0)).mu_pos
  let γμ : NNRealˣ :=
    Units.mk0 (Real.toNNReal μ) (ne_of_gt (by rwa [Real.toNNReal_pos]))
  have hγμ : (γμ : ℝ) = μ := by
    simp [γμ, Real.toNNReal_of_nonneg hμ_pos.le]
  have hobjective_nonempty : (p '' problem.ambientSet).Nonempty := by
    rcases problem.ambient_nonempty with ⟨x, hx⟩
    exact ⟨p x, ⟨x, hx, rfl⟩⟩
  have hmodel_bdd :
      BddBelow
        ((quadraticallyRegularizedObjective (p.affineApproximation xBar) μ xBar) ''
          problem.ambientSet) := by
    simpa [hγμ] using
      parametric_regularizedAffineApproximation_image_bddBelow
        (problem := problem) t xBar γμ
  refine le_csInf hobjective_nonempty ?_
  rintro _ ⟨x, hx, rfl⟩
  have hmodel_le :
      sInf ((quadraticallyRegularizedObjective (p.affineApproximation xBar) μ xBar) ''
        problem.ambientSet) ≤
        quadraticallyRegularizedObjective (p.affineApproximation xBar) μ xBar x := by
    exact csInf_le hmodel_bdd ⟨x, hx, rfl⟩
  have hlower :
      quadraticallyRegularizedObjective (p.affineApproximation xBar) μ xBar x ≤ p x := by
    -- Use the canonical lower quadratic bound for the fixed-`t` max-type owner.
    simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation,
      SmoothMinimaxProblem.objective, ge_iff_le] using
      (maxTypeObjective_quadratic_bounds_of_components_mem
        p.components μ L p.components_mem x xBar).1
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue,
    SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem_feasibleSet, p]
    using le_trans hmodel_le hlower

/-- Helper for Lemma 2.24: a convex scalar function lies above the secant line joining a point to
a later comparison point when evaluated to the left of that point. -/
private theorem convex_secant_lower_bound_left_shift
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {t0 t1 t2 : ℝ}
    (ht0t1 : t0 < t1) (ht1t2 : t1 < t2) :
    f t0 ≥ f t1 + ((t1 - t0) / (t2 - t1)) * (f t1 - f t2) := by
  let Δ : ℝ := t1 - t0
  have hΔ_pos : 0 < Δ := by
    dsimp [Δ]
    exact sub_pos.mpr ht0t1
  have hshift : t1 - Δ = t0 := by
    dsimp [Δ]
    ring
  -- Compare the left secant slope with the right secant slope through `ConvexOn.secant_mono`.
  have hslope :
      (f t1 - f (t1 - Δ)) / Δ ≤ (f t2 - f t1) / (t2 - t1) := by
    have hsecant :=
      hf.secant_mono
        (a := t1)
        (x := t1 - Δ)
        (y := t2)
        (by simp)
        (by simp [hshift])
        (by simp)
        (by linarith)
        ht1t2.ne'
        (by linarith)
    convert hsecant using 1
    ring_nf
  have hstep :
      f t1 - f (t1 - Δ) ≤ ((f t2 - f t1) / (t2 - t1)) * Δ := by
    exact (div_le_iff₀ hΔ_pos).1 hslope
  have hbound :
      f t1 - f (t1 - Δ) ≤ (Δ / (t2 - t1)) * (f t2 - f t1) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  -- Rearranging the secant estimate gives the claimed lower bound.
  have hbound' :
      f t1 - f t0 ≤ ((t1 - t0) / (t2 - t1)) * (f t2 - f t1) := by
    simpa [Δ, hshift] using hbound
  linarith

/-- Helper for Lemma 2.24: convexity of the `μ`-model value before the selected root yields the
secant lower estimate used in the source proof, with the denominator weakened from
`t★[problem; xBar](tBar) - tBar` to `t★[problem; xBar](tBar) - t`. -/
private theorem modelValue_secant_lower_before_regularized_root
    {t : ℝ}
    (ht_lt_tBar : t < tBar)
    (hroot_gt : tBar < t★[problem; xBar](tBar))
    (hroot_zero : modelValue (t★[problem; xBar](tBar)) xBar μ = 0)
    (hreferenceModel_nonneg : 0 ≤ modelValue tBar xBar μ)
    (hmu_convex : ConvexOn ℝ Set.univ (fun τ ↦ modelValue τ xBar μ)) :
    modelValue t xBar μ ≥
      modelValue tBar xBar μ +
        ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ := by
  have hstrong_secant :
      modelValue t xBar μ ≥
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - tBar)) *
            (modelValue tBar xBar μ - modelValue (t★[problem; xBar](tBar)) xBar μ) := by
    simpa using
      convex_secant_lower_bound_left_shift
        (f := fun τ ↦ modelValue τ xBar μ)
        hmu_convex
        ht_lt_tBar
        hroot_gt
  have hsecant_at_zero :
      modelValue t xBar μ ≥
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - tBar)) * modelValue tBar xBar μ := by
    simpa [hroot_zero] using hstrong_secant
  have hroot_gap_pos : 0 < t★[problem; xBar](tBar) - tBar := by
    linarith
  have hroot_gap_le :
      t★[problem; xBar](tBar) - tBar ≤ t★[problem; xBar](tBar) - t := by
    linarith
  have hcoefficient_le :
      (tBar - t) / (t★[problem; xBar](tBar) - t) ≤
        (tBar - t) / (t★[problem; xBar](tBar) - tBar) := by
    exact div_le_div_of_nonneg_left
      (sub_nonneg.mpr ht_lt_tBar.le)
      hroot_gap_pos
      hroot_gap_le
  -- A larger secant coefficient preserves the bound because the reference value is nonnegative.
  have hscaled_le :
      ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ ≤
        ((tBar - t) / (t★[problem; xBar](tBar) - tBar)) * modelValue tBar xBar μ := by
    exact mul_le_mul_of_nonneg_right hcoefficient_le hreferenceModel_nonneg
  have hweak_rhs_le :
      modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ ≤
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - tBar)) * modelValue tBar xBar μ := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hscaled_le (modelValue tBar xBar μ)
  exact le_trans hweak_rhs_le hsecant_at_zero

/-- Internal helper for Lemma 2.24 (2): once the owner value function satisfies the displayed
secant lower estimate at `t` and the reference `μ`-model value is nonnegative, the owner
`L`-model value at `(t, x)` is bounded below by the same square-root expression as in the source
statement. -/
-- Proof sketch: use
-- `problem.parametricProblemOptimalValue_le_upperRegularizedModelValue t x` to bound
-- `parametricOptimalValue t` above by the owner `L`-model value at `(t, x)`. Combine this with
-- the secant lower estimate for `parametricOptimalValue t`, factor the right-hand side as
-- `(1 + τ) * modelValue tBar xBar μ`, use the assumed nonnegativity of
-- `modelValue tBar xBar μ` together with the elementary inequality
-- `1 + τ ≥ 2 * sqrt τ` for `τ = (tBar - t) / (t★[problem; xBar](tBar) - t)`, and then apply
-- `hcomparison`.
private theorem local_value_lower_bound_of_secant_lower
    {x : E} {t : ℝ}
    (ht_lt_tBar : t < tBar)
    (hroot_gt : tBar < t★[problem; xBar](tBar))
    (hcomparison : modelValue tBar xBar μ ≥ (1 - κ) * modelValue tBar xBar L)
    (hreferenceModel_nonneg : 0 ≤ modelValue tBar xBar μ)
    (hsecant_lower :
      parametricOptimalValue t ≥
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ) :
    modelValue t x L ≥
      2 * (1 - κ) * modelValue tBar xBar L *
        Real.sqrt ((tBar - t) / (t★[problem; xBar](tBar) - t)) := by
  let τ : ℝ := (tBar - t) / (t★[problem; xBar](tBar) - t)
  have hroot_gap_pos : 0 < t★[problem; xBar](tBar) - t := by
    linarith
  have hτ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    exact div_nonneg (sub_nonneg.mpr ht_lt_tBar.le) hroot_gap_pos.le
  -- The secant estimate and the upper comparison bridge bound the `L`-model from below by
  -- `(1 + τ) * modelValue tBar xBar μ`.
  have hvalue_ge_factor :
      modelValue t x L ≥ (1 + τ) * modelValue tBar xBar μ := by
    calc
      modelValue t x L ≥ parametricOptimalValue t := by
        exact parametricProblemOptimalValue_le_upperRegularizedModelValue
          (problem := problem) t x
      _ ≥ modelValue tBar xBar μ + τ * modelValue tBar xBar μ := by
        simpa [τ] using hsecant_lower
      _ = (1 + τ) * modelValue tBar xBar μ := by
        ring
  -- Replace the factor `1 + τ` by the source lower bound `2 * sqrt τ`.
  have hsqrt_step : 2 * Real.sqrt τ ≤ 1 + τ := by
    have hsquare_nonneg : 0 ≤ (Real.sqrt τ - 1) ^ (2 : ℕ) := by
      exact sq_nonneg (Real.sqrt τ - 1)
    nlinarith [hsquare_nonneg, Real.sq_sqrt hτ_nonneg]
  have hsqrt_factor_le :
      (2 * Real.sqrt τ) * modelValue tBar xBar μ ≤
        (1 + τ) * modelValue tBar xBar μ := by
    exact mul_le_mul_of_nonneg_right hsqrt_step hreferenceModel_nonneg
  have hvalue_ge_sqrt_factor :
      modelValue t x L ≥ (2 * Real.sqrt τ) * modelValue tBar xBar μ := by
    exact le_trans hsqrt_factor_le hvalue_ge_factor
  have htwo_sqrt_nonneg : 0 ≤ 2 * Real.sqrt τ := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
    nlinarith
  -- Finally transport the reference-point comparison through the nonnegative factor `2 * sqrt τ`.
  have hcomparison_scaled :
      (2 * Real.sqrt τ) * ((1 - κ) * modelValue tBar xBar L) ≤
        (2 * Real.sqrt τ) * modelValue tBar xBar μ := by
    exact mul_le_mul_of_nonneg_left hcomparison htwo_sqrt_nonneg
  have hfinal :
      (2 * Real.sqrt τ) * ((1 - κ) * modelValue tBar xBar L) ≤
        modelValue t x L := by
    exact le_trans hcomparison_scaled hvalue_ge_sqrt_factor
  simpa [τ, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- Lemma 2.24 (2): if the owner `μ`-model value at `(tBar, xBar)` dominates `(1 - κ)` times the
owner `L`-model value, if the owner constrained value at `tBar` is positive, if
`τ ↦ modelValue τ xBar μ` is convex and has a root not smaller than `tBar`, and if `t < tBar`,
then for every base point `x ∈ E` the owner `L`-model value at `(t, x)` is bounded below by the
stated square-root expression involving the selected least root `t★[problem; xBar](tBar)`. The
textbook statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: first apply `referenceParameter_lt_regularizedModelValueRoot` to obtain
-- `tBar < t★[problem; xBar](tBar)` and then use
-- `problem.regularizedModelValueRoot_mem_of_convexOn xBar tBar` to identify the secant endpoint
-- as an actual zero of `τ ↦ modelValue τ xBar μ`. The positivity of
-- `parametricOptimalValue tBar` together with
-- `problem.parametricProblemOptimalValue_le_upperRegularizedModelValue tBar xBar` implies
-- positivity of `modelValue tBar xBar L`, and then `hcomparison` yields positivity of
-- `modelValue tBar xBar μ`. Then use the local helper
-- `modelValue_secant_lower_before_regularized_root` to extract the source secant estimate for
-- `τ ↦ modelValue τ xBar μ` between `t`, `tBar`, and `t★[problem; xBar](tBar)`, bound the
-- left-hand side by `parametricOptimalValue t` via
-- `problem.lowerRegularizedModelValue_le_parametricProblemOptimalValue t xBar`, and conclude with
-- the internal secant-lower helper using the derived nonnegativity of `modelValue tBar xBar μ`.
theorem local_value_lower_bound_before_reference_parameter
    {x : E} {t : ℝ}
    (hκ : κ < 1)
    (hcomparison : modelValue tBar xBar μ ≥ (1 - κ) * modelValue tBar xBar L)
    (hvalue_pos : 0 < parametricOptimalValue tBar)
    (hmu_convex : ConvexOn ℝ Set.univ (fun τ ↦ modelValue τ xBar μ))
    (hmu_root : ∃ τ : ℝ, tBar ≤ τ ∧ modelValue τ xBar μ = 0)
    (ht_lt_tBar : t < tBar) :
    modelValue t x L ≥
      2 * (1 - κ) * modelValue tBar xBar L *
        Real.sqrt ((tBar - t) / (t★[problem; xBar](tBar) - t)) := by
  -- First show that the selected root lies strictly to the right of the reference parameter.
  have hroot_gt :=
    referenceParameter_lt_regularizedModelValueRoot
      (problem := problem)
      hκ
      hcomparison
      hvalue_pos
      hmu_convex
      hmu_root
  have hroot_mem :=
    problem.regularizedModelValueRoot_mem_of_convexOn xBar tBar hmu_convex hmu_root
  -- Positivity of the constrained value at `tBar` propagates to both local model values there.
  have hmodelValueL_pos : 0 < modelValue tBar xBar L := by
    exact lt_of_lt_of_le hvalue_pos
      (parametricProblemOptimalValue_le_upperRegularizedModelValue
        (problem := problem) tBar xBar)
  have hfactor_pos : 0 < 1 - κ := by
    linarith
  have hreferenceModel_pos : 0 < modelValue tBar xBar μ := by
    have hscaled_pos : 0 < (1 - κ) * modelValue tBar xBar L := by
      exact mul_pos hfactor_pos hmodelValueL_pos
    exact lt_of_lt_of_le hscaled_pos hcomparison
  -- Convexity of the `μ`-model value gives the secant lower bound before the selected root.
  have hmodel_secant :
      modelValue t xBar μ ≥
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ := by
    exact modelValue_secant_lower_before_regularized_root
      (problem := problem)
      ht_lt_tBar
      hroot_gt
      hroot_mem.2
      hreferenceModel_pos.le
      hmu_convex
  have hparametric_secant :
      parametricOptimalValue t ≥
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ := by
    exact le_trans hmodel_secant
      (lowerRegularizedModelValue_le_parametricProblemOptimalValue
        (problem := problem) t xBar)
  exact local_value_lower_bound_of_secant_lower
    (problem := problem)
    (x := x)
    ht_lt_tBar
    hroot_gt
    hcomparison
    hreferenceModel_pos.le
    hparametric_secant

end
