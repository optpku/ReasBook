/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable {m : ℕ} {μ L : ℝ}

open SmoothMinimaxProblem ConstrainedMinimizationMethod

section

variable {problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L}

local notation "parametricProblem" => problem.toParametricSmoothMinimaxProblem
local notation "modelValue" => problem.regularizedModelValue

variable
    {κ t0 tStar : ℝ} {x0 : problem.ambientSet} {hL : 0 < L}
    {hStep1a : ∀ xBar : problem.ambientSet, ∀ t : ℝ, ∃ j, step1aAt problem κ xBar t hL j}

local notation "xSeq" =>
  ConstrainedMinimizationMethod.x problem κ t0 x0 hL hStep1a

local notation "tSeq" =>
  ConstrainedMinimizationMethod.t problem κ t0 x0 hL hStep1a

local notation "stoppedSeq" =>
  ConstrainedMinimizationMethod.stoppedInternalIterate problem κ t0 x0 hL hStep1a

local notation "selectedSeq" =>
  ConstrainedMinimizationMethod.selectedInternalIterate problem κ t0 x0 hL hStep1a

local notation "stoppedResidual" =>
  fun k ↦ modelValue (tSeq k) (stoppedSeq k : E) L

local notation "selectedResidual" =>
  fun k ↦ modelValue (tSeq k) (selectedSeq k : E) L

local notation "valueFunctionAt(" t ")" =>
  sInf ((parametricProblem t) '' (SmoothMinimaxProblem.feasibleSet (parametricProblem t)))

local notation "upperModelAtSuccessor(" k ")" =>
  quadraticallyRegularizedObjective
    (SmoothMinimaxProblem.affineApproximation
      (parametricProblem (tSeq k))
      (selectedSeq k : E))
    L
    (selectedSeq k : E)
    (xSeq (k + 1) : E)

/-
Primary domain: geometric decay estimates for the selected regularized-model residual in the
Chapter 2 two-level constrained scheme.

Owner abstractions sampled before refining:
- `ConstrainedMinimizationMethod` from `Algorithm_2_11.lean`, the source-facing owner of
  Algorithm 2.11 with the textbook root update, the selected internal iterate, and the exact
  outer successor `x_{k+1}`;
- `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` from
  `Definition_2_47.lean`, which owns the fixed-`t` smooth minimax bridge;
- `SmoothMinimaxProblem.affineApproximation` from `Definition_2_38.lean`, the owner fixed-`t`
  affine model used in the regularized residual;
- `HasGeometricRateOfConvergence` and
  `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` from
  `Proposition_2_30.lean`, which set the chapter style for one-step contraction sequences.

The best owner abstraction is the pair consisting of the outer owner
`ConstrainedMinimizationMethod`, together with the scalar owner
`HasGeometricRateOfConvergence` applied to the normalized stopped-residual sequence
`k ↦ modelValue (tSeq k) (stoppedSeq k) L / sqrt (tSeq (k + 1) - tSeq k)`.
Primitive data already live in `ConstrainedMinimizationMethod`: the master parameters `t_k`, the
first stopping indices `j(k)`, the selected indices `j*(k)`, and the internal owner method at
each master step, under the explicit Step `1(a)` existence hypothesis `hStep1a`. The internal
iterates `x_{k,j}` are then the derived view
`ConstrainedMinimizationMethod.internalIterate ... k j`, while the fixed-`t` residuals
`f^*(t_k; x_{k,j}; γ)` are the derived owner expressions `modelValue ... γ`. This avoids
rebuilding the fixed-`t` max-type model entrywise from
`constrainedAuxiliaryComponents` in a parallel local API.

Source/core/bridge triage:
- source-facing: the displayed geometric estimate for the selected residual
  `f^*(t_k; x_{k,j^*(k)}; L)`;
- core/canonical: `ConstrainedMinimizationMethod` together with the owner fixed-`t` problem
  `problem.toParametricSmoothMinimaxProblem t` and the owner geometric-rate predicate on the
  normalized stopped-residual scalar sequence;
- bridge/view: the equality `selected_residual_eq_upperModel_at_successor`, which identifies the
  selected residual with the attained upper-model value at the exact successor, the derived
  attained-upper-model estimate `upperModel_at_successor_le_geometric_rate`, and
  `ConstrainedMinimizationMethod.selected_residual_le_stopped_residual`.
-/

section GeometricRate

local notation "geometricBound(" k ")" =>
  ((tStar - t0) / (1 - κ)) * ((1 / (2 * (1 - κ))) ^ k)

/- Lemma 2.25 will be proved below by first estimating the stopped residual and then transferring
that bound to the selected residual through the canonical prefix-minimization comparison. -/
-- Proof sketch: set
-- `δ_k =
--   stoppedResidual k /
--     Real.sqrt (tSeq (k + 1) - tSeq k)`.
-- The decay hypothesis is first repackaged as the owner statement
-- `HasGeometricRateOfConvergence δ (1 - (2 * (1 - κ))⁻¹) δ_0`, hence
-- `δ_k ≤ (1 / (2 * (1 - κ))) ^ k * δ_0`. Use the initial `μ`-step bound together with the
-- comparison between the initial `L`- and `μ`-model values to control `δ_0`, then use the
-- uniform step-size estimate to bound the remaining square-root factor. Then transfer the
-- stopped-residual estimate to the selected residual via
-- `ConstrainedMinimizationMethod.selected_residual_le_stopped_residual`.
/-- Helper for Lemma 2.25: the normalized stopped residuals satisfy the textbook geometric decay
with factor `1 / (2 * (1 - κ))`. -/
-- Proof sketch: divide the displayed one-step contraction by the positive scalar
-- `2 * (1 - κ)`, then iterate the resulting scalar recurrence by induction.
lemma normalized_stopped_residual_le_geometric
    (hκ : κ < 1 / 2)
    (hdecay :
      ∀ k : ℕ,
        2 * (1 - κ) *
            (stoppedResidual (k + 1) /
              Real.sqrt (tSeq (k + 2) - tSeq (k + 1))) ≤
          stoppedResidual k / Real.sqrt (tSeq (k + 1) - tSeq k))
    (k : ℕ) :
    stoppedResidual k / Real.sqrt (tSeq (k + 1) - tSeq k) ≤
      ((1 / (2 * (1 - κ))) ^ k) *
        (stoppedResidual 0 / Real.sqrt (tSeq 1 - t0)) := by
  let δ : ℕ → ℝ :=
    fun n ↦ stoppedResidual n / Real.sqrt (tSeq (n + 1) - tSeq n)
  have hone_sub_kappa_pos : 0 < 1 - κ := by
    linarith
  have hfactor_pos : 0 < 2 * (1 - κ) := by
    positivity
  have hbeta_nonneg : 0 ≤ 1 / (2 * (1 - κ)) := by
    positivity
  have hstep :
      ∀ n : ℕ, δ (n + 1) ≤ (1 / (2 * (1 - κ))) * δ n := by
    intro n
    have hstep' :
        δ (n + 1) ≤ δ n / (2 * (1 - κ)) := by
      exact (le_div_iff₀ hfactor_pos).2 (by simpa [δ, mul_comm, mul_left_comm, mul_assoc] using hdecay n)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hstep'
  have hgeom : ∀ n : ℕ, δ n ≤ ((1 / (2 * (1 - κ))) ^ n) * δ 0 := by
    intro n
    induction n with
    | zero =>
        simp [δ]
    | succ n ihn =>
        calc
          δ (n + 1) ≤ (1 / (2 * (1 - κ))) * δ n := hstep n
          _ ≤ (1 / (2 * (1 - κ))) * (((1 / (2 * (1 - κ))) ^ n) * δ 0) := by
            gcongr
          _ = ((1 / (2 * (1 - κ))) ^ (n + 1)) * δ 0 := by
            rw [pow_succ]
            ring
  simpa [δ] using hgeom k

/-- Helper for Lemma 2.25: an attained minimum of the constrained regularized affine model
realizes the corresponding model value. -/
-- Proof sketch: convert the `IsMinOn` witness into an `IsGLB` statement for the image of the
-- upper model on `problem.ambientSet`, then identify the defining real infimum with that attained
-- minimum.
lemma regularizedModelValue_eq_of_isMinOn
    {τ γ : ℝ} {xBar xPlus : E}
    (hxPlus : xPlus ∈ problem.ambientSet)
    (hmin :
      IsMinOn
        (quadraticallyRegularizedObjective
          ((parametricProblem τ).affineApproximation xBar)
          γ
          xBar)
        problem.ambientSet
        xPlus) :
    modelValue τ xBar γ =
      quadraticallyRegularizedObjective
        ((parametricProblem τ).affineApproximation xBar)
        γ
        xBar
        xPlus := by
  let upperModel : E → ℝ :=
    quadraticallyRegularizedObjective
      ((parametricProblem τ).affineApproximation xBar)
      γ
      xBar
  -- The minimizing point realizes the exact infimum of the upper model over the ambient set.
  have hglb : IsGLB (upperModel '' problem.ambientSet) (upperModel xPlus) :=
    hmin.isGLB hxPlus
  rw [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue]
  simpa [upperModel] using hglb.csInf_eq ⟨upperModel xPlus, ⟨xPlus, hxPlus, rfl⟩⟩

/-- Helper for Lemma 2.25: increasing the scalar parameter can only decrease the affine
approximation of the fixed-`t` bridge problem. -/
-- Proof sketch: expand the finite maximum defining the affine approximation. The zero component
-- drops by exactly `Δ`, while every successor component is unchanged, so each component at
-- `t + Δ` is bounded above by some component at `t`.
lemma parametric_affine_approximation_shift_le
    (xBar x : E) {t Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    ((parametricProblem (t + Δ)).affineApproximation xBar) x ≤
      ((parametricProblem t).affineApproximation xBar) x := by
  rw [SmoothMinimaxProblem.affineApproximation, SmoothMinimaxProblem.affineApproximation]
  rw [maxTypeAffineApproximation_apply_firstOrderTaylorModelAt]
  rw [maxTypeAffineApproximation_apply_firstOrderTaylorModelAt]
  refine Finset.sup'_le _ _ ?_
  intro j hj
  cases j using Fin.cases with
  | zero =>
      have hzero :
          firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem (t + Δ)).components 0)
              xBar
              x =
            firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem t).components 0)
              xBar
              x -
              Δ := by
        simp [SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem,
          LagrangianProblem.constrainedAuxiliaryComponents, gradient, sub_eq_add_neg, add_assoc,
          add_left_comm, add_comm]
      rw [hzero]
      refine le_trans (sub_le_self _ hΔ) ?_
      simpa using
        (Finset.le_sup'
          (s := Finset.univ)
          (f := fun i : Fin (m + 1) ↦
            firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem t).components i)
              xBar
              x)
          (by simp : (0 : Fin (m + 1)) ∈ Finset.univ))
  | succ i =>
      have hsucc :
          firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem (t + Δ)).components i.succ)
              xBar
              x =
            firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem t).components i.succ)
              xBar
              x := by
        simp [SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem,
          LagrangianProblem.constrainedAuxiliaryComponents]
      rw [hsucc]
      simpa using
        (Finset.le_sup'
          (s := Finset.univ)
          (f := fun j : Fin (m + 1) ↦
            firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem t).components j)
              xBar
              x)
          (by simp : i.succ ∈ Finset.univ))

/-- Helper for Lemma 2.25: increasing the scalar parameter lowers the affine approximation by at
most the same amount. -/
-- Proof sketch: expand the finite maximum again. The zero component changes by exactly `Δ`, while
-- each successor component stays fixed and so automatically satisfies the weaker shifted bound.
lemma parametric_affine_approximation_sub_le_shift
    (xBar x : E) {t Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    ((parametricProblem t).affineApproximation xBar) x - Δ ≤
      ((parametricProblem (t + Δ)).affineApproximation xBar) x := by
  rw [SmoothMinimaxProblem.affineApproximation, SmoothMinimaxProblem.affineApproximation]
  rw [maxTypeAffineApproximation_apply_firstOrderTaylorModelAt]
  rw [maxTypeAffineApproximation_apply_firstOrderTaylorModelAt]
  rw [sub_le_iff_le_add]
  refine Finset.sup'_le _ _ ?_
  intro j hj
  cases j using Fin.cases with
  | zero =>
      have hzero :
          firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem (t + Δ)).components 0)
              xBar
              x =
            firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem t).components 0)
              xBar
              x -
              Δ := by
        simp [SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem,
          LagrangianProblem.constrainedAuxiliaryComponents, gradient, sub_eq_add_neg, add_assoc,
          add_left_comm, add_comm]
      have hle0 :
          firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem (t + Δ)).components 0)
              xBar
              x ≤
            Finset.univ.sup' Finset.univ_nonempty
              (fun j : Fin (m + 1) ↦
                firstOrderTaylorModelAt
                  ((problem.toParametricSmoothMinimaxProblem (t + Δ)).components j)
                  xBar
                  x) := by
        simpa using
          (Finset.le_sup'
            (s := Finset.univ)
            (f := fun j : Fin (m + 1) ↦
              firstOrderTaylorModelAt
                ((problem.toParametricSmoothMinimaxProblem (t + Δ)).components j)
                xBar
                x)
            (by simp : (0 : Fin (m + 1)) ∈ Finset.univ))
      have hle0' := add_le_add_right hle0 Δ
      rw [hzero] at hle0'
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hle0'
  | succ i =>
      have hsucc :
          firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem t).components i.succ)
              xBar
              x =
            firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem (t + Δ)).components i.succ)
              xBar
              x := by
        simp [SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem,
          LagrangianProblem.constrainedAuxiliaryComponents]
      rw [hsucc]
      have hle :
          firstOrderTaylorModelAt
              ((problem.toParametricSmoothMinimaxProblem (t + Δ)).components i.succ)
              xBar
              x ≤
            Finset.univ.sup' Finset.univ_nonempty
              (fun j : Fin (m + 1) ↦
                firstOrderTaylorModelAt
                  ((problem.toParametricSmoothMinimaxProblem (t + Δ)).components j)
                  xBar
                  x) := by
        simpa using
          (Finset.le_sup'
            (s := Finset.univ)
            (f := fun j : Fin (m + 1) ↦
              firstOrderTaylorModelAt
                ((problem.toParametricSmoothMinimaxProblem (t + Δ)).components j)
                xBar
                x)
            (by simp : i.succ ∈ Finset.univ))
      linarith

/-- Helper for Lemma 2.25: increasing the scalar parameter can only decrease the regularized upper
model at a fixed evaluation point. -/
-- Proof sketch: keep the quadratic regularization term unchanged and invoke the affine-model
-- shift comparison proved just above.
lemma regularized_upper_model_shift_le
    (xBar x : E) {t Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    quadraticallyRegularizedObjective
        ((parametricProblem (t + Δ)).affineApproximation xBar)
        μ
        xBar
        x ≤
      quadraticallyRegularizedObjective
        ((parametricProblem t).affineApproximation xBar)
        μ
        xBar
        x := by
  rw [quadraticallyRegularizedObjective_apply, quadraticallyRegularizedObjective_apply]
  simpa [add_assoc, add_left_comm, add_comm] using
    add_le_add_right
      (parametric_affine_approximation_shift_le
        (problem := problem)
        (xBar := xBar)
        (x := x)
        (t := t)
        (Δ := Δ)
        hΔ)
      ((μ / 2) * ‖x - xBar‖ ^ (2 : ℕ))

/-- Helper for Lemma 2.25: increasing the scalar parameter lowers the regularized upper model by
at most the same amount. -/
-- Proof sketch: as in the affine case, the quadratic term is unchanged, so the shifted lower
-- bound follows by adding that common quadratic term to the affine comparison.
lemma regularized_upper_model_sub_le_shift
    (xBar x : E) {t Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    quadraticallyRegularizedObjective
        ((parametricProblem t).affineApproximation xBar)
        μ
        xBar
        x -
        Δ ≤
      quadraticallyRegularizedObjective
        ((parametricProblem (t + Δ)).affineApproximation xBar)
        μ
        xBar
        x := by
  rw [quadraticallyRegularizedObjective_apply, quadraticallyRegularizedObjective_apply]
  linarith [parametric_affine_approximation_sub_le_shift
    (problem := problem)
    (xBar := xBar)
    (x := x)
    (t := t)
    (Δ := Δ)
    hΔ]

/-- Helper for Lemma 2.25: the `μ`-model value is monotone nonincreasing in the scalar
parameter. -/
-- Proof sketch: realize the two model values at their exact constrained minimizers and compare
-- the two attained upper-model values by the pointwise shift inequality.
lemma regularizedModelValue_shift_le
    (xBar : E) {t Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    modelValue (t + Δ) xBar μ ≤ modelValue t xBar μ := by
  have hμ_pos : 0 < μ := problem.objective_mem.mu_pos
  let γμ : NNRealˣ :=
    Units.mk0 (Real.toNNReal μ) (ne_of_gt (by rwa [Real.toNNReal_pos]))
  let x_t : E := problem.constrainedGradientMapping t xBar γμ
  let x_tΔ : E := problem.constrainedGradientMapping (t + Δ) xBar γμ
  have hgamma_mu : (γμ : ℝ) = μ := by
    simp [γμ, Real.toNNReal_of_nonneg hμ_pos.le]
  have hx_t : x_t ∈ problem.ambientSet := by
    simpa [x_t] using problem.constrainedGradientMapping_mem t xBar γμ
  have hx_tΔ : x_tΔ ∈ problem.ambientSet := by
    simpa [x_tΔ] using problem.constrainedGradientMapping_mem (t + Δ) xBar γμ
  -- Realize both model values at their exact minimizing steps.
  have hmin_t :
      IsMinOn
        (quadraticallyRegularizedObjective
          ((parametricProblem t).affineApproximation xBar)
          μ
          xBar)
        problem.ambientSet
        x_t := by
    simpa [x_t, hgamma_mu] using problem.constrainedGradientMapping_isMinOn t xBar γμ
  have hmin_tΔ :
      IsMinOn
        (quadraticallyRegularizedObjective
          ((parametricProblem (t + Δ)).affineApproximation xBar)
          μ
          xBar)
        problem.ambientSet
        x_tΔ := by
    simpa [x_tΔ, hgamma_mu] using
      problem.constrainedGradientMapping_isMinOn (t + Δ) xBar γμ
  have hmodel_t :
      modelValue t xBar μ =
        quadraticallyRegularizedObjective
          ((parametricProblem t).affineApproximation xBar)
          μ
          xBar
          x_t :=
    regularizedModelValue_eq_of_isMinOn (problem := problem) hx_t hmin_t
  have hmodel_tΔ :
      modelValue (t + Δ) xBar μ =
        quadraticallyRegularizedObjective
          ((parametricProblem (t + Δ)).affineApproximation xBar)
          μ
          xBar
          x_tΔ :=
    regularizedModelValue_eq_of_isMinOn (problem := problem) hx_tΔ hmin_tΔ
  -- Compare the attained values by replacing the minimizing point at `t + Δ` with the one at `t`.
  rw [hmodel_tΔ, hmodel_t]
  have hcompare_tΔ :
      quadraticallyRegularizedObjective
          ((parametricProblem (t + Δ)).affineApproximation xBar)
          μ
          xBar
          x_tΔ ≤
        quadraticallyRegularizedObjective
          ((parametricProblem (t + Δ)).affineApproximation xBar)
          μ
          xBar
          x_t := by
    exact (isMinOn_iff.mp hmin_tΔ) x_t hx_t
  calc
    quadraticallyRegularizedObjective
        ((parametricProblem (t + Δ)).affineApproximation xBar)
        μ
        xBar
        x_tΔ ≤
      quadraticallyRegularizedObjective
        ((parametricProblem (t + Δ)).affineApproximation xBar)
        μ
        xBar
        x_t := hcompare_tΔ
    _ ≤
      quadraticallyRegularizedObjective
        ((parametricProblem t).affineApproximation xBar)
        μ
        xBar
        x_t :=
      regularized_upper_model_shift_le (problem := problem) xBar x_t hΔ

/-- Helper for Lemma 2.25: when the scalar parameter is increased by `Δ ≥ 0`, the `μ`-model
value can drop by at most `Δ`. -/
-- Proof sketch: realize the two model values at their exact minimizers, bound the earlier value
-- at the later minimizer, and then use the pointwise shifted lower estimate for the upper model.
lemma regularizedModelValue_sub_le_shift
    (xBar : E) {t Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    modelValue t xBar μ - Δ ≤ modelValue (t + Δ) xBar μ := by
  have hμ_pos : 0 < μ := problem.objective_mem.mu_pos
  let γμ : NNRealˣ :=
    Units.mk0 (Real.toNNReal μ) (ne_of_gt (by rwa [Real.toNNReal_pos]))
  let x_t : E := problem.constrainedGradientMapping t xBar γμ
  let x_tΔ : E := problem.constrainedGradientMapping (t + Δ) xBar γμ
  have hgamma_mu : (γμ : ℝ) = μ := by
    simp [γμ, Real.toNNReal_of_nonneg hμ_pos.le]
  have hx_t : x_t ∈ problem.ambientSet := by
    simpa [x_t] using problem.constrainedGradientMapping_mem t xBar γμ
  have hx_tΔ : x_tΔ ∈ problem.ambientSet := by
    simpa [x_tΔ] using problem.constrainedGradientMapping_mem (t + Δ) xBar γμ
  -- As above, rewrite both scalar values through their exact minimizers.
  have hmin_t :
      IsMinOn
        (quadraticallyRegularizedObjective
          ((parametricProblem t).affineApproximation xBar)
          μ
          xBar)
        problem.ambientSet
        x_t := by
    simpa [x_t, hgamma_mu] using problem.constrainedGradientMapping_isMinOn t xBar γμ
  have hmin_tΔ :
      IsMinOn
        (quadraticallyRegularizedObjective
          ((parametricProblem (t + Δ)).affineApproximation xBar)
          μ
          xBar)
        problem.ambientSet
        x_tΔ := by
    simpa [x_tΔ, hgamma_mu] using
      problem.constrainedGradientMapping_isMinOn (t + Δ) xBar γμ
  have hmodel_t :
      modelValue t xBar μ =
        quadraticallyRegularizedObjective
          ((parametricProblem t).affineApproximation xBar)
          μ
          xBar
          x_t :=
    regularizedModelValue_eq_of_isMinOn (problem := problem) hx_t hmin_t
  have hmodel_tΔ :
      modelValue (t + Δ) xBar μ =
        quadraticallyRegularizedObjective
          ((parametricProblem (t + Δ)).affineApproximation xBar)
          μ
          xBar
          x_tΔ :=
    regularizedModelValue_eq_of_isMinOn (problem := problem) hx_tΔ hmin_tΔ
  -- Bound the earlier attained value by evaluating the earlier model at the later minimizer.
  rw [hmodel_t, hmodel_tΔ]
  have hcompare_t :
      quadraticallyRegularizedObjective
          ((parametricProblem t).affineApproximation xBar)
          μ
          xBar
          x_t ≤
        quadraticallyRegularizedObjective
          ((parametricProblem t).affineApproximation xBar)
          μ
          xBar
          x_tΔ := by
    exact (isMinOn_iff.mp hmin_t) x_tΔ hx_tΔ
  calc
    quadraticallyRegularizedObjective
        ((parametricProblem t).affineApproximation xBar)
        μ
        xBar
        x_t -
        Δ ≤
      quadraticallyRegularizedObjective
        ((parametricProblem t).affineApproximation xBar)
        μ
        xBar
        x_tΔ -
        Δ := by
      gcongr
    _ ≤
      quadraticallyRegularizedObjective
        ((parametricProblem (t + Δ)).affineApproximation xBar)
        μ
        xBar
        x_tΔ :=
      regularized_upper_model_sub_le_shift (problem := problem) xBar x_tΔ hΔ

/-- Helper for Lemma 2.25: once one `μ`-root exists above the reference parameter, the textbook
update defined by `sInf` is itself a root and stays above the reference parameter. -/
-- Proof sketch: the root set is bounded below by the reference parameter, so its infimum is at
-- least `t`. The two model-value shift bounds then show that the scalar value at the infimum is
-- squeezed between `0` and every positive `ε`, hence must vanish.
lemma regularizedModelValueRoot_mem_of_exists_root
    (xBar : E) (t : ℝ)
    (hroot : ∃ τ : ℝ, t ≤ τ ∧ modelValue τ xBar μ = 0) :
    t ≤ problem.regularizedModelValueRoot xBar t ∧
      modelValue (problem.regularizedModelValueRoot xBar t) xBar μ = 0 := by
  let roots : Set ℝ := {τ : ℝ | t ≤ τ ∧ modelValue τ xBar μ = 0}
  have hroots_nonempty : roots.Nonempty := by
    rcases hroot with ⟨τ, hτ_ge, hτ_zero⟩
    exact ⟨τ, hτ_ge, hτ_zero⟩
  have hroots_bdd : BddBelow roots := ⟨t, fun _ hτ ↦ hτ.1⟩
  have hsInf_ge : t ≤ sInf roots := by
    exact le_csInf hroots_nonempty fun _ hτ ↦ hτ.1
  -- Any actual root above `sInf roots` forces the value at the infimum to be nonnegative.
  have hvalue_nonneg : 0 ≤ modelValue (sInf roots) xBar μ := by
    rcases hroot with ⟨τ, hτ_ge, hτ_zero⟩
    have hτ_mem : τ ∈ roots := ⟨hτ_ge, hτ_zero⟩
    have hsInf_le_tau : sInf roots ≤ τ := csInf_le hroots_bdd hτ_mem
    have hΔ_nonneg : 0 ≤ τ - sInf roots := sub_nonneg.mpr hsInf_le_tau
    have hshift :=
      regularizedModelValue_shift_le
        (problem := problem)
        (xBar := xBar)
        (t := sInf roots)
        (Δ := τ - sInf roots)
        hΔ_nonneg
    have hsum : sInf roots + (τ - sInf roots) = τ := by
      ring
    calc
      0 = modelValue τ xBar μ := by simpa [hτ_zero]
      _ = modelValue (sInf roots + (τ - sInf roots)) xBar μ := by rw [hsum]
      _ ≤ modelValue (sInf roots) xBar μ := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift
  -- Approximating the infimum by roots above it squeezes the value at `sInf roots` to zero.
  have hvalue_le_eps :
      ∀ ε : ℝ, 0 < ε → modelValue (sInf roots) xBar μ ≤ ε := by
    intro ε hε
    rcases exists_lt_of_csInf_lt hroots_nonempty (lt_add_of_pos_right (sInf roots) hε) with
      ⟨τ, hτ_mem, hτ_lt⟩
    have hsInf_le_tau : sInf roots ≤ τ := csInf_le hroots_bdd hτ_mem
    have hΔ_nonneg : 0 ≤ τ - sInf roots := sub_nonneg.mpr hsInf_le_tau
    have hshift :=
      regularizedModelValue_sub_le_shift
        (problem := problem)
        (xBar := xBar)
        (t := sInf roots)
        (Δ := τ - sInf roots)
        hΔ_nonneg
    have hsum : sInf roots + (τ - sInf roots) = τ := by
      ring
    have hbound : modelValue (sInf roots) xBar μ ≤ τ - sInf roots := by
      have hshift' :
          modelValue (sInf roots) xBar μ - (τ - sInf roots) ≤ modelValue τ xBar μ := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, hsum] using hshift
      linarith [hshift', hτ_mem.2]
    have hgap_lt : τ - sInf roots < ε := by
      linarith
    exact hbound.trans hgap_lt.le
  have hvalue_zero : modelValue (sInf roots) xBar μ = 0 := by
    by_contra hne
    have hpos : 0 < modelValue (sInf roots) xBar μ := lt_of_le_of_ne hvalue_nonneg (Ne.symm hne)
    have hhalf_pos : 0 < modelValue (sInf roots) xBar μ / 2 := by
      linarith
    have hhalf_le :=
      hvalue_le_eps (modelValue (sInf roots) xBar μ / 2) hhalf_pos
    linarith
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValueRoot, roots] using
    And.intro hsInf_ge hvalue_zero

/-- Helper for Lemma 2.25: if the `μ`-model value is nonnegative at the current parameter and
becomes nonpositive at some later parameter, then an exact `μ`-root exists above the current
parameter. -/
-- Proof sketch: take the infimum of the later nonpositive parameters. The shift estimate
-- `regularizedModelValue_sub_le_shift` shows the value at this infimum is at most any positive
-- `ε`, hence nonpositive. If it were negative, then either the infimum equals the reference
-- parameter, contradicting the assumed nonnegativity there, or one can shift slightly to the
-- left and remain nonpositive, contradicting the infimum property.
lemma regularizedModelValue_exists_root_of_nonneg_at_reference_of_nonpos_above
    (xBar : E) (t : ℝ)
    (hreference_nonneg : 0 ≤ modelValue t xBar μ)
    (hnonpos :
      ∃ τ : ℝ, t ≤ τ ∧ modelValue τ xBar μ ≤ 0) :
    ∃ τ : ℝ, t ≤ τ ∧ modelValue τ xBar μ = 0 := by
  let nonpos : Set ℝ := {τ : ℝ | t ≤ τ ∧ modelValue τ xBar μ ≤ 0}
  have hnonpos_nonempty : nonpos.Nonempty := by
    rcases hnonpos with ⟨τ, hτ_ge, hτ_nonpos⟩
    exact ⟨τ, hτ_ge, hτ_nonpos⟩
  have hnonpos_bdd : BddBelow nonpos := ⟨t, fun _ hτ ↦ hτ.1⟩
  have hsInf_ge : t ≤ sInf nonpos := by
    exact le_csInf hnonpos_nonempty fun _ hτ ↦ hτ.1
  -- Approximate the infimum from the right by nonpositive points to force nonpositivity there.
  have hvalue_le_eps :
      ∀ ε : ℝ, 0 < ε → modelValue (sInf nonpos) xBar μ ≤ ε := by
    intro ε hε
    rcases exists_lt_of_csInf_lt hnonpos_nonempty (lt_add_of_pos_right (sInf nonpos) hε) with
      ⟨τ, hτ_mem, hτ_lt⟩
    have hsInf_le_tau : sInf nonpos ≤ τ := csInf_le hnonpos_bdd hτ_mem
    have hΔ_nonneg : 0 ≤ τ - sInf nonpos := sub_nonneg.mpr hsInf_le_tau
    have hshift :=
      regularizedModelValue_sub_le_shift
        (problem := problem)
        (xBar := xBar)
        (t := sInf nonpos)
        (Δ := τ - sInf nonpos)
        hΔ_nonneg
    have hsum : sInf nonpos + (τ - sInf nonpos) = τ := by
      ring
    have hbound : modelValue (sInf nonpos) xBar μ ≤ τ - sInf nonpos := by
      have hshift' :
          modelValue (sInf nonpos) xBar μ - (τ - sInf nonpos) ≤ modelValue τ xBar μ := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, hsum] using hshift
      linarith [hshift', hτ_mem.2]
    have hgap_lt : τ - sInf nonpos < ε := by
      linarith
    exact hbound.trans hgap_lt.le
  have hvalue_nonpos : modelValue (sInf nonpos) xBar μ ≤ 0 := by
    by_contra hpos
    have hvalue_pos : 0 < modelValue (sInf nonpos) xBar μ := lt_of_not_ge hpos
    have hhalf_pos : 0 < modelValue (sInf nonpos) xBar μ / 2 := by
      linarith
    have hhalf_le :=
      hvalue_le_eps (modelValue (sInf nonpos) xBar μ / 2) hhalf_pos
    linarith
  -- A negative value at the infimum would let us move slightly left while staying nonpositive.
  have hvalue_nonneg : 0 ≤ modelValue (sInf nonpos) xBar μ := by
    by_contra hneg
    have hvalue_neg : modelValue (sInf nonpos) xBar μ < 0 := lt_of_not_ge hneg
    by_cases hsInf_eq_t : sInf nonpos = t
    · have hreference_nonpos : modelValue t xBar μ ≤ 0 := by
        simpa [hsInf_eq_t] using hvalue_nonpos
      have hnot_neg : ¬ modelValue t xBar μ < 0 := not_lt_of_ge hreference_nonneg
      exact hnot_neg (by simpa [hsInf_eq_t] using hvalue_neg)
    · have ht_lt_sInf : t < sInf nonpos := lt_of_le_of_ne hsInf_ge (Ne.symm hsInf_eq_t)
      let ε : ℝ :=
        min ((sInf nonpos - t) / 2) (-modelValue (sInf nonpos) xBar μ / 2)
      have hgap_half_pos : 0 < (sInf nonpos - t) / 2 := by
        have hgap_pos : 0 < sInf nonpos - t := sub_pos.mpr ht_lt_sInf
        linarith
      have hvalue_half_pos : 0 < -modelValue (sInf nonpos) xBar μ / 2 := by
        linarith
      have hε_pos : 0 < ε := by
        dsimp [ε]
        exact lt_min hgap_half_pos hvalue_half_pos
      have hε_lt_gap : ε < sInf nonpos - t := by
        have hε_le_gap_half : ε ≤ (sInf nonpos - t) / 2 := by
          dsimp [ε]
          exact min_le_left _ _
        linarith
      have hε_lt_neg_value : ε < -modelValue (sInf nonpos) xBar μ := by
        have hε_le_value_half : ε ≤ -modelValue (sInf nonpos) xBar μ / 2 := by
          dsimp [ε]
          exact min_le_right _ _
        linarith
      let σ : ℝ := sInf nonpos - ε
      have hσ_ge : t ≤ σ := by
        dsimp [σ]
        linarith
      have hσ_lt : σ < sInf nonpos := by
        dsimp [σ]
        linarith
      have hε_nonneg : 0 ≤ ε := hε_pos.le
      have hshift :=
        regularizedModelValue_sub_le_shift
          (problem := problem)
          (xBar := xBar)
          (t := σ)
          (Δ := ε)
          hε_nonneg
      have hσ_add : σ + ε = sInf nonpos := by
        dsimp [σ]
        ring
      have hσ_nonpos : modelValue σ xBar μ ≤ 0 := by
        have hshift' :
            modelValue σ xBar μ ≤ modelValue (sInf nonpos) xBar μ + ε := by
          have hbase :
              modelValue σ xBar μ - ε ≤ modelValue (sInf nonpos) xBar μ := by
            simpa [hσ_add] using hshift
          linarith
        linarith [hshift', hε_lt_neg_value]
      have hσ_mem : σ ∈ nonpos := by
        exact ⟨hσ_ge, hσ_nonpos⟩
      exact (not_le_of_gt hσ_lt) (csInf_le hnonpos_bdd hσ_mem)
  have hvalue_zero : modelValue (sInf nonpos) xBar μ = 0 := by
    exact le_antisymm hvalue_nonpos hvalue_nonneg
  exact ⟨sInf nonpos, hsInf_ge, hvalue_zero⟩

/-- Helper for Lemma 2.25: a sign change for the stopped `μ`-model value above `t_k` yields an
exact root above `t_k`. -/
-- Proof sketch: specialize the previous sign-change lemma to the stopped iterate at stage `k`.
lemma stopped_mu_root_exists_above_current_parameter
    (k : ℕ)
    (hreference_nonneg : 0 ≤ modelValue (tSeq k) (stoppedSeq k : E) μ)
    (hnonpos :
      ∃ τ : ℝ, tSeq k ≤ τ ∧ modelValue τ (stoppedSeq k : E) μ ≤ 0) :
    ∃ τ : ℝ, tSeq k ≤ τ ∧ modelValue τ (stoppedSeq k : E) μ = 0 := by
  exact
    regularizedModelValue_exists_root_of_nonneg_at_reference_of_nonpos_above
      (problem := problem)
      (xBar := (stoppedSeq k : E))
      (t := tSeq k)
      hreference_nonneg
      hnonpos

/-- Helper for Lemma 2.25: the source primal-threshold hypothesis is taken over the actual
constrained feasible set, and therefore yields a nonpositive `μ`-model value at some parameter
not smaller than the current one. -/
lemma stopped_mu_model_nonpos_above_current_parameter
    (hprimal :
      IsGLB
        (Set.range fun x : problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↦
          problem x)
        tStar)
    (hinitial_value : valueFunctionAt(t0) ≤ tStar - t0)
    (k : ℕ) :
    ∃ τ : ℝ, tSeq k ≤ τ ∧ modelValue τ (stoppedSeq k : E) μ ≤ 0 := by
  let τ := max (tSeq k) tStar
  refine ⟨τ, le_max_left _ _, ?_⟩
  have hmodel_le_opt :
      modelValue τ (stoppedSeq k : E) μ ≤
        sInf ((parametricProblem τ) '' problem.ambientSet) := by
    simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue] using
      (parametricProblem τ).lowerRegularizedModelValue_le_optimalValue (stoppedSeq k : E)
  have hopt_nonpos : sInf ((parametricProblem τ) '' problem.ambientSet) ≤ 0 := by
    by_contra hpos
    have hsInf_pos : 0 < sInf ((parametricProblem τ) '' problem.ambientSet) := lt_of_not_ge hpos
    have hhalf_pos : 0 < sInf ((parametricProblem τ) '' problem.ambientSet) / 2 := by
      linarith
    rcases hprimal.exists_between_self_add hhalf_pos with ⟨_, ⟨x, rfl⟩, _, hxlt⟩
    have hx_constraints :
        ∀ i : Fin m, problem.constraints i ((x : problem.ambientSet) : E) ≤ 0 :=
      (problem.mem_feasibleSet_iff (x := (x : problem.ambientSet))).1 x.property
    have hx_feasible : ((x : problem.ambientSet) : E) ∈ problem.feasibleSet := by
      simpa [LagrangianProblem.mem_feasibleSet_iff] using hx_constraints
    have htau_ge : tStar ≤ τ := le_max_right _ _
    have hx_lt_tau :
        problem ((x : problem.ambientSet) : E) <
          τ + sInf ((parametricProblem τ) '' problem.ambientSet) / 2 := by
      linarith
    have haux_le :
        (parametricProblem τ) ((x : problem.ambientSet) : E) ≤
          sInf ((parametricProblem τ) '' problem.ambientSet) / 2 := by
      have haux :=
        problem.constrainedAuxiliaryObjective_le_of_mem_feasibleSet_lt_add
          (t := τ)
          (x := ((x : problem.ambientSet) : E))
          hx_feasible
          (le_of_lt hhalf_pos)
          hx_lt_tau
      simpa [SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem,
        LagrangianProblem.constrainedAuxiliaryObjective,
        LagrangianProblem.constrainedAuxiliaryComponents] using haux
    have hx_mem :
        (parametricProblem τ) ((x : problem.ambientSet) : E) ∈
          ((parametricProblem τ) '' problem.ambientSet) := by
      exact ⟨((x : problem.ambientSet) : E), (x : problem.ambientSet).property, rfl⟩
    have himage_bdd :
        BddBelow ((parametricProblem τ) '' problem.ambientSet) := by
      simpa using (parametricProblem τ).objective_image_bddBelow
    have hsInf_le_x :
        sInf ((parametricProblem τ) '' problem.ambientSet) ≤
          (parametricProblem τ) ((x : problem.ambientSet) : E) :=
      csInf_le himage_bdd hx_mem
    linarith
  exact hmodel_le_opt.trans hopt_nonpos

/-- Helper for Lemma 2.25: under the primal-threshold and initial-threshold-control hypotheses, a
nonpositive parameter update already forces the stopped residual to be nonpositive. -/
-- Proof sketch: if a `μ`-root exists above `t_k`, then the `sInf`-defined update must lie above
-- `t_k`; combining this with the assumed nonpositive step forces equality and hence a zero
-- `μ`-model value at `t_k`. If no such root exists, the nonpositive-above witness from the
-- primal-threshold hypothesis makes the `μ`-model value at `t_k` strictly negative by the
-- sign-change lemma. In either case the Step `1(a)` stopping inequality yields
-- `stoppedResidual k ≤ 0`.
lemma stopped_residual_nonpos_of_nonpos_step
    (hprimal :
      IsGLB
        (Set.range fun x : problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↦
          problem x)
        tStar)
    (hinitial_value : valueFunctionAt(t0) ≤ tStar - t0)
    (hκ : κ < 1 / 2)
    {k : ℕ}
    (hstep_nonpos : tSeq (k + 1) ≤ tSeq k) :
    stoppedResidual k ≤ 0 := by
  have hone_sub_kappa_pos : 0 < 1 - κ := by
    linarith
  have hstop :
      (1 - κ) * modelValue (tSeq k) (stoppedSeq k : E) L ≤
        modelValue (tSeq k) (stoppedSeq k : E) μ := by
    -- Step `1(a)` compares the stopped `L`- and `μ`-model values at the same parameter.
    simpa [ge_iff_le, ConstrainedMinimizationMethod.step1a,
      ConstrainedMinimizationMethod.stoppedInternalIterate,
      ConstrainedMinimizationMethod.stopIndex,
      ConstrainedMinimizationMethod.internalIterate] using
      (ConstrainedMinimizationMethod.stopping_condition
        (problem := problem) (κ := κ) (t0 := t0) (x0 := x0) (hL := hL) (hStep1a := hStep1a) k)
  by_cases hroot :
      ∃ τ : ℝ, tSeq k ≤ τ ∧ modelValue τ (stoppedSeq k : E) μ = 0
  · have hroot_step :=
      regularizedModelValueRoot_mem_of_exists_root
        (problem := problem)
        (xBar := (stoppedSeq k : E))
        (t := tSeq k)
        hroot
    have hk_le_succ : tSeq k ≤ tSeq (k + 1) := by
      simpa [ConstrainedMinimizationMethod.t_succ_eq_regularizedModelValueRoot
        (problem := problem) (κ := κ) (t0 := t0) (x0 := x0) (hL := hL) (hStep1a := hStep1a) k] using
        hroot_step.1
    have hstep_eq : tSeq (k + 1) = tSeq k := le_antisymm hstep_nonpos hk_le_succ
    have hmu_zero_succ :
        modelValue (tSeq (k + 1)) (stoppedSeq k : E) μ = 0 := by
      rw [ConstrainedMinimizationMethod.t_succ_eq_regularizedModelValueRoot
        (problem := problem) (κ := κ) (t0 := t0) (x0 := x0) (hL := hL)
        (hStep1a := hStep1a) k]
      exact hroot_step.2
    have hmu_zero :
        modelValue (tSeq k) (stoppedSeq k : E) μ = 0 := by
      rw [← hstep_eq]
      exact hmu_zero_succ
    have hscaled :
        (1 - κ) * modelValue (tSeq k) (stoppedSeq k : E) L ≤ 0 := by
      simpa [hmu_zero] using hstop
    nlinarith [hscaled, hone_sub_kappa_pos]
  · rcases stopped_mu_model_nonpos_above_current_parameter
      (hprimal := hprimal)
      (hinitial_value := hinitial_value)
      (problem := problem) (κ := κ) (t0 := t0) (x0 := x0) (hL := hL)
      (hStep1a := hStep1a) k with ⟨τ, hτ_ge, hτ_nonpos⟩
    have hmu_neg :
        modelValue (tSeq k) (stoppedSeq k : E) μ < 0 := by
      by_cases hmu_nonneg : 0 ≤ modelValue (tSeq k) (stoppedSeq k : E) μ
      · exact False.elim <|
          hroot <|
            stopped_mu_root_exists_above_current_parameter
              (problem := problem)
              (κ := κ)
              (t0 := t0)
              (x0 := x0)
              (hL := hL)
              (hStep1a := hStep1a)
              k
              hmu_nonneg
              ⟨τ, hτ_ge, hτ_nonpos⟩
      · exact lt_of_not_ge hmu_nonneg
    have hscaled :
        (1 - κ) * modelValue (tSeq k) (stoppedSeq k : E) L < 0 := by
      exact lt_of_le_of_lt hstop hmu_neg
    nlinarith [hscaled, hone_sub_kappa_pos]

/-- Helper for Lemma 2.25: when the current parameter increment is positive, the normalized
geometric decay reconstructs the textbook bound for the stopped residual itself. -/
-- Proof sketch: multiply the normalized estimate by `√(t_{k+1} - t_k)`, then split on the sign
-- of the initial `μ`-model value. If that initial value is nonpositive, the entire right-hand side
-- is nonpositive and the residual is automatically bounded by the nonnegative target expression.
-- If it is positive, use `hinit_step` and the uniform step-size bounds to compare both square-root
-- factors with `√(t^* - t₀)` and recover the source product estimate.
lemma stopped_residual_le_geometric_of_pos_step
    (hκ : κ < 1 / 2)
    (hdecay :
      ∀ k : ℕ,
        2 * (1 - κ) *
            (stoppedResidual (k + 1) /
              Real.sqrt (tSeq (k + 2) - tSeq (k + 1))) ≤
          stoppedResidual k / Real.sqrt (tSeq (k + 1) - tSeq k))
    (hinit_step :
      modelValue t0 (stoppedSeq 0 : E) μ ≤ tSeq 1 - t0)
    (hinitial_model :
      stoppedResidual 0 ≤ (1 / (1 - κ)) * modelValue t0 (stoppedSeq 0 : E) μ)
    (hstep_bound : ∀ k : ℕ, tSeq (k + 1) - tSeq k ≤ tStar - t0)
    (k : ℕ)
    (hstep_pos : 0 < tSeq (k + 1) - tSeq k) :
    stoppedResidual k ≤ geometricBound(k) := by
  let β : ℝ := 1 / (2 * (1 - κ))
  let μ0 : ℝ := modelValue t0 (stoppedSeq 0 : E) μ
  let Δ0 : ℝ := tSeq 1 - t0
  let Δk : ℝ := tSeq (k + 1) - tSeq k
  have hone_sub_kappa_pos : 0 < 1 - κ := by
    linarith
  have hscale_nonneg : 0 ≤ 1 / (1 - κ) := by
    positivity
  have hbeta_nonneg : 0 ≤ β := by
    positivity
  have hΔk_nonneg : 0 ≤ Δk := hstep_pos.le
  have hsqrt_Δk_pos : 0 < Real.sqrt Δk := Real.sqrt_pos.2 hstep_pos
  have hsqrt_Δk_nonneg : 0 ≤ Real.sqrt Δk := hsqrt_Δk_pos.le
  have hnormalized := normalized_stopped_residual_le_geometric
    (problem := problem) (κ := κ) (t0 := t0) (x0 := x0) (hL := hL) (hStep1a := hStep1a)
    hκ hdecay k
  -- First undo the normalization at the current index using positivity of the current square root.
  have hscaled :
      stoppedResidual k ≤
        (β ^ k) * (stoppedResidual 0 / Real.sqrt Δ0) * Real.sqrt Δk := by
    have hscaled_raw :
        stoppedResidual k ≤
          (((1 / (2 * (1 - κ))) ^ k) *
              (stoppedResidual 0 / Real.sqrt (tSeq 1 - t0))) *
            Real.sqrt (tSeq (k + 1) - tSeq k) := by
      exact (div_le_iff₀ hsqrt_Δk_pos).mp (by simpa [mul_assoc, mul_left_comm, mul_comm] using hnormalized)
    simpa [β, Δ0, Δk, mul_assoc, mul_left_comm, mul_comm] using hscaled_raw
  by_cases hμ0_nonpos : μ0 ≤ 0
  · have hres0_nonpos : stoppedResidual 0 ≤ 0 := by
      have htarget_nonpos : (1 / (1 - κ)) * μ0 ≤ 0 := by
        nlinarith
      exact hinitial_model.trans htarget_nonpos
    have hquot_nonpos : stoppedResidual 0 / Real.sqrt Δ0 ≤ 0 := by
      by_cases hsqrt_Δ0_zero : Real.sqrt Δ0 = 0
      · simp [hsqrt_Δ0_zero]
      · have hsqrt_Δ0_pos : 0 < Real.sqrt Δ0 := by
          exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hsqrt_Δ0_zero)
        exact (div_le_iff₀ hsqrt_Δ0_pos).2 (by simpa using hres0_nonpos)
    have hscaled_nonpos :
        (β ^ k) * (stoppedResidual 0 / Real.sqrt Δ0) * Real.sqrt Δk ≤ 0 := by
      have hleft_nonpos :
          (β ^ k) * (stoppedResidual 0 / Real.sqrt Δ0) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hbeta_nonneg k) hquot_nonpos
      exact mul_nonpos_of_nonpos_of_nonneg hleft_nonpos hsqrt_Δk_nonneg
    have hresidual_nonpos : stoppedResidual k ≤ 0 := hscaled.trans hscaled_nonpos
    have htStar_nonneg : 0 ≤ tStar - t0 := by
      have hk_bound : Δk ≤ tStar - t0 := by
        simpa [Δk] using hstep_bound k
      linarith
    have hgeometric_nonneg : 0 ≤ geometricBound(k) := by
      positivity
    exact hresidual_nonpos.trans hgeometric_nonneg
  · have hμ0_pos : 0 < μ0 := lt_of_not_ge hμ0_nonpos
    have hΔ0_pos : 0 < Δ0 := by
      have hinit_step' : μ0 ≤ Δ0 := by
        simpa [μ0, Δ0] using hinit_step
      linarith
    have hsqrt_Δ0_pos : 0 < Real.sqrt Δ0 := Real.sqrt_pos.2 hΔ0_pos
    have hμ0_le_Δ0 : μ0 ≤ Δ0 := by
      simpa [μ0, Δ0] using hinit_step
    have hμ0_le_tStar : μ0 ≤ tStar - t0 := by
      exact hμ0_le_Δ0.trans (by simpa [Δ0] using hstep_bound 0)
    have htStar_pos : 0 < tStar - t0 := by
      exact lt_of_lt_of_le hstep_pos (by simpa [Δk] using hstep_bound k)
    have hsqrt_μ0_le_sqrt_Δ0 : Real.sqrt μ0 ≤ Real.sqrt Δ0 := by
      exact Real.sqrt_le_sqrt hμ0_le_Δ0
    have hμ0_div_le_sqrt :
        μ0 / Real.sqrt Δ0 ≤ Real.sqrt μ0 := by
      have hsqrt_sq : Real.sqrt μ0 * Real.sqrt μ0 = μ0 := by
        rw [show Real.sqrt μ0 * Real.sqrt μ0 = (Real.sqrt μ0) ^ (2 : ℕ) by ring]
        rw [Real.sq_sqrt hμ0_pos.le]
      have hmul :
          μ0 ≤ Real.sqrt μ0 * Real.sqrt Δ0 := by
        calc
          μ0 = Real.sqrt μ0 * Real.sqrt μ0 := by
            exact hsqrt_sq.symm
          _ ≤ Real.sqrt μ0 * Real.sqrt Δ0 := by
            gcongr
      exact (div_le_iff₀ hsqrt_Δ0_pos).2 hmul
    have hquot_le :
        stoppedResidual 0 / Real.sqrt Δ0 ≤
          (1 / (1 - κ)) * Real.sqrt μ0 := by
      calc
        stoppedResidual 0 / Real.sqrt Δ0 ≤
            ((1 / (1 - κ)) * μ0) / Real.sqrt Δ0 := by
          exact div_le_div_of_nonneg_right hinitial_model (Real.sqrt_nonneg _)
        _ = (1 / (1 - κ)) * (μ0 / Real.sqrt Δ0) := by
          rw [mul_div_assoc]
        _ ≤ (1 / (1 - κ)) * Real.sqrt μ0 := by
          exact mul_le_mul_of_nonneg_left hμ0_div_le_sqrt hscale_nonneg
    have hsqrt_μ0_le_sqrt_tStar : Real.sqrt μ0 ≤ Real.sqrt (tStar - t0) := by
      exact Real.sqrt_le_sqrt hμ0_le_tStar
    have hsqrt_Δk_le_sqrt_tStar : Real.sqrt Δk ≤ Real.sqrt (tStar - t0) := by
      exact Real.sqrt_le_sqrt (by simpa [Δk] using hstep_bound k)
    have hsqrt_product_le :
        Real.sqrt μ0 * Real.sqrt Δk ≤ tStar - t0 := by
      have hsqrt_tStar_sq :
          Real.sqrt (tStar - t0) * Real.sqrt (tStar - t0) = tStar - t0 := by
        rw [show Real.sqrt (tStar - t0) * Real.sqrt (tStar - t0) =
            (Real.sqrt (tStar - t0)) ^ (2 : ℕ) by ring]
        rw [Real.sq_sqrt htStar_pos.le]
      calc
        Real.sqrt μ0 * Real.sqrt Δk ≤
            Real.sqrt (tStar - t0) * Real.sqrt (tStar - t0) := by
          exact mul_le_mul hsqrt_μ0_le_sqrt_tStar hsqrt_Δk_le_sqrt_tStar
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = tStar - t0 := by
          exact hsqrt_tStar_sq
    have hbase_product_le :
        ((1 / (1 - κ)) * Real.sqrt μ0) * Real.sqrt Δk ≤
          (tStar - t0) / (1 - κ) := by
      have hmul_le :
          (1 / (1 - κ)) * (Real.sqrt μ0 * Real.sqrt Δk) ≤
            (1 / (1 - κ)) * (tStar - t0) := by
        exact mul_le_mul_of_nonneg_left hsqrt_product_le hscale_nonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul_le
    have hright_le :
        (β ^ k) * (stoppedResidual 0 / Real.sqrt Δ0) * Real.sqrt Δk ≤
          ((β ^ k) * ((1 / (1 - κ)) * Real.sqrt μ0)) * Real.sqrt Δk := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hquot_le (pow_nonneg hbeta_nonneg k))
        hsqrt_Δk_nonneg
    have hfinal_step :
        (β ^ k) * (((1 / (1 - κ)) * Real.sqrt μ0) * Real.sqrt Δk) ≤
          geometricBound(k) := by
      have hmul_le :
          (β ^ k) *
              (((1 / (1 - κ)) * Real.sqrt μ0) * Real.sqrt Δk) ≤
            (β ^ k) * ((tStar - t0) / (1 - κ)) := by
        exact mul_le_mul_of_nonneg_left hbase_product_le (pow_nonneg hbeta_nonneg k)
      simpa [β, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul_le
    have hfinal_step' :
        ((β ^ k) * ((1 / (1 - κ)) * Real.sqrt μ0)) * Real.sqrt Δk ≤
          geometricBound(k) := by
      simpa [mul_assoc] using hfinal_step
    exact hscaled.trans (hright_le.trans hfinal_step')

/-- Helper for Lemma 2.25: the source primal-threshold hypothesis gives the universal lower
bound `min (tStar - t0) 0 ≤ valueFunctionAt(t0)`. -/
-- Proof sketch: apply the threshold-sign lower bound for the auxiliary objective pointwise on the
-- ambient set, then pass to the infimum defining `valueFunctionAt(t0)`.
lemma min_thresholdGap_zero_le_valueFunctionAt
    (hprimal :
      IsGLB
        (Set.range fun x : problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↦
          problem x)
        tStar) :
    min (tStar - t0) 0 ≤ valueFunctionAt(t0) := by
  have hprimal_feasible :
      IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar := by
    simpa [SmoothFunctionalConstraintsMinimizationProblem.toFunctionalConstraintsMinimizationProblem]
      using hprimal
  have hvalue_lower :
      min (tStar - t0) 0 ≤ sInf ((parametricProblem t0) '' problem.ambientSet) := by
    -- Pass the pointwise auxiliary lower bound to the infimum over the ambient set.
    refine le_csInf ?_ ?_
    · rcases problem.ambient_nonempty with ⟨x, hx⟩
      exact ⟨_, ⟨x, hx, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      have haux :
          min (tStar - t0) 0 ≤ problem.constrainedAuxiliaryObjective t0 x := by
        simpa using
          problem.min_sub_zero_le_constrainedAuxiliaryObjective
            (tStar := tStar)
            hprimal_feasible
            t0
            x
      simpa [SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem,
        LagrangianProblem.constrainedAuxiliaryObjective,
        LagrangianProblem.constrainedAuxiliaryComponents] using haux
  simpa [valueFunctionAt,
    SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem_feasibleSet]
    using hvalue_lower

/-- Helper for Lemma 2.25: the fixed-`t₀` optimal value is bounded above by the initial stopped
residual through the canonical upper-model comparison. -/
-- Proof sketch: apply the fixed-`t₀` owner theorem
-- `optimalValue_le_upperRegularizedModelValue` at the base point `(stoppedSeq 0 : E)` and then
-- rewrite the local notations `valueFunctionAt(t₀)` and `stoppedResidual 0`.
lemma valueFunctionAt_le_initialStoppedResidual :
    valueFunctionAt(t0) ≤ stoppedResidual 0 := by
  -- Use the owner optimal-value bridge instead of unfolding the infimum directly.
  simpa [valueFunctionAt, stoppedResidual,
    SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue] using
    (parametricProblem t0).optimalValue_le_upperRegularizedModelValue (stoppedSeq 0 : E)

/-- Helper for Lemma 2.25: the initial step and the initial model comparison already imply the
base geometric estimate at `k = 0`. -/
-- Proof sketch: first bound the initial `L`-model value by the initial `μ`-model value, then use
-- the first-step comparison and the uniform increment bound at `k = 0`.
lemma initialStoppedResidual_le_geometricBase
    (hκ : κ < 1 / 2)
    (hinit_step :
      modelValue t0 (stoppedSeq 0 : E) μ ≤ tSeq 1 - t0)
    (hinitial_model :
      stoppedResidual 0 ≤ (1 / (1 - κ)) * modelValue t0 (stoppedSeq 0 : E) μ)
    (hstep_bound : ∀ k : ℕ, tSeq (k + 1) - tSeq k ≤ tStar - t0) :
    stoppedResidual 0 ≤ geometricBound(0) := by
  have hone_sub_kappa_pos : 0 < 1 - κ := by
    linarith
  have hscale_nonneg : 0 ≤ 1 / (1 - κ) := by
    positivity
  -- Compare the initial stopped residual with the first parameter increment through the source
  -- `μ`-model estimate.
  calc
    stoppedResidual 0 ≤ (1 / (1 - κ)) * modelValue t0 (stoppedSeq 0 : E) μ := hinitial_model
    _ ≤ (1 / (1 - κ)) * (tSeq 1 - t0) := by
      exact mul_le_mul_of_nonneg_left hinit_step hscale_nonneg
    _ ≤ (1 / (1 - κ)) * (tStar - t0) := by
      exact mul_le_mul_of_nonneg_left (by simpa using hstep_bound 0) hscale_nonneg
    _ = geometricBound(0) := by
      simp [geometricBound]

/-- Helper for Lemma 2.25: if `modelValue t xBar μ < 0`, then no `μ`-root can occur at or above
the reference parameter `t`. -/
-- Proof sketch: monotonicity of the `μ`-model value in the scalar parameter pushes every value
-- above `t` below the negative reference value, so equality with `0` is impossible.
lemma regularizedModelValueRootSet_eq_empty_of_neg_at_reference
    {xBar : E} {t : ℝ}
    (hvalue_neg : modelValue t xBar μ < 0) :
    {τ : ℝ | t ≤ τ ∧ modelValue τ xBar μ = 0} = (∅ : Set ℝ) := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro τ hτ
  rcases hτ with ⟨hτ_ge, hτ_zero⟩
  have hΔ_nonneg : 0 ≤ τ - t := sub_nonneg.mpr hτ_ge
  have hshift :
      modelValue τ xBar μ ≤ modelValue t xBar μ := by
    have hshift_raw :=
      regularizedModelValue_shift_le
        (problem := problem)
        (xBar := xBar)
        (t := t)
        (Δ := τ - t)
        hΔ_nonneg
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift_raw
  have hnonneg : 0 ≤ modelValue t xBar μ := by
    simpa [hτ_zero] using hshift
  linarith

/-- Helper for Lemma 2.25: the `μ`-root update issued from the base parameter `0` is always
nonnegative. -/
-- Proof sketch: if a genuine root exists above `0`, then the root update lies in the same root
-- set; otherwise the owner convention returns `0`.
lemma regularizedModelValueRoot_nonneg_at_zero
    {xBar : E} :
    0 ≤ problem.regularizedModelValueRoot xBar 0 μ := by
  by_cases hroot : ∃ τ : ℝ, 0 ≤ τ ∧ modelValue τ xBar μ = 0
  · exact
      (regularizedModelValueRoot_mem_of_exists_root
        (problem := problem)
        (xBar := xBar)
        (t := 0)
        hroot).1
  · have hrootset_empty :
        {τ : ℝ | 0 ≤ τ ∧ modelValue τ xBar μ = 0} = (∅ : Set ℝ) := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro τ hτ
      exact hroot ⟨τ, hτ.1, hτ.2⟩
    rw [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValueRoot, hrootset_empty]
    simp

/-- Helper for Lemma 2.25: the initial scalar data force the threshold gap `tStar - t0` to be
nonnegative. -/
-- Proof sketch: assume `tStar - t0 < 0`. The threshold-sign lower bound and `hinitial_value`
-- pin `valueFunctionAt(t₀)` to that negative gap, while the canonical upper-model bridge and the
-- initial-step estimates force equality throughout the `k = 0` scalar chain. That makes the
-- first root set empty and hence `t₁ = 0`; the second step bound then forces `t₂ < 0`, but the
-- second root update cannot move left of `t₁ = 0` once its root set is nonempty, a contradiction.
lemma thresholdGap_nonneg
    (hprimal :
      IsGLB
        (Set.range fun x : problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↦
          problem x)
        tStar)
    (hκ_nonneg : 0 ≤ κ)
    (hκ : κ < 1 / 2)
    (hinit_step :
      modelValue t0 (stoppedSeq 0 : E) μ ≤ tSeq 1 - t0)
    (hinitial_value : valueFunctionAt(t0) ≤ tStar - t0)
    (hinitial_model :
      stoppedResidual 0 ≤ (1 / (1 - κ)) * modelValue t0 (stoppedSeq 0 : E) μ)
    (hstep_bound : ∀ k : ℕ, tSeq (k + 1) - tSeq k ≤ tStar - t0) :
    0 ≤ tStar - t0 := by
  by_contra hgap_nonneg
  let gap : ℝ := tStar - t0
  let μ0 : ℝ := modelValue t0 (stoppedSeq 0 : E) μ
  have hgap_neg : gap < 0 := by
    exact lt_of_not_ge hgap_nonneg
  have hμ0_le_gap : μ0 ≤ gap := by
    -- The first-step upper bound controls the initial `μ`-model value by the same gap.
    have hμ0_le_step0 : μ0 ≤ tSeq 1 - t0 := by
      simpa [μ0] using hinit_step
    exact hμ0_le_step0.trans (by simpa [gap] using hstep_bound 0)
  have hμ0_neg : μ0 < 0 := by
    linarith
  have hrootset0_empty :
      {τ : ℝ | t0 ≤ τ ∧ modelValue τ (stoppedSeq 0 : E) μ = 0} = (∅ : Set ℝ) := by
    simpa [μ0] using
      regularizedModelValueRootSet_eq_empty_of_neg_at_reference
        (problem := problem)
        (μ := μ)
        (xBar := (stoppedSeq 0 : E))
        (t := t0)
        hμ0_neg
  have ht1_eq_zero : tSeq 1 = 0 := by
    -- No root exists above `t₀`, so the first owner update is the empty-root infimum `0`.
    rw [ConstrainedMinimizationMethod.t_succ_eq_regularizedModelValueRoot
      (problem := problem)
      (κ := κ)
      (t0 := t0)
      (x0 := x0)
      (hL := hL)
      (hStep1a := hStep1a)
      0]
    rw [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValueRoot, hrootset0_empty]
    simp
  have hstep1_neg : tSeq 2 < 0 := by
    -- The second uniform step bound now pushes the next parameter strictly below zero.
    have hstep1_le : tSeq 2 - tSeq 1 ≤ gap := by
      simpa [gap] using hstep_bound 1
    rw [ht1_eq_zero] at hstep1_le
    linarith
  have ht2_nonneg : 0 ≤ tSeq 2 := by
    -- The second root update starts at `t₁ = 0`, so it can never move into negative scalars.
    simpa [ht1_eq_zero, ConstrainedMinimizationMethod.t_succ_eq_regularizedModelValueRoot
      (problem := problem)
      (κ := κ)
      (t0 := t0)
      (x0 := x0)
      (hL := hL)
      (hStep1a := hStep1a)
      1] using
      regularizedModelValueRoot_nonneg_at_zero
        (problem := problem)
        (μ := μ)
        (xBar := (stoppedSeq 1 : E))
  linarith

/-- Helper for Lemma 2.25: once the threshold gap is known to be nonnegative, every geometric
target is nonnegative as well. -/
-- Proof sketch: the geometric prefactor is a product of nonnegative scalars when `κ < 1 / 2`,
-- so the sign is inherited from `tStar - t0`.
lemma geometricBound_nonneg
    (hκ : κ < 1 / 2)
    (hgap_nonneg : 0 ≤ tStar - t0)
    (k : ℕ) :
    0 ≤ geometricBound(k) := by
  positivity

/-- Helper for Lemma 2.25: the stopped residual itself satisfies the displayed geometric
estimate. -/
-- Proof sketch: split on whether the current parameter increment is positive. The positive-step
-- branch is the existing algebraic square-root argument. If the step is nonpositive, the new
-- structural lemma gives `stoppedResidual k ≤ 0`; the remaining comparison depends only on the
-- sign of the geometric target.
lemma stopped_residual_le_geometric_bound
    (hprimal :
      IsGLB
        (Set.range fun x : problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↦
          problem x)
        tStar)
    (hκ_nonneg : 0 ≤ κ)
    (hκ : κ < 1 / 2)
    (hdecay :
      ∀ k : ℕ,
        2 * (1 - κ) *
            (stoppedResidual (k + 1) /
              Real.sqrt (tSeq (k + 2) - tSeq (k + 1))) ≤
          stoppedResidual k / Real.sqrt (tSeq (k + 1) - tSeq k))
    (hinit_step :
      modelValue t0 (stoppedSeq 0 : E) μ ≤ tSeq 1 - t0)
    (hinitial_value : valueFunctionAt(t0) ≤ tStar - t0)
    (hinitial_model :
      stoppedResidual 0 ≤ (1 / (1 - κ)) * modelValue t0 (stoppedSeq 0 : E) μ)
    (hstep_bound : ∀ k : ℕ, tSeq (k + 1) - tSeq k ≤ tStar - t0)
    (k : ℕ) :
    stoppedResidual k ≤ geometricBound(k) := by
  by_cases hstep_pos : 0 < tSeq (k + 1) - tSeq k
  · -- A positive step is exactly the square-root branch already isolated above.
    exact
      stopped_residual_le_geometric_of_pos_step
        (problem := problem)
        (κ := κ)
        (t0 := t0)
        (tStar := tStar)
        (x0 := x0)
        (hL := hL)
        (hStep1a := hStep1a)
        hκ
        hdecay
        hinit_step
        hinitial_model
        hstep_bound
        k
        hstep_pos
  · -- Route correction: the nonpositive-step case is structural, so first convert it to
    -- `stoppedResidual k ≤ 0` and isolate only the remaining sign comparison for the target.
    have hstep_nonpos : tSeq (k + 1) ≤ tSeq k := by
      linarith [le_of_not_gt hstep_pos]
    have hresidual_nonpos : stoppedResidual k ≤ 0 := by
      exact
        stopped_residual_nonpos_of_nonpos_step
          (problem := problem)
          (κ := κ)
          (t0 := t0)
          (tStar := tStar)
          (x0 := x0)
          (hL := hL)
          (hStep1a := hStep1a)
          hprimal
          hinitial_value
          hκ
          hstep_nonpos
    -- The initial scalar data already force the threshold gap to be nonnegative.
    have hgap_nonneg : 0 ≤ tStar - t0 := by
      exact
        thresholdGap_nonneg
          (problem := problem)
          (κ := κ)
          (t0 := t0)
          (tStar := tStar)
          (x0 := x0)
          (hL := hL)
          (hStep1a := hStep1a)
          hprimal
          hκ_nonneg
          hκ
          hinit_step
          hinitial_value
          hinitial_model
          hstep_bound
    have hgeometric_nonneg : 0 ≤ geometricBound(k) := by
      exact geometricBound_nonneg (κ := κ) (t0 := t0) (tStar := tStar) hκ hgap_nonneg k
    exact hresidual_nonpos.trans hgeometric_nonneg

/- In the source, the master update `t^*(x_{k,j(k)}, t_k)` is tied to the primal threshold
`t^*`; here that well-posedness is recovered from the source-facing primal-threshold hypothesis on
the actual constrained feasible set rather than by an extra ad hoc root-existence premise. -/
/-- Lemma 2.25: for the Chapter 2 two-level scheme with the canonical root update
`t_{k+1} = t^*(x_{k,j(k)}, t_k)`, assume `0 ≤ κ < 1 / 2`, assume the normalized stopped
residuals
`f^*(t_k; x_{k,j(k)}; L) / √(t_{k+1} - t_k)` decay by the factor `1 / (2 * (1 - κ))`, assume
`tStar` is the primal threshold, assume the initial threshold control
`f^*(t₀) ≤ t^* - t₀`, assume the initial `μ`-model value is controlled by the first parameter
increment, and assume every parameter increment is at most `t^* - t₀`. Then the selected residual
`f^*(t_k; x_{k,j^*(k)}; L)` satisfies the displayed geometric estimate. The attained upper-model
formulation at the exact successor `x_{k+1}` is kept only as a bridge consequence via
`selected_residual_eq_upperModel_at_successor`. -/
-- Proof sketch: estimate the stopped residual by the normalized geometric recurrence together
-- with the step-size bounds, and then pass to the selected residual through the canonical
-- prefix-minimization inequality `selected_residual_le_stopped_residual`.
lemma selected_residual_le_geometric_rate
    (hprimal :
      IsGLB
        (Set.range fun x : problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↦
          problem x)
        tStar)
    (hκ_nonneg : 0 ≤ κ)
    (hκ : κ < 1 / 2)
    (hdecay :
      ∀ k : ℕ,
        2 * (1 - κ) *
            (stoppedResidual (k + 1) /
              Real.sqrt (tSeq (k + 2) - tSeq (k + 1))) ≤
          stoppedResidual k / Real.sqrt (tSeq (k + 1) - tSeq k))
    (hinit_step :
      modelValue t0 (stoppedSeq 0 : E) μ ≤ tSeq 1 - t0)
    (hinitial_value : valueFunctionAt(t0) ≤ tStar - t0)
    (hinitial_model :
      stoppedResidual 0 ≤ (1 / (1 - κ)) * modelValue t0 (stoppedSeq 0 : E) μ)
    (hstep_bound : ∀ k : ℕ, tSeq (k + 1) - tSeq k ≤ tStar - t0)
    (k : ℕ) :
    selectedResidual k ≤ geometricBound(k) := by
  -- Pass from the chosen prefix minimizer to the stopped iterate, then invoke the structural
  -- stopped-residual estimate.
  calc
    selectedResidual k ≤ stoppedResidual k := by
      simpa using
        (ConstrainedMinimizationMethod.selected_residual_le_stopped_residual
          (problem := problem)
          (κ := κ)
          (t0 := t0)
          (x0 := x0)
          (hL := hL)
          (hStep1a := hStep1a)
          k)
    _ ≤ geometricBound(k) := by
      exact
        stopped_residual_le_geometric_bound
          (problem := problem)
          (κ := κ)
          (t0 := t0)
          (tStar := tStar)
          (x0 := x0)
          (hL := hL)
          (hStep1a := hStep1a)
          hprimal
          hκ_nonneg
          hκ
          hdecay
          hinit_step
          hinitial_value
          hinitial_model
          hstep_bound
          k

/-- The selected residual is the attained upper-model value at the exact successor `x_{k+1}`. -/
-- Proof sketch: `ConstrainedMinimizationMethod.x_succ_isMinOn_upperModel` states that `x_{k+1}`
-- minimizes the selected upper model on the ambient set. Identify the infimum
-- `selectedResidual k` with that attained value by `IsLeast.csInf_eq`.
lemma selected_residual_eq_upperModel_at_successor
    (k : ℕ) :
    selectedResidual k = upperModelAtSuccessor(k) := by
  let upperModel : E → ℝ :=
    quadraticallyRegularizedObjective
      (SmoothMinimaxProblem.affineApproximation
        (parametricProblem (tSeq k))
        (selectedSeq k : E))
      L
      (selectedSeq k : E)
  have hmin :
      IsMinOn upperModel problem.ambientSet (xSeq (k + 1) : E) := by
    simpa [upperModel] using
      ConstrainedMinimizationMethod.x_succ_isMinOn_upperModel
        (problem := problem) (κ := κ) (t0 := t0) (x0 := x0) (hL := hL) (hStep1a := hStep1a) k
  have hx_mem : (xSeq (k + 1) : E) ∈ problem.ambientSet := (xSeq (k + 1)).property
  have hglb : IsGLB (upperModel '' problem.ambientSet) (upperModel (xSeq (k + 1) : E)) := by
    simpa using hmin.isGLB hx_mem
  have himage_nonempty : (upperModel '' problem.ambientSet).Nonempty := by
    exact ⟨upperModel (xSeq (k + 1) : E), ⟨(xSeq (k + 1) : E), hx_mem, rfl⟩⟩
  -- Rewrite the defining infimum of the selected residual to the attained minimum at `x_{k+1}`.
  change
    problem.regularizedModelValue (tSeq k) (selectedSeq k : E) L =
      upperModel (xSeq (k + 1) : E)
  simpa [upperModel, SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue] using
    hglb.csInf_eq himage_nonempty

/-- Bridge consequence of Lemma 2.25: the equivalent attained-upper-model estimate at the exact
successor `x_{k+1}`. -/
lemma upperModel_at_successor_le_geometric_rate
    (hprimal :
      IsGLB
        (Set.range fun x : problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↦
          problem x)
        tStar)
    (hκ_nonneg : 0 ≤ κ)
    (hκ : κ < 1 / 2)
    (hdecay :
      ∀ k : ℕ,
        2 * (1 - κ) *
            (stoppedResidual (k + 1) /
              Real.sqrt (tSeq (k + 2) - tSeq (k + 1))) ≤
          stoppedResidual k / Real.sqrt (tSeq (k + 1) - tSeq k))
    (hinit_step :
      modelValue t0 (stoppedSeq 0 : E) μ ≤ tSeq 1 - t0)
    (hinitial_value : valueFunctionAt(t0) ≤ tStar - t0)
    (hinitial_model :
      stoppedResidual 0 ≤ (1 / (1 - κ)) * modelValue t0 (stoppedSeq 0 : E) μ)
    (hstep_bound : ∀ k : ℕ, tSeq (k + 1) - tSeq k ≤ tStar - t0)
    (k : ℕ) :
    upperModelAtSuccessor(k) ≤ geometricBound(k) := by
  -- Rewrite the selected residual as the attained upper-model value at `x_{k+1}` and reuse the
  -- selected-residual estimate.
  rw [← selected_residual_eq_upperModel_at_successor
    (problem := problem)
    (κ := κ)
    (t0 := t0)
    (x0 := x0)
    (hL := hL)
    (hStep1a := hStep1a)
    k]
  exact
    selected_residual_le_geometric_rate
      (problem := problem)
      (κ := κ)
      (t0 := t0)
      (tStar := tStar)
      (x0 := x0)
      (hL := hL)
      (hStep1a := hStep1a)
      hprimal
      hκ_nonneg
      hκ
      hdecay
      hinit_step
      hinitial_value
      hinitial_model
      hstep_bound
      k

end GeometricRate

end
