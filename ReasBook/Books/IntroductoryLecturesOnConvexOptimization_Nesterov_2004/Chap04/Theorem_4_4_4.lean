/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_38
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Assumption_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open SmoothNonlinearEquationProblem
open scoped ConstrainedArgmin InnerProduct LevelSetNotation Manifold MinimalSingularValue
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonLocalDecreaseNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation
open scoped Topology

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/- Theorem 4.4.4 lies in the whole-space modified Gauss--Newton / exact-solvability domain.

Sampled owner-style declarations:
* `SmoothNonlinearEquationProblem.solutionSet` in `Definition_4_4_8`, the chapter owner for the
  exact-solution locus `problem x = 0`;
* mathlib `LipschitzOnWith L (fun x ↦ fderiv ℝ problem x) Set.univ`, the canonical whole-space
  Jacobian-Lipschitz owner for the residual map;
* `HasUniformDualNondegeneracyOnInitialSublevelSet` in `Assumption_4_4_3`, the source-facing
  nondegeneracy owner on the norm-merit initial sublevel set;
* `IsMinOn` in mathlib, the canonical owner for global minimizers on `Set.univ`;
* `exact_solution_isMinOn_meritFunctionReformulation` in `Proposition_4_4_4`, the thin bridge
  from an exact solution back to the minimizer reformulation.

Best owner abstraction:
* source-facing: existence of an exact solution `xStar ∈ solutionSet problem` together with the
  displayed distance bound from the initial point;
* core/canonical: the residual map `problem` together with the whole-space Jacobian-Lipschitz
  owner `LipschitzOnWith L (fderiv ℝ problem) Set.univ`;
* bridge/view: the norm-merit reformulation `meritFunctionReformulation problem norm` on whose
  initial sublevel set Assumption 4.4.3 is imposed.

Primitive data:
* the bundled smooth residual map `problem`;
* the initial point `x0`;
* the nondegeneracy constant `σ`;
* the whole-space Jacobian-Lipschitz hypothesis on `problem`;
* the norm-merit nondegeneracy assumption
  `HasUniformDualNondegeneracyOnInitialSublevelSet`.

Derived API:
* the exact-solution owner `xStar ∈ solutionSet problem`;
* the initial-residual distance bound.

This refinement keeps the labeled theorem at the source-facing exact-solution layer. The
minimizer reformulation is left to the upstream bridge from `Proposition_4_4_4`
`exact_solution_isMinOn_meritFunctionReformulation` instead of being repackaged locally. It also
removes the nonfaithful global `C¹` hypothesis on the raw norm merit `x ↦ ‖problem x‖`, whose
nondifferentiability at nondegenerate zeros conflicts with Assumption 4.4.3, and instead places
the smoothness input on the canonical owner layer already used by the chapter Taylor-remainder
bridge: the whole-space Jacobian-Lipschitz control of `problem`.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯

section

variable {problem : SmoothMap}
variable {x0 : E} {σ : ℝ}

local notation "f" => meritFunctionReformulation problem norm

/-- Helper for Theorem 4.4.4: the initial point belongs to the initial sublevel set of the
norm-merit reformulation. -/
lemma initialPoint_mem_initial_normSublevel :
    x0 ∈ (𝓛[f]((f x0)) : Set E) := by
  -- The initial point attains the defining level value of its own sublevel set.
  change f x0 ≤ f x0
  exact le_rfl

/-- Helper for Theorem 4.4.4: Assumption 4.4.3 specializes at the initial point to a lower bound
for the dual minimal singular value of the initial Jacobian. -/
lemma dual_nondegeneracy_at_initialPoint
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem norm x0 σ) :
    σ ≤ σ_min((fderiv ℝ problem x0)†) :=
  HasUniformDualNondegeneracyOnInitialSublevelSet.lower_bound hσ
    (initialPoint_mem_initial_normSublevel (problem := problem) (x0 := x0))

/-- Helper for Theorem 4.4.4: if the Jacobian-Lipschitz constant is `0`, then the first-order
Taylor remainder on `Set.univ` vanishes identically, so `problem` is globally affine with linear
part `fderiv ℝ problem x₀`. -/
lemma zero_jacobian_lipschitz_gives_exact_linearization
    (L : NNReal)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hL0 : (L : ℝ) = 0)
    (x : E) :
    problem x = problem x0 + fderiv ℝ problem x0 (x - x0) := by
  -- Route correction: in the degenerate `L = 0` branch, the source proof first turns the
  -- residual map into an exact affine model before solving the linear equation at `x₀`.
  have hrem :
      ‖problem x - problem x0 - fderiv ℝ problem x0 (x - x0)‖ ≤
        ((L : ℝ) / 2) * ‖x - x0‖ ^ (2 : ℕ) :=
    problem.jacobian_lipschitz_taylor_remainder_le
      (𝓕 := Set.univ) convex_univ hJacobianLipschitz x0 x (by simp) (by simp)
  have hzero_norm :
      ‖problem x - problem x0 - fderiv ℝ problem x0 (x - x0)‖ = 0 := by
    have hle_zero :
        ‖problem x - problem x0 - fderiv ℝ problem x0 (x - x0)‖ ≤ 0 := by
      simpa [hL0] using hrem
    exact le_antisymm hle_zero (norm_nonneg _)
  have hsub :
      problem x - problem x0 = fderiv ℝ problem x0 (x - x0) := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero_norm)
  simpa [add_comm] using (sub_eq_iff_eq_add.mp hsub)

/-- Helper for Theorem 4.4.4: once the `L = 0` branch supplies a stronger
`‖x* - x₀‖ ≤ ‖problem x₀‖ / σ` estimate, the displayed theorem bound follows immediately. -/
lemma one_over_sigma_bound_le_two_over_sigma_bound
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem norm x0 σ)
    {r : ℝ}
    (hr : r ≤ ‖problem x0‖ / σ) :
    r ≤ (2 / σ) * ‖problem x0‖ := by
  -- Positivity of `σ` lets us compare the stronger one-step estimate to the theorem's bound.
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hscale :
      ‖problem x0‖ / σ ≤ (2 / σ) * ‖problem x0‖ := by
    have hnonneg : 0 ≤ ‖problem x0‖ := norm_nonneg _
    field_simp [hσ_pos.ne']
    nlinarith
  exact hr.trans hscale

/-- Helper for Theorem 4.4.4: a positive lower bound on the dual minimal singular value of a
real Hilbert-space operator yields a controlled preimage for every right-hand side. -/
lemma exists_preimage_norm_le_of_dualMinimalSingularValue_pos
    (A : E →L[ℝ] F)
    (hA : 0 < σ_min(A†))
    (b : F) :
    ∃ x : E, A x = b ∧ ‖x‖ ≤ ‖b‖ / σ_min(A†) := by
  simpa using exists_preimage_norm_le_of_adjoint_minimalSingularValue_pos
    (A := A) hA b

/-- Helper for Theorem 4.4.4: in the branch `L = 0`, affine exactness reduces the problem to a
single controlled preimage of the initial residual under `fderiv ℝ problem x₀`. -/
lemma exact_solution_of_zero_jacobian_lipschitz
    (L : NNReal)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem norm x0 σ)
    (hL0 : (L : ℝ) = 0) :
    ∃ xStar : E,
      xStar ∈ solutionSet problem ∧
        ‖xStar - x0‖ ≤ ‖problem x0‖ / σ := by
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hdual_pos : 0 < σ_min((fderiv ℝ problem x0)†) := by
    exact lt_of_lt_of_le hσ_pos
      (dual_nondegeneracy_at_initialPoint (problem := problem) (x0 := x0) (σ := σ) hσ)
  obtain ⟨h, hh, hbound⟩ :=
    exists_preimage_norm_le_of_dualMinimalSingularValue_pos
      (A := fderiv ℝ problem x0) hdual_pos (-problem x0)
  let xStar : E := x0 + h
  have hxStar_eq_zero : problem xStar = 0 := by
    -- Exact affine linearization turns the controlled correction into a true zero of `problem`.
    have hlin :
        problem xStar = problem x0 + fderiv ℝ problem x0 (xStar - x0) :=
      zero_jacobian_lipschitz_gives_exact_linearization
        (problem := problem) (x0 := x0) L hJacobianLipschitz hL0 xStar
    have hstep : fderiv ℝ problem x0 (xStar - x0) = -problem x0 := by
      simpa [xStar] using hh
    calc
      problem xStar = problem x0 + fderiv ℝ problem x0 (xStar - x0) := hlin
      _ = problem x0 + (-problem x0) := by rw [hstep]
      _ = 0 := by simp
  have hxStar_mem : xStar ∈ solutionSet problem := by
    rw [mem_solutionSet_iff]
    exact hxStar_eq_zero
  have hdist : ‖xStar - x0‖ ≤ ‖problem x0‖ / σ := by
    -- The affine correction size is exactly the desired distance to the initial point.
    simpa [xStar, norm_neg] using hbound
  exact ⟨xStar, hxStar_mem, hdist⟩

/-- Helper for Theorem 4.4.4: for positive `L`, each whole-space regularized local model with
parameter `L` attains a global minimizer. -/
lemma constant_regularization_argmin_nonempty
    (L : NNReal)
    (hL_pos : 0 < (L : ℝ))
    (x : E) :
    (argmin[Set.univ]
      (quadraticallyRegularizedObjective
        (ψ[problem; norm; fun y ↦ fderiv ℝ problem y] x)
        (L : ℝ)
        x)).Nonempty := by
  let objective : E → ℝ :=
    quadraticallyRegularizedObjective
      (ψ[problem; norm; fun y ↦ fderiv ℝ problem y] x)
      (L : ℝ)
      x
  have hobjective_cont : Continuous objective := by
    -- The local model is continuous in the trial point, and the quadratic penalty preserves it.
    unfold objective
    continuity
  have hstrong :
      StrongConvexOn Set.univ (L : ℝ) objective := by
    -- Add the convex norm-model slice to the `L`-strongly convex centered quadratic penalty.
    have hsplit :
        objective =
          (ψ[problem; norm; fun y ↦ fderiv ℝ problem y] x) +
            quadraticallyRegularizedObjective (fun _ : E ↦ 0) (L : ℝ) x := by
      funext y
      simp [objective, quadraticallyRegularizedObjective_apply]
    rw [hsplit]
    exact
      (quadraticallyRegularizedObjective_zero_strongConvexOn x (L : ℝ)).add_convexOn
        (modifiedGaussNewtonLocalModel_convex
          problem
          norm
          (fun y ↦ fderiv ℝ problem y)
          (IsSharpMeritFunction.convex (φ := norm))
          x)
  have hbdd :
      BddBelow (objective '' Set.univ) := by
    refine ⟨0, ?_⟩
    rintro z ⟨y, -, rfl⟩
    -- Both the norm-model term and the positive quadratic penalty are nonnegative.
    unfold objective
    simp [quadraticallyRegularizedObjective_apply, modifiedGaussNewtonLocalModel_apply,
      meritFunctionReformulation_apply, hL_pos.le]
  obtain ⟨y, -, hy_min⟩ :=
    SmoothMinimaxProblem.exists_isMinOn_of_isClosed_of_complete_of_bddBelow
      isClosed_univ
      Set.univ_nonempty
      hobjective_cont.continuousOn
      hstrong
      hL_pos
      hbdd
  exact ⟨⟨y, mem_constrainedArgmin_iff.mpr ⟨by simp, hy_min⟩⟩⟩

/-- Helper for Theorem 4.4.4: the fixed regularization value `L` is an admissible lower and upper
parameter bound for a constant-regularization modified Gauss--Newton method. -/
lemma constant_regularization_mem_Ioc
    (L : NNReal)
    (hL_pos : 0 < (L : ℝ)) :
    (L : ℝ) ∈ Set.Ioc (0 : ℝ) (L : ℝ) := by
  exact ⟨hL_pos, le_rfl⟩

/-- Helper for Theorem 4.4.4: the constant regularization rule `M_k ≡ L` stays in the admissible
interval `[L, 2L]`. -/
lemma constant_regularization_mem_Icc
    (L : NNReal)
    (hL_pos : 0 < (L : ℝ)) :
    ∀ k : ℕ, (fun _ : ℕ ↦ (L : ℝ)) k ∈ Set.Icc (L : ℝ) (2 * (L : ℝ)) := by
  intro k
  constructor
  · exact le_rfl
  · nlinarith [hL_pos]

/-- Helper for Theorem 4.4.4: under the whole-space Jacobian-Lipschitz hypothesis, every trial
point of a fixed-`L` modified Gauss--Newton step satisfies the standard merit/model comparison. -/
lemma constant_regularization_step_value_le_modelValue
    (L : NNReal)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (step : ModifiedGaussNewtonStep
      (ψ[problem; norm; fun y ↦ fderiv ℝ problem y]) Set.univ (L : ℝ))
    (x : E) :
    f (step.point x) ≤ (f[step]) x := by
  have hdisc :=
    abs_meritFunctionReformulation_sub_modifiedGaussNewtonLocalModel_le
      problem
      norm
      (IsSharpMeritFunction.lipschitz_one (φ := norm))
      convex_univ
      hJacobianLipschitz
      (by simp : x ∈ (Set.univ : Set E))
      (by simp : step.point x ∈ (Set.univ : Set E))
  have hupper_abs :
      meritFunctionReformulation problem norm (step.point x) -
          (ψ[problem; norm; fun y ↦ fderiv ℝ problem y]) x (step.point x) ≤
        ((L : ℝ) / 2) * ‖step.point x - x‖ ^ (2 : ℕ) := by
    exact (abs_le.mp hdisc).2
  have hupper :
      f (step.point x) ≤
        (ψ[problem; norm; fun y ↦ fderiv ℝ problem y]) x (step.point x) +
          ((L : ℝ) / 2) * ‖step.point x - x‖ ^ (2 : ℕ) := by
    linarith
  simpa [f, ModifiedGaussNewtonStep.modelValueAtUniv_def,
    ModifiedGaussNewtonStep.residualAtUniv_def, quadraticallyRegularizedObjective_apply] using
    hupper

/-- Helper for Theorem 4.4.4: a positive Jacobian-Lipschitz constant yields a modified
Gauss--Newton method with the fixed regularization rule `M_k ≡ L`. -/
lemma constant_regularization_method_exists
    (L : NNReal)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hL_pos : 0 < (L : ℝ)) :
    ∃ method : ModifiedGaussNewtonMethod problem norm (L : ℝ) (L : ℝ) x0,
      ∀ k : ℕ, method.regularization k = (L : ℝ) := by
  classical
  let step :
      ModifiedGaussNewtonStep
        (ψ[problem; norm; fun y ↦ fderiv ℝ problem y])
        Set.univ
        (L : ℝ) :=
    { minimizer := fun x ↦
        Classical.choice
          (constant_regularization_argmin_nonempty
            (problem := problem)
            L
            hL_pos
            x) }
  let method : ModifiedGaussNewtonMethod problem norm (L : ℝ) (L : ℝ) x0 :=
    { regularization := fun _ ↦ (L : ℝ)
      step := fun _ ↦ step
      L0_mem_Ioc := constant_regularization_mem_Ioc L hL_pos
      regularization_mem_Icc := constant_regularization_mem_Icc L hL_pos
      step_value_le_modelValue := fun k ↦
        constant_regularization_step_value_le_modelValue
          (problem := problem)
          L
          hJacobianLipschitz
          step
          (modifiedGaussNewtonIterates x0 (fun _ ↦ (L : ℝ)) (fun _ ↦ step) k) }
  exact ⟨method, fun _ ↦ rfl⟩

/-- Helper for Theorem 4.4.4: in the positive-`L` branch, one merit drop controls one orbit step
linearly with coefficient `2 / σ`. -/
lemma stepNorm_le_two_mul_meritDrop_div_sigma
    (L : NNReal)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem norm x0 σ)
    (hL_pos : 0 < (L : ℝ))
    (method : ModifiedGaussNewtonMethod problem norm (L : ℝ) (L : ℝ) x0)
    (hregularization : ∀ k : ℕ, method.regularization k = (L : ℝ)) :
    ∀ k : ℕ,
      ‖method (k + 1) - method k‖ ≤
        (2 / σ) * (f (method k) - f (method (k + 1))) := by
  intro k
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hstep_residual :
      ‖method (k + 1) - method k‖ ≤ ‖problem (method k)‖ / σ := by
    -- The accepted-step norm is controlled by the current residual through Assumption 4.4.3.
    simpa using
      modifiedGaussNewton_step_norm_le_residual_div_sigma
        (problem := problem) (φ := norm) (L0 := (L : ℝ)) (L := L)
        (x0 := x0) (σ := σ)
        method hσ k
  have hquad_drop :
      ((L : ℝ) / 2) * ‖method (k + 1) - method k‖ ^ (2 : ℕ) ≤
        f (method k) - f (method (k + 1)) := by
    -- The universal residual-square estimate gives the quadratic lower bound on the same drop.
    simpa [hregularization k, method.x_succ k, ModifiedGaussNewtonStep.residualAtUniv_def,
      norm_sub_rev] using
      (method.meritFunction_sub_succ_ge_half_mul_residual_sq k)
  by_cases hlarge :
      ((σ ^ (2 : ℕ)) / (L : ℝ)) ≤ f (method k)
  · have hlarge_drop :
        f (method (k + 1)) ≤
          f (method k) - ((σ ^ (2 : ℕ)) / (2 * (L : ℝ))) := by
      simpa using
        modifiedGaussNewton_fixed_regularization_large_value_oneStep_decrease
          (problem := problem) (φ := norm) (𝓕 := Set.univ) (L0 := (L : ℝ)) (L := L)
          (x0 := x0) (σ := σ) (γφ := 1)
          method convex_univ hJacobianLipschitz
          (by intro x hx; simp) hσ
          (by norm_num) (fun u ↦ by simp) hregularization k
          (by simpa using hlarge)
    have hdrop_const :
        ((σ ^ (2 : ℕ)) / (2 * (L : ℝ))) ≤ f (method k) - f (method (k + 1)) := by
      linarith
    by_cases hsmall_step : ‖method (k + 1) - method k‖ ≤ σ / (L : ℝ)
    · have hscaled :
          (σ / 2 : ℝ) * ‖method (k + 1) - method k‖ ≤
            ((σ ^ (2 : ℕ)) / (2 * (L : ℝ))) := by
        nlinarith
      exact (le_div_iff₀ hσ_pos).2 <| by
        linarith
    · have hlarge_step : σ / (L : ℝ) ≤ ‖method (k + 1) - method k‖ :=
        le_of_not_ge hsmall_step
      have hscaled :
          (σ / 2 : ℝ) * ‖method (k + 1) - method k‖ ≤
            ((L : ℝ) / 2) * ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
        nlinarith
      exact (le_div_iff₀ hσ_pos).2 <| by
        linarith
  · have hsmall :
        f (method k) < ((σ ^ (2 : ℕ)) / (L : ℝ)) := lt_of_not_ge hlarge
    have hsmall_decay :
        f (method (k + 1)) ≤
          ((L : ℝ) / (2 * σ ^ (2 : ℕ) * (1 : ℝ) ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) := by
      simpa using
        modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay
          (problem := problem) (φ := norm) (𝓕 := Set.univ) (L0 := (L : ℝ)) (L := L)
          (x0 := x0) (σ := σ) (γφ := 1)
          method convex_univ hJacobianLipschitz
          (by intro x hx; simp) hσ
          (by norm_num) (fun u ↦ by simp) hregularization k
          (by simpa using hsmall)
    have hhalf_current :
        ((L : ℝ) / (2 * σ ^ (2 : ℕ) * (1 : ℝ) ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) ≤
          (1 / 2 : ℝ) * f (method k) := by
      simpa using
        modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay_le_half_current
          (problem := problem) (φ := norm) (L0 := (L : ℝ)) (L := L)
          (x0 := x0) (σ := σ) (γφ := 1)
          method k
          (by simpa using hsmall)
    have hdrop_half :
        (1 / 2 : ℝ) * f (method k) ≤ f (method k) - f (method (k + 1)) := by
      linarith
    exact (le_div_iff₀ hσ_pos).2 <| by
      have hscaled :
          (σ / 2 : ℝ) * ‖method (k + 1) - method k‖ ≤ (1 / 2 : ℝ) * f (method k) := by
        have hσstep :
            σ * ‖method (k + 1) - method k‖ ≤ f (method k) := by
          simpa [f, meritFunctionReformulation_apply, mul_comm, mul_left_comm, mul_assoc] using
            (le_div_iff₀ hσ_pos).1 hstep_residual
        nlinarith
      linarith

/-- Helper for Theorem 4.4.4: in the positive-regularization branch, the fixed-`L` orbit
converges to an exact solution and stays inside the final distance bound ball around `x₀`. -/
lemma fixed_regularization_two_phase_solution_distance
    (L : NNReal)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem norm x0 σ)
    (hL_pos : 0 < (L : ℝ)) :
    ∃ xStar : E,
      xStar ∈ solutionSet problem ∧
        ‖xStar - x0‖ ≤ (2 / σ) * ‖problem x0‖ := by
  rcases constant_regularization_method_exists
    (problem := problem) (x0 := x0)
    L hJacobianLipschitz hL_pos with ⟨method, hregularization⟩
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hresidual_summable :
      Summable (fun k : ℕ ↦ ‖problem (method k)‖) := by
    -- Reuse the chapter summability theorem instead of rebuilding the capped-tail argument.
    simpa using
      modifiedGaussNewton_nonlinearResidual_summable
        (problem := problem) (φ := norm) (L0 := (L : ℝ)) (L := L)
        (x0 := x0) (σ := σ)
        method hσ
  have hstep_bound :
      ∀ k : ℕ,
        dist (method k) (method (k + 1)) ≤ ‖problem (method k)‖ / σ := by
    intro k
    calc
      dist (method k) (method (k + 1)) =
          ‖method (k + 1) - method k‖ := by
            rw [dist_eq_norm]
            simpa using norm_sub_rev (method k) (method (k + 1))
      _ ≤ ‖problem (method k)‖ / σ :=
        modifiedGaussNewton_step_norm_le_residual_div_sigma
          (problem := problem) (φ := norm) (L0 := (L : ℝ)) (L := L)
          (x0 := x0) (σ := σ)
          method hσ k
  have hstep_summable :
      Summable (fun k : ℕ ↦ ‖problem (method k)‖ / σ) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hresidual_summable.mul_left (σ⁻¹)
  have hcauchy : CauchySeq method :=
    cauchySeq_of_dist_le_of_summable
      (fun k : ℕ ↦ ‖problem (method k)‖ / σ)
      hstep_bound
      hstep_summable
  rcases cauchySeq_tendsto_of_isComplete
      (by simpa using (isComplete_univ : IsComplete (Set.univ : Set E)))
      (fun _ ↦ by simp)
      hcauchy with
    ⟨xStar, -, hxtendsto⟩
  have hnorm_zero :
      Tendsto (fun k : ℕ ↦ ‖problem (method k)‖) atTop (𝓝 0) :=
    hresidual_summable.tendsto_atTop_zero
  have hproblem_zero :
      Tendsto (fun k : ℕ ↦ problem (method k)) atTop (𝓝 (0 : F)) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_zero
  have hproblem_limit :
      Tendsto (fun k : ℕ ↦ problem (method k)) atTop (𝓝 (problem xStar)) :=
    (problem.continuous.tendsto xStar).comp hxtendsto
  have hxStar_zero : problem xStar = 0 := by
    exact tendsto_nhds_unique hproblem_limit hproblem_zero
  have hxStar_mem : xStar ∈ solutionSet problem := by
    rw [mem_solutionSet_iff]
    exact hxStar_zero
  have hstep_drop :
      ∀ k : ℕ,
        (σ / 2 : ℝ) * ‖method (k + 1) - method k‖ ≤
          f (method k) - f (method (k + 1)) := by
    intro k
    have hstep :
        ‖method (k + 1) - method k‖ ≤
          (2 / σ) * (f (method k) - f (method (k + 1))) :=
      stepNorm_le_two_mul_meritDrop_div_sigma
        (problem := problem) (x0 := x0) (σ := σ)
        L hJacobianLipschitz hσ hL_pos method hregularization k
    nlinarith
  obtain ⟨hstep_norm_summable, hgap⟩ :=
    tail_summable_and_gap_ge_tsum_of_one_step_decrease
      (problem := problem) (φ := norm) (L0 := (L : ℝ)) (L := (L : ℝ)) (x0 := x0)
      method
      (fStar := 0)
      (hf_lower := fun z ↦ by
        simpa [f, meritFunctionReformulation_apply] using
          (IsMeritFunction.nonneg (φ := norm) (problem z)))
      (c := σ / 2)
      (by positivity)
      0
      (fun k ↦ ‖method (k + 1) - method k‖)
      (fun _ ↦ norm_nonneg _)
      (by
        intro k
        simpa [Nat.zero_add] using hstep_drop k)
  have hdist_tsum :
      dist x0 xStar ≤ ∑' k, ‖method (k + 1) - method k‖ := by
    simpa [method.x_zero, dist_eq_norm, norm_sub_rev] using
      dist_le_tsum_of_dist_le_of_tendsto₀
        (fun k ↦ ‖method (k + 1) - method k‖)
        (fun k ↦ by
          rw [dist_eq_norm]
          simp [norm_sub_rev])
        hstep_norm_summable
        hxtendsto
  have htsum_bound :
      ∑' k, ‖method (k + 1) - method k‖ ≤ (2 / σ) * ‖problem x0‖ := by
    have hfx0 :
        f x0 = ‖problem x0‖ := by
      simp [f, meritFunctionReformulation_apply]
    have hmul :
        (σ / 2 : ℝ) * ∑' k, ‖method (k + 1) - method k‖ ≤ ‖problem x0‖ := by
      simpa [method.x_zero, hfx0] using hgap
    exact (le_div_iff₀ hσ_pos).2 <| by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  refine ⟨xStar, hxStar_mem, ?_⟩
  calc
    ‖xStar - x0‖ = dist x0 xStar := by rw [dist_eq_norm, norm_sub_rev]
    _ ≤ ∑' k, ‖method (k + 1) - method k‖ := hdist_tsum
    _ ≤ (2 / σ) * ‖problem x0‖ := htsum_bound

-- Proof sketch: apply the global modified Gauss--Newton method to the norm-merit reformulation
-- `x ↦ ‖problem x‖` with constant regularization `M_k = L`. The whole-space Jacobian-Lipschitz
-- hypothesis supplies the smooth residual-map owner needed for the chapter Taylor-remainder and
-- one-step decrease estimates, while Assumption 4.4.3 controls the same norm-merit sublevel set.
-- The fixed-`L` orbit satisfies the chapter one-step decrease estimate, which yields the
-- prefix-distance bound by telescoping the merit drops. A local fixed-`L` summability argument
-- then yields convergence to an exact solution, and the closed-ball bound passes to the limit.
-- Hence
-- `‖xStar - x0‖ ≤ (2 / σ) * ‖problem x0‖`.
/-- Theorem 4.4.4: if the residual map `problem` has `L`-Lipschitz Jacobian on `Set.univ` and
Assumption 4.4.3 holds on the initial sublevel set of the norm-merit reformulation
`x ↦ ‖problem x‖`, then there exists an exact solution `x* ∈ solutionSet problem` whose distance
from the initial point is bounded by `(2 / σ) * ‖problem x₀‖`. -/
theorem exists_exact_solution_dist_le_two_div_sigma_mul_initialResidual
    (L : NNReal)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem norm x0 σ) :
    ∃ xStar : E,
      xStar ∈ solutionSet problem ∧
        ‖xStar - x0‖ ≤ (2 / σ) * ‖problem x0‖ := by
  by_cases hL0 : (L : ℝ) = 0
  · -- In the degenerate branch, the residual map is globally affine, so one controlled solve at
    -- `x₀` already gives an exact solution with the stronger distance estimate.
    rcases exact_solution_of_zero_jacobian_lipschitz
      (problem := problem) (x0 := x0) (σ := σ)
      L hJacobianLipschitz hσ hL0 with ⟨xStar, hxStar, hdist⟩
    refine ⟨xStar, hxStar, ?_⟩
    exact one_over_sigma_bound_le_two_over_sigma_bound
      (problem := problem) (x0 := x0) (σ := σ) hσ hdist
  · have hL_pos : 0 < (L : ℝ) := by
      exact lt_of_le_of_ne (show 0 ≤ (L : ℝ) by exact_mod_cast L.2) (Ne.symm hL0)
    exact fixed_regularization_two_phase_solution_distance
      (problem := problem) (x0 := x0) (σ := σ)
      L hJacobianLipschitz hσ hL_pos

end
