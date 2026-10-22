/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Assumption_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Assumption_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Assumption_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open ModifiedGaussNewtonStep
open SmoothNonlinearEquationProblem
open scoped InnerProduct LevelSetNotation Manifold MinimalSingularValue
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonLocalDecreaseNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation
open scoped Topology

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- Theorem 4.4.5 lies in the global modified Gauss--Newton convergence domain.

Sampled owner-style declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate sequence
  and accepted-step dynamics;
* `HasLipschitzDerivativeOnWith` in `Assumption_4_4_1`, the source-facing whole-space
  first-order smoothness owner for the merit reformulation;
* `HasUniformDualNondegeneracyOnInitialSublevelSet` in `Assumption_4_4_3`, the source-facing
  nondegeneracy owner on the initial merit sublevel set;
* `SmoothNonlinearEquationProblem.solutionSet` in `Definition_4_4_8`, the chapter owner for the
  exact-solution locus `problem x = 0`;
* `cubicRegularizationNewton_iterates_tendsto_unique_feasible_limit` in `Theorem_4_1_3_3`, the
  chapter owner-style unique-limit theorem stated as set membership plus convergence;
* the bundled smooth-map owner `C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯` recalled in
  `Definition_4_4_8`.

Best owner abstraction:
* source-facing: convergence of a modified Gauss--Newton trajectory to an exact solution;
* core/canonical: a bundled smooth residual map, a sharp merit function, a method, and the
  chapter assumption owners already defined upstream together with the exact-solution owner
  `solutionSet problem`;
* bridge/view: the whole-space specialization, where Assumption 4.4.2 is automatic because the
  feasible set is `Set.univ`, and `mem_solutionSet_iff` translates set membership back to the
  textbook equation `problem x = 0`.

Primitive data:
* the smooth residual map `problem`;
* the sharp merit function `φ`;
* the modified Gauss--Newton method `method`;
* the whole-space assumptions `HasLipschitzDerivativeOnWith` and
  `HasUniformDualNondegeneracyOnInitialSublevelSet`.

Derived API:
* the merit reformulation `f = meritFunctionReformulation problem φ`;
* the convergence and exact-solution conclusion.

This item stays source-facing, but its ambient space is refined from the coordinate model
`EuclideanSpace ℝ (Fin n)` to the intrinsic owner layer already used by the chapter's algorithm
and assumption declarations. Since `IsSufficientlyLargeFeasibleSetAt f Set.univ x₀` is
definitionally automatic, that redundant whole-space hypothesis is removed from the theorem
interface. The conclusion is also refined from the raw equation `problem xStar = 0` to the
chapter owner `xStar ∈ solutionSet problem`, matching the existing unique-limit theorem surface
used elsewhere in the chapter.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {L0 : ℝ} {L : NNReal} {x0 : E₁} {σ : ℝ}

local notation "f" => meritFunctionReformulation problem φ
local notation "𝓢" => solutionSet problem
local notation "𝓛0" => (𝓛[f]((f x0)) : Set E₁)

/-- Helper for Theorem 4.4.5: the accepted modified Gauss--Newton steps never increase the merit
value, so every iterate remains in the initial sublevel set. -/
lemma modifiedGaussNewton_mem_initial_sublevel
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0) :
    ∀ k : ℕ, method k ∈ 𝓛0 := by
  intro k
  induction k with
  | zero =>
      -- The initial iterate is exactly `x₀`, so it lies in its own initial sublevel set.
      rw [mem_levelSet_iff]
      simp
  | succ k ih =>
      rw [mem_levelSet_iff] at ih ⊢
      -- The accepted step value is bounded by its model value, which is bounded by the current
      -- merit value on the whole-space feasible set.
      exact le_trans
        (le_trans (method.step_value_le_modelValue k) (method.step_modelValue_le_merit k))
        ih

/-- Helper for Theorem 4.4.5: a positive lower bound on the dual minimal singular value of a real
Hilbert-space operator yields a controlled preimage for every right-hand side. -/
lemma exists_preimage_norm_le_of_adjoint_minimalSingularValue_pos
    (A : E₁ →L[ℝ] E₂)
    (hA : 0 < σ_min(A†))
    (b : E₂) :
    ∃ x : E₁, A x = b ∧ ‖x‖ ≤ ‖b‖ / σ_min(A†) := by
  let B : E₂ →L[ℝ] E₂ →L[ℝ] ℝ :=
    (ContinuousLinearMap.toSesqForm (A†)).comp (A†)
  have hcoercive : IsCoercive B := by
    -- Coercivity comes from the pointwise lower bound attached to `σ_min(A†)`.
    refine ⟨σ_min(A†) ^ (2 : ℕ), by positivity, ?_⟩
    intro u
    change σ_min(A†) ^ (2 : ℕ) * ‖u‖ * ‖u‖ ≤ inner ℝ ((A†) u) ((A†) u)
    rw [inner_self_eq_norm_sq_to_K]
    have hbound : σ_min(A†) * ‖u‖ ≤ ‖(A†) u‖ := by
      simpa using (A†).minimalSingularValue_mul_norm_le u
    have hsq : (σ_min(A†) * ‖u‖) ^ (2 : ℕ) ≤ ‖(A†) u‖ ^ (2 : ℕ) := by
      exact
        (sq_le_sq₀
          (mul_nonneg (minimalSingularValue_nonneg (A†)) (norm_nonneg _))
          (norm_nonneg _)).2
          hbound
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  have hsurj :
      (InnerProductSpace.continuousLinearMapOfBilin B).range = ⊤ :=
    IsCoercive.range_eq_top hcoercive
  obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hsurj b
  have hoperator :
      InnerProductSpace.continuousLinearMapOfBilin B y = A ((A†) y) := by
    -- The Lax--Milgram operator of `B` is exactly `A ∘ A†`.
    apply ext_inner_right ℝ
    intro v
    rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
    calc
      (B y) v = inner ℝ ((A†) y) ((A†) v) := by
        simp [B, ContinuousLinearMap.toSesqForm_apply_coe]
      _ = inner ℝ (A ((A†) y)) v := by
        simpa using A.adjoint_inner_right ((A†) y) v
  have hAy : A ((A†) y) = b := by
    simpa [hoperator] using hy
  refine ⟨(A†) y, hAy, ?_⟩
  have hy_bound : σ_min(A†) * ‖y‖ ≤ ‖(A†) y‖ := by
    simpa using (A†).minimalSingularValue_mul_norm_le y
  have hx_sq_le : ‖(A†) y‖ ^ (2 : ℕ) ≤ ‖y‖ * ‖b‖ := by
    calc
      ‖(A†) y‖ ^ (2 : ℕ) = ‖inner ℝ ((A†) y) ((A†) y)‖ := by
        simp [inner_self_eq_norm_sq_to_K]
      _ = ‖inner ℝ y (A ((A†) y))‖ := by
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ ≤ ‖y‖ * ‖A ((A†) y)‖ := norm_inner_le_norm _ _
      _ = ‖y‖ * ‖b‖ := by rw [hAy]
  have hx_bound : σ_min(A†) * ‖(A†) y‖ ≤ ‖b‖ := by
    -- Combine the coercive solve with the adjoint lower bound and cancel the auxiliary vector.
    have hsq_mul :
        σ_min(A†) * ‖(A†) y‖ ^ (2 : ℕ) ≤ ‖b‖ * ‖(A†) y‖ := by
      calc
        σ_min(A†) * ‖(A†) y‖ ^ (2 : ℕ) ≤ σ_min(A†) * (‖y‖ * ‖b‖) := by
          gcongr
        _ = ‖b‖ * (σ_min(A†) * ‖y‖) := by ring
        _ ≤ ‖b‖ * ‖(A†) y‖ := by
          gcongr
    by_cases hy_zero : (A†) y = 0
    · simp [hy_zero]
    · have hy_pos : 0 < ‖(A†) y‖ := norm_pos_iff.mpr hy_zero
      exact le_of_mul_le_mul_right
        (by simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq_mul)
        hy_pos
  exact (le_div_iff₀ hA).2 <| by
    simpa [mul_comm] using hx_bound

/-- Helper for Theorem 4.4.5: every modified Gauss--Newton step is controlled by the current
nonlinear residual divided by the uniform dual nondegeneracy constant `σ`. -/
lemma modifiedGaussNewton_step_norm_le_residual_div_sigma
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ) :
    ∀ k : ℕ, ‖method (k + 1) - method k‖ ≤ ‖problem (method k)‖ / σ := by
  intro k
  have hmem : method k ∈ 𝓛0 :=
    modifiedGaussNewton_mem_initial_sublevel (method := method) k
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hdual_lower :
      σ ≤ σ_min((fderiv ℝ problem (method k))†) :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.lower_bound hσ hmem
  have hdual_pos : 0 < σ_min((fderiv ℝ problem (method k))†) := by
    exact lt_of_lt_of_le hσ_pos hdual_lower
  have hstep :
      ‖(method.step k).point (method k) - method k‖ ≤
        ‖problem (method k)‖ / σ_min((fderiv ℝ problem (method k))†) := by
    -- Use the controlled exact preimage of the linearized residual at the current iterate.
    let A : E₁ →L[ℝ] E₂ := fderiv ℝ problem (method k)
    obtain ⟨h, hh, hbound⟩ :=
      exists_preimage_norm_le_of_adjoint_minimalSingularValue_pos
        (A := A) hdual_pos (-problem (method k))
    have hh' : fderiv ℝ problem (method k) h = -problem (method k) := by
      simpa [A] using hh
    have hzero :
        problem (method k) + fderiv ℝ problem (method k) h = 0 := by
      rw [hh']
      simp
    have hmin :
        f[(method.step k)] (method k) ≤
          quadraticallyRegularizedObjective
            (ψ[problem; φ; fun y ↦ fderiv ℝ problem y] (method k))
            (method.regularization k)
            (method k)
            (method k + h) := by
      -- The selected step minimizes the regularized local model globally.
      simpa [ModifiedGaussNewtonStep.modelValueAtUniv_def,
        ModifiedGaussNewtonStep.residualAtUniv_def, quadraticallyRegularizedObjective_apply] using
        (isMinOn_univ_iff.mp (method.step_isMinOn k)) (method k + h)
    have hleft :
        (method.regularization k / 2 : ℝ) * ‖(method.step k).point (method k) - method k‖ ^ (2 : ℕ) ≤
          f[(method.step k)] (method k) := by
      -- Nonnegativity of the sharp merit isolates the quadratic term at the minimizer.
      have hnonneg :
          0 ≤
            meritFunctionReformulation
              (fun y ↦ problem (method k) + fderiv ℝ problem (method k) (y - method k))
              φ
              ((method.step k).point (method k)) := by
        simpa [meritFunctionReformulation_apply] using
          (IsMeritFunction.nonneg (φ := φ)
            (problem (method k) +
              fderiv ℝ problem (method k) ((method.step k).point (method k) - method k)))
      have hle :
          (method.regularization k / 2 : ℝ) *
              ‖(method.step k).point (method k) - method k‖ ^ (2 : ℕ) ≤
            meritFunctionReformulation
                (fun y ↦ problem (method k) + fderiv ℝ problem (method k) (y - method k))
                φ
                ((method.step k).point (method k)) +
              (method.regularization k / 2 : ℝ) *
                ‖(method.step k).point (method k) - method k‖ ^ (2 : ℕ) := by
        linarith
      simpa [ModifiedGaussNewtonStep.modelValueAtUniv_def,
        ModifiedGaussNewtonStep.residualAtUniv_def, modifiedGaussNewtonLocalModel_apply,
        meritFunctionReformulation_apply] using hle
    have hφ_zero : φ 0 = 0 := by
      simpa using (IsMeritFunction.eq_zero_iff (φ := φ) (0 : E₂)).2 rfl
    have hright :
        quadraticallyRegularizedObjective
            (ψ[problem; φ; fun y ↦ fderiv ℝ problem y] (method k))
            (method.regularization k)
            (method k)
            (method k + h) =
          (method.regularization k / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) := by
      -- The exact linearized correction sends the local-model residual to zero.
      simp [quadraticallyRegularizedObjective_apply, modifiedGaussNewtonLocalModel_apply,
        meritFunctionReformulation_apply, hzero, hφ_zero]
    have hquad :
        (method.regularization k / 2 : ℝ) *
            ‖(method.step k).point (method k) - method k‖ ^ (2 : ℕ) ≤
          (method.regularization k / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) := by
      calc
        (method.regularization k / 2 : ℝ) *
            ‖(method.step k).point (method k) - method k‖ ^ (2 : ℕ) ≤
          f[(method.step k)] (method k) := hleft
        _ ≤
            quadraticallyRegularizedObjective
              (ψ[problem; φ; fun y ↦ fderiv ℝ problem y] (method k))
              (method.regularization k)
              (method k)
              (method k + h) := hmin
        _ = (method.regularization k / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) := hright
    have hsq :
        ‖(method.step k).point (method k) - method k‖ ^ (2 : ℕ) ≤ ‖h‖ ^ (2 : ℕ) := by
      nlinarith [method.regularization_pos k, hquad]
    have hstep_le : ‖(method.step k).point (method k) - method k‖ ≤ ‖h‖ := by
      nlinarith [hsq, norm_nonneg ((method.step k).point (method k) - method k), norm_nonneg h]
    exact hstep_le.trans hbound
  have hcompare :
      ‖problem (method k)‖ / σ_min((fderiv ℝ problem (method k))†) ≤
        ‖problem (method k)‖ / σ := by
    exact div_le_div_of_nonneg_left (norm_nonneg _) hσ_pos.le hdual_lower
  simpa [method.x_succ k, norm_sub_rev] using hstep.trans hcompare

/-- Helper for Theorem 4.4.5: sharpness of `φ` upgrades the local-model decrease on the initial
sublevel set to the lower bound `(σ γ) r ≤ Δ_r(x)`. -/
lemma modifiedGaussNewton_localDecrease_ge_sigma_gamma_mul_radius
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    {γ : ℝ}
    (hγ_mem : γ ∈ Set.Ioc (0 : ℝ) 1)
    (hγ_lower : ∀ u : E₂, γ * ‖u‖ ≤ φ u)
    {x : E₁}
    (hx : x ∈ 𝓛0)
    (r : NNReal)
    (hr : (r : ℝ) ≤ ‖problem x‖ / (σ * γ)) :
    (σ * γ) * (r : ℝ) ≤ Δ[problem; φ; r](x) := by
  let model : E₁ → ℝ := ψ[problem; φ; fun y ↦ fderiv ℝ problem y] x
  let S : Set ℝ := model '' Metric.closedBall x r
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hγ_pos : 0 < γ := hγ_mem.1
  have hσγ_pos : 0 < σ * γ := mul_pos hσ_pos hγ_pos
  have hS_bdd : BddBelow S := by
    -- The modified Gauss--Newton local model is nonnegative on the whole ball.
    simpa [S, model] using
      bddBelow_image_closedBall_of_nonneg
        (ψ[problem; φ; fun y ↦ fderiv ℝ problem y]) r
        (fun x' y ↦ by
          simp [modifiedGaussNewtonLocalModel_apply])
        x
  have hdelta :
      Δ[problem; φ; r](x) = f x - sInf S := by
    -- Rewrite the local decrease through the closed-ball infimum formula.
    simpa [S, model, f, meritFunctionReformulation_apply] using
      localModelDecreaseAt_eq_sub_sInf_of_bddBelow
        (meritFunctionReformulation problem φ)
        (ψ[problem; φ; fun y ↦ fderiv ℝ problem y])
        r x hS_bdd
  by_cases hFx : problem x = 0
  · -- A zero residual forces radius `r = 0`, so only nonnegativity of `Δ_r(x)` remains.
    have hr_le_zero : (r : ℝ) ≤ 0 := by
      simpa [hFx] using hr
    have hr_zero : (r : ℝ) = 0 :=
      le_antisymm hr_le_zero r.2
    rw [hr_zero, mul_zero]
    exact modifiedGaussNewton_localDecrease_nonneg problem φ r x
  · have hdual_lower :
        σ ≤ σ_min((fderiv ℝ problem x)†) :=
      HasUniformDualNondegeneracyOnInitialSublevelSet.lower_bound hσ hx
    have hdual_pos : 0 < σ_min((fderiv ℝ problem x)†) := by
      exact lt_of_lt_of_le hσ_pos hdual_lower
    have hFx_pos : 0 < ‖problem x‖ :=
      norm_pos_iff.mpr hFx
    let A : E₁ →L[ℝ] E₂ := fderiv ℝ problem x
    obtain ⟨h, hh, hbound⟩ :=
      exists_preimage_norm_le_of_adjoint_minimalSingularValue_pos
        (A := A) hdual_pos (-problem x)
    have hh' : fderiv ℝ problem x h = -problem x := by
      simpa [A] using hh
    have hbound_sigma : ‖h‖ ≤ ‖problem x‖ / σ := by
      -- Compare the exact correction bound with the weaker denominator `σ`.
      refine hbound.trans ?_
      exact div_le_div_of_nonneg_left (norm_nonneg _) hσ_pos.le hdual_lower
    let t : ℝ := (r : ℝ) * σ / ‖problem x‖
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (mul_nonneg r.2 hσ_pos.le) (norm_nonneg _)
    have ht_le_one : t ≤ 1 := by
      -- The radius hypothesis is precisely the condition `t ≤ 1/γ`, then `γ ≤ 1` yields `t ≤ 1`.
      dsimp [t]
      have hmul : (r : ℝ) * σ * γ ≤ ‖problem x‖ := by
        exact (le_div_iff₀ hσγ_pos).1 hr
      have hmul' : (r : ℝ) * σ ≤ ‖problem x‖ := by
        have hγ_le_one : γ ≤ 1 := hγ_mem.2
        have hγ_nonneg : 0 ≤ γ := hγ_pos.le
        by_cases hγ_zero : γ = 0
        · linarith
        · have hdiv : (r : ℝ) * σ ≤ ‖problem x‖ / γ := by
            exact (le_div_iff₀ hγ_pos).2 hmul
          have hbound_one_div : ‖problem x‖ / γ ≤ ‖problem x‖ := by
            exact div_le_self (norm_nonneg _) hγ_nonneg hγ_le_one
          exact hdiv.trans hbound_one_div
      exact (div_le_iff₀ hFx_pos).2 hmul'
    let y : E₁ := x + t • h
    have hy_sub : y - x = t • h := by
      simp [y]
    have hyBall : y ∈ Metric.closedBall x r := by
      -- The scaled correction stays inside the radius-`r` closed ball.
      have hy_norm : ‖y - x‖ ≤ (r : ℝ) := by
        calc
          ‖y - x‖ = t * ‖h‖ := by
            rw [hy_sub, norm_smul, Real.norm_of_nonneg ht_nonneg]
          _ ≤ t * (‖problem x‖ / σ) := by
            exact mul_le_mul_of_nonneg_left hbound_sigma ht_nonneg
          _ = (r : ℝ) := by
            dsimp [t]
            field_simp [hσ_pos.ne', hFx_pos.ne']
            ring
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy_norm
    have hsInf_le : sInf S ≤ model y := by
      exact csInf_le hS_bdd ⟨y, hyBall, rfl⟩
    have hlin :
        problem x + fderiv ℝ problem x (y - x) = (1 - t) • problem x := by
      calc
        problem x + fderiv ℝ problem x (y - x)
            = problem x + fderiv ℝ problem x (t • h) := by
                rw [hy_sub]
        _ = problem x + t • fderiv ℝ problem x h := by
              rw [map_smul]
        _ = problem x + t • (-problem x) := by
              rw [hh']
        _ = (1 : ℝ) • problem x - t • problem x := by
              simp [sub_eq_add_neg]
        _ = (1 - t) • problem x := by
              rw [sub_smul]
    have hφ_zero : φ 0 = 0 := by
      simpa using (IsMeritFunction.eq_zero_iff (φ := φ) (0 : E₂)).2 rfl
    have hmodel_y :
        model y ≤ (1 - t) * f x := by
      -- Convexity of the sharp merit function controls the scaled residual along the segment to `0`.
      have hconv :
          φ ((1 - t) • problem x + t • (0 : E₂)) ≤
            (1 - t) * φ (problem x) + t * φ (0 : E₂) := by
        simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using
          (IsSharpMeritFunction.convex (φ := φ)).2
            (by simp)
            (by simp)
            (sub_nonneg.mpr ht_le_one)
            ht_nonneg
            (by ring)
      have hmodel_eq :
          model y = φ ((1 - t) • problem x + t • (0 : E₂)) := by
        simp [model, modifiedGaussNewtonLocalModel_apply, hlin]
      rw [hmodel_eq]
      simpa [f, meritFunctionReformulation_apply, hφ_zero] using hconv
    have hsInf_bound :
        sInf S ≤ f x - (σ * γ) * (r : ℝ) := by
      have hγ_scaled : t * (γ * ‖problem x‖) = (σ * γ) * (r : ℝ) := by
        dsimp [t]
        field_simp [hFx_pos.ne']
        ring
      have hsharp : γ * ‖problem x‖ ≤ f x := by
        simpa [f, meritFunctionReformulation_apply] using hγ_lower (problem x)
      have hlinear :
          (1 - t) * f x ≤ f x - (σ * γ) * (r : ℝ) := by
        have : (σ * γ) * (r : ℝ) ≤ t * f x := by
          calc
            (σ * γ) * (r : ℝ) = t * (γ * ‖problem x‖) := by
              rw [hγ_scaled]
              ring
            _ ≤ t * f x := by
              exact mul_le_mul_of_nonneg_left hsharp ht_nonneg
        nlinarith
      exact hsInf_le.trans <| hmodel_y.trans hlinear
    rw [hdelta]
    linarith

/-- Helper for Theorem 4.4.5: each one-step merit drop controls half of the residual capped at
the global threshold `((σ γ)^2) / (2L)`. -/
lemma modifiedGaussNewton_merit_drop_ge_half_min_residual_threshold
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    {γ : ℝ}
    (hγ_mem : γ ∈ Set.Ioc (0 : ℝ) 1)
    (hγ_lower : ∀ u : E₂, γ * ‖u‖ ≤ φ u)
    (k : ℕ) :
    (1 / 2 : ℝ) *
        min ‖problem (method k)‖ (((σ * γ) ^ (2 : ℕ)) / (2 * (L : ℝ))) ≤
      f (method k) - f (method (k + 1)) := by
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hγ_pos : 0 < γ := hγ_mem.1
  have hL_pos : 0 < (L : ℝ) := by
    exact lt_of_lt_of_le method.L0_pos method.L0_le_L
  have hstep :
      f (method (k + 1)) ≤ f[(method.step k)] (method k) := by
    simpa [method.x_succ k] using method.step_value_le_modelValue k
  let threshold : ℝ := ((σ * γ) ^ (2 : ℕ)) / (2 * (L : ℝ))
  by_cases hsmall :
      ‖problem (method k)‖ ≤ ((σ * γ) ^ (2 : ℕ)) / method.regularization k
  · let r : NNReal :=
        ⟨‖problem (method k)‖ / (σ * γ),
          div_nonneg (norm_nonneg _) (mul_nonneg hσ_pos.le hγ_pos.le)⟩
    have hr :
        (r : ℝ) ≤ ‖problem (method k)‖ / (σ * γ) := by
      rfl
    have hΔ :
        ‖problem (method k)‖ ≤ Δ[problem; φ; r]((method k)) := by
      simpa [r, mul_comm, mul_left_comm, mul_assoc] using
        modifiedGaussNewton_localDecrease_ge_sigma_gamma_mul_radius
          (problem := problem) (φ := φ) (L0 := L0) (L := L)
          (x0 := x0) (σ := σ)
          hσ
          hγ_mem
          hγ_lower
          (modifiedGaussNewton_mem_initial_sublevel (method := method) k)
          r
          hr
    have hgap :
        δ[(method.step k); f] (method k) ≥
          Δ[problem; φ; r]((method k)) -
            (method.regularization k / 2 : ℝ) * (r : ℝ) ^ (2 : ℕ) := by
      simpa using
        modifiedGaussNewton_modelGap_ge_scaled_localDecrease
          (problem := problem) (φ := φ)
          (M := method.regularization k)
          (hM := method.regularization_pos k)
          (step := method.step k)
          (x := method k)
          (r := r)
          (t := 1)
          (by norm_num)
          (by norm_num)
    have hquad :
        (method.regularization k / 2 : ℝ) * (r : ℝ) ^ (2 : ℕ) ≤
          ‖problem (method k)‖ / 2 := by
      dsimp [r]
      have hσγ_pos : 0 < σ * γ := mul_pos hσ_pos hγ_pos
      field_simp [hσγ_pos.ne', method.regularization_pos k.ne']
      nlinarith [hsmall]
    have hdrop :
        ‖problem (method k)‖ / 2 ≤ f (method k) - f (method (k + 1)) := by
      rw [ModifiedGaussNewtonStep.modelGapAtUniv_def] at hgap
      have hcore :
          ‖problem (method k)‖ / 2 ≤
            f (method k) - f[(method.step k)] (method k) := by
        linarith [hΔ, hgap, hquad]
      linarith
    calc
      (1 / 2 : ℝ) *
          min ‖problem (method k)‖ threshold
          ≤ ‖problem (method k)‖ / 2 := by
            gcongr
            exact min_le_left _ _
      _ ≤ f (method k) - f (method (k + 1)) := hdrop
  · let r : NNReal :=
        ⟨(σ * γ) / method.regularization k,
          div_nonneg (mul_nonneg hσ_pos.le hγ_pos.le) (method.regularization_pos k).le⟩
    have hthreshold_lt :
        ((σ * γ) ^ (2 : ℕ)) / method.regularization k < ‖problem (method k)‖ := by
      exact lt_of_not_ge hsmall
    have hr :
        (r : ℝ) ≤ ‖problem (method k)‖ / (σ * γ) := by
      dsimp [r]
      have hσγ_pos : 0 < σ * γ := mul_pos hσ_pos hγ_pos
      have := hthreshold_lt
      field_simp [hσγ_pos.ne', method.regularization_pos k.ne'] at this ⊢
      nlinarith
    have hΔ :
        (σ * γ) ^ (2 : ℕ) / method.regularization k ≤ Δ[problem; φ; r]((method k)) := by
      simpa [r, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        modifiedGaussNewton_localDecrease_ge_sigma_gamma_mul_radius
          (problem := problem) (φ := φ) (L0 := L0) (L := L)
          (x0 := x0) (σ := σ)
          hσ
          hγ_mem
          hγ_lower
          (modifiedGaussNewton_mem_initial_sublevel (method := method) k)
          r
          hr
    have hgap :
        δ[(method.step k); f] (method k) ≥
          Δ[problem; φ; r]((method k)) -
            (method.regularization k / 2 : ℝ) * (r : ℝ) ^ (2 : ℕ) := by
      simpa using
        modifiedGaussNewton_modelGap_ge_scaled_localDecrease
          (problem := problem) (φ := φ)
          (M := method.regularization k)
          (hM := method.regularization_pos k)
          (step := method.step k)
          (x := method k)
          (r := r)
          (t := 1)
          (by norm_num)
          (by norm_num)
    have hdrop :
        threshold / 2 ≤ f (method k) - f (method (k + 1)) := by
      rw [ModifiedGaussNewtonStep.modelGapAtUniv_def] at hgap
      have hreg_bound : method.regularization k ≤ 2 * (L : ℝ) :=
        method.regularization_le_two_mul_L k
      have hcore :
          threshold / 2 ≤
            f (method k) - f[(method.step k)] (method k) := by
        dsimp [threshold, r]
        field_simp [hL_pos.ne', method.regularization_pos k.ne']
        nlinarith [hΔ, hgap, hreg_bound]
      linarith
    have hlarge_threshold :
        threshold ≤ ‖problem (method k)‖ := by
      have hreg_bound : method.regularization k ≤ 2 * (L : ℝ) :=
        method.regularization_le_two_mul_L k
      have hσγ_sq_nonneg : 0 ≤ (σ * γ) ^ (2 : ℕ) := by positivity
      dsimp [threshold]
      have hbound :
          ((σ * γ) ^ (2 : ℕ)) / (2 * (L : ℝ)) ≤
            ((σ * γ) ^ (2 : ℕ)) / method.regularization k := by
        exact div_le_div_of_nonneg_left hσγ_sq_nonneg
          (show 0 < method.regularization k by exact method.regularization_pos k)
          hreg_bound
      exact hbound.trans hthreshold_lt.le
    have hmin_eq : min ‖problem (method k)‖ threshold = threshold := by
      exact min_eq_right hlarge_threshold
    simpa [hmin_eq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdrop

/-- Helper for Theorem 4.4.5: the nonlinear residual norms along the modified Gauss--Newton orbit
form a summable series. -/
lemma modifiedGaussNewton_nonlinearResidual_summable
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ) :
    Summable (fun k : ℕ ↦ ‖problem (method k)‖) := by
  obtain ⟨γ, hγ_mem, hγ_lower⟩ := IsSharpMeritFunction.sharp_origin (φ := φ)
  let threshold : ℝ := ((σ * γ) ^ (2 : ℕ)) / (2 * (L : ℝ))
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hγ_pos : 0 < γ := hγ_mem.1
  have hL_pos : 0 < (L : ℝ) := by
    exact lt_of_lt_of_le method.L0_pos method.L0_le_L
  have hthreshold_pos : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hcapped :
      Summable (fun k : ℕ ↦ min ‖problem (method k)‖ threshold) := by
    exact
      (tail_summable_and_gap_ge_tsum_of_one_step_decrease
        (problem := problem) (φ := φ) (L0 := L0) (L := (L : ℝ)) (x0 := x0)
        method
        (fStar := 0)
        (hf_lower := fun z ↦ by
          simpa [f, meritFunctionReformulation_apply] using
            (IsMeritFunction.nonneg (φ := φ) (problem z)))
        (c := 1 / 2)
        (by norm_num)
        0
        (fun k ↦ min ‖problem (method k)‖ threshold)
        (fun k ↦ by positivity)
        (fun k ↦ by
          simpa [threshold, mul_comm, mul_left_comm, mul_assoc] using
            modifiedGaussNewton_merit_drop_ge_half_min_residual_threshold
              (problem := problem) (φ := φ) (L0 := L0) (L := L)
              (x0 := x0) (σ := σ)
              method
              hσ
              hγ_mem
              hγ_lower
              k)).1
  have hcapped_zero :
      Tendsto (fun k : ℕ ↦ min ‖problem (method k)‖ threshold) atTop (𝓝 0) :=
    hcapped.tendsto_atTop_zero
  have heventually_small :
      ∀ᶠ k : ℕ in atTop, ‖problem (method k)‖ < threshold := by
    filter_upwards [hcapped_zero (Set.Iio_mem_nhds hthreshold_pos)] with k hk
    by_contra hnot
    have hlarge : threshold ≤ ‖problem (method k)‖ := not_lt.mp hnot
    have hmin_eq : min ‖problem (method k)‖ threshold = threshold :=
      min_eq_right hlarge
    rw [hmin_eq] at hk
    exact lt_irrefl _ hk
  rcases Filter.eventually_atTop.1 heventually_small with ⟨N, hN⟩
  have htail_capped :
      Summable (fun k : ℕ ↦ min ‖problem (method (N + k))‖ threshold) :=
    (summable_nat_add_iff N).1 hcapped
  have htail :
      Summable (fun k : ℕ ↦ ‖problem (method (N + k))‖) := by
    convert htail_capped using 1
    ext k
    exact min_eq_left_of_lt (hN (N + k) (Nat.le_add_right N k))
  exact (summable_nat_add_iff N).2 htail

-- Proof sketch: invoke the canonical whole-space bridge
-- `IsSufficientlyLargeFeasibleSetAt.univ f x0` to discharge Assumption 4.4.2 on `Set.univ`.
-- The substantive inputs are then the global decrease estimates and vanishing step-difference
-- consequences coming from Assumptions 4.4.1 and 4.4.3 for Algorithm 4.4.1. These show that the
-- modified Gauss--Newton iterates form a Cauchy sequence, hence converge in the complete domain
-- space. Then pass to the limit in the iteration equation and use uniform dual nondegeneracy to
-- conclude that the limit point belongs to the exact-solution set `𝓢`; uniqueness comes from
-- uniqueness of limits in a Hausdorff space.
/-- Theorem 4.4.5: in the whole-space setting, where Assumption 4.4.2 is automatic, any
modified Gauss--Newton sequence generated by Algorithm 4.4.1 for the merit reformulation
`f(x) = φ(F(x))` converges to a unique limit point `x*` in the exact-solution set of `F` under
Assumptions 4.4.1 and 4.4.3. -/
theorem modifiedGaussNewtonMethod_tendsto_unique_solution
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (hLipschitz : HasLipschitzDerivativeOnWith L Set.univ f)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ) :
    ∃! xStar : E₁, xStar ∈ 𝓢 ∧ Tendsto method atTop (𝓝 xStar) := by
  obtain ⟨γ, hγ_mem, hγ_lower⟩ := IsSharpMeritFunction.sharp_origin (φ := φ)
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hresidual_summable :
      Summable (fun k : ℕ ↦ ‖problem (method k)‖) :=
    modifiedGaussNewton_nonlinearResidual_summable
      (problem := problem) (φ := φ) (L0 := L0) (L := L)
      (x0 := x0) (σ := σ)
      method hσ
  have hstep_bound :
      ∀ k : ℕ, dist (method k) (method (k + 1)) ≤ ‖problem (method k)‖ / σ := by
    intro k
    calc
      dist (method k) (method (k + 1)) = ‖method (k + 1) - method k‖ := by
        rw [dist_eq_norm]
        simpa using norm_sub_rev (method k) (method (k + 1))
      _ ≤ ‖problem (method k)‖ / σ :=
        modifiedGaussNewton_step_norm_le_residual_div_sigma
          (problem := problem) (φ := φ) (L0 := L0) (L := L)
          (x0 := x0) (σ := σ)
          method hσ k
  have hstep_summable :
      Summable (fun k : ℕ ↦ ‖problem (method k)‖ / σ) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hresidual_summable.mul_left (σ⁻¹)
  have hcauchy : CauchySeq method :=
    cauchySeq_of_dist_le_of_summable
      (fun k : ℕ ↦ ‖problem (method k)‖ / σ)
      hstep_bound
      hstep_summable
  rcases cauchySeq_tendsto_of_isComplete
      (by simpa using (isComplete_univ : IsComplete (Set.univ : Set E₁)))
      (fun _ ↦ by simp)
      hcauchy with
    ⟨xStar, _, hxtendsto⟩
  have hnorm_zero :
      Tendsto (fun k : ℕ ↦ ‖problem (method k)‖) atTop (𝓝 0) :=
    hresidual_summable.tendsto_atTop_zero
  have hproblem_zero :
      Tendsto (fun k : ℕ ↦ problem (method k)) atTop (𝓝 (0 : E₂)) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_zero
  have hproblem_limit :
      Tendsto (fun k : ℕ ↦ problem (method k)) atTop (𝓝 (problem xStar)) :=
    (problem.continuous.tendsto xStar).comp hxtendsto
  have hxStar_zero : problem xStar = 0 := by
    exact tendsto_nhds_unique hproblem_limit hproblem_zero
  have hxStar_mem : xStar ∈ 𝓢 := by
    rw [mem_solutionSet_iff]
    exact hxStar_zero
  refine ⟨xStar, ⟨hxStar_mem, hxtendsto⟩, ?_⟩
  intro y hy
  rcases hy with ⟨hy_mem, hytendsto⟩
  have hy_eq : y = xStar :=
    tendsto_nhds_unique hytendsto hxtendsto
  simpa [hy_eq]

end
