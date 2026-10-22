/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Assumption_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_4_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open SmoothNonlinearEquationProblem
open scoped Manifold MinimalSingularValue

variable {E₁ : Type u} {E₂ : Type v}

/- Proposition 4.4.9 lies in the modified Gauss--Newton / merit-threshold / attained
distance-to-solution-set domain.

Sampled owner-style declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate dynamics;
* `modifiedGaussNewtonQuadraticMeritThreshold` and
  `modifiedGaussNewton_large_value_oneStep_decrease` in `Theorem_4_4_3`, the source-facing
  threshold and uniform decrease owner that control the pre-entry phase;
* mathlib `LipschitzOnWith L (fderiv ℝ problem) Set.univ`, the canonical whole-space
  Jacobian-Lipschitz owner used by `Theorem_4_4_3`;
* `solutionSet` in `Definition_4_4_8`, the chapter owner for exact solutions of the nonlinear
  system;
* `solutionSublevelDistanceSet` and `infDist_eq_of_isLeast_solutionSublevelDistanceSet` in
  `Definition_4_4_15`, the source-facing attained-distance owner and the canonical bridge from
  that attained minimum to `Metric.infDist x₀ (solutionSet problem)`;
* `ModifiedGaussNewtonMethod.first_merit_le_three_halves_mul_L_mul_infDist_sq` in
  `Proposition_4_4_8`, the canonical first-step merit bound in terms of
  `Metric.infDist x₀ (solutionSet problem)` once the attained-distance owner is supplied;

Best owner abstraction:
* source-facing: the threshold regime
  `f(x_k) < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L`, the first iterate index that
  enters it, and the resulting complexity bounds together with the exact-solution distance from
  `x₀`;
* core/canonical: a modified Gauss--Newton method together with the whole-space Jacobian-Lipschitz
  owner on `problem` and the dual nondegeneracy owner already used in `Theorem_4_4_3`;
* bridge/view: the comparison that replaces the first post-initial merit term by the
  exact-solution `Metric.infDist` expression from Proposition 4.4.8.

Primitive data:
* the smooth nonlinear equation problem `problem`;
* the sharp merit scalarizer `φ`;
* the modified Gauss--Newton orbit `method`;
* the threshold parameters `σ` and `γφ`;
* the whole-space Jacobian-Lipschitz hypothesis on `problem`;
* for the distance comparison, the source-facing attained-distance datum
  `IsLeast (solutionSublevelDistanceSet problem f x₀) D` together with the first-step
  exact-solution quadratic upper-model hypothesis on `solutionSet problem`.

Derived API:
* the canonical least-entry statement cut out directly by the threshold inequality
  `IsLeast {k | ...} N`;
* the source-facing first-step entry-index bound
  `N ≤ 1 + (4L / (σ² γ_φ²)) f (method 1)` from Proposition 4.4.9 `(1)`;
* the exact-solution-distance consequence from Proposition 4.4.9 `(2)`;
* the auxiliary strengthening obtained by replacing the first post-initial merit value
  `f (method 1)` by the larger initial value `f x₀`;
* the `Metric.infDist` simplification of the first-step merit term from Proposition 4.4.8 using
  the same owner-level exact-solution quadratic upper-model input together with the attained
  distance owner from Definition 4.4.15.

This refinement keeps the source-facing first-entry problem, but removes the file-local quadratic
region wrapper in favor of the upstream threshold owner
`modifiedGaussNewtonQuadraticMeritThreshold` and the canonical least-entry-set formulation
`IsLeast {k | ...} N`. It also keeps the numbered proposition centered on the first post-initial
merit term `f (method 1)` supplied by the validated upstream owner in Proposition 4.4.8, together
with the canonical exact-solution distance consequence on `Metric.infDist x₀ (solutionSet
problem)` only after reinstating the attained-distance owner already required upstream in
Proposition 4.4.8. The stronger initial-merit estimate using `f x₀` is retained only as an
auxiliary companion. Since this is the whole-space case, Assumption 4.4.2 is discharged by
`IsSufficientlyLargeFeasibleSetAt.univ`, so the public smoothness input is exactly the canonical
Jacobian-Lipschitz owner from `Theorem_4_4_3`.
-/

section

open scoped ModifiedGaussNewtonLocalModelNotation

variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

variable
    (problem : C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯)
    (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    {L0 : ℝ} (L : NNReal) (x0 : E₁)
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)

local notation "f" => meritFunctionReformulation problem φ
local notation "localModel" => ψ[problem; φ; fun x ↦ fderiv ℝ problem x]
local notation "𝓢" => solutionSet problem

omit [CompleteSpace E₁] [CompleteSpace E₂] in
/-- Helper for Proposition 4.4.9: every modified Gauss--Newton iterate stays in the initial merit
sublevel set. -/
lemma merit_iterate_mem_initial_sublevel (k : ℕ) :
    method k ∈ f ⁻¹' Set.Iic (f x0) := by
  induction k with
  | zero =>
      -- The initial iterate attains the defining level value.
      rw [mem_levelSet_iff]
      simp
  | succ k ih =>
      rw [mem_levelSet_iff] at ih ⊢
      -- One-step merit monotonicity propagates the sublevel membership.
      exact le_trans
        (le_trans (method.step_value_le_modelValue k) (method.step_modelValue_le_merit k))
        ih

omit [CompleteSpace E₁] [CompleteSpace E₂] in
/-- Helper for Proposition 4.4.9: every strict pre-entry iterate stays above the quadratic-merit
threshold. -/
lemma threshold_le_merit_of_lt_first_quadratic_merit_region_index
    {σ γφ : ℝ} {N k : ℕ}
    (hN :
      IsLeast
        {j : ℕ | f (method j) < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L}
        N)
    (hk : k < N) :
    modifiedGaussNewtonQuadraticMeritThreshold σ γφ L ≤ f (method k) := by
  -- A strict pre-entry index cannot already satisfy the threshold inequality.
  by_contra hthreshold
  have hk_mem :
      k ∈ {j : ℕ | f (method j) < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L} := by
    exact lt_of_not_ge hthreshold
  exact (Nat.not_le_of_lt hk) (hN.2 hk_mem)

/-- Helper for Proposition 4.4.9: evaluating the quadratic-regularized local model at a scaled
exact linearized correction gives the one-variable majorant used in the large-value regime. -/
lemma modifiedGaussNewton_scaled_exact_correction_majorant_bridge
    {σ γφ : ℝ}
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (k : ℕ)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le_one : t ≤ 1) :
    f (method (k + 1)) ≤
      (1 - t) * f (method k) +
        (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) *
          (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
  have hσ_pos : 0 < σ := hσ.1
  have hσγ_pos : 0 < σ * γφ := mul_pos hσ_pos hγφ_pos
  have hxk : method k ∈ f ⁻¹' Set.Iic (f x0) :=
    merit_iterate_mem_initial_sublevel
      (problem := problem) (φ := φ) (L := L) (x0 := x0) (method := method) k
  have hdual_lower := hσ.2 hxk
  have hdual_pos :
      0 <
        ContinuousLinearMap.minimalSingularValue
          (ContinuousLinearMap.adjoint (fderiv ℝ problem (method k))) := by
    exact lt_of_lt_of_le hσ_pos hdual_lower
  let A : E₁ →L[ℝ] E₂ := fderiv ℝ problem (method k)
  obtain ⟨h, hh, hbound⟩ :=
    adjoint_minimal_singular_value_pos_has_bounded_preimage
      (A := A) hdual_pos (-problem (method k))
  have hh' : fderiv ℝ problem (method k) h = -problem (method k) := by
    simpa [A] using hh
  have hbound_sigma : ‖h‖ ≤ ‖problem (method k)‖ / σ := by
    -- Lowering the denominator from `σ_min(A†)` to `σ` weakens the exact-correction bound.
    have hbound' :
        ‖h‖ ≤ ‖problem (method k)‖ /
          ContinuousLinearMap.minimalSingularValue
            (ContinuousLinearMap.adjoint (fderiv ℝ problem (method k))) := by
      simpa using hbound
    exact hbound'.trans <|
      div_le_div_of_nonneg_left (norm_nonneg _) hσ_pos hdual_lower
  have hsharp : γφ * ‖problem (method k)‖ ≤ f (method k) := by
    simpa [meritFunctionReformulation_apply] using hγφ_lower (problem (method k))
  have hbound_sharp : ‖h‖ ≤ f (method k) / (σ * γφ) := by
    -- Sharpness upgrades the norm bound on the exact correction to the merit-value scale.
    have hscaled :
        σ * γφ * ‖h‖ ≤ f (method k) := by
      calc
        σ * γφ * ‖h‖ ≤ σ * γφ * (‖problem (method k)‖ / σ) := by
          gcongr
        _ = γφ * ‖problem (method k)‖ := by
          field_simp [hσ_pos.ne']
        _ ≤ f (method k) := hsharp
    have hmul :
        ‖h‖ * (σ * γφ) ≤ f (method k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact (le_div_iff₀ hσγ_pos).2 hmul
  let model : E₁ → ℝ := ψ[problem; φ; fun x ↦ fderiv ℝ problem x] (method k)
  let y : E₁ := method k + t • h
  have hvalue :
      f (method (k + 1)) ≤
        quadraticallyRegularizedObjective
          model
          (method.regularization k)
          (method k)
          y := by
    -- The accepted step is feasible for the global minimization problem defining `step k`.
    have haccepted :
        f (method (k + 1)) ≤
          ModifiedGaussNewtonStep.modelValueAtUniv (method.step k) (method k) := by
      simpa [method.x_succ k] using method.step_value_le_modelValue k
    have hmin :
        ModifiedGaussNewtonStep.modelValueAtUniv (method.step k) (method k) ≤
          quadraticallyRegularizedObjective
            model
            (method.regularization k)
            (method k)
            y := by
      simpa [model, ModifiedGaussNewtonMethod.acceptedTrialPoint,
        ModifiedGaussNewtonStep.modelValueAtUniv_def,
        ModifiedGaussNewtonStep.residualAtUniv_def, quadraticallyRegularizedObjective_apply] using
        (isMinOn_univ_iff.mp (method.step_isMinOn k)) y
    exact haccepted.trans hmin
  have hy_sub : y - method k = t • h := by
    simp [y]
  have hlin :
      problem (method k) + fderiv ℝ problem (method k) (y - method k) =
        (1 - t) • problem (method k) := by
    -- The exact correction linearizes the residual down to the factor `1 - t`.
    calc
      problem (method k) + fderiv ℝ problem (method k) (y - method k)
          = problem (method k) + fderiv ℝ problem (method k) (t • h) := by
              rw [hy_sub]
      _ = problem (method k) + t • fderiv ℝ problem (method k) h := by
            rw [map_smul]
      _ = problem (method k) + t • (-problem (method k)) := by
            rw [hh']
      _ = (1 : ℝ) • problem (method k) - t • problem (method k) := by
            simp [sub_eq_add_neg]
      _ = (1 - t) • problem (method k) := by
            rw [sub_smul]
  have hφ_zero : φ 0 = 0 := by
    simpa using (IsMeritFunction.eq_zero_iff (φ := φ) (0 : E₂)).2 rfl
  have hmodel_y :
      model y ≤ (1 - t) * f (method k) := by
    -- Convexity of `φ` controls the local-model value along the segment to the zero residual.
    have hproblem_mem : problem (method k) ∈ (Set.univ : Set E₂) := by
      simp
    have hzero_mem : (0 : E₂) ∈ (Set.univ : Set E₂) := by
      simp
    have hone_sub_t_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht_le_one
    have hweights : (1 - t) + t = 1 := by
      ring
    have hconv :
        φ ((1 - t) • problem (method k) + t • (0 : E₂)) ≤
          (1 - t) * φ (problem (method k)) + t * φ (0 : E₂) := by
      simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using
        (IsSharpMeritFunction.convex (φ := φ)).2
          hproblem_mem
          hzero_mem
          hone_sub_t_nonneg
          ht_nonneg
          hweights
    have hmodel_eq :
        model y =
          φ ((1 - t) • problem (method k) + t • (0 : E₂)) := by
      simp only [model, modifiedGaussNewtonLocalModel_apply]
      have hresidual_eq :
          problem (method k) +
              ((fderiv ℝ problem (method k)) y -
                (fderiv ℝ problem (method k)) (method k)) =
            (1 - t) • problem (method k) + t • (0 : E₂) := by
        calc
          problem (method k) +
              ((fderiv ℝ problem (method k)) y -
                (fderiv ℝ problem (method k)) (method k)) =
            problem (method k) +
              (fderiv ℝ problem (method k)) (y - method k) := by
                congr 1
                symm
                exact ContinuousLinearMap.map_sub (fderiv ℝ problem (method k)) y (method k)
          _ = (1 - t) • problem (method k) := hlin
          _ = (1 - t) • problem (method k) + t • (0 : E₂) := by simp
      simpa using congrArg φ hresidual_eq
    rw [hmodel_eq]
    simpa [meritFunctionReformulation_apply, hφ_zero] using hconv
  have hbound_sq :
      ‖h‖ ^ (2 : ℕ) ≤ (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
    nlinarith [hbound_sharp, norm_nonneg h]
  have hquad_y :
      (method.regularization k / 2 : ℝ) * ‖y - method k‖ ^ (2 : ℕ) ≤
        (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) *
          (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
    -- The quadratic penalty is controlled by the norm bound on the exact correction.
    have hreg_nonneg : 0 ≤ (method.regularization k / 2 : ℝ) := by
      linarith [method.regularization_pos k]
    have hfactor_nonneg :
        0 ≤ ((method.regularization k / 2 : ℝ) * t ^ (2 : ℕ)) := by
      positivity
    calc
      (method.regularization k / 2 : ℝ) * ‖y - method k‖ ^ (2 : ℕ)
          = ((method.regularization k / 2 : ℝ) * t ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
              rw [hy_sub, norm_smul, Real.norm_of_nonneg ht_nonneg]
              ring
      _ ≤
          ((method.regularization k / 2 : ℝ) * t ^ (2 : ℕ)) *
            (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
              exact mul_le_mul_of_nonneg_left hbound_sq hfactor_nonneg
      _ =
          (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) *
            (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
              ring
  -- Combine the model bound with the quadratic penalty bound at the competitor `y`.
  calc
    f (method (k + 1)) ≤
        model y +
          (method.regularization k / 2 : ℝ) * ‖y - method k‖ ^ (2 : ℕ) := by
            simpa [quadraticallyRegularizedObjective_apply] using hvalue
    _ ≤
        (1 - t) * f (method k) +
          (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) *
            (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
              exact add_le_add hmodel_y hquad_y

/-- Helper for Proposition 4.4.9: the scaled exact-correction majorant together with the generic
regularization bound `M_k ≤ 2L`. -/
lemma modifiedGaussNewton_one_step_majorant_bridge
    {σ γφ : ℝ}
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (k : ℕ)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le_one : t ≤ 1) :
    f (method (k + 1)) ≤
      (1 - t) * f (method k) +
        ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
          (f (method k)) ^ (2 : ℕ) := by
  have hσ_pos : 0 < σ := hσ.1
  have hbase :=
    modifiedGaussNewton_scaled_exact_correction_majorant_bridge
      (problem := problem) (φ := φ) (L := L) (x0 := x0) (method := method)
      hσ hγφ_pos hγφ_lower k ht_nonneg ht_le_one
  have hcoef : (method.regularization k / 2 : ℝ) ≤ (L : ℝ) := by
    -- Algorithm 4.4.1 always keeps `M_k` below `2L`.
    have hreg : method.regularization k ≤ 2 * (L : ℝ) :=
      method.regularization_le_two_mul_L k
    linarith
  have hterm_nonneg :
      0 ≤ t ^ (2 : ℕ) * (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
    positivity
  have hterm :
      (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) *
          (f (method k) / (σ * γφ)) ^ (2 : ℕ) ≤
        ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
          (f (method k)) ^ (2 : ℕ) := by
    -- Rewrite the target coefficient in the same `t² (f / (σ γφ))²` form and compare scalars.
    have hcoef' : (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) ≤ (L : ℝ) * t ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    have hcompare :
        (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) *
            (f (method k) / (σ * γφ)) ^ (2 : ℕ) ≤
          (L : ℝ) * t ^ (2 : ℕ) * (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
      nlinarith [hcoef', hterm_nonneg]
    have hrepack :
        (L : ℝ) * t ^ (2 : ℕ) * (f (method k) / (σ * γφ)) ^ (2 : ℕ) =
          ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
            (f (method k)) ^ (2 : ℕ) := by
      field_simp [hσ_pos.ne', hγφ_pos.ne']
    exact hcompare.trans_eq hrepack
  have hsum :
      (1 - t) * f (method k) +
          (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) *
            (f (method k) / (σ * γφ)) ^ (2 : ℕ) ≤
        (1 - t) * f (method k) +
          ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
            (f (method k)) ^ (2 : ℕ) := by
    linarith
  exact hbase.trans hsum

/-- Helper for Proposition 4.4.9: this is the whole-space large-value decrease step from
Theorem 4.4.3, specialized to the current orbit. -/
lemma modifiedGaussNewton_large_value_oneStep_decrease_on_univ_bridge
    {σ γφ : ℝ}
    (_hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (k : ℕ)
    (hk :
      modifiedGaussNewtonQuadraticMeritThreshold σ γφ L ≤ f (method k)) :
    f (method (k + 1)) ≤
      f (method k) - ((σ ^ (2 : ℕ)) / (4 * (L : ℝ))) * γφ ^ (2 : ℕ) := by
  have hσ_pos : 0 < σ := hσ.1
  have hL_pos : 0 < (L : ℝ) := by
    exact lt_of_lt_of_le method.L0_pos method.L0_le_L
  have hthreshold_pos : 0 < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L := by
    -- All threshold parameters are strictly positive in the theorem regime.
    dsimp [modifiedGaussNewtonQuadraticMeritThreshold]
    positivity
  have hfk_pos : 0 < f (method k) := by
    exact lt_of_lt_of_le hthreshold_pos hk
  let t : ℝ := (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) / (2 * (L : ℝ) * f (method k))
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have hmul :
      σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) ≤ 2 * (L : ℝ) * f (method k) := by
    have hk' :
        (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) / (2 * (L : ℝ)) ≤ f (method k) := by
      simpa [modifiedGaussNewtonQuadraticMeritThreshold, div_eq_mul_inv, mul_assoc,
        mul_left_comm, mul_comm] using hk
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_le_iff₀ (show 0 < 2 * (L : ℝ) by positivity)).1 hk'
  have ht_le_one : t ≤ 1 := by
    -- The large-value hypothesis is exactly the scalar condition forcing `t ≤ 1`.
    dsimp [t]
    have hden_pos : 0 < 2 * (L : ℝ) * f (method k) := by
      positivity
    have hmul' :
        σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) ≤ 1 * (2 * (L : ℝ) * f (method k)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact (div_le_iff₀ hden_pos).2 hmul'
  have hmajorant :=
    modifiedGaussNewton_one_step_majorant_bridge
      (problem := problem) (φ := φ) (L := L) (x0 := x0) (method := method)
      hσ hγφ_pos hγφ_lower k ht_nonneg ht_le_one
  have hrepack :
      (1 - t) * f (method k) +
          ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
            (f (method k)) ^ (2 : ℕ) =
        f (method k) - ((σ ^ (2 : ℕ)) / (4 * (L : ℝ))) * γφ ^ (2 : ℕ) := by
    -- The chosen scalar `t` is the minimizer of the quadratic majorant.
    dsimp [t]
    have hfk_ne : φ (problem (method k)) ≠ 0 := by
      simpa [meritFunctionReformulation_apply] using hfk_pos.ne'
    field_simp [hL_pos.ne', hσ_pos.ne', hγφ_pos.ne', hfk_ne]
    ring
  rwa [hrepack] at hmajorant

omit [CompleteSpace E₁] [CompleteSpace E₂] in
/-- Helper for Proposition 4.4.9: this is the first-merit distance bridge from Proposition 4.4.8
for the current method. -/
lemma modifiedGaussNewton_first_merit_le_infDist_sq_bridge
    {D : ℝ}
    (hD : IsLeast (solutionSublevelDistanceSet problem f x0) D)
    (hupper :
      ∀ ⦃y : E₁⦄, y ∈ 𝓢 →
        localModel x0 y ≤ (L / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)) :
    f (method 1) ≤
      (3 / 2 : ℝ) * (L : ℝ) * Metric.infDist x0 𝓢 ^ (2 : ℕ) := by
  -- Realize the attained distance `D` by an exact solution in the solution set.
  have hmem : D ∈ (fun y : E₁ ↦ ‖y - x0‖) '' 𝓢 := by
    have hmem' : D ∈ solutionSublevelDistanceSet problem f x0 := hD.1
    rw [solutionSublevelDistanceSet_eq_image_solutionSet_of_meritFunctionReformulation
      (problem := problem) (φ := φ) (x0 := x0)] at hmem'
    exact hmem'
  rcases hmem with ⟨y, hy, hyD⟩
  have hupper' : localModel x0 y ≤ (L / 2 : ℝ) * D ^ (2 : ℕ) := by
    simpa [hyD] using hupper hy
  have hvalue :
      f (method 1) ≤
        localModel x0 (method.acceptedTrialPoint 0) +
          (method.regularization 0 / 2 : ℝ) * ‖method.acceptedTrialPoint 0 - x0‖ ^ (2 : ℕ) := by
    simpa [ModifiedGaussNewtonMethod.acceptedTrialPoint, method.x_zero,
      quadraticallyRegularizedObjective_apply, modifiedGaussNewtonLocalModel_apply] using
      method.step_value_le_modelValue 0
  have hmin :
      localModel x0 (method.acceptedTrialPoint 0) +
          (method.regularization 0 / 2 : ℝ) * ‖method.acceptedTrialPoint 0 - x0‖ ^ (2 : ℕ) ≤
        localModel x0 y + (method.regularization 0 / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ) := by
    simpa [method.x_zero, quadraticallyRegularizedObjective_apply,
      modifiedGaussNewtonLocalModel_apply] using
      (isMinOn_univ_iff.mp (method.step_isMinOn 0)) y
  have hmin' :
      localModel x0 (method.acceptedTrialPoint 0) +
          (method.regularization 0 / 2 : ℝ) * ‖method.acceptedTrialPoint 0 - x0‖ ^ (2 : ℕ) ≤
        localModel x0 y + (method.regularization 0 / 2 : ℝ) * D ^ (2 : ℕ) := by
    simpa [hyD] using hmin
  have hfirst :
      f (method 1) ≤
        ((L : ℝ) + method.regularization 0) / 2 * D ^ (2 : ℕ) := by
    nlinarith [hvalue, hmin', hupper']
  have hL_pos : 0 < (L : ℝ) := lt_of_lt_of_le method.L0_pos method.L0_le_L
  have hfirst' :
      f (method 1) ≤ (3 / 2 : ℝ) * (L : ℝ) * D ^ (2 : ℕ) := by
    nlinarith [hfirst, method.regularization_le_two_mul_L 0, sq_nonneg D, hL_pos]
  have hinf : Metric.infDist x0 𝓢 = D := by
    simpa [solutionSublevelSet_eq_solutionSet_of_meritFunctionReformulation
      (problem := problem) (φ := φ) (x0 := x0)] using
      (infDist_eq_of_isLeast_solutionSublevelDistanceSet problem f hD)
  simpa [hinf] using hfirst'

-- Proof sketch: if `N = 0`, the bound is immediate. Otherwise every iterate `x_k` with
-- `1 ≤ k < N` still lies in the large-value regime, so the one-step decrease from
-- Theorem 4.4.3 applies for `k = 1, ..., N - 1`. Summing those decreases from the first
-- post-initial iterate yields the bound by `f(x₁)` instead of `f(x₀)`.
/-- Proposition 4.4.9 (1): if `N` is the first iterate index satisfying the threshold inequality
`f(x_N) < (σ² / (2L)) γ_φ²`, then
`N ≤ 1 + (4L / (σ² γ_φ²)) f(x₁)`, where `x₁ = method 1` and
`f = meritFunctionReformulation problem φ`. -/
theorem modifiedGaussNewton_firstQuadraticMeritRegionIndex_le_one_add_scaled_firstMerit
    {σ γφ : ℝ}
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ :
      HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    {N : ℕ}
    (hN :
      IsLeast
        {k : ℕ | f (method k) < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L}
        N) :
    (N : ℝ) ≤
      1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1) := by
  -- Split off the trivial entry-at-once case.
  cases N with
  | zero =>
      have hσ_pos : 0 < σ := hσ.1
      have hfactor_nonneg :
          0 ≤ 4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) := by
        positivity
      have hmerit_nonneg : 0 ≤ f (method 1) := by
        simpa [meritFunctionReformulation] using
          (IsMeritFunction.nonneg (φ := φ) (problem (method 1)))
      nlinarith
  | succ n =>
      let c : ℝ := ((σ ^ (2 : ℕ)) / (4 * (L : ℝ))) * γφ ^ (2 : ℕ)
      have hσ_pos : 0 < σ := hσ.1
      have hL_pos : 0 < (L : ℝ) := lt_of_lt_of_le method.L0_pos method.L0_le_L
      have hc_pos : 0 < c := by
        dsimp [c]
        positivity
      have hstep :
          ∀ i ∈ Finset.range n,
            c ≤ f (method (1 + i)) - f (method (1 + i + 1)) := by
        intro i hi
        have hi_lt : i < n := Finset.mem_range.mp hi
        have hthreshold :
            modifiedGaussNewtonQuadraticMeritThreshold σ γφ L ≤ f (method (1 + i)) := by
          apply threshold_le_merit_of_lt_first_quadratic_merit_region_index
            (problem := problem) (φ := φ) (L := L) (x0 := x0) (method := method) hN
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_lt_succ hi_lt
        have hdecrease :
            f (method (1 + i + 1)) ≤
              f (method (1 + i)) - ((σ ^ (2 : ℕ)) / (4 * (L : ℝ))) * γφ ^ (2 : ℕ) := by
          simpa [Nat.add_assoc] using
            modifiedGaussNewton_large_value_oneStep_decrease_on_univ_bridge
              (problem := problem) (φ := φ) (L := L) (x0 := x0) (method := method)
              hJacobianLipschitz hσ hγφ_pos hγφ_lower (1 + i) hthreshold
        -- Rearranging each one-step decrease exposes a constant decrement.
        dsimp [c] at hdecrease ⊢
        linarith
      have hconst : (n : ℝ) * c = Finset.sum (Finset.range n) (fun _ : ℕ ↦ c) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      have hsum :
          (n : ℝ) * c ≤ f (method 1) - f (method (n + 1)) := by
        -- Sum the uniform decrement over the whole strict pre-entry range.
        calc
          (n : ℝ) * c = Finset.sum (Finset.range n) (fun _ : ℕ ↦ c) := hconst
          _ ≤ Finset.sum (Finset.range n)
                (fun i : ℕ ↦ f (method (1 + i)) - f (method (1 + i + 1))) := by
              exact Finset.sum_le_sum hstep
          _ = f (method 1) - f (method (n + 1)) := by
              simpa [Nat.add_assoc, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm] using
                (Finset.sum_range_sub' (fun i ↦ f (method (1 + i))) n)
      have hterminal_nonneg : 0 ≤ f (method (n + 1)) := by
        simpa [meritFunctionReformulation] using
          (IsMeritFunction.nonneg (φ := φ) (problem (method (n + 1))))
      have hcount_bound : (n : ℝ) * c ≤ f (method 1) := by
        nlinarith
      have hσ_ne : σ ≠ 0 := hσ_pos.ne'
      have hγ_ne : γφ ≠ 0 := hγφ_pos.ne'
      have hL_ne : (L : ℝ) ≠ 0 := hL_pos.ne'
      have hn :
          (n : ℝ) ≤
            (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1) := by
        dsimp [c] at hcount_bound ⊢
        field_simp [hσ_ne, hγ_ne, hL_ne] at hcount_bound ⊢
        nlinarith
      -- Convert the bound on `n = N - 1` back to the stated bound on `N`.
      have hsucc_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
        norm_num
      rw [hsucc_cast]
      nlinarith

-- Proof sketch: apply
-- `ModifiedGaussNewtonMethod.first_merit_le_three_halves_mul_L_mul_infDist_sq` with the same
-- owner-level exact-solution quadratic upper-model hypothesis on `𝓢 = solutionSet problem`
-- together with an attained minimum `hD` on `solutionSublevelDistanceSet problem f x₀`, then
-- multiply the resulting bound by `4 / (σ² γ_φ²)` and simplify the scalar expression.
omit [CompleteSpace E₁] [CompleteSpace E₂] in
/-- The first-step scalar bound `1 + (4L / (σ² γ_φ²)) f(x₁)` is at most
`1 + 6 ((L * Metric.infDist x₀ (solutionSet problem)) / (σ γ_φ))²`, where
`f = meritFunctionReformulation problem φ` and `x₁ = method 1`, provided the first local model
at `x₀` satisfies the same quadratic upper estimate on exact solutions in
`𝓢 = solutionSet problem` as in Proposition 4.4.8 and the attained distance from Definition
4.4.15 is realized by some `D`. This is the bridge used in
Proposition 4.4.9 (2). -/
theorem modifiedGaussNewton_firstMeritBound_le_distanceBound
    (σ γφ : ℝ)
    {D : ℝ}
    (hD : IsLeast (solutionSublevelDistanceSet problem f x0) D)
    (hupper :
      ∀ ⦃y : E₁⦄, y ∈ 𝓢 →
        localModel x0 y ≤ (L / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)) :
    1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1) ≤
      1 + 6 * ((((L : ℝ) * Metric.infDist x0 𝓢) / (σ * γφ)) ^ (2 : ℕ)) := by
  have hfirst :
      f (method 1) ≤
        (3 / 2 : ℝ) * (L : ℝ) * Metric.infDist x0 𝓢 ^ (2 : ℕ) := by
    exact modifiedGaussNewton_first_merit_le_infDist_sq_bridge
      (problem := problem) (φ := φ) (L := L) (x0 := x0) (method := method) hD hupper
  have hfactor_nonneg :
      0 ≤ 4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) := by
    positivity
  have hscaled :
      (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1) ≤
        (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) *
          ((3 / 2 : ℝ) * (L : ℝ) * Metric.infDist x0 𝓢 ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hfirst hfactor_nonneg
  by_cases hzero : σ * γφ = 0
  · have hden : σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) = 0 := by
      nlinarith
    simp [hzero, hden]
  · have hσ_ne : σ ≠ 0 := by
      intro hσ
      apply hzero
      simp [hσ]
    have hγ_ne : γφ ≠ 0 := by
      intro hγ
      apply hzero
      simp [hγ]
    have hden_ne : σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero 2 hσ_ne) (pow_ne_zero 2 hγ_ne)
    have hscalar :
        (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) *
            ((3 / 2 : ℝ) * (L : ℝ) * Metric.infDist x0 𝓢 ^ (2 : ℕ)) =
          6 * ((((L : ℝ) * Metric.infDist x0 𝓢) / (σ * γφ)) ^ (2 : ℕ)) := by
      field_simp [hσ_ne, hγ_ne, hden_ne, hzero]
      ring
    -- Proposition 4.4.8 turns the first-step merit term into the distance expression.
    calc
      1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1)
          ≤ 1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) *
              ((3 / 2 : ℝ) * (L : ℝ) * Metric.infDist x0 𝓢 ^ (2 : ℕ)) := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hscaled 1
      _ = 1 + 6 * ((((L : ℝ) * Metric.infDist x0 𝓢) / (σ * γφ)) ^ (2 : ℕ)) := by
            rw [hscalar]

-- Proof sketch: combine the companion first-step entry-index bound with
-- `modifiedGaussNewton_firstMeritBound_le_distanceBound`, which replaces the first-step merit
-- expression by the exact-solution-distance bound from Proposition 4.4.8 under the same
-- first-step exact-solution quadratic upper-model hypothesis on `𝓢`, using the attained-distance
-- owner from Definition 4.4.15.
/-- Proposition 4.4.9 (2): if `N` is the first iterate index satisfying the threshold inequality
`f(x_N) < (σ² / (2L)) γ_φ²`, then
`N ≤ 1 + 6 ((L * Metric.infDist x₀ (solutionSet problem)) / (σ γ_φ))²`, where
`f = meritFunctionReformulation problem φ`, provided the first local model at `x₀` satisfies the
same quadratic upper estimate on exact solutions in `𝓢 = solutionSet problem` as in
Proposition 4.4.8 and the attained distance from Definition 4.4.15 is realized by some `D`. -/
theorem modifiedGaussNewton_firstQuadraticMeritRegionIndex_le_distanceBound
    {σ γφ : ℝ}
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ :
      HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    {N : ℕ}
    (hN :
      IsLeast
        {k : ℕ | f (method k) < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L}
        N)
    {D : ℝ}
    (hD : IsLeast (solutionSublevelDistanceSet problem f x0) D)
    (hupper :
      ∀ ⦃y : E₁⦄, y ∈ 𝓢 →
        localModel x0 y ≤ (L / 2 : ℝ) * ‖y - x0‖ ^ (2 : ℕ)) :
    (N : ℝ) ≤ 1 + 6 * ((((L : ℝ) * Metric.infDist x0 𝓢) / (σ * γφ)) ^ (2 : ℕ)) := by
  -- Chain the source-facing entry-index bound with the distance bridge.
  calc
    (N : ℝ) ≤
        1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1) :=
      modifiedGaussNewton_firstQuadraticMeritRegionIndex_le_one_add_scaled_firstMerit
        (problem := problem) (φ := φ) (L := L) (x0 := x0) (method := method)
        hJacobianLipschitz hσ hγφ_pos hγφ_lower hN
    _ ≤ 1 + 6 * ((((L : ℝ) * Metric.infDist x0 𝓢) / (σ * γφ)) ^ (2 : ℕ)) :=
      modifiedGaussNewton_firstMeritBound_le_distanceBound
        (problem := problem) (φ := φ) (L := L) (x0 := x0) (method := method)
        σ γφ hD hupper

-- Proof sketch: `f (method 1) ≤ f x₀` by monotonicity of the merit values along the modified
-- Gauss--Newton orbit, so the source-facing estimate from Proposition 4.4.9 (1) strengthens to
-- the same coefficient applied to the initial merit value.
/-- Auxiliary strengthening: the first-entry bound from Proposition 4.4.9 (1) remains valid after
replacing the first post-initial merit value `f(x₁)` by the larger initial merit value `f(x₀)`. -/
theorem modifiedGaussNewton_firstQuadraticMeritRegionIndex_le_initialMerit
    {σ γφ : ℝ}
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ :
      HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    {N : ℕ}
    (hN :
      IsLeast
        {k : ℕ | f (method k) < modifiedGaussNewtonQuadraticMeritThreshold σ γφ L}
        N) :
    (N : ℝ) ≤
      1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f x0 := by
  have hfirst_bound :
      (N : ℝ) ≤
        1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1) :=
    modifiedGaussNewton_firstQuadraticMeritRegionIndex_le_one_add_scaled_firstMerit
      (problem := problem) (φ := φ) (L := L) (x0 := x0) (method := method)
      hJacobianLipschitz hσ hγφ_pos hγφ_lower hN
  have hfirst_le_initial : f (method 1) ≤ f x0 := by
    have hsublevel := merit_iterate_mem_initial_sublevel (method := method) (k := 1)
    rw [mem_levelSet_iff] at hsublevel
    simpa using hsublevel
  have hfactor_nonneg :
      0 ≤ 4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) := by
    have hσ_pos : 0 < σ := hσ.1
    positivity
  have hscaled :
      (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1) ≤
        (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f x0 := by
    exact mul_le_mul_of_nonneg_left hfirst_le_initial hfactor_nonneg
  -- Monotonicity of the coefficient transfers the first-step bound to the initial merit.
  calc
    (N : ℝ) ≤
        1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f (method 1) :=
      hfirst_bound
    _ ≤ 1 + (4 * (L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * f x0 := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hscaled 1

end
