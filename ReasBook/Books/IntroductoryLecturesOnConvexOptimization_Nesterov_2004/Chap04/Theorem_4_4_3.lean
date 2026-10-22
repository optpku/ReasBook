/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Assumption_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ModifiedGaussNewtonStep
open scoped InnerProduct Manifold MinimalSingularValue
open scoped LevelSetNotation
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

/- Theorem 4.4.3 lies in the modified Gauss--Newton / merit-threshold decrease domain.

Sampled owner-style declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate dynamics;
* `jacobian_lipschitz_taylor_remainder_le` in `Proposition_4_4_5`, the chapter owner for the
  first-order Taylor remainder bound on a convex Lipschitz domain;
* `abs_meritFunctionReformulation_sub_modifiedGaussNewtonLocalModel_le` in `Lemma_4_4_1`, the
  chapter owner for the merit/model discrepancy on that same convex domain;
* mathlib `LipschitzOnWith L (fderiv ℝ problem) 𝓕`, the canonical Jacobian-Lipschitz owner on a
  feasible set;
* `𝓛[f]((f x0)) ⊆ 𝓕`, the chapter's canonical initial-sublevel containment bridge already used in
  nearby Chapter 4 theorem surfaces;
* `HasUniformDualNondegeneracyOnInitialSublevelSet` in `Assumption_4_4_3`, the source-facing
  owner for the uniform dual nondegeneracy assumption.

Best owner abstraction:
* source-facing: the textbook one-step decrease and quadratic-decay estimates in the large-value
  and small-value regimes;
* core/canonical: a bundled smooth map `problem`, a sharp merit function `φ`, a modified
  Gauss--Newton method `method`, a convex feasible domain `𝓕`, the canonical sublevel-containment
  bridge `𝓛[f]((f x0)) ⊆ 𝓕`, the chapter dual-nondegeneracy owner, and the Jacobian-Lipschitz
  owner on `problem`;
* bridge/view: an explicit sharpness witness `γφ` for the merit function, because the displayed
  thresholds and decay constants depend on that particular witness, together with the convex-domain
  Taylor/model comparison supplied by Proposition 4.4.5 and Lemma 4.4.1.

Primitive data:
* the smooth map `problem`;
* the sharp merit function `φ`;
* the method `method`;
* the convex feasible domain `𝓕`;
* the Jacobian-Lipschitz hypothesis `LipschitzOnWith L (fderiv ℝ problem) 𝓕`;
* the sublevel containment bridge `𝓛[f]((f x0)) ⊆ 𝓕`;
* the threshold parameter `γφ`.

Derived API:
* convex feasible-domain geometry `Convex ℝ 𝓕`;
* positivity of `σ` and the initial-sublevel lower bound, bundled in
  `HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ`.

The earlier file put Theorem 4.4.3 on the scalar smoothness owner
`HasLipschitzDerivativeOnWith L 𝓕 (meritFunctionReformulation problem φ)`. That shifts the
mathematical content away from the Gauss--Newton residual map `problem`, while the chapter
comparison lemmas actually used here are stated on the Jacobian-Lipschitz owner
`LipschitzOnWith L (fderiv ℝ problem) 𝓕` over a convex domain. This refinement keeps the same
source-facing decrease theorems, but moves their smoothness hypothesis onto that canonical owner
and leaves the scalar merit reformulation as derived API rather than as the primitive smoothness
input.
-/

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {𝓕 : Set E₁}
variable {L0 : ℝ} {L : NNReal} {σ γφ : ℝ} {x0 : E₁}

local notation "f" => meritFunctionReformulation problem φ
local notation "𝓛0" => (𝓛[f]((f x0)) : Set E₁)

/-- The merit-value threshold `(σ² / (2L)) γ_φ²` separating the large-value and quadratic-decay
regimes in Theorem 4.4.3. -/
def modifiedGaussNewtonQuadraticMeritThreshold
    (σ γφ : ℝ) (L : NNReal) : ℝ :=
  ((σ ^ (2 : ℕ)) / (2 * (L : ℝ))) * γφ ^ (2 : ℕ)

/-- Helper for Theorem 4.4.3: the accepted steps never increase the merit value, so every iterate
stays in the initial sublevel set `𝓛[f]((f x₀))`. -/
lemma modifiedGaussNewton_mem_initial_sublevel
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0) :
    ∀ k : ℕ, method k ∈ 𝓛0 := by
  intro k
  induction k with
  | zero =>
      -- The initial iterate is exactly `x₀`, so it lies in its own sublevel set.
      rw [mem_levelSet_iff]
      simp
  | succ k ih =>
      rw [mem_levelSet_iff] at ih ⊢
      -- Chain the accepted-step estimate with the model-vs-current-merit comparison.
      exact le_trans
        (le_trans (method.step_value_le_modelValue k) (method.step_modelValue_le_merit k))
        ih

/-- Helper for Theorem 4.4.3: a positive lower bound on the dual minimal singular value of a
real Hilbert-space operator yields a controlled preimage for every right-hand side. -/
lemma adjoint_minimal_singular_value_pos_has_bounded_preimage
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
    have hbound_sq :
        (σ_min(A†) * ‖u‖) * (σ_min(A†) * ‖u‖) ≤ ‖(A†) u‖ * ‖(A†) u‖ := by
      exact mul_le_mul hbound hbound
        (mul_nonneg (minimalSingularValue_nonneg (A†)) (norm_nonneg _))
        (norm_nonneg _)
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hbound_sq
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
    change inner ℝ ((A†) y) ((A†) v) = inner ℝ (A ((A†) y)) v
    rw [A.adjoint_inner_right]
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
      _ = ‖y‖ * ‖b‖ := by
        rw [hAy]
  have hx_bound : σ_min(A†) * ‖(A†) y‖ ≤ ‖b‖ := by
    -- Combine the coercive solve with the adjoint lower bound and cancel the auxiliary vector.
    by_cases hAy_zero : (A†) y = 0
    · simp [hAy_zero]
    · have hAy_pos : 0 < ‖(A†) y‖ := norm_pos_iff.mpr hAy_zero
      have hy_le : ‖y‖ ≤ ‖(A†) y‖ / σ_min(A†) := by
        exact (le_div_iff₀ hA).2 <| by simpa [mul_comm] using hy_bound
      have hx_sq_le' :
          ‖(A†) y‖ ^ (2 : ℕ) ≤ (‖(A†) y‖ / σ_min(A†)) * ‖b‖ := by
        exact hx_sq_le.trans <| by gcongr
      have hx_mul :
          (σ_min(A†) * ‖(A†) y‖) * ‖(A†) y‖ ≤ ‖b‖ * ‖(A†) y‖ := by
        calc
          (σ_min(A†) * ‖(A†) y‖) * ‖(A†) y‖ = σ_min(A†) * ‖(A†) y‖ ^ (2 : ℕ) := by
              ring
          _ ≤ σ_min(A†) * ((‖(A†) y‖ / σ_min(A†)) * ‖b‖) := by
              gcongr
          _ = ‖b‖ * ‖(A†) y‖ := by
              field_simp [hA.ne']
      exact le_of_mul_le_mul_right hx_mul hAy_pos
  exact (le_div_iff₀ hA).2 <| by
    simpa [mul_comm] using hx_bound

/-- Helper for Theorem 4.4.3: comparing the accepted step with a scaled exact linearized
correction gives the one-variable quadratic majorant from the source proof. -/
lemma modifiedGaussNewton_scaled_exact_correction_majorant
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
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
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hσγ_pos : 0 < σ * γφ := mul_pos hσ_pos hγφ_pos
  have hxk : method k ∈ 𝓛0 :=
    modifiedGaussNewton_mem_initial_sublevel method k
  have hdual_lower :
      σ ≤ σ_min((fderiv ℝ problem (method k))†) :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.lower_bound hσ hxk
  have hdual_pos : 0 < σ_min((fderiv ℝ problem (method k))†) := by
    exact lt_of_lt_of_le hσ_pos hdual_lower
  let A : E₁ →L[ℝ] E₂ := fderiv ℝ problem (method k)
  obtain ⟨h, hh, hbound⟩ :=
    adjoint_minimal_singular_value_pos_has_bounded_preimage
      (A := A) hdual_pos (-problem (method k))
  have hh' : fderiv ℝ problem (method k) h = -problem (method k) := by
    simpa [A] using hh
  have hbound_sigma : ‖h‖ ≤ ‖problem (method k)‖ / σ := by
    -- Lowering the denominator from `σ_min(A†)` to `σ` weakens the exact-correction bound.
    exact hbound.trans <|
      div_le_div_of_nonneg_left (norm_nonneg _) hσ_pos.le hdual_lower
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
          ring
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
        f (method (k + 1)) ≤ f[(method.step k)] (method k) := by
      simpa [method.x_succ k] using method.step_value_le_modelValue k
    have hmin :
        f[(method.step k)] (method k) ≤
          quadraticallyRegularizedObjective
            model
            (method.regularization k)
            (method k)
            y := by
      simpa [ModifiedGaussNewtonStep.modelValueAtUniv_def,
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
      simp [model, modifiedGaussNewtonLocalModel_apply, hlin]
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

/-- Helper for Theorem 4.4.3: the exact-correction competitor estimate with the generic
regularization bound `M_k ≤ 2L`. -/
lemma modifiedGaussNewton_one_step_majorant
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
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
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hbase :=
    modifiedGaussNewton_scaled_exact_correction_majorant
      (method := method) (hσ := hσ) hγφ_pos hγφ_lower k ht_nonneg ht_le_one
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
    have hcompare :
        (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) *
            (f (method k) / (σ * γφ)) ^ (2 : ℕ) ≤
          (L : ℝ) * t ^ (2 : ℕ) * (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hcoef hterm_nonneg
    have hrepack :
        (L : ℝ) * t ^ (2 : ℕ) * (f (method k) / (σ * γφ)) ^ (2 : ℕ) =
          ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
            (f (method k)) ^ (2 : ℕ) := by
      field_simp [hσ_pos.ne', hγφ_pos.ne']
      ring
    exact hcompare.trans_eq hrepack
  calc
    f (method (k + 1)) ≤
        (1 - t) * f (method k) +
          (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) *
            (f (method k) / (σ * γφ)) ^ (2 : ℕ) := hbase
    _ ≤
        (1 - t) * f (method k) +
          ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
            (f (method k)) ^ (2 : ℕ) := by
              exact add_le_add_left hterm ((1 - t) * f (method k))

/-- Helper for Theorem 4.4.3: the exact-correction competitor estimate specialized to the fixed
regularization rule `M_k ≡ L`. -/
lemma modifiedGaussNewton_fixed_regularization_one_step_majorant
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (hregularization : ∀ k : ℕ, method.regularization k = (L : ℝ))
    (k : ℕ)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le_one : t ≤ 1) :
    f (method (k + 1)) ≤
      (1 - t) * f (method k) +
        ((L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
          (f (method k)) ^ (2 : ℕ) := by
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hbase :=
    modifiedGaussNewton_scaled_exact_correction_majorant
      (method := method) (hσ := hσ) hγφ_pos hγφ_lower k ht_nonneg ht_le_one
  have hrepack :
      (L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) * t ^ (2 : ℕ) *
          (f (method k)) ^ (2 : ℕ) =
        ((L : ℝ) / 2) * t ^ (2 : ℕ) *
          (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
    field_simp [hσ_pos.ne', hγφ_pos.ne']
    ring
  -- Substitute the fixed regularization identity and rewrite the coefficient.
  calc
    f (method (k + 1)) ≤
        (1 - t) * f (method k) +
          (method.regularization k / 2 : ℝ) * t ^ (2 : ℕ) *
            (f (method k) / (σ * γφ)) ^ (2 : ℕ) := hbase
    _ =
        (1 - t) * f (method k) +
          ((L : ℝ) / 2) * t ^ (2 : ℕ) *
            (f (method k) / (σ * γφ)) ^ (2 : ℕ) := by
              rw [hregularization k]
    _ =
        (1 - t) * f (method k) +
          ((L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
            (f (method k)) ^ (2 : ℕ) := by
              rw [hrepack]

-- Proof sketch: use monotonicity of the merit values along Algorithm 4.4.1 to keep `x_k` inside
-- the initial sublevel set, apply the uniform dual nondegeneracy assumption there, and invoke
-- Lemma 4.4.6 to obtain a correction `h_k*` with `‖h_k*‖ ≤ f(x_k) / (σ γφ)`. Evaluating the
-- quadratic-regularized local model along the segment `t ↦ t h_k*` and using the upper bound
-- `M_k ≤ 2L` yields a one-variable quadratic majorant; when
-- `f(x_k) ≥ (σ² / (2L)) γφ²`, its minimizer gives the decrease estimate `(4.4.23)`.
/-- Theorem 4.4.3 (1): under Assumptions 4.4.1, 4.4.2, and 4.4.3, if a modified Gauss--Newton
iterate satisfies `f(x_k) ≥ (σ² / (2L)) γ_φ²`, then the next merit value decreases by at least
`(σ² / (4L)) γ_φ²`. On the theorem surface, the only part of Assumption 4.4.2 used here is the
sublevel containment `𝓛[f]((f x₀)) ⊆ 𝓕`. -/
theorem modifiedGaussNewton_large_value_oneStep_decrease
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (k : ℕ)
    (hk :
      modifiedGaussNewtonQuadraticMeritThreshold σ γφ L ≤
        f (method k)) :
    f (method (k + 1)) ≤
      f (method k) - ((σ ^ (2 : ℕ)) / (4 * (L : ℝ))) * γφ ^ (2 : ℕ) := by
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
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
    exact (div_le_iff (by positivity : 0 < 2 * (L : ℝ))).1 hk'
  have ht_le_one : t ≤ 1 := by
    -- The large-value hypothesis is exactly the scalar condition forcing `t ≤ 1`.
    dsimp [t]
    have hden_pos : 0 < 2 * (L : ℝ) * f (method k) := by
      positivity
    have hmul' :
        σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) ≤ 1 * (2 * (L : ℝ) * f (method k)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact (div_le_iff hden_pos).2 hmul'
  have hmajorant :=
    modifiedGaussNewton_one_step_majorant
      (method := method) (hσ := hσ) hγφ_pos hγφ_lower k ht_nonneg ht_le_one
  have hrepack :
      (1 - t) * f (method k) +
          ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
            (f (method k)) ^ (2 : ℕ) =
        f (method k) - ((σ ^ (2 : ℕ)) / (4 * (L : ℝ))) * γφ ^ (2 : ℕ) := by
    -- The chosen scalar `t` is the minimizer of the quadratic majorant.
    dsimp [t]
    field_simp [hL_pos.ne', hσ_pos.ne', hγφ_pos.ne', hfk_pos.ne']
    ring
  rwa [hrepack] at hmajorant

-- Proof sketch: follow the same comparison with the one-dimensional model along `t h_k*`. In the
-- regime `f(x_k) < (σ² / (2L)) γφ²`, the scalar majorant is minimized at `t = 1`, which yields
-- the quadratic estimate `(4.4.24)`.
/-- Theorem 4.4.3 (2): under the same hypotheses, if
`f(x_k) < (σ² / (2L)) γ_φ²`, then
`f(x_{k+1}) ≤ (L / (σ² γ_φ²)) f(x_k)^2`. -/
theorem modifiedGaussNewton_small_value_quadratic_decay
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (k : ℕ)
    (hk :
      f (method k) <
        modifiedGaussNewtonQuadraticMeritThreshold σ γφ L) :
    f (method (k + 1)) ≤
      ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) := by
  -- In the small-value regime the source majorant is minimized at the endpoint `t = 1`.
  have hone_nonneg : 0 ≤ (1 : ℝ) := by
    norm_num
  have hone_le : (1 : ℝ) ≤ 1 := by
    norm_num
  have hmajorant :=
    modifiedGaussNewton_one_step_majorant
      (method := method) (hσ := hσ) hγφ_pos hγφ_lower k hone_nonneg hone_le
  simpa using hmajorant

-- Proof sketch: combine the threshold hypothesis
-- `f(x_k) < (σ² / (2L)) γφ²` with elementary scalar algebra to bound the quadratic factor from
-- Theorem 4.4.3 (2) by `1 / 2`.
/-- Under the small-value hypothesis from Theorem 4.4.3 (2), the quadratic upper bound is at most
half of the current merit value. -/
theorem modifiedGaussNewton_small_value_quadratic_decay_le_half_current
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (k : ℕ)
    (hk :
      f (method k) <
        modifiedGaussNewtonQuadraticMeritThreshold σ γφ L) :
    ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * f (method k) := by
  have hfk_nonneg : 0 ≤ f (method k) := by
    -- Merit functions are nonnegative on every residual value.
    simpa [meritFunctionReformulation] using
      (IsMeritFunction.nonneg (φ := φ) (problem (method k)))
  by_cases hd : σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) = 0
  · -- If the denominator vanishes, the left-hand side collapses to `0`.
    simp [hd]
    nlinarith
  · by_cases hL : (L : ℝ) = 0
    · -- If `L = 0`, then the threshold is `0`, contradicting nonnegativity of the merit value.
      have : ¬ f (method k) < 0 := not_lt_of_ge hfk_nonneg
      simp [modifiedGaussNewtonQuadraticMeritThreshold, hL] at hk
      contradiction
    · have hLpos : 0 < (L : ℝ) := by
        exact lt_of_le_of_ne (show 0 ≤ (L : ℝ) by exact_mod_cast L.2) (Ne.symm hL)
      have h2Lpos : 0 < 2 * (L : ℝ) := by
        positivity
      have hk' : f (method k) < (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) / (2 * (L : ℝ)) := by
        simpa [modifiedGaussNewtonQuadraticMeritThreshold, div_eq_mul_inv, mul_assoc,
          mul_left_comm, mul_comm] using hk
      have hmul : 2 * (L : ℝ) * f (method k) < σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) := by
        exact (lt_div_iff h2Lpos).1 hk'
      have hbound :
          2 * (L : ℝ) * (f (method k)) ^ (2 : ℕ) ≤
            (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) * f (method k) := by
        -- Multiply the threshold inequality by the nonnegative factor `f(x_k)`.
        nlinarith
      have hgoal :
          ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) ≤
            (1 / 2 : ℝ) * f (method k) := by
        field_simp [hd]
        nlinarith [hbound]
      exact hgoal

-- Proof sketch: repeat the argument from the first part, but use the fixed-parameter hypothesis
-- `M_k = L`. The same one-dimensional majorant now has quadratic coefficient `L / 2`, so when
-- `f(x_k) ≥ (σ² / L) γφ²` its minimizer yields the sharper linear decrease `(4.4.25)`.
/-- Theorem 4.4.3 (3): if Algorithm 4.4.1 is run with the fixed regularization rule `M_k ≡ L`
and `f(x_k) ≥ (σ² / L) γ_φ²`, then
`f(x_{k+1}) ≤ f(x_k) - (σ² / (2L)) γ_φ²`. As above, the feasible-set input is only the
sublevel containment `𝓛[f]((f x₀)) ⊆ 𝓕`. -/
theorem modifiedGaussNewton_fixed_regularization_large_value_oneStep_decrease
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (hregularization : ∀ k : ℕ, method.regularization k = (L : ℝ))
    (k : ℕ)
    (hk :
      ((σ ^ (2 : ℕ)) / (L : ℝ)) * γφ ^ (2 : ℕ) ≤
        f (method k)) :
    f (method (k + 1)) ≤
      f (method k) - ((σ ^ (2 : ℕ)) / (2 * (L : ℝ))) * γφ ^ (2 : ℕ) := by
  have hσ_pos : 0 < σ :=
    HasUniformDualNondegeneracyOnInitialSublevelSet.sigma_pos hσ
  have hL_pos : 0 < (L : ℝ) := by
    exact lt_of_lt_of_le method.L0_pos method.L0_le_L
  have hfk_pos : 0 < f (method k) := by
    -- The fixed-regularization large-value threshold is strictly positive.
    have hthreshold_pos :
        0 < ((σ ^ (2 : ℕ)) / (L : ℝ)) * γφ ^ (2 : ℕ) := by
      positivity
    exact lt_of_lt_of_le hthreshold_pos hk
  let t : ℝ := (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) / ((L : ℝ) * f (method k))
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have hmul :
      σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) ≤ (L : ℝ) * f (method k) := by
    have hk' :
        (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) / (L : ℝ) ≤ f (method k) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hk
    exact (div_le_iff hL_pos).1 hk'
  have ht_le_one : t ≤ 1 := by
    -- The stronger fixed-regularization threshold again forces the minimizing scalar into `[0,1]`.
    dsimp [t]
    have hden_pos : 0 < (L : ℝ) * f (method k) := by
      positivity
    have hmul' : σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) ≤ 1 * ((L : ℝ) * f (method k)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact (div_le_iff hden_pos).2 hmul'
  have hmajorant :=
    modifiedGaussNewton_fixed_regularization_one_step_majorant
      (method := method) (hσ := hσ) hγφ_pos hγφ_lower hregularization k ht_nonneg ht_le_one
  have hrepack :
      (1 - t) * f (method k) +
          ((L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * t ^ (2 : ℕ) *
            (f (method k)) ^ (2 : ℕ) =
        f (method k) - ((σ ^ (2 : ℕ)) / (2 * (L : ℝ))) * γφ ^ (2 : ℕ) := by
    -- The fixed-`L` quadratic majorant has the sharper minimizer `t = σ²γφ² / (L f_k)`.
    dsimp [t]
    field_simp [hL_pos.ne', hσ_pos.ne', hγφ_pos.ne', hfk_pos.ne']
    ring
  rwa [hrepack] at hmajorant

-- Proof sketch: in the fixed-parameter case `M_k = L`, the scalar majorant from the textbook
-- proof is minimized at `t = 1` whenever `f(x_k) < (σ² / L) γφ²`. This gives the quadratic bound
-- in `(4.4.26)`.
/-- Theorem 4.4.3 (4): if Algorithm 4.4.1 is run with `M_k ≡ L` and
`f(x_k) < (σ² / L) γ_φ²`, then
`f(x_{k+1}) ≤ (L / (2 σ² γ_φ²)) f(x_k)^2`, again using only the sublevel containment
`𝓛[f]((f x₀)) ⊆ 𝓕` from Assumption 4.4.2. -/
theorem modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (hregularization : ∀ k : ℕ, method.regularization k = (L : ℝ))
    (k : ℕ)
    (hk :
      f (method k) <
        ((σ ^ (2 : ℕ)) / (L : ℝ)) * γφ ^ (2 : ℕ)) :
    f (method (k + 1)) ≤
      ((L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) := by
  -- The fixed-regularization small-value branch is the endpoint specialization `t = 1`.
  have hone_nonneg : 0 ≤ (1 : ℝ) := by
    norm_num
  have hone_le : (1 : ℝ) ≤ 1 := by
    norm_num
  have hmajorant :=
    modifiedGaussNewton_fixed_regularization_one_step_majorant
      (method := method) (hσ := hσ) hγφ_pos hγφ_lower hregularization k hone_nonneg hone_le
  simpa using hmajorant

-- Proof sketch: the stronger threshold `f(x_k) < (σ² / L) γφ²` implies by scalar algebra that
-- the quadratic upper bound from Theorem 4.4.3 (4) is bounded by one half of `f(x_k)`.
/-- In the fixed-regularization small-value regime, the quadratic upper bound from
`modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay` is at most half of the
current merit value. -/
theorem modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay_le_half_current
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (k : ℕ)
    (hk :
      f (method k) <
        ((σ ^ (2 : ℕ)) / (L : ℝ)) * γφ ^ (2 : ℕ)) :
    ((L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * f (method k) := by
  have hfk_nonneg : 0 ≤ f (method k) := by
    -- Merit functions are nonnegative on every residual value.
    simpa [meritFunctionReformulation] using
      (IsMeritFunction.nonneg (φ := φ) (problem (method k)))
  by_cases hd : σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) = 0
  · -- If the denominator vanishes, the left-hand side is `0`.
    simp [hd]
    nlinarith
  · by_cases hL : (L : ℝ) = 0
    · -- If `L = 0`, then the threshold is `0`, again contradicting merit nonnegativity.
      have : ¬ f (method k) < 0 := not_lt_of_ge hfk_nonneg
      simp [hL] at hk
      contradiction
    · have hLpos : 0 < (L : ℝ) := by
        exact lt_of_le_of_ne (show 0 ≤ (L : ℝ) by exact_mod_cast L.2) (Ne.symm hL)
      have hk' : f (method k) < (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) / (L : ℝ) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hk
      have hmul : (L : ℝ) * f (method k) < σ ^ (2 : ℕ) * γφ ^ (2 : ℕ) := by
        exact (lt_div_iff hLpos).1 hk'
      have hbound :
          (L : ℝ) * (f (method k)) ^ (2 : ℕ) ≤
            (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ)) * f (method k) := by
        -- Multiply the threshold inequality by the nonnegative factor `f(x_k)`.
        nlinarith
      have hgoal :
          ((L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) ≤
            (1 / 2 : ℝ) * f (method k) := by
        field_simp [hd]
        nlinarith [hbound]
      exact hgoal

end
