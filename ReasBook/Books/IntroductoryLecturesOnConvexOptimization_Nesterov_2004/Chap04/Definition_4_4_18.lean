/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped InnerProduct
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

/- Definition 4.4.18 lies in the modified Gauss--Newton optimal-value / strong-dual norm-duality
domain.

Sampled owner-style declarations:
* `modifiedGaussNewtonOptimalValueAt` in `Proposition_4_4_6`, the chapter owner for the
  whole-space quadratic-regularized optimal value;
* `modifiedGaussNewtonLocalModel` in `Definition_4_4_11`, the chapter owner for the affine
  residual model;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the project owner for the
  centered quadratic penalty inside that optimal-value owner;
* `dual_norm_eq_sSup_closedUnitBall` in `Definition_4_4_4`, the chapter bridge expressing the
  strong-dual norm as a support function of the closed unit ball;
* `ContinuousLinearMap.comp` in mathlib, the canonical owner for precomposing a strong-dual
  functional with a continuous linear map;
* `InnerProductSpace.toDual` in mathlib, the Chapter 4 bridge from Hilbert-space vectors to the
  intrinsic strong dual.

Best owner abstraction:
* core/canonical: `modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x`

Source/core/bridge triage:
* source-facing: the specialized auxiliary value `f_M(x)` for the norm merit and its dual-ball
  formula;
* core/canonical: the Chapter 4 optimal-value owner above;
* bridge/view: the step-variable expansion, the strong-dual closed-ball objective, and the
  Hilbert-space `toDual` specialization.

Primitive data:
* a residual map `F`;
* a Jacobian family `J`;
* a base point `x`.

Derived API:
* the step-variable `sInf` expansion of the canonical owner;
* the positive-parameter dual objective over the closed unit ball in the strong dual;
* the `toDual` specialization recovering the textbook adjoint formula on Hilbert-space vectors.

This refinement deletes the duplicate local `ℝ`-valued infimum owner and reuses the Chapter 4
canonical owner directly. The file now keeps only the norm-specific bridge API. -/

variable {E₁ : Type u} {E₂ : Type v}

section AuxiliaryValue

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

variable (F : E₁ → E₂) (J : E₁ → E₁ →L[ℝ] E₂) (x : E₁)

/- Definition 4.4.18: the specialized auxiliary value `f_M(x)` for the merit `u ↦ ‖u‖` is the
canonical Chapter 4 optimal-value owner specialized to the norm local model. -/
set_option linter.hashCommand false in
#check (modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x : ℝ → EReal)

/-- Unfolding the canonical norm-specialized optimal-value owner recovers the textbook infimum of
the quadratic-regularized linearized residual objective over all steps `h`. -/
theorem modifiedGaussNewtonOptimalValueAt_norm_eq_sInf_range
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : ℝ) :
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x M =
      sInf (Set.range fun h ↦
        (‖F x + J x h‖ + (M / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) : EReal)) := by
  -- Rewrite the whole-space owner to the step variable `h = y - x`.
  rw [modifiedGaussNewtonOptimalValueAt_eq_sInf_range]
  congr 1
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y - x, ?_⟩
    simp only [quadraticallyRegularizedObjective_apply, modifiedGaussNewtonLocalModel_apply]
    exact_mod_cast
      (show ‖F x + (J x) (y - x)‖ + (M / 2) * ‖y - x‖ ^ (2 : ℕ) =
          ‖F x + (J x) (y - x)‖ + (M / 2) * ‖y - x‖ ^ (2 : ℕ) by
        rfl)
  · rintro ⟨h, rfl⟩
    refine ⟨h + x, ?_⟩
    simp only [quadraticallyRegularizedObjective_apply, modifiedGaussNewtonLocalModel_apply]
    have hshift :
        ‖F x + (J x) (h + x - x)‖ + (M / 2) * ‖h + x - x‖ ^ (2 : ℕ) =
          ‖F x + (J x) h‖ + (M / 2) * ‖h‖ ^ (2 : ℕ) := by
      simp
    exact_mod_cast hshift

end AuxiliaryValue

section DualObjective

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The intrinsic strong-dual objective corresponding to the norm auxiliary problem at a positive
regularization parameter `M`. -/
def modifiedGaussNewtonNormDualObjective
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) : StrongDual ℝ E₂ → ℝ :=
  fun s ↦ s (F x) -
    (1 / (2 * (M : ℝ)) : ℝ) * ‖s.comp (J x)‖ ^ (2 : ℕ)

/-- Evaluating the intrinsic strong-dual objective gives the canonical precomposition formula. -/
@[simp] theorem modifiedGaussNewtonNormDualObjective_apply
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) (s : StrongDual ℝ E₂) :
    modifiedGaussNewtonNormDualObjective F J M x s =
      s (F x) -
        (1 / (2 * (M : ℝ)) : ℝ) * ‖s.comp (J x)‖ ^ (2 : ℕ) := by
  rfl

/-- Helper for Definition 4.4.18: every linear functional plus the positive quadratic penalty is
bounded below by the expected Legendre-transform value. -/
lemma linear_functional_add_quadratic_ge_neg_sq_div
    (ℓ : StrongDual ℝ E₁) (M : NNRealˣ) (h : E₁) :
    -((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) ≤
      ℓ h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) := by
  -- First bound the linear term from below by the operator norm estimate.
  have hℓ : -(‖ℓ‖ * ‖h‖) ≤ ℓ h := by
    have hop : ‖ℓ h‖ ≤ ‖ℓ‖ * ‖h‖ := by
      simpa using ℓ.le_opNorm h
    calc
      -(‖ℓ‖ * ‖h‖) ≤ -‖ℓ h‖ := by
        linarith
      _ = -|ℓ h| := by
        simp [Real.norm_eq_abs]
      _ ≤ ℓ h := by
        simpa using neg_abs_le (ℓ h)
  -- Then complete the scalar square in the norm variable.
  have hM_nn : 0 < (M : NNReal) := pos_iff_ne_zero.mpr (Units.ne_zero M)
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast hM_nn
  have htwo :
      2 * (‖h‖ * ‖ℓ‖) ≤
        (M : ℝ) * ‖h‖ ^ (2 : ℕ) + ((M : ℝ)⁻¹ * ‖ℓ‖ ^ (2 : ℕ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (two_mul_le_add_mul_sq (a := ‖h‖) (b := ‖ℓ‖) (ε := (M : ℝ)) hM)
  have hyoung :
      ‖ℓ‖ * ‖h‖ ≤
        (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) +
          ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) := by
    have hm_ne : (M : ℝ) ≠ 0 := by
      linarith
    have hscaled :
        2 * (M : ℝ) * (‖ℓ‖ * ‖h‖) ≤
          2 * (M : ℝ) *
            ((((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) +
              ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ))) := by
      have hmul := mul_le_mul_of_nonneg_left htwo hM.le
      simpa [div_eq_mul_inv, mul_add, mul_assoc, mul_left_comm, mul_comm, hm_ne] using hmul
    have hcoeff_pos : 0 < 2 * (M : ℝ) := by
      positivity
    nlinarith [hcoeff_pos, hscaled]
  nlinarith [hℓ, hyoung]

/-- Helper for Definition 4.4.18: the norm of a primal vector is the support value of the closed
unit ball in the strong dual. -/
lemma norm_eq_sSup_dualClosedBall
    (u : E₂) :
    ‖u‖ =
      sSup ((fun s : StrongDual ℝ E₂ ↦ s u) '' closedBall (0 : StrongDual ℝ E₂) 1) := by
  let S : Set ℝ := (fun s : StrongDual ℝ E₂ ↦ s u) '' closedBall (0 : StrongDual ℝ E₂) 1
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, by simp, by simp⟩
  have hS_bound : ∀ y ∈ S, y ≤ ‖u‖ := by
    intro y hy
    rcases hy with ⟨s, hs_ball, rfl⟩
    have hs_norm : ‖s‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hs_ball
    have hs_eval : s u ≤ ‖u‖ := by
      have hop : ‖s u‖ ≤ ‖s‖ * ‖u‖ := by
        simpa using s.le_opNorm u
      calc
        s u ≤ |s u| := by
          exact le_abs_self _
        _ = ‖s u‖ := by
          simp [Real.norm_eq_abs]
        _ ≤ ‖s‖ * ‖u‖ := hop
        _ ≤ 1 * ‖u‖ := by
          exact mul_le_mul_of_nonneg_right hs_norm (norm_nonneg _)
        _ = ‖u‖ := by
          ring
    exact hs_eval
  have hS_bdd : BddAbove S := ⟨‖u‖, hS_bound⟩
  obtain ⟨s, hs_norm, hs_eval⟩ := exists_dual_vector'' ℝ u
  have hs_ball : s ∈ closedBall (0 : StrongDual ℝ E₂) 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hs_norm
  have hnorm_le : ‖u‖ ≤ sSup S := by
    refine le_csSup hS_bdd ?_
    exact ⟨s, hs_ball, hs_eval⟩
  have hsSup_le : sSup S ≤ ‖u‖ := csSup_le hS_nonempty hS_bound
  simpa [S] using le_antisymm hnorm_le hsSup_le

/-- Helper for Definition 4.4.18: for a fixed primal step, the negated dual-ball slice has the
expected greatest lower bound given by the norm support formula. -/
lemma neg_dual_pairing_add_quadratic_isGLB
    (u : E₂) (A : E₁ →L[ℝ] E₂) (M : NNRealˣ) (h : E₁) :
    IsGLB
      {r : ℝ | ∃ s : StrongDual ℝ E₂, s ∈ closedBall (0 : StrongDual ℝ E₂) 1 ∧
          r = -(s (u + A h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))}
      (-(‖u + A h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))) := by
  -- First show that every dual-ball slice lies above the negated norm support value.
  constructor
  · intro r hr
    rcases hr with ⟨s, hs_ball, rfl⟩
    have hs_norm : ‖s‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hs_ball
    have hs_eval : s (u + A h) ≤ ‖u + A h‖ := by
      have hop : ‖s (u + A h)‖ ≤ ‖s‖ * ‖u + A h‖ := by
        simpa using s.le_opNorm (u + A h)
      calc
        s (u + A h) ≤ |s (u + A h)| := by
          exact le_abs_self _
        _ = ‖s (u + A h)‖ := by
          simp [Real.norm_eq_abs]
        _ ≤ ‖s‖ * ‖u + A h‖ := hop
        _ ≤ 1 * ‖u + A h‖ := by
          exact mul_le_mul_of_nonneg_right hs_norm (norm_nonneg _)
        _ = ‖u + A h‖ := by
          ring
    linarith
  · intro b hb
    -- Then choose a Hahn-Banach support functional attaining the norm of `u + A h`.
    obtain ⟨s, hs_norm, hs_eval⟩ := exists_dual_vector'' ℝ (u + A h)
    have hs_ball : s ∈ closedBall (0 : StrongDual ℝ E₂) 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hs_norm
    change ∀ z ∈ {r : ℝ | ∃ s : StrongDual ℝ E₂, s ∈ closedBall (0 : StrongDual ℝ E₂) 1 ∧
      z = -(s (u + A h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))}, b ≤ z at hb
    have hb_slice : b ≤ -(s (u + A h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) := by
      exact hb _ ⟨s, hs_ball, rfl⟩
    simpa [hs_eval]
      using hb_slice

/-- Helper for Definition 4.4.18: the dual-ball objective always gives a lower bound on the
canonical norm-specialized auxiliary value. -/
theorem modifiedGaussNewtonOptimalValueAt_norm_ge_sSup_dualObjective
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) :
    sSup ((((↑) : ℝ → EReal) ∘ modifiedGaussNewtonNormDualObjective F J M x) ''
        closedBall (0 : StrongDual ℝ E₂) 1) ≤
      modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x (M : ℝ) := by
  -- Expand the primal owner to the step-variable infimum before proving weak duality pointwise.
  rw [modifiedGaussNewtonOptimalValueAt_norm_eq_sInf_range]
  refine le_sInf ?_
  rintro _ ⟨h, rfl⟩
  refine sSup_le ?_
  intro z hz
  rcases hz with ⟨s, hs_ball, rfl⟩
  have hs_norm : ‖s‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hs_ball
  have hsupport : s (F x + J x h) ≤ ‖F x + J x h‖ := by
    have hop : ‖s (F x + J x h)‖ ≤ ‖s‖ * ‖F x + J x h‖ := by
      simpa using s.le_opNorm (F x + J x h)
    calc
      s (F x + J x h) ≤ |s (F x + J x h)| := by
        exact le_abs_self _
      _ = ‖s (F x + J x h)‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖s‖ * ‖F x + J x h‖ := hop
      _ ≤ 1 * ‖F x + J x h‖ := by
        exact mul_le_mul_of_nonneg_right hs_norm (norm_nonneg _)
      _ = ‖F x + J x h‖ := by
        ring
  have hslice :
      -((1 / (2 * (M : ℝ)) : ℝ) * ‖s.comp (J x)‖ ^ (2 : ℕ)) ≤
        (s.comp (J x)) h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) :=
    linear_functional_add_quadratic_ge_neg_sq_div (ℓ := s.comp (J x)) (M := M) h
  have hreal :
      modifiedGaussNewtonNormDualObjective F J M x s ≤
        ‖F x + J x h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) := by
    -- Combine the slice bound with the unit-ball support inequality.
    calc
      modifiedGaussNewtonNormDualObjective F J M x s
          = s (F x) -
              (1 / (2 * (M : ℝ)) : ℝ) * ‖s.comp (J x)‖ ^ (2 : ℕ) := by
              simp [modifiedGaussNewtonNormDualObjective]
      _ ≤ s (F x) + ((s.comp (J x)) h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) := by
            linarith
      _ = (s (F x) + s (J x h)) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) := by
            simp [ContinuousLinearMap.comp_apply, add_assoc]
      _ = s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) := by
            rw [ContinuousLinearMap.map_add]
      _ ≤ ‖F x + J x h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) := by
            linarith
  exact EReal.coe_le_coe hreal

/-- Helper for Definition 4.4.18: every strict sub-norm level is attained by evaluation at some
point of the primal closed unit ball. -/
lemma existsLtApplyClosedBallOfLtDualNorm
    (ℓ : StrongDual ℝ E₁) {c : ℝ} (hc : c < ‖ℓ‖) :
    ∃ v ∈ closedBall (0 : E₁) 1, c < ℓ v := by
  let S : Set ℝ := ℓ '' closedBall (0 : E₁) 1
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, by simp, by simp⟩
  have hS_bdd : BddAbove S := by
    refine ⟨‖ℓ‖, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    have hv_norm : ‖v‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hv
    have hop : ‖ℓ v‖ ≤ ‖ℓ‖ * ‖v‖ := by
      simpa using ℓ.le_opNorm v
    calc
      ℓ v ≤ |ℓ v| := by
        exact le_abs_self _
      _ = ‖ℓ v‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖ℓ‖ * ‖v‖ := hop
      _ ≤ ‖ℓ‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _)
      _ = ‖ℓ‖ := by
        ring
  have hc' : c < sSup S := by
    exact hc.trans_eq (by simpa [S] using dual_norm_eq_sSup_closedUnitBall (s := ℓ))
  -- Convert the strict inequality below the support supremum into an explicit support vector.
  rcases (lt_csSup_iff hS_bdd hS_nonempty).mp hc' with ⟨y, hy, hcy⟩
  rcases hy with ⟨v, hv, rfl⟩
  exact ⟨v, hv, hcy⟩

/-- Helper for Definition 4.4.18: every strict lower candidate for the Legendre-transform value is
beaten by an explicit primal step. -/
lemma exists_neg_linear_functional_add_quadratic_gt
    (ℓ : StrongDual ℝ E₁) (M : NNRealˣ) {b : ℝ}
    (hb : b < ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ))) :
    ∃ h : E₁, b < -(ℓ h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) := by
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero M))
  by_cases hb_nonneg : 0 ≤ b
  · have hx_nonneg : 0 ≤ 2 * (M : ℝ) * b := by positivity
    have hcoeff : 0 < 2 * (M : ℝ) := by positivity
    have hnorm_sq : 2 * (M : ℝ) * b < ‖ℓ‖ ^ (2 : ℕ) := by
      have hm_ne : (M : ℝ) ≠ 0 := by linarith
      have hscaled :
          2 * (M : ℝ) * b <
            2 * (M : ℝ) *
              (((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ))) := by
        exact mul_lt_mul_of_pos_left hb hcoeff
      simpa [div_eq_mul_inv, hm_ne, mul_assoc, mul_left_comm, mul_comm] using hscaled
    have hsqrt_lt : Real.sqrt (2 * (M : ℝ) * b) < ‖ℓ‖ := by
      exact (Real.sqrt_lt hx_nonneg (norm_nonneg _)).2 hnorm_sq
    obtain ⟨c, hsqrt_lt_c, hc_lt_norm⟩ := exists_between hsqrt_lt
    have hc_nonneg : 0 ≤ c := by
      exact le_trans (Real.sqrt_nonneg _) hsqrt_lt_c.le
    have hc_pos : 0 < c := by
      exact lt_of_le_of_lt (Real.sqrt_nonneg _) hsqrt_lt_c
    have hscale_nonneg : 0 ≤ c / (M : ℝ) := by positivity
    have hb_lt_csq : b < c ^ (2 : ℕ) / (2 * (M : ℝ)) := by
      have hsq : 2 * (M : ℝ) * b < c ^ (2 : ℕ) := by
        exact (Real.sqrt_lt' hc_pos).1 hsqrt_lt_c
      rw [lt_div_iff₀ hcoeff]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hsq
    obtain ⟨v, hv_ball, hcv⟩ := existsLtApplyClosedBallOfLtDualNorm (ℓ := ℓ) hc_lt_norm
    have hv_norm : ‖v‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hv_ball
    have hquad_le :
        (((M : ℝ) / 2 : ℝ) * ‖-((c / (M : ℝ)) • v)‖ ^ (2 : ℕ)) ≤
          c ^ (2 : ℕ) / (2 * (M : ℝ)) := by
      have hnorm_le : ‖-((c / (M : ℝ)) • v)‖ ≤ c / (M : ℝ) := by
        calc
          ‖-((c / (M : ℝ)) • v)‖ = ‖(c / (M : ℝ)) • v‖ := by
            simp
          _ = |c| / (M : ℝ) * ‖v‖ := by
            simpa [Real.norm_eq_abs] using (norm_smul (c / (M : ℝ)) v)
          _ = (c / (M : ℝ)) * ‖v‖ := by
            simp [abs_of_nonneg hc_nonneg, div_eq_mul_inv]
          _ ≤ (c / (M : ℝ)) * 1 := by
            exact mul_le_mul_of_nonneg_left hv_norm hscale_nonneg
          _ = c / (M : ℝ) := by
            ring
      have hnorm_sq_le : ‖-((c / (M : ℝ)) • v)‖ ^ (2 : ℕ) ≤ (c / (M : ℝ)) ^ (2 : ℕ) := by
        rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hscale_nonneg]
        exact hnorm_le
      have hm_ne : (M : ℝ) ≠ 0 := by linarith
      calc
        (((M : ℝ) / 2 : ℝ) * ‖-((c / (M : ℝ)) • v)‖ ^ (2 : ℕ)) ≤
            (((M : ℝ) / 2 : ℝ) * (c / (M : ℝ)) ^ (2 : ℕ)) := by
          gcongr
        _ = c ^ (2 : ℕ) / (2 * (M : ℝ)) := by
          field_simp [hm_ne]
    refine ⟨-((c / (M : ℝ)) • v), ?_⟩
    have hlin :
        (c / (M : ℝ)) * c ≤ (c / (M : ℝ)) * ℓ v := by
      exact mul_le_mul_of_nonneg_left hcv.le hscale_nonneg
    have hm_ne : (M : ℝ) ≠ 0 := by linarith
    -- Scale a near-support vector so that the linear gain dominates the quadratic loss.
    calc
      b < c ^ (2 : ℕ) / (2 * (M : ℝ)) := hb_lt_csq
      _ = (c / (M : ℝ)) * c - c ^ (2 : ℕ) / (2 * (M : ℝ)) := by
        field_simp [hm_ne]
        ring
      _ ≤ (c / (M : ℝ)) * ℓ v -
            (((M : ℝ) / 2 : ℝ) * ‖-((c / (M : ℝ)) • v)‖ ^ (2 : ℕ)) := by
        linarith
      _ = -(-((c / (M : ℝ)) * ℓ v) +
            (((M : ℝ) / 2 : ℝ) * ‖-((c / (M : ℝ)) • v)‖ ^ (2 : ℕ))) := by
        ring
      _ = -(ℓ (-((c / (M : ℝ)) • v)) +
            (((M : ℝ) / 2 : ℝ) * ‖-((c / (M : ℝ)) • v)‖ ^ (2 : ℕ))) := by
        congr 1
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  · refine ⟨0, ?_⟩
    -- Negative lower candidates are already beaten by the zero step.
    have hb_neg : b < 0 := lt_of_not_ge hb_nonneg
    simpa using hb_neg

/-- Helper for Definition 4.4.18: the negated linear-plus-quadratic slice has the expected least
upper bound `‖ℓ‖² / (2M)`. -/
lemma neg_linear_functional_add_quadratic_isLUB
    (ℓ : StrongDual ℝ E₁) (M : NNRealˣ) :
    IsLUB
      (Set.range fun h : E₁ ↦ -(ℓ h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))))
      ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) := by
  constructor
  · rintro y ⟨h, rfl⟩
    -- The quadratic lower bound gives the universal upper bound after negation.
    have hbound :=
      linear_functional_add_quadratic_ge_neg_sq_div (ℓ := ℓ) (M := M) h
    linarith
  · intro b hb
    by_contra htarget
    have hlt_target : b < ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) := by
      exact lt_of_not_ge htarget
    obtain ⟨h, hh⟩ :=
      exists_neg_linear_functional_add_quadratic_gt (ℓ := ℓ) (M := M) hlt_target
    have hb_at_h :
        -(ℓ h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) ≤ b := by
      exact hb ⟨h, rfl⟩
    linarith

/-- Helper for Definition 4.4.18: on the weak-* dual closed ball, the fixed-step negated payoff
has the same infimum value as on the strong-dual closed ball. -/
lemma weakDual_closedBall_iInf_neg_payoff_eq
    (u : E₂) (A : E₁ →L[ℝ] E₂) (M : NNRealˣ) (h : E₁) :
    let B : Set (WeakDual ℝ E₂) :=
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
    ⨅ s ∈ B,
      -(WeakDual.toStrongDual s (u + A h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) =
        -(‖u + A h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) := by
  let B : Set (WeakDual ℝ E₂) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
  let ψ : WeakDual ℝ E₂ → ℝ := fun s ↦
    -(WeakDual.toStrongDual s (u + A h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
  have hB_nonempty : B.Nonempty := by
    -- The weak-* closed unit ball contains the zero functional.
    refine ⟨0, ?_⟩
    simp [B]
  have himage :
      ψ '' B =
        {r : ℝ | ∃ s : StrongDual ℝ E₂, s ∈ closedBall (0 : StrongDual ℝ E₂) 1 ∧
          r = -(s (u + A h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))} := by
    -- Transport the value set across the linear equivalence `toStrongDual`.
    ext r
    constructor
    · rintro ⟨s, hsB, rfl⟩
      exact ⟨WeakDual.toStrongDual s, hsB, rfl⟩
    · rintro ⟨s, hs_ball, rfl⟩
      refine ⟨StrongDual.toWeakDual s, ?_, ?_⟩
      · change s ∈ closedBall (0 : StrongDual ℝ E₂) 1
        simpa using hs_ball
      · simp [ψ]
  have hglb :
      IsGLB (ψ '' B)
        (-(‖u + A h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))) := by
    -- Reuse the strong-dual GLB computation after identifying the image sets.
    rw [himage]
    exact neg_dual_pairing_add_quadratic_isGLB (u := u) (A := A) (M := M) (h := h)
  have hψ_bdd : BddBelow (Set.range fun x : B ↦ ψ x) := by
    refine ⟨-(‖u + A h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hglb.1 ⟨x, x.property, rfl⟩
  have hψ_inf : (⨅ x : B, ψ x) ≤ sInf (∅ : Set ℝ) := by
    have hzero : (0 : WeakDual ℝ E₂) ∈ B := by
      simp [B]
    have hzero_val : ψ 0 ≤ sInf (∅ : Set ℝ) := by
      have hquad_nonneg : 0 ≤ (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) := by
        positivity
      rw [Real.sInf_empty]
      change
        -(((0 : StrongDual ℝ E₂) (u + A h)) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) ≤ 0
      simp
    exact (ciInf_le hψ_bdd ⟨0, hzero⟩).trans (by simpa using hzero_val)
  have hsub :
      (⨅ s ∈ B, ψ s) = ⨅ x : B, ψ x := by
    simpa using
      (cbiInf_eq_ciInf_subtype (p := fun s : WeakDual ℝ E₂ ↦ s ∈ B)
        (f := fun s _ ↦ ψ s) hψ_bdd hψ_inf)
  -- Convert the GLB of the image set back to the indexed infimum over the weak-* ball.
  have hmain :
      (⨅ s ∈ B, ψ s) = -(‖u + A h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) := by
    calc
    (⨅ s ∈ B, ψ s) = ⨅ x : B, ψ x := hsub
    _ = -(‖u + A h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) := by
      simpa [ψ] using hglb.ciInf_set_eq hB_nonempty
  simpa [B, ψ] using hmain

/-- Helper for Definition 4.4.18: the fixed weak-* dual slice has supremum equal to the negative
of the intrinsic dual objective. -/
lemma weakDual_closedBall_iSup_neg_payoff_eq
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) (s : WeakDual ℝ E₂) :
    (⨆ h : E₁,
      -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))) =
        -modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s) := by
  let ℓ : StrongDual ℝ E₁ := (WeakDual.toStrongDual s).comp (J x)
  let q : E₁ → ℝ := fun h ↦ -(ℓ h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
  let c : ℝ := -(WeakDual.toStrongDual s (F x))
  have hq_lub :
      IsLUB (Set.range q) ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) := by
    simpa [q, ℓ] using neg_linear_functional_add_quadratic_isLUB (ℓ := ℓ) (M := M)
  have hq_nonempty : (Set.range q).Nonempty := by
    exact ⟨q 0, ⟨0, rfl⟩⟩
  have hq_bdd : BddAbove (Set.range q) := by
    refine ⟨((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)), ?_⟩
    intro y hy
    exact hq_lub.1 hy
  have hrange :
      Set.range (fun h : E₁ ↦
        -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))) =
        OrderIso.addRight c '' Set.range q := by
    -- Split the fixed-dual payoff into a constant shift plus the quadratic conjugate slice.
    ext r
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨q h, ⟨h, rfl⟩, ?_⟩
      simp [q, c, ℓ, ContinuousLinearMap.comp_apply, add_assoc]
    · rintro ⟨z, ⟨h, rfl⟩, hz⟩
      refine ⟨h, ?_⟩
      simpa [q, c, ℓ, ContinuousLinearMap.comp_apply, add_assoc] using hz
  have hsSup_q :
      sSup (Set.range q) = ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) := by
    exact hq_lub.csSup_eq hq_nonempty
  -- Transport the supremum through the additive order isomorphism and identify the dual objective.
  calc
    (⨆ h : E₁,
      -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))) =
        sSup (Set.range fun h : E₁ ↦
          -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))) := by
      rfl
    _ = c + ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) := by
      rw [hrange, ← OrderIso.map_csSup' (OrderIso.addRight c) hq_nonempty hq_bdd, hsSup_q,
        OrderIso.addRight_apply]
      ring
    _ = -modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s) := by
      simp [modifiedGaussNewtonNormDualObjective, c, ℓ, sub_eq_add_neg]
      ring

/-- Helper for Definition 4.4.18: the weak-* dual-ball image of the norm dual objective is exactly
the strong-dual closed-ball image appearing in the theorem statement. -/
lemma weakDual_dualObjective_image_eq_strongDual_image
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) :
    let B : Set (WeakDual ℝ E₂) :=
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
    (fun s : WeakDual ℝ E₂ ↦
      modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s)) '' B =
      modifiedGaussNewtonNormDualObjective F J M x '' closedBall (0 : StrongDual ℝ E₂) 1 := by
  let B : Set (WeakDual ℝ E₂) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
  -- The weak-* and strong dual closed balls are identified by the inverse linear equivalences.
  ext r
  constructor
  · rintro ⟨s, hsB, rfl⟩
    exact ⟨WeakDual.toStrongDual s, hsB, rfl⟩
  · rintro ⟨s, hs_ball, rfl⟩
    refine ⟨StrongDual.toWeakDual s, ?_, ?_⟩
    · change s ∈ closedBall (0 : StrongDual ℝ E₂) 1
      simpa using hs_ball
    · change
        modifiedGaussNewtonNormDualObjective F J M x
            (WeakDual.toStrongDual (StrongDual.toWeakDual s)) =
          modifiedGaussNewtonNormDualObjective F J M x s
      simpa using congrArg (modifiedGaussNewtonNormDualObjective F J M x)
        (show WeakDual.toStrongDual (StrongDual.toWeakDual s) = s by rfl)

/-- Helper for Definition 4.4.18: on the weak-* closed dual ball, the intrinsic dual objective is
bounded above by the residual norm `‖F x‖`. -/
lemma weakDualDualObjective_le_norm_of_mem_closedBall
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) {s : WeakDual ℝ E₂}
    (hs : s ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1) :
    modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s) ≤ ‖F x‖ := by
  have hs_norm : ‖WeakDual.toStrongDual s‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hs
  have hs_eval : WeakDual.toStrongDual s (F x) ≤ ‖F x‖ := by
    -- The unit-ball constraint bounds every evaluation by the residual norm.
    have hop :
        ‖WeakDual.toStrongDual s (F x)‖ ≤ ‖WeakDual.toStrongDual s‖ * ‖F x‖ := by
      simpa using (WeakDual.toStrongDual s).le_opNorm (F x)
    calc
      WeakDual.toStrongDual s (F x) ≤ |WeakDual.toStrongDual s (F x)| := by
        exact le_abs_self _
      _ = ‖WeakDual.toStrongDual s (F x)‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖WeakDual.toStrongDual s‖ * ‖F x‖ := hop
      _ ≤ 1 * ‖F x‖ := by
        exact mul_le_mul_of_nonneg_right hs_norm (norm_nonneg _)
      _ = ‖F x‖ := by
        ring
  have hquad_nonneg :
      0 ≤
        (1 / (2 * (M : ℝ)) : ℝ) * ‖(WeakDual.toStrongDual s).comp (J x)‖ ^ (2 : ℕ) := by
    positivity
  -- Dropping the nonnegative quadratic term leaves the desired upper bound.
  calc
    modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s) =
        WeakDual.toStrongDual s (F x) -
          (1 / (2 * (M : ℝ)) : ℝ) * ‖(WeakDual.toStrongDual s).comp (J x)‖ ^ (2 : ℕ) := by
      simp [modifiedGaussNewtonNormDualObjective]
    _ ≤ WeakDual.toStrongDual s (F x) := by
      linarith
    _ ≤ ‖F x‖ := hs_eval

/-- Helper for Definition 4.4.18: for a fixed primal step, the weak-* payoff slice on the closed
dual ball is lower semicontinuous and quasiconvex. -/
lemma weakDualPayoff_leftSliceSionData
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) (h : E₁) :
    let B : Set (WeakDual ℝ E₂) :=
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
    let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s h' ↦
      -(WeakDual.toStrongDual s (F x + J x h') + (((M : ℝ) / 2 : ℝ) * ‖h'‖ ^ (2 : ℕ)))
    LowerSemicontinuousOn (fun s : WeakDual ℝ E₂ ↦ Φ s h) B ∧
      QuasiconvexOn ℝ B (fun s : WeakDual ℝ E₂ ↦ Φ s h) := by
  let B : Set (WeakDual ℝ E₂) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
  let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s h' ↦
    -(WeakDual.toStrongDual s (F x + J x h') + (((M : ℝ) / 2 : ℝ) * ‖h'‖ ^ (2 : ℕ)))
  let v : E₂ := F x + J x h
  let c : ℝ := (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))
  let evalMap : WeakDual ℝ E₂ →ₗ[ℝ] ℝ :=
    { toFun := fun s ↦ WeakDual.toStrongDual s v
      map_add' := by
        intro s t
        simp [WeakDual.toStrongDual_apply, v]
      map_smul' := by
        intro a s
        simp [WeakDual.toStrongDual_apply, v] }
  have hB_convex : Convex ℝ B := by
    -- The weak-* closed ball is the linear preimage of the strong-dual closed ball.
    have hclosedBall_convex : Convex ℝ (closedBall (0 : StrongDual ℝ E₂) 1) := by
      simpa using (convex_closedBall (0 : StrongDual ℝ E₂) (1 : ℝ))
    simpa [B] using hclosedBall_convex.linear_preimage (WeakDual.toStrongDual.toLinearMap)
  have hcont : Continuous (fun s : WeakDual ℝ E₂ ↦ Φ s h) := by
    -- Continuity comes from weak-* continuity of evaluation at the fixed vector `v`.
    have heval : Continuous fun s : WeakDual ℝ E₂ ↦ WeakDual.toStrongDual s v := by
      simpa [WeakDual.toStrongDual_apply, v] using (WeakDual.eval_continuous (𝕜 := ℝ) (E := E₂) v)
    have hcont' : Continuous fun s : WeakDual ℝ E₂ ↦ -WeakDual.toStrongDual s v - c := by
      simpa using heval.neg.sub continuous_const
    simpa [Φ, v, c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcont'
  have hconvex : ConvexOn ℝ B (fun s : WeakDual ℝ E₂ ↦ Φ s h) := by
    -- The fixed-step slice is affine in `s`, hence convex on every convex set.
    have hlin : ConvexOn ℝ B (((-evalMap : WeakDual ℝ E₂ →ₗ[ℝ] ℝ) : WeakDual ℝ E₂ → ℝ)) := by
      simpa using ((-evalMap : WeakDual ℝ E₂ →ₗ[ℝ] ℝ)).convexOn hB_convex
    have hconvex' : ConvexOn ℝ B (fun s : WeakDual ℝ E₂ ↦ (-evalMap) s + -c) := by
      simpa using hlin.add_const (-c)
    simpa [Φ, evalMap, v, c, add_assoc, add_left_comm, add_comm] using hconvex'
  exact ⟨hcont.continuousOn.lowerSemicontinuousOn, hconvex.quasiconvexOn⟩

/-- Helper for Definition 4.4.18: for a fixed weak-* dual vector, the linear-plus-quadratic
primal slice is continuous and convex on the whole step space. -/
lemma weakDualPayoff_rightSliceConvexCore
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) (s : WeakDual ℝ E₂) :
    let ℓ : StrongDual ℝ E₁ := (WeakDual.toStrongDual s).comp (J x)
    let ψ : E₁ → ℝ := fun h ↦
      ℓ h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))
    Continuous ψ ∧ ConvexOn ℝ Set.univ ψ := by
  let ℓ : StrongDual ℝ E₁ := (WeakDual.toStrongDual s).comp (J x)
  let ψ : E₁ → ℝ := fun h ↦
    ℓ h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))
  have hM_nonneg : 0 ≤ (((M : ℝ) / 2 : ℝ)) := by
    positivity
  have hpow_cont : Continuous fun h : E₁ ↦ ‖h‖ ^ (2 : ℕ) := by
    simpa using (continuous_norm.pow (2 : ℕ))
  have hcont : Continuous ψ := by
    -- Add the continuous linear term and the continuous quadratic penalty.
    have hquad : Continuous fun h : E₁ ↦ (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) := by
      simpa using continuous_const.mul hpow_cont
    simpa [ψ] using ℓ.continuous.add hquad
  have hpow_convex : ConvexOn ℝ Set.univ (fun h : E₁ ↦ ‖h‖ ^ (2 : ℕ)) := by
    simpa using
      (ConvexOn.pow (n := (2 : ℕ)) (convexOn_norm convex_univ) (fun x _ ↦ norm_nonneg (x : E₁)))
  have hquad_convex :
      ConvexOn ℝ Set.univ (fun h : E₁ ↦ (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) := by
    simpa [smul_eq_mul] using hpow_convex.smul hM_nonneg
  have hlin_convex : ConvexOn ℝ Set.univ ℓ := by
    simpa [ℓ] using ℓ.toLinearMap.convexOn convex_univ
  exact ⟨hcont, by simpa [ψ] using hlin_convex.add hquad_convex⟩

/-- Helper for Definition 4.4.18: for a fixed weak-* dual vector, the primal payoff slice is
upper semicontinuous and quasiconcave on the whole step space. -/
lemma weakDualPayoff_rightSliceSionData
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) (s : WeakDual ℝ E₂) :
    let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s' h ↦
      -(WeakDual.toStrongDual s' (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
    UpperSemicontinuousOn (fun h : E₁ ↦ Φ s h) Set.univ ∧
      QuasiconcaveOn ℝ Set.univ (fun h : E₁ ↦ Φ s h) := by
  let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s' h ↦
    -(WeakDual.toStrongDual s' (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
  let c : ℝ := WeakDual.toStrongDual s (F x)
  let ψ : E₁ → ℝ := fun h ↦
    ((WeakDual.toStrongDual s).comp (J x)) h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))
  have hcore : Continuous ψ ∧ ConvexOn ℝ Set.univ ψ := by
    -- Isolate the nonconstant part into the convex-core helper.
    simpa [ψ] using weakDualPayoff_rightSliceConvexCore (J := J) (x := x) (M := M) (s := s)
  rcases hcore with ⟨hψ_cont, hψ_convex⟩
  have hcont : Continuous (fun h : E₁ ↦ Φ s h) := by
    -- The payoff is the negation of a constant shift of the convex core.
    have hcont' : Continuous fun h : E₁ ↦ -(c + ψ h) := by
      simpa using (continuous_const.add hψ_cont).neg
    simpa [Φ, ψ, c, ContinuousLinearMap.comp_apply, add_assoc, add_left_comm, add_comm] using hcont'
  have hconc : ConcaveOn ℝ Set.univ (fun h : E₁ ↦ Φ s h) := by
    -- Negating a convex function turns it into a concave payoff slice.
    have hconc' : ConcaveOn ℝ Set.univ (fun h : E₁ ↦ -(c + ψ h)) := by
      simpa using ((convexOn_const c convex_univ).add hψ_convex).neg
    simpa [Φ, ψ, c, ContinuousLinearMap.comp_apply, add_assoc, add_left_comm, add_comm] using hconc'
  exact ⟨hcont.continuousOn.upperSemicontinuousOn, hconc.quasiconcaveOn⟩


/-- Helper for Definition 4.4.18: the inf-sup weak-* payoff value is the negative of the supremum
of the weak-* dual objective image. -/
lemma iInf_iSup_weakDualPayoff_eq_neg_sSupDualFun
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) :
    let B : Set (WeakDual ℝ E₂) :=
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
    let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s h ↦
      -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
    let dualFun : WeakDual ℝ E₂ → ℝ := fun s ↦
      modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s)
    (⨅ s ∈ B, ⨆ h : E₁, Φ s h) = -sSup (dualFun '' B) := by
  let B : Set (WeakDual ℝ E₂) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
  let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s h ↦
    -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
  let dualFun : WeakDual ℝ E₂ → ℝ := fun s ↦
    modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s)
  let g : WeakDual ℝ E₂ → ℝ := fun s ↦ -dualFun s
  have hslice (s : WeakDual ℝ E₂) : (⨆ h : E₁, Φ s h) = g s := by
    -- Rewrite each fixed-dual slice using the quadratic conjugate computation above.
    simpa [B, Φ, dualFun, g] using
      weakDual_closedBall_iSup_neg_payoff_eq (F := F) (J := J) (M := M) (x := x) (s := s)
  have hB_nonempty : B.Nonempty := by
    refine ⟨0, ?_⟩
    simp [B]
  have hg_bdd : BddBelow (Set.range fun t : B ↦ g t) := by
    refine ⟨-‖F x‖, ?_⟩
    rintro _ ⟨t, rfl⟩
    have ht_mem :
        WeakDual.toStrongDual (t : WeakDual ℝ E₂) ∈ closedBall (0 : StrongDual ℝ E₂) 1 := by
      exact t.property
    have ht_norm : ‖WeakDual.toStrongDual (t : WeakDual ℝ E₂)‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using ht_mem
    have hquad_nonneg :
        0 ≤ (1 / (2 * (M : ℝ)) : ℝ) *
          ‖(WeakDual.toStrongDual (t : WeakDual ℝ E₂)).comp (J x)‖ ^ (2 : ℕ) := by
      positivity
    have hs_eval : WeakDual.toStrongDual (t : WeakDual ℝ E₂) (F x) ≤ ‖F x‖ := by
      have hop :
          ‖WeakDual.toStrongDual (t : WeakDual ℝ E₂) (F x)‖ ≤
            ‖WeakDual.toStrongDual (t : WeakDual ℝ E₂)‖ * ‖F x‖ := by
        simpa using (WeakDual.toStrongDual (t : WeakDual ℝ E₂)).le_opNorm (F x)
      calc
        WeakDual.toStrongDual (t : WeakDual ℝ E₂) (F x) ≤
            |WeakDual.toStrongDual (t : WeakDual ℝ E₂) (F x)| := by
          exact le_abs_self _
        _ = ‖WeakDual.toStrongDual (t : WeakDual ℝ E₂) (F x)‖ := by
          simp [Real.norm_eq_abs]
        _ ≤ ‖WeakDual.toStrongDual (t : WeakDual ℝ E₂)‖ * ‖F x‖ := hop
        _ ≤ 1 * ‖F x‖ := by
          exact mul_le_mul_of_nonneg_right ht_norm (norm_nonneg _)
        _ = ‖F x‖ := by
          ring
    have hdual_le : dualFun t ≤ ‖F x‖ := by
      calc
        dualFun t =
            WeakDual.toStrongDual (t : WeakDual ℝ E₂) (F x) -
              (1 / (2 * (M : ℝ)) : ℝ) *
                ‖(WeakDual.toStrongDual (t : WeakDual ℝ E₂)).comp (J x)‖ ^ (2 : ℕ) := by
          simp [dualFun, modifiedGaussNewtonNormDualObjective]
        _ ≤ WeakDual.toStrongDual (t : WeakDual ℝ E₂) (F x) := by
          linarith
        _ ≤ ‖F x‖ := hs_eval
    linarith
  have hg_inf : (⨅ t : B, g t) ≤ sInf (∅ : Set ℝ) := by
    have hzero : (0 : WeakDual ℝ E₂) ∈ B := by
      simp [B]
    have hzero_val : g 0 ≤ sInf (∅ : Set ℝ) := by
      rw [Real.sInf_empty]
      change -modifiedGaussNewtonNormDualObjective F J M x (0 : StrongDual ℝ E₂) ≤ 0
      simp [modifiedGaussNewtonNormDualObjective]
    exact (ciInf_le hg_bdd ⟨0, hzero⟩).trans (by simpa using hzero_val)
  have himage :
      g '' B = Neg.neg '' (dualFun '' B) := by
    -- Identify the negated dual-objective image with the set negation used by `Real.sInf_neg`.
    ext r
    constructor
    · rintro ⟨s, hsB, rfl⟩
      exact ⟨dualFun s, ⟨s, hsB, rfl⟩, by simp [g]⟩
    · rintro ⟨z, hz, hz_eq⟩
      rcases hz with ⟨s, hsB, rfl⟩
      exact ⟨s, hsB, by simpa [g] using hz_eq⟩
  calc
    (⨅ s ∈ B, ⨆ h : E₁, Φ s h) = ⨅ s ∈ B, g s := by
      simp [hslice]
    _ = sInf (g '' B) := by
      symm
      exact csInf_image hg_bdd hg_inf
    _ = sInf (Neg.neg '' (dualFun '' B)) := by
      rw [himage]
    _ = -sSup (dualFun '' B) := by
      rw [Set.image_neg_eq_neg]
      exact Real.sInf_neg (dualFun '' B)

/-- Helper for Definition 4.4.18: the sup-inf weak-* payoff value is the negative of the primal
step infimum. -/
lemma iSup_iInf_weakDualPayoff_eq_neg_sInfPrimal
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) :
    let B : Set (WeakDual ℝ E₂) :=
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
    let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s h ↦
      -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
    let primal : E₁ → ℝ := fun h ↦
      ‖F x + J x h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))
    (⨆ h : E₁, ⨅ s ∈ B, Φ s h) = -sInf (Set.range primal) := by
  let B : Set (WeakDual ℝ E₂) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
  let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s h ↦
    -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
  let primal : E₁ → ℝ := fun h ↦
    ‖F x + J x h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))
  have hslice (h : E₁) : (⨅ s ∈ B, Φ s h) = -primal h := by
    -- Rewrite each fixed-step slice by the weak-* GLB lemma proved above.
    simpa [B, Φ, primal] using
      weakDual_closedBall_iInf_neg_payoff_eq (u := F x) (A := J x) (M := M) (h := h)
  have hneg :
      Set.range (fun h : E₁ ↦ -primal h) = Neg.neg '' Set.range primal := by
    -- Identify the negated range with the set negation used by `Real.sSup_neg`.
    ext r
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨primal h, ⟨h, rfl⟩, by simp⟩
    · rintro ⟨z, hz, hz_eq⟩
      rcases hz with ⟨h, rfl⟩
      exact ⟨h, hz_eq⟩
  calc
    (⨆ h : E₁, ⨅ s ∈ B, Φ s h) = ⨆ h : E₁, -primal h := by
      simp [hslice]
    _ = sSup (Set.range fun h : E₁ ↦ -primal h) := by
      rfl
    _ = sSup (Neg.neg '' Set.range primal) := by
      rw [hneg]
    _ = -sInf (Set.range primal) := by
      rw [Set.image_neg_eq_neg]
      exact Real.sSup_neg (Set.range primal)

/-- Helper for Definition 4.4.18: each fixed weak-* dual slice has the exact `IsLUB` witness
required by the real-valued Sion minimax theorem. -/
lemma weakDualPayoffFixedDual_isLUB
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) (s : WeakDual ℝ E₂) :
    IsLUB
      (Set.range fun h : E₁ ↦
        -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))))
      (-modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s)) := by
  let ℓ : StrongDual ℝ E₁ := (WeakDual.toStrongDual s).comp (J x)
  let q : E₁ → ℝ := fun h ↦ -(ℓ h + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
  let c : ℝ := -(WeakDual.toStrongDual s (F x))
  have hdual :
      -modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s) =
        c + ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) := by
    simp [modifiedGaussNewtonNormDualObjective, c, ℓ, sub_eq_add_neg]
    ring
  have hq_lub :
      IsLUB (Set.range q) ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) := by
    -- The quadratic conjugate slice already computes the needed supremum.
    simpa [q, ℓ] using neg_linear_functional_add_quadratic_isLUB (ℓ := ℓ) (M := M)
  -- Compare the full slice directly with the conjugate core plus the constant shift `c`.
  refine ⟨?_, ?_⟩
  · rintro y ⟨h, rfl⟩
    have hyq : q h ≤ ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) := by
      exact hq_lub.1 ⟨h, rfl⟩
    have hslice :
        -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) =
          c + q h := by
      simp [q, c, ℓ, add_left_comm, add_comm, ContinuousLinearMap.comp_apply]
    change
      -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) ≤
        -modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s)
    rw [hslice, hdual]
    linarith
  · intro b hb
    have hbq : ∀ z ∈ Set.range q, z ≤ b - c := by
      rintro z ⟨h, rfl⟩
      have hslice :
          c + q h ≤ b := by
        have hslice_mem :
            -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) ≤ b := by
          exact hb ⟨h, rfl⟩
        change
          -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) ≤ b
            at hslice_mem
        have hslice_eq :
            -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) =
              c + q h := by
          simp [q, c, ℓ, add_left_comm, add_comm, ContinuousLinearMap.comp_apply]
        linarith
      linarith
    have htarget : ((1 / (2 * (M : ℝ)) : ℝ) * ‖ℓ‖ ^ (2 : ℕ)) ≤ b - c := by
      exact hq_lub.2 hbq
    have hgoal : -modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s) ≤ b := by
      rw [hdual]
      linarith
    exact hgoal

/-- Helper for Definition 4.4.18: each fixed primal step has the exact `IsGLB` witness required
by the real-valued Sion minimax theorem. -/
lemma weakDualPayoffFixedStep_isGLB
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) (h : E₁) :
    IsGLB
      {r : ℝ | ∃ s : WeakDual ℝ E₂,
          s ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1 ∧
          -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) = r}
      (-(‖F x + J x h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))) := by
  have himage :
      {r : ℝ | ∃ s : WeakDual ℝ E₂,
          s ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1 ∧
          -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) = r} =
        {r : ℝ | ∃ s : StrongDual ℝ E₂, s ∈ closedBall (0 : StrongDual ℝ E₂) 1 ∧
          -(s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) = r} := by
    -- Identify the weak-* slice image with the already-solved strong-dual slice image.
    ext r
    constructor
    · rintro ⟨s, hsB, hr⟩
      exact ⟨WeakDual.toStrongDual s, hsB, hr⟩
    · rintro ⟨s, hs_ball, hr⟩
      refine ⟨StrongDual.toWeakDual s, ?_, ?_⟩
      · change s ∈ closedBall (0 : StrongDual ℝ E₂) 1
        simpa using hs_ball
      · simpa using hr
  have hstrong :
      IsGLB
        {r : ℝ | ∃ s : StrongDual ℝ E₂, s ∈ closedBall (0 : StrongDual ℝ E₂) 1 ∧
            -(s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))) = r}
        (-(‖F x + J x h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))) := by
    -- Reuse the strong-dual GLB computation after the image identification.
    simpa [eq_comm] using
      neg_dual_pairing_add_quadratic_isGLB (u := F x) (A := J x) (M := M) (h := h)
  rw [himage]
  exact hstrong

/-- Helper for Definition 4.4.18: Sion's minimax theorem on the weak-* closed dual ball gives the
core equality between the inf-sup and sup-inf payoff values. -/
lemma weakDualClosedBall_minimax_eq
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) :
    let B : Set (WeakDual ℝ E₂) :=
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
    let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s h ↦
      -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
    (⨅ s ∈ B, ⨆ h : E₁, Φ s h) = ⨆ h : E₁, ⨅ s ∈ B, Φ s h := by
  -- Route correction: use the real-valued `Sion.minimax` theorem directly, packaging the fixed
  -- slices by explicit `IsLUB`/`IsGLB` witnesses instead of the unusable complete-order variant.
  let B : Set (WeakDual ℝ E₂) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
  let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s h ↦
    -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
  let primal : E₁ → ℝ := fun h ↦
    ‖F x + J x h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))
  let dualFun : WeakDual ℝ E₂ → ℝ := fun s ↦
    modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s)
  let g : WeakDual ℝ E₂ → ℝ := fun s ↦ -dualFun s
  let k : E₁ → ℝ := fun h ↦ -primal h
  have hB_nonempty : B.Nonempty := by
    -- The weak-* closed ball contains the zero functional.
    refine ⟨0, ?_⟩
    simp [B]
  have hB_compact : IsCompact B := by
    -- Banach-Alaoglu gives weak-* compactness of the closed ball.
    simpa [B] using WeakDual.isCompact_closedBall (𝕜 := ℝ) (E := E₂)
      (0 : StrongDual ℝ E₂) (1 : ℝ)
  have hB_convex : Convex ℝ B := by
    -- Convexity is inherited from the strong-dual closed ball by linear preimage.
    have hclosedBall_convex : Convex ℝ (closedBall (0 : StrongDual ℝ E₂) 1) := by
      simpa using (convex_closedBall (0 : StrongDual ℝ E₂) (1 : ℝ))
    simpa [B] using hclosedBall_convex.linear_preimage (WeakDual.toStrongDual.toLinearMap)
  have hg_bddBelow : BddBelow (g '' B) := by
    -- The dual objective is uniformly bounded above by `‖F x‖` on the closed ball.
    refine ⟨-‖F x‖, ?_⟩
    rintro _ ⟨s, hsB, rfl⟩
    have hdual_le : dualFun s ≤ ‖F x‖ := by
      simpa [dualFun] using weakDualDualObjective_le_norm_of_mem_closedBall
        (F := F) (J := J) (x := x) (M := M) (s := s) hsB
    linarith
  have hk_bddAbove : BddAbove (k '' (Set.univ : Set E₁)) := by
    -- The primal objective is nonnegative, so its negation is bounded above by `0`.
    refine ⟨0, ?_⟩
    rintro _ ⟨h, -, rfl⟩
    have hprimal_nonneg : 0 ≤ primal h := by
      positivity
    linarith
  have hginf :
      IsGLB {g s | s ∈ B} (-sSup (dualFun '' B)) := by
    have himage : g '' B = Neg.neg '' (dualFun '' B) := by
      -- Normalize the family of row suprema through set negation.
      ext r
      constructor
      · rintro ⟨s, hsB, rfl⟩
        exact ⟨dualFun s, ⟨s, hsB, rfl⟩, by simp [g]⟩
      · rintro ⟨z, hz, hz_eq⟩
        rcases hz with ⟨s, hsB, rfl⟩
        exact ⟨s, hsB, by simpa [g] using hz_eq⟩
    have hglb : IsGLB (g '' B) (sInf (g '' B)) :=
      Real.isGLB_sInf (hB_nonempty.image g) hg_bddBelow
    have hsInf : sInf (g '' B) = -sSup (dualFun '' B) := by
      rw [himage]
      rw [Set.image_neg_eq_neg]
      exact Real.sInf_neg (dualFun '' B)
    change IsGLB (g '' B) (-sSup (dualFun '' B))
    exact hsInf ▸ hglb
  have hksup :
      IsLUB {k h | h ∈ (Set.univ : Set E₁)} (-sInf (Set.range primal)) := by
    have hnonempty : (k '' (Set.univ : Set E₁)).Nonempty := by
      exact ⟨k 0, ⟨0, by simp⟩⟩
    have hneg :
        k '' (Set.univ : Set E₁) = Neg.neg '' Set.range primal := by
      -- Normalize the family of column infima through set negation.
      ext r
      constructor
      · rintro ⟨h, -, rfl⟩
        exact ⟨primal h, ⟨h, rfl⟩, by simp [k]⟩
      · rintro ⟨z, hz, hz_eq⟩
        rcases hz with ⟨h, rfl⟩
        exact ⟨h, Set.mem_univ h, by simpa [k] using hz_eq⟩
    have hlub : IsLUB (k '' (Set.univ : Set E₁)) (sSup (k '' (Set.univ : Set E₁))) :=
      Real.isLUB_sSup hnonempty hk_bddAbove
    have hsSup : sSup (k '' (Set.univ : Set E₁)) = -sInf (Set.range primal) := by
      rw [hneg]
      rw [Set.image_neg_eq_neg]
      exact Real.sSup_neg (Set.range primal)
    change IsLUB (k '' (Set.univ : Set E₁)) (-sInf (Set.range primal))
    exact hsSup ▸ hlub
  have hminimax :
      -sSup (dualFun '' B) = -sInf (Set.range primal) := by
    -- Feed the slice witnesses into Sion's real-valued minimax theorem.
    exact Sion.minimax
      (X := B) (Y := (Set.univ : Set E₁)) (f := Φ)
      (ne_X := hB_nonempty)
      (kX := hB_compact)
      (hfy := fun h _ ↦ by
        simpa [B, Φ] using
          (weakDualPayoff_leftSliceSionData
            (F := F) (J := J) (x := x) (M := M) (h := h)).1)
      (hfy' := fun h _ ↦ by
        simpa [B, Φ] using
          (weakDualPayoff_leftSliceSionData
            (F := F) (J := J) (x := x) (M := M) (h := h)).2)
      (cY := convex_univ)
      (hfx := fun s hsB ↦ by
        simpa [Φ] using
          (weakDualPayoff_rightSliceSionData
            (F := F) (J := J) (x := x) (M := M) (s := s)).1)
      (hfx' := fun s hsB ↦ by
        simpa [Φ] using
          (weakDualPayoff_rightSliceSionData
            (F := F) (J := J) (x := x) (M := M) (s := s)).2)
      (cX := hB_convex)
      (sup_y := g)
      (hsup_y := fun s hsB ↦ by
        simpa [g, dualFun, Φ] using
          weakDualPayoffFixedDual_isLUB
            (F := F) (J := J) (x := x) (M := M) (s := s))
      (inf_sup := -sSup (dualFun '' B))
      (hinf_sup := hginf)
      (inf_x := k)
      (hinf_x := fun h _ ↦ by
        simpa [k, B, Φ, primal] using
          weakDualPayoffFixedStep_isGLB
            (F := F) (J := J) (x := x) (M := M) (h := h))
      (sup_inf := -sInf (Set.range primal))
      (hsup_inf := hksup)
  -- Rewrite the abstract minimax equality back to the indexed inf-sup and sup-inf expressions.
  calc
    (⨅ s ∈ B, ⨆ h : E₁, Φ s h) = -sSup (dualFun '' B) := by
      simpa [B, Φ, dualFun] using
        iInf_iSup_weakDualPayoff_eq_neg_sSupDualFun (F := F) (J := J) (x := x) (M := M)
    _ = -sInf (Set.range primal) := hminimax
    _ = ⨆ h : E₁, ⨅ s ∈ B, Φ s h := by
      symm
      simpa [B, Φ, primal] using
        iSup_iInf_weakDualPayoff_eq_neg_sInfPrimal (F := F) (J := J) (x := x) (M := M)

/-- Helper for Definition 4.4.18: coercing the infimum of a nonempty bounded-below real range into
`EReal` agrees with taking the infimum after coercion. -/
lemma ereal_sInf_coe_range_eq_of_nonempty_bddBelow
    {α : Type*} (f : α → ℝ)
    (hnonempty : (Set.range f).Nonempty)
    (hbddBelow : BddBelow (Set.range f)) :
    sInf (Set.range fun a ↦ (f a : EReal)) = ((sInf (Set.range f) : ℝ) : EReal) := by
  -- Transport the real greatest-lower-bound description across `ℝ → EReal`.
  have hglb : IsGLB (Set.range f) (sInf (Set.range f)) :=
    Real.isGLB_sInf hnonempty hbddBelow
  have hglb' :
      IsGLB (Real.toEReal '' Set.range f) (((sInf (Set.range f) : ℝ) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact_mod_cast hglb.1 hy
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          rintro rfl
          rcases hnonempty with ⟨y, hy⟩
          have : (⊤ : EReal) ≤ (y : EReal) := hz ⟨y, hy, rfl⟩
          simp at this
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : ∀ y ∈ Set.range f, r ≤ y := by
          intro y hy
          exact_mod_cast (hz ⟨y, hy, rfl⟩)
        exact_mod_cast hglb.2 hr
  calc
    sInf (Set.range fun a ↦ (f a : EReal)) = sInf (Real.toEReal '' Set.range f) := by
      congr 1
      ext z
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨f a, ⟨a, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    _ = ((sInf (Set.range f) : ℝ) : EReal) := by
      exact hglb'.csInf_eq (by
        rcases hnonempty with ⟨y, hy⟩
        exact ⟨(y : EReal), ⟨y, hy, rfl⟩⟩)

/-- Helper for Definition 4.4.18: coercing the supremum of a nonempty bounded-above real image
into `EReal` agrees with taking the supremum after coercion. -/
lemma ereal_sSup_coe_real_image_eq_of_nonempty_bddAbove
    {A : Set ℝ} (hA_nonempty : A.Nonempty) (hA_bddAbove : BddAbove A) :
    sSup (((↑) : ℝ → EReal) '' A) = ((sSup A : ℝ) : EReal) := by
  -- Transport the real least-upper-bound description across `ℝ → EReal`.
  have hlub : IsLUB A (sSup A) :=
    Real.isLUB_sSup hA_nonempty hA_bddAbove
  have hlub' : IsLUB (((↑) : ℝ → EReal) '' A) (((sSup A : ℝ) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact_mod_cast hlub.1 hy
    · intro z hz
      by_cases hz_top : z = ⊤
      · simp [hz_top]
      · have hz_bot : z ≠ ⊥ := by
          rintro rfl
          rcases hA_nonempty with ⟨y, hy⟩
          have : (y : EReal) ≤ (⊥ : EReal) := hz ⟨y, hy, rfl⟩
          simp at this
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : ∀ y ∈ A, y ≤ r := by
          intro y hy
          exact_mod_cast (hz ⟨y, hy, rfl⟩)
        exact_mod_cast hlub.2 hr
  exact hlub'.csSup_eq (hA_nonempty.image fun y : ℝ ↦ (y : EReal))

/-- Definition 4.4.18: for positive `M`, the canonical norm-specialized auxiliary value equals
the supremum of the intrinsic strong-dual objective over the closed unit ball of the residual
strong dual. -/
theorem modifiedGaussNewtonOptimalValueAt_norm_eq_sSup_dualObjective
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) :
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x (M : ℝ) =
      sSup ((((↑) : ℝ → EReal) ∘ modifiedGaussNewtonNormDualObjective F J M x) ''
          closedBall (0 : StrongDual ℝ E₂) 1) := by
  -- Route correction: first establish the real primal/dual equality from the explicit minimax
  -- bridge, and only then lift both sides across `ℝ → EReal`.
  let B : Set (WeakDual ℝ E₂) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E₂) 1
  let Φ : WeakDual ℝ E₂ → E₁ → ℝ := fun s h ↦
    -(WeakDual.toStrongDual s (F x + J x h) + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)))
  let primal : E₁ → ℝ := fun h ↦
    ‖F x + J x h‖ + (((M : ℝ) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ))
  let dualFun : WeakDual ℝ E₂ → ℝ := fun s ↦
    modifiedGaussNewtonNormDualObjective F J M x (WeakDual.toStrongDual s)
  have hprimal_nonempty : (Set.range primal).Nonempty := by
    exact ⟨primal 0, ⟨0, rfl⟩⟩
  have hprimal_bddBelow : BddBelow (Set.range primal) := by
    -- The primal objective is nonnegative.
    refine ⟨0, ?_⟩
    rintro _ ⟨h, rfl⟩
    positivity
  have hB_nonempty : B.Nonempty := by
    refine ⟨0, ?_⟩
    simp [B]
  have hdual_nonempty : (dualFun '' B).Nonempty := by
    exact hB_nonempty.image dualFun
  have hdual_bddAbove : BddAbove (dualFun '' B) := by
    -- The weak-* dual image inherits the uniform bound `dualFun s ≤ ‖F x‖`.
    refine ⟨‖F x‖, ?_⟩
    rintro _ ⟨s, hsB, rfl⟩
    simpa [dualFun] using
      weakDualDualObjective_le_norm_of_mem_closedBall
        (F := F) (J := J) (x := x) (M := M) (s := s) hsB
  have hreal :
      sInf (Set.range primal) = sSup (dualFun '' B) := by
    have hneg :
        -sSup (dualFun '' B) = -sInf (Set.range primal) := by
      calc
        -sSup (dualFun '' B) = (⨅ s ∈ B, ⨆ h : E₁, Φ s h) := by
          symm
          simpa [B, Φ, dualFun] using
            iInf_iSup_weakDualPayoff_eq_neg_sSupDualFun
              (F := F) (J := J) (x := x) (M := M)
        _ = (⨆ h : E₁, ⨅ s ∈ B, Φ s h) := by
          simpa [B, Φ] using
            weakDualClosedBall_minimax_eq (F := F) (J := J) (x := x) (M := M)
        _ = -sInf (Set.range primal) := by
          simpa [B, Φ, primal] using
            iSup_iInf_weakDualPayoff_eq_neg_sInfPrimal
              (F := F) (J := J) (x := x) (M := M)
    linarith
  have hdual_image :
      dualFun '' B =
        modifiedGaussNewtonNormDualObjective F J M x '' closedBall (0 : StrongDual ℝ E₂) 1 := by
    -- Move from the weak-* closed-ball image to the strong-dual image used in the theorem.
    simpa [B, dualFun] using
      weakDual_dualObjective_image_eq_strongDual_image (F := F) (J := J) (M := M) (x := x)
  -- Now transport the real primal/dual equality through the existing coercion lemmas.
  calc
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x (M : ℝ) =
        ((sInf (Set.range primal) : ℝ) : EReal) := by
      rw [modifiedGaussNewtonOptimalValueAt_norm_eq_sInf_range]
      simpa [primal] using
        ereal_sInf_coe_range_eq_of_nonempty_bddBelow
          (f := primal) hprimal_nonempty hprimal_bddBelow
    _ = ((sSup (dualFun '' B) : ℝ) : EReal) := by
      exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
    _ = sSup (((↑) : ℝ → EReal) '' (dualFun '' B)) := by
      symm
      exact ereal_sSup_coe_real_image_eq_of_nonempty_bddAbove hdual_nonempty hdual_bddAbove
    _ = sSup (((↑) : ℝ → EReal) ''
        (modifiedGaussNewtonNormDualObjective F J M x '' closedBall (0 : StrongDual ℝ E₂) 1)) := by
      rw [hdual_image]
    _ = sSup ((((↑) : ℝ → EReal) ∘ modifiedGaussNewtonNormDualObjective F J M x) ''
        closedBall (0 : StrongDual ℝ E₂) 1) := by
      congr 1
      ext z
      constructor
      · rintro ⟨r, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨modifiedGaussNewtonNormDualObjective F J M x y, ⟨y, hy, rfl⟩, rfl⟩

end DualObjective

section DualBridge

variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- Under the Riesz identification, the intrinsic strong-dual objective specializes to the
textbook Hilbert-space formula with the adjoint of `J x`. -/
@[simp] theorem modifiedGaussNewtonNormDualObjective_toDual
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) (s : E₂) :
    modifiedGaussNewtonNormDualObjective F J M x (InnerProductSpace.toDual ℝ E₂ s) =
      inner ℝ s (F x) -
        (1 / (2 * (M : ℝ)) : ℝ) * ‖(J x).adjoint s‖ ^ (2 : ℕ) := by
  simp [modifiedGaussNewtonNormDualObjective,
    show (InnerProductSpace.toDual ℝ E₂ s).comp (J x) =
        InnerProductSpace.toDual ℝ E₁ ((J x).adjoint s) by
    ext y
    simp [ContinuousLinearMap.adjoint_inner_left]]

end DualBridge

end
