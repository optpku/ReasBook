/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Module.Equiv

open Set

section Theorem125

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Source/core/bridge triage:
-- * source-facing: the local two-sided norm bounds near `x`
-- * core/canonical: the invertibility predicate `(fderiv ℝ F x).IsInvertible`
-- * bridge/view: an explicit `ContinuousLinearEquiv` identifying `fderiv ℝ F x`
--
-- Semantic recall: local Chapter 1 precedent used a `ContinuousLinearEquiv` witness for
-- `[F′(x)]⁻¹` existing, while later chapters use the canonical
-- `ContinuousLinearMap.IsInvertible` owner. This file keeps the Chapter 1 bridge theorem and
-- adds the canonical invertibility surface for reuse elsewhere in the repository.

/-- Local bi-Lipschitz bounds near `x` on `D` with constants `ε`, `α`, and `β`. -/
structure NormImageSubBoundsNear
    (D : Set E)
    (F : E → E)
    (x : E)
    (ε α β : ℝ) : Prop where
  eps_pos : 0 < ε
  alpha_pos : 0 < α
  alpha_lt_beta : α < β
  lower :
    ∀ ⦃u v : E⦄,
      u ∈ D →
      v ∈ D →
      max ‖u - x‖ ‖v - x‖ ≤ ε →
      α * ‖u - v‖ ≤ ‖F u - F v‖
  upper :
    ∀ ⦃u v : E⦄,
      u ∈ D →
      v ∈ D →
      max ‖u - x‖ ‖v - x‖ ≤ ε →
      ‖F u - F v‖ ≤ β * ‖u - v‖

/-- Helper for Chapter01 Theorem 1.2.25: on a subsingleton space, the two-sided norm estimate is
vacuous because every pair of points coincides. -/
lemma existsBoundsNear_of_subsingleton
    (D : Set E)
    (F : E → E)
    (x : E)
    (hsub : Subsingleton E) :
    ∃ ε α β : ℝ, NormImageSubBoundsNear D F x ε α β := by
  -- In a subsingleton space, every difference vanishes, so any positive constants work.
  refine ⟨1, 1, 2, ?_⟩
  refine ⟨zero_lt_one, zero_lt_one, by norm_num, ?_, ?_⟩
  · intro u v hu hv huv
    have huv' : u = v := hsub.elim u v
    subst huv'
    simp
  · intro u v hu hv huv
    have huv' : u = v := hsub.elim u v
    subst huv'
    simp

/-- Helper for Chapter01 Theorem 1.2.25: the operator norm of `A.symm` gives a lower bound for the
norm of `A z`. -/
lemma invOpNorm_mul_norm_le_norm_apply
    (A : E ≃L[ℝ] E)
    (z : E) :
    (1 / ‖(A.symm : E →L[ℝ] E)‖) * ‖z‖ ≤ ‖A z‖ := by
  -- Rewrite `z` through `A.symm (A z)` and then divide the operator-norm estimate by
  -- `‖A.symm‖`.
  rcases A.subsingleton_or_norm_symm_pos with hsub | hsymm_pos
  · have hz : z = 0 := hsub.elim z 0
    simp [hz]
  · have hbound : ‖z‖ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖A z‖ := by
      calc
        ‖z‖ = ‖(A.symm : E →L[ℝ] E) (A z)‖ := by
          simpa using congrArg norm (A.symm_apply_apply z)
        _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖A z‖ := (A.symm : E →L[ℝ] E).le_opNorm (A z)
    have hdiv : ‖z‖ / ‖(A.symm : E →L[ℝ] E)‖ ≤ ‖A z‖ := by
      exact (div_le_iff₀ hsymm_pos).2 (by simpa [mul_comm] using hbound)
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- Helper for Chapter01 Theorem 1.2.25: Theorem 1.2.24 supplies the exact linearization-error
bound at the base point `x`. -/
lemma linearizationErrorBoundAtBasePoint
    (D : Set E)
    (F : E → E)
    (x : E)
    (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hcont : ContDiffOn ℝ 1 F D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    {u v : E}
    (hu : u ∈ D)
    (hv : v ∈ D)
    (hx : x ∈ D) :
    ‖F u - F v - (fderiv ℝ F x) (u - v)‖ ≤
      (γ : ℝ) * max ‖u - x‖ ‖v - x‖ * ‖u - v‖ := by
  -- The `C¹` hypothesis yields differentiability on `D`, which is exactly the input needed by
  -- the segment by the maximal endpoint distance from `x`.
  have hDiff :
      ∀ z ∈ segment ℝ v u, DifferentiableAt ℝ F z := by
    intro z hz
    have hzD : z ∈ D := hD_convex.segment_subset hv hu hz
    exact (hcont.differentiableOn_one z hzD).differentiableAt (hD_open.mem_nhds hzD)
  have hbound :
      ∀ z ∈ segment ℝ v u,
        ‖fderiv ℝ F z - fderiv ℝ F x‖ ≤
          (γ : ℝ) * max ‖u - x‖ ‖v - x‖ := by
    intro z hz
    have hzD : z ∈ D := hD_convex.segment_subset hv hu hz
    have huBall : u ∈ Metric.closedBall x (max ‖u - x‖ ‖v - x‖) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using le_max_left ‖u - x‖ ‖v - x‖
    have hvBall : v ∈ Metric.closedBall x (max ‖u - x‖ ‖v - x‖) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using le_max_right ‖u - x‖ ‖v - x‖
    have hzBall : z ∈ Metric.closedBall x (max ‖u - x‖ ‖v - x‖) := by
      exact (convex_closedBall x (max ‖u - x‖ ‖v - x‖)).segment_subset hvBall huBall hz
    have hz_norm : ‖z - x‖ ≤ max ‖u - x‖ ‖v - x‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzBall
    have hderiv :
        ‖fderiv ℝ F z - fderiv ℝ F x‖ ≤ (γ : ℝ) * ‖z - x‖ := by
      simpa [dist_eq_norm] using hLip.dist_le_mul z hzD x hx
    exact hderiv.trans (mul_le_mul_of_nonneg_left hz_norm (NNReal.coe_nonneg γ))
  have hvSeg : v ∈ segment ℝ v u := by
    simpa using left_mem_segment ℝ v u
  have huSeg : u ∈ segment ℝ v u := by
    simpa using right_mem_segment ℝ v u
  exact Convex.norm_image_sub_le_of_norm_fderiv_le'
    hDiff hbound (convex_segment (𝕜 := ℝ) v u) hvSeg huSeg

/-- Helper for Chapter01 Theorem 1.2.25: the explicit choices of `ε`, `α`, and `β` satisfy the
positivity and comparison inequalities needed in the final norm estimate. -/
lemma chosenBiLipschitzConstants
    (γ : NNReal)
    {μ c : ℝ}
    (hμ_pos : 0 < μ)
    (hc_nonneg : 0 ≤ c) :
    let ε : ℝ := 1 / (2 * μ * ((γ : ℝ) + 1))
    let α : ℝ := 1 / (2 * μ)
    let β : ℝ := α + c + (γ : ℝ) * ε + 1
    0 < ε ∧ 0 < α ∧ α < β ∧ (γ : ℝ) * ε ≤ α := by
  -- The chosen radius makes the remainder coefficient at most `α`, and `β` has extra slack by
  -- construction.
  dsimp
  have hγ_nonneg : 0 ≤ (γ : ℝ) := NNReal.coe_nonneg γ
  have hγ_add_one_pos : 0 < (γ : ℝ) + 1 := by linarith
  have htwo_mul_pos : 0 < 2 * μ := by nlinarith
  have hdenom_pos : 0 < 2 * μ * ((γ : ℝ) + 1) := by nlinarith
  have hε_pos : 0 < 1 / (2 * μ * ((γ : ℝ) + 1)) := one_div_pos.mpr hdenom_pos
  have hα_pos : 0 < 1 / (2 * μ) := one_div_pos.mpr htwo_mul_pos
  have hγ_eps_le :
      (γ : ℝ) * (1 / (2 * μ * ((γ : ℝ) + 1))) ≤ 1 / (2 * μ) := by
    have hgamma_le : (γ : ℝ) ≤ (γ : ℝ) + 1 := by linarith
    have hscale_nonneg : 0 ≤ 1 / (2 * μ) := le_of_lt hα_pos
    calc
      (γ : ℝ) * (1 / (2 * μ * ((γ : ℝ) + 1)))
          = (1 / (2 * μ)) * ((γ : ℝ) / ((γ : ℝ) + 1)) := by
              field_simp [hμ_pos.ne', hγ_add_one_pos.ne']
      _ ≤ (1 / (2 * μ)) * 1 := by
            have hdiv_le_one : (γ : ℝ) / ((γ : ℝ) + 1) ≤ 1 := by
              apply (div_le_iff₀ hγ_add_one_pos).2
              nlinarith
            gcongr
      _ = 1 / (2 * μ) := by ring
  have hβ_gap_pos :
      0 < c + (γ : ℝ) * (1 / (2 * μ * ((γ : ℝ) + 1))) + 1 := by
    nlinarith
  constructor
  · exact hε_pos
  constructor
  · exact hα_pos
  constructor
  · nlinarith
  · exact hγ_eps_le

/-- Chapter01 Theorem 1.2.25: if `F : E → E` is `C¹` on the open convex
set `D`, `fderiv ℝ F` is Lipschitz on `D`, and `fderiv ℝ F x` is invertible,
then `F` is locally bi-Lipschitz near `x` on `D`. -/
theorem norm_image_sub_bounds_near_of_fderiv_isInvertible
    (D : Set E)
    (F : E → E)
    (x : E)
    (γ : NNReal)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hcont : ContDiffOn ℝ 1 F D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    (hInv : (fderiv ℝ F x).IsInvertible) :
    ∃ ε α β : ℝ, NormImageSubBoundsNear D F x ε α β := by
  by_cases hsub : Subsingleton E
  · -- On a subsingleton space, the conclusion is immediate because every pair `u, v` is equal.
    exact existsBoundsNear_of_subsingleton D F x hsub
  · -- Route correction: prove the nontrivial branch by combining Theorem 1.2.24 with the
    -- inverse-operator lower bound for the derivative at `x`.
    rcases hInv with ⟨A, hA⟩
    let μ : ℝ := ‖(A.symm : E →L[ℝ] E)‖
    let ε : ℝ := 1 / (2 * μ * ((γ : ℝ) + 1))
    let α : ℝ := 1 / (2 * μ)
    let β : ℝ := α + ‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ε + 1
    have hA' : fderiv ℝ F x = (A : E →L[ℝ] E) := hA.symm
    have hμ_pos : 0 < μ := by
      -- The derivative equivalence has nonzero inverse norm in the nontrivial branch.
      dsimp [μ]
      rcases A.subsingleton_or_norm_symm_pos with hsub' | hμ_pos
      · exact False.elim (hsub hsub')
      · exact hμ_pos
    have hconstants :
        0 < ε ∧ 0 < α ∧ α < β ∧ (γ : ℝ) * ε ≤ α := by
      -- Package the scalar inequalities once so the main estimate only handles norms.
      simpa [μ, ε, α, β] using
        chosenBiLipschitzConstants (γ := γ) (μ := μ) (c := ‖(A : E →L[ℝ] E)‖)
          hμ_pos (norm_nonneg _)
    rcases hconstants with ⟨hε_pos, hα_pos, hα_lt_beta, hγε_le_α⟩
    refine ⟨ε, α, β, ?_⟩
    refine ⟨hε_pos, hα_pos, hα_lt_beta, ?_, ?_⟩
    · intro u v hu hv huv
      -- First bound the Taylor remainder at `x`, then absorb it into the inverse-derivative
      -- lower estimate.
      have herr :
          ‖F u - F v - (A : E →L[ℝ] E) (u - v)‖ ≤
            (γ : ℝ) * max ‖u - x‖ ‖v - x‖ * ‖u - v‖ := by
        simpa [hA'] using
          linearizationErrorBoundAtBasePoint D F x γ hD_open hD_convex hcont hLip hu hv hx
      have hγε :
          (γ : ℝ) * max ‖u - x‖ ‖v - x‖ ≤ (γ : ℝ) * ε := by
        exact mul_le_mul_of_nonneg_left huv (NNReal.coe_nonneg γ)
      have herr' :
          ‖F u - F v - (A : E →L[ℝ] E) (u - v)‖ ≤
            ((γ : ℝ) * ε) * ‖u - v‖ := by
        exact herr.trans (mul_le_mul_of_nonneg_right hγε (norm_nonneg (u - v)))
      have hlinear_le :
          ‖(A : E →L[ℝ] E) (u - v)‖ ≤ ‖F u - F v‖ + ((γ : ℝ) * ε) * ‖u - v‖ := by
        -- Rewrite the linear part as the image difference minus the remainder, then use the
        -- triangle inequality.
        calc
          ‖(A : E →L[ℝ] E) (u - v)‖ =
              ‖F u - F v - (F u - F v - (A : E →L[ℝ] E) (u - v))‖ := by
                simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ ≤ ‖F u - F v‖ + ‖F u - F v - (A : E →L[ℝ] E) (u - v)‖ := norm_sub_le _ _
          _ ≤ ‖F u - F v‖ + ((γ : ℝ) * ε) * ‖u - v‖ := by
            gcongr
      have hmain :
          (1 / μ) * ‖u - v‖ ≤ ‖F u - F v‖ + α * ‖u - v‖ := by
        calc
          (1 / μ) * ‖u - v‖ ≤ ‖(A : E →L[ℝ] E) (u - v)‖ := by
            simpa [μ] using invOpNorm_mul_norm_le_norm_apply A (u - v)
          _ ≤ ‖F u - F v‖ + ((γ : ℝ) * ε) * ‖u - v‖ := hlinear_le
          _ ≤ ‖F u - F v‖ + α * ‖u - v‖ := by
            gcongr
      -- The special choice `α = 1 / (2 * μ)` leaves exactly half of the inverse bound on the
      -- right-hand side.
      have hhalf :
          α * ‖u - v‖ = ((1 / μ) * ‖u - v‖) / 2 := by
        dsimp [α]
        field_simp [hμ_pos.ne']
      rw [hhalf] at hmain
      nlinarith [hmain, norm_nonneg (F u - F v)]
    · intro u v hu hv huv
      -- The same remainder estimate plus the operator norm bound gives the upper Lipschitz
      -- constant.
      have herr :
          ‖F u - F v - (A : E →L[ℝ] E) (u - v)‖ ≤
            (γ : ℝ) * max ‖u - x‖ ‖v - x‖ * ‖u - v‖ := by
        simpa [hA'] using
          linearizationErrorBoundAtBasePoint D F x γ hD_open hD_convex hcont hLip hu hv hx
      have hγε :
          (γ : ℝ) * max ‖u - x‖ ‖v - x‖ ≤ (γ : ℝ) * ε := by
        exact mul_le_mul_of_nonneg_left huv (NNReal.coe_nonneg γ)
      have herr' :
          ‖F u - F v - (A : E →L[ℝ] E) (u - v)‖ ≤
            ((γ : ℝ) * ε) * ‖u - v‖ := by
        exact herr.trans (mul_le_mul_of_nonneg_right hγε (norm_nonneg (u - v)))
      have hupper_core :
          ‖F u - F v‖ ≤ ‖(A : E →L[ℝ] E) (u - v)‖ + ((γ : ℝ) * ε) * ‖u - v‖ := by
        -- Split the image difference into its linearized part and the first-order remainder.
        calc
          ‖F u - F v‖ =
              ‖(F u - F v - (A : E →L[ℝ] E) (u - v)) + (A : E →L[ℝ] E) (u - v)‖ := by
                simp [sub_eq_add_neg, add_assoc, add_left_comm]
          _ ≤ ‖F u - F v - (A : E →L[ℝ] E) (u - v)‖ + ‖(A : E →L[ℝ] E) (u - v)‖ :=
                norm_add_le _ _
          _ ≤ ((γ : ℝ) * ε) * ‖u - v‖ + ‖(A : E →L[ℝ] E) (u - v)‖ := by
            gcongr
          _ = ‖(A : E →L[ℝ] E) (u - v)‖ + ((γ : ℝ) * ε) * ‖u - v‖ := by ring
      calc
        ‖F u - F v‖ ≤ ‖(A : E →L[ℝ] E) (u - v)‖ + ((γ : ℝ) * ε) * ‖u - v‖ := hupper_core
        _ ≤ ‖(A : E →L[ℝ] E)‖ * ‖u - v‖ + ((γ : ℝ) * ε) * ‖u - v‖ := by
          gcongr
          exact (A : E →L[ℝ] E).le_opNorm (u - v)
        _ = (‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ε) * ‖u - v‖ := by ring
        _ ≤ β * ‖u - v‖ := by
          apply mul_le_mul_of_nonneg_right
          · dsimp [β]
            nlinarith [hα_pos]
          · exact norm_nonneg (u - v)

/-- Chapter01 Theorem 1.2.25: if `F : E → E` is `C¹` on the open convex
set `D`, `fderiv ℝ F` is Lipschitz on `D`, and `fderiv ℝ F x` is represented by
the continuous linear equivalence `A`, then `F` is locally bi-Lipschitz near
`x` on `D`. This is the source-facing Chapter 1 bridge form of the canonical
invertibility statement `norm_image_sub_bounds_near_of_fderiv_isInvertible`. -/
theorem norm_image_sub_bounds_near_of_fderiv_equiv
    (D : Set E)
    (F : E → E)
    (x : E)
    (γ : NNReal)
    (A : E ≃L[ℝ] E)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hcont : ContDiffOn ℝ 1 F D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    (hA : fderiv ℝ F x = (A : E →L[ℝ] E)) :
    ∃ ε α β : ℝ, NormImageSubBoundsNear D F x ε α β := by
  have hInv : (fderiv ℝ F x).IsInvertible := by
    rw [hA]
    exact ContinuousLinearMap.isInvertible_equiv
  exact norm_image_sub_bounds_near_of_fderiv_isInvertible D F x γ
    hD_open hD_convex hx hcont hLip hInv

end Theorem125
