/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem firmlyNonexpansiveOn_univ_iff {T : H → H} :
    FirmlyNonexpansiveOn (Set.univ : Set H) T ↔
      ∀ x y : H, ‖T x - T y‖ ^ (2 : ℕ) ≤ ⟪T x - T y, x - y⟫_ℝ := by
  rw [firmlyNonexpansiveOn_iff]
  constructor
  · intro h x y
    have hxy :
        ‖T x - T y‖ ^ (2 : ℕ) + ‖(x - T x) - (y - T y)‖ ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
      simpa using h x (by simp) y (by simp)
    have hres : (x - T x) - (y - T y) = (x - y) - (T x - T y) := by
      abel_nf
    rw [hres] at hxy
    have hnorm :
        ‖(x - y) - (T x - T y)‖ ^ (2 : ℕ) =
          ‖x - y‖ ^ (2 : ℕ) - 2 * ⟪x - y, T x - T y⟫_ℝ + ‖T x - T y‖ ^ (2 : ℕ) := by
      simpa [real_inner_comm] using norm_sub_sq_real (x - y) (T x - T y)
    rw [hnorm] at hxy
    have hxy' : ‖T x - T y‖ ^ (2 : ℕ) ≤ ⟪x - y, T x - T y⟫_ℝ := by
      nlinarith
    simpa [real_inner_comm] using hxy'
  · intro h x hx y hy
    have hxy : ‖T x - T y‖ ^ (2 : ℕ) ≤ ⟪T x - T y, x - y⟫_ℝ := h x y
    have hres : (x - T x) - (y - T y) = (x - y) - (T x - T y) := by
      abel_nf
    have hnorm :
        ‖(x - T x) - (y - T y)‖ ^ (2 : ℕ) =
          ‖x - y‖ ^ (2 : ℕ) - 2 * ⟪x - y, T x - T y⟫_ℝ + ‖T x - T y‖ ^ (2 : ℕ) := by
      rw [hres]
      simpa [real_inner_comm] using norm_sub_sq_real (x - y) (T x - T y)
    have hxy' : ‖T x - T y‖ ^ (2 : ℕ) ≤ ⟪x - y, T x - T y⟫_ℝ := by
      simpa [real_inner_comm] using hxy
    rw [hnorm]
    nlinarith [hxy']

private theorem firmlyNonexpansiveOn_univ_iff_reflectedMap_nonexpansive {T : H → H} :
    FirmlyNonexpansiveOn (Set.univ : Set H) T ↔
      ∀ x y : H, ‖((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y)‖ ≤ ‖x - y‖ := by
  rw [firmlyNonexpansiveOn_univ_iff]
  constructor
  · intro hT x y
    have hsq :
        ‖((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y)‖ ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
      have hnorm :
          ‖((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y)‖ ^ (2 : ℕ) =
            4 * ‖T x - T y‖ ^ (2 : ℕ) - 4 * ⟪T x - T y, x - y⟫_ℝ + ‖x - y‖ ^ (2 : ℕ) := by
        have hrewrite :
            ((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y) =
              (2 : ℝ) • (T x - T y) - (x - y) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        rw [hrewrite, norm_sub_sq_real]
        rw [show ‖(2 : ℝ) • (T x - T y)‖ ^ (2 : ℕ) = 4 * ‖T x - T y‖ ^ (2 : ℕ) by
          rw [norm_smul]
          norm_num
          ring]
        rw [show ⟪(2 : ℝ) • (T x - T y), x - y⟫_ℝ = 2 * ⟪T x - T y, x - y⟫_ℝ by
          rw [real_inner_smul_left]]
        ring
      rw [hnorm]
      nlinarith [hT x y]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  · intro hR x y
    have hsq :
        ‖((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y)‖ ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hR x y)
    have hnorm :
        ‖((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y)‖ ^ (2 : ℕ) =
          4 * ‖T x - T y‖ ^ (2 : ℕ) - 4 * ⟪T x - T y, x - y⟫_ℝ + ‖x - y‖ ^ (2 : ℕ) := by
      have hrewrite :
          ((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y) =
            (2 : ℝ) • (T x - T y) - (x - y) := by
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hrewrite, norm_sub_sq_real]
      rw [show ‖(2 : ℝ) • (T x - T y)‖ ^ (2 : ℕ) = 4 * ‖T x - T y‖ ^ (2 : ℕ) by
        rw [norm_smul]
        norm_num
        ring]
      rw [show ⟪(2 : ℝ) • (T x - T y), x - y⟫_ℝ = 2 * ⟪T x - T y, x - y⟫_ℝ by
        rw [real_inner_smul_left]]
      ring
    rw [hnorm] at hsq
    nlinarith

private theorem firmlyNonexpansiveOn_univ_iff_lipschitzWith_one_reflectedMap {T : H → H} :
    FirmlyNonexpansiveOn (Set.univ : Set H) T ↔
      LipschitzWith 1 (fun x ↦ (2 : ℝ) • T x - x) := by
  constructor
  · intro hT
    have hR :=
      firmlyNonexpansiveOn_univ_iff_reflectedMap_nonexpansive.1 hT
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [dist_eq_norm, one_mul] using hR x y
  · intro hR
    refine firmlyNonexpansiveOn_univ_iff_reflectedMap_nonexpansive.2 ?_
    intro x y
    simpa [dist_eq_norm, one_mul] using hR.dist_le_mul x y

/-- The soft thresholder at level `ρ`, as in formula (4.16). -/
noncomputable def softThresholder (ρ : ℝ) : H → H :=
  fun x ↦ if ρ < ‖x‖ then (1 - ρ / ‖x‖) • x else 0

/-- The soft thresholder acts by radial shrinkage outside the radius-`ρ` ball and vanishes
inside. -/
-- Proof sketch: unfold `softThresholder`.
theorem softThresholder_apply (ρ : ℝ) (x : H) :
    softThresholder ρ x = if ρ < ‖x‖ then (1 - ρ / ‖x‖) • x else 0 := by
  -- The definition is already in the required form.
  rfl

/-- The hard thresholder at level `ρ` and relaxation parameter `α`, as in formula (4.17). -/
noncomputable def hardThresholder (ρ α : ℝ) : H → H :=
  fun x ↦ if ρ < ‖x‖ then α • x else 0

/-- The hard thresholder scales vectors outside the radius-`ρ` ball and vanishes inside. -/
-- Proof sketch: unfold `hardThresholder`.
theorem hardThresholder_apply (ρ α : ℝ) (x : H) :
    hardThresholder ρ α x = if ρ < ‖x‖ then α • x else 0 := by
  -- The definition is already in the required form.
  rfl

/-- The operator `T₃` from formula (4.18). -/
noncomputable def reflectedSoftThresholder (ρ : ℝ) : H → H :=
  fun x ↦ if ρ < ‖x‖ then (1 - 2 * ρ / ‖x‖) • x else -x

/-- The operator `T₃` reflects vectors in the closed ball and applies the outer radial formula
outside it. -/
-- Proof sketch: unfold `reflectedSoftThresholder`.
theorem reflectedSoftThresholder_apply (ρ : ℝ) (x : H) :
    reflectedSoftThresholder ρ x =
      if ρ < ‖x‖ then (1 - 2 * ρ / ‖x‖) • x else -x := by
  -- The definition is already in the required form.
  rfl

private theorem closedBall_zero_nonempty {E : Type u} [NormedAddCommGroup E] (ρ : ℝ) (hρ : 0 < ρ) :
    (Metric.closedBall (0 : E) ρ : Set E).Nonempty := by
  -- The origin itself lies in the ball because its norm is `0`.
  refine ⟨0, ?_⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.le

section

variable [CompleteSpace H]

private theorem projectionPoint_closedBall_zero_eq_radial_clip (ρ : ℝ) (hρ : 0 < ρ) (x : H) :
    projectionPoint (Metric.closedBall (0 : H) ρ)
        (isChebyshev_of_nonempty_isClosed_convex
          (closedBall_zero_nonempty ρ hρ)
          (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) ρ))
          (convex_closedBall (0 : H) ρ)) x =
      if ρ < ‖x‖ then (ρ / ‖x‖) • x else x := by
  let C : Set H := Metric.closedBall (0 : H) ρ
  have hC_nonempty : C.Nonempty := closedBall_zero_nonempty ρ hρ
  have hC_closed : IsClosed C := Metric.isClosed_closedBall
  have hC_convex : Convex ℝ C := convex_closedBall (0 : H) ρ
  by_cases hx : ρ < ‖x‖
  · have hnormx_pos : 0 < ‖x‖ := lt_trans hρ hx
    have hnormx : ‖x‖ ≠ 0 := hnormx_pos.ne'
    have hp_norm : ‖(ρ / ‖x‖) • x‖ = ρ := by
      calc
        ‖(ρ / ‖x‖) • x‖ = |ρ / ‖x‖| * ‖x‖ := norm_smul _ _
        _ = (ρ / ‖x‖) * ‖x‖ := by
          rw [abs_of_pos (div_pos hρ hnormx_pos)]
        _ = ρ := by
          rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hnormx, mul_one]
    have hp_inner : ⟪(ρ / ‖x‖) • x, x⟫_ℝ = ρ * ‖x‖ := by
      calc
        ⟪(ρ / ‖x‖) • x, x⟫_ℝ = (ρ / ‖x‖) * ⟪x, x⟫_ℝ := by
          rw [real_inner_smul_left]
        _ = (ρ / ‖x‖) * ‖x‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
        _ = ρ * ‖x‖ := by
          rw [pow_two, div_eq_mul_inv]
          ring_nf
          field_simp [hnormx]
    -- The radial candidate satisfies the projection characterization.
    have hproj :
        (ρ / ‖x‖) • x =
          projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x := by
      refine
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mpr ?_
      refine ⟨?_, ?_⟩
      · -- The candidate lies on the sphere of radius `ρ`, hence in the closed ball.
        show dist ((ρ / ‖x‖) • x) 0 ≤ ρ
        simp [dist_eq_norm, hp_norm]
      · intro y hy
        have hy_norm : ‖y‖ ≤ ρ := by
          simpa [C, Metric.mem_closedBall, dist_eq_norm] using hy
        have hy_inner : ⟪y, x⟫_ℝ ≤ ρ * ‖x‖ := by
          calc
            ⟪y, x⟫_ℝ ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
            _ ≤ ρ * ‖x‖ := by
              gcongr
        have hcoef_nonneg : 0 ≤ 1 - ρ / ‖x‖ := by
          have hdiv_lt : ρ / ‖x‖ < 1 := by
            exact (div_lt_one hnormx_pos).2 hx
          linarith
        -- Route correction: use the variational inequality directly on the radial candidate instead
        -- of unfolding the metric infimum definition.
        calc
          ⟪y - (ρ / ‖x‖) • x, x - (ρ / ‖x‖) • x⟫_ℝ
              = (1 - ρ / ‖x‖) * ⟪y - (ρ / ‖x‖) • x, x⟫_ℝ := by
                rw [show x - (ρ / ‖x‖) • x = (1 - ρ / ‖x‖) • x by
                  calc
                    x - (ρ / ‖x‖) • x = (1 : ℝ) • x - (ρ / ‖x‖) • x := by rw [one_smul]
                    _ = (1 - ρ / ‖x‖) • x := by rw [sub_smul], real_inner_smul_right]
          _ ≤ 0 := by
            refine mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg ?_
            calc
              ⟪y - (ρ / ‖x‖) • x, x⟫_ℝ = ⟪y, x⟫_ℝ - ⟪(ρ / ‖x‖) • x, x⟫_ℝ := by
                rw [inner_sub_left]
              _ ≤ 0 := by
                linarith [hy_inner, hp_inner]
    simpa [C, hx] using hproj.symm
  · have hx_mem : x ∈ C := by
      simpa [C, Metric.mem_closedBall, dist_eq_norm] using le_of_not_gt hx
    -- Points already in the closed ball are fixed by the projector.
    have hproj :
        x =
          projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x := by
      refine
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mpr ?_
      refine ⟨hx_mem, ?_⟩
      intro y hy
      simp
    simpa [C, hx] using hproj.symm

private theorem softThresholder_eq_sub_projection_closedBall (ρ : ℝ) (hρ : 0 < ρ) (x : H) :
    softThresholder ρ x =
      x -
        projectionPoint (Metric.closedBall (0 : H) ρ)
          (isChebyshev_of_nonempty_isClosed_convex
            (closedBall_zero_nonempty ρ hρ)
            (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) ρ))
            (convex_closedBall (0 : H) ρ)) x := by
  -- Split according to the textbook radial threshold.
  rw [softThresholder_apply, projectionPoint_closedBall_zero_eq_radial_clip ρ hρ x]
  by_cases hx : ρ < ‖x‖
  · -- Outside the ball, `x - P x` is exactly the residual radial factor.
    simp [hx]
    have hsub : x - (ρ / ‖x‖) • x = (1 - ρ / ‖x‖) • x := by
      calc
        x - (ρ / ‖x‖) • x = (1 : ℝ) • x - (ρ / ‖x‖) • x := by rw [one_smul]
        _ = (1 - ρ / ‖x‖) • x := by rw [sub_smul]
    simpa using hsub.symm
  · -- Inside the ball, the projector fixes `x`, so the residual vanishes.
    simp [hx]

end

/-- Helper for Example 4.17: the reflected soft thresholder is the reflector `2T - Id` of the
soft thresholder. -/
theorem reflectedSoftThresholder_eq_reflectedMap_softThresholder (ρ : ℝ) (x : H) :
    reflectedSoftThresholder ρ x = (2 : ℝ) • softThresholder ρ x - x := by
  rw [reflectedSoftThresholder_apply, softThresholder_apply]
  by_cases hx : ρ < ‖x‖
  · rw [if_pos hx, if_pos hx]
    have hout :
        (2 : ℝ) • ((1 - ρ / ‖x‖) • x) - x = (1 - 2 * ρ / ‖x‖) • x := by
      calc
        (2 : ℝ) • ((1 - ρ / ‖x‖) • x) - x = (2 * (1 - ρ / ‖x‖)) • x - x := by
          rw [smul_smul]
        _ = (2 - 2 * ρ / ‖x‖) • x - x := by ring_nf
        _ = (1 - 2 * ρ / ‖x‖) • x := by
          calc
            (2 - 2 * ρ / ‖x‖) • x - x = (2 - 2 * ρ / ‖x‖) • x - (1 : ℝ) • x := by
              rw [one_smul]
            _ = ((2 - 2 * ρ / ‖x‖) - 1) • x := by rw [← sub_smul]
            _ = (1 - 2 * ρ / ‖x‖) • x := by ring_nf
    simpa using hout.symm
  · rw [if_neg hx, if_neg hx]
    simp

private theorem hardThresholder_fixed_iff_eq_zero (ρ α : ℝ) (hα1 : α < 1) (y : H) :
    hardThresholder ρ α y = y ↔ y = 0 := by
  constructor
  · intro hy
    by_cases hyρ : ρ < ‖y‖
    · -- On the outer branch the fixed-point equation forces `(α - 1) • y = 0`.
      have hscale : (α - 1) • y = 0 := by
        calc
          (α - 1) • y = α • y - y := by
            rw [sub_smul, one_smul]
          _ = hardThresholder ρ α y - y := by
            rw [hardThresholder_apply, if_pos hyρ]
          _ = 0 := by
            rw [hy, sub_self]
      have hαne : α - 1 ≠ 0 := sub_ne_zero.mpr hα1.ne
      rcases smul_eq_zero.mp hscale with hzero | hyzero
      · exact False.elim (hαne hzero)
      · exact hyzero
    · -- On the inner branch the operator value is `0`.
      rw [hardThresholder_apply, if_neg hyρ] at hy
      simpa using hy.symm
  · intro hy
    -- The origin is trivially fixed.
    rw [hy, hardThresholder_apply]
    simp

private theorem norm_hardThresholder_le_norm (ρ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (x : H) :
    ‖hardThresholder ρ α x‖ ≤ ‖x‖ := by
  by_cases hx : ρ < ‖x‖
  · -- Outside the ball, the operator just scales by a factor in `[0,1]`.
    rw [hardThresholder_apply, if_pos hx]
    calc
      ‖α • x‖ = α * ‖x‖ := by
        rw [norm_smul, Real.norm_of_nonneg hα0]
      _ ≤ ‖x‖ := by
        nlinarith [norm_nonneg x]
  · -- Inside the ball, the operator vanishes.
    rw [hardThresholder_apply, if_neg hx]
    simp

-- Proof sketch: identify `softThresholder ρ` with `Id - P_{closedBall 0 ρ}` and combine the
-- projector example with the firm-nonexpansive projector criterion.
/-- Example 4.17 (1): for positive level `ρ`, the soft thresholder is firmly nonexpansive. -/
theorem softThresholder_firmlyNonexpansive [CompleteSpace H] (ρ : ℝ) (hρ : 0 < ρ) :
    FirmlyNonexpansiveOn (Set.univ : Set H) (softThresholder ρ : H → H) := by
  rw [firmlyNonexpansiveOn_univ_iff]
  intro x y
  let C : Set H := Metric.closedBall (0 : H) ρ
  let P : H → H :=
    fun z ↦
      projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex
          (closedBall_zero_nonempty ρ hρ)
          (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) ρ))
          (convex_closedBall (0 : H) ρ)) z
  let a := P x - P y
  let b := x - y
  have hproj : ‖a‖ ^ (2 : ℕ) ≤ ⟪a, b⟫_ℝ := by
    simpa [a, b, P, C] using
      norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
        (closedBall_zero_nonempty ρ hρ)
        (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) ρ))
        (convex_closedBall (0 : H) ρ) x y
  have hresid_diff : (x - P x) - (y - P y) = b - a := by
    dsimp [a, b]
    abel_nf
  have hinner :
      ⟪b - a, b⟫_ℝ = ‖b‖ ^ (2 : ℕ) - ⟪a, b⟫_ℝ := by
    calc
      ⟪b - a, b⟫_ℝ = ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ := by
        rw [inner_sub_left]
      _ = ‖b‖ ^ (2 : ℕ) - ⟪a, b⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
  have hnorm :
      ‖b - a‖ ^ (2 : ℕ) = ‖b‖ ^ (2 : ℕ) - 2 * ⟪b, a⟫_ℝ + ‖a‖ ^ (2 : ℕ) := by
    simpa using norm_sub_sq_real b a
  have hfinal : ‖b - a‖ ^ (2 : ℕ) ≤ ⟪b - a, b⟫_ℝ := by
    have hnorm' :
        ‖b - a‖ ^ (2 : ℕ) = ‖b‖ ^ (2 : ℕ) - 2 * ⟪a, b⟫_ℝ + ‖a‖ ^ (2 : ℕ) := by
      simpa [real_inner_comm] using hnorm
    rw [hnorm', hinner]
    nlinarith [hproj]
  -- The residual map `x - P x` is exactly the soft thresholder.
  simpa [hresid_diff, a, b, P, C,
    softThresholder_eq_sub_projection_closedBall ρ hρ x,
    softThresholder_eq_sub_projection_closedBall ρ hρ y] using hfinal

-- Proof sketch: show that the only fixed point is `0`, then use `‖hardThresholder ρ α x‖ ≤ ‖x‖`
-- for `0 < α < 1` to verify the defining inequality relative to fixed points.
/-- Example 4.17 (2): for `0 < α < 1`, the hard thresholder is quasinonexpansive. -/
theorem hardThresholder_quasinonexpansive (ρ α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    QuasinonexpansiveOn (Set.univ : Set H) (hardThresholder ρ α : H → H) := by
  rw [quasinonexpansiveOn_iff]
  intro x _ y hy
  rcases hy with ⟨_, hyfix⟩
  have hy_zero : y = 0 := by
    rw [Function.mem_fixedPoints_iff] at hyfix
    exact (hardThresholder_fixed_iff_eq_zero ρ α hα1 y).mp hyfix
  -- The unique fixed point is `0`, so the norm estimate closes the proof.
  simpa [hy_zero] using
    norm_hardThresholder_le_norm ρ α hα0.le hα1.le x

-- Proof sketch: compare points on opposite sides of the sphere `‖x‖ = ρ`; the jump
-- discontinuity of `hardThresholder ρ α` prevents any `1`-Lipschitz bound when `0 < α < 1`.
/-- Example 4.17 (3): for `0 < α < 1`, the hard thresholder is not nonexpansive. -/
theorem hardThresholder_not_nonexpansive [Nontrivial H]
    (ρ α : ℝ) (hρ : 0 < ρ) (hα0 : 0 < α) (hα1 : α < 1) :
    ¬ LipschitzWith 1 (hardThresholder ρ α : H → H) := by
  intro hLip
  obtain ⟨u, hu⟩ := exists_norm_eq H hρ.le
  let v : H := (1 + α / 2) • u
  have hcoef_pos : 0 < 1 + α / 2 := by
    nlinarith [hα0]
  have hv_branch : ρ < ‖v‖ := by
    dsimp [v]
    rw [norm_smul, Real.norm_of_nonneg hcoef_pos.le, hu]
    nlinarith [hρ, hα0]
  have hu_branch : ¬ ρ < ‖u‖ := by
    rw [hu]
    exact lt_irrefl ρ
  have hTu : hardThresholder ρ α u = 0 := by
    rw [hardThresholder_apply, if_neg hu_branch]
  have hTv : hardThresholder ρ α v = α • v := by
    rw [hardThresholder_apply, if_pos hv_branch]
  have hdist := hLip.dist_le_mul u v
  -- The chosen radial pair crosses the threshold, so the operator jump is too large.
  rw [NNReal.coe_one, one_mul, hTu, hTv, dist_eq_norm, dist_eq_norm] at hdist
  dsimp [v] at hdist ⊢
  rw [zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg hα0.le, norm_smul,
    Real.norm_of_nonneg hcoef_pos.le, hu] at hdist
  have hvu : v - u = (α / 2) • u := by
    calc
      v - u = (1 + α / 2) • u - (1 : ℝ) • u := by
        dsimp [v]
        rw [one_smul]
      _ = ((1 + α / 2) - 1) • u := by rw [← sub_smul]
      _ = (α / 2) • u := by ring_nf
  have huv : u - v = -((α / 2) • u) := by
    rw [show u - v = -(v - u) by abel_nf, hvu]
  rw [huv, norm_neg, norm_smul, Real.norm_of_nonneg (by nlinarith [hα0]), hu] at hdist
  ring_nf at hdist
  nlinarith [hρ, hα0, hα1, hdist]

-- Proof sketch: choose a nonzero vector inside the radius-`ρ` ball and compare it with a fixed
-- point on the sphere of radius `2ρ`; the quasinonexpansive inequality fails when `α = 1`.
/-- Example 4.17 (4): at `α = 1`, the hard thresholder is not quasinonexpansive. -/
theorem hardThresholder_not_quasinonexpansive_at_one [Nontrivial H] (ρ : ℝ) (hρ : 0 < ρ) :
    ¬ QuasinonexpansiveOn (Set.univ : Set H) (hardThresholder ρ 1 : H → H) := by
  intro hQ
  rw [quasinonexpansiveOn_iff] at hQ
  obtain ⟨x, hx⟩ := exists_norm_eq H (show 0 ≤ ρ / 2 by positivity)
  let y : H := (4 : ℝ) • x
  have hx_branch : ¬ ρ < ‖x‖ := by
    rw [hx]
    nlinarith [hρ]
  have hy_branch : ρ < ‖y‖ := by
    dsimp [y]
    rw [norm_smul, Real.norm_of_nonneg (by positivity), hx]
    nlinarith [hρ]
  have hTx : hardThresholder ρ 1 x = 0 := by
    rw [hardThresholder_apply, if_neg hx_branch]
  have hTy : hardThresholder ρ 1 y = y := by
    rw [hardThresholder_apply, if_pos hy_branch]
    simp [y]
  have hineq :=
    hQ x (by simp) y (show y ∈ (Set.univ : Set H) ∩ Function.fixedPoints (hardThresholder ρ 1) by
        refine ⟨by simp, ?_⟩
        rw [Function.mem_fixedPoints_iff]
        exact hTy)
  -- The inside-ball point and the fixed point at radius `2ρ` violate quasinonexpansiveness.
  rw [hTx] at hineq
  dsimp [y] at hineq ⊢
  rw [zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity), hx] at hineq
  have hxy : x - y = (-3 : ℝ) • x := by
    calc
      x - y = (1 : ℝ) • x - (4 : ℝ) • x := by
        dsimp [y]
        rw [one_smul]
      _ = ((1 : ℝ) - 4) • x := by rw [← sub_smul]
      _ = (-3 : ℝ) • x := by norm_num
  rw [hxy, norm_smul, hx] at hineq
  norm_num at hineq
  nlinarith [hρ]

-- Proof sketch: rewrite `reflectedSoftThresholder ρ` as `2 * softThresholder ρ - Id` and invoke
-- the reflected-map characterization of firm nonexpansiveness.
/-- Example 4.17 (5): for positive level `ρ`, the operator `T₃` is nonexpansive. -/
theorem reflectedSoftThresholder_nonexpansive [CompleteSpace H] (ρ : ℝ) (hρ : 0 < ρ) :
    LipschitzWith 1 (reflectedSoftThresholder ρ : H → H) := by
  have hsoft :
      LipschitzWith 1 (fun x : H ↦ (2 : ℝ) • softThresholder ρ x - x) :=
    (firmlyNonexpansiveOn_univ_iff_lipschitzWith_one_reflectedMap).mp
      (softThresholder_firmlyNonexpansive ρ hρ)
  convert hsoft using 1
  funext x
  exact reflectedSoftThresholder_eq_reflectedMap_softThresholder ρ x

-- Proof sketch: test the firm inequality on antipodal points with norm `ρ`; the inequality from
-- firm nonexpansiveness fails on this boundary configuration.
/-- Example 4.17 (6): for positive level `ρ`, the operator `T₃` is not firmly nonexpansive. -/
theorem reflectedSoftThresholder_not_firmlyNonexpansive [Nontrivial H] (ρ : ℝ) (hρ : 0 < ρ) :
    ¬ FirmlyNonexpansiveOn (Set.univ : Set H) (reflectedSoftThresholder ρ : H → H) := by
  intro hFirm
  rw [firmlyNonexpansiveOn_univ_iff] at hFirm
  obtain ⟨u, hu⟩ := exists_norm_eq H hρ.le
  have hu_branch : ¬ ρ < ‖u‖ := by
    rw [hu]
    exact lt_irrefl ρ
  have hv_branch : ¬ ρ < ‖-u‖ := by
    rw [norm_neg, hu]
    exact lt_irrefl ρ
  have hTu : reflectedSoftThresholder ρ u = -u := by
    rw [reflectedSoftThresholder_apply, if_neg hu_branch]
  have hTv : reflectedSoftThresholder ρ (-u) = u := by
    rw [reflectedSoftThresholder_apply, if_neg hv_branch]
    simp
  have hineq := hFirm u (-u)
  -- On antipodal boundary points the firm inequality becomes impossible.
  rw [hTu, hTv] at hineq
  have hleft : -u - u = (-2 : ℝ) • u := by
    calc
      -u - u = (-u) + (-u) := by simp [sub_eq_add_neg]
      _ = (-1 : ℝ) • u + (-1 : ℝ) • u := by simp
      _ = (-2 : ℝ) • u := by
        rw [← add_smul]
        norm_num
  have hright : u - (-u) = (2 : ℝ) • u := by
    calc
      u - (-u) = u + u := by simp
      _ = (2 : ℝ) • u := by rw [two_smul]
  rw [hleft, hright, norm_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hu, pow_two] at hineq
  norm_num at hineq
  nlinarith [hρ]

end
