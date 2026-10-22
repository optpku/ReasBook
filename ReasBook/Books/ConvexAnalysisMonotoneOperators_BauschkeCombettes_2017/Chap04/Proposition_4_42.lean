/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {I : Type v} [Fintype I]

private lemma weighted_averagingParameter_mem_Ioo (ω α : I → ℝ)
    (hω : ∀ i, ω i ∈ Set.Icc (0 : ℝ) 1) (hω_sum : ∑ i, ω i = 1)
    (hα : ∀ i, α i ∈ Set.Ioo (0 : ℝ) 1) :
    (∑ i, ω i * α i) ∈ Set.Ioo (0 : ℝ) 1 := by
  classical
  let αbar : ℝ := ∑ i, ω i * α i
  have hω_exists : ∃ i, ω i ≠ 0 := by
    by_contra hω_exists
    have hω_zero : ∀ i, ω i = 0 := by
      intro i
      by_contra hωi
      exact hω_exists ⟨i, hωi⟩
    simp [hω_zero] at hω_sum
  rcases hω_exists with ⟨i₀, hωi₀_ne⟩
  have hωi₀_pos : 0 < ω i₀ := by
    exact lt_of_le_of_ne (hω i₀).1 (Ne.symm hωi₀_ne)
  have hαbar_pos : 0 < αbar := by
    have hi₀_pos : 0 < ω i₀ * α i₀ := mul_pos hωi₀_pos (hα i₀).1
    have hi₀_le : ω i₀ * α i₀ ≤ αbar := by
      simpa [αbar] using
        (Finset.single_le_sum
          (fun j _ ↦ mul_nonneg (hω j).1 (hα j).1.le)
          (by simp : i₀ ∈ (Finset.univ : Finset I)))
    exact lt_of_lt_of_le hi₀_pos hi₀_le
  have hαbar_lt : αbar < 1 := by
    let δ : ℝ := ∑ i, ω i * (1 - α i)
    have hδ_pos : 0 < δ := by
      have hi₀_pos : 0 < ω i₀ * (1 - α i₀) := by
        have hαi₀_lt : 0 < 1 - α i₀ := sub_pos.mpr (hα i₀).2
        exact mul_pos hωi₀_pos hαi₀_lt
      have hi₀_le : ω i₀ * (1 - α i₀) ≤ δ := by
        simpa [δ] using
          (Finset.single_le_sum
            (fun j _ ↦ mul_nonneg (hω j).1 (sub_nonneg.mpr (hα j).2.le))
            (by simp : i₀ ∈ (Finset.univ : Finset I)))
      exact lt_of_lt_of_le hi₀_pos hi₀_le
    have hsplit : αbar + δ = 1 := by
      calc
        αbar + δ = ∑ i, (ω i * α i + ω i * (1 - α i)) := by
          simp [αbar, δ, Finset.sum_add_distrib]
        _ = ∑ i, ω i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          ring
        _ = 1 := hω_sum
    nlinarith
  exact ⟨hαbar_pos, hαbar_lt⟩

/-- Helper for Proposition 4.42: normalizing the coefficients `ω i * α i` by their positive total
produces convex weights. -/
private lemma normalized_companion_weights_mem_Icc (ω α : I → ℝ)
    (hω : ∀ i, ω i ∈ Set.Icc (0 : ℝ) 1) (hαi : ∀ i, α i ∈ Set.Ioo (0 : ℝ) 1)
    (hα : (∑ i, ω i * α i) ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ i, (ω i * α i) / (∑ j, ω j * α j) ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  have hαbar_pos : 0 < ∑ j, ω j * α j := hα.1
  have hnum_nonneg : 0 ≤ ω i * α i := mul_nonneg (hω i).1 (hαi i).1.le
  have hnum_le :
      ω i * α i ≤ ∑ j, ω j * α j := by
    simpa using
      (Finset.single_le_sum
        (fun j _ ↦ mul_nonneg (hω j).1 (hαi j).1.le)
        (by simp : i ∈ (Finset.univ : Finset I)))
  refine ⟨div_nonneg hnum_nonneg hαbar_pos.le, ?_⟩
  have hdiv_le :
      (ω i * α i) / (∑ j, ω j * α j) ≤
        (∑ j, ω j * α j) / (∑ j, ω j * α j) := by
    exact div_le_div_of_nonneg_right hnum_le hαbar_pos.le
  simpa [ne_of_gt hαbar_pos] using hdiv_le

/-- Helper for Proposition 4.42: the normalized coefficients of the affine companion sum to `1`. -/
private lemma normalized_companion_weights_sum (ω α : I → ℝ)
    (hα : (∑ i, ω i * α i) ∈ Set.Ioo (0 : ℝ) 1) :
    ∑ i, (ω i * α i) / (∑ j, ω j * α j) = 1 := by
  let αbar : ℝ := ∑ i, ω i * α i
  have hαbar_pos : 0 < αbar := by
    simpa [αbar] using hα.1
  have hαbar_ne : αbar ≠ 0 := ne_of_gt hαbar_pos
  calc
    ∑ i, (ω i * α i) / (∑ j, ω j * α j)
        = ∑ i, (ω i * α i) / αbar := by simp [αbar]
    _ = ∑ i, (ω i * α i) * αbar⁻¹ := by
          simp [div_eq_mul_inv]
    _ = (∑ i, ω i * α i) * αbar⁻¹ := by
          rw [← Finset.sum_mul]
    _ = αbar * αbar⁻¹ := by simp [αbar]
    _ = 1 := by
          exact mul_inv_cancel₀ hαbar_ne

/-- Helper for Proposition 4.42: a finite convex combination of `1`-Lipschitz maps on `D` is again
`1`-Lipschitz. -/
private lemma lipschitzWith_weighted_sum_fintype (β : I → ℝ) (R : I → D → H)
    (hR : ∀ i, LipschitzWith 1 (R i))
    (hβ : ∀ i, β i ∈ Set.Icc (0 : ℝ) 1) (hβ_sum : ∑ i, β i = 1) :
    LipschitzWith 1 (fun x : D ↦ ∑ i, β i • R i x) := by
  -- Control the weighted companion by the same triangle-inequality argument as Proposition 4.9.
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  calc
    dist (∑ i, β i • R i x) (∑ i, β i • R i y)
        = ‖∑ i, β i • (R i x - R i y)‖ := by
            simp [dist_eq_norm, smul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖β i • (R i x - R i y)‖ := norm_sum_le _ _
    _ = ∑ i, β i * ‖R i x - R i y‖ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβ i).1]
    _ ≤ ∑ i, β i * dist x y := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hRi : ‖R i x - R i y‖ ≤ dist x y := by
            simpa [dist_eq_norm] using (hR i).dist_le_mul x y
          exact mul_le_mul_of_nonneg_left hRi (hβ i).1
    _ = (∑ i, β i) * dist x y := by
          rw [Finset.sum_mul]
    _ = 1 * dist x y := by
          rw [hβ_sum]

/-- Helper for Proposition 4.42: after expanding each averaged operator, the weighted sum regroups
into the affine form with coefficient `∑ i, ω i * α i`. -/
private lemma weighted_sum_affine_decomposition (ω α : I → ℝ) (T R : I → D → H)
    (hω_sum : ∑ i, ω i = 1)
    (hα : (∑ i, ω i * α i) ∈ Set.Ioo (0 : ℝ) 1)
    (hTR : ∀ i, T i = fun x : D ↦ (1 - α i) • (x : H) + α i • R i x) :
    (fun x : D ↦ ∑ i, ω i • T i x) =
      fun x : D ↦
        (1 - ∑ i, ω i * α i) • (x : H) +
          (∑ i, ω i * α i) •
            (∑ i, ((ω i * α i) / (∑ j, ω j * α j)) • R i x) := by
  let αbar : ℝ := ∑ i, ω i * α i
  have hαbar_pos : 0 < αbar := by
    simpa [αbar] using hα.1
  have hαbar_ne : αbar ≠ 0 := ne_of_gt hαbar_pos
  have hcoeff :
      ∑ i, ω i * (1 - α i) = 1 - αbar := by
    calc
      ∑ i, ω i * (1 - α i)
          = ∑ i, (ω i - ω i * α i) := by
              refine Finset.sum_congr rfl fun i _ ↦ by ring
      _ = (∑ i, ω i) - ∑ i, ω i * α i := by
            rw [Finset.sum_sub_distrib]
      _ = 1 - αbar := by
            simp [hω_sum, αbar]
  -- Expand every `T i`, collect the identity part, and factor the companion part through `αbar`.
  ext x
  calc
    ∑ i, ω i • T i x
        = ∑ i, ω i • ((1 - α i) • (x : H) + α i • R i x) := by
            refine Finset.sum_congr rfl fun i _ ↦ by simp [hTR i]
    _ = ∑ i, ((ω i * (1 - α i)) • (x : H) + (ω i * α i) • R i x) := by
          refine Finset.sum_congr rfl fun i _ ↦ by
            rw [smul_add, ← mul_smul, ← mul_smul]
    _ = (∑ i, (ω i * (1 - α i)) • (x : H)) + ∑ i, (ω i * α i) • R i x := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i, ω i * (1 - α i)) • (x : H) + ∑ i, (ω i * α i) • R i x := by
          rw [Finset.sum_smul]
    _ = (1 - αbar) • (x : H) + ∑ i, (ω i * α i) • R i x := by
          simp [hcoeff]
    _ = (1 - αbar) • (x : H) +
          αbar • (∑ i, ((ω i * α i) / αbar) • R i x) := by
          congr 1
          have hcomp :
              αbar • (∑ i, ((ω i * α i) / αbar) • R i x) =
                ∑ i, (ω i * α i) • R i x := by
            calc
              αbar • (∑ i, ((ω i * α i) / αbar) • R i x)
                  = ∑ i, (αbar * ((ω i * α i) / αbar)) • R i x := by
                      rw [Finset.smul_sum]
                      refine Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul]
              _ = ∑ i, (ω i * α i) • R i x := by
                    refine Finset.sum_congr rfl fun i _ ↦ ?_
                    congr 1
                    field_simp [hαbar_ne]
          exact hcomp.symm
    _ = (1 - ∑ i, ω i * α i) • (x : H) +
          (∑ i, ω i * α i) •
            (∑ i, ((ω i * α i) / (∑ j, ω j * α j)) • R i x) := by
          simp [αbar]

-- Proof sketch: for each `i`, write `T i = (1 - α i) Id + α i R i` with `R i` nonexpansive.
-- Set `α := ∑ i, ω i * α i` and define `R := ∑ i, (ω i * α i / α) • R i`. The coefficients of `R`
-- are nonnegative and sum to `1`, so `R` is nonexpansive by the convex-combination result for
-- nonexpansive maps. Expanding the weighted sum of the `T i` then gives
-- `∑ i, ω i • T i = (1 - α) Id + α R`.
/-- Proposition 4.42: a finite convex combination of `α i`-averaged operators on a subset of a
real Hilbert space is `(\sum i, ω i * α i)`-averaged. -/
theorem averagedWith_weightedSum (ω α : I → ℝ) (T : I → D → H)
    (hω : ∀ i, ω i ∈ Set.Icc (0 : ℝ) 1) (hω_sum : ∑ i, ω i = 1)
    (hT : ∀ i, AveragedWith (α i) (T i)) :
    AveragedWith (∑ i, ω i * α i) (fun x : D ↦ ∑ i, ω i • T i x) := by
  have hαi : ∀ i, α i ∈ Set.Ioo (0 : ℝ) 1 := fun i ↦ (hT i).mem_Ioo
  have hαbar : (∑ i, ω i * α i) ∈ Set.Ioo (0 : ℝ) 1 :=
    weighted_averagingParameter_mem_Ioo ω α hω hω_sum hαi
  -- Write each `T i` with its nonexpansive affine companion.
  have hT' :
      ∀ i, ∃ R : D → H, LipschitzWith 1 R ∧
        T i = fun x : D ↦ (1 - α i) • (x : H) + α i • R x := by
    intro i
    exact (averagedWith_iff.mp (hT i)).2
  choose R hR hTR using hT'
  let β : I → ℝ := fun i ↦ (ω i * α i) / (∑ j, ω j * α j)
  let S : D → H := fun x ↦ ∑ i, β i • R i x
  have hβ : ∀ i, β i ∈ Set.Icc (0 : ℝ) 1 := by
    -- The normalized companion coefficients are convex weights.
    intro i
    simpa [β] using normalized_companion_weights_mem_Icc ω α hω hαi hαbar i
  have hβ_sum : ∑ i, β i = 1 := by
    -- The normalized companion coefficients sum to one.
    simpa [β] using normalized_companion_weights_sum ω α hαbar
  have hS_lipschitz : LipschitzWith 1 S := by
    -- A convex combination of nonexpansive companions stays nonexpansive.
    simpa [S, β] using lipschitzWith_weighted_sum_fintype β R hR hβ hβ_sum
  -- Route correction: use the normalized weighted companion directly, then regroup the affine
  -- expansion of the weighted sum into `(1 - αbar) Id + αbar S`.
  refine averagedWith_iff.mpr ⟨hαbar, S, hS_lipschitz, ?_⟩
  simpa [S, β] using weighted_sum_affine_decomposition ω α T R hω_sum hαbar hTR

end
