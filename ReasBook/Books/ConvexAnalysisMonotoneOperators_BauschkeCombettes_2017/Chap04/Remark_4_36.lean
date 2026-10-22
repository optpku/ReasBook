/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Corollary_2_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Set

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {T : H → H} {α : ℝ}

private lemma companion_fixed_of_isFixedPt
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {T R : D → H} (hT : ∀ x : D, T x = (1 - α) • (x : H) + α • R x)
    {p : D} (hp : T p = p) :
    R p = p := by
  have h_avg : (p : H) = (1 - α) • (p : H) + α • R p := by
    calc
      (p : H) = T p := hp.symm
      _ = (1 - α) • (p : H) + α • R p := hT p
  have hsmul : α • (p : H) = α • R p := by
    have hp_sub : (p : H) - (1 - α) • (p : H) = α • (p : H) := by
      module
    have hsub : (p : H) - (1 - α) • (p : H) = α • R p := by
      simpa using congrArg (fun z ↦ z - (1 - α) • (p : H)) h_avg
    calc
      α • (p : H) = (p : H) - (1 - α) • (p : H) := hp_sub.symm
      _ = α • R p := hsub
  have hα_ne : α ≠ 0 := ne_of_gt hα.1
  exact smul_right_injective H hα_ne hsmul.symm

private lemma averaged_sqnorm_le_sqnorm_sub_correction
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {T R : D → H} (hR : LipschitzWith 1 R)
    (hT : ∀ x : D, T x = (1 - α) • (x : H) + α • R x)
    (x p : D) (hp : T p = p) :
    ‖T x - p‖ ^ 2 + α * (1 - α) * ‖(x : H) - R x‖ ^ 2 ≤ ‖(x : H) - p‖ ^ 2 := by
  have hRp : R p = p := companion_fixed_of_isFixedPt hα hT hp
  have hR_le : ‖R x - p‖ ≤ ‖(x : H) - p‖ := by
    simpa [Subtype.dist_eq, dist_eq_norm, hRp, one_mul] using hR.dist_le_mul x p
  have hR_sq_le : ‖R x - p‖ ^ 2 ≤ ‖(x : H) - p‖ ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hR_le 2
  have hTx_vec :
      T x - p = α • (R x - p) + (1 - α) • ((x : H) - p) := by
    rw [hT x]
    module
  have hTx_rewrite :
      ‖T x - p‖ ^ 2 = ‖α • (R x - p) + (1 - α) • ((x : H) - p)‖ ^ 2 := by
    simp [hTx_vec]
  have hdiff_rewrite :
      ‖(x : H) - R x‖ ^ 2 = ‖(R x - p) - ((x : H) - p)‖ ^ 2 := by
    congr 1
    rw [show (R x - p) - ((x : H) - p) = R x - x by abel]
    rw [norm_sub_rev]
  have h_affine :
      ‖T x - p‖ ^ 2 + α * (1 - α) * ‖(x : H) - R x‖ ^ 2 =
        α * ‖R x - p‖ ^ 2 + (1 - α) * ‖(x : H) - p‖ ^ 2 := by
    rw [hTx_rewrite, hdiff_rewrite]
    simpa using
      norm_sq_affine_combination_add_weighted_norm_sub_sq (R x - p) ((x : H) - p) α
  calc
    ‖T x - p‖ ^ 2 + α * (1 - α) * ‖(x : H) - R x‖ ^ 2
        = α * ‖R x - p‖ ^ 2 + (1 - α) * ‖(x : H) - p‖ ^ 2 := h_affine
    _ ≤ α * ‖(x : H) - p‖ ^ 2 + (1 - α) * ‖(x : H) - p‖ ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hR_sq_le hα.1.le) le_rfl
    _ = ‖(x : H) - p‖ ^ 2 := by ring

private lemma companion_ne_of_not_isFixedPt
    {T R : D → H} (hT : ∀ x : D, T x = (1 - α) • (x : H) + α • R x)
    {x : D} (hx : T x ≠ x) :
    (x : H) ≠ R x := by
  intro hRx
  have hTx : T x = x := by
    calc
      T x = (1 - α) • (x : H) + α • R x := hT x
      _ = (1 - α) • (x : H) + α • (x : H) := by rw [← hRx]
      _ = ((1 - α) + α) • (x : H) := by rw [← add_smul]
      _ = (1 : ℝ) • (x : H) := by congr 1; ring
      _ = x := one_smul ℝ (x : H)
  exact hx hTx

-- Proof sketch: unpack the canonical `AveragedWith` witness on the restriction to `D`, show that
-- fixed points of the averaged map are fixed by its nonexpansive companion, and then apply the
-- Hilbert-space affine norm identity with the resulting positive correction term.
/-- Remark 4.36: an averaged self-map on `D` is strictly quasinonexpansive on `D`. -/
theorem averaged_strictlyQuasinonexpansiveOn
    (hT : AveragedWith α (fun x : D ↦ T x)) :
    StrictlyQuasinonexpansiveOn D T := by
  rcases averagedWith_iff.mp hT with ⟨hα, R, hR, hTR⟩
  have hrepr : ∀ x : D, T x = (1 - α) • (x : H) + α • R x := by
    intro x
    simpa using congrArg (fun f : D → H ↦ f x) hTR
  rw [strictlyQuasinonexpansiveOn_iff]
  intro x hx p hp
  rcases mem_fixedPointSetOn_iff.mp hp with ⟨hpD, hpfix⟩
  let x' : D := ⟨x, hx.1⟩
  let p' : D := ⟨p, hpD⟩
  have hpfix' : T p' = p' := by
    simpa [p'] using hpfix
  have hsq :
      ‖T x - p‖ ^ 2 + α * (1 - α) * ‖x - R x'‖ ^ 2 ≤ ‖x - p‖ ^ 2 := by
    simpa [x', p'] using averaged_sqnorm_le_sqnorm_sub_correction hα hR hrepr x' p' hpfix'
  have hxfix_ne : T x' ≠ x' := by
    intro hxfix
    exact hx.2 <| mem_fixedPointSetOn_iff.mpr ⟨hx.1, by simpa [x'] using hxfix⟩
  have hxR_ne : x ≠ R x' := by
    simpa [x'] using companion_ne_of_not_isFixedPt hrepr hxfix_ne
  have hnorm_pos : 0 < ‖x - R x'‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hxR_ne
  have hcorr_pos : 0 < α * (1 - α) * ‖x - R x'‖ ^ 2 := by
    have h_one_sub_pos : 0 < 1 - α := sub_pos.mpr hα.2
    have hnorm_sq_pos : 0 < ‖x - R x'‖ ^ 2 := by nlinarith
    exact mul_pos (mul_pos hα.1 h_one_sub_pos) hnorm_sq_pos
  have hTx_sq_lt : ‖T x - p‖ ^ 2 < ‖x - p‖ ^ 2 := by
    nlinarith [hsq, hcorr_pos]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hTx_sq_lt

/-- An averaged self-map on `D` is quasinonexpansive on `D`. -/
theorem averaged_quasinonexpansiveOn
    (hT : AveragedWith α (fun x : D ↦ T x)) :
    QuasinonexpansiveOn D T :=
  (averaged_strictlyQuasinonexpansiveOn hT).quasinonexpansiveOn

end
