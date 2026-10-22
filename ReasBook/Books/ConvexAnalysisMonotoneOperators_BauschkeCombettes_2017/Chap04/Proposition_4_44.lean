/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Corollary_2_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_35

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H}

/-- The averaging constant attached to the composition of an `α₁`-averaged map with an
`α₂`-averaged map. -/
noncomputable def compositionAveragingConstant (α₁ α₂ : ℝ) : ℝ :=
  (α₁ + α₂ - 2 * α₁ * α₂) / (1 - α₁ * α₂)

/-- The composition averaging constant attached to two parameters in `(0, 1)` also lies in
`(0, 1)`. -/
theorem compositionAveragingConstant_mem_Ioo
    {α₁ α₂ : ℝ} (hα₁ : α₁ ∈ Set.Ioo (0 : ℝ) 1) (hα₂ : α₂ ∈ Set.Ioo (0 : ℝ) 1) :
    compositionAveragingConstant α₁ α₂ ∈ Set.Ioo (0 : ℝ) 1 := by
  have hdenom_pos : 0 < 1 - α₁ * α₂ := by
    nlinarith [hα₁.1, hα₁.2, hα₂.1, hα₂.2]
  have hnum_pos_aux : 0 < α₁ * (1 - α₂) + α₂ * (1 - α₁) := by
    nlinarith [hα₁.1, hα₁.2, hα₂.1, hα₂.2]
  have hnum_pos : 0 < α₁ + α₂ - 2 * α₁ * α₂ := by
    convert hnum_pos_aux using 1
    ring
  have hnum_lt_denom : α₁ + α₂ - 2 * α₁ * α₂ < 1 - α₁ * α₂ := by
    nlinarith [hα₁.1, hα₁.2, hα₂.1, hα₂.2]
  constructor
  · dsimp [compositionAveragingConstant]
    exact div_pos hnum_pos hdenom_pos
  · dsimp [compositionAveragingConstant]
    exact (div_lt_one hdenom_pos).2 hnum_lt_denom

/-- The affine-combination identity from Corollary 2.15 yields the lower bound used in the
composition argument. -/
private lemma weighted_sqnorm_ge_mul_norm_sub_sq (u v : H) (lam : ℝ) :
    lam * ‖u‖ ^ 2 + (1 - lam) * ‖v‖ ^ 2 ≥ lam * (1 - lam) * ‖u - v‖ ^ 2 := by
  have hidentity := norm_sq_affine_combination_add_weighted_norm_sub_sq u v lam
  have hnonneg : 0 ≤ ‖lam • u + (1 - lam) • v‖ ^ 2 := sq_nonneg _
  nlinarith [hidentity, hnonneg]

-- The two defect terms from the proof of Proposition 4.44 differ by the residual of `T₁ ∘ T₂`.
omit [InnerProductSpace ℝ H] in
private lemma composition_residual_eq_defect_sub_reverse_defect
    (T₁ T₂ : D → D) (x y : D) :
    (((T₂ x : H) - T₁ (T₂ x)) - ((T₂ y : H) - T₁ (T₂ y))) -
        (((y : H) - T₂ y) - ((x : H) - T₂ x)) =
      ((x : H) - T₁ (T₂ x)) - (y - T₁ (T₂ y)) := by
  simp [sub_eq_add_neg]
  abel_nf

/-- Proposition 4.44: the composition of two averaged self-maps is averaged, with averaging
constant `compositionAveragingConstant α₁ α₂`. -/
theorem averagedWith_comp {α₁ α₂ : ℝ} {T₁ T₂ : D → D}
    (hT₁ : AveragedWith α₁ (fun x : D ↦ (T₁ x : H)))
    (hT₂ : AveragedWith α₂ (fun x : D ↦ (T₂ x : H))) :
    AveragedWith (compositionAveragingConstant α₁ α₂) (fun x : D ↦ (T₁ (T₂ x) : H)) := by
  let α : ℝ := compositionAveragingConstant α₁ α₂
  let A : ℝ := (1 - α₁) / α₁
  let B : ℝ := (1 - α₂) / α₂
  let τ : ℝ := A + B
  have hα₁ : α₁ ∈ Set.Ioo (0 : ℝ) 1 := hT₁.mem_Ioo
  have hα₂ : α₂ ∈ Set.Ioo (0 : ℝ) 1 := hT₂.mem_Ioo
  have hα : α ∈ Set.Ioo (0 : ℝ) 1 := compositionAveragingConstant_mem_Ioo hα₁ hα₂
  have hA_pos : 0 < A := by
    dsimp [A]
    exact div_pos (sub_pos.mpr hα₁.2) hα₁.1
  have hB_pos : 0 < B := by
    dsimp [B]
    exact div_pos (sub_pos.mpr hα₂.2) hα₂.1
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    linarith
  rw [averagedWith_iff_residual_sqnorm_ineq hα]
  intro x y
  let a : H := ((T₂ x : H) - T₁ (T₂ x)) - ((T₂ y : H) - T₁ (T₂ y))
  let b : H := ((y : H) - T₂ y) - ((x : H) - T₂ x)
  have hT₁ineq := (averagedWith_iff_residual_sqnorm_ineq hα₁).1 hT₁ (T₂ x) (T₂ y)
  have hT₁ineq' :
      ‖(T₁ (T₂ x) : H) - T₁ (T₂ y)‖ ^ 2 ≤ ‖(T₂ x : H) - T₂ y‖ ^ 2 - A * ‖a‖ ^ 2 := by
    simpa [A, a] using hT₁ineq
  have hT₂ineq := (averagedWith_iff_residual_sqnorm_ineq hα₂).1 hT₂ x y
  have hT₂ineq' :
      ‖(T₂ x : H) - T₂ y‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 - B * ‖b‖ ^ 2 := by
    have hb_eq :
        b = - (((x : H) - T₂ x) - (y - T₂ y)) := by
      simp [b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      ‖(T₂ x : H) - T₂ y‖ ^ 2
          ≤ ‖(x : H) - y‖ ^ 2 - B * ‖((x : H) - T₂ x) - (y - T₂ y)‖ ^ 2 := by
            simpa [B] using hT₂ineq
      _ = ‖(x : H) - y‖ ^ 2 - B * ‖b‖ ^ 2 := by
            rw [hb_eq, norm_neg]
  have hsum :
      ‖(T₁ (T₂ x) : H) - T₁ (T₂ y)‖ ^ 2 ≤
        ‖(x : H) - y‖ ^ 2 - A * ‖a‖ ^ 2 - B * ‖b‖ ^ 2 := by
    nlinarith [hT₁ineq', hT₂ineq']
  have hLam_mem : A / τ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_of_lt (div_pos hA_pos hτ_pos)
    · have hA_le_τ : A ≤ τ := by
        dsimp [τ]
        linarith [le_of_lt hB_pos]
      have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
      have hdiv : A / τ ≤ 1 := by
        field_simp [hτ_ne]
        exact hA_le_τ
      exact hdiv
  have hweighted :
      (A / τ) * (1 - A / τ) * ‖a - b‖ ^ 2 ≤
        (A / τ) * ‖a‖ ^ 2 + (1 - A / τ) * ‖b‖ ^ 2 := by
    simpa using weighted_sqnorm_ge_mul_norm_sub_sq a b (A / τ)
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
  have hone_sub : 1 - A / τ = B / τ := by
    field_simp [hτ_ne]
    dsimp [τ]
    ring
  have hweighted' :
      (A / τ) * (B / τ) * ‖a - b‖ ^ 2 ≤
        (A / τ) * ‖a‖ ^ 2 + (B / τ) * ‖b‖ ^ 2 := by
    simpa [hone_sub] using hweighted
  have hmerge :
      (A * B / τ) * ‖a - b‖ ^ 2 ≤ A * ‖a‖ ^ 2 + B * ‖b‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hweighted' (le_of_lt hτ_pos)
    have hleft :
        τ * ((A / τ) * (B / τ) * ‖a - b‖ ^ 2) = (A * B / τ) * ‖a - b‖ ^ 2 := by
      field_simp [hτ_ne]
    have hright :
        τ * ((A / τ) * ‖a‖ ^ 2 + (B / τ) * ‖b‖ ^ 2) = A * ‖a‖ ^ 2 + B * ‖b‖ ^ 2 := by
      field_simp [hτ_ne]
    rw [hleft, hright] at hmul
    exact hmul
  have hresidual :
      a - b = ((x : H) - T₁ (T₂ x)) - (y - T₁ (T₂ y)) := by
    simpa [a, b] using composition_residual_eq_defect_sub_reverse_defect T₁ T₂ x y
  have hcoeff :
      A * B / τ = (1 - α) / α := by
    have hα₁_ne : α₁ ≠ 0 := ne_of_gt hα₁.1
    have hα₂_ne : α₂ ≠ 0 := ne_of_gt hα₂.1
    have hdenom_ne : 1 - α₁ * α₂ ≠ 0 := by
      nlinarith [hα₁.1, hα₁.2, hα₂.1, hα₂.2]
    dsimp [A, B, τ, α, compositionAveragingConstant]
    field_simp [hα₁_ne, hα₂_ne, hdenom_ne]
    ring
  have hresidual_control :
      ((1 - α) / α) * ‖((x : H) - T₁ (T₂ x)) - (y - T₁ (T₂ y))‖ ^ 2 ≤
        A * ‖a‖ ^ 2 + B * ‖b‖ ^ 2 := by
    calc
      ((1 - α) / α) * ‖((x : H) - T₁ (T₂ x)) - (y - T₁ (T₂ y))‖ ^ 2
          = (A * B / τ) * ‖a - b‖ ^ 2 := by
            rw [← hcoeff, ← hresidual]
      _ ≤ A * ‖a‖ ^ 2 + B * ‖b‖ ^ 2 := hmerge
  have htarget :
      ‖(T₁ (T₂ x) : H) - T₁ (T₂ y)‖ ^ 2 ≤
        ‖(x : H) - y‖ ^ 2 -
          ((1 - α) / α) * ‖((x : H) - T₁ (T₂ x)) - (y - T₁ (T₂ y))‖ ^ 2 := by
    nlinarith [hsum, hresidual_control]
  simpa [α] using htarget

end
