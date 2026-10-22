/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Expand the quadratic defect of `‖x - α • y‖` into a scalar expression controlled by
`⟪x, y⟫_ℝ`. -/
private lemma norm_sub_smul_mul_self_sub_norm_mul_self (x y : H) (α : ℝ) :
    ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖ =
      α * (α * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ) := by
  -- Rewrite the norm defect using the standard real inner-product expansion.
  calc
    ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖
        = (‖x‖ * ‖x‖ - 2 * ⟪x, α • y⟫_ℝ + ‖α • y‖ * ‖α • y‖) - ‖x‖ * ‖x‖ := by
            rw [norm_sub_mul_self_real]
    _ = -2 * ⟪x, α • y⟫_ℝ + ‖α • y‖ * ‖α • y‖ := by ring
    _ = -2 * (α * ⟪x, y⟫_ℝ) + ‖α • y‖ * ‖α • y‖ := by
          rw [real_inner_smul_right]
    _ = -2 * (α * ⟪x, y⟫_ℝ) + (|α| * ‖y‖) * (|α| * ‖y‖) := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = -2 * (α * ⟪x, y⟫_ℝ) + (α * α) * (‖y‖ * ‖y‖) := by
          rw [show (|α| * ‖y‖) * (|α| * ‖y‖) = (|α| * |α|) * (‖y‖ * ‖y‖) by ring,
            abs_mul_abs_self]
    _ = α * (α * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ) := by ring

/-- If the norm inequality holds for every `α ∈ [0,1]`, then the real inner product is
nonpositive. -/
private lemma real_inner_nonpos_of_norm_le_sub_smul_unitInterval (x y : H)
    (h : ∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖) :
    ⟪x, y⟫_ℝ ≤ 0 := by
  by_contra hxy
  have hxy_pos : 0 < ⟪x, y⟫_ℝ := lt_of_not_ge hxy
  let β : ℝ := ⟪x, y⟫_ℝ / (‖y‖ * ‖y‖ + 1)
  let α : ℝ := min 1 β
  have hden : 0 < ‖y‖ * ‖y‖ + 1 := by
    positivity
  have hβ_pos : 0 < β := by
    exact div_pos hxy_pos hden
  have hα_pos : 0 < α := by
    dsimp [α]
    exact (lt_min_iff.mpr ⟨zero_lt_one, hβ_pos⟩)
  have hα_mem : α ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨le_of_lt hα_pos, ?_⟩
    dsimp [α]
    exact min_le_left _ _
  -- Evaluate the interval hypothesis at a small positive scalar.
  have hα_norm : ‖x‖ ≤ ‖x - α • y‖ := h ⟨α, hα_mem⟩
  have hα_sq : ‖x‖ * ‖x‖ ≤ ‖x - α • y‖ * ‖x - α • y‖ := by
    nlinarith [hα_norm, norm_nonneg x, norm_nonneg (x - α • y)]
  have hdef_nonneg : 0 ≤ ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖ := by
    nlinarith
  -- The special choice of `α` makes the quadratic defect strictly negative.
  have hβ_eq : β * (‖y‖ * ‖y‖ + 1) = ⟪x, y⟫_ℝ := by
    simp [β, hden.ne']
  have hnorm_sq_nonneg : 0 ≤ ‖y‖ * ‖y‖ := by
    positivity
  have hβ_lt : β * (‖y‖ * ‖y‖) < ⟪x, y⟫_ℝ := by
    nlinarith [hβ_eq, hβ_pos]
  have hα_le_β : α ≤ β := by
    dsimp [α]
    exact min_le_right _ _
  have hα_lt : α * (‖y‖ * ‖y‖) < ⟪x, y⟫_ℝ := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα_le_β hnorm_sq_nonneg) hβ_lt
  have hfactor_neg : α * (α * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ) < 0 := by
    have : α * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ < 0 := by
      nlinarith [hα_lt, hxy_pos]
    exact mul_neg_of_pos_of_neg hα_pos this
  rw [norm_sub_smul_mul_self_sub_norm_mul_self] at hdef_nonneg
  linarith

/-- Lemma 2.13 (1), clause `(i)`: a nonpositive real inner product is equivalent to monotonicity
of `α ↦ ‖x - α • y‖` at `α = 0` along nonnegative real scalars. -/
theorem real_inner_nonpos_iff_norm_le_sub_nonneg_smul (x y : H) :
    ⟪x, y⟫_ℝ ≤ 0 ↔ ∀ α : NNReal, ‖x‖ ≤ ‖x - (α : ℝ) • y‖ := by
  constructor
  · intro hxy α
    have hα_nonneg : 0 ≤ (α : ℝ) := α.2
    have hy_sq_nonneg : 0 ≤ ‖y‖ * ‖y‖ := by
      positivity
    have hterm_nonneg : 0 ≤ (α : ℝ) * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ := by
      nlinarith [hxy, hα_nonneg, hy_sq_nonneg]
    have hfactor_nonneg : 0 ≤ (α : ℝ) * ((α : ℝ) * (‖y‖ * ‖y‖) - 2 * ⟪x, y⟫_ℝ) := by
      exact mul_nonneg hα_nonneg hterm_nonneg
    -- Nonnegativity of the defect gives the norm inequality after squaring.
    have hsq : ‖x‖ * ‖x‖ ≤ ‖x - (α : ℝ) • y‖ * ‖x - (α : ℝ) • y‖ := by
      nlinarith [norm_sub_smul_mul_self_sub_norm_mul_self x y (α : ℝ), hfactor_nonneg]
    have hsq' : ‖x‖ ^ 2 ≤ ‖x - (α : ℝ) • y‖ ^ 2 := by
      simpa [sq] using hsq
    exact le_of_sq_le_sq hsq' (norm_nonneg _)
  · intro h
    exact real_inner_nonpos_of_norm_le_sub_smul_unitInterval x y fun α ↦ by
      simpa using h ⟨α, α.2.1⟩

/-- Lemma 2.13 (1), clause `(i)`: it is enough to test the norm inequality only for
`α ∈ [0, 1]`. -/
theorem real_inner_nonpos_iff_norm_le_sub_smul_unitInterval (x y : H) :
    ⟪x, y⟫_ℝ ≤ 0 ↔ ∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖ := by
  constructor
  · intro hxy α
    exact (real_inner_nonpos_iff_norm_le_sub_nonneg_smul x y).mp hxy ⟨α, α.2.1⟩
  · exact real_inner_nonpos_of_norm_le_sub_smul_unitInterval x y

/-- Lemma 2.13 (1): package the textbook clause `(i)` as a `TFAE`. -/
theorem real_inner_nonpos_sub_smul_tfae (x y : H) :
    List.TFAE
      [⟪x, y⟫_ℝ ≤ 0,
        (∀ α : NNReal, ‖x‖ ≤ ‖x - (α : ℝ) • y‖),
        (∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖)] := by
  tfae_have 1 ↔ 2 := real_inner_nonpos_iff_norm_le_sub_nonneg_smul x y
  tfae_have 1 ↔ 3 := real_inner_nonpos_iff_norm_le_sub_smul_unitInterval x y
  tfae_finish

/-- If the norm inequality holds on `[-1,1]`, then the real inner product vanishes. -/
private lemma real_inner_eq_zero_of_norm_le_sub_smul_symmetricUnitInterval (x y : H)
    (h : ∀ α : Set.Icc (-1 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖) :
    ⟪x, y⟫_ℝ = 0 := by
  -- First restrict the symmetric interval hypothesis to `[0,1]`.
  have hy : ∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖ := fun α ↦
    h ⟨(α : ℝ), by constructor <;> linarith [α.2.1, α.2.2]⟩
  have hnonpos : ⟪x, y⟫_ℝ ≤ 0 := by
    exact (real_inner_nonpos_iff_norm_le_sub_smul_unitInterval x y).mpr hy
  -- Then apply part (i) to `-y` by testing the original hypothesis at `-α`.
  have hneg_interval : ∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • (-y)‖ := fun α ↦ by
    have hmem : (-(α : ℝ)) ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · linarith [α.2.2]
      · linarith [α.2.1]
    have hα : ‖x‖ ≤ ‖x - (-(α : ℝ)) • y‖ := h ⟨-(α : ℝ), hmem⟩
    simpa [sub_eq_add_neg, smul_neg, add_comm, add_left_comm, add_assoc] using hα
  have hneg_nonpos : ⟪x, -y⟫_ℝ ≤ 0 := by
    exact (real_inner_nonpos_iff_norm_le_sub_smul_unitInterval x (-y)).mpr hneg_interval
  have hnonneg : 0 ≤ ⟪x, y⟫_ℝ := by
    simpa [inner_neg_right] using hneg_nonpos
  exact le_antisymm hnonpos hnonneg

-- Proof sketch: if `⟪x, y⟫_ℝ = 0`, then `norm_sub_sq_eq_norm_sq_add_norm_sq_real` applied to
-- `x` and `α • y` gives the required inequality for every `α : ℝ`. Conversely, the hypothesis on
-- `α ∈ [-1,1]` implies the interval condition from part (i) for both `y` and `-y`, yielding
-- `⟪x, y⟫_ℝ ≤ 0` and `-⟪x, y⟫_ℝ ≤ 0`, hence equality.
/-- Lemma 2.13 (2), clause `(ii)`: vanishing of the real inner product is equivalent to the norm
inequality for every real scalar. -/
theorem real_inner_eq_zero_iff_norm_le_sub_smul (x y : H) :
    ⟪x, y⟫_ℝ = 0 ↔ ∀ α : ℝ, ‖x‖ ≤ ‖x - α • y‖ := by
  constructor
  · intro hxy α
    have horth : ⟪x, α • y⟫_ℝ = 0 := by
      rw [real_inner_smul_right, hxy, mul_zero]
    have hpyth : ‖x - α • y‖ * ‖x - α • y‖ = ‖x‖ * ‖x‖ + ‖α • y‖ * ‖α • y‖ :=
      norm_sub_sq_eq_norm_sq_add_norm_sq_real horth
    -- Orthogonality turns the defect into a nonnegative square term.
    have hsq : ‖x‖ * ‖x‖ ≤ ‖x - α • y‖ * ‖x - α • y‖ := by
      nlinarith [hpyth, norm_nonneg (α • y)]
    have hsq' : ‖x‖ ^ 2 ≤ ‖x - α • y‖ ^ 2 := by
      simpa [sq] using hsq
    exact le_of_sq_le_sq hsq' (norm_nonneg _)
  · intro h
    exact real_inner_eq_zero_of_norm_le_sub_smul_symmetricUnitInterval x y fun α ↦ h α

/-- Lemma 2.13 (2), clause `(ii)`: it is enough to test the norm inequality for
`α ∈ [-1, 1]`. -/
theorem real_inner_eq_zero_iff_norm_le_sub_smul_symmetricUnitInterval (x y : H) :
    ⟪x, y⟫_ℝ = 0 ↔ ∀ α : Set.Icc (-1 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖ := by
  constructor
  · intro hxy α
    exact (real_inner_eq_zero_iff_norm_le_sub_smul x y).mp hxy α
  · exact real_inner_eq_zero_of_norm_le_sub_smul_symmetricUnitInterval x y

/-- Lemma 2.13 (2): package the textbook clause `(ii)` as a `TFAE`. -/
theorem real_inner_eq_zero_sub_smul_tfae (x y : H) :
    List.TFAE
      [⟪x, y⟫_ℝ = 0,
        (∀ α : ℝ, ‖x‖ ≤ ‖x - α • y‖),
        (∀ α : Set.Icc (-1 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖)] := by
  tfae_have 1 ↔ 2 := real_inner_eq_zero_iff_norm_le_sub_smul x y
  tfae_have 1 ↔ 3 := real_inner_eq_zero_iff_norm_le_sub_smul_symmetricUnitInterval x y
  tfae_finish
