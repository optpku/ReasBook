/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.FirmlyNonexpansiveOn

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The residual map `Id - T` associated to a partially defined operator. -/
def residualMap (D : Set H) (T : D → H) : D → H :=
  fun x ↦ (x : H) - T x

/-- The reflected map `2T - Id` associated to a partially defined operator. -/
def reflectedMap (D : Set H) (T : D → H) : D → H :=
  fun x ↦ (2 : ℝ) • T x - x

/-- Helper for Proposition 4.4: a convex combination of `a` and `b` can be rewritten as
`b - α • (b - a)`. -/
private lemma segment_combination_eq_sub_smul (a b : H) (α : ℝ) :
    α • a + (1 - α) • b = b - α • (b - a) := by
  -- Rewrite the coefficient `(1 - α)` and then collect the additive terms.
  calc
    α • a + (1 - α) • b = α • a + (b - α • b) := by
      rw [sub_smul, one_smul]
    _ = b + (α • a - α • b) := by
      abel_nf
    _ = b - α • (b - a) := by
      rw [smul_sub]
      abel_nf

/-- Helper for Proposition 4.4: the reflected norm gap equals four times the firm
inner-product defect. -/
private lemma reflection_norm_gap_eq_four_mul (a b : H) :
    ‖a‖ ^ 2 - ‖(2 : ℝ) • b - a‖ ^ 2 = 4 * (inner ℝ a b - ‖b‖ ^ 2) := by
  have htwo : (2 : ℝ) • b = b + b := by
    simpa using (two_smul ℝ b)
  rw [htwo]
  have hsub : ‖a‖ ^ 2 - ‖(b + b) - a‖ ^ 2 = 2 * inner ℝ (b + b) a - ‖b + b‖ ^ 2 := by
    -- First isolate the reflected norm term using the standard `‖u - v‖²` identity.
    nlinarith [norm_sub_sq_real (b + b) a]
  have hnorm : ‖b + b‖ ^ 2 = 4 * ‖b‖ ^ 2 := by
    -- Then expand the doubled point `b + b`.
    rw [norm_add_sq_real, real_inner_self_eq_norm_sq]
    ring
  -- Assemble the two expansions and commute the inner product once.
  rw [hsub, hnorm, inner_add_left, real_inner_comm b a]
  ring

/-- Helper for Proposition 4.4: expanding `‖x - α • y‖² - ‖x‖²` factors the defect by `α`. -/
private lemma norm_sub_smul_defect_eq_factorized (x y : H) (α : ℝ) :
    ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖ =
      α * (α * (‖y‖ * ‖y‖) - 2 * inner ℝ x y) := by
  -- Rewrite the norm defect using the standard real inner-product expansion.
  calc
    ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖
        = (‖x‖ * ‖x‖ - 2 * inner ℝ x (α • y) + ‖α • y‖ * ‖α • y‖) - ‖x‖ * ‖x‖ := by
            rw [norm_sub_mul_self_real]
    _ = -2 * inner ℝ x (α • y) + ‖α • y‖ * ‖α • y‖ := by ring
    _ = -2 * (α * inner ℝ x y) + ‖α • y‖ * ‖α • y‖ := by
          rw [real_inner_smul_right]
    _ = -2 * (α * inner ℝ x y) + (|α| * ‖y‖) * (|α| * ‖y‖) := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = -2 * (α * inner ℝ x y) + (α * α) * (‖y‖ * ‖y‖) := by
          rw [show (|α| * ‖y‖) * (|α| * ‖y‖) = (|α| * |α|) * (‖y‖ * ‖y‖) by ring,
            abs_mul_abs_self]
    _ = α * (α * (‖y‖ * ‖y‖) - 2 * inner ℝ x y) := by ring

/-- Helper for Proposition 4.4: if `‖x‖ ≤ ‖x - α • y‖` on `[0,1]`, then `inner ℝ x y ≤ 0`. -/
private lemma inner_nonpos_of_unit_interval_sub_smul_norm_lower_bound (x y : H)
    (h : ∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖) :
    inner ℝ x y ≤ 0 := by
  by_contra hxy
  have hxy_pos : 0 < inner ℝ x y := lt_of_not_ge hxy
  let β : ℝ := inner ℝ x y / (‖y‖ * ‖y‖ + 1)
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
  have hβ_eq : β * (‖y‖ * ‖y‖ + 1) = inner ℝ x y := by
    simp [β, hden.ne']
  have hnorm_sq_nonneg : 0 ≤ ‖y‖ * ‖y‖ := by
    positivity
  have hβ_lt : β * (‖y‖ * ‖y‖) < inner ℝ x y := by
    nlinarith [hβ_eq, hβ_pos]
  have hα_le_β : α ≤ β := by
    dsimp [α]
    exact min_le_right _ _
  have hα_lt : α * (‖y‖ * ‖y‖) < inner ℝ x y := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα_le_β hnorm_sq_nonneg) hβ_lt
  have hfactor_neg : α * (α * (‖y‖ * ‖y‖) - 2 * inner ℝ x y) < 0 := by
    have : α * (‖y‖ * ‖y‖) - 2 * inner ℝ x y < 0 := by
      nlinarith [hα_lt, hxy_pos]
    exact mul_neg_of_pos_of_neg hα_pos this
  rw [norm_sub_smul_defect_eq_factorized] at hdef_nonneg
  linarith

/-- Helper for Proposition 4.4: firm nonexpansiveness of the residual map is equivalent to the
firm nonexpansiveness of `T` itself. -/
lemma firmlyNonexpansiveOn_residualMap_iff (D : Set H) (T : D → H) :
    FirmlyNonexpansiveOn D (residualMap D T) ↔ FirmlyNonexpansiveOn D T := by
  rw [firmlyNonexpansiveOn_iff]
  constructor
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : ‖residualMap D T x - residualMap D T y‖ ^ 2 ≤
        inner ℝ ((x : H) - y) (residualMap D T x - residualMap D T y) := h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hinner : inner ℝ a (a - b) = ‖a‖ ^ 2 - inner ℝ a b := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    -- Expanding the residual inequality leaves exactly the firm inequality for `T`.
    rw [hres] at hxy
    nlinarith [norm_sub_sq_real a b, hinner]
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : ‖b‖ ^ 2 ≤ inner ℝ a b := h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hinner : inner ℝ a (a - b) = ‖a‖ ^ 2 - inner ℝ a b := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    -- The same quadratic identity runs backwards to recover firm nonexpansiveness of `Id - T`.
    rw [hres]
    nlinarith [norm_sub_sq_real a b, hinner]

/-- Helper for Proposition 4.4: nonexpansiveness of the reflected map is equivalent to firm
nonexpansiveness of `T`. -/
lemma reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn (D : Set H) (T : D → H) :
    (∀ x y : D, ‖reflectedMap D T x - reflectedMap D T y‖ ≤ ‖(x : H) - y‖) ↔
      FirmlyNonexpansiveOn D T := by
  rw [firmlyNonexpansiveOn_iff]
  constructor
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : ‖reflectedMap D T x - reflectedMap D T y‖ ≤ ‖(x : H) - y‖ := h x y
    have hreflect : reflectedMap D T x - reflectedMap D T y = (2 : ℝ) • b - a := by
      calc
        reflectedMap D T x - reflectedMap D T y
            = ((2 : ℝ) • T x - (2 : ℝ) • T y) - ((x : H) - y) := by
                simp [reflectedMap]
                abel_nf
        _ = (2 : ℝ) • (T x - T y) - ((x : H) - y) := by rw [smul_sub]
        _ = (2 : ℝ) • b - a := by dsimp [a, b]
    have hsq : ‖(2 : ℝ) • b - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      rw [← hreflect]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hxy
    -- Lemma 2.17 turns the reflected norm gap into the firm inner-product inequality.
    nlinarith [reflection_norm_gap_eq_four_mul a b, hsq]
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : ‖b‖ ^ 2 ≤ inner ℝ a b := h x y
    have hreflect : reflectedMap D T x - reflectedMap D T y = (2 : ℝ) • b - a := by
      calc
        reflectedMap D T x - reflectedMap D T y
            = ((2 : ℝ) • T x - (2 : ℝ) • T y) - ((x : H) - y) := by
                simp [reflectedMap]
                abel_nf
        _ = (2 : ℝ) • (T x - T y) - ((x : H) - y) := by rw [smul_sub]
        _ = (2 : ℝ) • b - a := by dsimp [a, b]
    have hsq : ‖(2 : ℝ) • b - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      nlinarith [reflection_norm_gap_eq_four_mul a b, hxy]
    -- Squared norm control gives the original nonexpansive estimate because norms are nonnegative.
    rw [hreflect]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- Helper for Proposition 4.4: the residual cross-term condition is equivalent to firm
nonexpansiveness of `T`. -/
private lemma residual_cross_nonneg_iff_firmlyNonexpansiveOn (D : Set H) (T : D → H) :
    (∀ x y : D, 0 ≤ inner ℝ (T x - T y) (residualMap D T x - residualMap D T y)) ↔
      FirmlyNonexpansiveOn D T := by
  rw [firmlyNonexpansiveOn_iff]
  constructor
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : 0 ≤ inner ℝ (T x - T y) (residualMap D T x - residualMap D T y) := h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hinner : inner ℝ b (a - b) = inner ℝ a b - ‖b‖ ^ 2 := by
      rw [inner_sub_right, real_inner_comm b a, real_inner_self_eq_norm_sq]
    -- Expanding the residual inner product shows that clause (v) is exactly clause (iv).
    rw [hres] at hxy
    nlinarith [hinner]
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : ‖b‖ ^ 2 ≤ inner ℝ a b := h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hinner : inner ℝ b (a - b) = inner ℝ a b - ‖b‖ ^ 2 := by
      rw [inner_sub_right, real_inner_comm b a, real_inner_self_eq_norm_sq]
    -- The same identity turns the firm inequality back into the residual cross-term condition.
    rw [hres]
    nlinarith [hinner, hxy]

/-- Helper for Proposition 4.4: the residual cross-term sign condition is equivalent to the norm
lower bound along every segment joining `T x - T y` to `(x - y)`. -/
private lemma segment_norm_lower_bound_iff_residual_cross_nonneg (D : Set H) (T : D → H) :
    (∀ x y : D, 0 ≤ inner ℝ (T x - T y) (residualMap D T x - residualMap D T y)) ↔
      ∀ (x y : D) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
        ‖T x - T y‖ ≤ ‖α • ((x : H) - y) + (1 - α) • (T x - T y)‖ := by
  constructor
  · intro h x y α hα
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : 0 ≤ inner ℝ b (residualMap D T x - residualMap D T y) := by
      simpa [b] using h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hnonpos : inner ℝ b (b - a) ≤ 0 := by
      rw [hres] at hxy
      have hsum : inner ℝ b (a - b) + inner ℝ b (b - a) = 0 := by
        rw [← inner_add_right]
        abel_nf
        simp
      nlinarith
    have hβ : ‖b‖ ≤ ‖b - α • (b - a)‖ := by
      have hα_nonneg : 0 ≤ α := hα.1
      have hterm_nonneg : 0 ≤ α * (‖b - a‖ * ‖b - a‖) - 2 * inner ℝ b (b - a) := by
        have hnorm_nonneg : 0 ≤ ‖b - a‖ * ‖b - a‖ := by positivity
        nlinarith [hnonpos, hα_nonneg, hnorm_nonneg]
      have hfactor_nonneg : 0 ≤ α * (α * (‖b - a‖ * ‖b - a‖) - 2 * inner ℝ b (b - a)) := by
        exact mul_nonneg hα_nonneg hterm_nonneg
      have hsq : ‖b‖ * ‖b‖ ≤ ‖b - α • (b - a)‖ * ‖b - α • (b - a)‖ := by
        nlinarith [norm_sub_smul_defect_eq_factorized b (b - a) α, hfactor_nonneg]
      have hsq' : ‖b‖ ^ 2 ≤ ‖b - α • (b - a)‖ ^ 2 := by
        simpa [sq] using hsq
      exact le_of_sq_le_sq hsq' (norm_nonneg _)
    -- Rewrite the convex combination into `b - α • (b - a)`.
    simpa [a, b, segment_combination_eq_sub_smul] using hβ
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hsegment :
        ∀ β : Set.Icc (0 : ℝ) 1, ‖b‖ ≤ ‖b - (β : ℝ) • (b - a)‖ := by
      intro β
      have hβ := h x y (β : ℝ) β.2
      simpa [a, b, segment_combination_eq_sub_smul] using hβ
    have hnonpos : inner ℝ b (b - a) ≤ 0 :=
      inner_nonpos_of_unit_interval_sub_smul_norm_lower_bound b (b - a) hsegment
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    -- Rewriting `b - a = -(a - b)` recovers the residual cross-term formulation.
    rw [hres]
    have hsum : inner ℝ b (a - b) + inner ℝ b (b - a) = 0 := by
      rw [← inner_add_right]
      abel_nf
      simp
    nlinarith

-- Proof sketch: Rewrite each clause using the differences `x - y` and `T x - T y`, expand the
-- norms and inner products, and compare the resulting quadratic identities.
/-- Proposition 4.4: for an operator on a subset of a real Hilbert space, firm
nonexpansiveness, firm nonexpansiveness of `Id - T`, nonexpansiveness of `2T - Id`, and the
equivalent inequalities in (iv), (v), and (vi) form a TFAE list. -/
theorem firmlyNonexpansiveOn_tfae (D : Set H) (T : D → H) :
    List.TFAE
      [ FirmlyNonexpansiveOn D T,
        FirmlyNonexpansiveOn D (residualMap D T),
        ∀ x y : D, ‖reflectedMap D T x - reflectedMap D T y‖ ≤ ‖(x : H) - y‖,
        ∀ x y : D, ‖T x - T y‖ ^ 2 ≤ inner ℝ ((x : H) - y) (T x - T y),
        ∀ x y : D, 0 ≤ inner ℝ (T x - T y) (residualMap D T x - residualMap D T y),
        ∀ (x y : D) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
          ‖T x - T y‖ ≤ ‖α • ((x : H) - y) + (1 - α) • (T x - T y)‖ ] := by
  -- Clause (iv) is the common scalar inequality, so we connect each clause to it.
  tfae_have 1 ↔ 4 := firmlyNonexpansiveOn_iff D T
  tfae_have 1 ↔ 2 := (firmlyNonexpansiveOn_residualMap_iff D T).symm
  tfae_have 1 ↔ 3 := (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn D T).symm
  tfae_have 1 ↔ 5 := (residual_cross_nonneg_iff_firmlyNonexpansiveOn D T).symm
  -- The last equivalence is the interval-norm characterization from Lemma 2.13.
  tfae_have 5 ↔ 6 := segment_norm_lower_bound_iff_residual_cross_nonneg D T
  tfae_finish
