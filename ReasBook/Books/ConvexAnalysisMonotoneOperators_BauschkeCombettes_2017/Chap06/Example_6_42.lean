/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

section

variable {N : ℕ}

local notation "E" => PiLp 2 fun _ : Fin N ↦ ℝ
/-- Helper for Example 6.42: the translated support inequality at `x` is equivalent to the
pointwise variational inequality against every point of the original set. -/
private lemma innerSupremumOn_sub_singleton_le_zero_iff {C : Set E} {u p : E} :
    innerSupremumOn (C - ({p} : Set E)) u ≤ 0 ↔ ∀ z ∈ C, ⟪z - p, u⟫_ℝ ≤ 0 := by
  constructor
  · intro hsup z hz
    -- Compare the translate `C - {p}` against `{0}` to recover the pointwise inequalities.
    have hsep :
        innerSupremumOn (C - ({p} : Set E)) u ≤ innerInfimumOn ({0} : Set E) u := by
      simpa using hsup
    have hinner :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set E)) ({0} : Set E) u).1 hsep
    have hz_sub : z - p ∈ C - ({p} : Set E) := by
      exact ⟨z, hz, p, by simp, rfl⟩
    simpa using hinner (z - p) hz_sub 0 (by simp)
  · intro hinner
    -- Every element of `C - {p}` is a difference `z - p`, so the pointwise family implies the
    -- defining support bound.
    have hsep :
        innerSupremumOn (C - ({p} : Set E)) u ≤ innerInfimumOn ({0} : Set E) u :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set E)) ({0} : Set E) u).2
        (fun v hv w hw ↦ by
          have hw0 : w = 0 := by simpa using hw
          subst hw0
          rcases hv with ⟨z, hz, q, hq, hv⟩
          have hq' : q = p := by simpa using hq
          have hv' : v = z - p := by
            simpa [hq'] using hv.symm
          simpa [hv'] using hinner z hz)
    simpa using hsep

/-- Helper for Example 6.42: the variational inequality on the positive orthant is equivalent to
the coordinatewise sign and complementary-slackness conditions. -/
private lemma positive_orthant_translate_inner_nonpos_iff {x y : E}
    (hx : x ∈ ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E)) :
    (∀ z ∈ ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E), ⟪z - x, y⟫_ℝ ≤ 0) ↔
      ∀ i : Fin N, (x i = 0 → y i ≤ 0) ∧ (0 < x i → y i = 0) := by
  constructor
  · intro hvar i
    -- Test the variational inequality on the `i`-th positive coordinate direction.
    have hy_nonpos : y i ≤ 0 := by
      have hz_plus : x + (PiLp.single 2 i (1 : ℝ) : E) ∈ ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E) := by
        intro j
        by_cases hji : j = i
        · subst j
          have hxi_nonneg : 0 ≤ x i := hx i
          simpa [PiLp.single_apply] using add_nonneg hxi_nonneg zero_le_one
        · simpa [PiLp.single_apply, hji] using hx j
      have hprobe := hvar (x + (PiLp.single 2 i (1 : ℝ) : E)) hz_plus
      have hinner :
          ⟪(x + (PiLp.single 2 i (1 : ℝ) : E)) - x, y⟫_ℝ = y i := by
        calc
          ⟪(x + (PiLp.single 2 i (1 : ℝ) : E)) - x, y⟫_ℝ
              = ⟪(PiLp.single 2 i (1 : ℝ) : E), y⟫_ℝ := by
                  congr 1
                  ext j
                  by_cases hji : j = i
                  · subst j
                    simp
                  · simp [hji]
          _ = y i := by
            simpa using
              (EuclideanSpace.inner_single_left (𝕜 := ℝ) (ι := Fin N) i (1 : ℝ) y)
      calc
        y i = ⟪(x + (PiLp.single 2 i (1 : ℝ) : E)) - x, y⟫_ℝ := hinner.symm
        _ ≤ 0 := hprobe
    constructor
    · intro _
      exact hy_nonpos
    · intro hxi_pos
      -- Clear the `i`-th coordinate to force the complementary-slackness equality.
      have hz_clear : x - (PiLp.single 2 i (x i) : E) ∈ ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E) := by
        intro j
        by_cases hji : j = i
        · subst j
          simp
        · simpa [PiLp.single_apply, hji] using hx j
      have hprobe := hvar (x - (PiLp.single 2 i (x i) : E)) hz_clear
      have hsingle_neg : ⟪-(PiLp.single 2 i (x i) : E), y⟫_ℝ = -(x i * y i) := by
        rw [inner_neg_left]
        simpa using congrArg Neg.neg
          (EuclideanSpace.inner_single_left (𝕜 := ℝ) (ι := Fin N) i (x i) y)
      have hmul : -(x i * y i) ≤ 0 := by
        calc
          -(x i * y i) = ⟪(x - (PiLp.single 2 i (x i) : E)) - x, y⟫_ℝ := by
            calc
              -(x i * y i) = ⟪-(PiLp.single 2 i (x i) : E), y⟫_ℝ := hsingle_neg.symm
              _ = ⟪(x - (PiLp.single 2 i (x i) : E)) - x, y⟫_ℝ := by
                congr 1
                ext j
                by_cases hji : j = i
                · subst j
                  simp
                · simp [hji]
          _ ≤ 0 := hprobe
      nlinarith
  · intro hcoord z hz
    -- Expand the inner product as a finite sum and estimate each coordinate separately.
    rw [PiLp.inner_apply]
    refine Finset.sum_nonpos fun i _ ↦ ?_
    by_cases hxi0 : x i = 0
    · have hz_sub_nonneg : 0 ≤ z i - x i := by
        simpa [hxi0] using hz i
      have hy_nonpos : y i ≤ 0 := (hcoord i).1 hxi0
      have hmul : (z i - x i) * y i ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hz_sub_nonneg hy_nonpos
      have hmul' : y i * (z i - x i) ≤ 0 := by
        simpa [mul_comm] using hmul
      simpa using hmul'
    · have hxi_pos : 0 < x i := by
        exact lt_of_le_of_ne (hx i) (by simpa [eq_comm] using hxi0)
      have hy_zero : y i = 0 := (hcoord i).2 hxi_pos
      simp [hy_zero]

/-- Helper for Example 6.42: the variational inequality on the negative orthant is equivalent to
the coordinatewise sign and complementary-slackness conditions. -/
private lemma negative_orthant_translate_inner_nonpos_iff {x y : E}
    (hx : x ∈ ({ξ : E | ∀ i, ξ i ≤ 0} : Set E)) :
    (∀ z ∈ ({ξ : E | ∀ i, ξ i ≤ 0} : Set E), ⟪z - x, y⟫_ℝ ≤ 0) ↔
      ∀ i : Fin N, (x i = 0 → 0 ≤ y i) ∧ (x i < 0 → y i = 0) := by
  constructor
  · intro hvar i
    -- Test the variational inequality on the `i`-th negative coordinate direction.
    have hy_nonneg : 0 ≤ y i := by
      have hz_minus : x - (PiLp.single 2 i (1 : ℝ) : E) ∈ ({ξ : E | ∀ i, ξ i ≤ 0} : Set E) := by
        intro j
        by_cases hji : j = i
        · subst j
          have hxi_nonpos : x i ≤ 0 := hx i
          have : x i - 1 ≤ 0 := by
            linarith
          simpa [PiLp.single_apply] using this
        · simpa [PiLp.single_apply, hji] using hx j
      have hprobe := hvar (x - (PiLp.single 2 i (1 : ℝ) : E)) hz_minus
      have hsingle_neg : ⟪-(PiLp.single 2 i (1 : ℝ) : E), y⟫_ℝ = -y i := by
        rw [inner_neg_left]
        simpa using congrArg Neg.neg
          (EuclideanSpace.inner_single_left (𝕜 := ℝ) (ι := Fin N) i (1 : ℝ) y)
      have hminus : -y i ≤ 0 := by
        calc
          -y i = ⟪(x - (PiLp.single 2 i (1 : ℝ) : E)) - x, y⟫_ℝ := by
            calc
              -y i = ⟪-(PiLp.single 2 i (1 : ℝ) : E), y⟫_ℝ := hsingle_neg.symm
              _ = ⟪(x - (PiLp.single 2 i (1 : ℝ) : E)) - x, y⟫_ℝ := by
                congr 1
                ext j
                by_cases hji : j = i
                · subst j
                  simp
                · simp [hji]
          _ ≤ 0 := hprobe
      linarith
    constructor
    · intro _
      exact hy_nonneg
    · intro hxi_neg
      -- Clear the `i`-th coordinate to force the complementary-slackness equality.
      have hz_clear : x - (PiLp.single 2 i (x i) : E) ∈ ({ξ : E | ∀ i, ξ i ≤ 0} : Set E) := by
        intro j
        by_cases hji : j = i
        · subst j
          simp
        · simpa [PiLp.single_apply, hji] using hx j
      have hprobe := hvar (x - (PiLp.single 2 i (x i) : E)) hz_clear
      have hsingle_neg : ⟪-(PiLp.single 2 i (x i) : E), y⟫_ℝ = -(x i * y i) := by
        rw [inner_neg_left]
        simpa using congrArg Neg.neg
          (EuclideanSpace.inner_single_left (𝕜 := ℝ) (ι := Fin N) i (x i) y)
      have hmul : -(x i * y i) ≤ 0 := by
        calc
          -(x i * y i) = ⟪(x - (PiLp.single 2 i (x i) : E)) - x, y⟫_ℝ := by
            calc
              -(x i * y i) = ⟪-(PiLp.single 2 i (x i) : E), y⟫_ℝ := hsingle_neg.symm
              _ = ⟪(x - (PiLp.single 2 i (x i) : E)) - x, y⟫_ℝ := by
                congr 1
                ext j
                by_cases hji : j = i
                · subst j
                  simp
                · simp [hji]
          _ ≤ 0 := hprobe
      nlinarith
  · intro hcoord z hz
    -- Expand the inner product as a finite sum and estimate each coordinate separately.
    rw [PiLp.inner_apply]
    refine Finset.sum_nonpos fun i _ ↦ ?_
    by_cases hxi0 : x i = 0
    · have hz_sub_nonpos : z i - x i ≤ 0 := by
        simpa [hxi0] using hz i
      have hy_nonneg : 0 ≤ y i := (hcoord i).1 hxi0
      have hmul : (z i - x i) * y i ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hz_sub_nonpos hy_nonneg
      have hmul' : y i * (z i - x i) ≤ 0 := by
        simpa [mul_comm] using hmul
      simpa using hmul'
    · have hxi_neg : x i < 0 := by
        exact lt_of_le_of_ne (hx i) hxi0
      have hy_zero : y i = 0 := (hcoord i).2 hxi_neg
      simp [hy_zero]

-- Proof sketch: unfold `Set.normalCone` for the coordinatewise nonnegative orthant, rewrite
-- membership in the translated orthant coordinatewise, and identify the nonpositive inner-product condition
-- with the stated complementary-slackness inequalities on each coordinate.
/-- Example 6.42 (1): at a point of the positive orthant in `ℝ^N`, membership in the normal cone
is equivalent to having nonpositive coordinates where `x` vanishes and zero coordinates where `x`
is strictly positive. -/
theorem mem_normalCone_positiveOrthant_iff {x y : E}
    (hx : x ∈ ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E)) :
    y ∈ Set.normalCone ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E) x ↔
      ∀ i : Fin N, (x i = 0 → y i ≤ 0) ∧ (0 < x i → y i = 0) := by
  -- Rewrite normal-cone membership as the translated support inequality from Definition 6.38.
  rw [Set.normalCone_of_mem hx]
  -- Identify that translated inequality with the coordinatewise complementary-slackness conditions.
  exact
    (innerSupremumOn_sub_singleton_le_zero_iff
      (C := ({ξ : E | ∀ i, 0 ≤ ξ i} : Set E)) (u := y) (p := x)).trans
      (positive_orthant_translate_inner_nonpos_iff (x := x) (y := y) hx)

-- Proof sketch: unfold `Set.normalCone` for the negative orthant, rewrite membership
-- in the translated orthant coordinatewise, and identify the nonpositive inner-product condition
-- with the stated sign conditions on each coordinate.
/-- Example 6.42 (2): at a point of the negative orthant in `ℝ^N`, membership in the normal cone
is equivalent to having nonnegative coordinates where `x` vanishes and zero coordinates where `x`
is strictly negative. -/
theorem mem_normalCone_negativeOrthant_iff {x y : E}
    (hx : x ∈ ({ξ : E | ∀ i, ξ i ≤ 0} : Set E)) :
    y ∈ Set.normalCone ({ξ : E | ∀ i, ξ i ≤ 0} : Set E) x ↔
      ∀ i : Fin N, (x i = 0 → 0 ≤ y i) ∧ (x i < 0 → y i = 0) := by
  -- Rewrite normal-cone membership as the translated support inequality from Definition 6.38.
  rw [Set.normalCone_of_mem hx]
  -- Identify that translated inequality with the coordinatewise sign conditions.
  exact
    (innerSupremumOn_sub_singleton_le_zero_iff
      (C := ({ξ : E | ∀ i, ξ i ≤ 0} : Set E)) (u := y) (p := x)).trans
      (negative_orthant_translate_inner_nonpos_iff (x := x) (y := y) hx)

end
