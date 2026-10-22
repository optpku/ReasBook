/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_46

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace ERealFunction

/-- Helper for Remark 9.47: under the supercoercive hypothesis from Example 9.32, the recession
value at a scalar is `0` exactly at the origin and `⊤` away from the origin. -/
private theorem recession_value_eq_if_eq_zero_of_supercoercive
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (hsuper :
      Filter.Tendsto (fun t : ℝ ↦ (φ t : EReal) / ‖t‖)
        (Filter.comap (fun t : ℝ ↦ ‖t‖) Filter.atTop) (nhds (⊤ : EReal)))
    (t : ℝ) :
    (recessionFunction φ hφ.2.nonempty t : EReal) = if t = 0 then 0 else ⊤ := by
  -- Evaluate Example 9.32 at the scalar `t` and then simplify the indicator of `{0}ᶜ`.
  have ht :=
    congrFun
      (recessionFunction_eq_indicator_singleton_zero_of_supercoercive
        (H := ℝ) (f := φ) hφ hsuper) t
  by_cases hzero : t = 0
  · subst hzero
    simpa using ht
  · simpa [Set.indicator, hzero] using ht

/-- Helper for Remark 9.47: a finite `EReal` sum avoids `-∞` when each summand does. -/
private theorem finset_sum_ne_bot_of_forall_ne_bot_local
    {ι : Type*} {s : Finset ι} {a : ι → EReal}
    (hbot : ∀ i ∈ s, a i ≠ ⊥) :
    s.sum a ≠ ⊥ := by
  classical
  -- Induct over the finite set and use the binary characterization of sums avoiding `⊥`.
  revert hbot
  refine Finset.induction_on s ?_ ?_
  · intro hbot
    simp
  · intro i s his ih hbot
    rw [Finset.sum_insert his, EReal.add_ne_bot_iff]
    constructor
    · exact hbot i (Finset.mem_insert_self i s)
    · exact ih (fun j hj ↦ hbot j (Finset.mem_insert_of_mem hj))

/-- Helper for Remark 9.47: one `⊤` summand forces the whole finite `EReal` sum to be `⊤`
provided the remaining summands stay away from `⊥`. -/
private theorem finset_sum_eq_top_of_mem_eq_top_local
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {a : ι → EReal} {i : ι}
    (hi : i ∈ s) (hai : a i = ⊤) (hbot : ∀ j ∈ s.erase i, a j ≠ ⊥) :
    s.sum a = ⊤ := by
  -- Isolate the distinguished `⊤` summand and collapse the remaining tail by `⊤ + b = ⊤`.
  calc
    s.sum a = a i + (s.erase i).sum a := by
      symm
      exact Finset.add_sum_erase s a hi
    _ = ⊤ + (s.erase i).sum a := by
      rw [hai]
    _ = ⊤ := by
      have hsum_ne_bot : (s.erase i).sum a ≠ ⊥ :=
        finset_sum_ne_bot_of_forall_ne_bot_local hbot
      simpa using EReal.top_add_of_ne_bot hsum_ne_bot

/-- Helper for Remark 9.47: the positive-coordinate perspective slice never contributes `-∞`. -/
private theorem positive_index_sum_ne_bot
    (N : ℕ) (φ : ℝ → Set.Ioi (⊥ : EReal)) (x y : Fin N → ℝ) :
    (∑ i ∈ coordinatePhiDivergencePositiveIndices y,
      (y i : EReal) * (φ (x i / y i) : EReal)) ≠ ⊥ := by
  -- Each summand is a product of two values that already avoid `⊥`.
  refine finset_sum_ne_bot_of_forall_ne_bot_local ?_
  intro i hi
  have hyi : 0 < y i := by
    simpa [coordinatePhiDivergencePositiveIndices] using hi
  rw [EReal.mul_ne_bot]
  refine ⟨Or.inl (EReal.coe_ne_bot (y i)), Or.inr (φ (x i / y i)).property.ne',
    Or.inl (EReal.coe_ne_top (y i)), Or.inl (EReal.coe_nonneg.mpr hyi.le)⟩

-- Proof sketch: start from `coordinatePhiDivergence_eq_textbook_formula`. Then apply
-- `recessionFunction_eq_indicator_singleton_zero_of_supercoercive` coordinatewise to the
-- zero-coordinate sum. That sum is `0` exactly when every zero coordinate of `y` also has
-- vanishing `x`-coordinate, and it is `+∞` as soon as one exceptional zero coordinate appears.
/-- Remark 9.47: if `φ ∈ Γ₀(ℝ)` is supercoercive, so `(φ t : EReal) / ‖t‖ → +∞` as `‖t‖ → +∞`,
then the finite-dimensional `φ`-divergence from Example 9.46 reduces to the sum of the positive
coordinate perspective terms when `y` has no negative coordinates and every zero coordinate of
`y` also has vanishing `x`-coordinate, and equals `+∞` otherwise. -/
theorem coordinatePhiDivergence_eq_reduced_formula_of_supercoercive
    (N : ℕ) (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (hsuper :
      Filter.Tendsto (fun t : ℝ ↦ (φ t : EReal) / ‖t‖)
        (Filter.comap (fun t : ℝ ↦ ‖t‖) Filter.atTop) (nhds (⊤ : EReal)))
    (x y : Fin N → ℝ) :
    (coordinatePhiDivergence N φ hφ.2.nonempty (x, y) : EReal) =
      if coordinatePhiDivergenceNegativeIndices y = ∅ ∧
          ∀ i ∈ coordinatePhiDivergenceZeroIndices y, x i = 0 then
        ∑ i ∈ coordinatePhiDivergencePositiveIndices y,
          (y i : EReal) * (φ (x i / y i) : EReal)
      else
        ⊤ := by
  classical
  -- Start from Example 9.46 so that only the zero-coordinate recession slice needs to be reduced.
  rw [coordinatePhiDivergence_eq_textbook_formula N φ hφ.2.nonempty x y]
  by_cases hneg : coordinatePhiDivergenceNegativeIndices y = ∅
  · rw [if_pos hneg]
    by_cases hall : ∀ i ∈ coordinatePhiDivergenceZeroIndices y, x i = 0
    · -- If every zero coordinate of `y` also has `x i = 0`, all recession terms vanish.
      have hzero_sum :
          (∑ i ∈ coordinatePhiDivergenceZeroIndices y,
            (recessionFunction φ hφ.2.nonempty (x i) : EReal)) = 0 := by
        -- Rewrite each recession term to the `if x i = 0 then 0 else ⊤` form and use `hall`.
        refine Finset.sum_eq_zero ?_
        intro i hi
        rw [recession_value_eq_if_eq_zero_of_supercoercive φ hφ hsuper]
        simp [hall i hi]
      -- After the zero slice disappears, the reduced formula is exactly the positive slice.
      rw [if_pos ⟨hneg, hall⟩, hzero_sum, zero_add]
    · -- If one zero coordinate carries a nonzero `x`-coordinate, the zero slice already equals
      -- `⊤`, so the whole divergence is `⊤`.
      have hex :
          ∃ i, i ∈ coordinatePhiDivergenceZeroIndices y ∧ x i ≠ 0 := by
        by_contra hno
        apply hall
        intro j hj
        by_contra hxj
        exact hno ⟨j, hj, hxj⟩
      rcases hex with ⟨i, hi, hxi⟩
      have hzero_term_top :
          (recessionFunction φ hφ.2.nonempty (x i) : EReal) = ⊤ := by
        rw [recession_value_eq_if_eq_zero_of_supercoercive φ hφ hsuper]
        simp [hxi]
      have hzero_tail_ne_bot :
          ∀ j ∈ (coordinatePhiDivergenceZeroIndices y).erase i,
            (recessionFunction φ hφ.2.nonempty (x j) : EReal) ≠ ⊥ := by
        intro j hj
        rw [recession_value_eq_if_eq_zero_of_supercoercive φ hφ hsuper]
        by_cases hxj : x j = 0 <;> simp [hxj]
      have hzero_sum_top :
          (∑ j ∈ coordinatePhiDivergenceZeroIndices y,
            (recessionFunction φ hφ.2.nonempty (x j) : EReal)) = ⊤ := by
        -- The witness `i` contributes `⊤`, and every other recession term avoids `⊥`.
        simpa using
          (finset_sum_eq_top_of_mem_eq_top_local
            (s := coordinatePhiDivergenceZeroIndices y)
            (a := fun j ↦ (recessionFunction φ hφ.2.nonempty (x j) : EReal))
            (i := i) hi hzero_term_top hzero_tail_ne_bot)
      have hpositive_ne_bot :
          (∑ i ∈ coordinatePhiDivergencePositiveIndices y,
            (y i : EReal) * (φ (x i / y i) : EReal)) ≠ ⊥ :=
        positive_index_sum_ne_bot N φ x y
      have hreduced_false :
          ¬ (coordinatePhiDivergenceNegativeIndices y = ∅ ∧
            ∀ i ∈ coordinatePhiDivergenceZeroIndices y, x i = 0) := by
        intro h
        exact hall h.2
      -- The reduced branch is impossible here, and the explicit formula stays at `⊤`.
      rw [if_neg hreduced_false, hzero_sum_top]
      simpa using EReal.top_add_of_ne_bot hpositive_ne_bot
  · -- Once a negative coordinate is present, Example 9.46 already yields the `⊤` branch.
    have hreduced_false :
        ¬ (coordinatePhiDivergenceNegativeIndices y = ∅ ∧
          ∀ i ∈ coordinatePhiDivergenceZeroIndices y, x i = 0) := by
      intro h
      exact hneg h.1
    rw [if_neg hneg, if_neg hreduced_false]

end ERealFunction
