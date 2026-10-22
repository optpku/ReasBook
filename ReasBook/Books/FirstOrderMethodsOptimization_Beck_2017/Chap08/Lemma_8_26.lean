/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Interval

section

/- Lemma 8.26 is `source-facing`: it compares the integral of a nonincreasing real function on
adjacent unit intervals with the sum of its values at consecutive integers. The canonical owners
are `ContinuousOn`, `AntitoneOn`, interval integrals, and the integer interval `Finset.Icc`. -/

-- Proof sketch: on each unit interval `[k, k + 1]` with `k ∈ {a, …, b}`, antitonicity gives
-- `f (k + 1) ≤ f t ≤ f k`. Integrating over that interval and summing the resulting inequalities
-- yields the lower and upper bounds by the left- and right-shifted interval integrals.
/-- Lemma 8.26: if `f : [a - 1, b + 1] → ℝ` is continuous and nonincreasing on the real interval
with integer endpoints `a - 1` and `b + 1`, then the sum of its values at the integers
`a, a + 1, …, b` lies between the integrals over `[a, b + 1]` and `[a - 1, b]`. -/
theorem sum_integer_samples_bounds_intervalIntegrals_of_antitoneOn
    (f : ℝ → ℝ) (a b : ℤ) (hab : a ≤ b)
    (h_cont : ContinuousOn f (Set.Icc (((a - 1 : ℤ) : ℝ)) (((b + 1 : ℤ) : ℝ))))
    (h_anti : AntitoneOn f (Set.Icc (((a - 1 : ℤ) : ℝ)) (((b + 1 : ℤ) : ℝ)))) :
    ((∫ t in (a : ℝ)..(((b + 1 : ℤ) : ℝ)), f t) ≤
      Finset.sum (Finset.Icc a b) (fun k ↦ f (k : ℝ))) ∧
      (Finset.sum (Finset.Icc a b) (fun k ↦ f (k : ℝ)) ≤
        ∫ t in (((a - 1 : ℤ) : ℝ))..(b : ℝ), f t) := by
  -- Keep the continuity hypothesis explicit: it belongs to the textbook statement, even though
  -- the packaged antitone comparison lemmas below already supply the needed integrability.
  have _ := h_cont
  let n : ℕ := (b + 1 - a).toNat
  have h_nonneg : 0 ≤ b + 1 - a := by
    linarith
  have h_right : a + n = b + 1 := by
    dsimp [n]
    rw [← Int.toNat_of_nonneg h_nonneg]
    omega
  have h_left : a - 1 + n = b := by
    dsimp [n]
    rw [← Int.toNat_of_nonneg h_nonneg]
    omega
  have h_end_right : (a : ℝ) + n = ((b + 1 : ℤ) : ℝ) := by
    exact_mod_cast h_right
  have h_end_left : (((a - 1 : ℤ) : ℝ)) + n = (b : ℝ) := by
    exact_mod_cast h_left
  -- Reindex the integer sum to the `Finset.range n` shape expected by mathlib's comparison API.
  have h_sum_eq :
      Finset.sum (Finset.Icc a b) (fun k ↦ f (k : ℝ)) =
        Finset.sum (Finset.range n) (fun i ↦ f ((a + i : ℤ) : ℝ)) := by
    dsimp [n]
    rw [Int.Icc_eq_finset_map]
    rw [Finset.sum_map]
    rfl
  -- Restrict the global antitonicity to the two shifted windows used in the textbook proof.
  have h_left_window : AntitoneOn f (Set.Icc (a : ℝ) (((b + 1 : ℤ) : ℝ))) := by
    refine h_anti.mono ?_
    intro x hx
    refine ⟨?_, hx.2⟩
    exact le_trans (by norm_num) hx.1
  have h_right_window : AntitoneOn f (Set.Icc (((a - 1 : ℤ) : ℝ)) (b : ℝ)) := by
    refine h_anti.mono ?_
    intro x hx
    refine ⟨hx.1, ?_⟩
    exact le_trans hx.2 (by norm_num)
  have h_left_window' : AntitoneOn f (Set.Icc (a : ℝ) ((a : ℝ) + n)) := by
    rw [h_end_right]
    exact h_left_window
  have h_right_window' :
      AntitoneOn f (Set.Icc (((a - 1 : ℤ) : ℝ)) ((((a - 1 : ℤ) : ℝ)) + n)) := by
    rw [h_end_left]
    exact h_right_window
  constructor
  · -- On `[a, b + 1]`, the integral is bounded above by the sum of the left endpoint samples.
    calc
      (∫ t in (a : ℝ)..(((b + 1 : ℤ) : ℝ)), f t)
          = ∫ t in (a : ℝ)..((a : ℝ) + n), f t := by rw [h_end_right]
      _ ≤ Finset.sum (Finset.range n) (fun i ↦ f ((a : ℝ) + i)) := by
        exact h_left_window'.integral_le_sum
      _ = Finset.sum (Finset.range n) (fun i ↦ f ((a + i : ℤ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp
      _ = Finset.sum (Finset.Icc a b) (fun k ↦ f (k : ℝ)) := h_sum_eq.symm
  · -- On `[a - 1, b]`, the same comparison with right endpoints yields the reverse bound.
    calc
      Finset.sum (Finset.Icc a b) (fun k ↦ f (k : ℝ))
          = Finset.sum (Finset.range n) (fun i ↦ f ((a + i : ℤ) : ℝ)) := h_sum_eq
      _ = Finset.sum (Finset.range n) (fun i ↦ f ((((a - 1 : ℤ) : ℝ)) + (i + 1 : ℕ))) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
      _ ≤ ∫ t in (((a - 1 : ℤ) : ℝ))..((((a - 1 : ℤ) : ℝ)) + n), f t := by
        exact h_right_window'.sum_le_integral
      _ = ∫ t in (((a - 1 : ℤ) : ℝ))..(b : ℝ), f t := by rw [h_end_left]

end
