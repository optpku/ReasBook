/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Metric

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 4.18 is `source-facing` in the chapter norm-conjugacy API. The owner abstractions
already live upstream: Chapter 2 owns the indicator function `extendedIndicator`, and the
continuous-dual Fenchel conjugate on normed spaces is already present upstream in Chapter 4 as
`conjugate_function`. The primitive data here are therefore only the norm objective and the dual
closed unit ball; the proposition itself is the source-facing identification between those owner
objects. -/
recall extendedIndicator
recall conjugate_function
recall conjugate_function_apply

-- Proof sketch: if `‖y‖ ≤ 1`, the dual norm inequality gives `y x ≤ ‖y‖ * ‖x‖ ≤ ‖x‖`, so every
-- term `y x - ‖x‖` is at most `0`, and equality is attained at `x = 0`. If `‖y‖ > 1`, apply
-- Hahn-Banach to choose a unit vector on which `y` is arbitrarily close to its norm, then scale
-- along that direction to make `y x - ‖x‖` diverge to `∞`.
/-- Helper for Proposition 4.18: if `‖y‖ ≤ 1`, then the defining supremum for the conjugate of
`x ↦ ‖x‖` is bounded above by `0` and attained at `x = 0`. -/
lemma normConjugate_eq_zero_of_norm_le_one
    {y : StrongDual ℝ E} (hy : ‖y‖ ≤ 1) :
    conjugate_function (fun x : E ↦ (‖x‖ : EReal)) y = 0 := by
  -- Rewrite the conjugate into its defining supremum.
  rw [conjugate_function_apply]
  refine le_antisymm ?_ ?_
  · -- The dual norm inequality bounds every term in the range by `0`.
    refine sSup_le ?_
    rintro z ⟨x, rfl⟩
    have hyx_le : y x ≤ ‖x‖ := by
      calc
        y x ≤ ‖y x‖ := le_abs_self _
        _ ≤ ‖y‖ * ‖x‖ := ContinuousLinearMap.le_opNorm y x
        _ ≤ 1 * ‖x‖ := by
          gcongr
        _ = ‖x‖ := by ring
    change (((y x - ‖x‖ : ℝ) : EReal) ≤ 0)
    exact_mod_cast sub_nonpos.mpr hyx_le
  · -- Evaluating at the origin shows that the supremum is at least `0`.
    refine le_sSup ?_
    refine Set.mem_range.mpr ⟨0, ?_⟩
    simp

/-- Helper for Proposition 4.18: if `‖y‖ > 1`, then some vector gives a positive gap
`y x - ‖x‖`. -/
lemma exists_eval_sub_norm_pos_of_one_lt_norm
    {y : StrongDual ℝ E} (hy : 1 < ‖y‖) :
    ∃ x : E, 0 < y x - ‖x‖ := by
  -- Choose a point where the functional grows faster than the unit slope `‖x‖`.
  rcases y.exists_mul_lt_of_lt_opNorm (by positivity : 0 ≤ (1 : ℝ)) hy with ⟨x, hx⟩
  have hx' : ‖x‖ < ‖y x‖ := by simpa using hx
  by_cases hsign : 0 ≤ y x
  · -- In the nonnegative case, `|y x| = y x`, so the gap is already positive.
    refine ⟨x, ?_⟩
    calc
      0 < ‖y x‖ - ‖x‖ := sub_pos.mpr hx'
      _ = y x - ‖x‖ := by rw [Real.norm_of_nonneg hsign]
  · -- Otherwise replace `x` by `-x` so that the evaluation becomes positive.
    refine ⟨-x, ?_⟩
    have hneg : y x < 0 := lt_of_not_ge hsign
    calc
      0 < ‖y x‖ - ‖x‖ := sub_pos.mpr hx'
      _ = (-y x) - ‖x‖ := by rw [Real.norm_eq_abs, abs_of_neg hneg]
      _ = y (-x) - ‖-x‖ := by simp

/-- Helper for Proposition 4.18: along the ray `((n : ℝ) • x)`, the conjugate integrand is the
real scalar `n * (y x - ‖x‖)` viewed in `EReal`. -/
lemma normConjugateIntegrand_natSmul
    (y : StrongDual ℝ E) (x : E) (n : ℕ) :
    (y ((n : ℝ) • x) : EReal) - ‖(n : ℝ) • x‖ =
      ((((n : ℝ) * (y x - ‖x‖)) : ℝ) : EReal) := by
  -- Rewrite both the pairing and the norm on the ray into the same real normal form.
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hreal :
      y ((n : ℝ) • x) - ‖(n : ℝ) • x‖ = (n : ℝ) * (y x - ‖x‖) := by
    rw [map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg hn]
    ring
  exact_mod_cast hreal

/-- Helper for Proposition 4.18: if `‖y‖ > 1`, then the defining supremum for the conjugate of
`x ↦ ‖x‖` is unbounded above and therefore equals `⊤`. -/
lemma normConjugate_eq_top_of_one_lt_norm
    {y : StrongDual ℝ E} (hy : 1 < ‖y‖) :
    conjugate_function (fun x : E ↦ (‖x‖ : EReal)) y = ⊤ := by
  -- Rewrite the conjugate into its defining supremum and then show the range is unbounded above.
  rw [conjugate_function_apply]
  rcases exists_eval_sub_norm_pos_of_one_lt_norm hy with ⟨x, hx⟩
  let δ : ℝ := y x - ‖x‖
  have hδ : 0 < δ := hx
  refine (sSup_eq_top).2 ?_
  intro b hb
  -- Pass from the finite `EReal` threshold `b` to a real threshold and outrun it along a ray.
  rcases EReal.lt_iff_exists_real_btwn.1 hb with ⟨r, hbr, _⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (r / δ)
  have hr_lt_scaled : r < (n : ℝ) * δ := by
    have hn' : r / δ < (n : ℝ) := by exact_mod_cast hn
    exact (div_lt_iff₀ hδ).1 hn'
  refine ⟨_, Set.mem_range.mpr ⟨(n : ℝ) • x, rfl⟩, ?_⟩
  calc
    b < (r : EReal) := hbr
    _ < (((n : ℝ) * δ : ℝ) : EReal) := by exact_mod_cast hr_lt_scaled
    _ = (y ((n : ℝ) • x) : EReal) - ‖(n : ℝ) • x‖ := by
      simpa [δ] using (normConjugateIntegrand_natSmul y x n).symm

/-- Proposition 4.18: the Fenchel conjugate of the norm `x ↦ ‖x‖` is the extended-real-valued
indicator of the closed unit ball in the dual space. -/
theorem norm_conjugate_eq_extendedIndicator_closedBall
    :
    (fun y : StrongDual ℝ E ↦ conjugate_function (fun x : E ↦ (‖x‖ : EReal)) y) =
      δ_ (closedBall (0 : StrongDual ℝ E) 1) := by
  funext y
  by_cases hy : ‖y‖ ≤ 1
  · -- On the closed unit ball, the conjugate is `0`, matching the indicator value.
    have hmem : y ∈ closedBall (0 : StrongDual ℝ E) 1 :=
      mem_closedBall_zero_iff.mpr hy
    rw [normConjugate_eq_zero_of_norm_le_one hy, extendedIndicator_of_mem hmem]
  · -- Outside the closed unit ball, the conjugate is `⊤`, again matching the indicator.
    have hy' : 1 < ‖y‖ := lt_of_not_ge hy
    have hnot_mem : y ∉ closedBall (0 : StrongDual ℝ E) 1 := by
      simpa [mem_closedBall_zero_iff] using hy
    rw [normConjugate_eq_top_of_one_lt_norm hy', extendedIndicator_of_not_mem hnot_mem]

/-- Pointwise form of Proposition 4.18 on the continuous-dual bridge from
`conjugate_function`. -/
theorem norm_conjugate_apply_eq_extendedIndicator_closedBall
    (y : StrongDual ℝ E) :
    conjugate_function (fun x : E ↦ (‖x‖ : EReal)) y =
      (δ_ (closedBall (0 : StrongDual ℝ E) 1)) y := by
  simpa using congrArg (fun f : StrongDual ℝ E → EReal ↦ f y)
    norm_conjugate_eq_extendedIndicator_closedBall

-- Proof sketch: combine
-- `norm_conjugate_apply_eq_extendedIndicator_closedBall` with the defining behavior of `δ_ C`,
-- then rewrite membership in the closed ball centered at `0` as the norm inequality `‖y‖ ≤ 1`.
/-- The conjugate of the norm is `0` on the dual closed unit ball and `∞` outside it. -/
theorem norm_conjugate_eq_if_norm_le_one
    (y : StrongDual ℝ E) :
    conjugate_function (fun x : E ↦ (‖x‖ : EReal)) y =
      if ‖y‖ ≤ 1 then (0 : EReal) else ⊤ := by
  rw [norm_conjugate_apply_eq_extendedIndicator_closedBall]
  by_cases hy : ‖y‖ ≤ 1
  · have hmem : y ∈ closedBall (0 : StrongDual ℝ E) 1 :=
      mem_closedBall_zero_iff.mpr hy
    simp [hmem, hy]
  · have hnot_mem : y ∉ closedBall (0 : StrongDual ℝ E) 1 := by
      simpa [mem_closedBall_zero_iff] using hy
    simp [hnot_mem, hy]

end
