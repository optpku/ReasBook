/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Proposition 9.6: Jensen convexity sends every strict convex combination with a
`-∞` endpoint to `-∞`. -/
lemma strict_convex_combination_eq_bot_of_isConvex {f : H → EReal} (hf : IsConvex f)
    {x y : H} (hx : f x = ⊥) {a : ℝ} (ha : 0 < a) (ha_lt_one : a < 1) :
    f (a • x + (1 - a) • y) = ⊥ := by
  -- The convex upper bound already collapses to `⊥` because the positive weight multiplies `⊥`.
  have haE : 0 < (a : EReal) := EReal.coe_pos.mpr ha
  apply le_bot_iff.mp
  calc
    f (a • x + (1 - a) • y)
        ≤ (a : EReal) * f x + (1 - a : EReal) * f y := hf ha.le ha_lt_one.le
    _ = ⊥ := by simp [hx, EReal.mul_bot_of_pos haE]

/-- Helper for Proposition 9.6: the reciprocal convex combinations converge to the right endpoint.
-/
lemma tendsto_reciprocal_convex_combination_to_right (x y : H) :
    Tendsto (fun n : ℕ ↦ (1 / (n + 2 : ℝ)) • x + (1 - 1 / (n + 2 : ℝ)) • y) atTop (nhds y) := by
  -- Rewrite the segment as `y + α_n • (x - y)` so the scalar factor tends to `0`.
  have hbase : Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ)) : ℕ → ℝ) atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hshift : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have hrecip : Tendsto (fun n : ℕ ↦ (1 / (n + 2 : ℝ)) : ℕ → ℝ) atTop (nhds 0) := by
    convert (hbase.comp hshift) using 1
    ext n
    simp [Function.comp]
    ring
  have hzero :
      Tendsto (fun n : ℕ ↦ ((1 / (n + 2 : ℝ)) : ℝ) • (x - y)) atTop
        (nhds ((0 : ℝ) • (x - y))) := by
    exact Filter.Tendsto.smul_const hrecip (x - y)
  have hy : Tendsto (fun _ : ℕ ↦ y) atTop (nhds y) := tendsto_const_nhds
  have hadd :
      Tendsto (fun n : ℕ ↦ y + ((1 / (n + 2 : ℝ)) : ℝ) • (x - y)) atTop
        (nhds (y + (0 : ℝ) • (x - y))) :=
    hy.add hzero
  convert hadd using 1
  · ext n
    calc
      (1 / (n + 2 : ℝ)) • x + (1 - 1 / (n + 2 : ℝ)) • y
          = (1 / (n + 2 : ℝ)) • x + (y - (1 / (n + 2 : ℝ)) • y) := by
              rw [sub_smul, one_smul]
      _ = y + ((1 / (n + 2 : ℝ)) • x - (1 / (n + 2 : ℝ)) • y) := by abel
      _ = y + (1 / (n + 2 : ℝ)) • (x - y) := by rw [smul_sub]
  · simp

/-- Helper for Proposition 9.6: lower semicontinuity turns the constant `-∞` values on the
approaching segment into the endpoint value `-∞`. -/
lemma eq_bot_of_mem_gamma_of_eq_bot {f : H → EReal} (hf : f ∈ gamma H) {x y : H}
    (hx : f x = ⊥) :
    f y = ⊥ := by
  -- Unpack `Γ(ℋ)` into Jensen convexity and the sequential lower-semicontinuity criterion.
  rcases (mem_gamma_iff_seq_tendsto_le_liminf f).mp hf with ⟨hconv, hseq⟩
  let u : ℕ → H := fun n ↦ (1 / (n + 2 : ℝ)) • x + (1 - 1 / (n + 2 : ℝ)) • y
  have hu : Tendsto u atTop (nhds y) :=
    tendsto_reciprocal_convex_combination_to_right x y
  have hu_bot : ∀ n : ℕ, f (u n) = ⊥ := by
    -- Each strict convex combination on the segment still has value `-∞`.
    intro n
    refine strict_convex_combination_eq_bot_of_isConvex hconv hx ?_ ?_
    · exact one_div_pos.mpr (by positivity : (0 : ℝ) < n + 2)
    · have h : 1 / (n + 2 : ℝ) < 1 / (1 : ℝ) := by
        refine (one_div_lt_one_div (α := ℝ) ?_ ?_).2 ?_
        · positivity
        · norm_num
        · exact_mod_cast Nat.succ_lt_succ (Nat.succ_pos n)
      simpa using h
  have hliminf : f y ≤ liminf (f ∘ u) atTop := hseq hu
  have hconst : (f ∘ u) = fun _ : ℕ ↦ (⊥ : EReal) := by
    -- The source proof's segment values form the constant `-∞` sequence.
    funext n
    exact hu_bot n
  rw [hconst, Filter.liminf_const] at hliminf
  exact le_bot_iff.mp hliminf

-- Proof sketch: unpack `hf` into convexity and lower semicontinuity. For any `y`, if `f y ≠ ⊤`,
-- Proposition 8.4 applied along the segment from `x` to `y` shows that
-- `f (α • x + (1 - α) • y) = ⊥` for every `0 < α < 1`. Letting `α ↓ 0`, lower semicontinuity at
-- `y` forces `f y ≤ ⊥`, hence `f y = ⊥`; otherwise `f y = ⊤`.
/-- Proposition 9.6: if a function in `Γ(ℋ)` takes the value `-∞` at some point, then it is
nowhere real-valued: every value is either `-∞` or `+∞`. -/
theorem eq_bot_or_eq_top_of_mem_gamma_of_eq_bot {f : H → EReal} (hf : f ∈ gamma H) {x : H}
    (hx : f x = ⊥) (y : H) :
    f y = ⊥ ∨ f y = ⊤ := by
  by_cases hytop : f y = ⊤
  · -- This is the textbook's trivial branch.
    exact Or.inr hytop
  · -- Otherwise lower semicontinuity forces the endpoint value down to `-∞`.
    exact Or.inl (eq_bot_of_mem_gamma_of_eq_bot hf hx)

end ERealFunction
