/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {μ : Measure Ω}

-- Proof sketch: apply the upcrossing-strategy argument to the positive-part process
-- `Y n ω = (X n ω - a)⁺`, obtain that `Y` is a submartingale from the owner API
-- `Submartingale.sub_martingale` and `Submartingale.pos`, and combine
-- `Submartingale.sum_mul_upcrossingStrat_le` with the identity
-- `μ[Y n - Y 0] = μ[Y n] - μ[Y 0]` to isolate the difference of positive-part expectations.
/-- Lemma 11.3: for a real-valued discrete submartingale, the expected number of upcrossings of the
interval `(a, b)` before time `n` is bounded by the increase of the expected positive part above
`a`, divided by `b - a`. -/
theorem submartingale_upcrossing_inequality [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ) {a b : ℝ} (hab : a < b) (n : ℕ) :
    μ[upcrossingsBefore a b X n] ≤
      (μ[fun ω ↦ (X n ω - a)⁺] - μ[fun ω ↦ (X 0 ω - a)⁺]) / (b - a) := by
  let Y : ℕ → Ω → ℝ := fun k ω ↦ (X k ω - a)⁺
  have hY : Submartingale Y ℱ μ := by
    simpa [Y] using (hX.sub_martingale (martingale_const ℱ μ a)).pos
  have hup :
      upcrossingsBefore 0 (b - a) Y n = upcrossingsBefore a b X n := by
    ext ω
    simpa [Y] using (upcrossingsBefore_pos_eq hab)
  have hmul :
      (b - a) * μ[upcrossingsBefore 0 (b - a) Y n] ≤
        μ[∑ k ∈ Finset.range n, upcrossingStrat 0 (b - a) Y n k * (Y (k + 1) - Y k)] := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ((hY.sum_upcrossingStrat_mul 0 (b - a) n).integrable n) ?_
    · exact Filter.Eventually.of_forall fun ω ↦
        mul_nonneg (sub_nonneg.2 hab.le) (Nat.cast_nonneg _)
    · filter_upwards with ω
      have hω : 0 ≤ Y n ω := by
        change 0 ≤ (X n ω - a)⁺
        exact posPart_nonneg _
      simpa using (mul_upcrossingsBefore_le hω (sub_pos.2 hab))
  have hsum :
      μ[∑ k ∈ Finset.range n, upcrossingStrat 0 (b - a) Y n k * (Y (k + 1) - Y k)] ≤
        μ[Y n] - μ[Y 0] := by
    simpa using hY.sum_mul_upcrossingStrat_le
  have hbound : (b - a) * μ[upcrossingsBefore a b X n] ≤ μ[Y n] - μ[Y 0] := by
    rw [← hup]
    exact hmul.trans hsum
  refine (le_div_iff₀ (sub_pos.2 hab)).2 ?_
  simpa [Y, mul_comm] using hbound
