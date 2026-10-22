/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_37

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

-- Proof sketch: for each time `n`, every summand with `k < n` is `ℱ n`-measurable because
-- `H (k + 1)` is `ℱ k`-measurable by predictability and hence `ℱ n`-measurable by monotonicity,
-- while both `X (k + 1)` and `X k` are `ℱ n`-measurable by adaptedness. Finite sums preserve
-- measurability.
/-- Remark 9.38: the discrete stochastic integral `H · X` of a predictable real-valued process
`H` against an adapted real-valued process `X` is itself adapted to the filtration `ℱ`. -/
theorem stochasticIntegral_adapted {ℱ : Filtration ℕ mΩ} {H X : ℕ → Ω → ℝ}
    (hH : IsPredictable ℱ H) (hX : Adapted ℱ X) :
    Adapted ℱ (stochasticIntegral H X) := by
  intro n
  change Measurable[ℱ n] (fun ω ↦ ∑ k ∈ Finset.range n, H (k + 1) ω * (X (k + 1) ω - X k ω))
  refine Finset.measurable_sum _ fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  exact ((hH.measurable_add_one k).mono (ℱ.mono hk.le) (by rfl)).mul
    ((hX.measurable_le (Nat.succ_le_of_lt hk)).sub (hX.measurable_le hk.le))

end ProbabilityTheory
