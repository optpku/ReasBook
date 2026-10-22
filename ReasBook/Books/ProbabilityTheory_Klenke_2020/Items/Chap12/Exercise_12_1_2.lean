/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

-- Proof sketch: take the test functional `φ(x) = x 0` in the permutation-averaging formula for
-- conditional expectation on the `n`-exchangeable sigma-algebra. Then evaluate the resulting
-- average over `S(n)` explicitly: each of the first `n` coordinates appears equally often in the
-- orbit of the first coordinate, so the symmetrized average is the empirical mean of the first
-- `n` entries.
/-- Exercise 12.1.2: for an exchangeable real sequence, the conditional expectation of the first
coordinate with respect to the `n`-exchangeable sigma-algebra is the empirical mean of the first
`n` coordinates; this is the formal content of equation `(12.4)`. -/
theorem condExp_zero_eq_prefix_average_of_isExchangeable {X : ℕ → Ω → ℝ}
    [IsProbabilityMeasure μ] (hX : IsExchangeable X μ)
    (hX_meas : ∀ n, Measurable (X n)) (hX0 : Integrable (X 0) μ) (n : ℕ+) :
    μ[X 0 | nExchangeableSigmaAlgebra (Function.swap X) (n : ℕ)] =ᵐ[μ]
      fun ω ↦ (∑ i : Fin (n : ℕ), X i ω) / (n : ℝ) := by
  simpa [exchangeableAverage_apply_zero n, Function.comp, Function.swap] using
    condExp_eq_exchangeableAverage_of_isExchangeable hX hX_meas
      (measurable_pi_apply 0)
      (by simpa [Function.swap] using hX0)
      (n : ℕ)
