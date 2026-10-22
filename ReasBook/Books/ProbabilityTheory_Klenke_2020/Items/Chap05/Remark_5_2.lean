/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {X Y : Ω → ℝ}

-- Proof sketch: use `MemLp.mono_exponent` to lower the exponent from `n` to `k`, then apply
-- `MemLp.integrable_norm_pow'` and rewrite the real norm as the absolute value.
/-- Remark 5.2 (1): on a finite measure space, if `X ∈ L^n`, then every absolute moment of order
`k ≤ n` is finite. In particular, the textbook probability-space clause for `1 ≤ k ≤ n` is a
special case, giving the finiteness behind the notation `M_k`. -/
theorem integrable_abs_pow_of_memLp {n k : ℕ} (hX : MemLp X n μ) (hkn : k ≤ n) :
    Integrable (fun ω ↦ |X ω| ^ k) μ := by
  simpa [Real.norm_eq_abs] using
    (hX.mono_exponent (by exact_mod_cast hkn)).integrable_norm_pow'

section Probability

variable [IsProbabilityMeasure μ]

/- Remark 5.2 (2): if `X, Y ∈ L²(μ)`, then their product `XY` is integrable, so the covariance is
well-defined. This is the canonical Hölder consequence `MemLp.integrable_mul`. -/
recall MemLp.integrable_mul

/- Remark 5.2 (3): for square-integrable real random variables on a probability space, covariance
can be written as `𝔼[XY] - 𝔼[X] 𝔼[Y]`. This is the canonical theorem
`covariance_eq_sub`. -/
recall covariance_eq_sub

/- Remark 5.2 (4): variance is the covariance of a real random variable with itself. This is the
canonical identity `covariance_self`. -/
recall covariance_self

end Probability
