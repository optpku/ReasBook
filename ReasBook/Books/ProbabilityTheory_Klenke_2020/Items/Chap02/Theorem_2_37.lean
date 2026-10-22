/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- Theorem 2.37: Kolmogorov's 0--1 law in the canonical sequence form for a countably infinite
family of independent sub-`σ`-algebras. Any event measurable with respect to the tail
`σ`-algebra `limsup ℱ atTop = ⋂ n, ⋃ k ≥ n, ℱ k` has probability `0` or `1`. -/
-- Proof sketch: apply the canonical mathlib theorem
-- `ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop`, which states the 0--1
-- law for an independent sequence of sub-`σ`-algebras indexed by `ℕ`.
theorem measure_zero_or_one_of_measurableSet_tail_of_iIndep (μ : Measure Ω)
    (ℱ : ℕ → MeasurableSpace Ω) (h_le : ∀ n, ℱ n ≤ mΩ) (h_indep : iIndep ℱ μ) {A : Set Ω}
    (hA : MeasurableSet[limsup ℱ atTop] A) :
    μ A = 0 ∨ μ A = 1 := by
  -- The textbook tail `σ`-algebra is exactly `limsup ℱ atTop`, so the canonical mathlib
  -- formulation of Kolmogorov's 0--1 law applies without further reduction.
  exact ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep hA
