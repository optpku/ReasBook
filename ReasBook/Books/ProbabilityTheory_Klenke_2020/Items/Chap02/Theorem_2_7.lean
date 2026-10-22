/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

open scoped ENNReal

universe u

variable {Ω : Type u}

/-- Theorem 2.7 (1): If the series of the measures of the events `A n` is finite, then the
set-theoretic `limsup` event `limsup A atTop` has measure zero. -/
-- Proof sketch: Apply the first Borel-Cantelli lemma in the general measure-space form, viewing
-- `limsup A atTop` as the event that infinitely many of the `A n` occur.
theorem borelCantelli_measure_limsup_atTop_eq_zero [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : (∑' n, μ (A n)) ≠ ∞) :
    μ (limsup A atTop) = 0 := by
  -- Reuse the general measure-space Borel-Cantelli lemma for the tail event `limsup A atTop`.
  simpa using MeasureTheory.measure_limsup_atTop_eq_zero (μ := μ) (s := A) hA

/-- Theorem 2.7 (2): For an independent sequence of measurable events in a probability space, if
the series of their probabilities diverges, then the set-theoretic `limsup` event has probability
one. -/
-- Proof sketch: Use the second Borel-Cantelli lemma for an independent family of measurable sets;
-- the divergence of `∑' n, μ (A n)` forces `limsup A atTop` to have full measure.
theorem borelCantelli_measure_limsup_atTop_eq_one [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hA_meas : ∀ n : ℕ, MeasurableSet (A n))
    (hA_indep : iIndepSet A μ) (hA : (∑' n, μ (A n)) = ∞) :
    μ (limsup A atTop) = 1 := by
  -- Reuse the probability-space Borel-Cantelli lemma for measurable independent events.
  simpa using ProbabilityTheory.measure_limsup_eq_one (μ := μ) (s := A) hA_meas hA_indep hA
