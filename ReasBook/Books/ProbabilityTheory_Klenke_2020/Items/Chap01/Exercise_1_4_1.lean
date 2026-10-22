/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open scoped MeasureTheory

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: relative measurability with respect to `σ(|·|)` means that `g` factors through
-- `abs`; applying the resulting `FactorsThrough` statement to `x` and `-x` gives evenness.
-- Conversely, an even measurable map satisfies `g ∘ abs = g`, so it is measurable with respect to
-- `MeasurableSpace.comap abs (borel ℝ)` by composing with `comap_measurable abs`.
/-- Exercise 1.4.1: For a Borel measurable map `g : ℝ → ℝ`, measurability with respect to the
σ-algebra `σ(|·|) = MeasurableSpace.comap abs (borel ℝ)` is equivalent to `g` being even. -/
theorem measurable_comap_abs_iff_even (g : ℝ → ℝ) (hg : Measurable g) :
    Measurable[MeasurableSpace.comap abs (borel ℝ)] g ↔ Function.Even g := by
  constructor
  · intro h x
    have hfactor : Function.FactorsThrough g abs := h.factorsThrough
    have habs : abs (-x) = abs x := by
      simp
    exact hfactor habs
  · intro h
    have hcomp : g ∘ abs = g := by
      ext x
      by_cases hx : 0 ≤ x
      · simp [abs_of_nonneg hx]
      · simpa [abs_of_neg (lt_of_not_ge hx)] using h x
    simpa [hcomp] using hg.comp (comap_measurable abs)
