/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.DSlope

-- Semantic recall: mathlib's canonical finite-difference owner is `dslope`, and
-- `HasDerivAt.tendsto_slope_zero` / `hasDerivAt_iff_tendsto_slope_zero` express
-- that these finite-difference quotients approximate the derivative as the step tends to `0`.

open Filter
open scoped Topology

/- Chapter03 Definition 3.4-extra-1: finite-difference Newton's method replaces the exact
derivative data in Newton's method by finite-difference quotients. In mathlib, the canonical
finite-difference quotient at `x` with step `h` is `dslope f x (x + h)`, and its convergence to
the derivative is recorded by the slope-limit API below. -/

/-- Helper for Chapter03 Definition 3.4-extra-1: for a nonzero step `h`, the canonical
finite-difference quotient `dslope f x (x + h)` is the textbook forward quotient
`(f (x + h) - f x) / h`. -/
theorem dslope_add_eq_finiteDifferenceQuotient (f : ℝ → ℝ) (x h : ℝ) (hh : h ≠ 0) :
    dslope f x (x + h) = (f (x + h) - f x) / h := by
  -- Rewrite `dslope` to the usual slope formula away from the diagonal.
  rw [dslope_of_ne _ (by simpa using hh), slope_def_field]
  -- Normalize the denominator from `(x + h) - x` to `h`.
  congr 1
  ring

/-- Chapter03 Definition 3.4-extra-1: the derivative `HasDerivAt f f' x` is equivalent to
the convergence of the canonical finite-difference quotients `dslope f x (x + h)` to `f'`
as `h → 0`. -/
theorem hasDerivAt_iff_tendsto_dslope_add {f : ℝ → ℝ} {f' x : ℝ} :
    HasDerivAt f f' x ↔ Tendsto (fun h ↦ dslope f x (x + h)) (𝓝 0) (𝓝 f') := by
  constructor
  · intro hf
    -- The forward implication is continuity of `dslope f x` at `x` composed with `h ↦ x + h`.
    have hcont : ContinuousAt (dslope f x) x := by
      rw [continuousAt_dslope_same]
      exact hf.differentiableAt
    have hadd : ContinuousAt (fun h : ℝ ↦ x + h) 0 := continuousAt_const.add continuousAt_id
    have hcont' : ContinuousAt (dslope f x) ((fun h : ℝ ↦ x + h) 0) := by
      simpa using hcont
    have hcomp : ContinuousAt (fun h : ℝ ↦ dslope f x (x + h)) 0 := hcont'.comp hadd
    simpa [hf.deriv] using hcomp.tendsto
  · intro hdslope
    -- Route correction: reduce the backward implication to the standard punctured-neighborhood
    -- slope criterion instead of unfolding a separate finite-difference definition.
    have hslope :
        Tendsto (fun h ↦ slope f x (x + h)) (𝓝[≠] 0) (𝓝 f') := by
      refine Tendsto.congr' ?_ (hdslope.mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hne : x + h ≠ x := by
        simpa using hh
      simpa using dslope_of_ne f hne
    rw [hasDerivAt_iff_tendsto_slope_zero]
    refine Tendsto.congr' ?_ hslope
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [slope_def_field]
    ring

/-- Helper for Chapter03 Definition 3.4-extra-1: under `HasDerivAt f f' x`, the canonical
finite-difference quotients `dslope f x (x + h)` converge to `f'` as `h → 0`. -/
theorem HasDerivAt.tendsto_dslope_add {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    Tendsto (fun h ↦ dslope f x (x + h)) (𝓝 0) (𝓝 f') :=
  (hasDerivAt_iff_tendsto_dslope_add).1 hf
