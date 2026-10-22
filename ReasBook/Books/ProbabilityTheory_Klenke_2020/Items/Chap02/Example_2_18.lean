/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory ProbabilityTheory

-- Proof sketch: apply `iIndepFun_infinitePi` to the coordinate projections on the infinite product
-- space `E^ℕ` equipped with the product measure `Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)`.
/-- Example 2.18: For the Bernoulli product measure on `E^ℕ` associated to the probability vector
`p`, the coordinate projections `X_n (ω) = ω n` form an independent family of random variables. -/
theorem iIndepFun_coordinateProjection_of_bernoulliProductMeasure {E : Type u}
    [MeasurableSpace E] (p : PMF E) :
    iIndepFun (fun n (ω : ℕ → E) ↦ ω n) (Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)) := by
  have h : iIndepFun (fun i (ω : ℕ → E) ↦ id (ω i))
      (Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)) :=
    iIndepFun_infinitePi (fun _ ↦ measurable_id)
  simpa using h
