/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory ProbabilityTheory

universe u

-- Proof sketch: apply `ProbabilityTheory.iIndepFun_infinitePi` to the coordinate projections on
-- the product space `E^ℕ`, then pass from independence of the random variables to independence of
-- the pullback `σ`-algebras they generate.
/-- Example 2.12: in the infinite product of a finite experiment with law `p`, the coordinate
`σ`-algebras form an independent family. -/
theorem iIndep_coordinateProjection_of_bernoulliProductMeasure {E : Type u} [Fintype E]
    [MeasurableSpace E] (p : PMF E) :
    iIndep (fun i : ℕ ↦ MeasurableSpace.comap (Function.eval i) ‹MeasurableSpace E›)
      (Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)) := by
  have h : iIndepFun (fun i (ω : ℕ → E) ↦ id (ω i))
      (Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)) :=
    iIndepFun_infinitePi (fun _ ↦ measurable_id)
  simpa [Function.eval] using h.iIndep
