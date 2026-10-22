/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set MeasureTheory ProbabilityTheory

-- Proof sketch: apply `iIndepFun_infinitePi` to the coordinate projections on the product space
-- `E^ℕ`, then specialize `iIndepFun.measure_inter_preimage_eq_mul` to the measurable sets `A i`.
/-- Under the Bernoulli product measure on `E^ℕ`, the probability of a finite intersection of
coordinate preimages is the product of the corresponding one-coordinate event probabilities. -/
private theorem bernoulliProductMeasure_coordinateEvent_biInter_eq_prod {E : Type u}
    [MeasurableSpace E] [MeasurableSingletonClass E] (p : PMF E) {A : ℕ → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (s : Finset ℕ) :
    Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure) (⋂ i ∈ s, Function.eval i ⁻¹' A i) =
      ∏ i ∈ s, Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure) (Function.eval i ⁻¹' A i) := by
  have h_indep :
      iIndepFun (fun i (ω : ℕ → E) ↦ ω i) (Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)) :=
    iIndepFun_infinitePi (fun _ ↦ measurable_id)
  simpa [Function.eval] using h_indep.measure_inter_preimage_eq_mul s (fun i _ ↦ hA i)

-- Proof sketch: combine the finite-intersection identity above with
-- `iIndepSet_iff_meas_biInter`; on a finite measurable singleton space every subset of `E` is
-- measurable, so the coordinate events satisfy the required measurability hypotheses.
/-- Example 2.4: In the Bernoulli product space `E^ℕ` attached to a probability vector `p`, the
events that the `i`th experiment lands in prescribed subsets `A i ⊆ E` form an independent
family. -/
theorem coordinateEvent_iIndepSet_of_bernoulliProductMeasure {E : Type u} [Fintype E]
    [MeasurableSpace E] [MeasurableSingletonClass E] (p : PMF E) (A : ℕ → Set E) :
    iIndepSet (fun i ↦ Function.eval i ⁻¹' A i) (Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)) := by
  have hA : ∀ i, MeasurableSet (A i) := fun i ↦ (Set.toFinite (A i)).measurableSet
  refine (iIndepSet_iff_meas_biInter fun i ↦ (measurable_pi_apply i) (hA i)).2 ?_
  intro s
  simpa using bernoulliProductMeasure_coordinateEvent_biInter_eq_prod p hA s
