/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

/-- Theorem 2.19: a probability vector on a finite state space can be realized as the common law
of an independent sequence of `E`-valued random variables on some probability space. -/
theorem exists_independent_random_variables_with_prescribed_probabilities
    {E : Type u} [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E]
    (p : E → ENNReal) (hp : Finset.univ.sum p = 1) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : ℕ → Ω → E,
      (∀ n, Measurable (X n)) ∧
        (∀ n, HasLaw (X n) (PMF.ofFintype p hp).toMeasure P) ∧
        iIndepFun X P ∧
        IsProbabilityMeasure P := by
  simpa using exists_iid ℕ ((PMF.ofFintype p hp).toMeasure)

/-- Any random variable with the prescribed law assigns probability `p e` to the event `X = e`. -/
theorem hasLaw_preimage_singleton_eq_prescribedProbability
    {Ω : Type u} {E : Type u} [MeasurableSpace Ω] [Fintype E] [MeasurableSpace E]
    [MeasurableSingletonClass E] {P : Measure Ω} {X : Ω → E}
    {p : E → ENNReal} {hp : Finset.univ.sum p = 1}
    (hX : HasLaw X (PMF.ofFintype p hp).toMeasure P) (e : E) :
    P (X ⁻¹' {e}) = p e := by
  calc
    P (X ⁻¹' {e}) = P.map X {e} := by
      symm
      exact Measure.map_apply_of_aemeasurable hX.aemeasurable (measurableSet_singleton e)
    _ = (PMF.ofFintype p hp).toMeasure {e} := by rw [hX.map_eq]
    _ = p e := by
      exact (PMF.ofFintype p hp).toMeasure_apply_singleton e (measurableSet_singleton e)
