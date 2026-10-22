/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Probability.CDF

public section

universe u

/- Notation 4.1-extra-1: this preliminary notation paragraph is recorded by the
canonical finite-product, empty-set, measurability, probability-measure, and
event-set surfaces already used in Chapter 4. -/

#check Finset.prod_range_add_one_eq_factorial
#check (∅ : Set ℕ)
#check Measurable
#check MeasureTheory.IsProbabilityMeasure
#check ∀ {Ω : Type u} [MeasurableSpace Ω] (X : Ω → ℝ) (x : ℝ),
  {ω | X ω ≤ x} = X ⁻¹' Set.Iic x
