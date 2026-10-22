/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Proof sketch: apply `condExp_mono` to the pointwise bound
-- `Set.indicator {ω | ε ≤ ‖X ω‖₊} (fun _ ↦ (1 : ℝ)) ≤ fun ω ↦ (f ‖X ω‖₊ : ℝ) / f ε`,
-- then use `condExp_smul` to pull out the constant factor `1 / f ε`; the left-hand side is
-- exactly `P⟦{ω | ε ≤ ‖X ω‖₊} | ℱ⟧`.
/-- Exercise 8.2.5: the conditional Markov inequality. For a monotone increasing function
`f : [0, ∞) → [0, ∞)` and a threshold `ε` with `f ε > 0`, the conditional probability of the tail event
`{ω | |X ω| ≥ ε}` is almost surely bounded by the conditional expectation of `f (|X|)` divided by
`f ε`. -/
theorem condProb_abs_ge_le_condExp_div_of_monotone
    {ℱ : MeasurableSpace Ω} {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    {f : ℝ≥0 → ℝ≥0} (hf : Monotone f) {ε : ℝ≥0} (hfε : 0 < f ε)
    (hfi : Integrable (fun ω ↦ (f ‖X ω‖₊ : ℝ)) P) :
    P⟦{ω | ε ≤ ‖X ω‖₊} | ℱ⟧ ≤ᵐ[P]
      fun ω ↦ P[fun ω ↦ (f ‖X ω‖₊ : ℝ) | ℱ] ω / (f ε : ℝ) := by
  set A : Set Ω := {ω | ε ≤ ‖X ω‖₊}
  set g : Ω → ℝ := fun ω ↦ (f ‖X ω‖₊ : ℝ)
  set c : ℝ := (f ε : ℝ)
  have hXnn : @Measurable Ω ℝ≥0 mΩ NNReal.measurableSpace (fun ω ↦ ‖X ω‖₊) := by
    simpa using (@Measurable.nnnorm ℝ Ω inferInstance inferInstance inferInstance mΩ X hX)
  have hA : @MeasurableSet Ω mΩ A := by
    change @MeasurableSet Ω mΩ ((fun ω ↦ ‖X ω‖₊) ⁻¹' Set.Ici ε)
    exact MeasurableSet.preimage measurableSet_Ici hXnn
  have hc : 0 < c := by
    simpa [c] using hfε
  have hg_int : Integrable g P := by
    simpa [g] using hfi
  have hleft_int : Integrable (Set.indicator A (fun _ ↦ (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hA
  have hright_int : Integrable (fun ω ↦ g ω / c) P := by
    simpa [g, c, div_eq_mul_inv] using hg_int.mul_const c⁻¹
  have hpointwise : Set.indicator A (fun _ ↦ (1 : ℝ)) ≤ᵐ[P] fun ω ↦ g ω / c :=
    .of_forall fun ω ↦ by
      by_cases hω : ω ∈ A
      · have hge : f ε ≤ f ‖X ω‖₊ := hf hω
        have hdiv : 1 ≤ g ω / c := by
          rw [one_le_div hc]
          exact_mod_cast hge
        simpa [A, g, c, hω] using hdiv
      · have hnonneg : 0 ≤ g ω / c := by
          have hg_nonneg : 0 ≤ g ω := by
            change 0 ≤ (f ‖X ω‖₊ : ℝ)
            exact_mod_cast (f ‖X ω‖₊).2
          exact div_nonneg hg_nonneg hc.le
        simpa [A, g, c, hω] using hnonneg
  have hmono : P⟦A | ℱ⟧ ≤ᵐ[P] P[fun ω ↦ g ω / c | ℱ] := by
    simpa using condExp_mono hleft_int hright_int hpointwise
  have hpull : P[fun ω ↦ g ω / c | ℱ] =ᵐ[P] fun ω ↦ P[g | ℱ] ω / c := by
    simpa [g, c, div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (condExp_smul c⁻¹ g ℱ)
  simpa [A, g, c] using hmono.trans_eq hpull
