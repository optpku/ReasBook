/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Corollary_12_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Example_12_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

/- Corollary 12.19 is a `bridge/view` statement: the Chapter 12 owner
`exchangeableSigmaAlgebra (Function.swap X)` is reduced by Corollary 12.18 to the Chapter 2 owner
`tailRandomVariableMeasurableSpace X`, and the latter is handled by the canonical tail `0`-`1`
law from Theorem 2.37. -/

universe u v

variable {Ω : Type u} {E : Type v}

variable [MeasurableSpace Ω] [MeasurableSpace E]

-- Proof sketch: `exchangeableFamily_of_isIID` upgrades the i.i.d. hypothesis to the chapter owner
-- `IsExchangeable`, and Corollary 12.18 then replaces an exchangeable event by an a.e.-equal tail
-- event. Since the coordinates are measurable, Theorem 2.37 applies to that tail event.
/-- Corollary 12.19: for a measurable i.i.d. sequence `X`, every event measurable with respect to
the exchangeable `σ`-algebra of `X` has probability `0` or `1`. This is the Hewitt--Savage `0`-`1`
law. -/
theorem measure_zero_or_one_of_measurableSet_exchangeableSigmaAlgebra_of_isIID
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n))
    (hX_iid : IsIID X μ) {A : Set Ω}
    (hA : MeasurableSet[exchangeableSigmaAlgebra (Function.swap X)] A) :
    μ A = 0 ∨ μ A = 1 := by
  have hX_exchangeable : IsExchangeable X μ := exchangeableFamily_of_isIID hX_iid
  rcases exists_tail_measurableSet_ae_eq_of_mem_exchangeableSigmaAlgebra
      hX_exchangeable hA with
    ⟨B, hB, hAB⟩
  let ℱ : ℕ → MeasurableSpace Ω := fun n ↦ MeasurableSpace.comap (X n) inferInstance
  have hB_zero_one : μ B = 0 ∨ μ B = 1 := by
    have h_tail_eq : tailRandomVariableMeasurableSpace X = limsup ℱ atTop := by
      calc
        tailRandomVariableMeasurableSpace X = ⨅ n : ℕ, ⨆ i ∈ Set.Ici n, ℱ i := by
          simpa [ℱ] using tailMeasurableSpace_nat_eq_iInf_iSup_Ici ℱ
        _ = limsup ℱ atTop := by
          rw [Filter.limsup_eq_iInf_iSup_of_nat]
          simp [Set.mem_Ici]
    rw [h_tail_eq] at hB
    exact measure_zero_or_one_of_measurableSet_tail_of_iIndep μ ℱ
      (fun n ↦ (hX_meas n).comap_le) hX_iid.iIndepFun.iIndep hB
  have hAB_measure : μ A = μ B := measure_congr hAB
  rcases hB_zero_one with hB_zero | hB_one
  · left
    rw [hAB_measure, hB_zero]
  · right
    rw [hAB_measure, hB_one]
