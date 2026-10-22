/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Theorem_8_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

-- Proof sketch: apply `ProbabilityTheory.strong_law_ae_real` to the shifted sequence
-- `n ↦ Z (n + 1)`, deriving pairwise independence and identical distribution from the chapter's
-- canonical i.i.d. owner hypothesis `IsIID (fun n ↦ Z (n + 1)) P`.
/-- Example 12.16: if the one-based sequence `Z₁, Z₂, …` is independent and identically
distributed on a probability space with finite first moment, then its Cesàro averages converge
almost surely to `P[Z 1]`. -/
theorem strong_law_large_numbers_ae_tendsto_of_isIID
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hZ_int : Integrable (Z 1) P) (hZ_iid : IsIID (fun n ↦ Z (n + 1)) P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Z (i + 1) ω) / n) atTop (𝓝 P[Z 1]) := by
  have hZ_pairwise : Pairwise fun i j ↦ Z (i + 1) ⟂ᵢ[P] Z (j + 1) := by
    intro i j hij
    exact hZ_iid.iIndepFun.indepFun hij
  have hZ_ident : ∀ n, IdentDistrib (Z (n + 1)) (Z 1) P P := by
    intro n
    simpa using hZ_iid.identDistrib n 0
  simpa using
    strong_law_ae_real (fun n ↦ Z (n + 1))
      hZ_int hZ_pairwise hZ_ident

-- Proof sketch: use Kolmogorov's `0`-`1` law to show that every tail event for the independent
-- sequence has probability `0` or `1`, then apply the standard conditional-expectation fact that
-- conditioning a measurable real variable on a `P`-trivial `σ`-algebra gives its expectation.
/-- For an independent measurable real sequence, the conditional expectation of the first variable
with respect to the tail `σ`-algebra is almost surely equal to its expectation. -/
theorem condExp_first_sequenceTail_ae_eq_expectation_of_iIndepFun
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X μ) :
    μ[X 0 | tailRandomVariableMeasurableSpace X] =ᵐ[μ] fun _ ↦ μ[X 0] := by
  let ℱ : ℕ → MeasurableSpace Ω := fun n ↦ MeasurableSpace.comap (X n) (borel ℝ)
  have h_tail_eq : tailRandomVariableMeasurableSpace X = limsup ℱ atTop := by
    calc
      tailRandomVariableMeasurableSpace X = ⨅ n : ℕ, ⨆ i ∈ Set.Ici n, ℱ i := by
        simpa [ℱ] using tailMeasurableSpace_nat_eq_iInf_iSup_Ici ℱ
      _ = limsup ℱ atTop := by
        rw [Filter.limsup_eq_iInf_iSup_of_nat]
        simp [Set.mem_Ici]
  have h_tail_le : tailRandomVariableMeasurableSpace X ≤ ‹MeasurableSpace Ω› := by
    simpa [tailRandomVariableMeasurableSpace, tailMeasurableSpace] using
      (limsup_le_iSup.trans <| iSup_le fun n ↦ (hX_meas n).comap_le)
  refine condExp_zero_one_subalgebra_ae_eq h_tail_le (hX_meas 0) ?_
  intro A hA
  have hA_tail :
      MeasurableSet[limsup ℱ atTop] A := by
    rw [← h_tail_eq]
    exact hA
  exact measure_zero_or_one_of_measurableSet_limsup_atTop
    (fun n ↦ (hX_meas n).comap_le) hX_indep.iIndep hA_tail
