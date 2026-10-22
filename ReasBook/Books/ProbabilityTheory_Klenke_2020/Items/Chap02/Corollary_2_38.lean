/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
private theorem measurableSet_limsup_tail_generateFrom (A : ℕ → Set Ω) :
    MeasurableSet[limsup (fun n ↦ MeasurableSpace.generateFrom {A n}) atTop] (limsup A atTop) := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat', MeasurableSpace.measurableSet_iInf]
  intro n
  let m : MeasurableSpace Ω := ⨆ i, MeasurableSpace.generateFrom {A (i + n)}
  change MeasurableSet[m] (limsup A atTop)
  letI : MeasurableSpace Ω := m
  have hA : ∀ i, MeasurableSet (A (i + n)) := fun i ↦ by
    let h_le : MeasurableSpace.generateFrom {A (i + n)} ≤ m :=
      le_iSup (fun j ↦ MeasurableSpace.generateFrom {A (j + n)}) i
    exact h_le _ <| MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
  simpa [m, Filter.limsup_nat_add] using MeasurableSet.measurableSet_limsup hA

omit [MeasurableSpace Ω] in
private theorem measurableSet_liminf_tail_generateFrom (A : ℕ → Set Ω) :
    MeasurableSet[limsup (fun n ↦ MeasurableSpace.generateFrom {A n}) atTop] (liminf A atTop) := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat', MeasurableSpace.measurableSet_iInf]
  intro n
  let m : MeasurableSpace Ω := ⨆ i, MeasurableSpace.generateFrom {A (i + n)}
  change MeasurableSet[m] (liminf A atTop)
  letI : MeasurableSpace Ω := m
  have hA : ∀ i, MeasurableSet (A (i + n)) := fun i ↦ by
    let h_le : MeasurableSpace.generateFrom {A (i + n)} ≤ m :=
      le_iSup (fun j ↦ MeasurableSpace.generateFrom {A (j + n)}) i
    exact h_le _ <| MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
  simpa [m, Filter.liminf_nat_add] using MeasurableSet.measurableSet_liminf hA

/-- Corollary 2.38: For a sequence of independent measurable events, both the `limsup` event and
the `liminf` event have probability either `0` or `1`. -/
-- Proof sketch: View the events as the independent sequence of generated σ-algebras
-- `generateFrom {A n}`. Kolmogorov's `0`-`1` law applies to the tail event `limsup A atTop`.
-- The same tail σ-algebra argument applies directly to `liminf A atTop`.
theorem measure_limsup_and_liminf_zero_or_one_of_iIndepSet (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA_meas : ∀ n, MeasurableSet (A n)) (hA_indep : iIndepSet A μ) :
    (μ (limsup A atTop) = 0 ∨ μ (limsup A atTop) = 1) ∧
      (μ (liminf A atTop) = 0 ∨ μ (liminf A atTop) = 1) := by
  let s : ℕ → MeasurableSpace Ω := fun n ↦ MeasurableSpace.generateFrom {A n}
  have hs_le : ∀ n, s n ≤ ‹MeasurableSpace Ω› := fun n ↦
    MeasurableSpace.generateFrom_singleton_le (hA_meas n)
  have h_indep_comap : iIndep (fun n ↦ MeasurableSpace.comap (· ∈ A n) ⊤) μ :=
    hA_indep.iIndep_comap_mem
  have h_indep : iIndep s μ := by
    simpa [s, MeasurableSpace.generateFrom_singleton] using h_indep_comap
  have h_limsup_meas : MeasurableSet[limsup s atTop] (limsup A atTop) := by
    simpa [s] using measurableSet_limsup_tail_generateFrom A
  have h_liminf_meas : MeasurableSet[limsup s atTop] (liminf A atTop) := by
    simpa [s] using measurableSet_liminf_tail_generateFrom A
  refine ⟨?_, ?_⟩
  · exact measure_zero_or_one_of_measurableSet_limsup_atTop hs_le h_indep h_limsup_meas
  · exact measure_zero_or_one_of_measurableSet_limsup_atTop hs_le h_indep h_liminf_meas
