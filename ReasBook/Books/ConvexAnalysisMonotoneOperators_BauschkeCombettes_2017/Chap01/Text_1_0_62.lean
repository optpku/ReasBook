/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter

variable {X : Type u} [TopologicalSpace X]

private lemma eventually_mem_compl_of_isSeqClosed {s : Set X} (hs : IsSeqClosed s) {x : ℕ → X}
    {p : X} (hx : Tendsto x atTop (nhds p)) (hp : p ∈ sᶜ) :
    ∀ᶠ n in atTop, x n ∈ sᶜ := by
  by_contra hEvent
  have hFreq : ∃ᶠ n in atTop, x n ∈ s := by
    by_contra hFreq
    apply hEvent
    simpa [Filter.not_frequently] using hFreq
  rcases extraction_of_frequently_atTop hFreq with ⟨φ, hφ_mono, hφ_mem⟩
  exact hp <| hs hφ_mem <| hx.comp hφ_mono.tendsto_atTop

private lemma seqContinuous_ulift_mem_compl_of_isSeqClosed {s : Set X} (hs : IsSeqClosed s) :
    SeqContinuous (fun x : X ↦ ULift.up (x ∈ sᶜ)) := by
  intro x p hx
  by_cases hp : p ∈ sᶜ
  · have hmem : Tendsto (fun n ↦ x n ∈ sᶜ) atTop (nhds True) := by
      rw [tendsto_nhds_true]
      exact eventually_mem_compl_of_isSeqClosed hs hx hp
    simpa [Function.comp, hp] using continuous_uliftUp.seqContinuous hmem
  · have hfalse : Tendsto (fun n ↦ x n ∈ sᶜ) atTop (nhds False) := by
      simp [nhds_false]
    simpa [Function.comp, hp] using continuous_uliftUp.seqContinuous hfalse

/-- Text 1.0.62: a topological space is sequential if and only if every map from it to an
arbitrary topological space is continuous exactly when it is sequentially continuous. -/
-- Proof sketch: For the forward implication, use the existing theorem
-- `continuous_iff_seqContinuous` on a sequential space. For the converse, test the assumed
-- equivalence on the Sierpinski-valued characteristic map of `sᶜ`: sequential closedness of `s`
-- makes this map sequentially continuous, hence continuous, so `sᶜ` is open and `s` is closed.
theorem sequentialSpace_iff_forall_continuous_iff_seqContinuous :
    SequentialSpace X ↔
      ∀ ⦃Y : Type*⦄ [TopologicalSpace Y] (f : X → Y), Continuous f ↔ SeqContinuous f := by
  constructor
  · intro hX Y _ f
    letI : SequentialSpace X := hX
    exact (continuous_iff_seqContinuous : Continuous f ↔ SeqContinuous f)
  · intro h
    refine SequentialSpace.mk fun s hs ↦ ?_
    let f : X → ULift Prop := fun x ↦ ULift.up (x ∈ sᶜ)
    have hcont : Continuous f := (h f).2 (seqContinuous_ulift_mem_compl_of_isSeqClosed hs)
    have hcont' : Continuous (fun x : X ↦ x ∈ sᶜ) := by
      simpa [f, Function.comp] using continuous_uliftDown.comp hcont
    have hopen : IsOpen (sᶜ : Set X) := by
      simpa using (isOpen_iff_continuous_mem : IsOpen (sᶜ : Set X) ↔
        Continuous (fun x : X ↦ x ∈ sᶜ)).2 hcont'
    exact isOpen_compl_iff.mp hopen
