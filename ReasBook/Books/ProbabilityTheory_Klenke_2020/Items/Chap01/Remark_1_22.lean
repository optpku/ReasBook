/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set Cardinal
open scoped Cardinal

private theorem exists_nonmeasurableSet_of_countablyGenerated
    (α : Type*) [MeasurableSpace α] [MeasurableSpace.CountablyGenerated α] (hα : 𝔠 ≤ #α) :
    ∃ s : Set α, ¬ MeasurableSet s := by
  classical
  have hcount : Set.Countable (MeasurableSpace.countableGeneratingSet α) :=
    MeasurableSpace.countable_countableGeneratingSet
  have hgen : #(MeasurableSpace.countableGeneratingSet α) ≤ 𝔠 := by
    haveI : Countable (MeasurableSpace.countableGeneratingSet α) := hcount.to_subtype
    exact Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
  have hmeas : #{s : Set α // MeasurableSet s} ≤ 𝔠 := by
    have hm : ‹MeasurableSpace α› = MeasurableSpace.generateFrom
        (MeasurableSpace.countableGeneratingSet α) := by
      symm
      exact MeasurableSpace.generateFrom_countableGeneratingSet
    rw [hm]
    exact MeasurableSpace.cardinal_measurableSet_le_continuum hgen
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (Subtype.val : {s : Set α // MeasurableSet s} → Set α) := by
    intro s
    exact ⟨⟨s, h s⟩, rfl⟩
  have hset : #(Set α) ≤ 𝔠 :=
    (Cardinal.mk_le_of_surjective hsurj).trans hmeas
  rw [Cardinal.mk_set] at hset
  exact not_lt_of_ge (hset.trans hα) (Cardinal.cantor #α)

/-- Remark 1.22 (1): If `n > 0`, then `ℝ^n` has subsets that are not Borel sets. This formalizes
the definite existence claim in clause (i). -/
theorem exists_non_borel_set_euclidean (n : ℕ) [Fact (0 < n)] :
    ∃ s : Set (EuclideanSpace ℝ (Fin n)), ¬ MeasurableSet s := by
  let E := EuclideanSpace ℝ (Fin n)
  letI : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  have hE : 𝔠 ≤ #E := by
    simpa [E] using continuum_le_cardinal_of_module ℝ E
  simpa [E] using exists_nonmeasurableSet_of_countablyGenerated E hE

/-- Remark 1.22 (2): Every closed subset of `ℝ^n` is a Borel set. This formalizes the first part
of clause (ii). -/
theorem measurableSet_of_isClosed_euclidean (n : ℕ)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsClosed C) :
    MeasurableSet C :=
  hC.measurableSet

/-- Remark 1.22 (3): Every singleton subset of `ℝ^n` is a Borel set. This formalizes the
particular case highlighted at the end of clause (ii). -/
theorem measurableSet_singleton_euclidean (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet ({x} : Set (EuclideanSpace ℝ (Fin n))) := by
  exact MeasurableSet.singleton x

/-- Remark 1.22 (4): For `n > 0`, the Borel subsets of `ℝ^n` are not closed under arbitrary
unions, so they do not form a topology. This formalizes clause (iii). -/
theorem borel_euclidean_not_closedUnder_arbitrary_sUnion (n : ℕ) [Fact (0 < n)] :
    ¬ ∀ A : Set (Set (EuclideanSpace ℝ (Fin n))),
        (∀ s ∈ A, MeasurableSet s) → MeasurableSet (⋃₀ A) := by
  let E := EuclideanSpace ℝ (Fin n)
  intro h
  obtain ⟨V, hV⟩ := exists_non_borel_set_euclidean n
  let A : Set (Set E) := {s | ∃ x ∈ V, s = {x}}
  have hA : ∀ s ∈ A, MeasurableSet s := by
    intro s hs
    rcases hs with ⟨x, hx, rfl⟩
    exact measurableSet_singleton_euclidean n x
  have hUnion : ⋃₀ A = V := by
    ext x
    simp [A]
  exact hV (hUnion ▸ h A hA)
