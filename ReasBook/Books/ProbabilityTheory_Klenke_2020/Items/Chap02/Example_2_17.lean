/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

private lemma isPiSystem_insert_empty_range_singleton {E : Type w} [MeasurableSpace E] :
    IsPiSystem (insert ∅ (range fun x : E ↦ ({x} : Set E))) := by
  intro s hs t ht
  rcases hs with rfl | ⟨x, rfl⟩ <;> rcases ht with rfl | ⟨y, rfl⟩
  · simp
  · simp
  · simp
  · by_cases hxy : x = y <;> simp [hxy]

private lemma generateFrom_insert_empty_range_singleton_eq
    {E : Type w} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] :
    MeasurableSpace.generateFrom (insert ∅ (range fun x : E ↦ ({x} : Set E))) =
      ‹MeasurableSpace E› := by
  ext s
  constructor
  · intro hs
    have h_le :
        MeasurableSpace.generateFrom (insert ∅ (range fun x : E ↦ ({x} : Set E))) ≤
          ‹MeasurableSpace E› := by
      refine MeasurableSpace.generateFrom_le ?_
      intro t ht
      rcases ht with rfl | ⟨x, rfl⟩ <;> simp
    exact h_le s hs
  · intro _hs
    let m : MeasurableSpace E := MeasurableSpace.generateFrom (insert ∅
      (range fun x : E ↦ ({x} : Set E)))
    have hm_singleton : @MeasurableSingletonClass E m := by
      refine ⟨fun x ↦ ?_⟩
      exact MeasurableSpace.measurableSet_generateFrom (by
        right
        exact ⟨x, rfl⟩)
    have hm_discrete : @DiscreteMeasurableSpace E m :=
      @MeasurableSingletonClass.toDiscreteMeasurableSpace E m hm_singleton ‹Countable E›
    exact hm_discrete.forall_measurableSet s

private lemma singleton_preimage_family_iIndepSets
    {Ω : Type u} {ι : Type v} {E : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : ι → Ω → E)
    (h :
      ∀ (J : Finset ι) (x : J → E),
        μ (⋂ j : J, X j.1 ⁻¹' ({x j} : Set E)) = ∏ j : J, μ (X j.1 ⁻¹' ({x j} : Set E))) :
    iIndepSets
      (fun i ↦ Set.preimage (X i) '' insert ∅ (range fun x : E ↦ ({x} : Set E))) μ := by
  rw [iIndepSets_iff]
  intro J s hs
  classical
  by_cases h_empty : ∃ i, i ∈ J ∧ s i = ∅
  · rcases h_empty with ⟨i, hiJ, hsi⟩
    have h_inter : (⋂ j ∈ J, s j) = ∅ := by
      rw [Set.iInter₂_eq_empty_iff]
      intro ω
      exact ⟨i, hiJ, by simp [hsi]⟩
    have h_prod : ∏ j ∈ J, μ (s j) = 0 := by
      exact Finset.prod_eq_zero hiJ (by simp [hsi])
    simp [h_inter, h_prod]
  · have hx : ∀ j : J, ∃ x : E, s j.1 = X j.1 ⁻¹' ({x} : Set E) := by
      intro j
      rcases hs j.1 j.2 with ⟨t, ht, hts⟩
      rcases ht with rfl | ⟨x, rfl⟩
      · exact False.elim <| h_empty ⟨j.1, j.2, hts.symm⟩
      · exact ⟨x, hts.symm⟩
    choose x hx using hx
    rw [show (⋂ i ∈ J, s i) = ⋂ j : J, s j.1 by
      ext ω
      simp]
    rw [show (⋂ j : J, s j.1) = ⋂ j : J, X j.1 ⁻¹' ({x j} : Set E) by
      ext ω
      simp [hx]]
    rw [show (∏ i ∈ J, μ (s i)) = ∏ j : J, μ (s j.1) by
      exact (Finset.prod_attach J fun i ↦ μ (s i)).symm]
    rw [show (∏ j : J, μ (s j.1)) = ∏ j : J, μ (X j.1 ⁻¹' ({x j} : Set E)) by
      simp [hx]]
    exact h J x

-- Proof sketch: specialize `iIndepFun_iff_measure_inter_preimage_eq_mul` to the measurable
-- singleton sets `{x j}`. For the converse, the family `insert ∅ (range singleton)` is a
-- generating `π`-system on a countable measurable-singleton space, so Theorem 2.16 upgrades the
-- finite product formula on singleton cylinder events to independence.
/-- Example 2.17: for a family of `E`-valued random variables on a countable
measurable-singleton space, independence is equivalent to the finite product formula for the
singleton events `{X_j = x_j}`. -/
theorem iIndepFun_iff_measure_biInter_preimage_singleton_eq_prod
    {Ω : Type u} {ι : Type v} {E : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E] (μ : Measure Ω) (X : ι → Ω → E)
    (hX : ∀ i, Measurable (X i)) :
    iIndepFun X μ ↔
      ∀ (J : Finset ι) (x : J → E),
        μ (⋂ j : J, X j.1 ⁻¹' ({x j} : Set E)) = ∏ j : J, μ (X j.1 ⁻¹' ({x j} : Set E)) := by
  constructor
  · intro h J x
    have hJ : iIndepFun (fun j : J ↦ X j.1) μ := h.precomp Subtype.val_injective
    simpa using hJ.measure_inter_preimage_eq_mul Finset.univ
      (fun j _ ↦ measurableSet_singleton (x j))
  · intro h
    have h_singleton :
        iIndepSets
          (fun i ↦ Set.preimage (X i) '' insert ∅ (range fun x : E ↦ ({x} : Set E))) μ :=
      singleton_preimage_family_iIndepSets μ X h
    exact iIndepFun_of_iIndepSets_preimage_generators μ X hX
      (fun _ ↦ insert ∅ (range fun x : E ↦ ({x} : Set E)))
      (fun _ ↦ isPiSystem_insert_empty_range_singleton)
      (fun _ ↦ generateFrom_insert_empty_range_singleton_eq)
      h_singleton
