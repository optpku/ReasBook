/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

section BaireSpace

variable {X : Type u} [TopologicalSpace X] [BaireSpace X]

/-- Baire-space form of the corrected open-set clause used in Lemma 1.44: for a countable family
of open sets, taking the interior after the closure of the intersection agrees with taking the
interior after intersecting the closures. -/
theorem interior_closure_iInter_eq_interior_iInter_closure_of_isOpen
    (U : ℕ → Set X) (hopen : ∀ n, IsOpen (U n)) :
    interior (closure (⋂ n, U n)) = interior (⋂ n, closure (U n)) := by
  let s : Set X := interior (⋂ n, closure (U n))
  have hs_open : IsOpen s := isOpen_interior
  have hs_subset_closure : ∀ n, s ⊆ closure (U n) := fun n ↦
    interior_subset.trans <| iInter_subset _ n
  have hdense : ∀ n, Dense (((↑) : s → X) ⁻¹' U n) := fun n ↦ by
    rw [dense_iff_closure_eq]
    apply eq_univ_iff_forall.2
    intro x
    rw [← hs_open.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val]
    exact hs_subset_closure n x.2
  let _ : BaireSpace s := hs_open.baireSpace
  have hpreimage_dense :
      Dense (⋂ n, (((↑) : s → X) ⁻¹' U n)) :=
    dense_iInter_of_isOpen_nat (fun n ↦ (hopen n).preimage continuous_subtype_val) hdense
  have hs_subset : s ⊆ closure (⋂ n, U n) := by
    intro x hx
    have hx' : x ∈ closure (((↑) : s → X) '' (⋂ n, (((↑) : s → X) ⁻¹' U n))) :=
      (Subtype.dense_iff.mp hpreimage_dense) hx
    exact (closure_mono (by
      rintro y ⟨y, hy, rfl⟩
      have hy' : ∀ n, (y : X) ∈ U n := by
        simpa [Set.mem_iInter] using hy
      exact mem_iInter.2 hy') hx')
  refine Subset.antisymm ?_ (interior_maximal hs_subset hs_open)
  exact interior_mono <|
    closure_minimal (iInter_mono fun n ↦ subset_closure) <|
      isClosed_iInter fun _ ↦ isClosed_closure

/-- Baire-space form of the corrected closed-set clause used in Lemma 1.44, dual to
`interior_closure_iInter_eq_interior_iInter_closure_of_isOpen`. -/
theorem closure_iUnion_interior_eq_closure_interior_iUnion_of_isClosed
    (C : ℕ → Set X) (hclosed : ∀ n, IsClosed (C n)) :
    closure (⋃ n, interior (C n)) = closure (interior (⋃ n, C n)) := by
  let U : ℕ → Set X := fun n ↦ (C n)ᶜ
  have hU :
      interior (closure (⋂ n, U n)) = interior (⋂ n, closure (U n)) :=
    interior_closure_iInter_eq_interior_iInter_closure_of_isOpen U
      (fun n ↦ (hclosed n).isOpen_compl)
  have hU' := congrArg Compl.compl hU
  rw [← closure_compl, ← closure_compl] at hU'
  simpa [U, compl_iInter, compl_iUnion, ← interior_compl] using hU'.symm

end BaireSpace

section CompleteMetric

variable {X : Type u} [MetricSpace X] [CompleteSpace X]

/-- Lemma 1.44 [Ursescu]: specialized to complete metric spaces through their canonical
`BaireSpace` instance, the corrected Baire-category identities for countable unions of closed sets
and countable intersections of open sets hold with the necessary closure operators. -/
theorem lemma_1_44 :
    (∀ C : ℕ → Set X, (∀ n, IsClosed (C n)) →
      closure (⋃ n, interior (C n)) = closure (interior (⋃ n, C n))) ∧
    ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) →
      interior (closure (⋂ n, U n)) = interior (⋂ n, closure (U n)) := by
  constructor
  · intro C hclosed
    exact closure_iUnion_interior_eq_closure_interior_iUnion_of_isClosed C hclosed
  · intro U hopen
    exact interior_closure_iInter_eq_interior_iInter_closure_of_isOpen U hopen

end CompleteMetric
