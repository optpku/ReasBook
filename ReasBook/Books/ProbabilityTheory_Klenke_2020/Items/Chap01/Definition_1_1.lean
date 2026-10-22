/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

variable {X : Type u}

/-- Definition 1.1 (1): A class of sets is intersection-closed, or a pi-system in the textbook
sense, if it contains the intersection of any two of its members. -/
class IsInterClosed (A : Set (Set X)) : Prop where
  inter_mem : ∀ ⦃s t : Set X⦄, s ∈ A → t ∈ A → s ∩ t ∈ A

/- Mathlib companion to Definition 1.1 (1): `IsPiSystem` is the canonical library predicate for
closure under nonempty binary intersections. -/
recall IsPiSystem

/-- Binary intersection closure implies mathlib's `IsPiSystem` condition. -/
theorem IsInterClosed.isPiSystem {A : Set (Set X)} (hA : IsInterClosed A) :
    IsPiSystem A := by
  intro s hs t ht _
  exact hA.inter_mem hs ht

/-- If a family contains `∅`, then mathlib's `IsPiSystem` condition is equivalent to the
textbook binary-intersection closure. -/
theorem IsPiSystem.isInterClosed {A : Set (Set X)} (hA : IsPiSystem A) (hEmpty : (∅ : Set X) ∈ A) :
    IsInterClosed A := by
  refine ⟨?_⟩
  intro s t hs ht
  by_cases hst : (s ∩ t : Set X).Nonempty
  · exact hA s hs t ht hst
  · rw [not_nonempty_iff_eq_empty] at hst
    rwa [hst]

/-- Definition 1.1: for item (1), under the additional hypothesis `∅ ∈ A`, the textbook
binary-intersection formulation of a `π`-system agrees with mathlib's canonical predicate
`IsPiSystem`. -/
theorem isPiSystem_iff_isInterClosed_of_empty_mem {A : Set (Set X)} (hEmpty : (∅ : Set X) ∈ A) :
    IsPiSystem A ↔ IsInterClosed A := by
  constructor
  · intro hA
    exact hA.isInterClosed hEmpty
  · intro hA
    exact hA.isPiSystem

/-- Definition 1.1 (2): A class of sets is sigma-intersection-closed if it contains the
intersection of every sequence of its members. This is the canonical Lean formulation of closure
under countable intersections. -/
class IsCountablyInterClosed (A : Set (Set X)) : Prop where
  iInter_mem : ∀ s : ℕ → Set X, (∀ n : ℕ, s n ∈ A) → (⋂ n : ℕ, s n) ∈ A

/-- Countable intersection closure canonically implies binary intersection closure. -/
instance IsCountablyInterClosed.toIsInterClosed {A : Set (Set X)}
    (hA : IsCountablyInterClosed A) : IsInterClosed A where
  inter_mem {s t} hs ht := by
    let u : ℕ → Set X := fun n ↦ if n = 0 then s else t
    have hu : ∀ n : ℕ, u n ∈ A := by
      intro n
      by_cases hn : n = 0
      · simpa [u, hn] using hs
      · simpa [u, hn] using ht
    have hEq : (⋂ n : ℕ, u n) = s ∩ t := by
      rw [← inter_iInter_nat_succ u]
      ext x
      simp [u]
    exact hEq ▸ hA.iInter_mem u hu

/-- A sigma-intersection-closed class contains the intersection of every nonempty countable
subfamily of its members. -/
theorem IsCountablyInterClosed.sInter_mem {A : Set (Set X)} (hA : IsCountablyInterClosed A)
    {S : Set (Set X)} (hS : S.Countable) (hS_ne : S.Nonempty) (hSA : S ⊆ A) :
    ⋂₀ S ∈ A := by
  obtain ⟨s, rfl⟩ := hS.exists_eq_range hS_ne
  simpa [sInter_range] using hA.iInter_mem s (fun n ↦ hSA (mem_range_self n))

/-- Definition 1.1 (3): A class of sets is union-closed if it contains the union of any two of
its members. -/
class IsUnionClosed (A : Set (Set X)) : Prop where
  union_mem : ∀ ⦃s t : Set X⦄, s ∈ A → t ∈ A → s ∪ t ∈ A

/-- Definition 1.1 (4): A class of sets is sigma-union-closed if it contains the union of every
sequence of its members. This is the canonical Lean formulation of closure under countable
unions. -/
class IsCountablyUnionClosed (A : Set (Set X)) : Prop where
  iUnion_mem : ∀ s : ℕ → Set X, (∀ n : ℕ, s n ∈ A) → (⋃ n : ℕ, s n) ∈ A

/-- Countable union closure canonically implies binary union closure. -/
instance IsCountablyUnionClosed.toIsUnionClosed {A : Set (Set X)}
    (hA : IsCountablyUnionClosed A) : IsUnionClosed A where
  union_mem {s t} hs ht := by
    let u : ℕ → Set X := fun n ↦ if n = 0 then s else t
    have hu : ∀ n : ℕ, u n ∈ A := by
      intro n
      by_cases hn : n = 0
      · simpa [u, hn] using hs
      · simpa [u, hn] using ht
    have hEq : (⋃ n : ℕ, u n) = s ∪ t := by
      rw [← union_iUnion_nat_succ u]
      ext x
      simp [u]
    exact hEq ▸ hA.iUnion_mem u hu

/-- A sigma-union-closed class contains the union of every nonempty countable subfamily of its
members. -/
theorem IsCountablyUnionClosed.sUnion_mem {A : Set (Set X)} (hA : IsCountablyUnionClosed A)
    {S : Set (Set X)} (hS : S.Countable) (hS_ne : S.Nonempty) (hSA : S ⊆ A) :
    ⋃₀ S ∈ A := by
  obtain ⟨s, rfl⟩ := hS.exists_eq_range hS_ne
  simpa [sUnion_range] using hA.iUnion_mem s (fun n ↦ hSA (mem_range_self n))

/-- Definition 1.1 (5): A class of sets is difference-closed if it contains the difference of any
two of its members. -/
class IsDiffClosed (A : Set (Set X)) : Prop where
  diff_mem : ∀ ⦃s t : Set X⦄, s ∈ A → t ∈ A → s \ t ∈ A

/-- Definition 1.1 (6): A class of sets is complement-closed if it contains the complement of each
of its members. -/
class IsComplClosed (A : Set (Set X)) : Prop where
  compl_mem : ∀ ⦃s : Set X⦄, s ∈ A → sᶜ ∈ A
