module

public import Mathlib.Topology.Constructible
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.SetTheory.ZFC.PSet

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology

section

variable {X : Type u} [TopologicalSpace X]

/-- A subset of a topological space is a finite union of locally closed subsets. -/
def IsFiniteUnionOfLocallyClosed (E : Set X) : Prop :=
  ∃ S : Set (Set X), S.Finite ∧ (∀ Z ∈ S, IsLocallyClosed Z) ∧ E = ⋃₀ S

/-- A locally closed subset is a finite union of locally closed subsets, with one piece. -/
theorem IsLocallyClosed.isFiniteUnionOfLocallyClosed {E : Set X} (hE : IsLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed E := by
  refine ⟨{E}, Set.finite_singleton E, ?_, by simp⟩
  intro Z hZ
  exact hZ ▸ hE

namespace IsFiniteUnionOfLocallyClosed

/-- The empty set is a finite union of locally closed subsets. -/
theorem empty : IsFiniteUnionOfLocallyClosed (∅ : Set X) := by
  -- Use the empty family of locally closed pieces.
  refine ⟨∅, Set.finite_empty, ?_, ?_⟩
  · intro Z hZ
    exact False.elim (Set.notMem_empty Z hZ)
  · simp

/-- The whole space is a finite union of locally closed subsets. -/
theorem univ : IsFiniteUnionOfLocallyClosed (univ : Set X) :=
  isOpen_univ.isLocallyClosed.isFiniteUnionOfLocallyClosed

/-- Finite unions of locally closed subsets are stable under binary union. -/
theorem union {E F : Set X} (hE : IsFiniteUnionOfLocallyClosed E)
    (hF : IsFiniteUnionOfLocallyClosed F) : IsFiniteUnionOfLocallyClosed (E ∪ F) := by
  rcases hE with ⟨S, hSfin, hSlc, hEeq⟩
  rcases hF with ⟨T, hTfin, hTlc, hFeq⟩
  -- Combine the two finite families of pieces.
  refine ⟨S ∪ T, hSfin.union hTfin, ?_, ?_⟩
  · intro Z hZ
    rcases hZ with hZ | hZ
    · exact hSlc Z hZ
    · exact hTlc Z hZ
  · rw [hEeq, hFeq]
    ext x
    constructor
    · rintro (hx | hx)
      · rcases hx with ⟨Z, hZ, hxZ⟩
        exact ⟨Z, Or.inl hZ, hxZ⟩
      · rcases hx with ⟨Z, hZ, hxZ⟩
        exact ⟨Z, Or.inr hZ, hxZ⟩
    · rintro ⟨Z, hZ, hxZ⟩
      rcases hZ with hZ | hZ
      · exact Or.inl ⟨Z, hZ, hxZ⟩
      · exact Or.inr ⟨Z, hZ, hxZ⟩

-- Proof sketch: choose a finite enumeration of the finite family of locally closed pieces.
/-- Unpack a finite union of locally closed subsets into finitely many locally closed pieces. -/
theorem exists_eq_iUnion {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    ∃ n : ℕ, ∃ S : Fin n → Set X, (∀ i, IsLocallyClosed (S i)) ∧ E = ⋃ i, S i := by
  rcases hE with ⟨pieces, hpieces_fin, hpieces_lc, hEeq⟩
  classical
  letI : Fintype pieces := hpieces_fin.fintype
  let enum : Fin (Fintype.card pieces) ≃ pieces := (Fintype.equivFin pieces).symm
  -- Enumerate the finite family and forget the subtype proof in each enumerated piece.
  refine ⟨Fintype.card pieces, fun i ↦ (enum i : Set X), ?_, ?_⟩
  · intro i
    exact hpieces_lc (enum i) (enum i).property
  · rw [hEeq]
    ext x
    constructor
    · rintro ⟨Z, hZ, hxZ⟩
      let Zpiece : pieces := ⟨Z, hZ⟩
      refine Set.mem_iUnion.2 ⟨Fintype.equivFin pieces Zpiece, ?_⟩
      simpa [enum, Zpiece] using hxZ
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact ⟨(enum i : Set X), (enum i).property, hxi⟩

/-- Finite unions of locally closed subsets are stable under binary intersection. -/
theorem inter {E F : Set X} (hE : IsFiniteUnionOfLocallyClosed E)
    (hF : IsFiniteUnionOfLocallyClosed F) : IsFiniteUnionOfLocallyClosed (E ∩ F) := by
  rcases hE with ⟨S, hSfin, hSlc, hEeq⟩
  rcases hF with ⟨T, hTfin, hTlc, hFeq⟩
  -- Intersect every locally closed piece from the first family with every piece from the second.
  refine ⟨Set.image2 (fun A B : Set X ↦ A ∩ B) S T, hSfin.image2 _ hTfin, ?_, ?_⟩
  · intro Z hZ
    rcases hZ with ⟨A, hA, B, hB, rfl⟩
    exact (hSlc A hA).inter (hTlc B hB)
  · rw [hEeq, hFeq]
    ext x
    constructor
    · rintro ⟨⟨A, hA, hxA⟩, B, hB, hxB⟩
      exact ⟨A ∩ B, ⟨A, hA, B, hB, rfl⟩, hxA, hxB⟩
    · rintro ⟨Z, hZ, hxZ⟩
      rcases hZ with ⟨A, hA, B, hB, rfl⟩
      exact ⟨⟨A, hA, hxZ.1⟩, B, hB, hxZ.2⟩

/-- The complement of a locally closed subset is a finite union of locally closed subsets. -/
theorem compl_of_isLocallyClosed {E : Set X} (hE : IsLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed Eᶜ := by
  rcases hE with ⟨U, Z, hU, hZ, rfl⟩
  -- The complement of an open-closed intersection is the union of a closed set and an open set.
  rw [compl_inter]
  exact hU.isClosed_compl.isLocallyClosed.isFiniteUnionOfLocallyClosed.union
    hZ.isOpen_compl.isLocallyClosed.isFiniteUnionOfLocallyClosed

/-- Complements of finite indexed unions of locally closed subsets are finite unions of locally
closed subsets. -/
theorem compl_iUnion {n : ℕ} {S : Fin n → Set X} (hS : ∀ i, IsLocallyClosed (S i)) :
    IsFiniteUnionOfLocallyClosed (⋃ i, S i)ᶜ := by
  induction n with
  | zero =>
      -- The complement of the empty indexed union is the whole space.
      simpa using
        (IsFiniteUnionOfLocallyClosed.univ :
          IsFiniteUnionOfLocallyClosed (Set.univ : Set X))
  | succ n ih =>
      have hUnion : (⋃ i : Fin (n + 1), S i) = S 0 ∪ ⋃ i : Fin n, S i.succ := by
        ext x
        simp [Fin.exists_fin_succ]
      -- De Morgan reduces the complement to an intersection of the first complement and the tail.
      rw [hUnion, compl_union]
      exact (compl_of_isLocallyClosed (hS 0)).inter (ih fun i ↦ hS i.succ)

/-- Finite unions of locally closed subsets are stable under complement. -/
theorem compl {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsFiniteUnionOfLocallyClosed Eᶜ := by
  obtain ⟨n, S, hS, hEq⟩ := hE.exists_eq_iUnion
  -- Enumerate the finite family and apply the finite De Morgan argument.
  rw [hEq]
  exact compl_iUnion hS

end IsFiniteUnionOfLocallyClosed

namespace Topology

-- Proof sketch: constructible sets are generated from open retrocompact sets by finite unions and
-- complements. Open retrocompact sets are open, hence locally closed, and the class of finite
-- unions of locally closed sets is stable under the finite Boolean operations used in the
-- constructible induction.
/-- Any constructible subset is a finite union of locally closed subsets. -/
theorem IsConstructible.isFiniteUnionOfLocallyClosed {E : Set X} (hE : IsConstructible E) :
    IsFiniteUnionOfLocallyClosed E := by
  -- Follow the constructible-generation proof: open retrocompact generators are open, and the
  -- target class is stable under the Boolean operations in the induction principle.
  induction hE using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
      exact hUopen.isLocallyClosed.isFiniteUnionOfLocallyClosed
  | union S hS T hT hSfinite hTfinite =>
      exact hSfinite.union hTfinite
  | compl S hS hSfinite =>
      exact hSfinite.compl

end Topology

end
