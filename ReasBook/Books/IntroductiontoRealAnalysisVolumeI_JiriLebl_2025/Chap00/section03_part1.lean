/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped BigOperators

section Chap00
section Section03

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Definition 0.3.1: A set is a collection of objects called elements or
members. A set with no objects is the empty set, written `∅` (or `{}`). -/
abbrev ElementCollection (α : Type u) := Set α

/-- The empty set from Definition 0.3.1 is mathlib's `∅`. -/
abbrev emptyElementCollection (α : Type u) : ElementCollection α :=
  (∅ : Set α)

/-- The book's notion of set coincides with mathlib's `Set`. -/
theorem elementCollection_eq_set (α : Type u) : ElementCollection α = Set α := by
  rfl

/-- Definition 0.3.2: (i) `A ⊆ B` means every `x ∈ A` also satisfies `x ∈ B`; (ii) `A = B`
when each is a subset of the other (otherwise `A ≠ B`); (iii) `A ⊂ B` when `A ⊆ B` but
`A ≠ B`. -/
abbrev subsetElementCollection {α : Type u} (A B : ElementCollection α) : Prop :=
  A ⊆ B

/-- The book's notion of subset is mathlib's `⊆`. -/
theorem subsetElementCollection_iff {α : Type u} {A B : ElementCollection α} :
    subsetElementCollection A B ↔ A ⊆ B := by
  rfl

/-- The book's definition of equality of sets is mutual inclusion. -/
theorem elementCollection_eq_iff_subset_subset {α : Type u} {A B : ElementCollection α} :
    A = B ↔ subsetElementCollection A B ∧ subsetElementCollection B A := by
  constructor
  · intro h
    subst h
    constructor
    · intro x hx
      exact hx
    · intro x hx
      exact hx
  · intro h
    apply Set.ext
    intro x
    constructor
    · intro hx
      exact h.1 hx
    · intro hx
      exact h.2 hx

/-- Book notion of a proper subset: contained but not equal. -/
abbrev properSubsetElementCollection {α : Type u} (A B : ElementCollection α) : Prop :=
  subsetElementCollection A B ∧ A ≠ B

/-- The book's notion of proper subset coincides with mathlib's strict subset `⊂`. -/
theorem properSubsetElementCollection_iff {α : Type u} {A B : ElementCollection α} :
    properSubsetElementCollection A B ↔ A ⊂ B := by
  constructor
  · intro h
    exact ssubset_of_subset_of_ne h.1 h.2
  · intro h
    rcases (ssubset_iff_subset_ne).1 h with ⟨hAB, hne⟩
    exact ⟨hAB, hne⟩

/-- Example 0.3.3: Standard sets of numbers: the naturals `ℕ`, integers `ℤ`, rationals `ℚ`,
even naturals `{2m}`, and reals `ℝ`, with inclusions `ℕ ⊆ ℤ ⊆ ℚ ⊆ ℝ`. -/
def naturalsInReals : Set ℝ :=
  Set.range fun n : ℕ => (n : ℝ)

/-- Example 0.3.3 (continued). -/
def integersInReals : Set ℝ :=
  Set.range fun z : ℤ => (z : ℝ)

/-- Example 0.3.3 (continued). -/
def rationalsInReals : Set ℝ :=
  Set.range fun q : ℚ => (q : ℝ)

/-- Example 0.3.3 (continued). -/
def evenNaturalsInReals : Set ℝ :=
  Set.range fun m : ℕ => (2 * m : ℝ)

/-- Example 0.3.3: The canonical embeddings realize the chain `ℕ ⊆ ℤ ⊆ ℚ ⊆ ℝ`. -/
theorem naturalsInReals_subset_integersInReals :
    naturalsInReals ⊆ integersInReals := by
  intro x hx
  rcases hx with ⟨n, rfl⟩
  refine ⟨(n : ℤ), ?_⟩
  norm_cast

/-- Example 0.3.3 (continued). -/
theorem integersInReals_subset_rationalsInReals :
    integersInReals ⊆ rationalsInReals := by
  intro x hx
  rcases hx with ⟨z, rfl⟩
  refine ⟨(z : ℚ), ?_⟩
  norm_cast

/-- Example 0.3.3 (continued). -/
theorem rationalsInReals_subset_reals :
    rationalsInReals ⊆ (Set.univ : Set ℝ) := by
  intro x hx
  exact Set.mem_univ x

/-- Definition 0.3.4: (i) union `A ∪ B = {x : x ∈ A ∨ x ∈ B}`; (ii) intersection
`A ∩ B = {x : x ∈ A ∧ x ∈ B}`; (iii) relative complement (set difference) `A \ B = {x :
  x ∈ A ∧ x ∉ B}`; (iv) complement `Bᶜ` means the difference from the ambient universe or an
understood superset; (v) sets are disjoint when their intersection is empty. -/
abbrev unionElementCollection (A B : ElementCollection α) : ElementCollection α :=
  A ∪ B

theorem mem_unionElementCollection {A B : ElementCollection α} {x : α} :
    x ∈ unionElementCollection A B ↔ x ∈ A ∨ x ∈ B := by
  simp [unionElementCollection]

abbrev intersectionElementCollection (A B : ElementCollection α) :
    ElementCollection α :=
  A ∩ B

theorem mem_intersectionElementCollection {A B : ElementCollection α} {x : α} :
    x ∈ intersectionElementCollection A B ↔ x ∈ A ∧ x ∈ B := by
  simp [intersectionElementCollection]

abbrev relativeComplementElementCollection (A B : ElementCollection α) :
    ElementCollection α :=
  A \ B

theorem mem_relativeComplementElementCollection {A B : ElementCollection α} {x : α} :
    x ∈ relativeComplementElementCollection A B ↔ x ∈ A ∧ x ∉ B := by
  simp [relativeComplementElementCollection]

abbrev complementElementCollection (B : ElementCollection α) : ElementCollection α :=
  Set.compl B

theorem mem_complementElementCollection {B : ElementCollection α} {x : α} :
    x ∈ complementElementCollection B ↔ x ∉ B := by
  rfl

abbrev disjointElementCollections (A B : ElementCollection α) : Prop :=
  Disjoint A B

theorem disjointElementCollections_iff {A B : ElementCollection α} :
    disjointElementCollections A B ↔ A ∩ B = (∅ : Set α) := by
  simpa [disjointElementCollections] using
    (Set.disjoint_iff_inter_eq_empty : Disjoint A B ↔ A ∩ B = (∅ : Set α))

-- Helper lemmas for De Morgan identities on sets.
lemma deMorgan_compl_union {B C : Set α} : (B ∪ C)ᶜ = Bᶜ ∩ Cᶜ := by
  simp

lemma deMorgan_compl_inter {B C : Set α} : (B ∩ C)ᶜ = Bᶜ ∪ Cᶜ := by
  simpa using (Set.compl_inter B C)

lemma deMorgan_diff_union {A B C : Set α} :
    A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  ext x
  simp [Set.mem_diff, not_or, and_left_comm, and_assoc]

lemma deMorgan_diff_inter {A B C : Set α} :
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  classical
  ext x
  simp
  tauto

/-- Theorem 0.3.5 (DeMorgan). For sets `A`, `B`, `C`,
`(B ∪ C)ᶜ = Bᶜ ∩ Cᶜ` and `(B ∩ C)ᶜ = Bᶜ ∪ Cᶜ`; more generally,
`A \ (B ∪ C) = (A \ B) ∩ (A \ C)` and `A \ (B ∩ C) = (A \ B) ∪ (A \ C)`. -/
theorem deMorgan_sets {A B C : Set α} :
    (B ∪ C)ᶜ = Bᶜ ∩ Cᶜ ∧
      (B ∩ C)ᶜ = Bᶜ ∪ Cᶜ ∧
        A \ (B ∪ C) = (A \ B) ∩ (A \ C) ∧
          A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  refine ⟨deMorgan_compl_union, ?_⟩
  refine ⟨deMorgan_compl_inter, ?_⟩
  exact ⟨deMorgan_diff_union, deMorgan_diff_inter⟩

end Section03
end Chap00
