/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Set

variable {α : Type u}

/-- A family of sets is closed under complements. -/
def ComplClosed (A : Set (Set α)) : Prop :=
  ∀ ⦃s : Set α⦄, s ∈ A → sᶜ ∈ A

/-- A family of sets is closed under binary intersections. -/
def InterClosed (A : Set (Set α)) : Prop :=
  ∀ ⦃s t : Set α⦄, s ∈ A → t ∈ A → s ∩ t ∈ A

/-- A family of sets is closed under binary unions. -/
def UnionClosed (A : Set (Set α)) : Prop :=
  ∀ ⦃s t : Set α⦄, s ∈ A → t ∈ A → s ∪ t ∈ A

/-- A family of sets is closed under countable intersections. -/
def CountableInterClosed (A : Set (Set α)) : Prop :=
  ∀ ⦃S : Set (Set α)⦄, S.Countable → S ⊆ A → ⋂₀ S ∈ A

/-- A family of sets is closed under countable unions. -/
def CountableUnionClosed (A : Set (Set α)) : Prop :=
  ∀ ⦃S : Set (Set α)⦄, S.Countable → S ⊆ A → ⋃₀ S ∈ A

/-- Helper for Theorem 1.3: complement closure carries a subfamily to its image under
complement. -/
lemma compl_image_subset_of_subset {A S : Set (Set α)} (hA : ComplClosed A) (hS : S ⊆ A) :
    compl '' S ⊆ A := by
  intro t ht
  -- Unpack the complemented image and apply complement closure to the original member.
  rcases ht with ⟨s, hs, rfl⟩
  exact hA (hS hs)

-- Proof sketch: Use De Morgan's law for complements of binary unions and intersections, and apply
-- complement closure to transfer membership in the family across complements.
/-- Theorem 1.3 (1): if a family of sets is closed under complements, then binary intersection
closure is equivalent to binary union closure. -/
theorem interClosed_iff_unionClosed_of_complClosed {A : Set (Set α)} (hA : ComplClosed A) :
    InterClosed A ↔ UnionClosed A := by
  constructor
  · intro hInter s t hs ht
    -- De Morgan reduces the desired union to the complement of an intersection.
    have h_inter_compl : sᶜ ∩ tᶜ ∈ A := hInter (hA hs) (hA ht)
    have h_union_compl : (s ∪ t)ᶜ ∈ A := by
      simpa [Set.compl_union] using h_inter_compl
    -- Complement closure then returns from the complemented set to the original union.
    have h_union : ((s ∪ t)ᶜ)ᶜ ∈ A := hA h_union_compl
    simpa [Set.compl_inter] using h_union
  · intro hUnion s t hs ht
    -- De Morgan reduces the desired intersection to the complement of a union.
    have h_union_compl : sᶜ ∪ tᶜ ∈ A := hUnion (hA hs) (hA ht)
    have h_inter_compl : (s ∩ t)ᶜ ∈ A := by
      simpa [Set.compl_inter] using h_union_compl
    -- Complement closure then returns from the complemented set to the original intersection.
    have h_inter : ((s ∩ t)ᶜ)ᶜ ∈ A := hA h_inter_compl
    simpa [Set.compl_union] using h_inter

-- Proof sketch: Use De Morgan's laws `compl_sUnion` and `compl_sInter`, together with closure
-- under complements, to pass between countable intersections and countable unions.
/-- Theorem 1.3 (2): if a family of sets is closed under complements, then countable intersection
closure is equivalent to countable union closure. -/
theorem countableInterClosed_iff_countableUnionClosed_of_complClosed
    {A : Set (Set α)} (hA : ComplClosed A) :
    CountableInterClosed A ↔ CountableUnionClosed A := by
  constructor
  · intro hInter S hS hSA
    -- Pass to the complemented family so countable intersections apply directly.
    have h_compl_countable : (compl '' S).Countable := hS.image (fun s : Set α ↦ sᶜ)
    have h_compl_subset : compl '' S ⊆ A := compl_image_subset_of_subset hA hSA
    have h_sInter_compl : ⋂₀ (compl '' S) ∈ A := hInter h_compl_countable h_compl_subset
    -- De Morgan identifies the target union as the complement of that intersection.
    have h_sUnion : (⋂₀ (compl '' S))ᶜ ∈ A := hA h_sInter_compl
    simpa [Set.sUnion_eq_compl_sInter_compl] using h_sUnion
  · intro hUnion S hS hSA
    -- Pass to the complemented family so countable unions apply directly.
    have h_compl_countable : (compl '' S).Countable := hS.image (fun s : Set α ↦ sᶜ)
    have h_compl_subset : compl '' S ⊆ A := compl_image_subset_of_subset hA hSA
    have h_sUnion_compl : ⋃₀ (compl '' S) ∈ A := hUnion h_compl_countable h_compl_subset
    -- De Morgan identifies the target intersection as the complement of that union.
    have h_sInter : (⋃₀ (compl '' S))ᶜ ∈ A := hA h_sUnion_compl
    simpa [Set.sInter_eq_compl_sUnion_compl] using h_sInter

end Set
