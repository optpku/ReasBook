module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_6_definition_2_26.SteinerTripleSystem

public section

namespace SteinerTripleSystem

universe u

variable {α : Type u}

/-- Definition 2.26 (Steiner triple system). A Steiner triple system of order `n` is a pair
`(E, S)` where `E` has `n` elements and `S` is a collection of `3`-element subsets of `E` such
that every `2`-element subset of `E` is contained in exactly one member of `S`. -/
structure IsOfOrder (n : ℕ) (E : Finset α) (S : Set (Finset α)) : Prop where
  /-- The ground set has exactly `n` elements. -/
  card_eq : E.card = n
  /-- The family `S` is a Steiner triple system on the ground set `E`. -/
  isOn : IsOn E S

/-- Build a Steiner triple system of order `n` from the cardinality condition and the Steiner
triple system axioms on the chosen ground set. -/
def IsOfOrder.ofCardEqAndIsOn
    {n : ℕ} {E : Finset α} {S : Set (Finset α)}
    (h_card_eq : E.card = n)
    (h_isOn : IsOn E S) :
    IsOfOrder n E S :=
  ⟨h_card_eq, h_isOn⟩

/-- Unfolding specification for `IsOfOrder` in textbook terms. -/
theorem isOfOrder_iff
    {n : ℕ} {E : Finset α} {S : Set (Finset α)} :
    IsOfOrder n E S ↔
      E.card = n ∧
        (∀ s ∈ S, s ⊆ E) ∧
          S.Sized 3 ∧
            (∀ p, p ∈ E.powersetCard 2 → ∃! s, s ∈ S ∧ p ⊆ s) := by
  constructor
  · intro h
    -- Split the order condition from the Steiner triple system witness.
    refine ⟨h.card_eq, ?_⟩
    -- Unpack the Steiner triple system fields into the textbook conjunction.
    exact ⟨h.isOn.subset_ground, h.isOn.sized, h.isOn.pair_cover⟩
  · rintro ⟨h_card_eq, h_subset_ground, h_sized, h_pair_cover⟩
    -- Rebuild the bundled Steiner triple system witness from the explicit clauses.
    refine IsOfOrder.ofCardEqAndIsOn h_card_eq ?_
    -- Package the containment, uniformity, and pair-cover data into `IsOn`.
    exact IsOn.ofSubsetGroundSizedAndPairCover h_subset_ground h_sized h_pair_cover

end SteinerTripleSystem
