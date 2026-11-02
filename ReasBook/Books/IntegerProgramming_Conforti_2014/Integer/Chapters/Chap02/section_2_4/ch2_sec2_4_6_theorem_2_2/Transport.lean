module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_6_definition_2_26

public section

namespace SteinerTripleSystem

universe u v

variable {α : Type u} {β : Type v}

/-- Helper for Theorem 2.2: transporting a Steiner triple system along an embedding preserves the
Steiner axioms. -/
theorem IsOn.mapEmbedding {E : Finset α} {S : Set (Finset α)}
    (h : IsOn E S) (f : α ↪ β) :
    IsOn (E.map f) ((fun s : Finset α ↦ s.map f) '' S) := by
  classical
  refine IsOn.ofSubsetGroundSizedAndPairCover ?_ ?_ ?_
  · -- Mapping each block preserves containment in the mapped ground set.
    intro t ht
    rcases ht with ⟨s, hsS, rfl⟩
    exact (Finset.map_subset_map.2 (h.subset_ground s hsS))
  · -- Cardinality is preserved because `Finset.map` along an embedding is bijective on elements.
    intro t ht
    rcases ht with ⟨s, hsS, rfl⟩
    simpa using h.sized hsS
  · -- Pull the `2`-subset back through `powersetCard_map`, use uniqueness there, and remap it.
    intro p hp
    have hp' : p ∈ (E.powersetCard 2).map (Finset.mapEmbedding f).toEmbedding := by
      simpa [Finset.powersetCard_map] using hp
    rcases Finset.mem_map.mp hp' with ⟨q, hq, rfl⟩
    rcases h.pair_cover q hq with ⟨s, hs, hsuniq⟩
    refine ⟨s.map f, ?_, ?_⟩
    · exact ⟨⟨s, hs.1, rfl⟩, Finset.map_subset_map.2 hs.2⟩
    · intro t ht
      rcases ht with ⟨htS, hpt⟩
      rcases htS with ⟨u, huS, rfl⟩
      have hqu : q ⊆ u := Finset.map_subset_map.1 hpt
      have hus : u = s := hsuniq u ⟨huS, hqu⟩
      simp [hus]

/-- Helper for Theorem 2.2: an `IsOn` witness on a finite type can be transported across an
equivalence to the canonical `Fin` ground set. -/
theorem IsOn.mapEquivUniv [Fintype α] [Fintype β] {S : Set (Finset α)}
    (h : IsOn (Finset.univ : Finset α) S) (e : α ≃ β) :
    IsOn (Finset.univ : Finset β) ((fun s : Finset α ↦ s.map e.toEmbedding) '' S) := by
  -- The only extra work is rewriting the mapped universal ground set back to `Finset.univ`.
  simpa [Finset.map_univ_equiv] using h.mapEmbedding e.toEmbedding

/-- Helper for Theorem 2.2: any Steiner triple system on a finite type can be relabeled onto the
canonical ground set `Fin n` once the cardinality is identified with `n`. -/
theorem existsOnFin_of_cardEq [Fintype α] {n : ℕ}
    (h : ∃ S : Set (Finset α), IsOn (Finset.univ : Finset α) S)
    (hcard : Fintype.card α = n) :
    ∃ S : Set (Finset (Fin n)), IsOn Finset.univ S := by
  rcases h with ⟨S, hS⟩
  refine ⟨(fun s : Finset α ↦ s.map (Fintype.equivFinOfCardEq hcard).toEmbedding) '' S, ?_⟩
  simpa using hS.mapEquivUniv (Fintype.equivFinOfCardEq hcard)

end SteinerTripleSystem
