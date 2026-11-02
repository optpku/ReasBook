import Mathlib

noncomputable section

namespace SimpleGraph

/-- Helper for Proposition 8.9: the edges obtained by adjoining two ambient edges to a graph
supported away from `root` are exactly the lifted old edges and the two adjoined edges. -/
theorem mem_edgeSet_spanningCoe_sup_pair_iff
    {V : Type*}
    {G : SimpleGraph V}
    {root : V}
    (K : SimpleGraph {v : V // v ≠ root})
    (e f : G.edgeSet)
    (g : Sym2 V) :
    g ∈ (K.spanningCoe ⊔
        SimpleGraph.fromEdgeSet ({(e : Sym2 V), (f : Sym2 V)} : Set (Sym2 V))).edgeSet ↔
      (∃ d ∈ K.edgeSet,
          (Function.Embedding.subtype fun v : V ↦ v ≠ root).sym2Map d = g) ∨
        g = e ∨ g = f := by
  have heDiag : (e : Sym2 V) ∉ Sym2.diagSet := by
    simpa only [Sym2.mem_diagSet] using G.not_isDiag_of_mem_edgeSet e.2
  have hfDiag : (f : Sym2 V) ∉ Sym2.diagSet := by
    simpa only [Sym2.mem_diagSet] using G.not_isDiag_of_mem_edgeSet f.2
  -- Rewrite the union and mapped edge set once; the only discarded elements are diagonal pairs.
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_map,
    SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_union, Set.mem_image, Set.mem_diff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (hK | ⟨hpair, -⟩)
    · exact Or.inl hK
    · exact Or.inr hpair
  · rintro (hK | hge | hgf)
    · exact Or.inl hK
    · subst g
      exact Or.inr ⟨Or.inl rfl, heDiag⟩
    · subst g
      exact Or.inr ⟨Or.inr rfl, hfDiag⟩

/-- Helper for Proposition 8.9: an edge lifted from a graph whose vertices avoid `root` cannot
contain `root`. -/
lemma root_not_mem_sym2Map_subtype
    {V : Type*}
    {root : V}
    (d : Sym2 {v : V // v ≠ root}) :
    root ∉ (Function.Embedding.subtype fun v : V ↦ v ≠ root).sym2Map d := by
  intro hroot
  rw [Function.Embedding.sym2Map_apply] at hroot
  rcases Sym2.mem_map.mp hroot with ⟨v, -, hv⟩
  exact v.2 hv

/-- Helper for Proposition 8.9: adjoining two distinct edges incident with `root` to a graph
supported away from `root` gives `root` degree two. -/
theorem degree_spanningCoe_sup_rootPair
    {V : Type*}
    [Fintype V]
    {G : SimpleGraph V}
    {root : V}
    (K : SimpleGraph {v : V // v ≠ root})
    (e f : G.edgeSet)
    [Fintype ((K.spanningCoe ⊔
      SimpleGraph.fromEdgeSet ({(e : Sym2 V), (f : Sym2 V)} : Set (Sym2 V))).neighborSet root)]
    (he : root ∈ (e : Sym2 V))
    (hf : root ∈ (f : Sym2 V))
    (hef : e ≠ f) :
    (K.spanningCoe ⊔
        SimpleGraph.fromEdgeSet ({(e : Sym2 V), (f : Sym2 V)} : Set (Sym2 V))).degree root = 2 := by
  classical
  let H : SimpleGraph V :=
    K.spanningCoe ⊔
      SimpleGraph.fromEdgeSet ({(e : Sym2 V), (f : Sym2 V)} : Set (Sym2 V))
  have hIncidence : H.incidenceFinset root = {(e : Sym2 V), (f : Sym2 V)} := by
    ext g
    rw [H.mem_incidenceFinset]
    change (g ∈ H.edgeSet ∧ root ∈ g) ↔ g ∈ {(e : Sym2 V), (f : Sym2 V)}
    constructor
    · rintro ⟨hg, hroot⟩
      rcases (mem_edgeSet_spanningCoe_sup_pair_iff K e f g).1 hg with
        ⟨d, hd, hdg⟩ | hge | hgf
      · subst g
        exact (root_not_mem_sym2Map_subtype d hroot).elim
      · simp [hge]
      · simp [hgf]
    · intro hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with hge | hgf
      · subst g
        exact ⟨(mem_edgeSet_spanningCoe_sup_pair_iff K e f e).2
          (Or.inr (Or.inl rfl)), he⟩
      · subst g
        exact ⟨(mem_edgeSet_spanningCoe_sup_pair_iff K e f f).2
          (Or.inr (Or.inr rfl)), hf⟩
  have hefVal : (e : Sym2 V) ≠ (f : Sym2 V) := by
    intro h
    exact hef (Subtype.ext h)
  -- Degree is the cardinality of the incidence finset, now visibly a two-element set.
  rw [← H.card_incidenceFinset_eq_degree, hIncidence]
  simp [hefVal]

end SimpleGraph
