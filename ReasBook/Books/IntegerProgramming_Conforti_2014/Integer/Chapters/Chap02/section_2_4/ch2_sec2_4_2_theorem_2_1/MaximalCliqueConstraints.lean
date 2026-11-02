module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_1_proposition_2_5.SetPacking
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_2_definition_2_14.CliqueMatrix

open scoped BigOperators

public section

namespace Finset

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_theorem_2_1/MaximalCliqueConstraints.lean:
the sum of an integer-valued zero-one function is the number of its nonzero entries. -/
private lemma sum_eq_card_filter_ne_zero_of_zero_one
    {V : Type*} (K : Finset V) (x : V → ℤ)
    (hbin : ∀ v ∈ K, x v = 0 ∨ x v = 1) :
    K.sum x = ((K.filter fun v ↦ x v ≠ 0).card : ℤ) := by
  classical
  -- Replace each binary coordinate by the indicator that it is nonzero.
  calc
    K.sum x = ∑ v ∈ K, if x v ≠ 0 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rcases hbin v hv with hv0 | hv1
      · simp [hv0]
      · simp [hv1]
    _ = ((K.filter fun v ↦ x v ≠ 0).card : ℤ) := Finset.sum_boole _ _

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_theorem_2_1/MaximalCliqueConstraints.lean:
a zero-one integer sum is at most one exactly when its nonzero support has cardinality at most
one. -/
private lemma sum_le_one_iff_card_filter_ne_zero_le_one
    {V : Type*} (K : Finset V) (x : V → ℤ)
    (hbin : ∀ v ∈ K, x v = 0 ∨ x v = 1) :
    K.sum x ≤ 1 ↔ (K.filter fun v ↦ x v ≠ 0).card ≤ 1 := by
  -- Normalize the sum, then transport the inequality across the integer cast.
  rw [sum_eq_card_filter_ne_zero_of_zero_one K x hbin]
  norm_cast

end Finset

namespace SimpleGraph

universe u

variable {V : Type u} [Fintype V]

/-- The binary integer vectors on `V` satisfying all maximal-clique inequalities of `G`. -/
def maximalCliqueConstraintFamily (G : SimpleGraph V) : Set (V → ℤ) :=
  {x | (∀ v, x v = 0 ∨ x v = 1) ∧ ∀ K ∈ G.maximalCliques, K.sum x ≤ 1}

/-- Membership in `maximalCliqueConstraintFamily G` is exactly the binary condition together with
all maximal-clique inequalities of `G`. -/
theorem mem_maximalCliqueConstraintFamily_iff
    {G : SimpleGraph V} {x : V → ℤ} :
    x ∈ G.maximalCliqueConstraintFamily ↔
      (∀ v, x v = 0 ∨ x v = 1) ∧
        ∀ K ∈ G.maximalCliques, K.sum x ≤ 1 := by
  -- Unfolding exposes exactly the advertised binary and clique conditions.
  rfl

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_theorem_2_1/MaximalCliqueConstraints.lean:
every clique in a finite graph is contained in a maximal clique. -/
private lemma exists_maximalClique_superset
    (G : SimpleGraph V) (K : Finset V) (hK : G.IsClique (K : Set V)) :
    ∃ L ∈ G.maximalCliques, K ⊆ L := by
  classical
  -- Maximize the clique in the finite inclusion poset of vertex sets.
  obtain ⟨S, hKS, hSmax⟩ :=
    @Finite.exists_le_maximal (Set V) _ _ G.IsClique (K : Set V) hK
  have hSmaxFin : Maximal G.IsClique (S.toFinset : Set V) := by
    simpa using hSmax
  refine ⟨S.toFinset, (G.mem_maximalCliques_iff S.toFinset).2 hSmaxFin, ?_⟩
  -- Translate the set inclusion supplied by maximality to finset inclusion.
  intro v hv
  simpa using hKS hv

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_theorem_2_1/MaximalCliqueConstraints.lean:
a binary support is independent exactly when every maximal-clique sum is at most one. -/
private lemma isIndepSet_support_iff_maximalClique_sum_le_one
    (G : SimpleGraph V) (x : V → ℤ) (hbin : ∀ v, x v = 0 ∨ x v = 1) :
    G.IsIndepSet (Function.support x) ↔
      ∀ K ∈ G.maximalCliques, K.sum x ≤ 1 := by
  classical
  constructor
  · intro hind K hKmax
    have hK : G.IsClique (K : Set V) :=
      ((G.mem_maximalCliques_iff K).1 hKmax).1
    -- A clique and an independent support cannot share two distinct vertices.
    have hcard : (K.filter fun v ↦ x v ≠ 0).card ≤ 1 := by
      refine Finset.card_le_one_iff.2 ?_
      intro a b ha hb
      obtain ⟨haK, hax⟩ := Finset.mem_filter.1 ha
      obtain ⟨hbK, hbx⟩ := Finset.mem_filter.1 hb
      by_contra hab
      exact (hind hax hbx hab) (hK haK hbK hab)
    exact (Finset.sum_le_one_iff_card_filter_ne_zero_le_one K x
      (fun v _ ↦ hbin v)).2 hcard
  · intro hclique a ha b hb hab habAdj
    -- Extend the adjacent support pair to a maximal clique.
    have hpairSet : G.IsClique ({a, b} : Set V) :=
      SimpleGraph.isClique_pair.2 (fun _ ↦ habAdj)
    have hpair : G.IsClique (({a, b} : Finset V) : Set V) := by
      simpa using hpairSet
    obtain ⟨K, hKmax, hpairs⟩ := exists_maximalClique_superset G {a, b} hpair
    have hcard : (K.filter fun v ↦ x v ≠ 0).card ≤ 1 :=
      (Finset.sum_le_one_iff_card_filter_ne_zero_le_one K x
        (fun v _ ↦ hbin v)).1 (hclique K hKmax)
    have haPair : a ∈ ({a, b} : Finset V) := Finset.mem_insert_self a {b}
    have hbPair : b ∈ ({a, b} : Finset V) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    have haK : a ∈ K := hpairs haPair
    have hbK : b ∈ K := hpairs hbPair
    have haFilter : a ∈ K.filter fun v ↦ x v ≠ 0 :=
      Finset.mem_filter.2 ⟨haK, ha⟩
    have hbFilter : b ∈ K.filter fun v ↦ x v ≠ 0 :=
      Finset.mem_filter.2 ⟨hbK, hb⟩
    -- Cardinality at most one forces the adjacent support vertices to coincide.
    exact hab ((Finset.card_le_one_iff.1 hcard) haFilter hbFilter)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_theorem_2_1/MaximalCliqueConstraints.lean:
The stable-set family of a finite graph agrees with its binary maximal-clique-constraint family. -/
theorem stableSetFamily_eq_maximalCliqueConstraintFamily
    (G : SimpleGraph V) :
    G.stableSetFamily = G.maximalCliqueConstraintFamily := by
  -- Compare the families through their membership APIs and the support/clique bridge.
  ext x
  rw [mem_stableSetFamily_iff, mem_maximalCliqueConstraintFamily_iff]
  exact and_congr_right fun hbin ↦
    isIndepSet_support_iff_maximalClique_sum_le_one G x hbin

end SimpleGraph
