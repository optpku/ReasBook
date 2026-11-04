/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_4.ch4_sec4_4_4_theorem_4_23
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_7.ch4_sec4_7_definition_4_7_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section Example_4_28

universe u

open SimpleGraph
open scoped BigOperators

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V)

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel G.Adj

-- Semantic search note: `lean_leansearch` was unavailable in this session, so this file uses
-- local inspection of `SimpleGraph.edgeFinset`, `SimpleGraph.edgeSet`, and `Sym2` APIs.

/-- The edges of `G` with one endpoint in `A` and the other in `B`. -/
noncomputable def edgesBetween (G : SimpleGraph V) (A B : Set V) : Finset (Sym2 V) :=
  letI : DecidablePred fun e ↦ ∃ u ∈ A, ∃ v ∈ B, s(u, v) = e := Classical.decPred _
  G.edgeFinset.filter fun e ↦ ∃ u ∈ A, ∃ v ∈ B, s(u, v) = e

/-- An edge lies in `edgesBetween G A B` exactly when it is an edge of `G` with one endpoint in
`A` and the other in `B`. -/
theorem mem_edgesBetween_iff {A B : Set V} {e : Sym2 V} :
    e ∈ edgesBetween G A B ↔ e ∈ G.edgeSet ∧ ∃ u ∈ A, ∃ v ∈ B, s(u, v) = e := by
  classical
  -- Unfold the filtered finset and rewrite finset membership as edge-set membership.
  unfold edgesBetween
  simp

/-- An edge of `G` lies in `edgesBetween G A B` exactly when its two endpoints are split between
`A` and `B`. -/
theorem mem_edgesBetween_edge_iff {A B : Set V} {e : G.edgeSet} :
    (e : Sym2 V) ∈ edgesBetween G A B ↔
      (e.1.out.1 ∈ A ∧ e.1.out.2 ∈ B) ∨ (e.1.out.2 ∈ A ∧ e.1.out.1 ∈ B) := by
  constructor
  · intro he
    rcases (mem_edgesBetween_iff G).1 he with ⟨_, u, huA, v, hvB, huv⟩
    have huv' : s(u, v) = s(e.1.out.1, e.1.out.2) := by
      exact huv.trans e.1.out_eq.symm
    rw [Sym2.eq_iff] at huv'
    rcases huv' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨huA, hvB⟩
    · exact Or.inr ⟨huA, hvB⟩
  · intro he
    rcases he with ⟨huA, hvB⟩ | ⟨hvA, huB⟩
    · exact (mem_edgesBetween_iff G).2 ⟨e.2, e.1.out.1, huA, e.1.out.2, hvB, e.1.out_eq⟩
    · refine (mem_edgesBetween_iff G).2 ?_
      refine ⟨e.2, e.1.out.2, hvA, e.1.out.1, huB, ?_⟩
      exact Sym2.eq_swap.trans e.1.out_eq

/-- The cut function of `G`, defined by the cardinality of the cut-edge finset `δ[G] S`. -/
noncomputable def cutFunction (G : SimpleGraph V) : Set V → ℕ :=
  fun S ↦ (δ[G] S).card

/-- The value of `cutFunction G` on `S` is the cardinality of `δ[G] S`. -/
theorem cutFunction_apply (S : Set V) :
    cutFunction G S = (δ[G] S).card := by
  -- This is the defining equation of `cutFunction`.
  rfl

/-- An edge-coordinate lies in `δ[G] S` exactly when its endpoints are separated by `S`. -/
theorem mem_cutEdgeFinset_edge_iff {S : Set V} {e : G.edgeSet} :
    e ∈ δ[G] S ↔
      (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.2 ∈ S ∧ e.1.out.1 ∉ S) := by
  constructor
  · intro he
    rcases (mem_cutEdgeFinset_iff G).1 he with ⟨u, huS, v, hvS, huv⟩
    have huv' : s(u, v) = s(e.1.out.1, e.1.out.2) := by
      exact huv.trans e.1.out_eq.symm
    rw [Sym2.eq_iff] at huv'
    rcases huv' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨huS, hvS⟩
    · exact Or.inr ⟨huS, hvS⟩
  · intro he
    rcases he with ⟨huS, hvS⟩ | ⟨hvS, huS⟩
    · exact (mem_cutEdgeFinset_iff G).2 ⟨e.1.out.1, huS, e.1.out.2, hvS, e.1.out_eq⟩
    · refine (mem_cutEdgeFinset_iff G).2 ?_
      refine ⟨e.1.out.2, hvS, e.1.out.1, huS, ?_⟩
      exact Sym2.eq_swap.trans e.1.out_eq

private def edgeEmbedding (G : SimpleGraph V) : G.edgeSet ↪ Sym2 V where
  toFun := fun e ↦ e
  inj' := fun _ _ h ↦ Subtype.ext h

/-- Helper for Example 4.28: counting a filtered subset of `G.edgeFinset` is the same as summing
its indicator over all edges of `G`. -/
theorem edgesBetween_card_eq_edge_indicator_sum (A B : Set V) :
    (edgesBetween G A B).card =
      ∑ e : G.edgeSet, if (e : Sym2 V) ∈ edgesBetween G A B then 1 else 0 := by
  classical
  let s : Finset G.edgeSet := Finset.univ.filter fun e ↦ (e : Sym2 V) ∈ edgesBetween G A B
  have hs : s.map (edgeEmbedding G) = edgesBetween G A B := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.1 he with ⟨x, hx, rfl⟩
      simpa [s] using hx
    · intro he
      rcases (mem_edgesBetween_iff G).1 he with ⟨heG, hAB⟩
      refine Finset.mem_map.2 ?_
      refine ⟨⟨e, heG⟩, ?_, rfl⟩
      simpa [s] using he
  calc
    (edgesBetween G A B).card = (s.map (edgeEmbedding G)).card := by rw [hs.symm]
    _ = s.card := Finset.card_map _
    _ = ∑ e : G.edgeSet, if (e : Sym2 V) ∈ edgesBetween G A B then 1 else 0 := by
      simpa [s] using
        (Finset.card_eq_sum_ite (Finset.subset_univ s) :
          s.card = ∑ e ∈ Finset.univ, if e ∈ s then 1 else 0)

/-- Helper for Example 4.28: the cut function is the sum of the cut-edge indicator over the edge
coordinates of `G`. -/
theorem cutFunction_as_cut_indicator_sum (S : Set V) :
    cutFunction G S =
      ∑ e : G.edgeSet, if e ∈ δ[G] S then 1 else 0 := by
  classical
  -- Rewrite the cut cardinality as a natural-valued indicator sum.
  rw [cutFunction_apply]
  simpa using
    (Finset.card_eq_sum_ite (Finset.subset_univ (δ[G] S)) :
      (δ[G] S).card = ∑ e ∈ Finset.univ, if e ∈ δ[G] S then 1 else 0)

/-- Helper for Example 4.28: one fixed edge contributes exactly the discrepancy term between the
four cut indicators. -/
theorem edge_cut_contribution_identity {e : G.edgeSet} (S T : Set V) :
    (if e ∈ δ[G] S then 1 else 0) + (if e ∈ δ[G] T then 1 else 0) =
      (if e ∈ δ[G] (S ∩ T) then 1 else 0) + (if e ∈ δ[G] (S ∪ T) then 1 else 0) +
        2 * (if (e : Sym2 V) ∈ edgesBetween G (T \ S) (S \ T) then 1 else 0) := by
  -- Reduce every edge-membership test to endpoint membership and split on the four booleans.
  have hS :
      e ∈ δ[G] S ↔
        (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.2 ∈ S ∧ e.1.out.1 ∉ S) :=
    mem_cutEdgeFinset_edge_iff G
  have hT :
      e ∈ δ[G] T ↔
        (e.1.out.1 ∈ T ∧ e.1.out.2 ∉ T) ∨ (e.1.out.2 ∈ T ∧ e.1.out.1 ∉ T) :=
    mem_cutEdgeFinset_edge_iff G
  have hInter :
      e ∈ δ[G] (S ∩ T) ↔
        (e.1.out.1 ∈ S ∩ T ∧ e.1.out.2 ∉ S ∩ T) ∨
          (e.1.out.2 ∈ S ∩ T ∧ e.1.out.1 ∉ S ∩ T) :=
    mem_cutEdgeFinset_edge_iff G
  have hUnion :
      e ∈ δ[G] (S ∪ T) ↔
        (e.1.out.1 ∈ S ∪ T ∧ e.1.out.2 ∉ S ∪ T) ∨
          (e.1.out.2 ∈ S ∪ T ∧ e.1.out.1 ∉ S ∪ T) :=
    mem_cutEdgeFinset_edge_iff G
  have hDiff :
      (e : Sym2 V) ∈ edgesBetween G (T \ S) (S \ T) ↔
        (e.1.out.1 ∈ T \ S ∧ e.1.out.2 ∈ S \ T) ∨
          (e.1.out.2 ∈ T \ S ∧ e.1.out.1 ∈ S \ T) :=
    mem_edgesBetween_edge_iff G
  by_cases huS : e.1.out.1 ∈ S <;> by_cases hvS : e.1.out.2 ∈ S <;>
      by_cases huT : e.1.out.1 ∈ T <;> by_cases hvT : e.1.out.2 ∈ T
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]
  · simp [hS, hT, hInter, hUnion, hDiff, huS, hvS, huT, hvT, Set.mem_diff]

/-- Example 4.28 (1): for any vertex sets `S` and `T`, the cut function satisfies the counting
identity
`|δ(S)| + |δ(T)| = |δ(S ∩ T)| + |δ(S ∪ T)| + 2 |(T \ S : S \ T)|`. -/
theorem cutFunction_add_eq_inter_union_add_two_mul_card_edgesBetween_diff
    (S T : Set V) :
    cutFunction G S + cutFunction G T =
      cutFunction G (S ∩ T) + cutFunction G (S ∪ T) +
        2 * (edgesBetween G (T \ S) (S \ T)).card := by
  -- Count every term by summing the corresponding indicator over the edge coordinates of `G`.
  calc
    cutFunction G S + cutFunction G T
      = (∑ e : G.edgeSet, if e ∈ δ[G] S then 1 else 0) +
          ∑ e : G.edgeSet, if e ∈ δ[G] T then 1 else 0 := by
          rw [cutFunction_as_cut_indicator_sum G S]
          rw [cutFunction_as_cut_indicator_sum G T]
    _ = ∑ e : G.edgeSet, ((if e ∈ δ[G] S then 1 else 0) + (if e ∈ δ[G] T then 1 else 0)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ e : G.edgeSet,
          ((if e ∈ δ[G] (S ∩ T) then 1 else 0) + (if e ∈ δ[G] (S ∪ T) then 1 else 0) +
            2 * (if (e : Sym2 V) ∈ edgesBetween G (T \ S) (S \ T) then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro e he
          have hcontrib :
              (if e ∈ δ[G] S then 1 else 0) + (if e ∈ δ[G] T then 1 else 0) =
                (if e ∈ δ[G] (S ∩ T) then 1 else 0) + (if e ∈ δ[G] (S ∪ T) then 1 else 0) +
                  2 * (if (e : Sym2 V) ∈ edgesBetween G (T \ S) (S \ T) then 1 else 0) :=
            edge_cut_contribution_identity G S T
          simpa using hcontrib
    _ = (∑ e : G.edgeSet, if e ∈ δ[G] (S ∩ T) then 1 else 0) +
          (∑ e : G.edgeSet, if e ∈ δ[G] (S ∪ T) then 1 else 0) +
            2 * ∑ e : G.edgeSet,
              (if (e : Sym2 V) ∈ edgesBetween G (T \ S) (S \ T) then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = cutFunction G (S ∩ T) + cutFunction G (S ∪ T) +
          2 * (edgesBetween G (T \ S) (S \ T)).card := by
          rw [← cutFunction_as_cut_indicator_sum G (S ∩ T)]
          rw [← cutFunction_as_cut_indicator_sum G (S ∪ T)]
          rw [← edgesBetween_card_eq_edge_indicator_sum G (T \ S) (S \ T)]

/-- Example 4.28 (2): the cut function of a graph is submodular. -/
theorem cutFunction_submodular : Submodular (cutFunction G) := by
  intro S T
  change cutFunction G (S ∩ T) + cutFunction G (S ∪ T) ≤ cutFunction G S + cutFunction G T
  -- The counting identity has a nonnegative correction term, so dropping it gives submodularity.
  have hEq := cutFunction_add_eq_inter_union_add_two_mul_card_edgesBetween_diff G S T
  have hle :
      cutFunction G (S ∩ T) + cutFunction G (S ∪ T) ≤
        cutFunction G (S ∩ T) + cutFunction G (S ∪ T) +
          2 * (edgesBetween G (T \ S) (S \ T)).card := by
    exact Nat.le_add_right _ _
  rw [← hEq] at hle
  exact hle

end Example_4_28
