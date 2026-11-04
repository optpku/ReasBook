/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_1.ch4_sec4_4_1_definition_4_4_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_3.ch4_sec4_4_3_definition_4_4_3_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SimpleGraph.Subgraph (IsMinimumWeightMatchingOfCardinality matchingWeight)
open SimpleGraph.Walk (IsMatchingAugmenting)

-- This file reuses the chapter's minimum-weight matching owner together with the chapter-local
-- augmenting-path owner `SimpleGraph.Walk.IsMatchingAugmenting`.

universe u

section Remark_4_21

variable {α : Type*}
variable {V : Type u} [Finite V]
variable {G : SimpleGraph V}
variable [Preorder α]

/-- An augmenting path from a size-`k` matching has minimum length when no augmenting path coming
from any size-`k` matching has smaller `ℓ`-length. -/
def IsMinimumLengthAugmentingPath
    (k : ℕ)
    (M : G.Subgraph)
    (ℓ : ∀ {u v : V}, G.Walk u v → α)
    {u v : V} (P : G.Walk u v) : Prop :=
  M.IsMatching ∧
    M.edgeSet.ncard = k ∧
    IsMatchingAugmenting M P ∧
    ∀ (M' : G.Subgraph) {u' v' : V} (P' : G.Walk u' v'),
      M'.IsMatching →
      M'.edgeSet.ncard = k →
      IsMatchingAugmenting M' P' →
      ℓ P ≤ ℓ P'

/-- Remark 4.21. Observation 4.22: if `M` already has minimum weight among the matchings of
cardinality `k`, `P` is minimum-length among the augmenting paths based at size-`k` matchings, and
every matching of cardinality `k + 1` admits the standard decomposition through some size-`k`
matching and an augmenting path for that matching, then the resulting matching `N` has minimum
weight among all matchings of `G` of cardinality `k + 1`. -/
theorem shortest_augmenting_path_extension_is_minimum_weight_matching
    {k : ℕ} {M N : G.Subgraph} {u v : V}
    [AddCommMonoid α] [AddLeftMono α] [AddRightMono α]
    (w : Sym2 V → α)
    (ℓ : ∀ {x y : V}, G.Walk x y → α)
    (P : G.Walk u v)
    (hM : IsMinimumWeightMatchingOfCardinality w k M)
    (hP : IsMinimumLengthAugmentingPath k M ℓ P)
    (hN_matching : N.IsMatching)
    (hN_card : N.edgeSet.ncard = k + 1)
    (hN_weight : matchingWeight w N = matchingWeight w M + ℓ P)
    (hcompare :
      ∀ N' : G.Subgraph,
        N'.IsMatching →
        N'.edgeSet.ncard = k + 1 →
          ∃ (u' v' : V) (P' : G.Walk u' v') (M' : G.Subgraph),
            IsMatchingAugmenting M' P' ∧
              M'.IsMatching ∧
              M'.edgeSet.ncard = k ∧
              matchingWeight w N' = matchingWeight w M' + ℓ P') :
    IsMinimumWeightMatchingOfCardinality w (k + 1) N := by
  rcases hP with ⟨_, _, _, hP_shortest⟩
  refine ⟨hN_matching, hN_card, ?_⟩
  intro N' hN'_matching hN'_card
  -- Compare the competing matching to `M` through its augmenting-path decomposition.
  obtain ⟨_, _, P', M', hP'_aug, hM'_matching, hM'_card, hN'_weight⟩ :=
    hcompare N' hN'_matching hN'_card
  -- Minimality of `M` and of `P` gives the two inequalities that drive the weight comparison.
  have hM_le : matchingWeight w M ≤ matchingWeight w M' :=
    hM.minimum M' hM'_matching hM'_card
  have hP_le : ℓ P ≤ ℓ P' :=
    hP_shortest M' P' hM'_matching hM'_card hP'_aug
  -- Rewriting both size-`k + 1` matchings by their comparison formulas reduces the claim to
  -- adding the size-`k` and path-length inequalities.
  calc
    matchingWeight w N = matchingWeight w M + ℓ P := hN_weight
    _ ≤ matchingWeight w M' + ℓ P' := add_le_add hM_le hP_le
    _ = matchingWeight w N' := hN'_weight.symm

end Remark_4_21
