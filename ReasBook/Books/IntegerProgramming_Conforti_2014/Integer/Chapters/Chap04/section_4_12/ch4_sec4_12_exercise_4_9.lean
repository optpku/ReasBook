/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_corollary_4_7

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style owner scan:
-- * source-facing owner in this file: `IsLaminarSubsetFamily`
-- * canonical matrix owner reused here: Chapter 2's `matrixOfRowSupports`
-- * canonical total-unimodularity owner: `Matrix.IsTotallyUnimodular`
-- The local subset-family incidence matrix was a duplicate of `matrixOfRowSupports`, so this file
-- now states the matrix result directly for that upstream owner.

open scoped BigOperators

section Exercise49

universe u

variable {V : Type} [DecidableEq V]

/-- A finite family of subsets of `V` is laminar when any two members with nonempty intersection
are nested. -/
def IsLaminarSubsetFamily (𝒮 : Finset (Finset V)) : Prop :=
  ∀ ⦃S T : Finset V⦄, S ∈ 𝒮 → T ∈ 𝒮 → (S ∩ T).Nonempty → S ⊆ T ∨ T ⊆ S

/-- Helper for Exercise 4.9: the maximal nonempty members of a finite family. -/
private def maximal_nonempty_members (𝒮 : Finset (Finset V)) : Finset (Finset V) :=
  (𝒮.erase ∅).filter (fun R ↦ ∀ U ∈ 𝒮.erase ∅, R ⊂ U → False)

/-- Helper for Exercise 4.9: every nonempty member lies inside a maximal nonempty member. -/
private lemma exists_maximal_nonempty_member_containing
    (𝒮 : Finset (Finset V))
    {S : Finset V}
    (hS : S ∈ 𝒮.erase ∅) :
    ∃ R ∈ maximal_nonempty_members 𝒮, S ⊆ R := by
  classical
  let supersets : Finset (Finset V) := (𝒮.erase ∅).filter (fun U ↦ S ⊆ U)
  have hSupersets : supersets.Nonempty := by
    -- The seed set `S` itself belongs to the family of supersets.
    refine ⟨S, Finset.mem_filter.2 ⟨hS, subset_rfl⟩⟩
  let cardValues : Finset ℕ := supersets.image fun U ↦ U.card
  have hCardValues : cardValues.Nonempty := by
    rcases hSupersets with ⟨U, hU⟩
    exact ⟨U.card, Finset.mem_image.2 ⟨U, hU, rfl⟩⟩
  let c := cardValues.max' hCardValues
  have hcMem : c ∈ cardValues := Finset.max'_mem _ _
  rcases Finset.mem_image.1 hcMem with ⟨R, hR, hRc⟩
  have hmaxR : ∀ U ∈ supersets, U.card ≤ R.card := by
    intro U hU
    have hUCard : U.card ∈ cardValues := Finset.mem_image.2 ⟨U, hU, rfl⟩
    calc
      U.card ≤ c := Finset.le_max' _ _ hUCard
      _ = R.card := hRc.symm
  refine ⟨R, ?_, (Finset.mem_filter.1 hR).2⟩
  refine Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hR).1, ?_⟩
  intro U hU hRU
  -- Any strict larger superset of `R` would still lie in the supersets family, contradicting the
  -- maximal-cardinality choice of `R`.
  have hUSupersets : U ∈ supersets := by
    refine Finset.mem_filter.2 ⟨hU, ?_⟩
    exact Set.Subset.trans ((Finset.mem_filter.1 hR).2) hRU.1
  have hCardLe : U.card ≤ R.card := hmaxR U hUSupersets
  have hCardLt : R.card < U.card := Finset.card_lt_card hRU
  exact (Nat.not_lt_of_ge hCardLe hCardLt).elim

/-- Helper for Exercise 4.9: distinct maximal nonempty members of a laminar family are disjoint. -/
private lemma maximal_nonempty_members_pairwise_disjoint
    (𝒮 : Finset (Finset V))
    (h𝒮 : IsLaminarSubsetFamily 𝒮) :
    Set.PairwiseDisjoint
      (((maximal_nonempty_members 𝒮 : Finset (Finset V)) : Set (Finset V)))
      (fun R ↦ R) := by
  intro R hR T hT hRT
  refine Finset.disjoint_left.2 ?_
  intro x hxR hxT
  have hRerase : R ∈ 𝒮.erase ∅ := (Finset.mem_filter.1 hR).1
  have hTerase : T ∈ 𝒮.erase ∅ := (Finset.mem_filter.1 hT).1
  have hRmem : R ∈ 𝒮 := (Finset.mem_erase.1 hRerase).2
  have hTmem : T ∈ 𝒮 := (Finset.mem_erase.1 hTerase).2
  have hInt : (R ∩ T).Nonempty := ⟨x, Finset.mem_inter.2 ⟨hxR, hxT⟩⟩
  rcases h𝒮 hRmem hTmem hInt with hRTSub | hTRSub
  · -- Overlap forces comparability, and maximality rules out a strict containment.
    have hStrict : R ⊂ T := ⟨hRTSub, by
      intro hTR
      exact hRT (Finset.Subset.antisymm hRTSub hTR)⟩
    exact ((Finset.mem_filter.1 hR).2 T hTerase hStrict).elim
  · -- The symmetric strict-containment case is ruled out the same way.
    have hStrict : T ⊂ R := ⟨hTRSub, by
      intro hRT'
      exact hRT (Finset.Subset.antisymm hRT' hTRSub)⟩
    exact ((Finset.mem_filter.1 hT).2 R hRerase hStrict).elim

/-- Helper for Exercise 4.9: after deleting `∅`, the family splits into the branches under its
maximal nonempty members, and those branches are pairwise disjoint. -/
private lemma maximal_nonempty_members_biUnion_eq_erase_empty
    (𝒮 : Finset (Finset V))
    (h𝒮 : IsLaminarSubsetFamily 𝒮) :
    let roots := maximal_nonempty_members 𝒮
    let branch := fun R ↦ (𝒮.erase ∅).filter (fun S ↦ S ⊆ R)
    (𝒮.erase ∅ = roots.biUnion branch) ∧
      Set.PairwiseDisjoint (((roots : Finset (Finset V)) : Set (Finset V))) branch ∧
      Set.PairwiseDisjoint (((roots : Finset (Finset V)) : Set (Finset V))) (fun R ↦ R) := by
  classical
  dsimp
  have hRoots :
      Set.PairwiseDisjoint
        (((maximal_nonempty_members 𝒮 : Finset (Finset V)) : Set (Finset V)))
        (fun R ↦ R) :=
    maximal_nonempty_members_pairwise_disjoint 𝒮 h𝒮
  refine ⟨?_, ?_, hRoots⟩
  · -- Every nonempty family member belongs to the branch below some maximal nonempty root.
    ext S
    constructor
    · intro hS
      rcases exists_maximal_nonempty_member_containing 𝒮 hS with ⟨R, hR, hSR⟩
      exact Finset.mem_biUnion.2 ⟨R, hR, Finset.mem_filter.2 ⟨hS, hSR⟩⟩
    · intro hS
      rcases Finset.mem_biUnion.1 hS with ⟨R, -, hSR⟩
      exact (Finset.mem_filter.1 hSR).1
  · -- Two distinct roots have disjoint underlying sets, so no nonempty family member can lie in
    -- both corresponding branches.
    intro R hR T hT hRT
    refine Finset.disjoint_left.2 ?_
    intro S hSR hST
    have hSNonempty : S.Nonempty := by
      exact Finset.nonempty_iff_ne_empty.2 (Finset.mem_erase.1 (Finset.mem_filter.1 hSR).1).1
    rcases hSNonempty with ⟨x, hxS⟩
    have hxR : x ∈ R := (Finset.mem_filter.1 hSR).2 hxS
    have hxT : x ∈ T := (Finset.mem_filter.1 hST).2 hxS
    exact (Finset.disjoint_left.1 (hRoots hR hT hRT)) hxR hxT

/-- Helper for Exercise 4.9: the disjoint maximal nonempty roots occupy at most the whole ground
set. -/
private lemma sum_card_maximal_nonempty_members_le_card
    (N : Finset V)
    (𝒮 : Finset (Finset V))
    (h𝒮N : ∀ ⦃S : Finset V⦄, S ∈ 𝒮 → S ⊆ N)
    (h𝒮 : IsLaminarSubsetFamily 𝒮) :
    ∑ R ∈ maximal_nonempty_members 𝒮, R.card ≤ N.card := by
  classical
  have hRoots :
      Set.PairwiseDisjoint
        (((maximal_nonempty_members 𝒮 : Finset (Finset V)) : Set (Finset V)))
        (fun R ↦ R) :=
    maximal_nonempty_members_pairwise_disjoint 𝒮 h𝒮
  have hUnionSub :
      (maximal_nonempty_members 𝒮).biUnion id ⊆ N := by
    intro x hx
    rcases Finset.mem_biUnion.1 hx with ⟨R, hR, hxR⟩
    exact h𝒮N (Finset.mem_erase.1 (Finset.mem_filter.1 hR).1).2 hxR
  -- Rewrite the sum of root cardinalities as the cardinality of their disjoint union.
  calc
    ∑ R ∈ maximal_nonempty_members 𝒮, R.card =
        ((maximal_nonempty_members 𝒮).biUnion id).card := by
          simpa using (Finset.card_biUnion (s := maximal_nonempty_members 𝒮) (t := id) hRoots).symm
    _ ≤ N.card := Finset.card_le_card hUnionSub

/-- Helper for Exercise 4.9: removing a root `R` turns the remaining laminar family into the
disjoint union of the branches below its maximal nonempty members. -/
private lemma cardEraseRoot_eq_sum_childBranchCards
    (T : Finset (Finset V)) {R : Finset V}
    (hEmpty : ∅ ∉ T)
    (hT : IsLaminarSubsetFamily T) :
    let children := maximal_nonempty_members (T.erase R)
    let branch := fun C ↦ (T.erase R).filter (fun S ↦ S ⊆ C)
    (T.erase R).card = ∑ C ∈ children, (branch C).card := by
  classical
  dsimp
  have hEmptyErase : ∅ ∉ T.erase R := by
    simp [hEmpty]
  have hEraseLaminar : IsLaminarSubsetFamily (T.erase R) := by
    -- Laminarity restricts directly to the family with the root removed.
    intro S U hS hU hInt
    exact hT (Finset.mem_erase.1 hS).2 (Finset.mem_erase.1 hU).2 hInt
  rcases maximal_nonempty_members_biUnion_eq_erase_empty (𝒮 := T.erase R) hEraseLaminar with
    ⟨hDecomp, hPairwise, _⟩
  have hDecomp' :
      T.erase R =
        (maximal_nonempty_members (T.erase R)).biUnion
          (fun C ↦ (T.erase R).filter (fun S ↦ S ⊆ C)) := by
    -- The erased family already has no empty member, so the existing decomposition applies
    -- without changing the carrier.
    simpa [hEmptyErase] using hDecomp
  have hPairwise' :
      Set.PairwiseDisjoint
        ((((maximal_nonempty_members (T.erase R)) : Finset (Finset V)) : Set (Finset V)))
        (fun C ↦ (T.erase R).filter (fun S ↦ S ⊆ C)) := by
    -- The disjointness statement simplifies in the same way.
    simpa [hEmptyErase] using hPairwise
  calc
    (T.erase R).card =
        ((maximal_nonempty_members (T.erase R)).biUnion
          (fun C ↦ (T.erase R).filter (fun S ↦ S ⊆ C))).card := by
            exact congrArg Finset.card hDecomp'
    _ = ∑ C ∈ maximal_nonempty_members (T.erase R),
          ((T.erase R).filter (fun S ↦ S ⊆ C)).card := by
          simpa using
            (Finset.card_biUnion
              (s := maximal_nonempty_members (T.erase R))
              (t := fun C ↦ (T.erase R).filter (fun S ↦ S ⊆ C))
              hPairwise')

/-- Helper for Exercise 4.9: every maximal nonempty member of `T.erase R` is a strict subset of
the original root `R`. -/
private lemma maximalNonemptyMember_eraseRoot_strictSubset
    (T : Finset (Finset V)) {R C : Finset V}
    (hTR : ∀ ⦃S : Finset V⦄, S ∈ T → S ⊆ R)
    (hC : C ∈ maximal_nonempty_members (T.erase R)) :
    C ⊂ R := by
  have hCErase : C ∈ ((T.erase R).erase ∅) := (Finset.mem_filter.1 hC).1
  have hCTerase : C ∈ T.erase R := (Finset.mem_erase.1 hCErase).2
  have hCT : C ∈ T := (Finset.mem_erase.1 hCTerase).2
  have hCR : C ⊆ R := hTR hCT
  refine ⟨hCR, ?_⟩
  intro hRC
  -- If `R ⊆ C` as well, then `C = R`, contradicting that `R` was erased from the family.
  have hEq : C = R := Finset.Subset.antisymm hCR hRC
  exact (Finset.mem_erase.1 hCTerase).1 hEq

/-- Helper for Exercise 4.9: adding the number of summands back to
`∑ C ∈ children, (2 * C.card - 1)` recovers `2 * ∑ C ∈ children, C.card`. -/
private lemma sum_two_mul_card_sub_one_add_card
    (children : Finset (Finset V))
    (hChildren : ∀ C ∈ children, C.Nonempty) :
    (∑ C ∈ children, (2 * C.card - 1)) + children.card =
      2 * ∑ C ∈ children, C.card := by
  -- Combine the constant `+1` contributions into a single sum and then factor out the leading `2`.
  calc
    (∑ C ∈ children, (2 * C.card - 1)) + children.card =
        (∑ C ∈ children, (2 * C.card - 1)) + ∑ C ∈ children, 1 := by
          simp
    _ = ∑ C ∈ children, ((2 * C.card - 1) + 1) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ C ∈ children, 2 * C.card := by
          refine Finset.sum_congr rfl ?_
          intro C hC
          have hCcardPos : 1 ≤ C.card := (hChildren C hC).card_pos
          omega
    _ = 2 * ∑ C ∈ children, C.card := by
          symm
          exact Finset.mul_sum children (fun C ↦ C.card) 2

/-- Helper for Exercise 4.9: a laminar family rooted at a nonempty set `R` has at most
`2 * R.card - 1` members. -/
private lemma rootedLaminarSubsetFamily_card_le_two_mul_card_sub_one
    (R : Finset V) (T : Finset (Finset V))
    (hR : R.Nonempty)
    (hroot : R ∈ T)
    (hTR : ∀ ⦃S : Finset V⦄, S ∈ T → S ⊆ R)
    (hEmpty : ∅ ∉ T)
    (hT : IsLaminarSubsetFamily T) :
    T.card ≤ 2 * R.card - 1 := by
  classical
  revert hR hroot hTR hEmpty hT T
  refine Finset.strongInductionOn R ?_
  intro R ih T hR hroot hTR hEmpty hT
  let children : Finset (Finset V) := maximal_nonempty_members (T.erase R)
  let branch : Finset V → Finset (Finset V) := fun C ↦ (T.erase R).filter (fun S ↦ S ⊆ C)
  have hEraseCard :
      (T.erase R).card = ∑ C ∈ children, (branch C).card := by
    -- Normalize the erased family into a sum of the branch cardinalities.
    simpa [children, branch] using
      cardEraseRoot_eq_sum_childBranchCards (T := T) (R := R) hEmpty hT
  have hEraseLaminar : IsLaminarSubsetFamily (T.erase R) := by
    -- Laminarity is inherited by every subfamily defined by erasing one member.
    intro S U hS hU hInt
    exact hT (Finset.mem_erase.1 hS).2 (Finset.mem_erase.1 hU).2 hInt
  have hEraseSub : ∀ ⦃S : Finset V⦄, S ∈ T.erase R → S ⊆ R := by
    -- Every remaining member still lies inside the distinguished root.
    intro S hS
    exact hTR (Finset.mem_erase.1 hS).2
  have hSumChildrenCards :
      ∑ C ∈ children, C.card ≤ R.card := by
    -- The children are disjoint subsets of `R`, so their total size is bounded by `|R|`.
    simpa [children] using
      sum_card_maximal_nonempty_members_le_card
        (N := R) (𝒮 := T.erase R)
        (h𝒮N := by
          intro S hS
          exact hEraseSub hS)
        (h𝒮 := hEraseLaminar)
  have hChildNonempty :
      ∀ C ∈ children, C.Nonempty := by
    intro C hC
    have hCmem : C ∈ maximal_nonempty_members (T.erase R) := by
      simpa [children] using hC
    exact Finset.nonempty_iff_ne_empty.2 (Finset.mem_erase.1 (Finset.mem_filter.1 hCmem).1).1
  have hChildBranchBound :
      ∀ C ∈ children, (branch C).card ≤ 2 * C.card - 1 := by
    intro C hC
    have hCmem : C ∈ maximal_nonempty_members (T.erase R) := by
      simpa [children] using hC
    have hCStrict : C ⊂ R :=
      maximalNonemptyMember_eraseRoot_strictSubset
        (T := T) (R := R) hTR hCmem
    have hCNonempty : C.Nonempty := by
      -- Maximal nonempty members are, by definition, nonempty.
      exact hChildNonempty C hC
    have hCRoot : C ∈ branch C := by
      -- The root of a branch belongs to its own branch.
      have hCTerase : C ∈ T.erase R := by
        exact (Finset.mem_erase.1 (Finset.mem_filter.1 hCmem).1).2
      exact Finset.mem_filter.2 ⟨hCTerase, subset_rfl⟩
    have hBranchSub : ∀ ⦃S : Finset V⦄, S ∈ branch C → S ⊆ C := by
      -- Every member of the branch is filtered by containment in `C`.
      intro S hS
      exact (Finset.mem_filter.1 hS).2
    have hBranchEmpty : ∅ ∉ branch C := by
      -- The original family has no empty member, so neither does any branch.
      intro hEmptyBranch
      exact hEmpty ((Finset.mem_erase.1 (Finset.mem_filter.1 hEmptyBranch).1).2)
    have hBranchLam : IsLaminarSubsetFamily (branch C) := by
      -- Laminarity also restricts to each branch.
      intro S U hS hU hInt
      exact hT
        ((Finset.mem_erase.1 (Finset.mem_filter.1 hS).1).2)
        ((Finset.mem_erase.1 (Finset.mem_filter.1 hU).1).2)
        hInt
    -- The induction hypothesis applies because every branch root is a strict subset of `R`.
    exact ih C hCStrict (branch C) hCNonempty hCRoot hBranchSub hBranchEmpty hBranchLam
  have hBranchBoundSum :
      ∑ C ∈ children, (branch C).card ≤ ∑ C ∈ children, (2 * C.card - 1) := by
    -- Sum the branchwise rooted bounds over all children.
    refine Finset.sum_le_sum ?_
    intro C hC
    exact hChildBranchBound C hC
  by_cases hChildrenEmpty : children = ∅
  · have hEraseCardZero : (T.erase R).card = 0 := by
      -- If there are no children, then the erased family is empty.
      simpa [hChildrenEmpty] using hEraseCard
    have hTCard : T.card = 1 := by
      -- The family then consists only of the root `R`.
      have hCard := Finset.card_erase_add_one hroot
      omega
    have hRCardPos : 1 ≤ R.card := hR.card_pos
    omega
  · have hChildrenNonempty : children.Nonempty := Finset.card_pos.1 (Nat.pos_of_ne_zero fun h0 =>
      hChildrenEmpty (Finset.card_eq_zero.1 h0))
    by_cases hChildrenOne : children.card = 1
    · rcases Finset.card_eq_one.1 hChildrenOne with ⟨C, hChildrenEq⟩
      have hC : C ∈ children := by
        simpa [hChildrenEq]
      have hEraseCardSingle : (T.erase R).card = (branch C).card := by
        -- With one child, the erased family is exactly that one branch.
        simpa [hChildrenEq] using hEraseCard
      have hCStrict : C ⊂ R :=
        maximalNonemptyMember_eraseRoot_strictSubset
          (T := T) (R := R) hTR (by simpa [children] using hC)
      have hCcardLt : C.card < R.card := Finset.card_lt_card hCStrict
      have hBranchBound : (branch C).card ≤ 2 * C.card - 1 := hChildBranchBound C hC
      have hTCard : T.card = (branch C).card + 1 := by
        -- Add the root `R` back to the single branch.
        have hCard := Finset.card_erase_add_one hroot
        omega
      omega
    · have hChildrenTwo : 2 ≤ children.card := by
        have hChildrenCardPos : 1 ≤ children.card := hChildrenNonempty.card_pos
        omega
      have hWeightedBound :
          ∑ C ∈ children, (2 * C.card - 1) ≤ 2 * R.card - 2 := by
        -- At least two children pay for the `- children.card` term in the weighted sum.
        have hTwice :
            2 * (∑ C ∈ children, C.card) ≤ 2 * R.card :=
          Nat.mul_le_mul_left 2 hSumChildrenCards
        have hWeighted :
            (∑ C ∈ children, (2 * C.card - 1)) + children.card =
              2 * (∑ C ∈ children, C.card) := by
          simpa using sum_two_mul_card_sub_one_add_card children hChildNonempty
        omega
      have hEraseBound : (T.erase R).card ≤ 2 * R.card - 2 := by
        -- Summing the branch bounds gives the desired estimate for the erased family.
        calc
          (T.erase R).card = ∑ C ∈ children, (branch C).card := hEraseCard
          _ ≤ ∑ C ∈ children, (2 * C.card - 1) := hBranchBoundSum
          _ ≤ 2 * R.card - 2 := hWeightedBound
      have hCard := Finset.card_erase_add_one hroot
      have hRCardPos : 1 ≤ R.card := hR.card_pos
      have hTwoRCardPos : 2 ≤ 2 * R.card := by
        omega
      calc
        T.card = (T.erase R).card + 1 := by omega
        _ ≤ (2 * R.card - 2) + 1 := Nat.add_le_add_right hEraseBound 1
        _ = 2 * R.card - 1 := by
          omega

/-- Helper for Exercise 4.9: if the top-level maximal nonempty roots are present, then deleting
`∅` leaves at most `2 * N.card - 1` sets. -/
private lemma laminarEraseEmpty_card_le_two_mul_card_sub_one_of_nonemptyRoots
    (N : Finset V)
    (𝒮 : Finset (Finset V))
    (hRoots : (maximal_nonempty_members 𝒮).Nonempty)
    (h𝒮N : ∀ ⦃S : Finset V⦄, S ∈ 𝒮 → S ⊆ N)
    (h𝒮 : IsLaminarSubsetFamily 𝒮) :
    (𝒮.erase ∅).card ≤ 2 * N.card - 1 := by
  classical
  let roots : Finset (Finset V) := maximal_nonempty_members 𝒮
  let branch : Finset V → Finset (Finset V) := fun R ↦ (𝒮.erase ∅).filter (fun S ↦ S ⊆ R)
  have hRoots' : roots.Nonempty := by
    simpa [roots] using hRoots
  rcases maximal_nonempty_members_biUnion_eq_erase_empty (𝒮 := 𝒮) h𝒮 with
    ⟨hDecomp, hPairwise, _⟩
  have hEraseCard :
      (𝒮.erase ∅).card = ∑ R ∈ roots, (branch R).card := by
    -- Rewrite the nonempty part of the family as the disjoint union of its top-level rooted
    -- components.
    calc
      (𝒮.erase ∅).card = (roots.biUnion branch).card := by
        simpa [roots, branch] using congrArg Finset.card hDecomp
      _ = ∑ R ∈ roots, (branch R).card := by
        simpa [roots, branch] using
          (Finset.card_biUnion (s := roots) (t := branch) (by simpa [roots, branch] using hPairwise))
  have hRootCards : ∑ R ∈ roots, R.card ≤ N.card := by
    -- The top-level roots are disjoint subsets of the ground set `N`.
    simpa [roots] using sum_card_maximal_nonempty_members_le_card N 𝒮 h𝒮N h𝒮
  have hBranchBound :
      ∀ R ∈ roots, (branch R).card ≤ 2 * R.card - 1 := by
    intro R hR
    have hRmem : R ∈ maximal_nonempty_members 𝒮 := by
      simpa [roots] using hR
    have hRNonempty : R.Nonempty := by
      -- Top-level roots are nonempty because they come from `𝒮.erase ∅`.
      exact Finset.nonempty_iff_ne_empty.2 (Finset.mem_erase.1 (Finset.mem_filter.1 hRmem).1).1
    have hRInBranch : R ∈ branch R := by
      -- Each root lies in its own rooted branch.
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hRmem).1, subset_rfl⟩
    have hBranchSub : ∀ ⦃S : Finset V⦄, S ∈ branch R → S ⊆ R := by
      -- Branch members are defined by containment in the corresponding root.
      intro S hS
      exact (Finset.mem_filter.1 hS).2
    have hBranchEmpty : ∅ ∉ branch R := by
      -- Erasing `∅` at the top removes it from every branch as well.
      intro hEmptyBranch
      exact (Finset.mem_erase.1 (Finset.mem_filter.1 hEmptyBranch).1).1 rfl
    have hBranchLam : IsLaminarSubsetFamily (branch R) := by
      -- Laminarity again restricts to the branch.
      intro S U hS hU hInt
      exact h𝒮
        ((Finset.mem_erase.1 (Finset.mem_filter.1 hS).1).2)
        ((Finset.mem_erase.1 (Finset.mem_filter.1 hU).1).2)
        hInt
    have hBranchContained : ∀ ⦃S : Finset V⦄, S ∈ branch R → S ⊆ R := by
      intro S hS
      exact hBranchSub hS
    -- Apply the rooted counting lemma to each top-level component.
    exact rootedLaminarSubsetFamily_card_le_two_mul_card_sub_one
      (R := R) (T := branch R) hRNonempty hRInBranch hBranchContained hBranchEmpty hBranchLam
  have hRootNonempty :
      ∀ R ∈ roots, R.Nonempty := by
    intro R hR
    have hRmem : R ∈ maximal_nonempty_members 𝒮 := by
      simpa [roots] using hR
    exact Finset.nonempty_iff_ne_empty.2 (Finset.mem_erase.1 (Finset.mem_filter.1 hRmem).1).1
  have hBranchBoundSum :
      ∑ R ∈ roots, (branch R).card ≤ ∑ R ∈ roots, (2 * R.card - 1) := by
    -- Summing the rooted bounds over all roots controls the whole nonempty family.
    refine Finset.sum_le_sum ?_
    intro R hR
    exact hBranchBound R hR
  have hWeightedBound :
      ∑ R ∈ roots, (2 * R.card - 1) ≤ 2 * N.card - 1 := by
    -- The disjoint root sizes sum to at most `|N|`, and there is at least one root.
    have hTwice : 2 * (∑ R ∈ roots, R.card) ≤ 2 * N.card :=
      Nat.mul_le_mul_left 2 hRootCards
    have hWeighted :
        (∑ R ∈ roots, (2 * R.card - 1)) + roots.card =
          2 * (∑ R ∈ roots, R.card) := by
      simpa using sum_two_mul_card_sub_one_add_card roots hRootNonempty
    have hRootsCardPos : 1 ≤ roots.card := hRoots'.card_pos
    omega
  calc
    (𝒮.erase ∅).card = ∑ R ∈ roots, (branch R).card := hEraseCard
    _ ≤ ∑ R ∈ roots, (2 * R.card - 1) := hBranchBoundSum
    _ ≤ 2 * N.card - 1 := hWeightedBound

/-- Exercise 4.9 (1). A laminar family of subsets of a nonempty finite set has cardinality at most
twice the cardinality of the ground set. -/
theorem laminar_subset_family_card_le_two_mul_card
    (N : Finset V)
    (hN : N.Nonempty)
    (𝒮 : Finset (Finset V))
    (h𝒮N : ∀ ⦃S : Finset V⦄, S ∈ 𝒮 → S ⊆ N)
    (h𝒮 : IsLaminarSubsetFamily 𝒮) :
    𝒮.card ≤ 2 * N.card := by
  classical
  let roots : Finset (Finset V) := maximal_nonempty_members 𝒮
  by_cases hRoots : roots.Nonempty
  · -- Route correction: once the nonempty part splits into rooted components, each component is
    -- controlled by the rooted lemma and `∅` contributes at most one extra family member.
    have hEraseBound : (𝒮.erase ∅).card ≤ 2 * N.card - 1 := by
      simpa [roots] using
        laminarEraseEmpty_card_le_two_mul_card_sub_one_of_nonemptyRoots N 𝒮
          (by simpa [roots] using hRoots) h𝒮N h𝒮
    by_cases hEmpty : ∅ ∈ 𝒮
    · -- If `∅ ∈ 𝒮`, add it back after bounding the nonempty part.
      have hCard := Finset.card_erase_add_one hEmpty
      have hNCardPos : 1 ≤ N.card := hN.card_pos
      have hTwoNCardPos : 1 ≤ 2 * N.card := by
        omega
      calc
        𝒮.card = (𝒮.erase ∅).card + 1 := by omega
        _ ≤ (2 * N.card - 1) + 1 := Nat.add_le_add_right hEraseBound 1
        _ = 2 * N.card := Nat.sub_add_cancel hTwoNCardPos
    · -- Otherwise `𝒮 = 𝒮.erase ∅`, so the sharper bound already suffices.
      have hCard : 𝒮.card = (𝒮.erase ∅).card := by
        simpa [Finset.erase_eq_of_notMem hEmpty]
      calc
        𝒮.card = (𝒮.erase ∅).card := hCard
        _ ≤ 2 * N.card - 1 := hEraseBound
        _ ≤ 2 * N.card := by omega
  · have hRootsEmpty : roots = ∅ := Finset.not_nonempty_iff_eq_empty.1 hRoots
    rcases maximal_nonempty_members_biUnion_eq_erase_empty (𝒮 := 𝒮) h𝒮 with ⟨hDecomp, _, _⟩
    have hEraseEmpty : 𝒮.erase ∅ = ∅ := by
      -- With no maximal nonempty root, there are no nonempty family members at all.
      simpa [roots, hRootsEmpty] using hDecomp
    by_cases hEmpty : ∅ ∈ 𝒮
    · -- The family is then exactly `{∅}`.
      have hEraseCard : (𝒮.erase ∅).card = 0 := by
        simpa [hEraseEmpty]
      have hCard := Finset.card_erase_add_one hEmpty
      have hNCardPos : 1 ≤ N.card := hN.card_pos
      omega
    · -- If even `∅` is absent, the family is empty.
      have hCard : 𝒮.card = 0 := by
        simpa [Finset.erase_eq_of_notMem hEmpty] using congrArg Finset.card hEraseEmpty
      omega

/-- Helper for Exercise 4.9: any finite row-selected image of a laminar family is still laminar. -/
private lemma selected_row_image_isLaminarSubsetFamily
    {ι : Type u} [Fintype ι]
    (𝒮 : Finset (Finset V))
    (h𝒮 : IsLaminarSubsetFamily 𝒮)
    (row : ι ↪ 𝒮) :
    IsLaminarSubsetFamily (Finset.univ.image fun i ↦ ((row i : 𝒮) : Finset V)) := by
  -- Any two chosen rows come from members of the original laminar family, so the same nesting
  -- condition applies after passing to the image family.
  intro S T hS hT hInt
  rcases Finset.mem_image.1 hS with ⟨i, -, rfl⟩
  rcases Finset.mem_image.1 hT with ⟨k, -, rfl⟩
  exact h𝒮 (row i).2 (row k).2 hInt

/-- Helper for Exercise 4.9: among selected rows, the rows containing a fixed element are nested. -/
private lemma selected_rows_containing_element_are_nested
    {ι : Type u}
    (𝒮 : Finset (Finset V))
    (h𝒮 : IsLaminarSubsetFamily 𝒮)
    (row : ι ↪ 𝒮)
    {j : V} {i k : ι}
    (hij : j ∈ (((row i : 𝒮) : Finset V)))
    (hkj : j ∈ (((row k : 𝒮) : Finset V))) :
    (((row i : 𝒮) : Finset V) ⊆ ((row k : 𝒮) : Finset V)) ∨
      (((row k : 𝒮) : Finset V) ⊆ ((row i : 𝒮) : Finset V)) := by
  -- The common element `j` witnesses a nonempty intersection, so laminarity forces comparability.
  have hInt :
      ((((row i : 𝒮) : Finset V) ∩ (((row k : 𝒮) : Finset V))).Nonempty) := by
    exact ⟨j, Finset.mem_inter.2 ⟨hij, hkj⟩⟩
  exact h𝒮 (row i).2 (row k).2 hInt

/-- Helper for Exercise 4.9: the support attached to a selected row index is the underlying member
of the laminar family. -/
private def selected_row_support
    {ι : Type u}
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮) (i : ι) : Finset V :=
  ((row i : 𝒮) : Finset V)

/-- Helper for Exercise 4.9: the selected rows containing a fixed element form the column chain
used in the depth-parity argument. -/
private def selected_rows_containing
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮) (j : V) : Finset ι :=
  Finset.univ.filter fun i ↦ j ∈ selected_row_support 𝒮 row i

/-- Helper for Exercise 4.9: the strict supersets of a selected row inside a chosen finite row
set. -/
private def strict_selected_supersets
    {ι : Type u} [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮) (I : Finset ι) (i : ι) : Finset ι :=
  I.filter fun k ↦ selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row k

/-- Helper for Exercise 4.9: the depth of a selected row is the number of strict selected
supersets above it. -/
private def strict_selected_supersets_card
    {ι : Type u} [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮) (I : Finset ι) (i : ι) : ℕ :=
  (strict_selected_supersets 𝒮 row I i).card

/-- Helper for Exercise 4.9: the even-depth selected rows. -/
private def depth_parity_red
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮) : Finset ι :=
  Finset.univ.filter fun i ↦ Even (strict_selected_supersets_card 𝒮 row Finset.univ i)

/-- Helper for Exercise 4.9: the odd-depth selected rows. -/
private def depth_parity_blue
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮) : Finset ι :=
  Finset.univ.filter fun i ↦ ¬ Even (strict_selected_supersets_card 𝒮 row Finset.univ i)

/-- Helper for Exercise 4.9: distinct selected row indices have distinct underlying supports. -/
private lemma selected_row_support_injective
    {ι : Type u}
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮) :
    Function.Injective (selected_row_support 𝒮 row) := by
  -- The row embedding is already injective into the subtype of family members, so equality of
  -- supports forces equality of row indices.
  intro i k hik
  apply row.injective
  apply Subtype.ext
  exact hik

/-- Helper for Exercise 4.9: every nonempty finite chain has a member of maximal support
cardinality. -/
private lemma exists_card_maximal_member
    {ι : Type u}
    (I : Finset ι)
    (hI : I.Nonempty)
    (support : ι → Finset V) :
    ∃ m ∈ I, ∀ i ∈ I, (support i).card ≤ (support m).card := by
  classical
  let cardValues : Finset ℕ := I.image fun i ↦ (support i).card
  have hCardValues : cardValues.Nonempty := by
    rcases hI with ⟨i, hi⟩
    exact ⟨(support i).card, Finset.mem_image.2 ⟨i, hi, rfl⟩⟩
  let c := cardValues.max' hCardValues
  have hcMem : c ∈ cardValues := Finset.max'_mem _ _
  rcases Finset.mem_image.1 hcMem with ⟨m, hmI, hmc⟩
  refine ⟨m, hmI, ?_⟩
  intro i hi
  have hmem : (support i).card ∈ cardValues := Finset.mem_image.2 ⟨i, hi, rfl⟩
  calc
    (support i).card ≤ c := by
      exact Finset.le_max' _ _ hmem
    _ = (support m).card := hmc.symm

/-- Helper for Exercise 4.9: after erasing a maximal-cardinality member of a finite support chain,
every remaining support is a strict subset of that maximal support. -/
private lemma support_strictSubset_maximal_of_mem_erase
    {ι : Type u} [DecidableEq ι]
    (I : Finset ι)
    (support : ι → Finset V)
    {m i : ι}
    (hmI : m ∈ I)
    (hiI : i ∈ I.erase m)
    (hmaxCard : ∀ k ∈ I, (support k).card ≤ (support m).card)
    (hchain : ∀ a ∈ I, ∀ b ∈ I, support a ⊆ support b ∨ support b ⊆ support a)
    (hinj : Function.Injective support) :
    support i ⊂ support m := by
  have hiMem : i ∈ I := (Finset.mem_erase.1 hiI).2
  have him : i ≠ m := (Finset.mem_erase.1 hiI).1
  rcases hchain i hiMem m hmI with hiSub | hmSub
  · -- The chain comparability gives the forward inclusion, so it remains to rule out equality.
    refine ⟨hiSub, ?_⟩
    intro hmSub'
    have hsEq : support m = support i :=
      Finset.eq_of_subset_of_card_le hmSub' (hmaxCard i hiMem)
    exact him (hinj hsEq).symm
  · -- The opposite inclusion contradicts maximality unless the supports are equal, which
    -- injectivity forbids because `i` survived erasing `m`.
    have hsEq : support m = support i :=
      Finset.eq_of_subset_of_card_le hmSub (hmaxCard i hiMem)
    exact (him ((hinj hsEq).symm)).elim

/-- Helper for Exercise 4.9: a maximal member of a finite support chain has depth zero. -/
private lemma strict_selected_supersets_eq_empty_of_maximal
    {ι : Type u} [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮)
    (I : Finset ι)
    {m : ι}
    (hmI : m ∈ I)
    (hmax : ∀ i ∈ I, selected_row_support 𝒮 row m ⊆ selected_row_support 𝒮 row i → i = m) :
    strict_selected_supersets 𝒮 row I m = ∅ := by
  -- Route correction: prove the strict-superset filter is literally empty, then read off the
  -- depth-zero cardinality as a corollary instead of arguing with raw cardinal arithmetic.
  ext k
  constructor
  · intro hk
    rcases Finset.mem_filter.1 hk with ⟨hkI, hkStrict⟩
    have hkm : k = m := hmax k hkI hkStrict.1
    subst hkm
    simpa using hkStrict.2 (by intro x hx; exact hx)
  · intro hk
    simpa using hk

/-- Helper for Exercise 4.9: erasing a chosen strict superset removes exactly that one index from
the strict-superset filter. -/
private lemma strict_selected_supersets_eq_insert_of_erase_max
    {ι : Type u} [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮)
    (I : Finset ι)
    {m i : ι}
    (hmI : m ∈ I)
    (hiI : i ∈ I.erase m)
    (him : selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row m) :
    strict_selected_supersets 𝒮 row I i =
      insert m (strict_selected_supersets 𝒮 row (I.erase m) i) := by
  -- Rewriting the filter membership on both sides shows that the only removed strict superset is
  -- the chosen index `m`.
  ext k
  by_cases hk : k = m
  · subst hk
    simp [strict_selected_supersets, hmI, him]
  · simp [strict_selected_supersets, hk, Finset.mem_erase]

/-- Helper for Exercise 4.9: a maximal member of a finite support chain has depth zero. -/
private lemma strict_selected_supersets_card_eq_zero_of_maximal
    {ι : Type u} [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮)
    (I : Finset ι)
    {m : ι}
    (hmI : m ∈ I)
    (hmax : ∀ i ∈ I, selected_row_support 𝒮 row m ⊆ selected_row_support 𝒮 row i → i = m) :
    strict_selected_supersets_card 𝒮 row I m = 0 := by
  -- Read the depth directly from the exact empty-filter description.
  rw [strict_selected_supersets_card, strict_selected_supersets_eq_empty_of_maximal 𝒮 row I hmI hmax]
  simp

/-- Helper for Exercise 4.9: removing the maximal member of a finite support chain drops every
remaining depth by exactly one. -/
private lemma strict_selected_supersets_card_erase_max
    {ι : Type u} [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮)
    (I : Finset ι)
    {m i : ι}
    (hmI : m ∈ I)
    (hiI : i ∈ I.erase m)
    (him : selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row m)
    (hmax : ∀ k ∈ I.erase m,
        selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row k →
          k ∈ strict_selected_supersets 𝒮 row (I.erase m) i) :
    strict_selected_supersets_card 𝒮 row I i =
      strict_selected_supersets_card 𝒮 row (I.erase m) i + 1 := by
  -- Read the depth shift from the exact insert decomposition of the strict-superset filter.
  rw [strict_selected_supersets_card, strict_selected_supersets_card]
  rw [strict_selected_supersets_eq_insert_of_erase_max 𝒮 row I hmI hiI him]
  have hmNotMem : m ∉ strict_selected_supersets 𝒮 row (I.erase m) i := by
    simp [strict_selected_supersets]
  rw [Finset.card_insert_of_notMem hmNotMem]

/-- Helper for Exercise 4.9: a maximal support in a finite chain has no strict supersets. -/
private lemma strict_supersets_eq_empty_of_maximal
    {ι : Type u} [DecidableEq ι]
    (I : Finset ι)
    (support : ι → Finset V)
    {m : ι}
    (hmI : m ∈ I)
    (hmax : ∀ i ∈ I, support m ⊆ support i → i = m) :
    I.filter (fun k ↦ support m ⊂ support k) = ∅ := by
  -- Any candidate strict superset would contradict the maximality witness `hmax`.
  ext k
  constructor
  · intro hk
    rcases Finset.mem_filter.1 hk with ⟨hkI, hkStrict⟩
    have hkm : k = m := hmax k hkI hkStrict.1
    subst hkm
    exact (hkStrict.2 subset_rfl).elim
  · intro hk
    simpa using hk

/-- Helper for Exercise 4.9: after erasing a maximal support, the strict supersets of a remaining
member are exactly the erased maximal support together with the old strict supersets in the erase
family. -/
private lemma strict_supersets_eq_insert_of_erase_maximal
    {ι : Type u} [DecidableEq ι]
    (I : Finset ι)
    (support : ι → Finset V)
    {m i : ι}
    (hmI : m ∈ I)
    (hiI : i ∈ I.erase m)
    (him : support i ⊂ support m) :
    I.filter (fun k ↦ support i ⊂ support k) =
      insert m ((I.erase m).filter (fun k ↦ support i ⊂ support k)) := by
  -- The only strict superset lost when passing to `I.erase m` is the maximal member `m` itself.
  ext k
  by_cases hk : k = m
  · subst hk
    simp [hmI, him]
  · simp [hk, Finset.mem_erase]

/-- Helper for Exercise 4.9: adding one strict superset flips the parity sign in the alternating
chain sum. -/
private lemma alternating_chain_term_succ (n : ℕ) :
    (if Even (n + 1) then (1 : ℤ) else -1) =
      -(if Even n then (1 : ℤ) else -1) := by
  -- A successor toggles parity, so the alternating `±1` weight changes sign.
  by_cases hEven : Even n
  · simp [Nat.even_add_one, hEven]
  · simp [Nat.even_add_one, hEven]

/-- Helper for Exercise 4.9: along a finite chain of distinct sets through a common point, the
depth-parity alternating sum is always `0` or `1`. -/
private lemma common_point_chain_alternating_sum_zero_or_one
    {ι : Type u} [DecidableEq ι]
    (I : Finset ι)
    (support : ι → Finset V)
    {j : V}
    (hj : ∀ i ∈ I, j ∈ support i)
    (hchain : ∀ i ∈ I, ∀ k ∈ I, support i ⊆ support k ∨ support k ⊆ support i)
    (hinj : Function.Injective support) :
    Finset.sum I
        (fun i ↦ if Even ((I.filter fun k ↦ support i ⊂ support k).card) then (1 : ℤ) else -1) = 0 ∨
      Finset.sum I
        (fun i ↦ if Even ((I.filter fun k ↦ support i ⊂ support k).card) then (1 : ℤ) else -1) = 1 := by
  classical
  -- Route correction: erase a maximal support, show its term contributes `1`, and show every
  -- remaining term flips sign because the erased maximal support adds exactly one strict superset.
  refine Finset.strongInductionOn I ?_ j hj hchain hinj
  intro I ih j hj hchain hinj
  let weight : Finset ι → ι → ℤ := fun K i ↦
    if Even ((K.filter fun k ↦ support i ⊂ support k).card) then (1 : ℤ) else -1
  by_cases hI : I.Nonempty
  · rcases exists_card_maximal_member I hI support with ⟨m, hmI, hmaxCard⟩
    have hmMax : ∀ k ∈ I, support m ⊆ support k → k = m := by
      -- Equal cardinality upgrades the maximal inclusion to equality, and injectivity identifies
      -- the index of that support.
      intro k hk hkSub
      have hEq : support m = support k :=
        Finset.eq_of_subset_of_card_le hkSub (hmaxCard k hk)
      exact (hinj hEq).symm
    have hmWeight : weight I m = 1 := by
      -- The maximal support has no strict supersets, so its depth is zero and hence even.
      have hEmpty :
          I.filter (fun k ↦ support m ⊂ support k) = ∅ :=
        strict_supersets_eq_empty_of_maximal I support hmI hmMax
      simp [weight, hEmpty]
    have hTailWeight :
        ∀ i ∈ I.erase m, weight I i = -(weight (I.erase m) i) := by
      -- Erasing the maximal support removes exactly one strict superset above each remaining set.
      intro i hiI
      have him :
          support i ⊂ support m :=
        support_strictSubset_maximal_of_mem_erase I support hmI hiI hmaxCard hchain hinj
      have hFilter :
          I.filter (fun k ↦ support i ⊂ support k) =
            insert m ((I.erase m).filter (fun k ↦ support i ⊂ support k)) :=
        strict_supersets_eq_insert_of_erase_maximal I support hmI hiI him
      have hmNotMem : m ∉ (I.erase m).filter (fun k ↦ support i ⊂ support k) := by
        simp
      have hCard :
          (I.filter fun k ↦ support i ⊂ support k).card =
            ((I.erase m).filter fun k ↦ support i ⊂ support k).card + 1 := by
        rw [hFilter, Finset.card_insert_of_notMem hmNotMem]
      simpa [weight, hCard] using
        alternating_chain_term_succ (((I.erase m).filter fun k ↦ support i ⊂ support k).card)
    have hTailSum :
        Finset.sum (I.erase m) (weight I) =
          -Finset.sum (I.erase m) (weight (I.erase m)) := by
      -- Summing the pointwise sign flip over the erased family converts the tail into the
      -- negative of the smaller alternating sum.
      calc
        Finset.sum (I.erase m) (weight I) =
            Finset.sum (I.erase m) (fun i ↦ -(weight (I.erase m) i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hiI
              exact hTailWeight i hiI
        _ = -Finset.sum (I.erase m) (weight (I.erase m)) := by
              rw [Finset.sum_neg_distrib]
    have hjErase : ∀ i ∈ I.erase m, j ∈ support i := by
      -- The common point condition restricts to the erased family.
      intro i hiI
      exact hj i (Finset.mem_erase.1 hiI).2
    have hchainErase :
        ∀ i ∈ I.erase m, ∀ k ∈ I.erase m, support i ⊆ support k ∨ support k ⊆ support i := by
      -- The chain comparability also restricts to the erased family.
      intro i hiI k hkI
      exact hchain i (Finset.mem_erase.1 hiI).2 k (Finset.mem_erase.1 hkI).2
    rcases ih (I.erase m) (Finset.erase_ssubset hmI) j hjErase hchainErase hinj with hErase | hErase
    · -- If the smaller alternating sum is `0`, adding the maximal `+1` term yields `1`.
      right
      have hGoal : Finset.sum I (weight I) = 1 := by
        rw [(Finset.sum_erase_add (s := I) (a := m) (f := weight I) hmI).symm]
        rw [hTailSum, hmWeight, hErase]
        norm_num
      simpa [weight] using hGoal
    · -- If the smaller alternating sum is `1`, the maximal `+1` term cancels the tail `-1`.
      left
      have hGoal : Finset.sum I (weight I) = 0 := by
        rw [(Finset.sum_erase_add (s := I) (a := m) (f := weight I) hmI).symm]
        rw [hTailSum, hmWeight, hErase]
        norm_num
      simpa [weight] using hGoal
  · -- The empty chain contributes the empty sum, which is `0`.
    left
    have hEmpty : I = ∅ := Finset.not_nonempty_iff_eq_empty.1 hI
    simp [hEmpty, weight]

/-- Helper for Exercise 4.9: the row-bicoloring difference for the depth-parity coloring is the
alternating chain sum over the selected rows containing the column element. -/
private lemma selected_row_bicoloring_difference_eq_chain_alternating_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (row : ι ↪ 𝒮)
    (j : V) :
    row_bicoloring_difference ((matrixOfRowSupports 𝒮).submatrix row id)
        (depth_parity_red 𝒮 row) (depth_parity_blue 𝒮 row) j =
      Finset.sum (selected_rows_containing 𝒮 row j)
        (fun i ↦
          if Even
              (((selected_rows_containing 𝒮 row j).filter
                  fun k ↦ selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row k).card)
            then (1 : ℤ)
            else -1) := by
  classical
  -- Expand the red and blue contributions as universal sums with pointwise signs.
  rw [row_bicoloring_difference_apply]
  have hRed :
      (depth_parity_red 𝒮 row).sum
          (fun i ↦ ((matrixOfRowSupports 𝒮).submatrix row id) i j) =
        Finset.univ.sum
          (fun i ↦
            if Even (strict_selected_supersets_card 𝒮 row Finset.univ i) then
              ((matrixOfRowSupports 𝒮).submatrix row id) i j
            else 0) := by
    simpa [depth_parity_red] using
      (Finset.sum_filter
        (s := Finset.univ)
        (p := fun i ↦ Even (strict_selected_supersets_card 𝒮 row Finset.univ i))
        (f := fun i ↦ ((matrixOfRowSupports 𝒮).submatrix row id) i j))
  have hBlue :
      (depth_parity_blue 𝒮 row).sum
          (fun i ↦ ((matrixOfRowSupports 𝒮).submatrix row id) i j) =
        Finset.univ.sum
          (fun i ↦
            if ¬ Even (strict_selected_supersets_card 𝒮 row Finset.univ i) then
              ((matrixOfRowSupports 𝒮).submatrix row id) i j
            else 0) := by
    simpa [depth_parity_blue] using
      (Finset.sum_filter
        (s := Finset.univ)
        (p := fun i ↦ ¬ Even (strict_selected_supersets_card 𝒮 row Finset.univ i))
        (f := fun i ↦ ((matrixOfRowSupports 𝒮).submatrix row id) i j))
  rw [hRed, hBlue, ← Finset.sum_sub_distrib]
  -- Reexpress the target as a universal sum so that each row can be simplified independently.
  rw [selected_rows_containing, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hij : j ∈ selected_row_support 𝒮 row i
  · -- Once `i` contains `j`, every strict selected superset of `i` also contains `j`, so the
    -- global and local depth counts agree.
    have hSupersets :
        strict_selected_supersets 𝒮 row Finset.univ i =
          (selected_rows_containing 𝒮 row j).filter
            (fun k ↦ selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row k) := by
      ext k
      constructor
      · intro hk
        rcases Finset.mem_filter.1 hk with ⟨hkUniv, hkStrict⟩
        refine Finset.mem_filter.2 ?_
        constructor
        · exact Finset.mem_filter.2 ⟨hkUniv, hkStrict.1 hij⟩
        · exact hkStrict
      · intro hk
        rcases Finset.mem_filter.1 hk with ⟨hkSelected, hkStrict⟩
        exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hkSelected).1, hkStrict⟩
    have hijRow : j ∈ (((row i : 𝒮) : Finset V)) := by
      simpa [selected_row_support] using hij
    have hEntry :
        ((matrixOfRowSupports 𝒮).submatrix row id) i j = 1 := by
      simp [Matrix.submatrix_apply, matrixOfRowSupports, rowOfSupport, hijRow]
    by_cases hEven : Even (strict_selected_supersets_card 𝒮 row Finset.univ i)
    · -- Even depth means a `+1` contribution from the selected row.
      have hGlobalNotOdd :
          ¬ Odd (strict_selected_supersets_card 𝒮 row Finset.univ i) :=
        Nat.not_odd_iff_even.2 hEven
      have hLocalEven :
          Even
            (((selected_rows_containing 𝒮 row j).filter
                fun k ↦ selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row k).card) := by
        simpa [strict_selected_supersets_card, hSupersets] using hEven
      have hLocalNotOdd :
          ¬ Odd
            (((selected_rows_containing 𝒮 row j).filter
                fun k ↦ selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row k).card) :=
        Nat.not_odd_iff_even.2 hLocalEven
      have hTargetEven :
          Even
            ((Finset.univ.filter fun k ↦ j ∈ selected_row_support 𝒮 row k).filter
              fun k ↦ selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row k).card := by
        simpa [selected_rows_containing] using hLocalEven
      rw [hEntry]
      simp [hEven, hGlobalNotOdd, hTargetEven, hij]
    · -- Odd depth means the blue contribution survives with sign `-1`.
      have hGlobalOdd :
          Odd (strict_selected_supersets_card 𝒮 row Finset.univ i) :=
        Nat.not_even_iff_odd.1 hEven
      have hLocalOdd :
          Odd
            (((selected_rows_containing 𝒮 row j).filter
                fun k ↦ selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row k).card) := by
        simpa [strict_selected_supersets_card, hSupersets] using (Nat.not_even_iff_odd.1 hEven)
      have hLocalNotEven :
          ¬ Even
            (((selected_rows_containing 𝒮 row j).filter
                fun k ↦ selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row k).card) :=
        Nat.not_even_iff_odd.2 hLocalOdd
      have hTargetOdd :
          Odd
            ((Finset.univ.filter fun k ↦ j ∈ selected_row_support 𝒮 row k).filter
              fun k ↦ selected_row_support 𝒮 row i ⊂ selected_row_support 𝒮 row k).card := by
        simpa [selected_rows_containing] using hLocalOdd
      rw [hEntry]
      simp [hEven, hGlobalOdd, hTargetOdd, hij]
  · -- Rows not containing `j` contribute zero on both sides.
    have hijRow : j ∉ (((row i : 𝒮) : Finset V)) := by
      simpa [selected_row_support] using hij
    have hEntry :
        ((matrixOfRowSupports 𝒮).submatrix row id) i j = 0 := by
      simp [Matrix.submatrix_apply, matrixOfRowSupports, rowOfSupport, hijRow]
    rw [hEntry]
    by_cases hEven : Even (strict_selected_supersets_card 𝒮 row Finset.univ i)
    · have hGlobalNotOdd :
          ¬ Odd (strict_selected_supersets_card 𝒮 row Finset.univ i) :=
        Nat.not_odd_iff_even.2 hEven
      simp [hEven, hGlobalNotOdd, hij]
    · have hGlobalOdd :
          Odd (strict_selected_supersets_card 𝒮 row Finset.univ i) :=
        Nat.not_even_iff_odd.1 hEven
      simp [hEven, hGlobalOdd, hij]

/-- Helper for Exercise 4.9: parity of strict selected-row depth yields an equitable row
bicoloring for every selected row submatrix of a laminar family. -/
private lemma selected_laminar_rows_depth_parity_is_equitable_row_bicoloring
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (𝒮 : Finset (Finset V))
    (h𝒮 : IsLaminarSubsetFamily 𝒮)
    (row : ι ↪ 𝒮) :
    is_equitable_row_bicoloring
      ((matrixOfRowSupports 𝒮).submatrix row id)
      (depth_parity_red 𝒮 row)
      (depth_parity_blue 𝒮 row) := by
  classical
  rw [is_equitable_row_bicoloring_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- The red and blue classes are the even/odd partition of the row depths.
    refine Finset.disjoint_left.2 ?_
    intro i hiRed hiBlue
    exact (Finset.mem_filter.1 hiBlue).2 ((Finset.mem_filter.1 hiRed).2)
  · -- Every selected row has either even or odd depth.
    ext i
    by_cases hEven : Even (strict_selected_supersets_card 𝒮 row Finset.univ i)
    · simp [depth_parity_red, depth_parity_blue, hEven]
    · simp [depth_parity_red, depth_parity_blue, hEven, Nat.not_even_iff_odd.1 hEven]
  · intro j
    -- Bridge the column difference to the chain alternating sum for the rows containing `j`.
    rw [selected_row_bicoloring_difference_eq_chain_alternating_sum 𝒮 row j]
    have hj :
        ∀ i ∈ selected_rows_containing 𝒮 row j, j ∈ selected_row_support 𝒮 row i := by
      intro i hi
      exact (Finset.mem_filter.1 hi).2
    have hchain :
        ∀ i ∈ selected_rows_containing 𝒮 row j,
          ∀ k ∈ selected_rows_containing 𝒮 row j,
            selected_row_support 𝒮 row i ⊆ selected_row_support 𝒮 row k ∨
              selected_row_support 𝒮 row k ⊆ selected_row_support 𝒮 row i := by
      intro i hi k hk
      exact selected_rows_containing_element_are_nested 𝒮 h𝒮 row
        (hij := (Finset.mem_filter.1 hi).2)
        (hkj := (Finset.mem_filter.1 hk).2)
    -- The chain lemma now applies directly to the rows containing `j`.
    rcases common_point_chain_alternating_sum_zero_or_one
        (I := selected_rows_containing 𝒮 row j)
        (support := selected_row_support 𝒮 row)
        hj hchain (selected_row_support_injective 𝒮 row) with hsum | hsum
    · exact Or.inl hsum
    · exact Or.inr (Or.inl hsum)

/-- Exercise 4.9 (2). The incidence matrix of a laminar family of subsets is totally unimodular. -/
theorem matrixOfRowSupports_isTotallyUnimodular_of_isLaminarSubsetFamily
    (𝒮 : Finset (Finset V)) (h𝒮 : IsLaminarSubsetFamily 𝒮) :
    (matrixOfRowSupports 𝒮).IsTotallyUnimodular := by
  -- Route correction: prove Corollary 4.7 directly on arbitrary selected rows by coloring each
  -- row with the parity of its strict-superset depth, rather than transporting a coloring across
  -- an image-family reindexing.
  refine
    (totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring.{0, 0, 0}
      (matrixOfRowSupports 𝒮)).2 ?_
  intro ι _ _ row
  refine ⟨depth_parity_red 𝒮 row, depth_parity_blue 𝒮 row, ?_⟩
  -- The chosen parity classes satisfy Corollary 4.7 for every row submatrix.
  exact selected_laminar_rows_depth_parity_is_equitable_row_bicoloring 𝒮 h𝒮 row

end Exercise49
