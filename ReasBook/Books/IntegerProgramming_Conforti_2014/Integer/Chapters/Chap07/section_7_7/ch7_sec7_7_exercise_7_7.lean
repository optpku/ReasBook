/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_7.Coefficients
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_7.Order

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix
open SequenceIndependentLifting

noncomputable section

section Exercise77

universe u

variable {ι : Type u} [DecidableEq ι]

/-- Helper for Exercise 7.7: the local mirror of the private sequential-lifting recursion, with
an explicit lifted set `L` and current coefficient vector `c`. -/
def sequentialLiftingRun
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (β : ℝ)
    (L : Finset ι)
    (c : ι → ℝ)
    (σ : List ι) : Finset ι × (ι → ℝ) :=
  match σ with
  | [] => (L, c)
  | j :: τ =>
      let αj := next_sequential_lifting_coefficient S C L c β j
      sequentialLiftingRun S C β (insert j L) (Function.update c j αj) τ

/-- Helper for Exercise 7.7: the local mirror of the stagewise nonemptiness recursion, started
from an already lifted set `L`. -/
def sequentialLiftingFeasibleFrom
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (σ : List ι) : Prop :=
  match σ with
  | [] => True
  | j :: τ =>
      (sequential_lifting_slice S C L j).Nonempty ∧
        sequentialLiftingFeasibleFrom S C (insert j L) τ

/-- Helper for Exercise 7.7: running the local mirror over an appended list factors through the
state reached after the pre. -/
lemma sequentialLiftingRun_append
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (β : ℝ)
    (L : Finset ι)
    (c : ι → ℝ)
    (σ₁ σ₂ : List ι) :
    sequentialLiftingRun S C β L c (σ₁ ++ σ₂) =
      let state := sequentialLiftingRun S C β L c σ₁
      sequentialLiftingRun S C β state.1 state.2 σ₂ := by
  induction σ₁ generalizing L c with
  | nil =>
      -- The empty pre leaves the state unchanged.
      simp [sequentialLiftingRun]
  | cons j τ ih =>
      -- After one step, recurse on the remaining pre.
      simp [sequentialLiftingRun, ih]

/-- Helper for Exercise 7.7: the lifted-set component of the local mirror is exactly the initial
lifted set together with the indices appearing in the processed list. -/
lemma sequentialLiftingRun_liftedSet_eq
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (β : ℝ)
    (L : Finset ι)
    (c : ι → ℝ)
    (σ : List ι) :
    (sequentialLiftingRun S C β L c σ).1 = L ∪ σ.toFinset := by
  induction σ generalizing L c with
  | nil =>
      -- No additional indices are lifted by the empty run.
      simp [sequentialLiftingRun]
  | cons j τ ih =>
      -- A cons-step inserts `j` into the lifted set before recursing.
      simp [sequentialLiftingRun, ih]

/-- Helper for Exercise 7.7: if `j` does not appear in the processed suffix, the local mirror
never changes the `j`-coordinate. -/
lemma sequentialLiftingRunPreservesCoordinateOfNotMem
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (β : ℝ)
    (L : Finset ι)
    (c : ι → ℝ)
    (σ : List ι)
    {j : ι}
    (hj : j ∉ σ) :
    (sequentialLiftingRun S C β L c σ).2 j = c j := by
  induction σ generalizing L c with
  | nil =>
      -- The empty suffix performs no updates at all.
      simp [sequentialLiftingRun]
  | cons k τ ih =>
      -- The head update is at `k ≠ j`, so only the tail matters.
      have hjk : j ≠ k := by
        intro h
        apply hj
        simp [h]
      have hjτ : j ∉ τ := by
        intro hj'
        apply hj
        simp [hj']
      simpa [sequentialLiftingRun, hjk] using
        ih (insert k L)
          (Function.update c k (next_sequential_lifting_coefficient S C L c β k))
          hjτ

omit [DecidableEq ι] in
/-- Helper for Exercise 7.7: the pointwise objective can be compared through a finite set `A`
when both coefficient vectors agree off `A` and `x` vanishes on `A`. -/
lemma dotProduct_eq_of_zero_on_and_eq_off
    [Fintype ι]
    {A : Finset ι}
    {c₁ c₂ x : ι → ℝ}
    (hzero : ∀ k, k ∈ A → x k = 0)
    (heq : ∀ k, k ∉ A → c₁ k = c₂ k) :
    c₁ ⬝ᵥ x = c₂ ⬝ᵥ x := by
  -- Compare the summands coordinatewise, splitting on membership in `A`.
  rw [dotProduct, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases hkA : k ∈ A
  · simp [hzero k hkA]
  · simp [heq k hkA]

/-- Helper for Exercise 7.7: a pointwise equality on a subset transports an image-set inclusion. -/
lemma image_subset_of_subset_and_pointwise_eq
    {α β : Type*}
    {A B : Set α}
    {f g : α → β}
    (hsubset : A ⊆ B)
    (heq : ∀ x ∈ A, f x = g x) :
    f '' A ⊆ g '' B := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, hsubset hx, (heq x hx).symm⟩

/-- Helper for Exercise 7.7: enlarging the already lifted set can only enlarge the corresponding
stage slice. -/
lemma sequentialLiftingSlice_mono
    (S : Set (ι → ℝ))
    (C : Finset ι)
    {L₁ L₂ : Finset ι}
    {j : ι}
    (hL : L₁ ⊆ L₂) :
    sequential_lifting_slice S C L₁ j ⊆ sequential_lifting_slice S C L₂ j := by
  intro x hx
  rcases (mem_sequential_lifting_slice_iff.mp hx) with ⟨hxS, hxj, hxzero⟩
  refine mem_sequential_lifting_slice_iff.mpr ⟨hxS, hxj, ?_⟩
  intro k hk
  apply hxzero
  intro hk'
  apply hk
  rcases Finset.mem_insert.mp hk' with rfl | hk'
  · simp
  · rcases Finset.mem_union.mp hk' with hkC | hkL1
    · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_union.mpr <| Or.inl hkC
    · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_union.mpr <| Or.inr (hL hkL1)

omit [DecidableEq ι] in
/-- Helper for Exercise 7.7: the binary cube `{x | ∀ i, x i = 0 ∨ x i = 1}` is finite when the
index type is finite. -/
lemma finite_binaryCube
    [Finite ι] :
    Set.Finite ({x : ι → ℝ | ∀ i, x i = 0 ∨ x i = 1} : Set (ι → ℝ)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let encode : (ι → Bool) → (ι → ℝ) := fun b i ↦ if b i then 1 else 0
  have hrange :
      Set.range encode = ({x : ι → ℝ | ∀ i, x i = 0 ∨ x i = 1} : Set (ι → ℝ)) := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      intro i
      by_cases hb : b i
      · right
        simp [encode, hb]
      · left
        simp [encode, hb]
    · intro hx
      refine ⟨fun i ↦ x i = 1, ?_⟩
      funext i
      by_cases hxi : x i = 1
      · simp [encode, hxi]
      · rcases hx i with hzero | hone
        · simp [encode, hzero]
        · exact (hxi hone).elim
  simpa [hrange] using Set.finite_range encode

/-- Helper for Exercise 7.7: each sequential-lifting objective image set is bounded above because
the slice sits inside the finite binary cube. -/
lemma sequentialLiftingObjective_bddAbove
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (c : ι → ℝ)
    (j : ι)
    (hS_binary : S ⊆ {x | ∀ i, x i = 0 ∨ x i = 1}) :
    BddAbove ((fun x ↦ c ⬝ᵥ x) '' sequential_lifting_slice S C L j) := by
  -- The slice is finite because `S` lies in the finite binary cube, so its image is finite too.
  have hslice_finite : (sequential_lifting_slice S C L j).Finite := by
    refine (finite_binaryCube (ι := ι)).subset ?_
    intro x hx
    exact hS_binary (mem_sequential_lifting_slice_iff.mp hx).1
  exact hslice_finite.image (fun x ↦ c ⬝ᵥ x) |>.bddAbove

/-- Helper for Exercise 7.7: the local feasibility mirror factors through appended lists by
updating the already lifted set with the pre indices. -/
lemma sequentialLiftingFeasibleFrom_append_iff
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (σ₁ σ₂ : List ι) :
    sequentialLiftingFeasibleFrom S C L (σ₁ ++ σ₂) ↔
      sequentialLiftingFeasibleFrom S C L σ₁ ∧
        sequentialLiftingFeasibleFrom S C (L ∪ σ₁.toFinset) σ₂ := by
  induction σ₁ generalizing L with
  | nil =>
      -- With empty pre, this is just the identity decomposition.
      simp [sequentialLiftingFeasibleFrom]
  | cons j τ ih =>
      -- Peel off the head stage and recurse on the remaining pre.
      simp [sequentialLiftingFeasibleFrom, ih, and_assoc]

-- Local declaration justification (macro): the owner recursion in `Coefficients.lean` is a
-- private imported declaration, so a tiny `mkIdent` bridge is required to reference it from this
-- item file.
open Lean in
local macro "importedSequentialLiftingCoefficientsAuxTerm" : term =>
  let base :=
    Name.str
      (Name.str
        (Name.str
          (Name.str
            (Name.str
              (Name.str
                (Name.str Name.anonymous "_private")
                "Integer")
              "Chapters")
            "Chap07")
          "section_7_7")
        "ch7_sec7_7_exercise_7_7")
      "Coefficients"
  let base := Name.num base 0
  pure <| mkIdent <| Name.str base "sequential_lifting_coefficientsAux"

/-- Helper for Exercise 7.7: source-level handle for the imported private sequential-lifting
coefficient recursion. -/
private abbrev importedSequentialLiftingCoefficientsAux
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (β : ℝ)
    (L : Finset ι)
    (c : ι → ℝ)
    (σ : List ι) : ι → ℝ :=
  importedSequentialLiftingCoefficientsAuxTerm S C β L c σ

-- Local declaration justification (macro): the owner feasibility recursion in `Order.lean` is a
-- private imported declaration, so a tiny `mkIdent` bridge is required to reference it here.
open Lean in
local macro "importedFeasibleSequentialLiftingOrderAuxTerm" : term =>
  let base :=
    Name.str
      (Name.str
        (Name.str
          (Name.str
            (Name.str
              (Name.str
                (Name.str Name.anonymous "_private")
                "Integer")
              "Chapters")
            "Chap07")
          "section_7_7")
        "ch7_sec7_7_exercise_7_7")
      "Order"
  let base := Name.num base 0
  pure <| mkIdent <| Name.str base "feasibleSequentialLiftingOrderAux"

/-- Helper for Exercise 7.7: source-level handle for the imported private feasibility recursion. -/
private abbrev importedFeasibleSequentialLiftingOrderAux
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (σ : List ι) : Prop :=
  importedFeasibleSequentialLiftingOrderAuxTerm S C L σ

/-- Helper for Exercise 7.7: the imported private coefficient recursion agrees with the local
mirror started from the same lifted set and coefficient vector. -/
private lemma importedSequentialLiftingCoefficientsAux_eq_run
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (β : ℝ)
    (L : Finset ι)
    (c : ι → ℝ)
    (σ : List ι) :
    importedSequentialLiftingCoefficientsAux S C β L c σ =
      (sequentialLiftingRun S C β L c σ).2 := by
  induction σ generalizing L c with
  | nil =>
      -- Both recursions stop immediately on the empty suffix.
      rfl
  | cons j τ ih =>
      -- Both recursions perform the same one-step update before recursing on the tail.
      simpa [importedSequentialLiftingCoefficientsAux, sequentialLiftingRun] using
        ih (insert j L) (Function.update c j (next_sequential_lifting_coefficient S C L c β j))

/-- Helper for Exercise 7.7: the imported private feasibility recursion agrees with the local
stagewise nonemptiness mirror started from the same lifted set. -/
private lemma importedFeasibleSequentialLiftingOrderAux_eq_local
    (S : Set (ι → ℝ))
    (C L : Finset ι)
    (σ : List ι) :
    importedFeasibleSequentialLiftingOrderAux S C L σ ↔
      sequentialLiftingFeasibleFrom S C L σ := by
  induction σ generalizing L with
  | nil =>
      -- Both feasibility recursions are vacuous on the empty suffix.
      rfl
  | cons j τ ih =>
      -- A cons-step asks for the current slice to be nonempty and then recurses after inserting
      -- `j` into the lifted set.
      dsimp [importedFeasibleSequentialLiftingOrderAux, sequentialLiftingFeasibleFrom]
      constructor
      · intro h
        exact ⟨h.1, (ih (insert j L)).1 h.2⟩
      · intro h
        exact ⟨h.1, (ih (insert j L)).2 h.2⟩

/-- Helper for Exercise 7.7: the public coefficient vector should agree with the local mirror
started from the base state. -/
lemma sequentialLiftingRunEqPublic
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (σ : List ι) :
    sequential_lifting_coefficients S C α β σ =
      (sequentialLiftingRun S C β ∅ (base_coefficients C α) σ).2 := by
  -- Rewrite the public definition to the imported owner recursion and then use the local bridge.
  rw [sequential_lifting_coefficients]
  simpa using
    importedSequentialLiftingCoefficientsAux_eq_run
      S C β ∅ (base_coefficients C α) σ

/-- Helper for Exercise 7.7: the public feasibility predicate should agree with the local mirror
started from the empty lifted set. -/
lemma sequentialLiftingFeasibleFromEqPublic
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (σ : List ι) :
    IsFeasibleSequentialLiftingOrder S C σ ↔
      sequentialLiftingFeasibleFrom S C ∅ σ := by
  -- Rewrite the public feasibility predicate to the imported owner recursion and then use the
  -- local bridge.
  rw [IsFeasibleSequentialLiftingOrder]
  simpa using importedFeasibleSequentialLiftingOrderAux_eq_local S C ∅ σ

/-- Helper for Exercise 7.7: after splitting a run as `pre ++ j :: tail`, the `j`-coordinate
of the final coefficient vector is exactly the stage coefficient chosen when `j` is processed. -/
lemma sequentialLiftingRunCoordinateAtSplit
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (β : ℝ)
    (L : Finset ι)
    (c : ι → ℝ)
    (pre tail : List ι)
    {j : ι}
    (hjtail : j ∉ tail) :
    (sequentialLiftingRun S C β L c (pre ++ j :: tail)).2 j =
      next_sequential_lifting_coefficient S C
        (sequentialLiftingRun S C β L c pre).1
        (sequentialLiftingRun S C β L c pre).2
        β
        j := by
  -- First isolate the state reached after the pre.
  rw [sequentialLiftingRun_append]
  -- Then the tail leaves the newly updated `j`-coordinate unchanged.
  let state := sequentialLiftingRun S C β L c pre
  have hpreserve :
      (sequentialLiftingRun S C β (insert j state.1)
          (Function.update state.2 j
            (next_sequential_lifting_coefficient S C state.1 state.2 β j)) tail).2 j =
        (Function.update state.2 j
          (next_sequential_lifting_coefficient S C state.1 state.2 β j)) j := by
    simpa [state] using
      sequentialLiftingRunPreservesCoordinateOfNotMem
        S C β (insert j state.1)
        (Function.update state.2 j
          (next_sequential_lifting_coefficient S C state.1 state.2 β j))
        tail
        hjtail
  -- Evaluating the updated function at `j` recovers the stage coefficient.
  simpa [sequentialLiftingRun, state] using hpreserve

omit [DecidableEq ι] in
/-- Helper for Exercise 7.7: a nodup split `pre ++ j :: tail` keeps `j` out of both sides and
forces `pre` and `tail` to be disjoint. -/
private lemma splitNodupFacts
    {pre tail : List ι}
    {j : ι}
    (h : (pre ++ j :: tail).Nodup) :
    j ∉ pre ∧ j ∉ tail ∧ ∀ ⦃k : ι⦄, k ∈ pre → k ∉ tail := by
  -- Expand the nodup append relation once so the disjointness facts are available by projection.
  have hsplit :
      pre.Nodup ∧ (j ∉ tail ∧ tail.Nodup) ∧
        ∀ a ∈ pre, ¬a = j ∧ ∀ a₂ ∈ tail, ¬a = a₂ := by
    simpa [List.nodup_append] using h
  refine ⟨?_, hsplit.2.1.1, ?_⟩
  · intro hjpre
    exact (hsplit.2.2 j hjpre).1 rfl
  · intro k hkpre hktail
    exact (hsplit.2.2 k hkpre).2 k hktail rfl

/-- Helper for Exercise 7.7: erasing the singled-out entry from a nodup split list removes exactly
that middle occurrence. -/
private lemma erase_append_cons_of_nodup
    (pre tail : List ι)
    (j : ι)
    (h : (pre ++ j :: tail).Nodup) :
    (pre ++ j :: tail).erase j = pre ++ tail := by
  induction pre with
  | nil =>
      -- At the head, erasing `j` simply drops the front occurrence.
      simp
  | cons a pre ih =>
      -- Off the head, push the erase through and recurse on the smaller split.
      have hneq : a ≠ j := by
        have hfacts := splitNodupFacts (pre := a :: pre) (tail := tail) (j := j) h
        intro hEq
        exact hfacts.1 (by simp [hEq])
      have htail : (pre ++ j :: tail).Nodup := by
        simpa using h.of_cons
      simp [List.erase_cons_tail, hneq, ih htail]

omit [DecidableEq ι] in
/-- Helper for Exercise 7.7: any occurrence of `j` in a list isolates a split
`σ = pre ++ j :: tail`. -/
private lemma splitAtMem
    {j : ι}
    : ∀ {σ : List ι}, j ∈ σ → ∃ pre tail, σ = pre ++ j :: tail
  | [], hjσ => by
      simp at hjσ
  | k :: σ, hjσ => by
      by_cases hkj : k = j
      · subst hkj
        exact ⟨[], σ, rfl⟩
      · have hjσ' : j ∈ σ := by
          rcases (List.mem_cons.1 hjσ) with hEq | hjσ'
          · exact False.elim <| hkj hEq.symm
          · exact hjσ'
        rcases splitAtMem hjσ' with ⟨pre, tail, hsplit⟩
        exact ⟨k :: pre, tail, by simp [hsplit]⟩

/-- Helper for Exercise 7.7: every first-stage objective value also appears at the split stage
`pre ++ j :: tail`, because the pre-coordinates are still forced to `0` on the first slice. -/
private lemma firstStageObjectiveImage_subset_splitStage
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    {j : ι}
    (σ pre tail : List ι)
    (hσ : IsSequentialLiftingOrder C σ)
    (hsplit : σ = pre ++ j :: tail) :
    ((fun x ↦ base_coefficients C α ⬝ᵥ x) '' sequential_lifting_slice S C ∅ j) ⊆
      ((fun x ↦ (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).2 ⬝ᵥ x) ''
        sequential_lifting_slice S C
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).1
          j) := by
  let statePre := sequentialLiftingRun S C β ∅ (base_coefficients C α) pre
  have hstatePreSet : statePre.1 = pre.toFinset := by
    simp [statePre, sequentialLiftingRun_liftedSet_eq]
  have hnodup : (pre ++ j :: tail).Nodup := by
    simpa [hsplit] using hσ.nodup
  have hfacts := splitNodupFacts (pre := pre) (tail := tail) (j := j) hnodup
  have hjpre : j ∉ pre := hfacts.1
  have hsubset :
      sequential_lifting_slice S C ∅ j ⊆ sequential_lifting_slice S C statePre.1 j := by
    rw [hstatePreSet]
    exact sequentialLiftingSlice_mono S C (by simp)
  refine image_subset_of_subset_and_pointwise_eq hsubset ?_
  intro x hx
  -- The split-stage coefficients agree with the base coefficients off `pre`, and the first-stage
  -- slice already forces every coordinate in `pre` to vanish.
  refine dotProduct_eq_of_zero_on_and_eq_off (A := pre.toFinset) ?_ ?_
  · intro k hkpre
    rcases mem_sequential_lifting_slice_iff.mp hx with ⟨_, _, hxzero⟩
    have hkpreList : k ∈ pre := by
      simpa using hkpre
    have hkσ : k ∈ σ := by
      have hkSplit : k ∈ pre ++ j :: tail := List.mem_append.2 <| Or.inl hkpreList
      simpa [hsplit] using hkSplit
    have hkC : k ∉ C := (hσ.mem_iff).1 hkσ
    have hkj : k ≠ j := by
      intro hEq
      subst hEq
      exact hjpre hkpreList
    exact hxzero k (by simp [hkC, hkj])
  · intro k hknotpre
    have hknotpreList : k ∉ pre := by
      simpa using hknotpre
    simpa [statePre] using
      (sequentialLiftingRunPreservesCoordinateOfNotMem
        S C β ∅ (base_coefficients C α) pre hknotpreList).symm

/-- Helper for Exercise 7.7: every split-stage objective value also appears at the last stage,
because the tail updates only touch coordinates that are still forced to `0` at the split stage. -/
private lemma splitStageObjectiveImage_subset_lastStage
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    {j : ι}
    (σ pre tail : List ι)
    (hσ : IsSequentialLiftingOrder C σ)
    (hsplit : σ = pre ++ j :: tail) :
    ((fun x ↦ (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).2 ⬝ᵥ x) ''
        sequential_lifting_slice S C
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).1
          j) ⊆
      ((fun x ↦ (sequentialLiftingRun S C β ∅ (base_coefficients C α) (σ.erase j)).2 ⬝ᵥ x) ''
        sequential_lifting_slice S C
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) (σ.erase j)).1
          j) := by
  let statePre := sequentialLiftingRun S C β ∅ (base_coefficients C α) pre
  let stateLast := sequentialLiftingRun S C β ∅ (base_coefficients C α) (σ.erase j)
  have hnodup : (pre ++ j :: tail).Nodup := by
    simpa [hsplit] using hσ.nodup
  have hfacts := splitNodupFacts (pre := pre) (tail := tail) (j := j) hnodup
  have hjtail : j ∉ tail := hfacts.2.1
  have hpretail := hfacts.2.2
  have herase : σ.erase j = pre ++ tail := by
    simpa [hsplit] using erase_append_cons_of_nodup pre tail j hnodup
  have hstatePreSet : statePre.1 = pre.toFinset := by
    simp [statePre, sequentialLiftingRun_liftedSet_eq]
  have hstateLastSet : stateLast.1 = (pre ++ tail).toFinset := by
    dsimp [stateLast]
    rw [herase]
    simp [sequentialLiftingRun_liftedSet_eq]
  have hstateLastEq :
      stateLast = sequentialLiftingRun S C β statePre.1 statePre.2 tail := by
    dsimp [stateLast, statePre]
    rw [herase, sequentialLiftingRun_append]
  have hsubset :
      sequential_lifting_slice S C statePre.1 j ⊆ sequential_lifting_slice S C stateLast.1 j := by
    rw [hstatePreSet, hstateLastSet]
    refine sequentialLiftingSlice_mono S C ?_
    intro k hkpre
    rw [List.mem_toFinset] at hkpre ⊢
    exact List.mem_append.2 <| Or.inl hkpre
  refine image_subset_of_subset_and_pointwise_eq hsubset ?_
  intro x hx
  rw [hstatePreSet] at hx
  -- Off the tail, the last-stage run preserves the split-stage coefficients, and on the tail the
  -- split-stage slice forces every coordinate to vanish.
  refine dotProduct_eq_of_zero_on_and_eq_off (A := tail.toFinset) ?_ ?_
  · intro k hktail
    rcases mem_sequential_lifting_slice_iff.mp hx with ⟨_, _, hxzero⟩
    have hktailList : k ∈ tail := by
      simpa using hktail
    have hkσ : k ∈ σ := by
      have hkSplit : k ∈ pre ++ j :: tail := by
        simp [hktailList]
      simpa [hsplit] using hkSplit
    have hkC : k ∉ C := (hσ.mem_iff).1 hkσ
    have hkj : k ≠ j := by
      intro hEq
      subst hEq
      exact hjtail hktailList
    have hknotpre : k ∉ pre := by
      intro hkpre
      exact hpretail hkpre hktailList
    exact hxzero k (by
      have hknotpreFinset : k ∉ pre.toFinset := by
        simpa using hknotpre
      simp [hkC, hknotpreFinset, hkj])
  · intro k hknottail
    have hknottailList : k ∉ tail := by
      simpa using hknottail
    have hpres :
        (sequentialLiftingRun S C β statePre.1 statePre.2 tail).2 k = statePre.2 k := by
      simpa using
        sequentialLiftingRunPreservesCoordinateOfNotMem
          S C β statePre.1 statePre.2 tail hknottailList
    have hlast : stateLast.2 k = statePre.2 k := by
      exact (congrArg (fun s => s.2 k) hstateLastEq).trans hpres
    exact hlast.symm

/-- Helper for Exercise 7.7: once `j` appears after a pre, the coefficient assigned to `j` at
that split stage is bounded above by the coefficient obtained by lifting `j` first. -/
lemma splitStageCoefficientLeFirstStage
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (hS_binary : S ⊆ {x | ∀ i, x i = 0 ∨ x i = 1})
    {j : ι}
    (σ pre tail : List ι)
    (hσ : IsSequentialLiftingOrder C σ)
    (hsplit : σ = pre ++ j :: tail)
    (hfront_feasible : IsFeasibleSequentialLiftingOrder S C (j :: σ.erase j)) :
    next_sequential_lifting_coefficient S C
      (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).1
      (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).2
      β
      j ≤
    next_sequential_lifting_coefficient S C ∅ (base_coefficients C α) β j := by
  -- Route correction: compare the normalized image sets first, and only then compare the two
  -- `sSup` values elementwise.
  let statePre := sequentialLiftingRun S C β ∅ (base_coefficients C α) pre
  let firstImage : Set ℝ :=
    (fun x ↦ base_coefficients C α ⬝ᵥ x) '' sequential_lifting_slice S C ∅ j
  let splitImage : Set ℝ :=
    (fun x ↦ statePre.2 ⬝ᵥ x) '' sequential_lifting_slice S C statePre.1 j
  have hsubset :
      firstImage ⊆ splitImage := by
    simpa [firstImage, splitImage, statePre] using
      firstStageObjectiveImage_subset_splitStage S C α β σ pre tail hσ hsplit
  have hsplit_bdd : BddAbove splitImage := by
    simpa [splitImage, statePre] using
      sequentialLiftingObjective_bddAbove S C statePre.1 statePre.2 j hS_binary
  have hfirst_nonempty_slice : (sequential_lifting_slice S C ∅ j).Nonempty := by
    have hfrontLocal :=
      (sequentialLiftingFeasibleFromEqPublic S C (j :: σ.erase j)).1 hfront_feasible
    have hfrontStages :
        (sequential_lifting_slice S C ∅ j).Nonempty ∧
          sequentialLiftingFeasibleFrom S C {j} (σ.erase j) := by
      simpa [sequentialLiftingFeasibleFrom] using hfrontLocal
    exact hfrontStages.1
  have hfirst_nonempty : firstImage.Nonempty := by
    rcases hfirst_nonempty_slice with ⟨x, hx⟩
    exact ⟨base_coefficients C α ⬝ᵥ x, ⟨x, hx, rfl⟩⟩
  have hsSup_le : sSup firstImage ≤ sSup splitImage := by
    refine csSup_le hfirst_nonempty ?_
    intro r hr
    exact le_csSup hsplit_bdd (hsubset hr)
  -- Re-expanding both coefficients turns the problem into the previously established supremum
  -- comparison.
  rw [next_sequential_lifting_coefficient_eq, next_sequential_lifting_coefficient_eq]
  change β - sSup splitImage ≤ β - sSup firstImage
  linarith

/-- Helper for Exercise 7.7: moving `j` to the last stage can only decrease the coefficient
assigned to `j` compared with the value obtained at the split stage `pre ++ j :: tail`. -/
lemma lastStageCoefficientLeSplitStage
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (hS_binary : S ⊆ {x | ∀ i, x i = 0 ∨ x i = 1})
    {j : ι}
    (σ pre tail : List ι)
    (hσ : IsSequentialLiftingOrder C σ)
    (hsplit : σ = pre ++ j :: tail)
    (hσ_feasible : IsFeasibleSequentialLiftingOrder S C σ) :
    next_sequential_lifting_coefficient S C
      (sequentialLiftingRun S C β ∅ (base_coefficients C α) (σ.erase j)).1
      (sequentialLiftingRun S C β ∅ (base_coefficients C α) (σ.erase j)).2
      β
      j ≤
    next_sequential_lifting_coefficient S C
      (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).1
      (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).2
      β
      j := by
  -- Route correction: normalize `σ.erase j` to `pre ++ tail`, compare the two image sets, and
  -- only then move back to the coefficient formula.
  let statePre := sequentialLiftingRun S C β ∅ (base_coefficients C α) pre
  let stateLast := sequentialLiftingRun S C β ∅ (base_coefficients C α) (σ.erase j)
  let splitImage : Set ℝ :=
    (fun x ↦ statePre.2 ⬝ᵥ x) '' sequential_lifting_slice S C statePre.1 j
  let lastImage : Set ℝ :=
    (fun x ↦ stateLast.2 ⬝ᵥ x) '' sequential_lifting_slice S C stateLast.1 j
  have hsubset :
      splitImage ⊆ lastImage := by
    simpa [splitImage, lastImage, statePre, stateLast] using
      splitStageObjectiveImage_subset_lastStage S C α β σ pre tail hσ hsplit
  have hlast_bdd : BddAbove lastImage := by
    simpa [lastImage, stateLast] using
      sequentialLiftingObjective_bddAbove S C stateLast.1 stateLast.2 j hS_binary
  have hstatePreSet : statePre.1 = pre.toFinset := by
    simp [statePre, sequentialLiftingRun_liftedSet_eq]
  have hσLocal := (sequentialLiftingFeasibleFromEqPublic S C σ).1 hσ_feasible
  have hsplitLocal : sequentialLiftingFeasibleFrom S C ∅ (pre ++ j :: tail) := by
    simpa [hsplit] using hσLocal
  have happ :
      sequentialLiftingFeasibleFrom S C ∅ pre ∧
        sequentialLiftingFeasibleFrom S C pre.toFinset (j :: tail) := by
    simpa using
      (sequentialLiftingFeasibleFrom_append_iff S C ∅ pre (j :: tail)).1 hsplitLocal
  have hsplit_nonempty_slice : (sequential_lifting_slice S C statePre.1 j).Nonempty := by
    rw [hstatePreSet]
    have hsplitStages :
        (sequential_lifting_slice S C pre.toFinset j).Nonempty ∧
          sequentialLiftingFeasibleFrom S C (insert j pre.toFinset) tail := by
      simpa [sequentialLiftingFeasibleFrom] using happ.2
    exact hsplitStages.1
  have hsplit_nonempty : splitImage.Nonempty := by
    rcases hsplit_nonempty_slice with ⟨x, hx⟩
    exact ⟨statePre.2 ⬝ᵥ x, ⟨x, hx, rfl⟩⟩
  have hsSup_le : sSup splitImage ≤ sSup lastImage := by
    refine csSup_le hsplit_nonempty ?_
    intro r hr
    exact le_csSup hlast_bdd (hsubset hr)
  -- Re-expanding both coefficients turns the comparison into the supremum inequality above.
  rw [next_sequential_lifting_coefficient_eq, next_sequential_lifting_coefficient_eq]
  change β - sSup lastImage ≤ β - sSup splitImage
  linarith

/-- Exercise 7.7. For the sequential lifting procedure applied to a binary
set `S` and a valid base inequality supported on `C`, the coefficient of `x_j` is largest
when `x_j` is lifted
first in the order among feasible admissible lifting orders. Equivalently, moving `j` to the
front of any admissible lifting order with nonempty stagewise lifting slices can only increase
the lifted coefficient assigned to `j`. -/
theorem exercise_7_7_lifting_coefficient_maximal_when_first
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (hS_binary : S ⊆ {x | ∀ i, x i = 0 ∨ x i = 1})
    (hbase :
      is_valid_inequality
        {x | x ∈ S ∧ ∀ k, k ∉ C → x k = 0}
        (base_coefficients C α)
        β)
    {j : ι}
    (hj : j ∉ C)
    (σ : List ι)
    (hσ : IsSequentialLiftingOrder C σ)
    (hσ_feasible : IsFeasibleSequentialLiftingOrder S C σ)
    (hfront_feasible : IsFeasibleSequentialLiftingOrder S C (j :: σ.erase j)) :
    (sequential_lifting_coefficients S C α β σ) j ≤
      (sequential_lifting_coefficients S C α β (j :: σ.erase j)) j := by
  let _ := hbase
  let _ := hσ_feasible
  have hjσ : j ∈ σ := (hσ.mem_iff).2 hj
  rcases splitAtMem hjσ with ⟨pre, tail, hsplit⟩
  have hnodup : (pre ++ j :: tail).Nodup := by
    simpa [hsplit] using hσ.nodup
  have hjtail : j ∉ tail := (splitNodupFacts (pre := pre) (tail := tail) (j := j) hnodup).2.1
  have hfrontOrder : IsSequentialLiftingOrder C (j :: σ.erase j) :=
    IsSequentialLiftingOrder.cons_erase hσ hj
  have hjerase : j ∉ σ.erase j := by
    have hfrontNodup : j ∉ σ.erase j ∧ (σ.erase j).Nodup := by
      simpa using hfrontOrder.nodup
    exact hfrontNodup.1
  have hσcoord :
      (sequential_lifting_coefficients S C α β σ) j =
        next_sequential_lifting_coefficient S C
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).1
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).2
          β
          j := by
    rw [sequentialLiftingRunEqPublic]
    simpa [hsplit] using
      sequentialLiftingRunCoordinateAtSplit
        S C β ∅ (base_coefficients C α) pre tail hjtail
  have hfrontCoord :
      (sequential_lifting_coefficients S C α β (j :: σ.erase j)) j =
        next_sequential_lifting_coefficient S C ∅ (base_coefficients C α) β j := by
    rw [sequentialLiftingRunEqPublic]
    simpa using
      sequentialLiftingRunCoordinateAtSplit
        S C β ∅ (base_coefficients C α) [] (σ.erase j) hjerase
  -- Compare the stage coefficient inside `σ` with the coefficient obtained by moving `j` to the
  -- front, then rewrite both public coordinates to those stage values.
  calc
    (sequential_lifting_coefficients S C α β σ) j
        =
          next_sequential_lifting_coefficient S C
            (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).1
            (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).2
            β
            j := hσcoord
    _ ≤ next_sequential_lifting_coefficient S C ∅ (base_coefficients C α) β j :=
      splitStageCoefficientLeFirstStage S C α β hS_binary σ pre tail hσ hsplit hfront_feasible
    _ = (sequential_lifting_coefficients S C α β (j :: σ.erase j)) j := hfrontCoord.symm

/-- Part (2) of Exercise 7.7. Under the same hypotheses, the coefficient of `x_j` is
smallest when `x_j` is lifted last in the order among feasible admissible lifting orders.
Equivalently, moving
`j` to the end of any admissible lifting order with nonempty stagewise lifting slices can only
decrease the lifted coefficient assigned to `j`. -/
theorem exercise_7_7_lifting_coefficient_minimal_when_last
    [Fintype ι]
    (S : Set (ι → ℝ))
    (C : Finset ι)
    (α : ι → ℝ)
    (β : ℝ)
    (hS_binary : S ⊆ {x | ∀ i, x i = 0 ∨ x i = 1})
    (hbase :
      is_valid_inequality
        {x | x ∈ S ∧ ∀ k, k ∉ C → x k = 0}
        (base_coefficients C α)
        β)
    {j : ι}
    (hj : j ∉ C)
    (σ : List ι)
    (hσ : IsSequentialLiftingOrder C σ)
    (hσ_feasible : IsFeasibleSequentialLiftingOrder S C σ)
    (hlast_feasible : IsFeasibleSequentialLiftingOrder S C (σ.erase j ++ [j])) :
    (sequential_lifting_coefficients S C α β (σ.erase j ++ [j])) j ≤
      (sequential_lifting_coefficients S C α β σ) j := by
  let _ := hbase
  let _ := hlast_feasible
  have hjσ : j ∈ σ := (hσ.mem_iff).2 hj
  rcases splitAtMem hjσ with ⟨pre, tail, hsplit⟩
  have hnodup : (pre ++ j :: tail).Nodup := by
    simpa [hsplit] using hσ.nodup
  have hjtail : j ∉ tail := (splitNodupFacts (pre := pre) (tail := tail) (j := j) hnodup).2.1
  have hlastCoord :
      (sequential_lifting_coefficients S C α β (σ.erase j ++ [j])) j =
        next_sequential_lifting_coefficient S C
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) (σ.erase j)).1
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) (σ.erase j)).2
          β
          j := by
    rw [sequentialLiftingRunEqPublic]
    simpa using
      sequentialLiftingRunCoordinateAtSplit
        S C β ∅ (base_coefficients C α) (σ.erase j) [] (by simp)
  have hσcoord :
      (sequential_lifting_coefficients S C α β σ) j =
        next_sequential_lifting_coefficient S C
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).1
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).2
          β
          j := by
    rw [sequentialLiftingRunEqPublic]
    simpa [hsplit] using
      sequentialLiftingRunCoordinateAtSplit
        S C β ∅ (base_coefficients C α) pre tail hjtail
  -- Compare the last-stage coefficient with the split-stage coefficient inside `σ`, then rewrite
  -- both public coordinates to those stage values.
  calc
    (sequential_lifting_coefficients S C α β (σ.erase j ++ [j])) j
        =
          next_sequential_lifting_coefficient S C
            (sequentialLiftingRun S C β ∅ (base_coefficients C α) (σ.erase j)).1
            (sequentialLiftingRun S C β ∅ (base_coefficients C α) (σ.erase j)).2
            β
            j := hlastCoord
    _ ≤ next_sequential_lifting_coefficient S C
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).1
          (sequentialLiftingRun S C β ∅ (base_coefficients C α) pre).2
          β
          j := lastStageCoefficientLeSplitStage S C α β hS_binary σ pre tail hσ hsplit hσ_feasible
    _ = (sequential_lifting_coefficients S C α β σ) j := hσcoord.symm

end Exercise77
