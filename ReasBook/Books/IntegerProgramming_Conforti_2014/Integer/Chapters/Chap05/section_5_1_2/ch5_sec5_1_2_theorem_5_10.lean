/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_1.ch5_sec5_1_1_lemma_5_4.MixedCut
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Order.WellFoundedSet

open scoped Matrix

-- Semantic recall note: this file keeps the source-facing mixed-space split owners from
-- Theorem 5.10, while exposing them as thin bridges to the canonical Chapter 5 split-hull owner
-- on the flattened ambient space `ℝ^(nI + nC)`.

section Theorem510

variable {nI nC : ℕ}

/-- The mixed split hull `P^(π, π₀)` is the convex hull of the two split branches cut out by the
integer-block split data `(π, π₀)` on `P ⊆ ℝ^I × ℝ^C`. -/
def mixed_split_hull
    (P : Set (MixedRealPoint nI nC))
    (π : Fin nI → ℤ)
    (π0 : ℤ) : Set (MixedRealPoint nI nC) :=
  convexHull ℝ
    ({xy : MixedRealPoint nI nC |
        xy ∈ P ∧ (fun i : Fin nI ↦ (π i : ℝ)) ⬝ᵥ xy.1 ≤ (π0 : ℝ)} ∪
      {xy : MixedRealPoint nI nC |
        xy ∈ P ∧ (π0 : ℝ) + 1 ≤ (fun i : Fin nI ↦ (π i : ℝ)) ⬝ᵥ xy.1})

private lemma isLinearMap_appendEquiv :
    IsLinearMap ℝ
      (Fin.appendEquiv nI nC : MixedRealPoint nI nC → Fin (nI + nC) → ℝ) := by
  refine ⟨?_, ?_⟩
  · intro x y
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]
  · intro a x
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]

private lemma appendEquiv_image_convexHull
    (S : Set (MixedRealPoint nI nC)) :
    (Fin.appendEquiv nI nC : MixedRealPoint nI nC → Fin (nI + nC) → ℝ) '' convexHull ℝ S =
      convexHull ℝ
        ((Fin.appendEquiv nI nC : MixedRealPoint nI nC → Fin (nI + nC) → ℝ) '' S) := by
  simpa using isLinearMap_appendEquiv.image_convexHull S

private theorem appendEquiv_image_mixed_split_branch_lower
    (P : Set (MixedRealPoint nI nC))
    (π : Fin nI → ℤ)
    (π0 : ℤ) :
    Fin.appendEquiv nI nC ''
        {xy : MixedRealPoint nI nC |
          xy ∈ P ∧ (fun i : Fin nI ↦ (π i : ℝ)) ⬝ᵥ xy.1 ≤ (π0 : ℝ)} =
      split_branch_lower
        (Fin.appendEquiv nI nC '' P)
        (Fin.append π (fun _ : Fin nC ↦ (0 : ℤ))) π0 := by
  ext u
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    refine (mem_split_branch_lower_iff).2 ?_
    refine ⟨⟨xy, hxy.1, rfl⟩, ?_⟩
    simpa [split_dot, dotProduct, Fin.sum_univ_add] using hxy.2
  · intro hu
    rcases (mem_split_branch_lower_iff).1 hu with ⟨huP, huπ⟩
    rcases huP with ⟨xy, hxyP, rfl⟩
    refine ⟨xy, ⟨hxyP, ?_⟩, rfl⟩
    simpa [split_dot, dotProduct, Fin.sum_univ_add] using huπ

private theorem appendEquiv_image_mixed_split_branch_upper
    (P : Set (MixedRealPoint nI nC))
    (π : Fin nI → ℤ)
    (π0 : ℤ) :
    Fin.appendEquiv nI nC ''
        {xy : MixedRealPoint nI nC |
          xy ∈ P ∧ (π0 : ℝ) + 1 ≤ (fun i : Fin nI ↦ (π i : ℝ)) ⬝ᵥ xy.1} =
      split_branch_upper
        (Fin.appendEquiv nI nC '' P)
        (Fin.append π (fun _ : Fin nC ↦ (0 : ℤ))) π0 := by
  ext u
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    refine (mem_split_branch_upper_iff).2 ?_
    refine ⟨⟨xy, hxy.1, rfl⟩, ?_⟩
    simpa [split_dot, dotProduct, Fin.sum_univ_add] using hxy.2
  · intro hu
    rcases (mem_split_branch_upper_iff).1 hu with ⟨huP, huπ⟩
    rcases huP with ⟨xy, hxyP, rfl⟩
    refine ⟨xy, ⟨hxyP, ?_⟩, rfl⟩
    simpa [split_dot, dotProduct, Fin.sum_univ_add] using huπ

/-- Flattening by `Fin.appendEquiv` turns the mixed split hull into the canonical Chapter 5 split
hull cut out by the supported coefficient vector `Fin.append π 0` on `ℝ^(nI + nC)`. -/
theorem appendEquiv_image_mixed_split_hull
    (P : Set (MixedRealPoint nI nC))
    (π : Fin nI → ℤ)
    (π0 : ℤ) :
    Fin.appendEquiv nI nC '' mixed_split_hull P π π0 =
      split_hull
        (Fin.appendEquiv nI nC '' P)
        (Fin.append π (fun _ : Fin nC ↦ (0 : ℤ))) π0 := by
  rw [mixed_split_hull, split_hull, appendEquiv_image_convexHull, Set.image_union,
    appendEquiv_image_mixed_split_branch_lower, appendEquiv_image_mixed_split_branch_upper]

/-- The mixed split closure `P^split` is the intersection of `P^(π, π₀)` over all nonzero
integral split vectors on the integer block and all integral right-hand sides. -/
def mixed_split_closure
    (P : Set (MixedRealPoint nI nC)) : Set (MixedRealPoint nI nC) :=
  ⋂ π : {π : Fin nI → ℤ // π ≠ 0}, ⋂ π0 : ℤ, mixed_split_hull P π.1 π0

/-- Membership in `mixed_split_closure P` means belonging to every mixed split hull
`P^(π, π₀)` defined by nonzero integral split data on the integer block. -/
theorem mem_mixed_split_closure_iff
    (P : Set (MixedRealPoint nI nC))
    (xy : MixedRealPoint nI nC) :
    xy ∈ mixed_split_closure P ↔
      ∀ π : {π : Fin nI → ℤ // π ≠ 0}, ∀ π0 : ℤ, xy ∈ mixed_split_hull P π.1 π0 := by
  simp [mixed_split_closure]

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the rational block
matrix obtained by concatenating the integer and continuous constraint columns. -/
private def rationalMixedConstraintMatrix
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ) :
    Matrix (Fin m) (Fin (nI + nC)) ℚ :=
  fun i ↦ Fin.addCases (A_I i) (A_C i)

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: casting the rational
block matrix gives the corresponding real mixed constraint matrix. -/
private lemma rationalMixedConstraintMatrix_map
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ) :
    (rationalMixedConstraintMatrix A_I A_C).map (Rat.castHom ℝ) =
      mixedConstraintMatrix (A_I.map (Rat.castHom ℝ)) (A_C.map (Rat.castHom ℝ)) := by
  ext i j
  refine Fin.addCases ?_ ?_ j
  · intro jI
    simp [rationalMixedConstraintMatrix, mixedConstraintMatrix]
  · intro jC
    simp [rationalMixedConstraintMatrix, mixedConstraintMatrix]

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: flattening a rational
mixed polyhedron gives the ordinary polyhedron defined by its real block matrix. -/
private lemma appendEquiv_image_rationalMixedPolyhedron
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (b : Fin m → ℚ) :
    Fin.appendEquiv nI nC '' rational_mixed_polyhedron A_I A_C b =
      polyhedron_le_set
        (mixedConstraintMatrix (A_I.map (Rat.castHom ℝ)) (A_C.map (Rat.castHom ℝ)))
        (fun i ↦ (b i : ℝ)) := by
  ext z
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    rw [mem_rational_mixed_polyhedron_iff] at hxy
    rw [mem_polyhedron_le_set_iff]
    simpa [Fin.appendEquiv, mixedConstraintMatrix_mulVec_append] using hxy
  · intro hz
    refine ⟨(Fin.appendEquiv nI nC).symm z, ?_, ?_⟩
    · rw [mem_rational_mixed_polyhedron_iff]
      rw [mem_polyhedron_le_set_iff] at hz
      have hzeq :
          Fin.append (fun i ↦ z (Fin.castAdd nC i))
            (fun i ↦ z (Fin.natAdd nI i)) = z :=
        Fin.append_castAdd_natAdd
      rw [← hzeq] at hz
      simpa [Fin.appendEquiv, mixedConstraintMatrix_mulVec_append] using hz
    · exact (Fin.appendEquiv nI nC).apply_symm_apply z

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: every explicit
rational mixed system is rational under the canonical flattening definition. -/
private lemma rationalMixedPolyhedronIsRational
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (b : Fin m → ℚ) :
    is_rational_mixed_polyhedron (rational_mixed_polyhedron A_I A_C b) := by
  change is_rational_polyhedron
    (Fin.appendEquiv nI nC '' rational_mixed_polyhedron A_I A_C b)
  refine ⟨m, rationalMixedConstraintMatrix A_I A_C, b, ?_⟩
  rw [appendEquiv_image_rationalMixedPolyhedron, rationalMixedConstraintMatrix_map]

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a rational mixed
polyhedron admits an explicit rational block-system presentation. -/
private lemma existsRationalMixedPolyhedronPresentation
    (P : Set (MixedRealPoint nI nC))
    (hP : is_rational_mixed_polyhedron P) :
    ∃ m : ℕ,
      ∃ A_I : Matrix (Fin m) (Fin nI) ℚ,
        ∃ A_C : Matrix (Fin m) (Fin nC) ℚ,
          ∃ b : Fin m → ℚ, P = rational_mixed_polyhedron A_I A_C b := by
  change is_rational_polyhedron (Fin.appendEquiv nI nC '' P) at hP
  rcases hP with ⟨m, C, b, hflat⟩
  let A_I : Matrix (Fin m) (Fin nI) ℚ := fun i j ↦ C i (Fin.castAdd nC j)
  let A_C : Matrix (Fin m) (Fin nC) ℚ := fun i j ↦ C i (Fin.natAdd nI j)
  have hblocks : rationalMixedConstraintMatrix A_I A_C = C := by
    ext i j
    refine Fin.addCases ?_ ?_ j
    · intro jI
      simp [rationalMixedConstraintMatrix, A_I]
    · intro jC
      simp [rationalMixedConstraintMatrix, A_C]
  refine ⟨m, A_I, A_C, b, ?_⟩
  apply (Fin.appendEquiv nI nC).injective.image_injective
  rw [hflat, appendEquiv_image_rationalMixedPolyhedron,
    ← rationalMixedConstraintMatrix_map, hblocks]

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: appending a zero
continuous block preserves nonzeroness of an integer split vector. -/
private lemma flatMixedSplitNonzero
    {π : Fin nI → ℤ}
    (hπ : π ≠ 0) :
    Fin.append π (fun _ : Fin nC ↦ (0 : ℤ)) ≠ 0 := by
  -- Restriction to the integer block recovers the original split vector.
  intro happ
  apply hπ
  funext j
  have hcoord := congrFun happ (Fin.castAdd nC j)
  simpa using hcoord

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a split using all
flattened coordinates has a vacuous continuous-coordinate condition. -/
private lemma flatMixedSplitZeroOnContinuous
    (π : Fin nI → ℤ) :
    ∀ j ∈ (Finset.univ : Finset (Fin (nI + nC)))ᶜ,
      Fin.append π (fun _ : Fin nC ↦ (0 : ℤ)) j = 0 := by
  -- The complement of `Finset.univ` is empty.
  intro j hj
  simp at hj

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: package mixed split
data as a split of the flattened ambient space. -/
private def theorem510FlatMixedSplit
    (π : Fin nI → ℤ)
    (π0 : ℤ)
    (hπ : π ≠ 0) :
    Split (Finset.univ : Finset (Fin (nI + nC))) where
  π := Fin.append π (fun _ : Fin nC ↦ (0 : ℤ))
  π0 := π0
  nonzero := flatMixedSplitNonzero (nC := nC) hπ
  zero_on_continuous := flatMixedSplitZeroOnContinuous (nC := nC) π

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: flattening a mixed
split hull of a matrix polyhedron gives the corresponding split polyhedron. -/
private lemma memMixedSplitHullIffFlatSplitPolyhedron
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (π0 : ℤ)
    (hπ : π ≠ 0)
    (xy : MixedRealPoint nI nC) :
    xy ∈ mixed_split_hull (real_mixed_polyhedron A_I A_C b) π π0 ↔
      Fin.append xy.1 xy.2 ∈
        split_polyhedron (mixedConstraintMatrix A_I A_C) b
          (theorem510FlatMixedSplit π π0 hπ) := by
  have hflatSet :
      Fin.appendEquiv nI nC '' mixed_split_hull (real_mixed_polyhedron A_I A_C b) π π0 =
        split_polyhedron (mixedConstraintMatrix A_I A_C) b
          (theorem510FlatMixedSplit π π0 hπ) := by
    -- Apply the two established flattening interfaces once at the set level.
    rw [appendEquiv_image_mixed_split_hull,
      image_real_mixed_polyhedron_eq_polyhedron_le_set A_I A_C b]
    rfl
  constructor
  · intro hxy
    have hflatImage :
        Fin.appendEquiv nI nC xy ∈
          Fin.appendEquiv nI nC '' mixed_split_hull
            (real_mixed_polyhedron A_I A_C b) π π0 :=
      ⟨xy, hxy, rfl⟩
    rw [hflatSet] at hflatImage
    simpa [Fin.appendEquiv] using hflatImage
  · intro hflat
    have hflatImage :
        Fin.appendEquiv nI nC xy ∈
          Fin.appendEquiv nI nC '' mixed_split_hull
            (real_mixed_polyhedron A_I A_C b) π π0 := by
      rw [hflatSet]
      simpa [Fin.appendEquiv] using hflat
    rcases hflatImage with ⟨xyPreimage, hxyPreimageMem, hxyPreimageEq⟩
    have hxyEq : xyPreimage = xy :=
      (Fin.appendEquiv nI nC).injective hxyPreimageEq
    simpa [hxyEq] using hxyPreimageMem

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a basic multiplier
for the flattened split is exactly an independent-support mixed row multiplier. -/
private lemma memBasicRowMultiplierSetFlatMixedSplitIff
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (π : Fin nI → ℤ)
    (π0 : ℤ)
    (hπ : π ≠ 0)
    (u : Fin m → ℝ) :
    u ∈ basic_row_multiplier_set (mixedConstraintMatrix A_I A_C)
        (theorem510FlatMixedSplit π π0 hπ) ↔
      u ᵥ* A_I = (fun j : Fin nI ↦ (π j : ℝ)) ∧
        u ᵥ* A_C = 0 ∧
          RowMultiplierHasIndependentSupportRows (mixedConstraintMatrix A_I A_C) u := by
  constructor
  · intro hu
    rcases (mem_basic_row_multiplier_set_iff
        (mixedConstraintMatrix A_I A_C) (theorem510FlatMixedSplit π π0 hπ) u).mp hu with
      ⟨huRow, huIndep⟩
    refine ⟨?_, ?_, huIndep⟩
    · -- Read the integer block of the flattened row equation.
      ext j
      have hcoord := congrFun huRow (Fin.castAdd nC j)
      simpa [mixedConstraintMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_add,
        theorem510FlatMixedSplit] using hcoord
    · -- Read the continuous block of the same row equation.
      ext j
      have hcoord := congrFun huRow (Fin.natAdd nI j)
      simpa [mixedConstraintMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_add,
        theorem510FlatMixedSplit] using hcoord
  · rintro ⟨huAI, huAC, huIndep⟩
    refine (mem_basic_row_multiplier_set_iff
      (mixedConstraintMatrix A_I A_C) (theorem510FlatMixedSplit π π0 hπ) u).2 ?_
    refine ⟨?_, huIndep⟩
    -- Reassemble the two block equations into the flattened row equation.
    ext j
    refine Fin.addCases ?_ ?_ j
    · intro jI
      simpa [mixedConstraintMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_add,
        theorem510FlatMixedSplit] using congrFun huAI jI
    · intro jC
      simpa [mixedConstraintMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_add,
        theorem510FlatMixedSplit] using congrFun huAC jC

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a violating basic
flat multiplier supplies the corresponding mixed multiplier and identifies its floor. -/
private lemma flatBasicViolationToMixedMultiplier
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (π0 : ℤ)
    (hπ : π ≠ 0)
    (u : Fin m → ℝ)
    (huBasic :
      u ∈ basic_row_multiplier_set (mixedConstraintMatrix A_I A_C)
        (theorem510FlatMixedSplit π π0 hπ))
    (hub_left : (π0 : ℝ) < u ⬝ᵥ b)
    (hub_right : u ⬝ᵥ b < (π0 : ℝ) + 1) :
    IsMixedGomoryFractionalCutMultiplier A_I A_C b u ∧
      RowMultiplierHasIndependentSupportRows (mixedConstraintMatrix A_I A_C) u ∧
      Int.floor (u ⬝ᵥ b) = π0 := by
  rcases (memBasicRowMultiplierSetFlatMixedSplitIff
      A_I A_C π π0 hπ u).mp huBasic with ⟨huAI, huAC, huIndep⟩
  have huMixed : IsMixedGomoryFractionalCutMultiplier A_I A_C b u := by
    -- The strict strip inequalities rule out an integral right-hand-side value.
    refine ⟨?_, huAC, ?_⟩
    · intro j
      refine ⟨π j, ?_⟩
      simpa using congrFun huAI j
    · rintro ⟨z, hz⟩
      rw [hz] at hub_left hub_right
      have hz_lower : π0 < z := by
        exact_mod_cast hub_left
      have hz_upper : π0 + 1 ≤ z := Int.add_one_le_iff.mpr hz_lower
      have hz_upper_real : (π0 : ℝ) + 1 ≤ (z : ℝ) := by
        exact_mod_cast hz_upper
      linarith
  have hfloor : Int.floor (u ⬝ᵥ b) = π0 := by
    -- The strip is precisely the interval selecting this floor value.
    have hbounds :
        (π0 : ℝ) ≤ u ⬝ᵥ b ∧ u ⬝ᵥ b < (π0 : ℝ) + 1 := by
      exact ⟨le_of_lt hub_left, hub_right⟩
    exact Int.floor_eq_iff.mpr hbounds
  exact ⟨huMixed, huIndep, hfloor⟩

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: an ambient feasible
point belongs to every mixed hull cut out by the zero split vector. -/
private lemma memMixedSplitHullZeroOfMemRealMixedPolyhedron
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    {xy : MixedRealPoint nI nC}
    (hxy : xy ∈ real_mixed_polyhedron A_I A_C b)
    (π0 : ℤ) :
    xy ∈ mixed_split_hull (real_mixed_polyhedron A_I A_C b)
      (fun _ : Fin nI ↦ 0) π0 := by
  rw [mixed_split_hull]
  by_cases hπ0 : 0 ≤ π0
  · -- For nonnegative `π₀`, the lower branch contains every feasible point.
    refine subset_convexHull ℝ _ (Or.inl ?_)
    refine ⟨hxy, ?_⟩
    simp [hπ0]
  · -- Otherwise the upper branch contains every feasible point.
    have hupperInt : π0 + 1 ≤ 0 := Int.add_one_le_iff.mpr (lt_of_not_ge hπ0)
    refine subset_convexHull ℝ _ (Or.inr ?_)
    refine ⟨hxy, ?_⟩
    have hupperReal : (π0 : ℝ) + 1 ≤ (0 : ℝ) := by
      exact_mod_cast hupperInt
    simpa using hupperReal

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the difference of
positive- and negative-part slack evaluations is the scalar split gap. -/
private lemma mixedRowSlackGapEq
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (hπ : u ᵥ* A_I = fun i : Fin nI ↦ (π i : ℝ))
    (hAC : u ᵥ* A_C = 0)
    (xy : MixedRealPoint nI nC) :
    row_multiplier_pos u ⬝ᵥ (b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2)) -
        row_multiplier_neg u ⬝ᵥ (b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2)) =
      u ⬝ᵥ b - split_dot π xy.1 := by
  have hdecomp : row_multiplier_pos u - row_multiplier_neg u = u := by
    -- The positive and negative parts reconstruct each coordinate of `u`.
    ext i
    by_cases hi : 0 ≤ u i
    · have hneg : -u i ≤ 0 := by
        linarith
      simp [row_multiplier_pos, row_multiplier_neg, hi, hneg]
    · have hiNeg : u i < 0 := lt_of_not_ge hi
      have hneg : 0 ≤ -u i := by
        linarith
      simp [row_multiplier_pos, row_multiplier_neg, hiNeg.le, hneg]
  have hAu : u ⬝ᵥ (A_I *ᵥ xy.1) = split_dot π xy.1 := by
    rw [Matrix.dotProduct_mulVec, hπ, split_dot]
  have hCu : u ⬝ᵥ (A_C *ᵥ xy.2) = 0 := by
    simp [Matrix.dotProduct_mulVec, hAC]
  calc
    row_multiplier_pos u ⬝ᵥ (b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2)) -
        row_multiplier_neg u ⬝ᵥ (b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2)) =
        (row_multiplier_pos u - row_multiplier_neg u) ⬝ᵥ
          (b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2)) := by
            rw [sub_dotProduct]
    _ = u ⬝ᵥ (b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2)) := by
          rw [hdecomp]
    _ = u ⬝ᵥ b - u ⬝ᵥ (A_I *ᵥ xy.1 + A_C *ᵥ xy.2) := by
          rw [dotProduct_sub]
    _ = u ⬝ᵥ b - (u ⬝ᵥ (A_I *ᵥ xy.1) + u ⬝ᵥ (A_C *ᵥ xy.2)) := by
          rw [dotProduct_add]
    _ = u ⬝ᵥ b - split_dot π xy.1 := by
          rw [hAu, hCu]
          ring

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a mixed Gomory cut
is valid on the lower branch of its associated split. -/
private lemma mixedGomoryCutValidOnLowerBranch
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (hπ : u ᵥ* A_I = fun i : Fin nI ↦ (π i : ℝ))
    (hAC : u ᵥ* A_C = 0)
    (hub_nonint : ¬ ∃ z : ℤ, u ⬝ᵥ b = (z : ℝ))
    (xy : MixedRealPoint nI nC)
    (hslack : A_I *ᵥ xy.1 + A_C *ᵥ xy.2 ≤ b)
    (hlower : split_dot π xy.1 ≤ Int.floor (u ⬝ᵥ b)) :
    1 ≤ mixed_gomory_fractional_cut_value A_I A_C b u xy := by
  let r : Fin m → ℝ := b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2)
  let s1 : ℝ := row_multiplier_pos u ⬝ᵥ r
  let s2 : ℝ := row_multiplier_neg u ⬝ᵥ r
  have hub_not_mem : u ⬝ᵥ b ∉ Set.range (Int.cast : ℤ → ℝ) := by
    simpa [Set.mem_range, eq_comm] using hub_nonint
  have hf_ne : Int.fract (u ⬝ᵥ b) ≠ 0 :=
    (Int.fract_ne_zero_iff).2 hub_not_mem
  have hf_pos : 0 < Int.fract (u ⬝ᵥ b) :=
    lt_of_le_of_ne (Int.fract_nonneg _) hf_ne.symm
  have hf_lt_one : Int.fract (u ⬝ᵥ b) < 1 := Int.fract_lt_one _
  have hr_nonneg : 0 ≤ r := by
    -- Feasibility makes every slack coordinate nonnegative.
    intro i
    exact sub_nonneg.mpr (hslack i)
  have hneg_nonneg : 0 ≤ row_multiplier_neg u := by
    intro i
    simp [row_multiplier_neg]
  have hs2_nonneg : 0 ≤ s2 :=
    dotProduct_nonneg_of_nonneg hneg_nonneg hr_nonneg
  have hgapEq : s1 - s2 = u ⬝ᵥ b - split_dot π xy.1 := by
    simpa [r, s1, s2] using mixedRowSlackGapEq A_I A_C b u π hπ hAC xy
  have hgap : Int.fract (u ⬝ᵥ b) ≤ s1 - s2 := by
    rw [hgapEq, ← Int.self_sub_floor (u ⬝ᵥ b)]
    linarith
  -- The scalar fractional-cut estimate closes the normalized inequality.
  simpa [mixed_gomory_fractional_cut_value_eq, r, s1, s2] using
    one_le_fractionalCutExpr_of_lowerGap hf_pos hf_lt_one hs2_nonneg hgap

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a mixed Gomory cut
is valid on the upper branch of its associated split. -/
private lemma mixedGomoryCutValidOnUpperBranch
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (hπ : u ᵥ* A_I = fun i : Fin nI ↦ (π i : ℝ))
    (hAC : u ᵥ* A_C = 0)
    (hub_nonint : ¬ ∃ z : ℤ, u ⬝ᵥ b = (z : ℝ))
    (xy : MixedRealPoint nI nC)
    (hslack : A_I *ᵥ xy.1 + A_C *ᵥ xy.2 ≤ b)
    (hupper : (Int.floor (u ⬝ᵥ b) : ℝ) + 1 ≤ split_dot π xy.1) :
    1 ≤ mixed_gomory_fractional_cut_value A_I A_C b u xy := by
  let r : Fin m → ℝ := b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2)
  let s1 : ℝ := row_multiplier_pos u ⬝ᵥ r
  let s2 : ℝ := row_multiplier_neg u ⬝ᵥ r
  have hub_not_mem : u ⬝ᵥ b ∉ Set.range (Int.cast : ℤ → ℝ) := by
    simpa [Set.mem_range, eq_comm] using hub_nonint
  have hf_ne : Int.fract (u ⬝ᵥ b) ≠ 0 :=
    (Int.fract_ne_zero_iff).2 hub_not_mem
  have hf_pos : 0 < Int.fract (u ⬝ᵥ b) :=
    lt_of_le_of_ne (Int.fract_nonneg _) hf_ne.symm
  have hf_lt_one : Int.fract (u ⬝ᵥ b) < 1 := Int.fract_lt_one _
  have hr_nonneg : 0 ≤ r := by
    -- Feasibility makes every slack coordinate nonnegative.
    intro i
    exact sub_nonneg.mpr (hslack i)
  have hpos_nonneg : 0 ≤ row_multiplier_pos u := by
    intro i
    simp [row_multiplier_pos]
  have hs1_nonneg : 0 ≤ s1 :=
    dotProduct_nonneg_of_nonneg hpos_nonneg hr_nonneg
  have hgapEq : s1 - s2 = u ⬝ᵥ b - split_dot π xy.1 := by
    simpa [r, s1, s2] using mixedRowSlackGapEq A_I A_C b u π hπ hAC xy
  have hgap : 1 - Int.fract (u ⬝ᵥ b) ≤ s2 - s1 := by
    have hfract :
        1 - Int.fract (u ⬝ᵥ b) = (Int.floor (u ⬝ᵥ b) : ℝ) + 1 - u ⬝ᵥ b := by
      calc
        1 - Int.fract (u ⬝ᵥ b) =
            1 - (u ⬝ᵥ b - (Int.floor (u ⬝ᵥ b) : ℝ)) := by
              rw [Int.self_sub_floor]
        _ = (Int.floor (u ⬝ᵥ b) : ℝ) + 1 - u ⬝ᵥ b := by
              ring
    have hreverseGap : s2 - s1 = split_dot π xy.1 - u ⬝ᵥ b := by
      linarith [hgapEq]
    rw [hfract, hreverseGap]
    linarith
  -- The symmetric scalar estimate closes the normalized inequality.
  simpa [mixed_gomory_fractional_cut_value_eq, r, s1, s2] using
    one_le_fractionalCutExpr_of_upperGap hf_pos hf_lt_one hs1_nonneg hgap

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a mixed Gomory cut
value is affine on binary convex combinations. -/
private lemma mixedGomoryCutValueConvexCombination
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (α β : ℝ)
    (hαβ : α + β = 1)
    (x y : MixedRealPoint nI nC) :
    mixed_gomory_fractional_cut_value A_I A_C b u (α • x + β • y) =
      α * mixed_gomory_fractional_cut_value A_I A_C b u x +
        β * mixed_gomory_fractional_cut_value A_I A_C b u y := by
  have hslack :
      b - (A_I *ᵥ (α • x.1 + β • y.1) + A_C *ᵥ (α • x.2 + β • y.2)) =
        α • (b - (A_I *ᵥ x.1 + A_C *ᵥ x.2)) +
          β • (b - (A_I *ᵥ y.1 + A_C *ᵥ y.2)) := by
    -- Matrix multiplication distributes over the convex combination.
    ext i
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hβ : β = 1 - α := by
      linarith
    rw [hβ]
    ring
  have hcutCombo :
      mixed_gomory_fractional_cut_value A_I A_C b u (α • x + β • y) =
        row_multiplier_pos u ⬝ᵥ
            (b - (A_I *ᵥ (α • x.1 + β • y.1) + A_C *ᵥ (α • x.2 + β • y.2))) /
          Int.fract (u ⬝ᵥ b) +
          row_multiplier_neg u ⬝ᵥ
            (b - (A_I *ᵥ (α • x.1 + β • y.1) + A_C *ᵥ (α • x.2 + β • y.2))) /
            (1 - Int.fract (u ⬝ᵥ b)) := by
    simpa using mixed_gomory_fractional_cut_value_eq A_I A_C b u (α • x + β • y)
  rw [hcutCombo, mixed_gomory_fractional_cut_value_eq,
    mixed_gomory_fractional_cut_value_eq]
  rw [hslack, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_add, dotProduct_smul, dotProduct_smul]
  simp [smul_eq_mul]
  ring

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the halfspace of
points satisfying one mixed Gomory cut is convex. -/
private lemma mixedGomoryCutHalfspaceConvex
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ) :
    Convex ℝ
      {xy : MixedRealPoint nI nC |
        1 ≤ mixed_gomory_fractional_cut_value A_I A_C b u xy} := by
  intro x hx y hy α β hα_nonneg hβ_nonneg hαβ
  -- Affinity turns the two endpoint inequalities into the convex-combination inequality.
  have hxBound : 1 ≤ mixed_gomory_fractional_cut_value A_I A_C b u x := hx
  have hyBound : 1 ≤ mixed_gomory_fractional_cut_value A_I A_C b u y := hy
  change 1 ≤ mixed_gomory_fractional_cut_value A_I A_C b u (α • x + β • y)
  rw [mixedGomoryCutValueConvexCombination A_I A_C b u α β hαβ x y]
  nlinarith [hxBound, hyBound]

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the mixed Gomory
cut of a bundled multiplier is valid throughout its associated split hull. -/
private theorem mixedGomoryCutValidOnSplitHull
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (π : Fin nI → ℤ)
    (hπ : u ᵥ* A_I = fun i : Fin nI ↦ (π i : ℝ))
    (hu : IsMixedGomoryFractionalCutMultiplier A_I A_C b u)
    (xy : MixedRealPoint nI nC)
    (hxy :
      xy ∈ mixed_split_hull (real_mixed_polyhedron A_I A_C b) π
        (Int.floor (u ⬝ᵥ b))) :
    1 ≤ mixed_gomory_fractional_cut_value A_I A_C b u xy := by
  rw [mixed_split_hull] at hxy
  have hsubset :
      {z : MixedRealPoint nI nC |
          z ∈ real_mixed_polyhedron A_I A_C b ∧
            (fun i : Fin nI ↦ (π i : ℝ)) ⬝ᵥ z.1 ≤ (Int.floor (u ⬝ᵥ b) : ℝ)} ∪
        {z : MixedRealPoint nI nC |
          z ∈ real_mixed_polyhedron A_I A_C b ∧
            (Int.floor (u ⬝ᵥ b) : ℝ) + 1 ≤
              (fun i : Fin nI ↦ (π i : ℝ)) ⬝ᵥ z.1} ⊆
        {z : MixedRealPoint nI nC |
          1 ≤ mixed_gomory_fractional_cut_value A_I A_C b u z} := by
    intro z hz
    rcases hz with hz | hz
    · -- Apply the lower-branch scalar estimate after exposing matrix feasibility.
      exact mixedGomoryCutValidOnLowerBranch A_I A_C b u π hπ hu.2.1 hu.2.2 z
        (mem_real_mixed_polyhedron_iff.mp hz.1) hz.2
    · -- Apply the symmetric upper-branch estimate.
      exact mixedGomoryCutValidOnUpperBranch A_I A_C b u π hπ hu.2.1 hu.2.2 z
        (mem_real_mixed_polyhedron_iff.mp hz.1) hz.2
  exact convexHull_min hsubset (mixedGomoryCutHalfspaceConvex A_I A_C b u) hxy

-- Route correction: Corollary 5.6 imports this target through Lemma 5.4, so the needed
-- closure-to-cut-system equivalence is reconstructed here from the earlier Theorem 5.5 API.
/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the mixed split
closure of a real matrix system is its independent-support mixed cut system when `nI ≠ 0`. -/
private theorem mixedSplitClosureEqIndependentSupportCutSystem
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (hnI : nI ≠ 0) :
    mixed_split_closure (real_mixed_polyhedron A_I A_C b) =
      {xy | xy ∈ real_mixed_polyhedron A_I A_C b ∧
        ∀ u : Fin m → ℝ,
          IsMixedGomoryFractionalCutMultiplier A_I A_C b u →
            RowMultiplierHasIndependentSupportRows (mixedConstraintMatrix A_I A_C) u →
              1 ≤ mixed_gomory_fractional_cut_value A_I A_C b u xy} := by
  ext xy
  constructor
  · intro hxyClosure
    have hclosure := (mem_mixed_split_closure_iff
      (real_mixed_polyhedron A_I A_C b) xy).mp hxyClosure
    have hnI_pos : 0 < nI := Nat.pos_of_ne_zero hnI
    let j0 : Fin nI := ⟨0, hnI_pos⟩
    let πstar : Fin nI → ℤ := Pi.single j0 1
    have hπstar : πstar ≠ 0 := by
      -- A distinguished integer coordinate witnesses nonzeroness.
      intro hzero
      have hcoord := congrFun hzero j0
      simp [πstar] at hcoord
    have hxyStar := hclosure ⟨πstar, hπstar⟩ 0
    have hxyFlat :
        Fin.append xy.1 xy.2 ∈
          split_polyhedron (mixedConstraintMatrix A_I A_C) b
            (theorem510FlatMixedSplit πstar 0 hπstar) :=
      (memMixedSplitHullIffFlatSplitPolyhedron
        A_I A_C b πstar 0 hπstar xy).1 hxyStar
    have hxyPolyFlat := mem_polyhedron_of_memSplitPolyhedron
      (mixedConstraintMatrix A_I A_C) b
        (theorem510FlatMixedSplit πstar 0 hπstar) hxyFlat
    have hxyPoly : xy ∈ real_mixed_polyhedron A_I A_C b := by
      -- Translate the flattened feasibility condition back to the mixed system.
      rw [mem_polyhedron_le_set_iff, mixedConstraintMatrix_mulVec_append] at hxyPolyFlat
      exact mem_real_mixed_polyhedron_iff.mpr hxyPolyFlat
    refine ⟨hxyPoly, ?_⟩
    intro u hu _huIndep
    classical
    choose πu hπu using hu.1
    have hπuEq : u ᵥ* A_I = fun j : Fin nI ↦ (πu j : ℝ) := by
      funext j
      exact hπu j
    by_cases hπu_zero : πu = 0
    · have hxyZero :
          xy ∈ mixed_split_hull (real_mixed_polyhedron A_I A_C b) πu
            (Int.floor (u ⬝ᵥ b)) := by
        simpa [hπu_zero] using
          memMixedSplitHullZeroOfMemRealMixedPolyhedron
            A_I A_C b hxyPoly (Int.floor (u ⬝ᵥ b))
      exact mixedGomoryCutValidOnSplitHull
        A_I A_C b u πu hπuEq hu xy hxyZero
    · have hxySplit := hclosure ⟨πu, hπu_zero⟩ (Int.floor (u ⬝ᵥ b))
      exact mixedGomoryCutValidOnSplitHull
        A_I A_C b u πu hπuEq hu xy hxySplit
  · rintro ⟨hxyPoly, hxyCuts⟩
    rw [mem_mixed_split_closure_iff]
    intro π π0
    have hxyPolyFlat :
        Fin.append xy.1 xy.2 ∈ polyhedron_le_set (mixedConstraintMatrix A_I A_C) b := by
      rw [mem_polyhedron_le_set_iff, mixedConstraintMatrix_mulVec_append]
      exact mem_real_mixed_polyhedron_iff.mp hxyPoly
    have hflat :
        Fin.append xy.1 xy.2 ∈
          split_polyhedron (mixedConstraintMatrix A_I A_C) b
            (theorem510FlatMixedSplit π.1 π0 π.2) := by
      -- Theorem 5.5 reduces the fixed split hull to its basic cut system.
      rw [split_polyhedron_eq_basic_split_cut_system
        (mixedConstraintMatrix A_I A_C) b (theorem510FlatMixedSplit π.1 π0 π.2)]
      refine (mem_basic_split_cut_system_iff
        (mixedConstraintMatrix A_I A_C) b
          (theorem510FlatMixedSplit π.1 π0 π.2) π0
            (Fin.append xy.1 xy.2)).2 ?_
      refine ⟨hxyPolyFlat, ?_⟩
      intro u huBasic hub_left hub_right
      rcases flatBasicViolationToMixedMultiplier
          A_I A_C b π.1 π0 π.2 u huBasic hub_left hub_right with
        ⟨huMixed, huIndep, hfloor⟩
      have hcut := hxyCuts u huMixed huIndep
      rw [mixed_gomory_fractional_cut_value_eq_split_cut_value, hfloor] at hcut
      exact hcut
    exact (memMixedSplitHullIffFlatSplitPolyhedron
      A_I A_C b π.1 π0 π.2 xy).2 hflat

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: when the integer
block is empty, there are no nonzero split vectors and the mixed split closure is universal. -/
private lemma mixedSplitClosureEqUnivOfIntegerDimensionZero
    (P : Set (MixedRealPoint 0 nC)) :
    mixed_split_closure P = Set.univ := by
  -- The indexing subtype of nonzero functions `Fin 0 → ℤ` is empty.
  ext xy
  constructor
  · intro _
    trivial
  · intro _
    rw [mem_mixed_split_closure_iff]
    intro π
    exfalso
    apply π.2
    funext i
    exact Fin.elim0 i

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the universal mixed
set has a rational presentation with no inequalities. -/
private lemma univIsRationalMixedPolyhedron :
    is_rational_mixed_polyhedron (Set.univ : Set (MixedRealPoint nI nC)) := by
  -- Use the empty rational row system.
  have huniv :
      (Set.univ : Set (MixedRealPoint nI nC)) =
        rational_mixed_polyhedron
          (0 : Matrix (Fin 0) (Fin nI) ℚ)
          (0 : Matrix (Fin 0) (Fin nC) ℚ) (0 : Fin 0 → ℚ) := by
    ext xy
    simp [rational_mixed_polyhedron]
  rw [huniv]
  exact rationalMixedPolyhedronIsRational 0 0 0

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the normalized
coefficient of a slack coordinate in the mixed Gomory fractional cut generated by `u`. -/
private noncomputable def normalizedMixedCutCoefficient
    (b : Fin m → ℝ)
    (u : Fin m → ℝ) : Fin m → ℝ :=
  fun i ↦ row_multiplier_pos u i / Int.fract (u ⬝ᵥ b) +
    row_multiplier_neg u i / (1 - Int.fract (u ⬝ᵥ b))

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: every normalized
mixed-cut coefficient is nonnegative for a genuine fractional multiplier. -/
private lemma normalizedMixedCutCoefficient_nonneg
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (hu : IsMixedGomoryFractionalCutMultiplier A_I A_C b u) :
    0 ≤ normalizedMixedCutCoefficient b u := by
  have hub_not_mem : u ⬝ᵥ b ∉ Set.range (Int.cast : ℤ → ℝ) := by
    simpa [Set.mem_range, eq_comm] using hu.2.2
  have hf_ne : Int.fract (u ⬝ᵥ b) ≠ 0 :=
    (Int.fract_ne_zero_iff).2 hub_not_mem
  have hf_pos : 0 < Int.fract (u ⬝ᵥ b) :=
    lt_of_le_of_ne (Int.fract_nonneg _) hf_ne.symm
  have hf_lt_one : Int.fract (u ⬝ᵥ b) < 1 := Int.fract_lt_one _
  -- Both sign parts and both fractional denominators are nonnegative.
  intro i
  unfold normalizedMixedCutCoefficient
  have hposPart : 0 ≤ row_multiplier_pos u i := by
    simp [row_multiplier_pos]
  have hnegPart : 0 ≤ row_multiplier_neg u i := by
    simp [row_multiplier_neg]
  exact add_nonneg
    (div_nonneg hposPart hf_pos.le)
    (div_nonneg hnegPart (sub_nonneg.mpr hf_lt_one.le))

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the existing mixed
cut value is the dot product of its normalized coefficient vector with the slack vector. -/
private lemma normalizedMixedCutCoefficient_spec
    (A_I : Matrix (Fin m) (Fin nI) ℝ)
    (A_C : Matrix (Fin m) (Fin nC) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (xy : MixedRealPoint nI nC) :
    mixed_gomory_fractional_cut_value A_I A_C b u xy =
      normalizedMixedCutCoefficient b u ⬝ᵥ
        (b - (A_I *ᵥ xy.1 + A_C *ᵥ xy.2)) := by
  -- Distribute the finite dot product over the two normalized sign parts.
  rw [mixed_gomory_fractional_cut_value_eq]
  unfold normalizedMixedCutCoefficient dotProduct
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: this rational
matrix records the integer-block equation, the continuous-block equation, and vanishing outside
a prescribed row support. -/
private noncomputable def independentSupportRationalSystemMatrix
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (B : Finset (Fin m)) : Matrix (Fin ((nI + nC) + m)) (Fin m) ℚ :=
  fun k i ↦
    Fin.addCases
      (fun j ↦ Fin.addCases (fun jI ↦ A_I i jI) (fun jC ↦ A_C i jC) j)
      (fun r ↦ if r ∉ B ∧ r = i then 1 else 0) k

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: this integral
right-hand side packages an integer-block row together with the two zero blocks. -/
private def independentSupportIntegralSystemRhs
    (z : Fin nI → ℤ) : Fin ((nI + nC) + m) → ℤ :=
  Fin.append (Fin.append z (fun _ ↦ 0)) (fun _ ↦ 0)

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the rational support
system uses the cast of its integral right-hand side. -/
private def independentSupportRationalSystemRhs
    (z : Fin nI → ℤ) : Fin ((nI + nC) + m) → ℚ :=
  fun k ↦ (independentSupportIntegralSystemRhs z k : ℚ)

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a supported real row
multiplier solves the real scalar extension of the corresponding rational system. -/
private lemma independentSupportRationalSystem_realSolution
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (B : Finset (Fin m))
    (z : Fin nI → ℤ)
    (u : Fin m → ℝ)
    (huAI : u ᵥ* (A_I.map (Rat.castHom ℝ)) = fun j ↦ (z j : ℝ))
    (huAC : u ᵥ* (A_C.map (Rat.castHom ℝ)) = 0)
    (huSupport : ∀ i : Fin m, i ∉ B → u i = 0) :
    ((independentSupportRationalSystemMatrix A_I A_C B).map (Rat.castHom ℝ)) *ᵥ u =
      fun k ↦ (independentSupportRationalSystemRhs z k : ℝ) := by
  -- The first two blocks are the two prescribed row equations.
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro jI
      simpa [independentSupportRationalSystemMatrix,
        independentSupportRationalSystemRhs, independentSupportIntegralSystemRhs,
        Matrix.mulVec, Matrix.vecMul, dotProduct,
        mul_comm] using congrFun huAI jI
    · intro jC
      simpa [independentSupportRationalSystemMatrix,
        independentSupportRationalSystemRhs, independentSupportIntegralSystemRhs,
        Matrix.mulVec, Matrix.vecMul, dotProduct,
        mul_comm] using congrFun huAC jC
  · intro r
    by_cases hr : r ∈ B
    · simp [independentSupportRationalSystemMatrix,
        independentSupportRationalSystemRhs, independentSupportIntegralSystemRhs,
        Matrix.mulVec, hr]
    · have hdelta :
        (fun j : Fin m ↦ ((if r = j then (1 : ℚ) else 0 : ℚ) : ℝ)) ⬝ᵥ u =
            u r := by
        classical
        unfold dotProduct
        rw [Finset.sum_eq_single r]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · simp
      calc
        (((independentSupportRationalSystemMatrix A_I A_C B).map
            (Rat.castHom ℝ)) *ᵥ u) (Fin.natAdd (nI + nC) r) =
            (fun j : Fin m ↦ ((if r = j then (1 : ℚ) else 0 : ℚ) : ℝ)) ⬝ᵥ u := by
              simp [independentSupportRationalSystemMatrix, Matrix.mulVec, hr]
        _ = u r := hdelta
        _ = 0 := huSupport r hr
        _ = (independentSupportRationalSystemRhs z (Fin.natAdd (nI + nC) r) : ℝ) := by
              simp [independentSupportRationalSystemRhs,
                independentSupportIntegralSystemRhs]

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: independence of
the prescribed support makes the scalar-extended support system injective. -/
private lemma independentSupportRationalSystem_realInjective
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (B : Finset (Fin m))
    (hB : LinearIndependent ℝ
      (fun i : {i // i ∈ B} ↦
        mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
          (A_C.map (Rat.castHom ℝ)) i.1)) :
    Function.Injective
      (((independentSupportRationalSystemMatrix A_I A_C B).map
        (Rat.castHom ℝ)).mulVec) := by
  intro x y hxy
  let d : Fin m → ℝ := x - y
  have hdSystem :
      ((independentSupportRationalSystemMatrix A_I A_C B).map
        (Rat.castHom ℝ)) *ᵥ d = 0 := by
    -- Subtract the two system equations once, before reading their blocks.
    simp only [d, Matrix.mulVec_sub, hxy, sub_self]
  have hdOutside : ∀ i : Fin m, i ∉ B → d i = 0 := by
    intro i hi
    have hcoord := congrFun hdSystem (Fin.natAdd (nI + nC) i)
    have hdelta :
        (fun j : Fin m ↦ ((if i = j then (1 : ℚ) else 0 : ℚ) : ℝ)) ⬝ᵥ d =
          d i := by
      classical
      unfold dotProduct
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    have hdot :
        (fun j : Fin m ↦ ((if i = j then (1 : ℚ) else 0 : ℚ) : ℝ)) ⬝ᵥ d =
          0 := by
      simpa [independentSupportRationalSystemMatrix, Matrix.mulVec, hi] using hcoord
    exact hdelta.symm.trans hdot
  have hdRows :
      d ᵥ* mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
        (A_C.map (Rat.castHom ℝ)) = 0 := by
    -- The leading equation block says that the supported row combination vanishes.
    ext j
    refine Fin.addCases ?_ ?_ j
    · intro jI
      have hcoord := congrFun hdSystem
        (Fin.castAdd m (Fin.castAdd nC jI))
      simpa [independentSupportRationalSystemMatrix, mixedConstraintMatrix,
        Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm] using hcoord
    · intro jC
      have hcoord := congrFun hdSystem
        (Fin.castAdd m (Fin.natAdd nI jC))
      simpa [independentSupportRationalSystemMatrix, mixedConstraintMatrix,
        Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm] using hcoord
  have hdOnSupport : ∀ i : {i // i ∈ B}, d i.1 = 0 := by
    apply (Fintype.linearIndependent_iff.mp hB)
    -- Restrict the full zero row combination to `B`; all omitted coefficients vanish.
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    change ∑ i : {i // i ∈ B}, d i.1 *
        mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
          (A_C.map (Rat.castHom ℝ)) i.1 j = 0
    calc
      _ = ∑ i ∈ B, d i *
          mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
            (A_C.map (Rat.castHom ℝ)) i j := by
            simpa using Finset.sum_attach B
              (fun i : Fin m ↦ d i *
                mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
                  (A_C.map (Rat.castHom ℝ)) i j)
      _ = ∑ i, d i *
          mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
            (A_C.map (Rat.castHom ℝ)) i j := by
            apply Finset.sum_subset (Finset.subset_univ B)
            intro i _ hi
            rw [hdOutside i hi, zero_mul]
      _ = 0 := congrFun hdRows j
  apply sub_eq_zero.mp
  funext i
  change d i = 0
  by_cases hi : i ∈ B
  · exact hdOnSupport ⟨i, hi⟩
  · exact hdOutside i hi

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: injectivity of the
real support system descends to its rational form. -/
private lemma independentSupportRationalSystem_injective
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (B : Finset (Fin m))
    (hB : LinearIndependent ℝ
      (fun i : {i // i ∈ B} ↦
        mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
          (A_C.map (Rat.castHom ℝ)) i.1)) :
    Function.Injective (independentSupportRationalSystemMatrix A_I A_C B).mulVec := by
  intro x y hxy
  have hxyReal :
      ((independentSupportRationalSystemMatrix A_I A_C B).map
        (Rat.castHom ℝ)) *ᵥ (fun i ↦ (x i : ℝ)) =
      ((independentSupportRationalSystemMatrix A_I A_C B).map
        (Rat.castHom ℝ)) *ᵥ (fun i ↦ (y i : ℝ)) := by
    -- Cast the equality of rational system values coordinatewise.
    ext k
    calc
      (((independentSupportRationalSystemMatrix A_I A_C B).map
          (Rat.castHom ℝ)) *ᵥ (fun i ↦ (x i : ℝ))) k =
          ((independentSupportRationalSystemMatrix A_I A_C B *ᵥ x) k : ℝ) :=
            (RingHom.map_mulVec (Rat.castHom ℝ)
              (independentSupportRationalSystemMatrix A_I A_C B) x k).symm
      _ = ((independentSupportRationalSystemMatrix A_I A_C B *ᵥ y) k : ℝ) := by
            rw [hxy]
      _ = (((independentSupportRationalSystemMatrix A_I A_C B).map
          (Rat.castHom ℝ)) *ᵥ (fun i ↦ (y i : ℝ))) k :=
            RingHom.map_mulVec (Rat.castHom ℝ)
              (independentSupportRationalSystemMatrix A_I A_C B) y k
  have hcast := independentSupportRationalSystem_realInjective A_I A_C B hB hxyReal
  funext i
  exact Rat.cast_injective (congrFun hcast i)

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the matrix of a
rational linear map between coordinate spaces in their standard bases. -/
private noncomputable def standardBasisLinearMapMatrix
    (f : (Fin r → ℚ) →ₗ[ℚ] Fin s → ℚ) : Matrix (Fin s) (Fin r) ℚ :=
  LinearMap.toMatrix (Pi.basisFun ℚ (Fin r)) (Pi.basisFun ℚ (Fin s)) f

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: standard-basis
matrices turn composition of rational linear maps into matrix multiplication. -/
private lemma standardBasisLinearMapMatrix_comp
    (f : (Fin r → ℚ) →ₗ[ℚ] Fin s → ℚ)
    (g : (Fin t → ℚ) →ₗ[ℚ] Fin r → ℚ) :
    standardBasisLinearMapMatrix (f.comp g) =
      standardBasisLinearMapMatrix f * standardBasisLinearMapMatrix g := by
  -- Apply the basis-aware composition theorem to the three standard coordinate bases.
  unfold standardBasisLinearMapMatrix
  exact LinearMap.toMatrix_comp
    (Pi.basisFun ℚ (Fin t)) (Pi.basisFun ℚ (Fin r)) (Pi.basisFun ℚ (Fin s)) f g

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: multiplying the
standard-basis matrix by a coordinate vector evaluates the represented linear map. -/
private lemma standardBasisLinearMapMatrix_mulVec
    (f : (Fin r → ℚ) →ₗ[ℚ] Fin s → ℚ)
    (v : Fin r → ℚ) :
    standardBasisLinearMapMatrix f *ᵥ v = f v := by
  -- Standard-basis coordinates are definitionally the original coordinate functions.
  simpa only [standardBasisLinearMapMatrix, Pi.basisFun_repr] using
    LinearMap.toMatrix_mulVec_repr
      (Pi.basisFun ℚ (Fin r)) (Pi.basisFun ℚ (Fin s)) f v

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the
standard-basis matrix of matrix-vector multiplication is the original matrix. -/
private lemma standardBasisLinearMapMatrix_mulVecLin
    (C : Matrix (Fin r) (Fin s) ℚ) :
    standardBasisLinearMapMatrix C.mulVecLin = C := by
  -- Evaluate both matrices on standard basis vectors, where multiplication selects one column.
  ext i j
  simp [standardBasisLinearMapMatrix, LinearMap.toMatrix_apply]

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the identity
linear map has the identity matrix in the standard basis. -/
private lemma standardBasisLinearMapMatrix_id :
    standardBasisLinearMapMatrix
        (LinearMap.id : (Fin s → ℚ) →ₗ[ℚ] Fin s → ℚ) = 1 := by
  -- Invoke the general identity-matrix theorem at the standard coordinate basis.
  exact LinearMap.toMatrix_id (Pi.basisFun ℚ (Fin s))

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: an injective
rational linear system with a real solution has the corresponding rational solution. -/
private lemma existsRationalSolutionOfInjectiveSystem
    (C : Matrix (Fin r) (Fin s) ℚ)
    (d : Fin r → ℚ)
    (u : Fin s → ℝ)
    (hreal : (C.map (Rat.castHom ℝ)) *ᵥ u = fun i ↦ (d i : ℝ))
    (hCinj : Function.Injective C.mulVec) :
    ∃ q : Fin s → ℚ, C *ᵥ q = d ∧ ∀ i, (q i : ℝ) = u i := by
  classical
  have hker : LinearMap.ker C.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr hCinj
  let L : Matrix (Fin s) (Fin r) ℚ :=
    standardBasisLinearMapMatrix C.mulVecLin.leftInverse
  let q : Fin s → ℚ := L *ᵥ d
  have hLC : L * C = 1 := by
    calc
      L * C = standardBasisLinearMapMatrix C.mulVecLin.leftInverse *
          standardBasisLinearMapMatrix C.mulVecLin := by
            simp only [L, standardBasisLinearMapMatrix_mulVecLin]
      _ = standardBasisLinearMapMatrix
          (C.mulVecLin.leftInverse.comp C.mulVecLin) :=
        (standardBasisLinearMapMatrix_comp _ _).symm
      _ = standardBasisLinearMapMatrix
          (LinearMap.id : (Fin s → ℚ) →ₗ[ℚ] Fin s → ℚ) :=
        congrArg standardBasisLinearMapMatrix
          (LinearMap.leftInverse_comp_of_inj hker)
      _ = 1 := standardBasisLinearMapMatrix_id
  have hqCast : (fun i ↦ (q i : ℝ)) = u := by
    funext i
    calc
      (q i : ℝ) = (((L *ᵥ d) i : ℚ) : ℝ) := by rfl
      _ = ((L.map (Rat.castHom ℝ)) *ᵥ (fun k ↦ (d k : ℝ))) i :=
        RingHom.map_mulVec (Rat.castHom ℝ) L d i
      _ = ((L.map (Rat.castHom ℝ)) *ᵥ
          ((C.map (Rat.castHom ℝ)) *ᵥ u)) i := by rw [hreal]
      _ = (((L.map (Rat.castHom ℝ)) * (C.map (Rat.castHom ℝ))) *ᵥ u) i := by
        rw [Matrix.mulVec_mulVec]
      _ = ((((L * C).map (Rat.castHom ℝ))) *ᵥ u) i := by
        rw [Matrix.map_mul]
      _ = u i := by simp only [hLC, Matrix.map_one, Matrix.one_mulVec, map_zero, map_one]
  have hqSystem : C *ᵥ q = d := by
    funext k
    apply (Rat.cast_injective : Function.Injective (fun a : ℚ ↦ (a : ℝ)))
    calc
      (((C *ᵥ q) k : ℚ) : ℝ) =
          ((C.map (Rat.castHom ℝ)) *ᵥ (fun i ↦ (q i : ℝ))) k :=
        RingHom.map_mulVec (Rat.castHom ℝ) C q k
      _ = ((C.map (Rat.castHom ℝ)) *ᵥ u) k := by rw [hqCast]
      _ = (d k : ℝ) := congrFun hreal k
  exact ⟨q, hqSystem, congrFun hqCast⟩

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: an
independent-support mixed multiplier over rational data has rational coordinates. -/
private lemma existsRationalRowMultiplierOfIndependentSupport
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (b : Fin m → ℚ)
    (u : Fin m → ℝ)
    (hu : IsMixedGomoryFractionalCutMultiplier (A_I.map (Rat.castHom ℝ))
      (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) u)
    (huIndep : RowMultiplierHasIndependentSupportRows
      (mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
        (A_C.map (Rat.castHom ℝ))) u) :
    ∃ q : Fin m → ℚ, ∀ i, (q i : ℝ) = u i := by
  classical
  choose z hz using hu.1
  let B : Finset (Fin m) := row_multiplier_support u
  have huAI :
      u ᵥ* (A_I.map (Rat.castHom ℝ)) = fun j ↦ (z j : ℝ) := by
    funext j
    exact hz j
  have huSupport : ∀ i : Fin m, i ∉ B → u i = 0 := by
    intro i hi
    by_contra hui
    exact hi ((mem_row_multiplier_support_iff u i).2 hui)
  have hreal :
      ((independentSupportRationalSystemMatrix A_I A_C B).map
        (Rat.castHom ℝ)) *ᵥ u =
          fun k ↦ (independentSupportRationalSystemRhs z k : ℝ) :=
    independentSupportRationalSystem_realSolution
      A_I A_C B z u huAI hu.2.1 huSupport
  have hB : LinearIndependent ℝ
      (fun i : {i // i ∈ B} ↦
        mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
          (A_C.map (Rat.castHom ℝ)) i.1) := by
    simpa [B] using huIndep
  obtain ⟨q, _, hqu⟩ := existsRationalSolutionOfInjectiveSystem
    (independentSupportRationalSystemMatrix A_I A_C B)
    (independentSupportRationalSystemRhs z) u hreal
    (independentSupportRationalSystem_injective A_I A_C B hB)
  exact ⟨q, hqu⟩

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the matrix of the
canonical rational left inverse for a fixed support system. -/
private noncomputable def independentSupportLeftInverseMatrix
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (B : Finset (Fin m)) : Matrix (Fin m) (Fin ((nI + nC) + m)) ℚ :=
  standardBasisLinearMapMatrix
    (independentSupportRationalSystemMatrix A_I A_C B).mulVecLin.leftInverse

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the product of the
fixed-support inverse denominators is a common positive denominator. -/
private noncomputable def independentSupportCommonDenominator
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ) : ℕ :=
  ∏ B : Finset (Fin m), (independentSupportLeftInverseMatrix A_I A_C B).den

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the common support
denominator is strictly positive. -/
private lemma independentSupportCommonDenominator_pos
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ) :
    0 < independentSupportCommonDenominator A_I A_C := by
  -- Every rational matrix denominator is nonzero, hence positive.
  unfold independentSupportCommonDenominator
  apply Finset.prod_pos
  intro B _
  exact Nat.pos_of_ne_zero (independentSupportLeftInverseMatrix A_I A_C B).den_ne_zero

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: every fixed-support
inverse denominator divides the common denominator. -/
private lemma independentSupportDenominator_dvd_common
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (B : Finset (Fin m)) :
    (independentSupportLeftInverseMatrix A_I A_C B).den ∣
      independentSupportCommonDenominator A_I A_C := by
  -- The chosen factor occurs in the product over every row support.
  unfold independentSupportCommonDenominator
  exact Finset.dvd_prod_of_mem
    (fun C : Finset (Fin m) ↦ (independentSupportLeftInverseMatrix A_I A_C C).den)
    (Finset.mem_univ B)

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: applying a rational
linear map to an integral vector has an explicit numerator over its matrix denominator. -/
private lemma linearMap_apply_integral_eq_num_div_den
    (f : (Fin r → ℚ) →ₗ[ℚ] Fin s → ℚ)
    (v : Fin r → ℤ)
    (i : Fin s) :
    f (fun k ↦ (v k : ℚ)) i =
      ((∑ k, (standardBasisLinearMapMatrix f).num i k * v k : ℤ) : ℚ) /
        (standardBasisLinearMapMatrix f).den := by
  -- Expand in the standard basis and clear the common matrix denominator termwise.
  rw [← standardBasisLinearMapMatrix_mulVec]
  unfold Matrix.mulVec dotProduct
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [Int.cast_mul]
  change standardBasisLinearMapMatrix f i k * (v k : ℚ) =
    ((standardBasisLinearMapMatrix f).num i k : ℚ) * (v k : ℚ) /
      (standardBasisLinearMapMatrix f).den
  rw [← Matrix.num_div_den (standardBasisLinearMapMatrix f) i k]
  ring

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: all
independent-support row multipliers over fixed rational matrices lie in one rational lattice. -/
private lemma existsCommonDenominatorForIndependentRowMultipliers
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ) :
    ∃ D : ℕ, 0 < D ∧
      ∀ (b : Fin m → ℚ) (u : Fin m → ℝ),
        IsMixedGomoryFractionalCutMultiplier (A_I.map (Rat.castHom ℝ))
            (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) u →
          RowMultiplierHasIndependentSupportRows
              (mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
                (A_C.map (Rat.castHom ℝ))) u →
            ∃ z : Fin m → ℤ, ∀ i, u i = (z i : ℝ) / D := by
  classical
  let D := independentSupportCommonDenominator A_I A_C
  have hDpos : 0 < D := independentSupportCommonDenominator_pos A_I A_C
  refine ⟨D, hDpos, ?_⟩
  intro b u hu huIndep
  choose p hp using hu.1
  let B : Finset (Fin m) := row_multiplier_support u
  obtain ⟨q, hqu⟩ :=
    existsRationalRowMultiplierOfIndependentSupport A_I A_C b u hu huIndep
  have huAI :
      u ᵥ* (A_I.map (Rat.castHom ℝ)) = fun j ↦ (p j : ℝ) := by
    funext j
    exact hp j
  have huSupport : ∀ i : Fin m, i ∉ B → u i = 0 := by
    intro i hi
    by_contra hui
    exact hi ((mem_row_multiplier_support_iff u i).2 hui)
  have hreal :
      ((independentSupportRationalSystemMatrix A_I A_C B).map
        (Rat.castHom ℝ)) *ᵥ u =
          fun k ↦ (independentSupportRationalSystemRhs p k : ℝ) :=
    independentSupportRationalSystem_realSolution
      A_I A_C B p u huAI hu.2.1 huSupport
  have hqSystem :
      independentSupportRationalSystemMatrix A_I A_C B *ᵥ q =
        independentSupportRationalSystemRhs p := by
    -- Cast both sides; the rational multiplier and `u` are coordinatewise equal over `ℝ`.
    ext k
    apply (Rat.cast_injective : Function.Injective (fun a : ℚ ↦ (a : ℝ)))
    calc
      ((independentSupportRationalSystemMatrix A_I A_C B *ᵥ q) k : ℝ) =
          (((independentSupportRationalSystemMatrix A_I A_C B).map
            (Rat.castHom ℝ)) *ᵥ (fun i ↦ (q i : ℝ))) k :=
              RingHom.map_mulVec (Rat.castHom ℝ)
                (independentSupportRationalSystemMatrix A_I A_C B) q k
      _ = (((independentSupportRationalSystemMatrix A_I A_C B).map
            (Rat.castHom ℝ)) *ᵥ u) k := by
              congr 2
              funext i
              exact hqu i
      _ = (independentSupportRationalSystemRhs p k : ℝ) := congrFun hreal k
  have hB : LinearIndependent ℝ
      (fun i : {i // i ∈ B} ↦
        mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
          (A_C.map (Rat.castHom ℝ)) i.1) := by
    simpa [B] using huIndep
  have hCinj : Function.Injective
      (independentSupportRationalSystemMatrix A_I A_C B).mulVec :=
    independentSupportRationalSystem_injective A_I A_C B hB
  have hker : LinearMap.ker
      (independentSupportRationalSystemMatrix A_I A_C B).mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr hCinj
  have hcanonical :
      (independentSupportRationalSystemMatrix A_I A_C B).mulVecLin.leftInverse
          (independentSupportRationalSystemRhs p) = q := by
    -- The canonical left inverse recovers the unique rational solution.
    rw [← hqSystem]
    exact LinearMap.leftInverse_apply_of_inj hker q
  let L := independentSupportLeftInverseMatrix A_I A_C B
  let numer : Fin m → ℤ := fun i ↦
    ∑ k, L.num i k * independentSupportIntegralSystemRhs p k
  have hqDen : ∀ i, q i = (numer i : ℚ) / L.den := by
    intro i
    calc
      q i =
          (independentSupportRationalSystemMatrix A_I A_C B).mulVecLin.leftInverse
            (independentSupportRationalSystemRhs p) i := congrFun hcanonical.symm i
      _ = (numer i : ℚ) / L.den := by
            simpa [L, numer, independentSupportRationalSystemRhs] using
              linearMap_apply_integral_eq_num_div_den
                (independentSupportRationalSystemMatrix A_I A_C B).mulVecLin.leftInverse
                (independentSupportIntegralSystemRhs p) i
  have hLdvd : L.den ∣ D := by
    simpa [L, D] using independentSupportDenominator_dvd_common A_I A_C B
  obtain ⟨K, hK⟩ := hLdvd
  have hLpos : 0 < L.den := Nat.pos_of_ne_zero L.den_ne_zero
  have hKpos : 0 < K := by
    have hprod : 0 < L.den * K := by simpa [hK] using hDpos
    have hKne : K ≠ 0 := by
      intro hzero
      subst K
      simp at hprod
    exact Nat.pos_of_ne_zero hKne
  refine ⟨fun i ↦ numer i * K, ?_⟩
  intro i
  have hqGlobal : q i = ((numer i * K : ℤ) : ℚ) / D := by
    rw [hqDen i, hK]
    push_cast
    field_simp [Nat.ne_of_gt hLpos, Nat.ne_of_gt hKpos]
  calc
    u i = (q i : ℝ) := (hqu i).symm
    _ = (((numer i * K : ℤ) : ℚ) / (D : ℚ) : ℚ) := by rw [hqGlobal]
    _ = ((numer i * K : ℤ) : ℝ) / D := by
          change (Rat.castHom ℝ)
            (((numer i * K : ℤ) : ℚ) / (D : ℚ)) =
              ((numer i * K : ℤ) : ℝ) / (D : ℝ)
          exact map_div₀ (Rat.castHom ℝ) _ _

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the denominator
of a quotient of rationals divides the first denominator times the absolute second numerator. -/
private lemma ratDenDiv_dvd
    (q r : ℚ) :
    (q / r).den ∣ q.den * r.num.natAbs := by
  -- View division as multiplication by an inverse and identify the inverse denominator.
  by_cases hr : r = 0
  · subst r
    simp
  · rw [div_eq_mul_inv]
    simpa only [Rat.den_inv_of_ne_zero hr] using Rat.mul_den_dvd q r⁻¹

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the absolute
numerator of a rational in `[0,1)` is strictly smaller than its denominator. -/
private lemma ratNumNatAbs_ltDen
    (q : ℚ)
    (hq_nonneg : 0 ≤ q)
    (hq_lt_one : q < 1) :
    q.num.natAbs < q.den := by
  -- Compare numerator and denominator after clearing the positive denominator.
  have hnum_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq_nonneg
  have hquot : (q.num : ℚ) / q.den < 1 := by
    simpa [Rat.num_div_den] using hq_lt_one
  have hnum_lt : q.num < (q.den : ℤ) := by
    have hden_pos : (0 : ℚ) < q.den := by positivity
    have hrat : (q.num : ℚ) < q.den := (div_lt_one hden_pos).mp hquot
    exact_mod_cast hrat
  exact_mod_cast
    Int.natAbs_lt_natAbs_of_nonneg_of_lt hnum_nonneg hnum_lt

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a nonnegative
rational whose denominator divides `N` is a natural numerator over `N`. -/
private lemma existsNatDivEqOfRatDenDvd
    (q : ℚ)
    (N : ℕ)
    (hN : 0 < N)
    (hq_nonneg : 0 ≤ q)
    (hden : q.den ∣ N) :
    ∃ a : ℕ, q = (a : ℚ) / N := by
  obtain ⟨K, hK⟩ := hden
  have hnum_nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq_nonneg
  have hKpos : 0 < K := by
    by_contra hKnotPos
    have hKzero : K = 0 := Nat.eq_zero_of_not_pos hKnotPos
    rw [hKzero, Nat.mul_zero] at hK
    omega
  let a : ℕ := q.num.toNat * K
  refine ⟨a, ?_⟩
  rw [← q.num_div_den, hK]
  simp only [a]
  push_cast
  field_simp [q.den_ne_zero, Nat.ne_of_gt hKpos]
  exact_mod_cast (Int.toNat_of_nonneg hnum_nonneg).symm

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the rational
version of the normalized coefficient uses the same two sign parts and fractional denominator. -/
private noncomputable def rationalNormalizedMixedCutCoefficient
    (b : Fin m → ℚ)
    (q : Fin m → ℚ) : Fin m → ℚ :=
  fun i ↦ max (q i) 0 / Int.fract (q ⬝ᵥ b) +
    max (-q i) 0 / (1 - Int.fract (q ⬝ᵥ b))

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: casting a
rational normalized coefficient agrees with the real coefficient of the cast multiplier. -/
private lemma rationalNormalizedMixedCutCoefficient_cast
    (b : Fin m → ℚ)
    (q : Fin m → ℚ)
    (i : Fin m) :
    (rationalNormalizedMixedCutCoefficient b q i : ℝ) =
      normalizedMixedCutCoefficient (fun j ↦ (b j : ℝ))
        (fun j ↦ (q j : ℝ)) i := by
  -- Cast the rational dot product and its fractional part before the two divisions.
  have hdot : ((q ⬝ᵥ b : ℚ) : ℝ) =
      (fun j ↦ (q j : ℝ)) ⬝ᵥ (fun j ↦ (b j : ℝ)) := by
    exact RingHom.map_dotProduct (Rat.castHom ℝ) q b
  unfold rationalNormalizedMixedCutCoefficient normalizedMixedCutCoefficient
  rw [Rat.cast_add, Rat.cast_div, Rat.cast_div, Rat.cast_max, Rat.cast_max,
    Rat.cast_zero, Rat.cast_neg, Rat.cast_sub, Rat.cast_one, Rat.cast_fract, hdot]
  rfl

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: positivity of the
fractional part makes the rational normalized coefficient nonnegative. -/
private lemma rationalNormalizedMixedCutCoefficient_nonneg
    (b : Fin m → ℚ)
    (q : Fin m → ℚ)
    (hfract : Int.fract (q ⬝ᵥ b) ≠ 0) :
    0 ≤ rationalNormalizedMixedCutCoefficient b q := by
  have hf_pos : 0 < Int.fract (q ⬝ᵥ b) :=
    lt_of_le_of_ne (Int.fract_nonneg _) hfract.symm
  have hf_lt : Int.fract (q ⬝ᵥ b) < 1 := Int.fract_lt_one _
  -- Each summand has a nonnegative numerator and a positive denominator.
  intro i
  unfold rationalNormalizedMixedCutCoefficient
  exact add_nonneg
    (div_nonneg (le_max_right _ _) hf_pos.le)
    (div_nonneg (le_max_right _ _) (sub_nonneg.mpr hf_lt.le))

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: bounds on the
multiplier and fractional-part denominators bound every normalized coefficient denominator. -/
private lemma rationalNormalizedMixedCutCoefficient_den_le
    (b : Fin m → ℚ)
    (q : Fin m → ℚ)
    (D E : ℕ)
    (hD : 0 < D)
    (hqden : ∀ i, (q i).den ≤ D)
    (htden : (q ⬝ᵥ b).den ≤ E)
    (hfract : Int.fract (q ⬝ᵥ b) ≠ 0)
    (i : Fin m) :
    (rationalNormalizedMixedCutCoefficient b q i).den ≤ (D * E) ^ 2 := by
  let f : ℚ := Int.fract (q ⬝ᵥ b)
  let qpos : ℚ := max (q i) 0
  let qneg : ℚ := max (-q i) 0
  have hf_pos : 0 < f := lt_of_le_of_ne (Int.fract_nonneg _) hfract.symm
  have hf_lt : f < 1 := Int.fract_lt_one _
  have hfden : f.den ≤ E := by
    simpa [f, Rat.den_intFract] using htden
  have hfnum : f.num.natAbs ≤ E :=
    (ratNumNatAbs_ltDen f hf_pos.le hf_lt).le.trans hfden
  have honef_pos : 0 < 1 - f := sub_pos.mpr hf_lt
  have honef_lt : 1 - f < 1 := by linarith
  have honefden : (1 - f).den ≤ E := by
    simpa using hfden
  have honefnum : (1 - f).num.natAbs ≤ E :=
    (ratNumNatAbs_ltDen (1 - f) honef_pos.le honef_lt).le.trans honefden
  have hqposden : qpos.den ≤ D := by
    by_cases hqi : 0 ≤ q i
    · simpa [qpos, max_eq_left hqi] using hqden i
    · have hqiNonpos : q i ≤ 0 := le_of_lt (lt_of_not_ge hqi)
      simp [qpos, max_eq_right hqiNonpos, Nat.succ_le_iff.mpr hD]
  have hqnegden : qneg.den ≤ D := by
    by_cases hqi : 0 ≤ -q i
    · simpa [qneg, max_eq_left hqi] using hqden i
    · have hnegqiNonpos : -q i ≤ 0 := le_of_lt (lt_of_not_ge hqi)
      simp [qneg, max_eq_right hnegqiNonpos, Nat.succ_le_iff.mpr hD]
  have hposDen : (qpos / f).den ≤ D * E := by
    have hnum_pos : 0 < f.num.natAbs :=
      Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hfract)
    exact (Nat.le_of_dvd (Nat.mul_pos qpos.den_pos hnum_pos)
      (ratDenDiv_dvd qpos f)).trans
        (Nat.mul_le_mul hqposden hfnum)
  have hnegDen : (qneg / (1 - f)).den ≤ D * E := by
    have honef_ne : 1 - f ≠ 0 := ne_of_gt honef_pos
    have hnum_pos : 0 < (1 - f).num.natAbs :=
      Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr honef_ne)
    exact (Nat.le_of_dvd (Nat.mul_pos qneg.den_pos hnum_pos)
      (ratDenDiv_dvd qneg (1 - f))).trans
        (Nat.mul_le_mul hqnegden honefnum)
  have haddDvd : (qpos / f + qneg / (1 - f)).den ∣
      (qpos / f).den * (qneg / (1 - f)).den :=
    Rat.add_den_dvd _ _
  have haddPos : 0 < (qpos / f).den * (qneg / (1 - f)).den :=
    Nat.mul_pos (qpos / f).den_pos (qneg / (1 - f)).den_pos
  have haddLe := Nat.le_of_dvd haddPos haddDvd
  simpa [rationalNormalizedMixedCutCoefficient, f, qpos, qneg, pow_two] using
    haddLe.trans (Nat.mul_le_mul hposDen hnegDen)

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the rational
dot product with `b` is represented as a one-row rational linear map. -/
private noncomputable def rationalDotProductLinearMap
    (b : Fin m → ℚ) : (Fin m → ℚ) →ₗ[ℚ] Fin 1 → ℚ :=
  Matrix.mulVecLin ((fun (_ : Fin 1) (i : Fin m) ↦ b i) : Matrix (Fin 1) (Fin m) ℚ)

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: applying the
dot-product map to an integral vector is the expected dot product. -/
private lemma rationalDotProductLinearMap_apply
    (b : Fin m → ℚ)
    (z : Fin m → ℤ) :
    rationalDotProductLinearMap b (fun i ↦ (z i : ℚ)) 0 =
      (fun i ↦ (z i : ℚ)) ⬝ᵥ b := by
  -- The one matrix row is `b`; only commutativity changes the displayed order.
  unfold rationalDotProductLinearMap
  rw [Matrix.mulVecLin_apply]
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a multiplier on
the `D`-lattice has a dot product with rational `b` on one fixed denominator. -/
private lemma rationalDotProduct_eq_int_div_fixedDenominator
    (b : Fin m → ℚ)
    (D : ℕ)
    (hD : 0 < D)
    (z : Fin m → ℤ) :
    ∃ a : ℤ,
      (fun i ↦ (z i : ℚ) / D) ⬝ᵥ b =
        (a : ℚ) /
          ((standardBasisLinearMapMatrix (rationalDotProductLinearMap b)).den * D) := by
  let L := rationalDotProductLinearMap b
  let a : ℤ := ∑ i, (standardBasisLinearMapMatrix L).num 0 i * z i
  have hL :
      L (fun i ↦ (z i : ℚ)) 0 =
        (a : ℚ) / (standardBasisLinearMapMatrix L).den := by
    simpa [a] using linearMap_apply_integral_eq_num_div_den L z 0
  refine ⟨a, ?_⟩
  calc
    (fun i ↦ (z i : ℚ) / D) ⬝ᵥ b =
        ((fun i ↦ (z i : ℚ)) ⬝ᵥ b) / D := by
          unfold dotProduct
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = L (fun i ↦ (z i : ℚ)) 0 / D := by
          rw [rationalDotProductLinearMap_apply]
    _ = ((a : ℚ) / (standardBasisLinearMapMatrix L).den) / D := by rw [hL]
    _ = (a : ℚ) / ((standardBasisLinearMapMatrix L).den * D) := by
          field_simp [Nat.ne_of_gt hD, (standardBasisLinearMapMatrix L).den_ne_zero]

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: an explicit
integer-over-natural presentation forces the reduced rational denominator to divide it. -/
private lemma ratDen_dvd_of_eq_int_div_nat
    (q : ℚ)
    (a : ℤ)
    (E : ℕ)
    (hq : q = (a : ℚ) / E) :
    q.den ∣ E := by
  have hdiv : (a : ℚ) / E = Rat.divInt a E :=
    Rat.intCast_div_eq_divInt a E
  rw [hq, hdiv]
  exact_mod_cast Rat.den_dvd a E

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: all normalized
coefficients of independent-support cuts lie in one nonnegative natural-number lattice. -/
private lemma existsCommonDenominatorForNormalizedMixedCutCoefficients
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (b : Fin m → ℚ) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (u : Fin m → ℝ),
        IsMixedGomoryFractionalCutMultiplier (A_I.map (Rat.castHom ℝ))
            (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) u →
          RowMultiplierHasIndependentSupportRows
              (mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
                (A_C.map (Rat.castHom ℝ))) u →
            ∃ a : Fin m → ℕ, ∀ i,
              normalizedMixedCutCoefficient (fun j ↦ (b j : ℝ)) u i =
                (a i : ℝ) / N := by
  classical
  obtain ⟨D, hD, hDgrid⟩ :=
    existsCommonDenominatorForIndependentRowMultipliers A_I A_C
  let H : ℕ := (standardBasisLinearMapMatrix (rationalDotProductLinearMap b)).den
  let E : ℕ := H * D
  let K : ℕ := (D * E) ^ 2
  let N : ℕ := Nat.factorial K
  have hH : 0 < H := by
    exact Nat.pos_of_ne_zero
      (standardBasisLinearMapMatrix (rationalDotProductLinearMap b)).den_ne_zero
  have hE : 0 < E := Nat.mul_pos hH hD
  have hK : 0 < K := pow_pos (Nat.mul_pos hD hE) 2
  have hN : 0 < N := Nat.factorial_pos K
  refine ⟨N, hN, ?_⟩
  intro u hu huIndep
  obtain ⟨z, hzu⟩ := hDgrid b u hu huIndep
  let q : Fin m → ℚ := fun i ↦ (z i : ℚ) / D
  have hqu : (fun i ↦ (q i : ℝ)) = u := by
    funext i
    simpa [q] using (hzu i).symm
  have hdotCast : ((q ⬝ᵥ b : ℚ) : ℝ) =
      u ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
    calc
      ((q ⬝ᵥ b : ℚ) : ℝ) =
          (fun i ↦ (q i : ℝ)) ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
            exact RingHom.map_dotProduct (Rat.castHom ℝ) q b
      _ = u ⬝ᵥ (fun i ↦ (b i : ℝ)) := by rw [hqu]
  have hfract : Int.fract (q ⬝ᵥ b) ≠ 0 := by
    intro hf
    have hfractReal :
        Int.fract (u ⬝ᵥ (fun i ↦ (b i : ℝ))) ≠ 0 := by
      apply (Int.fract_ne_zero_iff).2
      simpa [Set.mem_range, eq_comm] using hu.2.2
    apply hfractReal
    rw [← hdotCast, ← Rat.cast_fract, hf]
    norm_num
  have hqden : ∀ i, (q i).den ≤ D := by
    intro i
    have hqi : q i = (z i : ℚ) / D := rfl
    have hdvd : (q i).den ∣ D :=
      ratDen_dvd_of_eq_int_div_nat (q i) (z i) D hqi
    exact Nat.le_of_dvd hD hdvd
  obtain ⟨dotNum, hdotNum⟩ :=
    rationalDotProduct_eq_int_div_fixedDenominator b D hD z
  have hdotNumQ : q ⬝ᵥ b = (dotNum : ℚ) / E := by
    simpa [q, E, H] using hdotNum
  have hdotden : (q ⬝ᵥ b).den ≤ E :=
    Nat.le_of_dvd hE (ratDen_dvd_of_eq_int_div_nat _ dotNum E hdotNumQ)
  have hcoeffDen : ∀ i,
      (rationalNormalizedMixedCutCoefficient b q i).den ≤ K := by
    intro i
    simpa [K] using rationalNormalizedMixedCutCoefficient_den_le
      b q D E hD hqden hdotden hfract i
  have hcoeffNonneg : 0 ≤ rationalNormalizedMixedCutCoefficient b q :=
    rationalNormalizedMixedCutCoefficient_nonneg b q hfract
  have hcoeffDvd : ∀ i,
      (rationalNormalizedMixedCutCoefficient b q i).den ∣ N := by
    intro i
    exact Nat.dvd_factorial
      (rationalNormalizedMixedCutCoefficient b q i).den_pos (hcoeffDen i)
  choose a ha using fun i ↦ existsNatDivEqOfRatDenDvd
    (rationalNormalizedMixedCutCoefficient b q i) N hN (hcoeffNonneg i) (hcoeffDvd i)
  refine ⟨a, ?_⟩
  intro i
  calc
    normalizedMixedCutCoefficient (fun j ↦ (b j : ℝ)) u i =
        normalizedMixedCutCoefficient (fun j ↦ (b j : ℝ))
          (fun j ↦ (q j : ℝ)) i := by rw [hqu]
    _ = (rationalNormalizedMixedCutCoefficient b q i : ℝ) :=
      (rationalNormalizedMixedCutCoefficient_cast b q i).symm
    _ = (((a i : ℕ) : ℚ) / (N : ℚ) : ℚ) := by rw [ha i]
    _ = (a i : ℝ) / N := by
      change (Rat.castHom ℝ) (((a i : ℕ) : ℚ) / (N : ℚ)) =
        (a i : ℝ) / (N : ℝ)
      rw [map_div₀]
      norm_cast

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: finitely many
independent-support cuts have rational coefficients and lie componentwise below every such cut. -/
private lemma existsFiniteRationalMinimalMixedCutCoefficients
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (b : Fin m → ℚ) :
    ∃ (t : ℕ) (v : Fin t → Fin m → ℝ) (c : Fin t → Fin m → ℚ),
      (∀ k,
        IsMixedGomoryFractionalCutMultiplier (A_I.map (Rat.castHom ℝ))
            (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) (v k) ∧
          RowMultiplierHasIndependentSupportRows
            (mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
              (A_C.map (Rat.castHom ℝ))) (v k)) ∧
      (∀ k i, (c k i : ℝ) =
        normalizedMixedCutCoefficient (fun j ↦ (b j : ℝ)) (v k) i) ∧
      ∀ (u : Fin m → ℝ),
        IsMixedGomoryFractionalCutMultiplier (A_I.map (Rat.castHom ℝ))
            (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) u →
          RowMultiplierHasIndependentSupportRows
              (mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
                (A_C.map (Rat.castHom ℝ))) u →
            ∃ k, ∀ i, (c k i : ℝ) ≤
              normalizedMixedCutCoefficient (fun j ↦ (b j : ℝ)) u i := by
  classical
  obtain ⟨N, hN, hencode⟩ :=
    existsCommonDenominatorForNormalizedMixedCutCoefficients A_I A_C b
  let Encoded : Set (Fin m → ℕ) :=
    {a | ∃ u : Fin m → ℝ,
      IsMixedGomoryFractionalCutMultiplier (A_I.map (Rat.castHom ℝ))
          (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) u ∧
        RowMultiplierHasIndependentSupportRows
            (mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
              (A_C.map (Rat.castHom ℝ))) u ∧
          ∀ i, normalizedMixedCutCoefficient (fun j ↦ (b j : ℝ)) u i =
            (a i : ℝ) / N}
  have hpwo : Encoded.IsPWO := Set.isPWO_of_wellQuasiOrderedLE Encoded
  have hminimalFinite : {a | Minimal (fun x ↦ x ∈ Encoded) a}.Finite :=
    (setOf_minimal_antichain (fun x ↦ x ∈ Encoded)).finite_of_partiallyWellOrderedOn
      (hpwo.mono (setOf_minimal_subset _))
  obtain ⟨t, a, _, haRange⟩ := hminimalFinite.fin_param
  have haEncoded : ∀ k, a k ∈ Encoded := by
    intro k
    have hkRange : a k ∈ Set.range a := ⟨k, rfl⟩
    have hkMinimal : Minimal (fun x ↦ x ∈ Encoded) (a k) := by
      rw [haRange] at hkRange
      exact hkRange
    exact hkMinimal.1
  choose v hvMixed hvIndep hvCoeff using haEncoded
  let c : Fin t → Fin m → ℚ := fun k i ↦ (a k i : ℚ) / N
  refine ⟨t, v, c, ?_, ?_, ?_⟩
  · intro k
    exact ⟨hvMixed k, hvIndep k⟩
  · intro k i
    calc
      (c k i : ℝ) = (a k i : ℝ) / N := by
        change (Rat.castHom ℝ) (((a k i : ℕ) : ℚ) / (N : ℚ)) =
          (a k i : ℝ) / (N : ℝ)
        rw [map_div₀]
        norm_cast
      _ = normalizedMixedCutCoefficient (fun j ↦ (b j : ℝ)) (v k) i :=
        (hvCoeff k i).symm
  · intro u hu huIndep
    obtain ⟨q, hq⟩ := hencode u hu huIndep
    have hqEncoded : q ∈ Encoded := ⟨u, hu, huIndep, hq⟩
    obtain ⟨qmin, hqmin_le, hqmin⟩ := hpwo.exists_le_minimal hqEncoded
    have hqminRange : qmin ∈ Set.range a := by
      rw [haRange]
      exact hqmin
    rcases hqminRange with ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    intro i
    have hcoord : a k i ≤ q i := hqmin_le i
    have hcFormula : (c k i : ℝ) = (a k i : ℝ) / N := by
      change (Rat.castHom ℝ) (((a k i : ℕ) : ℚ) / (N : ℚ)) =
        (a k i : ℝ) / (N : ℝ)
      exact map_div₀ (Rat.castHom ℝ) _ _
    have hcoordReal : (a k i : ℝ) ≤ q i := by
      exact_mod_cast hcoord
    rw [hcFormula, hq i]
    exact div_le_div_of_nonneg_right hcoordReal (Nat.cast_nonneg N)

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: a rational row
obtained from a slack coefficient expresses exactly the corresponding unit slack inequality. -/
private lemma rationalMixedCutRow_iff
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (b c : Fin m → ℚ)
    (xy : MixedRealPoint nI nC) :
    (fun j ↦ ((c ᵥ* A_I) j : ℝ)) ⬝ᵥ xy.1 +
          (fun j ↦ ((c ᵥ* A_C) j : ℝ)) ⬝ᵥ xy.2 ≤
        ((c ⬝ᵥ b - 1 : ℚ) : ℝ) ↔
      1 ≤ (fun i ↦ (c i : ℝ)) ⬝ᵥ
        ((fun i ↦ (b i : ℝ)) -
          ((A_I.map (Rat.castHom ℝ)) *ᵥ xy.1 +
            (A_C.map (Rat.castHom ℝ)) *ᵥ xy.2)) := by
  have hAI : (fun j ↦ ((c ᵥ* A_I) j : ℝ)) =
      (fun i ↦ (c i : ℝ)) ᵥ* (A_I.map (Rat.castHom ℝ)) := by
    funext j
    exact RingHom.map_vecMul (Rat.castHom ℝ) A_I c j
  have hAC : (fun j ↦ ((c ᵥ* A_C) j : ℝ)) =
      (fun i ↦ (c i : ℝ)) ᵥ* (A_C.map (Rat.castHom ℝ)) := by
    funext j
    exact RingHom.map_vecMul (Rat.castHom ℝ) A_C c j
  have hb : ((c ⬝ᵥ b : ℚ) : ℝ) =
      (fun i ↦ (c i : ℝ)) ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
    exact RingHom.map_dotProduct (Rat.castHom ℝ) c b
  rw [hAI, hAC, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec,
    dotProduct_sub, dotProduct_add, Rat.cast_sub, Rat.cast_one, hb]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Helper for sorry cleanup existing repo batch3 ch5_sec5_1_2_theorem_5_10: the independent-
support mixed cut system associated to rational data admits a finite rational presentation. -/
private theorem independentSupportCutSystemIsRational
    (A_I : Matrix (Fin m) (Fin nI) ℚ)
    (A_C : Matrix (Fin m) (Fin nC) ℚ)
    (b : Fin m → ℚ) :
    is_rational_mixed_polyhedron
      {xy | xy ∈ real_mixed_polyhedron (A_I.map (Rat.castHom ℝ))
          (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) ∧
        ∀ u : Fin m → ℝ,
          IsMixedGomoryFractionalCutMultiplier (A_I.map (Rat.castHom ℝ))
              (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) u →
            RowMultiplierHasIndependentSupportRows
                (mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
                  (A_C.map (Rat.castHom ℝ))) u →
              1 ≤ mixed_gomory_fractional_cut_value (A_I.map (Rat.castHom ℝ))
                (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) u xy} := by
  classical
  -- Route correction: use the fixed rational lattice and Dickson minimality, avoiding the
  -- unsupported descent from arbitrary cuts to globally undominated multipliers.
  obtain ⟨t, v, c, hv, hc, hdom⟩ :=
    existsFiniteRationalMinimalMixedCutCoefficients A_I A_C b
  let D_I : Matrix (Fin (m + t)) (Fin nI) ℚ := fun r j ↦
    Fin.addCases (fun i ↦ A_I i j) (fun k ↦ (c k ᵥ* A_I) j) r
  let D_C : Matrix (Fin (m + t)) (Fin nC) ℚ := fun r j ↦
    Fin.addCases (fun i ↦ A_C i j) (fun k ↦ (c k ᵥ* A_C) j) r
  let d : Fin (m + t) → ℚ :=
    Fin.addCases b (fun k ↦ c k ⬝ᵥ b - 1)
  suffices hsystem :
      {xy | xy ∈ real_mixed_polyhedron (A_I.map (Rat.castHom ℝ))
          (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) ∧
        ∀ u : Fin m → ℝ,
          IsMixedGomoryFractionalCutMultiplier (A_I.map (Rat.castHom ℝ))
              (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) u →
            RowMultiplierHasIndependentSupportRows
                (mixedConstraintMatrix (A_I.map (Rat.castHom ℝ))
                  (A_C.map (Rat.castHom ℝ))) u →
              1 ≤ mixed_gomory_fractional_cut_value (A_I.map (Rat.castHom ℝ))
                (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) u xy} =
        rational_mixed_polyhedron D_I D_C d by
    rw [hsystem]
    exact rationalMixedPolyhedronIsRational D_I D_C d
  ext xy
  rw [mem_rational_mixed_polyhedron_iff]
  constructor
  · rintro ⟨hxyPoly, hxyCuts⟩
    intro r
    refine Fin.addCases ?_ ?_ r
    · intro i
      -- The leading rows are exactly the original feasible system.
      have hi := (mem_real_mixed_polyhedron_iff.mp hxyPoly) i
      simpa only [D_I, D_C, d, Pi.add_apply, Matrix.mulVec, dotProduct,
        Matrix.map_apply, Fin.addCases_left] using hi
    · intro k
      -- A selected minimal cut becomes its standard rational row inequality.
      have hcut := hxyCuts (v k) (hv k).1 (hv k).2
      rw [normalizedMixedCutCoefficient_spec] at hcut
      have hcoeff : (fun i ↦ (c k i : ℝ)) =
          normalizedMixedCutCoefficient (fun i ↦ (b i : ℝ)) (v k) := by
        funext i
        exact hc k i
      rw [← hcoeff] at hcut
      have hrow := (rationalMixedCutRow_iff A_I A_C b (c k) xy).2 hcut
      simpa [D_I, D_C, d, Matrix.mulVec, dotProduct] using hrow
  · intro hrows
    have hxyPoly : xy ∈ real_mixed_polyhedron (A_I.map (Rat.castHom ℝ))
        (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) := by
      rw [mem_real_mixed_polyhedron_iff]
      intro i
      have hi := hrows (Fin.castAdd t i)
      simpa [D_I, D_C, d, Matrix.mulVec, dotProduct] using hi
    refine ⟨hxyPoly, ?_⟩
    intro u hu huIndep
    obtain ⟨k, hck⟩ := hdom u hu huIndep
    have hkRow := hrows (Fin.natAdd m k)
    have hkRowIneq :
        (fun j ↦ ((c k ᵥ* A_I) j : ℝ)) ⬝ᵥ xy.1 +
            (fun j ↦ ((c k ᵥ* A_C) j : ℝ)) ⬝ᵥ xy.2 ≤
          ((c k ⬝ᵥ b - 1 : ℚ) : ℝ) := by
      simpa [D_I, D_C, d, Matrix.mulVec, dotProduct] using hkRow
    have hkSlack : 1 ≤ (fun i ↦ (c k i : ℝ)) ⬝ᵥ
        ((fun i ↦ (b i : ℝ)) -
          ((A_I.map (Rat.castHom ℝ)) *ᵥ xy.1 +
            (A_C.map (Rat.castHom ℝ)) *ᵥ xy.2)) :=
      (rationalMixedCutRow_iff A_I A_C b (c k) xy).1 hkRowIneq
    have hslackNonneg : 0 ≤ (fun i ↦ (b i : ℝ)) -
        ((A_I.map (Rat.castHom ℝ)) *ᵥ xy.1 +
          (A_C.map (Rat.castHom ℝ)) *ᵥ xy.2) := by
      intro i
      exact sub_nonneg.mpr ((mem_real_mixed_polyhedron_iff.mp hxyPoly) i)
    rw [normalizedMixedCutCoefficient_spec]
    exact hkSlack.trans <|
      dotProduct_le_dotProduct_of_nonneg_right hck hslackNonneg

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap05/section_5_1_2/ch5_sec5_1_2_theorem_5_10.lean
Theorem 5.10 (Cook et al. [90]). Let `P ⊆ ℝ^I × ℝ^C` be a rational polyhedron and let
`S := P ∩ (ℤ^I × ℝ^C)`. Then the mixed split closure `P^split` is a rational polyhedron. -/
theorem mixed_split_closure_is_rational_mixed_polyhedron
    (P : Set (MixedRealPoint nI nC))
    (hP : is_rational_mixed_polyhedron P) :
    is_rational_mixed_polyhedron (mixed_split_closure P) := by
  -- Extract rational matrix data for the ambient polyhedron first.
  rcases existsRationalMixedPolyhedronPresentation P hP with ⟨m, A_I, A_C, b, rfl⟩
  by_cases hnI : nI = 0
  · -- With no integer coordinates the split family is empty, hence the closure is universal.
    subst nI
    rw [mixedSplitClosureEqUnivOfIntegerDimensionZero]
    exact univIsRationalMixedPolyhedron
  · -- For a nonempty integer block, pass through the independent-support cut interface.
    have hPresentation := independentSupportCutSystemIsRational A_I A_C b
    have hRationalReal :
        rational_mixed_polyhedron A_I A_C b =
          real_mixed_polyhedron (A_I.map (Rat.castHom ℝ))
            (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) := by
      ext xy
      rw [mem_rational_mixed_polyhedron_iff, mem_real_mixed_polyhedron_iff]
    rw [hRationalReal,
      mixedSplitClosureEqIndependentSupportCutSystem
        (A_I.map (Rat.castHom ℝ)) (A_C.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) hnI]
    exact hPresentation

end Theorem510

-- Audit that Theorem 5.10 uses only Lean's accepted logical foundations.
#print axioms mixed_split_closure_is_rational_mixed_polyhedron
