/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_4
import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}
variable (r : FreeGroup X)

local instance theorem_2_6_1_decidableEq : DecidableEq X := Classical.decEq X
local notation "basis" => FreeGroupBasis.ofFreeGroup X
local notation "G" => PresentedGroup (Set.singleton r)
local notation "gen" => (PresentedGroup.of : X → G)

-- Layer triage:
-- `source-facing`: Magnus's Freiheitssatz for the one-relator quotient `G = (X; r)`, a subset
-- `Y ⊆ X` omitting a generator `x` that occurs in the cyclically reduced relator `r`, and the
-- conclusion that the images of `Y` in `G` stay distinct and form a free basis of the subgroup
-- they generate.
-- `core/canonical`: `FreeGroupBasis.ofFreeGroup X`, `PresentedGroup (Set.singleton r)`,
-- `PresentedGroup.of`, `Subgroup.closure`, and `IsFreeGroupBasis`.
-- `bridge/view`: `basisLetterOccurs basis x r` is the established occurrence predicate for a
-- basis generator in a free-group element, and the subgroup-basis conclusion is expressed in the
-- canonical subset form used by `closure_preimage_isFreeGroupBasis_of_bijOn`.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.ofFreeGroup X` is the owner basis of the ambient free group `FreeGroup X`.
-- 2. `basisLetterOccurs` from Proposition `1-7-4` is the chapter's canonical bridge from the
--    basis owner to the source phrase “the generator `x` occurs in `r`”.
-- 3. `PresentedGroup (Set.singleton r)` together with `PresentedGroup.of` is the canonical owner
--    abstraction for the one-relator quotient `(X; r)`.
-- 4. `FreeGroup.map`, `FreeGroup.range_lift_eq_closure`, and `MulEquiv.ofBijective` are the
--    canonical owner-side APIs for embedding the free group on `Y` into `FreeGroup X`, identifying
--    its image subgroup in the quotient, and transporting the canonical free basis along the
--    resulting equivalence.
--
-- Primitive vs. derived:
-- the primitive source data are the relator `r`, the subset `Y`, the omitted generator `x`, and
-- the cyclic-reduction and occurrence hypotheses on `r`. The image subset `gen '' Y`, the
-- subgroup it generates in `G`, and the corresponding subtype-level basis assertion are derived
-- owner-side objects, so the theorem states them directly rather than through a parallel wrapper.

-- Proof sketch: this is Magnus's Freiheitssatz. One proves first that every nontrivial element of
-- the singleton normal closure of a cyclically reduced relator still contains each basis letter
-- occurring in that relator. Applying this to a subset `Y` omitting such a letter `x` shows that
-- no nontrivial reduced word in the images of `Y` can become trivial in the one-relator quotient,
-- so those images remain distinct and satisfy the universal property of a free basis for the
-- subgroup they generate.
/-- Theorem 2-6-1: if `r` is a cyclically reduced relator in the free group on `X`, and `Y ⊆ X`
omits a generator `x` that occurs in `r`, then in the one-relator quotient `(X; r)` the images of
the generators from `Y` remain distinct and form a free basis of the subgroup they generate. This
is the Freiheitssatz. -/
theorem freiheitssatz_injOn_presentedGroup_of_and_isFreeGroupBasis
    (Y : Set X) {x : X} (hr : FreeGroup.IsCyclicallyReduced r.toWord)
    (hx : basisLetterOccurs basis x r)
    (hxY : x ∉ Y) :
    Set.InjOn gen Y ∧
      IsFreeGroupBasis {g : Subgroup.closure (gen '' Y) | (g : G) ∈ gen '' Y} := by
  classical
  let embedY : FreeGroup Y →* FreeGroup X := FreeGroup.map Subtype.val
  let retractY : FreeGroup X →* FreeGroup Y :=
    FreeGroup.lift fun y ↦ if hy : y ∈ Y then FreeGroup.of ⟨y, hy⟩ else 1
  have hleft : retractY.comp embedY = MonoidHom.id (FreeGroup Y) := by
    ext y
    simp [embedY, retractY]
  have embedY_injective : Function.Injective embedY := by
    intro u v huv
    have h' := congrArg retractY huv
    have hleft_apply := DFunLike.congr_fun hleft
    exact (hleft_apply u).symm.trans <| h'.trans (hleft_apply v)
  let evalY : FreeGroup Y →* G := FreeGroup.lift fun y ↦ gen y.1
  have heval : (PresentedGroup.mk (Set.singleton r)).comp embedY = evalY := by
    ext y
    simp [embedY, evalY, PresentedGroup.of]
  have hnot_occurs :
      ∀ w : FreeGroup Y, ¬ basisLetterOccurs basis x (embedY w) := by
    intro w
    rw [basisLetterOccurs, reducedWordSupport, List.mem_toFinset]
    intro hxw
    have hembed :
        embedY w = FreeGroup.mk (w.toWord.map fun a : Y × Bool ↦ (a.1.1, a.2)) := by
      have hw : FreeGroup.mk w.toWord = w := FreeGroup.mk_toWord
      calc
        embedY w = embedY (FreeGroup.mk w.toWord) := by rw [hw]
        _ = FreeGroup.mk (w.toWord.map fun a : Y × Bool ↦ (a.1.1, a.2)) := by
          simp [embedY, FreeGroup.map.mk]
    have htoWord_embed :
        (embedY w).toWord = FreeGroup.reduce (w.toWord.map fun a : Y × Bool ↦ (a.1.1, a.2)) := by
      rw [hembed, FreeGroup.toWord_mk]
    have hxred :
        x ∈
          (FreeGroup.reduce
            (w.toWord.map fun a : Y × Bool ↦ (a.1.1, a.2))).map Prod.fst := by
      simpa [FreeGroupBasis.ofFreeGroup, htoWord_embed] using hxw
    have hred :
        FreeGroup.Red (w.toWord.map fun a : Y × Bool ↦ (a.1.1, a.2))
          (FreeGroup.reduce (w.toWord.map fun a : Y × Bool ↦ (a.1.1, a.2))) :=
      FreeGroup.reduce.red
    have hsub :
        List.Sublist
          ((FreeGroup.reduce (w.toWord.map fun a : Y × Bool ↦ (a.1.1, a.2))).map Prod.fst)
          (w.toWord.map fun a : Y × Bool ↦ a.1.1) :=
      by
        simpa [List.map_map] using (FreeGroup.Red.sublist hred).map Prod.fst
    have hxmem : x ∈ w.toWord.map fun a : Y × Bool ↦ a.1.1 := hsub.subset hxred
    rcases List.mem_map.1 hxmem with ⟨a, _, rfl⟩
    exact hxY a.1.2
  have evalY_injective : Function.Injective evalY := by
    intro u v huv
    by_contra huv'
    have hmk : PresentedGroup.mk (Set.singleton r) (embedY (u * v⁻¹)) = 1 := by
      change (((PresentedGroup.mk (Set.singleton r)).comp embedY) (u * v⁻¹)) = 1
      rw [heval, map_mul, huv, map_inv, mul_inv_cancel]
    have hmem : embedY (u * v⁻¹) ∈ Subgroup.normalClosure (Set.singleton r) :=
      PresentedGroup.mk_eq_one_iff.mp hmk
    have hne : embedY (u * v⁻¹) ≠ 1 := by
      intro htriv
      apply huv'
      exact eq_of_mul_inv_eq_one (embedY_injective <| by simpa using htriv)
    exact hnot_occurs (u * v⁻¹) <|
      FreeGroupBasis.basisLetterOccurs_of_mem_normalClosure_singleton_of_isCyclicallyReduced
        basis hr hx hmem hne
  have hgen_inj : Set.InjOn gen Y := by
    intro y hy z hz hyz
    have hyz' :
        evalY (FreeGroup.of ⟨y, hy⟩) = evalY (FreeGroup.of ⟨z, hz⟩) := by
      simpa [evalY] using hyz
    have hsub :
        (⟨y, hy⟩ : Y) = ⟨z, hz⟩ :=
      FreeGroup.of_injective (evalY_injective hyz')
    exact congrArg Subtype.val hsub
  have hrange : evalY.range = Subgroup.closure (gen '' Y) := by
    rw [FreeGroup.range_lift_eq_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let evalClosure : FreeGroup Y →* Subgroup.closure (gen '' Y) :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp evalY.rangeRestrict
  have evalClosure_injective : Function.Injective evalClosure := by
    intro u v huv
    have hrr_injective : Function.Injective evalY.rangeRestrict :=
      (MonoidHom.rangeRestrict_injective_iff).2 evalY_injective
    exact hrr_injective ((MulEquiv.subgroupCongr hrange).injective huv)
  have evalClosure_surjective : Function.Surjective evalClosure := by
    intro g
    rcases evalY.rangeRestrict_surjective ((MulEquiv.subgroupCongr hrange).symm g) with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    change (MulEquiv.subgroupCongr hrange) (evalY.rangeRestrict w) = g
    simp [hw]
  let basisY : FreeGroupBasis Y (Subgroup.closure (gen '' Y)) :=
    (FreeGroupBasis.ofFreeGroup Y).map (MulEquiv.ofBijective evalClosure
      ⟨evalClosure_injective, evalClosure_surjective⟩)
  have hbasis_range :
      Set.range basisY = {g : Subgroup.closure (gen '' Y) | (g : G) ∈ gen '' Y} := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      change (evalClosure (FreeGroup.of y) : G) ∈ gen '' Y
      exact ⟨y.1, y.2, by simp [evalClosure, evalY]⟩
    · rintro hg
      rcases hg with ⟨y, hy, hgy⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      change (basisY ⟨y, hy⟩ : G) = g
      simpa [basisY, evalClosure, evalY] using hgy
  exact ⟨hgen_inj, hbasis_range ▸ FreeGroupBasis.isFreeGroupBasis_range basisY⟩

end
