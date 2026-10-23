module

public import stacks_project.Chap06.Lemma_6_30_3
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Presheaf

universe u v

variable {X : Type u} [TopologicalSpace X]
variable {B : Set (Opens X)}

/-
Domain-style sampling for Lemma 6.30.4:
- primary domain: the basis-site sheaf condition, expressed through explicit basis covers and their
  pairwise overlaps;
- sampled owner declarations:
  `BasisCover`,
  `BasisIntersectionCover`,
  `BasisCover.HasSheafCondition`,
  `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible`;
- source/core/bridge triage:
  `source-facing`: the Stacks-style pairwise-overlap compatibility and unique gluing statement for
    a basis cover whose overlaps already lie in the basis;
  `core/canonical`: the owner object `BasisCover` together with the generic site-theoretic
    compatibility predicate `FamilyOfElementsOnObjects.IsCompatible`;
  `bridge/view`: the singleton overlap cover `BasisCover.singletonIntersectionCover`, which turns
    the general basis sheaf condition `(**)` into the source-facing pairwise-overlap form.

Primitive data are only the basis cover `𝒰 : BasisCover B U` and the cover-specific witness
`hInter` asserting that each actual overlap `Uᵢ ∩ Uⱼ` of that chosen cover lies in `B`. The
pairwise-overlap equalities are derived API: they unpack
`BasisCover.HasSheafCondition` for this singleton overlap cover, and should remain only a companion
bridge to the generic owner `FamilyOfElementsOnObjects.IsCompatible`, not a second primitive
owner.
-/

namespace BasisCover

variable {U : BasisOpen B}
variable (𝒰 : BasisCover B U)
variable (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)

/-- The actual pairwise overlap `Uᵢ ∩ Uⱼ`, viewed as a basis open when intersections stay in
`B`. -/
def intersection
    (i j : 𝒰.ι) : BasisOpen B :=
  ⟨(𝒰.obj i).obj ⊓ (𝒰.obj j).obj,
    hInter i j⟩

/-- The canonical inclusion of the overlap `Uᵢ ∩ Uⱼ` into the left factor `Uᵢ`. -/
abbrev intersectionLeft
    (i j : 𝒰.ι) : 𝒰.intersection hInter i j ⟶ 𝒰.obj i :=
  ⟨homOfLE inf_le_left⟩

/-- The canonical inclusion of the overlap `Uᵢ ∩ Uⱼ` into the right factor `Uⱼ`. -/
abbrev intersectionRight
    (i j : 𝒰.ι) : 𝒰.intersection hInter i j ⟶ 𝒰.obj j :=
  ⟨homOfLE inf_le_right⟩

/-- The source-facing pairwise-overlap compatibility condition is equivalent to the generic
site-theoretic compatibility predicate on the family of basis opens underlying the cover. -/
theorem isCompatible_iff
    (F : Presheaf.{max u v} (BasisOpen B)) (s : FamilyOfElementsOnObjects F 𝒰.obj) :
    s.IsCompatible ↔
      ∀ i j,
        F.map ((𝒰.intersectionLeft hInter i j).op) (s i) =
          F.map ((𝒰.intersectionRight hInter i j).op) (s j) := by
  constructor
  · intro hs i j
    simpa using
      hs (𝒰.intersection hInter i j) i j
        (𝒰.intersectionLeft hInter i j) (𝒰.intersectionRight hInter i j)
  · intro hs Z i j f g
    let h : Z ⟶ 𝒰.intersection hInter i j :=
      ⟨homOfLE <| le_inf (leOfHom f.hom) (leOfHom g.hom)⟩
    have hf : f = h ≫ 𝒰.intersectionLeft hInter i j := by
      apply ObjectProperty.hom_ext
      exact Subsingleton.elim _ _
    have hg : g = h ≫ 𝒰.intersectionRight hInter i j := by
      apply ObjectProperty.hom_ext
      exact Subsingleton.elim _ _
    calc
      F.map f.op (s i)
          = F.map h.op (F.map ((𝒰.intersectionLeft hInter i j).op) (s i)) := by
              rw [hf, op_comp, FunctorToTypes.map_comp_apply]
      _ = F.map h.op (F.map ((𝒰.intersectionRight hInter i j).op) (s j)) := by
            rw [hs i j]
      _ = F.map g.op (s j) := by
            rw [hg, op_comp, FunctorToTypes.map_comp_apply]

/-- The canonical overlap-cover bridge for a basis cover `𝒰`, obtained by taking each
`Uᵢ ∩ Uⱼ` itself as a singleton basis cover when intersections remain in `B`. -/
def singletonIntersectionCover
    : BasisIntersectionCover B 𝒰 where
  κ _ _ := PUnit
  obj i j _ := 𝒰.intersection hInter i j
  left i j _ := 𝒰.intersectionLeft hInter i j
  right i j _ := 𝒰.intersectionRight hInter i j
  iUnion_eq i j := by
    ext x
    simp [intersection]

/-- Lemma 6.30.4 specializes the basis sheaf condition `(**)` of Lemma 6.30.3 to the case where
the pairwise overlaps are already members of the basis, so no auxiliary overlap cover needs to be
chosen. -/
theorem hasSheafCondition_iff_uniqueGluing
    (F : Presheaf.{max u v} (BasisOpen B)) :
    HasSheafCondition F 𝒰 (𝒰.singletonIntersectionCover hInter) ↔
      ∀ s : FamilyOfElementsOnObjects F 𝒰.obj,
        s.IsCompatible →
          ∃! t : F.obj (op U), ∀ i, F.map (𝒰.hom i).op t = s i := by
  constructor
  · intro h s hs
    exact h s (fun i j _ ↦ (𝒰.isCompatible_iff hInter F s).1 hs i j)
  · intro h s hs
    exact h s ((𝒰.isCompatible_iff hInter F s).2 (fun i j ↦ hs i j PUnit.unit))

end BasisCover

-- Proof sketch: use Lemma 6.30.3 with the canonical singleton overlap covers from
-- `BasisCover.singletonIntersectionCover`, and rewrite the resulting sheaf condition by
-- `BasisCover.hasSheafCondition_iff_uniqueGluing`.
/-- Lemma 6.30.4: a basis presheaf is a sheaf exactly when unique gluing holds on each cover in a
chosen cofinal system, provided pairwise intersections of members of those covers stay in the
basis. -/
theorem basisPresheaf_isSheaf_iff_uniqueGluing_on_cofinal_basis_covers
    (hB : Opens.IsBasis B)
    (C : ∀ U : BasisOpen B, Set (BasisCover B U)) (hC : BasisCover.IsCofinalSystem C)
    (hInter :
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U →
        ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (F : Presheaf.{max u v} (BasisOpen B)) :
    Presheaf.IsSheaf (basisGrothendieckTopology B hB) F ↔
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U →
        ∀ s : FamilyOfElementsOnObjects F 𝒰.obj,
          s.IsCompatible →
            ∃! t : F.obj (op U), ∀ i, F.map (𝒰.hom i).op t = s i := by
  let hInterC : ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ C U → BasisIntersectionCover B 𝒰 :=
    fun {U} 𝒰 h𝒰 ↦ 𝒰.singletonIntersectionCover (hInter 𝒰 h𝒰)
  constructor
  · intro hSheaf U 𝒰 h𝒰 s hs
    have hCondition :=
      (basisPresheaf_isSheaf_iff_hasSheafCondition_on_cofinalSystem F C hInterC hB hC).1 hSheaf
    exact (𝒰.hasSheafCondition_iff_uniqueGluing (hInter 𝒰 h𝒰) F).1 (hCondition 𝒰 h𝒰) s hs
  · intro hUnique
    refine (basisPresheaf_isSheaf_iff_hasSheafCondition_on_cofinalSystem F C hInterC hB hC).2 ?_
    intro U 𝒰 h𝒰
    exact (𝒰.hasSheafCondition_iff_uniqueGluing (hInter 𝒰 h𝒰) F).2 (hUnique 𝒰 h𝒰)
