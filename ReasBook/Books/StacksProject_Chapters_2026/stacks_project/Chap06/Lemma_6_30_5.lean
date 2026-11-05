module

public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.Definition_6_30_2
public import stacks_project.Chap06.Stalks_as_filtered_colimits_over_basis_neighbourhoods

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace TopCat TopCat.Presheaf
open TopCat.Presheaf.Sheafify

noncomputable section

universe u v

namespace BasisSheaf

variable {X : Type u} [TopologicalSpace X] {B : Set (Opens X)}

-- Route correction: this item now stops at the source-facing basis-stalk statement of
-- Lemma 6.30.5. The later ordinary-sheaf transport belongs to `Lemma_6_30_6`, not here.

/-- The stalk of a basis sheaf at `x`, computed directly as the filtered colimit over basis
neighborhoods of `x`. -/
abbrev stalk (F : BasisSheaf B) (hB : Opens.IsBasis B) (x : X) :=
  basisPresheafStalk F.obj x

/-- The family of basis-stalk germs associated to a section over a basis open `U`. -/
abbrev sectionToBasisStalkFamily (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B) :
    F.obj.obj (op U) → ∀ x : U.1, F.stalk hB x.1 :=
  fun s x ↦
    colimit.ι (basisPresheafStalkDiagram F.obj x.1) (op ⟨U, x.2⟩) s

/-- The source-facing local representability condition from Stacks Lemma 6.30.5: a family of basis
stalk elements on `U` is locally induced by sections on basis neighborhoods inside `U`. -/
def IsLocallyRepresentable (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B)
    (t : ∀ x : U.1, F.stalk hB x.1) : Prop :=
  ∀ x : U.1,
    ∃ (V : BasisOpen B) (i : V ⟶ U) (_ : x.1 ∈ V.1) (s : F.obj.obj (op V)),
      ∀ y : V.1, t ⟨y.1, i.hom.le y.2⟩ = sectionToBasisStalkFamily F hB V s y

/-- Helper for Lemma 6.30.5: basis neighborhoods of `x` form a filtered indexing category after
taking opposites, since the basis can be refined inside any pairwise intersection. -/
instance basisOpenNhds_isFiltered (hB : Opens.IsBasis B) (x : X) :
    IsFiltered (BasisOpenNhds_basisColimits B x)ᵒᵖ := by
  classical
  letI : Nonempty ((BasisOpenNhds_basisColimits B x)ᵒᵖ) := by
    obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, -⟩ :=
      hB.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨op ⟨⟨W, hWB⟩, hxW⟩⟩
  refine
    { nonempty := inferInstance
      toIsFilteredOrEmpty :=
        { cocone_objs := ?_
          cocone_maps := ?_ } }
  · intro U V
    -- Refine two basis neighborhoods by a smaller basis neighborhood inside their intersection.
    have hxUV :
        x ∈ (((unop U).1.1 ⊓ (unop V).1.1 : Opens X)) := ⟨(unop U).2, (unop V).2⟩
    obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, hWle⟩ :=
      hB.exists_subset_of_mem_open hxUV ((((unop U).1.1 ⊓ (unop V).1.1 : Opens X)).2)
    let T : BasisOpenNhds_basisColimits B x := ⟨⟨W, hWB⟩, hxW⟩
    have hTU : W ≤ (unop U).1.1 := le_trans hWle inf_le_left
    have hTV : W ≤ (unop V).1.1 := le_trans hWle inf_le_right
    let iTU : T ⟶ unop U :=
      ObjectProperty.homMk
        (ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hTU))
    let iTV : T ⟶ unop V :=
      ObjectProperty.homMk
        (ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hTV))
    refine ⟨op T, ?_, ?_, trivial⟩
    · exact iTU.op
    · exact iTV.op
  · intro U V f g
    -- The indexing category is a preorder, so parallel arrows are automatically equal.
    refine ⟨V, 𝟙 V, ?_⟩
    apply Opposite.unop_injective
    apply ObjectProperty.hom_ext _
    apply ObjectProperty.hom_ext _
    exact Subsingleton.elim _ _

/-- Helper for Lemma 6.30.5: equality of two basis-stalk germs at a point can be represented on a
smaller basis neighborhood by equal restricted sections. -/
lemma exists_restriction_eq_of_basis_stalk_eq
    (F : BasisSheaf B) (hB : Opens.IsBasis B)
    {V W : BasisOpen B}
    (sV : F.obj.obj (op V)) (sW : F.obj.obj (op W))
    {x : X} (hxV : x ∈ V.1) (hxW : x ∈ W.1)
    (hEq :
      sectionToBasisStalkFamily F hB V sV ⟨x, hxV⟩ =
        sectionToBasisStalkFamily F hB W sW ⟨x, hxW⟩) :
    ∃ (T : BasisOpen B) (iTV : T ⟶ V) (iTW : T ⟶ W), x ∈ T.1 ∧
      F.obj.map iTV.op sV = F.obj.map iTW.op sW := by
  -- Unpack equality in the filtered colimit into equality after restriction to a common
  -- basis neighborhood of `x`.
  letI : IsFiltered (BasisOpenNhds_basisColimits B x)ᵒᵖ := basisOpenNhds_isFiltered (B := B) hB x
  rw [sectionToBasisStalkFamily, sectionToBasisStalkFamily] at hEq
  rw [Types.FilteredColimit.colimit_eq_iff (F := basisPresheafStalkDiagram F.obj x)] at hEq
  rcases hEq with ⟨T, iTV, iTW, hEq⟩
  refine ⟨(unop T).1, (iTV.unop).hom, (iTW.unop).hom, (unop T).2, ?_⟩
  simpa [basisPresheafStalkDiagram] using hEq

/-- Helper for Lemma 6.30.5: taking the basis-stalk germ family commutes with restricting a
section to a smaller basis open. -/
lemma sectionToBasisStalkFamily_map
    (F : BasisSheaf B) (hB : Opens.IsBasis B)
    {V W : BasisOpen B} (i : V ⟶ W) (s : F.obj.obj (op W)) (x : V.1) :
    sectionToBasisStalkFamily F hB V (F.obj.map i.op s) x =
      sectionToBasisStalkFamily F hB W s ⟨x.1, i.hom.le x.2⟩ := by
  -- Both germs are represented by the same section, viewed along the colimit cocone naturality.
  let ix : (⟨V, x.2⟩ : BasisOpenNhds_basisColimits B x.1) ⟶ ⟨W, i.hom.le x.2⟩ := ObjectProperty.homMk i
  rw [sectionToBasisStalkFamily, sectionToBasisStalkFamily]
  change
    colimit.ι (basisPresheafStalkDiagram F.obj x.1) (op ⟨V, x.2⟩)
        (((basisPresheafStalkDiagram F.obj x.1).map ix.op) s) =
      colimit.ι (basisPresheafStalkDiagram F.obj x.1) (op ⟨W, i.hom.le x.2⟩) s
  exact congrFun (colimit.w (basisPresheafStalkDiagram F.obj x.1) ix.op) s

/-- Helper for Lemma 6.30.5: for any basis cover, take as overlap cover all basis opens contained
in the actual pairwise intersections. -/
def intersectionBasisCover (hB : Opens.IsBasis B) {U : BasisOpen B} (𝒰 : BasisCover B U) :
    BasisIntersectionCover B 𝒰 where
  κ i j := { V : BasisOpen B // V.1 ≤ (𝒰.obj i).1 ⊓ (𝒰.obj j).1 }
  obj _ _ k := k.1
  left _ _ k := ⟨homOfLE (le_trans k.2 inf_le_left)⟩
  right _ _ k := ⟨homOfLE (le_trans k.2 inf_le_right)⟩
  iUnion_eq i j := by
    ext x
    constructor
    · intro hx
      obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, hWle⟩ :=
        hB.exists_subset_of_mem_open hx (((𝒰.obj i).1 ⊓ (𝒰.obj j).1).2)
      exact Set.mem_iUnion.mpr ⟨⟨⟨W, hWB⟩, hWle⟩, hxW⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
      exact k.2 hk

variable (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B)

-- Proof sketch: this is the defining colimit-germ family, so for each `x : U` we may take the
-- neighborhood `V = U` and the original section `s`.
/-- Any section over `U` determines a basis-stalk family satisfying the source-facing local
representability condition. -/
theorem sectionToBasisStalkFamily_isLocallyRepresentable (s : F.obj.obj (op U)) :
    IsLocallyRepresentable F hB U (sectionToBasisStalkFamily F hB U s) := by
  intro x
  refine ⟨U, 𝟙 U, x.2, s, ?_⟩
  -- The chosen witness section is literally the original section on `U`.
  intro y
  simp [sectionToBasisStalkFamily]

/-- Helper for Lemma 6.30.5: the map from sections on a basis open to their basis-stalk families
is injective. -/
lemma sectionToBasisStalkFamily_injective :
    Function.Injective (sectionToBasisStalkFamily F hB U) := by
  intro s s' hss'
  classical
  have hlocal :
      ∀ x : U.1,
        ∃ (V : BasisOpen B) (i : V ⟶ U), x.1 ∈ V.1 ∧
          F.obj.map i.op s = F.obj.map i.op s' := by
    intro x
    -- Equality of germs at `x` becomes equality after restriction to a smaller basis open.
    obtain ⟨V, iVs, iVs', hxV, hEq⟩ :=
      exists_restriction_eq_of_basis_stalk_eq F hB s s' x.2 x.2 (congrFun hss' x)
    have hi_hom : iVs.hom = iVs'.hom := Subsingleton.elim _ _
    have hi' : iVs = iVs' := ObjectProperty.hom_ext _ hi_hom
    refine ⟨V, iVs, hxV, ?_⟩
    simpa [hi'] using hEq
  choose V i hi hs using hlocal
  let 𝒰 : BasisCover B U :=
    { ι := U.1
      obj := V
      hom := i
      iUnion_eq := by
        ext y
        constructor
        · intro hy
          exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hi ⟨y, hy⟩⟩
        · intro hy
          rcases Set.mem_iUnion.mp hy with ⟨x, hx⟩
          exact (i x).hom.le hx }
  let σ : ∀ x : 𝒰.ι, F.obj.obj (op (𝒰.obj x)) := fun x ↦ F.obj.map ((𝒰.hom x).op) s
  have hcompat :
      ∀ x y k,
        F.obj.map ((intersectionBasisCover hB 𝒰).left x y k).op (σ x) =
          F.obj.map ((intersectionBasisCover hB 𝒰).right x y k).op (σ y) := by
    intro x y k
    -- Both overlap restrictions are the restriction of the same global section `s`.
    have hcomp :
        (intersectionBasisCover hB 𝒰).left x y k ≫ 𝒰.hom x =
          (intersectionBasisCover hB 𝒰).right x y k ≫ 𝒰.hom y :=
      ObjectProperty.hom_ext _ (Subsingleton.elim _ _)
    dsimp [σ]
    calc
      F.obj.map ((intersectionBasisCover hB 𝒰).left x y k).op (F.obj.map (𝒰.hom x).op s) =
          F.obj.map (((intersectionBasisCover hB 𝒰).left x y k ≫ 𝒰.hom x).op) s := by
            simp [FunctorToTypes.map_comp_apply]
      _ = F.obj.map (((intersectionBasisCover hB 𝒰).right x y k ≫ 𝒰.hom y).op) s := by
            rw [hcomp]
      _ = F.obj.map ((intersectionBasisCover hB 𝒰).right x y k).op (F.obj.map (𝒰.hom y).op s) := by
            simp [FunctorToTypes.map_comp_apply]
  obtain ⟨t, ht, ht_unique⟩ := F.property 𝒰 (intersectionBasisCover hB 𝒰) σ hcompat
  have hs_glue : ∀ x, F.obj.map ((𝒰.hom x).op) s = σ x := by
    intro x
    rfl
  have hs'_glue : ∀ x, F.obj.map ((𝒰.hom x).op) s' = σ x := by
    intro x
    calc
      F.obj.map ((𝒰.hom x).op) s' = F.obj.map ((𝒰.hom x).op) s := by
        symm
        exact hs x
      _ = σ x := rfl
  -- Uniqueness for the basis sheaf condition identifies the two original sections.
  exact (ht_unique s hs_glue).trans (ht_unique s' hs'_glue).symm

-- Proof sketch: on each overlap basis open, the two local sections induce the same basis-stalk
-- family because both realize the original family `t`; injectivity on that overlap then gives the
-- required equality of restricted sections. The basis sheaf condition glues these local sections.
/-- Lemma 6.30.5: for a sheaf of sets `F` on a basis `B` and a basis open `U`, taking germs gives a
bijection from sections on `U` to families of basis-stalk elements on `U` that are locally induced
by sections on basis neighborhoods inside `U`. -/
theorem sections_bijective_toLocallyRepresentableFamilies :
    Function.Bijective
      (fun s : F.obj.obj (op U) ↦
        show { t : ∀ x : U.1, F.stalk hB x.1 | IsLocallyRepresentable F hB U t } from
          ⟨sectionToBasisStalkFamily F hB U s,
            sectionToBasisStalkFamily_isLocallyRepresentable F hB U s⟩) := by
  constructor
  · intro s s' h
    -- Injectivity is the uniqueness half of the source proof.
    apply sectionToBasisStalkFamily_injective F hB U
    exact congrArg Subtype.val h
  · intro t
    rcases t with ⟨t, ht⟩
    suffices ∃ s : F.obj.obj (op U), sectionToBasisStalkFamily F hB U s = t by
      rcases this with ⟨s, hs⟩
      exact ⟨s, Subtype.ext hs⟩
    classical
    choose V i hi σ hσ using ht
    let 𝒰 : BasisCover B U :=
      { ι := U.1
        obj := V
        hom := i
        iUnion_eq := by
          ext y
          constructor
          · intro hy
            exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hi ⟨y, hy⟩⟩
          · intro hy
            rcases Set.mem_iUnion.mp hy with ⟨x, hx⟩
            exact (i x).hom.le hx }
    have hcompat :
        ∀ x y k,
          F.obj.map ((intersectionBasisCover hB 𝒰).left x y k).op (σ x) =
            F.obj.map ((intersectionBasisCover hB 𝒰).right x y k).op (σ y) := by
      intro x y k
      -- On the overlap, both restricted local sections realize the same stalk family `t`.
      apply sectionToBasisStalkFamily_injective F hB ((intersectionBasisCover hB 𝒰).obj x y k)
      ext z
      calc
        sectionToBasisStalkFamily F hB ((intersectionBasisCover hB 𝒰).obj x y k)
            (F.obj.map ((intersectionBasisCover hB 𝒰).left x y k).op (σ x)) z =
          sectionToBasisStalkFamily F hB (V x) (σ x)
            ⟨z.1, ((intersectionBasisCover hB 𝒰).left x y k).hom.le z.2⟩ := by
              simpa using
                sectionToBasisStalkFamily_map F hB
                  ((intersectionBasisCover hB 𝒰).left x y k) (σ x) z
        _ = t ⟨z.1, (i x).hom.le (((intersectionBasisCover hB 𝒰).left x y k).hom.le z.2)⟩ := by
          symm
          exact hσ x ⟨z.1, ((intersectionBasisCover hB 𝒰).left x y k).hom.le z.2⟩
        _ = t ⟨z.1, (i y).hom.le (((intersectionBasisCover hB 𝒰).right x y k).hom.le z.2)⟩ := by
          have hz :
              (⟨z.1, (i x).hom.le (((intersectionBasisCover hB 𝒰).left x y k).hom.le z.2)⟩ : U.1) =
                ⟨z.1, (i y).hom.le (((intersectionBasisCover hB 𝒰).right x y k).hom.le z.2)⟩ :=
            Subtype.ext rfl
          cases hz
          rfl
        _ = sectionToBasisStalkFamily F hB (V y) (σ y)
            ⟨z.1, ((intersectionBasisCover hB 𝒰).right x y k).hom.le z.2⟩ := by
          exact hσ y ⟨z.1, ((intersectionBasisCover hB 𝒰).right x y k).hom.le z.2⟩
        _ =
          sectionToBasisStalkFamily F hB ((intersectionBasisCover hB 𝒰).obj x y k)
            (F.obj.map ((intersectionBasisCover hB 𝒰).right x y k).op (σ y)) z := by
              symm
              simpa using
                sectionToBasisStalkFamily_map F hB
                  ((intersectionBasisCover hB 𝒰).right x y k) (σ y) z
    obtain ⟨s, hs, -⟩ := F.property 𝒰 (intersectionBasisCover hB 𝒰) σ hcompat
    refine ⟨s, ?_⟩
    ext x
    have hxEq : (⟨x.1, (𝒰.hom x).hom.le (hi x)⟩ : U.1) = x := Subtype.ext rfl
    -- Evaluate the glued section on the chosen neighborhood witnessing local representability at
    -- `x`.
    calc
      sectionToBasisStalkFamily F hB U s x =
          sectionToBasisStalkFamily F hB U s ⟨x.1, (𝒰.hom x).hom.le (hi x)⟩ := by
            cases hxEq.symm
            rfl
      _ =
          sectionToBasisStalkFamily F hB (V x)
            (F.obj.map ((𝒰.hom x).op) s) ⟨x.1, hi x⟩ := by
              symm
              simpa using
                sectionToBasisStalkFamily_map F hB (𝒰.hom x) s ⟨x.1, hi x⟩
      _ = sectionToBasisStalkFamily F hB (V x) (σ x) ⟨x.1, hi x⟩ := by
        rw [hs x]
      _ = t ⟨x.1, (i x).hom.le (hi x)⟩ := by
        symm
        exact hσ x ⟨x.1, hi x⟩
      _ = t x := by
        cases hxEq
        rfl

/-- `Set.BijOn` restatement of Lemma 6.30.5. -/
theorem sections_bijOn_locallyRepresentableFamilies :
    Set.BijOn
      (sectionToBasisStalkFamily F hB U)
      (Set.univ : Set (F.obj.obj (op U)))
      { t : ∀ x : U.1, F.stalk hB x.1 | IsLocallyRepresentable F hB U t } := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact sectionToBasisStalkFamily_isLocallyRepresentable F hB U s
  · intro s _ s' _ h
    exact sectionToBasisStalkFamily_injective F hB U h
  · intro t ht
    obtain ⟨s, hs⟩ :=
      (sections_bijective_toLocallyRepresentableFamilies F hB U).2 ⟨t, ht⟩
    exact ⟨s, Set.mem_univ _, congrArg Subtype.val hs⟩

end BasisSheaf
