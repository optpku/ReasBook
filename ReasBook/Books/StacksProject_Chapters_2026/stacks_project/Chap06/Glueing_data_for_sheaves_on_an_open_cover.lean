module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Sheaves.Functors
public import stacks_project.Chap06.Lemma_6_21_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe u w

section

variable {X : TopCat.{u}}

/-- The topological space underlying the open subspace `U ⊆ X`. -/
abbrev openSubsetSpace (U : Opens X) : TopCat.{u} :=
  (Opens.toTopCat X).obj U

/-- The inclusion of the open subspace `U` into the ambient space `X`. -/
abbrev openSubsetInclusion (U : Opens X) : openSubsetSpace U ⟶ X :=
  Opens.inclusion' U

/-- The inclusion of `U ∩ V` into `U`. -/
abbrev openSubsetIntersectionLeftInclusion (U V : Opens X) :
    openSubsetSpace (U ⊓ V) ⟶ openSubsetSpace U :=
  (Opens.toTopCat X).map (homOfLE inf_le_left)

/-- The inclusion of `U ∩ V` into `V`. -/
abbrev openSubsetIntersectionRightInclusion (U V : Opens X) :
    openSubsetSpace (U ⊓ V) ⟶ openSubsetSpace V :=
  (Opens.toTopCat X).map (homOfLE inf_le_right)

/-- The inclusion of `U ∩ V ∩ W` into `U`. -/
abbrev openSubsetTripleFirstInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace U :=
  (Opens.toTopCat X).map (homOfLE <|
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans
      (show U ⊓ V ≤ U from inf_le_left))

/-- The inclusion of `U ∩ V ∩ W` into `V`. -/
abbrev openSubsetTripleSecondInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace V :=
  (Opens.toTopCat X).map (homOfLE <|
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans
      (show U ⊓ V ≤ V from inf_le_right))

/-- The inclusion of `U ∩ V ∩ W` into `W`. -/
abbrev openSubsetTripleThirdInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace W :=
  (Opens.toTopCat X).map (homOfLE inf_le_right)

/-- The inclusion of `U ∩ V ∩ W` into `U ∩ V`. -/
abbrev openSubsetTripleToPairLeftInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace (U ⊓ V) :=
  (Opens.toTopCat X).map (homOfLE inf_le_left)

/-- The inclusion of `U ∩ V ∩ W` into `V ∩ W`. -/
abbrev openSubsetTripleToPairCenterInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace (V ⊓ W) :=
  (Opens.toTopCat X).map (homOfLE (inf_le_inf inf_le_right le_rfl))

/-- The inclusion of `U ∩ V ∩ W` into `U ∩ W`. -/
abbrev openSubsetTripleToPairOuterInclusion (U V W : Opens X) :
    openSubsetSpace (U ⊓ V ⊓ W) ⟶ openSubsetSpace (U ⊓ W) :=
  (Opens.toTopCat X).map (homOfLE
    (inf_le_inf (show U ⊓ V ≤ U from inf_le_left) le_rfl))

public abbrev tripleOverlapHom12
    {ι : Type w} (U : ι → Opens X)
    (family : ∀ i : ι, TopCat.Sheaf (Type u) (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (family i)) ≅
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion (U i) (U j))).obj (family j)))
    (i j k : ι) :
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj (family i)) ⟶
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj (family j)) :=
  (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U j))).symm.hom.app (family i) ≫
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).mapIso
        (overlapIso i j)).hom ≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U j))).symm.inv.app (family j)

public abbrev tripleOverlapHom23
    {ι : Type w} (U : ι → Opens X)
    (family : ∀ i : ι, TopCat.Sheaf (Type u) (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (family i)) ≅
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion (U i) (U j))).obj (family j)))
    (i j k : ι) :
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleSecondInclusion (U i) (U j) (U k))).obj (family j)) ⟶
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj (family k)) :=
  (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U j) (U k))).symm.hom.app (family j) ≫
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).mapIso
        (overlapIso j k)).hom ≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U j) (U k))).symm.inv.app (family k)

public abbrev tripleOverlapHom13
    {ι : Type w} (U : ι → Opens X)
    (family : ∀ i : ι, TopCat.Sheaf (Type u) (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (family i)) ≅
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion (U i) (U j))).obj (family j)))
    (i j k : ι) :
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleFirstInclusion (U i) (U j) (U k))).obj (family i)) ⟶
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleThirdInclusion (U i) (U j) (U k))).obj (family k)) :=
  (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U k))).symm.hom.app (family i) ≫
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).mapIso
        (overlapIso i k)).hom ≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U k))).symm.inv.app (family k)

/-- The cocycle condition for pairwise overlap isomorphisms in a sheaf gluing datum over an open
cover. -/
def SheafOpenCoverGlueingCocycleCondition
    {ι : Type w} (U : ι → Opens X)
    (family : ∀ i : ι, TopCat.Sheaf (Type u) (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (family i)) ≅
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion (U i) (U j))).obj (family j))) :
    Prop :=
  ∀ i j k : ι,
    tripleOverlapHom12 U family overlapIso i j k ≫
      tripleOverlapHom23 U family overlapIso i j k =
    tripleOverlapHom13 U family overlapIso i j k

/-- Gluing data for sheaves of sets on an open cover: a family of local sheaves together with
pairwise overlap isomorphisms satisfying the cocycle condition on triple intersections. -/
structure SheafOpenCoverGlueing {ι : Type w} (U : ι → Opens X) where
  /-- The local sheaf on the cover member `U i`. -/
  localSheaf : ∀ i, TopCat.Sheaf (Type u) (openSubsetSpace (U i))
  /-- The prescribed identification of the restrictions of `F i` and `F j` to `U i ∩ U j`. -/
  overlapIso : ∀ i j,
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (localSheaf i)) ≅
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionRightInclusion (U i) (U j))).obj (localSheaf j))
  /-- The overlap identifications satisfy the cocycle condition on triple intersections. -/
  cocycle : SheafOpenCoverGlueingCocycleCondition U localSheaf overlapIso
  /-- The indexed family of opens covers the ambient space. -/
  isCover : TopologicalSpace.IsOpenCover U

namespace SheafOpenCoverGlueing

variable {ι : Type w} {U : ι → Opens X}

public abbrev realizationLeftHom (data : SheafOpenCoverGlueing U)
    (F : X.Sheaf (Type u))
    (φ : ∀ i : ι,
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F) ≅ data.localSheaf i)
    (i j : ι) :
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i ⊓ U j))).obj F) ⟶
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionLeftInclusion (U i) (U j))).obj (data.localSheaf i)) :=
  (TopCat.Sheaf.pullbackComp
      (openSubsetIntersectionLeftInclusion (U i) (U j))
      (openSubsetInclusion (U i))).symm.hom.app F ≫
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))).mapIso (φ i)).hom

public abbrev realizationRightHom (data : SheafOpenCoverGlueing U)
    (F : X.Sheaf (Type u))
    (φ : ∀ i : ι,
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F) ≅ data.localSheaf i)
    (i j : ι) :
    ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i ⊓ U j))).obj F) ⟶
      ((TopCat.Sheaf.pullback (Type u)
        (openSubsetIntersectionRightInclusion (U i) (U j))).obj (data.localSheaf j)) :=
  (TopCat.Sheaf.pullbackComp
      (openSubsetIntersectionRightInclusion (U i) (U j))
      (openSubsetInclusion (U j))).symm.hom.app F ≫
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionRightInclusion (U i) (U j))).mapIso (φ j)).hom

/-- A sheaf on `X` realizes the given open-cover gluing datum if its restrictions to the cover
members recover the chosen local sheaves and the induced overlap comparisons agree with the
prescribed pairwise isomorphisms. -/
def Realizes (data : SheafOpenCoverGlueing U) (F : X.Sheaf (Type u)) : Prop :=
  ∃ φ : ∀ i : ι,
      ((TopCat.Sheaf.pullback (Type u) (openSubsetInclusion (U i))).obj F) ≅ data.localSheaf i,
    ∀ i j : ι,
      realizationLeftHom data F φ i j ≫ (data.overlapIso i j).hom =
        realizationRightHom data F φ i j

/-- A morphism of open-cover gluing data is a family of local morphisms compatible with the
prescribed overlap isomorphisms. -/
@[ext] structure Hom (A B : SheafOpenCoverGlueing U) where
  /-- The component on each member of the open cover. -/
  hom : ∀ i, A.localSheaf i ⟶ B.localSheaf i
  /-- Compatibility with the pairwise overlap identifications. -/
  comm : ∀ i j,
    ((TopCat.Sheaf.pullback (Type u)
      (openSubsetIntersectionLeftInclusion (U i) (U j))).map (hom i)) ≫
        (B.overlapIso i j).hom =
      (A.overlapIso i j).hom ≫
        ((TopCat.Sheaf.pullback (Type u)
          (openSubsetIntersectionRightInclusion (U i) (U j))).map (hom j))

/-- The identity morphism of open-cover gluing data. -/
def id (A : SheafOpenCoverGlueing U) : Hom A A where
  hom i := 𝟙 (A.localSheaf i)
  comm i j := by simp

/-- Morphisms of open-cover gluing data are determined by their local components. -/
@[ext] theorem hom_ext {A B : SheafOpenCoverGlueing U} {f g : Hom A B}
    (h : ∀ i, f.hom i = g.hom i) : f = g := by
  cases f with
  | mk fh fc =>
    cases g with
    | mk gh gc =>
      dsimp at h
      have hh : fh = gh := funext h
      cases hh
      have hc : fc = gc := Subsingleton.elim _ _
      cases hc
      rfl

/-- Composition of morphisms of open-cover gluing data. -/
def comp {A B C : SheafOpenCoverGlueing U} (f : Hom A B) (g : Hom B C) : Hom A C where
  hom i := f.hom i ≫ g.hom i
  comm i j := by
    simpa [Functor.map_comp, Category.assoc] using
      calc
        ((TopCat.Sheaf.pullback (Type u)
            (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i ≫ g.hom i)) ≫
            (C.overlapIso i j).hom
            =
              ((TopCat.Sheaf.pullback (Type u)
                  (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i)) ≫
                (((TopCat.Sheaf.pullback (Type u)
                    (openSubsetIntersectionLeftInclusion (U i) (U j))).map (g.hom i)) ≫
                  (C.overlapIso i j).hom) := by
                    simp [Functor.map_comp, Category.assoc]
        _ =
              ((TopCat.Sheaf.pullback (Type u)
                  (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i)) ≫
                ((B.overlapIso i j).hom ≫
                  ((TopCat.Sheaf.pullback (Type u)
                    (openSubsetIntersectionRightInclusion (U i) (U j))).map (g.hom j))) := by
                      rw [g.comm i j]
        _ =
              (((TopCat.Sheaf.pullback (Type u)
                  (openSubsetIntersectionLeftInclusion (U i) (U j))).map (f.hom i)) ≫
                (B.overlapIso i j).hom) ≫
                  ((TopCat.Sheaf.pullback (Type u)
                    (openSubsetIntersectionRightInclusion (U i) (U j))).map (g.hom j)) := by
                      simp [Category.assoc]
        _ =
              ((A.overlapIso i j).hom ≫
                ((TopCat.Sheaf.pullback (Type u)
                  (openSubsetIntersectionRightInclusion (U i) (U j))).map (f.hom j))) ≫
                    ((TopCat.Sheaf.pullback (Type u)
                      (openSubsetIntersectionRightInclusion (U i) (U j))).map (g.hom j)) := by
                        rw [f.comm i j]
        _ =
              (A.overlapIso i j).hom ≫
                (((TopCat.Sheaf.pullback (Type u)
                    (openSubsetIntersectionRightInclusion (U i) (U j))).map (f.hom j)) ≫
                  ((TopCat.Sheaf.pullback (Type u)
                    (openSubsetIntersectionRightInclusion (U i) (U j))).map (g.hom j))) := by
                      simp [Category.assoc]
        _ =
              (A.overlapIso i j).hom ≫
                ((TopCat.Sheaf.pullback (Type u)
                  (openSubsetIntersectionRightInclusion (U i) (U j))).map
                    (f.hom j ≫ g.hom j)) := by
                      simp [Functor.map_comp]

instance : Category (SheafOpenCoverGlueing U) where
  Hom A B := Hom A B
  id A := id A
  comp f g := comp f g
  id_comp f := by ext i; simp [id, comp]
  comp_id f := by ext i; simp [id, comp]
  assoc f g h := by ext i; simp [comp, Category.assoc]

public abbrev memberSheaf (U : ι → Opens X) (i : ι) :=
  (openSubsetSpace (U i)).Sheaf (Type u)

public abbrev overlapSheaf (U : ι → Opens X) (i j : ι) :=
  (openSubsetSpace (U i ⊓ U j)).Sheaf (Type u)

public abbrev tripleSheaf (U : ι → Opens X) (i j k : ι) :=
  (openSubsetSpace (U i ⊓ U j ⊓ U k)).Sheaf (Type u)

public abbrev restrictToMember (U : Opens X) :
    X.Sheaf (Type u) ⥤ (openSubsetSpace U).Sheaf (Type u) :=
  TopCat.Sheaf.pullback (Type u) (openSubsetInclusion U)

public abbrev restrictToOverlapLeft (U : ι → Opens X) (i j : ι) :
    memberSheaf U i ⥤ overlapSheaf U i j :=
  TopCat.Sheaf.pullback (Type u) (openSubsetIntersectionLeftInclusion (U i) (U j))

public abbrev restrictToOverlapRight (U : ι → Opens X) (i j : ι) :
    memberSheaf U j ⥤ overlapSheaf U i j :=
  TopCat.Sheaf.pullback (Type u) (openSubsetIntersectionRightInclusion (U i) (U j))

public abbrev restrictOverlapToTripleLeft (U : ι → Opens X) (i j k : ι) :
    overlapSheaf U i j ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))

public abbrev restrictOverlapToTripleCenter (U : ι → Opens X) (i j k : ι) :
    overlapSheaf U j k ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))

public abbrev restrictOverlapToTripleOuter (U : ι → Opens X) (i j k : ι) :
    overlapSheaf U i k ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))

public abbrev restrictToTripleFirst (U : ι → Opens X) (i j k : ι) :
    memberSheaf U i ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleFirstInclusion (U i) (U j) (U k))

public abbrev restrictToTripleSecond (U : ι → Opens X) (i j k : ι) :
    memberSheaf U j ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleSecondInclusion (U i) (U j) (U k))

public abbrev restrictToTripleThird (U : ι → Opens X) (i j k : ι) :
    memberSheaf U k ⥤ tripleSheaf U i j k :=
  TopCat.Sheaf.pullback (Type u) (openSubsetTripleThirdInclusion (U i) (U j) (U k))

@[simp] public theorem openSubsetIntersectionLeftInclusion_comp_inclusion
    (U V : Opens X) :
    openSubsetIntersectionLeftInclusion U V ≫ openSubsetInclusion U =
      openSubsetInclusion (U ⊓ V) :=
  rfl

@[simp] public theorem openSubsetIntersectionRightInclusion_comp_inclusion
    (U V : Opens X) :
    openSubsetIntersectionRightInclusion U V ≫ openSubsetInclusion V =
      openSubsetInclusion (U ⊓ V) :=
  rfl

@[simp] public theorem openSubsetTripleToPairLeft_comp_intersectionLeft
    (U V W : Opens X) :
    openSubsetTripleToPairLeftInclusion U V W ≫ openSubsetIntersectionLeftInclusion U V =
      openSubsetTripleFirstInclusion U V W :=
  rfl

@[simp] public theorem openSubsetTripleToPairLeft_comp_intersectionRight
    (U V W : Opens X) :
    openSubsetTripleToPairLeftInclusion U V W ≫ openSubsetIntersectionRightInclusion U V =
      openSubsetTripleSecondInclusion U V W :=
  rfl

@[simp] public theorem openSubsetTripleToPairCenter_comp_intersectionLeft
    (U V W : Opens X) :
    openSubsetTripleToPairCenterInclusion U V W ≫ openSubsetIntersectionLeftInclusion V W =
      openSubsetTripleSecondInclusion U V W :=
  rfl

@[simp] public theorem openSubsetTripleToPairCenter_comp_intersectionRight
    (U V W : Opens X) :
    openSubsetTripleToPairCenterInclusion U V W ≫ openSubsetIntersectionRightInclusion V W =
      openSubsetTripleThirdInclusion U V W :=
  rfl

@[simp] public theorem openSubsetTripleToPairOuter_comp_intersectionLeft
    (U V W : Opens X) :
    openSubsetTripleToPairOuterInclusion U V W ≫ openSubsetIntersectionLeftInclusion U W =
      openSubsetTripleFirstInclusion U V W :=
  rfl

@[simp] public theorem openSubsetTripleToPairOuter_comp_intersectionRight
    (U V W : Opens X) :
    openSubsetTripleToPairOuterInclusion U V W ≫ openSubsetIntersectionRightInclusion U W =
      openSubsetTripleThirdInclusion U V W :=
  rfl

public noncomputable def restrictToTripleFirstViaIJIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleFirst U i j k ≅
      restrictToOverlapLeft U i j ⋙ restrictOverlapToTripleLeft U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairLeft_comp_intersectionLeft (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U j))).symm

public noncomputable def restrictToTripleSecondViaIJIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleSecond U i j k ≅
      restrictToOverlapRight U i j ⋙ restrictOverlapToTripleLeft U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairLeft_comp_intersectionRight (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U j))).symm

public noncomputable def restrictToTripleSecondViaJKIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleSecond U i j k ≅
      restrictToOverlapLeft U j k ⋙ restrictOverlapToTripleCenter U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairCenter_comp_intersectionLeft (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U j) (U k))).symm

public noncomputable def restrictToTripleThirdViaJKIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleThird U i j k ≅
      restrictToOverlapRight U j k ⋙ restrictOverlapToTripleCenter U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairCenter_comp_intersectionRight (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U j) (U k))).symm

public noncomputable def restrictToTripleFirstViaIKIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleFirst U i j k ≅
      restrictToOverlapLeft U i k ⋙ restrictOverlapToTripleOuter U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairOuter_comp_intersectionLeft (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U k))).symm

public noncomputable def restrictToTripleThirdViaIKIso (U : ι → Opens X) (i j k : ι) :
    restrictToTripleThird U i j k ≅
      restrictToOverlapRight U i k ⋙ restrictOverlapToTripleOuter U i j k :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetTripleToPairOuter_comp_intersectionRight (U i) (U j) (U k)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U k))).symm

public noncomputable def pairIsoOnTriple12 (U : ι → Opens X) (i j k : ι)
    (A : memberSheaf U i) (B : memberSheaf U j)
    (e : (restrictToOverlapLeft U i j).obj A ≅ (restrictToOverlapRight U i j).obj B) :
    (restrictToTripleFirst U i j k).obj A ≅ (restrictToTripleSecond U i j k).obj B :=
  (restrictToTripleFirstViaIJIso U i j k).app A ≪≫
    (restrictOverlapToTripleLeft U i j k).mapIso e ≪≫
      ((restrictToTripleSecondViaIJIso U i j k).app B).symm

public noncomputable def pairIsoOnTriple23 (U : ι → Opens X) (i j k : ι)
    (A : memberSheaf U j) (B : memberSheaf U k)
    (e : (restrictToOverlapLeft U j k).obj A ≅ (restrictToOverlapRight U j k).obj B) :
    (restrictToTripleSecond U i j k).obj A ≅ (restrictToTripleThird U i j k).obj B :=
  (restrictToTripleSecondViaJKIso U i j k).app A ≪≫
    (restrictOverlapToTripleCenter U i j k).mapIso e ≪≫
      ((restrictToTripleThirdViaJKIso U i j k).app B).symm

public noncomputable def pairIsoOnTriple13 (U : ι → Opens X) (i j k : ι)
    (A : memberSheaf U i) (B : memberSheaf U k)
    (e : (restrictToOverlapLeft U i k).obj A ≅ (restrictToOverlapRight U i k).obj B) :
    (restrictToTripleFirst U i j k).obj A ≅ (restrictToTripleThird U i j k).obj B :=
  (restrictToTripleFirstViaIKIso U i j k).app A ≪≫
    (restrictOverlapToTripleOuter U i j k).mapIso e ≪≫
      ((restrictToTripleThirdViaIKIso U i j k).app B).symm

noncomputable def globalRestrictionToPairViaLeftIso (U : ι → Opens X) (i j : ι) :
    restrictToMember (U i ⊓ U j) ≅
      restrictToMember (U i) ⋙ restrictToOverlapLeft U i j :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetIntersectionLeftInclusion_comp_inclusion (U i) (U j)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetIntersectionLeftInclusion (U i) (U j))
      (openSubsetInclusion (U i))).symm

noncomputable def globalRestrictionToPairViaRightIso (U : ι → Opens X) (i j : ι) :
    restrictToMember (U i ⊓ U j) ≅
      restrictToMember (U j) ⋙ restrictToOverlapRight U i j :=
  eqToIso (congrArg (TopCat.Sheaf.pullback (Type u))
      (openSubsetIntersectionRightInclusion_comp_inclusion (U i) (U j)).symm) ≪≫
    (TopCat.Sheaf.pullbackComp
      (openSubsetIntersectionRightInclusion (U i) (U j))
      (openSubsetInclusion (U j))).symm

noncomputable def overlapIsoOfSheaf (U : ι → Opens X) (i j : ι)
    (F : X.Sheaf (Type u)) :
    (restrictToOverlapLeft U i j).obj ((restrictToMember (U i)).obj F) ≅
      (restrictToOverlapRight U i j).obj ((restrictToMember (U j)).obj F) :=
  ((globalRestrictionToPairViaLeftIso U i j).app F).symm ≪≫
    (globalRestrictionToPairViaRightIso U i j).app F

/-- Helper for Glueing data for sheaves on an open cover: `TopCat.Sheaf.pullbackComp` is the
left-adjoint comparison isomorphism for the definitional equality of pushforward functors. -/
private theorem sheafPullbackComp_def {W Y Z : TopCat.{u}} (f : W ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullbackComp f g =
      Adjunction.leftAdjointCompIso
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g))
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g =
            TopCat.Sheaf.pushforward (Type u) (f ≫ g) from rfl)) := by
  rfl

/-- Helper for Glueing data for sheaves on an open cover: the canonical pullback-composition
comparisons satisfy the standard pseudofunctor associativity identity. -/
private theorem sheaf_pushforward_assoc {W Y Z T : TopCat.{u}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type u) f)
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type u) g ⋙ TopCat.Sheaf.pushforward (Type u) h =
            TopCat.Sheaf.pushforward (Type u) (g ≫ h) from rfl)) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type u) f ⋙
            TopCat.Sheaf.pushforward (Type u) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl) =
    (Functor.associator
      (TopCat.Sheaf.pushforward (Type u) f)
      (TopCat.Sheaf.pushforward (Type u) g)
      (TopCat.Sheaf.pushforward (Type u) h)).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g =
            TopCat.Sheaf.pushforward (Type u) (f ≫ g) from rfl))
        (TopCat.Sheaf.pushforward (Type u) h) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type u) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type u) h =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl) := by
  -- Evaluate the functor-level coherence componentwise; both sides are definitionally the same.
  ext ℱ
  rfl

/-- Helper for Glueing data for sheaves on an open cover: the pullback-composition isomorphisms
inherit the associativity coherence from the left-adjoint comparison. -/
private theorem sheaf_pullback_comp_assoc {W Y Z T : TopCat.{u}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft _ (TopCat.Sheaf.pullbackComp (A := Type u) f g) ≪≫
      TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (TopCat.Sheaf.pullbackComp (A := Type u) g h) _ ≪≫
        TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h) := by
  -- This is the owner-level associativity coherence for left adjoints to the same composite
  -- pushforward functor.
  simpa [sheafPullbackComp_def] using
    (Adjunction.leftAdjointCompIso_assoc
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) h)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (g ≫ h))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g ≫ h))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) g ⋙ TopCat.Sheaf.pushforward (Type u) h =
          TopCat.Sheaf.pushforward (Type u) (g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type u) h =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) f ⋙
            TopCat.Sheaf.pushforward (Type u) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl))
      (sheaf_pushforward_assoc f g h))

/-- Helper for Glueing data for sheaves on an open cover: the canonical pullback-composition
comparisons satisfy the standard pseudofunctor associativity identity. -/
private theorem sheaf_pullback_pseudofunctor_associativity {W Y Z T : TopCat.{u}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).inv ≫
        (Functor.isoWhiskerRight
          (TopCat.Sheaf.pullbackComp (A := Type u) g h)
          (TopCat.Sheaf.pullback (Type u) f)).inv ≫
        (Functor.associator _ _ _).hom ≫
        (Functor.isoWhiskerLeft
          (TopCat.Sheaf.pullback (Type u) h)
          (TopCat.Sheaf.pullbackComp (A := Type u) f g)).hom ≫
        (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom =
      eqToHom (by simp) := by
  -- Package the owner-level associativity coherence in the hom form used by the cocycle proof.
  let e₁ := TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight
    (TopCat.Sheaf.pullbackComp (A := Type u) g h)
    (TopCat.Sheaf.pullback (Type u) f)
  let e₃ := Functor.isoWhiskerLeft
    (TopCat.Sheaf.pullback (Type u) h)
    (TopCat.Sheaf.pullbackComp (A := Type u) f g)
  let e₄ := TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have hcomp : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom := by
    -- Reuse the standard owner-side coherence for left adjoints to composite pushforwards.
    exact congrArg Iso.hom (sheaf_pullback_comp_assoc f g h)
  rw [hcomp]
  ext X
  simpa [Category.assoc] using Iso.inv_hom_id_app (e₂.trans e₁) X

/-- Helper for Glueing data for sheaves on an open cover: cancelling the left comparison in the
forward pullback-composition coherence identifies the endpoint with the direct restriction map. -/
private theorem sheaf_pullback_forward_endpoint {W Y Z T : TopCat.{u}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (F : T.Sheaf (Type u)) :
    (TopCat.Sheaf.pullbackComp (A := Type u) f g).inv.app
        ((TopCat.Sheaf.pullback (Type u) h).obj F) ≫
      (TopCat.Sheaf.pullback (Type u) f).map
        ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app F) ≫
      (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app F =
    (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app F := by
  -- Route correction: use the forward hom component of `sheaf_pullback_comp_assoc`, then cancel
  -- the left comparison isomorphism instead of manually reversing the coherence.
  apply (cancel_epi ((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
    ((TopCat.Sheaf.pullback (Type u) h).obj F))).1
  -- After precomposing with the direct comparison, the goal is exactly the specialized forward
  -- associativity identity.
  have hcancel :
      (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
            ((TopCat.Sheaf.pullback (Type u) h).obj F) ≫
          ((TopCat.Sheaf.pullbackComp (A := Type u) f g).inv.app
            ((TopCat.Sheaf.pullback (Type u) h).obj F) ≫
            (TopCat.Sheaf.pullback (Type u) f).map
              ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app F) =
        (TopCat.Sheaf.pullback (Type u) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app F := by
    simpa [Category.assoc] using
      (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom_inv_id_app_assoc
        ((TopCat.Sheaf.pullback (Type u) h).obj F)
        ((TopCat.Sheaf.pullback (Type u) f).map
          ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app F)
  have hassoc :
      (TopCat.Sheaf.pullback (Type u) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app F =
        (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
            ((TopCat.Sheaf.pullback (Type u) h).obj F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app F := by
    simpa [Category.assoc] using
      (congrArg (fun α ↦ α.hom.app F) (sheaf_pullback_comp_assoc f g h)).symm
  exact hcancel.trans hassoc

/-- Helper for Glueing data for sheaves on an open cover: cancelling the terminal direct
restriction in the inverse pullback-composition coherence yields the inverse endpoint map. -/
private theorem sheaf_pullback_inverse_endpoint {W Y Z T : TopCat.{u}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (F : T.Sheaf (Type u)) :
    (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).inv.app F ≫
      (TopCat.Sheaf.pullback (Type u) f).map
        ((TopCat.Sheaf.pullbackComp (A := Type u) g h).inv.app F) ≫
      (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
        ((TopCat.Sheaf.pullback (Type u) h).obj F) =
      (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).inv.app F := by
  -- Route correction: use the inverse-form coherence once and cancel the final direct restriction.
  apply (cancel_mono ((TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app F)).1
  -- Postcomposing with the direct restriction turns the goal into the normalized coherence path.
  have hcoh :
      (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).inv.app F ≫
          (TopCat.Sheaf.pullback (Type u) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type u) g h).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
            ((TopCat.Sheaf.pullback (Type u) h).obj F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app F =
        eqToHom (by simp) := by
    simpa [Category.assoc] using
      congrArg (fun α ↦ α.app F) (sheaf_pullback_pseudofunctor_associativity f g h)
  have hid :
      eqToHom (by simp) =
        (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).inv.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app F := by
    simpa using
      (Iso.inv_hom_id_app (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h) F).symm
  exact hcoh.trans hid

/-- Helper for Glueing data for sheaves on an open cover: the `i`-endpoint of the `(i,j)` path on
the triple overlap is the direct restriction from `F|_{U i}` to `F|_{U i ⊓ U j ⊓ U k}`. -/
private theorem triple_first_via_left_overlap_to_direct
    (U : ι → Opens X) (F : X.Sheaf (Type u)) (i j k : ι) :
    (restrictToTripleFirstViaIJIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
        (restrictOverlapToTripleLeft U i j k).map
          ((globalRestrictionToPairViaLeftIso U i j).inv.app F) ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U i ⊓ U j))).hom.app F =
      (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U i))).hom.app F := by
  -- Route correction: the first endpoint is the forward specialization of pullback pseudofunctor
  -- coherence, so normalize it directly instead of reversing the identity by hand.
  simpa [restrictToTripleFirstViaIJIso, globalRestrictionToPairViaLeftIso] using
    sheaf_pullback_forward_endpoint
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U j))
      (openSubsetInclusion (U i)) F

/-- Helper for Glueing data for sheaves on an open cover: the `j`-segment coming from the
`(i,j)` overlap is the direct restriction from the triple overlap into `U j`. -/
private theorem triple_second_via_left_overlap_to_direct
    (U : ι → Opens X) (F : X.Sheaf (Type u)) (i j k : ι) :
    (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U i ⊓ U j))).inv.app F ≫
      (restrictOverlapToTripleLeft U i j k).map
        ((globalRestrictionToPairViaRightIso U i j).hom.app F) ≫
      ((restrictToTripleSecondViaIJIso U i j k).app ((restrictToMember (U j)).obj F)).symm.hom =
    (TopCat.Sheaf.pullbackComp (A := Type u)
      (openSubsetTripleSecondInclusion (U i) (U j) (U k))
      (openSubsetInclusion (U j))).inv.app F := by
  -- The right half of the `(i,j)` path is the inverse endpoint specialization of the same
  -- pullback coherence, now along the inclusion into `U j`.
  simpa [restrictToTripleSecondViaIJIso, globalRestrictionToPairViaRightIso] using
    sheaf_pullback_inverse_endpoint
      (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U j))
      (openSubsetInclusion (U j)) F

/-- Helper for Glueing data for sheaves on an open cover: the `j`-segment coming from the
`(j,k)` overlap is the same direct restriction from `F|_{U j}` to the triple overlap. -/
private theorem triple_second_via_center_overlap_to_direct
    (U : ι → Opens X) (F : X.Sheaf (Type u)) (i j k : ι) :
    (restrictToTripleSecondViaJKIso U i j k).hom.app ((restrictToMember (U j)).obj F) ≫
        (restrictOverlapToTripleCenter U i j k).map
          ((globalRestrictionToPairViaLeftIso U j k).inv.app F) ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U j ⊓ U k))).hom.app F =
      (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleSecondInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U j))).hom.app F := by
  -- This is the forward endpoint specialization for the center overlap factorization into `U j`.
  simpa [restrictToTripleSecondViaJKIso, globalRestrictionToPairViaLeftIso] using
    sheaf_pullback_forward_endpoint
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U j) (U k))
      (openSubsetInclusion (U j)) F

/-- Helper for Glueing data for sheaves on an open cover: the `k`-segment coming from the
`(j,k)` overlap is the direct restriction from the triple overlap into `U k`. -/
private theorem triple_third_via_center_overlap_to_direct
    (U : ι → Opens X) (F : X.Sheaf (Type u)) (i j k : ι) :
    (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U j ⊓ U k))).inv.app F ≫
      (restrictOverlapToTripleCenter U i j k).map
        ((globalRestrictionToPairViaRightIso U j k).hom.app F) ≫
      ((restrictToTripleThirdViaJKIso U i j k).app ((restrictToMember (U k)).obj F)).symm.hom =
    (TopCat.Sheaf.pullbackComp (A := Type u)
      (openSubsetTripleThirdInclusion (U i) (U j) (U k))
      (openSubsetInclusion (U k))).inv.app F := by
  -- The right half of the center path is again the inverse endpoint specialization.
  simpa [restrictToTripleThirdViaJKIso, globalRestrictionToPairViaRightIso] using
    sheaf_pullback_inverse_endpoint
      (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U j) (U k))
      (openSubsetInclusion (U k)) F

/-- Helper for Glueing data for sheaves on an open cover: the `i`-endpoint of the `(i,k)` path on
the triple overlap is the same direct restriction from `F|_{U i}` to the triple overlap. -/
private theorem triple_first_via_outer_overlap_to_direct
    (U : ι → Opens X) (F : X.Sheaf (Type u)) (i j k : ι) :
    (restrictToTripleFirstViaIKIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
        (restrictOverlapToTripleOuter U i j k).map
          ((globalRestrictionToPairViaLeftIso U i k).inv.app F) ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U i ⊓ U k))).hom.app F =
      (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U i))).hom.app F := by
  -- The outer `(i,k)` endpoint follows the same forward comparison pattern as the `(i,j)` one.
  simpa [restrictToTripleFirstViaIKIso, globalRestrictionToPairViaLeftIso] using
    sheaf_pullback_forward_endpoint
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionLeftInclusion (U i) (U k))
      (openSubsetInclusion (U i)) F

/-- Helper for Glueing data for sheaves on an open cover: the `k`-endpoint of the `(i,k)` path on
the triple overlap is the same direct restriction into `U k`. -/
private theorem triple_third_via_outer_overlap_to_direct
    (U : ι → Opens X) (F : X.Sheaf (Type u)) (i j k : ι) :
    (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U i ⊓ U k))).inv.app F ≫
      (restrictOverlapToTripleOuter U i j k).map
        ((globalRestrictionToPairViaRightIso U i k).hom.app F) ≫
      ((restrictToTripleThirdViaIKIso U i j k).app ((restrictToMember (U k)).obj F)).symm.hom =
    (TopCat.Sheaf.pullbackComp (A := Type u)
      (openSubsetTripleThirdInclusion (U i) (U j) (U k))
      (openSubsetInclusion (U k))).inv.app F := by
  -- The outer right endpoint is the inverse counterpart of the same coherence specialization.
  simpa [restrictToTripleThirdViaIKIso, globalRestrictionToPairViaRightIso] using
    sheaf_pullback_inverse_endpoint
      (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
      (openSubsetIntersectionRightInclusion (U i) (U k))
      (openSubsetInclusion (U k)) F

/-- Helper for Glueing data for sheaves on an open cover: the `(i,j)` comparison induced from a
global sheaf is already the direct restriction from `U i` to `U j` on the triple overlap. -/
private theorem pairIsoOnTriple12_ofSheaf_direct_normal_form
    (U : ι → Opens X) (F : X.Sheaf (Type u)) (i j k : ι) :
    (pairIsoOnTriple12 U i j k
      ((restrictToMember (U i)).obj F)
      ((restrictToMember (U j)).obj F)
      (overlapIsoOfSheaf U i j F)).hom =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleFirstInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U i))).hom.app F ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleSecondInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U j))).inv.app F := by
  -- Unfold the `(i,j)` path once so the overlap isomorphism splits into its left and right legs.
  have hsplit :
      (pairIsoOnTriple12 U i j k
        ((restrictToMember (U i)).obj F)
        ((restrictToMember (U j)).obj F)
        (overlapIsoOfSheaf U i j F)).hom =
          (restrictToTripleFirstViaIJIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
            (restrictOverlapToTripleLeft U i j k).map
              ((globalRestrictionToPairViaLeftIso U i j).inv.app F) ≫
            (restrictOverlapToTripleLeft U i j k).map
              ((globalRestrictionToPairViaRightIso U i j).hom.app F) ≫
            ((restrictToTripleSecondViaIJIso U i j k).app
              ((restrictToMember (U j)).obj F)).symm.hom := by
    simp [pairIsoOnTriple12, overlapIsoOfSheaf]
  have hinsert :
      (restrictToTripleFirstViaIJIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
          (restrictOverlapToTripleLeft U i j k).map
            ((globalRestrictionToPairViaLeftIso U i j).inv.app F) ≫
          (restrictOverlapToTripleLeft U i j k).map
            ((globalRestrictionToPairViaRightIso U i j).hom.app F) ≫
          ((restrictToTripleSecondViaIJIso U i j k).app
            ((restrictToMember (U j)).obj F)).symm.hom =
        (restrictToTripleFirstViaIJIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
          (restrictOverlapToTripleLeft U i j k).map
            ((globalRestrictionToPairViaLeftIso U i j).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U j))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U j))).inv.app F ≫
          (restrictOverlapToTripleLeft U i j k).map
            ((globalRestrictionToPairViaRightIso U i j).hom.app F) ≫
          ((restrictToTripleSecondViaIJIso U i j k).app
            ((restrictToMember (U j)).obj F)).symm.hom := by
    -- Insert the pair-level identity so the left and right endpoint normalizations can fire.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (restrictToTripleFirstViaIJIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
            (restrictOverlapToTripleLeft U i j k).map
              ((globalRestrictionToPairViaLeftIso U i j).inv.app F) ≫
            t ≫
            (restrictOverlapToTripleLeft U i j k).map
              ((globalRestrictionToPairViaRightIso U i j).hom.app F) ≫
            ((restrictToTripleSecondViaIJIso U i j k).app
              ((restrictToMember (U j)).obj F)).symm.hom)
        (Iso.hom_inv_id_app
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U j))) F).symm
  have hleft :
      (restrictToTripleFirstViaIJIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
          (restrictOverlapToTripleLeft U i j k).map
            ((globalRestrictionToPairViaLeftIso U i j).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U j))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U j))).inv.app F ≫
          (restrictOverlapToTripleLeft U i j k).map
            ((globalRestrictionToPairViaRightIso U i j).hom.app F) ≫
          ((restrictToTripleSecondViaIJIso U i j k).app
            ((restrictToMember (U j)).obj F)).symm.hom =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleFirstInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U i))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U j))).inv.app F ≫
          (restrictOverlapToTripleLeft U i j k).map
            ((globalRestrictionToPairViaRightIso U i j).hom.app F) ≫
          ((restrictToTripleSecondViaIJIso U i j k).app
            ((restrictToMember (U j)).obj F)).symm.hom := by
    -- The left endpoint is exactly the direct restriction through `U i`.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          t ≫
            (TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
              (openSubsetInclusion (U i ⊓ U j))).inv.app F ≫
            (restrictOverlapToTripleLeft U i j k).map
              ((globalRestrictionToPairViaRightIso U i j).hom.app F) ≫
            ((restrictToTripleSecondViaIJIso U i j k).app
              ((restrictToMember (U j)).obj F)).symm.hom)
        (triple_first_via_left_overlap_to_direct U F i j k)
  have hright :
      (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U i))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U j))).inv.app F ≫
          (restrictOverlapToTripleLeft U i j k).map
            ((globalRestrictionToPairViaRightIso U i j).hom.app F) ≫
          ((restrictToTripleSecondViaIJIso U i j k).app
            ((restrictToMember (U j)).obj F)).symm.hom =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleFirstInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U i))).hom.app F ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleSecondInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U j))).inv.app F := by
    -- The right endpoint is the same direct restriction through `U j`.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleFirstInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i))).hom.app F ≫ t)
        (triple_second_via_left_overlap_to_direct U F i j k)
  exact hsplit.trans (hinsert.trans (hleft.trans hright))

/-- Helper for Glueing data for sheaves on an open cover: the `(j,k)` comparison induced from a
global sheaf is the direct restriction from `U j` to `U k` on the triple overlap. -/
private theorem pairIsoOnTriple23_ofSheaf_direct_normal_form
    (U : ι → Opens X) (F : X.Sheaf (Type u)) (i j k : ι) :
    (pairIsoOnTriple23 U i j k
      ((restrictToMember (U j)).obj F)
      ((restrictToMember (U k)).obj F)
      (overlapIsoOfSheaf U j k F)).hom =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleSecondInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U j))).hom.app F ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleThirdInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U k))).inv.app F := by
  -- Unfold the center path once so the overlap isomorphism splits into two mapped components.
  have hsplit :
      (pairIsoOnTriple23 U i j k
        ((restrictToMember (U j)).obj F)
        ((restrictToMember (U k)).obj F)
        (overlapIsoOfSheaf U j k F)).hom =
          (restrictToTripleSecondViaJKIso U i j k).hom.app ((restrictToMember (U j)).obj F) ≫
            (restrictOverlapToTripleCenter U i j k).map
              ((globalRestrictionToPairViaLeftIso U j k).inv.app F) ≫
            (restrictOverlapToTripleCenter U i j k).map
              ((globalRestrictionToPairViaRightIso U j k).hom.app F) ≫
            ((restrictToTripleThirdViaJKIso U i j k).app
              ((restrictToMember (U k)).obj F)).symm.hom := by
    simp [pairIsoOnTriple23, overlapIsoOfSheaf]
  have hinsert :
      (restrictToTripleSecondViaJKIso U i j k).hom.app ((restrictToMember (U j)).obj F) ≫
          (restrictOverlapToTripleCenter U i j k).map
            ((globalRestrictionToPairViaLeftIso U j k).inv.app F) ≫
          (restrictOverlapToTripleCenter U i j k).map
            ((globalRestrictionToPairViaRightIso U j k).hom.app F) ≫
          ((restrictToTripleThirdViaJKIso U i j k).app
            ((restrictToMember (U k)).obj F)).symm.hom =
        (restrictToTripleSecondViaJKIso U i j k).hom.app ((restrictToMember (U j)).obj F) ≫
          (restrictOverlapToTripleCenter U i j k).map
            ((globalRestrictionToPairViaLeftIso U j k).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U j ⊓ U k))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U j ⊓ U k))).inv.app F ≫
          (restrictOverlapToTripleCenter U i j k).map
            ((globalRestrictionToPairViaRightIso U j k).hom.app F) ≫
          ((restrictToTripleThirdViaJKIso U i j k).app
            ((restrictToMember (U k)).obj F)).symm.hom := by
    -- Insert the center pair identity so the two endpoint normalizations align.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (restrictToTripleSecondViaJKIso U i j k).hom.app ((restrictToMember (U j)).obj F) ≫
            (restrictOverlapToTripleCenter U i j k).map
              ((globalRestrictionToPairViaLeftIso U j k).inv.app F) ≫
            t ≫
            (restrictOverlapToTripleCenter U i j k).map
              ((globalRestrictionToPairViaRightIso U j k).hom.app F) ≫
            ((restrictToTripleThirdViaJKIso U i j k).app
              ((restrictToMember (U k)).obj F)).symm.hom)
        (Iso.hom_inv_id_app
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U j ⊓ U k))) F).symm
  have hleft :
      (restrictToTripleSecondViaJKIso U i j k).hom.app ((restrictToMember (U j)).obj F) ≫
          (restrictOverlapToTripleCenter U i j k).map
            ((globalRestrictionToPairViaLeftIso U j k).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U j ⊓ U k))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U j ⊓ U k))).inv.app F ≫
          (restrictOverlapToTripleCenter U i j k).map
            ((globalRestrictionToPairViaRightIso U j k).hom.app F) ≫
          ((restrictToTripleThirdViaJKIso U i j k).app
            ((restrictToMember (U k)).obj F)).symm.hom =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleSecondInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U j))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U j ⊓ U k))).inv.app F ≫
          (restrictOverlapToTripleCenter U i j k).map
            ((globalRestrictionToPairViaRightIso U j k).hom.app F) ≫
          ((restrictToTripleThirdViaJKIso U i j k).app
            ((restrictToMember (U k)).obj F)).symm.hom := by
    -- The left half is the direct restriction through `U j`.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          t ≫
            (TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
              (openSubsetInclusion (U j ⊓ U k))).inv.app F ≫
            (restrictOverlapToTripleCenter U i j k).map
              ((globalRestrictionToPairViaRightIso U j k).hom.app F) ≫
            ((restrictToTripleThirdViaJKIso U i j k).app
              ((restrictToMember (U k)).obj F)).symm.hom)
        (triple_second_via_center_overlap_to_direct U F i j k)
  have hright :
      (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleSecondInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U j))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U j ⊓ U k))).inv.app F ≫
          (restrictOverlapToTripleCenter U i j k).map
            ((globalRestrictionToPairViaRightIso U j k).hom.app F) ≫
          ((restrictToTripleThirdViaJKIso U i j k).app
            ((restrictToMember (U k)).obj F)).symm.hom =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleSecondInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U j))).hom.app F ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleThirdInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U k))).inv.app F := by
    -- The right half is the direct restriction into `U k`.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleSecondInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U j))).hom.app F ≫ t)
        (triple_third_via_center_overlap_to_direct U F i j k)
  exact hsplit.trans (hinsert.trans (hleft.trans hright))

/-- Helper for Glueing data for sheaves on an open cover: the `(i,k)` comparison induced from a
global sheaf is the direct restriction from `U i` to `U k` on the triple overlap. -/
private theorem pairIsoOnTriple13_ofSheaf_direct_normal_form
    (U : ι → Opens X) (F : X.Sheaf (Type u)) (i j k : ι) :
    (pairIsoOnTriple13 U i j k
      ((restrictToMember (U i)).obj F)
      ((restrictToMember (U k)).obj F)
      (overlapIsoOfSheaf U i k F)).hom =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleFirstInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U i))).hom.app F ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleThirdInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U k))).inv.app F := by
  -- Unfold the outer path once so the overlap isomorphism splits into its two mapped legs.
  have hsplit :
      (pairIsoOnTriple13 U i j k
        ((restrictToMember (U i)).obj F)
        ((restrictToMember (U k)).obj F)
        (overlapIsoOfSheaf U i k F)).hom =
          (restrictToTripleFirstViaIKIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
            (restrictOverlapToTripleOuter U i j k).map
              ((globalRestrictionToPairViaLeftIso U i k).inv.app F) ≫
            (restrictOverlapToTripleOuter U i j k).map
              ((globalRestrictionToPairViaRightIso U i k).hom.app F) ≫
            ((restrictToTripleThirdViaIKIso U i j k).app
              ((restrictToMember (U k)).obj F)).symm.hom := by
    simp [pairIsoOnTriple13, overlapIsoOfSheaf]
  have hinsert :
      (restrictToTripleFirstViaIKIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
          (restrictOverlapToTripleOuter U i j k).map
            ((globalRestrictionToPairViaLeftIso U i k).inv.app F) ≫
          (restrictOverlapToTripleOuter U i j k).map
            ((globalRestrictionToPairViaRightIso U i k).hom.app F) ≫
          ((restrictToTripleThirdViaIKIso U i j k).app
            ((restrictToMember (U k)).obj F)).symm.hom =
        (restrictToTripleFirstViaIKIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
          (restrictOverlapToTripleOuter U i j k).map
            ((globalRestrictionToPairViaLeftIso U i k).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U k))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U k))).inv.app F ≫
          (restrictOverlapToTripleOuter U i j k).map
            ((globalRestrictionToPairViaRightIso U i k).hom.app F) ≫
          ((restrictToTripleThirdViaIKIso U i j k).app
            ((restrictToMember (U k)).obj F)).symm.hom := by
    -- Insert the outer pair identity so the endpoint lemmas apply to each half.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (restrictToTripleFirstViaIKIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
            (restrictOverlapToTripleOuter U i j k).map
              ((globalRestrictionToPairViaLeftIso U i k).inv.app F) ≫
            t ≫
            (restrictOverlapToTripleOuter U i j k).map
              ((globalRestrictionToPairViaRightIso U i k).hom.app F) ≫
            ((restrictToTripleThirdViaIKIso U i j k).app
              ((restrictToMember (U k)).obj F)).symm.hom)
        (Iso.hom_inv_id_app
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U k))) F).symm
  have hleft :
      (restrictToTripleFirstViaIKIso U i j k).hom.app ((restrictToMember (U i)).obj F) ≫
          (restrictOverlapToTripleOuter U i j k).map
            ((globalRestrictionToPairViaLeftIso U i k).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U k))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U k))).inv.app F ≫
          (restrictOverlapToTripleOuter U i j k).map
            ((globalRestrictionToPairViaRightIso U i k).hom.app F) ≫
          ((restrictToTripleThirdViaIKIso U i j k).app
            ((restrictToMember (U k)).obj F)).symm.hom =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleFirstInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U i))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U k))).inv.app F ≫
          (restrictOverlapToTripleOuter U i j k).map
            ((globalRestrictionToPairViaRightIso U i k).hom.app F) ≫
          ((restrictToTripleThirdViaIKIso U i j k).app
            ((restrictToMember (U k)).obj F)).symm.hom := by
    -- The left half is the direct restriction through `U i`.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          t ≫
            (TopCat.Sheaf.pullbackComp (A := Type u)
              (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
              (openSubsetInclusion (U i ⊓ U k))).inv.app F ≫
            (restrictOverlapToTripleOuter U i j k).map
              ((globalRestrictionToPairViaRightIso U i k).hom.app F) ≫
            ((restrictToTripleThirdViaIKIso U i j k).app
              ((restrictToMember (U k)).obj F)).symm.hom)
        (triple_first_via_outer_overlap_to_direct U F i j k)
  have hright :
      (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U i))).hom.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i ⊓ U k))).inv.app F ≫
          (restrictOverlapToTripleOuter U i j k).map
            ((globalRestrictionToPairViaRightIso U i k).hom.app F) ≫
          ((restrictToTripleThirdViaIKIso U i j k).app
            ((restrictToMember (U k)).obj F)).symm.hom =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleFirstInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U i))).hom.app F ≫
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleThirdInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U k))).inv.app F := by
    -- The right half is the direct restriction into `U k`.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleFirstInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i))).hom.app F ≫ t)
        (triple_third_via_outer_overlap_to_direct U F i j k)
  exact hsplit.trans (hinsert.trans (hleft.trans hright))

public theorem ofSheaf_cocycle (U : ι → Opens X) (F : X.Sheaf (Type u)) :
    ∀ i j k,
      (pairIsoOnTriple12 U i j k
        ((restrictToMember (U i)).obj F)
        ((restrictToMember (U j)).obj F)
        (overlapIsoOfSheaf U i j F)).hom ≫
        (pairIsoOnTriple23 U i j k
          ((restrictToMember (U j)).obj F)
          ((restrictToMember (U k)).obj F)
          (overlapIsoOfSheaf U j k F)).hom =
            (pairIsoOnTriple13 U i j k
              ((restrictToMember (U i)).obj F)
              ((restrictToMember (U k)).obj F)
              (overlapIsoOfSheaf U i k F)).hom := by
  intro i j k
  let directSecond := TopCat.Sheaf.pullbackComp (A := Type u)
    (openSubsetTripleSecondInclusion (U i) (U j) (U k))
    (openSubsetInclusion (U j))
  let directThird := TopCat.Sheaf.pullbackComp (A := Type u)
    (openSubsetTripleThirdInclusion (U i) (U j) (U k))
    (openSubsetInclusion (U k))
  -- Route correction: all three overlap comparisons induced from `F` are the same direct
  -- restriction to `U i ⊓ U j ⊓ U k`, so rewrite to those normal forms and cancel the middle leg.
  have hrewrite :
      (pairIsoOnTriple12 U i j k
        ((restrictToMember (U i)).obj F)
        ((restrictToMember (U j)).obj F)
        (overlapIsoOfSheaf U i j F)).hom ≫
          (pairIsoOnTriple23 U i j k
            ((restrictToMember (U j)).obj F)
            ((restrictToMember (U k)).obj F)
            (overlapIsoOfSheaf U j k F)).hom =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleFirstInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U i))).hom.app F ≫
          directSecond.inv.app F ≫ directSecond.hom.app F ≫ directThird.inv.app F := by
    rw [pairIsoOnTriple12_ofSheaf_direct_normal_form,
      pairIsoOnTriple23_ofSheaf_direct_normal_form]
    simp [directSecond, directThird, Category.assoc]
  have hcancel :
      (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U i))).hom.app F ≫
          directSecond.inv.app F ≫ directSecond.hom.app F ≫ directThird.inv.app F =
        (TopCat.Sheaf.pullbackComp (A := Type u)
          (openSubsetTripleFirstInclusion (U i) (U j) (U k))
          (openSubsetInclusion (U i))).hom.app F ≫
          directThird.inv.app F := by
    -- The two normal forms differ only by the direct restriction through `U j`, which cancels.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (TopCat.Sheaf.pullbackComp (A := Type u)
            (openSubsetTripleFirstInclusion (U i) (U j) (U k))
            (openSubsetInclusion (U i))).hom.app F ≫ t)
        (directSecond.inv_hom_id_app_assoc F (directThird.inv.app F))
  have htarget :
      (TopCat.Sheaf.pullbackComp (A := Type u)
        (openSubsetTripleFirstInclusion (U i) (U j) (U k))
        (openSubsetInclusion (U i))).hom.app F ≫
          directThird.inv.app F =
        (pairIsoOnTriple13 U i j k
          ((restrictToMember (U i)).obj F)
          ((restrictToMember (U k)).obj F)
          (overlapIsoOfSheaf U i k F)).hom := by
    rw [pairIsoOnTriple13_ofSheaf_direct_normal_form]
  exact hrewrite.trans (hcancel.trans htarget)

/-- The canonical gluing datum obtained by restricting a sheaf on `X` to the members of an open
cover `U`. -/
def ofSheaf (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) (F : X.Sheaf (Type u)) :
    SheafOpenCoverGlueing U where
  localSheaf i := (restrictToMember (U i)).obj F
  overlapIso i j := overlapIsoOfSheaf U i j F
  cocycle := ofSheaf_cocycle U F
  isCover := hU

theorem ofSheaf_map_comm
    (U : ι → Opens X) {F G : X.Sheaf (Type u)} (α : F ⟶ G) :
    ∀ i j,
      (restrictToOverlapLeft U i j).map ((restrictToMember (U i)).map α) ≫
        (overlapIsoOfSheaf U i j G).hom =
          (overlapIsoOfSheaf U i j F).hom ≫
            (restrictToOverlapRight U i j).map ((restrictToMember (U j)).map α) := by
  intro i j
  -- Unfold the overlap comparison and move the morphism across the left comparison isomorphism.
  simpa [Functor.comp_map, overlapIsoOfSheaf, globalRestrictionToPairViaLeftIso,
    globalRestrictionToPairViaRightIso, Category.assoc] using
    calc
      ((restrictToMember (U i) ⋙ restrictToOverlapLeft U i j).map α) ≫
          (globalRestrictionToPairViaLeftIso U i j).inv.app G ≫
          (globalRestrictionToPairViaRightIso U i j).hom.app G
          =
            ((globalRestrictionToPairViaLeftIso U i j).inv.app F ≫
              (restrictToMember (U i ⊓ U j)).map α) ≫
              (globalRestrictionToPairViaRightIso U i j).hom.app G := by
                rw [Category.assoc, (globalRestrictionToPairViaLeftIso U i j).inv.naturality_assoc]
      _ =
            (globalRestrictionToPairViaLeftIso U i j).inv.app F ≫
              ((restrictToMember (U i ⊓ U j)).map α ≫
                (globalRestrictionToPairViaRightIso U i j).hom.app G) := by
                  simp [Category.assoc]
      _ =
            (globalRestrictionToPairViaLeftIso U i j).inv.app F ≫
              ((globalRestrictionToPairViaRightIso U i j).hom.app F ≫
                ((restrictToMember (U j) ⋙ restrictToOverlapRight U i j).map α)) := by
                  rw [(globalRestrictionToPairViaRightIso U i j).hom.naturality]
      _ =
            (globalRestrictionToPairViaLeftIso U i j).inv.app F ≫
              (globalRestrictionToPairViaRightIso U i j).hom.app F ≫
                ((restrictToMember (U j) ⋙ restrictToOverlapRight U i j).map α) := by
                  simp

/-- The restriction functor from sheaves on `X` to gluing data on the open cover `U`. -/
def ofSheafFunctor (U : ι → Opens X) (hU : TopologicalSpace.IsOpenCover U) :
    X.Sheaf (Type u) ⥤ SheafOpenCoverGlueing U where
  obj F := ofSheaf U hU F
  map α :=
    { hom := fun i ↦ (restrictToMember (U i)).map α
      comm := ofSheaf_map_comm U α }
  map_id F := by
    apply SheafOpenCoverGlueing.Hom.ext
    funext i
    change (restrictToMember (U i)).map (𝟙 F) =
      𝟙 ((restrictToMember (U i)).obj F)
    simp
  map_comp α β := by
    apply SheafOpenCoverGlueing.Hom.ext
    funext i
    change (restrictToMember (U i)).map (α ≫ β) =
      (restrictToMember (U i)).map α ≫ (restrictToMember (U i)).map β
    simp

end SheafOpenCoverGlueing

/-- A sheaf gluing datum on an open cover canonically supplies the covering hypothesis as a
`Fact`. -/
instance {ι : Type w} {U : ι → Opens X} (data : SheafOpenCoverGlueing U) :
    Fact (TopologicalSpace.IsOpenCover U) :=
  ⟨data.isCover⟩

end
