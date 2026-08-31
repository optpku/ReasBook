module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.CoversTop
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import stacks_project.Chap06.Definition_6_30_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Presheaf

universe u v w

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Definition 6.30.2:
- primary domain: sheaves of sets on a topological basis, stated by the Stacks Project gluing
  condition `(**)` on basis covers and chosen basis covers of pairwise intersections;
- sampled owner abstractions:
  `BasisOpen`,
  `SemiRepresentableFamily.Over`,
  `Presheaf`,
  `Functor.inducedTopology`,
  `Sheaf`;
- source-facing layer: basis covers, chosen covers of pairwise intersections, and the resulting
  gluing condition `(**)` for a basis presheaf;
- core/canonical owner: `Functor.inducedTopology` and `Sheaf` on the basis-open category, but only
  as a bridge once `hB : Opens.IsBasis B` is fixed;
- bridge/view layer: `BasisSiteSheaf`, the canonical sheaf category on the induced site.

Primitive data are the basis-open category together with basis covers and chosen overlap covers.
The source-facing owner is the gluing predicate on presheaves; the induced-topology sheaf category
is a derived bridge, not the main public definition. -/

/-- The inclusion of the basis-open category into the category of open subsets of `X`. -/
abbrev basisOpenInclusion (B : Set (Opens X)) : BasisOpen B ⥤ Opens X :=
  ObjectProperty.ι (fun U : Opens X ↦ U ∈ B)

private theorem range_basisOpenInclusion_obj (B : Set (Opens X)) :
    Set.range (basisOpenInclusion B).obj = B := by
  ext U
  constructor
  · rintro ⟨V, rfl⟩
    exact V.2
  · intro hU
    exact ⟨⟨U, hU⟩, rfl⟩

/-- The inclusion of basis opens into all opens is cover dense when `B` is a topological basis. -/
theorem basisOpenInclusion_isCoverDense {B : Set (Opens X)} (hB : Opens.IsBasis B) :
    (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) := by
  let G : BasisOpen B ⥤ Opens (TopCat.of X) := basisOpenInclusion B
  refine (TopCat.Opens.coverDense_iff_isBasis G).2 ?_
  simpa [G, range_basisOpenInclusion_obj B] using hB

/-- A covering of a basis open `U` by basis opens. -/
structure BasisCover (B : Set (Opens X)) (U : BasisOpen B) where
  /-- The index type of the covering family. -/
  ι : Type u
  /-- The basis open indexed by `i`. -/
  obj : ι → BasisOpen B
  /-- The inclusion of the `i`-th basis open into `U`. -/
  hom : ∀ i : ι, obj i ⟶ U
  /-- The union of the members of the family is `U`. -/
  iUnion_eq : (U.obj : Set X) = ⋃ i : ι, ((obj i).obj : Set X)

/-- Chosen coverings of the pairwise intersections in a basis cover. -/
structure BasisIntersectionCover (B : Set (Opens X)) {U : BasisOpen B}
    (𝒰 : BasisCover B U) where
  /-- The index type for the chosen cover of `Uᵢ ∩ Uⱼ`. -/
  κ : 𝒰.ι → 𝒰.ι → Type u
  /-- The basis opens covering each pairwise intersection. -/
  obj (i j : 𝒰.ι) (k : κ i j) : BasisOpen B
  /-- The inclusion of a chosen overlap open into the left member of the pair. -/
  left (i j : 𝒰.ι) (k : κ i j) : obj i j k ⟶ 𝒰.obj i
  /-- The inclusion of a chosen overlap open into the right member of the pair. -/
  right (i j : 𝒰.ι) (k : κ i j) : obj i j k ⟶ 𝒰.obj j
  /-- The chosen overlap family covers `Uᵢ ∩ Uⱼ`. -/
  iUnion_eq (i j : 𝒰.ι) :
    (((𝒰.obj i).obj ⊓ (𝒰.obj j).obj : Opens X) : Set X) =
      ⋃ k, ((obj i j k).obj : Set X)

namespace BasisCover

variable {B : Set (Opens X)} {U : BasisOpen B}

/-- The sheaf condition `(**)` for a basis cover together with chosen coverings of pairwise
intersections. -/
def HasSheafCondition (F : Presheaf (BasisOpen B)) (𝒰 : BasisCover B U)
    (𝒱 : BasisIntersectionCover B 𝒰) : Prop :=
  ∀ s : FamilyOfElementsOnObjects F 𝒰.obj,
    (∀ i j k, F.map ((𝒱.left i j k).op) (s i) = F.map ((𝒱.right i j k).op) (s j)) →
      ∃! t : F.obj (op U), ∀ i, F.map ((𝒰.hom i).op) t = s i

/-- Helper for Definition 6.30.2: a basis cover `𝒱` refines `𝒰` if each member of `𝒱` factors
through some member of `𝒰`. -/
def Refines (𝒱 𝒰 : BasisCover B U) : Prop :=
  ∃ α : 𝒱.ι → 𝒰.ι, ∀ i : 𝒱.ι, ∃ f : 𝒱.obj i ⟶ 𝒰.obj (α i), 𝒱.hom i = f ≫ 𝒰.hom (α i)

/-- A family `C(U)` of basis covers is cofinal if every basis cover of `U` is refined by a member
of `C(U)`. -/
def IsCofinalSystem (C : ∀ U : BasisOpen B, Set (BasisCover B U)) : Prop :=
  ∀ U : BasisOpen B, ∀ 𝒰 : BasisCover B U, ∃ 𝒱 : BasisCover B U, 𝒱 ∈ C U ∧
    Refines 𝒱 𝒰

end BasisCover

namespace CategoryTheory.Presheaf

variable {B : Set (Opens X)}

/-- Definition 6.30.2: a presheaf of sets on the basis `B` is a sheaf on that basis if it
satisfies the Stacks gluing condition `(**)` for every basis cover and every chosen basis cover of
its pairwise intersections. -/
def IsBasisSheaf (F : Presheaf (BasisOpen B)) : Prop :=
  ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U) (𝒱 : BasisIntersectionCover B 𝒰),
    BasisCover.HasSheafCondition F 𝒰 𝒱

/-- A basis sheaf satisfies the gluing condition `(**)` for every basis cover and every chosen
cover of the pairwise intersections. -/
-- Proof sketch: unfold `IsBasisSheaf`.
theorem isBasisSheaf_iff (F : Presheaf (BasisOpen B)) :
    F.IsBasisSheaf ↔
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U) (𝒱 : BasisIntersectionCover B 𝒰),
        BasisCover.HasSheafCondition F 𝒰 𝒱 := by
  -- The theorem is exactly the definitional expansion of `IsBasisSheaf`.
  rfl

end CategoryTheory.Presheaf

/-- The source-facing category of sheaves of sets on the basis `B`, defined by the gluing
condition `(**)` from Definition 6.30.2. -/
abbrev BasisSheaf (B : Set (Opens X)) :=
  ObjectProperty.FullSubcategory fun F : Presheaf (BasisOpen B) ↦ Presheaf.IsBasisSheaf F

/-- The Grothendieck topology on basis opens induced from the topology on all opens of `X`,
available once `B` is known to be a topological basis. -/
noncomputable abbrev basisGrothendieckTopology (B : Set (Opens X)) (hB : Opens.IsBasis B) :
    GrothendieckTopology (BasisOpen B) := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  exact (basisOpenInclusion B).inducedTopology (Opens.grothendieckTopology X)

/-- The canonical bridge/view category of `C`-valued sheaves on the induced basis site. -/
abbrev BasisSiteSheaf (C : Type v) [Category.{w} C] (B : Set (Opens X)) (hB : Opens.IsBasis B) :=
  Sheaf (basisGrothendieckTopology B hB) C
