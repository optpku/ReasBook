module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.Topology.Sheaves.Points
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sober
public import stacks_project.Chap07.Proposition_7_33_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open TopCat
open TopologicalSpace

universe u

namespace CategoryTheory

variable {X : TopCat.{u}}

/- Domain-style sampling for Example 7.33.6:
- primary domain: points of the opens site of a topological space, their classification by
  irreducible closed subsets, and the sober-space identification of irreducible closed subsets with
  points;
- sampled owner API:
  `GrothendieckTopology.Point`,
  `Opens.pointGrothendieckTopology`,
  `IrreducibleCloseds`,
  `IsGenericPoint`,
  `irreducibleSetEquivPoints`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point` together with the
  canonical topological owners `IrreducibleCloseds` and `irreducibleSetEquivPoints`.

Source/core/bridge triage:
- `source-facing`: the point `irreducibleClosedSitePoint Z` attached to an irreducible closed
  subset and the recovered irreducible closed subset `sitePointIrreducibleClosed Φ`;
- `core/canonical`: `GrothendieckTopology.Point`, `Opens.pointGrothendieckTopology`,
  `IrreducibleCloseds`, `IsGenericPoint`, and `irreducibleSetEquivPoints`;
- `bridge/view`: the comparison isomorphisms between an arbitrary opens-site point, the
  irreducible-closed point extracted from it, and in the sober case the standard point attached to
  the corresponding space point.

Primitive data versus derived API:
- primitive data: an irreducible closed subset `Z` or an opens-site point `Φ`;
- derived API: singleton-or-empty fiber descriptions, the recovered support
  `sitePointIrreducibleClosed Φ`, the generic-point comparison, and the sober-space point
  classification. The sober-case point itself is therefore best expressed directly via the canonical
  owner `irreducibleSetEquivPoints`, not via a parallel one-off wrapper definition.
-/

def irreducibleClosedPointFiberObj (Z : IrreducibleCloseds X) (U : Opens X) : Type u :=
  ULift (PLift (((Z : Set X) ∩ U).Nonempty))

def irreducibleClosedPointFiberMap (Z : IrreducibleCloseds X) {U V : Opens X} (i : U ⟶ V) :
    irreducibleClosedPointFiberObj Z U ⟶ irreducibleClosedPointFiberObj Z V :=
  fun h ↦ ⟨⟨Set.Nonempty.mono (fun _ hx ↦ ⟨hx.1, i.le hx.2⟩) h.down.down⟩⟩

theorem irreducibleClosedPointFiberMap_id (Z : IrreducibleCloseds X) (U : Opens X) :
    irreducibleClosedPointFiberMap Z (𝟙 U) = 𝟙 (irreducibleClosedPointFiberObj Z U) := by
  -- The identity inclusion leaves the witness of `Z ∩ U` unchanged.
  funext h
  cases h
  rfl

theorem irreducibleClosedPointFiberMap_comp (Z : IrreducibleCloseds X)
    {U V W : Opens X} (i : U ⟶ V) (j : V ⟶ W) :
    irreducibleClosedPointFiberMap Z (i ≫ j) =
      irreducibleClosedPointFiberMap Z i ≫ irreducibleClosedPointFiberMap Z j := by
  -- Both sides transport the same intersection witness along the same inclusion chain.
  funext h
  cases h
  rfl

def irreducibleClosedPointFiber (Z : IrreducibleCloseds X) : Opens X ⥤ Type u where
  obj := irreducibleClosedPointFiberObj Z
  map := irreducibleClosedPointFiberMap Z
  map_id := irreducibleClosedPointFiberMap_id Z
  map_comp := irreducibleClosedPointFiberMap_comp Z

instance irreducibleClosedPointFiber_elements_initiallySmall (Z : IrreducibleCloseds X) :
    InitiallySmall.{u} (irreducibleClosedPointFiber Z).Elements :=
  initiallySmall_of_essentiallySmall _

instance : OrderTop (Opens X) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

noncomputable instance : HasFiniteLimits (Opens X) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

-- Proof sketch: irreducibility shows that two opens meeting `Z` have intersection meeting `Z`,
-- and thinness of the opens category resolves the parallel-arrow axiom.
/-- Helper for Example 7.33.6: the category of elements of the singleton-or-empty fiber functor
attached to an irreducible closed subset is cofiltered. -/
theorem irreducibleClosedPointFiber_isCofiltered (Z : IrreducibleCloseds X) :
    IsCofiltered (irreducibleClosedPointFiber Z).Elements where
  nonempty := by
    -- The top open meets `Z` because irreducible subsets are nonempty.
    refine ⟨⟨⊤, ?_⟩⟩
    refine ⟨⟨?_⟩⟩
    exact Set.Nonempty.mono (fun x hxZ ↦ ⟨hxZ, by trivial⟩) Z.2.nonempty
  cone_objs := by
    rintro ⟨U, sU⟩ ⟨V, sV⟩
    -- If both opens meet `Z`, irreducibility gives a point in the intersection.
    have hUV : ((Z : Set X) ∩ (U ⊓ V : Opens X)).Nonempty := by
      exact Z.2.isPreirreducible U V U.2 V.2 sU.down.down sV.down.down
    refine ⟨⟨U ⊓ V, ⟨⟨hUV⟩⟩⟩, ?_, ?_, ?_⟩
    · exact ⟨homOfLE inf_le_left, rfl⟩
    · exact ⟨homOfLE inf_le_right, rfl⟩
    · exact ⟨⟩
  cone_maps := by
    rintro ⟨U, sU⟩ ⟨V, sV⟩ ⟨f, hf⟩ ⟨g, hg⟩
    -- Parallel morphisms already agree in the thin category of opens.
    exact ⟨⟨U, sU⟩, 𝟙 _, rfl⟩

theorem irreducibleClosedPointFiber_jointly_surjective (Z : IrreducibleCloseds X)
    {U : Opens X} (R : Sieve U) (hR : R ∈ Opens.grothendieckTopology X U)
    (s : (irreducibleClosedPointFiber Z).obj U) :
    ∃ (V : Opens X) (i : V ⟶ U), R i ∧ ∃ t : (irreducibleClosedPointFiber Z).obj V,
      (irreducibleClosedPointFiber Z).map i t = s := by
  -- Refine the covering sieve at a point of `Z ∩ U`.
  rcases s.down.down with ⟨x, hxZ, hxU⟩
  rcases hR x hxU with ⟨V, i, hi, hxV⟩
  refine ⟨V, i, hi, ⟨⟨⟨x, hxZ, hxV⟩⟩⟩, ?_⟩
  rfl

/- Internally, the point attached to `Z` uses the singleton-or-empty fiber over each open `U`:
it is empty when `Z ∩ U = ∅` and a singleton when `Z ∩ U` is nonempty. -/
/-- The point of the opens site attached to an irreducible closed subset `Z`. -/
noncomputable def irreducibleClosedSitePoint (Z : IrreducibleCloseds X) :
    (Opens.grothendieckTopology X).Point := by
  -- Package the singleton-or-empty fibers with their direct cofilteredness proof.
  exact
    { fiber := irreducibleClosedPointFiber Z
      isCofiltered := irreducibleClosedPointFiber_isCofiltered Z
      jointly_surjective := by
        intro U R hR s
        rcases irreducibleClosedPointFiber_jointly_surjective Z R hR s with
          ⟨V, i, hi, t, ht⟩
        exact ⟨V, i, hi, t, ht⟩ }

-- Proof sketch: once `irreducibleClosedPointFiber Z` is realized as the fiber of a site point,
-- finite-limit preservation is the standard exactness property of point fibers.
theorem irreducibleClosedPointFiber_preservesFiniteLimits (Z : IrreducibleCloseds X) :
    PreservesFiniteLimits (irreducibleClosedPointFiber Z) := by
  -- Reuse the canonical exactness instance for the fiber of a site point.
  change PreservesFiniteLimits (irreducibleClosedSitePoint Z).fiber
  infer_instance

noncomputable instance (Z : IrreducibleCloseds X) :
    PreservesFiniteLimits (irreducibleClosedPointFiber Z) :=
  irreducibleClosedPointFiber_preservesFiniteLimits Z

/-- The fiber of the point attached to `Z` over an open `U` is nonempty exactly when `U` meets
`Z`; since fibers of points on the opens site are subsingletons, this means the fiber is then a
singleton. -/
@[simp] theorem irreducibleClosedSitePoint_fiber_nonempty_iff
    (Z : IrreducibleCloseds X) (U : Opens X) :
    Nonempty ((irreducibleClosedSitePoint Z).fiber.obj U) ↔ ((Z : Set X) ∩ U).Nonempty := by
  -- The canonical fiber is definitionally the lifted witness type for `Z ∩ U`.
  change Nonempty (ULift (PLift (((Z : Set X) ∩ U).Nonempty))) ↔ ((Z : Set X) ∩ U).Nonempty
  constructor
  · rintro ⟨⟨⟨h⟩⟩⟩
    exact h
  · intro h
    exact ⟨⟨⟨h⟩⟩⟩

/-- The fiber of the point attached to `Z` over an open `U` is empty exactly when `U` is disjoint
from `Z`. -/
@[simp] theorem irreducibleClosedSitePoint_fiber_isEmpty_iff
    (Z : IrreducibleCloseds X) (U : Opens X) :
    IsEmpty ((irreducibleClosedSitePoint Z).fiber.obj U) ↔ Disjoint (Z : Set X) U := by
  -- The canonical fiber is empty precisely when no point of `Z` lies in `U`.
  change IsEmpty (ULift (PLift (((Z : Set X) ∩ U).Nonempty))) ↔ Disjoint (Z : Set X) U
  constructor
  · intro h
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      exact (h.false ⟨⟨⟨x, hx⟩⟩⟩).elim
    · intro hx
      simp at hx
  · intro h
    refine ⟨?_⟩
    intro s
    rcases s.down.down with ⟨x, hx⟩
    exact h.le_bot hx

def sitePointEmptyFiberOpens (Φ : (Opens.grothendieckTopology X).Point) : Set (Opens X) :=
  {U | IsEmpty (Φ.fiber.obj U)}

def sitePointEmptyFiberUnion (Φ : (Opens.grothendieckTopology X).Point) : Set X :=
  ⋃ U ∈ sitePointEmptyFiberOpens Φ, (U : Set X)

def sitePointIrreducibleClosedCarrier (Φ : (Opens.grothendieckTopology X).Point) : Set X :=
  (sitePointEmptyFiberUnion Φ)ᶜ

-- Proof sketch: every member of `sitePointEmptyFiberOpens Φ` is open, so their union is open and
-- its complement is closed.
theorem sitePointIrreducibleClosedCarrier_isClosed
    (Φ : (Opens.grothendieckTopology X).Point) :
    IsClosed (sitePointIrreducibleClosedCarrier Φ) := by
  -- The empty-fiber locus is a union of open subsets.
  simpa [sitePointIrreducibleClosedCarrier, sitePointEmptyFiberUnion] using
    (isOpen_iUnion fun U => isOpen_iUnion fun _ => U.2).isClosed_compl

/-- Helper for Example 7.33.6: every point of the opens site has a nonempty fiber over the top
open, because any element of the category of elements maps into `⊤`. -/
theorem sitePoint_top_fiber_nonempty
    (Φ : (Opens.grothendieckTopology X).Point) :
    Nonempty (Φ.fiber.obj (⊤ : Opens X)) := by
  classical
  let z : Φ.fiber.Elements := Classical.choice
    (show Nonempty Φ.fiber.Elements from (inferInstance : IsCofiltered Φ.fiber.Elements).nonempty)
  -- Move any existing fiber element to the terminal open.
  exact ⟨Φ.fiber.map (homOfLE le_top) z.2⟩

/-- Helper for Example 7.33.6: if the fiber over `V` is empty, then the fiber over any smaller
open `U ⟶ V` is empty as well. -/
theorem isEmpty_fiber_of_hom (Φ : (Opens.grothendieckTopology X).Point)
    {U V : Opens X} (i : U ⟶ V) (hV : IsEmpty (Φ.fiber.obj V)) :
    IsEmpty (Φ.fiber.obj U) := by
  -- Any element over `U` would map to an impossible element over `V`.
  refine ⟨?_⟩
  intro s
  exact hV.false (Φ.fiber.map i s)

/-- Helper for Example 7.33.6: if two opens have nonempty fibers for a site point, then their
intersection also has nonempty fiber. -/
theorem nonempty_fiber_inf_of_nonempty
    (Φ : (Opens.grothendieckTopology X).Point) (U V : Opens X)
    (hU : Nonempty (Φ.fiber.obj U)) (hV : Nonempty (Φ.fiber.obj V)) :
    Nonempty (Φ.fiber.obj (U ⊓ V)) := by
  classical
  let f : U ⟶ (⊤ : Opens X) := homOfLE le_top
  let g : V ⟶ (⊤ : Opens X) := homOfLE le_top
  let t : (Types.pullbackCone (Φ.fiber.map f) (Φ.fiber.map g)).pt := by
    refine ⟨⟨Classical.choice hU, Classical.choice hV⟩, ?_⟩
    have hsub : Subsingleton (Φ.fiber.obj (⊤ : Opens X)) :=
      Φ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop
    exact Subsingleton.elim _ _
  -- Pullback preservation identifies the fiber over `U ⊓ V` with this pullback.
  have hs : Nonempty (Φ.fiber.obj (pullback f g)) := by
    refine ⟨(PreservesPullback.iso Φ.fiber f g).inv
      ((Types.pullbackIsoPullback (Φ.fiber.map f) (Φ.fiber.map g)).inv t)⟩
  have hpullback : pullback f g = U ⊓ V := by
    exact CompleteLattice.pullback_eq_inf f g
  exact hpullback ▸ hs

/-- Helper for Example 7.33.6: an open has empty fiber exactly when it is disjoint from the raw
carrier recovered from all empty-fiber opens. -/
theorem isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier
    (Φ : (Opens.grothendieckTopology X).Point) (U : Opens X) :
    IsEmpty (Φ.fiber.obj U) ↔ Disjoint (sitePointIrreducibleClosedCarrier Φ) U := by
  constructor
  · intro hU
    -- If `U` itself has empty fiber, then every point of `U` lies in the excluded union.
    refine Set.disjoint_left.2 ?_
    intro x hxCarrier hxUmem
    have hxUnion : x ∈ sitePointEmptyFiberUnion Φ := by
      change x ∈ ⋃ U : Opens X, ⋃ (_ : U ∈ sitePointEmptyFiberOpens Φ), (U : Set X)
      exact Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨hU, hxUmem⟩⟩
    exact hxCarrier hxUnion
  · intro hDisj
    -- Route correction: cover `U` by smaller opens whose fibers are already empty.
    by_contra hU
    rw [not_isEmpty_iff] at hU
    let R : Sieve U := {
      arrows := fun V i => IsEmpty (Φ.fiber.obj V)
      downward_closed := by
        intro Y Z f hf g
        exact isEmpty_fiber_of_hom Φ g hf
    }
    have hR : R ∈ Opens.grothendieckTopology X U := by
      intro x hxU
      have hxnot : x ∉ sitePointIrreducibleClosedCarrier Φ := by
        intro hxCarrier
        exact Set.disjoint_left.1 hDisj hxCarrier hxU
      have hxUnion : x ∈ sitePointEmptyFiberUnion Φ := by
        simpa [sitePointIrreducibleClosedCarrier] using hxnot
      rcases Set.mem_iUnion.1 hxUnion with ⟨V, hxV⟩
      rcases Set.mem_iUnion.1 hxV with ⟨hV, hxV⟩
      refine ⟨U ⊓ V, homOfLE inf_le_left, ?_, ⟨hxU, hxV⟩⟩
      exact isEmpty_fiber_of_hom Φ (homOfLE inf_le_right) hV
    rcases hU with ⟨s⟩
    rcases Φ.jointly_surjective R hR s with ⟨V, i, hi, t, ht⟩
    exact hi.false t

-- Proof sketch: use the finite-limit and covering properties of a site point on the opens site to
-- show that if the complementary closed subset were the union of two proper closed subsets, then
-- one of them would already equal the whole support.
theorem sitePointIrreducibleClosedCarrier_isIrreducible
    (Φ : (Opens.grothendieckTopology X).Point) :
    IsIrreducible (sitePointIrreducibleClosedCarrier Φ) := by
  refine ⟨?_, ?_⟩
  · -- The top open cannot have empty fiber, so the recovered carrier is nonempty.
    by_contra hEmpty
    have hDisj : Disjoint (sitePointIrreducibleClosedCarrier Φ) (⊤ : Opens X) :=
      Set.disjoint_left.2 fun x hx _ ↦ hEmpty ⟨x, hx⟩
    have hTopEmpty :
        IsEmpty (Φ.fiber.obj (⊤ : Opens X)) :=
      (isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier Φ ⊤).2 hDisj
    exact not_isEmpty_iff.mpr (sitePoint_top_fiber_nonempty Φ) hTopEmpty
  · -- If the carrier is covered by two closed sets, one complement already has empty fiber.
    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro z₁ z₂ hz₁ hz₂ hcover
    let U₁ : Opens X := ⟨z₁ᶜ, hz₁.isOpen_compl⟩
    let U₂ : Opens X := ⟨z₂ᶜ, hz₂.isOpen_compl⟩
    have hDisjInf : Disjoint (sitePointIrreducibleClosedCarrier Φ) (U₁ ⊓ U₂ : Opens X) :=
      Set.disjoint_left.2 fun x hxS hxU ↦ by
        have hxCover : x ∈ z₁ ∪ z₂ := hcover hxS
        have hxNotCover : x ∉ z₁ ∪ z₂ := by
          rcases hxU with ⟨hxU₁, hxU₂⟩
          intro hx
          rcases hx with hx | hx
          · exact hxU₁ hx
          · exact hxU₂ hx
        exact (hxNotCover hxCover).elim
    have hInfEmpty :
        IsEmpty (Φ.fiber.obj (U₁ ⊓ U₂ : Opens X)) :=
      (isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier Φ (U₁ ⊓ U₂)).2 hDisjInf
    have hEither :
        IsEmpty (Φ.fiber.obj U₁) ∨ IsEmpty (Φ.fiber.obj U₂) := by
      by_cases hU₁ : IsEmpty (Φ.fiber.obj U₁)
      · exact Or.inl hU₁
      · by_cases hU₂ : IsEmpty (Φ.fiber.obj U₂)
        · exact Or.inr hU₂
        · exfalso
          rcases nonempty_fiber_inf_of_nonempty Φ U₁ U₂
              (not_isEmpty_iff.mp hU₁) (not_isEmpty_iff.mp hU₂) with ⟨s⟩
          exact hInfEmpty.false s
    rcases hEither with hU₁ | hU₂
    · left
      have hDisj :
          Disjoint (sitePointIrreducibleClosedCarrier Φ) U₁ :=
        (isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier Φ U₁).1 hU₁
      intro x hxS
      by_contra hxz₁
      exact Set.disjoint_left.1 hDisj hxS hxz₁
    · right
      have hDisj :
          Disjoint (sitePointIrreducibleClosedCarrier Φ) U₂ :=
        (isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier Φ U₂).1 hU₂
      intro x hxS
      by_contra hxz₂
      exact Set.disjoint_left.1 hDisj hxS hxz₂

/-- The irreducible closed subset canonically associated to a point of the opens site. -/
def sitePointIrreducibleClosed (Φ : (Opens.grothendieckTopology X).Point) :
    IrreducibleCloseds X :=
  ⟨sitePointIrreducibleClosedCarrier Φ,
    sitePointIrreducibleClosedCarrier_isIrreducible Φ,
    sitePointIrreducibleClosedCarrier_isClosed Φ⟩

/-- The irreducible closed subset recovered from `Φ` consists of those points all of whose open
neighbourhoods have nonempty fiber under `Φ`. -/
theorem coe_sitePointIrreducibleClosed (Φ : (Opens.grothendieckTopology X).Point) :
    (sitePointIrreducibleClosed Φ : Set X) =
      {x | ∀ U : Opens X, x ∈ U → Nonempty (Φ.fiber.obj U)} := by
  ext x
  change x ∈ sitePointIrreducibleClosedCarrier Φ ↔
      ∀ U : Opens X, x ∈ U → Nonempty (Φ.fiber.obj U)
  rw [sitePointIrreducibleClosedCarrier, Set.mem_compl_iff]
  constructor
  · intro hx U hxU
    -- If `x` lies in an empty-fiber open, then it lies in the excluded union.
    by_contra hU
    apply hx
    change x ∈ ⋃ U : Opens X, ⋃ (_ : U ∈ sitePointEmptyFiberOpens Φ), (U : Set X)
    exact Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨⟨fun s ↦ hU ⟨s⟩⟩, hxU⟩⟩
  · intro hx hxUnion
    -- Any witness that `x` lies in the excluded union contradicts the claimed nonemptiness.
    rcases Set.mem_iUnion.1 hxUnion with ⟨U, hxUnionU⟩
    rcases Set.mem_iUnion.1 hxUnionU with ⟨hU, hxU⟩
    rcases hx U hxU with ⟨s⟩
    exact hU.false s

/-- Membership in the irreducible closed subset recovered from `Φ` is equivalent to every open
neighbourhood having nonempty fiber. -/
@[simp] theorem mem_sitePointIrreducibleClosed_iff
    (Φ : (Opens.grothendieckTopology X).Point) {x : X} :
    x ∈ sitePointIrreducibleClosed Φ ↔
      ∀ U : Opens X, x ∈ U → Nonempty (Φ.fiber.obj U) := by
  change x ∈ ((sitePointIrreducibleClosed Φ : Set X)) ↔
      ∀ U : Opens X, x ∈ U → Nonempty (Φ.fiber.obj U)
  rw [coe_sitePointIrreducibleClosed]
  simp

/-- An open is disjoint from the irreducible closed subset recovered from `Φ` exactly when its
fiber under `Φ` is empty. -/
@[simp] theorem isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosed
    (Φ : (Opens.grothendieckTopology X).Point) (U : Opens X) :
    IsEmpty (Φ.fiber.obj U) ↔ Disjoint (sitePointIrreducibleClosed Φ : Set X) U := by
  -- This is the bundled version of the carrier-level emptiness/disjointness bridge.
  simpa [sitePointIrreducibleClosed] using
    isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosedCarrier Φ U

/-- Helper for Example 7.33.6: two points of the opens site are isomorphic once they have the same
nonempty opens, because every fiber is a subsingleton. -/
theorem iso_of_fiber_nonempty_iff
    {Φ Ψ : (Opens.grothendieckTopology X).Point}
    (h : ∀ U : Opens X, Nonempty (Φ.fiber.obj U) ↔ Nonempty (Ψ.fiber.obj U)) :
    Nonempty (Φ ≅ Ψ) := by
  classical
  refine ⟨{
    hom := {
      hom := {
        app := fun U s ↦ Classical.choice ((h U).2 ⟨s⟩)
        naturality := by
          intro U V f
          ext s
          let hsub : Subsingleton (Φ.fiber.obj V) :=
            Φ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop
          exact @Subsingleton.elim _ hsub _ _
      }
    }
    inv := {
      hom := {
        app := fun U s ↦ Classical.choice ((h U).1 ⟨s⟩)
        naturality := by
          intro U V f
          ext s
          let hsub : Subsingleton (Ψ.fiber.obj V) :=
            Ψ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop
          exact @Subsingleton.elim _ hsub _ _
      }
    }
    hom_inv_id := by
      ext U s
      let hsub : Subsingleton (Φ.fiber.obj U) :=
        Φ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop
      exact @Subsingleton.elim _ hsub _ _
    inv_hom_id := by
      ext U s
      let hsub : Subsingleton (Ψ.fiber.obj U) :=
        Ψ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop
      exact @Subsingleton.elim _ hsub _ _
  }⟩

/-- Helper for Example 7.33.6: the irreducible closed subset recovered from a point depends only on
its isomorphism class. -/
theorem sitePointIrreducibleClosed_eq_of_iso
    {Φ Ψ : (Opens.grothendieckTopology X).Point} (e : Φ ≅ Ψ) :
    sitePointIrreducibleClosed Φ = sitePointIrreducibleClosed Ψ := by
  ext x
  constructor
  · intro hx
    -- Transport a neighborhood fiber witness across the inverse point morphism.
    have hx' := (mem_sitePointIrreducibleClosed_iff Φ).1 hx
    exact (mem_sitePointIrreducibleClosed_iff Ψ).2 fun U hxU ↦ by
      rcases hx' U hxU with ⟨s⟩
      exact ⟨e.inv.hom.app U s⟩
  · intro hx
    -- Transport a neighborhood fiber witness across the forward point morphism.
    have hx' := (mem_sitePointIrreducibleClosed_iff Ψ).1 hx
    exact (mem_sitePointIrreducibleClosed_iff Φ).2 fun U hxU ↦ by
      rcases hx' U hxU with ⟨s⟩
      exact ⟨e.hom.hom.app U s⟩

-- Proof sketch: the example constructs the support `Z` of a site point `Φ` as the complement of
-- the largest open with empty fiber and shows that `Φ` is uniquely determined, up to isomorphism,
-- by the singleton-or-empty functor attached to this irreducible closed subset.
/-- Example 7.33.6: a point of the opens site is isomorphic to the canonical site point attached
to the irreducible closed subset extracted from its empty fibers. -/
theorem opensSitePoint_iso_irreducibleClosedSitePoint
    (Φ : (Opens.grothendieckTopology X).Point) :
    Nonempty (Φ ≅ irreducibleClosedSitePoint (sitePointIrreducibleClosed Φ)) := by
  -- Compare the two points objectwise through the nonemptiness of their fibers.
  refine iso_of_fiber_nonempty_iff (Φ := Φ)
    (Ψ := irreducibleClosedSitePoint (sitePointIrreducibleClosed Φ)) ?_
  intro U
  constructor
  · intro hU
    have hNotDisjoint : ¬ Disjoint (sitePointIrreducibleClosed Φ : Set X) U := by
      intro hDisj
      have hEmpty : IsEmpty (Φ.fiber.obj U) :=
        (isEmpty_fiber_iff_disjoint_sitePointIrreducibleClosed Φ U).2 hDisj
      exact (not_isEmpty_iff.mpr hU) hEmpty
    exact (irreducibleClosedSitePoint_fiber_nonempty_iff (sitePointIrreducibleClosed Φ) U).2
      (Set.not_disjoint_iff_nonempty_inter.1 hNotDisjoint)
  · intro hU
    rcases
      (irreducibleClosedSitePoint_fiber_nonempty_iff (sitePointIrreducibleClosed Φ) U).1 hU with
        ⟨x, hxZ, hxU⟩
    exact (mem_sitePointIrreducibleClosed_iff Φ).1 hxZ U hxU

/-- Helper for Example 7.33.6: recovering the irreducible closed subset attached to the canonical
singleton-or-empty point returns the original subset. -/
theorem sitePointIrreducibleClosed_of_irreducibleClosedSitePoint_aux
    (Z : IrreducibleCloseds X) :
    sitePointIrreducibleClosed (irreducibleClosedSitePoint Z) = Z := by
  -- Compare the two irreducible closed subsets by testing which opens have nonempty fiber.
  ext x
  constructor
  · intro hx
    by_contra hxZ
    let U : Opens X := ⟨(Z : Set X)ᶜ, Z.3.isOpen_compl⟩
    have hxU : x ∈ U := hxZ
    have hxFiber : Nonempty ((irreducibleClosedSitePoint Z).fiber.obj U) :=
      (mem_sitePointIrreducibleClosed_iff (irreducibleClosedSitePoint Z)).1 hx U hxU
    have hEmpty : IsEmpty ((irreducibleClosedSitePoint Z).fiber.obj U) := by
      refine (irreducibleClosedSitePoint_fiber_isEmpty_iff Z U).2 ?_
      exact disjoint_compl_right
    rcases hxFiber with ⟨s⟩
    exact hEmpty.false s
  · intro hxZ
    -- Any open neighbourhood of a point of `Z` meets `Z`, hence has nonempty canonical fiber.
    change x ∈ sitePointIrreducibleClosed (irreducibleClosedSitePoint Z)
    rw [mem_sitePointIrreducibleClosed_iff]
    intro U hxU
    exact (irreducibleClosedSitePoint_fiber_nonempty_iff Z U).2 ⟨x, hxZ, hxU⟩

/-- Companion uniqueness form of Example 7.33.6: points of the opens site `X_{Zar}`, and hence
points of `Sh(X)`, are in one-to-one correspondence up to isomorphism with irreducible closed
subsets of `X`. -/
theorem opensSitePoint_existsUnique_irreducibleClosedSubset
    (Φ : (Opens.grothendieckTopology X).Point) :
    ∃! Z : IrreducibleCloseds X, Nonempty (Φ ≅ irreducibleClosedSitePoint Z) := by
  refine ⟨sitePointIrreducibleClosed Φ, opensSitePoint_iso_irreducibleClosedSitePoint Φ, ?_⟩
  intro Z hZ
  rcases hZ with ⟨e⟩
  -- The extracted support is invariant under isomorphism, and the canonical point of `Z`
  -- recovers `Z` itself.
  exact ((sitePointIrreducibleClosed_eq_of_iso e).trans
    (sitePointIrreducibleClosed_of_irreducibleClosedSitePoint_aux Z)).symm

-- Proof sketch: for the singleton-or-empty point attached to `Z`, the largest open with empty
-- fiber is exactly `X \ Z`, so the complementary irreducible closed subset recovered by the
-- construction is `Z` itself.
/-- Recovering the irreducible closed subset attached to its own singleton-or-empty site point
returns the original subset. -/
theorem sitePointIrreducibleClosed_of_irreducibleClosedSitePoint (Z : IrreducibleCloseds X) :
    sitePointIrreducibleClosed (irreducibleClosedSitePoint Z) = Z := by
  exact sitePointIrreducibleClosed_of_irreducibleClosedSitePoint_aux Z

-- Proof sketch: if `x` is a generic point of `Z`, then an open subset meets `Z` if and only if
-- it contains `x`, so the singleton-or-empty point attached to `Z` and the standard site point
-- attached to `x` have isomorphic fiber functors.
/-- If `x` is a generic point of an irreducible closed subset `Z`, then the site point attached to
`Z` is isomorphic to the standard opens-site point attached to `x`. -/
theorem irreducibleClosedSitePoint_iso_pointGrothendieckTopology_of_isGenericPoint
    {x : X} {Z : IrreducibleCloseds X} (hx : IsGenericPoint x Z) :
    Nonempty (irreducibleClosedSitePoint Z ≅ Opens.pointGrothendieckTopology x) := by
  -- The generic-point criterion says that `U` meets `Z` exactly when `x ∈ U`.
  refine iso_of_fiber_nonempty_iff (Φ := irreducibleClosedSitePoint Z)
    (Ψ := Opens.pointGrothendieckTopology x) ?_
  intro U
  constructor
  · intro hU
    have hMeet : ((Z : Set X) ∩ U).Nonempty :=
      (irreducibleClosedSitePoint_fiber_nonempty_iff Z U).1 hU
    have hxU : x ∈ U := (hx.mem_open_set_iff U.2).2 hMeet
    simpa [Opens.pointGrothendieckTopology] using hxU
  · intro hU
    have hxU : x ∈ U := by
      simpa [Opens.pointGrothendieckTopology] using hU
    exact (irreducibleClosedSitePoint_fiber_nonempty_iff Z U).2
      ((hx.mem_open_set_iff U.2).1 hxU)

attribute [local instance] specializationOrder

-- Proof sketch: apply the irreducible-closed classification theorem, then use sobriety to identify
-- the resulting irreducible closed subset with the closure of a unique generic point.
/-- In a sober topological space, every point of the opens site is isomorphic to the standard site
point attached to its canonically associated point of `X`. -/
theorem opensSitePoint_iso_pointGrothendieckTopology_of_quasiSober
    [T0Space X] [QuasiSober X] (Φ : (Opens.grothendieckTopology X).Point) :
    Nonempty (Φ ≅ Opens.pointGrothendieckTopology
      (irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ))) := by
  -- Compare `Φ` first with its recovered irreducible closed subset, then use its generic point.
  let Z := sitePointIrreducibleClosed Φ
  have hgeneric : IsGenericPoint (irreducibleSetEquivPoints Z) (Z : Set X) := by
    simpa [irreducibleSetEquivPoints, Z] using Z.2.isGenericPoint_genericPoint Z.3
  rcases opensSitePoint_iso_irreducibleClosedSitePoint Φ with ⟨e₁⟩
  rcases irreducibleClosedSitePoint_iso_pointGrothendieckTopology_of_isGenericPoint
      (x := irreducibleSetEquivPoints Z) (Z := Z) hgeneric with ⟨e₂⟩
  exact ⟨e₁ ≪≫ e₂⟩

/-- Companion uniqueness form of Example 7.33.6 in the sober case. -/
theorem opensSitePoint_existsUnique_spacePoint [T0Space X] [QuasiSober X]
    (Φ : (Opens.grothendieckTopology X).Point) :
    ∃! x : X, Nonempty (Φ ≅ Opens.pointGrothendieckTopology x) := by
  refine ⟨irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ),
    opensSitePoint_iso_pointGrothendieckTopology_of_quasiSober Φ, ?_⟩
  intro y hy
  rcases opensSitePoint_iso_pointGrothendieckTopology_of_quasiSober Φ with ⟨e₁⟩
  rcases hy with ⟨e₂⟩
  let e : Opens.pointGrothendieckTopology (irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ))
      ≅ Opens.pointGrothendieckTopology y := e₁.symm ≪≫ e₂
  have hxy :
      irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ) ⤳ y :=
    Opens.pointGrothendieckTopologyHomEquiv e.hom
  have hyx :
      y ⤳ irreducibleSetEquivPoints (sitePointIrreducibleClosed Φ) :=
    Opens.pointGrothendieckTopologyHomEquiv e.inv
  exact (hxy.antisymm hyx).eq.symm

end CategoryTheory
