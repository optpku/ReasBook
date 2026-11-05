module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.SheafOfFunctions
public import stacks_project.Chap06.Definition_6_4_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open scoped TopCat

noncomputable section

universe u v

variable {X : TopCat.{u}} (M : X → Type v) [∀ x, AddCommGroup (M x)]

/- Domain-style sampling for Example 6.4.5:
- primary domain: abelian presheaves on a topological space built from pointwise direct sums;
- sampled owner API:
  `PAb(X)`,
  `TopCat.presheafToTypes`,
  `TopCat.presheafToTypes_map`,
  `DFinsupp.comapDomain`;
- source/core/bridge triage:
  `source-facing`: the presheaf `U ↦ Π₀ x : U, M x.1`;
  `core/canonical`: the presheaf owner `PAb(X)`;
  `bridge/view`: the restriction map obtained by restricting a `DFinsupp` along the canonical
    inclusion of the smaller open set into the larger one.

Primitive data are only the section object on each open set and the canonical restriction along an
inclusion of opens. The refinement therefore uses the canonical `DFinsupp.comapDomain`
restriction map directly and treats any coordinatewise view as derived API.
-/

/-- Sections of the pointwise direct-sum presheaf on an open set. -/
public abbrev pointwiseDirectSumSection (U : Opens X) : Type max u v :=
  Π₀ x : U, M x.1

/-- Restrict a direct-sum section along an inclusion of opens by keeping exactly the coordinates
indexed by points of the smaller open set. -/
public noncomputable abbrev pointwiseDirectSumSectionMap {U V : Opens X} (i : V ⟶ U) :
    pointwiseDirectSumSection M U →+ pointwiseDirectSumSection M V :=
  AddMonoidHom.mk'
    (DFinsupp.comapDomain (Opens.inclusion i.le) (Set.inclusion_injective i.le))
    (DFinsupp.comapDomain_add (Opens.inclusion i.le) (Set.inclusion_injective i.le))

/-- The direct-sum restriction map keeps the coordinate indexed by each point of the smaller open
set. -/
@[simp] private theorem pointwiseDirectSumSectionMap_apply {U V : Opens X} (i : V ⟶ U)
    (s : pointwiseDirectSumSection M U) (y : V) :
    pointwiseDirectSumSectionMap M i s y = s ⟨y, i.le y.2⟩ :=
  rfl

/-- Example 6.4.5: the assignment sending an open set `U` to the direct sum `⨁_{x ∈ U} M x`,
with restriction maps obtained by discarding summands supported outside the smaller open set,
defines a presheaf of abelian groups. -/
noncomputable abbrev pointwiseDirectSumPresheaf : PAb(X) :=
  { obj := fun U ↦ AddCommGrpCat.of (pointwiseDirectSumSection M U.unop)
    map := fun {_ _} i ↦ AddCommGrpCat.ofHom (pointwiseDirectSumSectionMap M i.unop)
    map_id := by
      intro U
      ext s y
      rfl
    map_comp := by
      intro U V W i j
      ext s y
      rfl }

-- Proof sketch: this is exactly the object assignment used in the definition of
-- `pointwiseDirectSumPresheaf`.
/-- The value of the pointwise direct-sum presheaf on `U` is the direct sum over the points of `U`.
-/
theorem pointwiseDirectSumPresheaf_obj (U : Opens X) :
    (pointwiseDirectSumPresheaf M).obj (op U) = AddCommGrpCat.of (Π₀ x : U, M x.1) :=
  rfl

/-- The restriction map of the pointwise direct-sum presheaf keeps the coordinate at each point of
the smaller open set and forgets the coordinates supported outside it. -/
@[simp] theorem pointwiseDirectSumPresheaf_map_apply {U V : Opens X} (i : V ⟶ U)
    (s : Π₀ x : U, M x.1) (y : V) :
    ((pointwiseDirectSumPresheaf M).map i.op s) y = s ⟨y, i.le y.2⟩ :=
  pointwiseDirectSumSectionMap_apply M i s y
