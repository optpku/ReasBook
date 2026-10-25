module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Group.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.Topology.Sheaves.Presheaf
public import stacks_project.Chap06.Definition_6_3_2
public import stacks_project.Chap06.Definition_6_4_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open scoped TopCat

universe u v

/- Domain-style sampling for Lemma 6.4.3:
- primary domain: abelian-group structures on a fixed set-valued presheaf and the canonical
  abelian-presheaf owner `PAb(X)`;
- inspected owner declarations:
  `PAb(X)`,
  `FunctorToTypes.prod`,
  `FunctorToTypes.prod.lift`,
  `AddGroup.ofLeftAxioms`;
- best owner abstraction: the canonical presheaf owner `PAb(X)`, while the source-facing content of
  this lemma is the equivalence between the four Stacks presentations on a fixed
  `F : X.Presheaf (Type v)`.

Primitive-vs-derived split:
- primitive source-facing data: the four presentations below on the fixed presheaf `F`;
- derived canonical view: the corresponding lift of `F` to the canonical owner `PAb(X)`, whose
  sectionwise additive structure and additive restriction maps are then derived from that owner.

Source/core/bridge triage:
- `source-facing`: `CompatibleAddCommGroupStructure F`, `CompatibleAddCommGroupMaps F`,
  `CompatibleAddCommGroupMapStructure F`, `CompatibleAdditionMapStructure F`;
- `core/canonical`: `PAb(X)`;
- `bridge/view`: the internal conversions between the four source-facing presentations. -/

/-- A compatible additive commutative group structure on the sections of a set-valued presheaf. -/
structure CompatibleAddCommGroupStructure {X : TopCat.{u}} (F : X.Presheaf (Type v)) where
  /-- Each section object of the presheaf carries an additive commutative group structure. -/
  addCommGroup (U : (Opens X)ᵒᵖ) : AddCommGroup (F.obj U)
  /-- Each restriction map is additive. -/
  map_add {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s t : F.obj U) :
    F.map i (s + t) = F.map i s + F.map i t

/-- A source-facing presentation of abelian-presheaf structure on `F` by presheaf maps `0`, `-`,
and `+`, together with the usual abelian-group axioms written pointwise on every open. -/
structure CompatibleAddCommGroupMaps {X : TopCat.{u}} (F : X.Presheaf (Type v)) where
  /-- The zero section as a morphism from the terminal presheaf. -/
  zero : ((PUnit : Type v) ₚ X : X.Presheaf (Type v)) ⟶ F
  /-- The inverse map of presheaves. -/
  neg : F ⟶ F
  /-- The addition morphism of presheaves. -/
  add : F ⨯ F ⟶ F
  /-- Zero is a left additive identity on each open. -/
  zero_add (U : (Opens X)ᵒᵖ) (s : F.obj U) :
    add.app U (FunctorToTypes.prodMk (zero.app U PUnit.unit) s) = s
  /-- Zero is a right additive identity on each open. -/
  add_zero (U : (Opens X)ᵒᵖ) (s : F.obj U) :
    add.app U (FunctorToTypes.prodMk s (zero.app U PUnit.unit)) = s
  /-- Addition is associative on each open. -/
  add_assoc (U : (Opens X)ᵒᵖ) (s t u : F.obj U) :
    add.app U (FunctorToTypes.prodMk (add.app U (FunctorToTypes.prodMk s t)) u) =
      add.app U (FunctorToTypes.prodMk s (add.app U (FunctorToTypes.prodMk t u)))
  /-- Every section has a left additive inverse. -/
  add_left_neg (U : (Opens X)ᵒᵖ) (s : F.obj U) :
    add.app U (FunctorToTypes.prodMk (neg.app U s) s) = zero.app U PUnit.unit
  /-- Addition is commutative on each open. -/
  add_comm (U : (Opens X)ᵒᵖ) (s t : F.obj U) :
    add.app U (FunctorToTypes.prodMk s t) = add.app U (FunctorToTypes.prodMk t s)

/-- A source-facing presentation of abelian-presheaf structure on `F` by presheaf maps `0`, `-`,
and `+`, together with sectionwise abelian-group structures for which those maps are the
corresponding operations. -/
structure CompatibleAddCommGroupMapStructure {X : TopCat.{u}} (F : X.Presheaf (Type v)) where
  /-- The zero section as a morphism from the terminal presheaf. -/
  zero : ((PUnit : Type v) ₚ X : X.Presheaf (Type v)) ⟶ F
  /-- The inverse map of presheaves. -/
  neg : F ⟶ F
  /-- The addition morphism of presheaves. -/
  add : F ⨯ F ⟶ F
  /-- The sectionwise abelian-group structures defined by these three presheaf maps. -/
  addCommGroup (U : (Opens X)ᵒᵖ) : AddCommGroup (F.obj U)
  /-- The zero morphism agrees with the zero section in the chosen sectionwise abelian group. -/
  zero_eq (U : (Opens X)ᵒᵖ) :
    by
      let _ := addCommGroup U
      exact zero.app U PUnit.unit = (0 : F.obj U)
  /-- The inverse morphism agrees with additive inverse in the chosen sectionwise abelian group. -/
  neg_eq (U : (Opens X)ᵒᵖ) (s : F.obj U) :
    by
      let _ := addCommGroup U
      exact neg.app U s = (-s : F.obj U)
  /-- The addition morphism agrees with addition in the chosen sectionwise abelian group. -/
  add_eq (U : (Opens X)ᵒᵖ) (s t : F.obj U) :
    by
      let _ := addCommGroup U
      exact add.app U (FunctorToTypes.prodMk s t) = (s + t : F.obj U)

/-- A source-facing addition-first presentation of abelian-presheaf structure on `F`: the only
primitive map is `+ : F × F ⟶ F`, and on every open this addition map is required to be the
addition law of an abelian-group structure on the sections. -/
structure CompatibleAdditionMapStructure {X : TopCat.{u}} (F : X.Presheaf (Type v)) where
  /-- The addition law as a presheaf morphism. -/
  add : F ⨯ F ⟶ F
  /-- The sectionwise abelian-group structures defined by this addition map. -/
  addCommGroup (U : (Opens X)ᵒᵖ) : AddCommGroup (F.obj U)
  /-- The addition morphism agrees with addition in the chosen sectionwise abelian group. -/
  add_eq (U : (Opens X)ᵒᵖ) (s t : F.obj U) :
    by
      let _ := addCommGroup U
      exact add.app U (FunctorToTypes.prodMk s t) = (s + t : F.obj U)

/-- A compatible additive commutative group structure on `F` induces additive commutative group
structures on all section sets of `F`. -/
instance instAddCommGroupSections {X : TopCat.{u}} {F : X.Presheaf (Type v)}
    (hF : CompatibleAddCommGroupStructure F) (U : Opens X) : AddCommGroup (F.obj (op U)) :=
  hF.addCommGroup (op U)

private theorem map_prodMk {X : TopCat.{u}} {F G : X.Presheaf (Type v)}
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s : F.obj U) (t : G.obj U) :
    (F ⨯ G).map i (FunctorToTypes.prodMk s t) =
      FunctorToTypes.prodMk (F.map i s) (G.map i t) := by
  -- Compare both sides through the product projections, where the map is componentwise.
  apply FunctorToTypes.prod_ext' (F := F) (G := G) V
  · calc
      ((Limits.prod.fst (X := F)).app V) ((F ⨯ G).map i (FunctorToTypes.prodMk s t))
          = F.map i (((Limits.prod.fst (X := F)).app U) (FunctorToTypes.prodMk s t)) := by
              simpa using congr_fun ((Limits.prod.fst (X := F)).naturality i)
                (FunctorToTypes.prodMk s t)
      _ = F.map i s := by
            exact congrArg (F.map i) (FunctorToTypes.prodMk_fst (F := F) (G := G) s t)
      _ = ((Limits.prod.fst (X := F)).app V) (FunctorToTypes.prodMk (F.map i s) (G.map i t)) := by
            exact (FunctorToTypes.prodMk_fst (F := F) (G := G) (F.map i s) (G.map i t)).symm
  · calc
      ((Limits.prod.snd (X := F)).app V) ((F ⨯ G).map i (FunctorToTypes.prodMk s t))
          = G.map i (((Limits.prod.snd (X := F)).app U) (FunctorToTypes.prodMk s t)) := by
              simpa using congr_fun ((Limits.prod.snd (X := F)).naturality i)
                (FunctorToTypes.prodMk s t)
      _ = G.map i t := by
            exact congrArg (G.map i) (FunctorToTypes.prodMk_snd (F := F) (G := G) s t)
      _ = ((Limits.prod.snd (X := F)).app V) (FunctorToTypes.prodMk (F.map i s) (G.map i t)) := by
            exact (FunctorToTypes.prodMk_snd (F := F) (G := G) (F.map i s) (G.map i t)).symm

@[simp]
theorem binaryProductIso_hom_app_prodMk {X : TopCat.{u}} {F G : X.Presheaf (Type v)}
    (U : (Opens X)ᵒᵖ) (s : F.obj U) (t : G.obj U) :
    (FunctorToTypes.binaryProductIso F G).hom.app U (FunctorToTypes.prodMk s t) = (s, t) := by
  ext <;> simp [FunctorToTypes.prodMk]

namespace CompatibleAddCommGroupStructure

variable {X : TopCat.{u}} {F : X.Presheaf (Type v)}

/-- Restriction maps preserve the zero section. -/
theorem map_zero (hF : CompatibleAddCommGroupStructure F) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    F.map i ((hF.addCommGroup U).zero) = (hF.addCommGroup V).zero := by
  let _ := hF.addCommGroup U
  let _ := hF.addCommGroup V
  let f : F.obj U →+ F.obj V := AddMonoidHom.mk' (F.map i) (hF.map_add i)
  exact f.map_zero

/-- Restriction maps preserve additive inverses. -/
theorem map_neg (hF : CompatibleAddCommGroupStructure F) {U V : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (s : F.obj U) :
    F.map i ((hF.addCommGroup U).neg s) = (hF.addCommGroup V).neg (F.map i s) := by
  let _ := hF.addCommGroup U
  let _ := hF.addCommGroup V
  let f : F.obj U →+ F.obj V := AddMonoidHom.mk' (F.map i) (hF.map_add i)
  exact f.map_neg s

public def zeroNatTrans (hF : CompatibleAddCommGroupStructure F) :
    ((PUnit : Type v) ₚ X : X.Presheaf (Type v)) ⟶ F where
  app U _ := by
    let _ := hF.addCommGroup U
    exact 0
  naturality := by
    intro U V i
    funext x
    cases x
    exact (hF.map_zero i).symm

public def negNatTrans (hF : CompatibleAddCommGroupStructure F) : F ⟶ F where
  app U s := by
    let _ := hF.addCommGroup U
    exact -s
  naturality := by
    intro U V i
    funext s
    exact (hF.map_neg i s).symm

public def addNatTrans (hF : CompatibleAddCommGroupStructure F) :
    FunctorToTypes.prod F F ⟶ F where
  app U z := by
    let _ := hF.addCommGroup U
    exact z.1 + z.2
  naturality := by
    intro U V i
    funext z
    exact (hF.map_add i z.1 z.2).symm

/-- The `0`, `-`, `+`-axiom presentation attached to a compatible sectionwise abelian-group
structure. -/
noncomputable def toCompatibleAddCommGroupMaps (hF : CompatibleAddCommGroupStructure F) :
    CompatibleAddCommGroupMaps F where
  zero := zeroNatTrans hF
  neg := negNatTrans hF
  add := (FunctorToTypes.binaryProductIso F F).hom ≫ addNatTrans hF
  zero_add U s := by
    let _ := hF.addCommGroup U
    simp [zeroNatTrans, addNatTrans]
  add_zero U s := by
    let _ := hF.addCommGroup U
    simp [zeroNatTrans, addNatTrans]
  add_assoc U s t u := by
    let _ := hF.addCommGroup U
    simp [addNatTrans, add_assoc]
  add_left_neg U s := by
    let _ := hF.addCommGroup U
    simp [zeroNatTrans, negNatTrans, addNatTrans]
  add_comm U s t := by
    let _ := hF.addCommGroup U
    simpa [addNatTrans] using (add_comm s t)

/-- The `0`, `-`, `+` map-and-structure presentation attached to a compatible sectionwise
abelian-group structure. -/
noncomputable def toCompatibleAddCommGroupMapStructure (hF : CompatibleAddCommGroupStructure F) :
    CompatibleAddCommGroupMapStructure F where
  zero := zeroNatTrans hF
  neg := negNatTrans hF
  add := (FunctorToTypes.binaryProductIso F F).hom ≫ addNatTrans hF
  addCommGroup := hF.addCommGroup
  zero_eq U := by
    let _ := hF.addCommGroup U
    simp [zeroNatTrans]
  neg_eq U s := by
    let _ := hF.addCommGroup U
    simp [negNatTrans]
  add_eq U s t := by
    let _ := hF.addCommGroup U
    simp [addNatTrans]

/-- The addition-first presentation attached to a compatible sectionwise abelian-group structure. -/
noncomputable def toCompatibleAdditionMapStructure (hF : CompatibleAddCommGroupStructure F) :
    CompatibleAdditionMapStructure F where
  add := (FunctorToTypes.binaryProductIso F F).hom ≫ addNatTrans hF
  addCommGroup := hF.addCommGroup
  add_eq U s t := by
    let _ := hF.addCommGroup U
    simp [addNatTrans]

/-- The canonical lift of a compatible sectionwise abelian-group structure on a set-valued
presheaf to the chapter owner `PAb(X)`. -/
noncomputable def toPAb (hF : CompatibleAddCommGroupStructure F) : PAb(X) where
  obj U := by
    let _ := hF.addCommGroup U
    exact AddCommGrpCat.of (F.obj U)
  map {U V} i := by
    let _ := hF.addCommGroup U
    let _ := hF.addCommGroup V
    exact AddCommGrpCat.ofHom <| AddMonoidHom.mk' (F.map i) (hF.map_add i)
  map_id := by
    intro U
    apply AddCommGrpCat.ext
    intro s
    simpa using congr_fun (F.map_id U) s
  map_comp := by
    intro U V W i j
    apply AddCommGrpCat.ext
    intro s
    simpa using congr_fun (F.map_comp i j) s

/-- Forgetting the canonical `PAb(X)`-lift recovers the original set-valued presheaf. -/
theorem toPAb_forget (hF : CompatibleAddCommGroupStructure F) :
    hF.toPAb ⋙ forget AddCommGrpCat = F := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro U V i
  ext s
  rfl

/-- Every `PAb(X)`-valued presheaf induces the compatible sectionwise abelian-group structure on its
underlying set-valued presheaf. -/
noncomputable def ofPAb (ℱ : PAb(X)) :
    CompatibleAddCommGroupStructure (ℱ ⋙ forget AddCommGrpCat) where
  addCommGroup U := by
    change AddCommGroup (ℱ.obj U)
    infer_instance
  map_add := by
    intro U V i s t
    change (ℱ.map i).hom (s + t) = (ℱ.map i).hom s + (ℱ.map i).hom t
    exact (ℱ.map i).hom.map_add s t

/-- Helper for Lemma 6.4.3: rebuilding the sectionwise compatible structure from its canonical
`PAb(X)` lift returns the original structure. -/
theorem ofPAb_toPAb (hF : CompatibleAddCommGroupStructure F) :
    CompatibleAddCommGroupStructure.ofPAb hF.toPAb = hF := by
  -- The canonical lift stores exactly the original sectionwise group laws and additive
  -- restriction maps.
  cases hF
  rfl

/-- Helper for Lemma 6.4.3: converting a `PAb(X)`-valued presheaf to its underlying compatible
sectionwise structure and lifting back recovers the original `PAb(X)` object. -/
theorem toPAb_ofPAb (ℱ : PAb(X)) :
    (CompatibleAddCommGroupStructure.ofPAb ℱ).toPAb = ℱ := by
  -- Objectwise the lift is unchanged, and on morphisms both sides are the same additive maps.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro U V i
  apply AddCommGrpCat.ext
  intro s
  rfl

end CompatibleAddCommGroupStructure

/-- Helper for Lemma 6.4.3: a morphism out of a product presheaf is determined by its values on
elements built from `FunctorToTypes.prodMk`. -/
private theorem prod_hom_ext {X : TopCat.{u}} {F G H : X.Presheaf (Type v)}
    {α β : F ⨯ G ⟶ H}
    (h : ∀ U s t, α.app U (FunctorToTypes.prodMk s t) = β.app U (FunctorToTypes.prodMk s t)) :
    α = β := by
  -- Every element of the product presheaf is a `prodMk` of its two projections.
  apply CategoryTheory.NatTrans.ext
  funext U z
  rw [show z =
      FunctorToTypes.prodMk ((Limits.prod.fst (X := F)).app U z)
        ((Limits.prod.snd (X := F)).app U z) by
      apply FunctorToTypes.prod_ext' (F := F) (G := G) U
      · rw [FunctorToTypes.prodMk_fst]
        rfl
      · rw [FunctorToTypes.prodMk_snd]
        rfl]
  exact h U _ _

namespace CompatibleAddCommGroupMaps

variable {X : TopCat.{u}} {F : X.Presheaf (Type v)}

/-- The `0`, `-`, `+` map-and-structure presentation attached to the `0`, `-`, `+`-axiom
presentation. -/
noncomputable def toCompatibleAddCommGroupMapStructure (hF : CompatibleAddCommGroupMaps F) :
    CompatibleAddCommGroupMapStructure F where
  zero := hF.zero
  neg := hF.neg
  add := hF.add
  addCommGroup U := by
    let _ : Zero (F.obj U) := ⟨hF.zero.app U PUnit.unit⟩
    let _ : Add (F.obj U) := ⟨fun s t ↦ hF.add.app U (FunctorToTypes.prodMk s t)⟩
    let _ : Neg (F.obj U) := ⟨hF.neg.app U⟩
    exact
      { AddGroup.ofLeftAxioms (hF.add_assoc U) (hF.zero_add U) (hF.add_left_neg U) with
        add_comm := hF.add_comm U }
  zero_eq U := rfl
  neg_eq U s := rfl
  add_eq U s t := rfl

/-- The sectionwise abelian-group presentation attached to the `0`, `-`, `+`-axiom presentation.
-/
noncomputable def toCompatibleAddCommGroupStructure (hF : CompatibleAddCommGroupMaps F) :
    CompatibleAddCommGroupStructure F where
  addCommGroup := hF.toCompatibleAddCommGroupMapStructure.addCommGroup
  map_add := by
    intro U V i s t
    let hG := hF.toCompatibleAddCommGroupMapStructure
    let _ := hG.addCommGroup U
    let _ := hG.addCommGroup V
    have h := congr_fun (hF.add.naturality i) (FunctorToTypes.prodMk s t)
    simpa [Function.comp, map_prodMk i s t, hG.add_eq U s t,
      hG.add_eq V (F.map i s) (F.map i t)] using h.symm

/-- Helper for Lemma 6.4.3: rebuilding the `0`, `-`, `+`-axiom presentation from its underlying
compatible sectionwise structure recovers the original primitive maps. -/
theorem toCompatibleAddCommGroupStructure_toCompatibleAddCommGroupMaps
    (hF : CompatibleAddCommGroupMaps F) :
    CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMaps
      (CompatibleAddCommGroupMaps.toCompatibleAddCommGroupStructure hF) = hF := by
  -- The primitive `0`, `-`, `+` maps are reconstructed pointwise from the induced abelian-group
  -- structure on each section.
  cases hF with
  | mk zero neg add zero_add add_zero add_assoc add_left_neg add_comm =>
      let hG : CompatibleAddCommGroupStructure F :=
        CompatibleAddCommGroupMaps.toCompatibleAddCommGroupStructure
          { zero := zero
            neg := neg
            add := add
            zero_add := zero_add
            add_zero := add_zero
            add_assoc := add_assoc
            add_left_neg := add_left_neg
            add_comm := add_comm }
      let hRec : CompatibleAddCommGroupMaps F :=
        CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMaps hG
      change hRec = {
        zero := zero
        neg := neg
        add := add
        zero_add := zero_add
        add_zero := add_zero
        add_assoc := add_assoc
        add_left_neg := add_left_neg
        add_comm := add_comm }
      rw [CompatibleAddCommGroupMaps.mk.injEq]
      have hzero : hRec.zero = zero := by
        rfl
      have hneg : hRec.neg = neg := by
        rfl
      have hadd : hRec.add = add := by
        apply prod_hom_ext
        intro U s t
        let _ := hG.addCommGroup U
        trans (s + t : F.obj U)
        · exact (CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMapStructure hG).add_eq U s t
        · rfl
      exact ⟨hzero, hneg, hadd⟩

end CompatibleAddCommGroupMaps

namespace CompatibleAddCommGroupMapStructure

variable {X : TopCat.{u}} {F : X.Presheaf (Type v)}

/-- The zero presheaf map agrees pointwise with the zero section of the induced sectionwise
abelian-group structure. -/
theorem zero_app_eq_zero (hF : CompatibleAddCommGroupMapStructure F) (U : (Opens X)ᵒᵖ) :
    by
      let _ := hF.addCommGroup U
      exact hF.zero.app U PUnit.unit = (0 : F.obj U) := by
  exact hF.zero_eq U

/-- The inverse presheaf map agrees pointwise with additive inverse in the induced sectionwise
abelian-group structure. -/
theorem neg_app_eq_neg (hF : CompatibleAddCommGroupMapStructure F) (U : (Opens X)ᵒᵖ)
    (s : F.obj U) :
    by
      let _ := hF.addCommGroup U
      exact hF.neg.app U s = (-s : F.obj U) := by
  exact hF.neg_eq U s

/-- The addition presheaf map agrees pointwise with addition in the induced sectionwise
abelian-group structure. -/
theorem add_app_eq_add (hF : CompatibleAddCommGroupMapStructure F) (U : (Opens X)ᵒᵖ)
    (s t : F.obj U) :
    by
      let _ := hF.addCommGroup U
      exact hF.add.app U (FunctorToTypes.prodMk s t) = (s + t : F.obj U) := by
  exact hF.add_eq U s t

/-- The `0`, `-`, `+`-axiom presentation attached to the `0`, `-`, `+` map-and-structure
presentation. -/
noncomputable def toCompatibleAddCommGroupMaps (hF : CompatibleAddCommGroupMapStructure F) :
    CompatibleAddCommGroupMaps F where
  zero := hF.zero
  neg := hF.neg
  add := hF.add
  zero_add U s := by
    let _ := hF.addCommGroup U
    rw [hF.zero_app_eq_zero U, hF.add_app_eq_add U]
    exact zero_add s
  add_zero U s := by
    let _ := hF.addCommGroup U
    rw [hF.zero_app_eq_zero U, hF.add_app_eq_add U]
    exact add_zero s
  add_assoc U s t u := by
    let _ := hF.addCommGroup U
    rw [hF.add_app_eq_add U, hF.add_app_eq_add U, hF.add_app_eq_add U, hF.add_app_eq_add U]
    exact add_assoc s t u
  add_left_neg U s := by
    let _ := hF.addCommGroup U
    rw [hF.neg_app_eq_neg U s, hF.zero_app_eq_zero U, hF.add_app_eq_add U]
    exact neg_add_cancel s
  add_comm U s t := by
    let _ := hF.addCommGroup U
    rw [hF.add_app_eq_add U, hF.add_app_eq_add U]
    exact add_comm s t

/-- The sectionwise abelian-group presentation attached to the `0`, `-`, `+` map-and-structure
presentation. -/
noncomputable def toCompatibleAddCommGroupStructure (hF : CompatibleAddCommGroupMapStructure F) :
    CompatibleAddCommGroupStructure F where
  addCommGroup := hF.addCommGroup
  map_add := by
    intro U V i s t
    let _ := hF.addCommGroup U
    let _ := hF.addCommGroup V
    have h := congr_fun (hF.add.naturality i) (FunctorToTypes.prodMk s t)
    simpa [Function.comp, map_prodMk i s t, hF.add_app_eq_add U s t,
      hF.add_app_eq_add V (F.map i s) (F.map i t)] using h.symm

/-- Helper for Lemma 6.4.3: rebuilding the map-and-structure presentation from its underlying
compatible sectionwise structure recovers the original primitive maps. -/
theorem toCompatibleAddCommGroupStructure_toCompatibleAddCommGroupMapStructure
    (hF : CompatibleAddCommGroupMapStructure F) :
    CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMapStructure
      (CompatibleAddCommGroupMapStructure.toCompatibleAddCommGroupStructure hF) = hF := by
  -- The primitive `0`, `-`, `+` maps are recovered pointwise from the chosen sectionwise groups.
  cases hF with
  | mk zero neg add addCommGroup zero_eq neg_eq add_eq =>
      let hRec : CompatibleAddCommGroupMapStructure F :=
        CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMapStructure
          (CompatibleAddCommGroupMapStructure.toCompatibleAddCommGroupStructure
            { zero := zero
              neg := neg
              add := add
              addCommGroup := addCommGroup
              zero_eq := zero_eq
              neg_eq := neg_eq
              add_eq := add_eq })
      change hRec = {
        zero := zero
        neg := neg
        add := add
        addCommGroup := addCommGroup
        zero_eq := zero_eq
        neg_eq := neg_eq
        add_eq := add_eq }
      rw [CompatibleAddCommGroupMapStructure.mk.injEq]
      have hzero : hRec.zero = zero := by
        apply CategoryTheory.NatTrans.ext
        funext U x
        cases x
        trans (0 : F.obj U)
        · exact hRec.zero_eq U
        · exact (zero_eq U).symm
      have hneg : hRec.neg = neg := by
        apply CategoryTheory.NatTrans.ext
        funext U s
        trans (-s : F.obj U)
        · exact hRec.neg_eq U s
        · exact (neg_eq U s).symm
      have hadd : hRec.add = add := by
        apply prod_hom_ext
        intro U s t
        trans (s + t : F.obj U)
        · exact hRec.add_eq U s t
        · exact (add_eq U s t).symm
      exact ⟨hzero, hneg, hadd, rfl⟩

end CompatibleAddCommGroupMapStructure

namespace CompatibleAdditionMapStructure

variable {X : TopCat.{u}} {F : X.Presheaf (Type v)}

/-- The addition presheaf map agrees pointwise with addition in the induced sectionwise
abelian-group structure. -/
theorem add_app_eq_add (hF : CompatibleAdditionMapStructure F) (U : (Opens X)ᵒᵖ)
    (s t : F.obj U) :
    by
      let _ := hF.addCommGroup U
      exact hF.add.app U (FunctorToTypes.prodMk s t) = (s + t : F.obj U) := by
  exact hF.add_eq U s t

/-- The sectionwise abelian-group presentation attached to an addition-first presheaf-map
presentation. -/
noncomputable def toCompatibleAddCommGroupStructure (hF : CompatibleAdditionMapStructure F) :
    CompatibleAddCommGroupStructure F where
  addCommGroup := hF.addCommGroup
  map_add := by
    intro U V i s t
    let _ := hF.addCommGroup U
    let _ := hF.addCommGroup V
    have h := congr_fun (hF.add.naturality i) (FunctorToTypes.prodMk s t)
    simpa [Function.comp, map_prodMk i s t, hF.add_app_eq_add U s t,
      hF.add_app_eq_add V (F.map i s) (F.map i t)] using h.symm

/-- Helper for Lemma 6.4.3: rebuilding the addition-first presentation from its underlying
compatible sectionwise structure recovers the original addition map. -/
theorem toCompatibleAddCommGroupStructure_toCompatibleAdditionMapStructure
    (hF : CompatibleAdditionMapStructure F) :
    CompatibleAddCommGroupStructure.toCompatibleAdditionMapStructure
      (CompatibleAdditionMapStructure.toCompatibleAddCommGroupStructure hF) = hF := by
  -- The addition map is reconstructed pointwise from the chosen sectionwise abelian-group law.
  cases hF with
  | mk add addCommGroup add_eq =>
      let hRec : CompatibleAdditionMapStructure F :=
        CompatibleAddCommGroupStructure.toCompatibleAdditionMapStructure
          (CompatibleAdditionMapStructure.toCompatibleAddCommGroupStructure
            { add := add
              addCommGroup := addCommGroup
              add_eq := add_eq })
      change hRec = { add := add, addCommGroup := addCommGroup, add_eq := add_eq }
      rw [CompatibleAdditionMapStructure.mk.injEq]
      have hadd : hRec.add = add := by
        apply prod_hom_ext
        intro U s t
        trans (s + t : F.obj U)
        · exact hRec.add_eq U s t
        · exact (add_eq U s t).symm
      exact ⟨hadd, rfl⟩

end CompatibleAdditionMapStructure

/-- Helper for Lemma 6.4.3: passing through the map-and-structure presentation does not change a
compatible sectionwise abelian-group structure. -/
theorem CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMapStructure_toCompatibleAddCommGroupStructure
    {X : TopCat.{u}} {F : X.Presheaf (Type v)} (hF : CompatibleAddCommGroupStructure F) :
    CompatibleAddCommGroupMapStructure.toCompatibleAddCommGroupStructure
      (hF.toCompatibleAddCommGroupMapStructure) = hF := by
  -- The sectionwise groups and additive restriction maps are carried through unchanged.
  rw [CompatibleAddCommGroupStructure.mk.injEq]
  rfl

/-- Helper for Lemma 6.4.3: passing through the `0`, `-`, `+`-axiom presentation does not change a
compatible sectionwise abelian-group structure. -/
theorem CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMaps_toCompatibleAddCommGroupStructure
    {X : TopCat.{u}} {F : X.Presheaf (Type v)} (hF : CompatibleAddCommGroupStructure F) :
    CompatibleAddCommGroupMaps.toCompatibleAddCommGroupStructure (hF.toCompatibleAddCommGroupMaps) =
      hF := by
  -- The induced `0`, `-`, `+` maps are built from the same sectionwise additive law.
  rw [CompatibleAddCommGroupStructure.mk.injEq]
  funext U
  let hG := hF.toCompatibleAddCommGroupMapStructure
  -- The rebuilt group law is the same pointwise addition recorded by the map-and-structure view.
  apply AddCommGroup.ext
  funext s t
  exact hG.add_eq U s t

/-- Helper for Lemma 6.4.3: passing through the addition-first presentation does not change a
compatible sectionwise abelian-group structure. -/
theorem CompatibleAddCommGroupStructure.toCompatibleAdditionMapStructure_toCompatibleAddCommGroupStructure
    {X : TopCat.{u}} {F : X.Presheaf (Type v)} (hF : CompatibleAddCommGroupStructure F) :
    CompatibleAdditionMapStructure.toCompatibleAddCommGroupStructure
      (hF.toCompatibleAdditionMapStructure) = hF := by
  -- Only the addition map is recorded, and it is rebuilt from the same sectionwise law.
  rw [CompatibleAddCommGroupStructure.mk.injEq]
  rfl

variable {X : TopCat.{u}} (F : X.Presheaf (Type v))

/-- Lemma 6.4.3, core owner form: compatible sectionwise abelian-group structures on the fixed
set-valued presheaf `F` are equivalent to lifts of `F` to the canonical abelian-presheaf owner
`PAb(X)`. -/
noncomputable def compatible_add_comm_group_structure_equiv_pabLift :
    CompatibleAddCommGroupStructure F ≃ { ℱ : PAb(X) // ℱ ⋙ forget AddCommGrpCat = F } where
  toFun hF := ⟨hF.toPAb, hF.toPAb_forget⟩
  invFun hF := by
    rcases hF with ⟨ℱ, hℱ⟩
    cases hℱ
    exact CompatibleAddCommGroupStructure.ofPAb ℱ
  left_inv hF := by
    -- The core lift forgets back to `F`, so the inverse just rebuilds the same structure.
    simpa using CompatibleAddCommGroupStructure.ofPAb_toPAb hF
  right_inv hF := by
    -- Equality in the subtype reduces to equality of the underlying `PAb(X)` lifts.
    rcases hF with ⟨ℱ, hℱ⟩
    cases hℱ
    apply Subtype.ext
    simpa using CompatibleAddCommGroupStructure.toPAb_ofPAb ℱ

/-- Lemma 6.4.3, source item (3): presheaf maps `0`, `-`, `+` whose pointwise values define
sectionwise abelian-group structures are equivalent to lifts of `F` to the canonical owner
`PAb(X)`. -/
noncomputable def compatible_add_comm_group_map_structure_equiv_pabLift :
    CompatibleAddCommGroupMapStructure F ≃ { ℱ : PAb(X) // ℱ ⋙ forget AddCommGrpCat = F } where
  toFun hF :=
    compatible_add_comm_group_structure_equiv_pabLift F
      hF.toCompatibleAddCommGroupStructure
  invFun hF :=
    CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMapStructure <|
      (compatible_add_comm_group_structure_equiv_pabLift F).symm hF
  left_inv hF := by
    -- The round trip only forgets to the compatible structure and then rebuilds the same maps.
    simpa using
      CompatibleAddCommGroupMapStructure.toCompatibleAddCommGroupStructure_toCompatibleAddCommGroupMapStructure
        hF
  right_inv hF := by
    -- Reduce to the core owner equivalence after identifying the unchanged compatible structure.
    rcases hF with ⟨ℱ, hℱ⟩
    cases hℱ
    apply Subtype.ext
    simpa [CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMapStructure_toCompatibleAddCommGroupStructure] using
      CompatibleAddCommGroupStructure.toPAb_ofPAb ℱ

/-- Lemma 6.4.3, source item (2): presheaf maps `0`, `-`, `+` satisfying the usual abelian-group
axioms are equivalent to lifts of `F` to the canonical owner `PAb(X)`. -/
noncomputable def compatible_add_comm_group_maps_equiv_pabLift :
    CompatibleAddCommGroupMaps F ≃ { ℱ : PAb(X) // ℱ ⋙ forget AddCommGrpCat = F } where
  toFun hF :=
    compatible_add_comm_group_structure_equiv_pabLift F
      hF.toCompatibleAddCommGroupStructure
  invFun hF :=
    CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMaps <|
      (compatible_add_comm_group_structure_equiv_pabLift F).symm hF
  left_inv hF := by
    -- The round trip rebuilds the same `0`, `-`, `+` maps from the induced compatible structure.
    simpa using
      CompatibleAddCommGroupMaps.toCompatibleAddCommGroupStructure_toCompatibleAddCommGroupMaps hF
  right_inv hF := by
    -- Reduce to the core owner equivalence after identifying the unchanged compatible structure.
    rcases hF with ⟨ℱ, hℱ⟩
    cases hℱ
    apply Subtype.ext
    simpa [CompatibleAddCommGroupStructure.toCompatibleAddCommGroupMaps_toCompatibleAddCommGroupStructure] using
      CompatibleAddCommGroupStructure.toPAb_ofPAb ℱ

/-- Lemma 6.4.3, source item (4): an addition map `+ : F × F ⟶ F` whose pointwise values define
sectionwise abelian-group structures is equivalent to a lift of `F` to the canonical owner
`PAb(X)`. -/
noncomputable def compatible_addition_map_structure_equiv_pabLift :
    CompatibleAdditionMapStructure F ≃ { ℱ : PAb(X) // ℱ ⋙ forget AddCommGrpCat = F } where
  toFun hF :=
    compatible_add_comm_group_structure_equiv_pabLift F
      hF.toCompatibleAddCommGroupStructure
  invFun hF :=
    CompatibleAddCommGroupStructure.toCompatibleAdditionMapStructure <|
      (compatible_add_comm_group_structure_equiv_pabLift F).symm hF
  left_inv hF := by
    -- The addition map is rebuilt pointwise from the same sectionwise additive law.
    simpa using
      CompatibleAdditionMapStructure.toCompatibleAddCommGroupStructure_toCompatibleAdditionMapStructure
        hF
  right_inv hF := by
    -- Reduce to the core owner equivalence after identifying the unchanged compatible structure.
    rcases hF with ⟨ℱ, hℱ⟩
    cases hℱ
    apply Subtype.ext
    simpa [CompatibleAddCommGroupStructure.toCompatibleAdditionMapStructure_toCompatibleAddCommGroupStructure] using
      CompatibleAddCommGroupStructure.toPAb_ofPAb ℱ

/-- Lemma 6.4.3, source item (3), as a derived source-facing comparison obtained from the common
equivalence with lifts to `PAb(X)`. -/
noncomputable def compatible_add_comm_group_structure_equiv_map_structure :
    CompatibleAddCommGroupStructure F ≃ CompatibleAddCommGroupMapStructure F :=
  (compatible_add_comm_group_structure_equiv_pabLift F).trans
    (compatible_add_comm_group_map_structure_equiv_pabLift F).symm

/-- Lemma 6.4.3, source items (2) and (3), as a derived source-facing comparison obtained from the
common equivalence with lifts to `PAb(X)`. -/
noncomputable def compatible_add_comm_group_maps_equiv_map_structure :
    CompatibleAddCommGroupMaps F ≃ CompatibleAddCommGroupMapStructure F :=
  (compatible_add_comm_group_maps_equiv_pabLift F).trans
    (compatible_add_comm_group_map_structure_equiv_pabLift F).symm

/-- Lemma 6.4.3, source items (1) and (2), as a derived source-facing comparison obtained from the
common equivalence with lifts to `PAb(X)`. -/
noncomputable def compatible_add_comm_group_structure_equiv_maps :
    CompatibleAddCommGroupStructure F ≃ CompatibleAddCommGroupMaps F :=
  (compatible_add_comm_group_structure_equiv_pabLift F).trans
    (compatible_add_comm_group_maps_equiv_pabLift F).symm

/-- Lemma 6.4.3, source item (4), as a derived source-facing comparison obtained from the common
equivalence with lifts to `PAb(X)`. -/
noncomputable def compatible_add_comm_group_structure_equiv_addition_map_structure :
    CompatibleAddCommGroupStructure F ≃ CompatibleAdditionMapStructure F :=
  (compatible_add_comm_group_structure_equiv_pabLift F).trans
    (compatible_addition_map_structure_equiv_pabLift F).symm
