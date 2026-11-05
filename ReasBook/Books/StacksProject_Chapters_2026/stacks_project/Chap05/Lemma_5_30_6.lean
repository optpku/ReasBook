module

public import stacks_project.Chap05.Lemma_5_30_3
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.MonCat.Colimits
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Topology.Algebra.Group.GroupTopology
import Mathlib.Topology.Category.TopCat.Adjunctions
import Mathlib.Topology.Category.TopCat.Monoidal

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped GrpObj MonObj

universe u

/- Domain-style sampling for topological groups:
- primary domain: category-theoretic colimits of topological groups, organized canonically as
  group objects in `TopCat`
- sampled declarations in the same owner layer:
  `Grp TopCat`,
  `GroupTopology.coinduced`,
  `MonCat.Colimits.colimitCocone`,
  `MonCat.Colimits.colimitIsColimit`,
  `preservesColimit_of_preserves_colimit_cocone`
- best owner abstraction: `Grp TopCat`, with the underlying `GrpCat` colimit as primitive algebraic
  data and the coarsest compatible group topology as the topological bridge

Layer triage:
- `source-facing`: Lemma 5.30.6 asserts that `Grp TopCat` has colimits and that the forgetful
  functor to `GrpCat` preserves them
- `core/canonical`: the owner `Grp TopCat` and the forgetful bridge `forget₂ (Grp TopCat) GrpCat`
- `bridge/view`: the underlying `MonCat` colimit equipped first with its induced group structure and
  then with the infimum of the coinduced group topologies from the cocone maps

Primitive-vs-derived split:
- primitive data: the `MonCat` colimit carrier for the underlying group diagram, the induced
  inversion, and the resulting coinduced `GroupTopology` on that carrier
- derived API: the owner instances `HasColimits (Grp TopCat)` and
  `PreservesColimits (forget₂ (Grp TopCat) GrpCat)`
- the public surface should therefore install those owner instances directly, with the conjunction
  theorem kept only as a secondary summary
-/

namespace TopologicalGroupCat

noncomputable section

open MonCat.Colimits

variable {J : Type u} [Category.{u} J]

private abbrev underlyingMonoidDiagram (F : J ⥤ Grp TopCat.{u}) :=
  F ⋙ forget₂ (Grp TopCat.{u}) GrpCat.{u} ⋙ forget₂ GrpCat.{u} MonCat.{u}

private abbrev underlyingGrpDiagram (F : J ⥤ Grp TopCat.{u}) :=
  F ⋙ forget₂ (Grp TopCat.{u}) GrpCat.{u}

/-- Helper for Lemma 5.30.6: every object in the underlying monoid diagram already carries the
ambient group structure coming from `GrpCat`. -/
private instance underlyingMonoidDiagram_obj_group (F : J ⥤ Grp TopCat.{u}) (j : J) :
    Group ((underlyingMonoidDiagram F).obj j) := by
  change Group ((underlyingGrpDiagram F).obj j)
  infer_instance

/-- Helper for Lemma 5.30.6: align the group structure on the topological carrier with the one
seen after forgetting to `GrpCat`. -/
private instance (priority := 100) carrierGroupFromUnderlyingGrpDiagram
    (F : J ⥤ Grp TopCat.{u}) (j : J) : Group (F.obj j).X := by
  change Group ((underlyingGrpDiagram F).obj j)
  infer_instance

/-- Helper for Lemma 5.30.6: the multiplication used on the topological carrier. -/
private abbrev carrierMul (X : Grp TopCat.{u}) : X.X → X.X → X.X :=
  fun a b ↦ (TopCat.Hom.hom μ[X.X]) (a, b)

/-- Helper for Lemma 5.30.6: the multiplication used after forgetting a topological group to
`GrpCat`. -/
private abbrev forgetMul (X : Grp TopCat.{u}) :
    (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X →
      (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X →
      (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X :=
  fun a b ↦ (TopCat.Hom.hom μ[X.X]) ((a : X.X), (b : X.X))

/-- Helper for Lemma 5.30.6: the multiplication used by the `mapGrp` presentation of the forgotten
topological space. -/
private abbrev mapGrpMul (X : Grp TopCat.{u}) [_instMonoidal : (forget TopCat.{u}).Monoidal] :
    ((forget TopCat.{u}).mapGrp.obj X).X →
      ((forget TopCat.{u}).mapGrp.obj X).X →
      ((forget TopCat.{u}).mapGrp.obj X).X :=
  fun a b ↦ (TopCat.Hom.hom μ[X.X]) ((a : X.X), (b : X.X))

/-- Helper for Lemma 5.30.6: multiplying in the topological carrier and then forgetting to
`GrpCat` agrees with multiplying in the forgotten group object. -/
private theorem carrier_mul_as_forget_mul (X : Grp TopCat.{u}) (a b : X.X) :
    ((carrierMul X a b : X.X) : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) =
      forgetMul X (a : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)
        (b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) := by
  rfl

/-- Helper for Lemma 5.30.6: multiplying in the forgotten group object and then reading the
result back on the topological carrier agrees with the carrier multiplication. -/
private theorem forget_mul_as_carrier_mul (X : Grp TopCat.{u})
    (a b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) :
    ((forgetMul X a b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) : X.X) =
      carrierMul X (a : X.X) (b : X.X) := by
  rfl

/-- Helper for Lemma 5.30.6: the monoidal comparison map for `forget TopCat` sends a pair to the
same pair on underlying types. -/
private theorem forget_monoidal_mu_eq_pair (X : Grp TopCat.{u})
    [_instMonoidal : (forget TopCat.{u}).Monoidal]
    (a b : ((forget TopCat.{u}).mapGrp.obj X).X) :
    Functor.LaxMonoidal.μ (forget TopCat.{u}) X.X X.X (a, b) = ((a : X.X), (b : X.X)) := by
  -- The product comparison for the forgetful functor preserves both projections.
  apply Prod.ext
  · simpa using congrFun (Functor.Monoidal.μ_fst (F := forget TopCat.{u}) X.X X.X) (a, b)
  · simpa using congrFun (Functor.Monoidal.μ_snd (F := forget TopCat.{u}) X.X X.X) (a, b)

/-- Helper for Lemma 5.30.6: the explicit forgotten multiplication agrees with the native
`GrpCat` multiplication on the same carrier. -/
private theorem forgetMul_eq_native_mul (X : Grp TopCat.{u})
    (a b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) :
    forgetMul X a b = a * b := by
  -- The forgotten `GrpCat` carrier is the `mapGrp` carrier equipped with the native group law.
  let _ : (forget TopCat.{u}).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
  have hmul :=
    congrFun (Functor.comp_mapGrp_mul (F := forget TopCat.{u}) (G := 𝟭 (Type u)) X) (a, b)
  simpa [forgetMul, forget_monoidal_mu_eq_pair (X := X) a b] using hmul.symm

/-- Helper for Lemma 5.30.6: multiplying on the carrier and then viewing the result in the
`mapGrp` presentation agrees with multiplying there directly. -/
private theorem carrier_mul_as_mapGrp_mul (X : Grp TopCat.{u})
    [_instMonoidal : (forget TopCat.{u}).Monoidal]
    (a b : X.X) :
    ((carrierMul X a b : X.X) : ((forget TopCat.{u}).mapGrp.obj X).X) =
      mapGrpMul X (a : ((forget TopCat.{u}).mapGrp.obj X).X)
        (b : ((forget TopCat.{u}).mapGrp.obj X).X) := by
  rfl

/-- Helper for Lemma 5.30.6: the explicit `mapGrp` multiplication agrees with the native group
law on the `mapGrp` carrier. -/
private theorem mapGrpMul_eq_native_mul (X : Grp TopCat.{u})
    [_instMonoidal : (forget TopCat.{u}).Monoidal]
    (a b : ((forget TopCat.{u}).mapGrp.obj X).X) :
    mapGrpMul X a b = a * b := by
  -- The native multiplication on the `mapGrp` carrier is the transported multiplication from
  -- `X.X`, with the monoidal comparison supplying the pair identification.
  have hmul :=
    congrFun (Functor.comp_mapGrp_mul (F := forget TopCat.{u}) (G := 𝟭 (Type u)) X) (a, b)
  simpa [mapGrpMul, forget_monoidal_mu_eq_pair (X := X) a b] using hmul.symm

/-- Helper for Lemma 5.30.6: the forgotten multiplication is the same binary operation as the
carrier multiplication, viewed on `X.X`. -/
private theorem forget_mul_operation_eq_carrier_mul (X : Grp TopCat.{u}) :
    (fun a b : X.X ↦
      forgetMul X (a : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)
        (b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)) =
      fun a b : X.X ↦ ((carrierMul X a b : X.X) :
        (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) := by
  funext a b
  rfl

/-- Helper for Lemma 5.30.6: the carrier multiplication is the same binary operation as the
forgotten multiplication read back on `X.X`. -/
private theorem carrier_mul_operation_eq_forget_mul (X : Grp TopCat.{u}) :
    (fun a b : X.X ↦
      ((forgetMul X (a : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)
          (b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) :
          (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) : X.X)) =
      carrierMul X := by
  funext a b
  rfl

/-- Helper for Lemma 5.30.6: after applying a map out of the forgotten group object, an equality
with carrier multiplication is equivalent to the same equality with forgotten multiplication. -/
private theorem map_eq_carrier_mul_iff_map_eq_forget_mul (X : Grp TopCat.{u}) {β : Sort*}
    (f : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X → β) (a b : X.X) (rhs : β) :
    f (((carrierMul X a b : X.X) : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)) = rhs ↔
      f (forgetMul X (a : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)
        (b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X)) = rhs := by
  -- This packages the definitional identification of the two source multiplications as a rewrite
  -- on equality propositions after applying an external map.
  rw [carrier_mul_as_forget_mul]

/-- Helper for Lemma 5.30.6: an equality with multiplication read from the forgotten group object
is equivalent to the corresponding equality with carrier multiplication. -/
private theorem eq_forget_mul_iff_eq_carrier_mul (X : Grp TopCat.{u}) (lhs : X.X)
    (a b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) :
    lhs = ((forgetMul X a b : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj X) : X.X) ↔
      lhs = carrierMul X (a : X.X) (b : X.X) := by
  -- This is the codomain-side transport needed after reading forgotten products back on `X.X`.
  rw [forget_mul_as_carrier_mul]

private def prequotientInv {F : J ⥤ Grp TopCat.{u}} :
    Prequotient (underlyingMonoidDiagram F) → Prequotient (underlyingMonoidDiagram F)
  | .of j x => .of j x⁻¹
  | .one => .one
  | .mul x y => .mul (prequotientInv y) (prequotientInv x)

/-- Helper for Lemma 5.30.6: inversion respects the quotient relation used for the monoid colimit. -/
private theorem prequotientInv_rel {F : J ⥤ Grp TopCat.{u}}
    {x y : Prequotient (underlyingMonoidDiagram F)}
    (h : Relation (underlyingMonoidDiagram F) x y) :
    Relation (underlyingMonoidDiagram F) (prequotientInv x) (prequotientInv y) := by
  induction h with
  | refl x =>
      exact Relation.refl _
  | symm x y hxy ih =>
      exact Relation.symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.trans _ _ _ ihxy ihyz
  | map j j' f x =>
      let g : (underlyingMonoidDiagram F).obj j →* (underlyingMonoidDiagram F).obj j' :=
        ((underlyingMonoidDiagram F).map f).hom
      have hmap :
          g x⁻¹ = (g x)⁻¹ := by
        exact map_inv g x
      change
        Relation (underlyingMonoidDiagram F)
          (Prequotient.of j' (((underlyingMonoidDiagram F).map f x)⁻¹))
          (Prequotient.of j x⁻¹)
      rw [← hmap]
      exact Relation.map (F := underlyingMonoidDiagram F) j j' f x⁻¹
  | mul j x y =>
      have hmul : (x * y)⁻¹ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      change
        Relation (underlyingMonoidDiagram F)
          (Prequotient.of j ((x * y)⁻¹))
          (Prequotient.mul (Prequotient.of j y⁻¹) (Prequotient.of j x⁻¹))
      rw [hmul]
      exact Relation.mul (F := underlyingMonoidDiagram F) j y⁻¹ x⁻¹
  | one j =>
      have hone : ((1 : (underlyingMonoidDiagram F).obj j)⁻¹) = 1 := inv_one
      change
        Relation (underlyingMonoidDiagram F)
          (Prequotient.of j ((1 : (underlyingMonoidDiagram F).obj j)⁻¹))
          Prequotient.one
      rw [hone]
      exact Relation.one (F := underlyingMonoidDiagram F) j
  | mul_1 x x' y h ih =>
      exact Relation.mul_2 _ _ _ ih
  | mul_2 x y y' h ih =>
      exact Relation.mul_1 _ _ _ ih
  | mul_assoc x y z =>
      exact Relation.symm _ _ (Relation.mul_assoc _ _ _)
  | one_mul x =>
      simpa using (Relation.mul_one (prequotientInv x))
  | mul_one x =>
      simpa using (Relation.one_mul (prequotientInv x))

/-- Helper for Lemma 5.30.6: every prequotient expression multiplied by its formal inverse is
equivalent to the unit. -/
private theorem prequotient_inv_mul_rel_one {F : J ⥤ Grp TopCat.{u}} :
    ∀ x : Prequotient (underlyingMonoidDiagram F),
      Relation (underlyingMonoidDiagram F) (.mul (prequotientInv x) x) .one
    := by
  intro x
  induction x with
  | of j x =>
      exact Relation.trans _ _ _
        (Relation.symm _ _ (Relation.mul (F := underlyingMonoidDiagram F) j x⁻¹ x))
        (inv_mul_cancel x ▸
          (Relation.one (F := underlyingMonoidDiagram F) j :
            Relation (underlyingMonoidDiagram F)
              (Prequotient.of j (1 : (underlyingMonoidDiagram F).obj j)) Prequotient.one))
  | one =>
      simpa using (Relation.one_mul (Prequotient.one : Prequotient (underlyingMonoidDiagram F)))
  | mul x y ihx ihy =>
      have h1 :
          Relation (underlyingMonoidDiagram F)
            (Prequotient.mul (Prequotient.mul (prequotientInv y) (prequotientInv x))
              (Prequotient.mul x y))
            (Prequotient.mul (prequotientInv y)
              (Prequotient.mul (prequotientInv x) (Prequotient.mul x y))) :=
        Relation.mul_assoc _ _ _
      have h2 :
          Relation (underlyingMonoidDiagram F)
            (Prequotient.mul (prequotientInv y)
              (Prequotient.mul (prequotientInv x) (Prequotient.mul x y)))
            (Prequotient.mul (prequotientInv y)
              (Prequotient.mul (Prequotient.mul (prequotientInv x) x) y)) :=
        Relation.mul_2 _ _ _ (Relation.symm _ _ (Relation.mul_assoc _ _ _))
      have h3 :
          Relation (underlyingMonoidDiagram F)
            (Prequotient.mul (prequotientInv y)
              (Prequotient.mul (Prequotient.mul (prequotientInv x) x) y))
            (Prequotient.mul (prequotientInv y) (Prequotient.mul Prequotient.one y)) :=
        Relation.mul_2 _ _ _ (Relation.mul_1 _ _ _ ihx)
      have h4 :
          Relation (underlyingMonoidDiagram F)
            (Prequotient.mul (prequotientInv y) (Prequotient.mul Prequotient.one y))
            (Prequotient.mul (prequotientInv y) y) :=
        Relation.mul_2 _ _ _ (Relation.one_mul _)
      exact Relation.trans _ _ _
        h1
        (Relation.trans _ _ _
          h2
          (Relation.trans _ _ _
            h3
            (Relation.trans _ _ _
              h4
              ihy)))

private instance colimitInv (F : J ⥤ Grp TopCat.{u}) :
    Inv (ColimitType (underlyingMonoidDiagram F)) where
  inv x :=
    Quotient.liftOn x
      (fun a ↦ Quotient.mk _ (prequotientInv a))
      (fun _ _ h ↦ by
        apply Quotient.sound
        exact prequotientInv_rel h)

private noncomputable instance colimitGroup (F : J ⥤ Grp TopCat.{u}) :
    Group (ColimitType (underlyingMonoidDiagram F)) where
  inv := (colimitInv F).inv
  inv_mul_cancel := by
    -- The quotient group law is checked on prequotient expressions.
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    change Quotient.mk _ (Prequotient.mul (prequotientInv a) a) = Quotient.mk _ Prequotient.one
    exact Quotient.sound (prequotient_inv_mul_rel_one a)

private noncomputable def grpColimit (F : J ⥤ Grp TopCat.{u}) : GrpCat.{u} :=
  GrpCat.of (ColimitType (underlyingMonoidDiagram F))

private noncomputable def grpColimitCocone (F : J ⥤ Grp TopCat.{u}) :
    Cocone (underlyingGrpDiagram F) where
  pt := grpColimit F
  ι.app j := GrpCat.ofHom ((MonCat.Colimits.colimitCocone (underlyingMonoidDiagram F)).ι.app j).hom
  ι.naturality i j f := by
    apply (forget₂ GrpCat MonCat).map_injective
    simpa [underlyingGrpDiagram, underlyingMonoidDiagram] using
      (MonCat.Colimits.colimitCocone (underlyingMonoidDiagram F)).ι.naturality f

private def grpColimitIsColimit (F : J ⥤ Grp TopCat.{u}) :
    IsColimit (grpColimitCocone F) := by
  -- Route correction: reuse the already-constructed monoid colimit and reflect it to groups.
  apply isColimitOfReflects (forget₂ GrpCat MonCat)
  simpa [grpColimitCocone, grpColimit, underlyingGrpDiagram, underlyingMonoidDiagram] using
    (MonCat.Colimits.colimitIsColimit (underlyingMonoidDiagram F))

private def admissibleGroupTopologies {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) : Set (GroupTopology c.pt) :=
  { t | ∀ j,
      GroupTopology.coinduced (fun x : (F.obj j).X ↦ (c.ι.app j).hom x) ≤ t }

private def coinducedGroupTopology {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) : GroupTopology c.pt :=
  sInf (admissibleGroupTopologies c)

/-- Helper for Lemma 5.30.6: the underlying function of a group-valued cocone leg, viewed on the
original topological-group carrier. -/
private abbrev coconeLegFun {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) : (F.obj j).X → c.pt :=
  fun x ↦ (c.ι.app j).hom x

/-- Helper for Lemma 5.30.6: a continuous map into a group topology yields an upper bound for the
coinduced group topology. -/
private theorem groupTopology_coinduced_le_of_continuous {α β : Type*}
    [tα : TopologicalSpace α] [Group β] (f : α → β) (t : GroupTopology β)
    (hf : @Continuous α β tα t.toTopologicalSpace f) :
    GroupTopology.coinduced f ≤ t := by
  rw [GroupTopology.coinduced]
  exact sInf_le (show t ∈ { b : GroupTopology β | TopologicalSpace.coinduced f tα ≤ b.toTopologicalSpace } from
    continuous_iff_coinduced_le.1 hf)

/-- Helper for Lemma 5.30.6: the final group topology is above each stagewise coinduced
topology. -/
private theorem stagewise_coinduced_le_coinducedGroupTopology {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    GroupTopology.coinduced (coconeLegFun c j) ≤ coinducedGroupTopology c := by
  rw [coinducedGroupTopology]
  exact le_sInf fun t ht => ht j

/-- Helper for Lemma 5.30.6: any topological group gives a group object in `TopCat`. -/
private instance topCatGrpObjOfTopologicalGroup (α : Type u) [Group α] [TopologicalSpace α]
    [IsTopologicalGroup α] : GrpObj (TopCat.of α) where
  one := TopCat.ofHom ⟨fun _ ↦ (1 : α), continuous_const⟩
  mul := TopCat.ofHom ⟨fun p : α × α ↦ p.1 * p.2, continuous_mul⟩
  one_mul := by
    apply TopCat.ext
    intro x
    change (1 : α) * x.2 = x.2
    exact _root_.one_mul x.2
  mul_one := by
    apply TopCat.ext
    intro x
    change x.1 * (1 : α) = x.1
    exact _root_.mul_one x.1
  mul_assoc := by
    apply TopCat.ext
    intro x
    change (x.1.1 * x.1.2) * x.2 = x.1.1 * (x.1.2 * x.2)
    exact _root_.mul_assoc x.1.1 x.1.2 x.2
  inv := TopCat.ofHom ⟨fun x : α ↦ x⁻¹, continuous_inv⟩
  left_inv := by
    apply TopCat.ext
    intro x
    change x⁻¹ * x = (1 : α)
    exact inv_mul_cancel x
  right_inv := by
    apply TopCat.ext
    intro x
    change x * x⁻¹ = (1 : α)
    exact mul_inv_cancel x

/-- Helper for Lemma 5.30.6: the carrier of an object of `Grp TopCat` is a topological group. -/
private instance carrierIsTopologicalGroup (X : Grp TopCat.{u}) : IsTopologicalGroup X.X where
  continuous_mul := by
    simpa using (TopCat.Hom.hom μ[X.X]).continuous
  continuous_inv := by
    simpa using (TopCat.Hom.hom ι[X.X]).continuous

private def topologicalColimit {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) : Grp TopCat.{u} :=
  let t := coinducedGroupTopology c
  letI : TopologicalSpace c.pt := t.toTopologicalSpace
  letI : IsTopologicalGroup c.pt := t.toIsTopologicalGroup
  { X := TopCat.of c.pt }

/-- Helper for Lemma 5.30.6: each cocone leg is continuous for the final group topology. -/
private theorem continuous_to_topologicalColimit {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    @Continuous (F.obj j).X c.pt (F.obj j).X.str (coinducedGroupTopology c).toTopologicalSpace
      (coconeLegFun c j) := by
  -- The final topology is built to dominate every stagewise coinduced topology.
  have hstage :
      GroupTopology.coinduced (coconeLegFun c j) ≤ coinducedGroupTopology c :=
    stagewise_coinduced_le_coinducedGroupTopology c j
  let tStage : GroupTopology c.pt := GroupTopology.coinduced (coconeLegFun c j)
  have hcont :
      @Continuous (F.obj j).X c.pt (F.obj j).X.str tStage.toTopologicalSpace (coconeLegFun c j) :=
    GroupTopology.coinduced_continuous (coconeLegFun c j)
  exact continuous_le_rng hstage hcont

/-- Helper for Lemma 5.30.6: each cocone leg still sends the unit to the unit after equipping the
colimit carrier with the final topology. -/
private theorem coconeLegFun_map_one {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    coconeLegFun c j (1 : (F.obj j).X) = (1 : c.pt) := by
  -- The cocone leg is a group homomorphism on the underlying carrier.
  let one' : (underlyingGrpDiagram F).obj j := 1
  have hone : (one' : (underlyingGrpDiagram F).obj j) = (1 : (F.obj j).X) := rfl
  rw [← hone]
  simpa [coconeLegFun, one'] using (c.ι.app j).hom.map_one

/-- Helper for Lemma 5.30.6: each cocone leg still respects multiplication after equipping the
colimit carrier with the final topology. -/
private theorem coconeLegHom_map_mul {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J)
    (x y : (underlyingGrpDiagram F).obj j) :
    (c.ι.app j).hom (x * y) = (c.ι.app j).hom x * (c.ι.app j).hom y := by
  -- On the forgotten `GrpCat` domain, multiplicativity is exactly the bundled homomorphism law.
  exact (c.ι.app j).hom.map_mul x y

private theorem coconeLegFun_map_mul {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) (x y : (F.obj j).X) :
    coconeLegFun c j (x * y) = coconeLegFun c j x * coconeLegFun c j y := by
  -- Route correction: rewrite the source multiplication onto the forgotten `GrpCat` carrier and
  -- then apply multiplicativity of the algebraic cocone leg.
  exact
    (map_eq_carrier_mul_iff_map_eq_forget_mul (X := F.obj j) ((c.ι.app j).hom) x y
      ((c.ι.app j).hom (x : (underlyingGrpDiagram F).obj j) *
        (c.ι.app j).hom (y : (underlyingGrpDiagram F).obj j))).2
      (by
        -- We rewrite the explicit forgotten product to the native `GrpCat` multiplication.
        rw [forgetMul_eq_native_mul]
        exact
          coconeLegHom_map_mul (c := c) (j := j) (x := (x : (underlyingGrpDiagram F).obj j))
            (y := (y : (underlyingGrpDiagram F).obj j)))

/-- Helper for Lemma 5.30.6: a cocone leg in `GrpCat` can be viewed directly as a bundled
monoid hom on the original topological-group carrier. -/
private abbrev coconeLegMonoidHom {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) : (F.obj j).X →* c.pt :=
  { toFun := coconeLegFun c j
    map_one' := coconeLegFun_map_one c j
    map_mul' := coconeLegFun_map_mul c j }

/-- Helper for Lemma 5.30.6: each cocone leg becomes a continuous monoid hom into the final
topological colimit. -/
private def coconeLegContinuousMonoidHom {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    (F.obj j).X →ₜ* (topologicalColimit c).X :=
  { toFun := coconeLegFun c j
    map_one' := coconeLegFun_map_one c j
    map_mul' := coconeLegFun_map_mul c j
    continuous_toFun := continuous_to_topologicalColimit c j }

private def toTopologicalColimit {F : J ⥤ Grp TopCat.{u}}
    (c : Cocone (underlyingGrpDiagram F)) (j : J) :
    F.obj j ⟶ topologicalColimit c :=
  ConcreteCategory.ofHom (C := Grp TopCat.{u}) (coconeLegContinuousMonoidHom c j)

/-- Helper for Lemma 5.30.6: the topological colimit legs inherit naturality from the algebraic
cocone legs. -/
private theorem toTopologicalColimit_naturality {F : J ⥤ Grp TopCat.{u}}
    {i j : J} (f : i ⟶ j) :
    F.map f ≫ toTopologicalColimit (grpColimitCocone F) j =
      toTopologicalColimit (grpColimitCocone F) i := by
  -- The concrete realization preserves the underlying function, so extensionality reduces
  -- naturality to the `GrpCat` cocone identity.
  ext x
  simpa [toTopologicalColimit, coconeLegContinuousMonoidHom, coconeLegFun] using
    ConcreteCategory.congr_hom ((grpColimitCocone F).ι.naturality f) x

private def topologicalColimitCocone (F : J ⥤ Grp TopCat.{u}) : Cocone F where
  pt := topologicalColimit (grpColimitCocone F)
  ι.app j := toTopologicalColimit (grpColimitCocone F) j
  ι.naturality _ _ f := toTopologicalColimit_naturality (F := F) f

/-- Helper for Lemma 5.30.6: the algebraic universal map from the group colimit to any target
cocone point. -/
private abbrev algebraicDesc {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) :
    grpColimit F ⟶ (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt :=
  (grpColimitIsColimit F).desc ((forget₂ (Grp TopCat.{u}) GrpCat.{u}).mapCocone s)

/-- Helper for Lemma 5.30.6: the algebraic desc map viewed as a function to the target carrier. -/
private abbrev algebraicDescFun {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) :
    grpColimit F → s.pt.X :=
  fun x ↦ (algebraicDesc (F := F) s).hom x

/-- Helper for Lemma 5.30.6: reading the forgotten target multiplication of the algebraic desc map
back on the topological carrier recovers the carrier multiplication. -/
private theorem algebraicDesc_forget_mul_as_carrier_mul {F : J ⥤ Grp TopCat.{u}}
    (s : Cocone F) (x y : grpColimit F) :
    ((forgetMul s.pt ((algebraicDesc (F := F) s).hom x)
        ((algebraicDesc (F := F) s).hom y) :
        (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) : s.pt.X) =
      carrierMul s.pt ((algebraicDesc (F := F) s).hom x : s.pt.X)
        ((algebraicDesc (F := F) s).hom y : s.pt.X) := by
  -- This is the codomain transport from the forgotten group object back to `s.pt.X`.
  exact
    forget_mul_as_carrier_mul (X := s.pt)
      ((algebraicDesc (F := F) s).hom x)
      ((algebraicDesc (F := F) s).hom y)

/-- Helper for Lemma 5.30.6: the algebraic desc map sends the unit to the unit. -/
private theorem algebraicDescFun_map_one {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) :
    algebraicDescFun (F := F) s 1 = (1 : s.pt.X) := by
  -- This is the unit law for the algebraic desc map, read on the topological carrier.
  change ((algebraicDesc (F := F) s).hom 1 :
      (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) =
    (1 : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt)
  exact (algebraicDesc (F := F) s).hom.map_one

/-- Helper for Lemma 5.30.6: the algebraic desc map respects multiplication on the carrier. -/
private theorem algebraicDescFun_map_mul {F : J ⥤ Grp TopCat.{u}} (s : Cocone F)
    (x y : grpColimit F) :
    algebraicDescFun (F := F) s (x * y) =
      algebraicDescFun (F := F) s x * algebraicDescFun (F := F) s y := by
  -- The desc map is already a group homomorphism on the underlying carrier.
  -- We first use multiplicativity in the forgotten `GrpCat` codomain and then rewrite that
  -- product back to the carrier multiplication on `s.pt.X`.
  exact
    (eq_forget_mul_iff_eq_carrier_mul (X := s.pt)
      ((algebraicDesc (F := F) s).hom (x * y))
      ((algebraicDesc (F := F) s).hom x)
      ((algebraicDesc (F := F) s).hom y)).1
      (by
        -- This `change` rewrites the codomain product into the explicit forgotten multiplication.
        change
          ((algebraicDesc (F := F) s).hom (x * y) :
              (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) =
            forgetMul s.pt ((algebraicDesc (F := F) s).hom x)
              ((algebraicDesc (F := F) s).hom y)
        rw [forgetMul_eq_native_mul]
        exact (algebraicDesc (F := F) s).hom.map_mul x y)

/-- Helper for Lemma 5.30.6: the algebraic desc map viewed as a bundled monoid hom to the target
topological-group carrier. -/
private abbrev algebraicDescMonoidHom {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) :
    grpColimit F →* s.pt.X where
  toFun := algebraicDescFun (F := F) s
  map_one' := algebraicDescFun_map_one (F := F) s
  map_mul' := algebraicDescFun_map_mul (F := F) s

/-- Helper for Lemma 5.30.6: the algebraic desc map factors each algebraic cocone leg through the
corresponding target cocone leg. -/
private theorem algebraicDesc_comp_coconeLeg {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) (j : J) :
    algebraicDescFun (F := F) s ∘ coconeLegFun (grpColimitCocone F) j =
      fun x ↦ s.ι.app j x := by
  -- The group-colimit factorization gives the required carrier-level equality.
  funext x
  simpa [algebraicDescFun, algebraicDesc, coconeLegFun, Function.comp] using
    ConcreteCategory.congr_hom
      ((grpColimitIsColimit F).fac ((forget₂ (Grp TopCat.{u}) GrpCat.{u}).mapCocone s) j) x

/-- Helper for Lemma 5.30.6: a cocone leg of the target cocone is continuous on the underlying
carriers. -/
private theorem continuous_targetCoconeLeg {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) (j : J) :
    Continuous (fun x : (F.obj j).X ↦ s.ι.app j x) := by
  -- The concrete-category realization of a morphism in `Grp TopCat` is a continuous monoid hom.
  change Continuous (ConcreteCategory.hom (s.ι.app j))
  exact (ConcreteCategory.hom (s.ι.app j)).continuous

/-- Helper for Lemma 5.30.6: the topology induced on the algebraic colimit by the algebraic desc
map to a target cocone point. -/
private def descInducedGroupTopology {F : J ⥤ Grp TopCat.{u}}
    (s : Cocone F) : GroupTopology (grpColimit F) :=
  { toTopologicalSpace := TopologicalSpace.induced (algebraicDescFun (F := F) s) s.pt.X.str
    toIsTopologicalGroup := topologicalGroup_induced (algebraicDescMonoidHom (F := F) s) }

/-- Helper for Lemma 5.30.6: the topology induced by the algebraic desc map is admissible for the
final-topology construction on the algebraic colimit. -/
private theorem descInducedGroupTopology_admissible {F : J ⥤ Grp TopCat.{u}}
    (s : Cocone F) :
    coinducedGroupTopology (grpColimitCocone F) ≤ descInducedGroupTopology (F := F) s := by
  -- Each stage leg becomes continuous into the induced topology because its composite with the
  -- desc map is the given continuous target cocone leg.
  rw [coinducedGroupTopology, admissibleGroupTopologies]
  refine sInf_le ?_
  intro j
  apply groupTopology_coinduced_le_of_continuous (t := descInducedGroupTopology (F := F) s)
  rw [descInducedGroupTopology]
  rw [continuous_iff_le_induced]
  rw [induced_compose]
  have hscont : Continuous (algebraicDescFun (F := F) s ∘ coconeLegFun (grpColimitCocone F) j) := by
    -- The algebraic factorization identifies the composite with the given target cocone leg.
    simpa [algebraicDesc_comp_coconeLeg (F := F) s j, Function.comp] using
      continuous_targetCoconeLeg (F := F) s j
  exact continuous_iff_le_induced.1 hscont

/-- Helper for Lemma 5.30.6: the algebraic desc map is continuous from the final group topology on
the colimit carrier. -/
private theorem continuous_algebraicDesc {F : J ⥤ Grp TopCat.{u}} (s : Cocone F) :
    @Continuous (grpColimit F) s.pt.X
      (coinducedGroupTopology (grpColimitCocone F)).toTopologicalSpace s.pt.X.str
      (algebraicDescFun (F := F) s) := by
  -- Continuity is exactly the comparison between the final source topology and the induced one.
  rw [continuous_iff_le_induced]
  simpa [descInducedGroupTopology] using
    (descInducedGroupTopology_admissible (F := F) s)

/-- Helper for Lemma 5.30.6: the universal map to any target cocone is a continuous monoid hom. -/
private def topologicalColimitDescContinuousMonoidHom {F : J ⥤ Grp TopCat.{u}}
    (s : Cocone F) : (topologicalColimit (grpColimitCocone F)).X →ₜ* s.pt.X :=
  { toFun := algebraicDescFun (F := F) s
    map_one' := (algebraicDescMonoidHom (F := F) s).map_one
    map_mul' := (algebraicDescMonoidHom (F := F) s).map_mul
    continuous_toFun := continuous_algebraicDesc (F := F) s }

/-- Helper for Lemma 5.30.6: the universal morphism from the constructed topological colimit to
any target cocone. -/
private def topologicalColimitDesc {F : J ⥤ Grp TopCat.{u}}
    (s : Cocone F) : topologicalColimit (grpColimitCocone F) ⟶ s.pt :=
  ConcreteCategory.ofHom (C := Grp TopCat.{u}) (topologicalColimitDescContinuousMonoidHom s)

/-- Helper for Lemma 5.30.6: a morphism of topological groups remains multiplicative after reading
its values in the forgotten `GrpCat` codomain. -/
private theorem forgetful_hom_map_mul {F : J ⥤ Grp TopCat.{u}} (s : Cocone F)
    (m : (topologicalColimitCocone F).pt ⟶ s.pt) :
    ∀ x y : grpColimit F,
      (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom (x * y)) :
          (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) =
        ((((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x) :
            (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) *
          (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y) :
            (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt)) := by
  intro x y
  -- Package multiplicativity of the continuous monoid hom through the carrier-to-forgetful
  -- coercion on the codomain.
  have h :=
    congrArg
      (fun z : s.pt.X ↦ (z : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt))
      ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).map_mul x y)
  exact h

private def topologicalColimitIsColimit (F : J ⥤ Grp TopCat.{u}) :
    IsColimit (topologicalColimitCocone F) where
  desc s := topologicalColimitDesc (F := F) s
  fac s i := by
    -- The topological factorization is the algebraic factorization on underlying carriers.
    apply Grp.hom_ext
    apply TopCat.ext
    intro x
    simpa [topologicalColimitCocone, toTopologicalColimit, topologicalColimitDesc,
      topologicalColimitDescContinuousMonoidHom, coconeLegContinuousMonoidHom,
      coconeLegFun, algebraicDescFun, algebraicDesc] using
      ConcreteCategory.congr_hom
        ((grpColimitIsColimit F).fac ((forget₂ (Grp TopCat.{u}) GrpCat.{u}).mapCocone s) i) x
  uniq s m hm := by
    -- Forgetting to `GrpCat` reduces uniqueness to the algebraic colimit.
    let _ : (forget TopCat.{u}).Monoidal :=
      Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
    let mGrp : grpColimit F ⟶ (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt :=
      GrpCat.ofHom
        { toFun := fun x ↦
            (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x) :
              (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt)
          map_one' := by
            change (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom 1) :
                (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt) =
              (1 : (forget₂ (Grp TopCat.{u}) GrpCat.{u}).obj s.pt)
            exact (ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom.map_one
          map_mul' := by
            -- Route correction: prove multiplicativity on `s.pt.X` first and then transport the
            -- resulting equality to the `mapGrp` carrier presentation.
            intro x y
            -- We cast the carrier-level multiplicativity statement into the `mapGrp` presentation
            -- and then rewrite the codomain product via the explicit `mapGrp` multiplication.
            have h_cast :
                (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom (x * y) : s.pt.X) :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X) =
                  ((carrierMul s.pt ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x)
                      ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y) : s.pt.X) :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X) := by
              exact
                congrArg
                  (fun z : s.pt.X ↦ (z : ((forget TopCat.{u}).mapGrp.obj s.pt).X))
                  ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).map_mul x y)
            have h_mapGrp :
                ((carrierMul s.pt ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x)
                    ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y) : s.pt.X) :
                  ((forget TopCat.{u}).mapGrp.obj s.pt).X) =
                mapGrpMul s.pt
                  (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x : s.pt.X) :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X)
                  (((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y : s.pt.X) :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X) := by
              exact
                carrier_mul_as_mapGrp_mul (X := s.pt)
                  ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x)
                  ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y)
            exact h_cast.trans <| h_mapGrp.trans <| by
              simpa using
                (mapGrpMul_eq_native_mul (X := s.pt)
                  ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom x :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X)
                  ((ConcreteCategory.hom (C := Grp TopCat.{u}) m).toMonoidHom y :
                    ((forget TopCat.{u}).mapGrp.obj s.pt).X)) }
    have hm' : ∀ j, (grpColimitCocone F).ι.app j ≫ mGrp =
        ((forget₂ (Grp TopCat.{u}) GrpCat.{u}).mapCocone s).ι.app j := by
      intro j
      ext x
      simpa [mGrp, topologicalColimitCocone, toTopologicalColimit, coconeLegContinuousMonoidHom,
        topologicalColimitDesc, topologicalColimitDescContinuousMonoidHom, coconeLegFun,
        algebraicDescFun, algebraicDesc] using ConcreteCategory.congr_hom (hm j) x
    have huniq : mGrp = algebraicDesc (F := F) s :=
      (grpColimitIsColimit F).uniq ((forget₂ (Grp TopCat.{u}) GrpCat.{u}).mapCocone s) mGrp hm'
    apply Grp.hom_ext
    apply TopCat.ext
    intro x
    simpa [mGrp, topologicalColimitDesc, topologicalColimitDescContinuousMonoidHom,
      algebraicDescFun, algebraicDesc] using ConcreteCategory.congr_hom huniq x

/-- Helper for Lemma 5.30.6: equip a group with the indiscrete topology and view it as an object of
`Grp TopCat`. -/
private noncomputable def trivialGrp : GrpCat.{u} ⥤ Grp TopCat.{u} := by
  let _ : TopCat.trivial.IsRightAdjoint := ⟨_, ⟨TopCat.adj₂⟩⟩
  let _ : PreservesFiniteProducts TopCat.trivial := inferInstance
  let _ : TopCat.trivial.Monoidal := Functor.Monoidal.ofChosenFiniteProducts TopCat.trivial
  exact grpTypeEquivalenceGrp.inverse ⋙ TopCat.trivial.mapGrp

/-- Helper for Lemma 5.30.6: the forgetful functor to groups is left adjoint to the indiscrete
topology functor on groups. -/
private noncomputable def trivialGrpAdj :
    forget₂ (Grp TopCat.{u}) GrpCat.{u} ⊣ trivialGrp := by
  let _ : (forget TopCat.{u}).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts (forget TopCat.{u})
  let _ : TopCat.trivial.IsRightAdjoint := ⟨_, ⟨TopCat.adj₂⟩⟩
  let _ : PreservesFiniteProducts TopCat.trivial := inferInstance
  let _ : TopCat.trivial.Monoidal := Functor.Monoidal.ofChosenFiniteProducts TopCat.trivial
  simpa [trivialGrp, Functor.comp_assoc] using
    ((CategoryTheory.Adjunction.mapGrp TopCat.adj₂).comp grpTypeEquivalenceGrp.toAdjunction)

instance hasColimitsOfShape (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (Grp TopCat.{u}) where
  has_colimit F := ⟨⟨topologicalColimitCocone F, topologicalColimitIsColimit F⟩⟩

/-- Lemma 5.30.6 (1): the category of topological groups has colimits of every small shape. -/
instance hasColimits : HasColimits (Grp TopCat.{u}) where
  has_colimits_of_shape K _ := by
    infer_instance

instance forgetToGrpCat_preservesColimitsOfShape (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (forget₂ (Grp TopCat.{u}) GrpCat.{u}) where
  preservesColimit := fun {F} ↦ by
    -- The forgetful functor is a left adjoint, hence it preserves colimits.
    let _ : PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) :=
      Adjunction.leftAdjoint_preservesColimits trivialGrpAdj
    infer_instance

/-- Lemma 5.30.6 (2): the forgetful functor from topological groups to groups preserves colimits. -/
instance forgetToGrpCat_preservesColimits :
    PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) where
  preservesColimitsOfShape {J} := by
    infer_instance

end

end TopologicalGroupCat

/-- Summary theorem collecting the colimit existence and preservation instances for
`Grp TopCat`. -/
theorem topologicalGroupCat_hasColimits_and_forgetToGrpCat_preservesColimits :
    HasColimits (Grp TopCat.{u}) ∧
      PreservesColimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}) := by
  exact ⟨TopologicalGroupCat.hasColimits, TopologicalGroupCat.forgetToGrpCat_preservesColimits⟩
