module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Generator.Type
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_29_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Functor.IsDenseSubsite
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

noncomputable section

universe u v uI u₀ v₀

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]
variable {I : Type uI} (ℱ : I → Sheaf J (Type (max u v)))

/-- Helper for Lemma 7.29.5: the replacement site is generated inside `Sh(J)` by the
sheafified representables, the chosen family `ℱ`, the terminal sheaf, and then closed under
pullbacks and subobjects. -/
inductive replacement_object_property : ObjectProperty (Sheaf J (Type (max u v)))
  | sheafifiedRepresentable (U : C) :
      replacement_object_property (h[U]^#[J])
  | family (i : I) :
      replacement_object_property (ℱ i)
  | terminal :
      replacement_object_property (Sheaf.terminal J Types.isTerminalPUnit)
  | pullback {X Y Z : Sheaf J (Type (max u v))}
      (f : X ⟶ Z) (g : Y ⟶ Z)
      (hX : replacement_object_property X) (hY : replacement_object_property Y)
      (hZ : replacement_object_property Z) :
      replacement_object_property (pullback f g)
  | of_mono {X Y : Sheaf J (Type (max u v))}
      (f : X ⟶ Y) [Mono f] (hY : replacement_object_property Y) :
      replacement_object_property X

/-- Helper for Lemma 7.29.5: the generated replacement property is closed under subobjects by
construction. -/
instance replacement_object_property_closed_under_subobjects :
    (replacement_object_property (J := J) ℱ).IsClosedUnderSubobjects where
  -- Any monomorphism into an object already in the generated class is one of the generators.
  prop_of_mono f _ hY := replacement_object_property.of_mono (J := J) (ℱ := ℱ) f hY

/-- Helper for Lemma 7.29.5: the generated replacement property contains a terminal object, so it
is closed under limits of the empty diagram. -/
instance replacement_object_property_closed_under_terminal :
    (replacement_object_property (J := J) ℱ).IsClosedUnderLimitsOfShape (Discrete PEmpty) where
  -- Reinterpret an empty-diagram limit as a terminal object and compare it with the chosen
  -- terminal sheaf generator.
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let c : Cone p.diag := ⟨X, p.π⟩
    have hterminal : IsTerminal X :=
      (Limits.isLimitEquivIsTerminalOfIsEmpty (c := c)).1 p.isLimit
    exact
      (replacement_object_property (J := J) ℱ).prop_of_iso
        ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).uniqueUpToIso hterminal)
        (replacement_object_property.terminal (J := J) (ℱ := ℱ))

/-- Helper for Lemma 7.29.5: the generated replacement property is closed under pullbacks, which
is the Lean form of the inductive step `C_n ↦ C_{n+1}` from the source proof. -/
instance replacement_object_property_closed_under_pullbacks :
    (replacement_object_property (J := J) ℱ).IsClosedUnderLimitsOfShape WalkingCospan where
  -- Identify a limiting cospan cone with the standard pullback of its two legs, then invoke the
  -- pullback generator on the full cospan, matching the source proof's closure under fiber
  -- products of previously generated objects.
  limitsOfShape_le := by
    rintro X ⟨p⟩
    have hpb :
        IsPullback (p.π.app WalkingCospan.left) (p.π.app WalkingCospan.right)
          (p.diag.map WalkingCospan.Hom.inl) (p.diag.map WalkingCospan.Hom.inr) :=
      IsPullback.of_isLimit_cone p.isLimit
    have hpullback :
        replacement_object_property (J := J) ℱ
          (pullback (p.diag.map WalkingCospan.Hom.inl) (p.diag.map WalkingCospan.Hom.inr)) :=
      replacement_object_property.pullback (J := J) (ℱ := ℱ)
        (p.diag.map WalkingCospan.Hom.inl) (p.diag.map WalkingCospan.Hom.inr)
        (p.prop_diag_obj WalkingCospan.left) (p.prop_diag_obj WalkingCospan.right)
        (p.prop_diag_obj WalkingCospan.one)
    exact
      (replacement_object_property (J := J) ℱ).prop_of_iso hpb.isoPullback.symm hpullback

/-- Helper for Lemma 7.29.5: the intermediate full subcategory generated by the replacement
property has finite limits because the property contains a terminal object and is closed under
pullbacks. -/
private theorem replacement_fullSubcategory_hasFiniteLimits :
    HasFiniteLimits (replacement_object_property (J := J) ℱ).FullSubcategory := by
  -- The full subcategory inherits the terminal-object and pullback constructions already encoded
  -- in `replacement_object_property`.
  let _ : HasTerminal (replacement_object_property (J := J) ℱ).FullSubcategory := inferInstance
  let _ : HasPullbacks (replacement_object_property (J := J) ℱ).FullSubcategory := inferInstance
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- Helper for Lemma 7.29.5: the ambient sheaf category is well-powered because the sheafified
representables generated from the separator `PUnit` form a separating family. -/
private theorem replacement_sheaf_wellPowered :
    WellPowered.{max u v} (Sheaf J (Type (max u v))) := by
  -- Start from the standard separator of `Type`, viewed as a singleton separating family.
  have hTypes :
      ObjectProperty.IsSeparating
        (.ofObj (fun _ : Unit ↦ PUnit.{max u v + 1})) := by
    exact ObjectProperty.IsSeparating.of_le
      (Types.isSeparator_punit : IsSeparator PUnit.{max u v + 1}) (by simp)
  -- Lift that separating family along sheafified free Yoneda objects.
  have hSheaf :
      ObjectProperty.IsSeparating
        (.ofObj (fun x : C × Unit ↦ Sheaf.freeYoneda J x.1 PUnit.{max u v + 1})) := by
    simpa using Sheaf.isSeparating (J := J) hTypes
  -- In a balanced category with pullbacks, a separating family is detecting, hence yields
  -- well-poweredness.
  exact wellPowered_of_isDetecting hSheaf.isDetecting

/-- Helper for Lemma 7.29.5: the stagewise source construction records chosen representatives of
subobjects of objects satisfying a property `P`. This is the Lean version of picking a set of
subsheaf representatives at each stage of the source proof. -/
private def replacement_subobject_stage
    (P : ObjectProperty (Sheaf J (Type (max u v)))) :
    ObjectProperty (Sheaf J (Type (max u v))) :=
  .ofObj (fun x : Σ Y : Subtype P, Subobject Y.1 ↦ (x.2 : Sheaf J (Type (max u v))))

/-- Helper for Lemma 7.29.5: the source proof builds the replacement site by stages.
Stage `0` contains the sheafified representables, the chosen family, and the terminal sheaf; each
successor stage adds pullbacks and chosen representatives of subobjects of the previous stage. -/
private def replacement_stage : Nat → ObjectProperty (Sheaf J (Type (max u v)))
  | 0 =>
      .ofObj (fun x : C ⊕ (I ⊕ Unit) =>
        Sum.elim
          (fun U ↦ h[U]^#[J])
          (fun y ↦ Sum.elim (fun i ↦ ℱ i) (fun _ ↦ Sheaf.terminal J Types.isTerminalPUnit) y)
          x)
  | n + 1 =>
      let Pn := replacement_stage n
      (Pn ⊔ Pn.strictLimitsOfShape WalkingCospan) ⊔ replacement_subobject_stage (J := J) Pn

/-- Helper for Lemma 7.29.5: a pullback of three objects already present in stage `n` lands in
stage `n + 1`, matching the source proof's fibre-product step. -/
private theorem replacement_stage_pullback
    (n : Nat) {X Y Z : Sheaf J (Type (max u v))} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : replacement_stage (J := J) ℱ n X)
    (hY : replacement_stage (J := J) ℱ n Y)
    (hZ : replacement_stage (J := J) ℱ n Z) :
    replacement_stage (J := J) ℱ (n + 1) (pullback f g) := by
  -- Move to the successor-stage definition and place the chosen pullback in the pullback summand.
  change
    (((replacement_stage (J := J) ℱ n ⊔
        (replacement_stage (J := J) ℱ n).strictLimitsOfShape WalkingCospan) ⊔
        replacement_subobject_stage (J := J) (replacement_stage (J := J) ℱ n))
      (pullback f g))
  refine Or.inl ?_
  refine Or.inr ?_
  refine ⟨cospan f g, ?_⟩
  rintro (_ | j)
  · simpa using hZ
  · cases j using WalkingPair.casesOn
    · simpa using hX
    · simpa using hY

/-- Helper for Lemma 7.29.5: once a stage is small, the chosen subobject representatives of that
stage are small as well. This is where well-poweredness supplies the small set of subsheaves. -/
private theorem replacement_subobject_stage_small
    (P : ObjectProperty (Sheaf J (Type (max u v))))
    [ObjectProperty.Small.{max u v} P] :
    ObjectProperty.Small.{max u v} (replacement_subobject_stage (J := J) P) := by
  -- Well-poweredness makes every `Subobject Y` small, so the sigma-indexed representative family
  -- used by `replacement_subobject_stage` is small.
  let _ : WellPowered.{max u v} (Sheaf J (Type (max u v))) :=
    replacement_sheaf_wellPowered (J := J)
  dsimp [replacement_subobject_stage]
  infer_instance

/-- Helper for Lemma 7.29.5: if the chosen family is already indexed by a
`Type (max u v)`-small type, then each source stage is small. This is the Lean realization of the
source proof's repeated statement that each `\mathcal C_n` has a set of objects. -/
private theorem replacement_stage_small [Small.{max u v} I] :
    ∀ n, ObjectProperty.Small.{max u v} (replacement_stage (J := J) ℱ n)
  | 0 => by
      -- The base stage is explicitly indexed by `C ⊕ (I ⊕ Unit)`.
      dsimp [replacement_stage]
      infer_instance
  | n + 1 => by
      -- The successor stage is the union of the previous stage, its chosen pullbacks, and its
      -- chosen subobject representatives.
      let _ : ObjectProperty.Small.{max u v} (replacement_stage (J := J) ℱ n) :=
        replacement_stage_small n
      let _ :
          ObjectProperty.Small.{max u v}
            ((replacement_stage (J := J) ℱ n).strictLimitsOfShape WalkingCospan) :=
        inferInstance
      let _ :
          ObjectProperty.Small.{max u v}
            (replacement_subobject_stage (J := J) (replacement_stage (J := J) ℱ n)) :=
        replacement_subobject_stage_small (J := J) (P := replacement_stage (J := J) ℱ n)
      dsimp [replacement_stage]
      infer_instance

/-- Helper for Lemma 7.29.5: every chosen source stage is contained in the inductively generated
replacement object property. This records the verified prefix of the source-proof skeleton even
before resolving the theorem's universe mismatch for the family index set. -/
private theorem replacement_stage_le_property :
    ∀ n,
      replacement_stage (J := J) ℱ n ≤ replacement_object_property (J := J) ℱ
  | 0 => by
      -- The base stage is exactly the list of generators appearing in the inductive definition.
      intro X hX
      rcases hX with ⟨U | (i | u)⟩
      · simpa [replacement_stage] using
          replacement_object_property.sheafifiedRepresentable (J := J) (ℱ := ℱ) U
      · simpa [replacement_stage] using replacement_object_property.family (J := J) (ℱ := ℱ) i
      · simpa [replacement_stage] using replacement_object_property.terminal (J := J) (ℱ := ℱ)
  | n + 1 => by
      -- At the successor step, pullback representatives are handled by the pullback closure of
      -- `replacement_object_property`, and chosen subobject representatives by the mono closure.
      intro X hX
      rcases hX with (hX | hX)
      · rcases hX with (hX | hX)
        · exact replacement_stage_le_property n _ hX
        · rcases hX with ⟨F, hF⟩
          exact
            (replacement_object_property (J := J) ℱ).prop_limit F
              (fun j ↦ replacement_stage_le_property n _ (hF j))
      · rcases hX with ⟨⟨Y, hY⟩, G⟩
        -- Replace the abstract subobject by an explicit monomorphism representative before using
        -- the mono-closure built into `replacement_object_property`.
        refine
          Subobject.ind
            (p := fun S : Subobject Y =>
              replacement_object_property (J := J) ℱ (S : Sheaf J (Type (max u v))))
            (P := G) ?_
        intro A f _
        exact
          replacement_object_property.of_mono (J := J) (ℱ := ℱ) (Subobject.mk f).arrow
            (replacement_stage_le_property n _ hY)

/-- Helper for Lemma 7.29.5: the stage filtration is monotone, so once an object appears at some
stage it remains available at every later stage. -/
private theorem replacement_stage_succ_le (n : Nat) :
    replacement_stage (J := J) ℱ n ≤ replacement_stage (J := J) ℱ (n + 1) := by
  intro X hX
  -- Each successor stage contains the previous stage as its left summand.
  change
    (((replacement_stage (J := J) ℱ n ⊔
        (replacement_stage (J := J) ℱ n).strictLimitsOfShape WalkingCospan) ⊔
        replacement_subobject_stage (J := J) (replacement_stage (J := J) ℱ n))
      X)
  exact Or.inl (Or.inl hX)

/-- Helper for Lemma 7.29.5: the stage filtration is monotone, so once an object appears at some
stage it remains available at every later stage. -/
private theorem replacement_stage_monotone :
    Monotone (replacement_stage (J := J) ℱ) := by
  intro n m hnm
  induction hnm with
  | refl =>
      exact fun _ hX ↦ hX
  | @step m hnm ih =>
      exact ih.trans (replacement_stage_succ_le (J := J) (ℱ := ℱ) m)

/-- Helper for Lemma 7.29.5: the replacement object property is essentially small because every
object generated by the source-proof closure operations is isomorphic to an object appearing in
some small stage of the filtration. -/
private theorem replacement_object_property_essentiallySmall [Small.{max u v} I] :
    ObjectProperty.EssentiallySmall.{max u v}
      (replacement_object_property (J := J) ℱ) := by
  let Q : ObjectProperty (Sheaf J (Type (max u v))) := ⨆ n, replacement_stage (J := J) ℱ n
  have hQsmall : ObjectProperty.Small.{max u v} Q := by
    let _ : ∀ n, ObjectProperty.Small.{max u v} (replacement_stage (J := J) ℱ n) :=
      replacement_stage_small (J := J) (ℱ := ℱ)
    dsimp [Q]
    infer_instance
  have hstage : ∀ n, replacement_stage (J := J) ℱ n ≤ Q := by
    intro n
    exact le_iSup (fun n ↦ replacement_stage (J := J) ℱ n) n
  have hle :
      replacement_object_property (J := J) ℱ ≤ Q.isoClosure := by
    intro X hX
    induction hX with
    | sheafifiedRepresentable U =>
        -- The sheafified representables are already present at stage `0`.
        refine ⟨h[U]^#[J], ?_, ⟨Iso.refl _⟩⟩
        exact (hstage 0) _ (by
          simpa [replacement_stage] using
            (ObjectProperty.ofObj_apply
              (fun x : C ⊕ (I ⊕ Unit) =>
                Sum.elim
                  (fun U ↦ h[U]^#[J])
                  (fun y ↦
                    Sum.elim (fun i ↦ ℱ i)
                      (fun _ ↦ Sheaf.terminal J Types.isTerminalPUnit) y)
                  x)
              (Sum.inl U)))
    | family i =>
        -- The chosen family is likewise part of the base stage.
        refine ⟨ℱ i, ?_, ⟨Iso.refl _⟩⟩
        exact (hstage 0) _ (by
          simpa [replacement_stage] using
            (ObjectProperty.ofObj_apply
              (fun x : C ⊕ (I ⊕ Unit) =>
                Sum.elim
                  (fun U ↦ h[U]^#[J])
                  (fun y ↦
                    Sum.elim (fun i ↦ ℱ i)
                      (fun _ ↦ Sheaf.terminal J Types.isTerminalPUnit) y)
                  x)
              (Sum.inr (Sum.inl i))))
    | terminal =>
        -- The terminal sheaf is the final generator in the base stage.
        refine ⟨Sheaf.terminal J Types.isTerminalPUnit, ?_, ⟨Iso.refl _⟩⟩
        exact (hstage 0) _ (by
          simpa [replacement_stage] using
            (ObjectProperty.ofObj_apply
              (fun x : C ⊕ (I ⊕ Unit) =>
                Sum.elim
                  (fun U ↦ h[U]^#[J])
                  (fun y ↦
                    Sum.elim (fun i ↦ ℱ i)
                      (fun _ ↦ Sheaf.terminal J Types.isTerminalPUnit) y)
                  x)
              (Sum.inr (Sum.inr ()))))
    | pullback f g hX hY hZ ihX ihY ihZ =>
        -- Move all three objects to a common stage and realize the new pullback at the next stage.
        rcases ihX with ⟨X', hXQ, ⟨eX⟩⟩
        rcases ihY with ⟨Y', hYQ, ⟨eY⟩⟩
        rcases ihZ with ⟨Z', hZQ, ⟨eZ⟩⟩
        rcases (by simpa [Q] using hXQ : ∃ nX, replacement_stage (J := J) ℱ nX X') with
          ⟨nX, hXn⟩
        rcases (by simpa [Q] using hYQ : ∃ nY, replacement_stage (J := J) ℱ nY Y') with
          ⟨nY, hYn⟩
        rcases (by simpa [Q] using hZQ : ∃ nZ, replacement_stage (J := J) ℱ nZ Z') with
          ⟨nZ, hZn⟩
        let n := max nX (max nY nZ)
        have hnX : nX ≤ n := le_max_left _ _
        have hnYZ : max nY nZ ≤ n := le_max_right _ _
        have hnY : nY ≤ n := le_trans (le_max_left _ _) hnYZ
        have hnZ : nZ ≤ n := le_trans (le_max_right _ _) hnYZ
        have hXn' : replacement_stage (J := J) ℱ n X' :=
          replacement_stage_monotone (J := J) (ℱ := ℱ) hnX X' hXn
        have hYn' : replacement_stage (J := J) ℱ n Y' :=
          replacement_stage_monotone (J := J) (ℱ := ℱ) hnY Y' hYn
        have hZn' : replacement_stage (J := J) ℱ n Z' :=
          replacement_stage_monotone (J := J) (ℱ := ℱ) hnZ Z' hZn
        let f' : X' ⟶ Z' := eX.inv ≫ f ≫ eZ.hom
        let g' : Y' ⟶ Z' := eY.inv ≫ g ≫ eZ.hom
        have hpullStage :
            replacement_stage (J := J) ℱ (n + 1) (pullback f' g') := by
          -- The source proof adds pullbacks of stage-`n` objects at stage `n + 1`.
          exact replacement_stage_pullback (J := J) (ℱ := ℱ) n f' g' hXn' hYn' hZn'
        have hpullQ : Q (pullback f' g') :=
          (hstage (n + 1)) _ hpullStage
        refine ⟨pullback f' g', hpullQ, ?_⟩
        -- The original pullback is canonically isomorphic to the pullback built after replacing
        -- each vertex by a stage representative.
        refine ⟨asIso (pullback.map f g f' g' eX.hom eY.hom eZ.hom ?_ ?_)⟩
        · dsimp [f']
          simp
        · dsimp [g']
          simp
    | @of_mono X Y f _ hY ihY =>
        -- Successor stages contain a chosen representative for every subobject of a stage object.
        rcases ihY with ⟨Y', hYQ, ⟨eY⟩⟩
        rcases (by simpa [Q] using hYQ : ∃ n, replacement_stage (J := J) ℱ n Y') with
          ⟨n, hYn⟩
        let X' : Sheaf J (Type (max u v)) :=
          ((Subobject.mk (f ≫ eY.hom)) : Subobject Y')
        have hXStage : replacement_stage (J := J) ℱ (n + 1) X' := by
          change
            (((replacement_stage (J := J) ℱ n ⊔
                (replacement_stage (J := J) ℱ n).strictLimitsOfShape WalkingCospan) ⊔
                replacement_subobject_stage (J := J) (replacement_stage (J := J) ℱ n))
              X')
          refine Or.inr ?_
          change
            replacement_subobject_stage (J := J) (replacement_stage (J := J) ℱ n) X'
          change
            ObjectProperty.ofObj
              (fun x : Σ Y : Subtype (replacement_stage (J := J) ℱ n), Subobject Y.1 ↦
                ((x.2 : Subobject x.1.1) : Sheaf J (Type (max u v))))
              X'
          exact
            ⟨(⟨⟨Y', hYn⟩, Subobject.mk (f ≫ eY.hom)⟩ :
              Σ Y : Subtype (replacement_stage (J := J) ℱ n), Subobject Y.1)⟩
        have hXQ : Q X' :=
          (hstage (n + 1)) _ hXStage
        exact ⟨X', hXQ, ⟨(Subobject.underlyingIso (f ≫ eY.hom)).symm⟩⟩
  exact ⟨Q, hQsmall, hle⟩

omit [HasWeakSheafify J (Type (max u v))] in
/-- Helper for Lemma 7.29.5: once the replacement object property is essentially small, its full
subcategory has a `Type (max u v)`-small model. -/
private theorem replacement_fullSubcategory_essentiallySmall
    (P : ObjectProperty (Sheaf J (Type (max u v))))
    (hP : ObjectProperty.EssentiallySmall.{max u v} P) :
    EssentiallySmall.{max u v} P.FullSubcategory := by
  let _ : ObjectProperty.EssentiallySmall.{max u v} P := hP
  infer_instance

/-- Helper for Lemma 7.29.5: transporting the surjective topology on the intermediate replacement
site to its small model preserves subcanonicality. -/
private theorem replacement_smallModel_inducedTopology_subcanonical
    {C₀ : Type u₀} [Category.{v₀} C₀]
    (J₀ : GrothendieckTopology C₀)
    [J₀.Subcanonical] [EssentiallySmall.{max u v} C₀] :
    ((equivSmallModel.{max u v} C₀).inverse.inducedTopology J₀).Subcanonical := by
  let e : C₀ ≌ SmallModel.{max u v} C₀ := equivSmallModel.{max u v} C₀
  let _ : Functor.IsContinuous e.inverse (e.inverse.inducedTopology J₀) J₀ := inferInstance
  exact GrothendieckTopology.subcanonical_of_full_of_faithful
    (F := e.inverse) (J := e.inverse.inducedTopology J₀) (K := J₀)

/-- Helper for Lemma 7.29.5: finite limits on the intermediate replacement site transport to its
small model along `equivSmallModel`. -/
private theorem replacement_smallModel_hasFiniteLimits
    {C₀ : Type u₀} [Category.{v₀} C₀]
    [HasFiniteLimits C₀] [EssentiallySmall.{max u v} C₀] :
    HasFiniteLimits (SmallModel.{max u v} C₀) := by
  refine hasFiniteLimits_of_hasFiniteLimits_of_size (C := SmallModel.{max u v} C₀) ?_
  intro K _ _
  let hK : HasLimitsOfShape K C₀ := HasFiniteLimits.out (C := C₀) K
  let _ : HasLimitsOfShape K C₀ := hK
  exact Adjunction.hasLimitsOfShape_of_equivalence (equivSmallModel.{max u v} C₀).inverse

/-- Helper for Lemma 7.29.5: the dense-subsite comparison from the intermediate replacement site
composes with the induced-topology dense-subsite structure on its small model. -/
private theorem replacement_composite_dense_subsite
    {C₀ : Type u₀} [Category.{v₀} C₀]
    {C' : Type (max u v)} [Category C']
    (J₀ : GrothendieckTopology C₀)
    (e : C₀ ≌ C')
    (v₀ : C ⥤ C₀)
    [v₀.IsDenseSubsite J J₀] :
    (v₀ ⋙ e.functor).IsDenseSubsite J (e.inverse.inducedTopology J₀) := by
  -- The small-model equivalence contributes the induced-topology dense-subsite owner, and the
  -- composite dense-subsite structure is assembled by transporting each field through the
  -- equivalence `e`.
  let _ : e.functor.IsDenseSubsite J₀ (e.inverse.inducedTopology J₀) := by
    infer_instance
  let _ : v₀.IsCoverDense J₀ := Functor.IsDenseSubsite.isCoverDense (J := J) (K := J₀) (G := v₀)
  let _ : v₀.IsLocallyFull J₀ :=
    Functor.IsDenseSubsite.isLocallyFull (J := J) (K := J₀) (G := v₀)
  let _ : v₀.IsLocallyFaithful J₀ :=
    Functor.IsDenseSubsite.isLocallyFaithful (J := J) (K := J₀) (G := v₀)
  have hcoverDense : (v₀ ⋙ e.functor).IsCoverDense (e.inverse.inducedTopology J₀) := by
    refine ⟨?_⟩
    intro X
    -- To cover `X` in the induced topology, pull back the usual `v₀`-cover of `e.inverse.obj X`
    -- and bridge the comparison map with the unit-counit identities.
    rw [Functor.mem_inducedTopology_sieves_iff]
    refine J₀.superset_covering ?_ (v₀.is_cover_of_isCoverDense J₀ (e.inverse.obj X))
    intro Y f hf
    rcases hf with ⟨⟨Z, lift, map, fac⟩⟩
    let g : (v₀ ⋙ e.functor).obj Z ⟶ X :=
      e.functor.map map ≫ e.counit.app X
    refine ⟨_, g, lift ≫ e.unit.app (v₀.obj Z), ?_, ?_⟩
    · exact Presieve.in_coverByImage (v₀ ⋙ e.functor) g
    · -- The unit/counit identities reduce the transported factorization back to the original
      -- factorization through `v₀`.
      simpa [g, Category.assoc] using fac.symm
  refine
    { isCoverDense' := hcoverDense
      isLocallyFull' := ?_
      isLocallyFaithful' := ?_
      functorPushforward_mem_iff := ?_ }
  · refine ⟨?_⟩
    intro U V f
    let f₀ : v₀.obj U ⟶ v₀.obj V := e.functor.preimage f
    have himage :
        (v₀ ⋙ e.functor).imageSieve f = v₀.imageSieve f₀ := by
      -- Fullness and faithfulness of `e.functor` identify the image-sieve condition before and
      -- after transport to the small model.
      ext W i
      constructor
      · rintro ⟨l, hl⟩
        refine ⟨l, ?_⟩
        apply e.functor.map_injective
        simpa [f₀, Functor.comp_map] using hl
      · rintro ⟨l, hl⟩
        refine ⟨l, ?_⟩
        simpa [f₀, Functor.comp_map] using congrArg (fun k ↦ e.functor.map k) hl
    have hmem₀ :
        (v₀.imageSieve f₀).functorPushforward v₀ ∈ J₀ (v₀.obj U) :=
      v₀.functorPushforward_imageSieve_mem J₀ f₀
    have hmem :
        ((v₀.imageSieve f₀).functorPushforward v₀).functorPushforward e.functor ∈
          (e.inverse.inducedTopology J₀) ((v₀ ⋙ e.functor).obj U) :=
      (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J₀)
        (K := e.inverse.inducedTopology J₀) (G := e.functor)).mpr hmem₀
    simpa [himage, Sieve.functorPushforward_comp] using hmem
  · refine ⟨?_⟩
    intro U V a b hab
    have hab₀ : v₀.map a = v₀.map b := by
      exact e.functor.map_injective hab
    have hmem₀ :
        (Sieve.equalizer a b).functorPushforward v₀ ∈ J₀ (v₀.obj U) :=
      v₀.functorPushforward_equalizer_mem J₀ a b hab₀
    have hmem :
        ((Sieve.equalizer a b).functorPushforward v₀).functorPushforward e.functor ∈
          (e.inverse.inducedTopology J₀) ((v₀ ⋙ e.functor).obj U) :=
      (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J₀)
        (K := e.inverse.inducedTopology J₀) (G := e.functor)).mpr hmem₀
    simpa [Sieve.functorPushforward_comp] using hmem
  · intro X S
    constructor
    · intro hS
      have hS₀ : (S.functorPushforward v₀).functorPushforward e.functor ∈
          (e.inverse.inducedTopology J₀) ((v₀ ⋙ e.functor).obj X) := by
        simpa [Sieve.functorPushforward_comp] using hS
      have hS₁ : S.functorPushforward v₀ ∈ J₀ (v₀.obj X) :=
        (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J₀)
          (K := e.inverse.inducedTopology J₀) (G := e.functor)).mp hS₀
      exact
        (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J) (K := J₀) (G := v₀)).mp hS₁
    · intro hS
      have hS₀ : S.functorPushforward v₀ ∈ J₀ (v₀.obj X) :=
        (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J) (K := J₀) (G := v₀)).mpr hS
      have hS₁ : (S.functorPushforward v₀).functorPushforward e.functor ∈
          (e.inverse.inducedTopology J₀) ((v₀ ⋙ e.functor).obj X) :=
        (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J₀)
          (K := e.inverse.inducedTopology J₀) (G := e.functor)).mpr hS₀
      simpa [Sieve.functorPushforward_comp] using hS₁

/-- Helper for Lemma 7.29.5: on the intermediate site produced from the replacement full
subcategory, the dense-subsite equivalence sends any ambient sheaf `X₀.obj` back to the
representable sheaf of `X₀`. -/
private noncomputable def replacement_intermediate_transport_iso
    (P : ObjectProperty (Sheaf J (Type (max u v))))
    [P.IsClosedUnderLimitsOfShape WalkingCospan]
    (hP : ∀ U : C, P (h[U]^#[J]))
    (X₀ : P.FullSubcategory) :
    ((sheafEquiv J (ObjectProperty.sheafSubcategorySurjectiveTopology P)
        (ObjectProperty.sheafSubcategoryRepresentableFunctor P hP) (Type (max u v))).functor.obj
        X₀.obj) ≅
      (ObjectProperty.sheafSubcategorySurjectiveTopology P).yoneda.obj X₀ := by
  let q := (ObjectProperty.sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardContinuous
    (Type (max u v)) J (ObjectProperty.sheafSubcategorySurjectiveTopology P)
  let _ : q.IsEquivalence := inferInstance
  let e := q.asEquivalence
  -- Apply the quasi-inverse of the dense-subsite equivalence to the inverse-image comparison from
  -- Lemma 7.29.4, then close with the equivalence unit at the representable sheaf of `X₀`.
  change (e.inverse.obj X₀.obj) ≅
      (ObjectProperty.sheafSubcategorySurjectiveTopology P).yoneda.obj X₀
  exact
    e.inverse.mapIso
      (ObjectProperty.sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso
        (P := P) (hP := hP) X₀).symm ≪≫
      (e.unitIso.app ((ObjectProperty.sheafSubcategorySurjectiveTopology P).yoneda.obj X₀)).symm

/-- Helper for Lemma 7.29.5: on the intermediate replacement site, every subobject of a
representable sheaf comes from a generated ambient sheaf by pulling it back through the
dense-subsite equivalence, so its underlying presheaf is representable. -/
private theorem replacement_intermediate_subobject_representable
    (X₀ :
      (replacement_object_property (J := J) ℱ).FullSubcategory)
    (G₀ :
      Subobject
        ((ObjectProperty.sheafSubcategorySurjectiveTopology
          (replacement_object_property (J := J) ℱ)).yoneda.obj X₀)) :
    ((G₀ :
      Sheaf
        (ObjectProperty.sheafSubcategorySurjectiveTopology
          (replacement_object_property (J := J) ℱ))
        (Type (max u v))).obj).IsRepresentable := by
  let P := replacement_object_property (J := J) ℱ
  let hP : ∀ U : C, P (h[U]^#[J]) :=
    fun U ↦ replacement_object_property.sheafifiedRepresentable (J := J) (ℱ := ℱ) U
  let J₀ : GrothendieckTopology P.FullSubcategory :=
    ObjectProperty.sheafSubcategorySurjectiveTopology P
  let v₀ : C ⥤ P.FullSubcategory :=
    ObjectProperty.sheafSubcategoryRepresentableFunctor P hP
  let E := sheafEquiv J J₀ v₀ (Type (max u v))
  let pulledArrow :
      E.inverse.obj (G₀ : Sheaf J₀ (Type (max u v))) ⟶ X₀.obj :=
    E.inverse.map
        (G₀.arrow ≫
          (replacement_intermediate_transport_iso
            (J := J) (P := P) hP X₀).inv) ≫
      (E.unitIso.app X₀.obj).inv
  have hpulled :
      P (E.inverse.obj (G₀ : Sheaf J₀ (Type (max u v)))) := by
    -- Pull the mono representative of `G₀` back to `Sh(J)` and use the source closure under
    -- subobjects encoded in `replacement_object_property`.
    exact
      replacement_object_property.of_mono (J := J) (ℱ := ℱ) pulledArrow X₀.property
  let X₁ : P.FullSubcategory :=
    ⟨E.inverse.obj (G₀ : Sheaf J₀ (Type (max u v))), hpulled⟩
  have hrepr_yoneda :
      (((J₀.yoneda.obj X₁).obj)).IsRepresentable := by
    -- The intermediate site is subcanonical, so the underlying presheaf of a representable sheaf
    -- is represented by the same object.
    exact
      isRepresentable_of_natIso (CategoryTheory.yoneda.obj X₁)
        ((J₀.yonedaCompSheafToPresheaf.app X₁).symm)
  have hrepr_transport :
      ((E.functor.obj X₁.obj).obj).IsRepresentable := by
    -- Route correction: we now transport representability through the explicit comparison iso on
    -- the intermediate site instead of trying to normalize the small-model transport first.
    exact
      isRepresentable_of_natIso (((J₀.yoneda.obj X₁).obj))
        (((sheafToPresheaf J₀ (Type (max u v))).mapIso
          (replacement_intermediate_transport_iso
            (J := J) (P := P) hP X₁)).symm)
  have hrepr_G₀ :
      ((G₀ : Sheaf J₀ (Type (max u v))).obj).IsRepresentable := by
    -- Finally, identify the transported source object with the original subobject via the
    -- equivalence counit.
    exact
      isRepresentable_of_natIso ((E.functor.obj X₁.obj).obj) <| by
        simpa [E, X₁] using
          (sheafToPresheaf J₀ (Type (max u v))).mapIso
            (E.counitIso.app (G₀ : Sheaf J₀ (Type (max u v))))
  simpa [J₀] using hrepr_G₀

/- Domain-style sampling for Lemma 7.29.5:
- primary domain: replacement-site presentations of a sheaf topos through full subcategories of
  sheaves, equipped with the canonical surjective topology from Lemma `7.29.4`;
- sampled owner declarations:
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.IsClosedUnderSubobjects`,
  `ObjectProperty.sheafSubcategorySurjectiveTopology`,
  `ObjectProperty.sheafSubcategoryRepresentableFunctor`,
  `Presheaf.IsLocallySurjective`,
  `Functor.IsDenseSubsite`,
  `Functor.IsDenseSubsite.sheafEquiv`;
- best owner abstraction: the source-facing statement should expose the replacement site
  `(C', J')`, its dense-subsite comparison functor `v : C ⥤ C'`, and the canonical dense-subsite
  sheaf equivalence `sheafEquiv J J' v`; the internal `ObjectProperty` full-subcategory
  presentation from Lemma `7.29.4` is only the construction layer producing that site;
- primitive data: the replacement category `C'`, its topology `J'`, finite limits on `C'`, and the
  comparison functor `v`;
- derived API: subcanonicality of `J'`, the dense-subsite owner on `v`, the induced sheaf
  equivalence `sheafEquiv J J' v`, and the owner-level representability predicates on every
  subsheaf of a representable sheaf on the replacement site and on the transported family.

Source/core/bridge triage:
- `source-facing`: the replacement site with its canonical surjective topology, together with the
  special-cocontinuous comparison and the fact that the chosen family becomes representable there;
- `core/canonical`: `Functor.IsDenseSubsite`, `sheafEquiv`, and the site-level owners
  `GrothendieckTopology.Subcanonical` and `HasFiniteLimits`;
- `bridge/view`: the internal `ObjectProperty` full-subcategory construction from Lemma `7.29.4`,
  used only to build the replacement site realizing the theorem.
-/

-- Proof sketch: build the replacement site from the full subcategory of `Sh(J)` generated by the
-- sheafified representables and the chosen family, closed under fibre products and subobjects.
-- Lemma `7.29.4` equips that full subcategory with its canonical surjective topology, whose
-- covering families are exactly the family presentations whose induced coproduct map of
-- representable presheaves is locally surjective. We then state only the resulting replacement
-- site `(C', J')`, the dense-subsite functor `v : C ⥤ C'`, this covering characterization, and
-- the canonical representability consequences.
/-- Helper for Lemma 7.29.5: under a subcanonical topology, the sheafified-representable functor
`U ↦ h_U^#` is fully faithful, because it is isomorphic to the sheaf-valued ulift-Yoneda
embedding (subcanonical representables are already sheaves), which is fully faithful. -/
private noncomputable def sheafifiedRepresentableFunctor_fullyFaithful (hJ : J.Subcanonical) :
    (J.sheafifiedRepresentableFunctor).FullyFaithful := by
  haveI := hJ
  exact (GrothendieckTopology.fullyFaithfulUliftYoneda J).ofIso
    (Functor.isoWhiskerLeft (GrothendieckTopology.uliftYoneda J)
        (sheafificationNatIso J (Type (max u v))) ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerRight (GrothendieckTopology.uliftYonedaCompSheafToPresheaf J)
        (presheafToSheaf J (Type (max u v))))

/-- Lemma 7.29.5: every `Type (max u v)`-small set-indexed family of sheaves on `Sh(J)` admits a replacement site
`(C', J')` with finite limits and subcanonical topology, together with a dense-subsite comparison
functor `v : C ⥤ C'`, such that a family on `C'` is covering exactly when the induced coproduct
map of representable presheaves is locally surjective, every subsheaf of a representable sheaf on
the replacement site has representable underlying presheaf, and, under the canonical
dense-subsite equivalence `sheafEquiv J J' v`, each sheaf `ℱ i` has representable underlying
presheaf on the replacement site. The construction is realized internally by the full-subcategory
presentation of Lemma `7.29.4`, but that construction layer is not part of the public API here. -/
theorem exists_representable_family_site_presentation [Small.{max u v} I] :
    ∃ (C' : Type (max u v)) (_ : Category C') (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (v : C ⥤ C') (_ : v.IsDenseSubsite J J')
      (_ : J.Subcanonical → v.FullyFaithful)
      (hcover :
        ∀ ⦃X : C'⦄ (R : Presieve X),
        R ∈ J'.toPrecoverage X ↔
          ∃ (ι : Type (max u v)) (Y : ι → C') (π : ∀ i, Y i ⟶ X),
            R = Presieve.ofArrows Y π ∧
              Presheaf.IsLocallySurjective J'
                (Limits.Sigma.desc (fun i ↦ (J'.yoneda.map (π i)).hom)))
      (hsub :
        ∀ X : C', ∀ G : Subobject (J'.yoneda.obj X),
          ((G : Sheaf J' (Type (max u v))).obj).IsRepresentable),
      ∀ i : I,
        (((sheafEquiv J J' v (Type (max u v))).functor.obj (ℱ i)).obj).IsRepresentable := by
  let P := replacement_object_property (J := J) ℱ
  let C₀ : Type (max (u + 1) (v + 1)) := P.FullSubcategory
  let hP : ∀ U : C, P (h[U]^#[J]) :=
    fun U ↦ replacement_object_property.sheafifiedRepresentable (J := J) (ℱ := ℱ) U
  let J₀ : GrothendieckTopology C₀ := ObjectProperty.sheafSubcategorySurjectiveTopology P
  let v₀ : C ⥤ C₀ := ObjectProperty.sheafSubcategoryRepresentableFunctor P hP
  let _ : J₀.Subcanonical := ObjectProperty.sheafSubcategorySurjectiveTopology_subcanonical (P := P)
  let _ : HasTerminal C₀ := inferInstance
  let _ : HasPullbacks C₀ := inferInstance
  let _ : HasFiniteLimits C₀ := replacement_fullSubcategory_hasFiniteLimits (J := J) (ℱ := ℱ)
  -- Route correction: the proof now follows the source proof's set-theoretic owner explicitly.
  -- The source phrase "a set of sheaves" is represented by `[Small.{max u v} I]`; without
  -- this hypothesis the small-model target `Type (max u v)` cannot contain the family generators.
  -- The large full subcategory from Lemma `7.29.4` is only an intermediate site.
  -- TODO: assemble the verified stage filtration (`replacement_stage_small` and
  -- `replacement_stage_le_property`) into essential smallness of the generated property.
  have hsmallP : ObjectProperty.EssentiallySmall.{max u v} P := by
    -- The small stage filtration is the source-proof realization of the phrase "a set of
    -- objects closed under fibre products and subsheaves".
    exact replacement_object_property_essentiallySmall (J := J) (ℱ := ℱ)
  -- Package the induced essential smallness of the intermediate full subcategory once so later
  -- small-model transport does not have to re-solve the same universe problem.
  have hsmallC₀ : EssentiallySmall.{max u v} C₀ := by
    change EssentiallySmall.{max u v} P.FullSubcategory
    exact replacement_fullSubcategory_essentiallySmall (J := J) (P := P) hsmallP
  let e : C₀ ≌ SmallModel.{max u v} C₀ :=
    @equivSmallModel C₀ _ hsmallC₀
  let C' : Type (max u v) := SmallModel.{max u v} C₀
  let J' : GrothendieckTopology C' := e.inverse.inducedTopology J₀
  let v : C ⥤ C' := v₀ ⋙ e.functor
  -- Transport subcanonicality from the intermediate site to its small model.
  have hsubcanonical : J'.Subcanonical := by
    let _ : Functor.IsContinuous e.inverse (e.inverse.inducedTopology J₀) J₀ := inferInstance
    simpa [J'] using
      (GrothendieckTopology.subcanonical_of_full_of_faithful
        (F := e.inverse) (J := e.inverse.inducedTopology J₀) (K := J₀))
  let _ : J'.Subcanonical := hsubcanonical
  -- Transport finite limits along the same small-model equivalence.
  have hfinite : HasFiniteLimits C' := by
    refine hasFiniteLimits_of_hasFiniteLimits_of_size (C := C') ?_
    intro K _ _
    let hK : HasLimitsOfShape K C₀ := HasFiniteLimits.out (C := C₀) K
    let _ : HasLimitsOfShape K C₀ := hK
    simpa [C', e] using Adjunction.hasLimitsOfShape_of_equivalence e.inverse
  -- The source dense-subsite comparison from Lemma `7.29.4` composes with the induced-topology
  -- dense-subsite structure on the small-model equivalence.
  have hdense : v.IsDenseSubsite J J' := by
    -- Route correction: the source proof uses one comparison functor `v`, so we package the
    -- intermediate and small-model dense-subsite owners into a single composite lemma first.
    let _ : v₀.IsDenseSubsite J J₀ := inferInstance
    simpa [v, J'] using
      replacement_composite_dense_subsite (J := J) (J₀ := J₀) e v₀
  -- Route correction: the remaining blocker is the theorem-local Yoneda comparison on the
  -- small model, after all relevant `J₀`/`J'` instances have been fixed.
  have hyonedaTransport :
      ∀ X : C',
        ((e.sheafCongr J₀ J' (Type (max u v))).functor.obj
          (J₀.yoneda.obj (e.inverse.obj X))) ≅
          (J'.yoneda.obj X) := by
    intro X
    -- Forget to presheaves so the small-model transport is reduced to the explicit representable
    -- comparison coming from the equivalence adjunction and the counit at `X`.
    refine (fullyFaithfulSheafToPresheaf J' (Type (max u v))).preimageIso ?_
    simpa [Equivalence.sheafCongr, Equivalence.sheafCongr.functor] using
      (Functor.isoWhiskerLeft e.inverse.op
          (J₀.yonedaCompSheafToPresheaf.app (e.inverse.obj X)) ≪≫
        (((e.symm.toAdjunction.representableBy (e.inverse.obj X)).toIso).symm ≪≫
          CategoryTheory.yoneda.mapIso (e.counitIso.app X)) ≪≫
        (J'.yonedaCompSheafToPresheaf.app X).symm)
  -- The remaining work is exactly the transport package from `(C₀, J₀)` to `(C', J')`.
  -- TODO: rewrite `J'` through `e.inverse.inducedTopology J₀` and transport the `J₀`-cover
  -- characterization from Lemma `7.29.4` across the equivalence `e`.
  have hcover :
      ∀ ⦃X : C'⦄ (R : Presieve X),
        R ∈ J'.toPrecoverage X ↔
          ∃ (ι : Type (max u v)) (Y : ι → C') (π : ∀ i, Y i ⟶ X),
            R = Presieve.ofArrows Y π ∧
              Presheaf.IsLocallySurjective J'
                (Limits.Sigma.desc (fun i ↦ (J'.yoneda.map (π i)).hom)) := by
    intro X R
    constructor
    · intro hR
      let ι : Type (max u v) := R.uncurry
      let Y : ι → C' := fun i ↦ i.1.1
      let π : ∀ i, Y i ⟶ X := fun i ↦ i.1.2
      have hR_eq : R = Presieve.ofArrows Y π := by
        -- Every presieve is the family of its own elements, so `toPrecoverage` already has the
        -- theorem-facing source shape.
        funext Z g
        apply propext
        constructor
        · intro hg
          simpa [Y, π] using
            (Presieve.ofArrows.mk (Y := Y) (f := π) (⟨⟨Z, g⟩, hg⟩ : ι))
        · rintro ⟨i⟩
          exact i.2
      refine ⟨ι, Y, π, hR_eq, ?_⟩
      have hcovering : Sieve.ofArrows Y π ∈ J' X := by
        -- `toPrecoverage` membership is exactly coverhood of the generated sieve.
        rw [hR_eq, GrothendieckTopology.mem_toPrecoverage_iff] at hR
        simpa [Sieve.ofArrows] using hR
      have hsurj_ulift :
          Presheaf.IsLocallySurjective J'
            (Limits.Sigma.desc
              (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i))) := by
        -- Use the generic cover criterion on the already-subcanonical small model.
        exact
          (J'.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map π).1 hcovering
      let eYoneda :
          CategoryTheory.uliftYoneda.{max u v} (C := C') ≅ CategoryTheory.yoneda :=
        CategoryTheory.uliftYonedaIsoYoneda.{max u v} (C := C')
      let sourceIso :
          (∐ fun i ↦ CategoryTheory.uliftYoneda.{max u v}.obj (Y i)) ⟶
            ∐ fun i ↦ CategoryTheory.yoneda.obj (Y i) :=
        Limits.Sigma.map (fun i ↦ (eYoneda.app (Y i)).hom)
      have hdesc :
          sourceIso ≫ Limits.Sigma.desc (fun i ↦ CategoryTheory.yoneda.map (π i)) =
            Limits.Sigma.desc
                (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i)) ≫
              (eYoneda.app X).hom := by
        -- Compare the two Sigma-desc maps componentwise through the Yoneda universe-change isos
        -- on both the source coproduct and the target representable.
        apply Limits.Sigma.hom_ext
        intro i
        rw [Limits.Sigma.ι_map_assoc]
        calc
          (eYoneda.app (Y i)).hom ≫
              Sigma.ι (fun i ↦ CategoryTheory.yoneda.obj (Y i)) i ≫
                Limits.Sigma.desc (fun i ↦ CategoryTheory.yoneda.map (π i)) =
            (eYoneda.app (Y i)).hom ≫ CategoryTheory.yoneda.map (π i) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ (eYoneda.app (Y i)).hom ≫ k)
                  (Limits.Sigma.ι_desc
                    (p := fun i ↦ CategoryTheory.yoneda.map (π i)) (b := i))
          _ = CategoryTheory.uliftYoneda.{max u v}.map (π i) ≫ (eYoneda.app X).hom := by
              simpa using (NatTrans.naturality eYoneda.hom (π i)).symm
          _ =
              Sigma.ι (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.obj (Y i)) i ≫
                Limits.Sigma.desc (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i)) ≫
                  (eYoneda.app X).hom := by
              symm
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ (eYoneda.app X).hom)
                  (Limits.Sigma.ι_desc
                    (p := fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i)) (b := i))
      have hsurj_composite :
          Presheaf.IsLocallySurjective J'
            (sourceIso ≫ Limits.Sigma.desc (fun i ↦ CategoryTheory.yoneda.map (π i))) := by
        -- Re-express the theorem-facing map as the generic `uliftYoneda` map followed by an
        -- isomorphism of representables.
        rw [hdesc]
        infer_instance
      have hsurj_yoneda :
          Presheaf.IsLocallySurjective J'
            (Limits.Sigma.desc (fun i ↦ CategoryTheory.yoneda.map (π i))) := by
        -- Since the source coproduct comparison is an isomorphism, local surjectivity can be read
        -- off after cancelling that source factor.
        exact
          (Presheaf.comp_isLocallySurjective_iff J' sourceIso
            (Limits.Sigma.desc (fun i ↦ CategoryTheory.yoneda.map (π i)))).1 hsurj_composite
      simpa using hsurj_yoneda
    · rintro ⟨ι, Y, π, rfl, hsurj⟩
      let eYoneda :
          CategoryTheory.uliftYoneda.{max u v} (C := C') ≅ CategoryTheory.yoneda :=
        CategoryTheory.uliftYonedaIsoYoneda.{max u v} (C := C')
      let sourceIso :
          (∐ fun i ↦ CategoryTheory.uliftYoneda.{max u v}.obj (Y i)) ⟶
            ∐ fun i ↦ CategoryTheory.yoneda.obj (Y i) :=
        Limits.Sigma.map (fun i ↦ (eYoneda.app (Y i)).hom)
      have hdesc :
          sourceIso ≫ Limits.Sigma.desc (fun i ↦ CategoryTheory.yoneda.map (π i)) =
            Limits.Sigma.desc
                (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i)) ≫
              (eYoneda.app X).hom := by
        -- The same componentwise comparison turns the theorem-facing Yoneda map back into the
        -- generic `uliftYoneda` cover map.
        apply Limits.Sigma.hom_ext
        intro i
        rw [Limits.Sigma.ι_map_assoc]
        calc
          (eYoneda.app (Y i)).hom ≫
              Sigma.ι (fun i ↦ CategoryTheory.yoneda.obj (Y i)) i ≫
                Limits.Sigma.desc (fun i ↦ CategoryTheory.yoneda.map (π i)) =
            (eYoneda.app (Y i)).hom ≫ CategoryTheory.yoneda.map (π i) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ (eYoneda.app (Y i)).hom ≫ k)
                  (Limits.Sigma.ι_desc
                    (p := fun i ↦ CategoryTheory.yoneda.map (π i)) (b := i))
          _ = CategoryTheory.uliftYoneda.{max u v}.map (π i) ≫ (eYoneda.app X).hom := by
              simpa using (NatTrans.naturality eYoneda.hom (π i)).symm
          _ =
              Sigma.ι (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.obj (Y i)) i ≫
                Limits.Sigma.desc (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i)) ≫
                  (eYoneda.app X).hom := by
              symm
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ (eYoneda.app X).hom)
                  (Limits.Sigma.ι_desc
                    (p := fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i)) (b := i))
      have hsurj_yoneda :
          Presheaf.IsLocallySurjective J'
            (Limits.Sigma.desc (fun i ↦ CategoryTheory.yoneda.map (π i))) := by
        simpa using hsurj
      have hsurj_composite :
          Presheaf.IsLocallySurjective J'
            (sourceIso ≫ Limits.Sigma.desc (fun i ↦ CategoryTheory.yoneda.map (π i))) := by
        -- Add the source coproduct comparison before switching to the generic `uliftYoneda`
        -- presentation of the cover map.
        let _ :
            Presheaf.IsLocallySurjective J'
              (Limits.Sigma.desc (fun i ↦ CategoryTheory.yoneda.map (π i))) :=
          hsurj_yoneda
        infer_instance
      have hsurj_ulift :
          Presheaf.IsLocallySurjective J'
            (Limits.Sigma.desc
              (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i))) := by
        have hsurj_target :
            Presheaf.IsLocallySurjective J'
              (Limits.Sigma.desc
                  (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i)) ≫
                (eYoneda.app X).hom) := by
          -- Reinterpret the theorem-facing source map as the `uliftYoneda` comparison followed
          -- by the target Yoneda isomorphism.
          rw [← hdesc]
          exact hsurj_composite
        have hsurj_with_inv :
            Presheaf.IsLocallySurjective J'
              ((Limits.Sigma.desc
                    (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i)) ≫
                  (eYoneda.app X).hom) ≫
                (eYoneda.app X).inv) := by
          infer_instance
        simpa [Category.assoc] using hsurj_with_inv
      rw [GrothendieckTopology.mem_toPrecoverage_iff]
      -- Now the generic `uliftYoneda` criterion closes the covering statement.
      simpa [Sieve.ofArrows] using
        (J'.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map π).2 hsurj_ulift
  -- TODO: transfer representability of subsheaves of representables from `(C₀, J₀)` to `(C', J')`
  -- using `e.sheafCongr` and `CategoryTheory.isRepresentable_of_natIso`.
  have hsmall_model_representable_transport :
      ∀ {F : Sheaf J₀ (Type (max u v))},
        F.obj.IsRepresentable →
          (((e.sheafCongr J₀ J' (Type (max u v))).functor.obj F).obj).IsRepresentable := by
    intro F hF
    let E := e.sheafCongr J₀ J' (Type (max u v))
    let _ : F.obj.IsRepresentable := hF
    let Y : C₀ := F.obj.reprX
    have hF_iso : J₀.yoneda.obj Y ≅ F := by
      -- Lift the chosen representability witness from presheaves to sheaves on `(C₀, J₀)`.
      refine (fullyFaithfulSheafToPresheaf J₀ (Type (max u v))).preimageIso ?_
      exact (J₀.yonedaCompSheafToPresheaf.app Y).symm ≪≫ F.obj.reprW
    have hYoneda :
        E.functor.obj (J₀.yoneda.obj Y) ≅ J'.yoneda.obj (e.functor.obj Y) := by
      -- Transport the intermediate representable along the small-model equivalence using the unit
      -- comparison on the representing object.
      exact
        E.functor.mapIso (J₀.yoneda.mapIso (e.unitIso.app Y)) ≪≫
          hyonedaTransport (e.functor.obj Y)
    have htransport :
        E.functor.obj F ≅ J'.yoneda.obj (e.functor.obj Y) := by
      -- Rewrite `F` by its chosen `J₀`-representable model before pushing it to `(C', J')`.
      exact E.functor.mapIso hF_iso.symm ≪≫ hYoneda
    exact
      isRepresentable_of_natIso (CategoryTheory.yoneda.obj (e.functor.obj Y))
        ((J'.yonedaCompSheafToPresheaf.app (e.functor.obj Y)) ≪≫
          ((sheafToPresheaf J' (Type (max u v))).mapIso htransport).symm)
  have hsub :
      ∀ X : C', ∀ G : Subobject (J'.yoneda.obj X),
        ((G : Sheaf J' (Type (max u v))).obj).IsRepresentable := by
    intro X G
    let E := e.sheafCongr J₀ J' (Type (max u v))
    let pulledArrow :
        E.inverse.obj (G : Sheaf J' (Type (max u v))) ⟶
          J₀.yoneda.obj (e.inverse.obj X) :=
      E.inverse.map G.arrow ≫
        (E.inverse.mapIso (hyonedaTransport X).symm).hom ≫
        (E.unitIso.app (J₀.yoneda.obj (e.inverse.obj X))).inv
    let G₀ : Subobject (J₀.yoneda.obj (e.inverse.obj X)) := Subobject.mk pulledArrow
    have hrepr_G₀ :
        ((G₀ : Sheaf J₀ (Type (max u v))).obj).IsRepresentable := by
      -- Pull the `J'`-subobject back to the intermediate site so the `J₀`-side subobject lemma
      -- applies exactly in the source-proof order.
      exact
        replacement_intermediate_subobject_representable
          (J := J) (ℱ := ℱ) (X₀ := e.inverse.obj X) G₀
    have hrepr_transport :
        ((E.functor.obj (G₀ : Sheaf J₀ (Type (max u v)))).obj).IsRepresentable := by
      -- Representability is preserved when the explicit intermediate subobject is pushed to the
      -- small model.
      exact hsmall_model_representable_transport hrepr_G₀
    have hcompare :
        E.functor.obj (G₀ : Sheaf J₀ (Type (max u v))) ≅
          (G : Sheaf J' (Type (max u v))) := by
      -- The pushed-forward mono representative identifies with the original subobject through the
      -- equivalence counit.
      exact
        E.functor.mapIso (Subobject.underlyingIso pulledArrow) ≪≫
          E.counitIso.app (G : Sheaf J' (Type (max u v)))
    exact
      isRepresentable_of_natIso
        ((E.functor.obj (G₀ : Sheaf J₀ (Type (max u v)))).obj)
        ((sheafToPresheaf J' (Type (max u v))).mapIso hcompare)
  -- TODO: compare the theorem-facing `sheafEquiv J J' v` with the composite equivalence coming
  -- from `v₀` and `e.sheafCongr`, then transport representability of each `ℱ i`.
  have hfamilyComparison :
      (sheafEquiv J J' v (Type (max u v))).functor ≅
        (sheafEquiv J J₀ v₀ (Type (max u v))).functor ⋙
          (e.sheafCongr J₀ J' (Type (max u v))).functor := by
    let E₀ := sheafEquiv J J₀ v₀ (Type (max u v))
    let E := e.sheafCongr J₀ J' (Type (max u v))
    let Ev := sheafEquiv J J' v (Type (max u v))
    have hright :
        E.inverse ⋙ E₀.inverse ≅ Ev.inverse := by
      -- The composite right adjoint is the pushforward for `v = v₀ ⋙ e.functor`.
      simpa [E₀, E, Ev, v] using
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (v₀ ⋙ e.functor)) (Type (max u v)) J J₀ J')
    -- Compare the one-step dense-subsite equivalence with the two-step route through `(C₀, J₀)`
    -- by uniqueness of left adjoints to the same pushforward functor.
    exact
      (Adjunction.leftAdjointUniq
        ((Adjunction.comp E₀.toAdjunction E.toAdjunction).ofNatIsoRight hright)
        Ev.toAdjunction).symm
  have hfamily :
      ∀ i : I,
        (((sheafEquiv J J' v (Type (max u v))).functor.obj (ℱ i)).obj).IsRepresentable := by
    intro i
    let E₀ := sheafEquiv J J₀ v₀ (Type (max u v))
    let E := e.sheafCongr J₀ J' (Type (max u v))
    let X₀ : C₀ :=
      ⟨ℱ i, replacement_object_property.family (J := J) (ℱ := ℱ) i⟩
    have hrepr_intermediate :
        ((E₀.functor.obj (ℱ i)).obj).IsRepresentable := by
      -- On the intermediate replacement site, each chosen family member is already representable
      -- by the object added at stage `0` of the source construction.
      exact
        isRepresentable_of_natIso (CategoryTheory.yoneda.obj X₀)
          ((J₀.yonedaCompSheafToPresheaf.app X₀) ≪≫
            ((sheafToPresheaf J₀ (Type (max u v))).mapIso
              (replacement_intermediate_transport_iso
                (J := J) (P := P) hP X₀)).symm)
    have hrepr_composite :
        ((E.functor.obj (E₀.functor.obj (ℱ i))).obj).IsRepresentable := by
      -- Push the intermediate representable family generator forward to the small model.
      exact hsmall_model_representable_transport hrepr_intermediate
    exact
      isRepresentable_of_natIso
        ((E.functor.obj (E₀.functor.obj (ℱ i))).obj)
        (((sheafToPresheaf J' (Type (max u v))).mapIso (hfamilyComparison.app (ℱ i))).symm)
  -- Assemble the final witness site after transporting the intermediate replacement site.
  have hvff : J.Subcanonical → v.FullyFaithful := by
    intro hJsub
    haveI := hJsub
    haveI : (J.sheafifiedRepresentableFunctor).Full :=
      (sheafifiedRepresentableFunctor_fullyFaithful J hJsub).full
    haveI : (J.sheafifiedRepresentableFunctor).Faithful :=
      (sheafifiedRepresentableFunctor_fullyFaithful J hJsub).faithful
    have hv₀ : (ObjectProperty.sheafSubcategoryRepresentableFunctor P hP).FullyFaithful :=
      Functor.FullyFaithful.ofFullyFaithful _
    exact hv₀.comp e.fullyFaithfulFunctor
  exact ⟨C', inferInstance, J', hsubcanonical, hfinite, v, hdense, hvff, hcover, hsub, hfamily⟩

end CategoryTheory
