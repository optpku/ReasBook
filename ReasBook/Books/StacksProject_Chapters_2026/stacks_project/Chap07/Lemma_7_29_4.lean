module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.EffectiveEpi.Coproduct
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import stacks_project.Chap07.Definition_7_29_2
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Lemma_7_17_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

noncomputable section

universe w u v u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace ObjectProperty

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (P : ObjectProperty (Sheaf J (Type (max u v))))

/- Domain-style sampling for Lemma 7.29.4:
- primary domain: surjective-cover pretopologies on full subcategories of sheaf categories and the
  resulting dense-subsite comparison;
- sampled owner declarations:
  `Presieve.ofArrows`,
  `Sheaf.IsLocallySurjective`,
  `Sheaf.IsQuasiCompactObject.finite_subcoproduct`,
  `Functor.IsDenseSubsite`;
- best owner abstraction: the source-facing covering predicate should be built from a small family
  presentation `Presieve.ofArrows Y π` of the presieve together with the ambient owner
  `Sheaf.IsLocallySurjective` on the canonical coproduct map `Sigma.desc (fun i ↦ (π i).hom)`;
  the later comparison statements are then organized around the canonical dense-subsite owner
  `Functor.IsDenseSubsite`;
- primitive data: the full subcategory `P.FullSubcategory`, a small family of morphisms
  `π : ∀ i, Y i ⟶ X`, and its induced coproduct map in the ambient sheaf category;
- derived API: the induced pretopology/topology, the dense-subsite structure on
  `sheafSubcategoryRepresentableFunctor P hP`, and the inverse-image/direct-image identifications
  with representables.

Source/core/bridge triage:
- `source-facing`: the surjective covering condition on presieves and the six clauses of
  Lemma 7.29.4;
- `core/canonical`: `Presieve.ofArrows`, `Sheaf.IsLocallySurjective`,
  `Functor.IsDenseSubsite`, and `J.uliftSheafifiedRepresentableHomEquiv`;
- `bridge/view`: the small-family presentation of a presieve and the later comparison between
  inverse image of Yoneda and the underlying ambient sheaf.

The public coverage predicate should therefore expose only the locally surjective coproduct-map
condition for a family presenting the presieve, with coproduct existence supplied internally by
the ambient sheaf category rather than packaged as extra data.
-/

instance hasCoproductOfFullSubcategoryFamily
    {ι : Type (max u v)} (Y : ι → P.FullSubcategory) :
    HasCoproduct (fun i ↦ (Y i).obj) := by
  let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  infer_instance

/-- A presieve on the full subcategory is covering when it admits a small family presentation whose
associated coproduct map is locally surjective as a morphism of ambient sheaves. -/
def sheafSubcategorySurjectiveCovering
    {X : P.FullSubcategory} (R : Presieve X) : Prop :=
  ∃ (ι : Type (max u v)) (Y : ι → P.FullSubcategory) (π : ∀ i, Y i ⟶ X),
    R = Presieve.ofArrows Y π ∧
      Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i ↦ (π i).hom))

-- Proof sketch: the coproduct over a singleton family is canonically the source object, and the
-- induced sigma-desc map is therefore an isomorphism in the ambient sheaf category.
/-- Helper for Lemma 7.29.4: the sigma-desc map associated with a singleton isomorphism family is
locally surjective. -/
theorem sheafSubcategory_singleton_sigma_desc_isLocallySurjective
    {X Y : P.FullSubcategory} (f : Y ⟶ X) [IsIso f] :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun _ : PUnit ↦ f.hom)) := by
  -- Reduce local surjectivity to epimorphicity in the ambient sheaf category.
  rw [Sheaf.isLocallySurjective_iff_epi]
  let _ : IsIso f.hom := by
    simpa using (inferInstance : IsIso (P.ι.map f))
  refine CategoryTheory.Epi.mk ?_
  intro Z g h hgh
  have hι := congrArg (fun k ↦ Limits.Sigma.ι (fun _ : PUnit ↦ Y.obj) PUnit.unit ≫ k) hgh
  have hι' :
      (Limits.Sigma.ι (fun _ : PUnit ↦ Y.obj) PUnit.unit ≫
          Limits.Sigma.desc (fun _ : PUnit ↦ f.hom)) ≫ g =
        (Limits.Sigma.ι (fun _ : PUnit ↦ Y.obj) PUnit.unit ≫
            Limits.Sigma.desc (fun _ : PUnit ↦ f.hom)) ≫ h := by
    simpa [Category.assoc] using hι
  have hunit :
      Limits.Sigma.ι (fun _ : PUnit ↦ Y.obj) PUnit.unit ≫
        Limits.Sigma.desc (fun _ : PUnit ↦ f.hom) = f.hom := by
    simpa using Limits.Sigma.ι_desc (fun _ : PUnit ↦ f.hom) PUnit.unit
  exact (cancel_epi f.hom).1 <| by
    calc
      f.hom ≫ g =
          (Limits.Sigma.ι (fun _ : PUnit ↦ Y.obj) PUnit.unit ≫
            Limits.Sigma.desc (fun _ : PUnit ↦ f.hom)) ≫ g := by rw [hunit]
      _ = (Limits.Sigma.ι (fun _ : PUnit ↦ Y.obj) PUnit.unit ≫
            Limits.Sigma.desc (fun _ : PUnit ↦ f.hom)) ≫ h := hι'
      _ = f.hom ≫ h := by rw [hunit]

-- Proof sketch: present the singleton presieve by its one-arrow family; the associated coproduct
-- map is an isomorphism in the ambient sheaf category, hence locally surjective.
/-- Singleton isomorphism families are covering for the surjective coverage on the full subcategory
of sheaves. -/
theorem sheafSubcategorySurjectiveCovering_hasIsos
    {X Y : P.FullSubcategory} (f : Y ⟶ X) [IsIso f] :
    sheafSubcategorySurjectiveCovering P (Presieve.singleton f) := by
  -- Present the singleton presieve by the `PUnit`-indexed family consisting only of `f`.
  refine ⟨PUnit, fun _ ↦ Y, fun _ ↦ f, ?_, ?_⟩
  · simpa using (Presieve.ofArrows_pUnit f).symm
  · -- The associated sigma-desc map is locally surjective by the singleton helper above.
    exact sheafSubcategory_singleton_sigma_desc_isLocallySurjective (P := P) f

-- Proof sketch: choose a family presentation of `R`, pull back the ambient locally surjective
-- coproduct map along the chosen morphism in the full subcategory, and identify the resulting
-- family with a presentation of the pullback presieve.
/-- Helper for Lemma 7.29.4: transporting the ambient pullback sigma-desc along the pullback
comparison isomorphisms gives the sigma-desc on full-subcategory pullbacks. -/
theorem sheafSubcategory_pullback_sigma_desc_isLocallySurjective
    [P.IsClosedUnderLimitsOfShape WalkingCospan]
    {X Y : P.FullSubcategory} (f : Y ⟶ X)
    {ι : Type (max u v)} (Z : ι → P.FullSubcategory) (pi : ∀ i, Z i ⟶ X)
    (hpi : Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i ↦ (pi i).hom))) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i ↦ (pullback.snd (pi i) f).hom)) := by
  let _ : HasCoproduct (fun i ↦ (pullback (pi i) f).obj) :=
    hasCoproductOfFullSubcategoryFamily (P := P) (fun i ↦ pullback (pi i) f)
  let _ : HasCoproduct (fun i ↦ P.ι.obj (pullback (pi i) f)) :=
    hasCoproductOfFullSubcategoryFamily (P := P) (fun i ↦ pullback (pi i) f)
  let _ : HasCoproduct (fun i ↦ pullback (pi i).hom f.hom) := by
    let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    infer_instance
  let _ : HasCoproduct (fun i ↦ pullback (P.ι.map (pi i)) (P.ι.map f)) := by
    let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    infer_instance
  let comparison :
      (∐ fun i ↦ (pullback (pi i) f).obj) ⟶
        ∐ fun i ↦ pullback (pi i).hom f.hom :=
    Limits.Sigma.map (fun i ↦ (PreservesPullback.iso P.ι (pi i) f).hom)
  -- First pull back the ambient locally surjective coproduct map along `f.hom`.
  have hpull :
      Sheaf.IsLocallySurjective
        (Limits.Sigma.desc (fun i ↦ pullback.snd (pi i).hom f.hom)) := by
    simpa using
      CategoryTheory.Sheaf.isLocallySurjective_sigma_desc_pullback_snd
        (J := J) (q := f.hom) (fun i ↦ (Z i).obj) (fun i ↦ (pi i).hom) hpi
  have hfac :
      comparison ≫ Limits.Sigma.desc (fun i ↦ pullback.snd (pi i).hom f.hom) =
        Limits.Sigma.desc (fun i ↦ (pullback.snd (pi i) f).hom) := by
    -- Then identify the full-subcategory pullback projections with the ambient ones through the
    -- pullback comparison isomorphisms.
    apply Limits.Sigma.hom_ext
    intro i
    simp only [comparison, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc]
    simpa using
      (PreservesPullback.iso_hom_snd (G := P.ι) (f := pi i) (g := f))
  have hcomp :
      Sheaf.IsLocallySurjective
        (comparison ≫ Limits.Sigma.desc (fun i ↦ pullback.snd (pi i).hom f.hom)) := by
    have hcomparison : Sheaf.IsLocallySurjective comparison := by
      rw [Sheaf.isLocallySurjective_iff_epi]
      change Epi (Limits.Sigma.map (fun i ↦ (PreservesPullback.iso P.ι (pi i) f).hom))
      let _ : ∀ i, Epi ((PreservesPullback.iso P.ι (pi i) f).hom) := fun i ↦ by
        infer_instance
      exact Limits.Sigma.map_epi (fun i ↦ (PreservesPullback.iso P.ι (pi i) f).hom)
    let _ : Sheaf.IsLocallySurjective comparison := hcomparison
    let _ : Sheaf.IsLocallySurjective
        (Limits.Sigma.desc (fun i ↦ pullback.snd (pi i).hom f.hom)) := hpull
    infer_instance
  exact hfac.symm ▸ hcomp

/-- Surjective covering families in the full subcategory of sheaves are stable under pullback. -/
theorem sheafSubcategorySurjectiveCovering_pullbacks
    [P.IsClosedUnderLimitsOfShape WalkingCospan]
    {X Y : P.FullSubcategory} (f : Y ⟶ X) (R : Presieve X)
    (hR : sheafSubcategorySurjectiveCovering P R) :
    sheafSubcategorySurjectiveCovering P (Presieve.pullbackArrows f R) := by
  rcases hR with ⟨ι, Z, pi, rfl, hpi⟩
  -- Present the pulled-back cover by the pulled-back family of arrows.
  refine ⟨ι, fun i ↦ pullback (pi i) f, fun i ↦ pullback.snd (pi i) f, ?_, ?_⟩
  · simpa using (Presieve.ofArrows_pullback f Z pi).symm
  · -- The ambient sigma-desc stays locally surjective after base change along `f`.
    exact sheafSubcategory_pullback_sigma_desc_isLocallySurjective (P := P) f Z pi hpi

-- Proof sketch: choose a family presentation of `R`, compose its ambient locally surjective
-- coproduct map with the ambient locally surjective coproduct maps for the chosen presentations of
-- the refining presieves, and identify the composite with a family presentation of `R.bind Ti`.
/-- Helper for Lemma 7.29.4: assembling a family of locally surjective maps into a coproduct map
to the coproduct of the targets preserves local surjectivity. -/
theorem sheaf_sigma_desc_of_componentwise_isLocallySurjective
    {ι : Type (max u v)} (Y F : ι → Sheaf J (Type (max u v)))
    [HasCoproduct Y] [HasCoproduct F]
    (gamma : ∀ i, Y i ⟶ F i)
    (hgamma : ∀ i, Sheaf.IsLocallySurjective (gamma i)) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i ↦ gamma i ≫ Limits.Sigma.ι F i)) := by
  -- Reduce local surjectivity to epimorphicity of the induced coproduct map.
  rw [Sheaf.isLocallySurjective_iff_epi]
  change Epi (Limits.Sigma.map gamma)
  let _ : ∀ i, Epi (gamma i) := fun i ↦
    (Sheaf.isLocallySurjective_iff_epi (φ := gamma i)).1 (hgamma i)
  exact Limits.Sigma.map_epi gamma

/-- Surjective covering families in the full subcategory of sheaves are closed under refinement by
surjective coverings on each domain. -/
theorem sheafSubcategorySurjectiveCovering_transitive
    {X : P.FullSubcategory} (R : Presieve X)
    (Ti : ∀ ⦃Y : P.FullSubcategory⦄ (f : Y ⟶ X), R f → Presieve Y)
    (hR : sheafSubcategorySurjectiveCovering P R)
    (hTi : ∀ ⦃Y : P.FullSubcategory⦄ (f : Y ⟶ X) (hf : R f),
      sheafSubcategorySurjectiveCovering P (Ti f hf)) :
    sheafSubcategorySurjectiveCovering P (R.bind Ti) := by
  classical
  rcases hR with ⟨ι, Yfam, pi, rfl, hpi⟩
  have hTi' :
      ∀ i : ι, sheafSubcategorySurjectiveCovering P (Ti (pi i) (Presieve.ofArrows.mk i)) :=
    fun i ↦ hTi (pi i) (Presieve.ofArrows.mk i)
  choose κ W rho hTi_eq hrho using hTi'
  let _ : ∀ i, HasCoproduct (fun j : κ i ↦ (W i j).obj) :=
    fun i ↦ hasCoproductOfFullSubcategoryFamily (P := P) (W i)
  let _ : HasCoproduct (fun i ↦ (Yfam i).obj) :=
    hasCoproductOfFullSubcategoryFamily (P := P) Yfam
  let _ : HasCoproduct (fun i ↦ ∐ fun j : κ i ↦ (W i j).obj) := by
    let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    infer_instance
  let _ : HasCoproduct (fun p : Σ i, κ i ↦ (W p.1 p.2).obj) := by
    let _ : HasColimitsOfShape (Discrete (Σ i, κ i)) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete (Σ i, κ i)) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    infer_instance
  let nestedDesc :
      (∐ fun i ↦ ∐ fun j : κ i ↦ (W i j).obj) ⟶
        ∐ fun i ↦ (Yfam i).obj :=
    Limits.Sigma.desc
      (fun i ↦ Limits.Sigma.desc (fun j : κ i ↦ (rho i j).hom) ≫
        Limits.Sigma.ι (fun i ↦ (Yfam i).obj) i)
  let outerDesc : (∐ fun i ↦ (Yfam i).obj) ⟶ X.obj :=
    Limits.Sigma.desc (fun i ↦ (pi i).hom)
  let flatDesc :
      (∐ fun p : Σ i, κ i ↦ (W p.1 p.2).obj) ⟶ X.obj :=
    Limits.Sigma.desc (fun p : Σ i, κ i ↦ (rho p.1 p.2 ≫ pi p.1).hom)
  let flattenIso :
      (∐ fun i ↦ ∐ fun j : κ i ↦ (W i j).obj) ≅
        ∐ fun p : Σ i, κ i ↦ (W p.1 p.2).obj :=
    Limits.sigmaSigmaIso (fun i ↦ κ i) (fun i j ↦ (W i j).obj)
  refine ⟨Σ i, κ i, fun p ↦ W p.1 p.2, fun p ↦ rho p.1 p.2 ≫ pi p.1, ?_, ?_⟩
  · -- Rewrite the bound presieve as the presieve generated by the flattened family.
    funext Y'
    funext f
    apply propext
    constructor
    · rintro ⟨Y'', g, f', hf, hg, rfl⟩
      rcases hf with ⟨i⟩
      rw [hTi_eq i] at hg
      rcases hg with ⟨j⟩
      exact
        (Presieve.ofArrows.mk
          (Y := fun p : Σ i, κ i ↦ W p.1 p.2)
          (f := fun p ↦ rho p.1 p.2 ≫ pi p.1) ⟨i, j⟩)
    · rintro ⟨⟨i, j⟩⟩
      refine ⟨Yfam i, rho i j, pi i, Presieve.ofArrows.mk i, ?_, by simp⟩
      rw [hTi_eq i]
      exact Presieve.ofArrows.mk j
  · -- Assemble the inner locally surjective maps, then compose with the original cover map and
    -- reindex the source along the sigma-sigma coproduct isomorphism.
    have hnested :
        Sheaf.IsLocallySurjective nestedDesc := by
      exact
        sheaf_sigma_desc_of_componentwise_isLocallySurjective
          (J := J) (fun i ↦ ∐ fun j : κ i ↦ (W i j).obj) (fun i ↦ (Yfam i).obj)
          (fun i ↦ Limits.Sigma.desc (fun j : κ i ↦ (rho i j).hom)) hrho
    have hnested_comp :
        Sheaf.IsLocallySurjective (nestedDesc ≫ outerDesc) := by
      let _ : Sheaf.IsLocallySurjective nestedDesc := hnested
      let _ : Sheaf.IsLocallySurjective outerDesc := hpi
      infer_instance
    have hflat :
        flattenIso.inv ≫ (nestedDesc ≫ outerDesc) = flatDesc := by
      apply Limits.Sigma.hom_ext
      intro p
      cases p with
      | mk i j =>
          calc
            Limits.Sigma.ι (fun p : Σ i, κ i ↦ (W p.1 p.2).obj) ⟨i, j⟩ ≫
                flattenIso.inv ≫ (nestedDesc ≫ outerDesc) =
              Limits.Sigma.ι (fun j : κ i ↦ (W i j).obj) j ≫
                Limits.Sigma.ι (fun i ↦ ∐ fun j : κ i ↦ (W i j).obj) i ≫
                  nestedDesc ≫ outerDesc := by
                    dsimp [flattenIso]
                    simpa [Category.assoc] using
                      (Limits.Sigma.ι_desc_assoc
                        (p := fun x : Σ i, κ i ↦
                          Limits.Sigma.ι (fun j ↦ (W x.1 j).obj) x.2 ≫
                            Limits.Sigma.ι (fun i ↦ ∐ fun j : κ i ↦ (W i j).obj) x.1)
                        (b := ⟨i, j⟩) (h := nestedDesc ≫ outerDesc))
            _ = (rho i j).hom ≫ (pi i).hom := by
              calc
                Limits.Sigma.ι (fun j : κ i ↦ (W i j).obj) j ≫
                    Limits.Sigma.ι (fun i ↦ ∐ fun j : κ i ↦ (W i j).obj) i ≫
                      nestedDesc ≫ outerDesc =
                  Limits.Sigma.ι (fun j : κ i ↦ (W i j).obj) j ≫
                    (Limits.Sigma.desc (fun j : κ i ↦ (rho i j).hom) ≫
                      Limits.Sigma.ι (fun i ↦ (Yfam i).obj) i) ≫ outerDesc := by
                    simpa [nestedDesc, Category.assoc] using
                      congrArg
                        (fun k ↦
                          Limits.Sigma.ι (fun j : κ i ↦ (W i j).obj) j ≫ k)
                        (Limits.Sigma.ι_desc_assoc
                          (p := fun i ↦
                            Limits.Sigma.desc (fun j : κ i ↦ (rho i j).hom) ≫
                              Limits.Sigma.ι (fun i ↦ (Yfam i).obj) i)
                          (b := i) (h := outerDesc))
                _ = (rho i j).hom ≫ Limits.Sigma.ι (fun i ↦ (Yfam i).obj) i ≫ outerDesc := by
                    simpa [Category.assoc] using
                      (Limits.Sigma.ι_desc_assoc
                        (p := fun j : κ i ↦ (rho i j).hom)
                        (b := j)
                        (h := Limits.Sigma.ι (fun i ↦ (Yfam i).obj) i ≫ outerDesc))
                _ = (rho i j).hom ≫ (pi i).hom := by
                  simpa [outerDesc, Category.assoc] using
                    congrArg (fun k ↦ (rho i j).hom ≫ k)
                      (Limits.Sigma.ι_desc
                        (p := fun i ↦ (pi i).hom)
                        (b := i))
            _ =
                Limits.Sigma.ι (fun p : Σ i, κ i ↦ (W p.1 p.2).obj) ⟨i, j⟩ ≫
                  flatDesc := by
                    symm
                    simpa [flatDesc, Category.assoc] using
                      (Limits.Sigma.ι_desc_assoc
                        (p := fun p : Σ i, κ i ↦ (rho p.1 p.2 ≫ pi p.1).hom)
                        (b := ⟨i, j⟩) (h := 𝟙 X.obj))
    have hflat_surj : Sheaf.IsLocallySurjective (flattenIso.inv ≫ (nestedDesc ≫ outerDesc)) := by
      let _ : Sheaf.IsLocallySurjective flattenIso.inv := by infer_instance
      let _ : Sheaf.IsLocallySurjective (nestedDesc ≫ outerDesc) := hnested_comp
      infer_instance
    have hflat' : flattenIso.inv ≫ nestedDesc ≫ outerDesc = flatDesc := by
      simpa [Category.assoc] using hflat
    simpa [Category.assoc, hflat'] using hflat_surj

/-- The pretopology on a full subcategory of `Sh(J)` whose covering families are those admitting a
small family presentation with locally surjective ambient coproduct map. -/
def sheafSubcategorySurjectivePretopology
    [P.IsClosedUnderLimitsOfShape WalkingCospan] : Pretopology P.FullSubcategory where
  coverings _ R := sheafSubcategorySurjectiveCovering P R
  has_isos := fun {_ _} f _ ↦ sheafSubcategorySurjectiveCovering_hasIsos P f
  pullbacks := fun {_ _} f R hR ↦ sheafSubcategorySurjectiveCovering_pullbacks P f R hR
  transitive := fun {_} R Ti hR hTi ↦
    sheafSubcategorySurjectiveCovering_transitive P R Ti hR hTi

/-- The canonical functor `U ↦ h_U^#` lifted from `C` to the chosen full subcategory of sheaves.
-/
noncomputable abbrev sheafSubcategoryRepresentableFunctor
    [HasWeakSheafify J (Type (max u v))]
    (hP : ∀ U : C, P (h[U]^#[J])) :
    C ⥤ P.FullSubcategory :=
  P.lift J.sheafifiedRepresentableFunctor hP

/-- Lemma 7.29.4 (1): the surjective covering families on the full subcategory of sheaves define
the Grothendieck topology on `\mathcal C'`, so `\mathcal C'` becomes a site. -/
abbrev sheafSubcategorySurjectiveTopology
    [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    GrothendieckTopology P.FullSubcategory :=
  (sheafSubcategorySurjectivePretopology P).toGrothendieck

-- Proof sketch: this is the defining equality of the topology abbreviation obtained from the
-- pretopology of locally surjective family presentations.
/-- The surjective topology on the full subcategory is by definition the Grothendieck topology
generated by the surjective pretopology. -/
theorem sheafSubcategorySurjectiveTopology_def
    [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    sheafSubcategorySurjectiveTopology P =
      (sheafSubcategorySurjectivePretopology P).toGrothendieck := by
  -- This is the defining equation of the abbreviation.
  rfl

-- Proof sketch: pull back the identity coproduct decomposition of `∐ Xᵢ` along `g`; after
-- swapping the pullback factors componentwise, the resulting sigma-desc is the ambient cover map
-- of the pullback family, which is locally surjective by the existing pullback lemma.
/-- Helper for Lemma 7.29.4: pulling back the coproduct injections along an ambient morphism gives
a locally surjective coproduct map onto the source of that morphism. -/
theorem sheaf_sigma_desc_pullback_fst_isLocallySurjective
    {ι : Type (max u v)} (X : ι → Sheaf J (Type (max u v)))
    [HasCoproduct X] {Z : Sheaf J (Type (max u v))} (g : Z ⟶ ∐ X)
    [∀ i, HasPullback g (Limits.Sigma.ι X i)]
    [∀ i, HasPullback (Limits.Sigma.ι X i) g]
    [HasCoproduct (fun i ↦ pullback g (Limits.Sigma.ι X i))]
    [HasCoproduct (fun i ↦ pullback (Limits.Sigma.ι X i) g)] :
    Sheaf.IsLocallySurjective
      (Limits.Sigma.desc (fun i ↦ pullback.fst g (Limits.Sigma.ι X i))) := by
  have hid :
      Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i ↦ Limits.Sigma.ι X i)) := by
    have hdesc : Limits.Sigma.desc (fun i ↦ Limits.Sigma.ι X i) = 𝟙 (∐ X) := by
      apply Limits.Sigma.hom_ext
      intro i
      simpa using
        (Limits.Sigma.ι_desc (p := fun i ↦ Limits.Sigma.ι X i) (b := i))
    simpa [hdesc] using (show Sheaf.IsLocallySurjective (𝟙 (∐ X)) by infer_instance)
  have hsnd :
      Sheaf.IsLocallySurjective
        (Limits.Sigma.desc (fun i ↦ pullback.snd (Limits.Sigma.ι X i) g)) := by
    exact
      CategoryTheory.Sheaf.isLocallySurjective_sigma_desc_pullback_snd
        (J := J) (q := g) X (fun i ↦ Limits.Sigma.ι X i) hid
  let comparison :
      (∐ fun i ↦ pullback g (Limits.Sigma.ι X i)) ⟶
        ∐ fun i ↦ pullback (Limits.Sigma.ι X i) g :=
    Limits.Sigma.map (fun i ↦ (pullbackSymmetry g (Limits.Sigma.ι X i)).hom)
  have hcomparison :
      Sheaf.IsLocallySurjective comparison := by
    rw [Sheaf.isLocallySurjective_iff_epi]
    change Epi (Limits.Sigma.map (fun i ↦ (pullbackSymmetry g (Limits.Sigma.ι X i)).hom))
    let _ : ∀ i, Epi ((pullbackSymmetry g (Limits.Sigma.ι X i)).hom) := fun i ↦ by
      infer_instance
    exact Limits.Sigma.map_epi (fun i ↦ (pullbackSymmetry g (Limits.Sigma.ι X i)).hom)
  have hfac :
      comparison ≫ Limits.Sigma.desc (fun i ↦ pullback.snd (Limits.Sigma.ι X i) g) =
        Limits.Sigma.desc (fun i ↦ pullback.fst g (Limits.Sigma.ι X i)) := by
    apply Limits.Sigma.hom_ext
    intro i
    simp only [comparison, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc]
    simpa using pullbackSymmetry_hom_comp_snd (f := g) (g := Limits.Sigma.ι X i)
  have hcomp :
      Sheaf.IsLocallySurjective
        (comparison ≫ Limits.Sigma.desc (fun i ↦ pullback.snd (Limits.Sigma.ι X i) g)) := by
    let _ : Sheaf.IsLocallySurjective comparison := hcomparison
    let _ :
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc (fun i ↦ pullback.snd (Limits.Sigma.ι X i) g)) := hsnd
    infer_instance
  exact hfac.symm ▸ hcomp

-- Proof sketch: local surjectivity of the ambient coproduct map makes the underlying family an
-- effective epi family in the sheaf topos once the pullback-of-coproduct cover map above is used
-- to discharge the coproduct/pullback interaction required by `effectiveEpiFamilyStructOf...`.
/-- Helper for Lemma 7.29.4: a locally surjective ambient coproduct presentation defines an
ambient effective-epimorphic family. -/
theorem sheafSubcategory_effectiveEpiFamily_of_surjective_presentation
    {X : P.FullSubcategory} {ι : Type (max u v)} (Y : ι → P.FullSubcategory)
    (π : ∀ i, Y i ⟶ X)
    (hπ : Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i ↦ (π i).hom))) :
    EffectiveEpiFamily (fun i ↦ (Y i).obj) (fun i ↦ (π i).hom) := by
  let _ : HasCoproduct (fun i ↦ (Y i).obj) :=
    hasCoproductOfFullSubcategoryFamily (P := P) Y
  let _ : Epi (Limits.Sigma.desc (fun i ↦ (π i).hom)) :=
    (Sheaf.isLocallySurjective_iff_epi _).1 hπ
  let _ : EffectiveEpi (Limits.Sigma.desc (fun i ↦ (π i).hom)) :=
    (regularEpiOfEpi _).effectiveEpi
  let _ :
      ∀ {Z : Sheaf J (Type (max u v))}
        (g : Z ⟶ ∐ fun i ↦ (Y i).obj),
        (∀ i, HasPullback g (Limits.Sigma.ι (fun i ↦ (Y i).obj) i)) := by
    intro Z g i
    let _ : HasLimitsOfShape WalkingCospan (Type (max u v)) := inferInstance
    let _ : HasLimitsOfShape WalkingCospan (Sheaf J (Type (max u v))) :=
      Sheaf.instHasLimitsOfShape
    infer_instance
  let _ :
      ∀ {Z : Sheaf J (Type (max u v))}
        (g : Z ⟶ ∐ fun i ↦ (Y i).obj),
        (∀ i, HasPullback (Limits.Sigma.ι (fun i ↦ (Y i).obj) i) g) := by
    intro Z g i
    let _ : ∀ i, HasPullback g (Limits.Sigma.ι (fun i ↦ (Y i).obj) i) := by
      intro i
      let _ : HasLimitsOfShape WalkingCospan (Type (max u v)) := inferInstance
      let _ : HasLimitsOfShape WalkingCospan (Sheaf J (Type (max u v))) :=
        Sheaf.instHasLimitsOfShape
      infer_instance
    exact
      CategoryTheory.Limits.hasPullback_symmetry
        (f := g) (g := Limits.Sigma.ι (fun i ↦ (Y i).obj) i)
  let _ :
      ∀ {Z : Sheaf J (Type (max u v))}
        (g : Z ⟶ ∐ fun i ↦ (Y i).obj),
        HasCoproduct (fun i ↦ pullback g (Limits.Sigma.ι (fun i ↦ (Y i).obj) i)) := by
    intro Z g
    let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    infer_instance
  let _ :
      ∀ {Z : Sheaf J (Type (max u v))}
        (g : Z ⟶ ∐ fun i ↦ (Y i).obj),
        HasCoproduct
          (fun i ↦ pullback (Limits.Sigma.ι (fun i ↦ (Y i).obj) i) g) := by
    intro Z g
    let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    infer_instance
  let _ :
      ∀ {Z : Sheaf J (Type (max u v))}
        (g : Z ⟶ ∐ fun i ↦ (Y i).obj),
        Epi
          (Limits.Sigma.desc
            (fun i ↦ pullback.fst g (Limits.Sigma.ι (fun i ↦ (Y i).obj) i))) := by
    intro Z g
    rw [← Sheaf.isLocallySurjective_iff_epi]
    exact sheaf_sigma_desc_pullback_fst_isLocallySurjective (J := J) (fun i ↦ (Y i).obj) g
  let h :=
    effectiveEpiFamilyStructOfEffectiveEpiDesc
      (fun i ↦ (Y i).obj) (fun i ↦ (π i).hom)
  exact ⟨⟨h⟩⟩

-- Proof sketch: use the explicit compatible-family criterion for `Presieve.ofArrows`; injectivity
-- follows from the ambient effective-epi family, and surjectivity descends a compatible ambient
-- family through the same effective-epi family after factoring arbitrary equal pairs through the
-- full-subcategory pullbacks.
/-- Helper for Lemma 7.29.4: a representable presheaf on the full subcategory satisfies descent
for any family whose ambient coproduct map is locally surjective. -/
theorem sheafSubcategory_representable_isSheafFor_of_surjective_presentation
    [P.IsClosedUnderLimitsOfShape WalkingCospan]
    {X ℱ : P.FullSubcategory} {ι : Type (max u v)} (Y : ι → P.FullSubcategory)
    (π : ∀ i, Y i ⟶ X)
    (hπ : Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i ↦ (π i).hom))) :
    Presieve.IsSheafFor (CategoryTheory.yoneda.obj ℱ) (Presieve.ofArrows Y π) := by
  let _ :
      EffectiveEpiFamily (fun i ↦ (Y i).obj) (fun i ↦ (π i).hom) :=
    sheafSubcategory_effectiveEpiFamily_of_surjective_presentation
      (P := P) Y π hπ
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]
  constructor
  · intro α β hαβ
    apply ObjectProperty.hom_ext P
    apply EffectiveEpiFamily.hom_ext (fun i ↦ (Y i).obj) (fun i ↦ (π i).hom)
    intro i
    have hi : π i ≫ α = π i ≫ β := by
      exact congrFun (congrArg Subtype.val hαβ) i
    simpa using congrArg (fun f => f.hom) hi
  · rintro x
    -- Build the descended ambient map from the compatible family, then lift it back to the full
    -- subcategory hom-set.
    have hxCompatAmbient :
        ∀ {Z : Sheaf J (Type (max u v))} (i₁ i₂ : ι)
          (g₁ : Z ⟶ (Y i₁).obj) (g₂ : Z ⟶ (Y i₂).obj),
          g₁ ≫ (π i₁).hom = g₂ ≫ (π i₂).hom →
            g₁ ≫ (x.1 i₁).hom = g₂ ≫ (x.1 i₂).hom := by
      intro Z i₁ i₂ g₁ g₂ hg
      let l' :
          Z ⟶ pullback (π i₁).hom (π i₂).hom :=
        pullback.lift g₁ g₂ <| by simpa using hg
      let l :
          Z ⟶
            (pullback (π i₁) (π i₂)).obj :=
        l' ≫ (PreservesPullback.iso P.ι (π i₁) (π i₂)).inv
      have hcompat_full :
          pullback.fst (π i₁) (π i₂) ≫ x.1 i₁ =
            pullback.snd (π i₁) (π i₂) ≫ x.1 i₂ := by
        simpa using
          x.2 i₁ i₂ (pullback (π i₁) (π i₂))
            (pullback.fst (π i₁) (π i₂)) (pullback.snd (π i₁) (π i₂)) <| by
              simpa using pullback.condition (f := π i₁) (g := π i₂)
      have hcompat :
          (pullback.fst (π i₁) (π i₂)).hom ≫ (x.1 i₁).hom =
            (pullback.snd (π i₁) (π i₂)).hom ≫ (x.1 i₂).hom := by
        simpa [Category.assoc] using congrArg (fun f => f.hom) hcompat_full
      have hlfst :
          l ≫ (pullback.fst (π i₁) (π i₂)).hom = g₁ := by
        calc
          l ≫ (pullback.fst (π i₁) (π i₂)).hom =
              l' ≫ pullback.fst (π i₁).hom (π i₂).hom := by
                simpa [l, l', Category.assoc] using
                  congrArg (fun k => l' ≫ k)
                    (PreservesPullback.iso_inv_fst (G := P.ι) (f := π i₁) (g := π i₂))
          _ = g₁ := by
            simpa [l'] using
              (pullback.lift_fst (f := (π i₁).hom) (g := (π i₂).hom) g₁ g₂ hg)
      have hlsnd :
          l ≫ (pullback.snd (π i₁) (π i₂)).hom = g₂ := by
        calc
          l ≫ (pullback.snd (π i₁) (π i₂)).hom =
              l' ≫ pullback.snd (π i₁).hom (π i₂).hom := by
                simpa [l, l', Category.assoc] using
                  congrArg (fun k => l' ≫ k)
                    (PreservesPullback.iso_inv_snd (G := P.ι) (f := π i₁) (g := π i₂))
          _ = g₂ := by
            simpa [l'] using
              (pullback.lift_snd (f := (π i₁).hom) (g := (π i₂).hom) g₁ g₂ hg)
      calc
        g₁ ≫ (x.1 i₁).hom = l ≫ (pullback.fst (π i₁) (π i₂)).hom ≫ (x.1 i₁).hom := by
          simpa [Category.assoc] using
            congrArg (fun k => k ≫ (x.1 i₁).hom) hlfst.symm
        _ = l ≫ (pullback.snd (π i₁) (π i₂)).hom ≫ (x.1 i₂).hom := by rw [hcompat]
        _ = g₂ ≫ (x.1 i₂).hom := by
          simpa [Category.assoc] using
            congrArg (fun k => k ≫ (x.1 i₂).hom) hlsnd
    refine ⟨⟨EffectiveEpiFamily.desc (fun i ↦ (Y i).obj) (fun i ↦ (π i).hom)
      (fun i ↦ (x.1 i).hom) hxCompatAmbient⟩, ?_⟩
    · apply Subtype.ext
      ext i
      apply ObjectProperty.hom_ext P
      exact
        EffectiveEpiFamily.fac (fun i ↦ (Y i).obj) (fun i ↦ (π i).hom)
          (fun i ↦ (x.1 i).hom) hxCompatAmbient i

/-- Lemma 7.29.4 (2): the surjective topology on the full subcategory of sheaves is subcanonical,
so representable presheaves on `\mathcal C'` are sheaves. -/
-- Proof sketch: a morphism into an ambient sheaf is determined by its restrictions along a
-- locally surjective family, and the equalizer condition is exactly Lemma 7.11.3 applied in the
-- ambient sheaf category.
instance sheafSubcategorySurjectiveTopology_subcanonical
    [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    (sheafSubcategorySurjectiveTopology P).Subcanonical := by
  refine GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ ?_
  intro ℱ
  -- Route correction: instead of forcing a coproduct argument inside the full subcategory, reduce
  -- the pretopology sheaf condition to the explicit compatible-family criterion for `ofArrows`
  -- and descend through the ambient effective-epi family.
  rw [sheafSubcategorySurjectiveTopology_def, Presieve.isSheaf_pretopology]
  intro X R hR
  rcases hR with ⟨ι, Z, π, rfl, hπ⟩
  exact
    sheafSubcategory_representable_isSheafFor_of_surjective_presentation
      (P := P) (ℱ := ℱ) Z π hπ

section

variable [HasWeakSheafify J (Type (max u v))]
variable [P.IsClosedUnderLimitsOfShape WalkingCospan]
variable (hP : ∀ U : C, P (h[U]^#[J]))

/-- Helper for Lemma 7.29.4: evaluating a morphism from a sheafified representable on the
canonical identity section recovers the corresponding section. -/
theorem sheafifiedRepresentable_component_eq_section
    {ℱ : Sheaf J (Type (max u v))} {U : C} (α : h[U]^#[J] ⟶ ℱ) :
    α.hom.app (op U)
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) =
      J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by
  -- This is the component form of the naturality of the sheafification adjunction hom-equivalence.
  simpa using (J.uliftSheafifiedRepresentableHomEquiv_comp (𝟙 (h[U]^#[J])) α).symm

/-- Helper for Lemma 7.29.4: the universal family of all morphisms from sheafified representables
into a fixed object of the full subcategory is a surjective covering family. -/
theorem sheafSubcategoryRepresentableFunctor_universalFamily_covering
    (ℱ : P.FullSubcategory) :
    sheafSubcategorySurjectiveCovering P
      (Presieve.ofArrows
        (fun I : Σ U : C, (sheafSubcategoryRepresentableFunctor P hP).obj U ⟶ ℱ ↦
          (sheafSubcategoryRepresentableFunctor P hP).obj I.1)
        (fun I ↦ I.2)) := by
  let v := sheafSubcategoryRepresentableFunctor P hP
  let ι : Type (max u v) := Σ U : C, v.obj U ⟶ ℱ
  refine ⟨ι, fun I ↦ v.obj I.1, fun I ↦ I.2, rfl, ?_⟩
  let σ : (∐ fun I : ι ↦ (v.obj I.1).obj) ⟶ ℱ.obj :=
    Limits.Sigma.desc (fun I : ι ↦ I.2.hom)
  -- Every section of `ℱ` comes from the universal family by choosing the corresponding
  -- sheafified-representable morphism as an index.
  refine ⟨fun {V} x ↦ ?_⟩
  let I : ι :=
    ⟨V, ObjectProperty.homMk ((J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj ℱ) V).symm x)⟩
  let t : ((∐ fun I : ι ↦ (v.obj I.1).obj).obj).obj (op V) :=
    J.uliftSheafifiedRepresentableHomEquiv (∐ fun I : ι ↦ (v.obj I.1).obj) V
      (Limits.Sigma.ι (fun I : ι ↦ (v.obj I.1).obj) I)
  have ht : σ.hom.app (op V) t = x := by
    -- Evaluate the chosen coproduct inclusion and then identify the selected component.
    have hcomp :
        σ.hom.app (op V) t =
          (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj ℱ) V)
            (Limits.Sigma.ι (fun I : ι ↦ (v.obj I.1).obj) I ≫ σ) := by
      symm
      simpa [t] using
        J.uliftSheafifiedRepresentableHomEquiv_comp
          (Limits.Sigma.ι (fun I : ι ↦ (v.obj I.1).obj) I) σ
    have hι :
        Limits.Sigma.ι (fun I : ι ↦ (v.obj I.1).obj) I ≫ σ = I.2.hom := by
      simpa [σ] using
        (Limits.Sigma.ι_desc
          (p := fun I : ι ↦ I.2.hom)
          (b := I))
    have hsection :
        (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj ℱ) V)
            (Limits.Sigma.ι (fun I : ι ↦ (v.obj I.1).obj) I ≫ σ) = x := by
      have hI :
          I.2.hom = (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj ℱ) V).symm x := by
        rfl
      calc
        (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj ℱ) V)
            (Limits.Sigma.ι (fun I : ι ↦ (v.obj I.1).obj) I ≫ σ) =
          (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj ℱ) V) (I.2.hom) := by
            exact congrArg (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj ℱ) V) hι
        _ = x := by simpa [hI] using
          (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj ℱ) V).apply_symm_apply x
    exact hcomp.trans hsection
  have htop : Presheaf.imageSieve σ.hom x = ⊤ := by
    -- Once the chosen section is literally in the image, its image sieve is the maximal sieve.
    calc
      Presheaf.imageSieve σ.hom x =
          Presheaf.imageSieve σ.hom (σ.hom.app (op V) t) := by rw [ht]
      _ = ⊤ := Presheaf.imageSieve_app σ.hom t
  rw [htop]
  exact J.top_mem V

/-- Helper for Lemma 7.29.4: a surjective covering family presents its generated sieve as a cover
for the associated Grothendieck topology. -/
theorem sheafSubcategorySurjectiveCovering_generate_mem
    {X : P.FullSubcategory} {R : Presieve X}
    (hR : sheafSubcategorySurjectiveCovering P R) :
    Sieve.generate R ∈ sheafSubcategorySurjectiveTopology P X := by
  -- Rewrite topology membership through the defining pretopology and use the chosen presentation.
  rw [sheafSubcategorySurjectiveTopology_def, Pretopology.mem_toGrothendieck]
  exact ⟨R, hR, Sieve.le_generate R⟩

/-- Helper for Lemma 7.29.4: the image-cover sieve on an object of the full subcategory is
covering for the surjective topology. -/
theorem sheafSubcategoryRepresentableFunctor_coverByImage_mem
    (ℱ : P.FullSubcategory) :
    Sieve.coverByImage (sheafSubcategoryRepresentableFunctor P hP) ℱ ∈
      sheafSubcategorySurjectiveTopology P ℱ := by
  let v := sheafSubcategoryRepresentableFunctor P hP
  let R : Presieve ℱ :=
    Presieve.ofArrows
      (fun I : Σ U : C, v.obj U ⟶ ℱ ↦ v.obj I.1)
      (fun I ↦ I.2)
  have hR : sheafSubcategorySurjectiveCovering P R :=
    sheafSubcategoryRepresentableFunctor_universalFamily_covering
      (P := P) (J := J) hP ℱ
  have hgen :
      Sieve.generate R ∈ sheafSubcategorySurjectiveTopology P ℱ :=
    sheafSubcategorySurjectiveCovering_generate_mem (P := P) hR
  have hRle : R ≤ (Sieve.coverByImage v ℱ : Presieve ℱ) := by
    -- Each generating arrow already factors through an image object by construction.
    intro Y f hf
    let I : Σ U : C, v.obj U ⟶ ℱ := Presieve.ofArrows.idx hf
    have hEq :
        f = eqToHom (Presieve.ofArrows.obj_idx hf).symm ≫ I.2 :=
      Presieve.ofArrows.eq_eqToHom_comp_hom_idx hf
    have hmem :
        (Sieve.coverByImage v ℱ)
          (eqToHom (Presieve.ofArrows.obj_idx hf).symm ≫ I.2) :=
      (Sieve.coverByImage v ℱ).downward_closed
        (Presieve.in_coverByImage v I.2)
        (eqToHom (Presieve.ofArrows.obj_idx hf).symm)
    simpa [hEq] using hmem
  have hgenle : Sieve.generate R ≤ Sieve.coverByImage v ℱ :=
    (Sieve.giGenerate.gc R (Sieve.coverByImage v ℱ)).2 hRle
  -- Enlarge the generated covering sieve to the image-cover sieve.
  exact (sheafSubcategorySurjectiveTopology P).superset_covering hgenle hgen

/-- Helper for Lemma 7.29.4: every `J`-cover on the source site pushes forward to a covering
sieve for the surjective topology on the full subcategory. -/
theorem sheafSubcategoryRepresentableFunctor_ofArrows_covering
    {U : C} (T : J.Cover U) :
    sheafSubcategorySurjectiveCovering P
      (Presieve.ofArrows
        (fun I : T.Arrow ↦ (sheafSubcategoryRepresentableFunctor P hP).obj I.Y)
        (fun I ↦ (sheafSubcategoryRepresentableFunctor P hP).map I.f)) := by
  let v := sheafSubcategoryRepresentableFunctor P hP
  refine ⟨T.Arrow, fun I ↦ v.obj I.Y, fun I ↦ v.map I.f, rfl, ?_⟩
  -- The canonical sheafified-representable cover map is locally surjective.
  simpa [v, sheafSubcategoryRepresentableFunctor,
    GrothendieckTopology.sheafifiedRepresentableMap] using
    (J.sheafifiedRepresentableCoverMap_isLocallySurjective (S := T))

/-- Helper for Lemma 7.29.4: the section corresponding to a source arrow `f : U' ⟶ U` is exactly
the value of `toSheafify` on the Yoneda section `f`. -/
theorem sheafSubcategoryRepresentableFunctor_section_eq_toSheafify_app
    {U' U : C} (f : U' ⟶ U) :
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
      ((sheafSubcategoryRepresentableFunctor P hP).map f).hom =
      ((sheafificationAdjunction J (Type (max u v))).unit.app
        (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U') (ULift.up f) := by
  have hId :
      J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J])) =
        ((sheafificationAdjunction J (Type (max u v))).unit.app
          (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U) (ULift.up (𝟙 U)) := by
    -- At the identity morphism, the hom-equivalence is definitionally the unit section.
    rfl
  calc
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
        ((sheafSubcategoryRepresentableFunctor P hP).map f).hom =
      (h[U]^#[J]).obj.map f.op
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) := by
          simpa [sheafSubcategoryRepresentableFunctor] using
            GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_naturality
              (J := J) f (h[U]^#[J]) (𝟙 (h[U]^#[J]))
    _ = (h[U]^#[J]).obj.map f.op
        (((sheafificationAdjunction J (Type (max u v))).unit.app
          (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U) (ULift.up (𝟙 U))) := by
            rw [hId]
    _ = ((sheafificationAdjunction J (Type (max u v))).unit.app
        (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U') (ULift.up f) := by
          let η :
              CategoryTheory.uliftYoneda.{max u v}.obj U ⟶ (h[U]^#[J]).obj :=
            (sheafificationAdjunction J (Type (max u v))).unit.app
              (CategoryTheory.uliftYoneda.{max u v}.obj U)
          have hnat := congrFun (NatTrans.naturality η f.op) (ULift.up (𝟙 U))
          simpa [η, CategoryTheory.uliftYoneda] using hnat.symm

/-- Helper for Lemma 7.29.4: every `J`-cover on the source site pushes forward to a covering
sieve for the surjective topology on the full subcategory. -/
theorem sheafSubcategoryRepresentableFunctor_functorPushforward_mem_of_mem
    {U : C} {S : Sieve U} (hS : S ∈ J U) :
    S.functorPushforward (sheafSubcategoryRepresentableFunctor P hP) ∈
      sheafSubcategorySurjectiveTopology P
        ((sheafSubcategoryRepresentableFunctor P hP).obj U) := by
  let v := sheafSubcategoryRepresentableFunctor P hP
  let T : J.Cover U := ⟨S, hS⟩
  let R : Presieve (v.obj U) :=
    Presieve.ofArrows (fun I : T.Arrow ↦ v.obj I.Y) (fun I ↦ v.map I.f)
  have hR : sheafSubcategorySurjectiveCovering P R :=
    sheafSubcategoryRepresentableFunctor_ofArrows_covering
      (P := P) (J := J) hP T
  have hgen :
      Sieve.generate R ∈ sheafSubcategorySurjectiveTopology P (v.obj U) :=
    sheafSubcategorySurjectiveCovering_generate_mem (P := P) hR
  -- Rewrite the generated target sieve as the pushforward of the source cover.
  have hrewrite :
      (T : Sieve U).functorPushforward v = Sieve.generate R := by
    calc
      (T : Sieve U).functorPushforward v =
          (Sieve.ofArrows (fun I : T.Arrow ↦ I.Y) (fun I ↦ I.f)).functorPushforward v := by
            simpa [GrothendieckTopology.Cover.ofArrows_eq T]
      _ = Sieve.generate
            (Presieve.ofArrows (fun I : T.Arrow ↦ v.obj I.Y) (fun I ↦ v.map I.f)) := by
            symm
            simpa using
              (Sieve.generate_map_eq_functorPushforward
                (F := v)
                (s := Presieve.ofArrows (fun I : T.Arrow ↦ I.Y) (fun I ↦ I.f)))
      _ = Sieve.generate R := by rfl
  have hT :
      (T : Sieve U).functorPushforward v ∈
        sheafSubcategorySurjectiveTopology P (v.obj U) := by
    simpa [hrewrite] using hgen
  simpa using hT

/-- Helper for Lemma 7.29.4: the source image sieve of a morphism between sheafified
representables is covering. -/
theorem sheafSubcategoryRepresentableFunctor_imageSieve_mem
    {U' U : C}
    (c :
      (sheafSubcategoryRepresentableFunctor P hP).obj U' ⟶
        (sheafSubcategoryRepresentableFunctor P hP).obj U) :
    (sheafSubcategoryRepresentableFunctor P hP).imageSieve c ∈ J U' := by
  let η :
      CategoryTheory.uliftYoneda.{max u v}.obj U ⟶ (h[U]^#[J]).obj :=
    (sheafificationAdjunction J (Type (max u v))).unit.app
      (CategoryTheory.uliftYoneda.{max u v}.obj U)
  let x : (h[U]^#[J]).obj.obj (op U') :=
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U' c.hom
  have hx :
      (sheafSubcategoryRepresentableFunctor P hP).imageSieve c =
        Presheaf.imageSieve η x := by
    -- Compare the source image sieve with the image sieve of the sheafification unit sectionwise.
    ext W g
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨ULift.up l, ?_⟩
      calc
        η.app (op W) (ULift.up l) =
          J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            ((sheafSubcategoryRepresentableFunctor P hP).map l).hom := by
            exact
              (sheafSubcategoryRepresentableFunctor_section_eq_toSheafify_app
                (P := P) (J := J) hP l).symm
        _ = J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            (((sheafSubcategoryRepresentableFunctor P hP).map g ≫ c).hom) := by
              exact congrArg (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W)
                (congrArg (fun k ↦ k.hom) hl)
        _ = (h[U]^#[J]).obj.map g.op x := by
              simpa [x, sheafSubcategoryRepresentableFunctor,
                GrothendieckTopology.sheafifiedRepresentableMap,
                GrothendieckTopology.sheafifiedRepresentableFunctor,
                GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
                (J.uliftSheafifiedRepresentableHomEquiv_naturality g (h[U]^#[J]) c.hom)
    · rintro ⟨l, hl⟩
      refine ⟨ULift.down l, ?_⟩
      apply ObjectProperty.hom_ext P
      apply (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W).injective
      calc
        J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            ((sheafSubcategoryRepresentableFunctor P hP).map (ULift.down l)).hom =
          η.app (op W) l := by
            exact
              sheafSubcategoryRepresentableFunctor_section_eq_toSheafify_app
                (P := P) (J := J) hP (ULift.down l)
        _ = (h[U]^#[J]).obj.map g.op x := hl
        _ = J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            (((sheafSubcategoryRepresentableFunctor P hP).map g ≫ c).hom) := by
              simpa [x, sheafSubcategoryRepresentableFunctor,
                GrothendieckTopology.sheafifiedRepresentableMap,
                GrothendieckTopology.sheafifiedRepresentableFunctor,
                GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
                (J.uliftSheafifiedRepresentableHomEquiv_naturality g (h[U]^#[J]) c.hom).symm
  have hmem :
      Presheaf.imageSieve η x ∈ J U' :=
    Presheaf.imageSieve_mem J η x
  -- The standard presheaf image-sieve cover becomes exactly the source image sieve.
  simpa [hx] using hmem

/-- Helper for Lemma 7.29.4: equality of two source arrows after sheafification is detected on a
covering equalizer sieve in the source site. -/
theorem sheafSubcategoryRepresentableFunctor_equalizer_mem
    {U' U : C} (a b : U' ⟶ U)
    (h :
      (sheafSubcategoryRepresentableFunctor P hP).map a =
        (sheafSubcategoryRepresentableFunctor P hP).map b) :
    Sieve.equalizer a b ∈ J U' := by
  let η :
      CategoryTheory.uliftYoneda.{max u v}.obj U ⟶ (h[U]^#[J]).obj :=
    (sheafificationAdjunction J (Type (max u v))).unit.app
      (CategoryTheory.uliftYoneda.{max u v}.obj U)
  have hsection :
      η.app (op U') (ULift.up a) = η.app (op U') (ULift.up b) := by
    -- Equality after sheafification gives equality of the corresponding sheafification sections.
    have h' : ((sheafSubcategoryRepresentableFunctor P hP).map a).hom =
        ((sheafSubcategoryRepresentableFunctor P hP).map b).hom := by
      exact congrArg (fun k ↦ k.hom) h
    have h'' := congrArg
      (fun α : h[U']^#[J] ⟶ h[U]^#[J] ↦
        α.hom.app (op U')
          (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
            (𝟙 (h[U']^#[J])))) h'
    have ha :
        ((sheafSubcategoryRepresentableFunctor P hP).map a).hom.hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          η.app (op U') (ULift.up a) := by
      calc
        ((sheafSubcategoryRepresentableFunctor P hP).map a).hom.hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
            ((sheafSubcategoryRepresentableFunctor P hP).map a).hom := by
              exact sheafifiedRepresentable_component_eq_section
                (J := J) (α := ((sheafSubcategoryRepresentableFunctor P hP).map a).hom)
        _ = η.app (op U') (ULift.up a) := by
              exact sheafSubcategoryRepresentableFunctor_section_eq_toSheafify_app
                (P := P) (J := J) hP a
    have hb :
        ((sheafSubcategoryRepresentableFunctor P hP).map b).hom.hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          η.app (op U') (ULift.up b) := by
      calc
        ((sheafSubcategoryRepresentableFunctor P hP).map b).hom.hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
            ((sheafSubcategoryRepresentableFunctor P hP).map b).hom := by
              exact sheafifiedRepresentable_component_eq_section
                (J := J) (α := ((sheafSubcategoryRepresentableFunctor P hP).map b).hom)
        _ = η.app (op U') (ULift.up b) := by
              exact sheafSubcategoryRepresentableFunctor_section_eq_toSheafify_app
                (P := P) (J := J) hP b
    exact ha.symm.trans (h''.trans hb)
  -- The presheaf equalizer sieve for the sheafification unit is the usual source equalizer sieve.
  let xa : ToType ((CategoryTheory.uliftYoneda.{max u v}.obj U).obj (op U')) := ULift.up a
  let xb : ToType ((CategoryTheory.uliftYoneda.{max u v}.obj U).obj (op U')) := ULift.up b
  have hEqSieve :
      Presheaf.equalizerSieve (F := CategoryTheory.uliftYoneda.{max u v}.obj U) xa xb =
        Sieve.equalizer a b := by
    ext W g
    change (CategoryTheory.uliftYoneda.{max u v}.obj U).map g.op xa =
        (CategoryTheory.uliftYoneda.{max u v}.obj U).map g.op xb ↔
      g ≫ a = g ≫ b
    simpa [CategoryTheory.uliftYoneda, xa, xb]
  simpa [hEqSieve] using
    (Presheaf.equalizerSieve_mem (J := J) (φ := η) (X := op U')
      xa xb hsection)

/-- Helper for Lemma 7.29.4: a target surjective covering family lying under the pushforward of a
source sieve forces the source sieve to be covering. -/
theorem sheafSubcategoryRepresentableFunctor_source_family_of_surjective_refinement
    {U : C} {S : Sieve U}
    {R : Presieve ((sheafSubcategoryRepresentableFunctor P hP).obj U)}
    (hR : sheafSubcategorySurjectiveCovering P R)
    (hRS :
      R ≤
        (S.functorPushforward (sheafSubcategoryRepresentableFunctor P hP) :
          Presieve _)) :
    ∃ (ι : Type (max u v)) (Y : ι → C) (π : ∀ i, Y i ⟶ U),
      (∀ i, S (π i)) ∧
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc
            (fun i ↦
              ((sheafSubcategoryRepresentableFunctor P hP).map (π i)).hom)) := by
  classical
  let v := sheafSubcategoryRepresentableFunctor P hP
  rcases hR with ⟨ι, Y₀, π₀, rfl, hπ₀⟩
  let str := fun i : ι ↦
    Presieve.getFunctorPushforwardStructure
      (hRS (Y₀ i) (π₀ i) (Presieve.ofArrows.mk i))
  let E : ι → Type (max u v) := fun i ↦ Σ W : C, v.obj W ⟶ Y₀ i
  let T : ∀ i : ι, (e : E i) → J.Cover e.1 := fun i e ↦
    ⟨v.imageSieve (e.2 ≫ (str i).lift),
      sheafSubcategoryRepresentableFunctor_imageSieve_mem
        (P := P) (J := J) hP (e.2 ≫ (str i).lift)⟩
  let κ : Type (max u v) := Σ i : ι, Σ e : E i, (T i e).Arrow
  let Y : κ → C := fun p ↦ p.2.2.Y
  let π : ∀ p : κ, Y p ⟶ U := fun p ↦ p.2.2.hf.choose ≫ (str p.1).premap
  have hπS : ∀ p : κ, S (π p) := by
    -- Each refined source arrow stays inside `S` because it factors through the chosen
    -- `str i.premap ∈ S`.
    intro p
    exact S.downward_closed (str p.1).cover p.2.2.hf.choose
  have hcomponent_eq :
      ∀ p : κ,
        (v.map p.2.2.f).hom ≫ p.2.1.2.hom ≫ (π₀ p.1).hom =
          (v.map (π p)).hom := by
    -- The image-sieve witness identifies each doubly refined component with the literal
    -- sheafified source arrow `π p`.
    intro p
    have hstr :
        (π₀ p.1).hom = (str p.1).lift.hom ≫ (v.map (str p.1).premap).hom := by
      exact congrArg (fun f ↦ f.hom) (str p.1).fac
    have hk :
        v.map p.2.2.hf.choose =
          v.map p.2.2.f ≫ (p.2.1.2 ≫ (str p.1).lift) := by
      exact p.2.2.hf.choose_spec
    have hk_hom :
        (v.map p.2.2.f).hom ≫ p.2.1.2.hom ≫ (str p.1).lift.hom =
          (v.map p.2.2.hf.choose).hom := by
      simpa [Category.assoc] using (congrArg (fun f ↦ f.hom) hk).symm
    calc
      (v.map p.2.2.f).hom ≫ p.2.1.2.hom ≫ (π₀ p.1).hom =
          (v.map p.2.2.f).hom ≫ p.2.1.2.hom ≫ (str p.1).lift.hom ≫
            (v.map (str p.1).premap).hom := by
              rw [hstr]
      _ = (v.map p.2.2.hf.choose).hom ≫ (v.map (str p.1).premap).hom := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ (v.map (str p.1).premap).hom) hk_hom
      _ = (v.map (π p)).hom := by
            simpa [π, Category.assoc] using
              congrArg (fun f ↦ f.hom)
                (v.map_comp p.2.2.hf.choose (str p.1).premap)
  let _ : HasCoproduct (fun i : ι ↦ (Y₀ i).obj) :=
    hasCoproductOfFullSubcategoryFamily (P := P) Y₀
  let _ : ∀ i : ι, HasCoproduct (fun e : E i ↦ (v.obj e.1).obj) := fun i ↦
    hasCoproductOfFullSubcategoryFamily (P := P) (fun e : E i ↦ v.obj e.1)
  let _ : ∀ i : ι, ∀ e : E i, HasCoproduct (fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) :=
    fun i e ↦
      hasCoproductOfFullSubcategoryFamily (P := P) (fun a : (T i e).Arrow ↦ v.obj a.Y)
  let _ :
      ∀ i : ι, HasCoproduct (fun e : E i ↦ ∐ fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) :=
    fun i ↦ by
      let _ : HasColimitsOfShape (Discrete (E i)) (Type (max u v)) := inferInstance
      let _ : HasColimitsOfShape (Discrete (E i)) (Sheaf J (Type (max u v))) :=
        Sheaf.instHasColimitsOfShape
      infer_instance
  let _ :
      ∀ i : ι, HasCoproduct (fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) :=
    fun i ↦
      hasCoproductOfFullSubcategoryFamily
        (P := P) (fun q : Σ e : E i, (T i e).Arrow ↦ v.obj q.2.Y)
  let _ :
      HasCoproduct
        (fun i : ι ↦ ∐ fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) := by
    let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    infer_instance
  let _ : HasCoproduct (fun p : κ ↦ (v.obj p.2.2.Y).obj) :=
    hasCoproductOfFullSubcategoryFamily (P := P) (fun p : κ ↦ v.obj p.2.2.Y)
  let universalDesc :
      ∀ i : ι, (∐ fun e : E i ↦ (v.obj e.1).obj) ⟶ (Y₀ i).obj :=
    fun i ↦ Limits.Sigma.desc (fun e : E i ↦ e.2.hom)
  let imageDesc :
      ∀ i : ι, ∀ e : E i,
        (∐ fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) ⟶ (v.obj e.1).obj :=
    fun i e ↦ Limits.Sigma.desc (fun a : (T i e).Arrow ↦ (v.map a.f).hom)
  let nestedDesc :
      ∀ i : ι,
        (∐ fun e : E i ↦ ∐ fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) ⟶
          ∐ fun e : E i ↦ (v.obj e.1).obj :=
    fun i ↦
      Limits.Sigma.desc
        (fun e : E i ↦ imageDesc i e ≫ Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e)
  let flatInnerDesc :
      ∀ i : ι,
        (∐ fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) ⟶ (Y₀ i).obj :=
    fun i ↦
      Limits.Sigma.desc
        (fun q : Σ e : E i, (T i e).Arrow ↦ (v.map q.2.f).hom ≫ q.1.2.hom)
  let refinedDesc :
      (∐ fun i : ι ↦ ∐ fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) ⟶
        ∐ fun i : ι ↦ (Y₀ i).obj :=
    Limits.Sigma.desc
      (fun i ↦ flatInnerDesc i ≫ Limits.Sigma.ι (fun i : ι ↦ (Y₀ i).obj) i)
  let outerDesc : (∐ fun i : ι ↦ (Y₀ i).obj) ⟶ (v.obj U).obj :=
    Limits.Sigma.desc (fun i ↦ (π₀ i).hom)
  let flattenInner :
      ∀ i : ι,
        (∐ fun e : E i ↦ ∐ fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) ≅
          ∐ fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj :=
    fun i ↦
      Limits.sigmaSigmaIso
        (fun e : E i ↦ (T i e).Arrow)
        (fun _ a ↦ (v.obj a.Y).obj)
  let flattenOuter :
      (∐ fun i : ι ↦ ∐ fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) ≅
        ∐ fun p : κ ↦ (v.obj p.2.2.Y).obj :=
    Limits.sigmaSigmaIso
      (fun i : ι ↦ Σ e : E i, (T i e).Arrow)
      (fun _ q ↦ (v.obj q.2.Y).obj)
  let finalDesc :
      (∐ fun p : κ ↦ (v.obj p.2.2.Y).obj) ⟶ (v.obj U).obj :=
    Limits.Sigma.desc
      (fun p : κ ↦ (v.map p.2.2.f).hom ≫ p.2.1.2.hom ≫ (π₀ p.1).hom)
  refine ⟨κ, Y, π, hπS, ?_⟩
  have huniversal_surj :
      ∀ i : ι,
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc (fun e : E i ↦ e.2.hom)) := by
    -- The universal family on each `Y₀ i` is locally surjective by the same sectionwise argument
    -- used for the global universal-family cover earlier in the file.
    intro i
    let σ : (∐ fun e : E i ↦ (v.obj e.1).obj) ⟶ (Y₀ i).obj := universalDesc i
    refine ⟨fun {V} x ↦ ?_⟩
    let e : E i :=
      ⟨V, ObjectProperty.homMk ((J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj (Y₀ i)) V).symm x)⟩
    let t : ((∐ fun e : E i ↦ (v.obj e.1).obj).obj).obj (op V) :=
      J.uliftSheafifiedRepresentableHomEquiv (∐ fun e : E i ↦ (v.obj e.1).obj) V
        (Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e)
    have ht : σ.hom.app (op V) t = x := by
      -- Evaluate the chosen coproduct inclusion and then identify the selected component.
      have hcomp :
          σ.hom.app (op V) t =
            (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj (Y₀ i)) V)
              (Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e ≫ σ) := by
        symm
        simpa [t] using
          J.uliftSheafifiedRepresentableHomEquiv_comp
            (Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e) σ
      have hι :
          Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e ≫ σ = e.2.hom := by
        simpa [σ] using
          (Limits.Sigma.ι_desc
            (p := fun e : E i ↦ e.2.hom)
            (b := e))
      have hsection :
          (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj (Y₀ i)) V)
              (Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e ≫ σ) = x := by
        have he :
            e.2.hom = (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj (Y₀ i)) V).symm x := by
          rfl
        calc
          (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj (Y₀ i)) V)
              (Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e ≫ σ) =
            (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj (Y₀ i)) V) (e.2.hom) := by
              exact congrArg (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj (Y₀ i)) V) hι
          _ = x := by
            simpa [he] using
              (J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj (Y₀ i)) V).apply_symm_apply x
      exact hcomp.trans hsection
    have htop : Presheaf.imageSieve σ.hom x = ⊤ := by
      -- Once the chosen section is literally in the image, its image sieve is the maximal sieve.
      calc
        Presheaf.imageSieve σ.hom x =
            Presheaf.imageSieve σ.hom (σ.hom.app (op V) t) := by rw [ht]
        _ = ⊤ := Presheaf.imageSieve_app σ.hom t
    rw [htop]
    exact J.top_mem V
  have himage_surj :
      ∀ (i : ι) (e : E i),
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc (fun a : (T i e).Arrow ↦ (v.map a.f).hom)) := by
    -- Each second-stage family is the canonical sheafified-representable cover map of the image
    -- sieve `T i e`.
    intro i e
    simpa [v, sheafSubcategoryRepresentableFunctor,
      GrothendieckTopology.sheafifiedRepresentableMap] using
      (J.sheafifiedRepresentableCoverMap_isLocallySurjective (S := T i e))
  have hnested_surj :
      ∀ i : ι, Sheaf.IsLocallySurjective (nestedDesc i) := by
    -- Assemble the second-stage locally surjective maps over the universal-family index `e`.
    intro i
    exact
      sheaf_sigma_desc_of_componentwise_isLocallySurjective
        (J := J)
        (fun e : E i ↦ ∐ fun a : (T i e).Arrow ↦ (v.obj a.Y).obj)
        (fun e : E i ↦ (v.obj e.1).obj)
        (fun e ↦ imageDesc i e)
        (himage_surj i)
  have hflatInner :
      ∀ i : ι, (flattenInner i).inv ≫ (nestedDesc i ≫ universalDesc i) = flatInnerDesc i := by
    -- The doubly refined family over `Y₀ i` is the sigma-sigma flattening of the nested owner.
    intro i
    apply Limits.Sigma.hom_ext
    intro q
    cases q with
    | mk e a =>
        calc
          Limits.Sigma.ι (fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) ⟨e, a⟩ ≫
              (flattenInner i).inv ≫ (nestedDesc i ≫ universalDesc i) =
            Limits.Sigma.ι (fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) a ≫
              Limits.Sigma.ι (fun e : E i ↦ ∐ fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) e ≫
                nestedDesc i ≫ universalDesc i := by
                  dsimp [flattenInner]
                  simpa [Category.assoc] using
                    (Limits.Sigma.ι_desc_assoc
                      (p := fun x : Σ e : E i, (T i e).Arrow ↦
                        Limits.Sigma.ι (fun a : (T i x.1).Arrow ↦ (v.obj a.Y).obj) x.2 ≫
                          Limits.Sigma.ι
                            (fun e : E i ↦ ∐ fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) x.1)
                      (b := ⟨e, a⟩) (h := nestedDesc i ≫ universalDesc i))
          _ = (v.map a.f).hom ≫ e.2.hom := by
            calc
              Limits.Sigma.ι (fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) a ≫
                  Limits.Sigma.ι (fun e : E i ↦ ∐ fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) e ≫
                    nestedDesc i ≫ universalDesc i =
                Limits.Sigma.ι (fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) a ≫
                  (imageDesc i e ≫
                    Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e) ≫ universalDesc i := by
                      simpa [nestedDesc, Category.assoc] using
                        congrArg
                          (fun k ↦
                            Limits.Sigma.ι (fun a : (T i e).Arrow ↦ (v.obj a.Y).obj) a ≫ k)
                          (Limits.Sigma.ι_desc_assoc
                            (p := fun e : E i ↦
                              imageDesc i e ≫
                                Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e)
                            (b := e) (h := universalDesc i))
              _ = (v.map a.f).hom ≫ Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e ≫
                    universalDesc i := by
                      simpa [imageDesc, Category.assoc] using
                        (Limits.Sigma.ι_desc_assoc
                          (p := fun a : (T i e).Arrow ↦ (v.map a.f).hom)
                          (b := a)
                          (h := Limits.Sigma.ι (fun e : E i ↦ (v.obj e.1).obj) e ≫
                            universalDesc i))
              _ = (v.map a.f).hom ≫ e.2.hom := by
                simpa [universalDesc, Category.assoc] using
                  congrArg (fun k ↦ (v.map a.f).hom ≫ k)
                    (Limits.Sigma.ι_desc (p := fun e : E i ↦ e.2.hom) (b := e))
          _ =
              Limits.Sigma.ι (fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) ⟨e, a⟩ ≫
                flatInnerDesc i := by
                  symm
                  simpa [flatInnerDesc, Category.assoc] using
                    (Limits.Sigma.ι_desc
                      (p := fun q : Σ e : E i, (T i e).Arrow ↦
                        (v.map q.2.f).hom ≫ q.1.2.hom)
                      (b := ⟨e, a⟩))
  have hflatInner_surj :
      ∀ i : ι, Sheaf.IsLocallySurjective (flatInnerDesc i) := by
    -- Compose the two refinement stages over `Y₀ i`, then reindex the source by `sigmaSigmaIso`.
    intro i
    have hcomp : Sheaf.IsLocallySurjective (nestedDesc i ≫ universalDesc i) := by
      let _ : Sheaf.IsLocallySurjective (nestedDesc i) := hnested_surj i
      let _ : Sheaf.IsLocallySurjective (universalDesc i) := huniversal_surj i
      infer_instance
    have hflat_surj :
        Sheaf.IsLocallySurjective ((flattenInner i).inv ≫ (nestedDesc i ≫ universalDesc i)) := by
      let _ : Sheaf.IsLocallySurjective (flattenInner i).inv := by infer_instance
      let _ : Sheaf.IsLocallySurjective (nestedDesc i ≫ universalDesc i) := hcomp
      infer_instance
    have hflat' : (flattenInner i).inv ≫ nestedDesc i ≫ universalDesc i = flatInnerDesc i := by
      simpa [Category.assoc] using hflatInner i
    simpa [Category.assoc, hflat'] using hflat_surj
  have hrefined_surj : Sheaf.IsLocallySurjective refinedDesc := by
    -- Assemble the locally surjective refined families over the original outer index `i`.
    exact
      sheaf_sigma_desc_of_componentwise_isLocallySurjective
        (J := J)
        (fun i : ι ↦ ∐ fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj)
        (fun i : ι ↦ (Y₀ i).obj)
        (fun i ↦ flatInnerDesc i)
        hflatInner_surj
  have hflatOuter :
      flattenOuter.inv ≫ (refinedDesc ≫ outerDesc) = finalDesc := by
    -- Flatten the outer sigma-index and identify the resulting component maps with the explicit
    -- three-stage composite into `v.obj U`.
    apply Limits.Sigma.hom_ext
    intro p
    cases p with
    | mk i q =>
        cases q with
        | mk e a =>
            calc
              Limits.Sigma.ι (fun p : κ ↦ (v.obj p.2.2.Y).obj) ⟨i, ⟨e, a⟩⟩ ≫
                  flattenOuter.inv ≫ (refinedDesc ≫ outerDesc) =
                Limits.Sigma.ι (fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) ⟨e, a⟩ ≫
                  Limits.Sigma.ι
                    (fun i : ι ↦ ∐ fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) i ≫
                      refinedDesc ≫ outerDesc := by
                        dsimp [flattenOuter]
                        simpa [Category.assoc] using
                          (Limits.Sigma.ι_desc_assoc
                            (p := fun x : κ ↦
                              Limits.Sigma.ι
                                  (fun q : Σ e : E x.1, (T x.1 e).Arrow ↦
                                    (v.obj q.2.Y).obj) x.2 ≫
                                Limits.Sigma.ι
                                  (fun i : ι ↦
                                    ∐ fun q : Σ e : E i, (T i e).Arrow ↦
                                      (v.obj q.2.Y).obj) x.1)
                            (b := ⟨i, ⟨e, a⟩⟩) (h := refinedDesc ≫ outerDesc))
              _ = (v.map a.f).hom ≫ e.2.hom ≫ (π₀ i).hom := by
                calc
                  Limits.Sigma.ι (fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) ⟨e, a⟩ ≫
                      Limits.Sigma.ι
                        (fun i : ι ↦ ∐ fun q : Σ e : E i, (T i e).Arrow ↦
                          (v.obj q.2.Y).obj) i ≫ refinedDesc ≫ outerDesc =
                    Limits.Sigma.ι (fun q : Σ e : E i, (T i e).Arrow ↦ (v.obj q.2.Y).obj) ⟨e, a⟩ ≫
                      (flatInnerDesc i ≫ Limits.Sigma.ι (fun i : ι ↦ (Y₀ i).obj) i) ≫
                        outerDesc := by
                          simpa [refinedDesc, Category.assoc] using
                            congrArg
                              (fun k ↦
                                Limits.Sigma.ι
                                  (fun q : Σ e : E i, (T i e).Arrow ↦
                                    (v.obj q.2.Y).obj) ⟨e, a⟩ ≫ k)
                              (Limits.Sigma.ι_desc_assoc
                                (p := fun i : ι ↦
                                  flatInnerDesc i ≫
                                    Limits.Sigma.ι (fun i : ι ↦ (Y₀ i).obj) i)
                                (b := i) (h := outerDesc))
                  _ = ((v.map a.f).hom ≫ e.2.hom) ≫
                        Limits.Sigma.ι (fun i : ι ↦ (Y₀ i).obj) i ≫ outerDesc := by
                        simpa [flatInnerDesc, Category.assoc] using
                          (Limits.Sigma.ι_desc_assoc
                            (p := fun q : Σ e : E i, (T i e).Arrow ↦
                              (v.map q.2.f).hom ≫ q.1.2.hom)
                            (b := ⟨e, a⟩)
                            (h := Limits.Sigma.ι (fun i : ι ↦ (Y₀ i).obj) i ≫ outerDesc))
                  _ = (v.map a.f).hom ≫ e.2.hom ≫ (π₀ i).hom := by
                    simpa [outerDesc, Category.assoc] using
                      congrArg (fun k ↦ ((v.map a.f).hom ≫ e.2.hom) ≫ k)
                        (Limits.Sigma.ι_desc (p := fun i : ι ↦ (π₀ i).hom) (b := i))
              _ =
                  Limits.Sigma.ι (fun p : κ ↦ (v.obj p.2.2.Y).obj) ⟨i, ⟨e, a⟩⟩ ≫
                    finalDesc := by
                      symm
                      simpa [finalDesc, Category.assoc] using
                        (Limits.Sigma.ι_desc
                          (p := fun p : κ ↦
                            (v.map p.2.2.f).hom ≫ p.2.1.2.hom ≫ (π₀ p.1).hom)
                          (b := ⟨i, ⟨e, a⟩⟩))
  have hfinal_surj : Sheaf.IsLocallySurjective finalDesc := by
    -- Compose the flattened refined source with the original surjective family.
    have hcomp : Sheaf.IsLocallySurjective (refinedDesc ≫ outerDesc) := by
      let _ : Sheaf.IsLocallySurjective refinedDesc := hrefined_surj
      let _ : Sheaf.IsLocallySurjective outerDesc := by simpa [outerDesc] using hπ₀
      infer_instance
    have hflat_surj : Sheaf.IsLocallySurjective (flattenOuter.inv ≫ (refinedDesc ≫ outerDesc)) := by
      let _ : Sheaf.IsLocallySurjective flattenOuter.inv := by infer_instance
      let _ : Sheaf.IsLocallySurjective (refinedDesc ≫ outerDesc) := hcomp
      infer_instance
    have hflat' : flattenOuter.inv ≫ refinedDesc ≫ outerDesc = finalDesc := by
      simpa [Category.assoc] using hflatOuter
    simpa [Category.assoc, hflat'] using hflat_surj
  have hfinal_eq :
      finalDesc = Limits.Sigma.desc (fun p : κ ↦ (v.map (π p)).hom) := by
    -- The bookkeeping lemma `hcomponent_eq` identifies each flattened component with the literal
    -- sheafified source arrow `π p`.
    apply Limits.Sigma.hom_ext
    intro p
    calc
      Limits.Sigma.ι (fun p : κ ↦ (v.obj p.2.2.Y).obj) p ≫ finalDesc =
          (v.map p.2.2.f).hom ≫ p.2.1.2.hom ≫ (π₀ p.1).hom := by
            simpa [finalDesc] using
              (Limits.Sigma.ι_desc
                (p := fun p : κ ↦ (v.map p.2.2.f).hom ≫ p.2.1.2.hom ≫ (π₀ p.1).hom)
                (b := p))
      _ = (v.map (π p)).hom := hcomponent_eq p
      _ = Limits.Sigma.ι (fun p : κ ↦ (v.obj p.2.2.Y).obj) p ≫
            Limits.Sigma.desc (fun p : κ ↦ (v.map (π p)).hom) := by
              symm
              simpa using
                (Limits.Sigma.ι_desc
                  (p := fun p : κ ↦ (v.map (π p)).hom)
                  (b := p))
  simpa [Y, hfinal_eq] using hfinal_surj

/-- Helper for Lemma 7.29.4: a target surjective covering family lying under the pushforward of a
source sieve forces the source sieve to be covering. -/
theorem sheafSubcategoryRepresentableFunctor_source_mem_of_surjective_refinement
    {U : C} {S : Sieve U}
    {R : Presieve ((sheafSubcategoryRepresentableFunctor P hP).obj U)}
    (hR : sheafSubcategorySurjectiveCovering P R)
    (hRS :
      R ≤
        (S.functorPushforward (sheafSubcategoryRepresentableFunctor P hP) :
          Presieve _)) :
    S ∈ J U := by
  obtain ⟨ι, Y, π, hπS, hπsurj⟩ :=
    sheafSubcategoryRepresentableFunctor_source_family_of_surjective_refinement
      (P := P) (J := J) hP hR hRS
  let _ : HasCoproduct (fun i : ι ↦ h[Y i]^#[J]) := by
    let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
    let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    infer_instance
  have hpres :
      Presheaf.IsLocallySurjective J
        (Limits.Sigma.desc (fun i ↦ CategoryTheory.uliftYoneda.{max u v}.map (π i))) := by
    exact
      (J.isLocallySurjective_sigmaDesc_sheafifiedRepresentableMap_iff Y π).1
        hπsurj
  have hcover : Sieve.ofArrows Y π ∈ J U := by
    exact
      (J.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map π).2
        hpres
  have hle : Sieve.ofArrows Y π ≤ S := by
    intro W f hf
    rw [Sieve.mem_ofArrows_iff] at hf
    rcases hf with ⟨i, g, rfl⟩
    exact S.downward_closed (hπS i) g
  -- Enlarge the explicitly produced source cover to the ambient sieve `S`.
  exact J.superset_covering hle hcover

/-- Lemma 7.29.4 (3): if every sheafified representable `h_U^#` belongs to the chosen full
subcategory, then the functor `v : \mathcal C \to \mathcal C'`, `U ↦ h_U^#`, is special
cocontinuous for the surjective topology on `\mathcal C'`. -/
-- Proof sketch: continuity and cocontinuity come from the description of coverings by locally
-- surjective maps of sheaves, the local fullness and faithfulness conditions are read off from the
-- sheafification adjunction on representables, and closure under pullbacks ensures the fibre
-- product conditions stay inside the full subcategory.
instance sheafSubcategoryRepresentableFunctor_isDenseSubsite :
    (sheafSubcategoryRepresentableFunctor P hP).IsDenseSubsite
      J (sheafSubcategorySurjectiveTopology P) := by
  refine
    { isCoverDense' := ?_
      isLocallyFull' := ?_
      isLocallyFaithful' := ?_
      functorPushforward_mem_iff := ?_ }
  · -- Route correction: cover density is proved from the universal family of all maps out of
    -- sheafified representables, rather than via the blocked basis-presentation route.
    exact ⟨fun ℱ ↦ sheafSubcategoryRepresentableFunctor_coverByImage_mem
      (P := P) (J := J) hP ℱ⟩
  · -- Source-local fullness on `J` pushes forward to target-local fullness on the surjective site.
    exact ⟨fun c ↦
      sheafSubcategoryRepresentableFunctor_functorPushforward_mem_of_mem
        (P := P) (J := J) hP
        (sheafSubcategoryRepresentableFunctor_imageSieve_mem
          (P := P) (J := J) hP c)⟩
  · -- Source-local faithfulness on `J` pushes forward to target-local faithfulness on the
    -- surjective site.
    exact ⟨fun a b h ↦
      sheafSubcategoryRepresentableFunctor_functorPushforward_mem_of_mem
        (P := P) (J := J) hP
        (sheafSubcategoryRepresentableFunctor_equalizer_mem
          (P := P) (J := J) hP a b h)⟩
  · intro U S
    refine Iff.intro ?_ ?_
    · -- TODO: the converse should refine a target surjective family by universal representable
      -- covers and then recover a source `J`-cover from the refined family.
      intro hS
      rw [sheafSubcategorySurjectiveTopology_def, Pretopology.mem_toGrothendieck] at hS
      rcases hS with ⟨R, hR, hRS⟩
      exact
        sheafSubcategoryRepresentableFunctor_source_mem_of_surjective_refinement
          (P := P) (J := J) hP hR hRS
    · -- Forward direction: a source covering gives the canonical sheafified representable cover.
      intro hS
      exact
        sheafSubcategoryRepresentableFunctor_functorPushforward_mem_of_mem
          (P := P) (J := J) hP hS

/- Bridge/view recall: once
`sheafSubcategoryRepresentableFunctor_isDenseSubsite` upgrades `U ↦ h_U^#` to the chapter's
canonical owner `Functor.IsDenseSubsite`, the induced cocontinuous direct image
on sheaves of sets is an equivalence after supplying the needed pointwise right Kan extensions, by
the bridge theorem from Definition `7.29.2`. -/
#check
  Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
    (sheafSubcategoryRepresentableFunctor P hP)

noncomputable def inverseImageYonedaObjUnderlyingIso
    (ℱ : P.FullSubcategory) :
    (((sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardContinuous
      (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)).obj
      ((sheafSubcategorySurjectiveTopology P).yoneda.obj ℱ)).obj ≅
        (P.ι.obj ℱ).obj :=
  NatIso.ofComponents
    (fun U ↦
      let e := J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj ℱ) U.unop
      Equiv.toIso
        { toFun := fun α ↦ e α.hom
          invFun := fun x ↦ ObjectProperty.homMk (e.symm x)
          left_inv := fun α ↦ ObjectProperty.hom_ext P (e.symm_apply_apply α.hom)
          right_inv := e.apply_symm_apply })
    (fun {U V} f ↦ by
      ext α
      simpa using
        J.uliftSheafifiedRepresentableHomEquiv_naturality f.unop (P.ι.obj ℱ) α.hom)

/-- Lemma 7.29.4 (4): for any object `\mathcal F` of the full subcategory, the inverse image of
the representable sheaf `h_\mathcal F` on `\mathcal C'` is canonically isomorphic to the
underlying sheaf `\mathcal F` on `\mathcal C`. -/
-- Proof sketch: evaluate the inverse image of the representable sheaf of `ℱ` on `U`; this gives
-- morphisms `h_U^# ⟶ ℱ`, which the sheafification adjunction identifies with sections of the
-- underlying ambient sheaf `ℱ.obj` over `U`.
noncomputable def sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso
    (ℱ : P.FullSubcategory) :
    (((sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardContinuous
      (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)).obj
      ((sheafSubcategorySurjectiveTopology P).yoneda.obj ℱ) ≅
        P.ι.obj ℱ) :=
  { hom := homMk (inverseImageYonedaObjUnderlyingIso P hP ℱ).hom
    inv := homMk (inverseImageYonedaObjUnderlyingIso P hP ℱ).inv
    hom_inv_id := by
      apply hom_ext
      exact (inverseImageYonedaObjUnderlyingIso P hP ℱ).hom_inv_id
    inv_hom_id := by
      apply hom_ext
      exact (inverseImageYonedaObjUnderlyingIso P hP ℱ).inv_hom_id }

-- Proof sketch: any isomorphism satisfies `hom ≫ inv = 𝟙`; apply this to the canonical inverse
-- image comparison isomorphism above.
/-- The inverse-image comparison isomorphism for representable sheaves has the expected left
inverse identity. -/
theorem sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso_hom_inv_id
    (ℱ : P.FullSubcategory) :
    (sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso P hP ℱ).hom ≫
        (sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso P hP ℱ).inv =
      𝟙 _ := by
  -- The comparison map is an isomorphism, so `hom ≫ inv = 𝟙`.
  simp

/-- Lemma 7.29.4 (5): for any `U` in `\mathcal C`, the direct image of `h_U^#` along the induced
equivalence is canonically the representable sheaf of `v(U)` in the subcanonical site
`\mathcal C'`. -/
-- Proof sketch: combine the adjunction between inverse and direct image with clause (4); then use
-- the Yoneda identification in the subcanonical topology on `\mathcal C'`.
noncomputable def sheafSubcategoryRepresentableFunctor_pushforward_sheafifiedRepresentable_iso
    (U : C) :
    (((sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardCocontinuous
      (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)).obj
      h[U]^#[J] ≅
        (sheafSubcategorySurjectiveTopology P).yoneda.obj
          ((sheafSubcategoryRepresentableFunctor P hP).obj U)) :=
  let g := (sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardCocontinuous
    (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)
  let q := (sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardContinuous
    (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)
  let _ : q.IsEquivalence := inferInstance
  let e := q.asEquivalence
  let adj := (sheafSubcategoryRepresentableFunctor P hP).sheafAdjunctionCocontinuous
    (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)
  let Y := (sheafSubcategorySurjectiveTopology P).yoneda.obj
    ((sheafSubcategoryRepresentableFunctor P hP).obj U)
  let h : g ≅ e.inverse := Adjunction.rightAdjointUniq adj e.toAdjunction
  h.app (h[U]^#[J]) ≪≫
    e.inverse.mapIso
      (sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso P hP
        ((sheafSubcategoryRepresentableFunctor P hP).obj U)).symm ≪≫
    (e.unitIso.app Y).symm

-- Proof sketch: any isomorphism satisfies `hom ≫ inv = 𝟙`; apply this to the canonical direct
-- image comparison isomorphism above.
/-- The direct-image comparison isomorphism for sheafified representables has the expected left
inverse identity. -/
theorem sheafSubcategoryRepresentableFunctor_pushforward_sheafifiedRepresentable_iso_hom_inv_id
    (U : C) :
    (sheafSubcategoryRepresentableFunctor_pushforward_sheafifiedRepresentable_iso P hP U).hom ≫
        (sheafSubcategoryRepresentableFunctor_pushforward_sheafifiedRepresentable_iso P hP U).inv =
      𝟙 _ := by
  -- The direct-image comparison is likewise an isomorphism, so the left inverse identity is
  -- immediate.
  simp

end

end ObjectProperty
end CategoryTheory
