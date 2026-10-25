module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import stacks_project.Chap07.Definition_7_17_1
public import stacks_project.Chap07.Definition_7_17_4
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Lemma_7_17_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

open Limits
open CategoryTheory.Presheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/-
Source/core/bridge triage for 7.17.5:
- core/canonical owner: `ObjectProperty.IsClosedUnderQuotients` applied to
  `Sheaf.IsQuasiCompactObject`
- source-facing statements: Lemma `7.17.5 (2)` on sheaves and Lemma `7.17.5 (1)` on site objects
- bridge/view: `Sheaf.isLocallySurjective_iff_epi`, `J.sheafifiedRepresentableMap`, together with
  `GrothendieckTopology.quasiCompactObject_iff_isQuasiCompactObject_sheafifiedRepresentable`
- primitive data: the owner predicate `Sheaf.IsQuasiCompactObject`
- derived API: quotient stability for locally surjective morphisms and the site-side transfer along
  sheafified representables
-/

omit [HasWeakSheafify J (Type (max u v))] in
/-- Helper for Lemma 7.17.5: on presheaves, pulling back each summand of a locally surjective
sigma-desc along a fixed map preserves local surjectivity. -/
private theorem presheaf_isLocallySurjective_sigmaDesc_pullback_snd
    {F G : Cᵒᵖ ⥤ Type (max u v)} (q : F ⟶ G)
    {ι : Type (max u v)} (X : ι → Cᵒᵖ ⥤ Type (max u v))
    (α : ∀ i, X i ⟶ G) [HasCoproduct X] [HasCoproduct fun i ↦ pullback (α i) q]
    (hα : Presheaf.IsLocallySurjective J (Limits.Sigma.desc α)) :
    Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i ↦ pullback.snd (α i) q)) := by
  -- Route correction: the pullback bridge is proved sectionwise by unpacking a coproduct witness,
  -- turning it into a pointwise pullback witness, and then repacking it into the pulled-back
  -- coproduct.
  refine ⟨fun s ↦ J.superset_covering ?_ (hα.imageSieve_mem (q.app _ s))⟩
  intro V g hg
  rcases hg with ⟨y, hy⟩
  cases hxy : (Types.coproductIso (fun i ↦ (X i).obj (op V))).hom
      ((Limits.sigmaObjIso X (op V)).hom y) with
  | mk i x =>
      -- First isolate the summand of the coproduct section that maps to the chosen local image.
      have hcopro :
          (Types.coproductIso (fun i ↦ (X i).obj (op V))).inv ⟨i, x⟩ =
            Sigma.ι (fun i ↦ (X i).obj (op V)) i x := by
        exact congrFun
          (Types.coproductIso_mk_comp_inv (fun i ↦ (X i).obj (op V)) i) x
      have hpre' := congrArg
          (fun z ↦ (Types.coproductIso (fun i ↦ (X i).obj (op V))).inv z) hxy
      have hpre :
          (Limits.sigmaObjIso X (op V)).hom y =
            Sigma.ι (fun i ↦ (X i).obj (op V)) i x := by
        simpa [hcopro] using hpre'
      have hy' : y = (Limits.sigmaObjIso X (op V)).inv
          (Sigma.ι (fun i ↦ (X i).obj (op V)) i x) := by
        simpa using congrArg (fun z ↦ (Limits.sigmaObjIso X (op V)).inv z) hpre
      have hdesc_mor :
          (Sigma.ι X i).app (op V) ≫ (Limits.Sigma.desc α).app (op V) = (α i).app (op V) := by
        simpa using CategoryTheory.congr_app (Limits.Sigma.ι_desc α i) (op V)
      have hdesc :
          (Limits.Sigma.desc α).app (op V)
            ((Limits.sigmaObjIso X (op V)).inv
              (Sigma.ι (fun i ↦ (X i).obj (op V)) i x)) =
            (α i).app (op V) x := by
        simpa using
          congrFun
            ((Limits.ι_comp_sigmaObjIso_inv_assoc X (op V) i
              ((Limits.Sigma.desc α).app (op V))).trans hdesc_mor) x
      have hx : (α i).app (op V) x = G.map g.op (q.app _ s) := by
        rw [← hdesc, ← hy']
        exact hy
      have hqx : (α i).app (op V) x = q.app (op V) (F.map g.op s) := by
        calc
          (α i).app (op V) x = G.map g.op (q.app _ s) := hx
          _ = q.app (op V) (F.map g.op s) := by
            symm
            simpa using congrFun (q.naturality g.op) s
      -- Build the corresponding pointwise pullback element and then reinsert it into the coproduct.
      let t' : Types.PullbackObj ((α i).app (op V)) (q.app (op V)) :=
        ⟨⟨x, F.map g.op s⟩, hqx⟩
      let t : (pullback (α i) q).obj (op V) :=
        (Limits.pullbackObjIso (α i) q (op V)).inv ((Types.pullbackIsoPullback _ _).inv t')
      have hsnd : (pullback.snd (α i) q).app (op V) t = F.map g.op s := by
        dsimp [t]
        simpa [t'] using
          congrFun (Limits.pullbackObjIso_inv_comp_snd (α i) q (op V))
            ((Types.pullbackIsoPullback ((α i).app (op V)) (q.app (op V))).inv t')
      have hdesc'_mor :
          (Sigma.ι (fun i ↦ pullback (α i) q) i).app (op V) ≫
              (Limits.Sigma.desc (fun i ↦ pullback.snd (α i) q)).app (op V) =
            (pullback.snd (α i) q).app (op V) := by
        simpa using
          CategoryTheory.congr_app
            (Limits.Sigma.ι_desc (fun i ↦ pullback.snd (α i) q) i) (op V)
      refine ⟨
        (Limits.sigmaObjIso (fun i ↦ pullback (α i) q) (op V)).inv
          (Sigma.ι (fun i ↦ (pullback (α i) q).obj (op V)) i t),
        ?_⟩
      simpa using
        (congrFun
            ((Limits.ι_comp_sigmaObjIso_inv_assoc (fun i ↦ pullback (α i) q)
              (op V) i ((Limits.Sigma.desc (fun i ↦ pullback.snd (α i) q)).app (op V))).trans
              hdesc'_mor) t).trans hsnd

/-- Helper for Lemma 7.17.5: local surjectivity of a sheaf sigma-desc is equivalent to local
surjectivity of the corresponding underlying presheaf sigma-desc after inserting the
sheafification comparison isomorphisms. -/
private theorem isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc
    {ι : Type (max u v)} (X : ι → Sheaf J (Type (max u v)))
    {G : Sheaf J (Type (max u v))}
    (α : ∀ i, X i ⟶ G) [HasCoproduct X] :
    IsLocallySurjective (Limits.Sigma.desc α) ↔
      Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i ↦ (α i).hom)) := by
  let Gsh := presheafToSheaf J (Type (max u v))
  let Fpres : ι → Cᵒᵖ ⥤ Type (max u v) := fun i ↦ (X i).obj
  let gPres : ∐ Fpres ⟶ G.obj := Limits.Sigma.desc (fun i ↦ (α i).hom)
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let Y : ι → Sheaf J (Type (max u v)) := fun i ↦ Gsh.obj (Fpres i)
  let _ : HasCoproduct Y := by
    simpa [Y, Fpres, Gsh] using
      (Limits.hasCoproduct_of_equiv_of_iso X Y (Equiv.refl _) fun i ↦
        (sheafificationIso (X i)).symm)
  let sourceIso : (∐ X) ⟶ ∐ Y := Limits.Sigma.map (fun i ↦ (sheafificationIso (X i)).hom)
  let middle : (∐ Y) ⟶ Gsh.obj (∐ Fpres) := Limits.sigmaComparison Gsh Fpres
  have hfac :
      Limits.Sigma.desc α = sourceIso ≫ middle ≫ Gsh.map gPres ≫ (sheafificationIso G).inv := by
    -- Compare the sheaf sigma-desc with the sheafified presheaf sigma-desc componentwise.
    apply Limits.Sigma.hom_ext
    intro i
    have hnat :
        (sheafificationIso (X i)).hom ≫ Gsh.map ((α i).hom) ≫ (sheafificationIso G).inv =
          α i := by
      -- Naturality of the sheafification isomorphism identifies each component map.
      have hnat' :
          (sheafificationIso (X i)).hom ≫ Gsh.map ((α i).hom) =
            α i ≫ (sheafificationIso G).hom := by
        simpa [Gsh, sheafificationNatIso, sheafificationIso] using
          ((sheafificationNatIso J (Type (max u v))).hom.naturality (α i)).symm
      calc
        (sheafificationIso (X i)).hom ≫ Gsh.map ((α i).hom) ≫ (sheafificationIso G).inv =
            α i ≫ (sheafificationIso G).hom ≫ (sheafificationIso G).inv := by
              simpa [Category.assoc] using
                congrArg (fun k => k ≫ (sheafificationIso G).inv) hnat'
        _ = α i := by simp
    rw [Limits.Sigma.ι_desc]
    symm
    change Limits.Sigma.ι X i ≫ Limits.Sigma.map (fun i ↦ (sheafificationIso (X i)).hom) ≫
          Limits.sigmaComparison Gsh Fpres ≫ Gsh.map gPres ≫ (sheafificationIso G).inv = α i
    rw [Limits.Sigma.ι_map_assoc, Limits.ι_comp_sigmaComparison_assoc]
    have hι : Gsh.map (Limits.Sigma.ι Fpres i) ≫ Gsh.map gPres = Gsh.map ((α i).hom) := by
      -- The presheaf sigma-desc collapses to the chosen component after the `i`th injection.
      simpa [gPres, Fpres] using
        congrArg (fun k => Gsh.map k)
          (Limits.Sigma.ι_desc (f := Fpres) (p := fun j ↦ (α j).hom) (b := i))
    calc
      (sheafificationIso (X i)).hom ≫ Gsh.map (Limits.Sigma.ι Fpres i) ≫ Gsh.map gPres ≫
          (sheafificationIso G).inv =
        (sheafificationIso (X i)).hom ≫ Gsh.map ((α i).hom) ≫ (sheafificationIso G).inv := by
          simpa [Category.assoc] using
            congrArg (fun k => (sheafificationIso (X i)).hom ≫ k ≫ (sheafificationIso G).inv) hι
      _ = α i := hnat
  constructor
  · intro hdesc
    have hcomp :
        Sheaf.IsLocallySurjective
          (sourceIso ≫ middle ≫ Gsh.map gPres ≫ (sheafificationIso G).inv) := by
      -- Replace the original sigma-desc by the comparison factorization.
      exact hfac.symm ▸ hdesc
    have hmid : Sheaf.IsLocallySurjective (middle ≫ Gsh.map gPres) := by
      -- Cancel the source and target isomorphisms on the sheaf side.
      rw [Sheaf.isLocallySurjective_iff_epi] at hcomp ⊢
      have hcomp' : Epi ((sourceIso ≫ (middle ≫ Gsh.map gPres)) ≫ (sheafificationIso G).inv) := by
        simpa [Category.assoc] using hcomp
      have hleft : Epi (sourceIso ≫ (middle ≫ Gsh.map gPres)) :=
        (epi_comp_iff_of_isIso
          (sourceIso ≫ (middle ≫ Gsh.map gPres)) ((sheafificationIso G).inv)).1 hcomp'
      exact
        (epi_comp_iff_of_epi sourceIso (middle ≫ Gsh.map gPres)).1
          (by simpa [Category.assoc] using hleft)
    have hmap : Sheaf.IsLocallySurjective (Gsh.map gPres) := by
      -- Cancel the sigma-comparison after moving to the presheaf side.
      rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
      have hmid' :
          Presheaf.IsLocallySurjective J
            ((sheafToPresheaf J (Type (max u v))).map (middle ≫ Gsh.map gPres)) := by
        exact hmid
      have hmid'' :
          Presheaf.IsLocallySurjective J
            (((sheafToPresheaf J (Type (max u v))).map middle) ≫
              (sheafToPresheaf J (Type (max u v))).map (Gsh.map gPres)) := by
        rw [Functor.map_comp] at hmid'
        exact hmid'
      let _ :
          Presheaf.IsLocallySurjective J
            ((sheafToPresheaf J (Type (max u v))).map middle) := by
        infer_instance
      let _ :
          Presheaf.IsLocallyInjective J
            ((sheafToPresheaf J (Type (max u v))).map middle) := by
        infer_instance
      exact
        (Presheaf.comp_isLocallySurjective_iff J
          ((sheafToPresheaf J (Type (max u v))).map middle)
          ((sheafToPresheaf J (Type (max u v))).map (Gsh.map gPres))).1 hmid''
    rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff] at hmap
    simpa [gPres] using hmap
  · intro hpres
    have hmap : Sheaf.IsLocallySurjective (Gsh.map gPres) := by
      -- Sheafify the locally surjective presheaf sigma-desc.
      rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
      simpa [gPres] using hpres
    let _ : Sheaf.IsLocallySurjective (Gsh.map gPres) := hmap
    have hmid : Sheaf.IsLocallySurjective (middle ≫ Gsh.map gPres) := by
      -- Compose back with the sigma-comparison on the sheaf side.
      infer_instance
    let _ : Sheaf.IsLocallySurjective (middle ≫ Gsh.map gPres) := hmid
    have hcomp :
        Sheaf.IsLocallySurjective
          (sourceIso ≫ middle ≫ Gsh.map gPres ≫ (sheafificationIso G).inv) := by
      -- Reinsert the source and target isomorphisms to recover the original sigma-desc.
      infer_instance
    exact hfac ▸ hcomp

/-- Helper for Lemma 7.17.5: pulling back each summand of a locally surjective sheaf sigma-desc
along a fixed map preserves local surjectivity. -/
private theorem isLocallySurjective_sigma_desc_pullback_snd
    {F G : Sheaf J (Type (max u v))} (q : F ⟶ G)
    {ι : Type (max u v)} (X : ι → Sheaf J (Type (max u v)))
    (α : ∀ i, X i ⟶ G)
    [HasCoproduct X] [HasCoproduct fun i ↦ pullback (α i) q]
    (hα : IsLocallySurjective (Limits.Sigma.desc α)) :
    IsLocallySurjective (Limits.Sigma.desc fun i ↦ pullback.snd (α i) q) := by
  let Fsh := sheafToPresheaf J (Type (max u v))
  let sourceMap :
      ∐ (fun i ↦ Fsh.obj (pullback (α i) q)) ⟶
        ∐ (fun i ↦ pullback (Fsh.map (α i)) (Fsh.map q)) :=
    Limits.Sigma.map (fun i ↦ Limits.pullbackComparison Fsh (α i) q)
  have hα_pres :
      Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i ↦ Fsh.map (α i))) := by
    -- Move the original sigma-desc to the presheaf level.
    simpa using (isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc (J := J) X α).1 hα
  have hpull_pres :
      Presheaf.IsLocallySurjective J
        (Limits.Sigma.desc (fun i ↦ pullback.snd (Fsh.map (α i)) (Fsh.map q))) := by
    -- Apply the sectionwise presheaf pullback construction.
    simpa using
      presheaf_isLocallySurjective_sigmaDesc_pullback_snd
        (J := J) (Fsh.map q) (fun i ↦ Fsh.obj (X i)) (fun i ↦ Fsh.map (α i)) hα_pres
  have hfac :
      sourceMap ≫ Limits.Sigma.desc (fun i ↦ pullback.snd (Fsh.map (α i)) (Fsh.map q)) =
        Limits.Sigma.desc (fun i ↦ Fsh.map (pullback.snd (α i) q)) := by
    -- The pullback comparison identifies the presheaf pullback family with the underlying
    -- presheaf of the sheaf pullback family.
    apply Limits.Sigma.hom_ext
    intro i
    simp only [sourceMap, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc]
    exact Limits.pullbackComparison_comp_snd Fsh (α i) q
  have hpull_sheaf_pres :
      Presheaf.IsLocallySurjective J
        (Limits.Sigma.desc (fun i ↦ Fsh.map (pullback.snd (α i) q))) := by
    -- Compose the locally surjective presheaf pullback family with the pullback comparison map.
    let _ : Presheaf.IsLocallySurjective J sourceMap := by
      infer_instance
    have hcomp :
        Presheaf.IsLocallySurjective J
          (sourceMap ≫ Limits.Sigma.desc (fun i ↦ pullback.snd (Fsh.map (α i)) (Fsh.map q))) := by
      exact (Presheaf.comp_isLocallySurjective_iff J sourceMap _).2 hpull_pres
    exact hfac ▸ hcomp
  -- Transport the pulled-back sigma-desc back to the sheaf level.
  exact
    (isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc
      (J := J) (fun i ↦ pullback (α i) q) (fun i ↦ pullback.snd (α i) q)).2 <| by
        simpa using hpull_sheaf_pres

omit [HasWeakSheafify J (Type (max u v))] in
/-- Helper for Lemma 7.17.5: once each pulled-back summand satisfies the pullback compatibility
relation, the finite pulled-back coproduct map factors through the corresponding finite original
family map. -/
lemma restricted_pullback_family_factorization
    {ι : Type (max u v)} {T : Set ι}
    {F G : Sheaf J (Type (max u v))} {X Y : ι → Sheaf J (Type (max u v))}
    [HasCoproduct X] [HasCoproduct fun i : T ↦ X i.1] [HasCoproduct fun i : T ↦ Y i.1]
    (π : F ⟶ G) (a : ∐ X ⟶ G)
    (fstY : ∀ i, Y i ⟶ X i) (sndY : ∀ i, Y i ⟶ F)
    (hcomp : ∀ i, sndY i ≫ π = fstY i ≫ Limits.Sigma.ι X i ≫ a) :
    Limits.Sigma.desc (fun i : T ↦ sndY i.1) ≫ π =
      Limits.Sigma.map (fun i : T ↦ fstY i.1) ≫
        Limits.Sigma.desc (fun i : T ↦ Limits.Sigma.ι X i.1 ≫ a) := by
  -- Reduce the coproduct equality to each finite summand and rewrite using the pullback relation.
  apply Limits.Sigma.hom_ext
  intro i
  rw [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc]
  simpa using hcomp i.1

omit [HasWeakSheafify J (Type (max u v))] in
/-- Helper for Lemma 7.17.5: if a finite pulled-back family factors through a finite original
family and the pulled-back family together with the quotient map are locally surjective, then the
original finite family is locally surjective as well. -/
lemma isLocallySurjective_of_epi_factorization
    {A B C D : Sheaf J (Type (max u v))}
    {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ D} {k : D ⟶ C}
    (fac : f ≫ g = h ≫ k)
    (hf : IsLocallySurjective f) (hg : IsLocallySurjective g) :
    IsLocallySurjective k := by
  -- Read local surjectivity as epimorphism and descend the epi across the factorization.
  rw [Sheaf.isLocallySurjective_iff_epi] at hf hg ⊢
  letI : Epi (f ≫ g) := by infer_instance
  exact CategoryTheory.epi_of_epi_fac fac.symm

instance isQuasiCompactObject_isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) := by
  refine ⟨?_⟩
  intro F G π _ hF
  refine ⟨?_⟩
  intro ι X _ a ha
  classical
  -- Route correction: switch from sheafified presheaf pullbacks to the canonical sheaf pullback
  -- family so the pullback compatibility is exactly `pullback.condition`.
  let Y : ι → Sheaf J (Type (max u v)) := fun i ↦ pullback (Limits.Sigma.ι X i ≫ a) π
  let fstY : ∀ i, Y i ⟶ X i := fun i ↦ pullback.fst (Limits.Sigma.ι X i ≫ a) π
  let sndY : ∀ i, Y i ⟶ F := fun i ↦ pullback.snd (Limits.Sigma.ι X i ≫ a) π
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let _ : HasCoproduct Y := by
    infer_instance
  let b : (∐ Y) ⟶ F := Limits.Sigma.desc sndY
  have hb : IsLocallySurjective b := by
    -- Pull back the locally surjective source family along the quotient map.
    have ha' : IsLocallySurjective (Limits.Sigma.desc (fun i ↦ Limits.Sigma.ι X i ≫ a)) := by
      have hdesc : Limits.Sigma.desc (fun i ↦ Limits.Sigma.ι X i ≫ a) = a := by
        apply Limits.Sigma.hom_ext
        intro i
        rw [Limits.Sigma.ι_desc]
      simpa [hdesc] using ha
    simpa [b, sndY] using
      isLocallySurjective_sigma_desc_pullback_snd
        (J := J) (q := π) (X := X) (α := fun i ↦ Limits.Sigma.ι X i ≫ a) ha'
  obtain ⟨T, hT, hbT_raw⟩ := hF.finite_subcoproduct Y b hb
  let _ : Fintype T := hT.fintype
  let _ : HasColimitsOfShape (Discrete T) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let bT : (∐ fun i : T ↦ Y i.1) ⟶ F :=
    Limits.Sigma.desc (fun i : T ↦ Limits.Sigma.ι Y i.1 ≫ b)
  have hbT : IsLocallySurjective bT := by
    simpa [bT] using hbT_raw
  let γ : (∐ fun i : T ↦ X i.1) ⟶ G :=
    Limits.Sigma.desc (fun i : T ↦ Limits.Sigma.ι X i.1 ≫ a)
  let δ : (∐ fun i : T ↦ Y i.1) ⟶ (∐ fun i : T ↦ X i.1) :=
    Limits.Sigma.map (fun i : T ↦ fstY i.1)
  have hpull : ∀ i, sndY i ≫ π = fstY i ≫ Limits.Sigma.ι X i ≫ a := by
    -- Each component identity is the defining commutativity of the pullback square.
    intro i
    simpa [fstY, sndY, Category.assoc] using
      (pullback.condition (f := Limits.Sigma.ι X i ≫ a) (g := π)).symm
  have hbT_eq : bT = Limits.Sigma.desc (fun i : T ↦ sndY i.1) := by
    apply Limits.Sigma.hom_ext
    intro i
    calc
      Limits.Sigma.ι (fun i : T ↦ Y i.1) i ≫ bT =
          Limits.Sigma.ι Y i.1 ≫ b := by
            simpa [bT] using
              (Limits.Sigma.ι_desc (fun i : T ↦ Limits.Sigma.ι Y i.1 ≫ b) i)
      _ = sndY i.1 := by
        simpa [b, sndY] using (Limits.Sigma.ι_desc sndY i)
      _ = Limits.Sigma.ι (fun i : T ↦ Y i.1) i ≫ Limits.Sigma.desc (fun i : T ↦ sndY i.1) := by
        symm
        exact Limits.Sigma.ι_desc (fun i : T ↦ sndY i.1) i
  have hfac : bT ≫ π = δ ≫ γ := by
    rw [hbT_eq]
    simpa [γ, δ] using
      restricted_pullback_family_factorization
        (J := J) (T := T) (F := F) (G := G) (X := X) (Y := Y) π a fstY sndY hpull
  have hπ : IsLocallySurjective π := by
    rw [Sheaf.isLocallySurjective_iff_epi]
    infer_instance
  -- With the finite factorization in place, epi descent converts the finite pulled-back family
  -- into the finite original family required by quasi-compactness of `G`.
  refine ⟨T, hT, ?_⟩
  exact isLocallySurjective_of_epi_factorization (J := J) hfac hbT hπ

/-- Lemma 7.17.5 (2): a locally surjective image of a quasi-compact sheaf of sets is
quasi-compact. -/
theorem isQuasiCompactObject_of_isLocallySurjective
    {F G : Sheaf J (Type (max u v))} (π : F ⟶ G)
    (hπ : IsLocallySurjective π) (hF : F.IsQuasiCompactObject) :
    G.IsQuasiCompactObject := by
  -- Route correction: once quotient-closure is established, the target is the epi image of `F`.
  rw [Sheaf.isLocallySurjective_iff_epi] at hπ
  exact
    ObjectProperty.prop_of_epi
      (P := (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v))))) π hF

end CategoryTheory.Sheaf

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open CategoryTheory.Sheaf
open scoped SheafifiedRepresentable

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/-- Lemma 7.17.5 (1): if `h[U]^#[J] ⟶ h[V]^#[J]` is locally surjective and `U` is quasi-compact,
then `V` is quasi-compact. -/
theorem quasiCompactObject_of_isLocallySurjective_sheafifiedRepresentableMap
    {U V : C} (f : U ⟶ V)
    (hf : IsLocallySurjective (J.sheafifiedRepresentableMap f))
    (hU : J.QuasiCompactObject U) :
    J.QuasiCompactObject V := by
  -- Route correction: transport quasi-compactness to sheafified representables, apply the sheaf
  -- statement, and transport back.
  rw [J.quasiCompactObject_iff_isQuasiCompactObject_sheafifiedRepresentable] at hU ⊢
  exact
    CategoryTheory.Sheaf.isQuasiCompactObject_of_isLocallySurjective
      (π := J.sheafifiedRepresentableMap f) hf hU

end CategoryTheory.GrothendieckTopology
