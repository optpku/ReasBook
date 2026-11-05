module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import stacks_project.Chap07.Definition_7_17_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

universe u v

namespace CategoryTheory
namespace Sheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} [HasWeakSheafify J (Type (max u v))]

/- Source/core/bridge triage for 7.17.6:
- source-facing notion: `Sheaf.IsQuasiCompactObject`
- core/canonical owner:
  `ObjectProperty.IsClosedUnderFiniteCoproducts
    (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v))))`
- bridge/view: any finite-family coproduct statement is obtained directly from
  `ObjectProperty.prop_coproduct`, so no parallel wrapper theorem is kept here
-/

omit [HasWeakSheafify J (Type (max u v))] in
/-- Helper for Lemma 7.17.6: a finite coproduct of componentwise locally surjective maps is again
locally surjective. -/
theorem isLocallySurjective_sigma_desc_of_componentwise
    {α : Type*} [Finite α]
    (Y F : α → Sheaf J (Type (max u v))) [HasCoproduct Y] [HasCoproduct F]
    (γ : ∀ a, Y a ⟶ F a)
    (hγ : ∀ a, IsLocallySurjective (γ a)) :
    IsLocallySurjective (Limits.Sigma.desc fun a ↦ γ a ≫ Limits.Sigma.ι F a) := by
  rw [Sheaf.isLocallySurjective_iff_epi]
  refine ⟨?_⟩
  intro Z g h hEq
  -- Test the equality after each coproduct injection into the finite target family.
  apply Limits.colimit.hom_ext
  intro j
  obtain ⟨a⟩ := j
  -- The component map `γ a` is epi, so equality after precomposing with it is enough.
  apply (cancel_epi (γ a)).1
  have hEq' := congrArg (fun k => Limits.Sigma.ι Y a ≫ k) hEq
  simpa only [CategoryTheory.Limits.Sigma.ι_desc_assoc] using hEq'

/-
The finite-union step only uses coproduct universal properties and the presheaf factorization API,
so the sheafification hypothesis is intentionally omitted from this helper.
-/
omit [HasWeakSheafify J (Type (max u v))] in
/-- Helper for Lemma 7.17.6: enlarging the chosen finite source subset preserves local
surjectivity of the induced subcoproduct map. -/
theorem isLocallySurjective_sigma_desc_of_subset
    {ι : Type*} {S T : Set ι} (hST : S ⊆ T)
    (X : ι → Sheaf J (Type (max u v))) {F : Sheaf J (Type (max u v))}
    [HasCoproduct X] (π : (∐ X) ⟶ F)
    [HasCoproduct fun i : S ↦ X i.1] [HasCoproduct fun i : T ↦ X i.1]
    (hS :
      IsLocallySurjective
        (Limits.Sigma.desc fun i : S ↦ Limits.Sigma.ι X i.1 ≫ π)) :
    IsLocallySurjective
      (Limits.Sigma.desc fun i : T ↦ Limits.Sigma.ι X i.1 ≫ π) := by
  -- Factor the `S`-indexed map through the `T`-indexed one using the subtype inclusion.
  let ιST : (∐ fun i : S ↦ X i.1) ⟶ ∐ fun i : T ↦ X i.1 :=
    Limits.Sigma.desc fun i : S ↦ Limits.Sigma.ι (fun j : T ↦ X j.1) ⟨i.1, hST i.2⟩
  have hfac :
      ιST ≫ Limits.Sigma.desc (fun i : T ↦ Limits.Sigma.ι X i.1 ≫ π) =
        Limits.Sigma.desc (fun i : S ↦ Limits.Sigma.ι X i.1 ≫ π) := by
    -- Each `S`-summand lands in the matching `T`-summand, so the two sigma-desc maps agree.
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
    simpa using
      (Limits.Sigma.ι_desc
        (f := fun j : S ↦ X j.1)
        (p := fun j : S ↦ Limits.Sigma.ι X j.1 ≫ π)
        (b := i)).symm
  -- Local surjectivity descends across this factorization on underlying presheaves.
  exact
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (congrArg (fun f => f.hom) hfac)

/-- Helper for Lemma 7.17.6: local surjectivity of a sheaf sigma-desc is equivalent to local
surjectivity of the underlying presheaf sigma-desc after inserting the sheafification comparison.
-/
theorem isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc
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
      -- Now cancel the sigma-comparison on the presheaf side, where the local criterion is stable.
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
      -- Finally reinsert the source and target comparison isomorphisms.
      infer_instance
    exact hfac ▸ hcomp

omit [HasWeakSheafify J (Type (max u v))] in
/-- Helper for Lemma 7.17.6: on presheaves, pulling back each summand along a fixed map preserves
local surjectivity of the sigma-desc. -/
theorem presheaf_isLocallySurjective_sigma_desc_pullback_snd
    {F G : Cᵒᵖ ⥤ Type (max u v)} (q : F ⟶ G)
    {ι : Type (max u v)} (X : ι → Cᵒᵖ ⥤ Type (max u v))
    (α : ∀ i, X i ⟶ G) [HasCoproduct X] [HasCoproduct fun i ↦ pullback (α i) q]
    (hα : Presheaf.IsLocallySurjective J (Limits.Sigma.desc α)) :
    Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i ↦ pullback.snd (α i) q)) := by
  -- Route correction: unpack a local coproduct preimage, lift it pointwise to the pullback, and
  -- then repack it into the pulled-back coproduct.
  refine ⟨fun s ↦ J.superset_covering ?_ (hα.imageSieve_mem (q.app _ s))⟩
  intro V g hg
  rcases hg with ⟨y, hy⟩
  cases hxy : (Types.coproductIso (fun i ↦ (X i).obj (op V))).hom
      ((Limits.sigmaObjIso X (op V)).hom y) with
  | mk i x =>
      -- Identify the coproduct summand containing the chosen local section.
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
      -- Package the pointwise witness into the pulled-back summand.
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

/-- Helper for Lemma 7.17.6: restricting a locally surjective coproduct map to one target summand
preserves local surjectivity on the original source family. -/
theorem isLocallySurjective_sigma_desc_pullback_snd
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
    -- First move the original sigma-desc to the presheaf level.
    simpa using (isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc (J := J) X α).1 hα
  have hpull_pres :
      Presheaf.IsLocallySurjective J
        (Limits.Sigma.desc (fun i ↦ pullback.snd (Fsh.map (α i)) (Fsh.map q))) := by
    -- Then perform the pullback-local-preimage construction on presheaves.
    simpa using
      presheaf_isLocallySurjective_sigma_desc_pullback_snd
        (J := J) (Fsh.map q) (fun i ↦ Fsh.obj (X i)) (fun i ↦ Fsh.map (α i)) hα_pres
  have hfac :
      sourceMap ≫ Limits.Sigma.desc (fun i ↦ pullback.snd (Fsh.map (α i)) (Fsh.map q)) =
        Limits.Sigma.desc (fun i ↦ Fsh.map (pullback.snd (α i) q)) := by
    -- The pullback comparison isomorphisms identify the presheaf pullback family with the
    -- underlying presheaf of the sheaf pullback family.
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
  -- Finally transport the pulled-back sigma-desc back to the sheaf level.
  exact
    (isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc
      (J := J) (fun i ↦ pullback (α i) q) (fun i ↦ pullback.snd (α i) q)).2 <| by
        simpa using hpull_sheaf_pres

/-- Helper for Lemma 7.17.6: quasi-compactness is invariant under isomorphism. -/
instance isQuasiCompactObject_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) where
  of_iso e hF := by
    refine ⟨?_⟩
    intro ι X _ π hπ
    let π' : (∐ X) ⟶ _ := π ≫ e.inv
    have hπ' : IsLocallySurjective π' := by
      -- Precompose the given locally surjective map with the inverse isomorphism.
      rw [Sheaf.isLocallySurjective_iff_epi] at hπ ⊢
      let _ : Epi π := hπ
      let _ : Epi e.inv := by infer_instance
      infer_instance
    obtain ⟨T, hT, hTsurj'⟩ := hF.finite_subcoproduct X π' hπ'
    let _ : Fintype T := hT.fintype
    let _ : HasColimitsOfShape (Discrete T) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    let δ' : (∐ fun i : T ↦ X i.1) ⟶ _ :=
      Limits.Sigma.desc fun i : T ↦ Limits.Sigma.ι X i.1 ≫ π'
    let δ : (∐ fun i : T ↦ X i.1) ⟶ _ :=
      Limits.Sigma.desc fun i : T ↦ Limits.Sigma.ι X i.1 ≫ π
    have hδ : IsLocallySurjective δ := by
      -- Compose the finite witness for `π ≫ e.inv` back with the target isomorphism.
      have hcomp : δ' ≫ e.hom = δ := by
        apply Limits.Sigma.hom_ext
        intro i
        calc
          Limits.Sigma.ι (fun i : T ↦ X i.1) i ≫ δ' ≫ e.hom =
              Limits.Sigma.ι X i.1 ≫ π' ≫ e.hom := by
                rw [Limits.Sigma.ι_desc_assoc, Category.assoc]
          _ = Limits.Sigma.ι X i.1 ≫ π := by
                simp [π', Category.assoc]
          _ = Limits.Sigma.ι (fun i : T ↦ X i.1) i ≫ δ := by
                symm
                simpa [δ] using
                  (Limits.Sigma.ι_desc (fun i : T ↦ Limits.Sigma.ι X i.1 ≫ π) i)
      have hδcomp : IsLocallySurjective (δ' ≫ e.hom) := by
        rw [Sheaf.isLocallySurjective_iff_epi] at hTsurj' ⊢
        let _ : Epi δ' := by simpa [δ'] using hTsurj'
        let _ : Epi e.hom := by infer_instance
        infer_instance
      exact hcomp ▸ hδcomp
    exact ⟨T, hT, hδ⟩

/-- Helper for Lemma 7.17.6: the nested pullback family over a finite target family collapses back
to the common finite source subcoproduct by forgetting the target index and projecting from each
pullback. -/
noncomputable abbrev nested_restricted_pullback_collapse
    {α ι : Type*} [Finite α] (X : ι → Sheaf J (Type (max u v)))
    (F : α → Sheaf J (Type (max u v))) [HasCoproduct X] [HasCoproduct F]
    {T : Set ι} [Finite T] (π : (∐ X) ⟶ ∐ F)
    [∀ a : α, HasCoproduct fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun a : α ↦ ∐ fun t : T ↦
      pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun t : T ↦ X t.1] :
    (∐ fun a : α ↦ ∐ fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) ⟶
      ∐ fun t : T ↦ X t.1 :=
  Limits.Sigma.desc fun a ↦
    Limits.Sigma.desc fun t : T ↦
      pullback.fst (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a) ≫
        Limits.Sigma.ι (fun t : T ↦ X t.1) t

/-- Helper for Lemma 7.17.6: reindex the nested restricted pullback source by the equivalent
pair index `T × α`, so the global pullback-distribution lemma can be applied once. -/
noncomputable abbrev nested_restricted_pullback_pair_source_iso
    {α ι : Type*} [Finite α] (X : ι → Sheaf J (Type (max u v)))
    (F : α → Sheaf J (Type (max u v))) [HasCoproduct X] [HasCoproduct F]
    {T : Set ι} [Finite T] (π : (∐ X) ⟶ ∐ F)
    [∀ a : α, HasCoproduct fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun a : α ↦ ∐ fun t : T ↦
      pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun q : Σ a : α, T ↦
      pullback (Limits.Sigma.ι X q.2.1 ≫ π) (Limits.Sigma.ι F q.1)]
    [HasCoproduct fun p : T × α ↦
      pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2)] :
    (∐ fun a : α ↦ ∐ fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) ≅
      (∐ fun p : T × α ↦
        pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2)) :=
  Limits.sigmaSigmaIso (fun _ : α ↦ T)
      (fun a t ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) ≪≫
    Limits.Sigma.whiskerEquiv
      ((Equiv.sigmaEquivProd α T).trans (Equiv.prodComm α T))
      (fun p ↦ eqToIso (by cases p <;> rfl))

/-- Helper for Lemma 7.17.6: the pair-indexed restricted pullback source collapses to the common
finite source subcoproduct by projecting to the `X`-side of each pullback. -/
noncomputable abbrev nested_restricted_pullback_pair_collapse
    {α ι : Type*} [Finite α] (X : ι → Sheaf J (Type (max u v)))
    (F : α → Sheaf J (Type (max u v))) [HasCoproduct X] [HasCoproduct F]
    {T : Set ι} [Finite T] (π : (∐ X) ⟶ ∐ F)
    [HasCoproduct fun p : T × α ↦
      pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2)]
    [HasCoproduct fun t : T ↦ X t.1] :
    (∐ fun p : T × α ↦ pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2)) ⟶
      ∐ fun t : T ↦ X t.1 :=
  Limits.Sigma.desc fun p : T × α ↦
    pullback.fst (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2) ≫
      Limits.Sigma.ι (fun t : T ↦ X t.1) p.1

/-- Helper for Lemma 7.17.6: the source reindexing isomorphism sends the nested injection for
`(a, t)` to the corresponding pair-indexed injection `(t, a)`. -/
theorem nested_restricted_pullback_pair_source_iso_hom_ι_ι
    {α ι : Type*} [Finite α] (X : ι → Sheaf J (Type (max u v)))
    (F : α → Sheaf J (Type (max u v))) [HasCoproduct X] [HasCoproduct F]
    {T : Set ι} [Finite T] (π : (∐ X) ⟶ ∐ F)
    [∀ a : α, HasCoproduct fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun a : α ↦ ∐ fun t : T ↦
      pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun q : Σ a : α, T ↦
      pullback (Limits.Sigma.ι X q.2.1 ≫ π) (Limits.Sigma.ι F q.1)]
    [HasCoproduct fun p : T × α ↦
      pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2)]
    (a : α) (t : T) :
    Limits.Sigma.ι (fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) t ≫
        Limits.Sigma.ι
          (fun a : α ↦ ∐ fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
          a ≫
        (nested_restricted_pullback_pair_source_iso (J := J) (T := T) X F π).hom =
      Limits.Sigma.ι
        (fun p : T × α ↦ pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2))
        (t, a) := by
  -- Route correction: isolate the sigma-reindexing normalization before comparing the full
  -- collapse maps, so the remaining extensionality proof becomes a direct coproduct calculation.
  rw [nested_restricted_pullback_pair_source_iso, Iso.trans_hom, Limits.sigmaSigmaIso_hom,
    Limits.Sigma.whiskerEquiv_hom]
  let m :
      (∐ fun p : Σ a : α, T ↦ pullback (Limits.Sigma.ι X p.2.1 ≫ π) (Limits.Sigma.ι F p.1)) ⟶
        ∐ fun p : T × α ↦ pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2) :=
    Limits.Sigma.map' (_root_.Prod.swap ∘ ⇑(Equiv.sigmaEquivProd α T))
      (fun j : Σ a : α, T ↦
        𝟙 (pullback (Limits.Sigma.ι X j.2.1 ≫ π) (Limits.Sigma.ι F j.1)))
  have hOuter :
      Limits.Sigma.ι
          (fun a : α ↦ ∐ fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
          a ≫
        Limits.Sigma.desc
          (fun i : α ↦
            Limits.Sigma.desc
              (fun x : T ↦
                Limits.Sigma.ι
                  (fun p : Σ a : α, T ↦
                    pullback (Limits.Sigma.ι X p.2.1 ≫ π) (Limits.Sigma.ι F p.1))
                  ⟨i, x⟩)) ≫
        m =
      Limits.Sigma.desc
        (fun x : T ↦
          Limits.Sigma.ι
            (fun p : Σ a : α, T ↦
              pullback (Limits.Sigma.ι X p.2.1 ≫ π) (Limits.Sigma.ι F p.1))
            ⟨a, x⟩) ≫
        m := by
    simpa [m, Category.assoc] using
      (Limits.Sigma.ι_desc_assoc
        (p := fun i : α ↦
          Limits.Sigma.desc
            (fun x : T ↦
              Limits.Sigma.ι
                (fun p : Σ a : α, T ↦
                  pullback (Limits.Sigma.ι X p.2.1 ≫ π) (Limits.Sigma.ι F p.1))
                ⟨i, x⟩))
        (b := a) (h := m))
  have hOuter' := congrArg
      (fun k ↦
        Limits.Sigma.ι
            (fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
            t ≫
          k)
      hOuter
  have hInner :
      Limits.Sigma.ι
          (fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
          t ≫
        Limits.Sigma.desc
          (fun x : T ↦
            Limits.Sigma.ι
              (fun p : Σ a : α, T ↦
                pullback (Limits.Sigma.ι X p.2.1 ≫ π) (Limits.Sigma.ι F p.1))
              ⟨a, x⟩) ≫
        m =
      Limits.Sigma.ι
          (fun p : Σ a : α, T ↦
            pullback (Limits.Sigma.ι X p.2.1 ≫ π) (Limits.Sigma.ι F p.1))
          ⟨a, t⟩ ≫
        m := by
    simpa [m, Category.assoc] using
      (Limits.Sigma.ι_desc_assoc
        (p := fun x : T ↦
          Limits.Sigma.ι
            (fun p : Σ a : α, T ↦
              pullback (Limits.Sigma.ι X p.2.1 ≫ π) (Limits.Sigma.ι F p.1))
            ⟨a, x⟩)
        (b := t) (h := m))
  calc
    Limits.Sigma.ι
          (fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
          t ≫
        Limits.Sigma.ι
          (fun a : α ↦ ∐ fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
          a ≫
        Limits.Sigma.desc
          (fun i : α ↦
            Limits.Sigma.desc
              (fun x : T ↦
                Limits.Sigma.ι
                  (fun p : Σ a : α, T ↦
                    pullback (Limits.Sigma.ι X p.2.1 ≫ π) (Limits.Sigma.ι F p.1))
                  ⟨i, x⟩)) ≫
        Limits.Sigma.map' (_root_.Prod.swap ∘ ⇑(Equiv.sigmaEquivProd α T))
          (fun j : Σ a : α, T ↦
            𝟙 (pullback (Limits.Sigma.ι X j.2.1 ≫ π) (Limits.Sigma.ι F j.1))) =
      Limits.Sigma.ι
          (fun p : Σ a : α, T ↦
            pullback (Limits.Sigma.ι X p.2.1 ≫ π) (Limits.Sigma.ι F p.1))
          ⟨a, t⟩ ≫
        Limits.Sigma.map' (_root_.Prod.swap ∘ ⇑(Equiv.sigmaEquivProd α T))
          (fun j : Σ a : α, T ↦
            𝟙 (pullback (Limits.Sigma.ι X j.2.1 ≫ π) (Limits.Sigma.ι F j.1))) := by
          simpa [m, Category.assoc] using hOuter'.trans hInner
    _ = Limits.Sigma.ι
          (fun p : T × α ↦ pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2))
          (t, a) := by
          rw [Limits.Sigma.ι_comp_map']
          simp

/-- Helper for Lemma 7.17.6: the original nested collapse map is the reindexed pair-indexed
collapse map after the canonical source reindexing isomorphism. -/
theorem nested_restricted_pullback_collapse_reindexed
    {α ι : Type*} [Finite α] (X : ι → Sheaf J (Type (max u v)))
    (F : α → Sheaf J (Type (max u v))) [HasCoproduct X] [HasCoproduct F]
    {T : Set ι} [Finite T] (π : (∐ X) ⟶ ∐ F)
    [∀ a : α, HasCoproduct fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun a : α ↦ ∐ fun t : T ↦
      pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun q : Σ a : α, T ↦
      pullback (Limits.Sigma.ι X q.2.1 ≫ π) (Limits.Sigma.ι F q.1)]
    [HasCoproduct fun p : T × α ↦
      pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2)]
    [HasCoproduct fun t : T ↦ X t.1] :
    nested_restricted_pullback_collapse (J := J) (T := T) X F π =
      (nested_restricted_pullback_pair_source_iso (J := J) (T := T) X F π).hom ≫
        nested_restricted_pullback_pair_collapse (J := J) (T := T) X F π := by
  -- Compare the two collapse maps after restricting to each outer and inner coproduct summand.
  apply Limits.Sigma.hom_ext
  intro a
  apply Limits.Sigma.hom_ext
  intro t
  have hOuter :
      Limits.Sigma.ι
          (fun a : α ↦ ∐ fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
          a ≫
        nested_restricted_pullback_collapse (J := J) (T := T) X F π =
      Limits.Sigma.desc
        (fun t : T ↦
          pullback.fst (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a) ≫
            Limits.Sigma.ι (fun t : T ↦ X t.1) t) := by
    simpa [nested_restricted_pullback_collapse] using
      (Limits.Sigma.ι_desc
        (fun a : α ↦
          Limits.Sigma.desc
            (fun t : T ↦
              pullback.fst (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a) ≫
                Limits.Sigma.ι (fun t : T ↦ X t.1) t))
        a)
  have hOuter' := congrArg
      (fun k ↦
        Limits.Sigma.ι
            (fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
            t ≫
          k)
      hOuter
  have hInner :
      Limits.Sigma.ι
          (fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
          t ≫
        Limits.Sigma.desc
          (fun t : T ↦
            pullback.fst (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a) ≫
              Limits.Sigma.ι (fun t : T ↦ X t.1) t) =
      pullback.fst (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a) ≫
        Limits.Sigma.ι (fun t : T ↦ X t.1) t := by
    simpa using
      (Limits.Sigma.ι_desc
        (fun t : T ↦
          pullback.fst (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a) ≫
            Limits.Sigma.ι (fun t : T ↦ X t.1) t)
        t)
  have hPair :
      Limits.Sigma.ι
          (fun p : T × α ↦ pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2))
          (t, a) ≫
        nested_restricted_pullback_pair_collapse (J := J) (T := T) X F π =
      pullback.fst (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a) ≫
        Limits.Sigma.ι (fun t : T ↦ X t.1) t := by
    simpa [nested_restricted_pullback_pair_collapse] using
      (Limits.Sigma.ι_desc
        (fun p : T × α ↦
          pullback.fst (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2) ≫
            Limits.Sigma.ι (fun t : T ↦ X t.1) p.1)
        (t, a))
  -- The source reindexing identifies the `(a, t)` summand with the pair-indexed summand `(t, a)`.
  calc
    Limits.Sigma.ι (fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) t ≫
        Limits.Sigma.ι
            (fun a : α ↦ ∐ fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
            a ≫
          nested_restricted_pullback_collapse (J := J) (T := T) X F π =
      pullback.fst (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a) ≫
        Limits.Sigma.ι (fun t : T ↦ X t.1) t := by
          simpa [Category.assoc] using hOuter'.trans hInner
    _ =
      Limits.Sigma.ι
          (fun p : T × α ↦ pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2))
          (t, a) ≫
        nested_restricted_pullback_pair_collapse (J := J) (T := T) X F π := by
          simpa using hPair.symm
    _ =
      Limits.Sigma.ι (fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) t ≫
        Limits.Sigma.ι
            (fun a : α ↦ ∐ fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a))
            a ≫
          (nested_restricted_pullback_pair_source_iso (J := J) (T := T) X F π).hom ≫
            nested_restricted_pullback_pair_collapse (J := J) (T := T) X F π := by
          rw [← nested_restricted_pullback_pair_source_iso_hom_ι_ι]
          simp [Category.assoc]

/-- Helper for Lemma 7.17.6: the pair-indexed restricted pullback collapse is the first projection
in the global pullback square distributing finite coproducts over pullbacks. -/
theorem isIso_nested_restricted_pullback_pair_collapse
    {α ι : Type*} [Finite α] (X : ι → Sheaf J (Type (max u v)))
    (F : α → Sheaf J (Type (max u v))) [HasCoproduct X] [HasCoproduct F]
    {T : Set ι} [Finite T] (π : (∐ X) ⟶ ∐ F)
    [HasCoproduct fun p : T × α ↦
      pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2)]
    [HasCoproduct fun t : T ↦ X t.1] :
    IsIso (nested_restricted_pullback_pair_collapse (J := J) (T := T) X F π) := by
  have hpb :
      IsPullback
        (nested_restricted_pullback_pair_collapse (J := J) (T := T) X F π)
        (Limits.Sigma.desc fun p : T × α ↦
          pullback.snd (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2) ≫
            Limits.Sigma.ι F p.2)
        (Limits.Sigma.desc fun t : T ↦ Limits.Sigma.ι X t.1 ≫ π)
        (Limits.Sigma.desc fun a : α ↦ Limits.Sigma.ι F a) := by
    -- Distribute the pullback of `π` along the finite target coproduct all at once.
    simpa [nested_restricted_pullback_pair_collapse] using
      (FinitaryPreExtensive.isPullback_sigmaDesc
        (C := Sheaf J (Type (max u v)))
        (f := fun t : T ↦ Limits.Sigma.ι X t.1 ≫ π)
        (g := fun a : α ↦ Limits.Sigma.ι F a))
  have hId : Limits.Sigma.desc (fun a : α ↦ Limits.Sigma.ι F a) = 𝟙 (∐ F) := by
    -- The coproduct map assembled from the target injections is the identity.
    apply Limits.Sigma.hom_ext
    intro a
    simpa using (Limits.Sigma.ι_desc (fun a : α ↦ Limits.Sigma.ι F a) a)
  let _ : IsIso (Limits.Sigma.desc fun a : α ↦ Limits.Sigma.ι F a) := by
    rw [hId]
    infer_instance
  let _ :
      HasPullback
        (Limits.Sigma.desc fun t : T ↦ Limits.Sigma.ι X t.1 ≫ π)
        (Limits.Sigma.desc fun a : α ↦ Limits.Sigma.ι F a) := hpb.hasPullback
  have hfac :
      hpb.isoPullback.hom ≫
          pullback.fst
            (Limits.Sigma.desc fun t : T ↦ Limits.Sigma.ι X t.1 ≫ π)
            (Limits.Sigma.desc fun a : α ↦ Limits.Sigma.ι F a) =
        nested_restricted_pullback_pair_collapse (J := J) (T := T) X F π := by
    -- The pair-indexed collapse is the canonical pullback projection up to the pullback iso.
    simpa using hpb.isoPullback_hom_fst
  -- Both factors on the right are isomorphisms, so the pair-collapse map is too.
  rw [← hfac]
  infer_instance

/-- Helper for Lemma 7.17.6: the nested restricted pullback collapse map is an isomorphism, by
identifying it with the first projection in the global pullback square over a finite coproduct. -/
theorem isIso_nested_restricted_pullback_collapse
    {α ι : Type*} [Finite α] (X : ι → Sheaf J (Type (max u v)))
    (F : α → Sheaf J (Type (max u v))) [HasCoproduct X] [HasCoproduct F]
    {T : Set ι} [Finite T] (π : (∐ X) ⟶ ∐ F)
    [∀ a : α, HasCoproduct fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun a : α ↦ ∐ fun t : T ↦
      pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun q : Σ a : α, T ↦
      pullback (Limits.Sigma.ι X q.2.1 ≫ π) (Limits.Sigma.ι F q.1)]
    [HasCoproduct fun p : T × α ↦
      pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2)]
    [HasCoproduct fun t : T ↦ X t.1] :
    IsIso (nested_restricted_pullback_collapse (J := J) (T := T) X F π) := by
  -- Rewrite to the pair-indexed collapse, whose isomorphism was proved directly from extensivity.
  rw [nested_restricted_pullback_collapse_reindexed (J := J) (T := T) X F π]
  let _ : IsIso (nested_restricted_pullback_pair_collapse (J := J) (T := T) X F π) :=
    isIso_nested_restricted_pullback_pair_collapse (J := J) (T := T) X F π
  infer_instance

/-- Helper for Lemma 7.17.6: after collapsing the nested restricted pullback source to the common
finite source family, the resulting map to the target finite coproduct is exactly the assembled map
obtained from the pullback projections to each target summand. -/
theorem nested_restricted_pullback_factorization
    {α ι : Type*} [Finite α] (X : ι → Sheaf J (Type (max u v)))
    (F : α → Sheaf J (Type (max u v))) [HasCoproduct X] [HasCoproduct F]
    {T : Set ι} [Finite T] (π : (∐ X) ⟶ ∐ F)
    [∀ a : α, HasCoproduct fun t : T ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun a : α ↦ ∐ fun t : T ↦
      pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)]
    [HasCoproduct fun t : T ↦ X t.1] :
    nested_restricted_pullback_collapse (J := J) (T := T) X F π ≫
        Limits.Sigma.desc (fun t : T ↦ Limits.Sigma.ι X t.1 ≫ π) =
      Limits.Sigma.desc
        (fun a : α ↦
          Limits.Sigma.desc
              (fun t : T ↦
                pullback.snd (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) ≫
            Limits.Sigma.ι F a) := by
  -- Compare the two maps after restricting to each outer and inner coproduct summand.
  apply Limits.Sigma.hom_ext
  intro a
  apply Limits.Sigma.hom_ext
  intro t
  -- On the `(a, t)` summand, both maps reduce to the pullback commutativity relation.
  simp only [nested_restricted_pullback_collapse, Category.assoc, Limits.Sigma.ι_desc_assoc,
    Limits.Sigma.ι_desc]
  simpa [Category.assoc] using
    pullback.condition (f := Limits.Sigma.ι X t.1 ≫ π) (g := Limits.Sigma.ι F a)

/-- Helper for Lemma 7.17.6: an actual finite coproduct of quasi-compact sheaves is
quasi-compact. -/
theorem finite_coproduct_isQuasiCompactObject
    {α : Type*} [Finite α] (F : α → Sheaf J (Type (max u v))) [HasCoproduct F]
    (hF : ∀ a, IsQuasiCompactObject (F a)) :
    IsQuasiCompactObject (∐ F) := by
  classical
  refine ⟨?_⟩
  intro ι X _ π hπ
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let _ : HasColimitsOfShape (Discrete α) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let P : α → ι → Sheaf J (Type (max u v)) :=
    fun a i ↦ pullback (Limits.Sigma.ι X i ≫ π) (Limits.Sigma.ι F a)
  let _ : ∀ a, HasCoproduct (P a) := fun a ↦ by infer_instance
  have hπdesc :
      IsLocallySurjective (Limits.Sigma.desc fun i : ι ↦ Limits.Sigma.ι X i ≫ π) := by
    have hπeq : Limits.Sigma.desc (fun i : ι ↦ Limits.Sigma.ι X i ≫ π) = π := by
      apply Limits.Sigma.hom_ext
      intro i
      simpa using (Limits.Sigma.ι_desc (fun i : ι ↦ Limits.Sigma.ι X i ≫ π) i)
    exact hπeq.symm ▸ hπ
  have hpull :
      ∀ a,
        IsLocallySurjective
          (Limits.Sigma.desc
            fun i : ι ↦ pullback.snd (Limits.Sigma.ι X i ≫ π) (Limits.Sigma.ι F a)) := by
    intro a
    -- Pull back the original locally surjective map along the `a`th target summand.
    exact isLocallySurjective_sigma_desc_pullback_snd (J := J)
      (q := Limits.Sigma.ι F a) X (fun i ↦ Limits.Sigma.ι X i ≫ π) hπdesc
  choose T hT hTsurj using
    fun a ↦ (hF a).finite_subcoproduct
      (P a)
      (Limits.Sigma.desc
        fun i : ι ↦ pullback.snd (Limits.Sigma.ι X i ≫ π) (Limits.Sigma.ι F a))
      (hpull a)
  let T' : Set ι := { i | ∃ a, i ∈ T a }
  have hT' : T'.Finite := by
    -- Only finitely many target summands contribute, and each contributes a finite source subset.
    have hUnion : (⋃ a, T a).Finite := by
      simpa using (Set.finite_univ : (Set.univ : Set α).Finite).biUnion (fun a _ ↦ hT a)
    have hEq : T' = ⋃ a, T a := by
      ext i
      simp [T']
    exact hEq ▸ hUnion
  let _ : Fintype T' := hT'.fintype
  let _ : HasColimitsOfShape (Discrete T') (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let _ : HasColimitsOfShape (Discrete (Σ a : α, T')) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let _ : HasColimitsOfShape (Discrete (T' × α)) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  have hγ :
      ∀ a,
        IsLocallySurjective
          (Limits.Sigma.desc
            fun t : T' ↦ pullback.snd (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) := by
    intro a
    let _ : Fintype (T a) := (hT a).fintype
    let _ : HasColimitsOfShape (Discrete (T a)) (Sheaf J (Type (max u v))) :=
      Sheaf.instHasColimitsOfShape
    -- Enlarge each componentwise witness from `T a` to the common finite source family `T'`.
    have hsubset :
        IsLocallySurjective
          (Limits.Sigma.desc fun i : T' ↦
            Limits.Sigma.ι (P a) i.1 ≫
              Limits.Sigma.desc
                (fun i : ι ↦ pullback.snd (Limits.Sigma.ι X i ≫ π) (Limits.Sigma.ι F a))) := by
      exact
        isLocallySurjective_sigma_desc_of_subset
          (J := J)
          (S := T a) (T := T')
          (hST := fun i hi ↦ ⟨a, hi⟩)
          (X := P a)
          (π := Limits.Sigma.desc
            fun i : ι ↦ pullback.snd (Limits.Sigma.ι X i ≫ π) (Limits.Sigma.ι F a))
          (hS := by simpa [P, Category.assoc] using hTsurj a)
    have hsubset_eq :
        Limits.Sigma.desc
            (fun i : T' ↦
              Limits.Sigma.ι (P a) i.1 ≫
                Limits.Sigma.desc
                  (fun i : ι ↦ pullback.snd (Limits.Sigma.ι X i ≫ π) (Limits.Sigma.ι F a))) =
          Limits.Sigma.desc
            (fun t : T' ↦ pullback.snd (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) := by
      apply Limits.Sigma.hom_ext
      intro t
      have hleft :
          Limits.Sigma.ι (fun i : T' ↦ P a i.1) t ≫
              Limits.Sigma.desc
                (fun i : T' ↦
                  Limits.Sigma.ι (P a) i.1 ≫
                    Limits.Sigma.desc
                      (fun i : ι ↦ pullback.snd (Limits.Sigma.ι X i ≫ π) (Limits.Sigma.ι F a))) =
            pullback.snd (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a) := by
        rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      have hright :
          Limits.Sigma.ι (fun i : T' ↦ P a i.1) t ≫
              Limits.Sigma.desc
                (fun t : T' ↦ pullback.snd (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) =
            pullback.snd (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a) := by
        rw [Limits.Sigma.ι_desc]
      exact hleft.trans hright.symm
    exact hsubset_eq ▸ hsubset
  let Y : α → Sheaf J (Type (max u v)) :=
    fun a ↦ ∐ fun t : T' ↦ pullback (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)
  let _ : HasCoproduct Y := by infer_instance
  let _ : HasCoproduct fun q : Σ a : α, T' ↦
      pullback (Limits.Sigma.ι X q.2.1 ≫ π) (Limits.Sigma.ι F q.1) := by infer_instance
  let _ : HasCoproduct fun p : T' × α ↦
      pullback (Limits.Sigma.ι X p.1.1 ≫ π) (Limits.Sigma.ι F p.2) := by infer_instance
  let κ :
      (∐ Y) ⟶
        ∐ fun t : T' ↦ X t.1 :=
    nested_restricted_pullback_collapse (J := J) (T := T') X F π
  let δ : (∐ fun t : T' ↦ X t.1) ⟶ ∐ F :=
    Limits.Sigma.desc fun t : T' ↦ Limits.Sigma.ι X t.1 ≫ π
  let ρ :
      (∐ Y) ⟶
        ∐ F :=
    Limits.Sigma.desc fun a : α ↦
      Limits.Sigma.desc
          (fun t : T' ↦ pullback.snd (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)) ≫
        Limits.Sigma.ι F a
  have hρ : IsLocallySurjective ρ := by
    -- Reassemble the finitely many componentwise pullback witnesses over the finite target family.
    exact isLocallySurjective_sigma_desc_of_componentwise
      (J := J)
      (Y := Y)
      (F := F)
      (γ := fun a ↦
        Limits.Sigma.desc
          (fun t : T' ↦ pullback.snd (Limits.Sigma.ι X t.1 ≫ π) (Limits.Sigma.ι F a)))
      hγ
  have hκ : IsIso κ := by
    -- The nested pullback source collapses isomorphically to the common finite subcoproduct.
    dsimp [κ]
    exact isIso_nested_restricted_pullback_collapse (J := J) (T := T') X F π
  have hfac : κ ≫ δ = ρ := by
    -- The collapse map followed by the restricted subcoproduct map is the assembled target map.
    simpa [κ, δ, ρ] using nested_restricted_pullback_factorization (J := J) (T := T') X F π
  have hδ : IsLocallySurjective δ := by
    -- Transport local surjectivity from the assembled map `ρ` across the collapse isomorphism.
    rw [Sheaf.isLocallySurjective_iff_epi] at hρ ⊢
    let _ : Epi ρ := hρ
    let _ : Epi κ := by
      let _ : IsIso κ := hκ
      infer_instance
    have hcomp : Epi (κ ≫ δ) := by
      simpa [hfac] using (show Epi ρ from inferInstance)
    exact (epi_comp_iff_of_epi κ δ).1 hcomp
  exact ⟨T', hT', hδ⟩

/-- Lemma 7.17.6: quasi-compact sheaf objects are closed under finite coproducts. -/
instance isQuasiCompactObject_isClosedUnderFiniteCoproducts
    : ObjectProperty.IsClosedUnderFiniteCoproducts
        (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) := by
  refine ⟨fun α _ ↦ ?_⟩
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro Z ⟨G, hG⟩
  -- Replace an arbitrary finite discrete colimit by the canonical finite coproduct presentation.
  let _ : HasColimitsOfShape (Discrete α) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let e : ∐ (fun a : α ↦ G.obj ⟨a⟩) ≅ colimit G := Limits.Sigma.isoColimit G
  -- The coproduct case is exactly the finite-coproduct theorem proved above.
  exact
    isQuasiCompactObject_isClosedUnderIsomorphisms.of_iso e
      (finite_coproduct_isQuasiCompactObject
        (J := J) (F := fun a : α ↦ G.obj ⟨a⟩) (fun a ↦ hG ⟨a⟩))

end Sheaf

section SmallIndex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Index-universe-polymorphic form of `isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc`:
the index type only needs to be small relative to the ambient sheaf universe. The proof shrinks
the index, applies the same-universe comparison, and cancels the reindexing isomorphisms on both
the sheaf and the presheaf side. -/
theorem Sheaf.isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc_of_small.{wι}
    {ι : Type wι} [Small.{max u v} ι] (X : ι → Sheaf J (Type (max u v)))
    {G : Sheaf J (Type (max u v))}
    (α : ∀ i, X i ⟶ G) [HasCoproduct X]
    [HasCoproduct (fun i ↦ (X i).obj)] :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc α) ↔
      Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i ↦ (α i).hom)) := by
  let e : ι ≃ Shrink.{max u v} ι := equivShrink.{max u v} ι
  let X' : Shrink.{max u v} ι → Sheaf J (Type (max u v)) := X ∘ e.symm
  let Xpres : ι → Cᵒᵖ ⥤ Type (max u v) := fun i ↦ (X i).obj
  let Xpres' : Shrink.{max u v} ι → Cᵒᵖ ⥤ Type (max u v) := Xpres ∘ e.symm
  let _ : HasCoproduct X' :=
    Limits.hasCoproduct_of_equiv_of_iso X X' e.symm (fun k ↦ Iso.refl _)
  let _ : HasCoproduct Xpres' :=
    Limits.hasCoproduct_of_equiv_of_iso Xpres Xpres' e.symm (fun k ↦ Iso.refl _)
  let α' : ∀ k : Shrink.{max u v} ι, X' k ⟶ G := fun k ↦ α (e.symm k)
  have hsheaf_fac :
      Limits.Sigma.desc α' = (Limits.Sigma.reindex e.symm X).hom ≫ Limits.Sigma.desc α := by
    apply Limits.Sigma.hom_ext
    intro k
    have h₀ : Limits.Sigma.ι X' k ≫ Limits.Sigma.desc α' = α (e.symm k) := by
      simpa [X', α', e] using (Limits.Sigma.ι_desc α' k)
    have h₁ : α (e.symm k) = Limits.Sigma.ι X (e.symm k) ≫ Limits.Sigma.desc α := by
      simpa using (Limits.Sigma.ι_desc α (e.symm k)).symm
    have h₂ :
        Limits.Sigma.ι X (e.symm k) ≫ Limits.Sigma.desc α =
          Limits.Sigma.ι X' k ≫
            (Limits.Sigma.reindex e.symm X).hom ≫ Limits.Sigma.desc α := by
      simpa [X'] using
        (Limits.Sigma.ι_reindex_hom_assoc (ε := e.symm) (f := X) k
          (Limits.Sigma.desc α)).symm
    exact h₀.trans (h₁.trans h₂)
  have hpres_fac :
      Limits.Sigma.desc (fun k : Shrink.{max u v} ι ↦ (α' k).hom) =
        (Limits.Sigma.reindex e.symm Xpres).hom ≫
          Limits.Sigma.desc (fun i ↦ (α i).hom) := by
    apply Limits.Sigma.hom_ext
    intro k
    have h₀ : Limits.Sigma.ι Xpres' k ≫
        Limits.Sigma.desc (fun k : Shrink.{max u v} ι ↦ (α' k).hom) = (α (e.symm k)).hom := by
      simpa [Xpres', α', e] using
        (Limits.Sigma.ι_desc (fun k : Shrink.{max u v} ι ↦ (α' k).hom) k)
    have h₁ : (α (e.symm k)).hom =
        Limits.Sigma.ι Xpres (e.symm k) ≫ Limits.Sigma.desc (fun i ↦ (α i).hom) := by
      simpa using (Limits.Sigma.ι_desc (fun i ↦ (α i).hom) (e.symm k)).symm
    have h₂ :
        Limits.Sigma.ι Xpres (e.symm k) ≫ Limits.Sigma.desc (fun i ↦ (α i).hom) =
          Limits.Sigma.ι Xpres' k ≫
            (Limits.Sigma.reindex e.symm Xpres).hom ≫
              Limits.Sigma.desc (fun i ↦ (α i).hom) := by
      simpa [Xpres'] using
        (Limits.Sigma.ι_reindex_hom_assoc (ε := e.symm) (f := Xpres) k
          (Limits.Sigma.desc (fun i ↦ (α i).hom))).symm
    exact h₀.trans (h₁.trans h₂)
  have hsh :
      Sheaf.IsLocallySurjective (Limits.Sigma.desc α) ↔
        Sheaf.IsLocallySurjective (Limits.Sigma.desc α') := by
    rw [Sheaf.isLocallySurjective_iff_epi, Sheaf.isLocallySurjective_iff_epi]
    constructor
    · intro h
      rw [hsheaf_fac]
      exact epi_comp _ _
    · intro h
      rw [hsheaf_fac] at h
      exact epi_of_epi (Limits.Sigma.reindex e.symm X).hom _
  have hpre :
      Presheaf.IsLocallySurjective J (Limits.Sigma.desc (fun i ↦ (α i).hom)) ↔
        Presheaf.IsLocallySurjective J
          (Limits.Sigma.desc (fun k : Shrink.{max u v} ι ↦ (α' k).hom)) := by
    rw [hpres_fac]
    exact (Presheaf.comp_isLocallySurjective_iff J
      (Limits.Sigma.reindex e.symm Xpres).hom
      (Limits.Sigma.desc (fun i ↦ (α i).hom))).symm
  rw [hsh, hpre]
  exact Sheaf.isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc
    (J := J) X' α'

end SmallIndex

end CategoryTheory
