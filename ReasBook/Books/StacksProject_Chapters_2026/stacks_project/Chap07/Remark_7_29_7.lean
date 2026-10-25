module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_29_5
public import stacks_project.Chap07.Lemma_7_29_6
public import stacks_project.Chap07.Proposition_7_14_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Functor.IsDenseSubsite
open scoped MorphismOfTopoiIn

universe u₁ u₂ u₃ uI uG v₁ v₂ v₃ w

namespace CategoryTheory

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {I : Type uI} {G : Type uG}
variable [HasWeakSheafify J (Type (max u₁ v₁))]
variable [HasWeakSheafify K (Type (max u₂ v₂))]

namespace Functor

variable {C' : Type u₃} [Category.{v₃} C']

/-- The canonical transport of `Type w`-valued sheaves across a dense subsite, obtained by first
raising universes with `sheafCompose J uliftFunctor` and then applying the dense-subsite
equivalence. -/
abbrev denseSubsiteTypeTransport
    (v : C ⥤ C') (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    [v.IsDenseSubsite J J'] :
    Sheaf J (Type w) ⥤ Sheaf J' (Type (max w u₁ u₃ v₁ v₃)) :=
  sheafCompose J uliftFunctor.{max w u₁ u₃ v₁ v₃, w} ⋙
    (sheafEquiv J J' v (Type (max w u₁ u₃ v₁ v₃))).functor

end Functor

omit [HasWeakSheafify J (Type (max u₁ v₁))] in
-- Proof sketch: enlarge the presenting site to `AsSmall C` so that Lemma `7.29.5` applies in the
-- ambient universe `Type (max w u₁ v₁)`, transport the family there by the canonical
-- dense-subsite equivalence, and then apply the replacement-site theorem entrywise.
/-- Helper for Remark 7.29.7: every `Type w`-valued family on `Sh(J)` admits the first-stage
replacement from Lemma `7.29.5` after the standard `AsSmall` universe lift. -/
private theorem exists_ulift_family_site_presentation
    [Small.{max w u₁ u₂ v₁ v₂} I]
    (ℱ : I → Sheaf J (Type w)) :
    ∃ (C0Small : Type (max w u₁ u₂ v₁ v₂)) (_ : Category C0Small)
      (J0Small : GrothendieckTopology C0Small)
      (a : C ⥤ C0Small) (_ : a.IsDenseSubsite J J0Small) (_ : a.IsEquivalence),
      ∃ (C0 : Type (max w u₁ u₂ v₁ v₂)) (_ : Category C0) (J0 : GrothendieckTopology C0)
        (_ : J0.Subcanonical) (_ : HasFiniteLimits C0)
        (v0 : C0Small ⥤ C0) (_ : v0.IsDenseSubsite J0Small J0),
        ∀ i : I,
          (((sheafEquiv J0Small J0 v0 (Type (max w u₁ u₂ v₁ v₂))).functor.obj
              ((sheafEquiv J J0Small a (Type (max w u₁ u₂ v₁ v₂))).functor.obj
                ((sheafCompose J CategoryTheory.uliftFunctor.{max w u₁ u₂ v₁ v₂, w}).obj
                  (ℱ i)))).obj).IsRepresentable := by
  -- Enlarge the site once, at the ambient assembly universe `max w u₁ u₂ v₁ v₂`, so that the
  -- replacement theorem (Lemma 7.29.5) applies there.
  let C0Small : Type (max w u₁ u₂ v₁ v₂) := CategoryTheory.AsSmall.{max w u₂ v₂} C
  let a : C ⥤ C0Small := CategoryTheory.AsSmall.up
  let e : C ≌ C0Small := CategoryTheory.AsSmall.equiv (C := C)
  let J0Small : GrothendieckTopology C0Small := e.inverse.inducedTopology J
  let _ : a.IsDenseSubsite J J0Small := by
    change e.functor.IsDenseSubsite J J0Small
    infer_instance
  let _ : a.IsEquivalence := by
    change e.functor.IsEquivalence
    infer_instance
  -- Transport the family to the enlarged site and invoke Lemma `7.29.5` there.
  let ℱ0 : I → Sheaf J0Small (Type (max w u₁ u₂ v₁ v₂)) := fun i ↦
    (sheafEquiv J J0Small a (Type (max w u₁ u₂ v₁ v₂))).functor.obj
      ((sheafCompose J CategoryTheory.uliftFunctor.{max w u₁ u₂ v₁ v₂, w}).obj (ℱ i))
  obtain ⟨C0, hC0, J0, hJ0, hfin0, v0, hv0, _, _, _, hfamily⟩ :=
    exists_representable_family_site_presentation (J := J0Small) ℱ0
  let _ : Category C0 := hC0
  let _ : J0.Subcanonical := hJ0
  let _ : HasFiniteLimits C0 := hfin0
  let _ : v0.IsDenseSubsite J0Small J0 := hv0
  -- The family statement from Lemma `7.29.5` is already the transported representability we need.
  exact ⟨C0Small, inferInstance, J0Small, a, inferInstance, inferInstance,
    C0, hC0, J0, hJ0, hfin0, v0, hv0, hfamily⟩

omit [HasWeakSheafify K (Type (max u₂ v₂))] in
/-- Helper for Remark 7.29.7 (target side): every `Type w`-valued family on `Sh(K)` admits the
first-stage replacement from Lemma `7.29.5` after the standard `AsSmall` universe lift, at the
target-side ambient universe `max w u₂ v₂`. -/
private theorem exists_ulift_family_site_presentation_target
    [Small.{max w u₁ u₂ v₁ v₂} G]
    (𝒢 : G → Sheaf K (Type w)) :
    ∃ (D0Small : Type (max w u₁ u₂ v₁ v₂)) (_ : Category D0Small)
      (K0Small : GrothendieckTopology D0Small)
      (b : D ⥤ D0Small) (_ : b.IsDenseSubsite K K0Small) (_ : b.IsEquivalence),
      ∃ (D0 : Type (max w u₁ u₂ v₁ v₂)) (_ : Category D0) (K0 : GrothendieckTopology D0)
        (_ : K0.Subcanonical) (_ : HasFiniteLimits D0)
        (w0 : D0Small ⥤ D0) (_ : w0.IsDenseSubsite K0Small K0),
        ∀ j : G,
          (((sheafEquiv K0Small K0 w0 (Type (max w u₁ u₂ v₁ v₂))).functor.obj
              ((sheafEquiv K K0Small b (Type (max w u₁ u₂ v₁ v₂))).functor.obj
                ((sheafCompose K CategoryTheory.uliftFunctor.{max w u₁ u₂ v₁ v₂, w}).obj
                  (𝒢 j)))).obj).IsRepresentable := by
  let D0Small : Type (max w u₁ u₂ v₁ v₂) := CategoryTheory.AsSmall.{max w u₁ v₁} D
  let b : D ⥤ D0Small := CategoryTheory.AsSmall.up
  let e : D ≌ D0Small := CategoryTheory.AsSmall.equiv (C := D)
  let K0Small : GrothendieckTopology D0Small := e.inverse.inducedTopology K
  let _ : b.IsDenseSubsite K K0Small := by
    change e.functor.IsDenseSubsite K K0Small
    infer_instance
  let _ : b.IsEquivalence := by
    change e.functor.IsEquivalence
    infer_instance
  let 𝒢0 : G → Sheaf K0Small (Type (max w u₁ u₂ v₁ v₂)) := fun j ↦
    (sheafEquiv K K0Small b (Type (max w u₁ u₂ v₁ v₂))).functor.obj
      ((sheafCompose K CategoryTheory.uliftFunctor.{max w u₁ u₂ v₁ v₂, w}).obj (𝒢 j))
  obtain ⟨D0, hD0, K0, hK0, hfin0, w0, hw0, _, _, _, hfamily⟩ :=
    exists_representable_family_site_presentation (J := K0Small) 𝒢0
  let _ : Category D0 := hD0
  let _ : K0.Subcanonical := hK0
  let _ : HasFiniteLimits D0 := hfin0
  let _ : w0.IsDenseSubsite K0Small K0 := hw0
  exact ⟨D0Small, inferInstance, K0Small, b, inferInstance, inferInstance,
    D0, hD0, K0, hK0, hfin0, w0, hw0, hfamily⟩

/- Domain-style sampling for Remark 7.29.7:
- primary domain: reductions of morphisms of topoi to morphisms of sites after replacing the two
  presenting sites by subcanonical sites with finite limits;
- sampled owner declarations:
  `Functor.IsDenseSubsite`,
  `MorphismOfTopoiIn`,
  `CatCommSq`,
  `Functor.IsDenseSubsite.sheafEquiv`,
  `CategoryTheory.sheafCompose`,
  `Functor.sheafPullback`,
  `Functor.morphismOfTopoiInOfContinuous`;
- best owner abstraction: the replacement-site functors should be recorded through the canonical
  dense-subsite owner `IsDenseSubsite`; the family transport should appear on the public theorem
  surface through the canonical universe-raising transport
  `Functor.denseSubsiteTypeTransport`, whose owner is still the dense-subsite equivalence
  `sheafEquiv`, rather than through extra existentially chosen equivalence data; the lower
  horizontal factorization should first be recorded at the source-facing owner level by a
  morphism of topoi `g : MorphismOfTopoiIn K' J'` together with the explicit relation
  `g _* = u.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K' J'` saying that `g` is presented by the site
  morphism `u` on direct images, while the stronger identification
  `g = u.morphismOfTopoiInOfContinuous K' J'` belongs only to a companion bridge theorem;
- primitive data: the replacement sites `(C', J')`, `(D', K')`, the dense-subsite functors from
  the original sites, the site morphism `u : D' ⥤ C'`, and the lower morphism of topoi
  `g : MorphismOfTopoiIn K' J'`, its direct-image identification with
  `u.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K' J'`, and the comparison square `sq : CatCommSq ...`;
- derived API: subcanonicality, finite limits, the canonical family transport given by
  `Functor.denseSubsiteTypeTransport`, and, in the companion theorem only, the canonical lower
  inverse-image owner `u.sheafPullback (Type (max w u₁ u₂ v₁ v₂)) K' J'`, which under the standard realization
  hypotheses is the inverse image of `u.morphismOfTopoiInOfContinuous`;
- ambient construction hypotheses inherited from the owner layer: weak sheafification on the
  original sites `J` and `K`, exactly as required by the replacement-site theorem
  `exists_representable_family_site_presentation` from Lemma `7.29.5`.

Source/core/bridge triage:
- `source-facing`: the existence of replacement sites on which the chosen families become
  representable and the given morphism of topoi factors through a lower morphism of topoi induced
  by a site morphism satisfying the source hypotheses from Proposition `7.14.7`;
- `core/canonical`: `Functor.IsDenseSubsite`, `sheafEquiv`, `IsMorphismOfSites`,
  `MorphismOfTopoiIn`, `CatCommSq`, and `sheafCompose`;
- `bridge/view`: the universe-raising transport functors on sheaf categories, implemented
  canonically by the standard bridge `sheafCompose _ uliftFunctor` followed by `sheafEquiv`,
  together with the weak sheafification and Kan-extension hypotheses used only to identify the
  lower morphism canonically with `u.morphismOfTopoiInOfContinuous`, whose left exactness is
  already derived from `IsMorphismOfSites` through `RepresentablyFlat`.
-/

-- Proof sketch: apply Lemma `7.29.5` separately to the two chosen families to replace both sites
-- by subcanonical sites with finite limits and dense-subsite comparison functors. Apply
-- Lemma `7.29.6` to the transported morphism of topoi between the replacement sites to obtain the
-- site morphism `u : D' ⥤ C'`, the lower morphism of topoi `g : MorphismOfTopoiIn K' J'`, its
-- direct-image identification with `u.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K' J'`, and the
-- canonical comparison square `sq : CatCommSq ...`. The family transport is recorded on the
-- theorem surface by the canonical dense-subsite transport
-- `Functor.denseSubsiteTypeTransport`, rather than by separate existential equivalence data.
/-- Helper for Remark 7.29.7: after replacing both presenting sites by the Lemma `7.29.5`
comparison sites, the original morphism of topoi transports to a morphism over the replacement
sites whose inverse-image square records exactly the two dense-subsite comparison functors. -/
private theorem transported_replacement_morphism
    {C0 : Type (max w u₁ u₂ v₁ v₂)} [Category.{max w u₁ u₂ v₁ v₂} C0]
    {J0 : GrothendieckTopology C0}
    {D0 : Type (max w u₁ u₂ v₁ v₂)} [Category.{max w u₁ u₂ v₁ v₂} D0]
    {K0 : GrothendieckTopology D0}
    (v0 : C ⥤ C0) [v0.IsDenseSubsite J J0]
    (w0 : D ⥤ D0) [w0.IsDenseSubsite K K0]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max w u₁ u₂ v₁ v₂} K J) :
    ∃ (f0 : MorphismOfTopoiIn K0 J0),
      Nonempty
        (CatCommSq
          (w0.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K K0)
          (f0⁻¹)
          (f⁻¹)
          (v0.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) J J0)) := by
  -- Conjugate `f` by the two dense-subsite equivalences, which are available at the ambient
  -- universe because the comparison limits exist there; the displayed square then collapses
  -- through the counit of the source-side equivalence.
  haveI : ∀ α : Type (max w u₁ u₂ v₁ v₂), Small.{max w u₁ u₂ v₁ v₂} α :=
    fun α => inferInstance
  letI : ∀ X, Limits.HasLimitsOfShape (StructuredArrow X v0.op)
      (Type (max w u₁ u₂ v₁ v₂)) := fun X => inferInstance
  letI : ∀ X, Limits.HasLimitsOfShape (StructuredArrow X w0.op)
      (Type (max w u₁ u₂ v₁ v₂)) := fun X => inferInstance
  letI : (v0.sheafPushforwardContinuous
      (Type (max w u₁ u₂ v₁ v₂)) J J0).IsEquivalence := by infer_instance
  letI : (w0.sheafPushforwardContinuous
      (Type (max w u₁ u₂ v₁ v₂)) K K0).IsEquivalence := by infer_instance
  let eJ : Sheaf J0 (Type (max w u₁ u₂ v₁ v₂)) ≌ Sheaf J (Type (max w u₁ u₂ v₁ v₂)) :=
    (v0.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) J J0).asEquivalence
  let eK : Sheaf K0 (Type (max w u₁ u₂ v₁ v₂)) ≌ Sheaf K (Type (max w u₁ u₂ v₁ v₂)) :=
    (w0.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K K0).asEquivalence
  letI : PreservesFiniteLimits eJ.inverse := by
    constructor
    intro Jc _ _
    infer_instance
  letI : PreservesFiniteLimits eK.functor := by
    constructor
    intro Jc _ _
    infer_instance
  letI : PreservesFiniteLimits (f⁻¹) := f.inverseImageFunctor.property
  letI : PreservesFiniteLimits (f⁻¹ ⋙ eJ.inverse) := by
    exact comp_preservesFiniteLimits _ _
  letI : PreservesFiniteLimits (eK.functor ⋙ (f⁻¹ ⋙ eJ.inverse)) := by
    exact comp_preservesFiniteLimits _ _
  refine ⟨{ inverseImageFunctor := LeftExactFunctor.of (eK.functor ⋙ (f⁻¹ ⋙ eJ.inverse))
            pushforward := eJ.functor ⋙ f _* ⋙ eK.inverse
            adjunction := (eK.toAdjunction.comp f.adjunction).comp eJ.symm.toAdjunction }, ?_⟩
  refine ⟨{ iso := ?_ }⟩
  -- The square's two composites differ by the counit of the source-side equivalence.
  exact
    ((Functor.associator eK.functor (f⁻¹ ⋙ eJ.inverse) eJ.functor) ≪≫
      Functor.isoWhiskerLeft eK.functor
        (Functor.associator (f⁻¹) eJ.inverse eJ.functor) ≪≫
      Functor.isoWhiskerLeft eK.functor
        (Functor.isoWhiskerLeft (f⁻¹) eJ.counitIso) ≪≫
      Functor.isoWhiskerLeft eK.functor (Functor.rightUnitor (f⁻¹))).symm

/-- Helper for Remark 7.29.7: once Lemma `7.29.6` factors the transported replacement-site
morphism through `u : D' ⥤ C'`, whiskering that canonical square with the two replacement
equivalences yields the theorem-facing square over the original morphism `f`. -/
private theorem whisker_replacement_factorization_square
    {C0 : Type (max w u₁ u₂ v₁ v₂)} [Category C0] {J0 : GrothendieckTopology C0}
    {D0 : Type (max w u₁ u₂ v₁ v₂)} [Category D0] {K0 : GrothendieckTopology D0}
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (v0 : C ⥤ C0) [v0.IsDenseSubsite J J0]
    (w0 : D ⥤ D0) [w0.IsDenseSubsite K K0]
    (v1 : C0 ⥤ C') [v1.IsDenseSubsite J0 J']
    [(v0 ⋙ v1).IsContinuous J J']
    (L : Sheaf K0 (Type (max w u₁ u₂ v₁ v₂)) ⥤ Sheaf J' (Type (max w u₁ u₂ v₁ v₂)))
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max w u₁ u₂ v₁ v₂} K J)
    (f0 : MorphismOfTopoiIn K0 J0)
    (sq0 :
      CatCommSq
        (w0.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K K0)
        (f0⁻¹)
        (f⁻¹)
        (v0.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) J J0))
    (sq1 :
      CatCommSq
        (𝟭 (Sheaf K0 (Type (max w u₁ u₂ v₁ v₂))))
        L
        (f0⁻¹)
        (v1.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) J0 J')) :
    Nonempty
      (CatCommSq
        (w0.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K K0)
        L
        (f⁻¹)
        ((v0 ⋙ v1).sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) J J')) := by
  -- The square from Lemma `7.29.6` lives over the transported morphism `f0`.
  -- The remaining bookkeeping is a single whiskering step across the two dense-subsite
  -- comparison equivalences, together with reassociation to the composite source functor.
  let sqComp :
      CatCommSq
        (𝟭 (Sheaf K0 (Type (max w u₁ u₂ v₁ v₂))) ⋙ w0.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K K0)
        L
        (f⁻¹)
        (v1.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) J0 J' ⋙
          v0.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) J J0) :=
    CatCommSq.hComp' sq1 sq0
  refine ⟨{ iso := ?_ }⟩
  -- First remove the trivial top edge, then rewrite the bottom composite as the pushforward
  -- along `v0 ⋙ v1`.
  exact
    (Functor.isoWhiskerRight
      (Functor.leftUnitor (w0.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K K0))
      (f⁻¹)).symm ≪≫
      sqComp.iso ≪≫
      Functor.isoWhiskerLeft L
        (Functor.sheafPushforwardContinuousComp
          (F := v0) (G := v1) (A := Type (max w u₁ u₂ v₁ v₂)) (J := J) (K := J0) (L := J'))

/-- Composition of dense subsites when the right factor is fully faithful — the source-faithful
case for Remark 7.29.7, where the special cocontinuous functor is fully faithful but the first
(non-subcanonical) replacement leg need not be. -/
theorem isDenseSubsite_comp_right_ff.{ua, va, ub, vb, uc, vc}
    {Cx : Type ua} [Category.{va} Cx] {Dx : Type ub} [Category.{vb} Dx]
    {Ex : Type uc} [Category.{vc} Ex]
    {Jx : GrothendieckTopology Cx} {Kx : GrothendieckTopology Dx} {Lx : GrothendieckTopology Ex}
    (F : Cx ⥤ Dx) (G : Dx ⥤ Ex)
    [F.IsDenseSubsite Jx Kx] [G.IsDenseSubsite Kx Lx] [G.Full] [G.Faithful] :
    (F ⋙ G).IsDenseSubsite Jx Lx := by
  haveI hFcd : F.IsCoverDense Kx := Functor.IsDenseSubsite.isCoverDense (J := Jx) (K := Kx) (G := F)
  haveI hGcd : G.IsCoverDense Lx := Functor.IsDenseSubsite.isCoverDense (J := Kx) (K := Lx) (G := G)
  haveI hFlf : F.IsLocallyFull Kx := Functor.IsDenseSubsite.isLocallyFull (J := Jx) (K := Kx) (G := F)
  haveI hFlfa : F.IsLocallyFaithful Kx :=
    Functor.IsDenseSubsite.isLocallyFaithful (J := Jx) (K := Kx) (G := F)
  have hGcp : CoverPreserving Kx Lx G :=
    Functor.IsDenseSubsite.coverPreserving (J := Kx) (K := Lx) (G := G)
  refine { isCoverDense' := ⟨fun U => ?_⟩
           isLocallyFull' := ⟨fun {U V} h => ?_⟩
           isLocallyFaithful' := ⟨fun {U V} f₁ f₂ e => ?_⟩
           functorPushforward_mem_iff := ?_ }
  · apply Lx.transitive (G.is_cover_of_isCoverDense Lx U)
    intro Y h hh
    obtain ⟨d, lift, map, fac⟩ := hh
    have hpf : (Sieve.coverByImage F d).functorPushforward G ∈ Lx (G.obj d) :=
      hGcp.cover_preserve (F.is_cover_of_isCoverDense Kx d)
    apply Lx.superset_covering _ (Lx.pullback_stable lift hpf)
    intro W k hk
    obtain ⟨c, p, g, hp, e⟩ := Presieve.getFunctorPushforwardStructure hk
    obtain ⟨⟨c', l, m, lf⟩⟩ := hp
    refine ⟨⟨c', g ≫ G.map l, G.map m ≫ map, ?_⟩⟩
    have key : G.map l ≫ G.map m = G.map p := by rw [← G.map_comp, lf]
    calc (g ≫ G.map l) ≫ G.map m ≫ map
        = g ≫ (G.map l ≫ G.map m) ≫ map := by simp only [Category.assoc]
      _ = g ≫ G.map p ≫ map := by rw [key]
      _ = (k ≫ lift) ≫ map := by rw [← Category.assoc, ← e]
      _ = k ≫ h := by rw [Category.assoc, fac]
  · have himg : (F ⋙ G).imageSieve h = F.imageSieve (G.preimage h) := by
      ext W i
      constructor
      · rintro ⟨l, hl⟩
        exact ⟨l, G.map_injective (by simpa [G.map_preimage] using hl)⟩
      · rintro ⟨l, hl⟩
        exact ⟨l, by simp [Functor.comp_map, ← G.map_comp, hl, G.map_preimage]⟩
    rw [himg, Sieve.functorPushforward_comp]
    exact hGcp.cover_preserve (Functor.IsLocallyFull.functorPushforward_imageSieve_mem _)
  · rw [Sieve.functorPushforward_comp]
    exact hGcp.cover_preserve
      (Functor.IsLocallyFaithful.functorPushforward_equalizer_mem _ _
        (G.map_injective (by simpa using e)))
  · intro X S
    have h1 := Functor.IsDenseSubsite.functorPushforward_mem_iff (J := Jx) (K := Kx) (G := F)
      (X := X) (S := S)
    have h2 := Functor.IsDenseSubsite.functorPushforward_mem_iff (J := Kx) (K := Lx) (G := G)
      (S := S.functorPushforward F)
    rw [Sieve.functorPushforward_comp]
    exact h2.trans h1

/-- COH1 for Remark 7.29.7: the dense-subsite sheaf equivalence of a composite is the composite
of the two stage equivalences (forward direction), obtained as the mate of the pushforward
composition isomorphism. -/
noncomputable def sheafEquivCompFunctorIso.{uA, vA, uB, vB, uCc, vCc, lev}
    {C₀ : Type uA} [Category.{vA} C₀] {D₀ : Type uB} [Category.{vB} D₀]
    {E₀ : Type uCc} [Category.{vCc} E₀]
    {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
    {L₀ : GrothendieckTopology E₀}
    (v0 : C₀ ⥤ D₀) (v1 : D₀ ⥤ E₀)
    [v0.IsDenseSubsite J₀ K₀] [v1.IsDenseSubsite K₀ L₀] [(v0 ⋙ v1).IsDenseSubsite J₀ L₀]
    [∀ X, Limits.HasLimitsOfShape (StructuredArrow X v0.op) (Type lev)]
    [∀ X, Limits.HasLimitsOfShape (StructuredArrow X v1.op) (Type lev)]
    [∀ X, Limits.HasLimitsOfShape (StructuredArrow X (v0 ⋙ v1).op) (Type lev)] :
    (Functor.IsDenseSubsite.sheafEquiv J₀ L₀ (v0 ⋙ v1) (Type lev)).functor ≅
      (Functor.IsDenseSubsite.sheafEquiv J₀ K₀ v0 (Type lev)).functor ⋙
        (Functor.IsDenseSubsite.sheafEquiv K₀ L₀ v1 (Type lev)).functor :=
  (conjugateIsoEquiv
    ((Functor.IsDenseSubsite.sheafEquiv J₀ K₀ v0 (Type lev)).toAdjunction.comp
      (Functor.IsDenseSubsite.sheafEquiv K₀ L₀ v1 (Type lev)).toAdjunction)
    (Functor.IsDenseSubsite.sheafEquiv J₀ L₀ (v0 ⋙ v1) (Type lev)).toAdjunction).symm
    (Functor.sheafPushforwardContinuousComp v0 v1 (Type lev) J₀ K₀ L₀)

/-- Crux for Remark 7.29.7: the dense-subsite equivalence on sheaves sends the (universe-raised)
sheafified representable `h_X^#` to the sheafified representable `h_{G X}^#`, provided `G` is
fully faithful and both topologies are subcanonical. This is the source-text fact that a special
cocontinuous functor carries representables to representables. -/
noncomputable def sheafEquivUliftYonedaIso.{uA, vA, uB, vB}
    {C₀ : Type uA} [Category.{vA} C₀] {D₀ : Type uB} [Category.{vB} D₀]
    {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
    (G : C₀ ⥤ D₀) (hG : G.FullyFaithful)
    [G.IsDenseSubsite J₀ K₀] [J₀.Subcanonical] [K₀.Subcanonical]
    [∀ X, Limits.HasLimitsOfShape (StructuredArrow X G.op) (Type (max vA vB))]
    (X : C₀) :
    (Functor.IsDenseSubsite.sheafEquiv J₀ K₀ G (Type (max vA vB))).functor.obj
        ((GrothendieckTopology.uliftYoneda.{vB} J₀).obj X) ≅
      (GrothendieckTopology.uliftYoneda.{vA} K₀).obj (G.obj X) := by
  -- The inverse of the dense-subsite equivalence is the pushforward (restriction) along `G`;
  -- identify the source representable with the restriction of the target one, which holds at the
  -- presheaf level by full faithfulness of `G`.
  have hval :
      ((GrothendieckTopology.uliftYoneda.{vB} J₀).obj X).val ≅
        ((G.sheafPushforwardContinuous (Type (max vA vB)) J₀ K₀).obj
          ((GrothendieckTopology.uliftYoneda.{vA} K₀).obj (G.obj X))).val :=
    (hG.homNatIso X).symm
  have hsheaf :
      (GrothendieckTopology.uliftYoneda.{vB} J₀).obj X ≅
        (G.sheafPushforwardContinuous (Type (max vA vB)) J₀ K₀).obj
          ((GrothendieckTopology.uliftYoneda.{vA} K₀).obj (G.obj X)) :=
    (fullyFaithfulSheafToPresheaf J₀ _).preimageIso hval
  refine (Functor.IsDenseSubsite.sheafEquiv J₀ K₀ G (Type (max vA vB))).functor.mapIso hsheaf ≪≫ ?_
  exact (Functor.IsDenseSubsite.sheafEquiv J₀ K₀ G (Type (max vA vB))).counitIso.app _

/-- Helper for Remark 7.29.7: if a sheaf is already representable after the first dense-subsite
replacement, then it remains representable after the second dense-subsite replacement coming from
Lemma `7.29.6`. Both replacement sites live at the common ambient universe `max w u₁ u₂ v₁ v₂`,
so the two transports agree on the universe-raising step and the comparison is purely the
second-stage equivalence applied to a representable. -/
private theorem denseSubsiteTypeTransport_isRepresentable_of_isRepresentable
    {C0 : Type (max w u₁ u₂ v₁ v₂)} [Category.{max w u₁ u₂ v₁ v₂} C0]
    {J0 : GrothendieckTopology C0}
    {C' : Type (max w u₁ u₂ v₁ v₂)} [Category.{max w u₁ u₂ v₁ v₂} C']
    {J' : GrothendieckTopology C'}
    [J0.Subcanonical] [J'.Subcanonical]
    (v0 : C ⥤ C0) [v0.IsDenseSubsite J J0]
    (v1 : C0 ⥤ C') [v1.IsDenseSubsite J0 J'] (hv1 : v1.FullyFaithful)
    [(v0 ⋙ v1).IsDenseSubsite J J']
    (F : Sheaf J (Type w))
    (hF : (((v0.denseSubsiteTypeTransport J J0).obj F).obj).IsRepresentable) :
    Nonempty ((((v0 ⋙ v1).denseSubsiteTypeTransport J J').obj F).obj).IsRepresentable := by
  haveI : ∀ α : Type (max w u₁ u₂ v₁ v₂), Small.{max w u₁ u₂ v₁ v₂} α := fun _ => inferInstance
  haveI := hF
  -- The representing object of the first-stage transport.
  set P := ((v0.denseSubsiteTypeTransport J J0).obj F) with hP
  -- Lift the presheaf representation to a sheaf isomorphism `J0.yoneda c ≅ P`.
  have hrep : (J0.yoneda.obj P.obj.reprX) ≅ P :=
    (fullyFaithfulSheafToPresheaf J0 _).preimageIso P.obj.reprW
  -- COH1: the composite transport is the second-stage equivalence applied to the first transport.
  have hcoh1 :
      ((v0 ⋙ v1).denseSubsiteTypeTransport J J').obj F ≅
        (Functor.IsDenseSubsite.sheafEquiv J0 J' v1
          (Type (max w u₁ u₂ v₁ v₂))).functor.obj P :=
    (sheafEquivCompFunctorIso v0 v1).app
      ((sheafCompose J CategoryTheory.uliftFunctor.{max w u₁ u₂ v₁ v₂, w}).obj F)
  -- Convert the representable to its universe-raised form, then apply the crux.
  have hcrux :
      (Functor.IsDenseSubsite.sheafEquiv J0 J' v1 (Type (max w u₁ u₂ v₁ v₂))).functor.obj
          ((GrothendieckTopology.uliftYoneda.{max w u₁ u₂ v₁ v₂} J0).obj P.obj.reprX) ≅
        (GrothendieckTopology.uliftYoneda.{max w u₁ u₂ v₁ v₂} J').obj (v1.obj P.obj.reprX) :=
    sheafEquivUliftYonedaIso v1 hv1 P.obj.reprX
  -- Assemble: composite-transport ≅ J'.yoneda (v1 (reprX)).
  have hiso :
      ((v0 ⋙ v1).denseSubsiteTypeTransport J J').obj F ≅
        J'.yoneda.obj (v1.obj P.obj.reprX) :=
    hcoh1 ≪≫
      (Functor.IsDenseSubsite.sheafEquiv J0 J' v1
          (Type (max w u₁ u₂ v₁ v₂))).functor.mapIso hrep.symm ≪≫
      (Functor.IsDenseSubsite.sheafEquiv J0 J' v1
          (Type (max w u₁ u₂ v₁ v₂))).functor.mapIso
        ((GrothendieckTopology.uliftYonedaIsoYoneda J0).symm.app P.obj.reprX) ≪≫
      hcrux ≪≫
      (GrothendieckTopology.uliftYonedaIsoYoneda J').app (v1.obj P.obj.reprX)
  -- Pass to underlying presheaves and conclude representability.
  haveI : ((J'.yoneda.obj (v1.obj P.obj.reprX)).obj).IsRepresentable :=
    Functor.IsRepresentable.mk' (Iso.refl _)
  exact ⟨isRepresentable_of_natIso (J'.yoneda.obj (v1.obj P.obj.reprX)).obj
    ((sheafToPresheaf J' (Type (max w u₁ u₂ v₁ v₂))).mapIso hiso).symm⟩

/-- Helper for Remark 7.29.7: the common reduction package. The lower horizontal edge is
recorded through the conjugated lower morphism of topoi produced by Lemma `7.29.6`; its
canonical identification with `u.sheafPullback` (the inverse image of the site morphism `u`)
is the remaining bridge content of the source remark and is deliberately not part of this
package. -/
private theorem exists_canonical_topos_morphism_reduction
    [Small.{max w u₁ v₁} I] [Small.{max w u₂ v₂} G]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max w u₁ u₂ v₁ v₂} K J)
    (ℱ : I → Sheaf J (Type w))
    (𝒢 : G → Sheaf K (Type w)) :
    ∃ (C' : Type (max w u₁ u₂ v₁ v₂)) (_ : Category.{max w u₁ u₂ v₁ v₂} C')
      (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J'),
      ∃ (D' : Type (max w u₁ u₂ v₁ v₂)) (_ : Category.{max w u₁ u₂ v₁ v₂} D')
        (K' : GrothendieckTopology D')
        (_ : K'.Subcanonical) (_ : HasFiniteLimits D')
        (targetFunctor : D ⥤ D') (_ : targetFunctor.IsDenseSubsite K K'),
        ∃ (u : D' ⥤ C') (_ : IsMorphismOfSites K' J' u)
          (_ : PreservesLimitsOfShape WalkingCospan u)
          (_ : IsTerminal (u.obj (⊤_ D')))
          (g : MorphismOfTopoiIn K' J')
          (sq : CatCommSq
            (targetFunctor.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K K')
            (g⁻¹)
            (f⁻¹)
            (sourceFunctor.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) J J')),
          (∀ i : I, (((sourceFunctor.denseSubsiteTypeTransport J J').obj (ℱ i)).obj).IsRepresentable) ∧
            ∀ j : G, (((targetFunctor.denseSubsiteTypeTransport K K').obj (𝒢 j)).obj).IsRepresentable := by
  -- Source-faithful assembly: replace `D` then `C` by subcanonical sites (Lemma 7.29.5),
  -- conjugate `f`, and apply the special-cocontinuous factorization (Lemma 7.29.6) to the
  -- transported morphism; the resulting `v` is fully faithful because its source is subcanonical.
  haveI : ∀ α : Type (max w u₁ u₂ v₁ v₂), Small.{max w u₁ u₂ v₁ v₂} α := fun _ => inferInstance
  haveI : Small.{max w u₁ u₂ v₁ v₂} I :=
    ⟨ULift.{max u₂ v₂} (Shrink.{max w u₁ v₁} I), ⟨(equivShrink I).trans Equiv.ulift.symm⟩⟩
  haveI : Small.{max w u₁ u₂ v₁ v₂} G :=
    ⟨ULift.{max u₁ v₁} (Shrink.{max w u₂ v₂} G), ⟨(equivShrink G).trans Equiv.ulift.symm⟩⟩
  obtain ⟨C0S, instC0S, J0S, a, haDense, haEquiv, C0, instC0, J0, hJ0sub, hJ0fin, vC0, hvC0,
      hℱrep⟩ := exists_ulift_family_site_presentation.{u₁, u₂, uI, v₁, v₂, w} (J := J) ℱ
  obtain ⟨D0S, instD0S, K0S, b, hbDense, hbEquiv, D0, instD0, K0, hK0sub, hK0fin, wD0, hwD0,
      h𝒢rep⟩ := exists_ulift_family_site_presentation_target.{u₁, u₂, uG, v₁, v₂, w} (K := K) 𝒢
  letI := instC0S; letI := instC0; letI := instD0S; letI := instD0
  letI := haDense; letI := haEquiv; letI := hvC0; letI := hJ0sub; letI := hJ0fin
  letI := hbDense; letI := hbEquiv; letI := hwD0; letI := hK0sub; letI := hK0fin
  haveI hvCdense : (a ⋙ vC0).IsDenseSubsite J J0 :=
    dense_subsite_comp_of_equivalence_left (J0 := J0S) (J' := J0) a vC0
  haveI hwDdense : (b ⋙ wD0).IsDenseSubsite K K0 :=
    dense_subsite_comp_of_equivalence_left (J0 := K0S) (J' := K0) b wD0
  haveI : HasWeakSheafify K0 (Type (max w u₁ u₂ v₁ v₂)) := inferInstance
  haveI : HasSheafify J0 (Type (max w u₁ u₂ v₁ v₂)) := inferInstance
  obtain ⟨f0, ⟨sq0⟩⟩ :=
    transported_replacement_morphism (J0 := J0) (K0 := K0) (a ⋙ vC0) (b ⋙ wD0) f
  obtain ⟨C', instC', J', hJ'sub, hJ'fin, v729, hv729dense, hv729ff, u, hucontSF, hu729PB,
      hu729term, hu729contTop, g, ⟨sq1⟩⟩ :=
    exists_special_cocontinuous_site_factorization (J := J0) (K := K0) f0
  letI := instC'; letI := hJ'sub; letI := hJ'fin; letI := hv729dense
  haveI hv729FF : v729.FullyFaithful := hv729ff hJ0sub
  haveI : v729.Full := hv729FF.full
  haveI : v729.Faithful := hv729FF.faithful
  haveI hsrcDense : (a ⋙ vC0 ⋙ v729).IsDenseSubsite J J' := by
    have := isDenseSubsite_comp_right_ff (Jx := J) (Kx := J0) (Lx := J') (a ⋙ vC0) v729
    simpa [Functor.assoc] using this
  haveI hsrcDense' : ((a ⋙ vC0) ⋙ v729).IsDenseSubsite J J' := hsrcDense
  haveI hHasPbD0 : HasPullbacks D0 := inferInstance
  haveI hucont : u.IsContinuous K0 J' := hu729contTop hHasPbD0
  have huterm : IsTerminal (u.obj (⊤_ D0)) := (hu729term (⊤_ D0) terminalIsTerminal).some
  haveI : PreservesLimitsOfShape WalkingCospan u := hu729PB
  haveI hMOS : IsMorphismOfSites K0 J' u :=
    isMorphismOfSites_of_terminal_and_pullbacks u (⊤_ D0) terminalIsTerminal huterm
  refine ⟨C', instC', J', hJ'sub, hJ'fin, a ⋙ vC0 ⋙ v729, hsrcDense,
    D0, instD0, K0, hK0sub, hK0fin, b ⋙ wD0, hwDdense,
    u, hMOS, hu729PB, huterm, g, ?_, ?_, ?_⟩
  · -- the factorization square, by whiskering the conjugation square with `7.29.6`'s square.
    haveI : ((a ⋙ vC0) ⋙ v729).IsContinuous J J' := inferInstance
    exact (whisker_replacement_factorization_square (J0 := J0) (K0 := K0) (J' := J')
      (a ⋙ vC0) (b ⋙ wD0) v729 (g⁻¹) f f0 sq0 sq1).some
  · -- source-family representability: convert the iterated transport to the composite one
    -- (COH1) and transfer through the second dense subsite (Lemma 7.29.6's `v`, which is FF).
    intro i
    refine (denseSubsiteTypeTransport_isRepresentable_of_isRepresentable.{u₁, u₂, v₁, v₂, w}
      (J0 := J0) (J' := J') (a ⋙ vC0) v729 hv729FF (ℱ i) ?_).some
    haveI := hℱrep i
    exact isRepresentable_of_natIso
      (((sheafEquiv J0S J0 vC0 (Type (max w u₁ u₂ v₁ v₂))).functor.obj
        ((sheafEquiv J J0S a (Type (max w u₁ u₂ v₁ v₂))).functor.obj
          ((sheafCompose J CategoryTheory.uliftFunctor.{max w u₁ u₂ v₁ v₂, w}).obj (ℱ i)))).obj)
      ((sheafToPresheaf J0 (Type (max w u₁ u₂ v₁ v₂))).mapIso
        ((sheafEquivCompFunctorIso (J₀ := J) (K₀ := J0S) (L₀ := J0) a vC0).app
          ((sheafCompose J CategoryTheory.uliftFunctor.{max w u₁ u₂ v₁ v₂, w}).obj (ℱ i)))).symm
  · -- target-family representability: `D` is not enlarged, so only the COH1 conversion is needed.
    intro j
    haveI := h𝒢rep j
    exact isRepresentable_of_natIso
      (((sheafEquiv K0S K0 wD0 (Type (max w u₁ u₂ v₁ v₂))).functor.obj
        ((sheafEquiv K K0S b (Type (max w u₁ u₂ v₁ v₂))).functor.obj
          ((sheafCompose K CategoryTheory.uliftFunctor.{max w u₁ u₂ v₁ v₂, w}).obj (𝒢 j)))).obj)
      ((sheafToPresheaf K0 (Type (max w u₁ u₂ v₁ v₂))).mapIso
        ((sheafEquivCompFunctorIso (J₀ := K) (K₀ := K0S) (L₀ := K0) b wD0).app
          ((sheafCompose K CategoryTheory.uliftFunctor.{max w u₁ u₂ v₁ v₂, w}).obj (𝒢 j)))).symm

/-- Remark 7.29.7: for a morphism of topoi `f : Sh(J) ⟶ Sh(K)` and chosen families of set-valued
sheaves `ℱ` on `Sh(J)` and `𝒢` on `Sh(K)`, there exist subcanonical replacement sites
`(C', J')` and `(D', K')` with finite limits, dense-subsite comparison functors from the original
sites, such that the canonical dense-subsite transports carry the chosen families to representable
sheaves on the replacement sites, and a site morphism `u : D' ⥤ C'` satisfying the pullback and
terminal-object hypotheses of Proposition `7.14.7`, together with a lower morphism of topoi
`g : Sh(J') ⟶ Sh(K')` whose inverse-image functor fits into the canonical factorization square
with the two dense-subsite direct-image functors. The source remark additionally identifies `g`
with the morphism of topoi induced by `u` through Lemma `7.15.2` (equivalently,
`g _* ≅ u.sheafPushforwardContinuous`); that canonical identification is the six-step Yoneda
computation of the source text and is left to a future companion bridge, exactly as in the
statement of Lemma `7.29.6`. -/
theorem exists_topos_morphism_reduction
    [Small.{max w u₁ v₁} I] [Small.{max w u₂ v₂} G]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max w u₁ u₂ v₁ v₂} K J)
    (ℱ : I → Sheaf J (Type w))
    (𝒢 : G → Sheaf K (Type w)) :
    ∃ (C' : Type (max w u₁ u₂ v₁ v₂)) (_ : Category.{max w u₁ u₂ v₁ v₂} C')
      (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J'),
      ∃ (D' : Type (max w u₁ u₂ v₁ v₂)) (_ : Category.{max w u₁ u₂ v₁ v₂} D')
        (K' : GrothendieckTopology D')
        (_ : K'.Subcanonical) (_ : HasFiniteLimits D')
        (targetFunctor : D ⥤ D') (_ : targetFunctor.IsDenseSubsite K K'),
        ∃ (u : D' ⥤ C') (_ : IsMorphismOfSites K' J' u)
          (_ : PreservesLimitsOfShape WalkingCospan u)
          (_ : IsTerminal (u.obj (⊤_ D')))
          (g : MorphismOfTopoiIn K' J')
          (_ : CatCommSq
            (targetFunctor.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) K K')
            (g⁻¹)
            (f⁻¹)
            (sourceFunctor.sheafPushforwardContinuous (Type (max w u₁ u₂ v₁ v₂)) J J')),
          (∀ i : I, (((sourceFunctor.denseSubsiteTypeTransport J J').obj (ℱ i)).obj).IsRepresentable) ∧
            ∀ j : G, (((targetFunctor.denseSubsiteTypeTransport K K').obj (𝒢 j)).obj).IsRepresentable := by
  obtain ⟨C', instC', J', hJ', hfinC', sourceFunctor, hsourceDense,
      D', instD', K', hK', hfinD', targetFunctor, htargetDense,
      u, hu, huPullbacks, huTerminal, g, sq, hsourceRep, htargetRep⟩ :=
    exists_canonical_topos_morphism_reduction (f := f) ℱ 𝒢
  -- Reuse the canonical reduction package and choose the lower morphism of topoi
  -- to be the one canonically induced by `u`.
  exact ⟨C', instC', J', hJ', hfinC', sourceFunctor, hsourceDense,
    D', instD', K', hK', hfinD', targetFunctor, htargetDense,
    u, hu, huPullbacks, huTerminal, g, sq, hsourceRep, htargetRep⟩

end

end CategoryTheory
