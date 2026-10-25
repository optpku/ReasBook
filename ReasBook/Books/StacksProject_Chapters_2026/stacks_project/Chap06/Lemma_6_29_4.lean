module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap05.Lemma_5_24_5
public import stacks_project.Chap05.Lemma_5_27_1
public import stacks_project.Chap06.Lemma_6_21_6
public import stacks_project.Chap06.Lemma_6_29_1
public import stacks_project.Chap06.Lemma_6_29_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open TopCat.Presheaf.Pushforward renaming id → pushforwardId
open CategoryTheory.Limits TopCat.Sheaf

universe u v w uJ vJ uT

noncomputable section

/-- Helper for Lemma 6.29.4: the functor sending an object to its identity arrow. -/
public noncomputable def identityArrowFunctor (C : Type u) [Category.{v} C] : C ⥤ Arrow C where
  obj X := Arrow.mk (𝟙 X)
  map {X Y} f := Arrow.homMk f f (by simp)
  map_id X := by
    ext
    · simp
    · simp
  map_comp {X Y Z} f g := by
    ext
    · simp
    · simp

/-- Helper for Lemma 6.29.4: the identity-arrow inclusion is final. -/
public theorem identityArrowFunctor_final (C : Type u) [Category.{v} C] :
    Functor.Final (identityArrowFunctor C) where
  out f := by
    let i : StructuredArrow f (identityArrowFunctor C) :=
      StructuredArrow.mk (Arrow.homMk f.hom (𝟙 f.right) (by simp [identityArrowFunctor]))
    refine CategoryTheory.isConnected_of_isInitial (StructuredArrow f (identityArrowFunctor C))
      (x := i) ?_
    refine IsInitial.ofUniqueHom (X := i) ?_ ?_
    · intro g
      exact StructuredArrow.homMk g.hom.right (by
        ext
        · simpa [i, identityArrowFunctor] using (Arrow.w_mk_right g.hom).symm
        · simp [i, identityArrowFunctor])
    · intro g m
      apply StructuredArrow.hom_ext
      have h := congrArg Arrow.Hom.right (StructuredArrow.w m)
      simpa [i, identityArrowFunctor] using h

section

variable {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{max u v})
variable (stageSheaf : ∀ j : I, TopCat.Sheaf (Type (max u v)) (F.obj j))
variable (stageMap : ∀ {j k : I} (a : j ⟶ k),
  stageSheaf k ⟶
    (TopCat.Sheaf.pushforward (Type (max u v)) (F.map a)).obj (stageSheaf j))

/- Domain-style sampling for Lemma 6.29.4:
- primary domain: compatible inverse systems of set-valued sheaves on a cofiltered diagram of
  spectral spaces, together with the comparison between stagewise sections over inverse-image opens
  and sections of the colimit sheaf on the inverse limit;
- sampled owner declarations:
  `CategoryTheory.CofilteredSiteDiagram`,
  `CategoryTheory.ColimitSiteStageFamily`,
  `CategoryTheory.colimitSiteStageFamilySectionsComparison`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`;
- owner abstraction: the chapter-wide compatible-family owner already lives at the site level, so
  this file should keep the source-facing topological inputs `stageSheaf`, `stageMap`, and their
  compatibilities separate, and use pullback-side maps only as a bridge to the canonical site-level
  comparison on compact-open basis sites;
- primitive data: the stage sheaves and the pushforward transition maps `stageMap`, together with
  their identity and cocycle compatibilities;
- derived API: the pullback-form transition maps, the over-category section diagram, the pulled-back
  colimit sheaf on the limit space, and the comparison map on quasi-compact opens.

Source/core/bridge triage:
- `source-facing`: the stage sheaves, the pushforward transition maps, and the topological
  comparison map on quasi-compact opens;
- `core/canonical`: the site-level owners
  `CategoryTheory.CofilteredSiteDiagram`,
  `CategoryTheory.ColimitSiteStageFamily`,
  and `CategoryTheory.colimitSiteStageFamilySectionsComparison`;
- `bridge/view`: the explicit topological over-category and pulled-back diagrams below, which are
  implementation devices translating the source-facing inverse-system data to the canonical owner
  layer. -/

/-- The canonical sheaf morphism
`(f_a)_* \mathcal F_a ⟶ (f_b)_* \mathcal F_b`
attached to a morphism `u : A ⟶ B` in `(Over i)ᵒᵖ`. -/
public theorem projectionPushforwardMap_eq
    {i : I} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    F.map B.unop.hom = F.map u.unop.left ≫ F.map A.unop.hom := by
  simpa [Functor.map_comp] using
    (congrArg (fun f ↦ F.map f) (Over.w u.unop)).symm

public theorem pushforwardEq_inv_app
    {X Y : TopCat.{max u v}} {f g : X ⟶ Y} (h : f = g)
    (P : TopCat.Presheaf (Type (max u v)) X) (U : (Opens Y)ᵒᵖ) :
  (TopCat.Presheaf.pushforwardEq h P).inv.app U = P.map (eqToHom (by cat_disch)) := by
  subst h
  simp [TopCat.Presheaf.pushforwardEq]

public theorem opens_mapIso_id_comp
    {X Y : TopCat.{w}} (f : X ⟶ Y) (h : f = 𝟙 X ≫ f) :
    Opens.mapIso f (𝟙 X ≫ f) h = Iso.refl _ := by
  cases h
  exact Opens.mapIso_refl f _

public theorem opens_mapIso_hom_trans
    {X Y : TopCat.{w}} {f g h : X ⟶ Y} (hfg : f = g) (hgh : g = h) :
    (Opens.mapIso f g hfg).hom ≫ (Opens.mapIso g h hgh).hom =
      (Opens.mapIso f h (hfg.trans hgh)).hom := by
  subst hfg
  subst hgh
  simp

public theorem opens_mapIso_inv_trans
    {X Y : TopCat.{w}} {f g h : X ⟶ Y} (hfg : f = g) (hgh : g = h) :
    (Opens.mapIso g h hgh).inv ≫ (Opens.mapIso f g hfg).inv =
      (Opens.mapIso f h (hfg.trans hgh)).inv := by
  subst hfg
  subst hgh
  simp

public theorem pushforwardEq_hom_trans
    {X Y : TopCat.{w}} {f g h : X ⟶ Y} (hfg : f = g) (hgh : g = h)
    (P : TopCat.Presheaf (Type v) X) :
    (TopCat.Presheaf.pushforwardEq hfg P).hom ≫
      (TopCat.Presheaf.pushforwardEq hgh P).hom =
        (TopCat.Presheaf.pushforwardEq (hfg.trans hgh) P).hom := by
  subst hfg
  subst hgh
  simp [TopCat.Presheaf.pushforwardEq]
  cat_disch

public theorem pushforwardEq_inv_trans
    {X Y : TopCat.{w}} {f g h : X ⟶ Y} (hfg : f = g) (hgh : g = h)
    (P : TopCat.Presheaf (Type v) X) :
    (TopCat.Presheaf.pushforwardEq hgh P).inv ≫
      (TopCat.Presheaf.pushforwardEq hfg P).inv =
        (TopCat.Presheaf.pushforwardEq (hfg.trans hgh) P).inv := by
  subst hfg
  subst hgh
  simp [TopCat.Presheaf.pushforwardEq]
  cat_disch

public theorem pushforwardEq_inv_naturality
    {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g)
    {P Q : TopCat.Presheaf (Type v) X} (α : P ⟶ Q) :
    (TopCat.Presheaf.pushforward (Type v) g).map α ≫
        (TopCat.Presheaf.pushforwardEq h Q).inv =
      (TopCat.Presheaf.pushforwardEq h P).inv ≫
        (TopCat.Presheaf.pushforward (Type v) f).map α := by
  subst h
  ext U x
  simp [TopCat.Presheaf.pushforwardEq]

public theorem pushforwardEq_id_comp_inv
    {X Y : TopCat.{max u v}} {g : X ⟶ X} (hg : g = 𝟙 X) (f : X ⟶ Y)
    (hfg : f = g ≫ f) (P : TopCat.Presheaf (Type (max u v)) X) :
    (TopCat.Presheaf.pushforward (Type (max u v)) f).map
        ((pushforwardId P).inv ≫ (TopCat.Presheaf.pushforwardEq hg P).inv) ≫
      (TopCat.Presheaf.pushforwardEq hfg P).inv = 𝟙 _ := by
  subst hg
  simp only [TopCat.Presheaf.pushforwardEq]
  rw [opens_mapIso_id_comp f hfg]
  simp only [Opens.mapIso_refl]
  ext U x
  simp [Functor.isoWhiskerRight, pushforwardId, TopCat.Presheaf.Pushforward.id]
  change P.map (𝟙 ((Opens.map f).obj U)).op x = x
  simp

public theorem pushforwardEq_comp_inv_naturality
    {W X Y Z : TopCat.{max u v}} {f : Y ⟶ X} {g : Z ⟶ Y} {p : X ⟶ W}
    {q : Y ⟶ W} {r : Z ⟶ W} {c : Z ⟶ X}
    (hfg : c = g ≫ f) (hp : q = f ≫ p) (hr : r = g ≫ q) (hcp : r = c ≫ p)
    {PX : TopCat.Presheaf (Type (max u v)) X}
    {PY : TopCat.Presheaf (Type (max u v)) Y}
    {PZ : TopCat.Presheaf (Type (max u v)) Z}
    (α : PX ⟶ (TopCat.Presheaf.pushforward (Type (max u v)) f).obj PY)
    (β : PY ⟶ (TopCat.Presheaf.pushforward (Type (max u v)) g).obj PZ) :
    (TopCat.Presheaf.pushforward (Type (max u v)) p).map
        (α ≫ (TopCat.Presheaf.pushforward (Type (max u v)) f).map β ≫
          (TopCat.Presheaf.pushforwardEq hfg PZ).inv) ≫
      (TopCat.Presheaf.pushforwardEq hcp PZ).inv =
        (TopCat.Presheaf.pushforward (Type (max u v)) p).map α ≫
          (TopCat.Presheaf.pushforwardEq hp PY).inv ≫
            (TopCat.Presheaf.pushforward (Type (max u v)) q).map β ≫
              (TopCat.Presheaf.pushforwardEq hr PZ).inv := by
  subst hfg
  subst hp
  subst hr
  ext U x
  simp [TopCat.Presheaf.pushforwardEq, Category.assoc]

/-- Helper for Lemma 6.29.4: evaluating a morphism after pushing it forward along `a` and
transporting by `c = b ≫ a` is heterogeneously the same as evaluating the original morphism on
`a⁻¹ U`. -/
public theorem pushforward_map_comp_inv_app_heq
    {W X Y : TopCat.{max u v}} (b : W ⟶ X) (a : X ⟶ Y)
    {c : W ⟶ Y} (hc : c = b ≫ a)
    {P : TopCat.Presheaf (Type (max u v)) X}
    {Q : TopCat.Presheaf (Type (max u v)) W}
    (α : P ⟶ (TopCat.Presheaf.pushforward (Type (max u v)) b).obj Q)
    (U : Opens Y) (s : P.obj (op ((Opens.map a).obj U))) :
    (((TopCat.Presheaf.pushforward (Type (max u v)) a).map α ≫
        (TopCat.Presheaf.pushforwardEq hc Q).inv).app (op U) s) ≍
      α.app (op ((Opens.map a).obj U)) s := by
  subst hc
  simp [TopCat.Presheaf.pushforwardEq]

/-- Helper for Lemma 6.29.4: a map between filtered colimits of type-valued diagrams is
bijective if each target representative is hit after one refinement and equality of two source
representatives is detected after one refinement. -/
public theorem filtered_colimMap_bijective_of_eventual
    {J : Type uJ} [Category.{vJ} J] [IsFilteredOrEmpty J]
    {F G : J ⥤ Type uT} [HasColimit F] [HasColimit G] (η : F ⟶ G)
    (hsurj :
      ∀ (j : J) (y : G.obj j), ∃ (k : J) (f : j ⟶ k) (x : F.obj k),
        η.app k x = G.map f y)
    (hinj :
      ∀ (j : J) {x y : F.obj j}, η.app j x = η.app j y →
        ∃ (k : J) (f : j ⟶ k), F.map f x = F.map f y) :
    Function.Bijective (colimMap η) := by
  constructor
  · intro x y hxy
    -- Move both source representatives to one common stage, then use the filtered equality
    -- criterion in the target and the eventual injectivity hypothesis.
    obtain ⟨j, xj, yj, hxj, hyj⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit F) x y
    rw [← hxj, ← hyj] at hxy ⊢
    have hxη :
        colimMap η (colimit.ι F j xj) = colimit.ι G j (η.app j xj) := by
      simpa using congrFun (ι_colimMap η j) xj
    have hyη :
        colimMap η (colimit.ι F j yj) = colimit.ι G j (η.app j yj) := by
      simpa using congrFun (ι_colimMap η j) yj
    have hηcol : colimit.ι G j (η.app j xj) = colimit.ι G j (η.app j yj) := by
      simpa [hxη, hyη] using hxy
    obtain ⟨k, f, hk⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff'
        (F := G) (colimit.isColimit G) (η.app j xj) (η.app j yj)).1 hηcol
    have hηrefined : η.app k (F.map f xj) = η.app k (F.map f yj) := by
      have hxnat := congrFun (η.naturality f) xj
      have hynat := congrFun (η.naturality f) yj
      exact hxnat.trans (hk.trans hynat.symm)
    obtain ⟨l, g, hg⟩ := hinj k hηrefined
    exact
      (Types.FilteredColimit.isColimit_eq_iff'
        (F := F) (colimit.isColimit F) xj yj).2
        ⟨l, f ≫ g, by simpa using hg⟩
  · intro z
    -- Present the target colimit element at one stage, then use eventual surjectivity there.
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective' (F := G) z
    obtain ⟨k, f, x, hx⟩ := hsurj j y
    refine ⟨colimit.ι F k x, ?_⟩
    calc
      colimMap η (colimit.ι F k x) = colimit.ι G k (η.app k x) := by
        simpa using congrFun (ι_colimMap η k) x
      _ = colimit.ι G k (G.map f y) := by
        rw [hx]
      _ = colimit.ι G j y := by
        simpa using congrFun (colimit.w G f) y
      _ = z := hy

/-- The canonical sheaf morphism
`(f_a)_* \mathcal F_a ⟶ (f_b)_* \mathcal F_b`
attached to a morphism `u : A ⟶ B` in `(Over i)ᵒᵖ`. -/
public noncomputable def projectionPushforwardMap
    {i : I} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    (TopCat.Sheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).obj
        (stageSheaf A.unop.left) ⟶
      (TopCat.Sheaf.pushforward (Type (max u v)) (F.map B.unop.hom)).obj
        (stageSheaf B.unop.left) :=
  (TopCat.Sheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map
      (stageMap u.unop.left) ≫
    ⟨(TopCat.Presheaf.pushforwardEq (projectionPushforwardMap_eq F u)
      (stageSheaf B.unop.left).presheaf).inv⟩

end

public structure InverseLimitTypeSheafSystem
    {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{max u v}) [IsCofiltered I]
    [∀ j : I, SpectralSpace ↥(F.obj j)] where
  stageSheaf : ∀ i : I, TopCat.Sheaf (Type (max u v)) (F.obj i)
  stageMap : ∀ {j k : I} (a : j ⟶ k),
      stageSheaf k ⟶
      (pushforward (Type (max u v)) (F.map a)).obj (stageSheaf j)
  stageMap_id :
    ∀ i : I,
      stageMap (𝟙 i) =
        ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
          (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩
  stageMap_comp :
    ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
      stageMap (b ≫ a) =
        ⟨(stageMap a ≫ (pushforward (Type (max u v)) (F.map a)).map (stageMap b)).1 ≫
          (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩

namespace InverseLimitTypeSheafSystem

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
variable {F : I ⥤ TopCat.{max u v}} [∀ j : I, SpectralSpace ↥(F.obj j)]
variable [HasColimitsOfShape Iᵒᵖ (TopCat.Sheaf (Type (max u v)) (limit F))]

variable (setup : InverseLimitTypeSheafSystem F)

/-- The canonical pullback-form transition attached to `a : j ⟶ k`, derived from the source-facing
pushforward map `\varphi_a : \mathcal F_k ⟶ f_{a,*}\mathcal F_j` by the pullback-pushforward
adjunction. This is the bridge-level form used by the later colimit sheaf construction on the
inverse-limit space. -/
public noncomputable def stagePullbackMap {j k : I} (a : j ⟶ k) :
    ((pullback (Type (max u v)) (F.map a)).obj (setup.stageSheaf k)) ⟶ setup.stageSheaf j :=
  ((pullbackPushforwardAdjunction (Type (max u v)) (F.map a)).homEquiv _ _).symm
    (setup.stageMap a)

/-- Helper for Lemma 6.29.4: the pullback-form transition is adjoint to the original
pushforward-form transition. -/
public theorem stageMap_unit_stagePullbackMap {j k : I} (a : j ⟶ k) :
    (pullbackPushforwardAdjunction (Type (max u v)) (F.map a)).unit.app
        (setup.stageSheaf k) ≫
      (pushforward (Type (max u v)) (F.map a)).map (setup.stagePullbackMap a) =
        setup.stageMap a := by
  have hunit :=
    Adjunction.homEquiv_unit
      (pullbackPushforwardAdjunction (Type (max u v)) (F.map a))
      (setup.stageSheaf k) (setup.stageSheaf j) (setup.stagePullbackMap a)
  have htranspose :
      ((pullbackPushforwardAdjunction (Type (max u v)) (F.map a)).homEquiv
          (setup.stageSheaf k) (setup.stageSheaf j))
        (setup.stagePullbackMap a) =
          setup.stageMap a := by
    simp [stagePullbackMap]
  exact hunit.trans htranspose

/-- The over-category diagram of pushforwarded stage sheaves on `X_i`. -/
public noncomputable def projectionPushforwardDiagram (i : I) :
    (Over i)ᵒᵖ ⥤ TopCat.Sheaf (Type (max u v)) (F.obj i) where
  obj A := (pushforward (Type (max u v)) (F.map A.unop.hom)).obj (setup.stageSheaf A.unop.left)
  map u := projectionPushforwardMap F setup.stageSheaf setup.stageMap u
  map_id A := by
    dsimp [projectionPushforwardMap]
    rw [setup.stageMap_id A.unop.left]
    apply Sheaf.hom_ext
    simpa [TopCat.Sheaf.pushforward_map] using
      @pushforwardEq_id_comp_inv.{u, v} (F.obj A.unop.left) (F.obj i)
        (F.map (𝟙 A.unop.left)) (F.map_id A.unop.left) (F.map A.unop.hom)
        (projectionPushforwardMap_eq F (𝟙 A)) (setup.stageSheaf A.unop.left).presheaf
  map_comp u v := by
    dsimp [projectionPushforwardMap]
    rw [setup.stageMap_comp u.unop.left v.unop.left]
    apply Sheaf.hom_ext
    simpa [TopCat.Sheaf.pushforward_map, Category.assoc] using
      pushforwardEq_comp_inv_naturality.{u, v}
        (F.map_comp v.unop.left u.unop.left)
        (projectionPushforwardMap_eq F u)
        (projectionPushforwardMap_eq F v)
        (projectionPushforwardMap_eq F (u ≫ v))
        (setup.stageMap u.unop.left).1
        (setup.stageMap v.unop.left).1

/-- The canonical sections functor at the open `U_i` on the stage `X_i`. -/
public abbrev stageSectionFunctor (i : I) (Uᵢ : Opens (F.obj i)) :
    TopCat.Sheaf (Type (max u v)) (F.obj i) ⥤ Type (max u v) :=
  (CategoryTheory.sheafSections (Opens.grothendieckTopology (F.obj i)) (Type (max u v))).obj
    (op Uᵢ)

/-- The section type `\mathcal{F}_j(f_a^{-1}(U_i))` attached to an object `a : j ⟶ i` of
`Over i`, derived by evaluating the canonical pushforward-sheaf diagram at `U_i`. -/
public abbrev projectionOpenSectionValue (i : I) (Uᵢ : Opens (F.obj i))
    (A : (Over i)ᵒᵖ) : Type (max u v) :=
  (stageSectionFunctor i Uᵢ).obj ((setup.projectionPushforwardDiagram i).obj A)

/-- The over-category diagram `a : j ⟶ i ↦ \mathcal{F}_j(f_a^{-1}(U_i))`, obtained by evaluating
the canonical pushforward-sheaf diagram at `U_i`. -/
public noncomputable def projectionOpenSectionDiagram (i : I) (Uᵢ : Opens (F.obj i)) :
    (Over i)ᵒᵖ ⥤ Type (max u v) :=
  setup.projectionPushforwardDiagram i ⋙ stageSectionFunctor i Uᵢ

/-- The colimit `\mathop{\mathrm{colim}}_{a : j \to i} \mathcal{F}_j(f_a^{-1}(U_i))`. -/
noncomputable def projectionOpenSectionColimit (i : I) (Uᵢ : Opens (F.obj i)) :
    Type (max u v) :=
  colimit (setup.projectionOpenSectionDiagram i Uᵢ)

/-- The transition map on the pulled-back stage-sheaf diagram over the limit space. -/
public noncomputable def pulledBackDiagramMap {j k : I} (a : j ⟶ k) :
    ((pullback (Type (max u v)) (limit.π F k)).obj (setup.stageSheaf k)) ⟶
      ((pullback (Type (max u v)) (limit.π F j)).obj (setup.stageSheaf j)) :=
  ((eqToIso (congrArg (pullback (Type (max u v))) (limit.w F a))).inv.app (setup.stageSheaf k)) ≫
    ((pullbackComp (limit.π F j) (F.map a)).inv.app (setup.stageSheaf k)) ≫
      (pullback (Type (max u v)) (limit.π F j)).map (setup.stagePullbackMap a)

public noncomputable def stagePullbackCompIso {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    pullback (Type (max u v)) (F.map b) ⋙ pullback (Type (max u v)) (F.map a) ≅
      pullback (Type (max u v)) (F.map (a ≫ b)) :=
  TopCat.Sheaf.pullbackComp (A := Type (max u v)) (F.map a) (F.map b) ≪≫
    eqToIso (congrArg (pullback (Type (max u v))) (F.map_comp a b).symm)

public noncomputable def limitStagePullbackCompIso {j k : I} (a : j ⟶ k) :
    pullback (Type (max u v)) (F.map a) ⋙ pullback (Type (max u v)) (limit.π F j) ≅
      pullback (Type (max u v)) (limit.π F k) :=
  TopCat.Sheaf.pullbackComp (A := Type (max u v)) (limit.π F j) (F.map a) ≪≫
    eqToIso (congrArg (pullback (Type (max u v))) (limit.w F a))

public theorem sheafPullbackComp_def {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullbackComp (A := Type w) f g =
      Adjunction.leftAdjointCompIso
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) g)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) f)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g))
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type w) f ⋙
              TopCat.Sheaf.pushforward (Type w) g =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g) from rfl)) := by
  rfl

/-- Helper for Lemma 6.29.4: the pullback unit for a composite map is the composite of the two
pullback units followed by the canonical `pullbackComp` comparison, on sections. -/
public theorem pullback_unit_comp_section_eq
    {X Y Z : TopCat.{max u v}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (𝒢 : TopCat.Sheaf (Type (max u v)) Z) (U : Opens Z)
    (s : 𝒢.1.obj (op U)) :
    (((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).hom.app 𝒢).1.app
        (op ((Opens.map f).obj ((Opens.map g).obj U)))
        (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app
              ((pullback (Type (max u v)) g).obj 𝒢)).1.app
          (op ((Opens.map g).obj U))
          (((pullbackPushforwardAdjunction (Type (max u v)) g).unit.app 𝒢).1.app
            (op U) s))) =
      (((pullbackPushforwardAdjunction (Type (max u v)) (f ≫ g)).unit.app 𝒢).1.app
        (op U) s) := by
  let adjfg := TopCat.Sheaf.pullbackPushforwardAdjunction (Type (max u v)) (f ≫ g)
  let adj :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type (max u v)) g).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type (max u v)) f)
  let e : TopCat.Sheaf.pushforward (Type (max u v)) f ⋙
        TopCat.Sheaf.pushforward (Type (max u v)) g ≅
      TopCat.Sheaf.pushforward (Type (max u v)) (f ≫ g) :=
    eqToIso
      (show TopCat.Sheaf.pushforward (Type (max u v)) f ⋙
          TopCat.Sheaf.pushforward (Type (max u v)) g =
        TopCat.Sheaf.pushforward (Type (max u v)) (f ≫ g) from rfl)
  have hconj :
      CategoryTheory.conjugateEquiv adjfg adj
        ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).hom) = 𝟙 _ := by
    have h_inv :
        CategoryTheory.conjugateEquiv adj adjfg
          ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).inv) = e.hom := by
      rw [sheafPullbackComp_def]
      simpa [adjfg, adj, e] using
        (CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type (max u v)) g)
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type (max u v)) f)
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type (max u v)) (f ≫ g))
          e)
    have hcomp :=
      CategoryTheory.conjugateEquiv_comp adjfg adj adjfg
        ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).hom)
        ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).inv)
    simpa [adjfg, adj, e, h_inv] using hcomp
  have hhom :
      adj.homEquiv 𝒢 ((TopCat.Sheaf.pullback (Type (max u v)) (f ≫ g)).obj 𝒢)
        ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).hom.app 𝒢) =
      adjfg.unit.app 𝒢 := by
    have hunit :=
      CategoryTheory.unit_conjugateEquiv
        adjfg adj
        ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).hom)
        𝒢
    simpa [adjfg, adj, Adjunction.homEquiv_unit, hconj] using hunit.symm
  simpa [adjfg, adj, Adjunction.homEquiv_unit] using
    congrArg
      (fun k ↦ k.1.app (op U) s)
      hhom

public theorem pullbackComp_inv_unit_naturality_app
    {X Y Z : TopCat.{max u v}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (𝒢 : TopCat.Sheaf (Type (max u v)) Z)
    (ℋ : TopCat.Sheaf (Type (max u v)) Y)
    (β : (pullback (Type (max u v)) g).obj 𝒢 ⟶ ℋ)
    (U : Opens Z)
    (s : (((pullback (Type (max u v)) g).obj 𝒢).1.obj
      (op ((Opens.map g).obj U)))) :
    (((pullbackComp f g).inv.app 𝒢 ≫ (pullback (Type (max u v)) f).map β).1.app
        (op ((Opens.map f).obj ((Opens.map g).obj U)))
        (((pullbackComp f g).hom.app 𝒢).1.app
          (op ((Opens.map f).obj ((Opens.map g).obj U)))
          (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app
              ((pullback (Type (max u v)) g).obj 𝒢)).1.app
            (op ((Opens.map g).obj U)) s))) =
      (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app ℋ).1.app
        (op ((Opens.map g).obj U)) (β.1.app (op ((Opens.map g).obj U)) s)) := by
  let V := (Opens.map g).obj U
  have hcancel :
      (pullbackComp f g).hom.app 𝒢 ≫
          ((pullbackComp f g).inv.app 𝒢 ≫ (pullback (Type (max u v)) f).map β) =
        (pullback (Type (max u v)) f).map β := by
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hnat :=
    Adjunction.unit_naturality
      (pullbackPushforwardAdjunction (Type (max u v)) f) β
  have hnat_app :=
    congrFun (congrArg (fun α ↦ α.1.app (op V)) hnat) s
  calc
    (((pullbackComp f g).inv.app 𝒢 ≫ (pullback (Type (max u v)) f).map β).1.app
        (op ((Opens.map f).obj ((Opens.map g).obj U)))
        (((pullbackComp f g).hom.app 𝒢).1.app
          (op ((Opens.map f).obj ((Opens.map g).obj U)))
          (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app
              ((pullback (Type (max u v)) g).obj 𝒢)).1.app
            (op ((Opens.map g).obj U)) s)))
        =
      (((pullbackComp f g).hom.app 𝒢 ≫
          ((pullbackComp f g).inv.app 𝒢 ≫ (pullback (Type (max u v)) f).map β)).1.app
        (op ((Opens.map f).obj ((Opens.map g).obj U)))
        (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app
            ((pullback (Type (max u v)) g).obj 𝒢)).1.app
          (op ((Opens.map g).obj U)) s)) := by
          rfl
    _ =
      (((pullback (Type (max u v)) f).map β).1.app
        (op ((Opens.map f).obj ((Opens.map g).obj U)))
        (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app
            ((pullback (Type (max u v)) g).obj 𝒢)).1.app
          (op ((Opens.map g).obj U)) s)) := by
          exact congrFun
            (congrArg (fun α ↦ α.1.app
              (op ((Opens.map f).obj ((Opens.map g).obj U)))) hcancel)
            (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app
              ((pullback (Type (max u v)) g).obj 𝒢)).1.app
                (op ((Opens.map g).obj U)) s)
    _ =
      (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app ℋ).1.app
        (op ((Opens.map g).obj U)) (β.1.app (op ((Opens.map g).obj U)) s)) := by
          simpa [V, ConcreteCategory.comp_apply, TopCat.Sheaf.pushforward_map] using hnat_app

public theorem pullbackComp_eqToHom_inv_unit_naturality_app_heq
    {X Y Z : TopCat.{max u v}} (f : X ⟶ Y) (g : Y ⟶ Z) {p : X ⟶ Z}
    (hp : p = f ≫ g)
    (𝒢 : TopCat.Sheaf (Type (max u v)) Z)
    (ℋ : TopCat.Sheaf (Type (max u v)) Y)
    (β : (pullback (Type (max u v)) g).obj 𝒢 ⟶ ℋ)
    (U : Opens Z)
    (s : (((pullback (Type (max u v)) g).obj 𝒢).1.obj
      (op ((Opens.map g).obj U)))) :
    let Φ :
        (pullback (Type (max u v)) p) ⟶
          (pullback (Type (max u v)) (f ≫ g)) :=
      eqToHom (congrArg (pullback (Type (max u v))) hp);
    (Φ.app 𝒢 ≫ (pullbackComp f g).inv.app 𝒢 ≫
        (pullback (Type (max u v)) f).map β).1.app
        (op ((Opens.map p).obj U))
        (cast (by
          subst p
          rfl)
          (((pullbackComp f g).hom.app 𝒢).1.app
            (op ((Opens.map f).obj ((Opens.map g).obj U)))
            (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app
                ((pullback (Type (max u v)) g).obj 𝒢)).1.app
              (op ((Opens.map g).obj U)) s))) ≍
      (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app ℋ).1.app
        (op ((Opens.map g).obj U)) (β.1.app (op ((Opens.map g).obj U)) s)) := by
  subst p
  simpa [Category.assoc, eqToHom_app] using
    (heq_of_eq
      (@pullbackComp_inv_unit_naturality_app.{u, v}
        (X := X) (Y := Y) (Z := Z) f g 𝒢 ℋ β U s))

public theorem pullback_unit_app_heq_of_eq
    {X Y : TopCat.{max u v}} {f g : X ⟶ Y} (h : f = g)
    (𝒢 : TopCat.Sheaf (Type (max u v)) Y) (U : Opens Y)
    (s : 𝒢.1.obj (op U)) :
    (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app 𝒢).1.app
        (op U) s) ≍
      (((pullbackPushforwardAdjunction (Type (max u v)) g).unit.app 𝒢).1.app
        (op U) s) := by
  subst h
  rfl

public theorem pullback_unit_app_heq_of_open_eq
    {X Y : TopCat.{max u v}} (f : X ⟶ Y)
    (𝒢 : TopCat.Sheaf (Type (max u v)) Y) {U V : Opens Y} (h : U = V)
    (s : 𝒢.1.obj (op U)) :
    (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app 𝒢).1.app
        (op U) s) ≍
      (((pullbackPushforwardAdjunction (Type (max u v)) f).unit.app 𝒢).1.app
        (op V) (cast (by cases h; rfl) s)) := by
  subst h
  rfl

public theorem pullback_unit_id_app_eq
    {Y : TopCat.{max u v}} (𝒢 : TopCat.Sheaf (Type (max u v)) Y) (U : Opens Y)
    {s t : 𝒢.1.obj (op U)}
    (hst :
      (((pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)).unit.app 𝒢).1.app
        (op U)) s =
      (((pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)).unit.app 𝒢).1.app
        (op U)) t) :
    s = t := by
  let adj := pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)
  let α : 𝒢 ⟶ (pushforward (Type (max u v)) (𝟙 Y)).obj 𝒢 :=
    ⟨(pushforwardId 𝒢.presheaf).inv ≫
      (TopCat.Presheaf.pushforwardEq (show 𝟙 Y = 𝟙 Y from rfl) 𝒢.presheaf).inv⟩
  let β := (pushforward (Type (max u v)) (𝟙 Y)).map ((adj.homEquiv 𝒢 𝒢).symm α)
  have hunit : adj.unit.app 𝒢 ≫ β = α := by
    have hunit0 := Adjunction.homEquiv_unit adj 𝒢 𝒢 ((adj.homEquiv 𝒢 𝒢).symm α)
    exact hunit0.trans (Equiv.apply_symm_apply (adj.homEquiv 𝒢 𝒢) α)
  have hcomp :=
    congrArg (fun e : 𝒢 ⟶ (pushforward (Type (max u v)) (𝟙 Y)).obj 𝒢 ↦
      e.1.app (op U)) hunit
  have hst' := congrArg (fun z ↦ β.1.app (op U) z) hst
  have hαs : α.1.app (op U) s = s := by
    dsimp [α]
    simp [TopCat.Presheaf.pushforwardEq]
  have hαt : α.1.app (op U) t = t := by
    dsimp [α]
    simp [TopCat.Presheaf.pushforwardEq]
  exact hαs.symm.trans
    ((congrFun hcomp s).symm.trans (hst'.trans ((congrFun hcomp t).trans hαt)))

public theorem pullback_unit_comp_pushforwardEq_heq
    {W X Y Z : TopCat.{max u v}} (H : W ⟶ X) (p : X ⟶ Y)
    (a : Y ⟶ Z) {c : X ⟶ Z} (hc : c = p ≫ a)
    (𝒢 : TopCat.Sheaf (Type (max u v)) Y) (U : Opens Z)
    (s : 𝒢.1.obj (op ((Opens.map a).obj U))) :
    let ℋ := (pullback (Type (max u v)) p).obj 𝒢;
    (((pullbackComp H p).hom.app 𝒢).1.app
        (op ((Opens.map H).obj ((Opens.map c).obj U)))
        (((pullbackPushforwardAdjunction (Type (max u v)) H).unit.app ℋ).1.app
          (op ((Opens.map c).obj U))
          ((TopCat.Presheaf.pushforwardEq hc ℋ.presheaf).inv.app (op U)
            (((pullbackPushforwardAdjunction (Type (max u v)) p).unit.app 𝒢).1.app
              (op ((Opens.map a).obj U)) s)))) ≍
      (((pullbackComp H p).hom.app 𝒢).1.app
        (op ((Opens.map H).obj ((Opens.map p).obj ((Opens.map a).obj U))))
        (((pullbackPushforwardAdjunction (Type (max u v)) H).unit.app ℋ).1.app
          (op ((Opens.map p).obj ((Opens.map a).obj U)))
          (((pullbackPushforwardAdjunction (Type (max u v)) p).unit.app 𝒢).1.app
            (op ((Opens.map a).obj U)) s))) := by
  subst hc
  simp [TopCat.Presheaf.pushforwardEq]

public theorem pullback_unit_comp_pushforwardEq_eqToHom_heq
    {W X Y Z : TopCat.{max u v}} (H : W ⟶ X) (p : X ⟶ Y)
    (a : Y ⟶ Z) {c : X ⟶ Z} (hc : c = p ≫ a) {q : W ⟶ Y}
    (hq : H ≫ p = q) (𝒢 : TopCat.Sheaf (Type (max u v)) Y)
    (U : Opens Z) (s : 𝒢.1.obj (op ((Opens.map a).obj U))) :
    let ℋ := (pullback (Type (max u v)) p).obj 𝒢;
    let Φ :
        (pullback (Type (max u v)) (H ≫ p)) ⟶
          (pullback (Type (max u v)) q) :=
      eqToHom (congrArg (pullback (Type (max u v))) hq);
    (((pullbackComp H p).hom.app 𝒢 ≫ Φ.app 𝒢).1.app
        (op ((Opens.map H).obj ((Opens.map c).obj U)))
        (((pullbackPushforwardAdjunction (Type (max u v)) H).unit.app ℋ).1.app
          (op ((Opens.map c).obj U))
          ((TopCat.Presheaf.pushforwardEq hc ℋ.presheaf).inv.app (op U)
            (((pullbackPushforwardAdjunction (Type (max u v)) p).unit.app 𝒢).1.app
              (op ((Opens.map a).obj U)) s))) ≍
      (((pullbackPushforwardAdjunction (Type (max u v)) q).unit.app 𝒢).1.app
        (op ((Opens.map a).obj U)) s)) := by
  subst hc
  subst hq
  simpa [TopCat.Presheaf.pushforwardEq, Category.assoc, eqToHom_app] using
    (@pullback_unit_comp_section_eq.{u, v} (X := W) (Y := X) (Z := Y)
      H p 𝒢 ((Opens.map a).obj U) s)

public theorem pullback_unit_comp_pushforward_unit_pushforwardEq_eqToHom_heq
    {W X Y Z : TopCat.{max u v}} (H : W ⟶ X) (p : X ⟶ Y)
    (a : Y ⟶ Z) {c : X ⟶ Z} (hc : c = p ≫ a) {q : W ⟶ Y}
    (hq : H ≫ p = q) (𝒢 : TopCat.Sheaf (Type (max u v)) Y)
    (U : Opens Z) (s : 𝒢.1.obj (op ((Opens.map a).obj U))) :
    let ℋ := (pullback (Type (max u v)) p).obj 𝒢;
    let Φ :
        (pullback (Type (max u v)) (H ≫ p)) ⟶
          (pullback (Type (max u v)) q) :=
      eqToHom (congrArg (pullback (Type (max u v))) hq);
    let Ψ :=
      (TopCat.Presheaf.pushforward (Type (max u v)) a).map
          (((pullbackPushforwardAdjunction (Type (max u v)) p).unit.app 𝒢).1) ≫
      (TopCat.Presheaf.pushforwardEq hc ℋ.presheaf).inv;
    (((pullbackComp H p).hom.app 𝒢 ≫ Φ.app 𝒢).1.app
        (op ((Opens.map H).obj ((Opens.map c).obj U)))
        (((pullbackPushforwardAdjunction (Type (max u v)) H).unit.app ℋ).1.app
          (op ((Opens.map c).obj U))
          (Ψ.app (op U) s))) ≍
      (((pullbackPushforwardAdjunction (Type (max u v)) q).unit.app 𝒢).1.app
        (op ((Opens.map a).obj U)) s) := by
  subst hc
  subst hq
  simpa [TopCat.Presheaf.pushforwardEq, Category.assoc, eqToHom_app] using
    (@pullback_unit_comp_section_eq.{u, v} (X := W) (Y := X) (Z := Y)
      H p 𝒢 ((Opens.map a).obj U) s)

public theorem sheafPushforward_assoc {W X Y Z : TopCat.{w}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type w) f)
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type w) g ⋙ TopCat.Sheaf.pushforward (Type w) h =
            TopCat.Sheaf.pushforward (Type w) (g ≫ h) from rfl)) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type w) f ⋙
            TopCat.Sheaf.pushforward (Type w) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl) =
    (Functor.associator
      (TopCat.Sheaf.pushforward (Type w) f)
      (TopCat.Sheaf.pushforward (Type w) g)
      (TopCat.Sheaf.pushforward (Type w) h)).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type w) f ⋙ TopCat.Sheaf.pushforward (Type w) g =
            TopCat.Sheaf.pushforward (Type w) (f ≫ g) from rfl))
        (TopCat.Sheaf.pushforward (Type w) h) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type w) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type w) h =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl) := by
  ext ℱ
  rfl

public theorem sheafPullbackComp_assoc {W X Y Z : TopCat.{w}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Functor.isoWhiskerLeft _ (TopCat.Sheaf.pullbackComp (A := Type w) f g) ≪≫
      TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (TopCat.Sheaf.pullbackComp (A := Type w) g h) _ ≪≫
        TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h) := by
  simpa [sheafPullbackComp_def] using
    (Adjunction.leftAdjointCompIso_assoc
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) h)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) g)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (g ≫ h))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g ≫ h))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) g ⋙ TopCat.Sheaf.pushforward (Type w) h =
          TopCat.Sheaf.pushforward (Type w) (g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) f ⋙ TopCat.Sheaf.pushforward (Type w) g =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type w) h =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) f ⋙
            TopCat.Sheaf.pushforward (Type w) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl))
      (sheafPushforward_assoc f g h))

public theorem sheafPullback_pseudofunctor_associativity {W X Y Z : TopCat.{w}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv ≫
        (Functor.isoWhiskerRight
          (TopCat.Sheaf.pullbackComp (A := Type w) g h)
          (TopCat.Sheaf.pullback (Type w) f)).inv ≫
        (Functor.associator _ _ _).hom ≫
        (Functor.isoWhiskerLeft
          (TopCat.Sheaf.pullback (Type w) h)
          (TopCat.Sheaf.pullbackComp (A := Type w) f g)).hom ≫
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom =
      eqToHom (by simp) := by
  let e₁ := TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight
    (TopCat.Sheaf.pullbackComp (A := Type w) g h)
    (TopCat.Sheaf.pullback (Type w) f)
  let e₃ := Functor.isoWhiskerLeft
    (TopCat.Sheaf.pullback (Type w) h)
    (TopCat.Sheaf.pullbackComp (A := Type w) f g)
  let e₄ := TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have hcomp : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom := by
    exact congrArg Iso.hom (sheafPullbackComp_assoc f g h)
  rw [hcomp]
  ext 𝒢
  simpa using Iso.inv_hom_id_app e₁ 𝒢

public theorem sheafPullback_inverse_endpoint {W X Y Z : TopCat.{w}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (𝒢 : TopCat.Sheaf (Type w) Z) :
    (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app 𝒢 ≫
      (TopCat.Sheaf.pullback (Type w) f).map
        ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app 𝒢) ≫
      (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
        ((TopCat.Sheaf.pullback (Type w) h).obj 𝒢) =
    (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app 𝒢 := by
  apply (cancel_mono ((TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app 𝒢)).1
  have hcoh :
      (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app 𝒢 ≫
          (TopCat.Sheaf.pullback (Type w) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app 𝒢) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
            ((TopCat.Sheaf.pullback (Type w) h).obj 𝒢) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app 𝒢 =
        eqToHom (by simp) := by
    simpa [Category.assoc] using
      congrArg (fun α ↦ α.app 𝒢) (sheafPullback_pseudofunctor_associativity f g h)
  have hid :
      eqToHom (by simp) =
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app 𝒢 ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app 𝒢 := by
    simpa using
      (Iso.inv_hom_id_app (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h) 𝒢).symm
  exact hcoh.trans hid

public theorem sheafPullback_mixed_endpoint {W X Y Z : TopCat.{w}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (𝒢 : TopCat.Sheaf (Type w) Z) :
      (TopCat.Sheaf.pullback (Type w) f).map
          ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app 𝒢) ≫
        (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
          ((TopCat.Sheaf.pullback (Type w) h).obj 𝒢) =
      (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).hom.app 𝒢 ≫
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app 𝒢 := by
  have hendpoint :=
    sheafPullback_inverse_endpoint (f := f) (g := g) (h := h) 𝒢
  let Aiso := TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)
  let Ciso := TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h
  let B :=
    (TopCat.Sheaf.pullback (Type w) f).map
      ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app 𝒢) ≫
    (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
      ((TopCat.Sheaf.pullback (Type w) h).obj 𝒢)
  change B = Aiso.hom.app 𝒢 ≫ Ciso.inv.app 𝒢
  have hstart : B = Aiso.hom.app 𝒢 ≫ (Aiso.inv.app 𝒢 ≫ B) := by
    rw [← Category.assoc, Aiso.hom_inv_id_app]
    simp
  have hend :
      Aiso.hom.app 𝒢 ≫ (Aiso.inv.app 𝒢 ≫ B) =
        Aiso.hom.app 𝒢 ≫ Ciso.inv.app 𝒢 := by
    simpa [Aiso, Ciso, B, Category.assoc] using
      congrArg (fun t ↦ Aiso.hom.app 𝒢 ≫ t) hendpoint
  exact hstart.trans hend

public theorem pullback_refinement_iso_coherence
    {W X Y Z : TopCat.{max u v}} (f : W ⟶ X) (p : X ⟶ Y) (a : Y ⟶ Z)
    {p' : X ⟶ Z} (hp : p ≫ a = p')
    {q : W ⟶ Y} (hq : f ≫ p = q)
    {q' : W ⟶ Z} (hq' : f ≫ p' = q') (hsmall : q ≫ a = q')
    (𝒢 : TopCat.Sheaf (Type (max u v)) Z)
    (𝒦 : TopCat.Sheaf (Type (max u v)) Y)
    (α : (TopCat.Sheaf.pullback (Type (max u v)) a).obj 𝒢 ⟶ 𝒦) :
    (TopCat.Sheaf.pullback (Type (max u v)) f).map
        (((eqToIso (congrArg (pullback (Type (max u v))) hp)).inv.app 𝒢) ≫
          ((pullbackComp p a).inv.app 𝒢) ≫
            (TopCat.Sheaf.pullback (Type (max u v)) p).map α) ≫
      ((pullbackComp f p).hom.app 𝒦) ≫
        (eqToHom (congrArg (pullback (Type (max u v))) hq)).app 𝒦 =
    ((pullbackComp f p').hom.app 𝒢) ≫
      (eqToHom (congrArg (pullback (Type (max u v))) hq')).app 𝒢 ≫
        ((eqToIso (congrArg (pullback (Type (max u v))) hsmall)).inv.app 𝒢) ≫
          ((pullbackComp q a).inv.app 𝒢) ≫
            (TopCat.Sheaf.pullback (Type (max u v)) q).map α := by
  subst p'
  subst q
  subst q'
  have hnat :=
    (TopCat.Sheaf.pullbackComp (A := Type (max u v)) f p).hom.naturality α
  have hmix :=
    sheafPullback_mixed_endpoint (f := f) (g := p) (h := a) 𝒢
  have hcalc :
      (TopCat.Sheaf.pullback (Type (max u v)) f).map
          ((pullbackComp p a).inv.app 𝒢) ≫
        (TopCat.Sheaf.pullback (Type (max u v)) f).map
          ((TopCat.Sheaf.pullback (Type (max u v)) p).map α) ≫
          (pullbackComp f p).hom.app 𝒦 =
      (pullbackComp f (p ≫ a)).hom.app 𝒢 ≫
        (pullbackComp (f ≫ p) a).inv.app 𝒢 ≫
          (TopCat.Sheaf.pullback (Type (max u v)) (f ≫ p)).map α := by
    calc
      (TopCat.Sheaf.pullback (Type (max u v)) f).map
          ((pullbackComp p a).inv.app 𝒢) ≫
        (TopCat.Sheaf.pullback (Type (max u v)) f).map
          ((TopCat.Sheaf.pullback (Type (max u v)) p).map α) ≫
          (pullbackComp f p).hom.app 𝒦 =
        (TopCat.Sheaf.pullback (Type (max u v)) f).map
            ((pullbackComp p a).inv.app 𝒢) ≫
          (pullbackComp f p).hom.app
              ((TopCat.Sheaf.pullback (Type (max u v)) a).obj 𝒢) ≫
            (TopCat.Sheaf.pullback (Type (max u v)) (f ≫ p)).map α := by
          simpa [Category.assoc] using
            congrArg
              (fun m ↦
                (TopCat.Sheaf.pullback (Type (max u v)) f).map
                  ((pullbackComp p a).inv.app 𝒢) ≫ m)
              hnat
      _ = (pullbackComp f (p ≫ a)).hom.app 𝒢 ≫
          (pullbackComp (f ≫ p) a).inv.app 𝒢 ≫
            (TopCat.Sheaf.pullback (Type (max u v)) (f ≫ p)).map α := by
          simpa [Category.assoc] using
            congrArg
              (fun m ↦ m ≫
                (TopCat.Sheaf.pullback (Type (max u v)) (f ≫ p)).map α)
              hmix
  simpa [Functor.map_comp, Category.assoc, eqToHom_map] using hcalc

public theorem pullback_refinement_iterated_map_heq
    {X Y Z : TopCat.{max u v}} (p : X ⟶ Y) (a : Y ⟶ Z)
    {p' : X ⟶ Z} (hp : p ≫ a = p')
    (𝒢 : TopCat.Sheaf (Type (max u v)) Z)
    (𝒦 : TopCat.Sheaf (Type (max u v)) Y)
    (α : (TopCat.Sheaf.pullback (Type (max u v)) a).obj 𝒢 ⟶ 𝒦)
    (U : Opens Z)
    (s : (((TopCat.Sheaf.pullback (Type (max u v)) a).obj 𝒢).presheaf).obj
      (op ((Opens.map a).obj U))) :
    ((((eqToIso (congrArg (pullback (Type (max u v))) hp)).inv.app 𝒢) ≫
          ((pullbackComp p a).inv.app 𝒢) ≫
            (TopCat.Sheaf.pullback (Type (max u v)) p).map α).1.app
        (op ((Opens.map p').obj U))
        (cast
          (congrArg
            (fun r : X ⟶ Z ↦
              (((TopCat.Sheaf.pullback (Type (max u v)) r).obj 𝒢).presheaf).obj
                (op ((Opens.map r).obj U)))
            hp)
          (_root_.iteratedPullbackSectionsMap p a 𝒢 U s))) ≍
      (((pullbackPushforwardAdjunction (Type (max u v)) p).unit.app 𝒦).1.app
        (op ((Opens.map a).obj U)) (α.1.app (op ((Opens.map a).obj U)) s)) := by
  subst p'
  dsimp [_root_.iteratedPullbackSectionsMap]
  let V := (Opens.map a).obj U
  let u :=
    (((pullbackPushforwardAdjunction (Type (max u v)) p).unit.app
      ((TopCat.Sheaf.pullback (Type (max u v)) a).obj 𝒢)).1.app (op V)) s
  have hcancel :=
    congrFun
      (congrArg
        (fun f ↦ f.1.app (op ((Opens.map p).obj V)))
        ((pullbackComp p a).hom_inv_id_app 𝒢))
      u
  have hmap_cancel :=
    congrArg
      (fun z ↦
        (((TopCat.Sheaf.pullback (Type (max u v)) p).map α).1.app
          (op ((Opens.map p).obj V))) z)
      hcancel
  have hnat :=
    congrFun
      (congrArg (fun f ↦ f.1.app (op V))
        ((pullbackPushforwardAdjunction (Type (max u v)) p).unit.naturality α))
      s
  simpa [V, u, ConcreteCategory.comp_apply] using hmap_cancel.trans hnat.symm

public theorem sheaf_hom_app_cast_heq {X : TopCat.{max u v}}
    {𝓕 𝓖 : TopCat.Sheaf (Type (max u v)) X} (α : 𝓕 ⟶ 𝓖)
    {U V : Opens X} (h : U = V) (s : 𝓕.1.obj (op U)) :
    α.1.app (op V)
        (cast (congrArg (fun W ↦ 𝓕.1.obj (op W)) h) s) ≍
      α.1.app (op U) s := by
  subst h
  rfl

public theorem heq_trans_fun_arg_of_eq
    {α : Sort uJ} {β γ δ : Sort uT} (f : α → β) {x y : α}
    (hxy : x = y) {z : γ} {w : δ} (hw : w ≍ f y) (hz : f x ≍ z) :
    w ≍ z := by
  subst hxy
  exact hw.trans hz

public theorem sheafPullbackComp_id_comp {X Y : TopCat.{max u v}} (f : X ⟶ Y) :
    TopCat.Sheaf.pullbackComp (A := Type (max u v)) f (𝟙 Y) =
      Functor.isoWhiskerRight
          ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)).leftAdjointIdIso
            (eqToIso rfl))
          (TopCat.Sheaf.pullback (Type (max u v)) f) ≪≫
        Functor.leftUnitor (TopCat.Sheaf.pullback (Type (max u v)) f) := by
  simpa [sheafPullbackComp_def] using
    (Adjunction.leftAdjointCompIso_id_comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type (max u v)) f)
      (eqToIso rfl)
      (eqToIso rfl)
      (by
        ext ℱ
        rfl))

public theorem pullbackId_homEquiv_symm_pushforwardId
    {Y : TopCat.{max u v}} (P : TopCat.Sheaf (Type (max u v)) Y) :
    (((pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)).homEquiv P P).symm
      ⟨(pushforwardId P.presheaf).inv ≫
        (TopCat.Presheaf.pushforwardEq (show 𝟙 Y = 𝟙 Y from rfl) P.presheaf).inv⟩) =
      (((pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)).leftAdjointIdIso
        (eqToIso rfl)).hom.app P) := by
  apply Equiv.injective
    ((pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)).homEquiv P P)
  rw [Equiv.apply_symm_apply]
  have h :=
    CategoryTheory.unit_conjugateEquiv
      CategoryTheory.Adjunction.id
      (pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y))
      (((pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)).leftAdjointIdIso
        (eqToIso rfl)).hom)
      P
  have hunit :
      ((pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)).homEquiv P P)
          (((pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)).leftAdjointIdIso
            (eqToIso rfl)).hom.app P) =
        eqToHom (show
          (pushforward (Type (max u v)) (𝟙 Y)).obj P = P by rfl) := by
    simpa [Adjunction.homEquiv_unit] using h.symm
  rw [hunit]
  apply Sheaf.hom_ext
  ext U x
  simp [TopCat.Presheaf.pushforwardEq, pushforwardId]
  change x = x
  rfl

public theorem pulledBackDiagramMap_id_aux
    {X Y : TopCat.{max u v}} (p : X ⟶ Y) {g : Y ⟶ Y} (hg : g = 𝟙 Y)
    (hpg : p ≫ g = p) (P : TopCat.Sheaf (Type (max u v)) Y) :
    ((eqToIso (congrArg (pullback (Type (max u v))) hpg)).inv.app P) ≫
        ((pullbackComp p g).inv.app P) ≫
          (pullback (Type (max u v)) p).map
            (((pullbackPushforwardAdjunction (Type (max u v)) g).homEquiv P P).symm
              ⟨(pushforwardId P.presheaf).inv ≫
                (TopCat.Presheaf.pushforwardEq hg P.presheaf).inv⟩) =
      𝟙 ((pullback (Type (max u v)) p).obj P) := by
  subst hg
  cases hpg
  rw [sheafPullbackComp_id_comp.{u, v} p]
  have hid := pullbackId_homEquiv_symm_pushforwardId.{u, v} P
  rw [hid]
  simp [Iso.trans_inv, Functor.whiskerRight_app, Functor.leftUnitor_inv_app]
  simpa [Functor.map_comp] using congrArg
    ((pullback (Type (max u v)) p).map)
    ((((pullbackPushforwardAdjunction (Type (max u v)) (𝟙 Y)).leftAdjointIdIso
      (eqToIso rfl)).inv_hom_id_app P))

public theorem homEquiv_conjugateEquiv_exchange
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (τ : L₂ ⟶ L₁) {X : C} {Y : D} (f : L₁.obj X ⟶ Y) :
    (adj₂.homEquiv X Y) (τ.app X ≫ f) =
      (adj₁.homEquiv X Y) f ≫ (conjugateEquiv adj₁ adj₂ τ).app Y := by
  have h1 : (adj₂.homEquiv X Y) (τ.app X ≫ f) =
      (adj₂.unit.app X ≫ R₂.map (τ.app X)) ≫ R₂.map f := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    rfl
  have h2 : (adj₁.homEquiv X Y) f ≫ (conjugateEquiv adj₁ adj₂ τ).app Y =
      (adj₁.unit.app X ≫ (conjugateEquiv adj₁ adj₂ τ).app (L₁.obj X)) ≫ R₂.map f := by
    rw [Adjunction.homEquiv_unit, Category.assoc, Category.assoc]
    exact congrArg (fun t ↦ adj₁.unit.app X ≫ t)
      ((conjugateEquiv adj₁ adj₂ τ).naturality f)
  rw [h1, h2, ← unit_conjugateEquiv]

public theorem stagePullbackMap_comp_aux
    {X Y Z : TopCat.{max u v}} {f : X ⟶ Y} {g : Y ⟶ Z} {c : X ⟶ Z}
    (hfg : c = f ≫ g)
    {PZ : TopCat.Sheaf (Type (max u v)) Z}
    {PY : TopCat.Sheaf (Type (max u v)) Y}
    {PX : TopCat.Sheaf (Type (max u v)) X}
    (α : PZ ⟶ (pushforward (Type (max u v)) g).obj PY)
    (β : PY ⟶ (pushforward (Type (max u v)) f).obj PX) :
    (((pullbackPushforwardAdjunction (Type (max u v)) c).homEquiv PZ PX).symm
        (α ≫ (pushforward (Type (max u v)) g).map β ≫
          ⟨(TopCat.Presheaf.pushforwardEq hfg PX.presheaf).inv⟩)) =
      ((eqToIso (congrArg (pullback (Type (max u v))) hfg)).hom.app PZ) ≫
        ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).inv.app PZ) ≫
          (pullback (Type (max u v)) f).map
            (((pullbackPushforwardAdjunction (Type (max u v)) g).homEquiv PZ PY).symm α) ≫
          (((pullbackPushforwardAdjunction (Type (max u v)) f).homEquiv PY PX).symm β) := by
  subst hfg
  symm
  rw [← Adjunction.homEquiv_apply_eq]
  have hex := homEquiv_conjugateEquiv_exchange
    ((pullbackPushforwardAdjunction (Type (max u v)) g).comp
      (pullbackPushforwardAdjunction (Type (max u v)) f))
    (pullbackPushforwardAdjunction (Type (max u v)) (f ≫ g))
    ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).inv)
    (f :=
      (pullback (Type (max u v)) f).map
          (((pullbackPushforwardAdjunction (Type (max u v)) g).homEquiv PZ PY).symm α) ≫
        (((pullbackPushforwardAdjunction (Type (max u v)) f).homEquiv PY PX).symm β))
  have hconj :
      (conjugateEquiv
          ((pullbackPushforwardAdjunction (Type (max u v)) g).comp
            (pullbackPushforwardAdjunction (Type (max u v)) f))
          (pullbackPushforwardAdjunction (Type (max u v)) (f ≫ g))
          ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).inv)).app PX =
        (eqToIso
          (show
            pushforward (Type (max u v)) f ⋙ pushforward (Type (max u v)) g =
              pushforward (Type (max u v)) (f ≫ g) from rfl)).hom.app PX := by
    have hnat :
        conjugateEquiv
            ((pullbackPushforwardAdjunction (Type (max u v)) g).comp
              (pullbackPushforwardAdjunction (Type (max u v)) f))
            (pullbackPushforwardAdjunction (Type (max u v)) (f ≫ g))
            ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).inv) =
          (eqToIso
            (show
              pushforward (Type (max u v)) f ⋙ pushforward (Type (max u v)) g =
                pushforward (Type (max u v)) (f ≫ g) from rfl)).hom := by
      rw [sheafPullbackComp_def f g]
      exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
        (pullbackPushforwardAdjunction (Type (max u v)) g)
        (pullbackPushforwardAdjunction (Type (max u v)) f)
        (pullbackPushforwardAdjunction (Type (max u v)) (f ≫ g))
        (eqToIso
          (show
            pushforward (Type (max u v)) f ⋙ pushforward (Type (max u v)) g =
              pushforward (Type (max u v)) (f ≫ g) from rfl))
    exact congrArg (fun η ↦ η.app PX) hnat
  rw [hconj] at hex
  let γ :=
    (((pullbackPushforwardAdjunction (Type (max u v)) g).homEquiv PZ PY).symm α)
  let δ :=
    (((pullbackPushforwardAdjunction (Type (max u v)) f).homEquiv PY PX).symm β)
  have hcomp :
      (((pullbackPushforwardAdjunction (Type (max u v)) f).homEquiv
            ((pullback (Type (max u v)) g).obj PZ) PX).trans
          ((pullbackPushforwardAdjunction (Type (max u v)) g).homEquiv PZ
            ((pushforward (Type (max u v)) f).obj PX)))
        ((pullback (Type (max u v)) f).map γ ≫ δ) =
        α ≫ (pushforward (Type (max u v)) g).map β := by
    rw [Equiv.trans_apply]
    have hf :
        ((pullbackPushforwardAdjunction (Type (max u v)) f).homEquiv
            ((pullback (Type (max u v)) g).obj PZ) PX)
          ((pullback (Type (max u v)) f).map γ ≫ δ) =
        γ ≫ β := by
      rw [Adjunction.homEquiv_naturality_left]
      simp [γ, δ]
    rw [hf]
    rw [Adjunction.homEquiv_naturality_right]
    simp [γ]
  have hex' :
      ((pullbackPushforwardAdjunction (Type (max u v)) (f ≫ g)).homEquiv PZ PX)
          ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).inv.app PZ ≫
            (pullback (Type (max u v)) f).map γ ≫ δ) =
        (α ≫ (pushforward (Type (max u v)) g).map β) ≫
          (eqToIso
            (show
              pushforward (Type (max u v)) f ⋙ pushforward (Type (max u v)) g =
                pushforward (Type (max u v)) (f ≫ g) from rfl)).hom.app PX := by
    calc
      ((pullbackPushforwardAdjunction (Type (max u v)) (f ≫ g)).homEquiv PZ PX)
          ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) f g).inv.app PZ ≫
            (pullback (Type (max u v)) f).map γ ≫ δ) =
        (((pullbackPushforwardAdjunction (Type (max u v)) f).homEquiv
              ((pullback (Type (max u v)) g).obj PZ) PX).trans
            ((pullbackPushforwardAdjunction (Type (max u v)) g).homEquiv PZ
              ((pushforward (Type (max u v)) f).obj PX)))
          ((pullback (Type (max u v)) f).map γ ≫ δ) ≫
            (eqToIso
              (show
                pushforward (Type (max u v)) f ⋙ pushforward (Type (max u v)) g =
                  pushforward (Type (max u v)) (f ≫ g) from rfl)).hom.app PX := by
          simpa [Adjunction.comp_homEquiv, Category.assoc, γ, δ] using hex
      _ = (α ≫ (pushforward (Type (max u v)) g).map β) ≫
          (eqToIso
            (show
              pushforward (Type (max u v)) f ⋙ pushforward (Type (max u v)) g =
                pushforward (Type (max u v)) (f ≫ g) from rfl)).hom.app PX := by
          rw [hcomp]
  simpa [γ, δ, TopCat.Presheaf.pushforwardEq, Category.assoc] using hex'

/-- Identity compatibility for the pulled-back stage-sheaf transition maps. -/
public theorem pulledBackDiagramMap_id (i : I) :
    setup.pulledBackDiagramMap (𝟙 i) = 𝟙 _ := by
  dsimp [pulledBackDiagramMap, stagePullbackMap]
  rw [setup.stageMap_id i]
  simpa using
    pulledBackDiagramMap_id_aux.{u, v} (limit.π F i) (F.map_id i) (limit.w F (𝟙 i))
      (setup.stageSheaf i)

public theorem stageMap_unit_pulledBackDiagramMap_naturality {j k : I} (a : j ⟶ k) :
    setup.stageMap a ≫
        (pushforward (Type (max u v)) (F.map a)).map
          ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F j)).unit.app
            (setup.stageSheaf j)) ≫
        (eqToHom (by rfl) :
          (pushforward (Type (max u v)) (F.map a)).obj
              ((pushforward (Type (max u v)) (limit.π F j)).obj
                ((pullback (Type (max u v)) (limit.π F j)).obj (setup.stageSheaf j))) ⟶
            (pushforward (Type (max u v)) (limit.π F j ≫ F.map a)).obj
              ((pullback (Type (max u v)) (limit.π F j)).obj (setup.stageSheaf j))) ≫
        (show
          (pushforward (Type (max u v)) (limit.π F j ≫ F.map a)).obj
              ((pullback (Type (max u v)) (limit.π F j)).obj (setup.stageSheaf j)) ⟶
            (pushforward (Type (max u v)) (limit.π F k)).obj
              ((pullback (Type (max u v)) (limit.π F j)).obj (setup.stageSheaf j)) from
          ⟨(TopCat.Presheaf.pushforwardEq (limit.w F a)
            (((pullback (Type (max u v)) (limit.π F j)).obj
              (setup.stageSheaf j)).presheaf)).hom⟩) =
      (pullbackPushforwardAdjunction (Type (max u v)) (limit.π F k)).unit.app
          (setup.stageSheaf k) ≫
        (pushforward (Type (max u v)) (limit.π F k)).map
          (setup.pulledBackDiagramMap a) := by
  have haux := stagePullbackMap_comp_aux.{u, v}
    (f := limit.π F j) (g := F.map a) (c := limit.π F k)
    (limit.w F a).symm
    (setup.stageMap a)
    ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F j)).unit.app
      (setup.stageSheaf j))
  apply_fun
    ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F k)).homEquiv
      (setup.stageSheaf k)
      ((pullback (Type (max u v)) (limit.π F j)).obj (setup.stageSheaf j))) at haux
  have hunit :
      (((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F j)).homEquiv
          (setup.stageSheaf j)
          ((pullback (Type (max u v)) (limit.π F j)).obj (setup.stageSheaf j))).symm
        ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F j)).unit.app
          (setup.stageSheaf j))) =
        𝟙 ((pullback (Type (max u v)) (limit.π F j)).obj (setup.stageSheaf j)) := by
    rw [Equiv.symm_apply_eq]
    exact Adjunction.homEquiv_id
      (pullbackPushforwardAdjunction (Type (max u v)) (limit.π F j))
      (setup.stageSheaf j)
  simpa [pulledBackDiagramMap, stagePullbackMap, hunit, Adjunction.homEquiv_unit,
    Category.assoc] using
    haux

/-- The sheaf-level map obtained by first viewing a stage sheaf over `X_i`, then applying the
unit for the projection from the inverse-limit space. -/
public noncomputable def projectionStageToLimitSheafMap
    {i : I} (A : (Over i)ᵒᵖ) :
    (setup.projectionPushforwardDiagram i).obj A ⟶
      (pushforward (Type (max u v)) (limit.π F i)).obj
        ((pullback (Type (max u v)) (limit.π F A.unop.left)).obj
          (setup.stageSheaf A.unop.left)) :=
  (pushforward (Type (max u v)) (F.map A.unop.hom)).map
      ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F A.unop.left)).unit.app
        (setup.stageSheaf A.unop.left)) ≫
    ⟨(TopCat.Presheaf.pushforwardEq (limit.w F A.unop.hom).symm
      (((pullback (Type (max u v)) (limit.π F A.unop.left)).obj
        (setup.stageSheaf A.unop.left)).presheaf)).inv⟩

/-- The specialized composite naturality square used to compare the over-category transition with
the pulled-back transition after pushing everything to the fixed space `X_i`. -/
public theorem projectionStageToLimitSheafMap_naturality
    {i : I} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    (setup.projectionPushforwardDiagram i).map u ≫
        setup.projectionStageToLimitSheafMap B =
      setup.projectionStageToLimitSheafMap A ≫
        (pushforward (Type (max u v)) (limit.π F i)).map
          (setup.pulledBackDiagramMap u.unop.left) := by
  apply Sheaf.hom_ext
  have hcast :=
    pushforwardEq_comp_inv_naturality.{u, v}
      (limit.w F u.unop.left).symm
      (projectionPushforwardMap_eq F u)
      (limit.w F B.unop.hom).symm
      (limit.w F A.unop.hom).symm
      (setup.stageMap u.unop.left).1
      ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F B.unop.left)).unit.app
        (setup.stageSheaf B.unop.left)).1
  have hunit := congrArg (fun e ↦ e.1)
    (setup.stageMap_unit_pulledBackDiagramMap_naturality u.unop.left)
  dsimp [projectionStageToLimitSheafMap, projectionPushforwardDiagram, projectionPushforwardMap]
  change
    (TopCat.Presheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map
        (setup.stageMap u.unop.left).1 ≫
      (TopCat.Presheaf.pushforwardEq (projectionPushforwardMap_eq F u)
          (setup.stageSheaf B.unop.left).presheaf).inv ≫
      (TopCat.Presheaf.pushforward (Type (max u v)) (F.map B.unop.hom)).map
        ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F B.unop.left)).unit.app
          (setup.stageSheaf B.unop.left)).1 ≫
      (TopCat.Presheaf.pushforwardEq (limit.w F B.unop.hom).symm
        (((pullback (Type (max u v)) (limit.π F B.unop.left)).obj
          (setup.stageSheaf B.unop.left)).presheaf)).inv =
    (TopCat.Presheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map
        ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F A.unop.left)).unit.app
          (setup.stageSheaf A.unop.left)).1 ≫
      (TopCat.Presheaf.pushforwardEq (limit.w F A.unop.hom).symm
        (((pullback (Type (max u v)) (limit.π F A.unop.left)).obj
          (setup.stageSheaf A.unop.left)).presheaf)).inv ≫
      (TopCat.Presheaf.pushforward (Type (max u v)) (limit.π F i)).map
        (setup.pulledBackDiagramMap u.unop.left).1
  have hunitPush := congrArg
    (fun e ↦
      (TopCat.Presheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map e ≫
        (TopCat.Presheaf.pushforwardEq (limit.w F A.unop.hom).symm
          (((pullback (Type (max u v)) (limit.π F B.unop.left)).obj
            (setup.stageSheaf B.unop.left)).presheaf)).inv)
    hunit
  have hnatCast :
      (TopCat.Presheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map
          (((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F A.unop.left)).unit.app
              (setup.stageSheaf A.unop.left) ≫
            (pushforward (Type (max u v)) (limit.π F A.unop.left)).map
              (setup.pulledBackDiagramMap u.unop.left)).1) ≫
        (TopCat.Presheaf.pushforwardEq (limit.w F A.unop.hom).symm
          (((pullback (Type (max u v)) (limit.π F B.unop.left)).obj
            (setup.stageSheaf B.unop.left)).presheaf)).inv =
      (TopCat.Presheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map
          ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F A.unop.left)).unit.app
            (setup.stageSheaf A.unop.left)).1 ≫
        (TopCat.Presheaf.pushforwardEq (limit.w F A.unop.hom).symm
          (((pullback (Type (max u v)) (limit.π F A.unop.left)).obj
            (setup.stageSheaf A.unop.left)).presheaf)).inv ≫
        (TopCat.Presheaf.pushforward (Type (max u v)) (limit.π F i)).map
          (setup.pulledBackDiagramMap u.unop.left).1 := by
    simpa [TopCat.Sheaf.pushforward_map, Functor.map_comp, Category.assoc] using
      congrArg
        (fun t ↦
          (TopCat.Presheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map
              ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F A.unop.left)).unit.app
                (setup.stageSheaf A.unop.left)).1 ≫ t)
        (pushforwardEq_inv_naturality.{max u v, max u v}
          (limit.w F A.unop.hom).symm (setup.pulledBackDiagramMap u.unop.left).1)
  exact hcast.symm.trans (hunitPush.trans hnatCast)

/-- The same naturality square, specialized to the over-category morphism attached to a
composable pair `i ⟶ j ⟶ k`. This is the exact composite square used in the cocycle proof for the
pulled-back diagram on the limit space. -/
public theorem projectionStageToLimitSheafMap_comp_naturality
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    (pushforward (Type (max u v)) (F.map b)).map (setup.stageMap a) ≫
        (eqToHom (by rfl) :
          (pushforward (Type (max u v)) (F.map b)).obj
              ((pushforward (Type (max u v)) (F.map a)).obj (setup.stageSheaf i)) ⟶
            (pushforward (Type (max u v)) (F.map a ≫ F.map b)).obj
              (setup.stageSheaf i)) ≫
        (show
          (pushforward (Type (max u v)) (F.map a ≫ F.map b)).obj (setup.stageSheaf i) ⟶
            (pushforward (Type (max u v)) (F.map (a ≫ b))).obj (setup.stageSheaf i) from
          ⟨(TopCat.Presheaf.pushforwardEq (F.map_comp a b).symm
            (setup.stageSheaf i).presheaf).hom⟩) ≫
        setup.projectionStageToLimitSheafMap (op (Over.mk (a ≫ b) : Over k)) =
      setup.projectionStageToLimitSheafMap (op (Over.mk b : Over k)) ≫
        (pushforward (Type (max u v)) (limit.π F k)).map
          (setup.pulledBackDiagramMap a) := by
  let A : (Over k)ᵒᵖ := op (Over.mk b)
  let B : (Over k)ᵒᵖ := op (Over.mk (a ≫ b))
  let uOver : B.unop ⟶ A.unop := Over.homMk a (by simp [A, B])
  let u : A ⟶ B := op uOver
  have hnat := setup.projectionStageToLimitSheafMap_naturality u
  dsimp [A, B, u, uOver, projectionPushforwardDiagram, projectionPushforwardMap] at hnat
  simpa [projectionPushforwardMap_eq, Category.assoc] using hnat

/-- The preceding composite naturality square after precomposing with the outer transition
`stageMap b` and using the cocycle identity for `stageMap (a ≫ b)`. This is the form needed
directly in the composition proof for the pulled-back diagram. -/
public theorem stageMap_projectionStageToLimitSheafMap_comp_naturality
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    setup.stageMap (a ≫ b) ≫
        setup.projectionStageToLimitSheafMap (op (Over.mk (a ≫ b) : Over k)) =
      setup.stageMap b ≫
        setup.projectionStageToLimitSheafMap (op (Over.mk b : Over k)) ≫
          (pushforward (Type (max u v)) (limit.π F k)).map
            (setup.pulledBackDiagramMap a) := by
  rw [setup.stageMap_comp b a]
  have hnat := setup.projectionStageToLimitSheafMap_comp_naturality a b
  simpa [Category.assoc] using congrArg (fun t ↦ setup.stageMap b ≫ t) hnat

/-- The composite naturality square in the exact unit form used to prove functoriality of the
pulled-back stage diagram.  After applying the projection unit at stage `k`, the transition for
`a ≫ b` agrees with the two-step transition through `b` and then `a`. -/
public theorem stageMap_unit_pulledBackDiagramMap_comp_naturality
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    (pullbackPushforwardAdjunction (Type (max u v)) (limit.π F k)).unit.app
        (setup.stageSheaf k) ≫
      (pushforward (Type (max u v)) (limit.π F k)).map
        (setup.pulledBackDiagramMap (a ≫ b)) =
    (pullbackPushforwardAdjunction (Type (max u v)) (limit.π F k)).unit.app
        (setup.stageSheaf k) ≫
      (pushforward (Type (max u v)) (limit.π F k)).map
        (setup.pulledBackDiagramMap b ≫ setup.pulledBackDiagramMap a) := by
  rw [Functor.map_comp]
  have hleft :
    (pullbackPushforwardAdjunction (Type (max u v)) (limit.π F k)).unit.app
          (setup.stageSheaf k) ≫
        (pushforward (Type (max u v)) (limit.π F k)).map
          (setup.pulledBackDiagramMap (a ≫ b)) =
      setup.stageMap (a ≫ b) ≫
        setup.projectionStageToLimitSheafMap (op (Over.mk (a ≫ b) : Over k)) := by
    simpa using (setup.stageMap_unit_pulledBackDiagramMap_naturality (a ≫ b)).symm
  have hmid :
      setup.stageMap (a ≫ b) ≫
          setup.projectionStageToLimitSheafMap (op (Over.mk (a ≫ b) : Over k)) =
        setup.stageMap b ≫
          setup.projectionStageToLimitSheafMap (op (Over.mk b : Over k)) ≫
            (pushforward (Type (max u v)) (limit.π F k)).map
              (setup.pulledBackDiagramMap a) := by
    simpa [Category.assoc] using
      setup.stageMap_projectionStageToLimitSheafMap_comp_naturality a b
  have hright :
      setup.stageMap b ≫
          setup.projectionStageToLimitSheafMap (op (Over.mk b : Over k)) ≫
            (pushforward (Type (max u v)) (limit.π F k)).map
              (setup.pulledBackDiagramMap a) =
        (pullbackPushforwardAdjunction (Type (max u v)) (limit.π F k)).unit.app
            (setup.stageSheaf k) ≫
          (pushforward (Type (max u v)) (limit.π F k)).map (setup.pulledBackDiagramMap b) ≫
            (pushforward (Type (max u v)) (limit.π F k)).map
              (setup.pulledBackDiagramMap a) := by
    have hb := congrArg
      (fun t ↦ t ≫ (pushforward (Type (max u v)) (limit.π F k)).map
        (setup.pulledBackDiagramMap a))
      (setup.stageMap_unit_pulledBackDiagramMap_naturality b)
    simpa [Category.assoc] using hb
  exact hleft.trans (hmid.trans hright)

/-- Composition compatibility for the adjoint pullback-form transition maps on the source stages. -/
public theorem stagePullbackMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    setup.stagePullbackMap (a ≫ b) =
      ((eqToIso (congrArg (pullback (Type (max u v))) (F.map_comp a b))).hom.app
          (setup.stageSheaf k)) ≫
        ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) (F.map a) (F.map b)).inv.app
          (setup.stageSheaf k)) ≫
        (pullback (Type (max u v)) (F.map a)).map (setup.stagePullbackMap b) ≫
        setup.stagePullbackMap a := by
  dsimp [stagePullbackMap]
  rw [setup.stageMap_comp b a]
  simpa [Category.assoc] using
    stagePullbackMap_comp_aux.{u, v}
      (f := F.map a) (g := F.map b) (c := F.map (a ≫ b))
      (F.map_comp a b)
      (setup.stageMap b)
      (setup.stageMap a)

public theorem stagePullbackMap_comp_hom {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    (stagePullbackCompIso (F := F) a b).hom.app (setup.stageSheaf k) ≫
        setup.stagePullbackMap (a ≫ b) =
      (pullback (Type (max u v)) (F.map a)).map (setup.stagePullbackMap b) ≫
        setup.stagePullbackMap a := by
  rw [setup.stagePullbackMap_comp a b]
  simpa [stagePullbackCompIso, Category.assoc] using
    congrArg
      (fun t ↦ t ≫
        (pullback (Type (max u v)) (F.map a)).map (setup.stagePullbackMap b) ≫
          setup.stagePullbackMap a)
      ((TopCat.Sheaf.pullbackComp (A := Type (max u v)) (F.map a) (F.map b)).hom_inv_id_app
        (setup.stageSheaf k))

/-- Composition compatibility for the pulled-back stage-sheaf transition maps. -/
public theorem pulledBackDiagramMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    setup.pulledBackDiagramMap (a ≫ b) =
      setup.pulledBackDiagramMap b ≫ setup.pulledBackDiagramMap a := by
  apply Equiv.injective
    ((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F k)).homEquiv
      (setup.stageSheaf k)
      ((pullback (Type (max u v)) (limit.π F i)).obj (setup.stageSheaf i)))
  simpa [Adjunction.homEquiv_unit, Functor.map_comp] using
    setup.stageMap_unit_pulledBackDiagramMap_comp_naturality a b

/-- The canonical diagram `i ↦ p_i^{-1}\mathcal{F}_i` on the inverse-limit space. -/
public noncomputable def pulledBackDiagram : Iᵒᵖ ⥤ TopCat.Sheaf (Type (max u v)) (limit F) where
  obj i := (pullback (Type (max u v)) (limit.π F i.unop)).obj (setup.stageSheaf i.unop)
  map f := setup.pulledBackDiagramMap f.unop
  map_id i := setup.pulledBackDiagramMap_id i.unop
  map_comp f g := setup.pulledBackDiagramMap_comp g.unop f.unop

/-- The colimit sheaf
`\mathcal{F} = \mathop{\mathrm{colim}}_i p_i^{-1}\mathcal{F}_i`
on the inverse-limit space. -/
noncomputable def colimitSheaf : TopCat.Sheaf (Type (max u v)) (limit F) :=
  colimit setup.pulledBackDiagram

/-- The sections functor on the inverse-limit space at `p_i^{-1}(U_i)`. -/
public abbrev limitProjectionSectionFunctor (i : I) (Uᵢ : Opens (F.obj i)) :
    TopCat.Sheaf (Type (max u v)) (limit F) ⥤ Type (max u v) :=
  (CategoryTheory.sheafSections (Opens.grothendieckTopology ↥(limit F))
      (Type (max u v))).obj (op ((Opens.map (limit.π F i)).obj Uᵢ))

/-- The over-category diagram
`a : j ⟶ i ↦ (p_j^{-1}\mathcal F_j)(p_i^{-1}(U_i))` used as the intermediate target in
the proof of Lemma 6.29.4. -/
public noncomputable def projectionPulledBackSectionDiagram (i : I) (Uᵢ : Opens (F.obj i)) :
    (Over i)ᵒᵖ ⥤ Type (max u v) :=
  (Over.forget i).op ⋙ setup.pulledBackDiagram ⋙ limitProjectionSectionFunctor (F := F) i Uᵢ

/-- The comparison from the intermediate over-category colimit of pulled-back stage sections to
the sections of the chosen colimit sheaf. This is the Lemma 6.29.1 part of the source proof,
with the over-category reindexing made explicit. -/
public noncomputable def projectionPulledBackSectionsComparison
    (i : I) (Uᵢ : Opens (F.obj i)) :
    colimit (setup.projectionPulledBackSectionDiagram i Uᵢ) ⟶
      (setup.colimitSheaf.presheaf).obj
        (op ((Opens.map (limit.π F i)).obj Uᵢ)) :=
  colimit.post ((Over.forget i).op ⋙ setup.pulledBackDiagram)
      (limitProjectionSectionFunctor (F := F) i Uᵢ) ≫
    (limitProjectionSectionFunctor (F := F) i Uᵢ).map
      (Functor.Final.colimitIso (Over.forget i).op setup.pulledBackDiagram).hom

-- Proof sketch: the limit-cone identity `p_j ≫ f_a = p_i` identifies the iterated inverse image
-- of `U_i` along `p_j` and `f_a` with the direct inverse image along `p_i`.
/-- The open pulled back along `p_j` from `f_a^{-1}(U_i)` agrees with `p_i^{-1}(U_i)`. -/
public theorem limit_projection_preimage_eq {i j : I} (a : j ⟶ i)
    (Uᵢ : Opens (F.obj i)) :
    (Opens.map (limit.π F j)).obj ((Opens.map (F.map a)).obj Uᵢ) =
      (Opens.map (limit.π F i)).obj Uᵢ := by
  -- Compare the two opens pointwise and rewrite the stage coordinate with the limit-cone
  -- relation `p_j ≫ f_a = p_i`.
  ext x
  constructor
  · intro hx
    have hπ : F.map a ((limit.π F j) x) = (limit.π F i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F a)) x
    simpa [hπ] using hx
  · intro hx
    have hπ : F.map a ((limit.π F j) x) = (limit.π F i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F a)) x
    simpa [hπ] using hx

/-- The canonical map from a stage section over `f_a^{-1}(U_i)` to the corresponding section of
`p_j^{-1}\mathcal{F}_j` over `p_i^{-1}(U_i)`. -/
public noncomputable def projectionOpenSectionToPulledBackStageMap
    (i : I) (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ) :
    setup.projectionOpenSectionValue i Uᵢ A ⟶
      (((setup.pulledBackDiagram.obj (op A.unop.left)).presheaf).obj
        (op ((Opens.map (limit.π F i)).obj Uᵢ))) :=
  (setup.projectionStageToLimitSheafMap A).1.app (op Uᵢ)

/-- Helper for Lemma 6.29.4: the projection-open map is the pullback unit along the source-stage
projection, followed by the exact `pushforwardEq` transport used in its definition. -/
public theorem projectionOpenSectionToPulledBackStageMap_eq_unit_pushforwardEq
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ)
    (s : setup.projectionOpenSectionValue i Uᵢ A) :
    setup.projectionOpenSectionToPulledBackStageMap i Uᵢ A s =
      (TopCat.Presheaf.pushforwardEq (limit.w F A.unop.hom).symm
        (((pullback (Type (max u v)) (limit.π F A.unop.left)).obj
          (setup.stageSheaf A.unop.left)).presheaf)).inv.app (op Uᵢ)
        (((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F A.unop.left)).unit.app
            (setup.stageSheaf A.unop.left)).1.app
          (op ((Opens.map (F.map A.unop.hom)).obj Uᵢ)) s) := by
  rfl

/-- The section-level naturality square comparing the over-category transition with the
pulled-back stage transition on the inverse-limit space. This is the localized composite
naturality square used by the comparison cocone. -/
public theorem projectionOpenSectionToPulledBackStageMap_naturality
    {i : I} (Uᵢ : Opens (F.obj i)) {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    (setup.projectionOpenSectionDiagram i Uᵢ).map u ≫
        setup.projectionOpenSectionToPulledBackStageMap i Uᵢ B =
        setup.projectionOpenSectionToPulledBackStageMap i Uᵢ A ≫
        (setup.pulledBackDiagram.map u.unop.left.op).1.app
          (op ((Opens.map (limit.π F i)).obj Uᵢ)) := by
  have hnat :=
    (congrArg (fun e ↦ e.1.app (op Uᵢ))
      (setup.projectionStageToLimitSheafMap_naturality u))
  simpa [projectionOpenSectionDiagram, stageSectionFunctor, projectionOpenSectionToPulledBackStageMap,
    pulledBackDiagram, TopCat.Sheaf.pushforward_map, Category.assoc] using hnat

/-- Helper for Lemma 6.29.4: the composite over-category naturality square after evaluating
sections on the fixed open of the outer stage. -/
public theorem projectionOpenSectionToPulledBackStageMap_comp_naturality
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (Uₖ : Opens (F.obj k)) :
    (setup.projectionOpenSectionDiagram k Uₖ).map
        (op (Over.homMk a (by simp) :
          (Over.mk (a ≫ b) : Over k) ⟶ (Over.mk b : Over k))) ≫
        setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk (a ≫ b) : Over k)) =
      setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk b : Over k)) ≫
        (setup.pulledBackDiagram.map a.op).1.app
          (op ((Opens.map (limit.π F k)).obj Uₖ)) := by
  simpa [projectionPulledBackSectionDiagram, limitProjectionSectionFunctor] using
    setup.projectionOpenSectionToPulledBackStageMap_naturality Uₖ
      (op (Over.homMk a (by simp) :
        (Over.mk (a ≫ b) : Over k) ⟶ (Over.mk b : Over k)))

/-- Helper for Lemma 6.29.4: the preceding composite square after precomposing with the
outer transition on sections. -/
public theorem stageMap_projectionOpenSectionToPulledBackStageMap_comp_naturality
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (Uₖ : Opens (F.obj k)) :
    (setup.stageMap (a ≫ b)).1.app (op Uₖ) ≫
        setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk (a ≫ b) : Over k)) =
      (setup.stageMap b).1.app (op Uₖ) ≫
        setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk b : Over k)) ≫
        (setup.pulledBackDiagram.map a.op).1.app
          (op ((Opens.map (limit.π F k)).obj Uₖ)) := by
  have hnat :=
    congrArg (fun e ↦ e.1.app (op Uₖ))
      (setup.stageMap_projectionStageToLimitSheafMap_comp_naturality a b)
  simpa [projectionOpenSectionToPulledBackStageMap, pulledBackDiagram,
    TopCat.Sheaf.pushforward_map, Category.assoc] using hnat

/-- Helper for Lemma 6.29.4: the composite section-level naturality square after passing to the
target over-category colimit. This is the form used when the proof has already chosen the
composite object `a ≫ b` and needs to compare it with the two-step object `b`. -/
public theorem projectionOpenSectionToPulledBackStageMap_colimit_comp_naturality
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (Uₖ : Opens (F.obj k)) :
    (setup.projectionOpenSectionDiagram k Uₖ).map
        (op (Over.homMk a (by simp) :
          (Over.mk (a ≫ b) : Over k) ⟶ (Over.mk b : Over k))) ≫
        setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk (a ≫ b) : Over k)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk (a ≫ b) : Over k)) =
      setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk b : Over k)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk b : Over k)) := by
  let u : op (Over.mk b : Over k) ⟶ op (Over.mk (a ≫ b) : Over k) :=
    op (Over.homMk a (by simp) :
      (Over.mk (a ≫ b) : Over k) ⟶ (Over.mk b : Over k))
  have hnat :=
    setup.projectionOpenSectionToPulledBackStageMap_comp_naturality a b Uₖ
  have hcolim :
      (setup.pulledBackDiagram.map a.op).1.app
            (op ((Opens.map (limit.π F k)).obj Uₖ)) ≫
          colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
            (op (Over.mk (a ≫ b) : Over k)) =
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk b : Over k)) := by
    simpa [u, projectionPulledBackSectionDiagram, limitProjectionSectionFunctor] using
      (colimit.w (setup.projectionPulledBackSectionDiagram k Uₖ) u)
  calc
    (setup.projectionOpenSectionDiagram k Uₖ).map
        (op (Over.homMk a (by simp) :
          (Over.mk (a ≫ b) : Over k) ⟶ (Over.mk b : Over k))) ≫
        setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk (a ≫ b) : Over k)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk (a ≫ b) : Over k)) =
      setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk b : Over k)) ≫
        (setup.pulledBackDiagram.map a.op).1.app
          (op ((Opens.map (limit.π F k)).obj Uₖ)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk (a ≫ b) : Over k)) := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ t ≫ colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
              (op (Over.mk (a ≫ b) : Over k)))
            hnat
    _ = setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk b : Over k)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk b : Over k)) := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ setup.projectionOpenSectionToPulledBackStageMap k Uₖ
              (op (Over.mk b : Over k)) ≫ t)
            hcolim

/-- Helper for Lemma 6.29.4: the colimit-level composite naturality square in the outer-stage
notation used by the Fubini step.  If `b : k ⟶ j` refines the outer object
`a : j ⟶ i`, then passing from `a` to the composite object `b ≫ a` and then applying the
source-to-pulled-back comparison gives the same target-colimit element as applying the comparison
at `a` directly. -/
public theorem projectionOpenSectionToPulledBackStageMap_colimit_refinement_naturality
    {i j k : I} (a : j ⟶ i) (b : k ⟶ j) (Uᵢ : Opens (F.obj i)) :
    (setup.projectionOpenSectionDiagram i Uᵢ).map
        (op (Over.homMk b (by simp) :
          (Over.mk (b ≫ a) : Over i) ⟶ (Over.mk a : Over i))) ≫
        setup.projectionOpenSectionToPulledBackStageMap i Uᵢ
          (op (Over.mk (b ≫ a) : Over i)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ)
          (op (Over.mk (b ≫ a) : Over i)) =
      setup.projectionOpenSectionToPulledBackStageMap i Uᵢ
          (op (Over.mk a : Over i)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ)
          (op (Over.mk a : Over i)) := by
  exact setup.projectionOpenSectionToPulledBackStageMap_colimit_comp_naturality b a Uᵢ

/-- Helper for Lemma 6.29.4: pointwise form of
`projectionOpenSectionToPulledBackStageMap_colimit_refinement_naturality`, used when the proof has
chosen an explicit section representative. -/
public theorem projectionOpenSectionToPulledBackStageMap_colimit_refinement_apply
    {i j k : I} (a : j ⟶ i) (b : k ⟶ j) (Uᵢ : Opens (F.obj i))
    (s : setup.projectionOpenSectionValue i Uᵢ (op (Over.mk a : Over i))) :
    colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ)
        (op (Over.mk (b ≫ a) : Over i))
        (setup.projectionOpenSectionToPulledBackStageMap i Uᵢ
          (op (Over.mk (b ≫ a) : Over i))
          ((setup.projectionOpenSectionDiagram i Uᵢ).map
            (op (Over.homMk b (by simp) :
              (Over.mk (b ≫ a) : Over i) ⟶ (Over.mk a : Over i))) s)) =
      colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ)
        (op (Over.mk a : Over i))
        (setup.projectionOpenSectionToPulledBackStageMap i Uᵢ
          (op (Over.mk a : Over i)) s) := by
  have h :=
    setup.projectionOpenSectionToPulledBackStageMap_colimit_refinement_naturality a b Uᵢ
  simpa [Category.assoc] using congrFun h s

/-- Helper for Lemma 6.29.4: the preceding colimit-level square after precomposing with the
outer transition map on sections. -/
public theorem stageMap_projectionOpenSectionToPulledBackStageMap_colimit_comp_naturality
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (Uₖ : Opens (F.obj k)) :
    (setup.stageMap (a ≫ b)).1.app (op Uₖ) ≫
        setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk (a ≫ b) : Over k)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk (a ≫ b) : Over k)) =
      (setup.stageMap b).1.app (op Uₖ) ≫
        setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk b : Over k)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk b : Over k)) := by
  have hnat :=
    setup.stageMap_projectionOpenSectionToPulledBackStageMap_comp_naturality a b Uₖ
  have hcolim :
      (setup.pulledBackDiagram.map a.op).1.app
            (op ((Opens.map (limit.π F k)).obj Uₖ)) ≫
          colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
            (op (Over.mk (a ≫ b) : Over k)) =
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk b : Over k)) := by
    let u : op (Over.mk b : Over k) ⟶ op (Over.mk (a ≫ b) : Over k) :=
      op (Over.homMk a (by simp) :
        (Over.mk (a ≫ b) : Over k) ⟶ (Over.mk b : Over k))
    simpa [u, projectionPulledBackSectionDiagram, limitProjectionSectionFunctor] using
      (colimit.w (setup.projectionPulledBackSectionDiagram k Uₖ) u)
  calc
    (setup.stageMap (a ≫ b)).1.app (op Uₖ) ≫
        setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk (a ≫ b) : Over k)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk (a ≫ b) : Over k)) =
      (setup.stageMap b).1.app (op Uₖ) ≫
        setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk b : Over k)) ≫
        (setup.pulledBackDiagram.map a.op).1.app
          (op ((Opens.map (limit.π F k)).obj Uₖ)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk (a ≫ b) : Over k)) := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ t ≫ colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
              (op (Over.mk (a ≫ b) : Over k)))
            hnat
    _ = (setup.stageMap b).1.app (op Uₖ) ≫
        setup.projectionOpenSectionToPulledBackStageMap k Uₖ
          (op (Over.mk b : Over k)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram k Uₖ)
          (op (Over.mk b : Over k)) := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ (setup.stageMap b).1.app (op Uₖ) ≫
              setup.projectionOpenSectionToPulledBackStageMap k Uₖ
                (op (Over.mk b : Over k)) ≫ t)
            hcolim

/-- Helper for Lemma 6.29.4: the stage-transition composite square in the outer-refinement
notation used in the Fubini step.  If `b : k ⟶ j` refines the outer object `a : j ⟶ i`, then
using the composite transition `b ≫ a` and then passing to the pulled-back over-colimit gives the
same element as using the outer transition `a` directly. -/
public theorem stageMap_projectionOpenSectionToPulledBackStageMap_colimit_refinement_naturality
    {i j k : I} (a : j ⟶ i) (b : k ⟶ j) (Uᵢ : Opens (F.obj i)) :
    (setup.stageMap (b ≫ a)).1.app (op Uᵢ) ≫
        setup.projectionOpenSectionToPulledBackStageMap i Uᵢ
          (op (Over.mk (b ≫ a) : Over i)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ)
          (op (Over.mk (b ≫ a) : Over i)) =
      (setup.stageMap a).1.app (op Uᵢ) ≫
        setup.projectionOpenSectionToPulledBackStageMap i Uᵢ
          (op (Over.mk a : Over i)) ≫
        colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ)
          (op (Over.mk a : Over i)) := by
  exact setup.stageMap_projectionOpenSectionToPulledBackStageMap_colimit_comp_naturality b a Uᵢ

/-- Helper for Lemma 6.29.4: pointwise form of
`stageMap_projectionOpenSectionToPulledBackStageMap_colimit_refinement_naturality`, used when a
proof has an explicit section at the outer target stage. -/
public theorem stageMap_projectionOpenSectionToPulledBackStageMap_colimit_refinement_apply
    {i j k : I} (a : j ⟶ i) (b : k ⟶ j) (Uᵢ : Opens (F.obj i))
    (s : (setup.stageSheaf i).1.obj (op Uᵢ)) :
    colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ)
        (op (Over.mk (b ≫ a) : Over i))
        (setup.projectionOpenSectionToPulledBackStageMap i Uᵢ
          (op (Over.mk (b ≫ a) : Over i))
          ((setup.stageMap (b ≫ a)).1.app (op Uᵢ) s)) =
      colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ)
        (op (Over.mk a : Over i))
        (setup.projectionOpenSectionToPulledBackStageMap i Uᵢ
          (op (Over.mk a : Over i))
          ((setup.stageMap a).1.app (op Uᵢ) s)) := by
  have h :=
    setup.stageMap_projectionOpenSectionToPulledBackStageMap_colimit_refinement_naturality
      a b Uᵢ
  simpa [Category.assoc] using congrFun h s

/-- Helper for Lemma 6.29.4: the componentwise source-to-pulled-back maps form the natural
transformation whose colimit map is the first formal comparison in the source proof. -/
public noncomputable def projectionOpenToPulledBackSectionsNatTrans
    (i : I) (Uᵢ : Opens (F.obj i)) :
    setup.projectionOpenSectionDiagram i Uᵢ ⟶
      setup.projectionPulledBackSectionDiagram i Uᵢ where
  app A := setup.projectionOpenSectionToPulledBackStageMap i Uᵢ A
  naturality := by
    intro A B u
    simpa [projectionPulledBackSectionDiagram, limitProjectionSectionFunctor] using
      setup.projectionOpenSectionToPulledBackStageMap_naturality Uᵢ u

/-- The cocone from the over-category diagram
`a : j ⟶ i ↦ \mathcal{F}_j(f_a^{-1}(U_i))`
to the sections of the colimit sheaf over `p_i^{-1}(U_i)`. -/
public noncomputable def projectionOpenSectionsComparisonCocone
    (i : I) (Uᵢ : Opens (F.obj i)) :
    Cocone (setup.projectionOpenSectionDiagram i Uᵢ) where
  pt := (setup.colimitSheaf.presheaf).obj
    (op ((Opens.map (limit.π F i)).obj Uᵢ))
  ι :=
    { app := fun A ↦
        setup.projectionOpenSectionToPulledBackStageMap i Uᵢ A ≫
          (colimit.ι setup.pulledBackDiagram (op A.unop.left)).1.app
            (op ((Opens.map (limit.π F i)).obj Uᵢ))
      naturality := fun {_ _} u ↦ by
        rw [← Category.assoc, setup.projectionOpenSectionToPulledBackStageMap_naturality Uᵢ u]
        rw [Category.assoc]
        exact congrArg
          (fun t ↦ setup.projectionOpenSectionToPulledBackStageMap i Uᵢ _ ≫ t)
          (congrArg
            (fun f ↦ f.1.app (op ((Opens.map (limit.π F i)).obj Uᵢ)))
            (colimit.w setup.pulledBackDiagram u.unop.left.op)) }

/-- The first comparison map in the source proof: send a stage section over `f_a^{-1}(U_i)` to
the corresponding pulled-back stage section over `p_i^{-1}(U_i)`, then pass to the over-category
colimit. -/
public noncomputable def projectionOpenToPulledBackSectionsColimitMap
    (i : I) (Uᵢ : Opens (F.obj i)) :
    setup.projectionOpenSectionColimit i Uᵢ ⟶
      colimit (setup.projectionPulledBackSectionDiagram i Uᵢ) := by
  change colimit (setup.projectionOpenSectionDiagram i Uᵢ) ⟶
    colimit (setup.projectionPulledBackSectionDiagram i Uᵢ)
  exact colimit.desc (setup.projectionOpenSectionDiagram i Uᵢ)
    { pt := colimit (setup.projectionPulledBackSectionDiagram i Uᵢ)
      ι :=
        { app := fun A ↦
            setup.projectionOpenSectionToPulledBackStageMap i Uᵢ A ≫
              colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ) A
          naturality := fun {_ _} u ↦ by
            rw [← Category.assoc, setup.projectionOpenSectionToPulledBackStageMap_naturality Uᵢ u]
            rw [Category.assoc]
            exact congrArg
              (fun t ↦ setup.projectionOpenSectionToPulledBackStageMap i Uᵢ _ ≫ t)
              (colimit.w (setup.projectionPulledBackSectionDiagram i Uᵢ) u) } }

/-- Helper for Lemma 6.29.4: the explicit first comparison agrees with the `colimMap` induced by
the source-to-pulled-back natural transformation. -/
public theorem projectionOpenToPulledBackSectionsColimitMap_eq_colimMap
    (i : I) (Uᵢ : Opens (F.obj i)) :
    setup.projectionOpenToPulledBackSectionsColimitMap i Uᵢ =
      colimMap (setup.projectionOpenToPulledBackSectionsNatTrans i Uᵢ) := by
  apply colimit.hom_ext
  intro A
  simp [projectionOpenToPulledBackSectionsColimitMap,
    projectionOpenToPulledBackSectionsNatTrans]
  rfl

/-- The canonical comparison map
`\mathop{\mathrm{colim}}_{a : j \to i} \mathcal{F}_j(f_a^{-1}(U_i)) \to
(\mathop{\mathrm{colim}}_j p_j^{-1}\mathcal{F}_j)(p_i^{-1}(U_i)) = \mathcal{F}(p_i^{-1}(U_i))`.
-/
noncomputable def projectionOpenSectionsComparison (i : I) (Uᵢ : Opens (F.obj i)) :
    setup.projectionOpenSectionColimit i Uᵢ ⟶
      (setup.colimitSheaf.presheaf).obj
        (op ((Opens.map (limit.π F i)).obj Uᵢ)) := by
  change _ ⟶ (setup.projectionOpenSectionsComparisonCocone i Uᵢ).pt
  exact colimit.desc _ (setup.projectionOpenSectionsComparisonCocone i Uᵢ)

/-- The explicit comparison used in the public statement is the composite of the formal
source-to-pulled-back over-colimit map and the sheaf-colimit section comparison. -/
public theorem projectionOpenToPulledBackSectionsColimitMap_comp
    (i : I) (Uᵢ : Opens (F.obj i)) :
    setup.projectionOpenToPulledBackSectionsColimitMap i Uᵢ ≫
        setup.projectionPulledBackSectionsComparison i Uᵢ =
      setup.projectionOpenSectionsComparison i Uᵢ := by
  apply colimit.hom_ext
  intro A
  change
    (colimit.ι (setup.projectionOpenSectionDiagram i Uᵢ) A ≫
        setup.projectionOpenToPulledBackSectionsColimitMap i Uᵢ) ≫
      setup.projectionPulledBackSectionsComparison i Uᵢ =
    colimit.ι (setup.projectionOpenSectionDiagram i Uᵢ) A ≫
      setup.projectionOpenSectionsComparison i Uᵢ
  have hsrc :
      colimit.ι (setup.projectionOpenSectionDiagram i Uᵢ) A ≫
          setup.projectionOpenToPulledBackSectionsColimitMap i Uᵢ =
        setup.projectionOpenSectionToPulledBackStageMap i Uᵢ A ≫
          colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ) A := by
    simp [projectionOpenToPulledBackSectionsColimitMap]
    rfl
  have htarget :
      colimit.ι (setup.projectionOpenSectionDiagram i Uᵢ) A ≫
          setup.projectionOpenSectionsComparison i Uᵢ =
        setup.projectionOpenSectionToPulledBackStageMap i Uᵢ A ≫
          (colimit.ι setup.pulledBackDiagram (op A.unop.left)).1.app
            (op ((Opens.map (limit.π F i)).obj Uᵢ)) := by
    simp [projectionOpenSectionsComparison, projectionOpenSectionsComparisonCocone]
    rfl
  rw [hsrc, htarget]
  have hleg :
      colimit.ι (setup.projectionPulledBackSectionDiagram i Uᵢ) A ≫
          setup.projectionPulledBackSectionsComparison i Uᵢ =
        (colimit.ι setup.pulledBackDiagram (op A.unop.left)).1.app
          (op ((Opens.map (limit.π F i)).obj Uᵢ)) := by
    dsimp [projectionPulledBackSectionsComparison]
    change
      (colimit.ι (((Over.forget i).op ⋙ setup.pulledBackDiagram) ⋙
            limitProjectionSectionFunctor (F := F) i Uᵢ) A ≫
          colimit.post ((Over.forget i).op ⋙ setup.pulledBackDiagram)
            (limitProjectionSectionFunctor (F := F) i Uᵢ)) ≫
        (limitProjectionSectionFunctor (F := F) i Uᵢ).map
          (Functor.Final.colimitIso (Over.forget i).op setup.pulledBackDiagram).hom =
        (colimit.ι setup.pulledBackDiagram (op A.unop.left)).1.app
          (op ((Opens.map (limit.π F i)).obj Uᵢ))
    rw [colimit.ι_post]
    simpa [Functor.map_comp] using
      congrArg
        (fun f ↦ (limitProjectionSectionFunctor (F := F) i Uᵢ).map f)
        (Functor.Final.ι_colimitIso_hom (Over.forget i).op setup.pulledBackDiagram A)
  simpa [Category.assoc] using
    congrArg
      (fun t ↦ setup.projectionOpenSectionToPulledBackStageMap i Uᵢ A ≫ t)
      hleg

end InverseLimitTypeSheafSystem

namespace SpectralInverseLimit

section

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
variable (F : I ⥤ TopCat.{max u v}) [∀ j : I, SpectralSpace ↥(F.obj j)]
variable (stageSheaf : ∀ i : I, TopCat.Sheaf (Type (max u v)) (F.obj i))
variable (stageMap : ∀ {j k : I} (a : j ⟶ k),
  stageSheaf k ⟶
    (pushforward (Type (max u v)) (F.map a)).obj (stageSheaf j))
variable (stageMap_id :
  ∀ i : I,
    stageMap (𝟙 i) =
      ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
        (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩)
variable (stageMap_comp :
  ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
    stageMap (b ≫ a) =
      ⟨(stageMap a ≫ (pushforward (Type (max u v)) (F.map a)).map (stageMap b)).1 ≫
        (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩)
variable [HasColimitsOfShape Iᵒᵖ (TopCat.Sheaf (Type (max u v)) (limit F))]

public noncomputable def setup : InverseLimitTypeSheafSystem F where
  stageSheaf := stageSheaf
  stageMap := stageMap
  stageMap_id := stageMap_id
  stageMap_comp := stageMap_comp

/-- The colimit `\mathop{\mathrm{colim}}_{a : j \to i} \mathcal{F}_j(f_a^{-1}(U_i))`. -/
noncomputable def projectionOpenSectionColimit (i : I) (Uᵢ : Opens (F.obj i)) :
    Type (max u v) :=
  (setup F stageSheaf stageMap stageMap_id stageMap_comp).projectionOpenSectionColimit i Uᵢ

/-- The colimit sheaf
`\mathcal{F} = \mathop{\mathrm{colim}}_i p_i^{-1}\mathcal{F}_i`
on the inverse-limit space. -/
noncomputable def colimitSheaf : TopCat.Sheaf (Type (max u v)) (limit F) :=
  (setup F stageSheaf stageMap stageMap_id stageMap_comp).colimitSheaf

/-- The canonical comparison map
`\mathop{\mathrm{colim}}_{a : j \to i} \mathcal{F}_j(f_a^{-1}(U_i)) \to
(\mathop{\mathrm{colim}}_j p_j^{-1}\mathcal{F}_j)(p_i^{-1}(U_i)) = \mathcal{F}(p_i^{-1}(U_i))`.
-/
noncomputable def projectionOpenSectionsComparison (i : I) (Uᵢ : Opens (F.obj i)) :
    projectionOpenSectionColimit F stageSheaf stageMap stageMap_id stageMap_comp i Uᵢ ⟶
      (colimitSheaf F stageSheaf stageMap stageMap_id stageMap_comp).presheaf.obj
        (op ((Opens.map (limit.π F i)).obj Uᵢ)) :=
  (setup F stageSheaf stageMap stageMap_id stageMap_comp).projectionOpenSectionsComparison i Uᵢ

/-- Helper for Lemma 6.29.4: the universe-small replacement of the index diagram used when
applying Lemma 6.29.3. -/
public noncomputable abbrev smallIndexDiagram :
    AsSmall.{max u v} I ⥤ TopCat.{max u v} :=
  AsSmall.down ⋙ F

/-- Helper for Lemma 6.29.4: Lemma 6.29.3 applies to the small replacement of the index
diagram at every stage. -/
public theorem smallIndex_limitPullbackSectionsColimitMap_isIso
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    (j : I) (𝒢 : (F.obj j).Sheaf (Type (max u v)))
    (U : Opens (F.obj j)) (hU : IsCompact (U : Set (F.obj j))) :
    IsIso (limitPullbackSectionsColimitMap
      (smallIndexDiagram (F := F)) (AsSmall.up.obj j) 𝒢 U) := by
  letI : ∀ x : AsSmall.{max u v} I,
      SpectralSpace ((smallIndexDiagram (F := F)).obj x) := by
    intro x
    change SpectralSpace (F.obj (AsSmall.down.obj x))
    infer_instance
  exact limitPullbackSectionsColimitMap_isIso (smallIndexDiagram (F := F))
    (by intro a b f; exact hF (AsSmall.down.map f))
    (AsSmall.up.obj j) 𝒢 U hU

/-- Helper for Lemma 6.29.4: the universe-small over-index diagram over a fixed stage.  Its
objects are arrows into `j`, and it is the diagram to which Lemma 6.29.3 is applied in the
formal/Fubini step. -/
public noncomputable abbrev overSmallIndexDiagram (j : I) :
    AsSmall.{max u v} (Over j) ⥤ TopCat.{max u v} :=
  AsSmall.down ⋙ Over.forget j ⋙ F

/-- Helper for Lemma 6.29.4: the small over-index functor is initial, combining the `AsSmall`
equivalence with the standard initiality of `Over.forget` over a cofiltered category. -/
public theorem overSmallIndexFunctor_initial (j : I) :
    (AsSmall.down ⋙ Over.forget j :
      AsSmall.{max u v} (Over j) ⥤ I).Initial := by
  -- First provide the non-inferable initiality instance for `AsSmall.down`; then compose it with
  -- the standard over-category initial functor.
  haveI : (AsSmall.down : AsSmall.{max u v} (Over j) ⥤ Over j).Initial := by
    change (AsSmall.equiv : Over j ≌ AsSmall.{max u v} (Over j)).inverse.Initial
    infer_instance
  exact CategoryTheory.Functor.initial_comp
    (AsSmall.down : AsSmall.{max u v} (Over j) ⥤ Over j) (Over.forget j)

/-- Helper for Lemma 6.29.4: the canonical limit isomorphism from the small over-index diagram
back to the ambient inverse limit. -/
public noncomputable def overSmallIndexLimitIso (j : I) :
    limit (overSmallIndexDiagram (F := F) j) ≅ limit F := by
  -- The preceding initiality result is the only non-inferable instance needed by
  -- `Functor.Initial.limitIso`.
  letI : (AsSmall.down ⋙ Over.forget j :
      AsSmall.{max u v} (Over j) ⥤ I).Initial :=
    overSmallIndexFunctor_initial (I := I) j
  exact Functor.Initial.limitIso
    (AsSmall.down ⋙ Over.forget j : AsSmall.{max u v} (Over j) ⥤ I) F

/-- Helper for Lemma 6.29.4: the over-index limit isomorphism has the expected projection
formula. This is the stable transport fact used to compare Lemma 6.29.3 with the ambient
projection maps. -/
public theorem overSmallIndexLimitIso_hom_π (j : I)
    (A : AsSmall.{max u v} (Over j)) :
    (overSmallIndexLimitIso (F := F) j).hom ≫
        limit.π F ((AsSmall.down ⋙ Over.forget j :
          AsSmall.{max u v} (Over j) ⥤ I).obj A) =
      limit.π (overSmallIndexDiagram (F := F) j) A := by
  -- Rewrite the ambient projection through `limit.pre`, then cancel the isomorphism with its
  -- inverse; this avoids unfolding the concrete limit object.
  have hpre :=
    limit.pre_π F
      (AsSmall.down ⋙ Over.forget j : AsSmall.{max u v} (Over j) ⥤ I) A
  rw [← hpre]
  change ((overSmallIndexLimitIso (F := F) j).hom ≫
      (overSmallIndexLimitIso (F := F) j).inv) ≫
        limit.π (overSmallIndexDiagram (F := F) j) A =
      limit.π (overSmallIndexDiagram (F := F) j) A
  rw [Iso.hom_inv_id, Category.id_comp]

/-- Helper for Lemma 6.29.4: the preceding projection formula at the identity object over the
chosen stage. This is the exact projection appearing in the target of Lemma 6.29.3. -/
public theorem overSmallIndexLimitIso_hom_base_π (j : I) :
    (overSmallIndexLimitIso (F := F) j).hom ≫ limit.π F j =
      limit.π (overSmallIndexDiagram (F := F) j)
        (AsSmall.up.obj (Over.mk (𝟙 j))) := by
  -- Specialize the general projection formula and simplify the small identity-over-stage object.
  simpa [overSmallIndexDiagram] using
    overSmallIndexLimitIso_hom_π (F := F) j (AsSmall.up.obj (Over.mk (𝟙 j)))

/-- Helper for Lemma 6.29.4: the inverse of the over-index limit isomorphism is `limit.pre`, so
its projections are the ambient projections. -/
public theorem overSmallIndexLimitIso_inv_π (j : I)
    (A : AsSmall.{max u v} (Over j)) :
    (overSmallIndexLimitIso (F := F) j).inv ≫
        limit.π (overSmallIndexDiagram (F := F) j) A =
      limit.π F ((AsSmall.down ⋙ Over.forget j :
        AsSmall.{max u v} (Over j) ⥤ I).obj A) := by
  -- Unfold only the canonical `limitIso` enough to expose `limit.pre_π`.
  simpa [overSmallIndexLimitIso] using
    limit.pre_π F
      (AsSmall.down ⋙ Over.forget j : AsSmall.{max u v} (Over j) ⥤ I) A

/-- Helper for Lemma 6.29.4: the inverse projection formula at the identity object over the
chosen stage. -/
public theorem overSmallIndexLimitIso_inv_base_π (j : I) :
    (overSmallIndexLimitIso (F := F) j).inv ≫
        limit.π (overSmallIndexDiagram (F := F) j)
          (AsSmall.up.obj (Over.mk (𝟙 j))) =
      limit.π F j := by
  -- Specialize the inverse projection computation at the identity-over-stage object.
  simpa [overSmallIndexDiagram] using
    overSmallIndexLimitIso_inv_π (F := F) j (AsSmall.up.obj (Over.mk (𝟙 j)))

/-- Helper for Lemma 6.29.4: Lemma 6.29.3 applied on the small over-index category above a
fixed stage. This is the local comparison in the source proof, before transporting its limit
object back to the ambient inverse limit. -/
public theorem overSmallIndex_limitPullbackSectionsColimitMap_isIso
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    (j : I) (𝒢 : (F.obj j).Sheaf (Type (max u v)))
    (U : Opens (F.obj j)) (hU : IsCompact (U : Set (F.obj j))) :
    IsIso (limitPullbackSectionsColimitMap
      (overSmallIndexDiagram (F := F) j) (AsSmall.up.obj (Over.mk (𝟙 j))) 𝒢 U) := by
  -- The over-index category is small after `AsSmall`; its objects still land in spectral stages,
  -- and the transition maps remain spectral by the original hypothesis.
  letI : IsCofiltered (AsSmall.{max u v} (Over j)) :=
    IsCofiltered.of_equivalence (AsSmall.equiv : Over j ≌ AsSmall.{max u v} (Over j))
  letI : ∀ x : AsSmall.{max u v} (Over j),
      SpectralSpace ((overSmallIndexDiagram (F := F) j).obj x) := by
    intro x
    change SpectralSpace (F.obj (AsSmall.down.obj x).left)
    infer_instance
  exact limitPullbackSectionsColimitMap_isIso (overSmallIndexDiagram (F := F) j)
    (by
      intro A B f
      change IsSpectralMap (F.map (AsSmall.down.map f).left)
      exact hF (AsSmall.down.map f).left)
    (AsSmall.up.obj (Over.mk (𝟙 j))) 𝒢 U hU

/-- Helper for Lemma 6.29.4: inverse images of the chosen quasi-compact open along stage maps
are quasi-compact. -/
public theorem projection_open_preimage_isCompact
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    {i : I} (Uᵢ : Opens (F.obj i)) (hUᵢ : IsCompact (Uᵢ : Set (F.obj i)))
    (A : (Over i)ᵒᵖ) :
    IsCompact ((F.map A.unop.hom) ⁻¹' (Uᵢ : Set (F.obj i))) := by
  exact (hF A.unop.hom).isCompact_preimage_of_isOpen Uᵢ.isOpen hUᵢ

/-- Helper for Lemma 6.29.4: the 6.29.3 comparison specialized to the stage and open attached
to an object `a : j ⟶ i` of the outer over-category. -/
public theorem overSmallIndex_projectionOpen_limitPullbackSectionsColimitMap_isIso
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    {i : I} (Uᵢ : Opens (F.obj i)) (hUᵢ : IsCompact (Uᵢ : Set (F.obj i)))
    (A : (Over i)ᵒᵖ) :
    IsIso (limitPullbackSectionsColimitMap
      (overSmallIndexDiagram (F := F) A.unop.left)
      (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
      (stageSheaf A.unop.left) ((Opens.map (F.map A.unop.hom)).obj Uᵢ)) := by
  -- The open `f_a^{-1}(U_i)` is compact because all transition maps are spectral.
  have hcompact_set : IsCompact ((F.map A.unop.hom) ⁻¹' (Uᵢ : Set (F.obj i))) := by
    exact projection_open_preimage_isCompact (F := F) hF Uᵢ hUᵢ A
  exact overSmallIndex_limitPullbackSectionsColimitMap_isIso
    (F := F) hF A.unop.left (stageSheaf A.unop.left)
    ((Opens.map (F.map A.unop.hom)).obj Uᵢ) (by simpa using hcompact_set)

/-- Helper for Lemma 6.29.4: an arrow `b : k ⟶ j`, viewed as an object in the over-category
which indexes Lemma 6.29.3 for the small over-index diagram above `j`. -/
public noncomputable def overSmallIndexOverObject {j : I} (B : Over j) :
    Over (AsSmall.up.obj (Over.mk (𝟙 j) : Over j)) :=
  Over.mk (AsSmall.up.map
    (Over.homMk B.hom (by simp) :
      B ⟶ (Over.mk (𝟙 j) : Over j)))

/-- Helper for Lemma 6.29.4: the identity object of the small over-index category above the
source of an outer over-object. -/
public noncomputable abbrev overSmallIndexIdentityBase {i : I} (A : (Over i)ᵒᵖ) :
    AsSmall.{max u v} (Over A.unop.left) :=
  (AsSmall.up : Over A.unop.left ⥤ AsSmall.{max u v} (Over A.unop.left)).obj
    (Over.mk (𝟙 A.unop.left))

/-- Helper for Lemma 6.29.4: the identity object in the over-category of the small over-index
base. -/
public noncomputable abbrev overSmallIndexIdentityObject {i : I} (A : (Over i)ᵒᵖ) :
    (Over (overSmallIndexIdentityBase A))ᵒᵖ :=
  op (Over.mk (𝟙 (overSmallIndexIdentityBase A)))

/-- Helper for Lemma 6.29.4: the outer over-category object obtained by composing
`a : j ⟶ i` with an inner small-over refinement of `j`. -/
public noncomputable def overSmallIndexOuterObject
    {i : I} (A : (Over i)ᵒᵖ)
    (C : (Over (AsSmall.up.obj (Over.mk (𝟙 A.unop.left) :
      Over A.unop.left)))ᵒᵖ) : (Over i)ᵒᵖ :=
  op (Over.mk ((AsSmall.down.map C.unop.hom).left ≫ A.unop.hom) : Over i)

/-- Helper for Lemma 6.29.4: the outer over-category morphism from `a : j ⟶ i` to the
composite object attached to an inner refinement. -/
public noncomputable def overSmallIndexOuterHom
    {i : I} (A : (Over i)ᵒᵖ)
    (C : (Over (AsSmall.up.obj (Over.mk (𝟙 A.unop.left) :
      Over A.unop.left)))ᵒᵖ) :
    A ⟶ overSmallIndexOuterObject A C :=
  op (Over.homMk (AsSmall.down.map C.unop.hom).left (by
    rfl) :
      (overSmallIndexOuterObject A C).unop ⟶ A.unop)

/-- Helper for Lemma 6.29.4: an inner small-over source representative is sent by the transition
map `stagePullbackMap` to the source section at the corresponding outer composite object. -/
public noncomputable def overSmallIndexSourceToOuter
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ)
    (C : (Over (AsSmall.up.obj (Over.mk (𝟙 A.unop.left) :
      Over A.unop.left)))ᵒᵖ) :
    (limitPullbackSectionsDiagram
        (overSmallIndexDiagram (F := F) A.unop.left)
        (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
        (stageSheaf A.unop.left)
        ((Opens.map (F.map A.unop.hom)).obj Uᵢ)).obj C ⟶
      ((setup F stageSheaf stageMap stageMap_id stageMap_comp).projectionOpenSectionDiagram
        i Uᵢ).obj (overSmallIndexOuterObject A C) := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  let b := (AsSmall.down.map C.unop.hom).left
  refine fun s ↦ cast ?_ ((σ.stagePullbackMap b).1.app
    (op ((Opens.map (F.map b)).obj ((Opens.map (F.map A.unop.hom)).obj Uᵢ))) s)
  dsimp [σ, overSmallIndexOuterObject,
    InverseLimitTypeSheafSystem.projectionOpenSectionDiagram,
    InverseLimitTypeSheafSystem.projectionOpenSectionValue,
    InverseLimitTypeSheafSystem.stageSectionFunctor,
    InverseLimitTypeSheafSystem.projectionPushforwardDiagram,
    overSmallIndexDiagram]
  simp [b, Functor.map_comp]
  rfl

/-- Helper for Lemma 6.29.4: the outer colimit-refinement square, specialized to the composite
object and morphism coming from an inner small-over refinement. -/
public theorem overSmallIndex_projectionOpen_colimit_refinement_apply
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ)
    (C : (Over (AsSmall.up.obj (Over.mk (𝟙 A.unop.left) :
      Over A.unop.left)))ᵒᵖ)
    (s : (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).obj A) :
    colimit.ι
        (InverseLimitTypeSheafSystem.projectionPulledBackSectionDiagram
          (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ)
        (overSmallIndexOuterObject A C)
        (InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap
          (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ
            (overSmallIndexOuterObject A C)
          ((InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
            (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).map
              (overSmallIndexOuterHom A C) s)) =
      colimit.ι
        (InverseLimitTypeSheafSystem.projectionPulledBackSectionDiagram
          (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ)
        A
        (InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap
          (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ A s) := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  let b := (AsSmall.down.map C.unop.hom).left
  have h :=
    InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap_colimit_refinement_apply
      (setup := σ) A.unop.hom b Uᵢ (s := s)
  simpa [σ, b, overSmallIndexOuterObject, overSmallIndexOuterHom] using h

/-- Helper for Lemma 6.29.4: the pointwise naturality square for the outer composite object
attached to an inner small-over refinement.  This is the non-colimit form of
`overSmallIndex_projectionOpen_colimit_refinement_apply`. -/
public theorem overSmallIndex_projectionOpen_refinement_naturality
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ)
    (C : (Over (AsSmall.up.obj (Over.mk (𝟙 A.unop.left) :
      Over A.unop.left)))ᵒᵖ) :
    (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
        (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).map
        (overSmallIndexOuterHom A C) ≫
      InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap
        (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ
          (overSmallIndexOuterObject A C) =
    InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap
        (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ A ≫
      (((InverseLimitTypeSheafSystem.pulledBackDiagram
        (setup F stageSheaf stageMap stageMap_id stageMap_comp)).map
          ((overSmallIndexOuterHom A C).unop.left.op)).1.app
            (op ((Opens.map (limit.π F i)).obj Uᵢ))) := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  simpa [σ, overSmallIndexOuterObject, overSmallIndexOuterHom] using
    InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap_naturality
      (setup := σ) Uᵢ (overSmallIndexOuterHom A C)

/-- Helper for Lemma 6.29.4: pointwise form of the specialized outer composite naturality
square. -/
public theorem overSmallIndex_projectionOpen_refinement_apply
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ)
    (C : (Over (AsSmall.up.obj (Over.mk (𝟙 A.unop.left) :
      Over A.unop.left)))ᵒᵖ)
    (s : (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).obj A) :
    InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap
        (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ
          (overSmallIndexOuterObject A C)
        ((InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
          (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).map
            (overSmallIndexOuterHom A C) s) =
      (InverseLimitTypeSheafSystem.projectionPulledBackSectionDiagram
        (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).map
        (overSmallIndexOuterHom A C)
        (InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap
          (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ A s) := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  have h :=
    overSmallIndex_projectionOpen_refinement_naturality
      (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
      (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C
  simpa [σ, InverseLimitTypeSheafSystem.projectionPulledBackSectionDiagram,
    InverseLimitTypeSheafSystem.limitProjectionSectionFunctor] using congrFun h s

/-- Helper for Lemma 6.29.4: the target open in the small over-index comparison is the pullback,
along the canonical over-index limit isomorphism, of the ambient open `p_i^{-1}(U_i)`. -/
public theorem overSmallIndex_projectionOpen_target_open_eq
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ) :
    (Opens.map
        (limit.π (overSmallIndexDiagram (F := F) A.unop.left)
          (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))))).obj
        ((Opens.map (F.map A.unop.hom)).obj Uᵢ) =
      (Opens.map (overSmallIndexLimitIso (F := F) A.unop.left).hom).obj
        ((Opens.map (limit.π F i)).obj Uᵢ) := by
  ext x
  constructor
  · intro hx
    have hbase :
        ((overSmallIndexLimitIso (F := F) A.unop.left).hom ≫
            limit.π F A.unop.left) x =
          limit.π (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))) x := by
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom
          (overSmallIndexLimitIso_hom_base_π (F := F) A.unop.left)) x
    have hπ :
        F.map A.unop.hom
            (limit.π F A.unop.left
              ((overSmallIndexLimitIso (F := F) A.unop.left).hom x)) =
          limit.π F i ((overSmallIndexLimitIso (F := F) A.unop.left).hom x) := by
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom (limit.w F A.unop.hom))
        ((overSmallIndexLimitIso (F := F) A.unop.left).hom x)
    change F.map A.unop.hom
        (limit.π (overSmallIndexDiagram (F := F) A.unop.left)
          (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))) x) ∈ Uᵢ at hx
    change limit.π F i ((overSmallIndexLimitIso (F := F) A.unop.left).hom x) ∈ Uᵢ
    exact hπ ▸ (hbase.symm ▸ hx)
  · intro hx
    have hbase :
        ((overSmallIndexLimitIso (F := F) A.unop.left).hom ≫
            limit.π F A.unop.left) x =
          limit.π (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))) x := by
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom
          (overSmallIndexLimitIso_hom_base_π (F := F) A.unop.left)) x
    have hπ :
        F.map A.unop.hom
            (limit.π F A.unop.left
              ((overSmallIndexLimitIso (F := F) A.unop.left).hom x)) =
          limit.π F i ((overSmallIndexLimitIso (F := F) A.unop.left).hom x) := by
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom (limit.w F A.unop.hom))
        ((overSmallIndexLimitIso (F := F) A.unop.left).hom x)
    change limit.π F i ((overSmallIndexLimitIso (F := F) A.unop.left).hom x) ∈ Uᵢ at hx
    change F.map A.unop.hom
        (limit.π (overSmallIndexDiagram (F := F) A.unop.left)
          (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))) x) ∈ Uᵢ
    exact hbase ▸ (hπ.symm ▸ hx)

/-- Helper for Lemma 6.29.4: the target open for a refined small-over object agrees with the
ambient outer open pulled back along the canonical over-index limit isomorphism. -/
public theorem overSmallIndex_projectionOpen_outer_target_open_eq
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ)
    (C : (Over (AsSmall.up.obj (Over.mk (𝟙 A.unop.left) :
      Over A.unop.left)))ᵒᵖ) :
    (Opens.map
        (limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left)).obj
        ((Opens.map (F.map (AsSmall.down.map C.unop.hom).left)).obj
          ((Opens.map (F.map A.unop.hom)).obj Uᵢ)) =
      (Opens.map (overSmallIndexLimitIso (F := F) A.unop.left).hom).obj
        ((Opens.map (limit.π F i)).obj Uᵢ) := by
  let H := overSmallIndexLimitIso (F := F) A.unop.left
  let b := (AsSmall.down.map C.unop.hom).left
  ext x
  constructor
  · intro hx
    have hsmall :
        F.map b
            (limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left x) =
          limit.π (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))) x := by
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom
          (limit.w (overSmallIndexDiagram (F := F) A.unop.left) C.unop.hom)) x
    have hbase :
        (H.hom ≫ limit.π F A.unop.left) x =
          limit.π (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))) x := by
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom
          (overSmallIndexLimitIso_hom_base_π (F := F) A.unop.left)) x
    have hπ :
        F.map A.unop.hom (limit.π F A.unop.left (H.hom x)) =
          limit.π F i (H.hom x) := by
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom (limit.w F A.unop.hom)) (H.hom x)
    change F.map A.unop.hom
        (F.map b
          (limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left x)) ∈ Uᵢ at hx
    change limit.π F i (H.hom x) ∈ Uᵢ
    rw [hsmall] at hx
    exact hπ ▸ (hbase.symm ▸ hx)
  · intro hx
    have hsmall :
        F.map b
            (limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left x) =
          limit.π (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))) x := by
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom
          (limit.w (overSmallIndexDiagram (F := F) A.unop.left) C.unop.hom)) x
    have hbase :
        (H.hom ≫ limit.π F A.unop.left) x =
          limit.π (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))) x := by
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom
          (overSmallIndexLimitIso_hom_base_π (F := F) A.unop.left)) x
    have hπ :
        F.map A.unop.hom (limit.π F A.unop.left (H.hom x)) =
          limit.π F i (H.hom x) := by
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom (limit.w F A.unop.hom)) (H.hom x)
    change limit.π F i (H.hom x) ∈ Uᵢ at hx
    change F.map A.unop.hom
        (F.map b
          (limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left x)) ∈ Uᵢ
    rw [hsmall]
    exact hbase ▸ (hπ.symm ▸ hx)

/-- Helper for Lemma 6.29.4: the sheaf-level target transport induced by the canonical
isomorphism between the small over-index limit and the ambient inverse limit. -/
public noncomputable def overSmallIndexProjectionTargetSheafIso
    (A : (Over i)ᵒᵖ) :
    ((pullback (Type (max u v))
        (limit.π (overSmallIndexDiagram (F := F) A.unop.left)
          (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))))).obj
        (stageSheaf A.unop.left)) ≅
      ((pullback (Type (max u v))
        (overSmallIndexLimitIso (F := F) A.unop.left).hom).obj
        ((pullback (Type (max u v)) (limit.π F A.unop.left)).obj
          (stageSheaf A.unop.left))) := by
  let H := overSmallIndexLimitIso (F := F) A.unop.left
  let psmall :=
    limit.π (overSmallIndexDiagram (F := F) A.unop.left)
      (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
  let pambient := limit.π F A.unop.left
  have hbase : H.hom ≫ pambient = psmall :=
    overSmallIndexLimitIso_hom_base_π (F := F) A.unop.left
  exact
    ((eqToIso (congrArg (pullback (Type (max u v))) hbase)).symm.app
        (stageSheaf A.unop.left)) ≪≫
      ((pullbackComp H.hom pambient).symm.app (stageSheaf A.unop.left))

/-- Helper for Lemma 6.29.4: the sheaf-level target transport for a refined small-over object,
induced by the canonical over-index limit isomorphism. -/
public noncomputable def overSmallIndexProjectionOuterSheafIso
    {i : I} (A : (Over i)ᵒᵖ)
    (C : (Over (AsSmall.up.obj (Over.mk (𝟙 A.unop.left) :
      Over A.unop.left)))ᵒᵖ) :
    ((pullback (Type (max u v))
        (limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left)).obj
        (stageSheaf (AsSmall.down.obj C.unop.left).left)) ≅
      ((pullback (Type (max u v))
        (overSmallIndexLimitIso (F := F) A.unop.left).hom).obj
        ((pullback (Type (max u v))
          (limit.π F (AsSmall.down.obj C.unop.left).left)).obj
          (stageSheaf (AsSmall.down.obj C.unop.left).left))) := by
  let H := overSmallIndexLimitIso (F := F) A.unop.left
  let qsmall :=
    limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left
  let k := (AsSmall.down.obj C.unop.left).left
  let qambient := limit.π F k
  have hq : H.hom ≫ qambient = qsmall :=
    overSmallIndexLimitIso_hom_π (F := F) A.unop.left C.unop.left
  exact
    ((eqToIso (congrArg (pullback (Type (max u v))) hq)).symm.app
        (stageSheaf k)) ≪≫
      ((pullbackComp H.hom qambient).symm.app (stageSheaf k))

/-- Helper for Lemma 6.29.4: an ambient pulled-back target section at an outer object `a : j ⟶ i`
as a target section for the small over-index comparison over `j`. -/
public noncomputable def overSmallIndexProjectionTargetMap
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ) :
    (InverseLimitTypeSheafSystem.projectionPulledBackSectionDiagram
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).obj A ⟶
      (limitPullbackSectionsCocone
        (overSmallIndexDiagram (F := F) A.unop.left)
        (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
        (stageSheaf A.unop.left)
        ((Opens.map (F.map A.unop.hom)).obj Uᵢ)).pt := by
  let H := overSmallIndexLimitIso (F := F) A.unop.left
  let W := (Opens.map (limit.π F i)).obj Uᵢ
  let ℋ :=
    (pullback (Type (max u v)) (limit.π F A.unop.left)).obj
      (stageSheaf A.unop.left)
  refine fun y ↦ cast ?_
    (((overSmallIndexProjectionTargetSheafIso
        (F := F) (stageSheaf := stageSheaf) A).inv).1.app
      (op ((Opens.map H.hom).obj W))
      (((pullbackPushforwardAdjunction (Type (max u v)) H.hom).unit.app ℋ).1.app
        (op W) y))
  -- The small target open is the pullback of the ambient open through the over-index limit iso.
  have hopen := overSmallIndex_projectionOpen_target_open_eq (F := F) Uᵢ A
  simpa [limitPullbackSectionsCocone, H, W] using
    congrArg
      (fun V ↦
        (((pullback (Type (max u v))
          (limit.π (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left))))).obj
        (stageSheaf A.unop.left)).presheaf).obj (op V))
      hopen.symm

set_option maxHeartbeats 1200000 in
/-- Helper for Lemma 6.29.4: a small-over representative whose limit image is the transported
ambient target section gives the required outer refined source representative. -/
theorem overSmallIndex_projectionOpen_source_to_outer_refinement_apply
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ)
    (C : (Over (AsSmall.up.obj (Over.mk (𝟙 A.unop.left) :
      Over A.unop.left)))ᵒᵖ)
    (s :
      (limitPullbackSectionsDiagram
        (overSmallIndexDiagram (F := F) A.unop.left)
        (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
        (stageSheaf A.unop.left)
        ((Opens.map (F.map A.unop.hom)).obj Uᵢ)).obj C)
    (y : (InverseLimitTypeSheafSystem.projectionPulledBackSectionDiagram
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).obj A)
    (hy :
      limitPullbackSectionsColimitMap
        (overSmallIndexDiagram (F := F) A.unop.left)
        (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
        (stageSheaf A.unop.left)
        ((Opens.map (F.map A.unop.hom)).obj Uᵢ)
        (colimit.ι
          (limitPullbackSectionsDiagram
            (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
            (stageSheaf A.unop.left)
            ((Opens.map (F.map A.unop.hom)).obj Uᵢ)) C s) =
        overSmallIndexProjectionTargetMap
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A y) :
    (InverseLimitTypeSheafSystem.projectionOpenToPulledBackSectionsNatTrans
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).app
        (overSmallIndexOuterObject A C)
        (overSmallIndexSourceToOuter
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C s) =
      (InverseLimitTypeSheafSystem.projectionPulledBackSectionDiagram
        (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).map
        (overSmallIndexOuterHom A C) y := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  have hy' :
      pullbackSectionsToLimitMap
        (F := overSmallIndexDiagram (F := F) A.unop.left)
        (i := overSmallIndexIdentityBase A)
        (stageSheaf A.unop.left)
        ((Opens.map (F.map A.unop.hom)).obj Uᵢ)
        C.unop s =
      overSmallIndexProjectionTargetMap
        (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
        (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A y := by
    simpa [limitPullbackSectionsColimitMap, limitPullbackSectionsCocone] using hy
  change
    (σ.projectionStageToLimitSheafMap (overSmallIndexOuterObject A C)).1.app (op Uᵢ)
      (overSmallIndexSourceToOuter
        (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
        (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C s) =
    (σ.pulledBackDiagram.map ((overSmallIndexOuterHom A C).unop.left.op)).1.app
      (op ((Opens.map (limit.π F i)).obj Uᵢ)) y
  -- The remaining step is the source-to-outer composite naturality square: apply the
  -- pullback of `stagePullbackMap` to `hy'`, then transport across the over-index limit iso.
  let H := overSmallIndexLimitIso (F := F) A.unop.left
  let k := (AsSmall.down.obj C.unop.left).left
  let W := (Opens.map (limit.π F i)).obj Uᵢ
  let P := (pullback (Type (max u v)) (limit.π F k)).obj (stageSheaf k)
  have hunit_eq :
      ∀ {x y : P.1.obj (op W)},
        (((pullbackPushforwardAdjunction (Type (max u v)) H.hom).unit.app P).1.app
          (op W)) x =
        (((pullbackPushforwardAdjunction (Type (max u v)) H.hom).unit.app P).1.app
          (op W)) y →
        x = y := by
    intro x y hxy
    let PH := (pullback (Type (max u v)) H.hom).obj P
    have hxy2 := congrArg
      (fun z ↦
        (((pullbackComp H.inv H.hom).hom.app P).1.app
          (op ((Opens.map H.inv).obj ((Opens.map H.hom).obj W)))
          (((pullbackPushforwardAdjunction (Type (max u v)) H.inv).unit.app PH).1.app
            (op ((Opens.map H.hom).obj W)) z))) hxy
    have hxcomp :=
      @InverseLimitTypeSheafSystem.pullback_unit_comp_section_eq.{u, v}
        (X := limit F) (Y := limit (overSmallIndexDiagram (F := F) A.unop.left))
        (Z := limit F) H.inv H.hom P W x
    have hycomp :=
      @InverseLimitTypeSheafSystem.pullback_unit_comp_section_eq.{u, v}
        (X := limit F) (Y := limit (overSmallIndexDiagram (F := F) A.unop.left))
        (Z := limit F) H.inv H.hom P W y
    have hcompxy := hxcomp.symm.trans (hxy2.trans hycomp)
    have hxid :=
      @InverseLimitTypeSheafSystem.pullback_unit_app_heq_of_eq.{u, v}
        (h := H.inv_hom_id) (𝒢 := P) (U := W) (s := x)
    have hyid :=
      @InverseLimitTypeSheafSystem.pullback_unit_app_heq_of_eq.{u, v}
        (h := H.inv_hom_id) (𝒢 := P) (U := W) (s := y)
    exact
      @InverseLimitTypeSheafSystem.pullback_unit_id_app_eq.{u, v}
        (Y := limit F) (𝒢 := P) (U := W)
        (hst := eq_of_heq (hxid.symm.trans ((heq_of_eq hcompxy).trans hyid)))
  apply hunit_eq
  let e := overSmallIndexProjectionOuterSheafIso
    (F := F) (stageSheaf := stageSheaf) A C
  have he_inj :
      ∀ {x y : ((pullback (Type (max u v)) H.hom).obj P).1.obj
          (op ((Opens.map H.hom).obj W))},
        e.inv.1.app (op ((Opens.map H.hom).obj W)) x =
          e.inv.1.app (op ((Opens.map H.hom).obj W)) y →
        x = y := by
    intro x y hxy
    have hxy2 := congrArg (e.hom.1.app (op ((Opens.map H.hom).obj W))) hxy
    have hxid := congrFun
      (congrArg (fun f ↦ f.1.app (op ((Opens.map H.hom).obj W))) e.inv_hom_id) x
    have hyid := congrFun
      (congrArg (fun f ↦ f.1.app (op ((Opens.map H.hom).obj W))) e.inv_hom_id) y
    simpa [ConcreteCategory.comp_apply] using hxid.symm.trans (hxy2.trans hyid)
  apply he_inj
  let b := (AsSmall.down.map C.unop.hom).left
  let tRaw := (σ.stagePullbackMap b).1.app
    (op ((Opens.map (F.map b)).obj ((Opens.map (F.map A.unop.hom)).obj Uᵢ))) s
  let t : (stageSheaf k).1.obj (op ((Opens.map (F.map (b ≫ A.unop.hom))).obj Uᵢ)) :=
    cast (by
      dsimp [σ, setup, k, b]
      simp [Functor.map_comp]
      rfl) tRaw
  have hq :
      H.hom ≫ limit.π F k =
        limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left := by
    simpa [H, k, b, overSmallIndexDiagram] using
      overSmallIndexLimitIso_hom_π (F := F) A.unop.left C.unop.left
  have hleftRaw :=
    @InverseLimitTypeSheafSystem.pullback_unit_comp_pushforward_unit_pushforwardEq_eqToHom_heq.{u, v}
      (limit (overSmallIndexDiagram (F := F) A.unop.left)) (limit F)
      (F.obj k) (F.obj i)
      H.hom (limit.π F k) (F.map (b ≫ A.unop.hom))
      (limit.π F i) (limit.w F (b ≫ A.unop.hom)).symm
      (limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left)
      hq
      (stageSheaf k) Uᵢ t
  have hsource :
      (σ.projectionStageToLimitSheafMap (overSmallIndexOuterObject A C)).1.app (op Uᵢ)
        (overSmallIndexSourceToOuter
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C s) =
      (TopCat.Presheaf.pushforwardEq (limit.w F (b ≫ A.unop.hom)).symm P.presheaf).inv.app
        (op Uᵢ)
        (((pullbackPushforwardAdjunction (Type (max u v)) (limit.π F k)).unit.app
            (stageSheaf k)).1.app
          (op ((Opens.map (F.map (b ≫ A.unop.hom))).obj Uᵢ)) t) := by
    have h :=
      InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap_eq_unit_pushforwardEq
        (setup := σ) Uᵢ (overSmallIndexOuterObject A C)
        (overSmallIndexSourceToOuter
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C s)
    simpa [σ, setup, P, t, tRaw, k, b, overSmallIndexOuterObject,
      overSmallIndexSourceToOuter] using h
  have hleft :
      e.inv.1.app (op ((Opens.map H.hom).obj W))
        (((pullbackPushforwardAdjunction (Type (max u v)) H.hom).unit.app P).1.app
          (op W)
          ((σ.projectionStageToLimitSheafMap (overSmallIndexOuterObject A C)).1.app (op Uᵢ)
            (overSmallIndexSourceToOuter
              (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
              (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C s))) ≍
        (((pullbackPushforwardAdjunction (Type (max u v))
              (limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left)).unit.app
            (stageSheaf k)).1.app
          (op ((Opens.map (F.map (b ≫ A.unop.hom))).obj Uᵢ)) t) := by
    rw [hsource]
    simpa [e, H, P, W, t, tRaw, σ, setup, overSmallIndexSourceToOuter,
      overSmallIndexOuterObject, InverseLimitTypeSheafSystem.projectionStageToLimitSheafMap,
      InverseLimitTypeSheafSystem.projectionPushforwardDiagram,
      projectionPushforwardMap, overSmallIndexProjectionOuterSheafIso,
      TopCat.Sheaf.pushforward_map, TopCat.Presheaf.pushforwardEq, Category.assoc,
      eqToHom_map] using hleftRaw
  have hright :
      e.inv.1.app (op ((Opens.map H.hom).obj W))
        (((pullbackPushforwardAdjunction (Type (max u v)) H.hom).unit.app P).1.app
          (op W)
          ((σ.pulledBackDiagram.map ((overSmallIndexOuterHom A C).unop.left.op)).1.app
            (op ((Opens.map (limit.π F i)).obj Uᵢ)) y)) ≍
        (((pullbackPushforwardAdjunction (Type (max u v))
              (limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left)).unit.app
            (stageSheaf k)).1.app
          (op ((Opens.map (F.map (b ≫ A.unop.hom))).obj Uᵢ)) t) := by
    let Uⱼ := (Opens.map (F.map A.unop.hom)).obj Uᵢ
    let qbase :=
      limit.π (overSmallIndexDiagram (F := F) A.unop.left) (overSmallIndexIdentityBase A)
    let qC := limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left
    have hsmallw : qC ≫ F.map b = qbase := by
      simpa [qC, qbase, b, overSmallIndexDiagram, overSmallIndexIdentityBase] using
        limit.w (overSmallIndexDiagram (F := F) A.unop.left) C.unop.hom
    let smallRefinementMap :
        ((pullback (Type (max u v)) qbase).obj (stageSheaf A.unop.left)) ⟶
          ((pullback (Type (max u v)) qC).obj (stageSheaf k)) :=
      ((eqToIso (congrArg (pullback (Type (max u v))) hsmallw)).inv.app
          (stageSheaf A.unop.left)) ≫
        ((pullbackComp qC (F.map b)).inv.app (stageSheaf A.unop.left)) ≫
          (pullback (Type (max u v)) qC).map (σ.stagePullbackMap b)
    let smallRefinementAtBase :=
      smallRefinementMap.1.app (op ((Opens.map qbase).obj Uⱼ))
    have htarget :
        e.inv.1.app (op ((Opens.map H.hom).obj W))
          (((pullbackPushforwardAdjunction (Type (max u v)) H.hom).unit.app P).1.app
            (op W)
            ((σ.pulledBackDiagram.map ((overSmallIndexOuterHom A C).unop.left.op)).1.app
              (op ((Opens.map (limit.π F i)).obj Uᵢ)) y)) ≍
          smallRefinementAtBase
            (overSmallIndexProjectionTargetMap
              (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
              (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A y) := by
      let eA := overSmallIndexProjectionTargetSheafIso
        (F := F) (stageSheaf := stageSheaf) A
      have hp :
          limit.π F k ≫ F.map b = limit.π F A.unop.left := by
        simpa [k, b] using (limit.w F b)
      have hbaseAmbient : H.hom ≫ limit.π F A.unop.left = qbase := by
        simpa [H, qbase, overSmallIndexIdentityBase] using
          overSmallIndexLimitIso_hom_base_π (F := F) A.unop.left
      have hsheaf :
          (pullback (Type (max u v)) H.hom).map
              (InverseLimitTypeSheafSystem.pulledBackDiagramMap (setup := σ) b) ≫ e.inv =
            eA.inv ≫ smallRefinementMap := by
        have hsheaf0 :=
          @InverseLimitTypeSheafSystem.pullback_refinement_iso_coherence.{u, v}
            (W := limit (overSmallIndexDiagram (F := F) A.unop.left))
            (X := limit F) (Y := F.obj k) (Z := F.obj A.unop.left)
            H.hom (limit.π F k) (F.map b)
            (p' := limit.π F A.unop.left) hp
            (q := qC) hq (q' := qbase) hbaseAmbient hsmallw
            (stageSheaf A.unop.left) (stageSheaf k)
            (InverseLimitTypeSheafSystem.stagePullbackMap (setup := σ) b)
        dsimp [smallRefinementMap, e, eA, overSmallIndexProjectionTargetSheafIso,
          overSmallIndexProjectionOuterSheafIso,
          InverseLimitTypeSheafSystem.pulledBackDiagramMap]
        exact hsheaf0
      have hnatUnit :=
        congrFun
          (congrArg (fun f ↦ f.1.app (op W))
            ((pullbackPushforwardAdjunction (Type (max u v)) H.hom).unit.naturality
              (InverseLimitTypeSheafSystem.pulledBackDiagramMap (setup := σ) b)))
          y
      have hnat :=
        let evalE := e.inv.1.app (op ((Opens.map H.hom).obj W))
        congrArg evalE hnatUnit
      have hsheaf_app :=
        congrFun
          (congrArg (fun f ↦ f.1.app (op ((Opens.map H.hom).obj W))) hsheaf)
          (((pullbackPushforwardAdjunction (Type (max u v)) H.hom).unit.app
            ((pullback (Type (max u v)) (limit.π F A.unop.left)).obj
              (stageSheaf A.unop.left))).1.app (op W) y)
      let z :=
        eA.inv.1.app (op ((Opens.map H.hom).obj W))
          (((pullbackPushforwardAdjunction (Type (max u v)) H.hom).unit.app
            ((pullback (Type (max u v)) (limit.π F A.unop.left)).obj
              (stageSheaf A.unop.left))).1.app (op W) y)
      have hmid :
          e.inv.1.app (op ((Opens.map H.hom).obj W))
            (((pullbackPushforwardAdjunction (Type (max u v)) H.hom).unit.app P).1.app
              (op W)
              ((σ.pulledBackDiagram.map ((overSmallIndexOuterHom A C).unop.left.op)).1.app
                (op ((Opens.map (limit.π F i)).obj Uᵢ)) y)) =
            smallRefinementMap.1.app (op ((Opens.map H.hom).obj W)) z := by
        exact hnat.trans (by
          simpa [z, ConcreteCategory.comp_apply, Category.assoc] using hsheaf_app)
      have hopenBase :
          (Opens.map H.hom).obj W = (Opens.map qbase).obj Uⱼ := by
        simpa [H, W, Uⱼ, qbase, overSmallIndexIdentityBase] using
          (overSmallIndex_projectionOpen_target_open_eq (F := F) Uᵢ A).symm
      have htarget_rhs :
          smallRefinementAtBase
            (overSmallIndexProjectionTargetMap
              (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
              (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A y) ≍
            smallRefinementMap.1.app (op ((Opens.map H.hom).obj W)) z := by
        simpa [z, eA, H, W, Uⱼ, qbase, overSmallIndexProjectionTargetMap,
          overSmallIndexProjectionTargetSheafIso, limitPullbackSectionsCocone] using
          @InverseLimitTypeSheafSystem.sheaf_hom_app_cast_heq.{u, v}
            (X := limit (overSmallIndexDiagram (F := F) A.unop.left))
            (𝓕 := (pullback (Type (max u v)) qbase).obj (stageSheaf A.unop.left))
            (𝓖 := (pullback (Type (max u v)) qC).obj (stageSheaf k))
            (α := smallRefinementMap) (h := hopenBase)
            (s := z)
      exact (heq_of_eq hmid).trans htarget_rhs.symm
    have hsmall :
        smallRefinementAtBase
          (pullbackSectionsToLimitMap
            (F := overSmallIndexDiagram (F := F) A.unop.left)
            (i := overSmallIndexIdentityBase A)
            (stageSheaf A.unop.left) Uⱼ C.unop s) ≍
        (((pullbackPushforwardAdjunction (Type (max u v))
              (limit.π (overSmallIndexDiagram (F := F) A.unop.left) C.unop.left)).unit.app
            (stageSheaf k)).1.app
          (op ((Opens.map (F.map (b ≫ A.unop.hom))).obj Uᵢ)) t) := by
      have hsmall0 :=
        @InverseLimitTypeSheafSystem.pullback_refinement_iterated_map_heq.{u, v}
          (X := limit (overSmallIndexDiagram (F := F) A.unop.left))
          (Y := F.obj k) (Z := F.obj A.unop.left)
          qC (F.map b) (p' := qbase) hsmallw
          (stageSheaf A.unop.left) (stageSheaf k)
          (InverseLimitTypeSheafSystem.stagePullbackMap (setup := σ) b)
          Uⱼ s
      change
        (((((eqToIso (congrArg (pullback (Type (max u v))) hsmallw)).inv.app
                (stageSheaf A.unop.left) ≫
              ((pullbackComp qC (F.map b)).inv.app (stageSheaf A.unop.left)) ≫
                (pullback (Type (max u v)) qC).map
                  (InverseLimitTypeSheafSystem.stagePullbackMap (setup := σ) b)).1.app
            (op ((Opens.map qbase).obj Uⱼ))
            (cast
              (congrArg
                (fun r : limit (overSmallIndexDiagram (F := F) A.unop.left) ⟶
                    F.obj A.unop.left ↦
                  (((TopCat.Sheaf.pullback (Type (max u v)) r).obj
                    (stageSheaf A.unop.left)).presheaf).obj
                      (op ((Opens.map r).obj Uⱼ)))
                hsmallw)
              (_root_.iteratedPullbackSectionsMap qC (F.map b)
                (stageSheaf A.unop.left) Uⱼ s))) ≍
          (((pullbackPushforwardAdjunction (Type (max u v)) qC).unit.app
              (stageSheaf k)).1.app
            (op ((Opens.map (F.map (b ≫ A.unop.hom))).obj Uᵢ)) t)))
      refine hsmall0.trans ?_
      have hopenStage :
          (Opens.map (F.map b)).obj Uⱼ =
            (Opens.map (F.map (b ≫ A.unop.hom))).obj Uᵢ := by
        simpa only [Uⱼ, Functor.map_comp] using
          (Opens.map_comp_obj (F.map b) (F.map A.unop.hom) Uᵢ).symm
      have hcast :=
        @InverseLimitTypeSheafSystem.sheaf_hom_app_cast_heq.{u, v}
          (X := F.obj k)
          (𝓕 := stageSheaf k)
          (𝓖 :=
            (pushforward (Type (max u v)) qC).obj
              ((pullback (Type (max u v)) qC).obj (stageSheaf k)))
          (α := (pullbackPushforwardAdjunction (Type (max u v)) qC).unit.app
            (stageSheaf k))
          (h := hopenStage)
          (s := (InverseLimitTypeSheafSystem.stagePullbackMap (setup := σ) b).1.app
            (op ((Opens.map (F.map b)).obj Uⱼ)) s)
      simpa only [Uⱼ, t, tRaw, Functor.map_comp] using hcast.symm
    exact InverseLimitTypeSheafSystem.heq_trans_fun_arg_of_eq
        (f := smallRefinementAtBase)
        (x :=
          pullbackSectionsToLimitMap
            (F := overSmallIndexDiagram (F := F) A.unop.left)
            (i := overSmallIndexIdentityBase A)
            (stageSheaf A.unop.left) Uⱼ C.unop s)
        (y :=
          overSmallIndexProjectionTargetMap
            (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
            (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A y)
        hy' htarget hsmall
  exact eq_of_heq (hleft.trans hright.symm)

/-- Helper for Lemma 6.29.4: view an outer stage section at `a : j ⟶ i` as the identity
small-over source representative over `j`. -/
public noncomputable def overSmallIndexIdentitySource
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ) :
    (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).obj A ⟶
    (limitPullbackSectionsDiagram
        (overSmallIndexDiagram (F := F) A.unop.left)
        (overSmallIndexIdentityBase A)
        (stageSheaf A.unop.left)
        ((Opens.map (F.map A.unop.hom)).obj Uᵢ)).obj
        (overSmallIndexIdentityObject A) := by
  let Uⱼ := (Opens.map (F.map A.unop.hom)).obj Uᵢ
  refine fun s ↦ cast ?_
    ((((pullbackPushforwardAdjunction (Type (max u v)) (𝟙 (F.obj A.unop.left))).leftAdjointIdIso
      (eqToIso rfl)).inv.app (stageSheaf A.unop.left)).1.app (op Uⱼ) s)
  dsimp [Uⱼ, InverseLimitTypeSheafSystem.projectionOpenSectionDiagram,
    InverseLimitTypeSheafSystem.projectionOpenSectionValue,
    InverseLimitTypeSheafSystem.stageSectionFunctor,
    InverseLimitTypeSheafSystem.projectionPushforwardDiagram,
    limitPullbackSectionsDiagram, overSmallIndexDiagram,
    overSmallIndexIdentityBase, overSmallIndexIdentityObject]
  have hmap :
      𝟙 (F.obj A.unop.left) =
        F.map ((𝟙 (overSmallIndexIdentityBase A) :
          overSmallIndexIdentityBase A ⟶ overSmallIndexIdentityBase A).down).left := by
    change 𝟙 (F.obj A.unop.left) = F.map (𝟙 A.unop.left)
    simp
  exact
    congrArg
      (fun f : F.obj A.unop.left ⟶ F.obj A.unop.left ↦
        ((((pullback (Type (max u v)) f).obj (stageSheaf A.unop.left)).presheaf).obj
          (op ((Opens.map f).obj Uⱼ))))
      hmap

/-- Helper for Lemma 6.29.4: after pushing the adjunction-unit formula for `stagePullbackMap`
through the outer map `a : j ⟶ i`, the result is still compatible with the same
`pushforwardEq` transport that defines the outer over-category transition. -/
public theorem overSmallIndex_stageMap_unit_outer_pushforwardEq_apply
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ)
    (C : (Over (overSmallIndexIdentityBase A))ᵒᵖ)
    (s : (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).obj A) :
    let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp;
    let b := (AsSmall.down.map C.unop.hom).left;
    (((TopCat.Presheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map
          (((pullbackPushforwardAdjunction (Type (max u v)) (F.map b)).unit.app
                (stageSheaf A.unop.left) ≫
              (pushforward (Type (max u v)) (F.map b)).map
                (InverseLimitTypeSheafSystem.stagePullbackMap (setup := σ) b)).1) ≫
        (TopCat.Presheaf.pushforwardEq
          (projectionPushforwardMap_eq F (overSmallIndexOuterHom A C))
          (stageSheaf (overSmallIndexOuterObject A C).unop.left).presheaf).inv).app
      (op Uᵢ)) s =
    (((TopCat.Presheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map
          (stageMap b).1 ≫
        (TopCat.Presheaf.pushforwardEq
          (projectionPushforwardMap_eq F (overSmallIndexOuterHom A C))
          (stageSheaf (overSmallIndexOuterObject A C).unop.left).presheaf).inv).app
      (op Uᵢ)) s := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  let b := (AsSmall.down.map C.unop.hom).left
  exact
    congrArg
      (fun e :
          stageSheaf A.unop.left ⟶
            (pushforward (Type (max u v)) (F.map b)).obj
              (stageSheaf (overSmallIndexOuterObject A C).unop.left) ↦
        (((TopCat.Presheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map e.1 ≫
            (TopCat.Presheaf.pushforwardEq
              (projectionPushforwardMap_eq F (overSmallIndexOuterHom A C))
              (stageSheaf (overSmallIndexOuterObject A C).unop.left).presheaf).inv).app
          (op Uᵢ)) s)
      (InverseLimitTypeSheafSystem.stageMap_unit_stagePullbackMap (setup := σ) b)

/-- Helper for Lemma 6.29.4: after putting an outer source section into the identity object of
the small over-index category, the small-over limit comparison is the transported outer
source-to-pulled-back comparison. -/
public theorem overSmallIndex_identitySource_limitPullbackSectionsColimitMap
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ)
    (s : (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).obj A) :
    limitPullbackSectionsColimitMap
        (overSmallIndexDiagram (F := F) A.unop.left)
        (overSmallIndexIdentityBase A)
        (stageSheaf A.unop.left)
        ((Opens.map (F.map A.unop.hom)).obj Uᵢ)
        (colimit.ι
          (limitPullbackSectionsDiagram
            (overSmallIndexDiagram (F := F) A.unop.left)
            (overSmallIndexIdentityBase A)
            (stageSheaf A.unop.left)
            ((Opens.map (F.map A.unop.hom)).obj Uᵢ))
          (overSmallIndexIdentityObject A)
          (overSmallIndexIdentitySource
            (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
            (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A s)) =
      overSmallIndexProjectionTargetMap
        (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
        (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A
        (InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap
          (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ A s) := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  let H := overSmallIndexLimitIso (F := F) A.unop.left
  let Uⱼ := (Opens.map (F.map A.unop.hom)).obj Uᵢ
  have hunit :=
    pullbackSectionsToLimitMap_identity_over_stage_eq_unit
      (F := overSmallIndexDiagram (F := F) A.unop.left)
      (k := overSmallIndexIdentityBase A)
      (ℋ := stageSheaf A.unop.left) (U0 := Uⱼ) (σ := s)
  have hbase :
      H.hom ≫ limit.π F A.unop.left =
        limit.π (overSmallIndexDiagram (F := F) A.unop.left)
          (overSmallIndexIdentityBase A) := by
    simpa [H, overSmallIndexIdentityBase] using
      overSmallIndexLimitIso_hom_base_π (F := F) A.unop.left
  have hcomp :=
    @InverseLimitTypeSheafSystem.pullback_unit_comp_section_eq.{u, v}
      (f := H.hom) (g := limit.π F A.unop.left)
      (𝒢 := stageSheaf A.unop.left) (U := Uⱼ) (s := s)
  have hleft :
      limitPullbackSectionsColimitMap
          (overSmallIndexDiagram (F := F) A.unop.left)
          (overSmallIndexIdentityBase A)
          (stageSheaf A.unop.left) Uⱼ
          (colimit.ι
            (limitPullbackSectionsDiagram
              (overSmallIndexDiagram (F := F) A.unop.left)
              (overSmallIndexIdentityBase A)
              (stageSheaf A.unop.left) Uⱼ)
            (overSmallIndexIdentityObject A)
            (overSmallIndexIdentitySource
              (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
              (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A s)) =
        (((pullbackPushforwardAdjunction (Type (max u v))
              (limit.π (overSmallIndexDiagram (F := F) A.unop.left)
                (overSmallIndexIdentityBase A))).unit.app
            (stageSheaf A.unop.left)).1.app (op Uⱼ)) s := by
    simpa [limitPullbackSectionsColimitMap, limitPullbackSectionsCocone,
      overSmallIndexIdentityBase, overSmallIndexIdentityObject,
      overSmallIndexIdentitySource, Uⱼ] using hunit
  rw [hleft]
  rw [InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap_eq_unit_pushforwardEq]
  dsimp [overSmallIndexProjectionTargetMap, overSmallIndexProjectionTargetSheafIso]
  rw [eq_comm]
  apply cast_eq_iff_heq.mpr
  have hcomposite :=
    @InverseLimitTypeSheafSystem.pullback_unit_comp_pushforwardEq_eqToHom_heq.{u, v}
      (limit (overSmallIndexDiagram (F := F) A.unop.left)) (limit F)
      (F.obj A.unop.left) (F.obj i)
      H.hom (limit.π F A.unop.left) (F.map A.unop.hom)
      (limit.π F i) (limit.w F A.unop.hom).symm
      (limit.π (overSmallIndexDiagram (F := F) A.unop.left)
        (overSmallIndexIdentityBase A))
      hbase
      (stageSheaf A.unop.left) Uᵢ s
  simpa [H, Uⱼ, TopCat.Presheaf.pushforwardEq, eqToHom_map] using hcomposite

/-- Helper for Lemma 6.29.4: refining the identity small-over representative and then translating
it back to the outer over-category gives the ordinary outer transition of the original section. -/
public theorem overSmallIndex_sourceToOuter_identity_refinement_apply
    {i : I} (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ)
    (C : (Over (overSmallIndexIdentityBase A))ᵒᵖ)
    (f : overSmallIndexIdentityObject A ⟶ C)
    (s : (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).obj A) :
    overSmallIndexSourceToOuter
        (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
        (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C
        ((limitPullbackSectionsDiagram
          (overSmallIndexDiagram (F := F) A.unop.left)
          (overSmallIndexIdentityBase A)
          (stageSheaf A.unop.left)
          ((Opens.map (F.map A.unop.hom)).obj Uᵢ)).map f
          (overSmallIndexIdentitySource
            (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
            (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A s)) =
      (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
        (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).map
        (overSmallIndexOuterHom A C) s := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  have hf : f.unop.left = C.unop.hom := by
    simpa using (Over.w f.unop)
  have hfOver :
      f.unop =
        (Over.homMk C.unop.hom (by
          simpa [overSmallIndexIdentityObject]) :
          C.unop ⟶ (overSmallIndexIdentityObject A).unop) := by
    ext
    exact hf
  have hunit :=
    overSmallIndex_stageMap_unit_outer_pushforwardEq_apply
      (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
      (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C s
  have hinner :=
    overPullbackSectionsMap_identity_over_stage_eq_pullback_unit
      (F := overSmallIndexDiagram (F := F) A.unop.left)
      (c := C.unop.hom) (ℋ := stageSheaf A.unop.left)
      (U0 := (Opens.map (F.map A.unop.hom)).obj Uᵢ) (σ := s)
  have hmap :
      ((limitPullbackSectionsDiagram
          (overSmallIndexDiagram (F := F) A.unop.left)
          (overSmallIndexIdentityBase A)
          (stageSheaf A.unop.left)
          ((Opens.map (F.map A.unop.hom)).obj Uᵢ)).map f
        (overSmallIndexIdentitySource
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A s)) =
      (((pullbackPushforwardAdjunction (Type (max u v))
          (F.map (AsSmall.down.map C.unop.hom).left)).unit.app
            (stageSheaf A.unop.left)).1.app
        (op ((Opens.map (F.map A.unop.hom)).obj Uᵢ)) s) := by
    simpa [hfOver, limitPullbackSectionsDiagram, overSmallIndexIdentitySource,
      overSmallIndexDiagram] using hinner
  rw [hmap]
  have hleft :
      (overSmallIndexSourceToOuter
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C
          ((((pullbackPushforwardAdjunction (Type (max u v))
              (F.map (AsSmall.down.map C.unop.hom).left)).unit.app
                (stageSheaf A.unop.left)).1.app
            (op ((Opens.map (F.map A.unop.hom)).obj Uᵢ)) s))) =
        ((((TopCat.Presheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map
              ((((pullbackPushforwardAdjunction (Type (max u v))
                    (F.map (AsSmall.down.map C.unop.hom).left)).unit.app
                  (stageSheaf A.unop.left) ≫
                (pushforward (Type (max u v))
                  (F.map (AsSmall.down.map C.unop.hom).left)).map
                  (InverseLimitTypeSheafSystem.stagePullbackMap
                    (setup := σ) (AsSmall.down.map C.unop.hom).left)).1)) ≫
            (TopCat.Presheaf.pushforwardEq
              (projectionPushforwardMap_eq F (overSmallIndexOuterHom A C))
              (stageSheaf (overSmallIndexOuterObject A C).unop.left).presheaf).inv).app
          (op Uᵢ)) s) := by
    dsimp [overSmallIndexSourceToOuter]
    apply cast_eq_iff_heq.mpr
    let b := (AsSmall.down.map C.unop.hom).left
    let α :
        (stageSheaf A.unop.left).presheaf ⟶
          (TopCat.Presheaf.pushforward (Type (max u v)) (F.map b)).obj
            (stageSheaf (overSmallIndexOuterObject A C).unop.left).presheaf :=
      (((pullbackPushforwardAdjunction (Type (max u v)) (F.map b)).unit.app
          (stageSheaf A.unop.left) ≫
        (pushforward (Type (max u v)) (F.map b)).map
          (InverseLimitTypeSheafSystem.stagePullbackMap (setup := σ) b)).1)
    have hpush :=
      @pushforward_map_comp_inv_app_heq.{u, v}
        (F.obj (overSmallIndexOuterObject A C).unop.left)
        (F.obj A.unop.left) (F.obj i)
        (b := F.map b) (a := F.map A.unop.hom)
        (c := F.map (overSmallIndexOuterObject A C).unop.hom)
        (hc := projectionPushforwardMap_eq F (overSmallIndexOuterHom A C))
        (P := (stageSheaf A.unop.left).presheaf)
        (Q := (stageSheaf (overSmallIndexOuterObject A C).unop.left).presheaf)
        (α := α) Uᵢ s
    simpa [σ, b, α] using hpush.symm
  exact hleft.trans (by
    simpa [σ, InverseLimitTypeSheafSystem.projectionOpenSectionDiagram,
      InverseLimitTypeSheafSystem.projectionOpenSectionValue,
      InverseLimitTypeSheafSystem.stageSectionFunctor,
      InverseLimitTypeSheafSystem.projectionPushforwardDiagram,
      projectionPushforwardMap, overSmallIndexOuterObject, overSmallIndexOuterHom,
      TopCat.Sheaf.pushforward_map, overSmallIndexDiagram, Category.assoc] using hunit)

/-- Helper for Lemma 6.29.4: equality after the source-to-pulled-back map at an outer object is
detected after a small-over refinement, translated back to the outer over-category. -/
public theorem overSmallIndex_projectionOpen_eventual_injective
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    {i : I} (Uᵢ : Opens (F.obj i)) (hUᵢ : IsCompact (Uᵢ : Set (F.obj i)))
    (A : (Over i)ᵒᵖ)
    {x y : (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).obj A}
    (hxy :
      (InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap
        (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ A) x =
      (InverseLimitTypeSheafSystem.projectionOpenSectionToPulledBackStageMap
        (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ A) y) :
    ∃ C : (Over ((AsSmall.up :
      Over A.unop.left ⥤ AsSmall.{max u v} (Over A.unop.left)).obj
        (Over.mk (𝟙 A.unop.left) : Over A.unop.left)))ᵒᵖ,
      (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
        (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).map
          (overSmallIndexOuterHom A C) x =
        (InverseLimitTypeSheafSystem.projectionOpenSectionDiagram
          (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ).map
          (overSmallIndexOuterHom A C) y := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  let Uⱼ := (Opens.map (F.map A.unop.hom)).obj Uᵢ
  let D :=
    limitPullbackSectionsDiagram
      (overSmallIndexDiagram (F := F) A.unop.left)
      (overSmallIndexIdentityBase A)
      (stageSheaf A.unop.left) Uⱼ
  let xid :=
    overSmallIndexIdentitySource
      (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
      (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A x
  let yid :=
    overSmallIndexIdentitySource
      (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
      (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A y
  have hsmallIso :
      IsIso (limitPullbackSectionsColimitMap
        (overSmallIndexDiagram (F := F) A.unop.left)
        (overSmallIndexIdentityBase A)
        (stageSheaf A.unop.left) Uⱼ) := by
    exact overSmallIndex_projectionOpen_limitPullbackSectionsColimitMap_isIso
      (F := F) (stageSheaf := stageSheaf) hF Uᵢ hUᵢ A
  have hinjSmall :
      Function.Injective (limitPullbackSectionsColimitMap
        (overSmallIndexDiagram (F := F) A.unop.left)
        (overSmallIndexIdentityBase A)
        (stageSheaf A.unop.left) Uⱼ) := by
    have hbij :
        Function.Bijective (limitPullbackSectionsColimitMap
          (overSmallIndexDiagram (F := F) A.unop.left)
          (overSmallIndexIdentityBase A)
          (stageSheaf A.unop.left) Uⱼ) := by
      rw [← CategoryTheory.isIso_iff_bijective]
      exact hsmallIso
    exact hbij.1
  have hxmap :
      limitPullbackSectionsColimitMap
          (overSmallIndexDiagram (F := F) A.unop.left)
          (overSmallIndexIdentityBase A)
          (stageSheaf A.unop.left) Uⱼ
          (colimit.ι D (overSmallIndexIdentityObject A) xid) =
        overSmallIndexProjectionTargetMap
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A
          (σ.projectionOpenSectionToPulledBackStageMap i Uᵢ A x) := by
    simpa [σ, D, xid, Uⱼ] using
      overSmallIndex_identitySource_limitPullbackSectionsColimitMap
        (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
        (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A x
  have hymap :
      limitPullbackSectionsColimitMap
          (overSmallIndexDiagram (F := F) A.unop.left)
          (overSmallIndexIdentityBase A)
          (stageSheaf A.unop.left) Uⱼ
          (colimit.ι D (overSmallIndexIdentityObject A) yid) =
        overSmallIndexProjectionTargetMap
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A
          (σ.projectionOpenSectionToPulledBackStageMap i Uᵢ A y) := by
    simpa [σ, D, yid, Uⱼ] using
      overSmallIndex_identitySource_limitPullbackSectionsColimitMap
        (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
        (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A y
  have htarget :
      overSmallIndexProjectionTargetMap
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A
          (σ.projectionOpenSectionToPulledBackStageMap i Uᵢ A x) =
        overSmallIndexProjectionTargetMap
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A
          (σ.projectionOpenSectionToPulledBackStageMap i Uᵢ A y) := by
    exact congrArg
      (overSmallIndexProjectionTargetMap
        (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
        (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A)
      (by simpa [σ] using hxy)
  have hcolim :
      colimit.ι D (overSmallIndexIdentityObject A) xid =
        colimit.ι D (overSmallIndexIdentityObject A) yid := by
    apply hinjSmall
    exact hxmap.trans (htarget.trans hymap.symm)
  obtain ⟨C, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (F := D) (colimit.isColimit D) xid yid).1 hcolim
  refine ⟨C, ?_⟩
  have hxouter :=
    overSmallIndex_sourceToOuter_identity_refinement_apply
      (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
      (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp)
      Uᵢ A C f x
  have hyouter :=
    overSmallIndex_sourceToOuter_identity_refinement_apply
      (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
      (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp)
      Uᵢ A C f y
  rw [← hxouter, ← hyouter]
  exact congrArg
    (overSmallIndexSourceToOuter
      (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
      (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C)
    hf

/-- The projection pullback of a compact open stage subset satisfies the finite-refinement
hypothesis used by Lemma 6.29.1. This packages the Stacks invocation of Topology, Lemma 5.24.5
and Lemma 5.27.1 in the exact form needed for the colimit-sheaf section comparison. -/
public theorem projection_preimage_hasCofinalFiniteQuasiCompactOverlapCoverings
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    (i : I) (Uᵢ : Opens (F.obj i)) (hUᵢ : IsCompact (Uᵢ : Set (F.obj i))) :
    CategoryTheory.GrothendieckTopology.HasCofinalFiniteQuasiCompactOverlapCoverings
      (Opens.grothendieckTopology ↥(limit F)) ((Opens.map (limit.π F i)).obj Uᵢ) := by
  classical
  letI : SpectralSpace ↥(limit F) :=
    spectralSpace_of_isLimit_of_cofiltered_spectral_diagram
      (C := limit.cone F) (limit.isLimit F) (fun {j k} a ↦ hF a)
  have hπ : IsSpectralMap (limit.π F i) :=
    isSpectralMap_projection_of_isLimit_of_cofiltered_spectral_diagram
      (C := limit.cone F) (limit.isLimit F) (fun {j k} a ↦ hF a) i
  let U : CompactOpens ↥(limit F) :=
    ⟨⟨((Opens.map (limit.π F i)).obj Uᵢ : Set ↥(limit F)), by
        change IsCompact ((limit.π F i) ⁻¹' (Uᵢ : Set (F.obj i)))
        exact hπ.isCompact_preimage_of_isOpen Uᵢ.isOpen hUᵢ⟩,
      ((Opens.map (limit.π F i)).obj Uᵢ).isOpen⟩
  refine ⟨?_⟩
  intro ι V hV_le hcover
  have hcover_set : (U : Set ↥(limit F)) ⊆ ⋃ a, (V a : Set ↥(limit F)) := by
    intro x hx
    rcases hcover ⟨x, by simpa [U] using hx⟩ with ⟨a, hxa⟩
    exact Set.mem_iUnion.2 ⟨a, hxa⟩
  obtain ⟨s, hs_cover, hs_subordinate⟩ :=
    compactOpen_hasCofinalFiniteQuasiCompactRefiningCovers U V hcover_set
  let t : Finset (Opens ↥(limit F)) := s.image CompactOpens.toOpens
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · intro W hW
    rcases Finset.mem_image.1 hW with ⟨K, hK, rfl⟩
    intro x hx
    have hxU : x ∈ (U : Set ↥(limit F)) := by
      rw [hs_cover]
      exact Set.mem_iUnion₂.2 ⟨K, hK, hx⟩
    simpa [U, CompactOpens.toOpens] using hxU
  · intro W hW
    rcases Finset.mem_image.1 hW with ⟨K, hK, rfl⟩
    obtain ⟨a, ha⟩ := hs_subordinate K hK
    exact ⟨a, by simpa [CompactOpens.toOpens] using ha⟩
  · intro x
    have hxU : (x : ↥(limit F)) ∈ (U : Set ↥(limit F)) := by
      simpa [U] using x.2
    rw [hs_cover] at hxU
    rcases Set.mem_iUnion₂.1 hxU with ⟨K, hK, hxK⟩
    exact ⟨K.toOpens, Finset.mem_image.2 ⟨K, hK, rfl⟩, by simpa [CompactOpens.toOpens] using hxK⟩
  · intro W hW W' hW'
    rcases Finset.mem_image.1 hW with ⟨K, hK, rfl⟩
    rcases Finset.mem_image.1 hW' with ⟨K', hK', rfl⟩
    simpa [CompactOpens.toOpens] using ((K ⊓ K' : CompactOpens ↥(limit F)).isCompact)

/-- The Lemma 6.29.1 part of Lemma 6.29.4: after reindexing the pulled-back sheaf diagram by
`(Over i)ᵒᵖ`, the comparison from the colimit of pulled-back stage sections to sections of the
colimit sheaf is an isomorphism. -/
public theorem projectionPulledBackSectionsComparison_isIso_viaSheafColimit
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    (i : I) (Uᵢ : Opens (F.obj i)) (hUᵢ : IsCompact (Uᵢ : Set (F.obj i))) :
    IsIso (InverseLimitTypeSheafSystem.projectionPulledBackSectionsComparison
      (setup F stageSheaf stageMap stageMap_id stageMap_comp) i Uᵢ) := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  letI : SpectralSpace ↥(limit F) :=
    spectralSpace_of_isLimit_of_cofiltered_spectral_diagram
      (C := limit.cone F) (limit.isLimit F) (fun {j k} a ↦ hF a)
  have hcover :=
    projection_preimage_hasCofinalFiniteQuasiCompactOverlapCoverings
      (F := F) hF i Uᵢ hUᵢ
  have hpost :
      IsIso
        (colimit.post ((Over.forget i).op ⋙ σ.pulledBackDiagram)
          (InverseLimitTypeSheafSystem.limitProjectionSectionFunctor (F := F) i Uᵢ)) := by
    rw [CategoryTheory.isIso_iff_bijective]
    exact
      bijective_sheafColimitSectionComparison_of_cofinalFiniteQuasiCompactOverlapCoverings
        ((Over.forget i).op ⋙ σ.pulledBackDiagram)
        ((Opens.map (limit.π F i)).obj Uᵢ)
        hcover
  have hfinal :
      IsIso
        ((InverseLimitTypeSheafSystem.limitProjectionSectionFunctor (F := F) i Uᵢ).map
          (Functor.Final.colimitIso (Over.forget i).op σ.pulledBackDiagram).hom) := by
    infer_instance
  simpa [InverseLimitTypeSheafSystem.projectionPulledBackSectionsComparison, σ] using
    (IsIso.comp_isIso' hpost hfinal)

-- Proof sketch: restrict each `stageSheaf j` to the compact-open basis site of `F.obj j`, package
-- the resulting basis sites into the canonical Chapter 7 owner
-- `CategoryTheory.CofilteredSiteDiagram`, convert `stageMap` to the corresponding
-- `CategoryTheory.ColimitSiteStageFamily` transition maps via the pullback-pushforward adjunction,
-- identify the topological comparison map above with
-- `CategoryTheory.colimitSiteStageFamilySectionsComparison`, and apply the site-level bijectivity
-- theorem together with Lemma `6.29.3`.
public theorem projectionOpenSectionsComparison_isIso_viaSiteComparison
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    (i : I) (Uᵢ : Opens (F.obj i)) (hUᵢ : IsCompact (Uᵢ : Set (F.obj i))) :
    IsIso (projectionOpenSectionsComparison F stageSheaf stageMap stageMap_id stageMap_comp
      i Uᵢ) := by
  let σ := setup F stageSheaf stageMap stageMap_id stageMap_comp
  -- The source proof first replaces the stage sections by the corresponding pulled-back
  -- stage sections.  This is the formal/Fubini plus Lemma 6.29.3 step; it remains the only
  -- nontrivial local comparison before applying the sheaf-colimit section theorem.
  have hfirst :
      IsIso (σ.projectionOpenToPulledBackSectionsColimitMap i Uᵢ) := by
    rw [σ.projectionOpenToPulledBackSectionsColimitMap_eq_colimMap i Uᵢ]
    rw [CategoryTheory.isIso_iff_bijective]
    refine filtered_colimMap_bijective_of_eventual
      (σ.projectionOpenToPulledBackSectionsNatTrans i Uᵢ) ?_ ?_
    · intro A y
      -- Apply Lemma 6.29.3 over the small over-category above the outer stage `A.unop.left`.
      let D :=
        limitPullbackSectionsDiagram
          (overSmallIndexDiagram (F := F) A.unop.left)
          (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
          (stageSheaf A.unop.left)
          ((Opens.map (F.map A.unop.hom)).obj Uᵢ)
      have hsmall :
          IsIso (limitPullbackSectionsColimitMap
            (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
            (stageSheaf A.unop.left)
            ((Opens.map (F.map A.unop.hom)).obj Uᵢ)) := by
        exact overSmallIndex_projectionOpen_limitPullbackSectionsColimitMap_isIso
          (F := F) (stageSheaf := stageSheaf) hF Uᵢ hUᵢ A
      have hsurjSmall :
          Function.Surjective (limitPullbackSectionsColimitMap
            (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
            (stageSheaf A.unop.left)
            ((Opens.map (F.map A.unop.hom)).obj Uᵢ)) := by
        have hbij :
            Function.Bijective (limitPullbackSectionsColimitMap
              (overSmallIndexDiagram (F := F) A.unop.left)
              (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
              (stageSheaf A.unop.left)
              ((Opens.map (F.map A.unop.hom)).obj Uᵢ)) := by
          rw [← CategoryTheory.isIso_iff_bijective]
          exact hsmall
        exact hbij.2
      obtain ⟨z, hz⟩ := hsurjSmall
        (overSmallIndexProjectionTargetMap
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A y)
      obtain ⟨C, s, hs⟩ := Types.jointly_surjective' (F := D) z
      refine ⟨overSmallIndexOuterObject A C, overSmallIndexOuterHom A C,
        overSmallIndexSourceToOuter
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A C s, ?_⟩
      have hrep :
          limitPullbackSectionsColimitMap
            (overSmallIndexDiagram (F := F) A.unop.left)
            (AsSmall.up.obj (Over.mk (𝟙 A.unop.left)))
            (stageSheaf A.unop.left)
            ((Opens.map (F.map A.unop.hom)).obj Uᵢ)
            (colimit.ι D C s) =
            overSmallIndexProjectionTargetMap
              (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
              (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) Uᵢ A y := by
        rw [hs]
        exact hz
      simpa [D, σ] using
        overSmallIndex_projectionOpen_source_to_outer_refinement_apply
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp)
          Uᵢ A C s y hrep
    · intro A x y hxy
      -- The small-over injectivity statement gives a refinement over `A.unop.left`; translate it
      -- into the corresponding composite object in the original outer over-category.
      obtain ⟨C, hC⟩ :=
        overSmallIndex_projectionOpen_eventual_injective
          (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
          (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp)
          hF Uᵢ hUᵢ A hxy
      exact ⟨overSmallIndexOuterObject A C, overSmallIndexOuterHom A C, by
        simpa [σ] using hC⟩
  -- Lemma 6.29.1 supplies the second comparison: sections of the over-category colimit of
  -- pulled-back stage sheaves agree with sections of the colimit sheaf over `p_i⁻¹(U_i)`.
  have hsecond :
      IsIso (σ.projectionPulledBackSectionsComparison i Uᵢ) := by
    exact projectionPulledBackSectionsComparison_isIso_viaSheafColimit
      (F := F) (stageSheaf := stageSheaf) (stageMap := stageMap)
      (stageMap_id := stageMap_id) (stageMap_comp := stageMap_comp) hF i Uᵢ hUᵢ
  have hcomp :
      σ.projectionOpenToPulledBackSectionsColimitMap i Uᵢ ≫
          σ.projectionPulledBackSectionsComparison i Uᵢ =
        σ.projectionOpenSectionsComparison i Uᵢ :=
    σ.projectionOpenToPulledBackSectionsColimitMap_comp i Uᵢ
  have htotal :
      IsIso (σ.projectionOpenToPulledBackSectionsColimitMap i Uᵢ ≫
        σ.projectionPulledBackSectionsComparison i Uᵢ) :=
    IsIso.comp_isIso' hfirst hsecond
  rw [hcomp] at htotal
  simpa [projectionOpenSectionsComparison, σ] using htotal

end

end SpectralInverseLimit

/-- Lemma 6.29.4: in the inverse-limit situation for spectral spaces and compatible type-valued
sheaves, if `U_i ⊆ X_i` is quasi-compact open, then the canonical map
`\mathop{\mathrm{colim}}_{a : j \to i} \mathcal{F}_j(f_a^{-1}(U_i)) \to
(\mathop{\mathrm{colim}}_j p_j^{-1}\mathcal{F}_j)(p_i^{-1}(U_i))`
is an isomorphism. -/
theorem spectralInverseLimit_projectionOpenSectionsComparison_isIso
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    (F : I ⥤ TopCat.{max u v}) [∀ j : I, SpectralSpace ↥(F.obj j)]
    (stageSheaf : ∀ i : I, TopCat.Sheaf (Type (max u v)) (F.obj i))
    (stageMap : ∀ {j k : I} (a : j ⟶ k),
      stageSheaf k ⟶
        (pushforward (Type (max u v)) (F.map a)).obj (stageSheaf j))
    (stageMap_id :
      ∀ i : I,
        stageMap (𝟙 i) =
          ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
            (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩)
    (stageMap_comp :
      ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
        stageMap (b ≫ a) =
          ⟨(stageMap a ≫ (pushforward (Type (max u v)) (F.map a)).map (stageMap b)).1 ≫
            (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩)
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    [HasColimitsOfShape Iᵒᵖ (TopCat.Sheaf (Type (max u v)) (limit F))]
    (i : I) (Uᵢ : Opens (F.obj i)) (hUᵢ : IsCompact (Uᵢ : Set (F.obj i))) :
    IsIso (SpectralInverseLimit.projectionOpenSectionsComparison
      F stageSheaf stageMap stageMap_id stageMap_comp i Uᵢ) :=
  SpectralInverseLimit.projectionOpenSectionsComparison_isIso_viaSiteComparison
    F stageSheaf stageMap stageMap_id stageMap_comp hF i Uᵢ hUᵢ
