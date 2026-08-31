module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_29_2
public import stacks_project.Chap07.Lemma_7_28_1
public import stacks_project.Chap07.Lemma_7_28_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.29.3:
- primary domain: comparison-lemma style sheaf equivalences for dense subsites and their slice-site
  localizations;
- sampled owner API:
  `Functor.IsDenseSubsite`,
  `Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension`,
  `Over.post`;
- source/core/bridge triage:
  `source-facing`: the localized dense-subsite instance for `Over.post u`;
  `core/canonical`: the dense-subsite direct-image equivalence instance for
  `G.sheafPushforwardCocontinuous`;
  `bridge/view`: the slice-site specialization obtained by instantiating that canonical instance at
  `G := Over.post u`.

Primitive data here are only the functor `u`, the object `U`, and the owner instance
`u.IsDenseSubsite J K`. The sheaf-equivalence statement is derived API from that
owner together with separate pointwise right Kan extension hypotheses on `Over.post u`, so this
file should keep only the localized owner instance and recall the bridge theorem directly rather
than introducing a parallel theorem wrapper.
-/

/-- Helper for Lemma 7.29.3: equalizer sieves in the slice category transport to equalizer sieves
of the underlying arrows in the base category. -/
private theorem overEquiv_equalizer
    {U : C} {X Y : Over U} (f g : X ⟶ Y) :
    Sieve.overEquiv X (Sieve.equalizer f g) = Sieve.equalizer f.left g.left := by
  ext Z k
  rw [Sieve.overEquiv_iff]
  constructor
  · -- Equality of slice morphisms is detected on their underlying arrows.
    intro hk
    change (Over.homMk k : Over.mk (k ≫ X.hom) ⟶ X) ≫ f =
        (Over.homMk k : Over.mk (k ≫ X.hom) ⟶ X) ≫ g at hk
    simpa using congrArg CommaMorphism.left hk
  · -- Conversely, equal underlying arrows give equal morphisms in the slice.
    intro hk
    change (Over.homMk k : Over.mk (k ≫ X.hom) ⟶ X) ≫ f =
        (Over.homMk k : Over.mk (k ≫ X.hom) ⟶ X) ≫ g
    apply Over.OverMorphism.ext
    simpa using hk

/-- Helper for Lemma 7.29.3: the pushforward-covering criterion for `Over.post u` is exactly the
base dense-subsite criterion for `u` transported along the slice forgetful functors. -/
private theorem overPost_functorPushforward_mem_iff
    (u : C ⥤ D) [u.IsDenseSubsite J K] {U : C} {X : Over U} {S : Sieve X} :
    S.functorPushforward (Over.post u) ∈ K.over (u.obj U) ((Over.post u).obj X) ↔ S ∈ J.over U X := by
  -- After moving both slice sieves to the base categories, this is exactly the defining dense
  -- subsite equivalence for `u`.
  rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
    overEquiv_functorPushforward_post]
  exact Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J) (K := K) (G := u)

/-- Helper for Lemma 7.29.3: local faithfulness of `u` on the base site upgrades directly to local
faithfulness of `Over.post u` on the slice site. -/
private theorem overPost_equalizer_mem
    (u : C ⥤ D) [u.IsDenseSubsite J K] {U : C} {X Y : Over U}
    (a b : X ⟶ Y) (h : (Over.post u).map a = (Over.post u).map b) :
    Sieve.equalizer a b ∈ J.over U X := by
  -- Transport the slice equalizer sieve to the base, then apply local faithfulness for `u`.
  rw [GrothendieckTopology.mem_over_iff, overEquiv_equalizer]
  have hleft : u.map a.left = u.map b.left := by
    simpa using congrArg CommaMorphism.left h
  exact Functor.IsDenseSubsite.equalizer_mem J K u a.left b.left hleft

/-- Helper for Lemma 7.29.3: local fullness on the slice follows by first lifting the underlying
arrow in the base, then refining by a covering equalizer so the lift becomes a morphism over
`U`. -/
private theorem overPost_imageSieve_mem
    (u : C ⥤ D) [u.IsDenseSubsite J K] {U : C} {X Y : Over U}
    (c : (Over.post u).obj X ⟶ (Over.post u).obj Y) :
    (Over.post u).imageSieve c ∈ J.over U X := by
  rw [GrothendieckTopology.mem_over_iff]
  let R : Sieve X.left := Sieve.overEquiv X ((Over.post u).imageSieve c)
  have hT : u.imageSieve c.left ∈ J X.left := Functor.IsDenseSubsite.imageSieve_mem J K u c.left
  -- Start from the base image-sieve cover and refine it by equalizers forcing the lifted arrow to
  -- commute with the structure map to `U`.
  refine J.transitive hT R ?_
  intro Z g hg
  rcases hg with ⟨l, hl⟩
  have hEq : Sieve.equalizer (l ≫ Y.hom) (g ≫ X.hom) ∈ J Z := by
    apply Functor.IsDenseSubsite.equalizer_mem J K u (l ≫ Y.hom) (g ≫ X.hom)
    rw [Functor.map_comp, Functor.map_comp]
    calc
      u.map l ≫ u.map Y.hom = (u.map g ≫ c.left) ≫ u.map Y.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ t ≫ u.map Y.hom) hl
      _ = u.map g ≫ u.map X.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ u.map g ≫ t) (Over.w c)
  refine J.superset_covering ?_ hEq
  intro V p hp
  rw [Sieve.pullback_apply]
  rw [Sieve.overEquiv_iff]
  refine ⟨Over.homMk (p ≫ l) ?_, ?_⟩
  · simpa [Category.assoc] using hp
  · -- After restricting by the equalizer cover, the lifted arrow is genuinely a morphism over
    -- `U`, hence it lies in the slice image sieve.
    apply Over.OverMorphism.ext
    simpa [Category.assoc] using congrArg (fun t ↦ u.map p ≫ t) hl

/-- Helper for Lemma 7.29.3: the slice cover-by-image sieve is covering because every base
factorization through `u.obj W` can be refined by a cover on `W` whose lifted arrows land over
`U`. -/
private theorem coverByImage_mem_over_post
    (u : C ⥤ D) [u.IsDenseSubsite J K] {U : C}
    (Y : Over (u.obj U)) :
    Sieve.coverByImage (Over.post u) Y ∈ K.over (u.obj U) Y := by
  letI : u.IsCoverDense K := Functor.IsDenseSubsite.isCoverDense J K u
  rw [GrothendieckTopology.mem_over_iff]
  let R : Sieve Y.left := Sieve.overEquiv Y (Sieve.coverByImage (Over.post u) Y)
  have hT : Sieve.coverByImage u Y.left ∈ K Y.left := u.is_cover_of_isCoverDense K Y.left
  -- First cover `Y.left` by objects in the image of `u`, then use local fullness of `u` on the
  -- structure morphism to refine each such factorization into an actual slice factorization.
  refine K.transitive hT R ?_
  intro Z g hg
  rcases hg with ⟨⟨W, lift, map, fac⟩⟩
  let S : Sieve W := u.imageSieve (map ≫ Y.hom)
  have hS : S ∈ J W := Functor.IsDenseSubsite.imageSieve_mem J K u (map ≫ Y.hom)
  have hSu : S.functorPushforward u ∈ K (u.obj W) := by
    exact (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J) (K := K) (G := u)
      (X := W) (S := S)).2 hS
  have hPull : (S.functorPushforward u).pullback lift ∈ K Z := K.pullback_stable lift hSu
  refine K.superset_covering ?_ hPull
  intro V p hp
  rw [Sieve.pullback_apply] at hp
  rw [Sieve.pullback_apply]
  rw [Sieve.overEquiv_iff]
  rcases hp with ⟨W', a, b, ha, hfac⟩
  rcases ha with ⟨q, hq⟩
  refine ⟨⟨Over.mk q, Over.homMk b ?_, Over.homMk (u.map a ≫ map) ?_, ?_⟩⟩
  · change b ≫ u.map q = (p ≫ g) ≫ Y.hom
    calc
      b ≫ u.map q = (b ≫ u.map a) ≫ map ≫ Y.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ b ≫ t) hq
      _ = (p ≫ lift) ≫ map ≫ Y.hom := by rw [hfac]
      _ = (p ≫ g) ≫ Y.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ p ≫ t ≫ Y.hom) fac
  · change (u.map a ≫ map) ≫ Y.hom = u.map q
    simpa [Category.assoc] using hq.symm
  · -- The refined factorization is now represented by an honest object of `Over U`.
    apply Over.OverMorphism.ext
    change b ≫ (u.map a ≫ map) = p ≫ g
    calc
      b ≫ (u.map a ≫ map) = (b ≫ u.map a) ≫ map := by simp [Category.assoc]
      _ = (p ≫ lift) ≫ map := by rw [hfac]
      _ = p ≫ g := by simpa [Category.assoc] using congrArg (fun t ↦ p ≫ t) fac

/-- Lemma 7.29.3, source-facing owner layer: a dense-subsite functor remains a dense subsite
after passage to any slice site. -/
instance overPost_isDenseSubsite
    (u : C ⥤ D) (U : C) [u.IsDenseSubsite J K] :
    (Over.post u).IsDenseSubsite (J.over U) (K.over (u.obj U)) := by
  -- Route correction: the planned `sourceLocal_isDenseSubsite` bridge is not available, so we
  -- construct the dense-subsite owner directly from the slice versions of properties (3)–(5).
  refine
    { isCoverDense' := ?_
      isLocallyFull' := ?_
      isLocallyFaithful' := ?_
      functorPushforward_mem_iff := ?_ }
  · -- Property (5): the slice cover-by-image sieve is covering.
    exact ⟨fun Y ↦ coverByImage_mem_over_post (J := J) (K := K) u Y⟩
  · -- Property (4): source-local fullness upgrades to target-local fullness via the
    -- pushforward-covering criterion.
    exact
      ⟨fun c ↦ (overPost_functorPushforward_mem_iff (J := J) (K := K) u).2
        (overPost_imageSieve_mem (J := J) (K := K) u c)⟩
  · -- Property (3): source-local faithfulness upgrades in the same way.
    exact
      ⟨fun a b h ↦ (overPost_functorPushforward_mem_iff (J := J) (K := K) u).2
        (overPost_equalizer_mem (J := J) (K := K) u a b h)⟩
  · -- Property (2): coverings on the slice are exactly the coverings whose pushforward is a
    -- covering on the target slice.
    intro X S
    exact overPost_functorPushforward_mem_iff (J := J) (K := K) u

/- Lemma 7.29.3, bridge/view recall: once `overPost_isDenseSubsite` upgrades `Over.post u`
to the canonical dense-subsite owner on slice sites, the induced cocontinuous direct image
on sheaves of sets is an equivalence after supplying the needed pointwise right Kan extensions. -/
variable (u : C ⥤ D) (U : C) [u.IsDenseSubsite J K]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂),
  (Over.post u).op.HasPointwiseRightKanExtension P]

#synth
  ((Over.post u).sheafPushforwardCocontinuous (Type (max u₁ u₂ v₁ v₂)) (J.over U)
    (K.over (u.obj U))).IsEquivalence

end CategoryTheory
