module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import stacks_project.Chap05.Lemma_5_23_3
import stacks_project.Chap05.Lemma_5_24_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits

universe u v

/- Domain-style sampling for cofiltered inverse limits of spectral spaces:
- primary domain: constructible-topology descent along cofiltered inverse systems of spectral
  spaces;
- sampled owner declarations:
  `limit.π`,
  `CategoryTheory.Functor.stableSubsetDiagram`,
  `compactSpace_limit_of_constructibleClosed_stableSubsetDiagram`,
  `nonempty_limit_of_constructibleClosed_stableSubsetDiagram`;
- best owner abstraction: the source-facing restricted diagram
  `X.stableSubsetDiagram Z hZ_maps`, with eventual stagewise statements derived by applying the
  canonical nonemptiness theorem to the constructibly closed family cut out by the failure of the
  desired inclusion.

Primitive-vs-derived split:
- primitive data: the ambient cofiltered spectral diagram `X`, the chosen stage `i`, and the
  constructibly closed/open subsets `E` and `F` of `X.obj i`;
- derived API: the eventual-stage criterion for the pullback inclusion on the limit, obtained by
  comparing the empty pullback of `E \\ F` on the limit with eventual emptiness after pullback to a
  stage over `i`.

Layer triage:
- `source-facing`: the Stacks eventual-stage inclusion criterion;
- `core/canonical`: `limit.π` for the limit projection and
  `nonempty_limit_of_constructibleClosed_stableSubsetDiagram` for the cofiltered nonemptiness
  owner theorem;
- `bridge/view`: the passage from inclusion `p⁻¹' E ⊆ p⁻¹' F` to emptiness of the inverse-image
  family of `E \\ F` on the cofiltered over-category of `i`.
-/

section

variable {I : Type u} [Category.{v} I] [CategoryTheory.IsCofiltered I]
variable (X : I ⥤ TopCat.{max u v}) [∀ j : I, SpectralSpace ↥(X.obj j)]
variable (hX : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (X.map a))
variable (i : I) (E F : Set (X.obj i))
variable (hE : IsClosed[constructibleTopology (X.obj i)] E)
variable (hF : IsOpen[constructibleTopology (X.obj i)] F)

/-- Helper for Lemma 5.24.3: the original diagram reindexed on the over-category of `i`. -/
private abbrev overDiagram : Over i ⥤ TopCat.{max u v} :=
  (Over.forget i) ⋙ X

/-- Helper for Lemma 5.24.3: the stagewise pullback of the difference `E \ F` along an object of
`Over i`. -/
private abbrev overStageDifference (a : Over i) : Set (X.obj a.left) :=
  (X.map a.hom) ⁻¹' (E \ F)

/-- Helper for Lemma 5.24.3: every over-stage pullback of `E \ F` is constructibly closed. -/
private theorem over_stage_difference_closed
    (hX : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (X.map a))
    (hE : IsClosed[constructibleTopology (X.obj i)] E)
    (hF : IsOpen[constructibleTopology (X.obj i)] F)
    (a : Over i) :
    IsClosed[constructibleTopology (X.obj a.left)] (overStageDifference (X := X) i E F a) := by
  -- The source proof works with the single constructibly closed set `E \ F`.
  have hDiffClosed : IsClosed[constructibleTopology (X.obj i)] (E \ F) := by
    letI : TopologicalSpace (X.obj i) := constructibleTopology (X.obj i)
    simpa [Set.diff_eq, inter_comm] using hE.inter hF.isClosed_compl
  -- Spectral maps are continuous for constructible topologies, so closedness pulls back.
  exact @IsClosed.preimage (X.obj a.left) (X.obj i)
    (constructibleTopology (X.obj a.left)) (constructibleTopology (X.obj i))
    (X.map a.hom) (hX a.hom).continuous_constructibleTopology _ hDiffClosed

/-- Helper for Lemma 5.24.3: the over-stage differences are stable under morphisms in `Over i`. -/
private theorem over_stage_difference_mapsTo {a b : Over i} (u : a ⟶ b) :
    Set.MapsTo (X.map u.left) (overStageDifference (X := X) i E F a)
      (overStageDifference (X := X) i E F b) := by
  intro x hx
  -- Compatibility in the over-category identifies the two ways to map `x` into stage `i`.
  change (X.map b.hom) ((X.map u.left) x) ∈ E \ F
  have hmap : X.map (u.left ≫ b.hom) = X.map a.hom := by
    simpa using congrArg (fun f ↦ X.map f) (Over.w u)
  have hcomp : (X.map b.hom) ((X.map u.left) x) = (X.map a.hom) x := by
    simpa [Functor.map_comp] using congrArg (fun f ↦ f x) hmap
  rw [hcomp]
  exact hx

/-- Helper for Lemma 5.24.3: inclusion of two inverse images is equivalent to emptiness of the
inverse image of the difference. -/
private theorem preimage_subset_iff_preimage_difference_empty
    {α β : Type*} (f : α → β) (E F : Set β) :
    f ⁻¹' E ⊆ f ⁻¹' F ↔ f ⁻¹' (E \ F) = ∅ := by
  constructor
  · intro h
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    exact hx.2 (h hx.1)
  · intro h x hxE
    by_contra hxF
    have hxDiff : x ∈ f ⁻¹' (E \ F) := ⟨hxE, hxF⟩
    have hxEmpty : x ∈ (∅ : Set α) := by
      simpa [h] using hxDiff
    simpa using hxEmpty

/-- Helper for Lemma 5.24.3: the pullback of `E \ F` to the inverse limit is nonempty exactly
when all pullbacks over objects of `Over i` are nonempty. -/
private theorem limit_preimage_difference_nonempty_iff_forall_over_stage_nonempty
    (hX : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (X.map a))
    (hE : IsClosed[constructibleTopology (X.obj i)] E)
    (hF : IsOpen[constructibleTopology (X.obj i)] F) :
    ((limit.π X i) ⁻¹' (E \ F)).Nonempty ↔
      ∀ a : Over i, ((X.map a.hom) ⁻¹' (E \ F)).Nonempty := by
  let D₀ : Over i ⥤ TopCat.{max u v} := overDiagram (X := X) i
  let Z : ∀ a : Over i, Set (D₀.obj a) := fun a ↦ (X.map a.hom) ⁻¹' (E \ F)
  have hZ_maps :
      ∀ ⦃a b : Over i⦄ (u : a ⟶ b), Set.MapsTo (D₀.map u) (Z a) (Z b) := by
    intro a b u
    change Set.MapsTo (X.map u.left) ((X.map a.hom) ⁻¹' (E \ F)) ((X.map b.hom) ⁻¹' (E \ F))
    exact over_stage_difference_mapsTo (X := X) i E F u
  have hZ_closed :
      ∀ a : Over i, IsClosed[constructibleTopology (D₀.obj a)] (Z a) := by
    intro a
    change IsClosed[constructibleTopology (X.obj a.left)] ((X.map a.hom) ⁻¹' (E \ F))
    exact over_stage_difference_closed (X := X) i E F hX hE hF a
  let D := D₀.stableSubsetDiagram Z hZ_maps
  constructor
  · rintro ⟨x, hx⟩ a
    refine ⟨(limit.π X a.left) x, ?_⟩
    -- A limit point lying over `E \ F` at stage `i` lies over the same difference at every
    -- object mapping to `i`.
    change X.map a.hom ((limit.π X a.left) x) ∈ E \ F
    have hπ :
        X.map a.hom ((limit.π X a.left) x) = (limit.π X i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w X a.hom)) x
    exact hπ.symm ▸ hx
  · intro hNonempty
    -- Lemma 5.24.2 gives a point of the stable inverse limit over `Over i`.
    let _ : ∀ a : Over i, SpectralSpace ↥(D₀.obj a) := by
      intro a
      change SpectralSpace ↥(X.obj a.left)
      infer_instance
    obtain ⟨x⟩ :=
      nonempty_limit_of_constructibleClosed_stableSubsetDiagram
        (F := D₀) (Z := Z) (hZ_maps := hZ_maps)
        (hF := fun a b u ↦ by simpa using hX u.left)
        hNonempty hZ_closed
    let eStable :
        limit D ≅ (TopCat.limitCone D).pt :=
      IsLimit.conePointUniqueUpToIso (limit.isLimit D) (TopCat.limitConeIsLimit D)
    let x' : (TopCat.limitCone D).pt := eStable.hom x
    let y : (TopCat.limitCone D₀).pt := by
      -- A point of the stable-subset limit is already a compatible family; we only forget
      -- membership in the chosen subsets.
      refine ⟨fun a ↦ (x'.1 a).1, ?_⟩
      intro a b u
      -- The compatibility relation is unchanged after forgetting the subtype proof.
      change D₀.map u ((x'.1 a).1) = (x'.1 b).1
      simpa [D, D₀, CategoryTheory.Functor.stableSubsetDiagram] using
        congrArg Subtype.val (x'.2 u)
    let c : Cone X :=
      (Functor.Initial.extendCone (F := Over.forget i) (G := X)).obj (TopCat.limitCone D₀)
    let hc : IsLimit c :=
      (Functor.Initial.isLimitExtendConeEquiv (F := Over.forget i) (G := X)
        (TopCat.limitCone D₀)).symm
          (TopCat.limitConeIsLimit D₀)
    let z : ↥(limit X) := (limit.isoLimitCone ⟨c, hc⟩).inv y
    refine ⟨z, ?_⟩
    -- Evaluate the extended cone at the identity object of `Over i` to recover a point of `E \ F`.
    have hz_proj :
        (limit.π X i) z = c.π.app i y := by
      change (((limit.isoLimitCone ⟨c, hc⟩).inv ≫ limit.π X i) y) = c.π.app i y
      exact DFunLike.congr_fun
        (congrArg ConcreteCategory.hom (limit.isoLimitCone_inv_π ⟨c, hc⟩ i)) y
    have hy_proj :
        c.π.app i y =
          (TopCat.limitCone D₀).π.app (Over.mk (𝟙 i)) y := by
      simpa using
        congrArg
          (fun g : c.pt ⟶ X.obj i ↦ g y)
          (Functor.Initial.extendCone_obj_π_app'
            (F := Over.forget i) (G := X)
            (c := TopCat.limitCone D₀)
            (X := Over.mk (𝟙 i)) (Y := i) (f := 𝟙 i))
    have hy_mem :
        (TopCat.limitCone D₀).π.app (Over.mk (𝟙 i)) y ∈ E \ F := by
      -- At the identity object, the stable-family coordinate is exactly a point of `E \ F`.
      change ((x'.1 (Over.mk (𝟙 i))).1 : X.obj i) ∈ E \ F
      simpa [D, Z, overStageDifference, Functor.map_id] using (x'.1 (Over.mk (𝟙 i))).2
    change (limit.π X i) z ∈ E \ F
    rw [hz_proj, hy_proj]
    exact hy_mem

-- Proof sketch: apply Lemma 5.24.2 to the cofiltered inverse system over `Over i` whose stage at
-- `a : j ⟶ i` is `f_a ⁻¹' E \ f_a ⁻¹' F`. Spectral maps are continuous for constructible
-- topologies, so these stagewise differences are constructible-topology closed, and emptiness of
-- the inverse limit is equivalent to eventual stagewise emptiness.
/-- Lemma 5.24.3: for a cofiltered inverse system of spectral spaces with spectral transition maps,
the inverse-image inclusion `p_i ⁻¹' E ⊆ p_i ⁻¹' F` for a constructibly closed subset `E` and a
constructibly open subset `F` of `X_i` holds if and only if the corresponding inclusion already
holds after pullback along some morphism `a : j ⟶ i`. -/
theorem limit_projection_preimage_subset_iff_exists_stage_preimage_subset :
    (hX : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (X.map a)) →
    (hE : IsClosed[constructibleTopology (X.obj i)] E) →
    (hF : IsOpen[constructibleTopology (X.obj i)] F) →
    (limit.π X i) ⁻¹' E ⊆ (limit.π X i) ⁻¹' F ↔
      ∃ (j : I) (a : j ⟶ i), (X.map a) ⁻¹' E ⊆ (X.map a) ⁻¹' F := by
  classical
  intro hX hE hF
  -- The source proof reduces everything to the single constructibly closed family `E \ F`.
  have hNonemptyIff :
      ((limit.π X i) ⁻¹' (E \ F)).Nonempty ↔
        ∀ a : Over i, (overStageDifference (X := X) i E F a).Nonempty :=
    limit_preimage_difference_nonempty_iff_forall_over_stage_nonempty
      (X := X) (hX := hX) i E F hE hF
  constructor
  · intro hLimitSubset
    have hLimitEmpty :
        (limit.π X i) ⁻¹' (E \ F) = ∅ :=
      (preimage_subset_iff_preimage_difference_empty (limit.π X i) E F).mp hLimitSubset
    by_contra hNoStage
    have hNoStage' :
        ∀ (j : I) (a : j ⟶ i), ¬ (X.map a) ⁻¹' E ⊆ (X.map a) ⁻¹' F := by
      intro j a haSubset
      exact hNoStage ⟨j, a, haSubset⟩
    have hAllNonempty :
        ∀ a : Over i, (overStageDifference (X := X) i E F a).Nonempty := by
      intro a
      by_contra ha
      exact hNoStage' a.left a.hom
        ((preimage_subset_iff_preimage_difference_empty (X.map a.hom) E F).mpr
          (Set.not_nonempty_iff_eq_empty.mp ha))
    exact
      (Set.not_nonempty_iff_eq_empty.mpr hLimitEmpty)
        (hNonemptyIff.mpr hAllNonempty)
  · rintro ⟨j, a, haSubset⟩
    have haEmpty :
        overStageDifference (X := X) i E F (Over.mk a) = ∅ :=
      (preimage_subset_iff_preimage_difference_empty (X.map a) E F).mp haSubset
    have hLimitEmpty :
        (limit.π X i) ⁻¹' (E \ F) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hLimitNonempty
      have hStageNonempty := (hNonemptyIff.mp hLimitNonempty) (Over.mk a)
      exact (Set.not_nonempty_iff_eq_empty.mpr haEmpty) hStageNonempty
    exact
      (preimage_subset_iff_preimage_difference_empty (limit.π X i) E F).mpr
        hLimitEmpty

end
