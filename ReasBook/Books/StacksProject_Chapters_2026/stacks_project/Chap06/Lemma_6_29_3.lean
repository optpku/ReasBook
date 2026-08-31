module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap05.Lemma_5_14_5
public import stacks_project.Chap05.Lemma_5_23_2
public import stacks_project.Chap05.Lemma_5_23_3
public import stacks_project.Chap05.Lemma_5_24_1
public import stacks_project.Chap05.Lemma_5_24_3
public import stacks_project.Chap05.Lemma_5_24_5
public import stacks_project.Chap05.Lemma_5_24_6
public import stacks_project.Chap06.Definition_6_30_2
public import stacks_project.Chap06.Lemma_6_21_5
public import stacks_project.Chap06.Lemma_6_21_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite Set TopologicalSpace Topology ConcreteCategory
open TopCat.Sheaf
open scoped TopCat

universe u

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

variable {I : Type u} [Category.{u, u} I]
variable (F : I ⥤ TopCat.{u})

/- Domain-style sampling for Lemma 6.29.3:
- primary domain: pullback of sheaves of types along continuous maps in an inverse system of
  spectral spaces, with the source-facing comparison map expressed on compact opens;
- sampled owner declarations:
  `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `TopCat.Sheaf.pullbackComp`,
  `PrespectralSpace.isBasis_opens`,
  `CategoryTheory.colimitSiteStagePullbackSectionsComparison`;
- owner abstraction: the comparison on stagewise pullback sections is canonically owned by the
  site-level declaration `CategoryTheory.colimitSiteStagePullbackSectionsComparison`, applied to
  the compact-open basis sites of the spectral stages; the topological map in this file is the
  source-facing specialization of that owner;
- primitive data: a cofiltered diagram `F`, a stage `i`, a sheaf `𝒢` on `F.obj i`, and a
  quasi-compact open `U ⊆ F.obj i`;
- derived API: the explicit `(Over i)ᵒᵖ` diagram of pullback section sets and the colimit
  comparison map. These are bridge-level presentations and should not remain the main public
  owner once the site-level comparison is available.

Source/core/bridge triage:
- `source-facing`: the comparison
  `colim_a f_a⁻¹ 𝒢 (f_a⁻¹(U)) ⟶ p_i⁻¹ 𝒢 (p_i⁻¹(U))`;
- `core/canonical`: the Chapter 7 site-level comparison owner on the compact-open basis site of
  the spectral stages, together with the basis restriction equivalence for sheaves;
- `bridge/view`: the explicit `(Over i)ᵒᵖ` diagram of stagewise pullback section types below, kept
  private because it is only an implementation view of the source-facing comparison. -/

private abbrev compactOpenBasis (X : TopCat.{u}) : Set (Opens X) :=
  { U : Opens X | IsCompact (U : Set X) }

private theorem compactOpenBasis_isBasis (X : TopCat.{u}) [SpectralSpace X] :
    Opens.IsBasis (compactOpenBasis X) :=
  PrespectralSpace.isBasis_opens X

/-- Helper for Lemma 6.29.3: every point of an open subset of a spectral space lies in a compact
open neighborhood still contained in that open. This is the stage-side shrinking step used when a
local representative is first obtained on an arbitrary stage open and then tightened to a compact
open before descent. -/
private theorem exists_compactOpen_subset_of_mem_open
    {X : TopCat.{u}} [SpectralSpace X] {U : Opens X} {x : X} (hx : x ∈ U) :
    ∃ V : CompactOpens X, x ∈ (V : Set X) ∧ (V : Set X) ⊆ U := by
  let B : Set (Set X) := {V : Set X | IsOpen V ∧ IsCompact V}
  have hBasis : IsTopologicalBasis B := PrespectralSpace.isTopologicalBasis (X := X)
  -- Choose one compact-open basis neighborhood of `x` inside the ambient open `U`.
  obtain ⟨V, hV, hxV, hVU⟩ := hBasis.exists_subset_of_mem_open hx U.isOpen
  refine ⟨⟨⟨V, hV.2⟩, hV.1⟩, hxV, hVU⟩

/-- Helper for Lemma 6.29.3: finitely many arrows into a fixed object of a cofiltered category
admit one common refinement stage. This is the synchronization step later used to move finitely
many local stage choices and finitely many overlap equalities to a single stage. -/
private theorem common_refinement_of_finite_arrows_to
    [IsCofiltered I] {i : I} {α : Type*} (s : Finset α) (j : α → I)
    (f : ∀ a : α, ∀ _ha : a ∈ s, j a ⟶ i) :
    ∃ k : I, ∃ g : k ⟶ i, ∀ a (ha : a ∈ s), ∃ h : k ⟶ j a, h ≫ f a ha = g := by
  classical
  revert f
  refine Finset.induction_on s ?_ ?_
  · intro f
    refine ⟨i, 𝟙 i, ?_⟩
    intro a ha
    exact False.elim (Finset.notMem_empty a ha)
  · intro a s has hrec f
    have hrec' := hrec (fun b hb ↦ f b (Finset.mem_insert_of_mem hb))
    rcases hrec' with ⟨k, g, hg⟩
    let m := IsCofiltered.min (j a) k
    let fa : m ⟶ i := IsCofiltered.minToLeft (j a) k ≫ f a (Finset.mem_insert_self a s)
    let fg : m ⟶ i := IsCofiltered.minToRight (j a) k ≫ g
    refine ⟨IsCofiltered.eq fa fg, IsCofiltered.eqHom fa fg ≫ fa, ?_⟩
    intro b hb
    by_cases hba : b = a
    · subst b
      refine ⟨IsCofiltered.eqHom fa fg ≫ IsCofiltered.minToLeft (j a) k, ?_⟩
      simp [fa, Category.assoc]
    · have hb' : b ∈ s := (Finset.mem_insert.mp hb).resolve_left hba
      rcases hg b hb' with ⟨hbk, hhbk⟩
      refine ⟨IsCofiltered.eqHom fa fg ≫ IsCofiltered.minToRight (j a) k ≫ hbk, ?_⟩
      calc
        (IsCofiltered.eqHom fa fg ≫ IsCofiltered.minToRight (j a) k ≫ hbk) ≫
            f b (Finset.mem_insert_of_mem hb')
            = IsCofiltered.eqHom fa fg ≫
                (IsCofiltered.minToRight (j a) k ≫ hbk ≫
                  f b (Finset.mem_insert_of_mem hb')) := by
                    simp [Category.assoc]
        _ = IsCofiltered.eqHom fa fg ≫ (IsCofiltered.minToRight (j a) k ≫ g) := by
              simp [hhbk]
        _ = IsCofiltered.eqHom fa fg ≫ fa := by
              simpa [fg, Category.assoc] using (IsCofiltered.eq_condition fa fg).symm

/-- Helper for Lemma 6.29.3: a finite family indexed by a `Fintype` can be synchronized to one
common refinement stage without first materializing the index set as an auxiliary `Finset`. This
is the exact bookkeeping form used later for the finitely many pairwise overlap refinements. -/
private theorem common_refinement_of_fintype_arrows_to
    [IsCofiltered I] {i : I} {α : Type*} [Fintype α] (j : α → I) (f : ∀ a : α, j a ⟶ i) :
    ∃ k : I, ∃ g : k ⟶ i, ∀ a : α, ∃ h : k ⟶ j a, h ≫ f a = g := by
  classical
  obtain ⟨k, g, hg⟩ :=
    common_refinement_of_finite_arrows_to
      (I := I) (i := i) (s := Finset.univ) (j := j) (f := fun a _ha ↦ f a)
  refine ⟨k, g, ?_⟩
  intro a
  simpa using hg a (by simp)

/-- Helper for Lemma 6.29.3: the finitely many pairwise overlap-refinement arrows
`c_{a,a'} : l_{a,a'} ⟶ k` can be synchronized to one common dominating stage over `k`. This is
the pure cofiltered-bookkeeping step needed before the refined overlap equalities are upgraded to a
single compatible family. -/
private theorem common_refinement_of_pairwise_arrows_to
    [IsCofiltered I] {k : I} {α : Type*} [Fintype α]
    (lqq : α → α → I) (cqq : ∀ a a' : α, lqq a a' ⟶ k) :
    ∃ l : I, ∃ c : l ⟶ k,
      ∀ a a' : α, ∃ d : l ⟶ lqq a a', d ≫ cqq a a' = c := by
  classical
  let j : α × α → I := fun p ↦ lqq p.1 p.2
  let f : ∀ p : α × α, j p ⟶ k := fun p ↦ cqq p.1 p.2
  obtain ⟨l, c, hc⟩ := common_refinement_of_fintype_arrows_to (I := I) (i := k) j f
  refine ⟨l, c, ?_⟩
  intro a a'
  simpa [j, f] using hc (a, a')

/-- Helper for Lemma 6.29.3: a spectral transition map pulls compact opens back to compact opens,
so it induces the corresponding functor on compact-open basis sites. -/
private noncomputable def compact_open_basis_stageFunctor
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) :
    BasisOpen (compactOpenBasis (F.obj i)) ⥤ BasisOpen (compactOpenBasis (F.obj j)) where
  obj U :=
    ⟨(Opens.map (F.map a)).obj U.obj,
      (hF a).isCompact_preimage_of_isOpen U.obj.isOpen U.property⟩
  -- The basis functor is just inverse image on opens, restricted to compact opens.
  map f := ObjectProperty.homMk ((Opens.map (F.map a)).map f.hom)
  map_id U := by
    rfl
  map_comp f g := by
    rfl

/-- Helper for Lemma 6.29.3: objectwise, the compact-open basis transition functor sends a compact
open `U` to the ordinary inverse image `(F.map a)⁻¹(U)`. This keeps the later owner-side site
packaging at the explicit open-set level. -/
private theorem compact_open_basis_stageFunctor_obj
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) (U : BasisOpen (compactOpenBasis (F.obj i))) :
    ((compact_open_basis_stageFunctor (F := F) hF a).obj U).obj =
      (Opens.map (F.map a)).obj U.obj := by
  -- The basis transition functor is defined by this explicit inverse-image formula.
  rfl

/-- Helper for Lemma 6.29.3: the inverse image of a compact open along a spectral transition map
is again a compact open on the source stage. This packages the `BasisOpen`-level pullback back
into the `CompactOpens` API used throughout the proof. -/
private def stage_pullback_compact_open
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) (U : CompactOpens (F.obj i)) : CompactOpens (F.obj j) :=
  ⟨⟨(Opens.map (F.map a)).obj U.toOpens,
      (hF a).isCompact_preimage_of_isOpen U.isOpen U.isCompact⟩,
    ((Opens.map (F.map a)).obj U.toOpens).isOpen⟩

/-- Helper for Lemma 6.29.3: the compact-open basis inclusion is continuous for the induced basis
topology, so sheaves on the stage can be restricted to the compact-open basis site. -/
private instance compact_open_basis_inclusion_isContinuous
    [∀ i : I, SpectralSpace (F.obj i)] (i : I) :
    Functor.IsContinuous
      (basisOpenInclusion (compactOpenBasis (F.obj i)))
      (basisGrothendieckTopology (compactOpenBasis (F.obj i))
        (compactOpenBasis_isBasis (F.obj i)))
      (Opens.grothendieckTopology (F.obj i)) := by
  letI :
      (basisOpenInclusion (compactOpenBasis (F.obj i))).IsCoverDense
        (Opens.grothendieckTopology (F.obj i)) :=
    basisOpenInclusion_isCoverDense (compactOpenBasis_isBasis (F.obj i))
  exact
    Functor.IsCoverDense.isContinuous
      (basisGrothendieckTopology (compactOpenBasis (F.obj i))
        (compactOpenBasis_isBasis (F.obj i)))
      (Opens.grothendieckTopology (F.obj i))
      (basisOpenInclusion (compactOpenBasis (F.obj i)))
      (Functor.inducedTopology_coverPreserving
        (basisOpenInclusion (compactOpenBasis (F.obj i)))
        (Opens.grothendieckTopology (F.obj i)))

/-- Helper for Lemma 6.29.3: forgetting from the compact-open basis site to all opens commutes
with the basis transition functor and the ordinary inverse-image functor on opens. -/
private theorem compact_open_basis_stageFunctor_comp_inclusion
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) :
    compact_open_basis_stageFunctor (F := F) hF a ⋙
        basisOpenInclusion (compactOpenBasis (F.obj j)) =
      basisOpenInclusion (compactOpenBasis (F.obj i)) ⋙ Opens.map (F.map a) := by
  -- Both functors are the same inverse-image operation, expressed before and after forgetting the
  -- compactness predicate on basis opens.
  rfl

/-- Helper for Lemma 6.29.3: the compact-open basis transition functor preserves covering sieves
because, after forgetting to ordinary opens, it is the usual inverse-image functor on opens. -/
private theorem compact_open_basis_stageFunctor_coverPreserving
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) :
    CoverPreserving
      (basisGrothendieckTopology (compactOpenBasis (F.obj i))
        (compactOpenBasis_isBasis (F.obj i)))
      (basisGrothendieckTopology (compactOpenBasis (F.obj j))
        (compactOpenBasis_isBasis (F.obj j)))
      (compact_open_basis_stageFunctor (F := F) hF a) := by
  let Bi := basisOpenInclusion (compactOpenBasis (F.obj i))
  let Bj := basisOpenInclusion (compactOpenBasis (F.obj j))
  letI : Bi.IsCoverDense (Opens.grothendieckTopology (F.obj i)) :=
    basisOpenInclusion_isCoverDense (compactOpenBasis_isBasis (F.obj i))
  letI : Bj.IsCoverDense (Opens.grothendieckTopology (F.obj j)) :=
    basisOpenInclusion_isCoverDense (compactOpenBasis_isBasis (F.obj j))
  refine ⟨?_⟩
  intro U S hS
  have hPush :
      Sieve.functorPushforward Bi S ∈
        Opens.grothendieckTopology (F.obj i) (Bi.obj U) := by
    -- Move the induced-topology cover back to the ambient opens site.
    exact
      (Functor.mem_inducedTopology_sieves_iff Bi
        (Opens.grothendieckTopology (F.obj i)) S).1
        (by simpa [Bi, basisGrothendieckTopology] using hS)
  have hPushImage :
      Sieve.functorPushforward (Opens.map (F.map a))
          (Sieve.functorPushforward Bi S) ∈
        Opens.grothendieckTopology (F.obj j)
          ((Opens.map (F.map a)).obj (Bi.obj U)) := by
    -- Ordinary inverse image on opens already preserves covering sieves.
    exact (coverPreserving_opens_map (F.map a)).cover_preserve hPush
  have hPushImage' :
      Sieve.functorPushforward (Bi ⋙ Opens.map (F.map a)) S ∈
        Opens.grothendieckTopology (F.obj j) (((Bi ⋙ Opens.map (F.map a)).obj U)) := by
    simpa [Sieve.functorPushforward_comp] using hPushImage
  have hTarget :
      Sieve.functorPushforward Bj
          (Sieve.functorPushforward (compact_open_basis_stageFunctor (F := F) hF a) S) ∈
        Opens.grothendieckTopology (F.obj j)
          (Bj.obj ((compact_open_basis_stageFunctor (F := F) hF a).obj U)) := by
    -- Rewrite the composite-with-inclusion description back to the basis transition functor.
    have hComp :
        Sieve.functorPushforward
            ((compact_open_basis_stageFunctor (F := F) hF a) ⋙ Bj) S ∈
          Opens.grothendieckTopology (F.obj j)
            ((((compact_open_basis_stageFunctor (F := F) hF a) ⋙ Bj).obj U)) :=
      (compact_open_basis_stageFunctor_comp_inclusion (F := F) hF a) ▸ hPushImage'
    simpa [Sieve.functorPushforward_comp] using hComp
  -- Transport the ambient-opens cover back through the basis inclusion on the target stage.
  exact
    (Functor.mem_inducedTopology_sieves_iff Bj
      (Opens.grothendieckTopology (F.obj j))
      (Sieve.functorPushforward (compact_open_basis_stageFunctor (F := F) hF a) S)).2
      (by simpa [basisGrothendieckTopology] using hTarget)

/-- The iterated-pullback section space computed through `f` and then `g` is the section space of
the pullback along `f ≫ g`. -/
public theorem inverseImageSectionValue_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (𝒢 : Z.Sheaf (Type u)) (U : Opens Z) :
    ((((f ≫ g)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map f).obj ((Opens.map g).obj U))) =
    ((((f ≫ g)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (f ≫ g)).obj U)) := by
  rfl

/-- The canonical map on sections induced by pulling back first along `g` and then along `f`. -/
noncomputable def iteratedPullbackSectionsMap {X Y Z : TopCat.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (𝒢 : Z.Sheaf (Type u)) (U : Opens Z) :
    ((((g⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map g).obj U))) ⟶
      ((((f ≫ g)⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map (f ≫ g)).obj U)) :=
  let η := (((pullbackPushforwardAdjunction (Type u) f).unit.app ((g⁻¹).obj 𝒢)).1.app
    (op ((Opens.map g).obj U)))
  let e := (pullbackComp f g).hom.app 𝒢
  fun s ↦ cast (inverseImageSectionValue_comp f g 𝒢 U)
    ((e.1.app (op ((Opens.map f).obj ((Opens.map g).obj U)))) (η s))

/-- A morphism in `Over i` identifies the corresponding iterated pullback section space with the
direct pullback section space. -/
theorem overPullbackSections_eq {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) {A B : Over i} (φ : A ⟶ B) :
    ((((F.map φ.left ≫ F.map B.hom)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (F.map φ.left ≫ F.map B.hom)).obj U)) =
    ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (F.map A.hom)).obj U)) := by
  simpa [Functor.map_comp] using
    congrArg
      (fun f : A.left ⟶ i ↦
        ((((F.map f)⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map (F.map f)).obj U)))
      (Over.w φ)

/-- Helper for Lemma 6.29.3: `TopCat.Sheaf.pullbackComp` is the left-adjoint comparison isomorphism
for the definitional equality of pushforward functors. -/
private theorem sheafPullbackComp_def {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullbackComp f g =
      Adjunction.leftAdjointCompIso
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g))
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g =
            TopCat.Sheaf.pushforward (Type u) (f ≫ g) from rfl)) := by
  rfl

/-- Helper for Lemma 6.29.3: the comparison for `pullbackComp (𝟙, g)` is the standard
left-unital adjunction comparison. -/
private theorem sheafPullbackComp_comp_id {X Y : TopCat.{u}} (g : X ⟶ Y) :
    TopCat.Sheaf.pullbackComp (𝟙 X) g =
      Functor.isoWhiskerLeft (TopCat.Sheaf.pullback (Type u) g)
          ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 X)).leftAdjointIdIso
            (eqToIso rfl)) ≪≫
        Functor.rightUnitor (TopCat.Sheaf.pullback (Type u) g) := by
  -- Compare `pullbackComp (𝟙, g)` with the canonical left-unital comparison for adjunctions.
  simpa [sheafPullbackComp_def] using
    (Adjunction.leftAdjointCompIso_comp_id
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 X))
      (eqToIso rfl)
      (eqToIso rfl)
      (by
        ext ℱ
        rfl))

/-- Helper for Lemma 6.29.3: the comparison for `pullbackComp (f, 𝟙)` is the standard
right-unital adjunction comparison. This is the identity-over-stage normalization needed when the
last remaining overlap argument is phrased on `Over.mk (𝟙 k)`. -/
private theorem sheafPullbackComp_id_comp {X Y : TopCat.{u}} (f : X ⟶ Y) :
    TopCat.Sheaf.pullbackComp f (𝟙 Y) =
      Functor.isoWhiskerRight
          ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 Y)).leftAdjointIdIso
            (eqToIso rfl))
          (TopCat.Sheaf.pullback (Type u) f) ≪≫
        Functor.leftUnitor (TopCat.Sheaf.pullback (Type u) f) := by
  -- Compare `pullbackComp (f, 𝟙)` with the canonical right-unital comparison for adjunctions.
  simpa [sheafPullbackComp_def] using
    (Adjunction.leftAdjointCompIso_id_comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 Y))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
      (eqToIso rfl)
      (eqToIso rfl)
      (by
        ext ℱ
        rfl))

/-- Helper for Lemma 6.29.3: for pullback along the identity map, the adjunction unit followed by
the component of `leftAdjointIdIso` is the identity. -/
private theorem sheafPullbackId_unit_hom_app {X : TopCat.{u}} (ℱ : X.Sheaf (Type u)) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 X)).unit.app ℱ) ≫
      (TopCat.Sheaf.pushforward (Type u) (𝟙 X)).map
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 X)).leftAdjointIdIso
          (eqToIso rfl)).hom.app ℱ) =
      𝟙 _ := by
  -- This is the mate formula for `leftAdjointIdIso`, specialized to the identity adjunction.
  have h :=
    CategoryTheory.unit_conjugateEquiv
      CategoryTheory.Adjunction.id
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 X))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 X)).leftAdjointIdIso
        (eqToIso rfl)).hom)
      ℱ
  simpa using h.symm

/-- Helper for Lemma 6.29.3: the section-level transport in
`inverseImageSectionValue_comp (𝟙, g)` is definitional. -/
private theorem inverseImageSectionValue_comp_id {X Y : TopCat.{u}} (g : X ⟶ Y)
    (𝒢 : Y.Sheaf (Type u)) (U : Opens Y) :
    inverseImageSectionValue_comp (𝟙 X) g 𝒢 U = rfl := by
  exact Subsingleton.elim _ _

/-- Helper for Lemma 6.29.3: pulling back sections first along `g` and then along the identity
does nothing. -/
private theorem iterated_pullback_sections_map_comp_id {X Y : TopCat.{u}} (g : X ⟶ Y)
    (𝒢 : Y.Sheaf (Type u)) (U : Opens Y) :
    iteratedPullbackSectionsMap (𝟙 X) g 𝒢 U = id := by
  ext s
  -- Remove the definitional casts so the identity-adjunction comparison becomes visible.
  rw [iteratedPullbackSectionsMap, inverseImageSectionValue_comp_id]
  dsimp
  rw [sheafPullbackComp_comp_id]
  -- After the comparison rewrite, the section map is exactly the evaluated identity adjunction.
  simpa using
    congrArg
      (fun k ↦ (k.1.app (op ((Opens.map g).obj U))) s)
      (sheafPullbackId_unit_hom_app ((g⁻¹).obj 𝒢))

/-- Helper for Lemma 6.29.3: the canonical pullback-composition isomorphisms satisfy the
associativity coherence coming from `Adjunction.leftAdjointCompIso_assoc`. -/
private theorem sheafPushforward_assoc {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type u) f)
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type u) g ⋙ TopCat.Sheaf.pushforward (Type u) h =
            TopCat.Sheaf.pushforward (Type u) (g ≫ h) from rfl)) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type u) f ⋙
            TopCat.Sheaf.pushforward (Type u) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl) =
    (Functor.associator
      (TopCat.Sheaf.pushforward (Type u) f)
      (TopCat.Sheaf.pushforward (Type u) g)
      (TopCat.Sheaf.pushforward (Type u) h)).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g =
            TopCat.Sheaf.pushforward (Type u) (f ≫ g) from rfl))
        (TopCat.Sheaf.pushforward (Type u) h) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type u) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type u) h =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl) := by
  -- Evaluate the functor-level coherence componentwise; both sides are definitionally the same.
  ext ℱ
  rfl

/-- Helper for Lemma 6.29.3: the canonical pullback-composition isomorphisms satisfy the
associativity coherence coming from `Adjunction.leftAdjointCompIso_assoc`. -/
private theorem sheafPullbackComp_assoc {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Functor.isoWhiskerLeft _ (TopCat.Sheaf.pullbackComp (A := Type u) f g) ≪≫
      TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (TopCat.Sheaf.pullbackComp (A := Type u) g h) _ ≪≫
        TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h) := by
  -- This is the owner-level associativity coherence for left adjoints to the same composite
  -- pushforward functor.
  simpa [sheafPullbackComp_def] using
    (Adjunction.leftAdjointCompIso_assoc
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) h)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (g ≫ h))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g ≫ h))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) g ⋙ TopCat.Sheaf.pushforward (Type u) h =
          TopCat.Sheaf.pushforward (Type u) (g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type u) h =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type u) f ⋙
            TopCat.Sheaf.pushforward (Type u) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g ≫ h) from rfl))
      (sheafPushforward_assoc f g h))

/-- Helper for Lemma 6.29.3: the hom components of the pullback-composition comparisons satisfy
the standard pseudofunctor associativity identity. -/
private theorem sheaf_pullback_pseudofunctor_associativity {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).inv ≫
        (Functor.isoWhiskerRight
          (TopCat.Sheaf.pullbackComp (A := Type u) g h)
          (TopCat.Sheaf.pullback (Type u) f)).inv ≫
        (Functor.associator _ _ _).hom ≫
        (Functor.isoWhiskerLeft
          (TopCat.Sheaf.pullback (Type u) h)
          (TopCat.Sheaf.pullbackComp (A := Type u) f g)).hom ≫
        (TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom =
      eqToHom (by simp) := by
  -- Route correction: package the isomorphism-level associativity once as a hom equality so the
  -- later section-level proof only has to evaluate this normalized comparison.
  let e₁ := TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight
    (TopCat.Sheaf.pullbackComp (A := Type u) g h)
    (TopCat.Sheaf.pullback (Type u) f)
  let e₃ := Functor.isoWhiskerLeft
    (TopCat.Sheaf.pullback (Type u) h)
    (TopCat.Sheaf.pullbackComp (A := Type u) f g)
  let e₄ := TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have hcomp : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom := by
    exact congrArg Iso.hom (sheafPullbackComp_assoc f g h)
  rw [hcomp]
  ext X
  simpa using Iso.inv_hom_id_app e₁ X

/-- Helper for Lemma 6.29.3: the unit for pullback along `f` is natural with respect to the
comparison map `pullbackComp g h` between the two ways of pulling back `𝒢` along `g` and `h`. -/
private theorem pullback_unit_naturality {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (𝒢 : Z.Sheaf (Type u)) :
    ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app 𝒢) ≫
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
          ((TopCat.Sheaf.pullback (Type u) (g ≫ h)).obj 𝒢) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
          ((TopCat.Sheaf.pullback (Type u) h ⋙ TopCat.Sheaf.pullback (Type u) g).obj 𝒢) ≫
        (TopCat.Sheaf.pushforward (Type u) f).map
          ((TopCat.Sheaf.pullback (Type u) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app 𝒢)) := by
  -- This is the sheaf-level unit naturality square, rewritten in the direction needed later.
  simpa using
    (Adjunction.unit_naturality
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
      ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app 𝒢)).symm

/-- Helper for Lemma 6.29.3: evaluating `pullback_unit_naturality` on the open
`g⁻¹(h⁻¹(U))` turns the sheaf-level naturality square into the section-level transport identity
needed for the iterated pullback maps. -/
private theorem pullback_unit_naturality_app_transport {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (𝒢 : Z.Sheaf (Type u)) (U : Opens Z)
    (t :
      ((((TopCat.Sheaf.pullback (Type u) h) ⋙
            (TopCat.Sheaf.pullback (Type u) g)).obj 𝒢).presheaf).obj
        (op ((Opens.map g).obj ((Opens.map h).obj U)))) :
    ((((TopCat.Sheaf.pullback (Type u) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app 𝒢)).hom.app
          (op ((Opens.map f).obj ((Opens.map g).obj ((Opens.map h).obj U)))))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
              ((TopCat.Sheaf.pullback (Type u) g).obj
                ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢))).hom.app
            (op ((Opens.map g).obj ((Opens.map h).obj U)))) t)) =
      ((((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app 𝒢) ≫
            (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
              ((TopCat.Sheaf.pullback (Type u) (g ≫ h)).obj 𝒢)).hom.app
          (op ((Opens.map g).obj ((Opens.map h).obj U)))) t := by
  -- Evaluate the sheaf-level naturality identity on the relevant open and section.
  simpa using
    congrArg
      (fun k ↦ k.hom.app (op ((Opens.map g).obj ((Opens.map h).obj U))) t)
      (pullback_unit_naturality f g h 𝒢).symm

/-- Helper for Lemma 6.29.3: the unit for pullback along `f ≫ g`, evaluated on a section over
`h⁻¹(U)`, is the same as first applying the `g`-unit and then the `f`-unit, and only afterwards
transporting through `pullbackComp f g`. -/
private theorem pullback_comp_unit_app_transport {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (𝒢 : Z.Sheaf (Type u)) (U : Opens Z)
    (t : (((TopCat.Sheaf.pullback (Type u) h).obj 𝒢).presheaf).obj
      (op ((Opens.map h).obj U))) :
    iteratedPullbackSectionsMap f g ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)
        ((Opens.map h).obj U)
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app
                ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)).hom.app
              (op ((Opens.map h).obj U))) t) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app
              ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)).hom.app
            (op ((Opens.map h).obj U))) t) := by
  -- Route correction: use the adjunction `homEquiv` for the composite pullback adjunction, so the
  -- unit of `f ≫ g` appears directly without expanding the composite adjunction counit.
  let ℋ := (TopCat.Sheaf.pullback (Type u) h).obj 𝒢
  let adjfg := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)
  let adj :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
  let e : TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g ≅
      TopCat.Sheaf.pushforward (Type u) (f ≫ g) :=
    eqToIso
      (show TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g =
          TopCat.Sheaf.pushforward (Type u) (f ≫ g) from rfl)
  have hconj :
      CategoryTheory.conjugateEquiv adjfg adj
        ((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom) = 𝟙 _ := by
    -- Conjugating the inverse comparison gives the definitional right-adjoint identity, so the
    -- conjugate of the forward comparison is forced to be the identity as well.
    have h_inv :
        CategoryTheory.conjugateEquiv adj adjfg
          ((TopCat.Sheaf.pullbackComp (A := Type u) f g).inv) = e.hom := by
      rw [sheafPullbackComp_def]
      simpa [adjfg, adj, e] using
        (CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g)
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g))
          e)
    have hcomp :=
      CategoryTheory.conjugateEquiv_comp adjfg adj adjfg
        ((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom)
        ((TopCat.Sheaf.pullbackComp (A := Type u) f g).inv)
    simpa [adjfg, adj, e, h_inv] using hcomp
  have hhom :
      adj.homEquiv ℋ ((TopCat.Sheaf.pullback (Type u) (f ≫ g)).obj ℋ)
        ((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app ℋ) =
      adjfg.unit.app ℋ := by
    -- The composite pullback comparison is characterized by the direct pullback unit.
    have hunit :=
      CategoryTheory.unit_conjugateEquiv
        adjfg adj
        ((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom)
        ℋ
    simpa [adjfg, adj, Adjunction.homEquiv_unit, hconj] using hunit.symm
  simpa [ℋ, adj, iteratedPullbackSectionsMap, inverseImageSectionValue_comp, Functor.comp_map,
    Adjunction.homEquiv_unit] using
    congrArg
      (fun k ↦ k.hom.app (op ((Opens.map h).obj U)) t)
      hhom

/-- Helper for Lemma 6.29.3: evaluating the iterated pullback map for `f` and `g` on the
`g`-unit section exposes the normalized nested-unit branch used later in the associativity proof. -/
private theorem iterated_pullback_sections_map_comp_unit_value {W X Y Z : TopCat.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (𝒢 : Z.Sheaf (Type u)) (U : Opens Z)
    (t : (((TopCat.Sheaf.pullback (Type u) h).obj 𝒢).presheaf).obj
      (op ((Opens.map h).obj U))) :
    iteratedPullbackSectionsMap f g ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)
        ((Opens.map h).obj U)
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app
                ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)).hom.app
              (op ((Opens.map h).obj U))) t) =
      cast
        (inverseImageSectionValue_comp f g ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)
          ((Opens.map h).obj U))
        ((((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
                ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)).hom.app
              (op ((Opens.map f).obj ((Opens.map g).obj ((Opens.map h).obj U)))))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
                  ((TopCat.Sheaf.pullback (Type u) g).obj
                    ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢))).hom.app
                (op ((Opens.map g).obj ((Opens.map h).obj U))))
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app
                      ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)).hom.app
                    (op ((Opens.map h).obj U))) t))) := by
  -- Unfold the definition once: this is exactly the nested-unit branch by construction.
  rfl

/-- Helper for Lemma 6.29.3: evaluating `sheafPullbackComp_assoc` on the normalized nested-unit
section yields the composite-form associativity identity before the final unit-naturality rewrite
on the right branch. -/
private theorem iterated_pullback_sections_map_assoc_composite
    {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (𝒢 : Z.Sheaf (Type u)) (U : Opens Z)
    (t : (((TopCat.Sheaf.pullback (Type u) h).obj 𝒢).presheaf).obj
      (op ((Opens.map h).obj U))) :
    let y :=
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
              ((TopCat.Sheaf.pullback (Type u) g).obj
                ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢))).hom.app
            (op ((Opens.map g).obj ((Opens.map h).obj U))))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app
                ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)).hom.app
              (op ((Opens.map h).obj U))) t))
    (((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app
            ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)) ≫
          ((TopCat.Sheaf.pullbackComp (A := Type u) (f ≫ g) h).hom.app 𝒢)).hom.app
        (op ((Opens.map f).obj ((Opens.map g).obj ((Opens.map h).obj U)))) y =
      ((((TopCat.Sheaf.pullback (Type u) f).map
              ((TopCat.Sheaf.pullbackComp (A := Type u) g h).hom.app 𝒢)) ≫
            ((TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app 𝒢)).hom.app
          (op ((Opens.map f).obj ((Opens.map g).obj ((Opens.map h).obj U)))) y) := by
  let y :=
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
            ((TopCat.Sheaf.pullback (Type u) g).obj
              ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢))).hom.app
          (op ((Opens.map g).obj ((Opens.map h).obj U))))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app
              ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)).hom.app
            (op ((Opens.map h).obj U))) t))
  -- This is exactly the isomorphism-level associativity coherence, evaluated on the normalized
  -- nested-unit section.
  have hassoc :=
    congrArg
      (fun k ↦ (k.hom.app 𝒢).1.app
        (op ((Opens.map f).obj ((Opens.map g).obj ((Opens.map h).obj U))))
        y)
      (sheafPullbackComp_assoc f g h)
  simpa [y, Category.assoc] using hassoc

/-- Helper for Lemma 6.29.3: iterated pullback on a single section is associative after
normalizing the canonical pullback-composition comparisons once. -/
private theorem iterated_pullback_sections_map_assoc_pointwise_transport
    {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (𝒢 : Z.Sheaf (Type u)) (U : Opens Z)
    (t : (((TopCat.Sheaf.pullback (Type u) h).obj 𝒢).presheaf).obj
      (op ((Opens.map h).obj U))) :
    iteratedPullbackSectionsMap (f ≫ g) h 𝒢 U t =
      cast (by rfl)
        ((iteratedPullbackSectionsMap f (g ≫ h) 𝒢 U ∘
          iteratedPullbackSectionsMap g h 𝒢 U) t) := by
  -- Normalize both sides to the app-level pullback-composition comparison acting on the relevant
  -- unit section.
  simp [iteratedPullbackSectionsMap, Function.comp]
  rw [← pullback_comp_unit_app_transport (f := f) (g := g) (h := h) (𝒢 := 𝒢) (U := U) (t := t)]
  rw [iterated_pullback_sections_map_comp_unit_value
    (f := f) (g := g) (h := h) (𝒢 := 𝒢) (U := U) (t := t)]
  -- The composite-form associativity identity already matches the left branch of the goal.
  have hcomp := iterated_pullback_sections_map_assoc_composite f g h 𝒢 U t
  -- Rewrite the right branch by pushing the `g`-comparison past the `f`-unit before applying
  -- the final comparison `pullbackComp f (g ≫ h)`.
  have hunit :=
    congrArg
      (fun z ↦
        (((TopCat.Sheaf.pullbackComp (A := Type u) f (g ≫ h)).hom.app 𝒢).hom.app
          (op ((Opens.map f).obj ((Opens.map g).obj ((Opens.map h).obj U)))) z))
      (pullback_unit_naturality_app_transport f g h 𝒢 U
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app
                ((TopCat.Sheaf.pullback (Type u) h).obj 𝒢)).hom.app
              (op ((Opens.map h).obj U))) t))
  simpa [Category.assoc] using hcomp.trans hunit

/-- Helper for Lemma 6.29.3: iterated pullback on sections is associative after normalizing the
canonical pullback-composition comparisons once. -/
private theorem iterated_pullback_sections_map_assoc_transport
    {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (𝒢 : Z.Sheaf (Type u)) (U : Opens Z) :
    iteratedPullbackSectionsMap (f ≫ g) h 𝒢 U =
      cast (by rfl)
        (iteratedPullbackSectionsMap f (g ≫ h) 𝒢 U ∘
          iteratedPullbackSectionsMap g h 𝒢 U) := by
  -- Reduce the function equality to the single-section transport proved just above.
  funext t
  simpa using iterated_pullback_sections_map_assoc_pointwise_transport f g h 𝒢 U t

/-- Helper for Lemma 6.29.3: changing the first pullback map by equality only changes the
iterated pullback section value by heterogeneous transport. -/
private theorem iterated_pullback_sections_map_heq_left
    {W X Y : TopCat.{u}} {f f' : W ⟶ X} (hf : f = f') (g : X ⟶ Y)
    (𝒢 : Y.Sheaf (Type u)) (U : Opens Y)
    (s : (((g⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map g).obj U))) :
    iteratedPullbackSectionsMap f g 𝒢 U s ≍
      iteratedPullbackSectionsMap f' g 𝒢 U s := by
  cases hf
  rfl

/-- Helper for Lemma 6.29.3: changing the second pullback map by equality only changes the
iterated pullback section value by heterogeneous transport, with the input section transported
along the same equality. -/
private theorem iterated_pullback_sections_map_heq_right
    {W X Y : TopCat.{u}} (f : W ⟶ X) {g g' : X ⟶ Y} (hg : g = g')
    (𝒢 : Y.Sheaf (Type u)) (U : Opens Y)
    (s : (((g⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map g).obj U))) :
    iteratedPullbackSectionsMap f g 𝒢 U s ≍
      iteratedPullbackSectionsMap f g' 𝒢 U (cast (by cases hg; rfl) s) := by
  cases hg
  rfl

/-- The transition map on pulled-back sections along a morphism in `Over i`. -/
noncomputable def overPullbackSectionsMap {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) {A B : Over i}
    (φ : A ⟶ B) :
    ((((F.map B.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map B.hom)).obj U)) ⟶
      ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map A.hom)).obj U)) :=
  fun s ↦ cast (overPullbackSections_eq F 𝒢 U φ)
    (iteratedPullbackSectionsMap (F.map φ.left) (F.map B.hom) 𝒢 U s)

-- Proof sketch: for an identity morphism the adjunction unit and the pullback-composition
-- isomorphism are both identities on sections.
/-- Identity compatibility for the stagewise pullback section transition maps. -/
theorem overPullbackSectionsMap_id {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (A : Over i) :
    overPullbackSectionsMap F 𝒢 U (𝟙 A) = id := by
  -- Evaluate the transition map on a section and remove the outer cast by heterogeneous equality.
  funext s
  simp [overPullbackSectionsMap]
  rw [cast_eq_iff_heq]
  -- After rewriting `F.map (𝟙 _)` to the identity map, this is exactly the identity pullback case.
  have hmap : F.map (𝟙 A.left) = 𝟙 (F.obj A.left) := by
    simp
  rw [hmap]
  exact heq_of_eq <|
    congrArg (fun k ↦ k s)
      (iterated_pullback_sections_map_comp_id
        (g := F.map A.hom) (𝒢 := 𝒢) (U := U))

-- Proof sketch: functoriality follows from naturality of the adjunction unit and coherence of the
-- pullback-composition isomorphism.
/-- Helper for Lemma 6.29.3: the normalized associativity identity for iterated pullback sections,
restated in the exact dependent-cast normal form used by `overPullbackSectionsMap_comp`. -/
private theorem over_pullback_sections_assoc_cast_transport {i : I}
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    {A B C : Over i} (φ : A ⟶ B) (ψ : B ⟶ C)
    (s :
      ((((F.map C.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map C.hom)).obj U))) :
    cast (overPullbackSections_eq F 𝒢 U (φ ≫ ψ))
      (iteratedPullbackSectionsMap (F.map (φ.left ≫ ψ.left)) (F.map C.hom) 𝒢 U s) =
    cast (overPullbackSections_eq F 𝒢 U φ)
      (iteratedPullbackSectionsMap (F.map φ.left) (F.map B.hom) 𝒢 U
        (cast (overPullbackSections_eq F 𝒢 U ψ)
          (iteratedPullbackSectionsMap (F.map ψ.left) (F.map C.hom) 𝒢 U s))) := by
  -- Peel off the outer casts into heterogeneous equalities so the remaining transport is only
  -- along equalities of the two comparison morphisms.
  rw [cast_eq_iff_heq, heq_cast_iff_heq]
  have hcomp : F.map (φ.left ≫ ψ.left) = F.map φ.left ≫ F.map ψ.left := by
    simp
  have hψ : F.map ψ.left ≫ F.map C.hom = F.map B.hom := by
    simpa [Functor.map_comp] using congrArg (fun f : B.left ⟶ i ↦ F.map f) (Over.w ψ)
  have hleft :
      iteratedPullbackSectionsMap (F.map (φ.left ≫ ψ.left)) (F.map C.hom) 𝒢 U s ≍
        iteratedPullbackSectionsMap (F.map φ.left ≫ F.map ψ.left) (F.map C.hom) 𝒢 U s := by
    simpa using
      iterated_pullback_sections_map_heq_left
        (hf := hcomp) (g := F.map C.hom) (𝒢 := 𝒢) (U := U) s
  have hassoc :
      iteratedPullbackSectionsMap (F.map φ.left ≫ F.map ψ.left) (F.map C.hom) 𝒢 U s =
        iteratedPullbackSectionsMap (F.map φ.left) (F.map ψ.left ≫ F.map C.hom) 𝒢 U
          (iteratedPullbackSectionsMap (F.map ψ.left) (F.map C.hom) 𝒢 U s) := by
    simpa [Function.comp] using
      iterated_pullback_sections_map_assoc_pointwise_transport
        (f := F.map φ.left) (g := F.map ψ.left) (h := F.map C.hom) (𝒢 := 𝒢) (U := U) s
  have hright :
      iteratedPullbackSectionsMap (F.map φ.left) (F.map ψ.left ≫ F.map C.hom) 𝒢 U
          (iteratedPullbackSectionsMap (F.map ψ.left) (F.map C.hom) 𝒢 U s) ≍
        iteratedPullbackSectionsMap (F.map φ.left) (F.map B.hom) 𝒢 U
          (cast (overPullbackSections_eq F 𝒢 U ψ)
            (iteratedPullbackSectionsMap (F.map ψ.left) (F.map C.hom) 𝒢 U s)) := by
    simpa [overPullbackSections_eq, Functor.map_comp] using
      iterated_pullback_sections_map_heq_right
        (f := F.map φ.left) (hg := hψ) (𝒢 := 𝒢) (U := U)
        (iteratedPullbackSectionsMap (F.map ψ.left) (F.map C.hom) 𝒢 U s)
  exact hleft.trans ((heq_of_eq hassoc).trans hright)

/-- Composition compatibility for the stagewise pullback section transition maps. -/
theorem overPullbackSectionsMap_comp {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i))
    {A B C : Over i} (φ : A ⟶ B) (ψ : B ⟶ C) :
    overPullbackSectionsMap F 𝒢 U (φ ≫ ψ) =
      overPullbackSectionsMap F 𝒢 U φ ∘ overPullbackSectionsMap F 𝒢 U ψ := by
  -- The dedicated cast-transport lemma already matches the exact `Over`-normal form here.
  funext s
  simpa [overPullbackSectionsMap, Function.comp] using
    over_pullback_sections_assoc_cast_transport (F := F) 𝒢 U φ ψ s

/-- Helper for Lemma 6.29.3: once two stage sections become equal after one refinement in
`Over i`, they remain equal after any further domination of that refinement. This isolates the
pure section-theoretic transport needed after the overlap-normalization step has produced pairwise
equalities at finitely many intermediate stages. -/
private theorem equal_overPullbackSectionsMap_of_dominated_refinement
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    {A B C : Over i} (φ : A ⟶ B) (ψ : B ⟶ C)
    {s t : ((((F.map C.hom)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (F.map C.hom)).obj U))}
    (hEq : overPullbackSectionsMap F 𝒢 U ψ s = overPullbackSectionsMap F 𝒢 U ψ t) :
    overPullbackSectionsMap F 𝒢 U (φ ≫ ψ) s =
      overPullbackSectionsMap F 𝒢 U (φ ≫ ψ) t := by
  -- Apply the additional refinement map to the already-equal sections and rewrite the composite
  -- transition with `overPullbackSectionsMap_comp`.
  simpa [overPullbackSectionsMap_comp, Function.comp] using
    congrArg (overPullbackSectionsMap F 𝒢 U φ) hEq

/-- Helper for Lemma 6.29.3: if two identity-over-stage lifts already agree after refining along
`cqq : lqq ⟶ k`, then they also agree after any dominating stage `c : l ⟶ k` factoring through
`cqq`. This packages the common-domination transport needed in the final overlap-gluing step. -/
private theorem equal_identity_over_stage_refinements_of_common_domination
    {k l lqq : I} (c : l ⟶ k) (cqq : lqq ⟶ k) (d : l ⟶ lqq) (hd : d ≫ cqq = c)
    (ℋ : (F.obj k).Sheaf (Type u)) (R : Opens (F.obj k))
    {σ τ : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
      (op ((Opens.map (F.map (𝟙 k))).obj R))}
    (hEq :
      overPullbackSectionsMap F ℋ R
          (A := Over.mk cqq) (B := Over.mk (𝟙 k))
          (Over.homMk cqq (by simp)) σ =
        overPullbackSectionsMap F ℋ R
          (A := Over.mk cqq) (B := Over.mk (𝟙 k))
          (Over.homMk cqq (by simp)) τ) :
    overPullbackSectionsMap F ℋ R
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) σ =
      overPullbackSectionsMap F ℋ R
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) τ := by
  let φd : Over.mk c ⟶ Over.mk cqq := Over.homMk d (by simpa [hd])
  let ψqq : Over.mk cqq ⟶ Over.mk (𝟙 k) := Over.homMk cqq (by simp)
  have hDom :=
    equal_overPullbackSectionsMap_of_dominated_refinement
      (F := F) (𝒢 := ℋ) (U := R)
      (A := Over.mk c) (B := Over.mk cqq) (C := Over.mk (𝟙 k))
      (φ := φd) (ψ := ψqq)
      (s := σ) (t := τ) hEq
  have hMor : φd ≫ ψqq = Over.homMk c (by simp) := by
    ext
    simp [φd, ψqq, hd, Category.assoc]
  simpa using (hMor ▸ hDom)

/-- Helper for Lemma 6.29.3: on an exact overlap open `Rqq`, the common-domination transport from
`cqq` to a fixed common stage `c` is exactly the equality of identity-over-stage refinements used
inside the final same-stage gluing argument. This keeps the endgame proof focused on section-level
normalizations instead of rebuilding the `Over`-morphism bookkeeping inline. -/
private theorem same_stage_overlap_equal_after_common_domination
    {k l lqq : I} (c : l ⟶ k) (cqq : lqq ⟶ k) (d : l ⟶ lqq) (hd : d ≫ cqq = c)
    (ℋ : (F.obj k).Sheaf (Type u)) (Rqq : Opens (F.obj k))
    {σqRid σq'Rid : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
      (op ((Opens.map (F.map (𝟙 k))).obj Rqq))}
    (hEq :
      overPullbackSectionsMap F ℋ Rqq
          (A := Over.mk cqq) (B := Over.mk (𝟙 k))
          (Over.homMk cqq (by simp)) σqRid =
        overPullbackSectionsMap F ℋ Rqq
          (A := Over.mk cqq) (B := Over.mk (𝟙 k))
          (Over.homMk cqq (by simp)) σq'Rid) :
    overPullbackSectionsMap F ℋ Rqq
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) σqRid =
      overPullbackSectionsMap F ℋ Rqq
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) σq'Rid := by
  -- The general common-domination owner already matches this exact-overlap refinement shape.
  exact
    equal_identity_over_stage_refinements_of_common_domination
      (F := F) (c := c) (cqq := cqq) (d := d) (hd := hd)
      (ℋ := ℋ) (R := Rqq) hEq

/-- The over-category diagram
`(a : j ⟶ i) ↦ f_a⁻¹ 𝒢 (f_a⁻¹(U))`
of stagewise pullback sections. -/
noncomputable def limitPullbackSectionsDiagram (i : I) (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) :
    (Over i)ᵒᵖ ⥤ Type u where
  obj A := (((((F.map A.unop.hom)⁻¹).obj 𝒢).presheaf).obj
    (op ((Opens.map (F.map A.unop.hom)).obj U)))
  map φ := overPullbackSectionsMap F 𝒢 U φ.unop
  map_id := by
    intro A
    simpa using overPullbackSectionsMap_id F 𝒢 U A.unop
  map_comp := by
    intro A B C φ ψ
    simpa using overPullbackSectionsMap_comp F 𝒢 U ψ.unop φ.unop

/-- The iterated pullback to the limit through an object of `Over i` is the direct pullback along
the projection `p_i`. -/
theorem limitPullbackSections_eq {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (A : Over i) :
    ((((limit.π F A.left ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U)) =
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
      (op ((Opens.map (limit.π F i)).obj U)) := by
  exact congrArg
    (fun f : limit F ⟶ F.obj i ↦
      (((f⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map f).obj U)))
    (limit.w F A.hom)

/-- The map from a stagewise pullback section to the pullback section on the limit space. -/
noncomputable def pullbackSectionsToLimitMap {i : I}
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) (A : Over i) :
    ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map A.hom)).obj U)) ⟶
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (limit.π F i)).obj U)) :=
  fun s ↦ cast (limitPullbackSections_eq F 𝒢 U A)
    (iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U s)

-- Proof sketch: the comparison to the limit is compatible with stage transition maps by the same
-- adjunction-unit naturality and pullback-composition coherence used above.
/-- Helper for Lemma 6.29.3: the normalized associativity identity for iterated pullback sections,
restated in the exact dependent-cast normal form used by `pullbackSectionsToLimitMap_naturality`.
-/
private theorem limit_pullback_sections_assoc_cast_transport {i : I}
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    {A B : Over i} (φ : A ⟶ B)
    (s :
      ((((F.map B.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map B.hom)).obj U))) :
    cast (limitPullbackSections_eq F 𝒢 U A)
      (iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U
        (cast (overPullbackSections_eq F 𝒢 U φ)
          (iteratedPullbackSectionsMap (F.map φ.left) (F.map B.hom) 𝒢 U s))) =
    cast (limitPullbackSections_eq F 𝒢 U B)
      (iteratedPullbackSectionsMap (limit.π F B.left) (F.map B.hom) 𝒢 U s) := by
  -- Peel off the outer casts into heterogeneous equalities and bridge the remaining morphism
  -- changes by the `Over.w` and `limit.w` comparison equalities.
  rw [cast_eq_iff_heq, heq_cast_iff_heq]
  have hφ : F.map φ.left ≫ F.map B.hom = F.map A.hom := by
    simpa [Functor.map_comp] using congrArg (fun f : A.left ⟶ i ↦ F.map f) (Over.w φ)
  have hlimit : limit.π F A.left ≫ F.map φ.left = limit.π F B.left := by
    simpa using limit.w F φ.left
  have hstart :
      iteratedPullbackSectionsMap (limit.π F A.left) (F.map φ.left ≫ F.map B.hom) 𝒢 U
          (iteratedPullbackSectionsMap (F.map φ.left) (F.map B.hom) 𝒢 U s) ≍
        iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U
          (cast (overPullbackSections_eq F 𝒢 U φ)
            (iteratedPullbackSectionsMap (F.map φ.left) (F.map B.hom) 𝒢 U s)) := by
    simpa [overPullbackSections_eq, Functor.map_comp] using
      iterated_pullback_sections_map_heq_right
        (f := limit.π F A.left) (hg := hφ) (𝒢 := 𝒢) (U := U)
        (iteratedPullbackSectionsMap (F.map φ.left) (F.map B.hom) 𝒢 U s)
  have hassoc :
      iteratedPullbackSectionsMap (limit.π F A.left ≫ F.map φ.left) (F.map B.hom) 𝒢 U s =
        iteratedPullbackSectionsMap (limit.π F A.left) (F.map φ.left ≫ F.map B.hom) 𝒢 U
          (iteratedPullbackSectionsMap (F.map φ.left) (F.map B.hom) 𝒢 U s) := by
    simpa [Function.comp] using
      iterated_pullback_sections_map_assoc_pointwise_transport
        (f := limit.π F A.left) (g := F.map φ.left) (h := F.map B.hom) (𝒢 := 𝒢) (U := U) s
  have hend :
      iteratedPullbackSectionsMap (limit.π F A.left ≫ F.map φ.left) (F.map B.hom) 𝒢 U s ≍
        iteratedPullbackSectionsMap (limit.π F B.left) (F.map B.hom) 𝒢 U s := by
    simpa using
      iterated_pullback_sections_map_heq_left
        (hf := hlimit) (g := F.map B.hom) (𝒢 := 𝒢) (U := U) s
  exact hstart.symm.trans ((heq_of_eq hassoc).symm.trans hend)

/-- Stagewise comparison maps to the limit are compatible with the over-category transitions. -/
theorem pullbackSectionsToLimitMap_naturality {i : I}
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    {A B : Over i} (φ : A ⟶ B) :
    overPullbackSectionsMap F 𝒢 U φ ≫ pullbackSectionsToLimitMap F 𝒢 U A =
      (pullbackSectionsToLimitMap F 𝒢 U B :
        ((((F.map B.hom)⁻¹).obj 𝒢).presheaf).obj
            (op ((Opens.map (F.map B.hom)).obj U)) ⟶
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
            (op ((Opens.map (limit.π F i)).obj U))) := by
  -- Evaluate on a section first, then rewrite the result into the exact cocone-leg cast shape.
  funext s
  -- The dedicated limit-side cast-transport lemma already matches the exact normal form here.
  simpa [overPullbackSectionsMap, pullbackSectionsToLimitMap, Function.comp] using
    limit_pullback_sections_assoc_cast_transport (F := F) 𝒢 U φ s

/-- The cocone from stagewise pullback sections to pullback sections on the limit space. -/
noncomputable def limitPullbackSectionsCocone (i : I)
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) :
    Cocone (limitPullbackSectionsDiagram F i 𝒢 U) where
  pt := ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
    (op ((Opens.map (limit.π F i)).obj U))
  ι :=
    { app := fun A ↦ pullbackSectionsToLimitMap F 𝒢 U A.unop
      naturality := fun {_ _} f ↦
        by simpa using pullbackSectionsToLimitMap_naturality F 𝒢 U f.unop }

/-- The canonical map from the colimit of stagewise pullback sections to the pullback sections on
the limit space. -/
noncomputable def limitPullbackSectionsColimitMap (i : I)
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) :
    colimit (limitPullbackSectionsDiagram F i 𝒢 U) ⟶
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (limit.π F i)).obj U)) :=
  colimit.desc (limitPullbackSectionsDiagram F i 𝒢 U) (limitPullbackSectionsCocone F i 𝒢 U)

/-- Helper for Lemma 6.29.3: evaluating the iterated pullback comparison on germs factors through
the stalk pullback isomorphism for the projection `limit.π F A.left`. -/
private theorem presheaf_stalk_pullback_hom_germ_apply {i : I}
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) (A : Over i)
    (s :
      ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map A.hom)).obj U)))
    (x : ↥(limit F))
    (hx : x ∈ (Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U) :
    let hxA : (limit.π F A.left) x ∈ (Opens.map (F.map A.hom)).obj U := by
      change F.map A.hom ((limit.π F A.left) x) ∈ U
      have hπ : F.map A.hom ((limit.π F A.left) x) = (limit.π F i) x := by
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F A.hom)) x
      exact hπ.symm ▸ (by simpa using hx)
    (TopCat.Presheaf.stalkPullbackIso (Type u) (limit.π F A.left)
        (((F.map A.hom)⁻¹).obj 𝒢).presheaf x).hom
      (((((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
        ((Opens.map (F.map A.hom)).obj U) ((limit.π F A.left) x) hxA s) =
      (((TopCat.Presheaf.pullback (Type u) (limit.π F A.left)).obj
            (((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (limit.π F A.left)).obj ((Opens.map (F.map A.hom)).obj U)) x hx
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) (limit.π F A.left)).unit.app
              (((F.map A.hom)⁻¹).obj 𝒢).presheaf).app
            (op ((Opens.map (F.map A.hom)).obj U))) s)) := by
  -- The presheaf-level stalk pullback owner already computes the first transport layer on germs.
  dsimp only
  simpa [ConcreteCategory.comp_apply] using
    congrArg
      (fun k ↦ k s)
      (TopCat.Presheaf.germ_stalkPullbackHom (Type u) (limit.π F A.left)
        (((F.map A.hom)⁻¹).obj 𝒢).presheaf x ((Opens.map (F.map A.hom)).obj U) hx)

/-- Helper for Lemma 6.29.3: the stalk functor sends a germ in a presheaf pullback to the
corresponding germ in its sheafification after applying the sheafification unit. -/
private theorem toSheafify_stalk_map_germ_apply {X : TopCat.{u}}
    (ℱ : X.Presheaf (Type u)) (W : Opens X) (x : X) (hx : x ∈ W)
    (t : ℱ.obj (op W)) :
    ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) ℱ))
      (ℱ.germ W x hx t) =
      (TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology X) ℱ) W x hx)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) ℱ).app (op W) t) := by
  -- This is the sheafification-unit specialization of `stalkFunctor_map_germ_apply`.
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) ℱ) t)

/-- Helper for Lemma 6.29.3: the stalk functor sends a sheafified germ to the corresponding germ
in the actual pullback sheaf after applying the inverse component of `TopCat.Sheaf.pullbackIso`. -/
private theorem pullbackIso_inv_stalk_map_germ_apply {X Y : TopCat.{u}}
    (f : X ⟶ Y) (𝒢 : Y.Sheaf (Type u)) (W : Opens X) (x : X) (hx : x ∈ W)
    (t :
      (sheafify (Opens.grothendieckTopology X)
        ((TopCat.Sheaf.forget (Type u) Y ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢)).obj
          (op W)) :
    ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        ((TopCat.Sheaf.forget (Type u) X).map
          ((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢)))
      ((TopCat.Presheaf.germ
          (sheafify (Opens.grothendieckTopology X)
            ((TopCat.Sheaf.forget (Type u) Y ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢))
          W x hx) t) =
      (((f⁻¹).obj 𝒢).presheaf).germ W x hx
        ((((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢).1.app (op W)) t) := by
  -- This is the `pullbackIso` specialization of `stalkFunctor_map_germ_apply`.
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hx
      ((TopCat.Sheaf.forget (Type u) X).map
        ((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢)) t)

/-- Helper for Lemma 6.29.3: on ordinary sections, the inverse component of
`TopCat.Sheaf.pullbackIso` identifies the sheafification of the presheaf pullback-unit section
with the sheaf-level pullback adjunction unit. -/
private theorem pullbackIso_inv_toSheafify_unit_section_eq {X Y : TopCat.{u}}
    (f : X ⟶ Y) (𝒢 : Y.Sheaf (Type u)) (U : Opens Y)
    (s : 𝒢.1.obj (op U)) :
    (((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢).1.app (op ((Opens.map f).obj U)))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Sheaf.forget (Type u) Y ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢)).app
            (op ((Opens.map f).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢.1).app
            (op U)) s)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app (op U)) s) := by
  -- Compare the abstract pullback adjunction unit with the left-Kan/sheafification pullback unit.
  have h :=
    Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
      (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) (Type u) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
      𝒢
  have happ :=
    congrArg
      (fun k ↦ (k.1.app (op U)) s)
      h
  have happ' :
      (((TopCat.Sheaf.pullbackIso (Type u) f).hom.app 𝒢).1.app (op ((Opens.map f).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
            (op U)) s) =
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Sheaf.forget (Type u) Y ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢)).app
            (op ((Opens.map f).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢.1).app
            (op U)) s) := by
    -- Evaluating the unit identity at `U` gives the exact section-level normalization.
    simpa using happ
  -- Apply the inverse pullback-comparison component and simplify by `hom_inv_id`.
  rw [← happ']
  simpa using
    congrArg
      (fun k ↦ (k.hom.app (op ((Opens.map f).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
            (op U)) s))
      (Iso.hom_inv_id_app (TopCat.Sheaf.pullbackIso (Type u) f) 𝒢)

/-- Helper for Lemma 6.29.3: after passing to stalks, the sheafification of the presheaf
pullback-unit germ and the inverse pullback comparison still recover the genuine sheaf pullback
unit germ. -/
private theorem pullbackIso_inv_toSheafify_unit_stalk_germ_eq {X Y : TopCat.{u}}
    (f : X ⟶ Y) (𝒢 : Y.Sheaf (Type u)) (U : Opens Y) (x : X)
    (hx : x ∈ (Opens.map f).obj U) (s : 𝒢.1.obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        ((TopCat.Sheaf.forget (Type u) X).map
          ((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢)))
      ((TopCat.Presheaf.germ
          (sheafify (Opens.grothendieckTopology X)
            ((TopCat.Sheaf.forget (Type u) Y ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢))
          ((Opens.map f).obj U) x hx)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            ((TopCat.Sheaf.forget (Type u) Y ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢)).app
          (op ((Opens.map f).obj U))
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢.1).app
              (op U)) s))) =
      (((f⁻¹).obj 𝒢).presheaf).germ ((Opens.map f).obj U) x hx
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
            (op U)) s) := by
  -- First compute the stalk image through `pullbackIso.inv`, then rewrite the section term using
  -- the ordinary-section normalization just proved above.
  rw [pullbackIso_inv_stalk_map_germ_apply]
  rw [pullbackIso_inv_toSheafify_unit_section_eq]

/-- Helper for Lemma 6.29.3: the germ of `iteratedPullbackSectionsMap` is obtained by applying the
stalk map of `pullbackComp` to the germ of the sheaf-level pullback unit section. -/
private theorem iteratedPullbackSectionsMap_stalk_germ_eq {X Y Z : TopCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (𝒢 : Z.Sheaf (Type u)) (U : Opens Z)
    (s : ((((g⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map g).obj U))))
    (x : X) (hx : x ∈ (Opens.map (f ≫ g)).obj U) :
    ((((f ≫ g)⁻¹).obj 𝒢).presheaf).germ
        ((Opens.map (f ≫ g)).obj U) x hx
        (iteratedPullbackSectionsMap f g 𝒢 U s) =
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          ((TopCat.Sheaf.forget (Type u) X).map
            ((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢)))
        (((((f⁻¹).obj ((g⁻¹).obj 𝒢)).presheaf).germ
            ((Opens.map f).obj ((Opens.map g).obj U)) x
            (by simpa [Opens.map_comp_obj, Function.comp] using hx)
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
                ((g⁻¹).obj 𝒢)).1.app (op ((Opens.map g).obj U))) s))) := by
  -- Evaluate the stalk map of the pullback-composition comparison on the pullback-unit section.
  rw [iteratedPullbackSectionsMap]
  dsimp
  simpa [Opens.map_comp_obj, Function.comp] using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply
      ((Opens.map f).obj ((Opens.map g).obj U))
      x
      (by simpa [Opens.map_comp_obj, Function.comp] using hx)
      ((TopCat.Sheaf.forget (Type u) X).map
        ((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
          ((g⁻¹).obj 𝒢)).1.app (op ((Opens.map g).obj U))) s)).symm

/-- Helper for Lemma 6.29.3: on germs, the sheaf-level stalk pullback isomorphism is obtained by
first applying the presheaf stalk pullback owner, then the sheafification unit on stalks, and
finally the inverse component of `TopCat.Sheaf.pullbackIso`. -/
private theorem sheaf_stalkPullbackIso_germ_apply {X Y : TopCat.{u}}
    (f : X ⟶ Y) (𝒢 : Y.Sheaf (Type u)) (U : Opens Y) (x : X)
    (hx : x ∈ (Opens.map f).obj U) (s : 𝒢.1.obj (op U)) :
    ((TopCat.Sheaf.stalkPullbackIso f 𝒢 x).hom)
      (𝒢.presheaf.germ U (f x) (by simpa using hx) s) =
      (((f⁻¹).obj 𝒢).presheaf).germ ((Opens.map f).obj U) x hx
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
            (op U)) s) := by
  have hx' : f x ∈ U := by
    simpa using hx
  -- Expand the sheaf-level stalk pullback bridge into its presheaf, sheafification, and
  -- `pullbackIso.inv` components.
  rw [TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom]
  change
    ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        ((TopCat.Sheaf.forget (Type u) X).map
          ((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢)))
      (((TopCat.Presheaf.stalkFunctor (Type u) x).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            ((TopCat.Presheaf.pullback (Type u) f).obj 𝒢.obj)))
        ((TopCat.Presheaf.stalkPullbackIso (Type u) f 𝒢.presheaf x).hom
          (𝒢.presheaf.germ U (f x) hx' s))) =
      (((f⁻¹).obj 𝒢).presheaf).germ ((Opens.map f).obj U) x hx
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
            (op U)) s)
  -- The presheaf owner computes the first leg on the chosen germ.
  have hpresheaf :
      (TopCat.Presheaf.stalkPullbackIso (Type u) f 𝒢.presheaf x).hom
          (𝒢.presheaf.germ U (f x) hx' s) =
        (((TopCat.Presheaf.pullback (Type u) f).obj 𝒢.1).germ
          ((Opens.map f).obj U) x hx
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢.1).app
              (op U)) s)) := by
    simpa [ConcreteCategory.comp_apply] using
      congrArg
        (fun k ↦ k s)
        (TopCat.Presheaf.germ_stalkPullbackHom (Type u) f 𝒢.1 x U hx)
  rw [hpresheaf]
  -- The sheafification unit transports that presheaf germ to the sheafification germ.
  rw [toSheafify_stalk_map_germ_apply
    (ℱ := ((TopCat.Presheaf.pullback (Type u) f).obj 𝒢.obj))
    (W := (Opens.map f).obj U) (x := x) (hx := hx)
    (t := ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢.1).app
      (op U)) s))]
  -- The final `pullbackIso.inv` component identifies the sheafification germ with the genuine
  -- pullback-sheaf germ.
  exact pullbackIso_inv_toSheafify_unit_stalk_germ_eq
    (f := f) (𝒢 := 𝒢) (U := U) (x := x) (hx := hx) (s := s)

/-- Helper for Lemma 6.29.3: the compact open `U_i` pulled back along an object of `Over i`. -/
private abbrev over_pullback_open {i : I} (U : Opens (F.obj i)) (A : Over i) :
    Opens (F.obj A.left) :=
  (Opens.map (F.map A.hom)).obj U

/-- Helper for Lemma 6.29.3: a point of `p_i^{-1}(U)` maps into the corresponding stage pullback
open `f_a^{-1}(U)`. -/
private theorem limit_projection_mem_over_pullback_open {i : I}
    (U : Opens (F.obj i)) (A : Over i) {x : ↥(limit F)}
    (hx : x ∈ (Opens.map (limit.π F i)).obj U) :
    (limit.π F A.left) x ∈ over_pullback_open F U A := by
  -- The cone relation `p_i = p_{A.left} ≫ f_a` rewrites the limit-side membership at once.
  change F.map A.hom ((limit.π F A.left) x) ∈ U
  have hπ : F.map A.hom ((limit.π F A.left) x) = (limit.π F i) x := by
    exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F A.hom)) x
  exact hπ.symm ▸ hx

/-- Helper for Lemma 6.29.3: before the final `limit.w` cast, the germ of the iterated pullback
section map to the limit is computed by first passing to the stage stalk via
`TopCat.Sheaf.stalkPullbackIso` and then applying the stalk map of the pullback-composition
comparison. This isolates the exact composite-projection stalk identity used in the injectivity
argument. -/
private theorem iterated_limit_pullback_sections_stalk_germ_eq {i : I}
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) (A : Over i)
    (s :
      ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
        (op (over_pullback_open F U A)))
    (x : ↥(limit F)) (hxA : (limit.π F A.left) x ∈ over_pullback_open F U A) :
    ((((limit.π F A.left ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
        ((Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U) x
        (by
          change F.map A.hom ((limit.π F A.left) x) ∈ U
          exact hxA)
        (iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U s) =
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          ((TopCat.Sheaf.forget (Type u) (limit F)).map
            ((TopCat.Sheaf.pullbackComp (A := Type u)
              (limit.π F A.left) (F.map A.hom)).hom.app 𝒢)))
        (((TopCat.Sheaf.stalkPullbackIso (limit.π F A.left)
              (((F.map A.hom)⁻¹).obj 𝒢) x).hom)
          (((((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
            (over_pullback_open F U A) ((limit.π F A.left) x) hxA s)) := by
  have hxcomp : x ∈ (Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U := by
    -- Rewrite the stage-side membership through the explicit composite projection.
    change F.map A.hom ((limit.π F A.left) x) ∈ U
    simpa using hxA
  -- Then compute the germ of the iterated pullback section map on the nose.
  rw [iteratedPullbackSectionsMap_stalk_germ_eq
    (f := limit.π F A.left) (g := F.map A.hom) (𝒢 := 𝒢) (U := U)
    (s := s) (x := x) (hx := hxcomp)]
  -- Finally rewrite the unit germ through the sheaf-level stalk pullback isomorphism.
  exact congrArg
    (((TopCat.Presheaf.stalkFunctor (Type u) x).map
      ((TopCat.Sheaf.forget (Type u) (limit F)).map
        ((TopCat.Sheaf.pullbackComp (A := Type u)
          (limit.π F A.left) (F.map A.hom)).hom.app 𝒢))))
    ((sheaf_stalkPullbackIso_germ_apply
      (f := limit.π F A.left) (𝒢 := (((F.map A.hom)⁻¹).obj 𝒢))
      (U := over_pullback_open F U A) (x := x) (hx := hxA) (s := s)).symm)

/-- Helper for Lemma 6.29.3: the points of `f_a⁻¹(U)` where two pullback sections have the same
stalk germ. This is the open equality locus used by the disagreement-locus argument. -/
private def equal_germ_locus {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (A : Over i)
    (s t : ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op (over_pullback_open F U A))) :
    Set (F.obj A.left) :=
  { x | ∃ hx : x ∈ over_pullback_open F U A,
      ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          (over_pullback_open F U A) x hx s =
        ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          (over_pullback_open F U A) x hx t }

/-- Helper for Lemma 6.29.3: the stage pullback of a quasi-compact open remains constructibly
closed, which is the closed half of the disagreement-locus setup. -/
private theorem over_pullback_open_isClosed_constructible [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) (A : Over i) :
    @IsClosed _ (constructibleTopology ↑(F.obj A.left))
      (over_pullback_open F U A : Set _) := by
  let UA : Opens (F.obj A.left) := over_pullback_open F U A
  -- Spectral maps pull back quasi-compact opens to quasi-compact opens.
  have hCompact : IsCompact (UA : Set ↑(F.obj A.left)) := by
    exact (hF A.hom).isCompact_preimage_of_isOpen U.isOpen hU
  -- Compact opens are clopen for the constructible topology.
  exact (isClopen_constructibleTopology_of_isConstructible
    (hCompact.isConstructible UA.isOpen)).1

/-- Helper for Lemma 6.29.3: equality of stalk germs is an open condition on the stage pullback
open, matching the source proof's equality locus. -/
private theorem equal_germ_locus_isOpen {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (A : Over i)
    (s t : ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op (over_pullback_open F U A))) :
    IsOpen (equal_germ_locus F 𝒢 U A s t) := by
  -- Germ equality at one point spreads to a neighborhood because the pullback is still a sheaf.
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨hxU, hst⟩
  rcases ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ_eq x hxU hxU s t hst with
    ⟨W, hxW, iWU, iWU', heq⟩
  refine Filter.mem_of_superset (W.isOpen.mem_nhds hxW) ?_
  intro y hyW
  refine ⟨iWU.le hyW, ?_⟩
  -- On the witness neighborhood the restricted sections coincide, so their germs coincide too.
  exact ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ_ext W hyW iWU iWU' heq

/-- Helper for Lemma 6.29.3: every open subset of a spectral stage is open for the constructible
topology. -/
private theorem isOpen_constructibleTopology_of_isOpen_stage [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} {s : Set (F.obj i)} (hs : IsOpen s) :
    @IsOpen ↥(F.obj i) (constructibleTopology ↥(F.obj i)) s := by
  -- The compact-open basis of a spectral space consists of constructible-topology open sets.
  refine PrespectralSpace.isTopologicalBasis.isOpen_induction ?_ ?_ hs
  · intro U hU
    exact hU.2.isOpen_constructibleTopology_of_isOpen hU.1
  · intro S hS
    let _ : TopologicalSpace ↥(F.obj i) := constructibleTopology ↥(F.obj i)
    exact isOpen_sUnion fun U hU ↦ hS U hU

/-- Helper for Lemma 6.29.3: the disagreement locus is constructibly closed inside the pulled-back
quasi-compact open. This packages the closed part of the Stacks injectivity argument. -/
private theorem disagreement_locus_isClosed_constructible [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) (A : Over i)
    (s t : ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op (over_pullback_open F U A))) :
    @IsClosed ↥(F.obj A.left) (constructibleTopology ↥(F.obj A.left))
      ((over_pullback_open F U A : Set _) \ equal_germ_locus F 𝒢 U A s t) := by
  -- The ambient pulled-back compact open is constructibly closed by spectrality of `F.map A.hom`.
  have hAmbient :
      @IsClosed ↥(F.obj A.left) (constructibleTopology ↥(F.obj A.left))
        (over_pullback_open F U A : Set _) :=
    over_pullback_open_isClosed_constructible (F := F) hF U hU A
  -- The equality locus is open in the ordinary topology, hence also open constructibly.
  have hEquality :
      @IsOpen ↥(F.obj A.left) (constructibleTopology ↥(F.obj A.left))
        (equal_germ_locus F 𝒢 U A s t) :=
    isOpen_constructibleTopology_of_isOpen_stage (F := F)
      (equal_germ_locus_isOpen (F := F) 𝒢 U A s t)
  -- Therefore the disagreement locus is constructibly closed.
  letI : TopologicalSpace ↥(F.obj A.left) := constructibleTopology ↥(F.obj A.left)
  exact hAmbient.sdiff hEquality

/-- Helper for Lemma 6.29.3: once the limit-side pullback of the pulled-back compact open lies in
the equality-germ locus, Lemma `5.24.3` identifies this with an eventual stagewise inclusion. -/
private theorem limit_preimage_over_pullback_open_subset_iff_exists_stage
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) (A : Over i)
    (s t : ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op (over_pullback_open F U A))) :
    (limit.π F A.left) ⁻¹' (over_pullback_open F U A : Set _) ⊆
        (limit.π F A.left) ⁻¹' (equal_germ_locus F 𝒢 U A s t) ↔
      ∃ (j : I) (b : j ⟶ A.left),
        (F.map b) ⁻¹' (over_pullback_open F U A : Set _) ⊆
          (F.map b) ⁻¹' (equal_germ_locus F 𝒢 U A s t) := by
  -- The pulled-back compact open is constructibly closed at stage `A.left`.
  have hAmbientClosed :
      @IsClosed ↥(F.obj A.left) (constructibleTopology ↥(F.obj A.left))
        (over_pullback_open F U A : Set _) :=
    over_pullback_open_isClosed_constructible (F := F) hF U hU A
  -- Germ equality is ordinary-open, hence constructibly open on a spectral stage.
  have hEqualityOpen :
      @IsOpen ↥(F.obj A.left) (constructibleTopology ↥(F.obj A.left))
        (equal_germ_locus F 𝒢 U A s t) :=
    isOpen_constructibleTopology_of_isOpen_stage (F := F)
      (equal_germ_locus_isOpen (F := F) 𝒢 U A s t)
  -- Apply Lemma `5.24.3` at the fixed stage `A.left`.
  simpa using
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := A.left)
      (E := (over_pullback_open F U A : Set _))
      (F := (equal_germ_locus F 𝒢 U A s t : Set (F.obj A.left)))
      hF hAmbientClosed hEqualityOpen)

/-- Helper for Lemma 6.29.3: once the limit-side pullback of the pulled-back compact open lies in
the equality-germ locus, Lemma `5.24.3` descends that inclusion to some stage refinement of `A`.
This isolates the geometric descent step of the injectivity argument from the remaining stalk
transport calculation. -/
private theorem exists_refinement_of_limit_equal_germ_locus_subset
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) (A : Over i)
    (s t : ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op (over_pullback_open F U A)))
    (hsubset :
      (limit.π F A.left) ⁻¹' (over_pullback_open F U A : Set _) ⊆
        (limit.π F A.left) ⁻¹' (equal_germ_locus F 𝒢 U A s t)) :
    ∃ (j : I) (b : j ⟶ A.left),
      (F.map b) ⁻¹' (over_pullback_open F U A : Set _) ⊆
        (F.map b) ⁻¹' (equal_germ_locus F 𝒢 U A s t) := by
  -- Reuse the specialized eventual-stage criterion for the equality locus.
  exact
    (limit_preimage_over_pullback_open_subset_iff_exists_stage
      (F := F) hF 𝒢 U hU A s t).mp hsubset

/-- Helper for Lemma 6.29.3: for a limit point, lying over the stage pullback open
`f_a⁻¹(U)` is equivalent to lying over the limit pullback open `p_i⁻¹(U)`. This is the basic
membership conversion used by the later germ comparison. -/
private theorem mem_limit_pullback_open_iff {i : I}
    (U : Opens (F.obj i)) (A : Over i) {x : ↥(limit F)} :
    (limit.π F A.left) x ∈ over_pullback_open F U A ↔
      x ∈ (Opens.map (limit.π F i)).obj U := by
  constructor
  · intro hxA
    change (limit.π F i) x ∈ U
    have hπx : F.map A.hom ((limit.π F A.left) x) = (limit.π F i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F A.hom)) x
    exact hπx ▸ hxA
  · intro hx
    exact limit_projection_mem_over_pullback_open (F := F) U A hx

/-- Helper for Lemma 6.29.3: transporting a pullback section along an equality of maps does not
change its germ, up to the unavoidable heterogeneous equality coming from the changed pullback
presheaf. This isolates the cast normalization used for the limit comparison and later
refinements. -/
private theorem pullback_germ_heq_of_hom_eq {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (hfg : f = g) (𝒢 : Y.Sheaf (Type u)) (U : Opens Y) (x : X)
    (hf : x ∈ (Opens.map f).obj U) (hg : x ∈ (Opens.map g).obj U)
    (s :
      ((((f⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map f).obj U)))) :
    (((((g⁻¹).obj 𝒢).presheaf).germ ((Opens.map g).obj U) x hg
        (cast
          (congrArg
            (fun p : X ⟶ Y ↦
              ((((p⁻¹).obj 𝒢).presheaf).obj
                (op ((Opens.map p).obj U))))
            hfg)
          s))) ≍
      ((((f⁻¹).obj 𝒢).presheaf).germ ((Opens.map f).obj U) x hf s) := by
  -- After reducing the map equality, only proof irrelevance for the membership witness remains.
  cases hfg
  cases Subsingleton.elim hg hf
  rfl

/-- Helper for Lemma 6.29.3: equality of the two images in the limit forces equality of the stage
germs on every point of the pulled-back compact open. This is the germ-level bridge needed by the
Stacks disagreement-locus argument. -/
private theorem pullbackSectionsToLimitMap_cast_germ_eq {i : I}
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) (A : Over i)
    (x : ↥(limit F)) (hxA : (limit.π F A.left) x ∈ over_pullback_open F U A)
    (s :
      ((((limit.π F A.left ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U))) :
    (((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
        ((Opens.map (limit.π F i)).obj U) x
        ((mem_limit_pullback_open_iff (F := F) U A).mp hxA)
        (cast (limitPullbackSections_eq F 𝒢 U A) s)) ≍
      ((((limit.π F A.left ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
        ((Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U) x
        (by
          change F.map A.hom ((limit.π F A.left) x) ∈ U
          simpa using hxA)
        s := by
  -- Collapse the composite projection `p_A ≫ f_a` to `p_i` before comparing germs.
  let hπ : limit F ⟶ F.obj i := limit.π F A.left ≫ F.map A.hom
  have hhπ : hπ = limit.π F i := limit.w F A.hom
  have hxLimit : x ∈ (Opens.map (limit.π F i)).obj U :=
    (mem_limit_pullback_open_iff (F := F) U A).mp hxA
  -- The generic map-equality transport theorem matches the exact cast used here.
  simpa [hπ] using
    (pullback_germ_heq_of_hom_eq
      (hfg := hhπ) (𝒢 := 𝒢) (U := U) (x := x)
      (hf := by
        change x ∈ (Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U
        change F.map A.hom ((limit.π F A.left) x) ∈ U
        simpa using hxA)
      (hg := hxLimit)
      (s := s))

/-- Helper for Lemma 6.29.3: equality of the two images in the limit forces equality of the stage
germs on every point of the pulled-back compact open. This is the germ-level bridge needed by the
Stacks disagreement-locus argument. -/
private theorem equal_limit_pullback_sections_preimage_subset_equal_germ_locus
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) (A : Over i)
    (s t : ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op (over_pullback_open F U A)))
    (hEq : pullbackSectionsToLimitMap F 𝒢 U A s =
      pullbackSectionsToLimitMap F 𝒢 U A t) :
    (limit.π F A.left) ⁻¹' (over_pullback_open F U A : Set _) ⊆
      (limit.π F A.left) ⁻¹' (equal_germ_locus F 𝒢 U A s t) := by
  -- Transport the limit-side equality to the stalk at each point of the pulled-back compact open.
  intro x hx
  refine ⟨hx, ?_⟩
  -- Move the limit-side equality to the stalk at `x`.
  have hxLimit : x ∈ (Opens.map (limit.π F i)).obj U :=
    (mem_limit_pullback_open_iff (F := F) U A).mp hx
  have hLimitGerm :=
    congrArg
      (((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
        ((Opens.map (limit.π F i)).obj U) x hxLimit)
      hEq
  have hIterated := hLimitGerm
  -- Rewrite the two casted limit germs to the raw iterated pullback germs before applying the
  -- normalized stalk formula.
  rw [pullbackSectionsToLimitMap, pullbackSectionsToLimitMap] at hIterated
  have hsCast :
      (((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (limit.π F i)).obj U) x hxLimit
          (cast (limitPullbackSections_eq F 𝒢 U A)
            (iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U s))) ≍
        ((((limit.π F A.left ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U) x
          (by
            change F.map A.hom ((limit.π F A.left) x) ∈ U
            simpa using hx)
          (iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U s) :=
    pullbackSectionsToLimitMap_cast_germ_eq
      (F := F) (𝒢 := 𝒢) (U := U) (A := A) (x := x) (hxA := hx)
      (s := iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U s)
  have htCast :
      (((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (limit.π F i)).obj U) x hxLimit
          (cast (limitPullbackSections_eq F 𝒢 U A)
            (iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U t))) ≍
        ((((limit.π F A.left ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U) x
          (by
            change F.map A.hom ((limit.π F A.left) x) ∈ U
            simpa using hx)
          (iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U t) :=
    pullbackSectionsToLimitMap_cast_germ_eq
      (F := F) (𝒢 := 𝒢) (U := U) (A := A) (x := x) (hxA := hx)
      (s := iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U t)
  have hIteratedRaw :
      ((((limit.π F A.left ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U) x
          (by
            change F.map A.hom ((limit.π F A.left) x) ∈ U
            simpa using hx)
          (iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U s) =
        ((((limit.π F A.left ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (limit.π F A.left ≫ F.map A.hom)).obj U) x
          (by
            change F.map A.hom ((limit.π F A.left) x) ∈ U
            simpa using hx)
          (iteratedPullbackSectionsMap (limit.π F A.left) (F.map A.hom) 𝒢 U t) := by
    -- The cast-normalization lemma removes the dependent transport from the limit germs.
    exact eq_of_heq (hsCast.symm.trans ((heq_of_eq hIterated).trans htCast))
  rw [iterated_limit_pullback_sections_stalk_germ_eq
      (F := F) (𝒢 := 𝒢) (U := U) (A := A) (s := s) (x := x) (hxA := hx),
    iterated_limit_pullback_sections_stalk_germ_eq
      (F := F) (𝒢 := 𝒢) (U := U) (A := A) (s := t) (x := x) (hxA := hx)] at hIteratedRaw
  -- The stalk map induced by the pullback-composition isomorphism is injective.
  let compMor :=
    (((TopCat.Presheaf.stalkFunctor (Type u) x).map
      ((TopCat.Sheaf.forget (Type u) (limit F)).map
        ((TopCat.Sheaf.pullbackComp (A := Type u)
          (limit.π F A.left) (F.map A.hom)).hom.app 𝒢))))
  have hCompInj :
      Function.Injective compMor := by
    simpa [compMor] using (ConcreteCategory.bijective_of_isIso compMor).1
  have hStageIso :
      ((TopCat.Sheaf.stalkPullbackIso (limit.π F A.left)
            (((F.map A.hom)⁻¹).obj 𝒢) x).hom)
          (((((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
            (over_pullback_open F U A) ((limit.π F A.left) x) hx s) =
        ((TopCat.Sheaf.stalkPullbackIso (limit.π F A.left)
            (((F.map A.hom)⁻¹).obj 𝒢) x).hom)
          (((((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
            (over_pullback_open F U A) ((limit.π F A.left) x) hx t) :=
    hCompInj (by simpa [compMor] using hIteratedRaw)
  -- The sheaf-level stalk pullback isomorphism is injective as well, so the original germs agree.
  let stalkIsoHom :=
    ((TopCat.Sheaf.stalkPullbackIso (limit.π F A.left)
      (((F.map A.hom)⁻¹).obj 𝒢) x).hom)
  have hStalkInj :
      Function.Injective stalkIsoHom := by
    simpa [stalkIsoHom] using (ConcreteCategory.bijective_of_isIso stalkIsoHom).1
  exact hStalkInj (by simpa [stalkIsoHom] using hStageIso)

/-- Helper for Lemma 6.29.3: if two stage sections have the same image on the limit, then after a
single refinement in `Over i` the two refined sections agree. This is the stagewise equality
witness used in the filtered-colimit injectivity step. -/
private theorem common_refinement_of_equal_limit_pullback_sections
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) (A : Over i)
    (s t : ((((F.map A.hom)⁻¹).obj 𝒢).presheaf).obj
      (op (over_pullback_open F U A)))
    (hEq : pullbackSectionsToLimitMap F 𝒢 U A s =
      pullbackSectionsToLimitMap F 𝒢 U A t) :
    ∃ (B : Over i) (φ : B ⟶ A),
      overPullbackSectionsMap F 𝒢 U φ s =
        overPullbackSectionsMap F 𝒢 U φ t := by
  have hsubset :
      (limit.π F A.left) ⁻¹' (over_pullback_open F U A : Set _) ⊆
        (limit.π F A.left) ⁻¹' (equal_germ_locus F 𝒢 U A s t) :=
    equal_limit_pullback_sections_preimage_subset_equal_germ_locus
      (F := F) hF 𝒢 U hU A s t hEq
  obtain ⟨j, b, hb⟩ :=
    exists_refinement_of_limit_equal_germ_locus_subset
      (F := F) hF 𝒢 U hU A s t hsubset
  let B : Over i := Over.mk (b ≫ A.hom)
  let φ : B ⟶ A := Over.homMk b (by simp [B])
  refine ⟨B, φ, ?_⟩
  -- Compare the two refined sections pointwise on stalks over `f_b⁻¹(f_a⁻¹(U))`.
  apply TopCat.Presheaf.section_ext (((F.map B.hom)⁻¹).obj 𝒢) (over_pullback_open F U B)
  intro x hxB
  have hxBA :
      x ∈ (Opens.map (F.map b ≫ F.map A.hom)).obj U := by
    change F.map A.hom ((F.map b) x) ∈ U
    simpa [B, over_pullback_open, Functor.map_comp, Function.comp] using hxB
  have hxA_pre :
      x ∈ (F.map b) ⁻¹' (over_pullback_open F U A : Set _) := by
    change (F.map b) x ∈ over_pullback_open F U A
    change F.map A.hom ((F.map b) x) ∈ U
    simpa [B, over_pullback_open, Functor.map_comp, Function.comp] using hxB
  have hxEq_pre :
      x ∈ (F.map b) ⁻¹' (equal_germ_locus F 𝒢 U A s t) :=
    hb hxA_pre
  rcases hxEq_pre with ⟨hxA, hStage⟩
  have hcomp : F.map b ≫ F.map A.hom = F.map B.hom := by
    simpa [B] using (Functor.map_comp F b A.hom).symm
  have hsCast :
      (((((F.map B.hom)⁻¹).obj 𝒢).presheaf).germ
          (over_pullback_open F U B) x hxB
          (overPullbackSectionsMap F 𝒢 U φ s)) ≍
        ((((F.map b ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (F.map b ≫ F.map A.hom)).obj U) x hxBA
          (iteratedPullbackSectionsMap (F.map b) (F.map A.hom) 𝒢 U s) := by
    -- Normalize the `Over`-level cast by the functoriality equality `F.map (b ≫ a)`.
    simpa [B, φ, overPullbackSectionsMap, overPullbackSections_eq, over_pullback_open] using
      (pullback_germ_heq_of_hom_eq
        (hfg := hcomp) (𝒢 := 𝒢) (U := U) (x := x)
        (hf := hxBA) (hg := hxB)
        (s := iteratedPullbackSectionsMap (F.map b) (F.map A.hom) 𝒢 U s))
  have htCast :
      (((((F.map B.hom)⁻¹).obj 𝒢).presheaf).germ
          (over_pullback_open F U B) x hxB
          (overPullbackSectionsMap F 𝒢 U φ t)) ≍
        ((((F.map b ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (F.map b ≫ F.map A.hom)).obj U) x hxBA
          (iteratedPullbackSectionsMap (F.map b) (F.map A.hom) 𝒢 U t) := by
    -- The same normalization applies to the second refined section.
    simpa [B, φ, overPullbackSectionsMap, overPullbackSections_eq, over_pullback_open] using
      (pullback_germ_heq_of_hom_eq
        (hfg := hcomp) (𝒢 := 𝒢) (U := U) (x := x)
        (hf := hxBA) (hg := hxB)
        (s := iteratedPullbackSectionsMap (F.map b) (F.map A.hom) 𝒢 U t))
  have hRaw :
      ((((F.map b ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (F.map b ≫ F.map A.hom)).obj U) x hxBA
          (iteratedPullbackSectionsMap (F.map b) (F.map A.hom) 𝒢 U s) =
        ((((F.map b ≫ F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (F.map b ≫ F.map A.hom)).obj U) x hxBA
          (iteratedPullbackSectionsMap (F.map b) (F.map A.hom) 𝒢 U t) := by
    -- Rewrite both refined germs through the stalk pullback isomorphism over `F.map b`.
    rw [iteratedPullbackSectionsMap_stalk_germ_eq
        (f := F.map b) (g := F.map A.hom) (𝒢 := 𝒢) (U := U)
        (s := s) (x := x) (hx := hxBA),
      iteratedPullbackSectionsMap_stalk_germ_eq
        (f := F.map b) (g := F.map A.hom) (𝒢 := 𝒢) (U := U)
        (s := t) (x := x) (hx := hxBA)]
    let compMor :=
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        ((TopCat.Sheaf.forget (Type u) (F.obj j)).map
          ((TopCat.Sheaf.pullbackComp (A := Type u)
            (F.map b) (F.map A.hom)).hom.app 𝒢)))
    let stalkIsoHom :=
      ((TopCat.Sheaf.stalkPullbackIso (F.map b)
        (((F.map A.hom)⁻¹).obj 𝒢) x).hom)
    have hsStage :
        stalkIsoHom
            (((((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
              (over_pullback_open F U A) ((F.map b) x) hxA s) =
          (((((F.map b)⁻¹).obj (((F.map A.hom)⁻¹).obj 𝒢)).presheaf).germ
            ((Opens.map (F.map b)).obj ((Opens.map (F.map A.hom)).obj U)) x
            (by simpa [over_pullback_open, Opens.map_comp_obj, Function.comp] using hxBA)
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map b)).unit.app
                (((F.map A.hom)⁻¹).obj 𝒢)).1.app
              (op ((Opens.map (F.map A.hom)).obj U))) s)) := by
      -- Rewrite the stage germ through the sheaf-level stalk pullback isomorphism.
      simpa [stalkIsoHom, over_pullback_open, Opens.map_comp_obj, Function.comp] using
        (sheaf_stalkPullbackIso_germ_apply
          (f := F.map b) (𝒢 := (((F.map A.hom)⁻¹).obj 𝒢))
          (U := over_pullback_open F U A) (x := x) (hx := hxA) (s := s))
    have htStage :
        stalkIsoHom
            (((((F.map A.hom)⁻¹).obj 𝒢).presheaf).germ
              (over_pullback_open F U A) ((F.map b) x) hxA t) =
          (((((F.map b)⁻¹).obj (((F.map A.hom)⁻¹).obj 𝒢)).presheaf).germ
            ((Opens.map (F.map b)).obj ((Opens.map (F.map A.hom)).obj U)) x
            (by simpa [over_pullback_open, Opens.map_comp_obj, Function.comp] using hxBA)
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map b)).unit.app
                (((F.map A.hom)⁻¹).obj 𝒢)).1.app
              (op ((Opens.map (F.map A.hom)).obj U))) t)) := by
      -- The same stalk comparison formula applies to the second section.
      simpa [stalkIsoHom, over_pullback_open, Opens.map_comp_obj, Function.comp] using
        (sheaf_stalkPullbackIso_germ_apply
          (f := F.map b) (𝒢 := (((F.map A.hom)⁻¹).obj 𝒢))
          (U := over_pullback_open F U A) (x := x) (hx := hxA) (s := t))
    have hIteratedStage :
        (((((F.map b)⁻¹).obj (((F.map A.hom)⁻¹).obj 𝒢)).presheaf).germ
          ((Opens.map (F.map b)).obj ((Opens.map (F.map A.hom)).obj U)) x
          (by simpa [over_pullback_open, Opens.map_comp_obj, Function.comp] using hxBA)
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map b)).unit.app
              (((F.map A.hom)⁻¹).obj 𝒢)).1.app
            (op ((Opens.map (F.map A.hom)).obj U))) s)) =
        (((((F.map b)⁻¹).obj (((F.map A.hom)⁻¹).obj 𝒢)).presheaf).germ
          ((Opens.map (F.map b)).obj ((Opens.map (F.map A.hom)).obj U)) x
          (by simpa [over_pullback_open, Opens.map_comp_obj, Function.comp] using hxBA)
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map b)).unit.app
              (((F.map A.hom)⁻¹).obj 𝒢)).1.app
            (op ((Opens.map (F.map A.hom)).obj U))) t)) := by
      -- The stage germ equality transports across the stalk pullback isomorphism.
      exact hsStage.symm.trans ((congrArg stalkIsoHom hStage).trans htStage)
    exact congrArg compMor hIteratedStage
  -- The two refined sections have the same germ at every point of the refined open.
  exact eq_of_heq (hsCast.trans ((heq_of_eq hRaw).trans htCast.symm))

/-- Helper for Lemma 6.29.3: the canonical map from the filtered colimit of stagewise pullback
sections to the limit pullback sections is injective. This is the direct Stacks injectivity
argument, packaged through one common refinement in `Over i`. -/
private theorem limitPullbackSectionsColimitMap_injective
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : I) (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) :
    Function.Injective (limitPullbackSectionsColimitMap F i 𝒢 U) := by
  intro x y hxy
  -- First lift both colimit classes to the same stage of `(Over i)ᵒᵖ`.
  obtain ⟨A, s, t, rfl, rfl⟩ :=
    CategoryTheory.Limits.Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (colimit.isColimit (limitPullbackSectionsDiagram F i 𝒢 U)) x y
  have hst :
      pullbackSectionsToLimitMap F 𝒢 U A.unop s =
        pullbackSectionsToLimitMap F 𝒢 U A.unop t := by
    simpa [limitPullbackSectionsColimitMap] using hxy
  obtain ⟨B, φ, hφ⟩ :=
    common_refinement_of_equal_limit_pullback_sections
      (F := F) hF 𝒢 U hU A.unop s t hst
  -- Equality at one common refinement stage is exactly the filtered-colimit equality criterion.
  exact
    (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
      (F := limitPullbackSectionsDiagram F i 𝒢 U)
      (colimit.isColimit (limitPullbackSectionsDiagram F i 𝒢 U))
      (i := A) s t).2 ⟨op B, φ.op, by simpa using hφ⟩

/-- Helper for Lemma 6.29.3: the canonical map from the presheaf pullback along `p_i` to the
actual pullback sheaf is locally surjective on the limit space. This records the local existence
of presheaf representatives for sections of `p_i⁻¹ 𝒢`. -/
private noncomputable def presheafPullbackToSheafPullback {i : I}
    (𝒢 : (F.obj i).Sheaf (Type u)) :
    ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf) ⟶
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf) :=
  (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥(limit F))
      ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf)) ≫
    ((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢).1

/-- Helper for Lemma 6.29.3: every section of `p_i⁻¹ 𝒢` on `p_i⁻¹(U)` is locally in the image of
the underlying presheaf pullback. This is the first sheaf-theoretic step in the surjective half
of the Stacks proof. -/
private theorem presheafPullbackToSheafPullback_def
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) :
    presheafPullbackToSheafPullback (F := F) (i := i) 𝒢 =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥(limit F))
          ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf)) ≫
        ((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢).1 := by
  -- The bridge map is defined to be this composite.
  rfl

/-- Helper for Lemma 6.29.3: the sheafification unit on the presheaf pullback along `p_i`
induces a bijection on every stalk. This is the proved owner-side input for the later local
surjectivity argument. -/
private theorem presheaf_pullback_toSheafify_stalk_bijective
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (x : ↥(limit F)) :
    Function.Bijective
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥(limit F))
          ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf))) := by
  -- This is exactly the standard sheafification-unit isomorphism on stalks, specialized to the
  -- pullback presheaf along `p_i`.
  have hIso :
      IsIso
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥(limit F))
            ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf))) := by
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        (p₀ := x) (C := Type u)
        (𝓕 := ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf)))
  exact
    ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥(limit F))
          ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf)))

/-- Helper for Lemma 6.29.3: the full comparison from the presheaf pullback along `p_i` to the
actual pullback sheaf is bijective on every stalk. This packages the stalkwise bridge before the
remaining finite stage-descent step. -/
private theorem presheafPullbackToSheafPullback_stalk_bijective
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (x : ↥(limit F)) :
    Function.Bijective
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢)) := by
  let stalkMap := TopCat.Presheaf.stalkFunctor (Type u) x
  let unitMap :=
    stalkMap.map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥(limit F))
        ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf))
  let comparisonMap :=
    stalkMap.map (((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢).1)
  have hUnit :
      Function.Bijective unitMap := by
    -- The first factor is the sheafification unit, whose stalk map is already known to be
    -- bijective.
    simpa [stalkMap, unitMap] using
      presheaf_pullback_toSheafify_stalk_bijective (F := F) (i := i) 𝒢 x
  have hComparison :
      Function.Bijective comparisonMap := by
    -- The second factor comes from the pullback-comparison isomorphism, so its stalk map is
    -- bijective as well.
    have hComparisonIso :
        IsIso
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map
            (((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢).1)) := by
      exact
        @Functor.map_isIso _ _ _ _ _ _
          (TopCat.Presheaf.stalkFunctor (Type u) x)
          (((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢).1)
          ((TopCat.Sheaf.forget (Type u) (limit F)).map_isIso
            ((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢))
    simpa [stalkMap, comparisonMap] using
      (ConcreteCategory.bijective_of_isIso
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          (((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢).1)))
  -- The stalk map of the composite bridge is the composition of those two bijections.
  have hMap :
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢)) =
      comparisonMap ∘ unitMap := by
    rw [presheafPullbackToSheafPullback_def]
    funext t
    change
      stalkMap.map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥(limit F))
              ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf) ≫
            (((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢).1))
          t =
        stalkMap.map (((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢).1)
          (stalkMap.map
            (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥(limit F))
              ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf))
            t)
    exact
      congrFun
        (Functor.map_comp stalkMap
          (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥(limit F))
            ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf))
          (((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢).1))
        t
  rw [hMap]
  exact Function.Bijective.comp hComparison hUnit

/-- Helper for Lemma 6.29.3: every section of `p_i⁻¹ 𝒢` is locally represented by a section of
the presheaf pullback along `p_i`. This records the local-existence half of the source proof
before compact-open descent to one stage. -/
private theorem presheafPullbackToSheafPullback_isLocallySurjective
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) :
    TopCat.Presheaf.IsLocallySurjective
      (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢) := by
  -- For presheaves on a topological space, local surjectivity is equivalent to surjectivity on
  -- all stalks.
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x
  exact (presheafPullbackToSheafPullback_stalk_bijective (F := F) (𝒢 := 𝒢) x).2

/-- Helper for Lemma 6.29.3: projection pullbacks of stage compact opens, now viewed on the actual
categorical limit object `limit F`. This keeps the later local-surjectivity step on the same space
as the target sections, avoiding an extra transport through `TopCat.limitCone`. -/
private def projection_preimage_basis
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)] :
    (Σ j : I, CompactOpens (F.obj j)) → Set ↥(limit F) :=
  fun p ↦ (limit.π F p.1) ⁻¹' (p.2 : Set (F.obj p.1))

/-- Helper for Lemma 6.29.3: realize a basis subset `p_j⁻¹(V)` as an actual open of the limit
space, so later local sections can be restricted to it without repeatedly rebuilding openness
proofs. -/
private def projection_preimage_open
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (p : Σ j : I, CompactOpens (F.obj j)) : Opens ↥(limit F) :=
  ⟨projection_preimage_basis (F := F) p, by
    rcases p with ⟨j, V⟩
    exact V.isOpen.preimage (limit.π F j).hom.continuous⟩

/-- Helper for Lemma 6.29.3: pullbacks of compact opens from the stages form a basis on the
inverse-limit space. This is the source-faithful replacement for the `5.24.5` basis fragment that
cannot be imported directly in this file. -/
private theorem projection_preimage_compact_open_basis
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a)) :
    IsTopologicalBasis (Set.range (projection_preimage_basis (F := F))) := by
  let C := limit.cone F
  let T : ∀ j : I, Set (Set ↥(F.obj j)) := fun j ↦
    {U : Set ↥(F.obj j) | IsOpen U ∧ IsCompact U}
  have hT_basis : ∀ j : I, IsTopologicalBasis (T j) := by
    intro j
    simpa [T] using (PrespectralSpace.isTopologicalBasis (X := F.obj j))
  have hT_univ : ∀ j : I, Set.univ ∈ T j := by
    intro j
    exact ⟨isOpen_univ, isCompact_univ⟩
  have hT_inter :
      ∀ j : I, ∀ U V : Set ↥(F.obj j), U ∈ T j → V ∈ T j → U ∩ V ∈ T j := by
    intro j U V hU hV
    exact ⟨hU.1.inter hV.1, hU.2.inter_of_isOpen hV.2 hU.1 hV.1⟩
  have hT_compat :
      ∀ i j : I, ∀ a : i ⟶ j, ∀ V, V ∈ T j → (F.map a) ⁻¹' V ∈ T i := by
    intro i j a V hV
    exact ⟨hV.1.preimage (hF a).continuous,
      (hF a).isCompact_preimage_of_isOpen hV.1 hV.2⟩
  have hBasisAux :
      IsTopologicalBasis {W : Set C.pt | ∃ j, ∃ V ∈ T j, W = C.π.app j ⁻¹' V} := by
    -- Apply the cofiltered-limit basis owner with the compact-open basis on each stage.
    exact
      TopCat.isTopologicalBasis_cofiltered_limit F C (limit.isLimit F)
        T hT_basis hT_univ hT_inter hT_compat
  have hRange :
      Set.range (projection_preimage_basis (F := F)) =
        {W : Set C.pt | ∃ j, ∃ V ∈ T j, W = C.π.app j ⁻¹' V} := by
    ext W
    constructor
    · rintro ⟨⟨j, U⟩, rfl⟩
      exact ⟨j, (U : Set ↥(F.obj j)), ⟨U.isOpen, U.isCompact⟩, rfl⟩
    · rintro ⟨j, U, hU, rfl⟩
      exact ⟨⟨j, ⟨⟨U, hU.2⟩, hU.1⟩⟩, rfl⟩
  -- Rewrite the owner theorem into the sigma-indexed family used in this file.
  rw [hRange]
  exact hBasisAux

/-- Helper for Lemma 6.29.3: every open neighborhood on the limit contains a smaller neighborhood
of the form `p_j⁻¹(V)` with `V` quasi-compact open on some stage. This is the basis-level
shrinking step used to replace arbitrary local-surjectivity opens by compact opens that can later
be descended to one stage. -/
private theorem exists_limit_projection_compact_open_neighborhood
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {W : Opens ↥(limit F)} {x : ↥(limit F)} (hx : x ∈ W) :
    ∃ (j : I) (V : CompactOpens (F.obj j)),
      x ∈ (limit.π F j) ⁻¹' (V : Set (F.obj j)) ∧
        (limit.π F j) ⁻¹' (V : Set (F.obj j)) ⊆ (W : Set ↥(limit F)) := by
  have hBasis := projection_preimage_compact_open_basis (F := F) hF
  -- Shrink the ambient open pullback to one basis element through the compact-open basis theorem.
  obtain ⟨S, hS, hxS, hSW⟩ := hBasis.exists_subset_of_mem_open hx W.isOpen
  rcases hS with ⟨⟨j, V⟩, rfl⟩
  exact ⟨j, V, hxS, hSW⟩

/-- Helper for Lemma 6.29.3: every point of `p_i⁻¹(U)` has a compact-open neighborhood of the
form `p_j⁻¹(V)` contained in `p_i⁻¹(U)`. This is the specialization of the general basis-shrinking
lemma to the pullback open appearing in the statement. -/
private theorem exists_projection_preimage_compact_open_subset
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (U : Opens (F.obj i)) {x : ↥(limit F)}
    (hx : x ∈ (Opens.map (limit.π F i)).obj U) :
    ∃ (j : I) (V : CompactOpens (F.obj j)),
      x ∈ (limit.π F j) ⁻¹' (V : Set (F.obj j)) ∧
        (limit.π F j) ⁻¹' (V : Set (F.obj j)) ⊆
          (Opens.map (limit.π F i)).obj U := by
  -- Reinterpret `p_i⁻¹(U)` as an open of the limit and apply the general neighborhood-shrinking
  -- lemma proved just above.
  exact
    exists_limit_projection_compact_open_neighborhood (F := F) hF
      (W := (Opens.map (limit.π F i)).obj U) hx

/-- Helper for Lemma 6.29.3: at stage `j`, keep only those points whose image in the fixed stage
`i` lies in the chosen compact open along every arrow `j ⟶ i`. This is the closed stable family
whose inverse limit realizes the pulled-back compact open. -/
private def stagewise_pullback_family
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (i : I) (U : CompactOpens (F.obj i)) (j : I) :
    Set (F.obj j) :=
  ⋂ a : j ⟶ i, (F.map a) ⁻¹' (U : Set (F.obj i))

/-- Helper for Lemma 6.29.3: each stagewise pullback family is closed in the constructible
topology, because every member is the pullback of the compact open `U` along a spectral map. -/
private theorem stagewise_pullback_family_closed
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : I) (U : CompactOpens (F.obj i)) (j : I) :
    IsClosed[constructibleTopology (F.obj j)]
      (stagewise_pullback_family (F := F) i U j) := by
  -- Compact opens are clopen for the constructible topology on a spectral space.
  have hU_closed : IsClosed[constructibleTopology (F.obj i)] (U : Set (F.obj i)) := by
    exact
      (isClopen_constructibleTopology_of_isConstructible
        (U.isCompact.isConstructible U.isOpen)).1
  -- Intersect the constructibly closed pullbacks over all arrows `j ⟶ i`.
  dsimp [stagewise_pullback_family]
  refine
    @isClosed_iInter (F.obj j) (j ⟶ i) (constructibleTopology (F.obj j))
      (fun a ↦ (F.map a) ⁻¹' (U : Set (F.obj i))) ?_
  intro a
  exact
    @IsClosed.preimage (F.obj j) (F.obj i)
      (constructibleTopology (F.obj j)) (constructibleTopology (F.obj i))
      (F.map a) (hF a).continuous_constructibleTopology _ hU_closed

/-- Helper for Lemma 6.29.3: the stagewise pullback family is stable under the transition maps of
the inverse system. -/
private theorem stagewise_pullback_family_mapsTo
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (i : I) (U : CompactOpens (F.obj i)) {j k : I} (a : j ⟶ k) :
    Set.MapsTo (F.map a)
      (stagewise_pullback_family (F := F) i U j)
      (stagewise_pullback_family (F := F) i U k) := by
  intro x hx
  refine mem_iInter.2 fun b ↦ ?_
  have hx' :
      x ∈ (F.map (a ≫ b)) ⁻¹' (U : Set (F.obj i)) := by
    exact mem_iInter.1 hx (a ≫ b)
  change F.map b (F.map a x) ∈ (U : Set (F.obj i))
  simpa [stagewise_pullback_family, Functor.map_comp] using hx'

/-- Helper for Lemma 6.29.3: forgetting the subtype coordinate gives a natural transformation
from the stable-subset diagram back to the ambient diagram. -/
private def stagewise_pullback_forget_hom
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (i : I) (U : CompactOpens (F.obj i))
    (hZ_maps :
      ∀ ⦃j k : I⦄ (a : j ⟶ k), Set.MapsTo (F.map a)
        (stagewise_pullback_family (F := F) i U j)
        (stagewise_pullback_family (F := F) i U k)) :
    (F.stableSubsetDiagram (stagewise_pullback_family (F := F) i U) hZ_maps) ⟶ F where
  app j := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  naturality {X Y} a := by
    -- Both sides are the same restricted ambient map on points.
    apply ConcreteCategory.ext
    ext x
    rfl


/-- Helper for Lemma 6.29.3: the inverse image of a stage open along the projection to that stage
is open on the actual categorical limit object. -/
private theorem limit_projection_preimage_isOpen
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (i : I) (U : Opens (F.obj i)) :
    IsOpen ((limit.π F i) ⁻¹' (U : Set (F.obj i))) := by
  -- This keeps the later compact-open shrinking argument on the same limit object as the target
  -- section space.
  exact U.isOpen.preimage (limit.π F i).hom.continuous

/-- Helper for Lemma 6.29.3: every open subset of a spectral space is open for the constructible
topology. -/
private theorem isOpen_constructibleTopology_of_isOpen {X : Type u} [TopologicalSpace X]
    [SpectralSpace X] {s : Set X} (hs : IsOpen s) :
    IsOpen[constructibleTopology X] s := by
  -- The compact-open basis of a spectral space consists of constructible opens.
  refine PrespectralSpace.isTopologicalBasis.isOpen_induction ?_ ?_ hs
  · intro V hV
    exact hV.2.isOpen_constructibleTopology_of_isOpen hV.1
  · intro S hS
    let _ : TopologicalSpace X := constructibleTopology X
    exact isOpen_sUnion fun V hV ↦ hS V hV

/-- Helper for Lemma 6.29.3: the inverse image of a compact open along the limit projection is
compact. This is the Chapter 5 compactness input needed before extracting a finite local
presentation of a section on `p_i⁻¹(U)`. -/
private theorem limit_projection_preimage_isCompact_of_compact_open
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : I) (U : CompactOpens (F.obj i)) :
    IsCompact ((limit.π F i) ⁻¹' (U : Set (F.obj i))) := by
  have hπ : IsSpectralMap (limit.π F i) :=
    isSpectralMap_projection_of_isLimit_of_cofiltered_spectral_diagram
      (C := limit.cone F) (limit.isLimit F) hF i
  exact hπ.isCompact_preimage_of_isOpen U.isOpen U.isCompact

/-- Helper for Lemma 6.29.3: for a quasi-compact open `U ⊆ X_i`, its pullback `p_i⁻¹(U)` is
compact on the limit space. This is the exact compactness statement used to cut a local cover down
to finitely many compact-open pieces. -/
private theorem limit_pullback_open_isCompact
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : I) (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) :
    IsCompact (((Opens.map (limit.π F i)).obj U : Opens ↥(limit F)) : Set ↥(limit F)) := by
  -- Repackage `U` as a compact open and apply the spectral-projection compactness lemma.
  let Uc : CompactOpens (F.obj i) := ⟨⟨(U : Set (F.obj i)), hU⟩, U.isOpen⟩
  simpa [Uc] using
    limit_projection_preimage_isCompact_of_compact_open (F := F) hF i Uc

/-- Helper for Lemma 6.29.3: once `p_i⁻¹(U)` is known to be compact on the limit, it admits a
finite cover by basis opens of the form `p_j⁻¹(V)` with `V` compact open on a stage. This is the
finite-cover extraction step before attaching local section representatives. -/
private theorem limit_pullback_open_has_finite_projection_preimage_cover
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (U : Opens (F.obj i))
    (hCompact : IsCompact (((Opens.map (limit.π F i)).obj U : Opens ↥(limit F)) : Set ↥(limit F))) :
    ∃ t : Finset (Σ j : I, CompactOpens (F.obj j)),
      (((Opens.map (limit.π F i)).obj U : Opens ↥(limit F)) : Set ↥(limit F)) ⊆
        ⋃ p ∈ t, projection_preimage_basis (F := F) p ∧
      ∀ p ∈ t, projection_preimage_basis (F := F) p ⊆
        (((Opens.map (limit.π F i)).obj U : Opens ↥(limit F)) : Set ↥(limit F)) := by
  classical
  let S : Set ↥(limit F) :=
    (((Opens.map (limit.π F i)).obj U : Opens ↥(limit F)) : Set ↥(limit F))
  have hNeighborhood :
      ∀ x : S, ∃ p : Σ j : I, CompactOpens (F.obj j),
        x.1 ∈ projection_preimage_basis (F := F) p ∧
          projection_preimage_basis (F := F) p ⊆ S := by
    intro x
    obtain ⟨j, V, hxV, hVsubset⟩ :=
      exists_projection_preimage_compact_open_subset (F := F) hF U x.2
    exact ⟨⟨j, V⟩, hxV, hVsubset⟩
  choose p hp_mem hp_sub using hNeighborhood
  have hOpen : ∀ x : S, IsOpen (projection_preimage_basis (F := F) (p x)) := by
    intro x
    rcases p x with ⟨j, V⟩
    -- Each chosen basis neighborhood is the pullback of a compact open along a projection.
    exact V.isOpen.preimage (limit.π F j).hom.continuous
  have hCover : S ⊆ ⋃ x : S, projection_preimage_basis (F := F) (p x) := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hp_mem ⟨x, hx⟩⟩
  obtain ⟨t₀, ht₀⟩ :=
    hCompact.elim_finite_subcover
      (fun x : S ↦ projection_preimage_basis (F := F) (p x))
      hOpen hCover
  let t : Finset (Σ j : I, CompactOpens (F.obj j)) := t₀.image p
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ ⋃ y ∈ t₀, projection_preimage_basis (F := F) (p y) := ht₀ hx
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨y, hx'⟩
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨hy, hyx⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨p y, Set.mem_iUnion.2 ?_⟩
    exact ⟨Finset.mem_image.2 ⟨y, hy, rfl⟩, hyx⟩
  · intro q hq
    rcases Finset.mem_image.1 hq with ⟨y, hy, rfl⟩
    exact hp_sub y

/-- Helper for Lemma 6.29.3: every section of the presheaf pullback along `p_i` comes from one
stage open in the canonical left-Kan-extension colimit presentation. This isolates the explicit
stage representative that the local-surjectivity step later normalizes to a sheaf section. -/
private theorem presheaf_pullback_section_has_stage_representative
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (W : Opens ↥(limit F))
    (t : ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf).obj (op W)) :
    ∃ (A : CostructuredArrow (Opens.map (limit.π F i)).op (op W))
      (σ : 𝒢.presheaf.obj A.left),
      colimit.ι (CostructuredArrow.proj (Opens.map (limit.π F i)).op (op W) ⋙ 𝒢.presheaf) A σ =
        (((Opens.map (limit.π F i)).op.leftKanExtensionObjIsoColimit 𝒢.presheaf (op W)).hom t) := by
  let e := ((Opens.map (limit.π F i)).op.leftKanExtensionObjIsoColimit 𝒢.presheaf (op W))
  -- Extract one explicit stage representative from the filtered colimit description of pullback.
  obtain ⟨A, σ, hσ⟩ :=
    CategoryTheory.Limits.Types.jointly_surjective
      (CostructuredArrow.proj (Opens.map (limit.π F i)).op (op W) ⋙ 𝒢.presheaf)
      (colimit.isColimit _) (e.hom t)
  exact ⟨A, σ, hσ⟩

/-- Helper for Lemma 6.29.3: a section of the presheaf pullback over an open `W` is literally the
restriction of one stage-open section along a single costructured-arrow map into `W`. This
normalizes the left-Kan-extension colimit witness to the explicit pullback formula needed later in
the source-faithful local-to-global descent. -/
private theorem presheaf_pullback_section_has_explicit_stage_representative
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (W : Opens ↥(limit F))
    (t : ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf).obj (op W)) :
    ∃ (A : CostructuredArrow (Opens.map (limit.π F i)).op (op W))
      (σ : 𝒢.presheaf.obj A.left),
      t =
        (((((Opens.map (limit.π F i)).op.leftKanExtensionUnit 𝒢.presheaf).app A.left) ≫
            (((Opens.map (limit.π F i)).op.leftKanExtension 𝒢.presheaf).map A.hom)) σ) := by
  let e := ((Opens.map (limit.π F i)).op.leftKanExtensionObjIsoColimit 𝒢.presheaf (op W))
  obtain ⟨A, σ, hσ⟩ :=
    presheaf_pullback_section_has_stage_representative (F := F) 𝒢 W t
  refine ⟨A, σ, ?_⟩
  have hInv :
      t =
        e.inv
          (colimit.ι (CostructuredArrow.proj (Opens.map (limit.π F i)).op (op W) ⋙ 𝒢.presheaf)
            A σ) := by
    -- Apply the inverse of the left-Kan-extension colimit comparison to the chosen colimit class.
    simpa [e] using congrArg e.inv hσ.symm
  have hι :
      e.inv
          (colimit.ι (CostructuredArrow.proj (Opens.map (limit.π F i)).op (op W) ⋙ 𝒢.presheaf)
            A σ) =
        (((((Opens.map (limit.π F i)).op.leftKanExtensionUnit 𝒢.presheaf).app A.left) ≫
            (((Opens.map (limit.π F i)).op.leftKanExtension 𝒢.presheaf).map A.hom)) σ) := by
    -- The owner-level `ι_leftKanExtensionObjIsoColimit_inv` formula turns that colimit class into
    -- the explicit stage section followed by restriction to `W`.
    have hι' :=
      congrArg
        (fun k ↦ k σ)
        ((Opens.map (limit.π F i)).op.ι_leftKanExtensionObjIsoColimit_inv
          (F := 𝒢.presheaf) (X := op W) A)
    simpa [e, TopCat.Presheaf.pullback] using hι'
  exact hInv.trans hι

/-- Helper for Lemma 6.29.3: applying the bridge from the presheaf pullback to the actual
pullback sheaf turns an explicit costructured-arrow representative into the genuine pullback-unit
section restricted along the chosen map into the target open. This is the section-level
normalization step before shrinking to compact opens. -/
private theorem explicit_stage_representative_eq_pullback_unit_section
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) {W : Opens ↥(limit F)}
    (A : CostructuredArrow (Opens.map (limit.π F i)).op (op W))
    (σ : 𝒢.presheaf.obj A.left) :
    (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢).app (op W)
        (((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf).map A.hom
          ((((Opens.map (limit.π F i)).op.leftKanExtensionUnit 𝒢.presheaf).app A.left) σ)) =
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map A.hom
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
            A.left) σ) := by
  -- Evaluate the naturality square for the bridge map on the chosen stage section.
  have hnat :=
    congrArg
      (fun k ↦
        k ((((Opens.map (limit.π F i)).op.leftKanExtensionUnit 𝒢.presheaf).app A.left) σ))
      ((presheafPullbackToSheafPullback (F := F) (i := i) 𝒢).naturality A.hom)
  have hunit :
      (((TopCat.Sheaf.pullbackIso (Type u) (limit.π F i)).inv.app 𝒢).1.app
          (op ((Opens.map (limit.π F i)).obj (Opposite.unop A.left))))
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology ↥(limit F))
            ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf)).app
          (op ((Opens.map (limit.π F i)).obj (Opposite.unop A.left)))
          ((((Opens.map (limit.π F i)).op.leftKanExtensionUnit 𝒢.presheaf).app A.left) σ)) =
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
            A.left) σ) := by
    simpa [TopCat.Presheaf.pullback] using
      (pullbackIso_inv_toSheafify_unit_section_eq
        (f := limit.π F i) (𝒢 := 𝒢) (U := Opposite.unop A.left) (s := σ))
  simpa [presheafPullbackToSheafPullback_def, hunit] using hnat

/-- Helper for Lemma 6.29.3: every point of `p_i⁻¹(U)` has a compact-open projection-basis
neighborhood on which the given pullback-sheaf section comes from a section of the presheaf
pullback along `p_i`. This isolates the local-surjectivity and basis-shrinking steps before the
remaining stage-representation descent. -/
private theorem point_has_projection_preimage_local_presheaf_representative
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    {x : ↥(limit F)} (hx : x ∈ (Opens.map (limit.π F i)).obj U) :
    ∃ (j : I) (Wj : CompactOpens (F.obj j)),
      x ∈ projection_preimage_open (F := F) ⟨j, Wj⟩ ∧
        ∃ hWU : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
            (Opens.map (limit.π F i)).obj U,
          ∃ t :
            ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf).obj
              (op (projection_preimage_open (F := F) ⟨j, Wj⟩)),
            (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢).app
                (op (projection_preimage_open (F := F) ⟨j, Wj⟩)) t =
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s := by
  let Ulimit : Opens ↥(limit F) := (Opens.map (limit.π F i)).obj U
  have hlocal :=
    (TopCat.Presheaf.isLocallySurjective_iff
      (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢)).mp
      (presheafPullbackToSheafPullback_isLocallySurjective (F := F) (i := i) 𝒢)
  -- Choose an arbitrary local presheaf representative of the section near `x`.
  obtain ⟨N, hNU, ⟨tN, htN⟩, hxN⟩ := hlocal Ulimit s x hx
  -- Shrink that open to one compact-open basis neighborhood of the inverse-limit topology.
  obtain ⟨j, Wj, hxW, hWN⟩ :=
    exists_limit_projection_compact_open_neighborhood (F := F) hF (W := N) hxN
  let W : Opens ↥(limit F) := projection_preimage_open (F := F) ⟨j, Wj⟩
  have hWN_le : W ≤ N := by
    intro y hy
    exact hWN hy
  have hWU : W ≤ Ulimit := le_trans hWN_le hNU
  let tW :
      ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf).obj (op W) :=
    ((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf).map (homOfLE hWN_le).op tN
  have hEqW :
      (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢).app (op W) tW =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s := by
    -- Restrict the local equality from `N` down to the chosen basis neighborhood.
    have hnat :=
      TopCat.Presheaf.map_restrict
        (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢) hWN_le tN
    have hrestrict :=
      congrArg
        (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWN_le).op)
        htN
    calc
      (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢).app (op W) tW =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWN_le).op
            ((presheafPullbackToSheafPullback (F := F) (i := i) 𝒢).app (op N) tN) := by
              simpa [tW, TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] using hnat
      _ = ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWN_le).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hNU).op s) := by
              simpa [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] using hrestrict
      _ = ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s := by
            have hop :
                (homOfLE hNU).op ≫ (homOfLE hWN_le).op = (homOfLE hWU).op := by
              apply Subsingleton.elim
            simpa [Functor.map_comp] using
              congrArg
                (fun f : op Ulimit ⟶ op W ↦
                  ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
                hop
  refine ⟨j, Wj, ?_, hWU, tW, hEqW⟩
  simpa [W, projection_preimage_open] using hxW

/-- Helper for Lemma 6.29.3: every point of `p_i⁻¹(U)` has a projection-basis neighborhood on
which the given pullback-sheaf section is already the restriction of a genuine stage-open
pullback-unit section. This packages the new section-level normalization without yet shrinking the
stage open to a compact open. -/
private theorem point_has_projection_preimage_local_stage_open_representative
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    {x : ↥(limit F)} (hx : x ∈ (Opens.map (limit.π F i)).obj U) :
    ∃ (j : I) (Wj : CompactOpens (F.obj j)),
      x ∈ projection_preimage_open (F := F) ⟨j, Wj⟩ ∧
        ∃ hWU : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
            (Opens.map (limit.π F i)).obj U,
          ∃ (A : CostructuredArrow (Opens.map (limit.π F i)).op
              (op (projection_preimage_open (F := F) ⟨j, Wj⟩)))
            (σ : 𝒢.presheaf.obj A.left),
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s =
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map A.hom
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app A.left) σ) := by
  obtain ⟨j, Wj, hxW, hWU, t, ht⟩ :=
    point_has_projection_preimage_local_presheaf_representative
      (F := F) hF 𝒢 U s hx
  let W : Opens ↥(limit F) := projection_preimage_open (F := F) ⟨j, Wj⟩
  obtain ⟨A, σ, hStage⟩ :=
    presheaf_pullback_section_has_explicit_stage_representative (F := F) 𝒢 W t
  have hStage' :
      t =
        (((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf).map A.hom
          ((((Opens.map (limit.π F i)).op.leftKanExtensionUnit 𝒢.presheaf).app A.left) σ)) := by
    -- Rewrite the explicit left-Kan-extension representative in the concrete pullback-presheaf API.
    simpa [TopCat.Presheaf.pullback] using hStage
  refine ⟨j, Wj, hxW, hWU, A, σ, ?_⟩
  -- Normalize the local presheaf representative to a genuine stage-open pullback-unit section.
  calc
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s =
        (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢).app (op W) t := by
          simpa [W] using ht.symm
    _ =
        (presheafPullbackToSheafPullback (F := F) (i := i) 𝒢).app (op W)
          (((TopCat.Presheaf.pullback (Type u) (limit.π F i)).obj 𝒢.presheaf).map A.hom
            ((((Opens.map (limit.π F i)).op.leftKanExtensionUnit 𝒢.presheaf).app A.left) σ)) := by
              rw [hStage']
    _ =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map A.hom
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
              A.left) σ) := by
                exact explicit_stage_representative_eq_pullback_unit_section
                  (F := F) (i := i) 𝒢 A σ

/-- Helper for Lemma 6.29.3: every point of `p_i⁻¹(U)` has a projection-basis neighborhood on
which the given pullback-sheaf section is already the restriction of a genuine pullback-unit
section coming from a compact open of `X_i`. This is the compact-open refinement of the
stage-open local representative needed before the finite descent/gluing step. -/
private theorem point_has_projection_preimage_local_stage_representative
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    {x : ↥(limit F)} (hx : x ∈ (Opens.map (limit.π F i)).obj U) :
    ∃ (j : I) (Wj : CompactOpens (F.obj j)) (Vi : CompactOpens (F.obj i))
      (σ : 𝒢.1.obj (op Vi.toOpens)),
      x ∈ projection_preimage_open (F := F) ⟨j, Wj⟩ ∧
        ∃ hWU : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
            (Opens.map (limit.π F i)).obj U,
          ∃ hWV : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
              (Opens.map (limit.π F i)).obj Vi.toOpens,
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s =
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWV).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app (op Vi.toOpens)) σ) := by
  obtain ⟨j₀, Wj₀, hxW₀, hW₀U, A, σA, hEq₀⟩ :=
    point_has_projection_preimage_local_stage_open_representative
      (F := F) hF 𝒢 U s hx
  let W₀ : Opens ↥(limit F) := projection_preimage_open (F := F) ⟨j₀, Wj₀⟩
  have hW₀A :
      W₀ ≤ (Opens.map (limit.π F i)).obj (Opposite.unop A.left) := by
    simpa [W₀] using (Opposite.unop A.hom).le
  have hxA : (limit.π F i) x ∈ Opposite.unop A.left := by
    exact hW₀A hxW₀
  obtain ⟨Vi, hxVi, hViA_set⟩ :=
    exists_compactOpen_subset_of_mem_open
      (X := F.obj i) (U := Opposite.unop A.left) (x := (limit.π F i) x) hxA
  have hViA : Vi.toOpens ≤ Opposite.unop A.left := by
    exact hViA_set
  let Wcap : Opens ↥(limit F) := W₀ ⊓ (Opens.map (limit.π F i)).obj Vi.toOpens
  have hxWcap : x ∈ Wcap := by
    exact ⟨hxW₀, hxVi⟩
  obtain ⟨j, Wj, hxW, hWcap⟩ :=
    exists_limit_projection_compact_open_neighborhood (F := F) hF (W := Wcap) hxWcap
  let W : Opens ↥(limit F) := projection_preimage_open (F := F) ⟨j, Wj⟩
  have hWW₀ : W ≤ W₀ := by
    intro y hy
    exact (hWcap hy).1
  have hWVi : W ≤ (Opens.map (limit.π F i)).obj Vi.toOpens := by
    intro y hy
    exact (hWcap hy).2
  have hWU : W ≤ (Opens.map (limit.π F i)).obj U := le_trans hWW₀ hW₀U
  have hWUA :
      W ≤ (Opens.map (limit.π F i)).obj (Opposite.unop A.left) := le_trans hWW₀ hW₀A
  have hPreViA :
      (Opens.map (limit.π F i)).obj Vi.toOpens ≤
        (Opens.map (limit.π F i)).obj (Opposite.unop A.left) := by
    intro y hy
    exact hViA hy
  let σ : 𝒢.1.obj (op Vi.toOpens) := 𝒢.presheaf.map (homOfLE hViA).op σA
  have hRestrict := congrArg
      (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWW₀).op)
      hEq₀
  have hLeft :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWW₀).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₀U).op s) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s := by
    have hop :
        (homOfLE hW₀U).op ≫ (homOfLE hWW₀).op = (homOfLE hWU).op := by
      apply Subsingleton.elim
    simpa [Functor.map_comp] using
      congrArg
        (fun f : op ((Opens.map (limit.π F i)).obj U) ⟶ op W ↦
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
        hop
  have hUnitNat :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hPreViA).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
              A.left) σA) =
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
            (op Vi.toOpens)) σ) := by
    -- Restrict the unit section from the larger stage open `A.left.unop` to the compact open `Vi`.
    simpa [σ, TopologicalSpace.Opens.map_homOfLE] using
      (NatTrans.naturality_apply
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1)
        (homOfLE hViA).op σA).symm
  have hRight :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWW₀).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map A.hom
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app A.left) σA)) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWVi).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
              (op Vi.toOpens)) σ) := by
    have hcomp₁ : A.hom ≫ (homOfLE hWW₀).op = (homOfLE hWUA).op := by
      apply Subsingleton.elim
    have hcomp₂ :
        (homOfLE hPreViA).op ≫ (homOfLE hWVi).op = (homOfLE hWUA).op := by
      apply Subsingleton.elim
    calc
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWW₀).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map A.hom
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app A.left) σA)) =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWUA).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app A.left) σA) := by
              simpa [Functor.map_comp] using
                congrArg
                  (fun f :
                    ((Opens.map (limit.π F i)).op.obj A.left) ⟶ op W ↦
                    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f
                      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                          𝒢).1.app A.left) σA))
                  hcomp₁
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWVi).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hPreViA).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app A.left) σA)) := by
                    simpa [Functor.map_comp] using
                      congrArg
                        (fun f :
                          ((Opens.map (limit.π F i)).op.obj A.left) ⟶ op W ↦
                          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f
                            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                                𝒢).1.app A.left) σA))
                        hcomp₂.symm
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWVi).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
                (op Vi.toOpens)) σ) := by
                  rw [hUnitNat]
  refine ⟨j, Wj, Vi, σ, ?_, hWU, hWVi, ?_⟩
  · simpa [W, projection_preimage_open] using hxW
  · -- Restrict the stage-open equality to the compact-open refinement and rewrite both sides.
    calc
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWW₀).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₀U).op s) := by
              simpa using hLeft.symm
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWW₀).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map A.hom
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app A.left) σA)) := by
                    simpa [W₀] using hRestrict
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWVi).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
                (op Vi.toOpens)) σ) := by
                  exact hRight

/-- Helper for Lemma 6.29.3: one local presentation datum consists of a stage `j`, a compact open
`Wj ⊆ X_j`, a compact open `Vi ⊆ X_i`, and a section of `𝒢` on `Vi`. This is the finite datum
later extracted from the pointwise compact-open local representatives. -/
private abbrev LocalStageSectionDatum
    [∀ i : I, SpectralSpace (F.obj i)] (i : I) (𝒢 : (F.obj i).Sheaf (Type u)) :=
  Σ j : I, Σ _ : CompactOpens (F.obj j), Σ Vi : CompactOpens (F.obj i), 𝒢.1.obj (op Vi.toOpens)

/-- Helper for Lemma 6.29.3: one finite local datum can be descended from the limit side to an
actual compact-open section of a stage pullback sheaf over some stage mapping to `i`. This
packages the output of the single-datum descent step so later finite synchronization lemmas can
refer to it without repeating the entire dependent existential. -/
private abbrev DescendedLocalSectionData
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    (q : LocalStageSectionDatum (F := F) i 𝒢) :=
  ∃ (k : I) (α : k ⟶ q.1) (a : k ⟶ i),
    let Wk : CompactOpens (F.obj k) :=
      stage_pullback_compact_open (F := F) hF α q.2.1
    ; ∃ hStage : (F.map α) ⁻¹' (q.2.1 : Set (F.obj q.1)) ⊆
        (F.map a) ⁻¹' (q.2.2.1 : Set (F.obj i)),
      ∃ hWkU : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
          (Opens.map (limit.π F i)).obj U,
        ∃ hWkV : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
            (Opens.map (limit.π F i)).obj q.2.2.1.toOpens,
          ∃ hWkVi : Wk.toOpens ≤ (Opens.map (F.map a)).obj q.2.2.1.toOpens,
            ∃ τ : ((((F.map a)⁻¹).obj 𝒢).presheaf).obj (op Wk.toOpens),
              τ =
                ((((F.map a)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkVi).op
                  ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map a)).unit.app
                      𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) ∧
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s =
                ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
                  ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                      𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2)

/-- Helper for Lemma 6.29.3: after choosing one common stage over `i`, a descended local datum is
the same data together with a comparison arrow from that common stage to the datum's original
stage-over-`i`. This keeps the common-stage synchronization interface short enough to use in the
final surjectivity proof. -/
private abbrev CommonStageDescendedLocalSectionData
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    (q : LocalStageSectionDatum (F := F) i 𝒢) (j : I) (g : j ⟶ i) :=
  ∃ (k : I) (α : k ⟶ q.1) (a : k ⟶ i) (δ : j ⟶ k),
    let Wk : CompactOpens (F.obj k) :=
      stage_pullback_compact_open (F := F) hF α q.2.1
    ; δ ≫ a = g ∧
      ∃ hStage : (F.map α) ⁻¹' (q.2.1 : Set (F.obj q.1)) ⊆
          (F.map a) ⁻¹' (q.2.2.1 : Set (F.obj i)),
        ∃ hWkU : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
            (Opens.map (limit.π F i)).obj U,
          ∃ hWkV : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
              (Opens.map (limit.π F i)).obj q.2.2.1.toOpens,
            ∃ hWkVi : Wk.toOpens ≤ (Opens.map (F.map a)).obj q.2.2.1.toOpens,
              ∃ τ : ((((F.map a)⁻¹).obj 𝒢).presheaf).obj (op Wk.toOpens),
                τ =
                  ((((F.map a)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkVi).op
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map a)).unit.app
                        𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) ∧
                ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s =
                ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                        𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2)

/-- Helper for Lemma 6.29.3: once one local datum has been transported to a common stage `j`,
choosing an actual compact open `Wj ⊆ X_j` together with the corresponding local section and
limit-side comparison packages the section-bearing data that must later be descended to the stage
cover used for gluing. -/
private abbrev CommonStageLocalSectionOn
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    (q : LocalStageSectionDatum (F := F) i 𝒢) {j : I} (g : j ⟶ i)
    (Wj : CompactOpens (F.obj j)) :=
  projection_preimage_open (F := F) ⟨j, Wj⟩ =
      projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ∧
    ∃ hWjU : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
        (Opens.map (limit.π F i)).obj U,
      ∃ hWjV : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
          (Opens.map (limit.π F i)).obj q.2.2.1.toOpens,
        ∃ hWjVi : Wj.toOpens ≤ (Opens.map (F.map g)).obj q.2.2.1.toOpens,
          ∃ τj : ((((F.map g)⁻¹).obj 𝒢).presheaf).obj (op Wj.toOpens),
            τj =
              ((((F.map g)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjVi).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map g)).unit.app
                    𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) ∧
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjU).op s =
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjV).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2)

/-- Helper for Lemma 6.29.3: a section of `p_i⁻¹ 𝒢` over `p_i⁻¹(U)` admits a finite cover by
projection-basis compact opens on which it is represented by pullback-unit sections coming from
compact opens of `X_i`. This packages the pointwise local compact-open representatives into the
finite family needed for the later one-stage descent and gluing argument. -/
private theorem pullback_section_has_finite_projection_preimage_local_presentation
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (hU : IsCompact (U : Set (F.obj i)))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U))) :
    ∃ t : Finset (LocalStageSectionDatum (F := F) i 𝒢),
      (((Opens.map (limit.π F i)).obj U : Opens ↥(limit F)) : Set ↥(limit F)) ⊆
        ⋃ q ∈ t, projection_preimage_basis (F := F) ⟨q.1, q.2.1⟩ ∧
      ∀ q ∈ t,
        ∃ hWU : projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ≤
            (Opens.map (limit.π F i)).obj U,
          ∃ hWV : projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ≤
              (Opens.map (limit.π F i)).obj q.2.2.1.toOpens,
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s =
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWV).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
  classical
  let S : Set ↥(limit F) :=
    (((Opens.map (limit.π F i)).obj U : Opens ↥(limit F)) : Set ↥(limit F))
  have hCompact :
      IsCompact (((Opens.map (limit.π F i)).obj U : Opens ↥(limit F)) : Set ↥(limit F)) :=
    limit_pullback_open_isCompact (F := F) hF i U hU
  have hNeighborhood :
      ∀ x : S, ∃ q : LocalStageSectionDatum (F := F) i 𝒢,
        x.1 ∈ projection_preimage_basis (F := F) ⟨q.1, q.2.1⟩ ∧
          ∃ hWU : projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ≤
              (Opens.map (limit.π F i)).obj U,
            ∃ hWV : projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ≤
                (Opens.map (limit.π F i)).obj q.2.2.1.toOpens,
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s =
                ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWV).op
                  ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                      𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
    intro x
    obtain ⟨j, Wj, Vi, σ, hxW, hWU, hWV, hEq⟩ :=
      point_has_projection_preimage_local_stage_representative
        (F := F) hF 𝒢 U s x.2
    refine ⟨⟨j, Wj, Vi, σ⟩, ?_, hWU, hWV, hEq⟩
    simpa [projection_preimage_open] using hxW
  choose q hq_mem hqWU hqWV hqEq using hNeighborhood
  have hOpen :
      ∀ x : S, IsOpen (projection_preimage_basis (F := F) ⟨(q x).1, (q x).2.1⟩) := by
    intro x
    exact ((q x).2.1).isOpen.preimage (limit.π F ((q x).1)).hom.continuous
  have hCover :
      S ⊆ ⋃ x : S, projection_preimage_basis (F := F) ⟨(q x).1, (q x).2.1⟩ := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hq_mem ⟨x, hx⟩⟩
  -- Compactness cuts the pointwise local presentation down to finitely many basis neighborhoods.
  obtain ⟨t₀, ht₀⟩ :=
    hCompact.elim_finite_subcover
      (fun x : S ↦ projection_preimage_basis (F := F) ⟨(q x).1, (q x).2.1⟩)
      hOpen hCover
  let t : Finset (LocalStageSectionDatum (F := F) i 𝒢) := t₀.image q
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ ⋃ y ∈ t₀, projection_preimage_basis (F := F) ⟨(q y).1, (q y).2.1⟩ := ht₀ hx
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨y, hx'⟩
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨hy, hyx⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨q y, Set.mem_iUnion.2 ?_⟩
    exact ⟨Finset.mem_image.2 ⟨y, hy, rfl⟩, hyx⟩
  · intro q' hq'
    rcases Finset.mem_image.1 hq' with ⟨x, hx, rfl⟩
    exact ⟨hqWU x, hqWV x, hqEq x⟩

/-- Helper for Lemma 6.29.3: if a compact projection-basis neighborhood on stage `j` lies over a
compact open on the base stage `i`, then Lemma `5.24.6(2)` refines it to one actual stage `k`
over `i`. Restricting the limit-side equality to that refined compact neighborhood preserves the
same local comparison with the base-stage pullback-unit section. -/
private theorem local_stage_section_datum_refines_limit_side_equality
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    (q : LocalStageSectionDatum (F := F) i 𝒢)
    (hWU : projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ≤
      (Opens.map (limit.π F i)).obj U)
    (hWV : projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ≤
      (Opens.map (limit.π F i)).obj q.2.2.1.toOpens)
    (hEq :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWV).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2)) :
    ∃ (k : I) (α : k ⟶ q.1) (a : k ⟶ i),
      let Wk : CompactOpens (F.obj k) :=
        stage_pullback_compact_open (F := F) hF α q.2.1
      ∃ hStage : (F.map α) ⁻¹' (q.2.1 : Set (F.obj q.1)) ⊆
          (F.map a) ⁻¹' (q.2.2.1 : Set (F.obj i)),
        ∃ hWkU : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
            (Opens.map (limit.π F i)).obj U,
          ∃ hWkV : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
              (Opens.map (limit.π F i)).obj q.2.2.1.toOpens,
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s =
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
  obtain ⟨k, α, a, hStage⟩ :=
    exists_common_refinement_of_preimage_subset
      (F := F) (fun {_ _} b ↦ hF b) q.2.1 q.2.2.1 hWV
  let Wk : CompactOpens (F.obj k) :=
    stage_pullback_compact_open (F := F) hF α q.2.1
  have hRefine :
      projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
        projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ := by
    intro x hx
    have hx' : F.map α ((limit.π F k) x) ∈ (q.2.1 : Set (F.obj q.1)) := by
      simpa [projection_preimage_open, projection_preimage_basis, Wk, stage_pullback_compact_open]
        using hx
    have hπ : F.map α ((limit.π F k) x) = (limit.π F q.1) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F α)) x
    change (limit.π F q.1) x ∈ (q.2.1 : Set (F.obj q.1))
    simpa [hπ] using hx'
  have hWkU :
      projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
        (Opens.map (limit.π F i)).obj U :=
    le_trans hRefine hWU
  have hWkV :
      projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
        (Opens.map (limit.π F i)).obj q.2.2.1.toOpens :=
    le_trans hRefine hWV
  have hRestrict :=
    congrArg
      (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hRefine).op)
      hEq
  refine ⟨k, α, a, hStage, hWkU, hWkV, ?_⟩
  -- Restrict the previously known local equality from `p_j⁻¹(W_j)` to the refined neighborhood
  -- `p_k⁻¹((F.map α)⁻¹(W_j))`.
  calc
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hRefine).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s) := by
            have hop :
                (homOfLE hWU).op ≫ (homOfLE hRefine).op = (homOfLE hWkU).op := by
              apply Subsingleton.elim
            simpa [Functor.map_comp] using
              congrArg
                (fun f :
                  op ((Opens.map (limit.π F i)).obj U) ⟶
                    op (projection_preimage_open (F := F) ⟨k, Wk⟩) ↦
                  ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
                hop.symm
    _ =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hRefine).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWV).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2)) := by
                  simpa using hRestrict
    _ =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
            have hop :
                (homOfLE hWV).op ≫ (homOfLE hRefine).op = (homOfLE hWkV).op := by
              apply Subsingleton.elim
            simpa [Functor.map_comp] using
              congrArg
                (fun f :
                  op ((Opens.map (limit.π F i)).obj q.2.2.1.toOpens) ⟶
                    op (projection_preimage_open (F := F) ⟨k, Wk⟩) ↦
                  ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                        𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2))
                hop

/-- Helper for Lemma 6.29.3: a set-theoretic refinement
`(F.map α)⁻¹(W) ⊆ (F.map a)⁻¹(V)` induces the corresponding morphism of stage opens
`(F.map α)⁻¹(U) ⟶ (F.map a)⁻¹(V)`. This is the restriction map needed to turn a base-stage
pullback-unit section into an actual local section on the refined compact open. -/
private theorem stage_pullback_compact_open_le_map_of_subset
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j k : I} (α : k ⟶ j) (a : k ⟶ i)
    (W : CompactOpens (F.obj j)) (V : CompactOpens (F.obj i))
    (hStage : (F.map α) ⁻¹' (W : Set (F.obj j)) ⊆ (F.map a) ⁻¹' (V : Set (F.obj i))) :
    (stage_pullback_compact_open (F := F) hF α W).toOpens ≤
      (Opens.map (F.map a)).obj V.toOpens := by
  intro x hx
  exact hStage (by simpa [stage_pullback_compact_open] using hx)

/-- Helper for Lemma 6.29.3: after refining one local presentation datum to a stage over `i`, the
base-stage section produces an honest local section of the pullback sheaf on the refined compact
open. This isolates the section-valued part of the local descent interface while carrying along
the already proved limit-side equality on that refined neighborhood. -/
private theorem local_stage_section_datum_descends_to_base_stage
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    (q : LocalStageSectionDatum (F := F) i 𝒢)
    (hWU : projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ≤
      (Opens.map (limit.π F i)).obj U)
    (hWV : projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ≤
      (Opens.map (limit.π F i)).obj q.2.2.1.toOpens)
    (hEq :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWU).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWV).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2)) :
    DescendedLocalSectionData (F := F) hF 𝒢 U s q := by
  rcases
      local_stage_section_datum_refines_limit_side_equality
        (F := F) hF 𝒢 U s q hWU hWV hEq with
    ⟨k, α, a, hStage, hWkU, hWkV, hEqRefined⟩
  let Wk : CompactOpens (F.obj k) :=
    stage_pullback_compact_open (F := F) hF α q.2.1
  have hWkVi :
      Wk.toOpens ≤ (Opens.map (F.map a)).obj q.2.2.1.toOpens := by
    -- Turn the refined set-theoretic inclusion into the restriction morphism on stage opens.
    exact
      stage_pullback_compact_open_le_map_of_subset
        (F := F) hF α a q.2.1 q.2.2.1 hStage
  let τ : ((((F.map a)⁻¹).obj 𝒢).presheaf).obj (op Wk.toOpens) :=
    ((((F.map a)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkVi).op
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map a)).unit.app 𝒢).1.app
          (op q.2.2.1.toOpens)) q.2.2.2)
  refine ⟨k, α, a, hStage, hWkU, hWkV, hWkVi, τ, rfl, hEqRefined⟩

/-- Helper for Lemma 6.29.3: once each local compact-open datum has been descended to some stage
over `i`, cofilteredness synchronizes the finitely many descended arrows to one common stage over
`i`. This isolates the finite-arrow domination step before the later same-stage cover refinement
and sheaf gluing. -/
private theorem descended_local_sections_admit_common_stage
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    (t : Finset (LocalStageSectionDatum (F := F) i 𝒢))
    (hDescendedLocal : ∀ q ∈ t, DescendedLocalSectionData (F := F) hF 𝒢 U s q) :
    ∃ (j : I) (g : j ⟶ i),
      ∀ q ∈ t, CommonStageDescendedLocalSectionData (F := F) hF 𝒢 U s q j g := by
  classical
  choose k α a hTail using hDescendedLocal
  let jt : {q // q ∈ t} → I := fun q ↦ k q.1 q.2
  obtain ⟨j, g, hg⟩ :=
    common_refinement_of_finite_arrows_to
      (I := I) (i := i) (s := t.attach) (j := jt)
      (f := fun q _hq ↦ a q.1 q.2)
  refine ⟨j, g, ?_⟩
  intro q hq
  have hqAttach : (⟨q, hq⟩ : {q // q ∈ t}) ∈ t.attach := by
    simp
  rcases hg ⟨q, hq⟩ hqAttach with ⟨δ, hδ⟩
  refine ⟨k q hq, α q hq, a q hq, δ, ?_⟩
  simpa [CommonStageDescendedLocalSectionData, DescendedLocalSectionData] using
    And.intro hδ (hTail q hq)

/-- Helper for Lemma 6.29.3: once one local datum has been moved to a common stage `j`, the
refined compact open can be realized directly on `X_j`, together with the corresponding local
section of `((F.map g)⁻¹).obj 𝒢`. This makes the common-stage data explicit enough for the later
finite cover descent and overlap-gluing step. -/
private theorem common_stage_descended_section_transport
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    (q : LocalStageSectionDatum (F := F) i 𝒢) {j : I} {g : j ⟶ i}
    (hCommon : CommonStageDescendedLocalSectionData (F := F) hF 𝒢 U s q j g) :
    ∃ Wj : CompactOpens (F.obj j),
      projection_preimage_open (F := F) ⟨j, Wj⟩ =
        projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ∧
      ∃ hWjU : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
          (Opens.map (limit.π F i)).obj U,
        ∃ hWjV : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
            (Opens.map (limit.π F i)).obj q.2.2.1.toOpens,
          ∃ hWjVi : Wj.toOpens ≤ (Opens.map (F.map g)).obj q.2.2.1.toOpens,
            ∃ τj : ((((F.map g)⁻¹).obj 𝒢).presheaf).obj (op Wj.toOpens),
              τj =
                ((((F.map g)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjVi).op
                  ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map g)).unit.app
                      𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) ∧
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjU).op s =
                ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjV).op
                  ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                      𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
  rcases hCommon with ⟨k, α, a, δ, hδ, hStage, hWkU, hWkV, hWkVi, τ, hτ, hEq⟩
  let Wk : CompactOpens (F.obj k) :=
    stage_pullback_compact_open (F := F) hF α q.2.1
  let Wj : CompactOpens (F.obj j) :=
    stage_pullback_compact_open (F := F) hF (δ ≫ α) q.2.1
  have hWkEqQ :
      projection_preimage_open (F := F) ⟨k, Wk⟩ =
        projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ := by
    ext x
    constructor
    · intro hx
      have hx' : F.map α ((limit.π F k) x) ∈ (q.2.1 : Set (F.obj q.1)) := by
        simpa [projection_preimage_open, projection_preimage_basis, Wk, stage_pullback_compact_open]
          using hx
      have hπ : F.map α ((limit.π F k) x) = (limit.π F q.1) x := by
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F α)) x
      change (limit.π F q.1) x ∈ (q.2.1 : Set (F.obj q.1))
      simpa [hπ] using hx'
    · intro hx
      have hx' : (limit.π F q.1) x ∈ (q.2.1 : Set (F.obj q.1)) := by
        simpa [projection_preimage_open, projection_preimage_basis] using hx
      change F.map α ((limit.π F k) x) ∈ (q.2.1 : Set (F.obj q.1))
      have hπ : F.map α ((limit.π F k) x) = (limit.π F q.1) x := by
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F α)) x
      simpa [projection_preimage_open, projection_preimage_basis, Wk, stage_pullback_compact_open,
        hπ] using hx'
  have hWjEqQ :
      projection_preimage_open (F := F) ⟨j, Wj⟩ =
        projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ := by
    ext x
    constructor
    · intro hx
      have hx' : F.map (δ ≫ α) ((limit.π F j) x) ∈ (q.2.1 : Set (F.obj q.1)) := by
        simpa [projection_preimage_open, projection_preimage_basis, Wj, stage_pullback_compact_open]
          using hx
      have hπ : F.map (δ ≫ α) ((limit.π F j) x) = (limit.π F q.1) x := by
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F (δ ≫ α))) x
      change (limit.π F q.1) x ∈ (q.2.1 : Set (F.obj q.1))
      rw [hπ] at hx'
      exact hx'
    · intro hx
      have hx' : (limit.π F q.1) x ∈ (q.2.1 : Set (F.obj q.1)) := by
        simpa [projection_preimage_open, projection_preimage_basis] using hx
      change F.map (δ ≫ α) ((limit.π F j) x) ∈ (q.2.1 : Set (F.obj q.1))
      have hπ : F.map (δ ≫ α) ((limit.π F j) x) = (limit.π F q.1) x := by
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F (δ ≫ α))) x
      rw [hπ]
      exact hx'
  have hWjEqWk :
      projection_preimage_open (F := F) ⟨j, Wj⟩ =
        projection_preimage_open (F := F) ⟨k, Wk⟩ := by
    exact hWjEqQ.trans hWkEqQ.symm
  have hWjU :
      projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
        (Opens.map (limit.π F i)).obj U := by
    exact hWjEqWk.symm ▸ hWkU
  have hWjV :
      projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
        (Opens.map (limit.π F i)).obj q.2.2.1.toOpens := by
    exact hWjEqWk.symm ▸ hWkV
  have hWjVi :
      Wj.toOpens ≤ (Opens.map (F.map g)).obj q.2.2.1.toOpens := by
    intro x hx
    have hx' : F.map (δ ≫ α) x ∈ (q.2.1 : Set (F.obj q.1)) := by
      simpa [Wj, stage_pullback_compact_open] using hx
    have hx'' : F.map α (F.map δ x) ∈ (q.2.1 : Set (F.obj q.1)) := by
      simpa [Functor.map_comp] using hx'
    have hStage' : F.map a (F.map δ x) ∈ (q.2.2.1 : Set (F.obj i)) := hStage hx''
    change F.map g x ∈ (q.2.2.1 : Set (F.obj i))
    have hg : F.map g x = F.map a (F.map δ x) := by
      simpa [Functor.map_comp] using congrArg (fun f : j ⟶ i ↦ F.map f x) hδ.symm
    exact hg ▸ hStage'
  let τj : ((((F.map g)⁻¹).obj 𝒢).presheaf).obj (op Wj.toOpens) :=
    ((((F.map g)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjVi).op
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map g)).unit.app 𝒢).1.app
          (op q.2.2.1.toOpens)) q.2.2.2)
  have hEqWj :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjU).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjV).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
    -- Restrict the already-proved limit-side equality from the old common-stage neighborhood
    -- `p_k⁻¹(Wk)` to the equal neighborhood `p_j⁻¹(Wj)`.
    calc
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjU).op s =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjEqWk.le).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s) := by
              have hop :
                  (homOfLE hWkU).op ≫ (homOfLE hWjEqWk.le).op = (homOfLE hWjU).op := by
                apply Subsingleton.elim
              simpa [Functor.map_comp] using
                congrArg
                  (fun f :
                    op ((Opens.map (limit.π F i)).obj U) ⟶
                      op (projection_preimage_open (F := F) ⟨j, Wj⟩) ↦
                    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
                  hop.symm
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjEqWk.le).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2)) := by
                    rw [hEq]
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjV).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
              have hop :
                  (homOfLE hWkV).op ≫ (homOfLE hWjEqWk.le).op = (homOfLE hWjV).op := by
                apply Subsingleton.elim
              simpa [Functor.map_comp] using
                congrArg
                  (fun f :
                    op ((Opens.map (limit.π F i)).obj q.2.2.1.toOpens) ⟶
                      op (projection_preimage_open (F := F) ⟨j, Wj⟩) ↦
                    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f
                      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                          𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2))
                  hop
  refine ⟨Wj, hWjEqQ, hWjU, hWjV, hWjVi, τj, rfl, hEqWj⟩

/-- Helper for Lemma 6.29.3: the projection pullback of the stage pullback `g⁻¹(U_i)` agrees with
the original limit pullback `p_i⁻¹(U_i)`. This is the set-theoretic normalization needed before
descending the finite common-stage cover to an actual stage cover. -/
private theorem projection_preimage_open_stage_pullback_eq
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (g : j ⟶ i) (Ui : CompactOpens (F.obj i)) :
    projection_preimage_open (F := F)
        ⟨j, stage_pullback_compact_open (F := F) hF g Ui⟩ =
      (Opens.map (limit.π F i)).obj Ui.toOpens := by
  ext x
  constructor
  · intro hx
    have hx' : F.map g ((limit.π F j) x) ∈ (Ui : Set (F.obj i)) := by
      simpa [projection_preimage_open, projection_preimage_basis, stage_pullback_compact_open]
        using hx
    change (limit.π F i) x ∈ (Ui : Set (F.obj i))
    have hπ : F.map g ((limit.π F j) x) = (limit.π F i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F g)) x
    simpa [hπ] using hx'
  · intro hx
    have hx' : (limit.π F i) x ∈ (Ui : Set (F.obj i)) := by
      simpa using hx
    change F.map g ((limit.π F j) x) ∈ (Ui : Set (F.obj i))
    have hπ : F.map g ((limit.π F j) x) = (limit.π F i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F g)) x
    simpa [projection_preimage_open, projection_preimage_basis, stage_pullback_compact_open, hπ]
      using hx'

/-- Helper for Lemma 6.29.3: once the local compact opens have been materialized on one common
stage `j`, Lemma `5.24.6 (3)` turns their limit-side cover of `p_i⁻¹(U_i)` into a genuine finite
cover of `g⁻¹(U_i)` after refining to one stage over `j`. -/
private theorem common_stage_transport_family_refines_to_stage_cover
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (Ui : CompactOpens (F.obj i))
    (t : Finset (LocalStageSectionDatum (F := F) i 𝒢))
    (htCover :
      (((Opens.map (limit.π F i)).obj Ui.toOpens : Opens ↥(limit F)) : Set ↥(limit F)) ⊆
        ⋃ q ∈ t, projection_preimage_basis (F := F) ⟨q.1, q.2.1⟩)
    {j : I} {g : j ⟶ i}
    (W : {q // q ∈ t} → CompactOpens (F.obj j))
    (hW :
      ∀ q : {q // q ∈ t},
        projection_preimage_open (F := F) ⟨j, W q⟩ =
            projection_preimage_open (F := F) ⟨q.1.1, q.1.2.1⟩ ∧
          projection_preimage_open (F := F) ⟨j, W q⟩ ≤
            (Opens.map (limit.π F i)).obj Ui.toOpens) :
    (limit.π F j) ⁻¹'
        ((stage_pullback_compact_open (F := F) hF g Ui : CompactOpens (F.obj j)) :
          Set (F.obj j)) =
      ⋃ q : {q // q ∈ t}, (limit.π F j) ⁻¹' (W q : Set (F.obj j)) ∧
    ∃ (k : I) (b : k ⟶ j),
      (F.map b) ⁻¹'
          ((stage_pullback_compact_open (F := F) hF g Ui : CompactOpens (F.obj j)) :
            Set (F.obj j)) =
        ⋃ q : {q // q ∈ t}, (F.map b) ⁻¹' (W q : Set (F.obj j)) := by
  classical
  have hF' : ∀ ⦃i' j' : I⦄ (a : j' ⟶ i'), IsSpectralMap (F.map a) := fun {_ _} a ↦ hF a
  have hLimitCover :
      (limit.π F j) ⁻¹'
          ((stage_pullback_compact_open (F := F) hF g Ui : CompactOpens (F.obj j)) :
            Set (F.obj j)) =
        ⋃ q : {q // q ∈ t}, (limit.π F j) ⁻¹' (W q : Set (F.obj j)) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      have hxOpen :
          x ∈ projection_preimage_open (F := F)
            ⟨j, stage_pullback_compact_open (F := F) hF g Ui⟩ := by
        simpa [projection_preimage_open, projection_preimage_basis] using hx
      have hxUi : x ∈ (Opens.map (limit.π F i)).obj Ui.toOpens := by
        simpa [projection_preimage_open_stage_pullback_eq (F := F) hF g Ui] using hxOpen
      rcases Set.mem_iUnion₂.mp (htCover hxUi) with ⟨q, hq, hxq⟩
      let q' : {q // q ∈ t} := ⟨q, hq⟩
      refine Set.mem_iUnion.mpr ⟨q', ?_⟩
      have hxq' : x ∈ projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ := by
        simpa [projection_preimage_open, projection_preimage_basis] using hxq
      have hxW : x ∈ projection_preimage_open (F := F) ⟨j, W q'⟩ := by
        simpa [(hW q').1] using hxq'
      simpa [projection_preimage_open, projection_preimage_basis] using hxW
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
      have hxW : x ∈ projection_preimage_open (F := F) ⟨j, W q⟩ := by
        simpa [projection_preimage_open, projection_preimage_basis] using hxq
      have hxUi : x ∈ (Opens.map (limit.π F i)).obj Ui.toOpens := (hW q).2 hxW
      have hxOpen :
          x ∈ projection_preimage_open (F := F)
            ⟨j, stage_pullback_compact_open (F := F) hF g Ui⟩ := by
        simpa [projection_preimage_open_stage_pullback_eq (F := F) hF g Ui] using hxUi
      simpa [projection_preimage_open, projection_preimage_basis] using hxOpen
  obtain ⟨k, b, hb⟩ :=
    exists_stage_of_preimage_eq_iUnion
      (F := F) hF' (i := j)
      (Ui := stage_pullback_compact_open (F := F) hF g Ui)
      (V := W) hLimitCover
  exact ⟨hLimitCover, k, b, hb⟩

/-- Helper for Lemma 6.29.3: if one common-stage local comparison is known on a compact open
`W_j ⊆ X_j`, then restricting along any refinement arrow `b : k ⟶ j` produces the corresponding
comparison on the pulled-back compact open `b⁻¹(W_j) ⊆ X_k`. This isolates the stage-`k`
normalization step from the later finite overlap-refinement and gluing package. -/
private theorem common_stage_section_refines_limit_side_equality
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    {j : I} {g : j ⟶ i} (q : LocalStageSectionDatum (F := F) i 𝒢)
    (Wj : CompactOpens (F.obj j))
    (hWjU : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
      (Opens.map (limit.π F i)).obj U)
    (hWjV : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
      (Opens.map (limit.π F i)).obj q.2.2.1.toOpens)
    (hWjVi : Wj.toOpens ≤ (Opens.map (F.map g)).obj q.2.2.1.toOpens)
    (hEqWj :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjU).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjV).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2))
    {k : I} (b : k ⟶ j) :
    let Wk := stage_pullback_compact_open (F := F) hF b Wj
    ∃ hWkU : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
        (Opens.map (limit.π F i)).obj U,
      ∃ hWkV : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
          (Opens.map (limit.π F i)).obj q.2.2.1.toOpens,
        ∃ hWkVi : Wk.toOpens ≤ (Opens.map (F.map (b ≫ g))).obj q.2.2.1.toOpens,
          ∃ τk : ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).obj (op Wk.toOpens),
            τk =
              ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).map (homOfLE hWkVi).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map (b ≫ g))).unit.app
                    𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) ∧
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s =
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
  let Wk : CompactOpens (F.obj k) := stage_pullback_compact_open (F := F) hF b Wj
  have hWkEq :
      projection_preimage_open (F := F) ⟨k, Wk⟩ =
        projection_preimage_open (F := F) ⟨j, Wj⟩ := by
    ext x
    constructor
    · intro hx
      have hx' : F.map b ((limit.π F k) x) ∈ (Wj : Set (F.obj j)) := by
        simpa [projection_preimage_open, projection_preimage_basis, Wk, stage_pullback_compact_open]
          using hx
      have hπ : F.map b ((limit.π F k) x) = (limit.π F j) x := by
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F b)) x
      change (limit.π F j) x ∈ (Wj : Set (F.obj j))
      simpa [projection_preimage_open, projection_preimage_basis, hπ] using hx'
    · intro hx
      have hx' : (limit.π F j) x ∈ (Wj : Set (F.obj j)) := by
        simpa [projection_preimage_open, projection_preimage_basis] using hx
      change F.map b ((limit.π F k) x) ∈ (Wj : Set (F.obj j))
      have hπ : F.map b ((limit.π F k) x) = (limit.π F j) x := by
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F b)) x
      simpa [projection_preimage_open, projection_preimage_basis, Wk, stage_pullback_compact_open,
        hπ] using hx'
  have hWkU :
      projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
        (Opens.map (limit.π F i)).obj U :=
    le_trans hWkEq.le hWjU
  have hWkV :
      projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
        (Opens.map (limit.π F i)).obj q.2.2.1.toOpens :=
    le_trans hWkEq.le hWjV
  have hWkVi :
      Wk.toOpens ≤ (Opens.map (F.map (b ≫ g))).obj q.2.2.1.toOpens := by
    intro x hx
    have hxWj : F.map b x ∈ (Wj : Set (F.obj j)) := by
      simpa [Wk, stage_pullback_compact_open] using hx
    have hxVi : F.map g (F.map b x) ∈ (q.2.2.1 : Set (F.obj i)) := hWjVi hxWj
    change F.map (b ≫ g) x ∈ (q.2.2.1 : Set (F.obj i))
    simpa [Functor.map_comp] using hxVi
  let τk : ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).obj (op Wk.toOpens) :=
    ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).map (homOfLE hWkVi).op
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map (b ≫ g))).unit.app 𝒢).1.app
          (op q.2.2.1.toOpens)) q.2.2.2)
  have hEqWk :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
    -- Restrict the known limit-side equality from `p_j⁻¹(W_j)` to the refined neighborhood
    -- `p_k⁻¹(b⁻¹(W_j))`.
    calc
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkEq.le).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjU).op s) := by
              have hop :
                  (homOfLE hWjU).op ≫ (homOfLE hWkEq.le).op = (homOfLE hWkU).op := by
                apply Subsingleton.elim
              simpa [Functor.map_comp] using
                congrArg
                  (fun f :
                    op ((Opens.map (limit.π F i)).obj U) ⟶
                      op (projection_preimage_open (F := F) ⟨k, Wk⟩) ↦
                    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
                  hop.symm
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkEq.le).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjV).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2)) := by
                    simpa using congrArg
                      (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkEq.le).op)
                      hEqWj
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
              have hop :
                  (homOfLE hWjV).op ≫ (homOfLE hWkEq.le).op = (homOfLE hWkV).op := by
                apply Subsingleton.elim
              simpa [Functor.map_comp] using
                congrArg
                  (fun f :
                    op ((Opens.map (limit.π F i)).obj q.2.2.1.toOpens) ⟶
                      op (projection_preimage_open (F := F) ⟨k, Wk⟩) ↦
                    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f
                      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                          𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2))
                  hop
  refine ⟨hWkU, hWkV, hWkVi, τk, rfl, hEqWk⟩

/-- Helper for Lemma 6.29.3: once the finite common-stage family is chosen on actual compact opens
`W q ⊆ X_j`, restricting along the cover-refinement arrow `b : k ⟶ j` produces the corresponding
stage-`k` local section data on the concrete cover pieces used by `hbCover`. -/
private theorem descended_common_stage_section_limit_image_eq_restriction
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    {j : I} {g : j ⟶ i} (q : LocalStageSectionDatum (F := F) i 𝒢)
    (Wj : CompactOpens (F.obj j))
    (hW :
      CommonStageLocalSectionOn (F := F) 𝒢 U s q (g := g) Wj)
    {k : I} (b : k ⟶ j) :
    let Wk := stage_pullback_compact_open (F := F) hF b Wj
    ∃ hWkU : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
        (Opens.map (limit.π F i)).obj U,
      ∃ hWkV : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
          (Opens.map (limit.π F i)).obj q.2.2.1.toOpens,
        ∃ hWkVi : Wk.toOpens ≤ (Opens.map (F.map (b ≫ g))).obj q.2.2.1.toOpens,
          ∃ τk : ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).obj (op Wk.toOpens),
            τk =
              ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).map (homOfLE hWkVi).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map (b ≫ g))).unit.app
                    𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) ∧
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s =
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
  rcases hW with ⟨_, hWjU, hWjV, hWjVi, _, _, hEqWj⟩
  -- The alignment theorem now applies to the actual cover piece `Wj`.
  simpa using
    (common_stage_section_refines_limit_side_equality
      (F := F) hF 𝒢 U s q Wj hWjU hWjV hWjVi hEqWj (b := b))

/-- Helper for Lemma 6.29.3: if two local pullback-unit representatives both restrict to the same
limit section `s`, then the two corresponding limit-side unit sections agree on the overlap. This
isolates the overlap normalization on the limit side before the final stage-refinement step turns
that equality into an equality of stage sections. -/
private theorem overlap_limit_unit_sections_eq_of_common_restriction
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    {k : I} (W₁ W₂ : CompactOpens (F.obj k))
    {V₁ V₂ : CompactOpens (F.obj i)}
    (σ₁ : 𝒢.1.obj (op V₁.toOpens)) (σ₂ : 𝒢.1.obj (op V₂.toOpens))
    (hW₁U : projection_preimage_open (F := F) ⟨k, W₁⟩ ≤
      (Opens.map (limit.π F i)).obj U)
    (hW₂U : projection_preimage_open (F := F) ⟨k, W₂⟩ ≤
      (Opens.map (limit.π F i)).obj U)
    (hW₁V : projection_preimage_open (F := F) ⟨k, W₁⟩ ≤
      (Opens.map (limit.π F i)).obj V₁.toOpens)
    (hW₂V : projection_preimage_open (F := F) ⟨k, W₂⟩ ≤
      (Opens.map (limit.π F i)).obj V₂.toOpens)
    (hEq₁ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁U).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁V).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₁.toOpens)) σ₁))
    (hEq₂ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂U).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂V).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₂.toOpens)) σ₂)) :
    ∃ V : Opens ↥(limit F),
      ∃ hV₁ : V ≤ projection_preimage_open (F := F) ⟨k, W₁⟩,
        ∃ hV₂ : V ≤ projection_preimage_open (F := F) ⟨k, W₂⟩,
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₁ hW₁V)).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app (op V₁.toOpens)) σ₁) =
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₂ hW₂V)).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app (op V₂.toOpens)) σ₂) := by
  let V : Opens ↥(limit F) :=
    projection_preimage_open (F := F) ⟨k, W₁⟩ ⊓
      projection_preimage_open (F := F) ⟨k, W₂⟩
  have hV₁ : V ≤ projection_preimage_open (F := F) ⟨k, W₁⟩ := inf_le_left
  have hV₂ : V ≤ projection_preimage_open (F := F) ⟨k, W₂⟩ := inf_le_right
  have hLeft₁ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hV₁).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁U).op s) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₁ hW₁U)).op s := by
    have hop :
        (homOfLE hW₁U).op ≫ (homOfLE hV₁).op =
          (homOfLE (le_trans hV₁ hW₁U)).op := by
      apply Subsingleton.elim
    simpa [Functor.map_comp] using
      congrArg
        (fun f :
          op ((Opens.map (limit.π F i)).obj U) ⟶
            op V ↦
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
        hop
  have hRight₁ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hV₁).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁V).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₁.toOpens)) σ₁)) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₁ hW₁V)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₁.toOpens)) σ₁) := by
    have hop :
        (homOfLE hW₁V).op ≫ (homOfLE hV₁).op =
          (homOfLE (le_trans hV₁ hW₁V)).op := by
      apply Subsingleton.elim
    simpa [Functor.map_comp] using
      congrArg
        (fun f :
          op ((Opens.map (limit.π F i)).obj V₁.toOpens) ⟶
            op V ↦
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₁.toOpens)) σ₁))
        hop
  have hLeft₂ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hV₂).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂U).op s) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₂ hW₂U)).op s := by
    have hop :
        (homOfLE hW₂U).op ≫ (homOfLE hV₂).op =
          (homOfLE (le_trans hV₂ hW₂U)).op := by
      apply Subsingleton.elim
    simpa [Functor.map_comp] using
      congrArg
        (fun f :
          op ((Opens.map (limit.π F i)).obj U) ⟶
            op V ↦
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
        hop
  have hRight₂ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hV₂).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂V).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₂.toOpens)) σ₂)) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₂ hW₂V)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₂.toOpens)) σ₂) := by
    have hop :
        (homOfLE hW₂V).op ≫ (homOfLE hV₂).op =
          (homOfLE (le_trans hV₂ hW₂V)).op := by
      apply Subsingleton.elim
    simpa [Functor.map_comp] using
      congrArg
        (fun f :
          op ((Opens.map (limit.π F i)).obj V₂.toOpens) ⟶
            op V ↦
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₂.toOpens)) σ₂))
        hop
  have hUnit₁ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₁ hW₁U)).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₁ hW₁V)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₁.toOpens)) σ₁) := by
    -- Restrict the first local equality from `p_k⁻¹(W₁)` to the overlap open.
    calc
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₁ hW₁U)).op s =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hV₁).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁U).op s) := by
              simpa using hLeft₁.symm
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hV₁).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁V).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app (op V₁.toOpens)) σ₁)) := by
                    simpa using congrArg
                      (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hV₁).op)
                      hEq₁
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₁ hW₁V)).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₁.toOpens)) σ₁) := by
                  simpa using hRight₁
  have hUnit₂ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₂ hW₂U)).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₂ hW₂V)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₂.toOpens)) σ₂) := by
    -- The same restriction argument applies to the second local equality.
    calc
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₂ hW₂U)).op s =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hV₂).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂U).op s) := by
              simpa using hLeft₂.symm
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hV₂).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂V).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app (op V₂.toOpens)) σ₂)) := by
                    simpa using congrArg
                      (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hV₂).op)
                      hEq₂
      _ =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₂ hW₂V)).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₂.toOpens)) σ₂) := by
                  simpa using hRight₂
  have hCommon :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₁ hW₁U)).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE (le_trans hV₂ hW₂U)).op s := by
    -- Both routes are restrictions of the same global section `s` to the same overlap open.
    have hop :
        (homOfLE (le_trans hV₁ hW₁U)).op =
          (homOfLE (le_trans hV₂ hW₂U)).op := by
      apply Subsingleton.elim
    simpa using
      congrArg
        (fun f :
          op ((Opens.map (limit.π F i)).obj U) ⟶
            op V ↦
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
        hop
  -- Compare both overlap restrictions through the common restriction of `s`.
  exact ⟨V, hV₁, hV₂, hUnit₁.symm.trans (hCommon.trans hUnit₂)⟩

/-- Helper for Lemma 6.29.3: the stage-cover equality `hbCover` is exactly the statement that the
pulled-back compact open `(b ≫ g)⁻¹(U_i)` is covered by the concrete stage-`k` compact opens
`b⁻¹(W_q)`. This normalizes the set-theoretic cover into the `CompactOpens` language used by the
final gluing step. -/
private theorem stage_pullback_compact_open_cover_eq
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j k : I} (g : j ⟶ i) (Ui : CompactOpens (F.obj i))
    {α : Type*} (W : α → CompactOpens (F.obj j)) (b : k ⟶ j)
    (hbCover :
      (F.map b) ⁻¹'
          ((stage_pullback_compact_open (F := F) hF g Ui : CompactOpens (F.obj j)) :
            Set (F.obj j)) =
        ⋃ a : α, (F.map b) ⁻¹' (W a : Set (F.obj j))) :
    ((stage_pullback_compact_open (F := F) hF (b ≫ g) Ui : CompactOpens (F.obj k)) :
        Set (F.obj k)) =
      ⋃ a : α, ((stage_pullback_compact_open (F := F) hF b (W a) :
        CompactOpens (F.obj k)) : Set (F.obj k)) := by
  ext x
  simpa [stage_pullback_compact_open, Functor.map_comp] using
    congrArg (fun s : Set (F.obj k) ↦ x ∈ s) hbCover

/-- Helper for Lemma 6.29.3: the pullback of the exact overlap `W₁ ⊓ W₂` to the limit space is
the intersection of the two corresponding projection-basis opens. This keeps the final overlap
comparison on the concrete compact-open overlap rather than on an arbitrary auxiliary open. -/
private theorem projection_preimage_open_inf
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {k : I} (W₁ W₂ : CompactOpens (F.obj k)) :
    projection_preimage_open (F := F) ⟨k, W₁ ⊓ W₂⟩ =
      projection_preimage_open (F := F) ⟨k, W₁⟩ ⊓
        projection_preimage_open (F := F) ⟨k, W₂⟩ := by
  ext x
  simpa [projection_preimage_open, projection_preimage_basis]

/-- Helper for Lemma 6.29.3: if two local pullback-unit representatives both restrict to the same
global limit section on `p_k⁻¹(W₁)` and `p_k⁻¹(W₂)`, then the corresponding limit-side unit
sections agree on the exact overlap `p_k⁻¹(W₁ ⊓ W₂)`. This removes the old arbitrary-open
packaging and isolates the precise overlap equality used in the final refinement step. -/
private theorem exact_overlap_limit_unit_sections_eq
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    {k : I} (W₁ W₂ : CompactOpens (F.obj k))
    {V₁ V₂ : CompactOpens (F.obj i)}
    (σ₁ : 𝒢.1.obj (op V₁.toOpens)) (σ₂ : 𝒢.1.obj (op V₂.toOpens))
    (hW₁U : projection_preimage_open (F := F) ⟨k, W₁⟩ ≤
      (Opens.map (limit.π F i)).obj U)
    (hW₂U : projection_preimage_open (F := F) ⟨k, W₂⟩ ≤
      (Opens.map (limit.π F i)).obj U)
    (hW₁V : projection_preimage_open (F := F) ⟨k, W₁⟩ ≤
      (Opens.map (limit.π F i)).obj V₁.toOpens)
    (hW₂V : projection_preimage_open (F := F) ⟨k, W₂⟩ ≤
      (Opens.map (limit.π F i)).obj V₂.toOpens)
    (hEq₁ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁U).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁V).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₁.toOpens)) σ₁))
    (hEq₂ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂U).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂V).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₂.toOpens)) σ₂)) :
    ∃ hR₁ : projection_preimage_open (F := F) ⟨k, W₁ ⊓ W₂⟩ ≤
        projection_preimage_open (F := F) ⟨k, W₁⟩,
      ∃ hR₂ : projection_preimage_open (F := F) ⟨k, W₁ ⊓ W₂⟩ ≤
          projection_preimage_open (F := F) ⟨k, W₂⟩,
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
            (homOfLE (le_trans hR₁ hW₁V)).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₁.toOpens)) σ₁) =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
            (homOfLE (le_trans hR₂ hW₂V)).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₂.toOpens)) σ₂) := by
  let R : Opens ↥(limit F) := projection_preimage_open (F := F) ⟨k, W₁ ⊓ W₂⟩
  have hR₁ : R ≤ projection_preimage_open (F := F) ⟨k, W₁⟩ := by
    -- Rewrite the exact overlap as an infimum and project to the left factor pointwise.
    intro x hx
    have hx' :
        x ∈ projection_preimage_open (F := F) ⟨k, W₁⟩ ⊓
            projection_preimage_open (F := F) ⟨k, W₂⟩ := by
      simpa [R, projection_preimage_open_inf (F := F) W₁ W₂] using hx
    exact hx'.1
  have hR₂ : R ≤ projection_preimage_open (F := F) ⟨k, W₂⟩ := by
    -- The same exact-overlap rewrite gives the right inclusion pointwise.
    intro x hx
    have hx' :
        x ∈ projection_preimage_open (F := F) ⟨k, W₁⟩ ⊓
            projection_preimage_open (F := F) ⟨k, W₂⟩ := by
      simpa [R, projection_preimage_open_inf (F := F) W₁ W₂] using hx
    exact hx'.2
  have hLeft₁ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₁).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁U).op s) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₁ hW₁U)).op s := by
    have hop :
        (homOfLE hW₁U).op ≫ (homOfLE hR₁).op =
          (homOfLE (le_trans hR₁ hW₁U)).op := by
      apply Subsingleton.elim
    simpa [Functor.map_comp] using
      congrArg
        (fun f :
          op ((Opens.map (limit.π F i)).obj U) ⟶ op R ↦
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
        hop
  have hRight₁ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₁).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁V).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₁.toOpens)) σ₁)) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₁ hW₁V)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₁.toOpens)) σ₁) := by
    have hop :
        (homOfLE hW₁V).op ≫ (homOfLE hR₁).op =
          (homOfLE (le_trans hR₁ hW₁V)).op := by
      apply Subsingleton.elim
    simpa [Functor.map_comp] using
      congrArg
        (fun f :
          op ((Opens.map (limit.π F i)).obj V₁.toOpens) ⟶ op R ↦
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app (op V₁.toOpens)) σ₁))
        hop
  have hLeft₂ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₂).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂U).op s) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₂ hW₂U)).op s := by
    have hop :
        (homOfLE hW₂U).op ≫ (homOfLE hR₂).op =
          (homOfLE (le_trans hR₂ hW₂U)).op := by
      apply Subsingleton.elim
    simpa [Functor.map_comp] using
      congrArg
        (fun f :
          op ((Opens.map (limit.π F i)).obj U) ⟶ op R ↦
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
        hop
  have hRight₂ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₂).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂V).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₂.toOpens)) σ₂)) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₂ hW₂V)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₂.toOpens)) σ₂) := by
    have hop :
        (homOfLE hW₂V).op ≫ (homOfLE hR₂).op =
          (homOfLE (le_trans hR₂ hW₂V)).op := by
      apply Subsingleton.elim
    simpa [Functor.map_comp] using
      congrArg
        (fun f :
          op ((Opens.map (limit.π F i)).obj V₂.toOpens) ⟶ op R ↦
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app (op V₂.toOpens)) σ₂))
        hop
  have hUnit₁ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₁ hW₁U)).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₁ hW₁V)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₁.toOpens)) σ₁) := by
    -- Restrict the first local equality from `p_k⁻¹(W₁)` to the exact overlap open.
    calc
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₁ hW₁U)).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₁).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁U).op s) := by
            simpa using hLeft₁.symm
      _ =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₁).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁V).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₁.toOpens)) σ₁)) := by
                  simpa using congrArg
                    (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₁).op)
                    hEq₁
      _ =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₁ hW₁V)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₁.toOpens)) σ₁) := by
                simpa using hRight₁
  have hUnit₂ :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₂ hW₂U)).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₂ hW₂V)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₂.toOpens)) σ₂) := by
    -- The same restriction argument works for the second local equality.
    calc
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₂ hW₂U)).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₂).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂U).op s) := by
            simpa using hLeft₂.symm
      _ =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₂).op
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂V).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₂.toOpens)) σ₂)) := by
                  simpa using congrArg
                    (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₂).op)
                    hEq₂
      _ =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₂ hW₂V)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V₂.toOpens)) σ₂) := by
                simpa using hRight₂
  have hCommon :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₁ hW₁U)).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (le_trans hR₂ hW₂U)).op s := by
    have hop :
        (homOfLE (le_trans hR₁ hW₁U)).op =
          (homOfLE (le_trans hR₂ hW₂U)).op := by
      apply Subsingleton.elim
    simpa using
      congrArg
        (fun f :
          op ((Opens.map (limit.π F i)).obj U) ⟶ op R ↦
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map f s)
        hop
  exact ⟨hR₁, hR₂, hUnit₁.symm.trans (hCommon.trans hUnit₂)⟩

/-- Helper for Lemma 6.29.3: successive restrictions of a sheaf section compose to the single
restriction along the composite inclusion. This is the rewrite-friendly restriction normal form
used to expose both the exact overlap equality on the limit side and the corresponding restricted
stage sections on the source side. -/
private theorem sheaf_section_restriction_comp_eq
    {X : TopCat.{u}} (ℱ : X.Sheaf (Type u))
    {V W R : Opens X} (hWV : W ≤ V) (hRW : R ≤ W) (σ : ℱ.1.obj (op V)) :
    ℱ.1.map (homOfLE hRW).op (ℱ.1.map (homOfLE hWV).op σ) =
      ℱ.1.map (homOfLE (le_trans hRW hWV)).op σ := by
  -- The two restriction routes are the same arrow in the opens category.
  have hop :
      (homOfLE hWV).op ≫ (homOfLE hRW).op =
        (homOfLE (le_trans hRW hWV)).op := by
    apply Subsingleton.elim
  simpa [Functor.map_comp] using
    congrArg
      (fun f : op V ⟶ op R ↦ ℱ.1.map f σ)
      hop

/-- Helper for Lemma 6.29.3: the exact-overlap term in `hOverlapExact` is exactly the restriction
of the already-known limit-side pullback-unit image on `p_k^{-1}(W₁)`. This isolates the limit
half of the missing overlap normalization in a reusable one-line rewrite. -/
private theorem pullback_unit_restriction_limit_image_eq
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i k : I} (𝒢 : (F.obj i).Sheaf (Type u)) {V : Opens (F.obj i)}
    {W₁ R : CompactOpens (F.obj k)} (σ : 𝒢.1.obj (op V))
    (hW₁V : projection_preimage_open (F := F) ⟨k, W₁⟩ ≤
      (Opens.map (limit.π F i)).obj V)
    (hR₁ : projection_preimage_open (F := F) ⟨k, R⟩ ≤
      projection_preimage_open (F := F) ⟨k, W₁⟩) :
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
        (homOfLE (le_trans hR₁ hW₁V)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
            (op V)) σ) =
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₁).op
        (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁V).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
              (op V)) σ)) := by
  -- Rewrite the single restriction to the overlap as two successive restrictions.
  simpa using
    (sheaf_section_restriction_comp_eq
      (ℱ := ((limit.π F i)⁻¹).obj 𝒢)
      (hWV := hW₁V) (hRW := hR₁)
      (σ := ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
        (op V)) σ))).symm

/-- Helper for Lemma 6.29.3: the section map induced by `TopCat.Sheaf.pullbackComp` commutes with
restriction to smaller opens. This is the restriction-half of the remaining overlap-transport
bridge from nested limit pullbacks to the collapsed limit pullback used in the final gluing step.
-/
private theorem pullbackComp_hom_restriction_eq
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (𝒢 : Z.Sheaf (Type u))
    {W R : Opens X} (hRW : R ≤ W)
    (σ :
      ((((f⁻¹).obj ((g⁻¹).obj 𝒢)).presheaf).obj
        (op W))) :
    (((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1.app (op R))
        (((((f⁻¹).obj ((g⁻¹).obj 𝒢)).presheaf).map (homOfLE hRW).op) σ) =
      (((((f ≫ g)⁻¹).obj 𝒢).presheaf).map (homOfLE hRW).op)
        ((((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1.app
          (op W)) σ) := by
  -- Evaluate naturality of the pullback-composition comparison on the chosen restricted section.
  simpa [TopologicalSpace.Opens.map_homOfLE, ConcreteCategory.comp_apply] using
    (NatTrans.naturality_apply
      (((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1)
      (homOfLE hRW).op σ)

/-- Helper for Lemma 6.29.3: on every open, the section map induced by
`TopCat.Sheaf.pullbackComp` is injective. This is the final owner-side input needed to turn the
collapsed overlap equality on the limit into an equality in the nested pullback source expected by
`common_refinement_of_equal_limit_pullback_sections`. -/
private theorem pullbackComp_hom_app_injective
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (𝒢 : Z.Sheaf (Type u))
    (W : Opens X) :
    Function.Injective
      ((((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1.app (op W))) := by
  let e := (TopCat.Sheaf.pullbackComp (A := Type u) f g).app 𝒢
  intro s t hst
  -- Apply the inverse component of `pullbackComp` on the same open to cancel the comparison.
  have hInv :=
    congrArg ((e.inv).1.app (op W)) hst
  have hs :
      (e.inv).1.app (op W) ((e.hom).1.app (op W) s) = s := by
    simpa [e, ConcreteCategory.comp_apply] using
      congrArg (fun m ↦ (m.1.app (op W)) s) e.hom_inv_id
  have ht :
      (e.inv).1.app (op W) ((e.hom).1.app (op W) t) = t := by
    simpa [e, ConcreteCategory.comp_apply] using
      congrArg (fun m ↦ (m.1.app (op W)) t) e.hom_inv_id
  exact hs.symm.trans (hInv.trans ht)

/-- Helper for Lemma 6.29.3: if two maps `f, g : X ⟶ Y` are equal, then restricting a section of
`f⁻¹ 𝒢` and transporting it across the induced pullback cast is the same as first transporting the
section and then restricting it on the `g`-pullback side. This is the cast bridge needed when the
raw `pullbackComp` overlap equality is rewritten into the reassociated family indexed by
`F.map (c ≫ b ≫ g)`. -/
private theorem pullback_section_restriction_cast_eq_of_hom_eq
    {X Y : TopCat.{u}} {f g : X ⟶ Y} (hfg : f = g) (𝒢 : Y.Sheaf (Type u))
    {W R : Opens X} (i : R ⟶ W)
    (σ : (((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj (op W)) :
    (((TopCat.Sheaf.pullback (Type u) g).obj 𝒢).presheaf).map i.op
        (cast (by cases hfg; rfl) σ) =
      cast (by cases hfg; rfl)
        ((((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).map i.op σ) := by
  -- After replacing `g` by `f`, both the outer restriction map and the casts are definitional.
  cases hfg
  rfl

/-- Restricting a presheaf section after transporting it across an equality of source opens is
the same as restricting before the transport. This isolates the proof-relevant `homOfLE` noise
that appears when two inverse-image opens are equal by a limit-cone identity. -/
private theorem presheaf_restrict_cast_source_eq
    {X : TopCat.{u}} (P : TopCat.Presheaf (Type u) X)
    {R W W' : Opens X} (hWW' : W = W') (hRW : R ≤ W) (hRW' : R ≤ W')
    (s : P.obj (op W)) :
    P.map (homOfLE hRW').op (cast (by rw [hWW']) s) =
      P.map (homOfLE hRW).op s := by
  subst hWW'
  congr 1

/-- Helper for Lemma 6.29.3: if two maps are equal, then the corresponding pullback-unit sections
on a fixed open agree after transporting across the induced pullback cast. This is the primitive
source-open cast normalization used before restricting the composite pullback-unit section. -/
private theorem pullback_unit_app_cast_eq_of_hom_eq
    {X Y : TopCat.{u}} {f g : X ⟶ Y} (hfg : f = g) (𝒢 : Y.Sheaf (Type u))
    {V : Opens Y} (σ : 𝒢.1.obj (op V)) :
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
        (op V)) σ) =
      cast
        (by
          cases hfg
          rfl)
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app 𝒢).1.app
            (op V)) σ) := by
  -- Once the pullback maps are identified, the unit section is definitionally the same.
  cases hfg
  rfl

/-- Helper for Lemma 6.29.3: if two maps are equal, then restricting the pullback-unit section
for one map agrees with restricting the pullback-unit section for the other map after transporting
across the induced pullback cast on the smaller source open. This packages the exact
restriction-plus-unit normalization used later at the limit projection. -/
private theorem pullback_unit_restriction_eq_of_hom_eq
    {X Y : TopCat.{u}} {f g : X ⟶ Y} (hfg : f = g) (𝒢 : Y.Sheaf (Type u))
    {R : Opens X} {V : Opens Y} (σ : 𝒢.1.obj (op V))
    (hRV : R ≤ (Opens.map f).obj V) :
    (((g⁻¹).obj 𝒢).presheaf).map
        (homOfLE (by
          simpa [hfg] using hRV)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app 𝒢).1.app
            (op V)) σ) =
      cast
        (by
          cases hfg
          rfl)
        (((((f⁻¹).obj 𝒢).presheaf).map
            (homOfLE hRV).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
                (op V)) σ))) := by
  -- Once the two pullback maps are identified, both the restriction morphism and the pulled-back
  -- unit section become definitionally the same.
  cases hfg
  rfl

/-- Helper for Lemma 6.29.3: the generic restriction/cast transport can be specialized to the
comparison `limit.π F k ≫ F.map h = limit.π F i`. This packages the exact limit-side cast bridge
used when a collapsed overlap section is rewritten from the composite pullback to the direct
`p_i`-pullback. -/
private theorem limit_pullback_section_restriction_cast_eq
    {i k : I} (h : k ⟶ i) (𝒢 : (F.obj i).Sheaf (Type u))
    {W R : Opens ↥(limit F)} (iRW : R ⟶ W)
    (σ : (((TopCat.Sheaf.pullback (Type u) (limit.π F k ≫ F.map h)).obj 𝒢).presheaf).obj (op W)) :
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map iRW.op
        (cast
          (by
            simpa using
              congrArg
                (fun f : limit F ⟶ F.obj i ↦
                  (((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj (op W))
                (limit.w F h))
          σ) =
      cast
        (by
          simpa using
            congrArg
              (fun f : limit F ⟶ F.obj i ↦
                (((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj (op R))
              (limit.w F h))
        ((((TopCat.Sheaf.pullback (Type u) (limit.π F k ≫ F.map h)).obj 𝒢).presheaf).map
          iRW.op σ) := by
  -- This is the generic restriction/cast commute lemma specialized to the limit comparison.
  exact
    pullback_section_restriction_cast_eq_of_hom_eq
      (hfg := by simpa using limit.w F h)
      (𝒢 := 𝒢) (i := iRW) (σ := σ)

/-- Helper for Lemma 6.29.3: the section-level transport in
`inverseImageSectionValue_comp (f, 𝟙)` is definitional. This removes the last cast in the
identity-over-stage normalization. -/
private theorem inverseImageSectionValue_comp_right_id {X Y : TopCat.{u}} (f : X ⟶ Y)
    (ℱ : Y.Sheaf (Type u)) (U : Opens Y) :
    inverseImageSectionValue_comp f (𝟙 Y) ℱ U = rfl := by
  exact Subsingleton.elim _ _

/-- Helper for Lemma 6.29.3: after lifting a section through the identity-pullback equivalence,
the iterated pullback comparison for `(f, 𝟙)` is exactly the ordinary pullback-unit section along
`f`. This is the transport-free core of the identity-over-stage adapter. -/
private theorem iteratedPullbackSectionsMap_identity_over_stage_eq_unit
    {X Y : TopCat.{u}} (f : X ⟶ Y) (ℋ : Y.Sheaf (Type u)) (U : Opens Y)
    (σ : ℋ.1.obj (op U)) :
    iteratedPullbackSectionsMap f (𝟙 Y) ℋ U
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 Y)).leftAdjointIdIso
            (eqToIso rfl)).inv.app ℋ).1.app (op U) σ) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℋ).1.app
          (op U)) σ) := by
  let α :
      TopCat.Sheaf.pullback (Type u) (𝟙 Y) ⋙ 𝟭 (TopCat.Sheaf (Type u) Y) ≅
        𝟭 (TopCat.Sheaf (Type u) Y) :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 Y)).leftAdjointIdIso
      (eqToIso rfl)
  -- Expand the iterated pullback map once and rewrite the comparison isomorphism into the
  -- right-unital form from `sheafPullbackComp_id_comp`.
  rw [iteratedPullbackSectionsMap, inverseImageSectionValue_comp_right_id]
  dsimp
  rw [sheafPullbackComp_id_comp]
  dsimp
  -- Naturality of the pullback unit across `α.hom` removes the identity-pullback transport.
  have hnat :=
    (Adjunction.unit_naturality
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
      (α.hom.app ℋ)).symm
  have happ :=
    congrArg
      (fun m ↦
        (m.1.app (op U))
          ((((α.inv.app ℋ).1.app (op U)) σ)))
      hnat
  dsimp at happ
  have hα :
      (((α.hom.app ℋ).1.app (op U))
          ((((α.inv.app ℋ).1.app (op U)) σ))) = σ := by
    simpa using
      congrArg
        (fun m ↦ (m.1.app (op U)) σ)
        (Iso.inv_hom_id_app α ℋ)
  -- Rewrite the whiskered/right-unital comparison to the plain pullback map so unit naturality can
  -- be read off directly on sections.
  change
    (((TopCat.Sheaf.pullback (Type u) f).map (α.hom.app ℋ)).1.app
        (op ((Opens.map f).obj U)))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
          ((TopCat.Sheaf.pullback (Type u) (𝟙 Y)).obj ℋ)).1.app
          (op U))
        ((((α.inv.app ℋ).1.app (op U)) σ))) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℋ).1.app
          (op U)) σ)
  have h1 :
      (((TopCat.Sheaf.pullback (Type u) f).map (α.hom.app ℋ)).1.app
          (op ((Opens.map f).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
            ((TopCat.Sheaf.pullback (Type u) (𝟙 Y)).obj ℋ)).1.app
            (op U))
          ((((α.inv.app ℋ).1.app (op U)) σ))) =
        (((TopCat.Sheaf.pushforward (Type u) f).map
            ((TopCat.Sheaf.pullback (Type u) f).map (α.hom.app ℋ))).1.app
          (op U))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
              ((TopCat.Sheaf.pullback (Type u) (𝟙 Y)).obj ℋ)).1.app
              (op U))
            ((((α.inv.app ℋ).1.app (op U)) σ))) := by
    rfl
  have h2 :
      (((TopCat.Sheaf.pushforward (Type u) f).map
          ((TopCat.Sheaf.pullback (Type u) f).map (α.hom.app ℋ))).1.app
        (op U))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
            ((TopCat.Sheaf.pullback (Type u) (𝟙 Y)).obj ℋ)).1.app
            (op U))
          ((((α.inv.app ℋ).1.app (op U)) σ))) =
        (((α.hom.app ℋ) ≫
            (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℋ).1.app
          (op U))
          ((((α.inv.app ℋ).1.app (op U)) σ)) := by
    simpa [ConcreteCategory.comp_apply] using happ.symm
  have h3 :
      (((α.hom.app ℋ) ≫
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℋ).1.app
        (op U))
        ((((α.inv.app ℋ).1.app (op U)) σ)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℋ).1.app
          (op U)) σ) := by
    simpa [ConcreteCategory.comp_apply] using
      congrArg
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℋ).1.app
            (op U)))
        hα
  exact h1.trans (h2.trans h3)

/-- Helper for Lemma 6.29.3: lifting a section on a stage through the identity object of `Over`
and then mapping it to the limit recovers the ordinary pullback-unit section on the limit. This is
the adapter needed to feed raw overlap sections into
`common_refinement_of_equal_limit_pullback_sections` at `Over.mk (𝟙 k)`. -/
theorem pullbackSectionsToLimitMap_identity_over_stage_eq_unit
    {k : I} (ℋ : (F.obj k).Sheaf (Type u)) (U0 : Opens (F.obj k))
    (σ : ℋ.1.obj (op U0)) :
    let σid :
        ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj U0)) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op U0) σ)
    pullbackSectionsToLimitMap F ℋ U0 (Over.mk (𝟙 k)) σid =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app ℋ).1.app
          (op U0)) σ) := by
  dsimp
  -- After `F.map (𝟙 k)` is simplified to the identity, the statement is exactly the core
  -- identity-over-stage transport computed above.
  let σraw :
      ((((𝟙 (F.obj k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (𝟙 (F.obj k))).obj U0)) :=
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
      (eqToIso rfl)).inv.app ℋ).1.app (op U0) σ)
  have hmap : F.map (𝟙 k) = 𝟙 (F.obj k) := by
    simp
  have hheq :
      iteratedPullbackSectionsMap (limit.π F k) (F.map (𝟙 k)) ℋ U0
          (cast (by simpa [hmap] using rfl) σraw) ≍
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app ℋ).1.app
            (op U0)) σ) := by
    exact
      (iterated_pullback_sections_map_heq_right
        (f := limit.π F k) (hg := hmap.symm) (𝒢 := ℋ) (U := U0) σraw).symm.trans
        (heq_of_eq
          (iteratedPullbackSectionsMap_identity_over_stage_eq_unit
            (f := limit.π F k) (ℋ := ℋ) (U := U0) (σ := σ)))
  simpa [pullbackSectionsToLimitMap, hmap, σraw, cast_eq_iff_heq] using hheq

/-- Helper for Lemma 6.29.3: refining the identity-over-stage lift of a raw section is exactly the
usual pullback-unit section of the refined raw section. This converts the output of
`common_refinement_of_equal_limit_pullback_sections` back to the raw refined overlap sections used
for sheaf gluing. -/
theorem overPullbackSectionsMap_identity_over_stage_eq_pullback_unit
    {k l : I} (c : l ⟶ k) (ℋ : (F.obj k).Sheaf (Type u)) (U0 : Opens (F.obj k))
    (σ : ℋ.1.obj (op U0)) :
    let σid :
        ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj U0)) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op U0) σ)
    overPullbackSectionsMap F ℋ U0
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) σid =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map c)).unit.app ℋ).1.app
          (op U0)) σ) := by
  dsimp
  -- Once the `Over`-morphism is unfolded, the refinement map is the same `(f, 𝟙)` comparison with
  -- `f = F.map c`.
  let σraw :
      ((((𝟙 (F.obj k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (𝟙 (F.obj k))).obj U0)) :=
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
      (eqToIso rfl)).inv.app ℋ).1.app (op U0) σ)
  have hmap : F.map (𝟙 k) = 𝟙 (F.obj k) := by
    simp
  have hheq :
      iteratedPullbackSectionsMap (F.map c) (F.map (𝟙 k)) ℋ U0
          (cast (by simpa [hmap] using rfl) σraw) ≍
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map c)).unit.app ℋ).1.app
            (op U0)) σ) := by
    exact
      (iterated_pullback_sections_map_heq_right
        (f := F.map c) (hg := hmap.symm) (𝒢 := ℋ) (U := U0) σraw).symm.trans
        (heq_of_eq
          (iteratedPullbackSectionsMap_identity_over_stage_eq_unit
            (f := F.map c) (ℋ := ℋ) (U := U0) (σ := σ)))
  simpa [overPullbackSectionsMap, Functor.map_comp, hmap, σraw, cast_eq_iff_heq] using hheq

/-- Helper for Lemma 6.29.3: restricting a section of a sheaf on `X_k` and then applying the
pullback unit along `p_k` is the same as first applying the unit and then restricting along the
preimage inclusion. This is the restriction-side normalization needed on overlap opens before the
identity-over-stage adapter is applied. -/
private theorem stage_pullback_unit_restriction_eq
    {k : I} (ℋ : (F.obj k).Sheaf (Type u)) {W R : Opens (F.obj k)}
    (hRW : R ≤ W) (σ : ℋ.1.obj (op W)) :
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app ℋ).1.app
        (op R)) (ℋ.1.map (homOfLE hRW).op σ)) =
      ((((limit.π F k)⁻¹).obj ℋ).presheaf).map
        (homOfLE (by
          intro x hx
          exact hRW hx)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app ℋ).1.app
            (op W)) σ) := by
  -- Evaluate the unit naturality square on the chosen section and rewrite it as a restriction
  -- identity on concrete sections.
  simpa [TopologicalSpace.Opens.map_homOfLE, ConcreteCategory.comp_apply] using
    (NatTrans.naturality_apply
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app ℋ).1)
      (homOfLE hRW).op σ)

/-- Helper for Lemma 6.29.3: if a section on `X_k` is first restricted to an overlap open `R` and
then lifted through the identity object of `Over k`, its image in the limit is exactly the
restriction of the original pullback-unit image. This packages the new normalization step needed
before feeding restricted local sections into
`common_refinement_of_equal_limit_pullback_sections`. -/
private theorem pullbackSectionsToLimitMap_identity_over_stage_restriction_eq
    {k : I} (ℋ : (F.obj k).Sheaf (Type u)) {W R : Opens (F.obj k)}
    (hRW : R ≤ W) (σ : ℋ.1.obj (op W)) :
    let σR : ℋ.1.obj (op R) :=
      ℋ.1.map (homOfLE hRW).op σ
    let σRid : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
    pullbackSectionsToLimitMap F ℋ R (Over.mk (𝟙 k)) σRid =
      ((((limit.π F k)⁻¹).obj ℋ).presheaf).map
        (homOfLE (by
          intro x hx
          exact hRW hx)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app ℋ).1.app
            (op W)) σ) := by
  let σR : ℋ.1.obj (op R) :=
    ℋ.1.map (homOfLE hRW).op σ
  let σRid : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
        simpa using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
            (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
  change pullbackSectionsToLimitMap F ℋ R (Over.mk (𝟙 k)) σRid = _
  -- First remove the identity-over-stage lift via the dedicated adapter, then rewrite the result
  -- as the restriction of the unreduced pullback-unit image on `W`.
  have hLift :
      pullbackSectionsToLimitMap F ℋ R (Over.mk (𝟙 k)) σRid =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app ℋ).1.app
          (op R)) (ℋ.1.map (homOfLE hRW).op σ)) := by
            simpa [σR, σRid] using
              pullbackSectionsToLimitMap_identity_over_stage_eq_unit
                (F := F) (ℋ := ℋ) (U0 := R) (σ := σR)
  exact hLift.trans <|
    stage_pullback_unit_restriction_eq
      (F := F) (ℋ := ℋ) hRW σ

/-- Helper for Lemma 6.29.3: the limit image of an identity-over-stage lift commutes with
restriction on the stage open. This is the restriction-stable overlap transport needed when the
final common-refinement step packages restricted raw stage sections into the identity-over-stage
source expected by `common_refinement_of_equal_limit_pullback_sections`. -/
private theorem pullbackSectionsToLimitMap_identity_over_stage_restrict_eq
    {k : I} (ℋ : (F.obj k).Sheaf (Type u)) {W R : Opens (F.obj k)}
    (hRW : R ≤ W) (σ : ℋ.1.obj (op W)) :
    let σidW : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj W)) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op W) σ)
    let σR : ℋ.1.obj (op R) :=
      ℋ.1.map (homOfLE hRW).op σ
    let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
    pullbackSectionsToLimitMap F ℋ R (Over.mk (𝟙 k)) σidR =
      ((((limit.π F k)⁻¹).obj ℋ).presheaf).map
        (homOfLE (by
          intro x hx
          exact hRW hx)).op
        (pullbackSectionsToLimitMap F ℋ W (Over.mk (𝟙 k)) σidW) := by
  let σidW : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj W)) := by
        simpa using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
            (eqToIso rfl)).inv.app ℋ).1.app (op W) σ)
  let σR : ℋ.1.obj (op R) :=
    ℋ.1.map (homOfLE hRW).op σ
  let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
        simpa using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
            (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
  let hπRW :
      (Opens.map (limit.π F k)).obj R ≤ (Opens.map (limit.π F k)).obj W := by
    intro x hx
    exact hRW hx
  -- Rewrite both sides to the same restricted pullback-unit section on the limit.
  have hLeft :
      pullbackSectionsToLimitMap F ℋ R (Over.mk (𝟙 k)) σidR =
        ((((limit.π F k)⁻¹).obj ℋ).presheaf).map
          (homOfLE hπRW).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app ℋ).1.app
              (op W)) σ) := by
    simpa [σR, σidR] using
      pullbackSectionsToLimitMap_identity_over_stage_restriction_eq
        (F := F) (ℋ := ℋ) hRW σ
  have hRight :
      ((((limit.π F k)⁻¹).obj ℋ).presheaf).map
          (homOfLE hπRW).op
          (pullbackSectionsToLimitMap F ℋ W (Over.mk (𝟙 k)) σidW) =
        ((((limit.π F k)⁻¹).obj ℋ).presheaf).map
          (homOfLE hπRW).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app ℋ).1.app
              (op W)) σ) := by
    simpa [σidW] using
      congrArg
        (((((limit.π F k)⁻¹).obj ℋ).presheaf).map
          (homOfLE hπRW).op)
        (pullbackSectionsToLimitMap_identity_over_stage_eq_unit
          (F := F) (ℋ := ℋ) (U0 := W) (σ := σ))
  exact hLeft.trans hRight.symm

/-- Helper for Lemma 6.29.3: restricting an identity-over-stage lift from a compact open `W₁`
to the exact overlap `W₁ ⊓ W₂` commutes with the limit comparison map. This compact-open
specialization keeps the exact-overlap bridge in a rewrite-friendly form. -/
private theorem pullbackSectionsToLimitMap_identity_over_stage_restrict_eq_inf
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {k : I} (ℋ : (F.obj k).Sheaf (Type u)) (W₁ W₂ : CompactOpens (F.obj k))
    (σ : ℋ.1.obj (op W₁.toOpens)) :
    let R : Opens (F.obj k) := (W₁ ⊓ W₂).toOpens
    let σidW : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj W₁.toOpens)) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op W₁.toOpens) σ)
    let σR : ℋ.1.obj (op R) :=
      ℋ.1.map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ W₁.toOpens from
            by
              intro x hx
              exact hx.1)).op
        σ
    let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
          simpa [σR] using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
    pullbackSectionsToLimitMap F ℋ R (Over.mk (𝟙 k)) σidR =
      ((((limit.π F k)⁻¹).obj ℋ).presheaf).map
        (homOfLE
          (show projection_preimage_open (F := F) ⟨k, W₁ ⊓ W₂⟩ ≤
              projection_preimage_open (F := F) ⟨k, W₁⟩ from
            by
              intro x hx
              exact hx.1)).op
        (pullbackSectionsToLimitMap F ℋ W₁.toOpens (Over.mk (𝟙 k)) σidW) := by
  let R : Opens (F.obj k) := (W₁ ⊓ W₂).toOpens
  let σidW : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
      (op ((Opens.map (F.map (𝟙 k))).obj W₁.toOpens)) := by
        simpa using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
              (𝟙 (F.obj k))).leftAdjointIdIso
            (eqToIso rfl)).inv.app ℋ).1.app (op W₁.toOpens) σ)
  let σR : ℋ.1.obj (op R) :=
    ℋ.1.map
      (homOfLE
        (show (W₁ ⊓ W₂).toOpens ≤ W₁.toOpens from
          by
            intro x hx
            exact hx.1)).op
      σ
  let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
      (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
        simpa [σR] using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
              (𝟙 (F.obj k))).leftAdjointIdIso
            (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
  -- This is exactly the general restriction theorem specialized to the exact compact-open overlap.
  simpa [R, σidW, σR, σidR] using
    pullbackSectionsToLimitMap_identity_over_stage_restrict_eq
      (F := F) (ℋ := ℋ)
      (W := W₁.toOpens) (R := R)
      (show R ≤ W₁.toOpens by
        intro x hx
        exact hx.1)
      σ

/-- Helper for Lemma 6.29.3: pulling back an exact compact-open overlap to a lower stage is the
same compact-open overlap of the two pulled-back pieces. This is the concrete overlap
normalization needed before the final pairwise compatibility family can be packaged for gluing. -/
private theorem stage_pullback_compact_open_inf
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) (U₁ U₂ : CompactOpens (F.obj i)) :
    stage_pullback_compact_open (F := F) hF a (U₁ ⊓ U₂) =
      stage_pullback_compact_open (F := F) hF a U₁ ⊓
        stage_pullback_compact_open (F := F) hF a U₂ := by
  ext x
  -- Both sides are the same inverse-image condition written before and after distributing
  -- preimage over intersection.
  rfl

/-- Helper for Lemma 6.29.3: on opens, the pullback of an exact compact-open overlap is exactly
the infimum of the two pulled-back opens. This is the open-index normalization exposed by the
remaining compatibility transport through `pullbackComp.hom`. -/
private theorem stage_pullback_compact_open_toOpens_inf
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) (U₁ U₂ : CompactOpens (F.obj i)) :
    (stage_pullback_compact_open (F := F) hF a (U₁ ⊓ U₂)).toOpens =
      (stage_pullback_compact_open (F := F) hF a U₁).toOpens ⊓
        (stage_pullback_compact_open (F := F) hF a U₂).toOpens := by
  -- This is the open-level version of `stage_pullback_compact_open_inf`, recorded separately so
  -- later compatibility arguments can rewrite overlap indices without reopening compact-open
  -- structure equalities.
  simpa using
    congrArg CompactOpens.toOpens
      (stage_pullback_compact_open_inf (F := F) hF a U₁ U₂)

/-- Helper for Lemma 6.29.3: the open attached to a compact-open overlap is symmetric in the two
factors. This isolates the base-open commutation needed when the right-overlap normalization is
rewritten from `W₂ ⊓ W₁` to the fixed order `W₁ ⊓ W₂`. -/
private theorem compact_open_inf_comm
    {X : TopCat.{u}} [SpectralSpace X] (U₁ U₂ : CompactOpens ↑X) :
    U₁ ⊓ U₂ = U₂ ⊓ U₁ := by
  -- Compact-open overlaps are pointwise intersections, so swapping the factors does not change
  -- the resulting compact open.
  ext x
  constructor
  · intro hx
    exact And.symm hx
  · intro hx
    exact And.symm hx

/-- Helper for Lemma 6.29.3: the open attached to a compact-open overlap is symmetric in the two
factors. This isolates the base-open commutation needed when the right-overlap normalization is
rewritten from `W₂ ⊓ W₁` to the fixed order `W₁ ⊓ W₂`. -/
private theorem compact_open_inf_toOpens_comm
    {X : TopCat.{u}} [SpectralSpace X] (U₁ U₂ : CompactOpens ↑X) :
    (U₁ ⊓ U₂).toOpens = (U₂ ⊓ U₁).toOpens := by
  -- Forgetting the compact-open structure preserves the compact-open commutation equality.
  simpa using congrArg CompactOpens.toOpens (compact_open_inf_comm U₁ U₂)

/-- Helper for Lemma 6.29.3: the pulled-back exact overlap open is symmetric in the two compact
open factors. This isolates the `⊓`-commutation that still needs to be threaded through the
dependent casts in the final common-stage overlap normalization. -/
private theorem stage_pullback_compact_open_inf_comm
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) (U₁ U₂ : CompactOpens (F.obj i)) :
    stage_pullback_compact_open (F := F) hF a (U₁ ⊓ U₂) =
      stage_pullback_compact_open (F := F) hF a (U₂ ⊓ U₁) := by
  -- The pullback of a compact-open overlap is again computed pointwise by intersection, so the
  -- symmetry of the overlap survives after pulling back along `a`.
  ext x
  constructor
  · intro hx
    simpa [stage_pullback_compact_open] using And.symm hx
  · intro hx
    simpa [stage_pullback_compact_open] using And.symm hx

/-- Helper for Lemma 6.29.3: the pulled-back exact overlap open is symmetric in the two compact
open factors. This isolates the `⊓`-commutation that still needs to be threaded through the
dependent casts in the final common-stage overlap normalization. -/
private theorem stage_pullback_compact_open_toOpens_inf_comm
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) (U₁ U₂ : CompactOpens (F.obj i)) :
    (stage_pullback_compact_open (F := F) hF a (U₁ ⊓ U₂)).toOpens =
      (stage_pullback_compact_open (F := F) hF a (U₂ ⊓ U₁)).toOpens := by
  -- Forgetting the compact-open structure preserves the pulled-back overlap commutation equality.
  simpa using
    congrArg CompactOpens.toOpens
      (stage_pullback_compact_open_inf_comm (F := F) hF a U₁ U₂)

/-- Helper for Lemma 6.29.3: the pulled-back exact overlap `a⁻¹(U₁ ∩ U₂)` maps to the pulled-back
right factor `a⁻¹(U₂)`. This is the right-branch inclusion used repeatedly when overlap
restrictions are written in fixed order. -/
private theorem stage_pullback_compact_open_inf_le_right
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) (U₁ U₂ : CompactOpens (F.obj i)) :
    (stage_pullback_compact_open (F := F) hF a (U₁ ⊓ U₂)).toOpens ≤
      (stage_pullback_compact_open (F := F) hF a U₂).toOpens := by
  -- The pulled-back overlap is pointwise the conjunction of membership in the two pulled-back
  -- factors, so projecting to the right factor gives the desired inclusion.
  intro x hx
  simpa [stage_pullback_compact_open] using hx.2

/-- Helper for Lemma 6.29.3: the pulled-back exact overlap `a⁻¹(U₁ ∩ U₂)` maps to the pulled-back
left factor `a⁻¹(U₁)`. This is the left-branch counterpart used when overlap restrictions are
normalized before the common-stage compatibility check. -/
private theorem stage_pullback_compact_open_inf_le_left
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : I} (a : j ⟶ i) (U₁ U₂ : CompactOpens (F.obj i)) :
    (stage_pullback_compact_open (F := F) hF a (U₁ ⊓ U₂)).toOpens ≤
      (stage_pullback_compact_open (F := F) hF a U₁).toOpens := by
  -- The pulled-back overlap is pointwise the conjunction of membership in the two pulled-back
  -- factors, so projecting to the left factor gives the desired inclusion.
  intro x hx
  simpa [stage_pullback_compact_open] using hx.1

/-- Helper for Lemma 6.29.3: once a family of descended sections on a common stage is known to
agree on every exact pairwise overlap, it is already a compatible family for sheaf gluing on that
stage cover. This isolates the final compatibility check from the earlier refinement bookkeeping.
-/
private theorem isCompatible_of_pairwise_overlap_eq
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {k l : I} (c : l ⟶ k) (ℋ : (F.obj k).Sheaf (Type u))
    {α : Type*} (W : α → CompactOpens (F.obj k))
    (u :
      ∀ a : α,
        ((((F.map c)⁻¹).obj ℋ).presheaf).obj
          (op ((stage_pullback_compact_open (F := F) hF c (W a)).toOpens)))
    (hOverlap :
      ∀ a a' : α,
        ((((F.map c)⁻¹).obj ℋ).presheaf).map
            (homOfLE
              (show
                (stage_pullback_compact_open (F := F) hF c (W a ⊓ W a')).toOpens ≤
                  (stage_pullback_compact_open (F := F) hF c (W a)).toOpens from
                by
                  intro x hx
                  simpa [stage_pullback_compact_open] using hx.1)).op
            (u a) =
          ((((F.map c)⁻¹).obj ℋ).presheaf).map
            (homOfLE
              (show
                (stage_pullback_compact_open (F := F) hF c (W a ⊓ W a')).toOpens ≤
                  (stage_pullback_compact_open (F := F) hF c (W a')).toOpens from
                by
                  intro x hx
                  simpa [stage_pullback_compact_open] using hx.2)).op
            (u a')) :
    TopCat.Presheaf.IsCompatible
      ((((F.map c)⁻¹).obj ℋ).presheaf)
      (fun a : α ↦ (stage_pullback_compact_open (F := F) hF c (W a)).toOpens)
      u := by
  intro a a'
  -- Rewrite the abstract pairwise intersection in `IsCompatible` to the exact pulled-back compact
  -- overlap handled by `hOverlap`.
  simpa [stage_pullback_compact_open_inf (F := F) hF c (W a) (W a')] using hOverlap a a'

/-- Helper for Lemma 6.29.3: pullback-unit sections commute with restriction to smaller opens.
This is the stage-side restriction normalization used both when overlap equalities are descended to
one stage and when the final compatible family is checked on pairwise intersections. -/
private theorem pullback_unit_section_restriction_eq
    {X Y : TopCat.{u}} (f : X ⟶ Y) (ℋ : Y.Sheaf (Type u)) {W R : Opens Y}
    (hRW : R ≤ W) (σ : ℋ.1.obj (op W)) :
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℋ).1.app
        (op R)) (ℋ.1.map (homOfLE hRW).op σ)) =
      ((((f⁻¹).obj ℋ).presheaf).map
        (homOfLE (by
          intro x hx
          exact hRW hx)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℋ).1.app
            (op W)) σ)) := by
  -- Evaluate the unit naturality square on the chosen section and read it as a restriction
  -- identity on concrete sections.
  simpa [TopologicalSpace.Opens.map_homOfLE, ConcreteCategory.comp_apply] using
    (NatTrans.naturality_apply
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℋ).1)
      (homOfLE hRW).op σ)

/-- Helper for Lemma 6.29.3: if a local section of `g⁻¹ 𝒢` is already the restriction of the
pullback-unit section of `σ`, then first applying the pullback unit along `f` and then collapsing
the nested pullback with `pullbackComp.hom` is exactly the restriction of the direct pullback-unit
section along `f ≫ g`. This packages the normalization used both in the overlap-collapse step and
in the final stalkwise local comparison. -/
private theorem pullbackComp_hom_unit_restriction_eq
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (𝒢 : Z.Sheaf (Type u))
    {W : Opens Y} {V : Opens Z}
    (σ : 𝒢.1.obj (op V))
    (τ : (((g⁻¹).obj 𝒢).presheaf).obj (op W))
    (hWV : W ≤ (Opens.map g).obj V)
    (hτ :
      τ =
        (((g⁻¹).obj 𝒢).presheaf).map (homOfLE hWV).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app 𝒢).1.app
              (op V)) σ)) :
    (((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1.app
        (op ((Opens.map f).obj W)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
              ((g⁻¹).obj 𝒢)).1.app
            (op W)) τ) =
      ((((f ≫ g)⁻¹).obj 𝒢).presheaf).map
        (homOfLE (by
          intro x hx
          exact hWV hx)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app 𝒢).1.app
            (op V)) σ) := by
  let σg : (((g⁻¹).obj 𝒢).presheaf).obj (op ((Opens.map g).obj V)) :=
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app 𝒢).1.app
        (op V)) σ)
  let hPre : (Opens.map f).obj W ≤ (Opens.map (f ≫ g)).obj V := by
    intro x hx
    exact hWV hx
  let σid :
      ((((TopCat.Sheaf.pullback (Type u) (𝟙 Z)).obj 𝒢).presheaf).obj
        (op ((Opens.map (𝟙 Z)).obj V))) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 Z)).leftAdjointIdIso
                (eqToIso rfl)).inv.app 𝒢).1.app (op V) σ)
  have hNestedUnit :
      (((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1.app
          (op ((Opens.map f).obj ((Opens.map g).obj V)))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
                ((g⁻¹).obj 𝒢)).1.app
              (op ((Opens.map g).obj V))) σg)) =
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app 𝒢).1.app
            (op V)) σ) := by
    -- Normalize the nested-unit branch by inserting the identity pullback on `Z` once and then
    -- using associativity together with the identity-over-stage normalization on `g` and `f ≫ g`.
    have hAssoc :=
      iterated_pullback_sections_map_assoc_pointwise_transport
        (f := f) (g := g) (h := 𝟙 Z) (𝒢 := 𝒢) (U := V) σid
    have hLeft :
        iteratedPullbackSectionsMap (f ≫ g) (𝟙 Z) 𝒢 V σid =
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app 𝒢).1.app
              (op V)) σ) := by
      simpa [σid] using
        (iteratedPullbackSectionsMap_identity_over_stage_eq_unit
          (f := f ≫ g) (ℋ := 𝒢) (U := V) (σ := σ))
    have hRight :
        cast (by rfl)
            ((iteratedPullbackSectionsMap f (g ≫ 𝟙 Z) 𝒢 V ∘
                iteratedPullbackSectionsMap g (𝟙 Z) 𝒢 V) σid) =
          (((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1.app
            (op ((Opens.map f).obj ((Opens.map g).obj V)))
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
                  ((g⁻¹).obj 𝒢)).1.app
                (op ((Opens.map g).obj V))) σg)) := by
      simpa [iteratedPullbackSectionsMap, Function.comp, σg, σid] using
        congrArg
          (fun t ↦ cast (by rfl) (iteratedPullbackSectionsMap f (g ≫ 𝟙 Z) 𝒢 V t))
          (iteratedPullbackSectionsMap_identity_over_stage_eq_unit
            (f := g) (ℋ := 𝒢) (U := V) (σ := σ))
    exact hRight.symm.trans (hAssoc.symm.trans hLeft)
  -- First rewrite the local section by its descended-unit description, then commute the `f`-unit
  -- past the restriction, and finally collapse the nested pullback-unit branch.
  calc
    (((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1.app
        (op ((Opens.map f).obj W)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
              ((g⁻¹).obj 𝒢)).1.app
            (op W)) τ) =
      (((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1.app
        (op ((Opens.map f).obj W)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
              ((g⁻¹).obj 𝒢)).1.app
            (op W))
          ((((g⁻¹).obj 𝒢).presheaf).map (homOfLE hWV).op σg)) := by
            simpa [σg, hτ]
    _ =
      (((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1.app
        (op ((Opens.map f).obj W)))
        (((((f⁻¹).obj ((g⁻¹).obj 𝒢)).presheaf).map
            (homOfLE hPre).op)
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
                ((g⁻¹).obj 𝒢)).1.app
              (op ((Opens.map g).obj V))) σg)) := by
            exact congrArg
              ((((TopCat.Sheaf.pullbackComp (A := Type u) f g).hom.app 𝒢).1.app
                  (op ((Opens.map f).obj W))))
              (pullback_unit_section_restriction_eq
                (f := f) (ℋ := ((g⁻¹).obj 𝒢)) (hRW := hWV) (σ := σg))
    _ =
      ((((f ≫ g)⁻¹).obj 𝒢).presheaf).map (homOfLE hPre).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app 𝒢).1.app
            (op V)) σ) := by
              rw [pullbackComp_hom_restriction_eq]
              exact congrArg
                (((((f ≫ g)⁻¹).obj 𝒢).presheaf).map (homOfLE hPre).op)
                hNestedUnit

/-- Helper for Lemma 6.29.3: refining an identity-over-stage lift on a larger open and then
restricting to a smaller open is the same as first restricting the stage section and then taking
its identity-over-stage lift before refining. This is the exact restriction normalization needed
when the eventual common-stage family is checked on pairwise overlaps. -/
private theorem overPullbackSectionsMap_identity_over_stage_restrict_eq
    {k l : I} (c : l ⟶ k) (ℋ : (F.obj k).Sheaf (Type u)) {W R : Opens (F.obj k)}
    (hRW : R ≤ W) (σ : ℋ.1.obj (op W)) :
    let σidW : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj W)) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op W) σ)
    let σR : ℋ.1.obj (op R) :=
      ℋ.1.map (homOfLE hRW).op σ
    let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
    ((((F.map c)⁻¹).obj ℋ).presheaf).map
        (homOfLE (by
          intro x hx
          exact hRW hx)).op
        (overPullbackSectionsMap F ℋ W
          (A := Over.mk c) (B := Over.mk (𝟙 k))
          (Over.homMk c (by simp)) σidW) =
      overPullbackSectionsMap F ℋ R
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) σidR := by
  let σidW : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
      (op ((Opens.map (F.map (𝟙 k))).obj W)) := by
        simpa using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
              (𝟙 (F.obj k))).leftAdjointIdIso
            (eqToIso rfl)).inv.app ℋ).1.app (op W) σ)
  let σR : ℋ.1.obj (op R) :=
    ℋ.1.map (homOfLE hRW).op σ
  let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
      (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
        simpa using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
              (𝟙 (F.obj k))).leftAdjointIdIso
            (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
  let hPre :
      (Opens.map (F.map c)).obj R ≤ (Opens.map (F.map c)).obj W := by
        intro x hx
        exact hRW (by simpa using hx)
  -- Rewrite both sides as the restriction of the same pullback-unit section along `F.map c`.
  have hLeft :
      ((((F.map c)⁻¹).obj ℋ).presheaf).map
          (homOfLE hPre).op
          (overPullbackSectionsMap F ℋ W
            (A := Over.mk c) (B := Over.mk (𝟙 k))
            (Over.homMk c (by simp)) σidW) =
        ((((F.map c)⁻¹).obj ℋ).presheaf).map
          (homOfLE hPre).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
              (F.map c)).unit.app ℋ).1.app (op W)) σ) := by
    simpa [σidW] using
      congrArg
        (((((F.map c)⁻¹).obj ℋ).presheaf).map
          (homOfLE hPre).op)
        (overPullbackSectionsMap_identity_over_stage_eq_pullback_unit
          (F := F) (c := c) (ℋ := ℋ) (U0 := W) (σ := σ))
  have hRight :
      overPullbackSectionsMap F ℋ R
          (A := Over.mk c) (B := Over.mk (𝟙 k))
          (Over.homMk c (by simp)) σidR =
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
            (F.map c)).unit.app ℋ).1.app (op R)) (ℋ.1.map (homOfLE hRW).op σ)) := by
    simpa [σR, σidR] using
      overPullbackSectionsMap_identity_over_stage_eq_pullback_unit
        (F := F) (c := c) (ℋ := ℋ) (U0 := R) (σ := σR)
  have hRestr :
      ((((F.map c)⁻¹).obj ℋ).presheaf).map
          (homOfLE hPre).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
              (F.map c)).unit.app ℋ).1.app (op W)) σ) =
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
            (F.map c)).unit.app ℋ).1.app (op R)) (ℋ.1.map (homOfLE hRW).op σ)) := by
    simpa using
      (pullback_unit_section_restriction_eq (f := F.map c) (ℋ := ℋ) hRW σ).symm
  exact hLeft.trans (hRestr.trans (by simpa using hRight.symm))

/-- Helper for Lemma 6.29.3: after refining an identity-over-stage lift along `c : l ⟶ k`,
restricting it to the exact compact-open overlap `W₁ ⊓ W₂` is the same as first restricting the
raw stage section on `W₁` to `W₁ ⊓ W₂` and then refining that restricted identity-over-stage lift.
This is the compact-open specialization of the restriction normalization used in the final
same-stage gluing step. -/
private theorem overPullbackSectionsMap_identity_over_stage_restrict_eq_inf
    [∀ i : I, SpectralSpace (F.obj i)]
    {k l : I} (c : l ⟶ k) (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (ℋ : (F.obj k).Sheaf (Type u)) (W₁ W₂ : CompactOpens (F.obj k))
    (σ : ℋ.1.obj (op W₁.toOpens)) :
    let R : Opens (F.obj k) := (W₁ ⊓ W₂).toOpens
    let σidW : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj W₁.toOpens)) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op W₁.toOpens) σ)
    let σR : ℋ.1.obj (op R) :=
      ℋ.1.map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ W₁.toOpens from
            by
              intro x hx
              exact hx.1)).op
        σ
    let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
          simpa [σR] using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
    ((((F.map c)⁻¹).obj ℋ).presheaf).map
        (homOfLE
          (show
            (stage_pullback_compact_open (F := F) hF c (W₁ ⊓ W₂)).toOpens ≤
              (stage_pullback_compact_open (F := F) hF c W₁).toOpens from
            by
              intro x hx
              simpa [stage_pullback_compact_open] using hx.1)).op
        (overPullbackSectionsMap F ℋ W₁.toOpens
          (A := Over.mk c) (B := Over.mk (𝟙 k))
          (Over.homMk c (by simp)) σidW) =
      overPullbackSectionsMap F ℋ R
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) σidR := by
  let R : Opens (F.obj k) := (W₁ ⊓ W₂).toOpens
  let σidW : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
      (op ((Opens.map (F.map (𝟙 k))).obj W₁.toOpens)) := by
        simpa using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
              (𝟙 (F.obj k))).leftAdjointIdIso
            (eqToIso rfl)).inv.app ℋ).1.app (op W₁.toOpens) σ)
  let σR : ℋ.1.obj (op R) :=
    ℋ.1.map
      (homOfLE
        (show (W₁ ⊓ W₂).toOpens ≤ W₁.toOpens from
          by
            intro x hx
            exact hx.1)).op
      σ
  let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
      (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
        simpa [σR] using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
              (𝟙 (F.obj k))).leftAdjointIdIso
            (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
  simpa [R, σidW, σR, σidR] using
    overPullbackSectionsMap_identity_over_stage_restrict_eq
      (F := F) (c := c) (ℋ := ℋ)
      (W := W₁.toOpens) (R := R)
      (show R ≤ W₁.toOpens by
        intro x hx
        exact hx.1)
      σ

/-- Helper for Lemma 6.29.3: the exact-overlap normalization for
`overPullbackSectionsMap_identity_over_stage_restrict_eq_inf` is also available in the reverse
direction, rewriting the refined overlap section back to the restriction of the larger common-stage
section. This is the orientation used when overlap equalities are converted into the explicit
`IsCompatible` equations on a common stage. -/
private theorem overPullbackSectionsMap_identity_over_stage_restrict_eq_inf_symm
    [∀ i : I, SpectralSpace (F.obj i)]
    {k l : I} (c : l ⟶ k) (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (ℋ : (F.obj k).Sheaf (Type u)) (W₁ W₂ : CompactOpens (F.obj k))
    (σ : ℋ.1.obj (op W₁.toOpens)) :
    let R : Opens (F.obj k) := (W₁ ⊓ W₂).toOpens
    let σR : ℋ.1.obj (op R) :=
      ℋ.1.map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ W₁.toOpens from
            by
              intro x hx
              exact hx.1)).op
        σ
    let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
          simpa [σR] using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
    overPullbackSectionsMap F ℋ R
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) σidR =
      ((((F.map c)⁻¹).obj ℋ).presheaf).map
        (homOfLE
          (show
            (stage_pullback_compact_open (F := F) hF c (W₁ ⊓ W₂)).toOpens ≤
              (stage_pullback_compact_open (F := F) hF c W₁).toOpens from
            by
              intro x hx
              simpa [stage_pullback_compact_open] using hx.1)).op
        (overPullbackSectionsMap F ℋ W₁.toOpens
          (A := Over.mk c) (B := Over.mk (𝟙 k))
          (Over.homMk c (by simp)) (by
            simpa using
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                  (𝟙 (F.obj k))).leftAdjointIdIso
                (eqToIso rfl)).inv.app ℋ).1.app (op W₁.toOpens) σ))) := by
  -- This is exactly the previous overlap-normalization theorem, read in the reverse direction.
  simpa using
    (overPullbackSectionsMap_identity_over_stage_restrict_eq_inf
      (F := F) (c := c) (hF := hF) (ℋ := ℋ)
      (W₁ := W₁) (W₂ := W₂) (σ := σ)).symm

/-- Helper for Lemma 6.29.3: the reverse exact-overlap normalization specialized to the swapped
right branch `W₂ ⊓ W₁`. This thin adapter isolates the already-stable half of the final right
overlap argument before the remaining proposition-level transport back to the fixed overlap order.
-/
private theorem overPullbackSectionsMap_identity_over_stage_restrict_eq_inf_symm_swapped
    [∀ i : I, SpectralSpace (F.obj i)]
    {k l : I} (c : l ⟶ k) (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (ℋ : (F.obj k).Sheaf (Type u)) (W₁ W₂ : CompactOpens (F.obj k))
    (σ : ℋ.1.obj (op W₂.toOpens)) :
    let R : Opens (F.obj k) := (W₂ ⊓ W₁).toOpens
    let σR : ℋ.1.obj (op R) :=
      ℋ.1.map
        (homOfLE
          (show (W₂ ⊓ W₁).toOpens ≤ W₂.toOpens from
            by
              intro x hx
              exact hx.1)).op
        σ
    let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
          simpa [σR] using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
    overPullbackSectionsMap F ℋ R
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) σidR =
      ((((F.map c)⁻¹).obj ℋ).presheaf).map
        (homOfLE
          (show
            (stage_pullback_compact_open (F := F) hF c (W₂ ⊓ W₁)).toOpens ≤
              (stage_pullback_compact_open (F := F) hF c W₂).toOpens from
            by
              intro x hx
              simpa [stage_pullback_compact_open] using hx.1)).op
        (overPullbackSectionsMap F ℋ W₂.toOpens
          (A := Over.mk c) (B := Over.mk (𝟙 k))
          (Over.homMk c (by simp)) (by
            simpa using
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                  (𝟙 (F.obj k))).leftAdjointIdIso
                (eqToIso rfl)).inv.app ℋ).1.app (op W₂.toOpens) σ))) := by
  -- This is exactly the reverse exact-overlap normalization with the overlap factors swapped.
  simpa using
    (overPullbackSectionsMap_identity_over_stage_restrict_eq_inf_symm
      (F := F) (c := c) (hF := hF) (ℋ := ℋ)
      (W₁ := W₂) (W₂ := W₁) (σ := σ))

/-- Helper for Lemma 6.29.3: a stage-side inclusion `W ⊆ h⁻¹(V)` induces the corresponding
inclusion `p_k⁻¹(W) ⊆ p_i⁻¹(V)` on the limit. This isolates the open-level transport that the
remaining overlap bridge repeatedly needs. -/
private theorem limit_projection_preimage_le_of_stage_le
    {i k : I} (h : k ⟶ i) {V : Opens (F.obj i)} {W : Opens (F.obj k)}
    (hWV : W ≤ (Opens.map (F.map h)).obj V) :
    (Opens.map (limit.π F k)).obj W ≤ (Opens.map (limit.π F i)).obj V := by
  intro x hx
  have hπ :
      F.map h ((limit.π F k) x) = (limit.π F i) x := by
    exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F h)) x
  simpa [hπ] using hWV hx

/-- Helper for Lemma 6.29.3: restriction/cast transport specialized to a source open
`O ⊆ f_h⁻¹(U)`. This keeps the proof-relevant `homOfLE` term on the direct `p_i` side in the
canonical `limit_projection_preimage_le_of_stage_le` form used by the descent proof. -/
private theorem limit_pullback_section_restriction_cast_eq_source_open
    {i k : I} (h : k ⟶ i) (𝒢 : (F.obj i).Sheaf (Type u))
    {U : Opens (F.obj i)} {O : Opens (F.obj k)}
    (hOU : O ≤ (Opens.map (F.map h)).obj U)
    (σ :
      (((TopCat.Sheaf.pullback (Type u) (limit.π F k ≫ F.map h)).obj 𝒢).presheaf).obj
        (op ((Opens.map (limit.π F k)).obj ((Opens.map (F.map h)).obj U)))) :
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
        (homOfLE (limit_projection_preimage_le_of_stage_le (F := F) (h := h) hOU)).op
        (cast (limitPullbackSections_eq F 𝒢 U (Over.mk h)) σ) =
      cast
        (by
          exact
            congrArg
              (fun f : limit F ⟶ F.obj i ↦
                (((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj
                  (op ((Opens.map (limit.π F k)).obj O)))
              (limit.w F h))
        ((((TopCat.Sheaf.pullback (Type u) (limit.π F k ≫ F.map h)).obj 𝒢).presheaf).map
          (homOfLE (by
            intro x hx
            exact hOU hx)).op σ) := by
  let hπOU :
      (Opens.map (limit.π F k)).obj O ≤
        (Opens.map (limit.π F k)).obj ((Opens.map (F.map h)).obj U) := by
    intro x hx
    exact hOU hx
  convert
    (limit_pullback_section_restriction_cast_eq
      (F := F) (h := h) (𝒢 := 𝒢)
      (W := (Opens.map (limit.π F k)).obj ((Opens.map (F.map h)).obj U))
      (R := (Opens.map (limit.π F k)).obj O)
      (iRW := homOfLE hπOU)
      (σ := σ))
    using 1
  · have hOpenU :
        (Opens.map (limit.π F k)).obj ((Opens.map (F.map h)).obj U) =
          (Opens.map (limit.π F i)).obj U := by
      ext x
      change F.map h ((limit.π F k) x) ∈ U ↔ (limit.π F i) x ∈ U
      have hπ : F.map h ((limit.π F k) x) = (limit.π F i) x := by
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F h)) x
      rw [hπ]
    have hCastW :
        (((TopCat.Sheaf.pullback (Type u) (limit.π F k ≫ F.map h)).obj 𝒢).presheaf).obj
            (op ((Opens.map (limit.π F k)).obj ((Opens.map (F.map h)).obj U))) =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
            (op ((Opens.map (limit.π F k)).obj ((Opens.map (F.map h)).obj U))) := by
      exact
        congrArg
          (fun f : limit F ⟶ F.obj i ↦
            (((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj
              (op ((Opens.map (limit.π F k)).obj ((Opens.map (F.map h)).obj U))))
          (limit.w F h)
    have hres :=
      presheaf_restrict_cast_source_eq
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf)
        (hWW' := hOpenU)
        (hRW := hπOU)
        (hRW' := limit_projection_preimage_le_of_stage_le (F := F) (h := h) hOU)
        (s := cast hCastW σ)
    convert hres using 1
    · simp [cast_cast]

/-- Helper for Lemma 6.29.3: after pulling a compact-open piece back from stage `j` to stage `k`
and then further to stage `l`, the resulting refined piece still lies over the original stage-`k`
piece on the limit. This packages the refined-piece inclusion repeatedly used in the final
stalkwise comparison. -/
private theorem refined_stage_pullback_piece_le
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {j k l : I} (b : k ⟶ j) (c : l ⟶ k) (W : CompactOpens (F.obj j)) :
    projection_preimage_open (F := F)
        ⟨l, stage_pullback_compact_open (F := F) hF c
          (stage_pullback_compact_open (F := F) hF b W)⟩ ≤
      projection_preimage_open (F := F)
        ⟨k, stage_pullback_compact_open (F := F) hF b W⟩ := by
  -- The refined piece is defined by first pulling back the stage-`k` piece along `c`, so its
  -- limit preimage maps into that stage-`k` piece by the generic projection-transport lemma.
  exact
    limit_projection_preimage_le_of_stage_le
      (F := F) (h := c)
      (W := (stage_pullback_compact_open (F := F) hF c
        (stage_pullback_compact_open (F := F) hF b W)).toOpens)
      (V := (stage_pullback_compact_open (F := F) hF b W).toOpens)
      (by
        intro x hx
        simpa [stage_pullback_compact_open] using hx)

/-- Helper for Lemma 6.29.3: transporting the pullback-unit section on a source open for the
composite map `p_k ≫ h` across the canonical equality `limit.w F h` identifies it with the direct
pullback-unit section for `p_i` on the same open. This isolates the source-open cast normalization
that the final limit-side restriction bridge needs before any restriction map is applied. -/
private theorem limit_pullback_unit_cast_eq_on_composite_open
    {i k : I} (h : k ⟶ i) (𝒢 : (F.obj i).Sheaf (Type u))
    {V : Opens (F.obj i)} (σ : 𝒢.1.obj (op V)) :
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k ≫ F.map h)).unit.app
        𝒢).1.app (op V)) σ) =
      cast
        (by
          simpa using
            congrArg
              (fun f : limit F ⟶ F.obj i ↦
                ((((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj
                  (op ((Opens.map f).obj V))))
              (limit.w F h))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
            𝒢).1.app (op V)) σ) := by
  -- The source-open unit section only depends on the underlying projection map, so after
  -- replacing `p_k ≫ h` by `p_i` the two sections are definitionally identical.
  exact
    pullback_unit_app_cast_eq_of_hom_eq
      (hfg := by simpa using limit.w F h)
      (𝒢 := 𝒢) (σ := σ)

/-- Helper for Lemma 6.29.3: restricting the composite-open pullback-unit section for
`limit.π F k ≫ F.map h` to the smaller open `(Opens.map (limit.π F k)).obj W` agrees with the
corresponding restriction of the direct `p_i`-pullback-unit section, after transporting through
`limit.w F h`. This is the exact limit-side cast bridge needed in the final overlap collapse. -/
private theorem limit_pullback_unit_restriction_cast_eq_exact
    {i k : I} (h : k ⟶ i) (𝒢 : (F.obj i).Sheaf (Type u))
    {W : Opens (F.obj k)} {V : Opens (F.obj i)}
    (σ : 𝒢.1.obj (op V)) (hWV : W ≤ (Opens.map (F.map h)).obj V) :
    ((((limit.π F k ≫ F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE (by
          simpa [Functor.map_comp] using
            (limit_projection_preimage_le_of_stage_le (F := F) (h := h) hWV))).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k ≫ F.map h)).unit.app
            𝒢).1.app (op V)) σ) =
      cast
        (by
          simpa using
            congrArg
              (fun f : limit F ⟶ F.obj i ↦
                ((((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj
                  (op ((Opens.map (limit.π F k)).obj W))))
              (limit.w F h))
        (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
            (homOfLE
              (limit_projection_preimage_le_of_stage_le (F := F) (h := h) hWV)).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V)) σ)) := by
  -- Specialize the generic map-equality normalization to `limit.w F h`, so both the unit section
  -- and the restriction map are transported in one stable step.
  exact
    pullback_unit_restriction_eq_of_hom_eq
      (hfg := by simpa using (limit.w F h).symm)
      (𝒢 := 𝒢)
      (R := (Opens.map (limit.π F k)).obj W)
      (V := V)
      (σ := σ)
      (hRV := limit_projection_preimage_le_of_stage_le (F := F) (h := h) hWV)

/-- Helper for Lemma 6.29.3: after collapsing an identity-over-stage lift on `X_k` through
`TopCat.Sheaf.pullbackComp` along the limit projection `p_k`, the resulting composite-pullback
section is exactly the restriction of the direct `p_i`-pullback-unit section, up to the canonical
cast coming from `p_k ≫ h = p_i`. This is the limit-side normalization used when the final exact
overlap equality is rewritten into the form required by `hEqOverlap`. -/
private theorem pullback_comp_limit_unit_restriction_eq
    {i k : I} (h : k ⟶ i) (𝒢 : (F.obj i).Sheaf (Type u))
    {W : Opens (F.obj k)} {V : Opens (F.obj i)}
    (σ : 𝒢.1.obj (op V))
    (τ : ((((F.map h)⁻¹).obj 𝒢).presheaf).obj (op W))
    (hWV : W ≤ (Opens.map (F.map h)).obj V)
    (hτ :
      τ =
        ((((F.map h)⁻¹).obj 𝒢).presheaf).map (homOfLE hWV).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app 𝒢).1.app
              (op V)) σ)) :
    let σidW :
        ((((F.map (𝟙 k))⁻¹).obj (((F.map h)⁻¹).obj 𝒢)).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj W)) := by
          simpa using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
                (eqToIso rfl)).inv.app (((F.map h)⁻¹).obj 𝒢)).1.app (op W) τ)
    (((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F k) (F.map h)).hom.app 𝒢).1.app
        (op ((Opens.map (limit.π F k)).obj W)))
        (pullbackSectionsToLimitMap F (((F.map h)⁻¹).obj 𝒢) W (Over.mk (𝟙 k)) σidW) =
      cast
        (by
          simpa using
            congrArg
              (fun f : limit F ⟶ F.obj i ↦
                ((((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj
                  (op ((Opens.map (limit.π F k)).obj W))))
              (limit.w F h))
        (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
            (homOfLE (limit_projection_preimage_le_of_stage_le
              (F := F) (h := h) hWV)).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V)) σ)) := by
  let σidW :
      ((((F.map (𝟙 k))⁻¹).obj (((F.map h)⁻¹).obj 𝒢)).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj W)) := by
        simpa using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app (((F.map h)⁻¹).obj 𝒢)).1.app (op W) τ)
  -- First replace the identity-over-stage lift by the ordinary pullback unit along `p_k`.
  have hLift :
      pullbackSectionsToLimitMap F (((F.map h)⁻¹).obj 𝒢) W (Over.mk (𝟙 k)) σidW =
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app
            (((F.map h)⁻¹).obj 𝒢)).1.app (op W)) τ) := by
    simpa [σidW] using
      pullbackSectionsToLimitMap_identity_over_stage_eq_unit
        (F := F) (ℋ := ((F.map h)⁻¹).obj 𝒢) (U0 := W) (σ := τ)
  -- Then collapse the nested pullback/unit branch and transport the resulting section across
  -- `limit.w F h : limit.π F k ≫ F.map h = limit.π F i`.
  have hcomp : limit.π F k ≫ F.map h = limit.π F i := by
    simpa using limit.w F h
  calc
    (((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F k) (F.map h)).hom.app 𝒢).1.app
        (op ((Opens.map (limit.π F k)).obj W)))
        (pullbackSectionsToLimitMap F (((F.map h)⁻¹).obj 𝒢) W (Over.mk (𝟙 k)) σidW) =
      (((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F k) (F.map h)).hom.app 𝒢).1.app
          (op ((Opens.map (limit.π F k)).obj W)))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k)).unit.app
              (((F.map h)⁻¹).obj 𝒢)).1.app (op W)) τ) := by
            rw [hLift]
    _ =
      ((((limit.π F k ≫ F.map h)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (by
            intro x hx
            exact hWV hx)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F k ≫ F.map h)).unit.app
              𝒢).1.app (op V)) σ) := by
            exact
              pullbackComp_hom_unit_restriction_eq
                (f := limit.π F k) (g := F.map h) (𝒢 := 𝒢)
                (σ := σ) (τ := τ) (hWV := hWV) (hτ := hτ)
    _ =
      cast
        (by
          simpa using
            congrArg
              (fun f : limit F ⟶ F.obj i ↦
                ((((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj
                  (op ((Opens.map (limit.π F k)).obj W))))
              (limit.w F h))
        (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
            (homOfLE (limit_projection_preimage_le_of_stage_le
              (F := F) (h := h) hWV)).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V)) σ)) := by
          -- Use the exact source-open cast normalization together with the restriction/cast
          -- commutation lemma, so the composite branch is rewritten directly to the `p_i` branch.
          exact
            limit_pullback_unit_restriction_cast_eq_exact
              (F := F) (h := h) (𝒢 := 𝒢) (σ := σ) (hWV := hWV)

/-- Helper for Lemma 6.29.3: an exact-overlap equality of two limit-side pullback-unit sections
can be rewritten into the two-step restriction form needed when that overlap equality is compared
to a pulled-back stage section. -/
private theorem exact_overlap_limit_unit_sections_eq_two_step_restriction
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    {i k : I} (𝒢 : (F.obj i).Sheaf (Type u))
    (W₁ W₂ : CompactOpens (F.obj k))
    {V₁ V₂ : Opens (F.obj i)}
    (σ₁ : 𝒢.1.obj (op V₁)) (σ₂ : 𝒢.1.obj (op V₂))
    (hW₁V : projection_preimage_open (F := F) ⟨k, W₁⟩ ≤
      (Opens.map (limit.π F i)).obj V₁)
    (hW₂V : projection_preimage_open (F := F) ⟨k, W₂⟩ ≤
      (Opens.map (limit.π F i)).obj V₂)
    (hExact :
      ∃ hR₁ : projection_preimage_open (F := F) ⟨k, W₁ ⊓ W₂⟩ ≤
          projection_preimage_open (F := F) ⟨k, W₁⟩,
        ∃ hR₂ : projection_preimage_open (F := F) ⟨k, W₁ ⊓ W₂⟩ ≤
            projection_preimage_open (F := F) ⟨k, W₂⟩,
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
              (homOfLE (le_trans hR₁ hW₁V)).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app (op V₁)) σ₁) =
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
              (homOfLE (le_trans hR₂ hW₂V)).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                  𝒢).1.app (op V₂)) σ₂)) :
    ∃ hR₁ : projection_preimage_open (F := F) ⟨k, W₁ ⊓ W₂⟩ ≤
        projection_preimage_open (F := F) ⟨k, W₁⟩,
      ∃ hR₂ : projection_preimage_open (F := F) ⟨k, W₁ ⊓ W₂⟩ ≤
          projection_preimage_open (F := F) ⟨k, W₂⟩,
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₁).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
                (homOfLE hW₁V).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app (op V₁)) σ₁)) =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₂).op
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
                (homOfLE hW₂V).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app (op V₂)) σ₂)) := by
  rcases hExact with ⟨hR₁, hR₂, hEq⟩
  refine ⟨hR₁, hR₂, ?_⟩
  -- Normalize the single-step exact-overlap equality into the two-step restriction form used by
  -- the later stage-side comparison.
  calc
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₁).op
        (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
            (homOfLE hW₁V).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₁)) σ₁)) =
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
        (homOfLE (le_trans hR₁ hW₁V)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
            𝒢).1.app (op V₁)) σ₁) := by
            symm
            exact
              pullback_unit_restriction_limit_image_eq
                (F := F) (𝒢 := 𝒢) (W₁ := W₁) (R := W₁ ⊓ W₂) σ₁ hW₁V hR₁
    _ =
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
        (homOfLE (le_trans hR₂ hW₂V)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
            𝒢).1.app (op V₂)) σ₂) := hEq
    _ =
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₂).op
        (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
            (homOfLE hW₂V).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V₂)) σ₂)) := by
            exact
              pullback_unit_restriction_limit_image_eq
                (F := F) (𝒢 := 𝒢) (W₁ := W₂) (R := W₁ ⊓ W₂) σ₂ hW₂V hR₂

/-- Helper for Lemma 6.29.3: restricting a stage-side local section to the exact overlap agrees
with restricting the corresponding pullback-unit section in one step. This packages the source-side
normalization used before the common-refinement argument is applied. -/
private theorem restricted_stage_section_eq_two_step_restriction
    [∀ i : I, SpectralSpace (F.obj i)]
    {i k : I} (h : k ⟶ i) (𝒢 : (F.obj i).Sheaf (Type u))
    {W₁ W₂ : CompactOpens (F.obj k)} {V : Opens (F.obj i)}
    (σ : 𝒢.1.obj (op V))
    (τ : ((((F.map h)⁻¹).obj 𝒢).presheaf).obj (op W₁.toOpens))
    (hW₁V : W₁.toOpens ≤ (Opens.map (F.map h)).obj V)
    (hτ :
      τ =
        ((((F.map h)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁V).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app
              𝒢).1.app (op V)) σ)) :
    ((((F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ W₁.toOpens from
            by
              intro x hx
              exact hx.1)).op
        τ =
      ((((F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ (Opens.map (F.map h)).obj V from
            by
              intro x hx
              exact hW₁V hx.1)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app
            𝒢).1.app (op V)) σ) := by
  -- Rewrite the restricted stage section as the corresponding restricted pullback-unit section.
  calc
    ((((F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ W₁.toOpens from
            by
              intro x hx
              exact hx.1)).op
        τ =
      ((((F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ W₁.toOpens from
            by
              intro x hx
              exact hx.1)).op
        (((((F.map h)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₁V).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app
              𝒢).1.app (op V)) σ)) := by
            simpa [hτ]
    _ =
      ((((F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ (Opens.map (F.map h)).obj V from
            by
              intro x hx
              exact hW₁V hx.1)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app
            𝒢).1.app (op V)) σ) := by
            simpa using
              (sheaf_section_restriction_comp_eq
                (ℱ := ((F.map h)⁻¹).obj 𝒢)
                (hWV := hW₁V)
                (hRW := (show (W₁ ⊓ W₂).toOpens ≤ W₁.toOpens from
                  by
                    intro x hx
                    exact hx.1))
                (σ := ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app
                  𝒢).1.app (op V)) σ)))

/-- Helper for Lemma 6.29.3: the same source-side normalization can be written with the overlap
kept in the fixed order `W₁ ⊓ W₂` while the section being restricted lives on the right branch
`W₂`. This is the exact fixed-owner form needed when the final overlap collapse compares the left
and right local sections on the same open `Rqq`. -/
private theorem restricted_stage_section_eq_two_step_restriction_right_fixed_owner
    [∀ i : I, SpectralSpace (F.obj i)]
    {i k : I} (h : k ⟶ i) (𝒢 : (F.obj i).Sheaf (Type u))
    {W₁ W₂ : CompactOpens (F.obj k)} {V : Opens (F.obj i)}
    (σ : 𝒢.1.obj (op V))
    (τ : ((((F.map h)⁻¹).obj 𝒢).presheaf).obj (op W₂.toOpens))
    (hW₂V : W₂.toOpens ≤ (Opens.map (F.map h)).obj V)
    (hτ :
      τ =
        ((((F.map h)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂V).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app
              𝒢).1.app (op V)) σ)) :
    ((((F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ W₂.toOpens from
            by
              intro x hx
              exact hx.2)).op
        τ =
      ((((F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ (Opens.map (F.map h)).obj V from
            by
              intro x hx
              exact hW₂V hx.2)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app
            𝒢).1.app (op V)) σ) := by
  -- Rewrite the right-branch section by its descended-unit description and compose the two
  -- restrictions into the single fixed-owner restriction to `W₁ ⊓ W₂`.
  calc
    ((((F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ W₂.toOpens from
            by
              intro x hx
              exact hx.2)).op
        τ =
      ((((F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ W₂.toOpens from
            by
              intro x hx
              exact hx.2)).op
        (((((F.map h)⁻¹).obj 𝒢).presheaf).map (homOfLE hW₂V).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app
              𝒢).1.app (op V)) σ)) := by
              simpa [hτ]
    _ =
      ((((F.map h)⁻¹).obj 𝒢).presheaf).map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ (Opens.map (F.map h)).obj V from
            by
              intro x hx
              exact hW₂V hx.2)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app
            𝒢).1.app (op V)) σ) := by
              simpa using
                (sheaf_section_restriction_comp_eq
                  (ℱ := ((F.map h)⁻¹).obj 𝒢)
                  (hWV := hW₂V)
                  (hRW := (show (W₁ ⊓ W₂).toOpens ≤ W₂.toOpens from
                    by
                      intro x hx
                      exact hx.2))
                  (σ := ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app
                    𝒢).1.app (op V)) σ)))

/-- Helper for Lemma 6.29.3: if a family on a common stage is already compatible in the nested
pullback sheaf `c⁻¹(h⁻¹ 𝒢)`, then applying `TopCat.Sheaf.pullbackComp.hom` produces the exact
pairwise overlap equality for the corresponding raw family in the compositional pullback sheaf
`(F.map c ≫ F.map h)⁻¹ 𝒢`. This isolates the naturality half of the final compatibility step,
before the outer reassociation cast to `F.map (c ≫ h)` is applied. -/
private theorem pullbackComp_hom_preserves_overlap_eq_raw
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i k l : I} (c : l ⟶ k) (h : k ⟶ i) (𝒢 : (F.obj i).Sheaf (Type u))
    {α : Type*} (W : α → CompactOpens (F.obj k))
    (u :
      ∀ a : α,
        ((((F.map c)⁻¹).obj (((F.map h)⁻¹).obj 𝒢)).presheaf).obj
          (op ((stage_pullback_compact_open (F := F) hF c (W a)).toOpens)))
    (hCompat :
      TopCat.Presheaf.IsCompatible
        ((((F.map c)⁻¹).obj (((F.map h)⁻¹).obj 𝒢)).presheaf)
        (fun a : α ↦ (stage_pullback_compact_open (F := F) hF c (W a)).toOpens)
        u)
    (q q' : α) :
    let uRaw :
        ∀ a : α,
          (((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map h)).obj 𝒢).presheaf).obj
            (op ((stage_pullback_compact_open (F := F) hF c (W a)).toOpens)) :=
      fun a ↦
        ((((TopCat.Sheaf.pullbackComp (A := Type u) (F.map c) (F.map h)).hom.app 𝒢).1.app
            (op ((stage_pullback_compact_open (F := F) hF c (W a)).toOpens))))
          (u a)
    (((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map h)).obj 𝒢).presheaf).map
        (((stage_pullback_compact_open (F := F) hF c (W q)).toOpens).infLELeft
          ((stage_pullback_compact_open (F := F) hF c (W q')).toOpens)).op
        (uRaw q) =
      (((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map h)).obj 𝒢).presheaf).map
        (((stage_pullback_compact_open (F := F) hF c (W q)).toOpens).infLERight
          ((stage_pullback_compact_open (F := F) hF c (W q')).toOpens)).op
        (uRaw q') := by
  let Oq : Opens (F.obj l) :=
    (stage_pullback_compact_open (F := F) hF c (W q)).toOpens
  let Oq' : Opens (F.obj l) :=
    (stage_pullback_compact_open (F := F) hF c (W q')).toOpens
  let R : Opens (F.obj l) := Oq ⊓ Oq'
  let uRaw :
      ∀ a : α,
        (((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map h)).obj 𝒢).presheaf).obj
          (op ((stage_pullback_compact_open (F := F) hF c (W a)).toOpens)) :=
    fun a ↦
      ((((TopCat.Sheaf.pullbackComp (A := Type u) (F.map c) (F.map h)).hom.app 𝒢).1.app
          (op ((stage_pullback_compact_open (F := F) hF c (W a)).toOpens))))
        (u a)
  have hComp :=
    congrArg
      ((((TopCat.Sheaf.pullbackComp (A := Type u) (F.map c) (F.map h)).hom.app 𝒢).1.app
          (op R)))
      (hCompat q q')
  have hLeft :
      (((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map h)).obj 𝒢).presheaf).map
          (Oq.infLELeft Oq').op
          (uRaw q) =
        (((TopCat.Sheaf.pullbackComp (A := Type u) (F.map c) (F.map h)).hom.app 𝒢).1.app
            (op R))
          (((((F.map c)⁻¹).obj (((F.map h)⁻¹).obj 𝒢)).presheaf).map
            (Oq.infLELeft Oq').op
            (u q)) := by
    -- Naturality of `pullbackComp.hom` identifies restriction after transport with transport
    -- after restriction on the left overlap map.
    simpa [uRaw, Oq, Oq', R] using
      (pullbackComp_hom_restriction_eq
        (f := F.map c) (g := F.map h) (𝒢 := 𝒢)
        (W := Oq) (R := R)
        (hRW := show R ≤ Oq by
          intro x hx
          exact hx.1)
        (σ := u q)).symm
  have hRight :
      (((TopCat.Sheaf.pullbackComp (A := Type u) (F.map c) (F.map h)).hom.app 𝒢).1.app
          (op R))
        (((((F.map c)⁻¹).obj (((F.map h)⁻¹).obj 𝒢)).presheaf).map
          (Oq.infLERight Oq').op
          (u q')) =
      (((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map h)).obj 𝒢).presheaf).map
          (Oq.infLERight Oq').op
          (uRaw q') := by
    -- The same naturality rewrite converts the right overlap map into the explicit raw family.
    simpa [uRaw, Oq, Oq', R] using
      (pullbackComp_hom_restriction_eq
        (f := F.map c) (g := F.map h) (𝒢 := 𝒢)
        (W := Oq') (R := R)
        (hRW := show R ≤ Oq' by
          intro x hx
          exact hx.2)
        (σ := u q'))
  exact hLeft.trans (hComp.trans hRight)

/-- Helper for Lemma 6.29.3: the swapped exact-overlap normalization can be transported back to
the fixed overlap owner `(W₁ ⊓ W₂).toOpens`, producing the precise right-branch restriction shape
needed in the final common-stage compatibility proof. -/
private theorem overPullbackSectionsMap_overlap_owner_transport
    [∀ i : I, SpectralSpace (F.obj i)]
    {k l : I} (c : l ⟶ k) (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (ℋ : (F.obj k).Sheaf (Type u)) (W₁ W₂ : CompactOpens (F.obj k))
    (σ : ℋ.1.obj (op W₂.toOpens)) :
    let R : Opens (F.obj k) := (W₁ ⊓ W₂).toOpens
    let σR : ℋ.1.obj (op R) :=
      ℋ.1.map
        (homOfLE
          (show (W₁ ⊓ W₂).toOpens ≤ W₂.toOpens from
            by
              intro x hx
              exact hx.2)).op
        σ
    let σidR : ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
        (op ((Opens.map (F.map (𝟙 k))).obj R)) := by
          simpa [σR] using
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (𝟙 (F.obj k))).leftAdjointIdIso
              (eqToIso rfl)).inv.app ℋ).1.app (op R) σR)
    overPullbackSectionsMap F ℋ R
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) σidR =
      ((((F.map c)⁻¹).obj ℋ).presheaf).map
        (homOfLE
          (stage_pullback_compact_open_inf_le_right
            (F := F) hF c W₁ W₂)).op
        (overPullbackSectionsMap F ℋ W₂.toOpens
          (A := Over.mk c) (B := Over.mk (𝟙 k))
          (Over.homMk c (by simp)) (by
            simpa using
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                  (𝟙 (F.obj k))).leftAdjointIdIso
                (eqToIso rfl)).inv.app ℋ).1.app (op W₂.toOpens) σ))) := by
  have hR :
      (W₁ ⊓ W₂).toOpens ≤ W₂.toOpens := by
    -- The fixed overlap owner already sits inside the right branch by projection to the second
    -- factor.
    intro x hx
    exact hx.2
  -- Route correction: the desired fixed-owner statement is exactly the general restriction
  -- normalization specialized to the right inclusion `R ≤ W₂`, so no separate swapped-owner
  -- transport is needed here.
  simpa using
    (overPullbackSectionsMap_identity_over_stage_restrict_eq
      (F := F) (c := c) (ℋ := ℋ)
      (W := W₂.toOpens) (R := (W₁ ⊓ W₂).toOpens)
      hR σ).symm

/-- Helper for Lemma 6.29.3: a set-level equality describing a descended stage cover upgrades to
the corresponding opens-level cover inequality. This is the exact bridge needed before invoking
sheaf gluing or coverwise extensionality on the refined compact-open family. -/
private theorem stage_pullback_compact_open_cover_le_iSup
    [∀ i : I, SpectralSpace (F.obj i)]
    {i j : I} (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (a : j ⟶ i) (U : CompactOpens (F.obj i))
    {α : Type*} (W : α → CompactOpens (F.obj j))
    (hCover :
      ((stage_pullback_compact_open (F := F) hF a U : CompactOpens (F.obj j)) :
          Set (F.obj j)) =
        ⋃ q : α, ((W q : CompactOpens (F.obj j)) : Set (F.obj j))) :
    (stage_pullback_compact_open (F := F) hF a U).toOpens ≤
      iSup (fun q : α ↦ (W q).toOpens) := by
  -- Read the set-level cover as membership in one concrete compact-open piece, then package that
  -- witness into the corresponding `iSup`-cover on opens.
  intro x hx
  have hx' :
      x ∈ ((stage_pullback_compact_open (F := F) hF a U : CompactOpens (F.obj j)) :
        Set (F.obj j)) := by
    simpa using hx
  rw [hCover] at hx'
  rcases Set.mem_iUnion.mp hx' with ⟨q, hxq⟩
  exact Opens.mem_iSup.2 ⟨q, by simpa using hxq⟩

/-- Helper for Lemma 6.29.3: once a stage-`k` compact-open piece lies in `h⁻¹(V)`, its pullback to
any further stage `l` lies in `(c ≫ h)⁻¹(V)`. This packages the local-open inclusion that remains
available after passing from the stage-`k` cover to the refined stage-`l` cover used in the final
stalkwise comparison. -/
private theorem refined_stage_pullback_piece_le_stage_pullback
    [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i k l : I} (h : k ⟶ i) (c : l ⟶ k) (W : CompactOpens (F.obj k))
    {V : Opens (F.obj i)}
    (hWV : W.toOpens ≤ (Opens.map (F.map h)).obj V) :
    (stage_pullback_compact_open (F := F) hF c W).toOpens ≤
      (Opens.map (F.map (c ≫ h))).obj V := by
  -- The refined point maps into `W` under `F.map c`, and the original inclusion `hWV` then places
  -- that image inside `h⁻¹(V)`.
  intro y hy
  simpa [Functor.map_comp] using hWV (by simpa [stage_pullback_compact_open] using hy)

/-- Helper for Lemma 6.29.3: if a point of the limit lies over `p_i^{-1}(U_i)`, then after
descending the finite stage-`k` cover and pulling it back further to stage `l`, the point lies in
one concrete refined cover piece. This is the geometric witness later used when the final
stalkwise extensionality argument chooses a local piece through a given limit point. -/
private theorem exists_refined_cover_piece_through_limit_point
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j k l : I} (g : j ⟶ i) (b : k ⟶ j) (c : l ⟶ k)
    (Ui : CompactOpens (F.obj i))
    {α : Type*} (Wk : α → CompactOpens (F.obj k))
    (hWkCover :
      ((stage_pullback_compact_open (F := F) hF (b ≫ g) Ui : CompactOpens (F.obj k)) :
          Set (F.obj k)) =
        ⋃ q : α, ((Wk q : CompactOpens (F.obj k)) : Set (F.obj k)))
    {x : ↥(limit F)}
    (hx : x ∈ (Opens.map (limit.π F i)).obj Ui.toOpens) :
    ∃ q : α,
      x ∈ projection_preimage_open (F := F)
        ⟨l, stage_pullback_compact_open (F := F) hF c (Wk q)⟩ := by
  have hxStage :
      x ∈ projection_preimage_open (F := F)
        ⟨l, stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui⟩ := by
    -- Rewrite the target pullback open along `limit.w` so the limit-side membership `hx`
    -- becomes a concrete membership statement on stage `l`.
    have hx' : (limit.π F l) x ∈
        ((stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui : CompactOpens (F.obj l)) :
          Set (F.obj l)) := by
      change F.map (c ≫ b ≫ g) ((limit.π F l) x) ∈ (Ui : Set (F.obj i))
      have hπ :
          F.map (c ≫ b ≫ g) ((limit.π F l) x) = (limit.π F i) x := by
        exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F (c ≫ b ≫ g))) x
      rw [hπ]
      exact hx
    simpa [projection_preimage_open, projection_preimage_basis] using hx'
  have hWlCover :
      ((stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui : CompactOpens (F.obj l)) :
          Set (F.obj l)) =
        ⋃ q : α,
          ((stage_pullback_compact_open (F := F) hF c (Wk q) : CompactOpens (F.obj l)) :
            Set (F.obj l)) := by
    -- Pull back the stage-`k` cover further along `c`.
    have hPullbackCover :
        (F.map c) ⁻¹'
            ((stage_pullback_compact_open (F := F) hF (b ≫ g) Ui : CompactOpens (F.obj k)) :
              Set (F.obj k)) =
          ⋃ q : α, (F.map c) ⁻¹' ((Wk q : CompactOpens (F.obj k)) : Set (F.obj k)) := by
      ext y
      simpa using congrArg (fun s : Set (F.obj k) ↦ y ∈ (F.map c) ⁻¹' s) hWkCover
    simpa using
      (stage_pullback_compact_open_cover_eq
        (F := F) hF (b ≫ g) Ui Wk c hPullbackCover)
  have hxUnion :
      (limit.π F l) x ∈
        ⋃ q : α,
          ((stage_pullback_compact_open (F := F) hF c (Wk q) : CompactOpens (F.obj l)) :
            Set (F.obj l)) := by
    have hx' :
        (limit.π F l) x ∈
          ((stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui :
            CompactOpens (F.obj l)) : Set (F.obj l)) := by
      simpa [projection_preimage_open, projection_preimage_basis] using hxStage
    simpa [hWlCover] using hx'
  rcases Set.mem_iUnion.mp hxUnion with ⟨q, hxq⟩
  refine ⟨q, ?_⟩
  simpa [projection_preimage_open, projection_preimage_basis] using hxq

/-- Helper for Lemma 6.29.3: if a point lies in a refined cover piece over `Wk`, then the germ of
the global limit section `s` equals the germ of the corresponding local `p_i`-pullback-unit
section at that point. This packages the `hEqk` comparison together with the passage from the
refined piece back to the original stage-`k` cover piece. -/
private theorem limit_section_germ_eq_stage_unit_on_refined_piece
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i k l : I} (c : l ⟶ k) (𝒢 : (F.obj i).Sheaf (Type u))
    {U V : Opens (F.obj i)}
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    (Wk : CompactOpens (F.obj k))
    (hWkU : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
      (Opens.map (limit.π F i)).obj U)
    (hWkV : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
      (Opens.map (limit.π F i)).obj V)
    (σ : 𝒢.1.obj (op V))
    (hEq :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V)) σ))
    {x : ↥(limit F)}
    (hx : x ∈ projection_preimage_open (F := F)
      ⟨l, stage_pullback_compact_open (F := F) hF c Wk⟩) :
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
        ((Opens.map (limit.π F i)).obj U) x
        (hWkU <|
          (limit_projection_preimage_le_of_stage_le (F := F) (h := c)
            (W := (stage_pullback_compact_open (F := F) hF c Wk).toOpens)
            (V := Wk.toOpens)
            (by
              intro y hy
              simpa [stage_pullback_compact_open] using hy)) hx)
        s =
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
        ((Opens.map (limit.π F i)).obj V) x
        (hWkV <|
          (limit_projection_preimage_le_of_stage_le (F := F) (h := c)
            (W := (stage_pullback_compact_open (F := F) hF c Wk).toOpens)
            (V := Wk.toOpens)
            (by
              intro y hy
              simpa [stage_pullback_compact_open] using hy)) hx)
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
            𝒢).1.app (op V)) σ) := by
  have hxk :
      x ∈ projection_preimage_open (F := F) ⟨k, Wk⟩ :=
    (limit_projection_preimage_le_of_stage_le (F := F) (h := c)
      (W := (stage_pullback_compact_open (F := F) hF c Wk).toOpens)
      (V := Wk.toOpens)
      (by
        intro y hy
        simpa [stage_pullback_compact_open] using hy)) hx
  have hGermEq :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
          (projection_preimage_open (F := F) ⟨k, Wk⟩) x hxk
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
          (projection_preimage_open (F := F) ⟨k, Wk⟩) x hxk
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V)) σ)) := by
    -- Apply the section equality on `p_k⁻¹(Wk)` to the germ at the chosen limit point.
    exact
      congrArg
        (((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
          (projection_preimage_open (F := F) ⟨k, Wk⟩) x hxk)
        hEq
  have hsRes :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
          (projection_preimage_open (F := F) ⟨k, Wk⟩) x hxk
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (limit.π F i)).obj U) x (hWkU hxk) s := by
    -- Restricting `s` to the stage-`k` cover piece does not change its germ there.
    simpa using
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ_res_apply
        (homOfLE hWkU) x hxk s
  have hσRes :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
          (projection_preimage_open (F := F) ⟨k, Wk⟩) x hxk
          (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                𝒢).1.app (op V)) σ)) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
          ((Opens.map (limit.π F i)).obj V) x (hWkV hxk)
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
              𝒢).1.app (op V)) σ) := by
    -- The same restriction-to-germ identity applies to the local pullback-unit representative.
    simpa using
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ_res_apply
        (homOfLE hWkV) x hxk
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
          𝒢).1.app (op V)) σ)
  exact hsRes.symm.trans (hGermEq.trans hσRes)

/-- Helper for Lemma 6.29.3: if a glued common-stage section is already normalized on a source
open `O`, then the image of the global glued section in the limit, restricted to `p_l⁻¹(O)`,
matches the direct `p_i`-pullback-unit section on that same refined piece. This is the exact
section-level bridge used in the last refined-piece stalk comparison. -/
private theorem glued_limit_image_restrict_eq_stage_unit_on_source_open
    {i l : I} (h : l ⟶ i) (𝒢 : (F.obj i).Sheaf (Type u))
    {U V : Opens (F.obj i)} {O : Opens (F.obj l)}
    (glU :
      ((((F.map h)⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map h)).obj U)))
    (σ : 𝒢.1.obj (op V))
    (hOU : O ≤ (Opens.map (F.map h)).obj U)
    (hOV : O ≤ (Opens.map (F.map h)).obj V)
    (hτ :
      ((((F.map h)⁻¹).obj 𝒢).presheaf).map (homOfLE hOU).op glU =
        ((((F.map h)⁻¹).obj 𝒢).presheaf).map (homOfLE hOV).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map h)).unit.app 𝒢).1.app
              (op V)) σ)) :
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
        (homOfLE (limit_projection_preimage_le_of_stage_le (F := F) (h := h) hOU)).op
        (pullbackSectionsToLimitMap F 𝒢 U (Over.mk h) glU) =
    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
        (homOfLE (limit_projection_preimage_le_of_stage_le (F := F) (h := h) hOV)).op
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
            (op V)) σ) := by
  let τ : ((((F.map h)⁻¹).obj 𝒢).presheaf).obj (op O) :=
    ((((F.map h)⁻¹).obj 𝒢).presheaf).map (homOfLE hOU).op glU
  let τid :
      ((((F.map (𝟙 l))⁻¹).obj (((F.map h)⁻¹).obj 𝒢)).presheaf).obj
        (op ((Opens.map (F.map (𝟙 l))).obj O)) := by
        simpa [τ] using
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj l))).leftAdjointIdIso
              (eqToIso rfl)).inv.app (((F.map h)⁻¹).obj 𝒢)).1.app (op O) τ)
  let hπOU :
      (Opens.map (limit.π F l)).obj O ≤
        (Opens.map (limit.π F l)).obj ((Opens.map (F.map h)).obj U) := by
    intro x hx
    exact hOU hx
  let hCast :
      ((((TopCat.Sheaf.pullback (Type u) (limit.π F l ≫ F.map h)).obj 𝒢).presheaf).obj
        (op ((Opens.map (limit.π F l)).obj O))) =
      ((((TopCat.Sheaf.pullback (Type u) (limit.π F i)).obj 𝒢).presheaf).obj
        (op ((Opens.map (limit.π F l)).obj O))) := by
    simpa [Functor.map_comp] using
      congrArg
        (fun f : limit F ⟶ F.obj i ↦
          ((((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj
            (op ((Opens.map (limit.π F l)).obj O))))
        (limit.w F h)
  have hOpenU :
      (Opens.map (limit.π F l)).obj ((Opens.map (F.map h)).obj U) =
        (Opens.map (limit.π F i)).obj U := by
    ext x
    change F.map h ((limit.π F l) x) ∈ U ↔ (limit.π F i) x ∈ U
    have hπ : F.map h ((limit.π F l) x) = (limit.π F i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F h)) x
    rw [hπ]
  have hLocalize :
      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (limit_projection_preimage_le_of_stage_le (F := F) (h := h) hOU)).op
          (pullbackSectionsToLimitMap F 𝒢 U (Over.mk h) glU) =
        cast hCast
          ((((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F l) (F.map h)).hom.app 𝒢).1.app
              (op ((Opens.map (limit.π F l)).obj O)))
            (pullbackSectionsToLimitMap F (((F.map h)⁻¹).obj 𝒢) O (Over.mk (𝟙 l)) τid)) := by
    -- Restrict the global limit image to `p_l⁻¹(O)` and rewrite it as the localized branch over
    -- `O`, still before collapsing the composite pullback to the direct `p_i` branch.
    have hCastRestrict :
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
            (homOfLE (limit_projection_preimage_le_of_stage_le (F := F) (h := h) hOU)).op
            (pullbackSectionsToLimitMap F 𝒢 U (Over.mk h) glU) =
          cast hCast
            (((((TopCat.Sheaf.pullback (Type u) (limit.π F l ≫ F.map h)).obj 𝒢).presheaf).map
                (homOfLE hπOU).op)
              (iteratedPullbackSectionsMap (limit.π F l) (F.map h) 𝒢 U glU)) := by
      -- This is exactly the generic restriction/cast commutation for `limit.w F h`, specialized
      -- to the iterated pullback section over `U`.
      dsimp [pullbackSectionsToLimitMap]
      have hCast_eq :
          (by
            simpa using
              congrArg
                (fun f : limit F ⟶ F.obj i ↦
                  (((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj
                    (op ((Opens.map (limit.π F l)).obj O)))
              (limit.w F h)) = hCast := by
        apply Subsingleton.elim
      have hmain :=
        limit_pullback_section_restriction_cast_eq_source_open
          (F := F) (h := h) (𝒢 := 𝒢) hOU
          (σ := iteratedPullbackSectionsMap (limit.π F l) (F.map h) 𝒢 U glU)
      convert hmain using 1 <;> apply Subsingleton.elim
    have hIterated :
        (((((TopCat.Sheaf.pullback (Type u) (limit.π F l ≫ F.map h)).obj 𝒢).presheaf).map
            (homOfLE hπOU).op)
          (iteratedPullbackSectionsMap (limit.π F l) (F.map h) 𝒢 U glU)) =
          (((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F l) (F.map h)).hom.app 𝒢).1.app
              (op ((Opens.map (limit.π F l)).obj O)))
            (pullbackSectionsToLimitMap F (((F.map h)⁻¹).obj 𝒢) O (Over.mk (𝟙 l)) τid) := by
      -- Commute restriction past the pullback unit and the `pullbackComp` comparison, then
      -- rewrite the identity-over-stage branch on `O` by the dedicated normalization theorem.
      let ηU :
          ((((TopCat.Sheaf.pullback (Type u) (limit.π F l)).obj (((F.map h)⁻¹).obj 𝒢)).presheaf).obj
            (op ((Opens.map (limit.π F l)).obj ((Opens.map (F.map h)).obj U)))) :=
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F l)).unit.app
            (((F.map h)⁻¹).obj 𝒢)).1.app (op ((Opens.map (F.map h)).obj U))) glU)
      let ηO :
          ((((TopCat.Sheaf.pullback (Type u) (limit.π F l)).obj (((F.map h)⁻¹).obj 𝒢)).presheaf).obj
            (op ((Opens.map (limit.π F l)).obj O))) :=
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F l)).unit.app
            (((F.map h)⁻¹).obj 𝒢)).1.app (op O)) τ)
      let eU :=
        (((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F l) (F.map h)).hom.app 𝒢).1.app
          (op ((Opens.map (limit.π F l)).obj ((Opens.map (F.map h)).obj U))))
      let eO :=
        (((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F l) (F.map h)).hom.app 𝒢).1.app
          (op ((Opens.map (limit.π F l)).obj O)))
      calc
        (((((TopCat.Sheaf.pullback (Type u) (limit.π F l ≫ F.map h)).obj 𝒢).presheaf).map
            (homOfLE hπOU).op)
          (iteratedPullbackSectionsMap (limit.π F l) (F.map h) 𝒢 U glU)) =
          eO ηO := by
            dsimp [iteratedPullbackSectionsMap]
            have hCompRestrict :
                (((((TopCat.Sheaf.pullback (Type u) (limit.π F l ≫ F.map h)).obj 𝒢).presheaf).map
                    (homOfLE hπOU).op) (eU ηU)) =
                  eO
                    (((((TopCat.Sheaf.pullback (Type u) (limit.π F l)).obj
                        (((F.map h)⁻¹).obj 𝒢)).presheaf).map (homOfLE hπOU).op) ηU) := by
              simpa [eU, eO, ηU] using
                (pullbackComp_hom_restriction_eq
                  (f := limit.π F l) (g := F.map h) (𝒢 := 𝒢)
                  (hRW := hπOU)
                  (σ := ηU)).symm
            have hUnitRestrict :
                (((((TopCat.Sheaf.pullback (Type u) (limit.π F l)).obj
                        (((F.map h)⁻¹).obj 𝒢)).presheaf).map
                    (homOfLE hπOU).op) ηU) = ηO := by
              simpa [ηU, ηO, τ] using
                (pullback_unit_section_restriction_eq
                  (f := limit.π F l) (ℋ := ((F.map h)⁻¹).obj 𝒢)
                  (hRW := hOU) (σ := glU)).symm
            exact hCompRestrict.trans <|
              congrArg eO hUnitRestrict
        _ =
          eO (pullbackSectionsToLimitMap F (((F.map h)⁻¹).obj 𝒢) O (Over.mk (𝟙 l)) τid) := by
            simpa [eO, ηO, τid] using
              congrArg eO
                (pullbackSectionsToLimitMap_identity_over_stage_eq_unit
                  (F := F) (ℋ := ((F.map h)⁻¹).obj 𝒢) (U0 := O) (σ := τ)).symm
    exact hCastRestrict.trans <| by simpa [hCast] using congrArg (cast hCast) hIterated
  have hCollapse :
      cast hCast
        ((((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F l) (F.map h)).hom.app 𝒢).1.app
            (op ((Opens.map (limit.π F l)).obj O)))
          (pullbackSectionsToLimitMap F (((F.map h)⁻¹).obj 𝒢) O (Over.mk (𝟙 l)) τid)) =
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
          (homOfLE (limit_projection_preimage_le_of_stage_le (F := F) (h := h) hOV)).op
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app 𝒢).1.app
              (op V)) σ) := by
    -- Collapse the localized branch on `O` to the direct `p_i`-pullback-unit section.
    simpa [hCast, τid, τ] using
      congrArg (cast hCast) <|
        (pullback_comp_limit_unit_restriction_eq
        (F := F) (h := h) (𝒢 := 𝒢) (W := O) (V := V)
        (σ := σ) (τ := τ) (hWV := hOV)
        (hτ := by simpa [τ] using hτ))
  exact hLocalize.trans hCollapse

/-- Helper for Lemma 6.29.3: after all local representatives have been moved to one common stage
and the finite limit-side cover has been descended to an actual cover on a refinement stage, the
remaining source-faithful task is to normalize each descended local section on that stage cover,
refine finitely many overlap equalities to one common stage, and glue there. This theorem isolates
that last section-theoretic endgame so the main surjectivity proof no longer ends in one
monolithic `sorry`. -/
private theorem same_stage_descended_sections_glue_after_common_refinement
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : I} (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i))
    (hU : IsCompact (U : Set (F.obj i)))
    (s : (((limit.π F i)⁻¹).obj 𝒢).presheaf.obj (op ((Opens.map (limit.π F i)).obj U)))
    (t : Finset (LocalStageSectionDatum (F := F) i 𝒢))
    {j : I} {g : j ⟶ i}
    (Ui : CompactOpens (F.obj i)) (hUi : Ui.toOpens = U)
    (W : {q // q ∈ t} → CompactOpens (F.obj j))
    (hW :
      ∀ q : {q // q ∈ t},
        CommonStageLocalSectionOn (F := F) 𝒢 U s q.1 (g := g) (W q))
    (hStageCover :
      (limit.π F j) ⁻¹'
          ((stage_pullback_compact_open (F := F) hF g Ui : CompactOpens (F.obj j)) :
            Set (F.obj j)) =
        ⋃ q : {q // q ∈ t}, (limit.π F j) ⁻¹' (W q : Set (F.obj j)))
    {k : I} (b : k ⟶ j)
    (hbCover :
      (F.map b) ⁻¹'
          ((stage_pullback_compact_open (F := F) hF g Ui : CompactOpens (F.obj j)) :
            Set (F.obj j)) =
        ⋃ q : {q // q ∈ t}, (F.map b) ⁻¹' (W q : Set (F.obj j))) :
    ∃ a, limitPullbackSectionsColimitMap F i 𝒢 U a = s := by
  have hPulledBackLocal :
      ∀ q : {q // q ∈ t},
        let Wk := stage_pullback_compact_open (F := F) hF b (W q)
        ∃ hWkU : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
            (Opens.map (limit.π F i)).obj U,
          ∃ hWkV : projection_preimage_open (F := F) ⟨k, Wk⟩ ≤
              (Opens.map (limit.π F i)).obj q.1.2.2.1.toOpens,
            ∃ hWkVi : Wk.toOpens ≤ (Opens.map (F.map (b ≫ g))).obj q.1.2.2.1.toOpens,
              ∃ τk : ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).obj (op Wk.toOpens),
                τk =
                  ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).map (homOfLE hWkVi).op
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                        (F.map (b ≫ g))).unit.app 𝒢).1.app
                          (op q.1.2.2.1.toOpens)) q.1.2.2.2) ∧
                ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkU).op s =
                  ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWkV).op
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                        (limit.π F i)).unit.app 𝒢).1.app
                          (op q.1.2.2.1.toOpens)) q.1.2.2.2) := by
    intro q
    -- The actual stage-cover pieces from `hbCover` now carry the descended local section data.
    simpa using
      (descended_common_stage_section_limit_image_eq_restriction
        (F := F) hF 𝒢 U s q.1 (W q) (hW q) (b := b))
  choose hWkU hWkV hWkVi τk hτk hEqk using hPulledBackLocal
  let Wk : {q // q ∈ t} → CompactOpens (F.obj k) :=
    fun q ↦ stage_pullback_compact_open (F := F) hF b (W q)
  have hWkCover :
      ((stage_pullback_compact_open (F := F) hF (b ≫ g) Ui : CompactOpens (F.obj k)) :
          Set (F.obj k)) =
        ⋃ q : {q // q ∈ t}, ((Wk q : CompactOpens (F.obj k)) : Set (F.obj k)) := by
    -- Rewrite the descended stage cover directly in terms of the compact opens `Wk q`.
    simpa [Wk] using
      (stage_pullback_compact_open_cover_eq
        (F := F) hF g Ui W b hbCover)
  have hOverlapExact :
      ∀ q q' : {q // q ∈ t},
        ∃ hR₁ : projection_preimage_open (F := F) ⟨k, Wk q ⊓ Wk q'⟩ ≤
            projection_preimage_open (F := F) ⟨k, Wk q⟩,
          ∃ hR₂ : projection_preimage_open (F := F) ⟨k, Wk q ⊓ Wk q'⟩ ≤
              projection_preimage_open (F := F) ⟨k, Wk q'⟩,
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
                (homOfLE (le_trans hR₁ (hWkV q))).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app (op q.1.2.2.1.toOpens)) q.1.2.2.2) =
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
                (homOfLE (le_trans hR₂ (hWkV q'))).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                    𝒢).1.app (op q'.1.2.2.1.toOpens)) q'.1.2.2.2) := by
    intro q q'
    -- The overlap equality now lives on the exact compact-open overlap `Wk q ⊓ Wk q'`.
    simpa [Wk] using
      (exact_overlap_limit_unit_sections_eq
        (F := F) 𝒢 U s (Wk q) (Wk q')
        q.1.2.2.2 q'.1.2.2.2 (hWkU q) (hWkU q') (hWkV q) (hWkV q') (hEqk q) (hEqk q'))
  have hOverlapLimit :
      ∀ q q' : {q // q ∈ t},
        ∃ hR₁ : projection_preimage_open (F := F) ⟨k, Wk q ⊓ Wk q'⟩ ≤
            projection_preimage_open (F := F) ⟨k, Wk q⟩,
          ∃ hR₂ : projection_preimage_open (F := F) ⟨k, Wk q ⊓ Wk q'⟩ ≤
              projection_preimage_open (F := F) ⟨k, Wk q'⟩,
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₁).op
                (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
                    (homOfLE (hWkV q)).op
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                        𝒢).1.app (op q.1.2.2.1.toOpens)) q.1.2.2.2)) =
              ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hR₂).op
                (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
                    (homOfLE (hWkV q')).op
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                        𝒢).1.app (op q'.1.2.2.1.toOpens)) q'.1.2.2.2)) := by
    intro q q'
    -- The exact-overlap comparison is already the desired two-step restriction equality after the
    -- standalone overlap-normalization helper is applied.
    exact
      exact_overlap_limit_unit_sections_eq_two_step_restriction
        (F := F) (𝒢 := 𝒢) (W₁ := Wk q) (W₂ := Wk q')
        q.1.2.2.2 q'.1.2.2.2 (hWkV q) (hWkV q') (hOverlapExact q q')
  have hRestrictedStageSections :
      ∀ q q' : {q // q ∈ t},
        ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).map
            (homOfLE (show (Wk q ⊓ Wk q').toOpens ≤ (Wk q).toOpens from inf_le_left)).op
            (τk q) =
          ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).map
              (homOfLE
                (show (Wk q ⊓ Wk q').toOpens ≤
                    (Opens.map (F.map (b ≫ g))).obj q.1.2.2.1.toOpens from
                  le_trans inf_le_left (hWkVi q))).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map (b ≫ g))).unit.app
                  𝒢).1.app (op q.1.2.2.1.toOpens)) q.1.2.2.2) := by
    intro q q'
    -- The restricted stage section is exactly the restricted pullback-unit section after the
    -- standalone source-side normalization helper is applied.
    exact
      restricted_stage_section_eq_two_step_restriction
        (F := F) (h := b ≫ g) (𝒢 := 𝒢) q.1.2.2.2 (τk q) (hWkVi q) (hτk q)
  -- The local data is now normalized on the concrete stage cover `Wk`, and the overlap equality is
  -- no longer hidden behind an arbitrary auxiliary open: `hOverlapExact` already identifies the
  -- two limit-side unit sections on the exact overlap `projection_preimage_open ⟨k, Wk q ⊓ Wk q'⟩`.
  -- The new normalizations `hOverlapLimit` and `hRestrictedStageSections` remove the remaining
  -- ambiguity about whether we are viewing those terms as single-step or two-step restrictions.
  classical
  have hExistsCommonStageGluing :
      ∀ {l : I} (c : l ⟶ k)
        (u :
          ∀ q : {q // q ∈ t},
            ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).obj
              (op ((stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens)))
        (hCompat :
          TopCat.Presheaf.IsCompatible
            ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf)
            (fun q : {q // q ∈ t} ↦
              (stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens)
            u),
        ∃ gl :
            ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).obj
              (op ((stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui).toOpens)),
          ∀ q : {q // q ∈ t},
            ∃ iUVq :
                (stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens ⟶
                  (stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui).toOpens,
              ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).map iUVq.op gl = u q := by
    intro l c u hCompat
    let Wl : {q // q ∈ t} → CompactOpens (F.obj l) :=
      fun q ↦ stage_pullback_compact_open (F := F) hF c (Wk q)
    have hPullbackWkCover :
        (F.map c) ⁻¹'
            ((stage_pullback_compact_open (F := F) hF (b ≫ g) Ui : CompactOpens (F.obj k)) :
              Set (F.obj k)) =
          ⋃ q : {q // q ∈ t}, (F.map c) ⁻¹' ((Wk q : CompactOpens (F.obj k)) : Set (F.obj k)) := by
      ext x
      simpa using congrArg (fun s : Set (F.obj k) ↦ x ∈ (F.map c) ⁻¹' s) hWkCover
    have hWlCover :
        ((stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui : CompactOpens (F.obj l)) :
            Set (F.obj l)) =
          ⋃ q : {q // q ∈ t}, ((Wl q : CompactOpens (F.obj l)) : Set (F.obj l)) := by
      -- Pull the already-descended stage-`k` cover further back along `c`.
      simpa [Wl] using
        (stage_pullback_compact_open_cover_eq
          (F := F) hF (b ≫ g) Ui Wk c hPullbackWkCover)
    have hWlCoverOpens :
        (stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui).toOpens ≤
          iSup (fun q : {q // q ∈ t} ↦ (Wl q).toOpens) := by
      -- The refined set-level cover `hWlCover` is exactly the opens-level cover inequality needed
      -- by `existsUnique_gluing'`.
      exact
        stage_pullback_compact_open_cover_le_iSup
          (F := F) hF (c ≫ b ≫ g) Ui Wl hWlCover
    obtain ⟨gl, hgl, -⟩ :=
      (((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).existsUnique_gluing'
        (U := fun q : {q // q ∈ t} ↦ (Wl q).toOpens)
        (V := (stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui).toOpens)
        (iUV := fun q ↦ homOfLE <|
          show (Wl q).toOpens ≤
              (stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui).toOpens from
            by
              intro x hx
              have hx' :
                  x ∈ ((Wl q : CompactOpens (F.obj l)) : Set (F.obj l)) := by
                simpa [Wl] using hx
              have hx'' :
                  x ∈ ((stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui :
                    CompactOpens (F.obj l)) : Set (F.obj l)) := by
                rw [hWlCover]
                exact Set.mem_iUnion.2 ⟨q, hx'⟩
              simpa using hx'')
        hWlCoverOpens u hCompat
    refine ⟨gl, ?_⟩
    intro q
    refine ⟨homOfLE ?_, ?_⟩
    · intro x hx
      have hx' :
          x ∈ ((Wl q : CompactOpens (F.obj l)) : Set (F.obj l)) := by
        simpa [Wl] using hx
      have hx'' :
          x ∈ ((stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui :
            CompactOpens (F.obj l)) : Set (F.obj l)) := by
        rw [hWlCover]
        exact Set.mem_iUnion.2 ⟨q, hx'⟩
      simpa using hx''
    · simpa [Wl] using hgl q
  -- Route correction: the right-unital comparison `pullbackComp (f, 𝟙)` is now available, so the
  -- old normalization gap has been reduced to a smaller interface issue. The remaining blocker is
  -- to package the raw overlap sections of `((F.map (b ≫ g))⁻¹).obj 𝒢` into the identity-over-`k`
  -- source expected by `common_refinement_of_equal_limit_pullback_sections`. The later sheaf
  -- gluing step is now packaged abstractly by `hExistsCommonStageGluing`, and the finite common
  -- domination / compatibility owners are now available separately; only the exact overlap
  -- transport bridge into `common_refinement_of_equal_limit_pullback_sections` is still missing.
  let ℋ : (F.obj k).Sheaf (Type u) := ((F.map (b ≫ g))⁻¹).obj 𝒢
  let σidW :
      ∀ q : {q // q ∈ t},
        ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj (Wk q).toOpens)) :=
    fun q ↦ by
      simpa [ℋ] using
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
          (eqToIso rfl)).inv.app ℋ).1.app (op (Wk q).toOpens) (τk q))
  have hOverlapRefined :
      ∀ q q' : {q // q ∈ t},
        ∃ (Bqq : Over k) (φqq : Bqq ⟶ Over.mk (𝟙 k)),
          let Rqq : Opens (F.obj k) := (Wk q ⊓ Wk q').toOpens
          let σqR : ℋ.1.obj (op Rqq) :=
            ℋ.1.map
              (homOfLE
                (show (Wk q ⊓ Wk q').toOpens ≤ (Wk q).toOpens from inf_le_left)).op
              (τk q)
          let σq'R : ℋ.1.obj (op Rqq) :=
            ℋ.1.map
              (homOfLE
                (show (Wk q ⊓ Wk q').toOpens ≤ (Wk q').toOpens from inf_le_right)).op
              (τk q')
          let σqRid :
              ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
                (op ((Opens.map (F.map (𝟙 k))).obj Rqq)) := by
                  simpa [σqR] using
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
                        (eqToIso rfl)).inv.app ℋ).1.app (op Rqq) σqR)
          let σq'Rid :
              ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
                (op ((Opens.map (F.map (𝟙 k))).obj Rqq)) := by
                  simpa [σq'R] using
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
                        (eqToIso rfl)).inv.app ℋ).1.app (op Rqq) σq'R)
          overPullbackSectionsMap F ℋ Rqq φqq σqRid =
            overPullbackSectionsMap F ℋ Rqq φqq σq'Rid := by
    intro q q'
    let Rqq : Opens (F.obj k) := (Wk q ⊓ Wk q').toOpens
    let σqR : ℋ.1.obj (op Rqq) :=
      ℋ.1.map
        (homOfLE
          (show (Wk q ⊓ Wk q').toOpens ≤ (Wk q).toOpens from inf_le_left)).op
        (τk q)
    let σq'R : ℋ.1.obj (op Rqq) :=
      ℋ.1.map
        (homOfLE
          (show (Wk q ⊓ Wk q').toOpens ≤ (Wk q').toOpens from inf_le_right)).op
        (τk q')
    let σqRid :
        ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj Rqq)) := by
            simpa [σqR] using
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
                  (eqToIso rfl)).inv.app ℋ).1.app (op Rqq) σqR)
    let σq'Rid :
        ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj Rqq)) := by
            simpa [σq'R] using
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
                  (eqToIso rfl)).inv.app ℋ).1.app (op Rqq) σq'R)
    have hLimitEq :
        pullbackSectionsToLimitMap F ℋ Rqq (Over.mk (𝟙 k)) σqRid =
          pullbackSectionsToLimitMap F ℋ Rqq (Over.mk (𝟙 k)) σq'Rid := by
      -- Route correction: first collapse the overlap equality into the exact identity-over-stage
      -- domain used by `common_refinement_of_equal_limit_pullback_sections`; only afterwards do we
      -- ask for a refinement stage.
      obtain ⟨hR₁, hR₂, hEqOverlap⟩ := hOverlapExact q q'
      have hLeftId :
          pullbackSectionsToLimitMap F ℋ Rqq (Over.mk (𝟙 k)) σqRid =
            ((((limit.π F k)⁻¹).obj ℋ).presheaf).map (homOfLE hR₁).op
              (pullbackSectionsToLimitMap F ℋ (Wk q).toOpens (Over.mk (𝟙 k)) (σidW q)) := by
        -- Restrict the identity-over-`k` image of the `q`-section from `Wk q` to the exact
        -- overlap owner `Rqq`.
        simpa [Rqq, σqR, σqRid, σidW] using
          (pullbackSectionsToLimitMap_identity_over_stage_restrict_eq_inf
            (F := F) (ℋ := ℋ) (W₁ := Wk q) (W₂ := Wk q') (σ := τk q))
      have hRightId :
          pullbackSectionsToLimitMap F ℋ Rqq (Over.mk (𝟙 k)) σq'Rid =
            ((((limit.π F k)⁻¹).obj ℋ).presheaf).map (homOfLE hR₂).op
              (pullbackSectionsToLimitMap F ℋ (Wk q').toOpens (Over.mk (𝟙 k)) (σidW q')) := by
        -- The same restriction normalization packages the right branch in the fixed overlap order.
        simpa [Rqq, σq'R, σq'Rid, σidW] using
          (pullbackSectionsToLimitMap_identity_over_stage_restrict_eq
            (F := F) (ℋ := ℋ)
            (W := (Wk q').toOpens) (R := Rqq)
            (show Rqq ≤ (Wk q').toOpens by
              intro x hx
              exact hx.2)
            (τk q'))
      let κR :=
        (((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F k) (F.map (b ≫ g))).hom.app
          𝒢).1.app (op ((Opens.map (limit.π F k)).obj Rqq)))
      let κWq :=
        (((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F k) (F.map (b ≫ g))).hom.app
          𝒢).1.app (op ((Opens.map (limit.π F k)).obj (Wk q).toOpens)))
      let κWq' :=
        (((TopCat.Sheaf.pullbackComp (A := Type u) (limit.π F k) (F.map (b ≫ g))).hom.app
          𝒢).1.app (op ((Opens.map (limit.π F k)).obj (Wk q').toOpens)))
      have hR₁k :
          (Opens.map (limit.π F k)).obj Rqq ≤
            (Opens.map (limit.π F k)).obj (Wk q).toOpens := by
        -- Rewrite the exact-overlap inclusion into the raw `Opens.map` form needed by
        -- `pullbackComp_hom_restriction_eq`.
        intro x hx
        exact hR₁ (by simpa [projection_preimage_open, projection_preimage_basis] using hx)
      have hR₂k :
          (Opens.map (limit.π F k)).obj Rqq ≤
            (Opens.map (limit.π F k)).obj (Wk q').toOpens := by
        -- The same translation applies to the right overlap inclusion.
        intro x hx
        exact hR₂ (by simpa [projection_preimage_open, projection_preimage_basis] using hx)
      have hCollapsedEq :
          κR (pullbackSectionsToLimitMap F ℋ Rqq (Over.mk (𝟙 k)) σqRid) =
            κR (pullbackSectionsToLimitMap F ℋ Rqq (Over.mk (𝟙 k)) σq'Rid) := by
        -- Route correction: rewrite each overlap branch directly to the corresponding `p_i`-side
        -- restriction term, so `hEqOverlap` can be used without another intermediate cast lemma.
        have eR :
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).obj
                (op ((Opens.map (limit.π F k)).obj Rqq)) =
              ((((limit.π F k ≫ F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).obj
                (op ((Opens.map (limit.π F k)).obj Rqq)) := by
          simpa using
            congrArg
              (fun f : limit F ⟶ F.obj i ↦
                ((((TopCat.Sheaf.pullback (Type u) f).obj 𝒢).presheaf).obj
                  (op ((Opens.map (limit.π F k)).obj Rqq))))
              (limit.w F (b ≫ g))
        have hLeftCollapsed :
            κR (pullbackSectionsToLimitMap F ℋ Rqq (Over.mk (𝟙 k)) σqRid) =
              cast eR
                (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
                    (homOfLE (le_trans hR₁ (hWkV q))).op
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                        (limit.π F i)).unit.app 𝒢).1.app
                          (op q.1.2.2.1.toOpens)) q.1.2.2.2)) := by
          have hτLeft :
              σqR =
                ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).map
                  (homOfLE
                    (show Rqq ≤ (Opens.map (F.map (b ≫ g))).obj q.1.2.2.1.toOpens from
                      by
                        intro x hx
                        exact hWkVi q hx.1)).op
                  ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                      (F.map (b ≫ g))).unit.app 𝒢).1.app
                        (op q.1.2.2.1.toOpens)) q.1.2.2.2) := by
            simpa [Rqq, σqR] using hRestrictedStageSections q q'
          simpa [Rqq, σqR, σqRid, κR, ℋ] using
            (pullback_comp_limit_unit_restriction_eq
              (F := F) (h := b ≫ g) (𝒢 := 𝒢)
              (W := Rqq) (V := q.1.2.2.1.toOpens)
              (σ := q.1.2.2.2) (τ := σqR)
              (hWV := show Rqq ≤ (Opens.map (F.map (b ≫ g))).obj q.1.2.2.1.toOpens from
                by
                  intro x hx
                  exact hWkVi q hx.1)
              (hτ := hτLeft))
        have hRightCollapsed :
            κR (pullbackSectionsToLimitMap F ℋ Rqq (Over.mk (𝟙 k)) σq'Rid) =
              cast eR
                (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
                    (homOfLE (le_trans hR₂ (hWkV q'))).op
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                        (limit.π F i)).unit.app 𝒢).1.app
                          (op q'.1.2.2.1.toOpens)) q'.1.2.2.2)) := by
          have hτRight :
              σq'R =
                ((((F.map (b ≫ g))⁻¹).obj 𝒢).presheaf).map
                  (homOfLE
                    (show Rqq ≤ (Opens.map (F.map (b ≫ g))).obj q'.1.2.2.1.toOpens from
                      by
                        intro x hx
                        exact hWkVi q' hx.2)).op
                  ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                      (F.map (b ≫ g))).unit.app 𝒢).1.app
                        (op q'.1.2.2.1.toOpens)) q'.1.2.2.2) := by
            simpa [Rqq, σq'R] using
              (restricted_stage_section_eq_two_step_restriction_right_fixed_owner
                (F := F) (h := b ≫ g) (𝒢 := 𝒢)
                (W₁ := Wk q) (W₂ := Wk q')
                (V := q'.1.2.2.1.toOpens)
                (σ := q'.1.2.2.2) (τ := τk q')
                (hW₂V := hWkVi q') (hτ := hτk q'))
          simpa [Rqq, σq'R, σq'Rid, κR, ℋ] using
            (pullback_comp_limit_unit_restriction_eq
              (F := F) (h := b ≫ g) (𝒢 := 𝒢)
              (W := Rqq) (V := q'.1.2.2.1.toOpens)
              (σ := q'.1.2.2.2) (τ := σq'R)
              (hWV := show Rqq ≤ (Opens.map (F.map (b ≫ g))).obj q'.1.2.2.1.toOpens from
                by
                  intro x hx
                  exact hWkVi q' hx.2)
              (hτ := hτRight))
        have hCastEq :
            cast eR
                (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
                    (homOfLE (le_trans hR₁ (hWkV q))).op
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                        (limit.π F i)).unit.app 𝒢).1.app
                          (op q.1.2.2.1.toOpens)) q.1.2.2.2)) =
              cast eR
                (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map
                    (homOfLE (le_trans hR₂ (hWkV q'))).op
                    ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                        (limit.π F i)).unit.app 𝒢).1.app
                          (op q'.1.2.2.1.toOpens)) q'.1.2.2.2)) := by
          exact congrArg (cast eR) hEqOverlap
        exact hLeftCollapsed.trans (hCastEq.trans hRightCollapsed.symm)
      exact
        (pullbackComp_hom_app_injective
          (f := limit.π F k) (g := F.map (b ≫ g)) (𝒢 := 𝒢)
          ((Opens.map (limit.π F k)).obj Rqq))
          hCollapsedEq
    obtain ⟨B, φ, hφ⟩ :=
      common_refinement_of_equal_limit_pullback_sections
        (F := F) hF ℋ Rqq (by simpa [Rqq] using (Wk q ⊓ Wk q').isCompact) (Over.mk (𝟙 k))
        σqRid σq'Rid hLimitEq
    refine ⟨B, φ, ?_⟩
    dsimp [Rqq, σqR, σq'R, σqRid, σq'Rid]
    exact hφ
  choose Bqq φqq hOverlapRefined using hOverlapRefined
  let lqq : {q // q ∈ t} → {q // q ∈ t} → I := fun q q' ↦ (Bqq q q').left
  let cqq : ∀ q q' : {q // q ∈ t}, lqq q q' ⟶ k := fun q q' ↦ (φqq q q').left
  obtain ⟨l, c, hc⟩ :=
    common_refinement_of_pairwise_arrows_to (I := I) (k := k) lqq cqq
  let uNested :
      ∀ q : {q // q ∈ t},
        ((((F.map c)⁻¹).obj ℋ).presheaf).obj
          (op ((stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens)) :=
    fun q ↦
      overPullbackSectionsMap F ℋ (Wk q).toOpens
        (A := Over.mk c) (B := Over.mk (𝟙 k))
        (Over.homMk c (by simp)) (σidW q)
  have hNestedOverlap :
      ∀ q q' : {q // q ∈ t},
        ((((F.map c)⁻¹).obj ℋ).presheaf).map
            (homOfLE
              (show
                (stage_pullback_compact_open (F := F) hF c (Wk q ⊓ Wk q')).toOpens ≤
                  (stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens from
                by
                  intro x hx
                  simpa [stage_pullback_compact_open] using hx.1)).op
            (uNested q) =
          ((((F.map c)⁻¹).obj ℋ).presheaf).map
            (homOfLE
              (show
                (stage_pullback_compact_open (F := F) hF c (Wk q ⊓ Wk q')).toOpens ≤
                  (stage_pullback_compact_open (F := F) hF c (Wk q')).toOpens from
                by
                  intro x hx
                  simpa [stage_pullback_compact_open] using hx.2)).op
            (uNested q') := by
    intro q q'
    let Rqq : Opens (F.obj k) := (Wk q ⊓ Wk q').toOpens
    let σqR : ℋ.1.obj (op Rqq) :=
      ℋ.1.map
        (homOfLE
          (show (Wk q ⊓ Wk q').toOpens ≤ (Wk q).toOpens from inf_le_left)).op
        (τk q)
    let σq'R : ℋ.1.obj (op Rqq) :=
      ℋ.1.map
        (homOfLE
          (show (Wk q ⊓ Wk q').toOpens ≤ (Wk q').toOpens from inf_le_right)).op
        (τk q')
    let σqRid :
        ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj Rqq)) := by
            simpa [σqR] using
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
                  (eqToIso rfl)).inv.app ℋ).1.app (op Rqq) σqR)
    let σq'Rid :
        ((((F.map (𝟙 k))⁻¹).obj ℋ).presheaf).obj
          (op ((Opens.map (F.map (𝟙 k))).obj Rqq)) := by
            simpa [σq'R] using
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (𝟙 (F.obj k))).leftAdjointIdIso
                  (eqToIso rfl)).inv.app ℋ).1.app (op Rqq) σq'R)
    rcases hc q q' with ⟨d, hd⟩
    have hdb : d ≫ (Bqq q q').hom = c := by
      have hw : (Bqq q q').hom = cqq q q' := by
        simpa [cqq] using (Over.w (φqq q q')).symm
      simpa [hw] using hd
    let φd : Over.mk c ⟶ Bqq q q' := Over.homMk d hdb
    have hDomRaw :
        overPullbackSectionsMap F ℋ Rqq (φd ≫ φqq q q') σqRid =
          overPullbackSectionsMap F ℋ Rqq (φd ≫ φqq q q') σq'Rid := by
      exact
        equal_overPullbackSectionsMap_of_dominated_refinement
          (F := F) (𝒢 := ℋ) (U := Rqq)
          (A := Over.mk c) (B := Bqq q q') (C := Over.mk (𝟙 k))
          (φ := φd) (ψ := φqq q q')
          (s := σqRid) (t := σq'Rid)
          (hEq := hOverlapRefined q q')
    have hMor : φd ≫ φqq q q' = Over.homMk c (by simp) := by
      ext
      simpa [cqq, lqq] using hd
    have hDom :
        overPullbackSectionsMap F ℋ Rqq
            (A := Over.mk c) (B := Over.mk (𝟙 k))
            (Over.homMk c (by simp)) σqRid =
          overPullbackSectionsMap F ℋ Rqq
            (A := Over.mk c) (B := Over.mk (𝟙 k))
            (Over.homMk c (by simp)) σq'Rid := by
      exact hMor ▸ hDomRaw
    have hLeftNested :
        ((((F.map c)⁻¹).obj ℋ).presheaf).map
            (homOfLE
              (show
                (stage_pullback_compact_open (F := F) hF c (Wk q ⊓ Wk q')).toOpens ≤
                  (stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens from
                stage_pullback_compact_open_inf_le_left (F := F) hF c (Wk q) (Wk q'))).op
            (uNested q) =
          overPullbackSectionsMap F ℋ Rqq
            (A := Over.mk c) (B := Over.mk (𝟙 k))
            (Over.homMk c (by simp)) σqRid := by
      simpa [uNested, σidW, Rqq, σqR, σqRid] using
        (overPullbackSectionsMap_identity_over_stage_restrict_eq_inf
          (F := F) (c := c) (hF := hF) (ℋ := ℋ)
          (W₁ := Wk q) (W₂ := Wk q') (σ := τk q))
    have hRightNested :
        overPullbackSectionsMap F ℋ Rqq
            (A := Over.mk c) (B := Over.mk (𝟙 k))
            (Over.homMk c (by simp)) σq'Rid =
          ((((F.map c)⁻¹).obj ℋ).presheaf).map
            (homOfLE
              (show
                (stage_pullback_compact_open (F := F) hF c (Wk q ⊓ Wk q')).toOpens ≤
                (stage_pullback_compact_open (F := F) hF c (Wk q')).toOpens from
              by
                intro x hx
                simpa [stage_pullback_compact_open] using hx.2)).op
            (uNested q') := by
      -- The dedicated owner-transport lemma packages the swapped right-branch normalization in
      -- the fixed overlap order needed by `hNestedOverlap`.
      simpa [uNested, σidW, Rqq] using
        (overPullbackSectionsMap_overlap_owner_transport
          (F := F) (c := c) (hF := hF) (ℋ := ℋ)
          (W₁ := Wk q) (W₂ := Wk q') (σ := τk q'))
    -- Rewrite the domination equality back into the explicit overlap restrictions of `uNested`.
    exact hLeftNested.trans (hDom.trans hRightNested)
  have hCompatNested :
      TopCat.Presheaf.IsCompatible
        ((((F.map c)⁻¹).obj ℋ).presheaf)
        (fun q : {q // q ∈ t} ↦
          (stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens)
        uNested := by
    -- The pairwise overlap equalities are now synchronized to one common stage over `k`.
    exact
      isCompatible_of_pairwise_overlap_eq
        (F := F) hF c ℋ Wk uNested hNestedOverlap
  let uSectionsRaw :
      ∀ q : {q // q ∈ t},
        (((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map (b ≫ g))).obj 𝒢).presheaf).obj
          (op ((stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens)) :=
    fun q ↦
      ((((TopCat.Sheaf.pullbackComp (A := Type u) (F.map c) (F.map (b ≫ g))).hom.app
          𝒢).1.app (op ((stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens))))
        (uNested q)
  let uSections :
      ∀ q : {q // q ∈ t},
        ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).obj
          (op ((stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens)) :=
    fun q ↦ by
      exact cast (by simp [Functor.map_comp])
        (uSectionsRaw q)
  have hCompat :
      TopCat.Presheaf.IsCompatible
        ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf)
        (fun q : {q // q ∈ t} ↦
          (stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens)
        uSections := by
    intro q q'
    let Oq : Opens (F.obj l) := (stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens
    let Oq' : Opens (F.obj l) := (stage_pullback_compact_open (F := F) hF c (Wk q')).toOpens
    have hcomp : F.map c ≫ F.map (b ≫ g) = F.map (c ≫ b ≫ g) := by
      simp [Functor.map_comp]
    have hOverlapCast :
        (((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map (b ≫ g))).obj 𝒢).presheaf).obj
            (op (Oq ⊓ Oq')) =
          ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).obj (op (Oq ⊓ Oq')) := by
      simp [Oq, Oq']
    have hLeftCast :
        ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).map (Oq.infLELeft Oq').op
            (uSections q) =
          cast hOverlapCast
            ((((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map (b ≫ g))).obj 𝒢).presheaf).map
              (Oq.infLELeft Oq').op
              (uSectionsRaw q)) := by
      -- Restriction commutes with the reassociation cast on the left overlap map.
      simpa [uSections, uSectionsRaw, Oq, Oq', hcomp] using
        (pullback_section_restriction_cast_eq_of_hom_eq
          (hfg := hcomp) (𝒢 := 𝒢) (i := Oq.infLELeft Oq') (σ := uSectionsRaw q))
    have hRightCast :
        ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).map (Oq.infLERight Oq').op
            (uSections q') =
          cast hOverlapCast
            ((((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map (b ≫ g))).obj 𝒢).presheaf).map
              (Oq.infLERight Oq').op
              (uSectionsRaw q')) := by
      -- The same cast-transport identity handles the right overlap map.
      simpa [uSections, uSectionsRaw, Oq, Oq', hcomp] using
        (pullback_section_restriction_cast_eq_of_hom_eq
          (hfg := hcomp) (𝒢 := 𝒢) (i := Oq.infLERight Oq') (σ := uSectionsRaw q'))
    -- After transporting both restriction terms across the same overlap cast, the remaining
    -- equality is exactly the raw compatibility already proved for `uSectionsRaw`.
    calc
      ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).map (Oq.infLELeft Oq').op
          (uSections q) =
        cast hOverlapCast
          ((((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map (b ≫ g))).obj 𝒢).presheaf).map
            (Oq.infLELeft Oq').op
            (uSectionsRaw q)) := hLeftCast
      _ =
        cast hOverlapCast
          ((((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map (b ≫ g))).obj 𝒢).presheaf).map
            (Oq.infLERight Oq').op
            (uSectionsRaw q')) := by
              exact congrArg (cast hOverlapCast) <|
                pullbackComp_hom_preserves_overlap_eq_raw
                  (F := F) (hF := hF) (c := c) (h := b ≫ g) (𝒢 := 𝒢)
                  (W := Wk) (u := uNested) (hCompat := hCompatNested) q q'
      _ =
        ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).map (Oq.infLERight Oq').op
          (uSections q') := hRightCast.symm
  obtain ⟨gl, hgl⟩ := hExistsCommonStageGluing c uSections hCompat
  have hglUType :
      (stage_pullback_compact_open (F := F) hF (c ≫ b ≫ g) Ui).toOpens =
        (Opens.map (F.map (c ≫ b ≫ g))).obj U := by
    ext x
    simpa [stage_pullback_compact_open, hUi, Functor.map_comp, Category.assoc]
  let glU :
      ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).obj
        (op ((Opens.map (F.map (c ≫ b ≫ g))).obj U)) :=
    cast (by rw [← hglUType]) gl
  have hglue_image :
    pullbackSectionsToLimitMap F 𝒢 U (Over.mk (c ≫ b ≫ g)) glU = s := by
    -- Compare the two limit sections stalkwise, choosing one refined cover piece through each
    -- point of `p_i⁻¹(U)` and normalizing both germs to the same direct `p_i`-pullback-unit germ.
    apply TopCat.Presheaf.section_ext (((limit.π F i)⁻¹).obj 𝒢) ((Opens.map (limit.π F i)).obj U)
    intro x hx
    have hxUi : x ∈ (Opens.map (limit.π F i)).obj Ui.toOpens := by
      simpa [hUi] using hx
    obtain ⟨q, hxq⟩ :=
      exists_refined_cover_piece_through_limit_point
        (F := F) hF (g := g) (b := b) (c := c) (Ui := Ui)
        (Wk := Wk) (hWkCover := hWkCover) hxUi
    have hRight :
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
            ((Opens.map (limit.π F i)).obj U) x hx s =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
            ((Opens.map (limit.π F i)).obj q.1.2.2.1.toOpens) x
            ((hWkV q) <|
              (limit_projection_preimage_le_of_stage_le (F := F) (h := c)
                (W := (stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens)
                (V := (Wk q).toOpens)
                (by
                  intro y hy
                  simpa [stage_pullback_compact_open] using hy)) hxq)
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (limit.π F i)).unit.app 𝒢).1.app
                  (op q.1.2.2.1.toOpens)) q.1.2.2.2) :=
      limit_section_germ_eq_stage_unit_on_refined_piece
        (F := F) (hF := hF) (c := c) (𝒢 := 𝒢)
        (U := U) (V := q.1.2.2.1.toOpens) (s := s)
        (Wk := Wk q) (hWkU := hWkU q) (hWkV := hWkV q)
        (σ := q.1.2.2.2) (hEq := hEqk q) (x := x) hxq
    have hLeft :
        ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
            ((Opens.map (limit.π F i)).obj U) x hx
            (pullbackSectionsToLimitMap F 𝒢 U (Over.mk (c ≫ b ≫ g)) glU) =
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
            ((Opens.map (limit.π F i)).obj q.1.2.2.1.toOpens) x
            ((hWkV q) <|
              (limit_projection_preimage_le_of_stage_le (F := F) (h := c)
                (W := (stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens)
                (V := (Wk q).toOpens)
                (by
                  intro y hy
                  simpa [stage_pullback_compact_open] using hy)) hxq)
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (limit.π F i)).unit.app 𝒢).1.app
                  (op q.1.2.2.1.toOpens)) q.1.2.2.2) := by
      let Oq : Opens (F.obj l) :=
        (stage_pullback_compact_open (F := F) hF c (Wk q)).toOpens
      let Pq : Opens ↥(limit F) :=
        projection_preimage_open (F := F)
          ⟨l, stage_pullback_compact_open (F := F) hF c (Wk q)⟩
      have hPqk :
          Pq ≤ projection_preimage_open (F := F) ⟨k, Wk q⟩ :=
        limit_projection_preimage_le_of_stage_le
          (F := F) (h := c) (W := Oq) (V := (Wk q).toOpens)
          (by
            intro y hy
            simpa [Oq, stage_pullback_compact_open] using hy)
      have hPqU :
          Pq ≤ (Opens.map (limit.π F i)).obj U :=
        le_trans hPqk (hWkU q)
      have hPqV :
          Pq ≤ (Opens.map (limit.π F i)).obj q.1.2.2.1.toOpens :=
        le_trans hPqk (hWkV q)
      have hWkUi :
          (Wk q).toOpens ≤ (Opens.map (F.map (b ≫ g))).obj Ui.toOpens := by
        intro y hy
        have hyUnion :
            y ∈ ⋃ q' : {q // q ∈ t}, ((Wk q' : CompactOpens (F.obj k)) : Set (F.obj k)) :=
          Set.mem_iUnion.2 ⟨q, by simpa using hy⟩
        have hyStage :
            y ∈ ((stage_pullback_compact_open (F := F) hF (b ≫ g) Ui :
              CompactOpens (F.obj k)) : Set (F.obj k)) := by
          rw [hWkCover]
          exact hyUnion
        simpa [stage_pullback_compact_open] using hyStage
      have hOqU :
          Oq ≤ (Opens.map (F.map (c ≫ b ≫ g))).obj U := by
        simpa [Oq, hUi, Functor.map_comp, Category.assoc] using
          (refined_stage_pullback_piece_le_stage_pullback
            (F := F) hF (h := b ≫ g) (c := c) (W := Wk q)
            (V := Ui.toOpens) hWkUi)
      have hOqV :
          Oq ≤ (Opens.map (F.map (c ≫ b ≫ g))).obj q.1.2.2.1.toOpens := by
        simpa [Oq, Functor.map_comp, Category.assoc] using
          (refined_stage_pullback_piece_le_stage_pullback
            (F := F) hF (h := b ≫ g) (c := c) (W := Wk q)
            (V := q.1.2.2.1.toOpens) (hWkVi q))
      obtain ⟨iUVq, hglq⟩ := hgl q
      have hglUq :
          ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).map
              (homOfLE hOqU).op glU =
            uSections q := by
        -- The glued common-stage section restricts to the chosen local branch on the refined piece.
        -- After rewriting `U` as `Ui.toOpens`, the codomain of `glU` is definitionally the stage
        -- pullback open used by the gluing witness `hglq`, so only proof-irrelevant inclusion data
        -- remains.
        subst U
        dsimp [glU]
        simpa [stage_pullback_compact_open, Functor.map_comp, Category.assoc] using hglq
      have huNestedq :
          uNested q =
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map c)).unit.app
                ℋ).1.app (op (Wk q).toOpens)) (τk q)) := by
        -- The identity-over-stage refinement of `τk q` is just the ordinary pullback unit along
        -- `F.map c`.
        simpa [uNested, σidW, ℋ] using
          (overPullbackSectionsMap_identity_over_stage_eq_pullback_unit
            (F := F) (c := c) (ℋ := ℋ) (U0 := (Wk q).toOpens) (σ := τk q))
      have huSectionsRawq :
          uSectionsRaw q =
            ((((TopCat.Sheaf.pullback (Type u) (F.map c ≫ F.map (b ≫ g))).obj 𝒢).presheaf).map
                (homOfLE (by
                  simpa [Oq] using hOqV)).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                    (F.map c ≫ F.map (b ≫ g))).unit.app 𝒢).1.app
                      (op q.1.2.2.1.toOpens)) q.1.2.2.2)) := by
        -- Normalize the chosen local branch to the direct pullback-unit section on the refined
        -- piece before comparing its image in the limit.
        -- Rewrite `uNested q` as the ordinary pullback unit along `F.map c`, then collapse the
        -- nested pullback branch with the dedicated `pullbackComp` restriction lemma.
        dsimp [uSectionsRaw]
        rw [huNestedq]
        simpa [Oq, Functor.map_comp, Category.assoc] using
          (pullbackComp_hom_unit_restriction_eq
            (f := F.map c) (g := F.map (b ≫ g)) (𝒢 := 𝒢)
            (W := (Wk q).toOpens) (V := q.1.2.2.1.toOpens)
            (σ := q.1.2.2.2) (τ := τk q)
            (hWV := hWkVi q) (hτ := hτk q))
      have huSectionsq :
          uSections q =
            ((((F.map (c ≫ b ≫ g))⁻¹).obj 𝒢).presheaf).map
                (homOfLE hOqV).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                    (F.map (c ≫ b ≫ g))).unit.app 𝒢).1.app
                      (op q.1.2.2.1.toOpens)) q.1.2.2.2) := by
        -- Collapse the reassociation cast in `uSections` to the direct composite pullback.
        -- The outer cast in `uSections` is exactly the reassociation cast from
        -- `F.map c ≫ F.map (b ≫ g)` to `F.map (c ≫ b ≫ g)`.
        have hcomp : F.map c ≫ F.map (b ≫ g) = F.map (c ≫ b ≫ g) := by
          simp [Functor.map_comp]
        dsimp [uSections]
        rw [huSectionsRawq]
        exact
          (pullback_unit_restriction_eq_of_hom_eq
            (hfg := hcomp) (𝒢 := 𝒢)
            (R := Oq) (V := q.1.2.2.1.toOpens)
            (σ := q.1.2.2.2)
            (hRV := by simpa [Oq] using hOqV)).symm
      have hPqEq :
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hPqU).op
              (pullbackSectionsToLimitMap F 𝒢 U (Over.mk (c ≫ b ≫ g)) glU) =
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hPqV).op
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                  (limit.π F i)).unit.app 𝒢).1.app
                    (op q.1.2.2.1.toOpens)) q.1.2.2.2) := by
        -- Rewrite the global glued image on `Pq` to the localized branch on `Oq`, then collapse
        -- that branch to the direct `p_i`-pullback-unit section using the already-normalized
        -- source-side equality `hglUq.trans huSectionsq`.
        simpa [Pq, Oq, projection_preimage_open, projection_preimage_basis] using
          (glued_limit_image_restrict_eq_stage_unit_on_source_open
            (F := F) (h := c ≫ b ≫ g) (𝒢 := 𝒢)
            (U := U) (V := q.1.2.2.1.toOpens) (O := Oq)
            (glU := glU) (σ := q.1.2.2.2)
            (hOU := hOqU) (hOV := hOqV)
            (hτ := hglUq.trans huSectionsq))
      have hLocal :
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ Pq x hxq
              (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hPqU).op
                (pullbackSectionsToLimitMap F 𝒢 U (Over.mk (c ≫ b ≫ g)) glU)) =
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ Pq x hxq
              (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hPqV).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                    (limit.π F i)).unit.app 𝒢).1.app
                      (op q.1.2.2.1.toOpens)) q.1.2.2.2)) := by
        exact
          congrArg
            (((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ Pq x hxq)
            hPqEq
      have hLeftRes :
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ Pq x hxq
              (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hPqU).op
                (pullbackSectionsToLimitMap F 𝒢 U (Over.mk (c ≫ b ≫ g)) glU)) =
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
              ((Opens.map (limit.π F i)).obj U) x (hPqU hxq)
              (pullbackSectionsToLimitMap F 𝒢 U (Over.mk (c ≫ b ≫ g)) glU) := by
        -- Restricting the glued image to the refined piece does not change its germ there.
        simpa using
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ_res_apply
            (homOfLE hPqU) x hxq
            (pullbackSectionsToLimitMap F 𝒢 U (Over.mk (c ≫ b ≫ g)) glU)
      have hRightRes :
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ Pq x hxq
              (((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hPqV).op
                ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                    (limit.π F i)).unit.app 𝒢).1.app
                      (op q.1.2.2.1.toOpens)) q.1.2.2.2)) =
            ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ
              ((Opens.map (limit.π F i)).obj q.1.2.2.1.toOpens) x (hPqV hxq)
              ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                  (limit.π F i)).unit.app 𝒢).1.app
                    (op q.1.2.2.1.toOpens)) q.1.2.2.2) := by
        -- The same restriction-to-germ identity applies to the direct stage-unit section.
        simpa using
          ((((limit.π F i)⁻¹).obj 𝒢).presheaf).germ_res_apply
            (homOfLE hPqV) x hxq
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
                (limit.π F i)).unit.app 𝒢).1.app
                  (op q.1.2.2.1.toOpens)) q.1.2.2.2)
      exact hLeftRes.symm.trans (hLocal.trans hRightRes)
    exact hLeft.trans hRight.symm
  refine ⟨(colimit.ι (limitPullbackSectionsDiagram F i 𝒢 U) (op (Over.mk (c ≫ b ≫ g)))) glU, ?_⟩
  simpa [limitPullbackSectionsColimitMap, limitPullbackSectionsCocone] using hglue_image

/-- Helper for Lemma 6.29.3: the remaining source-faithful surjectivity argument consists of the
finite compact-open local presentation, descent to one common stage, descent of the finite cover to
an actual stage cover, and then one last overlap-refinement-and-gluing step. This theorem packages
all already-verified setup before the final gluing blocker. -/
private theorem limitPullbackSectionsColimitMap_surjective
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : I) (𝒢 : (F.obj i).Sheaf (Type u))
    (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) :
    Function.Surjective (limitPullbackSectionsColimitMap F i 𝒢 U) := by
  intro s
  obtain ⟨t, htCover, htLocal⟩ :=
    pullback_section_has_finite_projection_preimage_local_presentation
      (F := F) hF 𝒢 U hU s
  have hDescendedLocal :
      ∀ q ∈ t, DescendedLocalSectionData (F := F) hF 𝒢 U s q := by
    intro q hq
    rcases htLocal q hq with ⟨hWU, hWV, hEq⟩
    exact
      local_stage_section_datum_descends_to_base_stage
        (F := F) hF 𝒢 U s q hWU hWV hEq
  have hCommonStage :
      ∃ (j : I) (g : j ⟶ i),
        ∀ q ∈ t, CommonStageDescendedLocalSectionData (F := F) hF 𝒢 U s q j g := by
    -- Move the finitely many descended stage arrows to one common stage over `i` before tackling
    -- the actual same-stage cover refinement and gluing step.
    exact
      descended_local_sections_admit_common_stage
        (F := F) hF 𝒢 U s t hDescendedLocal
  have hSameStage :
      ∃ (j : I) (g : j ⟶ i),
        ∀ q ∈ t,
          ∃ Wj : CompactOpens (F.obj j),
            projection_preimage_open (F := F) ⟨j, Wj⟩ =
              projection_preimage_open (F := F) ⟨q.1, q.2.1⟩ ∧
            ∃ hWjU : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
                (Opens.map (limit.π F i)).obj U,
              ∃ hWjV : projection_preimage_open (F := F) ⟨j, Wj⟩ ≤
                  (Opens.map (limit.π F i)).obj q.2.2.1.toOpens,
                ∃ hWjVi : Wj.toOpens ≤ (Opens.map (F.map g)).obj q.2.2.1.toOpens,
                  ∃ τj : ((((F.map g)⁻¹).obj 𝒢).presheaf).obj (op Wj.toOpens),
                    τj =
                      ((((F.map g)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjVi).op
                        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (F.map g)).unit.app
                            𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) ∧
                    ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjU).op s =
                      ((((limit.π F i)⁻¹).obj 𝒢).presheaf).map (homOfLE hWjV).op
                        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (limit.π F i)).unit.app
                            𝒢).1.app (op q.2.2.1.toOpens)) q.2.2.2) := by
    rcases hCommonStage with ⟨j, g, hg⟩
    refine ⟨j, g, ?_⟩
    intro q hq
    -- Materialize the common-stage witness as an honest compact open and section on `X_j`.
    exact
      common_stage_descended_section_transport
        (F := F) hF 𝒢 U s q (hg q hq)
  let Ui : CompactOpens (F.obj i) := ⟨⟨U, hU⟩, U.isOpen⟩
  rcases hSameStage with ⟨j, g, hg⟩
  have hSameStageOn :
      ∀ q : {q // q ∈ t},
        ∃ Wj : CompactOpens (F.obj j),
          CommonStageLocalSectionOn (F := F) 𝒢 U s q.1 (g := g) Wj := by
    intro q
    simpa [CommonStageLocalSectionOn] using hg q.1 q.2
  choose W hW using hSameStageOn
  have hWBasic :
      ∀ q : {q // q ∈ t},
        projection_preimage_open (F := F) ⟨j, W q⟩ =
            projection_preimage_open (F := F) ⟨q.1.1, q.1.2.1⟩ ∧
          projection_preimage_open (F := F) ⟨j, W q⟩ ≤
            (Opens.map (limit.π F i)).obj Ui.toOpens := by
    intro q
    rcases hW q with ⟨hEqWj, hWjU, hWjV, hWjVi, τj, hτj, hEq⟩
    exact ⟨hEqWj, hWjU⟩
  rcases
      common_stage_transport_family_refines_to_stage_cover
        (F := F) hF 𝒢 Ui t htCover (j := j) (g := g) W hWBasic with
    ⟨hStageCover, k, b, hbCover⟩
  -- The geometric descent is complete. The last remaining work is to normalize the local sections
  -- on the stage-`k` cover, refine finitely many overlap equalities to one stage, and glue there.
  exact
    same_stage_descended_sections_glue_after_common_refinement
      (F := F) hF 𝒢 U hU s t Ui rfl W hW hStageCover b hbCover

-- Proof sketch: keep the proved injective half and the local presheaf-representative interface,
-- use the newly rebuilt compactness owner for `p_i⁻¹(U)`, and then finish by the source-faithful
-- finite compact-open descent/gluing argument.
private theorem limitPullbackSectionsColimitMap_isIso_viaSiteComparison
    [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a)) (i : I)
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) :
    IsIso (limitPullbackSectionsColimitMap F i 𝒢 U) := by
  -- Route correction: abandon the stalled Chapter 7 owner route and return to the source-faithful
  -- finite descent/gluing proof. This file already proves injectivity and local stage
  -- representatives on the limit, and the compactness input for `p_i⁻¹(U)` is now rebuilt
  -- locally. The remaining gap is to package a finite compact-open local presentation of the
  -- section, descend that finite family to one stage via `5.24.6`, and glue after one common
  -- refinement.
  rw [CategoryTheory.isIso_iff_bijective]
  exact ⟨limitPullbackSectionsColimitMap_injective (F := F) hF i 𝒢 U hU,
    limitPullbackSectionsColimitMap_surjective (F := F) hF i 𝒢 U hU⟩

-- Proof sketch: once the Chapter 5 import collision is repaired, finish the existing injective
-- proof by the Stacks surjectivity argument: finite local representatives on `p_i⁻¹(U)`, descent
-- to one stage, one common refinement for pairwise compatibility, and sheaf gluing.
/-- Lemma 6.29.3: for a cofiltered diagram of spectral spaces with spectral transition maps, the
canonical comparison map from the colimit of the stagewise pullback sections
`f_a⁻¹ 𝒢 (f_a⁻¹(U))` to the pullback sections `p_i⁻¹ 𝒢 (p_i⁻¹(U))` on the limit space is an
isomorphism for every quasi-compact open `U ⊆ X_i`. -/
theorem limitPullbackSectionsColimitMap_isIso [IsCofiltered I] [∀ i : I, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a)) (i : I)
    (𝒢 : (F.obj i).Sheaf (Type u)) (U : Opens (F.obj i)) (hU : IsCompact (U : Set (F.obj i))) :
    IsIso (limitPullbackSectionsColimitMap F i 𝒢 U) :=
  limitPullbackSectionsColimitMap_isIso_viaSiteComparison F hF i 𝒢 U hU

end
