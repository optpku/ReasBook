module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Spectral.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import stacks_project.Chap05.Lemma_5_14_2
import stacks_project.Chap05.Lemma_5_23_2
import stacks_project.Chap05.Lemma_5_23_3
import stacks_project.Chap05.Lemma_5_24_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits

section

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v w}} [∀ j : J, SpectralSpace (F.obj j)]

/- Domain-style sampling for Lemma 5.24.6:
- primary domain: cofiltered inverse limits of spectral spaces, with descent of quasi-compact
  opens and eventual stagewise inclusion;
- inspected owner-level declarations:
  `open_eq_preimage_of_isLimit_of_isConstructible`,
  `constructible_eq_preimage_of_isLimit`,
  `limit_projection_preimage_subset_iff_exists_stage_preimage_subset`,
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- best owner abstraction first: the spectral/constructible descent owner for part `(1)` is
  `open_eq_preimage_of_isLimit_of_isConstructible`, whose output already lives in
  `CompactOpens`; `limit_projection_preimage_subset_iff_exists_stage_preimage_subset` is the
  chapter-level owner for eventual stagewise inclusion in part `(2)`;
- primitive data: the cofiltered spectral diagram and the limit-side or stagewise `CompactOpens`;
- derived API: part `(1)` as the chosen-limit specialization of open constructible descent, then
  the common-refinement inclusion criterion and the finite union/intersection descent statements.

Source/core/bridge triage:
- `source-facing`: the numbered Lemma 5.24.6 statements about quasi-compact opens on the chosen
  inverse limit and their eventual stagewise behavior;
- `core/canonical`: `Topology.IsConstructible` together with `CompactOpens` and the chapter 5.24
  cofiltered-limit descent owners;
- `bridge/view`: part `(1)` is the chosen-limit specialization of
  `open_eq_preimage_of_isLimit_of_isConstructible`, turning a limit-side `CompactOpens` object into
  its stagewise `CompactOpens` ancestor.

The finite-family parts are stated over an arbitrary `Fintype` rather than `Fin n`: the source
mathematics uses only finiteness, so the `Fin n` encoding would be presentation-level bookkeeping
rather than primitive data.
-/

-- Proof sketch: first descend the limit-side compact open to a single stage open via
-- `compact_open_eq_preimage_of_isLimit`, then refine that stage open by compact-open basis pieces
-- and use compactness of the limit-side subset to keep only finitely many of them.
/-- Lemma 5.24.6 (1): every quasi-compact open subset of the inverse limit of a cofiltered diagram
of spectral spaces with spectral transition maps is the pullback of a quasi-compact open subset
from some stage. -/
theorem compact_open_eq_preimage_of_limit
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (W : CompactOpens ↥(limit F)) :
    ∃ (i : J) (Wi : CompactOpens (F.obj i)),
      (W : Set ↥(limit F)) = (limit.π F i) ⁻¹' (Wi : Set (F.obj i)) := by
  let _ := hF
  let C : Cone F := limit.cone F
  have hC : IsLimit C := by
    simpa [C] using limit.isLimit F
  obtain ⟨i, U, hU⟩ := compact_open_eq_preimage_of_isLimit (F := F) (C := C) hC (by
    simpa [C] using W)
  have hU' : (W : Set ↥(limit F)) = (limit.π F i) ⁻¹' (U : Set (F.obj i)) := by
    simpa [C] using hU
  let S : Set (Set (F.obj i)) := {s | IsOpen s ∧ IsCompact s ∧ s ⊆ (U : Set (F.obj i))}
  have hU_eq : (U : Set (F.obj i)) = ⋃₀ S := by
    simpa [S, and_left_comm, and_assoc] using
      (PrespectralSpace.isTopologicalBasis (X := F.obj i)).open_eq_sUnion' U.isOpen
  let V : {s : Set (F.obj i) // s ∈ S} → CompactOpens (F.obj i) :=
    fun s ↦ ⟨⟨s.1, s.2.2.1⟩, s.2.1⟩
  have hOpen : ∀ s : {s : Set (F.obj i) // s ∈ S},
      IsOpen ((limit.π F i) ⁻¹' (V s : Set (F.obj i))) := by
    intro s
    exact (V s).isOpen.preimage (limit.π F i).hom.continuous
  have hCover : (W : Set ↥(limit F)) ⊆ ⋃ s : {s : Set (F.obj i) // s ∈ S},
      (limit.π F i) ⁻¹' (V s : Set (F.obj i)) := by
    intro x hx
    rw [hU'] at hx
    change (limit.π F i) x ∈ (U : Set (F.obj i)) at hx
    rw [hU_eq] at hx
    rcases mem_sUnion.1 hx with ⟨s, hsS, hsx⟩
    exact mem_iUnion.2 ⟨⟨s, hsS⟩, hsx⟩
  obtain ⟨t, ht⟩ := W.isCompact.elim_finite_subcover
    (fun s : {s : Set (F.obj i) // s ∈ S} ↦ (limit.π F i) ⁻¹' (V s : Set (F.obj i))) hOpen hCover
  let Wi : CompactOpens (F.obj i) := t.sup V
  refine ⟨i, Wi, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ⋃ s ∈ t, (limit.π F i) ⁻¹' (V s : Set (F.obj i)) := by
      have htx := ht hx
      rw [Set.mem_iUnion] at htx
      rcases htx with ⟨s, htx⟩
      rw [Set.mem_iUnion] at htx
      rcases htx with ⟨hs, hsx⟩
      exact mem_iUnion.2 ⟨s, mem_iUnion.2 ⟨hs, hsx⟩⟩
    simpa [Wi, CompactOpens.coe_finsetSup] using hx'
  · intro hx
    have hx' : x ∈ ⋃ s ∈ t, (limit.π F i) ⁻¹' (V s : Set (F.obj i)) := by
      simpa [Wi, CompactOpens.coe_finsetSup] using hx
    rw [hU']
    rw [Set.mem_preimage]
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨s, hx'⟩
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨hs, hsx⟩
    exact s.2.2.2 hsx

/-- Helper for Lemma 5.24.6: pulling back along a limit projection can be rewritten through any
refining stage map. -/
private theorem limit_projection_preimage_eq_stage_preimage
    {J : Type v} [Category.{w} J] {F : J ⥤ TopCat.{max v w}}
    {i k : J} (a : k ⟶ i) (S : Set (F.obj i)) :
    (limit.π F i) ⁻¹' S = (limit.π F k) ⁻¹' ((F.map a) ⁻¹' S) := by
  -- The limit cone relation identifies the `i`-coordinate with the `k`-coordinate followed by `a`.
  ext x
  constructor
  · intro hx
    change F.map a ((limit.π F k) x) ∈ S
    have hπ : F.map a ((limit.π F k) x) = (limit.π F i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F a)) x
    simpa [hπ] using hx
  · intro hx
    change F.map a ((limit.π F k) x) ∈ S at hx
    have hπ : F.map a ((limit.π F k) x) = (limit.π F i) x := by
      exact DFunLike.congr_fun (congrArg ConcreteCategory.hom (limit.w F a)) x
    simpa [hπ] using hx

/-- Helper for Lemma 5.24.6: compact opens are constructibly closed on a spectral space. -/
private theorem compact_open_isClosed_constructibleTopology
    {X : Type*} [TopologicalSpace X] [SpectralSpace X] (U : CompactOpens X) :
    IsClosed[constructibleTopology X] (U : Set X) := by
  -- Compact opens are constructible, hence clopen for the constructible topology.
  exact (isClopen_constructibleTopology_of_isConstructible
    (U.isCompact.isConstructible U.isOpen)).1

/-- Helper for Lemma 5.24.6: compact opens are constructibly open on a spectral space. -/
private theorem compact_open_isOpen_constructibleTopology
    {X : Type*} [TopologicalSpace X] [SpectralSpace X] (U : CompactOpens X) :
    IsOpen[constructibleTopology X] (U : Set X) := by
  -- Compact opens are constructible, hence clopen for the constructible topology.
  exact (isClopen_constructibleTopology_of_isConstructible
    (U.isCompact.isConstructible U.isOpen)).2

/-- Helper for Lemma 5.24.6: inverse image commutes with the finite `CompactOpens` supremum
packaged by `Finset.univ.sup`. -/
private theorem preimage_finset_sup_eq_iUnion
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι] (f : X → Y) (V : ι → CompactOpens Y) :
    f ⁻¹' ((Finset.univ.sup V : CompactOpens Y) : Set Y) = ⋃ t, f ⁻¹' (V t : Set Y) := by
  classical
  -- Membership in the finite supremum is exactly membership in one of the finitely many opens.
  ext x
  simp [CompactOpens.coe_finsetSup]

/-- Helper for Lemma 5.24.6: inverse image commutes with the finite `CompactOpens` infimum
packaged by `Finset.univ.inf`. -/
private theorem preimage_finset_inf_eq_iInter
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SpectralSpace Y]
    {ι : Type*} [Fintype ι] (f : X → Y) (V : ι → CompactOpens Y) :
    f ⁻¹' ((Finset.univ.inf V : CompactOpens Y) : Set Y) = ⋂ t, f ⁻¹' (V t : Set Y) := by
  classical
  -- Unfold the finite infimum inductively and rewrite each step as an intersection preimage.
  have haux :
      ∀ s : Finset ι,
        f ⁻¹' ((s.inf V : CompactOpens Y) : Set Y) = ⋂ t ∈ s, f ⁻¹' (V t : Set Y) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        ext x
        simp
    | insert a s ha hs =>
        ext x
        simp [Finset.inf_insert, hs, CompactOpens.coe_inf]
  simpa using haux Finset.univ

-- Proof sketch: specialize
-- `limit_projection_preimage_subset_iff_exists_stage_preimage_subset` from Lemma `5.24.3` to the
-- constructibly closed set `Ui` and the constructibly open set `Uj`, then use cofilteredness to
-- compare the two stage indices on a common refinement.
/-- Lemma 5.24.6 (2): if the pullback of a quasi-compact open from one stage is contained in the
pullback of a quasi-compact open from another stage, then this inclusion already holds after
pullback to some common refinement stage. -/
theorem exists_common_refinement_of_preimage_subset
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : J} (Ui : CompactOpens (F.obj i)) (Uj : CompactOpens (F.obj j))
    (hsub : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) ⊆
      (limit.π F j) ⁻¹' (Uj : Set (F.obj j))) :
    ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) ⊆ (F.map b) ⁻¹' (Uj : Set (F.obj j)) := by
  have hF' : ∀ ⦃j k : J⦄ (a : j ⟶ k), IsSpectralMap (F.map a) := fun {_ _} a ↦ hF a
  obtain ⟨k₀, a₀, b₀, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  let Ei : Set (F.obj k₀) := (F.map a₀) ⁻¹' (Ui : Set (F.obj i))
  let Fj : Set (F.obj k₀) := (F.map b₀) ⁻¹' (Uj : Set (F.obj j))
  have hEi_closed : IsClosed[constructibleTopology (F.obj k₀)] Ei := by
    -- Pull the constructibly closed compact open `Ui` back along the spectral transition map.
    dsimp [Ei]
    exact @IsClosed.preimage (F.obj k₀) (F.obj i)
      (constructibleTopology (F.obj k₀)) (constructibleTopology (F.obj i))
      (F.map a₀) (hF a₀).continuous_constructibleTopology _ <|
        compact_open_isClosed_constructibleTopology Ui
  have hFj_open : IsOpen[constructibleTopology (F.obj k₀)] Fj := by
    -- Pull the constructibly open compact open `Uj` back along the spectral transition map.
    dsimp [Fj]
    exact @IsOpen.preimage (F.obj k₀) (F.obj j)
      (constructibleTopology (F.obj k₀)) (constructibleTopology (F.obj j))
      (F.map b₀) (hF b₀).continuous_constructibleTopology _ <|
        compact_open_isOpen_constructibleTopology Uj
  have hsub_k₀ : (limit.π F k₀) ⁻¹' Ei ⊆ (limit.π F k₀) ⁻¹' Fj := by
    -- Rewrite the original limit-side inclusion on the common refinement stage `k₀`.
    intro x hx
    have hx' : x ∈ (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) := by
      rw [limit_projection_preimage_eq_stage_preimage (F := F) a₀ (Ui : Set (F.obj i))]
      exact hx
    have hx'' : x ∈ (limit.π F j) ⁻¹' (Uj : Set (F.obj j)) := hsub hx'
    rw [limit_projection_preimage_eq_stage_preimage (F := F) b₀ (Uj : Set (F.obj j))] at hx''
    exact hx''
  obtain ⟨k, c, hc⟩ :=
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := k₀) (E := Ei) (F := Fj)
      hF' hEi_closed hFj_open).mp hsub_k₀
  refine ⟨k, c ≫ a₀, c ≫ b₀, ?_⟩
  -- Compose the single-stage inclusion obtained at `k₀` with the chosen refinement arrow.
  simpa [Ei, Fj, Functor.map_comp, Set.preimage_preimage] using hc

-- Proof sketch: descend the quasi-compact open on the limit to one stage by part `(1)`, then use
-- part `(2)` to descend each inclusion in the finite union and cofilteredness to dominate the
-- resulting finite set of stages by a single refinement.
/-- Lemma 5.24.6 (3): if the pullback of a quasi-compact open from a stage is a finite union of
pullbacks of quasi-compact opens from the same stage, then after pulling back along some morphism
to that stage the corresponding finite union identity already holds there. -/
theorem exists_stage_of_preimage_eq_iUnion
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : J} {ι : Type u} [Fintype ι] (Ui : CompactOpens (F.obj i))
    (V : ι → CompactOpens (F.obj i))
    (hcover : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) =
      ⋃ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i))) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) = ⋃ t, (F.map a) ⁻¹' (V t : Set (F.obj i)) := by
  classical
  have hF' : ∀ ⦃j k : J⦄ (a : j ⟶ k), IsSpectralMap (F.map a) := fun {_ _} a ↦ hF a
  let _ := hF
  let Wsup : CompactOpens (F.obj i) := Finset.univ.sup V
  have hWsup_preimage :
      (limit.π F i) ⁻¹' (Wsup : Set (F.obj i)) =
        ⋃ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i)) := by
    -- The finite family is compressed into one compact open via `sup`.
    unfold Wsup
    exact preimage_finset_sup_eq_iUnion (f := limit.π F i) V
  have hUi_to_Wsup :
      (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) ⊆
        (limit.π F i) ⁻¹' (Wsup : Set (F.obj i)) := by
    -- The limit-side equality gives one inclusion immediately.
    intro x hx
    rw [hcover] at hx
    exact hWsup_preimage.symm ▸ hx
  have hWsup_to_Ui :
      (limit.π F i) ⁻¹' (Wsup : Set (F.obj i)) ⊆
        (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) := by
    -- The reverse inclusion is the same equality read backwards.
    intro x hx
    rw [hWsup_preimage] at hx
    exact hcover.symm ▸ hx
  have hUi_closed : IsClosed[constructibleTopology (F.obj i)] (Ui : Set (F.obj i)) := by
    exact compact_open_isClosed_constructibleTopology Ui
  have hUi_open : IsOpen[constructibleTopology (F.obj i)] (Ui : Set (F.obj i)) := by
    exact compact_open_isOpen_constructibleTopology Ui
  have hWsup_closed : IsClosed[constructibleTopology (F.obj i)] (Wsup : Set (F.obj i)) := by
    exact compact_open_isClosed_constructibleTopology Wsup
  have hWsup_open : IsOpen[constructibleTopology (F.obj i)] (Wsup : Set (F.obj i)) := by
    exact compact_open_isOpen_constructibleTopology Wsup
  obtain ⟨j₁, a₁, ha₁⟩ :=
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := i) (E := (Ui : Set (F.obj i))) (F := (Wsup : Set (F.obj i)))
      hF' hUi_closed hWsup_open).mp hUi_to_Wsup
  obtain ⟨j₂, a₂, ha₂⟩ :=
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := i) (E := (Wsup : Set (F.obj i))) (F := (Ui : Set (F.obj i)))
      hF' hWsup_closed hUi_open).mp hWsup_to_Ui
  obtain ⟨j, b₁, b₂, hb⟩ := IsCofiltered.cospan a₁ a₂
  have hleft :
      (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) ⊆
        (F.map (b₁ ≫ a₁)) ⁻¹' (Wsup : Set (F.obj i)) := by
    -- Pull the first eventual inclusion back to the common cospan stage.
    simpa [Functor.map_comp, Set.preimage_preimage] using Set.preimage_mono ha₁
  have hright :
      (F.map (b₁ ≫ a₁)) ⁻¹' (Wsup : Set (F.obj i)) ⊆
        (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) := by
    -- Pull the second eventual inclusion back and rewrite along the commuting square.
    simpa [hb, Functor.map_comp, Set.preimage_preimage] using Set.preimage_mono ha₂
  refine ⟨j, b₁ ≫ a₁, ?_⟩
  -- After both inclusions are descended to one stage, rewrite the finite supremum as a union.
  calc
    (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) =
        (F.map (b₁ ≫ a₁)) ⁻¹' (Wsup : Set (F.obj i)) :=
      Set.Subset.antisymm hleft hright
    _ = ⋃ t, (F.map (b₁ ≫ a₁)) ⁻¹' (V t : Set (F.obj i)) := by
      unfold Wsup
      exact preimage_finset_sup_eq_iUnion (f := F.map (b₁ ≫ a₁)) V

-- Proof sketch: argue exactly as in part `(3)`, replacing finite unions by finite intersections
-- and using that inverse images commute with intersections.
/-- Lemma 5.24.6 (4): if the pullback of a quasi-compact open from a stage is a finite
intersection of pullbacks of quasi-compact opens from the same stage, then after pulling back
along some morphism to that stage the corresponding finite intersection identity already holds
there. -/
theorem exists_stage_of_preimage_eq_iInter
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : J} {ι : Type u} [Fintype ι] (Ui : CompactOpens (F.obj i))
    (V : ι → CompactOpens (F.obj i))
    (hcover : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) =
      ⋂ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i))) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) = ⋂ t, (F.map a) ⁻¹' (V t : Set (F.obj i)) := by
  classical
  have hF' : ∀ ⦃j k : J⦄ (a : j ⟶ k), IsSpectralMap (F.map a) := fun {_ _} a ↦ hF a
  let _ := hF
  let Winf : CompactOpens (F.obj i) := Finset.univ.inf V
  have hWinf_preimage :
      (limit.π F i) ⁻¹' (Winf : Set (F.obj i)) =
        ⋂ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i)) := by
    -- The finite family is compressed into one compact open via `inf`.
    simpa [Winf] using preimage_finset_inf_eq_iInter (f := limit.π F i) V
  have hUi_to_Winf :
      (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) ⊆
        (limit.π F i) ⁻¹' (Winf : Set (F.obj i)) := by
    -- The limit-side equality gives one inclusion immediately.
    intro x hx
    rw [hcover] at hx
    exact hWinf_preimage.symm ▸ hx
  have hWinf_to_Ui :
      (limit.π F i) ⁻¹' (Winf : Set (F.obj i)) ⊆
        (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) := by
    -- The reverse inclusion is the same equality read backwards.
    intro x hx
    rw [hWinf_preimage] at hx
    exact hcover.symm ▸ hx
  have hUi_closed : IsClosed[constructibleTopology (F.obj i)] (Ui : Set (F.obj i)) := by
    exact compact_open_isClosed_constructibleTopology Ui
  have hUi_open : IsOpen[constructibleTopology (F.obj i)] (Ui : Set (F.obj i)) := by
    exact compact_open_isOpen_constructibleTopology Ui
  have hWinf_closed : IsClosed[constructibleTopology (F.obj i)] (Winf : Set (F.obj i)) := by
    exact compact_open_isClosed_constructibleTopology Winf
  have hWinf_open : IsOpen[constructibleTopology (F.obj i)] (Winf : Set (F.obj i)) := by
    exact compact_open_isOpen_constructibleTopology Winf
  obtain ⟨j₁, a₁, ha₁⟩ :=
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := i) (E := (Ui : Set (F.obj i))) (F := (Winf : Set (F.obj i)))
      hF' hUi_closed hWinf_open).mp hUi_to_Winf
  obtain ⟨j₂, a₂, ha₂⟩ :=
    (limit_projection_preimage_subset_iff_exists_stage_preimage_subset
      (X := F) (i := i) (E := (Winf : Set (F.obj i))) (F := (Ui : Set (F.obj i)))
      hF' hWinf_closed hUi_open).mp hWinf_to_Ui
  obtain ⟨j, b₁, b₂, hb⟩ := IsCofiltered.cospan a₁ a₂
  have hleft :
      (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) ⊆
        (F.map (b₁ ≫ a₁)) ⁻¹' (Winf : Set (F.obj i)) := by
    -- Pull the first eventual inclusion back to the common cospan stage.
    simpa [Functor.map_comp, Set.preimage_preimage] using Set.preimage_mono ha₁
  have hright :
      (F.map (b₁ ≫ a₁)) ⁻¹' (Winf : Set (F.obj i)) ⊆
        (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) := by
    -- Pull the second eventual inclusion back and rewrite along the commuting square.
    simpa [hb, Functor.map_comp, Set.preimage_preimage] using Set.preimage_mono ha₂
  refine ⟨j, b₁ ≫ a₁, ?_⟩
  -- After both inclusions are descended to one stage, rewrite the finite infimum as an
  -- intersection.
  calc
    (F.map (b₁ ≫ a₁)) ⁻¹' (Ui : Set (F.obj i)) =
        (F.map (b₁ ≫ a₁)) ⁻¹' (Winf : Set (F.obj i)) :=
      Set.Subset.antisymm hleft hright
    _ = ⋂ t, (F.map (b₁ ≫ a₁)) ⁻¹' (V t : Set (F.obj i)) := by
      simpa [Winf] using preimage_finset_inf_eq_iInter (f := F.map (b₁ ≫ a₁)) V

end
