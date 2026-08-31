module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace Topology

universe u v

/- Domain-style sampling for Example 7.7.4:
- primary domain: the opens site of a topological space and cover-dense basis functors;
- sampled owner declarations:
  `Topology.IsInducing.functor`,
  `TopCat.Opens.coverDense_iff_isBasis`,
  `Functor.inducedTopology`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
- source-facing layer: the generic-point extension of `X` and the explicit basic opens `U ∪ {none}`;
- core/canonical owner: the inducing inclusion `X ⟶ generic_point_extension X` and its opens
  functor `(generic_point_inclusion_isInducing X).functor`;
- bridge/view: the explicit set-theoretic description of the owner object
  `(generic_point_inclusion_isInducing X).functorObj U`.

Primitive data here are the topology on `Option X` and the explicit basic opens of the generic-point
extension. The functor on opens, the induced Grothendieck topology, and the sheaf comparison are
derived from the canonical owner `Topology.IsInducing.functor`, so the file should reuse that owner
instead of keeping a parallel hand-built opens functor. -/

/-- A presieve on `U : Opens X` is covering for the modified opens site if it is a usual open
cover and, in addition, a cover of `⊥` is required to contain at least one arrow. -/
def modified_opens_covering (X : TopCat.{u}) {U : Opens X} (R : Presieve U) : Prop :=
  (∀ x ∈ U, ∃ (V : Opens X) (f : V ⟶ U), R f ∧ x ∈ V) ∧
    (U = ⊥ → ∃ (V : Opens X) (f : V ⟶ U), R f)

/-
Internal predicate defining the opens of the generic-point extension.
-/
def IsOpenGenericPoint (X : TopCat.{u}) (s : Set (Option X)) : Prop :=
  s = ∅ ∨ none ∈ s ∧ IsOpen ((Option.some : X → Option X) ⁻¹' s)

theorem isOpenGenericPoint_univ (X : TopCat.{u}) :
    IsOpenGenericPoint X (Set.univ : Set (Option X)) := by
  right
  exact ⟨by simp, isOpen_univ⟩

theorem isOpenGenericPoint_inter (X : TopCat.{u}) {s t : Set (Option X)}
    (hs : IsOpenGenericPoint X s) (ht : IsOpenGenericPoint X t) :
    IsOpenGenericPoint X (s ∩ t) := by
  rcases hs with rfl | ⟨hs_none, hs_open⟩
  · left
    simp
  rcases ht with rfl | ⟨ht_none, ht_open⟩
  · left
    simp
  right
  refine ⟨by simp [hs_none, ht_none], ?_⟩
  simpa [Set.preimage_inter] using hs_open.inter ht_open

theorem preimage_some_sUnion (X : TopCat.{u}) (S : Set (Set (Option X))) :
    ((Option.some : X → Option X) ⁻¹' ⋃₀ S) =
      ⋃₀ (((Option.some : X → Option X) ⁻¹' ·) '' S) := by
  ext x
  simp

theorem isOpenGenericPoint_sUnion (X : TopCat.{u}) {S : Set (Set (Option X))}
    (hS : ∀ s ∈ S, IsOpenGenericPoint X s) :
    IsOpenGenericPoint X (⋃₀ S) := by
  by_cases h_empty : (⋃₀ S : Set (Option X)) = ∅
  · left
    exact h_empty
  · right
    have h_nonempty : (⋃₀ S : Set (Option X)).Nonempty := by
      rwa [Set.nonempty_iff_ne_empty]
    have h_none : (none : Option X) ∈ ⋃₀ S := by
      rcases h_nonempty with ⟨x, hx⟩
      rcases Set.mem_sUnion.mp hx with ⟨s, hsS, hxs⟩
      rcases hS s hsS with rfl | ⟨hs_none, hs_open⟩
      · simp at hxs
      · exact Set.mem_sUnion.mpr ⟨s, hsS, hs_none⟩
    refine ⟨h_none, ?_⟩
    rw [preimage_some_sUnion X S]
    apply isOpen_sUnion
    rintro _ ⟨s, hsS, rfl⟩
    rcases hS s hsS with rfl | ⟨hs_none, hs_open⟩
    · simp
    · simpa using hs_open

/-- The topology on `Option X` whose open sets are exactly `∅` together with the subsets
`U ∪ {none}` for `U` open in `X`. -/
@[reducible]
def generic_point_topology (X : TopCat.{u}) : TopologicalSpace (Option X) where
  IsOpen := IsOpenGenericPoint X
  isOpen_univ := isOpenGenericPoint_univ X
  isOpen_inter _ _ := isOpenGenericPoint_inter X
  isOpen_sUnion _ := isOpenGenericPoint_sUnion X

/-- Example 7.7.4: the space obtained from `X` by adjoining one generic point `none`, with opens
given by `∅` and the subsets `U ∪ {none}` for `U` open in `X`. -/
def generic_point_extension (X : TopCat.{u}) : TopCat.{u} where
  carrier := Option X
  str := generic_point_topology X

lemma generic_point_eq_insert_image (X : TopCat.{u}) {s : Set (Option X)} (hs : none ∈ s) :
    s = Set.insert (none : Option X)
      (Option.some '' ((Option.some : X → Option X) ⁻¹' s)) := by
  ext x
  cases x with
  | none =>
      constructor
      · intro _
        exact Set.mem_insert _ _
      · intro _
        exact hs
  | some x =>
      constructor <;> intro hx
      · exact Or.inr ⟨x, hx, rfl⟩
      · rcases hx with hnone | ⟨y, hy, hxy⟩
        · cases hnone
        · cases hxy
          exact hy

theorem preimage_some_insert_none_image (U : Set X) :
    ((Option.some : X → Option X) ⁻¹' Set.insert (none : Option X) (Option.some '' U)) = U := by
  ext x
  constructor
  · intro hx
    rcases hx with hnone | ⟨y, hy, hxy⟩
    · cases Option.some_ne_none x hnone
    · cases hxy
      exact hy
  · intro hx
    exact Or.inr ⟨x, hx, rfl⟩

/-- The canonical inclusion of `X` into its generic-point extension. -/
def generic_point_inclusion (X : TopCat.{u}) : X ⟶ generic_point_extension X := by
  let Y : TopCat.{u} := generic_point_extension X
  exact ⟨⟨(fun x ↦ (some x : Y)), by
    rw [continuous_def]
    intro s hs
    change IsOpenGenericPoint X s at hs
    rcases hs with rfl | ⟨_, hs_open⟩
    · change IsOpen (∅ : Set X)
      exact isOpen_empty
    · exact hs_open⟩⟩

/-- The topology on `X` is induced from the generic-point extension via the canonical inclusion. -/
theorem generic_point_inclusion_isInducing (X : TopCat.{u}) :
    Topology.IsInducing (generic_point_inclusion X) := by
  refine ⟨?_⟩
  refine TopologicalSpace.ext (by
    funext U
    apply propext
    constructor
    · intro hU
      refine ⟨Set.insert (none : generic_point_extension X)
          ((Option.some : X → generic_point_extension X) '' U), ?_, ?_⟩
      · change IsOpenGenericPoint X
          (Set.insert (none : Option X) (Option.some '' U))
        refine Or.inr ⟨Set.mem_insert _ _, ?_⟩
        rw [preimage_some_insert_none_image]
        exact hU
      · simpa [generic_point_inclusion, TopCat.ofHom] using
          (preimage_some_insert_none_image U)
    · rintro ⟨s, hs, rfl⟩
      simpa [generic_point_inclusion, TopCat.ofHom] using
        (show IsOpen ((Option.some : X → generic_point_extension X) ⁻¹' s) from by
          change IsOpenGenericPoint X s at hs
          rcases hs with rfl | ⟨_, hs_open⟩
          · simp
          · exact hs_open)
  )

-- Proof sketch: every nonempty open in `generic_point_extension X` contains `none`, so it is
-- recovered uniquely from its preimage under `Option.some`.
/-- The open subsets of the generic-point extension are exactly `∅` and the sets `U ∪ {none}` with
`U` open in `X`. -/
theorem isOpen_generic_point_extension_iff (X : TopCat.{u}) {s : Set (generic_point_extension X)} :
    IsOpen s ↔
      s = ∅ ∨ ∃ U : Set X, IsOpen U ∧
        s = Set.insert (none : generic_point_extension X)
          ((Option.some : X → generic_point_extension X) '' U) := by
  change IsOpenGenericPoint X s ↔
      s = ∅ ∨ ∃ U : Set X, IsOpen U ∧
        s = Set.insert (none : Option X) (Option.some '' U)
  constructor
  · intro hs
    rcases hs with rfl | ⟨hs_none, hs_open⟩
    · left
      rfl
    · right
      exact ⟨_, hs_open, by simpa using generic_point_eq_insert_image X hs_none⟩
  · intro hs
    rcases hs with rfl | ⟨U, hU, rfl⟩
    · left
      rfl
    · right
      refine ⟨Set.mem_insert _ _, ?_⟩
      rw [preimage_some_insert_none_image U]
      exact hU

-- Proof sketch: this is one of the defining open sets of `generic_point_extension X`.
/-- Every open subset `U` of `X` yields the open subset `U ∪ {none}` of the generic-point
extension. -/
theorem isOpen_insert_none_image_of_isOpen (X : TopCat.{u}) {U : Set X} (hU : IsOpen U) :
    IsOpen
      ((Set.insert (none : generic_point_extension X)
          ((Option.some : X → generic_point_extension X) '' U)) :
        Set (generic_point_extension X)) :=
  (isOpen_generic_point_extension_iff X).2 (Or.inr ⟨U, hU, rfl⟩)

def generic_point_insert_none_open (X : TopCat.{u}) (U : Opens X) :
    Opens (generic_point_extension X) :=
  ⟨((Set.insert (none : generic_point_extension X)
      ((Option.some : X → generic_point_extension X) '' (U : Set X))) :
        Set (generic_point_extension X)),
    isOpen_insert_none_image_of_isOpen X U.2⟩

theorem map_insert_none_image_basic_open (X : TopCat.{u}) (U : Opens X) :
    (Opens.map (generic_point_inclusion X)).obj
        (generic_point_insert_none_open X U) =
      U := by
  ext x
  change (some x : generic_point_extension X) ∈
      Set.insert (none : generic_point_extension X)
        ((Option.some : X → generic_point_extension X) '' (U : Set X)) ↔ x ∈ U
  constructor
  · intro hx
    rcases hx with hnone | ⟨y, hy, hxy⟩
    · cases Option.some_ne_none x hnone
    · cases hxy
      exact hy
  · intro hx
    exact Or.inr ⟨x, hx, rfl⟩

@[simp] theorem mem_generic_point_functorObj_iff (X : TopCat.{u}) (U : Opens X)
    {x : generic_point_extension X} :
    x ∈ (generic_point_inclusion_isInducing X).functorObj U ↔
      x ∈ Set.insert (none : generic_point_extension X)
        ((Option.some : X → generic_point_extension X) '' (U : Set X)) := by
  cases x with
  | none =>
      constructor
      · intro _
        exact Set.mem_insert _ _
      · intro _
        refine Opens.mem_sSup.mpr ⟨generic_point_insert_none_open X U, ?_, ?_⟩
        · exact map_insert_none_image_basic_open X U
        · exact Set.mem_insert _ _
  | some x =>
      constructor
      · intro hx
        exact Or.inr ⟨x,
          ((generic_point_inclusion_isInducing X).mem_functorObj_iff U).1
            (by simpa [generic_point_inclusion] using hx),
          rfl⟩
      · rintro (hnone | ⟨y, hy, hxy⟩)
        · cases hnone
        · cases hxy
          have hx :
              (generic_point_inclusion X) x ∈ (generic_point_inclusion_isInducing X).functorObj U :=
            ((generic_point_inclusion_isInducing X).mem_functorObj_iff U).2 hy
          simpa [generic_point_inclusion] using hx

instance generic_point_inclusion_functor_full (X : TopCat.{u}) :
    Functor.Full ((generic_point_inclusion_isInducing X).functor) where
  map_surjective {U V} f := ⟨homOfLE <| by
    intro x hx
    have hx' :
        (generic_point_inclusion X) x ∈ ((generic_point_inclusion_isInducing X).functor).obj U :=
      ((generic_point_inclusion_isInducing X).mem_functorObj_iff U).2 hx
    have hy' :
        (generic_point_inclusion X) x ∈ ((generic_point_inclusion_isInducing X).functor).obj V :=
      f.le hx'
    exact ((generic_point_inclusion_isInducing X).mem_functorObj_iff V).1 hy',
      Subsingleton.elim _ _⟩

instance generic_point_inclusion_functor_faithful (X : TopCat.{u}) :
    Functor.Faithful ((generic_point_inclusion_isInducing X).functor) where
  map_injective := by
    intro U V f g hfg
    exact Subsingleton.elim f g

-- Proof sketch: every nonempty open of the generic-point extension is itself one of the basic
-- opens `U ∪ {none}`, while the empty open requires no basis element because it has no points.
/-- The opens `U ∪ {none}` form a basis for the generic-point extension. -/
theorem generic_point_inclusion_functor_isBasis (X : TopCat.{u}) :
    Opens.IsBasis (Set.range ((generic_point_inclusion_isInducing X).functorObj)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro S x hx
  rcases (isOpen_generic_point_extension_iff X).1 S.2 with hS | ⟨U, hU, hS⟩
  · exfalso
    have hxS : x ∈ (S : Set (generic_point_extension X)) := hx
    change x ∈ S.carrier at hxS
    rw [hS] at hxS
    simp at hxS
  · let U' : Opens X := ⟨U, hU⟩
    refine ⟨(generic_point_inclusion_isInducing X).functorObj U', ⟨U', rfl⟩, ?_, ?_⟩
    · have hx' :
          x ∈ Set.insert (none : generic_point_extension X)
            ((Option.some : X → generic_point_extension X) '' U) := by
        have hxS : x ∈ (S : Set (generic_point_extension X)) := hx
        change x ∈ S.carrier at hxS
        rw [hS] at hxS
        exact hxS
      exact (mem_generic_point_functorObj_iff X U').2 <| by simpa [U'] using hx'
    · intro y hy
      have hy' :
          y ∈ Set.insert (none : generic_point_extension X)
            ((Option.some : X → generic_point_extension X) '' U) := by
        exact (mem_generic_point_functorObj_iff X U').1 hy
      have : y ∈ (S : Set (generic_point_extension X)) := by
        change y ∈ S.carrier
        rw [hS]
        exact hy'
      exact this

instance generic_point_inclusion_functor_isCoverDense (X : TopCat.{u}) :
    ((generic_point_inclusion_isInducing X).functor).IsCoverDense
      (Opens.grothendieckTopology (generic_point_extension X)) := by
  have hBasis :
      Opens.IsBasis (Set.range ((generic_point_inclusion_isInducing X).functorObj)) := by
    exact generic_point_inclusion_functor_isBasis X
  exact
    (TopCat.Opens.coverDense_iff_isBasis ((generic_point_inclusion_isInducing X).functor)).2
      hBasis

/-- The modified opens Grothendieck topology on `X`, presented canonically as the topology
induced from the cover-dense basis functor `U ↦ U ∪ {none}` into the opens site of the
generic-point extension. -/
def modified_opens_grothendieck_topology (X : TopCat.{u}) : GrothendieckTopology (Opens X) :=
  letI :
      ((generic_point_inclusion_isInducing X).functor).IsCoverDense
        (Opens.grothendieckTopology (generic_point_extension X)) :=
    generic_point_inclusion_functor_isCoverDense X
  letI :
      ((generic_point_inclusion_isInducing X).functor).LocallyCoverDense
        (Opens.grothendieckTopology (generic_point_extension X)) :=
    inferInstance
  (generic_point_inclusion_isInducing X).functor.inducedTopology
    (Opens.grothendieckTopology (generic_point_extension X))

/-- Helper for Example 7.7.4: a modified covering family on an open set contains at least one
arrow. -/
lemma modified_opens_covering_exists_arrow (X : TopCat.{u}) {U : Opens X} {R : Presieve U}
    (hR : modified_opens_covering X R) :
    ∃ (V : Opens X) (f : V ⟶ U), R f := by
  rcases hR with ⟨hcover, hbot⟩
  by_cases hU : U = ⊥
  · -- On `⊥`, the extra clause in the modified covering relation gives the arrow directly.
    exact hbot hU
  · classical
    -- Away from `⊥`, pick an actual point of `U` and use the ordinary open-cover clause.
    have hU_ne_empty : (U : Set X) ≠ ∅ := by
      intro h_empty
      apply hU
      apply le_antisymm
      · intro x hx
        have hxU : x ∈ (U : Set X) := hx
        simp [h_empty] at hxU
      · intro x hx
        exact False.elim (by simpa using hx)
    rcases Set.nonempty_iff_ne_empty.mpr hU_ne_empty with ⟨x, hx⟩
    rcases hcover x hx with ⟨V, f, hf, _⟩
    exact ⟨V, f, hf⟩

-- Proof sketch: the explicit covering families are exactly the coverings induced from the basis
-- `U ↦ U ∪ {none}` of the generic-point extension.
/-- The textbook covering relation on `Opens X` presents the induced Grothendieck topology coming
from the generic-point extension. -/
theorem modified_opens_covering_iff_mem_modified_opens_grothendieck_topology
    (X : TopCat.{u}) {U : Opens X} {R : Presieve U} :
    modified_opens_covering X R ↔
      Sieve.generate R ∈ modified_opens_grothendieck_topology X U := by
  let F := (generic_point_inclusion_isInducing X).functor
  have hforward :
      modified_opens_covering X R →
        Sieve.generate (Presieve.map F R) ∈
          Opens.grothendieckTopology (generic_point_extension X) (F.obj U) := by
    intro hR x hx
    -- Compare the textbook cover to pointwise covering of `F.obj U = U ∪ {none}`.
    cases x with
    | none =>
        -- The generic point `none` is covered exactly when the family contains some arrow.
        rcases modified_opens_covering_exists_arrow X hR with ⟨V, f, hf⟩
        refine ⟨F.obj V, F.map f, ?_, ?_⟩
        · exact Sieve.le_generate (Presieve.map F R) _ _ ⟨hf⟩
        · exact
            (mem_generic_point_functorObj_iff X V (x := (none : generic_point_extension X))).2
              (Set.mem_insert _ _)
    | some x0 =>
        -- A usual point `some x0` is covered by the ordinary open-cover clause on `U`.
        have hxU : x0 ∈ U := by
          have hxU' :=
            (mem_generic_point_functorObj_iff X U (x := (some x0 : generic_point_extension X))).1 hx
          rcases hxU' with hnone | ⟨y, hy, hxy⟩
          · cases hnone
          · cases hxy
            exact hy
        rcases hR.1 x0 hxU with ⟨V, f, hf, hxV⟩
        refine ⟨F.obj V, F.map f, ?_, ?_⟩
        · exact Sieve.le_generate (Presieve.map F R) _ _ ⟨hf⟩
        · exact
            (mem_generic_point_functorObj_iff X V (x := (some x0 : generic_point_extension X))).2
              (Or.inr ⟨x0, hxV, rfl⟩)
  have hback :
      Sieve.generate (Presieve.map F R) ∈
          Opens.grothendieckTopology (generic_point_extension X) (F.obj U) →
        modified_opens_covering X R := by
    intro hR
    refine ⟨?_, ?_⟩
    · intro x hx
      -- Covering `some x` in the generic-point extension recovers an original covering arrow.
      have hxF : (some x : generic_point_extension X) ∈ F.obj U := by
        exact (mem_generic_point_functorObj_iff X U).2 (Or.inr ⟨x, hx, rfl⟩)
      rcases hR (some x) hxF with ⟨W, f, hf, hxW⟩
      rcases hf with ⟨Y, i, g, hg, rfl⟩
      rw [Presieve.map_iff] at hg
      rcases hg with ⟨V, hV, g0, hg0, _⟩
      subst hV
      have hxV' : (some x : generic_point_extension X) ∈ F.obj V := i.le hxW
      have hxV : x ∈ V := by
        have hxV'' :=
          (mem_generic_point_functorObj_iff X V (x := (some x : generic_point_extension X))).1 hxV'
        rcases hxV'' with hnone | ⟨y, hy, hxy⟩
        · cases hnone
        · cases hxy
          exact hy
      exact ⟨V, g0, hg0, hxV⟩
    · intro _
      -- When `U = ⊥`, covering the generic point `none` forces the family to be nonempty.
      have hnone : (none : generic_point_extension X) ∈ F.obj U := by
        exact (mem_generic_point_functorObj_iff X U (x := (none : generic_point_extension X))).2
          (Set.mem_insert _ _)
      rcases hR none hnone with ⟨W, f, hf, _⟩
      rcases hf with ⟨Y, i, g, hg, rfl⟩
      rw [Presieve.map_iff] at hg
      rcases hg with ⟨V, hV, g0, hg0, _⟩
      subst hV
      exact ⟨V, g0, hg0⟩
  have hrewrite :
      Sieve.generate R ∈ modified_opens_grothendieck_topology X U ↔
        Sieve.generate (Presieve.map F R) ∈
          Opens.grothendieckTopology (generic_point_extension X) (F.obj U) := by
    constructor
    · intro hR
      have hR' :
          Sieve.functorPushforward F (Sieve.generate R) ∈
            Opens.grothendieckTopology (generic_point_extension X) (F.obj U) := by
        simpa [modified_opens_grothendieck_topology, F, Functor.mem_inducedTopology_sieves_iff] using
          hR
      simpa [Sieve.generate_map_eq_functorPushforward] using hR'
    · intro hR
      have hR' :
          Sieve.functorPushforward F (Sieve.generate R) ∈
            Opens.grothendieckTopology (generic_point_extension X) (F.obj U) := by
        simpa [Sieve.generate_map_eq_functorPushforward] using hR
      simpa [modified_opens_grothendieck_topology, F, Functor.mem_inducedTopology_sieves_iff] using
        hR'
  constructor
  · intro hR
    -- Rewrite the induced topology membership to an ordinary covering condition upstairs.
    exact hrewrite.mpr (hforward hR)
  · intro hR
    -- Pull a covering sieve upstairs back down to the explicit textbook covering predicate.
    exact hback (hrewrite.mp hR)

-- Proof sketch: the singleton family `{⊥ ⟶ ⊥}` covers because the ordinary covering condition on
-- `⊥` is vacuous, and the extra modified condition is witnessed by the unique identity arrow.
/-- The identity family on `⊥` is a covering in the modified opens site. -/
theorem modified_opens_covering_bot_singleton (X : TopCat.{u}) :
    modified_opens_covering X (Presieve.singleton (𝟙 (⊥ : Opens X))) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact False.elim (by simpa using hx)
  · intro hU
    refine ⟨⊥, 𝟙 _, ?_⟩
    exact Presieve.singleton_self (𝟙 (⊥ : Opens X))

-- Proof sketch: this is the comparison lemma for the cover-dense opens functor induced by the
-- canonical inclusion `X ⟶ generic_point_extension X`.
/-- Set-valued sheaves on the modified opens site are exactly sheaves on the generic-point
extension. -/
noncomputable def modified_opens_type_sheaf_equiv (X : TopCat.{u}) :
    Sheaf (modified_opens_grothendieck_topology X) (Type (max u v)) ≌
      TopCat.Sheaf (Type (max u v)) (generic_point_extension X) := by
  letI :
      ((generic_point_inclusion_isInducing X).functor).IsCoverDense
        (Opens.grothendieckTopology (generic_point_extension X)) :=
    generic_point_inclusion_functor_isCoverDense X
  letI :
      ((generic_point_inclusion_isInducing X).functor).LocallyCoverDense
        (Opens.grothendieckTopology (generic_point_extension X)) :=
    inferInstance
  letI :
      ∀ X₁ : (Opens (generic_point_extension X))ᵒᵖ,
        Limits.HasLimitsOfShape
          (StructuredArrow X₁ ((generic_point_inclusion_isInducing X).functor).op)
            (Type (max u v)) :=
    fun _ ↦ by infer_instance
  simpa [modified_opens_grothendieck_topology] using
    ((generic_point_inclusion_isInducing X).functor).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology (generic_point_extension X)) (Type (max u v))
