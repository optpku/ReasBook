/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Lemma_2_4_2
import AlgebraicTopology_May_1999.Chap02.Lemma_2_4_4
import AlgebraicTopology_May_1999.Chap02.Proposition_2_4_6
import AlgebraicTopology_May_1999.Chap02.Theorem_2_7_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory Limits
open unitInterval
open scoped unitInterval

noncomputable section

variable {ι : Type v}

/-- Helper for Proposition 2.8.1: an open subset determines its Sierpinski-valued characteristic
map. -/
private noncomputable def opensIndicator
    {Y : Type u} [TopologicalSpace Y]
    (U : TopologicalSpace.Opens (TopCat.of Y)) :
    TopCat.of Y ⟶ TopCat.of (ULift Prop) :=
  TopCat.ofHom
    ⟨fun y ↦ ULift.up (y ∈ U), continuous_uliftUp.comp ((isOpen_iff_continuous_mem).mp U.isOpen)⟩

/-- Helper for Proposition 2.8.1: the constantly true Sierpinski-valued map. -/
private noncomputable def trueIndicator (Y : TopCat) : Y ⟶ TopCat.of (ULift Prop) :=
  TopCat.ofHom (ContinuousMap.const Y (ULift.up True))

/-- A based space has a contractible neighborhood of its chosen basepoint whose identity map is
homotopic relative to that basepoint to the constant map at that basepoint. -/
def has_contractible_base_neighborhood (X : Under (⊤_ TopCat)) : Prop :=
  ∃ V : TopologicalSpace.Opens X.right,
    ∃ hxV : underTopBasepoint X ∈ V,
      ContractibleSpace V ∧
        (ContinuousMap.id V).HomotopicRel
          (ContinuousMap.const V ⟨underTopBasepoint X, hxV⟩)
          {⟨underTopBasepoint X, hxV⟩}

/-- The canonical homomorphism from the free product of the fundamental groups of a family of
based spaces to the fundamental group of their wedge sum, realized as the coproduct in
`Under (⊤_ TopCat)`. -/
abbrev wedge_fundamental_group_comparison
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X] :
    Monoid.CoprodI (fun i ↦ FundamentalGroup (X i).right (underTopBasepoint (X i))) →*
      FundamentalGroup (∐ X).right (underTopBasepoint (∐ X)) :=
  Monoid.CoprodI.lift fun i ↦ (fundamentalGroupFunctor.map (Sigma.ι X i)).hom

/-- Helper for Proposition 2.8.1: a chosen contractible neighborhood of the basepoint is path
connected. -/
theorem contractible_base_neighborhood_path_connected
    (X : Under (⊤_ TopCat))
    (hX : has_contractible_base_neighborhood X) :
    ∃ V : TopologicalSpace.Opens X.right,
      underTopBasepoint X ∈ V ∧ PathConnectedSpace V := by
  rcases hX with ⟨V, hxV, hV, _hbase⟩
  -- Contractibility gives the path-connectedness needed for the van Kampen cover members.
  let _ : ContractibleSpace V := hV
  refine ⟨V, hxV, ?_⟩
  infer_instance

/-- Helper for Proposition 2.8.1: the fundamental group of a chosen contractible base
neighborhood is trivial at the induced basepoint. -/
theorem contractible_base_neighborhood_fundamentalGroup_subsingleton
    (X : Under (⊤_ TopCat))
    (hX : has_contractible_base_neighborhood X) :
    ∃ V : TopologicalSpace.Opens X.right,
      ∃ hxV : underTopBasepoint X ∈ V,
        Subsingleton (FundamentalGroup V ⟨underTopBasepoint X, hxV⟩) := by
  rcases hX with ⟨V, hxV, hV, _hbase⟩
  -- The contractible neighborhood contributes the trivial vertex group in the star-cover diagram.
  have hsub : Subsingleton (FundamentalGroup V ⟨underTopBasepoint X, hxV⟩) := by
    let _ : SimplyConnectedSpace V := SimplyConnectedSpace.ofContractible V
    change
      Subsingleton
        (Path.Homotopic.Quotient
          ((⟨underTopBasepoint X, hxV⟩ : V))
          ((⟨underTopBasepoint X, hxV⟩ : V)))
    infer_instance
  exact ⟨V, hxV, hsub⟩

/-- Helper for Proposition 2.8.1: loops in a contractible open subset map trivially into the
ambient fundamental group. -/
theorem fundamentalGroup_map_from_contractible_open_eq_one
    {X : Type u} [TopologicalSpace X]
    (V : TopologicalSpace.Opens (TopCat.of X))
    [ContractibleSpace V]
    (x : V)
    (γ : FundamentalGroup V x) :
    FundamentalGroup.map (TopologicalSpace.Opens.inclusion' V).hom x γ = 1 := by
  -- First collapse the loop inside the contractible open subset itself.
  have hsub : Subsingleton (FundamentalGroup V x) := by
    let _ : SimplyConnectedSpace V := SimplyConnectedSpace.ofContractible V
    change Subsingleton (Path.Homotopic.Quotient x x)
    infer_instance
  have hγ : γ = 1 := hsub.elim _ _
  -- Functoriality then sends that unique element to the identity in the ambient group.
  rw [hγ]
  exact map_one _

/-- Helper for Proposition 2.8.1: a homomorphism out of a subsingleton source is unique. -/
private theorem subsingleton_monoidHom_ext
    {A B : Type*} [Monoid A] [Monoid B] [Subsingleton A]
    (f g : A →* B) :
    f = g := by
  -- Every element of the source is the unit, so both homomorphisms agree pointwise.
  ext a
  have ha : a = 1 := Subsingleton.elim _ _
  rw [ha, map_one, map_one]

/-- Helper for Proposition 2.8.1: each chosen neighborhood contracts to the actual distinguished
basepoint used in the wedge construction. -/
theorem contractible_neighborhood_id_homotopic_basepoint_const
    (X : ι → Under (⊤_ TopCat))
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (hbase : ∀ i,
      (ContinuousMap.id (V i)).HomotopicRel
        (ContinuousMap.const (V i) ⟨underTopBasepoint (X i), hxV i⟩)
        {⟨underTopBasepoint (X i), hxV i⟩})
    (i : ι) :
    (ContinuousMap.id (V i)).HomotopicRel
      (ContinuousMap.const (V i) ⟨underTopBasepoint (X i), hxV i⟩)
      {⟨underTopBasepoint (X i), hxV i⟩} := by
  exact hbase i

/-- Helper for Proposition 2.8.1: each leg of the public van Kampen cocone is the inclusion map on
fundamental groups for the corresponding open-cover member. -/
private theorem fundamental_group_cover_cocone_app_eq_map_inclusion
    {X : Type u} [TopologicalSpace X]
    {ι : Type v}
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (i : TopologicalSpace.IsOpenCover.Index O) :
    ((fundamental_group_cover_cocone O x hx).ι.app i).hom =
      FundamentalGroup.map (TopologicalSpace.Opens.inclusion' (O i)).hom ⟨x, hx i⟩ := by
  -- The canonical cocone leg is definitionally the fundamental-group map of the open inclusion.
  ext g
  induction g using Path.Homotopic.Quotient.ind with
  | mk γ =>
      simpa [fundamental_group_cover_cocone, FundamentalGroup.map] using
        (FundamentalGroup.mapOfEq_apply (f := _) (h := rfl) (p := γ))

/-- Helper for Proposition 2.8.1: each morphism in the public van Kampen diagram is the induced
map on fundamental groups for the corresponding inclusion between cover members. -/
private theorem fundamental_group_cover_diagram_map_eq_map_of_inclusion
    {X : Type u} [TopologicalSpace X]
    {ι : Type v}
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    {i j : TopologicalSpace.IsOpenCover.Index O} (f : i ⟶ j) :
    ((fundamental_group_cover_diagram O x hx).map f).hom =
      FundamentalGroup.map (((TopologicalSpace.Opens.toTopCat (TopCat.of X)).map f.hom).hom)
        ⟨x, hx i⟩ := by
  -- The diagram morphism is again the fundamental-group map of the literal inclusion morphism.
  ext g
  induction g using Path.Homotopic.Quotient.ind with
  | mk γ =>
      simpa [fundamental_group_cover_diagram, FundamentalGroup.map] using
        (FundamentalGroup.mapOfEq_apply (f := _) (h := rfl) (p := γ))

/-- Helper for Proposition 2.8.1: the wedge coproduct cocone in `Under (⊤_ TopCat)` induces the
expected wide-pushout colimit cocone on the underlying spaces. -/
noncomputable def wedge_wide_pushout_is_colimit
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X] :
    IsColimit
      (WidePushoutShape.mkCocone
        (F := WidePushoutShape.wideSpan
          (⊤_ TopCat)
          (fun i ↦ (X i).right)
          (fun i ↦ (X i).hom))
        ((∐ X).hom)
        (fun i ↦ (Sigma.ι X i).right)
        (fun i ↦ by
          simpa using (Sigma.ι X i).w.symm)) := by
  refine IsColimit.ofExistsUnique fun s ↦ ?_
  let p : ∀ i, X i ⟶ Under.mk (s.ι.app none) := fun i ↦
    Under.homMk (s.ι.app (some i)) (s.w (WidePushoutShape.Hom.init i))
  refine ⟨(Sigma.desc p).right, ?_, ?_⟩
  · intro j
    cases j with
    | none =>
        -- The descended map is a morphism in `Under`, so it preserves the common basepoint leg.
        exact (Sigma.desc p).w
    | some i =>
        -- On each summand, the descended map agrees with the specified cocone leg by coproduct
        -- universal property in `Under`.
        simpa [p] using congrArg (fun f => f.right) (Sigma.ι_desc p i)
  · intro m hm
    let δ : ∀ k : Fin 2, ∐ X ⟶ Under.mk (s.ι.app none)
      | 0 => Under.homMk m (hm none)
      | 1 => Under.homMk (Sigma.desc p).right (Sigma.desc p).w
    have hδ :
        δ 0 = δ 1 := by
      apply Sigma.hom_ext
      intro i
      ext x
      have hleft : (Sigma.ι X i ≫ δ 0).right = s.ι.app (some i) := by
        have hcomp : (Sigma.ι X i ≫ δ 0).right = (Sigma.ι X i).right ≫ m := by
          simp [δ, Under.comp_right]
        have hfac : (Sigma.ι X i).right ≫ m = s.ι.app (some i) := by
          simpa using hm (some i)
        exact hcomp.trans hfac
      have hright : (Sigma.ι X i ≫ δ 1).right = s.ι.app (some i) := by
        have hcomp : (Sigma.ι X i ≫ δ 1).right = (Sigma.ι X i).right ≫ (Sigma.desc p).right := by
          simp [δ, Under.comp_right]
        have hfac : (Sigma.ι X i).right ≫ (Sigma.desc p).right = s.ι.app (some i) := by
          simpa [p] using congrArg (fun f => f.right) (Sigma.ι_desc p i)
        exact hcomp.trans hfac
      have hEq : (Sigma.ι X i ≫ δ 0).right = (Sigma.ι X i ≫ δ 1).right :=
        hleft.trans hright.symm
      exact congrArg (fun f => f x) hEq
    simpa [δ] using congrArg (fun f => f.right) hδ

/-- Helper for Proposition 2.8.1: a family of summand opens containing every wedge basepoint
descends to an ambient open subset of the wedge with the prescribed pullbacks. -/
private theorem wide_pushout_open_of_compatible_pullbacks
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (U : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxU : ∀ i, underTopBasepoint (X i) ∈ U i) :
    ∃ W : TopologicalSpace.Opens ((∐ X).right),
      (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤ ∧
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j := by
  let c :
      Cocone
        (WidePushoutShape.wideSpan
          (⊤_ TopCat)
          (fun i ↦ (X i).right)
          (fun i ↦ (X i).hom)) :=
    WidePushoutShape.mkCocone
      (F := WidePushoutShape.wideSpan
        (⊤_ TopCat)
        (fun i ↦ (X i).right)
        (fun i ↦ (X i).hom))
      (trueIndicator (⊤_ TopCat))
      (fun i ↦ opensIndicator (U i))
      (fun i ↦ by
        -- Compatibility along the head leg is exactly the assumption that each basepoint lies in
        -- the chosen summand open.
        ext u
        have hinj : Function.Injective (TopCat.terminalIsoPUnit.hom : (⊤_ TopCat) → PUnit) := by
          intro a b hab
          simpa using congrArg (TopCat.terminalIsoPUnit.inv : PUnit → (⊤_ TopCat)) hab
        have hu : u = TopCat.terminalIsoPUnit.inv PUnit.unit := by
          apply hinj
          simp
        rw [hu]
        change ((X i).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) ∈ U i) ↔ True
        exact ⟨fun _ ↦ trivial, fun _ ↦ hxU i⟩)
  let φ : (∐ X).right ⟶ TopCat.of (ULift Prop) :=
    (wedge_wide_pushout_is_colimit X).desc c
  let W : TopologicalSpace.Opens ((∐ X).right) :=
    ⟨{x | (φ.hom x).down}, by
      -- The descended characteristic map cuts out an open `True`-locus in the wedge.
      have hcont : Continuous fun x : (∐ X).right ↦ (φ.hom x).down :=
        continuous_uliftDown.comp φ.hom.continuous
      simpa using (isOpen_iff_continuous_mem).2 hcont⟩
  refine ⟨W, ?_, ?_⟩
  · ext u
    -- Pulling back along the terminal leg recovers the constant-`True` characteristic map.
    change (φ.hom (((∐ X).hom) u)).down ↔ True
    have hfac :=
      congrArg
        (fun f : (⊤_ TopCat) ⟶ TopCat.of (ULift Prop) => f.hom u)
        ((wedge_wide_pushout_is_colimit X).fac c none)
    simpa [W, φ, c, trueIndicator, opensIndicator] using congrArg ULift.down hfac
  · intro j
    ext y
    -- On each summand, the descended characteristic map is the original one for `U j`.
    change (φ.hom (((Sigma.ι X j).right) y)).down ↔ y ∈ U j
    have hfac :=
      congrArg
        (fun f : (X j).right ⟶ TopCat.of (ULift Prop) => f.hom y)
        ((wedge_wide_pushout_is_colimit X).fac c (some j))
    simpa [W, φ, c, trueIndicator, opensIndicator] using congrArg ULift.down hfac

/-- Helper for Proposition 2.8.1: the `some i` star family uses the full distinguished summand and
the chosen neighborhoods on the others. -/
private noncomputable def wedge_star_some_family
    (X : ι → Under (⊤_ TopCat)) [DecidableEq ι]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (i : ι) :
    ∀ j, TopologicalSpace.Opens (X j).right :=
  fun j ↦ if j = i then (⊤ : TopologicalSpace.Opens (X j).right) else V j

/-- Helper for Proposition 2.8.1: the `some i` star pattern still contains every wedge
basepoint on every summand. -/
private theorem wedge_star_some_family_basepoint_mem
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (i : ι) :
    ∀ j, underTopBasepoint (X j) ∈
      @wedge_star_some_family ι X (Classical.decEq ι) V i j := by
  classical
  intro j
  by_cases hji : j = i
  · simp [wedge_star_some_family, hji]
  · simpa [wedge_star_some_family, hji] using hxV j

/-- Helper for Proposition 2.8.1: the source-faithful `Option ι`-indexed star cover on the wedge,
with `none` for the common core and `some i` for the star centered on the `i`-th summand. -/
private noncomputable def wedge_star_cover
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i) :
    Option ι → TopologicalSpace.Opens ((∐ X).right)
  | none =>
      Classical.choose (wide_pushout_open_of_compatible_pullbacks X V hxV)
  | some i =>
      Classical.choose
        (wide_pushout_open_of_compatible_pullbacks X
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_some_family_basepoint_mem X V hxV i))

/-- Helper for Proposition 2.8.1: the common core star member pulls back to the chosen
contractible neighborhood on each summand. -/
private theorem wedge_star_cover_none_pullback
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (j : ι) :
    (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj
        (wedge_star_cover X V hxV none) = V j := by
  -- The `none` member is defined by descending exactly the family `V`.
  exact (Classical.choose_spec (wide_pushout_open_of_compatible_pullbacks X V hxV)).2 j

/-- Helper for Proposition 2.8.1: the `i`-th star member contains the entire distinguished
summand. -/
private theorem wedge_star_cover_some_same_pullback
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (i : ι) :
    (TopologicalSpace.Opens.map ((Sigma.ι X i).right)).obj
        (wedge_star_cover X V hxV (some i)) = ⊤ := by
  -- On the distinguished summand, the specialized star pattern uses the full space `⊤`.
  simpa [wedge_star_cover, wedge_star_some_family] using
    (Classical.choose_spec
      (wide_pushout_open_of_compatible_pullbacks X
        (@wedge_star_some_family ι X (Classical.decEq ι) V i)
        (wedge_star_some_family_basepoint_mem X V hxV i))).2 i

/-- Helper for Proposition 2.8.1: off the distinguished summand, a star member restricts to the
chosen basepoint neighborhood. -/
private theorem wedge_star_cover_some_ne_pullback
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    {i j : ι} (hji : j ≠ i) :
    (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj
        (wedge_star_cover X V hxV (some i)) = V j := by
  -- Off the distinguished summand, the star pattern keeps the original neighborhood `V j`.
  simpa [wedge_star_cover, wedge_star_some_family, hji] using
    (Classical.choose_spec
      (wide_pushout_open_of_compatible_pullbacks X
        (@wedge_star_some_family ι X (Classical.decEq ι) V i)
        (wedge_star_some_family_basepoint_mem X V hxV i))).2 j

/-- Helper for Proposition 2.8.1: every star-cover member contains the wedge basepoint, so its
pullback along the terminal leg is the top open subset. -/
private theorem wedge_star_cover_head_pullback
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (o : Option ι) :
    (TopologicalSpace.Opens.map ((∐ X).hom)).obj
        (wedge_star_cover X V hxV o) = ⊤ := by
  cases o with
  | none =>
      -- The `none` member is descended from the family `V`, which contains every basepoint.
      exact (Classical.choose_spec (wide_pushout_open_of_compatible_pullbacks X V hxV)).1
  | some i =>
      -- The same terminal-leg formula holds for the specialized `some i` star family.
      exact (Classical.choose_spec
        (wide_pushout_open_of_compatible_pullbacks X
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_some_family_basepoint_mem X V hxV i))).1

/-- Helper for Proposition 2.8.1: the common core member restricts to `V j` on the `j`-th summand
at the level of point membership. -/
private theorem mem_wedge_star_cover_none_pullback_iff
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (j : ι) (y : (X j).right) :
    ((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV none) ↔ y ∈ V j := by
  -- This is just the pullback formula for the `none` member, rewritten pointwise.
  change y ∈ (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj
      (wedge_star_cover X V hxV none) ↔ y ∈ V j
  rw [wedge_star_cover_none_pullback X V hxV j]

/-- Helper for Proposition 2.8.1: the distinguished summand lies entirely inside its own star
member, pointwise on the `i`-th summand. -/
private theorem mem_wedge_star_cover_some_same_pullback_iff
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (i : ι) (y : (X i).right) :
    ((Sigma.ι X i).right y ∈ wedge_star_cover X V hxV (some i)) := by
  -- The pullback of the `i`-th star member along the `i`-th summand is `⊤`.
  change y ∈ (TopologicalSpace.Opens.map ((Sigma.ι X i).right)).obj
      (wedge_star_cover X V hxV (some i))
  rw [wedge_star_cover_some_same_pullback X V hxV i]
  trivial

/-- Helper for Proposition 2.8.1: away from its distinguished summand, a star member restricts to
the chosen neighborhood `V j`, pointwise. -/
private theorem mem_wedge_star_cover_some_ne_pullback_iff
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    {i j : ι} (hji : j ≠ i) (y : (X j).right) :
    ((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV (some i)) ↔ y ∈ V j := by
  -- Off the distinguished summand, the star member has the original neighborhood pullback.
  change y ∈ (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj
      (wedge_star_cover X V hxV (some i)) ↔ y ∈ V j
  rw [wedge_star_cover_some_ne_pullback X V hxV hji]

/-- Helper for Proposition 2.8.1: every point on the head leg lies in every star member. -/
private theorem mem_wedge_star_cover_head
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (o : Option ι) (u : ⊤_ TopCat) :
    ((∐ X).hom u ∈ wedge_star_cover X V hxV o) := by
  -- The head pullback of every star member is `⊤`.
  change u ∈ (TopologicalSpace.Opens.map ((∐ X).hom)).obj (wedge_star_cover X V hxV o)
  rw [wedge_star_cover_head_pullback X V hxV o]
  trivial

/-- Helper for Proposition 2.8.1: an open subset of the wedge is determined by its pullbacks to
the head leg and to every summand leg of the wide pushout presentation. -/
private theorem wedge_star_cover_ext
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W W' : TopologicalSpace.Opens ((∐ X).right))
    (hhead :
      (TopologicalSpace.Opens.map ((∐ X).hom)).obj W =
        (TopologicalSpace.Opens.map ((∐ X).hom)).obj W')
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W =
        (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W') :
    W = W' := by
  let c :
      Cocone
        (WidePushoutShape.wideSpan
          (⊤_ TopCat)
          (fun i ↦ (X i).right)
          (fun i ↦ (X i).hom)) :=
    WidePushoutShape.mkCocone
      (F := WidePushoutShape.wideSpan
        (⊤_ TopCat)
        (fun i ↦ (X i).right)
        (fun i ↦ (X i).hom))
      ((∐ X).hom)
      (fun i ↦ (Sigma.ι X i).right)
      (fun i ↦ by
        simpa using (Sigma.ι X i).w.symm)
  ext x
  constructor
  · intro hx
    -- Represent the wedge point along one leg of the wide pushout and compare the two pullbacks.
    obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep
      (WidePushoutShape.wideSpan (⊤_ TopCat) (fun i ↦ (X i).right) (fun i ↦ (X i).hom))
      (wedge_wide_pushout_is_colimit X) x
    cases j with
    | none =>
        have hy : y ∈ (TopologicalSpace.Opens.map ((∐ X).hom)).obj W := by
          simpa [c] using hx
        have hy' : y ∈ (TopologicalSpace.Opens.map ((∐ X).hom)).obj W' := by
          rw [← hhead]
          exact hy
        simpa [c] using hy'
    | some i =>
        have hy : y ∈ (TopologicalSpace.Opens.map ((Sigma.ι X i).right)).obj W := by
          simpa [c] using hx
        have hy' : y ∈ (TopologicalSpace.Opens.map ((Sigma.ι X i).right)).obj W' := by
          rw [← hsummand i]
          exact hy
        simpa [c] using hy'
  · intro hx
    -- The reverse implication uses the same representative analysis with the equalities reversed.
    obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep
      (WidePushoutShape.wideSpan (⊤_ TopCat) (fun i ↦ (X i).right) (fun i ↦ (X i).hom))
      (wedge_wide_pushout_is_colimit X) x
    cases j with
    | none =>
        have hy : y ∈ (TopologicalSpace.Opens.map ((∐ X).hom)).obj W' := by
          simpa [c] using hx
        have hy' : y ∈ (TopologicalSpace.Opens.map ((∐ X).hom)).obj W := by
          rw [hhead]
          exact hy
        simpa [c] using hy'
    | some i =>
        have hy : y ∈ (TopologicalSpace.Opens.map ((Sigma.ι X i).right)).obj W' := by
          simpa [c] using hx
        have hy' : y ∈ (TopologicalSpace.Opens.map ((Sigma.ι X i).right)).obj W := by
          rw [hsummand i]
          exact hy
        simpa [c] using hy'

/-- Helper for Proposition 2.8.1: intersecting any star member with the common core returns the
common core. -/
private theorem wedge_star_cover_inf_none
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (o : Option ι) :
    wedge_star_cover X V hxV none ⊓ wedge_star_cover X V hxV o =
      wedge_star_cover X V hxV none := by
  apply wedge_star_cover_ext X
  · -- Every star member contains the wedge basepoint, so the head pullback stays `⊤`.
    ext u
    change (((∐ X).hom u ∈ wedge_star_cover X V hxV none) ∧
        ((∐ X).hom u ∈ wedge_star_cover X V hxV o)) ↔
      ((∐ X).hom u ∈ wedge_star_cover X V hxV none)
    constructor
    · intro hu
      simpa using hu.1
    · intro hu
      exact ⟨hu, mem_wedge_star_cover_head X V hxV o u⟩
  · intro j
    -- On each summand, the intersection reduces to `V j`.
    cases o with
    | none =>
        ext y
        change (((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV none) ∧
            ((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV none)) ↔
          ((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV none)
        simpa [mem_wedge_star_cover_none_pullback_iff]
    | some i =>
        by_cases hji : j = i
        · subst j
          ext y
          change (((Sigma.ι X i).right y ∈ wedge_star_cover X V hxV none) ∧
              ((Sigma.ι X i).right y ∈ wedge_star_cover X V hxV (some i))) ↔
            ((Sigma.ι X i).right y ∈ wedge_star_cover X V hxV none)
          constructor
          · intro hy
            exact hy.1
          · intro hy
            exact ⟨hy, mem_wedge_star_cover_some_same_pullback_iff X V hxV i y⟩
        · ext y
          change (((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV none) ∧
              ((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV (some i))) ↔
            ((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV none)
          constructor
          · intro hy
            exact hy.1
          · intro hy
            have hyV : y ∈ V j := (mem_wedge_star_cover_none_pullback_iff X V hxV j y).mp hy
            exact ⟨hy, (mem_wedge_star_cover_some_ne_pullback_iff X V hxV hji y).mpr hyV⟩

/-- Helper for Proposition 2.8.1: intersecting the `i`-th star member with itself is idempotent. -/
private theorem wedge_star_cover_inf_some_same
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (i : ι) :
    wedge_star_cover X V hxV (some i) ⊓ wedge_star_cover X V hxV (some i) =
      wedge_star_cover X V hxV (some i) := by
  apply wedge_star_cover_ext X
  · -- The head pullback is still `⊤`, so nothing changes on the common basepoint leg.
    ext u
    change (((∐ X).hom u ∈ wedge_star_cover X V hxV (some i)) ∧
        ((∐ X).hom u ∈ wedge_star_cover X V hxV (some i))) ↔
      ((∐ X).hom u ∈ wedge_star_cover X V hxV (some i))
    constructor
    · intro hu
      simpa using hu.1
    · intro hu
      exact ⟨hu, hu⟩
  · intro j
    -- The distinguished summand stays whole, and every other summand stays `V j`.
    by_cases hji : j = i
    · subst j
      ext y
      change (((Sigma.ι X i).right y ∈ wedge_star_cover X V hxV (some i)) ∧
          ((Sigma.ι X i).right y ∈ wedge_star_cover X V hxV (some i))) ↔
        ((Sigma.ι X i).right y ∈ wedge_star_cover X V hxV (some i))
      constructor
      · intro hy
        simpa using hy.1
      · intro hy
        exact ⟨hy, hy⟩
    · ext y
      change (((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV (some i)) ∧
          ((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV (some i))) ↔
        ((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV (some i))
      simpa [mem_wedge_star_cover_some_ne_pullback_iff X V hxV hji y]

/-- Helper for Proposition 2.8.1: intersecting two distinct starred summands collapses to the
common core. -/
private theorem wedge_star_cover_inf_some_ne
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    {i j : ι} (hij : i ≠ j) :
    wedge_star_cover X V hxV (some i) ⊓ wedge_star_cover X V hxV (some j) =
      wedge_star_cover X V hxV none := by
  apply wedge_star_cover_ext X
  · -- Every star member contains the wedge basepoint, so the head pullback again stays `⊤`.
    ext u
    change (((∐ X).hom u ∈ wedge_star_cover X V hxV (some i)) ∧
        ((∐ X).hom u ∈ wedge_star_cover X V hxV (some j))) ↔
      ((∐ X).hom u ∈ wedge_star_cover X V hxV none)
    constructor
    · intro hu
      exact mem_wedge_star_cover_head X V hxV none u
    · intro hu
      exact ⟨mem_wedge_star_cover_head X V hxV (some i) u,
        mem_wedge_star_cover_head X V hxV (some j) u⟩
  · intro k
    -- On each summand, at least one factor contributes only the chosen neighborhood `V k`.
    by_cases hki : k = i
    · subst k
      ext y
      change (((Sigma.ι X i).right y ∈ wedge_star_cover X V hxV (some i)) ∧
          ((Sigma.ι X i).right y ∈ wedge_star_cover X V hxV (some j))) ↔
        ((Sigma.ι X i).right y ∈ wedge_star_cover X V hxV none)
      constructor
      · intro hy
        exact (mem_wedge_star_cover_none_pullback_iff X V hxV i y).mpr
          ((mem_wedge_star_cover_some_ne_pullback_iff X V hxV hij y).mp hy.2)
      · intro hy
        have hyV : y ∈ V i := (mem_wedge_star_cover_none_pullback_iff X V hxV i y).mp hy
        exact ⟨mem_wedge_star_cover_some_same_pullback_iff X V hxV i y,
          (mem_wedge_star_cover_some_ne_pullback_iff X V hxV hij y).mpr hyV⟩
    · by_cases hkj : k = j
      · subst k
        ext y
        change (((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV (some i)) ∧
            ((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV (some j))) ↔
          ((Sigma.ι X j).right y ∈ wedge_star_cover X V hxV none)
        constructor
        · intro hy
          exact (mem_wedge_star_cover_none_pullback_iff X V hxV j y).mpr
            ((mem_wedge_star_cover_some_ne_pullback_iff X V hxV hij.symm y).mp hy.1)
        · intro hy
          have hyV : y ∈ V j := (mem_wedge_star_cover_none_pullback_iff X V hxV j y).mp hy
          exact ⟨(mem_wedge_star_cover_some_ne_pullback_iff X V hxV hij.symm y).mpr hyV,
            mem_wedge_star_cover_some_same_pullback_iff X V hxV j y⟩
      · ext y
        change (((Sigma.ι X k).right y ∈ wedge_star_cover X V hxV (some i)) ∧
            ((Sigma.ι X k).right y ∈ wedge_star_cover X V hxV (some j))) ↔
          ((Sigma.ι X k).right y ∈ wedge_star_cover X V hxV none)
        constructor
        · intro hy
          exact (mem_wedge_star_cover_none_pullback_iff X V hxV k y).mpr
            ((mem_wedge_star_cover_some_ne_pullback_iff X V hxV hki y).mp hy.1)
        · intro hy
          have hyV : y ∈ V k := (mem_wedge_star_cover_none_pullback_iff X V hxV k y).mp hy
          exact ⟨(mem_wedge_star_cover_some_ne_pullback_iff X V hxV hki y).mpr hyV,
            (mem_wedge_star_cover_some_ne_pullback_iff X V hxV hkj y).mpr hyV⟩

/-- Helper for Proposition 2.8.1: the star cover is closed under nonempty finite intersections
because every binary intersection is again either the common core or one starred summand. -/
private theorem wedge_star_cover_closed_under_nonempty_finite_intersections
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i) :
    TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections (wedge_star_cover X V hxV) := by
  classical
  intro t ht
  -- Induct on the nonempty finite family, collapsing one binary intersection at a time.
  induction t using Finset.induction_on with
  | empty =>
      cases ht.ne_empty rfl
  | @insert a s ha ih =>
      by_cases hs : s.Nonempty
      · obtain ⟨o, ho⟩ := ih hs
        have hinsert :
            (insert a s).inf' ht (wedge_star_cover X V hxV) =
              wedge_star_cover X V hxV a ⊓ s.inf' hs (wedge_star_cover X V hxV) := by
          simpa [ha] using
            (Finset.inf'_insert
              (s := s) (H := hs) (f := wedge_star_cover X V hxV) (b := a))
        cases a with
        | none =>
            refine ⟨none, ?_⟩
            rw [hinsert, ho]
            simpa using wedge_star_cover_inf_none X V hxV o
        | some i =>
            cases o with
            | none =>
                refine ⟨none, ?_⟩
                rw [hinsert, ho]
                simpa [inf_comm] using wedge_star_cover_inf_none X V hxV (some i)
            | some j =>
                by_cases hij : i = j
                · refine ⟨some i, ?_⟩
                  rw [hinsert, ho]
                  simpa [hij] using wedge_star_cover_inf_some_same X V hxV i
                · refine ⟨none, ?_⟩
                  rw [hinsert, ho]
                  simpa using wedge_star_cover_inf_some_ne X V hxV hij
      · have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst hsEmpty
        refine ⟨a, ?_⟩
        simpa using
          (Finset.inf'_singleton (f := wedge_star_cover X V hxV) (b := a))

/-- Helper for Proposition 2.8.1: the `Option ι` star family really covers the whole wedge. -/
private theorem wedge_star_cover_isOpenCover
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i) :
    TopologicalSpace.IsOpenCover (wedge_star_cover X V hxV) := by
  let c :
      Cocone
        (WidePushoutShape.wideSpan
          (⊤_ TopCat)
          (fun i ↦ (X i).right)
          (fun i ↦ (X i).hom)) :=
    WidePushoutShape.mkCocone
      (F := WidePushoutShape.wideSpan
        (⊤_ TopCat)
        (fun i ↦ (X i).right)
        (fun i ↦ (X i).hom))
      ((∐ X).hom)
      (fun i ↦ (Sigma.ι X i).right)
      (fun i ↦ by
        simpa using (Sigma.ι X i).w.symm)
  rw [TopologicalSpace.IsOpenCover]
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep
      (WidePushoutShape.wideSpan (⊤_ TopCat) (fun i ↦ (X i).right) (fun i ↦ (X i).hom))
      (wedge_wide_pushout_is_colimit X) x
    cases j with
    | none =>
        -- A point represented by the terminal leg lands in the common core member `none`.
        have hy : (c.ι.app none) y ∈ wedge_star_cover X V hxV none := by
          have hyTop : y ∈ (⊤ : TopologicalSpace.Opens (⊤_ TopCat)) := by
            trivial
          have hy' : y ∈ (TopologicalSpace.Opens.map (c.ι.app none)).obj
              (wedge_star_cover X V hxV none) := by
            change y ∈ (TopologicalSpace.Opens.map ((∐ X).hom)).obj
              (wedge_star_cover X V hxV none)
            rw [wedge_star_cover_head_pullback X V hxV none]
            simpa using hyTop
          simpa [c] using hy'
        change (c.ι.app none) y ∈ iSup (wedge_star_cover X V hxV)
        exact (TopologicalSpace.Opens.mem_iSup).2 ⟨none, hy⟩
    | some i =>
        -- A point represented in the `i`-th summand lands in the corresponding `some i` member.
        have hy : (c.ι.app (some i)) y ∈ wedge_star_cover X V hxV (some i) := by
          have hyTop : y ∈ (⊤ : TopologicalSpace.Opens (X i).right) := by
            trivial
          have hy' : y ∈ (TopologicalSpace.Opens.map (c.ι.app (some i))).obj
              (wedge_star_cover X V hxV (some i)) := by
            change y ∈ (TopologicalSpace.Opens.map ((Sigma.ι X i).right)).obj
              (wedge_star_cover X V hxV (some i))
            rw [wedge_star_cover_some_same_pullback X V hxV i]
            exact hyTop
          exact hy'
        change (c.ι.app (some i)) y ∈ iSup (wedge_star_cover X V hxV)
        exact (TopologicalSpace.Opens.mem_iSup).2 ⟨some i, hy⟩

/-- Helper for Proposition 2.8.1: every point on the head leg is the wedge basepoint. -/
private theorem wedge_head_eq_basepoint
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (u : ⊤_ TopCat) :
    (∐ X).hom u = underTopBasepoint (∐ X) := by
  -- The terminal object has a unique point, so every head-leg representative is the basepoint.
  have hu : u = TopCat.terminalIsoPUnit.inv PUnit.unit := by
    have hunit : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
      cases TopCat.terminalIsoPUnit.hom u
      rfl
    have := congrArg (TopCat.terminalIsoPUnit.inv : PUnit → ⊤_ TopCat) hunit
    simpa using this
  simpa [underTopBasepoint, hu]

/-- Helper for Proposition 2.8.1: the wedge basepoint belongs to every star-cover member. -/
private theorem wedge_star_cover_basepoint_mem
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (o : Option ι) :
    underTopBasepoint (∐ X) ∈ wedge_star_cover X V hxV o := by
  -- This is the pointwise form of the already-established head pullback formula.
  simpa [underTopBasepoint] using
    mem_wedge_star_cover_head X V hxV o (TopCat.terminalIsoPUnit.inv PUnit.unit)

/-- Helper for Proposition 2.8.1: evaluating the structure map of a based space at the unique
point of the terminal object recovers its distinguished basepoint. -/
private theorem under_hom_eq_basepoint
    (Y : Under (⊤_ TopCat))
    (u : ⊤_ TopCat) :
    Y.hom u = underTopBasepoint Y := by
  have hu : u = TopCat.terminalIsoPUnit.inv PUnit.unit := by
    have hunit : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
      cases TopCat.terminalIsoPUnit.hom u
      rfl
    simpa using congrArg (TopCat.terminalIsoPUnit.inv : PUnit → ⊤_ TopCat) hunit
  simpa [underTopBasepoint, hu]

/-- Helper for Proposition 2.8.1: the wedge basepoint viewed as a point of any star member. -/
private noncomputable def wedge_star_cover_basepoint
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (o : Option ι) :
    wedge_star_cover X V hxV o :=
  ⟨underTopBasepoint (∐ X), wedge_star_cover_basepoint_mem X V hxV o⟩

/-- Helper for Proposition 2.8.1: the `j`-th contractible neighborhood maps into the common-core
star member. -/
private noncomputable def wedge_star_cover_none_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (j : ι) :
    C(V j, wedge_star_cover X V hxV none) :=
  ⟨fun z ↦
      ⟨(Sigma.ι X j).right z,
        (mem_wedge_star_cover_none_pullback_iff X V hxV j z).mpr z.2⟩,
    (((Sigma.ι X j).right).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Helper for Proposition 2.8.1: the common-core branch inclusion sends the distinguished
basepoint of `X j` to the wedge basepoint of the common core. -/
private theorem wedge_star_cover_none_leg_basepoint
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (j : ι) :
    wedge_star_cover_none_leg X V hxV j ⟨underTopBasepoint (X j), hxV j⟩ =
      wedge_star_cover_basepoint X V hxV none := by
  -- Both subtype points have ambient image equal to the wedge basepoint.
  apply Subtype.ext
  exact fundamentalGroupFunctorMap_basepoint (Sigma.ι X j)

/-- Helper for Proposition 2.8.1: the distinguished summand maps into its own star member. -/
private noncomputable def wedge_star_cover_some_same_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (i : ι) :
    C((X i).right, wedge_star_cover X V hxV (some i)) :=
  ⟨fun y ↦
      ⟨(Sigma.ι X i).right y,
        mem_wedge_star_cover_some_same_pullback_iff X V hxV i y⟩,
    (((Sigma.ι X i).right).hom.continuous).subtype_mk _⟩

/-- Helper for Proposition 2.8.1: the distinguished branch inclusion also sends the chosen
basepoint to the wedge basepoint of the `some i` star member. -/
private theorem wedge_star_cover_some_same_leg_basepoint
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (i : ι) :
    wedge_star_cover_some_same_leg X V hxV i (underTopBasepoint (X i)) =
      wedge_star_cover_basepoint X V hxV (some i) := by
  -- On the distinguished branch, the basepoint is glued in unchanged.
  apply Subtype.ext
  exact fundamentalGroupFunctorMap_basepoint (Sigma.ι X i)

/-- Helper for Proposition 2.8.1: an off-center contractible neighborhood maps into the
corresponding starred member. -/
private noncomputable def wedge_star_cover_some_ne_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    {i j : ι} (hji : j ≠ i) :
    C(V j, wedge_star_cover X V hxV (some i)) :=
  ⟨fun z ↦
      ⟨(Sigma.ι X j).right z,
        (mem_wedge_star_cover_some_ne_pullback_iff X V hxV hji z).mpr z.2⟩,
    (((Sigma.ι X j).right).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Helper for Proposition 2.8.1: the off-center branch inclusion also sends its distinguished
basepoint to the wedge basepoint of the centered star member. -/
private theorem wedge_star_cover_some_ne_leg_basepoint
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    {i j : ι} (hji : j ≠ i) :
    wedge_star_cover_some_ne_leg X V hxV hji ⟨underTopBasepoint (X j), hxV j⟩ =
      wedge_star_cover_basepoint X V hxV (some i) := by
  -- Off the center, the chosen neighborhood still meets the star member at the glued basepoint.
  apply Subtype.ext
  exact fundamentalGroupFunctorMap_basepoint (Sigma.ι X j)

/-- Helper for Proposition 2.8.1: the common core sits inside every starred member as an open
subspace. -/
private theorem wedge_star_cover_none_le_some
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (i : ι) :
    wedge_star_cover X V hxV none ≤ wedge_star_cover X V hxV (some i) := by
  -- The already-proved binary intersection formula says exactly that the common core is contained
  -- in every starred member.
  exact inf_eq_left.mp (wedge_star_cover_inf_none X V hxV (some i))

/-- Helper for Proposition 2.8.1: the inclusion of the common core into the `i`-th starred member
as a continuous map of open subspaces. -/
private noncomputable def wedge_star_cover_none_to_some
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (i : ι) :
    C(wedge_star_cover X V hxV none, wedge_star_cover X V hxV (some i)) :=
  ⟨fun z ↦ ⟨z.1, wedge_star_cover_none_le_some X V hxV i z.2⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Helper for Proposition 2.8.1: the contractible neighborhood `V i` includes into the full
distinguished summand `X i`. -/
private noncomputable def wedge_star_cover_same_neighborhood_inclusion
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (i : ι) :
    C(V i, (X i).right) :=
  ⟨fun z ↦ z.1, continuous_subtype_val⟩

/-- Helper for Proposition 2.8.1: on the distinguished summand, the common-core inclusion into
the `i`-th star agrees with the neighborhood inclusion followed by the distinguished summand leg. -/
private theorem wedge_star_cover_none_to_some_comp_same_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (i : ι) :
    (wedge_star_cover_none_to_some X V hxV i).comp (wedge_star_cover_none_leg X V hxV i) =
      (wedge_star_cover_some_same_leg X V hxV i).comp
        (wedge_star_cover_same_neighborhood_inclusion X V i) := by
  -- Both composites are the same subtype-valued map on `V i`.
  ext z
  rfl

/-- Helper for Proposition 2.8.1: away from the distinguished summand, the common-core inclusion
into the `i`-th star is literally the off-center neighborhood leg. -/
private theorem wedge_star_cover_none_to_some_comp_ne_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    {i j : ι} (hji : j ≠ i) :
    (wedge_star_cover_none_to_some X V hxV i).comp (wedge_star_cover_none_leg X V hxV j) =
      wedge_star_cover_some_ne_leg X V hxV hji := by
  -- Off the center, both maps are the identical inclusion of `V j` into the `i`-th star member.
  ext z
  rfl

/-- Helper for Proposition 2.8.1: every point of a star member can be joined to the wedge
basepoint inside that same member. -/
private theorem wedge_star_cover_joined_to_basepoint
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    [∀ i, PathConnectedSpace (X i).right]
    (hVpath : ∀ i, PathConnectedSpace (V i))
    (o : Option ι)
    (x : wedge_star_cover X V hxV o) :
    Joined x (wedge_star_cover_basepoint X V hxV o) := by
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep
    (WidePushoutShape.wideSpan (⊤_ TopCat) (fun i ↦ (X i).right) (fun i ↦ (X i).hom))
    (wedge_wide_pushout_is_colimit X) x.1
  cases j with
  | none =>
      -- A head-leg representative is already the wedge basepoint.
      have hxeq : x = wedge_star_cover_basepoint X V hxV o := by
        ext
        exact hy.symm.trans (wedge_head_eq_basepoint X y)
      simpa [hxeq] using Joined.refl (wedge_star_cover_basepoint X V hxV o)
  | some j =>
      cases o with
      | none =>
          -- In the common core, every representative lies in some contractible neighborhood `V j`.
          have hy_mem : ((Sigma.ι X j).right y) ∈ wedge_star_cover X V hxV none := by
            exact hy ▸ x.2
          have hyV : y ∈ V j :=
            (mem_wedge_star_cover_none_pullback_iff X V hxV j y).mp hy_mem
          let _ : PathConnectedSpace (V j) := hVpath j
          let γ :
              Path (⟨y, hyV⟩ : V j) ⟨underTopBasepoint (X j), hxV j⟩ :=
            PathConnectedSpace.somePath _ _
          have hstart :
              x = wedge_star_cover_none_leg X V hxV j ⟨y, hyV⟩ := by
            ext
            simpa [wedge_star_cover_none_leg] using hy.symm
          have hend :
              wedge_star_cover_basepoint X V hxV none =
                wedge_star_cover_none_leg X V hxV j ⟨underTopBasepoint (X j), hxV j⟩ := by
            ext
            simpa [wedge_star_cover_basepoint, wedge_star_cover_none_leg] using
              (fundamentalGroupFunctorMap_basepoint (Sigma.ι X j)).symm
          -- Mapping the neighborhood path into the wedge stays inside the common core.
          exact ⟨(γ.map (wedge_star_cover_none_leg X V hxV j).continuous).cast hstart hend⟩
      | some i =>
          by_cases hji : j = i
          · subst j
            -- On the distinguished summand, use the ambient path-connectedness of `X i`.
            change (X i).right at y
            let γ : Path y (underTopBasepoint (X i)) := PathConnectedSpace.somePath _ _
            have hstart :
                x = wedge_star_cover_some_same_leg X V hxV i y := by
              ext
              simpa [wedge_star_cover_some_same_leg] using hy.symm
            have hend :
                wedge_star_cover_basepoint X V hxV (some i) =
                  wedge_star_cover_some_same_leg X V hxV i (underTopBasepoint (X i)) := by
              ext
              simpa [wedge_star_cover_basepoint, wedge_star_cover_some_same_leg] using
                (fundamentalGroupFunctorMap_basepoint (Sigma.ι X i)).symm
            exact ⟨(γ.map (wedge_star_cover_some_same_leg X V hxV i).continuous).cast
              hstart hend⟩
          · -- Off the distinguished summand, the point lies in the chosen contractible neighborhood.
            have hy_mem : ((Sigma.ι X j).right y) ∈ wedge_star_cover X V hxV (some i) := by
              exact hy ▸ x.2
            have hyV : y ∈ V j :=
              (mem_wedge_star_cover_some_ne_pullback_iff X V hxV hji y).mp hy_mem
            let _ : PathConnectedSpace (V j) := hVpath j
            let γ :
                Path (⟨y, hyV⟩ : V j) ⟨underTopBasepoint (X j), hxV j⟩ :=
              PathConnectedSpace.somePath _ _
            have hstart :
                x = wedge_star_cover_some_ne_leg X V hxV hji ⟨y, hyV⟩ := by
              ext
              simpa [wedge_star_cover_some_ne_leg] using hy.symm
            have hend :
                wedge_star_cover_basepoint X V hxV (some i) =
                  wedge_star_cover_some_ne_leg X V hxV hji ⟨underTopBasepoint (X j), hxV j⟩ := by
              ext
              simpa [wedge_star_cover_basepoint, wedge_star_cover_some_ne_leg] using
                (fundamentalGroupFunctorMap_basepoint (Sigma.ι X j)).symm
            exact ⟨(γ.map (wedge_star_cover_some_ne_leg X V hxV hji).continuous).cast
              hstart hend⟩

/-- Helper for Proposition 2.8.1: every star member is path connected, because any of its points
can be joined to the wedge basepoint within that member. -/
private theorem wedge_star_cover_path_connected
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    [∀ i, PathConnectedSpace (X i).right]
    (hVpath : ∀ i, PathConnectedSpace (V i))
    (o : Option ι) :
    PathConnectedSpace (wedge_star_cover X V hxV o) := by
  refine ⟨⟨wedge_star_cover_basepoint X V hxV o⟩, ?_⟩
  intro x y
  -- Join both points to the common wedge basepoint and concatenate the two paths.
  exact (wedge_star_cover_joined_to_basepoint X V hxV hVpath o x).trans
    (wedge_star_cover_joined_to_basepoint X V hxV hVpath o y).symm

/-- Helper for Proposition 2.8.1: if an open subset `W` of the wedge pulls back to `⊤` along the
head leg, then the wedge basepoint belongs to `W`. -/
private theorem open_subtype_wide_pushout_basepoint_mem
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤) :
    underTopBasepoint (∐ X) ∈ W := by
  -- The terminal pullback formula says exactly that every point on the head leg lands in `W`.
  change
    TopCat.terminalIsoPUnit.inv PUnit.unit ∈
      (TopologicalSpace.Opens.map ((∐ X).hom)).obj W
  rw [hhead]
  trivial

/-- Helper for Proposition 2.8.1: every branch open `U j` contains the distinguished basepoint of
its summand once the ambient open subset `W` contains the wedge basepoint. -/
private theorem open_subtype_wide_pushout_branch_basepoint_mem
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (j : ι) :
    underTopBasepoint (X j) ∈ U j := by
  -- Move the ambient basepoint membership across the `j`-th summand pullback formula.
  have hW : underTopBasepoint (∐ X) ∈ W :=
    open_subtype_wide_pushout_basepoint_mem X W hhead
  have hpull : ((Sigma.ι X j).right (underTopBasepoint (X j))) ∈ W := by
    have hbase :
        (Sigma.ι X j).right (underTopBasepoint (X j)) = underTopBasepoint (∐ X) := by
      simpa using fundamentalGroupFunctorMap_basepoint (Sigma.ι X j)
    exact hbase ▸ hW
  change underTopBasepoint (X j) ∈ (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W at hpull
  rw [hsummand j] at hpull
  exact hpull

/-- Helper for Proposition 2.8.1: every point of an open subtype of the wedge is represented
either by the head leg or by one of the prescribed branch pullbacks. -/
private theorem open_subtype_wide_pushout_exists_rep
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (x : W) :
    (∃ u : ⊤_ TopCat, ((∐ X).hom u) = x.1) ∨
      ∃ j, ∃ y : U j, ((Sigma.ι X j).right y) = x.1 := by
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep
    (WidePushoutShape.wideSpan
      (⊤_ TopCat)
      (fun j ↦ (X j).right)
      (fun j ↦ (X j).hom))
    (wedge_wide_pushout_is_colimit X)
    x.1
  cases j with
  | none =>
      -- A head representative already gives the required `none`-branch witness.
      exact Or.inl ⟨y, hy⟩
  | some i =>
      have hyW : ((Sigma.ι X i).right y) ∈ W := by
        exact hy ▸ x.2
      have hyU : y ∈ U i := by
        change y ∈ (TopologicalSpace.Opens.map ((Sigma.ι X i).right)).obj W at hyW
        rw [hsummand i] at hyW
        exact hyW
      -- A summand representative that lies in `W` automatically lands in the prescribed pullback
      -- open `U i`.
      exact Or.inr ⟨i, ⟨y, hyU⟩, hy⟩

/-- Helper for Proposition 2.8.1: every point of the terminal space is the chosen terminal
point. -/
private theorem terminal_eq_terminal_point
    (u : ⊤_ TopCat) :
    u = TopCat.terminalIsoPUnit.inv PUnit.unit := by
  have hunit : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
    cases TopCat.terminalIsoPUnit.hom u
    rfl
  have := congrArg (TopCat.terminalIsoPUnit.inv : PUnit → ⊤_ TopCat) hunit
  simpa using this

/-- Helper for Proposition 2.8.1: the subtype wide-pushout uses the wedge basepoint as its head
vertex. -/
private noncomputable def open_subtype_wide_pushout_basepoint
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤) :
    W :=
  ⟨underTopBasepoint (∐ X), open_subtype_wide_pushout_basepoint_mem X W hhead⟩

/-- Helper for Proposition 2.8.1: every prescribed branch point of the subtype diagram really
lands in the ambient open subset `W`. -/
private theorem open_subtype_wide_pushout_branch_image_mem
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (j : ι) (y : U j) :
    (Sigma.ι X j).right y ∈ W := by
  -- The `j`-th branch inclusion into `W` is exactly the prescribed pullback formula.
  change y.1 ∈ (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W
  rw [hsummand j]
  exact y.2

/-- Helper for Proposition 2.8.1: the subtype wide-pushout diagram remembers the chosen
basepoint in each prescribed pullback `U j`. -/
private noncomputable def open_subtype_wide_pushout_branch_basepoint_map
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (j : ι) :
    (⊤_ TopCat) ⟶ TopCat.of (U j) :=
  TopCat.ofHom
    (ContinuousMap.const _ ⟨underTopBasepoint (X j),
      open_subtype_wide_pushout_branch_basepoint_mem X W U hhead hsummand j⟩)

/-- Helper for Proposition 2.8.1: the subtype wide-pushout diagram has one branch for each
prescribed pullback `U j`. -/
private noncomputable def open_subtype_wide_pushout_diagram
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j) :
    WidePushoutShape ι ⥤ TopCat :=
  WidePushoutShape.wideSpan
    (⊤_ TopCat)
    (fun j ↦ TopCat.of (U j))
    (open_subtype_wide_pushout_branch_basepoint_map X W U hhead hsummand)

/-- Helper for Proposition 2.8.1: the canonical head leg of the subtype wide-pushout cocone picks
out the wedge basepoint inside `W`. -/
private noncomputable def open_subtype_wide_pushout_head_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤) :
    (⊤_ TopCat) ⟶ TopCat.of W :=
  TopCat.ofHom (ContinuousMap.const _ (open_subtype_wide_pushout_basepoint X W hhead))

/-- Helper for Proposition 2.8.1: each prescribed branch `U j` includes into the ambient open
subtype `W`. -/
private noncomputable def open_subtype_wide_pushout_branch_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (j : ι) :
    TopCat.of (U j) ⟶ TopCat.of W :=
  TopCat.ofHom
    ⟨fun y ↦
        ⟨(Sigma.ι X j).right y,
          open_subtype_wide_pushout_branch_image_mem X W U hsummand j y⟩,
      (((Sigma.ι X j).right).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Helper for Proposition 2.8.1: the canonical subtype legs satisfy the wide-pushout cocone
compatibility relation. -/
private theorem open_subtype_wide_pushout_cocone_comm
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (j : ι) :
    (open_subtype_wide_pushout_diagram X W U hhead hsummand).map
        (WidePushoutShape.Hom.init j) ≫
      open_subtype_wide_pushout_branch_leg X W U hsummand j =
        open_subtype_wide_pushout_head_leg X W hhead := by
  ext u
  -- The two subtype points have the same ambient image, namely the wedge basepoint.
  have hu : u = TopCat.terminalIsoPUnit.inv PUnit.unit :=
    terminal_eq_terminal_point u
  subst hu
  change (Sigma.ι X j).right (underTopBasepoint (X j)) = underTopBasepoint (∐ X)
  exact fundamentalGroupFunctorMap_basepoint (Sigma.ι X j)

/-- Helper for Proposition 2.8.1: the prescribed pullbacks and the wedge basepoint assemble into
the canonical subtype wide-pushout cocone with point `W`. -/
private noncomputable def open_subtype_wide_pushout_cocone
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j) :
    Cocone (open_subtype_wide_pushout_diagram X W U hhead hsummand) :=
  WidePushoutShape.mkCocone
    (open_subtype_wide_pushout_head_leg X W hhead)
    (open_subtype_wide_pushout_branch_leg X W U hsummand)
    (open_subtype_wide_pushout_cocone_comm X W U hhead hsummand)

/-- Helper for Proposition 2.8.1: a cocone on the subtype wide-pushout diagram extends to the
ambient wedge diagram once the target is given the discrete topology. -/
private noncomputable def open_subtype_wide_pushout_extension_head
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (s : Cocone ((open_subtype_wide_pushout_diagram X W U hhead hsummand) ⋙ forget TopCat)) :
    (⊤_ TopCat) → s.pt :=
  s.ι.app none

/-- Helper for Proposition 2.8.1: each branch of a subtype cocone extends to the ambient summand
by using the head value outside the prescribed pullback `U j`. -/
private noncomputable def open_subtype_wide_pushout_extension_branch
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (s : Cocone ((open_subtype_wide_pushout_diagram X W U hhead hsummand) ⋙ forget TopCat))
    (j : ι) :
    (X j).right → s.pt :=
  letI : DecidablePred fun x : (X j).right ↦ x ∈ U j := Classical.decPred _
  fun x ↦
    if hx : x ∈ U j then
      s.ι.app (some j) ⟨x, hx⟩
    else
      s.ι.app none (TopCat.terminalIsoPUnit.inv PUnit.unit)

/-- Helper for Proposition 2.8.1: the discrete ambient extension preserves the wide-pushout cocone
compatibility at each branch basepoint. -/
private theorem open_subtype_wide_pushout_extension_comm
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (s : Cocone ((open_subtype_wide_pushout_diagram X W U hhead hsummand) ⋙ forget TopCat))
    (j : ι) :
    (open_subtype_wide_pushout_extension_branch X W U hhead hsummand s j) ∘ (X j).hom =
      open_subtype_wide_pushout_extension_head X W U hhead hsummand s := by
  funext u
  -- On the common basepoint, the subtype cocone relation identifies the branch value with the
  -- head value.
  have hu : u = TopCat.terminalIsoPUnit.inv PUnit.unit :=
    terminal_eq_terminal_point u
  subst hu
  have hbase : underTopBasepoint (X j) ∈ U j :=
    open_subtype_wide_pushout_branch_basepoint_mem X W U hhead hsummand j
  have hfac :=
    congrArg (fun k ↦ k.hom (TopCat.terminalIsoPUnit.inv PUnit.unit))
      (s.w (WidePushoutShape.Hom.init j))
  have hbranch :
      open_subtype_wide_pushout_extension_branch X W U hhead hsummand s j
          (underTopBasepoint (X j)) =
        s.ι.app (some j) ⟨underTopBasepoint (X j), hbase⟩ := by
    classical
    simp [open_subtype_wide_pushout_extension_branch, hbase]
  change open_subtype_wide_pushout_extension_branch X W U hhead hsummand s j
      ((X j).hom (TopCat.terminalIsoPUnit.inv PUnit.unit)) =
    open_subtype_wide_pushout_extension_head X W U hhead hsummand s
      (TopCat.terminalIsoPUnit.inv PUnit.unit)
  rw [show (X j).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) = underTopBasepoint (X j) by rfl]
  rw [hbranch]
  simpa [open_subtype_wide_pushout_diagram, open_subtype_wide_pushout_branch_basepoint_map,
    open_subtype_wide_pushout_extension_head, underTopBasepoint] using hfac

/-- Helper for Proposition 2.8.1: a cocone on the subtype wide-pushout diagram extends to a
discrete-target cocone on the ambient wedge diagram. -/
private noncomputable def open_subtype_wide_pushout_extension_cocone
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (s : Cocone ((open_subtype_wide_pushout_diagram X W U hhead hsummand) ⋙ forget TopCat)) :
    Cocone
      ((WidePushoutShape.wideSpan
        (⊤_ TopCat)
        (fun j ↦ (X j).right)
        (fun j ↦ (X j).hom)) ⋙ forget TopCat) :=
  WidePushoutShape.mkCocone
    (TypeCat.ofHom (open_subtype_wide_pushout_extension_head X W U hhead hsummand s))
    (fun j ↦ TypeCat.ofHom
      (open_subtype_wide_pushout_extension_branch X W U hhead hsummand s j))
    (fun j ↦ by
      ext u
      exact congrFun (open_subtype_wide_pushout_extension_comm X W U hhead hsummand s j) u)

/-- Helper for Proposition 2.8.1: a map out of `W` is determined by its value at the wedge
basepoint and on each prescribed branch inclusion `U j ⟶ W`. -/
private theorem open_subtype_wide_pushout_hom_ext
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    {Y : Type*} (f g : W → Y)
    (hbase :
      f (open_subtype_wide_pushout_basepoint X W hhead) =
        g (open_subtype_wide_pushout_basepoint X W hhead))
    (hbranch :
      ∀ j (y : U j),
        f ((open_subtype_wide_pushout_branch_leg X W U hsummand j) y) =
          g ((open_subtype_wide_pushout_branch_leg X W U hsummand j) y)) :
    f = g := by
  funext x
  -- Analyze `x` by an ambient wedge representative and reduce to the stated head/branch data.
  rcases open_subtype_wide_pushout_exists_rep X W U hsummand x with hheadRep | hsummandRep
  · rcases hheadRep with ⟨u, hu⟩
    have hx :
        x = open_subtype_wide_pushout_basepoint X W hhead := by
      apply Subtype.ext
      exact hu.symm.trans (wedge_head_eq_basepoint X u)
    simpa [hx] using hbase
  · rcases hsummandRep with ⟨j, y, hy⟩
    have hx :
        x = (open_subtype_wide_pushout_branch_leg X W U hsummand j) y := by
      apply Subtype.ext
      simpa [open_subtype_wide_pushout_branch_leg] using hy.symm
    simpa [hx] using hbranch j y

/-- Helper for Proposition 2.8.1: the canonical cocone on an open subtype `W` with prescribed
head and branch pullbacks is a colimit after forgetting the topology. -/
private noncomputable def open_subtype_wide_pushout_is_colimit_type
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j) :
    IsColimit ((forget TopCat).mapCocone
      (open_subtype_wide_pushout_cocone X W U hhead hsummand)) := by
  refine IsColimit.ofExistsUnique fun s ↦ ?_
  let hambient := isColimitOfPreserves (forget TopCat) (wedge_wide_pushout_is_colimit X)
  let sExt := open_subtype_wide_pushout_extension_cocone X W U hhead hsummand s
  let Φ : (∐ X).right → s.pt := (hambient.desc sExt).hom
  let desc : W → s.pt := fun x ↦ Φ x.1
  have hdescFac :
      ∀ j,
        ((forget TopCat).mapCocone
          (open_subtype_wide_pushout_cocone X W U hhead hsummand)).ι.app j ≫ TypeCat.ofHom desc =
            s.ι.app j := by
    intro j
    cases j with
    | none =>
        ext u
        -- The head leg is the ambient wedge basepoint, so the ambient descended map can be read
        -- off from the head face of the extension cocone.
        have hfac :=
          congrArg (fun f ↦ f.hom u) (hambient.fac sExt none)
        have hΦ :
            Φ (underTopBasepoint (∐ X)) = Φ ((∐ X).hom u) := by
          exact congrArg Φ (wedge_head_eq_basepoint X u).symm
        simpa [desc, open_subtype_wide_pushout_cocone, open_subtype_wide_pushout_head_leg,
          open_subtype_wide_pushout_basepoint, hambient, sExt,
          open_subtype_wide_pushout_extension_cocone,
          open_subtype_wide_pushout_extension_head] using hΦ.trans hfac
    | some j =>
        ext y
        -- On a branch point `y : U j`, the discrete extension agrees with the original branch leg.
        have hfac :=
          congrArg (fun f ↦ f.hom y.1) (hambient.fac sExt (some j))
        change
          Φ ((Sigma.ι X j).right y.1) =
            open_subtype_wide_pushout_extension_branch X W U hhead hsummand s j y.1 at hfac
        change Φ ((Sigma.ι X j).right y.1) = s.ι.app (some j) y
        simpa [Φ, hambient, sExt, open_subtype_wide_pushout_extension_cocone,
          open_subtype_wide_pushout_extension_branch, y.2] using hfac
  refine ⟨TypeCat.ofHom desc, hdescFac, ?_⟩
  intro m hm
  -- Uniqueness is now the map-ext principle for functions out of `W`.
  apply ConcreteCategory.hom_ext
  intro x
  apply congrFun
  apply open_subtype_wide_pushout_hom_ext X W U hhead hsummand m.hom desc
  · have hmBase := congrArg (fun f ↦ f.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)) (hm none)
    have hdescBase := congrArg (fun f ↦ f.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)) (hdescFac none)
    exact hmBase.trans hdescBase.symm
  · intro j y
    have hmBranch := congrArg (fun f ↦ f.hom y) (hm (some j))
    have hdescBranch := congrArg (fun f ↦ f.hom y) (hdescFac (some j))
    exact hmBranch.trans hdescBranch.symm

/-- Helper for Proposition 2.8.1: an open subset of the subtype `W` is open exactly when its
pullbacks along the subtype head leg and subtype branch legs are open. -/
private theorem open_subtype_wide_pushout_isOpen_iff
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (A : Set W) :
    IsOpen A ↔
      ∀ j, IsOpen (((open_subtype_wide_pushout_cocone X W U hhead hsummand).ι.app j) ⁻¹' A) := by
  let cambient :
      Cocone
        (WidePushoutShape.wideSpan
          (⊤_ TopCat)
          (fun j ↦ (X j).right)
          (fun j ↦ (X j).hom)) :=
    WidePushoutShape.mkCocone
      (F := WidePushoutShape.wideSpan
        (⊤_ TopCat)
        (fun j ↦ (X j).right)
        (fun j ↦ (X j).hom))
      ((∐ X).hom)
      (fun j ↦ (Sigma.ι X j).right)
      (fun j ↦ by
        simpa using (Sigma.ι X j).w.symm)
  let csub := open_subtype_wide_pushout_cocone X W U hhead hsummand
  constructor
  · intro hA
    -- Open sets pull back to open sets along each subtype cocone leg.
    intro j
    exact hA.preimage (csub.ι.app j).hom.continuous
  · intro hA
    -- Route correction: the ambient wide-pushout colimit now supplies the openness of the
    -- underlying image `Subtype.val '' A`, which then recovers openness in the subtype.
    rw [isOpen_induced_iff]
    refine ⟨Subtype.val '' A, ?_, ?_⟩
    · -- Check openness on the ambient wedge by reducing each preimage to the corresponding subtype
      -- preimage.
      refine (TopCat.isOpen_iff_of_isColimit cambient (wedge_wide_pushout_is_colimit X)
        (Subtype.val '' A)).2 ?_
      intro j
      cases j with
      | none =>
          have hpre :
              ((∐ X).hom) ⁻¹' (Subtype.val '' A) =
                (open_subtype_wide_pushout_head_leg X W hhead) ⁻¹' A := by
            ext u
            constructor
            · rintro ⟨a, ha, hau⟩
              have haeq : a = (open_subtype_wide_pushout_head_leg X W hhead) u :=
                Subtype.ext (hau.trans (wedge_head_eq_basepoint X u))
              simpa [haeq] using ha
            · intro hu
              refine ⟨(open_subtype_wide_pushout_head_leg X W hhead) u, hu, ?_⟩
              exact (wedge_head_eq_basepoint X u).symm
          have hheadOpen :
              IsOpen (((open_subtype_wide_pushout_head_leg X W hhead)) ⁻¹' A) := by
            by_cases hmem : open_subtype_wide_pushout_basepoint X W hhead ∈ A
            · have hpreuniv :
                  ((open_subtype_wide_pushout_head_leg X W hhead)) ⁻¹' A = Set.univ := by
                ext u
                constructor
                · intro _
                  trivial
                · intro _
                  simpa [open_subtype_wide_pushout_head_leg] using hmem
              rw [hpreuniv]
              exact isOpen_univ
            · have hprempty :
                  ((open_subtype_wide_pushout_head_leg X W hhead)) ⁻¹' A = ∅ := by
                ext u
                constructor
                · intro hu
                  exact (hmem (by simpa [open_subtype_wide_pushout_head_leg] using hu)).elim
                · intro hu
                  cases hu
              rw [hprempty]
              exact isOpen_empty
          change IsOpen (((∐ X).hom) ⁻¹' (Subtype.val '' A))
          rw [hpre]
          exact hheadOpen
      | some j =>
          have hpre :
              Subtype.val ''
                  (((open_subtype_wide_pushout_branch_leg X W U hsummand j) ⁻¹' A) : Set (U j)) =
                ((Sigma.ι X j).right) ⁻¹' (Subtype.val '' A) := by
            ext y
            constructor
            · rintro ⟨z, hz, rfl⟩
              exact ⟨(open_subtype_wide_pushout_branch_leg X W U hsummand j) z, hz, rfl⟩
            · rintro ⟨a, ha, hay⟩
              have hyU : y ∈ U j := by
                rw [← hsummand j]
                change (Sigma.ι X j).right y ∈ W
                simpa [hay] using a.2
              have haeq : a = (open_subtype_wide_pushout_branch_leg X W U hsummand j) ⟨y, hyU⟩ := by
                apply Subtype.ext
                exact hay
              refine ⟨⟨y, hyU⟩, ?_, rfl⟩
              simpa [haeq] using ha
          have hbranchOpen :
              IsOpen (((open_subtype_wide_pushout_branch_leg X W U hsummand j) ⁻¹' A) :
                Set (U j)) := by
            simpa [csub, open_subtype_wide_pushout_cocone] using hA (some j)
          have himageOpen :
              IsOpen
                (Subtype.val ''
                  (((open_subtype_wide_pushout_branch_leg X W U hsummand j) ⁻¹' A) :
                    Set (U j))) :=
            (U j).isOpen.isOpenMap_subtype_val _ hbranchOpen
          simpa [cambient, hpre] using himageOpen
    · -- The subtype projection is injective, so pulling back the image recovers the original set.
      ext x
      constructor
      · rintro ⟨a, ha, hax⟩
        have : a = x := Subtype.ext hax
        simpa [this] using ha
      · intro hx
        exact ⟨x, hx, rfl⟩

/-- Helper for Proposition 2.8.1: the topology on an open subtype `W` is the supremum of the
coinduced topologies from its canonical wide-pushout legs. -/
private theorem open_subtype_wide_pushout_coinduced_eq
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j) :
    (TopCat.of W).str =
      ⨆ j,
        ((open_subtype_wide_pushout_diagram X W U hhead hsummand).obj j).str.coinduced
          ((open_subtype_wide_pushout_cocone X W U hhead hsummand).ι.app j) := by
  ext A
  -- Extensionality on open sets reduces the equality to the subtype pullback criterion above.
  rw [open_subtype_wide_pushout_isOpen_iff X W U hhead hsummand A]
  constructor <;> intro h <;> simpa only [isOpen_iSup_iff, isOpen_coinduced] using h

/-- Helper for Proposition 2.8.1: the canonical subtype cocone is a genuine colimit in `TopCat`
once the underlying-Type colimit is upgraded by the recovered subtype topology. -/
private noncomputable def open_subtype_wide_pushout_is_colimit
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j) :
    IsColimit (open_subtype_wide_pushout_cocone X W U hhead hsummand) := by
  -- The forgotten cocone is already colimiting on underlying types, and the previous theorem
  -- supplies exactly the coinduced-topology equality required by `TopCat`.
  exact Nonempty.some <|
    (TopCat.nonempty_isColimit_iff_eq_coinduced
      (open_subtype_wide_pushout_cocone X W U hhead hsummand)
    (open_subtype_wide_pushout_is_colimit_type X W U hhead hsummand)).2
      (open_subtype_wide_pushout_coinduced_eq X W U hhead hsummand)

/-- Helper for Proposition 2.8.1: a singleton-relative homotopy can be viewed as a map into the
path space by swapping the interval and source coordinates and then currying. -/
private noncomputable def homotopyRel_pathspace_map
    {A : Type*} [TopologicalSpace A]
    {Y : Type*} [TopologicalSpace Y]
    {f₀ f₁ : C(A, Y)} {S : Set A}
    (H : f₀.HomotopyRel f₁ S) :
    C(A, C(I, Y)) :=
  ContinuousMap.curry
    (H.toHomotopy.toContinuousMap.comp
      ⟨Homeomorph.prodComm A I, (Homeomorph.prodComm A I).continuous_toFun⟩)

/-- Helper for Proposition 2.8.1: evaluating the path-space map recovers the original homotopy at
the chosen time and point. -/
private theorem homotopyRel_pathspace_map_apply
    {A : Type*} [TopologicalSpace A]
    {Y : Type*} [TopologicalSpace Y]
    {f₀ f₁ : C(A, Y)} {S : Set A}
    (H : f₀.HomotopyRel f₁ S) (a : A) (t : I) :
    homotopyRel_pathspace_map H a t = H (t, a) := by
  rfl

/-- Helper for Proposition 2.8.1: at a fixed singleton point, the path-space map of a
singleton-relative homotopy is the constant path at the preserved value. -/
private theorem homotopyRel_pathspace_map_eq_const
    {A : Type*} [TopologicalSpace A]
    {Y : Type*} [TopologicalSpace Y]
    {f₀ f₁ : C(A, Y)} {a₀ : A} {y₀ : Y}
    (H : f₀.HomotopyRel f₁ ({a₀} : Set A))
    (hf₀ : f₀ a₀ = y₀) :
    homotopyRel_pathspace_map H a₀ = ContinuousMap.const I y₀ := by
  -- The relative condition forces the entire track at `a₀` to stay at `y₀`.
  ext t : 1
  simpa [homotopyRel_pathspace_map_apply, hf₀] using
    H.eq_fst t (by simp : a₀ ∈ ({a₀} : Set A))

/-- Helper for Proposition 2.8.1: a continuous family of paths with the right endpoint data
packages into a singleton-relative homotopy. -/
private noncomputable def pathspace_map_homotopy_rel
    {A : Type*} [TopologicalSpace A]
    {Y : Type*} [TopologicalSpace Y]
    (d : C(A, C(I, Y)))
    (f₀ f₁ : C(A, Y))
    (hd₀ : ∀ a, d a 0 = f₀ a)
    (hd₁ : ∀ a, d a 1 = f₁ a)
    (a₀ : A) (y₀ : Y)
    (hf₀ : f₀ a₀ = y₀)
    (hdconst : d a₀ = ContinuousMap.const I y₀) :
    f₀.HomotopyRel f₁ ({a₀} : Set A) := by
  refine
    { toHomotopy := ?_, prop' := ?_ }
  · refine
      { toContinuousMap := (ContinuousMap.uncurry d).comp
          ⟨Homeomorph.prodComm I A, (Homeomorph.prodComm I A).continuous_toFun⟩
        map_zero_left := ?_
        map_one_left := ?_ }
    · intro a
      -- Evaluating the descended path family at `0` gives the starting map.
      change d a 0 = f₀ a
      exact hd₀ a
    · intro a
      -- Evaluating at `1` gives the ending map.
      change d a 1 = f₁ a
      exact hd₁ a
  · intro t a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    -- At the fixed point, the descended path family is literally the constant path at `y₀`.
    change d a t = f₀ a
    have hconst : d a t = y₀ := by
      simpa [hdconst]
    exact hconst.trans hf₀.symm

/-- Helper for Proposition 2.8.1: the distinguished branch basepoint maps to the subtype
wide-pushout basepoint. -/
private theorem open_subtype_wide_pushout_branch_leg_basepoint
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (j : ι) :
    open_subtype_wide_pushout_branch_leg X W U hsummand j
        ⟨underTopBasepoint (X j),
          open_subtype_wide_pushout_branch_basepoint_mem X W U hhead hsummand j⟩ =
      open_subtype_wide_pushout_basepoint X W hhead := by
  -- Both subtype points have the wedge basepoint as their ambient image.
  apply Subtype.ext
  exact fundamentalGroupFunctorMap_basepoint (Sigma.ι X j)

/-- Helper for Proposition 2.8.1: branchwise singleton-relative homotopies descend through the
subtype wide pushout to a singleton-relative homotopy on the ambient open subtype. -/
private noncomputable def open_subtype_wide_pushout_desc_homotopy_rel
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (W : TopologicalSpace.Opens ((∐ X).right))
    (U : ∀ j, TopologicalSpace.Opens (X j).right)
    (hhead : (TopologicalSpace.Opens.map ((∐ X).hom)).obj W = ⊤)
    (hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j)
    (hcolim : IsColimit (open_subtype_wide_pushout_cocone X W U hhead hsummand))
    {Y : Type*} [TopologicalSpace Y]
    (y₀ : Y)
    (f₀ f₁ : C(W, Y))
    (f₀branch f₁branch : ∀ j, C(U j, Y))
    (hf₀branch :
      ∀ j,
        f₀.comp (open_subtype_wide_pushout_branch_leg X W U hsummand j).hom = f₀branch j)
    (hf₁branch :
      ∀ j,
        f₁.comp (open_subtype_wide_pushout_branch_leg X W U hsummand j).hom = f₁branch j)
    (hf₀ :
      f₀ (open_subtype_wide_pushout_basepoint X W hhead) = y₀)
    (hf₁ :
      f₁ (open_subtype_wide_pushout_basepoint X W hhead) = y₀)
    (H :
      ∀ j,
        (f₀branch j).HomotopyRel (f₁branch j)
          ({⟨underTopBasepoint (X j),
              open_subtype_wide_pushout_branch_basepoint_mem X W U hhead hsummand j⟩} : Set (U j))) :
    f₀.HomotopyRel f₁ ({open_subtype_wide_pushout_basepoint X W hhead} : Set W) := by
  let S :
      Cocone (open_subtype_wide_pushout_diagram X W U hhead hsummand) :=
    WidePushoutShape.mkCocone
      (TopCat.ofHom (ContinuousMap.const _ (ContinuousMap.const I y₀)))
      (fun j ↦ TopCat.ofHom (homotopyRel_pathspace_map (H j)))
      (fun j ↦ by
        ext u t
        have hu : u = TopCat.terminalIsoPUnit.inv PUnit.unit :=
          terminal_eq_terminal_point u
        subst hu
        let yj : U j :=
          ⟨underTopBasepoint (X j),
            open_subtype_wide_pushout_branch_basepoint_mem X W U hhead hsummand j⟩
        have hbranch₀ :
            f₀branch j yj = y₀ := by
          have hfac :
              f₀ (open_subtype_wide_pushout_branch_leg X W U hsummand j yj) = f₀branch j yj := by
            simpa using congrArg (fun g : C(U j, Y) => g yj) (hf₀branch j)
          rw [open_subtype_wide_pushout_branch_leg_basepoint X W U hhead hsummand j] at hfac
          exact hfac.symm.trans hf₀
        have hconst :
            homotopyRel_pathspace_map (H j) yj = ContinuousMap.const I y₀ :=
          homotopyRel_pathspace_map_eq_const (H j) hbranch₀
        simpa using congrArg (fun p : C(I, Y) => p t) hconst)
  let d : C(W, C(I, Y)) := (hcolim.desc S).hom
  have hd₀ : ∀ x : W, d x 0 = f₀ x := by
    -- Compare the time-`0` evaluation with `f₀` by checking the subtype basepoint and all
    -- subtype branches.
    have hfun :
        (fun x : W ↦ d x 0) = fun x : W ↦ f₀ x := by
      exact open_subtype_wide_pushout_hom_ext X W U hhead hsummand
        (fun x : W ↦ d x 0)
        (fun x : W ↦ f₀ x)
        (by
          have hfac :=
            congrArg
              (fun m : (⊤_ TopCat) ⟶ TopCat.of (C(I, Y)) ↦
                m (TopCat.terminalIsoPUnit.inv PUnit.unit) 0)
              (hcolim.fac S none)
          simpa [d, S, hf₀] using hfac)
        (by
          intro j y
          have hfac :=
            congrArg (fun m : TopCat.of (U j) ⟶ TopCat.of (C(I, Y)) ↦ m y 0)
              (hcolim.fac S (some j))
          have hbranch₀ : homotopyRel_pathspace_map (H j) y 0 = f₀branch j y := by
            simpa [homotopyRel_pathspace_map_apply] using (H j).apply_zero y
          have htarget :
              f₀branch j y = f₀ (open_subtype_wide_pushout_branch_leg X W U hsummand j y) := by
            simpa using (congrArg (fun g : C(U j, Y) => g y) (hf₀branch j)).symm
          exact hfac.trans (hbranch₀.trans htarget))
    exact fun x ↦ congrFun hfun x
  have hd₁ : ∀ x : W, d x 1 = f₁ x := by
    -- The same branchwise comparison at time `1` identifies the terminal evaluation with `f₁`.
    have hfun :
        (fun x : W ↦ d x 1) = fun x : W ↦ f₁ x := by
      exact open_subtype_wide_pushout_hom_ext X W U hhead hsummand
        (fun x : W ↦ d x 1)
        (fun x : W ↦ f₁ x)
        (by
          have hfac :=
            congrArg
              (fun m : (⊤_ TopCat) ⟶ TopCat.of (C(I, Y)) ↦
                m (TopCat.terminalIsoPUnit.inv PUnit.unit) 1)
              (hcolim.fac S none)
          simpa [d, S, hf₁] using hfac)
        (by
          intro j y
          have hfac :=
            congrArg (fun m : TopCat.of (U j) ⟶ TopCat.of (C(I, Y)) ↦ m y 1)
              (hcolim.fac S (some j))
          have hbranch₁ : homotopyRel_pathspace_map (H j) y 1 = f₁branch j y := by
            simpa [homotopyRel_pathspace_map_apply] using (H j).apply_one y
          have htarget :
              f₁branch j y = f₁ (open_subtype_wide_pushout_branch_leg X W U hsummand j y) := by
            simpa using (congrArg (fun g : C(U j, Y) => g y) (hf₁branch j)).symm
          exact hfac.trans (hbranch₁.trans htarget))
    exact fun x ↦ congrFun hfun x
  have hdconst :
      d (open_subtype_wide_pushout_basepoint X W hhead) = ContinuousMap.const I y₀ := by
    -- Evaluating the descended path map on the head leg recovers the constant path at `y₀`.
    have hfac :=
      congrArg
        (fun m : (⊤_ TopCat) ⟶ TopCat.of (C(I, Y)) ↦ m (TopCat.terminalIsoPUnit.inv PUnit.unit))
        (hcolim.fac S none)
    simpa [d, S, open_subtype_wide_pushout_head_leg, open_subtype_wide_pushout_basepoint] using hfac
  exact pathspace_map_homotopy_rel
    d f₀ f₁ hd₀ hd₁ (open_subtype_wide_pushout_basepoint X W hhead) y₀ hf₀ hdconst

/-- Helper for Proposition 2.8.1: the full distinguished summand identifies with the `i`-th branch
object in the subtype wide-pushout for the starred member `wedge_star_cover ... (some i)`. -/
private noncomputable def wedge_star_cover_some_same_branch_entry
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (i : ι) :
    C((X i).right, (@wedge_star_some_family ι X (Classical.decEq ι) V i i)) :=
  ⟨fun y ↦ by
      classical
      refine ⟨y, ?_⟩
      simp [wedge_star_some_family],
    continuous_id.subtype_mk _⟩

/-- Helper for Proposition 2.8.1: the forward cocone evaluates a branch point by keeping it on
the distinguished summand and collapsing every off-center branch to the chosen basepoint. -/
private noncomputable def wedge_star_member_forward_branch_fun
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (_hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι) (j : ι) :
    @wedge_star_some_family ι X (Classical.decEq ι) V i j → (X i).right :=
  let _ : DecidableEq ι := Classical.decEq ι
  fun y ↦ if hji : j = i then hji ▸ y.1 else underTopBasepoint (X i)

/-- Helper for Proposition 2.8.1: the branchwise rule defining the forward cocone is continuous on
each summand input. -/
private theorem wedge_star_member_forward_branch_fun_continuous
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι) (j : ι) :
    Continuous (wedge_star_member_forward_branch_fun X V hxV i j) := by
  classical
  by_cases hji : j = i
  · subst j
    -- On the distinguished branch, the forward map is just the subtype projection.
    simpa [wedge_star_member_forward_branch_fun] using
      (continuous_subtype_val :
        Continuous fun y : @wedge_star_some_family ι X (Classical.decEq ι) V i i ↦ y.1)
  · -- Away from the distinguished branch, the forward map is constant at the basepoint.
    simpa [wedge_star_member_forward_branch_fun, hji] using
      (continuous_const :
        Continuous
          fun _ : @wedge_star_some_family ι X (Classical.decEq ι) V i j ↦
            underTopBasepoint (X i))

/-- Helper for Proposition 2.8.1: the head vertex of the starred-member forward cocone is the
constant map to the distinguished basepoint of `X i`. -/
private noncomputable def wedge_star_member_forward_head
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (_hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι) :
    (⊤_ TopCat) ⟶ (X i).right :=
  TopCat.ofHom (ContinuousMap.const _ (underTopBasepoint (X i)))

/-- Helper for Proposition 2.8.1: the branch maps for the starred-member forward cocone use the
identity on the distinguished branch and constant basepoint maps elsewhere. -/
private noncomputable def wedge_star_member_forward_branch
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι) (j : ι) :
    TopCat.of (@wedge_star_some_family ι X (Classical.decEq ι) V i j) ⟶ (X i).right :=
  TopCat.ofHom
    ⟨wedge_star_member_forward_branch_fun X V hxV i j,
      wedge_star_member_forward_branch_fun_continuous X V hxV i j⟩

/-- Helper for Proposition 2.8.1: the forward cocone branches agree with the common head value at
the glued wedge basepoint. -/
private theorem wedge_star_member_forward_comm
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι) (j : ι) :
    (open_subtype_wide_pushout_diagram X
        (wedge_star_cover X V hxV (some i))
        (@wedge_star_some_family ι X (Classical.decEq ι) V i)
        (wedge_star_cover_head_pullback X V hxV (some i))
        (fun k ↦ by
          classical
          by_cases hki : k = i
          · subst k
            convert wedge_star_cover_some_same_pullback X V hxV i using 1
            simp [wedge_star_some_family]
          · convert wedge_star_cover_some_ne_pullback X V hxV hki using 1
            simp [wedge_star_some_family, hki])).map
        (WidePushoutShape.Hom.init j) ≫
      wedge_star_member_forward_branch X V hxV i j =
        wedge_star_member_forward_head X V hxV i := by
  classical
  by_cases hji : j = i
  · subst j
    ext u
    -- On the distinguished branch, evaluating at the unique terminal point recovers the chosen
    -- basepoint after forgetting the full-open-subtype wrapper.
    have hu : u = TopCat.terminalIsoPUnit.inv PUnit.unit :=
      terminal_eq_terminal_point u
    subst hu
    simp only [wedge_star_member_forward_branch, wedge_star_member_forward_branch_fun,
      wedge_star_member_forward_head, open_subtype_wide_pushout_diagram,
      wedge_star_some_family] at *
    rfl
  · ext u
    -- Off the distinguished branch, both sides are literally the same constant map.
    have hu : u = TopCat.terminalIsoPUnit.inv PUnit.unit :=
      terminal_eq_terminal_point u
    subst hu
    simp only [wedge_star_member_forward_branch, wedge_star_member_forward_branch_fun,
      wedge_star_member_forward_head, open_subtype_wide_pushout_diagram,
      wedge_star_some_family, hji] at *
    rfl

/-- Helper for Proposition 2.8.1: the `i`-th starred member admits the source-faithful forward map
to the distinguished summand, obtained by descending the identity on branch `i` and the
basepoint-constant maps on the other branches. -/
private noncomputable def wedge_star_member_forward_map
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι)
    (hsomeColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV (some i))
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_cover_head_pullback X V hxV (some i))
          (fun j ↦ by
            classical
            by_cases hji : j = i
            · subst j
              convert wedge_star_cover_some_same_pullback X V hxV i using 1
              simp [wedge_star_some_family]
            · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
              simp [wedge_star_some_family, hji]))) :
    C(wedge_star_cover X V hxV (some i), (X i).right) :=
  (hsomeColim.desc <|
    WidePushoutShape.mkCocone
      (wedge_star_member_forward_head X V hxV i)
      (wedge_star_member_forward_branch X V hxV i)
      (wedge_star_member_forward_comm X V hxV i)).hom

/-- Helper for Proposition 2.8.1: the common core has trivial fundamental group because the
branchwise based contractions descend to a contraction of the whole common core. -/
private theorem wedge_common_core_fundamental_group_subsingleton
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ i, TopologicalSpace.Opens (X i).right)
    (hxV : ∀ i, underTopBasepoint (X i) ∈ V i)
    (hbase : ∀ i,
      (ContinuousMap.id (V i)).HomotopicRel
        (ContinuousMap.const (V i) ⟨underTopBasepoint (X i), hxV i⟩)
        {⟨underTopBasepoint (X i), hxV i⟩})
    (hnoneColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV none)
          V
          (wedge_star_cover_head_pullback X V hxV none)
          (wedge_star_cover_none_pullback X V hxV))) :
    Subsingleton
      (FundamentalGroup (wedge_star_cover X V hxV none)
        (wedge_star_cover_basepoint X V hxV none)) := by
  let Hbranch :
      ∀ j,
        (wedge_star_cover_none_leg X V hxV j).HomotopyRel
          (ContinuousMap.const (V j) (wedge_star_cover_basepoint X V hxV none))
          ({⟨underTopBasepoint (X j), hxV j⟩} : Set (V j)) := by
    intro j
    -- Postcompose the local based contraction with the inclusion of `V j` into the common core.
    let Hj : (ContinuousMap.id (V j)).HomotopyRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        ({⟨underTopBasepoint (X j), hxV j⟩} : Set (V j)) := Classical.choice (hbase j)
    simpa [wedge_star_cover_none_leg_basepoint X V hxV j] using
      Hj.compContinuousMap (wedge_star_cover_none_leg X V hxV j)
  have Hcore :
      (ContinuousMap.id (wedge_star_cover X V hxV none)).HomotopyRel
        (ContinuousMap.const (wedge_star_cover X V hxV none)
          (wedge_star_cover_basepoint X V hxV none))
        ({wedge_star_cover_basepoint X V hxV none} :
          Set (wedge_star_cover X V hxV none)) := by
    -- The common core is the subtype wide pushout of the neighborhoods `V j`, so the descended
    -- path-space cocone contracts it to the wedge basepoint.
    exact open_subtype_wide_pushout_desc_homotopy_rel
      X
      (wedge_star_cover X V hxV none)
      V
      (wedge_star_cover_head_pullback X V hxV none)
      (wedge_star_cover_none_pullback X V hxV)
      hnoneColim
      (wedge_star_cover_basepoint X V hxV none)
      (ContinuousMap.id _)
      (ContinuousMap.const _ (wedge_star_cover_basepoint X V hxV none))
      (fun j ↦ wedge_star_cover_none_leg X V hxV j)
      (fun j ↦ ContinuousMap.const (V j) (wedge_star_cover_basepoint X V hxV none))
      (fun j ↦ by
        -- On each branch, the identity on the common core restricts to the branch inclusion.
        ext z
        rfl)
      (fun j ↦ by
        -- The constant contraction target also restricts to the same constant basepoint map.
        ext z
        rfl)
      rfl
      rfl
      Hbranch
  have hcontractible : ContractibleSpace (wedge_star_cover X V hxV none) := by
    -- The descended nullhomotopy of the identity is exactly the criterion for contractibility.
    rw [contractible_iff_id_nullhomotopic]
    exact ⟨wedge_star_cover_basepoint X V hxV none, ⟨Hcore.toHomotopy⟩⟩
  -- Once the common core is contractible, its fundamental group is automatically trivial.
  let _ : ContractibleSpace (wedge_star_cover X V hxV none) := hcontractible
  let _ : SimplyConnectedSpace (wedge_star_cover X V hxV none) :=
    SimplyConnectedSpace.ofContractible (wedge_star_cover X V hxV none)
  change Subsingleton
    (Path.Homotopic.Quotient
      (wedge_star_cover_basepoint X V hxV none)
      (wedge_star_cover_basepoint X V hxV none))
  infer_instance

/-- Helper for Proposition 2.8.1: on the distinguished summand, the descended forward map for the
`some i` star member is literally the identity. -/
private theorem wedge_star_member_forward_map_comp_some_same_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι)
    (hsomeColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV (some i))
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_cover_head_pullback X V hxV (some i))
          (fun j ↦ by
            classical
            by_cases hji : j = i
            · subst j
              convert wedge_star_cover_some_same_pullback X V hxV i using 1
              simp [wedge_star_some_family]
            · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
              simp [wedge_star_some_family, hji]))) :
    (wedge_star_member_forward_map X V hxV i hsomeColim).comp
        (wedge_star_cover_some_same_leg X V hxV i) =
      ContinuousMap.id (X i).right := by
  classical
  -- Read the distinguished branch of the descended cocone and identify the full branch open
  -- subtype with `(X i).right`.
  ext y
  let U :
      ∀ j, TopologicalSpace.Opens (X j).right :=
    @wedge_star_some_family ι X (Classical.decEq ι) V i
  let hsummand :
      ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj
          (wedge_star_cover X V hxV (some i)) = U j := by
    intro j
    classical
    by_cases hji : j = i
    · subst j
      simpa [U, wedge_star_some_family] using wedge_star_cover_some_same_pullback X V hxV i
    · simpa [U, wedge_star_some_family, hji] using wedge_star_cover_some_ne_pullback X V hxV hji
  have hfac :=
    congrArg
      (fun m : TopCat.of (U i) ⟶ (X i).right ↦
        m (wedge_star_cover_some_same_branch_entry X V i y))
      (hsomeColim.fac
        (WidePushoutShape.mkCocone
          (wedge_star_member_forward_head X V hxV i)
          (wedge_star_member_forward_branch X V hxV i)
          (wedge_star_member_forward_comm X V hxV i))
        (some i))
  -- After evaluating on the canonical branch entry, both sides reduce to the same point `y`.
  simpa [wedge_star_member_forward_map, wedge_star_cover_some_same_leg,
    wedge_star_member_forward_branch, wedge_star_member_forward_branch_fun,
    open_subtype_wide_pushout_cocone, open_subtype_wide_pushout_branch_leg,
    hsummand, U, wedge_star_some_family] using hfac

/-- Helper for Proposition 2.8.1: on an off-center branch, the descended forward map for the
`some i` star member is constant at the distinguished basepoint of `(X i).right`. -/
private theorem wedge_star_member_forward_map_comp_some_ne_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι)
    {j : ι} (hji : j ≠ i)
    (hsomeColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV (some i))
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_cover_head_pullback X V hxV (some i))
          (fun k ↦ by
            classical
            by_cases hki : k = i
            · subst k
              convert wedge_star_cover_some_same_pullback X V hxV i using 1
              simp [wedge_star_some_family]
            · convert wedge_star_cover_some_ne_pullback X V hxV hki using 1
              simp [wedge_star_some_family, hki]))) :
    (wedge_star_member_forward_map X V hxV i hsomeColim).comp
        (wedge_star_cover_some_ne_leg X V hxV hji) =
      ContinuousMap.const (V j) (underTopBasepoint (X i)) := by
  classical
  let U :
      ∀ k, TopologicalSpace.Opens (X k).right :=
    @wedge_star_some_family ι X (Classical.decEq ι) V i
  let hsummand :
      ∀ k, (TopologicalSpace.Opens.map ((Sigma.ι X k).right)).obj
          (wedge_star_cover X V hxV (some i)) = U k := by
    intro k
    classical
    by_cases hki : k = i
    · subst k
      simpa [U, wedge_star_some_family] using wedge_star_cover_some_same_pullback X V hxV i
    · simpa [U, wedge_star_some_family, hki] using wedge_star_cover_some_ne_pullback X V hxV hki
  -- Read the off-center face of the descended cocone and simplify it to the constant branch map.
  ext z
  let zU : U j := by
    refine ⟨z.1, ?_⟩
    simpa [U, wedge_star_some_family, hji] using z.2
  have hfac :=
    congrArg
      (fun m : TopCat.of (U j) ⟶ (X i).right ↦ m zU)
      (hsomeColim.fac
        (WidePushoutShape.mkCocone
          (wedge_star_member_forward_head X V hxV i)
          (wedge_star_member_forward_branch X V hxV i)
          (wedge_star_member_forward_comm X V hxV i))
        (some j))
  simpa [wedge_star_member_forward_map, wedge_star_member_forward_branch,
    wedge_star_member_forward_branch_fun, open_subtype_wide_pushout_cocone,
    open_subtype_wide_pushout_branch_leg, wedge_star_cover_some_ne_leg, hsummand, U,
    wedge_star_some_family, hji] using hfac

/-- Helper for Proposition 2.8.1: the starred-member forward map sends the wedge basepoint of the
star member to the distinguished basepoint of the centered summand. -/
private theorem wedge_star_member_forward_map_basepoint
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι)
    (hsomeColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV (some i))
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_cover_head_pullback X V hxV (some i))
          (fun j ↦ by
            classical
            by_cases hji : j = i
            · subst j
              convert wedge_star_cover_some_same_pullback X V hxV i using 1
              simp [wedge_star_some_family]
            · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
              simp [wedge_star_some_family, hji]))) :
    wedge_star_member_forward_map X V hxV i hsomeColim
        (wedge_star_cover_basepoint X V hxV (some i)) =
      underTopBasepoint (X i) := by
  -- Evaluate the already-proved identity-on-the-centered-branch formula at the centered basepoint.
  have hsame :=
    congrArg
      (fun m : C((X i).right, (X i).right) => m (underTopBasepoint (X i)))
      (wedge_star_member_forward_map_comp_some_same_leg X V hxV i hsomeColim)
  simpa [wedge_star_cover_some_same_leg_basepoint X V hxV i] using hsame

/-- Helper for Proposition 2.8.1: the ambient inclusion of a star-cover member fixes its chosen
subtype basepoint. -/
private theorem wedge_star_cover_member_inclusion_basepoint
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (o : Option ι) :
    (TopologicalSpace.Opens.inclusion' (wedge_star_cover X V hxV o)).hom
        (wedge_star_cover_basepoint X V hxV o) =
      underTopBasepoint (∐ X) := by
  rfl

/-- Helper for Proposition 2.8.1: including the centered branch into its star member and then into
the wedge is exactly the coproduct inclusion `Sigma.ι X i`. -/
private theorem wedge_star_cover_some_inclusion_comp_same_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι) :
    (TopologicalSpace.Opens.inclusion' (wedge_star_cover X V hxV (some i))).hom.comp
        (wedge_star_cover_some_same_leg X V hxV i) =
      TopCat.Hom.hom ((Sigma.ι X i).right) := by
  -- Both composites forget the same subtype witness and land in the wedge through `Sigma.ι X i`.
  ext y
  rfl

/-- Helper for Proposition 2.8.1: the off-center branch contraction for a `some i` star member is
already expressed in the exact dependent branch coordinates needed by the subtype wide-pushout
descent. -/
private noncomputable def wedge_star_some_off_center_homotopy_rel_transport
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X] [DecidableEq ι]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hbase : ∀ j,
      (ContinuousMap.id (V j)).HomotopicRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        {⟨underTopBasepoint (X j), hxV j⟩})
    (i : ι)
    {j : ι} (hji : j ≠ i) :
    let W := wedge_star_cover X V hxV (some i)
    let U : ∀ k, TopologicalSpace.Opens (X k).right :=
      wedge_star_some_family X V i
    let hhead := wedge_star_cover_head_pullback X V hxV (some i)
    let hsummand :
        ∀ k, (TopologicalSpace.Opens.map ((Sigma.ι X k).right)).obj W = U k := fun k ↦ by
      classical
      by_cases hki : k = i
      · subst k
        simpa [U, wedge_star_some_family] using wedge_star_cover_some_same_pullback X V hxV i
      · simpa [U, wedge_star_some_family, hki] using wedge_star_cover_some_ne_pullback X V hxV hki
    (ContinuousMap.const (U j) (wedge_star_cover_basepoint X V hxV (some i))).HomotopyRel
      ((open_subtype_wide_pushout_branch_leg X W U hsummand j).hom)
      ({⟨underTopBasepoint (X j),
          open_subtype_wide_pushout_branch_basepoint_mem X W U hhead hsummand j⟩} : Set (U j)) :=
  by
    classical
    let W := wedge_star_cover X V hxV (some i)
    let U : ∀ k, TopologicalSpace.Opens (X k).right :=
      wedge_star_some_family X V i
    let e : C(U j, V j) :=
      ⟨fun y ↦
          ⟨y.1, by
            simpa [U, wedge_star_some_family, hji] using y.2⟩,
        continuous_subtype_val.subtype_mk
          (fun y ↦ by
            simpa [U, wedge_star_some_family, hji] using y.2)⟩
    let hhead := wedge_star_cover_head_pullback X V hxV (some i)
    let hsummand :
        ∀ k, (TopologicalSpace.Opens.map ((Sigma.ι X k).right)).obj W = U k := fun k ↦ by
      by_cases hki : k = i
      · subst k
        simpa [U, wedge_star_some_family] using wedge_star_cover_some_same_pullback X V hxV i
      · simpa [U, wedge_star_some_family, hki] using wedge_star_cover_some_ne_pullback X V hxV hki
    have hyj : underTopBasepoint (X j) ∈ U j := by
      simpa [U, wedge_star_some_family, hji] using hxV j
    let yj : U j :=
      ⟨underTopBasepoint (X j), hyj⟩
    let Hj : (ContinuousMap.id (V j)).HomotopyRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        ({⟨underTopBasepoint (X j), hxV j⟩} : Set (V j)) := Classical.choice (hbase j)
    let HU :
        e.HomotopyRel
          (ContinuousMap.const (U j) ⟨underTopBasepoint (X j), hxV j⟩)
          ({yj} : Set (U j)) := by
      -- Restrict the chosen based contraction on `V j` along the explicit map `U j ⟶ V j`.
      refine
        { toHomotopy := Hj.toHomotopy.compContinuousMap e
          prop' := ?_ }
      intro t y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      have heq : e yj = ⟨underTopBasepoint (X j), hxV j⟩ := by
        rfl
      have hprop : Hj.toHomotopy (t, e yj) = e yj := by
        simpa [heq] using Hj.prop t (e yj) (by simp [heq])
      simpa [ContinuousMap.Homotopy.compContinuousMap, e, yj, U, wedge_star_some_family, hji]
        using hprop
    let HW :=
      (HU.compContinuousMap (wedge_star_cover_some_ne_leg X V hxV hji)).symm
    have hconst :
        (wedge_star_cover_some_ne_leg X V hxV hji).comp
            (ContinuousMap.const (U j) ⟨underTopBasepoint (X j), hxV j⟩) =
          ContinuousMap.const (U j) (wedge_star_cover_basepoint X V hxV (some i)) := by
      -- The off-center branch inclusion sends the chosen neighborhood basepoint to the wedge
      -- basepoint of the centered star member.
      ext y
      simp [wedge_star_cover_some_ne_leg_basepoint]
    have hbranch :
        (wedge_star_cover_some_ne_leg X V hxV hji).comp e =
          (open_subtype_wide_pushout_branch_leg X W U hsummand j).hom := by
      -- Both maps are the same subtype inclusion of the off-center branch into `W`.
      ext y
      rfl
    simpa [yj, hyj, U, wedge_star_some_family, hji] using HW.cast hconst hbranch

/-- Helper for Proposition 2.8.1: each starred member deformation-retracts onto its distinguished
summand, relative to the wedge basepoint of that member. -/
private noncomputable def wedge_star_member_backward_forward_homotopy_rel
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hbase : ∀ j,
      (ContinuousMap.id (V j)).HomotopicRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        {⟨underTopBasepoint (X j), hxV j⟩})
    (i : ι)
    (hsomeColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV (some i))
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_cover_head_pullback X V hxV (some i))
          (fun j ↦ by
            classical
            by_cases hji : j = i
            · subst j
              convert wedge_star_cover_some_same_pullback X V hxV i using 1
              simp [wedge_star_some_family]
            · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
              simp [wedge_star_some_family, hji]))) :
    ((wedge_star_cover_some_same_leg X V hxV i).comp
        (wedge_star_member_forward_map X V hxV i hsomeColim)).HomotopyRel
      (ContinuousMap.id (wedge_star_cover X V hxV (some i)))
      ({wedge_star_cover_basepoint X V hxV (some i)} :
        Set (wedge_star_cover X V hxV (some i))) :=
  by
    classical
    let W := wedge_star_cover X V hxV (some i)
    let U : ∀ j, TopologicalSpace.Opens (X j).right :=
      @wedge_star_some_family ι X (Classical.decEq ι) V i
    let hhead := wedge_star_cover_head_pullback X V hxV (some i)
    let hsummand :
        ∀ j, (TopologicalSpace.Opens.map ((Sigma.ι X j).right)).obj W = U j := by
      intro j
      classical
      by_cases hji : j = i
      · subst j
        simpa [U, wedge_star_some_family] using wedge_star_cover_some_same_pullback X V hxV i
      · simpa [U, wedge_star_some_family, hji] using wedge_star_cover_some_ne_pullback X V hxV hji
    let f₀branch : ∀ j, C(U j, W) := fun j ↦
      if hji : j = i then
        (open_subtype_wide_pushout_branch_leg X W U hsummand j).hom
      else
        ContinuousMap.const (U j) (wedge_star_cover_basepoint X V hxV (some i))
    have hf₀branch :
        ∀ j,
          ((wedge_star_cover_some_same_leg X V hxV i).comp
              (wedge_star_member_forward_map X V hxV i hsomeColim)).comp
              (open_subtype_wide_pushout_branch_leg X W U hsummand j).hom =
            f₀branch j := by
      intro j
      classical
      by_cases hji : j = i
      · subst j
        -- On the distinguished branch, the forward map is already the identity.
        ext y
        have hsame :=
          congrArg
            (fun m : C((X i).right, (X i).right) => m y.1)
            (wedge_star_member_forward_map_comp_some_same_leg X V hxV i hsomeColim)
        calc
          (Sigma.ι X i).right
              ((wedge_star_member_forward_map X V hxV i hsomeColim)
                ((open_subtype_wide_pushout_branch_leg X W U hsummand i).hom y)) =
              (Sigma.ι X i).right y.1 := by
                simpa [open_subtype_wide_pushout_branch_leg] using
                  congrArg ((Sigma.ι X i).right) hsame
          _ = ↑((f₀branch i) y) := by
                simp [f₀branch, open_subtype_wide_pushout_branch_leg]
      · -- Off the distinguished branch, the forward map collapses the branch to the wedge
        -- basepoint of the star member.
        ext y
        let yV : V j := by
          refine ⟨y.1, ?_⟩
          simpa [U, wedge_star_some_family, hji] using y.2
        have hne :=
          congrArg
            (fun m : C(V j, (X i).right) => m yV)
            (wedge_star_member_forward_map_comp_some_ne_leg X V hxV i hji hsomeColim)
        calc
          (Sigma.ι X i).right
              ((wedge_star_member_forward_map X V hxV i hsomeColim)
                ((open_subtype_wide_pushout_branch_leg X W U hsummand j).hom y)) =
              (Sigma.ι X i).right (underTopBasepoint (X i)) := by
                simpa [yV, W, U, hsummand, wedge_star_some_family, hji,
                  open_subtype_wide_pushout_branch_leg] using
                  congrArg ((Sigma.ι X i).right) hne
          _ = underTopBasepoint (∐ X) := fundamentalGroupFunctorMap_basepoint (Sigma.ι X i)
          _ = ↑(wedge_star_cover_basepoint X V hxV (some i)) := by
                rfl
          _ = ↑((f₀branch j) y) := by
                simp [f₀branch, hji]
    have hf₀ :
        ((wedge_star_cover_some_same_leg X V hxV i).comp
            (wedge_star_member_forward_map X V hxV i hsomeColim))
          (open_subtype_wide_pushout_basepoint X W hhead) =
          wedge_star_cover_basepoint X V hxV (some i) := by
      -- Evaluate the centered branch equality at the common basepoint.
      have hbranch :=
        congrArg
          (fun g : C(U i, W) =>
            g ⟨underTopBasepoint (X i),
              open_subtype_wide_pushout_branch_basepoint_mem X W U hhead hsummand i⟩)
          (hf₀branch i)
      simpa [f₀branch, open_subtype_wide_pushout_branch_leg_basepoint X W U hhead hsummand i]
        using hbranch
    have Hbranch :
        ∀ j,
          (f₀branch j).HomotopyRel
            ((open_subtype_wide_pushout_branch_leg X W U hsummand j).hom)
            ({⟨underTopBasepoint (X j),
                open_subtype_wide_pushout_branch_basepoint_mem X W U hhead hsummand j⟩} :
              Set (U j)) := by
      intro j
      classical
      by_cases hji : j = i
      · subst j
        -- The centered branch is fixed pointwise, so the relative homotopy is just the identity.
        simpa [f₀branch, W, U, hsummand, wedge_star_some_family,
          open_subtype_wide_pushout_branch_basepoint_mem] using
          (ContinuousMap.HomotopyRel.refl
            (open_subtype_wide_pushout_branch_leg X W U hsummand i).hom
            ({⟨underTopBasepoint (X i),
                open_subtype_wide_pushout_branch_basepoint_mem X W U hhead hsummand i⟩} :
              Set (U i)))
      · -- Off-center branches use the transported local contraction.
        simpa [W, U, hhead, hsummand, f₀branch, hji] using
          wedge_star_some_off_center_homotopy_rel_transport X V hxV hbase i hji
    -- Descend the branchwise deformation retractions through the subtype wide-pushout colimit.
    exact open_subtype_wide_pushout_desc_homotopy_rel
      X W U hhead hsummand hsomeColim
      (wedge_star_cover_basepoint X V hxV (some i))
      ((wedge_star_cover_some_same_leg X V hxV i).comp
        (wedge_star_member_forward_map X V hxV i hsomeColim))
      (ContinuousMap.id W)
      f₀branch
      (fun j ↦ (open_subtype_wide_pushout_branch_leg X W U hsummand j).hom)
      hf₀branch
      (fun j ↦ rfl)
      hf₀
      rfl
      Hbranch

/-- Helper for Proposition 2.8.1: each non-core star member is homotopy equivalent to its
distinguished summand. -/
private noncomputable def wedge_star_member_homotopy_equiv
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hbase : ∀ j,
      (ContinuousMap.id (V j)).HomotopicRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        {⟨underTopBasepoint (X j), hxV j⟩})
    (i : ι)
    (hsomeColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV (some i))
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_cover_head_pullback X V hxV (some i))
          (fun j ↦ by
            classical
            by_cases hji : j = i
            · subst j
              convert wedge_star_cover_some_same_pullback X V hxV i using 1
              simp [wedge_star_some_family]
            · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
              simp [wedge_star_some_family, hji]))) :
    ContinuousMap.HomotopyEquiv (wedge_star_cover X V hxV (some i)) (X i).right where
  toFun := wedge_star_member_forward_map X V hxV i hsomeColim
  invFun := wedge_star_cover_some_same_leg X V hxV i
  left_inv :=
    ⟨(wedge_star_member_backward_forward_homotopy_rel X V hxV hbase i hsomeColim).toHomotopy⟩
  right_inv := by
    -- The forward map is already literally inverse to the distinguished branch inclusion.
    simpa [wedge_star_member_forward_map_comp_some_same_leg X V hxV i hsomeColim] using
      (show (ContinuousMap.id (X i).right).Homotopic (ContinuousMap.id (X i).right) from
        ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id (X i).right)⟩)

/-- Helper for Proposition 2.8.1: each star-cover member is regarded as a based space using the
common wedge basepoint. -/
private noncomputable def wedge_star_cover_member_based_space
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (o : Option ι) :
    Under (⊤_ TopCat) :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (wedge_star_cover_basepoint X V hxV o)))

/-- Helper for Proposition 2.8.1: the ambient inclusion of a star member is a morphism of based
spaces. -/
private theorem wedge_star_cover_member_inclusion_under_hom_w
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (o : Option ι) :
    (wedge_star_cover_member_based_space X V hxV o).hom ≫
        TopCat.ofHom (TopologicalSpace.Opens.inclusion' (wedge_star_cover X V hxV o)).hom =
      (∐ X).hom := by
  -- Evaluate both morphisms at the unique terminal point to reduce to the wedge basepoint.
  ext u
  change (wedge_star_cover_basepoint X V hxV o : wedge_star_cover X V hxV o).1 = (∐ X).hom u
  exact (wedge_head_eq_basepoint X u).symm

/-- Helper for Proposition 2.8.1: the ambient inclusion of a star member as a based-space map. -/
private noncomputable def wedge_star_cover_member_inclusion_under_hom
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (o : Option ι) :
    wedge_star_cover_member_based_space X V hxV o ⟶ ∐ X :=
  Under.homMk
    (TopCat.ofHom (TopologicalSpace.Opens.inclusion' (wedge_star_cover X V hxV o)).hom)
    (wedge_star_cover_member_inclusion_under_hom_w X V hxV o)

/-- Helper for Proposition 2.8.1: the distinguished branch inclusion is a morphism of based
spaces. -/
private theorem wedge_star_cover_some_same_under_hom_w
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι) :
    (X i).hom ≫ TopCat.ofHom (wedge_star_cover_some_same_leg X V hxV i) =
      (wedge_star_cover_member_based_space X V hxV (some i)).hom := by
  -- The distinguished branch inclusion sends the actual summand basepoint to the star-member
  -- basepoint, so the two `Under` legs agree on the terminal point.
  ext u
  have hbase : (X i).hom u = underTopBasepoint (X i) :=
    under_hom_eq_basepoint (X i) u
  have hcomp :
      ((wedge_star_cover_some_same_leg X V hxV i).comp (TopCat.Hom.hom (X i).hom)) u =
        wedge_star_cover_some_same_leg X V hxV i (underTopBasepoint (X i)) :=
    congrArg (wedge_star_cover_some_same_leg X V hxV i) hbase
  have hval :
      wedge_star_cover_some_same_leg X V hxV i (underTopBasepoint (X i)) =
        wedge_star_cover_basepoint X V hxV (some i) :=
    wedge_star_cover_some_same_leg_basepoint X V hxV i
  have hgoal :
      ((wedge_star_cover_some_same_leg X V hxV i).comp (TopCat.Hom.hom (X i).hom)) u =
        wedge_star_cover_basepoint X V hxV (some i) :=
    hcomp.trans hval
  simpa [wedge_star_cover_member_based_space] using hgoal

/-- Helper for Proposition 2.8.1: the centered branch inclusion viewed as a map of based
spaces. -/
private noncomputable def wedge_star_cover_some_same_under_hom
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι) :
    X i ⟶ wedge_star_cover_member_based_space X V hxV (some i) :=
  Under.homMk
    (TopCat.ofHom (wedge_star_cover_some_same_leg X V hxV i))
    (wedge_star_cover_some_same_under_hom_w X V hxV i)

/-- Helper for Proposition 2.8.1: the starred deformation retraction map is a morphism of based
spaces. -/
private theorem wedge_star_member_forward_under_hom_w
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι)
    (hsomeColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV (some i))
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_cover_head_pullback X V hxV (some i))
          (fun j ↦ by
            classical
            by_cases hji : j = i
            · subst j
              convert wedge_star_cover_some_same_pullback X V hxV i using 1
              simp [wedge_star_some_family]
            · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
              simp [wedge_star_some_family, hji]))) :
    (wedge_star_cover_member_based_space X V hxV (some i)).hom ≫
        TopCat.ofHom (wedge_star_member_forward_map X V hxV i hsomeColim) =
      (X i).hom := by
  -- The descended retraction was built to preserve the chosen wedge basepoint.
  ext u
  change wedge_star_member_forward_map X V hxV i hsomeColim
      (wedge_star_cover_basepoint X V hxV (some i)) =
    (X i).hom u
  rw [wedge_star_member_forward_map_basepoint X V hxV i hsomeColim]
  exact (under_hom_eq_basepoint (X i) u).symm

/-- Helper for Proposition 2.8.1: the starred deformation retraction map as a based-space
morphism. -/
private noncomputable def wedge_star_member_forward_under_hom
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι)
    (hsomeColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV (some i))
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_cover_head_pullback X V hxV (some i))
          (fun j ↦ by
            classical
            by_cases hji : j = i
            · subst j
              convert wedge_star_cover_some_same_pullback X V hxV i using 1
              simp [wedge_star_some_family]
            · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
              simp [wedge_star_some_family, hji]))) :
    wedge_star_cover_member_based_space X V hxV (some i) ⟶ X i :=
  Under.homMk
    (TopCat.ofHom (wedge_star_member_forward_map X V hxV i hsomeColim))
    (wedge_star_member_forward_under_hom_w X V hxV i hsomeColim)

/-- Helper for Proposition 2.8.1: the based map to the distinguished summand induces an
isomorphism on fundamental groups. -/
private theorem wedge_star_member_forward_under_hom_isIso
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hbase : ∀ j,
      (ContinuousMap.id (V j)).HomotopicRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        {⟨underTopBasepoint (X j), hxV j⟩})
    (i : ι)
    (hsomeColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV (some i))
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_cover_head_pullback X V hxV (some i))
          (fun j ↦ by
            classical
            by_cases hji : j = i
            · subst j
              convert wedge_star_cover_some_same_pullback X V hxV i using 1
              simp [wedge_star_some_family]
            · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
              simp [wedge_star_some_family, hji]))) :
    IsIso (fundamentalGroupFunctor.map
      (wedge_star_member_forward_under_hom X V hxV i hsomeColim)) := by
  let g := fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i)
  let f := fundamentalGroupFunctor.map (wedge_star_member_forward_under_hom X V hxV i hsomeColim)
  have hleft_rel :
      basedHomotopyRel
        (wedge_star_member_forward_under_hom X V hxV i hsomeColim ≫
          wedge_star_cover_some_same_under_hom X V hxV i)
        (𝟙 (wedge_star_cover_member_based_space X V hxV (some i))) := by
    -- The geometric deformation retraction already gives the needed singleton-relative homotopy.
    refine ⟨?_⟩
    simpa [wedge_star_cover_member_based_space] using
      wedge_star_member_backward_forward_homotopy_rel X V hxV hbase i hsomeColim
  have hleft : f ≫ g = 𝟙 _ := by
    -- Homotopy invariance turns the based deformation retraction into an identity on `π₁`.
    simpa [f, g, Functor.map_comp] using
      (fundamentalGroupFunctor_map_eq_of_based_homotopy hleft_rel)
  have hright_under :
      wedge_star_cover_some_same_under_hom X V hxV i ≫
        wedge_star_member_forward_under_hom X V hxV i hsomeColim = 𝟙 (X i) := by
    -- On the distinguished summand, the forward map is literally inverse to the inclusion.
    ext y
    simpa [wedge_star_cover_some_same_under_hom, wedge_star_member_forward_under_hom] using
      congrArg (fun m : C((X i).right, (X i).right) => m y)
        (wedge_star_member_forward_map_comp_some_same_leg X V hxV i hsomeColim)
  have hright : g ≫ f = 𝟙 _ := by
    simpa [f, g] using congrArg fundamentalGroupFunctor.map hright_under
  exact ⟨⟨g, hleft, hright⟩⟩

/-- Helper for Proposition 2.8.1: any outgoing cover morphism from the `some i` vertex to a
different vertex forces the source star-member group to be trivial. -/
private theorem wedge_star_member_fundamental_group_subsingleton_of_hom_to_other
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hnoneSubsingleton :
      Subsingleton
        (FundamentalGroup (wedge_star_cover X V hxV none)
          (wedge_star_cover_basepoint X V hxV none)))
    (i : ι)
    {s o : TopologicalSpace.IsOpenCover.Index (wedge_star_cover X V hxV)}
    (hs : (show Option ι from s) = some i)
    (f : s ⟶ o)
    (ho : o ≠ s) :
    Subsingleton
      (FundamentalGroup (wedge_star_cover X V hxV (some i))
        (wedge_star_cover_basepoint X V hxV (some i))) := by
  change Option ι at s o
  change s = some i at hs
  subst hs
  have hle : wedge_star_cover X V hxV (some i) ≤ wedge_star_cover X V hxV o := f.hom.le
  have hVi_top : V i = ⊤ := by
    -- The `i`-th summand lies entirely in the source star member, so inclusion into a different
    -- target member forces the `i`-th pullback there to be all of `(X i).right`.
    apply TopologicalSpace.Opens.ext
    ext y
    constructor
    · intro hy
      trivial
    · intro _
      have hySome : ((Sigma.ι X i).right y) ∈ wedge_star_cover X V hxV (some i) :=
        mem_wedge_star_cover_some_same_pullback_iff X V hxV i y
      have hyTarget : ((Sigma.ι X i).right y) ∈ wedge_star_cover X V hxV o := hle hySome
      cases o with
      | none =>
          exact (mem_wedge_star_cover_none_pullback_iff X V hxV i y).mp hyTarget
      | some j =>
          have hij : i ≠ j := by
            intro hij
            exact ho (by simp [hij])
          exact (mem_wedge_star_cover_some_ne_pullback_iff X V hxV hij y).mp hyTarget
  have hcover_eq : wedge_star_cover X V hxV (some i) = wedge_star_cover X V hxV none := by
    -- Once `V i = ⊤`, the `some i` star member has the same pullbacks as the common core.
    apply wedge_star_cover_ext X
    · rw [wedge_star_cover_head_pullback X V hxV (some i),
        wedge_star_cover_head_pullback X V hxV none]
    · intro j
      by_cases hji : j = i
      · subst j
        rw [wedge_star_cover_some_same_pullback X V hxV i,
          wedge_star_cover_none_pullback X V hxV i, hVi_top]
      · rw [wedge_star_cover_some_ne_pullback X V hxV hji,
          wedge_star_cover_none_pullback X V hxV j]
  have hsome_le_none : wedge_star_cover X V hxV (some i) ≤ wedge_star_cover X V hxV none := by
    rw [hcover_eq]
  have hnone_le_some : wedge_star_cover X V hxV none ≤ wedge_star_cover X V hxV (some i) := by
    rw [hcover_eq]
  let φ : C(wedge_star_cover X V hxV (some i), wedge_star_cover X V hxV none) :=
    ⟨fun x ↦ ⟨x.1, hsome_le_none x.2⟩, continuous_subtype_val.subtype_mk _⟩
  let ψ : C(wedge_star_cover X V hxV none, wedge_star_cover X V hxV (some i)) :=
    ⟨fun x ↦ ⟨x.1, hnone_le_some x.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hφ_base :
      φ (wedge_star_cover_basepoint X V hxV (some i)) =
        wedge_star_cover_basepoint X V hxV none := by
    apply Subtype.ext
    rfl
  have hψ_base :
      ψ (wedge_star_cover_basepoint X V hxV none) =
        wedge_star_cover_basepoint X V hxV (some i) := by
    apply Subtype.ext
    rfl
  let some_to_none :
      wedge_star_cover_member_based_space X V hxV (some i) ⟶
        wedge_star_cover_member_based_space X V hxV none :=
    Under.homMk (TopCat.ofHom φ) (by
      -- The inclusion from the off-center star member into the common core fixes the wedge
      -- basepoint on the nose.
      ext u
      change φ ((wedge_star_cover_member_based_space X V hxV (some i)).hom u) =
        (wedge_star_cover_member_based_space X V hxV none).hom u
      rw [show (wedge_star_cover_member_based_space X V hxV (some i)).hom u =
          wedge_star_cover_basepoint X V hxV (some i) by rfl]
      rw [show (wedge_star_cover_member_based_space X V hxV none).hom u =
          wedge_star_cover_basepoint X V hxV none by rfl]
      exact hφ_base)
  let none_to_some :
      wedge_star_cover_member_based_space X V hxV none ⟶
        wedge_star_cover_member_based_space X V hxV (some i) :=
    Under.homMk (TopCat.ofHom ψ) (by
      -- The reverse inclusion uses the same literal wedge basepoint.
      ext u
      change ψ ((wedge_star_cover_member_based_space X V hxV none).hom u) =
        (wedge_star_cover_member_based_space X V hxV (some i)).hom u
      rw [show (wedge_star_cover_member_based_space X V hxV none).hom u =
          wedge_star_cover_basepoint X V hxV none by rfl]
      rw [show (wedge_star_cover_member_based_space X V hxV (some i)).hom u =
          wedge_star_cover_basepoint X V hxV (some i) by rfl]
      exact hψ_base)
  have hcomp :
      fundamentalGroupFunctor.map some_to_none ≫ fundamentalGroupFunctor.map none_to_some =
        𝟙 _ := by
    have hstrict : some_to_none ≫ none_to_some = 𝟙 _ := by
      ext x
      rfl
    simpa using congrArg fundamentalGroupFunctor.map hstrict
  have hsub_none :
      Subsingleton (fundamentalGroupFunctor.obj (wedge_star_cover_member_based_space X V hxV none)) := by
    simpa [wedge_star_cover_member_based_space] using hnoneSubsingleton
  -- The source group retracts onto the already-trivial common-core group, so it is trivial too.
  refine ⟨fun a b ↦ ?_⟩
  let g := fundamentalGroupFunctor.map some_to_none
  let h := fundamentalGroupFunctor.map none_to_some
  have hab : g.hom a = g.hom b := Subsingleton.elim _ _
  have hcomp_a := congrArg (fun z => z.hom a) hcomp
  have hcomp_b := congrArg (fun z => z.hom b) hcomp
  have hcomp_a' : h.hom (g.hom a) = a := by
    simpa [g, h] using hcomp_a
  have hcomp_b' : h.hom (g.hom b) = b := by
    simpa [g, h] using hcomp_b
  have hstep : a = h.hom (g.hom b) := by
    rw [← hcomp_a', hab]
  exact hstep.trans hcomp_b'

/-- Helper for Proposition 2.8.1: the `some i` vertex contributes the distinguished free-product
generator after retracting the star member onto the `i`-th summand. -/
private noncomputable def wedge_star_cover_to_coprod_some_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hbase : ∀ j,
      (ContinuousMap.id (V j)).HomotopicRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        {⟨underTopBasepoint (X j), hxV j⟩})
    (hsomeColim :
      ∀ i,
        IsColimit
          (open_subtype_wide_pushout_cocone X
            (wedge_star_cover X V hxV (some i))
            (@wedge_star_some_family ι X (Classical.decEq ι) V i)
            (wedge_star_cover_head_pullback X V hxV (some i))
            (fun j ↦ by
              classical
              by_cases hji : j = i
              · subst j
                convert wedge_star_cover_some_same_pullback X V hxV i using 1
                simp [wedge_star_some_family]
              · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
                simp [wedge_star_some_family, hji])))
    (i : ι) :
    (fundamental_group_cover_diagram
        (wedge_star_cover X V hxV)
        (underTopBasepoint (∐ X))
        (wedge_star_cover_basepoint_mem X V hxV)).obj (some i) ⟶
      GrpCat.of (Monoid.CoprodI (fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))) :=
  fundamentalGroupFunctor.map (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
    GrpCat.ofHom
      (Monoid.CoprodI.of
        (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
        (i := i))

/-- Helper for Proposition 2.8.1: the cover-to-coproduct cocone leg at any actual cover index. -/
private noncomputable def wedge_star_cover_to_coprod_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hbase : ∀ j,
      (ContinuousMap.id (V j)).HomotopicRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        {⟨underTopBasepoint (X j), hxV j⟩})
    (hnoneSubsingleton :
      Subsingleton
        (FundamentalGroup (wedge_star_cover X V hxV none)
          (wedge_star_cover_basepoint X V hxV none)))
    (hsomeColim :
      ∀ i,
        IsColimit
          (open_subtype_wide_pushout_cocone X
            (wedge_star_cover X V hxV (some i))
            (@wedge_star_some_family ι X (Classical.decEq ι) V i)
            (wedge_star_cover_head_pullback X V hxV (some i))
            (fun j ↦ by
              classical
              by_cases hji : j = i
              · subst j
                convert wedge_star_cover_some_same_pullback X V hxV i using 1
                simp [wedge_star_some_family]
              · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
                simp [wedge_star_some_family, hji])))
    (o : TopologicalSpace.IsOpenCover.Index (wedge_star_cover X V hxV)) :
    (fundamental_group_cover_diagram
        (wedge_star_cover X V hxV)
        (underTopBasepoint (∐ X))
        (wedge_star_cover_basepoint_mem X V hxV)).obj o ⟶
      GrpCat.of (Monoid.CoprodI (fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))) :=
  match (show Option ι from o) with
  | none => GrpCat.ofHom 1
  | some i => wedge_star_cover_to_coprod_some_leg X V hxV hbase hsomeColim i

/-- Helper for Proposition 2.8.1: exposing the actual cover indices as raw `Option ι` vertices
reduces any morphism proof to the four concrete source-target cases. -/
private theorem wedge_star_cover_index_hom_cases
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    {a b : TopologicalSpace.IsOpenCover.Index (wedge_star_cover X V hxV)}
    (f : a ⟶ b)
    {motive : Prop}
    (hnone_none : ((show Option ι from a) = none) → ((show Option ι from b) = none) → motive)
    (hnone_some :
      ∀ j, ((show Option ι from a) = none) → ((show Option ι from b) = some j) → motive)
    (hsome_none :
      ∀ i, ((show Option ι from a) = some i) → ((show Option ι from b) = none) → motive)
    (hsome_some :
      ∀ i j, ((show Option ι from a) = some i) → ((show Option ι from b) = some j) → motive) :
    motive := by
  change Option ι at a b
  cases a with
  | none =>
      cases b with
      | none =>
          exact hnone_none rfl rfl
      | some j =>
          exact hnone_some j rfl rfl
  | some i =>
      cases b with
      | none =>
          exact hsome_none i rfl rfl
      | some j =>
          exact hsome_some i j rfl rfl

/-- Helper for Proposition 2.8.1: any endomorphism of a fixed `some i` star-cover vertex induces
the identity on the corresponding diagram group. -/
private theorem wedge_star_cover_some_endomorphism_based_map_eq_id
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι)
    (f :
      (show TopologicalSpace.IsOpenCover.Index (wedge_star_cover X V hxV) from some i) ⟶
        (show TopologicalSpace.IsOpenCover.Index (wedge_star_cover X V hxV) from some i)) :
    Under.homMk
        (((TopologicalSpace.Opens.toTopCat ((∐ X).right)).map f.hom))
        (by
          ext u
          rfl) =
      𝟙 (wedge_star_cover_member_based_space X V hxV (some i)) := by
  -- The actual self-inclusion on a fixed star-cover member is pointwise the identity map.
  ext u
  rfl

/-- Helper for Proposition 2.8.1: any endomorphism of a fixed `some i` star-cover vertex induces
the identity on the corresponding diagram group. -/
private theorem wedge_star_cover_diagram_map_some_same_eq_id
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι)
    (f :
      (show TopologicalSpace.IsOpenCover.Index (wedge_star_cover X V hxV) from some i) ⟶
        (show TopologicalSpace.IsOpenCover.Index (wedge_star_cover X V hxV) from some i)) :
    ((fundamental_group_cover_diagram
          (wedge_star_cover X V hxV)
          (underTopBasepoint (∐ X))
          (wedge_star_cover_basepoint_mem X V hxV)).map f) =
      𝟙 _ := by
  -- Route correction: normalize the actual cover endomorphism at the based-space level first,
  -- then apply the fundamental-group functor once.
  simpa [fundamental_group_cover_diagram] using
    congrArg fundamentalGroupFunctor.map
      (wedge_star_cover_some_endomorphism_based_map_eq_id X V hxV i f)

/-- Helper for Proposition 2.8.1: the centered branch inclusion followed by the ambient star-member
inclusion is exactly the coproduct leg `Sigma.ι X i`. -/
private theorem wedge_star_cover_some_same_under_hom_comp_member_inclusion
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι) :
    wedge_star_cover_some_same_under_hom X V hxV i ≫
        wedge_star_cover_member_inclusion_under_hom X V hxV (some i) =
      Sigma.ι X i := by
  -- Both based maps forget the same subtype witness before entering the wedge through the
  -- distinguished coproduct leg.
  ext y
  exact congrArg
    (fun m : C((X i).right, (∐ X).right) => m y)
    (wedge_star_cover_some_inclusion_comp_same_leg X V hxV i)

/-- Helper for Proposition 2.8.1: on the distinguished summand, the forward map is literally
inverse to the centered branch inclusion. -/
private theorem wedge_star_cover_some_same_under_hom_comp_forward_under_hom_eq_id
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (i : ι)
    (hsomeColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV (some i))
          (@wedge_star_some_family ι X (Classical.decEq ι) V i)
          (wedge_star_cover_head_pullback X V hxV (some i))
          (fun j ↦ by
            classical
            by_cases hji : j = i
            · subst j
              convert wedge_star_cover_some_same_pullback X V hxV i using 1
              simp [wedge_star_some_family]
            · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
              simp [wedge_star_some_family, hji]))) :
    wedge_star_cover_some_same_under_hom X V hxV i ≫
        wedge_star_member_forward_under_hom X V hxV i hsomeColim =
      𝟙 (X i) := by
  -- The centered branch is fixed pointwise by the star-member deformation retraction.
  ext y
  simpa [wedge_star_cover_some_same_under_hom, wedge_star_member_forward_under_hom] using
    congrArg (fun m : C((X i).right, (X i).right) => m y)
      (wedge_star_member_forward_map_comp_some_same_leg X V hxV i hsomeColim)

/-- Helper for Proposition 2.8.1: the star-member retraction followed by the centered branch
inclusion induces the identity on the corresponding fundamental group. -/
private theorem wedge_star_member_forward_then_same_fundamental_group_eq_id
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hbase : ∀ j,
      (ContinuousMap.id (V j)).HomotopicRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        {⟨underTopBasepoint (X j), hxV j⟩})
    (hsomeColim :
      ∀ i,
        IsColimit
          (open_subtype_wide_pushout_cocone X
            (wedge_star_cover X V hxV (some i))
            (@wedge_star_some_family ι X (Classical.decEq ι) V i)
            (wedge_star_cover_head_pullback X V hxV (some i))
            (fun j ↦ by
              classical
              by_cases hji : j = i
              · subst j
                convert wedge_star_cover_some_same_pullback X V hxV i using 1
                simp [wedge_star_some_family]
              · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
                simp [wedge_star_some_family, hji])))
    (i : ι) :
    fundamentalGroupFunctor.map (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
        fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) =
      𝟙 _ := by
  have hleft_rel :
      basedHomotopyRel
        (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i) ≫
          wedge_star_cover_some_same_under_hom X V hxV i)
        (𝟙 (wedge_star_cover_member_based_space X V hxV (some i))) := by
    -- The deformation retraction already supplies the needed based homotopy.
    refine ⟨?_⟩
    simpa [wedge_star_cover_member_based_space] using
      wedge_star_member_backward_forward_homotopy_rel X V hxV hbase i (hsomeColim i)
  -- Homotopy invariance turns that deformation retraction into the identity on `π₁`.
  simpa [Functor.map_comp] using
    (fundamentalGroupFunctor_map_eq_of_based_homotopy hleft_rel)

/-- Helper for Proposition 2.8.1: the free-product comparison sends the `i`-th coproduct generator
to the fundamental-group map induced by the coproduct inclusion `Sigma.ι X i`. -/
private theorem wedge_star_generator_comp_comparison
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (i : ι) :
    GrpCat.ofHom
        (Monoid.CoprodI.of
          (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
          (i := i)) ≫
      GrpCat.ofHom (wedge_fundamental_group_comparison X) =
        fundamentalGroupFunctor.map (Sigma.ι X i) := by
  -- This is the defining universal property of the coproduct map `wedge_fundamental_group_comparison`.
  ext g
  rfl

/-- Helper for Proposition 2.8.1: the ambient inclusion of any star-cover member induces exactly
the corresponding leg of the van Kampen cocone. -/
private theorem wedge_star_cover_member_inclusion_under_hom_fundamental_group_map_eq_cover_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (o : TopologicalSpace.IsOpenCover.Index (wedge_star_cover X V hxV)) :
    fundamentalGroupFunctor.map (wedge_star_cover_member_inclusion_under_hom X V hxV o) =
      (fundamental_group_cover_cocone
        (wedge_star_cover X V hxV)
        (underTopBasepoint (∐ X))
        (wedge_star_cover_basepoint_mem X V hxV)).ι.app o := by
  -- Both legs are induced by the same literal subtype inclusion of the star member into the wedge.
  ext g
  induction g using Path.Homotopic.Quotient.ind with
  | mk γ =>
      rfl

/-- Helper for Proposition 2.8.1: the star-cover legs to the free product are natural along the
actual open-cover diagram. -/
private theorem wedge_star_cover_to_coprod_cocone_naturality
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hbase : ∀ j,
      (ContinuousMap.id (V j)).HomotopicRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        {⟨underTopBasepoint (X j), hxV j⟩})
    (hnoneSubsingleton :
      Subsingleton
        (FundamentalGroup (wedge_star_cover X V hxV none)
          (wedge_star_cover_basepoint X V hxV none)))
    (hsomeColim :
      ∀ i,
        IsColimit
          (open_subtype_wide_pushout_cocone X
            (wedge_star_cover X V hxV (some i))
            (@wedge_star_some_family ι X (Classical.decEq ι) V i)
            (wedge_star_cover_head_pullback X V hxV (some i))
            (fun j ↦ by
              classical
              by_cases hji : j = i
              · subst j
                convert wedge_star_cover_some_same_pullback X V hxV i using 1
                simp [wedge_star_some_family]
              · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
                simp [wedge_star_some_family, hji])))
    {a b : TopologicalSpace.IsOpenCover.Index (wedge_star_cover X V hxV)}
    (f : a ⟶ b) :
    ((fundamental_group_cover_diagram
          (wedge_star_cover X V hxV)
          (underTopBasepoint (∐ X))
          (wedge_star_cover_basepoint_mem X V hxV)).map f) ≫
        wedge_star_cover_to_coprod_leg X V hxV hbase hnoneSubsingleton hsomeColim b =
      wedge_star_cover_to_coprod_leg X V hxV hbase hnoneSubsingleton hsomeColim a := by
  -- Split the actual cover morphism into the four concrete `Option`-indexed cases.
  change Option ι at a b
  cases a with
  | none =>
      cases b with
      | none =>
          let _ :
              Subsingleton
                ((fundamental_group_cover_diagram
                    (wedge_star_cover X V hxV)
                    (underTopBasepoint (∐ X))
                    (wedge_star_cover_basepoint_mem X V hxV)).obj none) := by
            simpa [wedge_star_cover_member_based_space] using hnoneSubsingleton
          -- Every map out of the common core is unique because that source group is trivial.
          ext x
          have hx : x = 1 := Subsingleton.elim _ _
          rw [hx, map_one, map_one]
      | some j =>
          let _ :
              Subsingleton
                ((fundamental_group_cover_diagram
                    (wedge_star_cover X V hxV)
                    (underTopBasepoint (∐ X))
                    (wedge_star_cover_basepoint_mem X V hxV)).obj none) := by
            simpa [wedge_star_cover_member_based_space] using hnoneSubsingleton
          -- The `none` source stays trivial regardless of which star member it maps into.
          ext x
          have hx : x = 1 := Subsingleton.elim _ _
          rw [hx, map_one, map_one]
  | some i =>
      cases b with
      | none =>
          let _ :
              Subsingleton
                ((fundamental_group_cover_diagram
                    (wedge_star_cover X V hxV)
                    (underTopBasepoint (∐ X))
                    (wedge_star_cover_basepoint_mem X V hxV)).obj (some i)) := by
            simpa [wedge_star_cover_member_based_space] using
              wedge_star_member_fundamental_group_subsingleton_of_hom_to_other
                X V hxV hnoneSubsingleton i rfl f (by simp)
          -- Any morphism from `some i` to `none` forces the source group to collapse.
          ext x
          have hx : x = 1 := Subsingleton.elim _ _
          rw [hx, map_one, map_one]
      | some j =>
          by_cases hij : i = j
          · subst hij
            -- On the diagonal, the only cover endomorphism is the identity.
            rw [wedge_star_cover_diagram_map_some_same_eq_id X V hxV i f]
            simp [wedge_star_cover_to_coprod_leg]
          · let _ :
                Subsingleton
                  ((fundamental_group_cover_diagram
                      (wedge_star_cover X V hxV)
                      (underTopBasepoint (∐ X))
                      (wedge_star_cover_basepoint_mem X V hxV)).obj (some i)) := by
              simpa [wedge_star_cover_member_based_space] using
                wedge_star_member_fundamental_group_subsingleton_of_hom_to_other
                  X V hxV hnoneSubsingleton i rfl f (by
                    intro h
                    apply hij
                    cases h
                    rfl)
            -- Off the diagonal, the source star-member group is again trivial.
            ext x
            have hx : x = 1 := Subsingleton.elim _ _
            rw [hx, map_one, map_one]

/-- Helper for Proposition 2.8.1: the star-cover cocone landing in the free product of the
summand fundamental groups. -/
private noncomputable def wedge_star_cover_to_coprod_cocone
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hbase : ∀ j,
      (ContinuousMap.id (V j)).HomotopicRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        {⟨underTopBasepoint (X j), hxV j⟩})
    (hnoneSubsingleton :
      Subsingleton
        (FundamentalGroup (wedge_star_cover X V hxV none)
          (wedge_star_cover_basepoint X V hxV none)))
    (hsomeColim :
      ∀ i,
        IsColimit
          (open_subtype_wide_pushout_cocone X
            (wedge_star_cover X V hxV (some i))
            (@wedge_star_some_family ι X (Classical.decEq ι) V i)
            (wedge_star_cover_head_pullback X V hxV (some i))
            (fun j ↦ by
              classical
              by_cases hji : j = i
              · subst j
                convert wedge_star_cover_some_same_pullback X V hxV i using 1
                simp [wedge_star_some_family]
              · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
                simp [wedge_star_some_family, hji]))) :
    Cocone
      (fundamental_group_cover_diagram
        (wedge_star_cover X V hxV)
        (underTopBasepoint (∐ X))
        (wedge_star_cover_basepoint_mem X V hxV)) :=
  { pt := GrpCat.of (Monoid.CoprodI (fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j))))
    ι :=
      { app := wedge_star_cover_to_coprod_leg X V hxV hbase hnoneSubsingleton hsomeColim
        naturality := fun _ _ f ↦
          wedge_star_cover_to_coprod_cocone_naturality
            X V hxV hbase hnoneSubsingleton hsomeColim f } }

/-- Helper for Proposition 2.8.1: the `some i` leg of the free-product cocone followed by the
canonical comparison map is the literal ambient cover-inclusion map. -/
private theorem wedge_star_some_leg_comp_comparison_eq_cover_leg
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    (V : ∀ j, TopologicalSpace.Opens (X j).right)
    (hxV : ∀ j, underTopBasepoint (X j) ∈ V j)
    (hbase : ∀ j,
      (ContinuousMap.id (V j)).HomotopicRel
        (ContinuousMap.const (V j) ⟨underTopBasepoint (X j), hxV j⟩)
        {⟨underTopBasepoint (X j), hxV j⟩})
    (hsomeColim :
      ∀ i,
        IsColimit
          (open_subtype_wide_pushout_cocone X
            (wedge_star_cover X V hxV (some i))
            (@wedge_star_some_family ι X (Classical.decEq ι) V i)
            (wedge_star_cover_head_pullback X V hxV (some i))
            (fun j ↦ by
              classical
              by_cases hji : j = i
              · subst j
                convert wedge_star_cover_some_same_pullback X V hxV i using 1
                simp [wedge_star_some_family]
              · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
                simp [wedge_star_some_family, hji])))
    (i : ι) :
    wedge_star_cover_to_coprod_some_leg X V hxV hbase hsomeColim i ≫
        GrpCat.ofHom (wedge_fundamental_group_comparison X) =
      (fundamental_group_cover_cocone
        (wedge_star_cover X V hxV)
        (underTopBasepoint (∐ X))
        (wedge_star_cover_basepoint_mem X V hxV)).ι.app (some i) := by
  have hSigma :
      fundamentalGroupFunctor.map (Sigma.ι X i) =
        fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
          fundamentalGroupFunctor.map
            (wedge_star_cover_member_inclusion_under_hom X V hxV (some i)) := by
    -- The ambient coproduct leg factors through the centered branch and the star-member inclusion.
    simpa [Functor.map_comp] using
      (congrArg fundamentalGroupFunctor.map
        (wedge_star_cover_some_same_under_hom_comp_member_inclusion X V hxV i)).symm
  have hrewrite :
      fundamentalGroupFunctor.map
          (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
        fundamentalGroupFunctor.map (Sigma.ι X i) =
      fundamentalGroupFunctor.map
          (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
        (fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
          fundamentalGroupFunctor.map
            (wedge_star_cover_member_inclusion_under_hom X V hxV (some i))) := by
    -- Reassociating after the summand-factorization keeps the comparison calculation flat.
    simpa [Category.assoc] using
      congrArg
        (fun m ↦
          fundamentalGroupFunctor.map
              (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫ m)
        hSigma
  -- Rewrite the generator through the comparison map, then factor the summand inclusion through
  -- the centered branch and the public cover-member inclusion.
  have hstep₁ :
      wedge_star_cover_to_coprod_some_leg X V hxV hbase hsomeColim i ≫
          GrpCat.ofHom (wedge_fundamental_group_comparison X) =
        fundamentalGroupFunctor.map
            (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
          fundamentalGroupFunctor.map (Sigma.ι X i) := by
    simpa [wedge_star_cover_to_coprod_some_leg, Category.assoc] using
      congrArg
        (fun m ↦
          fundamentalGroupFunctor.map
              (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫ m)
        (wedge_star_generator_comp_comparison X i)
  have hstep₂ :
      fundamentalGroupFunctor.map
          (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
        fundamentalGroupFunctor.map (Sigma.ι X i) =
      fundamentalGroupFunctor.map
          (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
        (fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
          fundamentalGroupFunctor.map
            (wedge_star_cover_member_inclusion_under_hom X V hxV (some i))) := hrewrite
  have hstep₃ :
      fundamentalGroupFunctor.map
          (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
        (fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
          fundamentalGroupFunctor.map
            (wedge_star_cover_member_inclusion_under_hom X V hxV (some i))) =
      (fundamentalGroupFunctor.map
          (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
        fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i)) ≫
          fundamentalGroupFunctor.map
            (wedge_star_cover_member_inclusion_under_hom X V hxV (some i)) := by
    simp [Category.assoc]
  have hstep₄ :
      (fundamentalGroupFunctor.map
          (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
        fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i)) ≫
          fundamentalGroupFunctor.map
            (wedge_star_cover_member_inclusion_under_hom X V hxV (some i)) =
        fundamentalGroupFunctor.map
          (wedge_star_cover_member_inclusion_under_hom X V hxV (some i)) := by
    rw [wedge_star_member_forward_then_same_fundamental_group_eq_id X V hxV hbase hsomeColim i]
    simp
  have hstep₅ :
      fundamentalGroupFunctor.map
          (wedge_star_cover_member_inclusion_under_hom X V hxV (some i)) =
        (fundamental_group_cover_cocone
          (wedge_star_cover X V hxV)
          (underTopBasepoint (∐ X))
          (wedge_star_cover_basepoint_mem X V hxV)).ι.app (some i) :=
    wedge_star_cover_member_inclusion_under_hom_fundamental_group_map_eq_cover_leg X V hxV (some i)
  exact hstep₁.trans (hstep₂.trans (hstep₃.trans (hstep₄.trans hstep₅)))

/-- Proposition 2.8.1: if `X i` is a path-connected family of based spaces and each `X i` has a
contractible neighborhood that contracts to its chosen basepoint, then the canonical homomorphism
from the free product of the groups `π₁(X i)` to the fundamental group of the wedge sum `∐ X` is an
isomorphism. -/
-- Proof sketch: cover the wedge sum `∐ X` by the open subsets obtained by taking one full summand
-- `X i` together with the chosen contractible basepoint neighborhoods in the other summands.
-- Theorem 2.7.5 identifies the fundamental group of the wedge with the colimit of the resulting
-- diagram of groups. The based contractions collapse every nontrivial multiple intersection to
-- the glued basepoint, so only the vertex groups of the individual summands contribute to the
-- colimit, which is the indexed free product `Monoid.CoprodI`.
theorem wedge_fundamental_group_is_free_product
    (X : ι → Under (⊤_ TopCat)) [HasCoproduct X]
    [∀ i, PathConnectedSpace (X i).right]
    (hV : ∀ i, has_contractible_base_neighborhood (X i)) :
    IsIso (GrpCat.ofHom (wedge_fundamental_group_comparison X)) := by
  classical
  choose V hxV hVdata using hV
  let hcontractible : ∀ i, ContractibleSpace (V i) := fun i ↦ (hVdata i).1
  let hbase :
      ∀ i,
        (ContinuousMap.id (V i)).HomotopicRel
          (ContinuousMap.const (V i) ⟨underTopBasepoint (X i), hxV i⟩)
          {⟨underTopBasepoint (X i), hxV i⟩} := fun i ↦ (hVdata i).2
  let hVpath : ∀ i, PathConnectedSpace (V i) := fun i ↦ by
    let _ : ContractibleSpace (V i) := hcontractible i
    infer_instance
  let hnoneColim :
      IsColimit
        (open_subtype_wide_pushout_cocone X
          (wedge_star_cover X V hxV none)
          V
          (wedge_star_cover_head_pullback X V hxV none)
          (wedge_star_cover_none_pullback X V hxV)) :=
    open_subtype_wide_pushout_is_colimit X
      (wedge_star_cover X V hxV none)
      V
      (wedge_star_cover_head_pullback X V hxV none)
      (wedge_star_cover_none_pullback X V hxV)
  let hsomeColim :
      ∀ i,
        IsColimit
          (open_subtype_wide_pushout_cocone X
            (wedge_star_cover X V hxV (some i))
            (@wedge_star_some_family ι X (Classical.decEq ι) V i)
            (wedge_star_cover_head_pullback X V hxV (some i))
            (fun j ↦ by
              classical
              by_cases hji : j = i
              · subst j
                convert wedge_star_cover_some_same_pullback X V hxV i using 1
                simp [wedge_star_some_family]
              · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
                simp [wedge_star_some_family, hji])) := fun i ↦
      open_subtype_wide_pushout_is_colimit X
        (wedge_star_cover X V hxV (some i))
        (@wedge_star_some_family ι X (Classical.decEq ι) V i)
        (wedge_star_cover_head_pullback X V hxV (some i))
        (fun j ↦ by
          classical
          by_cases hji : j = i
          · subst j
            convert wedge_star_cover_some_same_pullback X V hxV i using 1
            simp [wedge_star_some_family]
          · convert wedge_star_cover_some_ne_pullback X V hxV hji using 1
            simp [wedge_star_some_family, hji])
  let hnoneSubsingleton :
      Subsingleton
        (FundamentalGroup (wedge_star_cover X V hxV none)
          (wedge_star_cover_basepoint X V hxV none)) :=
    wedge_common_core_fundamental_group_subsingleton X V hxV hbase hnoneColim
  let S :=
    wedge_star_cover_to_coprod_cocone X V hxV hbase hnoneSubsingleton hsomeColim
  let hcolim :=
    fundamental_group_is_colimit_of_path_connected_open_cover
      (wedge_star_cover X V hxV)
      (wedge_star_cover_isOpenCover X V hxV)
      (underTopBasepoint (∐ X))
      (wedge_star_cover_basepoint_mem X V hxV)
      (wedge_star_cover_path_connected X V hxV hVpath)
      (wedge_star_cover_closed_under_nonempty_finite_intersections X V hxV)
  let δ := hcolim.desc S
  refine ⟨⟨δ, ?_, ?_⟩⟩
  · -- Check the left inverse on the free-product generators.
    ext i g
    have hcover :
        GrpCat.ofHom
            (Monoid.CoprodI.of
              (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
              (i := i)) ≫
          GrpCat.ofHom (wedge_fundamental_group_comparison X) =
            fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
              (fundamental_group_cover_cocone
                (wedge_star_cover X V hxV)
                (underTopBasepoint (∐ X))
                (wedge_star_cover_basepoint_mem X V hxV)).ι.app (some i) := by
      -- Reexpress the generator through the centered branch and the actual cover inclusion.
      have hcover₁ :
          GrpCat.ofHom
              (Monoid.CoprodI.of
                (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
                (i := i)) ≫
            GrpCat.ofHom (wedge_fundamental_group_comparison X) =
          fundamentalGroupFunctor.map (Sigma.ι X i) := by
        rw [wedge_star_generator_comp_comparison]
      have hcover₂ :
          fundamentalGroupFunctor.map (Sigma.ι X i) =
            fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
              fundamentalGroupFunctor.map
                (wedge_star_cover_member_inclusion_under_hom X V hxV (some i)) := by
        simpa [Functor.map_comp] using
          (congrArg fundamentalGroupFunctor.map
            (wedge_star_cover_some_same_under_hom_comp_member_inclusion X V hxV i)).symm
      have hcover₃ :
          fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
              fundamentalGroupFunctor.map
                (wedge_star_cover_member_inclusion_under_hom X V hxV (some i)) =
            fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
              (fundamental_group_cover_cocone
                (wedge_star_cover X V hxV)
                (underTopBasepoint (∐ X))
                (wedge_star_cover_basepoint_mem X V hxV)).ι.app (some i) := by
        simpa [Category.assoc] using
          congrArg
            (fun m ↦ fundamentalGroupFunctor.map
                (wedge_star_cover_some_same_under_hom X V hxV i) ≫ m)
            (wedge_star_cover_member_inclusion_under_hom_fundamental_group_map_eq_cover_leg
              X V hxV (some i))
      exact hcover₁.trans (hcover₂.trans hcover₃)
    have hfac :=
      fundamental_group_is_colimit_of_path_connected_open_cover_desc_fac
        (wedge_star_cover X V hxV)
        (wedge_star_cover_isOpenCover X V hxV)
        (underTopBasepoint (∐ X))
        (wedge_star_cover_basepoint_mem X V hxV)
        (wedge_star_cover_path_connected X V hxV hVpath)
        (wedge_star_cover_closed_under_nonempty_finite_intersections X V hxV)
        S (some i)
    have hretract :
        fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
            wedge_star_cover_to_coprod_some_leg X V hxV hbase hsomeColim i =
          GrpCat.ofHom
            (Monoid.CoprodI.of
              (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
              (i := i)) := by
      have hsame_forward :
          fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
              fundamentalGroupFunctor.map
                (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) =
            𝟙 _ := by
        -- The centered branch inclusion is literally inverse to the forward retraction.
        simpa [Functor.map_comp] using
          congrArg fundamentalGroupFunctor.map
            (wedge_star_cover_some_same_under_hom_comp_forward_under_hom_eq_id
              X V hxV i (hsomeColim i))
      calc
        fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
            wedge_star_cover_to_coprod_some_leg X V hxV hbase hsomeColim i =
          (fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
              fundamentalGroupFunctor.map
                (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i))) ≫
            GrpCat.ofHom
              (Monoid.CoprodI.of
                (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
                (i := i)) := by
              change
                fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
                    (fundamentalGroupFunctor.map
                      (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i)) ≫
                      GrpCat.ofHom
                        (Monoid.CoprodI.of
                          (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
                          (i := i))) =
                  (fundamentalGroupFunctor.map
                      (wedge_star_cover_some_same_under_hom X V hxV i) ≫
                    fundamentalGroupFunctor.map
                      (wedge_star_member_forward_under_hom X V hxV i (hsomeColim i))) ≫
                    GrpCat.ofHom
                      (Monoid.CoprodI.of
                        (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
                        (i := i))
              simp [Category.assoc]
        _ =
          GrpCat.ofHom
            (Monoid.CoprodI.of
              (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
              (i := i)) := by
              simp [hsame_forward]
    -- Precompose the descent equation with the centered branch inclusion.
    have hgenerator :
        GrpCat.ofHom
            (Monoid.CoprodI.of
              (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
              (i := i)) ≫
          GrpCat.ofHom (wedge_fundamental_group_comparison X) ≫
            δ =
        GrpCat.ofHom
          (Monoid.CoprodI.of
            (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
            (i := i)) := by
      have hgenerator₁ :
          GrpCat.ofHom
              (Monoid.CoprodI.of
                (M := fun j ↦ FundamentalGroup (X j).right (underTopBasepoint (X j)))
                (i := i)) ≫
            GrpCat.ofHom (wedge_fundamental_group_comparison X) ≫
              δ =
            (fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
                (fundamental_group_cover_cocone
                  (wedge_star_cover X V hxV)
                  (underTopBasepoint (∐ X))
                  (wedge_star_cover_basepoint_mem X V hxV)).ι.app (some i)) ≫
                δ := by
        simpa [Category.assoc] using congrArg (fun m ↦ m ≫ δ) hcover
      have hgenerator₂ :
          (fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
              (fundamental_group_cover_cocone
                (wedge_star_cover X V hxV)
                (underTopBasepoint (∐ X))
                (wedge_star_cover_basepoint_mem X V hxV)).ι.app (some i)) ≫
                δ =
            fundamentalGroupFunctor.map (wedge_star_cover_some_same_under_hom X V hxV i) ≫
              wedge_star_cover_to_coprod_some_leg X V hxV hbase hsomeColim i := by
        simpa [Category.assoc] using
          congrArg
            (fun m ↦ fundamentalGroupFunctor.map
                (wedge_star_cover_some_same_under_hom X V hxV i) ≫ m)
            hfac
      exact hgenerator₁.trans (hgenerator₂.trans hretract)
    simpa [Category.assoc] using congrArg (fun m ↦ m.hom g) hgenerator
  · -- Check the right inverse on the actual cover vertices and descend by the colimit property.
    apply hcolim.hom_ext
    intro o
    cases o with
    | none =>
        have hfac :=
          fundamental_group_is_colimit_of_path_connected_open_cover_desc_fac
            (wedge_star_cover X V hxV)
            (wedge_star_cover_isOpenCover X V hxV)
            (underTopBasepoint (∐ X))
            (wedge_star_cover_basepoint_mem X V hxV)
            (wedge_star_cover_path_connected X V hxV hVpath)
            (wedge_star_cover_closed_under_nonempty_finite_intersections X V hxV)
            S none
        have hfac_comp :=
          congrArg (fun m ↦ m ≫ GrpCat.ofHom (wedge_fundamental_group_comparison X)) hfac
        let _ :
            Subsingleton
              ((fundamental_group_cover_diagram
                  (wedge_star_cover X V hxV)
                  (underTopBasepoint (∐ X))
                  (wedge_star_cover_basepoint_mem X V hxV)).obj none) := by
          simpa [wedge_star_cover_member_based_space] using hnoneSubsingleton
        -- The `none` source group is trivial, so the remaining comparison is unique.
        calc
          (fundamental_group_cover_cocone
              (wedge_star_cover X V hxV)
              (underTopBasepoint (∐ X))
              (wedge_star_cover_basepoint_mem X V hxV)).ι.app none ≫
              δ ≫ GrpCat.ofHom (wedge_fundamental_group_comparison X) =
            S.ι.app none ≫ GrpCat.ofHom (wedge_fundamental_group_comparison X) := by
              simpa [Category.assoc] using hfac_comp
          _ =
            (fundamental_group_cover_cocone
              (wedge_star_cover X V hxV)
              (underTopBasepoint (∐ X))
              (wedge_star_cover_basepoint_mem X V hxV)).ι.app none := by
              ext x
              have hx : x = 1 := Subsingleton.elim _ _
              rw [hx, map_one, map_one]
    | some i =>
        have hfac :=
          fundamental_group_is_colimit_of_path_connected_open_cover_desc_fac
            (wedge_star_cover X V hxV)
            (wedge_star_cover_isOpenCover X V hxV)
            (underTopBasepoint (∐ X))
            (wedge_star_cover_basepoint_mem X V hxV)
            (wedge_star_cover_path_connected X V hxV hVpath)
            (wedge_star_cover_closed_under_nonempty_finite_intersections X V hxV)
            S (some i)
        have hfac_comp :=
          congrArg (fun m ↦ m ≫ GrpCat.ofHom (wedge_fundamental_group_comparison X)) hfac
        -- The `some i` branch is exactly the normalized comparison identity proved above.
        calc
          (fundamental_group_cover_cocone
              (wedge_star_cover X V hxV)
              (underTopBasepoint (∐ X))
              (wedge_star_cover_basepoint_mem X V hxV)).ι.app (some i) ≫
              δ ≫ GrpCat.ofHom (wedge_fundamental_group_comparison X) =
            S.ι.app (some i) ≫ GrpCat.ofHom (wedge_fundamental_group_comparison X) := by
              simpa [Category.assoc] using hfac_comp
          _ =
            (fundamental_group_cover_cocone
              (wedge_star_cover X V hxV)
              (underTopBasepoint (∐ X))
              (wedge_star_cover_basepoint_mem X V hxV)).ι.app (some i) := by
              simpa [S, wedge_star_cover_to_coprod_cocone] using
                wedge_star_some_leg_comp_comparison_eq_cover_leg X V hxV hbase hsomeColim i
