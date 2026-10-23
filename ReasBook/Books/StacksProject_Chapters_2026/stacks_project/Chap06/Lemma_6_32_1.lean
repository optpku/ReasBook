module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.ClosedSubsetInclusion
public import stacks_project.Chap06.Definition_6_15_1
public import stacks_project.Chap06.Lemma_6_13_1
public import stacks_project.Chap06.Lemma_6_15_2
public import stacks_project.Chap06.Lemma_6_21_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open CategoryTheory.Functor
open CategoryTheory.Functor.sheafPullbackConstruction
open TopCat.Presheaf.stalkPushforward

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe u v w

section

variable {X : TopCat.{u}}
variable {Z : Set X}

local notation "sZ" => X.subsetInclusion Z
local notation "iZ" => X.closedSubsetInclusion Z

/- Domain-style sampling for Lemma 6.32.1:
- primary domain: sheaf pushforward/pullback and stalk comparison for the inclusion of a closed
  subset in `TopCat`;
- sampled owner declarations:
  `TopCat.subsetInclusion`,
  `TopCat.closedSubsetInclusion`,
  `IsAlgebraicStructure`,
  `stalkPushforward_iso_of_isInducing`,
  `Sheaf.pullbackPushforwardAdjunction`,
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`;
- owner abstraction: the ambient owner is the subset inclusion morphism
  `TopCat.subsetInclusion X Z`; the closed-subset inclusion
  `TopCat.closedSubsetInclusion X Z` is only the source-facing bridge for the clauses that use
  closedness to describe stalks outside `Z`; the coefficient-side owner is the chapter predicate
  `IsAlgebraicStructure C F` for algebraic-structure-valued clauses and the canonical stalk and
  adjunction APIs attached to a map of spaces;
- primitive data: only the subset `Z : Set X`, its inclusion into `X`, and the coefficient pair
  `(C, F)` when a clause is stated for algebraic structures;
- derived API: the stalk comparison, the counit isomorphisms, and the terminal/zero stalk
  consequences outside `Z`, obtained from those owners.

Source/core/bridge triage:
- `source-facing`: the Stacks-project assertions about pushforward from a closed subset and the
  resulting stalk/counit behavior;
- `core/canonical`: the mathlib stalk-pushforward and pullback-pushforward-adjunction owners for a
  map of spaces;
- `bridge/view`: the specialization of those owners to the closed-subset inclusion. -/

/-- Helper for Lemma 6.32.1: if an ambient open set is disjoint from `Z`, then its pullback along
the subset inclusion is the empty open of `Z`. -/
private theorem subsetInclusion_obj_eq_bot_of_disjoint {U : Opens X}
    (hU : (U : Set X) ⊆ Zᶜ) :
    (Opens.map iZ).obj U = ⊥ := by
  -- A point of the pulled-back open would lie both in `U` and in `Z`, contradicting disjointness.
  ext z
  constructor
  · intro hz
    exact False.elim (hU hz z.2)
  · intro hz
    exact False.elim hz

/-- Helper for Lemma 6.32.1: over any ambient open disjoint from `Z`, the pushforward sheaf of
sets evaluates to a singleton. -/
private noncomputable def closedSubsetTypeSheaf_pushforward_obj_isTerminal_of_disjoint
    (ℱ : TopCat.Sheaf (Type u) (TopCat.of Z)) {U : Opens X} (hU : (U : Set X) ⊆ Zᶜ) :
    IsTerminal ((((Sheaf.pushforward (Type u) iZ).obj ℱ).presheaf).obj (op U)) := by
  -- Rewrite the pulled-back open to `⊥`, where a sheaf has terminal sections.
  change IsTerminal (ℱ.presheaf.obj (op ((Opens.map iZ).obj U)))
  simpa [subsetInclusion_obj_eq_bot_of_disjoint (X := X) (Z := Z) hU] using
    ℱ.isTerminalOfEqEmpty (subsetInclusion_obj_eq_bot_of_disjoint (X := X) (Z := Z) hU)

/-- Helper for Lemma 6.32.1: over any ambient open disjoint from `Z`, the pushforward sheaf of
sets has a unique section. -/
private noncomputable abbrev closedSubsetTypeSheaf_pushforward_obj_unique_of_disjoint
    (ℱ : TopCat.Sheaf (Type u) (TopCat.of Z)) {U : Opens X} (hU : (U : Set X) ⊆ Zᶜ) :
    Unique ((((Sheaf.pushforward (Type u) iZ).obj ℱ).presheaf).obj (op U)) :=
  CategoryTheory.Limits.Types.isTerminalEquivUnique _
    (closedSubsetTypeSheaf_pushforward_obj_isTerminal_of_disjoint (X := X) (Z := Z) ℱ hU)

local instance preservesLimits_forgetType_6_32_1 :
    PreservesLimits (forget (Type u)) :=
  CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeHom

local instance preservesFilteredColimits_forgetType_6_32_1 :
    PreservesFilteredColimits (forget (Type u)) := by
  letI : PreservesColimits (forget (Type u)) :=
    CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeHom
  exact PreservesColimits.preservesFilteredColimits (forget (Type u))

local instance reflectsIsos_forgetType_6_32_1 :
    (forget (Type u)).ReflectsIsomorphisms :=
  CategoryTheory.instReflectsIsomorphismsForgetTypeHom

local instance faithful_forgetType_6_32_1 :
    (forget (Type u)).Faithful := inferInstance

local instance : IsAlgebraicStructure (Type u) (forget (Type u)) where

-- Proof sketch: because `Z` is closed, every point `x ∉ Z` has an open neighbourhood disjoint
-- from `Z`; on that neighbourhood the pushforward sheaf is evaluating the original sheaf on the
-- empty open, whose sections form a singleton.
/-- Consequence of Lemma 6.32.1 (1): if `x ∉ Z`, then the stalk of the pushforward of a sheaf of sets on the
closed subset `Z` is canonically a singleton; equivalently, its map to the terminal set is an
isomorphism. -/
theorem closedSubsetTypeSheaf_pushforward_stalk_unique_of_not_mem
    (hZ : IsClosed Z) (ℱ : TopCat.Sheaf (Type u) (TopCat.of Z))
    {x : X} (hx : x ∉ Z) :
    IsIso
      (terminal.from
        (((Sheaf.pushforward (Type u)
            iZ).obj
          ℱ).presheaf.stalk x)) := by
  let ℱ' := ((Sheaf.pushforward (Type u) iZ).obj ℱ).presheaf
  let U₀ : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hxU₀ : x ∈ U₀ := hx
  let hU₀ :
      Unique (ℱ'.obj (op U₀)) :=
    closedSubsetTypeSheaf_pushforward_obj_unique_of_disjoint (X := X) (Z := Z) ℱ
      (by
        intro y hy
        show y ∈ Zᶜ
        exact hy)
  -- It suffices to show that the stalk is a singleton type.
  rw [CategoryTheory.isIso_iff_bijective]
  constructor
  · intro s t hst
    rcases ℱ'.germ_exist x s with ⟨U₁, hxU₁, s₁, rfl⟩
    rcases ℱ'.germ_exist x t with ⟨U₂, hxU₂, t₂, rfl⟩
    let W : Opens X := U₀ ⊓ U₁ ⊓ U₂
    have hxW : x ∈ W := by
      exact ⟨⟨hxU₀, hxU₁⟩, hxU₂⟩
    have hWdisjoint : (W : Set X) ⊆ Zᶜ := by
      intro y hy
      show y ∈ Zᶜ
      exact hy.1.1
    let hW :
        Unique (ℱ'.obj (op W)) :=
      closedSubsetTypeSheaf_pushforward_obj_unique_of_disjoint (X := X) (Z := Z) ℱ hWdisjoint
    let iWU₁ : W ⟶ U₁ := homOfLE (by intro y hy; exact hy.1.2)
    let iWU₂ : W ⟶ U₂ := homOfLE (by intro y hy; exact hy.2)
    have hrestr :
        ℱ'.map iWU₁.op s₁ = ℱ'.map iWU₂.op t₂ := by
      letI := hW
      exact Subsingleton.elim _ _
    -- Restrict both germs to the common disjoint neighbourhood `W`, where every section is equal.
    calc
      ℱ'.germ U₁ x hxU₁ s₁
          = ℱ'.germ W x hxW (ℱ'.map iWU₁.op s₁) := by
              symm
              simpa [iWU₁, W] using ℱ'.germ_res_apply iWU₁ x hxW s₁
      _ = ℱ'.germ W x hxW (ℱ'.map iWU₂.op t₂) := by rw [hrestr]
      _ = ℱ'.germ U₂ x hxU₂ t₂ := by
            simpa [iWU₂, W] using ℱ'.germ_res_apply iWU₂ x hxW t₂
  · intro b
    letI := hU₀
    refine ⟨ℱ'.germ U₀ x hxU₀ default, ?_⟩
    exact Subsingleton.elim _ _

-- Proof sketch: the subtype inclusion `Z ↪ X` is inducing, so the canonical map on stalks for
-- pushforward along the inclusion is an isomorphism by the standard `stalkPushforward` result.
section

variable {C : Type v} [Category.{u} C] [HasColimits.{u} C]
variable (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z)

/- Core/canonical recall: for the inclusion `Z ↪ X`, the stalk comparison is the direct
specialization of `stalkPushforward_iso_of_isInducing`. -/
/-- Helper for Lemma 6.32.1: at a point of `Z`, the stalk of the pushforward along the subset
inclusion is canonically the original stalk. -/
private noncomputable def subsetSheaf_pushforward_stalkIsoAtPoint :
    (((Sheaf.pushforward C sZ).obj ℱ).presheaf.stalk (sZ z)) ≅ ℱ.presheaf.stalk z := by
  letI : IsIso (ℱ.presheaf.stalkPushforward C iZ z) :=
    stalkPushforward_iso_of_isInducing C Topology.IsInducing.subtypeVal ℱ.presheaf z
  simpa [TopCat.closedSubsetInclusion, TopCat.subsetInclusion] using
    (asIso (ℱ.presheaf.stalkPushforward C iZ z))

#check
  (stalkPushforward_iso_of_isInducing
    C Topology.IsInducing.subtypeVal ℱ.presheaf z :
      IsIso (ℱ.presheaf.stalkPushforward C iZ z))

end

section

variable {A : Type v} [Category.{u} A] {FA : A → A → Type u} {CA : A → Type u}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- Helper for Lemma 6.32.1: the stalk functor sends a germ through the sheafification unit to the
corresponding sheafified germ. -/
private theorem toSheafify_stalk_map_germ_apply {Y : TopCat.{u}}
    (ℱ : Y.Presheaf (Type u)) (W : Opens Y) (y : Y) (hy : y ∈ W)
    (t : ℱ.obj (op W)) :
    ((TopCat.Presheaf.stalkFunctor (Type u) y).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) ℱ))
      (ℱ.germ W y hy t) =
      (TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology Y) ℱ) W y hy)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y) ℱ).app (op W) t) := by
  -- This is the sheafification-unit specialization of `stalkFunctor_map_germ_apply`.
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) ℱ) t)

/-- Helper for Lemma 6.32.1: after applying the inverse pullback comparison on stalks, a
sheafified germ becomes the corresponding germ in the actual pullback sheaf. -/
private theorem pullbackIso_inv_stalk_map_germ_apply {Y T : TopCat.{u}}
    (f : Y ⟶ T) (𝒢 : T.Sheaf (Type u)) (W : Opens Y) (y : Y) (hy : y ∈ W)
    (t :
      (sheafify (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.forget (Type u) T ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢)).obj
          (op W)) :
    ((TopCat.Presheaf.stalkFunctor (Type u) y).map
        ((TopCat.Sheaf.forget (Type u) Y).map
          ((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢)))
      ((TopCat.Presheaf.germ
          (sheafify (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.forget (Type u) T ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢))
          W y hy) t) =
      (((f⁻¹).obj 𝒢).presheaf).germ W y hy
        ((((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢).1.app (op W)) t) := by
  -- This is the `pullbackIso.inv` specialization of `stalkFunctor_map_germ_apply`.
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy
      ((TopCat.Sheaf.forget (Type u) Y).map
        ((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢)) t)

/-- Helper for Lemma 6.32.1: on ordinary sections, the inverse component of
`TopCat.Sheaf.pullbackIso` identifies the sheafification of the presheaf pullback-unit section
with the sheaf-level pullback adjunction unit. -/
private theorem pullbackIso_inv_toSheafify_unit_section_eq {Y T : TopCat.{u}}
    (f : Y ⟶ T) (𝒢 : T.Sheaf (Type u)) (U : Opens T)
    (s : 𝒢.1.obj (op U)) :
    (((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢).1.app (op ((Opens.map f).obj U)))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget (Type u) T ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢)).app
            (op ((Opens.map f).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢.1).app
            (op U)) s)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app (op U)) s) := by
  -- Compare the abstract pullback adjunction unit with the left-Kan/sheafification pullback unit.
  have h :=
    Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
      (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) (Type u) (Opens.grothendieckTopology T) (Opens.grothendieckTopology Y))
      𝒢
  have happ :=
    congrArg
      (fun k ↦ (k.1.app (op U)) s)
      h
  have happ' :
      (((TopCat.Sheaf.pullbackIso (Type u) f).hom.app 𝒢).1.app (op ((Opens.map f).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
            (op U)) s) =
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget (Type u) T ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢)).app
            (op ((Opens.map f).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢.1).app
            (op U)) s) := by
    -- Evaluating the unit identity at `U` gives the needed section-level normalization.
    simpa using happ
  -- Apply the inverse pullback-comparison component and simplify by `hom_inv_id`.
  rw [← happ']
  simpa using
    congrArg
      (fun k ↦ (k.hom.app (op ((Opens.map f).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
            (op U)) s))
      (Iso.hom_inv_id_app (TopCat.Sheaf.pullbackIso (Type u) f) 𝒢)

/-- Helper for Lemma 6.32.1: after passing to stalks, the sheafification of the presheaf
pullback-unit germ and the inverse pullback comparison recover the genuine sheaf pullback-unit
germ. -/
private theorem pullbackIso_inv_toSheafify_unit_stalk_germ_eq {Y T : TopCat.{u}}
    (f : Y ⟶ T) (𝒢 : T.Sheaf (Type u)) (U : Opens T) (y : Y)
    (hy : y ∈ (Opens.map f).obj U) (s : 𝒢.1.obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor (Type u) y).map
        ((TopCat.Sheaf.forget (Type u) Y).map
          ((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢)))
      ((TopCat.Presheaf.germ
          (sheafify (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.forget (Type u) T ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢))
          ((Opens.map f).obj U) y hy)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.forget (Type u) T ⋙ TopCat.Presheaf.pullback (Type u) f).obj 𝒢)).app
          (op ((Opens.map f).obj U))
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢.1).app
              (op U)) s))) =
      (((f⁻¹).obj 𝒢).presheaf).germ ((Opens.map f).obj U) y hy
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
            (op U)) s) := by
  -- First compute the stalk image through `pullbackIso.inv`, then rewrite the section term.
  rw [pullbackIso_inv_stalk_map_germ_apply]
  rw [pullbackIso_inv_toSheafify_unit_section_eq]

/-- Lemma 6.32.1: on germs, the sheaf-level stalk pullback isomorphism is obtained by
first applying the presheaf stalk pullback owner, then the sheafification unit on stalks, and
finally the inverse component of `TopCat.Sheaf.pullbackIso`. -/
theorem subsetSheaf_sheafStalkPullbackGermApply
    (f : TopCat.of Z ⟶ X) (𝒢 : X.Sheaf (Type u)) (U : Opens X) (z : TopCat.of Z)
    (hz : z ∈ (Opens.map f).obj U) (s : 𝒢.1.obj (op U)) :
    ((TopCat.Sheaf.stalkPullbackIso f 𝒢 z).hom)
      (𝒢.presheaf.germ U (f z) (by simpa using hz) s) =
      (((f⁻¹).obj 𝒢).presheaf).germ ((Opens.map f).obj U) z hz
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
            (op U)) s) := by
  have hz' : f z ∈ U := by
    simpa using hz
  -- Expand the sheaf-level pullback-stalk bridge into its presheaf, sheafification, and
  -- `pullbackIso.inv` factors, then compute each factor on the chosen germ.
  rw [TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom]
  change
    ((TopCat.Presheaf.stalkFunctor (Type u) z).map
        ((TopCat.Sheaf.forget (Type u) (TopCat.of Z)).map
          ((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢)))
      (((TopCat.Presheaf.stalkFunctor (Type u) z).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
            ((TopCat.Presheaf.pullback (Type u) f).obj 𝒢.obj)))
        ((TopCat.Presheaf.stalkPullbackIso (Type u) f 𝒢.presheaf z).hom
          (𝒢.presheaf.germ U (f z) hz' s))) =
      (((f⁻¹).obj 𝒢).presheaf).germ ((Opens.map f).obj U) z hz
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).1.app
            (op U)) s)
  have hpresheaf :
      (TopCat.Presheaf.stalkPullbackIso (Type u) f 𝒢.presheaf z).hom
          (𝒢.presheaf.germ U (f z) hz' s) =
        (((TopCat.Presheaf.pullback (Type u) f).obj 𝒢.1).germ
          ((Opens.map f).obj U) z hz
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢.1).app
              (op U)) s)) := by
    -- The presheaf-level stalk pullback owner computes the first leg on the chosen germ.
    simpa [ConcreteCategory.comp_apply] using
      congrArg
        (fun k ↦ k s)
        (TopCat.Presheaf.germ_stalkPullbackHom (Type u) f 𝒢.1 z U hz)
  rw [hpresheaf]
  -- The sheafification unit moves the pullback-unit section to the corresponding sheafified germ.
  rw [toSheafify_stalk_map_germ_apply
    (ℱ := ((TopCat.Presheaf.pullback (Type u) f).obj 𝒢.obj))
    (W := (Opens.map f).obj U) (y := z) (hy := hz)
    (t := ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢.1).app
      (op U)) s))]
  -- The final `pullbackIso.inv` component identifies that sheafified germ with the true
  -- pullback-sheaf unit germ.
  exact pullbackIso_inv_toSheafify_unit_stalk_germ_eq
    (f := f) (𝒢 := 𝒢) (U := U) (y := z) (hy := hz) (s := s)

end

/-- Helper for Lemma 6.32.1: in the set-valued case, the inside-`Z` stalk map of the counit agrees
with the explicit `stalkPushforward` isomorphism. -/
private theorem subsetSheaf_type_counit_stalk_comp_eq
    (ℱ : TopCat.Sheaf (Type u) (TopCat.of Z)) (z : TopCat.of Z) :
    (TopCat.Sheaf.stalkPullbackIso sZ ((Sheaf.pushforward (Type u) sZ).obj ℱ) z).hom ≫
      ((TopCat.Presheaf.stalkFunctor (Type u) z).map
        ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ).hom) =
    (subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱ) z).hom := by
  -- Compare both maps after precomposing with germs; the left route uses the sheaf pullback-unit
  -- germ formula, while the right route is the direct `stalkPushforward` computation.
  apply TopCat.Presheaf.stalk_hom_ext (((Sheaf.pushforward (Type u) sZ).obj ℱ).presheaf)
  intro U hzU
  ext s
  have hzMap : z ∈ (Opens.map sZ).obj U := by
    simpa [TopCat.subsetInclusion] using hzU
  have hleft₁ :
      ((TopCat.Sheaf.stalkPullbackIso sZ ((Sheaf.pushforward (Type u) sZ).obj ℱ) z).hom)
          ((((Sheaf.pushforward (Type u) sZ).obj ℱ).presheaf).germ U (sZ z) hzU s) =
        ((((sZ⁻¹).obj ((Sheaf.pushforward (Type u) sZ).obj ℱ)).presheaf).germ
          ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
                ((Sheaf.pushforward (Type u) sZ).obj ℱ)).1.app (op U)) s)) := by
    -- First compute the germ through the sheaf-level pullback-stalk comparison.
    simpa using
      (subsetSheaf_sheafStalkPullbackGermApply
        (f := sZ) (𝒢 := ((Sheaf.pushforward (Type u) sZ).obj ℱ))
        (U := U) (z := z) (hz := hzMap) (s := s))
  have hsection :
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ).1.app
          (op ((Opens.map sZ).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
              ((Sheaf.pushforward (Type u) sZ).obj ℱ)).1.app (op U)) s) = s := by
    -- Evaluate the right-triangle identity on the chosen ambient section.
    change
      ((((Sheaf.pushforward (Type u) sZ).map
              ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ)).1.app
          (op U))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
              ((Sheaf.pushforward (Type u) sZ).obj ℱ)).1.app (op U)) s)) =
      (fun k ↦ (k.1.app (op U)) s) (𝟙 ((Sheaf.pushforward (Type u) sZ).obj ℱ))
    exact congrArg
      (fun k ↦ (k.1.app (op U)) s)
      ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).right_triangle_components ℱ)
  have hleft₂ := by
    -- Next move the counit stalk map back to the corresponding section-level counit map.
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply
        ((Opens.map sZ).obj U) z hzMap
        ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ).hom
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
              ((Sheaf.pushforward (Type u) sZ).obj ℱ)).1.app (op U)) s))
  have hright :
      ((subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱ) z).hom)
        ((((Sheaf.pushforward (Type u) sZ).obj ℱ).presheaf).germ U (sZ z) hzU s) =
      ℱ.presheaf.germ ((Opens.map sZ).obj U) z hzMap s := by
    -- The explicit comparison is just the usual `stalkPushforward` map on this germ.
    simpa [subsetSheaf_pushforward_stalkIsoAtPoint, ConcreteCategory.comp_apply] using
      congrArg
        (fun k ↦ k s)
        (TopCat.Presheaf.stalkPushforward_germ (Type u) sZ ℱ.presheaf U z hzMap)
  calc
    (((TopCat.Sheaf.stalkPullbackIso sZ ((Sheaf.pushforward (Type u) sZ).obj ℱ) z).hom) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) z).map
            (((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ).hom)))
        ((((Sheaf.pushforward (Type u) sZ).obj ℱ).presheaf).germ U (sZ z) hzU s)
        =
      ((TopCat.Presheaf.stalkFunctor (Type u) z).map
          (((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ).hom))
        ((((sZ⁻¹).obj ((Sheaf.pushforward (Type u) sZ).obj ℱ)).presheaf).germ
          ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
                ((Sheaf.pushforward (Type u) sZ).obj ℱ)).1.app (op U)) s)) := by
            change
              ((TopCat.Presheaf.stalkFunctor (Type u) z).map
                  (((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ).hom))
                (((TopCat.Sheaf.stalkPullbackIso sZ ((Sheaf.pushforward (Type u) sZ).obj ℱ) z).hom)
                  ((((Sheaf.pushforward (Type u) sZ).obj ℱ).presheaf).germ U (sZ z) hzU s)) =
                _
            rw [hleft₁]
    _ =
      (ℱ.presheaf.germ ((Opens.map sZ).obj U) z hzMap)
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ).1.app
            (op ((Opens.map sZ).obj U)))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
                ((Sheaf.pushforward (Type u) sZ).obj ℱ)).1.app (op U)) s)) := hleft₂
    _ = ℱ.presheaf.germ ((Opens.map sZ).obj U) z hzMap s := by
      rw [hsection]
    _ =
      ((subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱ) z).hom)
        ((((Sheaf.pushforward (Type u) sZ).obj ℱ).presheaf).germ U (sZ z) hzU s) := by
          symm
          exact hright

/-- Helper for Lemma 6.32.1: in the set-valued case, the stalk map of the counit is an
isomorphism at every point of `Z`. -/
private theorem subsetSheaf_type_counit_stalk_map_isIso
    (ℱ : TopCat.Sheaf (Type u) (TopCat.of Z)) (z : TopCat.of Z) :
    IsIso
      (((TopCat.Presheaf.stalkFunctor (Type u) z).map
        ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ).hom)) := by
  -- Cancel the stalk pullback comparison and reduce to the explicit `stalkPushforward` isomorphism.
  let e := TopCat.Sheaf.stalkPullbackIso sZ ((Sheaf.pushforward (Type u) sZ).obj ℱ) z
  have hEq :
      ((TopCat.Presheaf.stalkFunctor (Type u) z).map
          ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ).hom) =
        e.inv ≫ (subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱ) z).hom := by
    apply (cancel_epi e.hom).1
    calc
      e.hom ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) z).map
            ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ).hom)
          =
        (subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱ) z).hom := by
            simpa [e] using subsetSheaf_type_counit_stalk_comp_eq (ℱ := ℱ) z
      _ =
        e.hom ≫
          (e.inv ≫ (subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱ) z).hom) := by
            simp
  rw [hEq]
  letI : IsIso e.inv := by infer_instance
  letI : IsIso (subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱ) z).hom := by
    infer_instance
  simpa using
    (CategoryTheory.IsIso.comp_isIso
      (f := e.inv)
      (h := (subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱ) z).hom))

/-- Helper for Lemma 6.32.1: in the set-valued case, the pullback-pushforward counit is an
isomorphism. -/
private theorem subsetSheaf_type_pullback_pushforward_counit_isIso
    (ℱ : TopCat.Sheaf (Type u) (TopCat.of Z)) :
    IsIso ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ) := by
  -- The stalkwise criterion upgrades the explicit inside-`Z` stalk isomorphisms to a sheaf
  -- isomorphism.
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro z
  exact subsetSheaf_type_counit_stalk_map_isIso (ℱ := ℱ) z

/-- Helper for Lemma 6.32.1: in `AddCommGrpCat`, the map to the terminal object is an isomorphism
exactly when the source object is zero. -/
private theorem addCommGrpCat_isIso_terminal_from_iff_isZero (A : AddCommGrpCat.{u}) :
    IsIso (terminal.from A) ↔ IsZero A := by
  -- Rewrite the terminal map as the zero morphism and then use the standard zero-object criterion.
  have h :
      terminal.from A = (0 : A ⟶ ⊤_ AddCommGrpCat.{u}) := by
    simpa using
      (terminalIsTerminal.isZero).eq_of_tgt
        (terminal.from A) (0 : A ⟶ ⊤_ AddCommGrpCat.{u})
  rw [h, isIsoZero_iff_source_target_isZero]
  constructor
  · rintro ⟨hA, _⟩
    exact hA
  · intro hA
    exact ⟨hA, terminalIsTerminal.isZero⟩

section
variable {C : Type v} [Category.{u} C]
variable {FC : C → C → Type u} {CC : C → Type u}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
variable [IsAlgebraicStructure C (forget C)] [HasColimits.{u} C]

/-- Helper for Lemma 6.32.1: make the limit-preservation part of
`IsAlgebraicStructure C (forget C)` directly available in this section. -/
local instance : PreservesLimits (forget C) := inferInstance

/-- Helper for Lemma 6.32.1: make the filtered-colimit-preservation part of
`IsAlgebraicStructure C (forget C)` directly available in this section. -/
local instance : PreservesFilteredColimits (forget C) := inferInstance

/-- Helper for Lemma 6.32.1: algebraic-structure categories have the limits needed for sheaf
pullback. -/
local instance : HasLimits C := inferInstance

/-- Helper for Lemma 6.32.1: make the reflection of isomorphisms for `forget C` directly
available in this section. -/
local instance : (forget C).ReflectsIsomorphisms := inferInstance

/-- Helper for Lemma 6.32.1: full colimits provide the filtered colimits needed for
`stalkCompIso`. -/
local instance : HasFilteredColimits C :=
  hasFilteredColimitsOfSize_of_hasColimitsOfSize

/-- Helper for Lemma 6.32.1: the neighborhood category of a point is cofiltered. -/
local instance openNhds_isCofiltered_6_32_1 (x : X) : IsCofiltered (OpenNhds x) := by
  -- Open neighborhoods are closed under intersections and nonempty, so they form a cofiltered
  -- semilattice.
  let _ : SemilatticeInf (OpenNhds x) := inferInstance
  let _ : Nonempty (OpenNhds x) := inferInstance
  exact CategoryTheory.isCofiltered_of_semilatticeInf_nonempty (OpenNhds x)

/-- Helper for Lemma 6.32.1: the opposite neighborhood category of a point is filtered. -/
local instance openNhds_op_isFiltered_6_32_1 (x : X) : IsFiltered (OpenNhds x)ᵒᵖ :=
  CategoryTheory.isFiltered_op_of_isCofiltered (C := OpenNhds x)

/-- Helper for Lemma 6.32.1: the forward stalk-comparison isomorphism sends a germ in a
`C`-valued stalk to the corresponding germ in the underlying `Type`-valued stalk. -/
private theorem stalkCompIso_hom_germ_apply
    (ℱ : X.Presheaf C) (x : X) (U : Opens X) (hx : x ∈ U)
    (s : CC (ℱ.obj (op U))) :
    (stalkCompIso x (forget C) ℱ).hom (ℱ.germ U x hx s) =
      TopCat.Presheaf.germ (ℱ ⋙ forget C) U x hx s := by
  letI : HasColimitsOfShape (OpenNhds x)ᵒᵖ C :=
    HasColimits.hasColimitsOfShape (C := C) ((OpenNhds x)ᵒᵖ)
  letI : HasColimit ((OpenNhds.inclusion x).op ⋙ ℱ) :=
    HasColimitsOfShape.has_colimit ((OpenNhds.inclusion x).op ⋙ ℱ)
  letI : HasColimit (((OpenNhds.inclusion x).op ⋙ ℱ) ⋙ forget C) := by infer_instance
  -- Unfold the comparison isomorphism to the colimit-preservation isomorphism and evaluate its
  -- cocone-leg formula on the chosen germ.
  simpa [TopCat.Presheaf.germ, stalkCompIso, filteredStalkCompIso, filteredStalkFunctor]
    using congrFun
      (ι_preservesColimitIso_hom
        (G := forget C)
        (F := ((OpenNhds.inclusion x).op ⋙ ℱ))
        (j := op ⟨U, hx⟩))
      s

/-- Helper for Lemma 6.32.1: the inverse stalk-comparison isomorphism sends an underlying germ
back to the corresponding germ in the `C`-valued stalk. -/
private theorem stalkCompIso_inv_germ_apply
    (ℱ : X.Presheaf C) (x : X) (U : Opens X) (hx : x ∈ U)
    (s : CC (ℱ.obj (op U))) :
    (stalkCompIso x (forget C) ℱ).inv
        (TopCat.Presheaf.germ (ℱ ⋙ forget C) U x hx s) =
      ℱ.germ U x hx s := by
  letI : HasColimitsOfShape (OpenNhds x)ᵒᵖ C :=
    HasColimits.hasColimitsOfShape (C := C) ((OpenNhds x)ᵒᵖ)
  letI : HasColimit ((OpenNhds.inclusion x).op ⋙ ℱ) :=
    HasColimitsOfShape.has_colimit ((OpenNhds.inclusion x).op ⋙ ℱ)
  letI : HasColimit (((OpenNhds.inclusion x).op ⋙ ℱ) ⋙ forget C) := by infer_instance
  -- The inverse formula is the companion cocone-leg identity for `preservesColimitIso`.
  simpa [TopCat.Presheaf.germ, stalkCompIso, filteredStalkCompIso, filteredStalkFunctor]
    using congrFun
      (ι_preservesColimitIso_inv
        (G := forget C)
        (F := ((OpenNhds.inclusion x).op ⋙ ℱ))
        (j := op ⟨U, hx⟩))
      s

/-- Helper for Lemma 6.32.1: conjugating a stalk map by the source and target
`stalkCompIso` identifies it with the stalk map of the forgotten presheaf morphism. -/
private theorem stalkCompIso_conjugate_stalkFunctor_map
    {Y : TopCat.{u}} (x : Y) {ℱ 𝒢 : Y.Presheaf C} (α : ℱ ⟶ 𝒢) :
    (stalkCompIso x (forget C) ℱ).inv ≫
        (forget C).map ((TopCat.Presheaf.stalkFunctor C x).map α) ≫
        (stalkCompIso x (forget C) 𝒢).hom =
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        (((Functor.whiskeringRight (Opens Y)ᵒᵖ C (Type u)).obj (forget C)).map α)) := by
  -- This is exactly the naturality square of `filteredStalkCompIso`, rewritten in stalk form.
  have h :=
    (filteredStalkCompIso x (forget C)).hom.naturality α
  simpa [stalkCompIso, filteredStalkCompIso, filteredStalkFunctor, Category.assoc]
    using congrArg (fun k ↦ (stalkCompIso x (forget C) ℱ).inv ≫ k) h

/-- Helper for Lemma 6.32.1: the pointwise form of
`stalkCompIso_conjugate_stalkFunctor_map` moves a `C`-valued stalk map across the source and
target comparison isomorphisms. -/
private theorem stalkCompIso_conjugate_stalkFunctor_map_apply
    {Y : TopCat.{u}} (x : Y) {ℱ 𝒢 : Y.Presheaf C} (α : ℱ ⟶ 𝒢) (y : CC (ℱ.stalk x)) :
    (stalkCompIso x (forget C) 𝒢).hom
      (((TopCat.Presheaf.stalkFunctor C x).map α) y) =
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        (((Functor.whiskeringRight (Opens Y)ᵒᵖ C (Type u)).obj (forget C)).map α))
        ((stalkCompIso x (forget C) ℱ).hom y) := by
  -- Evaluate the conjugation identity on the image of `y` under the source comparison and
  -- cancel the resulting `inv ≫ hom`.
  have h :=
    congrArg
      (fun k ↦ k ((stalkCompIso x (forget C) ℱ).hom y))
      (stalkCompIso_conjugate_stalkFunctor_map (C := C) (x := x) (α := α))
  have hcancel :=
    congrArg
      (fun t ↦
        (stalkCompIso x (forget C) 𝒢).hom
          (((TopCat.Presheaf.stalkFunctor C x).map α) t))
      ((Iso.toEquiv (stalkCompIso x (forget C) ℱ)).left_inv y)
  calc
    (stalkCompIso x (forget C) 𝒢).hom
        (((TopCat.Presheaf.stalkFunctor C x).map α) y)
      =
        (stalkCompIso x (forget C) 𝒢).hom
          (((TopCat.Presheaf.stalkFunctor C x).map α)
            ((stalkCompIso x (forget C) ℱ).inv ((stalkCompIso x (forget C) ℱ).hom y))) := by
            symm
            exact hcancel
    _ =
      ((stalkCompIso x (forget C) ℱ).inv ≫
          (forget C).map ((TopCat.Presheaf.stalkFunctor C x).map α) ≫
          (stalkCompIso x (forget C) 𝒢).hom)
        ((stalkCompIso x (forget C) ℱ).hom y) := by
          rfl
    _ =
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        (((Functor.whiskeringRight (Opens Y)ᵒᵖ C (Type u)).obj (forget C)).map α))
        ((stalkCompIso x (forget C) ℱ).hom y) := h


/-- Helper for Lemma 6.32.1: after forgetting to underlying sets, the explicit inside-`Z`
`stalkPushforward` comparison agrees with the set-valued explicit comparison on every germ. -/
private theorem subsetSheaf_pushforward_stalkIsoAtPoint_underlying_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzU : sZ z ∈ U) (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
      { obj := ℱ.presheaf ⋙ forget C
        property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
    let eTgt := stalkCompIso z (forget C) ℱ.presheaf
    eTgt.hom
        (((subsetSheaf_pushforward_stalkIsoAtPoint (C := C) (ℱ := ℱ) z).hom)
          ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).germ U (sZ z) hzU s)) =
      ((subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱₜ) z).hom)
        (TopCat.Presheaf.germ
          ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C) U (sZ z) hzU s) := by
  let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
    { obj := ℱ.presheaf ⋙ forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
  let eTgt := stalkCompIso z (forget C) ℱ.presheaf
  have hzMap : z ∈ (Opens.map sZ).obj U := by
    simpa [TopCat.subsetInclusion] using hzU
  have hzMapi : z ∈ (Opens.map iZ).obj U := by
    simpa [TopCat.closedSubsetInclusion, TopCat.subsetInclusion] using hzMap
  letI : IsIso (ℱ.presheaf.stalkPushforward C iZ z) :=
    stalkPushforward_iso_of_isInducing C Topology.IsInducing.subtypeVal ℱ.presheaf z
  have hpush :
      ((subsetSheaf_pushforward_stalkIsoAtPoint (C := C) (ℱ := ℱ) z).hom)
          ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).germ U (sZ z) hzU s) =
        ℱ.presheaf.germ ((Opens.map sZ).obj U) z hzMap s := by
    -- The explicit comparison is the usual inducing-map stalk pushforward morphism.
    change
      ((asIso (ℱ.presheaf.stalkPushforward C iZ z)).hom)
          ((((Sheaf.pushforward C iZ).obj ℱ).presheaf).germ U (iZ z) hzMapi s) =
        ℱ.presheaf.germ ((Opens.map iZ).obj U) z hzMapi s
    have hpush_raw :
        ((asIso (ℱ.presheaf.stalkPushforward C iZ z)).hom)
            ((((Sheaf.pushforward C iZ).obj ℱ).presheaf).germ U (iZ z) hzMapi s) =
          (ℱ.presheaf.germ ((Opens.map iZ).obj U) z hzMapi) s := by
      calc
        ((asIso (ℱ.presheaf.stalkPushforward C iZ z)).hom)
            ((((Sheaf.pushforward C iZ).obj ℱ).presheaf).germ U (iZ z) hzMapi s)
            =
          ((((Sheaf.pushforward C iZ).obj ℱ).presheaf).germ U (iZ z) hzMapi ≫
              (asIso (ℱ.presheaf.stalkPushforward C iZ z)).hom) s := by
                symm
                exact CategoryTheory.comp_apply _ _ _
        _ = (ℱ.presheaf.germ ((Opens.map iZ).obj U) z hzMapi) s := by
          exact congrArg
            (fun k ↦ k s)
            (TopCat.Presheaf.stalkPushforward_germ C iZ ℱ.presheaf U z hzMapi)
    simpa [subsetSheaf_pushforward_stalkIsoAtPoint, TopCat.closedSubsetInclusion,
      TopCat.subsetInclusion] using hpush_raw
  rw [hpush]
  have hpushType :
      ((subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱₜ) z).hom)
          (TopCat.Presheaf.germ
            ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C) U (sZ z) hzU s) =
        TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap s := by
    -- The set-valued explicit comparison is the same stalk-pushforward owner for `ℱ ⋙ forget C`.
    simpa [ℱₜ, subsetSheaf_pushforward_stalkIsoAtPoint, TopCat.closedSubsetInclusion,
      TopCat.subsetInclusion, ConcreteCategory.comp_apply] using
      congrArg
        (fun k ↦ k s)
        (TopCat.Presheaf.stalkPushforward_germ (Type u) sZ ℱₜ.presheaf U z hzMap)
  -- The target stalk comparison then forgets to the corresponding set-valued germ.
  calc
    eTgt.hom (ℱ.presheaf.germ ((Opens.map sZ).obj U) z hzMap s)
        = TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap s := by
            dsimp [eTgt]
            exact
              (stalkCompIso_hom_germ_apply (ℱ := ℱ.presheaf) (x := z)
                (U := (Opens.map sZ).obj U) (hx := hzMap) (s := s))
    _ =
      ((subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱₜ) z).hom)
        (TopCat.Presheaf.germ
          ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C) U (sZ z) hzU s) := by
            symm
            exact hpushType

/-- Helper for Lemma 6.32.1: after conjugating by the source and target stalk-comparison
isomorphisms, the explicit `C`-valued `stalkPushforward` comparison becomes the set-valued
explicit comparison. -/
private theorem subsetSheaf_pushforward_stalkIsoAtPoint_underlying_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) :
    let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
      { obj := ℱ.presheaf ⋙ forget C
        property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
    let eSrc := stalkCompIso (sZ z) (forget C) (((Sheaf.pushforward C sZ).obj ℱ).presheaf)
    let eTgt := stalkCompIso z (forget C) ℱ.presheaf
    eSrc.inv ≫ (forget C).map (subsetSheaf_pushforward_stalkIsoAtPoint (C := C) (ℱ := ℱ) z).hom ≫
        eTgt.hom =
      (subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱₜ) z).hom := by
  let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
    { obj := ℱ.presheaf ⋙ forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
  let eSrc := stalkCompIso (sZ z) (forget C) (((Sheaf.pushforward C sZ).obj ℱ).presheaf)
  let eTgt := stalkCompIso z (forget C) ℱ.presheaf
  -- Compare both stalk morphisms on the germ generators of the underlying pushforward stalk.
  apply TopCat.Presheaf.stalk_hom_ext ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C)
  intro U hzU
  ext s
  -- The inverse source comparison recovers the original `C`-valued germ, so the germ-level
  -- underlying comparison closes the resulting equality.
  calc
    (eSrc.inv ≫ (forget C).map (subsetSheaf_pushforward_stalkIsoAtPoint
          (C := C) (ℱ := ℱ) z).hom ≫ eTgt.hom)
        (TopCat.Presheaf.germ ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C)
          U (sZ z) hzU s)
        =
      eTgt.hom
        (((subsetSheaf_pushforward_stalkIsoAtPoint (C := C) (ℱ := ℱ) z).hom)
          ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).germ U (sZ z) hzU s)) := by
            change
              eTgt.hom
                (((subsetSheaf_pushforward_stalkIsoAtPoint (C := C) (ℱ := ℱ) z).hom)
                  (eSrc.inv
                    (TopCat.Presheaf.germ
                      ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C) U (sZ z) hzU s))) =
                _
            rw [stalkCompIso_inv_germ_apply
              (ℱ := ((Sheaf.pushforward C sZ).obj ℱ).presheaf) (x := sZ z)
              (U := U) (hx := hzU) (s := s)]
    _ =
      ((subsetSheaf_pushforward_stalkIsoAtPoint (C := Type u) (ℱ := ℱₜ) z).hom)
        (TopCat.Presheaf.germ
          ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C) U (sZ z) hzU s) := by
            exact subsetSheaf_pushforward_stalkIsoAtPoint_underlying_germ_eq
              (C := C) (ℱ := ℱ) (z := z) (U := U) (hzU := hzU) (s := s)

/-- Helper for Lemma 6.32.1: the source stalk-comparison isomorphism carries an underlying germ in
the pushed-forward stalk back to the corresponding `C`-valued germ. -/
private theorem subsetSheaf_pushforward_source_stalkCompIso_inv_germ_apply
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzU : sZ z ∈ U) (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    (stalkCompIso (sZ z) (forget C) (((Sheaf.pushforward C sZ).obj ℱ).presheaf)).inv
        (TopCat.Presheaf.germ
          ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C) U (sZ z) hzU s) =
      (((Sheaf.pushforward C sZ).obj ℱ).presheaf).germ U (sZ z) hzU s := by
  -- This is the specialization of `stalkCompIso_inv_germ_apply` to the pushed-forward stalk.
  exact stalkCompIso_inv_germ_apply
    (ℱ := ((Sheaf.pushforward C sZ).obj ℱ).presheaf) (x := sZ z)
    (U := U) (hx := hzU) (s := s)

/-- Helper for Lemma 6.32.1: on a germ generator, the set-valued counit composite for the
underlying sheaf reduces to the corresponding underlying germ. -/
private theorem subsetSheaf_type_counit_stalk_comp_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzU : sZ z ∈ U)
    (s : ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C).obj (op U)) :
    let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
      { obj := ℱ.presheaf ⋙ forget C
        property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
    let hzMap : z ∈ (Opens.map sZ).obj U := by
      simpa [TopCat.subsetInclusion] using hzU
    let g :=
      TopCat.Presheaf.germ
        ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C) U (sZ z) hzU s
    (((TopCat.Sheaf.stalkPullbackIso sZ ((Sheaf.pushforward (Type u) sZ).obj ℱₜ) z).hom) ≫
        ((TopCat.Presheaf.stalkFunctor (Type u) z).map
          ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱₜ).hom))
      g =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap s := by
  let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
    { obj := ℱ.presheaf ⋙ forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
  have hzMap : z ∈ (Opens.map sZ).obj U := by
    simpa [TopCat.subsetInclusion] using hzU
  let g :=
    TopCat.Presheaf.germ
      ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C) U (sZ z) hzU s
  have hpullback :
      ((TopCat.Sheaf.stalkPullbackIso sZ ((Sheaf.pushforward (Type u) sZ).obj ℱₜ) z).hom) g =
        ((((sZ⁻¹).obj ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).presheaf).germ
          ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
                ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).1.app (op U)) s)) := by
    -- First expand the Type-valued sheaf stalk pullback comparison on the chosen germ.
    simpa [g] using
      (subsetSheaf_sheafStalkPullbackGermApply
        (f := sZ) (𝒢 := ((Sheaf.pushforward (Type u) sZ).obj ℱₜ))
        (U := U) (z := z) (hz := hzMap) (s := s))
  have hcounit :
      ((TopCat.Presheaf.stalkFunctor (Type u) z).map
          ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱₜ).hom)
        ((((sZ⁻¹).obj ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).presheaf).germ
          ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
                ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).1.app (op U)) s)) =
        TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱₜ).1.app
              (op ((Opens.map sZ).obj U)))
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
                  ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).1.app (op U)) s)) := by
    -- Then move the counit stalk map back to the corresponding section-level counit map.
    simpa [ℱₜ] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply
        ((Opens.map sZ).obj U) z hzMap
        ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱₜ).hom
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
              ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).1.app (op U)) s))
  have hsection :
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱₜ).1.app
          (op ((Opens.map sZ).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
              ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).1.app (op U)) s) = s := by
    -- The right-triangle identity collapses the counit after the pullback unit.
    change
      ((((Sheaf.pushforward (Type u) sZ).map
              ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱₜ)).1.app
          (op U))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
              ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).1.app (op U)) s)) =
      (fun k ↦ (k.1.app (op U)) s) (𝟙 ((Sheaf.pushforward (Type u) sZ).obj ℱₜ))
    exact congrArg
      (fun k ↦ (k.1.app (op U)) s)
      ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).right_triangle_components ℱₜ)
  -- Combining the pullback-germ computation with the counit and the triangle identity gives the
  -- normalized underlying germ.
  calc
    (((TopCat.Sheaf.stalkPullbackIso sZ ((Sheaf.pushforward (Type u) sZ).obj ℱₜ) z).hom) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) z).map
            ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱₜ).hom))
        g
        =
      ((TopCat.Presheaf.stalkFunctor (Type u) z).map
          ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱₜ).hom)
        ((((sZ⁻¹).obj ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).presheaf).germ
          ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
                ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).1.app (op U)) s)) := by
            change
              ((TopCat.Presheaf.stalkFunctor (Type u) z).map
                  ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱₜ).hom)
                (((TopCat.Sheaf.stalkPullbackIso sZ
                    ((Sheaf.pushforward (Type u) sZ).obj ℱₜ) z).hom) g) = _
            rw [hpullback]
    _ =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱₜ).1.app
            (op ((Opens.map sZ).obj U)))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
                ((Sheaf.pushforward (Type u) sZ).obj ℱₜ)).1.app (op U)) s)) := hcounit
    _ = TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap s := by
      rw [hsection]

/-- Helper for Lemma 6.32.1: the source stalk-comparison isomorphism sends a pushed-forward germ to
the corresponding underlying germ. -/
private theorem subsetSheaf_pushforward_source_stalkCompIso_hom_germ_apply
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzU : sZ z ∈ U) (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    (stalkCompIso (sZ z) (forget C) (((Sheaf.pushforward C sZ).obj ℱ).presheaf)).hom
        ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).germ U (sZ z) hzU s) =
      TopCat.Presheaf.germ
        ((((Sheaf.pushforward C sZ).obj ℱ).presheaf) ⋙ forget C) U (sZ z) hzU s := by
  -- This is the source-side specialization of the general stalk-comparison germ formula.
  exact stalkCompIso_hom_germ_apply
    (ℱ := ((Sheaf.pushforward C sZ).obj ℱ).presheaf) (x := sZ z)
    (U := U) (hx := hzU) (s := s)

/-- Helper for Lemma 6.32.1: after the target-side stalk comparison, an explicit `C`-valued germ
becomes the corresponding underlying germ. -/
private theorem subsetSheaf_target_stalkCompIso_hom_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzMap : z ∈ (Opens.map sZ).obj U)
    (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    (stalkCompIso z (forget C) ℱ.presheaf).hom
      (ℱ.presheaf.germ ((Opens.map sZ).obj U) z hzMap s) =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap s := by
  -- This is the target-side specialization of `stalkCompIso_hom_germ_apply`.
  exact stalkCompIso_hom_germ_apply
    (ℱ := ℱ.presheaf) (x := z) (U := ((Opens.map sZ).obj U)) (hx := hzMap) (s := s)

/-- Helper for Lemma 6.32.1: the presheaf-level stalk pullback owner already sends a pushed-forward
germ to the explicit presheaf pullback-unit germ. -/
private theorem subsetSheaf_presheaf_stalkPullback_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzU : sZ z ∈ U) (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let G := (Sheaf.pushforward C sZ).obj ℱ
    let hzMap : z ∈ (Opens.map sZ).obj U := by
      simpa [TopCat.subsetInclusion] using hzU
    (TopCat.Presheaf.stalkPullbackIso C sZ G.presheaf z).hom
        (G.presheaf.germ U (sZ z) hzU s) =
      (((TopCat.Presheaf.pullback C sZ).obj G.1).germ
        ((Opens.map sZ).obj U) z hzMap
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction C sZ).unit.app G.1).app
            (op U)) s)) := by
  let G := (Sheaf.pushforward C sZ).obj ℱ
  have hzMap : z ∈ (Opens.map sZ).obj U := by
    simpa [TopCat.subsetInclusion] using hzU
  -- The presheaf-level stalk pullback owner computes the first leg on the chosen germ.
  calc
    (TopCat.Presheaf.stalkPullbackIso C sZ G.presheaf z).hom
        (G.presheaf.germ U (sZ z) hzU s)
      =
        ((G.presheaf.germ U (sZ z) hzU) ≫
          (TopCat.Presheaf.stalkPullbackIso C sZ G.presheaf z).hom) s := by
            rw [CategoryTheory.comp_apply]
    _ =
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction C sZ).unit.app G.1).app
            (op U)) ≫
          (((TopCat.Presheaf.pullback C sZ).obj G.1).germ
            ((Opens.map sZ).obj U) z hzMap)) s := by
              simpa [G, TopCat.Presheaf.stalkPullbackIso, TopCat.subsetInclusion] using
                congrArg
                  (fun k ↦ k s)
                  (TopCat.Presheaf.germ_stalkPullbackHom C sZ G.1 z U hzU)
    _ =
        (((TopCat.Presheaf.pullback C sZ).obj G.1).germ
          ((Opens.map sZ).obj U) z hzMap)
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction C sZ).unit.app G.1).app
              (op U)) s) := by
                rw [CategoryTheory.comp_apply]
                rfl

/-- Helper for Lemma 6.32.1: after the presheaf-level stalk pullback comparison, the target
stalk-comparison isomorphism forgets the resulting pullback germ to the corresponding underlying
presheaf pullback-unit germ. -/
private theorem subsetSheaf_presheaf_stalkPullback_underlying_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzU : sZ z ∈ U) (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
    let P := (TopCat.Presheaf.pullback C sZ).obj G.1
    let hzMap : z ∈ (Opens.map sZ).obj U := by
      simpa [TopCat.subsetInclusion] using hzU
    let presheafUnit :
        CC (P.obj (op ((Opens.map sZ).obj U))) :=
      ((((TopCat.Presheaf.pullbackPushforwardAdjunction C sZ).unit.app G.1).app (op U)) s)
    let eP := stalkCompIso z (forget C) P
    eP.hom
      ((TopCat.Presheaf.stalkPullbackIso C sZ G.presheaf z).hom
        (G.presheaf.germ U (sZ z) hzU s)) =
      TopCat.Presheaf.germ (P ⋙ forget C) ((Opens.map sZ).obj U) z hzMap presheafUnit := by
  let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
  let P := (TopCat.Presheaf.pullback C sZ).obj G.1
  have hzMap : z ∈ (Opens.map sZ).obj U := by
    simpa [TopCat.subsetInclusion] using hzU
  let presheafUnit :
      CC (P.obj (op ((Opens.map sZ).obj U))) :=
    ((((TopCat.Presheaf.pullbackPushforwardAdjunction C sZ).unit.app G.1).app (op U)) s)
  let eP := stalkCompIso z (forget C) P
  -- First compute the presheaf pullback leg, then forget the resulting pullback germ.
  calc
    eP.hom
        ((TopCat.Presheaf.stalkPullbackIso C sZ G.presheaf z).hom
          (G.presheaf.germ U (sZ z) hzU s))
        =
      eP.hom
        (P.germ ((Opens.map sZ).obj U) z hzMap presheafUnit) := by
            rw [subsetSheaf_presheaf_stalkPullback_germ_eq
              (C := C) (ℱ := ℱ) (z := z) (U := U) (hzU := hzU) (s := s)]
    _ =
      TopCat.Presheaf.germ (P ⋙ forget C) ((Opens.map sZ).obj U) z hzMap presheafUnit := by
            exact
              stalkCompIso_hom_germ_apply
                (ℱ := P) (x := z) (U := ((Opens.map sZ).obj U))
                (hx := hzMap) (s := presheafUnit)

/-- Helper for Lemma 6.32.1: evaluating the pushed-forward sheaf on `U` is definitionally
evaluation of the original sheaf on the pulled-back open. -/
private theorem subsetSheaf_pushforward_obj_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (U : Opens X) :
    ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U)) =
      (ℱ.presheaf.obj (op ((Opens.map sZ).obj U))) := rfl

/-- Helper for Lemma 6.32.1: forgetting a `C`-valued sheaf to the underlying set-valued
presheaf. -/
private noncomputable abbrev sheafForgetToTypes (Y : TopCat.{u}) :
    TopCat.Sheaf C Y ⥤ TopCat.Presheaf (Type u) Y :=
  TopCat.Sheaf.forget C Y ⋙
    ((Functor.whiskeringRight (Opens Y)ᵒᵖ C (Type u)).obj (forget C))

/-- Helper for Lemma 6.32.1: forgetting a `C`-valued sheaf gives a set-valued sheaf with the
same underlying presheaf. -/
private noncomputable abbrev underlyingTypeSheaf {Y : TopCat.{u}}
    (ℱ : TopCat.Sheaf C Y) :
    TopCat.Sheaf (Type u) Y :=
  { obj := ℱ.presheaf ⋙ forget C
    property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }

/-- Helper for Lemma 6.32.1: an isomorphism of `C`-valued sheaves induces an isomorphism of the
corresponding underlying sheaves of sets. -/
private noncomputable def underlyingTypeSheaf_mapIso {Y : TopCat.{u}}
    {ℱ 𝒢 : TopCat.Sheaf C Y} (e : ℱ ≅ 𝒢) :
    underlyingTypeSheaf (C := C) ℱ ≅ underlyingTypeSheaf (C := C) 𝒢 :=
  ObjectProperty.isoMk _ <|
    ((Functor.whiskeringRight (Opens Y)ᵒᵖ C (Type u)).obj (forget C)).mapIso
      ((TopCat.Sheaf.forget C Y).mapIso e)

/-- Helper for Lemma 6.32.1: evaluating the underlying map induced by a sheaf isomorphism agrees
definitionally with evaluating the original section map. -/
private theorem underlyingTypeSheaf_mapIso_hom_app_apply {Y : TopCat.{u}}
    {ℱ 𝒢 : TopCat.Sheaf C Y} (e : ℱ ≅ 𝒢) (U : Opens Y)
    (s : CC (ℱ.1.obj (op U))) :
    (((underlyingTypeSheaf_mapIso (C := C) e).hom).1.app (op U)) s =
      ((e.hom).1.app (op U)) s := by
  -- The underlying isomorphism is obtained by whiskering with `forget C`, so its section map is
  -- exactly the underlying function of the original section map.
  rfl

/-- Helper for Lemma 6.32.1: after forgetting algebraic structure, the inverse pullback
comparison sends the sheafified presheaf pullback-unit section of the pushed-forward sheaf to the
genuine pullback-unit section. -/
private theorem subsetSheaf_pullback_middle_section_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (U : Opens X)
    (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
      { obj := ℱ.presheaf ⋙ forget C
        property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
    let Gₜ := (Sheaf.pushforward (Type u) sZ).obj ℱₜ
    (((TopCat.Sheaf.pullbackIso (Type u) sZ).inv.app Gₜ).1.app
        (op ((Opens.map sZ).obj U)))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          ((TopCat.Sheaf.forget (Type u) X ⋙ TopCat.Presheaf.pullback (Type u) sZ).obj Gₜ)).app
          (op ((Opens.map sZ).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app Gₜ.1).app
            (op U)) s)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app Gₜ).1.app
          (op U)) s) := by
  let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
    { obj := ℱ.presheaf ⋙ forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
  let Gₜ := (Sheaf.pushforward (Type u) sZ).obj ℱₜ
  -- This is exactly the Type-valued section-level pullback-unit normalization for the forgotten
  -- pushed-forward sheaf.
  simpa [Gₜ, ℱₜ] using
    (pullbackIso_inv_toSheafify_unit_section_eq
      (f := sZ) (𝒢 := Gₜ) (U := U) (s := s))

/-- Helper for Lemma 6.32.1: after passing the section-level middle-leg normalization to stalks,
the forgotten inverse pullback comparison on the pushed-forward underlying sheaf sends the
sheafified pullback-unit germ to the genuine pullback-unit germ. -/
private theorem subsetSheaf_pullback_middle_underlying_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzMap : z ∈ (Opens.map sZ).obj U)
    (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
      { obj := ℱ.presheaf ⋙ forget C
        property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
    let Gₜ := (Sheaf.pushforward (Type u) sZ).obj ℱₜ
    ((TopCat.Presheaf.stalkFunctor (Type u) z).map
        ((TopCat.Sheaf.forget (Type u) (TopCat.of Z)).map
          ((TopCat.Sheaf.pullbackIso (Type u) sZ).inv.app Gₜ)))
      ((TopCat.Presheaf.germ
          (sheafify (Opens.grothendieckTopology (TopCat.of Z))
            ((TopCat.Sheaf.forget (Type u) X ⋙ TopCat.Presheaf.pullback (Type u) sZ).obj Gₜ))
          ((Opens.map sZ).obj U) z hzMap)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
            ((TopCat.Sheaf.forget (Type u) X ⋙ TopCat.Presheaf.pullback (Type u) sZ).obj Gₜ)).app
          (op ((Opens.map sZ).obj U))
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app Gₜ.1).app
              (op U)) s))) =
      (((sZ⁻¹).obj Gₜ).presheaf).germ ((Opens.map sZ).obj U) z hzMap
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app Gₜ).1.app
            (op U)) s) := by
  let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
    { obj := ℱ.presheaf ⋙ forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
  let Gₜ := (Sheaf.pushforward (Type u) sZ).obj ℱₜ
  -- This is the generic stalk-level middle-leg normalization specialized to the forgotten
  -- pushed-forward sheaf.
  simpa [Gₜ, ℱₜ] using
    (pullbackIso_inv_toSheafify_unit_stalk_germ_eq
      (f := sZ) (𝒢 := Gₜ) (U := U) (y := z) (hy := hzMap) (s := s))

/-- Helper for Lemma 6.32.1: the Type-valued pullback comparison sends the actual pullback-unit
section back to the corresponding sheafified presheaf pullback-unit section. -/
private theorem subsetSheaf_type_pullbackIso_hom_unit_section_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (U : Opens X)
    (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
    (((TopCat.Sheaf.pullbackIso (Type u) sZ).hom.app (underlyingTypeSheaf G)).1.app
        (op ((Opens.map sZ).obj U)))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
            (underlyingTypeSheaf G)).1.app (op U)) s) =
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          ((TopCat.Sheaf.forget (Type u) X ⋙ TopCat.Presheaf.pullback (Type u) sZ).obj
            (underlyingTypeSheaf G))).app
        (op ((Opens.map sZ).obj U))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
              (underlyingTypeSheaf G).1).app (op U)) s)) := by
  let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
  let V : Opens (TopCat.of Z) := (Opens.map sZ).obj U
  let t :
      (sheafify (Opens.grothendieckTopology (TopCat.of Z))
        ((TopCat.Sheaf.forget (Type u) X ⋙ TopCat.Presheaf.pullback (Type u) sZ).obj
          (underlyingTypeSheaf G))).obj (op V) :=
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
        ((TopCat.Sheaf.forget (Type u) X ⋙ TopCat.Presheaf.pullback (Type u) sZ).obj
          (underlyingTypeSheaf G))).app
      (op V))
      ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
            (underlyingTypeSheaf G).1).app (op U)) s)
  -- Rewrite the actual unit section via `pullbackIso.inv`, then cancel with `hom`.
  calc
    (((TopCat.Sheaf.pullbackIso (Type u) sZ).hom.app (underlyingTypeSheaf G)).1.app
        (op V))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app
            (underlyingTypeSheaf G)).1.app (op U)) s) =
      (((TopCat.Sheaf.pullbackIso (Type u) sZ).hom.app (underlyingTypeSheaf G)).1.app
          (op V))
        ((((TopCat.Sheaf.pullbackIso (Type u) sZ).inv.app (underlyingTypeSheaf G)).1.app
            (op V)) t) := by
          rw [pullbackIso_inv_toSheafify_unit_section_eq
            (f := sZ) (𝒢 := underlyingTypeSheaf G) (U := U) (s := s)]
    _ = t := by
          simpa [t, V] using
            congrArg
              (fun k ↦ (k.1.app (op V)) t)
              (Iso.inv_hom_id_app (TopCat.Sheaf.pullbackIso (Type u) sZ) (underlyingTypeSheaf G))

/-- Helper for Lemma 6.32.1: the Type-valued stalk pullback isomorphism for the underlying
pushed-forward sheaf sends a pushed-forward germ to the corresponding pullback-unit germ. -/
private theorem subsetSheaf_type_pullback_stalk_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzU : sZ z ∈ U) (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) := underlyingTypeSheaf ℱ
    let Gₜ : TopCat.Sheaf (Type u) X := (Sheaf.pushforward (Type u) sZ).obj ℱₜ
    let hzMap : z ∈ (Opens.map sZ).obj U := by
      simpa [TopCat.subsetInclusion] using hzU
    ((TopCat.Sheaf.stalkPullbackIso sZ Gₜ z).hom)
      (Gₜ.presheaf.germ U (sZ z) hzU s) =
      (((sZ⁻¹).obj Gₜ).presheaf).germ ((Opens.map sZ).obj U) z hzMap
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app Gₜ).1.app
            (op U)) s) := by
  let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) := underlyingTypeSheaf ℱ
  let Gₜ : TopCat.Sheaf (Type u) X := (Sheaf.pushforward (Type u) sZ).obj ℱₜ
  have hzMap : z ∈ (Opens.map sZ).obj U := by
    simpa [TopCat.subsetInclusion] using hzU
  -- This is the Type-valued specialization of the general stalk pullback germ formula.
  simpa [ℱₜ, Gₜ] using
    (subsetSheaf_sheafStalkPullbackGermApply
      (f := sZ) (𝒢 := Gₜ) (U := U) (z := z) (hz := hzMap) (s := s))

/-- Helper for Lemma 6.32.1: applying the counit after the pullback-pushforward unit gives back the
original pushed-forward section. -/
private theorem subsetSheaf_counit_unit_section_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (U : Opens X)
    (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ).1.app
        (op ((Opens.map sZ).obj U)))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
            ((Sheaf.pushforward C sZ).obj ℱ)).1.app (op U)) s) = s := by
  -- Evaluate the right-triangle identity on the chosen ambient section.
  change
    (((Sheaf.pushforward C sZ).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ)).1.app (op U))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
            ((Sheaf.pushforward C sZ).obj ℱ)).1.app (op U)) s) = s
  have h :=
    congrArg
      (fun k ↦ (k.1.app (op U)))
      ((Sheaf.pullbackPushforwardAdjunction C sZ).right_triangle_components ℱ)
  change
    (((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
          ((Sheaf.pushforward C sZ).obj ℱ)).1.app (op U)) ≫
        (((Sheaf.pushforward C sZ).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ)).1.app (op U)) =
      𝟙 _ at h
  have hs := congrArg (fun k ↦ k s) h
  calc
    (((Sheaf.pushforward C sZ).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ)).1.app (op U))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app
              ((Sheaf.pushforward C sZ).obj ℱ)).1.app (op U)) s)
      =
        (𝟙 ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) s := by
          simpa only [CategoryTheory.comp_apply] using hs
    _ = s := by
          exact ConcreteCategory.id_apply s

/-- Helper for Lemma 6.32.1: fix the common middle sheafification owner used to compare the
Type-valued pullback and the underlying pullback of the `C`-valued pushed-forward sheaf. -/
private noncomputable abbrev subsetSheaf_pullback_forget_middle
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) :
    TopCat.Sheaf (Type u) (TopCat.of Z) :=
  let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
  let P := (TopCat.Presheaf.pullback C sZ).obj G.1
  (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology (TopCat.of Z)) (Type u)).obj
    (P ⋙ forget C)

/-- Helper for Lemma 6.32.1: after the presheaf pullback leg has been forgotten, applying the
sheafification unit on stalks produces the corresponding germ in the common middle owner. -/
private theorem subsetSheaf_pullback_forget_middle_toSheafify_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzMap : z ∈ (Opens.map sZ).obj U)
    (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
    let P := (TopCat.Presheaf.pullback C sZ).obj G.1
    let presheafUnit :
        CC (P.obj (op ((Opens.map sZ).obj U))) :=
      ((((TopCat.Presheaf.pullbackPushforwardAdjunction C sZ).unit.app G.1).app
          (op U)) s)
    ((TopCat.Presheaf.stalkFunctor (Type u) z).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          (P ⋙ forget C)))
      (TopCat.Presheaf.germ (P ⋙ forget C) ((Opens.map sZ).obj U) z hzMap presheafUnit) =
      TopCat.Presheaf.germ ((subsetSheaf_pullback_forget_middle (C := C) ℱ).presheaf)
        ((Opens.map sZ).obj U) z hzMap
        (((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
            (P ⋙ forget C)).app (op ((Opens.map sZ).obj U))) presheafUnit) := by
  let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
  let P := (TopCat.Presheaf.pullback C sZ).obj G.1
  let presheafUnit :
      CC (P.obj (op ((Opens.map sZ).obj U))) :=
    ((((TopCat.Presheaf.pullbackPushforwardAdjunction C sZ).unit.app G.1).app
        (op U)) s)
  -- This is the common middle-owner specialization of `toSheafify_stalk_map_germ_apply`.
  simpa [subsetSheaf_pullback_forget_middle, G, presheafUnit] using
    (toSheafify_stalk_map_germ_apply
      (ℱ := (P ⋙ forget C)) (W := ((Opens.map sZ).obj U)) (y := z)
      (hy := hzMap) (t := presheafUnit))

/-- Helper for Lemma 6.32.1: after applying the counit stalk map to the explicit pullback-unit
germ and then forgetting algebraic structure, one recovers the underlying original germ. -/
private theorem subsetSheaf_counit_on_pullback_unit_underlying_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzMap : z ∈ (Opens.map sZ).obj U)
    (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
    let unitSection :
        CC ((((sZ⁻¹).obj G).presheaf).obj (op ((Opens.map sZ).obj U))) :=
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app G).1.app (op U)) s)
    let eTgt := stalkCompIso z (forget C) ℱ.presheaf
    eTgt.hom
      (((TopCat.Presheaf.stalkFunctor C z).map
          ((Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ).hom)
        ((((sZ⁻¹).obj G).presheaf).germ ((Opens.map sZ).obj U) z hzMap unitSection)) =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap s := by
  let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
  let unitSection :
      CC ((((sZ⁻¹).obj G).presheaf).obj (op ((Opens.map sZ).obj U))) :=
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app G).1.app (op U)) s)
  let eSrc := stalkCompIso z (forget C) (((sZ⁻¹).obj G).presheaf)
  let eTgt := stalkCompIso z (forget C) ℱ.presheaf
  let α := ((Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ).hom
  have hconj :
      eSrc.inv ≫ (forget C).map ((TopCat.Presheaf.stalkFunctor C z).map α) ≫ eTgt.hom =
        ((TopCat.Presheaf.stalkFunctor (Type u) z).map
          (((Functor.whiskeringRight (Opens (TopCat.of Z))ᵒᵖ C (Type u)).obj (forget C)).map α)) := by
    -- Conjugate the `C`-valued counit stalk map by the source and target stalk comparisons.
    exact stalkCompIso_conjugate_stalkFunctor_map (C := C) (x := z) (α := α)
  have hsection :
      (((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ).1.app
          (op ((Opens.map sZ).obj U)))
        unitSection = s := by
    -- The section-level right triangle collapses the counit after the explicit unit section.
    simpa [G, unitSection] using
      (subsetSheaf_counit_unit_section_eq (C := C) (ℱ := ℱ) (U := U) (s := s))
  have hmap :
      ((TopCat.Presheaf.stalkFunctor (Type u) z).map
          (((Functor.whiskeringRight (Opens (TopCat.of Z))ᵒᵖ C (Type u)).obj (forget C)).map α))
        (TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C)
          ((Opens.map sZ).obj U) z hzMap unitSection) =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap
        ((((Functor.whiskeringRight (Opens (TopCat.of Z))ᵒᵖ C (Type u)).obj (forget C)).map α).app
          (op ((Opens.map sZ).obj U)) unitSection) := by
    -- The forgotten stalk map carries the forgotten germ to the forgotten section-level counit.
    simpa [α, ConcreteCategory.comp_apply] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply
        ((Opens.map sZ).obj U) z hzMap
        ((((Functor.whiskeringRight (Opens (TopCat.of Z))ᵒᵖ C (Type u)).obj
            (forget C)).map α))
        unitSection)
  -- Move the source germ through the stalk comparison, then rewrite the forgotten counit stalk map
  -- as the corresponding underlying section map and finish with the triangle identity.
  calc
    eTgt.hom
        (((TopCat.Presheaf.stalkFunctor C z).map α)
          ((((sZ⁻¹).obj G).presheaf).germ ((Opens.map sZ).obj U) z hzMap unitSection))
        =
      eTgt.hom
        (((TopCat.Presheaf.stalkFunctor C z).map α)
          (eSrc.inv
            (TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C)
              ((Opens.map sZ).obj U) z hzMap unitSection))) := by
            rw [stalkCompIso_inv_germ_apply
              (ℱ := (((sZ⁻¹).obj G).presheaf)) (x := z) (U := ((Opens.map sZ).obj U))
              (hx := hzMap) (s := unitSection)]
    _ =
      (eSrc.inv ≫ (forget C).map ((TopCat.Presheaf.stalkFunctor C z).map α) ≫ eTgt.hom)
        (TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C)
          ((Opens.map sZ).obj U) z hzMap unitSection) := by
            rfl
    _ =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap
        ((((Functor.whiskeringRight (Opens (TopCat.of Z))ᵒᵖ C (Type u)).obj (forget C)).map α).app
          (op ((Opens.map sZ).obj U)) unitSection) := by
            rw [hconj]
            exact hmap
    _ =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ).1.app
            (op ((Opens.map sZ).obj U)))
          unitSection) := by
            rfl
    _ = TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap s := by
      rw [hsection]

/-- Helper for Lemma 6.32.1: after conjugating the counit stalk map by the source and target
stalk comparisons, the explicit pullback-unit germ in the actual pullback stalk is sent to the
underlying original germ. -/
private theorem subsetSheaf_counit_underlying_conjugated_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzMap : z ∈ (Opens.map sZ).obj U)
    (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
    let unitSection :
        CC ((((sZ⁻¹).obj G).presheaf).obj (op ((Opens.map sZ).obj U))) :=
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app G).1.app (op U)) s)
    let eSrc := stalkCompIso z (forget C) (((sZ⁻¹).obj G).presheaf)
    let eTgt := stalkCompIso z (forget C) ℱ.presheaf
    (eSrc.inv ≫
        (forget C).map ((TopCat.Presheaf.stalkFunctor C z).map
          ((Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ).hom) ≫
        eTgt.hom)
      (TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C)
        ((Opens.map sZ).obj U) z hzMap unitSection) =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap s := by
  let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
  let unitSection :
      CC ((((sZ⁻¹).obj G).presheaf).obj (op ((Opens.map sZ).obj U))) :=
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app G).1.app (op U)) s)
  let eSrc := stalkCompIso z (forget C) (((sZ⁻¹).obj G).presheaf)
  let eTgt := stalkCompIso z (forget C) ℱ.presheaf
  -- First recover the `C`-valued pullback-unit germ from the underlying source germ, then apply
  -- the already-proved underlying counit computation.
  calc
    (eSrc.inv ≫
        (forget C).map ((TopCat.Presheaf.stalkFunctor C z).map
          ((Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ).hom) ≫
        eTgt.hom)
      (TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C)
        ((Opens.map sZ).obj U) z hzMap unitSection)
        =
      eTgt.hom
        (((TopCat.Presheaf.stalkFunctor C z).map
            ((Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ).hom)
          ((((sZ⁻¹).obj G).presheaf).germ ((Opens.map sZ).obj U) z hzMap unitSection)) := by
            change
              eTgt.hom
                (((TopCat.Presheaf.stalkFunctor C z).map
                    ((Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ).hom)
                  (eSrc.inv
                    (TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C)
                      ((Opens.map sZ).obj U) z hzMap unitSection))) = _
            rw [stalkCompIso_inv_germ_apply
              (ℱ := (((sZ⁻¹).obj G).presheaf)) (x := z)
              (U := ((Opens.map sZ).obj U)) (hx := hzMap) (s := unitSection)]
    _ =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) ((Opens.map sZ).obj U) z hzMap s := by
        exact subsetSheaf_counit_on_pullback_unit_underlying_germ_eq
          (C := C) (ℱ := ℱ) (z := z) (U := U) (hzMap := hzMap) (s := s)

/-- Helper for Lemma 6.32.1: after forgetting algebraic structure, the explicit pullback-unit germ
in the actual pullback stalk becomes the corresponding underlying germ. -/
private theorem subsetSheaf_pullback_unit_underlying_germ_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzMap : z ∈ (Opens.map sZ).obj U)
    (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
    let unitSection :
        CC ((((sZ⁻¹).obj G).presheaf).obj (op ((Opens.map sZ).obj U))) :=
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app G).1.app (op U)) s)
    let eMid := stalkCompIso z (forget C) (((sZ⁻¹).obj G).presheaf)
    eMid.hom
      ((((sZ⁻¹).obj G).presheaf).germ ((Opens.map sZ).obj U) z hzMap unitSection) =
      TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C)
        ((Opens.map sZ).obj U) z hzMap unitSection := by
  let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
  let unitSection :
      CC ((((sZ⁻¹).obj G).presheaf).obj (op ((Opens.map sZ).obj U))) :=
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app G).1.app (op U)) s)
  let eMid := stalkCompIso z (forget C) (((sZ⁻¹).obj G).presheaf)
  -- This is the target-side specialization of `stalkCompIso_hom_germ_apply`.
  change (stalkCompIso z (forget C) (((sZ⁻¹).obj G).presheaf)).hom
      ((((sZ⁻¹).obj G).presheaf).germ ((Opens.map sZ).obj U) z hzMap unitSection) =
    TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C)
      ((Opens.map sZ).obj U) z hzMap unitSection
  exact
    (stalkCompIso_hom_germ_apply
      (ℱ := (((sZ⁻¹).obj G).presheaf)) (x := z)
      (U := ((Opens.map sZ).obj U)) (hx := hzMap) (s := unitSection))

/-- Helper for Lemma 6.32.1: once the underlying pullback-stalk computation is known, the
target-side stalk comparison recovers the corresponding `C`-valued pullback-unit germ. -/
private theorem subsetSheaf_stalkPullbackIso_germ_eq_of_underlying_eq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (z : TopCat.of Z) (U : Opens X)
    (hzU : sZ z ∈ U) (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U)))
    (hunder :
      let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
      let hzMap : z ∈ (Opens.map sZ).obj U := by
        simpa [TopCat.subsetInclusion] using hzU
      let eMid := stalkCompIso z (forget C) (((sZ⁻¹).obj G).presheaf)
      eMid.hom
        (((TopCat.Sheaf.stalkPullbackIso sZ G z).hom)
          (G.presheaf.germ U (sZ z) hzU s)) =
        TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C)
          ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app G).1.app (op U)) s)) :
    let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
    let hzMap : z ∈ (Opens.map sZ).obj U := by
      simpa [TopCat.subsetInclusion] using hzU
    ((TopCat.Sheaf.stalkPullbackIso sZ G z).hom)
      (G.presheaf.germ U (sZ z) hzU s) =
      (((sZ⁻¹).obj G).presheaf).germ ((Opens.map sZ).obj U) z hzMap
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app G).1.app (op U)) s) := by
  let G : TopCat.Sheaf C X := (Sheaf.pushforward C sZ).obj ℱ
  have hzMap : z ∈ (Opens.map sZ).obj U := by
    simpa [TopCat.subsetInclusion] using hzU
  let eMid := stalkCompIso z (forget C) (((sZ⁻¹).obj G).presheaf)
  -- Apply the faithful target-side stalk comparison and compare both images with the underlying
  -- pullback-unit germ formula.
  apply (Iso.toEquiv eMid).injective
  calc
    eMid.hom
        (((TopCat.Sheaf.stalkPullbackIso sZ G z).hom)
          (G.presheaf.germ U (sZ z) hzU s))
        =
      TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C)
        ((Opens.map sZ).obj U) z hzMap
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app G).1.app (op U)) s) := by
            exact hunder
    _ =
      eMid.hom
        ((((sZ⁻¹).obj G).presheaf).germ ((Opens.map sZ).obj U) z hzMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction C sZ).unit.app G).1.app (op U)) s)) := by
            symm
            exact
              subsetSheaf_pullback_unit_underlying_germ_eq
                (C := C) (ℱ := ℱ) (z := z) (U := U) (hzMap := hzMap) (s := s)

/-- Helper for Lemma 6.32.1: a section-level equality for a Type-valued owner map immediately
induces the corresponding stalk-level equality on the chosen germ. -/
private theorem subsetSheaf_owner_stalk_bridge_of_section_eq
    {mid : TopCat.Sheaf (Type u) (TopCat.of Z)}
    (G : TopCat.Sheaf C X) (z : TopCat.of Z) (V : Opens (TopCat.of Z))
    (hzV : z ∈ V) (midSection : mid.presheaf.obj (op V))
    (unitSection : CC ((((sZ⁻¹).obj G).presheaf).obj (op V)))
    (α : mid ⟶ underlyingTypeSheaf (C := C) (((sZ⁻¹).obj G)))
    (hα : (α.1.app (op V)) midSection = unitSection) :
    ((TopCat.Presheaf.stalkFunctor (Type u) z).map α.1)
      (TopCat.Presheaf.germ mid.presheaf V z hzV midSection) =
      TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C) V z hzV unitSection := by
  -- Transport the chosen germ through the stalk map, then rewrite the resulting section.
  calc
    ((TopCat.Presheaf.stalkFunctor (Type u) z).map α.1)
      (TopCat.Presheaf.germ mid.presheaf V z hzV midSection) =
      TopCat.Presheaf.germ
        ((underlyingTypeSheaf (C := C) (((sZ⁻¹).obj G))).presheaf)
        V z hzV ((α.1.app (op V)) midSection) := by
        simpa [underlyingTypeSheaf] using
          (TopCat.Presheaf.stalkFunctor_map_germ_apply V z hzV α.1 midSection)
    _ =
      TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C) V z hzV unitSection := by
        simpa [underlyingTypeSheaf] using congrArg
          (fun t ↦
            TopCat.Presheaf.germ ((((sZ⁻¹).obj G).presheaf) ⋙ forget C) V z hzV t)
          hα

/-- Helper for Lemma 6.32.1: forgetting the inverse pullback comparison evaluates sectionwise as
the underlying inverse pullback section map. -/
private theorem underlyingTypeSheaf_mapIso_inv_app_apply {Y : TopCat.{u}}
    {ℱ 𝒢 : TopCat.Sheaf C Y} (e : ℱ ≅ 𝒢) (U : Opens Y)
    (s : CC (𝒢.1.obj (op U))) :
    (((underlyingTypeSheaf_mapIso (C := C) e.symm).hom).1.app (op U)) s =
      ((e.inv).1.app (op U)) s := by
  -- Rewrite the inverse section map as the hom of the underlying isomorphism for `e.symm`.
  simpa using
    (underlyingTypeSheaf_mapIso_hom_app_apply (C := C)
      (e := e.symm) (U := U) (s := s))

/-- Helper for Lemma 6.32.1: on stalk germs, the underlying inverse of a sheaf isomorphism sends
the underlying germ of a section to the underlying germ of its inverse image section. -/
private theorem underlyingTypeSheaf_mapIso_inv_stalk_germ_apply {Y : TopCat.{u}}
    {ℱ 𝒢 : TopCat.Sheaf C Y} (e : ℱ ≅ 𝒢) (V : Opens Y) (y : Y) (hy : y ∈ V)
    (s : CC (𝒢.1.obj (op V))) :
    ((TopCat.Presheaf.stalkFunctor (Type u) y).map
        ((underlyingTypeSheaf_mapIso (C := C) e.symm).hom).1)
      (TopCat.Presheaf.germ (𝒢.presheaf ⋙ forget C) V y hy s) =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) V y hy
        (((e.inv).1.app (op V)) s) := by
  -- Move the underlying germ across the underlying inverse stalk map, then rewrite the section
  -- using the section-level inverse comparison.
  calc
    ((TopCat.Presheaf.stalkFunctor (Type u) y).map
        ((underlyingTypeSheaf_mapIso (C := C) e.symm).hom).1)
      (TopCat.Presheaf.germ (𝒢.presheaf ⋙ forget C) V y hy s) =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) V y hy
        ((((underlyingTypeSheaf_mapIso (C := C) e.symm).hom).1.app (op V)) s) := by
          simpa [underlyingTypeSheaf] using
            (TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy
              (((underlyingTypeSheaf_mapIso (C := C) e.symm).hom).1) s)
    _ =
      TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) V y hy
        (((e.inv).1.app (op V)) s) := by
          simpa using congrArg
            (fun t ↦ TopCat.Presheaf.germ (ℱ.presheaf ⋙ forget C) V y hy t)
            (underlyingTypeSheaf_mapIso_inv_app_apply (C := C)
              (e := e) (U := V) (s := s))

/-- Helper for Lemma 6.32.1: on stalks, the symmetric image of a sheaf isomorphism under
`stalkFunctor.mapIso` is definitionally the stalk map of the inverse component. -/
private theorem stalkFunctor_mapIso_symm_hom_eq_map_inv {Y : TopCat.{u}}
    {ℱ 𝒢 : TopCat.Sheaf C Y} (e : ℱ ≅ 𝒢) (y : Y) :
    ((TopCat.Presheaf.stalkFunctor C y).mapIso
        ((TopCat.Sheaf.forget C Y).mapIso e)).symm.hom =
      (TopCat.Presheaf.stalkFunctor C y).map
        ((TopCat.Sheaf.forget C Y).map e.inv) := by
  rfl

/-- Helper for Lemma 6.32.1: on `C`-valued stalks, the inverse pullback comparison carries a
sheafified germ to the corresponding germ in the actual pullback sheaf. -/
private theorem subsetSheaf_pullbackIsoInvStalkMapGermApply {Y T : TopCat.{u}}
    [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology Y) C]
    (f : Y ⟶ T) (𝒢 : T.Sheaf C) (W : Opens Y) (y : Y) (hy : y ∈ W)
    (t :
      CC
        ((sheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget C T ⋙ TopCat.Presheaf.pullback C f).obj 𝒢)).obj (op W))) :
    ((TopCat.Presheaf.stalkFunctor C y).map
        ((TopCat.Sheaf.forget C Y).map
          ((TopCat.Sheaf.pullbackIso C f).inv.app 𝒢)))
      ((TopCat.Presheaf.germ
          (sheafify (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.forget C T ⋙ TopCat.Presheaf.pullback C f).obj 𝒢))
          W y hy) t) =
      (((f⁻¹).obj 𝒢).presheaf).germ W y hy
        ((((TopCat.Sheaf.pullbackIso C f).inv.app 𝒢).1.app (op W)) t) := by
  -- This is the `C`-valued specialization of `stalkFunctor_map_germ_apply` for `pullbackIso.inv`.
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy
      ((TopCat.Sheaf.forget C Y).map
        ((TopCat.Sheaf.pullbackIso C f).inv.app 𝒢)) t)

/-- Helper for Lemma 6.32.1: for algebraic-structure-valued sheaves, the sheafification unit on
stalks sends a germ to the corresponding sheafified germ. -/
private theorem toSheafify_stalkMapGermApplyOfAlgebraicStructure {Y : TopCat.{u}}
    [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology Y) C]
    (ℱ : Y.Presheaf C) (W : Opens Y) (y : Y) (hy : y ∈ W)
    (t : CC (ℱ.obj (op W))) :
    ((TopCat.Presheaf.stalkFunctor C y).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) ℱ))
      (ℱ.germ W y hy t) =
      (TopCat.Presheaf.germ (sheafify (Opens.grothendieckTopology Y) ℱ) W y hy)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y) ℱ).app (op W) t) := by
  -- This is the `C`-valued specialization of `stalkFunctor_map_germ_apply` for the sheafification
  -- unit.
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) ℱ) t)

/-- Helper for Lemma 6.32.1: in the subset-inclusion situation, the inverse Type-valued pullback
comparison sends the sheafified presheaf pullback-unit section of the forgotten pushed-forward
sheaf to the genuine pullback-unit section. -/
private theorem subsetSheaf_pullbackIsoInvToSheafifyUnitSectionEq
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) (U : Opens X)
    (s : CC ((((Sheaf.pushforward C sZ).obj ℱ).presheaf).obj (op U))) :
    let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) := underlyingTypeSheaf ℱ
    let Gₜ := (Sheaf.pushforward (Type u) sZ).obj ℱₜ
    (((TopCat.Sheaf.pullbackIso (Type u) sZ).inv.app Gₜ).1.app
        (op ((Opens.map sZ).obj U)))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of Z))
          ((TopCat.Sheaf.forget (Type u) X ⋙ TopCat.Presheaf.pullback (Type u) sZ).obj Gₜ)).app
          (op ((Opens.map sZ).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app Gₜ.1).app
            (op U)) s)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) sZ).unit.app Gₜ).1.app
          (op U)) s) := by
  -- This is the already-proved Type-valued middle-leg normalization for the forgotten
  -- pushed-forward sheaf.
  simpa [underlyingTypeSheaf] using
    (subsetSheaf_pullback_middle_section_eq (C := C) (ℱ := ℱ) (U := U) (s := s))

/-- Owner theorem: for the subset inclusion `s : Z ↪ X`, the counit
`i^{-1} i_* ℱ ⟶ ℱ` is an isomorphism for any sheaf of algebraic structures on `Z`.
The set-valued and abelian-group clauses are specializations of this owner statement. -/
theorem subsetSheaf_pullback_pushforward_counit_isIso
    (ℱ : TopCat.Sheaf C (TopCat.of Z)) :
    IsIso ((Sheaf.pullbackPushforwardAdjunction C sZ).counit.app ℱ) := by
  -- This is the imported owner theorem for subset inclusions, specialized to `sZ`.
  let _ :
      ∀ {X₁ : Opens X} (S : (Opens.grothendieckTopology X).Cover X₁),
        HasLimitsOfShape (WalkingMulticospan S.shape) C := by
    intro X₁ S
    exact HasLimits.has_limits_of_shape (C := C) (WalkingMulticospan S.shape)
  let _ :
      ∀ (X₁ : Opens X), IsCofiltered ((Opens.grothendieckTopology X).Cover X₁) := by
    intro X₁
    let _ : SemilatticeInf ((Opens.grothendieckTopology X).Cover X₁) := inferInstance
    let _ : Nonempty ((Opens.grothendieckTopology X).Cover X₁) := inferInstance
    exact CategoryTheory.isCofiltered_of_semilatticeInf_nonempty _
  let _ :
      ∀ (X₁ : Opens X), IsFiltered ((Opens.grothendieckTopology X).Cover X₁)ᵒᵖ := by
    intro X₁
    exact
      CategoryTheory.isFiltered_op_of_isCofiltered
        (C := (Opens.grothendieckTopology X).Cover X₁)
  let _ :
      ∀ {X₁ : Opens X} (S : (Opens.grothendieckTopology X).Cover X₁),
        PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget C) := by
    intro X₁ S
    exact PreservesLimitsOfSize.preservesLimitsOfShape (F := forget C)
  let _ :
      ∀ (P : (Opens X)ᵒᵖ ⥤ C) (X₁ : Opens X) (S : (Opens.grothendieckTopology X).Cover X₁),
        HasMultiequalizer (S.index P) := by
    intro P X₁ S
    change HasLimit (S.index P).multicospan
    exact HasLimitsOfShape.has_limit (C := C) (J := WalkingMulticospan S.shape)
      (S.index P).multicospan
  let _ :
      ∀ (X₁ : Opens X), HasColimitsOfShape ((Opens.grothendieckTopology X).Cover X₁)ᵒᵖ C := by
    intro X₁
    exact
      HasColimits.hasColimitsOfShape (C := C)
        (((Opens.grothendieckTopology X).Cover X₁)ᵒᵖ)
  let _ :
      ∀ (X₁ : Opens X),
        PreservesColimitsOfShape ((Opens.grothendieckTopology X).Cover X₁)ᵒᵖ (forget C) := by
    intro X₁
    infer_instance
  letI :
      (CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) C).IsRightAdjoint :=
    CategoryTheory.sheafToPresheaf_isRightAdjoint
      (J := Opens.grothendieckTopology X) (D := C)
  letI := subsetSheafPushforward_counit_isIso (X := X) (C := C) Z
  change IsIso ((Sheaf.pullbackPushforwardAdjunction C (X.subsetInclusion Z)).counit.app ℱ)
  infer_instance

/-- Helper for Lemma 6.32.1: for a sheaf of algebraic structures on `Z`, the filtered stalk of its
pushforward at a point outside `Z` is terminal. -/
private theorem subsetSheaf_pushforward_filteredStalk_isTerminal_of_not_mem
    (hZ : IsClosed Z) (ℱ : TopCat.Sheaf C (TopCat.of Z))
    {x : X} (hx : x ∉ Z) :
    IsIso
      (terminal.from
        (filteredStalk x
          ((Sheaf.pushforward C iZ).obj ℱ).presheaf)) := by
  let F := ((Sheaf.pushforward C iZ).obj ℱ).presheaf
  let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
    { obj := ℱ.presheaf ⋙ forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
  let e :
      (forget C).obj (filteredStalk x F) ≅ TopCat.Presheaf.stalk (F ⋙ forget C) x :=
    stalkCompIso x (forget C) F
  have hType :
      IsIso (terminal.from (TopCat.Presheaf.stalk (F ⋙ forget C) x)) := by
    -- The underlying-set stalk is exactly the stalk from the set-valued specialization.
    simpa [F] using
      (closedSubsetTypeSheaf_pushforward_stalk_unique_of_not_mem
        (X := X) (Z := Z) hZ ℱₜ (x := x) hx)
  have hUnderlying :
      IsIso (terminal.from ((forget C).obj (filteredStalk x F))) := by
    have hcomp :
        e.hom ≫ terminal.from (TopCat.Presheaf.stalk (F ⋙ forget C) x) =
          terminal.from ((forget C).obj (filteredStalk x F)) := by
      apply terminalIsTerminal.hom_ext
    rw [← hcomp]
    infer_instance
  have hForgetMap :
      IsIso ((forget C).map (terminal.from (filteredStalk x F))) := by
    have hcomp :
        ((forget C).map (terminal.from (filteredStalk x F))) ≫
            (PreservesTerminal.iso (forget C)).hom =
          terminal.from ((forget C).obj (filteredStalk x F)) := by
      apply terminalIsTerminal.hom_ext
    have hEq :
        (forget C).map (terminal.from (filteredStalk x F)) =
          terminal.from ((forget C).obj (filteredStalk x F)) ≫
            (PreservesTerminal.iso (forget C)).inv := by
      apply (cancel_mono (PreservesTerminal.iso (forget C)).hom).1
      calc
        ((forget C).map (terminal.from (filteredStalk x F))) ≫
            (PreservesTerminal.iso (forget C)).hom
            = terminal.from ((forget C).obj (filteredStalk x F)) := hcomp
        _ =
            (terminal.from ((forget C).obj (filteredStalk x F)) ≫
              (PreservesTerminal.iso (forget C)).inv) ≫
                (PreservesTerminal.iso (forget C)).hom := by
                  symm
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦ terminal.from ((forget C).obj (filteredStalk x F)) ≫ k)
                      (CategoryTheory.Iso.inv_hom_id (PreservesTerminal.iso (forget C)))
    rw [hEq]
    infer_instance
  -- Reflect the underlying isomorphism back to `C`.
  exact isIso_of_reflects_iso (terminal.from (filteredStalk x F)) (forget C)

/- Set-valued specialization: for sheaves of sets on `Z`, the counit `i^{-1} i_* ℱ ⟶ ℱ` is the
direct `Type` specialization of the owner theorem above. -/
section

variable (ℱ : TopCat.Sheaf (Type u) (TopCat.of Z))

#check
  (show IsIso ((Sheaf.pullbackPushforwardAdjunction (Type u) sZ).counit.app ℱ) from
    subsetSheaf_pullback_pushforward_counit_isIso ℱ)

end

-- Proof sketch: the abelian-group version is the same counit map as in the set-valued case, now
-- taken in `AddCommGrpCat`; the stalk computation on points of `Z` identifies it with the
-- identity on every stalk.
/- Abelian-group specialization: on abelian sheaves over `Z`, the counit
`i^{-1} i_* ℱ ⟶ ℱ` is the `AddCommGrpCat` specialization of the same owner theorem. -/
section

variable (ℱ : TopCat.Sheaf AddCommGrpCat (TopCat.of Z))

#check
  (show IsIso ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat sZ).counit.app ℱ) from
    subsetSheaf_pullback_pushforward_counit_isIso ℱ)

end

-- Proof sketch: outside `Z`, the pushforward sheaf is already the zero object on a sufficiently
-- small neighbourhood disjoint from `Z`; taking the filtered colimit defining the stalk preserves
-- this zero object in `AddCommGrpCat`.
/-- Consequence of Lemma 6.32.1 (2): if `x ∉ Z`, then the stalk of the pushforward of an abelian sheaf on the
closed subset `Z` is zero. -/
theorem closedSubsetAbelianSheaf_pushforward_stalk_isZero_of_not_mem
    (hZ : IsClosed Z) (ℱ : TopCat.Sheaf AddCommGrpCat (TopCat.of Z))
    {x : X} (hx : x ∉ Z) :
    IsZero
      (((Sheaf.pushforward AddCommGrpCat
          iZ).obj
        ℱ).presheaf.stalk x) := by
  -- Translate the terminal-stalk statement from the algebraic-structure owner theorem into zero.
  simpa [filteredStalk_eq_stalk, addCommGrpCat_isIso_terminal_from_iff_isZero] using
    (subsetSheaf_pushforward_filteredStalk_isTerminal_of_not_mem
      (X := X) (Z := Z) (C := AddCommGrpCat) hZ ℱ hx)

end

section

variable {C : Type v} [Category.{u} C]
variable {FC : C → C → Type u} {CC : C → Type u}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
variable [IsAlgebraicStructure C (forget C)]

-- Proof sketch: as in the set-valued case, a point outside `Z` has a neighbourhood disjoint from
-- `Z`, so the pushforward sheaf evaluates on the empty open there; for sheaves of algebraic
-- structures, sections over the empty open form the final object, and the forgetful functor to
-- `Type` reduces the filtered-stalk claim to the corresponding statement for sets.
/-- Consequence of Lemma 6.32.1 (3): if `x ∉ Z`, then the chapter filtered stalk of the pushforward of a sheaf
of algebraic structures on the closed subset `Z` is terminal; equivalently, its canonical map to
the terminal object is an isomorphism. -/
theorem closedSubsetSheaf_pushforward_stalk_isTerminal_of_not_mem
    (hZ : IsClosed Z) (ℱ : TopCat.Sheaf C (TopCat.of Z))
    {x : X} (hx : x ∉ Z) :
    IsIso
      (terminal.from
        (filteredStalk x
          ((Sheaf.pushforward C
              iZ).obj
            ℱ).presheaf)) := by
  let F := ((Sheaf.pushforward C iZ).obj ℱ).presheaf
  let ℱₜ : TopCat.Sheaf (Type u) (TopCat.of Z) :=
    { obj := ℱ.presheaf ⋙ forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget C) ℱ.presheaf).mp ℱ.2 }
  let e :
      (forget C).obj (filteredStalk x F) ≅ TopCat.Presheaf.stalk (F ⋙ forget C) x :=
    stalkCompIso x (forget C) F
  have hType :
      IsIso (terminal.from (TopCat.Presheaf.stalk (F ⋙ forget C) x)) := by
    -- The underlying-set stalk is exactly the stalk from the set-valued specialization.
    simpa [F] using
      (closedSubsetTypeSheaf_pushforward_stalk_unique_of_not_mem
        (X := X) (Z := Z) hZ ℱₜ (x := x) hx)
  have hUnderlying :
      IsIso (terminal.from ((forget C).obj (filteredStalk x F))) := by
    have hcomp :
        e.hom ≫ terminal.from (TopCat.Presheaf.stalk (F ⋙ forget C) x) =
          terminal.from ((forget C).obj (filteredStalk x F)) := by
      apply terminalIsTerminal.hom_ext
    rw [← hcomp]
    infer_instance
  have hForgetMap :
      IsIso ((forget C).map (terminal.from (filteredStalk x F))) := by
    have hcomp :
        ((forget C).map (terminal.from (filteredStalk x F))) ≫
            (PreservesTerminal.iso (forget C)).hom =
          terminal.from ((forget C).obj (filteredStalk x F)) := by
      apply terminalIsTerminal.hom_ext
    have hEq :
        (forget C).map (terminal.from (filteredStalk x F)) =
          terminal.from ((forget C).obj (filteredStalk x F)) ≫
            (PreservesTerminal.iso (forget C)).inv := by
      apply (cancel_mono (PreservesTerminal.iso (forget C)).hom).1
      calc
        ((forget C).map (terminal.from (filteredStalk x F))) ≫
            (PreservesTerminal.iso (forget C)).hom
            = terminal.from ((forget C).obj (filteredStalk x F)) := hcomp
        _ =
            (terminal.from ((forget C).obj (filteredStalk x F)) ≫
              (PreservesTerminal.iso (forget C)).inv) ≫
                (PreservesTerminal.iso (forget C)).hom := by
                  symm
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦ terminal.from ((forget C).obj (filteredStalk x F)) ≫ k)
                      (CategoryTheory.Iso.inv_hom_id (PreservesTerminal.iso (forget C)))
    rw [hEq]
    infer_instance
  -- Reflect the underlying isomorphism back to `C`.
  exact isIso_of_reflects_iso (terminal.from (filteredStalk x F)) (forget C)

end

end
