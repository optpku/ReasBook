module

public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.ClosedSubsetInclusion
public import stacks_project.Chap06.Definition_6_15_1
public import stacks_project.Chap06.Lemma_6_13_1
public import stacks_project.Chap06.Lemma_6_21_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite Set TopCat TopologicalSpace
open TopCat.Presheaf.stalkPushforward
open TopCat.Sheaf

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe v u

section

variable {X : TopCat.{v}}
variable {C : Type u} [Category.{v} C]
variable {FC : C → C → Type v} {CC : C → Type v}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory.{v} C FC]
variable [IsAlgebraicStructure C (forget C)]
variable (Z : Set X)

local instance preservesLimits_forgetType_6_32_4 :
    PreservesLimits (CategoryTheory.forget (Type v)) :=
  CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeHom

local instance preservesFilteredColimits_forgetType_6_32_4 :
    PreservesFilteredColimits (CategoryTheory.forget (Type v)) := by
  letI : PreservesColimits (CategoryTheory.forget (Type v)) :=
    CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeHom
  exact PreservesColimits.preservesFilteredColimits (CategoryTheory.forget (Type v))

local instance reflectsIsos_forgetType_6_32_4 :
    (CategoryTheory.forget (Type v)).ReflectsIsomorphisms :=
  CategoryTheory.instReflectsIsomorphismsForgetTypeHom

local instance faithful_forgetType_6_32_4 :
    (CategoryTheory.forget (Type v)).Faithful := inferInstance

/- Domain-style sampling for Lemma 6.32.4:
- primary domain: pushforward of sheaves along the inclusion of a closed subset in `TopCat`;
- sampled owner declarations:
  `TopCat.closedSubsetInclusion`,
  `TopCat.subsetInclusion`,
  `Sheaf.pushforward`,
  `Sheaf.pullbackPushforwardAdjunction`,
  `subsetSheaf_pullback_pushforward_counit_isIso`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`,
  `filteredStalk`;
- owner abstraction: the ambient owner map is `X.subsetInclusion Z`, while the numbered Stacks
  item is its closed-subset specialization `X.closedSubsetInclusion Z`; the public theorem is the
  fully-faithfulness of the induced sheaf pushforward on algebraic-structure-valued sheaves;
- primitive data: the subset `Z : Set X`, its canonical inclusion into `X`, and the existing
  pullback/pushforward adjunction on sheaves for the algebraic-structure pair `(C, forget C)`;
- derived API: the subset-level fully faithful companion theorem obtained canonically from the
  counit-isomorphism owner theorem of Lemma `6.32.1`, the source-facing essential-image criterion
  in terms of `filteredStalk`, and the ordinary-stalk reformulation only as a bridge under the
  stronger `[HasColimits C]` hypothesis.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma about direct image from a closed subset;
- `core/canonical`: `X.subsetInclusion Z` together with `Sheaf.pushforward`;
- `bridge/view`: the closed-subset specialization `X.closedSubsetInclusion Z` and the adjunction
  theorem turning the counit isomorphism into full faithfulness. -/

local notation "sZ" => X.subsetInclusion Z

local notation "iZ" => X.closedSubsetInclusion Z

/-- Helper for Lemma 6.32.4: if an ambient open set is disjoint from `Z`, then its pullback along
the closed-subset inclusion is the empty open of `Z`. -/
private theorem closedSubsetInclusion_obj_eq_bot_of_disjoint {U : Opens X}
    (hU : (U : Set X) ⊆ Zᶜ) :
    (Opens.map iZ).obj U = ⊥ := by
  -- A point of the pulled-back open would lie both in `U` and in `Z`, contradicting disjointness.
  ext z
  constructor
  · intro hz
    exact False.elim (hU hz z.2)
  · intro hz
    exact False.elim hz

/-- Helper for Lemma 6.32.4: over any ambient open disjoint from `Z`, the pushforward sheaf of
sets evaluates to a singleton. -/
private noncomputable def closedSubsetTypeSheaf_pushforward_obj_isTerminal_of_disjoint
    (ℱ : TopCat.Sheaf (Type v) (TopCat.of Z)) {U : Opens X} (hU : (U : Set X) ⊆ Zᶜ) :
    IsTerminal ((((Sheaf.pushforward (Type v) iZ).obj ℱ).presheaf).obj (op U)) := by
  -- Rewrite the pulled-back open to `⊥`, where a sheaf has terminal sections.
  change IsTerminal (ℱ.presheaf.obj (op ((Opens.map iZ).obj U)))
  simpa [closedSubsetInclusion_obj_eq_bot_of_disjoint (X := X) (Z := Z) hU] using
    ℱ.isTerminalOfEqEmpty (closedSubsetInclusion_obj_eq_bot_of_disjoint (X := X) (Z := Z) hU)

/-- Helper for Lemma 6.32.4: over any ambient open disjoint from `Z`, the pushforward sheaf of
sets has a unique section. -/
private noncomputable abbrev closedSubsetTypeSheaf_pushforward_obj_unique_of_disjoint
    (ℱ : TopCat.Sheaf (Type v) (TopCat.of Z)) {U : Opens X} (hU : (U : Set X) ⊆ Zᶜ) :
    Unique ((((Sheaf.pushforward (Type v) iZ).obj ℱ).presheaf).obj (op U)) :=
  CategoryTheory.Limits.Types.isTerminalEquivUnique _
    (closedSubsetTypeSheaf_pushforward_obj_isTerminal_of_disjoint
      (X := X) (Z := Z) ℱ hU)

/-- Helper for Lemma 6.32.4: at any point outside `Z`, the stalk of a set-valued pushforward from
the closed subset is terminal. -/
private theorem closedSubsetTypeSheaf_pushforward_stalk_unique_of_not_mem
    (hZ : IsClosed Z) (ℱ : TopCat.Sheaf (Type v) (TopCat.of Z))
    {x : X} (hx : x ∉ Z) :
    IsIso
      (terminal.from
        (((Sheaf.pushforward (Type v)
            iZ).obj
          ℱ).presheaf.stalk x)) := by
  let ℱ' := ((Sheaf.pushforward (Type v) iZ).obj ℱ).presheaf
  let U₀ : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hxU₀ : x ∈ U₀ := hx
  let hU₀ :
      Unique (ℱ'.obj (op U₀)) :=
    closedSubsetTypeSheaf_pushforward_obj_unique_of_disjoint (X := X) (Z := Z) ℱ
      (by
        intro y hy
        show y ∈ Zᶜ
        exact hy)
  -- Reduce the stalk to a singleton type by restricting germs to a common disjoint neighborhood.
  rw [CategoryTheory.isIso_iff_bijective]
  constructor
  · intro s t hst
    rcases ℱ'.germ_exist x s with ⟨U₁, hxU₁, s₁, rfl⟩
    rcases ℱ'.germ_exist x t with ⟨U₂, hxU₂, t₂, rfl⟩
    let W : Opens X := U₀ ⊓ U₁ ⊓ U₂
    have hxW : x ∈ W := ⟨⟨hxU₀, hxU₁⟩, hxU₂⟩
    have hWdisjoint : (W : Set X) ⊆ Zᶜ := by
      intro y hy
      show y ∈ Zᶜ
      exact hy.1.1
    let hW :
        Unique (ℱ'.obj (op W)) :=
      closedSubsetTypeSheaf_pushforward_obj_unique_of_disjoint
        (X := X) (Z := Z) ℱ hWdisjoint
    let iWU₁ : W ⟶ U₁ := homOfLE (by intro y hy; exact hy.1.2)
    let iWU₂ : W ⟶ U₂ := homOfLE (by intro y hy; exact hy.2)
    have hrestr :
        ℱ'.map iWU₁.op s₁ = ℱ'.map iWU₂.op t₂ := by
      letI := hW
      exact Subsingleton.elim _ _
    -- The common restriction is unique on the disjoint neighborhood `W`.
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

/-- Helper for Lemma 6.32.4: pushforwards from the closed subset have terminal filtered stalks at
points outside `Z`. -/
private theorem closedSubsetSheaf_pushforward_stalk_isTerminal_of_not_mem
    (hZ : IsClosed Z) (ℱ : TopCat.Sheaf C (TopCat.of Z))
    {x : X} (hx : x ∉ Z) :
    IsIso
      (terminal.from
        (filteredStalk x
          ((Sheaf.pushforward C
              iZ).obj
            ℱ).presheaf)) := by
  let F := ((Sheaf.pushforward C iZ).obj ℱ).presheaf
  let ℱₜ : TopCat.Sheaf (Type v) (TopCat.of Z) :=
    { obj := ℱ.presheaf ⋙ CategoryTheory.forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (CategoryTheory.forget C) ℱ.presheaf).mp ℱ.2 }
  let e :
      (CategoryTheory.forget C).obj (filteredStalk x F) ≅
        TopCat.Presheaf.stalk (F ⋙ CategoryTheory.forget C) x :=
    stalkCompIso x (CategoryTheory.forget C) F
  have hType :
      IsIso (terminal.from (TopCat.Presheaf.stalk (F ⋙ CategoryTheory.forget C) x)) := by
    -- The underlying-set stalk is the set-valued closed-subset specialization.
    simpa [F] using
      (closedSubsetTypeSheaf_pushforward_stalk_unique_of_not_mem
        (X := X) (Z := Z) hZ ℱₜ (x := x) hx)
  have hUnderlying :
      IsIso (terminal.from ((CategoryTheory.forget C).obj (filteredStalk x F))) := by
    -- Transport terminality across the canonical comparison between filtered stalks and forgotten
    -- ordinary stalks.
    have hcomp :
        e.hom ≫ terminal.from (TopCat.Presheaf.stalk (F ⋙ CategoryTheory.forget C) x) =
          terminal.from ((CategoryTheory.forget C).obj (filteredStalk x F)) := by
      apply terminalIsTerminal.hom_ext
    rw [← hcomp]
    infer_instance
  have hForgetMap :
      IsIso ((CategoryTheory.forget C).map (terminal.from (filteredStalk x F))) := by
    -- Rewrite the forgotten terminal morphism into the canonical terminal map in `Type`.
    have hcomp :
        ((CategoryTheory.forget C).map (terminal.from (filteredStalk x F))) ≫
            (PreservesTerminal.iso (CategoryTheory.forget C)).hom =
          terminal.from ((CategoryTheory.forget C).obj (filteredStalk x F)) := by
      apply terminalIsTerminal.hom_ext
    have hEq :
        (CategoryTheory.forget C).map (terminal.from (filteredStalk x F)) =
          terminal.from ((CategoryTheory.forget C).obj (filteredStalk x F)) ≫
            (PreservesTerminal.iso (CategoryTheory.forget C)).inv := by
      apply (cancel_mono (PreservesTerminal.iso (CategoryTheory.forget C)).hom).1
      calc
        ((CategoryTheory.forget C).map (terminal.from (filteredStalk x F))) ≫
            (PreservesTerminal.iso (CategoryTheory.forget C)).hom
            = terminal.from ((CategoryTheory.forget C).obj (filteredStalk x F)) := hcomp
        _ =
            (terminal.from ((CategoryTheory.forget C).obj (filteredStalk x F)) ≫
              (PreservesTerminal.iso (CategoryTheory.forget C)).inv) ≫
                (PreservesTerminal.iso (CategoryTheory.forget C)).hom := by
                  symm
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦ terminal.from ((CategoryTheory.forget C).obj (filteredStalk x F)) ≫ k)
                      (CategoryTheory.Iso.inv_hom_id
                        (PreservesTerminal.iso (CategoryTheory.forget C)))
    rw [hEq]
    simpa using hUnderlying
  -- Reflect the terminality of the underlying type back to `C`.
  exact isIso_of_reflects_iso (terminal.from (filteredStalk x F)) (CategoryTheory.forget C)

/-- Helper for Lemma 6.32.4: an open subset of the closed subspace `Z` is represented in `X` by
removing the image of its closed complement. -/
private noncomputable def closedSubsetAmbientOpen
    (hZ : IsClosed Z) (W : Opens (TopCat.of Z)) : Opens X where
  carrier := (Subtype.val '' ((W : Set (TopCat.of Z))ᶜ))ᶜ
  is_open' := by
    -- The complement of the image of a closed subset of the closed subspace is open in `X`.
    refine (hZ.isClosedMap_subtype_val _ ?_).isOpen_compl
    exact W.2.isClosed_compl

/-- Helper for Lemma 6.32.4: pulling the canonical ambient representative back to `Z` recovers the
original open subset. -/
private theorem closedSubsetAmbientOpen_pullback_eq
    (hZ : IsClosed Z) (W : Opens (TopCat.of Z)) :
    (Opens.map iZ).obj (closedSubsetAmbientOpen (X := X) (Z := Z) hZ W) = W := by
  -- A point of `Z` lies in the ambient representative exactly when it is not in the closed
  -- complement that was removed.
  ext z
  constructor
  · intro hz
    by_contra hzW
    exact hz ⟨z, hzW, rfl⟩
  · intro hzW
    intro hzImage
    rcases hzImage with ⟨z', hz'W, hzEq⟩
    exact hz'W (Subtype.ext hzEq ▸ hzW)

/-- Helper for Lemma 6.32.4: the ambient representative of the pullback of an ambient open is that
open together with the complement of `Z`. -/
private theorem closedSubsetAmbientOpen_map_eq_sup
    (hZ : IsClosed Z) (U : Opens X) :
    closedSubsetAmbientOpen (X := X) (Z := Z) hZ ((Opens.map iZ).obj U) =
      U ⊔ ⟨Zᶜ, hZ.isOpen_compl⟩ := by
  -- On points of `Z` this is exactly membership in `U`; away from `Z` both sides are automatic.
  ext x
  by_cases hxZ : x ∈ Z
  · constructor
    · intro hx
      have hxU : x ∈ U := by
        by_contra hxU
        apply hx
        refine ⟨⟨x, hxZ⟩, ?_, rfl⟩
        simpa [TopCat.closedSubsetInclusion, TopCat.subsetInclusion] using hxU
      exact Or.inl hxU
    · intro hx
      rcases hx with hxU | hxCompl
      · intro hxImage
        rcases hxImage with ⟨z, hz, rfl⟩
        exact hz (by simpa [TopCat.closedSubsetInclusion, TopCat.subsetInclusion] using hxU)
      · exact False.elim (hxCompl hxZ)
  · constructor
    · intro _hx
      exact Or.inr hxZ
    · intro _hx
      intro hxImage
      rcases hxImage with ⟨z, _hz, rfl⟩
      exact hxZ z.2

/-- Helper for Lemma 6.32.4: the ambient representative is monotone with respect to inclusion of
opens in the closed subspace. -/
private theorem closedSubsetAmbientOpen_mono
    (hZ : IsClosed Z) {W₁ W₂ : Opens (TopCat.of Z)} (h : W₁ ≤ W₂) :
    closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₁ ≤
      closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₂ := by
  -- A point excluded by the larger complement is already excluded by the smaller complement.
  intro x hx
  intro hxImage
  apply hx
  rcases hxImage with ⟨z, hzW₂, rfl⟩
  exact ⟨z, fun hzW₁ ↦ hzW₂ (h hzW₁), rfl⟩

/-- Helper for Lemma 6.32.4: the ambient representative of the empty open of `Z` is the
complement of `Z`. -/
private theorem closedSubsetAmbientOpen_bot_eq
    (hZ : IsClosed Z) :
    closedSubsetAmbientOpen (X := X) (Z := Z) hZ (⊥ : Opens (TopCat.of Z)) =
      ⟨Zᶜ, hZ.isOpen_compl⟩ := by
  -- Inside `Z` there are no points of the empty open, while outside `Z` every point remains.
  ext x
  constructor
  · intro hx
    intro hxZ
    exact hx ⟨⟨x, hxZ⟩, by
      intro hxbot
      exact hxbot, rfl⟩
  · intro hx
    intro hxImage
    rcases hxImage with ⟨z, _hz, rfl⟩
    exact hx z.2

/-- Helper for Lemma 6.32.4: the ambient representative sends intersections in `Z` to ambient
intersections in `X`. -/
private theorem closedSubsetAmbientOpen_inf_eq
    (hZ : IsClosed Z) (W₁ W₂ : Opens (TopCat.of Z)) :
    closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W₁ ⊓ W₂) =
      closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₁ ⊓
        closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₂ := by
  -- On `Z` this is the usual intersection criterion; away from `Z` every ambient representative
  -- already contains the point.
  ext x
  by_cases hxZ : x ∈ Z
  · constructor
    · intro hx
      constructor
      · intro hxImage
        apply hx
        rcases hxImage with ⟨z, hzW₁, rfl⟩
        exact ⟨z, fun hz ↦ hzW₁ hz.1, rfl⟩
      · intro hxImage
        apply hx
        rcases hxImage with ⟨z, hzW₂, rfl⟩
        exact ⟨z, fun hz ↦ hzW₂ hz.2, rfl⟩
    · intro hx
      intro hxImage
      rcases hx with ⟨hx₁, hx₂⟩
      rcases hxImage with ⟨z, hzInf, rfl⟩
      by_cases hzW₁ : z ∈ W₁
      · have hzW₂ : z ∉ W₂ := fun hzW₂ ↦ hzInf ⟨hzW₁, hzW₂⟩
        exact hx₂ ⟨z, hzW₂, rfl⟩
      · exact hx₁ ⟨z, hzW₁, rfl⟩
  · constructor
    · intro hx
      constructor
      · intro hxImage
        apply hx
        rcases hxImage with ⟨z, hzW₁, rfl⟩
        exact ⟨z, fun hz ↦ hzW₁ hz.1, rfl⟩
      · intro hxImage
        apply hx
        rcases hxImage with ⟨z, hzW₂, rfl⟩
        exact ⟨z, fun hz ↦ hzW₂ hz.2, rfl⟩
    · intro _hx
      intro hxImage
      rcases hxImage with ⟨z, _hz, rfl⟩
      exact hxZ z.2

/-- Helper for Lemma 6.32.4: for a nonempty family of opens in `Z`, the ambient representative
commutes with the covering supremum. -/
private theorem closedSubsetAmbientOpen_iSup_eq_of_nonempty
    (hZ : IsClosed Z) {ι : Type*} [Nonempty ι] (W : ι → Opens (TopCat.of Z)) :
    closedSubsetAmbientOpen (X := X) (Z := Z) hZ (iSup W) =
      iSup fun i ↦ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W i) := by
  -- Compare pointwise, splitting into points on `Z` and outside `Z`.
  ext x
  by_cases hxZ : x ∈ Z
  · constructor
    · intro hx
      -- On `Z`, membership is equivalent to belonging to some member of the family.
      by_cases hmem : ∃ i, ((⟨x, hxZ⟩ : TopCat.of Z) ∈ W i)
      · rcases hmem with ⟨i, hi⟩
        simp only [SetLike.mem_coe, Opens.mem_iSup]
        exact ⟨i, by
          intro hxImage
          rcases hxImage with ⟨z, hz, rfl⟩
          exact hz hi⟩
      · exfalso
        apply hx
        refine ⟨⟨x, hxZ⟩, ?_, rfl⟩
        simpa [Opens.mem_iSup] using hmem
    · intro hx
      -- Any ambient representative on the right already forces membership in the ambient union.
      rcases (by
        simpa [Opens.mem_iSup] using hx :
          ∃ i, x ∈ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W i)) with ⟨i, hi⟩
      intro hxImage
      rcases hxImage with ⟨z, hz, rfl⟩
      have hzWi : z ∈ W i := by
        by_contra hzWi
        exact hi ⟨z, hzWi, rfl⟩
      exact hz (by simpa [Opens.mem_iSup] using ⟨i, hzWi⟩)
  · constructor
    · intro _
      -- Outside `Z`, every ambient representative already contains the point.
      rcases Classical.choice (inferInstance : Nonempty ι) with i
      simp only [SetLike.mem_coe, Opens.mem_iSup]
      refine ⟨i, ?_⟩
      intro hxImage
      rcases hxImage with ⟨z, _, rfl⟩
      exact hxZ z.2
    · intro _
      intro hxImage
      rcases hxImage with ⟨z, _, rfl⟩
      exact hxZ z.2

/-- Helper for Lemma 6.32.4: a sheaf isomorphism induces an isomorphism on filtered stalks. -/
private noncomputable abbrev filteredStalkIsoOfIso
    {ℱ 𝒢 : X.Sheaf C} (e : ℱ ≅ 𝒢) (x : X) :
    filteredStalk x ℱ.presheaf ≅ filteredStalk x 𝒢.presheaf :=
  (filteredStalkFunctor x).mapIso ((TopCat.Sheaf.forget C X).mapIso e)

/-- Helper for Lemma 6.32.4: terminality of a filtered stalk transports across a sheaf
isomorphism. -/
private theorem filteredStalk_terminal_from_isIso_of_iso
    {ℱ 𝒢 : X.Sheaf C} (e : ℱ ≅ 𝒢) (x : X)
    [IsIso (terminal.from (filteredStalk x ℱ.presheaf))] :
    IsIso (terminal.from (filteredStalk x 𝒢.presheaf)) := by
  -- Turn the source terminal morphism into terminality and transport it along the stalk
  -- isomorphism induced by `e`.
  let hSourceTerminal : IsTerminal (filteredStalk x ℱ.presheaf) :=
    IsTerminal.ofIso terminalIsTerminal
      (asIso (terminal.from (filteredStalk x ℱ.presheaf))).symm
  let hTargetTerminal : IsTerminal (filteredStalk x 𝒢.presheaf) :=
    IsTerminal.ofIso hSourceTerminal (filteredStalkIsoOfIso (C := C) e x)
  exact isIso_of_isTerminal hTargetTerminal terminalIsTerminal
    (terminal.from (filteredStalk x 𝒢.presheaf))

/-- Helper for Lemma 6.32.4: terminality of a filtered stalk forces terminality of the underlying
set-valued stalk. -/
private theorem underlying_stalk_terminal_of_filtered_terminal
    (𝒢 : X.Sheaf C) (x : X)
    [IsIso (terminal.from (filteredStalk x 𝒢.presheaf))] :
    IsIso (terminal.from (TopCat.Presheaf.stalk (𝒢.presheaf ⋙ forget C) x)) := by
  let e :
      (CategoryTheory.forget C).obj (filteredStalk x 𝒢.presheaf) ≅
        TopCat.Presheaf.stalk (𝒢.presheaf ⋙ CategoryTheory.forget C) x :=
    stalkCompIso x (CategoryTheory.forget C) 𝒢.presheaf
  have hType :
      IsIso (terminal.from ((CategoryTheory.forget C).obj (filteredStalk x 𝒢.presheaf))) := by
    -- Rewrite the forgetful image of the terminal map into the canonical terminal map in `Type`.
    have hForgetMap :
        IsIso ((CategoryTheory.forget C).map (terminal.from (filteredStalk x 𝒢.presheaf))) := by
      infer_instance
    have hcomp :
        ((CategoryTheory.forget C).map (terminal.from (filteredStalk x 𝒢.presheaf))) ≫
            (PreservesTerminal.iso (CategoryTheory.forget C)).hom =
          terminal.from ((CategoryTheory.forget C).obj (filteredStalk x 𝒢.presheaf)) := by
      apply terminalIsTerminal.hom_ext
    rw [← hcomp]
    infer_instance
  -- Turn the underlying terminal map into terminality and transport it along the comparison
  -- isomorphism from filtered stalks to underlying set-valued stalks.
  let hSource :
      IsTerminal ((CategoryTheory.forget C).obj (filteredStalk x 𝒢.presheaf)) :=
    IsTerminal.ofIso terminalIsTerminal
      (asIso (terminal.from ((CategoryTheory.forget C).obj (filteredStalk x 𝒢.presheaf)))).symm
  let hTarget :
      IsTerminal (TopCat.Presheaf.stalk (𝒢.presheaf ⋙ CategoryTheory.forget C) x) :=
    IsTerminal.ofIso hSource e
  exact isIso_of_isTerminal hTarget terminalIsTerminal
    (terminal.from (TopCat.Presheaf.stalk (𝒢.presheaf ⋙ CategoryTheory.forget C) x))

section

omit C FC CC

/-- Helper for Lemma 6.32.4: every section object of the terminal `Type`-valued sheaf is a
singleton. -/
private noncomputable abbrev terminal_type_sheaf_sections_unique
    (U : Opens X) :
    Unique (((⊤_ TopCat.Sheaf (Type v) X).presheaf).obj (op U)) := by
  let e :
      (⊤_ TopCat.Sheaf (Type v) X) ≅
        Sheaf.terminal (Opens.grothendieckTopology X) Types.isTerminalPUnit :=
    terminalIsTerminal.uniqueUpToIso
      (Sheaf.isTerminalTerminal (Opens.grothendieckTopology X) Types.isTerminalPUnit)
  let eU :
      (((⊤_ TopCat.Sheaf (Type v) X).presheaf).obj (op U)) ≅ PUnit :=
    ((TopCat.Sheaf.forget (Type v) X).mapIso e).app (op U)
  -- Evaluate the terminal-sheaf comparison at `U` and transport the singleton structure of
  -- `PUnit` back to the section object.
  exact eU.toEquiv.unique

/-- Helper for Lemma 6.32.4: the stalk of the terminal `Type`-valued sheaf is a singleton. -/
private noncomputable abbrev terminal_type_sheaf_stalk_unique
    (x : X) :
    Unique (((⊤_ TopCat.Sheaf (Type v) X).presheaf).stalk x) := by
  let F := ((⊤_ TopCat.Sheaf (Type v) X).presheaf)
  let hUniqueTop := terminal_type_sheaf_sections_unique (X := X) (⊤ : Opens X)
  let sTop : F.obj (op (⊤ : Opens X)) := hUniqueTop.default
  refine
    { default := F.germ (⊤ : Opens X) x (by simp) sTop
      uniq := ?_ }
  intro s
  rcases F.germ_exist x s with ⟨U, hxU, t, rfl⟩
  let iU : U ⟶ (⊤ : Opens X) := homOfLE (by intro y hy; simp)
  -- Every local section of the terminal sheaf agrees with the restriction of the unique top
  -- section, so the corresponding germs coincide.
  have ht : t = F.map iU.op sTop := by
    let hUniqueU := terminal_type_sheaf_sections_unique (X := X) U
    exact Subsingleton.elim _ _
  calc
    F.germ U x hxU t = F.germ U x hxU (F.map iU.op sTop) := by rw [ht]
    _ = F.germ (⊤ : Opens X) x (by simp) sTop := by
      simpa [iU] using (F.germ_res_apply iU x hxU sTop)

include C FC CC

end

/-- Helper for Lemma 6.32.4: after restricting the underlying `Type`-valued sheaf to an open set
contained in `Zᶜ`, every stalk remains terminal. -/
private theorem pullback_stalk_terminal_of_disjoint_open
    (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf)))
    {V : Opens X} (hV : (V : Set X) ⊆ Zᶜ) (y : TopCat.of V) :
    IsIso
      (terminal.from
        (((TopCat.Sheaf.pullback (Type v) (X.subsetInclusion (V : Set X))).obj
            { obj := 𝒢.presheaf ⋙ CategoryTheory.forget C
              property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
                (CategoryTheory.forget C) 𝒢.presheaf).mp 𝒢.2 }).presheaf.stalk y)) := by
  let jV : TopCat.of V ⟶ X := X.subsetInclusion (V : Set X)
  let 𝒢ₜ : X.Sheaf (Type v) :=
    { obj := 𝒢.presheaf ⋙ CategoryTheory.forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (CategoryTheory.forget C) 𝒢.presheaf).mp 𝒢.2 }
  let GV : TopCat.Sheaf (Type v) (TopCat.of V) :=
    (TopCat.Sheaf.pullback (Type v) jV).obj 𝒢ₜ
  have hy : jV y ∉ Z := by
    -- Points of the open subspace lie outside `Z` by the disjointness hypothesis.
    exact hV y.2
  have hFiltered :
      IsIso (terminal.from (filteredStalk (jV y) 𝒢.presheaf)) :=
    h𝒢 (jV y) hy
  let _ : IsIso (terminal.from (filteredStalk (jV y) 𝒢.presheaf)) := hFiltered
  have hAmbient :
      IsIso
        (terminal.from
          (TopCat.Presheaf.stalk (𝒢.presheaf ⋙ CategoryTheory.forget C) (jV y))) :=
    underlying_stalk_terminal_of_filtered_terminal (C := C) 𝒢 (jV y)
  let _ :
      IsIso
        (terminal.from
          (TopCat.Presheaf.stalk (𝒢.presheaf ⋙ CategoryTheory.forget C) (jV y))) :=
    hAmbient
  let hAmbientTerminal :
      IsTerminal (TopCat.Presheaf.stalk (𝒢.presheaf ⋙ CategoryTheory.forget C) (jV y)) :=
    IsTerminal.ofIso terminalIsTerminal
      (asIso
        (terminal.from
          (TopCat.Presheaf.stalk (𝒢.presheaf ⋙ CategoryTheory.forget C) (jV y)))).symm
  let hPullbackTerminal : IsTerminal (GV.presheaf.stalk y) :=
    IsTerminal.ofIso hAmbientTerminal
      (TopCat.Sheaf.stalkPullbackIso jV 𝒢ₜ y)
  -- The stalk comparison identifies the pullback stalk with the ambient stalk at `y`.
  simpa [GV, jV] using
    (isIso_of_isTerminal hPullbackTerminal terminalIsTerminal
      (terminal.from (GV.presheaf.stalk y)))

/-- Helper for Lemma 6.32.4: if all stalks of a `Type`-valued sheaf are terminal, then its top
sections are terminal. -/
private theorem pullback_terminal_map_isIso_of_stalkwise_terminal
    {V : Opens X} (GV : TopCat.Sheaf (Type v) (TopCat.of V))
    (hGV : ∀ y : TopCat.of V, IsIso (terminal.from (GV.presheaf.stalk y))) :
    IsIso (terminal.from (GV.presheaf.obj (op (⊤ : Opens (TopCat.of V))))) := by
  have hf :
      ∀ x : (⊤ : Opens (TopCat.of V)),
        IsIso
          ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map
            (terminal.from GV).1) := by
    intro x
    have hSrcMap : IsIso (terminal.from (GV.presheaf.stalk x.1)) := hGV x.1
    let _ : IsIso (terminal.from (GV.presheaf.stalk x.1)) := hSrcMap
    let hSrcTerminal : IsTerminal (GV.presheaf.stalk x.1) :=
      IsTerminal.ofIso terminalIsTerminal
        (asIso (terminal.from (GV.presheaf.stalk x.1))).symm
    let hSrc : Unique (GV.presheaf.stalk x.1) :=
      CategoryTheory.Limits.Types.isTerminalEquivUnique _ hSrcTerminal
    let hTgt :
        Unique (((⊤_ TopCat.Sheaf (Type v) (TopCat.of V)).presheaf).stalk x.1) :=
      terminal_type_sheaf_stalk_unique (X := TopCat.of V) x.1
    -- The stalk map lands in a singleton, and its source is already singleton.
    rw [CategoryTheory.isIso_iff_bijective]
    constructor
    · intro a b _hab
      exact (hSrc.uniq a).trans (hSrc.uniq b).symm
    · intro b
      refine ⟨hSrc.default, ?_⟩
      exact (hTgt.uniq _).trans (hTgt.uniq _).symm
  let _ :
      ∀ x : (⊤ : Opens (TopCat.of V)),
        IsIso
          ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map
            (terminal.from GV).1) := hf
  have hTopMap :
      IsIso (((terminal.from GV).1.app (op (⊤ : Opens (TopCat.of V))))) :=
    TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
      (terminal.from GV) (⊤ : Opens (TopCat.of V))
  let hTerminalSections :
      Unique (((⊤_ TopCat.Sheaf (Type v) (TopCat.of V)).presheaf).obj
        (op (⊤ : Opens (TopCat.of V)))) :=
    terminal_type_sheaf_sections_unique (X := TopCat.of V) (⊤ : Opens (TopCat.of V))
  rw [CategoryTheory.isIso_iff_bijective] at hTopMap
  let hSourceSections : Unique (GV.presheaf.obj (op (⊤ : Opens (TopCat.of V)))) := by
    refine
      { default := Classical.choose (hTopMap.2 hTerminalSections.default)
        uniq := ?_ }
    intro s
    apply hTopMap.1
    letI := hTerminalSections
    exact Subsingleton.elim _ _
  let hSourceTerminal :
      IsTerminal (GV.presheaf.obj (op (⊤ : Opens (TopCat.of V)))) :=
    (CategoryTheory.Limits.Types.isTerminalEquivUnique _).symm hSourceSections
  -- Once the top section set is a singleton, the canonical map to the terminal type is an
  -- isomorphism.
  exact isIso_of_isTerminal hSourceTerminal terminalIsTerminal
    (terminal.from (GV.presheaf.obj (op (⊤ : Opens (TopCat.of V)))))

/-- Helper for Lemma 6.32.4: on any open set contained in `Zᶜ`, the underlying set of sections is
singleton once all filtered stalks away from `Z` are terminal. -/
private theorem underlying_sections_terminal_of_disjoint_open
    (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf)))
    {V : Opens X} (hV : (V : Set X) ⊆ Zᶜ) :
    IsIso (terminal.from (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (Opposite.op V)))) := by
  let jV : TopCat.of V ⟶ X := X.subsetInclusion (V : Set X)
  let hOpenEmbedding : Topology.IsOpenEmbedding jV := by
    simpa [jV, TopCat.subsetInclusion] using TopologicalSpace.Opens.isOpenEmbedding V
  let 𝒢ₜ : X.Sheaf (Type v) :=
    { obj := 𝒢.presheaf ⋙ CategoryTheory.forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (CategoryTheory.forget C) 𝒢.presheaf).mp 𝒢.2 }
  let GV : TopCat.Sheaf (Type v) (TopCat.of V) :=
    (hOpenEmbedding.sheafPullback (Type v)).obj 𝒢ₜ
  have hGV :
      ∀ y : TopCat.of V, IsIso (terminal.from (GV.presheaf.stalk y)) := by
    intro y
    have hPullback :
        IsIso
          (terminal.from
            (((TopCat.Sheaf.pullback (Type v) jV).obj
                𝒢ₜ).presheaf.stalk y)) :=
      pullback_stalk_terminal_of_disjoint_open (C := C) (Z := Z) 𝒢 h𝒢 hV y
    let _ :
        IsIso
          (terminal.from
            (((TopCat.Sheaf.pullback (Type v) jV).obj
                𝒢ₜ).presheaf.stalk y)) :=
      hPullback
    let hPullbackTerminal :
        IsTerminal
          (((TopCat.Sheaf.pullback (Type v) jV).obj
              𝒢ₜ).presheaf.stalk y) :=
      IsTerminal.ofIso terminalIsTerminal
        (asIso
          (terminal.from
            (((TopCat.Sheaf.pullback (Type v) jV).obj
                𝒢ₜ).presheaf.stalk y))).symm
    let hRestrictedTerminal : IsTerminal (GV.presheaf.stalk y) :=
      IsTerminal.ofIso hPullbackTerminal
        ((TopCat.Presheaf.stalkFunctor (Type v) y).mapIso
          ((TopCat.Sheaf.forget (Type v) (TopCat.of V)).mapIso
            ((hOpenEmbedding.sheafPullbackIso (Type v)).app 𝒢ₜ)))
    exact isIso_of_isTerminal hRestrictedTerminal terminalIsTerminal
      (terminal.from (GV.presheaf.stalk y))
  have hTop :
      IsIso (terminal.from (GV.presheaf.obj (op (⊤ : Opens (TopCat.of V))))) :=
    pullback_terminal_map_isIso_of_stalkwise_terminal (X := X) GV hGV
  let _ :
      IsIso (terminal.from (GV.presheaf.obj (op (⊤ : Opens (TopCat.of V))))) :=
    hTop
  -- For the naive pullback along the open embedding `V ↪ X`, the top open is exactly `V`.
  change IsIso
    (terminal.from
      (𝒢ₜ.1.obj
        (op
          (hOpenEmbedding.functor.obj
            (⊤ : Opens (TopCat.of V)))))) at hTop
  have hTopOpen : hOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of V)) = V := by
    -- The image of the top open under the inclusion functor is the ambient open `V` itself.
    ext x
    constructor
    · intro hx
      rcases hx with ⟨x', -, rfl⟩
      exact x'.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  rw [hTopOpen] at hTop
  simpa [𝒢ₜ] using hTop

/-- Helper for Lemma 6.32.4: on any open set disjoint from `Z`, the section object of `𝒢` is
terminal once all filtered stalks away from `Z` are terminal. -/
private theorem sections_terminal_of_disjoint_open
    (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf)))
    {V : Opens X} (hV : (V : Set X) ⊆ Zᶜ) :
    IsIso (terminal.from (𝒢.presheaf.obj (Opposite.op V))) := by
  -- First prove the underlying `Type`-valued section set is a singleton.
  have hUnderlying :
      IsIso (terminal.from (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (Opposite.op V)))) :=
    underlying_sections_terminal_of_disjoint_open (C := C) (Z := Z) 𝒢 h𝒢 hV
  let _ :
      IsIso (terminal.from (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (Opposite.op V)))) :=
    hUnderlying
  have hForgetMap :
      IsIso ((CategoryTheory.forget C).map (terminal.from (𝒢.presheaf.obj (Opposite.op V)))) := by
    -- Rewrite the forgetful image of the terminal map into the canonical terminal map in `Type`.
    have hcomp :
        ((CategoryTheory.forget C).map (terminal.from (𝒢.presheaf.obj (Opposite.op V)))) ≫
            (PreservesTerminal.iso (CategoryTheory.forget C)).hom =
          terminal.from ((CategoryTheory.forget C).obj (𝒢.presheaf.obj (Opposite.op V))) := by
      apply terminalIsTerminal.hom_ext
    have hEq :
        (CategoryTheory.forget C).map (terminal.from (𝒢.presheaf.obj (Opposite.op V))) =
          terminal.from ((CategoryTheory.forget C).obj (𝒢.presheaf.obj (Opposite.op V))) ≫
            (PreservesTerminal.iso (CategoryTheory.forget C)).inv := by
      apply (cancel_mono (PreservesTerminal.iso (CategoryTheory.forget C)).hom).1
      calc
        ((CategoryTheory.forget C).map (terminal.from (𝒢.presheaf.obj (Opposite.op V)))) ≫
            (PreservesTerminal.iso (CategoryTheory.forget C)).hom
            = terminal.from ((CategoryTheory.forget C).obj (𝒢.presheaf.obj (Opposite.op V))) := hcomp
        _ =
            (terminal.from ((CategoryTheory.forget C).obj (𝒢.presheaf.obj (Opposite.op V))) ≫
              (PreservesTerminal.iso (CategoryTheory.forget C)).inv) ≫
                (PreservesTerminal.iso (CategoryTheory.forget C)).hom := by
                  symm
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦
                        terminal.from ((CategoryTheory.forget C).obj
                          (𝒢.presheaf.obj (Opposite.op V))) ≫ k)
                      (CategoryTheory.Iso.inv_hom_id
                        (PreservesTerminal.iso (CategoryTheory.forget C)))
    rw [hEq]
    simpa using hUnderlying
  -- Reflect the singleton underlying section set back to `C`.
  exact isIso_of_reflects_iso
    (terminal.from (𝒢.presheaf.obj (Opposite.op V))) (CategoryTheory.forget C)

/-- Helper for Lemma 6.32.4: on an ambient open disjoint from `Z`, the underlying set of sections
is a singleton. -/
private noncomputable abbrev underlying_sections_unique_of_disjoint_open
    (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf)))
    {V : Opens X} (hV : (V : Set X) ⊆ Zᶜ) :
    Unique (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (Opposite.op V))) := by
  -- Convert the terminal morphism into an `IsTerminal` witness, then package it as `Unique`.
  have hTerminalMap :
      IsIso (terminal.from (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (Opposite.op V)))) :=
    underlying_sections_terminal_of_disjoint_open (C := C) (Z := Z) 𝒢 h𝒢 hV
  let _ :
      IsIso (terminal.from (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (Opposite.op V)))) :=
    hTerminalMap
  let hTerminal :
      IsTerminal (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (Opposite.op V))) :=
    IsTerminal.ofIso terminalIsTerminal
      ((asIso
        (terminal.from
          (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj
            (Opposite.op V))))).symm)
  exact CategoryTheory.Limits.Types.isTerminalEquivUnique _ hTerminal

/-- Helper for Lemma 6.32.4: restricting from `U ∪ Zᶜ` to `U` is an isomorphism once all stalks
outside `Z` are terminal. -/
private theorem ambient_union_restriction_isIso
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf)))
    (U : Opens X) :
    IsIso
      (𝒢.presheaf.map (homOfLE le_sup_left).op :
        𝒢.presheaf.obj (op (U ⊔ ⟨Zᶜ, hZ.isOpen_compl⟩)) ⟶
          𝒢.presheaf.obj (op U)) := by
  let ZcOpen : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩
  let V : Opens X := U ⊔ ZcOpen
  let 𝒢ₜ : X.Sheaf (Type v) :=
    { obj := 𝒢.presheaf ⋙ CategoryTheory.forget C
      property := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (CategoryTheory.forget C) 𝒢.presheaf).mp 𝒢.2 }
  have hUnderlying :
      IsIso
        ((CategoryTheory.forget C).map
          (𝒢.presheaf.map (homOfLE le_sup_left).op :
            𝒢.presheaf.obj (op V) ⟶ 𝒢.presheaf.obj (op U))) := by
    rw [CategoryTheory.isIso_iff_bijective]
    constructor
    · intro s t hst
      change 𝒢.presheaf.map (homOfLE le_sup_left).op s =
          𝒢.presheaf.map (homOfLE le_sup_left).op t at hst
      let hUniqueCompl :
          Unique (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (op ZcOpen))) :=
        underlying_sections_unique_of_disjoint_open (C := C) (Z := Z) 𝒢 h𝒢
          (V := ZcOpen) (by
            intro x hx
            exact hx)
      -- Compare the two sections on the cover `{U, Zᶜ}`.
      refine 𝒢ₜ.eq_of_locally_eq₂
        (homOfLE (show U ≤ V by exact le_sup_left))
        (homOfLE (show ZcOpen ≤ V by exact le_sup_right))
        (show V ≤ U ⊔ ZcOpen by exact le_rfl)
        s t hst ?_
      letI := hUniqueCompl
      exact Subsingleton.elim _ _
    · intro s
      let hUniqueCompl :
          Unique (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (op ZcOpen))) :=
        underlying_sections_unique_of_disjoint_open (C := C) (Z := Z) 𝒢 h𝒢
          (V := ZcOpen) (by
            intro x hx
            exact hx)
      let sCompl : ((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (op ZcOpen)) := hUniqueCompl.default
      let cover : Bool → Opens X := fun b ↦ if b then U else ZcOpen
      let iUV : ∀ b : Bool, cover b ⟶ V
        | true => homOfLE le_sup_left
        | false => homOfLE le_sup_right
      let sf : ∀ b : Bool, ToType (𝒢.presheaf.obj (op (cover b)))
        | true => s
        | false => sCompl
      have hcompat : TopCat.Presheaf.IsCompatible 𝒢ₜ.presheaf cover sf := by
        intro i j
        cases i <;> cases j
        · rfl
        ·
          let hUniqueInter :
              Unique (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (op (ZcOpen ⊓ U)))) :=
            underlying_sections_unique_of_disjoint_open (C := C) (Z := Z) 𝒢 h𝒢
              (V := ZcOpen ⊓ U) (by
                intro x hx
                exact hx.1)
          letI := hUniqueInter
          simpa [cover, sf] using
            (Subsingleton.elim
              (𝒢ₜ.presheaf.map (Opens.infLELeft ZcOpen U).op sCompl)
              (𝒢ₜ.presheaf.map (Opens.infLERight ZcOpen U).op s))
        ·
          let hUniqueInter :
              Unique (((𝒢.presheaf ⋙ CategoryTheory.forget C).obj (op (U ⊓ ZcOpen)))) :=
            underlying_sections_unique_of_disjoint_open (C := C) (Z := Z) 𝒢 h𝒢
              (V := U ⊓ ZcOpen) (by
                intro x hx
                exact hx.2)
          letI := hUniqueInter
          simpa [cover, sf] using
            (Subsingleton.elim
              (𝒢ₜ.presheaf.map (Opens.infLELeft U ZcOpen).op s)
              (𝒢ₜ.presheaf.map (Opens.infLERight U ZcOpen).op sCompl))
        · rfl
      have hcover : V ≤ iSup cover := by
        intro x hx
        simpa [V, ZcOpen, cover, Opens.mem_iSup, or_comm] using hx
      -- Glue the prescribed section on `U` with the unique section on `Zᶜ`.
      obtain ⟨t, ht, -⟩ := 𝒢ₜ.existsUnique_gluing' (U := cover) (V := V) iUV hcover sf hcompat
      refine ⟨t, ?_⟩
      change 𝒢.presheaf.map (homOfLE le_sup_left).op t = s
      simpa [V, ZcOpen, cover, sf, iUV] using ht true
  let _ :
      IsIso
        ((CategoryTheory.forget C).map
          (𝒢.presheaf.map (homOfLE le_sup_left).op :
            𝒢.presheaf.obj (op V) ⟶ 𝒢.presheaf.obj (op U))) :=
    hUnderlying
  -- Reflect the underlying bijection of section sets back to `C`.
  exact isIso_of_reflects_iso
    (𝒢.presheaf.map (homOfLE le_sup_left).op :
      𝒢.presheaf.obj (op V) ⟶ 𝒢.presheaf.obj (op U))
    (CategoryTheory.forget C)

/-- Helper for Lemma 6.32.4: the ambient-open construction defines an order hom on opens of the
closed subspace. -/
private def closedSubsetAmbientOpenOrderHom
    (hZ : IsClosed Z) : Opens (TopCat.of Z) →o Opens X where
  toFun := closedSubsetAmbientOpen (X := X) (Z := Z) hZ
  monotone' := fun _ _ h ↦ closedSubsetAmbientOpen_mono (X := X) (Z := Z) hZ h

/-- Helper for Lemma 6.32.4: the candidate converse witness presheaf on `Z`, obtained by
evaluating `𝒢` on the canonical ambient representatives of opens of the closed subspace. -/
private noncomputable def closedSubsetRestrictionPresheaf
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C) :
    TopCat.Presheaf C (TopCat.of Z) :=
  (closedSubsetAmbientOpenOrderHom (X := X) (Z := Z) hZ).toFunctor.op ⋙ 𝒢.presheaf

/-- Helper for Lemma 6.32.4: the restriction map for the left intersection inclusion in `Z`
matches the corresponding ambient restriction map after identifying ambient intersections. -/
private theorem closedSubsetAmbientOpen_infLELeft_eq
    (hZ : IsClosed Z) (W₁ W₂ : Opens (TopCat.of Z)) :
    (closedSubsetAmbientOpenOrderHom (X := X) (Z := Z) hZ).toFunctor.map (W₁.infLELeft W₂) =
      eqToHom (closedSubsetAmbientOpen_inf_eq (X := X) (Z := Z) hZ W₁ W₂) ≫
        (closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₁).infLELeft
          (closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₂) := by
  -- `Opens X` is a thin category, so there is a unique inclusion with these source and target.
  apply Subsingleton.elim

/-- Helper for Lemma 6.32.4: the restriction map for the right intersection inclusion in `Z`
matches the corresponding ambient restriction map after identifying ambient intersections. -/
private theorem closedSubsetAmbientOpen_infLERight_eq
    (hZ : IsClosed Z) (W₁ W₂ : Opens (TopCat.of Z)) :
    (closedSubsetAmbientOpenOrderHom (X := X) (Z := Z) hZ).toFunctor.map (W₁.infLERight W₂) =
      eqToHom (closedSubsetAmbientOpen_inf_eq (X := X) (Z := Z) hZ W₁ W₂) ≫
        (closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₁).infLERight
          (closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₂) := by
  -- Again, both sides are the unique inclusion between the same opens.
  apply Subsingleton.elim

/-- Helper for Lemma 6.32.4: after identifying the ambient supremum of a nonempty family, the
restriction map to a member of the family matches the corresponding ambient restriction map. -/
private theorem closedSubsetAmbientOpen_leSupr_eq
    (hZ : IsClosed Z) {ι : Type*} [Nonempty ι] (W : ι → Opens (TopCat.of Z)) (i : ι) :
    (closedSubsetAmbientOpenOrderHom (X := X) (Z := Z) hZ).toFunctor.map (Opens.leSupr W i) =
      Opens.leSupr (fun j ↦ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W j)) i ≫
        eqToHom ((closedSubsetAmbientOpen_iSup_eq_of_nonempty
          (X := X) (Z := Z) hZ W).symm) := by
  -- Thinness of the lattice of opens identifies these two inclusion morphisms.
  apply Subsingleton.elim

/-- Helper for Lemma 6.32.4: compatibility for the explicit restriction presheaf is exactly
compatibility for the same family viewed on the ambient opens of `X`. -/
private theorem closedSubsetAmbientOpen_infLELeft_apply
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C) (W₁ W₂ : Opens (TopCat.of Z))
    (s : ToType (𝒢.presheaf.obj (op (closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₁)))) :
    ((closedSubsetRestrictionPresheaf (X := X) (Z := Z) (C := C) hZ 𝒢).map
        (W₁.infLELeft W₂).op) s =
      𝒢.presheaf.map
        (eqToHom (closedSubsetAmbientOpen_inf_eq (X := X) (Z := Z) hZ W₁ W₂)).op
        (𝒢.presheaf.map
          ((closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₁).infLELeft
            (closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₂)).op s) := by
  -- Evaluate the morphism identity for the left overlap on the forgotten presheaf.
  let Gt : TopCat.Presheaf (Type v) X := 𝒢.presheaf ⋙ CategoryTheory.forget C
  have h :=
    congrArg
      (fun k ↦ (Gt.map k.op) s)
      (closedSubsetAmbientOpen_infLELeft_eq (X := X) (Z := Z) hZ W₁ W₂)
  simpa [Gt, FunctorToTypes.map_comp_apply, closedSubsetRestrictionPresheaf,
    closedSubsetAmbientOpenOrderHom] using h

/-- Helper for Lemma 6.32.4: the right overlap restriction in the explicit restriction presheaf
matches the corresponding ambient restriction map after identifying intersections. -/
private theorem closedSubsetAmbientOpen_infLERight_apply
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C) (W₁ W₂ : Opens (TopCat.of Z))
    (s : ToType (𝒢.presheaf.obj (op (closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₂)))) :
    ((closedSubsetRestrictionPresheaf (X := X) (Z := Z) (C := C) hZ 𝒢).map
        (W₁.infLERight W₂).op) s =
      𝒢.presheaf.map
        (eqToHom (closedSubsetAmbientOpen_inf_eq (X := X) (Z := Z) hZ W₁ W₂)).op
        (𝒢.presheaf.map
          ((closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₁).infLERight
            (closedSubsetAmbientOpen (X := X) (Z := Z) hZ W₂)).op s) := by
  -- Evaluate the morphism identity for the right overlap on the forgotten presheaf.
  let Gt : TopCat.Presheaf (Type v) X := 𝒢.presheaf ⋙ CategoryTheory.forget C
  have h :=
    congrArg
      (fun k ↦ (Gt.map k.op) s)
      (closedSubsetAmbientOpen_infLERight_eq (X := X) (Z := Z) hZ W₁ W₂)
  simpa [Gt, FunctorToTypes.map_comp_apply, closedSubsetRestrictionPresheaf,
    closedSubsetAmbientOpenOrderHom] using h

/-- Helper for Lemma 6.32.4: after identifying the nonempty ambient supremum, the restriction map
to a member of the family is the ambient restriction map on sections. -/
private theorem closedSubsetAmbientOpen_leSupr_apply
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C) {ι : Type*} [Nonempty ι]
    (W : ι → Opens (TopCat.of Z)) (i : ι)
    (s : ToType
      (𝒢.presheaf.obj
        (op (closedSubsetAmbientOpen (X := X) (Z := Z) hZ (iSup W))))) :
    ((closedSubsetRestrictionPresheaf (X := X) (Z := Z) (C := C) hZ 𝒢).map
        (Opens.leSupr W i).op) s =
      𝒢.presheaf.map
        (Opens.leSupr (fun j ↦ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W j)) i).op
        (𝒢.presheaf.map
          (eqToHom ((closedSubsetAmbientOpen_iSup_eq_of_nonempty
            (X := X) (Z := Z) hZ W).symm)).op s) := by
  -- Evaluate the nonempty-cover morphism identity on the forgotten presheaf.
  let Gt : TopCat.Presheaf (Type v) X := 𝒢.presheaf ⋙ CategoryTheory.forget C
  have h :=
    congrArg
      (fun k ↦ (Gt.map k.op) s)
      (closedSubsetAmbientOpen_leSupr_eq (X := X) (Z := Z) hZ W i)
  simpa [Gt, FunctorToTypes.map_comp_apply, closedSubsetRestrictionPresheaf,
    closedSubsetAmbientOpenOrderHom] using h

/-- Helper for Lemma 6.32.4: compatibility for the explicit restriction presheaf is exactly
compatibility for the same family viewed on the ambient opens of `X`. -/
private theorem closedSubsetRestrictionPresheaf_compatible_iff_ambient
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C) {ι : Type*}
    (W : ι → Opens (TopCat.of Z))
    (sf : ∀ i, ToType ((closedSubsetRestrictionPresheaf
      (X := X) (Z := Z) (C := C) hZ 𝒢).obj (op (W i)))) :
    TopCat.Presheaf.IsCompatible
        (closedSubsetRestrictionPresheaf (X := X) (Z := Z) (C := C) hZ 𝒢) W sf ↔
      TopCat.Presheaf.IsCompatible
        𝒢.presheaf (fun i ↦ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W i)) sf := by
  constructor
  · intro h i j
    -- Rewrite the restriction-presheaf compatibility equation into the ambient one and cancel the
    -- common transport through the identified intersection.
    have hij := h i j
    rw [closedSubsetAmbientOpen_infLELeft_apply (X := X) (Z := Z) (C := C) hZ 𝒢 (W i) (W j),
      closedSubsetAmbientOpen_infLERight_apply (X := X) (Z := Z) (C := C) hZ 𝒢 (W i) (W j)] at hij
    exact
      (ConcreteCategory.bijective_of_isIso
        (𝒢.presheaf.map
          (eqToHom (closedSubsetAmbientOpen_inf_eq
            (X := X) (Z := Z) hZ (W i) (W j))).op)).1 hij
  · intro h i j
    -- Apply the common transport to the ambient compatibility equation.
    rw [closedSubsetAmbientOpen_infLELeft_apply (X := X) (Z := Z) (C := C) hZ 𝒢 (W i) (W j),
      closedSubsetAmbientOpen_infLERight_apply (X := X) (Z := Z) (C := C) hZ 𝒢 (W i) (W j)]
    exact congrArg
      (𝒢.presheaf.map
        (eqToHom (closedSubsetAmbientOpen_inf_eq (X := X) (Z := Z) hZ (W i) (W j))).op)
      (h i j)

/-- Helper for Lemma 6.32.4: after transporting along the nonempty-cover ambient supremum
comparison, a gluing on the restriction presheaf is exactly an ambient gluing. -/
private theorem closedSubsetRestrictionPresheaf_isGluing_iff_ambient
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C) {ι : Type*} [Nonempty ι]
    (W : ι → Opens (TopCat.of Z))
    (sf : ∀ i, ToType ((closedSubsetRestrictionPresheaf
      (X := X) (Z := Z) (C := C) hZ 𝒢).obj (op (W i))))
    (s : ToType
      (𝒢.presheaf.obj
        (op (closedSubsetAmbientOpen (X := X) (Z := Z) hZ (iSup W))))) :
    TopCat.Presheaf.IsGluing
        (closedSubsetRestrictionPresheaf (X := X) (Z := Z) (C := C) hZ 𝒢) W sf
        (show ToType ((closedSubsetRestrictionPresheaf
          (X := X) (Z := Z) (C := C) hZ 𝒢).obj (op (iSup W))) from s) ↔
      TopCat.Presheaf.IsGluing
        𝒢.presheaf
        (fun i ↦ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W i))
        sf
        (𝒢.presheaf.map
          (eqToHom ((closedSubsetAmbientOpen_iSup_eq_of_nonempty
            (X := X) (Z := Z) hZ W).symm)).op s) := by
  constructor
  · intro hs i
    -- Rewrite the restriction map from the explicit presheaf to the ambient restriction map.
    simpa [closedSubsetAmbientOpen_leSupr_apply (X := X) (Z := Z) (C := C) hZ 𝒢 W i s] using hs i
  · intro hs i
    -- The ambient gluing equation is the same statement after transporting along the supremum
    -- comparison.
    simpa [closedSubsetAmbientOpen_leSupr_apply (X := X) (Z := Z) (C := C) hZ 𝒢 W i s] using hs i

/-- Helper for Lemma 6.32.4: sections on the complement `Zᶜ` form a singleton once all filtered
stalks away from `Z` are terminal. -/
private noncomputable abbrev closedSubsetComplement_sections_unique
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf))) :
    Unique (ToType (𝒢.presheaf.obj (op (⟨Zᶜ, hZ.isOpen_compl⟩ : Opens X)))) := by
  let ZcOpen : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩
  let hTerminalZc :
      IsIso (terminal.from (𝒢.presheaf.obj (op ZcOpen))) :=
    sections_terminal_of_disjoint_open (C := C) (Z := Z) 𝒢 h𝒢
      (V := ZcOpen) (by intro x hx; exact hx)
  let _ : IsIso (terminal.from (𝒢.presheaf.obj (op ZcOpen))) := hTerminalZc
  let hTerminalObj : IsTerminal (𝒢.presheaf.obj (op ZcOpen)) :=
    IsTerminal.ofIso terminalIsTerminal
      (asIso (terminal.from (𝒢.presheaf.obj (op ZcOpen)))).symm
  exact CategoryTheory.Limits.Concrete.uniqueOfTerminalOfPreserves
    (C := C) (X := 𝒢.presheaf.obj (op ZcOpen)) hTerminalObj

/-- Helper for Lemma 6.32.4: the explicit ambient-open restriction presheaf on `Z` satisfies the
sheaf condition once sections on opens contained in `Zᶜ` are terminal. -/
private theorem closedSubsetRestrictionPresheaf_isSheaf
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf))) :
    (closedSubsetRestrictionPresheaf (X := X) (Z := Z) (C := C) hZ 𝒢).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι W sf hsf
  classical
  by_cases hι : Nonempty ι
  · letI := hι
    -- For a nonempty cover, transport the compatible family to the ambient opens and use the
    -- ambient sheaf `𝒢` to obtain the unique gluing there.
    have hAmbientCompat :
        TopCat.Presheaf.IsCompatible
          𝒢.presheaf (fun i ↦ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W i)) sf :=
      (closedSubsetRestrictionPresheaf_compatible_iff_ambient
        (X := X) (Z := Z) (C := C) hZ 𝒢 W sf).1 hsf
    obtain ⟨t, ht, htuniq⟩ :=
      𝒢.existsUnique_gluing (fun i ↦ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W i))
        sf hAmbientCompat
    let e :
        𝒢.presheaf.obj
            (op (iSup fun i ↦ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W i))) ≅
          𝒢.presheaf.obj
            (op (closedSubsetAmbientOpen (X := X) (Z := Z) hZ (iSup W))) :=
      𝒢.presheaf.mapIso
        (eqToIso
          (closedSubsetAmbientOpen_iSup_eq_of_nonempty (X := X) (Z := Z) hZ W)).op
    let s : ToType
        ((closedSubsetRestrictionPresheaf
          (X := X) (Z := Z) (C := C) hZ 𝒢).obj (op (iSup W))) :=
      e.hom t
    have hsTransport :
        𝒢.presheaf.map
          (eqToHom ((closedSubsetAmbientOpen_iSup_eq_of_nonempty
            (X := X) (Z := Z) hZ W).symm)).op s = t := by
      simpa [s, e] using e.hom_inv_id_apply t
    refine ⟨s, ?_, ?_⟩
    · -- Transport the ambient gluing back across the supremum comparison.
      apply (closedSubsetRestrictionPresheaf_isGluing_iff_ambient
        (X := X) (Z := Z) (C := C) hZ 𝒢 W sf s).2
      have hsTransport' : e.inv s = t := by
        simpa [e] using hsTransport
      intro i
      have hti : 𝒢.presheaf.map
          (Opens.leSupr (fun i ↦ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W i)) i).op
          (e.inv s) = sf i := by
        simpa [hsTransport'] using ht i
      simpa [e] using hti
    · intro s' hs'
      -- Uniqueness reduces to ambient uniqueness after transporting `s'` forward.
      have hs'ambient :
          TopCat.Presheaf.IsGluing
            𝒢.presheaf
            (fun i ↦ closedSubsetAmbientOpen (X := X) (Z := Z) hZ (W i))
            sf
            (𝒢.presheaf.map
              (eqToHom ((closedSubsetAmbientOpen_iSup_eq_of_nonempty
                (X := X) (Z := Z) hZ W).symm)).op s') :=
        (closedSubsetRestrictionPresheaf_isGluing_iff_ambient
          (X := X) (Z := Z) (C := C) hZ 𝒢 W sf s').1 hs'
      have hs'Eq :
          𝒢.presheaf.map
              (eqToHom ((closedSubsetAmbientOpen_iSup_eq_of_nonempty
                (X := X) (Z := Z) hZ W).symm)).op s' = t :=
        htuniq _ hs'ambient
      have hs'Eq' : e.inv s' = t := by
        simpa [e] using hs'Eq
      have hsTransport' : e.inv s = t := by
        simpa [e] using hsTransport
      exact
        (ConcreteCategory.bijective_of_isIso
          e.inv).1
          (hs'Eq'.trans hsTransport'.symm)
  · -- If the cover is empty, the supremum open is `⊥`, whose ambient representative is `Zᶜ`.
    have hbot : iSup W = (⊥ : Opens (TopCat.of Z)) := by
      apply le_antisymm
      · refine iSup_le fun i ↦ ?_
        exact False.elim (hι ⟨i⟩)
      · intro x hx
        exact False.elim hx
    let ZcOpen : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩
    let hUniqueZc :
        Unique (ToType (𝒢.presheaf.obj (op ZcOpen))) :=
      closedSubsetComplement_sections_unique (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢
    let eEmpty :
        ToType ((closedSubsetRestrictionPresheaf
          (X := X) (Z := Z) (C := C) hZ 𝒢).obj (op (iSup W))) ≃
          ToType (𝒢.presheaf.obj (op ZcOpen)) :=
      Equiv.cast (by
        simp [closedSubsetRestrictionPresheaf, closedSubsetAmbientOpenOrderHom, hbot, ZcOpen,
          closedSubsetAmbientOpen_bot_eq (X := X) (Z := Z) hZ])
    refine ⟨?_, ?_, ?_⟩
    · -- The unique section over `Zᶜ` supplies the empty-cover gluing.
      exact eEmpty.symm hUniqueZc.default
    · intro i
      exact False.elim (hι ⟨i⟩)
    · intro s hs
      apply eEmpty.injective
      simpa using (hUniqueZc.uniq (eEmpty s))

/-- Helper for Lemma 6.32.4: the converse witness sheaf on `Z`, obtained from the explicit
ambient-open restriction presheaf. -/
private noncomputable abbrev closedSubsetRestrictionSheaf
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf))) :
    TopCat.Sheaf C (TopCat.of Z) :=
  { obj := closedSubsetRestrictionPresheaf (X := X) (Z := Z) (C := C) hZ 𝒢
    property := closedSubsetRestrictionPresheaf_isSheaf (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢 }

/-- Helper for Lemma 6.32.4: the component of the pushforward comparison from the explicit
restriction sheaf back to the ambient sheaf. -/
private noncomputable def closedSubsetRestrictionSheaf_pushforward_component_hom
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf)))
    (U : Opens X) :
    (((Sheaf.pushforward C iZ).obj
      (closedSubsetRestrictionSheaf (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢)).presheaf.obj (op U)) ⟶
        𝒢.presheaf.obj (op U) :=
  𝒢.presheaf.map
      (eqToHom ((closedSubsetAmbientOpen_map_eq_sup
        (X := X) (Z := Z) hZ U).symm)).op ≫
    𝒢.presheaf.map (homOfLE le_sup_left).op

/-- Helper for Lemma 6.32.4: the comparison component from the pushforward restriction sheaf to
the ambient sheaf is natural in the ambient open set. -/
private theorem closedSubsetRestrictionSheaf_pushforward_component_naturality
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf)))
    {U V : Opens X} (f : U ⟶ V) :
    (((((Sheaf.pushforward C iZ).obj
      (closedSubsetRestrictionSheaf (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢)).presheaf).map f.op) ≫
      closedSubsetRestrictionSheaf_pushforward_component_hom
        (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢 U) =
      (closedSubsetRestrictionSheaf_pushforward_component_hom
        (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢 V) ≫
        𝒢.presheaf.map f.op := by
  -- Both composites are section maps induced by the unique inclusion of opens in `X`.
  apply ConcreteCategory.hom_ext
  intro s
  simpa [closedSubsetRestrictionSheaf_pushforward_component_hom,
    closedSubsetRestrictionSheaf, closedSubsetRestrictionPresheaf, closedSubsetAmbientOpenOrderHom,
    Category.assoc, ← Functor.map_comp] using
    (congrArg
      (fun k ↦ 𝒢.presheaf.map k s)
      (Subsingleton.elim _ _))

/-- Helper for Lemma 6.32.4: pushing forward the explicit restriction sheaf gives back the
original presheaf on `X`. -/
private noncomputable def closedSubsetRestrictionSheaf_pushforward_presheaf_iso
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf))) :
    ((Sheaf.pushforward C iZ).obj
      (closedSubsetRestrictionSheaf (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢)).presheaf ≅
        𝒢.presheaf :=
  NatIso.ofComponents
    (fun U ↦ by
      let _ :
          IsIso
            (𝒢.presheaf.map
              (homOfLE (show U.unop ≤ U.unop ⊔ ⟨Zᶜ, hZ.isOpen_compl⟩ by
                exact le_sup_left)).op :
              𝒢.presheaf.obj (op (U.unop ⊔ ⟨Zᶜ, hZ.isOpen_compl⟩)) ⟶
                𝒢.presheaf.obj (op U.unop)) :=
        ambient_union_restriction_isIso
          (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢 U.unop
      exact
      ((𝒢.presheaf.mapIso
          (eqToIso
            (closedSubsetAmbientOpen_map_eq_sup
              (X := X) (Z := Z) hZ U.unop)).op).symm) ≪≫
        asIso
          (𝒢.presheaf.map
            (homOfLE (show U.unop ≤ U.unop ⊔ ⟨Zᶜ, hZ.isOpen_compl⟩ by
              exact le_sup_left)).op))
    (fun {_ _} f ↦ by
      simpa [closedSubsetRestrictionSheaf_pushforward_component_hom] using
        closedSubsetRestrictionSheaf_pushforward_component_naturality
          (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢 f.unop)

/-- Helper for Lemma 6.32.4: the pushed-forward explicit restriction sheaf is isomorphic to the
original sheaf on `X`. -/
private noncomputable def closedSubsetRestrictionSheaf_pushforward_iso
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C)
    (h𝒢 : ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf))) :
    (Sheaf.pushforward C iZ).obj
      (closedSubsetRestrictionSheaf (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢) ≅ 𝒢 :=
  let e := closedSubsetRestrictionSheaf_pushforward_presheaf_iso
    (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢
  { hom := ⟨e.hom⟩
    inv := ⟨e.inv⟩
    hom_inv_id := by
      -- The sheaf-level inverse identity is the presheaf-level one.
      apply CategoryTheory.Sheaf.hom_ext
      exact e.hom_inv_id
    inv_hom_id := by
      -- The sheaf-level forward identity is the presheaf-level one.
      apply CategoryTheory.Sheaf.hom_ext
      exact e.inv_hom_id }

-- Proof sketch: for a pushforward from the closed subspace, stalks away from `Z` are terminal,
-- equivalently the canonical maps from those stalks to the terminal object are isomorphisms;
-- conversely, if these maps are isomorphisms away from `Z`, then the adjunction map from the
-- pushforward of the restriction back to the original sheaf is an isomorphism.

/-- Lemma 6.32.4 (1): a sheaf of algebraic structures on `X` lies in the essential image of
pushforward from a closed subset `Z` if and only if, at every point of `X \ Z`, the canonical map
from the filtered stalk to the terminal object is an isomorphism. This is the source-facing owner
statement; the ordinary-stalk reformulation is only a bridge once `[HasColimits C]` is available.
-/
theorem closedSubsetSheafPushforward_essImage_iff_filteredStalk_isTerminal_of_not_mem
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C) :
    (Sheaf.pushforward C iZ).essImage 𝒢 ↔
      ∀ x : X, x ∉ Z → IsIso (terminal.from (filteredStalk x 𝒢.presheaf)) := by
  constructor
  · intro h𝒢 x hx
    rcases h𝒢 with ⟨ℱ, ⟨e⟩⟩
    -- Pushforwards from the closed subset have terminal filtered stalks away from `Z`.
    have hSource :
        IsIso
          (terminal.from
            (filteredStalk x
              ((Sheaf.pushforward C iZ).obj ℱ).presheaf)) :=
      closedSubsetSheaf_pushforward_stalk_isTerminal_of_not_mem (C := C) (Z := Z) hZ ℱ hx
    -- Terminality transports across the filtered-stalk isomorphism induced by `e`.
    let _ : IsIso
        (terminal.from
          (filteredStalk x
            ((Sheaf.pushforward C iZ).obj ℱ).presheaf)) := hSource
    exact filteredStalk_terminal_from_isIso_of_iso (C := C) e x
  · intro h𝒢
    -- Route correction: the converse must still exhibit a sheaf on `Z` together with a unit map
    -- whose filtered stalk maps are isomorphisms. The complement-open terminality bridge is now
    -- established by `underlying_sections_terminal_of_disjoint_open` and
    -- `sections_terminal_of_disjoint_open`; the remaining work is to package the explicit
    -- ambient-open restriction sheaf on `Z` and compare its pushforward back to `𝒢`.
    exact ⟨closedSubsetRestrictionSheaf (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢,
      ⟨closedSubsetRestrictionSheaf_pushforward_iso
        (X := X) (Z := Z) (C := C) hZ 𝒢 h𝒢⟩⟩

include FC CC

/-- Lemma 6.32.4 (2): a sheaf of algebraic structures on `X` lies in the essential image of
pushforward from a closed subset `Z` if and only if, at every point of `X \ Z`, the canonical map
from the ordinary stalk to the terminal object is an isomorphism. This is only the
`[HasColimits C]` bridge form of the filtered-stalk owner theorem above. -/
theorem closedSubsetSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem
    [HasColimits.{v} C]
    (hZ : IsClosed Z) (𝒢 : X.Sheaf C) :
    (Sheaf.pushforward C iZ).essImage 𝒢 ↔
      ∀ x : X, x ∉ Z → IsIso (terminal.from (𝒢.presheaf.stalk x)) := by
  simpa [filteredStalk_eq_stalk] using
    (closedSubsetSheafPushforward_essImage_iff_filteredStalk_isTerminal_of_not_mem
      Z hZ 𝒢)

omit FC CC

end
