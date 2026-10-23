module

public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.SheafOfFunctions


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopCat.Presheaf TopCat.Presheaf.Sheafify TopologicalSpace

noncomputable section

universe v

section

variable {X : TopCat.{v}} (F : Presheaf (Type v) X)

/-
Domain-style sampling for Lemma 6.18.1:
- primary domain: sheafification of `Type`-valued presheaves and stalkwise local-germ criteria;
- sampled owner API:
  `TopCat.Presheaf.sheafify`,
  `TopCat.Presheaf.sheafifyStalkIso`,
  `TopCat.Presheaf.toSheafify`,
  `TopCat.Presheaf.Sheafify.isLocallyGerm`;
- best owner abstraction: the bundled sheafification `F.sheafify`, with stalk comparison given by
  `F.sheafifyStalkIso`;
- primitive data: the presheaf `F` and the open set `U`;
- derived API: the concrete subtype realization of `F.sheafify` inside the presheaf of functions
  into stalks, and the induced map on stalks from `F.toSheafify`.

Source/core/bridge triage:
- `source-facing`: the pullback description of sections of `F^#(U)`;
- `core/canonical`: `F.sheafify` together with `F.sheafifyStalkIso`;
- `bridge/view`: the subtype inclusion
  `(subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)`.
-/

-- Proof sketch: use the canonical owner `F.sheafify` for sections of `F^#(U)`, map a section to
-- its family of germs in the stalks of `F^#`, pass to the original stalks via the primitive owner
-- map `F.stalkToFiber` (equivalently the hom of `F.sheafifyStalkIso`), and compare with the local-
-- germ realization inside the product presheaf of stalks.
/-- Helper for Lemma 6.18.1: the stalk-family map `σ` is exactly the underlying dependent function
of a sheafification section. -/
lemma sheafify_section_stalk_family_eq (U : Opens X) (s : F.sheafify.presheaf.obj (op U)) :
    (fun x : U ↦ F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s)) =
      ((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U) s) := by
  -- Evaluate the germ of the sheafification section at each point.
  ext x
  exact TopCat.stalkToFiber_germ (isLocallyGerm F) U x.1 x.2 s

/-- Helper for Lemma 6.18.1: each component map `F_x → Π(F)_x` induced by `F.toSheafify` is
injective. -/
lemma to_stalk_sections_stalk_injective (x : X) :
    Function.Injective (((stalkFunctor (Type v) x).map
      (F.toSheafify ≫
        subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate))) := by
  have h_unit : Function.Injective ((stalkFunctor (Type v) x).map F.toSheafify) := by
    intro a b hab
    obtain ⟨U, hxU, s, rfl⟩ := F.germ_exist x a
    obtain ⟨V, hxV, t, rfl⟩ := F.germ_exist x b
    have hU :
        ((stalkFunctor (Type v) x).map F.toSheafify) (F.germ U x hxU s) =
          F.sheafify.presheaf.germ U x hxU (F.toSheafify.app (op U) s) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU F.toSheafify s
    have hV :
        ((stalkFunctor (Type v) x).map F.toSheafify) (F.germ V x hxV t) =
          F.sheafify.presheaf.germ V x hxV (F.toSheafify.app (op V) t) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV F.toSheafify t
    have hab' :
        F.sheafify.presheaf.germ U x hxU (F.toSheafify.app (op U) s) =
          F.sheafify.presheaf.germ V x hxV (F.toSheafify.app (op V) t) := by
      exact hU.symm.trans (hab.trans hV)
    have hUfiber :
        F.stalkToFiber x (F.sheafify.presheaf.germ U x hxU (F.toSheafify.app (op U) s)) =
          F.germ U x hxU s := by
      simpa [TopCat.Presheaf.toSheafify] using
        (TopCat.stalkToFiber_germ (isLocallyGerm F) U x hxU (F.toSheafify.app (op U) s))
    have hVfiber :
        F.stalkToFiber x (F.sheafify.presheaf.germ V x hxV (F.toSheafify.app (op V) t)) =
          F.germ V x hxV t := by
      simpa [TopCat.Presheaf.toSheafify] using
        (TopCat.stalkToFiber_germ (isLocallyGerm F) V x hxV (F.toSheafify.app (op V) t))
    -- Push equality in the sheafification stalk through `stalkToFiber` to recover equality in `F_x`.
    calc
      F.germ U x hxU s =
        F.stalkToFiber x (F.sheafify.presheaf.germ U x hxU (F.toSheafify.app (op U) s)) := by
          symm
          exact hUfiber
      _ =
        F.stalkToFiber x (F.sheafify.presheaf.germ V x hxV (F.toSheafify.app (op V) t)) := by
          exact congrArg (F.stalkToFiber x) hab'
      _ = F.germ V x hxV t := hVfiber
  have h_subtype :
      Function.Injective ((stalkFunctor (Type v) x).map
        (subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)) := by
    -- The subtype inclusion is injective on each open set, so its stalk maps are injective.
    simpa using
      (stalkFunctor_map_injective_of_app_injective
        (C := Type v)
        (f := subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)
        (x := x)
        (fun U s t hst ↦ Subtype.ext hst))
  intro a b hab
  -- Apply injectivity first on the stalk map of the subtype inclusion, then on the unit map.
  have hab' :
      ((stalkFunctor (Type v) x).map F.toSheafify) a =
        ((stalkFunctor (Type v) x).map F.toSheafify) b := by
    exact h_subtype <| by simpa using hab
  exact h_unit hab'

/-- Helper for Lemma 6.18.1: a stalk family is locally a germ exactly when each stalk value comes
from the image of the component map `F_x → Π(F)_x`. -/
lemma isLocallyGerm_pred_iff_stalkwise_lift
    (U : Opens X) (s : (X.presheafToTypes (fun x ↦ F.stalk x)).obj (op U)) :
    ((isLocallyGerm F).toPrelocalPredicate).pred s ↔
      ∀ x : U, ∃ t : F.stalk x.1,
        (X.presheafToTypes (fun y ↦ F.stalk y)).germ U x.1 x.2 s =
          ((stalkFunctor (Type v) x.1).map
            (F.toSheafify ≫
              subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)) t := by
  constructor
  · intro hs x
    rcases hs x with ⟨V, hxV, iV, g, hg⟩
    refine ⟨F.germ V x.1 hxV g, ?_⟩
    -- Rewrite the stalk image through the actual local germ witness `g`.
    calc
      (X.presheafToTypes (fun y ↦ F.stalk y)).germ U x.1 x.2 s =
          (X.presheafToTypes (fun y ↦ F.stalk y)).germ V x.1 hxV
            (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op V))
              (F.toSheafify.app (op V) g)) := by
                apply (X.presheafToTypes (fun y ↦ F.stalk y)).germ_ext V hxV iV (𝟙 _)
                exact funext fun y ↦ hg y
      _ =
          ((stalkFunctor (Type v) x.1).map
            (F.toSheafify ≫
              subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate))
            (F.germ V x.1 hxV g) := by
              symm
              exact TopCat.Presheaf.stalkFunctor_map_germ_apply V x.1 hxV
                (F.toSheafify ≫
                  subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate) g
  · intro hs
    intro x
    rcases hs x with ⟨t, ht⟩
    rcases F.germ_exist x.1 t with ⟨V, hxV, g, rfl⟩
    have h_germs :
        (X.presheafToTypes (fun y ↦ F.stalk y)).germ U x.1 x.2 s =
          (X.presheafToTypes (fun y ↦ F.stalk y)).germ V x.1 hxV
            (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op V))
              (F.toSheafify.app (op V) g)) := by
      -- Rewrite the stalkwise image condition using the explicit representative of `t`.
      exact ht.trans <|
        TopCat.Presheaf.stalkFunctor_map_germ_apply V x.1 hxV
          (F.toSheafify ≫
            subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate) g
    obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
      (X.presheafToTypes (fun y ↦ F.stalk y)).germ_eq x.1 x.2 hxV _ _ h_germs
    refine ⟨W, hxW, iWU, ?_⟩
    refine ⟨F.map iWV.op g, ?_⟩
    -- Shrink to a neighborhood where the family is literally given by the germs of `g`.
    intro y
    have hy := congrFun hW y
    calc
      s (iWU y) =
        (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op V))
          (F.toSheafify.app (op V) g)) (iWV y) := by
            simpa [TopCat.presheafToTypes_map] using hy
      _ = F.germ V (iWV y).1 (iWV y).2 g := rfl
      _ = F.germ W y.1 y.2 (F.map iWV.op g) := by
        symm
        exact F.germ_res_apply iWV y.1 y.2 g

/-- Helper for Lemma 6.18.1: the four canonical maps form a commutative square. -/
lemma sheafify_square_commutes (U : Opens X) :
    let Fsharp := F.sheafify.presheaf
    let stalkSections := X.presheafToTypes (fun x ↦ F.stalk x)
    let sectionStalks : Type v := ∀ x : U, F.stalk x.1
    let stalkSectionStalks : Type v := ∀ x : U, stalkSections.stalk x.1
    let ι :
        Fsharp.obj (op U) ⟶ stalkSections.obj (op U) :=
      (subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)
    let σ : Fsharp.obj (op U) ⟶ sectionStalks :=
      fun s x ↦ F.stalkToFiber x.1 (Fsharp.germ U x.1 x.2 s)
    let γ : stalkSections.obj (op U) ⟶ stalkSectionStalks :=
      fun s x ↦ stalkSections.germ U x.1 x.2 s
    let τ : sectionStalks ⟶ stalkSectionStalks :=
      fun s x ↦
        ((stalkFunctor (Type v) x.1).map
          (F.toSheafify ≫
            subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)) (s x)
    ι ≫ γ = σ ≫ τ := by
  dsimp
  ext s x
  rcases s.2 x with ⟨V, hxV, iV, g, hg⟩
  have hsx :
      F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s) = F.germ V x.1 hxV g := by
    calc
      F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s) =
          (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)) s) x := by
            exact congrFun (sheafify_section_stalk_family_eq F U s) x
      _ = F.germ V x.1 hxV g := hg ⟨x.1, hxV⟩
  -- Compare both sides through the same local germ witness `g`.
  change
    (X.presheafToTypes (fun y ↦ F.stalk y)).germ U x.1 x.2
        (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)) s) =
      ((stalkFunctor (Type v) x.1).map
        (F.toSheafify ≫
          subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate))
        (F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s))
  calc
    (X.presheafToTypes (fun y ↦ F.stalk y)).germ U x.1 x.2
        (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)) s) =
      (X.presheafToTypes (fun y ↦ F.stalk y)).germ V x.1 hxV
        (((subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op V))
          (F.toSheafify.app (op V) g)) := by
            apply (X.presheafToTypes (fun y ↦ F.stalk y)).germ_ext V hxV iV (𝟙 _)
            exact funext fun y ↦ hg y
    _ =
      ((stalkFunctor (Type v) x.1).map
        (F.toSheafify ≫
          subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate))
        (F.germ V x.1 hxV g) := by
          symm
          exact TopCat.Presheaf.stalkFunctor_map_germ_apply V x.1 hxV
            (F.toSheafify ≫
              subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate) g
    _ =
      ((stalkFunctor (Type v) x.1).map
        (F.toSheafify ≫
          subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate))
        (F.stalkToFiber x.1 (F.sheafify.presheaf.germ U x.1 x.2 s)) := by
          rw [hsx]

/-- Lemma 6.18.1: for an open set `U`, sections of the sheafification `F^#(U)` form the pullback of
the canonical inclusion `F^#(U) ↪ Π(F)(U)`, the family of germ maps
`F^#(U) → ∏_{x ∈ U} F_x` obtained from `F.sheafifyStalkIso`, the inclusion
`Π(F)(U) → ∏_{x ∈ U} Π(F)_x`, and the product of the canonical stalk maps
`∏_{x ∈ U} F_x → ∏_{x ∈ U} Π(F)_x`. -/
lemma sheafify_section_pullback_diagram (U : Opens X) :
    let Fsharp := F.sheafify.presheaf
    let stalkSections := X.presheafToTypes (fun x ↦ F.stalk x)
    let sectionStalks : Type v := ∀ x : U, F.stalk x.1
    let stalkSectionStalks : Type v := ∀ x : U, stalkSections.stalk x.1
    let ι :
        Fsharp.obj (op U) ⟶ stalkSections.obj (op U) :=
      (subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)
    let σ : Fsharp.obj (op U) ⟶ sectionStalks :=
      fun s x ↦ F.stalkToFiber x.1 (Fsharp.germ U x.1 x.2 s)
    let γ : stalkSections.obj (op U) ⟶ stalkSectionStalks :=
      fun s x ↦ stalkSections.germ U x.1 x.2 s
    let τ : sectionStalks ⟶ stalkSectionStalks :=
      fun s x ↦
        ((stalkFunctor (Type v) x.1).map
          (F.toSheafify ≫
            subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)) (s x)
    IsPullback ι σ γ τ := by
  dsimp
  rw [CategoryTheory.Limits.Types.isPullback_iff]
  refine ⟨sheafify_square_commutes F U, ?_, ?_⟩
  · intro a b hab
    -- The top arrow is a subtype inclusion, so equality upstairs follows from equality downstairs.
    apply Subtype.ext
    exact hab.1
  · intro s t hst
    have hs :
        ((isLocallyGerm F).toPrelocalPredicate).pred s := by
      -- The source proof identifies local-germ sections by stalkwise liftability.
      rw [isLocallyGerm_pred_iff_stalkwise_lift F U s]
      intro x
      exact ⟨t x, congrFun hst x⟩
    refine ⟨⟨s, hs⟩, rfl, ?_⟩
    ext x
    apply to_stalk_sections_stalk_injective F x.1
    -- Compare both candidates after mapping to the lower-right corner.
    have hcomm :=
      congrFun (congrFun (sheafify_square_commutes F U) ⟨s, hs⟩) x
    have hx := congrFun hst x
    simpa using hcomm.symm.trans hx

end
