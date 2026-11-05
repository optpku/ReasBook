module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

universe w v u

/- Domain-style sampling for Lemma 6.23.1:
- primary domain: pushforwards of sheaves of algebraic structures and comparison with the
  underlying sheaves of sets;
- inspected owner declarations:
  `sheafCompose`,
  `Sheaf.homEquiv`,
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pushforwardForgetIso`;
- best owner abstraction:
  the source-facing theorem is about an `f`-map of underlying sheaves of sets, so the correct
  public owner is the underlying-sheaf functor `sheafCompose JY F`, written below as
  `underlyingSheaf`, and the sheaf morphism
  `(underlyingSheaf).obj 𝒢 ⟶ (underlyingSheaf).obj ((Sheaf.pushforward C f).obj ℱ)`,
  which is the underlying-sheaf form of the canonical pushforward target `𝒢 ⟶
    (Sheaf.pushforward C f).obj ℱ`;
- primitive data:
  the underlying sheaf morphism of sets `φ` and the sectionwise existence of lifts
  `ψV : 𝒢(V) ⟶ (f_* ℱ)(V)` in `C`;
- derived API:
  the unique lifted sheaf morphism `Φ` and the equation
  `(sheafCompose JY F).map Φ = φ`.

Source/core/bridge triage:
- `source-facing`: the textbook lifting criterion for an `f`-map of underlying sheaves of sets;
- `core/canonical`: `Sheaf.pushforward C f`;
- `bridge/view`: the sheaf-level underlying-set view obtained by `sheafCompose JY F`, equivalent to
  the direct-image sheaf of sets via `TopCat.Sheaf.pushforwardForgetIso`.

The theorem therefore remains source-facing, but its public surface should use the canonical
sheaf-morphism owner rather than a raw presheaf transformation, while keeping the sectionwise lift
criterion as the derived bridge via `Sheaf.homEquiv`. -/

section

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [F.Faithful]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable {ℱ : X.Sheaf C} {𝒢 : Y.Sheaf C}

local notation "JY" => Opens.grothendieckTopology Y
local notation "underlyingSheaf" => sheafCompose JY F

omit [F.Faithful] in
/-- Helper for Lemma 6.23.1: forgetting a morphism of `C`-valued sheaves applies `F` to each
section map. -/
lemma underlying_sheaf_map_app_6_23_1
    [(Opens.grothendieckTopology Y).HasSheafCompose F]
    (Φ : 𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ) (V : Opens Y) :
    (Sheaf.homEquiv ((underlyingSheaf).map Φ)).app (op V) =
      F.map ((Sheaf.homEquiv Φ).app (op V)) := by
  -- This is definitionally how `sheafCompose` acts on morphisms.
  rfl

/-- Helper for Lemma 6.23.1: the chosen sectionwise lifts satisfy the presheaf naturality
condition. -/
lemma chosen_pushforward_section_maps_natural
    [(Opens.grothendieckTopology Y).HasSheafCompose F]
    (φ : (underlyingSheaf).obj 𝒢 ⟶ (underlyingSheaf).obj ((Sheaf.pushforward C f).obj ℱ))
    (hφ : ∀ V : Opens Y, ∃ ψV : 𝒢.presheaf.obj (op V) ⟶
        ((Sheaf.pushforward C f).obj ℱ).presheaf.obj (op V),
        F.map ψV = (Sheaf.homEquiv φ).app (op V))
    {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    𝒢.presheaf.map i ≫ Classical.choose (hφ V.unop) =
      Classical.choose (hφ U.unop) ≫ ((Sheaf.pushforward C f).obj ℱ).presheaf.map i := by
  -- Apply faithfulness of `F` so that the target square becomes the naturality square of `φ`.
  apply F.map_injective
  rw [Functor.map_comp, Functor.map_comp, Classical.choose_spec (hφ V.unop),
    Classical.choose_spec (hφ U.unop)]
  simpa using (NatTrans.naturality (Sheaf.homEquiv φ) i)

/-- Helper for Lemma 6.23.1: the chosen sectionwise lifts assemble into a morphism of
`C`-valued presheaves. -/
def sectionwise_lift_to_pushforward_presheaf_hom
    [(Opens.grothendieckTopology Y).HasSheafCompose F]
    (φ : (underlyingSheaf).obj 𝒢 ⟶ (underlyingSheaf).obj ((Sheaf.pushforward C f).obj ℱ))
    (hφ : ∀ V : Opens Y, ∃ ψV : 𝒢.presheaf.obj (op V) ⟶
        ((Sheaf.pushforward C f).obj ℱ).presheaf.obj (op V),
        F.map ψV = (Sheaf.homEquiv φ).app (op V)) :
    𝒢.presheaf ⟶ ((Sheaf.pushforward C f).obj ℱ).presheaf where
  app U := Classical.choose (hφ U.unop)
  naturality := fun {U V} i ↦ chosen_pushforward_section_maps_natural
    (F := F) (f := f) (φ := φ) (hφ := hφ) (U := U) (V := V) i

/-- Helper for Lemma 6.23.1: the sheaf morphism built from the chosen sectionwise lifts forgets to
the original underlying sheaf morphism. -/
lemma constructed_lift_recovers_underlying_map_6_23_1
    [(Opens.grothendieckTopology Y).HasSheafCompose F]
    (φ : (underlyingSheaf).obj 𝒢 ⟶ (underlyingSheaf).obj ((Sheaf.pushforward C f).obj ℱ))
    (hφ : ∀ V : Opens Y, ∃ ψV : 𝒢.presheaf.obj (op V) ⟶
        ((Sheaf.pushforward C f).obj ℱ).presheaf.obj (op V),
        F.map ψV = (Sheaf.homEquiv φ).app (op V)) :
    (underlyingSheaf).map
        (Sheaf.homEquiv.symm (sectionwise_lift_to_pushforward_presheaf_hom
          (F := F) (f := f) (φ := φ) hφ)) = φ := by
  -- Compare the two underlying morphisms componentwise on sections over each open set.
  apply (Sheaf.homEquiv).injective
  ext U
  -- Each component is the chosen lift, and forgetting that lift is exactly the prescribed map.
  rw [underlying_sheaf_map_app_6_23_1]
  rename_i a
  change F.map ((sectionwise_lift_to_pushforward_presheaf_hom
    (F := F) (f := f) (φ := φ) hφ).app U) a = (Sheaf.homEquiv φ).app U a
  simpa [sectionwise_lift_to_pushforward_presheaf_hom] using
    congrFun (Classical.choose_spec (hφ U.unop)) a

-- Proof sketch: for each open `V ⊆ Y`, choose a morphism in `C` whose underlying set map is the
-- given component of the sheaf morphism `φ : 𝒢ᵤ ⟶ f_* ℱᵤ` on sections over `V`. The
-- restriction-compatibility of `φ` and faithfulness of `F` force these sectionwise lifts to be
-- natural in `V`, hence they assemble into a morphism of `C`-valued sheaves `𝒢 ⟶ f_* ℱ`.
-- Uniqueness follows because `F` is faithful.
/-- Lemma 6.23.1: an `f`-map of the underlying sheaves of sets of `C`-valued sheaves comes from a
unique `f`-morphism of sheaves of algebraic structures if each section map is induced by a
morphism in `C`. -/
theorem existsUnique_pushforward_hom_of_underlying_sectionwise_structure_preserving
    [(Opens.grothendieckTopology Y).HasSheafCompose F]
    (φ : (underlyingSheaf).obj 𝒢 ⟶ (underlyingSheaf).obj ((Sheaf.pushforward C f).obj ℱ))
    (hφ : ∀ V : Opens Y, ∃ ψV : 𝒢.presheaf.obj (op V) ⟶
        ((Sheaf.pushforward C f).obj ℱ).presheaf.obj (op V),
        F.map ψV = (Sheaf.homEquiv φ).app (op V)) :
    ∃! Φ : 𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ,
      (underlyingSheaf).map Φ = φ :=
    by
  let ψ : 𝒢.presheaf ⟶ ((Sheaf.pushforward C f).obj ℱ).presheaf :=
    sectionwise_lift_to_pushforward_presheaf_hom (F := F) (f := f) (φ := φ) hφ
  let Φ : 𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ := Sheaf.homEquiv.symm ψ
  refine ⟨Φ, ?_, ?_⟩
  · -- The constructed lift forgets to the original map by construction of its section maps.
    simpa [Φ, ψ] using constructed_lift_recovers_underlying_map_6_23_1
      (F := F) (f := f) (φ := φ) hφ
  · intro Φ' hΦ'
    -- Faithfulness of the underlying-sheaf functor turns equality after forgetting into equality.
    exact (sheafCompose JY F).map_injective <| by
      calc
        (underlyingSheaf).map Φ' = φ := hΦ'
        _ = (underlyingSheaf).map Φ := by
          symm
          simpa [Φ, ψ] using constructed_lift_recovers_underlying_map_6_23_1
            (F := F) (f := f) (φ := φ) hφ

end
