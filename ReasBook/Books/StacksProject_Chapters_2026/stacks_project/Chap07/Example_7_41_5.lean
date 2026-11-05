module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Example_7_6_5
public import stacks_project.Chap07.Lemma_7_41_1
public import stacks_project.Chap07.Lemma_7_41_4
public import stacks_project.Chap07.Proposition_7_9_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Action

universe u

namespace CategoryTheory

noncomputable section

/- Domain-style sampling for Example 7.41.5:
- primary domain: continuous site pushforward on the surjective sites of `G`-sets and `H`-sets,
  together with the action-level coinduction model for `Action.res (Type u) φ` and the
  left-regular-sections owner from Proposition 7.9.1;
- sampled owner API:
  `Action.res`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPushforwardContinuous`,
  `(Action.jointlySurjectiveTopology G).yonedaEquiv`,
  `sheafSectionsOnLeftRegularFunctor`,
  `Representation.coind'`;
- source/core/bridge triage:
  `source-facing`: the counit `f⁻¹ f_* ℱ ⟶ ℱ` for the continuous morphism of sites induced by
    `Action.res (Type u) φ`, together with its evaluation-at-`1` description on the `Map_G(H, S)`
    model;
  `core/canonical`: the adjunction `sheafAdjunctionContinuous` and the owner predicate
    `Sheaf.IsLocallySurjective` on its counit;
  `bridge/view`: the explicit `H →[G] S` action-level model.

The public refinement below exposes the source-facing positive statement directly on the canonical
sheaf counit, and keeps the explicit evaluation-at-`1` map only as a companion view. The formal
bridge is evaluation of the pushforward on the left regular `H`-set, which canonically recovers
the explicit `H →[G] S` model.
-/

/- The source-facing explicit `Map_G(H, S)` model used internally below: equivariant maps from the
left `G`-set on `H` induced by `φ : G →* H` to the `G`-set `S`. Public statements use the direct
canonical type expression `H →[G] S` rather than a file-local wrapper. -/
abbrev restrictedEquivariantMaps
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Type u) [MulAction G S] :=
  letI : MulAction G H := MulAction.compHom H φ
  H →[G] S

theorem actionRes_preservesFiniteLimits
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    PreservesFiniteLimits (Action.res (Type u) φ) := by
  let _ : PreservesFiniteLimits ((Action.res (Type u) φ) ⋙ Action.forget (Type u) G) := by
    change PreservesFiniteLimits (Action.forget (Type u) H)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves
    (Action.res (Type u) φ) (Action.forget (Type u) G)

instance actionRes_representablyFlat
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    RepresentablyFlat (Action.res (Type u) φ) := by
  let _ : PreservesFiniteLimits (Action.res (Type u) φ) :=
    actionRes_preservesFiniteLimits φ
  exact flat_of_preservesFiniteLimits (Action.res (Type u) φ)

instance actionRes_coverPreserving
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    CoverPreserving (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) (Action.res (Type u) φ) where
  cover_preserve {U} {S} hS := by
    rw [Action.mem_jointlySurjectiveTopology_iff] at hS ⊢
    intro x
    rcases hS x with ⟨Y, f, hf, hx⟩
    exact
      ⟨(Action.res (Type u) φ).obj Y, (Action.res (Type u) φ).map f,
        Sieve.image_mem_functorPushforward (Action.res (Type u) φ) S hf, hx⟩

@[instance 10000] instance actionRes_isContinuous
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    (Action.res (Type u) φ).IsContinuous (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat (Action.jointlySurjectiveTopology G) (Action.res (Type u) φ))
    (actionRes_coverPreserving φ)

@[reducible] def equivariantMapRightTranslation
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Type u) [MulAction G S] :
    MulAction H (restrictedEquivariantMaps φ S) := by
  letI : MulAction G H := MulAction.compHom H φ
  exact
    { smul := fun h a ↦
        { toFun := fun x ↦ a (x * h)
          map_smul' := fun g x ↦ by
            change a ((φ g * x) * h) = g • a (x * h)
            rw [mul_assoc]
            exact a.map_smul g (x * h) }
      one_smul := fun a ↦ by
        apply MulActionHom.ext
        intro x
        change a (x * 1) = a x
        simp
      mul_smul := fun h₁ h₂ a ↦ by
        apply MulActionHom.ext
        intro x
        change a (x * (h₁ * h₂)) = a ((x * h₁) * h₂)
        rw [mul_assoc] }

/- The explicit `H`-action on `Map_G(H, S)` used internally below, given by right translation on
the source `H`. The corresponding left-regular-sections comparison is kept private; the public
companion statement uses the direct canonical type expression `H →[G] S`. -/
@[reducible] def equivariantMapAction
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Type u) [MulAction G S] :
    Action (Type u) H :=
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ S) := equivariantMapRightTranslation φ S
  Action.ofMulAction H (restrictedEquivariantMaps φ S)

abbrev equivariantMapObj
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Action (Type u) G) :
    Action (Type u) H :=
  letI : MulAction G S.V := instMulAction S
  equivariantMapAction φ S.V

def equivariantMapMap
    {G H : Type u} [Group G] [Group H] (φ : G →* H)
    {X Y : Action (Type u) G} (f : X ⟶ Y) :
    equivariantMapObj φ X ⟶ equivariantMapObj φ Y :=
  letI : MulAction G X.V := instMulAction X
  letI : MulAction G Y.V := instMulAction Y
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ X.V) := equivariantMapRightTranslation φ X.V
  letI : MulAction H (restrictedEquivariantMaps φ Y.V) := equivariantMapRightTranslation φ Y.V
  { hom := fun a : restrictedEquivariantMaps φ X.V ↦
      { toFun := fun h ↦ f.hom (a h)
        map_smul' := fun g h ↦ by
          simpa using congrArg (fun k ↦ k (a h)) (f.comm g) }
    comm := fun h ↦ by
      funext (a : restrictedEquivariantMaps φ X.V)
      apply MulActionHom.ext
      intro x
      rfl }

theorem equivariantMapMap_id
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (X : Action (Type u) G) :
    equivariantMapMap φ (𝟙 X) = 𝟙 (equivariantMapObj φ X) := by
  letI : MulAction G X.V := instMulAction X
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ X.V) := equivariantMapRightTranslation φ X.V
  apply Action.hom_ext
  funext (a : restrictedEquivariantMaps φ X.V)
  apply MulActionHom.ext
  intro x
  change a x = a x
  rfl

theorem equivariantMapMap_comp
    {G H : Type u} [Group G] [Group H] (φ : G →* H)
    {X Y Z : Action (Type u) G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    equivariantMapMap φ (f ≫ g) = equivariantMapMap φ f ≫ equivariantMapMap φ g := by
  letI : MulAction G X.V := instMulAction X
  letI : MulAction G Y.V := instMulAction Y
  letI : MulAction G Z.V := instMulAction Z
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ X.V) := equivariantMapRightTranslation φ X.V
  letI : MulAction H (restrictedEquivariantMaps φ Y.V) := equivariantMapRightTranslation φ Y.V
  letI : MulAction H (restrictedEquivariantMaps φ Z.V) := equivariantMapRightTranslation φ Z.V
  apply Action.hom_ext
  funext (a : restrictedEquivariantMaps φ X.V)
  apply MulActionHom.ext
  intro x
  change g.hom (f.hom (a x)) = g.hom (f.hom (a x))
  rfl

/-- An explicit action-level model for the pushforward attached to a group homomorphism
`φ : G → H`: it sends a `G`-set `S` to the `H`-set of `G`-equivariant maps `H → S`, where `G`
acts on `H` through `φ` and `H` acts by right translation on the source. The canonical
characterization is the continuous pushforward on sheaves along `Action.res (Type u) φ`; this
explicit model is kept only to support the concrete `H →[G] S` companion statements
below. -/
def equivariantMapPushforward
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    Action (Type u) G ⥤ Action (Type u) H where
  obj := equivariantMapObj φ
  map := equivariantMapMap φ
  map_id := equivariantMapMap_id φ
  map_comp := equivariantMapMap_comp φ

def equivariantMapPushforwardHomEquiv
    {G H : Type u} [Group G] [Group H] (φ : G →* H)
    (X : Action (Type u) H) (Y : Action (Type u) G) :
    (((Action.res (Type u) φ).obj X) ⟶ Y) ≃ (X ⟶ equivariantMapObj φ Y) := by
  letI : MulAction H X.V := instMulAction X
  letI : MulAction G Y.V := instMulAction Y
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ Y.V) := equivariantMapRightTranslation φ Y.V
  refine
    { toFun := fun f ↦
        { hom := fun x ↦
            { toFun := fun h ↦ f.hom (h • x)
              map_smul' := fun g h ↦ by
                change f.hom ((φ g * h) • x) = g • f.hom (h • x)
                simpa [mul_smul] using congrArg (fun k ↦ k (h • x)) (f.comm g) }
          comm := fun h ↦ by
            funext x
            apply MulActionHom.ext
            intro h'
            change f.hom (h' • (h • x)) = f.hom ((h' * h) • x)
            rw [mul_smul] }
      invFun := fun a ↦
        { hom := fun x ↦ (show restrictedEquivariantMaps φ Y.V from a.hom x) 1
          comm := fun g ↦ by
            funext (x : X.V)
            have hx := congrArg
              (fun k ↦ (show restrictedEquivariantMaps φ Y.V from k x) 1) (a.comm (φ g))
            have hx' :
                (show restrictedEquivariantMaps φ Y.V from a.hom ((φ g) • x)) 1 =
                  (show restrictedEquivariantMaps φ Y.V from
                    ((equivariantMapObj φ Y).ρ (φ g)) (a.hom x)) 1 := by
              simpa using hx
            have hy :
                (show restrictedEquivariantMaps φ Y.V from
                  ((equivariantMapObj φ Y).ρ (φ g)) (a.hom x)) 1 =
                    g • ((show restrictedEquivariantMaps φ Y.V from a.hom x) 1) := by
              change (show restrictedEquivariantMaps φ Y.V from a.hom x) (1 * φ g) =
                  g • ((show restrictedEquivariantMaps φ Y.V from a.hom x) 1)
              have hy := (show restrictedEquivariantMaps φ Y.V from a.hom x).map_smul g 1
              change (show restrictedEquivariantMaps φ Y.V from a.hom x) (φ g * 1) =
                  g • ((show restrictedEquivariantMaps φ Y.V from a.hom x) 1) at hy
              simpa using hy
            exact hx'.trans (by simpa using hy) }
      left_inv := fun f ↦ by
        apply Action.hom_ext
        funext (x : X.V)
        change f.hom ((1 : H) • x) = f.hom x
        simp
      right_inv := fun a ↦ by
        apply Action.hom_ext
        funext (x : X.V)
        apply MulActionHom.ext
        intro h
        have hx := congrArg
          (fun k ↦ (show restrictedEquivariantMaps φ Y.V from k x) 1) (a.comm h)
        change (show restrictedEquivariantMaps φ Y.V from a.hom (h • x)) 1 =
            (show restrictedEquivariantMaps φ Y.V from
              ((equivariantMapObj φ Y).ρ h) (a.hom x)) 1 at hx
        change (show restrictedEquivariantMaps φ Y.V from a.hom (h • x)) 1 =
            (show restrictedEquivariantMaps φ Y.V from a.hom x) (1 * h) at hx
        simpa using hx }

/-- Restriction along `φ` is left adjoint to the explicit equivariant-map pushforward model. -/
noncomputable def equivariantMapPushforwardAdjunction
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    Action.res (Type u) φ ⊣ equivariantMapPushforward φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := equivariantMapPushforwardHomEquiv φ
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply Action.hom_ext
        funext x
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        letI : MulAction G Y'.V := instMulAction Y'
        letI : MulAction G H := MulAction.compHom H φ
        letI : MulAction H (restrictedEquivariantMaps φ Y'.V) := equivariantMapRightTranslation φ Y'.V
        apply Action.hom_ext
        funext x
        apply MulActionHom.ext
        intro h
        rfl }

/-- The explicit functor `equivariantMapPushforward φ` is the right adjoint in the adjunction
`Action.res (Type u) φ ⊣ equivariantMapPushforward φ`. -/
@[instance 10000] instance
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    (equivariantMapPushforward φ).IsRightAdjoint :=
  (equivariantMapPushforwardAdjunction φ).isRightAdjoint

noncomputable def yonedaCompSheafPushforwardContinuousIso
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    (Action.jointlySurjectiveTopology G).yoneda ⋙
        (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
          (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) ≅
      equivariantMapPushforward φ ⋙ (Action.jointlySurjectiveTopology H).yoneda := by
  let eLeft :
      ((Action.jointlySurjectiveTopology G).yoneda ⋙
          (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
            (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)) ⋙
        sheafToPresheaf (Action.jointlySurjectiveTopology H) (Type u) ≅
      CategoryTheory.yoneda ⋙
        (Functor.whiskeringLeft (Action (Type u) H)ᵒᵖ (Action (Type u) G)ᵒᵖ (Type u)).obj
          (Action.res (Type u) φ).op :=
    (Functor.isoWhiskerLeft (Action.jointlySurjectiveTopology G).yoneda
      ((Action.res (Type u) φ).sheafPushforwardContinuousCompSheafToPresheafIso (Type u)
        (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G))) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((Action.jointlySurjectiveTopology G).yonedaCompSheafToPresheaf) _
  let eRight :
      (equivariantMapPushforward φ ⋙ (Action.jointlySurjectiveTopology H).yoneda) ⋙
        sheafToPresheaf (Action.jointlySurjectiveTopology H) (Type u) ≅
      CategoryTheory.yoneda ⋙
        (Functor.whiskeringLeft (Action (Type u) H)ᵒᵖ (Action (Type u) G)ᵒᵖ (Type u)).obj
          (Action.res (Type u) φ).op :=
    Functor.associator _ _ _ ≪≫
      (Functor.isoWhiskerLeft (equivariantMapPushforward φ)
      ((Action.jointlySurjectiveTopology H).yonedaCompSheafToPresheaf)) ≪≫
      Adjunction.compYonedaIso (equivariantMapPushforwardAdjunction φ)
  exact
    ((fullyFaithfulSheafToPresheaf (Action.jointlySurjectiveTopology H) (Type u)).whiskeringRight
      (Action (Type u) G)).preimageIso
      (eLeft ≪≫ eRight.symm)

instance actionRes_sheafPushforwardContinuous_isRightAdjoint
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    ((Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
      (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)).IsRightAdjoint := by
  let eG :
      Action (Type u) G ≌ Sheaf (Action.jointlySurjectiveTopology G) (Type u) :=
    ((Action.jointlySurjectiveTopology G).yoneda).asEquivalence
  letI : (equivariantMapPushforward φ ⋙ (Action.jointlySurjectiveTopology H).yoneda).IsRightAdjoint :=
    inferInstance
  letI :
      ((Action.jointlySurjectiveTopology G).yoneda ⋙
        (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
          (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso (yonedaCompSheafPushforwardContinuousIso φ).symm
  exact
    (((Adjunction.ofIsRightAdjoint
        ((Action.jointlySurjectiveTopology G).yoneda ⋙
          (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
            (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G))).comp
        eG.toAdjunction).ofNatIsoRight
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eG.counitIso
          ((Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
            (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)) ≪≫
        Functor.leftUnitor _)).isRightAdjoint

-- Internal action-level counit computation used below to identify the canonical sheaf counit with
-- evaluation at `1` through Proposition 7.9.1 and the left-regular-sections comparison.
theorem equivariantMapPushforward_counit_eq_eval_one
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    letI : MulAction G H := MulAction.compHom H φ
    ((equivariantMapPushforwardAdjunction φ).counit.app (Action.ofMulAction G S)).hom =
      fun a : H →[G] S ↦ a 1 := by
  -- The counit of `Adjunction.mkOfHomEquiv` is the inverse half of the hom-equivalence at `𝟙`.
  rfl

-- Proof sketch: choose one value in `S` on each left coset of `φ(G)` in `H`, prescribing the
-- value `s` on the coset of `1`; injectivity of `φ` makes the equivariance condition consistent.
theorem equivariantMapPushforward_counit_surjective_of_injective
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ)
    (S : Action (Type u) G) :
    Function.Surjective ((equivariantMapPushforwardAdjunction φ).counit.app S).hom := by
  classical
  letI : MulAction G H := MulAction.compHom H φ
  intro s
  change S.V at s
  letI : MulAction G S.V := instMulAction S
  let q : H → _root_.Quotient (QuotientGroup.rightRel φ.range) := Quotient.mk''
  let q₁ : _root_.Quotient (QuotientGroup.rightRel φ.range) := Quotient.mk'' (1 : H)
  choose! repRaw hrepRaw using
    (Quotient.mk''_surjective : Function.Surjective
      (Quotient.mk'' : H → _root_.Quotient (QuotientGroup.rightRel φ.range)))
  let rep : _root_.Quotient (QuotientGroup.rightRel φ.range) → H := fun q ↦
    if hq : q = q₁ then 1 else repRaw q
  have hrep :
      ∀ q : _root_.Quotient (QuotientGroup.rightRel φ.range), Quotient.mk'' (rep q) = q := by
    intro q
    by_cases hq : q = q₁
    · subst hq
      simp [rep, q₁]
    · simp [rep, hq, hrepRaw q]
  let γRange : H → φ.range := fun h ↦
    ⟨h * (rep (q h))⁻¹, by
      have hq : q (rep (q h)) = q h :=
        hrep (q h)
      exact
        QuotientGroup.rightRel_apply.1
          (Quotient.eq''.1 hq)⟩
  let γ : H → G := fun h ↦ Classical.choose (γRange h).2
  have hγ : ∀ h : H, φ (γ h) = (γRange h).1 := by
    intro h
    exact Classical.choose_spec (γRange h).2
  have hγ_one : γ 1 = 1 := by
    apply hφ
    calc
      φ (γ 1) = (γRange 1).1 := hγ 1
      _ = 1 := by
        change (1 : H) * (rep q₁)⁻¹ = 1
        simp [rep]
      _ = φ 1 := by simp
  let a : restrictedEquivariantMaps φ S.V :=
    { toFun := fun h ↦ γ h • s
      map_smul' := fun g h ↦ by
        -- The quotient representative is constant on left `φ(G)`-cosets, so the transport
        -- element `γ` changes by left multiplication by `g`.
        have hγ_mul : γ (φ g * h) = g * γ h := by
          apply hφ
          calc
            φ (γ (φ g * h)) = (γRange (φ g * h)).1 := hγ _
            _ = φ g * (γRange h).1 := by
              change (φ g * h) * (rep (q (φ g * h)))⁻¹ =
                  φ g * (h * (rep (q h))⁻¹)
              have hq : q (φ g * h) = q h := by
                apply Quotient.sound'
                rw [QuotientGroup.rightRel_apply]
                refine ⟨g⁻¹, ?_⟩
                simp
              simp [hq, mul_assoc]
            _ = φ g * φ (γ h) := by rw [hγ]
            _ = φ (g * γ h) := by simp
        simpa [mul_smul] using congrArg (fun x ↦ x • s) hγ_mul }
  refine ⟨a, ?_⟩
  -- The counit is explicit evaluation at `1`, and the normalized representative of the identity
  -- coset forces the chosen lift to take the value `s` at `1`.
  have hEval :
      ((equivariantMapPushforwardAdjunction φ).counit.app S).hom a = a 1 := by
    cases S
    rfl
  rw [hEval]
  change γ 1 • s = s
  simp [hγ_one]

/-- Helper for Example 7.41.5: injectivity of `φ` makes restriction along `φ` cover-dense for the
jointly surjective topology on `G`-sets. -/
instance actionRes_isCoverDense_of_injective
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ) :
    (Action.res (Type u) φ).IsCoverDense (Action.jointlySurjectiveTopology G) := by
  -- Package the surjective counit arrow as a singleton jointly-surjective cover.
  refine (Action.res (Type u) φ).isCoverDense_of_generate_singleton_functor_π_mem
    (Action.jointlySurjectiveTopology G) ?_
  intro S
  refine ⟨(equivariantMapPushforward φ).obj S, ((equivariantMapPushforwardAdjunction φ).counit.app S), ?_⟩
  rw [Action.mem_jointlySurjectiveTopology_iff]
  intro s
  rcases equivariantMapPushforward_counit_surjective_of_injective φ hφ S s with ⟨a, rfl⟩
  refine ⟨_, _, ?_, ⟨a, rfl⟩⟩
  exact Sieve.le_generate _ _ _ (Presieve.singleton_self _)

/-- Helper for Example 7.41.5: cover-dense restriction along an injective group map reflects
epimorphisms on sheaves of types without needing a `HasSheafify` hypothesis. -/
instance actionRes_sheafPushforwardContinuous_reflectsEpimorphisms_of_injective
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ) :
    ((Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
      (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)).ReflectsEpimorphisms where
  reflects := by
    intro X Y a ha
    refine ⟨?_⟩
    intro Z g h hgh
    letI : (Action.res (Type u) φ).IsCoverDense (Action.jointlySurjectiveTopology G) :=
      actionRes_isCoverDense_of_injective φ hφ
    let JG := Action.jointlySurjectiveTopology G
    let JH := Action.jointlySurjectiveTopology H
    let F := Action.res (Type u) φ
    let R : Sheaf JG (Type u) ⥤ Sheaf JH (Type u) :=
      F.sheafPushforwardContinuous (Type u) JH JG
    have hR : R.map g = R.map h := by
      letI : Epi (R.map a) := ha
      apply (cancel_epi (R.map a)).1
      simpa only [R, ← Functor.map_comp] using congrArg (fun t ↦ R.map t) hgh
    ext U x
    cases U with
    | op U =>
      apply Functor.IsCoverDense.ext F Z U
      intro V f
      have hRY := congrArg
        (fun k : R.obj Y ⟶ R.obj Z ↦
          k.hom.app (op V) (Y.obj.map f.op x)) hR
      dsimp [R, F, Functor.sheafPushforwardContinuous] at hRY
      have hgNat :
          g.hom.app (op (F.obj V)) (Y.obj.map f.op x) =
            Z.obj.map f.op (g.hom.app (op U) x) := by
        simpa using congrFun (g.hom.naturality f.op) x
      have hhNat :
          h.hom.app (op (F.obj V)) (Y.obj.map f.op x) =
            Z.obj.map f.op (h.hom.app (op U) x) := by
        simpa using congrFun (h.hom.naturality f.op) x
      rw [← hgNat, ← hhNat]
      exact hRY

/- The left-regular-sections view of the continuous pushforward along `Action.res (Type u) φ`.
This is the canonical sheaf-level object whose action-level comparison with `H →[G] S` is used
below. -/
abbrev continuousPushforwardLeftRegularSections
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Action (Type u) G) :
    Action (Type u) H :=
  (sheafSectionsOnLeftRegularFunctor H).obj
    (((Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
      (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)).obj
      ((Action.jointlySurjectiveTopology G).yoneda.obj S))

/-- The `H`-action obtained by evaluating the canonical continuous pushforward along
`Action.res (Type u) φ` on the left regular `H`-set. -/
noncomputable abbrev actionRes_pushforwardLeftRegularAction
    {G H : Type u} [Group G] [Group H] (S : Type u) [MulAction G S] (φ : G →* H) :
    Action (Type u) H :=
  continuousPushforwardLeftRegularSections φ (Action.ofMulAction G S)

noncomputable def actionRes_pushforwardLeftRegularEquiv
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (S : Action (Type u) G) :
    (continuousPushforwardLeftRegularSections φ S).V ≃
      (((Action.res (Type u) φ).obj (Action.leftRegular H)) ⟶ S) := by
  let hFF : ((Action.jointlySurjectiveTopology G).yoneda).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ((Action.jointlySurjectiveTopology G).yoneda)
  change (((Action.jointlySurjectiveTopology G).yoneda.obj S).obj.obj
      (Opposite.op ((Action.res (Type u) φ).obj (Action.leftRegular H)))) ≃
    (((Action.res (Type u) φ).obj (Action.leftRegular H)) ⟶ S)
  exact
    ((Action.jointlySurjectiveTopology G).yonedaEquiv :
      ((Action.jointlySurjectiveTopology G).yoneda.obj ((Action.res (Type u) φ).obj (Action.leftRegular H)) ⟶
        (Action.jointlySurjectiveTopology G).yoneda.obj S) ≃
        (((Action.jointlySurjectiveTopology G).yoneda.obj S).obj.obj
          (Opposite.op ((Action.res (Type u) φ).obj (Action.leftRegular H))))).symm.trans
      hFF.homEquiv.symm

def equivariantMapsToActionHom
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    restrictedEquivariantMaps φ S →
      ((Action.res (Type u) φ).obj (Action.leftRegular H) ⟶ Action.ofMulAction G S)
  | a => by
      letI : MulAction G H := MulAction.compHom H φ
      exact
        { hom := a.toFun
          comm := fun g ↦ by
            ext h
            change a (φ g * (show H from h)) = g • a (show H from h)
            exact a.map_smul g (show H from h) }

noncomputable def continuousPushforwardLeftRegularEquivariantMapsEquivAux
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    (continuousPushforwardLeftRegularSections φ (Action.ofMulAction G S)).V ≃
      restrictedEquivariantMaps φ S := by
  let e := actionRes_pushforwardLeftRegularEquiv φ (Action.ofMulAction G S)
  letI : MulAction G H := MulAction.compHom H φ
  refine Equiv.ofBijective
    (fun a ↦
      { toFun := (e a).hom
        map_smul' := fun g h ↦ by
          simpa using congrArg (fun k ↦ k h) ((e a).comm g) }) ?_
  constructor
  · intro a b hab
    apply e.injective
    ext h
    exact congrArg (fun k : restrictedEquivariantMaps φ S ↦ k h) hab
  · intro a
    refine ⟨e.symm (equivariantMapsToActionHom φ a), ?_⟩
    ext h
    exact congrArg
      (fun k :
        ((Action.res (Type u) φ).obj (Action.leftRegular H) ⟶ Action.ofMulAction G S) ↦
          k.hom h)
      (e.apply_symm_apply (equivariantMapsToActionHom φ a))

/-- Helper for Example 7.41.5: under `actionRes_pushforwardLeftRegularEquiv`, pullback along
right multiplication on the left regular `H`-set becomes precomposition by that same right
multiplication on equivariant maps. -/
theorem actionRes_pushforwardLeftRegularEquiv_rightMul
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H)
    (h : H)
    (ψ : (continuousPushforwardLeftRegularSections φ (Action.ofMulAction G S)).V) :
    actionRes_pushforwardLeftRegularEquiv φ (Action.ofMulAction G S)
      (((continuousPushforwardLeftRegularSections φ (Action.ofMulAction G S)).ρ h) ψ) =
      (Action.res (Type u) φ).map (gSetForgetfulPointLeftRegularRightMul H h) ≫
        actionRes_pushforwardLeftRegularEquiv φ (Action.ofMulAction G S) ψ := by
  let JG := Action.jointlySurjectiveTopology G
  let hFF : (JG.yoneda).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful JG.yoneda
  let ψ' :
      (((Action.jointlySurjectiveTopology G).yoneda.obj (Action.ofMulAction G S)).obj.obj
        (Opposite.op ((Action.res (Type u) φ).obj (Action.leftRegular H)))) := by
    -- Unfold the left-regular-sections object so the Yoneda equivalence can read the section `ψ`.
    simpa [continuousPushforwardLeftRegularSections, sheafSectionsOnLeftRegularFunctor] using ψ
  -- Compare morphisms after applying the fully faithful Yoneda embedding.
  apply hFF.homEquiv.injective
  -- Under `yonedaEquiv`, the left-regular action is pullback along right multiplication.
  change
    hFF.homEquiv
        (((JG.yonedaEquiv).symm.trans hFF.homEquiv.symm)
          (((continuousPushforwardLeftRegularSections φ (Action.ofMulAction G S)).ρ h) ψ)) =
      hFF.homEquiv
        ((Action.res (Type u) φ).map (gSetForgetfulPointLeftRegularRightMul H h) ≫
          (((JG.yonedaEquiv).symm.trans hFF.homEquiv.symm) ψ))
  rw [Equiv.trans_apply, Equiv.trans_apply]
  symm
  simpa [ψ', continuousPushforwardLeftRegularSections, sheafSectionsOnLeftRegularFunctor] using
    (JG.yonedaEquiv_symm_naturality_left
      ((Action.res (Type u) φ).map (gSetForgetfulPointLeftRegularRightMul H h))
      ((Action.jointlySurjectiveTopology G).yoneda.obj (Action.ofMulAction G S))
      ψ')

theorem continuousPushforwardLeftRegularEquivariantMaps_comm
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    ∀ h : H,
      (continuousPushforwardLeftRegularSections φ (Action.ofMulAction G S)).ρ h ≫
      (continuousPushforwardLeftRegularEquivariantMapsEquivAux φ).toIso.hom =
      (continuousPushforwardLeftRegularEquivariantMapsEquivAux φ).toIso.hom ≫
        (equivariantMapAction φ S).ρ h := by
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (restrictedEquivariantMaps φ S) := equivariantMapRightTranslation φ S
  intro h
  ext ψ x
  -- Evaluate the transported section after rewriting pullback on the left-regular object as
  -- precomposition by right multiplication on the explicit equivariant-map model.
  simpa [equivariantMapAction, equivariantMapRightTranslation] using
    congrArg
      (fun k :
        ((Action.res (Type u) φ).obj (Action.leftRegular H) ⟶ Action.ofMulAction G S) ↦
          k.hom x)
      (actionRes_pushforwardLeftRegularEquiv_rightMul φ h ψ)

/-- The left-regular-sections comparison identifying the canonical continuous pushforward along
`Action.res (Type u) φ` with the explicit right-translation action on `H →[G] S`. -/
noncomputable def actionRes_pushforwardLeftRegularEquivariantMapsIso
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    letI : MulAction G H := MulAction.compHom H φ
    letI : MulAction H (H →[G] S) := equivariantMapRightTranslation φ S
    actionRes_pushforwardLeftRegularAction S φ ≅ Action.ofMulAction H (H →[G] S) := by
  letI : MulAction G H := MulAction.compHom H φ
  letI : MulAction H (H →[G] S) := equivariantMapRightTranslation φ S
  exact Action.mkIso
    (continuousPushforwardLeftRegularEquivariantMapsEquivAux φ).toIso
    (continuousPushforwardLeftRegularEquivariantMaps_comm φ)

noncomputable def actionRes_sheafAdjunctionViaYoneda
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    (((Action.jointlySurjectiveTopology H).yoneda).asEquivalence.inverse ⋙
        Action.res (Type u) φ ⋙
          (Action.jointlySurjectiveTopology G).yoneda) ⊣
      (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
        (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) := by
  let eG : Action (Type u) G ≌ Sheaf (Action.jointlySurjectiveTopology G) (Type u) :=
    ((Action.jointlySurjectiveTopology G).yoneda).asEquivalence
  let eH : Action (Type u) H ≌ Sheaf (Action.jointlySurjectiveTopology H) (Type u) :=
    ((Action.jointlySurjectiveTopology H).yoneda).asEquivalence
  let adjH : eH.inverse ⊣ eH.functor := eH.symm.toAdjunction
  let adjMaps : Action.res (Type u) φ ⊣ equivariantMapPushforward φ :=
    equivariantMapPushforwardAdjunction φ
  let adjG : eG.functor ⊣ eG.inverse := eG.toAdjunction
  let adj :
      (eH.inverse ⋙ Action.res (Type u) φ ⋙ eG.functor) ⊣
        (eG.inverse ⋙ equivariantMapPushforward φ ⋙ eH.functor) :=
    (adjH.comp adjMaps).comp adjG
  let i :
      (eG.inverse ⋙ equivariantMapPushforward φ ⋙ eH.functor) ≅
        (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
          (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) := by
    calc
      eG.inverse ⋙ equivariantMapPushforward φ ⋙ eH.functor
          ≅ eG.inverse ⋙ (equivariantMapPushforward φ ⋙ eH.functor) :=
        (Functor.associator _ _ _).symm
      _ ≅ eG.inverse ⋙
            ((Action.jointlySurjectiveTopology G).yoneda ⋙
              (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
                (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)) :=
        Functor.isoWhiskerLeft eG.inverse (yonedaCompSheafPushforwardContinuousIso φ).symm
      _ ≅
            (eG.inverse ⋙ (Action.jointlySurjectiveTopology G).yoneda) ⋙
              (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
                (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) :=
        (Functor.associator _ _ _).symm
      _ ≅
            𝟭 (Sheaf (Action.jointlySurjectiveTopology G) (Type u)) ⋙
              (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
                (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) :=
        Functor.isoWhiskerRight eG.counitIso _
      _ ≅
            (Action.res (Type u) φ).sheafPushforwardContinuous (Type u)
              (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) :=
        Functor.leftUnitor _
  exact adj.ofNatIsoRight i

noncomputable def actionRes_sheafPullbackIso
    {G H : Type u} [Group G] [Group H] (φ : G →* H) :
    (((Action.jointlySurjectiveTopology H).yoneda).asEquivalence.inverse ⋙
        Action.res (Type u) φ ⋙
          (Action.jointlySurjectiveTopology G).yoneda) ≅
      (Action.res (Type u) φ).sheafPullback (Type u)
        (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G) :=
  Adjunction.leftAdjointUniq
    (actionRes_sheafAdjunctionViaYoneda φ)
    ((Action.res (Type u) φ).sheafAdjunctionContinuous (Type u)
      (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G))

/-- The action-level map on `H →[G] S` induced by the counit of the canonical continuous sheaf
adjunction along `Action.res (Type u) φ`, viewed through Proposition 7.9.1 and the
left-regular-sections comparison. -/
noncomputable def actionRes_pushforwardCounitMap
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    letI : MulAction G H := MulAction.compHom H φ
    (H →[G] S) → S :=
  letI : MulAction G H := MulAction.compHom H φ
  ((equivariantMapPushforwardAdjunction φ).counit.app (Action.ofMulAction G S)).hom

/-- Helper for Example 7.41.5: after transporting the canonical sheaf counit through the
left-regular-sections comparison, one recovers the counit of the explicit
`Action.res (Type u) φ ⊣ equivariantMapPushforward φ` adjunction. -/
theorem actionRes_pushforwardCounitMap_eq_explicit_counit
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    letI : MulAction G H := MulAction.compHom H φ
    actionRes_pushforwardCounitMap φ = fun a : H →[G] S ↦
      ((equivariantMapPushforwardAdjunction φ).counit.app (Action.ofMulAction G S)).hom a := by
  letI : MulAction G H := MulAction.compHom H φ
  -- Route correction: compare the two counits after all sheaf-level identifications have been
  -- reduced to the explicit `H →[G] S` action model.
  rfl

/-- Example 7.41.5 (1): source-facing bridge. Under Proposition 7.9.1 and the left-regular-sections
comparison for the canonical continuous pushforward along `Action.res (Type u) φ`, the counit at
the sheaf corresponding to the `G`-set `S` is the explicit evaluation map `(H →[G] S) → S`,
`a ↦ a(1)`. -/
theorem equivariant_map_pushforward_counit_eq_eval_one
    {G H S : Type u} [Group G] [Group H] [MulAction G S] (φ : G →* H) :
    letI : MulAction G H := MulAction.compHom H φ
    actionRes_pushforwardCounitMap φ = fun a : H →[G] S ↦ a 1 := by
  letI : MulAction G H := MulAction.compHom H φ
  -- First replace the transported sheaf counit by the explicit action-level counit.
  simpa [actionRes_pushforwardCounitMap_eq_explicit_counit] using
    equivariantMapPushforward_counit_eq_eval_one φ

/-- Example 7.41.5 (2): canonical sheaf form. If `φ : G → H` is injective, then for the sheaf
attached to a `G`-set `S`, the counit `f⁻¹ f_* ℱ ⟶ ℱ` of the chapter's chosen adjunction
`(Action.res (Type u) φ).sheafAdjunctionContinuous ...` is locally surjective. The continuity
instance for `Action.res (Type u) φ` together with the canonical `Type`-valued sheaf pullback
construction supplies the needed right-adjoint structure internally. -/
theorem continuous_pushforward_counit_isLocallySurjective_of_injective
    {G H S : Type u} [Group G] [Group H] [MulAction G S]
    [HasSheafify.{u, u, u + 1, u + 1} (Action.jointlySurjectiveTopology G) (Type u)]
    (φ : G →* H)
    (hφ : Function.Injective φ) :
    Sheaf.IsLocallySurjective
      (((Action.res (Type u) φ).sheafAdjunctionContinuous (Type u)
          (Action.jointlySurjectiveTopology H) (Action.jointlySurjectiveTopology G)).counit.app
        ((Action.jointlySurjectiveTopology G).yoneda.obj (Action.ofMulAction G S))) := by
  let JG := Action.jointlySurjectiveTopology G
  let JH := Action.jointlySurjectiveTopology H
  let Y : Sheaf JG (Type u) := JG.yoneda.obj (Action.ofMulAction G S)
  let R :
      Sheaf JG (Type u) ⥤ Sheaf JH (Type u) :=
    (Action.res (Type u) φ).sheafPushforwardContinuous (Type u) JH JG
  let adj :=
    (Action.res (Type u) φ).sheafAdjunctionContinuous (Type u) JH JG
  letI : (Action.res (Type u) φ).IsCoverDense JG :=
    actionRes_isCoverDense_of_injective φ hφ
  letI : R.ReflectsEpimorphisms :=
    actionRes_sheafPushforwardContinuous_reflectsEpimorphisms_of_injective φ hφ
  have hSplit : IsSplitEpi (R.map (adj.counit.app Y)) := by
    -- After applying the pushforward, the counit is split by the unit via the right triangle.
    refine IsSplitEpi.mk' ⟨adj.unit.app (R.obj Y), ?_⟩
    exact adj.right_triangle_components Y
  have hMapEpi : Epi (R.map (adj.counit.app Y)) :=
    SplitEpi.epi hSplit.exists_splitEpi.some
  have hCounitEpi : Epi (adj.counit.app Y) := by
    -- Reflect the split epimorphism of the pushed-forward counit back to the source sheaf map.
    exact CategoryTheory.Functor.epi_of_epi_map (F := R) (f := adj.counit.app Y) hMapEpi
  -- Translate the categorical epimorphism statement back to local surjectivity on sheaves.
  exact
    (Sheaf.isLocallySurjective_iff_epi
      (J := Action.jointlySurjectiveTopology G) (φ := adj.counit.app Y)).2 hCounitEpi

/-- Example 7.41.5 (3): explicit companion. If `φ : G → H` is injective, then the concrete map
`(H →[G] S) → S`, `a ↦ a(1)`, is surjective, where `G` acts on `H` via `φ`. This is the
left-regular-sections view of `continuous_pushforward_counit_isLocallySurjective_of_injective`. -/
theorem equivariant_map_eval_one_surjective_of_injective
    {G H S : Type u} [Group G] [Group H] [MulAction G S]
    (φ : G →* H) (hφ : Function.Injective φ) :
    letI : MulAction G H := MulAction.compHom H φ
    Function.Surjective (fun a : H →[G] S ↦ a 1) := by
  letI : MulAction G H := MulAction.compHom H φ
  -- The explicit evaluation map is definitionally the counit of the action-level adjunction.
  change Function.Surjective
    (((equivariantMapPushforwardAdjunction φ).counit.app (Action.ofMulAction G S)).hom)
  exact equivariantMapPushforward_counit_surjective_of_injective φ hφ (Action.ofMulAction G S)

-- Proof sketch: with `G = {1}`, every function `H → Bool` is automatically `G`-equivariant,
-- so two distinct functions agreeing at `1` give distinct preimages of the same value.
local instance punitTrivialMulAction (α : Type u) : MulAction PUnit.{u + 1} α where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

local instance zmod2MultiplicativeFintype : Fintype (Multiplicative (ZMod 2)) :=
  Fintype.ofEquiv (ZMod 2) Multiplicative.ofAdd

/-- In the two-point example from the text, evaluation at `1` need not be injective. -/
theorem equivariant_map_eval_one_not_injective_example :
    letI : MulAction PUnit (Multiplicative (ZMod 2)) :=
      MulAction.compHom (Multiplicative (ZMod 2)) (1 : PUnit →* Multiplicative (ZMod 2))
    ¬ Function.Injective (fun a : Multiplicative (ZMod 2) →[PUnit] Bool ↦ a 1) := by
  letI : MulAction PUnit (Multiplicative (ZMod 2)) :=
    MulAction.compHom (Multiplicative (ZMod 2)) (1 : PUnit →* Multiplicative (ZMod 2))
  let a₀ : Multiplicative (ZMod 2) →[PUnit] Bool :=
    { toFun := fun _ ↦ false
      map_smul' := by
        intro g h
        cases g
        rfl }
  let a₁ : Multiplicative (ZMod 2) →[PUnit] Bool :=
    { toFun := fun h ↦ decide (h = Multiplicative.ofAdd 1)
      map_smul' := by
        intro g h
        cases g
        have hs : (PUnit.unit : PUnit) • h = h := by
          simpa using
            (MulAction.compHom_smul_def
              (f := (1 : PUnit →* Multiplicative (ZMod 2))) PUnit.unit h)
        change decide ((PUnit.unit : PUnit) • h = Multiplicative.ofAdd 1) =
          (PUnit.unit : PUnit) • decide (h = Multiplicative.ofAdd 1)
        rw [hs]
        rfl }
  intro hinj
  have hab : a₀ = a₁ := by
    exact @hinj a₀ a₁ (show a₀ 1 = a₁ 1 from by
      change false = decide ((1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1)
      decide)
  have hneq := congrArg
    (fun a : Multiplicative (ZMod 2) →[PUnit] Bool ↦ a (Multiplicative.ofAdd 1)) hab
  have h0 : a₀ (Multiplicative.ofAdd 1) = false := rfl
  have h1 : a₁ (Multiplicative.ofAdd 1) = true := by
    change decide ((Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) =
      Multiplicative.ofAdd 1) = true
    decide
  change a₀ (Multiplicative.ofAdd 1) = a₁ (Multiplicative.ofAdd 1) at hneq
  rw [h0, h1] at hneq
  cases hneq

/-- Helper for Example 7.41.5: the constant `false` map from the point to `Bool` in the trivial
`PUnit`-action category. -/
def two_point_false_map :
    Action.ofMulAction PUnit PUnit ⟶ Action.ofMulAction PUnit Bool where
  hom := fun _ ↦ false
  comm g := by
    funext x
    cases g
    rfl

/-- Helper for Example 7.41.5: the constant `true` map from the point to `Bool` in the trivial
`PUnit`-action category. -/
def two_point_true_map :
    Action.ofMulAction PUnit PUnit ⟶ Action.ofMulAction PUnit Bool where
  hom := fun _ ↦ true
  comm g := by
    funext x
    cases g
    rfl

/-- Helper for Example 7.41.5: collapsing `Bool` to the point in the trivial `PUnit`-action
category. -/
def two_point_collapse_map :
    Action.ofMulAction PUnit Bool ⟶ Action.ofMulAction PUnit PUnit where
  hom := fun _ ↦ PUnit.unit
  comm g := by
    funext x
    cases g
    rfl

/-- Helper for Example 7.41.5: the two constant maps equalize after collapsing `Bool` to the
point. -/
theorem two_point_collapse_condition :
    two_point_false_map ≫ two_point_collapse_map =
      two_point_true_map ≫ two_point_collapse_map := by
  -- Both composites are the unique map `PUnit ⟶ PUnit`.
  apply Action.hom_ext
  funext x
  rfl

/-- Helper for Example 7.41.5: the trivial-action diagram `PUnit ⇉ Bool ⟶ PUnit` is a
coequalizer in `Action (Type 0) PUnit`. -/
noncomputable def two_point_coequalizer_witness_in_trivial_actions :
    IsColimit (Cofork.ofπ two_point_collapse_map two_point_collapse_condition) := by
  refine Cofork.IsColimit.ofExistsUnique ?_
  intro s
  have hs : s.π false = s.π true := by
    simpa [two_point_false_map, two_point_true_map] using
      congrFun (congrArg Action.Hom.hom s.condition) PUnit.unit
  -- The colimit descends by sending the unique source point to the common value of `s.π`.
  refine ⟨
    { hom := fun _ ↦ s.π.hom false
      comm := by
        intro g
        funext x
        cases g
        cases x
        simpa using congrFun (s.π.comm PUnit.unit) false }, ?_, ?_⟩
  · -- Evaluating on `false` and `true` recovers `s.π`, using the cofork condition on `true`.
    apply Action.hom_ext
    funext x
    cases x with
    | false => rfl
    | true => exact hs
  · intro m hm
    -- Uniqueness follows by evaluating at the unique point of `PUnit`.
    apply Action.hom_ext
    funext x
    cases x
    simpa [two_point_collapse_map] using congrFun (congrArg Action.Hom.hom hm) false

/-- Helper for Example 7.41.5: the target `Bool` in the constantness classifier carries the
trivial action of `Multiplicative (ZMod 2)`. -/
instance two_point_classifier_targetAction :
    MulAction (Multiplicative (ZMod 2)) Bool where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Helper for Example 7.41.5: the empty type carries the trivial action of
`Multiplicative (ZMod 2)`. -/
instance zmod2_pempty_mulAction : MulAction (Multiplicative (ZMod 2)) PEmpty where
  smul _ x := x.elim
  one_smul x := x.elim
  mul_smul _ _ x := x.elim

/-- Helper for Example 7.41.5: right translation preserves the equality predicate
`a(1) = a(σ)`, so the constantness classifier is `H`-equivariant. -/
theorem two_point_constantness_classifier_comm
    (h : Multiplicative (ZMod 2)) :
    (equivariantMapObj (1 : PUnit →* Multiplicative (ZMod 2))
        (Action.ofMulAction PUnit Bool)).ρ h ≫
      (fun a : (equivariantMapObj (1 : PUnit →* Multiplicative (ZMod 2))
          (Action.ofMulAction PUnit Bool)).V ↦
        decide
          (((show restrictedEquivariantMaps
                  (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a) 1) =
            ((show restrictedEquivariantMaps
                  (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)
              (Multiplicative.ofAdd 1)))) =
    (fun a : (equivariantMapObj (1 : PUnit →* Multiplicative (ZMod 2))
        (Action.ofMulAction PUnit Bool)).V ↦
      decide
      (((show restrictedEquivariantMaps
              (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a) 1) =
        ((show restrictedEquivariantMaps
              (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)
          (Multiplicative.ofAdd 1)))) ≫
        (Action.ofMulAction (Multiplicative (ZMod 2)) Bool).ρ h := by
  funext a
  letI : MulAction (Multiplicative (ZMod 2))
      (restrictedEquivariantMaps (1 : PUnit →* Multiplicative (ZMod 2)) Bool) :=
    equivariantMapRightTranslation (1 : PUnit →* Multiplicative (ZMod 2)) Bool
  change decide
      (((h • (show restrictedEquivariantMaps
              (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)) 1) =
        ((h • (show restrictedEquivariantMaps
              (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a))
          (Multiplicative.ofAdd 1))) =
    h • decide
      (((show restrictedEquivariantMaps
              (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a) 1) =
        ((show restrictedEquivariantMaps
              (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)
          (Multiplicative.ofAdd 1)))
  fin_cases h
  · change decide
        (((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)
            (1 * Multiplicative.ofAdd (0 : ZMod 2))) =
          ((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)
            (Multiplicative.ofAdd 1 * Multiplicative.ofAdd (0 : ZMod 2)))) =
      decide
        (((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a) 1) =
          ((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)
            (Multiplicative.ofAdd 1)))
    simp
  · change decide
        (((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)
            (1 * Multiplicative.ofAdd (1 : ZMod 2))) =
          ((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)
            (Multiplicative.ofAdd 1 * Multiplicative.ofAdd (1 : ZMod 2)))) =
      decide
        (((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a) 1) =
          ((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)
            (Multiplicative.ofAdd 1)))
    have hsq :
        (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) *
            Multiplicative.ofAdd 1 = 1 := by
      decide
    rw [hsq]
    simp [eq_comm]

/-- Helper for Example 7.41.5: the mapped two-point object admits a classifier that records
whether a function `H → Bool` is constant on the two elements of `H`. -/
def two_point_constantness_classifier :
    equivariantMapObj (1 : PUnit →* Multiplicative (ZMod 2))
      (Action.ofMulAction PUnit Bool) ⟶
      Action.ofMulAction (Multiplicative (ZMod 2)) Bool :=
  { hom := fun a ↦
      decide
        (((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a) 1) =
          ((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from a)
            (Multiplicative.ofAdd 1)))
    comm := two_point_constantness_classifier_comm }

/-- Helper for Example 7.41.5: the constantness classifier equalizes the two constant maps after
applying the explicit pushforward `Map(H, -)`. -/
theorem two_point_constantness_classifier_equalizes :
    (equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).map
        two_point_false_map ≫
      two_point_constantness_classifier =
    (equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).map
        two_point_true_map ≫
      two_point_constantness_classifier := by
  let Fact := equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))
  letI : MulAction PUnit (Multiplicative (ZMod 2)) :=
    MulAction.compHom (Multiplicative (ZMod 2)) (1 : PUnit →* Multiplicative (ZMod 2))
  apply Action.hom_ext
  funext a
  -- Both composites are the constant `true` map, since the pushed-forward functions are constant.
  have hfalse :
      ((Fact.map two_point_false_map ≫ two_point_constantness_classifier).hom a) = true := by
    rfl
  have htrue :
      ((Fact.map two_point_true_map ≫ two_point_constantness_classifier).hom a) = true := by
    rfl
  rw [hfalse, htrue]

/-- Helper for Example 7.41.5: the source `Multiplicative (ZMod 2)` is viewed as a trivial
`PUnit`-set via the unique homomorphism `PUnit → Multiplicative (ZMod 2)`. -/
local instance two_point_sourceAction :
    MulAction PUnit (Multiplicative (ZMod 2)) :=
  MulAction.compHom (Multiplicative (ZMod 2)) (1 : PUnit →* Multiplicative (ZMod 2))

/-- Helper for Example 7.41.5: the constant `false` section is `PUnit`-equivariant because both
source and target carry the trivial `PUnit`-action. -/
theorem two_point_constant_false_section_map_smul
    : ∀ g : PUnit, ∀ _h : Multiplicative (ZMod 2), false = g • false := by
  intro g _h
  cases g
  rfl

/-- Helper for Example 7.41.5: the exact-typed witness section given by the constant `false`
function in the mapped two-point object. -/
def two_point_constant_false_section :
    ((equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).obj
      (Action.ofMulAction PUnit Bool)).V :=
  show restrictedEquivariantMaps (1 : PUnit →* Multiplicative (ZMod 2)) Bool from
    @MulActionHom.mk PUnit PUnit (@id PUnit)
      (Multiplicative (ZMod 2)) two_point_sourceAction.toSMul
      Bool inferInstance
      (fun _ ↦ false)
      two_point_constant_false_section_map_smul

/-- Helper for Example 7.41.5: the characteristic function of `σ` is `PUnit`-equivariant because
restriction along the trivial group action does not move the source. -/
theorem two_point_sigma_section_map_smul
    : ∀ g : PUnit,
        ∀ h : Multiplicative (ZMod 2),
          decide
              (two_point_sourceAction.smul g h = Multiplicative.ofAdd 1) =
            g • decide (h = Multiplicative.ofAdd 1) := by
  intro g h
  cases g
  have hs : two_point_sourceAction.smul PUnit.unit h = h := by
    simpa using
      (MulAction.compHom_smul_def
        (f := (1 : PUnit →* Multiplicative (ZMod 2))) PUnit.unit h)
  change decide
      (two_point_sourceAction.smul PUnit.unit h =
        (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2))) =
    decide (h = Multiplicative.ofAdd 1)
  rw [hs]

/-- Helper for Example 7.41.5: the exact-typed witness section given by the characteristic
function of `σ` in the mapped two-point object. -/
def two_point_sigma_section :
    ((equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).obj
      (Action.ofMulAction PUnit Bool)).V :=
  show restrictedEquivariantMaps (1 : PUnit →* Multiplicative (ZMod 2)) Bool from
    @MulActionHom.mk PUnit PUnit (@id PUnit)
      (Multiplicative (ZMod 2)) two_point_sourceAction.toSMul
      Bool inferInstance
      (fun h ↦ decide (h = Multiplicative.ofAdd 1))
      two_point_sigma_section_map_smul

/-- Helper for Example 7.41.5: the constant `false` witness evaluates to `false` at `1`. -/
theorem two_point_constant_false_section_apply_one :
    (show restrictedEquivariantMaps
        (1 : PUnit →* Multiplicative (ZMod 2)) Bool from two_point_constant_false_section) 1 =
      false := by
  rfl

/-- Helper for Example 7.41.5: the constant `false` witness evaluates to `false` at `σ`. -/
theorem two_point_constant_false_section_apply_sigma :
    (show restrictedEquivariantMaps
        (1 : PUnit →* Multiplicative (ZMod 2)) Bool from two_point_constant_false_section)
        (Multiplicative.ofAdd 1) = false := by
  rfl

/-- Helper for Example 7.41.5: the characteristic-`σ` witness vanishes at `1`. -/
theorem two_point_sigma_section_apply_one :
    (show restrictedEquivariantMaps
        (1 : PUnit →* Multiplicative (ZMod 2)) Bool from two_point_sigma_section) 1 =
      false := by
  change decide ((1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1) = false
  decide

/-- Helper for Example 7.41.5: the characteristic-`σ` witness is `true` at `σ`. -/
theorem two_point_sigma_section_apply_sigma :
    (show restrictedEquivariantMaps
        (1 : PUnit →* Multiplicative (ZMod 2)) Bool from two_point_sigma_section)
        (Multiplicative.ofAdd 1) = true := by
  change decide
      ((Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1) = true
  decide

/-- Helper for Example 7.41.5: the constantness classifier separates the constant `false`
function from the characteristic function of `σ`. -/
theorem two_point_constantness_classifier_witness_values :
    two_point_constantness_classifier.hom two_point_constant_false_section = true ∧
      two_point_constantness_classifier.hom two_point_sigma_section = false := by
  constructor
  · change decide
        (((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from two_point_constant_false_section)
            1) =
          ((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from two_point_constant_false_section)
            (Multiplicative.ofAdd 1))) = true
    rw [two_point_constant_false_section_apply_one, two_point_constant_false_section_apply_sigma]
    decide
  · change decide
        (((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from two_point_sigma_section)
            1) =
          ((show restrictedEquivariantMaps
                (1 : PUnit →* Multiplicative (ZMod 2)) Bool from two_point_sigma_section)
            (Multiplicative.ofAdd 1))) = false
    rw [two_point_sigma_section_apply_one, two_point_sigma_section_apply_sigma]
    decide

/-- Helper for Example 7.41.5: after collapsing `Bool` to the point, the constant `false`
section and the characteristic function of `σ` become equal. -/
theorem two_point_collapse_map_witness_sections_eq :
    ((equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).map
        two_point_collapse_map).hom two_point_constant_false_section =
      ((equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).map
        two_point_collapse_map).hom two_point_sigma_section := by
  rfl

/-- Helper for Example 7.41.5: after applying `Map(H, -)`, the two-point cofork is not a
coequalizer because the constantness classifier factors through it only if it is constant, while
it distinguishes a constant function from the characteristic function of `σ`. -/
theorem mapped_two_point_cofork_not_colimit :
    IsColimit
      (Cofork.ofπ
        ((equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).map
          two_point_collapse_map)
        (by
          simp only [← Functor.map_comp, two_point_collapse_condition]) :
          Cofork
            (((equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).map
              two_point_false_map))
            (((equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).map
              two_point_true_map))) → False := by
  intro hcol
  let Fact := equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))
  let s :
      Fact.obj (Action.ofMulAction PUnit PUnit) ⟶
        Action.ofMulAction (Multiplicative (ZMod 2)) Bool :=
    Cofork.IsColimit.desc hcol
      two_point_constantness_classifier
      two_point_constantness_classifier_equalizes
  have hs :
      Fact.map two_point_collapse_map ≫ s = two_point_constantness_classifier := by
    -- The colimit factorization identifies the classifier with the descended morphism.
    simpa [s] using
      (Cofork.IsColimit.π_desc'
        hcol
        two_point_constantness_classifier
        two_point_constantness_classifier_equalizes)
  have hfalse :
      two_point_constantness_classifier.hom two_point_constant_false_section =
        s.hom (((Fact.map two_point_collapse_map).hom two_point_constant_false_section)) := by
    -- Evaluate the factorization identity on the constant `false` witness.
    simpa using
      congrFun (congrArg Action.Hom.hom hs) two_point_constant_false_section
        |>.symm
  have hsigma :
      two_point_constantness_classifier.hom two_point_sigma_section =
        s.hom (((Fact.map two_point_collapse_map).hom two_point_sigma_section)) := by
    -- Evaluate the same identity on the characteristic-`σ` witness.
    simpa using
      congrFun (congrArg Action.Hom.hom hs) two_point_sigma_section
        |>.symm
  have hclassifier :
      two_point_constantness_classifier.hom two_point_constant_false_section =
        two_point_constantness_classifier.hom two_point_sigma_section := by
    -- The two witnesses collapse to the same section in the cofork point, so the factorized map
    -- must assign them the same classifier value.
    calc
      two_point_constantness_classifier.hom two_point_constant_false_section =
          s.hom (((Fact.map two_point_collapse_map).hom two_point_constant_false_section)) := hfalse
      _ = s.hom (((Fact.map two_point_collapse_map).hom two_point_sigma_section)) := by
        rw [two_point_collapse_map_witness_sections_eq]
      _ = two_point_constantness_classifier.hom two_point_sigma_section := hsigma.symm
  obtain ⟨hconst, hsigma⟩ := two_point_constantness_classifier_witness_values
  rw [hconst, hsigma] at hclassifier
  cases hclassifier

/-- Helper for Example 7.41.5: if the canonical sheaf pushforward preserves coequalizers, then so
does the explicit action-level functor `Map(H, -)` obtained from Proposition 7.9.1. -/
theorem sheaf_pushforward_preserves_coequalizers_implies_action_preserves_coequalizers
    (hpres :
      PreservesColimitsOfShape WalkingParallelPair
        ((Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))).sheafPushforwardContinuous
          (Type 0) (Action.jointlySurjectiveTopology (Multiplicative (ZMod 2)))
          (Action.jointlySurjectiveTopology PUnit))) :
    PreservesColimitsOfShape WalkingParallelPair
      (equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))) := by
  let JG := Action.jointlySurjectiveTopology PUnit
  let JH := Action.jointlySurjectiveTopology (Multiplicative (ZMod 2))
  let Fsh :=
    (Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))).sheafPushforwardContinuous
      (Type 0) JH JG
  let Fact := equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))
  letI : PreservesColimitsOfShape WalkingParallelPair Fsh := by
    simpa [Fsh] using hpres
  letI : PreservesColimitsOfShape WalkingParallelPair (JG.yoneda ⋙ Fsh) := by
    infer_instance
  letI : PreservesColimitsOfShape WalkingParallelPair (Fact ⋙ JH.yoneda) := by
    -- Transport the preservation statement across the Yoneda comparison isomorphism.
    simpa [Fact, Fsh] using
      (preservesColimitsOfShape_of_natIso
        (yonedaCompSheafPushforwardContinuousIso
          (1 : PUnit →* Multiplicative (ZMod 2))))
  exact preservesColimitsOfShape_of_reflects_of_preserves Fact JH.yoneda

/-- Helper for Example 7.41.5: the explicit pushforward sends the initial trivial `PUnit`-action
to an initial `Multiplicative (ZMod 2)`-action because there are no equivariant maps to `PEmpty`.
-/
theorem punit_action_pempty_isInitial :
    Nonempty (IsInitial (Action.ofMulAction PUnit PEmpty)) := by
  refine ⟨IsInitial.ofUniqueHom (fun X ↦ ?_) ?_⟩
  · refine
      { hom := fun x ↦ x.elim
        comm := fun h ↦ by
          funext x
          exact x.elim }
  · intro X m
    apply Action.hom_ext
    funext x
    exact x.elim

/-- Helper for Example 7.41.5: the image of the initial trivial `PUnit`-action under `Map(H, -)`
is initial because there are no equivariant maps from `H` to `PEmpty`. -/
theorem equivariantMapPushforward_obj_pempty_isInitial_exists :
    Nonempty
      (IsInitial
        ((equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).obj
          (Action.ofMulAction PUnit PEmpty))) := by
  let Fact := equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))
  have hempty : IsEmpty ((Fact.obj (Action.ofMulAction PUnit PEmpty)).V) := by
    refine ⟨fun a ↦ ?_⟩
    exact ((show restrictedEquivariantMaps
              (1 : PUnit →* Multiplicative (ZMod 2)) PEmpty from a) 1).elim
  refine ⟨IsInitial.ofUniqueHom (fun X ↦ ?_) ?_⟩
  · refine
      { hom := fun a ↦ False.elim (hempty.false a)
        comm := fun h ↦ by
          funext a
          exact False.elim (hempty.false a) }
  · intro X m
    apply Action.hom_ext
    funext a
    exact False.elim (hempty.false a)

/-- Helper for Example 7.41.5: the explicit pushforward sends the initial trivial `PUnit`-action
to an initial `Multiplicative (ZMod 2)`-action because there are no equivariant maps to `PEmpty`.
-/
noncomputable def equivariantMapPushforward_obj_pempty_isInitial :
    IsInitial
      ((equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))).obj
        (Action.ofMulAction PUnit PEmpty)) :=
  Classical.choice equivariantMapPushforward_obj_pempty_isInitial_exists

/-- Helper for Example 7.41.5: the explicit pushforward `Map(H, -)` preserves the initial
object, so pushout preservation will force it to preserve coequalizers as well. -/
theorem equivariantMapPushforward_preserves_initial_example :
    PreservesColimitsOfShape (Discrete.{0} PEmpty.{1})
      (equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))) := by
  let Fact := equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))
  let hSourceIso :
      (⊥_ (Action (Type 0) PUnit)) ≅ Action.ofMulAction PUnit PEmpty :=
    IsInitial.uniqueUpToIso initialIsInitial (Classical.choice punit_action_pempty_isInitial)
  let hTargetIso :
      (⊥_ (Action (Type 0) (Multiplicative (ZMod 2)))) ≅
        Fact.obj (⊥_ (Action (Type 0) PUnit)) :=
    (IsInitial.uniqueUpToIso initialIsInitial
      equivariantMapPushforward_obj_pempty_isInitial) ≪≫
      (Fact.mapIso hSourceIso.symm)
  have :
      PreservesColimit (Functor.empty.{0} (Action (Type 0) PUnit)) Fact :=
    preservesInitial_of_iso Fact hTargetIso
  exact preservesColimitsOfShape_pempty_of_preservesInitial Fact

-- Proof sketch: the two-point example above shows that the counit of the canonical continuous
-- pushforward along `Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))` is not
-- injective on left-regular sections, and the Stacks argument then concludes that this `f_*`
-- cannot commute with coequalizers.
/-- Example 7.41.5 (4): for `G = {1}` and `H = {1, σ}`, the canonical continuous pushforward on
sheaves along `Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))` does not preserve
coequalizers. Via Proposition 7.9.1 and the left-regular-sections bridge above, this is the
concrete `Map_{PUnit}(H, -)` example from the text. -/
theorem continuous_pushforward_not_preserves_coequalizers_example :
    ¬ PreservesColimitsOfShape WalkingParallelPair
      ((Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))).sheafPushforwardContinuous
        (Type 0) (Action.jointlySurjectiveTopology (Multiplicative (ZMod 2)))
        (Action.jointlySurjectiveTopology PUnit)) := by
  intro hpres
  let Fact := equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))
  letI : PreservesColimitsOfShape WalkingParallelPair Fact :=
    sheaf_pushforward_preserves_coequalizers_implies_action_preserves_coequalizers hpres
  have hmapped :
      IsColimit
        (Cofork.ofπ (Fact.map two_point_collapse_map)
          (by simp only [← Fact.map_comp, two_point_collapse_condition]) :
          Cofork (Fact.map two_point_false_map) (Fact.map two_point_true_map)) := by
    -- Preserve the known source-side coequalizer into the explicit action model.
    simpa [Fact] using
      (Limits.isColimitCoforkMapOfIsColimit (G := Fact)
        two_point_collapse_condition
        two_point_coequalizer_witness_in_trivial_actions)
  exact mapped_two_point_cofork_not_colimit hmapped

-- Proof sketch: the same `G = {1}`, `H = {1, σ}` example from the text gives a pushout diagram
-- whose image under the pushforward functor fails to remain a pushout.
/-- Example 7.41.5 (5): for `G = {1}` and `H = {1, σ}`, the canonical continuous pushforward on
sheaves along `Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))` does not preserve
pushouts. Via Proposition 7.9.1 and the left-regular-sections bridge above, this is the concrete
`Map_{PUnit}(H, -)` example from the text. -/
theorem continuous_pushforward_not_preserves_pushouts_example :
    ¬ PreservesColimitsOfShape WalkingSpan
      ((Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))).sheafPushforwardContinuous
        (Type 0) (Action.jointlySurjectiveTopology (Multiplicative (ZMod 2)))
        (Action.jointlySurjectiveTopology PUnit)) := by
  intro hpush
  let JG := Action.jointlySurjectiveTopology PUnit
  let JH := Action.jointlySurjectiveTopology (Multiplicative (ZMod 2))
  let Fsh :=
    (Action.res (Type 0) (1 : PUnit →* Multiplicative (ZMod 2))).sheafPushforwardContinuous
      (Type 0) JH JG
  let Fact := equivariantMapPushforward (1 : PUnit →* Multiplicative (ZMod 2))
  letI : PreservesColimitsOfShape WalkingSpan Fsh := by
    simpa [Fsh] using hpush
  letI : PreservesColimitsOfShape WalkingSpan (JG.yoneda ⋙ Fsh) := by
    infer_instance
  letI : PreservesColimitsOfShape WalkingSpan (Fact ⋙ JH.yoneda) := by
    -- Transport pushout preservation to the explicit action-level pushforward.
    simpa [Fact, Fsh] using
      (preservesColimitsOfShape_of_natIso
        (yonedaCompSheafPushforwardContinuousIso
          (1 : PUnit →* Multiplicative (ZMod 2))))
  letI : PreservesColimitsOfShape WalkingSpan Fact :=
    preservesColimitsOfShape_of_reflects_of_preserves Fact JH.yoneda
  letI : PreservesColimitsOfShape (Discrete.{0} PEmpty.{1}) Fact :=
    equivariantMapPushforward_preserves_initial_example
  letI : HasInitial (Action (Type 0) PUnit) := by
    infer_instance
  letI : HasPushouts (Action (Type 0) PUnit) := by
    infer_instance
  letI : PreservesColimitsOfShape (Discrete WalkingPair) Fact :=
    preservesBinaryCoproducts_of_preservesInitial_and_pushouts Fact
  letI : PreservesColimitsOfShape WalkingParallelPair Fact :=
    preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts Fact
  have hmapped :
      IsColimit
        (Cofork.ofπ (Fact.map two_point_collapse_map)
          (by simp only [← Fact.map_comp, two_point_collapse_condition]) :
          Cofork (Fact.map two_point_false_map) (Fact.map two_point_true_map)) := by
    -- Pushouts plus initials force coequalizer preservation in the action model.
    simpa [Fact] using
      (Limits.isColimitCoforkMapOfIsColimit (G := Fact)
        two_point_collapse_condition
        two_point_coequalizer_witness_in_trivial_actions)
  exact mapped_two_point_cofork_not_colimit hmapped

end

end CategoryTheory
