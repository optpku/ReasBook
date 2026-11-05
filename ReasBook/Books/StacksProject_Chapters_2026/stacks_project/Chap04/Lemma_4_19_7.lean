module

public import stacks_project.Chap04.Lemma_4_19_6
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe vI uI

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I]

local instance : Small.{max uI vI} I := small_max I

/- Domain-style sampling for Lemma 4.19.7:
- source-facing input: the chapter owner `HasSpanCocones`
- core/canonical owners in this domain: `Functor.PreservesMonomorphisms`,
  `NatTrans.mono_iff_mono_app`, `mono_iff_injective`,
  `Types.FilteredColimit.Rel`, and the stronger mathlib owner
  `MorphismProperty.IsStableUnderFilteredColimits (monomorphisms (Type _))`
- best owner abstraction here: the local instance
  `(colim : (I ⥤ Type _) ⥤ Type _).PreservesMonomorphisms` under `[HasSpanCocones I]`;
  the filtered-colimit owner is only a background comparison because it would strengthen the
  source hypothesis to filteredness
- target layer here: keep the monomorphism-preservation instance as the owner-level statement,
  and derive the source-facing injectivity formulations as thin bridge theorems
-/

private theorem rel_of_eqvGen_colimitTypeRel
    [HasSpanCocones I] {F : I ⥤ Type (max uI vI)}
    {p q : Σ i, F.obj i} (h : Relation.EqvGen F.ColimitTypeRel p q) :
    Types.FilteredColimit.Rel F p q := by
  induction h with
  | rel p q hpq =>
      exact Types.FilteredColimit.rel_of_colimitTypeRel F p q hpq
  | refl p =>
      exact ⟨p.1, 𝟙 p.1, 𝟙 p.1, rfl⟩
  | symm _ _ _ ih =>
      rcases ih with ⟨k, f, g, hfg⟩
      exact ⟨k, g, f, hfg.symm⟩
  | trans p q r _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨k₁, f₁, g₁, h₁⟩
      rcases ih₂ with ⟨k₂, f₂, g₂, h₂⟩
      obtain ⟨k, h₁₂, h₂₁, hh⟩ := HasSpanCocones.span g₁ f₂
      refine ⟨k, f₁ ≫ h₁₂, g₂ ≫ h₂₁, ?_⟩
      calc
        F.map (f₁ ≫ h₁₂) p.2 = F.map h₁₂ (F.map f₁ p.2) := by
          rw [FunctorToTypes.map_comp_apply]
        _ = F.map h₁₂ (F.map g₁ q.2) := by rw [h₁]
        _ = F.map (g₁ ≫ h₁₂) q.2 := by
          rw [FunctorToTypes.map_comp_apply]
        _ = F.map (f₂ ≫ h₂₁) q.2 := by rw [hh]
        _ = F.map h₂₁ (F.map f₂ q.2) := by
          rw [FunctorToTypes.map_comp_apply]
        _ = F.map h₂₁ (F.map g₂ r.2) := by rw [h₂]
        _ = F.map (g₂ ≫ h₂₁) r.2 := by
          rw [FunctorToTypes.map_comp_apply]

/-
Source/core/bridge triage for Lemma 4.19.7:
- `source-facing`: the full textbook payload, namely the injectivity statement for `Type`-valued
  colimits together with the assertion that the analogous statement fails for
  `AddCommGrpCat`.
- `core/canonical`: `(colim : (I ⥤ Type _) ⥤ Type _).PreservesMonomorphisms`.
- `bridge/view`: the injectivity reformulation obtained from `mono_iff_injective` together with
  the explicit `AddCommGrpCat` counterexample theorem.
-/

/-- Lemma 4.19.7, core/canonical form: if every span in `I` admits a cocone, then the colimit
functor on `Type`-valued diagrams preserves monomorphisms. -/
instance colim_preservesMonomorphisms_of_hasSpanCocones [HasSpanCocones I] :
    (colim : (I ⥤ Type (max uI vI)) ⥤ Type (max uI vI)).PreservesMonomorphisms where
  preserves := by
    intro M N α hα
    letI : Mono α := hα
    rw [mono_iff_injective]
    intro x y hxy
    obtain ⟨i, x, rfl⟩ := Types.jointly_surjective' x
    obtain ⟨j, y, rfl⟩ := Types.jointly_surjective' y
    simp only [Types.Colimit.ι_map_apply] at hxy
    have hrel :
        Types.FilteredColimit.Rel N ⟨i, α.app i x⟩ ⟨j, α.app j y⟩ :=
      rel_of_eqvGen_colimitTypeRel (Types.colimit_eq hxy)
    rcases hrel with ⟨k, f, g, hfg⟩
    have hxy' : M.map f x = M.map g y := by
      have hαk : Mono (α.app k) := (NatTrans.mono_iff_mono_app α).1 hα k
      apply (mono_iff_injective (α.app k)).1 hαk
      calc
        α.app k (M.map f x) = N.map f (α.app i x) := by
          simpa using congrFun (α.naturality f) x
        _ = N.map g (α.app j y) := hfg
        _ = α.app k (M.map g y) := by
          simpa using (congrFun (α.naturality g) y).symm
    exact Types.colimit_sound' f g hxy'

/-- Helper for Lemma 4.19.7: the one-object category attached to the group of order two admits
span cocones. -/
-- Proof sketch: every morphism is invertible, so for a span `x ⟶ y`, `x ⟶ z` we can choose the
-- unique object as apex and the inverses of the two arrows as fillers.
private theorem singleObj_order_two_hasSpanCocones :
    HasSpanCocones (SingleObj (Multiplicative (ZMod 2))) := by
  letI : Groupoid (SingleObj (Multiplicative (ZMod 2))) := inferInstance
  refine ⟨?_⟩
  intro x y z f g
  cases x
  cases y
  cases z
  refine ⟨PUnit.unit, inv f, inv g, ?_⟩
  simp

/-- Helper for Lemma 4.19.7: the shear endomorphism `(x, y) ↦ (x + y, y)` of `(ZMod 2)^2`
squares to the identity. -/
-- Proof sketch: check the two coordinates after a second application; the first acquires `y + y`
-- and this vanishes in `ZMod 2`.
private theorem zmod_two_pair_shear_involutive :
    let shear : End (AddCommGrpCat.of (ZMod 2 × ZMod 2)) :=
      AddCommGrpCat.ofHom
        { toFun := fun p ↦ (p.1 + p.2, p.2)
          map_zero' := by simp
          map_add' := by
            intro a b
            ext <;> simp [add_left_comm, add_comm] }
    shear ≫ shear = 𝟙 _ := by
  dsimp
  apply AddCommGrpCat.ext
  intro p
  rcases p with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> rfl

/-- Helper for Lemma 4.19.7: the inclusion `x ↦ (x, 0)` followed by the second projection is the
zero morphism. -/
-- Proof sketch: the second coordinate of `(x, 0)` is always zero.
private theorem zmod_two_first_inclusion_comp_second_projection :
    let inl : AddCommGrpCat.of (ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2 × ZMod 2) :=
      AddCommGrpCat.ofHom
        { toFun := fun x ↦ (x, 0)
          map_zero' := by simp
          map_add' := by
            intro a b
            ext <;> simp }
    let snd : AddCommGrpCat.of (ZMod 2 × ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2) :=
      AddCommGrpCat.ofHom
        { toFun := fun p ↦ p.2
          map_zero' := by simp
          map_add' := by
            intro a b
            simp }
    inl ≫ snd = 0 := by
  dsimp
  ext x
  simp

/-- Helper for Lemma 4.19.7: the inclusion of the first summand into `(ZMod 2) × (ZMod 2)`. -/
private def zmod_two_first_inclusion :
    AddCommGrpCat.of (ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2 × ZMod 2) :=
  AddCommGrpCat.ofHom (AddMonoidHom.inl (ZMod 2) (ZMod 2))

/-- Helper for Lemma 4.19.7: the inclusion of the second summand into `(ZMod 2) × (ZMod 2)`. -/
private def zmod_two_second_inclusion :
    AddCommGrpCat.of (ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2 × ZMod 2) :=
  AddCommGrpCat.ofHom (AddMonoidHom.inr (ZMod 2) (ZMod 2))

/-- Helper for Lemma 4.19.7: the projection to the second summand of `(ZMod 2) × (ZMod 2)`. -/
private def zmod_two_second_projection :
    AddCommGrpCat.of (ZMod 2 × ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2) :=
  AddCommGrpCat.ofHom (AddMonoidHom.snd (ZMod 2) (ZMod 2))

/-- Helper for Lemma 4.19.7: the shear endomorphism `(x, y) ↦ (x + y, y)` of `(ZMod 2)^2`. -/
private def zmod_two_pair_shear :
    End (AddCommGrpCat.of (ZMod 2 × ZMod 2)) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.prod
      (AddMonoidHom.fst (ZMod 2) (ZMod 2) + AddMonoidHom.snd (ZMod 2) (ZMod 2))
      (AddMonoidHom.snd (ZMod 2) (ZMod 2)))

/-- Helper for Lemma 4.19.7: the one-object index category used for the order-two counterexample. -/
private abbrev order_two_index :=
  SingleObj (Multiplicative (ZMod 2))

/-- Helper for Lemma 4.19.7: the distinguished non-identity endomorphism in the one-object
order-two category. -/
private def order_two_generator : End (SingleObj.star (Multiplicative (ZMod 2))) :=
  Multiplicative.ofAdd (0 : ZMod 2)

/-- Helper for Lemma 4.19.7: the first-summand inclusion is fixed by the shear action. -/
private theorem zmod_two_first_inclusion_comp_shear :
    zmod_two_first_inclusion ≫ zmod_two_pair_shear = zmod_two_first_inclusion := by
  ext x <;> simp [zmod_two_first_inclusion, zmod_two_pair_shear]

/-- Helper for Lemma 4.19.7: the second projection is fixed by the shear action. -/
private theorem zmod_two_pair_shear_comp_second_projection :
    zmod_two_pair_shear ≫ zmod_two_second_projection = zmod_two_second_projection := by
  ext x
  simp [zmod_two_pair_shear, zmod_two_second_projection]

-- Helper route for Lemma 4.19.7: package the explicit factor through the second projection and
-- then promote it to the stated `∃!` factorization theorem.
/-- Helper for Lemma 4.19.7: the explicit factor through the second projection. -/
private def zmod_two_second_factor {W : AddCommGrpCat}
    (k : AddCommGrpCat.of (ZMod 2 × ZMod 2) ⟶ W) :
    AddCommGrpCat.of (ZMod 2) ⟶ W :=
  zmod_two_second_inclusion ≫ k

/-- Helper for Lemma 4.19.7: the explicit factor through `snd` really composes back to the
original shear-invariant map. -/
private theorem zmod_two_second_factor_comp {W : AddCommGrpCat}
    (k : AddCommGrpCat.of (ZMod 2 × ZMod 2) ⟶ W)
    (hk : zmod_two_pair_shear ≫ k = k) :
    zmod_two_second_projection ≫ zmod_two_second_factor k = k := by
  -- First kill the first basis vector using the shear relation on `(0, 1)`.
  ext x
  have h11 : k (1, 1) = k (0, 1) := by
    simpa [zmod_two_pair_shear] using
      congrArg (fun f : AddCommGrpCat.of (ZMod 2 × ZMod 2) ⟶ W ↦ f (0, 1)) hk
  have hadd : k (1, 1) = k (1, 0) + k (0, 1) := by
    simpa using k.hom.map_add (1, 0) (0, 1)
  have h10 : k (1, 0) = 0 := by
    have : k (1, 0) + k (0, 1) = 0 + k (0, 1) := by
      rw [← hadd, h11, zero_add]
    exact add_right_cancel this
  have hfst : k (x.1, 0) = 0 := by
    rcases x with ⟨x1, x2⟩
    fin_cases x1
    · have hzero : k ((0, 0) : ZMod 2 × ZMod 2) = 0 := by
        calc
          k ((0, 0) : ZMod 2 × ZMod 2) = k 0 := by rfl
          _ = 0 := by exact k.hom.map_zero
      simpa using hzero
    · simpa using h10
  -- Split `(x, y)` as `(x, 0) + (0, y)` and use additivity.
  calc
    ((zmod_two_second_projection ≫ zmod_two_second_factor k) x) = k (0, x.2) := by
      rfl
    _ = k (x.1, 0) + k (0, x.2) := by
      rw [hfst, zero_add]
    _ = k ((x.1, 0) + (0, x.2)) := by
      symm
      simpa using k.hom.map_add (x.1, 0) (0, x.2)
    _ = k x := by
      rcases x with ⟨x1, x2⟩
      simp

/-- Helper for Lemma 4.19.7: the factor through `snd` is unique. -/
private theorem zmod_two_second_factor_unique {W : AddCommGrpCat}
    (k : AddCommGrpCat.of (ZMod 2 × ZMod 2) ⟶ W)
    (l : AddCommGrpCat.of (ZMod 2) ⟶ W)
    (hl : zmod_two_second_projection ≫ l = k) :
    l = zmod_two_second_factor k := by
  -- Evaluate the factorization identity on the second-summand inclusion.
  ext y
  simpa [zmod_two_second_projection, zmod_two_second_inclusion, zmod_two_second_factor] using
    congrArg (fun f : AddCommGrpCat.of (ZMod 2 × ZMod 2) ⟶ W ↦ f (0, y)) hl

private theorem shear_invariant_factors_through_snd {W : AddCommGrpCat}
    (k : AddCommGrpCat.of (ZMod 2 × ZMod 2) ⟶ W)
    (hk : zmod_two_pair_shear ≫ k = k) :
    ∃! l : AddCommGrpCat.of (ZMod 2) ⟶ W,
      zmod_two_second_projection ≫ l = k := by
  refine ⟨zmod_two_second_factor k, zmod_two_second_factor_comp k hk, ?_⟩
  intro l hl
  exact zmod_two_second_factor_unique k l hl

-- Proof sketch: the remaining work is to package the trivial and shear actions on the one-object
-- order-two category into explicit colimit cocones and then transport `colim.map α` across those
-- identifications.
/-- Helper for Lemma 4.19.7: the lifted one-object category attached to the group of order two. -/
private abbrev lifted_order_two_index : Type :=
  SingleObj (ULift.{uI} (Multiplicative (ZMod 2)))

/-- Helper for Lemma 4.19.7: the lifted one-object order-two category admits span cocones. -/
-- Proof sketch: every morphism is invertible, so we again take the unique object as apex and use
-- inverse morphisms as the dotted fillers.
private theorem lifted_singleObj_order_two_hasSpanCocones :
    HasSpanCocones lifted_order_two_index := by
  letI : Groupoid lifted_order_two_index := inferInstance
  refine ⟨?_⟩
  intro x y z f g
  cases x
  cases y
  cases z
  refine ⟨PUnit.unit, inv f, inv g, ?_⟩
  simp

/-- Helper for Lemma 4.19.7: the identity endomorphism of `ZMod 2` is involutive. -/
private theorem zmod_two_identity_involutive :
    (𝟙 (AddCommGrpCat.of (ZMod 2))) ≫ 𝟙 _ = 𝟙 _ := by
  simp

/-- Helper for Lemma 4.19.7: the trivial endomorphism assignment on `ZMod 2` indexed by the
lifted order-two monoid. -/
private def lifted_order_two_end_action_add {A : AddCommGrpCat} (e : End A) : ZMod 2 → End A
  | 0 => 𝟙 A
  | _ => e

/-- Helper for Lemma 4.19.7: addition in `ZMod 2` matches composition for the chosen involution. -/
-- Proof sketch: check the four possible sums in `ZMod 2`; the only nontrivial case is
-- `1 + 1 = 0`, where we use the involutivity hypothesis.
private theorem lifted_order_two_end_action_add_map_add {A : AddCommGrpCat} (e : End A)
    (he : e ≫ e = 𝟙 A) (a b : ZMod 2) :
    lifted_order_two_end_action_add e (a + b) =
      lifted_order_two_end_action_add e a * lifted_order_two_end_action_add e b := by
  fin_cases a <;> fin_cases b
  · change 𝟙 A = 𝟙 A ≫ 𝟙 A
    simp
  · change e = e ≫ 𝟙 A
    simp
  · change e = 𝟙 A ≫ e
    simp
  · change 𝟙 A = e ≫ e
    simpa using he.symm

/-- Helper for Lemma 4.19.7: the lifted order-two monoid acts through the chosen involution. -/
private def lifted_order_two_end_action {A : AddCommGrpCat} (e : End A) :
    ULift.{uI} (Multiplicative (ZMod 2)) → End A :=
  fun a ↦ lifted_order_two_end_action_add e (Multiplicative.toAdd a.down)

/-- Helper for Lemma 4.19.7: the lifted order-two action sends the identity to the identity. -/
private theorem lifted_order_two_end_action_map_one {A : AddCommGrpCat} (e : End A) :
    lifted_order_two_end_action e 1 = 𝟙 A := by
  rfl

/-- Helper for Lemma 4.19.7: the lifted order-two action is multiplicative. -/
-- Proof sketch: after projecting down from `ULift`, this is exactly the checked four-case
-- computation on `ZMod 2`.
private theorem lifted_order_two_end_action_map_mul {A : AddCommGrpCat} (e : End A)
    (he : e ≫ e = 𝟙 A) (a b : ULift.{uI} (Multiplicative (ZMod 2))) :
    lifted_order_two_end_action e (a * b) =
      lifted_order_two_end_action e a * lifted_order_two_end_action e b := by
  change
    lifted_order_two_end_action_add e (Multiplicative.toAdd ((a * b).down)) =
      lifted_order_two_end_action_add e (Multiplicative.toAdd a.down) *
        lifted_order_two_end_action_add e (Multiplicative.toAdd b.down)
  simpa using
    lifted_order_two_end_action_add_map_add e he (Multiplicative.toAdd a.down)
      (Multiplicative.toAdd b.down)

/-- Helper for Lemma 4.19.7: the lifted order-two action packaged as a monoid hom. -/
private def lifted_order_two_action_hom (A : AddCommGrpCat) (e : End A) (he : e ≫ e = 𝟙 A) :
    ULift.{uI} (Multiplicative (ZMod 2)) →* End A where
  toFun := lifted_order_two_end_action e
  map_one' := lifted_order_two_end_action_map_one e
  map_mul' := lifted_order_two_end_action_map_mul e he

/-- Helper for Lemma 4.19.7: the lifted order-two action viewed as a diagram in
`AddCommGrpCat`. -/
private def lifted_order_two_action_functor (A : AddCommGrpCat) (e : End A)
    (he : e ≫ e = 𝟙 A) : lifted_order_two_index ⥤ AddCommGrpCat :=
  SingleObj.functor (lifted_order_two_action_hom A e he)

/-- Helper for Lemma 4.19.7: the trivial action cocone on `ZMod 2` is well defined. -/
-- Proof sketch: every morphism of the trivial action is the identity, so the cocone leg is
-- constant.
private theorem lifted_trivial_order_two_action_leg_commutes
    (a : ULift.{uI} (Multiplicative (ZMod 2))) :
    lifted_order_two_end_action (A := AddCommGrpCat.of (ZMod 2)) (𝟙 _) a ≫ 𝟙 _ = 𝟙 _ := by
  rcases a with ⟨a⟩
  fin_cases a
  · change 𝟙 (AddCommGrpCat.of (ZMod 2)) ≫ 𝟙 _ = 𝟙 _
    simp
  · change 𝟙 (AddCommGrpCat.of (ZMod 2)) ≫ 𝟙 _ = 𝟙 _
    simp

/-- Helper for Lemma 4.19.7: the first-summand inclusion intertwines the trivial and shear
lifted order-two actions. -/
-- Proof sketch: on the nontrivial generator, this is exactly the computation
-- `inl ≫ shear = inl`.
private theorem lifted_zmod_two_first_inclusion_intertwines
    (a : ULift.{uI} (Multiplicative (ZMod 2))) :
    lifted_order_two_end_action (A := AddCommGrpCat.of (ZMod 2)) (𝟙 _) a ≫
        zmod_two_first_inclusion =
        zmod_two_first_inclusion ≫
        lifted_order_two_end_action (A := AddCommGrpCat.of (ZMod 2 × ZMod 2))
          zmod_two_pair_shear a := by
  rcases a with ⟨a⟩
  fin_cases a
  · change 𝟙 (AddCommGrpCat.of (ZMod 2)) ≫ zmod_two_first_inclusion =
      zmod_two_first_inclusion ≫ 𝟙 (AddCommGrpCat.of (ZMod 2 × ZMod 2))
    simp
  · change 𝟙 (AddCommGrpCat.of (ZMod 2)) ≫ zmod_two_first_inclusion =
      zmod_two_first_inclusion ≫ zmod_two_pair_shear
    simpa using zmod_two_first_inclusion_comp_shear.symm

/-- Helper for Lemma 4.19.7: the second projection is a cocone leg for the lifted shear action. -/
-- Proof sketch: on the nontrivial generator, this is the computation
-- `shear ≫ snd = snd`.
private theorem lifted_shear_order_two_action_leg_commutes
    (a : ULift.{uI} (Multiplicative (ZMod 2))) :
    lifted_order_two_end_action (A := AddCommGrpCat.of (ZMod 2 × ZMod 2))
        zmod_two_pair_shear a ≫ zmod_two_second_projection =
      zmod_two_second_projection := by
  rcases a with ⟨a⟩
  fin_cases a
  · change 𝟙 (AddCommGrpCat.of (ZMod 2 × ZMod 2)) ≫ zmod_two_second_projection =
      zmod_two_second_projection
    simp
  · change zmod_two_pair_shear ≫ zmod_two_second_projection = zmod_two_second_projection
    exact zmod_two_pair_shear_comp_second_projection

/-- Helper for Lemma 4.19.7: the identity cocone on the lifted trivial action. -/
private def lifted_trivial_order_two_action_cocone :
    Cocone
      (lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2)) (𝟙 _)
        zmod_two_identity_involutive) where
  pt := AddCommGrpCat.of (ZMod 2)
  ι := SingleObj.natTrans (𝟙 _) lifted_trivial_order_two_action_leg_commutes

/-- Helper for Lemma 4.19.7: every cocone on the lifted trivial action factors through the
identity cocone by its unique leg. -/
private def lifted_trivial_order_two_action_desc
    (s : Cocone
      (lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2)) (𝟙 _)
        zmod_two_identity_involutive)) :
    AddCommGrpCat.of (ZMod 2) ⟶ s.pt :=
  s.ι.app (SingleObj.star _)

/-- Helper for Lemma 4.19.7: the identity cocone has the expected factorization property. -/
private theorem lifted_trivial_order_two_action_fac
    (s : Cocone
      (lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2)) (𝟙 _)
        zmod_two_identity_involutive)) (j : lifted_order_two_index) :
    lifted_trivial_order_two_action_cocone.ι.app j ≫
        lifted_trivial_order_two_action_desc s =
      s.ι.app j := by
  cases j
  change 𝟙 _ ≫ s.ι.app (SingleObj.star _) = s.ι.app (SingleObj.star _)
  simp

/-- Helper for Lemma 4.19.7: the identity cocone on the lifted trivial action is universal. -/
private theorem lifted_trivial_order_two_action_uniq
    (s : Cocone
      (lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2)) (𝟙 _)
        zmod_two_identity_involutive))
    (m : AddCommGrpCat.of (ZMod 2) ⟶ s.pt)
    (hm : ∀ j : lifted_order_two_index,
      lifted_trivial_order_two_action_cocone.ι.app j ≫ m = s.ι.app j) :
    m = lifted_trivial_order_two_action_desc s := by
  simpa using hm (SingleObj.star _)

/-- Helper for Lemma 4.19.7: the identity cocone on the lifted trivial action is colimiting. -/
private def lifted_trivial_order_two_action_isColimit :
    IsColimit lifted_trivial_order_two_action_cocone :=
  IsColimit.mk
    lifted_trivial_order_two_action_desc
    lifted_trivial_order_two_action_fac
    lifted_trivial_order_two_action_uniq

/-- Helper for Lemma 4.19.7: the second-projection cocone on the lifted shear action. -/
private def lifted_shear_order_two_action_cocone :
    Cocone
      (lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2 × ZMod 2))
        zmod_two_pair_shear zmod_two_pair_shear_involutive) where
  pt := AddCommGrpCat.of (ZMod 2)
  ι := SingleObj.natTrans zmod_two_second_projection
    lifted_shear_order_two_action_leg_commutes

/-- Helper for Lemma 4.19.7: any cocone on the lifted shear action is invariant under the shear
endomorphism. -/
private theorem lifted_shear_order_two_action_invariant
    (s : Cocone
      (lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2 × ZMod 2))
        zmod_two_pair_shear zmod_two_pair_shear_involutive)) :
    zmod_two_pair_shear ≫ s.ι.app (SingleObj.star _) = s.ι.app (SingleObj.star _) := by
  simpa [lifted_order_two_action_functor, lifted_order_two_action_hom, lifted_order_two_end_action]
    using s.w (ULift.up (Multiplicative.ofAdd (1 : ZMod 2)))

/-- Helper for Lemma 4.19.7: the universal morphism out of the lifted shear cocone is the
factorization through `snd`. -/
private def lifted_shear_order_two_action_desc
    (s : Cocone
      (lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2 × ZMod 2))
        zmod_two_pair_shear zmod_two_pair_shear_involutive)) :
    AddCommGrpCat.of (ZMod 2) ⟶ s.pt :=
  zmod_two_second_factor (s.ι.app (SingleObj.star _))

/-- Helper for Lemma 4.19.7: the second-projection cocone has the expected factorization
property. -/
private theorem lifted_shear_order_two_action_fac
    (s : Cocone
      (lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2 × ZMod 2))
        zmod_two_pair_shear zmod_two_pair_shear_involutive)) (j : lifted_order_two_index) :
    lifted_shear_order_two_action_cocone.ι.app j ≫
        lifted_shear_order_two_action_desc s =
      s.ι.app j := by
  cases j
  simpa [lifted_shear_order_two_action_desc] using
    zmod_two_second_factor_comp (s.ι.app (SingleObj.star _))
      (lifted_shear_order_two_action_invariant s)

/-- Helper for Lemma 4.19.7: the second-projection cocone on the lifted shear action is
universal. -/
private theorem lifted_shear_order_two_action_uniq
    (s : Cocone
      (lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2 × ZMod 2))
        zmod_two_pair_shear zmod_two_pair_shear_involutive))
    (m : AddCommGrpCat.of (ZMod 2) ⟶ s.pt)
    (hm : ∀ j : lifted_order_two_index,
      lifted_shear_order_two_action_cocone.ι.app j ≫ m = s.ι.app j) :
    m = lifted_shear_order_two_action_desc s := by
  exact zmod_two_second_factor_unique (s.ι.app (SingleObj.star _)) m
    (hm (SingleObj.star _))

/-- Helper for Lemma 4.19.7: the second-projection cocone on the lifted shear action is
colimiting. -/
private def lifted_shear_order_two_action_isColimit :
    IsColimit lifted_shear_order_two_action_cocone :=
  IsColimit.mk
    lifted_shear_order_two_action_desc
    lifted_shear_order_two_action_fac
    lifted_shear_order_two_action_uniq

private theorem addCommGrpCat_counterexample_to_colimMap_mono :
    ∃ (J : Type) (_ : Category.{uI} J) (_ : HasSpanCocones J)
      (M N : J ⥤ AddCommGrpCat.{0}) (α : M ⟶ N),
      Mono α ∧ ¬ Mono (colim.map α) := by
  let M :=
    lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2)) (𝟙 _)
      zmod_two_identity_involutive
  let N :=
    lifted_order_two_action_functor (AddCommGrpCat.of (ZMod 2 × ZMod 2))
      zmod_two_pair_shear zmod_two_pair_shear_involutive
  let α : M ⟶ N := SingleObj.natTrans zmod_two_first_inclusion
    lifted_zmod_two_first_inclusion_intertwines
  refine ⟨lifted_order_two_index, (inferInstance : Category.{uI} lifted_order_two_index),
    lifted_singleObj_order_two_hasSpanCocones,
    M, N, α, ?_, ?_⟩
  · -- The component map is the first-summand inclusion, hence injective.
    refine (NatTrans.mono_iff_mono_app α).2 ?_
    intro j
    cases j
    refine (AddCommGrpCat.mono_iff_injective _).2 ?_
    intro x y hxy
    simpa [α, zmod_two_first_inclusion] using congrArg (fun p : ZMod 2 × ZMod 2 ↦ p.1) hxy
  · let tM : ColimitCocone M := ⟨lifted_trivial_order_two_action_cocone,
      lifted_trivial_order_two_action_isColimit⟩
    let tN : ColimitCocone N := ⟨lifted_shear_order_two_action_cocone,
      lifted_shear_order_two_action_isColimit⟩
    let eM : colimit M ≅ AddCommGrpCat.of (ZMod 2) := colimit.isoColimitCocone tM
    let eN : colimit N ≅ AddCommGrpCat.of (ZMod 2) := colimit.isoColimitCocone tN
    have hzero :
        colim.map α ≫ eN.hom =
          eM.hom ≫ (0 : AddCommGrpCat.of (ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2)) := by
      apply colimit.hom_ext
      intro j
      cases j
      have hleft :
          colimit.ι M (SingleObj.star _) ≫ (colim.map α ≫ eN.hom) = 0 := by
        calc
          colimit.ι M (SingleObj.star _) ≫ (colim.map α ≫ eN.hom)
              = (α.app (SingleObj.star _) ≫ colimit.ι N (SingleObj.star _)) ≫ eN.hom := by
                  simpa [Category.assoc] using
                    congrArg (fun f ↦ f ≫ eN.hom) (colimit.ι_map α (SingleObj.star _))
          _ = α.app (SingleObj.star _) ≫ (colimit.ι N (SingleObj.star _) ≫ eN.hom) := by
                simp [Category.assoc]
          _ = α.app (SingleObj.star _) ≫ zmod_two_second_projection := by
                ext x
                have hιN :
                    colimit.ι N (SingleObj.star _) ≫ eN.hom =
                      zmod_two_second_projection :=
                  colimit.isoColimitCocone_ι_hom tN (SingleObj.star _)
                simpa [Category.assoc] using
                  congrArg
                    (fun f : N.obj (SingleObj.star _) ⟶ AddCommGrpCat.of (ZMod 2) ↦
                      f ((α.app (SingleObj.star _)) x))
                    hιN
          _ = 0 := by
                simpa [α] using zmod_two_first_inclusion_comp_second_projection
      have hright :
          colimit.ι M (SingleObj.star _) ≫
              (eM.hom ≫ (0 : AddCommGrpCat.of (ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2))) = 0 := by
        simp
      exact hleft.trans hright.symm
    have htransport : eM.inv ≫ colim.map α ≫ eN.hom = 0 := by
      simpa [Category.assoc] using congrArg (fun f ↦ eM.inv ≫ f) hzero
    intro hmono
    -- Route correction: transport the colimit map to the explicit `ZMod 2` models, where it
    -- becomes the zero endomorphism and hence cannot be mono.
    have hinjLeft :
        Function.Injective (eM.inv : AddCommGrpCat.of (ZMod 2) ⟶ colimit M) :=
      (ConcreteCategory.bijective_of_isIso eM.inv).1
    have hinjMiddle : Function.Injective (colim.map α) :=
      (AddCommGrpCat.mono_iff_injective _).1 hmono
    have hinjRight :
        Function.Injective (eN.hom : colimit N ⟶ AddCommGrpCat.of (ZMod 2)) :=
      (ConcreteCategory.bijective_of_isIso eN.hom).1
    have hzeroInj :
        Function.Injective (0 : AddCommGrpCat.of (ZMod 2) ⟶ AddCommGrpCat.of (ZMod 2)) := by
      rw [← htransport]
      intro x y hxy
      exact hinjLeft (hinjMiddle (hinjRight hxy))
    have h01 : (0 : ZMod 2) = 1 := hzeroInj (by simp)
    have hne : (0 : ZMod 2) ≠ 1 := by
      decide
    exact hne h01

/-- Lemma 4.19.7, bridge/view form for `Type`: objectwise injective natural transformations induce
injective maps on colimits whenever every span in `I` admits a cocone. -/
theorem colimit_map_injective_of_app_injective [HasSpanCocones I]
    {M N : I ⥤ Type (max uI vI)} (α : M ⟶ N)
    (hα : ∀ i : I, Function.Injective (α.app i)) :
    Function.Injective (colim.map α) := by
  letI : Mono α := (NatTrans.mono_iff_mono_app α).2 fun i ↦ (mono_iff_injective _).2 (hα i)
  exact (mono_iff_injective _).1 (colim.map_mono α)

/-- Lemma 4.19.7, source-facing negative half: the analogous injectivity statement for colimits is
false in general for `AddCommGrpCat`-valued diagrams, even when every span admits a cocone. -/
theorem addCommGrpCat_counterexample_to_colimit_map_injective :
    ∃ (J : Type) (_ : Category.{uI} J) (_ : HasSpanCocones J)
      (M N : J ⥤ AddCommGrpCat.{0}) (α : M ⟶ N),
      (∀ j : J, Function.Injective (α.app j)) ∧
        ¬ Function.Injective (colim.map α) := by
  obtain ⟨J, hJ, hSpan, M, N, α, hMono, hcolim⟩ := addCommGrpCat_counterexample_to_colimMap_mono
  letI : Category J := hJ
  letI : HasSpanCocones J := hSpan
  have hMonoApp := (NatTrans.mono_iff_mono_app α).1 hMono
  refine ⟨J, hJ, hSpan, M, N, α, ?_, ?_⟩
  · intro j
    exact (AddCommGrpCat.mono_iff_injective _).1 (hMonoApp j)
  · simpa [AddCommGrpCat.mono_iff_injective] using hcolim

end CategoryTheory.Limits
