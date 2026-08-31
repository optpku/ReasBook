module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MorphismProperty
open LeftFraction
open LeftFraction.Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable {D : Type*} [Category D]
variable {X X' Y Y' : C}

local notation "Q" => LeftFraction.Localization.Q

/- Domain-style sampling for Lemma 4.27.10:
- primary domain: left-fraction localizations and commutative-square lifting;
- inspected owner declarations:
  `Functor.IsLocalization`,
  `MorphismProperty.LeftFraction.map_comp_map_eq_map`,
  `Localization.exists_leftFraction`,
  `MorphismProperty.map_eq_iff_postcomp`;
- best owner abstraction: an ambient localization functor `L` with `[L.IsLocalization W]`,
  together with `W.LeftFraction` for the primitive roof data representing the vertical localization
  morphisms; `homMk` is only the canonical-model bridge for `Q W`.

Primitive data: the two roof representatives `aFrac : W.LeftFraction X X'` and
`bFrac : W.LeftFraction Y Y'`.
Derived API: their represented morphisms `aFrac.map L (Localization.inverts L W)` and
  `bFrac.map L (Localization.inverts L W)` in an arbitrary localization; for `L = Q W` these
  become `homMk aFrac` and `homMk bFrac`.

Source/core/bridge triage:
- `source-facing`: `commutative_square_lifts_to_left_fraction_square`;
- `core/canonical`: `localization_commutative_square_has_left_fraction_lift`,
  `Functor.IsLocalization`, `W.LeftFraction`, and `LeftFraction.map`;
- `bridge/view`: specialization from `LeftFraction.map` to `homMk` for `Q W`, and the
  equation-form companion `commutative_square_lifts_to_left_fraction_square_eq`. -/

private theorem leftFraction_map_postcomp_eq (L : C ⥤ D) [L.IsLocalization W]
    {X Y : C} (φ : W.LeftFraction X Y)
    {Z : C} (t : φ.Y' ⟶ Z) (ht : W (φ.s ≫ t)) :
    φ.map L (Localization.inverts L W) =
      (LeftFraction.mk (φ.f ≫ t) (φ.s ≫ t) ht).map L (Localization.inverts L W) := by
  exact (MorphismProperty.LeftFraction.map_eq_iff L W φ
    (LeftFraction.mk (φ.f ≫ t) (φ.s ≫ t) ht)).2 ⟨Z, t, 𝟙 _, by simp, by simp, ht⟩

-- Proof sketch: represent `a` by a left fraction with denominator in `W`; use the
-- left-calculus square-completion axiom to compare it with `f'`; refine the target of `f''` so
-- that `b` is also represented by such a fraction; then compare the two composites in the
-- localization, cancel the common denominator, and apply `map_eq_iff_postcomp` to force the left
-- square to commute after one more refinement.
/-- A commutative square in a localization can be represented by a commutative diagram in `C`
whose vertical arrows are denominators in `W`. -/
theorem localization_commutative_square_has_left_fraction_lift
    (L : C ⥤ D) [L.IsLocalization W]
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X')
    (b : L.obj Y ⟶ L.obj Y')
    (hcomm : CommSq (L.map f) a b (L.map f')) :
    ∃ (aFrac : {φ : W.LeftFraction X X' //
          a = φ.map L (Localization.inverts L W)})
      (bFrac : {φ : W.LeftFraction Y Y' //
          b = φ.map L (Localization.inverts L W)})
      (f'' : aFrac.val.Y' ⟶ bFrac.val.Y'),
        CommSq f aFrac.val.f bFrac.val.f f'' ∧
          CommSq f' aFrac.val.s bFrac.val.s f'' := by
  obtain ⟨aFrac, ha⟩ := Localization.exists_leftFraction L W a
  obtain ⟨b₀, hb₀⟩ := Localization.exists_leftFraction L W b
  let cFrac : W.LeftFraction aFrac.Y' Y' :=
    RightFraction.leftFraction (RightFraction.mk aFrac.s aFrac.hs f')
  have hc : f' ≫ cFrac.s = aFrac.s ≫ cFrac.f := by
    simpa [cFrac] using
      (RightFraction.leftFraction_fac (RightFraction.mk aFrac.s aFrac.hs f'))
  let dFrac : W.LeftFraction cFrac.Y' b₀.Y' :=
    RightFraction.leftFraction (RightFraction.mk cFrac.s cFrac.hs b₀.s)
  have hd : b₀.s ≫ dFrac.s = cFrac.s ≫ dFrac.f := by
    simpa [dFrac] using
      (RightFraction.leftFraction_fac (RightFraction.mk cFrac.s cFrac.hs b₀.s))
  have hcommon : W (cFrac.s ≫ dFrac.f) := by
    simpa [hd] using W.comp_mem _ _ b₀.hs dFrac.hs
  let bRef : W.LeftFraction Y Y' :=
    LeftFraction.mk (b₀.f ≫ dFrac.s) (cFrac.s ≫ dFrac.f) hcommon
  let aRef : W.LeftFraction X Y' :=
    LeftFraction.mk (aFrac.f ≫ cFrac.f ≫ dFrac.f) (cFrac.s ≫ dFrac.f) hcommon
  have hbRef : b = bRef.map L (Localization.inverts L W) := by
    calc
      b = b₀.map L (Localization.inverts L W) := hb₀
      _ = bRef.map L (Localization.inverts L W) := by
        exact (MorphismProperty.LeftFraction.map_eq_iff L W b₀ bRef).2
          ⟨dFrac.Y', dFrac.s, 𝟙 _, by simpa [bRef, Category.assoc] using hd, by simp [bRef],
            by simpa using W.comp_mem _ _ b₀.hs dFrac.hs⟩
  have haRef : a ≫ L.map f' = aRef.map L (Localization.inverts L W) := by
    calc
      a ≫ L.map f' = aFrac.map L (Localization.inverts L W) ≫ L.map f' := by
        simpa using congrArg (fun k ↦ k ≫ L.map f') ha
      _ = (LeftFraction.mk (aFrac.f ≫ cFrac.f) cFrac.s cFrac.hs).map L
          (Localization.inverts L W) := by
        simpa [cFrac, LeftFraction.comp₀, MorphismProperty.LeftFraction.map_ofHom] using
          MorphismProperty.LeftFraction.map_comp_map_eq_map aFrac (ofHom W f') cFrac hc L
      _ = aRef.map L (Localization.inverts L W) := by
        simpa [aRef, Category.assoc] using leftFraction_map_postcomp_eq W L
          (LeftFraction.mk (aFrac.f ≫ cFrac.f) cFrac.s cFrac.hs) dFrac.f hcommon
  have hEq :
      (LeftFraction.mk (f ≫ bRef.f) bRef.s bRef.hs).map L (Localization.inverts L W) =
        aRef.map L (Localization.inverts L W) := by
    calc
      (LeftFraction.mk (f ≫ bRef.f) bRef.s bRef.hs).map L (Localization.inverts L W) =
          L.map f ≫ bRef.map L (Localization.inverts L W) := by
        symm
        simpa [LeftFraction.comp₀, MorphismProperty.LeftFraction.map_ofHom] using
          (MorphismProperty.LeftFraction.map_comp_map_eq_map (ofHom W f) bRef
            (ofHom W bRef.f) (by simp) L)
      _ = a ≫ L.map f' := by simpa [hbRef] using hcomm.w
      _ = aRef.map L (Localization.inverts L W) := haRef
  have hEq' :
      (LeftFraction.mk (f ≫ bRef.f) aRef.s aRef.hs).map L (Localization.inverts L W) =
        (LeftFraction.mk aRef.f aRef.s aRef.hs).map L (Localization.inverts L W) := by
    simpa [aRef, bRef] using hEq
  have hmap : L.map (f ≫ bRef.f) = L.map aRef.f := by
    simpa using congrArg (fun k ↦ k ≫ L.map aRef.s) hEq'
  obtain ⟨Z, u, hu, hnum⟩ := (map_eq_iff_postcomp L W (f ≫ bRef.f) aRef.f).mp hmap
  let bFrac : W.LeftFraction Y Y' :=
    LeftFraction.mk (bRef.f ≫ u) (bRef.s ≫ u) (W.comp_mem _ _ bRef.hs hu)
  let f'' : aFrac.Y' ⟶ bFrac.Y' := cFrac.f ≫ dFrac.f ≫ u
  refine ⟨⟨aFrac, ha⟩, ⟨bFrac, ?_⟩, f'', ?_, ?_⟩
  · calc
      b = bRef.map L (Localization.inverts L W) := hbRef
      _ = bFrac.map L (Localization.inverts L W) := by
        dsimp [bFrac]
        simpa [Category.assoc] using leftFraction_map_postcomp_eq W L bRef u
          (W.comp_mem _ _ bRef.hs hu)
  · refine ⟨?_⟩
    dsimp [bFrac, bRef, aRef, f''] at hnum ⊢
    simpa [Category.assoc] using hnum
  · refine ⟨?_⟩
    dsimp [bFrac, bRef, f'']
    calc
      f' ≫ ((cFrac.s ≫ dFrac.f) ≫ u) = (f' ≫ cFrac.s) ≫ dFrac.f ≫ u := by
        simp [Category.assoc]
      _ = (aFrac.s ≫ cFrac.f) ≫ dFrac.f ≫ u := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ dFrac.f ≫ u) hc
      _ = aFrac.s ≫ (cFrac.f ≫ dFrac.f ≫ u) := by simp [Category.assoc]

/-- Lemma 4.27.10: a commutative square in the left-fraction localization can be represented by a
commutative diagram in `C` whose vertical arrows are denominators in `W`. -/
theorem commutative_square_lifts_to_left_fraction_square
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : (Q W).obj X ⟶ (Q W).obj X')
    (b : (Q W).obj Y ⟶ (Q W).obj Y')
    (hcomm :
      CommSq ((Q W).map f) a b
        ((Q W).map f')) :
    ∃ (aFrac : {φ : W.LeftFraction X X' // a = homMk φ})
      (bFrac : {φ : W.LeftFraction Y Y' // b = homMk φ})
      (f'' : aFrac.val.Y' ⟶ bFrac.val.Y'),
        CommSq f aFrac.val.f bFrac.val.f f'' ∧
          CommSq f' aFrac.val.s bFrac.val.s f'' := by
  obtain ⟨aFrac, bFrac, f'', hleft, hright⟩ :=
    localization_commutative_square_has_left_fraction_lift W (Q W) f f' a b hcomm
  refine ⟨⟨aFrac.val, ?_⟩, ⟨bFrac.val, ?_⟩, f'', hleft, hright⟩
  · simpa [LeftFraction.Localization.homMk_eq] using aFrac.property
  · simpa [LeftFraction.Localization.homMk_eq] using bFrac.property

/-- Companion to Lemma 4.27.10 in equation form. -/
theorem commutative_square_lifts_to_left_fraction_square_eq
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : (Q W).obj X ⟶ (Q W).obj X')
    (b : (Q W).obj Y ⟶ (Q W).obj Y')
    (hcomm :
      (Q W).map f ≫ b =
        a ≫ (Q W).map f') :
    ∃ (aFrac : {φ : W.LeftFraction X X' // a = homMk φ})
      (bFrac : {φ : W.LeftFraction Y Y' // b = homMk φ})
      (f'' : aFrac.val.Y' ⟶ bFrac.val.Y'),
        f ≫ bFrac.val.f = aFrac.val.f ≫ f'' ∧
          aFrac.val.s ≫ f'' = f' ≫ bFrac.val.s := by
  obtain ⟨aFrac, bFrac, f'', hleft, hright⟩ :=
    commutative_square_lifts_to_left_fraction_square W f f' a b ⟨hcomm⟩
  exact ⟨aFrac, bFrac, f'', hleft.w, hright.w.symm⟩

end CategoryTheory
