module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CategoryTheory

open MorphismProperty
open MorphismProperty.RightFraction
open Localization

variable {C : Type u} [Category.{v} C]

variable (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
variable {D : Type*} [Category D]
variable {X Y X' Y' : C}

/- Domain-style sampling for Lemma 4.27.18:
- primary domain: commutative squares in a localization with right-fraction representatives;
- inspected owner declarations:
  `Functor.IsLocalization`,
  `MorphismProperty.RightFraction`,
  `Localization.exists_rightFraction`,
  `MorphismProperty.RightFraction.map_eq_iff`,
  `MorphismProperty.map_eq_iff_precomp`;
- best owner abstraction: `Functor.IsLocalization W` for the ambient localization functor, with
  `W.RightFraction` as the primitive roof data representing the vertical localization morphisms.

Primitive data: the two right-fraction representatives `aFrac : W.RightFraction X X'` and
`bFrac : W.RightFraction Y Y'`.
Derived API: the represented localization morphisms
  `aFrac.map L (Localization.inverts L W)` and
  `bFrac.map L (Localization.inverts L W)` for an arbitrary localization functor `L`; for the
  canonical localization functor `W.Q`, these are exactly the source-facing vertical morphisms.

Source/core/bridge triage:
- `source-facing`: `commutative_square_lifts_to_right_fraction_square`;
- `core/canonical`: `localization_commutative_square_has_right_fraction_lift`, together with
  `Functor.IsLocalization`, `W.RightFraction`, and the owner-level equality criteria for
  represented localization morphisms;
- `bridge/view`: the equation-form companion
  `commutative_square_lifts_to_right_fraction_square_eq`. -/

private theorem rightFraction_map_precomp_eq
    (L : C ⥤ D) [L.IsLocalization W] {X Y : C} (φ : W.RightFraction X Y)
    {X'' : C} (t : X'' ⟶ φ.X') (ht : W (t ≫ φ.s)) :
    φ.map L (inverts L W) =
      (RightFraction.mk (t ≫ φ.s) ht (t ≫ φ.f)).map L (inverts L W) := by
  exact (MorphismProperty.RightFraction.map_eq_iff L W φ
    (RightFraction.mk (t ≫ φ.s) ht (t ≫ φ.f))).2
      ⟨X'', t, 𝟙 _, by simp, by simp, by simpa using ht⟩

/-- Core companion: a commutative square in any localization functor for `W` can be represented
by a commutative diagram in `C` after replacing the source and target by arrows in `W`. -/
theorem localization_commutative_square_has_right_fraction_lift
    (L : C ⥤ D) [L.IsLocalization W] (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X') (b : L.obj Y ⟶ L.obj Y')
    (hcomm : CommSq a (L.map f) (L.map f') b) :
    ∃ (aFrac : W.RightFraction X X') (bFrac : W.RightFraction Y Y')
      (f'' : aFrac.X' ⟶ bFrac.X'),
      CommSq f'' aFrac.s bFrac.s f ∧
        CommSq aFrac.f f'' f' bFrac.f ∧
        a = aFrac.map L (inverts L W) ∧
        b = bFrac.map L (inverts L W) := by
  obtain ⟨a₀, ha₀⟩ := exists_rightFraction L W a
  obtain ⟨bFrac, hb⟩ := exists_rightFraction L W b
  let cFrac : W.RightFraction X bFrac.X' :=
    (LeftFraction.mk f bFrac.s bFrac.hs).rightFraction
  have hc : cFrac.s ≫ f = cFrac.f ≫ bFrac.s := by
    simpa [cFrac] using
      (LeftFraction.rightFraction_fac (LeftFraction.mk f bFrac.s bFrac.hs))
  let dFrac : W.RightFraction cFrac.X' a₀.X' :=
    (LeftFraction.mk cFrac.s a₀.s a₀.hs).rightFraction
  have hd : dFrac.s ≫ cFrac.s = dFrac.f ≫ a₀.s := by
    simpa [dFrac] using
      (LeftFraction.rightFraction_fac (LeftFraction.mk cFrac.s a₀.s a₀.hs))
  have hleft :
      L.map dFrac.s ≫ L.map cFrac.s ≫ a = L.map (dFrac.f ≫ a₀.f) := by
    calc
      L.map dFrac.s ≫ L.map cFrac.s ≫ a =
          L.map dFrac.f ≫ L.map a₀.s ≫ a := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ a) (congrArg L.map hd)
      _ = L.map dFrac.f ≫ L.map a₀.s ≫ a₀.map L (inverts L W) := by
            rw [ha₀]
      _ = L.map dFrac.f ≫ L.map a₀.f := by
            simp
      _ = L.map (dFrac.f ≫ a₀.f) := by
            simp [Functor.map_comp]
  have hright :
      L.map cFrac.s ≫ L.map f ≫ b = L.map (cFrac.f ≫ bFrac.f) := by
    calc
      L.map cFrac.s ≫ L.map f ≫ b =
          L.map cFrac.f ≫ L.map bFrac.s ≫ b := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ b) (congrArg L.map hc)
      _ = L.map cFrac.f ≫ L.map bFrac.s ≫ bFrac.map L (inverts L W) := by
            rw [hb]
      _ = L.map cFrac.f ≫ L.map bFrac.f := by
            simp
      _ = L.map (cFrac.f ≫ bFrac.f) := by
            simp [Functor.map_comp]
  have hEq :
      L.map (dFrac.f ≫ a₀.f ≫ f') = L.map (dFrac.s ≫ cFrac.f ≫ bFrac.f) := by
    calc
      L.map (dFrac.f ≫ a₀.f ≫ f') =
          L.map (dFrac.f ≫ a₀.f) ≫ L.map f' := by
            simp [Functor.map_comp, Category.assoc]
      _ = (L.map dFrac.s ≫ L.map cFrac.s ≫ a) ≫ L.map f' := by
            rw [hleft]
      _ = L.map dFrac.s ≫ L.map cFrac.s ≫ (a ≫ L.map f') := by
            simp [Category.assoc]
      _ = L.map dFrac.s ≫ L.map cFrac.s ≫ (L.map f ≫ b) := by
            rw [hcomm.w]
      _ = L.map dFrac.s ≫ (L.map cFrac.s ≫ L.map f ≫ b) := by
            simp
      _ = L.map dFrac.s ≫ L.map (cFrac.f ≫ bFrac.f) := by
            rw [hright]
      _ = L.map (dFrac.s ≫ cFrac.f ≫ bFrac.f) := by
            simp [Functor.map_comp]
  obtain ⟨Z, u, hu, hnum⟩ :=
    (map_eq_iff_precomp L W (dFrac.f ≫ a₀.f ≫ f') (dFrac.s ≫ cFrac.f ≫ bFrac.f)).mp hEq
  have haFrac : W (u ≫ dFrac.f ≫ a₀.s) := by
    simpa [Category.assoc, hd] using
      W.comp_mem _ _ hu (W.comp_mem _ _ dFrac.hs cFrac.hs)
  let aFrac : W.RightFraction X X' :=
    RightFraction.mk (u ≫ dFrac.f ≫ a₀.s) haFrac (u ≫ dFrac.f ≫ a₀.f)
  let f'' : aFrac.X' ⟶ bFrac.X' := u ≫ dFrac.s ≫ cFrac.f
  refine ⟨aFrac, bFrac, f'', ?_, ?_, ?_, hb⟩
  · refine ⟨?_⟩
    dsimp [aFrac, f'']
    calc
      (u ≫ dFrac.s ≫ cFrac.f) ≫ bFrac.s = u ≫ dFrac.s ≫ (cFrac.f ≫ bFrac.s) := by
        simp [Category.assoc]
      _ = u ≫ dFrac.s ≫ (cFrac.s ≫ f) := by
        simpa [Category.assoc] using congrArg (fun k ↦ u ≫ dFrac.s ≫ k) hc.symm
      _ = u ≫ (dFrac.s ≫ cFrac.s) ≫ f := by
        simp [Category.assoc]
      _ = (u ≫ dFrac.f ≫ a₀.s) ≫ f := by
        simpa [Category.assoc] using congrArg (fun k ↦ u ≫ k ≫ f) hd
      _ = aFrac.s ≫ f := by
        simp [aFrac, Category.assoc]
  · refine ⟨?_⟩
    dsimp [aFrac, f'']
    simpa [Category.assoc] using hnum
  · calc
      a = a₀.map L (inverts L W) := ha₀
      _ = aFrac.map L (inverts L W) := by
        have haPrecomp : W ((u ≫ dFrac.f) ≫ a₀.s) := by
          simpa [Category.assoc] using haFrac
        dsimp [aFrac]
        simpa [Category.assoc] using
          rightFraction_map_precomp_eq W L a₀ (u ≫ dFrac.f) haPrecomp

/-- Equation-form companion for an arbitrary localization functor of `W`. -/
theorem localization_commutative_square_has_right_fraction_lift_eq
    (L : C ⥤ D) [L.IsLocalization W] (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X') (b : L.obj Y ⟶ L.obj Y')
    (hcomm : L.map f ≫ b = a ≫ L.map f') :
    ∃ (aFrac : W.RightFraction X X') (bFrac : W.RightFraction Y Y')
      (f'' : aFrac.X' ⟶ bFrac.X'),
      aFrac.s ≫ f = f'' ≫ bFrac.s ∧
        aFrac.f ≫ f' = f'' ≫ bFrac.f ∧
        a = aFrac.map L (inverts L W) ∧
        b = bFrac.map L (inverts L W) := by
  obtain ⟨aFrac, bFrac, f'', hleft, hright, ha, hb⟩ :=
    localization_commutative_square_has_right_fraction_lift W L f f' a b ⟨hcomm.symm⟩
  exact ⟨aFrac, bFrac, f'', hleft.w.symm, hright.w, ha, hb⟩

/-- Lemma 4.27.18: a commutative square in the canonical localization `W.Q` can be represented
by a commutative diagram in `C` whose vertical arrows are right-fraction denominators in `W`. -/
theorem commutative_square_lifts_to_right_fraction_square
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : W.Q.obj X ⟶ W.Q.obj X') (b : W.Q.obj Y ⟶ W.Q.obj Y')
    (hcomm : CommSq a (W.Q.map f) (W.Q.map f') b) :
    ∃ (aFrac : {φ : W.RightFraction X X' // a = φ.map W.Q (inverts _ _)})
      (bFrac : {φ : W.RightFraction Y Y' // b = φ.map W.Q (inverts _ _)})
      (f'' : aFrac.val.X' ⟶ bFrac.val.X'),
      CommSq f'' aFrac.val.s bFrac.val.s f ∧
        CommSq aFrac.val.f f'' f' bFrac.val.f := by
  obtain ⟨aFrac, bFrac, f'', hleft, hright, ha, hb⟩ :=
    localization_commutative_square_has_right_fraction_lift W W.Q f f' a b hcomm
  exact ⟨⟨aFrac, ha⟩, ⟨bFrac, hb⟩, f'', hleft, hright⟩

/-- Equation-form companion for the canonical right-fraction lift statement. -/
theorem commutative_square_lifts_to_right_fraction_square_eq
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : W.Q.obj X ⟶ W.Q.obj X') (b : W.Q.obj Y ⟶ W.Q.obj Y')
    (hcomm : W.Q.map f ≫ b = a ≫ W.Q.map f') :
    ∃ (aFrac : {φ : W.RightFraction X X' // a = φ.map W.Q (inverts _ _)})
      (bFrac : {φ : W.RightFraction Y Y' // b = φ.map W.Q (inverts _ _)})
      (f'' : aFrac.val.X' ⟶ bFrac.val.X'),
      aFrac.val.s ≫ f = f'' ≫ bFrac.val.s ∧
        aFrac.val.f ≫ f' = f'' ≫ bFrac.val.f := by
  obtain ⟨aFrac, bFrac, f'', hleft, hright⟩ :=
    commutative_square_lifts_to_right_fraction_square W f f' a b ⟨hcomm.symm⟩
  exact ⟨aFrac, bFrac, f'', hleft.w.symm, hright.w⟩

end CategoryTheory
