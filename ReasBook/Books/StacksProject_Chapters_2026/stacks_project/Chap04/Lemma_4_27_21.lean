module

public import stacks_project.Chap04.Definition_4_27_20

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (S : MorphismProperty C) [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]

/- Domain-style sampling for Lemma 4.27.21:
- source-facing content: the Stacks description of the saturated closure
  `S' = { f | ∃ g h, S (f ≫ g) ∧ S (h ≫ f) }`
- core/canonical owner abstraction: the localization functor `S.Q` and the induced morphism
  property `S.saturatedClosure` of morphisms inverted by `S.Q`
- upstream owner facts inspected before refining:
  `MorphismProperty.Q_inverts`,
  `MorphismProperty.IsInvertedBy.iff_le_inverseImage_isomorphisms`,
  `Functor.q_isLocalization`,
  `Adjunction.isLocalization`

Primitive data: the two calculus-of-fractions owner instances on `S`.
Derived API: the owner `S.saturatedClosure`, its saturation, and the comparison with the textbook
source-facing description. In particular, the inclusion `S ≤ S.saturatedClosure` is already the
canonical owner fact `S.Q_inverts`, so no parallel inclusion wrapper is kept.

Source/core/bridge triage:
- `source-facing`: the textbook characterization of `S.saturatedClosure`
- `core/canonical`: the owner `S.saturatedClosure`
- `bridge/view`: the minimality theorem `saturatedClosure_le_iff`
-/

/-- The saturated closure of `S`, i.e. the morphisms inverted by the canonical localization
functor `S.Q`. -/
abbrev saturatedClosure : MorphismProperty C :=
  (isomorphisms S.Localization).inverseImage S.Q

/-- Helper for Lemma 4.27.21: every morphism of `S` already lies in the saturated closure. -/
lemma mem_saturatedClosure_of_mem {X Y : C} {f : X ⟶ Y} (hf : S f) :
    S.saturatedClosure f := by
  -- The localization functor inverts each morphism of `S`.
  change IsIso (S.Q.map f)
  exact Localization.inverts S.Q S _ hf

/-- Helper for Lemma 4.27.21: by definition the localization functor `S.Q` inverts the saturated
closure of `S`. -/
lemma saturatedClosure_inverts : S.saturatedClosure.IsInvertedBy S.Q := by
  intro X Y f hf
  -- Unfolding the inverse-image definition turns membership into invertibility of `S.Q.map f`.
  change IsIso (S.Q.map f) at hf
  exact hf

/-- Helper for Lemma 4.27.21: two-sided composites in `S` force the middle morphism to become an
isomorphism after localization. -/
lemma mem_saturatedClosure_of_two_sided_S_composites {X Y Z₁ Z₂ : C} {f : X ⟶ Y}
    {g : Y ⟶ Z₁} {h : Z₂ ⟶ X} (hfg : S (f ≫ g)) (hhf : S (h ≫ f)) :
    S.saturatedClosure f := by
  -- We build explicit right and left inverses for `S.Q.map f` from the two composite witnesses.
  change IsIso (S.Q.map f)
  let invRight : S.Q.obj Y ⟶ S.Q.obj X :=
    S.Q.map g ≫ (Localization.isoOfHom S.Q S (f ≫ g) hfg).inv
  let invLeft : S.Q.obj Y ⟶ S.Q.obj X :=
    (Localization.isoOfHom S.Q S (h ≫ f) hhf).inv ≫ S.Q.map h
  have h_right : S.Q.map f ≫ invRight = 𝟙 _ := by
    -- The right inverse comes from the inverse of `S.Q.map (f ≫ g)`.
    dsimp [invRight]
    simpa [Functor.map_comp, Category.assoc] using
      (Localization.isoOfHom_hom_inv_id S.Q S (f ≫ g) hfg)
  have h_left_aux : invLeft ≫ S.Q.map f = 𝟙 _ := by
    -- The left inverse comes from the inverse of `S.Q.map (h ≫ f)`.
    dsimp [invLeft]
    simpa [Functor.map_comp, Category.assoc] using
      (Localization.isoOfHom_inv_hom_id S.Q S (h ≫ f) hhf)
  have h_inv_eq : invLeft = invRight := by
    -- Any left inverse and right inverse of the same morphism agree.
    calc
      invLeft = invLeft ≫ 𝟙 _ := by simp
      _ = invLeft ≫ (S.Q.map f ≫ invRight) := by rw [h_right]
      _ = (invLeft ≫ S.Q.map f) ≫ invRight := by simp [Category.assoc]
      _ = invRight := by rw [h_left_aux, Category.id_comp]
  have h_left : invRight ≫ S.Q.map f = 𝟙 _ := by
    rw [← h_inv_eq, h_left_aux]
  exact ⟨invRight, h_right, h_left⟩

/-- Helper for Lemma 4.27.21: a morphism in the saturated closure admits a postcomposition that
lies in `S`. -/
lemma exists_postcomp_mem_of_mem_saturatedClosure {X Y : C} {f : X ⟶ Y}
    (hf : S.saturatedClosure f) :
    ∃ (Z : C) (g : Y ⟶ Z), S (f ≫ g) := by
  -- Route correction: represent the inverse of `S.Q.map f` by a left fraction, then clear the
  -- denominator to turn localization invertibility into an `S`-postcomposition witness.
  change IsIso (S.Q.map f) at hf
  letI : IsIso (S.Q.map f) := hf
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction S.Q S (inv (S.Q.map f))
  have hcomp : S.Q.map f ≫ φ.map S.Q (Localization.inverts S.Q S) = 𝟙 _ := by
    rw [← hφ]
    exact IsIso.hom_inv_id (S.Q.map f)
  have hmap : S.Q.map (f ≫ φ.f) = S.Q.map φ.s := by
    -- Multiplying by the denominator of the left fraction removes the inverse.
    calc
      S.Q.map (f ≫ φ.f) = S.Q.map f ≫ S.Q.map φ.f := by
        rw [Functor.map_comp]
      _ = S.Q.map f ≫ (φ.map S.Q (Localization.inverts S.Q S) ≫ S.Q.map φ.s) := by
        rw [MorphismProperty.LeftFraction.map_comp_map_s]
      _ = (S.Q.map f ≫ φ.map S.Q (Localization.inverts S.Q S)) ≫ S.Q.map φ.s := by
        simp [Category.assoc]
      _ = 𝟙 _ ≫ S.Q.map φ.s := by rw [hcomp]
      _ = S.Q.map φ.s := by simp
  obtain ⟨Z, t, ht, hpost⟩ :=
    (MorphismProperty.map_eq_iff_postcomp S.Q S (f ≫ φ.f) φ.s).mp hmap
  refine ⟨Z, φ.f ≫ t, ?_⟩
  -- The required composite is identified with the `S`-morphism `φ.s ≫ t`.
  have hs : S (φ.s ≫ t) := S.comp_mem _ _ φ.hs ht
  have hpost' : f ≫ φ.f ≫ t = φ.s ≫ t := by
    simpa [Category.assoc] using hpost
  rw [hpost']
  exact hs

/-- Helper for Lemma 4.27.21: a morphism in the saturated closure admits a precomposition that
lies in `S`. -/
lemma exists_precomp_mem_of_mem_saturatedClosure {X Y : C} {f : X ⟶ Y}
    (hf : S.saturatedClosure f) :
    ∃ (Z : C) (h : Z ⟶ X), S (h ≫ f) := by
  -- Route correction: use a right-fraction presentation of the inverse to recover an
  -- `S`-precomposition witness.
  change IsIso (S.Q.map f) at hf
  letI : IsIso (S.Q.map f) := hf
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction S.Q S (inv (S.Q.map f))
  have hcomp : φ.map S.Q (Localization.inverts S.Q S) ≫ S.Q.map f = 𝟙 _ := by
    rw [← hφ]
    exact IsIso.inv_hom_id (S.Q.map f)
  have hmap : S.Q.map (φ.f ≫ f) = S.Q.map φ.s := by
    -- Multiplying by the denominator of the right fraction removes the inverse.
    calc
      S.Q.map (φ.f ≫ f) = S.Q.map φ.f ≫ S.Q.map f := by
        rw [Functor.map_comp]
      _ = (S.Q.map φ.s ≫ φ.map S.Q (Localization.inverts S.Q S)) ≫ S.Q.map f := by
        rw [MorphismProperty.RightFraction.map_s_comp_map]
      _ = S.Q.map φ.s ≫ (φ.map S.Q (Localization.inverts S.Q S) ≫ S.Q.map f) := by
        simp
      _ = S.Q.map φ.s ≫ 𝟙 _ := by rw [hcomp]
      _ = S.Q.map φ.s := by simp
  obtain ⟨Z, t, ht, hpre⟩ :=
    (MorphismProperty.map_eq_iff_precomp S.Q S (φ.f ≫ f) φ.s).mp hmap
  refine ⟨Z, t ≫ φ.f, ?_⟩
  -- The required composite is identified with the `S`-morphism `t ≫ φ.s`.
  have hs : S (t ≫ φ.s) := S.comp_mem _ _ ht φ.hs
  simpa [Category.assoc, hpre] using hs

/-- Lemma 4.27.21: for a multiplicative system `S`, the morphisms whose image under the canonical
localization functor `S.Q : C ⥤ S.Localization` is an isomorphism are exactly the textbook set
`S'` of morphisms `f` for which there exist arrows `g` and `h` with `f ≫ g ∈ S` and
`h ≫ f ∈ S`. -/
theorem saturatedClosure_eq :
    S.saturatedClosure =
      fun X Y f ↦
        ∃ (Z₁ Z₂ : C) (g : Y ⟶ Z₁) (h : Z₂ ⟶ X), S (f ≫ g) ∧ S (h ≫ f) := by
  ext X Y f
  constructor
  · intro hf
    -- Extract one witness on each side from the inverse of `S.Q.map f`.
    obtain ⟨Z₁, g, hfg⟩ := exists_postcomp_mem_of_mem_saturatedClosure S hf
    obtain ⟨Z₂, h, hhf⟩ := exists_precomp_mem_of_mem_saturatedClosure S hf
    exact ⟨Z₁, Z₂, g, h, hfg, hhf⟩
  · rintro ⟨Z₁, Z₂, g, h, hfg, hhf⟩
    -- Two-sided composite witnesses already force invertibility in the localization.
    exact mem_saturatedClosure_of_two_sided_S_composites S hfg hhf

/-- The morphisms inverted by `S.Q` form a saturated multiplicative system. -/
instance saturatedClosure_isSaturatedMultiplicativeSystem :
    IsSaturatedMultiplicativeSystem S.saturatedClosure := by
  refine
    { toHasLeftCalculusOfFractions := ?_
      toHasRightCalculusOfFractions := ?_
      saturation := ?_ }
  · refine
      { exists_leftFraction := ?_
        ext := ?_ }
    · intro X Y φ
      -- Represent the localized morphism of the right fraction by a left fraction over `S`, then
      -- refine the denominator until the equality holds on the nose.
      obtain ⟨ψ₀, hψ₀⟩ :=
        Localization.exists_leftFraction S.Q S (φ.map S.Q (saturatedClosure_inverts S))
      have hψ₀_assoc :
          ψ₀.map S.Q (Localization.inverts S.Q S) ≫ S.Q.map ψ₀.s = S.Q.map ψ₀.f :=
        MorphismProperty.LeftFraction.map_comp_map_s ψ₀ S.Q (Localization.inverts S.Q S)
      have hmap : S.Q.map (φ.s ≫ ψ₀.f) = S.Q.map (φ.f ≫ ψ₀.s) := by
        calc
          S.Q.map (φ.s ≫ ψ₀.f) = S.Q.map φ.s ≫ S.Q.map ψ₀.f := by
            rw [Functor.map_comp]
          _ =
              S.Q.map φ.s ≫ ψ₀.map S.Q (Localization.inverts S.Q S) ≫ S.Q.map ψ₀.s := by
            rw [← hψ₀_assoc]
          _ =
              (S.Q.map φ.s ≫ ψ₀.map S.Q (Localization.inverts S.Q S)) ≫ S.Q.map ψ₀.s := by
            simp [Category.assoc]
          _ =
              (S.Q.map φ.s ≫ φ.map S.Q (saturatedClosure_inverts S)) ≫ S.Q.map ψ₀.s := by
            rw [hψ₀]
          _ = S.Q.map φ.f ≫ S.Q.map ψ₀.s := by
            rw [MorphismProperty.RightFraction.map_s_comp_map]
          _ = S.Q.map (φ.f ≫ ψ₀.s) := by
            rw [Functor.map_comp]
      obtain ⟨Z, t, ht, hpost⟩ :=
        (MorphismProperty.map_eq_iff_postcomp S.Q S (φ.s ≫ ψ₀.f) (φ.f ≫ ψ₀.s)).mp hmap
      have hs : S.saturatedClosure (ψ₀.s ≫ t) :=
        mem_saturatedClosure_of_mem S (S.comp_mem _ _ ψ₀.hs ht)
      refine ⟨{ f := ψ₀.f ≫ t, s := ψ₀.s ≫ t, hs := hs }, ?_⟩
      -- The refined denominator clears the localization ambiguity.
      simpa [Category.assoc] using hpost.symm
    · intro X' X Y f₁ f₂ s hs hEq
      -- A precomposition witness in `S` for `s` reduces the equalization problem to the left
      -- calculus axiom already available for `S`.
      obtain ⟨Z, a, ha⟩ := exists_precomp_mem_of_mem_saturatedClosure S hs
      obtain ⟨Y', t, ht, hfac⟩ :=
        MorphismProperty.HasLeftCalculusOfFractions.ext (W := S) f₁ f₂ (a ≫ s) ha
          (by simpa [Category.assoc] using congrArg (fun k ↦ a ≫ k) hEq)
      exact ⟨Y', t, mem_saturatedClosure_of_mem S ht, hfac⟩
  · refine
      { exists_rightFraction := ?_
        ext := ?_ }
    · intro X Y φ
      -- Represent the localized morphism of the left fraction by a right fraction over `S`, then
      -- refine the numerator until the equality holds on the nose.
      obtain ⟨ψ₀, hψ₀⟩ :=
        Localization.exists_rightFraction S.Q S (φ.map S.Q (saturatedClosure_inverts S))
      have hmap : S.Q.map (ψ₀.s ≫ φ.f) = S.Q.map (ψ₀.f ≫ φ.s) := by
        calc
          S.Q.map (ψ₀.s ≫ φ.f) = S.Q.map ψ₀.s ≫ S.Q.map φ.f := by
            rw [Functor.map_comp]
          _ =
              S.Q.map ψ₀.s ≫
                (φ.map S.Q (saturatedClosure_inverts S) ≫ S.Q.map φ.s) := by
            rw [MorphismProperty.LeftFraction.map_comp_map_s]
          _ =
              (S.Q.map ψ₀.s ≫ φ.map S.Q (saturatedClosure_inverts S)) ≫ S.Q.map φ.s := by
            simp [Category.assoc]
          _ =
              (S.Q.map ψ₀.s ≫ ψ₀.map S.Q (Localization.inverts S.Q S)) ≫ S.Q.map φ.s := by
            rw [hψ₀]
          _ = S.Q.map ψ₀.f ≫ S.Q.map φ.s := by
            rw [MorphismProperty.RightFraction.map_s_comp_map]
          _ = S.Q.map (ψ₀.f ≫ φ.s) := by
            rw [Functor.map_comp]
      obtain ⟨Z, t, ht, hpre⟩ :=
        (MorphismProperty.map_eq_iff_precomp S.Q S (ψ₀.s ≫ φ.f) (ψ₀.f ≫ φ.s)).mp hmap
      have hs : S.saturatedClosure (t ≫ ψ₀.s) :=
        mem_saturatedClosure_of_mem S (S.comp_mem _ _ ht ψ₀.hs)
      refine ⟨{ s := t ≫ ψ₀.s, hs := hs, f := t ≫ ψ₀.f }, ?_⟩
      -- The refined numerator clears the localization ambiguity.
      simpa [Category.assoc] using hpre
    · intro X Y Y' f₁ f₂ s hs hEq
      -- A postcomposition witness in `S` for `s` reduces the equalization problem to the right
      -- calculus axiom already available for `S`.
      obtain ⟨Z, b, hb⟩ := exists_postcomp_mem_of_mem_saturatedClosure S hs
      obtain ⟨X', t, ht, hfac⟩ :=
        MorphismProperty.HasRightCalculusOfFractions.ext (W := S) f₁ f₂ (s ≫ b) hb
          (by simpa [Category.assoc] using congrArg (fun k ↦ k ≫ b) hEq)
      exact ⟨X', t, mem_saturatedClosure_of_mem S ht, hfac⟩
  · intro X0 X1 X2 X3 f g h hfg hgh
    -- A left witness from `f ≫ g` and a right witness from `g ≫ h` are exactly the data needed
    -- to show that `g` lies in the textbook characterization of the saturated closure.
    obtain ⟨Zl, a, ha⟩ := exists_precomp_mem_of_mem_saturatedClosure S hfg
    obtain ⟨Zr, b, hb⟩ := exists_postcomp_mem_of_mem_saturatedClosure S hgh
    rw [saturatedClosure_eq S]
    refine ⟨Zr, Zl, h ≫ b, a ≫ f, ?_, ?_⟩
    · simpa [Category.assoc] using hb
    · simpa [Category.assoc] using ha

/- The owner `S.saturatedClosure` is the smallest saturated multiplicative system containing `S`.
-/
theorem saturatedClosure_le_iff
    {T : MorphismProperty C} [IsSaturatedMultiplicativeSystem T] :
    S.saturatedClosure ≤ T ↔ S ≤ T := by
  constructor
  · intro h
    exact
      ((IsInvertedBy.iff_le_inverseImage_isomorphisms S S.Q).1 S.Q_inverts).trans h
  · intro hST
    rw [saturatedClosure_eq S]
    intro X Y f hf
    rcases hf with ⟨Z₁, Z₂, g, h, hfg, hhf⟩
    exact IsSaturatedMultiplicativeSystem.saturation h f g (hST _ hhf) (hST _ hfg)

/- The owner `S.saturatedClosure` lies in every saturated multiplicative system containing `S`. -/
theorem saturatedClosure_le
    {T : MorphismProperty C} [IsSaturatedMultiplicativeSystem T] (hST : S ≤ T) :
    S.saturatedClosure ≤ T :=
  (saturatedClosure_le_iff S).2 hST

end MorphismProperty
end CategoryTheory
