module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.Tactic.Recall

@[expose] public section

open CategoryTheory
open CategoryTheory.MorphismProperty
open OreLocalization

universe u

variable {R : Type u}

namespace CategoryTheory.SingleObj

variable [Monoid R]

/-- The morphism property on the one-object category `SingleObj R` induced by a submonoid
`S : Submonoid R`. -/
def submonoidProperty (S : Submonoid R) : MorphismProperty (SingleObj R) :=
  fun _ _ f ↦ f ∈ S

@[simp]
theorem submonoidProperty_iff (S : Submonoid R) {X Y : SingleObj R} (f : X ⟶ Y) :
    submonoidProperty S f ↔ f ∈ S :=
  Iff.rfl

section Monoid

variable (S : Submonoid R)

local notation "W" => submonoidProperty S

private def endHom {M : Type*} [Monoid M] {C : Type*} [Category C]
    (F : SingleObj M ⥤ C) : M →* End (F.obj (star M)) where
  toFun m := F.map m
  map_one' := by simpa [id_as_one] using F.map_id (star M)
  map_mul' m n := by
    simpa [comp_as_mul] using F.map_comp n m

/- Domain-style sampling for Remark 4.27.3:
- primary domain: Ore localization and categorical localization on the one-object category
  `SingleObj R`;
- declarations inspected:
  `SingleObj.submonoidProperty`,
  `MorphismProperty.IsMultiplicative`,
  `OreLocalization.OreSet`,
  `OreLocalization.nonempty_oreSet_iff`,
  `Functor.IsLocalization`,
  `Localization.equivalenceFromModel`;
- best owner abstractions:
  `(SingleObj.submonoidProperty S).IsMultiplicative` for the unconditional MS1 content,
  `OreSet S` for the monoid-side left denominator data, and
  `(numeratorHom.toFunctor : SingleObj R ⥤ SingleObj R[S⁻¹]).IsLocalization
    (SingleObj.submonoidProperty S)`
  for the categorical localization statement;
- primitive data: the submonoid `S` and the induced morphism property
  `SingleObj.submonoidProperty S` on `SingleObj R`;
- derived API: the multiplicative-system bridge `W.IsMultiplicative`, the left/right
  denominator conditions, the induced calculus-of-fractions structures, and the localization
  equivalence supplied by `Localization.equivalenceFromModel`.

This item is a `bridge/view`: it translates the source-facing denominator conditions into the
canonical owner objects `(SingleObj.submonoidProperty S).IsMultiplicative`, `OreSet S`, and
`Functor.IsLocalization`. The public API should therefore use those owners directly rather than
parallel wrapper declarations or `Nonempty (OreSet S)` shells. -/

/-- Remark 4.27.3, MS1 clause: for a submonoid `S` of a monoid `R`, the induced morphism
property on the one-object category `SingleObj R` is multiplicative. -/
@[instance]
theorem submonoidProperty_isMultiplicative : (submonoidProperty S).IsMultiplicative := by
  exact
    { id_mem := fun _ ↦ show (1 : R) ∈ S from S.one_mem
      comp_mem := fun f g hf hg ↦ by
        simpa [comp_as_mul] using S.mul_mem hg hf }

-- Proof sketch: unwind `HasRightCalculusOfFractions` for the morphism property defined by `S` on
-- `SingleObj R`; because there is only one object and composition is reversed multiplication, the
-- right Ore-completion and right-cancellation axioms become exactly the right permutable and
-- right reversible conditions.
/-- Companion translation of the right calculus-of-fractions axioms on `SingleObj R` into the
usual right denominator-set conditions on the submonoid `S`. -/
theorem hasRightCalculusOfFractions_iff_rightDenominatorConditions :
    (submonoidProperty S).HasRightCalculusOfFractions ↔
      (∀ (r : R) (s : S), ∃ (r' : R) (s' : S), r * s' = s * r') ∧
        ∀ (r₁ r₂ : R) (s : S), s * r₁ = s * r₂ → ∃ s' : S, r₁ * s' = r₂ * s' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro r s
      let φ : LeftFraction W (star R) (star R) :=
        { Y' := star R
          f := r
          s := (s : R)
          hs := s.2 }
      obtain ⟨ψ, hψ⟩ := h.exists_rightFraction φ
      refine ⟨ψ.f, ⟨ψ.s, ψ.hs⟩, ?_⟩
      simpa [comp_as_mul] using hψ
    · intro r₁ r₂ s hs
      let f₁ : star R ⟶ star R := r₁
      let f₂ : star R ⟶ star R := r₂
      let s₀ : star R ⟶ star R := s
      obtain ⟨_, t, ht, ht_eq⟩ :=
        h.ext f₁ f₂ s₀ s.2 (by simpa [f₁, f₂, s₀, comp_as_mul] using hs)
      refine ⟨⟨t, ht⟩, ?_⟩
      simpa [f₁, f₂, s₀, comp_as_mul] using ht_eq
  · rintro ⟨hOre, hCancel⟩
    refine
      { toIsMultiplicative := inferInstance
        exists_rightFraction := ?_
        ext := ?_ }
    · intro X Y φ
      obtain ⟨r', s', hs'⟩ := hOre φ.f ⟨φ.s, φ.hs⟩
      refine ⟨{ X' := star R, s := (s' : R), hs := s'.2, f := r' }, ?_⟩
      simpa [comp_as_mul] using hs'
    · intro X Y Y' f₁ f₂ s hs h_eq
      obtain ⟨t, ht⟩ := hCancel f₁ f₂ ⟨s, hs⟩ (by simpa [comp_as_mul] using h_eq)
      refine ⟨star R, (t : R), t.2, ?_⟩
      simpa [comp_as_mul] using ht

-- Proof sketch: with an `OreSet S`, the canonical owner fields `ore_right_cancel`, `oreNum`,
-- `oreDenom`, and `ore_eq` supply exactly the extension and Ore-completion data required by
-- `HasLeftCalculusOfFractions` for the morphism property `W` on `SingleObj R`.
/-- Remark 4.27.3, first clause, owner-level direction: the canonical left Ore-set structure
`OreSet S` induces a left calculus of fractions on `SingleObj R` for the morphism property coming
from `S`. -/
@[instance]
theorem submonoidProperty_hasLeftCalculusOfFractions [OreSet S] :
    (submonoidProperty S).HasLeftCalculusOfFractions := by
  exact
    { toIsMultiplicative := inferInstance
      exists_leftFraction := by
        intro X Y φ
        refine ⟨.mk (oreNum φ.f ⟨φ.s, φ.hs⟩) (oreDenom φ.f ⟨φ.s, φ.hs⟩)
          (oreDenom φ.f ⟨φ.s, φ.hs⟩).2, ?_⟩
        simpa [comp_as_mul] using ore_eq φ.f ⟨φ.s, φ.hs⟩
      ext := by
        intro X' X Y f₁ f₂ s hs h_eq
        obtain ⟨t, ht⟩ := ore_right_cancel f₁ f₂ ⟨s, hs⟩
          (by simpa [comp_as_mul] using h_eq)
        refine ⟨star R, (t : R), t.2, ?_⟩
        simpa [comp_as_mul] using ht }

-- Proof sketch: the forward implication is obtained by unwinding the left-fraction axioms on
-- `SingleObj R`; conversely, the denominator conditions are exactly `nonempty_oreSet_iff`, and
-- any resulting `OreSet S` feeds the instance above.
/-- Companion reformulation of Remark 4.27.3, first clause, in the traditional left
denominator-set conditions. -/
theorem hasLeftCalculusOfFractions_iff_leftDenominatorConditions :
    (submonoidProperty S).HasLeftCalculusOfFractions ↔
      (∀ (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s → ∃ s' : S, s' * r₁ = s' * r₂) ∧
        ∀ (r : R) (s : S), ∃ (r' : R) (s' : S), s' * r = r' * s := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro r₁ r₂ s hs
      let f₁ : star R ⟶ star R := r₁
      let f₂ : star R ⟶ star R := r₂
      let s₀ : star R ⟶ star R := s
      obtain ⟨_, t, ht, ht_eq⟩ :=
        h.ext f₁ f₂ s₀ s.2 (by simpa [f₁, f₂, s₀, comp_as_mul] using hs)
      refine ⟨⟨t, ht⟩, ?_⟩
      simpa [f₁, f₂, s₀, comp_as_mul] using ht_eq
    · intro r s
      let φ : RightFraction W (star R) (star R) :=
        { X' := star R
          s := (s : R)
          hs := s.2
          f := r }
      obtain ⟨ψ, hψ⟩ := h.exists_leftFraction φ
      refine ⟨ψ.f, ⟨ψ.s, ψ.hs⟩, ?_⟩
      simpa [comp_as_mul] using hψ
  · intro h
    rw [← nonempty_oreSet_iff] at h
    rcases h with ⟨hS⟩
    letI : OreSet S := hS
    exact inferInstance

private noncomputable def oreUnitHom {C : Type*} [Category C] (F : SingleObj R ⥤ C)
    (hF : (submonoidProperty S).IsInvertedBy F) : S →* Units (End (F.obj (star R))) :=
  Units.liftRight ((endHom F).comp S.subtype)
    (fun s ↦ by
      let f : star R ⟶ star R := s
      letI : IsIso (F.map f) := hF f s.2
      exact ⟨F.map f, inv (F.map f), by simp, by simp⟩)
    fun _ ↦ rfl

private def numeratorUnitHom {C : Type*} [Category C] [OreSet S]
    (F : SingleObj R[S⁻¹] ⥤ C) : S →* Units (End (F.obj (star R[S⁻¹]))) :=
  Units.liftRight ((endHom F).comp (numeratorHom.comp S.subtype))
    (fun s ↦ Units.map (endHom F) (numeratorUnit s))
    fun s ↦ by
      change (endHom F) ((s : R) /ₒ (1 : S)) = (endHom F) ((s : R) /ₒ (1 : S))
      rfl

@[simp]
private theorem coe_oreUnitHom {C : Type*} [Category C] (F : SingleObj R ⥤ C)
    (hF : (submonoidProperty S).IsInvertedBy F) (s : S) :
    ↑(oreUnitHom S F hF s) = endHom F s := by
  simp [oreUnitHom, endHom]

@[simp]
private theorem coe_numeratorUnitHom {C : Type*} [Category C] [OreSet S]
    (F : SingleObj R[S⁻¹] ⥤ C) (s : S) :
    ↑(numeratorUnitHom S F s) = endHom F (numeratorHom (s : R)) := by
  simp [numeratorUnitHom, endHom, numeratorHom_apply]

@[simp]
private theorem endHom_comp_numerator {C : Type*} [Category C] [OreSet S]
    (F : SingleObj R[S⁻¹] ⥤ C) (s : S) :
    endHom (numeratorHom.toFunctor ⋙ F) s = endHom F (numeratorHom (s : R)) := by
  rfl

private noncomputable def oreLocalizationStrictUniversalPropertyFixedTarget
    (E : Type*) [Category E] [OreSet S] :
    Localization.StrictUniversalPropertyFixedTarget
      ((numeratorHom : R →* R[S⁻¹]).toFunctor) (submonoidProperty S) E
    where
  inverts := by
    intro X Y f hf
    cases X
    cases Y
    let g : End (star R[S⁻¹]) := numeratorHom.toFunctor.map f
    have hunit :
        IsUnit g := by
      simpa using numerator_isUnit ⟨f, hf⟩
    exact (CategoryTheory.isUnit_iff_isIso g).1 hunit
  lift F hF := by
    let φ := endHom F
    let φS := oreUnitHom S F hF
    let hφ : ∀ s : S, φ s = (φS s : End (F.obj (star R))) := fun s ↦ by
      simp [φ, φS]
    exact functor (universalMulHom φ φS hφ)
  fac F hF := by
    let φ := endHom F
    let φS := oreUnitHom S F hF
    let hφ : ∀ s : S, φ s = (φS s : End (F.obj (star R))) := fun s ↦ by
      simp [φ, φS]
    change numeratorHom.toFunctor ⋙ functor (universalMulHom φ φS hφ) = F
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro X Y f
    cases X
    cases Y
    change universalMulHom φ φS hφ (numeratorHom f) = eqToHom rfl ≫ F.map f ≫ eqToHom rfl.symm
    simpa [φ] using
      (universalMulHom_commutes φ φS hφ :
        universalMulHom φ φS hφ (numeratorHom f) = φ f)
  uniq F₁ F₂ hFF := by
    let φ₁ := endHom F₁
    let φS := numeratorUnitHom S F₁
    let hφ : ∀ s : S,
        (endHom (numeratorHom.toFunctor ⋙ F₁)) s =
          (φS s : End (F₁.obj (star R[S⁻¹]))) := fun s ↦ by
      simpa [φS] using (endHom_comp_numerator S F₁ s)
    have hX : F₁.obj (star R[S⁻¹]) = F₂.obj (star R[S⁻¹]) :=
      Functor.congr_obj hFF (star R)
    let ψ₂ : R[S⁻¹] →* End (F₁.obj (star R[S⁻¹])) :=
      { toFun := fun x ↦ eqToHom hX ≫ F₂.map x ≫ eqToHom hX.symm
        map_one' := by
          change eqToHom hX ≫ F₂.map (𝟙 (star R[S⁻¹])) ≫ eqToHom hX.symm = 𝟙 _
          simp
        map_mul' := by
          intro x y
          let fx : star R[S⁻¹] ⟶ star R[S⁻¹] := x
          let fy : star R[S⁻¹] ⟶ star R[S⁻¹] := y
          let a : End (F₁.obj (star R[S⁻¹])) := eqToHom hX ≫ F₂.map x ≫ eqToHom hX.symm
          let b : End (F₁.obj (star R[S⁻¹])) := eqToHom hX ≫ F₂.map y ≫ eqToHom hX.symm
          change eqToHom hX ≫ F₂.map (x * y) ≫ eqToHom hX.symm = a * b
          rw [show x * y = fy ≫ fx by simp [fx, fy, comp_as_mul], F₂.map_comp]
          simp [a, b, CategoryTheory.End.mul_def, Category.assoc, fx, fy] }
    have hφ₁ :
        φ₁ = universalMulHom (endHom (numeratorHom.toFunctor ⋙ F₁)) φS hφ :=
      universalMulHom_unique (endHom (numeratorHom.toFunctor ⋙ F₁)) φS hφ φ₁
        (fun r ↦ rfl)
    have hnum :
        ∀ r : R, ψ₂ (numeratorHom r) = (endHom (numeratorHom.toFunctor ⋙ F₁)) r := by
      intro r
      simpa [ψ₂, endHom] using
        (Functor.congr_hom hFF r).symm
    have hψ₂ :
        ψ₂ = universalMulHom (endHom (numeratorHom.toFunctor ⋙ F₁)) φS hφ :=
      universalMulHom_unique (endHom (numeratorHom.toFunctor ⋙ F₁)) φS hφ ψ₂ hnum
    have hmapHom : φ₁ = ψ₂ := hφ₁.trans hψ₂.symm
    refine CategoryTheory.Functor.ext (fun _ ↦ hX) ?_
    intro X Y x
    cases X
    cases Y
    have hx := congrArg (fun h : R[S⁻¹] →* End (F₁.obj (star R[S⁻¹])) ↦ h x) hmapHom
    simpa [φ₁, ψ₂, endHom] using hx

section OreSet

variable [OreSet S]

/-- Remark 4.27.3, second clause: for a left denominator set `S`, the canonical functor from the
one-object category of `R` to the one-object category of the Ore localization `R[S⁻¹]` is a
localization of `SingleObj R` at the morphisms coming from `S`. -/
instance oreLocalizationFunctor_isLocalization :
    (numeratorHom.toFunctor : SingleObj R ⥤ SingleObj R[S⁻¹]).IsLocalization
      (submonoidProperty S) := by
  exact Functor.IsLocalization.mk' _ _
    (oreLocalizationStrictUniversalPropertyFixedTarget S (SingleObj R[S⁻¹]))
    (oreLocalizationStrictUniversalPropertyFixedTarget S
      (MorphismProperty.Localization (submonoidProperty S)))

/- Remark 4.27.3, second clause: once the canonical functor
`numeratorHom.toFunctor` is recognized as a localization at the morphisms coming from `S`, the
resulting equivalence with the constructed localization is exactly the canonical
`Localization.equivalenceFromModel`. -/
#check
  (Localization.equivalenceFromModel
      (numeratorHom.toFunctor : SingleObj R ⥤ SingleObj R[S⁻¹]) (submonoidProperty S) :
    MorphismProperty.Localization (submonoidProperty S) ≌ SingleObj R[S⁻¹])

end OreSet

end Monoid

end CategoryTheory.SingleObj
