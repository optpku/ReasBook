module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

/- Domain-style sampling for Lemma 4.33.4:
- primary domain: strongly cartesian morphisms for a functor together with pullback squares in the
  base category;
- sampled owner API:
  `Functor.IsStronglyCartesian`,
  `IsStronglyCartesian.map`,
  `Functor.IsHomLift`,
  `IsHomLift.fac'`,
  `CategoryTheory.IsPullback`;
- source-facing layer: the Stacks lemma asserting that a strongly cartesian lift of the second base
  pullback projection produces a pullback square in the total category;
- core/canonical owners: `Functor.IsStronglyCartesian` for the induced comparison morphism and
  `IsPullback` for the resulting square;
- bridge/view: the left leg upstairs is derived by `IsStronglyCartesian.map`, and the needed base
  comparison is read off from the owner-level `IsHomLift` API.

Primitive-vs-derived split:
- primitive data: the morphisms `φ`, `ψ`, `a`, the base pullback, and the two
  `IsStronglyCartesian` instances;
- derived API: the owner-level comparison morphism from `IsStronglyCartesian.map`, the base
  compatibility lemma identifying it with the pullback cospan, and the resulting `IsPullback`
  statement. -/

open IsStronglyCartesian IsHomLift

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]

section

variable (p : E ⥤ C) {x y z w : E} (φ : x ⟶ y) (ψ : z ⟶ y)

-- Proof sketch: for a cone `t` over `φ` and `ψ`, the base pullback square provides a comparison
-- map `p.obj t.pt ⟶ R`; strong cartesianness of `a` lifts `t.snd` through that comparison, and
-- strong cartesianness of `φ` identifies the composite with `t.fst`.
/-- Lemma 4.33.4: if the square formed by `p.map χ`, `p.map a`, `p.map φ`, and `p.map ψ` is a
pullback square in the base category, `φ` is strongly cartesian over its base map, and `a` is
strongly cartesian over the other base leg, then the square `χ, a, φ, ψ` is a pullback square in
the total category. -/
theorem isPullback_of_isPullback_of_isStronglyCartesian
    {R : C} {f : R ⟶ p.obj x} {g : R ⟶ p.obj z} {χ : w ⟶ x} (hbase : IsPullback f g (p.map φ) (p.map ψ))
    (a : w ⟶ z) [p.IsHomLift f χ] [p.IsStronglyCartesian (p.map φ) φ]
    [p.IsStronglyCartesian g a] (hχ : χ ≫ φ = a ≫ ψ) :
    IsPullback χ a φ ψ := by
  have hw : p.obj w = R := IsHomLift.domain_eq p g a
  let baseMap (t : PullbackCone φ ψ) : p.obj t.pt ⟶ R :=
    hbase.lift (p.map t.fst) (p.map t.snd) (by
      simpa using congrArg (Functor.map p) t.condition)
  have baseMap_fst (t : PullbackCone φ ψ) : baseMap t ≫ f = p.map t.fst := by
    simp [baseMap]
  have baseMap_snd (t : PullbackCone φ ψ) : p.map t.snd = baseMap t ≫ g := by
    simpa [baseMap] using
      (hbase.lift_snd (p.map t.fst) (p.map t.snd) (congrArg (Functor.map p) t.condition)).symm
  let lift (t : PullbackCone φ ψ) : t.pt ⟶ w :=
    IsStronglyCartesian.map p g a (baseMap_snd t) t.snd
  refine IsPullback.of_isLimit' ⟨hχ⟩ ?_
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro t
    have hlift : lift t ≫ a = t.snd := by
      dsimp [lift]
      exact IsStronglyCartesian.fac p g a (baseMap_snd t) t.snd
    letI : p.IsHomLift (baseMap t ≫ f) (lift t ≫ χ) := inferInstance
    letI : p.IsHomLift (p.map t.fst) (lift t ≫ χ) := by
      exact (baseMap_fst t) ▸ inferInstance
    apply IsStronglyCartesian.ext p (p.map φ) φ (p.map t.fst)
    calc
      (lift t ≫ χ) ≫ φ = lift t ≫ (χ ≫ φ) := by simp [Category.assoc]
      _ = lift t ≫ (a ≫ ψ) := by rw [hχ]
      _ = (lift t ≫ a) ≫ ψ := by simp [Category.assoc]
      _ = t.snd ≫ ψ := by rw [hlift]
      _ = t.fst ≫ φ := by simpa using t.condition.symm
  · intro t
    dsimp [lift]
    exact IsStronglyCartesian.fac p g a (baseMap_snd t) t.snd
  · intro t m hmfst hmsnd
    have hχbase : p.map χ = eqToHom hw ≫ f := by
      simpa [hw] using IsHomLift.fac' p f χ
    have habase : p.map a = eqToHom hw ≫ g := by
      simpa [hw] using IsHomLift.fac' p g a
    have hmfst' : (p.map m ≫ eqToHom hw) ≫ f = p.map t.fst := by
      calc
        (p.map m ≫ eqToHom hw) ≫ f = p.map m ≫ p.map χ := by simp [Category.assoc, hχbase]
        _ = p.map t.fst := by
          simpa [Functor.map_comp] using congrArg (Functor.map p) hmfst
    have hmsnd' : (p.map m ≫ eqToHom hw) ≫ g = p.map t.snd := by
      calc
        (p.map m ≫ eqToHom hw) ≫ g = p.map m ≫ p.map a := by simp [Category.assoc, habase]
        _ = p.map t.snd := by
          simpa [Functor.map_comp] using congrArg (Functor.map p) hmsnd
    have hm : p.map m ≫ eqToHom hw = baseMap t := by
      apply hbase.hom_ext
      · exact hmfst'.trans (baseMap_fst t).symm
      · exact hmsnd'.trans (baseMap_snd t)
    have hm' : p.map m = baseMap t ≫ eqToHom hw.symm := by
      calc
        p.map m = (p.map m ≫ eqToHom hw) ≫ eqToHom hw.symm := by simp [Category.assoc]
        _ = baseMap t ≫ eqToHom hw.symm := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eqToHom hw.symm) hm
    letI : p.IsHomLift (baseMap t) m := by
      refine IsHomLift.of_fac' p (baseMap t) m rfl hw ?_
      simpa using hm'
    dsimp [lift]
    exact IsStronglyCartesian.map_uniq p g a (baseMap_snd t) t.snd m hmsnd

/- Companion bridge: specialize Lemma 4.33.4 to the canonical chosen pullback of `p.map φ` and
`p.map ψ` in the base category. -/
theorem strongly_cartesian_pullback_isPullback
    {a : w ⟶ z} [HasPullback (p.map φ) (p.map ψ)] [p.IsStronglyCartesian (p.map φ) φ]
    [p.IsStronglyCartesian (pullback.snd (p.map φ) (p.map ψ)) a] :
    IsPullback
      (IsStronglyCartesian.map p (p.map φ) φ
        (IsPullback.of_hasPullback (p.map φ) (p.map ψ)).w.symm
        (a ≫ ψ))
      a φ ψ := by
  let hbase : IsPullback
      (pullback.fst (p.map φ) (p.map ψ))
      (pullback.snd (p.map φ) (p.map ψ))
      (p.map φ)
      (p.map ψ) :=
    IsPullback.of_hasPullback (p.map φ) (p.map ψ)
  exact isPullback_of_isPullback_of_isStronglyCartesian p φ ψ hbase a
    (IsStronglyCartesian.fac p (p.map φ) φ hbase.w.symm (a ≫ ψ))

end

end CategoryTheory.Functor
