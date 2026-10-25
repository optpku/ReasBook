module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Over
open CategoryTheory.IsHomLift
open CategoryTheory.Functor.IsStronglyCartesian

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/- Domain-style sampling for Lemma 4.33.11:
- primary domain: fibred categories over a slice category and transport of cartesian structure
  across the slice forgetful functor.
- inspected owner-level declarations:
  `Functor.IsHomLift.of_fac`,
  `Functor.IsStronglyCartesian.universal_property`,
  `Functor.IsPreFibered.exists_isCartesian`,
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian`.
- best owner abstraction: `Functor.IsFibered` on the slice-valued functor `p' : S ⥤ Over U`;
  the slice forgetful comparison is a bridge, not a second owner.
- primitive data: the underlying morphism `f.left` in `C` and the owner-level lift/cartesian
  predicates for `p' ⋙ Over.forget U`.
- derived API: the induced slice-level `IsHomLift`, `IsStronglyCartesian`, and `IsFibered`
  structures on `p'`, including the typeclass instances below for `p'.IsStronglyCartesian` and
  `p'.IsFibered`.

Source/core/bridge triage:
- `source-facing`: `isStronglyCartesian_of_comp_over_forget` and
  `isFibered_of_comp_over_forget`.
- `core/canonical`: `Functor.IsHomLift`, `Functor.IsStronglyCartesian`, and
  `Functor.IsFibered`.
- `bridge/view`: the public equivalence
  `isHomLift_over_iff_comp_over_forget` between slice lifts and underlying lifts in `C`.
-/

/-- Bridge lemma for Lemma 4.33.11: a morphism in `Over U` is a lift for `p'` exactly when its
underlying morphism in `C` is a lift for `p' ⋙ Over.forget U`. -/
theorem isHomLift_over_iff_comp_over_forget {U : C} (p' : S ⥤ Over U)
    {a b : S} {A : Over U} {f : A ⟶ p'.obj a} {φ : b ⟶ a}
    : p'.IsHomLift f φ ↔ (p' ⋙ Over.forget U).IsHomLift f.left φ := by
  let q := p' ⋙ Over.forget U
  constructor
  · intro
    refine IsHomLift.of_fac q f.left φ ?_ rfl ?_
    · simpa [q] using congrArg (fun X ↦ X.left) (domain_eq p' f φ)
    · simpa [q] using congrArg (fun m ↦ m.left) (fac p' f φ)
  · intro
    have hdom : (p'.obj b).left = A.left := domain_eq q f.left φ
    have hA : p'.obj b = A := by
      exact CostructuredArrow.obj_ext (p'.obj b) A hdom <| by
        simpa [q, Category.assoc, ← w f] using
          (congrArg (fun k ↦ k ≫ (p'.obj a).hom) ((fac' q f.left φ).symm)).trans
            (w (p'.map φ))
    subst A
    refine IsHomLift.of_fac' p' f φ rfl rfl ?_
    apply OverMorphism.ext
    simpa [q] using (fac' q f.left φ)

/-- If a morphism over `Over U` is strongly cartesian after composing with the slice forgetful
functor, then it is already strongly cartesian in the slice. -/
theorem isStronglyCartesian_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    {a b : S} {A : Over U} {f : A ⟶ p'.obj a} {φ : b ⟶ a}
    [(p' ⋙ Over.forget U).IsStronglyCartesian f.left φ] :
    p'.IsStronglyCartesian f φ := by
  let q := p' ⋙ Over.forget U
  haveI : p'.IsHomLift f φ := (isHomLift_over_iff_comp_over_forget p').2 inferInstance
  have hA : A = p'.obj b := (domain_eq p' f φ).symm
  subst A
  refine { universal_property' := ?_ }
  intro c g φ' hφ'
  haveI : q.IsHomLift (g ≫ f).left φ' :=
    (isHomLift_over_iff_comp_over_forget p').1 inferInstance
  obtain ⟨χ, hχ, hχuniq⟩ :=
    universal_property q f.left φ g.left ((g ≫ f).left) (by simp) φ'
  refine ⟨χ, ⟨?_, hχ.2⟩, ?_⟩
  · haveI : q.IsHomLift g.left χ := hχ.1
    exact (isHomLift_over_iff_comp_over_forget p').2 inferInstance
  · intro ψ hψ
    haveI : p'.IsHomLift g ψ := hψ.1
    apply hχuniq ψ
    haveI : q.IsHomLift g.left ψ :=
      (isHomLift_over_iff_comp_over_forget p').1 inferInstance
    exact ⟨inferInstance, hψ.2⟩

instance {U : C} (p' : S ⥤ Over U)
    {a b : S} {A : Over U} {f : A ⟶ p'.obj a} {φ : b ⟶ a}
    [(p' ⋙ Over.forget U).IsStronglyCartesian f.left φ] :
    p'.IsStronglyCartesian f φ :=
  isStronglyCartesian_of_comp_over_forget p'

-- Proof sketch: choose a cartesian lift of the underlying arrow `f.left` for
-- `p' ⋙ Over.forget U` using the owner API `Functor.IsPreFibered.exists_isCartesian`, upgrade it
-- to a strongly cartesian lift via
-- `Functor.IsFibered.isStronglyCartesian_of_isCartesian`, and transport that structure to `Over U`
-- with `isStronglyCartesian_of_comp_over_forget`.
/-- Lemma 4.33.11: if a functor `p' : S ⥤ Over U` becomes fibred after composing with the slice
forgetful functor `Over.forget U : Over U ⥤ C`, then `p'` is itself fibred over `Over U`.
Equivalently, if a fibred category over `C` factors through the slice category `C/U`, then the
induced functor to `C/U` is fibred. -/
theorem isFibered_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    [(p' ⋙ Over.forget U).IsFibered] :
    p'.IsFibered := by
  let q := p' ⋙ Over.forget U
  haveI : q.IsFibered := by
    dsimp [q]
    infer_instance
  exact IsFibered.of_exists_isStronglyCartesian fun a A f ↦ by
    obtain ⟨b, φ, hφ⟩ :=
      IsPreFibered.exists_isCartesian q rfl f.left
    letI : q.IsCartesian f.left φ := hφ
    letI : q.IsStronglyCartesian f.left φ :=
      IsFibered.isStronglyCartesian_of_isCartesian q f.left φ
    haveI : (p' ⋙ Over.forget U).IsStronglyCartesian f.left φ := by
      simpa [q] using (show q.IsStronglyCartesian f.left φ from inferInstance)
    exact ⟨b, φ, inferInstance⟩

instance {U : C} (p' : S ⥤ Over U) [(p' ⋙ Over.forget U).IsFibered] :
    p'.IsFibered :=
  isFibered_of_comp_over_forget p'

end CategoryTheory.Functor
