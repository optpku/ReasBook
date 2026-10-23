module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u w'

namespace CategoryTheory

namespace GrothendieckTopology

open CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Layering for Definition 7.38.1:
- primary domain: conservative families of points of a site and the site-level enough-points
  condition;
- sampled owner declarations:
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `GrothendieckTopology.HasEnoughPoints`,
  `HasEnoughPoints.exists_objectProperty`,
  `ObjectProperty.ofObj_iff`;
- core/canonical owners: `P.IsConservativeFamilyOfPoints` for an object property `P` on `J.Point`
  and the site-level class `J.HasEnoughPoints`;
- source-facing bridge/view: the two theorems below translate between the textbook indexed-family
  formulation and those owner declarations.
- primitive data: for the first bridge theorem, an arbitrary indexed family `p : ι → J.Point`; for
  the enough-points owner, a `w`-small object property `P : ObjectProperty J.Point`;
- derived API: the indexed-family conservativity criterion and the small-family enough-points
  existence bridge.
-/

/- Definition 7.38.1 packages a family of points as an object property on `J.Point`; the
canonical notion of a conservative family is `ObjectProperty.IsConservativeFamilyOfPoints`. -/
recall ObjectProperty.IsConservativeFamilyOfPoints

/- Definition 7.38.1: a site has enough points if it admits a small conservative family of points;
this is the canonical mathlib class `GrothendieckTopology.HasEnoughPoints`. -/
recall HasEnoughPoints

/-- An indexed family of points is conservative exactly when the associated object property on
`J.Point` is a conservative family of points in the canonical sense. -/
theorem isConservativePointFamily_iff {ι : Type w'} (p : ι → Point.{w} J) :
    (ofObj p).IsConservativeFamilyOfPoints ↔
      ∀ ⦃ℱ 𝒢 : Sheaf J (Type w)⦄ (φ : ℱ ⟶ 𝒢),
        (∀ i : ι, IsIso ((p i).sheafFiber.map φ)) → IsIso φ := by
  constructor
  · intro hP ℱ 𝒢 φ hφ
    refine (hP.jointlyReflectIsomorphisms_type.isIso_iff φ).2 ?_
    intro Φ
    rcases (ofObj_iff p Φ.obj).1 Φ.property with ⟨i, hi⟩
    rw [← hi]
    exact hφ i
  · intro hP
    refine ⟨⟨fun φ hφ ↦ hP φ fun i ↦ ?_⟩⟩
    simpa using hφ ⟨p i, ofObj_apply p i⟩

/-- Definition 7.38.1: the site `(C, J)` has enough points exactly when it admits a `w`-small
indexed conservative family of points. -/
theorem hasEnoughPoints_iff_exists_conservativePointFamily :
    HasEnoughPoints.{w} J ↔
      ∃ (ι : Type w) (p : ι → Point.{w} J), (ofObj p).IsConservativeFamilyOfPoints := by
  constructor
  · intro hJ
    obtain ⟨P, hsmall, hP⟩ := hJ.exists_objectProperty
    letI : Small.{w} (Subtype P) := hsmall
    let ι : Type w := Shrink.{w} (Subtype P)
    let e : Subtype P ≃ ι := equivShrink (Subtype P)
    let p : ι → Point.{w} J := fun i ↦ (e.symm i).1
    refine ⟨ι, p, ?_⟩
    have hofObj : ofObj p = P := by
      ext Φ
      rw [ofObj_iff]
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).2
      · intro hΦ
        refine ⟨e ⟨Φ, hΦ⟩, ?_⟩
        simp [p]
    simpa [hofObj] using hP
  · rintro ⟨ι, p, hP⟩
    exact ⟨⟨ofObj p, inferInstance, hP⟩⟩

end GrothendieckTopology

end CategoryTheory
