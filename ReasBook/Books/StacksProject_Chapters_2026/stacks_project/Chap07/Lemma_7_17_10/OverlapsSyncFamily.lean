module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsSyncTarget

@[expose] public section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open CategoryTheory Limits Opposite
open CategoryTheory.GrothendieckTopology

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {K : Precoverage C}
variable [K.HasPullbacks] [K.IsStableUnderBaseChange]
variable [HasWeakSheafify K.toCoverage.toGrothendieck (Type (max u v))]

local notation "J" => K.toCoverage.toGrothendieck

section

variable (β : Ordinal.{max u v}) (F : Set.Iio β ⥤ Sheaf K.toCoverage.toGrothendieck (Type (max u v)))
variable (hcover : ∀ (U : C) (R : Presieve U),
  R ∈ K U → Cardinal.lift (Cardinal.mk R.uncurry) < β.cof)

include F

include hcover

/-- Helper for Lemma 7.17.10: a family of overlap comparisons with the same base colimit
family gives a later-stage witness for each member of the family. This isolates the expensive
colimit-overlap call from the canonical fixed-target synchronization helper. -/
lemma presheafColimit_overlap_family_stage_witness
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left right : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ a : ι, Z a ⟶ (left a).1.1)
    (gt : ∀ a : ι, Z a ⟶ (right a).1.1)
    (hover :
      ∀ a : ι, gl a ≫ (left a).1.2 = gt a ≫ (right a).1.2)
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (hw_image :
      ∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := e) (U := i.1.1) (w i) =
          x i) :
    ∀ a : ι,
      ∃ d : Set.Iio β, ∃ f : e ⟶ d,
        ((F.map f).1.app (op (Z a)))
            (((F.obj e).1.map (gl a).op) (w (left a))) =
          ((F.map f).1.app (op (Z a)))
            (((F.obj e).1.map (gt a).op) (w (right a))) := by
  intro a
  exact
    presheafColimit_overlap_eq_at_later_stage
      (β := β)
      (F := F)
      (hcover := hcover)
      (x := x)
      (hx := hx)
      (v' := w)
      (hv_image := hw_image)
      (i := left a)
      (j := right a)
      (Z := Z a)
      (gi := gl a)
      (gj := gt a)
      (hover a)

omit hcover in

end

end CategoryTheory
