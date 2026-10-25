module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsSync

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

omit hcover in
/-- Helper for Lemma 7.17.10: once a canonical base-cover branch has been identified with the
`right`-branch of an actual `T j`-element, the synchronized base-cover equality and the first-level
equality at that `T j`-element combine to recover the desired fixed-target equality.

This helper is kept as a small formal target only; the previous generated proof had an invalid
projection in the displayed target and should not drive replanning. -/
lemma stage_family_fixed_target_eq_of_base_cover_eq_and_first_level
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (hfirst_e :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj e).1.map q.2.1.2.op) (w q.1) =
          ((F.obj e).1.map (gr q).op) (w (right q)))
    {q qj : Σ i : R.uncurry, (T i).uncurry}
    {X : C}
    {a : X ⟶ (right q).1.1}
    {b : X ⟶ (right qj).1.1}
    {c : X ⟶ qj.2.1.1}
    {d : X ⟶ (qj.1).1.1}
    (hbase :
      ((F.obj e).1.map a.op) (w (right q)) =
        ((F.obj e).1.map b.op) (w (right qj)))
    (hb : b = c ≫ gr qj)
    (hc : d = c ≫ qj.2.1.2) :
    ((F.obj e).1.map a.op) (w (right q)) =
      ((F.obj e).1.map d.op) (w qj.1) := by
  -- Push the first-level equality for `qj` along `c`, so the right-hand branch is rewritten from
  -- `right qj` to the actual source branch `qj.1`.
  have hrewrite :
      ((F.obj e).1.map d.op) (w qj.1) =
        ((F.obj e).1.map b.op) (w (right qj)) := by
    have hqj := congrArg (((F.obj e).1.map c.op)) (hfirst_e qj)
    simpa [FunctorToTypes.map_comp_apply, Category.assoc, op_comp, hb, hc] using hqj
  exact hbase.trans hrewrite.symm


end

end CategoryTheory
