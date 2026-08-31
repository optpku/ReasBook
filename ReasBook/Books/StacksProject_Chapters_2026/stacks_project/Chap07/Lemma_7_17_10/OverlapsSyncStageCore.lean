module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsSyncLocalPullback

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

/-- Helper for Lemma 7.17.10: an overlap equality in the presheaf colimit has a later-stage
witness in the ordinal diagram. -/
lemma presheafColimit_overlap_eq_at_later_stage
    {U : C} {R : Presieve U}
    (x : ∀ i : R.uncurry,
      (colimit (F ⋙ sheafToPresheaf J (Type (max u v)))).obj (op i.1.1))
    (hx :
      Presieve.Arrows.Compatible
        (colimit (F ⋙ sheafToPresheaf J (Type (max u v))))
        (fun i : R.uncurry ↦ i.1.2) x)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hv_image :
      ∀ i,
        presheafColimit_stageClass (β := β) (F := F) (a := d) (U := i.1.1) (v' i) =
          x i)
    {i j : R.uncurry} {Z : C}
    (gi : Z ⟶ i.1.1) (gj : Z ⟶ j.1.1)
    (hcomm : gi ≫ i.1.2 = gj ≫ j.1.2) :
    ∃ e : Set.Iio β, ∃ f : d ⟶ e,
      ((F.map f).1.app (op Z)) (((F.obj d).1.map gi.op) (v' i)) =
        ((F.map f).1.app (op Z)) (((F.obj d).1.map gj.op) (v' j)) := by
  have hcolim :
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op Z))
          (((F.obj d).1.map gi.op) (v' i)) =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op Z))
          (((F.obj d).1.map gj.op) (v' j)) := by
    exact
      presheafColimit_overlap_eq_in_colimit
        (β := β)
        (F := F)
        (hcover := hcover)
        (x := x)
        (hx := hx)
        (v := v')
        (hv_image := hv_image)
        (gi := gi)
        (gj := gj)
        hcomm
  exact
    presheafColimit_section_eq_at_later_stage
      (β := β)
      (F := F)
      (U := Z)
      (i := d)
      (s := ((F.obj d).1.map gi.op) (v' i))
      (t := ((F.obj d).1.map gj.op) (v' j))
      (h := hcolim)

omit hcover in
/-- Helper for Lemma 7.17.10: an equality after a local transition remains equal after passing
through any common later stage. -/
lemma stage_family_transport_eq_through_common_stage
    {d b e : Set.Iio β} (f : d ⟶ b) (hbe : b.1 ≤ e.1) (hde : d.1 ≤ e.1)
    {X : C} {x y : (F.obj d).1.obj (op X)}
    (h :
      ((F.map f).1.app (op X)) x =
        ((F.map f).1.app (op X)) y) :
    ((F.map (homOfLE hde)).1.app (op X)) x =
      ((F.map (homOfLE hde)).1.app (op X)) y := by
  have hcomp : f ≫ homOfLE hbe = homOfLE hde := by
    exact Subsingleton.elim _ _
  have hrewrite : F.map (homOfLE hde) = F.map (f ≫ homOfLE hbe) := by
    exact congrArg F.map hcomp.symm
  rw [hrewrite]
  simpa [Functor.map_comp, Function.comp] using
    congrArg (((F.map (homOfLE hbe)).1.app (op X))) h

omit hcover in
/-- Helper for Lemma 7.17.10: an equality of two restrictions at one stage remains equal after
precomposing both branches by the same morphism. -/
lemma stage_family_precompose_restriction_eq
    {e : Set.Iio β} {X Y A B : C} (k : X ⟶ Y)
    {f : Y ⟶ A} {g : Y ⟶ B}
    {s : (F.obj e).1.obj (op A)} {t : (F.obj e).1.obj (op B)}
    (h :
      ((F.obj e).1.map f.op) s =
        ((F.obj e).1.map g.op) t) :
    ((F.obj e).1.map (k ≫ f).op) s =
      ((F.obj e).1.map (k ≫ g).op) t := by
  have h' := congrArg (((F.obj e).1.map k.op)) h
  simpa [FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using h'

end

end CategoryTheory
