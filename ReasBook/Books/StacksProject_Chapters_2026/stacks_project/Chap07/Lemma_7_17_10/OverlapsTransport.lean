module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsBasic

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
/-- Helper for Lemma 7.17.10: equality of two restrictions at one stage transports unchanged
to any later ordinal stage. -/
lemma stage_family_two_restriction_eq_at_later_stage
    {d e : Set.Iio β} (hde : d.1 ≤ e.1)
    {X A B : C}
    (leftMap : X ⟶ A) (rightMap : X ⟶ B)
    (xA : (F.obj d).1.obj (op A)) (xB : (F.obj d).1.obj (op B))
    (h :
      ((F.obj d).1.map leftMap.op) xA =
        ((F.obj d).1.map rightMap.op) xB) :
    ((F.obj e).1.map leftMap.op)
        (((F.map (homOfLE hde)).1.app (op A)) xA) =
      ((F.obj e).1.map rightMap.op)
        (((F.map (homOfLE hde)).1.app (op B)) xB) := by
  have hleft :
      ((F.obj e).1.map leftMap.op)
          (((F.map (homOfLE hde)).1.app (op A)) xA) =
        ((F.map (homOfLE hde)).1.app (op X))
          (((F.obj d).1.map leftMap.op) xA) := by
    exact
      (sheaf_transition_app_map_eq_map_app
        (β := β)
        (F := F)
        (f := homOfLE hde)
        (g := leftMap)
        (a := xA)).symm
  have hmid :
      ((F.map (homOfLE hde)).1.app (op X))
          (((F.obj d).1.map leftMap.op) xA) =
        ((F.map (homOfLE hde)).1.app (op X))
          (((F.obj d).1.map rightMap.op) xB) :=
    congrArg (((F.map (homOfLE hde)).1.app (op X))) h
  have hright :
      ((F.map (homOfLE hde)).1.app (op X))
          (((F.obj d).1.map rightMap.op) xB) =
        ((F.obj e).1.map rightMap.op)
          (((F.map (homOfLE hde)).1.app (op B)) xB) := by
    exact
      sheaf_transition_app_map_eq_map_app
        (β := β)
        (F := F)
        (f := homOfLE hde)
        (g := rightMap)
        (a := xB)
  exact hleft.trans (hmid.trans hright)

end

end CategoryTheory
