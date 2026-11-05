module

public import stacks_project.Chap07.Lemma_7_17_10.GlueSigma

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

/-- Helper for Lemma 7.17.10: every stage sheaf is a sheaf for the sigma refinement because that
refinement generates a covering sieve in `J = J`. -/
lemma stage_sheaf_isSheafFor_sigma_refinement
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    {e : Set.Iio β} :
    Presieve.IsSheafFor
      ((F.obj e).1)
      (Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        T) := by
  -- Pass from the stage sheaf property on `J` to the explicit sigma refinement via the sieve it
  -- generates.
  exact
    (((isSheaf_iff_isSheaf_of_type J ((F.obj e).1)).1 (F.obj e).2).isSheafFor
      (Presieve.bindOfArrows
        (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2)
        T)
      (sigma_refinement_generate_mem_toGrothendieck
        (F := F)
        (β := β)
        (hcover := hcover)
        (hR := hR)
        T
        hT))


end

end CategoryTheory
