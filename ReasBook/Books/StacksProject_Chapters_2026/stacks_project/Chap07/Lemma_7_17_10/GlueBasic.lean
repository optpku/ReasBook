module

public import stacks_project.Chap07.Lemma_7_17_10.Overlaps

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

/-- Helper for Lemma 7.17.10: a pointwise overlap solver packages directly into compatibility of
the synchronized stage family on the original cover. -/
lemma stage_family_compatible_of_first_level_pullback_equalities
    {U : C} {R : Presieve U}
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hoverlap :
      ∀ {r j : R.uncurry} {W : C}
        (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1),
        gr' ≫ r.1.2 = hj' ≫ j.1.2 →
          ((F.obj d).1.map gr'.op) (v' r) =
            ((F.obj d).1.map hj'.op) (v' j)) :
    Presieve.Arrows.Compatible ((F.obj d).1) (fun i : R.uncurry ↦ i.1.2) v' := by
  -- Compatibility is exactly the same overlap statement written in `Presieve.Arrows` form.
  intro r j W gr' hj' hW
  exact hoverlap gr' hj' hW

/-- Helper for Lemma 7.17.10: if a section on the sigma refinement glues the branchwise
restrictions of the stage family `v'`, then its restriction along each base branch already
recovers the original family `v'`. -/
lemma sigma_refinement_stage_glue_restricts_to_base_family
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (td : (F.obj d).1.obj (op U))
    (htd :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj d).1.map (q.2.1.2 ≫ q.1.1.2).op) td =
          ((F.obj d).1.map q.2.1.2.op) (v' q.1)) :
    ∀ i : R.uncurry, ((F.obj d).1.map i.1.2.op) td = v' i := by
  intro i
  have hTi : Presieve.IsSheafFor ((F.obj d).1) (T i) := by
    -- The stage sheaf is already a sheaf for each chosen pullback cover in the coverage `K`.
    exact
      ((Presieve.isSheaf_coverage (K := K.toCoverage) ((F.obj d).1)).1
        ((isSheaf_iff_isSheaf_of_type J ((F.obj d).1)).1 (F.obj d).2)) (T i) (hT i)
  apply hTi.isSeparatedFor.ext
  intro Y g hg
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨i, ⟨⟨Y, g⟩, hg⟩⟩
  -- Evaluate the sigma-gluing identity on the branch indexed by `q`.
  simpa [q, FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using htd q


end

end CategoryTheory
