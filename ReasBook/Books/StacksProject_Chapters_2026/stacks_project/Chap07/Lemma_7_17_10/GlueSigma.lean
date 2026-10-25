module

public import stacks_project.Chap07.Lemma_7_17_10.GlueBasic

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

/-- Helper for Lemma 7.17.10: sigma-refinement compatibility is obtained by applying the previous
base-cover overlap descent to each overlap pair in the sigma refinement. -/
lemma stage_family_sigma_refinement_compatible_of_base_cover_owner_equalities
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (hfirst_e :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj e).1.map q.2.1.2.op) (w q.1) =
          ((F.obj e).1.map (gr q).op) (w (right q)))
    (htarget_e :
      ∀ p : targeted_secondary_owner_index (T := T) B,
        ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
          let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
          let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
          ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj))) :
    Presieve.Arrows.Compatible
      ((F.obj e).1)
      (fun q : Σ i : R.uncurry, (T i).uncurry ↦ q.2.1.2 ≫ q.1.1.2)
      (fun q ↦ ((F.obj e).1.map q.2.1.2.op) (w q.1)) := by
  intro q₁ q₂ Z a b h
  -- Route correction: the sigma overlap is reduced directly to the base-cover overlap lemma,
  -- so the fixed target branch is introduced only inside the concrete local refinement.
  simpa [FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using
    stage_family_overlap_of_base_cover_owner_equalities_at_global_stage
      (β := β)
      (F := F)
      (K := K)
      (hcover := hcover)
      (T := T)
      (hT := hT)
      (right := right)
      (gr := gr)
      (htarget_e := htarget_e)
      (w := w)
      (hfirst_e := hfirst_e)
      (B := B)
      (hB := hB)
      (r := q₁.1)
      (j := q₂.1)
      (gr' := a ≫ q₁.2.1.2)
      (hj' := b ≫ q₂.2.1.2)
      (by simpa [Category.assoc] using h)


end

end CategoryTheory
