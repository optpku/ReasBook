module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsSyncStageCore

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

/-- Helper for Lemma 7.17.10: once the desired fixed-target equality is known after restricting to
every branch of a covering presieve `D`, sheaf separatedness at stage `e` descends it to the
original overlap witness. -/
lemma stage_family_target_overlap_eq_of_cover_branch_equalities
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (p : targeted_secondary_owner_index (T := T) B)
    (z : targeted_secondary_target_overlap_witness (T := T) (B := B) p)
    (D : Presieve z.1)
    (hD : D ∈ K z.1)
    (htarget_local :
      ∀ n : D.uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
        let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
        ((F.obj e).1.map (n.1.2 ≫ z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
          ((F.obj e).1.map (n.1.2 ≫ z.2.2.2.1 ≫ gr qj).op) (w (right qj))) :
    let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
    let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
    ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
      ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj)) := by
  let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
  let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
  have hDd : Presieve.IsSheafFor ((F.obj e).1) D := by
    -- The synchronized stage remains a sheaf on the auxiliary covering presieve used to descend
    -- the branchwise target comparison.
    exact
      ((Presieve.isSheaf_coverage (K := K.toCoverage) ((F.obj e).1)).1
        ((isSheaf_iff_isSheaf_of_type J ((F.obj e).1)).1 (F.obj e).2)) D hD
  apply hDd.isSeparatedFor.ext
  intro X k hk
  let n : D.uncurry := ⟨⟨X, k⟩, hk⟩
  -- Evaluate the branchwise hypothesis on the concrete branch `n` of `D`.
  simpa [q, qj, n, FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using htarget_local n

end

end CategoryTheory
