module

public import stacks_project.Chap07.Lemma_7_17_10.Core

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

/-- Helper for Lemma 7.17.10: once the secondary branch equalities have been synchronized to one
stage, sheaf separatedness on each secondary pullback cover descends them to the first-level
overlap equalities. -/
lemma presheafColimit_secondary_cover_eq_at_common_stage
    {U : C} {R : Presieve U}
    {ι : Type (max u v)}
    (left right : ι → R.uncurry)
    (Z : ι → C)
    (gl : ∀ q : ι, Z q ⟶ (left q).1.1)
    (gr : ∀ q : ι, Z q ⟶ (right q).1.1)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (B : ∀ q : ι, Presieve (Z q))
    (hB : ∀ q, B q ∈ K (Z q))
    (hbranch_d :
      ∀ p : Σ q : ι, (B q).uncurry,
        ((F.obj d).1.map (p.2.1.2 ≫ gl p.1).op) (v' (left p.1)) =
          ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1))) :
    ∀ q : ι,
      ((F.obj d).1.map (gl q).op) (v' (left q)) =
        ((F.obj d).1.map (gr q).op) (v' (right q)) := by
  intro q
  have hBd : Presieve.IsSheafFor ((F.obj d).1) (B q) := by
    -- Descend the synchronized branch equalities along the chosen secondary cover `B q`.
    exact
      ((Presieve.isSheaf_coverage (K := K.toCoverage) ((F.obj d).1)).1
        ((isSheaf_iff_isSheaf_of_type J ((F.obj d).1)).1 (F.obj d).2)) (B q) (hB q)
  apply hBd.isSeparatedFor.ext
  intro Y g hg
  let p : Σ q : ι, (B q).uncurry := ⟨q, ⟨⟨Y, g⟩, hg⟩⟩
  simpa [p, FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using hbranch_d p

/-- Helper for Lemma 7.17.10: normalizing the two chosen pullback factorizations identifies the
resulting overlap equality over the base object. -/
lemma pullback_branch_factorization_base_eq
    {U : C} {R : Presieve U}
    {r j k : R.uncurry}
    {W Y A : C}
    {gr' : W ⟶ r.1.1} {hj' : W ⟶ j.1.1}
    {g : Y ⟶ W} {i : Y ⟶ A} {e : A ⟶ r.1.1} {i' : A ⟶ k.1.1}
    (hie : g ≫ gr' = i ≫ e)
    (hi'e' : e ≫ r.1.2 = i' ≫ k.1.2)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2) :
    (i ≫ i') ≫ k.1.2 = (g ≫ hj') ≫ j.1.2 := by
  -- Reassociate the two branch factorizations until both sides are written over the same base
  -- composite to `U`.
  calc
    (i ≫ i') ≫ k.1.2 = i ≫ (e ≫ r.1.2) := by
      simpa [Category.assoc] using congrArg (fun t ↦ i ≫ t) hi'e'.symm
    _ = (i ≫ e) ≫ r.1.2 := by simp [Category.assoc]
    _ = (g ≫ gr') ≫ r.1.2 := by
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ r.1.2) hie.symm
    _ = g ≫ (hj' ≫ j.1.2) := by
      simpa [Category.assoc] using congrArg (fun t ↦ g ≫ t) hW
    _ = (g ≫ hj') ≫ j.1.2 := by simp [Category.assoc]

/-- Helper for Lemma 7.17.10: once the first-level pullback equalities have been synchronized at
one stage, the remaining gap is to descend them to genuine overlap compatibility on the original
cover. -/
lemma pullback_branch_restriction_eq_of_first_level_equality
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hfirst :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj d).1.map q.2.1.2.op) (v' q.1) =
          ((F.obj d).1.map (gr q).op) (v' (right q)))
    {r : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1)
    (he : T r e)
    (hie : g ≫ gr' = i ≫ e) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ((F.obj d).1.map g.op) (((F.obj d).1.map gr'.op) (v' r)) =
      ((F.obj d).1.map (i ≫ gr q).op) (v' (right q)) := by
  -- Rewrite the restricted branch through the synchronized first-level equality indexed by `e`.
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  have hq := hfirst q
  have hi := congrArg (((F.obj d).1.map i.op)) hq
  -- Normalizing both composites isolates the concrete branch map that will later be compared to
  -- the target overlap branch.
  have hleft :
      ((F.obj d).1.map g.op) (((F.obj d).1.map gr'.op) (v' r)) =
        ((F.obj d).1.map i.op) (((F.obj d).1.map e.op) (v' r)) := by
    simpa [FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using
      congrArg (fun f : Y ⟶ r.1.1 ↦ ((F.obj d).1.map f.op) (v' r)) hie
  calc
    ((F.obj d).1.map g.op) (((F.obj d).1.map gr'.op) (v' r)) =
        ((F.obj d).1.map i.op) (((F.obj d).1.map e.op) (v' r)) := hleft
    _ = ((F.obj d).1.map i.op) (((F.obj d).1.map (gr q).op) (v' (right q))) := by
          simpa [q] using hi
    _ = ((F.obj d).1.map (i ≫ gr q).op) (v' (right q)) := by
          simp [FunctorToTypes.map_comp_apply, Category.assoc, op_comp]

/-- Helper for Lemma 7.17.10: first-level pullback equalities transport unchanged to any later
ordinal stage obtained by a single transition map. -/
lemma stage_family_first_level_pullback_equalities_at_later_stage
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {d e : Set.Iio β}
    (hde : d.1 ≤ e.1)
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hfirst :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj d).1.map q.2.1.2.op) (v' q.1) =
          ((F.obj d).1.map (gr q).op) (v' (right q))) :
    ∀ q : Σ i : R.uncurry, (T i).uncurry,
      ((F.obj e).1.map q.2.1.2.op)
          (((F.map (homOfLE hde)).1.app (op q.1.1.1)) (v' q.1)) =
        ((F.obj e).1.map (gr q).op)
          (((F.map (homOfLE hde)).1.app (op (right q).1.1)) (v' (right q))) := by
  intro q
  -- Push the first-level equality forward along the transition map and commute restrictions with
  -- that transition on both sides.
  calc
    ((F.obj e).1.map q.2.1.2.op)
        (((F.map (homOfLE hde)).1.app (op q.1.1.1)) (v' q.1)) =
      ((F.map (homOfLE hde)).1.app (op q.2.1.1))
        (((F.obj d).1.map q.2.1.2.op) (v' q.1)) := by
          simpa using
            (sheaf_transition_app_map_eq_map_app
              (β := β)
              (F := F)
              (f := homOfLE hde)
              (g := q.2.1.2)
              (a := v' q.1)).symm
    _ =
      ((F.map (homOfLE hde)).1.app (op q.2.1.1))
        (((F.obj d).1.map (gr q).op) (v' (right q))) := by
          exact congrArg (((F.map (homOfLE hde)).1.app (op q.2.1.1))) (hfirst q)
    _ =
      ((F.obj e).1.map (gr q).op)
        (((F.map (homOfLE hde)).1.app (op (right q).1.1)) (v' (right q))) := by
          simpa using
            (sheaf_transition_app_map_eq_map_app
              (β := β)
              (F := F)
              (f := homOfLE hde)
              (g := gr q)
              (a := v' (right q)))


end

end CategoryTheory
