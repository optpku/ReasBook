module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsTransport

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

/-- Helper for Lemma 7.17.10: each branch of a retained secondary pullback cover can be refined to
one branch of the original covering family at the synchronized stage, while keeping track of the
base composite to `U`. -/
lemma stage_family_secondary_branch_refines_to_cover_branch
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hfirst :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj d).1.map q.2.1.2.op) (v' q.1) =
          ((F.obj d).1.map (gr q).op) (v' (right q)))
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hBfac : ∀ q, (B q).FactorsThruAlong (T q.1) q.2.1.2)
    (hbranch_d :
      ∀ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry,
        ((F.obj d).1.map (p.2.1.2 ≫ p.1.2.1.2).op) (v' p.1.1) =
          ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1)))
    {r : R.uncurry} {A : C} (e : A ⟶ r.1.1) (he : T r e)
    (m : (B ⟨r, ⟨⟨A, e⟩, he⟩⟩).uncurry) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ∃ k : R.uncurry, ∃ t : m.1.1 ⟶ k.1.1,
      ((F.obj d).1.map (m.1.2 ≫ gr q).op) (v' (right q)) =
        ((F.obj d).1.map t.op) (v' k) ∧
      t ≫ k.1.2 = (m.1.2 ≫ e) ≫ r.1.2 := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  obtain ⟨A', i', e', he', hi'e'⟩ := hBfac q m.2
  let q' : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A', e'⟩, he'⟩⟩
  let k : R.uncurry := right q'
  have hbranch_q :
      ((F.obj d).1.map (m.1.2 ≫ e).op) (v' r) =
        ((F.obj d).1.map (m.1.2 ≫ gr q).op) (v' (right q)) := by
    -- Evaluate the retained synchronized secondary equality on the concrete branch `m`.
    simpa [q] using hbranch_d ⟨q, m⟩
  have hstage_q' :
      ((F.obj d).1.map (m.1.2 ≫ e).op) (v' r) =
        ((F.obj d).1.map (i' ≫ gr q').op) (v' k) := by
    -- Push the first-level equality for the factorized branch `q'` across the factorization map
    -- `i' : m.1.1 ⟶ A'`.
    have hi := congrArg (((F.obj d).1.map i'.op)) (hfirst q')
    have hleft :
        ((F.obj d).1.map (m.1.2 ≫ e).op) (v' r) =
          ((F.obj d).1.map (i' ≫ e').op) (v' r) := by
      exact congrArg (fun f : m.1.1 ⟶ r.1.1 ↦ ((F.obj d).1.map f.op) (v' r)) hi'e'.symm
    have hright :
        ((F.obj d).1.map (i' ≫ e').op) (v' r) =
          ((F.obj d).1.map (i' ≫ gr q').op) (v' k) := by
      simpa [q', k, FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using hi
    exact hleft.trans hright
  refine ⟨k, i' ≫ gr q', hbranch_q.symm.trans hstage_q', ?_⟩
  -- The refined branch keeps the same composite to `U` as the original secondary branch.
  calc
    (i' ≫ gr q') ≫ k.1.2 = i' ≫ (gr q' ≫ k.1.2) := by simp [Category.assoc]
    _ = i' ≫ (e' ≫ r.1.2) := by
          simpa [q', k] using congrArg (fun t ↦ i' ≫ t) (hcomm q').symm
    _ = (i' ≫ e') ≫ r.1.2 := by simp [Category.assoc]
    _ = (m.1.2 ≫ e) ≫ r.1.2 := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ r.1.2) hi'e'

/-- Helper for Lemma 7.17.10: after pulling a retained secondary cover back along the outer
factorization map, each transported branch still refines to one original cover branch, and the
refined branch keeps the same composite to `U` as the fixed overlap branch. -/
lemma stage_family_pulled_back_secondary_branch_refines_to_cover_branch
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    (hfirst :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj d).1.map q.2.1.2.op) (v' q.1) =
          ((F.obj d).1.map (gr q).op) (v' (right q)))
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hBfac : ∀ q, (B q).FactorsThruAlong (T q.1) q.2.1.2)
    (hbranch_d :
      ∀ p : Σ q : Σ i : R.uncurry, (T i).uncurry, (B q).uncurry,
        ((F.obj d).1.map (p.2.1.2 ≫ p.1.2.1.2).op) (v' p.1.1) =
          ((F.obj d).1.map (p.2.1.2 ≫ gr p.1).op) (v' (right p.1)))
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    (hie : g ≫ gr' = i ≫ e)
    (D : Presieve Y)
    (hDfac : D.FactorsThruAlong (B ⟨r, ⟨⟨A, e⟩, he⟩⟩) i) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ∀ n : D.uncurry,
      ∃ k : R.uncurry, ∃ t : n.1.1 ⟶ k.1.1,
        ((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q)) =
          ((F.obj d).1.map t.op) (v' k) ∧
        t ≫ k.1.2 = ((n.1.2 ≫ g ≫ hj') ≫ j.1.2) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  change
    ∀ n : D.uncurry,
      ∃ k : R.uncurry, ∃ t : n.1.1 ⟶ k.1.1,
        ((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q)) =
          ((F.obj d).1.map t.op) (v' k) ∧
        t ≫ k.1.2 = ((n.1.2 ≫ g ≫ hj') ≫ j.1.2)
  intro n
  let Y' : C := n.1.1
  let g' : Y' ⟶ Y := n.1.2
  have hDbranch :
      ∃ (A' : C) (i' : Y' ⟶ A') (e' : A' ⟶ A),
        B q e' ∧ i' ≫ e' = g' ≫ i := by
    exact hDfac n.2
  obtain ⟨A', i', e', he', hi'e'⟩ := hDbranch
  let m : (B q).uncurry := ⟨⟨A', e'⟩, he'⟩
  obtain ⟨k, t, hstage, hbase⟩ :=
    stage_family_secondary_branch_refines_to_cover_branch
      (K := K)
      (hcover := hcover)
      (β := β)
      (F := F)
      (T := T)
      (right := right)
      (gr := gr)
      (hcomm := hcomm)
      (v' := v')
      (hfirst := hfirst)
      (B := B)
      (hBfac := hBfac)
      (hbranch_d := hbranch_d)
      (r := r)
      (e := e)
      (he := he)
      (m := m)
  refine ⟨k, i' ≫ t, ?_, ?_⟩
  · -- Transport the stage equality from the retained secondary branch to the pulled-back branch.
    have hi := congrArg (((F.obj d).1.map i'.op)) hstage
    have hleft_path : i' ≫ e' ≫ gr q = n.1.2 ≫ i ≫ gr q := by
      simpa [g', Category.assoc] using congrArg (fun f : Y' ⟶ A ↦ f ≫ gr q) hi'e'
    have hleft :
        ((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q)) =
          ((F.obj d).1.map (i' ≫ e' ≫ gr q).op) (v' (right q)) := by
      exact
        congrArg
          (fun f : Y' ⟶ (right q).1.1 ↦ ((F.obj d).1.map f.op) (v' (right q)))
          hleft_path.symm
    have hright :
        ((F.obj d).1.map (i' ≫ e' ≫ gr q).op) (v' (right q)) =
          ((F.obj d).1.map (i' ≫ t).op) (v' k) := by
      simpa [FunctorToTypes.map_comp_apply, q, m, Category.assoc, op_comp] using hi
    exact hleft.trans hright
  · -- Normalize the two factorizations until both branches are written over the same overlap.
    have hbranch_base :
        (g' ≫ g) ≫ gr' = i' ≫ (e' ≫ e) := by
      calc
        (g' ≫ g) ≫ gr' = g' ≫ (g ≫ gr') := by simp [Category.assoc]
        _ = g' ≫ (i ≫ e) := by
              simpa using congrArg (fun t ↦ g' ≫ t) hie
        _ = (g' ≫ i) ≫ e := by simp [Category.assoc]
        _ = (i' ≫ e') ≫ e := by
              simpa [Category.assoc] using congrArg (fun t ↦ t ≫ e) hi'e'.symm
        _ = i' ≫ (e' ≫ e) := by simp [Category.assoc]
    have hbase_to_j :
        (i' ≫ t) ≫ k.1.2 = ((g' ≫ g) ≫ hj') ≫ j.1.2 := by
      simpa [Category.assoc] using
        pullback_branch_factorization_base_eq
          (β := β)
          (F := F)
          (hcover := hcover)
          (r := r)
          (j := j)
          (k := k)
          (gr' := gr')
          (hj' := hj')
          (g := g' ≫ g)
          (i := i')
          (e := e' ≫ e)
          (i' := t)
          (hie := hbranch_base)
          (hi'e' := hbase.symm)
          (hW := hW)
    simpa [g', Category.assoc] using hbase_to_j


end

end CategoryTheory
