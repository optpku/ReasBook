module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsRefine

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

/-- Helper for Lemma 7.17.10: once the first-level pullback equalities have been synchronized at
one stage, the remaining gap is to descend them to genuine overlap compatibility on the original
cover. -/
lemma stage_family_targeted_secondary_target_eq
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (hB : ∀ q, B q ∈ K q.2.1.1)
    {d : Set.Iio β}
    (v' : ∀ i : R.uncurry, (F.obj d).1.obj (op i.1.1))
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    (D : Presieve Y)
    (hD : D ∈ K Y)
    (htarget :
      ∀ n : D.uncurry,
        let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
        ((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q)) =
          ((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ((F.obj d).1.map (i ≫ gr q).op) (v' (right q)) =
      ((F.obj d).1.map (g ≫ hj').op) (v' j) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  have hDd : Presieve.IsSheafFor ((F.obj d).1) D := by
    -- The synchronized stage is still a sheaf on the pulled-back secondary cover.
    exact
      ((Presieve.isSheaf_coverage (K := K.toCoverage) ((F.obj d).1)).1
        ((isSheaf_iff_isSheaf_of_type J ((F.obj d).1)).1 (F.obj d).2)) D hD
  apply hDd.isSeparatedFor.ext
  intro X n hn
  let p : D.uncurry := ⟨⟨X, n⟩, hn⟩
  -- Evaluate the targeted branchwise equality on the concrete branch of the pulled-back cover.
  simpa [q, p, FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using htarget p

/-- Helper for Lemma 7.17.10: after pulling a retained secondary branch back along the outer
factorization, the refined branch still has the same composite to `U` as the fixed overlap branch
`j`. -/
lemma pulled_back_secondary_branch_base_eq_to_fixed_overlap
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    (hie : g ≫ gr' = i ≫ e)
    (B : Presieve A)
    (D : Presieve Y)
    (hDfac : D.FactorsThruAlong B i)
    (n : D.uncurry) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ∃ m : B.uncurry, ∃ i' : n.1.1 ⟶ m.1.1,
      i' ≫ m.1.2 = n.1.2 ≫ i ∧
      ((i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2 = ((n.1.2 ≫ g ≫ hj') ≫ j.1.2) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  rcases n with ⟨⟨Y', g'⟩, hg'⟩
  obtain ⟨A', i', e', he', hi'e'⟩ := hDfac hg'
  let m : B.uncurry := ⟨⟨A', e'⟩, he'⟩
  refine ⟨m, i', ?_, ?_⟩
  · simpa [m] using hi'e'
  -- Reassociate the pulled-back secondary branch until it matches the fixed overlap branch over
  -- the common base object `U`.
  calc
    ((i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2 =
        (i' ≫ m.1.2) ≫ (gr q ≫ (right q).1.2) := by simp [Category.assoc]
    _ = (g' ≫ i) ≫ (gr q ≫ (right q).1.2) := by
          simpa [m, Category.assoc] using congrArg (fun t ↦ t ≫ (gr q ≫ (right q).1.2)) hi'e'
    _ = (g' ≫ i) ≫ (e ≫ r.1.2) := by
          simpa [q] using congrArg (fun t ↦ (g' ≫ i) ≫ t) (hcomm q).symm
    _ = ((g' ≫ i) ≫ e) ≫ r.1.2 := by simp [Category.assoc]
    _ = ((g' ≫ g) ≫ gr') ≫ r.1.2 := by
          simpa [Category.assoc] using congrArg (fun t ↦ (g' ≫ t) ≫ r.1.2) hie.symm
    _ = (g' ≫ g) ≫ (hj' ≫ j.1.2) := by
          simpa [Category.assoc] using congrArg (fun t ↦ (g' ≫ g) ≫ t) hW
    _ = ((g' ≫ g ≫ hj') ≫ j.1.2) := by simp [Category.assoc]

/-- Helper for Lemma 7.17.10: once the pulled-back owner branch has been matched with the outer
factorization `i`, the fixed-overlap base equality can be rewritten directly on the source of the
pulled-back branch. -/
lemma pulled_back_secondary_branch_base_eq_to_fixed_overlap_normalized
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {r j : R.uncurry} {Y A : C}
    (hj' : Y ⟶ j.1.1)
    (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    {B : Presieve A} {D : Presieve Y}
    (n : D.uncurry)
    {m : B.uncurry} {i' : n.1.1 ⟶ m.1.1}
    (hi' : i' ≫ m.1.2 = n.1.2 ≫ i)
    (hbase :
      let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
      ((i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2 = ((n.1.2 ≫ hj') ≫ j.1.2)) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ((n.1.2 ≫ i ≫ gr q) ≫ (right q).1.2) = ((n.1.2 ≫ hj') ≫ j.1.2) := by
  -- This is only the associativity/rewriting step isolated from the later same-stage descent.
  simpa [Category.assoc, hi'] using hbase

/-- Helper for Lemma 7.17.10: after choosing one branch `n` of the pulled-back secondary cover,
any further precomposition `k` preserves the normalized equality of composites to the remembered
fixed overlap branch `j`. -/
lemma sigma_refinement_overlap_base_composite_eq
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {r j : R.uncurry} {W Y A X : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    (hie : g ≫ gr' = i ≫ e)
    {B : Presieve A} {D : Presieve Y}
    (hDfac : D.FactorsThruAlong B i)
    (n : D.uncurry)
    (k : X ⟶ n.1.1) :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    ∃ m : B.uncurry,
      ∃ i' : n.1.1 ⟶ m.1.1,
        i' ≫ m.1.2 = n.1.2 ≫ i ∧
        ((k ≫ i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2 = ((k ≫ n.1.2 ≫ g ≫ hj') ≫ j.1.2) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  rcases n with ⟨⟨Y', g'⟩, hg'⟩
  obtain ⟨A', i', e', he', hi'e'⟩ := hDfac hg'
  let m : B.uncurry := ⟨⟨A', e'⟩, he'⟩
  have hi' : i' ≫ m.1.2 = g' ≫ i := by
    simpa [m] using hi'e'
  refine ⟨m, i', ?_, ?_⟩
  · exact hi'
  -- Precomposing the normalized overlap equality keeps the source proof's base-composite route
  -- intact while exposing the exact transport needed for the later fixed-target descent.
  calc
    ((k ≫ i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2 =
        (((k ≫ g') ≫ i) ≫ gr q) ≫ (right q).1.2 := by
          simpa [Category.assoc, hi']
    _ = ((k ≫ g') ≫ i) ≫ (gr q ≫ (right q).1.2) := by
          simp [Category.assoc]
    _ = ((k ≫ g') ≫ i) ≫ (e ≫ r.1.2) := by
          simpa [q] using congrArg (fun t ↦ ((k ≫ g') ≫ i) ≫ t) (hcomm q).symm
    _ = ((((k ≫ g') ≫ i) ≫ e) ≫ r.1.2) := by
          simp [Category.assoc]
    _ = ((((k ≫ g') ≫ g) ≫ gr') ≫ r.1.2) := by
          simpa [Category.assoc] using congrArg (fun t ↦ (((k ≫ g') ≫ t) ≫ r.1.2)) hie.symm
    _ = (((k ≫ g') ≫ g) ≫ (hj' ≫ j.1.2)) := by
          simpa [Category.assoc] using congrArg (fun t ↦ (((k ≫ g') ≫ g) ≫ t)) hW
    _ = ((k ≫ g' ≫ g ≫ hj') ≫ j.1.2) := by
          simp [Category.assoc]

/-- Helper for Lemma 7.17.10: once a refined branch of `D` is further refined by a branch of the
fixed-target pullback cover over `j`, the resulting `T j`-branch has the same composite to `U` as
the corresponding retained secondary branch. -/
lemma fixed_target_pullback_branch_base_composite_eq
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {r j : R.uncurry} {W Y A X A' : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e : A ⟶ r.1.1) (he : T r e)
    (hie : g ≫ gr' = i ≫ e)
    {B : Presieve A} {D : Presieve Y}
    (hDfac : D.FactorsThruAlong B i)
    (n : D.uncurry)
    (k : X ⟶ n.1.1)
    (c : X ⟶ A') (e' : A' ⟶ j.1.1) (he' : T j e')
    (hc : c ≫ e' = k ≫ n.1.2 ≫ g ≫ hj') :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
    let qj : Σ i : R.uncurry, (T i).uncurry := ⟨j, ⟨⟨A', e'⟩, he'⟩⟩
    ((k ≫ n.1.2 ≫ i ≫ gr q) ≫ (right q).1.2) =
      ((c ≫ gr qj) ≫ (right qj).1.2) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e⟩, he⟩⟩
  let qj : Σ i : R.uncurry, (T i).uncurry := ⟨j, ⟨⟨A', e'⟩, he'⟩⟩
  obtain ⟨m, i', hi', hbase⟩ :=
    sigma_refinement_overlap_base_composite_eq
      (K := K)
      (β := β)
      (F := F)
      (hcover := hcover)
      (T := T)
      (right := right)
      (gr := gr)
      (hcomm := hcomm)
      (gr' := gr')
      (hj' := hj')
      (hW := hW)
      (g := g)
      (i := i)
      (e := e)
      (he := he)
      (hie := hie)
      (hDfac := hDfac)
      (n := n)
      (k := k)
  -- First rewrite the retained secondary branch to the normalized fixed-target overlap branch.
  calc
    ((k ≫ n.1.2 ≫ i ≫ gr q) ≫ (right q).1.2) =
        (((k ≫ i' ≫ m.1.2) ≫ gr q) ≫ (right q).1.2) := by
          simpa [Category.assoc, hi', q]
    _ = ((k ≫ n.1.2 ≫ g ≫ hj') ≫ j.1.2) := by
          simpa [q] using hbase
    _ = (c ≫ e' ≫ j.1.2) := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ j.1.2) hc.symm
    _ = c ≫ (e' ≫ j.1.2) := by
          simp [Category.assoc]
    _ = c ≫ (gr qj ≫ (right qj).1.2) := by
          simpa [qj] using congrArg (fun t ↦ c ≫ t) (hcomm qj)
    _ = ((c ≫ gr qj) ≫ (right qj).1.2) := by
          simp [Category.assoc]

/-- Helper for Lemma 7.17.10: if a synchronized stage family still maps to the original
compatible colimit family, then every branch of a pulled-back secondary cover already compares to
the fixed overlap branch `j` in the presheaf colimit. -/
lemma presheafColimit_fixed_target_pullback_branch_eq_in_colimit
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
        presheafColimit_stageClass (β := β) (F := F) (a := d) (U := i.1.1) (v' i) = x i)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e₀ : A ⟶ r.1.1) (he : T r e₀)
    (hie : g ≫ gr' = i ≫ e₀)
    (B : Presieve A)
    (D : Presieve Y)
    (hDfac : D.FactorsThruAlong B i) :
    ∀ n : D.uncurry,
      let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op n.1.1))
          (((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q))) =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op n.1.1))
          (((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)) := by
  intro n
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
  obtain ⟨m, i', hi', hbase⟩ :=
    pulled_back_secondary_branch_base_eq_to_fixed_overlap
      (β := β)
      (F := F)
      (hcover := hcover)
      (T := T)
      (right := right)
      (gr := gr)
      (hcomm := hcomm)
      (gr' := gr')
      (hj' := hj')
      (hW := hW)
      (g := g)
      (i := i)
      (e := e₀)
      (he := he)
      (hie := hie)
      (B := B)
      (D := D)
      (hDfac := hDfac)
      (n := n)
  -- Compare the two branches directly in the presheaf colimit, now that both composites to `U`
  -- have been normalized against the fixed target branch `j`.
  have hcolim :
      ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op n.1.1))
          (((F.obj d).1.map (((i' ≫ m.1.2) ≫ gr q)).op) (v' (right q))) =
        ((colimit.ι (F ⋙ sheafToPresheaf J (Type (max u v))) d).app (op n.1.1))
          (((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)) := by
    exact
      presheafColimit_overlap_eq_in_colimit
        (β := β)
        (F := F)
        (hcover := hcover)
        (x := x)
        (hx := hx)
        (v := v')
        (hv_image := hv_image)
        (gi := ((i' ≫ m.1.2) ≫ gr q))
        (gj := n.1.2 ≫ g ≫ hj')
        hbase
  simpa [Category.assoc, q, hi'] using hcolim


end

end CategoryTheory
