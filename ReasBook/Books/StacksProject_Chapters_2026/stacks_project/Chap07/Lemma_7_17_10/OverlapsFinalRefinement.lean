module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsFinalBasic

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
/-- Helper for Lemma 7.17.10: on one concrete common source, the synchronized target-overlap
equality and the first-level equality recover the fixed-target comparison after restriction. -/
lemma stage_family_fixed_target_eq_on_refined_common_source
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
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (htarget_e :
      ∀ p : targeted_secondary_owner_index (T := T) B,
        ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
          let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
          let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
          ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj)))
    {r j : R.uncurry} {W Y A X A₁ A₂ N : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e₀ : A ⟶ r.1.1) (he : T r e₀)
    (hie : g ≫ gr' = i ≫ e₀)
    (nmap : N ⟶ Y)
    (i₁ : N ⟶ A₁) (e₁ : A₁ ⟶ A) (he₁ : B ⟨r, ⟨⟨A, e₀⟩, he⟩⟩ e₁)
    (hi₁ : i₁ ≫ e₁ = nmap ≫ i)
    (k : X ⟶ N)
    (c : X ⟶ A₂) (e₂ : A₂ ⟶ j.1.1) (he₂ : T j e₂)
    (hc : c ≫ e₂ = k ≫ nmap ≫ g ≫ hj') :
    let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
    ((F.obj e).1.map k.op) (((F.obj e).1.map (nmap ≫ i ≫ gr q).op) (w (right q))) =
      ((F.obj e).1.map k.op) (((F.obj e).1.map (nmap ≫ g ≫ hj').op) (w j)) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
  let m : (B q).uncurry := ⟨⟨A₁, e₁⟩, he₁⟩
  let p : targeted_secondary_owner_index (T := T) B := ⟨⟨q, m⟩, j⟩
  let qj : Σ i : R.uncurry, (T i).uncurry := ⟨j, ⟨⟨A₂, e₂⟩, he₂⟩⟩
  let hoverlap :
      targeted_secondary_target_overlap_witness (T := T) (B := B) p :=
    ⟨X, k ≫ i₁, ⟨⟨A₂, e₂⟩, he₂⟩,
      ⟨c,
        pulled_back_secondary_branch_target_overlap_base_eq
          (T := T)
          (B := B)
          (gr' := gr')
          (hj' := hj')
          (hW := hW)
          (g := g)
          (i := i)
          (e₀ := e₀)
          (he := he)
          (hie := hie)
          (nmap := nmap)
          (i₁ := i₁)
          (e₁ := e₁)
          (he₁ := he₁)
          (hi₁ := hi₁)
          (k := k)
          (c := c)
          (e₂ := e₂)
          (he₂ := he₂)
          (hc := hc)⟩⟩
  have htarget_branch :
      ((F.obj e).1.map (k ≫ nmap ≫ i ≫ gr q).op) (w (right q)) =
        ((F.obj e).1.map (c ≫ gr qj).op) (w (right qj)) := by
    have hpath :
        k ≫ nmap ≫ i ≫ gr q = k ≫ i₁ ≫ e₁ ≫ gr q := by
      simpa [Category.assoc] using congrArg (fun f ↦ k ≫ f ≫ gr q) hi₁.symm
    have hraw :
        ((F.obj e).1.map (k ≫ i₁ ≫ e₁ ≫ gr q).op) (w (right q)) =
          ((F.obj e).1.map (c ≫ gr qj).op) (w (right qj)) := by
      simpa [p, q, qj, m, hoverlap, Category.assoc] using htarget_e p hoverlap
    exact
      (congrArg (fun f ↦ ((F.obj e).1.map f.op) (w (right q))) hpath).trans hraw
  have hfinal :
      ((F.obj e).1.map (k ≫ nmap ≫ i ≫ gr q).op) (w (right q)) =
        ((F.obj e).1.map (k ≫ nmap ≫ g ≫ hj').op) (w qj.1) := by
    refine
      stage_family_fixed_target_eq_of_base_cover_eq_and_first_level
        (K := K)
        (β := β)
        (F := F)
        (T := T)
        (right := right)
        (gr := gr)
        (w := w)
        (hfirst_e := hfirst_e)
        (q := q)
        (qj := qj)
        (a := k ≫ nmap ≫ i ≫ gr q)
        (b := c ≫ gr qj)
        (c := c)
        (d := k ≫ nmap ≫ g ≫ hj')
        htarget_branch
        rfl
        ?_
    simpa [qj, Category.assoc] using hc.symm
  simpa [q, qj, FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using hfinal

omit hcover in
/-- Helper for Lemma 7.17.10: after the anonymous base-cover equalities have been synchronized at
the global stage `e`, the remaining fixed-target comparison is proved branchwise by refining one
pulled-back secondary branch and then descending by separatedness. -/
lemma stage_family_fixed_target_eq_on_base_cover_refinement
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {e : Set.Iio β}
    (w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1))
    (hfirst_e :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        ((F.obj e).1.map q.2.1.2.op) (w q.1) =
          ((F.obj e).1.map (gr q).op) (w (right q)))
    (B : ∀ q : Σ i : R.uncurry, (T i).uncurry, Presieve q.2.1.1)
    (htarget_e :
      ∀ p : targeted_secondary_owner_index (T := T) B,
        ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
          let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
          let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
          ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj)))
    {r j : R.uncurry} {W Y A : C}
    (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1)
    (hW : gr' ≫ r.1.2 = hj' ≫ j.1.2)
    (g : Y ⟶ W) (i : Y ⟶ A) (e₀ : A ⟶ r.1.1) (he : T r e₀)
    (hie : g ≫ gr' = i ≫ e₀)
    (D : Presieve Y) (hD : D ∈ K Y)
    (hDfac : D.FactorsThruAlong (B ⟨r, ⟨⟨A, e₀⟩, he⟩⟩) i) :
    ∀ n : D.uncurry,
      let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
      ((F.obj e).1.map (n.1.2 ≫ i ≫ gr q).op) (w (right q)) =
        ((F.obj e).1.map (n.1.2 ≫ g ≫ hj').op) (w j) := by
  intro n
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
  obtain ⟨A₁, i₁, e₁, he₁, hi₁⟩ := hDfac n.2
  obtain ⟨E, hE, hEfac⟩ := K.toCoverage.pullback (n.1.2 ≫ g ≫ hj') (T j) (hT j)
  have hEe : Presieve.IsSheafFor ((F.obj e).1) E := by
    -- The global stage remains a sheaf on the concrete target-side refinement cover.
    exact
      ((Presieve.isSheaf_coverage (K := K.toCoverage) ((F.obj e).1)).1
        ((isSheaf_iff_isSheaf_of_type J ((F.obj e).1)).1 (F.obj e).2)) E hE
  apply hEe.isSeparatedFor.ext
  intro X k hk
  let t : E.uncurry := ⟨⟨X, k⟩, hk⟩
  obtain ⟨A₂, c, e₂, he₂, hc⟩ := hEfac t.2
  exact
    stage_family_fixed_target_eq_on_refined_common_source
      (β := β)
      (F := F)
      (K := K)
      (T := T)
      (right := right)
      (gr := gr)
      (w := w)
      (hfirst_e := hfirst_e)
      (B := B)
      (htarget_e := htarget_e)
      (gr' := gr')
      (hj' := hj')
      (hW := hW)
      (g := g)
      (i := i)
      (e₀ := e₀)
      (he := he)
      (hie := hie)
      (nmap := n.1.2)
      (i₁ := i₁)
      (e₁ := e₁)
      (he₁ := he₁)
      (hi₁ := hi₁)
      (k := k)
      (c := c)
      (e₂ := e₂)
      (he₂ := he₂)
      (hc := hc)


end

end CategoryTheory
