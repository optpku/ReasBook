module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsFinalRefinement

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

/-- Helper for Lemma 7.17.10: once the anonymous base-cover equalities and the first-level
equalities both live at the global stage `e`, one concrete overlap on `R` is handled by opening
the outer pullback cover, then the pulled-back secondary cover, and finally the local
fixed-target refinement. -/
lemma stage_family_overlap_of_base_cover_owner_equalities_at_global_stage
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
    (hB : ∀ q, B q ∈ K q.2.1.1)
    (htarget_e :
      ∀ p : targeted_secondary_owner_index (T := T) B,
        ∀ z : targeted_secondary_target_overlap_witness (T := T) (B := B) p,
          let q : Σ i : R.uncurry, (T i).uncurry := p.1.1
          let qj : Σ i : R.uncurry, (T i).uncurry := ⟨p.2, z.2.2.1⟩
          ((F.obj e).1.map (z.2.1 ≫ p.1.2.1.2 ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (z.2.2.2.1 ≫ gr qj).op) (w (right qj))) :
    ∀ {r j : R.uncurry} {W : C}
      (gr' : W ⟶ r.1.1) (hj' : W ⟶ j.1.1),
      gr' ≫ r.1.2 = hj' ≫ j.1.2 →
        ((F.obj e).1.map gr'.op) (w r) =
          ((F.obj e).1.map hj'.op) (w j) := by
  intro r j W gr' hj' hW
  -- Route correction: the outer pullback descent now happens at the global fixed stage `e`. The
  -- only remaining source-faithful gap is to convert the retained owner family into a
  -- fixed-target branchwise equality against the chosen branch `j`.
  obtain ⟨S, hS, hSfac⟩ := K.toCoverage.pullback gr' (T r) (hT r)
  have hSe : Presieve.IsSheafFor ((F.obj e).1) S := by
    -- The globally synchronized stage remains a sheaf on the outer pullback cover.
    exact
      ((Presieve.isSheaf_coverage (K := K.toCoverage) ((F.obj e).1)).1
        ((isSheaf_iff_isSheaf_of_type J ((F.obj e).1)).1 (F.obj e).2)) S hS
  apply hSe.isSeparatedFor.ext
  intro Y g hg
  let m : S.uncurry := ⟨⟨Y, g⟩, hg⟩
  obtain ⟨A, i, e₀, he, hie⟩ := hSfac m.2
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
  have hbranch :
      ((F.obj e).1.map g.op) (((F.obj e).1.map gr'.op) (w r)) =
        ((F.obj e).1.map (i ≫ gr q).op) (w (right q)) := by
    -- Rewrite the outer branch with the transported first-level equality indexed by `q`.
    simpa [q] using
      pullback_branch_restriction_eq_of_first_level_equality
        (K := K)
        (hcover := hcover)
        (β := β)
        (F := F)
        (T := T)
        (right := right)
        (gr := gr)
        (v' := w)
        (hfirst := hfirst_e)
        (r := r)
        (gr' := gr')
        (g := g)
        (i := i)
        (e := e₀)
        (he := he)
        (hie := hie.symm)
  have htarget :
      ((F.obj e).1.map (i ≫ gr q).op) (w (right q)) =
        ((F.obj e).1.map (g ≫ hj').op) (w j) := by
    obtain ⟨D, hD, hDfac⟩ := K.toCoverage.pullback i (B q) (hB q)
    -- The remaining descent happens on the pullback of the retained secondary cover along `i`,
    -- and the fixed target branch is introduced only inside this local branchwise refinement.
    refine
      stage_family_targeted_secondary_target_eq
        (K := K)
        (hcover := hcover)
        (β := β)
        (F := F)
        (T := T)
        (right := right)
        (gr := gr)
        (B := B)
        (hB := hB)
        (v' := w)
        (gr' := gr')
        (hj' := hj')
        (g := g)
        (i := i)
        (e := e₀)
        (he := he)
        (D := D)
        (hD := hD)
        (htarget :=
          stage_family_fixed_target_eq_on_base_cover_refinement
            (β := β)
            (F := F)
            (K := K)
            (T := T)
            (hT := hT)
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
            (hie := hie.symm)
            (D := D)
            (hD := hD)
            (hDfac := hDfac))
  -- The outer descent closes once the targeted inner comparison is available on this branch.
  simpa [FunctorToTypes.map_comp_apply, Category.assoc, op_comp] using hbranch.trans htarget


end

end CategoryTheory
