module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsGeometry

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

/-- Helper for Lemma 7.17.10: for one fixed overlap pair and one pulled-back secondary cover, the
fixed-target branchwise colimit equalities synchronize to a single later stage while preserving
the colimit images of the base family. -/
lemma presheafColimit_common_stage_of_fixed_overlap_branch_equalities
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
          presheafColimit_stageClass (β := β) (F := F) (a := d) (U := i.1.1) (v' i) =
            x i)
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
    (hD : D ∈ K Y)
    (hDfac : D.FactorsThruAlong B i) :
      ∃ e : Set.Iio β, ∃ hde : d.1 ≤ e.1,
        ∃ w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1),
          (∀ i,
            presheafColimit_stageClass (β := β) (F := F) (a := e) (U := i.1.1) (w i) =
              x i) ∧
        (∀ n : D.uncurry,
          let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
          ((F.obj e).1.map (n.1.2 ≫ i ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (n.1.2 ≫ g ≫ hj').op) (w j)) := by
  let q : Σ i : R.uncurry, (T i).uncurry := ⟨r, ⟨⟨A, e₀⟩, he⟩⟩
  choose b f hf using
    fun n : D.uncurry ↦
      presheafColimit_section_eq_at_later_stage
        (β := β)
        (F := F)
        (U := n.1.1)
        (i := d)
        (s := ((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q)))
        (t := ((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j))
        (h :=
          presheafColimit_fixed_target_pullback_branch_eq_in_colimit
            (β := β)
            (F := F)
            (hcover := hcover)
            (x := x)
            (hx := hx)
            (v' := v')
            (hv_image := hv_image)
            (T := T)
            (right := right)
            (gr := gr)
            (hcomm := hcomm)
            (gr' := gr')
            (hj' := hj')
            (hW := hW)
            (g := g)
            (i := i)
            (e₀ := e₀)
            (he := he)
            (hie := hie)
            (B := B)
            (D := D)
            (hDfac := hDfac)
            (n := n))
  by_cases hDne : Nonempty D.uncurry
  · obtain ⟨e, heD⟩ :=
      coveringPresieve_common_stage_of_small_family
        (β := β)
        (F := F)
        (f := fun n : D.uncurry ↦ (b n).1)
        (hf := fun n ↦ (b n).2)
        (hι := hcover Y D hD)
    obtain ⟨n₀⟩ := hDne
    have hde : d.1 ≤ e.1 := by
      exact le_trans (leOfHom (f n₀)) (heD n₀)
    let w : ∀ i : R.uncurry, (F.obj e).1.obj (op i.1.1) := fun i' ↦
      ((F.map (homOfLE hde)).1.app (op i'.1.1)) (v' i')
    have hw_image :
        ∀ i' : R.uncurry,
          presheafColimit_stageClass (β := β) (F := F) (a := e) (U := i'.1.1) (w i') =
            x i' := by
      intro i'
      -- Transporting the base family to the common stage preserves its prescribed colimit image.
      have hmap :
          presheafColimit_stageClass (β := β) (F := F) (a := d) (U := i'.1.1) (v' i') =
            presheafColimit_stageClass (β := β) (F := F) (a := e) (U := i'.1.1) (w i') := by
        simpa [presheafColimit_stageClass, stageSectionAsPresheaf, w] using
          (congrFun
            (congrFun
              (congrArg NatTrans.app
              (colimit.w (F ⋙ sheafToPresheaf J (Type (max u v))) (homOfLE hde)))
            (op i'.1.1))
          (v' i')).symm
      exact hmap.symm.trans (hv_image i')
    have htarget_e :
        ∀ n : D.uncurry,
          ((F.obj e).1.map (n.1.2 ≫ i ≫ gr q).op) (w (right q)) =
            ((F.obj e).1.map (n.1.2 ≫ g ≫ hj').op) (w j) := by
      intro n
      have hcomp : f n ≫ homOfLE (heD n) = homOfLE hde := by
        exact Subsingleton.elim _ _
      have hleft :
          ((F.obj e).1.map (n.1.2 ≫ i ≫ gr q).op) (w (right q)) =
            ((F.map (homOfLE hde)).1.app (op n.1.1))
              (((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q))) := by
        -- Move the left branch restriction across the common transport to the synchronized stage.
        simpa [w] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hde)
            (g := n.1.2 ≫ i ≫ gr q)
            (a := v' (right q))).symm
      have hright :
          ((F.obj e).1.map (n.1.2 ≫ g ≫ hj').op) (w j) =
            ((F.map (homOfLE hde)).1.app (op n.1.1))
              (((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)) := by
        -- The same transport rewrite applies to the fixed target branch `j`.
        simpa [w] using
          (sheaf_transition_app_map_eq_map_app
            (β := β)
            (F := F)
            (f := homOfLE hde)
            (g := n.1.2 ≫ g ≫ hj')
            (a := v' j)).symm
      have hstage :
          ((F.map (homOfLE hde)).1.app (op n.1.1))
              (((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q))) =
            ((F.map (homOfLE hde)).1.app (op n.1.1))
              (((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)) := by
        -- Factor the common transport through the local later-stage witness chosen for this branch.
        let lhs := ((F.obj d).1.map (n.1.2 ≫ i ≫ gr q).op) (v' (right q))
        let rhs := ((F.obj d).1.map (n.1.2 ≫ g ≫ hj').op) (v' j)
        have hmap_lhs :
            ((F.map (homOfLE hde)).1.app (op n.1.1)) lhs =
              ((F.map (f n ≫ homOfLE (heD n))).1.app (op n.1.1)) lhs := by
          simpa [lhs] using
            congrArg
              (fun a : d ⟶ e ↦ ((F.map a).1.app (op n.1.1)) lhs)
              hcomp.symm
        have hmap_rhs :
            ((F.map (homOfLE hde)).1.app (op n.1.1)) rhs =
              ((F.map (f n ≫ homOfLE (heD n))).1.app (op n.1.1)) rhs := by
          simpa [rhs] using
            congrArg
              (fun a : d ⟶ e ↦ ((F.map a).1.app (op n.1.1)) rhs)
              hcomp.symm
        have hlocal :
            ((F.map (f n ≫ homOfLE (heD n))).1.app (op n.1.1)) lhs =
              ((F.map (f n ≫ homOfLE (heD n))).1.app (op n.1.1)) rhs := by
          simpa [lhs, rhs, Functor.map_comp, Function.comp] using
            congrArg (((F.map (homOfLE (heD n))).1.app (op n.1.1))) (hf n)
        exact hmap_lhs.trans (hlocal.trans hmap_rhs.symm)
      exact hleft.trans (hstage.trans hright.symm)
    exact ⟨e, hde, w, hw_image, htarget_e⟩
  · haveI : IsEmpty D.uncurry := not_nonempty_iff.mp hDne
    -- If there are no pulled-back branches, the current stage already satisfies the empty family
    -- of fixed-target comparisons.
    refine ⟨d, le_rfl, v', hv_image, ?_⟩
    intro n
    exact isEmptyElim n


end

end CategoryTheory
