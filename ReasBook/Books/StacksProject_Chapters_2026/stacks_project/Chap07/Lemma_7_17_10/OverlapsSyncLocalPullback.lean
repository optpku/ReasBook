module

public import stacks_project.Chap07.Lemma_7_17_10.OverlapsFixed

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

/-- Site-local replacement for the temporary global pullback used in the fixed-target overlap
synchronization. The data remembers one common source for the left base branch and one branch of
`T j`, plus the universal lifting property needed later in the proof. -/
structure siteLocalTargetOverlapData
    {U : C} {R : Presieve U}
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    {A : C} (baseRight : R.uncurry) (baseGr : A ⟶ baseRight.1.1)
    (j : R.uncurry) (qj : (T j).uncurry) where
  Z : C
  gl : Z ⟶ baseRight.1.1
  gt : Z ⟶ (right ⟨j, qj⟩).1.1
  hover : gl ≫ baseRight.1.2 = gt ≫ (right ⟨j, qj⟩).1.2
  lift {X : C} (left : X ⟶ A) (target : X ⟶ qj.1.1)
    (h :
      left ≫ baseGr ≫ baseRight.1.2 =
        target ≫ qj.1.2 ≫ j.1.2) :
    X ⟶ Z
  lift_gl {X : C} (left : X ⟶ A) (target : X ⟶ qj.1.1)
    (h :
      left ≫ baseGr ≫ baseRight.1.2 =
        target ≫ qj.1.2 ≫ j.1.2) :
    lift left target h ≫ gl = left ≫ baseGr
  lift_gt {X : C} (left : X ⟶ A) (target : X ⟶ qj.1.1)
    (h :
      left ≫ baseGr ≫ baseRight.1.2 =
        target ≫ qj.1.2 ≫ j.1.2) :
    lift left target h ≫ gt = target ≫ gr ⟨j, qj⟩

namespace siteLocalTargetOverlapData

/-- Existence of the site-local overlap data from the Stacks site pullback condition: pull back the
original covering branch `j` along the left morphism to `U`, then pull back the `T j`-branch along
the resulting map to `j`. -/
theorem exists_ofPullbacks
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {A : C} (baseRight : R.uncurry) (baseGr : A ⟶ baseRight.1.1)
    (j : R.uncurry) (qj : (T j).uncurry) :
    Nonempty (siteLocalTargetOverlapData T right gr baseRight baseGr j qj) := by
  let leftMapToU : A ⟶ U := baseGr ≫ baseRight.1.2
  have hfirstPull : HasPullback j.1.2 leftMapToU := by
    haveI : R.HasPullbacks leftMapToU :=
      K.hasPullbacks_of_mem leftMapToU hR
    exact R.hasPullback leftMapToU j.2
  letI : HasPullback j.1.2 leftMapToU := hfirstPull
  let firstPull : C := pullback j.1.2 leftMapToU
  let firstToTarget : firstPull ⟶ j.1.1 := pullback.fst j.1.2 leftMapToU
  let firstToLeft : firstPull ⟶ A := pullback.snd j.1.2 leftMapToU
  have hsecondPull : HasPullback qj.1.2 firstToTarget := by
    haveI : (T j).HasPullbacks firstToTarget :=
      K.hasPullbacks_of_mem firstToTarget (hT j)
    exact (T j).hasPullback firstToTarget qj.2
  letI : HasPullback qj.1.2 firstToTarget := hsecondPull
  let Z : C := pullback qj.1.2 firstToTarget
  let gl : Z ⟶ baseRight.1.1 :=
    pullback.snd qj.1.2 firstToTarget ≫ firstToLeft ≫ baseGr
  let gt : Z ⟶ (right ⟨j, qj⟩).1.1 :=
    pullback.fst qj.1.2 firstToTarget ≫ gr ⟨j, qj⟩
  have hover : gl ≫ baseRight.1.2 = gt ≫ (right ⟨j, qj⟩).1.2 := by
    have hfirst :
        firstToTarget ≫ j.1.2 = firstToLeft ≫ leftMapToU := by
      change
        pullback.fst j.1.2 leftMapToU ≫ j.1.2 =
          pullback.snd j.1.2 leftMapToU ≫ leftMapToU
      exact pullback.condition
    have hsecond :
        pullback.fst qj.1.2 firstToTarget ≫ qj.1.2 =
          pullback.snd qj.1.2 firstToTarget ≫ firstToTarget := by
      exact pullback.condition
    have htarget :
        qj.1.2 ≫ j.1.2 = gr ⟨j, qj⟩ ≫ (right ⟨j, qj⟩).1.2 :=
      hcomm ⟨j, qj⟩
    calc
      gl ≫ baseRight.1.2 =
          pullback.snd qj.1.2 firstToTarget ≫ firstToLeft ≫ leftMapToU := by
            change
              (pullback.snd qj.1.2 firstToTarget ≫ firstToLeft ≫ baseGr) ≫
                  baseRight.1.2 =
                pullback.snd qj.1.2 firstToTarget ≫ firstToLeft ≫ leftMapToU
            dsimp only [leftMapToU]
            simp only [Category.assoc]
      _ = pullback.snd qj.1.2 firstToTarget ≫ firstToTarget ≫ j.1.2 := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ pullback.snd qj.1.2 firstToTarget ≫ f) hfirst.symm
      _ = pullback.fst qj.1.2 firstToTarget ≫ qj.1.2 ≫ j.1.2 := by
            simpa [Category.assoc] using congrArg (fun f ↦ f ≫ j.1.2) hsecond.symm
      _ = pullback.fst qj.1.2 firstToTarget ≫ gr ⟨j, qj⟩ ≫
            (right ⟨j, qj⟩).1.2 := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ pullback.fst qj.1.2 firstToTarget ≫ f) htarget
      _ = gt ≫ (right ⟨j, qj⟩).1.2 := by
            change
              pullback.fst qj.1.2 firstToTarget ≫ gr ⟨j, qj⟩ ≫
                  (right ⟨j, qj⟩).1.2 =
                (pullback.fst qj.1.2 firstToTarget ≫ gr ⟨j, qj⟩) ≫
                  (right ⟨j, qj⟩).1.2
            exact (Category.assoc _ _ _).symm
  refine ⟨?_⟩
  refine
    { Z := Z
      gl := gl
      gt := gt
      hover := hover
      lift := ?_
      lift_gl := ?_
      lift_gt := ?_ }
  · intro X left target h
    let toFirst : X ⟶ firstPull :=
      pullback.lift (target ≫ qj.1.2) left (by
        simpa [leftMapToU, Category.assoc] using h.symm)
    exact
      pullback.lift target toFirst (by
        have hfst :
            toFirst ≫ pullback.fst j.1.2 leftMapToU = target ≫ qj.1.2 := by
          simpa [toFirst] using
            pullback.lift_fst (target ≫ qj.1.2) left
              (by simpa [leftMapToU, Category.assoc] using h.symm)
        simpa [firstToTarget] using hfst.symm)
  · intro X left target h
    let toFirst : X ⟶ firstPull :=
      pullback.lift (target ≫ qj.1.2) left (by
        simpa [leftMapToU, Category.assoc] using h.symm)
    let l : X ⟶ Z :=
      pullback.lift target toFirst (by
        have hfst :
            toFirst ≫ pullback.fst j.1.2 leftMapToU = target ≫ qj.1.2 := by
          simpa [toFirst] using
            pullback.lift_fst (target ≫ qj.1.2) left
              (by simpa [leftMapToU, Category.assoc] using h.symm)
        simpa [firstToTarget] using hfst.symm)
    have hsnd₂ : l ≫ pullback.snd qj.1.2 firstToTarget = toFirst := by
      simpa [l] using
        pullback.lift_snd target toFirst (by
          have hfst :
              toFirst ≫ pullback.fst j.1.2 leftMapToU = target ≫ qj.1.2 := by
            simpa [toFirst] using
              pullback.lift_fst (target ≫ qj.1.2) left
                (by simpa [leftMapToU, Category.assoc] using h.symm)
          simpa [firstToTarget] using hfst.symm)
    have hsnd₁ : toFirst ≫ firstToLeft = left := by
      change toFirst ≫ pullback.snd j.1.2 leftMapToU = left
      simpa [toFirst] using
        pullback.lift_snd (target ≫ qj.1.2) left
          (by simpa [leftMapToU, Category.assoc] using h.symm)
    calc
      l ≫ gl =
          (l ≫ pullback.snd qj.1.2 firstToTarget) ≫ firstToLeft ≫ baseGr := by
            change
              l ≫ (pullback.snd qj.1.2 firstToTarget ≫ firstToLeft ≫ baseGr) =
                (l ≫ pullback.snd qj.1.2 firstToTarget) ≫ firstToLeft ≫ baseGr
            simp only [Category.assoc]
      _ = toFirst ≫ firstToLeft ≫ baseGr := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ f ≫ firstToLeft ≫ baseGr) hsnd₂
      _ = left ≫ baseGr := by
            simpa [Category.assoc] using congrArg (fun f ↦ f ≫ baseGr) hsnd₁
  · intro X left target h
    let toFirst : X ⟶ firstPull :=
      pullback.lift (target ≫ qj.1.2) left (by
        simpa [leftMapToU, Category.assoc] using h.symm)
    let l : X ⟶ Z :=
      pullback.lift target toFirst (by
        have hfst :
            toFirst ≫ pullback.fst j.1.2 leftMapToU = target ≫ qj.1.2 := by
          simpa [toFirst] using
            pullback.lift_fst (target ≫ qj.1.2) left
              (by simpa [leftMapToU, Category.assoc] using h.symm)
        simpa [firstToTarget] using hfst.symm)
    have hfst₂ : l ≫ pullback.fst qj.1.2 firstToTarget = target := by
      simpa [l] using
        pullback.lift_fst target toFirst (by
          have hfst :
              toFirst ≫ pullback.fst j.1.2 leftMapToU = target ≫ qj.1.2 := by
            simpa [toFirst] using
              pullback.lift_fst (target ≫ qj.1.2) left
                (by simpa [leftMapToU, Category.assoc] using h.symm)
          simpa [firstToTarget] using hfst.symm)
    calc
      l ≫ gt = (l ≫ pullback.fst qj.1.2 firstToTarget) ≫ gr ⟨j, qj⟩ := by
        change
          l ≫ (pullback.fst qj.1.2 firstToTarget ≫ gr ⟨j, qj⟩) =
            (l ≫ pullback.fst qj.1.2 firstToTarget) ≫ gr ⟨j, qj⟩
        exact (Category.assoc _ _ _).symm
      _ = target ≫ gr ⟨j, qj⟩ := by
        exact congrArg (fun f ↦ f ≫ gr ⟨j, qj⟩) hfst₂

/-- Chosen site-local overlap data. The computational body is intentionally just a classical choice;
the large pullback construction lives in the propositional existence theorem above, which keeps
`.olean` generation from compiling a large data-producing term. -/
noncomputable def ofPullbacks
    {U : C} {R : Presieve U} (hR : R ∈ K U)
    (T : ∀ i : R.uncurry, Presieve i.1.1)
    (hT : ∀ i, T i ∈ K i.1.1)
    (right : (Σ i : R.uncurry, (T i).uncurry) → R.uncurry)
    (gr : ∀ q : Σ i : R.uncurry, (T i).uncurry, q.2.1.1 ⟶ (right q).1.1)
    (hcomm :
      ∀ q : Σ i : R.uncurry, (T i).uncurry,
        q.2.1.2 ≫ q.1.1.2 = gr q ≫ (right q).1.2)
    {A : C} (baseRight : R.uncurry) (baseGr : A ⟶ baseRight.1.1)
    (j : R.uncurry) (qj : (T j).uncurry) :
    siteLocalTargetOverlapData T right gr baseRight baseGr j qj :=
  Classical.choice
    (exists_ofPullbacks
      (K := K)
      (hR := hR)
      (T := T)
      (hT := hT)
      (right := right)
      (gr := gr)
      (hcomm := hcomm)
      (baseRight := baseRight)
      (baseGr := baseGr)
      (j := j)
      (qj := qj))

end siteLocalTargetOverlapData

end CategoryTheory
