/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_2_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_1.Iterates

public section

/-! Reusable GPCG iterate interface for Exercise 9.12.

This item-owned foundation module supplies the minimal source-facing GPCG owner
surface needed by the `§9.4.2` benchmark exercise without inventing the still
missing concrete Chapter 9 benchmark data. The owner keeps the two algorithmic
phases explicit: a projected-gradient stage followed by an inner
conjugate-gradient refinement of a stagewise quadratic model.
-/

noncomputable section

namespace GPCG

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The projected-gradient stage point `f_v^GP` used by GPCG. -/
@[expose] def projectedStage
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (σ : ℝ) (f : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n :=
  GradientProjection.update P J σ f

/-- The inner conjugate-gradient refinement started from the projected stage
`f_v^GP`, using the stagewise quadratic-model coefficients
`quadraticMatrix f_v^GP` and `linearTerm f_v^GP`. -/
@[expose] def cgRefinement
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (innerSteps : ℕ) (fGP : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n :=
  (ConjugateGradient.iterates (quadraticMatrix fGP) (linearTerm fGP) fGP innerSteps).solution

/-- One outer GPCG update first takes the projected-gradient stage point and
then applies the prescribed number of conjugate-gradient inner iterations. -/
@[expose] def update
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℝ) (innerSteps : ℕ) (f : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n :=
  let fGP := projectedStage P J σ f
  cgRefinement quadraticMatrix linearTerm innerSteps fGP

/-- The recursive GPCG iterates generated from the initial iterate `f₀` by the
projected-gradient stage and the inner conjugate-gradient refinement. -/
@[expose] def iterates
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℕ → ℝ) (innerSteps : ℕ → ℕ)
    (f0 : EuclideanSpace ℝ n) :
    ℕ → EuclideanSpace ℝ n
  | 0 => f0
  | v + 1 =>
      update P J quadraticMatrix linearTerm (σ v) (innerSteps v)
        (iterates P J quadraticMatrix linearTerm σ innerSteps f0 v)

/-- The projected-gradient stage points attached to the canonical outer GPCG
iterate family. -/
@[expose] def projectedStages
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℕ → ℝ) (innerSteps : ℕ → ℕ)
    (f0 : EuclideanSpace ℝ n) :
    ℕ → EuclideanSpace ℝ n := fun v ↦
      projectedStage P J (σ v)
        (iterates P J quadraticMatrix linearTerm σ innerSteps f0 v)

/-- `IsStep` records that `next` is obtained from `f` by one GPCG outer step:
first the projected-gradient stage with step size `σ`, then the prescribed
inner conjugate-gradient refinement. -/
@[expose] def IsStep
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℝ) (innerSteps : ℕ)
    (f next : EuclideanSpace ℝ n) : Prop :=
  let fGP := projectedStage P J σ f
  next = cgRefinement quadraticMatrix linearTerm innerSteps fGP

/-- `IsIterateSequence P J quadraticMatrix linearTerm σ innerSteps f₀ f` means
that `f` starts at `f₀` and every successive pair satisfies the source-facing
two-phase GPCG step relation. -/
@[expose] def IsIterateSequence
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℕ → ℝ) (innerSteps : ℕ → ℕ)
    (f0 : EuclideanSpace ℝ n)
    (f : ℕ → EuclideanSpace ℝ n) : Prop :=
  f 0 = f0 ∧
    ∀ v : ℕ,
      IsStep P J quadraticMatrix linearTerm (σ v) (innerSteps v) (f v) (f (v + 1))

omit [DecidableEq n] in
@[simp] theorem projectedStage_eq
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (σ : ℝ) (f : EuclideanSpace ℝ n) :
    projectedStage P J σ f = GradientProjection.update P J σ f := rfl

@[simp] theorem update_eq
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℝ) (innerSteps : ℕ) (f : EuclideanSpace ℝ n) :
    update P J quadraticMatrix linearTerm σ innerSteps f =
      cgRefinement quadraticMatrix linearTerm innerSteps (projectedStage P J σ f) := rfl

@[simp] theorem iterates_zero
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℕ → ℝ) (innerSteps : ℕ → ℕ)
    (f0 : EuclideanSpace ℝ n) :
    iterates P J quadraticMatrix linearTerm σ innerSteps f0 0 = f0 := rfl

@[simp] theorem iterates_succ
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℕ → ℝ) (innerSteps : ℕ → ℕ)
    (f0 : EuclideanSpace ℝ n) (v : ℕ) :
    iterates P J quadraticMatrix linearTerm σ innerSteps f0 (v + 1) =
      update P J quadraticMatrix linearTerm (σ v) (innerSteps v)
        (iterates P J quadraticMatrix linearTerm σ innerSteps f0 v) := rfl

@[simp] theorem projectedStages_apply
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℕ → ℝ) (innerSteps : ℕ → ℕ)
    (f0 : EuclideanSpace ℝ n) (v : ℕ) :
    projectedStages P J quadraticMatrix linearTerm σ innerSteps f0 v =
      projectedStage P J (σ v)
        (iterates P J quadraticMatrix linearTerm σ innerSteps f0 v) := rfl

theorem iterates_succ_eq_cgRefinement
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℕ → ℝ) (innerSteps : ℕ → ℕ)
    (f0 : EuclideanSpace ℝ n) (v : ℕ) :
    iterates P J quadraticMatrix linearTerm σ innerSteps f0 (v + 1) =
      cgRefinement quadraticMatrix linearTerm (innerSteps v)
        (projectedStages P J quadraticMatrix linearTerm σ innerSteps f0 v) := rfl

theorem isStep_iff
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℝ) (innerSteps : ℕ)
    (f next : EuclideanSpace ℝ n) :
    IsStep P J quadraticMatrix linearTerm σ innerSteps f next ↔
      next =
        cgRefinement quadraticMatrix linearTerm innerSteps (projectedStage P J σ f) := by
  rfl

theorem isIterateSequence_iff
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℕ → ℝ) (innerSteps : ℕ → ℕ)
    (f0 : EuclideanSpace ℝ n)
    (f : ℕ → EuclideanSpace ℝ n) :
    IsIterateSequence P J quadraticMatrix linearTerm σ innerSteps f0 f ↔
      f 0 = f0 ∧
        ∀ v : ℕ,
          IsStep P J quadraticMatrix linearTerm (σ v) (innerSteps v) (f v) (f (v + 1)) := by
  rfl

theorem recurrence_iff_eq_iterates
    (P : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (J : EuclideanSpace ℝ n → ℝ)
    (quadraticMatrix : EuclideanSpace ℝ n → Matrix n n ℝ)
    (linearTerm : EuclideanSpace ℝ n → EuclideanSpace ℝ n)
    (σ : ℕ → ℝ) (innerSteps : ℕ → ℕ)
    (f0 : EuclideanSpace ℝ n)
    (f : ℕ → EuclideanSpace ℝ n) :
    IsIterateSequence P J quadraticMatrix linearTerm σ innerSteps f0 f ↔
      f = iterates P J quadraticMatrix linearTerm σ innerSteps f0 := by
  constructor
  · rintro ⟨h0, hstep⟩
    funext v
    induction v with
    | zero =>
        exact h0
    | succ v hv =>
        have hnext :
            f (v + 1) =
              cgRefinement quadraticMatrix linearTerm (innerSteps v)
                (projectedStage P J (σ v) (f v)) := by
          exact
            (isStep_iff P J quadraticMatrix linearTerm (σ v) (innerSteps v)
              (f v) (f (v + 1))).1 (hstep v)
        calc
          f (v + 1) =
              cgRefinement quadraticMatrix linearTerm (innerSteps v)
                (projectedStage P J (σ v) (f v)) := hnext
          _ =
              cgRefinement quadraticMatrix linearTerm (innerSteps v)
                (projectedStage P J (σ v)
                  (iterates P J quadraticMatrix linearTerm σ innerSteps f0 v)) := by
                rw [hv]
          _ = iterates P J quadraticMatrix linearTerm σ innerSteps f0 (v + 1) := by
                rw [iterates_succ_eq_cgRefinement, projectedStages_apply]
  · intro hf
    constructor
    · simp [hf]
    · intro v
      simp [hf, isStep_iff]

end GPCG
