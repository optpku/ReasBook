/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_20.ReducedHessian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

noncomputable section

namespace GPRN

open scoped Matrix

universe u

variable {ι : Type u} [Fintype ι]

/-- The reduced-Newton direction `s_v` at a projected stage point `f_v^GP`
uses the reduced Hessian `H_R(f_v^GP)` and the gradient `gradient J f_v^GP`
whenever `H_R(f_v^GP)` is nonsingular. -/
@[expose] def reducedNewtonDirection
    [DecidableEq ι]
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (fGP : EuclideanSpace ℝ ι)
    (hHR : IsUnit ((ActiveSet.reducedHessian
      (ActiveSet.active (fun i x ↦ x i) fGP) (hessianMatrix fGP)).det)) :
    EuclideanSpace ℝ ι :=
  let HR :=
    ActiveSet.reducedHessian (ActiveSet.active (fun i x ↦ x i) fGP) (hessianMatrix fGP);
  -((((↑(hHR.unit⁻¹) : ℝ) • HR.adjugate).toEuclideanLin) (gradient J fGP))

/-- The reduced-Newton stage updates the projected stage point `f_v^GP` by the
search direction `s_v` and reduced-stage step size `τ_v`, followed by the same
projection `P`. -/
@[expose] def reducedNewtonUpdate
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (τ : ℝ) (fGP s : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  P (fGP + τ • s)

/-- The one-step projected-gradient stage point `f_v^GP` attached to the outer
iterate `f_v`. -/
@[expose] def projectedStage
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ : ℝ) (f : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  GradientProjection.update P J σ f

/-- Backend outer update with an already supplied reduced-stage direction `s_v`.
The source-facing GPRN step relation itself is `GPRN.IsStep` below. -/
@[expose] def update
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ τ : ℝ) (f s : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  let fGP := projectedStage P J σ f
  reducedNewtonUpdate P τ fGP s

/-- Backend outer iterates generated from a stagewise reduced-direction
sequence `s`. The source-facing GPRN iterate-sequence owner is
`GPRN.IsIterateSequence` below. -/
@[expose] def iterates
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι) :
    ℕ → EuclideanSpace ℝ ι
  | 0 => f0
  | v + 1 => update P J (σ v) (τ v) (iterates P J σ τ f0 s v) (s v)

/-- The intermediate projected-gradient stage points `f_v^GP` attached to the
outer GPRN iterates defined from the reduced-direction sequence `s`. -/
@[expose] def projectedStages
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι) :
    ℕ → EuclideanSpace ℝ ι := fun v ↦
      projectedStage P J (σ v) (iterates P J σ τ f0 s v)

/-- A vector `s` is a reduced-Newton direction at a projected stage point
`f_v^GP` when the reduced Hessian there is nonsingular and `s` is given by the
source formula `-H_R(f_v^GP)⁻¹ gradient J f_v^GP`. -/
def IsReducedNewtonDirection
    [DecidableEq ι]
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (fGP s : EuclideanSpace ℝ ι) :
    Prop :=
  ∃ hHR : IsUnit ((ActiveSet.reducedHessian
      (ActiveSet.active (fun i x ↦ x i) fGP) (hessianMatrix fGP)).det),
    s = reducedNewtonDirection J hessianMatrix fGP hHR

/-- Algorithm 9.3.3. A single GPRN step from `f_v` to `f_(v+1)` uses the
projected stage `f_v^GP`, a reduced-Newton direction `s_v` at that stage, an
exact reduced-stage line search `τ_v`, and the reduced-Newton update formula
for the successor iterate. -/
@[expose] def IsStep
    [DecidableEq ι]
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℝ) (f s next : EuclideanSpace ℝ ι) :
    Prop :=
  IsReducedNewtonDirection J hessianMatrix (projectedStage P J σ f) s ∧
    IsMinOn
      (LineSearch.profile (J ∘ P) (projectedStage P J σ f) s)
      (Set.Ioi (0 : ℝ))
      τ ∧
    next = reducedNewtonUpdate P τ (projectedStage P J σ f) s

/-- Algorithm 9.3.3. A stagewise reduced-direction sequence `s` is a GPRN
iterate sequence for the canonical backend family `GPRN.iterates P J σ τ f0 s`
when every successor satisfies the full GPRN step relation. -/
@[expose] def IsIterateSequence
    [DecidableEq ι]
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι) :
    Prop :=
  ∀ v,
    IsStep P J hessianMatrix (σ v) (τ v)
      (iterates P J σ τ f0 s v)
      (s v)
      (iterates P J σ τ f0 s (v + 1))

/-- The stagewise reduced-direction sequence of Algorithm 9.3.3 is source-faithful
when each supplied stage direction `s_v` satisfies the reduced-Newton formula
at the corresponding projected stage point `f_v^GP`. -/
def IsReducedDirectionSequence
    [DecidableEq ι]
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι) :
    Prop :=
  ∀ v, IsReducedNewtonDirection J hessianMatrix (projectedStages P J σ τ f0 s v) (s v)

/-- The reduced-stage line-search condition in Algorithm 9.3.3: at each outer
stage `v`, the reduced-stage step size `τ v` minimizes the projected objective
profile over the ray starting at the projected stage point `f_v^GP` in the
supplied reduced-stage direction `s_v`. -/
def IsExactReducedLineSearch
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι) :
    Prop :=
  ∀ v,
    IsMinOn
      (LineSearch.profile (J ∘ P)
        (projectedStages P J σ τ f0 s v)
        (s v))
      (Set.Ioi (0 : ℝ))
      (τ v)

/-- `reducedNewtonDirection` is the explicit reduced-Hessian formula
`-H_R(f_v^GP)⁻¹ gradient J f_v^GP` under a nonsingularity witness for
`H_R(f_v^GP)`. -/
@[simp] theorem reducedNewtonDirection_eq
    [DecidableEq ι]
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (fGP : EuclideanSpace ℝ ι)
    (hHR : IsUnit ((ActiveSet.reducedHessian
      (ActiveSet.active (fun i x ↦ x i) fGP) (hessianMatrix fGP)).det)) :
    reducedNewtonDirection J hessianMatrix fGP hHR =
      -((ActiveSet.reducedHessian (ActiveSet.active (fun i x ↦ x i) fGP)
            (hessianMatrix fGP))⁻¹).toEuclideanLin
          (gradient J fGP) := by
  let HR :=
    ActiveSet.reducedHessian (ActiveSet.active (fun i x ↦ x i) fGP) (hessianMatrix fGP)
  calc
    reducedNewtonDirection J hessianMatrix fGP hHR =
      -((((↑(hHR.unit⁻¹) : ℝ) • HR.adjugate).toEuclideanLin) (gradient J fGP)) := by
        rfl
    _ = -((HR⁻¹).toEuclideanLin (gradient J fGP)) := by
        rw [Matrix.nonsing_inv_apply HR hHR]

/-- The witness-built reduced-Newton direction satisfies the source-facing
predicate `IsReducedNewtonDirection`. -/
theorem isReducedNewtonDirection_reducedNewtonDirection
    [DecidableEq ι]
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (fGP : EuclideanSpace ℝ ι)
    (hHR : IsUnit ((ActiveSet.reducedHessian
      (ActiveSet.active (fun i x ↦ x i) fGP) (hessianMatrix fGP)).det)) :
    IsReducedNewtonDirection J hessianMatrix fGP
      (reducedNewtonDirection J hessianMatrix fGP hHR) :=
  ⟨hHR, rfl⟩

/-- The one-step projected stage point is the projected-gradient update from
the current outer iterate `f_v`. -/
@[simp] theorem projectedStage_eq
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ : ℝ) (f : EuclideanSpace ℝ ι) :
    projectedStage P J σ f = GradientProjection.update P J σ f := rfl

/-- The zeroth GPRN iterate is the initial guess `f0`. -/
@[simp] theorem iterates_zero
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι) :
    iterates P J σ τ f0 s 0 = f0 := rfl

/-- The successor GPRN iterate is obtained by one outer update from the current
iterate. -/
@[simp] theorem iterates_succ
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι)
    (v : ℕ) :
    iterates P J σ τ f0 s (v + 1) =
      update P J (σ v) (τ v) (iterates P J σ τ f0 s v) (s v) := rfl

/-- The intermediate projected stage point at index `v` is obtained by applying
the projected-gradient stage to the current outer iterate `f_v`. -/
@[simp] theorem projectedStages_apply
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι)
    (v : ℕ) :
    projectedStages P J σ τ f0 s v =
      projectedStage P J (σ v) (iterates P J σ τ f0 s v) := rfl

/-- The successor iterate decomposes into the projected-gradient stage point
followed by the supplied reduced-stage correction. -/
theorem iterates_succ_eq_reducedNewtonUpdate
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι)
    (v : ℕ) :
    iterates P J σ τ f0 s (v + 1) =
      reducedNewtonUpdate
        P
        (τ v)
        (projectedStages P J σ τ f0 s v)
        (s v) := rfl

namespace IsStep

variable [DecidableEq ι]

/-- The reduced-Newton-direction component extracted from a GPRN step. -/
theorem direction
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℝ) (f s next : EuclideanSpace ℝ ι)
    (h : IsStep P J hessianMatrix σ τ f s next) :
    IsReducedNewtonDirection J hessianMatrix (projectedStage P J σ f) s :=
  h.1

/-- The reduced-stage exact line-search component extracted from a GPRN step. -/
theorem exactLineSearch
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℝ) (f s next : EuclideanSpace ℝ ι)
    (h : IsStep P J hessianMatrix σ τ f s next) :
    IsMinOn
      (LineSearch.profile (J ∘ P) (projectedStage P J σ f) s)
      (Set.Ioi (0 : ℝ))
      τ :=
  h.2.1

/-- The successor-update formula extracted from a GPRN step. -/
theorem next_eq
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℝ) (f s next : EuclideanSpace ℝ ι)
    (h : IsStep P J hessianMatrix σ τ f s next) :
    next = reducedNewtonUpdate P τ (projectedStage P J σ f) s :=
  h.2.2

end IsStep

/-- Specification theorem for the one-step GPRN relation `GPRN.IsStep`. -/
theorem isStep_iff
    [DecidableEq ι]
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℝ) (f s next : EuclideanSpace ℝ ι) :
    IsStep P J hessianMatrix σ τ f s next ↔
      IsReducedNewtonDirection J hessianMatrix (projectedStage P J σ f) s ∧
        IsMinOn
          (LineSearch.profile (J ∘ P) (projectedStage P J σ f) s)
          (Set.Ioi (0 : ℝ))
          τ ∧
        next = reducedNewtonUpdate P τ (projectedStage P J σ f) s := Iff.rfl

/-- The source-facing GPRN iterate-sequence owner is equivalent to combining
the backend reduced-direction and exact reduced-stage line-search predicates. -/
theorem isIterateSequence_iff
    [DecidableEq ι]
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι) :
    IsIterateSequence P J hessianMatrix σ τ f0 s ↔
      IsReducedDirectionSequence P J hessianMatrix σ τ f0 s ∧
        IsExactReducedLineSearch P J σ τ f0 s := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro v
      exact IsStep.direction P J hessianMatrix (σ v) (τ v)
        (iterates P J σ τ f0 s v) (s v) (iterates P J σ τ f0 s (v + 1)) (h v)
    · intro v
      exact IsStep.exactLineSearch P J hessianMatrix (σ v) (τ v)
        (iterates P J σ τ f0 s v) (s v) (iterates P J σ τ f0 s (v + 1)) (h v)
  · rintro ⟨hDirections, hLineSearch⟩ v
    refine ⟨hDirections v, hLineSearch v, ?_⟩
    exact iterates_succ_eq_reducedNewtonUpdate P J σ τ f0 s v

namespace IsIterateSequence

variable [DecidableEq ι]

/-- A GPRN iterate sequence has the source reduced-direction property at every
projected stage. -/
theorem isReducedDirectionSequence
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι)
    (h : IsIterateSequence P J hessianMatrix σ τ f0 s) :
    IsReducedDirectionSequence P J hessianMatrix σ τ f0 s :=
  (isIterateSequence_iff P J hessianMatrix σ τ f0 s).mp h |>.1

/-- A GPRN iterate sequence has the source exact reduced-stage line search at
every stage. -/
theorem isExactReducedLineSearch
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι)
    (h : IsIterateSequence P J hessianMatrix σ τ f0 s) :
    IsExactReducedLineSearch P J σ τ f0 s :=
  (isIterateSequence_iff P J hessianMatrix σ τ f0 s).mp h |>.2

end IsIterateSequence

/-- Specification lemma for the stagewise reduced-direction predicate. -/
theorem isReducedDirectionSequence_iff
    [DecidableEq ι]
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (hessianMatrix : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι) :
    IsReducedDirectionSequence P J hessianMatrix σ τ f0 s ↔
      ∀ v,
        IsReducedNewtonDirection J hessianMatrix
          (projectedStages P J σ τ f0 s v)
          (s v) := Iff.rfl

/-- Specification lemma for the reduced-stage exact line-search predicate. -/
theorem isExactReducedLineSearch_iff
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : EuclideanSpace ℝ ι → ℝ)
    (σ τ : ℕ → ℝ) (f0 : EuclideanSpace ℝ ι)
    (s : ℕ → EuclideanSpace ℝ ι) :
    IsExactReducedLineSearch P J σ τ f0 s ↔
      ∀ v,
        IsMinOn
          (LineSearch.profile (J ∘ P)
            (projectedStages P J σ τ f0 s v)
            (s v))
          (Set.Ioi (0 : ℝ))
          (τ v) := Iff.rfl

end GPRN
