/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_20.ReducedHessian
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8.FeasibleSet
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

noncomputable section

namespace ProjectedNewton

open scoped Matrix

variable {n : ℕ}

/-- The reduced-Newton direction `s_v` at the current iterate `f_v` uses the
reduced Hessian `NonnegativeOrthant.reducedHessian f_v (hessianMatrix f_v)` and
the gradient `gradient J f_v` whenever that reduced Hessian is nonsingular. -/
@[expose] def reducedNewtonDirection
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n))
    (hHR : IsUnit ((NonnegativeOrthant.reducedHessian f (hessianMatrix f)).det)) :
    EuclideanSpace ℝ (Fin n) :=
  let HR := NonnegativeOrthant.reducedHessian f (hessianMatrix f);
  -((((↑(hHR.unit⁻¹) : ℝ) • HR.adjugate).toEuclideanLin) (gradient J f))

/-- A single projected Newton update from `f_v` with step size `τ_v` and search
direction `s_v` is `P (f_v + τ_v • s_v)`. -/
@[expose] def update
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (τ : ℝ)
    (f s : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  P (f + τ • s)

/-- The projected Newton iterates generated from the nonnegative initial guess
`f₀`, the projected step-size sequence `τ`, and a supplied reduced-direction
sequence `s`. -/
@[expose] def iterates
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => f0
  | v + 1 => update P (τ v) (iterates P τ f0 s v) (s v)

/-- A vector `s_v` is a reduced-Newton direction at `f_v` when the reduced
Hessian there is nonsingular and `s_v` is given by the source formula
`-H_R(f_v)⁻¹ gradient J f_v`. -/
@[expose] def IsReducedNewtonDirection
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (f s : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ∃ hHR : IsUnit ((NonnegativeOrthant.reducedHessian f (hessianMatrix f)).det),
    s = reducedNewtonDirection J hessianMatrix f hHR

/-- The exact projected line-search condition for Algorithm 9.3.2: at each
iterate `v`, the step size `τ v` minimizes the projected objective profile
`LineSearch.profile (J ∘ P) (f_v) (s_v)` over `Set.Ioi (0 : ℝ)`. -/
@[expose] def IsExactLineSearch
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ∀ v,
    IsMinOn
      (LineSearch.profile (J ∘ P) (iterates P τ f0 s v) (s v))
      (Set.Ioi (0 : ℝ))
      (τ v)

/-- Algorithm 9.3.2. A single projected Newton step from `f_v` to `f_(v+1)`
uses a reduced-Newton direction `s_v` at `f_v`, an exact projected line search
`τ_v`, and the projected update formula for the successor iterate. -/
@[expose] def IsStep
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ)
    (f s next : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  IsReducedNewtonDirection J hessianMatrix f s ∧
    IsMinOn
      (LineSearch.profile (J ∘ P) f s)
      (Set.Ioi (0 : ℝ))
      τ ∧
    next = update P τ f s

/-- Algorithm 9.3.2. A stagewise reduced-direction sequence `s` is a projected
Newton iterate sequence for the canonical backend family
`ProjectedNewton.iterates P τ f0 s` when the initial guess `f₀` is feasible and
every successor satisfies the full projected Newton step relation. -/
@[expose] def IsIterateSequence
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n)) :
    Prop :=
  f0 ∈ NonnegativeOrthant.feasibleSet n ∧
    ∀ v,
      IsStep P J hessianMatrix (τ v)
        (iterates P τ f0 s v)
        (s v)
        (iterates P τ f0 s (v + 1))

/-- `reducedNewtonDirection` is the explicit reduced-Hessian formula
`-H_R(f_v)⁻¹ gradient J f_v` under a nonsingularity witness for `H_R(f_v)`. -/
@[simp] theorem reducedNewtonDirection_eq
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n))
    (hHR : IsUnit ((NonnegativeOrthant.reducedHessian f (hessianMatrix f)).det)) :
    reducedNewtonDirection J hessianMatrix f hHR =
      -((NonnegativeOrthant.reducedHessian f (hessianMatrix f))⁻¹).toEuclideanLin
        (gradient J f) := by
  -- Normalize the definition once so the nonsingular-inverse rewrite matches exactly.
  let HR := NonnegativeOrthant.reducedHessian f (hessianMatrix f)
  calc
    reducedNewtonDirection J hessianMatrix f hHR =
      -((((↑(hHR.unit⁻¹) : ℝ) • HR.adjugate).toEuclideanLin) (gradient J f)) := by
        rfl
    _ = -((HR⁻¹).toEuclideanLin (gradient J f)) := by
        rw [Matrix.nonsing_inv_apply HR hHR]

/-- The witness-built reduced-Newton direction satisfies
`ProjectedNewton.IsReducedNewtonDirection`. -/
theorem isReducedNewtonDirection_reducedNewtonDirection
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n))
    (hHR : IsUnit ((NonnegativeOrthant.reducedHessian f (hessianMatrix f)).det)) :
    IsReducedNewtonDirection J hessianMatrix f
      (reducedNewtonDirection J hessianMatrix f hHR) := by
  -- Package the defining witness and equation into the source-facing predicate.
  exact ⟨hHR, rfl⟩

/-- The projected Newton update is the projected affine step `P (f + τ • s)`. -/
@[simp] theorem update_eq
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (τ : ℝ)
    (f s : EuclideanSpace ℝ (Fin n)) :
    update P τ f s = P (f + τ • s) := by
  -- The backend update is defined as the projected affine step.
  rfl

/-- The zeroth projected Newton iterate is the initial guess `f₀`. -/
@[simp] theorem iterates_zero
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n)) :
    iterates P τ f0 s 0 = f0 := by
  -- The iterate recursion starts from the supplied initial guess.
  rfl

/-- The successor projected Newton iterate is obtained by one projected Newton
update from the current iterate with step size `τ v` and direction `s v`. -/
@[simp] theorem iterates_succ
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n))
    (v : ℕ) :
    iterates P τ f0 s (v + 1) =
      update P (τ v) (iterates P τ f0 s v) (s v) := by
  -- A successor iterate is one projected Newton update from the current iterate.
  rfl

namespace IsStep

/-- The reduced-Newton-direction component extracted from a projected Newton
step. -/
theorem direction
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ)
    (f s next : EuclideanSpace ℝ (Fin n))
    (h : IsStep P J hessianMatrix τ f s next) :
    IsReducedNewtonDirection J hessianMatrix f s := by
  -- The reduced-direction component is the first conjunct of `IsStep`.
  exact h.1

/-- The exact projected line-search component extracted from a projected Newton
step. -/
theorem exactLineSearch
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ)
    (f s next : EuclideanSpace ℝ (Fin n))
    (h : IsStep P J hessianMatrix τ f s next) :
    IsMinOn
      (LineSearch.profile (J ∘ P) f s)
      (Set.Ioi (0 : ℝ))
      τ := by
  -- The exact projected line-search condition is the second conjunct of `IsStep`.
  exact h.2.1

/-- The successor-update formula extracted from a projected Newton step. -/
theorem next_eq
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ)
    (f s next : EuclideanSpace ℝ (Fin n))
    (h : IsStep P J hessianMatrix τ f s next) :
    next = update P τ f s := by
  -- The stored successor formula is the final conjunct of `IsStep`.
  exact h.2.2

end IsStep

/-- Specification theorem for the one-step projected Newton relation
`ProjectedNewton.IsStep`. -/
theorem isStep_iff
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ)
    (f s next : EuclideanSpace ℝ (Fin n)) :
    IsStep P J hessianMatrix τ f s next ↔
      IsReducedNewtonDirection J hessianMatrix f s ∧
        IsMinOn
          (LineSearch.profile (J ∘ P) f s)
          (Set.Ioi (0 : ℝ))
          τ ∧
        next = update P τ f s := by
  -- The one-step relation is defined by this conjunction.
  rfl

/-- Specification theorem for the backend projected line-search predicate. -/
theorem isExactLineSearch_iff
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n)) :
    IsExactLineSearch P J τ f0 s ↔
      ∀ v,
        IsMinOn
          (LineSearch.profile (J ∘ P) (iterates P τ f0 s v) (s v))
          (Set.Ioi (0 : ℝ))
          (τ v) := by
  -- The backend exact line-search predicate is already this stagewise condition.
  rfl

/-- The source-facing iterate-sequence owner is equivalent to combining the
initial feasibility condition with the backend pointwise step relation. -/
theorem isIterateSequence_iff
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n)) :
    IsIterateSequence P J hessianMatrix τ f0 s ↔
      f0 ∈ NonnegativeOrthant.feasibleSet n ∧
        ∀ v,
          IsStep P J hessianMatrix (τ v)
            (iterates P τ f0 s v)
            (s v)
            (iterates P τ f0 s (v + 1)) := by
  -- The iterate-sequence owner is defined by feasibility plus stagewise steps.
  rfl

namespace IsIterateSequence

/-- A projected Newton iterate sequence starts from a feasible initial guess in
`NonnegativeOrthant.feasibleSet n`. -/
theorem feasible
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n))
    (h : IsIterateSequence P J hessianMatrix τ f0 s) :
    f0 ∈ NonnegativeOrthant.feasibleSet n := by
  -- Read the initial-feasibility component from the iterate-sequence specification.
  exact (isIterateSequence_iff P J hessianMatrix τ f0 s).mp h |>.1

/-- Every stage of a projected Newton iterate sequence satisfies the source
one-step projected Newton relation. -/
theorem step
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n))
    (h : IsIterateSequence P J hessianMatrix τ f0 s) :
    ∀ v,
      IsStep P J hessianMatrix (τ v)
        (iterates P τ f0 s v)
        (s v)
        (iterates P τ f0 s (v + 1)) := by
  -- Read the stagewise step relation from the iterate-sequence specification.
  exact (isIterateSequence_iff P J hessianMatrix τ f0 s).mp h |>.2

/-- A projected Newton iterate sequence has the exact projected line-search
property at every stage. -/
theorem exactLineSearch
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n))
    (h : IsIterateSequence P J hessianMatrix τ f0 s) :
    IsExactLineSearch P J τ f0 s := by
  -- Unfold the stagewise line-search predicate and prove it one index at a time.
  intro v
  -- Each iterate-sequence stage is a projected Newton step, so its line search is exact.
  exact IsStep.exactLineSearch P J hessianMatrix (τ v)
    (iterates P τ f0 s v) (s v) (iterates P τ f0 s (v + 1))
    (step P J hessianMatrix τ f0 s h v)

end IsIterateSequence

end ProjectedNewton
