/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_2.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_15.Projector

public section

/-!
Algorithm 9.3.2. Projected Newton Method.

This item exposes Algorithm 9.3.2 on the nonnegative orthant through the
source-facing specialization namespace `Algorithm932`, whose public owners
`Algorithm932.IsStep` and `Algorithm932.IsIterateSequence` are thin bridges to
the reusable backend owners `ProjectedNewton.IsStep` and
`ProjectedNewton.IsIterateSequence` at the canonical orthant projector
`NonnegativeOrthant.projector n`. The foundation module
`Book.Ch9.Algorithm_9_3_2.Iterates` also keeps the explicit reduced-Hessian
direction `ProjectedNewton.reducedNewtonDirection`, the projected update
`ProjectedNewton.update`, the backend iterate family `ProjectedNewton.iterates`,
and the extracted line-search predicate `ProjectedNewton.IsExactLineSearch`
available as companion API. The active set `ActiveSet.active`, the reduced
Hessian `NonnegativeOrthant.reducedHessian`, the feasible set
`NonnegativeOrthant.feasibleSet`, and the projected line-search profile
`LineSearch.profile` are reused directly from existing Chapter 9 owners.
-/

namespace Algorithm932

/-- Algorithm 9.3.2. A single projected Newton step on the nonnegative orthant
specializes the backend `ProjectedNewton.IsStep` owner to the canonical
projector `NonnegativeOrthant.projector n`. -/
abbrev IsStep
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ)
    (f s next : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ProjectedNewton.IsStep (NonnegativeOrthant.projector n) J hessianMatrix τ f s next

/-- `Algorithm932.IsStep` is exactly the orthant-specialized backend projected
Newton step relation. -/
theorem isStep_iff
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ)
    (f s next : EuclideanSpace ℝ (Fin n)) :
    IsStep n J hessianMatrix τ f s next ↔
      ProjectedNewton.IsStep
        (NonnegativeOrthant.projector n) J hessianMatrix τ f s next :=
  Iff.rfl

/-- Algorithm 9.3.2. A projected Newton trajectory on the nonnegative orthant
specializes the backend `ProjectedNewton.IsIterateSequence` owner to the
canonical projector `NonnegativeOrthant.projector n`. -/
abbrev IsIterateSequence
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ProjectedNewton.IsIterateSequence
    (NonnegativeOrthant.projector n) J hessianMatrix τ f0 s

/-- `Algorithm932.IsIterateSequence` is exactly the orthant-specialized backend
projected Newton iterate-sequence predicate. -/
theorem isIterateSequence_iff
    (n : ℕ)
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (hessianMatrix :
      EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℕ → ℝ)
    (f0 : EuclideanSpace ℝ (Fin n))
    (s : ℕ → EuclideanSpace ℝ (Fin n)) :
    IsIterateSequence n J hessianMatrix τ f0 s ↔
      ProjectedNewton.IsIterateSequence
        (NonnegativeOrthant.projector n) J hessianMatrix τ f0 s :=
  Iff.rfl

end Algorithm932

/-
Algorithm 9.3.2.

The source-facing projected Newton method on the nonnegative orthant is exposed
through the specialized step and iterate-sequence owners
`Algorithm932.IsStep` and `Algorithm932.IsIterateSequence`.
-/
#check Algorithm932.IsStep
#check Algorithm932.IsIterateSequence

/-
Backend companion checks for the reusable generic owners behind
Algorithm 9.3.2.
-/
#check ProjectedNewton.IsStep
#check ProjectedNewton.IsIterateSequence
#check ProjectedNewton.reducedNewtonDirection
#check ProjectedNewton.IsExactLineSearch
#check ProjectedNewton.update
#check ProjectedNewton.iterates

/-
Backend anchor checks for the active set `𝒜_v`, the reduced Hessian `H_R(f_v)`,
the nonnegative feasible set, the projected line-search profile, and the
ambient gradient owner reused by the projected Newton formalization.
-/
#check ActiveSet.active
#check NonnegativeOrthant.reducedHessian
#check NonnegativeOrthant.feasibleSet
#check LineSearch.profile
#check gradient
