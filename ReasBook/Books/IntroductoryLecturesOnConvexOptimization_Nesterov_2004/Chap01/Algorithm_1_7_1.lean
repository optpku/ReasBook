/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap

noncomputable section

universe u

section System

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Layer targeted by this refinement:
* source-facing: `NewtonSystem.Method`, together with the recursive orbit `NewtonSystem.orbit`
  under the natural step-preservation hypothesis
* core/canonical: the admissible domain `NewtonSystem.AdmissiblePoint` together with the owner
  step `NewtonSystem.step`
* bridge/view: the scalar specialization `NewtonSystem.step_scalar_def`

Primary domain:
* finite-dimensional Newton methods for nonlinear systems built from the Fréchet derivative

Sampled owner-style declarations:
* `fderiv ℝ F x`
* `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero`
* `Function.iterate`
* `DampedNewton.Method`
* `newtonIterate`

Owner abstraction:
* the Newton admissible domain `NewtonSystem.AdmissiblePoint F`, with the owner step
  `NewtonSystem.step` as core data and the Newton trajectory/method interface derived from it

Primitive data:
* for a single update: a map `F : E → E` and an admissible point
  `x : NewtonSystem.AdmissiblePoint F`
* for a source-facing Newton method: an admissible-point trajectory satisfying the Newton
  recursion

Derived API:
* under preservation of admissibility by the Newton step, the canonical recursive orbit
  `NewtonSystem.orbit`
* the scalar Newton formula as a one-dimensional bridge, not primitive data
-/

namespace NewtonSystem

/-- Points where the Jacobian of `F` is nonsingular. -/
abbrev AdmissiblePoint (F : E → E) :=
  {x : E // (fderiv ℝ F x).det ≠ 0}

/-- The Newton update at an admissible point. -/
def step (F : E → E) (x : AdmissiblePoint F) : E :=
  (x : E) - (((fderiv ℝ F (x : E)).toContinuousLinearEquivOfDetNeZero x.property).symm (F x))

/-- Expanding `step F x` recovers the inverse-Jacobian correction
`x₊ = x - [F'(x)]⁻¹ F(x)`. -/
theorem step_def (F : E → E) (x : AdmissiblePoint F) :
    step F x =
      (x : E) - (((fderiv ℝ F (x : E)).toContinuousLinearEquivOfDetNeZero x.property).symm
        (F x)) :=
  rfl

/-- The admissible Newton domain is preserved by taking one Newton step. This is the extra
well-definedness hypothesis needed to build the canonical recursive orbit. -/
def StepPreservesAdmissibility (F : E → E) : Prop :=
  ∀ x : AdmissiblePoint F, (fderiv ℝ F (step F x)).det ≠ 0

private def stepMap (F : E → E) (hstep : StepPreservesAdmissibility F) :
    AdmissiblePoint F → AdmissiblePoint F :=
  fun x ↦ ⟨step F x, hstep x⟩

/-- Algorithm 1.7.1: a Newton method for the nonlinear system `F(x) = 0` started at `x₀` is a
trajectory of admissible points whose successive iterates are obtained from the Newton update.
The Jacobian nondegeneracy at each iterate is part of the data because the textbook algorithm
assumes the Newton correction remains well defined along the orbit. -/
structure Method (F : E → E) (x0 : E) where
  /-- The Newton iterates, valued in the natural admissible domain. -/
  x : ℕ → AdmissiblePoint F
  /-- The zeroth iterate is the prescribed initial point `x₀`. -/
  x_zero : (x 0 : E) = x0
  /-- The Newton iterates satisfy the recursive update rule. -/
  step_eq : ∀ k : ℕ, (x (k + 1) : E) = step F (x k)

namespace Method

/-- A Newton method can be used as its underlying trajectory of iterates. -/
instance {F : E → E} {x0 : E} :
    CoeFun (Method F x0) (fun _ ↦ ℕ → E) where
  coe method := fun k ↦ method.x k

/-- The Jacobian of `F` is nonsingular at every iterate of a Newton method. -/
theorem jacobian_nondegenerate
    {F : E → E} {x0 : E} (method : Method F x0) (k : ℕ) :
    (fderiv ℝ F (method k)).det ≠ 0 :=
  (method.x k).property

/-- Every Newton method starts from its prescribed initial point. -/
@[simp] theorem zero_eq
    {F : E → E} {x0 : E} (method : Method F x0) :
    method 0 = x0 :=
  method.x_zero

/-- Each iterate of a Newton method is the Newton update of the previous iterate. -/
theorem succ_eq
    {F : E → E} {x0 : E} (method : Method F x0) (k : ℕ) :
    method (k + 1) = step F (method.x k) := by
  simpa using method.step_eq k

/-- The tail of a Newton method started at iterate `k` is again a Newton method, now with initial
point `method k`. -/
def tail {F : E → E} {x0 : E} (method : Method F x0) (k : ℕ) :
    Method F (method k) where
  x j := method.x (j + k)
  x_zero := by simp
  step_eq j := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using method.step_eq (j + k)

/-- Evaluating the Newton tail at index `j` recovers the original orbit at index `j + k`. -/
@[simp] theorem tail_apply
    {F : E → E} {x0 : E} (method : Method F x0) (k j : ℕ) :
    method.tail k j = method (j + k) :=
  rfl

end Method

/-- The canonical recursive Newton orbit on the admissible domain, defined when admissibility is
preserved by one Newton step. -/
def orbitPoint (F : E → E) (x0 : AdmissiblePoint F)
    (hstep : StepPreservesAdmissibility F) : ℕ → AdmissiblePoint F :=
  fun k ↦ (stepMap F hstep)^[k] x0

/-- The underlying trajectory in `E` of the canonical recursive Newton orbit. -/
def orbit (F : E → E) (x0 : AdmissiblePoint F)
    (hstep : StepPreservesAdmissibility F) : ℕ → E :=
  fun k ↦ orbitPoint F x0 hstep k

/-- The zeroth point of the canonical Newton orbit is the initial point. -/
@[simp] theorem orbit_zero (F : E → E) (x0 : AdmissiblePoint F)
    (hstep : StepPreservesAdmissibility F) :
    orbit F x0 hstep 0 = x0 :=
  rfl

/-- The Jacobian of `F` is nonsingular at every point of the canonical Newton orbit. -/
theorem orbit_jacobian_nondegenerate (F : E → E) (x0 : AdmissiblePoint F)
    (hstep : StepPreservesAdmissibility F) (k : ℕ) :
    (fderiv ℝ F (orbit F x0 hstep k)).det ≠ 0 :=
  (orbitPoint F x0 hstep k).property

/-- The canonical Newton orbit satisfies the recursive Newton update rule. -/
theorem orbit_succ (F : E → E) (x0 : AdmissiblePoint F)
    (hstep : StepPreservesAdmissibility F) (k : ℕ) :
    orbit F x0 hstep (k + 1) =
      step F (orbitPoint F x0 hstep k) := by
  have hiter :=
    congrArg (fun y : AdmissiblePoint F ↦ (y : E))
      (Function.iterate_succ_apply' (stepMap F hstep) k x0)
  simpa [orbit, orbitPoint, stepMap] using hiter

end NewtonSystem

end System

/-- For scalar maps, a nonzero derivative makes the Fréchet derivative invertible. -/
theorem fderiv_det_ne_zero_of_deriv_ne_zero {φ : ℝ → ℝ} {t : ℝ}
    (hφ' : deriv φ t ≠ 0) :
    (fderiv ℝ φ t).det ≠ 0 := by
  simpa [det_toSpanSingleton, ← toSpanSingleton_deriv] using hφ'

private theorem toSpanSingleton_symm_apply_eq_div (a b : ℝ) (ha : a ≠ 0) :
    ((toSpanSingleton ℝ a).toContinuousLinearEquivOfDetNeZero
      (by simpa [det_toSpanSingleton] using ha)).symm b = b / a := by
  let e := (toSpanSingleton ℝ a).toContinuousLinearEquivOfDetNeZero
    (by simpa [det_toSpanSingleton] using ha)
  apply e.injective
  simp [e, div_eq_mul_inv, ha]

namespace NewtonSystem

/-- Scalar specialization of Algorithm 1.7.1: if `φ'(t) ≠ 0`, then the system Newton step is the
textbook scalar Newton update `t₊ = t - φ(t) / φ'(t)`. -/
theorem step_scalar_def (φ : ℝ → ℝ) (t : ℝ) (hφ' : deriv φ t ≠ 0) :
    step φ ⟨t, fderiv_det_ne_zero_of_deriv_ne_zero hφ'⟩ = t - φ t / deriv φ t := by
  rw [step]
  simp only [toSpanSingleton_deriv.symm]
  rw [toSpanSingleton_symm_apply_eq_div _ _ hφ']

end NewtonSystem

/-
Algorithm 1.7.1 (optimization specialization): after adding an inner product so that gradients are
available, Newton's update for unconstrained minimization is the system Newton step applied to the
stationarity equation `∇ f(x) = 0`.
-/
end
