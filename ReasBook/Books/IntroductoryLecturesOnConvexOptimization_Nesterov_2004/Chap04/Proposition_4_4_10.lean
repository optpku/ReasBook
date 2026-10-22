/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Proposition 4.4.10 lies in the modified-Newton / quadratic-entry domain.

Sampled owner declarations:
* `DampedNewton.Method` in `Algorithm_4_1_2`, the ambient chapter owner for damped Newton
  trajectories;
* `ModifiedNewtonMethod` in this file, the source-facing globalized damped-Newton owner used by
  Proposition 4.4.10;
* `HasQuadraticConvergenceFrom` in `Text_4_2_24`, the chapter owner for quadratic tail
  convergence from a given index;
* `StrongConvexOn.eq_of_isMinOn` in `Chap03/Corollary_3_2_3`, the canonical uniqueness owner for
  a strongly convex minimizer;
* `HasLipschitzContinuousHessian`, written on theorem surfaces as `φ ∈ C22[L]`, in
  `Definition_4_2_7`, the chapter owner for the Hessian-Lipschitz hypothesis.
* semantic recall: `lean_leansearch` found no relevant analogue beyond generic Newton maps, so
  the local precedent is `Algorithm_4_1_2` on `DampedNewton.Method` together with
  `Text_4_2_24` on `HasQuadraticConvergenceFrom`.

Best owner abstraction:
* source-facing: the scalar characteristic quantity `ξ = L ‖x₀ - x*‖ / σ`, the modified-Newton
  orbit owner `method : ModifiedNewtonMethod φ x0`, and the first quadratic-region-entry
  index bound from the textbook proposition;
* core/canonical: `StrongConvexOn Set.univ σ φ`, `φ ∈ C22[L]`,
  the region-entry predicate `InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k`, and
  the tail predicate `HasQuadraticConvergenceFrom method xStar k` for the same modified-Newton
  orbit;
* bridge/view: `modifiedNewtonQuadraticConvergenceRegion σ L xStar`, the iterate-entry predicate
  `InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k`, and the exact-line-search
  globalization owner `SatisfiesExactLineSearchAlong` along the Newton directions of the damped
  orbit.

Primitive data:
* the objective `φ`, the strong-convexity modulus `σ`, the Hessian-Lipschitz constant `L`, the
  minimizer `xStar`, the source initial point `x0`, and the associated modified-Newton orbit
  `method`.

Derived API:
* the least quadratic-entry index package
  `IsLeast {k : ℕ | InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k} N1`;
* the source-facing pointwise region cut out by the local condition
  `modifiedNewtonCharacteristicQuantity σ L x xStar < 1`.
-/

/-- The characteristic quantity `ξ = L ‖x₀ - x*‖ / σ` attached to the modified Newton
convergence estimate. -/
def modifiedNewtonCharacteristicQuantity
    (σ : ℝ) (L : NNReal) (x0 xStar : E) : ℝ :=
  (L : ℝ) * ‖x0 - xStar‖ / σ

-- Proof sketch: unfold `modifiedNewtonCharacteristicQuantity`.
/-- Expanding `modifiedNewtonCharacteristicQuantity σ L x₀ x*` gives the textbook formula
`ξ = L ‖x₀ - x*‖ / σ`. -/
@[simp] theorem modifiedNewtonCharacteristicQuantity_def
    (σ : ℝ) (L : NNReal) (x0 xStar : E) :
    modifiedNewtonCharacteristicQuantity σ L x0 xStar =
      (L : ℝ) * ‖x0 - xStar‖ / σ :=
  rfl

/-- The local quadratic-convergence region for the modified Newton estimate consists of the points
`x` for which the characteristic quantity relative to `xStar` is strictly smaller than `1`. -/
def modifiedNewtonQuadraticConvergenceRegion
    (σ : ℝ) (L : NNReal) (xStar : E) : Set E :=
  {x | modifiedNewtonCharacteristicQuantity σ L x xStar < 1}

-- Proof sketch: unfold `modifiedNewtonQuadraticConvergenceRegion`.
/-- Membership in `modifiedNewtonQuadraticConvergenceRegion σ L xStar` is exactly the local
inequality `L ‖x - x*‖ / σ < 1`. -/
@[simp] theorem mem_modifiedNewtonQuadraticConvergenceRegion_iff
    (σ : ℝ) (L : NNReal) (xStar x : E) :
    x ∈ modifiedNewtonQuadraticConvergenceRegion σ L xStar ↔
      modifiedNewtonCharacteristicQuantity σ L x xStar < 1 :=
  Iff.rfl

section

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A full Newton orbit for `∇ φ` is the unit-step special case of the chapter's modified Newton
iteration owner `DampedNewton.Method φ x0`. This bridge preserves the iterate sequence and equips
it with the constant unit step-size schedule. -/
def NewtonSystem.Method.toDampedNewtonMethod
    {φ : E → ℝ} {x0 : E} (method : NewtonSystem.Method (∇ φ) x0) :
    DampedNewton.Method φ x0 where
  x := method.x
  x_zero := method.x_zero
  stepSize := fun _ ↦ 1
  stepSize_pos := fun _ ↦ by norm_num
  step_eq := fun k ↦ by
    rw [method.step_eq k, DampedNewton.step_def, NewtonSystem.step_def, one_smul]

/-- The unit-step damped-Newton bridge does not change the underlying iterate sequence. -/
@[simp] theorem NewtonSystem.Method.toDampedNewtonMethod_apply
    {φ : E → ℝ} {x0 : E} (method : NewtonSystem.Method (∇ φ) x0) (k : ℕ) :
    method.toDampedNewtonMethod k = method k :=
  rfl

instance {φ : E → ℝ} {x0 : E} :
    Coe (NewtonSystem.Method (∇ φ) x0) (DampedNewton.Method φ x0) where
  coe := NewtonSystem.Method.toDampedNewtonMethod

/-- The Newton search direction carried by a damped Newton orbit. -/
def DampedNewton.Method.searchDirection
    {φ : E → ℝ} {x0 : E} (method : DampedNewton.Method φ x0) (k : ℕ) : E :=
  (((fderiv ℝ (∇ φ) (method.x k : E)).toContinuousLinearEquivOfDetNeZero
      (method.x k).property).symm (∇ φ (method k)))

/-- Expanding the damped Newton recursion shows
`x_(k+1) = x_k - h_k d_k`, where `d_k` is the Newton search direction. -/
theorem DampedNewton.Method.succ_eq_sub_stepSize_smul_searchDirection
    {φ : E → ℝ} {x0 : E} (method : DampedNewton.Method φ x0) (k : ℕ) :
    method (k + 1) = method k - method.stepSize k • method.searchDirection k := by
  simpa [DampedNewton.Method.searchDirection, DampedNewton.step_def] using method.step_eq k

/-- The modified Newton iteration used in Proposition 4.4.10 packages a damped Newton orbit
together with the exact line-search globalization along its Newton directions. -/
structure ModifiedNewtonMethod (φ : E → ℝ) (x0 : E) where
  /-- The underlying damped Newton orbit. -/
  toMethod : DampedNewton.Method φ x0
  /-- Each damping factor is chosen by exact line search along the Newton direction. -/
  exactLineSearch :
    SatisfiesExactLineSearchAlong φ toMethod toMethod.searchDirection toMethod.stepSize

namespace ModifiedNewtonMethod

instance {φ : E → ℝ} {x0 : E} :
    Coe (ModifiedNewtonMethod φ x0) (DampedNewton.Method φ x0) where
  coe := ModifiedNewtonMethod.toMethod

instance {φ : E → ℝ} {x0 : E} :
    CoeFun (ModifiedNewtonMethod φ x0) (fun _ ↦ ℕ → E) where
  coe method := method.toMethod

/-- A modified Newton method inherits the exact line-search globalization of its damped orbit. -/
theorem exactLineSearchAlong
    {φ : E → ℝ} {x0 : E} (method : ModifiedNewtonMethod φ x0) (k : ℕ) :
    IsMinOn
      (fun h : ℝ ↦ φ (method k - h • method.toMethod.searchDirection k))
      (Set.Ici (0 : ℝ))
      (method.toMethod.stepSize k) :=
  method.exactLineSearch.isMinOn k

/-- Every step size of a modified Newton method is nonnegative by exact line search. -/
theorem stepSize_nonneg
    {φ : E → ℝ} {x0 : E} (method : ModifiedNewtonMethod φ x0) (k : ℕ) :
    method.toMethod.stepSize k ∈ Set.Ici (0 : ℝ) :=
  method.exactLineSearch.nonneg k

/-- The damped Newton recursion of a modified Newton method is the textbook update
`x_(k+1) = x_k - h_k d_k`. -/
theorem succ_eq_sub_stepSize_smul_searchDirection
    {φ : E → ℝ} {x0 : E} (method : ModifiedNewtonMethod φ x0) (k : ℕ) :
    method (k + 1) = method k - method.toMethod.stepSize k • method.toMethod.searchDirection k :=
  method.toMethod.succ_eq_sub_stepSize_smul_searchDirection k

end ModifiedNewtonMethod

/-- `InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k` means that the `k`th iterate
of the source modified-Newton sequence lies in the local quadratic-convergence region. -/
def InModifiedNewtonQuadraticConvergenceRegion
    (method : ℕ → E) (σ : ℝ) (L : NNReal) (xStar : E) (k : ℕ) : Prop :=
  method k ∈ modifiedNewtonQuadraticConvergenceRegion σ L xStar

-- Proof sketch: unfold `InModifiedNewtonQuadraticConvergenceRegion`.
/-- Expanding `InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k` says exactly that the
`k`th iterate satisfies the local condition `L ‖x_k - x*‖ / σ < 1`. -/
@[simp] theorem inModifiedNewtonQuadraticConvergenceRegion_iff
    (method : ℕ → E) (σ : ℝ) (L : NNReal) (xStar : E) (k : ℕ) :
    InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k ↔
      modifiedNewtonCharacteristicQuantity σ L (method k) xStar < 1 :=
  Iff.rfl

/-- Helper for Proposition 4.4.10: whole-space `σ`-strong convexity forces each Hessian to
expand norms by at least `σ`. -/
private lemma hessianApplyNormGeSigmaMulNorm
    {φ : E → ℝ} {σ : ℝ}
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hσ : 0 < σ)
    (hφ_C2 : ContDiff ℝ 2 φ)
    (x u : E) :
    σ * ‖u‖ ≤ ‖(fderiv ℝ (∇ φ) x) u‖ := by
  have hUniv_nonempty : (interior (Set.univ : Set E)).Nonempty := by
    simp
  have hcont : ContinuousOn φ (Set.univ : Set E) := hφ_C2.continuous.continuousOn
  have hC2 : ContDiffOn ℝ 2 φ (interior (Set.univ : Set E)) := by
    simpa using hφ_C2.contDiffOn
  have hbound : σ • (1 : E →L[ℝ] E) ≤ hessian φ x := by
    -- Specialize the global strong-convexity owner to the whole-space Hessian lower bound.
    have hiff :=
      (strongConvexOn_iff_hessian_lower_bound
        hσ convex_univ hUniv_nonempty hcont hC2).1 hφ_strong
    simpa using hiff x (by simp)
  have hquad :
      σ * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ (hessian φ x u) u := by
    -- Convert the Loewner lower bound into the quadratic-form inequality needed for Cauchy.
    exact
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hσ hC2 (by simp : x ∈ interior (Set.univ : Set E))).1 hbound u
  by_cases hu : u = 0
  · -- The zero vector saturates the lower bound.
    simp [hu]
  · -- Cauchy-Schwarz bounds the quadratic form by the operator output norm times `‖u‖`.
    have hinner_le : inner ℝ (hessian φ x u) u ≤ ‖hessian φ x u‖ * ‖u‖ := by
      exact le_trans (le_abs_self _) <| by
        simpa [real_inner_comm] using abs_real_inner_le_norm (hessian φ x u) u
    have hmul : σ * ‖u‖ ^ (2 : ℕ) ≤ ‖hessian φ x u‖ * ‖u‖ := le_trans hquad hinner_le
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hmul' : σ * ‖u‖ * ‖u‖ ≤ ‖hessian φ x u‖ * ‖u‖ := by
      simpa [pow_two, mul_assoc] using hmul
    have hdiv := (mul_le_mul_iff_of_pos_right hu_norm_pos).mp hmul'
    simpa [hessian] using hdiv

/-- Helper for Proposition 4.4.10: the inverse Hessian at an admissible Newton point is
globally bounded by `σ⁻¹` under whole-space `σ`-strong convexity. -/
private lemma inverseFDerivGradientApplyLeInvSigma
    {φ : E → ℝ} {σ : ℝ}
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hσ : 0 < σ)
    (hφ_C2 : ContDiff ℝ 2 φ)
    (p : NewtonSystem.AdmissiblePoint (∇ φ))
    (v : E) :
    ‖(((fderiv ℝ (∇ φ) (p : E)).toContinuousLinearEquivOfDetNeZero p.property).symm v)‖ ≤
      (1 / σ) * ‖v‖ := by
  let u :=
    (((fderiv ℝ (∇ φ) (p : E)).toContinuousLinearEquivOfDetNeZero p.property).symm v)
  have hbound :
      σ * ‖u‖ ≤ ‖(fderiv ℝ (∇ φ) (p : E)) u‖ :=
    hessianApplyNormGeSigmaMulNorm hφ_strong hσ hφ_C2 (p : E) u
  have happly :
      (fderiv ℝ (∇ φ) (p : E)) u = v := by
    -- Apply the inverse-Jacobian bridge at the admissible point `p`.
    exact
      (fderiv ℝ (∇ φ) (p : E)).toContinuousLinearEquivOfDetNeZero p.property
        |>.apply_symm_apply v
  have hdiv : ‖u‖ ≤ ‖v‖ / σ := by
    -- Move the strong-convexity factor `σ` to the right-hand side.
    refine (le_div_iff₀ hσ).2 ?_
    simpa [u, happly, mul_comm, mul_left_comm, mul_assoc] using hbound
  simpa [u, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Helper for Proposition 4.4.10: one modified Newton step satisfies the quadratic position-error
bound at the constants `σ` and `L`. -/
private lemma modifiedNewtonStepErrorLeQuadratic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (p : NewtonSystem.AdmissiblePoint (∇ φ)) :
    ‖NewtonSystem.step (∇ φ) p - xStar‖ ≤
      ((L : ℝ) / (2 * σ)) * ‖(p : E) - xStar‖ ^ (2 : ℕ) := by
  let A : E →L[ℝ] E := hessian φ (p : E)
  let Ainv : E →L[ℝ] E :=
    (((fderiv ℝ (∇ φ) (p : E)).toContinuousLinearEquivOfDetNeZero p.property).symm :
      E →L[ℝ] E)
  let e : E := (p : E) - xStar
  have hφ_C2 : ContDiff ℝ 2 φ := hφ_hessian.contDiff
  have hgrad0 : ∇ φ xStar = 0 := by
    -- Any differentiable global minimizer is stationary.
    exact isMinOn_gradient_eq_zero hxStar
  have hstep_eq :
      NewtonSystem.step (∇ φ) p - xStar = Ainv (A e - ∇ φ (p : E)) := by
    -- Rewrite the Newton correction as inverse Hessian applied to the Taylor remainder.
    calc
      NewtonSystem.step (∇ φ) p - xStar = ((p : E) - Ainv (∇ φ (p : E))) - xStar := by
        simp [NewtonSystem.step_def, Ainv]
      _ = e - Ainv (∇ φ (p : E)) := by
        simp [e, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = Ainv (A e) - Ainv (∇ φ (p : E)) := by
        rw [show Ainv (A e) = e by
          simpa [A, Ainv, hessian] using
            (ContinuousLinearEquiv.symm_apply_apply
              ((fderiv ℝ (∇ φ) (p : E)).toContinuousLinearEquivOfDetNeZero p.property) e)]
      _ = Ainv (A e - ∇ φ (p : E)) := by
        simp
  have hremainder_raw :
      ‖A e - ∇ φ (p : E)‖ ≤ ((L : ℝ) / 2) * ‖xStar - (p : E)‖ ^ (2 : ℕ) := by
    -- The Hessian-Lipschitz Taylor remainder controls the gradient linearization defect.
    simpa [A, e, hgrad0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (HasLipschitzContinuousHessian.gradient_deviation_le hφ_hessian (p : E) xStar)
  have hremainder :
      ‖A e - ∇ φ (p : E)‖ ≤ ((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ) := by
    calc
      ‖A e - ∇ φ (p : E)‖ ≤ ((L : ℝ) / 2) * ‖xStar - (p : E)‖ ^ (2 : ℕ) :=
        hremainder_raw
      _ = ((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ) := by
        rw [norm_sub_rev]
  have hAinv :
      ∀ v : E, ‖Ainv v‖ ≤ (1 / σ) * ‖v‖ := by
    intro v
    -- The Hessian lower bound gives a uniform inverse-operator estimate.
    simpa [Ainv] using
      inverseFDerivGradientApplyLeInvSigma hφ_strong hσ hφ_C2 p v
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  calc
    ‖NewtonSystem.step (∇ φ) p - xStar‖ = ‖Ainv (A e - ∇ φ (p : E))‖ := by
      rw [hstep_eq]
    _ ≤ (1 / σ) * ‖A e - ∇ φ (p : E)‖ := hAinv _
    _ ≤ (1 / σ) * (((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ)) := by
      gcongr
    _ = ((L : ℝ) / (2 * σ)) * ‖e‖ ^ (2 : ℕ) := by
      field_simp [hσ_ne]
    _ = ((L : ℝ) / (2 * σ)) * ‖(p : E) - xStar‖ ^ (2 : ℕ) := by
      simp [e]

/-- Helper for Proposition 4.4.10: shifting a quadratic-convergence tail back to the original
modified-Newton orbit preserves `HasQuadraticConvergenceFrom`. -/
private theorem hasQuadraticConvergenceFrom_of_tailSeq
    {x : ℕ → E} {xStar : E} {k : ℕ}
    (h : HasQuadraticConvergenceFrom (fun j ↦ x (k + j)) xStar 0) :
    HasQuadraticConvergenceFrom x xStar k := by
  rcases h with ⟨c, hc, htendsto, hbound⟩
  refine ⟨c, hc, ?_, ⟨Nat.zero_le k, ?_⟩⟩
  · -- Shifting the sequence by `k` does not change its limit.
    have htendsto' : Filter.Tendsto (fun j ↦ x (j + k)) Filter.atTop (nhds xStar) := by
      simpa [Nat.add_comm] using htendsto
    simpa using (Filter.tendsto_add_atTop_iff_nat k).1 htendsto'
  · -- Rewrite the shifted quadratic recurrence at an arbitrary index `j ≥ k`.
    intro j hj
    rcases Nat.exists_eq_add_of_le hj with ⟨n, rfl⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.sub_zero] using
      hbound.bound (Nat.zero_le n)

/-- Helper for Proposition 4.4.10: exact line search compares the accepted modified-Newton step
with the full Newton trial at parameter `1`. -/
private lemma modifiedNewtonObjective_le_fullTrial
    {φ : E → ℝ} {x0 : E}
    (method : ModifiedNewtonMethod φ x0) (k : ℕ) :
    φ (method (k + 1)) ≤ φ (NewtonSystem.step (∇ φ) (method.toMethod.x k)) := by
  -- The accepted step minimizes the one-variable search objective over all `h ≥ 0`, so it is no
  -- worse than the full Newton trial `h = 1`.
  have hmin := method.exactLineSearchAlong k
  rw [isMinOn_iff] at hmin
  have htrial_mem : (1 : ℝ) ∈ Set.Ici (0 : ℝ) := by
    simp
  simpa [ModifiedNewtonMethod.succ_eq_sub_stepSize_smul_searchDirection,
    DampedNewton.Method.searchDirection, NewtonSystem.step_def, one_smul] using
    hmin 1 htrial_mem

/-- Helper for Proposition 4.4.10: exact line search compares the accepted modified-Newton step
with every nonnegative point on the Newton ray, in particular with each `α ∈ [0, 1]`. -/
private lemma modifiedNewtonObjectiveSucc_le_alphaRayComparison
    {φ : E → ℝ} {x0 : E}
    (method : ModifiedNewtonMethod φ x0) (k : ℕ) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    φ (method (k + 1)) ≤ φ (method k - α • method.toMethod.searchDirection k) := by
  -- Exact line search minimizes the objective over the whole nonnegative Newton ray.
  have hmin := method.exactLineSearchAlong k
  rw [isMinOn_iff] at hmin
  simpa [ModifiedNewtonMethod.succ_eq_sub_stepSize_smul_searchDirection] using hmin α hα.1

/-- Helper for Proposition 4.4.10: exact line search makes the modified-Newton objective values
stepwise nonincreasing. -/
private lemma modifiedNewtonObjective_nonincreasing
    {φ : E → ℝ} {x0 : E}
    (method : ModifiedNewtonMethod φ x0) (k : ℕ) :
    φ (method (k + 1)) ≤ φ (method k) := by
  -- Compare the accepted step with the trivial Newton-ray parameter `α = 0`.
  let α : ℝ := 0
  have hα : α ∈ Set.Icc (0 : ℝ) 1 := by
    simp [α]
  simpa [α] using
    modifiedNewtonObjectiveSucc_le_alphaRayComparison method k hα

/-- Helper for Proposition 4.4.10: every modified-Newton iterate stays below the initial
objective value. -/
private lemma modifiedNewtonObjective_le_initial
    {φ : E → ℝ} {x0 : E}
    (method : ModifiedNewtonMethod φ x0) :
    ∀ k : ℕ, φ (method k) ≤ φ x0 := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Append one exact-line-search decrease step to the induction hypothesis.
      exact (modifiedNewtonObjective_nonincreasing method k).trans ih

/-- Helper for Proposition 4.4.10: the objective gap above `φ xStar` never exceeds its initial
value along the modified-Newton orbit. -/
private lemma modifiedNewtonObjectiveGap_le_initial
    {φ : E → ℝ} {x0 xStar : E}
    (method : ModifiedNewtonMethod φ x0) (k : ℕ) :
    φ (method k) - φ xStar ≤ φ x0 - φ xStar := by
  -- Subtract the same minimizer value from the global objective monotonicity estimate.
  linarith [modifiedNewtonObjective_le_initial method k]

/-- Helper for Proposition 4.4.10: every modified-Newton objective gap above the minimizer is
nonnegative. -/
private lemma modifiedNewtonObjectiveGap_nonneg
    {φ : E → ℝ} {x0 xStar : E}
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0) (k : ℕ) :
    0 ≤ φ (method k) - φ xStar := by
  -- The chosen minimizer `xStar` is no worse than every iterate of the modified-Newton orbit.
  exact sub_nonneg.mpr <| (isMinOn_iff.mp hxStar) (method k) (by simp)

/-- Helper for Proposition 4.4.10: exact line search compares the next objective gap with every
segment point between the current iterate and the full Newton trial. -/
private lemma modifiedNewtonObjectiveGapSucc_le_alphaTrialGap
    {φ : E → ℝ} {σ : ℝ} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (method : ModifiedNewtonMethod φ x0) (k : ℕ) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    φ (method (k + 1)) - φ xStar ≤
      (1 - α) * (φ (method k) - φ xStar) +
        α * (φ (NewtonSystem.step (∇ φ) (method.toMethod.x k)) - φ xStar) := by
  let x := method k
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  have hcomparison :
      φ (method (k + 1)) ≤ φ (x - α • d) := by
    -- Exact line search lets us compare the accepted point with the same Newton ray at `α`.
    simpa [x, d] using modifiedNewtonObjectiveSucc_le_alphaRayComparison method k hα
  have hsegment_eq : x - α • d = (1 - α) • x + α • T := by
    -- The Newton-ray comparison point is the convex combination of `x` and the full trial `T`.
    simp [x, d, T, NewtonSystem.step_def, DampedNewton.Method.searchDirection, sub_eq_add_neg,
      add_smul, smul_sub, add_assoc, add_left_comm, add_comm]
  have hsegment :
      φ (x - α • d) ≤ (1 - α) * φ x + α * φ T := by
    -- Strong convexity plus `σ > 0` lets us drop the nonnegative correction term.
    rw [hsegment_eq]
    have hstrong :
        φ ((1 - α) • x + α • T) ≤
          (1 - α) * φ x + α * φ T -
            (1 - α) * α * ((σ / 2) * ‖x - T‖ ^ (2 : ℕ)) := by
      exact hφ_strong.2 (by simp) (by simp) (sub_nonneg.mpr hα.2) hα.1 (by ring)
    have hcorr_nonneg : 0 ≤ (1 - α) * α * ((σ / 2) * ‖x - T‖ ^ (2 : ℕ)) := by
      have hleft_nonneg : 0 ≤ (1 - α) * α := by
        exact mul_nonneg (sub_nonneg.mpr hα.2) hα.1
      have hσhalf_nonneg : 0 ≤ σ / 2 := by linarith
      have hright_nonneg : 0 ≤ (σ / 2) * ‖x - T‖ ^ (2 : ℕ) := by
        exact mul_nonneg hσhalf_nonneg (sq_nonneg ‖x - T‖)
      exact mul_nonneg hleft_nonneg hright_nonneg
    linarith
  -- Subtract the same minimizer value from the convex segment comparison.
  linarith

/-- Helper for Proposition 4.4.10: before dropping the strong-convexity correction, the accepted
step gap is bounded by the convex interpolation with the full-trial gap minus the quadratic
segment decrease term. -/
private lemma modifiedNewtonObjectiveGapSucc_le_alphaTrialGap_sub_quadraticDecrease
    {φ : E → ℝ} {σ : ℝ} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (method : ModifiedNewtonMethod φ x0) (k : ℕ) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    φ (method (k + 1)) - φ xStar ≤
      (1 - α) * (φ (method k) - φ xStar) +
        α * (φ (NewtonSystem.step (∇ φ) (method.toMethod.x k)) - φ xStar) -
        (1 - α) * α *
          ((σ / 2) *
            ‖method k - NewtonSystem.step (∇ φ) (method.toMethod.x k)‖ ^ (2 : ℕ)) := by
  let x := method k
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  have hcomparison :
      φ (method (k + 1)) ≤ φ (x - α • d) := by
    -- Exact line search lets us compare the accepted point with the same Newton ray at `α`.
    simpa [x, d] using modifiedNewtonObjectiveSucc_le_alphaRayComparison method k hα
  have hsegment_eq : x - α • d = (1 - α) • x + α • T := by
    -- The Newton-ray comparison point is the convex combination of `x` and the full trial `T`.
    simp [x, d, T, NewtonSystem.step_def, DampedNewton.Method.searchDirection, sub_eq_add_neg,
      add_smul, smul_sub, add_assoc, add_left_comm, add_comm]
  have hsegment :
      φ (x - α • d) ≤
        (1 - α) * φ x + α * φ T -
          (1 - α) * α * ((σ / 2) * ‖x - T‖ ^ (2 : ℕ)) := by
    -- Route correction: keep the strong-convexity correction term explicit instead of discarding
    -- it, so the remaining blocker is only how to convert this quadratic decrease into the
    -- chosen-`α` cubic model used later.
    rw [hsegment_eq]
    exact
      hφ_strong.2 (by simp) (by simp) (sub_nonneg.mpr hα.2) hα.1 (by ring)
  -- Subtract the same minimizer value from the exact segment comparison while preserving the
  -- negative strong-convexity correction.
  linarith

/-- Helper for Proposition 4.4.10: exact line search bounds the next objective gap by the
full-trial gradient penalty at any segment parameter `α ∈ [0, 1]`. -/
private lemma modifiedNewtonObjectiveGapSucc_le_alphaTrialGradientPenalty
    {φ : E → ℝ} {σ : ℝ} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0) (k : ℕ) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    φ (method (k + 1)) - φ xStar ≤
      (1 - α) * (φ (method k) - φ xStar) +
        α * ((1 / (2 * σ)) *
          ‖∇ φ (NewtonSystem.step (∇ φ) (method.toMethod.x k))‖ ^ (2 : ℕ)) := by
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  have hgap_step :
      φ (method (k + 1)) - φ xStar ≤
        (1 - α) * (φ (method k) - φ xStar) + α * (φ T - φ xStar) := by
    -- First compare the accepted point with the convex segment point on the Newton ray.
    simpa [T] using modifiedNewtonObjectiveGapSucc_le_alphaTrialGap hσ hφ_strong method k hα
  have hφ_C1 : ContDiff ℝ 1 φ := hφ_hessian.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hdiff : Differentiable ℝ φ := fun y ↦ hφ_C1.differentiable_one y
  have hxStar_argmin : xStar ∈ constrainedArgmin (Set.univ : Set E) φ := by
    exact mem_constrainedArgmin_iff.mpr ⟨by simp, hxStar⟩
  have hpolyak :
      φ T - φ xStar ≤ (1 / (2 * σ)) * ‖∇ φ T‖ ^ (2 : ℕ) :=
    StrongConvexOn.sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn
      (by
        exact mem_strongConvexClass_iff.mpr ⟨hσ, hφ_strong⟩)
      hdiff hxStar_argmin
  have hscaled :
      α * (φ T - φ xStar) ≤
        α * ((1 / (2 * σ)) * ‖∇ φ T‖ ^ (2 : ℕ)) := by
    -- The trial-point Polyak estimate can be multiplied by the nonnegative segment weight `α`.
    exact mul_le_mul_of_nonneg_left hpolyak hα.1
  -- Substitute the trial-gap penalty into the convex segment comparison.
  linarith

/-- Helper for Proposition 4.4.10: strong convexity lower-bounds the objective gap by the squared
distance to the minimizer. -/
private lemma objectiveGap_ge_halfSigma_mul_sqDistToMinimizer
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {xStar y : E}
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar) :
    (σ / 2) * ‖y - xStar‖ ^ (2 : ℕ) ≤ φ y - φ xStar := by
  have hφ_C1 : ContDiff ℝ 1 φ := hφ_hessian.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hgrad0 : ∇ φ xStar = 0 := isMinOn_gradient_eq_zero hxStar
  have hφ_C1_xStar : ContDiffAt ℝ 1 φ xStar := hφ_C1.contDiffAt (x := xStar)
  have hgradAt : HasGradientAt φ (∇ φ xStar) xStar := by
    exact hφ_C1_xStar.differentiableAt one_ne_zero |>.hasGradientAt
  have hgrowth :
      φ y ≥ φ xStar + inner ℝ (∇ φ xStar) (y - xStar) + (σ / 2) * ‖y - xStar‖ ^ (2 : ℕ) := by
    -- Apply the global strong-convexity lower tangent inequality at the minimizer.
    exact
      StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
        hφ_strong (by simp) (by simp) hgradAt
  -- The minimizer gradient vanishes, so only the quadratic growth term remains.
  have hgrowth' :
      φ y ≥ φ xStar + (σ / 2) * ‖y - xStar‖ ^ (2 : ℕ) := by
    simpa [hgrad0] using hgrowth
  linarith [hgrowth']

/-- Helper for Proposition 4.4.10: the squared characteristic quantity is controlled by the
normalized objective gap. -/
private lemma modifiedNewtonCharacteristicSq_le_normalizedObjectiveGap
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {xStar y : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar) :
    modifiedNewtonCharacteristicQuantity σ L y xStar ^ (2 : ℕ) ≤
      (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) * (φ y - φ xStar) := by
  let r : ℝ := ‖y - xStar‖
  let c : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  have hgap :
      (σ / 2) * r ^ (2 : ℕ) ≤ φ y - φ xStar := by
    -- Use the canonical strong-convexity growth estimate at the minimizer.
    simpa [r] using
      (objectiveGap_ge_halfSigma_mul_sqDistToMinimizer hφ_strong hφ_hessian hxStar :
        (σ / 2) * ‖y - xStar‖ ^ (2 : ℕ) ≤ φ y - φ xStar)
  have hc_nonneg : 0 ≤ c := by
    positivity
  have hscaled :
      c * ((σ / 2) * r ^ (2 : ℕ)) ≤ c * (φ y - φ xStar) := by
    -- Multiply the gap lower bound by the normalized characteristic prefactor.
    exact mul_le_mul_of_nonneg_left hgap hc_nonneg
  have hq_sq :
      modifiedNewtonCharacteristicQuantity σ L y xStar ^ (2 : ℕ) =
        c * ((σ / 2) * r ^ (2 : ℕ)) := by
    -- Expand the characteristic quantity and simplify the scalar prefactors once.
    dsimp [c, r, modifiedNewtonCharacteristicQuantity]
    field_simp [hσ.ne']
  calc
    modifiedNewtonCharacteristicQuantity σ L y xStar ^ (2 : ℕ) =
        c * ((σ / 2) * r ^ (2 : ℕ)) := hq_sq
    _ ≤ c * (φ y - φ xStar) := hscaled
    _ = (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) * (φ y - φ xStar) := by
      rfl

/-- Helper for Proposition 4.4.10: the characteristic quantity at every iterate is uniformly
controlled by the initial normalized objective gap. -/
private lemma modifiedNewtonCharacteristicSq_le_initialNormalizedObjectiveGap
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0) (k : ℕ) :
    modifiedNewtonCharacteristicQuantity σ L (method k) xStar ^ (2 : ℕ) ≤
      (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) * (φ x0 - φ xStar) := by
  have hcurrent :
      modifiedNewtonCharacteristicQuantity σ L (method k) xStar ^ (2 : ℕ) ≤
        (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) *
          (φ (method k) - φ xStar) := by
    -- First place the current iterate in the canonical characteristic-versus-gap comparison.
    simpa using
      (modifiedNewtonCharacteristicSq_le_normalizedObjectiveGap hσ hφ_strong hφ_hessian hxStar :
        modifiedNewtonCharacteristicQuantity σ L (method k) xStar ^ (2 : ℕ) ≤
          (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) *
            (φ (method k) - φ xStar))
  have hcoeff_nonneg :
      0 ≤ (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) := by
    positivity
  have hgap :
      (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) * (φ (method k) - φ xStar) ≤
        (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) * (φ x0 - φ xStar) := by
    -- Then freeze the normalized gap by the monotonicity of the modified-Newton objective.
    exact mul_le_mul_of_nonneg_left (modifiedNewtonObjectiveGap_le_initial method k) hcoeff_nonneg
  exact hcurrent.trans hgap

/-- Helper for Proposition 4.4.10: the gradient at the full Newton trial point is quadratic in
the Newton search direction. -/
private lemma modifiedNewtonFullTrialGradientNormLeQuadratic
    {φ : E → ℝ} {L : NNReal} {x0 : E}
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0) (k : ℕ) :
    ‖∇ φ (NewtonSystem.step (∇ φ) (method.toMethod.x k))‖ ≤
      ((L : ℝ) / 2) * ‖method.toMethod.searchDirection k‖ ^ (2 : ℕ) := by
  let x := method k
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  have hstep_eq : T - x = -d := by
    -- Expand the full Newton trial and cancel the base point.
    simp [T, x, d, NewtonSystem.step_def, DampedNewton.Method.searchDirection, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  have hstep_lin : hessian φ x (T - x) = -∇ φ x := by
    -- The full Newton correction exactly cancels the linearized gradient at the base point.
    have happly :
        (fderiv ℝ (∇ φ) x) d = ∇ φ x := by
      change
        (fderiv ℝ (∇ φ) ↑(method.toMethod.x k))
            ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
                (method.toMethod.x k).property).symm)
              (∇ φ ↑(method.toMethod.x k))) =
          ∇ φ ↑(method.toMethod.x k)
      exact
        ContinuousLinearEquiv.apply_symm_apply
          ((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
            (method.toMethod.x k).property)
          (∇ φ ↑(method.toMethod.x k))
    calc
      hessian φ x (T - x) = (fderiv ℝ (∇ φ) x) (-d) := by
        simpa [hessian, x] using congrArg (fderiv ℝ (∇ φ) x) hstep_eq
      _ = -(fderiv ℝ (∇ φ) x d) := by
        simp
      _ = -∇ φ x := by
        rw [happly]
  have hdeviation := HasLipschitzContinuousHessian.gradient_deviation_le hφ_hessian x T
  -- Rewrite the Taylor remainder at the trial point using the Newton cancellation identity.
  calc
    ‖∇ φ T‖ = ‖∇ φ T - ∇ φ x - hessian φ x (T - x)‖ := by
      rw [hstep_lin]
      simp
    _ ≤ ((L : ℝ) / 2) * ‖T - x‖ ^ (2 : ℕ) := hdeviation
    _ = ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
      rw [hstep_eq]
      simp

/-- Helper for Proposition 4.4.10: the Newton search direction is controlled by the current error
times `1 + q_k / 2`. -/
private lemma modifiedNewtonSearchDirectionNorm_le_one_add_halfCharacteristic_mulError
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} :
    ‖method.toMethod.searchDirection k‖ ≤
      (1 + modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) *
        ‖method k - xStar‖ := by
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let r : ℝ := ‖method k - xStar‖
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method k) xStar
  have hq_def : q = ((L : ℝ) / σ) * r := by
    -- Expand the characteristic quantity once and keep the rest of the proof in this spelling.
    simp [q, r, modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  have hd_eq :
      d = (method k - xStar) - (T - xStar) := by
    -- Compare the current error with the full-trial error to recover the Newton direction.
    calc
      d = method k - T := by
        simp [d, T, NewtonSystem.step_def, DampedNewton.Method.searchDirection, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm]
      _ = (method k - xStar) - (T - xStar) := by
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have htrial :
      ‖T - xStar‖ ≤ ((L : ℝ) / (2 * σ)) * r ^ (2 : ℕ) := by
    -- The full Newton trial already satisfies the standard quadratic one-step error bound.
    simpa [T, r] using
      modifiedNewtonStepErrorLeQuadratic hσ hφ_strong hφ_hessian hxStar (method.toMethod.x k)
  calc
    ‖d‖ = ‖(method k - xStar) - (T - xStar)‖ := by rw [hd_eq]
    _ ≤ ‖method k - xStar‖ + ‖T - xStar‖ := norm_sub_le _ _
    _ = r + ‖T - xStar‖ := by simp [r]
    _ ≤ r + ((L : ℝ) / (2 * σ)) * r ^ (2 : ℕ) := by
      simpa [add_comm] using add_le_add_left htrial r
    _ = (1 + q / 2) * r := by
      rw [hq_def]
      ring
    _ = (1 + modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) *
          ‖method k - xStar‖ := by
      simp [q, r]

/-- Helper for Proposition 4.4.10: subtracting the current minimizer error from the Newton search
direction leaves exactly the negative full-trial error. -/
private lemma modifiedNewtonSearchDirectionSubError_eq_neg_fullTrialError
    {φ : E → ℝ} {x0 xStar : E}
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} :
    method.toMethod.searchDirection k - (method k - xStar) =
      -(NewtonSystem.step (∇ φ) (method.toMethod.x k) - xStar) := by
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  -- Route correction: compare the search direction with the minimizer error through the full
  -- Newton trial, not through the old coarse `‖d_k‖` normalization.
  calc
    d - (method k - xStar) = (method k - T) - (method k - xStar) := by
      simp [d, T, NewtonSystem.step_def, DampedNewton.Method.searchDirection, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]
    _ = -(T - xStar) := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 4.4.10: the Newton search direction differs from the minimizer error by
at most `(q_k / 2) * ‖x_k - x*‖`, where `q_k = (L / σ) ‖x_k - x*‖`. -/
private lemma modifiedNewtonSearchDirectionSubError_le_halfCharacteristic_mulError
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} :
    ‖method.toMethod.searchDirection k - (method k - xStar)‖ ≤
      (modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) *
        ‖method k - xStar‖ := by
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let r : ℝ := ‖method k - xStar‖
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method k) xStar
  have htrial :
      ‖T - xStar‖ ≤ ((L : ℝ) / (2 * σ)) * r ^ (2 : ℕ) := by
    -- Reuse the full-trial quadratic error estimate on the current admissible Newton point.
    simpa [T, r] using
      (modifiedNewtonStepErrorLeQuadratic
        hσ hφ_strong hφ_hessian hxStar (method.toMethod.x k))
  have hq_def : q = ((L : ℝ) / σ) * r := by
    -- Keep the characteristic quantity in the normalized `((L / σ) * r)` form.
    simp [q, r, modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  calc
    ‖method.toMethod.searchDirection k - (method k - xStar)‖ = ‖-(T - xStar)‖ := by
      rw [modifiedNewtonSearchDirectionSubError_eq_neg_fullTrialError (method := method)
        (xStar := xStar) (k := k)]
    _ = ‖T - xStar‖ := by
      simpa [norm_sub_rev]
    _ ≤ ((L : ℝ) / (2 * σ)) * r ^ (2 : ℕ) := htrial
    _ = (q / 2) * r := by
      rw [hq_def]
      ring
    _ = (modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) *
          ‖method k - xStar‖ := by
      simp [q, r]

/-- Helper for Proposition 4.4.10: each comparison point on the Newton ray is the exact segment
point toward `x*` plus the scaled full-trial error perturbation. -/
private lemma modifiedNewtonAlphaSearchPoint_eq_lineMap_add_trialError
    {φ : E → ℝ} {x0 xStar : E}
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} {α : ℝ} :
    method k - α • method.toMethod.searchDirection k =
      AffineMap.lineMap (method k) xStar α +
        α • (NewtonSystem.step (∇ φ) (method.toMethod.x k) - xStar) := by
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  -- Route correction: expose the minimizer segment and the full-trial perturbation as separate
  -- pieces before estimating the remaining accepted-step recurrence.
  calc
    method k - α • d =
        method k - α • ((method k - xStar) - (T - xStar)) := by
          rw [show d = (method k - xStar) - (T - xStar) by
            calc
              d = method k - T := by
                simp [d, T, NewtonSystem.step_def, DampedNewton.Method.searchDirection,
                  sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
              _ = (method k - xStar) - (T - xStar) := by
                simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]]
    _ = AffineMap.lineMap (method k) xStar α + α • (T - xStar) := by
      simp [AffineMap.lineMap_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        smul_sub, sub_smul]

/-- Helper for Proposition 4.4.10: subtracting the minimizer segment point from the Newton-ray
comparison point leaves exactly the scaled full-trial error. -/
private lemma modifiedNewtonAlphaSearchPoint_sub_lineMap_eq_scaledTrialError
    {φ : E → ℝ} {x0 xStar : E}
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} {α : ℝ} :
    (method k - α • method.toMethod.searchDirection k) -
        AffineMap.lineMap (method k) xStar α =
      α • (NewtonSystem.step (∇ φ) (method.toMethod.x k) - xStar) := by
  -- Rewrite the Newton-ray comparison point first, then subtract the segment point in one step.
  rw [modifiedNewtonAlphaSearchPoint_eq_lineMap_add_trialError (method := method)
    (xStar := xStar) (k := k) (α := α)]
  abel

/-- Helper for Proposition 4.4.10: the Newton-ray comparison point stays within the scaled
full-trial error of the minimizer segment point. -/
private lemma modifiedNewtonAlphaSearchPointSubLineMap_le_scaledHalfCharacteristicMulError
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ‖(method k - α • method.toMethod.searchDirection k) -
        AffineMap.lineMap (method k) xStar α‖ ≤
      α *
        ((modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) *
          ‖method k - xStar‖) := by
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  have hpoint_eq :
      (method k - α • method.toMethod.searchDirection k) -
          AffineMap.lineMap (method k) xStar α =
        α • (T - xStar) := by
    -- Reuse the exact perturbation identity before taking norms.
    simpa [T] using
      modifiedNewtonAlphaSearchPoint_sub_lineMap_eq_scaledTrialError
        (method := method) (xStar := xStar) (k := k) (α := α)
  have htrial :
      ‖T - xStar‖ ≤
        (modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) *
          ‖method k - xStar‖ := by
    -- The perturbation is exactly the full-trial error, so the deviation estimate gives the
    -- desired scale.
    calc
      ‖T - xStar‖ = ‖-(T - xStar)‖ := by
        simpa using (norm_neg (T - xStar)).symm
      _ = ‖method.toMethod.searchDirection k - (method k - xStar)‖ := by
        rw [modifiedNewtonSearchDirectionSubError_eq_neg_fullTrialError (method := method)
          (xStar := xStar) (k := k)]
      _ ≤
          (modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) *
            ‖method k - xStar‖ := by
              exact modifiedNewtonSearchDirectionSubError_le_halfCharacteristic_mulError
                hσ hφ_strong hφ_hessian hxStar method (k := k)
  calc
    ‖(method k - α • method.toMethod.searchDirection k) -
        AffineMap.lineMap (method k) xStar α‖ = ‖α • (T - xStar)‖ := by
          rw [hpoint_eq]
    _ = α * ‖T - xStar‖ := by
      simp [norm_smul_of_nonneg, hα.1]
    _ ≤ α *
        ((modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) *
          ‖method k - xStar‖) := by
            exact mul_le_mul_of_nonneg_left htrial hα.1

/-- Helper for Proposition 4.4.10: the current objective gap is bounded by the Newton quadratic
energy together with the cubic Taylor remainder at `xStar`. -/
private lemma modifiedNewtonObjectiveGap_le_halfNewtonEnergy_add_cubicError
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ}
    (hxStar : IsMinOn φ Set.univ xStar) :
    φ (method k) - φ xStar ≤
      (1 / 2 : ℝ) *
          inner ℝ
            (hessian φ (method k) (method.toMethod.searchDirection k))
            (method.toMethod.searchDirection k) +
        ((L : ℝ) / 6) * ‖method k - xStar‖ ^ (3 : ℕ) := by
  let x := method k
  let d := method.toMethod.searchDirection k
  let e := x - xStar
  let hφ_C2 : ContDiff ℝ 2 φ := hφ_hessian.contDiff
  have hnewton_eq : hessian φ x d = ∇ φ x := by
    -- Expanding the Newton search direction recovers the linearized gradient equation.
    change
      (fderiv ℝ (∇ φ) ↑(method.toMethod.x k))
          ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
              (method.toMethod.x k).property).symm)
            (∇ φ ↑(method.toMethod.x k))) =
        ∇ φ ↑(method.toMethod.x k)
    exact
      ContinuousLinearEquiv.apply_symm_apply
        ((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
          (method.toMethod.x k).property)
        (∇ φ ↑(method.toMethod.x k))
  have herror :=
    HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le
      hφ_hessian x xStar
  have hmodel_lower :
      secondOrderTaylorModelAt φ x xStar -
          ((L : ℝ) / 6) * ‖xStar - x‖ ^ (3 : ℕ) ≤
        φ xStar := by
    -- Use the lower side of the Taylor remainder bound at `xStar`.
    linarith [(abs_le.mp herror).1]
  have hselfAdjoint : IsSelfAdjoint (hessian φ x) := by
    simpa using
      (fderiv_gradient_isSymmetric_of_contDiffAt (f := φ) (x := x)
        (hf := hφ_C2.contDiffAt (x := x))).isSelfAdjoint
  have hquad_nonneg :
      0 ≤ inner ℝ (hessian φ x (d - e)) (d - e) := by
    have hUniv_nonempty : (interior (Set.univ : Set E)).Nonempty := by
      simp
    have hcont : ContinuousOn φ (Set.univ : Set E) := hφ_C2.continuous.continuousOn
    have hC2 : ContDiffOn ℝ 2 φ (interior (Set.univ : Set E)) := by
      simpa using hφ_C2.contDiffOn
    have hbound : σ • (1 : E →L[ℝ] E) ≤ hessian φ x := by
      -- Whole-space strong convexity supplies the Hessian Loewner lower bound at `x`.
      have hiff :=
        (strongConvexOn_iff_hessian_lower_bound
          hσ convex_univ hUniv_nonempty hcont hC2).1 hφ_strong
      simpa [x] using hiff x (by simp)
    have hquad :=
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hσ hC2 (by simp : x ∈ interior (Set.univ : Set E))).1 hbound (d - e)
    exact le_trans (by positivity) hquad
  have hcross :
      inner ℝ (hessian φ x e) d = inner ℝ (hessian φ x d) e := by
    -- Self-adjointness identifies the two mixed Hessian terms in the quadratic expansion.
    calc
      inner ℝ (hessian φ x e) d = inner ℝ e (hessian φ x d) := hselfAdjoint.isSymmetric _ _
      _ = inner ℝ (hessian φ x d) e := by rw [real_inner_comm]
  have htrial_model_lower :
      φ x -
          (1 / 2 : ℝ) * inner ℝ (hessian φ x d) d ≤
        secondOrderTaylorModelAt φ x xStar := by
    -- Compare the Taylor model at `xStar` with the exact Newton quadratic energy.
    rw [secondOrderTaylorModelAt_apply, ← hnewton_eq]
    have hquadratic_expand :
        inner ℝ (hessian φ x (d - e)) (d - e) =
          inner ℝ (hessian φ x d) d -
            2 * inner ℝ (hessian φ x d) e +
            inner ℝ (hessian φ x e) e := by
      calc
        inner ℝ (hessian φ x (d - e)) (d - e) =
            inner ℝ (hessian φ x d - hessian φ x e) (d - e) := by
              simp [ContinuousLinearMap.map_sub]
        _ =
            (inner ℝ (hessian φ x d - hessian φ x e) d) -
              inner ℝ (hessian φ x d - hessian φ x e) e := by
              rw [inner_sub_right]
        _ =
            (inner ℝ (hessian φ x d) d - inner ℝ (hessian φ x e) d) -
              (inner ℝ (hessian φ x d) e - inner ℝ (hessian φ x e) e) := by
              rw [inner_sub_left, inner_sub_left]
        _ =
            inner ℝ (hessian φ x d) d -
              inner ℝ (hessian φ x d) e -
              inner ℝ (hessian φ x e) d +
              inner ℝ (hessian φ x e) e := by
              ring
        _ =
            inner ℝ (hessian φ x d) d -
              2 * inner ℝ (hessian φ x d) e +
              inner ℝ (hessian φ x e) e := by
              rw [hcross]
              ring
    have hquadratic :
        0 ≤
          inner ℝ (hessian φ x d) d -
            2 * inner ℝ (hessian φ x d) e +
            inner ℝ (hessian φ x e) e := by
      rw [← hquadratic_expand]
      exact hquad_nonneg
    have htarget :
        inner ℝ (hessian φ x d) e -
            (1 / 2 : ℝ) * inner ℝ (hessian φ x e) e ≤
          (1 / 2 : ℝ) * inner ℝ (hessian φ x d) d := by
      linarith
    have hdisp : xStar - x = -e := by
      simp [e, sub_eq_add_neg]
    rw [hdisp]
    have hrewrite :
        φ x + inner ℝ (hessian φ x d) (-e) +
            (1 / 2 : ℝ) * inner ℝ (hessian φ x (-e)) (-e) =
          φ x -
            (inner ℝ (hessian φ x d) e -
              (1 / 2 : ℝ) * inner ℝ (hessian φ x e) e) := by
      simp [inner_smul_left, inner_smul_right, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hrewrite]
    linarith
  have hnorm_eq : ‖xStar - x‖ = ‖x - xStar‖ := by
    simpa [norm_sub_rev]
  have hcombined :
      φ x -
          (1 / 2 : ℝ) * inner ℝ (hessian φ x d) d -
          ((L : ℝ) / 6) * ‖x - xStar‖ ^ (3 : ℕ) ≤
        φ xStar := by
    -- Compare the full-trial model lower bound with the Taylor remainder at `xStar`.
    rw [hnorm_eq] at hmodel_lower
    exact (sub_le_sub_right htrial_model_lower _).trans hmodel_lower
  -- Rearranging the lower bound on `φ xStar` gives the desired upper bound on the current gap.
  linarith

/-- Helper for Proposition 4.4.10: exact line search plus the quadratic Taylor model on the
Newton ray bounds the next objective gap by the current gap and two cubic remainders. -/
private lemma modifiedNewtonObjectiveGapSucc_le_alphaCurrentAndDirectionCubic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    φ (method (k + 1)) - φ xStar ≤
      (1 - α) * (φ (method k) - φ xStar) +
        α * (((L : ℝ) / 6) * ‖method k - xStar‖ ^ (3 : ℕ)) +
        ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖method.toMethod.searchDirection k‖ ^ (3 : ℕ) := by
  let x := method k
  let d := method.toMethod.searchDirection k
  let curv : ℝ := inner ℝ (hessian φ x d) d
  have hcomparison :
      φ (method (k + 1)) ≤ φ (x - α • d) := by
    -- Exact line search compares the accepted point with the same Newton ray at `α`.
    simpa [x, d] using modifiedNewtonObjectiveSucc_le_alphaRayComparison method k hα
  have herror :=
    HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le
      hφ_hessian x (x - α • d)
  have hupper :
      φ (x - α • d) ≤
        secondOrderTaylorModelAt φ x (x - α • d) +
          ((L : ℝ) / 6) * ‖(x - α • d) - x‖ ^ (3 : ℕ) := by
    -- The Hessian-Lipschitz remainder controls the quadratic Taylor model on the Newton ray.
    linarith [(abs_le.mp herror).2]
  have hnewton_eq : hessian φ x d = ∇ φ x := by
    -- Expanding the Newton search direction recovers the linearized gradient equation.
    change
      (fderiv ℝ (∇ φ) ↑(method.toMethod.x k))
          ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
              (method.toMethod.x k).property).symm)
            (∇ φ ↑(method.toMethod.x k))) =
        ∇ φ ↑(method.toMethod.x k)
    exact
      ContinuousLinearEquiv.apply_symm_apply
        ((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
          (method.toMethod.x k).property)
        (∇ φ ↑(method.toMethod.x k))
  have hmodel_ray :
      secondOrderTaylorModelAt φ x (x - α • d) =
        φ x - α * curv + (α ^ (2 : ℕ) / 2) * curv := by
    -- Along the Newton ray, the quadratic Taylor model collapses to the scalar curvature term.
    rw [secondOrderTaylorModelAt_apply, ← hnewton_eq]
    simp [x, d, curv, inner_smul_left, inner_smul_right, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm, mul_assoc]
    ring
  have hcurv_nonneg : 0 ≤ curv := by
    have hUniv_nonempty : (interior (Set.univ : Set E)).Nonempty := by
      simp
    have hφ_C2 : ContDiff ℝ 2 φ := hφ_hessian.contDiff
    have hcont : ContinuousOn φ (Set.univ : Set E) := hφ_C2.continuous.continuousOn
    have hC2 : ContDiffOn ℝ 2 φ (interior (Set.univ : Set E)) := by
      simpa using hφ_C2.contDiffOn
    have hbound : σ • (1 : E →L[ℝ] E) ≤ hessian φ x := by
      -- Whole-space strong convexity supplies the Hessian Loewner lower bound at `x`.
      have hiff :=
        (strongConvexOn_iff_hessian_lower_bound
          hσ convex_univ hUniv_nonempty hcont hC2).1 hφ_strong
      simpa [x] using hiff x (by simp)
    have hquad :=
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hσ hC2 (by simp : x ∈ interior (Set.univ : Set E))).1 hbound d
    exact le_trans (by positivity) hquad
  have hgap_curv :
      φ x - φ xStar ≤
        (1 / 2 : ℝ) * curv + ((L : ℝ) / 6) * ‖x - xStar‖ ^ (3 : ℕ) := by
    -- Reuse the Newton-energy bound for the current iterate.
    simpa [x, d, curv] using
      modifiedNewtonObjectiveGap_le_halfNewtonEnergy_add_cubicError
        hσ hφ_strong hφ_hessian method hxStar (k := k)
  have hgap_step :
      φ x - φ xStar - (α * curv - (α ^ (2 : ℕ) / 2) * curv) ≤
        (1 - α) * (φ x - φ xStar) +
          α * (((L : ℝ) / 6) * ‖x - xStar‖ ^ (3 : ℕ)) := by
    -- The Newton curvature absorbs an `α`-fraction of the current objective gap, leaving only
    -- the current cubic Taylor remainder.
    have hcurv_dom :
        (1 / 2 : ℝ) * curv ≤ (1 - α / 2) * curv := by
      have hcoeff : (1 / 2 : ℝ) ≤ 1 - α / 2 := by
        nlinarith [hα.2]
      exact mul_le_mul_of_nonneg_right hcoeff hcurv_nonneg
    have hgap_curv' :
        φ x - φ xStar ≤
          (1 - α / 2) * curv + ((L : ℝ) / 6) * ‖x - xStar‖ ^ (3 : ℕ) := by
      have hcurv_shift :
          (1 / 2 : ℝ) * curv + ((L : ℝ) / 6) * ‖x - xStar‖ ^ (3 : ℕ) ≤
            (1 - α / 2) * curv + ((L : ℝ) / 6) * ‖x - xStar‖ ^ (3 : ℕ) := by
        exact add_le_add hcurv_dom le_rfl
      exact hgap_curv.trans hcurv_shift
    have hscaled_gap :
        α * (φ x - φ xStar) ≤
          (α - α ^ (2 : ℕ) / 2) * curv +
            α * (((L : ℝ) / 6) * ‖x - xStar‖ ^ (3 : ℕ)) := by
      have hmul := mul_le_mul_of_nonneg_left hgap_curv' hα.1
      nlinarith
    linarith
  calc
    φ (method (k + 1)) - φ xStar ≤
        secondOrderTaylorModelAt φ x (x - α • d) - φ xStar +
          ((L : ℝ) / 6) * ‖(x - α • d) - x‖ ^ (3 : ℕ) := by
          linarith
    _ =
        φ x - φ xStar - (α * curv - (α ^ (2 : ℕ) / 2) * curv) +
          ((L : ℝ) / 6) * ‖(x - α • d) - x‖ ^ (3 : ℕ) := by
          rw [hmodel_ray]
          ring
    _ ≤
        (1 - α) * (φ x - φ xStar) +
          α * (((L : ℝ) / 6) * ‖x - xStar‖ ^ (3 : ℕ)) +
          ((L : ℝ) / 6) * ‖(x - α • d) - x‖ ^ (3 : ℕ) := by
          gcongr
    _ =
        (1 - α) * (φ (method k) - φ xStar) +
          α * (((L : ℝ) / 6) * ‖method k - xStar‖ ^ (3 : ℕ)) +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖method.toMethod.searchDirection k‖ ^ (3 : ℕ) := by
          have hα_nonneg : 0 ≤ α := hα.1
          simp [x, d, norm_smul, Real.norm_of_nonneg hα_nonneg, mul_pow, mul_assoc,
            mul_left_comm, mul_comm, sub_eq_add_neg]

/-- Helper for Proposition 4.4.10: the current cubic Taylor remainder is controlled by the
current objective gap times the characteristic quantity. -/
private lemma modifiedNewtonCurrentCubic_le_thirdCharacteristic_mulObjectiveGap
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} :
    ((L : ℝ) / 6) * ‖method k - xStar‖ ^ (3 : ℕ) ≤
      (modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 3) *
        (φ (method k) - φ xStar) := by
  let r : ℝ := ‖method k - xStar‖
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method k) xStar
  have hgap :
      (σ / 2) * r ^ (2 : ℕ) ≤ φ (method k) - φ xStar := by
    -- Strong convexity turns the current objective gap into the canonical quadratic error lower
    -- bound around the minimizer.
    simpa [r] using
      (objectiveGap_ge_halfSigma_mul_sqDistToMinimizer hφ_strong hφ_hessian hxStar :
        (σ / 2) * ‖method k - xStar‖ ^ (2 : ℕ) ≤ φ (method k) - φ xStar)
  have hq_def : q = ((L : ℝ) / σ) * r := by
    -- Keep the characteristic quantity in the normalized `((L / σ) * r)` form for one scalar
    -- rewrite, then reuse the quadratic gap lower bound.
    simp [q, r, modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  calc
    ((L : ℝ) / 6) * r ^ (3 : ℕ) =
        (q / 3) * ((σ / 2) * r ^ (2 : ℕ)) := by
          rw [hq_def]
          field_simp [hσ.ne']
          ring
    _ ≤ (q / 3) * (φ (method k) - φ xStar) := by
          exact mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ q / 3)
    _ =
        (modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 3) *
          (φ (method k) - φ xStar) := by
          simp [q]

/-- Helper for Proposition 4.4.10: after rewriting both cubic terms through the characteristic
quantity, the accepted-step objective gap satisfies a characteristic-weighted scalar recurrence. -/
private lemma modifiedNewtonObjectiveGapSucc_le_characteristicWeightedGap
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    φ (method (k + 1)) - φ xStar ≤
      ((1 - α) +
          (modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 3) *
            (α +
              α ^ (3 : ℕ) *
                (1 + modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) ^
                  (3 : ℕ))) *
        (φ (method k) - φ xStar) := by
  let gap : ℝ := φ (method k) - φ xStar
  let r : ℝ := ‖method k - xStar‖
  let d := method.toMethod.searchDirection k
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method k) xStar
  have hq_nonneg : 0 ≤ q := by
    -- The characteristic quantity is a nonnegative scalar multiple of a norm.
    have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
    exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
  have hgap_nonneg : 0 ≤ gap := by
    -- Strong convexity keeps every objective gap above the quadratic distance lower bound.
    have hgap_lower :
        (σ / 2) * ‖method k - xStar‖ ^ (2 : ℕ) ≤ gap := by
      simpa [gap] using
        (objectiveGap_ge_halfSigma_mul_sqDistToMinimizer hφ_strong hφ_hessian hxStar :
          (σ / 2) * ‖method k - xStar‖ ^ (2 : ℕ) ≤ φ (method k) - φ xStar)
    exact le_trans (by positivity) hgap_lower
  have hα_nonneg : 0 ≤ α := hα.1
  have hstep :=
    modifiedNewtonObjectiveGapSucc_le_alphaCurrentAndDirectionCubic
      hσ hφ_strong hφ_hessian hxStar method (k := k) hα
  have hcurrent_cubic :
      ((L : ℝ) / 6) * r ^ (3 : ℕ) ≤ (q / 3) * gap := by
    -- Route correction: rewrite the current cubic term through the gap lower bound first, so the
    -- remaining recurrence depends only on the characteristic quantity `q_k`.
    simpa [q, r, gap] using
      (modifiedNewtonCurrentCubic_le_thirdCharacteristic_mulObjectiveGap
        hσ hφ_strong hφ_hessian hxStar method (k := k) :
          ((L : ℝ) / 6) * ‖method k - xStar‖ ^ (3 : ℕ) ≤
            (modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 3) *
              (φ (method k) - φ xStar))
  have hdir_le :
      ‖d‖ ≤ (1 + q / 2) * r := by
    -- Reuse the owner-level direction bound in the same local `q_k` and `r_k` notation.
    simpa [d, q, r] using
      modifiedNewtonSearchDirectionNorm_le_one_add_halfCharacteristic_mulError
        hσ hφ_strong hφ_hessian hxStar method
  have hdir_cube :
      ‖d‖ ^ (3 : ℕ) ≤ ((1 + q / 2) * r) ^ (3 : ℕ) := by
    have hd_nonneg : 0 ≤ ‖d‖ := norm_nonneg _
    have hone_add_half_q_nonneg : 0 ≤ 1 + q / 2 := by
      nlinarith
    have hright_nonneg : 0 ≤ (1 + q / 2) * r := by
      exact mul_nonneg hone_add_half_q_nonneg (norm_nonneg _)
    exact pow_le_pow_left₀ hd_nonneg hdir_le 3
  have hdir_cubic :
      ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ) ≤
        ((q / 3) * (α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ))) * gap := by
    have hone_add_half_q_nonneg : 0 ≤ 1 + q / 2 := by
      nlinarith
    have hα_cube_nonneg : 0 ≤ α ^ (3 : ℕ) := by
      exact pow_nonneg hα_nonneg _
    have hcoeff_nonneg : 0 ≤ ((L : ℝ) / 6) * α ^ (3 : ℕ) := by
      exact mul_nonneg (by positivity : 0 ≤ (L : ℝ) / 6) hα_cube_nonneg
    have hdir_factor_nonneg : 0 ≤ α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ) := by
      exact mul_nonneg hα_cube_nonneg (pow_nonneg hone_add_half_q_nonneg _)
    calc
      ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ) ≤
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * (((1 + q / 2) * r) ^ (3 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hdir_cube hcoeff_nonneg
      _ = (α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ)) * (((L : ℝ) / 6) * r ^ (3 : ℕ)) := by
            ring
      _ ≤ (α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ)) * ((q / 3) * gap) := by
            exact mul_le_mul_of_nonneg_left hcurrent_cubic hdir_factor_nonneg
      _ = ((q / 3) * (α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ))) * gap := by
            ring
  calc
    φ (method (k + 1)) - φ xStar ≤
        (1 - α) * gap +
          α * (((L : ℝ) / 6) * r ^ (3 : ℕ)) +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ) := by
          simpa [gap, r, d] using hstep
    _ ≤ (1 - α) * gap + α * ((q / 3) * gap) +
          ((q / 3) * (α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ))) * gap := by
          exact add_le_add_left
            (add_le_add
              (mul_le_mul_of_nonneg_left hcurrent_cubic hα_nonneg)
              hdir_cubic)
            ((1 - α) * gap)
    _ =
        ((1 - α) + (q / 3) * (α + α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ))) * gap := by
          ring
    _ =
        ((1 - α) +
            (modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 3) *
              (α +
                α ^ (3 : ℕ) *
                  (1 + modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) ^
                    (3 : ℕ))) *
          (φ (method k) - φ xStar) := by
          simp [q, gap]

/-- Helper for Proposition 4.4.10: under the sharper bootstrap threshold
`((L : ℝ) / σ) * ‖x_k - x*‖ ≤ 1 / 2`, the accepted modified-Newton step satisfies the quadratic
error recurrence with coefficient `(L : ℝ) / σ`. -/
private lemma modifiedNewtonAcceptedStepErrorLeQuadratic_of_mul_le_half
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ}
    (hk_half : ((L : ℝ) / σ) * ‖method k - xStar‖ ≤ (1 / 2 : ℝ)) :
    ‖method (k + 1) - xStar‖ ≤
      ((L : ℝ) / σ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let r : ℝ := ‖method k - xStar‖
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method k) xStar
  let hφ_C1 : ContDiff ℝ 1 φ := hφ_hessian.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hdiff : Differentiable ℝ φ := fun y ↦ hφ_C1.differentiable_one y
  have hxStar_argmin : xStar ∈ constrainedArgmin (Set.univ : Set E) φ := by
    exact mem_constrainedArgmin_iff.mpr ⟨by simp, hxStar⟩
  have hpolyak :
      φ T - φ xStar ≤ (1 / (2 * σ)) * ‖∇ φ T‖ ^ (2 : ℕ) :=
    StrongConvexOn.sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn
      (by
        exact mem_strongConvexClass_iff.mpr ⟨hσ, hφ_strong⟩)
      hdiff hxStar_argmin
  have hobjective :
      φ (method (k + 1)) ≤ φ T :=
    modifiedNewtonObjective_le_fullTrial method k
  have hgap_upper :
      φ (method (k + 1)) - φ xStar ≤ (1 / (2 * σ)) * ‖∇ φ T‖ ^ (2 : ℕ) := by
    linarith
  have hgap_lower :
      (σ / 2) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        φ (method (k + 1)) - φ xStar := by
    -- Strong convexity turns the accepted-point objective gap into a quadratic distance bound.
    simpa using
      (objectiveGap_ge_halfSigma_mul_sqDistToMinimizer hφ_strong hφ_hessian hxStar :
        (σ / 2) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          φ (method (k + 1)) - φ xStar)
  have hnorm_sq :
      (σ * ‖method (k + 1) - xStar‖) ^ (2 : ℕ) ≤ ‖∇ φ T‖ ^ (2 : ℕ) := by
    -- Compare the lower and upper gap estimates and rewrite the left side as a square.
    have hleft :
        σ ^ (2 : ℕ) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          (2 * σ) * (φ (method (k + 1)) - φ xStar) := by
      nlinarith [hgap_lower]
    have hright :
        (2 * σ) * (φ (method (k + 1)) - φ xStar) ≤ ‖∇ φ T‖ ^ (2 : ℕ) := by
      have hmul :=
        mul_le_mul_of_nonneg_left hgap_upper (show 0 ≤ 2 * σ by positivity)
      simpa [hσ.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    have hraw :
        σ ^ (2 : ℕ) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤ ‖∇ φ T‖ ^ (2 : ℕ) :=
      hleft.trans hright
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hraw
  have hnorm_le_grad :
      ‖method (k + 1) - xStar‖ ≤ ‖∇ φ T‖ / σ := by
    have hσnorm_nonneg : 0 ≤ σ * ‖method (k + 1) - xStar‖ := by positivity
    have hgrad_nonneg : 0 ≤ ‖∇ φ T‖ := norm_nonneg _
    have hσnorm_le : σ * ‖method (k + 1) - xStar‖ ≤ ‖∇ φ T‖ := by
      have hsq := (sq_le_sq).1 hnorm_sq
      simpa [abs_of_nonneg hσnorm_nonneg, abs_of_nonneg hgrad_nonneg] using hsq
    exact (le_div_iff₀ hσ).2 <| by simpa [mul_comm] using hσnorm_le
  have hgrad_trial :
      ‖∇ φ T‖ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) :=
    modifiedNewtonFullTrialGradientNormLeQuadratic hφ_hessian method k
  have hgrad_over_sigma :
      ‖∇ φ T‖ / σ ≤ ((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ) := by
    have hcoeff :
        ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) =
          (((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ)) * σ := by
      field_simp [hσ.ne']
    exact (div_le_iff₀ hσ).2 <| by
      calc
        ‖∇ φ T‖ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := hgrad_trial
        _ = (((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ)) * σ := hcoeff
  have hq_le_half : q ≤ (1 / 2 : ℝ) := by
    -- The companion hypothesis is exactly the characteristic half-threshold in local notation.
    simpa [q, r, modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm] using hk_half
  have hdir_le :
      ‖d‖ ≤ (1 + q / 2) * r := by
    -- First control the Newton direction by the current error and the characteristic quantity.
    simpa [d, r] using
      modifiedNewtonSearchDirectionNorm_le_one_add_halfCharacteristic_mulError
        hσ hφ_strong hφ_hessian hxStar method
  have hdir_le_fiveQuarter :
      ‖d‖ ≤ ((5 : ℝ) / 4) * r := by
    -- The half-threshold reduces the local direction factor to the fixed constant `5 / 4`.
    have hr_nonneg : 0 ≤ r := by positivity
    have hfactor_le : 1 + q / 2 ≤ (5 : ℝ) / 4 := by
      nlinarith
    exact hdir_le.trans <| mul_le_mul_of_nonneg_right hfactor_le hr_nonneg
  have hdir_sq :
      ‖d‖ ^ (2 : ℕ) ≤ (((5 : ℝ) / 4) * r) ^ (2 : ℕ) := by
    have hd_nonneg : 0 ≤ ‖d‖ := norm_nonneg _
    have hright_nonneg : 0 ≤ ((5 : ℝ) / 4) * r := by positivity
    nlinarith [hdir_le_fiveQuarter, hd_nonneg, hright_nonneg]
  calc
    ‖method (k + 1) - xStar‖ ≤ ‖∇ φ T‖ / σ := hnorm_le_grad
    _ ≤ ((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ) := hgrad_over_sigma
    _ ≤ ((L : ℝ) / (2 * σ)) * (((5 : ℝ) / 4) * r) ^ (2 : ℕ) := by
      have hcoeff_nonneg : 0 ≤ (L : ℝ) / (2 * σ) := by positivity
      exact mul_le_mul_of_nonneg_left hdir_sq hcoeff_nonneg
    _ ≤ ((L : ℝ) / σ) * r ^ (2 : ℕ) := by
      have hmain_nonneg : 0 ≤ ((L : ℝ) / σ) * r ^ (2 : ℕ) := by positivity
      calc
        ((L : ℝ) / (2 * σ)) * (((5 : ℝ) / 4) * r) ^ (2 : ℕ) =
            (25 / 32 : ℝ) * (((L : ℝ) / σ) * r ^ (2 : ℕ)) := by
              field_simp [hσ.ne']
              ring
        _ ≤ ((L : ℝ) / σ) * r ^ (2 : ℕ) := by
          nlinarith
    _ = ((L : ℝ) / σ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
      simp [r]

/-- Helper for Proposition 4.4.10: a quadratic recurrence with `c * r 0 < 1` forces the whole
tail to converge to `0`. -/
private lemma quadraticTailTendstoZero_of_scaled_lt_one
    {r : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hr_nonneg : ∀ j : ℕ, 0 ≤ r j)
    (hquad : ∀ j : ℕ, r (j + 1) ≤ c * (r j) ^ (2 : ℕ))
    (hscaled0 : c * r 0 < 1) :
    Filter.Tendsto r Filter.atTop (nhds 0) := by
  have hsuperlinear : HasEventuallySuperlinearErrorBound r 0 c 0 :=
    HasEventuallySuperlinearErrorBound.of_quadratic_bound hquad
  have hscaled_nonneg : 0 ≤ c * r 0 := mul_nonneg hc.le (hr_nonneg 0)
  have hpow :
      Filter.Tendsto (fun j : ℕ ↦ (c * r 0) ^ (2 ^ j : ℕ)) Filter.atTop (nhds 0) := by
    -- The repeated-squaring majorant tends to `0` because `0 ≤ c * r 0 < 1`.
    exact
      (tendsto_pow_atTop_nhds_zero_of_lt_one hscaled_nonneg hscaled0).comp
        (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 2 by decide))
  have hmajorant :
      Filter.Tendsto (fun j : ℕ ↦ (1 / c) * (c * r 0) ^ (2 ^ j : ℕ)) Filter.atTop (nhds 0) := by
    -- Multiplying the repeated-squaring term by the constant `1 / c` preserves convergence.
    simpa using tendsto_const_nhds.mul hpow
  have htail :
      ∀ j : ℕ, r j ≤ (1 / c) * (c * r 0) ^ (2 ^ j : ℕ) := by
    -- The Chapter 1 quadratic-tail owner already provides the repeated-squaring majorant.
    intro j
    simpa using
      HasEventuallySuperlinearErrorBound.quadratic_tail_bound hsuperlinear hr_nonneg hc 0 j
  -- Squeeze the nonnegative error sequence by the vanishing repeated-squaring majorant.
  exact squeeze_zero hr_nonneg htail hmajorant

/-- Helper for Proposition 4.4.10: if a scalar function `g` is `m`-strongly monotone and vanishes
at `h`, then the distance from `h` to the full-step parameter `1` is controlled by `|g 1| / m`. -/
private lemma abs_sub_le_div_of_strong_mono_zero
    {g : ℝ → ℝ} {m h : ℝ}
    (hm : 0 < m)
    (hmono : ∀ {s t : ℝ}, s ≤ t → m * (t - s) ≤ g t - g s)
    (hh : g h = 0) :
    |1 - h| ≤ |g 1| / m := by
  rcases le_total h 1 with hle | hge
  · -- If the exact minimizer lies before the full step, monotonicity compares `g h = 0` to `g 1`.
    have hbound : m * (1 - h) ≤ g 1 := by
      have := hmono hle
      simpa [hh, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using this
    have hleft_nonneg : 0 ≤ m * (1 - h) := mul_nonneg hm.le (sub_nonneg.mpr hle)
    have hg1_nonneg : 0 ≤ g 1 := le_trans hleft_nonneg hbound
    have hdiv : 1 - h ≤ g 1 / m := by
      apply (le_div_iff₀ hm).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbound
    rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonneg hg1_nonneg]
    exact hdiv
  · -- If the minimizer lies beyond the full step, the same monotonicity bound controls `-g 1`.
    have hbound : m * (h - 1) ≤ -g 1 := by
      have := hmono hge
      have htmp : m * (h - 1) ≤ 0 - g 1 := by
        simpa [hh, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using this
      simpa using htmp
    have hleft_nonneg : 0 ≤ m * (h - 1) := mul_nonneg hm.le (sub_nonneg.mpr hge)
    have hg1_nonpos : g 1 ≤ 0 := by
      have : 0 ≤ -g 1 := le_trans hleft_nonneg hbound
      linarith
    have hdiv : h - 1 ≤ (-g 1) / m := by
      apply (le_div_iff₀ hm).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbound
    have habs_l : |1 - h| = h - 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hge)]
      ring
    rw [habs_l, abs_of_nonpos hg1_nonpos]
    simpa using hdiv

/-- Helper for Proposition 4.4.10: if a scalar function `g` is `m`-strongly monotone and vanishes
at `h`, then every comparison point `a` controls its distance to `h` by `|g a| / m`. -/
private lemma abs_sub_le_div_of_strong_mono_zero_at
    {g : ℝ → ℝ} {m h a : ℝ}
    (hm : 0 < m)
    (hmono : ∀ {s t : ℝ}, s ≤ t → m * (t - s) ≤ g t - g s)
    (hh : g h = 0) :
    |a - h| ≤ |g a| / m := by
  rcases le_total h a with hle | hge
  · -- If the reference point lies after the root, strong monotonicity compares `g h = 0` to `g a`.
    have hbound : m * (a - h) ≤ g a := by
      have := hmono hle
      simpa [hh, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using this
    have hleft_nonneg : 0 ≤ m * (a - h) := mul_nonneg hm.le (sub_nonneg.mpr hle)
    have hga_nonneg : 0 ≤ g a := le_trans hleft_nonneg hbound
    have hdiv : a - h ≤ g a / m := by
      apply (le_div_iff₀ hm).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbound
    rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonneg hga_nonneg]
    exact hdiv
  · -- If the reference point lies before the root, the same monotonicity bound controls `-g a`.
    have hbound : m * (h - a) ≤ -g a := by
      have := hmono hge
      have htmp : m * (h - a) ≤ 0 - g a := by
        simpa [hh, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using this
      simpa using htmp
    have hleft_nonneg : 0 ≤ m * (h - a) := mul_nonneg hm.le (sub_nonneg.mpr hge)
    have hga_nonpos : g a ≤ 0 := by
      have : 0 ≤ -g a := le_trans hleft_nonneg hbound
      linarith
    have hdiv : h - a ≤ (-g a) / m := by
      apply (le_div_iff₀ hm).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbound
    have habs_l : |a - h| = h - a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hge)]
      ring
    rw [habs_l, abs_of_nonpos hga_nonpos]
    simpa using hdiv

/-- Helper for Proposition 4.4.10: an exact line-search minimizer on `[0, ∞)` has its distance to
any comparison point `a` controlled by the derivative at `a` once the ray derivative is
`m`-strongly monotone and points downhill at `0`. -/
private lemma rayExactLineSearch_absSub_le_absDeriv_div_curvature
    {ψ ψ' : ℝ → ℝ} {h m a : ℝ}
    (hh_nonneg : h ∈ Set.Ici (0 : ℝ))
    (hmin : IsMinOn ψ (Set.Ici (0 : ℝ)) h)
    (hm : 0 < m)
    (hderiv : ∀ t : ℝ, HasDerivAt ψ (ψ' t) t)
    (hderiv0_neg : ψ' 0 < 0)
    (hmono : ∀ {s t : ℝ}, s ≤ t → m * (t - s) ≤ ψ' t - ψ' s) :
    |a - h| ≤ |ψ' a| / m := by
  have hh_ge : 0 ≤ h := hh_nonneg
  have hpos : 0 < h := by
    by_contra hnot
    have hh0 : h = 0 := le_antisymm (le_of_not_gt hnot) hh_ge
    have hlocal : IsLocalMinOn ψ (Set.Ici (0 : ℝ)) 0 := by
      simpa [hh0] using hmin.localize
    have hdir : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) (0 : ℝ) := by
      -- The positive ray direction stays inside `[0, ∞)` along the whole segment from `0` to `1`.
      refine mem_posTangentConeAt_of_segment_subset ?_
      intro x hx
      have hx' : x ∈ segment ℝ (0 : ℝ) 1 := by
        simpa using hx
      exact (segment_subset_Icc (show (0 : ℝ) ≤ 1 by norm_num) hx').1
    have hnonneg : 0 ≤ ψ' 0 := by
      -- A boundary minimizer would force a nonnegative one-sided derivative, contradicting descent.
      have hderivWithin : HasDerivWithinAt ψ (ψ' 0) (Set.Ici (0 : ℝ)) 0 :=
        (hderiv 0).hasDerivWithinAt
      have := hlocal.hasFDerivWithinAt_nonneg hderivWithin.hasFDerivWithinAt hdir
      simpa using this
    linarith
  have hnhdsSet : Set.Ici (0 : ℝ) ∈ nhdsSet (Set.Ici h) := Ici_mem_nhdsSet_Ici hpos
  rw [mem_nhdsSet_iff_forall] at hnhdsSet
  have hnhds : Set.Ici (0 : ℝ) ∈ nhds h := hnhdsSet h (by simp)
  have hlocal : IsLocalMin ψ h := hmin.isLocalMin hnhds
  have hroot : ψ' h = 0 := IsLocalMin.hasDerivAt_eq_zero hlocal (hderiv h)
  -- Once the minimizer is interior, the strong monotonicity estimate reduces the problem to a
  -- pure scalar root-comparison inequality at the chosen comparison point `a`.
  exact abs_sub_le_div_of_strong_mono_zero_at hm hmono hroot

/-- Helper for Proposition 4.4.10: an exact line-search minimizer on `[0, ∞)` has its distance to
the full-step parameter `1` controlled by the endpoint derivative once the ray derivative is
`m`-strongly monotone and points downhill at `0`. -/
private lemma rayExactLineSearch_absOneSub_le_absDerivOne_div_curvature
    {ψ ψ' : ℝ → ℝ} {h m : ℝ}
    (hh_nonneg : h ∈ Set.Ici (0 : ℝ))
    (hmin : IsMinOn ψ (Set.Ici (0 : ℝ)) h)
    (hm : 0 < m)
    (hderiv : ∀ t : ℝ, HasDerivAt ψ (ψ' t) t)
    (hderiv0_neg : ψ' 0 < 0)
    (hmono : ∀ {s t : ℝ}, s ≤ t → m * (t - s) ≤ ψ' t - ψ' s) :
    |1 - h| ≤ |ψ' 1| / m := by
  -- Reuse the arbitrary-reference version at the textbook comparison point `a = 1`.
  simpa using
    (rayExactLineSearch_absSub_le_absDeriv_div_curvature
      hh_nonneg hmin hm hderiv hderiv0_neg hmono :
        |(1 : ℝ) - h| ≤ |ψ' 1| / m)

/-- Helper for Proposition 4.4.10: the affine line `s ↦ x + s • d` has derivative `d`. -/
private theorem line_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar multiple and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Proposition 4.4.10: scalarizing the gradient along an affine line differentiates to
the Hessian pairing in the line direction. -/
private theorem scalarizedGradientLine_hasDerivAt
    {φ : E → ℝ} (hφ_C2 : ContDiff ℝ 2 φ) (x d u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ φ (x + s • d)) u)
      (inner ℝ (hessian φ (x + t • d) d) u) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hφ_C2_at : ContDiffAt ℝ 2 φ (x + t • d) := hφ_C2.contDiffAt (x + t • d)
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ φ) (x + t • d) := by
    -- A `C²` objective has a differentiable Fréchet derivative field.
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ φ) (x + t • d) :=
      hφ_C2_at.fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ φ) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ φ (x + s • d))
        ((hessian φ (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the derivative of the gradient with the affine-line derivative.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let ℓ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ ℓ (∇ φ (x + s • d)))
        (ℓ.comp ((hessian φ (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose the gradient line with the scalar functional `v ↦ ⟪v, u⟫`.
    simpa [ℓ] using ((ℓ.hasFDerivAt).comp t hgradLine)
  simpa [ℓ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Proposition 4.4.10: away from the degenerate zero-direction branch, exact line
search keeps the accepted step size within `q_k / (2 - q_k)` of the full Newton step. -/
private lemma modifiedNewtonStepSizeAbsSlack_le_characteristicRatio
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ}
    (hk : InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k)
    (hd : method.toMethod.searchDirection k ≠ 0) :
    |1 - method.toMethod.stepSize k| ≤
      modifiedNewtonCharacteristicQuantity σ L (method k) xStar /
        (2 - modifiedNewtonCharacteristicQuantity σ L (method k) xStar) := by
  let x := method k
  let d := method.toMethod.searchDirection k
  let h := method.toMethod.stepSize k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let r : ℝ := ‖x - xStar‖
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L x xStar
  let ψ : ℝ → ℝ := fun t ↦ φ (x - t • d)
  let ψ' : ℝ → ℝ := fun t ↦ -inner ℝ (∇ φ (x - t • d)) d
  have hφ_C2 : ContDiff ℝ 2 φ := hφ_hessian.contDiff
  have hφ_C1 : ContDiff ℝ 1 φ := hφ_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hφ_diff : DifferentiableOn ℝ φ (Set.univ : Set E) := by
    intro y hy
    exact (hφ_C1.differentiable_one y).differentiableWithinAt
  have hkq : q < 1 := by
    simpa [q, x] using hk
  have hq_nonneg : 0 ≤ q := by
    have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
    exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
  have hq_def : q = ((L : ℝ) / σ) * r := by
    -- Keep the characteristic quantity in the normalized `((L / σ) * r)` form for later algebra.
    simp [q, r, modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  have hq_def : q = ((L : ℝ) / σ) * r := by
    -- Keep the characteristic quantity in the normalized `((L / σ) * r)` form for later algebra.
    simp [q, r, modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc,
      mul_comm, mul_left_comm]
  have hh_nonneg : h ∈ Set.Ici (0 : ℝ) := by
    simpa [h] using method.stepSize_nonneg k
  have hmin : IsMinOn ψ (Set.Ici (0 : ℝ)) h := by
    simpa [ψ, x, d, h] using method.exactLineSearchAlong k
  have hderiv : ∀ t : ℝ, HasDerivAt ψ (ψ' t) t := by
    intro t
    have hφ_C1_at : ContDiffAt ℝ 1 φ (x + t • (-d)) := hφ_C1.contDiffAt (x + t • (-d))
    have hgradAt : HasGradientAt φ (∇ φ (x + t • (-d))) (x + t • (-d)) := by
      exact (hφ_C1_at.differentiableAt one_ne_zero).hasGradientAt
    have hline :
        HasDerivAt (fun s : ℝ ↦ φ (x + s • (-d)))
          (inner ℝ (∇ φ (x + t • (-d))) (-d)) t := by
      -- Compose the ambient derivative of `φ` with the affine Newton ray.
      simpa using
        (hgradAt.hasFDerivAt.comp t (line_hasDerivAt x (-d) t).hasFDerivAt).hasDerivAt
    simpa [ψ, ψ', sub_eq_add_neg] using hline
  have hnewton_eq : hessian φ x d = ∇ φ x := by
    -- Expanding the Newton search direction recovers the linearized gradient equation.
    change
      (fderiv ℝ (∇ φ) ↑(method.toMethod.x k))
          ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
              (method.toMethod.x k).property).symm)
            (∇ φ ↑(method.toMethod.x k))) =
        ∇ φ ↑(method.toMethod.x k)
    exact
      ContinuousLinearEquiv.apply_symm_apply
        ((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
          (method.toMethod.x k).property)
        (∇ φ ↑(method.toMethod.x k))
  have hUniv_nonempty : (interior (Set.univ : Set E)).Nonempty := by
    simp
  have hcont : ContinuousOn φ (Set.univ : Set E) := hφ_C2.continuous.continuousOn
  have hC2 : ContDiffOn ℝ 2 φ (interior (Set.univ : Set E)) := by
    simpa using hφ_C2.contDiffOn
  have hbound :
      σ • (1 : E →L[ℝ] E) ≤ hessian φ x := by
    -- Whole-space strong convexity gives the Hessian Loewner lower bound at the current iterate.
    have hiff :=
      (strongConvexOn_iff_hessian_lower_bound
        hσ convex_univ hUniv_nonempty hcont hC2).1 hφ_strong
    simpa using hiff x (by simp)
  have hcurvature_lower :
      σ * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ (hessian φ x d) d := by
    -- Convert the Loewner bound into the scalar curvature along the Newton ray.
    exact
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hσ hC2 (by simp : x ∈ interior (Set.univ : Set E))).1 hbound d
  have hderiv0_neg : ψ' 0 < 0 := by
    -- The Newton direction is a strict descent direction because its curvature is positive.
    have hd_norm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd
    have hcurvature_pos : 0 < inner ℝ (hessian φ x d) d := by
      have hleft_pos : 0 < σ * ‖d‖ ^ (2 : ℕ) := by
        positivity
      exact lt_of_lt_of_le hleft_pos hcurvature_lower
    have hψ0 :
        ψ' 0 = -inner ℝ (hessian φ x d) d := by
      simp [ψ', hnewton_eq]
    rw [hψ0]
    linarith
  have hstrong_mono :
      ∀ {s t : ℝ}, s ≤ t → (σ * ‖d‖ ^ (2 : ℕ)) * (t - s) ≤ ψ' t - ψ' s := by
    intro s t hst
    have hgrad_mono :=
      (strongConvexOn_iff_gradient_monotone convex_univ hφ_diff).1 hφ_strong
    have hmono := hgrad_mono (x - s • d) (x - t • d) (by simp) (by simp)
    have hpair :
        σ * ‖(x - s • d) - (x - t • d)‖ ^ (2 : ℕ) ≤
          inner ℝ (∇ φ (x - s • d) - ∇ φ (x - t • d)) ((x - s • d) - (x - t • d)) := by
      simpa [gradientWithin, fderivWithin_univ] using hmono
    have hpair' :
        σ * (((t - s) * ‖d‖) ^ (2 : ℕ)) ≤
          (t - s) * (ψ' t - ψ' s) := by
      -- Rewrite the gradient monotonicity pairing along the affine Newton ray.
      have hdiff :
          (x - s • d) - (x - t • d) = (t - s) • d := by
        calc
          (x - s • d) - (x - t • d) = (x + -x) + (t • d + -(s • d)) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = t • d + -(s • d) := by simp
          _ = (t - s) • d := by
            simpa [sub_eq_add_neg, add_smul]
      rw [hdiff] at hpair
      have hpair_smul :
          σ * (((t - s) * ‖d‖) ^ (2 : ℕ)) ≤
            (t - s) * inner ℝ (∇ φ (x - s • d) - ∇ φ (x - t • d)) d := by
        simpa [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hst), pow_two,
          real_inner_smul_right, mul_assoc, mul_left_comm, mul_comm] using hpair
      have hpair_split :
          σ * (((t - s) * ‖d‖) ^ (2 : ℕ)) ≤
            (t - s) *
              (inner ℝ (∇ φ (x - s • d)) d - inner ℝ (∇ φ (x - t • d)) d) := by
        simpa [inner_sub_left] using hpair_smul
      simpa [ψ', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hpair_split
    by_cases hts : t = s
    · subst hts
      simp
    · have hst_ne : s ≠ t := by
        intro hst_eq
        exact hts hst_eq.symm
      have hts_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hst hst_ne)
      have hpair_div :
          (t - s) * ((σ * ‖d‖ ^ (2 : ℕ)) * (t - s)) ≤ (t - s) * (ψ' t - ψ' s) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hpair'
      have hdiv := (mul_le_mul_iff_of_pos_left hts_pos).mp hpair_div
      simpa [mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hslack_raw :
      |1 - h| ≤ |ψ' 1| / (σ * ‖d‖ ^ (2 : ℕ)) := by
    -- The scalar exact-line-search lemma applies to the Newton ray with curvature
    -- `σ * ‖d‖²`.
    exact
      rayExactLineSearch_absOneSub_le_absDerivOne_div_curvature
        hh_nonneg hmin (show 0 < σ * ‖d‖ ^ (2 : ℕ) by positivity)
        hderiv hderiv0_neg hstrong_mono
  have hgrad_trial :
      ‖∇ φ T‖ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
    -- Control the endpoint derivative by the quadratic full-trial gradient estimate.
    simpa [T, d] using modifiedNewtonFullTrialGradientNormLeQuadratic hφ_hessian method k
  have hpsi_one :
      ψ' 1 = -inner ℝ (∇ φ T) d := by
    simp [ψ', T, x, d, NewtonSystem.step_def, DampedNewton.Method.searchDirection]
  have hratio :
      |ψ' 1| / (σ * ‖d‖ ^ (2 : ℕ)) ≤ q / (2 - q) := by
    have hden_pos : 0 < σ * ‖d‖ ^ (2 : ℕ) := by
      positivity
    have hdir :
        ‖d‖ ≤ (1 + q / 2) * r := by
      -- Reuse the existing direction bound in normalized local notation.
      simpa [d, q, r, x] using
        modifiedNewtonSearchDirectionNorm_le_one_add_halfCharacteristic_mulError
          hσ hφ_strong hφ_hessian hxStar method
    have hendpoint :
        |ψ' 1| / (σ * ‖d‖ ^ (2 : ℕ)) ≤ ((L : ℝ) / (2 * σ)) * ‖d‖ := by
      have habs_inner :
          |ψ' 1| ≤ ‖∇ φ T‖ * ‖d‖ := by
        rw [hpsi_one]
        simpa using (abs_real_inner_le_norm (∇ φ T) d)
      have hscaled :
          |ψ' 1| ≤ (((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ)) * ‖d‖ := by
        exact habs_inner.trans <| by
          gcongr
      have hcoeff :
          (((L : ℝ) / (2 * σ)) * ‖d‖) * (σ * ‖d‖ ^ (2 : ℕ)) =
            (((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ)) * ‖d‖ := by
        field_simp [hσ.ne']
      have hnum :
          |ψ' 1| ≤ (((L : ℝ) / (2 * σ)) * ‖d‖) * (σ * ‖d‖ ^ (2 : ℕ)) := by
        calc
          |ψ' 1| ≤ (((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ)) * ‖d‖ := hscaled
          _ = (((L : ℝ) / (2 * σ)) * ‖d‖) * (σ * ‖d‖ ^ (2 : ℕ)) := by
            rw [hcoeff]
      exact (div_le_iff₀ hden_pos).2 hnum
    calc
      |ψ' 1| / (σ * ‖d‖ ^ (2 : ℕ)) ≤ ((L : ℝ) / (2 * σ)) * ‖d‖ := hendpoint
      _ ≤ ((L : ℝ) / (2 * σ)) * ((1 + q / 2) * r) := by
        gcongr
      _ = q / 2 + q ^ (2 : ℕ) / 4 := by
        rw [hq_def]
        ring
      _ ≤ q / (2 - q) := by
        have hden_pos : 0 < 2 - q := by linarith
        refine (le_div_iff₀ hden_pos).2 ?_
        nlinarith
  exact hslack_raw.trans hratio

/-- Helper for Proposition 4.4.10: under the actual local region hypothesis `q_k < 1`, the
accepted modified-Newton step should satisfy the sharp quadratic error recurrence. -/
private lemma
    modifiedNewtonAcceptedStepErrorLeQuadratic_of_characteristic_le_twoSqrtTwoSubTwo
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ}
    (hkq :
      modifiedNewtonCharacteristicQuantity σ L (method k) xStar ≤
        2 * (Real.sqrt (2 : ℝ) - 1)) :
    ‖method (k + 1) - xStar‖ ≤
      ((L : ℝ) / σ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let r : ℝ := ‖method k - xStar‖
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method k) xStar
  let hφ_C1 : ContDiff ℝ 1 φ := hφ_hessian.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hdiff : Differentiable ℝ φ := fun y ↦ hφ_C1.differentiable_one y
  have hxStar_argmin : xStar ∈ constrainedArgmin (Set.univ : Set E) φ := by
    exact mem_constrainedArgmin_iff.mpr ⟨by simp, hxStar⟩
  have hpolyak :
      φ T - φ xStar ≤ (1 / (2 * σ)) * ‖∇ φ T‖ ^ (2 : ℕ) :=
    StrongConvexOn.sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn
      (by
        exact mem_strongConvexClass_iff.mpr ⟨hσ, hφ_strong⟩)
      hdiff hxStar_argmin
  have hobjective :
      φ (method (k + 1)) ≤ φ T :=
    modifiedNewtonObjective_le_fullTrial method k
  have hgap_upper :
      φ (method (k + 1)) - φ xStar ≤ (1 / (2 * σ)) * ‖∇ φ T‖ ^ (2 : ℕ) := by
    -- Compare the accepted point with the full Newton trial in objective value.
    linarith
  have hgap_lower :
      (σ / 2) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        φ (method (k + 1)) - φ xStar := by
    -- Strong convexity turns the accepted-point objective gap into a quadratic distance bound.
    simpa using
      (objectiveGap_ge_halfSigma_mul_sqDistToMinimizer hφ_strong hφ_hessian hxStar :
        (σ / 2) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          φ (method (k + 1)) - φ xStar)
  have hnorm_sq :
      (σ * ‖method (k + 1) - xStar‖) ^ (2 : ℕ) ≤ ‖∇ φ T‖ ^ (2 : ℕ) := by
    -- Combine the lower and upper gap estimates into a squared norm inequality.
    have hleft :
        σ ^ (2 : ℕ) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          (2 * σ) * (φ (method (k + 1)) - φ xStar) := by
      nlinarith [hgap_lower]
    have hright :
        (2 * σ) * (φ (method (k + 1)) - φ xStar) ≤ ‖∇ φ T‖ ^ (2 : ℕ) := by
      have hmul :=
        mul_le_mul_of_nonneg_left hgap_upper (show 0 ≤ 2 * σ by positivity)
      simpa [hσ.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    have hraw :
        σ ^ (2 : ℕ) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤ ‖∇ φ T‖ ^ (2 : ℕ) :=
      hleft.trans hright
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hraw
  have hnorm_le_grad :
      ‖method (k + 1) - xStar‖ ≤ ‖∇ φ T‖ / σ := by
    have hσnorm_nonneg : 0 ≤ σ * ‖method (k + 1) - xStar‖ := by positivity
    have hgrad_nonneg : 0 ≤ ‖∇ φ T‖ := norm_nonneg _
    have hσnorm_le : σ * ‖method (k + 1) - xStar‖ ≤ ‖∇ φ T‖ := by
      have hsq := (sq_le_sq).1 hnorm_sq
      simpa [abs_of_nonneg hσnorm_nonneg, abs_of_nonneg hgrad_nonneg] using hsq
    exact (le_div_iff₀ hσ).2 <| by simpa [mul_comm] using hσnorm_le
  have hgrad_trial :
      ‖∇ φ T‖ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) :=
    modifiedNewtonFullTrialGradientNormLeQuadratic hφ_hessian method k
  have hgrad_over_sigma :
      ‖∇ φ T‖ / σ ≤ ((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ) := by
    -- Divide the trial gradient estimate by `σ`.
    have hcoeff :
        ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) =
          (((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ)) * σ := by
      field_simp [hσ.ne']
    exact (div_le_iff₀ hσ).2 <| by
      calc
        ‖∇ φ T‖ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := hgrad_trial
        _ = (((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ)) * σ := hcoeff
  have hq_nonneg : 0 ≤ q := by
    have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
    exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
  have hq_threshold : q ≤ 2 * (Real.sqrt (2 : ℝ) - 1) := by
    simpa [q] using hkq
  have hdir_le :
      ‖d‖ ≤ (1 + q / 2) * r := by
    -- Reuse the direction bound in the local characteristic notation.
    simpa [d, q, r] using
      modifiedNewtonSearchDirectionNorm_le_one_add_halfCharacteristic_mulError
        hσ hφ_strong hφ_hessian hxStar method
  have hdir_sq :
      ‖d‖ ^ (2 : ℕ) ≤ ((1 + q / 2) * r) ^ (2 : ℕ) := by
    have hd_nonneg : 0 ≤ ‖d‖ := norm_nonneg _
    have hright_nonneg : 0 ≤ (1 + q / 2) * r := by positivity
    nlinarith [hdir_le, hd_nonneg, hright_nonneg]
  have hfactor_le : (1 / 2 : ℝ) * (1 + q / 2) ^ (2 : ℕ) ≤ 1 := by
    -- The explicit threshold `q ≤ 2 (√2 - 1)` is exactly the range where the objective route
    -- closes the quadratic error estimate.
    have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ (2 : ℕ) = 2 := by
      rw [pow_two]
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
    nlinarith [hq_nonneg, hq_threshold, hsqrt_sq]
  calc
    ‖method (k + 1) - xStar‖ ≤ ‖∇ φ T‖ / σ := hnorm_le_grad
    _ ≤ ((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ) := hgrad_over_sigma
    _ ≤ ((L : ℝ) / (2 * σ)) * ((1 + q / 2) * r) ^ (2 : ℕ) := by
      have hcoeff_nonneg : 0 ≤ (L : ℝ) / (2 * σ) := by positivity
      exact mul_le_mul_of_nonneg_left hdir_sq hcoeff_nonneg
    _ = ((1 / 2 : ℝ) * (1 + q / 2) ^ (2 : ℕ)) * (((L : ℝ) / σ) * r ^ (2 : ℕ)) := by
      field_simp [hσ.ne']
    _ ≤ ((L : ℝ) / σ) * r ^ (2 : ℕ) := by
      have hmain_nonneg : 0 ≤ ((L : ℝ) / σ) * r ^ (2 : ℕ) := by positivity
      nlinarith
    _ = ((L : ℝ) / σ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
      simp [r]

/-- Helper for Proposition 4.4.10: in the local region, the accepted modified-Newton step still
satisfies a coarse quadratic error estimate with coefficient `2 * (L / σ)`. -/
private lemma modifiedNewtonAcceptedStepErrorLeTwoMulQuadratic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ}
    (hk : InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k) :
    ‖method (k + 1) - xStar‖ ≤
      (2 * ((L : ℝ) / σ)) * ‖method k - xStar‖ ^ (2 : ℕ) := by
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let r : ℝ := ‖method k - xStar‖
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method k) xStar
  by_cases hd : d = 0
  · let x := method k
    let hφ_C1 : ContDiff ℝ 1 φ := hφ_hessian.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hdiff : Differentiable ℝ φ := fun y ↦ hφ_C1.differentiable_one y
    have hxStar_argmin : xStar ∈ constrainedArgmin (Set.univ : Set E) φ := by
      exact mem_constrainedArgmin_iff.mpr ⟨by simp, hxStar⟩
    have hgrad_eq :
        ∇ φ x = 0 := by
      -- A vanishing search direction means the current gradient already vanishes.
      have happly_zero :=
        congrArg
          (((fderiv ℝ (∇ φ) x).toContinuousLinearEquivOfDetNeZero (method.toMethod.x k).property) :
            E → E)
          hd
      simpa [x, d, DampedNewton.Method.searchDirection] using happly_zero
    have hgap_upper :
        φ x - φ xStar ≤ (1 / (2 * σ)) * ‖∇ φ x‖ ^ (2 : ℕ) :=
      StrongConvexOn.sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn
        (by
          exact mem_strongConvexClass_iff.mpr ⟨hσ, hφ_strong⟩)
        hdiff hxStar_argmin
    have hgap_nonneg : 0 ≤ φ x - φ xStar := by
      -- Every iterate lies above the global minimum value at `xStar`.
      simpa [x] using modifiedNewtonObjectiveGap_nonneg hxStar method k
    have hgap_eq : φ x = φ xStar := by
      -- The Polyak upper bound and minimizer lower bound force equality of objective values.
      have hgap_zero : φ x - φ xStar = 0 := by
        have hgap_upper_zero : φ x - φ xStar ≤ 0 := by
          simpa [hgrad_eq] using hgap_upper
        linarith
      linarith
    have hx_min : IsMinOn φ Set.univ x := by
      -- Matching the minimizer value shows that the current iterate is itself a global minimizer.
      rw [isMinOn_iff]
      intro y hy
      have hstar_min := (isMinOn_iff.mp hxStar) y hy
      linarith
    have hx_eq : x = xStar := by
      -- Strong convexity gives uniqueness of the global minimizer.
      exact StrongConvexOn.eq_of_isMinOn hφ_strong hσ (by simp [x]) hx_min (by simp) hxStar
    have hnext_eq : method (k + 1) = xStar := by
      -- With zero search direction, the accepted step stays at the current minimizer.
      calc
        method (k + 1) = method k - method.toMethod.stepSize k • d := by
          simpa [d] using method.succ_eq_sub_stepSize_smul_searchDirection k
        _ = method k := by simp [hd]
        _ = xStar := hx_eq
    have hrhs_nonneg :
        0 ≤ (2 * ((L : ℝ) / σ)) * ‖method k - xStar‖ ^ (2 : ℕ) := by
      positivity
    simpa [hnext_eq] using hrhs_nonneg
  · have hq_lt : q < 1 := by
      simpa [q] using hk
    have hq_nonneg : 0 ≤ q := by
      have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
      exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
    have hr_nonneg : 0 ≤ r := by
      exact norm_nonneg _
    have hq_def : q = ((L : ℝ) / σ) * r := by
      -- Keep the characteristic quantity in the normalized `((L / σ) * r)` form.
      simp [q, r, modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc,
        mul_left_comm, mul_comm]
    have hstep_eq :
        method (k + 1) - xStar =
          (T - xStar) + (1 - method.toMethod.stepSize k) • d := by
      -- Split the accepted step into the full Newton trial plus the step-size slack term.
      calc
        method (k + 1) - xStar = (method k - method.toMethod.stepSize k • d) - xStar := by
          simpa [d] using congrArg (fun z : E ↦ z - xStar) (method.succ_eq_sub_stepSize_smul_searchDirection k)
        _ = (T - xStar) + (1 - method.toMethod.stepSize k) • d := by
          simp [T, d, NewtonSystem.step_def, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            smul_sub, sub_smul]
    have htrial :
        ‖T - xStar‖ ≤ ((L : ℝ) / (2 * σ)) * r ^ (2 : ℕ) := by
      -- Reuse the quadratic full-trial estimate at the current admissible Newton point.
      simpa [T, r] using
        (modifiedNewtonStepErrorLeQuadratic
          hσ hφ_strong hφ_hessian hxStar (method.toMethod.x k))
    have hslack :
        |1 - method.toMethod.stepSize k| ≤ q / (2 - q) := by
      -- The exact line-search slack is already controlled by the local characteristic ratio.
      simpa [q] using
        modifiedNewtonStepSizeAbsSlack_le_characteristicRatio
          hσ hφ_strong hφ_hessian hxStar method hk hd
    have hdir_le :
        ‖d‖ ≤ (1 + q / 2) * r := by
      -- Reuse the standard direction bound inside the normalized local notation.
      simpa [d, q, r] using
        modifiedNewtonSearchDirectionNorm_le_one_add_halfCharacteristic_mulError
          hσ hφ_strong hφ_hessian hxStar method
    have hslack_term :
        ‖(1 - method.toMethod.stepSize k) • d‖ ≤
          (3 / 2 : ℝ) * (((L : ℝ) / σ) * r ^ (2 : ℕ)) := by
      rw [norm_smul]
      have hratio_nonneg : 0 ≤ q / (2 - q) := by
        positivity
      have hmul :
          |1 - method.toMethod.stepSize k| * ‖d‖ ≤
            (q / (2 - q)) * ((1 + q / 2) * r) := by
        exact mul_le_mul hslack hdir_le (norm_nonneg _) hratio_nonneg
      calc
        |1 - method.toMethod.stepSize k| * ‖d‖ ≤
            (q / (2 - q)) * ((1 + q / 2) * r) := hmul
        _ ≤ (3 / 2 : ℝ) * q * r := by
          nlinarith
        _ = (3 / 2 : ℝ) * (((L : ℝ) / σ) * r ^ (2 : ℕ)) := by
          rw [hq_def, pow_two]
          ring
    calc
      ‖method (k + 1) - xStar‖ = ‖(T - xStar) + (1 - method.toMethod.stepSize k) • d‖ := by
        rw [hstep_eq]
      _ ≤ ‖T - xStar‖ + ‖(1 - method.toMethod.stepSize k) • d‖ := norm_add_le _ _
      _ ≤ ((L : ℝ) / (2 * σ)) * r ^ (2 : ℕ) +
            ((3 / 2 : ℝ) * (((L : ℝ) / σ) * r ^ (2 : ℕ))) := by
          gcongr
      _ = (2 * ((L : ℝ) / σ)) * r ^ (2 : ℕ) := by
          ring
      _ = (2 * ((L : ℝ) / σ)) * ‖method k - xStar‖ ^ (2 : ℕ) := by
          simp [r]

/-- Helper for Proposition 4.4.10: the existing full-trial objective route yields the explicit
local characteristic model
`q_(k+1) ≤ (1 / 2) * (1 + q_k / 2)^2 * q_k^2` inside `q_k < 1`. -/
private lemma modifiedNewtonCharacteristicSucc_le_localQuadraticModel
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ}
    (hk : InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k) :
    modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar ≤
      ((1 / 2 : ℝ) *
          (1 + modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) ^ (2 : ℕ)) *
        modifiedNewtonCharacteristicQuantity σ L (method k) xStar ^ (2 : ℕ) := by
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let r : ℝ := ‖method k - xStar‖
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method k) xStar
  let hφ_C1 : ContDiff ℝ 1 φ := hφ_hessian.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hdiff : Differentiable ℝ φ := fun y ↦ hφ_C1.differentiable_one y
  have hxStar_argmin : xStar ∈ constrainedArgmin (Set.univ : Set E) φ := by
    exact mem_constrainedArgmin_iff.mpr ⟨by simp, hxStar⟩
  have hkq : q < 1 := by
    simpa [q] using hk
  have hpolyak :
      φ T - φ xStar ≤ (1 / (2 * σ)) * ‖∇ φ T‖ ^ (2 : ℕ) :=
    StrongConvexOn.sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn
      (by
        exact mem_strongConvexClass_iff.mpr ⟨hσ, hφ_strong⟩)
      hdiff hxStar_argmin
  have hobjective :
      φ (method (k + 1)) ≤ φ T :=
    modifiedNewtonObjective_le_fullTrial method k
  have hgap_upper :
      φ (method (k + 1)) - φ xStar ≤ (1 / (2 * σ)) * ‖∇ φ T‖ ^ (2 : ℕ) := by
    -- Compare the accepted point with the full Newton trial in objective value.
    linarith
  have hgap_lower :
      (σ / 2) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        φ (method (k + 1)) - φ xStar := by
    -- Strong convexity turns the accepted-point objective gap into a quadratic distance bound.
    simpa using
      (objectiveGap_ge_halfSigma_mul_sqDistToMinimizer hφ_strong hφ_hessian hxStar :
        (σ / 2) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          φ (method (k + 1)) - φ xStar)
  have hnorm_sq :
      (σ * ‖method (k + 1) - xStar‖) ^ (2 : ℕ) ≤ ‖∇ φ T‖ ^ (2 : ℕ) := by
    -- Combine the lower and upper gap estimates into a squared norm inequality.
    have hleft :
        σ ^ (2 : ℕ) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          (2 * σ) * (φ (method (k + 1)) - φ xStar) := by
      nlinarith [hgap_lower]
    have hright :
        (2 * σ) * (φ (method (k + 1)) - φ xStar) ≤ ‖∇ φ T‖ ^ (2 : ℕ) := by
      have hmul :=
        mul_le_mul_of_nonneg_left hgap_upper (show 0 ≤ 2 * σ by positivity)
      simpa [hσ.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    have hraw :
        σ ^ (2 : ℕ) * ‖method (k + 1) - xStar‖ ^ (2 : ℕ) ≤ ‖∇ φ T‖ ^ (2 : ℕ) :=
      hleft.trans hright
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hraw
  have hnorm_le_grad :
      ‖method (k + 1) - xStar‖ ≤ ‖∇ φ T‖ / σ := by
    -- Take square roots of the preceding bound after recording nonnegativity on both sides.
    have hσnorm_nonneg : 0 ≤ σ * ‖method (k + 1) - xStar‖ := by positivity
    have hgrad_nonneg : 0 ≤ ‖∇ φ T‖ := norm_nonneg _
    have hσnorm_le : σ * ‖method (k + 1) - xStar‖ ≤ ‖∇ φ T‖ := by
      have hsq := (sq_le_sq).1 hnorm_sq
      simpa [abs_of_nonneg hσnorm_nonneg, abs_of_nonneg hgrad_nonneg] using hsq
    exact (le_div_iff₀ hσ).2 <| by simpa [mul_comm] using hσnorm_le
  have hgrad_trial :
      ‖∇ φ T‖ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) :=
    modifiedNewtonFullTrialGradientNormLeQuadratic hφ_hessian method k
  have hgrad_over_sigma :
      ‖∇ φ T‖ / σ ≤ ((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ) := by
    -- Divide the trial gradient estimate by `σ`.
    have hcoeff :
        ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) =
          (((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ)) * σ := by
      field_simp [hσ.ne']
    exact (div_le_iff₀ hσ).2 <| by
      calc
        ‖∇ φ T‖ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := hgrad_trial
        _ = (((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ)) * σ := hcoeff
  have hq_nonneg : 0 ≤ q := by
    have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
    exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
  have hq_def : q = ((L : ℝ) / σ) * r := by
    -- Keep the characteristic quantity in the normalized `((L / σ) * r)` form for later algebra.
    simp [q, r, modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  have hdir_le :
      ‖d‖ ≤ (1 + q / 2) * r := by
    -- Reuse the direction bound in the local characteristic notation.
    simpa [d, q, r] using
      modifiedNewtonSearchDirectionNorm_le_one_add_halfCharacteristic_mulError
        hσ hφ_strong hφ_hessian hxStar method
  have hdir_sq :
      ‖d‖ ^ (2 : ℕ) ≤ ((1 + q / 2) * r) ^ (2 : ℕ) := by
    -- Square the direction estimate in a nonnegative context.
    have hd_nonneg : 0 ≤ ‖d‖ := norm_nonneg _
    have hright_nonneg : 0 ≤ (1 + q / 2) * r := by positivity
    nlinarith [hdir_le, hd_nonneg, hright_nonneg]
  have herror :
      ‖method (k + 1) - xStar‖ ≤
        ((1 / 2 : ℝ) * (1 + q / 2) ^ (2 : ℕ)) * (((L : ℝ) / σ) * r ^ (2 : ℕ)) := by
    -- This is the strongest one-step estimate available from the existing full-trial route.
    calc
      ‖method (k + 1) - xStar‖ ≤ ‖∇ φ T‖ / σ := hnorm_le_grad
      _ ≤ ((L : ℝ) / (2 * σ)) * ‖d‖ ^ (2 : ℕ) := hgrad_over_sigma
      _ ≤ ((L : ℝ) / (2 * σ)) * ((1 + q / 2) * r) ^ (2 : ℕ) := by
          have hcoeff_nonneg : 0 ≤ (L : ℝ) / (2 * σ) := by positivity
          exact mul_le_mul_of_nonneg_left hdir_sq hcoeff_nonneg
      _ = ((1 / 2 : ℝ) * (1 + q / 2) ^ (2 : ℕ)) * (((L : ℝ) / σ) * r ^ (2 : ℕ)) := by
          field_simp [hσ.ne']
  have hq_next_def :
      modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar =
        ((L : ℝ) / σ) * ‖method (k + 1) - xStar‖ := by
    -- Expand the next characteristic quantity in the normalized `((L / σ) * ‖e‖)` form.
    simp [modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm]
  have hcoeff_nonneg : 0 ≤ (L : ℝ) / σ := by positivity
  calc
    modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar =
        ((L : ℝ) / σ) * ‖method (k + 1) - xStar‖ := hq_next_def
    _ ≤ ((L : ℝ) / σ) *
          (((1 / 2 : ℝ) * (1 + q / 2) ^ (2 : ℕ)) * (((L : ℝ) / σ) * r ^ (2 : ℕ))) := by
          exact mul_le_mul_of_nonneg_left herror hcoeff_nonneg
    _ = ((1 / 2 : ℝ) * (1 + q / 2) ^ (2 : ℕ)) * q ^ (2 : ℕ) := by
          rw [hq_def]
          ring
    _ =
        ((1 / 2 : ℝ) *
            (1 + modifiedNewtonCharacteristicQuantity σ L (method k) xStar / 2) ^ (2 : ℕ)) *
          modifiedNewtonCharacteristicQuantity σ L (method k) xStar ^ (2 : ℕ) := by
          simp [q]

/-- Helper for Proposition 4.4.10: the quadratic Taylor model at `x` is controlled along the
segment to `xStar` by the objective value at the segment point plus the cubic Hessian-Lipschitz
remainder. -/
private lemma secondOrderTaylorModelAt_lineMap_le_objective_add_segmentCubic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x xStar : E} {α : ℝ}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) ≤
      φ (AffineMap.lineMap x xStar α) +
        ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x - xStar‖ ^ (3 : ℕ) := by
  let yα : E := AffineMap.lineMap x xStar α
  have herror :=
    HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le
      hφ_hessian x yα
  have hyα_eq :
      yα = α • (xStar - x) + x := by
    -- Keep the segment displacement explicit before normalizing its norm.
    simpa [yα] using AffineMap.lineMap_apply x xStar α
  have hyα_norm_eq :
      ‖(yα - x : E)‖ = α * ‖(xStar - x : E)‖ := by
    -- The segment displacement has length `α` times the endpoint distance.
    rw [hyα_eq]
    simp [norm_smul_of_nonneg, hα.1]
  calc
    secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α)
        = secondOrderTaylorModelAt φ x yα := by simp [yα]
    _ ≤ φ yα + ((L : ℝ) / 6) * ‖(yα - x : E)‖ ^ (3 : ℕ) := by
          -- Use the one-sided Taylor remainder bound directly on the minimizer segment.
          linarith [(abs_le.mp herror).1]
    _ = φ (AffineMap.lineMap x xStar α) +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x - xStar‖ ^ (3 : ℕ) := by
          rw [hyα_norm_eq]
          simp [yα, norm_sub_rev, Real.norm_of_nonneg hα.1, mul_pow, mul_assoc, mul_left_comm,
            mul_comm]

/-- Helper for Proposition 4.4.10: the quadratic Taylor model at `x` is controlled along the
segment to `xStar` by convexity of `φ` and the Hessian-Lipschitz cubic remainder. -/
private lemma secondOrderTaylorModelAt_lineMap_le_convexCombination_add_segmentCubic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x xStar : E} {α : ℝ}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) ≤
      (1 - α) * φ x + α * φ xStar +
        ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x - xStar‖ ^ (3 : ℕ) := by
  let yα : E := AffineMap.lineMap x xStar α
  have hconvex : ConvexOn ℝ Set.univ φ := by
    -- Positive strong convexity specializes to ordinary convexity on the ambient space.
    exact strongConvexOn_zero.mp (hφ_strong.mono hσ.le)
  have hconv :
      φ yα ≤ (1 - α) * φ x + α * φ xStar := by
    -- Convexity along the segment from `x` to `xStar` controls the objective part.
    simpa [yα, AffineMap.lineMap_apply_module, mul_comm, mul_left_comm, mul_assoc] using
      hconvex.2
        (by simp : x ∈ (Set.univ : Set E))
        (by simp : xStar ∈ (Set.univ : Set E))
        (sub_nonneg.mpr hα.2)
        hα.1
        (by ring)
  have herror :=
    HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le
      hφ_hessian x yα
  have hmodel_upper :
      secondOrderTaylorModelAt φ x yα ≤
        φ yα + ((L : ℝ) / 6) * ‖(yα - x : E)‖ ^ (3 : ℕ) := by
    -- Use the one-sided Taylor remainder bound in the direction `model ≤ objective + cubic`.
    linarith [(abs_le.mp herror).1]
  have hyα_eq :
      yα = α • (xStar - x) + x := by
    -- `lineMap` exposes the displacement from `x` toward `xStar`.
    simpa [yα] using AffineMap.lineMap_apply x xStar α
  have hyα_norm_eq :
      ‖(yα - x : E)‖ = α * ‖(xStar - x : E)‖ := by
    -- The segment displacement has length `α` times the endpoint distance.
    rw [hyα_eq]
    simp [norm_smul_of_nonneg, hα.1]
  calc
    secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α)
        = secondOrderTaylorModelAt φ x yα := by simp [yα]
    _ ≤ φ yα + ((L : ℝ) / 6) * ‖(yα - x : E)‖ ^ (3 : ℕ) := hmodel_upper
    _ ≤ (1 - α) * φ x + α * φ xStar + ((L : ℝ) / 6) * ‖(yα - x : E)‖ ^ (3 : ℕ) := by
      gcongr
    _ = (1 - α) * φ x + α * φ xStar +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x - xStar‖ ^ (3 : ℕ) := by
      rw [hyα_norm_eq]
      simp [norm_sub_rev, Real.norm_of_nonneg hα.1, mul_pow, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 4.4.10: along the segment from the current iterate to the minimizer,
strong convexity upgrades the gap contraction from the convex factor `1 - α` to the sharper
square factor `(1 - α)^2`. -/
private lemma strongConvex_lineMapGap_le_sq_mul_gap
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x xStar : E} {α : ℝ}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    φ (AffineMap.lineMap x xStar α) - φ xStar ≤
      (1 - α) ^ (2 : ℕ) * (φ x - φ xStar) := by
  have hsegment :
      φ (AffineMap.lineMap x xStar α) ≤
        (1 - α) * φ x + α * φ xStar -
          (1 - α) * α * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) := by
    -- Route correction: use the exact strong-convexity correction on the minimizer segment
    -- before any normalization to the shifted accepted-step gap.
    rw [AffineMap.lineMap_apply_module]
    exact hφ_strong.2 (by simp) (by simp) (sub_nonneg.mpr hα.2) hα.1 (by ring)
  have hgap_lower :
      (σ / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤ φ x - φ xStar := by
    -- Strong convexity turns the endpoint gap into the quadratic distance term on the same
    -- segment.
    exact objectiveGap_ge_halfSigma_mul_sqDistToMinimizer hφ_strong hφ_hessian hxStar
  have hscale_nonneg : 0 ≤ (1 - α) * α := by
    exact mul_nonneg (sub_nonneg.mpr hα.2) hα.1
  have hscaled_gap :
      (1 - α) * α * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) ≤
        (1 - α) * α * (φ x - φ xStar) := by
    exact mul_le_mul_of_nonneg_left hgap_lower hscale_nonneg
  have hgap_step :
      φ (AffineMap.lineMap x xStar α) - φ xStar ≤
        (1 - α) * (φ x - φ xStar) -
          (1 - α) * α * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) := by
    -- First subtract the minimizer value while keeping the strong-convexity correction visible.
    linarith
  -- Replace the quadratic correction by the endpoint gap itself to expose the sharp square factor.
  calc
    φ (AffineMap.lineMap x xStar α) - φ xStar ≤
        (1 - α) * (φ x - φ xStar) -
          (1 - α) * α * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) := hgap_step
    _ ≤
        (1 - α) * (φ x - φ xStar) -
          (1 - α) * α * (φ x - φ xStar) := by
            gcongr
    _ = (1 - α) ^ (2 : ℕ) * (φ x - φ xStar) := by
      ring

/-- Helper for Proposition 4.4.10: the full Newton trial minimizes the quadratic Taylor model
frozen at the current iterate. -/
private lemma modifiedNewtonFullTrial_isMinOn_secondOrderTaylorModel
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} :
    IsMinOn
      (secondOrderTaylorModelAt φ (method k))
      Set.univ
      (NewtonSystem.step (∇ φ) (method.toMethod.x k)) := by
  let x := method k
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let hφ_C2 : ContDiff ℝ 2 φ := hφ_hessian.contDiff
  have hnewton_eq : hessian φ x d = ∇ φ x := by
    -- Expanding the Newton search direction recovers the frozen linearized gradient.
    change
      (fderiv ℝ (∇ φ) ↑(method.toMethod.x k))
          ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
              (method.toMethod.x k).property).symm)
            (∇ φ ↑(method.toMethod.x k))) =
        ∇ φ ↑(method.toMethod.x k)
    exact
      ContinuousLinearEquiv.apply_symm_apply
        ((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
          (method.toMethod.x k).property)
        (∇ φ ↑(method.toMethod.x k))
  have hselfAdjoint : IsSelfAdjoint (hessian φ x) := by
    -- A `C²` objective has self-adjoint Hessian at the current iterate.
    simpa using
      (fderiv_gradient_isSymmetric_of_contDiffAt (f := φ) (x := x)
        (hf := hφ_C2.contDiffAt (x := x))).isSelfAdjoint
  have hUniv_nonempty : (interior (Set.univ : Set E)).Nonempty := by
    simp
  have hcont : ContinuousOn φ (Set.univ : Set E) := hφ_C2.continuous.continuousOn
  have hC2 : ContDiffOn ℝ 2 φ (interior (Set.univ : Set E)) := by
    simpa using hφ_C2.contDiffOn
  have hbound : σ • (1 : E →L[ℝ] E) ≤ hessian φ x := by
    -- Whole-space strong convexity gives a positive-definite frozen Hessian.
    have hiff :=
      (strongConvexOn_iff_hessian_lower_bound
        hσ convex_univ hUniv_nonempty hcont hC2).1 hφ_strong
    simpa [x] using hiff x (by simp)
  rw [isMinOn_iff]
  intro y hy
  let z := y - x
  have hquad_nonneg :
      0 ≤ inner ℝ (hessian φ x (z + d)) (z + d) := by
    have hquad :=
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hσ hC2 (by simp : x ∈ interior (Set.univ : Set E))).1 hbound (z + d)
    exact le_trans (by positivity) hquad
  have hcross :
      inner ℝ (hessian φ x d) z = inner ℝ (hessian φ x z) d := by
    -- Self-adjointness identifies the mixed Hessian terms in the completed square.
    calc
      inner ℝ (hessian φ x d) z = inner ℝ z (hessian φ x d) := by rw [real_inner_comm]
      _ = inner ℝ (hessian φ x z) d := (hselfAdjoint.isSymmetric z d).symm
  have hquadratic :
      0 ≤
        inner ℝ (hessian φ x z) z +
          2 * inner ℝ (hessian φ x d) z +
          inner ℝ (hessian φ x d) d := by
    -- The frozen Taylor-model gap is a positive quadratic form in `z + d`.
    simpa [z, ContinuousLinearMap.map_add, hcross, inner_add_left, inner_add_right, two_mul,
      add_assoc, add_left_comm, add_comm] using hquad_nonneg
  have hT_disp : T - x = -d := by
    -- The full Newton trial is obtained from `x` by the unit Newton correction.
    simp [T, x, d, NewtonSystem.step_def, DampedNewton.Method.searchDirection, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  rw [secondOrderTaylorModelAt_apply, secondOrderTaylorModelAt_apply, hT_disp, ← hnewton_eq]
  have hT_rewrite :
      φ x + inner ℝ (hessian φ x d) (-d) +
          (1 / 2 : ℝ) * inner ℝ (hessian φ x (-d)) (-d) =
        φ x - (1 / 2 : ℝ) * inner ℝ (hessian φ x d) d := by
    -- Normalize the full-trial model value into the completed-square base point.
    simp [inner_smul_left, inner_smul_right, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hT_rewrite]
  -- The completed-square inequality is exactly the pointwise minimality of the frozen model.
  nlinarith

/-- Helper for Proposition 4.4.10: the full Newton trial's quadratic Taylor-model value is no
larger than the model value at the segment point from the current iterate to `xStar`. -/
private lemma modifiedNewtonFullTrial_secondOrderTaylorModel_le_lineMap
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    secondOrderTaylorModelAt φ (method k)
        (NewtonSystem.step (∇ φ) (method.toMethod.x k)) ≤
      secondOrderTaylorModelAt φ (method k)
        (AffineMap.lineMap (method k) xStar α) := by
  have hmin :=
    modifiedNewtonFullTrial_isMinOn_secondOrderTaylorModel
      hσ hφ_strong hφ_hessian method (k := k)
  -- Evaluate the frozen model minimizer at the segment point toward the minimizer `xStar`.
  exact (isMinOn_iff.mp hmin) _ (by simp)

/-- Helper for Proposition 4.4.10: the full Newton trial's frozen quadratic Taylor-model gap
above `φ xStar` is controlled by the current cubic Taylor remainder. -/
private lemma modifiedNewtonFullTrialTaylorModelGap_le_currentCubic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} :
    secondOrderTaylorModelAt φ (method k)
        (NewtonSystem.step (∇ φ) (method.toMethod.x k)) - φ xStar ≤
      ((L : ℝ) / 6) * ‖method k - xStar‖ ^ (3 : ℕ) := by
  let x := method k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  have hmodel_min :
      secondOrderTaylorModelAt φ x T ≤ secondOrderTaylorModelAt φ x xStar := by
    -- The full Newton trial minimizes the frozen quadratic Taylor model at the current iterate.
    have hmin :=
      modifiedNewtonFullTrial_isMinOn_secondOrderTaylorModel
        hσ hφ_strong hφ_hessian method (k := k)
    exact (isMinOn_iff.mp hmin) xStar (by simp)
  have herror :=
    HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le
      hφ_hessian x xStar
  have hxStar_model_gap :
      secondOrderTaylorModelAt φ x xStar - φ xStar ≤
        ((L : ℝ) / 6) * ‖x - xStar‖ ^ (3 : ℕ) := by
    -- The Hessian-Lipschitz remainder controls the frozen Taylor model at the minimizer.
    have hupper :
        secondOrderTaylorModelAt φ x xStar ≤
          φ xStar + ((L : ℝ) / 6) * ‖xStar - x‖ ^ (3 : ℕ) := by
      linarith [(abs_le.mp herror).1]
    rw [norm_sub_rev] at hupper
    linarith
  -- Subtract the minimizer value after comparing the full-trial model with the model at `xStar`.
  linarith

/-- Helper for Proposition 4.4.10: a nonnegative characteristic quantity with square at most
`1 / 3` already lies below the sharper threshold `2 (√2 - 1)`. -/
private lemma modifiedNewtonCharacteristic_le_twoSqrtTwoSubTwo_of_sq_le_oneThird
    {q : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hq_sq : q ^ (2 : ℕ) ≤ (1 / 3 : ℝ)) :
    q ≤ 2 * (Real.sqrt (2 : ℝ) - 1) := by
  have hq_le_threeFifths : q ≤ (3 / 5 : ℝ) := by
    have hq_sq_five : q ^ (2 : ℕ) ≤ (3 / 5 : ℝ) ^ (2 : ℕ) := by
      calc
        q ^ (2 : ℕ) ≤ 1 / 3 := hq_sq
        _ ≤ (3 / 5 : ℝ) ^ (2 : ℕ) := by norm_num
    exact (sq_le_sq₀ hq_nonneg (by positivity : 0 ≤ (3 / 5 : ℝ))).1 hq_sq_five
  have hsqrt_two_ge : (7 / 5 : ℝ) ≤ Real.sqrt (2 : ℝ) := by
    have hsq :
        (7 / 5 : ℝ) ^ (2 : ℕ) ≤ (Real.sqrt (2 : ℝ)) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
      norm_num
    exact (sq_le_sq₀ (by positivity : 0 ≤ (7 / 5 : ℝ)) (Real.sqrt_nonneg _)).1 hsq
  have hthreshold_ge : (3 / 5 : ℝ) ≤ 2 * (Real.sqrt (2 : ℝ) - 1) := by
    have hfourFifths :
        (4 / 5 : ℝ) ≤ 2 * (Real.sqrt (2 : ℝ) - 1) := by
      have hmul :=
        mul_le_mul_of_nonneg_left hsqrt_two_ge (show 0 ≤ (2 : ℝ) by positivity)
      linarith
    exact (show (3 / 5 : ℝ) ≤ 4 / 5 by norm_num).trans hfourFifths
  exact hq_le_threeFifths.trans hthreshold_ge

/-- Helper for Proposition 4.4.10: a nonnegative characteristic quantity with square at most
`1 / 4` lies below the half-threshold needed for the public region-entry witness. -/
private lemma modifiedNewtonCharacteristic_le_half_of_sq_le_quarter
    {q : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hq_sq : q ^ (2 : ℕ) ≤ (1 / 4 : ℝ)) :
    q ≤ (1 / 2 : ℝ) := by
  have hq_sq_half : q ^ (2 : ℕ) ≤ (1 / 2 : ℝ) ^ (2 : ℕ) := by
    calc
      q ^ (2 : ℕ) ≤ 1 / 4 := hq_sq
      _ = (1 / 2 : ℝ) ^ (2 : ℕ) := by norm_num
  exact (sq_le_sq₀ hq_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ))).1 hq_sq_half

/-- Helper for Proposition 4.4.10: once the current characteristic quantity lies below the
explicit sharp threshold `2 (sqrt 2 - 1)`, the next characteristic quantity is bounded by its
square. -/
private lemma modifiedNewtonCharacteristicSucc_le_sq_of_characteristic_le_twoSqrtTwoSubTwo
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ}
    (hkq :
      modifiedNewtonCharacteristicQuantity σ L (method k) xStar ≤
        2 * (Real.sqrt (2 : ℝ) - 1)) :
    modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar ≤
      modifiedNewtonCharacteristicQuantity σ L (method k) xStar ^ (2 : ℕ) := by
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method k) xStar
  have herror :
      ‖method (k + 1) - xStar‖ ≤
        ((L : ℝ) / σ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
    -- Reuse the sharp accepted-step quadratic error estimate once the explicit threshold holds.
    simpa using
      modifiedNewtonAcceptedStepErrorLeQuadratic_of_characteristic_le_twoSqrtTwoSubTwo
        hσ hφ_strong hφ_hessian hxStar method hkq
  have hq_def : q = ((L : ℝ) / σ) * ‖method k - xStar‖ := by
    -- Keep the current characteristic quantity in its normalized `((L / σ) * ‖e_k‖)` form.
    simp [q, modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm]
  have hq_next_def :
      modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar =
        ((L : ℝ) / σ) * ‖method (k + 1) - xStar‖ := by
    -- Expand the next characteristic quantity in the same normalized form.
    simp [modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm]
  have hcoeff_nonneg : 0 ≤ (L : ℝ) / σ := by
    positivity
  calc
    modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar =
        ((L : ℝ) / σ) * ‖method (k + 1) - xStar‖ := hq_next_def
    _ ≤ ((L : ℝ) / σ) * (((L : ℝ) / σ) * ‖method k - xStar‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left herror hcoeff_nonneg
    _ = (((L : ℝ) / σ) * ‖method k - xStar‖) ^ (2 : ℕ) := by
      ring
    _ = q ^ (2 : ℕ) := by
      rw [hq_def]
    _ = modifiedNewtonCharacteristicQuantity σ L (method k) xStar ^ (2 : ℕ) := by
      simp [q]

/-- Helper for Proposition 4.4.10: once an iterate lies in the local region `q_k < 1`, the next
characteristic square should already drop below `1 / 3`, which is enough to enter the sharp
threshold used by the quadratic tail bootstrap. -/
private lemma modifiedNewtonCharacteristicSqSucc_le_oneThird_of_localRegion
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ}
    (hk : InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k) :
    modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar ^ (2 : ℕ) ≤ (1 / 3 : ℝ) := by
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method k) xStar
  let qNext : ℝ := modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar
  have hq_nonneg : 0 ≤ q := by
    have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
    exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
  have hq_lt_one : q < 1 := by
    simpa [q] using hk
  have hqNext_nonneg : 0 ≤ qNext := by
    have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
    exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
  have hlocal_model :
      qNext ≤ ((1 / 2 : ℝ) * (1 + q / 2) ^ (2 : ℕ)) * q ^ (2 : ℕ) := by
    -- Route correction: reuse the existing local characteristic model on the accepted-step
    -- surface instead of reintroducing the discarded pure-cubic bridge.
    simpa [q, qNext] using
      modifiedNewtonCharacteristicSucc_le_localQuadraticModel
        hσ hφ_strong hφ_hessian hxStar method hk
  have hsq :
      qNext ^ (2 : ℕ) ≤
        ((((1 / 2 : ℝ) * (1 + q / 2) ^ (2 : ℕ)) * q ^ (2 : ℕ)) ^ (2 : ℕ)) := by
    -- Square the accepted-step characteristic model in a nonnegative scalar context.
    exact sq_le_sq₀ hqNext_nonneg (by positivity) hlocal_model
  calc
    modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar ^ (2 : ℕ) = qNext ^ (2 : ℕ) := by
      simp [qNext]
    _ ≤ ((((1 / 2 : ℝ) * (1 + q / 2) ^ (2 : ℕ)) * q ^ (2 : ℕ)) ^ (2 : ℕ)) := hsq
    _ ≤ (1 / 3 : ℝ) := by
      nlinarith

/-- Helper for Proposition 4.4.10: once the orbit enters the local region `q_k < 1`, the direct
characteristic recurrence propagates quadratic convergence from the same index `k`. -/
private theorem modifiedNewtonTailQuadraticBootstrap
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0) {k : ℕ}
    (hk : InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k) :
    HasQuadraticConvergenceFrom method xStar k := by
  by_cases hLzero : (L : ℝ) = 0
  · let tail : ℕ → E := fun j ↦ method (k + j)
    let r : ℕ → ℝ := fun j ↦ ‖tail j - xStar‖
    let c : ℝ := 1 / (2 * (r 0 + 1))
    have hc : 0 < c := by
      positivity
    have hr_nonneg : ∀ j : ℕ, 0 ≤ r j := by
      -- The tail error sequence is nonnegative because it is defined by norms.
      intro j
      exact norm_nonneg _
    have hregion_tail :
        ∀ j : ℕ, InModifiedNewtonQuadraticConvergenceRegion method σ L xStar (k + j) := by
      -- When `L = 0`, the quadratic region is all of `E`.
      intro j
      simpa [InModifiedNewtonQuadraticConvergenceRegion, modifiedNewtonQuadraticConvergenceRegion,
        modifiedNewtonCharacteristicQuantity_def, hLzero]
    have hquad : ∀ j : ℕ, r (j + 1) ≤ c * (r j) ^ (2 : ℕ) := by
      -- The zero-`L` branch collapses the coarse quadratic estimate to `r (j + 1) ≤ 0`.
      intro j
      have hstep :
          r (j + 1) ≤ (2 * ((L : ℝ) / σ)) * (r j) ^ (2 : ℕ) := by
        simpa [r, tail, Nat.add_assoc] using
          modifiedNewtonAcceptedStepErrorLeTwoMulQuadratic
            hσ hφ_strong hφ_hessian hxStar method (hregion_tail j)
      have hzero : r (j + 1) ≤ 0 := by
        simpa [hLzero] using hstep
      exact hzero.trans (by positivity)
    have hscaled0 : c * r 0 < 1 := by
      -- The auxiliary positive constant is chosen so that `c * r 0 < 1/2`.
      have hden_pos : 0 < 2 * (r 0 + 1) := by positivity
      have hle_half :
          (1 / (2 * (r 0 + 1))) * r 0 ≤ (1 / 2 : ℝ) := by
        rw [show (1 / (2 * (r 0 + 1))) * r 0 = r 0 / (2 * (r 0 + 1)) by ring]
        refine (div_le_iff₀ hden_pos).2 ?_
        nlinarith [hr_nonneg 0]
      have hlt_one : (1 / (2 * (r 0 + 1))) * r 0 < 1 := by
        exact lt_of_le_of_lt hle_half (by norm_num)
      simpa [c] using hlt_one
    have htendsto_r : Filter.Tendsto r Filter.atTop (nhds 0) := by
      exact quadraticTailTendstoZero_of_scaled_lt_one hc hr_nonneg hquad hscaled0
    have htendsto_tail : Filter.Tendsto tail Filter.atTop (nhds xStar) := by
      -- Convergence of the error norms is exactly convergence of the tail to the minimizer.
      exact (tendsto_iff_norm_sub_tendsto_zero).2 <| by simpa [r, tail] using htendsto_r
    exact
      hasQuadraticConvergenceFrom_of_tailSeq
        ⟨c, hc, htendsto_tail, HasEventuallySuperlinearErrorBound.of_quadratic_bound hquad⟩
  · let tail : ℕ → E := fun j ↦ method (k + j)
    let r : ℕ → ℝ := fun j ↦ ‖tail j - xStar‖
    let tailSharp : ℕ → E := fun j ↦ method (k + 1 + j)
    let rSharp : ℕ → ℝ := fun j ↦ ‖tailSharp j - xStar‖
    let cSharp : ℝ := (L : ℝ) / σ
    let c : ℝ := 2 * cSharp
    have hsqrt_two_sq : (Real.sqrt (2 : ℝ)) ^ (2 : ℕ) = (2 : ℝ) := by
      rw [pow_two]
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
    have hsqrt_two_lt_threeHalves : Real.sqrt (2 : ℝ) < (3 / 2 : ℝ) := by
      have hsq :
          (Real.sqrt (2 : ℝ)) ^ (2 : ℕ) < (3 / 2 : ℝ) ^ (2 : ℕ) := by
        rw [hsqrt_two_sq]
        norm_num
      exact
        (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ (3 / 2 : ℝ))).1 hsq
    have hone_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt (2 : ℝ) := by
      have hsq : (1 : ℝ) ^ (2 : ℕ) ≤ (Real.sqrt (2 : ℝ)) ^ (2 : ℕ) := by
        rw [hsqrt_two_sq]
        norm_num
      exact (sq_le_sq₀ (by positivity : 0 ≤ (1 : ℝ)) (Real.sqrt_nonneg _)).1 hsq
    have hthreshold_nonneg : 0 ≤ 2 * (Real.sqrt (2 : ℝ) - 1) := by
      nlinarith [hone_le_sqrt_two]
    have hthreshold_lt_one : 2 * (Real.sqrt (2 : ℝ) - 1) < (1 : ℝ) := by
      nlinarith [hsqrt_two_lt_threeHalves]
    have hcSharp : 0 < cSharp := by
      have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
      exact div_pos (lt_of_le_of_ne hL_nonneg (Ne.symm hLzero)) hσ
    have hc : 0 < c := by
      positivity
    have hr_nonneg : ∀ j : ℕ, 0 ≤ r j := by
      -- The tail error sequence is nonnegative because it is defined by norms.
      intro j
      exact norm_nonneg _
    have hrSharp_nonneg : ∀ j : ℕ, 0 ≤ rSharp j := by
      intro j
      exact norm_nonneg _
    have hqSharp_nonneg :
        ∀ j : ℕ, 0 ≤ modifiedNewtonCharacteristicQuantity σ L (tailSharp j) xStar := by
      intro j
      have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
      exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
    have hq_one_sq :
        modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar ^ (2 : ℕ) ≤ (1 / 3 : ℝ) := by
      -- The first local step must enter the sharp threshold before the quadratic tail starts.
      simpa using
        modifiedNewtonCharacteristicSqSucc_le_oneThird_of_localRegion
          hσ hφ_strong hφ_hessian hxStar method hk
    have hq_one_threshold :
        modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar ≤
          2 * (Real.sqrt (2 : ℝ) - 1) := by
      have hq_one_nonneg :
          0 ≤ modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar := by
        have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
        exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
      exact
        modifiedNewtonCharacteristic_le_twoSqrtTwoSubTwo_of_sq_le_oneThird
          hq_one_nonneg hq_one_sq
    have hthreshold_tailSharp :
        ∀ j : ℕ,
          modifiedNewtonCharacteristicQuantity σ L (tailSharp j) xStar ≤
            2 * (Real.sqrt (2 : ℝ) - 1) := by
      intro j
      induction j with
      | zero =>
          simpa [tailSharp] using hq_one_threshold
      | succ j ih =>
          have hstep :
              modifiedNewtonCharacteristicQuantity σ L (tailSharp (j + 1)) xStar ≤
                modifiedNewtonCharacteristicQuantity σ L (tailSharp j) xStar ^ (2 : ℕ) := by
            -- Once the sharp threshold holds at `tailSharp j`, the verified quadratic recurrence
            -- propagates it along the whole shifted tail.
            simpa [tailSharp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              modifiedNewtonCharacteristicSucc_le_sq_of_characteristic_le_twoSqrtTwoSubTwo
                hσ hφ_strong hφ_hessian hxStar method (k := k + 1 + j) ih
          have hqj_nonneg :
              0 ≤ modifiedNewtonCharacteristicQuantity σ L (tailSharp j) xStar := hqSharp_nonneg j
          have hqj_sq_le :
              modifiedNewtonCharacteristicQuantity σ L (tailSharp j) xStar ^ (2 : ℕ) ≤
                2 * (Real.sqrt (2 : ℝ) - 1) := by
            calc
              modifiedNewtonCharacteristicQuantity σ L (tailSharp j) xStar ^ (2 : ℕ)
                  ≤ (2 * (Real.sqrt (2 : ℝ) - 1)) ^ (2 : ℕ) := by
                    exact pow_le_pow_left₀ hqj_nonneg ih 2
              _ ≤ 2 * (Real.sqrt (2 : ℝ) - 1) := by
                    have hthreshold_le_one : 2 * (Real.sqrt (2 : ℝ) - 1) ≤ (1 : ℝ) := by
                      linarith
                    nlinarith [hthreshold_nonneg, hthreshold_le_one]
          exact hstep.trans hqj_sq_le
    have hlocal_tail :
        ∀ j : ℕ, InModifiedNewtonQuadraticConvergenceRegion method σ L xStar (k + 1 + j) := by
      intro j
      have hqj_lt_one :
          modifiedNewtonCharacteristicQuantity σ L (tailSharp j) xStar < 1 := by
        exact lt_of_le_of_lt (hthreshold_tailSharp j) hthreshold_lt_one
      simpa [tailSharp, InModifiedNewtonQuadraticConvergenceRegion,
        modifiedNewtonQuadraticConvergenceRegion, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hqj_lt_one
    have hquadSharp : ∀ j : ℕ, rSharp (j + 1) ≤ cSharp * (rSharp j) ^ (2 : ℕ) := by
      intro j
      -- After the first local step, the sharp threshold recurrence gives the standard quadratic
      -- error bound on the shifted tail.
      simpa [rSharp, tailSharp, cSharp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        modifiedNewtonAcceptedStepErrorLeQuadratic_of_characteristic_le_twoSqrtTwoSubTwo
          hσ hφ_strong hφ_hessian hxStar method (k := k + 1 + j) (hthreshold_tailSharp j)
    have hscaledSharp0 : cSharp * rSharp 0 < 1 := by
      -- The first shifted iterate already lies below the sharp threshold, hence inside the local
      -- radius needed by the standard quadratic-tail argument.
      calc
        cSharp * rSharp 0 =
            modifiedNewtonCharacteristicQuantity σ L (method (k + 1)) xStar := by
              simp [cSharp, rSharp, tailSharp, modifiedNewtonCharacteristicQuantity_def,
                div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ 2 * (Real.sqrt (2 : ℝ) - 1) := hq_one_threshold
        _ < 1 := hthreshold_lt_one
    have htendsto_rSharp : Filter.Tendsto rSharp Filter.atTop (nhds 0) := by
      exact
        quadraticTailTendstoZero_of_scaled_lt_one
          hcSharp hrSharp_nonneg hquadSharp hscaledSharp0
    have htendsto_tailSharp : Filter.Tendsto tailSharp Filter.atTop (nhds xStar) := by
      -- Convergence of the shifted-tail error norms is exactly convergence of that tail to the
      -- minimizer.
      exact (tendsto_iff_norm_sub_tendsto_zero).2 <| by
        simpa [rSharp, tailSharp] using htendsto_rSharp
    have htendsto_method : Filter.Tendsto method Filter.atTop (nhds xStar) := by
      -- A finite prefix does not affect the limit, so convergence of the shifted tail implies
      -- convergence of the original modified-Newton orbit.
      have htendsto_shift :
          Filter.Tendsto (fun j : ℕ ↦ method (j + (k + 1))) Filter.atTop (nhds xStar) := by
        simpa [tailSharp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htendsto_tailSharp
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Filter.tendsto_add_atTop_iff_nat (k + 1)).1 htendsto_shift
    have hbound : HasEventuallySuperlinearErrorBound (fun j ↦ ‖method j - xStar‖) 0 c k := by
      refine ⟨Nat.zero_le k, ?_⟩
      intro j hj
      rcases Nat.exists_eq_add_of_le hj with ⟨n, rfl⟩
      cases n with
      | zero =>
          -- The entry step itself only satisfies the coarse quadratic bound, which fixes the
          -- public constant `2 * (L / σ)` in the same-index `HasQuadraticConvergenceFrom`.
          simpa [c, r, tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            modifiedNewtonAcceptedStepErrorLeTwoMulQuadratic
              hσ hφ_strong hφ_hessian hxStar method hk
      | succ n =>
          have hsharp :
              ‖method (k + (n + 1) + 1) - xStar‖ ≤
                cSharp * ‖method (k + (n + 1)) - xStar‖ ^ (2 : ℕ) := by
            simpa [rSharp, tailSharp, cSharp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              hquadSharp n
          exact hsharp.trans <| by
            have hmain_nonneg : 0 ≤ ‖method (k + (n + 1)) - xStar‖ ^ (2 : ℕ) := by positivity
            have hcoeff_le : cSharp ≤ c := by
              dsimp [c, cSharp]
              linarith
            exact mul_le_mul_of_nonneg_right hcoeff_le hmain_nonneg
    exact ⟨c, hc, htendsto_method, hbound⟩

/-- Entry of the `k`th modified Newton iterate into the local quadratic-convergence region forces
quadratic convergence of the same orbit from index `k`. -/
theorem hasQuadraticConvergenceFrom_of_inModifiedNewtonQuadraticConvergenceRegion
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0) {k : ℕ}
    (hk : InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k) :
    HasQuadraticConvergenceFrom method xStar k := by
  exact modifiedNewtonTailQuadraticBootstrap
    hσ hφ_strong hφ_hessian hxStar method hk

-- Proof sketch: use the canonical owner hypotheses `StrongConvexOn Set.univ σ φ` and `φ ∈ C22[L]`
-- to control the global phase of the modified Newton orbit by the characteristic quantity
-- `ξ = L ‖x₀ - x*‖ / σ`. Strong convexity supplies uniqueness of the minimizer from `hxStar`.
-- The first phase ends when the orbit enters the local quadratic-convergence regime, and the
-- textbook estimate yields the bound `N₁ ≤ 6.25 * sqrt ξ` whenever `ξ ≥ 1`.
/-- If the modified-Newton characteristic quantity `ξ = L ‖x₀ - x*‖ / σ` is strictly smaller
than `1`, then the modified Newton orbit already starts in the local quadratic-convergence
regime, so it converges quadratically to `x*` from index `0`. -/
theorem modifiedNewton_hasQuadraticConvergenceFrom_zero_of_characteristicQuantity_lt_one
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (hxi : modifiedNewtonCharacteristicQuantity σ L x0 xStar < 1) :
    HasQuadraticConvergenceFrom method xStar 0 := by
  -- At index `0`, the local characteristic condition is exactly the hypothesis on `x0`.
  apply hasQuadraticConvergenceFrom_of_inModifiedNewtonQuadraticConvergenceRegion
    hσ hφ_strong hφ_hessian hxStar method
  simpa using hxi

/-- Helper for Proposition 4.4.10: the shifted normalized accepted-step gap sequence
`Δ j = ((2 L²) / σ³) * (φ(x_{j+1}) - φ(x*))` lives on the accepted-step surface used by the
remaining global `O(√ξ)` entry proof. -/
private def modifiedNewtonShiftedNormalizedGap
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (method : ModifiedNewtonMethod φ x0) : ℕ → ℝ :=
  fun j ↦
    (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) *
      (φ (method (j + 1)) - φ xStar)

/-- Helper for Proposition 4.4.10: every shifted normalized accepted-step gap is nonnegative. -/
private lemma modifiedNewtonShiftedNormalizedGap_nonneg
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (j : ℕ) :
    0 ≤ modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method j := by
  -- The shifted normalized gap is a nonnegative scalar multiple of an objective gap.
  dsimp [modifiedNewtonShiftedNormalizedGap]
  exact mul_nonneg (by positivity)
    (modifiedNewtonObjectiveGap_nonneg hxStar method (j + 1))

/-- Helper for Proposition 4.4.10: the next characteristic square is bounded by the shifted
normalized accepted-step gap at the matching shifted index. -/
private lemma modifiedNewtonCharacteristicSq_le_shiftedNormalizedGap
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (j : ℕ) :
    modifiedNewtonCharacteristicQuantity σ L (method (j + 1)) xStar ^ (2 : ℕ) ≤
      modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method j := by
  -- This is exactly the owner comparison `q² ≤ ((2L²)/σ³) * gap`, shifted by one iterate.
  simpa [modifiedNewtonShiftedNormalizedGap] using
    (modifiedNewtonCharacteristicSq_le_normalizedObjectiveGap hσ hφ_strong hφ_hessian hxStar :
      modifiedNewtonCharacteristicQuantity σ L (method (j + 1)) xStar ^ (2 : ℕ) ≤
        (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) *
          (φ (method (j + 1)) - φ xStar))

/-- Helper for Proposition 4.4.10: after shifting the accepted-step gaps by one index, the
accepted-step recurrence becomes a recurrence in the scalar surface `Δ`. -/
private lemma modifiedNewtonShiftedNormalizedGapSucc_le_largePhaseModel
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {j : ℕ} {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method (j + 1) ≤
      ((1 - α) +
          (Real.sqrt
              (modifiedNewtonShiftedNormalizedGap
                (σ := σ) (L := L) (xStar := xStar) method j) / 3) *
            (α +
              α ^ (3 : ℕ) *
                (1 +
                    Real.sqrt
                      (modifiedNewtonShiftedNormalizedGap
                        (σ := σ) (L := L) (xStar := xStar) method j) / 2) ^
                  (3 : ℕ))) *
        modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method j := by
  let Δ : ℕ → ℝ := modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method (j + 1)) xStar
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  have hΔ_nonneg : 0 ≤ Δ j := by
    -- The shifted normalized gap is nonnegative because it comes from the objective gap.
    simpa [Δ] using modifiedNewtonShiftedNormalizedGap_nonneg hσ hxStar method j
  have hq_nonneg : 0 ≤ q := by
    have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
    exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
  have hq_sq : q ^ (2 : ℕ) ≤ Δ j := by
    -- The characteristic-to-gap bridge is aligned with the shifted index by construction.
    simpa [Δ, q] using
      modifiedNewtonCharacteristicSq_le_shiftedNormalizedGap
        hσ hφ_strong hφ_hessian hxStar method j
  have hq_le_sqrtΔ : q ≤ Real.sqrt (Δ j) := by
    have hsq :
        q ^ (2 : ℕ) ≤ (Real.sqrt (Δ j)) ^ (2 : ℕ) := by
      simpa [Real.sq_sqrt hΔ_nonneg] using hq_sq
    exact (sq_le_sq₀ hq_nonneg (Real.sqrt_nonneg _)).1 hsq
  have hs_nonneg : 0 ≤ s := by positivity
  have hstep_gap :
      φ (method (j + 2)) - φ xStar ≤
        ((1 - α) +
            (q / 3) * (α + α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ))) *
          (φ (method (j + 1)) - φ xStar) := by
    -- Shift the accepted-step recurrence so its current surface is exactly `Δ j`.
    simpa [q, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (modifiedNewtonObjectiveGapSucc_le_characteristicWeightedGap
        hσ hφ_strong hφ_hessian hxStar method (k := j + 1) hα)
  have hscaled_gap :
      Δ (j + 1) ≤
        ((1 - α) +
            (q / 3) * (α + α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ))) *
          Δ j := by
    -- Multiply the shifted accepted-step recurrence by the fixed normalization scale.
    have hmul := mul_le_mul_of_nonneg_left hstep_gap hs_nonneg
    dsimp [Δ] at hmul ⊢
    simpa [s, modifiedNewtonShiftedNormalizedGap, mul_assoc, mul_left_comm, mul_comm,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmul
  have hsqrt_term_nonneg :
      0 ≤
        α +
          α ^ (3 : ℕ) *
            (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ) := by
    have hpow_nonneg : 0 ≤ α ^ (3 : ℕ) := by exact pow_nonneg hα.1 _
    have hsqrt_base_nonneg : 0 ≤ 1 + Real.sqrt (Δ j) / 2 := by positivity
    have hsqrt_pow_nonneg : 0 ≤ (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ) := by
      exact pow_nonneg hsqrt_base_nonneg _
    nlinarith
  have hinner_le :
      α + α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ) ≤
        α + α ^ (3 : ℕ) * (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ) := by
    have hbase :
        1 + q / 2 ≤ 1 + Real.sqrt (Δ j) / 2 := by
      nlinarith
    have hpow :
        (1 + q / 2) ^ (3 : ℕ) ≤
          (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ) := by
      exact pow_le_pow_left₀ (by positivity : 0 ≤ 1 + q / 2) hbase 3
    have hmul :
        α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ) ≤
          α ^ (3 : ℕ) * (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hpow (by exact pow_nonneg hα.1 _)
    nlinarith
  have htail_le :
      (q / 3) * (α + α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ)) ≤
        (Real.sqrt (Δ j) / 3) *
          (α + α ^ (3 : ℕ) * (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ)) := by
    have hq_div_le : q / 3 ≤ Real.sqrt (Δ j) / 3 := by
      nlinarith
    calc
      (q / 3) * (α + α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ)) ≤
          (q / 3) * (α + α ^ (3 : ℕ) * (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hinner_le (by positivity : 0 ≤ q / 3)
      _ ≤
          (Real.sqrt (Δ j) / 3) *
            (α + α ^ (3 : ℕ) * (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ)) := by
            exact mul_le_mul_of_nonneg_right hq_div_le hsqrt_term_nonneg
  have hcoeff_le :
      ((1 - α) +
          (q / 3) * (α + α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ))) ≤
        ((1 - α) +
            (Real.sqrt (Δ j) / 3) *
              (α + α ^ (3 : ℕ) * (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ))) := by
    linarith
  calc
    Δ (j + 1) ≤
        ((1 - α) +
            (q / 3) * (α + α ^ (3 : ℕ) * (1 + q / 2) ^ (3 : ℕ))) *
          Δ j := hscaled_gap
    _ ≤
        ((1 - α) +
            (Real.sqrt (Δ j) / 3) *
              (α + α ^ (3 : ℕ) * (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ))) *
          Δ j := by
            exact mul_le_mul_of_nonneg_right hcoeff_le hΔ_nonneg
    _ = ((1 - α) +
            (Real.sqrt
                (modifiedNewtonShiftedNormalizedGap
                  (σ := σ) (L := L) (xStar := xStar) method j) / 3) *
              (α +
                α ^ (3 : ℕ) *
                  (1 +
                      Real.sqrt
                        (modifiedNewtonShiftedNormalizedGap
                          (σ := σ) (L := L) (xStar := xStar) method j) / 2) ^
                    (3 : ℕ))) *
          modifiedNewtonShiftedNormalizedGap
            (σ := σ) (L := L) (xStar := xStar) method j := by
            simp [Δ]

/-- Helper for Proposition 4.4.10: hitting the shifted normalized gap threshold `Δ j ≤ 1 / 4`
forces the next characteristic quantity below `1 / 2`. -/
private lemma modifiedNewtonCharacteristicSucc_le_half_of_shiftedNormalizedGap_le_quarter
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {j : ℕ}
    (hΔ : modifiedNewtonShiftedNormalizedGap
        (σ := σ) (L := L) (xStar := xStar) method j ≤ (1 / 4 : ℝ)) :
    modifiedNewtonCharacteristicQuantity σ L (method (j + 1)) xStar ≤ (1 / 2 : ℝ) := by
  let q : ℝ := modifiedNewtonCharacteristicQuantity σ L (method (j + 1)) xStar
  have hq_nonneg : 0 ≤ q := by
    have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
    exact div_nonneg (mul_nonneg hL_nonneg (norm_nonneg _)) hσ.le
  have hq_sq :
      q ^ (2 : ℕ) ≤
        modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method j := by
    -- The characteristic square is controlled by the shifted normalized gap on the same index.
    simpa [q] using
      modifiedNewtonCharacteristicSq_le_shiftedNormalizedGap
        hσ hφ_strong hφ_hessian hxStar method j
  exact
    modifiedNewtonCharacteristic_le_half_of_sq_le_quarter
      hq_nonneg (hq_sq.trans hΔ)

/-- Helper for Proposition 4.4.10: a one-step quarter-root drop by `1 / 5` telescopes linearly
as long as every earlier shifted gap stays above the threshold `1 / 4`. -/
private lemma shiftedGapQuarterRoot_bound_of_drop
    {Δ : ℕ → ℝ}
    (hdrop : ∀ j : ℕ, (1 / 4 : ℝ) ≤ Δ j →
      Real.rpow (Δ (j + 1)) (1 / 4 : ℝ) ≤
        Real.rpow (Δ j) (1 / 4 : ℝ) - (1 / 5 : ℝ)) :
    ∀ k : ℕ,
      (∀ j < k, (1 / 4 : ℝ) ≤ Δ j) →
        Real.rpow (Δ k) (1 / 4 : ℝ) ≤
          Real.rpow (Δ 0) (1 / 4 : ℝ) - (k : ℝ) / 5 := by
  intro k
  induction k with
  | zero =>
      intro _
      -- The initial quarter root is the starting point of the telescoping estimate.
      simp
  | succ k ih =>
      intro hall
      have hk_threshold : (1 / 4 : ℝ) ≤ Δ k := hall k (Nat.lt_succ_self k)
      have hall_prev : ∀ j < k, (1 / 4 : ℝ) ≤ Δ j := by
        intro j hj
        exact hall j (Nat.lt_trans hj (Nat.lt_succ_self k))
      have hprev := ih hall_prev
      -- Apply the one-step drop at index `k` and then telescope the already accumulated loss.
      calc
        Real.rpow (Δ (k + 1)) (1 / 4 : ℝ)
            ≤ Real.rpow (Δ k) (1 / 4 : ℝ) - (1 / 5 : ℝ) := hdrop k hk_threshold
        _ ≤ (Real.rpow (Δ 0) (1 / 4 : ℝ) - (k : ℝ) / 5) - (1 / 5 : ℝ) := by
            linarith
        _ = Real.rpow (Δ 0) (1 / 4 : ℝ) - (((k + 1 : ℕ) : ℝ) / 5) := by
            norm_num [Nat.cast_add]

/-- Helper for Proposition 4.4.10: once a `1 / 5` quarter-root drop is available above the
threshold `1 / 4`, some shifted gap must cross that threshold within `1 + 5 * Δ₀^(1/4)` steps. -/
private lemma existsQuarterEntry_of_shiftedGapQuarterRootDrop
    {Δ : ℕ → ℝ}
    (hnonneg : ∀ j : ℕ, 0 ≤ Δ j)
    (hdrop : ∀ j : ℕ, (1 / 4 : ℝ) ≤ Δ j →
      Real.rpow (Δ (j + 1)) (1 / 4 : ℝ) ≤
        Real.rpow (Δ j) (1 / 4 : ℝ) - (1 / 5 : ℝ)) :
    ∃ j : ℕ,
      ((j + 1 : ℕ) : ℝ) ≤ 1 + 5 * Real.rpow (Δ 0) (1 / 4 : ℝ) ∧
        Δ j ≤ (1 / 4 : ℝ) := by
  let a : ℝ := Real.rpow (Δ 0) (1 / 4 : ℝ)
  let N : ℕ := Nat.floor (5 * a)
  have ha_nonneg : 0 ≤ a := by
    -- The initial quarter root is nonnegative because the shifted gaps are nonnegative.
    exact Real.rpow_nonneg (hnonneg 0) _
  by_contra hno
  have hfloor_le : (N : ℝ) ≤ 5 * a := by
    -- `Nat.floor` always stays below the real quantity it floors.
    exact Nat.floor_le (show 0 ≤ 5 * a by positivity)
  have hall : ∀ j : ℕ, j ≤ N → (1 / 4 : ℝ) ≤ Δ j := by
    intro j hj
    have hj_bound : ((j + 1 : ℕ) : ℝ) ≤ 1 + 5 * a := by
      have hj_cast : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
      calc
        ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by norm_num
        _ ≤ (N : ℝ) + 1 := by linarith
        _ ≤ 1 + 5 * a := by linarith
    have hj_not_quarter : ¬ Δ j ≤ (1 / 4 : ℝ) := by
      intro hj_quarter
      exact hno ⟨j, hj_bound, hj_quarter⟩
    linarith [lt_of_not_ge hj_not_quarter]
  have htelescoped :
      Real.rpow (Δ (N + 1)) (1 / 4 : ℝ) ≤
        a - (((N + 1 : ℕ) : ℝ) / 5) := by
    have hall_before : ∀ j < N + 1, (1 / 4 : ℝ) ≤ Δ j := by
      intro j hj
      exact hall j (Nat.le_of_lt_succ hj)
    -- Telescope the one-step drops across the whole prefix of length `N + 1`.
    simpa [a] using shiftedGapQuarterRoot_bound_of_drop hdrop (k := N + 1) hall_before
  have hleft_nonneg : 0 ≤ Real.rpow (Δ (N + 1)) (1 / 4 : ℝ) := by
    exact Real.rpow_nonneg (hnonneg (N + 1)) _
  have hfloor_lt : 5 * a < ((N + 1 : ℕ) : ℝ) := by
    -- The successor of the floor already lies strictly above the floored real quantity.
    simpa [N, Nat.cast_add] using Nat.lt_floor_add_one (5 * a)
  have ha_lt : a < (((N + 1 : ℕ) : ℝ) / 5) := by
    exact (lt_div_iff₀ (show (0 : ℝ) < 5 by norm_num)).2 <| by
      simpa [mul_comm] using hfloor_lt
  -- The telescoped upper bound is negative, contradicting nonnegativity of quarter roots.
  linarith

/-- Helper for Proposition 4.4.10: the source assumption `1 ≤ ξ` absorbs the additive `1` in the
generic quarter-entry budget once the initial shifted quarter root is bounded by
`(21 / 20) * sqrt ξ`. -/
private lemma one_add_five_mul_initialQuarterRoot_le_sqrtCharacteristicBudget
    {ξ a : ℝ}
    (hxi : 1 ≤ ξ)
    (ha : a ≤ (21 / 20 : ℝ) * Real.sqrt ξ) :
    1 + 5 * a ≤ (25 / 4 : ℝ) * Real.sqrt ξ := by
  have hsqrt_ge_one : 1 ≤ Real.sqrt ξ := by
    have hξ_nonneg : 0 ≤ ξ := le_trans (by norm_num) hxi
    have hsq :
        (1 : ℝ) ^ (2 : ℕ) ≤ (Real.sqrt ξ) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt hξ_nonneg]
      nlinarith
    simpa using
      (sq_le_sq₀ (by positivity : 0 ≤ (1 : ℝ)) (Real.sqrt_nonneg ξ)).1 hsq
  -- Replace the generic initial quarter-root term by the explicit `sqrt ξ` bridge, then absorb
  -- the remaining additive `1` using `sqrt ξ ≥ 1`.
  calc
    1 + 5 * a ≤ 1 + 5 * ((21 / 20 : ℝ) * Real.sqrt ξ) := by
      gcongr
    _ = 1 + (21 / 4 : ℝ) * Real.sqrt ξ := by
      ring
    _ ≤ Real.sqrt ξ + (21 / 4 : ℝ) * Real.sqrt ξ := by
      gcongr
    _ = (25 / 4 : ℝ) * Real.sqrt ξ := by
      ring

/-- Helper for Proposition 4.4.10: a quartic upper bound on a nonnegative quantity yields the
corresponding quarter-root upper bound. -/
private lemma quarterRoot_le_of_le_fourthPower
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hab : a ≤ b ^ (4 : ℕ)) :
    Real.rpow a (1 / 4 : ℝ) ≤ b := by
  have hquarter_fourth :
      Real.rpow (b ^ (4 : ℕ)) (1 / 4 : ℝ) = b := by
    -- Raise the quartic majorant to the quarter power before collapsing the exponents.
    calc
      Real.rpow (b ^ (4 : ℕ)) (1 / 4 : ℝ)
          = Real.rpow b ((4 : ℝ) * (1 / 4 : ℝ)) := by
              simpa [Real.rpow_natCast] using
                (Real.rpow_mul hb (4 : ℝ) (1 / 4 : ℝ)).symm
      _ = b := by
            norm_num [Real.rpow_one]
  -- Monotonicity of `Real.rpow` transfers the quartic comparison to quarter-root variables.
  exact
    (Real.rpow_le_rpow ha hab (by positivity : 0 ≤ (1 / 4 : ℝ))).trans_eq hquarter_fourth

/-- Helper for Proposition 4.4.10: the frozen quadratic Taylor model at the full Newton trial
point is exactly the current objective value minus half of the Newton curvature energy. -/
private lemma modifiedNewtonFullTrial_secondOrderTaylorModel_eq_sub_halfNewtonCurvature
    {φ : E → ℝ} {x0 : E}
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} :
    secondOrderTaylorModelAt φ (method k)
        (NewtonSystem.step (∇ φ) (method.toMethod.x k)) =
      φ (method k) -
        (1 / 2 : ℝ) *
          inner ℝ
            (hessian φ (method k) (method.toMethod.searchDirection k))
            (method.toMethod.searchDirection k) := by
  let x := method k
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  have hnewton_eq : hessian φ x d = ∇ φ x := by
    -- Expanding the Newton search direction recovers the frozen linearized gradient equation.
    change
      (fderiv ℝ (∇ φ) ↑(method.toMethod.x k))
          ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
              (method.toMethod.x k).property).symm)
            (∇ φ ↑(method.toMethod.x k))) =
        ∇ φ ↑(method.toMethod.x k)
    exact
      ContinuousLinearEquiv.apply_symm_apply
        ((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
          (method.toMethod.x k).property)
        (∇ φ ↑(method.toMethod.x k))
  have hT_disp : T - x = -d := by
    -- The full Newton trial is obtained from the current iterate by the unit Newton correction.
    simp [T, x, d, NewtonSystem.step_def, DampedNewton.Method.searchDirection, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  -- Normalize the full-trial Taylor-model value into the Newton curvature form used later.
  rw [secondOrderTaylorModelAt_apply, hT_disp, ← hnewton_eq]
  simp [x, d, T, inner_smul_left, inner_smul_right, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm]

/-- Helper for Proposition 4.4.10: along the accepted Newton ray, the frozen quadratic Taylor
model interpolates exactly between the current objective value and the full-trial model value
with coefficients `(1 - α)^2` and `α (2 - α)`. -/
private lemma modifiedNewtonAlphaSearchPoint_secondOrderTaylorModel_eq_sqSelf_add_fullTrialModel
    {φ : E → ℝ} {x0 : E}
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} {α : ℝ} :
    secondOrderTaylorModelAt φ (method k) (method k - α • method.toMethod.searchDirection k) =
      (1 - α) ^ (2 : ℕ) * φ (method k) +
        (α * (2 - α)) *
          secondOrderTaylorModelAt φ (method k)
            (NewtonSystem.step (∇ φ) (method.toMethod.x k)) := by
  let x := method k
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let curv : ℝ := inner ℝ (hessian φ x d) d
  have hnewton_eq : hessian φ x d = ∇ φ x := by
    -- Expanding the Newton search direction recovers the frozen linearized gradient equation.
    change
      (fderiv ℝ (∇ φ) ↑(method.toMethod.x k))
          ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
              (method.toMethod.x k).property).symm)
            (∇ φ ↑(method.toMethod.x k))) =
        ∇ φ ↑(method.toMethod.x k)
    exact
      ContinuousLinearEquiv.apply_symm_apply
        ((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
          (method.toMethod.x k).property)
        (∇ φ ↑(method.toMethod.x k))
  have hmodel_ray :
      secondOrderTaylorModelAt φ x (x - α • d) =
        φ x - α * curv + (α ^ (2 : ℕ) / 2) * curv := by
    -- Along the Newton ray, the Taylor model collapses to a scalar quadratic in `α`.
    rw [secondOrderTaylorModelAt_apply, ← hnewton_eq]
    simp [x, d, curv, inner_smul_left, inner_smul_right, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm, mul_assoc]
    ring
  have hmodel_trial :
      secondOrderTaylorModelAt φ x T = φ x - (1 / 2 : ℝ) * curv := by
    -- Reuse the dedicated full-trial model identity so the interpolation stays in one spelling.
    simpa [x, d, T, curv] using
      modifiedNewtonFullTrial_secondOrderTaylorModel_eq_sub_halfNewtonCurvature
        (method := method) (k := k)
  calc
    secondOrderTaylorModelAt φ (method k) (method k - α • method.toMethod.searchDirection k)
        = φ x - α * curv + (α ^ (2 : ℕ) / 2) * curv := by
            simpa [x, d, curv] using hmodel_ray
    _ = (1 - α) ^ (2 : ℕ) * φ x + (α * (2 - α)) * (φ x - (1 / 2 : ℝ) * curv) := by
          ring
    _ = (1 - α) ^ (2 : ℕ) * φ (method k) +
          (α * (2 - α)) * secondOrderTaylorModelAt φ (method k) T := by
          rw [hmodel_trial]

/-- Helper for Proposition 4.4.10: on the frozen quadratic Taylor-model surface, the difference
between the accepted Newton-ray point and the minimizer segment point is exactly the sum of a
linear trial-error term and a negative quadratic trial-error correction. -/
private lemma modifiedNewtonAlphaSearchPoint_secondOrderTaylorModel_sub_lineMap_eq_trialErrorCorrection
    {φ : E → ℝ} {L : NNReal} {x0 xStar : E}
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} {α : ℝ} :
    secondOrderTaylorModelAt φ (method k) (method k - α • method.toMethod.searchDirection k) -
        secondOrderTaylorModelAt φ (method k) (AffineMap.lineMap (method k) xStar α) =
      α * (1 - α) *
          inner ℝ (∇ φ (method k))
            (NewtonSystem.step (∇ φ) (method.toMethod.x k) - xStar) -
        (α ^ (2 : ℕ) / 2) *
          inner ℝ
            (hessian φ (method k)
              (NewtonSystem.step (∇ φ) (method.toMethod.x k) - xStar))
            (NewtonSystem.step (∇ φ) (method.toMethod.x k) - xStar) := by
  let x := method k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let u : E := T - x
  let w : E := T - xStar
  have hselfAdjoint : IsSelfAdjoint (hessian φ x) := by
    -- A `C²` objective has self-adjoint Hessian at the current iterate.
    simpa [x] using
      (fderiv_gradient_isSymmetric_of_contDiffAt (f := φ) (x := x)
        (hf := hφ_hessian.contDiff.contDiffAt (x := x))).isSelfAdjoint
  have hu_eq_neg_grad : hessian φ x u = -∇ φ x := by
    have hnewton_eq : hessian φ x (method.toMethod.searchDirection k) = ∇ φ x := by
      -- Expanding the Newton search direction recovers the linearized gradient equation.
      change
        (fderiv ℝ (∇ φ) ↑(method.toMethod.x k))
            ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
                (method.toMethod.x k).property).symm)
              (∇ φ ↑(method.toMethod.x k))) =
          ∇ φ ↑(method.toMethod.x k)
      exact
        ContinuousLinearEquiv.apply_symm_apply
          ((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
            (method.toMethod.x k).property)
          (∇ φ ↑(method.toMethod.x k))
    have hu_eq_neg_d : u = -method.toMethod.searchDirection k := by
      -- The full Newton trial differs from the current iterate by the unit Newton correction.
      simp [u, T, x, NewtonSystem.step_def, DampedNewton.Method.searchDirection, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]
    rw [hu_eq_neg_d, ContinuousLinearMap.map_neg, hnewton_eq]
  have hsearch_disp : method k - α • method.toMethod.searchDirection k = x + α • u := by
    -- Rewrite the accepted Newton-ray comparison point through the full-trial displacement.
    simp [u, T, x, NewtonSystem.step_def, DampedNewton.Method.searchDirection, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  have hline_disp : AffineMap.lineMap (method k) xStar α = x + α • (u - w) := by
    -- The minimizer segment displacement differs from the full-trial displacement by `w = T - x*`.
    have hline_raw :
        AffineMap.lineMap (method k) xStar α = x + α • (xStar - x) := by
      simpa [x] using AffineMap.lineMap_apply x xStar α
    have hw_split : xStar - x = u - w := by
      simp [u, w, x, T, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hline_raw, hw_split]
  have hcross :
      inner ℝ (hessian φ x w) u = inner ℝ (hessian φ x u) w := by
    -- Self-adjointness identifies the mixed Hessian terms in the quadratic expansion.
    calc
      inner ℝ (hessian φ x w) u = inner ℝ u (hessian φ x w) := by rw [real_inner_comm]
      _ = inner ℝ (hessian φ x u) w := (hselfAdjoint.isSymmetric u w).symm
  -- Expand both frozen Taylor-model values around the same base point `x`.
  rw [hsearch_disp, hline_disp, secondOrderTaylorModelAt_apply, secondOrderTaylorModelAt_apply]
  rw [sub_eq_add_neg]
  have hrewrite :
      φ x + inner ℝ (∇ φ x) (α • u) +
          (1 / 2 : ℝ) * inner ℝ (hessian φ x (α • u)) (α • u) +
          -(φ x + inner ℝ (∇ φ x) (α • (u - w)) +
              (1 / 2 : ℝ) * inner ℝ (hessian φ x (α • (u - w))) (α • (u - w))) =
        α * (1 - α) * inner ℝ (∇ φ x) w -
          (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w := by
    -- Route correction: keep the whole model difference on the frozen Taylor-model surface and
    -- collapse it to one linear trial-error term plus one quadratic correction term.
    rw [hu_eq_neg_grad]
    simp [ContinuousLinearMap.map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, inner_smul_left, inner_smul_right, hcross, sub_eq_add_neg, pow_two,
      mul_assoc, mul_left_comm, mul_comm]
    ring
  simpa [x, T, u, w] using hrewrite

/-- Helper for Proposition 4.4.10: after rewriting the accepted Newton ray through the frozen
quadratic Taylor model, only the square gap term and the weighted full-trial cubic remainder
remain. -/
private lemma modifiedNewtonAlphaSearchPoint_secondOrderTaylorModelGap_le_sqGap_add_trialCubic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    secondOrderTaylorModelAt φ (method k) (method k - α • method.toMethod.searchDirection k) -
        φ xStar ≤
      (1 - α) ^ (2 : ℕ) * (φ (method k) - φ xStar) +
        (α * (2 - α)) * (((L : ℝ) / 6) * ‖method k - xStar‖ ^ (3 : ℕ)) := by
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  have htrial_gap :
      secondOrderTaylorModelAt φ (method k) T - φ xStar ≤
        ((L : ℝ) / 6) * ‖method k - xStar‖ ^ (3 : ℕ) := by
    -- The full Newton trial sits above the minimizer value only by the current cubic remainder.
    simpa [T] using
      modifiedNewtonFullTrialTaylorModelGap_le_currentCubic
        hσ hφ_strong hφ_hessian hxStar method (k := k)
  have htrial_weight_nonneg : 0 ≤ α * (2 - α) := by
    -- The ray weight stays nonnegative on the admissible interval `α ∈ [0, 1]`.
    nlinarith [hα.1, hα.2]
  calc
    secondOrderTaylorModelAt φ (method k) (method k - α • method.toMethod.searchDirection k) -
        φ xStar =
      (1 - α) ^ (2 : ℕ) * (φ (method k) - φ xStar) +
        (α * (2 - α)) *
          (secondOrderTaylorModelAt φ (method k) T - φ xStar) := by
            rw [modifiedNewtonAlphaSearchPoint_secondOrderTaylorModel_eq_sqSelf_add_fullTrialModel
              (method := method) (k := k) (α := α)]
            ring
    _ ≤
      (1 - α) ^ (2 : ℕ) * (φ (method k) - φ xStar) +
        (α * (2 - α)) * (((L : ℝ) / 6) * ‖method k - xStar‖ ^ (3 : ℕ)) := by
            gcongr

/-- Helper for Proposition 4.4.10: exact line search plus the one-sided Hessian-Lipschitz Taylor
remainder bounds the accepted point by the frozen quadratic Taylor model at any comparison point
on the Newton ray, with only the direction-cubic remainder left. -/
private lemma modifiedNewtonObjectiveSucc_le_alphaRayTaylorModel_add_directionCubic
    {φ : E → ℝ} {L : NNReal} {x0 : E}
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    φ (method (k + 1)) ≤
      secondOrderTaylorModelAt φ (method k) (method k - α • method.toMethod.searchDirection k) +
        ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖method.toMethod.searchDirection k‖ ^ (3 : ℕ) := by
  let x := method k
  let y := method k - α • method.toMethod.searchDirection k
  have hcomparison : φ (method (k + 1)) ≤ φ y := by
    -- Exact line search compares the accepted point with the same Newton ray point `y`.
    simpa [y] using modifiedNewtonObjectiveSucc_le_alphaRayComparison method k hα
  have herror :=
    HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le
      hφ_hessian x y
  have hupper :
      φ y ≤ secondOrderTaylorModelAt φ x y + ((L : ℝ) / 6) * ‖(y - x : E)‖ ^ (3 : ℕ) := by
    -- Use the upper side of the quadratic Taylor remainder bound at the comparison point `y`.
    linarith [(abs_le.mp herror).2]
  have hy_norm :
      ‖(y - x : E)‖ = α * ‖method.toMethod.searchDirection k‖ := by
    -- The Newton-ray displacement has length `α` times the direction norm.
    simp [x, y, norm_smul, Real.norm_of_nonneg hα.1]
  calc
    φ (method (k + 1)) ≤ φ y := hcomparison
    _ ≤ secondOrderTaylorModelAt φ x y + ((L : ℝ) / 6) * ‖(y - x : E)‖ ^ (3 : ℕ) := hupper
    _ = secondOrderTaylorModelAt φ (method k) (method k - α • method.toMethod.searchDirection k) +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖method.toMethod.searchDirection k‖ ^ (3 : ℕ) := by
          rw [hy_norm]
          simp [x, y, mul_pow, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 4.4.10: evaluating the frozen Taylor model at `xStar` separates the
current objective gap into the Newton curvature energy minus the full-trial error curvature, with
only the cubic Hessian-Lipschitz remainder left. -/
private lemma modifiedNewtonObjectiveGap_le_halfNewtonEnergy_sub_halfTrialError_add_currentCubic
    {φ : E → ℝ} {L : NNReal} {x0 xStar : E}
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {k : ℕ} :
    φ (method k) - φ xStar ≤
      (1 / 2 : ℝ) *
          inner ℝ
            (hessian φ (method k) (method.toMethod.searchDirection k))
            (method.toMethod.searchDirection k) -
        (1 / 2 : ℝ) *
          inner ℝ
            (hessian φ (method k)
              (NewtonSystem.step (∇ φ) (method.toMethod.x k) - xStar))
            (NewtonSystem.step (∇ φ) (method.toMethod.x k) - xStar) +
        ((L : ℝ) / 6) * ‖method k - xStar‖ ^ (3 : ℕ) := by
  let x := method k
  let d := method.toMethod.searchDirection k
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x k)
  let w : E := T - xStar
  have herror :=
    HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le
      hφ_hessian x xStar
  have hmodel_lower :
      secondOrderTaylorModelAt φ x xStar -
          ((L : ℝ) / 6) * ‖(xStar - x : E)‖ ^ (3 : ℕ) ≤
        φ xStar := by
    -- Use the lower side of the Taylor remainder bound exactly at the minimizer point `xStar`.
    linarith [(abs_le.mp herror).1]
  have hnewton_eq : hessian φ x d = ∇ φ x := by
    -- Expanding the Newton search direction recovers the frozen linearized gradient equation.
    change
      (fderiv ℝ (∇ φ) ↑(method.toMethod.x k))
          ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
              (method.toMethod.x k).property).symm)
            (∇ φ ↑(method.toMethod.x k))) =
        ∇ φ ↑(method.toMethod.x k)
    exact
      ContinuousLinearEquiv.apply_symm_apply
        ((fderiv ℝ (∇ φ) ↑(method.toMethod.x k)).toContinuousLinearEquivOfDetNeZero
          (method.toMethod.x k).property)
        (∇ φ ↑(method.toMethod.x k))
  have hselfAdjoint : IsSelfAdjoint (hessian φ x) := by
    -- A `C²` objective has self-adjoint Hessian at the current iterate.
    simpa [x] using
      (fderiv_gradient_isSymmetric_of_contDiffAt (f := φ) (x := x)
        (hf := hφ_hessian.contDiff.contDiffAt (x := x))).isSelfAdjoint
  have hdisp : xStar - x = -(d + w) := by
    -- The minimizer displacement splits into the Newton correction plus the full-trial error.
    simp [w, T, x, d, NewtonSystem.step_def, DampedNewton.Method.searchDirection, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  have hcross :
      inner ℝ (hessian φ x w) d = inner ℝ (hessian φ x d) w := by
    -- Self-adjointness identifies the mixed Hessian terms in the `d + w` expansion.
    calc
      inner ℝ (hessian φ x w) d = inner ℝ d (hessian φ x w) := by rw [real_inner_comm]
      _ = inner ℝ (hessian φ x d) w := (hselfAdjoint.isSymmetric d w).symm
  have hmodel_eval :
      secondOrderTaylorModelAt φ x xStar =
        φ x -
          (1 / 2 : ℝ) * inner ℝ (hessian φ x d) d +
          (1 / 2 : ℝ) * inner ℝ (hessian φ x w) w := by
    -- Route correction: evaluate the frozen model at `xStar` through `xStar - x = -(d + w)` so
    -- the mixed terms cancel exactly and only the Newton energy and full-trial error remain.
    rw [secondOrderTaylorModelAt_apply, hdisp, ← hnewton_eq]
    simp [ContinuousLinearMap.map_add, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, hcross, x, d, T, w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    ring
  have hnorm_eq : ‖(xStar - x : E)‖ = ‖x - xStar‖ := by
    simpa [norm_sub_rev]
  rw [hmodel_eval, hnorm_eq] at hmodel_lower
  -- Rearranging the exact frozen-model evaluation leaves the current gap bounded by the Newton
  -- curvature energy minus the full-trial error curvature, plus the cubic remainder.
  linarith

/-- Helper for Proposition 4.4.10: exact line search bounds the first accepted-step gap by the
scalar Taylor envelope along the initial Newton ray, with the exact initial Newton curvature kept
visible until the later quartic budget step. -/
private lemma modifiedNewtonInitialAcceptedGap_le_alphaRayScalarEnvelope
    {φ : E → ℝ} {L : NNReal} {x0 xStar : E}
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    φ (method 1) - φ xStar ≤
      (φ (method 0) - φ xStar) -
        α *
          inner ℝ
            (hessian φ (method 0) (method.toMethod.searchDirection 0))
            (method.toMethod.searchDirection 0) +
        (α ^ (2 : ℕ) / 2) *
          inner ℝ
            (hessian φ (method 0) (method.toMethod.searchDirection 0))
            (method.toMethod.searchDirection 0) +
        ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖method.toMethod.searchDirection 0‖ ^ (3 : ℕ) := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let curv : ℝ := inner ℝ (hessian φ x d) d
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  have haccepted_model :
      φ (method 1) ≤
        secondOrderTaylorModelAt φ x (x - α • d) + directionCubic := by
    -- Start from the exact accepted-step comparison and keep only the direction-cubic remainder.
    simpa [x, d, directionCubic] using
      modifiedNewtonObjectiveSucc_le_alphaRayTaylorModel_add_directionCubic
        hφ_hessian method (k := 0) hα
  have hmodel_ray :
      secondOrderTaylorModelAt φ x (x - α • d) =
        φ x - α * curv + (α ^ (2 : ℕ) / 2) * curv := by
    -- Route correction: use the exact frozen-model interpolation with the full Newton trial
    -- instead of the false pointwise distance-surface bound from the earlier route.
    calc
      secondOrderTaylorModelAt φ x (x - α • d) =
          (1 - α) ^ (2 : ℕ) * φ x +
            (α * (2 - α)) * secondOrderTaylorModelAt φ x T := by
              simpa [x, d, T] using
                modifiedNewtonAlphaSearchPoint_secondOrderTaylorModel_eq_sqSelf_add_fullTrialModel
                  (method := method) (k := 0) (α := α)
      _ =
          (1 - α) ^ (2 : ℕ) * φ x +
            (α * (2 - α)) * (φ x - (1 / 2 : ℝ) * curv) := by
              rw [modifiedNewtonFullTrial_secondOrderTaylorModel_eq_sub_halfNewtonCurvature
                (method := method) (k := 0)]
              simp [x, d, T, curv]
      _ = φ x - α * curv + (α ^ (2 : ℕ) / 2) * curv := by
            ring
  calc
    φ (method 1) - φ xStar ≤
        secondOrderTaylorModelAt φ x (x - α • d) - φ xStar + directionCubic := by
          linarith
    _ = (φ x - φ xStar) - α * curv + (α ^ (2 : ℕ) / 2) * curv + directionCubic := by
          rw [hmodel_ray]
          ring
    _ =
        (φ (method 0) - φ xStar) -
          α *
            inner ℝ
              (hessian φ (method 0) (method.toMethod.searchDirection 0))
              (method.toMethod.searchDirection 0) +
          (α ^ (2 : ℕ) / 2) *
            inner ℝ
              (hessian φ (method 0) (method.toMethod.searchDirection 0))
              (method.toMethod.searchDirection 0) +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖method.toMethod.searchDirection 0‖ ^ (3 : ℕ) := by
          simp [x, d, curv, directionCubic]

/-- Helper for Proposition 4.4.10: scaling the strong-convexity quadratic surface by
`((2 L²) / σ³)` produces the square `ξ²` of the modified-Newton characteristic quantity. -/
private lemma modifiedNewton_initial_quadratic_normalization
    {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ) :
    (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) *
        ((σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) =
      modifiedNewtonCharacteristicQuantity σ L x0 xStar ^ (2 : ℕ) := by
  -- Expand `ξ = (L / σ) * ‖x0 - xStar‖` once and clear the scalar denominators.
  simp [modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm]
  field_simp [hσ.ne']
  ring

/-- Helper for Proposition 4.4.10: scaling the cubic remainder by `((2 L²) / σ³)` produces the
factor `((1 / 3) * α³ * ξ) * ξ²` needed in the initial local model. -/
private lemma modifiedNewton_initial_cubic_normalization
    {σ : ℝ} {L : NNReal} {x0 xStar : E} {α : ℝ}
    (hσ : 0 < σ) :
    (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ)) *
        (((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x0 - xStar‖ ^ (3 : ℕ)) =
      ((1 / 3 : ℝ) * α ^ (3 : ℕ) * modifiedNewtonCharacteristicQuantity σ L x0 xStar) *
        modifiedNewtonCharacteristicQuantity σ L x0 xStar ^ (2 : ℕ) := by
  -- Expand the characteristic quantity and then group the scalar factors into `ξ * ξ²`.
  simp [modifiedNewtonCharacteristicQuantity_def, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm]
  field_simp [hσ.ne']
  ring

/-- Helper for Proposition 4.4.10: at `k = 0`, the Newton search direction is the initial
minimizer error minus the full-trial error. -/
private lemma modifiedNewtonInitialSearchDirection_eq_error_sub_fullTrialError
    {φ : E → ℝ} {x0 xStar : E}
    (method : ModifiedNewtonMethod φ x0) :
    method.toMethod.searchDirection 0 =
      (x0 - xStar) - (NewtonSystem.step (∇ φ) (method.toMethod.x 0) - xStar) := by
  have hsub :
      method.toMethod.searchDirection 0 - (method 0 - xStar) =
        -(NewtonSystem.step (∇ φ) (method.toMethod.x 0) - xStar) := by
    -- Reuse the global search-direction/trial-error identity at the initial index.
    simpa using
      modifiedNewtonSearchDirectionSubError_eq_neg_fullTrialError
        (method := method) (xStar := xStar) (k := 0)
  -- Move the current error term to the other side so the source decomposition is explicit.
  calc
    method.toMethod.searchDirection 0 =
        (method.toMethod.searchDirection 0 - (method 0 - xStar)) + (method 0 - xStar) := by
          abel
    _ = -(NewtonSystem.step (∇ φ) (method.toMethod.x 0) - xStar) + (method 0 - xStar) := by
          rw [hsub]
    _ = (method 0 - xStar) - (NewtonSystem.step (∇ φ) (method.toMethod.x 0) - xStar) := by
          abel
    _ = (x0 - xStar) - (NewtonSystem.step (∇ φ) (method.toMethod.x 0) - xStar) := by
          simp

/-- Helper for Proposition 4.4.10: at `k = 0`, the Newton direction norm is bounded by the sum of
the initial distance and the full-trial error norm. -/
private lemma modifiedNewtonInitialSearchDirectionNorm_le_distance_add_trialError
    {φ : E → ℝ} {x0 xStar : E}
    (method : ModifiedNewtonMethod φ x0) :
    ‖method.toMethod.searchDirection 0‖ ≤
      ‖x0 - xStar‖ + ‖NewtonSystem.step (∇ φ) (method.toMethod.x 0) - xStar‖ := by
  have hd_eq :
      method.toMethod.searchDirection 0 =
        (x0 - xStar) - (NewtonSystem.step (∇ φ) (method.toMethod.x 0) - xStar) := by
    -- Keep the source decomposition `d = e - w` explicit before taking norms.
    exact
      modifiedNewtonInitialSearchDirection_eq_error_sub_fullTrialError
        (method := method) (xStar := xStar)
  calc
    ‖method.toMethod.searchDirection 0‖ =
        ‖(x0 - xStar) - (NewtonSystem.step (∇ φ) (method.toMethod.x 0) - xStar)‖ := by
          rw [hd_eq]
    _ ≤ ‖x0 - xStar‖ + ‖NewtonSystem.step (∇ φ) (method.toMethod.x 0) - xStar‖ :=
          norm_sub_le _ _

/-- Helper for Proposition 4.4.10: after combining the accepted-step Taylor envelope with the
exact frozen-model decomposition at `k = 0`, the initial shifted gap is reduced to the single
specialized budget surface that still mixes the curvature, trial error, and direction cubic. -/
private lemma modifiedNewtonInitialAcceptedGap_le_specializedBudgetSurface
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let curv : ℝ := inner ℝ (hessian φ x d) d
    let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
    let currentCubic : ℝ := ((L : ℝ) / 6) * ‖x0 - xStar‖ ^ (3 : ℕ)
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
      s * ((((1 - α) ^ (2 : ℕ) / 2) * curv) -
          (1 / 2 : ℝ) * inner ℝ (hessian φ x w) w +
          currentCubic +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)) := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let curv : ℝ := inner ℝ (hessian φ x d) d
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  let currentCubic : ℝ := ((L : ℝ) / 6) * ‖x0 - xStar‖ ^ (3 : ℕ)
  have henvelope :
      φ (method 1) - φ xStar ≤
        (φ x - φ xStar) - α * curv + (α ^ (2 : ℕ) / 2) * curv +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ) := by
    -- Keep the accepted point on the exact frozen Taylor envelope along the initial Newton ray.
    simpa [x, d, curv, α] using
      modifiedNewtonInitialAcceptedGap_le_alphaRayScalarEnvelope
        (hφ_hessian := hφ_hessian) (method := method) (xStar := xStar) (α := α) hα
  have hgap_curvature :
      φ x - φ xStar ≤
        (1 / 2 : ℝ) * curv -
          (1 / 2 : ℝ) * inner ℝ (hessian φ x w) w + currentCubic := by
    -- Evaluate the initial objective gap through the Newton energy minus the full-trial error
    -- curvature so the remaining blocker is a single coupled surface.
    simpa [x, d, w, curv, currentCubic] using
      modifiedNewtonObjectiveGap_le_halfNewtonEnergy_sub_halfTrialError_add_currentCubic
        (hφ_hessian := hφ_hessian) (method := method) (xStar := xStar) (k := 0)
  have hs_nonneg : 0 ≤ s := by
    positivity
  have hsurface :
      φ (method 1) - φ xStar ≤
        (((1 - α) ^ (2 : ℕ) / 2) * curv) -
          (1 / 2 : ℝ) * inner ℝ (hessian φ x w) w +
          currentCubic +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ) := by
    -- Combine the accepted-step envelope with the exact current-gap decomposition.
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsurface hs_nonneg
  -- Normalize the left-hand side to the shifted gap surface and keep the right-hand side as one
  -- scalar frontier.
  simpa [modifiedNewtonShiftedNormalizedGap, x, d, T, w, curv, s, currentCubic,
    mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Proposition 4.4.10: the first shifted accepted-step gap should satisfy the direct
quartic budget once the accepted-step scalar envelope is combined with the frozen-model
decomposition and the full-trial error surface at `k = 0`. -/
private lemma modifiedNewtonInitialAcceptedGap_le_lineMap_trialCorrection_surface
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
      s * ((secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) - φ xStar) +
          α * (1 - α) * inner ℝ (∇ φ x) w -
          (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)) := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  have henvelope :
      φ (method 1) ≤ secondOrderTaylorModelAt φ x (x - α • d) + directionCubic := by
    -- Keep the accepted point on the exact frozen Taylor envelope along the initial Newton ray.
    simpa [x, d, directionCubic] using
      modifiedNewtonObjectiveSucc_le_alphaRayTaylorModel_add_directionCubic
        (hφ_hessian := hφ_hessian) (method := method) (k := 0) (α := α) hα
  have htrialCorrection :
      secondOrderTaylorModelAt φ x (x - α • d) - secondOrderTaylorModelAt φ x
          (AffineMap.lineMap x xStar α) =
        α * (1 - α) * inner ℝ (∇ φ x) w -
          (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w := by
    -- Route correction: keep the exact trial-error correction visible before any coarse
    -- norm bound or scalarization.
    simpa [x, d, T, w] using
      modifiedNewtonAlphaSearchPoint_secondOrderTaylorModel_sub_lineMap_eq_trialErrorCorrection
        (hφ_hessian := hφ_hessian) (method := method) (k := 0) (α := α)
  have hsurface :
      φ (method 1) - φ xStar ≤
        (secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) - φ xStar) +
          α * (1 - α) * inner ℝ (∇ φ x) w -
          (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
          directionCubic := by
    -- Substitute the exact trial-correction identity into the accepted-point Taylor envelope.
    linarith
  have hs_nonneg : 0 ≤ s := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsurface hs_nonneg
  -- Normalize the accepted-point inequality to the shifted gap surface used by the global proof.
  simpa [modifiedNewtonShiftedNormalizedGap, x, d, T, w, s, directionCubic,
    mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Proposition 4.4.10: after the line-map / trial-correction pivot, the remaining
initial analytic step is to collapse the coupled frozen-model surface to the distance budget
`((1 - α)^2) * ((σ / 2) * ‖x₀ - x*‖²) + ((L / 6) * α³ * ‖x₀ - x*‖³)`. -/
private lemma modifiedNewton_initial_lineMap_model_le_segment_budget
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let x := method 0
    secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) - φ xStar ≤
      (1 - α) * (φ x - φ xStar) -
        α * (1 - α) * ((σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) +
        ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x0 - xStar‖ ^ (3 : ℕ) := by
  let x := method 0
  have hmodel :
      secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) ≤
        φ (AffineMap.lineMap x xStar α) +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x0 - xStar‖ ^ (3 : ℕ) := by
    -- Keep the exact Hessian-Lipschitz segment remainder in terms of the endpoint distance.
    simpa [x] using
      secondOrderTaylorModelAt_lineMap_le_objective_add_segmentCubic
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (x := x) (xStar := xStar) (α := α) hα
  have hsegment :
      φ (AffineMap.lineMap x xStar α) - φ xStar ≤
        (1 - α) * (φ x - φ xStar) -
          α * (1 - α) * ((σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
    have hstrong_segment :
        φ (AffineMap.lineMap x xStar α) ≤
          (1 - α) * φ x + α * φ xStar -
            (1 - α) * α * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) := by
      -- Strong convexity along the minimizer segment contributes the exact quadratic correction.
      rw [AffineMap.lineMap_apply_module]
      exact hφ_strong.2 (by simp) (by simp) (sub_nonneg.mpr hα.2) hα.1 (by ring)
    -- Subtract the minimizer value while keeping the segment correction explicit.
    simpa [x, mul_assoc, mul_left_comm, mul_comm] using hstrong_segment
  -- Combine the segment Taylor upper bound with the strong-convexity segment estimate.
  linarith

/-- Helper for Proposition 4.4.10: strong convexity at the initial point gives an upper tangent
bound on the initial objective gap in terms of the initial minimizer error. -/
private lemma modifiedNewton_initial_gap_le_gradient_error_sub_distance_budget
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0) :
    let x := method 0
    let e : E := x0 - xStar
    φ x - φ xStar ≤
      inner ℝ (∇ φ x) e - ((σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  let x := method 0
  let e : E := x0 - xStar
  let hφ_C1 : ContDiff ℝ 1 φ := hφ_hessian.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hgradAt : HasGradientAt φ (∇ φ x) x := by
    -- The `C²` hypothesis gives the gradient needed for the strong-convexity tangent inequality.
    exact (hφ_C1.contDiffAt (x := x)).differentiableAt one_ne_zero |>.hasGradientAt
  have hgrowth :
      φ xStar ≥
        φ x + inner ℝ (∇ φ x) (xStar - x) + (σ / 2) * ‖xStar - x‖ ^ (2 : ℕ) := by
    -- Apply the lower tangent inequality at the current iterate and evaluate it at `xStar`.
    exact
      StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
        hφ_strong (by simp) (by simp) hgradAt
  have hrewrite :
      φ x + inner ℝ (∇ φ x) (xStar - x) + (σ / 2) * ‖xStar - x‖ ^ (2 : ℕ) =
        φ x - inner ℝ (∇ φ x) e + (σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    -- Rewrite everything in the source error variable `e = x₀ - x*`.
    rw [show xStar - x = -e by simp [x, e, sub_eq_add_neg]]
    simp [e, x, norm_sub_rev, inner_smul_right, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]
  rw [hrewrite] at hgrowth
  -- Rearranging the tangent inequality isolates the upper bound on the initial gap.
  linarith

/-- Helper for Proposition 4.4.10: the mixed Hessian trial-error term is absorbed by the weighted
quadratic form of the initial Newton direction and the negative trial-error curvature. -/
private lemma modifiedNewton_initial_weighted_trial_absorption
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ} :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    α * (1 - α) * inner ℝ (hessian φ x d) w -
        (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w ≤
      ((1 - α) ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x d) d := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let hφ_C2 : ContDiff ℝ 2 φ := hφ_hessian.contDiff
  have hUniv_nonempty : (interior (Set.univ : Set E)).Nonempty := by
    simp
  have hcont : ContinuousOn φ (Set.univ : Set E) := hφ_C2.continuous.continuousOn
  have hC2 : ContDiffOn ℝ 2 φ (interior (Set.univ : Set E)) := by
    simpa using hφ_C2.contDiffOn
  have hbound : σ • (1 : E →L[ℝ] E) ≤ hessian φ x := by
    -- Whole-space strong convexity supplies the Hessian Loewner lower bound at the initial point.
    have hiff :=
      (strongConvexOn_iff_hessian_lower_bound
        hσ convex_univ hUniv_nonempty hcont hC2).1 hφ_strong
    simpa [x] using hiff x (by simp)
  have hselfAdjoint : IsSelfAdjoint (hessian φ x) := by
    -- The Hessian is self-adjoint because the objective is `C²`.
    simpa [x] using
      (fderiv_gradient_isSymmetric_of_contDiffAt (f := φ) (x := x)
        (hf := hφ_C2.contDiffAt (x := x))).isSelfAdjoint
  have hquad_nonneg :
      0 ≤
        inner ℝ (hessian φ x (((1 - α) • d) - α • w)) (((1 - α) • d) - α • w) := by
    have hquad :=
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hσ hC2 (by simp : x ∈ interior (Set.univ : Set E))).1 hbound (((1 - α) • d) - α • w)
    exact le_trans (by positivity) hquad
  have hcross :
      inner ℝ (hessian φ x w) d = inner ℝ (hessian φ x d) w := by
    -- Self-adjointness identifies the two mixed Hessian terms in the completed square.
    calc
      inner ℝ (hessian φ x w) d = inner ℝ d (hessian φ x w) := by rw [real_inner_comm]
      _ = inner ℝ (hessian φ x d) w := (hselfAdjoint.isSymmetric d w).symm
  have hquadratic :
      0 ≤
        (1 - α) ^ (2 : ℕ) * inner ℝ (hessian φ x d) d -
          2 * (α * (1 - α) * inner ℝ (hessian φ x d) w) +
          α ^ (2 : ℕ) * inner ℝ (hessian φ x w) w := by
    -- Expand the positive Hessian square for `((1 - α) • d) - α • w`.
    simpa [ContinuousLinearMap.map_sub, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, hcross, sub_eq_add_neg, pow_two, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm] using hquad_nonneg
  -- Rearranging the completed-square inequality yields the desired absorption estimate.
  nlinarith

/-- Helper for Proposition 4.4.10: the initial objective-gap excess above the distance budget
collapses to the single full-trial Hessian pairing `-⟪H w, e⟫`. -/
private lemma modifiedNewton_initial_gap_excess_le_hessian_trialError_pairing
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0) :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
    φ x - φ xStar - distanceBudget ≤
      -inner ℝ (hessian φ x w) e := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
  have hgap :
      φ x - φ xStar ≤ inner ℝ (∇ φ x) e - distanceBudget := by
    -- Start from the strong-convexity tangent upper bound at the initial iterate.
    simpa [x, e, distanceBudget] using
      modifiedNewton_initial_gap_le_gradient_error_sub_distance_budget
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (method := method) (xStar := xStar)
  have hgrad_eq : hessian φ x d = ∇ φ x := by
    -- Expanding the Newton search direction recovers the frozen linearized gradient equation.
    change
      (fderiv ℝ (∇ φ) ↑(method.toMethod.x 0))
          ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x 0)).toContinuousLinearEquivOfDetNeZero
              (method.toMethod.x 0).property).symm)
            (∇ φ ↑(method.toMethod.x 0))) =
        ∇ φ ↑(method.toMethod.x 0)
    exact
      ContinuousLinearEquiv.apply_symm_apply
        ((fderiv ℝ (∇ φ) ↑(method.toMethod.x 0)).toContinuousLinearEquivOfDetNeZero
          (method.toMethod.x 0).property)
        (∇ φ ↑(method.toMethod.x 0))
  have hd_eq : d = e - w := by
    -- Keep the source decomposition `d = e - w` explicit before collapsing the gap excess.
    simpa [x, d, T, w, e] using
      modifiedNewtonInitialSearchDirection_eq_error_sub_fullTrialError
        (method := method) (xStar := xStar)
  have hUniv_nonempty : (interior (Set.univ : Set E)).Nonempty := by
    simp
  have hcont : ContinuousOn φ (Set.univ : Set E) := hφ_hessian.contDiff.continuous.continuousOn
  have hC2 : ContDiffOn ℝ 2 φ (interior (Set.univ : Set E)) := by
    simpa using hφ_hessian.contDiff.contDiffOn
  have hbound : σ • (1 : E →L[ℝ] E) ≤ hessian φ x := by
    -- Whole-space strong convexity supplies the Hessian Loewner lower bound at the initial point.
    have hiff :=
      (strongConvexOn_iff_hessian_lower_bound
        hσ convex_univ hUniv_nonempty hcont hC2).1 hφ_strong
    simpa [x] using hiff x (by simp)
  have hbudget_le :
      2 * distanceBudget ≤ inner ℝ (hessian φ x e) e := by
    -- Convert the distance budget to the Hessian quadratic form using strong convexity.
    have hquad :=
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hσ hC2 (by simp : x ∈ interior (Set.univ : Set E))).1 hbound e
    have hrewrite : 2 * distanceBudget = σ * ‖e‖ ^ (2 : ℕ) := by
      dsimp [distanceBudget]
      ring
    rw [hrewrite]
    exact hquad
  have hcollapse :
      inner ℝ (∇ φ x) e - inner ℝ (hessian φ x e) e =
        -inner ℝ (hessian φ x w) e := by
    -- Substitute `∇ φ x = H d` and `d = e - w` so only the full-trial error term survives.
    rw [← hgrad_eq, hd_eq, ContinuousLinearMap.map_sub]
    simp [inner_sub_left]
    ring
  calc
    φ x - φ xStar - distanceBudget ≤ inner ℝ (∇ φ x) e - 2 * distanceBudget := by
      linarith
    _ ≤ inner ℝ (∇ φ x) e - inner ℝ (hessian φ x e) e := by
      linarith
    _ = -inner ℝ (hessian φ x w) e := hcollapse

/-- Helper for Proposition 4.4.10: after splitting off the exact line-map distance budget, the
remaining initial surface is an explicit residual consisting of the initial gap excess above the
strong-convexity budget, the trial-error correction, and the direction-cubic remainder. -/
private lemma modifiedNewton_initial_coupled_surface_le_distance_budget_add_residual
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
    let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
    let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
    let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
    let residual : ℝ :=
      (1 - α) * (φ x - φ xStar - distanceBudget) +
        α * (1 - α) * inner ℝ (∇ φ x) w -
        (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic
    s * ((secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) - φ xStar) +
        α * (1 - α) * inner ℝ (∇ φ x) w -
        (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic) ≤
      s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic) + residual) := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
  let residual : ℝ :=
    (1 - α) * (φ x - φ xStar - distanceBudget) +
      α * (1 - α) * inner ℝ (∇ φ x) w -
      (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
      directionCubic
  have hline_budget :
      secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) - φ xStar ≤
        (1 - α) * (φ x - φ xStar) - α * (1 - α) * distanceBudget + segmentCubic := by
    -- First isolate the exact segment Taylor budget on the minimizer line.
    simpa [x, e, segmentCubic, distanceBudget] using
      modifiedNewton_initial_lineMap_model_le_segment_budget
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (method := method) (xStar := xStar) (α := α) hα
  have hsurface_split :
      (secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) - φ xStar) +
          α * (1 - α) * inner ℝ (∇ φ x) w -
          (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
          directionCubic ≤
        (((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic) + residual := by
    -- Route correction: keep the initial gap excess above the strong-convexity budget as an
    -- explicit residual instead of forcing the false generic pure-distance collapse.
    calc
      (secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) - φ xStar) +
          α * (1 - α) * inner ℝ (∇ φ x) w -
          (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
          directionCubic ≤
        (1 - α) * (φ x - φ xStar) -
            α * (1 - α) * distanceBudget +
            segmentCubic +
            α * (1 - α) * inner ℝ (∇ φ x) w -
            (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
            directionCubic := by
              linarith [hline_budget]
      _ = (((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic) + residual := by
            dsimp [residual]
            ring
  have hs_nonneg : 0 ≤ s := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsurface_split hs_nonneg
  -- Scale the distance-budget part and the explicit residual by the fixed normalization factor.
  simpa [x, d, T, w, e, s, segmentCubic, directionCubic, distanceBudget, residual, mul_assoc,
    mul_left_comm, mul_comm] using hmul

/-- Helper for Proposition 4.4.10: after the exact gap-excess collapse, the explicit residual
reduces to one Hessian remainder surface involving only the full-trial error `w`. -/
private lemma modifiedNewton_initial_residual_le_remainder_surface
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ} :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
    let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
    let residual : ℝ :=
      (1 - α) * (φ x - φ xStar - distanceBudget) +
        α * (1 - α) * inner ℝ (∇ φ x) w -
        (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic
    residual ≤
      -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
        (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  let residual : ℝ :=
    (1 - α) * (φ x - φ xStar - distanceBudget) +
      α * (1 - α) * inner ℝ (∇ φ x) w -
      (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
      directionCubic
  have hgap_surface :
      φ x - φ xStar - distanceBudget ≤
        -inner ℝ (hessian φ x w) e := by
    -- Collapse the initial gap excess to the single full-trial Hessian pairing.
    simpa [x, d, T, w, e, distanceBudget] using
      modifiedNewton_initial_gap_excess_le_hessian_trialError_pairing
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (method := method) (xStar := xStar)
  have hgrad_eq : hessian φ x d = ∇ φ x := by
    -- Expanding the Newton search direction recovers the frozen linearized gradient equation.
    change
      (fderiv ℝ (∇ φ) ↑(method.toMethod.x 0))
          ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x 0)).toContinuousLinearEquivOfDetNeZero
              (method.toMethod.x 0).property).symm)
            (∇ φ ↑(method.toMethod.x 0))) =
        ∇ φ ↑(method.toMethod.x 0)
    exact
      ContinuousLinearEquiv.apply_symm_apply
        ((fderiv ℝ (∇ φ) ↑(method.toMethod.x 0)).toContinuousLinearEquivOfDetNeZero
          (method.toMethod.x 0).property)
        (∇ φ ↑(method.toMethod.x 0))
  have hd_eq : d = e - w := by
    -- Keep the source decomposition `d = e - w` explicit before rewriting the trial correction.
    simpa [x, d, T, w, e] using
      modifiedNewtonInitialSearchDirection_eq_error_sub_fullTrialError
        (method := method) (xStar := xStar)
  have hselfAdjoint : IsSelfAdjoint (hessian φ x) := by
    -- A `C²` objective has self-adjoint Hessian at the initial iterate.
    simpa [x] using
      (fderiv_gradient_isSymmetric_of_contDiffAt (f := φ) (x := x)
        (hf := hφ_hessian.contDiff.contDiffAt (x := x))).isSelfAdjoint
  have hgrad_pair :
      inner ℝ (∇ φ x) w =
        inner ℝ (hessian φ x w) e - inner ℝ (hessian φ x w) w := by
    -- Substitute `∇ φ x = H d` and `d = e - w`, then use symmetry to move `H` onto `w`.
    calc
      inner ℝ (∇ φ x) w = inner ℝ (hessian φ x d) w := by rw [← hgrad_eq]
      _ = inner ℝ (hessian φ x (e - w)) w := by rw [hd_eq]
      _ = inner ℝ (hessian φ x e) w - inner ℝ (hessian φ x w) w := by
            simp [ContinuousLinearMap.map_sub, inner_sub_left]
      _ = inner ℝ (hessian φ x w) e - inner ℝ (hessian φ x w) w := by
            rw [show inner ℝ (hessian φ x e) w = inner ℝ (hessian φ x w) e by
                  calc
                    inner ℝ (hessian φ x e) w = inner ℝ w (hessian φ x e) := by
                      rw [real_inner_comm]
                    _ = inner ℝ (hessian φ x w) e := (hselfAdjoint.isSymmetric w e).symm]
  calc
    residual ≤
        (1 - α) * (-inner ℝ (hessian φ x w) e) +
          α * (1 - α) * inner ℝ (∇ φ x) w -
          (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
          directionCubic := by
            dsimp [residual]
            linarith
    _ =
        -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
          (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
          directionCubic := by
            rw [hgrad_pair]
            ring

/-- Helper for Proposition 4.4.10: after isolating the distance-budget contribution, the initial
shifted accepted-step gap is exactly a sum of the budget surface and the scaled exact remainder
surface. -/
private lemma modifiedNewtonInitialAcceptedGap_le_budgetSurface_add_exactRemainder
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
    let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
    let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
    let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
      s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic)) +
        s * (-((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
            (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
            directionCubic) := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
  let residual : ℝ :=
    (1 - α) * (φ x - φ xStar - distanceBudget) +
      α * (1 - α) * inner ℝ (∇ φ x) w -
      (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
      directionCubic
  let exactRemainder : ℝ :=
    -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
      (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
      directionCubic
  have hsurface_split :
      modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
        s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic) + residual) := by
    -- First separate the honest distance-budget surface from the exact residual.
    have hline_surface :
        modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
          s * ((secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) - φ xStar) +
              α * (1 - α) * inner ℝ (∇ φ x) w -
              (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
              directionCubic) := by
      simpa [x, d, T, w, s, directionCubic] using
        modifiedNewtonInitialAcceptedGap_le_lineMap_trialCorrection_surface
          (hσ := hσ) (hφ_hessian := hφ_hessian) (method := method) (xStar := xStar) (α := α) hα
    have hbudget_plus_residual :
        s * ((secondOrderTaylorModelAt φ x (AffineMap.lineMap x xStar α) - φ xStar) +
            α * (1 - α) * inner ℝ (∇ φ x) w -
            (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
            directionCubic) ≤
          s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic) + residual) := by
      simpa [x, d, T, w, e, s, segmentCubic, directionCubic, distanceBudget, residual] using
        modifiedNewton_initial_coupled_surface_le_distance_budget_add_residual
          (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
          (method := method) (xStar := xStar) (α := α) hα
    exact hline_surface.trans hbudget_plus_residual
  have hexact_surface :
      residual ≤ exactRemainder := by
    -- Then collapse the residual to the exact Hessian remainder surface from the source route.
    simpa [x, d, T, w, e, distanceBudget, directionCubic, residual, exactRemainder] using
      modifiedNewton_initial_residual_le_remainder_surface
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (method := method) (xStar := xStar) (α := α)
  have hs_nonneg : 0 ≤ s := by
    positivity
  have hscaled_exact :
      s * residual ≤ s * exactRemainder := by
    -- Scale the exact remainder inequality by the fixed normalization factor.
    exact mul_le_mul_of_nonneg_left hexact_surface hs_nonneg
  calc
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
        s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic) + residual) :=
          hsurface_split
    _ = s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic)) + s * residual := by
          ring
    _ ≤ s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic)) + s * exactRemainder := by
          exact add_le_add_left hscaled_exact _
    _ = s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic)) +
          s * (-((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
              (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
              directionCubic) := by
          rfl

/-- Helper for Proposition 4.4.10: after specializing the exact remainder surface at
`α = (3 / 4) / sqrt ξ`, only the final vector-to-scalar quartic estimate remains. -/
private lemma modifiedNewton_initial_specialized_remainder_surface_normal_form
    {φ : E → ℝ} {L : NNReal} {x0 xStar : E}
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ} :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
    -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
        (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic =
      -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) d -
        (1 - α + α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  have hd_eq : d = e - w := by
    -- Keep the source decomposition `d = e - w` explicit before scalarizing the mixed pairings.
    simpa [x, d, T, w, e] using
      modifiedNewtonInitialSearchDirection_eq_error_sub_fullTrialError
        (method := method) (xStar := xStar)
  have he_eq : e = d + w := by
    -- Rewrite the initial error as the Newton direction plus the full-trial error.
    calc
      e = (e - w) + w := by abel
      _ = d + w := by rw [← hd_eq]
  -- Route correction: expose the remainder surface in the `d`/`w` coordinates before any norm
  -- estimates, so the analytic blocker is isolated to bounding one mixed pairing and one
  -- positive quadratic term.
  rw [he_eq]
  simp [inner_add_right]
  ring

/-- Helper for Proposition 4.4.10: the specialized exact remainder surface can be rewritten in the
absorption-aligned `e`/`d` form that matches the weighted trial-error inequality. -/
private lemma modifiedNewton_initial_specialized_remainder_surface_absorption_form
    {φ : E → ℝ} {L : NNReal} {x0 xStar : E}
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ} :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
    -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
        (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic =
      -(1 - α) * inner ℝ (hessian φ x w) e +
        α * (1 - α) * inner ℝ (hessian φ x d) w -
        (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  have hselfAdjoint : IsSelfAdjoint (hessian φ x) := by
    -- A `C²` objective has self-adjoint Hessian at the initial iterate.
    simpa [x] using
      (fderiv_gradient_isSymmetric_of_contDiffAt (f := φ) (x := x)
        (hf := hφ_hessian.contDiff.contDiffAt (x := x))).isSelfAdjoint
  have hd_eq : d = e - w := by
    -- Keep the source decomposition `d = e - w` explicit before rewriting the mixed pairing.
    simpa [x, d, T, w, e] using
      modifiedNewtonInitialSearchDirection_eq_error_sub_fullTrialError
        (method := method) (xStar := xStar)
  have he_eq : e = d + w := by
    -- Rewrite the initial error as the Newton direction plus the full-trial error.
    calc
      e = (e - w) + w := by abel
      _ = d + w := by rw [← hd_eq]
  have hcross :
      inner ℝ (hessian φ x d) w = inner ℝ (hessian φ x w) d := by
    -- Self-adjointness identifies the two mixed Hessian spellings used by the absorption step.
    calc
      inner ℝ (hessian φ x d) w = inner ℝ w (hessian φ x d) := by rw [real_inner_comm]
      _ = inner ℝ (hessian φ x w) d := (hselfAdjoint.isSymmetric w d).symm
  -- Route correction: rewrite the exact remainder in the mixed-term package consumed by the
  -- weighted trial-absorption lemma instead of the raw `d`/`w` normal form.
  rw [he_eq]
  simp [inner_add_right, hcross]
  ring

/-- Helper for Proposition 4.4.10: after rewriting the exact remainder in the absorption-aligned
form, the mixed Hessian term is absorbed into the initial gap excess, the Newton energy, and the
direction-cubic remainder. -/
private lemma modifiedNewton_initial_specialized_remainder_surface_le_gapEnergyCubic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
    -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
        (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic ≤
      (1 - α) * (φ x - φ xStar - ((σ / 2) * ‖e‖ ^ (2 : ℕ))) +
        ((1 - α) ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x d) d +
        directionCubic := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  have hsurface_eq :
      -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
          (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
          directionCubic =
        -(1 - α) * inner ℝ (hessian φ x w) e +
          α * (1 - α) * inner ℝ (hessian φ x d) w -
          (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
          directionCubic := by
    -- First rewrite the exact remainder in the mixed-term package handled by absorption.
    simpa [x, d, T, w, e, directionCubic] using
      modifiedNewton_initial_specialized_remainder_surface_absorption_form
        (hφ_hessian := hφ_hessian) (method := method) (xStar := xStar) (α := α)
  have hgap :
      φ x - φ xStar - ((σ / 2) * ‖e‖ ^ (2 : ℕ)) ≤
        -inner ℝ (hessian φ x w) e := by
    -- Collapse the initial gap excess to the single full-trial Hessian pairing.
    simpa [x, d, T, w, e] using
      modifiedNewton_initial_gap_excess_le_hessian_trialError_pairing
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (method := method) (xStar := xStar)
  have hone_sub_nonneg : 0 ≤ 1 - α := by
    nlinarith [hα.1, hα.2]
  have hscaled_gap :
      (1 - α) * (φ x - φ xStar - ((σ / 2) * ‖e‖ ^ (2 : ℕ))) ≤
        -(1 - α) * inner ℝ (hessian φ x w) e := by
    -- Scale the gap-excess inequality by the nonnegative weight `1 - α`.
    exact mul_le_mul_of_nonneg_left hgap hone_sub_nonneg
  have habsorb :
      α * (1 - α) * inner ℝ (hessian φ x d) w -
          (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w ≤
        ((1 - α) ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x d) d := by
    -- Absorb the mixed trial-error term into the weighted Newton energy.
    simpa [x, d, T, w] using
      modifiedNewton_initial_weighted_trial_absorption
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (method := method) (xStar := xStar) (α := α)
  calc
    -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
        (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic =
      -(1 - α) * inner ℝ (hessian φ x w) e +
        α * (1 - α) * inner ℝ (hessian φ x d) w -
        (α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
        directionCubic := hsurface_eq
    _ ≤
      (1 - α) * (φ x - φ xStar - ((σ / 2) * ‖e‖ ^ (2 : ℕ))) +
        ((1 - α) ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x d) d +
        directionCubic := by
          linarith

/-- Helper for Proposition 4.4.10: strong convexity at the initial iterate lower-bounds the
full-trial quadratic form of `w = T - x*` by `σ ‖w‖²`. -/
private lemma modifiedNewton_initial_trial_error_quadratic_ge_sigma
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0) :
    let x := method 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    σ * ‖w‖ ^ (2 : ℕ) ≤ inner ℝ (hessian φ x w) w := by
  let x := method 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let hφ_C2 : ContDiff ℝ 2 φ := hφ_hessian.contDiff
  have hUniv_nonempty : (interior (Set.univ : Set E)).Nonempty := by
    simp
  have hcont : ContinuousOn φ (Set.univ : Set E) := hφ_C2.continuous.continuousOn
  have hC2 : ContDiffOn ℝ 2 φ (interior (Set.univ : Set E)) := by
    simpa using hφ_C2.contDiffOn
  have hbound : σ • (1 : E →L[ℝ] E) ≤ hessian φ x := by
    -- Whole-space strong convexity supplies the Hessian Loewner lower bound at the initial point.
    have hiff :=
      (strongConvexOn_iff_hessian_lower_bound
        hσ convex_univ hUniv_nonempty hcont hC2).1 hφ_strong
    simpa [x] using hiff x (by simp)
  -- Convert the Loewner lower bound into the quadratic-form inequality at the trial error `w`.
  exact
    (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
      hσ hC2 (by simp : x ∈ interior (Set.univ : Set E))).1 hbound w

/-- Helper for Proposition 4.4.10: at `k = 0`, the Hessian applied to the full-trial error is
exactly the gradient linearization defect, so Hessian Lipschitzness bounds its norm by
`(L / 2) * ‖x₀ - x*‖²`. -/
private lemma modifiedNewton_initial_trial_error_hessian_image_norm_le_half_L_sqDistance
    {φ : E → ℝ} {L : NNReal} {x0 xStar : E}
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0) :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    ‖hessian φ x w‖ ≤ ((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ) := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  have hgrad0 : ∇ φ xStar = 0 := by
    -- A differentiable global minimizer is stationary, so the minimizer endpoint contributes no
    -- gradient term in the linearization defect.
    exact isMinOn_gradient_eq_zero hxStar
  have hgrad_eq : hessian φ x d = ∇ φ x := by
    -- Expanding the Newton search direction recovers the frozen linearized gradient equation.
    change
      (fderiv ℝ (∇ φ) ↑(method.toMethod.x 0))
          ((((fderiv ℝ (∇ φ) ↑(method.toMethod.x 0)).toContinuousLinearEquivOfDetNeZero
              (method.toMethod.x 0).property).symm)
            (∇ φ ↑(method.toMethod.x 0))) =
        ∇ φ ↑(method.toMethod.x 0)
    exact
      ContinuousLinearEquiv.apply_symm_apply
        ((fderiv ℝ (∇ φ) ↑(method.toMethod.x 0)).toContinuousLinearEquivOfDetNeZero
          (method.toMethod.x 0).property)
        (∇ φ ↑(method.toMethod.x 0))
  have hd_eq : d = e - w := by
    -- Keep the source decomposition `d = e - w` explicit before isolating the trial error `w`.
    simpa [x, d, T, w, e] using
      modifiedNewtonInitialSearchDirection_eq_error_sub_fullTrialError
        (method := method) (xStar := xStar)
  have hw_eq : w = e - d := by
    -- Rearranging the same source identity makes the gradient-deviation defect match `H w`.
    rw [hd_eq]
    abel
  have hrewrite :
      hessian φ x w = hessian φ x e - ∇ φ x := by
    -- Rewrite the exact full-trial error image into the Hessian-Lipschitz gradient defect.
    calc
      hessian φ x w = hessian φ x (e - d) := by rw [hw_eq]
      _ = hessian φ x e - hessian φ x d := by
            simp [ContinuousLinearMap.map_sub]
      _ = hessian φ x e - ∇ φ x := by rw [hgrad_eq]
  have hdeviation :
      ‖hessian φ x e - ∇ φ x‖ ≤ ((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ) := by
    -- The minimizer-endpoint gradient deviation estimate is already the needed `e`-quadratic
    -- bound once `∇ φ x* = 0` is substituted.
    simpa [x, e, hgrad0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (HasLipschitzContinuousHessian.gradient_deviation_le hφ_hessian x xStar)
  -- Consume the exact rewrite first, then the standard Hessian-Lipschitz defect bound.
  calc
    ‖hessian φ x w‖ = ‖hessian φ x e - ∇ φ x‖ := by rw [hrewrite]
    _ ≤ ((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ) := hdeviation

/-- Helper for Proposition 4.4.10: at `k = 0`, the full-trial error `w` and the accepted search
direction `d` satisfy the specialized characteristic-quantity bounds used in the quartic budget
step. -/
private lemma modifiedNewton_initial_specialized_trial_error_direction_bounds
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0) :
    let ξ : ℝ := modifiedNewtonCharacteristicQuantity σ L x0 xStar
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    ‖w‖ ≤ (ξ / 2) * ‖e‖ ∧ ‖d‖ ≤ (1 + ξ / 2) * ‖e‖ := by
  let ξ : ℝ := modifiedNewtonCharacteristicQuantity σ L x0 xStar
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  have hw_trial :
      ‖d - e‖ ≤ (ξ / 2) * ‖e‖ := by
    -- Specialize the generic search-direction minus error bound to the initial index.
    simpa [ξ, d, e] using
      modifiedNewtonSearchDirectionSubError_le_halfCharacteristic_mulError
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (hxStar := hxStar) (method := method) (xStar := xStar) (k := 0)
  have hw_eq : d - e = -w := by
    -- At `k = 0`, the search-direction error is exactly the negative full-trial error.
    simpa [d, T, w, e] using
      modifiedNewtonSearchDirectionSubError_eq_neg_fullTrialError
        (method := method) (xStar := xStar) (k := 0)
  have hw :
      ‖w‖ ≤ (ξ / 2) * ‖e‖ := by
    -- Convert the specialized `‖d - e‖` bound to the full-trial error notation `w`.
    calc
      ‖w‖ = ‖d - e‖ := by
            rw [hw_eq]
            simp
      _ ≤ (ξ / 2) * ‖e‖ := hw_trial
  have hd :
      ‖d‖ ≤ (1 + ξ / 2) * ‖e‖ := by
    -- Specialize the generic Newton-direction norm bound to the initial index.
    simpa [ξ, d, e] using
      modifiedNewtonSearchDirectionNorm_le_one_add_halfCharacteristic_mulError
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (hxStar := hxStar) (method := method) (xStar := xStar) (k := 0)
  -- Package the two initial-index norm bounds once so the final quartic bridge stays flat.
  exact ⟨hw, hd⟩

/-- Helper for Proposition 4.4.10: once the budget parameter is specialized to
`α = (3 / 4) / γ`, the remaining scalar quartic budget closes on the regime `γ ≥ 1`. -/
private lemma modifiedNewton_initial_specialized_gamma_poly_le_quartic_margin
    {γ : ℝ}
    (hγ : 1 ≤ γ) :
    ((((1 - (3 / 4 : ℝ) / γ) ^ (2 : ℕ)) +
          (1 / 3 : ℝ) * ((3 / 4 : ℝ) / γ) ^ (3 : ℕ) * γ ^ (2 : ℕ)) *
        γ ^ (4 : ℕ)) ≤
      ((21 / 20 : ℝ) * γ) ^ (4 : ℕ) := by
  have hγ_pos : 0 < γ := by
    -- The source regime keeps the normalized square-root variable away from zero.
    linarith
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  -- Clear the reciprocal denominators and reduce the quartic comparison to a polynomial
  -- inequality on the half-line `γ ≥ 1`.
  field_simp [hγ_ne]
  nlinarith

/-- Helper for Proposition 4.4.10: before the final quartic scalar normalization, the exact
initial remainder surface is bounded by the Hessian-image norm envelope together with the exact
negative trial-error curvature term. -/
private lemma modifiedNewton_initial_specialized_remainder_surface_le_normCurvatureEnvelope
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
    let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
    s * (-((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
          (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
          directionCubic) ≤
      s * (((1 - α) ^ (2 : ℕ)) * ((((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ)) * ‖e‖) -
          (α - α ^ (2 : ℕ) / 2) * (σ * ‖w‖ ^ (2 : ℕ)) +
          directionCubic) := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  have hcross_raw :
      -inner ℝ (hessian φ x w) e ≤ ‖hessian φ x w‖ * ‖e‖ := by
    -- Bound the mixed Hessian pairing by Cauchy-Schwarz before using the initial Hessian-image
    -- control on the full-trial error.
    have hnorm_inner :
        |inner ℝ (hessian φ x w) e| ≤ ‖hessian φ x w‖ * ‖e‖ := by
      simpa [Real.norm_eq_abs] using norm_inner_le_norm (hessian φ x w) e
    nlinarith
  have htrial_image :
      ‖hessian φ x w‖ ≤ ((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ) := by
    -- The initial full-trial error is exactly the Hessian-Lipschitz gradient defect at `x₀`.
    simpa [x, d, T, w, e] using
      modifiedNewton_initial_trial_error_hessian_image_norm_le_half_L_sqDistance
        (hφ_hessian := hφ_hessian) (hxStar := hxStar) (method := method) (xStar := xStar)
  have htrial_curvature :
      σ * ‖w‖ ^ (2 : ℕ) ≤ inner ℝ (hessian φ x w) w := by
    -- Strong convexity keeps the exact negative trial-error curvature term available in the
    -- envelope instead of discarding it.
    simpa [x, T, w] using
      modifiedNewton_initial_trial_error_quadratic_ge_sigma
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (method := method) (xStar := xStar)
  have hone_sq_nonneg : 0 ≤ (1 - α) ^ (2 : ℕ) := by
    positivity
  have hcurv_coeff_nonneg : 0 ≤ α - α ^ (2 : ℕ) / 2 := by
    nlinarith [hα.1, hα.2]
  have hcross_term :
      -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e ≤
        ((1 - α) ^ (2 : ℕ)) * ((((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ)) * ‖e‖) := by
    have hcross_norm :
        ‖hessian φ x w‖ * ‖e‖ ≤ (((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ)) * ‖e‖ := by
      exact mul_le_mul_of_nonneg_right htrial_image (norm_nonneg e)
    exact mul_le_mul_of_nonneg_left (hcross_raw.trans hcross_norm) hone_sq_nonneg
  have htrial_term :
      -(α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w ≤
        -(α - α ^ (2 : ℕ) / 2) * (σ * ‖w‖ ^ (2 : ℕ)) := by
    -- Keep the negative curvature contribution exact while replacing `⟪H w, w⟫` by its strong
    -- convexity lower bound.
    nlinarith
  have hs_nonneg : 0 ≤ s := by
    positivity
  have hshell :
      -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
          (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
          directionCubic ≤
        ((1 - α) ^ (2 : ℕ)) * ((((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ)) * ‖e‖) -
          (α - α ^ (2 : ℕ) / 2) * (σ * ‖w‖ ^ (2 : ℕ)) +
          directionCubic := by
    -- Only the mixed Hessian pairing is bounded absolutely; the negative trial-error curvature is
    -- retained exactly so the final scalar closure can still exploit its cancellation.
    linarith
  exact mul_le_mul_of_nonneg_left hshell hs_nonneg

/-- Helper for Proposition 4.4.10: under the source regime `1 ≤ ξ`, the chosen initial-budget
parameter `α = (3 / 4) / sqrt ξ` is admissible for the repaired one-step local model. -/
private lemma modifiedNewtonInitialBudgetParameter_mem_Icc
    {ξ : ℝ}
    (hξ : 1 ≤ ξ) :
    ((3 / 4 : ℝ) / Real.sqrt ξ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hξ_nonneg : 0 ≤ ξ := le_trans (by norm_num) hξ
  have hsqrt_ge_one : 1 ≤ Real.sqrt ξ := by
    have hsq : (1 : ℝ) ^ (2 : ℕ) ≤ (Real.sqrt ξ) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt hξ_nonneg]
      nlinarith
    exact (sq_le_sq₀ (by positivity : 0 ≤ (1 : ℝ)) (Real.sqrt_nonneg ξ)).1 hsq
  have hsqrt_pos : 0 < Real.sqrt ξ := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1) hsqrt_ge_one
  constructor
  · -- The chosen parameter is nonnegative because `sqrt ξ` stays positive in the source regime.
    positivity
  · -- The same source regime keeps the reciprocal factor below the admissible upper bound `1`.
    exact (div_le_iff₀ hsqrt_pos).2 <| by
      nlinarith [hsqrt_ge_one]

/-- Helper for Proposition 4.4.10: after specializing the line-map / trial-correction surface at
`α = (3 / 4) / sqrt ξ`, the proved prefix reduces the initial shifted gap to the pure budget
surface plus the remaining norm/curvature shell. -/
private lemma modifiedNewtonInitialLineMapTrialSurface_le_budgetSurface_add_normCurvatureShell
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar) :
    let ξ : ℝ := modifiedNewtonCharacteristicQuantity σ L x0 xStar
    let γ : ℝ := Real.sqrt ξ
    let α : ℝ := (3 / 4 : ℝ) / γ
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
    let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
    let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
    let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
      s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic)) +
        s * (((1 - α) ^ (2 : ℕ)) * ((((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ)) * ‖e‖) -
            (α - α ^ (2 : ℕ) / 2) * (σ * ‖w‖ ^ (2 : ℕ)) +
            directionCubic) := by
  let ξ : ℝ := modifiedNewtonCharacteristicQuantity σ L x0 xStar
  let γ : ℝ := Real.sqrt ξ
  let α : ℝ := (3 / 4 : ℝ) / γ
  have hα : α ∈ Set.Icc (0 : ℝ) 1 := by
    -- Reuse the specialized admissibility proof for the fixed source parameter.
    simpa [ξ, α] using modifiedNewtonInitialBudgetParameter_mem_Icc hxi
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
  let exactRemainder : ℝ :=
    -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
      (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
      directionCubic
  let shell : ℝ :=
    ((1 - α) ^ (2 : ℕ)) * ((((L : ℝ) / 2) * ‖e‖ ^ (2 : ℕ)) * ‖e‖) -
      (α - α ^ (2 : ℕ) / 2) * (σ * ‖w‖ ^ (2 : ℕ)) +
      directionCubic
  have hbudget_plus_exact :
      modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
        s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic)) +
          s * exactRemainder := by
    -- First expose the exact budget surface plus the specialized exact remainder.
    simpa [x, d, T, w, e, s, segmentCubic, directionCubic, distanceBudget, exactRemainder] using
      modifiedNewtonInitialAcceptedGap_le_budgetSurface_add_exactRemainder
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (method := method) (xStar := xStar) (α := α) hα
  have hremainder_shell :
      s * exactRemainder ≤ s * shell := by
    -- Then replace the exact remainder by the remaining norm / curvature shell.
    simpa [x, d, T, w, e, s, directionCubic, exactRemainder, shell] using
      modifiedNewton_initial_specialized_remainder_surface_le_normCurvatureEnvelope
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (hxStar := hxStar) (method := method) (xStar := xStar) (α := α) hα
  calc
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
        s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic)) +
          s * exactRemainder := hbudget_plus_exact
    _ ≤ s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic)) + s * shell := by
          exact add_le_add_left hremainder_shell _

/-- Helper for Proposition 4.4.10: combining the exact budget split with strong convexity on the
initial error rewrites the remaining initial surface as a signed Newton-energy term, a signed
full-trial curvature term, and the two cubic remainders. -/
private lemma modifiedNewtonInitialAcceptedGap_le_segmentBudget_add_signedEnergy
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let curv : ℝ := inner ℝ (hessian φ x d) d
    let trialCurv : ℝ := inner ℝ (hessian φ x w) w
    let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
    let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
    let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
      s * ((((1 - α) ^ (2 : ℕ) / 2) * curv) - (1 / 2 : ℝ) * trialCurv +
        segmentCubic + directionCubic) := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let curv : ℝ := inner ℝ (hessian φ x d) d
  let trialCurv : ℝ := inner ℝ (hessian φ x w) w
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  let distanceBudget : ℝ := ((σ / 2) * ‖e‖ ^ (2 : ℕ))
  let exactRemainder : ℝ :=
    -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) e -
      (α - α ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x w) w +
      directionCubic
  have hbudget_plus_exact :
      modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
        s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic)) +
          s * exactRemainder := by
    -- First keep the exact budget split so the later cancellation happens before any norm loss.
    simpa [x, d, T, w, e, s, segmentCubic, directionCubic, distanceBudget, exactRemainder] using
      modifiedNewtonInitialAcceptedGap_le_budgetSurface_add_exactRemainder
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (method := method) (xStar := xStar) (α := α) hα
  have hφ_C2 : ContDiff ℝ 2 φ := hφ_hessian.contDiff
  have hUniv_nonempty : (interior (Set.univ : Set E)).Nonempty := by
    simp
  have hcont : ContinuousOn φ (Set.univ : Set E) := hφ_C2.continuous.continuousOn
  have hC2 : ContDiffOn ℝ 2 φ (interior (Set.univ : Set E)) := by
    simpa using hφ_C2.contDiffOn
  have hbound : σ • (1 : E →L[ℝ] E) ≤ hessian φ x := by
    -- Whole-space strong convexity supplies the Hessian Loewner lower bound at the initial point.
    have hiff :=
      (strongConvexOn_iff_hessian_lower_bound
        hσ convex_univ hUniv_nonempty hcont hC2).1 hφ_strong
    simpa [x] using hiff x (by simp)
  have hdistance_le :
      ((1 - α) ^ (2 : ℕ)) * distanceBudget ≤
        ((1 - α) ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x e) e := by
    have hquad :=
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hσ hC2 (by simp : x ∈ interior (Set.univ : Set E))).1 hbound e
    have hrewrite : 2 * distanceBudget = σ * ‖e‖ ^ (2 : ℕ) := by
      dsimp [distanceBudget]
      ring
    have hbudget_le :
        2 * distanceBudget ≤ inner ℝ (hessian φ x e) e := by
      rw [hrewrite]
      exact hquad
    have hone_sq_nonneg : 0 ≤ (1 - α) ^ (2 : ℕ) := by
      positivity
    nlinarith
  have hselfAdjoint : IsSelfAdjoint (hessian φ x) := by
    -- The Hessian is self-adjoint because the objective is `C²`.
    simpa [x] using
      (fderiv_gradient_isSymmetric_of_contDiffAt (f := φ) (x := x)
        (hf := hφ_C2.contDiffAt (x := x))).isSelfAdjoint
  have hd_eq : d = e - w := by
    -- Keep the source decomposition `d = e - w` explicit before expanding the quadratic form.
    simpa [x, d, T, w, e] using
      modifiedNewtonInitialSearchDirection_eq_error_sub_fullTrialError
        (method := method) (xStar := xStar)
  have he_eq : e = d + w := by
    -- Rewrite the initial error as the Newton direction plus the full-trial error.
    calc
      e = (e - w) + w := by abel
      _ = d + w := by rw [← hd_eq]
  have hcross :
      inner ℝ (hessian φ x w) d = inner ℝ (hessian φ x d) w := by
    -- Self-adjointness identifies the mixed Hessian terms in the `e = d + w` expansion.
    calc
      inner ℝ (hessian φ x w) d = inner ℝ d (hessian φ x w) := by rw [real_inner_comm]
      _ = inner ℝ (hessian φ x d) w := (hselfAdjoint.isSymmetric d w).symm
  have hhee_expand :
      inner ℝ (hessian φ x e) e = curv + 2 * inner ℝ (hessian φ x w) d + trialCurv := by
    -- Expand the initial-error quadratic form in the `d` / `w` coordinates.
    rw [he_eq]
    simp [curv, trialCurv, ContinuousLinearMap.map_add, inner_add_left, inner_add_right, hcross]
    ring
  have hexact_normal :
      exactRemainder =
        -((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) d -
          (1 - α + α ^ (2 : ℕ) / 2) * trialCurv +
          directionCubic := by
    -- Route correction: use the exact `d` / `w` normal form, not the older absolute shell.
    simpa [x, d, T, w, e, trialCurv, directionCubic] using
      modifiedNewton_initial_specialized_remainder_surface_normal_form
        (L := L) (method := method) (xStar := xStar) (α := α)
  have hs_nonneg : 0 ≤ s := by
    positivity
  have hsurface_unscaled :
      (((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic) + exactRemainder ≤
        (((1 - α) ^ (2 : ℕ) / 2) * curv) - (1 / 2 : ℝ) * trialCurv +
          segmentCubic + directionCubic := by
    -- Replace the distance budget by the Hessian quadratic form, then cancel the mixed terms
    -- against the exact remainder before the final scalar closure.
    calc
      (((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic) + exactRemainder ≤
          (((1 - α) ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x e) e + segmentCubic) +
            exactRemainder := by
              linarith [hdistance_le]
      _ = (((1 - α) ^ (2 : ℕ) / 2) * curv) - (1 / 2 : ℝ) * trialCurv +
            segmentCubic + directionCubic := by
              rw [hhee_expand, hexact_normal]
              ring
  have hscaled_surface :
      s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic) + exactRemainder) ≤
        s * ((((1 - α) ^ (2 : ℕ) / 2) * curv) - (1 / 2 : ℝ) * trialCurv +
          segmentCubic + directionCubic) := by
    -- Multiply the exact signed-energy surface by the fixed normalization scale.
    exact mul_le_mul_of_nonneg_left hsurface_unscaled hs_nonneg
  calc
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
        s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic)) +
          s * exactRemainder := hbudget_plus_exact
    _ = s * ((((1 - α) ^ (2 : ℕ)) * distanceBudget + segmentCubic) + exactRemainder) := by
          ring
    _ ≤ s * ((((1 - α) ^ (2 : ℕ) / 2) * curv) - (1 / 2 : ℝ) * trialCurv +
          segmentCubic + directionCubic) := hscaled_surface

/-- Helper for Proposition 4.4.10: the signed Newton-energy surface can be frozen as the initial
error quadratic form together with the exact `d`/`w` remainder normal form. -/
private lemma modifiedNewtonInitialSignedEnergySurface_eq_initialQuadratic_add_exactRemainder
    {φ : E → ℝ} {L : NNReal} {x0 xStar : E}
    (hφ_hessian : φ ∈ C22[L])
    (method : ModifiedNewtonMethod φ x0)
    {α : ℝ} :
    let x := method 0
    let d := method.toMethod.searchDirection 0
    let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
    let w : E := T - xStar
    let e : E := x0 - xStar
    let curv : ℝ := inner ℝ (hessian φ x d) d
    let trialCurv : ℝ := inner ℝ (hessian φ x w) w
    let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
    let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
    (((1 - α) ^ (2 : ℕ) / 2) * curv) - (1 / 2 : ℝ) * trialCurv + segmentCubic + directionCubic =
      (((1 - α) ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x e) e) + segmentCubic +
        (-((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) d -
          (1 - α + α ^ (2 : ℕ) / 2) * trialCurv + directionCubic) := by
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let curv : ℝ := inner ℝ (hessian φ x d) d
  let trialCurv : ℝ := inner ℝ (hessian φ x w) w
  let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  have hselfAdjoint : IsSelfAdjoint (hessian φ x) := by
    -- A `C²` objective has self-adjoint Hessian at the initial iterate.
    simpa [x] using
      (fderiv_gradient_isSymmetric_of_contDiffAt (f := φ) (x := x)
        (hf := hφ_hessian.contDiff.contDiffAt (x := x))).isSelfAdjoint
  have hd_eq : d = e - w := by
    -- Keep the source decomposition `d = e - w` explicit before expanding the initial quadratic
    -- form.
    simpa [x, d, T, w, e] using
      modifiedNewtonInitialSearchDirection_eq_error_sub_fullTrialError
        (method := method) (xStar := xStar)
  have he_eq : e = d + w := by
    -- Rewrite the initial error as the Newton direction plus the full-trial error.
    calc
      e = (e - w) + w := by abel
      _ = d + w := by rw [← hd_eq]
  have hcross :
      inner ℝ (hessian φ x w) d = inner ℝ (hessian φ x d) w := by
    -- Self-adjointness identifies the mixed Hessian pairings in the `e = d + w` expansion.
    calc
      inner ℝ (hessian φ x w) d = inner ℝ d (hessian φ x w) := by rw [real_inner_comm]
      _ = inner ℝ (hessian φ x d) w := (hselfAdjoint.isSymmetric d w).symm
  have hhee_expand :
      inner ℝ (hessian φ x e) e = curv + 2 * inner ℝ (hessian φ x w) d + trialCurv := by
    -- Expand the initial-error quadratic form in the `d` / `w` coordinates.
    rw [he_eq]
    simp [curv, trialCurv, ContinuousLinearMap.map_add, inner_add_left, inner_add_right, hcross]
    ring
  -- Freeze the signed surface as one initial-error quadratic term plus the exact normal-form
  -- remainder that still couples `d` and the full-trial error `w`.
  rw [hhee_expand]
  ring

/-- Helper for Proposition 4.4.10: after the line-map / trial-correction pivot, the initial
shifted accepted-step gap should be closed directly on the line-map surface instead of the older
exact-remainder branch. -/
private lemma modifiedNewton_initial_specialized_lineMapSurface_le_budgetQuartic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar) :
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
      (((21 / 20 : ℝ) * Real.sqrt
          (modifiedNewtonCharacteristicQuantity σ L x0 xStar)) ^ (4 : ℕ)) := by
  let ξ : ℝ := modifiedNewtonCharacteristicQuantity σ L x0 xStar
  let γ : ℝ := Real.sqrt ξ
  let α : ℝ := (3 / 4 : ℝ) / γ
  have hα : α ∈ Set.Icc (0 : ℝ) 1 := by
    -- The source regime `ξ ≥ 1` makes the chosen budget parameter admissible.
    simpa [ξ, α] using modifiedNewtonInitialBudgetParameter_mem_Icc hxi
  let x := method 0
  let d := method.toMethod.searchDirection 0
  let T := NewtonSystem.step (∇ φ) (method.toMethod.x 0)
  let w : E := T - xStar
  let e : E := x0 - xStar
  let curv : ℝ := inner ℝ (hessian φ x d) d
  let trialCurv : ℝ := inner ℝ (hessian φ x w) w
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  let segmentCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖e‖ ^ (3 : ℕ)
  let directionCubic : ℝ := ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖d‖ ^ (3 : ℕ)
  -- Route correction: keep the exact signed Newton-energy surface on the public path, rather than
  -- returning to the older absolute shell that loses the cancellation needed for the quartic step.
  have hsigned_surface :
      modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
        s * ((((1 - α) ^ (2 : ℕ) / 2) * curv) - (1 / 2 : ℝ) * trialCurv +
          segmentCubic + directionCubic) := by
    -- Collapse the exact budget split before any scalar normalization, so the remaining blocker is
    -- the signed curvature surface itself.
    simpa [ξ, γ, α, x, d, T, w, e, curv, trialCurv, s, segmentCubic, directionCubic] using
      modifiedNewtonInitialAcceptedGap_le_segmentBudget_add_signedEnergy
        (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
        (method := method) (xStar := xStar) (α := α) hα
  have hξ_nonneg : 0 ≤ ξ := le_trans (by norm_num) hxi
  have hγ_ge_one : 1 ≤ γ := by
    -- The source regime `ξ ≥ 1` lifts directly to the square-root variable `γ`.
    have hsq : (1 : ℝ) ^ (2 : ℕ) ≤ γ ^ (2 : ℕ) := by
      simpa [γ, Real.sq_sqrt hξ_nonneg] using hxi
    exact (sq_le_sq₀ (by positivity : 0 ≤ (1 : ℝ)) (Real.sqrt_nonneg ξ)).1 hsq
  have hγ_pos : 0 < γ := by
    -- The same square-root variable stays strictly positive, so reciprocal normalization is legal.
    linarith
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hsigned_remainder_surface :
      modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
        s * ((((1 - α) ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x e) e) + segmentCubic +
          (-((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) d -
            (1 - α + α ^ (2 : ℕ) / 2) * trialCurv + directionCubic)) := by
    -- Freeze the live frontier as one initial-error quadratic term plus the exact `d` / `w`
    -- remainder normal form before any scalar normalization.
    calc
      modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
          s * ((((1 - α) ^ (2 : ℕ) / 2) * curv) - (1 / 2 : ℝ) * trialCurv +
            segmentCubic + directionCubic) := hsigned_surface
      _ =
          s * ((((1 - α) ^ (2 : ℕ) / 2) * inner ℝ (hessian φ x e) e) + segmentCubic +
            (-((1 - α) ^ (2 : ℕ)) * inner ℝ (hessian φ x w) d -
              (1 - α + α ^ (2 : ℕ) / 2) * trialCurv + directionCubic)) := by
            congr 1
            simpa [x, d, T, w, e, curv, trialCurv, segmentCubic, directionCubic] using
              modifiedNewtonInitialSignedEnergySurface_eq_initialQuadratic_add_exactRemainder
                (hφ_hessian := hφ_hessian) (method := method) (xStar := xStar) (α := α)
  -- TODO(Proposition 4.4.10): the remaining blocker is the scalar closure of the exact signed
  -- surface after rewriting it to
  -- `((1 - α)^2 / 2) * ⟪H e, e⟫ + segmentCubic - ((1 - α)^2) * ⟪H w, d⟫ -
  --   (1 - α + α^2 / 2) * trialCurv + directionCubic`.
  -- The current dependency-closed API still lacks the bridge that scalarizes this exact quadratic
  -- plus `d`/`w` remainder package at `α = (3 / 4) / sqrt ξ`; the discarded norm-shell route is
  -- too lossy, but the remaining positive `⟪H e, e⟫` term is also not directly upper-bounded by
  -- the existing helpers.
  sorry

/-- Helper for Proposition 4.4.10: once the coupled initial surface has been collapsed to the
distance budget, the fixed normalization factor `((2 L²) / σ³)` turns that budget into the
`ξ²` scalar quartic used by the final one-variable estimate. -/
private lemma modifiedNewtonInitialDistance_budget_normalization
    {σ : ℝ} {L : NNReal} {x0 xStar : E} {α : ℝ}
    (hσ : 0 < σ) :
    let ξ : ℝ := modifiedNewtonCharacteristicQuantity σ L x0 xStar
    let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
    s * (((1 - α) ^ (2 : ℕ)) * ((σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) +
        ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x0 - xStar‖ ^ (3 : ℕ)) =
      ((((1 - α) ^ (2 : ℕ)) + (1 / 3 : ℝ) * α ^ (3 : ℕ) * ξ) * ξ ^ (2 : ℕ)) := by
  let ξ : ℝ := modifiedNewtonCharacteristicQuantity σ L x0 xStar
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  -- Separate the quadratic and cubic pieces, then rewrite each with the dedicated `ξ`
  -- normalization lemmas.
  rw [mul_add]
  rw [show s * ((1 - α) ^ (2 : ℕ) * ((σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ))) =
      ((1 - α) ^ (2 : ℕ)) *
        (s * ((σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ))) by ring]
  rw [show s * (((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x0 - xStar‖ ^ (3 : ℕ)) =
      ((1 / 3 : ℝ) * α ^ (3 : ℕ) * ξ) * ξ ^ (2 : ℕ) by
        simpa [ξ, s] using
          modifiedNewton_initial_cubic_normalization (hσ := hσ) (x0 := x0) (xStar := xStar)
            (L := L) (α := α)]
  rw [show s * ((σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) = ξ ^ (2 : ℕ) by
      simpa [ξ, s] using
        modifiedNewton_initial_quadratic_normalization (hσ := hσ) (L := L) (x0 := x0)
          (xStar := xStar)]
  ring

/-- Helper for Proposition 4.4.10: once the line-map surface has been collapsed to the distance
budget at `α = (3 / 4) / sqrt ξ`, the remaining scalar estimate is exactly the quartic margin
`((21 / 20) * sqrt ξ)^4`. -/
private lemma modifiedNewtonInitialBudgetSurface_le_quarticMargin
    {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar) :
    let ξ : ℝ := modifiedNewtonCharacteristicQuantity σ L x0 xStar
    let γ : ℝ := Real.sqrt ξ
    let α : ℝ := (3 / 4 : ℝ) / γ
    let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
    s * ((((1 - α) ^ (2 : ℕ)) * ((σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ))) +
        ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x0 - xStar‖ ^ (3 : ℕ)) ≤
      (((21 / 20 : ℝ) * γ) ^ (4 : ℕ)) := by
  let ξ : ℝ := modifiedNewtonCharacteristicQuantity σ L x0 xStar
  let γ : ℝ := Real.sqrt ξ
  let α : ℝ := (3 / 4 : ℝ) / γ
  let s : ℝ := (((2 : ℝ) * (L : ℝ) ^ (2 : ℕ)) / σ ^ (3 : ℕ))
  have hξ_nonneg : 0 ≤ ξ := le_trans (by norm_num) hxi
  have hγ_ge_one : 1 ≤ γ := by
    have hsq : (1 : ℝ) ^ (2 : ℕ) ≤ γ ^ (2 : ℕ) := by
      simpa [γ, Real.sq_sqrt hξ_nonneg] using hxi
    exact (sq_le_sq₀ (by positivity : 0 ≤ (1 : ℝ)) (Real.sqrt_nonneg ξ)).1 hsq
  have hnormalize :
      s * ((((1 - α) ^ (2 : ℕ)) * ((σ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ))) +
          ((L : ℝ) / 6) * α ^ (3 : ℕ) * ‖x0 - xStar‖ ^ (3 : ℕ)) =
        ((((1 - α) ^ (2 : ℕ)) + (1 / 3 : ℝ) * α ^ (3 : ℕ) * ξ) * ξ ^ (2 : ℕ)) := by
    -- Rewrite the geometric budget into the scalar `ξ`-surface consumed by the quartic estimate.
    simpa [ξ, s] using
      modifiedNewtonInitialDistance_budget_normalization
        (hσ := hσ) (L := L) (x0 := x0) (xStar := xStar) (α := α)
  -- The pure scalar step is already isolated in the earlier `γ`-polynomial estimate.
  rw [hnormalize]
  simpa [ξ, γ, α, Real.sq_sqrt hξ_nonneg] using
    modifiedNewton_initial_specialized_gamma_poly_le_quartic_margin hγ_ge_one

/-- Helper for Proposition 4.4.10: the first shifted accepted-step gap should satisfy the direct
quartic budget once the accepted-step scalar envelope is combined with the frozen-model
decomposition and the full-trial error surface at `k = 0`. -/
private lemma modifiedNewtonShiftedNormalizedGapInitial_le_budgetQuartic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar) :
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0 ≤
      (((21 / 20 : ℝ) * Real.sqrt
          (modifiedNewtonCharacteristicQuantity σ L x0 xStar)) ^ (4 : ℕ)) := by
  -- Route correction: the initial quartic bridge is now owned by the line-map surface rather than
  -- the discarded exact-remainder branch.
  simpa using
    modifiedNewton_initial_specialized_lineMapSurface_le_budgetQuartic
      (hσ := hσ) (hφ_strong := hφ_strong) (hφ_hessian := hφ_hessian)
      (hxStar := hxStar) (method := method) (xStar := xStar) hxi

/-- Helper for Proposition 4.4.10: once the repaired normalized recurrence is specialized with
`α = (3 / 5) / β`, the remaining quartic scalar inequality closes on the phase range
`β ≥ 1 / sqrt 2`. -/
private lemma modifiedNewtonQuarterPhaseScalarStep
    {β : ℝ}
    (hβ : 1 / Real.sqrt (2 : ℝ) ≤ β) :
    ((((1 - (3 / 5 : ℝ) / β) ^ (2 : ℕ)) +
          (1 / 3 : ℝ) * ((3 / 5 : ℝ) / β) ^ (3 : ℕ) * β ^ (2 : ℕ)) *
        β ^ (4 : ℕ)) ≤
      (β - 1 / 5 : ℝ) ^ (4 : ℕ) := by
  have hβ_pos : 0 < β := by
    -- The phase hypothesis places `β` above a fixed positive threshold.
    have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := by positivity
    have hthreshold_pos : 0 < (1 : ℝ) / Real.sqrt (2 : ℝ) := by positivity
    linarith
  have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
  -- Clear the reciprocal denominators and reduce to a polynomial inequality on the half-line.
  field_simp [hβ_ne]
  nlinarith [hβ]

/-- Helper for Proposition 4.4.10: the live large-phase recurrence also closes on the same
chosen parameter `α = (3 / 5) / β` once `β` stays above `1 / sqrt 2`. -/
private lemma modifiedNewtonQuarterPhaseLargePhaseScalarStep
    {β : ℝ}
    (hβ : 1 / Real.sqrt (2 : ℝ) ≤ β) :
    (((1 - (3 / 5 : ℝ) / β) +
          (β ^ (2 : ℕ) / 3) *
            (((3 / 5 : ℝ) / β) +
              ((3 / 5 : ℝ) / β) ^ (3 : ℕ) * (1 + β ^ (2 : ℕ) / 2) ^ (3 : ℕ))) *
        β ^ (4 : ℕ)) ≤
      (β - 1 / 5 : ℝ) ^ (4 : ℕ) := by
  have hβ_pos : 0 < β := by
    -- The phase hypothesis keeps the quarter-root variable away from zero.
    have hthreshold_pos : 0 < (1 : ℝ) / Real.sqrt (2 : ℝ) := by positivity
    linarith
  have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
  -- Clear the reciprocal denominators and reduce to a scalar polynomial inequality.
  field_simp [hβ_ne]
  nlinarith [hβ]

/-- Helper for Proposition 4.4.10: once the repaired initial-step recurrence is specialized with
`α = (3 / 4) / γ`, the remaining quartic budget inequality closes on the range `γ ≥ 1`. -/
private lemma modifiedNewtonInitialBudgetScalarStep
    {γ : ℝ}
    (hγ : 1 ≤ γ) :
    ((((1 - (3 / 4 : ℝ) / γ) ^ (2 : ℕ)) +
          (1 / 3 : ℝ) * ((3 / 4 : ℝ) / γ) ^ (3 : ℕ) * γ ^ (2 : ℕ)) *
        γ ^ (4 : ℕ)) ≤
      ((21 / 20 : ℝ) * γ) ^ (4 : ℕ) := by
  have hγ_pos : 0 < γ := by
    -- The source regime keeps the normalized square-root variable away from zero.
    linarith
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  -- Clear the reciprocal denominators and finish with a scalar polynomial estimate.
  field_simp [hγ_ne]
  nlinarith

/-- Helper for Proposition 4.4.10: above the shifted threshold `Δ j ≥ 1 / 4`, the shifted
accepted-step gap should lose at least `1 / 5` in quarter-root variables in one step. -/
private lemma modifiedNewtonShiftedNormalizedGapRpowDrop_of_ge_quarter
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    {j : ℕ}
    (hj :
      (1 / 4 : ℝ) ≤ modifiedNewtonShiftedNormalizedGap
        (σ := σ) (L := L) (xStar := xStar) method j) :
    Real.rpow
        (modifiedNewtonShiftedNormalizedGap
          (σ := σ) (L := L) (xStar := xStar) method (j + 1))
        (1 / 4 : ℝ) ≤
    Real.rpow
          (modifiedNewtonShiftedNormalizedGap
            (σ := σ) (L := L) (xStar := xStar) method j)
          (1 / 4 : ℝ) -
        (1 / 5 : ℝ) := by
  let Δ : ℕ → ℝ := modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method
  let β : ℝ := Real.rpow (Δ j) (1 / 4 : ℝ)
  have hΔ_nonneg : 0 ≤ Δ j := by
    -- Keep the current shifted gap nonnegative before passing to quarter-root variables.
    simpa [Δ] using modifiedNewtonShiftedNormalizedGap_nonneg hσ hxStar method j
  have hΔ_succ_nonneg : 0 ≤ Δ (j + 1) := by
    -- The same nonnegativity holds at the next shifted index.
    simpa [Δ] using modifiedNewtonShiftedNormalizedGap_nonneg hσ hxStar method (j + 1)
  have hβ_four : β ^ (4 : ℕ) = Δ j := by
    -- The current shifted gap is exactly the fourth power of the quarter-root variable `β`.
    calc
      β ^ (4 : ℕ) = Real.rpow (Δ j) ((1 / 4 : ℝ) * (4 : ℝ)) := by
        simpa [β, Real.rpow_natCast] using
          (Real.rpow_mul hΔ_nonneg (1 / 4 : ℝ) (4 : ℝ)).symm
      _ = Δ j := by
        norm_num [Real.rpow_one]
  have hβ_nonneg : 0 ≤ β := by
    -- The quarter-root variable stays nonnegative because it is an `rpow` of a nonnegative gap.
    exact Real.rpow_nonneg hΔ_nonneg _
  have hnormalized_drop :
      Δ (j + 1) ≤ (β - (1 / 5 : ℝ)) ^ (4 : ℕ) := by
    let α : ℝ := (3 / 5 : ℝ) / β
    have hβ_sq_ge_half : (1 / 2 : ℝ) ≤ β ^ (2 : ℕ) := by
      -- The phase hypothesis `Δ j ≥ 1 / 4` implies the quarter-root variable lies above the
      -- stronger threshold `1 / sqrt 2`.
      have hβ_four_ge : (1 / 4 : ℝ) ≤ β ^ (4 : ℕ) := by
        simpa [hβ_four] using hj
      have hβ_sq_nonneg : 0 ≤ β ^ (2 : ℕ) := by positivity
      nlinarith
    have hβ_ge_threshold : 1 / Real.sqrt (2 : ℝ) ≤ β := by
      have hthreshold_sq : (1 / Real.sqrt (2 : ℝ)) ^ (2 : ℕ) = (1 / 2 : ℝ) := by
        have hsqrt_two_sq : Real.sqrt (2 : ℝ) ^ (2 : ℕ) = (2 : ℝ) := by
          simpa [pow_two] using Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)
        nlinarith
      have hsq : (1 / Real.sqrt (2 : ℝ)) ^ (2 : ℕ) ≤ β ^ (2 : ℕ) := by
        rw [hthreshold_sq]
        exact hβ_sq_ge_half
      exact (sq_le_sq₀ (by positivity : 0 ≤ 1 / Real.sqrt (2 : ℝ)) hβ_nonneg).1 hsq
    have hβ_ge_threeFifths : (3 / 5 : ℝ) ≤ β := by
      have hsq : (3 / 5 : ℝ) ^ (2 : ℕ) ≤ β ^ (2 : ℕ) := by
        calc
          (3 / 5 : ℝ) ^ (2 : ℕ) ≤ (1 / 2 : ℝ) := by norm_num
          _ ≤ β ^ (2 : ℕ) := hβ_sq_ge_half
      exact (sq_le_sq₀ (by positivity : 0 ≤ (3 / 5 : ℝ)) hβ_nonneg).1 hsq
    have hβ_pos : 0 < β := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / Real.sqrt (2 : ℝ))
      hβ_ge_threshold
    have hα : α ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact (div_le_iff₀ hβ_pos).2 <| by
          simpa [α] using hβ_ge_threeFifths
    have hsqrt_eq : Real.sqrt (Δ j) = β ^ (2 : ℕ) := by
      -- Rewrite the square root of the current shifted gap in terms of the quarter-root variable.
      rw [← hβ_four]
      calc
        Real.sqrt (β ^ (4 : ℕ)) = Real.sqrt ((β ^ (2 : ℕ)) ^ (2 : ℕ)) := by
          congr 1
          ring_nf
        _ = β ^ (2 : ℕ) := by
          rw [Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (by positivity : 0 ≤ β ^ (2 : ℕ))
    have hlocal :
        Δ (j + 1) ≤
          (((1 - α) +
                (β ^ (2 : ℕ) / 3) *
                  (α + α ^ (3 : ℕ) * (1 + β ^ (2 : ℕ) / 2) ^ (3 : ℕ))) *
            β ^ (4 : ℕ)) := by
      -- Route correction: consume the live large-phase recurrence directly on the chosen
      -- `α = (3 / 5) / β` surface instead of rebuilding the discarded repaired local model.
      calc
        Δ (j + 1) ≤
            ((1 - α) +
                (Real.sqrt (Δ j) / 3) *
                  (α + α ^ (3 : ℕ) * (1 + Real.sqrt (Δ j) / 2) ^ (3 : ℕ))) *
              Δ j := by
                exact
                  modifiedNewtonShiftedNormalizedGapSucc_le_largePhaseModel
                    hσ hφ_strong hφ_hessian hxStar method (j := j) hα
        _ = (((1 - α) +
                (β ^ (2 : ℕ) / 3) *
                  (α + α ^ (3 : ℕ) * (1 + β ^ (2 : ℕ) / 2) ^ (3 : ℕ))) *
              β ^ (4 : ℕ)) := by
                rw [hsqrt_eq, hβ_four]
    have hscalar :
        (((1 - α) +
              (β ^ (2 : ℕ) / 3) *
                (α + α ^ (3 : ℕ) * (1 + β ^ (2 : ℕ) / 2) ^ (3 : ℕ))) *
            β ^ (4 : ℕ)) ≤
          (β - (1 / 5 : ℝ)) ^ (4 : ℕ) := by
      -- The chosen parameter `α = (3 / 5) / β` closes the quartic estimate on the live
      -- large-phase scalar surface.
      simpa [α] using modifiedNewtonQuarterPhaseLargePhaseScalarStep hβ_ge_threshold
    exact hlocal.trans hscalar
  have hβ_sub_nonneg : 0 ≤ β - (1 / 5 : ℝ) := by
    -- The threshold hypothesis `Δ j ≥ 1 / 4` forces `β` well above the drop size `1 / 5`.
    have hβ_four_ge : (1 / 4 : ℝ) ≤ β ^ (4 : ℕ) := by
      simpa [hβ_four] using hj
    have hβ_sq_ge_half : (1 / 2 : ℝ) ≤ β ^ (2 : ℕ) := by
      have hβ_sq_nonneg : 0 ≤ β ^ (2 : ℕ) := by positivity
      nlinarith
    have hβ_ge_half : (1 / 2 : ℝ) ≤ β := by
      have hsq : (1 / 2 : ℝ) ^ (2 : ℕ) ≤ β ^ (2 : ℕ) := by
        calc
          (1 / 2 : ℝ) ^ (2 : ℕ) ≤ (1 / 2 : ℝ) := by norm_num
          _ ≤ β ^ (2 : ℕ) := hβ_sq_ge_half
      exact (sq_le_sq₀ (by positivity : 0 ≤ (1 / 2 : ℝ)) hβ_nonneg).1 hsq
    linarith
  -- Once the quartic model is available, take fourth roots on both sides in one monotone step.
  have hroot :=
    quarterRoot_le_of_le_fourthPower hΔ_succ_nonneg hβ_sub_nonneg hnormalized_drop
  simpa [β] using hroot

/-- Helper for Proposition 4.4.10: under the source assumption `1 ≤ ξ`, the initial shifted
accepted-step quarter root should already be bounded by a budget-compatible multiple of
`sqrt ξ`. -/
private lemma modifiedNewtonShiftedNormalizedGapInitialRpow_le_budgetCompatibleSqrtCharacteristic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar) :
    Real.rpow
        (modifiedNewtonShiftedNormalizedGap
          (σ := σ) (L := L) (xStar := xStar) method 0)
        (1 / 4 : ℝ) ≤
      (21 / 20 : ℝ) *
        Real.sqrt (modifiedNewtonCharacteristicQuantity σ L x0 xStar) := by
  let ξ : ℝ := modifiedNewtonCharacteristicQuantity σ L x0 xStar
  let Δ0 : ℝ :=
    modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method 0
  have hξ_nonneg : 0 ≤ ξ := by
    -- The source hypothesis `1 ≤ ξ` places the characteristic quantity in the nonnegative range.
    exact le_trans (by norm_num) hxi
  have hΔ0_nonneg : 0 ≤ Δ0 := by
    -- The initial shifted accepted-step gap is nonnegative by construction.
    simpa [Δ0] using modifiedNewtonShiftedNormalizedGap_nonneg hσ hxStar method 0
  have hinitial_quartic :
      Δ0 ≤ ((21 / 20 : ℝ) * Real.sqrt ξ) ^ (4 : ℕ) := by
    -- Route correction: the initial bridge now comes directly from the quartic budget lemma,
    -- instead of the discarded fixed-`α` local-model surface.
    simpa [Δ0, ξ] using
      modifiedNewtonShiftedNormalizedGapInitial_le_budgetQuartic
        hσ hφ_strong hφ_hessian hxStar method hxi
  have hbudget_nonneg : 0 ≤ (21 / 20 : ℝ) * Real.sqrt ξ := by
    -- The source regime `ξ ≥ 1` keeps the budget-compatible quarter-root bound nonnegative.
    exact mul_nonneg (by positivity : 0 ≤ (21 / 20 : ℝ)) (Real.sqrt_nonneg ξ)
  -- The remaining step is the same generic fourth-root monotonicity applied to the initial gap.
  exact quarterRoot_le_of_le_fourthPower hΔ0_nonneg hbudget_nonneg hinitial_quartic

/-- Helper for Proposition 4.4.10: the remaining global phase should first reach the stronger
shifted normalized-gap threshold `Δ j ≤ 1 / 4`, which immediately gives `q_(j+1) ≤ 1 / 2`. -/
private lemma modifiedNewtonExistsQuarterShiftedGapEntry_le_sqrtCharacteristic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar) :
    ∃ j : ℕ,
      ((j + 1 : ℕ) : ℝ) ≤
        (25 / 4 : ℝ) * Real.sqrt (modifiedNewtonCharacteristicQuantity σ L x0 xStar) ∧
        modifiedNewtonShiftedNormalizedGap
          (σ := σ) (L := L) (xStar := xStar) method j ≤ (1 / 4 : ℝ) := by
  let Δ : ℕ → ℝ := modifiedNewtonShiftedNormalizedGap (σ := σ) (L := L) (xStar := xStar) method
  -- Route correction: isolate the public global blocker as a pure shifted-gap entry witness
  -- before converting it to the half-threshold on `q_(j+1)`.
  have hnonneg : ∀ j : ℕ, 0 ≤ Δ j := by
    intro j
    -- Every shifted normalized gap is nonnegative by construction from an accepted-step gap.
    simpa [Δ] using modifiedNewtonShiftedNormalizedGap_nonneg hσ hxStar method j
  have hdrop :
      ∀ j : ℕ, (1 / 4 : ℝ) ≤ Δ j →
        Real.rpow (Δ (j + 1)) (1 / 4 : ℝ) ≤
          Real.rpow (Δ j) (1 / 4 : ℝ) - (1 / 5 : ℝ) := by
    intro j hj
    -- Consume the analytic quarter-root decrement once it is proved on the shifted-gap surface.
    simpa [Δ] using
      modifiedNewtonShiftedNormalizedGapRpowDrop_of_ge_quarter
        hσ hφ_strong hφ_hessian hxStar method hj
  have hinit :
      Real.rpow (Δ 0) (1 / 4 : ℝ) ≤
        (21 / 20 : ℝ) *
          Real.sqrt (modifiedNewtonCharacteristicQuantity σ L x0 xStar) := by
    -- The remaining initial bridge should be stated directly on the shifted accepted-step gap.
    simpa [Δ] using
      modifiedNewtonShiftedNormalizedGapInitialRpow_le_budgetCompatibleSqrtCharacteristic
        hσ hφ_strong hφ_hessian hxStar method hxi
  rcases existsQuarterEntry_of_shiftedGapQuarterRootDrop hnonneg hdrop with
    ⟨j, hj_generic, hj_quarter⟩
  refine ⟨j, ?_, hj_quarter⟩
  have hbudget :
      1 + 5 * Real.rpow (Δ 0) (1 / 4 : ℝ) ≤
        (25 / 4 : ℝ) * Real.sqrt (modifiedNewtonCharacteristicQuantity σ L x0 xStar) := by
    -- The generic threshold-entry budget closes once the initial quarter root is compared to
    -- `sqrt ξ` with the budget-compatible constant.
    exact one_add_five_mul_initialQuarterRoot_le_sqrtCharacteristicBudget hxi hinit
  exact hj_generic.trans hbudget

/-- Helper for Proposition 4.4.10: the remaining global phase should first reach the stronger
shifted normalized-gap threshold `Δ j ≤ 1 / 4`, which immediately gives `q_(j+1) ≤ 1 / 2`. -/
private lemma modifiedNewtonExistsHalfThresholdEntry_le_sqrtCharacteristic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar) :
    ∃ j : ℕ,
      ((j + 1 : ℕ) : ℝ) ≤
        (25 / 4 : ℝ) * Real.sqrt (modifiedNewtonCharacteristicQuantity σ L x0 xStar) ∧
        modifiedNewtonCharacteristicQuantity σ L (method (j + 1)) xStar ≤ (1 / 2 : ℝ) := by
  rcases modifiedNewtonExistsQuarterShiftedGapEntry_le_sqrtCharacteristic
      hσ hφ_strong hφ_hessian hxStar method hxi with
    ⟨j, hj_bound, hj_quarter⟩
  refine ⟨j, hj_bound, ?_⟩
  -- Convert the quarter-threshold witness on the shifted accepted-step gap into the half-threshold
  -- witness on the next characteristic quantity.
  exact
    modifiedNewtonCharacteristicSucc_le_half_of_shiftedNormalizedGap_le_quarter
      hσ hφ_strong hφ_hessian hxStar method hj_quarter

/-- Helper for Proposition 4.4.10: some modified-Newton iterate enters the local quadratic region
within the displayed `6.25 * sqrt ξ` threshold. -/
private lemma modifiedNewton_existsQuadraticRegionEntry_le_sqrtCharacteristic
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar) :
    ∃ k : ℕ,
      (k : ℝ) ≤
        (25 / 4 : ℝ) * Real.sqrt (modifiedNewtonCharacteristicQuantity σ L x0 xStar) ∧
        InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k := by
  rcases modifiedNewtonExistsHalfThresholdEntry_le_sqrtCharacteristic
      hσ hφ_strong hφ_hessian hxStar method hxi with
    ⟨j, hj_bound, hj_half⟩
  refine ⟨j + 1, ?_, ?_⟩
  · -- The stronger half-threshold witness already carries the displayed iteration budget.
    simpa using hj_bound
  · -- The half-threshold is strictly inside the public quadratic-convergence region `q < 1`.
    have hj_lt_one :
        modifiedNewtonCharacteristicQuantity σ L (method (j + 1)) xStar < 1 := by
      linarith
    simpa using hj_lt_one

/-- Proposition 4.4.10: with characteristic quantity
`ξ = L ‖x₀ - x*‖ / σ`, if `φ` is `σ`-strongly convex on `Set.univ`, belongs to `C22[L]`, `x*`
minimizes `φ` on `Set.univ`, `method` is the associated modified Newton iteration started at
`x₀`, and `N₁` is the first iterate index for which the orbit enters the modified-Newton region of
quadratic convergence, then the assumption `1 ≤ ξ` implies `N₁ ≤ 6.25 * sqrt ξ`. -/
theorem modifiedNewton_firstQuadraticRegionEntryIndex_le_sqrt_characteristicQuantity
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar)
    {N1 : ℕ}
    (hN1 :
      IsLeast {k : ℕ | InModifiedNewtonQuadraticConvergenceRegion method σ L xStar k} N1) :
    (N1 : ℝ) ≤
      (25 / 4 : ℝ) * Real.sqrt (modifiedNewtonCharacteristicQuantity σ L x0 xStar) := by
  rcases modifiedNewton_existsQuadraticRegionEntry_le_sqrtCharacteristic
      hσ hφ_strong hφ_hessian hxStar method hxi with
    ⟨k, hk_bound, hk_mem⟩
  have hN1_le_k : N1 ≤ k := hN1.2 hk_mem
  exact (show (N1 : ℝ) ≤ (k : ℝ) from by exact_mod_cast hN1_le_k).trans hk_bound

/-- If `N₁` is the least index from which the modified Newton orbit converges quadratically to
`x*`, then the same scalar bound as in Proposition 4.4.10 applies to that tail-convergence index.
This is kept as a companion corollary for downstream uses that package the first quadratic phase by
`HasQuadraticConvergenceFrom`. -/
theorem modifiedNewton_firstQuadraticConvergenceIndex_le_sqrt_characteristicQuantity
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : ModifiedNewtonMethod φ x0)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar)
    {N1 : ℕ}
    (hN1 :
      IsLeast {k : ℕ | HasQuadraticConvergenceFrom method xStar k} N1) :
    (N1 : ℝ) ≤
      (25 / 4 : ℝ) * Real.sqrt (modifiedNewtonCharacteristicQuantity σ L x0 xStar) := by
  rcases modifiedNewton_existsQuadraticRegionEntry_le_sqrtCharacteristic
      hσ hφ_strong hφ_hessian hxStar method hxi with
    ⟨k, hk_bound, hk_mem⟩
  have hk_quad : HasQuadraticConvergenceFrom method xStar k :=
    hasQuadraticConvergenceFrom_of_inModifiedNewtonQuadraticConvergenceRegion
      hσ hφ_strong hφ_hessian hxStar method hk_mem
  have hN1_le_k : N1 ≤ k := hN1.2 hk_quad
  exact (show (N1 : ℝ) ≤ (k : ℝ) from by exact_mod_cast hN1_le_k).trans hk_bound

end
