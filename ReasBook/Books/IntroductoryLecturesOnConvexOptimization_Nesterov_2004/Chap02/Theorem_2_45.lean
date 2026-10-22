/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_35
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

open AffineMap
open scoped MaxTypeStep StrongConvexSmooth

/- Primary domain: accelerated exact proximal-gradient recurrences for unconstrained smooth
max-type objectives on proper real inner-product spaces.

Owner declarations sampled for this refinement:
* `SmoothMinimaxProblem` in `Definition_2_38` owns the component family together with the smooth
  strongly convex problem data;
* `constantStepSchemeIIMinimax` and `constantStepSchemeIIMinimaxX` in `Algorithm_2_9`, the
  recursive source-facing Algorithm 2.9 owner and its iterate projection;
* `maxTypeAffineApproximation` in `Lemma_2_18` owns the affine max-type local model;
* `quadraticallyRegularizedObjective` in `Definition_1_4_17.lean` owns the exact proximal
  subproblem;
* `optimal_method_alpha0_initial_curvature` in `Algorithm_2_4` owns the canonical scalar
  `γ₀ = α₀ (α₀ L - μ) / (1 - α₀)` attached to the admissible initial parameter `α₀`.

Accordingly the primitive data here are the smooth minimax owner `problem`, the unconstrained
specialization `problem.feasibleSet = Set.univ`, a minimizing point `xStar` for `Set.univ`, the
source-facing scalar assumptions, the positive step-size witness `hL : 0 < L`, and the recursive
Algorithm 2.9 trajectory determined by the initial data `x0, α₀`. The constrained owner
trajectory is used through the canonical subtype bridge induced by
`problem.feasibleSet = Set.univ`, so no parallel unconstrained scheme wrapper is introduced. The
component `C¹` regularity, the induced curvature interval `γ₀ ∈ (μ, 3L + μ]`, and the exact
proximal-step specification are derived from these owners: `problem.components_mem` supplies
`0 < μ`, `hL` supplies `0 < L`, and
`optimal_method_alpha0_initial_curvature_mem_Ioc` turns the admissible `α₀` hypothesis into the
owner interval fact for `γ₀`. The canonical reciprocal-condition-number owner remains the chapter
notation `q[μ, L]`, so the public theorem surface should use `√q[μ, L]` rather than expanding it
back to `√(μ / L)`.
-/

section AcceleratedMaxTypeProximalRates

variable {μ L : ℝ} (problem : SmoothMinimaxProblem E ι μ L)

local notation "Q" => problem.feasibleSet
local instance instLocalChap02_Theorem_2_451 : Fact (Set.Nonempty Q) := ⟨problem.feasible_nonempty⟩
local instance instLocalChap02_Theorem_2_452 : Fact (IsClosed Q) := ⟨problem.feasible_closed⟩
local instance instLocalChap02_Theorem_2_453 : Fact (Convex ℝ Q) := ⟨problem.feasible_convex⟩

private theorem x0_mem_feasible
    (hfeasible_univ : problem.feasibleSet = Set.univ) (x0 : E) :
    x0 ∈ problem.feasibleSet := by
  simp [hfeasible_univ]

section

variable (hfeasible_univ : problem.feasibleSet = Set.univ)
local notation "fObj" => maxTypeObjective problem.components
variable (xStar : E)
variable (hL : 0 < L)
variable (x0 : E)
local notation "γL" => (Units.mk0 (Real.toNNReal L) (by positivity) : NNRealˣ)
local notation "qf" => q[μ, L]
local notation "αRange" => Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf)

variable (α0 : ℝ)

local notation "γ0" => optimal_method_alpha0_initial_curvature μ L α0
variable (hα0 : α0 ∈ αRange)
local notation "x0Q" =>
  Subtype.mk x0 (x0_mem_feasible problem hfeasible_univ x0)
local notation "xSeq" =>
  constantStepSchemeIIMinimaxX problem hL x0Q (Subtype.mk α0 hα0)

/-- Helper for Theorem 2.45: the admissible initial scalar `α₀` forces the induced curvature
`γ₀ = α₀ (α₀ L - μ) / (1 - α₀)` to lie in the interval `(μ, 3L + μ]`. -/
private lemma accelerated_max_type_gamma0_mem_Ioc
    (problem : SmoothMinimaxProblem E ι μ L)
    (hL : 0 < L)
    (hα0 : α0 ∈ αRange) :
    γ0 ∈ Set.Ioc μ (3 * L + μ) := by
  classical
  -- Convert the textbook `α₀` hypothesis into the scalar interval required by the Chapter 2
  -- weight bounds.
  let i : ι := Classical.choice ‹Nonempty ι›
  have hcomponent : IsStrongConvexSmoothObjective μ L (problem.components i) := by
    simpa [Set.mem_setOf_eq] using problem.components_mem i
  exact optimal_method_alpha0_initial_curvature_mem_Ioc hcomponent.mu_pos hL hα0

/-- Helper for Theorem 2.45: the initial Lyapunov energy is nonnegative at a global minimizer. -/
private lemma accelerated_max_type_initial_energy_nonneg
    (problem : SmoothMinimaxProblem E ι μ L)
    (xStar : E)
    (hxStar : IsMinOn (maxTypeObjective problem.components) Set.univ xStar)
    (hL : 0 < L)
    (hα0 : α0 ∈ αRange) :
    0 ≤ maxTypeObjective problem.components x0 -
        maxTypeObjective problem.components xStar +
        (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  -- The initial energy is the sum of the initial objective gap and a nonnegative quadratic term.
  have hγ0 : γ0 ∈ Set.Ioc μ (3 * L + μ) :=
    accelerated_max_type_gamma0_mem_Ioc (problem := problem) (hL := hL) (hα0 := hα0)
  have hobj_nonneg :
      0 ≤ maxTypeObjective problem.components x0 -
          maxTypeObjective problem.components xStar := by
    exact sub_nonneg.mpr ((isMinOn_univ_iff.mp hxStar) x0)
  have hquad_nonneg : 0 ≤ (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hμ : 0 < μ := by
      classical
      let i : ι := Classical.choice ‹Nonempty ι›
      exact (mem_S11_iff.mp (problem.components_mem i)).mu_pos
    have hγ0_pos : 0 < γ0 := lt_trans hμ hγ0.1
    positivity
  linarith

/-- Helper for Theorem 2.45: the exact minimax residual at stage `j` is the scaled step gap
`L • (y_j - x_{j+1})`. -/
private lemma accelerated_max_type_reduced_gradient_eq_smul_sub
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    g_f[Q | problem.components; γL]
        (constantStepSchemeIIMinimaxY problem hL x0Q (Subtype.mk α0 hα0') j) =
      L •
        (constantStepSchemeIIMinimaxY problem hL x0Q (Subtype.mk α0 hα0') j -
          (constantStepSchemeIIMinimaxX problem hL x0Q (Subtype.mk α0 hα0') (j + 1) : E)) := by
  -- Rewrite the chosen-step residual through the source-facing iterate update.
  simpa [Real.toNNReal_of_nonneg hL.le] using
    maxTypeReducedGradient_eq_smul_sub_ofFact
      Q
      problem.components
      (constantStepSchemeIIMinimaxY problem hL x0Q (Subtype.mk α0 hα0') j)
      γL

/-- Helper for Theorem 2.45: the curvature sequence generated by the Algorithm 2.9 scalar
parameters satisfies the owner identity `γ_{j+1} = L α_j²`. -/
private lemma accelerated_max_type_estimating_curvature_succ_eq_L_mul_sq
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    estimatingSequenceCurvature μ γ0
        (constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0'))
        (j + 1) =
      L *
        (constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0') j) ^ (2 : ℕ) := by
  -- The induced initial curvature and the scalar recurrence recover the standard owner formula.
  induction j with
  | zero =>
      have hα0_Ioo : α0 ∈ Set.Ioo (0 : ℝ) 1 :=
        constantStepSchemeII_alpha_mem_Ioo_of_mem_Ioc hα0'
      rw [estimatingSequenceCurvature_succ]
      simp
      unfold optimal_method_alpha0_initial_curvature
      field_simp [sub_ne_zero.mpr hα0_Ioo.2.ne']
      ring
  | succ j ih =>
      rw [estimatingSequenceCurvature_succ, ih]
      have hrec :=
        constantStepSchemeIIMinimaxAlpha_succ_equation
          problem hL x0Q (Subtype.mk α0 hα0') j
      have hcalc :
          (1 -
                constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0') (j + 1)) *
              (L *
                (constantStepSchemeIIMinimaxAlpha
                    problem hL x0Q (Subtype.mk α0 hα0') j) ^
                  (2 : ℕ)) +
            constantStepSchemeIIMinimaxAlpha
                problem hL x0Q (Subtype.mk α0 hα0') (j + 1) *
              μ =
            L *
              (constantStepSchemeIIMinimaxAlpha
                  problem hL x0Q (Subtype.mk α0 hα0') (j + 1)) ^
                (2 : ℕ) := by
        have hscaled := congrArg (fun t : ℝ => L * t) hrec
        field_simp [hL.ne'] at hscaled
        nlinarith [hscaled]
      simpa using hcalc

/-- Helper for Theorem 2.45: the Algorithm 2.9 main iterate sequence with an arbitrary admissible
initial scalar witness. -/
private def acceleratedMaxTypeXSeq
    (hα0' : α0 ∈ αRange) :
    ℕ → E :=
  fun k ↦ constantStepSchemeIIMinimaxX problem hL x0Q (Subtype.mk α0 hα0') k

/-- Helper for Theorem 2.45: the Algorithm 2.9 extrapolated sequence with an arbitrary admissible
initial scalar witness. -/
private def acceleratedMaxTypeYSeq
    (hα0' : α0 ∈ αRange) :
    ℕ → E :=
  constantStepSchemeIIMinimaxY problem hL x0Q (Subtype.mk α0 hα0')

/-- Helper for Theorem 2.45: the Algorithm 2.9 scalar sequence with an arbitrary admissible
initial scalar witness. -/
private def acceleratedMaxTypeAlphaSeq
    (hα0' : α0 ∈ αRange) :
    ℕ → ℝ :=
  constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0')

/-- Helper for Theorem 2.45: the stage-`j` exact lower affine-quadratic model built from the
Algorithm 2.9 exact step and reduced gradient. -/
private def acceleratedMaxTypeEstimatingModel
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    E → ℝ :=
  fun x ↦
    let yj :=
      acceleratedMaxTypeYSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let xNext :=
      acceleratedMaxTypeXSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    let g :=
      g_f[Q | problem.components; γL](yj)
    fObj xNext +
      inner ℝ g (x - yj) +
      (1 / (2 * L)) * ‖g‖ ^ (2 : ℕ) +
      (μ / 2) * ‖x - yj‖ ^ (2 : ℕ)

/-- Helper for Theorem 2.45: the theorem-local estimating-sequence functions generated by the
max-type exact lower models. -/
private def acceleratedMaxTypeEstimatingFunction
    (hα0' : α0 ∈ αRange) :
    ℕ → E → ℝ
  | 0 => quadraticallyRegularizedObjective (fun _ : E ↦ fObj x0) γ0 x0
  | j + 1 =>
      lineMap
        (acceleratedMaxTypeEstimatingFunction hα0' j)
        (acceleratedMaxTypeEstimatingModel
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j)
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j)

/-- Helper for Theorem 2.45: the theorem-local estimating-sequence center recursion driven by the
max-type reduced gradients. -/
private def acceleratedMaxTypeEstimatingCenter
    (hα0' : α0 ∈ αRange) :
    ℕ → E
  | 0 => x0
  | j + 1 =>
      let gammaCurr :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          j
      let gammaNext :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          (j + 1)
      let yj :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let gj :=
        g_f[Q | problem.components; γL](yj)
      let αj :=
        acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      (1 / gammaNext) •
        (((1 - αj) * gammaCurr) • acceleratedMaxTypeEstimatingCenter hα0' j +
          (αj * μ) • yj -
          αj • gj)
termination_by j => j
decreasing_by simp_wf

/-- Helper for Theorem 2.45: the theorem-local scalar values `φ_k^*` attached to the max-type
estimating-sequence recursion. -/
private def acceleratedMaxTypeEstimatingValue
    (hα0' : α0 ∈ αRange) :
    ℕ → ℝ
  | 0 => fObj x0
  | j + 1 =>
      let gammaCurr :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          j
      let gammaNext :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          (j + 1)
      let yj :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let gj :=
        g_f[Q | problem.components; γL](yj)
      let xNext :=
        acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' (j + 1)
      let centerCurr :=
        acceleratedMaxTypeEstimatingCenter
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let αj :=
        acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      (1 - αj) *
          acceleratedMaxTypeEstimatingValue hα0' j +
        αj * fObj xNext +
        (αj / (2 * L) - αj ^ (2 : ℕ) / (2 * gammaNext)) * ‖gj‖ ^ (2 : ℕ) +
        (αj * (1 - αj) * gammaCurr / gammaNext) *
          ((μ / 2) * ‖yj - centerCurr‖ ^ (2 : ℕ) + inner ℝ gj (centerCurr - yj))
termination_by j => j
decreasing_by simp_wf

/-- Helper for Theorem 2.45: evaluating the stagewise max-type lower model recovers the displayed
affine-quadratic formula. -/
@[simp] private theorem acceleratedMaxTypeEstimatingModel_apply
    (hα0' : α0 ∈ αRange)
    (j : ℕ) (x : E) :
    acceleratedMaxTypeEstimatingModel
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j x =
      let yj :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let xNext :=
        acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' (j + 1)
      let g :=
        g_f[Q | problem.components; γL](yj)
      fObj xNext +
        inner ℝ g (x - yj) +
        (1 / (2 * L)) * ‖g‖ ^ (2 : ℕ) +
        (μ / 2) * ‖x - yj‖ ^ (2 : ℕ) := rfl

/-- Helper for Theorem 2.45: the theorem-local estimating sequence starts from the initial
quadratic model at `x0`. -/
@[simp] private theorem acceleratedMaxTypeEstimatingFunction_zero
    (hα0' : α0 ∈ αRange) :
    acceleratedMaxTypeEstimatingFunction
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' 0 =
      quadraticallyRegularizedObjective (fun _ : E ↦ fObj x0) γ0 x0 := rfl

/-- Helper for Theorem 2.45: the theorem-local estimating sequence satisfies the affine recursion
with the exact max-type lower model. -/
private theorem acceleratedMaxTypeEstimatingFunction_succ
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    acceleratedMaxTypeEstimatingFunction
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1) =
      lineMap
        (acceleratedMaxTypeEstimatingFunction
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j)
        (acceleratedMaxTypeEstimatingModel
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j)
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j) := rfl

/-- Helper for Theorem 2.45: evaluating the successor stage exposes the line-map recursion
pointwise. -/
@[simp] private theorem acceleratedMaxTypeEstimatingFunction_succ_apply
    (hα0' : α0 ∈ αRange)
    (j : ℕ) (x : E) :
    acceleratedMaxTypeEstimatingFunction
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1) x =
      (1 - acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j) *
          acceleratedMaxTypeEstimatingFunction
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j x +
        acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j *
          acceleratedMaxTypeEstimatingModel
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j x := by
  -- Unfold the affine-combination owner at the point `x`.
  simpa [lineMap_apply_module] using
    congrFun
      (acceleratedMaxTypeEstimatingFunction_succ
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j)
      x

/-- Helper for Theorem 2.45: the theorem-local center recursion starts from the initial point
`x0`. -/
private theorem acceleratedMaxTypeEstimatingCenter_zero
    (hα0' : α0 ∈ αRange) :
    acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' 0 = x0 := by
  -- Unfold the recursive owner at the base stage.
  simp [acceleratedMaxTypeEstimatingCenter]

/-- Helper for Theorem 2.45: the theorem-local value recursion starts from the initial objective
value `f(x0)`. -/
private theorem acceleratedMaxTypeEstimatingValue_zero
    (hα0' : α0 ∈ αRange) :
    acceleratedMaxTypeEstimatingValue
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' 0 = fObj x0 := by
  -- Unfold the scalar recursion at stage `0`.
  simp [acceleratedMaxTypeEstimatingValue]

/-- Helper for Theorem 2.45: every curvature generated by the theorem-local scalar recurrence is
strictly positive. -/
private theorem accelerated_max_type_estimating_curvature_pos'
    (hα0' : α0 ∈ αRange) :
    ∀ j : ℕ,
      0 <
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          j
  | 0 => by
      have hγ0 :
          γ0 ∈ Set.Ioc μ (3 * L + μ) :=
        accelerated_max_type_gamma0_mem_Ioc
          (problem := problem) (hL := hL) (α0 := α0) (hα0 := hα0')
      have hμ : 0 < μ := by
        classical
        let i : ι := Classical.choice inferInstance
        exact (mem_S11_iff.mp (problem.components_mem i)).mu_pos
      exact lt_trans hμ hγ0.1
  | j + 1 => by
      have hcurv :
          estimatingSequenceCurvature μ γ0
              (acceleratedMaxTypeAlphaSeq
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0')
              (j + 1) =
            L *
              (acceleratedMaxTypeAlphaSeq
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j) ^ (2 : ℕ) := by
        simpa [acceleratedMaxTypeAlphaSeq] using
          accelerated_max_type_estimating_curvature_succ_eq_L_mul_sq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j
      rw [hcurv]
      have hα :
          0 <
            acceleratedMaxTypeAlphaSeq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' j := by
        simpa [acceleratedMaxTypeAlphaSeq] using
          (constantStepSchemeIIMinimaxAlpha_mem_Ioo
            problem hL x0Q (Subtype.mk α0 hα0') j).1
      positivity

/-- Helper for Theorem 2.45: the theorem-local center recursion unfolds at successor stages to
the displayed affine update. -/
private theorem acceleratedMaxTypeEstimatingCenter_succ
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1) =
      let gammaCurr :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          j
      let gammaNext :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          (j + 1)
      let yj :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let gj :=
        g_f[Q | problem.components; γL](yj)
      let αj :=
        acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      (1 / gammaNext) •
        (((1 - αj) * gammaCurr) •
            acceleratedMaxTypeEstimatingCenter
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' j +
          (αj * μ) • yj -
          αj • gj) := by
  -- Unfold the recursive definition at stage `j + 1`.
  simp [acceleratedMaxTypeEstimatingCenter]

/-- Helper for Theorem 2.45: the theorem-local minimum-value recursion unfolds at successor stages
to the displayed scalar update. -/
private theorem acceleratedMaxTypeEstimatingValue_succ
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    acceleratedMaxTypeEstimatingValue
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1) =
      let gammaCurr :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          j
      let gammaNext :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          (j + 1)
      let yj :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let gj :=
        g_f[Q | problem.components; γL](yj)
      let xNext :=
        acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' (j + 1)
      let centerCurr :=
        acceleratedMaxTypeEstimatingCenter
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let αj :=
        acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      (1 - αj) *
          acceleratedMaxTypeEstimatingValue
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j +
        αj * fObj xNext +
        (αj / (2 * L) - αj ^ (2 : ℕ) / (2 * gammaNext)) * ‖gj‖ ^ (2 : ℕ) +
        (αj * (1 - αj) * gammaCurr / gammaNext) *
          ((μ / 2) * ‖yj - centerCurr‖ ^ (2 : ℕ) + inner ℝ gj (centerCurr - yj)) := by
  -- Unfold the recursive definition at stage `j + 1`.
  simp [acceleratedMaxTypeEstimatingValue]

/-- Helper for Theorem 2.45: subtracting the base point `y_j` from the center recursion isolates
the transport term that later appears in the `φ_{j+1}^*` induction. -/
private theorem accelerated_max_type_estimating_center_succ_sub_eq
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1) -
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      =
      let gammaCurr :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          j
      let gammaNext :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          (j + 1)
      let yj :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let gj :=
        g_f[Q | problem.components; γL](yj)
      let αj :=
        acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      (1 / gammaNext) •
        (((1 - αj) * gammaCurr) •
            (acceleratedMaxTypeEstimatingCenter
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' j - yj) -
          αj • gj) := by
  let center :=
    acceleratedMaxTypeEstimatingCenter
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gamma : ℕ → ℝ :=
    estimatingSequenceCurvature μ γ0
      (acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
  let alpha : ℕ → ℝ :=
    acceleratedMaxTypeAlphaSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let ySeq :=
    acceleratedMaxTypeYSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gSeq : ℕ → E := fun k ↦ g_f[Q | problem.components; γL](ySeq k)
  let gammaCurr : ℝ := gamma j
  let gammaNext : ℝ := gamma (j + 1)
  let vCurr : E := center j
  let yj : E := ySeq j
  let gj : E := gSeq j
  have hgammaNext_ne : gammaNext ≠ 0 := by
    have hpos :=
      accelerated_max_type_estimating_curvature_pos'
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    simpa [gammaNext] using hpos.ne'
  have hyj : (1 / gammaNext) • (gammaNext • yj) = yj := by
    rw [smul_smul, one_div, inv_mul_cancel₀ hgammaNext_ne, one_smul]
  have hcurv :
      gammaNext = (1 - alpha j) * gammaCurr + alpha j * μ := by
    simpa [gammaCurr, gammaNext, alpha] using
      estimatingSequenceCurvature_succ μ γ0 alpha j
  -- Rewrite the center update relative to `y_j` and absorb the `y_j` coefficient with the
  -- curvature recursion.
  calc
    center (j + 1) - yj
        = (1 / gammaNext) •
            (((1 - alpha j) * gammaCurr) • vCurr + (alpha j * μ) • yj - alpha j • gj) - yj := by
              simpa [center, gammaCurr, gammaNext, vCurr, yj, gj, alpha, ySeq] using
                congrArg (fun z : E ↦ z - yj)
                  (acceleratedMaxTypeEstimatingCenter_succ
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' j)
    _ = (1 / gammaNext) •
          (((1 - alpha j) * gammaCurr) • vCurr + (alpha j * μ) • yj - alpha j • gj) -
          (1 / gammaNext) • (gammaNext • yj) := by rw [hyj]
    _ = (1 / gammaNext) •
          ((((1 - alpha j) * gammaCurr) • vCurr + (alpha j * μ) • yj - alpha j • gj) -
            gammaNext • yj) := by
            conv_rhs => rw [smul_sub]
    _ = (1 / gammaNext) •
          (((1 - alpha j) * gammaCurr) • (vCurr - yj) - alpha j • gj) := by
          congr 1
          change
            ((1 - alpha j) * gammaCurr) • vCurr + (alpha j * μ) • yj - alpha j • gj -
                (((1 - alpha j) * gammaCurr + alpha j * μ) • yj) =
              ((1 - alpha j) * gammaCurr) • (vCurr - yj) - alpha j • gj
          rw [add_smul, smul_sub]
          abel

/-- Helper for Theorem 2.45: after expanding the centered quadratic about `y_j`, the cross term
is exactly the transport combination needed in the successor canonical-quadratic identity. -/
private theorem accelerated_max_type_estimating_center_succ_cross_term_eq
    (hα0' : α0 ∈ αRange)
    (j : ℕ) (x : E) :
    let gammaCurr :=
      estimatingSequenceCurvature μ γ0
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        j
    let gammaNext :=
      estimatingSequenceCurvature μ γ0
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        (j + 1)
    let vCurr :=
      acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let vNext :=
      acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    let yj :=
      acceleratedMaxTypeYSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let gj := g_f[Q | problem.components; γL](yj)
    gammaNext * inner ℝ (x - yj) (yj - vNext) =
      (1 - acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j) *
        gammaCurr * inner ℝ (x - yj) (yj - vCurr) +
      acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j *
        inner ℝ gj (x - yj) := by
  let center :=
    acceleratedMaxTypeEstimatingCenter
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gamma : ℕ → ℝ :=
    estimatingSequenceCurvature μ γ0
      (acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
  let alpha : ℕ → ℝ :=
    acceleratedMaxTypeAlphaSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let ySeq :=
    acceleratedMaxTypeYSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gSeq : ℕ → E := fun k ↦ g_f[Q | problem.components; γL](ySeq k)
  let gammaCurr : ℝ := gamma j
  let gammaNext : ℝ := gamma (j + 1)
  let vCurr : E := center j
  let vNext : E := center (j + 1)
  let yj : E := ySeq j
  let gj : E := gSeq j
  have hgammaNext_ne : gammaNext ≠ 0 := by
    have hpos :=
      accelerated_max_type_estimating_curvature_pos'
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    simpa [gammaNext] using hpos.ne'
  have hsub :
      yj - vNext =
        (1 / gammaNext) •
          (((1 - alpha j) * gammaCurr) • (yj - vCurr) + alpha j • gj) := by
    calc
      yj - vNext = -(vNext - yj) := by abel
      _ = -((1 / gammaNext) • (((1 - alpha j) * gammaCurr) • (vCurr - yj) - alpha j • gj)) := by
            rw [accelerated_max_type_estimating_center_succ_sub_eq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' j]
      _ = (1 / gammaNext) •
            (((1 - alpha j) * gammaCurr) • (yj - vCurr) + alpha j • gj) := by
            simp [sub_eq_add_neg, add_comm]
  -- Move the reciprocal inside the inner product and clear the curvature denominator.
  calc
    gammaNext * inner ℝ (x - yj) (yj - vNext)
        = gammaNext * inner ℝ (x - yj)
            ((1 / gammaNext) • (((1 - alpha j) * gammaCurr) • (yj - vCurr) + alpha j • gj)) := by
              rw [hsub]
    _ =
        (1 - alpha j) * gammaCurr * inner ℝ (x - yj) (yj - vCurr) +
          alpha j * inner ℝ gj (x - yj) := by
            rw [real_inner_smul_right, inner_add_right, real_inner_smul_right,
              real_inner_smul_right, real_inner_comm (x - yj) gj]
            field_simp [hgammaNext_ne]

/-- Helper for Theorem 2.45: the shifted center norm at the next stage expands to the scalar
correction term used in the successor value recursion. -/
private theorem accelerated_max_type_estimating_center_succ_norm_sq_eq
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    let gammaCurr :=
      estimatingSequenceCurvature μ γ0
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        j
    let gammaNext :=
      estimatingSequenceCurvature μ γ0
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        (j + 1)
    let vCurr :=
      acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let vNext :=
      acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    let yj :=
      acceleratedMaxTypeYSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let gj := g_f[Q | problem.components; γL](yj)
    (gammaNext / 2) * ‖vNext - yj‖ ^ (2 : ℕ) =
      (((1 - acceleratedMaxTypeAlphaSeq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' j) ^
            (2 : ℕ) * gammaCurr ^ (2 : ℕ)) / (2 * gammaNext)) *
        ‖vCurr - yj‖ ^ (2 : ℕ) -
      (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j *
        (1 - acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j) * gammaCurr / gammaNext) *
        inner ℝ gj (vCurr - yj) +
      (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j ^ (2 : ℕ) / (2 * gammaNext)) *
        ‖gj‖ ^ (2 : ℕ) := by
  let center :=
    acceleratedMaxTypeEstimatingCenter
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gamma : ℕ → ℝ :=
    estimatingSequenceCurvature μ γ0
      (acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
  let alpha : ℕ → ℝ :=
    acceleratedMaxTypeAlphaSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let ySeq :=
    acceleratedMaxTypeYSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gSeq : ℕ → E := fun k ↦ g_f[Q | problem.components; γL](ySeq k)
  let gammaCurr : ℝ := gamma j
  let gammaNext : ℝ := gamma (j + 1)
  let vCurr : E := center j
  let vNext : E := center (j + 1)
  let yj : E := ySeq j
  let gj : E := gSeq j
  have hgammaNext_ne : gammaNext ≠ 0 := by
    have hpos :=
      accelerated_max_type_estimating_curvature_pos'
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    simpa [gammaNext] using hpos.ne'
  have hscaled :
      (gammaNext / 2) *
          ‖(1 / gammaNext) • (((1 - alpha j) * gammaCurr) • (vCurr - yj) - alpha j • gj)‖ ^
              (2 : ℕ) =
        (1 / (2 * gammaNext)) *
          ‖((1 - alpha j) * gammaCurr) • (vCurr - yj) - alpha j • gj‖ ^ (2 : ℕ) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp [hgammaNext_ne]
  have hexpand :
      ‖((1 - alpha j) * gammaCurr) • (vCurr - yj) - alpha j • gj‖ ^ (2 : ℕ) =
        ((1 - alpha j) * gammaCurr) ^ (2 : ℕ) * ‖vCurr - yj‖ ^ (2 : ℕ) -
          2 * ((1 - alpha j) * gammaCurr) * alpha j * inner ℝ (vCurr - yj) gj +
          alpha j ^ (2 : ℕ) * ‖gj‖ ^ (2 : ℕ) := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  calc
    (gammaNext / 2) * ‖vNext - yj‖ ^ (2 : ℕ)
        = (gammaNext / 2) *
            ‖(1 / gammaNext) • (((1 - alpha j) * gammaCurr) • (vCurr - yj) - alpha j • gj)‖ ^
              (2 : ℕ) := by
              simpa [gammaNext, gammaCurr, vCurr, vNext, yj, gj, center, ySeq] using
                congrArg (fun z : E ↦ (gammaNext / 2) * ‖z‖ ^ (2 : ℕ))
                  (accelerated_max_type_estimating_center_succ_sub_eq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' j)
    _ = (1 / (2 * gammaNext)) *
          ‖((1 - alpha j) * gammaCurr) • (vCurr - yj) - alpha j • gj‖ ^ (2 : ℕ) := hscaled
    _ =
        (((1 - alpha j) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ)) / (2 * gammaNext)) *
            ‖vCurr - yj‖ ^ (2 : ℕ) -
          (alpha j * (1 - alpha j) * gammaCurr / gammaNext) *
            inner ℝ gj (vCurr - yj) +
          (alpha j ^ (2 : ℕ) / (2 * gammaNext)) * ‖gj‖ ^ (2 : ℕ) := by
          rw [hexpand, real_inner_comm (vCurr - yj) gj]
          field_simp [hgammaNext_ne]

/-- Helper for Theorem 2.45: the theorem-local estimating sequence is the centered quadratic
`quadraticallyRegularizedObjective (fun _ ↦ φ_k^*) γ_k v_k`. -/
private theorem accelerated_max_type_estimating_function_eq_canonical_quadratic
    (hα0' : α0 ∈ αRange)
    (k : ℕ) :
    acceleratedMaxTypeEstimatingFunction
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' k =
      quadraticallyRegularizedObjective
        (fun _ : E ↦
          acceleratedMaxTypeEstimatingValue
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' k)
        (estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          k)
        (acceleratedMaxTypeEstimatingCenter
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' k) := by
  let center :=
    acceleratedMaxTypeEstimatingCenter
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let value :=
    acceleratedMaxTypeEstimatingValue
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let phi :=
    acceleratedMaxTypeEstimatingFunction
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gamma : ℕ → ℝ :=
    estimatingSequenceCurvature μ γ0
      (acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
  ext x
  induction k generalizing x with
  | zero =>
      -- At the base stage the local sequence is exactly the initial quadratic model.
      simp [phi, value, center, gamma, quadraticallyRegularizedObjective_apply,
        acceleratedMaxTypeEstimatingValue_zero, acceleratedMaxTypeEstimatingCenter_zero]
  | succ k hk =>
      let gammaCurr : ℝ := gamma k
      let gammaNext : ℝ := gamma (k + 1)
      let vCurr : E := center k
      let vNext : E := center (k + 1)
      let yk : E :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' k
      let gk : E := g_f[Q | problem.components; γL](yk)
      let xNext : E :=
        acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' (k + 1)
      let αk : ℝ :=
        acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' k
      have hrecx :
          phi (k + 1) x =
            (1 - acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k) *
                (value k + (gammaCurr / 2) * ‖x - vCurr‖ ^ (2 : ℕ)) +
              acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k *
                (fObj xNext +
                  (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) +
                  inner ℝ gk (x - yk) +
                  (μ / 2) * ‖x - yk‖ ^ (2 : ℕ)) := by
        calc
          phi (k + 1) x =
              (1 - acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k) *
                  phi k x +
                acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k *
                  acceleratedMaxTypeEstimatingModel
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k x := by
                simpa [phi] using
                  (acceleratedMaxTypeEstimatingFunction_succ_apply
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k x)
          _ =
              (1 - acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k) *
                  quadraticallyRegularizedObjective (fun _ : E ↦ value k) (gamma k) (center k) x +
                acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k *
                  acceleratedMaxTypeEstimatingModel
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k x := by
                have hk' :
                    phi k x =
                      quadraticallyRegularizedObjective (fun _ : E ↦ value k) (gamma k) (center k) x := by
                  simpa [phi, value, center, gamma] using hk x
                rw [hk']
          _ =
              (1 - acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k) *
                  (value k + (gammaCurr / 2) * ‖x - vCurr‖ ^ (2 : ℕ)) +
                acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k *
                  acceleratedMaxTypeEstimatingModel
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k x := by
                simp [quadraticallyRegularizedObjective_apply, gammaCurr, vCurr]
          _ =
              (1 - acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k) *
                  (value k + (gammaCurr / 2) * ‖x - vCurr‖ ^ (2 : ℕ)) +
                acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k *
                  (fObj xNext + (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) +
                    inner ℝ gk (x - yk) + (μ / 2) * ‖x - yk‖ ^ (2 : ℕ)) := by
                have hmodel :
                    acceleratedMaxTypeEstimatingModel
                        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                        (x0 := x0) (α0 := α0) hα0' k x =
                      fObj xNext + (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) +
                        inner ℝ gk (x - yk) + (μ / 2) * ‖x - yk‖ ^ (2 : ℕ) := by
                  simpa [xNext, gk, yk, add_assoc, add_left_comm, add_comm] using
                    (acceleratedMaxTypeEstimatingModel_apply
                      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                      (x0 := x0) (α0 := α0) hα0' k x)
                rw [hmodel]
      have hgammaNext_ne : gammaNext ≠ 0 := by
        have hpos :=
          accelerated_max_type_estimating_curvature_pos'
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' (k + 1)
        simpa [gammaNext] using hpos.ne'
      have hcurv :
          gammaNext =
            (1 - acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k) *
                gammaCurr +
              acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k * μ := by
        simpa [gammaCurr, gammaNext] using
          estimatingSequenceCurvature_succ μ γ0
            (acceleratedMaxTypeAlphaSeq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0')
            k
      have hvalue :
          value (k + 1) =
            (1 - acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k) *
                value k +
              acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k *
                fObj xNext +
              (acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k / (2 * L) -
                acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k ^ (2 : ℕ) / (2 * gammaNext)) *
                ‖gk‖ ^ (2 : ℕ) +
              (acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k *
                (1 - acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k) * gammaCurr / gammaNext) *
                ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) := by
        simpa [value, gammaCurr, gammaNext, vCurr, yk, gk, xNext] using
          acceleratedMaxTypeEstimatingValue_succ
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' k
      have hcross :
          gammaNext * inner ℝ (x - yk) (yk - vNext) =
            (1 - acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k) *
                gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
              acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k *
                inner ℝ gk (x - yk) := by
        simpa [gammaCurr, gammaNext, vCurr, vNext, yk, gk] using
          accelerated_max_type_estimating_center_succ_cross_term_eq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' k x
      have hnorm :
          (gammaNext / 2) * ‖yk - vNext‖ ^ (2 : ℕ) =
            (((1 - acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k) ^
                  (2 : ℕ) * gammaCurr ^ (2 : ℕ)) / (2 * gammaNext)) *
                ‖vCurr - yk‖ ^ (2 : ℕ) -
              (acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k *
                (1 - acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0' k) *
                gammaCurr / gammaNext) *
                inner ℝ gk (vCurr - yk) +
              (acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' k ^ (2 : ℕ) / (2 * gammaNext)) *
                ‖gk‖ ^ (2 : ℕ) := by
        simpa [gammaCurr, gammaNext, vCurr, vNext, yk, gk, norm_sub_rev] using
          accelerated_max_type_estimating_center_succ_norm_sq_eq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' k
      change
        phi (k + 1) x =
          value (k + 1) + (gammaNext / 2) * ‖(x - vNext : E)‖ ^ (2 : ℕ)
      rw [hrecx, hvalue,
        centered_quadratic_expand_about_point gammaCurr x yk vCurr,
        centered_quadratic_expand_about_point gammaNext x yk vNext, hcross, hnorm]
      let commonForm :=
        (1 - αk) * value k +
          αk * fObj xNext +
          (1 - αk) * (gammaCurr / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) +
          ((1 - αk) * gammaCurr) * inner ℝ (x - yk) (yk - vCurr) +
          ((1 - αk) * (gammaCurr / 2) + αk * (μ / 2)) * ‖x - yk‖ ^ (2 : ℕ) +
          αk * inner ℝ gk (x - yk)
      have hconstCoeff :
          αk * (1 - αk) * gammaCurr / gammaNext * (μ / 2) +
            (1 - αk) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext) =
              (1 - αk) * (gammaCurr / 2) := by
        field_simp [hgammaNext_ne]
        rw [hcurv]
        ring
      have hxCoeff :
          gammaNext / 2 = (1 - αk) * (gammaCurr / 2) + αk * (μ / 2) := by
        nlinarith [hcurv]
      have hleft :
          (1 - αk) *
              (value k +
                (gammaCurr / 2 * ‖yk - vCurr‖ ^ (2 : ℕ) +
                  gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                  gammaCurr / 2 * ‖x - yk‖ ^ (2 : ℕ))) +
            αk *
              (fObj xNext + 1 / (2 * L) * ‖gk‖ ^ (2 : ℕ) +
                inner ℝ gk (x - yk) + μ / 2 * ‖x - yk‖ ^ (2 : ℕ)) =
            commonForm + αk * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) := by
        simp [commonForm]
        ring
      have hright :
          (1 - αk) * value k +
              αk * fObj xNext +
              (αk / (2 * L) - αk ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
              αk * (1 - αk) * gammaCurr / gammaNext *
                ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) +
            (((1 - αk) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext)) *
                  ‖vCurr - yk‖ ^ (2 : ℕ) -
                αk * (1 - αk) * gammaCurr / gammaNext * inner ℝ gk (vCurr - yk) +
                αk ^ (2 : ℕ) / (2 * gammaNext) * ‖gk‖ ^ (2 : ℕ) +
              ((1 - αk) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                αk * inner ℝ gk (x - yk)) +
              gammaNext / 2 * ‖x - yk‖ ^ (2 : ℕ)) =
            commonForm + αk * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) := by
        calc
          (1 - αk) * value k +
                αk * fObj xNext +
                (αk / (2 * L) - αk ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
                αk * (1 - αk) * gammaCurr / gammaNext *
                  ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) +
              (((1 - αk) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext)) *
                    ‖vCurr - yk‖ ^ (2 : ℕ) -
                  αk * (1 - αk) * gammaCurr / gammaNext * inner ℝ gk (vCurr - yk) +
                  αk ^ (2 : ℕ) / (2 * gammaNext) * ‖gk‖ ^ (2 : ℕ) +
                ((1 - αk) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                  αk * inner ℝ gk (x - yk)) +
                gammaNext / 2 * ‖x - yk‖ ^ (2 : ℕ))
              =
              (1 - αk) * value k +
                αk * fObj xNext +
                αk * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) +
                (αk * (1 - αk) * gammaCurr / gammaNext * (μ / 2) +
                    (1 - αk) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext)) *
                  ‖yk - vCurr‖ ^ (2 : ℕ) +
                ((1 - αk) * gammaCurr) * inner ℝ (x - yk) (yk - vCurr) +
                (gammaNext / 2) * ‖x - yk‖ ^ (2 : ℕ) +
                αk * inner ℝ gk (x - yk) := by
                  simp [norm_sub_rev]
                  ring
          _ = commonForm + αk * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) := by
            rw [hconstCoeff, hxCoeff]
            simp [commonForm]
            ring
      -- Match the constant, linear, and quadratic coefficients after the recentering identity.
      simpa [quadraticallyRegularizedObjective_apply, gammaCurr, gammaNext, vCurr, vNext, yk, gk,
        xNext, αk] using hleft.trans hright.symm

/-- Helper for Theorem 2.45: every theorem-local estimating function attains the value
`φ_k^*` as its minimum. -/
private theorem accelerated_max_type_estimating_min_value
    (hα0' : α0 ∈ αRange)
    (k : ℕ) :
    IsLeast
      (Set.range
        (acceleratedMaxTypeEstimatingFunction
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' k))
      (acceleratedMaxTypeEstimatingValue
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' k) := by
  have hcurv_pos :
      0 <
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          k :=
    accelerated_max_type_estimating_curvature_pos'
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' k
  -- Re-express the stage function as a canonical quadratic and use the generic minimum-value
  -- theorem for centered quadratics.
  simpa [accelerated_max_type_estimating_function_eq_canonical_quadratic
    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
    (x0 := x0) (α0 := α0) hα0' k] using
    canonical_quadratic_isLeast_value
      (E := E)
      (γ := estimatingSequenceCurvature μ γ0
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        k)
      (c := acceleratedMaxTypeEstimatingValue
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' k)
      (v := acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' k)
      hcurv_pos

/-- Helper for Theorem 2.45: the exact proximal-gradient step at stage `j` yields the textbook
lower affine-quadratic bound on the max-type objective. -/
private lemma accelerated_max_type_exact_step_objective_lower_bound
    (hα0' : α0 ∈ αRange)
    (j : ℕ) (x : E) :
    fObj x ≥
      fObj (acceleratedMaxTypeXSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)) +
        inner ℝ
          (g_f[Q | problem.components; γL]
            (acceleratedMaxTypeYSeq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' j))
          (x - acceleratedMaxTypeYSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j) +
        (1 / (2 * L)) *
          ‖g_f[Q | problem.components; γL]
              (acceleratedMaxTypeYSeq
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j)‖ ^ (2 : ℕ) +
        (μ / 2) * ‖x -
          acceleratedMaxTypeYSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j‖ ^ (2 : ℕ) := by
  let yj :=
    acceleratedMaxTypeYSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let xPlus :=
    acceleratedMaxTypeXSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' (j + 1)
  let modelγ :=
    quadraticallyRegularizedObjective (problem.affineApproximation yj) L yj
  let g :=
    g_f[Q | problem.components; γL](yj)
  let correction := (1 / (2 * (γL : ℝ))) * ‖g‖ ^ (2 : ℕ)
  have hx : x ∈ Q := by
    simp [hfeasible_univ]
  have hxPlus_mem : xPlus ∈ Q := by
    -- The chosen exact step always lies in the feasible set.
    simpa [xPlus, yj, acceleratedMaxTypeXSeq, acceleratedMaxTypeYSeq] using
      (maxTypeGradientMapping_mem_and_isMinOn_ofFact Q problem.components yj γL).1
  have hxPlus_isMinOn :
      IsMinOn modelγ Q xPlus := by
    -- The Algorithm 2.9 exact step is already the owner minimizer of the regularized affine model.
    simpa [modelγ, xPlus, yj, acceleratedMaxTypeXSeq, acceleratedMaxTypeYSeq,
      Real.toNNReal_of_nonneg hL.le] using
      constantStepSchemeIIMinimaxX_succ_isMinOn
        problem hL x0Q (Subtype.mk α0 hα0') j
  have hlower :
      quadraticallyRegularizedObjective (problem.affineApproximation yj) μ yj x ≤ fObj x := by
    -- The componentwise `𝓢^{1,1}` bounds give the global lower quadratic model at `y_j`.
    simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation, yj,
      ge_iff_le] using
      (maxTypeObjective_quadratic_bounds_of_components_mem
        problem.components μ L problem.components_mem x yj).1
  have hupper :
      fObj xPlus ≤ modelγ xPlus := by
    -- Evaluating the upper tangent model at the exact step gives the `L`-regularized upper bound.
    simpa [modelγ, quadraticallyRegularizedObjective_apply,
      SmoothMinimaxProblem.affineApproximation, yj, xPlus] using
      (maxTypeObjective_quadratic_bounds_of_components_mem
        problem.components μ L problem.components_mem xPlus yj).2
  have hγL_eq : (γL : ℝ) = L := by
    change ((Real.toNNReal L : NNReal) : ℝ) = L
    simp [Real.toNNReal_of_nonneg hL.le]
  have hstrong :
      StrongConvexOn Set.univ L modelγ := by
    -- The affine max-type model plus a positive quadratic term is strongly convex on the ambient
    -- space.
    simpa [modelγ, yj, SmoothMinimaxProblem.affineApproximation, hγL_eq] using
      regularizedMaxTypeObjective_strongConvexOn_univ problem.components yj γL
  have hstrong_feasible :
      StrongConvexOn Q L modelγ := by
    -- Restrict the ambient strong-convexity owner to the feasible set `Q`.
    rw [strongConvexOn_iff_convex] at hstrong ⊢
    exact hstrong.subset (by simp) problem.feasible_convex
  have hgrowth :
      modelγ x ≥ modelγ xPlus + (L / 2) * ‖x - xPlus‖ ^ (2 : ℕ) :=
    hstrong_feasible.quadratic_growth_of_isMinOn_of_mem hxPlus_mem hxPlus_isMinOn x hx
  have hgrad :
      g = (γL : ℝ) • (yj - xPlus) := by
    simpa [g, yj, xPlus, acceleratedMaxTypeXSeq, acceleratedMaxTypeYSeq,
      Real.toNNReal_of_nonneg hL.le] using
      accelerated_max_type_reduced_gradient_eq_smul_sub
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
  have hmodel :
      fObj xPlus + (L / 2) * ‖x - xPlus‖ ^ (2 : ℕ) =
        quadraticallyRegularizedObjective
          (affineModelAt (fun _ : E ↦ fObj xPlus + correction) (fun _ ↦ g) yj)
          (γL : ℝ)
          yj
          x := by
    have hcompleted :=
      quadraticallyRegularizedObjective_affineModelAt_eq_completedSquare
        (fun _ : E ↦ fObj xPlus + correction) g yj x γL
    have hγ : (γL : ℝ) ≠ 0 := by
      exact (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γL))).ne'
    have hxPlus_eq : yj - ((γL : ℝ)⁻¹) • g = xPlus := by
      calc
        yj - ((γL : ℝ)⁻¹) • g
            = yj - ((γL : ℝ)⁻¹) • ((γL : ℝ) • (yj - xPlus)) := by rw [hgrad]
        _ = yj - (yj - xPlus) := by rw [smul_smul, inv_mul_cancel₀ hγ, one_smul]
        _ = xPlus := by abel
    rw [hcompleted, hxPlus_eq]
    simp only [correction]
    rw [hγL_eq]
    ring
  -- Chain the lower quadratic model, quadratic growth from the exact-step minimizer, and the
  -- completed-square expansion.
  calc
    fObj x ≥ quadraticallyRegularizedObjective (problem.affineApproximation yj) μ yj x := hlower
    _ = modelγ x - ((γL : ℝ) / 2) * ‖x - yj‖ ^ (2 : ℕ) + (μ / 2) * ‖x - yj‖ ^ (2 : ℕ) := by
          simp [modelγ, quadraticallyRegularizedObjective_apply, yj,
            Real.toNNReal_of_nonneg hL.le]
    _ ≥ modelγ xPlus + (L / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          ((γL : ℝ) / 2) * ‖x - yj‖ ^ (2 : ℕ) + (μ / 2) * ‖x - yj‖ ^ (2 : ℕ) := by
          nlinarith [hgrowth]
    _ ≥ fObj xPlus + (L / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          ((γL : ℝ) / 2) * ‖x - yj‖ ^ (2 : ℕ) + (μ / 2) * ‖x - yj‖ ^ (2 : ℕ) := by
          gcongr
    _ =
        (quadraticallyRegularizedObjective
            (affineModelAt (fun _ : E ↦ fObj xPlus + correction) (fun _ ↦ g) yj)
            (γL : ℝ)
            yj
            x) -
          ((γL : ℝ) / 2) * ‖x - yj‖ ^ (2 : ℕ) +
          (μ / 2) * ‖x - yj‖ ^ (2 : ℕ) := by
            rw [← hmodel]
    _ =
        fObj xPlus + inner ℝ g (x - yj) + correction + (μ / 2) * ‖x - yj‖ ^ (2 : ℕ) := by
          simp [quadraticallyRegularizedObjective_apply, affineModelAt_apply]
          ring
    _ =
        fObj xPlus +
          inner ℝ
            (g_f[Q | problem.components; γL](yj))
            (x - yj) +
          (1 / (2 * L)) * ‖g_f[Q | problem.components; γL](yj)‖ ^ (2 : ℕ) +
          (μ / 2) * ‖x - yj‖ ^ (2 : ℕ) := by
            simp [g, correction, Real.toNNReal_of_nonneg hL.le]

/-- Helper for Theorem 2.45: every stage of the theorem-local max-type lower model is dominated
pointwise by the objective. -/
private lemma accelerated_max_type_estimating_model_le_objective
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    acceleratedMaxTypeEstimatingModel
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j ≤ fObj := by
  intro x
  -- Reuse the exact-step lower bound as the pointwise domination needed in the estimate sequence.
  simpa [acceleratedMaxTypeEstimatingModel] using
    accelerated_max_type_exact_step_objective_lower_bound
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j x

/-- Helper for Theorem 2.45: every curvature generated by the local estimating-sequence scalar
recurrence is strictly positive. -/
private lemma accelerated_max_type_estimating_curvature_pos
    (hα0' : α0 ∈ αRange) :
    ∀ j : ℕ,
      0 <
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          j
  | 0 => by
      -- The initial curvature is positive because the admissible `α₀` interval gives `γ₀ > μ > 0`.
      have hγ0 :
          γ0 ∈ Set.Ioc μ (3 * L + μ) :=
        accelerated_max_type_gamma0_mem_Ioc
          (problem := problem) (hL := hL) (α0 := α0) (hα0 := hα0')
      have hμ : 0 < μ := by
        classical
        let i : ι := Classical.choice inferInstance
        exact (mem_S11_iff.mp (problem.components_mem i)).mu_pos
      exact lt_trans hμ hγ0.1
  | j + 1 => by
      -- For successor stages, the owner curvature identity is `γ_{j+1} = L α_j²`.
      have hcurv :
          estimatingSequenceCurvature μ γ0
              (acceleratedMaxTypeAlphaSeq
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0')
              (j + 1) =
            L *
              (acceleratedMaxTypeAlphaSeq
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j) ^ (2 : ℕ) := by
        simpa [acceleratedMaxTypeAlphaSeq] using
          accelerated_max_type_estimating_curvature_succ_eq_L_mul_sq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j
      rw [hcurv]
      have hα :
          0 <
            acceleratedMaxTypeAlphaSeq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' j := by
        simpa [acceleratedMaxTypeAlphaSeq] using
          (constantStepSchemeIIMinimaxAlpha_mem_Ioo
            problem hL x0Q (Subtype.mk α0 hα0') j).1
      positivity

/-- Helper for Theorem 2.45: the theorem-local estimating sequence stays below the canonical
affine upper model `lineMap fObj (φ₀) λ_k`. -/
private lemma accelerated_max_type_estimating_function_upper_bound
    (hα0' : α0 ∈ αRange) :
    ∀ j : ℕ,
      acceleratedMaxTypeEstimatingFunction
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j ≤
        lineMap
          fObj
          (acceleratedMaxTypeEstimatingFunction
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' 0)
          (estimatingWeight
            (acceleratedMaxTypeAlphaSeq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0')
            j)
  | 0 => by
      -- At stage zero, the affine upper model is exact because `λ₀ = 1`.
      simpa [estimatingWeight, lineMap_apply_module]
  | j + 1 => by
      intro x
      have ih :=
        accelerated_max_type_estimating_function_upper_bound
          (hα0' := hα0') j x
      have hmodel :=
        accelerated_max_type_estimating_model_le_objective
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j x
      have hα_mem :
          acceleratedMaxTypeAlphaSeq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' j ∈ Set.Ico (0 : ℝ) 1 := by
        simpa [acceleratedMaxTypeAlphaSeq] using
          constantStepSchemeIIMinimaxAlpha_mem_Ico
            problem hL x0Q (Subtype.mk α0 hα0') j
      have hα_nonneg :
          0 ≤
            acceleratedMaxTypeAlphaSeq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' j :=
        hα_mem.1
      have hone_minus_nonneg :
          0 ≤
            1 - acceleratedMaxTypeAlphaSeq
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' j := by
        exact sub_nonneg.mpr hα_mem.2.le
      -- Insert the stagewise lower-model domination into the affine recursion.
      calc
        acceleratedMaxTypeEstimatingFunction
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' (j + 1) x
            =
          (1 - acceleratedMaxTypeAlphaSeq
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j) *
              acceleratedMaxTypeEstimatingFunction
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j x +
            acceleratedMaxTypeAlphaSeq
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j *
              acceleratedMaxTypeEstimatingModel
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j x := by
              rw [acceleratedMaxTypeEstimatingFunction_succ_apply
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j x]
        _ ≤
          (1 - acceleratedMaxTypeAlphaSeq
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j) *
              lineMap
                fObj
                (acceleratedMaxTypeEstimatingFunction
                  (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                  (x0 := x0) (α0 := α0) hα0' 0)
                (estimatingWeight
                  (acceleratedMaxTypeAlphaSeq
                    (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                    (x0 := x0) (α0 := α0) hα0')
                  j)
                x +
            acceleratedMaxTypeAlphaSeq
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j *
              fObj x := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left ih hone_minus_nonneg)
                (mul_le_mul_of_nonneg_left hmodel hα_nonneg)
        _ =
          lineMap
            fObj
            (acceleratedMaxTypeEstimatingFunction
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' 0)
            (estimatingWeight
              (acceleratedMaxTypeAlphaSeq
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0')
              (j + 1))
            x := by
              simp [estimatingWeight, lineMap_apply_module]

              ring

/-- Helper for Theorem 2.45: rewriting the successor center recursion at the common basepoint
`y_j` converts the new center gap into the old iterate gap and the fresh exact-step gap. -/
private lemma accelerated_max_type_estimating_center_succ_at_basepoint
    (hα0' : α0 ∈ αRange) {j : ℕ}
    (hcenter :
      let gammaCurr :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          j
      let gammaNext :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          (j + 1)
      let αj :=
        acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let vj :=
        acceleratedMaxTypeEstimatingCenter
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let yj :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let xj :=
        acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      vj - yj = (gammaNext / (αj * gammaCurr)) • (yj - xj)) :
    let αj :=
      acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let xj :=
      acceleratedMaxTypeXSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let xj1 :=
      acceleratedMaxTypeXSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    let yj :=
      acceleratedMaxTypeYSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let vj1 :=
      acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    vj1 - yj = (((1 - αj) / αj) : ℝ) • (yj - xj) - (1 / αj : ℝ) • (yj - xj1) := by
  let alphaSeq :=
    acceleratedMaxTypeAlphaSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gamma : ℕ → ℝ := estimatingSequenceCurvature μ γ0 alphaSeq
  let αj : ℝ := alphaSeq j
  let γj : ℝ := gamma j
  let γj1 : ℝ := gamma (j + 1)
  let vj :=
    acceleratedMaxTypeEstimatingCenter
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let vj1 :=
    acceleratedMaxTypeEstimatingCenter
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' (j + 1)
  let yj :=
    acceleratedMaxTypeYSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let xj :=
    acceleratedMaxTypeXSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let xj1 :=
    acceleratedMaxTypeXSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' (j + 1)
  let gj : E := g_f[Q | problem.components; γL](yj)
  have hαj_pos : 0 < αj := by
    simpa [alphaSeq, αj, acceleratedMaxTypeAlphaSeq] using
      (constantStepSchemeIIMinimaxAlpha_mem_Ioo
        problem hL x0Q (Subtype.mk α0 hα0') j).1
  have hγj_pos : 0 < γj := by
    simpa [gamma, γj] using
      accelerated_max_type_estimating_curvature_pos'
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
  have hγj1_pos : 0 < γj1 := by
    simpa [gamma, γj1] using
      accelerated_max_type_estimating_curvature_pos'
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
  have hcenter' : vj - yj = (γj1 / (αj * γj)) • (yj - xj) := by
    simpa [alphaSeq, gamma, αj, γj, γj1, vj, yj, xj] using hcenter
  have hcenter_sub :
      vj1 - yj = (1 / γj1) • (((1 - αj) * γj) • (vj - yj) - αj • gj) := by
    simpa [alphaSeq, gamma, αj, γj, γj1, vj, vj1, yj, gj] using
      accelerated_max_type_estimating_center_succ_sub_eq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
  have hgrad : gj = L • (yj - xj1) := by
    simpa [alphaSeq, xj1, yj, gj] using
      accelerated_max_type_reduced_gradient_eq_smul_sub
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
  have hγj1 :
      γj1 = L * αj ^ (2 : ℕ) := by
    simpa [alphaSeq, gamma, αj, γj1] using
      accelerated_max_type_estimating_curvature_succ_eq_L_mul_sq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
  -- Route correction: first normalize the center recursion at `y_j`, then use the exact-step
  -- identity `g_j = L • (y_j - x_{j+1})`.
  calc
    vj1 - yj = (1 / γj1) • (((1 - αj) * γj) • (vj - yj) - αj • gj) := hcenter_sub
    _ = (1 / γj1) • (((1 - αj) * γj) • ((γj1 / (αj * γj)) • (yj - xj)) - αj • gj) := by
          rw [hcenter']
    _ = (1 / γj1) •
          ((((1 - αj) * γj) * (γj1 / (αj * γj))) • (yj - xj) - αj • gj) := by
          rw [smul_smul]
    _ = (((1 - αj) / αj) : ℝ) • (yj - xj) - (αj / γj1 : ℝ) • gj := by
          rw [smul_sub, smul_smul, smul_smul]
          have hcoef1 :
              ((1 / γj1 : ℝ) * (((1 - αj) * γj) * (γj1 / (αj * γj)))) = (1 - αj) / αj := by
            field_simp [hαj_pos.ne', hγj_pos.ne', hγj1_pos.ne']
          have hcoef2 : ((1 / γj1 : ℝ) * αj) = αj / γj1 := by
            ring
          rw [hcoef1, hcoef2]
    _ = (((1 - αj) / αj) : ℝ) • (yj - xj) - ((αj * L) / γj1 : ℝ) • (yj - xj1) := by
          rw [hgrad, smul_smul]
          congr 2
          ring
    _ = (((1 - αj) / αj) : ℝ) • (yj - xj) - (1 / αj : ℝ) • (yj - xj1) := by
          have hcoef3 : ((αj * L) / γj1 : ℝ) = 1 / αj := by
            rw [hγj1]
            field_simp [hL.ne', hαj_pos.ne']
          rw [hcoef3]

/-- Helper for Theorem 2.45: the normalized successor coefficient is exactly the next transport
factor times the textbook momentum coefficient `β_j`. -/
private lemma accelerated_max_type_normalized_center_coeff_eq_transport_coeff
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    let αj :=
      acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let αj1 :=
      acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    let gammaNext :=
      estimatingSequenceCurvature μ γ0
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        (j + 1)
    let gammaNextNext :=
      estimatingSequenceCurvature μ γ0
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        (j + 2)
    let βj := (αj * (1 - αj)) / (αj ^ (2 : ℕ) + αj1)
    ((((1 - αj) / αj) - βj) : ℝ) = (gammaNextNext / (αj1 * gammaNext)) * βj := by
  let alphaSeq :=
    acceleratedMaxTypeAlphaSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gamma : ℕ → ℝ := estimatingSequenceCurvature μ γ0 alphaSeq
  let αj : ℝ := alphaSeq j
  let αj1 : ℝ := alphaSeq (j + 1)
  let γj1 : ℝ := gamma (j + 1)
  let γj2 : ℝ := gamma (j + 2)
  let βj : ℝ := (αj * (1 - αj)) / (αj ^ (2 : ℕ) + αj1)
  have hαj_pos : 0 < αj := by
    simpa [alphaSeq, αj, acceleratedMaxTypeAlphaSeq] using
      (constantStepSchemeIIMinimaxAlpha_mem_Ioo
        problem hL x0Q (Subtype.mk α0 hα0') j).1
  have hαj1_pos : 0 < αj1 := by
    simpa [alphaSeq, αj1, acceleratedMaxTypeAlphaSeq] using
      (constantStepSchemeIIMinimaxAlpha_mem_Ioo
        problem hL x0Q (Subtype.mk α0 hα0') (j + 1)).1
  have hγj1 :
      γj1 = L * αj ^ (2 : ℕ) := by
    simpa [alphaSeq, gamma, αj, γj1] using
      accelerated_max_type_estimating_curvature_succ_eq_L_mul_sq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
  have hγj2 :
      γj2 = L * αj1 ^ (2 : ℕ) := by
    simpa [alphaSeq, gamma, αj1, γj2] using
      accelerated_max_type_estimating_curvature_succ_eq_L_mul_sq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
  have hden_ne : αj ^ (2 : ℕ) + αj1 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hαj_pos.ne', hαj1_pos]
  -- Rewrite both transport factors through `γ_{m+1} = L α_m²`, then reduce to a scalar identity.
  simpa [alphaSeq, gamma, αj, αj1, γj1, γj2, βj] using
    (show ((((1 - αj) / αj) - βj) : ℝ) = (γj2 / (αj1 * γj1)) * βj by
      dsimp [βj]
      rw [hγj1, hγj2]
      field_simp [hL.ne', hαj_pos.ne', hαj1_pos.ne', hden_ne]
      ring)

private lemma accelerated_max_type_estimating_center_succ_normalized
    (hα0' : α0 ∈ αRange) {j : ℕ}
    (hcenter :
      let gammaCurr :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          j
      let gammaNext :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          (j + 1)
      let αj :=
        acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let vj :=
        acceleratedMaxTypeEstimatingCenter
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let yj :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let xj :=
        acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      vj - yj = (gammaNext / (αj * gammaCurr)) • (yj - xj)) :
    let αj :=
      acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let αj1 :=
      acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    let xj :=
      acceleratedMaxTypeXSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let xj1 :=
      acceleratedMaxTypeXSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    let yj :=
      acceleratedMaxTypeYSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let yj1 :=
      acceleratedMaxTypeYSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    let vj1 :=
      acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
    let βj := (αj * (1 - αj)) / (αj ^ (2 : ℕ) + αj1)
    vj1 - yj1 = ((((1 - αj) / αj) - βj) : ℝ) • (xj1 - xj) := by
  let alphaSeq :=
    acceleratedMaxTypeAlphaSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let αj : ℝ := alphaSeq j
  let αj1 : ℝ := alphaSeq (j + 1)
  let xj :=
    acceleratedMaxTypeXSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let xj1 :=
    acceleratedMaxTypeXSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' (j + 1)
  let yj :=
    acceleratedMaxTypeYSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let yj1 :=
    acceleratedMaxTypeYSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' (j + 1)
  let vj1 :=
    acceleratedMaxTypeEstimatingCenter
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' (j + 1)
  let βj : ℝ := (αj * (1 - αj)) / (αj ^ (2 : ℕ) + αj1)
  have hαj_pos : 0 < αj := by
    simpa [alphaSeq, αj, acceleratedMaxTypeAlphaSeq] using
      (constantStepSchemeIIMinimaxAlpha_mem_Ioo
        problem hL x0Q (Subtype.mk α0 hα0') j).1
  have hcenter_base :
      vj1 - yj =
        (((1 - αj) / αj) : ℝ) • (yj - xj) - (1 / αj : ℝ) • (yj - xj1) := by
    simpa [alphaSeq, αj, xj, xj1, yj, vj1] using
      accelerated_max_type_estimating_center_succ_at_basepoint
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' hcenter
  have hyj1 :
      yj1 = xj1 + βj • (xj1 - xj) := by
    change
      constantStepSchemeIIMinimaxY problem hL x0Q (Subtype.mk α0 hα0') (j + 1) =
        (constantStepSchemeIIMinimaxX problem hL x0Q (Subtype.mk α0 hα0') (j + 1) : E) +
          ((constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0') j *
                (1 - constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0') j)) /
              (constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0') j ^ (2 : ℕ) +
                constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0') (j + 1))) •
            ((constantStepSchemeIIMinimaxX problem hL x0Q (Subtype.mk α0 hα0') (j + 1) : E) -
              (constantStepSchemeIIMinimaxX problem hL x0Q (Subtype.mk α0 hα0') j : E))
    exact
      constantStepSchemeIIMinimaxY_succ
        problem hL x0Q (Subtype.mk α0 hα0') j
  have hydecomp :
      yj - xj = (yj - xj1) + (xj1 - xj) := by
    abel
  have hysucc :
      yj1 - yj = -(yj - xj1) + βj • (xj1 - xj) := by
    calc
      yj1 - yj = (xj1 + βj • (xj1 - xj)) - yj := by
            rw [hyj1]
      _ = -(yj - xj1) + βj • (xj1 - xj) := by
            abel
  -- Subtract the momentum update `y_{j+1} - y_j` after first normalizing at the common basepoint
  -- `y_j`.
  calc
    vj1 - yj1 = (vj1 - yj) - (yj1 - yj) := by
      abel
    _ =
        ((((1 - αj) / αj) : ℝ) • ((yj - xj1) + (xj1 - xj)) -
            (1 / αj : ℝ) • (yj - xj1)) -
          (-(yj - xj1) + βj • (xj1 - xj)) := by
          rw [hcenter_base, hydecomp, hysucc]
    _ = ((((1 - αj) / αj) - βj) : ℝ) • (xj1 - xj) := by
          let u : E := yj - xj1
          let v : E := xj1 - xj
          have hcancel : ((((1 - αj) / αj : ℝ) - 1 / αj + 1) : ℝ) = 0 := by
            field_simp [hαj_pos.ne']
            ring
          change ((((1 - αj) / αj) : ℝ) • (u + v) - (1 / αj : ℝ) • u) - (-u + βj • v) =
            ((((1 - αj) / αj) - βj) : ℝ) • v
          calc
            ((((1 - αj) / αj) : ℝ) • (u + v) - (1 / αj : ℝ) • u) - (-u + βj • v)
                = ((((1 - αj) / αj) - 1 / αj + 1) : ℝ) • u +
                    ((((1 - αj) / αj) - βj) : ℝ) • v := by
                      module
            _ = ((((1 - αj) / αj) - βj) : ℝ) • v := by
                  rw [hcancel, zero_smul, zero_add]

/-- Helper for Theorem 2.45: the theorem-local estimating center differs from `y_j` by the
scaled iterate gap `(γ_{j+1} / (α_j γ_j)) (y_j - x_j)`. -/
private lemma accelerated_max_type_estimating_center_sub_eq_iterate_gap
    (hα0' : α0 ∈ αRange) :
    ∀ j : ℕ,
      let gammaCurr :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          j
      let gammaNext :=
        estimatingSequenceCurvature μ γ0
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          (j + 1)
      let αj :=
        acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let vj :=
        acceleratedMaxTypeEstimatingCenter
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let yj :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let xj :=
        acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      vj - yj = (gammaNext / (αj * gammaCurr)) • (yj - xj)
  | 0 => by
      -- At time zero, both the center and the extrapolated point equal the initial iterate.
      simp [acceleratedMaxTypeEstimatingCenter_zero, acceleratedMaxTypeYSeq, acceleratedMaxTypeXSeq]
  | Nat.succ j => by
      have ih :=
        accelerated_max_type_estimating_center_sub_eq_iterate_gap
          (hα0' := hα0') j
      let alphaSeq :=
        acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0'
      let gamma : ℕ → ℝ := estimatingSequenceCurvature μ γ0 alphaSeq
      let αj : ℝ := alphaSeq j
      let αj1 : ℝ := alphaSeq (j + 1)
      let γj1 : ℝ := gamma (j + 1)
      let γj2 : ℝ := gamma (j + 2)
      let xj :=
        acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      let xj1 :=
        acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' (j + 1)
      let yj1 :=
        acceleratedMaxTypeYSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' (j + 1)
      let vj1 :=
        acceleratedMaxTypeEstimatingCenter
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' (j + 1)
      let βj : ℝ := (αj * (1 - αj)) / (αj ^ (2 : ℕ) + αj1)
      have hnormalized :
          vj1 - yj1 = ((((1 - αj) / αj) - βj) : ℝ) • (xj1 - xj) := by
        simpa [alphaSeq, gamma, αj, αj1, xj, xj1, yj1, vj1, βj] using
          accelerated_max_type_estimating_center_succ_normalized
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' ih
      have hyj1 :
          yj1 = xj1 + βj • (xj1 - xj) := by
        change
          constantStepSchemeIIMinimaxY problem hL x0Q (Subtype.mk α0 hα0') (j + 1) =
            (constantStepSchemeIIMinimaxX problem hL x0Q (Subtype.mk α0 hα0') (j + 1) : E) +
              ((constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0') j *
                    (1 - constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0') j)) /
                  (constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0') j ^
                      (2 : ℕ) +
                    constantStepSchemeIIMinimaxAlpha problem hL x0Q (Subtype.mk α0 hα0') (j + 1))) •
                ((constantStepSchemeIIMinimaxX problem hL x0Q (Subtype.mk α0 hα0') (j + 1) : E) -
                  (constantStepSchemeIIMinimaxX problem hL x0Q (Subtype.mk α0 hα0') j : E))
        exact
          constantStepSchemeIIMinimaxY_succ
            problem hL x0Q (Subtype.mk α0 hα0') j
      have hygap :
          yj1 - xj1 = βj • (xj1 - xj) := by
        calc
          yj1 - xj1 = (xj1 + βj • (xj1 - xj)) - xj1 := by
                rw [hyj1]
          _ = βj • (xj1 - xj) := by
                abel
      have hcoeff :
          ((((1 - αj) / αj) - βj) : ℝ) = (γj2 / (αj1 * γj1)) * βj := by
        simpa [alphaSeq, gamma, αj, αj1, γj1, γj2, βj] using
          accelerated_max_type_normalized_center_coeff_eq_transport_coeff
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j
      -- Route correction: use the normalized successor identity before returning to the public
      -- transport factor `(γ_{j+2} / (α_{j+1} γ_{j+1})) (y_{j+1} - x_{j+1})`.
      calc
        vj1 - yj1 = ((((1 - αj) / αj) - βj) : ℝ) • (xj1 - xj) := hnormalized
        _ = ((γj2 / (αj1 * γj1)) * βj : ℝ) • (xj1 - xj) := by
              rw [hcoeff]
        _ = (γj2 / (αj1 * γj1) : ℝ) • (βj • (xj1 - xj)) := by
              rw [smul_smul]
        _ = (γj2 / (αj1 * γj1) : ℝ) • (yj1 - xj1) := by
              rw [hygap]

/-- Helper for Theorem 2.45: the weighted transport combination
`((α_j γ_j) / γ_{j+1}) (v_j - y_j) + (x_j - y_j)` vanishes along the theorem-local trajectory. -/
private lemma accelerated_max_type_transport_shift_eq_zero
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    let gammaCurr :=
      estimatingSequenceCurvature μ γ0
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        j
    let gammaNext :=
      estimatingSequenceCurvature μ γ0
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        (j + 1)
    let αj :=
      acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let vj :=
      acceleratedMaxTypeEstimatingCenter
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let yj :=
      acceleratedMaxTypeYSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    let xj :=
      acceleratedMaxTypeXSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    (((αj * gammaCurr) / gammaNext) • (vj - yj) + (xj - yj) : E) = 0 := by
  let alphaSeq :=
    acceleratedMaxTypeAlphaSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gamma : ℕ → ℝ := estimatingSequenceCurvature μ γ0 alphaSeq
  let αj : ℝ := alphaSeq j
  let γj : ℝ := gamma j
  let γj1 : ℝ := gamma (j + 1)
  let vj :=
    acceleratedMaxTypeEstimatingCenter
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let yj :=
    acceleratedMaxTypeYSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let xj :=
    acceleratedMaxTypeXSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  have hcenter :=
    accelerated_max_type_estimating_center_sub_eq_iterate_gap
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  have hαj_pos : 0 < αj := by
    simpa [alphaSeq, αj, acceleratedMaxTypeAlphaSeq] using
      (constantStepSchemeIIMinimaxAlpha_mem_Ioo
        problem hL x0Q (Subtype.mk α0 hα0') j).1
  have hγj_pos : 0 < γj := by
    simpa [gamma, γj] using
      accelerated_max_type_estimating_curvature_pos'
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
  have hγj1_pos : 0 < γj1 := by
    simpa [gamma, γj1] using
      accelerated_max_type_estimating_curvature_pos'
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
  -- Convert the center-gap identity into the exact mixed-term cancellation surface.
  calc
    (((αj * γj) / γj1) • (vj - yj) + (xj - yj) : E)
        = (((αj * γj) / γj1) •
            ((γj1 / (αj * γj)) • (yj - xj)) + (xj - yj) : E) := by
              rw [hcenter]
    _ = (yj - xj) + (xj - yj) := by
          rw [smul_smul]
          have hcoef : (((αj * γj) / γj1 : ℝ) * (γj1 / (αj * γj))) = 1 := by
            field_simp [hαj_pos.ne', hγj_pos.ne', hγj1_pos.ne']
          rw [hcoef, one_smul]
    _ = 0 := by
          abel

/-- Helper for Theorem 2.45: after inserting the exact-step lower bound into the successor
estimating-value recursion, the remaining `‖g_j‖²` coefficient vanishes because
`γ_{j+1} = L α_j²`. -/
private lemma accelerated_max_type_curvature_coeff_eq_zero
    (hα0' : α0 ∈ αRange)
    (j : ℕ) :
    let gammaNext :=
      estimatingSequenceCurvature μ γ0
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        (j + 1)
    let αj :=
      acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
    (1 / (2 * L) - αj ^ (2 : ℕ) / (2 * gammaNext) : ℝ) = 0 := by
  set alphaSeq :=
    (acceleratedMaxTypeAlphaSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' : ℕ → ℝ)
  set γj1 := (estimatingSequenceCurvature μ γ0 alphaSeq (j + 1) : ℝ)
  set αj := (alphaSeq j : ℝ)
  have hγj1 :
      γj1 = L * αj ^ (2 : ℕ) := by
    simpa [αj, γj1, alphaSeq] using
      accelerated_max_type_estimating_curvature_succ_eq_L_mul_sq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
  have hαj_pos : 0 < αj := by
    simpa [alphaSeq, αj, acceleratedMaxTypeAlphaSeq] using
      (constantStepSchemeIIMinimaxAlpha_mem_Ioo
        problem hL x0Q (Subtype.mk α0 hα0') j).1
  simpa [αj, γj1, alphaSeq, hγj1] using
    show (1 / (2 * L) - αj ^ (2 : ℕ) / (2 * (L * αj ^ (2 : ℕ))) : ℝ) = 0 by
      field_simp [hL.ne', hαj_pos.ne']
      ring

/-- Helper for Theorem 2.45: one exact max-type proximal step propagates the domination
`f(x_j) ≤ φ_j^*` to the next stage `f(x_{j+1}) ≤ φ_{j+1}^*`. -/
private lemma accelerated_max_type_estimating_value_step_ge_objective
    (hα0' : α0 ∈ αRange)
    (j : ℕ)
    (hφj :
      fObj
          (acceleratedMaxTypeXSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j) ≤
        acceleratedMaxTypeEstimatingValue
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j) :
    fObj
        (acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' (j + 1)) ≤
      acceleratedMaxTypeEstimatingValue
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1) := by
  let value :=
    acceleratedMaxTypeEstimatingValue
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let alphaSeq :=
    acceleratedMaxTypeAlphaSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gamma : ℕ → ℝ := estimatingSequenceCurvature μ γ0 alphaSeq
  let αj : ℝ := alphaSeq j
  let γj : ℝ := gamma j
  let γj1 : ℝ := gamma (j + 1)
  let vj :=
    acceleratedMaxTypeEstimatingCenter
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let yj :=
    acceleratedMaxTypeYSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let gj : E := g_f[Q | problem.components; γL](yj)
  let xj :=
    acceleratedMaxTypeXSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' j
  let xj1 :=
    acceleratedMaxTypeXSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0' (j + 1)
  let A : ℝ := αj * (1 - αj) * γj / γj1
  let c : ℝ := (αj * γj) / γj1
  let R : ℝ :=
    (1 / (2 * L) - αj ^ (2 : ℕ) / (2 * γj1)) * ‖gj‖ ^ (2 : ℕ) +
      (1 - αj) * inner ℝ gj (xj - yj) +
      A * inner ℝ gj (vj - yj) +
      (1 - αj) * ((μ / 2) * ‖xj - yj‖ ^ (2 : ℕ)) +
      A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ))
  have hα_mem : αj ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [alphaSeq, αj, acceleratedMaxTypeAlphaSeq] using
      constantStepSchemeIIMinimaxAlpha_mem_Ioo
        problem hL x0Q (Subtype.mk α0 hα0') j
  have hα_nonneg : 0 ≤ αj := hα_mem.1.le
  have hone_minus_nonneg : 0 ≤ 1 - αj := sub_nonneg.mpr hα_mem.2.le
  have hγj_pos : 0 < γj := by
    simpa [gamma, γj] using
      accelerated_max_type_estimating_curvature_pos'
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
  have hγj1_pos : 0 < γj1 := by
    simpa [gamma, γj1] using
      accelerated_max_type_estimating_curvature_pos'
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' (j + 1)
  have hμ : 0 < μ := by
    classical
    let i : ι := Classical.choice inferInstance
    exact (mem_S11_iff.mp (problem.components_mem i)).mu_pos
  have hvalue :
      value (j + 1) =
        (1 - αj) * value j +
          αj * fObj xj1 +
          (αj / (2 * L) - αj ^ (2 : ℕ) / (2 * γj1)) * ‖gj‖ ^ (2 : ℕ) +
          A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ) + inner ℝ gj (vj - yj)) := by
    simpa [value, alphaSeq, gamma, αj, γj, γj1, vj, yj, gj, xj1, A] using
      acceleratedMaxTypeEstimatingValue_succ
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j
  have hstep_lower :
      fObj xj ≥
        fObj xj1 +
          inner ℝ gj (xj - yj) +
          (1 / (2 * L)) * ‖gj‖ ^ (2 : ℕ) +
          (μ / 2) * ‖xj - yj‖ ^ (2 : ℕ) := by
    simpa [xj, xj1, yj, gj] using
      accelerated_max_type_exact_step_objective_lower_bound
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j xj
  have hstep_scaled :=
    mul_le_mul_of_nonneg_left hstep_lower hone_minus_nonneg
  have hφ_scaled : (1 - αj) * fObj xj ≤ (1 - αj) * value j := by
    exact mul_le_mul_of_nonneg_left hφj hone_minus_nonneg
  have hcombined :
      (1 - αj) *
            (fObj xj1 +
              inner ℝ gj (xj - yj) +
              (1 / (2 * L)) * ‖gj‖ ^ (2 : ℕ) +
              (μ / 2) * ‖xj - yj‖ ^ (2 : ℕ)) ≤
        (1 - αj) * value j := by
    exact le_trans hstep_scaled hφ_scaled
  have htarget : fObj xj1 ≤ value (j + 1) := by
    rw [hvalue]
    have hpre :=
      add_le_add_right hcombined
        (αj * fObj xj1 +
          (αj / (2 * L) - αj ^ (2 : ℕ) / (2 * γj1)) * ‖gj‖ ^ (2 : ℕ) +
          A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ) + inner ℝ gj (vj - yj)))
    have hpre' :
        fObj xj1 + R ≤
          (1 - αj) * value j +
            αj * fObj xj1 +
            (αj / (2 * L) - αj ^ (2 : ℕ) / (2 * γj1)) * ‖gj‖ ^ (2 : ℕ) +
            A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ) + inner ℝ gj (vj - yj)) := by
      have hleft_eq :
          αj * fObj xj1 +
              (αj / (2 * L) - αj ^ (2 : ℕ) / (2 * γj1)) * ‖gj‖ ^ (2 : ℕ) +
              A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ) + inner ℝ gj (vj - yj)) +
              (1 - αj) *
                (fObj xj1 +
                  inner ℝ gj (xj - yj) +
                  (1 / (2 * L)) * ‖gj‖ ^ (2 : ℕ) +
                  (μ / 2) * ‖xj - yj‖ ^ (2 : ℕ)) =
            fObj xj1 + R := by
        dsimp [R, A]
        ring
      have hright_eq :
          αj * fObj xj1 +
              (αj / (2 * L) - αj ^ (2 : ℕ) / (2 * γj1)) * ‖gj‖ ^ (2 : ℕ) +
              A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ) + inner ℝ gj (vj - yj)) +
              (1 - αj) * value j =
            (1 - αj) * value j +
              αj * fObj xj1 +
              (αj / (2 * L) - αj ^ (2 : ℕ) / (2 * γj1)) * ‖gj‖ ^ (2 : ℕ) +
              A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ) + inner ℝ gj (vj - yj)) := by
        ring
      rw [← hleft_eq, ← hright_eq]
      exact hpre
    have hcurv0 :
        (1 / (2 * L) - αj ^ (2 : ℕ) / (2 * γj1) : ℝ) = 0 := by
      have hγj1 :
          γj1 = L * αj ^ (2 : ℕ) := by
        simpa [alphaSeq, gamma, αj, γj1] using
          accelerated_max_type_estimating_curvature_succ_eq_L_mul_sq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j
      rw [hγj1]
      field_simp [hL.ne', hα_mem.1.ne']
      ring
    have htransport :
        c • (vj - yj) + (xj - yj) = 0 := by
      have htransport' :=
        accelerated_max_type_transport_shift_eq_zero
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j
      dsimp [c, alphaSeq, gamma, αj, γj, γj1, vj, yj, xj] at htransport'
      exact htransport'
    have hxgap :
        xj - yj = -(c • (vj - yj)) := by
      simpa using eq_neg_of_add_eq_zero_right htransport
    have hcross_cancel :
        (1 - αj) * inner ℝ gj (xj - yj) + A * inner ℝ gj (vj - yj) = 0 := by
      rw [hxgap, inner_neg_right, real_inner_smul_right]
      simp [A, c]
      ring
    have hquad_shift :
        (1 - αj) * ((μ / 2) * ‖xj - yj‖ ^ (2 : ℕ)) =
          ((1 - αj) * c ^ (2 : ℕ)) * ((μ / 2) * ‖vj - yj‖ ^ (2 : ℕ)) := by
      rw [hxgap, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have hA_nonneg : 0 ≤ A := by
      exact
        div_nonneg (mul_nonneg (mul_nonneg hα_nonneg hone_minus_nonneg) hγj_pos.le) hγj1_pos.le
    have hcoef_nonneg : 0 ≤ (1 - αj) * c ^ (2 : ℕ) + A := by
      have hleft : 0 ≤ (1 - αj) * c ^ (2 : ℕ) := by
        exact mul_nonneg hone_minus_nonneg (sq_nonneg c)
      linarith
    have hquad_nonneg :
        0 ≤
          (1 - αj) * ((μ / 2) * ‖xj - yj‖ ^ (2 : ℕ)) +
            A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ)) := by
      let qv : ℝ := (μ / 2) * ‖vj - yj‖ ^ (2 : ℕ)
      have hqv_nonneg : 0 ≤ qv := by
        positivity
      have hprod : 0 ≤ (((1 - αj) * c ^ (2 : ℕ)) + A) * qv := by
        exact mul_nonneg hcoef_nonneg hqv_nonneg
      calc
        0 ≤ (((1 - αj) * c ^ (2 : ℕ)) + A) * qv := hprod
        _ = ((1 - αj) * c ^ (2 : ℕ)) * qv + A * qv := by
              ring
        _ =
            (1 - αj) * ((μ / 2) * ‖xj - yj‖ ^ (2 : ℕ)) +
              A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ)) := by
              have hnorm_eq : ‖vj - yj‖ = ‖yj - vj‖ := by
                rw [norm_sub_rev]
              rw [hquad_shift]
              simp [qv, hnorm_eq]
    have hR_eq :
        R =
          (1 - αj) * ((μ / 2) * ‖xj - yj‖ ^ (2 : ℕ)) +
            A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ)) := by
      calc
        R =
            (1 / (2 * L) - αj ^ (2 : ℕ) / (2 * γj1)) * ‖gj‖ ^ (2 : ℕ) +
              ((1 - αj) * inner ℝ gj (xj - yj) + A * inner ℝ gj (vj - yj)) +
              ((1 - αj) * ((μ / 2) * ‖xj - yj‖ ^ (2 : ℕ)) +
                A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ))) := by
              simp [R]
              ring
        _ =
            (1 - αj) * ((μ / 2) * ‖xj - yj‖ ^ (2 : ℕ)) +
              A * ((μ / 2) * ‖yj - vj‖ ^ (2 : ℕ)) := by
              rw [hcurv0, hcross_cancel]
              ring
    have hR_nonneg : 0 ≤ R := by
      rw [hR_eq]
      exact hquad_nonneg
    have hstart : fObj xj1 ≤ fObj xj1 + R := by
      exact le_add_of_nonneg_right hR_nonneg
    exact hstart.trans hpre'
  simpa [value, xj1] using htarget

/-- Helper for Theorem 2.45: the theorem-local estimating values dominate the actual objective
values along the accelerated max-type proximal trajectory. -/
private lemma accelerated_max_type_estimating_value_ge_objective
    (hα0' : α0 ∈ αRange) :
    ∀ j : ℕ,
      fObj
          (acceleratedMaxTypeXSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0' j) ≤
        acceleratedMaxTypeEstimatingValue
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' j := by
  -- Follow the source estimate-sequence induction: the base value is exact, and the successor
  -- step is the theorem-local one-step comparison proved above.
  intro j
  induction j with
  | zero =>
      simp [acceleratedMaxTypeEstimatingValue_zero, acceleratedMaxTypeXSeq]
  | succ j ih =>
      exact accelerated_max_type_estimating_value_step_ge_objective
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0' j ih

/-- Helper for Theorem 2.45: the abstract estimating-sequence theorem already yields the local
objective gap bound once the iterate-versus-value domination is available. -/
private lemma accelerated_max_type_objective_gap_le_estimating_weight
    (hα0' : α0 ∈ αRange)
    (hxStar : IsMinOn fObj Set.univ xStar)
    (k : ℕ) :
    fObj
        (acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0' k) -
        fObj xStar ≤
      estimatingWeight
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0')
          k *
        (fObj x0 - fObj xStar + (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  -- Route correction: reduce the public gap bound to the generic estimate-sequence theorem, so
  -- only the source-specific domination `f(x_k) ≤ φ_k^*` remains as the substantive blocker.
  simpa [acceleratedMaxTypeXSeq] using
    estimating_sequence_suboptimality_le
      fObj
      (acceleratedMaxTypeXSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
      (acceleratedMaxTypeEstimatingFunction
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
      (acceleratedMaxTypeEstimatingValue
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
      (acceleratedMaxTypeAlphaSeq
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
      xStar
      hxStar
      γ0
      (accelerated_max_type_estimating_value_ge_objective
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
      (accelerated_max_type_estimating_min_value
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
      (accelerated_max_type_estimating_function_upper_bound
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
      (acceleratedMaxTypeEstimatingFunction_zero
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (α0 := α0) hα0')
      k

/-- Helper for Theorem 2.45: the estimating-sequence weight attached to the local scalar
recurrence satisfies the hyperbolic bound from Lemma 2.10. -/
private lemma accelerated_max_type_estimating_weight_le_hyperbolic
    (hα0' : α0 ∈ αRange)
    (k : ℕ) :
    estimatingWeight
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        k ≤
      (4 * μ) /
        ((γ0 - μ) *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt qf) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt qf))) ^
            (2 : ℕ)) := by
  classical
  let alphaSeq : ℕ → ℝ :=
    acceleratedMaxTypeAlphaSeq
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0'
  let gammaSeq : ℕ → ℝ :=
    estimatingSequenceCurvature μ γ0 alphaSeq
  have hγ0_mem : γ0 ∈ Set.Ioc μ (3 * L + μ) :=
    accelerated_max_type_gamma0_mem_Ioc
      (problem := problem) (hL := hL) (α0 := α0) (hα0 := hα0')
  have hμ : 0 < μ := by
    let i : ι := Classical.choice inferInstance
    exact (mem_S11_iff.mp (problem.components_mem i)).mu_pos
  let method : OptimalMethodRecurrence (fun _ : E ↦ (0 : ℝ)) L μ x0 γ0 :=
    { L_pos := hL
      mu_nonneg := hμ.le
      gamma0_pos := lt_trans hμ hγ0_mem.1
      x := fun _ ↦ x0
      y := fun _ ↦ x0
      v := fun _ ↦ x0
      alpha := alphaSeq
      gamma := gammaSeq
      x_zero := rfl
      v_zero := rfl
      gamma_zero := rfl
      alpha_mem_Ioo := by
        intro j
        simpa [alphaSeq, acceleratedMaxTypeAlphaSeq] using
          constantStepSchemeIIMinimaxAlpha_mem_Ioo
            problem hL x0Q (Subtype.mk α0 hα0') j
      alpha_equation := by
        intro j
        have hcurv :
            gammaSeq (j + 1) = L * alphaSeq j ^ (2 : ℕ) := by
          simpa [gammaSeq, alphaSeq] using
            accelerated_max_type_estimating_curvature_succ_eq_L_mul_sq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' j
        have hsucc :
            gammaSeq (j + 1) = (1 - alphaSeq j) * gammaSeq j + alphaSeq j * μ := by
          simpa [gammaSeq] using estimatingSequenceCurvature_succ μ γ0 alphaSeq j
        linarith
      gamma_succ := by
        intro j
        simpa [gammaSeq] using estimatingSequenceCurvature_succ μ γ0 alphaSeq j
      y_eq := by
        intro j
        have hgamma_pos :
            0 < gammaSeq j + alphaSeq j * μ := by
          have hgamma_curr_pos :
              0 < gammaSeq j := by
            simpa [gammaSeq] using
              accelerated_max_type_estimating_curvature_pos'
                (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
                (x0 := x0) (α0 := α0) hα0' j
          have halpha_pos :
              0 < alphaSeq j := by
            simpa [alphaSeq, acceleratedMaxTypeAlphaSeq] using
              (constantStepSchemeIIMinimaxAlpha_mem_Ioo
                problem hL x0Q (Subtype.mk α0 hα0') j).1
          positivity
        have hsucc :
            gammaSeq (j + 1) = (1 - alphaSeq j) * gammaSeq j + alphaSeq j * μ := by
          simpa [gammaSeq] using estimatingSequenceCurvature_succ μ γ0 alphaSeq j
        have hcoef :
            gammaSeq j + alphaSeq j * μ =
              alphaSeq j * gammaSeq j + gammaSeq (j + 1) := by
          rw [hsucc]
          ring
        calc
          x0 = (1 / (gammaSeq j + alphaSeq j * μ)) •
              ((gammaSeq j + alphaSeq j * μ) • x0) := by
                rw [smul_smul, one_div, inv_mul_cancel₀ hgamma_pos.ne',
                  one_smul]
          _ = (1 / (gammaSeq j + alphaSeq j * μ)) •
              ((alphaSeq j * gammaSeq j + gammaSeq (j + 1)) • x0) := by
                congr 1
                exact congrArg (fun t : ℝ ↦ t • x0) hcoef
          _ = (1 / (gammaSeq j + alphaSeq j * μ)) •
              ((alphaSeq j * gammaSeq j) • x0 + gammaSeq (j + 1) • x0) := by
                rw [add_smul]
      v_succ := by
        intro j
        have hnext_pos :
            0 < gammaSeq (j + 1) := by
          simpa [gammaSeq] using
            accelerated_max_type_estimating_curvature_pos'
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0' (j + 1)
        have hsucc :
            gammaSeq (j + 1) = (1 - alphaSeq j) * gammaSeq j + alphaSeq j * μ := by
          simpa [gammaSeq] using estimatingSequenceCurvature_succ μ γ0 alphaSeq j
        calc
          x0 = (1 / gammaSeq (j + 1)) • (gammaSeq (j + 1) • x0) := by
                rw [smul_smul, one_div, inv_mul_cancel₀ hnext_pos.ne', one_smul]
          _ = (1 / gammaSeq (j + 1)) •
              ((((1 - alphaSeq j) * gammaSeq j + alphaSeq j * μ) • x0)) := by
                simpa using congrArg
                  (fun t : ℝ ↦ (1 / gammaSeq (j + 1)) • (t • x0))
                  hsucc.symm
          _ = (1 / gammaSeq (j + 1)) •
              (((1 - alphaSeq j) * gammaSeq j) • x0 + (alphaSeq j * μ) • x0) := by
                rw [add_smul]
          _ = (1 / gammaSeq (j + 1)) •
              (((1 - alphaSeq j) * gammaSeq j) • x0 +
                (alphaSeq j * μ) • x0 -
                alphaSeq j • (0 : E)) := by
                simp
          _ = (1 / gammaSeq (j + 1)) •
              (((1 - alphaSeq j) * gammaSeq j) • x0 +
                (alphaSeq j * μ) • x0 -
                alphaSeq j • gradient (fun _ : E ↦ (0 : ℝ)) x0) := by
                have hgrad_zero : gradient (fun _ : E ↦ (0 : ℝ)) x0 = 0 := by
                  simpa using (gradient_fun_const (x := x0) (c := (0 : ℝ)))
                rw [hgrad_zero] }
  have hweight :
      estimatingWeight alphaSeq k = method.weight k := by
    induction k with
    | zero =>
        simp [estimatingWeight, OptimalMethodRecurrence.weight]
    | succ k ih =>
        rw [estimatingWeight, OptimalMethodRecurrence.weight_succ, ih]
  have hbound :
      method.weight k ≤
        (4 * μ) /
          ((γ0 - μ) *
            (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt qf) -
              Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt qf))) ^
              (2 : ℕ)) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (OptimalMethodRecurrence.weight_bounds method hμ hγ0_mem k).1
  calc
    estimatingWeight
        (acceleratedMaxTypeAlphaSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0')
        k = method.weight k := by
          simpa [alphaSeq] using hweight
    _ ≤
      (4 * μ) /
        ((γ0 - μ) *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt qf) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt qf))) ^
            (2 : ℕ)) := hbound

/-- Theorem 2.45: if a finite max-type objective has `μ`-strongly convex `L`-smooth component
functions, admits a global minimizer `xStar`, and the exact accelerated proximal-gradient scheme
is started from an admissible parameter `α₀`, then the objective gap along the iterates satisfies
the displayed hyperbolic estimate. -/
-- Proof sketch: build the estimating-sequence Lyapunov energy attached to the exact max-type
-- proximal-gradient update `x_f(y_k; L)` and prove that it is nonincreasing along the scheme.
-- The owner bridge `optimal_method_alpha0_initial_curvature_mem_Ioc`, applied using
-- `problem.components_mem`, `hL`, and `hα0`, supplies `γ₀ ∈ (μ, 3L + μ]`. The initial energy is
-- `f(x₀) - f(x*) + (γ₀ / 2) ‖x₀ - x*‖²`, while the scalar recurrence for `α_k`
-- yields the lower bound on the estimating-sequence weight expressed by the hyperbolic
-- denominator. Dividing the energy inequality by this lower bound gives the claimed estimate.
theorem acceleratedMaxTypeProximal_hyperbolic_objective_gap_le
    (hα0 : α0 ∈ αRange)
    (hxStar : IsMinOn fObj Set.univ xStar)
    (k : ℕ) :
    fObj (xSeq k) - fObj xStar ≤
      (4 * μ *
        (fObj x0 - fObj xStar +
          (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ))) /
        ((γ0 - μ) *
          (Real.exp
              (((k + 1 : ℝ) / 2) * Real.sqrt qf) -
            Real.exp
              (-(((k + 1 : ℝ) / 2) * Real.sqrt qf))) ^
            (2 : ℕ)) := by
  let E0 :=
    fObj x0 - fObj xStar + (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)
  have hE0_nonneg : 0 ≤ E0 := by
    -- The initial Lyapunov energy is nonnegative because `xStar` minimizes the objective.
    simpa [E0] using
      accelerated_max_type_initial_energy_nonneg
        (problem := problem) (xStar := xStar) (hxStar := hxStar) (hL := hL)
        (x0 := x0) (α0 := α0) (hα0 := hα0)
  have hgap :
      fObj
          (acceleratedMaxTypeXSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0 k) - fObj xStar ≤
        estimatingWeight
            (acceleratedMaxTypeAlphaSeq
              (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
              (x0 := x0) (α0 := α0) hα0)
            k *
          E0 := by
    have hgap0 :=
      accelerated_max_type_objective_gap_le_estimating_weight
        (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
        (x0 := x0) (xStar := xStar) (α0 := α0) hα0 hxStar k
    simpa [E0] using hgap0
  have hweight :=
    accelerated_max_type_estimating_weight_le_hyperbolic
      (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
      (x0 := x0) (α0 := α0) hα0 k
  have hscaled := mul_le_mul_of_nonneg_right hweight hE0_nonneg
  have hrhs :
      estimatingWeight
          (acceleratedMaxTypeAlphaSeq
            (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
            (x0 := x0) (α0 := α0) hα0)
          k *
        E0 ≤
      (4 * μ * E0) /
        ((γ0 - μ) *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt qf) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt qf))) ^
            (2 : ℕ)) := by
    simpa [E0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  change
    fObj
        (acceleratedMaxTypeXSeq
          (problem := problem) (hfeasible_univ := hfeasible_univ) (hL := hL)
          (x0 := x0) (α0 := α0) hα0 k) - fObj xStar ≤
      (4 * μ * E0) /
        ((γ0 - μ) *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt qf) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt qf))) ^
            (2 : ℕ))
  exact hgap.trans hrhs

/-- Under the same assumptions as the hyperbolic estimate, the objective gap also satisfies the
simpler quadratic `O((k + 1)⁻²)` upper bound. -/
-- Proof sketch: start from
-- `acceleratedMaxTypeProximal_hyperbolic_objective_gap_le` and bound the hyperbolic denominator
-- from below using `exp t - exp (-t) ≥ 2 t` for `t ≥ 0`, with
-- `t = ((k + 1) / 2) * sqrt q[μ, L]`. Then simplify the resulting factor using
-- `q[μ, L] = μ / L`.
theorem acceleratedMaxTypeProximal_quadratic_objective_gap_le
    (hα0 : α0 ∈ αRange)
    (hxStar : IsMinOn fObj Set.univ xStar)
    (k : ℕ) :
    fObj (xSeq k) - fObj xStar ≤
      (4 * L / ((γ0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ))) *
        (fObj x0 - fObj xStar +
          (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  let E0 :=
    fObj x0 - fObj xStar + (γ0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)
  -- Start from the hyperbolic estimate already proved in the source-faithful first theorem.
  have hhyper :=
    acceleratedMaxTypeProximal_hyperbolic_objective_gap_le
      (problem := problem) (hfeasible_univ := hfeasible_univ) (xStar := xStar)
      (hL := hL) (x0 := x0) (α0 := α0) (hα0 := hα0) (hxStar := hxStar) k
  have hγ0 : γ0 ∈ Set.Ioc μ (3 * L + μ) :=
    accelerated_max_type_gamma0_mem_Ioc
      (problem := problem) (hL := hL) (α0 := α0) (hα0 := hα0)
  have hμ : 0 < μ := by
    -- Any component already carries the chapter's `μ > 0` strong-convexity witness.
    classical
    let i : ι := Classical.choice inferInstance
    exact (mem_S11_iff.mp (problem.components_mem i)).mu_pos
  have hgap : 0 < γ0 - μ := by
    linarith [hγ0.1]
  have hE0_nonneg : 0 ≤ E0 := by
    -- Reuse the minimizer-based sign information on the initial Lyapunov energy.
    simpa [E0] using
      accelerated_max_type_initial_energy_nonneg
        (problem := problem) (xStar := xStar) (hxStar := hxStar) (hL := hL)
        (x0 := x0) (α0 := α0) (hα0 := hα0)
  have hfactor :=
    optimal_method_hyperbolic_factor_le_quadratic_factor hμ hL k
  have hscaled :=
    mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ 4 * E0 / (γ0 - μ))
  have hrhs :
      (4 * μ * E0) /
          ((γ0 - μ) *
            (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt qf) -
              Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt qf))) ^
              (2 : ℕ)) ≤
        (4 * L / ((γ0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ))) * E0 := by
    -- Compare the hyperbolic and quadratic scalar factors and then restore the common energy term.
    simpa [E0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hbound := le_trans hhyper hrhs
  simpa [E0, mul_assoc, mul_left_comm, mul_comm] using hbound

end

end AcceleratedMaxTypeProximalRates
