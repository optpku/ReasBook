/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_26
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/- Algorithm 4.2.2 lies in the chapter accelerated cubic-Newton / estimating-sequence domain.

Sampled owner declarations:
* `CubicRegularizationMapping` in `Definition_4_2_12`, the chapter owner for a cubic step `T_M`
  together with its minimizing property;
* `cubicNewtonEstimatingFunction` in `Definition_4_2_14`, the chapter owner for estimating
  functions of the form `ℓ_k(x) + (C / 6) ‖x - x₀‖^3`;
* `CubicNewtonEstimatingSequence` in `Definition_4_2_14`, which shows that the primitive data for
  that owner live in affine parts `ℓ_k`, minimizing points, and scalar sequences, rather than an
  arbitrary primitive family `ψ_k`;
* `sampledAffineMinorant` in `Chap03/Proposition_3_26`, the canonical affine-map owner of
  `z ↦ f(y) + ⟪g, z - y⟫`, matching the affine-gradient increment in the algorithm.

Best owner abstraction:
* source-facing: `AcceleratedCubicNewtonMethod`;
* core/canonical: `CubicRegularizationMapping f M` for the step layer and
  `cubicNewtonEstimatingFunction` for the estimating-function layer;
* bridge/view: `sampledAffineMinorant (x (k + 1)) (∇ f (x (k + 1))) (f (x (k + 1)))`.

Primitive data:
* the cubic-step owners `T_{L₃}` and `T_{2L₃}`, recorded canonically as
  `CubicRegularizationMapping f (L3 : ℝ)` and `CubicRegularizationMapping f (2 * (L3 : ℝ))`;
* the standing chapter smoothness owner `f ∈ C22[L3]`;
* the iterate sequence `x_k`;
* the affine parts `ℓ_k` of the estimating functions;
* the minimizing sequence `v_k`;
* the accumulated weights `A_k`;
* the initialization and recursion laws specific to Algorithm 4.2.2.

Derived API:
* `ContDiff ℝ 2 f` and global `L₃`-Lipschitz control of `hessian f`, both supplied by
  `objective_mem`;
* the estimating functions `ψ_k`, derived canonically as
  `cubicNewtonEstimatingFunction affinePart (6 * (L3 : ℝ)) x0`;
* the textbook formulas for `ψ₁` and `ψ_{k+1}`;
* the minimizing property of `v_k` written on the `ψ_k` surface.

Source/core/bridge triage:
* source-facing: Algorithm 4.2.2 itself;
* core/canonical: `CubicRegularizationMapping f M` and `cubicNewtonEstimatingFunction`;
* bridge/view: the affine-gradient update term as `sampledAffineMinorant`.

The previous file stored the full family `ψ_k` as primitive data even though Chapter 4 already
owns these functions canonically by their affine parts plus the fixed cubic term. This refinement
keeps the source-facing algorithm object, but records only the two step owners actually used by
Algorithm 4.2.2, moves the estimating-function surface to the canonical estimating-function
owner, and records the standing `C22[L3]` hypothesis once on the owner instead of duplicating it
downstream. -/

/-- The scalar coefficient `a_k = ((k + 1) (k + 2)) / 2` used in the accelerated cubic Newton
estimating-sequence update. -/
def acceleratedCubicNewtonWeight (k : ℕ) : ℝ :=
  (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2

/-- Expanding `acceleratedCubicNewtonWeight k` gives the textbook coefficient
`a_k = ((k + 1) (k + 2)) / 2`. -/
@[simp] theorem acceleratedCubicNewtonWeight_def (k : ℕ) :
    acceleratedCubicNewtonWeight k = (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2 :=
  rfl

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- The interpolation point `y_k = (k / (k + 3)) x_k + (3 / (k + 3)) v_k` determined by the
iterate sequence `x_k` and the minimizer sequence `v_k`. -/
def acceleratedCubicNewtonInterpolationPoint
    (x v : ℕ → E) (k : ℕ) : E :=
  ((k : ℝ) / ((k : ℝ) + 3)) • x k + (3 / ((k : ℝ) + 3)) • v k

/-- Expanding `acceleratedCubicNewtonInterpolationPoint x v k` gives the textbook formula for
`y_k`. -/
@[simp] theorem acceleratedCubicNewtonInterpolationPoint_def
    (x v : ℕ → E) (k : ℕ) :
    acceleratedCubicNewtonInterpolationPoint x v k =
      ((k : ℝ) / ((k : ℝ) + 3)) • x k + (3 / ((k : ℝ) + 3)) • v k :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Algorithm 4.2.2: an accelerated cubic regularization method for Newton's method with the
chosen cubic-step owners `T_{L₃}` and `T_{2L₃}`, Hessian-Lipschitz constant `L₃`, and initial
point `x₀` consists of the iterate sequence `x_k`, affine parts `ℓ_k` of the estimating
functions, estimating-function minimizers `v_k`, and scaling parameters `A_k` such that
`x₁ = T_{L₃}(x₀)`, `ψ_k(x) = ℓ_k(x) + L₃ ‖x - x₀‖^3`, `ℓ₁(x) = f(x₁)`, `A₁ = 1`, each `v_k`
minimizes `ψ_k`, each successor iterate satisfies `x_{k+1} = T_{2L₃}(y_k)` with
`y_k = (k / (k + 3)) x_k + (3 / (k + 3)) v_k`, the affine parts satisfy
`ℓ_{k+1} = ℓ_k + a_k [f(x_{k+1}) + ⟪∇ f(x_{k+1}), · - x_{k+1}⟫]`, and the updates
`A_{k+1} = A_k + a_k` hold for `a_k = ((k + 1) (k + 2)) / 2`. -/
structure AcceleratedCubicNewtonMethod
    (f : E → ℝ) (L3 : NNReal) (x0 : E) where
  /-- The canonical cubic-step owner `T_{L₃}` used for the first iterate. -/
  step : CubicRegularizationMapping f (L3 : ℝ)
  /-- The canonical cubic-step owner `T_{2L₃}` used in the recursive updates. -/
  doubleStep : CubicRegularizationMapping f (2 * (L3 : ℝ))
  /-- The objective belongs to the chapter smoothness owner `C_M^{2,2}`. -/
  objective_mem : f ∈ C22[L3]
  /-- The main iterate sequence `x₀, x₁, x₂, ...`. -/
  x : ℕ → E
  /-- The affine parts `ℓ_k` of the estimating functions `ψ_k`. -/
  affinePart : ℕ → E →ᵃ[ℝ] ℝ
  /-- The minimizers `v_k` of the estimating functions `ψ_k`. -/
  v : ℕ → E
  /-- The scaling parameters `A_k`. -/
  A : ℕ → ℝ
  /-- The initialization fixes the starting point `x₀`. -/
  x_zero : x 0 = x0
  /-- The first accelerated iterate is the cubic step `x₁ = T_{L₃}(x₀)`. -/
  x_one : x 1 = step x0
  /-- The first affine part is the constant affine map with value `f(x₁)`. -/
  affinePart_one : affinePart 1 = AffineMap.const ℝ E (f (x 1))
  /-- The initial scaling parameter equals `A₁ = 1`. -/
  A_one : A 1 = 1
  /-- Each `v_k` is a global minimizer of the estimating function `ψ_k`. -/
  v_isMin (k : ℕ) (hk : 1 ≤ k) :
    IsMinOn (cubicNewtonEstimatingFunction affinePart (6 * (L3 : ℝ)) x0 k) Set.univ (v k)
  /-- Each successor iterate is obtained by the cubic regularization step
  `x_{k+1} = T_{2L₃}(y_k)` with `y_k = (k / (k + 3)) x_k + (3 / (k + 3)) v_k`. -/
  x_succ (k : ℕ) (hk : 1 ≤ k) :
    x (k + 1) = doubleStep (acceleratedCubicNewtonInterpolationPoint x v k)
  /-- The affine parts satisfy the affine-gradient recursion from the algorithm. -/
  affinePart_succ (k : ℕ) (hk : 1 ≤ k) :
    affinePart (k + 1) =
      affinePart k +
        acceleratedCubicNewtonWeight k •
          sampledAffineMinorant (x (k + 1)) (∇ f (x (k + 1))) (f (x (k + 1)))
  /-- The scaling parameters satisfy `A_{k+1} = A_k + a_k`. -/
  A_succ (k : ℕ) (hk : 1 ≤ k) : A (k + 1) = A k + acceleratedCubicNewtonWeight k

namespace AcceleratedCubicNewtonMethod

variable {f : E → ℝ} {L3 : NNReal} {x0 : E}

/-- The estimating functions `ψ_k` of an accelerated cubic Newton method, written on the
canonical chapter owner surface. -/
def psi
    (method : AcceleratedCubicNewtonMethod f L3 x0) :
    ℕ → E → ℝ :=
  cubicNewtonEstimatingFunction method.affinePart (6 * (L3 : ℝ)) x0

/-- An accelerated cubic Newton method can be used as its iterate sequence `x_k`. -/
instance :
    CoeFun (AcceleratedCubicNewtonMethod f L3 x0) (fun _ ↦ ℕ → E) where
  coe method := method.x

/-- Evaluating `method.psi k` gives the affine part plus the fixed cubic term `L₃ ‖x - x₀‖^3`.
-/
@[simp] theorem psi_apply
    (method : AcceleratedCubicNewtonMethod f L3 x0) (k : ℕ) (z : E) :
    method.psi k z =
      method.affinePart k z + (L3 : ℝ) * ‖z - x0‖ ^ (3 : ℕ) := by
  rw [psi, cubicNewtonEstimatingFunction_apply]
  congr 1
  ring

/-- The first estimating function is `ψ₁(x) = f(x₁) + L₃ ‖x - x₀‖^3`. -/
theorem psi_one
    (method : AcceleratedCubicNewtonMethod f L3 x0) :
    method.psi 1 = fun z ↦ f (method 1) + (L3 : ℝ) * ‖z - x0‖ ^ (3 : ℕ) := by
  ext z
  simp [method.affinePart_one]

/-- An accelerated cubic Newton method carries the canonical `C_M^{2,2}` owner data for the
objective. -/
theorem contDiff
    (method : AcceleratedCubicNewtonMethod f L3 x0) :
    ContDiff ℝ 2 f :=
  method.objective_mem.contDiff

/-- An accelerated cubic Newton method carries the global Hessian-Lipschitz bound with constant
`L₃`. -/
theorem hessian_lipschitz
    (method : AcceleratedCubicNewtonMethod f L3 x0) :
    LipschitzWith L3 (hessian f) :=
  HasLipschitzContinuousHessian.lipschitz method.objective_mem

/-- Each `v_k` globally minimizes the estimating function `ψ_k`. -/
theorem psi_isMin
    (method : AcceleratedCubicNewtonMethod f L3 x0) {k : ℕ} (hk : 1 ≤ k) :
    IsMinOn (method.psi k) Set.univ (method.v k) := by
  simpa [psi] using method.v_isMin k hk

/-- The distinguished cubic step `T_{L₃}` globally minimizes the corresponding cubic model. -/
theorem step_isMinOn
    (method : AcceleratedCubicNewtonMethod f L3 x0) (y : E) :
    IsMinOn
      (cubicRegularizationQuadraticApproximation f (L3 : ℝ) y)
      Set.univ
      (method.step y) := by
  exact method.step.isMinOn_apply y

/-- The distinguished cubic step `T_{2L₃}` globally minimizes the corresponding cubic model. -/
theorem doubleStep_isMinOn
    (method : AcceleratedCubicNewtonMethod f L3 x0) (y : E) :
    IsMinOn
      (cubicRegularizationQuadraticApproximation f (2 * (L3 : ℝ)) y)
      Set.univ
      (method.doubleStep y) := by
  exact method.doubleStep.isMinOn_apply y

/-- The first accelerated iterate globally minimizes the `L₃` cubic model at `x₀`. -/
theorem x_one_isMinOn
    (method : AcceleratedCubicNewtonMethod f L3 x0) :
    IsMinOn
      (cubicRegularizationQuadraticApproximation f (L3 : ℝ) x0)
      Set.univ
      (method 1) := by
  simpa [method.x_one] using method.step_isMinOn x0

/-- Each recursive accelerated iterate globally minimizes the `2L₃` cubic model at the current
interpolation point. -/
theorem x_succ_isMinOn
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    {k : ℕ} (hk : 1 ≤ k) :
    IsMinOn
      (cubicRegularizationQuadraticApproximation
        f
        (2 * (L3 : ℝ))
        (acceleratedCubicNewtonInterpolationPoint method method.v k))
      Set.univ
      (method (k + 1)) := by
  simpa [method.x_succ k hk] using
    method.doubleStep_isMinOn (acceleratedCubicNewtonInterpolationPoint method method.v k)

/-- The estimating functions satisfy the affine-gradient recursion from the algorithm. -/
theorem psi_succ
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    {k : ℕ} (hk : 1 ≤ k) :
    method.psi (k + 1) = fun z ↦
      method.psi k z +
        acceleratedCubicNewtonWeight k *
          (f (method (k + 1)) + inner ℝ (∇ f (method (k + 1))) (z - method (k + 1))) := by
  ext z
  rw [psi_apply, psi_apply, method.affinePart_succ k hk]
  simp [sampledAffineMinorant_apply]
  ring

end AcceleratedCubicNewtonMethod

end

end
