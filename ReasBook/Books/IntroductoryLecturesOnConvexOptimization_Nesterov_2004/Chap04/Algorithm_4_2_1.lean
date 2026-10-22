/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 4.2.1 lies in the whole-space cubic-regularization / Hessian-Lipschitz optimization
domain on real Hilbert spaces.

Sampled owner-style declarations:
* `HasLipschitzContinuousHessian L3 f`, written on theorem surfaces as `f ∈ C22[L3]`, in
  `Definition_4_2_7`;
* `cubicRegularizationQuadraticApproximation f M x` in `Definition_4_1_3`, the chapter owner of
  the cubic model minimized by the step;
* `CubicRegularizationMapping f M` in `Definition_4_2_12`, the chapter owner of a chosen
  minimizer map for the cubic model together with its minimizing property;
* `Function.iterate`, the canonical owner of autonomous discrete trajectories.

Best owner abstraction:
* source-facing: `CubicNewtonMethod`;
* core/canonical: `f ∈ C22[L3]`, `CubicRegularizationMapping f (L3 : ℝ)`, `Function.iterate`,
  and
  `cubicRegularizationQuadraticApproximation f (L3 : ℝ) x`;
* bridge/view: companion theorems recovering the textbook recursive identities and cubic-model
  minimizing statement from the owner-layer step API.

Primitive data:
* the objective `f`;
* the regularization constant `L3`;
* the chosen cubic-model minimizer map `T_{L₃}`;
* whole-space Hessian-Lipschitz membership `f ∈ C22[L3]`.

Derived API:
* the canonical iterate sequence `x₀, x₁, x₂, ... = T_{L₃}^[k](x₀)`;
* the recursive identities `x₀ = x0` and `x_{k+1} = T_{L₃}(x_k)`;
* `ContDiff ℝ 2 f` and the global Hessian-Lipschitz bound for `f`;
* the textbook minimizing property of each cubic Newton step on the cubic model
  `cubicRegularizationQuadraticApproximation`.

The previous version stored an arbitrary iterate sequence together with its initial-value and
successor equations as primitive data. This refinement keeps the source-facing algorithm object,
but rewrites its public data to the canonical owner layer: the standing Hessian-Lipschitz
assumption `f ∈ C22[L3]` and the cubic-model minimizer-map owner
`CubicRegularizationMapping f (L3 : ℝ)`. The iterate family is now the canonical recursive orbit
of the chosen step map from `x₀`.
-/

/-- Algorithm 4.2.1: a cubic Newton method for an objective `f`, an initial point `x₀`, and a
Lipschitz-Hessian constant `L₃` consists of a chosen cubic-model minimizer map `T_{L₃}` and the
standing owner hypothesis `f ∈ C22[L3]`; the iterate sequence `x₀, x₁, x₂, ...` is the canonical
recursive orbit `x_k = T_{L₃}^[k](x₀)`. -/
structure CubicNewtonMethod
    (f : E → ℝ) (L3 : NNReal) (x0 : E) where
  /-- The chosen cubic-model minimizer map `T_{L₃}`. -/
  step : CubicRegularizationMapping f (L3 : ℝ)
  /-- The objective belongs to the canonical whole-space Hessian-Lipschitz owner `C_M^{2,2}`. -/
  objective_mem : f ∈ C22[L3]

namespace CubicNewtonMethod

variable {f : E → ℝ} {L3 : NNReal} {x0 : E}

/-- A cubic Newton method can be used as its canonical recursive iterate sequence. -/
instance : CoeFun (CubicNewtonMethod f L3 x0) (fun _ ↦ ℕ → E) where
  coe method k := method.step^[k] x0

/-- The zeroth iterate of a cubic Newton method is the prescribed initial point `x₀`. -/
@[simp] theorem x_zero (method : CubicNewtonMethod f L3 x0) :
    method 0 = x0 := by
  simp

/-- The canonical cubic Newton orbit satisfies the recursive update
`x_{k+1} = T_{L₃}(x_k)`. -/
theorem x_succ (method : CubicNewtonMethod f L3 x0) (k : ℕ) :
    method (k + 1) = method.step (method k) := by
  simpa using (Function.iterate_succ_apply' method.step k x0)

/-- A cubic Newton method carries the canonical `C_M^{2,2}` owner data for the objective. -/
theorem contDiff (method : CubicNewtonMethod f L3 x0) :
    ContDiff ℝ 2 f :=
  method.objective_mem.contDiff

/-- A cubic Newton method carries the global Hessian-Lipschitz bound with constant `L₃`. -/
theorem hessian_lipschitz (method : CubicNewtonMethod f L3 x0) :
    LipschitzWith L3 (hessian f) :=
  method.objective_mem.lipschitz

/-- Each cubic Newton update globally minimizes the canonical cubic model with parameter `L₃`. -/
theorem step_isMinOn (method : CubicNewtonMethod f L3 x0) (x : E) :
    IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ (method.step x) := by
  simpa using method.step.isMinOn_apply x

end CubicNewtonMethod

end
