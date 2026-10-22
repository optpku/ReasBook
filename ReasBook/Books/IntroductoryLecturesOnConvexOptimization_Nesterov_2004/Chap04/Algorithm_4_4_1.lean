/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Algorithm 4.4.1 lies in the modified Gauss--Newton / smooth nonlinear-equation domain.

Sampled owner-style declarations:
* `ContMDiffMap` in `Definition_4_4_8`, the chapter's canonical bundled smooth-map owner;
* `IsSharpMeritFunction` in `Definition_4_4_9`, the source-facing sharp merit-function owner on a
  real normed residual space;
* `modifiedGaussNewtonLocalModel` in `Definition_4_4_11`, the source-facing local-model owner
  already stated intrinsically over real normed spaces;
* `ModifiedGaussNewtonStep` in `Definition_4_4_12`, the source-facing chosen-step owner built on
  the canonical regularized-objective layer.

Source/core/bridge triage:
* source-facing: the algorithmic data `x_k`, `M_k`, and the chosen step maps `V_{M_k}`;
* core/canonical: a smooth residual map together with the merit reformulation and local-model
  owners already defined upstream;
* bridge/view: `acceptedTrialPoint`, which repackages the chosen step value as the next iterate.

Primitive data:
* a bundled smooth map `problem`;
* a sharp merit function `φ`;
* the regularization sequence and chosen modified Gauss--Newton steps.

Derived API:
* the canonical recursive iterate sequence `x₀, x₁, x₂, ...`;
* the coercion from a method to that iterate sequence;
* the identities `x₀ = x0` and `x_{k+1} = V_{M_k}(x_k)`;
* the accepted trial point and its identification with `x_{k+1}`.

The algorithm owner therefore lives on the same intrinsic real normed-space layer as the chapter's
canonical smooth-map, merit-function, local-model, and step owners. The textbook
`ℝⁿ → ℝᵐ` specialization is a direct instance rather than primitive owner data.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

/-- The modified Gauss--Newton iterates generated from an initial point `x₀`, a regularization
schedule `M_k`, and a chosen step owner `V_{M_k}` at each index. -/
def modifiedGaussNewtonIterates
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    (x0 : E₁)
    (regularization : ℕ → ℝ)
    (step : (k : ℕ) →
      ModifiedGaussNewtonStep
        (ψ[problem; φ; fun x ↦ fderiv ℝ problem x])
        Set.univ (regularization k)) :
    ℕ → E₁ :=
  Nat.rec x0 fun k x ↦ (step k).point x

@[simp] theorem modifiedGaussNewtonIterates_zero
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    (x0 : E₁)
    (regularization : ℕ → ℝ)
    (step : (k : ℕ) →
      ModifiedGaussNewtonStep
        (ψ[problem; φ; fun x ↦ fderiv ℝ problem x])
        Set.univ (regularization k)) :
    modifiedGaussNewtonIterates x0 regularization step 0 = x0 :=
  rfl

@[simp] theorem modifiedGaussNewtonIterates_succ
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    (x0 : E₁)
    (regularization : ℕ → ℝ)
    (step : (k : ℕ) →
      ModifiedGaussNewtonStep
        (ψ[problem; φ; fun x ↦ fderiv ℝ problem x])
        Set.univ (regularization k))
    (k : ℕ) :
    modifiedGaussNewtonIterates x0 regularization step (k + 1) =
      (step k).point (modifiedGaussNewtonIterates x0 regularization step k) :=
  rfl

/-- Algorithm 4.4.1: a modified Gauss--Newton method for a smooth nonlinear equation problem
`problem : ℝⁿ → ℝᵐ`, a sharp merit function `φ`, constants `L₀ ∈ (0, L]` and `L`, and an
initial point `x₀` consists of a parameter sequence `M_k ∈ [L₀, 2L]` and a chosen modified
Gauss--Newton step `V_{M_k}` at each iteration such that
`f (V_{M_k}(x_k)) ≤ f[V_{M_k}](x_k)`, where the iterate sequence is the canonical recursion
`x_{k+1} = V_{M_k}(x_k)` with `x₀ = x0` and `f = meritFunctionReformulation problem φ`. -/
structure ModifiedGaussNewtonMethod
    (problem : SmoothMap)
    (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (L0 L : ℝ) (x0 : E₁) where
  /-- The chosen regularization parameters `M₀, M₁, M₂, ...`. -/
  regularization : ℕ → ℝ
  /-- For each iteration `k`, `step k` is the chosen modified Gauss--Newton step with
  regularization parameter `M_k`. -/
  step
      (k : ℕ) :
      ModifiedGaussNewtonStep
        (ψ[problem; φ; fun x ↦ fderiv ℝ problem x])
        Set.univ (regularization k)
  /-- The parameter `L₀` lies in the interval `(0, L]`. -/
  L0_mem_Ioc : L0 ∈ Set.Ioc (0 : ℝ) L
  /-- Every chosen regularization parameter `M_k` belongs to the admissible interval
  `[L₀, 2L]`. -/
  regularization_mem_Icc (k : ℕ) : regularization k ∈ Set.Icc L0 (2 * L)
  /-- The accepted modified Gauss--Newton trial point satisfies
  `f (V_{M_k}(x_k)) ≤ f[V_{M_k}](x_k)` at every iteration. -/
  step_value_le_modelValue (k : ℕ) :
    meritFunctionReformulation problem φ
        ((step k).point (modifiedGaussNewtonIterates x0 regularization step k)) ≤
      (f[(step k)]) (modifiedGaussNewtonIterates x0 regularization step k)

namespace ModifiedGaussNewtonMethod

/-- A modified Gauss--Newton method can be used as its underlying iterate sequence `x_k`. -/
instance
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁} :
    CoeFun (ModifiedGaussNewtonMethod problem φ L0 L x0) (fun _ ↦ ℕ → E₁) where
  coe method := modifiedGaussNewtonIterates x0 method.regularization method.step

/-- The zeroth iterate of a modified Gauss--Newton method is the prescribed initial point `x₀`. -/
@[simp] theorem x_zero
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) :
    method 0 = x0 :=
  rfl

/-- The canonical modified Gauss--Newton orbit satisfies the recursion
`x_{k+1} = V_{M_k}(x_k)`. -/
@[simp] theorem x_succ
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) (k : ℕ) :
    method (k + 1) = (method.step k).point (method k) :=
  rfl

/-- The standing parameter `L₀` is positive. -/
theorem L0_pos
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) :
    0 < L0 :=
  method.L0_mem_Ioc.1

/-- The standing parameter `L₀` is bounded above by `L`. -/
theorem L0_le_L
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) :
    L0 ≤ L :=
  method.L0_mem_Ioc.2

/-- Every chosen regularization parameter is bounded below by `L₀`. -/
theorem L0_le_regularization
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) (k : ℕ) :
    L0 ≤ method.regularization k :=
  (method.regularization_mem_Icc k).1

/-- Every chosen regularization parameter also lies in the weaker interval `(0, 2L]`. -/
theorem regularization_mem_Ioc
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) (k : ℕ) :
    method.regularization k ∈ Set.Ioc (0 : ℝ) (2 * L) := by
  refine ⟨lt_of_lt_of_le method.L0_pos (method.L0_le_regularization k),
    (method.regularization_mem_Icc k).2⟩

/-- Every chosen regularization parameter is positive. -/
theorem regularization_pos
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) (k : ℕ) :
    0 < method.regularization k :=
  (method.regularization_mem_Ioc k).1

/-- Every chosen regularization parameter is bounded above by `2L`. -/
theorem regularization_le_two_mul_L
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) (k : ℕ) :
    method.regularization k ≤ 2 * L :=
  (method.regularization_mem_Ioc k).2

/-- The accepted modified Gauss--Newton trial point used at iteration `k`. -/
def acceptedTrialPoint
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) (k : ℕ) :
    E₁ :=
  (method.step k).point (method k)

/-- At the current iterate `x_k`, the selected modified Gauss--Newton step globally minimizes the
corresponding quadratic-regularized local model. -/
theorem step_isMinOn
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) (k : ℕ) :
    IsMinOn
      (quadraticallyRegularizedObjective
        (ψ[problem; φ; fun x ↦ fderiv ℝ problem x] (method k))
        (method.regularization k)
        (method k))
      Set.univ
      (method.acceptedTrialPoint k) := by
  simpa [acceptedTrialPoint] using (method.step k).isMinOn_point (method k)

/-- At the current iterate `x_k`, the chosen model value is bounded above by the current merit
value `f(x_k)`. -/
theorem step_modelValue_le_merit
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) (k : ℕ) :
    (f[(method.step k)]) (method k) ≤ meritFunctionReformulation problem φ (method k) := by
  have hmin :
      quadraticallyRegularizedObjective
          (ψ[problem; φ; fun x ↦ fderiv ℝ problem x] (method k))
          (method.regularization k)
          (method k)
          (method.acceptedTrialPoint k) ≤
        quadraticallyRegularizedObjective
          (ψ[problem; φ; fun x ↦ fderiv ℝ problem x] (method k))
          (method.regularization k)
          (method k)
          (method k) :=
    (isMinOn_univ_iff.mp (method.step_isMinOn k)) (method k)
  simpa [acceptedTrialPoint, quadraticallyRegularizedObjective_apply,
    modifiedGaussNewtonLocalModel_apply, meritFunctionReformulation] using hmin

/-- The accepted trial point at iteration `k` is exactly the next iterate `x_{k+1}`. -/
theorem acceptedTrialPoint_eq_succ
    {problem : SmoothMap}
    {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
    {L0 L : ℝ} {x0 : E₁}
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) (k : ℕ) :
    method.acceptedTrialPoint k = method (k + 1) :=
  rfl

end ModifiedGaussNewtonMethod

end
