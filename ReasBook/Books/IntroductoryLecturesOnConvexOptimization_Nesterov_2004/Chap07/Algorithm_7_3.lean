/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators ConstrainedArgmin

variable {m n N : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-
Algorithm 7.3 lies in the chapter's support-function smoothing / accelerated proximal-update
domain.

Sampled owner-style declarations:
- `supportFunctionSmoothingMap` in `Definition_7_15`, the chapter bridge from a matrix model to
  the canonical Chapter 6 smoothing owner;
- `ConvexBody.gammaOne` in `Definition_7_11`, the chapter owner of the support coefficient
  `γ₁(F)`;
- `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the chapter owner of the
  regularized dual argmax set;
- `acceleratedSchemeSearchPoint` in `Algorithm_7_8`, the chapter owner of the common extrapolated
  point `y_k = (k / (k + 2)) x_k + (2 / (k + 2)) v_k`;
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner and
  bridge for constrained minimizer sets;
- mathlib `IsMinOn`, the canonical optimization predicate for the primal step.

Best owner abstraction:
- source-facing: `SupportFunctionSmoothingMethod`, with the support-function data and dual
  sequence `ν_k`;
- core/canonical: `smoothedPrimalObjectiveArgmax`, `acceleratedSchemeSearchPoint`, and
  `argmin[Q]`;
- bridge/view: `supportFunctionSmoothingParameter`,
  `supportFunctionSmoothingDualWeightSum`, and
  `supportFunctionSmoothingPrimalMinimand`.

Primitive data:
- the support-function problem owner `problem : SupportFunctionOptimizationProblem m n`,
  the source radius `R`, the input point `x₀`, and the sequences `x_k`, `v_k`, `ν_k`.

Derived API:
- the support data `A` and `Q₂`, reused from `problem`;
- the convex-body bridge `problem.supportBody`, derived from the problem's `Q₂` data;
- the localized feasible set `Q₁(R)`, reused from `boundedFeasibleSet problem.Q1 x₀ R`;
- the support coefficient `γ₁(F)`, reused from `problem.supportBody.gammaOne`;
- the smoothing parameter `μ`;
- the extrapolated point `y_k`, reused from the chapter owner `acceleratedSchemeSearchPoint`;
- the weighted dual sum and source-specific primal minimand;
- the dual argmax set, reused from `smoothedPrimalObjectiveArgmax` through
  `supportFunctionSmoothingMap` and `quadraticDistanceTo 0`;
- the primal argmin set, reused directly from the Chapter 1 owner `argmin[Q]`;
- the output point `x̄ = x_N`.

This refinement keeps the source-facing Algorithm 7.3 objects, deletes the duplicate local
`γ₁(F)` owner and the duplicate local dual-maximization owner layer, and states the method
directly in terms of the canonical chapter owners for the extrapolated point, the dual argmax
step, and the constrained primal argmin step.
-/

/-- The smoothing parameter `μ = 2R / (γ₁(F) √(N (N + 1)))` used by Method `S_N(R)`. -/
def supportFunctionSmoothingParameter (R gammaOne : ℝ) (N : ℕ) : ℝ :=
  (2 * R) / (gammaOne * Real.sqrt (N * (N + 1)))

/-- Expanding `supportFunctionSmoothingParameter R gammaOne N` recovers the textbook formula
`μ = 2R / (γ₁(F) √(N (N + 1)))`. -/
-- Proof sketch: unfold `supportFunctionSmoothingParameter`.
theorem supportFunctionSmoothingParameter_eq (R gammaOne : ℝ) (N : ℕ) :
    supportFunctionSmoothingParameter R gammaOne N =
      (2 * R) / (gammaOne * Real.sqrt (N * (N + 1))) := by
  -- The companion theorem is exactly the defining equation of the parameter.
  rfl

/-- The weighted dual sum `∑_{i=0}^k ((i + 1) / 2) ν_i` appearing in the primal proximal
subproblem of Method `S_N(R)`. -/
def supportFunctionSmoothingDualWeightSum
    (nu : ℕ → Eₘ) (k : ℕ) : Eₘ :=
  ∑ i ∈ Finset.range (k + 1), (((i : ℝ) + 1) / 2) • nu i

/-- Expanding `supportFunctionSmoothingDualWeightSum nu k` gives the finite sum
`∑_{i=0}^k ((i + 1) / 2) ν_i`. -/
-- Proof sketch: unfold `supportFunctionSmoothingDualWeightSum`.
theorem supportFunctionSmoothingDualWeightSum_eq_sum
    (nu : ℕ → Eₘ) (k : ℕ) :
    supportFunctionSmoothingDualWeightSum nu k =
      ∑ i ∈ Finset.range (k + 1), (((i : ℝ) + 1) / 2) • nu i := by
  -- The weighted sum theorem is just the unfolded definition.
  rfl

/-- The primal proximal minimand
`x ↦ (1 / (2μ)) ‖x - x₀‖² + ⟪A x, ∑_{i=0}^k ((i + 1) / 2) ν_i⟫`. -/
def supportFunctionSmoothingPrimalMinimand
    (A : Matrix (Fin m) (Fin n) ℝ) (μ : ℝ) (x0 : Eₙ)
    (nu : ℕ → Eₘ) (k : ℕ) (x : Eₙ) : ℝ :=
  (1 / (2 * μ)) * ‖x - x0‖ ^ (2 : ℕ) +
    inner ℝ (A.toEuclideanLin x) (supportFunctionSmoothingDualWeightSum nu k)

/-- Evaluating `supportFunctionSmoothingPrimalMinimand A μ x0 nu k` at `x` gives the quadratic
proximal term around `x₀` plus the linear term against
`∑_{i=0}^k ((i + 1) / 2) ν_i`. -/
-- Proof sketch: unfold `supportFunctionSmoothingPrimalMinimand`.
theorem supportFunctionSmoothingPrimalMinimand_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (μ : ℝ) (x0 : Eₙ)
    (nu : ℕ → Eₘ) (k : ℕ) (x : Eₙ) :
    supportFunctionSmoothingPrimalMinimand A μ x0 nu k x =
      (1 / (2 * μ)) * ‖x - x0‖ ^ (2 : ℕ) +
        inner ℝ (A.toEuclideanLin x) (supportFunctionSmoothingDualWeightSum nu k) := by
  -- Evaluating the minimand reproduces its defining quadratic-plus-linear formula.
  rfl

/-- Algorithm 7.3 [Chapter7_2.json:24]: Method `S_N(R)` for the direct use of the support
function uses a support-function problem `problem` with matrix `A` and support set `Q₂`, the
localized
feasible set `Q₁(R) = boundedFeasibleSet problem.Q1 x₀ R`, the radius parameter `R`, the input
point `x₀`, and sequences `x_k`, `v_k`, and `ν_k`, with `x₀ = v₀`, and a positive horizon
`N ≥ 1`, such that for every `k = 0, …, N - 1` one has
`y_k = (k / (k + 2)) x_k + (2 / (k + 2)) v_k`, the vector `ν_k` belongs to
`arg max_{u ∈ Q₂} {⟪A y_k, u⟫ - (μ / 2) ‖u‖²}`, the point `v_{k+1}` belongs to
`arg min_{x ∈ Q₁(R)} {(1 / (2μ)) ‖x - x₀‖² + ⟪A x, ∑_{i=0}^k ((i + 1) / 2) ν_i⟫}`,
and `x_{k+1} = (k / (k + 2)) x_k + (2 / (k + 2)) v_{k+1}`, where
`μ = 2R / (γ₁(F) √(N (N + 1)))` with the canonical Chapter 7 coefficient
`γ₁(F) = problem.supportBody.gammaOne`. -/
structure SupportFunctionSmoothingMethod (m n N : ℕ) where
  /-- The support-function optimization problem supplying `A`, `Q₂`, and `Q₁`. -/
  problem : SupportFunctionOptimizationProblem m n
  /-- The radius parameter `R` supplied to the method. -/
  radius : ℝ
  /-- The input point `x₀`. -/
  initialPoint : EuclideanSpace ℝ (Fin n)
  /-- The primal iterates `x₀, x₁, x₂, ...`. -/
  x : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The auxiliary proximal points `v₀, v₁, v₂, ...`. -/
  v : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The dual maximizers `ν₀, ν₁, ν₂, ...`. -/
  nu : ℕ → EuclideanSpace ℝ (Fin m)
  /-- The initial iterate is the input point `x₀`. -/
  x_zero : x 0 = initialPoint
  /-- The initial proximal point is the input point `x₀`. -/
  v_zero : v 0 = initialPoint
  /-- The source method uses a positive iteration horizon `N ≥ 1`. -/
  iteration_count_pos : 1 ≤ N
  /-- For each `k = 0, …, N - 1`, the chosen dual point `ν_k` maximizes the regularized dual
  objective over `Q₂` at the extrapolated point `y_k`. -/
  nu_mem_argmax :
    ∀ k : ℕ, k < N →
      nu k ∈
        smoothedPrimalObjectiveArgmax
          (supportFunctionSmoothingMap problem.A) problem.Q2
          0
          (quadraticDistanceTo (0 : EuclideanSpace ℝ (Fin m)))
          (supportFunctionSmoothingParameter radius problem.supportBody.gammaOne N)
          (acceleratedSchemeSearchPoint x v k)
  /-- For each `k = 0, …, N - 1`, the successor proximal point `v_{k+1}` minimizes the proximal
  primal objective over `Q₁(R)`. -/
  v_succ_mem_argmin :
    ∀ k : ℕ, k < N →
      v (k + 1) ∈
        argmin[boundedFeasibleSet problem.Q1 initialPoint radius]
          (supportFunctionSmoothingPrimalMinimand problem.A
            (supportFunctionSmoothingParameter radius problem.supportBody.gammaOne N)
            initialPoint nu
            k)
  /-- For each `k = 0, …, N - 1`, the successor iterate is the convex combination
  `x_{k+1} = (k / (k + 2)) x_k + (2 / (k + 2)) v_{k+1}`. -/
  x_succ :
    ∀ k : ℕ, k < N →
      x (k + 1) =
        ((k : ℝ) / (k + 2)) • x k + ((2 : ℝ) / (k + 2)) • v (k + 1)

namespace SupportFunctionSmoothingMethod

/-- A support-function smoothing method can be used as its iterate sequence `x_k`. -/
instance : CoeFun (SupportFunctionSmoothingMethod m n N) (fun _ ↦ ℕ → Eₙ) where
  coe method := method.x

section

variable (method : SupportFunctionSmoothingMethod m n N)

local notation "Q₂" => method.problem.supportBody

/-- The smoothing parameter `μ = 2R / (γ₁(F) √(N (N + 1)))` attached to a run of Algorithm 7.3. -/
def smoothingParameter : ℝ :=
  supportFunctionSmoothingParameter method.radius (Q₂).gammaOne N

/-- Expanding `method.smoothingParameter` recovers the textbook parameter formula. -/
-- Proof sketch: unfold `SupportFunctionSmoothingMethod.smoothingParameter`.
theorem smoothingParameter_eq :
    method.smoothingParameter =
      supportFunctionSmoothingParameter method.radius (Q₂).gammaOne N := by
  -- The method-level parameter is defined by this support-function formula.
  rfl

end

/-- The specialized smoothed primal objective attached to the support-function data of
Algorithm 7.3. -/
def smoothedObjective (method : SupportFunctionSmoothingMethod m n N) : Eₙ → ℝ :=
  smoothedPrimalObjective
    (supportFunctionSmoothingMap method.problem.A)
    method.problem.Q2
    0
    0
    (quadraticDistanceTo (0 : Eₘ))
    method.smoothingParameter

/-- Evaluating `method.smoothedObjective` at `x` expands to the Chapter 6 smoothed support-function
objective specialized by the method's support data. -/
-- Proof sketch: unfold `SupportFunctionSmoothingMethod.smoothedObjective`.
theorem smoothedObjective_apply
    (method : SupportFunctionSmoothingMethod m n N) (x : Eₙ) :
    method.smoothedObjective x =
      smoothedPrimalObjective
        (supportFunctionSmoothingMap method.problem.A)
        method.problem.Q2
        0
        0
        (quadraticDistanceTo (0 : Eₘ))
        method.smoothingParameter
        x := by
  -- Evaluating the wrapper objective unfolds to the specialized Chapter 6 objective.
  rfl

/-- The output point `x̄` of Method `S_N(R)`, defined to be the final iterate `x_N`. -/
def outputPoint (method : SupportFunctionSmoothingMethod m n N) : Eₙ :=
  method.x N

/-- For each `k < N`, the selected dual point `ν_k` belongs to the regularized dual argmax set at
the extrapolated point `y_k`. -/
-- Proof sketch: this is exactly the `nu_mem_argmax` field of the structure.
theorem nu_mem_argmax_set
    (method : SupportFunctionSmoothingMethod m n N) {k : ℕ} (hk : k < N) :
    method.nu k ∈
      smoothedPrimalObjectiveArgmax
        (supportFunctionSmoothingMap method.problem.A)
        method.problem.Q2
        0
        (quadraticDistanceTo (0 : EuclideanSpace ℝ (Fin m)))
        method.smoothingParameter
        (acceleratedSchemeSearchPoint method.x method.v k) := by
  -- This wrapper is the structure field, with the method parameter spelling unfolded.
  simpa [SupportFunctionSmoothingMethod.smoothingParameter] using method.nu_mem_argmax k hk

/-- For each `k < N`, the successor proximal point `v_{k+1}` belongs to the proximal primal
argmin set over `Q₁(R)`. -/
-- Proof sketch: this is exactly the `v_succ_mem_argmin` field of the structure.
theorem v_succ_mem_argmin_set
    (method : SupportFunctionSmoothingMethod m n N) {k : ℕ} (hk : k < N) :
    method.v (k + 1) ∈
      argmin[boundedFeasibleSet method.problem.Q1 method.initialPoint method.radius]
        (supportFunctionSmoothingPrimalMinimand method.problem.A
          method.smoothingParameter
          method.initialPoint method.nu
          k) := by
  -- This wrapper is the structure field, again after unfolding the method parameter.
  simpa [SupportFunctionSmoothingMethod.smoothingParameter] using method.v_succ_mem_argmin k hk

/-- The output point `x̄` of Method `S_N(R)` is the final iterate `x_N`. -/
-- Proof sketch: unfold `outputPoint`.
theorem outputPoint_eq
    (method : SupportFunctionSmoothingMethod m n N) :
    method.outputPoint = method.x N := by
  -- The output point is defined to be the final iterate.
  rfl

end SupportFunctionSmoothingMethod
