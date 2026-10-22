/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators ConstrainedArgmin PositiveDefMatrixNorm

variable {n N : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Algorithm 7.8 lies in the chapter's accelerated constrained-minimization / proximal-subproblem
domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem`, `argmin[Q]`, and `mem_constrainedArgmin_iff` in
  `Chap01/Definition_1_3_3`, the project owners for a feasible set together with its constrained
  minimizer set;
- `positiveDefMatrixNorm` and the notation `‖·‖[G]` in `Chap07/Definition_7_23`, the chapter
  owner of the quadratic term attached to a positive-definite matrix;
- `proximalMinimizationProblem` in `Chap06/Definition_6_26`, the chapter pattern of expressing a
  proximal subproblem through the Chapter 1 problem/argmin owners instead of a parallel argmin
  wrapper;
- `AcceleratedProjectedGradientScheme` in `Chap07/Proposition_7_16`, the nearby lower-level run
  owner that keeps the algorithmic data at a chosen-gradient / feasible-set level instead of
  baking in whole-space differentiability.

Best owner abstraction:
- source-facing: Algorithm 7.8's finite-horizon accelerated run with matrix-weighted proximal
  updates;
- core/canonical: `SetConstrainedMinimizationProblem E` and `argmin[Q]`;
- bridge/view: `acceleratedSchemeProximalMinimand`, whose quadratic term is routed through
  `positiveDefMatrixNorm` and whose constrained argmin is expressed through the Chapter 1 owner.

Primitive data:
- the constrained problem owner `problem : SetConstrainedMinimizationProblem E`;
- a chosen gradient field on `Q`;
- the prox matrix owner `G : {G // G.PosDef}`, smoothness `L`, initial point `x₀`, and iterate
  sequences `x_k`, `v_k`.

Derived API:
- the feasible set and objective through `problem`;
- the proximal minimizer set through
  `argmin[problem.feasibleSet] (acceleratedSchemeProximalMinimand ...)`.

This refinement deletes the duplicate local quadratic-form owner, stores the feasible-set /
objective pair through the Chapter 1 constrained-problem owner, and keeps the algorithm's
gradient-side hypotheses at the weaker feasible-set level already used elsewhere in the chapter.
The closedness of `Q` and positivity of the finite horizon are auxiliary assumptions for
existence/analysis results, not primitive run data of the owner itself.
-/

/-- The extrapolated point
`y_k = (k / (k + 2)) x_k + (2 / (k + 2)) v_k`
used in the accelerated scheme `S(φ, L, Q, G, x₀, N)`. -/
def acceleratedSchemeSearchPoint
    (x v : ℕ → E) (k : ℕ) : E :=
  ((k : ℝ) / (k + 2)) • x k + ((2 : ℝ) / (k + 2)) • v k

-- Proof sketch: unfold `acceleratedSchemeSearchPoint`.
/-- Evaluating `acceleratedSchemeSearchPoint x v k` recovers the displayed convex combination
defining `y_k`. -/
theorem acceleratedSchemeSearchPoint_eq
    (x v : ℕ → E) (k : ℕ) :
    acceleratedSchemeSearchPoint x v k =
      ((k : ℝ) / (k + 2)) • x k + ((2 : ℝ) / (k + 2)) • v k :=
  rfl

/-- The weighted gradient sum
`∑_{i=0}^k ((i + 1) / 2) ∇φ(y_i)`
appearing in the proximal subproblem of Algorithm 7.8. -/
def acceleratedSchemeWeightedGradientSum
    (gradient : E → E) (x v : ℕ → E) (k : ℕ) : E :=
  ∑ i ∈ Finset.range (k + 1),
    ((((i : ℝ) + 1) / 2) : ℝ) • gradient (acceleratedSchemeSearchPoint x v i)

-- Proof sketch: unfold `acceleratedSchemeWeightedGradientSum`.
/-- Expanding `acceleratedSchemeWeightedGradientSum gradient x v k` gives the finite sum
`∑_{i=0}^k ((i + 1) / 2) gradient(y_i)`. -/
theorem acceleratedSchemeWeightedGradientSum_eq_sum
    (gradient : E → E) (x v : ℕ → E) (k : ℕ) :
    acceleratedSchemeWeightedGradientSum gradient x v k =
      ∑ i ∈ Finset.range (k + 1),
        ((((i : ℝ) + 1) / 2) : ℝ) • gradient (acceleratedSchemeSearchPoint x v i) :=
  rfl

/-- The proximal minimand
`v ↦ ⟪∑_{i=0}^k ((i + 1) / 2) ∇φ(y_i), v - x₀⟫ + (L / 2) ‖v - x₀‖_G^2`
from the inner minimization step of Algorithm 7.8. -/
def acceleratedSchemeProximalMinimand
    (gradient : E → E) (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (L : NNRealˣ) (x0 : E)
    (x v : ℕ → E) (k : ℕ) (u : E) : ℝ :=
  inner ℝ (acceleratedSchemeWeightedGradientSum gradient x v k) (u - x0) +
    (((L : ℝ) / 2) : ℝ) * ‖u - x0‖[G] ^ (2 : ℕ)

-- Proof sketch: unfold `acceleratedSchemeProximalMinimand`.
/-- Evaluating `acceleratedSchemeProximalMinimand gradient G L x0 x v k` at `u` gives the linear
term against `∑_{i=0}^k ((i + 1) / 2) gradient(y_i)` plus the quadratic penalty
`(L / 2) ‖u - x₀‖_G^2`. -/
theorem acceleratedSchemeProximalMinimand_apply
    (gradient : E → E) (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (L : NNRealˣ) (x0 : E)
    (x v : ℕ → E) (k : ℕ) (u : E) :
    acceleratedSchemeProximalMinimand gradient G L x0 x v k u =
      inner ℝ (acceleratedSchemeWeightedGradientSum gradient x v k) (u - x0) +
        (((L : ℝ) / 2) : ℝ) * ‖u - x0‖[G] ^ (2 : ℕ) :=
  rfl

/-- Algorithm 7.8: the accelerated scheme `S(φ, L, Q, G, x₀, N)` for a differentiable convex
objective `φ` on a feasible set `Q ⊆ ℝⁿ` with positive-definite weight matrix `G` and parameter
`L > 0` consists of sequences `x_k` and `v_k` started from `x₀`, such that for every
`k = 0, …, N - 1` one has
`y_k = (k / (k + 2)) x_k + (2 / (k + 2)) v_k`,
`v_{k+1} ∈ arg min_{v ∈ Q} [⟪∑_{i=0}^k ((i + 1) / 2) ∇φ(y_i), v - x₀⟫ + (L / 2) ‖v - x₀‖_G^2]`,
and
`x_{k+1} = (k / (k + 2)) x_k + (2 / (k + 2)) v_{k+1}`.
The owner stores only the run-defining data and update laws; auxiliary assumptions such as
closedness of `Q` or positivity of `N` belong to theorem-level bridges and analyses. The output
of the scheme is `x_N`. -/
structure AcceleratedConvexMinimizationScheme (n N : ℕ) where
  /-- The constrained problem owner supplying the feasible set `Q ⊆ ℝⁿ` and the objective
  `φ : ℝⁿ → ℝ`. -/
  problem : SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))
  /-- The objective is convex on `Q`. -/
  objective_convex : ConvexOn ℝ problem.feasibleSet problem
  /-- A chosen gradient field for the objective on `Q`. -/
  gradient : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  /-- The chosen field agrees with the gradient of the objective at each feasible point. -/
  gradient_hasGradientAt {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ problem.feasibleSet) :
      HasGradientAt problem (gradient x) x
  /-- The positive-definite matrix owner defining the proximal quadratic term. -/
  metricMatrix : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}
  /-- The smoothness parameter `L > 0`, encoded canonically as a positive nonnegative real. -/
  smoothness : NNRealˣ
  /-- The initial point `x₀`. -/
  initialPoint : EuclideanSpace ℝ (Fin n)
  /-- The initial point belongs to the feasible set. -/
  initialPoint_mem : initialPoint ∈ problem.feasibleSet
  /-- The primal iterates `x₀, x₁, x₂, ...`. -/
  x : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The auxiliary points `v₀, v₁, v₂, ...`. -/
  v : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The primal sequence starts at `x₀`. -/
  x_zero : x 0 = initialPoint
  /-- The auxiliary sequence starts at `v₀ = x₀`. -/
  v_zero : v 0 = initialPoint
  /-- For each `k = 0, …, N - 1`, the successor point `v_{k+1}` minimizes the proximal
  objective over `Q`. -/
  v_succ_mem_argmin (k : ℕ) (hk : k < N) :
      v (k + 1) ∈
        argmin[problem.feasibleSet]
          (acceleratedSchemeProximalMinimand gradient metricMatrix smoothness initialPoint x v k)
  /-- For each `k = 0, …, N - 1`, the successor iterate is the convex combination
  `x_{k+1} = (k / (k + 2)) x_k + (2 / (k + 2)) v_{k+1}`. -/
  x_succ (k : ℕ) (hk : k < N) :
      x (k + 1) =
        ((k : ℝ) / (k + 2)) • x k + ((2 : ℝ) / (k + 2)) • v (k + 1)

namespace AcceleratedConvexMinimizationScheme

/-- The feasible set of an accelerated scheme run is convex. -/
theorem convexSet
    (scheme : AcceleratedConvexMinimizationScheme n N) :
    Convex ℝ scheme.problem.feasibleSet :=
  scheme.objective_convex.1

/-- A run of Algorithm 7.8 can be used as its iterate sequence `x_k`. -/
instance : CoeFun (AcceleratedConvexMinimizationScheme n N)
    (fun _ ↦ ℕ → EuclideanSpace ℝ (Fin n)) where
  coe scheme := scheme.x

/-- The output point of Algorithm 7.8 is the final iterate `x_N`. -/
def outputPoint (scheme : AcceleratedConvexMinimizationScheme n N) :
    EuclideanSpace ℝ (Fin n) :=
  scheme.x N

/-- For each `k < N`, the successor auxiliary point `v_{k+1}` belongs to the proximal argmin set
over `Q`. -/
-- Proof sketch: this is exactly the `v_succ_mem_argmin` field of the structure.
theorem v_succ_mem_argmin_set
    (scheme : AcceleratedConvexMinimizationScheme n N) {k : ℕ} (hk : k < N) :
    scheme.v (k + 1) ∈
      argmin[scheme.problem.feasibleSet]
        (acceleratedSchemeProximalMinimand
          scheme.gradient
          scheme.metricMatrix
          scheme.smoothness
          scheme.initialPoint
          scheme.x
          scheme.v
          k) :=
  scheme.v_succ_mem_argmin k hk

/-- The output point of Algorithm 7.8 is the final iterate `x_N`. -/
-- Proof sketch: unfold `outputPoint`.
theorem outputPoint_eq
    (scheme : AcceleratedConvexMinimizationScheme n N) :
    scheme.outputPoint = scheme.x N :=
  rfl

end AcceleratedConvexMinimizationScheme

end
