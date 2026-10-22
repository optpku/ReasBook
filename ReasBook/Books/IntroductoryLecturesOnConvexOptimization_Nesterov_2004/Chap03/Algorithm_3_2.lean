/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_40

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/-
Primary domain: projected first-order subgradient methods for convex minimization over a simple
closed convex feasible set.

Relevant owner-style declarations sampled before refinement:
- `FirstOrderConvexMinimizationProblem` in `Definition_3_40` for the ambient feasible set,
  convex objective, and first-order oracle;
- `FirstOrderConvexMinimizationProblem.projection` and
  `FirstOrderConvexMinimizationProblem.projection_mem` in `Definition_3_40` for the canonical
  Euclidean projection back to the feasible set;
- `normalize` for the canonical normalized direction `g / ‖g‖`, taken to be `0` when `g = 0`;
- `FirstOrderConvexMinimizationProblem.normalizedSubgradientStep` in `Definition_3_40` for the
  owner projected normalized oracle step.

Owner abstraction:
- `FirstOrderConvexMinimizationProblem E`.

Source/core/bridge triage:
- `source-facing`: `IsAdmissibleSubgradientStepsizeSequence`, `SimpleSetSubgradientMethod`, and
  the recursive iterate sequence `iterates`;
- `core/canonical`: the owner one-step map
  `FirstOrderConvexMinimizationProblem.normalizedSubgradientStep`;
- `bridge/view`: the recursion clause of `iterates`, exposed by `iterates_succ`, which applies the
  owner step along the method's time-dependent stepsizes.

Primitive data:
- a feasible starting point `x₀`;
- a raw stepsize sequence.

Derived API:
- the owner normalized projected step;
- the iterate sequence and its feasibility.
- the separate admissibility predicate on the raw stepsize sequence.

Accordingly, this file keeps only the source-facing extra algorithm data and derives the ambient
feasible set, objective, and oracle from the owner problem rather than duplicating that package
locally; it also keeps the public API centered on the recursive iterate sequence instead of adding
a redundant method-specific wrapper around the owner one-step map. Admissibility of the stepsizes
is tracked separately by `IsAdmissibleSubgradientStepsizeSequence method.stepsize` rather than
being packaged as primitive run data. -/

/-- An admissible stepsize sequence for the simple-set subgradient method is positive, tends to
`0`, and has divergent partial sums. -/
structure IsAdmissibleSubgradientStepsizeSequence (h : ℕ → ℝ) : Prop where
  /-- Every stepsize is strictly positive. -/
  pos : ∀ k : ℕ, 0 < h k
  /-- The stepsizes vanish asymptotically. -/
  tendsto_zero : Filter.Tendsto h Filter.atTop (nhds 0)
  /-- The partial sums of the stepsizes diverge to `+∞`. -/
  sum_diverges :
    Filter.Tendsto (fun N : ℕ ↦ (Finset.range N).sum h) Filter.atTop Filter.atTop

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Algorithm 3.2: a simple-set subgradient method for minimizing `f` over a simple closed convex
set `Q` consists of a feasible starting point `x₀` and a stepsize sequence; the objective,
feasible set, and first-order oracle are inherited from the owner first-order convex minimization
problem. The output sequence is the recursively defined iteration obtained by applying the owner
normalized subgradient step with stepsize `h_k` at the current iterate, i.e.
`x_{k+1} = π_Q (x_k - h_k • (g(x_k) / ‖g(x_k)‖))`, where `g(x_k)` is the owner-oracle subgradient
at `x_k`. The textbook admissibility conditions on `(h_k)` are recorded separately by
`IsAdmissibleSubgradientStepsizeSequence`. -/
structure SimpleSetSubgradientMethod
    (problem : FirstOrderConvexMinimizationProblem E) where
  /-- The prescribed initial point `x₀`. -/
  x0 : E
  /-- The initial point is feasible. -/
  x0_mem : x0 ∈ problem.feasibleSet
  /-- The stepsize sequence `h₀, h₁, ...`. -/
  stepsize : ℕ → ℝ

namespace SimpleSetSubgradientMethod

variable {problem : FirstOrderConvexMinimizationProblem E}

/-- The finite prefix `(h₀, ..., h_k)` of the method's stepsize sequence, viewed in the canonical
Euclidean coordinate space used by `deltaN`. This is a thin bridge from the source-facing infinite
stepsize sequence to the finite-horizon owner API. -/
def stepsizePrefix (method : SimpleSetSubgradientMethod problem) (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 1)) :=
  (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm (fun i ↦ method.stepsize i)

/-- Evaluating the finite stepsize prefix at a coordinate recovers the corresponding stepsize. -/
@[simp] theorem stepsizePrefix_apply (method : SimpleSetSubgradientMethod problem) (k : ℕ)
    (i : Fin (k + 1)) :
    method.stepsizePrefix k i = method.stepsize i := by
  simp [stepsizePrefix]

section Projection

variable [CompleteSpace E]

/-- The output sequence of the simple-set subgradient method is defined by projecting each
normalized oracle subgradient step back to `Q`. -/
def iterates (method : SimpleSetSubgradientMethod problem) : ℕ → E
  | 0 => method.x0
  | k + 1 => problem.normalizedSubgradientStep (method.stepsize k) (iterates method k)

/-- A simple-set subgradient method can be used as its underlying sequence of iterates. -/
instance : CoeFun (SimpleSetSubgradientMethod problem) (fun _ ↦ ℕ → E) where
  coe method := iterates method

/-- The zeroth iterate of the method is the prescribed starting point `x₀`. -/
theorem iterates_zero (method : SimpleSetSubgradientMethod problem) :
    method 0 = method.x0 := rfl

/-- Each successor iterate is the owner normalized subgradient step with the current stepsize. -/
theorem iterates_succ (method : SimpleSetSubgradientMethod problem) (k : ℕ) :
    method (k + 1) =
      problem.normalizedSubgradientStep (method.stepsize k) (method k) := rfl

/-- Every iterate produced by the method belongs to the feasible set `Q`. -/
theorem iterates_mem (method : SimpleSetSubgradientMethod problem) (k : ℕ) :
    method k ∈ problem.feasibleSet := by
  induction k with
  | zero =>
      simpa [method.iterates_zero] using method.x0_mem
  | succ k _ =>
      rw [method.iterates_succ]
      exact problem.normalizedSubgradientStep_mem (method.stepsize k) (method k)

end Projection

end SimpleSetSubgradientMethod
