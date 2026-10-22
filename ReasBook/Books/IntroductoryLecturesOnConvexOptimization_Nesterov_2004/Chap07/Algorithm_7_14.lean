/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/- Algorithm 7.14 lies in the chapter's primal barrier-subgradient / relative-scale maximization
domain.

Mandatory domain-style sampling:
- `PrimalUpdateScheme` and `primalUpdatePayoff` in `Algorithm_7_13`, the neighboring owner pattern
  where primitive positive parameters are stored on `NNRealˣ`, the trajectory lives in the
  feasible subtype, and the displayed textbook objective is kept as derived API;
- `DualBarrierSubgradientMethod` in `Algorithm_7_12`, the chapter's dual barrier-subgradient owner
  showing that the barrier-subgradient domain already uses a dedicated owner rather than ad hoc
  iterate-plus-feasibility wrappers;
- mathlib `IsMaxOn`, the canonical maximizer predicate used throughout nearby Chapter 7 files;
- `barrierSubgradientDirection` below, the source-facing scaled-gradient owner reused by the later
  uncertain-environment variant.

Best owner abstraction:
- source-facing: Algorithm 7.14's primal barrier-subgradient run maximizing the displayed
  relative-scale objective over `P₀`;
- core/canonical: `IsMaxOn`, the positive-real owner `NNRealˣ`, and a feasible trajectory
  `ℕ → P₀`;
- bridge/view: the displayed step objective `barrierSubgradientStepObjective`.

Primitive data:
- the feasible set `P₀`, objective pair `F`, `ψ`, positive parameter `v`, initial point `x₀ ∈ P₀`,
  and feasible iterate sequence `x₀, x₁, x₂, ...`;
- differentiability and positivity of `ψ` on `P₀`;
- the stepwise maximizer condition for the displayed objective.

Derived API:
- coercion of a method to its underlying iterate sequence in `E`;
- the step objective attached to a method;
- feasibility of the initial point and all iterates.

The previous version stored feasibility and positivity as separate primitive fields while keeping
the trajectory in the ambient space `E`. In this domain, those are not primitive mathematical
choices: `x₀ ∈ P₀` and `x_k ∈ P₀` are better carried directly by subtype data, and the positive
algorithm parameter is better carried by the project-standard owner `NNRealˣ`. This refinement
keeps Algorithm 7.14 source-facing while shrinking the public data to the canonical core.
-/

/-- The positive barrier penalty weight used at iteration `k` in Algorithm 7.14. -/
def barrierSubgradientPenaltyWeight (v : NNRealˣ) (k : ℕ) : ℝ :=
  (Real.sqrt (v : ℝ) + Real.sqrt ((k + 1 : ℕ) : ℝ)) /
    Real.sqrt ((v : ℝ) * ((k + 1 : ℕ) : ℝ))

/-- The scaled barrier gradient `∇ ψ(x) / ψ(x)` appearing in the relative-scale linearization. -/
def barrierSubgradientDirection (ψ : E → ℝ) (x : E) : E :=
  (ψ x)⁻¹ • ∇ ψ x

/-- Expanding `barrierSubgradientDirection ψ x` gives the scaled gradient
`(1 / ψ(x)) ∇ ψ(x)`. -/
theorem barrierSubgradientDirection_def (ψ : E → ℝ) (x : E) :
    barrierSubgradientDirection ψ x = (ψ x)⁻¹ • ∇ ψ x :=
  rfl

/-- The step objective optimized at iteration `k` in the barrier subgradient scheme. -/
def barrierSubgradientStepObjective
    {P0 : Set E} (F ψ : E → ℝ) (v : NNRealˣ) (x0 : P0) (history : ℕ → P0) (k : ℕ) :
    E → ℝ :=
  fun x ↦
    (1 / ((k : ℝ) + 1)) *
        ∑ i ∈ Finset.range (k + 1),
          inner ℝ (barrierSubgradientDirection ψ (history i : E)) (x - (history i : E)) -
      barrierSubgradientPenaltyWeight v k * (F x - F x0)

/-- Evaluating `barrierSubgradientStepObjective` recovers the displayed maximization objective from
Algorithm 7.14. -/
theorem barrierSubgradientStepObjective_apply
    {P0 : Set E} (F ψ : E → ℝ) (v : NNRealˣ) (x0 : P0) (history : ℕ → P0) (k : ℕ) (x : E) :
    barrierSubgradientStepObjective F ψ v x0 history k x =
      (1 / ((k : ℝ) + 1)) *
          ∑ i ∈ Finset.range (k + 1),
            inner ℝ (barrierSubgradientDirection ψ (history i : E)) (x - (history i : E)) -
        barrierSubgradientPenaltyWeight v k * (F x - F x0) :=
  rfl

/-- Algorithm 7.14: a barrier subgradient method for maximizing a positive differentiable function
`ψ` over a feasible set `P₀` relative to a reference function `F` and positive parameter `v`
consists of an initial point `x₀ ∈ P₀` and a feasible iterate sequence `x_k` such that each
successor `x_{k+1}` maximizes the displayed relative-scale model over `P₀`. -/
structure BarrierSubgradientMethod
    (P0 : Set E) (F ψ : E → ℝ) (v : NNRealˣ) (x0 : P0) where
  /-- The barrier function `ψ` is differentiable on `P₀`. -/
  ψ_differentiableOn : DifferentiableOn ℝ ψ P0
  /-- The barrier function `ψ` is strictly positive on `P₀`. -/
  ψ_pos : ∀ ⦃x : E⦄, x ∈ P0 → 0 < ψ x
  /-- The feasible iterate sequence `x₀, x₁, x₂, ...`. -/
  iterate : ℕ → P0
  /-- The zeroth iterate is the prescribed initial point `x₀`. -/
  iterate_zero : iterate 0 = x0
  /-- Each successor iterate `x_{k+1}` maximizes the step objective over `P₀`. -/
  step_isMax :
    ∀ k : ℕ,
      IsMaxOn
        (barrierSubgradientStepObjective F ψ v x0 iterate k)
        P0
        (iterate (k + 1) : E)

namespace BarrierSubgradientMethod

/-- A barrier subgradient method can be used as its iterate sequence `x_k`. -/
instance {P0 : Set E} {F ψ : E → ℝ} {v : NNRealˣ} {x0 : P0} :
    CoeFun (BarrierSubgradientMethod P0 F ψ v x0) (fun _ ↦ ℕ → E) where
  coe method k := method.iterate k

/-- The prescribed initial point belongs to the feasible set `P₀`. -/
theorem x0_mem
    {P0 : Set E} {F ψ : E → ℝ} {v : NNRealˣ} {x0 : P0}
    (_method : BarrierSubgradientMethod P0 F ψ v x0) :
    (x0 : E) ∈ P0 :=
  x0.property

/-- The step objective attached to a barrier subgradient method at time `k`. -/
def stepObjective
    {P0 : Set E} {F ψ : E → ℝ} {v : NNRealˣ} {x0 : P0}
    (method : BarrierSubgradientMethod P0 F ψ v x0) (k : ℕ) : E → ℝ :=
  barrierSubgradientStepObjective F ψ v x0 method.iterate k

/-- Expanding `method.stepObjective k` gives the objective from Algorithm 7.14 evaluated on the
iterate history of `method`. -/
theorem stepObjective_def
    {P0 : Set E} {F ψ : E → ℝ} {v : NNRealˣ} {x0 : P0}
    (method : BarrierSubgradientMethod P0 F ψ v x0) (k : ℕ) :
    method.stepObjective k = barrierSubgradientStepObjective F ψ v x0 method.iterate k :=
  rfl

/-- Every iterate of a barrier subgradient method belongs to the feasible set `P₀`. -/
theorem iterate_mem
    {P0 : Set E} {F ψ : E → ℝ} {v : NNRealˣ} {x0 : P0}
    (method : BarrierSubgradientMethod P0 F ψ v x0) (k : ℕ) :
    (method.iterate k : E) ∈ P0 :=
  (method.iterate k).property

/-- Every successor iterate of a barrier subgradient method belongs to the feasible set `P₀`. -/
theorem iterates_succ_mem
    {P0 : Set E} {F ψ : E → ℝ} {v : NNRealˣ} {x0 : P0}
    (method : BarrierSubgradientMethod P0 F ψ v x0) (k : ℕ) :
    method (k + 1) ∈ P0 :=
  (method.iterate (k + 1)).property

end BarrierSubgradientMethod

end
