/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 7.16 lies in the chapter's uncertain-environment barrier-subgradient /
relative-scale maximization domain.

Mandatory domain-style sampling:
- `BarrierSubgradientMethod`, `barrierSubgradientPenaltyWeight`, and
  `barrierSubgradientDirection` in `Algorithm_7_14`, the neighboring Chapter 7 owner pattern for
  barrier-subgradient maximization with a positive penalty parameter and a feasible trajectory;
- `PrimalUpdateScheme` in `Algorithm_7_13`, the chapter owner pattern where the iterate sequence
  lives in the feasible subtype instead of ambient-space data plus separate feasibility fields;
- `dynamicStrategyAverageRateOfGrowth` in `Definition_7_74`, the nearby finite-horizon Chapter 7
  owner pattern where the primitive data are indexed by `Fin (N + 1)` instead of by arbitrary
  `ℕ`-tails;
- mathlib `IsMaxOn`, the canonical maximizer predicate used throughout nearby Chapter 7 files.

Best owner abstraction:
- source-facing: Algorithm 7.16's uncertain-environment barrier-subgradient run over a fixed
  horizon `N`;
- core/canonical: `IsMaxOn`, the project-standard positive parameter owner `NNRealˣ`, the
  finite-horizon payoff family `Fin N → E → ℝ`, and a feasible trajectory `Fin (N + 1) → P`;
- bridge/view: the displayed step objective with the varying payoff family `ψ_i`, with the step
  index restricted to `k : Fin N` and the objective sum taken over the finite initial segment
  `Finset.Iic k`.

Primitive data:
- the feasible set `P`, reference function `F`, positive penalty parameter `ν`, initial point
  `x₀ ∈ P`, payoff family `ψ₀, …, ψ_{N-1}`, horizon `N`, and feasible iterate trace
  `x₀, …, x_N`;
- differentiability and strict positivity of each sampled payoff `ψ_i` on `P`;
- the stepwise maximizer condition for the displayed uncertain-environment objective at each
  stage `k = 0, …, N - 1`.

Derived API:
- coercion of a method to its finite iterate trace `Fin (N + 1) → E`;
- the step objective attached to a method, defined only for `k : Fin N`;
- feasibility of the initial point, every iterate, and every successor iterate;
- barrier assumptions on `F`, which belong to downstream theorem layers once actual
  self-concordant geometry is used.

The previous version weakened the owner layer in two ways: it stored the finite-horizon run as an
arbitrary infinite family `ℕ → P`, and it exposed `ψ`, `method k`, and `stepObjective k` for all
natural indices even though Algorithm 7.16 only specifies the data up to the horizon `N`. This
refinement keeps the same source-facing finite run, but moves the primitive data to the genuine
finite-horizon owner layer: the payoffs are indexed by `Fin N`, the iterates by `Fin (N + 1)`,
and the maximizer certificates by `Fin N`. That removes dependence on arbitrary tail choices
without changing the mathematics on the source-defined horizon.
-/

/-- The step objective optimized at stage `k : Fin N` in the uncertain-environment barrier
method. The finite sum is taken over the initial segment `{ i : Fin N | i ≤ k } = Finset.Iic k`,
so only the source-defined payoff data `ψ₀, …, ψ_k` and iterate history `x₀, …, x_k` enter. -/
def uncertainEnvironmentBarrierStepObjective
    {P : Set E} {N : ℕ} (F : E → ℝ) (ψ : Fin N → E → ℝ) (ν : NNRealˣ) (x0 : P)
    (history : Fin (N + 1) → P) (k : Fin N) :
    E → ℝ :=
  fun x ↦
    (1 / ((k : ℝ) + 1)) *
        (Finset.sum (Finset.Iic k) fun i ↦
          inner ℝ (barrierSubgradientDirection (ψ i) (history i.castSucc : E))
            (x - (history i.castSucc : E))) -
      barrierSubgradientPenaltyWeight ν k * (F x - F x0)

-- Proof sketch: unfold `uncertainEnvironmentBarrierStepObjective`; this is exactly the displayed
-- maximization functional, rewritten on the finite-horizon owner surface where the stage sum is
-- the initial segment `Finset.Iic k`.
/-- Evaluating `uncertainEnvironmentBarrierStepObjective F ψ ν x0 history k` recovers the
finite-horizon Algorithm 7.16 objective at stage `k`. -/
theorem uncertainEnvironmentBarrierStepObjective_apply
    {P : Set E} {N : ℕ} (F : E → ℝ) (ψ : Fin N → E → ℝ) (ν : NNRealˣ) (x0 : P)
    (history : Fin (N + 1) → P) (k : Fin N) (x : E) :
    uncertainEnvironmentBarrierStepObjective F ψ ν x0 history k x =
      (1 / ((k : ℝ) + 1)) *
          (Finset.sum (Finset.Iic k) fun i ↦
            inner ℝ (barrierSubgradientDirection (ψ i) (history i.castSucc : E))
              (x - (history i.castSucc : E))) -
        barrierSubgradientPenaltyWeight ν k * (F x - F x0) :=
  rfl

/-- Algorithm 7.16: given an initial point `x₀ ∈ P`, a finite-horizon payoff family
`ψ₀, …, ψ_{N-1}`, and a horizon `N`, an uncertain-environment barrier subgradient method is a
finite run `x₀, …, x_N` such that for each stage `k = 0, …, N - 1`, the next iterate
`x_{k+1}` maximizes the displayed averaged relative-scale model with barrier penalty over `P`.
The self-concordant-barrier hypothesis on `F` is part of later theorem layers, not primitive run
data. -/
structure UncertainEnvironmentBarrierSubgradientMethod
    (P : Set E) (F : E → ℝ) (ν : NNRealˣ) (N : ℕ) (ψ : Fin N → E → ℝ) (x0 : P) where
  /-- Each payoff `ψ_i` from the finite horizon is differentiable on the feasible set `P`. -/
  ψ_differentiableOn (i : Fin N) : DifferentiableOn ℝ (ψ i) P
  /-- Each payoff `ψ_i` from the finite horizon is strictly positive on the feasible set `P`. -/
  ψ_pos (i : Fin N) {x : E} (hx : x ∈ P) : 0 < ψ i x
  /-- The finite feasible iterate trace `x₀, …, x_N`. -/
  iterate : Fin (N + 1) → P
  /-- The zeroth iterate is the prescribed initial point `x₀`. -/
  iterate_zero : iterate 0 = x0
  /-- For each stage `k : Fin N`, the successor iterate `x_{k+1}` maximizes the averaged
  relative-scale objective with barrier penalty over `P`. Feasibility is carried by the subtype
  trace `iterate : Fin (N + 1) → P`. -/
  step_isMax (k : Fin N) :
    IsMaxOn
      (uncertainEnvironmentBarrierStepObjective F ψ ν x0 iterate k)
      P
      (iterate k.succ : E)

namespace UncertainEnvironmentBarrierSubgradientMethod

/-- A run of Algorithm 7.16 can be used as its finite iterate trace `x₀, …, x_N`. -/
instance
    {P : Set E} {F : E → ℝ} {ν : NNRealˣ} {N : ℕ} {ψ : Fin N → E → ℝ} {x0 : P} :
    CoeFun (UncertainEnvironmentBarrierSubgradientMethod P F ν N ψ x0)
      (fun _ ↦ Fin (N + 1) → E) where
  coe method k := method.iterate k

/-- The prescribed initial point belongs to the feasible set `P`. -/
theorem x0_mem
    {P : Set E} {F : E → ℝ} {ν : NNRealˣ} {N : ℕ} {ψ : Fin N → E → ℝ} {x0 : P}
    (_method : UncertainEnvironmentBarrierSubgradientMethod P F ν N ψ x0) :
    (x0 : E) ∈ P :=
  x0.property

/-- The step objective attached to an uncertain-environment barrier method at stage `k : Fin N`.
-/
def stepObjective
    {P : Set E} {F : E → ℝ} {ν : NNRealˣ} {N : ℕ} {ψ : Fin N → E → ℝ} {x0 : P}
    (method : UncertainEnvironmentBarrierSubgradientMethod P F ν N ψ x0) (k : Fin N) :
    E → ℝ :=
  uncertainEnvironmentBarrierStepObjective F ψ ν x0 method.iterate k

-- Proof sketch: unfold `stepObjective`; it is the stage-objective definition specialized to the
-- finite iterate trace of `method`.
/-- Expanding `method.stepObjective k` gives the Algorithm 7.16 objective evaluated on the
finite iterate trace of `method`. -/
theorem stepObjective_def
    {P : Set E} {F : E → ℝ} {ν : NNRealˣ} {N : ℕ} {ψ : Fin N → E → ℝ} {x0 : P}
    (method : UncertainEnvironmentBarrierSubgradientMethod P F ν N ψ x0) (k : Fin N) :
    method.stepObjective k = uncertainEnvironmentBarrierStepObjective F ψ ν x0 method.iterate k :=
  rfl

/-- Every iterate of an uncertain-environment barrier method belongs to the feasible set `P`. -/
theorem iterate_mem
    {P : Set E} {F : E → ℝ} {ν : NNRealˣ} {N : ℕ} {ψ : Fin N → E → ℝ} {x0 : P}
    (method : UncertainEnvironmentBarrierSubgradientMethod P F ν N ψ x0)
    (k : Fin (N + 1)) :
    method k ∈ P :=
  (method.iterate k).property

/-- Every successor iterate `x_{k+1}` belongs to the feasible set `P`. -/
theorem iterates_succ_mem
    {P : Set E} {F : E → ℝ} {ν : NNRealˣ} {N : ℕ} {ψ : Fin N → E → ℝ} {x0 : P}
    (method : UncertainEnvironmentBarrierSubgradientMethod P F ν N ψ x0)
    (k : Fin N) :
    method k.succ ∈ P :=
  (method.iterate k.succ).property

/-- For each stage `k : Fin N`, the successor iterate `x_{k+1}` maximizes the Algorithm 7.16
step objective over `P`. -/
theorem step_isMaxOn
    {P : Set E} {F : E → ℝ} {ν : NNRealˣ} {N : ℕ} {ψ : Fin N → E → ℝ} {x0 : P}
    (method : UncertainEnvironmentBarrierSubgradientMethod P F ν N ψ x0)
    (k : Fin N) :
    IsMaxOn (method.stepObjective k) P (method k.succ) := by
  simpa [stepObjective] using method.step_isMax k

end UncertainEnvironmentBarrierSubgradientMethod

end
