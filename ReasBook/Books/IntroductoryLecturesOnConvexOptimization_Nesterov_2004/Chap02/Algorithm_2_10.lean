/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_38
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Remark_2_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MaxTypeStep StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι] {μ L : ℝ}

local notation "qf" => q[μ, L]

/-
Primary domain: fixed-momentum accelerated recurrences for smooth minimax problems on proper real
inner-product spaces.

Owner declarations sampled for this refinement:
* `ConstantStepSchemeIIMomentumRecurrence` in `Algorithm_2_4` is the canonical upstream momentum
  owner for accelerated trajectories;
* `ConstantStepSchemeIIIMomentumRecurrence.toConstantStepSchemeIIMomentumRecurrence` in
  `Proposition_2_12` provides the source-facing fixed-`β` bridge to that owner;
* `SmoothMinimaxProblem` in `Definition_2_38` owns the feasible set, component family, and the
  derived affine model `problem.affineApproximation`;
* `quadraticallyRegularizedObjective` in `Definition_1_4_17.lean` owns the exact minimax step
  objective once that affine model is fixed;
* `maxTypeGradientMapping` and `maxTypeGradientMapping_mem_and_isMinOn_ofFact` in
  `Remark_2_41_1` own the canonical exact step `x_f(xBar; L)` for that regularized affine
  max-type model.

Layer triage:
* `source-facing`: the recursive trajectory `optimalMinimaxMethod`, i.e. the fixed-momentum
  minimax states `((x_k, y_k))` together with the textbook update `x_{k+1} = x_f(y_k; L)`;
* `core/canonical`: `ConstantStepSchemeIIIMomentumRecurrence`,
  `ConstantStepSchemeIIMomentumRecurrence`, and `maxTypeGradientMapping`;
* `bridge/view`: `optimalMinimaxMethodToIIIMomentumRecurrence`,
  `optimalMinimaxMethodToMomentumRecurrence`, and the derived minimizer theorem
  `optimalMinimaxMethodX_succ_isMinOn`.

Primitive data are therefore the owner fixed-momentum recurrence, the parameter side conditions
`0 < L`, and the exact step equality to the owner chosen point `maxTypeGradientMapping ...
(y_k) L`. The constant coefficient `β` and the underlying `(x_k, y_k)` recurrence belong to the
recursive source-facing object and are bridged to the owner abstraction only after the fact; the
older minimizer-predicate view is kept only as derived API.
-/

section

variable (problem : SmoothMinimaxProblem E ι μ L) (x0 : problem.feasibleSet) (hL : 0 < L)

local notation "Q" => problem.feasibleSet
local notation "γL" => (Units.mk0 (Real.toNNReal L) (by positivity) : NNRealˣ)

local instance instLocalChap02_Algorithm_2_101 : Fact (Set.Nonempty Q) := ⟨problem.feasible_nonempty⟩
local instance instLocalChap02_Algorithm_2_102 : Fact (IsClosed Q) := ⟨problem.feasible_closed⟩
local instance instLocalChap02_Algorithm_2_103 : Fact (Convex ℝ Q) := ⟨problem.feasible_convex⟩

/-- The one-step state update of Algorithm 2.10 on pairs `(x_k, y_k)`. -/
noncomputable def optimalMinimaxMethodStep :
    Q × E → Q × E :=
  fun state ↦
    let xk := state.1
    let yk := state.2
    let xNext : Q :=
      ⟨x_f[Q | problem.components; γL](yk),
        (maxTypeGradientMapping_mem_and_isMinOn_ofFact
          Q
          problem.components
          yk
          γL).1⟩
    let yNext :=
      (xNext : E) + β[qf] • ((xNext : E) - (xk : E))
    (xNext, yNext)

/-- Algorithm 2.10: the recursive minimax trajectory started from `(x₀, y₀) = (x0, x0)` and
updated by the canonical exact max-type step
`x_{k+1} = x_f(y_k; L)` together with the fixed-momentum extrapolation
`y_{k+1} = x_{k+1} + β (x_{k+1} - x_k)`, where
`β = β[qf] = β[q[μ, L]]`. -/
noncomputable def optimalMinimaxMethod
    (problem : SmoothMinimaxProblem E ι μ L) (x0 : problem.feasibleSet) (hL : 0 < L) :
    ℕ → problem.feasibleSet × E
  | 0 => (x0, (x0 : E))
  | k + 1 =>
      optimalMinimaxMethodStep
        problem
        hL
        (optimalMinimaxMethod problem x0 hL k)

/-- The feasible iterate sequence `x_k` of Algorithm 2.10. -/
noncomputable def optimalMinimaxMethodX
    (problem : SmoothMinimaxProblem E ι μ L) (x0 : problem.feasibleSet) (hL : 0 < L) :
    ℕ → problem.feasibleSet :=
  fun k ↦ (optimalMinimaxMethod problem x0 hL k).1

/-- The extrapolated sequence `y_k` of Algorithm 2.10. -/
noncomputable def optimalMinimaxMethodY
    (problem : SmoothMinimaxProblem E ι μ L) (x0 : problem.feasibleSet) (hL : 0 < L) :
    ℕ → E :=
  fun k ↦ (optimalMinimaxMethod problem x0 hL k).2

local notation "state" => optimalMinimaxMethod problem x0 hL
local notation "xSeq" => optimalMinimaxMethodX problem x0 hL
local notation "ySeq" => optimalMinimaxMethodY problem x0 hL

@[simp] theorem optimalMinimaxMethod_zero :
    state 0 = (x0, (x0 : E)) :=
  rfl

/-- The recursive minimax state satisfies the one-step update law. -/
@[simp] theorem optimalMinimaxMethod_succ (k : ℕ) :
    state (k + 1) =
      optimalMinimaxMethodStep
        problem
        hL
        (state k) :=
  rfl

/-- The recursive minimax trajectory starts from `x₀ = x0`. -/
@[simp] theorem optimalMinimaxMethodX_zero :
    xSeq 0 = x0 :=
  rfl

/-- The recursive minimax trajectory starts from `y₀ = x0`. -/
@[simp] theorem optimalMinimaxMethodY_zero :
    ySeq 0 = (x0 : E) :=
  rfl

/-- The recursive minimax iterates satisfy the textbook exact-step update
`x_{k+1} = x_f(y_k; L)`. -/
@[simp] theorem optimalMinimaxMethodX_succ (k : ℕ) :
    (xSeq (k + 1) : E) =
      x_f[Q | problem.components; γL](ySeq k) :=
  by
    change
      x_f[Q | problem.components; γL]((optimalMinimaxMethod problem x0 hL k).2) =
        x_f[Q | problem.components; γL](ySeq k)
    rfl

/-- The recursive minimax extrapolated points satisfy the fixed-momentum update. -/
@[simp] theorem optimalMinimaxMethodY_succ (k : ℕ) :
    ySeq (k + 1) =
      (xSeq (k + 1) : E) + β[qf] • ((xSeq (k + 1) : E) - (xSeq k : E)) :=
  by
    change
      (x_f[Q | problem.components; γL]((optimalMinimaxMethod problem x0 hL k).2) : E) +
          β[qf] •
            ((x_f[Q | problem.components; γL]((optimalMinimaxMethod problem x0 hL k).2) : E) -
              ((optimalMinimaxMethod problem x0 hL k).1 : E)) =
        (xSeq (k + 1) : E) + β[qf] • ((xSeq (k + 1) : E) - (xSeq k : E))
    rw [optimalMinimaxMethodX_succ problem x0 hL k]
    rfl

/-- The recursive Algorithm 2.10 trajectory, viewed through the owner fixed-momentum recurrence
API. -/
def optimalMinimaxMethodToIIIMomentumRecurrence :
    ConstantStepSchemeIIIMomentumRecurrence E Q qf x0 where
  x := xSeq
  y := ySeq
  x_zero := optimalMinimaxMethodX_zero problem x0 hL
  y_zero := optimalMinimaxMethodY_zero problem x0 hL
  y_succ := optimalMinimaxMethodY_succ problem x0 hL

/-- Under the admissible reciprocal-condition-number hypothesis `q_f ∈ (0, 1]`, the recursive
Algorithm 2.10 trajectory yields the canonical type-II momentum owner by adjoining the constant
scalar sequence `α_k = √q_f`. -/
def optimalMinimaxMethodToMomentumRecurrence
    (hqf : qf ∈ Set.Ioc (0 : ℝ) 1) :
    ConstantStepSchemeIIMomentumRecurrence
      E Q qf x0 (Real.sqrt qf) :=
  ConstantStepSchemeIIIMomentumRecurrence.toConstantStepSchemeIIMomentumRecurrence
    (optimalMinimaxMethodToIIIMomentumRecurrence problem x0 hL)
    hqf

/-- The canonical exact step of Algorithm 2.10 is a feasible minimizer of the corresponding
quadratically regularized affine max-type model. -/
theorem optimalMinimaxMethodX_succ_isMinOn (k : ℕ) :
    IsMinOn
      (quadraticallyRegularizedObjective (problem.affineApproximation (ySeq k)) L (ySeq k))
      Q
      (xSeq (k + 1) : E) := by
  rw [optimalMinimaxMethodX_succ problem x0 hL k]
  simpa [SmoothMinimaxProblem.affineApproximation, Real.toNNReal_of_nonneg hL.le] using
    (maxTypeGradientMapping_mem_and_isMinOn_ofFact
      Q
      problem.components
      (ySeq k)
      γL).2

end

end
