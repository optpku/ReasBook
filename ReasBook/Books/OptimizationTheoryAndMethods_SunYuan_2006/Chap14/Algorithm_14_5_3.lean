/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_5_1

noncomputable section

open scoped BigOperators
open Chapter14

section

variable {n : ℕ}

-- Layer triage:
-- * core/canonical inherited from `Algorithm_14_3_1`: `subdifferential`
-- * source-facing: `BundleMethod`
-- * bridge/view: `Chapter14.IsSubgradientAt`, Step-2/Step-3 predicates, and namespace accessors

-- Semantic recall: `lean_leansearch` did not surface a canonical mathlib owner for bundle-method
-- runs in nonsmooth optimization. This file therefore keeps the Step-1 through Step-5 data and
-- update rules explicit in a local source-faithful `BundleMethod` owner.

/-- `bundleLinearCombination g λ` is the Step-2 weighted sum `∑ i, λ i • g_(i + 1)` indexed by
the bundle elements `1, …, k`. -/
def bundleLinearCombination (g : ℕ → Point n) {k : ℕ} (lam : Fin k → ℝ) : Point n :=
  ∑ i : Fin k, lam i • g (i.1 + 1)

/-- Unfolding `bundleLinearCombination g λ` gives the Step-2 sum
`∑ i, λ i • g_(i + 1)`. -/
theorem bundleLinearCombination_eq_sum
    (g : ℕ → Point n) {k : ℕ} (lam : Fin k → ℝ) :
    bundleLinearCombination g lam = ∑ i : Fin k, lam i • g (i.1 + 1) :=
  rfl

/-- `BundleWeightFeasible t ε k λ` records the Step-2 side conditions `(14.5.7)`-`(14.5.9)`:
the weights sum to `1`, are nonnegative, and satisfy the recorded bundle-error bound
`∑ i, λ i * t_i^(k) ≤ ε`. -/
def BundleWeightFeasible
    (t : (k : ℕ) → Fin k → ℝ) (epsilon : ℝ) (k : ℕ) (lam : Fin k → ℝ) : Prop :=
  (∑ i : Fin k, lam i) = 1 ∧
    (∀ i : Fin k, 0 ≤ lam i) ∧
      (∑ i : Fin k, lam i * t k i) ≤ epsilon

/-- Unfolding `BundleWeightFeasible t ε k λ` gives the Step-2 constraints
`(14.5.7)`-`(14.5.9)`. -/
theorem bundleWeightFeasible_iff
    (t : (k : ℕ) → Fin k → ℝ) (epsilon : ℝ) (k : ℕ) (lam : Fin k → ℝ) :
    BundleWeightFeasible t epsilon k lam ↔
      (∑ i : Fin k, lam i) = 1 ∧
        (∀ i : Fin k, 0 ≤ lam i) ∧
          (∑ i : Fin k, lam i * t k i) ≤ epsilon := by
  -- This companion theorem is the definitional normal form of `BundleWeightFeasible`.
  rfl

/-- `bundleDirectionFromWeights g λ` is the Step-2 search direction `d_k` obtained from the
weighted subgradient combination `(14.5.10)`. -/
def bundleDirectionFromWeights (g : ℕ → Point n) {k : ℕ} (lam : Fin k → ℝ) : Point n :=
  -bundleLinearCombination g lam

/-- Unfolding `bundleDirectionFromWeights g λ` gives the Step-2 direction
`-∑ i, λ i • g_(i + 1)`. -/
theorem bundleDirectionFromWeights_eq
    (g : ℕ → Point n) {k : ℕ} (lam : Fin k → ℝ) :
    bundleDirectionFromWeights g lam = -bundleLinearCombination g lam :=
  rfl

/-- `SolvesBundleStepTwoSystem g t ε k λ d` records that `λ` solves the Step-2 system
`(14.5.7)`-`(14.5.9)` against the recorded bundle errors `t_i^(k)` and that `(14.5.10)`
defines the corresponding direction `d`. -/
def SolvesBundleStepTwoSystem
    (g : ℕ → Point n)
    (t : (k : ℕ) → Fin k → ℝ)
    (epsilon : ℝ)
    (k : ℕ)
    (lam : Fin k → ℝ)
    (d : Point n) : Prop :=
  BundleWeightFeasible t epsilon k lam ∧
    (∀ μ : Fin k → ℝ,
      BundleWeightFeasible t epsilon k μ →
        ‖bundleLinearCombination g lam‖ ≤ ‖bundleLinearCombination g μ‖) ∧
    d = bundleDirectionFromWeights g lam

/-- Unfolding `SolvesBundleStepTwoSystem g t ε k λ d` gives the Step-2 feasibility,
optimality, and direction equations `(14.5.7)`-`(14.5.10)`. -/
theorem solvesBundleStepTwoSystem_iff
    (g : ℕ → Point n)
    (t : (k : ℕ) → Fin k → ℝ)
    (epsilon : ℝ)
    (k : ℕ)
    (lam : Fin k → ℝ)
    (d : Point n) :
    SolvesBundleStepTwoSystem g t epsilon k lam d ↔
      BundleWeightFeasible t epsilon k lam ∧
        (∀ μ : Fin k → ℝ,
          BundleWeightFeasible t epsilon k μ →
            ‖bundleLinearCombination g lam‖ ≤ ‖bundleLinearCombination g μ‖) ∧
        d = bundleDirectionFromWeights g lam :=
  Iff.rfl

/-- `SatisfiesBundleNullStepCondition f x y g d α ε` is the Step-3 alternative `(14.5.11)`,
namely `f y - α * ⟪g, d⟫ ≥ f x - ε`. -/
def SatisfiesBundleNullStepCondition
    (f : Point n → ℝ) (x y g d : Point n) (α epsilon : ℝ) : Prop :=
  f y - α * inner ℝ g d ≥ f x - epsilon

/-- Unfolding `SatisfiesBundleNullStepCondition f x y g d α ε` gives the Step-3 null-step
inequality `(14.5.11)`. -/
theorem satisfiesBundleNullStepCondition_iff
    (f : Point n → ℝ) (x y g d : Point n) (α epsilon : ℝ) :
    SatisfiesBundleNullStepCondition f x y g d α epsilon ↔
      f y - α * inner ℝ g d ≥ f x - epsilon :=
  Iff.rfl

/-- `IsAcceptingBundleSubgradient f y g d m₁` means that `g` is the recorded trial
subgradient at `y` and satisfies the bundle acceptance inequality
`⟪g, d⟫ ≥ -(m₁ * ‖d‖ ^ 2)`. -/
def IsAcceptingBundleSubgradient
    (f : Point n → ℝ) (y g d : Point n) (m1 : ℝ) : Prop :=
  IsSubgradientAt f y g ∧ SatisfiesConjugateSubgradientAcceptanceTest g d m1

/-- Unfolding `IsAcceptingBundleSubgradient f y g d m₁` gives the subgradient membership and
acceptance inequality recorded for the continuing-stage trial subgradient. -/
theorem isAcceptingBundleSubgradient_iff
    (f : Point n → ℝ) (y g d : Point n) (m1 : ℝ) :
    IsAcceptingBundleSubgradient f y g d m1 ↔
      IsSubgradientAt f y g ∧ SatisfiesConjugateSubgradientAcceptanceTest g d m1 :=
  Iff.rfl

/-- `IsBundleTrialStep f x y g d α m₂ ε` records the source Step-3 admissibility rule:
`y = x + α d`, and either the serious-step inequality `(14.5.4)` holds or the fallback branch
records `(14.5.11)`. -/
def IsBundleTrialStep
    (f : Point n → ℝ)
    (x y g d : Point n)
    (α m2 epsilon : ℝ) : Prop :=
  y = x + α • d ∧
    (SatisfiesSufficientDescentStep f x y d α m2 ∨
      SatisfiesBundleNullStepCondition f x y g d α epsilon)

/-- Unfolding `IsBundleTrialStep f x y g d α m₂ ε` gives the Step-3 point update and the
serious-step versus null-step alternatives from the source. -/
theorem isBundleTrialStep_iff
    (f : Point n → ℝ)
    (x y g d : Point n)
    (α m2 epsilon : ℝ) :
    IsBundleTrialStep f x y g d α m2 epsilon ↔
      y = x + α • d ∧
        (SatisfiesSufficientDescentStep f x y d α m2 ∨
          SatisfiesBundleNullStepCondition f x y g d α epsilon) :=
  Iff.rfl

/-- Chapter14 Algorithm 14.5.3: a bundle method for `objective : ℝ^n → ℝ` records the iterate
sequence `x_k`, Step-2 bundle coefficients `λ_i^(k)`, search directions `d_k`, Step-3 trial
points `y_k`, trial subgradients `g_(k + 1) ∈ ∂ objective(y_k)`, and linearization errors
`t_j^(k)`, together with the source initialization `g₁ ∈ ∂ objective(x₁)` and
`t_1^(1) = 1`, the parameter bounds `0 < m₂ < m₁ < 1 / 2`, `ε > 0`, `η > 0`,
the Step-2 system `(14.5.7)`-`(14.5.10)` for the bundle weights and directions, the Step-3
admissibility rule `y_k = x_k + α_k d_k` with either `(14.5.4)` or `(14.5.11)`, the accepted
trial subgradient condition `g_(k + 1) ∈ ∂ objective(y_k)` together with
`⟪g_(k + 1), d_k⟫ ≥ -(m₁ * ‖d_k‖ ^ 2)`, the Step-4 serious-step updates, the Step-5
null-step updates, and constancy of the iterate sequence after the stopping test `‖d_k‖ ≤ η`. -/
structure BundleMethod (n : ℕ) where
  objective : Point n → ℝ
  initialPoint : Point n
  iterate : ℕ → Point n
  subgradient : ℕ → Point n
  trialPoint : ℕ → Point n
  trialStepSize : ℕ → ℝ
  bundleWeight : (k : ℕ) → Fin k → ℝ
  direction : ℕ → Point n
  linearizationError : (k : ℕ) → Fin k → ℝ
  m1 : ℝ
  m2 : ℝ
  epsilon : ℝ
  eta : ℝ
  m2_pos : 0 < m2
  m2_lt_m1 : m2 < m1
  m1_lt_half : m1 < (1 / 2 : ℝ)
  epsilon_pos : 0 < epsilon
  eta_pos : 0 < eta
  iterate_one : iterate 1 = initialPoint
  subgradient_one_mem : IsSubgradientAt objective initialPoint (subgradient 1)
  linearizationError_one : linearizationError 1 (0 : Fin 1) = 1
  stepTwoSpec (k : ℕ) (hk : 1 ≤ k) :
    SolvesBundleStepTwoSystem
      subgradient
      linearizationError
      epsilon
      k
      (bundleWeight k)
      (direction k)
  trialStepSpec (k : ℕ) (hk : 1 ≤ k) (hcont : eta < ‖direction k‖) :
    IsBundleTrialStep
      objective
      (iterate k)
      (trialPoint k)
      (subgradient (k + 1))
      (direction k)
      (trialStepSize k)
      m2
      epsilon
  trialSubgradientSpec (k : ℕ) (hk : 1 ≤ k) (hcont : eta < ‖direction k‖) :
    IsAcceptingBundleSubgradient
      objective
      (trialPoint k)
      (subgradient (k + 1))
      (direction k)
      m1
  iterate_succ_of_serious
      (k : ℕ)
      (hk : 1 ≤ k)
      (hcont : eta < ‖direction k‖)
      (hserious :
        SatisfiesSufficientDescentStep
          objective
          (iterate k)
          (trialPoint k)
          (direction k)
          (trialStepSize k)
          m2) :
    iterate (k + 1) = trialPoint k
  linearizationError_succ_of_serious_old
      (k : ℕ)
      (hk : 1 ≤ k)
      (hcont : eta < ‖direction k‖)
      (hserious :
        SatisfiesSufficientDescentStep
          objective
          (iterate k)
          (trialPoint k)
          (direction k)
          (trialStepSize k)
          m2)
      (i : Fin k) :
    linearizationError (k + 1) (Fin.castSucc i) =
      linearizationError k i +
        objective (iterate (k + 1)) -
          objective (iterate k) -
            trialStepSize k * inner ℝ (subgradient (i.1 + 1)) (direction k)
  linearizationError_succ_of_serious_new
      (k : ℕ)
      (hk : 1 ≤ k)
      (hcont : eta < ‖direction k‖)
      (hserious :
        SatisfiesSufficientDescentStep
          objective
          (iterate k)
          (trialPoint k)
          (direction k)
          (trialStepSize k)
          m2) :
    linearizationError (k + 1) (Fin.last k) = 1
  iterate_succ_of_null
      (k : ℕ)
      (hk : 1 ≤ k)
      (hcont : eta < ‖direction k‖)
      (hnull :
        ¬ SatisfiesSufficientDescentStep
            objective
            (iterate k)
            (trialPoint k)
            (direction k)
            (trialStepSize k)
            m2) :
    iterate (k + 1) = iterate k
  linearizationError_succ_of_null_old
      (k : ℕ)
      (hk : 1 ≤ k)
      (hcont : eta < ‖direction k‖)
      (hnull :
        ¬ SatisfiesSufficientDescentStep
            objective
            (iterate k)
            (trialPoint k)
            (direction k)
            (trialStepSize k)
            m2)
      (i : Fin k) :
    linearizationError (k + 1) (Fin.castSucc i) = linearizationError k i
  linearizationError_succ_of_null_new
      (k : ℕ)
      (hk : 1 ≤ k)
      (hcont : eta < ‖direction k‖)
      (hnull :
        ¬ SatisfiesSufficientDescentStep
            objective
            (iterate k)
            (trialPoint k)
            (direction k)
            (trialStepSize k)
            m2) :
    linearizationError (k + 1) (Fin.last k) =
      objective (iterate k) -
        objective (trialPoint k) +
          trialStepSize k * inner ℝ (subgradient (k + 1)) (direction k)
  iterate_tail_eq_of_stop (k : ℕ) (hk : 1 ≤ k) (hstop : ‖direction k‖ ≤ eta)
      (l : ℕ) (hkl : k ≤ l) :
    iterate (l + 1) = iterate k

namespace BundleMethod

/-- A bundle method coerces to its iterate sequence `k ↦ x_k`. -/
instance instCoe : Coe (_root_.BundleMethod n) (ℕ → Point n) where
  coe method := method.iterate

/-- A bundle method can be evaluated at stage `k` as its iterate `x_k`. -/
instance instCoeFun : CoeFun (_root_.BundleMethod n) (fun _ ↦ ℕ → Point n) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply (method : _root_.BundleMethod n) (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- At the initial point `x₁`, the recorded vector `g₁` is a subgradient of
`method.objective`. -/
theorem subgradient_one_mem_at_initialPoint (method : _root_.BundleMethod n) :
    IsSubgradientAt method.objective method.initialPoint (method.subgradient 1) :=
  method.subgradient_one_mem

/-- `method.shiftedIterate k` is the iterate sequence reindexed from stage `1`, i.e.
`x_(k + 1)`. -/
def shiftedIterate (method : _root_.BundleMethod n) : ℕ → Point n :=
  fun k ↦ method.iterate (k + 1)

/-- Unfolding `method.shiftedIterate` gives the source iterate sequence `x_(k + 1)`. -/
theorem shiftedIterate_apply (method : _root_.BundleMethod n) (k : ℕ) :
    method.shiftedIterate k = method.iterate (k + 1) :=
  rfl

/-- `method.stopsAt k` is the Step-2 stopping test `‖d_k‖ ≤ η`. -/
def stopsAt (method : _root_.BundleMethod n) (k : ℕ) : Prop :=
  ‖method.direction k‖ ≤ method.eta

/-- Unfolding `method.stopsAt k` gives the stopping condition `‖d_k‖ ≤ η`. -/
theorem stopsAt_iff (method : _root_.BundleMethod n) (k : ℕ) :
    method.stopsAt k ↔ ‖method.direction k‖ ≤ method.eta :=
  Iff.rfl

/-- If `k ≥ 1`, the recorded Step-2 data solve `(14.5.7)`-`(14.5.10)`. -/
theorem stepTwoSpecAt
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k) :
    SolvesBundleStepTwoSystem
      method.subgradient
      method.linearizationError
      method.epsilon
      k
      (method.bundleWeight k)
      (method.direction k) :=
  method.stepTwoSpec k hk

/-- If `k ≥ 1`, the recorded bundle weights satisfy the Step-2 constraints
`(14.5.7)`-`(14.5.9)`. -/
theorem bundleWeightFeasibleAt
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k) :
    BundleWeightFeasible
      method.linearizationError
      method.epsilon
      k
      (method.bundleWeight k) :=
  (solvesBundleStepTwoSystem_iff
      method.subgradient
      method.linearizationError
      method.epsilon
      k
      (method.bundleWeight k)
      (method.direction k)).1 (method.stepTwoSpec k hk) |>.1

/-- If `k ≥ 1`, the recorded Step-2 bundle weights minimize the norm of the weighted
subgradient combination among all feasible weights. -/
theorem bundleLinearCombination_norm_leAt
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k)
    {μ : Fin k → ℝ}
    (hμ :
      BundleWeightFeasible
        method.linearizationError
        method.epsilon
        k
        μ) :
    ‖bundleLinearCombination method.subgradient (method.bundleWeight k)‖ ≤
      ‖bundleLinearCombination method.subgradient μ‖ :=
  (solvesBundleStepTwoSystem_iff
      method.subgradient
      method.linearizationError
      method.epsilon
      k
      (method.bundleWeight k)
      (method.direction k)).1 (method.stepTwoSpec k hk) |>.2.1 μ hμ

/-- If `k ≥ 1`, the recorded Step-2 direction is the weighted bundle combination from
`(14.5.10)`. -/
theorem direction_eq_bundleDirectionAt
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k) :
    method.direction k =
      bundleDirectionFromWeights method.subgradient (method.bundleWeight k) :=
  (solvesBundleStepTwoSystem_iff
      method.subgradient
      method.linearizationError
      method.epsilon
      k
      (method.bundleWeight k)
      (method.direction k)).1 (method.stepTwoSpec k hk) |>.2.2

/-- If `k ≥ 1` and the stopping test fails, the recorded Step-3 data satisfy the source
admissibility rule. -/
theorem trialStepSpecAt
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k)
    (hcont : method.eta < ‖method.direction k‖) :
    IsBundleTrialStep
      method.objective
      (method.iterate k)
      (method.trialPoint k)
      (method.subgradient (k + 1))
      (method.direction k)
      (method.trialStepSize k)
      method.m2
      method.epsilon :=
  method.trialStepSpec k hk hcont

/-- If `k ≥ 1` and the stopping test fails, the recorded `g_(k + 1)` is a subgradient of
`method.objective` at the trial point `y_k`. -/
theorem trialSubgradient_memAt
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k)
    (hcont : method.eta < ‖method.direction k‖) :
    IsSubgradientAt method.objective (method.trialPoint k) (method.subgradient (k + 1)) :=
  (isAcceptingBundleSubgradient_iff
      method.objective
      (method.trialPoint k)
      (method.subgradient (k + 1))
      (method.direction k)
      method.m1).1 (method.trialSubgradientSpec k hk hcont) |>.1

/-- If `k ≥ 1` and the stopping test fails, the recorded `g_(k + 1)` satisfies the acceptance
inequality `⟪g_(k + 1), d_k⟫ ≥ -(m₁ * ‖d_k‖ ^ 2)`. -/
theorem trialSubgradient_acceptsAt
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k)
    (hcont : method.eta < ‖method.direction k‖) :
    SatisfiesConjugateSubgradientAcceptanceTest
      (method.subgradient (k + 1))
      (method.direction k)
      method.m1 :=
  (isAcceptingBundleSubgradient_iff
      method.objective
      (method.trialPoint k)
      (method.subgradient (k + 1))
      (method.direction k)
      method.m1).1 (method.trialSubgradientSpec k hk hcont) |>.2

/-- If `k ≥ 1` and the stopping test fails, the recorded Step-3 trial point is
`x_k + α_k d_k`. -/
theorem trialPoint_eq_add_smul_direction
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k)
    (hcont : method.eta < ‖method.direction k‖) :
    method.trialPoint k = method.iterate k + method.trialStepSize k • method.direction k :=
  (isBundleTrialStep_iff
      method.objective
      (method.iterate k)
      (method.trialPoint k)
      (method.subgradient (k + 1))
      (method.direction k)
      (method.trialStepSize k)
      method.m2
      method.epsilon).1 (method.trialStepSpec k hk hcont) |>.1

/-- If `k ≥ 1` and the stopping test fails, the recorded Step-3 data satisfy either the
serious-step inequality `(14.5.4)` or the null-step inequality `(14.5.11)`. -/
theorem serious_or_nullStepAt
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k)
    (hcont : method.eta < ‖method.direction k‖) :
    SatisfiesSufficientDescentStep
        method.objective
        (method.iterate k)
        (method.trialPoint k)
        (method.direction k)
        (method.trialStepSize k)
        method.m2 ∨
      SatisfiesBundleNullStepCondition
        method.objective
        (method.iterate k)
        (method.trialPoint k)
        (method.subgradient (k + 1))
        (method.direction k)
        (method.trialStepSize k)
        method.epsilon :=
  (isBundleTrialStep_iff
      method.objective
      (method.iterate k)
      (method.trialPoint k)
      (method.subgradient (k + 1))
      (method.direction k)
      (method.trialStepSize k)
      method.m2
      method.epsilon).1 (method.trialStepSpec k hk hcont) |>.2

/-- If `k ≥ 1`, the stopping test fails, and the serious-step inequality does not hold, then the
recorded Step-3 data satisfy the fallback inequality `(14.5.11)`. -/
theorem nullStepSpecAt
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k)
    (hcont : method.eta < ‖method.direction k‖)
    (hnull :
      ¬ SatisfiesSufficientDescentStep
        method.objective
        (method.iterate k)
        (method.trialPoint k)
        (method.direction k)
        (method.trialStepSize k)
        method.m2) :
    SatisfiesBundleNullStepCondition
      method.objective
      (method.iterate k)
      (method.trialPoint k)
      (method.subgradient (k + 1))
      (method.direction k)
      (method.trialStepSize k)
      method.epsilon := by
  rcases method.serious_or_nullStepAt hk hcont with hserious | hnullStep
  · exact False.elim (hnull hserious)
  · exact hnullStep

/-- If `k ≥ 1`, the stopping test fails, and the serious-step test holds, then the next iterate
is the recorded trial point `y_k`. -/
theorem iterate_succ_eq_trialPoint_of_serious
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k)
    (hcont : method.eta < ‖method.direction k‖)
    (hserious :
      SatisfiesSufficientDescentStep
        method.objective
        (method.iterate k)
        (method.trialPoint k)
        (method.direction k)
        (method.trialStepSize k)
        method.m2) :
    method.iterate (k + 1) = method.trialPoint k :=
  method.iterate_succ_of_serious k hk hcont hserious

/-- If `k ≥ 1`, the stopping test fails, and the serious-step test does not hold, then the next
iterate stays at `x_k`. -/
theorem iterate_succ_eq_self_of_null
    (method : _root_.BundleMethod n) {k : ℕ} (hk : 1 ≤ k)
    (hcont : method.eta < ‖method.direction k‖)
    (hnull :
      ¬ SatisfiesSufficientDescentStep
        method.objective
        (method.iterate k)
        (method.trialPoint k)
        (method.direction k)
        (method.trialStepSize k)
        method.m2) :
    method.iterate (k + 1) = method.iterate k :=
  method.iterate_succ_of_null k hk hcont hnull

/-- Once the stopping test holds at stage `k`, the recorded iterate sequence stays constant from
that stage onward. -/
theorem iterate_eq_of_stop
    (method : _root_.BundleMethod n) {k l : ℕ} (hk : 1 ≤ k)
    (hstop : method.stopsAt k) (hkl : k ≤ l) :
    method.iterate (l + 1) = method.iterate k :=
  method.iterate_tail_eq_of_stop k hk hstop l hkl

/-- `method.isEpsilonOptimalAt k` means that the `k`-th iterate satisfies the source target
estimate `f(x_k) ≤ f⋆[method.objective] + ε`. -/
def isEpsilonOptimalAt (method : _root_.BundleMethod n) (k : ℕ) : Prop :=
  method.objective (method.iterate k) ≤ f⋆[method.objective] + method.epsilon

/-- Unfolding `method.isEpsilonOptimalAt k` gives the source inequality
`f(x_k) ≤ f⋆[method.objective] + ε`. -/
theorem isEpsilonOptimalAt_iff
    (method : _root_.BundleMethod n) (k : ℕ) :
    method.isEpsilonOptimalAt k ↔
      method.objective (method.iterate k) ≤ f⋆[method.objective] + method.epsilon :=
  Iff.rfl

end BundleMethod

#print axioms bundleLinearCombination
#print axioms bundleDirectionFromWeights
#print axioms BundleWeightFeasible
#print axioms SolvesBundleStepTwoSystem
#print axioms Chapter14.IsSubgradientAt
#print axioms SatisfiesSufficientDescentStep
#print axioms SatisfiesBundleNullStepCondition
#print axioms SatisfiesConjugateSubgradientAcceptanceTest
#print axioms IsBundleTrialStep
#print axioms BundleMethod

end
