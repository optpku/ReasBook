/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.EuclideanSubgradient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section

section

variable {n : ℕ}

open Chapter14
open scoped BigOperators

local notation "Point" => Chapter14.Point n

-- Layer triage:
-- * core/canonical inherited from `Algorithm_14_3_1`: `subdifferential`
-- * source-facing: `ConjugateSubgradientMethod`
-- * bridge/view: `Chapter14.IsSubgradientAt`, Step-3/Step-4 predicates, and namespace accessors

/-- `conjugateSubgradientDirectionCombination g I β d k` is the Step-2 expression
`-g_k + ∑_{i ∈ I_k \\ {k}} β_(k,i) d_i` from `(14.5.1)`, using the active set `I_k` and the
recorded conjugacy coefficients `β_(k,i)`. -/
def conjugateSubgradientDirectionCombination
    (subgradient : ℕ → Point)
    (activeSet : ℕ → Finset ℕ)
    (conjugateCoefficient : ℕ → ℕ → ℝ)
    (direction : ℕ → Point)
    (k : ℕ) : Point :=
  -subgradient k +
    Finset.sum ((activeSet k).erase k) (fun i ↦ conjugateCoefficient k i • direction i)

/-- Unfolding `conjugateSubgradientDirectionCombination g I β d k` gives the Step-2 formula
`-g_k + ∑_{i ∈ I_k \\ {k}} β_(k,i) d_i`. -/
theorem conjugateSubgradientDirectionCombination_eq
    (subgradient : ℕ → Point)
    (activeSet : ℕ → Finset ℕ)
    (conjugateCoefficient : ℕ → ℕ → ℝ)
    (direction : ℕ → Point)
    (k : ℕ) :
    conjugateSubgradientDirectionCombination
        subgradient activeSet conjugateCoefficient direction k =
      -subgradient k +
        Finset.sum ((activeSet k).erase k) (fun i ↦ conjugateCoefficient k i • direction i) :=
  rfl

/-- `SatisfiesConjugateSubgradientStepTwo g I β d k` records the Step-2 formulas `(14.5.1)`-
`(14.5.3)` at stage `k > 1`: the current direction is the active-set conjugate combination of
the current subgradient and retained previous directions, and the current subgradient is
conjugate to each retained direction in `I_k \\ {k}`. -/
def SatisfiesConjugateSubgradientStepTwo
    (subgradient : ℕ → Point)
    (activeSet : ℕ → Finset ℕ)
    (conjugateCoefficient : ℕ → ℕ → ℝ)
    (direction : ℕ → Point)
    (k : ℕ) : Prop :=
  direction k =
      conjugateSubgradientDirectionCombination
        subgradient activeSet conjugateCoefficient direction k ∧
    ∀ i ∈ (activeSet k).erase k, inner ℝ (subgradient k) (direction i) = 0

/-- Unfolding `SatisfiesConjugateSubgradientStepTwo g I β d k` gives the Step-2 combination
formula and the conjugacy relations against the retained indices in `I_k \\ {k}`. -/
theorem satisfiesConjugateSubgradientStepTwo_iff
    (subgradient : ℕ → Point)
    (activeSet : ℕ → Finset ℕ)
    (conjugateCoefficient : ℕ → ℕ → ℝ)
    (direction : ℕ → Point)
    (k : ℕ) :
    SatisfiesConjugateSubgradientStepTwo
        subgradient activeSet conjugateCoefficient direction k ↔
      direction k =
          conjugateSubgradientDirectionCombination
            subgradient activeSet conjugateCoefficient direction k ∧
        ∀ i ∈ (activeSet k).erase k, inner ℝ (subgradient k) (direction i) = 0 :=
  Iff.rfl

/-- `SatisfiesSufficientDescentStep f x y d α m₂` is the sufficient-descent inequality
`(14.5.4)`, namely `f y ≤ f x - m₂ * α * ‖d‖ ^ 2`. -/
def SatisfiesSufficientDescentStep
    (f : Point → ℝ) (x y d : Point) (α m₂ : ℝ) : Prop :=
  f y ≤ f x - m₂ * α * ‖d‖ ^ 2

/-- Unfolding `SatisfiesSufficientDescentStep f x y d α m₂` gives the inequality `(14.5.4)`. -/
theorem satisfiesSufficientDescentStep_iff
    (f : Point → ℝ) (x y d : Point) (α m₂ : ℝ) :
    SatisfiesSufficientDescentStep f x y d α m₂ ↔
      f y ≤ f x - m₂ * α * ‖d‖ ^ 2 :=
  Iff.rfl

/-- `IsConjugateSubgradientTrialStep f x y d α m₂ m₃ ε` records Step 3 of Algorithm 14.5.1:
`y = x + α d`, and either the sufficient-descent inequality `(14.5.4)` holds or the short-step
condition `(14.5.5)` holds. -/
def IsConjugateSubgradientTrialStep
    (f : Point → ℝ) (x y d : Point) (α m₂ m₃ ε : ℝ) : Prop :=
  y = x + α • d ∧
    (SatisfiesSufficientDescentStep f x y d α m₂ ∨ ‖y - x‖ ≤ m₃ * ε)

/-- Unfolding `IsConjugateSubgradientTrialStep f x y d α m₂ m₃ ε` gives the Step-3 update and
the alternative conditions `(14.5.4)` and `(14.5.5)`. -/
theorem isConjugateSubgradientTrialStep_iff
    (f : Point → ℝ) (x y d : Point) (α m₂ m₃ ε : ℝ) :
    IsConjugateSubgradientTrialStep f x y d α m₂ m₃ ε ↔
      y = x + α • d ∧
        (SatisfiesSufficientDescentStep f x y d α m₂ ∨ ‖y - x‖ ≤ m₃ * ε) :=
  Iff.rfl

/-- `SatisfiesConjugateSubgradientAcceptanceTest g d m₁` is the Step-4 inequality `(14.5.6)`,
namely `⟪g, d⟫ ≥ -m₁ * ‖d‖ ^ 2`. -/
def SatisfiesConjugateSubgradientAcceptanceTest
    (g d : Point) (m₁ : ℝ) : Prop :=
  inner ℝ g d ≥ -(m₁ * ‖d‖ ^ 2)

/-- Unfolding `SatisfiesConjugateSubgradientAcceptanceTest g d m₁` gives the Step-4 inequality
`(14.5.6)`. -/
theorem satisfiesConjugateSubgradientAcceptanceTest_iff
    (g d : Point) (m₁ : ℝ) :
    SatisfiesConjugateSubgradientAcceptanceTest g d m₁ ↔
      inner ℝ g d ≥ -(m₁ * ‖d‖ ^ 2) :=
  Iff.rfl

/-- `HasAcceptingBundleSubgradient f y d m₁` means that Step 4 admits some
`g ∈ ∂ f(y)` satisfying the acceptance inequality `(14.5.6)`. -/
def HasAcceptingBundleSubgradient
    (f : Point → ℝ) (y d : Point) (m₁ : ℝ) : Prop :=
  ∃ g : Point,
    IsSubgradientAt f y g ∧ SatisfiesConjugateSubgradientAcceptanceTest g d m₁

/-- Unfolding `HasAcceptingBundleSubgradient f y d m₁` gives the Step-4 existence condition
from `(14.5.6)`. -/
theorem hasAcceptingBundleSubgradient_iff
    (f : Point → ℝ) (y d : Point) (m₁ : ℝ) :
    HasAcceptingBundleSubgradient f y d m₁ ↔
      ∃ g : Point,
        IsSubgradientAt f y g ∧ SatisfiesConjugateSubgradientAcceptanceTest g d m₁ :=
  Iff.rfl

/-- Chapter14 Algorithm 14.5.1: the conjugate subgradient method for `f : ℝ^n → ℝ` starts from
an initial point `x₁`, a stagewise subgradient sequence `g_k` with `g₁ ∈ ∂ f(x₁)`, parameters
`0 < m₂ < m₁ < 1 / 2`, `0 < m₃ < 1`, `ε > 0`, `η > 0`, and the initial active set `I₁ = {1}`.
Its Step-2 data are recorded directly by the restart formula `d₁ = -g₁`, the active-set
combination `(14.5.1)` with coefficients `β_(k,i)`, and the conjugacy relations
`(14.5.2)`-`(14.5.3)` against the retained directions in `I_k \\ {k}`. On continuing stages
`η < ‖d_k‖`, the recorded trial point `y_k` satisfies Step 3, Step 4 branches on the
existential predicate `HasAcceptingBundleSubgradient objective (trialPoint k) (direction k) m₁`,
the recorded `g_(k + 1) ∈ ∂ f(y_k)` is a witness on accepting stages, and Step 5 updates the
active set by keeping exactly the indices whose iterates lie within `ε` of `x_(k + 1)`. -/
structure ConjugateSubgradientMethod (n : ℕ) where
  objective : EuclideanSpace ℝ (Fin n) → ℝ
  initialPoint : EuclideanSpace ℝ (Fin n)
  subgradient : ℕ → EuclideanSpace ℝ (Fin n)
  m₁ : ℝ
  m₂ : ℝ
  m₃ : ℝ
  ε : ℝ
  η : ℝ
  iterate : ℕ → EuclideanSpace ℝ (Fin n)
  trialPoint : ℕ → EuclideanSpace ℝ (Fin n)
  direction : ℕ → EuclideanSpace ℝ (Fin n)
  stepSize : ℕ → ℝ
  activeSet : ℕ → Finset ℕ
  conjugateCoefficient : ℕ → ℕ → ℝ
  m₂_pos : 0 < m₂
  m₂_lt_m₁ : m₂ < m₁
  m₁_lt_one_half : m₁ < 1 / 2
  m₃_pos : 0 < m₃
  m₃_lt_one : m₃ < 1
  ε_pos : 0 < ε
  η_pos : 0 < η
  iterate_one : iterate 1 = initialPoint
  subgradient_one_mem : IsSubgradientAt objective initialPoint (subgradient 1)
  activeSet_one : activeSet 1 = ({1} : Finset ℕ)
  direction_one : direction 1 = -subgradient 1
  stepTwoSpec :
    ∀ k, 1 < k →
      SatisfiesConjugateSubgradientStepTwo
        subgradient
        activeSet
        conjugateCoefficient
        direction
        k
  trialStep :
    ∀ k, 1 ≤ k → η < ‖direction k‖ →
      IsConjugateSubgradientTrialStep
        objective
        (iterate k)
        (trialPoint k)
        (direction k)
        (stepSize k)
        m₂
        m₃
        ε
  trialSubgradient_mem :
    ∀ k, 1 ≤ k → η < ‖direction k‖ →
      IsSubgradientAt objective (trialPoint k) (subgradient (k + 1))
  subgradient_succ_accepts_of_hasAcceptingBundleSubgradient :
    ∀ k, 1 ≤ k → η < ‖direction k‖ →
      HasAcceptingBundleSubgradient objective (trialPoint k) (direction k) m₁ →
        SatisfiesConjugateSubgradientAcceptanceTest (subgradient (k + 1)) (direction k) m₁
  iterate_succ_of_accepting :
    ∀ k, 1 ≤ k → η < ‖direction k‖ →
      HasAcceptingBundleSubgradient objective (trialPoint k) (direction k) m₁ →
        iterate (k + 1) = trialPoint k
  iterate_succ_of_rejecting :
    ∀ k, 1 ≤ k → η < ‖direction k‖ →
      ¬ HasAcceptingBundleSubgradient objective (trialPoint k) (direction k) m₁ →
        iterate (k + 1) = iterate k
  activeSet_succ :
    ∀ k, 1 ≤ k → η < ‖direction k‖ →
      activeSet (k + 1) =
        (insert (k + 1) (activeSet k)).filter
          (fun i ↦ ‖iterate i - iterate (k + 1)‖ ≤ ε)

namespace ConjugateSubgradientMethod

/-- A conjugate subgradient method coerces to its objective function `ℝ^n → ℝ`. -/
instance instCoeFun :
    CoeFun (ConjugateSubgradientMethod n) (fun _ ↦ Point → ℝ) where
  coe method := method.objective

/-- Evaluating `method` as a function returns its objective value. -/
theorem coe_apply (method : ConjugateSubgradientMethod n) (x : Point) :
    method x = method.objective x :=
  rfl

/-- `method.shiftedIterate k` is the iterate sequence reindexed from stage `1`, i.e.
`x_(k + 1)`. -/
def shiftedIterate (method : ConjugateSubgradientMethod n) : ℕ → Point :=
  fun k ↦ method.iterate (k + 1)

/-- Unfolding `method.shiftedIterate` gives the source iterate sequence `x_(k + 1)`. -/
theorem shiftedIterate_apply (method : ConjugateSubgradientMethod n) (k : ℕ) :
    method.shiftedIterate k = method.iterate (k + 1) :=
  rfl

/-- `method.stopsAt k` is the Step-2 stopping condition `‖d_k‖ ≤ η`. -/
def stopsAt (method : ConjugateSubgradientMethod n) (k : ℕ) : Prop :=
  ‖method.direction k‖ ≤ method.η

/-- `method.dropSetAt k` is the Step-5 index set `T_k` of iterates more than `ε` away from
`x_(k + 1)`. -/
def dropSetAt
    (method : ConjugateSubgradientMethod n) (k : ℕ) : Finset ℕ :=
  (insert (k + 1) (method.activeSet k)).filter
    (fun i ↦ method.ε < ‖method.iterate i - method.iterate (k + 1)‖)

/-- Unfolding `method.stopsAt k` gives the Step-2 condition `‖d_k‖ ≤ η`. -/
theorem stopsAt_iff
    (method : ConjugateSubgradientMethod n) (k : ℕ) :
    stopsAt method k ↔ ‖method.direction k‖ ≤ method.η :=
  Iff.rfl

/-- Unfolding `method.dropSetAt k` gives the Step-5 index condition
`ε < ‖x_i - x_(k + 1)‖`. -/
theorem mem_dropSetAt_iff
    (method : ConjugateSubgradientMethod n) (k i : ℕ) :
    i ∈ dropSetAt method k ↔
      i ∈ insert (k + 1) (method.activeSet k) ∧
        method.ε < ‖method.iterate i - method.iterate (k + 1)‖ := by
  simp [dropSetAt]

/-- The initial Step-2 direction is the restart direction `d₁ = -g₁`. -/
theorem direction_one_eq_neg_subgradient
    (method : ConjugateSubgradientMethod n) :
    method.direction 1 = -method.subgradient 1 :=
  method.direction_one

/-- On every stage `k > 1`, the recorded Step-2 data satisfy `(14.5.1)`-`(14.5.3)`. -/
theorem stepTwoSpecAt
    (method : ConjugateSubgradientMethod n) {k : ℕ} (hk : 1 < k) :
    SatisfiesConjugateSubgradientStepTwo
      method.subgradient
      method.activeSet
      method.conjugateCoefficient
      method.direction
      k :=
  method.stepTwoSpec k hk

/-- On every stage `k > 1`, the recorded direction is the Step-2 active-set combination
`-g_k + ∑_{i ∈ I_k \\ {k}} β_(k,i) d_i`. -/
theorem direction_eq_conjugateSubgradientDirectionCombination
    (method : ConjugateSubgradientMethod n) {k : ℕ} (hk : 1 < k) :
    method.direction k =
      conjugateSubgradientDirectionCombination
        method.subgradient
        method.activeSet
        method.conjugateCoefficient
        method.direction
        k :=
  (satisfiesConjugateSubgradientStepTwo_iff
      method.subgradient
      method.activeSet
      method.conjugateCoefficient
      method.direction
      k).1 (method.stepTwoSpec k hk) |>.1

/-- On every stage `k > 1`, the recorded Step-2 data make `g_k` conjugate to each retained
direction `d_i` with `i ∈ I_k \\ {k}`. -/
theorem subgradient_conjugate_to_retained_direction
    (method : ConjugateSubgradientMethod n) {k i : ℕ}
    (hk : 1 < k) (hi : i ∈ (method.activeSet k).erase k) :
    inner ℝ (method.subgradient k) (method.direction i) = 0 :=
  (satisfiesConjugateSubgradientStepTwo_iff
      method.subgradient
      method.activeSet
      method.conjugateCoefficient
      method.direction
      k).1 (method.stepTwoSpec k hk) |>.2 i hi

/-- At the initial point `x₁`, the recorded vector `g₁` is a subgradient of
`method.objective`. -/
theorem subgradient_one_mem_at_initialPoint
    (method : ConjugateSubgradientMethod n) :
    IsSubgradientAt method.objective method.initialPoint (method.subgradient 1) :=
  method.subgradient_one_mem

/-- If `η < ‖d_k‖`, the recorded Step-3 trial point is `x_k + α_k d_k`. -/
theorem trialPoint_eq_add_smul_direction
    (method : ConjugateSubgradientMethod n) {k : ℕ}
    (hk : 1 ≤ k) (hcontinue : method.η < ‖method.direction k‖) :
    method.trialPoint k = method.iterate k + method.stepSize k • method.direction k :=
  ((isConjugateSubgradientTrialStep_iff
      method.objective
      (method.iterate k)
      (method.trialPoint k)
      (method.direction k)
      (method.stepSize k)
      method.m₂
      method.m₃
      method.ε).1 (method.trialStep k hk hcontinue)).1

/-- If `η < ‖d_k‖`, the recorded vector `g_(k + 1)` is a subgradient of `method.objective` at
the trial point `y_k`. -/
theorem subgradient_succ_mem_at_trialPoint
    (method : ConjugateSubgradientMethod n) {k : ℕ}
    (hk : 1 ≤ k) (hcontinue : method.η < ‖method.direction k‖) :
    IsSubgradientAt method.objective (method.trialPoint k) (method.subgradient (k + 1)) :=
  method.trialSubgradient_mem k hk hcontinue

/-- If `η < ‖d_k‖` and Step 4 is in the accepting case, the recorded vector `g_(k + 1)`
itself satisfies the acceptance inequality `(14.5.6)`. -/
theorem subgradient_succ_accepts_at_trialPoint_of_hasAcceptingBundleSubgradient
    (method : ConjugateSubgradientMethod n) {k : ℕ}
    (hk : 1 ≤ k) (hcontinue : method.η < ‖method.direction k‖)
    (haccept :
      HasAcceptingBundleSubgradient
        method.objective
        (method.trialPoint k)
        (method.direction k)
        method.m₁) :
    SatisfiesConjugateSubgradientAcceptanceTest
      (method.subgradient (k + 1))
      (method.direction k)
      method.m₁ :=
  method.subgradient_succ_accepts_of_hasAcceptingBundleSubgradient k hk hcontinue haccept

/-- If `η < ‖d_k‖`, then Step 4 either accepts `y_k` because some subgradient at `y_k`
satisfies `(14.5.6)` or keeps `x_(k + 1) = x_k` when no such subgradient exists. -/
theorem iterate_succ_eq_trialPoint_or_self
    (method : ConjugateSubgradientMethod n) {k : ℕ}
    (hk : 1 ≤ k) (hcontinue : method.η < ‖method.direction k‖) :
    (HasAcceptingBundleSubgradient
        method.objective
        (method.trialPoint k)
        (method.direction k)
        method.m₁ ∧
      method.iterate (k + 1) = method.trialPoint k) ∨
    (¬ HasAcceptingBundleSubgradient
        method.objective
        (method.trialPoint k)
        (method.direction k)
        method.m₁ ∧
      method.iterate (k + 1) = method.iterate k) := by
  by_cases haccept :
      HasAcceptingBundleSubgradient
        method.objective
        (method.trialPoint k)
        (method.direction k)
        method.m₁
  · exact Or.inl ⟨haccept, method.iterate_succ_of_accepting k hk hcontinue haccept⟩
  · exact Or.inr ⟨haccept, method.iterate_succ_of_rejecting k hk hcontinue haccept⟩

end ConjugateSubgradientMethod

end
