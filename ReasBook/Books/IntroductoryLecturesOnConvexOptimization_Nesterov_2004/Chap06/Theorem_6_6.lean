/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Algorithm_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_39
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin

universe u v

section

variable {X : Type u} {U : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable {Q₁ : Set X} {Q₂ : Set U}
variable (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
variable {A : X →L[ℝ] StrongDual ℝ U}
variable {hatf : X → ℝ} {hatφ : U → ℝ} {d₁ : X → ℝ} {d₂ : U → ℝ}
variable (xμ : ℝ → U → X)
variable
    (hxμ :
      ∀ μ : ℝ, ∀ u : U,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ u))
variable (uμ : ℝ → X → U)
variable
    (huμ :
      ∀ μ : ℝ, ∀ x : X, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
variable (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂)
variable {fμ₂ : ℝ → X → ℝ} {φμ₁ : ℝ → U → ℝ}
variable {fμ₂_zero : ℝ → Q₁ → ℝ} {φ_zero : Q₂ → ℝ}
variable {initialPrimalSmoothing initialDualSmoothing : ℝ}
variable (initialState : Q₁ × Q₂)

/- Theorem 6.6 lies in the chapter's alternating excessive-gap propagation domain.

Primary mathematical domain:
- parity-split propagation of the Chapter 6 excessive-gap certificate along the iterates generated
  by Algorithm 6.3.

Sampled owner-style declarations:
- `algorithm_6_3_step_size` in `Chap06/Algorithm_6_3`, the Algorithm 6.3 owner of the step-size
  sequence `τ_k = 2 / (k + 3)`;
- `algorithm_6_3_primal_smoothing` and `algorithm_6_3_dual_smoothing` in
  `Chap06/Algorithm_6_3`, the source-facing owners of the smoothing recursions
  `μ₁,k`, `μ₂,k`;
- `alternatingExcessiveGapPrimalIterate` and `alternatingExcessiveGapDualIterate` in
  `Chap06/Algorithm_6_3`, the source-facing owners of the actual Algorithm 6.3 iterates;
- `satisfiesExcessiveGapCondition` in `Chap06/Theorem_6_4` and
  `satisfiesExcessiveGapConditionWithMu1Zero` in `Chap06/Definition_6_39`, the chapter owners of
  the two certificate layers used by the even and odd updates.

Best owner abstraction:
- source-facing: the actual Algorithm 6.3 iterate and smoothing sequences;
- core/canonical: the Algorithm 6.3 recursion lemmas from `Chap06/Algorithm_6_3` and the two
  Chapter 6 excessive-gap certificate predicates;
- bridge/view: the induction theorem below, which turns the one-step even and odd propagation
  rules into a certificate for every iterate.

Primitive data:
- the initial state `( \bar x₀, \bar u₀ )`;
- the initial smoothing parameters `μ₁,0`, `μ₂,0`;
- the Chapter 6 even and odd update-owner data;
- the stagewise even-step and odd-step certificate propagation rules.

Derived API:
- the general excessive-gap certificate for every iterate pair of Algorithm 6.3.

The previous version restated this theorem for arbitrary iterate and smoothing sequences satisfying
the same parity split and kept local duplicate certificate aliases. This file now consumes the
actual Algorithm 6.3 owners together with the chapter certificate owners directly, so the chapter
has one public recursion surface instead of generic duplicates.
-/

local notation "μ₁" =>
  algorithm_6_3_primal_smoothing initialPrimalSmoothing

local notation "μ₂" =>
  algorithm_6_3_dual_smoothing initialDualSmoothing

local notation "x̄" =>
  alternatingExcessiveGapPrimalIterate
    hQ₁
    hQ₂
    xμ
    hxμ
    uμ
    huμ
    x₀
    V
    initialPrimalSmoothing
    initialDualSmoothing
    initialState

local notation "ū" =>
  alternatingExcessiveGapDualIterate
    hQ₁
    hQ₂
    xμ
    hxμ
    uμ
    huμ
    x₀
    V
    initialPrimalSmoothing
    initialDualSmoothing
    initialState

local notation "x̄ₑ" =>
  fun k ↦
    algorithm_6_3_even_primal_iterate
      hQ₁
      hQ₂
      xμ
      hxμ
      uμ
      huμ
      initialPrimalSmoothing
      initialDualSmoothing
      (x̄ k, ū k)
      k

local notation "ūₑ" =>
  fun k ↦
    algorithm_6_3_even_dual_iterate
      hQ₁
      hQ₂
      xμ
      hxμ
      uμ
      huμ
      initialPrimalSmoothing
      initialDualSmoothing
      (x̄ k, ū k)
      k

local notation "x̄ₒ" =>
  fun k ↦
    algorithm_6_3_odd_primal_iterate
      hQ₁
      hQ₂
      uμ
      huμ
      x₀
      initialDualSmoothing
      (x̄ k, ū k)
      k

local notation "ūₒ" =>
  fun k ↦
    algorithm_6_3_odd_dual_iterate
      hQ₂
      uμ
      huμ
      V
      initialDualSmoothing
      (x̄ k, ū k)
      k

/-- Helper for Theorem 6.6: an even Algorithm 6.3 step preserves the Chapter 6 excessive-gap
certificate after rewriting the successor iterate into the canonical even-step owners. -/
-- Proof sketch: rewrite the successor iterate pair `(x̄ (k + 1), ū (k + 1))` using the even-step
-- recursion lemmas from Algorithm 6.3 and then apply the given even-step propagation hypothesis.
lemma algorithm_6_3_even_step_certificate
    (heven_step :
      ∀ k : ℕ, Even k →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ (k + 1)))
          (φμ₁ (μ₁ (k + 1)))
          (x̄ₑ k)
          (ūₑ k))
    (k : ℕ)
    (hk_even : Even k)
    (hk_cert :
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ k))
        (φμ₁ (μ₁ k))
        (x̄ k)
        (ū k)) :
    satisfiesExcessiveGapCondition
      Q₁
      Q₂
      (fμ₂ (μ₂ (k + 1)))
      (φμ₁ (μ₁ (k + 1)))
      (x̄ (k + 1))
      (ū (k + 1)) := by
  -- Identify the successor iterate with the canonical even-step update.
  have hx :
      x̄ (k + 1) = x̄ₑ k := by
    change
      x̄ (k + 1) =
        algorithm_6_3_even_primal_iterate
          hQ₁
          hQ₂
          xμ
          hxμ
          uμ
          huμ
          initialPrimalSmoothing
          initialDualSmoothing
          (x̄ k, ū k)
          k
    simpa using
      (alternatingExcessiveGapPrimalIterate_succ_of_even
        hQ₁
        hQ₂
        xμ
        hxμ
        uμ
        huμ
        x₀
        V
        initialPrimalSmoothing
        initialDualSmoothing
        initialState
        hk_even)
  have hu :
      ū (k + 1) = ūₑ k := by
    change
      ū (k + 1) =
        algorithm_6_3_even_dual_iterate
          hQ₁
          hQ₂
          xμ
          hxμ
          uμ
          huμ
          initialPrimalSmoothing
          initialDualSmoothing
          (x̄ k, ū k)
          k
    simpa using
      (alternatingExcessiveGapDualIterate_succ_of_even
        hQ₁
        hQ₂
        xμ
        hxμ
        uμ
        huμ
        x₀
        V
        initialPrimalSmoothing
        initialDualSmoothing
        initialState
        hk_even)
  -- Transport the even-step certificate along those recursion identities.
  have hx_val : ((x̄ (k + 1) : Q₁) : X) = (x̄ₑ k : X) :=
    congrArg (fun x : Q₁ ↦ (x : X)) hx
  have hu_val : ((ū (k + 1) : Q₂) : U) = (ūₑ k : U) :=
    congrArg (fun u : Q₂ ↦ (u : U)) hu
  change
    fμ₂ (μ₂ (k + 1)) (((x̄ (k + 1)) : Q₁) : X) ≤
      φμ₁ (μ₁ (k + 1)) (((ū (k + 1)) : Q₂) : U)
  rw [hx_val, hu_val]
  exact heven_step k hk_even hk_cert

/-- Helper for Theorem 6.6: an odd Algorithm 6.3 step preserves the Chapter 6 excessive-gap
certificate by passing through the `μ₁ = 0` certificate layer and then rewriting the successor
iterate into the canonical odd-step owners. -/
-- Proof sketch: convert the general certificate at step `k` into the `μ₁ = 0` version, propagate
-- it across the odd update, convert back to the general certificate at the odd-step owner, and
-- finally rewrite `(x̄ (k + 1), ū (k + 1))`.
lemma algorithm_6_3_odd_step_certificate
    (hodd_source :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ k))
          φ_zero
          (x̄ k)
          (ū k))
    (hodd_step :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ k))
          φ_zero
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ (k + 1)))
          φ_zero
          (x̄ₒ k)
          (ūₒ k))
    (hodd_target :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ (k + 1)))
          φ_zero
          (x̄ₒ k)
          (ūₒ k) →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ (k + 1)))
          (φμ₁ (μ₁ (k + 1)))
          (x̄ₒ k)
          (ūₒ k))
    (k : ℕ)
    (hk_odd : Odd k)
    (hk_cert :
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ k))
        (φμ₁ (μ₁ k))
        (x̄ k)
        (ū k)) :
    satisfiesExcessiveGapCondition
      Q₁
      Q₂
      (fμ₂ (μ₂ (k + 1)))
      (φμ₁ (μ₁ (k + 1)))
      (x̄ (k + 1))
      (ū (k + 1)) := by
  -- First move to the odd-step bridge certificate with `μ₁ = 0`.
  have hsource :
      satisfiesExcessiveGapConditionWithMu1Zero
        (fμ₂_zero (μ₂ k))
        φ_zero
        (x̄ k)
        (ū k) :=
    hodd_source k hk_odd hk_cert
  have hstep :
      satisfiesExcessiveGapConditionWithMu1Zero
        (fμ₂_zero (μ₂ (k + 1)))
        φ_zero
        (x̄ₒ k)
        (ūₒ k) :=
    hodd_step k hk_odd hsource
  have htarget :
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ (k + 1)))
        (φμ₁ (μ₁ (k + 1)))
        (x̄ₒ k)
        (ūₒ k) :=
    hodd_target k hk_odd hstep
  -- Then identify the actual successor iterate with the odd-step owner.
  have hx :
      x̄ (k + 1) = x̄ₒ k := by
    change
      x̄ (k + 1) =
        algorithm_6_3_odd_primal_iterate
          hQ₁
          hQ₂
          uμ
          huμ
          x₀
          initialDualSmoothing
          (x̄ k, ū k)
          k
    simpa using
      (alternatingExcessiveGapPrimalIterate_succ_of_odd
        hQ₁
        hQ₂
        xμ
        hxμ
        uμ
        huμ
        x₀
        V
        initialPrimalSmoothing
        initialDualSmoothing
        initialState
        hk_odd)
  have hu :
      ū (k + 1) = ūₒ k := by
    change
      ū (k + 1) =
        algorithm_6_3_odd_dual_iterate
          hQ₂
          uμ
          huμ
          V
          initialDualSmoothing
          (x̄ k, ū k)
          k
    simpa using
      (alternatingExcessiveGapDualIterate_succ_of_odd
        hQ₁
        hQ₂
        xμ
        hxμ
        uμ
        huμ
        x₀
        V
        initialPrimalSmoothing
        initialDualSmoothing
        initialState
        hk_odd)
  -- Transport the odd-step target certificate back to the actual successor iterate.
  have hx_val : ((x̄ (k + 1) : Q₁) : X) = (x̄ₒ k : X) :=
    congrArg (fun x : Q₁ ↦ (x : X)) hx
  have hu_val : ((ū (k + 1) : Q₂) : U) = (ūₒ k : U) :=
    congrArg (fun u : Q₂ ↦ (u : U)) hu
  change
    fμ₂ (μ₂ (k + 1)) (((x̄ (k + 1)) : Q₁) : X) ≤
      φμ₁ (μ₁ (k + 1)) (((ū (k + 1)) : Q₂) : U)
  rw [hx_val, hu_val]
  exact htarget

/-- Helper for Theorem 6.6: one Algorithm 6.3 step propagates the Chapter 6 excessive-gap
certificate by splitting on the parity of the current index. -/
-- Proof sketch: use `Nat.even_or_odd k` to reduce the step to the dedicated even or odd
-- propagation lemma proved above.
lemma algorithm_6_3_excessive_gap_step
    (heven_step :
      ∀ k : ℕ, Even k →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ (k + 1)))
          (φμ₁ (μ₁ (k + 1)))
          (x̄ₑ k)
          (ūₑ k))
    (hodd_source :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ k))
          φ_zero
          (x̄ k)
          (ū k))
    (hodd_step :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ k))
          φ_zero
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ (k + 1)))
          φ_zero
          (x̄ₒ k)
          (ūₒ k))
    (hodd_target :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ (k + 1)))
          φ_zero
          (x̄ₒ k)
          (ūₒ k) →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ (k + 1)))
          (φμ₁ (μ₁ (k + 1)))
          (x̄ₒ k)
          (ūₒ k))
    (k : ℕ)
    (hk_cert :
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ k))
        (φμ₁ (μ₁ k))
        (x̄ k)
        (ū k)) :
    satisfiesExcessiveGapCondition
      Q₁
      Q₂
      (fμ₂ (μ₂ (k + 1)))
      (φμ₁ (μ₁ (k + 1)))
      (x̄ (k + 1))
      (ū (k + 1)) := by
  -- The parity split isolates the two source-faithful recursion branches.
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · exact
      algorithm_6_3_even_step_certificate
        hQ₁
        hQ₂
        xμ
        hxμ
        uμ
        huμ
        x₀
        V
        initialState
        heven_step
        k
        hk_even
        hk_cert
  · exact
      algorithm_6_3_odd_step_certificate
        hQ₁
        hQ₂
        xμ
        hxμ
        uμ
        huμ
        x₀
        V
        initialState
        hodd_source
        hodd_step
        hodd_target
        k
        hk_odd
        hk_cert

-- Proof sketch: argue by induction on `k`. The base case is `hzero`. For the inductive step,
-- propagate the certificate from iterate `k` to iterate `k + 1` using the parity-split helper
-- above, which already encodes the even and odd source recursions.
/-- Theorem 6.6: if the initial Algorithm 6.3 iterate pair satisfies the Chapter 6 excessive-gap
condition, if each even step preserves the general excessive-gap certificate, and if each odd step
passes through the `μ₁ = 0` excessive-gap certificate before returning to the general one, then
every Algorithm 6.3 iterate pair satisfies the general excessive-gap condition. -/
theorem algorithm_6_3_iterates_satisfy_excessive_gap_condition
    (hzero :
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ 0))
        (φμ₁ (μ₁ 0))
        (x̄ 0)
        (ū 0))
    (heven_step :
      ∀ k : ℕ, Even k →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ (k + 1)))
          (φμ₁ (μ₁ (k + 1)))
          (x̄ₑ k)
          (ūₑ k))
    (hodd_source :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ k))
          φ_zero
          (x̄ k)
          (ū k))
    (hodd_step :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ k))
          φ_zero
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ (k + 1)))
          φ_zero
          (x̄ₒ k)
          (ūₒ k))
    (hodd_target :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ (k + 1)))
          φ_zero
          (x̄ₒ k)
          (ūₒ k) →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ (k + 1)))
          (φμ₁ (μ₁ (k + 1)))
          (x̄ₒ k)
          (ūₒ k))
    (k : ℕ) :
    satisfiesExcessiveGapCondition
      Q₁
      Q₂
      (fμ₂ (μ₂ k))
      (φμ₁ (μ₁ k))
      (x̄ k)
      (ū k) := by
  induction k with
  | zero =>
      -- The base iterate is exactly the assumed initial certificate.
      simpa using hzero
  | succ k hk =>
      -- Propagate the certificate through one Algorithm 6.3 step.
      exact
        algorithm_6_3_excessive_gap_step
          hQ₁
          hQ₂
          xμ
          hxμ
          uμ
          huμ
          x₀
          V
          initialState
          heven_step
          hodd_source
          hodd_step
          hodd_target
          k
          hk

end
