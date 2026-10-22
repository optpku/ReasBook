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

variable
    {X : Type u} {U : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    {Q₁ : Set X} {Q₂ : Set U}
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    {A₀ : X →L[ℝ] StrongDual ℝ U}
    {hatf : X → ℝ} {hatφ : U → ℝ} {d₁ : X → ℝ} {d₂ : U → ℝ}
    (xμ : ℝ → U → X)
    (hxμ :
      ∀ μ : ℝ, ∀ u : U,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A₀ hatf d₁ μ u))
    (uμ : ℝ → X → U)
    (huμ :
      ∀ μ : ℝ, ∀ x : X, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A₀ Q₂ hatφ d₂ μ x)
    (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂)
    {fμ₂ : ℝ → X → ℝ} {φμ₁ : ℝ → U → ℝ}
    {fμ₂_zero : ℝ → Q₁ → ℝ} {φ_zero : Q₂ → ℝ}
    {initialPrimalSmoothing initialDualSmoothing : ℝ}
    (initialState : Q₁ × Q₂)

/- Theorem 6.2.2 lies in the chapter's alternating excessive-gap recursion / rate domain.

Mandatory domain-style sampling before refinement:
- `algorithm_6_3_primal_smoothing` and `algorithm_6_3_dual_smoothing` in
  `Chap06/Algorithm_6_3`, the source-facing smoothing-parameter recursions of Algorithm 6.3;
- `alternatingExcessiveGapPrimalIterate` and `alternatingExcessiveGapDualIterate` in
  `Chap06/Algorithm_6_3`, the source-facing owners of the actual alternating recursion;
- `algorithm_6_3_iterates_satisfy_excessive_gap_condition` in `Chap06/Theorem_6_6`, the chapter
  owner propagating the excessive-gap certificate along the actual Algorithm 6.3 recursion;
- `satisfiesExcessiveGapCondition` in `Chap06/Theorem_6_4`, the chapter owner of the excessive-gap
  certificate;
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, the chapter owner turning an
  excessive-gap certificate into the textbook raw-gap budget estimate.

Best owner abstraction:
- source-facing: the actual Algorithm 6.3 smoothing and iterate sequences;
- core/canonical: `algorithm_6_3_iterates_satisfy_excessive_gap_condition`,
  `satisfiesExcessiveGapCondition`, and `raw_duality_gap_le_excessive_gap_budget`;
- bridge/view: the rate theorem below, which composes the canonical propagation result with the
  raw-gap budget estimate.

Primitive data:
- the feasible sets and the Chapter 6 even/odd update-owner data used by Algorithm 6.3;
- the initial smoothing parameters `μ₁,0`, `μ₂,0`;
- the feasible initial state, the canonical propagation hypotheses from `Theorem_6_6`, and the
  stagewise smoothing bounds.

Derived API:
- the stagewise excessive-gap certificate for the actual Algorithm 6.3 iterates;
- the duality-gap rate bound obtained from that certificate and the smoothing budget estimate.

The previous version still fed Theorem 6.2.2 through external smoothing sequences. This
refinement instead reuses the source-facing smoothing owners from `Algorithm_6_3`, so the rate
theorem now speaks directly about the chapter's actual recursion.
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

/-- Helper for Theorem 6.2.2: one Algorithm 6.3 step propagates the excessive-gap certificate
from iterate `k` to iterate `k + 1` by splitting on the parity of `k`. -/
-- Proof sketch: on even indices, rewrite the `(k + 1)` iterate with the canonical even-step
-- recurrences and apply `heven_step`; on odd indices, pass through the `μ₁ = 0` certificate
-- using `hodd_source`, `hodd_step`, and `hodd_target`, then rewrite the `(k + 1)` iterate with
-- the canonical odd-step recurrences.
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
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · -- The even branch closes after rewriting the recursive iterate into the even-step owner.
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
    have hx_val : ((x̄ (k + 1) : Q₁) : X) = (x̄ₑ k : X) :=
      congrArg (fun x : Q₁ ↦ (x : X)) hx
    have hu_val : ((ū (k + 1) : Q₂) : U) = (ūₑ k : U) :=
      congrArg (fun u : Q₂ ↦ (u : U)) hu
    change
      fμ₂ (μ₂ (k + 1)) (((x̄ (k + 1)) : Q₁) : X) ≤
        φμ₁ (μ₁ (k + 1)) (((ū (k + 1)) : Q₂) : U)
    rw [hx_val, hu_val]
    exact heven_step k hk_even hk_cert
  · -- The odd branch factors through the `μ₁ = 0` certificate before returning to the general one.
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
    have hx_val : ((x̄ (k + 1) : Q₁) : X) = (x̄ₒ k : X) :=
      congrArg (fun x : Q₁ ↦ (x : X)) hx
    have hu_val : ((ū (k + 1) : Q₂) : U) = (ūₒ k : U) :=
      congrArg (fun u : Q₂ ↦ (u : U)) hu
    change
      fμ₂ (μ₂ (k + 1)) (((x̄ (k + 1)) : Q₁) : X) ≤
        φμ₁ (μ₁ (k + 1)) (((ū (k + 1)) : Q₂) : U)
    rw [hx_val, hu_val]
    exact htarget

/-- Helper for Theorem 6.2.2: every Algorithm 6.3 iterate pair satisfies the excessive-gap
certificate once the initial pair and both parity updates satisfy the chapter hypotheses. -/
-- Proof sketch: start from `hzero` at `k = 0` and propagate the certificate through each
-- successive iterate using the parity-split one-step lemma above.
lemma algorithm_6_3_excessive_gap_certificate
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
      simpa using hzero
  | succ k hk =>
      -- Move from iterate `k` to iterate `k + 1` using the parity-split propagation lemma.
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

/-- Helper for Theorem 6.2.2: the excessive-gap certificate at iterate `k` yields the textbook
raw duality-gap budget `μ₁,k D₁ + μ₂,k D₂`. -/
-- Proof sketch: chain the lower estimate for `fμ₂`, the excessive-gap certificate, and the upper
-- estimate for `φμ₁` to obtain
-- `f (x̄ k) - μ₂ k * D₂ ≤ φ (ū k) + μ₁ k * D₁`, then rearrange with linear arithmetic.
lemma raw_duality_gap_at_iterate_le_smoothing_budget
    {f : X → ℝ} {φ : U → ℝ} {D₁ D₂ : ℝ}
    (hfμ₂_lower :
      ∀ k : ℕ,
        f (x̄ k) - μ₂ k * D₂ ≤ fμ₂ (μ₂ k) (x̄ k))
    (hφμ₁_upper :
      ∀ k : ℕ,
        φμ₁ (μ₁ k) (ū k) ≤ φ (ū k) + μ₁ k * D₁)
    (k : ℕ)
    (hk_cert :
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ k))
        (φμ₁ (μ₁ k))
        (x̄ k)
        (ū k)) :
    f (x̄ k) - φ (ū k) ≤ μ₁ k * D₁ + μ₂ k * D₂ := by
  -- The certificate sits between the stagewise lower and upper smoothing estimates.
  have hbudget_chain :
      f (x̄ k) - μ₂ k * D₂ ≤ φ (ū k) + μ₁ k * D₁ :=
    (hfμ₂_lower k).trans (hk_cert.trans (hφμ₁_upper k))
  -- Rearranging the smoothing terms yields the desired raw-gap estimate.
  linarith

/-- Theorem 6.2.2: if the Algorithm 6.3 iterates start from an excessive-gap pair and each even
and odd update satisfy the canonical propagation hypotheses of `Theorem_6_6`, then every iterate
pair `(x̄_k, ū_k)` of the feasible Algorithm 6.3 recursion satisfies the Chapter 6 excessive-gap
certificate; if the smoothing budget also obeys the chapter rate estimate, then the raw duality
gap satisfies the same rate bound. -/
-- Route correction: this proof now propagates the certificate locally inside Theorem 6.2.2
-- instead of importing the later chapter propagation theorem.
-- Proof sketch: first establish the excessive-gap certificate for every iterate by induction on
-- the Algorithm 6.3 recursion; then turn that certificate into the raw-gap budget using
-- `raw_duality_gap_le_excessive_gap_budget`; finally compose with `hbudget`.
theorem algorithm_6_3_excessive_gap_and_duality_gap_rate
    {A : X →L[ℝ] U}
    {f : X → ℝ} {φ : U → ℝ} {D₁ D₂ : ℝ}
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
    (hfμ₂_lower :
      ∀ k : ℕ,
        f (x̄ k) - μ₂ k * D₂ ≤ fμ₂ (μ₂ k) (x̄ k))
    (hφμ₁_upper :
      ∀ k : ℕ,
        φμ₁ (μ₁ k) (ū k) ≤ φ (ū k) + μ₁ k * D₁)
    (hbudget :
      ∀ k : ℕ,
        μ₁ k * D₁ + μ₂ k * D₂ ≤
          (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ((k : ℝ) + 1)) :
    ∀ k : ℕ,
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ k))
        (φμ₁ (μ₁ k))
        (x̄ k)
        (ū k) ∧
      f (x̄ k) - φ (ū k) ≤
        (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ((k : ℝ) + 1) := by
  intro k
  constructor
  · -- The first component is the propagated excessive-gap certificate.
    exact
      algorithm_6_3_excessive_gap_certificate
        hQ₁
        hQ₂
        xμ
        hxμ
        uμ
        huμ
        x₀
        V
        initialState
        hzero
        heven_step
        hodd_source
        hodd_step
        hodd_target
        k
  · -- The second component composes the raw-gap budget with the smoothing rate estimate.
    have hk_cert :
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) :=
      algorithm_6_3_excessive_gap_certificate
        hQ₁
        hQ₂
        xμ
        hxμ
        uμ
        huμ
        x₀
        V
        initialState
        hzero
        heven_step
        hodd_source
        hodd_step
        hodd_target
        k
    exact
      (raw_duality_gap_at_iterate_le_smoothing_budget
        hQ₁
        hQ₂
        xμ
        hxμ
        uμ
        huμ
        x₀
        V
        initialState
        hfμ₂_lower
        hφμ₁_upper
        k
        hk_cert).trans (hbudget k)

end
