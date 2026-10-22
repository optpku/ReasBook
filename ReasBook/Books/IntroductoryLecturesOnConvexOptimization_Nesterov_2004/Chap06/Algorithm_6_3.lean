/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Algebra.Ring.Parity
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open StronglyConvexDualUpdate
open scoped ConstrainedArgmin

/- This item lies in the chapter's alternating excessive-gap recursion domain.

Primary mathematical domain:
- the parity-dependent recursive primal-dual method driven by the Algorithm 6.3 step size
  `τ_k = 2 / (k + 3)`, with the direct even-step update layer from `Theorem_6_4` and the direct
  odd-step update layer from `Theorem_6_2_3` / `Theorem_6_7`.

Sampled owner-style declarations:
- `reduced_primal_smoothing` in `Theorem_6_4`, the chapter owner of the even-step update
  `μ₁⁺ = (1 - τ) μ₁`;
- `StronglyConvexDualUpdate.reducedDualSmoothing` in `Theorem_6_2_3`, the chapter owner of the
  odd-step update `μ₂⁺ = (1 - τ) μ₂`;
- `predicted_primal_point` and `updated_dual_point` in `Theorem_6_4`, the direct even-branch
  update owners consumed by the algorithm;
- `StronglyConvexDualUpdate.predictedDualPoint` and
  `StronglyConvexDualUpdate.updatedPrimalPoint`, the direct odd-branch update owners consumed by
  the algorithm.

Best owner abstraction:
- source-facing: the Algorithm 6.3 smoothing recursions `μ₁,k`, `μ₂,k` together with the
  alternating recursive state sequence;
- core/canonical: the chapter smoothing-update owners
  `reduced_primal_smoothing` and `StronglyConvexDualUpdate.reducedDualSmoothing`;
- bridge/view: the primal and dual projections and their parity-split recurrence lemmas.

Primitive data:
- an initial pair `( \bar x₀, \bar u₀ )`;
- the initial smoothing parameters `μ₁,0` and `μ₂,0`;
- the Chapter 6 oracle data used by the even and odd update owners.

Derived API:
- the recursive smoothing-parameter owners `μ₁,k` and `μ₂,k`;
- the recursive state sequence of Algorithm 6.3;
- the projected primal and dual iterate sequences `\bar x_k` and `\bar u_k`;
- the even- and odd-step recurrence lemmas expressed with the chapter smoothing-update owners.

The previous version weakened Algorithm 6.3 to an arbitrary alternating process driven by four
external update maps. This file now keeps the source-facing smoothing recursions public and builds
the recursive iterates directly from the chapter's actual even and odd update owners.
-/

section

/-- The Algorithm 6.3 step-size sequence is `τ_k = 2 / (k + 3)`. -/
def algorithm_6_3_step_size (k : ℕ) : ℝ :=
  (2 : ℝ) / ((k : ℝ) + 3)

/-- The Algorithm 6.3 step size is always positive. -/
theorem algorithm_6_3_step_size_pos (k : ℕ) :
    0 < algorithm_6_3_step_size k := by
  dsimp [algorithm_6_3_step_size]
  positivity

/-- The Algorithm 6.3 step size always lies below `1`. -/
theorem algorithm_6_3_step_size_lt_one (k : ℕ) :
    algorithm_6_3_step_size k < 1 := by
  have hk : (2 : ℝ) < (k : ℝ) + 3 := by
    have hk' : (0 : ℝ) ≤ k := by
      exact_mod_cast Nat.zero_le k
    nlinarith
  have hden : (0 : ℝ) < (k : ℝ) + 3 := by
    positivity
  simpa [algorithm_6_3_step_size] using (div_lt_one hden).2 hk

/-- The Algorithm 6.3 step size is the Chapter 6 convex-combination parameter. -/
theorem algorithm_6_3_step_size_mem_Icc (k : ℕ) :
    algorithm_6_3_step_size k ∈ Set.Icc (0 : ℝ) 1 :=
  tau_mem_Icc (algorithm_6_3_step_size_pos k) (algorithm_6_3_step_size_lt_one k)

/-- The Algorithm 6.3 primal smoothing sequence `μ₁,k`. -/
def algorithm_6_3_primal_smoothing (initialPrimalSmoothing : ℝ) :
    ℕ → ℝ :=
  fun
    | 0 => initialPrimalSmoothing
    | k + 1 =>
        if Even k then
          reduced_primal_smoothing
            (algorithm_6_3_primal_smoothing initialPrimalSmoothing k)
            (algorithm_6_3_step_size k)
        else
          algorithm_6_3_primal_smoothing initialPrimalSmoothing k

/-- The Algorithm 6.3 dual smoothing sequence `μ₂,k`. -/
def algorithm_6_3_dual_smoothing (initialDualSmoothing : ℝ) :
    ℕ → ℝ :=
  fun
    | 0 => initialDualSmoothing
    | k + 1 =>
        if Even k then
          algorithm_6_3_dual_smoothing initialDualSmoothing k
        else
          reducedDualSmoothing
            (algorithm_6_3_dual_smoothing initialDualSmoothing k)
            (algorithm_6_3_step_size k)

section SmoothingRecurrence

variable (initialPrimalSmoothing initialDualSmoothing : ℝ)

local notation "μ₁" =>
  algorithm_6_3_primal_smoothing initialPrimalSmoothing

local notation "μ₂" =>
  algorithm_6_3_dual_smoothing initialDualSmoothing

@[simp] theorem algorithm_6_3_primal_smoothing_zero :
    μ₁ 0 = initialPrimalSmoothing :=
  rfl

@[simp] theorem algorithm_6_3_dual_smoothing_zero :
    μ₂ 0 = initialDualSmoothing :=
  rfl

/-- At an even stage `k`, Algorithm 6.3 updates the primal smoothing parameter by the chapter
rule `μ₁,k+1 = (1 - τ_k) μ₁,k`. -/
theorem algorithm_6_3_primal_smoothing_succ_of_even {k : ℕ} (hk : Even k) :
    μ₁ (k + 1) = reduced_primal_smoothing (μ₁ k) (algorithm_6_3_step_size k) := by
  simp [algorithm_6_3_primal_smoothing, hk]

/-- At an even stage `k`, Algorithm 6.3 leaves the dual smoothing parameter unchanged. -/
theorem algorithm_6_3_dual_smoothing_succ_of_even {k : ℕ} (hk : Even k) :
    μ₂ (k + 1) = μ₂ k := by
  simp [algorithm_6_3_dual_smoothing, hk]

/-- At an odd stage `k`, Algorithm 6.3 leaves the primal smoothing parameter unchanged. -/
theorem algorithm_6_3_primal_smoothing_succ_of_odd {k : ℕ} (hk : Odd k) :
    μ₁ (k + 1) = μ₁ k := by
  simp [algorithm_6_3_primal_smoothing, Nat.not_even_iff_odd.mpr hk]

/-- At an odd stage `k`, Algorithm 6.3 updates the dual smoothing parameter by the chapter rule
`μ₂,k+1 = (1 - τ_k) μ₂,k`. -/
theorem algorithm_6_3_dual_smoothing_succ_of_odd {k : ℕ} (hk : Odd k) :
    μ₂ (k + 1) = reducedDualSmoothing (μ₂ k) (algorithm_6_3_step_size k) := by
  simp [algorithm_6_3_dual_smoothing, Nat.not_even_iff_odd.mpr hk]

end SmoothingRecurrence

section Updates

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

variable {Q₁ : Set E₁} {Q₂ : Set E₂}
variable (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
variable {A : E₁ →L[ℝ] StrongDual ℝ E₂}
variable {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {d₁ : E₁ → ℝ} {d₂ : E₂ → ℝ}
variable (xμ : ℝ → E₂ → E₁)
variable
    (hxμ :
      ∀ μ : ℝ, ∀ u : E₂,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ u))
variable (uμ : ℝ → E₁ → E₂)
variable
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
variable (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂)

omit [CompleteSpace E₂] in
private theorem dualOracle_mem
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (μ : ℝ) (x : Q₁) :
    uμ μ x ∈ Q₂ := by
  have hu :
      uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ (x : E₁) :=
    huμ μ x x.property
  exact
    (mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ μ (x : E₁) (uμ μ x)).mp hu |>.1

private def dualOracle
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (μ : ℝ) : Q₁ → Q₂ :=
  fun x ↦ ⟨uμ μ x, dualOracle_mem uμ huμ μ x⟩

private def algorithm_6_3_even_step
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (xμ : ℝ → E₂ → E₁)
    (hxμ :
      ∀ μ : ℝ, ∀ u : E₂,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ u))
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (initialPrimalSmoothing initialDualSmoothing : ℝ)
    (state : Q₁ × Q₂) (k : ℕ) : Q₁ × Q₂ :=
  let μ₁ := algorithm_6_3_primal_smoothing initialPrimalSmoothing k
  let μ₂ := algorithm_6_3_dual_smoothing initialDualSmoothing k
  let τ := algorithm_6_3_step_size k
  let hτ := algorithm_6_3_step_size_mem_Icc k
  let xHat := predicted_primal_point hQ₁ (hxμ μ₁) state.1 state.2 τ hτ
  let uBarPlus := updated_dual_point hQ₂ (huμ μ₂) state.2 xHat τ hτ
  (updated_primal_point hQ₁ (hxμ (reduced_primal_smoothing μ₁ τ)) state.1 uBarPlus τ hτ,
    uBarPlus)

private def algorithm_6_3_odd_step
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂) (initialDualSmoothing : ℝ)
    (state : Q₁ × Q₂) (k : ℕ) : Q₁ × Q₂ :=
  let μ₂ := algorithm_6_3_dual_smoothing initialDualSmoothing k
  let τ := algorithm_6_3_step_size k
  let hτ := algorithm_6_3_step_size_mem_Icc k
  let uμ₂ := dualOracle uμ huμ μ₂
  (updatedPrimalPoint hQ₁ hQ₂ x₀ uμ₂ state.1 state.2 τ hτ,
    updatedDualPoint hQ₂ uμ₂ V state.1 state.2 τ hτ)

/-- The even-stage primal iterate is the Chapter 6 updated primal point
`\bar x_+ = (1 - τ) \bar x + τ x_{μ₁^+}(\bar u_+)`, with
`\hat x = (1 - τ) \bar x + τ x_{μ₁}(\bar u)` and
`\bar u_+ = (1 - τ) \bar u + τ u_{μ₂}(\hat x)`. -/
def algorithm_6_3_even_primal_iterate
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (xμ : ℝ → E₂ → E₁)
    (hxμ :
      ∀ μ : ℝ, ∀ u : E₂,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ u))
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (initialPrimalSmoothing initialDualSmoothing : ℝ)
    (state : Q₁ × Q₂) (k : ℕ) : Q₁ :=
  let μ₁ := algorithm_6_3_primal_smoothing initialPrimalSmoothing k
  let μ₂ := algorithm_6_3_dual_smoothing initialDualSmoothing k
  let τ := algorithm_6_3_step_size k
  let hτ := algorithm_6_3_step_size_mem_Icc k
  let xHat := predicted_primal_point hQ₁ (hxμ μ₁) state.1 state.2 τ hτ
  let uBarPlus := updated_dual_point hQ₂ (huμ μ₂) state.2 xHat τ hτ
  updated_primal_point hQ₁ (hxμ (reduced_primal_smoothing μ₁ τ)) state.1 uBarPlus τ hτ

/-- The even-stage dual iterate is the Chapter 6 updated dual point
`\bar u_+ = (1 - τ) \bar u + τ u_{μ₂}(\hat x)`. -/
def algorithm_6_3_even_dual_iterate
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (xμ : ℝ → E₂ → E₁)
    (hxμ :
      ∀ μ : ℝ, ∀ u : E₂,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ u))
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (initialPrimalSmoothing initialDualSmoothing : ℝ)
    (state : Q₁ × Q₂) (k : ℕ) : Q₂ :=
  let μ₁ := algorithm_6_3_primal_smoothing initialPrimalSmoothing k
  let μ₂ := algorithm_6_3_dual_smoothing initialDualSmoothing k
  let τ := algorithm_6_3_step_size k
  let hτ := algorithm_6_3_step_size_mem_Icc k
  let xHat := predicted_primal_point hQ₁ (hxμ μ₁) state.1 state.2 τ hτ
  updated_dual_point hQ₂ (huμ μ₂) state.2 xHat τ hτ

/-- The odd-stage primal iterate is the Chapter 6 strongly-convex-dual updated primal point
`\bar x_+ = (1 - τ) \bar x + τ x₀(\hat u)`. -/
def algorithm_6_3_odd_primal_iterate
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (x₀ : Q₂ → Q₁) (initialDualSmoothing : ℝ)
    (state : Q₁ × Q₂) (k : ℕ) : Q₁ :=
  let μ₂ := algorithm_6_3_dual_smoothing initialDualSmoothing k
  let τ := algorithm_6_3_step_size k
  let hτ := algorithm_6_3_step_size_mem_Icc k
  updatedPrimalPoint hQ₁ hQ₂ x₀ (dualOracle uμ huμ μ₂) state.1 state.2 τ hτ

/-- The odd-stage dual iterate is the Chapter 6 strongly-convex-dual updated dual point
`\bar u_+ = V(\hat u)`. -/
def algorithm_6_3_odd_dual_iterate
    (hQ₂ : Convex ℝ Q₂)
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (V : Q₂ → Q₂) (initialDualSmoothing : ℝ)
    (state : Q₁ × Q₂) (k : ℕ) : Q₂ :=
  let μ₂ := algorithm_6_3_dual_smoothing initialDualSmoothing k
  let τ := algorithm_6_3_step_size k
  let hτ := algorithm_6_3_step_size_mem_Icc k
  updatedDualPoint hQ₂ (dualOracle uμ huμ μ₂) V state.1 state.2 τ hτ

/-- Algorithm 6.3: given an initial pair `( \bar x₀, \bar u₀ )`, initial smoothing parameters
`μ₁,0`, `μ₂,0`, and the chapter's even and odd update owners, the alternating excessive-gap
method is the recursive state sequence that uses the chapter step size `τ_k = 2 / (k + 3)` and
applies the even branch at even indices and the odd branch at odd indices. -/
def alternatingExcessiveGapState
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (xμ : ℝ → E₂ → E₁)
    (hxμ :
      ∀ μ : ℝ, ∀ u : E₂,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ u))
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂)
    (initialPrimalSmoothing initialDualSmoothing : ℝ)
    (initialState : Q₁ × Q₂) : ℕ → Q₁ × Q₂
  | 0 => initialState
  | k + 1 =>
      let state :=
        alternatingExcessiveGapState
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
          k
      if Even k then
        algorithm_6_3_even_step
          hQ₁
          hQ₂
          xμ
          hxμ
          uμ
          huμ
          initialPrimalSmoothing
          initialDualSmoothing
          state
          k
      else
        algorithm_6_3_odd_step
          hQ₁
          hQ₂
          uμ
          huμ
          x₀
          V
          initialDualSmoothing
          state
          k

/-- The primal iterate sequence `\bar x_k` of Algorithm 6.3 is the first projection of the
alternating recursive state sequence. -/
def alternatingExcessiveGapPrimalIterate
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (xμ : ℝ → E₂ → E₁)
    (hxμ :
      ∀ μ : ℝ, ∀ u : E₂,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ u))
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂)
    (initialPrimalSmoothing initialDualSmoothing : ℝ)
    (initialState : Q₁ × Q₂) : ℕ → Q₁ :=
  fun k ↦
    (alternatingExcessiveGapState
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
        k).1

/-- The dual iterate sequence `\bar u_k` of Algorithm 6.3 is the second projection of the
alternating recursive state sequence. -/
def alternatingExcessiveGapDualIterate
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (xμ : ℝ → E₂ → E₁)
    (hxμ :
      ∀ μ : ℝ, ∀ u : E₂,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ u))
    (uμ : ℝ → E₁ → E₂)
    (huμ :
      ∀ μ : ℝ, ∀ x : E₁, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
    (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂)
    (initialPrimalSmoothing initialDualSmoothing : ℝ)
    (initialState : Q₁ × Q₂) : ℕ → Q₂ :=
  fun k ↦
    (alternatingExcessiveGapState
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
        k).2

section Recurrence

variable
    (initialPrimalSmoothing initialDualSmoothing : ℝ)
    (initialState : Q₁ × Q₂)

local notation "μ₁" =>
  algorithm_6_3_primal_smoothing initialPrimalSmoothing

local notation "μ₂" =>
  algorithm_6_3_dual_smoothing initialDualSmoothing

local notation "state" =>
  alternatingExcessiveGapState
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

@[simp] theorem alternatingExcessiveGapState_zero :
    state 0 = initialState :=
  rfl

@[simp] theorem alternatingExcessiveGapPrimalIterate_zero :
    x̄ 0 = initialState.1 :=
  rfl

@[simp] theorem alternatingExcessiveGapDualIterate_zero :
    ū 0 = initialState.2 :=
  rfl

/-- Expanding the primal iterate recovers the first projection of the recursive state sequence. -/
@[simp] theorem alternatingExcessiveGapPrimalIterate_eq_fst (k : ℕ) :
    x̄ k = (state k).1 :=
  rfl

/-- Expanding the dual iterate recovers the second projection of the recursive state sequence. -/
@[simp] theorem alternatingExcessiveGapDualIterate_eq_snd (k : ℕ) :
    ū k = (state k).2 :=
  rfl

/-- At an even stage `k`, the Algorithm 6.3 state update is the direct even branch at the current
smoothing parameters `μ₁,k`, `μ₂,k` and the chapter step size `τ_k`. -/
theorem alternatingExcessiveGapState_succ_of_even {k : ℕ} (hk : Even k) :
    state (k + 1) =
      (algorithm_6_3_even_primal_iterate
          hQ₁
          hQ₂
          xμ
          hxμ
          uμ
          huμ
          initialPrimalSmoothing
          initialDualSmoothing
          (state k)
          k,
        algorithm_6_3_even_dual_iterate
          hQ₁
          hQ₂
          xμ
          hxμ
          uμ
          huμ
          initialPrimalSmoothing
          initialDualSmoothing
          (state k)
          k) := by
  simp [alternatingExcessiveGapState, algorithm_6_3_even_step,
    algorithm_6_3_even_primal_iterate, algorithm_6_3_even_dual_iterate, hk]

/-- At an odd stage `k`, the Algorithm 6.3 state update is the direct odd branch at the current
smoothing parameters `μ₁,k`, `μ₂,k` and the chapter step size `τ_k`. -/
theorem alternatingExcessiveGapState_succ_of_odd {k : ℕ} (hk : Odd k) :
    state (k + 1) =
      (algorithm_6_3_odd_primal_iterate
          hQ₁
          hQ₂
          uμ
          huμ
          x₀
          initialDualSmoothing
          (state k)
          k,
        algorithm_6_3_odd_dual_iterate
          hQ₂
          uμ
          huμ
          V
          initialDualSmoothing
          (state k)
          k) := by
  simp [alternatingExcessiveGapState, algorithm_6_3_odd_step,
    algorithm_6_3_odd_primal_iterate, algorithm_6_3_odd_dual_iterate,
    Nat.not_even_iff_odd.mpr hk]

/-- At an even stage `k`, the primal iterate update of Algorithm 6.3 is the direct even-branch
primal update at the current smoothing parameters `μ₁,k`, `μ₂,k` and the chapter step size
`τ_k`. -/
theorem alternatingExcessiveGapPrimalIterate_succ_of_even {k : ℕ} (hk : Even k) :
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
        (state k)
        k := by
  simpa [alternatingExcessiveGapPrimalIterate] using
    congrArg Prod.fst
      (alternatingExcessiveGapState_succ_of_even
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
        hk)

/-- At an even stage `k`, the dual iterate update of Algorithm 6.3 is the direct even-branch
dual update at the current smoothing parameters `μ₁,k`, `μ₂,k` and the chapter step size
`τ_k`. -/
theorem alternatingExcessiveGapDualIterate_succ_of_even {k : ℕ} (hk : Even k) :
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
        (state k)
        k := by
  simpa [alternatingExcessiveGapDualIterate] using
    congrArg Prod.snd
      (alternatingExcessiveGapState_succ_of_even
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
        hk)

/-- At an odd stage `k`, the primal iterate update of Algorithm 6.3 is the direct odd-branch
primal update at the current smoothing parameters `μ₁,k`, `μ₂,k` and the chapter step size
`τ_k`. -/
theorem alternatingExcessiveGapPrimalIterate_succ_of_odd {k : ℕ} (hk : Odd k) :
    x̄ (k + 1) =
      algorithm_6_3_odd_primal_iterate
        hQ₁
        hQ₂
        uμ
        huμ
        x₀
        initialDualSmoothing
        (state k)
        k := by
  simpa [alternatingExcessiveGapPrimalIterate] using
    congrArg Prod.fst
      (alternatingExcessiveGapState_succ_of_odd
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
        hk)

/-- At an odd stage `k`, the dual iterate update of Algorithm 6.3 is the direct odd-branch
dual update at the current smoothing parameters `μ₁,k`, `μ₂,k` and the chapter step size
`τ_k`. -/
theorem alternatingExcessiveGapDualIterate_succ_of_odd {k : ℕ} (hk : Odd k) :
    ū (k + 1) =
      algorithm_6_3_odd_dual_iterate
        hQ₂
        uμ
        huμ
        V
        initialDualSmoothing
        (state k)
        k := by
  simpa [alternatingExcessiveGapDualIterate] using
    congrArg Prod.snd
      (alternatingExcessiveGapState_succ_of_odd
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
        hk)

end Recurrence

end Updates

/- The smoothing and recursion lemmas above are the public source-facing surface for later theorem
files. -/

end

end
