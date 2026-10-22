/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.InitialSublevelSet
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Basic

open Filter
open scoped Gradient

section NonmonotoneArmijo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Source/core/bridge triage:
-- * source-facing: the window/reference-value data and the exponent-indexed nonmonotone
--   Armijo acceptance test from Theorem 2.5.9;
-- * core/canonical: `IsBacktrackingLineSearchStep` for the geometric trial sequence
--   `h ↦ σ ^ h` along the scaled search direction `τ • d k`;
-- * bridge/view: the exponent view `nonmonotoneArmijoAcceptsAtExponent`, obtained by
--   evaluating the canonical backtracking owner on that geometric trial sequence.

/-- The backtracking steplength `τ σ^h` used at exponent `h`. -/
def nonmonotoneArmijoStep (τ σ : ℝ) (h : ℕ) : ℝ :=
  (σ ^ h) * τ

-- Semantic recall: `nonmonotoneArmijoReferenceValue` is the Chapter 2 owner for the bounded
-- recent-value window, `lineSearchObjective` is the chapter's canonical owner for the
-- one-dimensional search ray, and `HasGradientAt` is the generic calculus API that makes
-- `∇ f y` non-vacuous.

/-- The nonmonotone Armijo sufficient-decrease test expressed on the scaled search direction
`τ • d k`, with the trial parameter interpreted as the normalized backtracking factor. -/
def nonmonotoneArmijoBacktrackingAccepts
    (f : E → ℝ) (x g d : ℕ → E)
    (τ γ : ℝ) (m : ℕ → ℕ) (k : ℕ) (α : ℝ) (z : E) : Prop :=
  f z ≤
    nonmonotoneArmijoReferenceValue f x k (m k) +
      γ * α * inner ℝ (g k) (τ • d k)

/-- The nonmonotone Armijo sufficient-decrease test at iteration `k` and backtracking
exponent `h`. -/
def nonmonotoneArmijoAcceptsAtExponent
    (f : E → ℝ) (x g d : ℕ → E)
    (τ σ γ : ℝ) (m : ℕ → ℕ) (k h : ℕ) : Prop :=
  nonmonotoneArmijoBacktrackingAccepts f x g d τ γ m k (σ ^ h)
    (backtrackingTrialPoint (x k) (τ • d k) (fun h' ↦ σ ^ h') h)

/-- Unfolding `nonmonotoneArmijoAcceptsAtExponent` recovers the nonmonotone Armijo
sufficient-decrease inequality written with the explicit gradient data `g k`. -/
theorem nonmonotoneArmijoAcceptsAtExponent_iff
    {f : E → ℝ} {x g d : ℕ → E}
    {τ σ γ : ℝ} {m : ℕ → ℕ} {k h : ℕ} :
    nonmonotoneArmijoAcceptsAtExponent f x g d τ σ γ m k h ↔
      f (x k + nonmonotoneArmijoStep τ σ h • d k) ≤
        nonmonotoneArmijoReferenceValue f x k (m k) +
          γ * nonmonotoneArmijoStep τ σ h * inner ℝ (g k) (d k) := by
  simp [nonmonotoneArmijoAcceptsAtExponent, nonmonotoneArmijoBacktrackingAccepts,
    nonmonotoneArmijoStep, backtrackingTrialPoint, smul_smul, inner_smul_right, mul_assoc,
    mul_left_comm, mul_comm]

/-- `IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp` records the update rule
`x (k + 1) = x k + α k • d k`, the nonzero search directions, the admissible parameters
`τ > 0` and `γ ∈ (0, 1)`, the window-size recursion
`m (k + 1) ≤ min (m k + 1) M` with `m 0 = 0`, and the fact that `exp k` is the first
accepted exponent in the nonmonotone Armijo test computed from the explicit gradient
data `g k`, packaged through the chapter's canonical backtracking-line-search owner for
the geometric trial sequence `h ↦ σ ^ h` on the scaled direction `τ • d k` (which
therefore forces `σ ∈ (0, 1)`), with
`α k = nonmonotoneArmijoStep τ σ (exp k)`. -/
class IsNonmonotoneArmijoLineSearch
    (f : E → ℝ) (x g d : ℕ → E) (α : ℕ → ℝ)
    (τ σ γ : ℝ) (M : ℕ) (m exp : ℕ → ℕ) : Prop where
  direction_ne : ∀ k, d k ≠ 0
  update : ∀ k, x (k + 1) = x k + α k • d k
  tau_pos : 0 < τ
  gamma_mem_Ioo : γ ∈ Set.Ioo (0 : ℝ) 1
  m_zero : m 0 = 0
  m_step : ∀ k, m (k + 1) ≤ min (m k + 1) M
  alpha_eq : ∀ k, α k = nonmonotoneArmijoStep τ σ (exp k)
  backtrackingStep :
    ∀ k,
      IsBacktrackingLineSearchStep
        (nonmonotoneArmijoBacktrackingAccepts f x g d τ γ m k)
        (x k) (τ • d k) (fun h ↦ σ ^ h) (exp k)

/-- A nonmonotone Armijo line-search witness is proposition-valued, hence subsingleton. -/
instance isNonmonotoneArmijoLineSearchSubsingleton
    (f : E → ℝ) (x g d : ℕ → E) (α : ℕ → ℝ)
    (τ σ γ : ℝ) (M : ℕ) (m exp : ℕ → ℕ) :
    Subsingleton (IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp) := inferInstance

/-- The geometric backtracking owner in a nonmonotone Armijo run forces the shrink factor
`σ` to lie in `(0, 1)`. -/
theorem IsNonmonotoneArmijoLineSearch.sigma_mem_Ioo
    {f : E → ℝ} {x g d : ℕ → E} {α : ℕ → ℝ}
    {τ σ γ : ℝ} {M : ℕ} {m exp : ℕ → ℕ}
    (hLineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp) :
    σ ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · simpa using (hLineSearch.backtrackingStep 0).step_pos 1
  · simpa using (hLineSearch.backtrackingStep 0).strictReduction 0

/-- The canonical backtracking owner carried by a nonmonotone Armijo run implies that
`exp k` satisfies the source-facing exponent-indexed acceptance test. -/
theorem IsNonmonotoneArmijoLineSearch.acceptsAtExponent
    {f : E → ℝ} {x g d : ℕ → E} {α : ℕ → ℝ}
    {τ σ γ : ℝ} {M : ℕ} {m exp : ℕ → ℕ}
    (hLineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp) (k : ℕ) :
    nonmonotoneArmijoAcceptsAtExponent f x g d τ σ γ m k (exp k) := by
  simpa [nonmonotoneArmijoAcceptsAtExponent] using
    (hLineSearch.backtrackingStep k).accepts

/-- The canonical backtracking owner carried by a nonmonotone Armijo run recovers the
source-facing least-accepted-exponent statement. -/
theorem IsNonmonotoneArmijoLineSearch.isLeastAcceptedExponent
    {f : E → ℝ} {x g d : ℕ → E} {α : ℕ → ℝ}
    {τ σ γ : ℝ} {M : ℕ} {m exp : ℕ → ℕ}
    (hLineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp) (k : ℕ) :
    IsLeast {h' : ℕ | nonmonotoneArmijoAcceptsAtExponent f x g d τ σ γ m k h'} (exp k) := by
  simpa [nonmonotoneArmijoAcceptsAtExponent] using
    (hLineSearch.backtrackingStep k).isLeastAcceptedIndex

/-- Any exponent smaller than the accepted one fails the source-facing nonmonotone Armijo
acceptance test. -/
theorem IsNonmonotoneArmijoLineSearch.not_acceptsAtExponent_of_lt
    {f : E → ℝ} {x g d : ℕ → E} {α : ℕ → ℝ}
    {τ σ γ : ℝ} {M : ℕ} {m exp : ℕ → ℕ} {k h : ℕ}
    (hLineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp)
    (hh : h < exp k) :
    ¬ nonmonotoneArmijoAcceptsAtExponent f x g d τ σ γ m k h := by
  simpa [nonmonotoneArmijoAcceptsAtExponent] using
    (hLineSearch.backtrackingStep k).not_accepts_of_lt hh

/-- Any exponent satisfying the source-facing nonmonotone Armijo acceptance test is at least the
accepted exponent `exp k`. -/
theorem IsNonmonotoneArmijoLineSearch.le_of_acceptsAtExponent
    {f : E → ℝ} {x g d : ℕ → E} {α : ℕ → ℝ}
    {τ σ γ : ℝ} {M : ℕ} {m exp : ℕ → ℕ} {k h : ℕ}
    (hLineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp)
    (hAccepts : nonmonotoneArmijoAcceptsAtExponent f x g d τ σ γ m k h) :
    exp k ≤ h := by
  simpa [nonmonotoneArmijoAcceptsAtExponent] using
    (hLineSearch.backtrackingStep k).le_of_accepts hAccepts

/-- Expanding `IsNonmonotoneArmijoLineSearch` gives the explicit update, the nonredundant
parameter data, the window recursion, the accepted step formula, and the canonical
backtracking-step owner from which `σ ∈ (0, 1)` is derived separately. -/
theorem isNonmonotoneArmijoLineSearch_iff
    {f : E → ℝ} {x g d : ℕ → E} {α : ℕ → ℝ}
    {τ σ γ : ℝ} {M : ℕ} {m exp : ℕ → ℕ} :
    IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp ↔
      (∀ k, d k ≠ 0) ∧
        (∀ k, x (k + 1) = x k + α k • d k) ∧
        0 < τ ∧
        γ ∈ Set.Ioo (0 : ℝ) 1 ∧
        m 0 = 0 ∧
        (∀ k, m (k + 1) ≤ min (m k + 1) M) ∧
        (∀ k, α k = nonmonotoneArmijoStep τ σ (exp k)) ∧
        ∀ k,
          IsBacktrackingLineSearchStep
            (nonmonotoneArmijoBacktrackingAccepts f x g d τ γ m k)
            (x k) (τ • d k) (fun h ↦ σ ^ h) (exp k) := by
  constructor
  · intro h
    exact ⟨h.direction_ne, h.update, h.tau_pos, h.gamma_mem_Ioo, h.m_zero, h.m_step,
      h.alpha_eq, h.backtrackingStep⟩
  · rintro ⟨hDirection, hUpdate, hTau, hGamma, hmZero, hmStep, hAlpha, hBacktracking⟩
    exact
      { direction_ne := hDirection
        update := hUpdate
        tau_pos := hTau
        gamma_mem_Ioo := hGamma
        m_zero := hmZero
        m_step := hmStep
        alpha_eq := hAlpha
        backtrackingStep := hBacktracking }

end NonmonotoneArmijo

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable
  (f : E → ℝ) (x g d : ℕ → E) (α : ℕ → ℝ)
  (τ σ γ c1 c2 : ℝ) (M : ℕ) (m exp : ℕ → ℕ)

/-- Helper for Chapter02 Theorem 2.5.9: if every iterate in the current nonmonotone Armijo
window belongs to the initial sublevel set, then the reference value of that window is bounded by
the initial objective value. -/
lemma nonmonotoneArmijo_referenceValue_le_initialValue
    {k mk : ℕ}
    (h_mem :
      ∀ j ∈ nonmonotoneArmijoWindow k mk,
        x (k - j) ∈ initialSublevelSet f (x 0)) :
    nonmonotoneArmijoReferenceValue f x k mk ≤ f (x 0) := by
  -- The window maximum is bounded once every window entry is bounded by `f (x 0)`.
  rw [nonmonotoneArmijoReferenceValue_eq]
  exact Finset.sup'_le _ _ fun j hj ↦ h_mem j hj

/-- Chapter02 Theorem 2.5.9 (1): if `x`, `d`, and `α` satisfy the nonmonotone Armijo
line-search update with parameters `τ`, `σ`, `γ`, and memory bound `M`, and if the search
directions satisfy the descent bound
`inner ℝ (g k) (d k) ≤ -c1 * ‖g k‖^2` whenever
`x k ∈ initialSublevelSet f (x 0)`, then every iterate remains in
`initialSublevelSet f (x 0)`. This sublevel-invariance step uses only the update and accepted-step
data of the nonmonotone Armijo run together with the descent inequality; compactness,
gradient-regularity, and direction-norm hypotheses belong to later parts of the theorem,
not to this part `(1)`. -/
theorem nonmonotoneArmijoLineSearch_iterates_mem_initialSublevelSet
    (hc1 : 0 < c1)
    (h_descent :
      ∀ k,
        x k ∈ initialSublevelSet f (x 0) →
        inner ℝ (g k) (d k) ≤ -c1 * ‖g k‖ ^ (2 : ℕ))
    (h_lineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp)
    (k : ℕ) : x k ∈ initialSublevelSet f (x 0) := by
  refine Nat.strong_induction_on k ?_
  intro k ih
  cases k with
  | zero =>
      -- The initial iterate belongs to its own initial sublevel set.
      simp [initialSublevelSet]
  | succ k =>
      have hk_mem : x k ∈ initialSublevelSet f (x 0) :=
        ih k (Nat.lt_succ_self k)
      have hAccepts : nonmonotoneArmijoAcceptsAtExponent f x g d τ σ γ m k (exp k) :=
        h_lineSearch.acceptsAtExponent k
      rw [nonmonotoneArmijoAcceptsAtExponent_iff] at hAccepts
      have hReference_le :
          nonmonotoneArmijoReferenceValue f x k (m k) ≤ f (x 0) := by
        -- Every window entry is an earlier iterate, so strong induction bounds each one.
        refine nonmonotoneArmijo_referenceValue_le_initialValue
          (f := f) (x := x) (k := k) (mk := m k) ?_
        intro j hj
        exact ih (k - j) <| lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self k)
      have hInner_nonpos : inner ℝ (g k) (d k) ≤ 0 := by
        have hNeg_nonpos : -c1 * ‖g k‖ ^ (2 : ℕ) ≤ 0 := by
          nlinarith [hc1, sq_nonneg ‖g k‖]
        exact le_trans (h_descent k hk_mem) hNeg_nonpos
      have hStep_nonneg : 0 ≤ nonmonotoneArmijoStep τ σ (exp k) := by
        have hSigma_pos : 0 < σ := h_lineSearch.sigma_mem_Ioo.1
        exact le_of_lt <| mul_pos (pow_pos hSigma_pos _) h_lineSearch.tau_pos
      have hCorrection_nonpos :
          γ * nonmonotoneArmijoStep τ σ (exp k) * inner ℝ (g k) (d k) ≤ 0 := by
        have hGamma_nonneg : 0 ≤ γ := le_of_lt h_lineSearch.gamma_mem_Ioo.1
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg hGamma_nonneg hStep_nonneg) hInner_nonpos
      -- The accepted step stays below the bounded reference value because the Armijo
      -- correction term is nonpositive on descent directions.
      calc
        f (x (k + 1)) = f (x k + nonmonotoneArmijoStep τ σ (exp k) • d k) := by
          rw [h_lineSearch.update k, h_lineSearch.alpha_eq k]
        _ ≤
            nonmonotoneArmijoReferenceValue f x k (m k) +
              γ * nonmonotoneArmijoStep τ σ (exp k) * inner ℝ (g k) (d k) :=
          hAccepts
        _ ≤ f (x 0) := by
          linarith [hReference_le, hCorrection_nonpos]

/-- Helper for Chapter02 Theorem 2.5.9: the bounded-memory nonmonotone Armijo reference values
form a stepwise antitone sequence. -/
lemma nonmonotoneArmijo_referenceValue_antitone
    (hc1 : 0 < c1)
    (h_descent :
      ∀ k,
        x k ∈ initialSublevelSet f (x 0) →
        inner ℝ (g k) (d k) ≤ -c1 * ‖g k‖ ^ (2 : ℕ))
    (h_lineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp)
    (k : ℕ) :
    nonmonotoneArmijoReferenceValue f x (k + 1) (m (k + 1)) ≤
      nonmonotoneArmijoReferenceValue f x k (m k) := by
  have hk_mem :
      x k ∈ initialSublevelSet f (x 0) :=
    nonmonotoneArmijoLineSearch_iterates_mem_initialSublevelSet
      (f := f) (x := x) (g := g) (d := d) (α := α) (τ := τ) (σ := σ) (γ := γ)
      (c1 := c1) (M := M) (m := m) (exp := exp) hc1 h_descent h_lineSearch k
  have hAccepts : nonmonotoneArmijoAcceptsAtExponent f x g d τ σ γ m k (exp k) :=
    h_lineSearch.acceptsAtExponent k
  rw [nonmonotoneArmijoAcceptsAtExponent_iff] at hAccepts
  have hInner_nonpos : inner ℝ (g k) (d k) ≤ 0 := by
    have hNeg_nonpos : -c1 * ‖g k‖ ^ (2 : ℕ) ≤ 0 := by
      nlinarith [hc1, sq_nonneg ‖g k‖]
    exact le_trans (h_descent k hk_mem) hNeg_nonpos
  have hStep_nonneg : 0 ≤ nonmonotoneArmijoStep τ σ (exp k) := by
    have hSigma_pos : 0 < σ := h_lineSearch.sigma_mem_Ioo.1
    exact le_of_lt <| mul_pos (pow_pos hSigma_pos _) h_lineSearch.tau_pos
  have hCorrection_nonpos :
      γ * nonmonotoneArmijoStep τ σ (exp k) * inner ℝ (g k) (d k) ≤ 0 := by
    have hGamma_nonneg : 0 ≤ γ := le_of_lt h_lineSearch.gamma_mem_Ioo.1
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hGamma_nonneg hStep_nonneg) hInner_nonpos
  rw [nonmonotoneArmijoReferenceValue_eq]
  refine Finset.sup'_le _ _ ?_
  intro j hj
  rcases mem_nonmonotoneArmijoWindow.mp hj with ⟨hjk, hjm⟩
  cases j with
  | zero =>
      -- The newest value is controlled by the accepted Armijo decrease.
      calc
        f (x (k + 1)) = f (x k + nonmonotoneArmijoStep τ σ (exp k) • d k) := by
          rw [h_lineSearch.update k, h_lineSearch.alpha_eq k]
        _ ≤
            nonmonotoneArmijoReferenceValue f x k (m k) +
              γ * nonmonotoneArmijoStep τ σ (exp k) * inner ℝ (g k) (d k) :=
          hAccepts
        _ ≤ nonmonotoneArmijoReferenceValue f x k (m k) := by
          linarith
  | succ j =>
      -- Any older value in the new window already belonged to the previous window.
      have hjk' : j ≤ k := Nat.succ_le_succ_iff.mp hjk
      have hjm' : j ≤ m k := by
        have hm_step : m (k + 1) ≤ m k + 1 := le_trans (h_lineSearch.m_step k) (Nat.min_le_left _ _)
        exact Nat.succ_le_succ_iff.mp (le_trans hjm hm_step)
      have hj_mem : j ∈ nonmonotoneArmijoWindow k (m k) :=
        (mem_nonmonotoneArmijoWindow).2 ⟨hjk', hjm'⟩
      have hOld_le :
          f (x (k - j)) ≤ nonmonotoneArmijoReferenceValue f x k (m k) := by
        rw [nonmonotoneArmijoReferenceValue_eq]
        exact
          Finset.le_sup'
            (s := nonmonotoneArmijoWindow k (m k))
            (f := fun i ↦ f (x (k - i))) hj_mem
      simpa [Nat.succ_sub_succ_eq_sub] using hOld_le

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable
  (f : E → ℝ) (x g d : ℕ → E) (α : ℕ → ℝ)
  (τ σ γ c1 c2 : ℝ) (M : ℕ) (m exp : ℕ → ℕ)

/-- Helper for Chapter02 Theorem 2.5.9: every bounded nonmonotone Armijo window contains an
actual iterate where the reference value is attained. -/
lemma nonmonotoneArmijo_reference_argmax
    (k : ℕ) :
    ∃ ell,
      k - m k ≤ ell ∧
        ell ≤ k ∧
          nonmonotoneArmijoReferenceValue f x k (m k) = f (x ell) := by
  rw [nonmonotoneArmijoReferenceValue_eq]
  obtain ⟨j, hj, hjmax⟩ :=
    Finset.exists_mem_eq_sup'
      (s := nonmonotoneArmijoWindow k (m k))
      (H := nonmonotoneArmijoWindow_nonempty k (m k))
      (f := fun i ↦ f (x (k - i)))
  rcases mem_nonmonotoneArmijoWindow.mp hj with ⟨hjk, hjm⟩
  refine ⟨k - j, Nat.sub_le_sub_left hjm k, Nat.sub_le _ _, ?_⟩
  simpa using hjmax

/-- Helper for Chapter02 Theorem 2.5.9: the bounded-memory reference values converge because
they form an antitone real sequence and each reference value is attained inside the compact
initial sublevel set. -/
lemma nonmonotoneArmijo_reference_value_converges
    (h_compact : IsCompact (initialSublevelSet f (x 0)))
    (h_hasGradient :
      ∀ y ∈ initialSublevelSet f (x 0), ∃ gy : E, HasGradientVectorAt f gy y)
    (h_mem : ∀ k, x k ∈ initialSublevelSet f (x 0))
    (h_reference_step :
      ∀ k,
        nonmonotoneArmijoReferenceValue f x (k + 1) (m (k + 1)) ≤
          nonmonotoneArmijoReferenceValue f x k (m k)) :
    ∃ cInf : ℝ,
      Tendsto (fun k ↦ nonmonotoneArmijoReferenceValue f x k (m k)) atTop (nhds cInf) := by
  let c : ℕ → ℝ := fun k ↦ nonmonotoneArmijoReferenceValue f x k (m k)
  have hc_antitone : Antitone c := by
    exact antitone_nat_of_succ_le h_reference_step
  have h_continuous :
      ContinuousOn f (initialSublevelSet f (x 0)) := by
    intro y hy
    rcases h_hasGradient y hy with ⟨gy, hgy⟩
    exact hgy.differentiableAt.continuousAt.continuousWithinAt
  have h_bddBelow_image :
      BddBelow (f '' initialSublevelSet f (x 0)) :=
    h_compact.bddBelow_image h_continuous
  have h_bddBelow_c : BddBelow (Set.range c) := by
    rcases h_bddBelow_image with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro _ ⟨k, rfl⟩
    rcases nonmonotoneArmijo_reference_argmax
        (f := f) (x := x) (m := m) k with ⟨ell, -, -, hell⟩
    have hell_mem : x ell ∈ initialSublevelSet f (x 0) := h_mem ell
    have hb_ell : b ≤ f (x ell) := by
      exact hb ⟨x ell, hell_mem, rfl⟩
    simpa [c, hell] using hb_ell
  exact Real.tendsto_of_bddBelow_antitone h_bddBelow_c hc_antitone

/-- Helper for Chapter02 Theorem 2.5.9: after one full memory block, the later reference window
contains some accepted step whose Armijo correction is controlled by the drop of the reference
value. -/
lemma nonmonotoneArmijo_reference_drop_has_small_correction
    (h_reference_step :
      ∀ k,
        nonmonotoneArmijoReferenceValue f x (k + 1) (m (k + 1)) ≤
          nonmonotoneArmijoReferenceValue f x k (m k))
    (h_lineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp)
    (k : ℕ) :
    ∃ i,
      k ≤ i ∧
        i ≤ k + M ∧
          γ * (α i * (- inner ℝ (g i) (d i))) ≤
            nonmonotoneArmijoReferenceValue f x k (m k) -
              nonmonotoneArmijoReferenceValue f x (k + M + 1) (m (k + M + 1)) := by
  let c : ℕ → ℝ := fun n ↦ nonmonotoneArmijoReferenceValue f x n (m n)
  have hc_antitone : Antitone c := by
    exact antitone_nat_of_succ_le h_reference_step
  have hm_bound : m (k + M + 1) ≤ M := by
    have hm_step : m (k + M + 1) ≤ min (m (k + M) + 1) M := by
      simpa [Nat.add_assoc] using h_lineSearch.m_step (k + M)
    exact le_trans hm_step (Nat.min_le_right _ _)
  rcases nonmonotoneArmijo_reference_argmax
      (f := f) (x := x) (m := m) (k + M + 1) with
    ⟨ell, hell_low, hell_hi, hell_eq⟩
  have hm_total : m (k + M + 1) ≤ k + M + 1 := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      le_trans hm_bound (Nat.le_add_left M (k + 1))
  have hEll_ge : k + 1 ≤ ell := by
    have hbase : k + 1 ≤ k + M + 1 - m (k + M + 1) := by
      exact (Nat.le_sub_iff_add_le hm_total).2 <| by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          add_le_add_left hm_bound (k + 1)
    exact le_trans hbase hell_low
  let i : ℕ := ell - 1
  have hi_succ : i + 1 = ell := by
    dsimp [i]
    exact Nat.sub_add_cancel (le_trans (Nat.succ_le_succ (Nat.zero_le k)) hEll_ge)
  have hi_ge : k ≤ i := by
    dsimp [i]
    exact Nat.le_pred_of_lt (lt_of_lt_of_le (Nat.lt_succ_self k) hEll_ge)
  have hi_le : i ≤ k + M := by
    exact Nat.succ_le_succ_iff.mp <| by
      simpa [hi_succ] using hell_hi
  have hAccepts : nonmonotoneArmijoAcceptsAtExponent f x g d τ σ γ m i (exp i) :=
    h_lineSearch.acceptsAtExponent i
  rw [nonmonotoneArmijoAcceptsAtExponent_iff] at hAccepts
  have hAcceptedValue :
      f (x ell) ≤ c i + γ * α i * inner ℝ (g i) (d i) := by
    -- Rewrite the accepted trial at `i` as the actual iterate `x (i + 1) = x ell`.
    calc
      f (x ell) = f (x (i + 1)) := by rw [hi_succ]
      _ = f (x i + nonmonotoneArmijoStep τ σ (exp i) • d i) := by
        rw [h_lineSearch.update i, h_lineSearch.alpha_eq i]
      _ ≤ c i + γ * nonmonotoneArmijoStep τ σ (exp i) * inner ℝ (g i) (d i) :=
        hAccepts
      _ = c i + γ * α i * inner ℝ (g i) (d i) := by
        rw [h_lineSearch.alpha_eq i]
  have hci_le : c i ≤ c k := hc_antitone hi_ge
  refine ⟨i, hi_ge, hi_le, ?_⟩
  -- The later maximizing value is therefore controlled by the earlier reference drop and
  -- a single accepted Armijo correction inside the block `[k, k + M]`.
  have hLater_le :
      c (k + M + 1) ≤ c k + γ * α i * inner ℝ (g i) (d i) := by
    simpa [c, hell_eq] using
      le_trans hAcceptedValue
        (by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hci_le (γ * α i * inner ℝ (g i) (d i)))
  linarith

/-- Helper for Chapter02 Theorem 2.5.9: choosing one correction from each bounded memory block
produces a bounded-lag selector whose Armijo correction tends to zero. -/
lemma nonmonotoneArmijo_small_correction_selector_tendsto_zero
    (h_mem : ∀ k, x k ∈ initialSublevelSet f (x 0))
    (hc1 : 0 < c1)
    (h_descent :
      ∀ k,
        x k ∈ initialSublevelSet f (x 0) →
          inner ℝ (g k) (d k) ≤ -c1 * ‖g k‖ ^ (2 : ℕ))
    (h_reference_step :
      ∀ k,
        nonmonotoneArmijoReferenceValue f x (k + 1) (m (k + 1)) ≤
          nonmonotoneArmijoReferenceValue f x k (m k))
    (h_reference_tendsto :
      ∃ cInf : ℝ,
        Tendsto (fun k ↦ nonmonotoneArmijoReferenceValue f x k (m k)) atTop (nhds cInf))
    (h_lineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp) :
    ∃ ψ : ℕ → ℕ,
      (∀ k, k ≤ ψ k ∧ ψ k ≤ k + M) ∧
        Tendsto
          (fun k ↦ α (ψ k) * (- inner ℝ (g (ψ k)) (d (ψ k))))
          atTop (nhds 0) := by
  classical
  let c : ℕ → ℝ := fun n ↦ nonmonotoneArmijoReferenceValue f x n (m n)
  obtain ⟨cInf, hcTendsto⟩ := h_reference_tendsto
  have hShift :
      Tendsto (fun k ↦ c (k + (M + 1))) atTop (nhds cInf) := by
    exact (Filter.tendsto_add_atTop_iff_nat (M + 1)).2 hcTendsto
  have hDrop :
      Tendsto (fun k ↦ c k - c (k + (M + 1))) atTop (nhds 0) := by
    simpa [c] using hcTendsto.sub hShift
  have hChoose :
      ∀ k,
        ∃ i,
          k ≤ i ∧
            i ≤ k + M ∧
              γ * (α i * (- inner ℝ (g i) (d i))) ≤ c k - c (k + (M + 1)) := by
    intro k
    simpa [c, Nat.add_assoc] using
      nonmonotoneArmijo_reference_drop_has_small_correction
        (f := f) (x := x) (g := g) (d := d) (α := α) (τ := τ) (σ := σ) (γ := γ)
        (M := M) (m := m) (exp := exp)
        h_reference_step h_lineSearch k
  choose ψ hψ_ge hψ_le hψ_drop using hChoose
  have hGamma_nonneg : 0 ≤ γ := le_of_lt h_lineSearch.gamma_mem_Ioo.1
  have hScaled :
      Tendsto
        (fun k ↦ γ * (α (ψ k) * (- inner ℝ (g (ψ k)) (d (ψ k)))))
        atTop (nhds 0) := by
    refine squeeze_zero
      (fun k ↦ ?_)
      (fun k ↦ hψ_drop k)
      hDrop
    have hAlpha_nonneg : 0 ≤ α (ψ k) := by
      rw [h_lineSearch.alpha_eq (ψ k), nonmonotoneArmijoStep]
      exact le_of_lt <| mul_pos (pow_pos h_lineSearch.sigma_mem_Ioo.1 _) h_lineSearch.tau_pos
    have hInner_nonpos : inner ℝ (g (ψ k)) (d (ψ k)) ≤ 0 := by
      have hNeg_nonpos : -c1 * ‖g (ψ k)‖ ^ (2 : ℕ) ≤ 0 := by
        nlinarith [hc1, sq_nonneg ‖g (ψ k)‖]
      exact le_trans (h_descent (ψ k) (h_mem (ψ k))) hNeg_nonpos
    have hCorrection_nonneg :
        0 ≤ α (ψ k) * (- inner ℝ (g (ψ k)) (d (ψ k))) := by
      exact mul_nonneg hAlpha_nonneg (neg_nonneg.mpr hInner_nonpos)
    exact mul_nonneg hGamma_nonneg hCorrection_nonneg
  refine ⟨ψ, ?_, ?_⟩
  · intro k
    exact ⟨hψ_ge k, hψ_le k⟩
  · have hGamma_ne : γ ≠ 0 := ne_of_gt h_lineSearch.gamma_mem_Ioo.1
    have hRescaled :
        Tendsto
          (fun k ↦ γ⁻¹ * (γ * (α (ψ k) * (- inner ℝ (g (ψ k)) (d (ψ k))))))
          atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hScaled)
    simpa [mul_assoc, hGamma_ne] using hRescaled

omit f x τ σ γ c1 c2 m exp in
/-- Helper for Chapter02 Theorem 2.5.9: composing the bounded-lag small-correction selector
with the convergent subsequence keeps the same bounded-window control and transports the
vanishing Armijo correction onto the selected cluster branch. -/
lemma nonmonotoneArmijo_selector_cluster_correction_tendsto_zero
    {φ ψ : ℕ → ℕ}
    (hψ : ∀ k, k ≤ ψ k ∧ ψ k ≤ k + M)
    (h_small :
      Tendsto
        (fun k ↦ α (ψ k) * (- inner ℝ (g (ψ k)) (d (ψ k))))
        atTop (nhds 0))
    (hφ : StrictMono φ) :
    ∃ θ : ℕ → ℕ,
      (∀ n, φ n ≤ θ n ∧ θ n ≤ φ n + M) ∧
        Tendsto
          (fun n ↦ α (θ n) * (- inner ℝ (g (θ n)) (d (θ n))))
          atTop (nhds 0) := by
  let θ : ℕ → ℕ := fun n ↦ ψ (φ n)
  refine ⟨θ, ?_, ?_⟩
  · intro n
    -- The composed selector still lands in the same bounded memory window.
    simpa [θ] using hψ (φ n)
  · -- The zero-correction limit composes with the strictly monotone subsequence `φ`.
    change Tendsto
      ((fun k ↦ α (ψ k) * (- inner ℝ (g (ψ k)) (d (ψ k)))) ∘ φ)
      atTop (nhds 0)
    exact h_small.comp hφ.tendsto_atTop

/-- Helper for Chapter02 Theorem 2.5.9: a positive quadratic lower bound against a scalar
sequence tending to `0` forces the underlying quantity to tend to `0`. -/
lemma nonmonotoneArmijo_tendsto_zero_of_mul_sq_le_of_tendsto_zero
    {a : ℝ} (ha : 0 < a) {u v : ℕ → ℝ}
    (hbound : ∀ k, a * u k ^ (2 : ℕ) ≤ v k)
    (hv : Tendsto v atTop (nhds 0)) :
    Tendsto u atTop (nhds 0) := by
  -- First transport the zero limit onto the nonnegative quadratic lower bound.
  have hau_sq : Tendsto (fun k ↦ a * u k ^ (2 : ℕ)) atTop (nhds 0) := by
    refine squeeze_zero ?_ hbound hv
    intro k
    positivity
  have hu_sq : Tendsto (fun k ↦ u k ^ (2 : ℕ)) atTop (nhds 0) := by
    simpa [one_div, ha.ne', mul_assoc] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ 1 / a) atTop (nhds (1 / a))).mul hau_sq)
  -- Then take square roots to pass from `u^2 → 0` to `|u| → 0`.
  have hu_abs : Tendsto (fun k ↦ |u k|) atTop (nhds 0) := by
    simpa [Real.sqrt_sq_eq_abs] using Filter.Tendsto.sqrt hu_sq
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 hu_abs

/-- Helper for Chapter02 Theorem 2.5.9: once the selected Armijo correction tends to `0`, the
actual selector step gaps `dist (x (θ n + 1)) (x (θ n))` also tend to `0`. -/
lemma nonmonotoneArmijo_theta_step_gap_tendsto_zero
    {θ : ℕ → ℕ}
    (h_mem : ∀ k, x k ∈ initialSublevelSet f (x 0))
    (hc1 : 0 < c1) (hc2 : 0 < c2)
    (h_descent :
      ∀ k,
        x k ∈ initialSublevelSet f (x 0) →
          inner ℝ (g k) (d k) ≤ -c1 * ‖g k‖ ^ (2 : ℕ))
    (h_dir_bound :
      ∀ k,
        x k ∈ initialSublevelSet f (x 0) →
          ‖d k‖ ≤ c2 * ‖g k‖)
    (h_lineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp)
    (h_small :
      Tendsto
        (fun n ↦ α (θ n) * (- inner ℝ (g (θ n)) (d (θ n))))
        atTop (nhds 0)) :
    Tendsto (fun n ↦ dist (x (θ n + 1)) (x (θ n))) atTop (nhds 0) := by
  have hScaled :
      Tendsto
        (fun n ↦ (τ * c2 ^ (2 : ℕ)) *
          (α (θ n) * (- inner ℝ (g (θ n)) (d (θ n)))))
        atTop (nhds 0) := by
    simpa [mul_assoc] using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ τ * c2 ^ (2 : ℕ)) atTop (nhds (τ * c2 ^ (2 : ℕ)))).mul h_small)
  refine nonmonotoneArmijo_tendsto_zero_of_mul_sq_le_of_tendsto_zero
    (a := c1) hc1 ?_ hScaled
  intro n
  have hn_mem : x (θ n) ∈ initialSublevelSet f (x 0) := h_mem (θ n)
  have hAlpha_nonneg : 0 ≤ α (θ n) := by
    rw [h_lineSearch.alpha_eq (θ n), nonmonotoneArmijoStep]
    exact le_of_lt <| mul_pos (pow_pos h_lineSearch.sigma_mem_Ioo.1 _) h_lineSearch.tau_pos
  have hAlpha_le_tau : α (θ n) ≤ τ := by
    rw [h_lineSearch.alpha_eq (θ n), nonmonotoneArmijoStep]
    have hPow_le_one :
        σ ^ exp (θ n) ≤ 1 := by
      exact pow_le_one₀ (le_of_lt h_lineSearch.sigma_mem_Ioo.1) (le_of_lt h_lineSearch.sigma_mem_Ioo.2)
    calc
      σ ^ exp (θ n) * τ ≤ 1 * τ := by
        exact mul_le_mul_of_nonneg_right hPow_le_one (le_of_lt h_lineSearch.tau_pos)
      _ = τ := by ring
  have hDir_sq :
      ‖d (θ n)‖ ^ (2 : ℕ) ≤ c2 ^ (2 : ℕ) * ‖g (θ n)‖ ^ (2 : ℕ) := by
    have hDir_sq_raw :
        ‖d (θ n)‖ ^ (2 : ℕ) ≤ (c2 * ‖g (θ n)‖) ^ (2 : ℕ) := by
      exact sq_le_sq.mpr <| by
        simpa [abs_of_nonneg (norm_nonneg _),
          abs_of_nonneg (mul_nonneg (le_of_lt hc2) (norm_nonneg _))] using
          h_dir_bound (θ n) hn_mem
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hDir_sq_raw
  have hDescent_sq :
      c1 * ‖g (θ n)‖ ^ (2 : ℕ) ≤ - inner ℝ (g (θ n)) (d (θ n)) := by
    nlinarith [h_descent (θ n) hn_mem]
  have hDist_eq :
      dist (x (θ n + 1)) (x (θ n)) = α (θ n) * ‖d (θ n)‖ := by
    have hDist_eq_abs :
        dist (x (θ n + 1)) (x (θ n)) = |α (θ n)| * ‖d (θ n)‖ := by
      rw [dist_eq_norm, h_lineSearch.update (θ n), add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs]
    calc
      dist (x (θ n + 1)) (x (θ n)) = |α (θ n)| * ‖d (θ n)‖ := hDist_eq_abs
      _ = α (θ n) * ‖d (θ n)‖ := by rw [abs_of_nonneg hAlpha_nonneg]
  -- The Armijo correction dominates the squared step gap through the descent and direction
  -- estimates, exactly as in the source proof's "small correction implies small motion" step.
  have hStep_sq_bound :
      c1 * dist (x (θ n + 1)) (x (θ n)) ^ (2 : ℕ) ≤
        (τ * c2 ^ (2 : ℕ)) * (α (θ n) * (- inner ℝ (g (θ n)) (d (θ n)))) := by
    have hAlpha_sq : α (θ n) ^ (2 : ℕ) ≤ τ * α (θ n) := by
      nlinarith [hAlpha_nonneg, hAlpha_le_tau]
    have hDist_sq :
        dist (x (θ n + 1)) (x (θ n)) ^ (2 : ℕ) =
          α (θ n) ^ (2 : ℕ) * ‖d (θ n)‖ ^ (2 : ℕ) := by
      rw [hDist_eq, pow_two, pow_two]
      ring
    have hDir_scaled :
        α (θ n) ^ (2 : ℕ) * ‖d (θ n)‖ ^ (2 : ℕ) ≤
          α (θ n) ^ (2 : ℕ) * (c2 ^ (2 : ℕ) * ‖g (θ n)‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hDir_sq (by positivity)
    have hAlpha_scaled :
        α (θ n) ^ (2 : ℕ) * (c2 ^ (2 : ℕ) * ‖g (θ n)‖ ^ (2 : ℕ)) ≤
          (τ * α (θ n)) * (c2 ^ (2 : ℕ) * ‖g (θ n)‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right hAlpha_sq (by positivity)
    have hDescent_scaled :
        (τ * α (θ n) * c2 ^ (2 : ℕ)) * (c1 * ‖g (θ n)‖ ^ (2 : ℕ)) ≤
          (τ * α (θ n) * c2 ^ (2 : ℕ)) * (- inner ℝ (g (θ n)) (d (θ n))) := by
      have hCoeff_nonneg : 0 ≤ τ * α (θ n) * c2 ^ (2 : ℕ) := by
        exact mul_nonneg
          (mul_nonneg (le_of_lt h_lineSearch.tau_pos) hAlpha_nonneg)
          (by positivity)
      exact mul_le_mul_of_nonneg_left hDescent_sq hCoeff_nonneg
    calc
      c1 * dist (x (θ n + 1)) (x (θ n)) ^ (2 : ℕ) =
          c1 * (α (θ n) ^ (2 : ℕ) * ‖d (θ n)‖ ^ (2 : ℕ)) := by
        rw [hDist_sq]
      _ ≤ c1 * (α (θ n) ^ (2 : ℕ) * (c2 ^ (2 : ℕ) * ‖g (θ n)‖ ^ (2 : ℕ))) := by
        exact mul_le_mul_of_nonneg_left hDir_scaled (le_of_lt hc1)
      _ ≤ c1 * ((τ * α (θ n)) * (c2 ^ (2 : ℕ) * ‖g (θ n)‖ ^ (2 : ℕ))) := by
        exact mul_le_mul_of_nonneg_left hAlpha_scaled (le_of_lt hc1)
      _ = (τ * α (θ n) * c2 ^ (2 : ℕ)) * (c1 * ‖g (θ n)‖ ^ (2 : ℕ)) := by ring
      _ ≤ (τ * α (θ n) * c2 ^ (2 : ℕ)) * (- inner ℝ (g (θ n)) (d (θ n))) :=
        hDescent_scaled
      _ = (τ * c2 ^ (2 : ℕ)) * (α (θ n) * (- inner ℝ (g (θ n)) (d (θ n)))) := by ring
  exact hStep_sq_bound

/-- Helper for Chapter02 Theorem 2.5.9: if one recorded gradient is already zero, then the
direction bound and the update rule force the whole tail to stay fixed, so every accumulation
point equals that stationary iterate. -/
lemma nonmonotoneArmijo_stationary_of_zero_iterate_gradient
    (h_mem : ∀ k, x k ∈ initialSublevelSet f (x 0))
    (h_iterateGradient :
      ∀ k,
        x k ∈ initialSublevelSet f (x 0) →
          HasGradientVectorAt f (g k) (x k))
    (h_dir_bound :
      ∀ k,
        x k ∈ initialSublevelSet f (x 0) →
          ‖d k‖ ≤ c2 * ‖g k‖)
    (h_lineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp)
    {xBar : E} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (h_tendsto : Tendsto (x ∘ φ) atTop (nhds xBar))
    {k0 : ℕ}
    (hk0 : g k0 = 0) :
    IsStationaryPoint f xBar := by
  have hk0_mem : x k0 ∈ initialSublevelSet f (x 0) := h_mem k0
  have hGrad_zero_k0 : HasGradientVectorAt f (0 : E) (x k0) := by
    -- Rewriting the recorded zero gradient turns the iterate-gradient witness into the
    -- zero derivative required for stationarity at `x k0`.
    simpa [hk0] using h_iterateGradient k0 hk0_mem
  have hStationary_k0 : IsStationaryPoint f (x k0) := by
    simpa [HasGradientVectorAt, IsStationaryPoint] using hGrad_zero_k0
  have h_tail :
      ∀ t : ℕ, k0 ≤ t → x t = x k0 := by
    intro t htk0
    rcases Nat.exists_eq_add_of_le htk0 with ⟨j, rfl⟩
    induction j with
    | zero =>
        rfl
    | succ j ih =>
        have hmem_j : x (k0 + j) ∈ initialSublevelSet f (x 0) := by
          simpa [ih (Nat.le_add_right k0 j)] using hk0_mem
        have hGrad_j : HasGradientVectorAt f (g (k0 + j)) (x k0) := by
          simpa [ih (Nat.le_add_right k0 j)] using h_iterateGradient (k0 + j) hmem_j
        have hg_zero : g (k0 + j) = 0 := by
          have hDerivEq :
              InnerProductSpace.toDualMap ℝ E (g (k0 + j)) =
                InnerProductSpace.toDualMap ℝ E (0 : E) := by
            exact hGrad_j.hasFDerivAt.unique hGrad_zero_k0.hasFDerivAt
          exact (InnerProductSpace.toDualMap ℝ E).injective hDerivEq
        have hDir_zero : d (k0 + j) = 0 := by
          have hDir_norm : ‖d (k0 + j)‖ ≤ 0 := by
            simpa [hg_zero] using h_dir_bound (k0 + j) hmem_j
          exact norm_eq_zero.mp <| le_antisymm hDir_norm (norm_nonneg _)
        -- Once the search direction vanishes, the line-search update leaves the iterate fixed.
        calc
          x (k0 + (j + 1)) = x (k0 + j + 1) := by simp [Nat.add_assoc]
          _ = x (k0 + j) + α (k0 + j) • d (k0 + j) := h_lineSearch.update (k0 + j)
          _ = x (k0 + j) := by simp [hDir_zero]
          _ = x k0 := ih (Nat.le_add_right k0 j)
  have h_subseq_const :
      Tendsto (x ∘ φ) atTop (nhds (x k0)) := by
    have h_eventually_eq :
        (fun _ : ℕ ↦ x k0) =ᶠ[atTop] x ∘ φ := by
      filter_upwards [Filter.eventually_ge_atTop k0] with i hi
      symm
      exact h_tail (φ i) (le_trans hi (hφ.id_le i))
    exact Tendsto.congr' h_eventually_eq tendsto_const_nhds
  have hxBar_eq : xBar = x k0 :=
    tendsto_nhds_unique h_tendsto h_subseq_const
  simpa [hxBar_eq] using hStationary_k0

/-- Chapter02 Theorem 2.5.9 (2): under the hypotheses of `(1)`, every subsequential
limit `xBar` of the iterate sequence `x` is a stationary point of `f` in the chapter's
canonical derivative-zero sense `IsStationaryPoint f xBar`. Besides the pointwise
gradient-vector witnesses on `initialSublevelSet f (x 0)`, the source-faithful convergence
argument uses a uniformly continuous gradient field `grad` on this compact initial sublevel
set, while the nonmonotone Armijo run is recorded using the explicit iterate-gradient data `g`. -/
theorem nonmonotoneArmijoLineSearch_accumulationPoint_stationary
    (grad : E → E)
    (h_compact : IsCompact (initialSublevelSet f (x 0)))
    (h_hasGradient :
      ∀ y ∈ initialSublevelSet f (x 0), HasGradientVectorAt f (grad y) y)
    (h_iterateGradient :
      ∀ k,
        x k ∈ initialSublevelSet f (x 0) →
          HasGradientVectorAt f (g k) (x k))
    (hc1 : 0 < c1) (hc2 : 0 < c2)
    (h_descent :
      ∀ k,
        x k ∈ initialSublevelSet f (x 0) →
          inner ℝ (g k) (d k) ≤ -c1 * ‖g k‖ ^ (2 : ℕ))
    (h_dir_bound :
      ∀ k,
        x k ∈ initialSublevelSet f (x 0) →
          ‖d k‖ ≤ c2 * ‖g k‖)
    (h_lineSearch : IsNonmonotoneArmijoLineSearch f x g d α τ σ γ M m exp)
    {xBar : E} {φ : ℕ → ℕ}
    (h_gradUniform : UniformContinuousOn grad (initialSublevelSet f (x 0)))
    (hφ : StrictMono φ)
    (h_tendsto : Tendsto (x ∘ φ) atTop (nhds xBar)) :
    IsStationaryPoint f xBar := by
  have h_mem :
      ∀ k, x k ∈ initialSublevelSet f (x 0) := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih
    cases k with
    | zero =>
        -- The initial iterate lies in the initial sublevel set by definition.
        simp [initialSublevelSet]
    | succ k =>
        have hk_mem : x k ∈ initialSublevelSet f (x 0) :=
          ih k (Nat.lt_succ_self k)
        have hAccepts : nonmonotoneArmijoAcceptsAtExponent f x g d τ σ γ m k (exp k) :=
          h_lineSearch.acceptsAtExponent k
        rw [nonmonotoneArmijoAcceptsAtExponent_iff] at hAccepts
        have hReference_le :
            nonmonotoneArmijoReferenceValue f x k (m k) ≤ f (x 0) := by
          -- Every entry in the bounded window is an earlier iterate already controlled by
          -- the strong-induction hypothesis.
          rw [nonmonotoneArmijoReferenceValue_eq]
          refine Finset.sup'_le _ _ ?_
          intro j hj
          exact ih (k - j) <| lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self k)
        have hInner_nonpos : inner ℝ (g k) (d k) ≤ 0 := by
          have hNeg_nonpos : -c1 * ‖g k‖ ^ (2 : ℕ) ≤ 0 := by
            nlinarith [hc1, sq_nonneg ‖g k‖]
          exact le_trans (h_descent k hk_mem) hNeg_nonpos
        have hStep_nonneg : 0 ≤ nonmonotoneArmijoStep τ σ (exp k) := by
          have hSigma_pos : 0 < σ := h_lineSearch.sigma_mem_Ioo.1
          exact le_of_lt <| mul_pos (pow_pos hSigma_pos _) h_lineSearch.tau_pos
        have hCorrection_nonpos :
            γ * nonmonotoneArmijoStep τ σ (exp k) * inner ℝ (g k) (d k) ≤ 0 := by
          have hGamma_nonneg : 0 ≤ γ := le_of_lt h_lineSearch.gamma_mem_Ioo.1
          exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg hGamma_nonneg hStep_nonneg) hInner_nonpos
        -- The accepted Armijo step remains below the initial objective level.
        calc
          f (x (k + 1)) = f (x k + nonmonotoneArmijoStep τ σ (exp k) • d k) := by
            rw [h_lineSearch.update k, h_lineSearch.alpha_eq k]
          _ ≤
              nonmonotoneArmijoReferenceValue f x k (m k) +
                γ * nonmonotoneArmijoStep τ σ (exp k) * inner ℝ (g k) (d k) :=
            hAccepts
          _ ≤ f (x 0) := by
            linarith [hReference_le, hCorrection_nonpos]
  have hxBar_mem : xBar ∈ initialSublevelSet f (x 0) := by
    -- The compact initial sublevel set is closed, so the subsequential limit stays inside it.
    exact h_compact.isClosed.mem_of_tendsto h_tendsto <|
      Eventually.of_forall fun n ↦ h_mem (φ n)
  by_cases h_zero : ∃ k, g k = 0
  · rcases h_zero with ⟨k0, hk0⟩
    exact nonmonotoneArmijo_stationary_of_zero_iterate_gradient
      (f := f) (x := x) (g := g) (d := d) (α := α) (τ := τ) (σ := σ) (γ := γ)
      (c2 := c2) (M := M) (m := m) (exp := exp)
      h_mem h_iterateGradient h_dir_bound h_lineSearch hφ h_tendsto hk0
  · have h_nonzero : ∀ k, g k ≠ 0 := by
      simpa [not_exists] using h_zero
    have h_reference_step :
        ∀ k,
          nonmonotoneArmijoReferenceValue f x (k + 1) (m (k + 1)) ≤
            nonmonotoneArmijoReferenceValue f x k (m k) := by
      intro k
      have hk_mem : x k ∈ initialSublevelSet f (x 0) := h_mem k
      have hAccepts : nonmonotoneArmijoAcceptsAtExponent f x g d τ σ γ m k (exp k) :=
        h_lineSearch.acceptsAtExponent k
      rw [nonmonotoneArmijoAcceptsAtExponent_iff] at hAccepts
      have hInner_nonpos : inner ℝ (g k) (d k) ≤ 0 := by
        have hNeg_nonpos : -c1 * ‖g k‖ ^ (2 : ℕ) ≤ 0 := by
          nlinarith [hc1, sq_nonneg ‖g k‖]
        exact le_trans (h_descent k hk_mem) hNeg_nonpos
      have hStep_nonneg : 0 ≤ nonmonotoneArmijoStep τ σ (exp k) := by
        have hSigma_pos : 0 < σ := h_lineSearch.sigma_mem_Ioo.1
        exact le_of_lt <| mul_pos (pow_pos hSigma_pos _) h_lineSearch.tau_pos
      have hCorrection_nonpos :
          γ * nonmonotoneArmijoStep τ σ (exp k) * inner ℝ (g k) (d k) ≤ 0 := by
        have hGamma_nonneg : 0 ≤ γ := le_of_lt h_lineSearch.gamma_mem_Ioo.1
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg hGamma_nonneg hStep_nonneg) hInner_nonpos
      rw [nonmonotoneArmijoReferenceValue_eq]
      refine Finset.sup'_le _ _ ?_
      intro j hj
      rcases mem_nonmonotoneArmijoWindow.mp hj with ⟨hjk, hjm⟩
      cases j with
      | zero =>
          -- The newest iterate is controlled by the accepted sufficient-decrease inequality.
          calc
            f (x (k + 1)) = f (x k + nonmonotoneArmijoStep τ σ (exp k) • d k) := by
              rw [h_lineSearch.update k, h_lineSearch.alpha_eq k]
            _ ≤
                nonmonotoneArmijoReferenceValue f x k (m k) +
                  γ * nonmonotoneArmijoStep τ σ (exp k) * inner ℝ (g k) (d k) :=
              hAccepts
            _ ≤ nonmonotoneArmijoReferenceValue f x k (m k) := by
              linarith
      | succ j =>
          -- Older values in the new window already appear in the previous window.
          have hjk' : j ≤ k := Nat.succ_le_succ_iff.mp hjk
          have hjm' : j ≤ m k := by
            have hm_step : m (k + 1) ≤ m k + 1 := by
              exact le_trans (h_lineSearch.m_step k) (Nat.min_le_left _ _)
            exact Nat.succ_le_succ_iff.mp (le_trans hjm hm_step)
          have hj_mem : j ∈ nonmonotoneArmijoWindow k (m k) :=
            (mem_nonmonotoneArmijoWindow).2 ⟨hjk', hjm'⟩
          have hOld_le :
              f (x (k - j)) ≤ nonmonotoneArmijoReferenceValue f x k (m k) := by
            rw [nonmonotoneArmijoReferenceValue_eq]
            exact
              Finset.le_sup'
                (s := nonmonotoneArmijoWindow k (m k))
                (f := fun i ↦ f (x (k - i))) hj_mem
          simpa [Nat.succ_sub_succ_eq_sub] using hOld_le
    have h_reference_argmax :
        ∀ k,
          ∃ ell,
            k - m k ≤ ell ∧
              ell ≤ k ∧
                nonmonotoneArmijoReferenceValue f x k (m k) = f (x ell) := by
      intro k
      exact nonmonotoneArmijo_reference_argmax
        (f := f) (x := x) (m := m) k
    have h_reference_tendsto :
        ∃ cInf : ℝ,
          Tendsto (fun k ↦ nonmonotoneArmijoReferenceValue f x k (m k)) atTop (nhds cInf) := by
      exact nonmonotoneArmijo_reference_value_converges
        (f := f) (x := x) (m := m)
        h_compact
        (fun y hy ↦ ⟨grad y, h_hasGradient y hy⟩)
        h_mem h_reference_step
    have h_smallCorrection :
        ∃ ψ : ℕ → ℕ,
          (∀ k, k ≤ ψ k ∧ ψ k ≤ k + M) ∧
            Tendsto
              (fun k ↦ α (ψ k) * (- inner ℝ (g (ψ k)) (d (ψ k))))
              atTop (nhds 0) := by
      exact nonmonotoneArmijo_small_correction_selector_tendsto_zero
        (f := f) (x := x) (g := g) (d := d) (α := α) (τ := τ) (σ := σ) (γ := γ)
        (c1 := c1) (M := M) (m := m) (exp := exp)
        h_mem hc1 h_descent h_reference_step h_reference_tendsto h_lineSearch
    obtain ⟨ψ, hψ_bounds, hψ_small⟩ := h_smallCorrection
    have h_selectorAlongCluster :
        ∃ θ : ℕ → ℕ,
          (∀ n, φ n ≤ θ n ∧ θ n ≤ φ n + M) ∧
            Tendsto
              (fun n ↦ α (θ n) * (- inner ℝ (g (θ n)) (d (θ n))))
              atTop (nhds 0) := by
      exact nonmonotoneArmijo_selector_cluster_correction_tendsto_zero
        (α := α) (g := g) (d := d) (M := M) hψ_bounds hψ_small hφ
    obtain ⟨θ, hθ_bounds, hθ_small⟩ := h_selectorAlongCluster
    have h_iterateGradient_eq :
        ∀ k, g k = grad (x k) := by
      intro k
      have hk_mem : x k ∈ initialSublevelSet f (x 0) := h_mem k
      have hRecorded := h_iterateGradient k hk_mem
      have hAmbient := h_hasGradient (x k) hk_mem
      have hDualEq :
          InnerProductSpace.toDualMap ℝ E (g k) =
            InnerProductSpace.toDualMap ℝ E (grad (x k)) := by
        exact hRecorded.hasFDerivAt.unique hAmbient.hasFDerivAt
      exact (InnerProductSpace.toDualMap ℝ E).injective hDualEq
    have hθ_gap :
        Tendsto (fun n ↦ dist (x (θ n + 1)) (x (θ n))) atTop (nhds 0) := by
      -- Step 1 of the source-faithful replan is now discharged on the selected branch `θ`.
      exact nonmonotoneArmijo_theta_step_gap_tendsto_zero
        (f := f) (x := x) (g := g) (d := d) (α := α) (τ := τ) (σ := σ) (γ := γ)
        (c1 := c1) (c2 := c2) (M := M) (m := m) (exp := exp)
        h_mem hc1 hc2 h_descent h_dir_bound h_lineSearch hθ_small
    -- Route correction: the earlier block-sum drop route is too strong. What is now verified is
    -- that the reference values converge and each bounded memory block contains a selected index
    -- with vanishing Armijo correction, this correction has been transported onto the composed
    -- selector branch `θ n`, and the corresponding selector step gaps now satisfy `x (θ n + 1) -
    -- x (θ n) → 0`.
    -- TODO: the remaining source-faithful blocker is to justify that the bounded-lag selector
    -- branch `x ∘ θ` stays in the same nonstationary neighborhood of `xBar`, so that one fixed
    -- accepted exponent and a uniform lower gradient bound can contradict `hθ_small`.
    sorry

end
