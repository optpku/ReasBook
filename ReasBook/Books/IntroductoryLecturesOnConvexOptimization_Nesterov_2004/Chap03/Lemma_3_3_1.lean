/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

noncomputable section

universe u

/- Lemma 3.3.1 lies in the chapter's level-method scalar-history domain.

Best owner abstraction:
* the primitive scalar history `(\hat f_k^*, f_k^*)` is `LevelMethodHistory`

Primitive data:
* `approximateOptimalValue`
* `optimalValue`

Derived API:
* `gap`
* `levelValue`
* `valueInterval`
* `shouldStop`

This file keeps only the two scalar sequences as primitive data. The gap, the level value, and
the stopping test `δ_k ≤ ε` are all derived from that owner history rather than repeated later as
parallel sequence-level wrappers.
-/

/-- The scalar data from a level-method model needed for the monotonicity and gap estimates:
the approximate optimal values `\hat f_k^*` and the record values `f_k^*`. -/
structure LevelMethodHistory where
  /-- The approximate optimal values `\hat f_k^*`. -/
  approximateOptimalValue : ℕ → ℝ
  /-- The record values `f_k^* = min_{0 ≤ i ≤ k} f(x_i)`. -/
  optimalValue : ℕ → ℝ

namespace LevelMethodNotation

scoped notation:max "fhat(" history:arg ", " k:arg ")" =>
  LevelMethodHistory.approximateOptimalValue history k

scoped notation:max "fstar(" history:arg ", " k:arg ")" =>
  LevelMethodHistory.optimalValue history k

end LevelMethodNotation

namespace LevelMethodHistory

/-- The model gap `δ_k = f_k^* - \hat f_k^*` at iteration `k`. -/
def gap (history : LevelMethodHistory) (k : ℕ) : ℝ :=
  history.optimalValue k - history.approximateOptimalValue k

/-- The model gap is the difference between the exact and approximate optimal values. -/
-- Proof sketch: unfold `LevelMethodHistory.gap`.
theorem gap_eq_sub (history : LevelMethodHistory) (k : ℕ) :
    history.gap k = history.optimalValue k - history.approximateOptimalValue k :=
  rfl

/-- The level value `ℓ_k(α) = (1 - α) \hat f_k^* + α f_k^*`. -/
def levelValue (history : LevelMethodHistory) (α : ℝ) (k : ℕ) : ℝ :=
  (1 - α) * history.approximateOptimalValue k + α * history.optimalValue k

/-- The level value can be rewritten as `f_k^* - (1 - α) δ_k`. -/
-- Proof sketch: unfold `LevelMethodHistory.levelValue` and `LevelMethodHistory.gap`, then
-- expand the products and collect terms.
theorem levelValue_eq_optimal_sub_one_sub_alpha_mul_gap
    (history : LevelMethodHistory) (α : ℝ) (k : ℕ) :
    history.levelValue α k = history.optimalValue k - (1 - α) * history.gap k := by
  rw [levelValue, gap_eq_sub]
  ring

/-- The interval `Δ_k = [\hat f_k^*, f_k^*]` attached to a level-method history. -/
def valueInterval (history : LevelMethodHistory) (k : ℕ) : Set ℝ :=
  Set.Icc (history.approximateOptimalValue k) (history.optimalValue k)

/-- Membership in `history.valueInterval k` is the pair of inequalities
`\hat f_k^* ≤ t ≤ f_k^*`. -/
theorem mem_valueInterval_iff
    (history : LevelMethodHistory) (k : ℕ) (t : ℝ) :
    t ∈ history.valueInterval k ↔
      history.approximateOptimalValue k ≤ t ∧ t ≤ history.optimalValue k :=
  Iff.rfl

end LevelMethodHistory

namespace LevelMethodNotation

scoped notation:max "δ[" history:arg "](" k:arg ")" =>
  LevelMethodHistory.gap history k

scoped notation:max "ℓ[" history:arg "](" α:arg ", " k:arg ")" =>
  LevelMethodHistory.levelValue history α k

scoped notation:max "Δ[" history:arg "](" k:arg ")" =>
  LevelMethodHistory.valueInterval history k

end LevelMethodNotation

open scoped LevelMethodNotation

namespace LevelMethodHistory

/-- The textbook stopping test `δ_k ≤ ε` for a scalar level-method history. -/
def shouldStop (history : LevelMethodHistory) (ε : ℝ) (k : ℕ) : Prop :=
  history.gap k ≤ ε

/-- The stopping test is exactly the inequality `δ_k ≤ ε`. -/
-- Proof sketch: unfold `LevelMethodHistory.shouldStop`.
theorem shouldStop_iff (history : LevelMethodHistory) (ε : ℝ) (k : ℕ) :
    history.shouldStop ε k ↔ history.gap k ≤ ε :=
  Iff.rfl

/-- If `\hat f_k^*` is a lower bound for the optimum value `f^*`, then the stopping test
`δ_k ≤ ε` implies `f_k^* - f^* ≤ ε`. -/
-- Proof sketch: combine the single-index lower-bound estimate
-- `history.approximateOptimalValue k ≤ fStar` with the identity
-- `δ_k = history.optimalValue k - history.approximateOptimalValue k`, then use the stopping
-- inequality `δ_k ≤ ε`.
theorem optimalValue_sub_fStar_le_epsilon_of_shouldStop
    (history : LevelMethodHistory) {fStar ε : ℝ} (k : ℕ)
    (hvalidLower : history.approximateOptimalValue k ≤ fStar)
    (hstop : history.shouldStop ε k) :
    history.optimalValue k - fStar ≤ ε := by
  rw [shouldStop_iff, gap_eq_sub] at hstop
  linarith

/-- Bridge/view: if on the interval `[k, p]` the record values are bounded below by the terminal
record value, the gaps are bounded above by the initial gap, and `δ_p ≥ (1 - α) δ_k`, then every
intermediate level value `ℓ_i(α)` is at least `\hat f_p^*`. -/
theorem levelValue_ge_approximateOptimalValue_of_intervalMonotonicity
    (history : LevelMethodHistory) {α : ℝ} {k p : ℕ}
    (hα : α ≤ 1)
    (hoptimal_mono :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → fstar(history, p) ≤ fstar(history, i))
    (hgap_mono :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → δ[history](i) ≤ δ[history](k))
    (hgap_large : δ[history](p) ≥ (1 - α) * δ[history](k)) :
    ∀ {i : ℕ}, k ≤ i → i ≤ p → ℓ[history](α, i) ≥ fhat(history, p) := by
  intro i hki hip
  have hOneSubAlpha_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα
  have hoptimal : history.optimalValue p ≤ history.optimalValue i := hoptimal_mono hki hip
  have hgap_i : history.gap i ≤ history.gap k := hgap_mono hki hip
  have hscaled_gap_i : (1 - α) * history.gap i ≤ (1 - α) * history.gap k :=
    mul_le_mul_of_nonneg_left hgap_i hOneSubAlpha_nonneg
  have hscaled_gap_p : (1 - α) * history.gap i ≤ history.gap p :=
    hscaled_gap_i.trans hgap_large
  rw [history.levelValue_eq_optimal_sub_one_sub_alpha_mul_gap α i]
  linarith [history.gap_eq_sub p]

/-- Lemma 3.3.1: if the record values satisfy `f_{j+1}^* ≤ f_j^*`, the model gaps satisfy
`δ_{j+1} ≤ δ_j`, and the gap still obeys `δ_p ≥ (1 - α) δ_k`, then every
intermediate level value `ℓ_i(α)` with `k ≤ i ≤ p` is at least `\hat f_p^*`. -/
-- Proof sketch: since `α ≤ 1`, the factor `1 - α` is nonnegative. Use the stepwise monotonicity
-- of the gaps to show `δ_i ≤ δ_k` for `k ≤ i ≤ p`, hence
-- `(1 - α) * δ_i ≤ (1 - α) * δ_k ≤ δ_p`. Rewrite `ℓ_i(α)` as
-- `f_i^* - (1 - α) * δ_i`, compare `f_i^*` with `f_p^*` using the monotonicity of the record
-- values, and finish by expanding `δ_p = f_p^* - \hat f_p^*`.
theorem levelValue_ge_approximateOptimalValue_of_gap_large_enough
    (history : LevelMethodHistory) {α : ℝ} {k p : ℕ}
    (hα : α ≤ 1)
    (hoptimal_succ : ∀ j : ℕ, history.optimalValue (j + 1) ≤ history.optimalValue j)
    (hgap_succ : ∀ j : ℕ, history.gap (j + 1) ≤ history.gap j)
    (hgap_large : δ[history](p) ≥ (1 - α) * δ[history](k)) :
    ∀ {i : ℕ}, k ≤ i → i ≤ p → ℓ[history](α, i) ≥ fhat(history, p) := by
  have hoptimal_antitone : Antitone history.optimalValue :=
    antitone_nat_of_succ_le hoptimal_succ
  have hgap_antitone : Antitone history.gap :=
    antitone_nat_of_succ_le hgap_succ
  intro i hki hip
  exact
    history.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity hα
    (fun {_i} _hki hip' ↦ hoptimal_antitone hip')
    (fun {_i} hki' _hip ↦ hgap_antitone hki')
    hgap_large
    hki
    hip

end LevelMethodHistory
