/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped SelfConcordantAuxiliaryFunction

/- Lemma 5.1.4 belongs to the one-variable self-concordant auxiliary-function / Fenchel-conjugacy
domain.

Relevant owner-style declarations sampled before refinement:
* `selfConcordantOmega`, `selfConcordantOmegaStar`, `selfConcordantOmegaDeriv`, and
  `selfConcordantOmegaPrimeStar` in `Definition_5_0_21`, the chapter owners for `ω`, `ω_*`,
  `ω'`, and `ω'_*`;
* `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg` in `Definition_5_0_21`, the
  canonical Chapter 5 constructors for the natural `ω` and `ω_*` subtype arguments;
* `fenchelDual` in `Definition_5_0_27`, the project-level canonical owner for Fenchel conjugacy in
  higher dimension;
* `IsMaxOn` in mathlib, the canonical owner-level maximizer predicate behind the scalar Fenchel
  support formulas.

Best owner abstraction:
* source-facing: the fixed chapter owners `ω`, `ω_*`, together with their explicit derivative and
  inverse branches `ω'`, `ω'_*`, and the textbook maximization identities built from them;
* core/canonical: the already-defined chapter auxiliary functions from `Definition_5_0_21`;
* bridge/view: the explicit scalar formulas specialized to those owners.

Primitive data:
* `ω`;
* `ω_*`.

Derived API:
* `ω'` and `ω'_*`;
* the canonical subtype constructors `selfConcordantOmegaArg` and
  `selfConcordantOmegaStarArg`;
* the domain-membership lemmas for `ω'` and `ω'_*`;
* the seven source-facing Fenchel-conjugacy identities of Lemma 5.1.4, stated directly against
  the canonical owners on their mathematically forced domains: the full owner domains for the
  inverse identities `(1)`, `(2)`, `(6)`, `(7)`, and the constrained nonnegative maximization
  regimes for `(3)`, `(4)`, `(5)`, without a parallel local point/maximand wrapper API; the
  maximizer data for parts `(3)` and `(4)` is carried by the numbered statements themselves. -/

theorem neg_one_lt_selfConcordantUnit_of_nonneg {t : ℝ} (ht : 0 ≤ t) : -1 < t := by
  have h : -1 < ((1 : NNReal) : ℝ) * t := neg_one_lt_mf_mul_of_nonneg ht
  simpa using h

/-- For `t ≥ 0`, the derivative branch `ω'(t)` is nonnegative. -/
theorem selfConcordantOmegaDeriv_nonneg {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    0 ≤ ω' tω := by
  have hneg : -1 < t := neg_one_lt_selfConcordantUnit_of_nonneg ht
  have hneg1 : -1 < ((1 : NNReal) : ℝ) * t := by
    simpa using hneg
  let tω : Ioi (-1 : ℝ) := selfConcordantOmegaArg 1 t hneg1
  have hden : 0 < 1 + t := by
    linarith
  -- Expand `ω'` to its rational formula and use positivity of the denominator.
  have hmain : 0 ≤ ω' tω := by
    rw [selfConcordantOmegaDeriv_apply]
    simp [tω]
    exact div_nonneg ht hden.le
  simpa [tω] using hmain

/-- On its natural domain `(-1, ∞)`, the derivative branch `ω'(t)` lies below `1`. -/
theorem selfConcordantOmegaDeriv_lt_one (tω : Ioi (-1 : ℝ)) :
    ω' tω < 1 := by
  have hden : 0 < 1 + (tω : ℝ) := by
    nlinarith [show (-1 : ℝ) < (tω : ℝ) from tω.property]
  -- Clear the positive denominator and reduce to the obvious inequality `t < 1 + t`.
  rw [selfConcordantOmegaDeriv_apply, div_lt_iff₀ hden]
  nlinarith

/-- For `t ≥ 0`, the derivative branch `ω'(t)` belongs to the slope interval `[0, 1)`. -/
theorem selfConcordantOmegaDeriv_mem_Ico {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    ω' tω ∈ Ico (0 : ℝ) 1 := by
  have hneg : -1 < t := neg_one_lt_selfConcordantUnit_of_nonneg ht
  have hneg1 : -1 < ((1 : NNReal) : ℝ) * t := by
    simpa using hneg
  let tω : Ioi (-1 : ℝ) := selfConcordantOmegaArg 1 t hneg1
  -- Package the lower and upper bounds into the interval membership statement.
  have hmain : ω' tω ∈ Ico (0 : ℝ) 1 := by
    refine ⟨selfConcordantOmegaDeriv_nonneg ht, selfConcordantOmegaDeriv_lt_one tω⟩
  simpa [tω] using hmain

/-- For `τ ∈ [0, 1)`, the inverse branch `ω'_*(τ)` is nonnegative. -/
theorem selfConcordantOmegaPrimeStar_nonneg {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    0 ≤ ω'_* ⟨τ, hτ1⟩ := by
  have hden : 0 < 1 - τ := by
    linarith
  -- Expand `ω'_*` to its rational formula and use positivity of the denominator.
  rw [selfConcordantOmegaPrimeStar_apply]
  exact div_nonneg hτ0 hden.le

/-- On its natural domain `(-∞, 1)`, the inverse branch `ω'_*(τ)` lies above `-1`. -/
theorem selfConcordantOmegaPrimeStar_gt_neg_one (τω : Iio (1 : ℝ)) :
    -1 < ω'_* τω := by
  have hden : 0 < 1 - (τω : ℝ) := by
    nlinarith [show ((τω : ℝ) : ℝ) < 1 from τω.property]
  -- Clear the positive denominator and reduce to a linear inequality.
  rw [selfConcordantOmegaPrimeStar_apply, lt_div_iff₀ hden]
  nlinarith

-- Proof sketch: substitute the explicit formulas
-- `ω'(t) = t / (1 + t)` and `ω'_*(τ) = τ / (1 - τ)` and simplify.
/-- Lemma 5.1.4 (1): for `τ < 1`, applying `ω'` to `ω'_*(τ)` returns `τ`. -/
theorem selfConcordantOmegaDeriv_selfConcordantOmegaPrimeStar
    {τ : ℝ} (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    let tω := selfConcordantOmegaArg 1 (ω'_* τω) (by
      simpa using selfConcordantOmegaPrimeStar_gt_neg_one τω)
    ω' tω = τ := by
  have hτ1' : ((1 : NNReal) : ℝ) * τ < 1 := by
    simpa using hτ1
  let τω : Iio (1 : ℝ) := selfConcordantOmegaStarArg 1 τ hτ1'
  have hprime : -1 < ω'_* τω := selfConcordantOmegaPrimeStar_gt_neg_one τω
  have hprime1 : -1 < ((1 : NNReal) : ℝ) * ω'_* τω := by
    simpa using hprime
  let tω : Ioi (-1 : ℝ) := selfConcordantOmegaArg 1 (ω'_* τω) hprime1
  have hne : 1 - τ ≠ 0 := by
    linarith
  -- Substitute the explicit formulas for `ω'` and `ω'_*` and simplify the rational identity.
  have hmain : ω' tω = τ := by
    simp [tω, τω]
    field_simp [hne]
    ring
  simpa [tω, τω] using hmain

-- Proof sketch: substitute the explicit formulas
-- `ω'(t) = t / (1 + t)` and `ω'_*(τ) = τ / (1 - τ)` and simplify.
/-- Lemma 5.1.4 (2): for `t > -1`, applying `ω'_*` to `ω'(t)` returns `t`. -/
theorem selfConcordantOmegaPrimeStar_selfConcordantOmegaDeriv
    {t : ℝ} (ht : -1 < t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using ht)
    let τω := selfConcordantOmegaStarArg 1 (ω' tω) (by
      simpa using selfConcordantOmegaDeriv_lt_one tω)
    ω'_* τω = t := by
  have ht1' : -1 < ((1 : NNReal) : ℝ) * t := by
    simpa using ht
  let tω : Ioi (-1 : ℝ) := selfConcordantOmegaArg 1 t ht1'
  have hτω1 : ω' tω < 1 := selfConcordantOmegaDeriv_lt_one tω
  have hτω1' : ((1 : NNReal) : ℝ) * ω' tω < 1 := by
    simpa using hτω1
  let τω : Iio (1 : ℝ) := selfConcordantOmegaStarArg 1 (ω' tω) hτω1'
  have hne : 1 + t ≠ 0 := by
    linarith
  -- Substitute the explicit formulas for `ω'` and `ω'_*` and simplify the rational identity.
  have hmain : ω'_* τω = t := by
    simp [tω, τω]
    field_simp [hne]
    ring
  simpa [tω, τω] using hmain

-- Proof sketch: evaluate the support functional `ξ ↦ ξ * t - ω_*(ξ)` at its canonical maximizer
-- `ξ = ω'(t)`.
/-- Lemma 5.1.4 (3): for `t ≥ 0`, the value `ω(t)` is the maximal value of the Fenchel support
functional `ξ ↦ ξ t - ω_*(ξ)` on `[0, 1)`, realized at `ξ = ω'(t)`. -/
theorem selfConcordantOmega_eq_mul_selfConcordantOmegaDeriv_sub_selfConcordantOmegaStar_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    let ξω := selfConcordantOmegaStarArg 1 (ω' tω) (by
      simpa using selfConcordantOmegaDeriv_lt_one tω)
    ξω ∈ {ξ : Iio (1 : ℝ) | 0 ≤ (ξ : ℝ)} ∧
      IsMaxOn
        (fun ξ : Iio (1 : ℝ) ↦ (ξ : ℝ) * t - ω_* ξ)
        {ξ : Iio (1 : ℝ) | 0 ≤ (ξ : ℝ)} ξω ∧
      ω tω = t * ω' tω - ω_* ξω := by
  have hneg : -1 < t := neg_one_lt_selfConcordantUnit_of_nonneg ht
  have hneg1 : -1 < ((1 : NNReal) : ℝ) * t := by
    simpa using hneg
  let tω : Ioi (-1 : ℝ) := selfConcordantOmegaArg 1 t hneg1
  have hξω1 : ω' tω < 1 := selfConcordantOmegaDeriv_lt_one tω
  have hξω1' : ((1 : NNReal) : ℝ) * ω' tω < 1 := by
    simpa using hξω1
  let ξω : Iio (1 : ℝ) := selfConcordantOmegaStarArg 1 (ω' tω) hξω1'
  have hξω0 : 0 ≤ (ξω : ℝ) := by
    -- The canonical slope point lies in the admissible interval `[0, 1)`.
    have hω' : 0 ≤ ω' tω := by
      simpa [tω] using selfConcordantOmegaDeriv_nonneg ht
    simpa [ξω] using hω'
  have hne : 1 + t ≠ 0 := by
    linarith
  have hfrac : 1 - t / (1 + t) = 1 / (1 + t) := by
    field_simp [hne]
    ring
  -- Evaluate the support functional exactly at the canonical maximizer `ξ = ω'(t)`.
  have hvalue : ω tω = t * ω' tω - ω_* ξω := by
    rw [selfConcordantOmega_apply, selfConcordantOmegaDeriv_apply, selfConcordantOmegaStar_apply]
    simp [tω, ξω]
    rw [hfrac, one_div, Real.log_inv]
    field_simp [hne]
    ring
  -- Compare every admissible competitor to `ω(t)` using the log inequality route.
  have hmax :
      IsMaxOn
        (fun ξ : Iio (1 : ℝ) ↦ (ξ : ℝ) * t - ω_* ξ)
        {ξ : Iio (1 : ℝ) | 0 ≤ (ξ : ℝ)} ξω := by
    rw [isMaxOn_iff]
    intro ξ hξ
    have hξ0 : 0 ≤ (ξ : ℝ) := by
      simpa using hξ
    have hξ1 : 0 < 1 - (ξ : ℝ) := by
      nlinarith [show ((ξ : ℝ) : ℝ) < 1 from ξ.property]
    have ht1 : 0 < 1 + t := by
      linarith
    have hlog : Real.log ((1 + t) * (1 - (ξ : ℝ))) ≤ (1 + t) * (1 - (ξ : ℝ)) - 1 := by
      exact Real.log_le_sub_one_of_pos (mul_pos ht1 hξ1)
    rw [Real.log_mul ht1.ne' hξ1.ne'] at hlog
    have hineq : (ξ : ℝ) * t - ω_* ξ ≤ ω tω := by
      rw [selfConcordantOmega_apply, selfConcordantOmegaStar_apply]
      simp [tω] at hlog ⊢
      nlinarith
    have hvalue' : ω tω = (ξω : ℝ) * t - ω_* ξω := by
      simpa [ξω, mul_comm] using hvalue
    linarith
  have hmem : ξω ∈ {ξ : Iio (1 : ℝ) | 0 ≤ (ξ : ℝ)} := by
    simpa using hξω0
  have hresult :
      ξω ∈ {ξ : Iio (1 : ℝ) | 0 ≤ (ξ : ℝ)} ∧
        IsMaxOn
          (fun ξ : Iio (1 : ℝ) ↦ (ξ : ℝ) * t - ω_* ξ)
          {ξ : Iio (1 : ℝ) | 0 ≤ (ξ : ℝ)} ξω ∧
        ω tω = t * ω' tω - ω_* ξω := ⟨hmem, hmax, hvalue⟩
  simpa [tω, ξω] using hresult

-- Proof sketch: evaluate the support functional `ξ ↦ τ * ξ - ω(ξ)` at its canonical maximizer
-- `ξ = ω'_*(τ)`.
/-- Lemma 5.1.4 (4): for `τ ∈ [0, 1)`, the value `ω_*(τ)` is the maximal value of the Fenchel
support functional `ξ ↦ τ ξ - ω(ξ)` on `[0, ∞)`, realized at `ξ = ω'_*(τ)`. -/
theorem
    selfConcordantOmegaStar_eq_mul_selfConcordantOmegaPrimeStar_sub_selfConcordantOmega_of_mem_Ico
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    let tω := selfConcordantOmegaArg 1 (ω'_* τω) (by
      simpa using selfConcordantOmegaPrimeStar_gt_neg_one τω)
    tω ∈ {ξ : Ioi (-1 : ℝ) | 0 ≤ (ξ : ℝ)} ∧
      IsMaxOn
        (fun ξ : Ioi (-1 : ℝ) ↦ τ * (ξ : ℝ) - ω ξ)
        {ξ : Ioi (-1 : ℝ) | 0 ≤ (ξ : ℝ)} tω ∧
      ω_* τω = τ * ω'_* τω - ω tω := by
  have hτ1' : ((1 : NNReal) : ℝ) * τ < 1 := by
    simpa using hτ1
  let τω : Iio (1 : ℝ) := selfConcordantOmegaStarArg 1 τ hτ1'
  have hprime : -1 < ω'_* τω := selfConcordantOmegaPrimeStar_gt_neg_one τω
  have hprime1 : -1 < ((1 : NNReal) : ℝ) * ω'_* τω := by
    simpa using hprime
  let tω : Ioi (-1 : ℝ) := selfConcordantOmegaArg 1 (ω'_* τω) hprime1
  have htω0 : 0 ≤ (tω : ℝ) := by
    -- The canonical primal optimizer `ω'_*(τ)` is nonnegative on `[0, 1)`.
    have hω' : 0 ≤ ω'_* τω := by
      simpa [τω] using selfConcordantOmegaPrimeStar_nonneg hτ0 hτ1
    simpa [tω] using hω'
  have hne : 1 - τ ≠ 0 := by
    linarith
  have hone : 1 + τ / (1 - τ) = 1 / (1 - τ) := by
    field_simp [hne]
    ring
  -- Evaluate the support functional exactly at the canonical maximizer `ξ = ω'_*(τ)`.
  have hvalue : ω_* τω = τ * ω'_* τω - ω tω := by
    rw [selfConcordantOmegaStar_apply, selfConcordantOmegaPrimeStar_apply, selfConcordantOmega_apply]
    simp [tω, τω]
    rw [hone, one_div, Real.log_inv]
    field_simp [hne]
    ring
  -- Compare every admissible competitor to `ω_*(τ)` using the same log inequality route.
  have hmax :
      IsMaxOn
        (fun ξ : Ioi (-1 : ℝ) ↦ τ * (ξ : ℝ) - ω ξ)
        {ξ : Ioi (-1 : ℝ) | 0 ≤ (ξ : ℝ)} tω := by
    rw [isMaxOn_iff]
    intro ξ hξ
    have hξ0 : 0 ≤ (ξ : ℝ) := by
      simpa using hξ
    have hξ1 : 0 < 1 + (ξ : ℝ) := by
      nlinarith [show (-1 : ℝ) < (ξ : ℝ) from ξ.property]
    have hτpos : 0 < 1 - τ := by
      linarith
    have hlog : Real.log ((1 + (ξ : ℝ)) * (1 - τ)) ≤ ((1 + (ξ : ℝ)) * (1 - τ)) - 1 := by
      exact Real.log_le_sub_one_of_pos (mul_pos hξ1 hτpos)
    rw [Real.log_mul hξ1.ne' hτpos.ne'] at hlog
    have hineq : τ * (ξ : ℝ) - ω ξ ≤ ω_* τω := by
      rw [selfConcordantOmega_apply, selfConcordantOmegaStar_apply]
      simp [τω] at hlog ⊢
      nlinarith
    have hvalue' : ω_* τω = τ * (tω : ℝ) - ω tω := by
      simpa [tω, τω, mul_comm] using hvalue
    linarith
  have hmem : tω ∈ {ξ : Ioi (-1 : ℝ) | 0 ≤ (ξ : ℝ)} := by
    simpa using htω0
  have hresult :
      tω ∈ {ξ : Ioi (-1 : ℝ) | 0 ≤ (ξ : ℝ)} ∧
        IsMaxOn
          (fun ξ : Ioi (-1 : ℝ) ↦ τ * (ξ : ℝ) - ω ξ)
          {ξ : Ioi (-1 : ℝ) | 0 ≤ (ξ : ℝ)} tω ∧
        ω_* τω = τ * ω'_* τω - ω tω := ⟨hmem, hmax, hvalue⟩
  simpa [tω, τω] using hresult

-- Proof sketch: combine the supremum characterization of `ω_*(τ)` with the admissible test point
-- `t`.
/-- Lemma 5.1.4 (5): the Fenchel--Young inequality
`ω(t) + ω_*(τ) ≥ τ t` holds for `t ≥ 0` and `τ < 1`. -/
theorem selfConcordantOmega_add_selfConcordantOmegaStar_ge_mul
    {t τ : ℝ} (ht : 0 ≤ t) (hτ1 : τ < 1) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg ht)
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    ω tω + ω_* τω ≥ τ * t := by
  have hneg : -1 < t := neg_one_lt_selfConcordantUnit_of_nonneg ht
  have hneg1 : -1 < ((1 : NNReal) : ℝ) * t := by
    simpa using hneg
  let tω : Ioi (-1 : ℝ) := selfConcordantOmegaArg 1 t hneg1
  have hτ1' : ((1 : NNReal) : ℝ) * τ < 1 := by
    simpa using hτ1
  let τω : Iio (1 : ℝ) := selfConcordantOmegaStarArg 1 τ hτ1'
  have ht1 : 0 < 1 + t := by
    linarith
  have hτpos : 0 < 1 - τ := by
    linarith
  have hlog : Real.log ((1 + t) * (1 - τ)) ≤ (1 + t) * (1 - τ) - 1 := by
    exact Real.log_le_sub_one_of_pos (mul_pos ht1 hτpos)
  -- Rewrite to the standard scalar log inequality `log x ≤ x - 1`.
  have hmain : ω tω + ω_* τω ≥ τ * t := by
    rw [selfConcordantOmega_apply, selfConcordantOmegaStar_apply]
    rw [Real.log_mul ht1.ne' hτpos.ne'] at hlog
    simp [tω, τω] at hlog ⊢
    nlinarith
  simpa [tω, τω] using hmain

-- Proof sketch: evaluate the maximization formula for `ω_*(τ)` at the maximizing point
-- `ξ = ω'_*(τ)`.
/-- Lemma 5.1.4 (6): for `τ < 1`, the conjugate value is
`ω_*(τ) = τ ω'_*(τ) - ω(ω'_*(τ))`. -/
theorem selfConcordantOmegaStar_eq_mul_selfConcordantOmegaPrimeStar_sub_selfConcordantOmega
    {τ : ℝ} (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    let tω := selfConcordantOmegaArg 1 (ω'_* τω) (by
      simpa using selfConcordantOmegaPrimeStar_gt_neg_one τω)
    ω_* τω = τ * ω'_* τω - ω tω := by
  have hτ1' : ((1 : NNReal) : ℝ) * τ < 1 := by
    simpa using hτ1
  let τω : Iio (1 : ℝ) := selfConcordantOmegaStarArg 1 τ hτ1'
  have hprime : -1 < ω'_* τω := selfConcordantOmegaPrimeStar_gt_neg_one τω
  have hprime1 : -1 < ((1 : NNReal) : ℝ) * ω'_* τω := by
    simpa using hprime
  let tω : Ioi (-1 : ℝ) := selfConcordantOmegaArg 1 (ω'_* τω) hprime1
  have hne : 1 - τ ≠ 0 := by
    linarith
  have hone : 1 + τ / (1 - τ) = 1 / (1 - τ) := by
    field_simp [hne]
    ring
  -- Expand the explicit formulas and simplify the canonical optimizer identity.
  have hmain : ω_* τω = τ * ω'_* τω - ω tω := by
    rw [selfConcordantOmegaStar_apply, selfConcordantOmegaPrimeStar_apply, selfConcordantOmega_apply]
    simp [tω, τω]
    rw [hone, one_div, Real.log_inv]
    field_simp [hne]
    ring
  simpa [tω, τω] using hmain

-- Proof sketch: substitute `τ = ω'(t)` into part `(6)` and use part `(2)` to identify the
-- maximizing point.
/-- Lemma 5.1.4 (7): for `t > -1`, the original function value can be recovered from the conjugate
by `ω(t) = t ω'(t) - ω_*(ω'(t))`. -/
theorem selfConcordantOmega_eq_mul_selfConcordantOmegaDeriv_sub_selfConcordantOmegaStar
    {t : ℝ} (ht : -1 < t) :
    let tω := selfConcordantOmegaArg 1 t (by
      simpa using ht)
    let τω := selfConcordantOmegaStarArg 1 (ω' tω) (by
      simpa using selfConcordantOmegaDeriv_lt_one tω)
    ω tω = t * ω' tω - ω_* τω := by
  have ht1' : -1 < ((1 : NNReal) : ℝ) * t := by
    simpa using ht
  let tω : Ioi (-1 : ℝ) := selfConcordantOmegaArg 1 t ht1'
  have hτω1 : ω' tω < 1 := selfConcordantOmegaDeriv_lt_one tω
  have hτω1' : ((1 : NNReal) : ℝ) * ω' tω < 1 := by
    simpa using hτω1
  let τω : Iio (1 : ℝ) := selfConcordantOmegaStarArg 1 (ω' tω) hτω1'
  have hprime : -1 < ω'_* τω := selfConcordantOmegaPrimeStar_gt_neg_one τω
  have hprime1 : -1 < ((1 : NNReal) : ℝ) * ω'_* τω := by
    simpa using hprime
  let tω' : Ioi (-1 : ℝ) := selfConcordantOmegaArg 1 (ω'_* τω) hprime1
  -- Use part (6) at the canonical slope `τ = ω'(t)`.
  have hstar : ω_* τω = ω' tω * ω'_* τω - ω tω' := by
    simpa [tω, τω, tω'] using
      (selfConcordantOmegaStar_eq_mul_selfConcordantOmegaPrimeStar_sub_selfConcordantOmega
        (τ := ω' tω) hτω1)
  -- Identify the maximizing point with the original `t` via the inverse identity.
  have hinv : ω'_* τω = t := by
    simpa [tω, τω] using
      (selfConcordantOmegaPrimeStar_selfConcordantOmegaDeriv (t := t) ht)
  have htω' : tω' = tω := by
    apply Subtype.ext
    simpa [tω, tω'] using hinv
  have hstar' : ω_* τω = t * ω' tω - ω tω := by
    rw [hinv, htω'] at hstar
    simpa [mul_comm] using hstar
  have hmain : ω tω = t * ω' tω - ω_* τω := by
    linarith
  simpa [tω, τω] using hmain

end
