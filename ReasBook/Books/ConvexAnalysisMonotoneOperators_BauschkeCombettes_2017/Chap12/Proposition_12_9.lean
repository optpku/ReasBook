/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- The `p`-power norm kernel `x ↦ ‖x‖^p / (γ p)` as an `]-∞,+∞]`-valued function. -/
noncomputable def normPowerKernel (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) :
    H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ ‖x‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))).toEReal

/-- Coercing the `p`-power norm kernel to `EReal` recovers the formula `‖x‖^p / (γ p)`. -/
@[simp]
theorem normPowerKernel_apply (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) (x : H) :
    (normPowerKernel p γ x : EReal) =
      (((‖x‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := by
  simp [normPowerKernel]

/-- The `p`-power infimal-convolution regularization `g_γ = f □ (‖·‖^p / (γ p))`. -/
noncomputable def normPowerEnvelope {α : Type*} [CoeTC α EReal] (f : H → α) (p : Set.Ici (1 : ℝ))
    (γ : Set.Ioi (0 : ℝ)) : H → EReal :=
  f □ normPowerKernel p γ

-- Proof sketch: unfold `normPowerEnvelope` and apply `infimalConvolution_apply`.
/-- The value of the `p`-power envelope at `x` is the defining infimum over translated `p`-power
norm penalizations. -/
theorem normPowerEnvelope_apply {α : Type*} [CoeTC α EReal] (f : H → α) (p : Set.Ici (1 : ℝ))
    (γ : Set.Ioi (0 : ℝ)) (x : H) :
    normPowerEnvelope f p γ x =
      ⨅ y : H, (f y : EReal) +
        (((‖x - y‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := by
  simp [normPowerEnvelope, infimalConvolution_apply]

-- Proof sketch: unfold both envelopes as infimal convolutions and use the kernel-identification
-- theorem for `p = 2`.
/-- For the quadratic exponent `p = 2`, the `p`-power envelope is exactly the canonical Moreau
envelope `{}^[γ] f`. -/
theorem normPowerEnvelope_two_eq_moreauEnvelope
    {α : Type*} [CoeTC α EReal] (f : H → α) (γ : Set.Ioi (0 : ℝ)) :
    normPowerEnvelope f ⟨(2 : ℝ), by norm_num⟩ γ = {}^[γ] f := sorry

-- Proof sketch: Proposition 12.6 (ii) gives
-- `dom (f □ normPowerKernel p γ) = dom f + dom (normPowerKernel p γ)`, and the kernel is finite on
-- all of `H`, so its domain is `Set.univ`. This is the full-domain / upper-finiteness statement:
-- it rules out the value `⊤`, but not a priori the value `⊥`.
/-- Proposition 12.9 (1): clause (i), the `p`-power envelope has full domain, equivalently it
never attains the value `+∞`. -/
theorem dom_normPowerEnvelope_eq_univ
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty)
    (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) :
    dom (normPowerEnvelope f p γ) = Set.univ := sorry

-- Proof sketch: compare the penalization factors `1 / (μ p) ≤ 1 / (γ p)` when `γ < μ`, then use
-- the definition of the infimal convolution. The lower bound comes from
-- `sInf (Set.range f) ≤ f y` for every `y`, and the upper bound comes from testing the infimum at
-- `y = x`.
/-- Proposition 12.9 (2): clause (ii), if `γ < μ`, then the `μ`-envelope is pointwise below the
`γ`-envelope, while the `γ`-envelope value lies between the infimum of `f` and `f x`. -/
theorem normPowerEnvelope_mono_and_mem_Icc
    (f : H → Set.Ioi (⊥ : EReal)) (p : Set.Ici (1 : ℝ))
    (γ μ : Set.Ioi (0 : ℝ)) (hγμ : (γ : ℝ) < μ) (x : H) :
    normPowerEnvelope f p μ x ∈
        Set.Icc (sInf (Set.range f.asEReal)) (normPowerEnvelope f p γ x) ∧
      normPowerEnvelope f p γ x ≤ (f x : EReal) := sorry

-- Proof sketch: apply part (ii) pointwise to compare the ranges of `f` and `normPowerEnvelope f p
-- γ`, then use the universal characterization of `sInf`.
/-- Proposition 12.9 (3): clause (iii), the `p`-power envelope has the same infimum over `H` as
`f`. -/
theorem sInf_range_normPowerEnvelope_eq_sInf_range (f : H → Set.Ioi (⊥ : EReal))
    (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) :
    sInf (Set.range (normPowerEnvelope f p γ)) = sInf (Set.range f.asEReal) := sorry

-- Proof sketch: the lower bound is part (ii). For the upper bound, fix `y`, estimate the infimum
-- defining `normPowerEnvelope f p μ x` by the single test point `y`, and let `μ → +∞` so the
-- penalization term tends to `0`.
/-- Proposition 12.9 (4): clause (iv), for each `x`, the `p`-power envelope values converge to the
infimum of `f` as `γ → +∞`. -/
theorem tendsto_normPowerEnvelope_atTop (f : H → Set.Ioi (⊥ : EReal))
    (p : Set.Ici (1 : ℝ)) (x : H) :
    Filter.Tendsto (fun γ : Set.Ioi (0 : ℝ) ↦ normPowerEnvelope f p γ x) Filter.atTop
      (nhds (sInf (Set.range f.asEReal))) := sorry

-- Proof sketch: choose `z ∈ dom f` using properness, evaluate the infimal convolution at that
-- fixed point, and bound the translated kernel on `Metric.ball x ρ` via the triangle inequality.
/-- Proposition 12.9 (5): clause (v), for fixed `γ`, the `p`-power envelope is bounded above on
every open ball of `H`. -/
theorem normPowerEnvelope_boundedAbove_on_ball
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty)
    (p : Set.Ici (1 : ℝ)) (γ : Set.Ioi (0 : ℝ)) :
    ∀ x : H, ∀ ρ : Set.Ioi (0 : ℝ), ∃ M : ℝ,
      ∀ y ∈ Metric.ball x (ρ : ℝ), normPowerEnvelope f p γ y ≤ (M : EReal) := sorry

end ERealFunction
