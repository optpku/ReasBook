/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Filter.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_4

noncomputable section

open Filter Asymptotics

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

-- Domain sampling:
-- * primary domain: asymptotic convergence rates for normed-space sequences.
-- * sampled core owners: mathlib's `Asymptotics.IsLittleO` / `=o[atTop]`,
--   Chapter 03's `HasSuperlinearConvergenceTo`, and Chapter 01's
--   `HasQSuperlinearConvergenceTo`.
-- * source/core/bridge triage: `HasSuperlinearlyConvergentStep` is the source-facing owner for
--   the SQP trial-step notion `(12.3.2)`. The raw ratio `sqpStepErrorRatio` is derived API, and
--   the little-`o` and Chapter 03 superlinear-sequence formulations are only bridges because the
--   source ratio uses totalized division, so equivalence with `=o[atTop]` needs an explicit
--   zero-denominator compatibility hypothesis.

/-- The SQP step error ratio `‖x k + d k - xStar‖ / ‖x k - xStar‖` from `(12.3.2)`. -/
def sqpStepErrorRatio (x d : ℕ → E) (xStar : E) : ℕ → ℝ :=
  fun k ↦ ‖x k + d k - xStar‖ / ‖x k - xStar‖

/-- The defining formula for `sqpStepErrorRatio`. -/
@[simp] theorem sqpStepErrorRatio_apply (x d : ℕ → E) (xStar : E) (k : ℕ) :
    sqpStepErrorRatio x d xStar k = ‖x k + d k - xStar‖ / ‖x k - xStar‖ := rfl

/-- Chapter12 Definition 12.3-extra-1: an SQP search-direction sequence `d` for iterates `x` is
a superlinearly convergent step relative to `xStar` when the ratio
`‖x k + d k - xStar‖ / ‖x k - xStar‖` tends to `0` along `atTop`, i.e. when `(12.3.2)` holds. -/
def HasSuperlinearlyConvergentStep (x d : ℕ → E) (xStar : E) : Prop :=
  Tendsto (sqpStepErrorRatio x d xStar) atTop (nhds (0 : ℝ))

/-- Unfolding characterization of `HasSuperlinearlyConvergentStep`. -/
theorem hasSuperlinearlyConvergentStep_iff (x d : ℕ → E) (xStar : E) :
    HasSuperlinearlyConvergentStep x d xStar ↔
      Tendsto (fun k ↦ ‖x k + d k - xStar‖ / ‖x k - xStar‖) atTop (nhds (0 : ℝ)) :=
  Iff.rfl

/-- Under the natural denominator-zero compatibility
`x k = xStar → x k + d k = xStar` on a tail, the source ratio-limit formulation `(12.3.2)`
agrees with the canonical little-`o` owner for the numerator and denominator error functions. -/
theorem hasSuperlinearlyConvergentStep_iff_isLittleO
    (x d : ℕ → E) (xStar : E)
    (hzero : ∀ᶠ k in atTop, x k = xStar → x k + d k = xStar) :
    HasSuperlinearlyConvergentStep x d xStar ↔
      (fun k ↦ ‖x k + d k - xStar‖) =o[atTop] fun k ↦ ‖x k - xStar‖ := by
  have hnorm :
      ∀ᶠ k in atTop, ‖x k - xStar‖ = 0 → ‖x k + d k - xStar‖ = 0 :=
    hzero.mono fun k hk hkNorm ↦ by
      rw [norm_eq_zero] at hkNorm ⊢
      exact sub_eq_zero.2 (hk (sub_eq_zero.1 hkNorm))
  change Tendsto (fun k ↦ ‖x k + d k - xStar‖ / ‖x k - xStar‖) atTop (nhds (0 : ℝ)) ↔
      (fun k ↦ ‖x k + d k - xStar‖) =o[atTop] fun k ↦ ‖x k - xStar‖
  exact (isLittleO_iff_tendsto' hnorm).symm

/-- Under the eventual full-step update `x (k + 1) = x k + d k` and the same denominator-zero
compatibility needed for the source ratio, the SQP step condition refines to the canonical
Chapter 03 superlinear-convergence owner for the iterate sequence. -/
theorem HasSuperlinearlyConvergentStep.toHasSuperlinearConvergenceTo
    {x d : ℕ → E} {xStar : E}
    (h : HasSuperlinearlyConvergentStep x d xStar)
    (hx : Tendsto x atTop (nhds xStar))
    (hzero : ∀ᶠ k in atTop, x k = xStar → x k + d k = xStar)
    (hupdate : ∀ᶠ k in atTop, x (k + 1) = x k + d k) :
    HasSuperlinearConvergenceTo x xStar := by
  have hlittle :
      (fun k ↦ ‖x k + d k - xStar‖) =o[atTop] fun k ↦ ‖x k - xStar‖ :=
    (hasSuperlinearlyConvergentStep_iff_isLittleO x d xStar hzero).1 h
  have hnum :
      (fun k ↦ ‖x k + d k - xStar‖) =ᶠ[atTop] fun k ↦ ‖x (k + 1) - xStar‖ := by
    filter_upwards [hupdate] with k hk
    simp [hk]
  exact
    { tendsto := hx
      isLittleO := hlittle.congr' hnum (EventuallyEq.refl _ _) }

/-- Under the eventual full-step update `x (k + 1) = x k + d k`, the source SQP step ratio is
exactly the canonical Chapter 1 `Q`-superlinear ratio on a tail, so the step condition refines
directly to `HasQSuperlinearConvergenceTo`. -/
theorem HasSuperlinearlyConvergentStep.toHasQSuperlinearConvergenceTo
    {x d : ℕ → E} {xStar : E}
    (h : HasSuperlinearlyConvergentStep x d xStar)
    (hx : Tendsto x atTop (nhds xStar))
    (hupdate : ∀ᶠ k in atTop, x (k + 1) = x k + d k) :
    HasQSuperlinearConvergenceTo x xStar := by
  have hratio :
      (qErrorRatio x xStar 1) =ᶠ[atTop] sqpStepErrorRatio x d xStar := by
    filter_upwards [hupdate] with k hk
    simp [qErrorRatio, sqpStepErrorRatio, hk, Real.rpow_one]
  exact
    { tendsto := hx
      ratio_tendsto := Tendsto.congr' hratio.symm h }

/-- Under the eventual full-step update `x (k + 1) = x k + d k` and the natural
denominator-zero compatibility for the source ratio, the SQP step condition is equivalent to the
canonical Chapter 03 superlinear-convergence owner for the iterate sequence. -/
theorem hasSuperlinearlyConvergentStep_iff_hasSuperlinearConvergenceTo
    {x d : ℕ → E} {xStar : E}
    (hx : Tendsto x atTop (nhds xStar))
    (hzero : ∀ᶠ k in atTop, x k = xStar → x k + d k = xStar)
    (hupdate : ∀ᶠ k in atTop, x (k + 1) = x k + d k) :
    HasSuperlinearlyConvergentStep x d xStar ↔ HasSuperlinearConvergenceTo x xStar := by
  constructor
  · intro h
    exact h.toHasSuperlinearConvergenceTo hx hzero hupdate
  · intro h
    have hnum :
        (fun k ↦ ‖x (k + 1) - xStar‖) =ᶠ[atTop] fun k ↦ ‖x k + d k - xStar‖ := by
      filter_upwards [hupdate] with k hk
      simp [hk]
    have hlittle :
        (fun k ↦ ‖x k + d k - xStar‖) =o[atTop] fun k ↦ ‖x k - xStar‖ :=
      h.isLittleO.congr' hnum (EventuallyEq.refl _ _)
    exact (hasSuperlinearlyConvergentStep_iff_isLittleO x d xStar hzero).2 hlittle

end
