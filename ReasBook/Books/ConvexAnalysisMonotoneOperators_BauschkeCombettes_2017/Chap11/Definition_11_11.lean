/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [SeminormedAddCommGroup H]

/-- Definition 11.11 (1): an extended-real-valued function is coercive when its values tend to
`+∞` along every net for which `‖x‖ → +∞`. -/
abbrev Coercive (f : H → EReal) : Prop :=
  Filter.Tendsto f (Bornology.cobounded H) (nhds (⊤ : EReal))

/-- Definition 11.11 (2): an extended-real-valued function is supercoercive when the quotient
`f x / ‖x‖` tends to `+∞` as `‖x‖ → +∞`. -/
abbrev Supercoercive (f : H → EReal) : Prop :=
  Filter.Tendsto (fun x ↦ f x / ‖x‖) (Bornology.cobounded H) (nhds (⊤ : EReal))

/-- Coercivity is equivalently convergence to `+∞` along the textbook norm-at-infinity filter. -/
theorem coercive_iff_tendsto_norm_atTop (f : H → EReal) :
    Coercive f ↔
      Filter.Tendsto f (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : EReal)) := by
  simp [Coercive, comap_norm_atTop]

/-- Supercoercivity is equivalently convergence of `x ↦ f x / ‖x‖` to `+∞` along the textbook
norm-at-infinity filter. -/
theorem supercoercive_iff_tendsto_norm_atTop (f : H → EReal) :
    Supercoercive f ↔
      Filter.Tendsto (fun x ↦ f x / ‖x‖)
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : EReal)) := by
  simp [Supercoercive, comap_norm_atTop]

/-- On a singleton seminormed additive group, every extended-real-valued function is coercive. -/
theorem coercive_of_subsingleton [Subsingleton H] (f : H → EReal) :
    Coercive f := by
  simp [Coercive]

/-- On a singleton seminormed additive group, every extended-real-valued function is supercoercive. -/
theorem supercoercive_of_subsingleton [Subsingleton H] (f : H → EReal) :
    Supercoercive f := by
  simp [Supercoercive]

/-- A supercoercive extended-real-valued function is coercive. -/
theorem coercive_of_supercoercive {f : H → EReal} (hf : Supercoercive f) :
    Coercive f := by
  change Filter.Tendsto f (Bornology.cobounded H) (nhds (⊤ : EReal))
  change Filter.Tendsto (fun x ↦ f x / ‖x‖) (Bornology.cobounded H) (nhds (⊤ : EReal)) at hf
  rw [EReal.tendsto_nhds_top_iff_real] at hf ⊢
  intro ξ
  have hnorm : ∀ᶠ x in Bornology.cobounded H, (1 : ℝ) ≤ ‖x‖ := by
    simpa using
      (eventually_cobounded_le_norm (1 : ℝ) :
        ∀ᶠ x in Bornology.cobounded H, (1 : ℝ) ≤ ‖x‖)
  by_cases hξ : 0 ≤ ξ
  · have hquot : ∀ᶠ x in Bornology.cobounded H, (ξ : EReal) < f x / ‖x‖ := hf ξ
    filter_upwards [hquot, hnorm] with x hxquot hxnorm
    have hnorm_pos : (0 : EReal) < ‖x‖ := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hxnorm
    have hxmul : (ξ : EReal) * ‖x‖ < f x :=
      (EReal.lt_div_iff hnorm_pos (by simp)).1 hxquot
    have hxle : (ξ : EReal) ≤ (ξ : EReal) * ‖x‖ := by
      calc
        (ξ : EReal) = (ξ : EReal) * 1 := by simp
        _ ≤ (ξ : EReal) * ‖x‖ := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hxnorm) (by exact_mod_cast hξ)
    exact lt_of_le_of_lt hxle hxmul
  · have hquot : ∀ᶠ x in Bornology.cobounded H, (0 : EReal) < f x / ‖x‖ := hf 0
    filter_upwards [hquot, hnorm] with x hxquot hxnorm
    have hnorm_pos : (0 : EReal) < ‖x‖ := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hxnorm
    have hpos' : (0 : EReal) * ‖x‖ < f x :=
      (EReal.lt_div_iff hnorm_pos (by simp)).1 hxquot
    have hpos : (0 : EReal) < f x := by
      simpa using hpos'
    exact lt_trans (by exact_mod_cast not_le.mp hξ) hpos

end ERealFunction
