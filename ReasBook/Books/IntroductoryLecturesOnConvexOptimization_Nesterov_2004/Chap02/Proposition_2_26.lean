/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexAnalysis

/-
Primary domain: one-variable secant estimates for convex value functions.

Owner abstractions sampled before refining:
* mathlib `ConvexOn`
* mathlib `ConvexOn.slope_mono_adjacent`
* mathlib `ConvexOn.secant_mono`
* chapter `extendedRealEffectiveDomain`
* chapter `extendedRealRealPart`

Best owner abstraction:
* `ConvexOn 𝕜 s f` on the ordered-field line

Primitive data:
* a function on the scalar line
* convexity on the ambient owner set

Derived API:
* the left-shifted secant lower bound below on the canonical ordered-field owner
* the finite-value `EReal` bridge via `extendedRealEffectiveDomain` and `extendedRealRealPart`

Source/core/bridge triage:
* source-facing: Proposition 2.26 for an extended-real value function with finite comparison points
* core/canonical: `ConvexOn 𝕜 s f` and `ConvexOn.secant_mono`
* bridge/view: restricting an `EReal`-valued function to its finite real part

The public file therefore keeps the source-facing finite-value statement and the owner scalar-line
secant theorem, but no parallel wrapper structure. The midpoint finite-value condition is derived
from convexity of the finite-value domain rather than stored as primitive data.
-/

namespace ConvexOn

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {s : Set 𝕜} {f : 𝕜 → 𝕜}

/-- A convex function on a convex subset of a linearly ordered field satisfies the left-shifted
secant lower bound obtained by comparing the secants over `[t₁ - Δ, t₁]` and `[t₁, t₂]`. -/
-- Proof sketch: if `Δ = 0`, the claim is immediate. For `Δ > 0`, apply
-- `ConvexOn.secant_mono` with base point `t₁`, after deriving `t₁ ∈ s` from convexity of `s`,
-- and rearrange the resulting secant inequality.
theorem secant_lower_bound_left_shift (hf : ConvexOn 𝕜 s f)
    {t1 t2 Delta : 𝕜} (hleft : t1 - Delta ∈ s) (ht2 : t2 ∈ s)
    (hDelta : 0 ≤ Delta) (ht : t1 < t2) :
    f (t1 - Delta) ≥
      f t1 + (Delta / (t2 - t1)) * (f t1 - f t2) := by
  rcases eq_or_lt_of_le hDelta with rfl | hDelta
  · simp
  have ht1 : t1 ∈ s := by
    exact hf.1.ordConnected.out hleft ht2 ⟨by linarith, ht.le⟩
  have hslope :
      (f t1 - f (t1 - Delta)) / Delta ≤ (f t2 - f t1) / (t2 - t1) := by
    have hsecant :=
      hf.secant_mono ht1 hleft ht2 (by linarith) ht.ne' (by linarith)
    convert hsecant using 1
    ring
  have hstep :
      f t1 - f (t1 - Delta) ≤
        ((f t2 - f t1) / (t2 - t1)) * Delta := by
    exact (div_le_iff₀ hDelta).1 hslope
  have hbound :
      f t1 - f (t1 - Delta) ≤
        (Delta / (t2 - t1)) * (f t2 - f t1) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  linarith

/-- If a convex function on a convex subset of a linearly ordered field is positive at `t₁` and
nonpositive at a right endpoint `t₂`, then necessarily `t₁ < t₂`, and the left-shifted secant
lower bound specialized to `t₂` gives a lower estimate at every `t₀ < t₁`. -/
theorem strict_lt_and_secant_lower_bound_of_nonpos_right
    (hf : ConvexOn 𝕜 s f) {t0 t1 t2 : 𝕜} (ht0 : t0 ∈ s) (ht2 : t2 ∈ s)
    (ht0t1 : t0 < t1) (ht1t2 : t1 ≤ t2)
    (hpos : 0 < f t1) (ht2_nonpos : f t2 ≤ 0) :
    t1 < t2 ∧
      f t0 ≥ f t1 + ((t1 - t0) / (t2 - t1)) * f t1 := by
  have ht1_ne_t2 : t1 ≠ t2 := by
    intro h
    exact not_le_of_gt hpos (by simpa [h] using ht2_nonpos)
  have ht1t2' : t1 < t2 :=
    lt_of_le_of_ne ht1t2 ht1_ne_t2
  let coeff : 𝕜 := (t1 - t0) / (t2 - t1)
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    exact div_nonneg (sub_nonneg.mpr ht0t1.le) (sub_nonneg.mpr ht1t2'.le)
  have hshift : t1 - (t1 - t0) = t0 := by
    ring
  have hleft : t1 - (t1 - t0) ∈ s := by
    simpa [hshift] using ht0
  have hsecant :
      f t1 + coeff * (f t1 - f t2) ≤ f t0 := by
    dsimp [coeff]
    simpa [hshift] using
      (hf.secant_lower_bound_left_shift
        hleft
        ht2
        (sub_nonneg.mpr ht0t1.le)
        ht1t2')
  have hdrop_term :
      coeff * f t1 ≤ coeff * (f t1 - f t2) := by
    refine mul_le_mul_of_nonneg_left ?_ hcoeff_nonneg
    linarith
  have hdrop :
      f t1 + coeff * f t1 ≤
        f t1 + coeff * (f t1 - f t2) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_left hdrop_term (f t1)
  refine ⟨ht1t2', ?_⟩
  simpa [coeff] using hdrop.trans hsecant

end

end ConvexOn

/-- Proposition 2.26: if an extended-real convex value function is finite at the secant endpoints,
then the same left-shifted secant lower bound holds for its finite real values. This is the
source-facing finite-value form used for functions such as `t ↦ f^*(t; x̄; γ)`. -/
theorem secant_lower_bound_left_shift_of_finite_values
    {f : ℝ → EReal}
    (hf : ConvexOn ℝ (dom f) (extendedRealRealPart f))
    {t1 t2 Delta : ℝ}
    (hleft : t1 - Delta ∈ dom f)
    (ht2 : t2 ∈ dom f)
    (hDelta : 0 ≤ Delta) (ht : t1 < t2) :
    extendedRealRealPart f (t1 - Delta) ≥
      extendedRealRealPart f t1 +
        (Delta / (t2 - t1)) * (extendedRealRealPart f t1 - extendedRealRealPart f t2) := by
  simpa using hf.secant_lower_bound_left_shift hleft ht2 hDelta ht
