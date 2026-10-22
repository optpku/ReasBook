/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SelfConcordantAuxiliaryFunction

noncomputable section

/-
Proposition 5.0.22 lies in the Chapter 5 one-variable convexity / auxiliary-function domain.

Sampled owner-style declarations:
* `selfConcordantOmega` and `selfConcordantOmegaStar` in `Definition_5_0_21`, the chapter owners
  for `ω` and `ω_*`;
* `selfConcordantOmega_apply` and `selfConcordantOmegaStar_apply`, the canonical owner-level
  evaluation lemmas recovering the textbook scalar formulas from those owners;
* `convexOn_of_deriv2_nonneg` in mathlib, the standard one-variable convexity owner for proving
  interval convexity from nonnegative second derivative;
* `convex_Ioi` and `convex_Iio`, the canonical interval-convexity owners for the two domains.

Source/core/bridge triage:
* source-facing: the convexity of the Chapter 5 auxiliary functions on their natural intervals;
* core/canonical: the chapter owners `ω` and `ω_*` together with mathlib's `ConvexOn`;
* bridge/view: the canonical ambient real-valued extensions
  `Function.extend Subtype.val ω 0` and `Function.extend Subtype.val ω_* 0`, used only because
  `ConvexOn` is stated for total functions on `ℝ`.

Primitive data:
* the source-facing owners `ω : Set.Ioi (-1) → ℝ` and `ω_* : Set.Iio 1 → ℝ`.

Derived API:
* their canonical ambient extensions via `Function.extend Subtype.val ... 0`, which agree with
  the owners on the relevant convex domains and are mathematically irrelevant off those domains.

This refinement removes the duplicate raw-formula surface from the proposition statements and
reuses the chapter owners directly. -/

-- Proof sketch: compute the second derivatives of the two scalar functions,
-- `ω''(t) = (1 + t)⁻²` on `(-1, ∞)` and `ω_*''(τ) = (1 - τ)⁻²` on `(-∞, 1)`,
-- and apply the standard one-variable criterion that nonnegative second derivative
-- on a convex interval implies convexity.

/-- Helper for Proposition 5.0.22: the ambient extension of `ω` agrees with the raw scalar
formula on its natural interval. -/
private lemma selfConcordantOmega_extend_eqOn_raw :
    Set.EqOn (Function.extend Subtype.val ω 0)
      (fun x : ℝ ↦ x - Real.log (1 + x))
      (Set.Ioi (-1 : ℝ)) := by
  intro x hx
  -- On the subtype domain, `Function.extend` reduces to ordinary evaluation of `ω`.
  rw [Function.extend_val_apply hx]
  simp

/-- Helper for Proposition 5.0.22: the raw scalar formula for `ω` has the expected first
derivative on `(-1, ∞)`. -/
private lemma selfConcordantOmega_raw_hasDerivAt {x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun y : ℝ ↦ y - Real.log (1 + y)) (1 - (1 + x)⁻¹) x := by
  have hx_ne : 1 + x ≠ 0 := by linarith
  -- Differentiate `x` and `log (1 + x)` separately, then simplify the resulting scalar algebra.
  simpa using
    (hasDerivAt_id x).sub
      ((Real.hasDerivAt_log hx_ne).comp x ((hasDerivAt_id x).const_add 1))

/-- Helper for Proposition 5.0.22: the derivative of the raw `ω` formula has the expected second
derivative on `(-1, ∞)`. -/
private lemma selfConcordantOmega_raw_deriv_hasDerivAt {x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun y : ℝ ↦ 1 - (1 + y)⁻¹) (((1 + x) ^ 2)⁻¹) x := by
  have hx_ne : 1 + x ≠ 0 := by linarith
  -- Route correction: differentiate the inverse branch directly, so the second derivative
  -- appears as the reciprocal of a square with no quotient-rule bookkeeping.
  have h_inv :
      HasDerivAt (fun y : ℝ ↦ (1 + y)⁻¹) (-1 / (1 + x) ^ 2) x := by
    simpa using (((hasDerivAt_id x).const_add 1).inv hx_ne)
  -- Subtracting the inverse derivative from the constant `1` yields the positive reciprocal term.
  convert (hasDerivAt_const x (1 : ℝ)).sub h_inv using 1
  all_goals simp [div_eq_mul_inv]

/-- Helper for Proposition 5.0.22: the raw scalar formula for `ω` is convex on `(-1, ∞)`. -/
private lemma selfConcordantOmega_raw_convexOn :
    ConvexOn ℝ (Set.Ioi (-1 : ℝ))
      (fun x : ℝ ↦ x - Real.log (1 + x)) := by
  -- The open interval is convex, so it suffices to show the second derivative is nonnegative.
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi (-1 : ℝ))
    (f' := fun x : ℝ ↦ 1 - (1 + x)⁻¹)
    (f'' := fun x : ℝ ↦ ((1 + x) ^ 2)⁻¹) ?_ ?_ ?_ ?_
  · intro x hx
    -- The first derivative witness gives continuity on the interval for free.
    exact (selfConcordantOmega_raw_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    -- Since `(-1, ∞)` is open, the within-derivative matches the ordinary derivative.
    simpa [interior_Ioi] using
      (selfConcordantOmega_raw_hasDerivAt (by simpa [interior_Ioi] using hx)).hasDerivWithinAt
  · intro x hx
    -- Apply the same open-set reduction to the derivative formula itself.
    simpa [interior_Ioi] using
      (selfConcordantOmega_raw_deriv_hasDerivAt (by simpa [interior_Ioi] using hx)).hasDerivWithinAt
  · intro x hx
    have hx_pos : 0 < 1 + x := by
      have : -1 < x := by simpa [interior_Ioi] using hx
      linarith
    -- The second derivative is the reciprocal of a positive square.
    have hx_sq_pos : 0 < (1 + x) ^ 2 := by positivity
    have hx_inv_pos : 0 < (((1 + x) ^ 2)⁻¹ : ℝ) := by positivity
    exact le_of_lt hx_inv_pos

/-- Helper for Proposition 5.0.22: the ambient extension of `ω_*` agrees with the raw scalar
formula on its natural interval. -/
private lemma selfConcordantOmegaStar_extend_eqOn_raw :
    Set.EqOn (Function.extend Subtype.val ω_* 0)
      (fun x : ℝ ↦ -x - Real.log (1 - x))
      (Set.Iio (1 : ℝ)) := by
  intro x hx
  -- On the subtype domain, `Function.extend` reduces to ordinary evaluation of `ω_*`.
  rw [Function.extend_val_apply hx]
  simp

/-- Helper for Proposition 5.0.22: the raw scalar formula for `ω_*` has the expected first
derivative on `(-∞, 1)`. -/
private lemma selfConcordantOmegaStar_raw_hasDerivAt {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y : ℝ ↦ -y - Real.log (1 - y)) ((-1 : ℝ) + (1 - x)⁻¹) x := by
  have hx_ne : 1 - x ≠ 0 := by linarith
  have h_log :
      HasDerivAt (fun y : ℝ ↦ Real.log (1 - y)) (-(1 - x)⁻¹) x := by
    -- Differentiate `log (1 - y)` by composing with the affine map `y ↦ 1 - y`.
    simpa using
      (Real.hasDerivAt_log hx_ne).comp x ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
  -- Combining the `-y` and `-log (1 - y)` contributions gives the textbook derivative formula.
  simpa using ((hasDerivAt_id x).neg).sub h_log

/-- Helper for Proposition 5.0.22: the derivative of the raw `ω_*` formula has the expected
second derivative on `(-∞, 1)`. -/
private lemma selfConcordantOmegaStar_raw_deriv_hasDerivAt {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y : ℝ ↦ (-1 : ℝ) + (1 - y)⁻¹) (((1 - x) ^ 2)⁻¹) x := by
  have hx_ne : 1 - x ≠ 0 := by linarith
  have h_inv :
      HasDerivAt (fun y : ℝ ↦ (1 - y)⁻¹) (1 / (1 - x) ^ 2) x := by
    -- The derivative of the inverse picks up two minus signs, so the result is positive.
    simpa using (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).inv hx_ne)
  -- Adding the constant `-1` does not change the derivative.
  convert (hasDerivAt_const x (-1 : ℝ)).add h_inv using 1
  all_goals simp [div_eq_mul_inv]

/-- Helper for Proposition 5.0.22: the raw scalar formula for `ω_*` is convex on `(-∞, 1)`. -/
private lemma selfConcordantOmegaStar_raw_convexOn :
    ConvexOn ℝ (Set.Iio (1 : ℝ))
      (fun x : ℝ ↦ -x - Real.log (1 - x)) := by
  -- The same second-derivative criterion applies on the left-open interval.
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Iio (1 : ℝ))
    (f' := fun x : ℝ ↦ (-1 : ℝ) + (1 - x)⁻¹)
    (f'' := fun x : ℝ ↦ ((1 - x) ^ 2)⁻¹) ?_ ?_ ?_ ?_
  · intro x hx
    -- The first derivative witness supplies continuity on the domain.
    exact (selfConcordantOmegaStar_raw_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    -- Since `(-∞, 1)` is open, the within-derivative matches the ordinary derivative.
    simpa [interior_Iio] using
      (selfConcordantOmegaStar_raw_hasDerivAt (by simpa [interior_Iio] using hx)).hasDerivWithinAt
  · intro x hx
    -- Apply the same open-set reduction to the derivative formula.
    simpa [interior_Iio] using
      (selfConcordantOmegaStar_raw_deriv_hasDerivAt
        (by simpa [interior_Iio] using hx)).hasDerivWithinAt
  · intro x hx
    have hx_pos : 0 < 1 - x := by
      have : x < 1 := by simpa [interior_Iio] using hx
      linarith
    -- Again the second derivative is the reciprocal of a positive square.
    have hx_sq_pos : 0 < (1 - x) ^ 2 := by positivity
    have hx_inv_pos : 0 < (((1 - x) ^ 2)⁻¹ : ℝ) := by positivity
    exact le_of_lt hx_inv_pos

/-- Proposition 5.0.22 (1): the ambient real-function view of the Chapter 5 owner `ω` is convex
on `(-1, ∞)`. -/
theorem selfConcordantOmega_convexOn :
    ConvexOn ℝ (Set.Ioi (-1 : ℝ))
      (Function.extend Subtype.val ω 0) := by
  -- Prove convexity for the raw scalar formula, then transport it back to the owner-level view.
  refine selfConcordantOmega_raw_convexOn.congr ?_
  intro x hx
  symm
  exact selfConcordantOmega_extend_eqOn_raw hx

/-- Proposition 5.0.22 (2): the ambient real-function view of the Chapter 5 owner `ω_*` is convex
on `(-∞, 1)`. -/
theorem selfConcordantOmegaStar_convexOn :
    ConvexOn ℝ (Set.Iio (1 : ℝ))
      (Function.extend Subtype.val ω_* 0) := by
  -- Repeat the same transport step for `ω_*` after proving convexity of the raw formula.
  refine selfConcordantOmegaStar_raw_convexOn.congr ?_
  intro x hx
  symm
  exact selfConcordantOmegaStar_extend_eqOn_raw hx

end
