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

/- Lemma 5.1.5 lies in the Chapter 5 self-concordant auxiliary-function domain.

Sampled owner-style declarations:
* `selfConcordantOmega` and the scoped notation `ω` from `Definition_5_0_21`, the chapter owner
  for the auxiliary function `t ↦ t - log (1 + t)`;
* `selfConcordantOmegaStar` and the scoped notation `ω_*` from `Definition_5_0_21`, the chapter
  owner for the auxiliary function `t ↦ -t - log (1 - t)`;
* `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg` from `Definition_5_0_21`, the
  scaled-argument bridge constructors used elsewhere in Chapter 5 but not as the main scalar
  surface here;
* `selfConcordantOmega_apply` and `selfConcordantOmegaStar_apply`, the canonical owner-level
  evaluation lemmas recovering the textbook scalar formulas;
* `Real.log_le_sub_one_of_pos` in mathlib, the standard logarithmic comparison theorem underlying
  the elementary rational sandwich estimates.

Source/core/bridge triage:
* source-facing: the textbook rational lower and upper bounds for `ω` on `[0, ∞)` and for `ω_*`
  on `[0, 1)`;
* core/canonical: the Chapter 5 owners `ω` and `ω_*`;
* bridge/view: the subtype constructors `selfConcordantOmegaArg`,
  `selfConcordantOmegaStarArg`, and the subtype-level evaluation lemmas
  `selfConcordantOmega_apply`, `selfConcordantOmegaStar_apply`.

Primitive data:
* a real parameter `t` in the textbook domain (`0 ≤ t`, or `0 ≤ t < 1` for `ω_*`).

Derived API:
* the rational comparison statements, now stated directly against the canonical owners `ω` and
  `ω_*`, with the raw logarithmic formulas recovered by the existing evaluation lemmas.

This refinement keeps the source-facing inequalities unchanged while removing the duplicate raw
formula surface from the main declarations. -/

-- Proof sketch: use the elementary denominator comparison
-- `1 + (2 / 3) t ≤ 1 + t` for `t ≥ 0`, then divide the common numerator `t^2` by the
-- corresponding positive denominators.
/-- The simpler lower rational approximation with denominator `1 + t` is bounded above by the
intermediate lower bound with denominator `1 + (2 / 3) t`. -/
theorem selfConcordantOmega_simpleLowerBound_le_intermediate
    {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 / (2 * (1 + t)) ≤
      t ^ 2 / (2 * (1 + (2 / 3 : ℝ) * t)) := by
  -- Compare the positive denominators and clear them in one pass.
  have hden₁ : 0 < 2 * (1 + t) := by nlinarith
  have hden₂ : 0 < 2 * (1 + (2 / 3 : ℝ) * t) := by nlinarith
  field_simp [hden₁.ne', hden₂.ne']
  nlinarith

/-- Helper for Lemma 5.1.5: the raw scalar lower bound
`t ^ 2 / (2 * (1 + (2 / 3) t)) ≤ t - log (1 + t)` on `[0, ∞)`. -/
lemma omegaIntermediateLowerBoundRaw
    {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 / (2 * (1 + (2 / 3 : ℝ) * t)) ≤ t - Real.log (1 + t) := by
  let g : ℝ → ℝ := fun x ↦ x - Real.log (1 + x) - x ^ 2 / (2 * (1 + (2 / 3 : ℝ) * x))
  -- Route correction: the stable Lean route is to show the gap `g` is monotone on `[0, ∞)`.
  have hcont : ContinuousOn g (Set.Ici 0) := by
    intro x hx
    have hx0 : 0 ≤ x := by simpa using hx
    have hx1 : 1 + x ≠ 0 := by nlinarith
    have hx2 : 2 * (1 + (2 / 3 : ℝ) * x) ≠ 0 := by nlinarith
    have hid : ContinuousAt (fun y : ℝ ↦ y) x := by simpa using continuousAt_id
    have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
      have hinner : ContinuousAt (fun y : ℝ ↦ 1 + y) x := by
        simpa using continuousAt_const.add continuousAt_id
      exact hinner.log hx1
    have hrat : ContinuousAt (fun y : ℝ ↦ y ^ 2 / (2 * (1 + (2 / 3 : ℝ) * y))) x := by
      have hnum : ContinuousAt (fun y : ℝ ↦ y ^ 2) x := by
        simpa using continuousAt_id.pow 2
      have hsmul : ContinuousAt (fun y : ℝ ↦ (2 / 3 : ℝ) * y) x := by
        simpa using continuousAt_const.mul continuousAt_id
      have hinner : ContinuousAt (fun y : ℝ ↦ 1 + (2 / 3 : ℝ) * y) x := by
        simpa using continuousAt_const.add hsmul
      have hden : ContinuousAt (fun y : ℝ ↦ 2 * (1 + (2 / 3 : ℝ) * y)) x := by
        simpa using continuousAt_const.mul hinner
      exact hnum.div hden hx2
    exact ((hid.sub hlog).sub hrat).continuousWithinAt
  have hderiv :
      ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt g (x ^ 3 / ((x + 1) * (2 * x + 3) ^ 2)) x := by
    intro x hx
    have hx0 : 0 < x := by simpa using hx
    have hx1 : 1 + x ≠ 0 := by nlinarith
    have hx2 : 2 * x + 3 ≠ 0 := by nlinarith
    have hlog :
        HasDerivAt (fun y : ℝ ↦ Real.log (1 + y)) ((1 + x)⁻¹) x := by
      simpa using (((hasDerivAt_id x).const_add 1).log hx1)
    have hmain :
        HasDerivAt (fun y : ℝ ↦ y - Real.log (1 + y)) (x / (1 + x)) x := by
      convert (hasDerivAt_id x).sub hlog using 1
      field_simp [hx1]
      ring
    have hfrac :
        HasDerivAt
          (fun y : ℝ ↦ y ^ 2 / (2 * y + 3))
          ((2 * x * (2 * x + 3) - x ^ 2 * 2) / (2 * x + 3) ^ 2) x := by
      have hden : HasDerivAt (fun y : ℝ ↦ 2 * y + 3) 2 x := by
        simpa
            [two_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
          (((hasDerivAt_id x).const_mul 2).const_add 3)
      have hquot := (hasDerivAt_pow 2 x).div hden (by nlinarith)
      convert hquot using 1
      · ring_nf
    have hquad :
        HasDerivAt
          (fun y : ℝ ↦ y ^ 2 / (2 * (1 + (2 / 3 : ℝ) * y)))
          (3 * x * (x + 3) / (2 * x + 3) ^ 2) x := by
      convert hfrac.const_mul (3 / 2 : ℝ) using 1
      · ext y
        field_simp
        ring
      · field_simp [hx2]
        ring
    have hderivEq :
        x / (1 + x) - 3 * x * (x + 3) / (2 * x + 3) ^ 2 =
          x ^ 3 / ((x + 1) * (2 * x + 3) ^ 2) := by
      field_simp [hx1, hx2]
      ring
    convert hmain.sub hquad using 1
    · simpa using hderivEq.symm
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun x ↦
      x ^ 3 / ((x + 1) * (2 * x + 3) ^ 2)) hcont ?_ ?_
    · intro x hx
      have hx' : x ∈ Set.Ioi (0 : ℝ) := by
        simpa [interior_Ici] using hx
      exact (hderiv x hx').hasDerivWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa using hx
      have hx1 : 0 < x + 1 := by nlinarith
      have hx2 : 0 < (2 * x + 3) ^ 2 := by positivity
      positivity
  -- Evaluate the monotone gap at `0` and transport the conclusion back to `t`.
  have hgap : 0 ≤ g t := by
    have hmono' := hmono (by simp) ht ht
    simpa [g] using hmono'
  simpa [g] using hgap

/-- Helper for Lemma 5.1.5: the raw scalar upper bound
`t - log (1 + t) ≤ t ^ 2 / (2 + t)` on `[0, ∞)`. -/
lemma omegaUpperBoundRaw
    {t : ℝ} (ht : 0 ≤ t) :
    t - Real.log (1 + t) ≤ t ^ 2 / (2 + t) := by
  -- Use mathlib's sharp lower bound on `log (1 + t)` and rearrange.
  have hlog : 2 * t / (t + 2) ≤ Real.log (1 + t) :=
    Real.le_log_one_add_of_nonneg ht
  have ht2 : 0 < t + 2 := by linarith
  have hrewrite : 2 * t / (t + 2) = t - t ^ 2 / (t + 2) := by
    field_simp [ht2.ne']
    ring
  have hcalc : t - t ^ 2 / (t + 2) ≤ Real.log (1 + t) := by
    simpa [hrewrite] using hlog
  have hsub : t - Real.log (1 + t) ≤ t ^ 2 / (t + 2) := by
    linarith
  simpa [add_comm] using hsub

/-- Helper for Lemma 5.1.5: the raw scalar lower bound
`τ ^ 2 / (2 - τ) ≤ -τ - log (1 - τ)` on `[0, 1)`. -/
lemma omegaStarLowerBoundRaw
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    τ ^ 2 / (2 - τ) ≤ -τ - Real.log (1 - τ) := by
  let x : ℝ := τ / (2 - τ)
  have h1τ : 0 < 1 - τ := by linarith
  have h2τ : 0 < 2 - τ := by linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x < 1 := by
    dsimp [x]
    refine (div_lt_one h2τ).2 ?_
    linarith
  have hx_add : 1 + x = 2 / (2 - τ) := by
    dsimp [x]
    field_simp [h2τ.ne']
    ring
  have hx_sub : 1 - x = 2 * (1 - τ) / (2 - τ) := by
    dsimp [x]
    field_simp [h2τ.ne']
    ring
  have hratio : (1 + x) / (1 - x) = (1 - τ)⁻¹ := by
    rw [hx_add, hx_sub]
    field_simp [h1τ.ne', h2τ.ne']
  have hseries : x ≤ -(2⁻¹ * Real.log (1 - τ)) := by
    simpa [x, hratio, Real.log_inv] using Real.sum_range_le_log_div hx0 hx1 1
  have hlog : 2 * τ / (2 - τ) ≤ -Real.log (1 - τ) := by
    have hdouble : 2 * x ≤ -Real.log (1 - τ) := by
      nlinarith [hseries]
    calc
      2 * τ / (2 - τ) = 2 * x := by
        dsimp [x]
        field_simp [h2τ.ne']
      _ ≤ -Real.log (1 - τ) := hdouble
  have hrewrite : 2 * τ / (2 - τ) - τ = τ ^ 2 / (2 - τ) := by
    field_simp [h2τ.ne']
    ring
  linarith [hlog, hrewrite]

/-- Helper for Lemma 5.1.5: the raw scalar upper bound
`-τ - log (1 - τ) ≤ τ ^ 2 / (2 * (1 - τ))` on `[0, 1)`. -/
lemma omegaStarUpperBoundRaw
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    -τ - Real.log (1 - τ) ≤ τ ^ 2 / (2 * (1 - τ)) := by
  let x : ℝ := τ / (2 - τ)
  have h1τ : 0 < 1 - τ := by linarith
  have h2τ : 0 < 2 - τ := by linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x < 1 := by
    dsimp [x]
    refine (div_lt_one h2τ).2 ?_
    linarith
  have hx_add : 1 + x = 2 / (2 - τ) := by
    dsimp [x]
    field_simp [h2τ.ne']
    ring
  have hx_sub : 1 - x = 2 * (1 - τ) / (2 - τ) := by
    dsimp [x]
    field_simp [h2τ.ne']
    ring
  have hratio : (1 + x) / (1 - x) = (1 - τ)⁻¹ := by
    rw [hx_add, hx_sub]
    field_simp [h1τ.ne', h2τ.ne']
  have htail : 2 * (x + x ^ 3 / (1 - x ^ 2)) = τ * (2 - τ) / (2 * (1 - τ)) := by
    have hx_cube : x ^ 3 / (1 - x ^ 2) = τ ^ 3 / (4 * (1 - τ) * (2 - τ)) := by
      calc
        x ^ 3 / (1 - x ^ 2) = (τ ^ 3 / (2 - τ) ^ 3) / ((4 - 4 * τ) / (2 - τ) ^ 2) := by
          dsimp [x]
          field_simp [h1τ.ne', h2τ.ne']
          have hden : (2 - τ) ^ 2 - τ ^ 2 = 4 * (1 - τ) := by ring
          rw [hden]
          field_simp [h1τ.ne']
        _ = τ ^ 3 / (4 * (1 - τ) * (2 - τ)) := by
          have h4eq : 4 - 4 * τ = 4 * (1 - τ) := by ring
          rw [h4eq]
          field_simp [h1τ.ne', h2τ.ne']
    rw [hx_cube]
    dsimp [x]
    have h4 : 4 - τ * 4 ≠ 0 := by nlinarith
    field_simp [h1τ.ne', h2τ.ne', h4]
    have haux : τ ^ 3 * (4 - τ * 4)⁻¹ * 4 - τ ^ 4 * (4 - τ * 4)⁻¹ * 4 = τ ^ 3 := by
      have h4eq : 4 - τ * 4 = 4 * (1 - τ) := by ring
      rw [h4eq]
      field_simp [h1τ.ne']
    linarith
  have hseries :
      -(2⁻¹ * Real.log (1 - τ)) ≤ x + x ^ 3 / (1 - x ^ 2) := by
    simpa [x, hratio, Real.log_inv] using Real.log_div_le_sum_range_add hx0 hx1 1
  have hlog : -Real.log (1 - τ) ≤ τ * (2 - τ) / (2 * (1 - τ)) := by
    have hdouble : -Real.log (1 - τ) ≤ 2 * (x + x ^ 3 / (1 - x ^ 2)) := by
      nlinarith [hseries]
    calc
      -Real.log (1 - τ) ≤ 2 * (x + x ^ 3 / (1 - x ^ 2)) := hdouble
      _ = τ * (2 - τ) / (2 * (1 - τ)) := htail
  have hrewrite : τ * (2 - τ) / (2 * (1 - τ)) - τ = τ ^ 2 / (2 * (1 - τ)) := by
    field_simp [h1τ.ne']
    ring
  linarith [hlog, hrewrite]

-- Proof sketch: compare `ω' (t) = t / (1 + t)` with the derivatives of
-- `t ↦ t^2 / (2 * (1 + (2 / 3) * t))` and `t ↦ t^2 / (2 + t)` on `[0, ∞)`, use that all three
-- functions vanish at `t = 0`, and integrate the derivative inequalities.
/-- Lemma 5.1.5: for `t ≥ 0`, the self-concordant auxiliary function
`ω(t)` lies between the rational bounds
`t² / (2 * (1 + (2 / 3) t))` and `t² / (2 + t)`. -/
theorem selfConcordantOmega_bounds
    {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      have h : -1 < ((1 : NNReal) : ℝ) * t := neg_one_lt_mf_mul_of_nonneg ht
      simpa using h)
    t ^ 2 / (2 * (1 + (2 / 3 : ℝ) * t)) ≤ ω tω ∧
      ω tω ≤ t ^ 2 / (2 + t) := by
  dsimp
  constructor
  · -- Rewrite the owner-level value `ω tω` to the textbook scalar formula and apply the raw bound.
    simpa using omegaIntermediateLowerBoundRaw ht
  · -- The upper bound follows from the same owner-level rewrite.
    simpa using omegaUpperBoundRaw ht

-- Proof sketch: compare `ω'_* (t) = t / (1 - t)` with the derivatives of
-- `t ↦ t^2 / (2 - t)` and `t ↦ t^2 / (2 * (1 - t))` on `[0, 1)`, note that all three functions
-- vanish at `t = 0`, and integrate the derivative inequalities along the interval.
/-- For `t ∈ [0, 1)`, the auxiliary function `ω_*(t)` is squeezed between
`t² / (2 - t)` and `t² / (2 * (1 - t))`. -/
theorem selfConcordantOmegaStar_bounds
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    τ ^ 2 / (2 - τ) ≤ ω_* τω ∧
      ω_* τω ≤ τ ^ 2 / (2 * (1 - τ)) := by
  dsimp
  constructor
  · -- Reduce `ω_* τω` to `-τ - log (1 - τ)` and apply the raw lower estimate.
    simpa using omegaStarLowerBoundRaw hτ0 hτ1
  · -- Reduce `ω_* τω` to `-τ - log (1 - τ)` and apply the raw upper estimate.
    simpa using omegaStarUpperBoundRaw hτ0 hτ1

end
