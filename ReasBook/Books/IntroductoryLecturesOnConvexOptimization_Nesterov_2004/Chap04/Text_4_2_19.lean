/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient MinGradientNormAlongIterates

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.19 lies in the chapter finite-window best-gradient domain for accelerated
cubic-Newton rate estimates.

Sampled owner declarations:
* `minGradientNormAlongIterates` in `Chap02/Definition_2_23`, the core owner for the sampled
  minimum gradient norm over a finite iterate window;
* the source-facing notation `g[f; x; k, T | h]` for that owner, also in
  `Chap02/Definition_2_23`;
* `accelerated_cubic_newton_min_gradient_norm_le_explicit_rate` in `Text_4_2_18`, the immediate
  predecessor source-facing rate statement for the same sampled-minimum domain.

Source/core/bridge triage:
* source-facing: Text 4.2.19's sampled minimum gradient norm over the window `1 ≤ k ≤ 4m`,
  written below as `g⋆[m]`;
* core/canonical: `minGradientNormAlongIterates f x 1 (4 * m) h`;
* bridge/view: the local source-facing notation `g⋆[m]`, with no extra owner-level wrapper.

Primitive data:
* the objective `f`, iterate sequence `x`, initial point `x0`, and comparison point `xStar`;
* the integer parameter `m`, with the source window condition `m ≥ 1`;
* the source-required positive-`L₃` regime `0 < (L3 : ℝ)`;
* the single comparison `f xStar ≤ f (x (4 * m))` used to pass from the gap at `x_{3m}`
  relative to `xStar` to the drop from `x_{3m}` to `x_{4m}`;
* the gap and descent inequalities at the iterates `x_{3m}` and `x_{4m}`.

Derived API:
* the specialized sampled minimum gradient norm `g⋆[m]`;
* the intermediate `rpow` estimate and the final explicit rate stated in the text.

Accordingly, this file works at the weaker iterate-sequence layer already used in `Text_4_2_18`:
the accelerated cubic-Newton algorithm package is not primitive mathematical data for the two
displayed inequalities, so the public theorems are stated for an arbitrary sequence `x : ℕ → E`.
The fixed-start sampled minimum is written with the local notation `g⋆[m]` so the theorem surface
does not expose the auxiliary witness `1 ≤ 4m`, and the intermediate and explicit estimates remain
separate atomic theorems instead of a conjunction-valued wrapper. -/

section AcceleratedCubicNewtonGradientNormBound

variable {f : E → ℝ} {L3 : NNReal} {x : ℕ → E} {x0 xStar : E}
variable {m : ℕ} (hm : 1 ≤ m)
local notation "g⋆[" m "]" => g[f; x; 1, 4 * m | by omega]

/-- Helper for Text 4 2 19: the sampled minimum over the first `4m` iterates is nonnegative
because it is attained by a gradient norm. -/
lemma sampledMinNonneg :
    0 ≤ g⋆[m] := by
  -- Realize the sampled minimum as one sampled gradient norm in the window.
  rcases minGradientNormAlongIterates.exists_eq f x (by omega : 1 ≤ 4 * m) with
      ⟨i, -, -, hi_eq⟩
  rw [hi_eq]
  exact norm_nonneg _

/-- Helper for Text 4 2 19: for a positive third-order Lipschitz constant, `L₃^(3/2)` splits into
`L₃ * sqrt L₃`. -/
lemma l3_rpowThreeHalvesEqMulSqrt
    (hL3 : 0 < (L3 : ℝ)) :
    Real.rpow (L3 : ℝ) (3 / 2 : ℝ) = (L3 : ℝ) * Real.sqrt (L3 : ℝ) := by
  -- Rewrite `3 / 2` as `1 + 1 / 2` so the square-root factor appears explicitly.
  calc
    Real.rpow (L3 : ℝ) (3 / 2 : ℝ) = Real.rpow (L3 : ℝ) ((1 : ℝ) + 1 / 2) := by
      norm_num
    _ = Real.rpow (L3 : ℝ) (1 : ℝ) * Real.rpow (L3 : ℝ) (1 / 2 : ℝ) := by
      simpa using Real.rpow_add hL3 (1 : ℝ) (1 / 2 : ℝ)
    _ = (L3 : ℝ) * Real.rpow (L3 : ℝ) (1 / 2 : ℝ) := by
      simp [Real.rpow_one]
    _ = (L3 : ℝ) * Real.sqrt (L3 : ℝ) := by
      simp [Real.sqrt_eq_rpow]

/-- Helper for Text 4 2 19: combining the displayed gap estimate at `x_{3m}` with the descent
bound from `x_{3m}` to `x_{4m}` yields the intermediate `3 / 2`-power inequality for `g⋆[m]`. -/
lemma sampledMinRpowThreeHalvesLeIntermediateRate
    (hL3 : 0 < (L3 : ℝ))
    (hxStar4m : f xStar ≤ f (x (4 * m)))
    (hgap :
      f (x (3 * m)) - f xStar ≤
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((3 * m : ℝ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
    (hdrop :
      f (x (3 * m)) - f (x (4 * m)) ≥
        ((m : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[m] (3 / 2 : ℝ)) :
    Real.rpow g⋆[m] (3 / 2 : ℝ) ≤
      ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
        ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))) := by
  have hsqrt_pos : 0 < Real.sqrt (L3 : ℝ) := Real.sqrt_pos.2 hL3
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hm
  have hcoeff_pos : 0 < ((m : ℝ) / (3 * Real.sqrt (L3 : ℝ))) := by
    positivity
  have hupper_gap :
      f (x (3 * m)) - f (x (4 * m)) ≤
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((3 * m : ℝ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)) := by
    -- Compare `f (x (4m))` to `f xStar`, then insert the displayed gap bound at `x_{3m}`.
    linarith
  have hdescent_le :
      ((m : ℝ) / (3 * Real.sqrt (L3 : ℝ))) * Real.rpow g⋆[m] (3 / 2 : ℝ) ≤
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((3 * m : ℝ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)) :=
    hdrop.trans hupper_gap
  have hdiv :
      Real.rpow g⋆[m] (3 / 2 : ℝ) ≤
        ((8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((3 * m : ℝ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))) /
          (((m : ℝ) / (3 * Real.sqrt (L3 : ℝ)))) := by
    -- Divide by the positive descent coefficient.
    refine (le_div_iff₀ hcoeff_pos).2 ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdescent_le
  have hquotient :
      ((8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((3 * m : ℝ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))) /
          (((m : ℝ) / (3 * Real.sqrt (L3 : ℝ)))) =
        ((8 : ℝ) * (L3 : ℝ) * Real.sqrt (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)) := by
    -- Normalize the quotient so the factor `L₃ * sqrt L₃` can be repackaged as `L₃^(3/2)`.
    field_simp [hsqrt_pos.ne', hm_pos.ne',
      show ((3 * m : ℝ)) ≠ 0 by positivity,
      show (((3 * m : ℝ) + 1)) ≠ 0 by positivity,
      show (((3 * m : ℝ) + 2)) ≠ 0 by positivity]
  rw [hquotient] at hdiv
  calc
    Real.rpow g⋆[m] (3 / 2 : ℝ) ≤
        ((8 : ℝ) * (L3 : ℝ) * Real.sqrt (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)) := hdiv
    _ =
        ((8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        congrArg
          (fun t : ℝ ↦
            ((8 : ℝ) * t * ‖x0 - xStar‖ ^ (3 : ℕ)) /
              ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
          (l3_rpowThreeHalvesEqMulSqrt (L3 := L3) hL3).symm

-- Proof sketch: the comparison `hxStar4m : f xStar ≤ f (x (4m))` gives
-- `f (x (3m)) - f (x (4m)) ≤ f (x (3m)) - f xStar`. Combine the assumed upper and
-- lower bounds, using `hL3 : 0 < (L3 : ℝ)` for the square-root and `rpow` manipulations, to get
-- an estimate on `Real.rpow g⋆[m] (3 / 2)`, then raise both sides to the power `2 / 3`.
/-- Under `0 < (L3 : ℝ)`, the comparison `f xStar ≤ f (x (4 * m))`, the gap bound at
`x_{3m}`, and the descent lower bound from `x_{3m}` to `x_{4m}`,
Text 4.2.19 first yields the intermediate estimate on the sampled minimum
`g⋆[m] = min_{1 ≤ k ≤ 4m} ‖∇ f (x k)‖`,
namely
`g⋆[m] ≤
(8 L₃^(3/2) R₀^3 / (m² (3m + 1) (3m + 2)))^(2/3)`, where `R₀ = ‖x₀ - xStar‖`. -/
theorem acceleratedCubicNewton_minGradientNorm_le_intermediate_bound
    (hL3 : 0 < (L3 : ℝ))
    (hxStar4m : f xStar ≤ f (x (4 * m)))
    (hgap :
      f (x (3 * m)) - f xStar ≤
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((3 * m : ℝ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
    (hdrop :
      f (x (3 * m)) - f (x (4 * m)) ≥
        ((m : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[m] (3 / 2 : ℝ)) :
    g⋆[m] ≤
      Real.rpow
        ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
        (2 / 3 : ℝ) := by
  have hg_nonneg : 0 ≤ g⋆[m] := sampledMinNonneg (f := f) (x := x) (m := m) hm
  have hrpow_bound :
      Real.rpow g⋆[m] (3 / 2 : ℝ) ≤
        ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))) :=
    sampledMinRpowThreeHalvesLeIntermediateRate
      (f := f) (x := x) (x0 := x0) (xStar := xStar) (m := m) hm
      hL3 hxStar4m hgap hdrop
  have hraised :
      Real.rpow (Real.rpow g⋆[m] (3 / 2 : ℝ)) (2 / 3 : ℝ) ≤
        Real.rpow
          ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
            ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
          (2 / 3 : ℝ) := by
    -- Raise the `3 / 2`-power inequality to the reciprocal exponent `2 / 3`.
    exact Real.rpow_le_rpow (Real.rpow_nonneg hg_nonneg _) hrpow_bound (by norm_num)
  -- Collapse the reciprocal exponents to recover the sampled minimum itself.
  calc
    g⋆[m] = Real.rpow g⋆[m] (1 : ℝ) := by
      simp
    _ = Real.rpow (Real.rpow g⋆[m] (3 / 2 : ℝ)) (2 / 3 : ℝ) := by
      simpa [show ((3 / 2 : ℝ) * (2 / 3 : ℝ)) = 1 by norm_num] using
        (Real.rpow_mul hg_nonneg (3 / 2 : ℝ) (2 / 3 : ℝ))
    _ ≤
        Real.rpow
          ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
            ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
          (2 / 3 : ℝ) := hraised

/-- Helper for Text 4 2 19: the intermediate `rpow` bound is dominated by the displayed explicit
rate once the denominator is compared to a crude `m⁴` lower bound. -/
lemma intermediateBoundLeExplicitRate
    (hm : 1 ≤ m)
    (hL3 : 0 < (L3 : ℝ)) :
    Real.rpow
        ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
        (2 / 3 : ℝ) ≤
      ((2 : ℝ) ^ (8 : ℕ) * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        Real.rpow (4 * m : ℝ) (8 / 3 : ℝ) := by
  have hL3_nonneg : 0 ≤ (L3 : ℝ) := by
    exact_mod_cast L3.2
  have hnorm_nonneg : 0 ≤ ‖x0 - xStar‖ := norm_nonneg _
  have hm_nonneg : 0 ≤ (m : ℝ) := by
    positivity
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hm
  have hL3_rpow_nonneg : 0 ≤ Real.rpow (L3 : ℝ) (3 / 2 : ℝ) :=
    Real.rpow_nonneg hL3_nonneg _
  have hnum_first :
      Real.rpow
          (((8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) * ‖x0 - xStar‖ ^ (3 : ℕ))
          (2 / 3 : ℝ) =
        Real.rpow ((8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) *
          Real.rpow (‖x0 - xStar‖ ^ (3 : ℕ)) (2 / 3 : ℝ) := by
    -- Split the numerator into the scalar factor and the cubic norm factor.
    simpa using
      (Real.mul_rpow
        (x := (8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ))
        (y := ‖x0 - xStar‖ ^ (3 : ℕ))
        (z := (2 / 3 : ℝ))
        (by positivity : 0 ≤ (8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ))
        (by positivity : 0 ≤ ‖x0 - xStar‖ ^ (3 : ℕ)))
  have hnum_second :
      Real.rpow ((8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) =
        Real.rpow (8 : ℝ) (2 / 3 : ℝ) *
          Real.rpow (Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) := by
    -- Split the remaining scalar factor so each exponent can be simplified separately.
    simpa using
      (Real.mul_rpow
        (x := (8 : ℝ))
        (y := Real.rpow (L3 : ℝ) (3 / 2 : ℝ))
        (z := (2 / 3 : ℝ))
        (by positivity)
        hL3_rpow_nonneg)
  have hnum :
      Real.rpow
          ((8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ))
          (2 / 3 : ℝ) =
        Real.rpow (8 : ℝ) (2 / 3 : ℝ) *
          Real.rpow (Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) *
          Real.rpow (‖x0 - xStar‖ ^ (3 : ℕ)) (2 / 3 : ℝ) := by
    -- Associate the triple product into a two-step `mul_rpow` decomposition.
    rw [show ((8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) =
        (((8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) * ‖x0 - xStar‖ ^ (3 : ℕ)) by ring]
    rw [hnum_first, hnum_second]
  have h8 :
      Real.rpow (8 : ℝ) (2 / 3 : ℝ) = 4 := by
    have h8pow : (8 : ℝ) = Real.rpow (2 : ℝ) (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
    calc
      Real.rpow (8 : ℝ) (2 / 3 : ℝ) =
          Real.rpow (Real.rpow (2 : ℝ) (3 : ℝ)) (2 / 3 : ℝ) := by
        rw [h8pow]
      _ = Real.rpow (2 : ℝ) ((3 : ℝ) * (2 / 3 : ℝ)) := by
        simpa using (Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ)) (3 : ℝ) (2 / 3 : ℝ)).symm
      _ = 4 := by
        norm_num [Real.rpow_natCast]
  have hL3_collapse :
      Real.rpow (Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) = (L3 : ℝ) := by
    -- Collapse the reciprocal exponents on `L₃`.
    calc
      Real.rpow (Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) =
          Real.rpow (L3 : ℝ) ((3 / 2 : ℝ) * (2 / 3 : ℝ)) := by
        simpa using (Real.rpow_mul hL3_nonneg (3 / 2 : ℝ) (2 / 3 : ℝ)).symm
      _ = (L3 : ℝ) := by
        norm_num [Real.rpow_one]
  have hnorm_collapse :
      Real.rpow (‖x0 - xStar‖ ^ (3 : ℕ)) (2 / 3 : ℝ) =
        ‖x0 - xStar‖ ^ (2 : ℕ) := by
    -- Collapse the reciprocal exponents on the cubic norm factor.
    have hnorm_pow : ‖x0 - xStar‖ ^ (3 : ℕ) = Real.rpow ‖x0 - xStar‖ (3 : ℝ) := by
      simp
    calc
      Real.rpow (‖x0 - xStar‖ ^ (3 : ℕ)) (2 / 3 : ℝ) =
          Real.rpow (Real.rpow ‖x0 - xStar‖ (3 : ℝ)) (2 / 3 : ℝ) := by
        rw [hnorm_pow]
      _ = Real.rpow ‖x0 - xStar‖ ((3 : ℝ) * (2 / 3 : ℝ)) := by
        simpa using (Real.rpow_mul hnorm_nonneg (3 : ℝ) (2 / 3 : ℝ)).symm
      _ = ‖x0 - xStar‖ ^ (2 : ℕ) := by
        norm_num [Real.rpow_natCast]
  have hmainRewrite :
      Real.rpow
          ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
            ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
          (2 / 3 : ℝ) =
        (4 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          Real.rpow
            ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))
            (2 / 3 : ℝ) := by
    -- Rewrite the intermediate bound as a simple numerator over a single `rpow` denominator.
    calc
      Real.rpow
          ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
            ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
          (2 / 3 : ℝ) =
          Real.rpow
              ((8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ))
              (2 / 3 : ℝ) /
            Real.rpow
              ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))
              (2 / 3 : ℝ) := by
        simpa using
          (Real.div_rpow
            (x := (8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ))
            (y := (m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))
            (z := (2 / 3 : ℝ))
            (by positivity : 0 ≤ (8 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) *
              ‖x0 - xStar‖ ^ (3 : ℕ))
            (by positivity : 0 ≤
              (m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
      _ =
          (Real.rpow (8 : ℝ) (2 / 3 : ℝ) *
              Real.rpow (Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) *
              Real.rpow (‖x0 - xStar‖ ^ (3 : ℕ)) (2 / 3 : ℝ)) /
            Real.rpow
              ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))
              (2 / 3 : ℝ) := by
        rw [hnum]
      _ =
          (4 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            Real.rpow
              ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))
              (2 / 3 : ℝ) := by
        rw [h8, hL3_collapse, hnorm_collapse]
  have hlinear_one : (m : ℝ) ≤ (3 * m : ℝ) + 1 := by
    nlinarith
  have hlinear_two : (m : ℝ) ≤ (3 * m : ℝ) + 2 := by
    nlinarith
  have hden_ge :
      (m : ℝ) ^ (4 : ℕ) ≤
        (m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2) := by
    -- The quadratic-linear denominator dominates the crude lower bound `m⁴`.
    have hmul :
        (m : ℝ) * (m : ℝ) ≤ ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2) := by
      exact mul_le_mul hlinear_one hlinear_two (by positivity) (by positivity)
    calc
      (m : ℝ) ^ (4 : ℕ) = (m : ℝ) ^ (2 : ℕ) * ((m : ℝ) * (m : ℝ)) := by
        ring
      _ ≤ (m : ℝ) ^ (2 : ℕ) * (((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)) := by
        exact mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2) := by
        ring
  have hden_rpow :
      Real.rpow ((m : ℝ) ^ (4 : ℕ)) (2 / 3 : ℝ) ≤
        Real.rpow
          ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))
          (2 / 3 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) hden_ge (by norm_num)
  have hm4_rpow_pos : 0 <
      Real.rpow ((m : ℝ) ^ (4 : ℕ)) (2 / 3 : ℝ) := by
    exact Real.rpow_pos_of_pos (by positivity : 0 < (m : ℝ) ^ (4 : ℕ)) _
  have hboundToM :
      (4 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          Real.rpow
            ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))
            (2 / 3 : ℝ) ≤
        (4 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          Real.rpow ((m : ℝ) ^ (4 : ℕ)) (2 / 3 : ℝ) := by
    -- Replace the true denominator by the weaker but simpler lower bound `m⁴`.
    exact div_le_div_of_nonneg_left (by positivity) hm4_rpow_pos hden_rpow
  have hm_collapse :
      Real.rpow ((m : ℝ) ^ (4 : ℕ)) (2 / 3 : ℝ) =
        Real.rpow (m : ℝ) (8 / 3 : ℝ) := by
    -- Collapse the exponents on `m⁴`.
    have hm_pow : (m : ℝ) ^ (4 : ℕ) = Real.rpow (m : ℝ) (4 : ℝ) := by
      simp
    calc
      Real.rpow ((m : ℝ) ^ (4 : ℕ)) (2 / 3 : ℝ) =
          Real.rpow (Real.rpow (m : ℝ) (4 : ℝ)) (2 / 3 : ℝ) := by
        rw [hm_pow]
      _ = Real.rpow (m : ℝ) ((4 : ℝ) * (2 / 3 : ℝ)) := by
        simpa using (Real.rpow_mul hm_nonneg (4 : ℝ) (2 / 3 : ℝ)).symm
      _ = Real.rpow (m : ℝ) (8 / 3 : ℝ) := by
        norm_num
  have hconstMul :
      (4 : ℝ) * Real.rpow (4 : ℝ) (8 / 3 : ℝ) ≤ (2 : ℝ) ^ (8 : ℕ) := by
    -- The displayed constant is intentionally loose, so it dominates the simplified numerator.
    have hsplit :
        Real.rpow (4 : ℝ) (8 / 3 : ℝ) =
          Real.rpow (4 : ℝ) (2 : ℝ) * Real.rpow (4 : ℝ) (2 / 3 : ℝ) := by
      simpa [show (8 / 3 : ℝ) = (2 : ℝ) + 2 / 3 by norm_num] using
        (Real.rpow_add (by positivity : 0 < (4 : ℝ)) (2 : ℝ) (2 / 3 : ℝ))
    calc
      (4 : ℝ) * Real.rpow (4 : ℝ) (8 / 3 : ℝ) =
          (4 : ℝ) * Real.rpow (4 : ℝ) (2 : ℝ) * Real.rpow (4 : ℝ) (2 / 3 : ℝ) := by
        rw [hsplit]
        ring
      _ ≤ (4 : ℝ) * Real.rpow (4 : ℝ) (2 : ℝ) * (4 : ℝ) := by
        have hpow_le : Real.rpow (4 : ℝ) (2 / 3 : ℝ) ≤ (4 : ℝ) := by
          simpa [Real.rpow_one] using
            (Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1 : ℝ) ≤ 4)
              (by norm_num : (2 / 3 : ℝ) ≤ 1))
        exact mul_le_mul_of_nonneg_left hpow_le
          (by norm_num [Real.rpow_natCast] :
            0 ≤ (4 : ℝ) * Real.rpow (4 : ℝ) (2 : ℝ))
      _ = (2 : ℝ) ^ (8 : ℕ) := by
        norm_num [Real.rpow_natCast]
  have hrpow4_pos : 0 < Real.rpow (4 : ℝ) (8 / 3 : ℝ) := by
    exact Real.rpow_pos_of_pos (by positivity : 0 < (4 : ℝ)) _
  have hconst :
      (4 : ℝ) ≤ ((2 : ℝ) ^ (8 : ℕ)) / Real.rpow (4 : ℝ) (8 / 3 : ℝ) := by
    -- Divide the constant comparison by the positive factor `4^(8/3)`.
    refine (le_div_iff₀ hrpow4_pos).2 ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using hconstMul
  have htargetFactor :
      ((2 : ℝ) ^ (8 : ℕ) * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          Real.rpow (4 * m : ℝ) (8 / 3 : ℝ) =
        ((((2 : ℝ) ^ (8 : ℕ)) / Real.rpow (4 : ℝ) (8 / 3 : ℝ)) *
            (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          Real.rpow (m : ℝ) (8 / 3 : ℝ) := by
    -- Factor the explicit denominator into the constant piece `4^(8/3)` and the `m` piece.
    have hmul :
        Real.rpow (4 * m : ℝ) (8 / 3 : ℝ) =
          Real.rpow (4 : ℝ) (8 / 3 : ℝ) * Real.rpow (m : ℝ) (8 / 3 : ℝ) := by
      simpa [show (4 * m : ℝ) = (4 : ℝ) * (m : ℝ) by norm_num] using
        (Real.mul_rpow (x := (4 : ℝ)) (y := (m : ℝ)) (z := (8 / 3 : ℝ))
          (by positivity : 0 ≤ (4 : ℝ)) hm_nonneg)
    rw [hmul]
    field_simp [hrpow4_pos.ne', (Real.rpow_pos_of_pos hm_pos (8 / 3 : ℝ)).ne']
  have hnum_compare :
      4 * ((L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) ≤
        (((2 : ℝ) ^ (8 : ℕ)) / Real.rpow (4 : ℝ) (8 / 3 : ℝ)) *
          ((L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
    -- Inflate the simplified constant from `4` to the displayed explicit constant.
    exact mul_le_mul_of_nonneg_right hconst (by positivity)
  calc
    Real.rpow
        ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
        (2 / 3 : ℝ) =
        (4 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          Real.rpow
            ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2))
            (2 / 3 : ℝ) := hmainRewrite
    _ ≤
        (4 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          Real.rpow ((m : ℝ) ^ (4 : ℕ)) (2 / 3 : ℝ) := hboundToM
    _ =
        (4 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          Real.rpow (m : ℝ) (8 / 3 : ℝ) := by
      rw [hm_collapse]
    _ ≤
        ((((2 : ℝ) ^ (8 : ℕ)) / Real.rpow (4 : ℝ) (8 / 3 : ℝ)) *
            (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          Real.rpow (m : ℝ) (8 / 3 : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (div_le_div_of_nonneg_right hnum_compare (Real.rpow_nonneg hm_nonneg _))
    _ =
        ((2 : ℝ) ^ (8 : ℕ) * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          Real.rpow (4 * m : ℝ) (8 / 3 : ℝ) := by
      rw [htargetFactor]

-- Proof sketch: apply `acceleratedCubicNewton_minGradientNorm_le_intermediate_bound`, then use
-- `(3m + 1) (3m + 2) > 9 m²` to simplify the denominator and rewrite the result in terms of
-- `(4m)^(8/3)`.
/-- Text 4 2 19: let `f` have third-order Lipschitz constant `L₃`, let `xStar` be a minimizer,
let `R₀ = ‖x₀ - xStar‖`, and let `x` be an iterate sequence satisfying the two displayed
inequalities at `x_{3m}` and `x_{4m}`. If for some `m ≥ 1` one has the objective-gap bound at
`x_{3m}` and the descent lower bound from `x_{3m}` to `x_{4m}` involving the sampled minimum
`g⋆[m] = min_{1 ≤ k ≤ 4m} ‖∇ f (x k)‖`, then, provided
`0 < (L3 : ℝ)` and `f xStar ≤ f (x (4 * m))` (for instance because `xStar` is a global
minimizer for the iterates under consideration), one gets
`g⋆[m] ≤ 2^8 L₃ R₀² / (4m)^(8/3)`. -/
theorem acceleratedCubicNewton_minGradientNorm_lt_explicit_rate
    (hL3 : 0 < (L3 : ℝ))
    (hxStar4m : f xStar ≤ f (x (4 * m)))
    (hgap :
      f (x (3 * m)) - f xStar ≤
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((3 * m : ℝ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
    (hdrop :
      f (x (3 * m)) - f (x (4 * m)) ≥
          ((m : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[m] (3 / 2 : ℝ)) :
    g⋆[m] ≤
      ((2 : ℝ) ^ (8 : ℕ) * (L3 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        Real.rpow (4 * m : ℝ) (8 / 3 : ℝ) := by
  have hintermediate :
      g⋆[m] ≤
        Real.rpow
          ((8 * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
            ((m : ℝ) ^ (2 : ℕ) * ((3 * m : ℝ) + 1) * ((3 * m : ℝ) + 2)))
          (2 / 3 : ℝ) :=
    acceleratedCubicNewton_minGradientNorm_le_intermediate_bound
      (f := f) (x := x) (x0 := x0) (xStar := xStar) (m := m) hm
      hL3 hxStar4m hgap hdrop
  -- Chain the intermediate theorem with the scalar comparison helper.
  exact hintermediate.trans <|
    intermediateBoundLeExplicitRate
      (L3 := L3) (x0 := x0) (xStar := xStar) (m := m) hm hL3

end AcceleratedCubicNewtonGradientNormBound
