/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient MinGradientNormAlongIterates

noncomputable section

universe u

/- Text 4.2.18 lies in the chapter finite-window best-gradient domain for accelerated
cubic-Newton iterates.

Sampled owner declarations:
* `minGradientNormAlongIterates` in `Chap02/Definition_2_23`, the core owner for the sampled
  minimum gradient norm over a finite iterate window;
* the source-facing notation `g[f; x; k, T | h]` for that owner, also in
  `Chap02/Definition_2_23`;
* `cubicNewton_gap_le_inverse_square_rate_of_bounded_sublevel` in `Theorem_4_2_2`, the nearby
  chapter rate theorem whose radius parameter is already owned canonically as a nonnegative
  constant;
* `false_acceleration_gap_le_inverse_eighth_rate` in `Text_4_2_17`, the neighboring scalar-rate
  theorem that likewise records its radius data with `R : NNReal`;
* `minGradientNormAlongIterates.le`, the canonical pointwise upper-bound API for the same owner;
* `acceleratedCubicNewton_minGradientNorm_le_intermediate_bound` and
  `acceleratedCubicNewton_minGradientNorm_lt_explicit_rate` in `Text_4_2_19`, the later
  accelerated-cubic-Newton rate statements using the same owner notation with `T = 4m`.

Source/core/bridge triage:
* source-facing: Text 4.2.18's sampled minimum gradient norm `g_T^*` for the first `T` iterates;
* core/canonical: `minGradientNormAlongIterates f x 1 T h`;
* bridge/view: the chapter owner notation `g[f; x; 1, T | h]`, with no extra local wrapper.

Primitive data:
* the objective `f`, the iterate sequence `x`, and the comparison point `xStar`;
* the chapter-standard Hessian-Lipschitz owner parameter `L3 : NNReal`, the chapter-standard
  nonnegative radius owner `D : NNReal`, and the source-required positivity hypothesis
  `0 < (L3 : ℝ)`;
* the fixed-start window witness `1 ≤ T`, and for the explicit-rate specialization only the index
  relation `T = 3m + 2`;
* the two displayed inequalities controlling the gap at `x_{2m}` and the drop from `x_{2m}` to
  `x_T`, both kept as explicit theorem binders rather than ambient section assumptions;
* the single comparison `f xStar ≤ f (x T)` used to pass from the gap at `x_{2m}` relative to
  `xStar` to the drop from `x_{2m}` to `x_T`.

Derived API:
* the intermediate and explicit rate bounds proved below.

Accordingly, this file keeps the source-facing textbook bound but replaces the duplicate scalar
placeholder `gT` by the chapter owner `minGradientNormAlongIterates`, hides the auxiliary witness
`1 ≤ T` behind local source-facing notation for the fixed-start sampled minimum, records the radius
with the chapter-standard nonnegative owner `D : NNReal`, and states the objective gaps directly as
evaluations of `f` on the iterates instead of as separate primitive scalar variables.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section AcceleratedCubicNewtonGradientNormBound

variable {f : E → ℝ} {x : ℕ → E} {xStar : E}
variable {m T : ℕ}
variable {L3 : NNReal} {D : NNReal}

section FixedStartWindow

variable (h1T : 1 ≤ T)

local notation "g⋆[" T "]" => g[f; x; 1, T | h1T]

/-- Helper for Text 4 2 18: the sampled minimum over the fixed-start window is nonnegative because
it is attained by a gradient norm. -/
lemma sampled_min_nonneg :
    0 ≤ g⋆[T] := by
  -- Realize the sampled minimum as one gradient norm in the window.
  rcases minGradientNormAlongIterates.exists_eq f x h1T with ⟨i, -, -, hi_eq⟩
  rw [hi_eq]
  exact norm_nonneg _

/-- Helper for Text 4 2 18: for a positive Hessian-Lipschitz constant, the `3 / 2` real power of
`L₃` splits into the linear factor times the square root factor. -/
lemma l3_rpow_three_halves_eq_mul_sqrt
    (hL3 : 0 < (L3 : ℝ)) :
    Real.rpow (L3 : ℝ) (3 / 2 : ℝ) = (L3 : ℝ) * Real.sqrt (L3 : ℝ) := by
  -- Rewrite `3 / 2` as `1 + 1 / 2` so that the square-root factor appears explicitly.
  calc
    Real.rpow (L3 : ℝ) (3 / 2 : ℝ) = Real.rpow (L3 : ℝ) ((1 : ℝ) + 1 / 2) := by norm_num
    _ = Real.rpow (L3 : ℝ) (1 : ℝ) * Real.rpow (L3 : ℝ) (1 / 2 : ℝ) := by
      simpa using Real.rpow_add hL3 (1 : ℝ) (1 / 2 : ℝ)
    _ = (L3 : ℝ) * Real.rpow (L3 : ℝ) (1 / 2 : ℝ) := by
      simp [Real.rpow_one]
    _ = (L3 : ℝ) * Real.sqrt (L3 : ℝ) := by
      simp [Real.sqrt_eq_rpow]

/-- Helper for Text 4 2 18: combining the displayed even-index gap estimate with the terminal drop
bound yields the intermediate `3 / 2`-power inequality for the sampled minimum. -/
lemma sampled_min_rpow_three_halves_le_intermediate_rate
    (hL3 : 0 < (L3 : ℝ))
    (hxStarT : f xStar ≤ f (x T))
    (heven_gap :
      f (x (2 * m)) - f xStar ≤
        (9 * (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (2 : ℕ)))
    (hterminal_drop :
      f (x (2 * m)) - f (x T) ≥
        ((m + 2 : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[T] (3 / 2 : ℝ)) :
    Real.rpow g⋆[T] (3 / 2 : ℝ) ≤
      ((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
        (4 * (m + 2 : ℝ) ^ (3 : ℕ)) := by
  have hL3_nonneg : 0 ≤ (L3 : ℝ) := by exact_mod_cast L3.2
  have hsqrt_pos : 0 < Real.sqrt (L3 : ℝ) := Real.sqrt_pos.2 hL3
  have hcoeff_pos : 0 < ((m + 2 : ℝ) / (3 * Real.sqrt (L3 : ℝ))) := by
    positivity
  have hupper_gap :
      f (x (2 * m)) - f (x T) ≤
        (9 * (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (2 : ℕ)) := by
    -- Compare the terminal value to `xStar`, then insert the displayed even-index gap bound.
    linarith
  have hdescent_le :
      ((m + 2 : ℝ) / (3 * Real.sqrt (L3 : ℝ))) * Real.rpow g⋆[T] (3 / 2 : ℝ) ≤
        (9 * (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (2 : ℕ)) :=
    hterminal_drop.trans hupper_gap
  have hdiv :
      Real.rpow g⋆[T] (3 / 2 : ℝ) ≤
        ((9 * (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (2 : ℕ))) /
          (((m + 2 : ℝ) / (3 * Real.sqrt (L3 : ℝ)))) := by
    -- Divide by the positive descent coefficient.
    refine (le_div_iff₀ hcoeff_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdescent_le
  have hquotient :
      ((9 * (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (2 : ℕ))) /
          (((m + 2 : ℝ) / (3 * Real.sqrt (L3 : ℝ)))) =
        ((27 : ℝ) * (L3 : ℝ) * Real.sqrt (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
          (4 * (m + 2 : ℝ) ^ (3 : ℕ)) := by
    field_simp [hsqrt_pos.ne', show ((m + 2 : ℝ)) ≠ 0 by positivity]
    ring
  -- Normalize the quotient and then package `L₃ * sqrt L₃` back into `L₃^(3 / 2)`.
  rw [hquotient] at hdiv
  calc
    Real.rpow g⋆[T] (3 / 2 : ℝ) ≤
        ((27 : ℝ) * (L3 : ℝ) * Real.sqrt (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
          (4 * (m + 2 : ℝ) ^ (3 : ℕ)) := hdiv
    _ =
        ((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
          (4 * (m + 2 : ℝ) ^ (3 : ℕ)) := by
      have hrewrite :
          ((27 : ℝ) * (L3 : ℝ) * Real.sqrt (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
              (4 * (m + 2 : ℝ) ^ (3 : ℕ)) =
            ((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
              (4 * (m + 2 : ℝ) ^ (3 : ℕ)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          congrArg
            (fun t : ℝ ↦
              ((27 : ℝ) * t * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
            (l3_rpow_three_halves_eq_mul_sqrt (L3 := L3) hL3).symm
      exact hrewrite

-- Proof sketch: combine the upper bound on `f (x (2 * m)) - f xStar` with the lower bound on
-- `f (x (2 * m)) - f (x T)` and the direct comparison `f xStar ≤ f (x T)`. This yields an upper
-- bound on `Real.rpow g⋆[T] (3 / 2)`, after which one raises both sides to the
-- power `2 / 3`.
/-- The two displayed estimates preceding Text 4.2.18 imply the intermediate bound
`g_T^* ≤ ((27 L₃^(3/2) D^3) / (4 (m + 2)^3))^(2/3)` for the fixed-start sampled minimum
`g_T^* = g⋆[T] = min_{1 ≤ k ≤ T} ‖∇ f (x k)‖`, where `D` is recorded as a
nonnegative radius constant. -/
theorem accelerated_cubic_newton_min_gradient_norm_le_intermediate_bound
    (hL3 : 0 < (L3 : ℝ))
    (hxStarT : f xStar ≤ f (x T))
    (heven_gap :
      f (x (2 * m)) - f xStar ≤
        (9 * (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (2 : ℕ)))
    (hterminal_drop :
      f (x (2 * m)) - f (x T) ≥
        ((m + 2 : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[T] (3 / 2 : ℝ))
    :
    g⋆[T] ≤
      Real.rpow
        (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
          (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
        (2 / 3 : ℝ) := by
  have hg_nonneg : 0 ≤ g⋆[T] := sampled_min_nonneg (f := f) (x := x) (T := T) h1T
  have hrpow_bound :
      Real.rpow g⋆[T] (3 / 2 : ℝ) ≤
        ((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
          (4 * (m + 2 : ℝ) ^ (3 : ℕ)) :=
    sampled_min_rpow_three_halves_le_intermediate_rate
      (f := f) (x := x) (xStar := xStar) (m := m) (T := T) (L3 := L3) (D := D) h1T
      hL3 hxStarT heven_gap hterminal_drop
  have hraised :
      Real.rpow (Real.rpow g⋆[T] (3 / 2 : ℝ)) (2 / 3 : ℝ) ≤
        Real.rpow
          (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
            (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
          (2 / 3 : ℝ) := by
    -- Raise the already-proved `3 / 2`-power inequality to the reciprocal exponent `2 / 3`.
    exact Real.rpow_le_rpow (Real.rpow_nonneg hg_nonneg _) hrpow_bound (by norm_num)
  calc
    g⋆[T] = Real.rpow g⋆[T] (1 : ℝ) := by
      simp
    _ = Real.rpow (Real.rpow g⋆[T] (3 / 2 : ℝ)) (2 / 3 : ℝ) := by
      -- Collapse the reciprocal exponents to recover the sampled minimum itself.
      simpa [show ((3 / 2 : ℝ) * (2 / 3 : ℝ)) = 1 by norm_num] using
        (Real.rpow_mul hg_nonneg (3 / 2 : ℝ) (2 / 3 : ℝ))
    _ ≤
        Real.rpow
          (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
            (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
          (2 / 3 : ℝ) := hraised

end FixedStartWindow

section FixedStartWindowExplicit

variable (hT : T = 3 * m + 2)

local notation "g⋆[" T "]" => g[f; x; 1, T | by omega]

/-- Helper for Text 4 2 18: when `T = 3m + 2`, the intermediate scalar bound simplifies to the
displayed inverse-square rate in `T + 4`. -/
lemma explicit_rate_rewrite_of_T_eq_three_mul_add_two
    (hT_eq : T = 3 * m + 2) :
    Real.rpow
        (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
          (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
        (2 / 3 : ℝ) =
      ((3 : ℝ) ^ (4 : ℕ) * (L3 : ℝ) * (D : ℝ) ^ (2 : ℕ)) /
        (Real.rpow 2 (4 / 3 : ℝ) * (T + 4 : ℝ) ^ (2 : ℕ)) := by
  have hL3_nonneg : 0 ≤ (L3 : ℝ) := by exact_mod_cast L3.2
  have hD_nonneg : 0 ≤ (D : ℝ) := by exact_mod_cast D.2
  have hm2_nonneg : 0 ≤ (m + 2 : ℝ) := by positivity
  have hL3_rpow_nonneg : 0 ≤ Real.rpow (L3 : ℝ) (3 / 2 : ℝ) :=
    Real.rpow_nonneg hL3_nonneg _
  have hnum_first :
      Real.rpow
          (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) * (D : ℝ) ^ (3 : ℕ))
          (2 / 3 : ℝ) =
        Real.rpow ((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) *
          Real.rpow ((D : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ) := by
    simpa using
      (Real.mul_rpow
        (x := (27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ))
        (y := (D : ℝ) ^ (3 : ℕ))
        (z := (2 / 3 : ℝ))
        (by positivity)
        (by positivity))
  have hnum_second :
      Real.rpow ((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) =
        Real.rpow (27 : ℝ) (2 / 3 : ℝ) *
          Real.rpow (Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) := by
    simpa using
      (Real.mul_rpow
        (x := (27 : ℝ))
        (y := Real.rpow (L3 : ℝ) (3 / 2 : ℝ))
        (z := (2 / 3 : ℝ))
        (by positivity)
        hL3_rpow_nonneg)
  have hnum :
      Real.rpow
          ((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ))
          (2 / 3 : ℝ) =
        Real.rpow (27 : ℝ) (2 / 3 : ℝ) *
          Real.rpow (Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) *
          Real.rpow ((D : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ) := by
    -- Split the numerator into three nonnegative factors before simplifying each exponent.
    rw [show ((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) =
        (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) * (D : ℝ) ^ (3 : ℕ)) by ring]
    rw [hnum_first, hnum_second]
  have hden :
      Real.rpow (4 * (m + 2 : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ) =
        Real.rpow 4 (2 / 3 : ℝ) *
          Real.rpow ((m + 2 : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ) := by
    -- Split the denominator into the constant factor and the cubic window length.
    simpa using
      (Real.mul_rpow
        (x := (4 : ℝ))
        (y := (m + 2 : ℝ) ^ (3 : ℕ))
        (z := (2 / 3 : ℝ))
        (by positivity)
        (by positivity))
  have h27 :
      Real.rpow (27 : ℝ) (2 / 3 : ℝ) = 9 := by
    have h27pow : (27 : ℝ) = Real.rpow (3 : ℝ) (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
    calc
      Real.rpow (27 : ℝ) (2 / 3 : ℝ) =
          Real.rpow (Real.rpow (3 : ℝ) (3 : ℝ)) (2 / 3 : ℝ) := by
        rw [h27pow]
      _ = Real.rpow (3 : ℝ) ((3 : ℝ) * (2 / 3 : ℝ)) := by
        simpa using (Real.rpow_mul (by positivity : 0 ≤ (3 : ℝ)) (3 : ℝ) (2 / 3 : ℝ)).symm
      _ = 9 := by
        norm_num [Real.rpow_natCast]
  have hL3_collapse :
      Real.rpow (Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) = (L3 : ℝ) := by
    calc
      Real.rpow (Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) =
          Real.rpow (L3 : ℝ) ((3 / 2 : ℝ) * (2 / 3 : ℝ)) := by
        simpa using (Real.rpow_mul hL3_nonneg (3 / 2 : ℝ) (2 / 3 : ℝ)).symm
      _ = (L3 : ℝ) := by
        norm_num [Real.rpow_one]
  have hD_collapse :
      Real.rpow ((D : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ) = (D : ℝ) ^ (2 : ℕ) := by
    have hDpow : (D : ℝ) ^ (3 : ℕ) = Real.rpow (D : ℝ) (3 : ℝ) := by
      simp
    calc
      Real.rpow ((D : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ) =
          Real.rpow (Real.rpow (D : ℝ) (3 : ℝ)) (2 / 3 : ℝ) := by
        rw [hDpow]
      _ = Real.rpow (D : ℝ) ((3 : ℝ) * (2 / 3 : ℝ)) := by
        simpa using (Real.rpow_mul hD_nonneg (3 : ℝ) (2 / 3 : ℝ)).symm
      _ = (D : ℝ) ^ (2 : ℕ) := by
        norm_num [Real.rpow_natCast]
  have h4 :
      Real.rpow 4 (2 / 3 : ℝ) = Real.rpow 2 (4 / 3 : ℝ) := by
    have h4pow : (4 : ℝ) = Real.rpow (2 : ℝ) (2 : ℝ) := by
      norm_num [Real.rpow_natCast]
    calc
      Real.rpow 4 (2 / 3 : ℝ) = Real.rpow (Real.rpow 2 (2 : ℝ)) (2 / 3 : ℝ) := by
        rw [h4pow]
      _ = Real.rpow 2 ((2 : ℝ) * (2 / 3 : ℝ)) := by
        simpa using (Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ)) (2 : ℝ) (2 / 3 : ℝ)).symm
      _ = Real.rpow 2 (4 / 3 : ℝ) := by norm_num
  have hm2_collapse :
      Real.rpow ((m + 2 : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ) = (m + 2 : ℝ) ^ (2 : ℕ) := by
    have hm2pow : (m + 2 : ℝ) ^ (3 : ℕ) = Real.rpow (m + 2 : ℝ) (3 : ℝ) := by
      simp
    calc
      Real.rpow ((m + 2 : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ) =
          Real.rpow (Real.rpow (m + 2 : ℝ) (3 : ℝ)) (2 / 3 : ℝ) := by
        rw [hm2pow]
      _ = Real.rpow (m + 2 : ℝ) ((3 : ℝ) * (2 / 3 : ℝ)) := by
        simpa using (Real.rpow_mul hm2_nonneg (3 : ℝ) (2 / 3 : ℝ)).symm
      _ = (m + 2 : ℝ) ^ (2 : ℕ) := by
        norm_num [Real.rpow_natCast]
  have hmain_rewrite :
      Real.rpow
          (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
            (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
          (2 / 3 : ℝ) =
        (9 * (L3 : ℝ) * (D : ℝ) ^ (2 : ℕ)) /
          (Real.rpow 2 (4 / 3 : ℝ) * (m + 2 : ℝ) ^ (2 : ℕ)) := by
    -- Route correction: expose the quotient first, then simplify each `rpow` factor separately.
    calc
      Real.rpow
          (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
            (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
          (2 / 3 : ℝ) =
          Real.rpow
              ((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ))
              (2 / 3 : ℝ) /
            Real.rpow (4 * (m + 2 : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ) := by
        simpa using
            (Real.div_rpow
            (x := (27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ))
            (y := 4 * (m + 2 : ℝ) ^ (3 : ℕ))
            (z := (2 / 3 : ℝ))
            (by positivity)
            (by positivity))
      _ =
          (Real.rpow (27 : ℝ) (2 / 3 : ℝ) *
              Real.rpow (Real.rpow (L3 : ℝ) (3 / 2 : ℝ)) (2 / 3 : ℝ) *
              Real.rpow ((D : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ)) /
            (Real.rpow 4 (2 / 3 : ℝ) *
              Real.rpow ((m + 2 : ℝ) ^ (3 : ℕ)) (2 / 3 : ℝ)) := by
        rw [hnum, hden]
      _ =
          (9 * (L3 : ℝ) * (D : ℝ) ^ (2 : ℕ)) /
            (Real.rpow 2 (4 / 3 : ℝ) * (m + 2 : ℝ) ^ (2 : ℕ)) := by
        rw [h27, hL3_collapse, hD_collapse, h4, hm2_collapse]
  have hT_real : (T : ℝ) = 3 * (m : ℝ) + 2 := by
    exact_mod_cast hT_eq
  have hT_shift : (T + 4 : ℝ) = 3 * (m + 2 : ℝ) := by
    -- Rewrite the explicit time parameter in terms of `m + 2`.
    calc
      (T + 4 : ℝ) = (T : ℝ) + 4 := by norm_num
      _ = (3 * (m : ℝ) + 2) + 4 := by rw [hT_real]
      _ = 3 * (m + 2 : ℝ) := by ring
  have hwindow_square : (T + 4 : ℝ) ^ (2 : ℕ) = (3 : ℝ) ^ (2 : ℕ) * (m + 2 : ℝ) ^ (2 : ℕ) := by
    rw [hT_shift, mul_pow]
  calc
    Real.rpow
        (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
          (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
        (2 / 3 : ℝ) =
        (9 * (L3 : ℝ) * (D : ℝ) ^ (2 : ℕ)) /
          (Real.rpow 2 (4 / 3 : ℝ) * (m + 2 : ℝ) ^ (2 : ℕ)) := hmain_rewrite
    _ = ((3 : ℝ) ^ (4 : ℕ) * (L3 : ℝ) * (D : ℝ) ^ (2 : ℕ)) /
          (Real.rpow 2 (4 / 3 : ℝ) * (T + 4 : ℝ) ^ (2 : ℕ)) := by
      rw [hwindow_square]
      field_simp [show Real.rpow 2 (4 / 3 : ℝ) ≠ 0 by
        exact (Real.rpow_pos_of_pos (by positivity : 0 < (2 : ℝ)) (4 / 3 : ℝ)).ne',
        show ((m + 2 : ℝ)) ≠ 0 by positivity]
      ring

/-- Helper for Text 4 2 18: once the specialization `T = 3m + 2` is available explicitly, the
intermediate theorem closes the textbook inverse-square rate bound. -/
theorem accelerated_cubic_newton_min_gradient_norm_le_explicit_rate_of_T_eq_three_mul_add_two
    (hT_eq : T = 3 * m + 2)
    (hL3 : 0 < (L3 : ℝ))
    (hxStarT : f xStar ≤ f (x T))
    (heven_gap :
      f (x (2 * m)) - f xStar ≤
        (9 * (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (2 : ℕ)))
    (hterminal_drop :
      f (x (2 * m)) - f (x T) ≥
        ((m + 2 : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[T] (3 / 2 : ℝ))
    :
    g⋆[T] ≤
      ((3 : ℝ) ^ (4 : ℕ) * (L3 : ℝ) * (D : ℝ) ^ (2 : ℕ)) /
        (Real.rpow 2 (4 / 3 : ℝ) * (T + 4 : ℝ) ^ (2 : ℕ)) := by
  have hintermediate :
      g⋆[T] ≤
        Real.rpow
          (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
            (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
          (2 / 3 : ℝ) :=
    accelerated_cubic_newton_min_gradient_norm_le_intermediate_bound
      (f := f) (x := x) (xStar := xStar) (m := m) (T := T) (L3 := L3) (D := D)
      (h1T := by omega) hL3 hxStarT heven_gap hterminal_drop
  -- Finish by substituting the specialized relation between `T` and `m`.
  calc
    g⋆[T] ≤
        Real.rpow
          (((27 : ℝ) * Real.rpow (L3 : ℝ) (3 / 2 : ℝ) * (D : ℝ) ^ (3 : ℕ)) /
            (4 * (m + 2 : ℝ) ^ (3 : ℕ)))
          (2 / 3 : ℝ) := hintermediate
    _ =
        ((3 : ℝ) ^ (4 : ℕ) * (L3 : ℝ) * (D : ℝ) ^ (2 : ℕ)) /
          (Real.rpow 2 (4 / 3 : ℝ) * (T + 4 : ℝ) ^ (2 : ℕ)) :=
        explicit_rate_rewrite_of_T_eq_three_mul_add_two
          (m := m) (T := T) (L3 := L3) (D := D) hT_eq

-- Proof sketch: apply
-- `accelerated_cubic_newton_min_gradient_norm_le_intermediate_bound`, then substitute
-- `m + 2 = (T + 4) / 3` from `T = 3m + 2` and simplify the resulting powers of `3`, `2`, and
-- `(D : ℝ)`.
/-- Text 4 2 18: if the accelerated cubic-Newton iterates satisfy
`f(x_{2m}) - f(xStar) ≤ 9 L₃ D^3 / (4 (m + 2)^2)` and
`f(x_{2m}) - f(x_T) ≥ ((m + 2) / (3 √L₃)) (g_T^*)^(3/2)` with `T = 3m + 2`, then the fixed-start
sampled minimum gradient norm
`g_T^* = g⋆[T] = min_{1 ≤ k ≤ T} ‖∇ f (x k)‖` satisfies the explicit inverse-square bound
`g_T^* ≤ 3^4 L₃ D^2 / (2^(4/3) (T + 4)^2)` provided `L₃ > 0` and `f xStar ≤ f (x_T)`, for
instance when `xStar` is a global minimizer. -/
theorem accelerated_cubic_newton_min_gradient_norm_le_explicit_rate
    (hL3 : 0 < (L3 : ℝ))
    (hxStarT : f xStar ≤ f (x T))
    (heven_gap :
      f (x (2 * m)) - f xStar ≤
        (9 * (L3 : ℝ) * (D : ℝ) ^ (3 : ℕ)) / (4 * (m + 2 : ℝ) ^ (2 : ℕ)))
    (hterminal_drop :
      f (x (2 * m)) - f (x T) ≥
        ((m + 2 : ℝ) / (3 * Real.sqrt (L3 : ℝ))) *
          Real.rpow g⋆[T] (3 / 2 : ℝ))
    :
    g⋆[T] ≤
      ((3 : ℝ) ^ (4 : ℕ) * (L3 : ℝ) * (D : ℝ) ^ (2 : ℕ)) /
        (Real.rpow 2 (4 / 3 : ℝ) * (T + 4 : ℝ) ^ (2 : ℕ)) := by
  -- Route correction: the section already carries the specialization witness `hT`, so the final
  -- theorem is just the wrapper around the specialized explicit-rate bound proved above.
  have hT_eq : T = 3 * m + 2 := hT
  -- Reuse the specialized theorem verbatim and forward the four displayed hypotheses unchanged.
  simpa using
    accelerated_cubic_newton_min_gradient_norm_le_explicit_rate_of_T_eq_three_mul_add_two
      (f := f) (x := x) (xStar := xStar) (m := m) (T := T) (L3 := L3) (D := D) (hT := hT)
      hT_eq hL3 hxStarT heven_gap hterminal_drop

end FixedStartWindowExplicit

end AcceleratedCubicNewtonGradientNormBound
