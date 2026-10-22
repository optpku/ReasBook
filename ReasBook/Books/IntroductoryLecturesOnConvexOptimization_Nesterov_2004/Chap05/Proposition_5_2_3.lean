/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Proposition 5.2.3 lies in the Chapter 5 strongly-convex quadratic-regime entry-time domain on
real normed spaces.

Primary mathematical domain:
* strongly convex objectives together with the canonical strong-convexity specialization of the
  Chapter 4 global rate estimate, and the resulting Chapter 5 quadratic region
  `𝒬[f | f(x*), M_f]`

Sampled owner-style declarations:
* `selfConcordantQuadraticRegion` and the notation `𝒬[f | f*, M_f]` in `Definition_5_2_9`, the
  Chapter 5 source-facing quadratic-region owner;
* `strongConvexSelfConcordanceConstant` in `Definition_5_2_8`, the chapter owner for the
  canonical strong-convexity-induced self-concordance constant
  `M_f = L₃ / (2 σ₂^(3 / 2))`;
* `mem_selfConcordantQuadraticRegion_iff_mem_cubicNewtonQuadraticDecreaseRegion` in
  `Definition_5_2_9`, the canonical bridge to the older Chapter 4 comparison region;
* `cubicNewton_gap_le_inverse_square_rate_of_bounded_sublevel` in `Chap04/Theorem_4_2_2`, the
  nearby chapter theorem whose strong-convexity specialization produces the canonical
  coefficient `2^(5/2) c M_f (f(x₀) - f(x*))^(3/2) / k^p`;
* `StrongConvexOn.quadratic_growth_of_isMinOn` in `Chap02/Theorem_2_30`, the canonical
  quadratic-growth owner behind that specialization;
* `stronglyConvexHalfGapIndex` in `Definition_5_2_10`, the downstream owner showing that the
  natural strong-convexity scaling parameter is `Δ = M_f * √gap`, not a local wrapper.

Best owner abstraction:
* source-facing: the first index where the iterate enters the Chapter 5 region
  `𝒬[f | f(x*), M_f]`;
* core/canonical: the Chapter 5 region owner together with the canonical strong-convexity
  specialization of the Chapter 4 inverse-square rate;
* bridge/view: the comparison between the Chapter 5 threshold `1 / (8 M_f^2)`, the Chapter 4
  multiplication-form region `cubicNewtonQuadraticDecreaseRegion`, and the scaled gap
  `Δ = M_f * √gap`.

Primitive data:
* the strong-convexity parameter sign `0 < σ₂`;
* the iterate family `x`;
* the minimizer `x*` together with the canonical owner witness `IsMinOn f Set.univ x*`;
* the global-rate constants `c`, `p`;
* the canonical strong-convexity-specialized rate bound `hrate`;
* the least-entry witness `hN`.

Derived API:
* the Chapter 5 quadratic-region owner `𝒬[f | f(x*), M_f]`;
* the strong-convexity scaling `Δ M_f gap`.

This refinement keeps Proposition 5.2.3 source-facing while removing the noncanonical free radius
parameter `D`. The theorem surface now uses the canonical strong-convexity-specialized rate
coefficient that one obtains from the Chapter 4 inverse-square estimate via
`StrongConvexOn.quadratic_growth_of_isMinOn`, so the public statement no longer pretends that an
arbitrary bounded-sublevel witness is itself controlled by strong convexity. The entry condition
stays phrased directly with the Chapter 5 owner `𝒬[f | f(x*), M_f]` rather than the older
Chapter 4 comparison region. -/

/-- The strong-convex scaled gap `Δ = M_f * √gap` used in the textbook complexity estimate for
entering the quadratic-convergence region. In source-facing applications the gap is the
suboptimality `f(x) - f(x*)`, whose nonnegativity is supplied by `IsMinOn`. -/
def stronglyConvexScaledGap (Mf gap : ℝ) : ℝ :=
  Mf * Real.sqrt gap

/- Source-facing Lean notation for the textbook strongly-convex scaled gap owner `Δ`. -/
scoped[StronglyConvexScaledGap] notation:max "Δ" => stronglyConvexScaledGap

open scoped SelfConcordantQuadraticRegion StronglyConvexScaledGap

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

section

variable {σ2 : ℝ} {L3 : NNReal}

/-- Helper for Proposition 5.2.3: if `N` is the least index whose iterate lies in the Chapter 5
quadratic region, then the predecessor iterate is still outside that region. -/
lemma pred_not_mem_selfConcordantQuadraticRegion_of_isLeast
    {f : E → ℝ} {fStar : ℝ} {Mf : NNReal} {x : ℕ → E} {N : ℕ}
    (hNtwo : 2 ≤ N)
    (hN : IsLeast {n : ℕ | x n ∈ 𝒬[f | fStar, Mf]} N) :
    x (N - 1) ∉ 𝒬[f | fStar, Mf] := by
  -- The least-entry witness forbids membership at any smaller index, in particular at `N - 1`.
  intro hxpred
  have hpred_lt : N - 1 < N := Nat.sub_lt (lt_of_lt_of_le (by norm_num) hNtwo) (by norm_num)
  exact (not_lt_of_ge (hN.2 hxpred)) hpred_lt

/-- Helper for Proposition 5.2.3: being outside `𝒬[f | f*, M_f]` forces the function gap to lie
strictly above the Chapter 5 threshold `1 / (8 M_f^2)`. -/
lemma outside_selfConcordantQuadraticRegion_gap_lower_bound
    {f : E → ℝ} {fStar : ℝ} {Mf : NNReal} {xk : E}
    (hx : xk ∉ 𝒬[f | fStar, Mf]) :
    1 / (8 * (Mf : ℝ) ^ (2 : ℕ)) < f xk - fStar := by
  have hMf : 0 < Mf := Mf_pos_of_not_mem_selfConcordantQuadraticRegion hx
  -- Rewriting nonmembership through the positive-`M_f` threshold yields the strict lower bound.
  rw [mem_selfConcordantQuadraticRegion_iff_div hMf] at hx
  exact lt_of_not_ge hx

/-- Helper for Proposition 5.2.3: the strong-convex scaled gap `Δ M_f gap` is nonnegative when
both the scale and the gap are nonnegative. -/
lemma stronglyConvexScaledGap_nonneg
    {Mf gap : ℝ} (hMf : 0 ≤ Mf) (_hgap : 0 ≤ gap) :
    0 ≤ Δ Mf gap := by
  -- The source-facing scaled gap is the product of a nonnegative scale and a square root.
  rw [stronglyConvexScaledGap]
  exact mul_nonneg hMf (Real.sqrt_nonneg gap)

/-- Helper for Proposition 5.2.3: the coefficient obtained after clearing the Chapter 5 threshold
matches the source-facing scaled-gap cube `2^(11/2) c (Δ M_f gap)^3`. -/
lemma scaled_gap_cube_rewrite
    {Mf gap c : ℝ} (hgap : 0 ≤ gap) :
    (8 : ℝ) * Mf ^ (2 : ℕ) *
        (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * Mf * Real.rpow gap (3 / 2 : ℝ)) =
      Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c * (Δ Mf gap) ^ (3 : ℕ) := by
  -- Rewrite the fractional powers into square roots and collect the cubic scaled-gap factor.
  have hgap32 : Real.rpow gap (3 / 2 : ℝ) = gap * Real.sqrt gap := by
    calc
      Real.rpow gap (3 / 2 : ℝ) = Real.rpow gap ((1 : ℝ) + 1 / 2) := by norm_num
      _ = Real.rpow gap (1 : ℝ) * Real.rpow gap (1 / 2 : ℝ) := by
        simpa using
          (Real.rpow_add_of_nonneg hgap (show 0 ≤ (1 : ℝ) by positivity)
            (show 0 ≤ (1 / 2 : ℝ) by positivity))
      _ = gap * Real.sqrt gap := by
        simp [Real.sqrt_eq_rpow]
  have htwo :
      Real.rpow (2 : ℝ) (11 / 2 : ℝ) = (8 : ℝ) * Real.rpow (2 : ℝ) (5 / 2 : ℝ) := by
    calc
      Real.rpow (2 : ℝ) (11 / 2 : ℝ) = Real.rpow (2 : ℝ) ((5 / 2 : ℝ) + 3) := by norm_num
      _ = Real.rpow (2 : ℝ) (5 / 2 : ℝ) * Real.rpow (2 : ℝ) (3 : ℝ) := by
        simpa using
          (Real.rpow_add (show 0 < (2 : ℝ) by positivity) (5 / 2 : ℝ) (3 : ℝ))
      _ = Real.rpow (2 : ℝ) (5 / 2 : ℝ) * 8 := by norm_num
      _ = (8 : ℝ) * Real.rpow (2 : ℝ) (5 / 2 : ℝ) := by ring
  have hgap_cube : gap * Real.sqrt gap = (Real.sqrt gap) ^ (3 : ℕ) := by
    calc
      gap * Real.sqrt gap = (Real.sqrt gap) ^ (2 : ℕ) * Real.sqrt gap := by
        rw [show (Real.sqrt gap) ^ (2 : ℕ) = gap by simpa using Real.sq_sqrt hgap]
      _ = (Real.sqrt gap) ^ (3 : ℕ) := by ring
  -- Route correction: rewrite the left coefficient into a cubic square-root factor first, then
  -- collect it into `(Mf * √gap)^3`.
  calc
    (8 : ℝ) * Mf ^ (2 : ℕ) *
        (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * Mf * Real.rpow gap (3 / 2 : ℝ)) =
        (8 : ℝ) * Mf ^ (2 : ℕ) *
          (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * Mf * (Real.sqrt gap) ^ (3 : ℕ)) := by
      rw [hgap32, hgap_cube]
    _ = (8 : ℝ) * Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf * Real.sqrt gap) ^ (3 : ℕ) := by
      ring
    _ = Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c * (Δ Mf gap) ^ (3 : ℕ) := by
      rw [stronglyConvexScaledGap, htwo]

/-- Helper for Proposition 5.2.3: once the predecessor gap is above the Chapter 5 threshold while
still satisfying the source rate estimate, the predecessor index is bounded by the scaled-gap
root. -/
lemma pred_index_lt_scaled_gap_root_of_rate
    {c p Mf gap0 gapk : ℝ} {k : ℕ}
    (hc : 0 < c) (hp : 0 < p) (hMf : 0 < Mf) (hgap0 : 0 ≤ gap0) (hk : 0 < k)
    (hlower : 1 / (8 * Mf ^ (2 : ℕ)) < gapk)
    (hupper :
      gapk ≤
        (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * Mf * Real.rpow gap0 (3 / 2 : ℝ)) /
          Real.rpow (k : ℝ) p) :
    (k : ℝ) <
      Real.rpow
        (Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c * (Δ Mf gap0) ^ (3 : ℕ))
        (1 / p) := by
  let coeff : ℝ := (8 : ℝ) * Mf ^ (2 : ℕ)
  let numerator : ℝ :=
    Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * Mf * Real.rpow gap0 (3 / 2 : ℝ)
  have hcoeff_pos : 0 < coeff := by
    dsimp [coeff]
    positivity
  have hkpow_pos : 0 < Real.rpow (k : ℝ) p := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast hk) p
  have hscaled_lower : 1 < coeff * gapk := by
    -- Multiply the threshold lower bound by the positive coefficient `8 M_f^2`.
    have hlower' : 1 / coeff < gapk := by
      simpa [coeff] using hlower
    have hmultiplied : coeff * (1 / coeff) < coeff * gapk :=
      mul_lt_mul_of_pos_left hlower' hcoeff_pos
    simpa [one_div, hcoeff_pos.ne'] using hmultiplied
  have hscaled_upper : coeff * gapk ≤ coeff * (numerator / Real.rpow (k : ℝ) p) := by
    -- The source rate estimate is monotone under multiplication by the same positive coefficient.
    exact mul_le_mul_of_nonneg_left hupper hcoeff_pos.le
  have hdiv :
      1 < (coeff * numerator) / Real.rpow (k : ℝ) p := by
    have hcombined : 1 < coeff * (numerator / Real.rpow (k : ℝ) p) :=
      lt_of_lt_of_le hscaled_lower hscaled_upper
    simpa [coeff, numerator, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcombined
  have hkpow_lt :
      Real.rpow (k : ℝ) p <
        Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c * (Δ Mf gap0) ^ (3 : ℕ) := by
    -- Clearing the positive denominator isolates the scalar inequality on `k^p`.
    have hraw : Real.rpow (k : ℝ) p < coeff * numerator := by
      simpa [one_mul] using (lt_div_iff₀ hkpow_pos).1 hdiv
    have hcoeff_numerator :
        coeff * numerator =
          Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c * (Δ Mf gap0) ^ (3 : ℕ) := by
      dsimp [coeff, numerator]
      simpa [mul_assoc, mul_left_comm, mul_comm] using scaled_gap_cube_rewrite (Mf := Mf) (c := c) hgap0
    rwa [hcoeff_numerator] at hraw
  have hscaled_nonneg : 0 ≤ Δ Mf gap0 := by
    -- The scaled initial gap is nonnegative because both factors are nonnegative.
    exact stronglyConvexScaledGap_nonneg hMf.le hgap0
  have htwo_nonneg : 0 ≤ Real.rpow (2 : ℝ) (11 / 2 : ℝ) := by
    exact le_of_lt (Real.rpow_pos_of_pos (by positivity) (11 / 2 : ℝ))
  have htarget_nonneg :
      0 ≤ Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c * (Δ Mf gap0) ^ (3 : ℕ) := by
    -- The scalar root base is a product of three nonnegative factors.
    exact mul_nonneg (mul_nonneg htwo_nonneg hc.le) (pow_nonneg hscaled_nonneg 3)
  -- Apply the positive-exponent inverse-`rpow` equivalence to recover the bound on `k`.
  simpa [one_div] using
    (Real.lt_rpow_inv_iff_of_pos (show 0 ≤ (k : ℝ) by positivity) htarget_nonneg hp).2 hkpow_lt

-- Proof sketch: start from the canonical strong-convexity specialization of the Chapter 4 rate
-- bound,
-- `f(x_k) - f(x*) ≤ 2^(5/2) c M_f (f(x₀) - f(x*))^(3/2) / k^p`
-- with `M_f = L₃ / (2 * σ₂^(3 / 2))`, compare it to the defining threshold
-- `f(x) - f(x*) ≤ 1 / (8 M_f^2)` of `𝒬[f | f(x*), M_f]`, and choose the first positive integer
-- above the scalar root. Converting that natural-number rounding into a real inequality yields
-- the final `1 + ...` bound on the least entry index.
/-- Proposition 5.2.3: assume the iterate sequence `x_k` satisfies the global rate
`f(x_k) - f(x*) ≤ (2^(5/2) c M_f / k^p) * (f(x₀) - f(x*))^(3/2)`, where `x*` is a global
minimizer of `f`,
`M_f = L₃ / (2 * σ₂^(3 / 2))`, then `N` is bounded by the corresponding constant multiple of
`Δ_f(x₀)^(3 / p)`, with the natural-number rounding written as
`1 + (2^(11/2) c Δ_f(x₀)^3)^(1 / p)`. Here `N` is the least index for which `x_N` enters the
Chapter 5 quadratic region `𝒬[f | f(x*), M_f]`. Under `L₃ > 0`, the Chapter 5 threshold
`f(x_N) - f(x*) ≤ 1 / (8 M_f^2)` is equivalent to the older Chapter 4 comparison-region
condition `2 L₃² (f(x_N) - f(x*)) ≤ σ₂³`. -/
theorem stronglyConvex_firstSourceQuadraticConvergenceRegionEntryIndex_le
    {f : E → ℝ}
    (x : ℕ → E) (xStar : E) {c p : ℝ}
    (hσ2 : 0 < σ2)
    (hmin : IsMinOn f Set.univ xStar)
    (hc : 0 < c) (hp : 0 < p)
    (hrate :
      ∀ k : ℕ, 0 < k →
        f (x k) - f xStar ≤
          (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c *
            (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) *
            Real.rpow (f (x 0) - f xStar) (3 / 2 : ℝ)) /
            Real.rpow (k : ℝ) p)
    {N : ℕ}
    (hN :
      IsLeast
        {n : ℕ | x n ∈ 𝒬[f | f xStar, strongConvexSelfConcordanceConstant σ2 L3]}
        N) :
    (N : ℝ) ≤
      1 +
      Real.rpow
        (Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c *
          (Δ (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) (f (x 0) - f xStar)) ^ (3 : ℕ))
        (1 / p) := by
  have hgap0_nonneg : 0 ≤ f (x 0) - f xStar := by
    -- The minimizer witness turns the initial suboptimality into a nonnegative scalar gap.
    have hmin0 : f xStar ≤ f (x 0) := (isMinOn_univ_iff.mp hmin) (x 0)
    linarith
  have hscaled0_nonneg :
      0 ≤ Δ (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) (f (x 0) - f xStar) := by
    -- The strong-convexity scale is an `NNReal`, so its real coercion is nonnegative.
    exact stronglyConvexScaledGap_nonneg (by positivity) hgap0_nonneg
  have htwo_nonneg : 0 ≤ Real.rpow (2 : ℝ) (11 / 2 : ℝ) := by
    exact le_of_lt (Real.rpow_pos_of_pos (by positivity) (11 / 2 : ℝ))
  have hroot_base_nonneg :
      0 ≤
        Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c *
          (Δ (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) (f (x 0) - f xStar)) ^ (3 : ℕ) := by
    -- The final root base is built from a positive scalar, a positive constant, and a cube.
    exact mul_nonneg (mul_nonneg htwo_nonneg hc.le) (pow_nonneg hscaled0_nonneg 3)
  have hroot_nonneg :
      0 ≤
        Real.rpow
          (Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c *
            (Δ (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) (f (x 0) - f xStar)) ^ (3 : ℕ))
          (1 / p) := by
    apply Real.rpow_nonneg
    exact hroot_base_nonneg
  by_cases hNsmall : N ≤ 1
  · -- If the least entry time is already `0` or `1`, the target bound is immediate.
    calc
      (N : ℝ) ≤ 1 := by exact_mod_cast hNsmall
      _ ≤
          1 +
            Real.rpow
              (Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c *
                (Δ (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) (f (x 0) - f xStar)) ^
                  (3 : ℕ))
              (1 / p) := by
          linarith
  · have hNtwo : 2 ≤ N := by
      exact Nat.succ_le_of_lt (lt_of_not_ge hNsmall)
    have hNone : 1 ≤ N := le_trans (by norm_num) hNtwo
    have hkpos : 0 < N - 1 := by
      exact Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num) hNtwo)
    have hpred_not_mem :
        x (N - 1) ∉ 𝒬[f | f xStar, strongConvexSelfConcordanceConstant σ2 L3] :=
      pred_not_mem_selfConcordantQuadraticRegion_of_isLeast hNtwo hN
    have hMf_pos :
        0 < strongConvexSelfConcordanceConstant σ2 L3 :=
      Mf_pos_of_not_mem_selfConcordantQuadraticRegion hpred_not_mem
    have hlower :
        1 / (8 * (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) ^ (2 : ℕ)) <
          f (x (N - 1)) - f xStar :=
      outside_selfConcordantQuadraticRegion_gap_lower_bound hpred_not_mem
    have hpred_lt_root :
        (((N - 1 : ℕ) : ℝ)) <
          Real.rpow
            (Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c *
              (Δ (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) (f (x 0) - f xStar)) ^
                (3 : ℕ))
            (1 / p) :=
      pred_index_lt_scaled_gap_root_of_rate
        hc hp hMf_pos hgap0_nonneg hkpos hlower (hrate (N - 1) hkpos)
    -- The predecessor estimate closes the main branch after restoring `N = (N - 1) + 1`.
    calc
      (N : ℝ) = (((N - 1 : ℕ) + 1 : ℕ) : ℝ) := by
        -- Cast the natural identity `N = (N - 1) + 1` instead of rewriting a real subtraction.
        rw [Nat.sub_add_cancel hNone]
      _ = (((N - 1 : ℕ) : ℝ)) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      _ ≤
          Real.rpow
            (Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c *
              (Δ (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) (f (x 0) - f xStar)) ^
                (3 : ℕ))
            (1 / p) +
            1 := by
          linarith
      _ = 1 +
          Real.rpow
            (Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c *
              (Δ (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) (f (x 0) - f xStar)) ^
                (3 : ℕ))
            (1 / p) := by
          ring

end
