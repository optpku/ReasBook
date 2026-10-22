/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Primary domain:
* scalar one-step contraction factors and radius recurrences for locally optimal gradient steps

Relevant owner-style declarations sampled before refining:
* `IsMinOn` in mathlib, the canonical owner predicate for an attained minimizer of a real-valued
  function on a set
* `HasGeometricRateOfConvergence` and
  `HasGeometricRateOfConvergence.of_step_bound` in `Definition_1_2_6.lean`
* `gradientMethod_dist_le_optimal_geometric_rate` in `Chap02/Theorem_2_17.lean`, the later
  owner-style optimal constant-step result
* the schedule type `(ℕ → ℝ)` recalled in `Definition_1_6_2.lean`

Source/core/bridge triage:
* source-facing: the step-dependent coefficients `a_k(h)` and `b_k(h)`, the optimal-step
  minimizer condition, the strict radius invariance, and the displayed recurrences and bounds
* core/canonical: `IsMinOn` for `h_k^*` and `HasGeometricRateOfConvergence` for the transformed
  gap sequence
* bridge/view: the radius owner `localGradientRadius μ M = 2 * μ / M`, the scaled radius
  `a_k = (M / (L + μ)) r_k`, and the gap ratio `r_k / ((2 * μ / M) - r_k)`

Best owner abstraction:
* `IsMinOn` for the source minimizer `h_k^*`, paired with `HasGeometricRateOfConvergence` for the
  intrinsic gap-ratio sequence

Primitive data:
* the radius sequence `r`
* the step schedule `h`
* the parameters `μ`, `L`, and the positive radius/Lipschitz datum `M : NNRealˣ`
* the initial source bound `0 < r_0 < localGradientRadius μ M`
* nonnegativity of the radius sequence, from which positivity of later radii is derived under
  the optimal-step hypotheses
* the one-step estimate
  `r_{k+1} ≤ max { a_k(h_k), b_k(h_k) } * r_k`

Derived API:
* `h_k^* = 2 / (L + μ)`
* strict invariance `r_{k+1} < r_k < localGradientRadius μ M`
* positivity of every later radius, obtained from the initial positivity and nonnegativity data
* the explicit radius recurrence
* the scaled recurrence for `a_k = (M / (L + μ)) r_k`
* the owner geometric-rate statement for the gap ratio
* the displayed bounds `(1.2.31)` and `(1.2.32)`

This file keeps those textbook scalar expressions as local notation inside the theorem layer,
uses `IsMinOn` only for the source minimizer layer, and lets the downstream recurrence lemmas
consume the derived textbook identity `h_k = 2 / (L + μ)` rather than repeating the minimizer
witness. The bridge to `HasGeometricRateOfConvergence` remains public instead of a private
helper. The positive denominator datum is carried canonically by `M : NNRealˣ` and the owner
`localGradientRadius`, rather than being recovered only from side inequalities. -/

section

variable {r h : ℕ → ℝ} {μ L : ℝ} {M : NNRealˣ}

/-- The local radius `2 * μ / M` from Theorem 1.6.14, with positivity of `M` encoded in
`M : NNRealˣ`. -/
def localGradientRadius (μ : ℝ) (M : NNRealˣ) : ℝ :=
  2 * μ / (M : ℝ)

/-- Expanding `localGradientRadius μ M` gives the textbook radius `2 * μ / M`. -/
theorem localGradientRadius_def (μ : ℝ) (M : NNRealˣ) :
    localGradientRadius μ M = 2 * μ / (M : ℝ) :=
  rfl

local notation "radius" => localGradientRadius μ M
local notation "step" => (2 / (L + μ) : ℝ)
local notation "q" => (2 * μ / (L + μ) : ℝ)
local notation "positiveSteps" => Set.Ioi (0 : ℝ)
local notation "aCoeff" =>
  fun k hStep ↦ 1 - hStep * (μ - (M : ℝ) * r k / 2)
local notation "bCoeff" =>
  fun k hStep ↦ hStep * (L + (M : ℝ) * r k / 2) - 1
local notation "bound" =>
  fun k hStep ↦ max (aCoeff k hStep) (bCoeff k hStep)
local notation "scaled" => fun k ↦ ((M : ℝ) / (L + μ)) * r k
local notation "gap" => fun k ↦ r k / (radius - r k)

/-- Helper for Theorem 1.6.14: the two affine radius factors cross exactly at the textbook step
`2 / (L + μ)`. -/
lemma localGradient_aCoeff_eq_bCoeff_iff
    (hLμ : 0 < L + μ) {k : ℕ} {hStep : ℝ} :
    aCoeff k hStep = bCoeff k hStep ↔ hStep = step := by
  constructor
  · intro hEq
    -- The shared `M r_k / 2` terms cancel, leaving a scalar linear equation in `hStep`.
    have hmul : hStep * (L + μ) = 2 := by
      linarith
    apply (eq_div_iff hLμ.ne').2
    linarith
  · intro hStep_eq
    subst hStep
    -- Substituting the textbook step makes the two branches coincide.
    field_simp [hLμ.ne']
    ring_nf

/-- Helper for Theorem 1.6.14: evaluating the maximum branch at the textbook step gives the
common affine value `((L - μ) + M r_k) / (L + μ)`. -/
lemma localGradient_bound_at_step
    (hLμ : 0 < L + μ) (k : ℕ) :
    bound k step = ((L - μ) + (M : ℝ) * r k) / (L + μ) := by
  have hcross : aCoeff k step = bCoeff k step :=
    (localGradient_aCoeff_eq_bCoeff_iff (r := r) (μ := μ) (L := L) (M := M) hLμ).2 rfl
  -- At the crossing point the maximum collapses to either branch.
  change max (aCoeff k step) (bCoeff k step) = ((L - μ) + (M : ℝ) * r k) / (L + μ)
  rw [max_eq_left hcross.ge]
  field_simp [hLμ.ne']
  ring_nf

/-- If `0 ≤ r_k < 2 * μ / M` and `h_k^*` minimizes `max {a_k(h), b_k(h)}` over positive
step sizes, then `h_k^* = 2 / (L + μ)`. -/
theorem localGradientRadiusBound_optimalStep_eq
    (hμ : 0 < μ) (hμL : μ ≤ L)
    {k : ℕ} {hStar : ℝ}
    (hrk_nonneg : 0 ≤ r k) (hrk_lt : r k < radius)
    (hopt : IsMinOn (bound k) positiveSteps hStar) :
    hStar = step := by
  have hLμ : 0 < L + μ := by
    nlinarith [hμ, hμL]
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  have hslope_left : 0 < μ - (M : ℝ) * r k / 2 := by
    -- The source radius constraint makes the decreasing branch genuinely decreasing.
    unfold localGradientRadius at hrk_lt
    have hrk_mul : r k * (M : ℝ) < 2 * μ := by
      exact (lt_div_iff₀ hM).mp hrk_lt
    nlinarith [hrk_mul]
  have hstep_pos : 0 < step := by
    positivity
  have hcross : aCoeff k step = bCoeff k step :=
    (localGradient_aCoeff_eq_bCoeff_iff (r := r) (μ := μ) (L := L) (M := M) hLμ).2 rfl
  have hmin := isMinOn_iff.mp hopt
  have hstep_mem : step ∈ positiveSteps := by
    change 0 < step
    exact hstep_pos
  have hstep_le : bound k hStar ≤ bound k step := by
    exact hmin step hstep_mem
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hbranch_lt : bCoeff k hStar < aCoeff k hStar := by
      have : hStar * (L + μ) < 2 := by
        nlinarith [hlt, hLμ]
      linarith
    have hbound_star : bound k hStar = aCoeff k hStar := by
      change max (aCoeff k hStar) (bCoeff k hStar) = aCoeff k hStar
      rw [max_eq_left hbranch_lt.le]
    have hbound_step : bound k step = aCoeff k step := by
      change max (aCoeff k step) (bCoeff k step) = aCoeff k step
      rw [max_eq_left hcross.ge]
    have hbetter : aCoeff k step < aCoeff k hStar := by
      -- Left of the crossing, the maximum is the decreasing branch.
      nlinarith [hlt, hslope_left]
    have : bound k step < bound k hStar := by
      simpa [hbound_star, hbound_step] using hbetter
    exact not_lt_of_ge hstep_le this
  · have hbranch_gt : aCoeff k hStar < bCoeff k hStar := by
      have : 2 < hStar * (L + μ) := by
        nlinarith [hgt, hLμ]
      linarith
    have hbound_star : bound k hStar = bCoeff k hStar := by
      change max (aCoeff k hStar) (bCoeff k hStar) = bCoeff k hStar
      rw [max_eq_right hbranch_gt.le]
    have hbound_step : bound k step = bCoeff k step := by
      change max (aCoeff k step) (bCoeff k step) = bCoeff k step
      rw [max_eq_right hcross.le]
    have hbetter : bCoeff k step < bCoeff k hStar := by
      -- Right of the crossing, the maximum is the increasing branch.
      have hslope_right : 0 < L + (M : ℝ) * r k / 2 := by
        nlinarith [hμ, hμL, hrk_nonneg]
      nlinarith [hgt, hslope_right]
    have : bound k step < bound k hStar := by
      simpa [hbound_star, hbound_step] using hbetter
    exact not_lt_of_ge hstep_le this

/-- Helper for Theorem 1.6.14: once `r_k < 2 * μ / M`, the scaled variable
`a_k = (M / (L + μ)) r_k` lies below `q = 2 * μ / (L + μ)`. -/
lemma localGradient_scaled_lt_q_of_radius_lt
    (hμ : 0 < μ) (hμL : μ ≤ L)
    {k : ℕ} (hrk_lt : r k < radius) :
    scaled k < q := by
  have hLμ : 0 < L + μ := by
    nlinarith [hμ, hμL]
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  have hMr_lt : (M : ℝ) * r k < 2 * μ := by
    -- Clearing the positive denominator `M` converts the radius bound into the scaled bound.
    unfold localGradientRadius at hrk_lt
    have hmul : r k * (M : ℝ) < 2 * μ := by
      exact (lt_div_iff₀ hM).mp hrk_lt
    simpa [mul_comm] using hmul
  -- Divide the same numerator inequality by the positive factor `L + μ`.
  calc
    scaled k = ((M : ℝ) * r k) / (L + μ) := by
      field_simp [hLμ.ne']
    _ < q := by
      exact (div_lt_div_iff_of_pos_right hLμ).2 hMr_lt

/-- Helper for Theorem 1.6.14: inside the invariant region `r_k < 2 * μ / M`, the source gap
ratio can be rewritten in the scaled variable as `a_k / (q - a_k)`. -/
lemma localGradient_gap_eq_scaled_div_q_sub_scaled
    (hμ : 0 < μ) (hμL : μ ≤ L)
    {k : ℕ} (hrk_lt : r k < radius) :
    gap k = scaled k / (q - scaled k) := by
  have hLμ : 0 < L + μ := by
    nlinarith
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  have hM_ne : (M : ℝ) ≠ 0 := by
    exact_mod_cast (show (M : NNReal) ≠ 0 from by
      exact Units.ne_zero M)
  have hscaled_lt_q :=
    localGradient_scaled_lt_q_of_radius_lt (r := r) (μ := μ) (L := L) (M := M) hμ hμL hrk_lt
  have hMr_lt : (M : ℝ) * r k < 2 * μ := by
    -- Clearing the positive denominator `M` exposes the shared source denominator `2 * μ - M r_k`.
    unfold localGradientRadius at hrk_lt
    have hmul : r k * (M : ℝ) < 2 * μ := by
      exact (lt_div_iff₀ hM).mp hrk_lt
    simpa [mul_comm] using hmul
  have hshared_pos : 0 < 2 * μ - (M : ℝ) * r k := by
    nlinarith
  have hradius_sub :
      radius - r k = (2 * μ - (M : ℝ) * r k) / (M : ℝ) := by
    -- This is the source denominator after moving to the common numerator `2 * μ - M r_k`.
    unfold localGradientRadius
    field_simp [hM_ne]
  have hq_sub :
      q - scaled k = (2 * μ - (M : ℝ) * r k) / (L + μ) := by
    -- The scaled denominator is the same source numerator divided by `L + μ`.
    field_simp [hLμ.ne']
  change r k / (radius - r k) =
      (((M : ℝ) / (L + μ)) * r k) / ((2 * μ / (L + μ)) - ((M : ℝ) / (L + μ)) * r k)
  rw [hradius_sub, hq_sub]
  -- With both denominators normalized, the identity is a direct cancellation.
  field_simp [hM_ne, hLμ.ne', hshared_pos.ne']

/-- Helper for Theorem 1.6.14: the scaled variable can be reconstructed from the source gap ratio
by `a_k = q * gap_k / (1 + gap_k)`. -/
lemma localGradient_scaled_eq_q_mul_gap_div_one_add_gap
    (hμ : 0 < μ) (hμL : μ ≤ L)
    {k : ℕ} (hrk_lt : r k < radius) :
    scaled k = q * gap k / (1 + gap k) := by
  have hLμ : 0 < L + μ := by
    nlinarith [hμ, hμL]
  have hq_pos : 0 < q := by
    change 0 < (2 * μ) / (L + μ)
    positivity
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hscaled_lt_q :=
    localGradient_scaled_lt_q_of_radius_lt (r := r) (μ := μ) (L := L) (M := M) hμ hμL hrk_lt
  let a : ℝ := scaled k
  have ha_lt : a < q := by
    simpa [a] using hscaled_lt_q
  have hqa_pos : 0 < q - a := sub_pos.mpr ha_lt
  have hqa_ne : q - a ≠ 0 := sub_ne_zero.mpr ha_lt.ne.symm
  have hsum :
      1 + a / (q - a) = q / (q - a) := by
    -- The inverse Möbius transform uses the normalized denominator `q / (q - a)`.
    calc
      1 + a / (q - a) = (q - a) / (q - a) + a / (q - a) := by
        rw [div_self hqa_ne]
      _ = ((q - a) + a) / (q - a) := by
        rw [← add_div]
      _ = q / (q - a) := by
        ring
  have hq_gap :
      q * (a / (q - a)) / (1 + a / (q - a)) = a := by
    rw [hsum]
    have hq_div_ne : q / (q - a) ≠ 0 := div_ne_zero hq_ne hqa_ne
    apply (div_eq_iff hq_div_ne).2
    -- Clear the normalized denominator `q / (q - a)` to recover the identity map.
    field_simp [hq_ne, hqa_ne]
  -- Substitute the normalized gap expression and apply the inverse Möbius formula.
  rw [localGradient_gap_eq_scaled_div_q_sub_scaled
    (r := r) (μ := μ) (L := L) (M := M) hμ hμL hrk_lt]
  simpa [a] using hq_gap.symm

/-- Helper for Theorem 1.6.14: positive radii convert the gap ratio back into the reciprocal-gap
expression `radius / r_k - 1`. -/
lemma localGradient_reciprocal_gap_eq
    {k : ℕ} (hrk_pos : 0 < r k) (hrk_lt : r k < radius) :
    radius / r k - 1 = 1 / gap k := by
  have hgap_den : radius - r k ≠ 0 := sub_ne_zero.mpr hrk_lt.ne.symm
  -- Clearing denominators shows the two rational forms coincide.
  field_simp [hgap_den, hrk_pos.ne']

section Recurrence

variable (hμ : 0 < μ) (hμL : μ ≤ L)
variable (hstep : ∀ k : ℕ, h k = step)
variable (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)

/-- Under `0 < μ` and `μ ≤ L`, so that `L + μ > 0`, once the step schedule is identified with
the textbook value `h_k = 2 / (L + μ)`, the source radius estimate becomes
`r_{k+1} ≤ ((L - μ) r_k + M r_k^2) / (L + μ)`. -/
theorem localGradientRadius_recurrence_of_optimal_step
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hstep : ∀ k : ℕ, h k = step)
    (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)
    (k : ℕ) :
    r (k + 1) ≤ ((L - μ) * r k + (M : ℝ) * r k ^ (2 : ℕ)) / (L + μ) := by
  have hLμ : 0 < L + μ := by
    nlinarith [hμ, hμL]
  -- Specialize the source one-step bound at the textbook minimizer `2 / (L + μ)`.
  calc
    r (k + 1) ≤ bound k (h k) * r k := hrec k
    _ = bound k step * r k := by rw [hstep k]
    _ = (((L - μ) + (M : ℝ) * r k) / (L + μ)) * r k := by
      rw [localGradient_bound_at_step (r := r) (μ := μ) (L := L) (M := M) hLμ k]
    _ = ((L - μ) * r k + (M : ℝ) * r k ^ (2 : ℕ)) / (L + μ) := by
      field_simp [hLμ.ne']

/-- Under `0 < μ` and `μ ≤ L`, so that the scaling by `L + μ` is nondegenerate, for the scaled
radii `a_k = (M / (L + μ)) r_k`, substituting the textbook step `h_k = 2 / (L + μ)` turns the
source recurrence into
`a_{k+1} ≤ (1 - q + a_k) a_k` with `q = 2 * μ / (L + μ)`. -/
theorem localGradientScaledRadius_recurrence_of_optimal_step
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hstep : ∀ k : ℕ, h k = step)
    (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)
    (k : ℕ) :
    scaled (k + 1) ≤ (1 - q + scaled k) * scaled k := by
  have hLμ : 0 < L + μ := by
    nlinarith [hμ, hμL]
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  have hscale_nonneg : 0 ≤ (M : ℝ) / (L + μ) := by
    positivity
  have hraw :=
    mul_le_mul_of_nonneg_left
      (localGradientRadius_recurrence_of_optimal_step
        (r := r) (h := h) (μ := μ) (L := L) (M := M) hμ hμL hstep hrec k)
      hscale_nonneg
  -- Multiply the radius recurrence by `M / (L + μ)` and rewrite both sides into `a_k`.
  calc
    scaled (k + 1) = ((M : ℝ) / (L + μ)) * r (k + 1) := by
      rfl
    _ ≤ ((M : ℝ) / (L + μ)) *
        (((L - μ) * r k + (M : ℝ) * r k ^ (2 : ℕ)) / (L + μ)) := hraw
    _ = (1 - q + scaled k) * scaled k := by
      field_simp [hLμ.ne', hM.ne']
      ring

end Recurrence

section OptimalStep

variable (hμ : 0 < μ) (hμL : μ ≤ L)
variable (hr0 : 0 < r 0 ∧ r 0 < radius)
variable (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
variable (hopt : ∀ k : ℕ, IsMinOn (bound k) positiveSteps (h k))
variable (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)

/-- If the sequence `r` is nonnegative, `0 < r_0 < 2 * μ / M`, and each `h_k` is the source
minimizer `h_k^*`, then the optimal-step identity `h_k = 2 / (L + μ)` propagates along the
radius-invariant region `r_k < 2 * μ / M`. -/
theorem localGradientRadius_strict_decay_of_optimal_step
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hr0 : 0 < r 0 ∧ r 0 < radius)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
    (hopt : ∀ k : ℕ, IsMinOn (bound k) positiveSteps (h k))
    (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)
    (k : ℕ) :
    h k = step ∧ r k < radius := by
  have hLμ : 0 < L + μ := by
    nlinarith [hμ, hμL]
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  induction k with
  | zero =>
      constructor
      · -- The initial minimizer already lies at the textbook crossing point.
        exact localGradientRadiusBound_optimalStep_eq
          (r := r) (μ := μ) (L := L) (M := M) hμ hμL
          (hr_nonneg 0) hr0.2 (hopt 0)
      · exact hr0.2
  | succ k ih =>
      rcases ih with ⟨hk_eq, hrk_lt⟩
      have hMr_lt : (M : ℝ) * r k < 2 * μ := by
        -- The inductive radius bound keeps the source coefficient strictly below one.
        unfold localGradientRadius at hrk_lt
        have hmul : r k * (M : ℝ) < 2 * μ := by
          exact (lt_div_iff₀ hM).mp hrk_lt
        simpa [mul_comm] using hmul
      have hcoeff_lt_one : (((L - μ) + (M : ℝ) * r k) / (L + μ)) < 1 := by
        have hnumer_lt : (L - μ) + (M : ℝ) * r k < L + μ := by
          nlinarith
        have hnumer_lt' : (L - μ) + (M : ℝ) * r k < 1 * (L + μ) := by
          simpa using hnumer_lt
        exact (div_lt_iff₀ hLμ).2 hnumer_lt'
      have hr_succ_lt : r (k + 1) < radius := by
        -- Route correction: propagate the invariant through the explicit one-step bound, rather
        -- than trying to infer strict decay from the raw `max` recurrence directly.
        calc
          r (k + 1) ≤ (((L - μ) + (M : ℝ) * r k) / (L + μ)) * r k := by
            calc
              r (k + 1) ≤ bound k (h k) * r k := hrec k
              _ = bound k step * r k := by rw [hk_eq]
              _ = (((L - μ) + (M : ℝ) * r k) / (L + μ)) * r k := by
                rw [localGradient_bound_at_step (r := r) (μ := μ) (L := L) (M := M) hLμ k]
          _ ≤ r k := by
            have hrk_nonneg := hr_nonneg k
            have hcoeff_le_one : (((L - μ) + (M : ℝ) * r k) / (L + μ)) ≤ 1 := hcoeff_lt_one.le
            exact by
              simpa using mul_le_mul_of_nonneg_right hcoeff_le_one hrk_nonneg
          _ < radius := hrk_lt
      constructor
      · -- Once the next radius is still inside the invariant region, the minimizer is again the
        -- textbook step.
        exact localGradientRadiusBound_optimalStep_eq
          (r := r) (μ := μ) (L := L) (M := M) hμ hμL
          (hr_nonneg (k + 1)) hr_succ_lt (hopt (k + 1))
      · exact hr_succ_lt

/-- Helper for Theorem 1.6.14: under the optimal-step schedule, the gap ratio contracts by the
factor `1 / (1 + q)` in one step. -/
lemma localGradientGap_step_bound_of_optimal_step
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hr0 : 0 < r 0 ∧ r 0 < radius)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
    (hopt : ∀ k : ℕ, IsMinOn (bound k) positiveSteps (h k))
    (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)
    (k : ℕ) :
    gap (k + 1) ≤ gap k / (1 + q) := by
  have hq_pos : 0 < q := by
    have hLμ : 0 < L + μ := by
      nlinarith
    change 0 < (2 * μ) / (L + μ)
    positivity
  have hk_lt :
      r k < radius :=
    (localGradientRadius_strict_decay_of_optimal_step
      (r := r) (h := h) (μ := μ) (L := L) (M := M)
      hμ hμL hr0 hr_nonneg hopt hrec k).2
  have hk1_lt :
      r (k + 1) < radius :=
    (localGradientRadius_strict_decay_of_optimal_step
      (r := r) (h := h) (μ := μ) (L := L) (M := M)
      hμ hμL hr0 hr_nonneg hopt hrec (k + 1)).2
  have hscaled_lt_q :=
    localGradient_scaled_lt_q_of_radius_lt (r := r) (μ := μ) (L := L) (M := M) hμ hμL hk_lt
  have hscaled1_lt_q :=
    localGradient_scaled_lt_q_of_radius_lt (r := r) (μ := μ) (L := L) (M := M) hμ hμL hk1_lt
  have hLμ : 0 < L + μ := by
    nlinarith
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  have hscaled_nonneg : 0 ≤ scaled k := by
    exact mul_nonneg (div_nonneg hM.le hLμ.le) (hr_nonneg k)
  have hscaled1_nonneg : 0 ≤ scaled (k + 1) := by
    exact mul_nonneg (div_nonneg hM.le hLμ.le) (hr_nonneg (k + 1))
  have hstep_eq : ∀ n : ℕ, h n = step := fun n ↦
    (localGradientRadius_strict_decay_of_optimal_step
      (r := r) (h := h) (μ := μ) (L := L) (M := M)
      hμ hμL hr0 hr_nonneg hopt hrec n).1
  have hscaled_step :=
    localGradientScaledRadius_recurrence_of_optimal_step
      (r := r) (h := h) (μ := μ) (L := L) (M := M)
      hμ hμL hstep_eq hrec k
  have hnorm :
      (1 + q - scaled k) * scaled (k + 1) ≤ scaled k := by
    have hfactor_nonneg : 0 ≤ 1 + q - scaled k := by
      nlinarith [hscaled_lt_q]
    have hfactor_bound : (1 + q - scaled k) * (1 - q + scaled k) ≤ 1 := by
      have hsq_nonneg : 0 ≤ (q - scaled k) ^ (2 : ℕ) := sq_nonneg (q - scaled k)
      nlinarith
    -- Normalize the quadratic recurrence by the positive factor `1 + q - a_k`.
    calc
      (1 + q - scaled k) * scaled (k + 1)
          ≤ (1 + q - scaled k) * ((1 - q + scaled k) * scaled k) := by
            gcongr
      _ = ((1 + q - scaled k) * (1 - q + scaled k)) * scaled k := by ring
      _ ≤ 1 * scaled k := by
            gcongr
      _ = scaled k := by ring
  have hgap_eq :=
    localGradient_gap_eq_scaled_div_q_sub_scaled
      (r := r) (μ := μ) (L := L) (M := M) hμ hμL hk_lt
  have hgap1_eq :=
    localGradient_gap_eq_scaled_div_q_sub_scaled
      (r := r) (μ := μ) (L := L) (M := M) hμ hμL hk1_lt
  have hden_pos : 0 < q - scaled k := by
    nlinarith
  have hden1_pos : 0 < q - scaled (k + 1) := by
    nlinarith
  have honeq_pos : 0 < 1 + q := by
    linarith
  have honeq_ne : (1 + q) ≠ 0 := honeq_pos.ne'
  have hcross :
      (1 + q) * gap (k + 1) ≤ gap k := by
    rw [hgap_eq, hgap1_eq]
    let a : ℝ := scaled k
    let b : ℝ := scaled (k + 1)
    have hnorm_ab : (1 + q - a) * b ≤ a := by
      simpa [a, b] using hnorm
    have ha_nonneg : 0 ≤ a := by
      simpa [a] using hscaled_nonneg
    have hb_nonneg : 0 ≤ b := by
      simpa [b] using hscaled1_nonneg
    have ha_lt : a < q := by
      simpa [a] using hscaled_lt_q
    have hb_lt : b < q := by
      simpa [b] using hscaled1_lt_q
    have hmain :
        (1 + q) * (scaled (k + 1) / (q - scaled (k + 1)))
          ≤ scaled k / (q - scaled k) := by
      have hdena_pos : 0 < q - a := by
        simpa [a] using hden_pos
      have hdenb_pos : 0 < q - b := by
        simpa [b] using hden1_pos
      have hcross_mul_ab :
          (1 + q) * b * (q - a) ≤ a * (q - b) := by
        nlinarith [hnorm_ab, ha_nonneg, hb_nonneg, ha_lt, hb_lt]
      have hmain_ab :
          (1 + q) * (b / (q - b)) ≤ a / (q - a) := by
        have hcross_mul_ab' :
            ((1 + q) * b) * (q - a) ≤ a * (q - b) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hcross_mul_ab
        have hmain_ab' :
            ((1 + q) * b) / (q - b) ≤ a / (q - a) := by
          exact (div_le_div_iff₀ hdenb_pos hdena_pos).2 hcross_mul_ab'
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmain_ab'
      simpa [a, b] using hmain_ab
    simpa [a, b] using hmain
  -- Convert the normalized contraction back to the displayed gap form.
  have hcross' : gap (k + 1) * (1 + q) ≤ gap k := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross
  exact (le_div_iff₀ honeq_pos).2 hcross'

/-- The owner geometric-rate statement for the gap ratio
`r_k / ((2 * μ / M) - r_k)` under the source optimal-step choice, with positivity of each radius
derived from `0 < r_0 < 2 * μ / M`, nonnegativity, and the strict-decay layer above. -/
theorem localGradientGap_hasGeometricRate_of_optimal_step
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hr0 : 0 < r 0 ∧ r 0 < radius)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
    (hopt : ∀ k : ℕ, IsMinOn (bound k) positiveSteps (h k))
    (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)
    :
    HasGeometricRateOfConvergence gap (q / (1 + q)) (gap 0) := by
  have hq_pos : 0 < q := by
    have hLμ : 0 < L + μ := by
      nlinarith
    change 0 < (2 * μ) / (L + μ)
    positivity
  have hrate_le_one : q / (1 + q) ≤ 1 := by
    have honeq_pos : 0 < 1 + q := by
      linarith
    exact (div_le_iff₀ honeq_pos).2 <| by
      nlinarith
  have hfactor : 1 - q / (1 + q) = 1 / (1 + q) := by
    have honeq_pos : 0 < 1 + q := by
      linarith
    field_simp [honeq_pos.ne']
    ring
  -- The one-step gap contraction is exactly the step bound for geometric convergence.
  refine HasGeometricRateOfConvergence.of_step_bound hrate_le_one le_rfl ?_
  intro k
  calc
    gap (k + 1) ≤ gap k / (1 + q) := by
      exact localGradientGap_step_bound_of_optimal_step
        (r := r) (h := h) (μ := μ) (L := L) (M := M)
        hμ hμL hr0 hr_nonneg hopt hrec k
    _ = (1 - q / (1 + q)) * gap k := by
      rw [hfactor]
      ring

-- Proof sketch: combine the geometric-rate statement for `gap k = r k / (radius - r k)` with
-- the algebraic identity `radius / r k - 1 = 1 / gap k`, then rewrite the textbook recurrence
-- into the displayed reciprocal-gap inequality.
/-- Theorem 1.6.14 (1): if each `h_k` is the source minimizer `h_k^*` of
`max {a_k(h), b_k(h)}`, the radius sequence is positive, and `0 < r_0 < 2 * μ / M`, then
the reciprocal-gap estimate `(1.2.31)` holds:
`radius / r_k - 1 ≥ (1 + q)^k (radius / r_0 - 1)`. -/
theorem localGradientScaledRadius_reciprocal_gap_lower_bound_of_optimal_step
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hr0 : 0 < r 0 ∧ r 0 < radius)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
    (hopt : ∀ k : ℕ, IsMinOn (bound k) positiveSteps (h k))
    (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)
    (hr_pos : ∀ k : ℕ, 0 < r k)
    (k : ℕ) :
    radius / r k - 1 ≥ (1 + q) ^ k * (radius / r 0 - 1) := by
  -- Route correction: after the gap sequence has a geometric rate, invert that bound with
  -- `localGradient_reciprocal_gap_eq` to recover the displayed reciprocal-gap inequality.
  have hq_pos : 0 < q := by
    have hLμ : 0 < L + μ := by
      nlinarith
    change 0 < (2 * μ) / (L + μ)
    positivity
  have honeq_pos : 0 < 1 + q := by
    linarith
  have hfactor : 1 - q / (1 + q) = 1 / (1 + q) := by
    field_simp [honeq_pos.ne']
    ring
  have hk_lt :
      r k < radius :=
    (localGradientRadius_strict_decay_of_optimal_step
      (r := r) (h := h) (μ := μ) (L := L) (M := M)
      hμ hμL hr0 hr_nonneg hopt hrec k).2
  have hgap_rate :=
    localGradientGap_hasGeometricRate_of_optimal_step
      (r := r) (h := h) (μ := μ) (L := L) (M := M)
      hμ hμL hr0 hr_nonneg hopt hrec
  have hgap_bound : gap k ≤ gap 0 / (1 + q) ^ k := by
    have hrate_k := hgap_rate k
    rw [hfactor] at hrate_k
    simpa [div_eq_mul_inv] using hrate_k
  have hgapk_pos : 0 < gap k := by
    exact div_pos (hr_pos k) (sub_pos.mpr hk_lt)
  have hgap0_pos : 0 < gap 0 := by
    exact div_pos hr0.1 (sub_pos.mpr hr0.2)
  have hpow_pos : 0 < (1 + q) ^ k := by
    exact pow_pos honeq_pos k
  have hpow_mul : gap k * (1 + q) ^ k ≤ gap 0 := by
    exact (le_div_iff₀ hpow_pos).mp hgap_bound
  have hinv :
      (1 + q) ^ k / gap 0 ≤ 1 / gap k := by
    exact (div_le_div_iff₀ hgap0_pos hgapk_pos).2 <| by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hpow_mul
  -- Rewrite both reciprocals back into the source expression `radius / r_k - 1`.
  calc
    (1 + q) ^ k * (radius / r 0 - 1)
        = (1 + q) ^ k / gap 0 := by
          rw [localGradient_reciprocal_gap_eq
            (r := r) (μ := μ) (M := M) (k := 0) hr0.1 hr0.2]
          ring
    _ ≤ 1 / gap k := hinv
    _ = radius / r k - 1 := by
          rw [localGradient_reciprocal_gap_eq
            (r := r) (μ := μ) (M := M) (k := k) (hr_pos k) hk_lt]

-- Proof sketch: start from the reciprocal-gap estimate `(1.2.31)` and solve the resulting
-- inequality for `r k`. Multiplying by `M / (L + μ)` rewrites the bound in terms of
-- `scaled k = (M / (L + μ)) r k`.
/-- Theorem 1.6.14 (2): under the same optimal-step hypotheses, the scaled radii satisfy the
first explicit upper bound from `(1.2.32)`:
`a_k ≤ (q r_0) / (r_0 + (1 + q)^k (radius - r_0))`. -/
theorem localGradientScaledRadius_first_upper_bound_of_optimal_step
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hr0 : 0 < r 0 ∧ r 0 < radius)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
    (hopt : ∀ k : ℕ, IsMinOn (bound k) positiveSteps (h k))
    (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)
    (k : ℕ) :
    scaled k ≤ (q * r 0) / (r 0 + (1 + q) ^ k * (radius - r 0)) := by
  have hq_pos : 0 < q := by
    have hLμ : 0 < L + μ := by
      nlinarith
    change 0 < (2 * μ) / (L + μ)
    positivity
  have honeq_pos : 0 < 1 + q := by
    linarith
  have hfactor : 1 - q / (1 + q) = 1 / (1 + q) := by
    field_simp [honeq_pos.ne']
    ring
  have hk_lt :
      r k < radius :=
    (localGradientRadius_strict_decay_of_optimal_step
      (r := r) (h := h) (μ := μ) (L := L) (M := M)
      hμ hμL hr0 hr_nonneg hopt hrec k).2
  have hgap_rate :=
    localGradientGap_hasGeometricRate_of_optimal_step
      (r := r) (h := h) (μ := μ) (L := L) (M := M)
      hμ hμL hr0 hr_nonneg hopt hrec
  let g : ℝ := r 0 / ((1 + q) ^ k * (radius - r 0))
  have hg_eq : gap 0 / (1 + q) ^ k = g := by
    dsimp [g]
    change r 0 / (radius - r 0) / (1 + q) ^ k = r 0 / ((1 + q) ^ k * (radius - r 0))
    field_simp [sub_ne_zero.mpr hr0.2.ne.symm, pow_ne_zero _ honeq_pos.ne']
  have hgap_bound : gap k ≤ g := by
    have hraw : gap k ≤ gap 0 / (1 + q) ^ k := by
      have hrate_k := hgap_rate k
      rw [hfactor] at hrate_k
      simpa [div_eq_mul_inv] using hrate_k
    rw [hg_eq] at hraw
    exact hraw
  have hgap_nonneg : 0 ≤ gap k := by
    exact div_nonneg (hr_nonneg k) (sub_nonneg.mpr hk_lt.le)
  have hg_nonneg : 0 ≤ g := by
    dsimp [g]
    exact div_nonneg hr0.1.le <|
      mul_nonneg (pow_nonneg honeq_pos.le _) (sub_nonneg.mpr hr0.2.le)
  have hfrac :
      gap k / (1 + gap k) ≤ g / (1 + g) := by
    have hden_pos : 0 < 1 + gap k := by
      nlinarith
    have hdeng_pos : 0 < 1 + g := by
      nlinarith
    have hcross : gap k * (1 + g) ≤ g * (1 + gap k) := by
      nlinarith [hgap_bound]
    exact (div_le_div_iff₀ hden_pos hdeng_pos).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcross
  have hfrac_q :
      q * (gap k / (1 + gap k)) ≤ q * (g / (1 + g)) := by
    exact mul_le_mul_of_nonneg_left hfrac hq_pos.le
  have hscaled_eq :
      scaled k = q * (gap k / (1 + gap k)) := by
    calc
      scaled k = q * gap k / (1 + gap k) :=
        localGradient_scaled_eq_q_mul_gap_div_one_add_gap
          (r := r) (μ := μ) (L := L) (M := M) hμ hμL hk_lt
      _ = q * (gap k / (1 + gap k)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
  -- Bound `gap k` by its geometric envelope, then rewrite the envelope in the textbook form.
  calc
    scaled k = q * (gap k / (1 + gap k)) := hscaled_eq
    _ ≤ q * (g / (1 + g)) := hfrac_q
    _ = (q * r 0) / (r 0 + (1 + q) ^ k * (radius - r 0)) := by
          dsimp [g]
          field_simp [sub_ne_zero.mpr hr0.2.ne.symm, pow_ne_zero _ honeq_pos.ne']
          ring

-- Proof sketch: derive the first bound in `(1.2.32)` from `(1.2.31)`, then bound the
-- denominator below by `(radius - r 0) * (1 + q)^k` to obtain the geometric upper estimate.
/-- Theorem 1.6.14 (3): under the same optimal-step hypotheses, the scaled radii satisfy the
second explicit upper bound from `(1.2.32)`:
`a_k ≤ ((q r_0) / (radius - r_0)) (1 / (1 + q))^k`. -/
theorem localGradientScaledRadius_second_upper_bound_of_optimal_step
    (hμ : 0 < μ) (hμL : μ ≤ L)
    (hr0 : 0 < r 0 ∧ r 0 < radius)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
    (hopt : ∀ k : ℕ, IsMinOn (bound k) positiveSteps (h k))
    (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)
    (k : ℕ) :
    scaled k ≤ ((q * r 0) / (radius - r 0)) * (1 / (1 + q)) ^ k := by
  have hq_pos : 0 < q := by
    have hLμ : 0 < L + μ := by
      nlinarith
    change 0 < (2 * μ) / (L + μ)
    positivity
  have honeq_pos : 0 < 1 + q := by
    linarith
  have hnum_nonneg : 0 ≤ q * r 0 := by
    exact mul_nonneg hq_pos.le hr0.1.le
  have hden_pos : 0 < (1 + q) ^ k * (radius - r 0) := by
    exact mul_pos (pow_pos honeq_pos _) (sub_pos.mpr hr0.2)
  have hfirst :=
    localGradientScaledRadius_first_upper_bound_of_optimal_step
      (r := r) (h := h) (μ := μ) (L := L) (M := M)
      hμ hμL hr0 hr_nonneg hopt hrec k
  have hden_le :
      (1 + q) ^ k * (radius - r 0)
        ≤ r 0 + (1 + q) ^ k * (radius - r 0) := by
    nlinarith [hr0.1]
  -- Lower the denominator by dropping the nonnegative `r_0` term.
  calc
    scaled k ≤ (q * r 0) / (r 0 + (1 + q) ^ k * (radius - r 0)) := hfirst
    _ ≤ (q * r 0) / ((1 + q) ^ k * (radius - r 0)) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
    _ = ((q * r 0) / (radius - r 0)) * (1 / (1 + q)) ^ k := by
          rw [one_div_pow]
          field_simp [sub_ne_zero.mpr hr0.2.ne.symm, pow_ne_zero _ honeq_pos.ne']

end OptimalStep

end

end
