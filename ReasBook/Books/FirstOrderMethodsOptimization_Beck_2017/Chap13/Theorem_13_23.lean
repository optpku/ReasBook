/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_65
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_22

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Set

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby Chapter 5 and Chapter 13 owners. The primary domain is strong convexity. The sampled owner
abstractions are:

- mathlib's function-side owner `StrongConvexOn`;
- Chapter 5's smoothness owner `is_l_smooth_on`;
- Chapter 13's primitive set-side owner `Set.StrongConvex`, with the source-facing wrapper
  `Set.StronglyConvexWith` adding only positivity and nonemptiness.

Accordingly, the first theorem below remains `source-facing`, while the second is a `bridge/view`
statement derived from the owner projection rather than a parallel local copy of the same
mathematics. -/

-- Proof sketch: combine strong convexity of `g` with the sublevel assumptions `g x, g y ≤ α` to
-- show that the chord point has function value at most
-- `α - (σ_g / 2) t (1 - t) ‖x - y‖²`. Use nonnegativity and smoothness of `g` to bound the norm
-- of the derivative at the chord point by `sqrt (2 L_g g(...))`, then apply the smoothness upper
-- estimate to any point in the prescribed closed ball and use concavity of `sqrt` to conclude
-- that the whole ball stays inside the `α`-sublevel set.
/-- Strong convexity controls the value of `g` at the chord point of two points in the
`α`-sublevel set. -/
lemma sublevel_chord_value_le
    (g : E → ℝ) (α : ℝ) (σg : ℝ) (hg_strong : StrongConvexOn univ σg g)
    {x y : E} (hx : g x ≤ α) (hy : g y ≤ α) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    g (t • x + (1 - t) • y) ≤
      α - (σg / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) := by
  -- The strong-convexity chord estimate is exactly the source proof's first inequality.
  have hstrong := hg_strong.2
  have hconvex :
      g (t • x + (1 - t) • y) ≤
        t * g x + (1 - t) * g y - t * (1 - t) * ((σg / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      hstrong (show x ∈ (univ : Set E) by simp) (show y ∈ (univ : Set E) by simp)
        ht.1 (sub_nonneg.mpr ht.2) (by linarith)
  have htx : t * g x ≤ t * α := mul_le_mul_of_nonneg_left hx ht.1
  have hty : (1 - t) * g y ≤ (1 - t) * α := by
    apply mul_le_mul_of_nonneg_left hy
    linarith [ht.2]
  calc
    g (t • x + (1 - t) • y)
        ≤ t * g x + (1 - t) * g y - t * (1 - t) * ((σg / 2) * ‖x - y‖ ^ (2 : ℕ)) := hconvex
    _ ≤ t * α + (1 - t) * α - t * (1 - t) * ((σg / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
      linarith
    _ = α - (σg / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) := by ring

/-- On the whole space, `L`-smoothness gives the Banach-space quadratic upper model with the
Fréchet derivative. -/
lemma is_l_smooth_on_upper_quadratic_univ
    {g : E → ℝ} {Lg : NNReal} (hg_smooth : is_l_smooth_on g univ Lg) (x y : E) :
    g y ≤ g x + fderiv ℝ g x (y - x) + ((Lg : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  -- Route correction: the Chapter 10 global descent lemma already provides the exact quadratic
  -- upper model needed here, so this helper is only an adapter to the local theorem statement.
  simpa using is_l_smooth_on_univ_fderiv_descent hg_smooth x y

/-- Multiplying a real number by its sign recovers its absolute value. -/
private lemma real_sign_mul_eq_abs (t : ℝ) : Real.sign t * t = |t| := by
  -- Split by the sign of `t` and reduce to the defining formulas for `Real.sign`.
  rcases lt_trichotomy t 0 with ht_neg | rfl | ht_pos
  · simp [Real.sign_of_neg ht_neg, abs_of_neg ht_neg]
  · simp
  · simp [Real.sign_of_pos ht_pos, abs_of_pos ht_pos]

/-- A real-valued continuous linear functional admits a unit-ball direction whose image is strictly
larger than any sub-opnorm threshold. -/
lemma exists_norm_lt_one_lt_apply_of_lt_opNorm_real
    (a : E →L[ℝ] ℝ) {r : ℝ} (hr : r < ‖a‖) :
    ∃ v : E, ‖v‖ < 1 ∧ r < a v := by
  -- First choose a vector whose image norm is above `r`, then flip its sign so the image itself
  -- is positive and still above `r`.
  obtain ⟨u, hu_norm, hu_apply⟩ := ContinuousLinearMap.exists_lt_apply_of_lt_opNorm a hr
  let v : E := Real.sign (a u) • u
  have hsign_abs_le_one : |Real.sign (a u)| ≤ 1 := by
    rcases lt_trichotomy (a u) 0 with hau_neg | hau_zero | hau_pos
    · simp [Real.sign_of_neg hau_neg]
    · simp [hau_zero]
    · simp [Real.sign_of_pos hau_pos]
  have hv_norm : ‖v‖ < 1 := by
    calc
      ‖v‖ = |Real.sign (a u)| * ‖u‖ := by
        rw [show v = Real.sign (a u) • u by rfl, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right hsign_abs_le_one (norm_nonneg _)
      _ = ‖u‖ := by ring
      _ < 1 := hu_norm
  have hv_apply_eq : a v = |a u| := by
    calc
      a v = Real.sign (a u) * a u := by
        simp [v]
      _ = |a u| := real_sign_mul_eq_abs (a u)
  have hr_apply_abs : r < |a u| := by
    simpa [Real.norm_eq_abs] using hu_apply
  exact ⟨v, hv_norm, hv_apply_eq ▸ hr_apply_abs⟩

/-- Nonnegativity and global smoothness bound the derivative norm by `√(2 L_g g(x))`. -/
lemma norm_fderiv_le_sqrt_two_mul_value
    {g : E → ℝ} {Lg : NNReal}
    (hg_nonneg : ∀ x, 0 ≤ g x) (hLg : 0 < (Lg : ℝ))
    (hg_smooth : is_l_smooth_on g univ Lg) (x : E) :
    ‖fderiv ℝ g x‖ ≤ Real.sqrt (2 * (Lg : ℝ) * g x) := by
  -- Route correction: reuse the Chapter 10 quadratic upper model and run the source proof's
  -- trial-step contradiction instead of rebuilding the descent estimate from scratch.
  refine le_of_not_gt ?_
  intro hgt
  obtain ⟨r, hsqrt_lt_r, hr_lt_norm⟩ := exists_between hgt
  have hr_pos : 0 < r := lt_of_le_of_lt (Real.sqrt_nonneg _) hsqrt_lt_r
  obtain ⟨v, hv_norm, hr_lt_apply⟩ :=
    exists_norm_lt_one_lt_apply_of_lt_opNorm_real (fderiv ℝ g x) hr_lt_norm
  set s : ℝ := r / (Lg : ℝ)
  set y : E := x - s • v
  have hs_pos : 0 < s := by
    -- The trial-step length is positive because both `r` and `L_g` are positive.
    dsimp [s]
    exact div_pos hr_pos hLg
  have hy_nonneg : 0 ≤ g y := hg_nonneg y
  have hyx : y - x = -s • v := by
    -- The displacement from `x` to the trial point is the chosen negative step.
    simp [y, sub_eq_add_neg, add_left_comm, add_comm]
  have hlinear :
      fderiv ℝ g x (y - x) < -(r ^ (2 : ℕ) / (Lg : ℝ)) := by
    have hs_mul : s * r < s * fderiv ℝ g x v := by
      exact mul_lt_mul_of_pos_left hr_lt_apply hs_pos
    -- The sign-normalized direction makes the linear term strictly negative.
    rw [hyx]
    calc
      fderiv ℝ g x (-s • v) = -(s * fderiv ℝ g x v) := by
        simp
      _ < -(s * r) := by
        linarith
      _ = -(r ^ (2 : ℕ) / (Lg : ℝ)) := by
        dsimp [s]
        field_simp [hLg.ne']
  have hstep_norm :
      ‖y - x‖ ≤ s := by
    -- The trial-step stays within the scaled unit ball because `‖v‖ < 1`.
    rw [hyx]
    calc
      ‖-s • v‖ = |s| * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg]
      _ ≤ |s| * 1 := by
        exact mul_le_mul_of_nonneg_left hv_norm.le (abs_nonneg s)
      _ = s := by
        rw [abs_of_pos hs_pos, mul_one]
  have hstep_sq :
      ‖y - x‖ ^ (2 : ℕ) ≤ s ^ (2 : ℕ) := by
    -- Squaring preserves the norm bound because both sides are nonnegative.
    nlinarith [hstep_norm, norm_nonneg (y - x), hs_pos.le]
  have hquad :
      ((Lg : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) ≤ r ^ (2 : ℕ) / (2 * (Lg : ℝ)) := by
    -- Rewrite the quadratic remainder in terms of the chosen step length `s = r / L_g`.
    calc
      ((Lg : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ)
          ≤ ((Lg : ℝ) / 2) * s ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_left hstep_sq (by positivity)
      _ = r ^ (2 : ℕ) / (2 * (Lg : ℝ)) := by
        dsimp [s]
        field_simp [hLg.ne']
  have hdescent :
      g y ≤ g x + fderiv ℝ g x (y - x) + ((Lg : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    -- The global quadratic model controls the function value at the trial point.
    simpa [y] using is_l_smooth_on_upper_quadratic_univ hg_smooth x y
  have hy_upper : g y < g x - r ^ (2 : ℕ) / (2 * (Lg : ℝ)) := by
    -- The linear gain dominates the quadratic remainder along this trial step.
    calc
      g y ≤ g x + fderiv ℝ g x (y - x) + ((Lg : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := hdescent
      _ < g x + (-(r ^ (2 : ℕ) / (Lg : ℝ))) + r ^ (2 : ℕ) / (2 * (Lg : ℝ)) := by
            linarith
      _ = g x - r ^ (2 : ℕ) / (2 * (Lg : ℝ)) := by
            ring
  have hgap_pos : 0 < g x - r ^ (2 : ℕ) / (2 * (Lg : ℝ)) := by
    exact lt_of_le_of_lt hy_nonneg hy_upper
  have hr_sq_lt : r ^ (2 : ℕ) < 2 * (Lg : ℝ) * g x := by
    -- Multiply the positive gap by `2 L_g` to recover the scalar inequality from the source.
    have hmul_pos :
        0 < (2 * (Lg : ℝ)) * (g x - r ^ (2 : ℕ) / (2 * (Lg : ℝ))) := by
      exact mul_pos (by positivity) hgap_pos
    have hmul_eq :
        (2 * (Lg : ℝ)) * (g x - r ^ (2 : ℕ) / (2 * (Lg : ℝ))) =
          2 * (Lg : ℝ) * g x - r ^ (2 : ℕ) := by
      field_simp [hLg.ne']
    rw [hmul_eq] at hmul_pos
    linarith
  have harg_nonneg : 0 ≤ 2 * (Lg : ℝ) * g x := by
    nlinarith [hg_nonneg x, hLg.le]
  have hsqrt_sq_lt : 2 * (Lg : ℝ) * g x < r ^ (2 : ℕ) := by
    -- Squaring `sqrt(2 L_g g(x)) < r` yields the opposite inequality, contradiction.
    have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * (Lg : ℝ) * g x) := Real.sqrt_nonneg _
    have hsq : (Real.sqrt (2 * (Lg : ℝ) * g x)) ^ (2 : ℕ) = 2 * (Lg : ℝ) * g x := by
      simpa using Real.sq_sqrt harg_nonneg
    nlinarith [hsqrt_lt_r, hsqrt_nonneg, hr_pos, hsq]
  exact (lt_irrefl _ <| lt_trans hsqrt_sq_lt hr_sq_lt)

/-- The radius correction term matches the source proof's `β / (2 * sqrt α)` normalization. -/
lemma radius_correction_eq_beta_div_two_sqrt_alpha
    (α : ℝ) (Lg : NNReal) (σg t r : ℝ) (hα : 0 < α) (hLg : 0 < (Lg : ℝ)) :
    ((((σg / Real.sqrt (2 * α * (Lg : ℝ))) / 2) * t * (1 - t) * r) *
        Real.sqrt ((Lg : ℝ) / 2)) =
      (((σg / 2) * t * (1 - t) * r) / (2 * Real.sqrt α)) := by
  have hsqrt_alpha_ne : Real.sqrt α ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hα)
  have hsqrt_half_ne : Real.sqrt ((Lg : ℝ) / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    positivity
  have hsqrt_two_lg :
      Real.sqrt (2 * (Lg : ℝ)) = 2 * Real.sqrt ((Lg : ℝ) / 2) := by
    -- Rewrite `2 L_g` as `4 * (L_g / 2)` so that `sqrt` pulls out the factor `2`.
    calc
      Real.sqrt (2 * (Lg : ℝ)) = Real.sqrt (4 * ((Lg : ℝ) / 2)) := by
        congr 1
        ring
      _ = Real.sqrt (4 : ℝ) * Real.sqrt ((Lg : ℝ) / 2) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ (4 : ℝ))]
      _ = 2 * Real.sqrt ((Lg : ℝ) / 2) := by
        norm_num
  have hsqrt_split :
      Real.sqrt (2 * α * (Lg : ℝ)) = 2 * Real.sqrt α * Real.sqrt ((Lg : ℝ) / 2) := by
    -- Split the denominator into the `α` and `L_g` square-root factors.
    calc
      Real.sqrt (2 * α * (Lg : ℝ)) = Real.sqrt (α * (2 * (Lg : ℝ))) := by
        congr 1
        ring
      _ = Real.sqrt α * Real.sqrt (2 * (Lg : ℝ)) := by
        rw [Real.sqrt_mul hα.le]
      _ = Real.sqrt α * (2 * Real.sqrt ((Lg : ℝ) / 2)) := by
        rw [hsqrt_two_lg]
      _ = 2 * Real.sqrt α * Real.sqrt ((Lg : ℝ) / 2) := by
        ring
  -- Cancel the common `sqrt (L_g / 2)` factor after rewriting the denominator.
  calc
    ((((σg / Real.sqrt (2 * α * (Lg : ℝ))) / 2) * t * (1 - t) * r) *
          Real.sqrt ((Lg : ℝ) / 2))
        = ((((σg / 2) * t * (1 - t) * r) * Real.sqrt ((Lg : ℝ) / 2)) /
            Real.sqrt (2 * α * (Lg : ℝ))) := by
              field_simp
    _ = ((((σg / 2) * t * (1 - t) * r) * Real.sqrt ((Lg : ℝ) / 2)) /
          (2 * Real.sqrt α * Real.sqrt ((Lg : ℝ) / 2))) := by
            rw [hsqrt_split]
    _ = (((σg / 2) * t * (1 - t) * r) / (2 * Real.sqrt α)) := by
          field_simp [hsqrt_alpha_ne, hsqrt_half_ne]

/-- The final square-root correction stays below `α`. -/
lemma sqrt_sub_add_beta_div_two_sqrt_alpha_sq_le_alpha
    (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β) (hβα : β ≤ α) :
    (Real.sqrt (α - β) + β / (2 * Real.sqrt α)) ^ (2 : ℕ) ≤ α := by
  have hsqrt_alpha_pos : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hsqrt_alpha_ne : Real.sqrt α ≠ 0 := hsqrt_alpha_pos.ne'
  have hright_nonneg : 0 ≤ Real.sqrt α - β / (2 * Real.sqrt α) := by
    -- The tangent-line upper bound is nonnegative because `β ≤ α`.
    have hβ_term_le : β / (2 * Real.sqrt α) ≤ Real.sqrt α := by
      have hsq_alpha : (Real.sqrt α) ^ (2 : ℕ) = α := by
        simpa using Real.sq_sqrt hα.le
      have hden_pos : 0 < 2 * Real.sqrt α := by
        positivity
      have hmul : β ≤ (2 * Real.sqrt α) * Real.sqrt α := by
        nlinarith [hβα, hsq_alpha]
      exact (div_le_iff₀ hden_pos).2 <| by
        simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
    linarith
  have htangent_sq :
      α - β ≤ (Real.sqrt α - β / (2 * Real.sqrt α)) ^ (2 : ℕ) := by
    -- Expanding the square leaves the manifestly nonnegative correction `β² / (4 α)`.
    have hsq_alpha : (Real.sqrt α) ^ (2 : ℕ) = α := by
      simpa using Real.sq_sqrt hα.le
    have hsquare :
        (Real.sqrt α - β / (2 * Real.sqrt α)) ^ (2 : ℕ) =
          α - β + β ^ (2 : ℕ) / (4 * α) := by
      field_simp [hsqrt_alpha_ne]
      rw [hsq_alpha]
      ring
    rw [hsquare]
    have hcorr_nonneg : 0 ≤ β ^ (2 : ℕ) / (4 * α) := by
      positivity
    linarith
  have hsqrt_tangent :
      Real.sqrt (α - β) ≤ Real.sqrt α - β / (2 * Real.sqrt α) := by
    -- Convert the tangent-line comparison to a squared inequality on the nonnegative half-line.
    rw [Real.sqrt_le_iff]
    exact ⟨hright_nonneg, htangent_sq⟩
  have hsum_le :
      Real.sqrt (α - β) + β / (2 * Real.sqrt α) ≤ Real.sqrt α := by
    linarith
  have hsum_nonneg : 0 ≤ Real.sqrt (α - β) + β / (2 * Real.sqrt α) := by
    positivity
  have hsqrt_alpha_sq : (Real.sqrt α) ^ (2 : ℕ) = α := by
    simpa using Real.sq_sqrt hα.le
  -- Square the previous inequality to reach the target upper bound by `α`.
  nlinarith [hsum_le, hsum_nonneg, Real.sqrt_nonneg α, hsqrt_alpha_sq]

/-- Theorem 13.23: if `g` is nonnegative, globally `L_g`-smooth, and globally `σ_g`-strongly
convex, and if the `α`-sublevel set is nonempty, then `C_α = g ⁻¹' Iic α` is
`σ_g / sqrt(2 α L_g)`-strongly convex in the Chapter 13 source-facing sense. -/
theorem sublevelSet_stronglyConvexWith_of_nonnegative_isLSmoothOn_of_strongConvexOn
    (g : E → ℝ) (α : ℝ) (Lg : NNReal) (σg : ℝ) (hα : 0 < α) (hLg : 0 < (Lg : ℝ))
    (hσg : 0 < σg) (hsublevel_nonempty : (g ⁻¹' Iic α).Nonempty)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_smooth : is_l_smooth_on g univ Lg)
    (hg_strong : StrongConvexOn univ σg g) :
    Set.StronglyConvexWith (g ⁻¹' Iic α) (σg / Real.sqrt (2 * α * (Lg : ℝ))) := by
  refine
    { sigma_pos := ?_
      nonempty := hsublevel_nonempty
      strongConvex := ?_ }
  · -- The target modulus is positive because both `σ_g` and `sqrt (2 α L_g)` are positive.
    exact div_pos hσg (Real.sqrt_pos.2 (by positivity))
  · intro x hx y hy t ht z hz
    have hxα : g x ≤ α := by
      simpa using hx
    have hyα : g y ≤ α := by
      simpa using hy
    let c : E := t • x + (1 - t) • y
    let β : ℝ := (σg / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)
    let γ : ℝ :=
      ((σg / Real.sqrt (2 * α * (Lg : ℝ))) / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)
    let δ : ℝ := γ * Real.sqrt ((Lg : ℝ) / 2)
    have h_one_sub_t : 0 ≤ 1 - t := by
      linarith [ht.2]
    have hβ_nonneg : 0 ≤ β := by
      -- The strong-convexity chord deficit is nonnegative on `[0,1]`.
      dsimp [β]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) ht.1) h_one_sub_t)
        (by positivity)
    have hγ_nonneg : 0 ≤ γ := by
      -- The ball radius is nonnegative for the same reason.
      dsimp [γ]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) ht.1) h_one_sub_t)
        (by positivity)
    have hδ_nonneg : 0 ≤ δ := by
      -- The correction term in the completed square is nonnegative.
      dsimp [δ]
      positivity
    have hz_norm : ‖z - c‖ ≤ γ := by
      -- Membership in the closed ball is exactly the norm bound needed in the smoothness step.
      simpa [c, γ, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
    have hgc_le : g c ≤ α - β := by
      -- Strong convexity plus the sublevel assumptions gives the chord-value deficit.
      simpa [c, β] using sublevel_chord_value_le g α σg hg_strong hxα hyα ht
    have hgc_nonneg : 0 ≤ g c := hg_nonneg c
    have halpha_sub_nonneg : 0 ≤ α - β := by
      linarith
    have hβ_le_α : β ≤ α := by
      linarith
    have hz_upper_raw :
        g z ≤ g c + fderiv ℝ g c (z - c) + ((Lg : ℝ) / 2) * ‖z - c‖ ^ (2 : ℕ) := by
      -- Apply the global quadratic upper model at the chord point `c`.
      simpa [c] using is_l_smooth_on_upper_quadratic_univ hg_smooth c z
    have hlinear :
        fderiv ℝ g c (z - c) ≤ Real.sqrt (2 * (Lg : ℝ) * g c) * γ := by
      -- Bound the linear term first by the operator norm and then by the derivative estimate.
      calc
        fderiv ℝ g c (z - c) ≤ ‖(fderiv ℝ g c) (z - c)‖ := by
          exact le_abs_self _
        _ ≤ ‖fderiv ℝ g c‖ * ‖z - c‖ := by
          exact (fderiv ℝ g c).le_opNorm (z - c)
        _ ≤ ‖fderiv ℝ g c‖ * γ := by
          exact mul_le_mul_of_nonneg_left hz_norm (norm_nonneg _)
        _ ≤ Real.sqrt (2 * (Lg : ℝ) * g c) * γ := by
          exact mul_le_mul_of_nonneg_right
            (norm_fderiv_le_sqrt_two_mul_value hg_nonneg hLg hg_smooth c)
            hγ_nonneg
    have hquad :
        ((Lg : ℝ) / 2) * ‖z - c‖ ^ (2 : ℕ) ≤ ((Lg : ℝ) / 2) * γ ^ (2 : ℕ) := by
      -- Replace the distance to the center by the radius bound from the closed-ball hypothesis.
      have hsq : ‖z - c‖ ^ (2 : ℕ) ≤ γ ^ (2 : ℕ) := by
        nlinarith [hz_norm, norm_nonneg (z - c), hγ_nonneg]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    have hsqrt_two_lg :
        Real.sqrt (2 * (Lg : ℝ)) = 2 * Real.sqrt ((Lg : ℝ) / 2) := by
      -- This normalization is the scalar identity behind the square completion.
      calc
        Real.sqrt (2 * (Lg : ℝ)) = Real.sqrt (4 * ((Lg : ℝ) / 2)) := by
          congr 1
          ring
        _ = Real.sqrt (4 : ℝ) * Real.sqrt ((Lg : ℝ) / 2) := by
          rw [Real.sqrt_mul (by positivity : 0 ≤ (4 : ℝ))]
        _ = 2 * Real.sqrt ((Lg : ℝ) / 2) := by
          norm_num
    have hsqrt_cross :
        Real.sqrt (2 * (Lg : ℝ) * g c) =
          2 * Real.sqrt (g c) * Real.sqrt ((Lg : ℝ) / 2) := by
      -- Factor `sqrt (2 L_g g(c))` into the two square-root terms from the completed square.
      calc
        Real.sqrt (2 * (Lg : ℝ) * g c) = Real.sqrt (g c * (2 * (Lg : ℝ))) := by
          congr 1
          ring
        _ = Real.sqrt (g c) * Real.sqrt (2 * (Lg : ℝ)) := by
          rw [Real.sqrt_mul hgc_nonneg]
        _ = Real.sqrt (g c) * (2 * Real.sqrt ((Lg : ℝ) / 2)) := by
          rw [hsqrt_two_lg]
        _ = 2 * Real.sqrt (g c) * Real.sqrt ((Lg : ℝ) / 2) := by
          ring
    have hz_square :
        g z ≤ (Real.sqrt (g c) + δ) ^ (2 : ℕ) := by
      -- Combine the smooth upper estimate with the derivative bound and complete the square.
      calc
        g z ≤ g c + Real.sqrt (2 * (Lg : ℝ) * g c) * γ + ((Lg : ℝ) / 2) * γ ^ (2 : ℕ) := by
          linarith [hz_upper_raw, hlinear, hquad]
        _ = (Real.sqrt (g c) + δ) ^ (2 : ℕ) := by
          have hgc_sq : (Real.sqrt (g c)) ^ (2 : ℕ) = g c := by
            simpa using Real.sq_sqrt hgc_nonneg
          have hlg_sq : (Real.sqrt ((Lg : ℝ) / 2)) ^ (2 : ℕ) = (Lg : ℝ) / 2 := by
            simpa using Real.sq_sqrt (by positivity : 0 ≤ (Lg : ℝ) / 2)
          rw [hsqrt_cross]
          dsimp [δ]
          nlinarith [hgc_sq, hlg_sq]
    have hsqrt_gc_le : Real.sqrt (g c) ≤ Real.sqrt (α - β) := by
      -- The source proof now replaces `g(c)` by the stronger bound `α - β`.
      exact Real.sqrt_le_sqrt hgc_le
    have hsquare_mono :
        (Real.sqrt (g c) + δ) ^ (2 : ℕ) ≤ (Real.sqrt (α - β) + δ) ^ (2 : ℕ) := by
      -- Monotonicity of squaring on the nonnegative half-line transfers the bound on `sqrt (g c)`.
      have hsum_le :
          Real.sqrt (g c) + δ ≤ Real.sqrt (α - β) + δ := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hsqrt_gc_le δ
      have hleft_nonneg : 0 ≤ Real.sqrt (g c) + δ := by
        positivity
      have hright_nonneg : 0 ≤ Real.sqrt (α - β) + δ := by
        positivity
      nlinarith
    have hδ_eq : δ = β / (2 * Real.sqrt α) := by
      -- This is exactly the scalar normalization from the source proof.
      dsimp [δ, γ, β]
      simpa using
        radius_correction_eq_beta_div_two_sqrt_alpha α Lg σg t (‖x - y‖ ^ (2 : ℕ)) hα hLg
    have hz_alpha : g z ≤ α := by
      -- Finish with the scalar square-root estimate from the textbook.
      calc
        g z ≤ (Real.sqrt (g c) + δ) ^ (2 : ℕ) := hz_square
        _ ≤ (Real.sqrt (α - β) + δ) ^ (2 : ℕ) := hsquare_mono
        _ = (Real.sqrt (α - β) + β / (2 * Real.sqrt α)) ^ (2 : ℕ) := by
              rw [hδ_eq]
        _ ≤ α := sqrt_sub_add_beta_div_two_sqrt_alpha_sq_le_alpha α β hα hβ_nonneg hβ_le_α
    simpa using hz_alpha

/-- Bridge/view: the primitive owner `Set.StrongConvex` is obtained from the source-facing theorem
in the positive regime, while the degenerate cases reduce to the zero-modulus convex sublevel-set
statement. -/
theorem sublevelSet_strongConvex_of_nonnegative_isLSmoothOn_of_strongConvexOn
    (g : E → ℝ) (α : ℝ) (Lg : NNReal) (σg : ℝ) (hσg : 0 < σg)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_smooth : is_l_smooth_on g univ Lg)
    (hg_strong : StrongConvexOn univ σg g) :
    Set.StrongConvex (g ⁻¹' Iic α) (σg / Real.sqrt (2 * α * (Lg : ℝ))) := by
  by_cases hsublevel_nonempty : (g ⁻¹' Iic α).Nonempty
  · have hsublevel_convex : Convex ℝ (g ⁻¹' Iic α) := by
      have hg_convexOn : ConvexOn ℝ univ g := (hg_strong.strictConvexOn hσg).convexOn
      simpa using hg_convexOn.convex_le α
    have hsublevel_strongConvex_zero : Set.StrongConvex (g ⁻¹' Iic α) 0 := by
      intro x hx y hy t ht
      rw [show ((0 : ℝ) / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) = 0 by ring,
        Metric.closedBall_zero]
      exact singleton_subset_iff.2 <| by
        simpa [AffineMap.lineMap_apply_module, add_comm]
          using hsublevel_convex.lineMap_mem hy hx ht
    by_cases hα : 0 < α
    · by_cases hLg : 0 < (Lg : ℝ)
      · exact
          (sublevelSet_stronglyConvexWith_of_nonnegative_isLSmoothOn_of_strongConvexOn
            g α Lg σg hα hLg hσg hsublevel_nonempty hg_nonneg hg_smooth hg_strong).strongConvex
      · have hLg_zero : (Lg : ℝ) = 0 := by
          nlinarith [Lg.coe_nonneg]
        simpa [hLg_zero] using hsublevel_strongConvex_zero
    · have hsqrt : Real.sqrt (2 * α * (Lg : ℝ)) = 0 := by
        apply Real.sqrt_eq_zero_of_nonpos
        nlinarith [le_of_not_gt hα, Lg.coe_nonneg]
      simpa [hsqrt] using hsublevel_strongConvex_zero
  · intro x hx
    exact (hsublevel_nonempty ⟨x, hx⟩).elim

end
