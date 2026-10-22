/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_3
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_10

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDualMap)
open WithLp (toLp ofLp)

noncomputable section

section

local notation "E" => EuclideanSpace ℝ (Fin 2)

/- Lemma 8.5 is `source-facing` in the chapter's two-dimensional Wolfe example. Domain sampling
uses the Chapter 2 support-function owner `support_function`, its Euclidean specialization from
`Lemma_2_1`, and the Chapter 3 vector-side owner `euclideanSubdifferentialAt`. The textbook's
objects are already concrete, so this file keeps that concrete `ℝ × ℝ` model: an explicit support
set `C`, the explicit piecewise function from (8.5), and three atomic theorem statements for
parts (a), (b), and (c). -/

/-- The truncated ellipsoidal set `C` from Wolfe's example. -/
def wolfe_example_support_set (γ : ℝ) : Set E :=
  {y | y 0 ^ 2 + y 1 ^ 2 / γ ≤ 1 ∧ 1 / Real.sqrt (1 + γ) ≤ y 0}

/-- Membership in `wolfe_example_support_set γ` is exactly the displayed quadratic inequality
together with the lower bound on the first coordinate. -/
@[simp] theorem mem_wolfe_example_support_set_iff {γ : ℝ} {y : E} :
    y ∈ wolfe_example_support_set γ ↔
      y 0 ^ 2 + y 1 ^ 2 / γ ≤ 1 ∧ 1 / Real.sqrt (1 + γ) ≤ y 0 := by
  -- Unfolding the set recovers the defining conjunction verbatim.
  rfl

/-- The piecewise function `f` from equation (8.5) in Wolfe's example. -/
def wolfe_example_function (γ : ℝ) (x : E) : ℝ :=
  if |x 1| ≤ x 0 then
    Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2)
  else
    (x 0 + γ * |x 1|) / Real.sqrt (1 + γ)

-- Proof sketch: unfold `wolfe_example_function`; the theorem is exactly the defining piecewise
-- formula from equation (8.5).
/-- The Wolfe example function is given by the two branches from equation (8.5). -/
theorem wolfe_example_function_eq_piecewise (γ : ℝ) (x : E) :
    wolfe_example_function γ x =
      if |x 1| ≤ x 0 then
        Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2)
      else
        (x 0 + γ * |x 1|) / Real.sqrt (1 + γ) := by
  -- The statement is exactly the definition of `wolfe_example_function`.
  rfl

/-- Helper for Lemma 8.5: the truncated ellipsoidal support set is nonempty, closed, and convex
for `γ > 0`. -/
lemma wolfe_example_support_set_nonempty_closed_convex
    (γ : ℝ) (hγ : 0 < γ) :
    (wolfe_example_support_set γ).Nonempty ∧
      IsClosed (wolfe_example_support_set γ) ∧
      Convex ℝ (wolfe_example_support_set γ) := by
  have h_nonempty : (wolfe_example_support_set γ).Nonempty := by
    -- The point `(1, 0)` lies on the ellipsoid and satisfies the truncation inequality.
    refine ⟨toLp 2 ![(1 : ℝ), (0 : ℝ)], ?_⟩
    have hsqrt_le : (1 : ℝ) ≤ Real.sqrt (1 + γ) := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + γ) := Real.sqrt_nonneg (1 + γ)
      have hsq : Real.sqrt (1 + γ) ^ 2 = 1 + γ := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith
    have hsqrt_pos : 0 < Real.sqrt (1 + γ) := by
      have : 0 < 1 + γ := by
        linarith
      exact Real.sqrt_pos.2 this
    have hbound : 1 / Real.sqrt (1 + γ) ≤ (1 : ℝ) := by
      have h_inv : (Real.sqrt (1 + γ))⁻¹ ≤ 1 := by
        exact (inv_le_one₀ hsqrt_pos).2 hsqrt_le
      simpa [one_div] using h_inv
    refine ⟨?_, hbound⟩
    norm_num [wolfe_example_support_set]
  have h_closed : IsClosed (wolfe_example_support_set γ) := by
    -- The support set is the intersection of a quadratic sublevel set and a closed halfspace.
    have h_quad : IsClosed {y : E | y 0 ^ 2 + y 1 ^ 2 / γ ≤ 1} := by
      have hcont0 : Continuous fun y : E ↦ y 0 := by
        simpa using
          (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 ↦ ℝ) 0)
      have hcont1 : Continuous fun y : E ↦ y 1 := by
        simpa using
          (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 ↦ ℝ) 1)
      have hcont : Continuous fun y : E ↦ y 0 ^ 2 + y 1 ^ 2 / γ := by
        exact (hcont0.pow 2).add ((hcont1.pow 2).div_const γ)
      simpa using isClosed_le hcont continuous_const
    have h_halfspace : IsClosed {y : E | 1 / Real.sqrt (1 + γ) ≤ y 0} := by
      have hcont0 : Continuous fun y : E ↦ y 0 := by
        simpa using
          (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 ↦ ℝ) 0)
      simpa using isClosed_le continuous_const hcont0
    simpa [wolfe_example_support_set, Set.setOf_and] using h_quad.inter h_halfspace
  have h_convex : Convex ℝ (wolfe_example_support_set γ) := by
    -- Convexity comes from Jensen's inequality for each squared coordinate and the halfspace
    -- description of the truncation constraint.
    have h_quad : Convex ℝ {y : E | y 0 ^ 2 + y 1 ^ 2 / γ ≤ 1} := by
      intro y hy z hz a b ha hb hab
      have hy' : y 0 ^ 2 + y 1 ^ 2 / γ ≤ 1 := hy
      have hz' : z 0 ^ 2 + z 1 ^ 2 / γ ≤ 1 := hz
      have h0 : (a * y 0 + b * z 0) ^ 2 ≤ a * y 0 ^ 2 + b * z 0 ^ 2 := by
        have hsq : 0 ≤ a * b * (y 0 - z 0) ^ 2 := by
          positivity
        nlinarith
      have h1 : (a * y 1 + b * z 1) ^ 2 ≤ a * y 1 ^ 2 + b * z 1 ^ 2 := by
        have hsq : 0 ≤ a * b * (y 1 - z 1) ^ 2 := by
          positivity
        nlinarith
      have h1_div :
          (a * y 1 + b * z 1) ^ 2 / γ ≤ (a * y 1 ^ 2 + b * z 1 ^ 2) / γ := by
        exact div_le_div_of_nonneg_right h1 (le_of_lt hγ)
      have hsum :
          (a * y 0 + b * z 0) ^ 2 + (a * y 1 + b * z 1) ^ 2 / γ ≤
            (a * y 0 ^ 2 + b * z 0 ^ 2) + (a * y 1 ^ 2 + b * z 1 ^ 2) / γ := by
        nlinarith
      have h_rhs :
          (a * y 0 ^ 2 + b * z 0 ^ 2) + (a * y 1 ^ 2 + b * z 1 ^ 2) / γ ≤ 1 := by
        calc
          (a * y 0 ^ 2 + b * z 0 ^ 2) + (a * y 1 ^ 2 + b * z 1 ^ 2) / γ
              = a * (y 0 ^ 2 + y 1 ^ 2 / γ) + b * (z 0 ^ 2 + z 1 ^ 2 / γ) := by ring
          _ ≤ a * 1 + b * 1 := by
            gcongr
          _ = 1 := by
            nlinarith
      exact le_trans hsum h_rhs
    have h_halfspace : Convex ℝ {y : E | 1 / Real.sqrt (1 + γ) ≤ y 0} := by
      intro y hy z hz a b ha hb hab
      have hy' : 1 / Real.sqrt (1 + γ) ≤ y 0 := hy
      have hz' : 1 / Real.sqrt (1 + γ) ≤ z 0 := hz
      change 1 / Real.sqrt (1 + γ) ≤ a * y 0 + b * z 0
      have hya : a * (1 / Real.sqrt (1 + γ)) ≤ a * y 0 := by
        nlinarith
      have hzb : b * (1 / Real.sqrt (1 + γ)) ≤ b * z 0 := by
        nlinarith
      have hsum :
          (a + b) * (1 / Real.sqrt (1 + γ)) ≤ a * y 0 + b * z 0 := by
        nlinarith
      simpa [hab] using hsum
    simpa [wolfe_example_support_set, Set.setOf_and] using h_quad.inter h_halfspace
  exact ⟨h_nonempty, h_closed, h_convex⟩

/-- Helper for Lemma 8.5: in `ℝ²`, the Euclidean pairing with `x` is the displayed coordinate
formula `x₁ y₁ + x₂ y₂`. -/
lemma wolfe_example_pairing_eq (x y : E) :
    ((toDualMap ℝ E x) y : ℝ) = x 0 * y 0 + x 1 * y 1 := by
  -- The `Fin 2` inner product is the sum of the two coordinate products.
  calc
    ((toDualMap ℝ E x) y : ℝ) = inner ℝ x y := by
      rfl
    _ = inner ℝ (x 0) (y 0) + inner ℝ (x 1) (y 1) := by
      simp [PiLp.inner_apply, Fin.sum_univ_two]
    _ = y 0 * x 0 + y 1 * x 1 := by
      change y 0 * starRingEnd ℝ (x 0) + y 1 * starRingEnd ℝ (x 1) = _
      simp
    _ = x 0 * y 0 + x 1 * y 1 := by
      ring

/-- Helper for Lemma 8.5: the real sign recovers the absolute value after multiplication. -/
lemma real_sign_mul_eq_abs (r : ℝ) : Real.sign r * r = |r| := by
  -- Split by the sign of `r` and rewrite the absolute value in each branch.
  by_cases hr_pos : 0 < r
  · simp [Real.sign_of_pos hr_pos, abs_of_pos hr_pos]
  · by_cases hr_zero : r = 0
    · simp [hr_zero]
    · have hr_neg : r < 0 := lt_of_le_of_ne (le_of_not_gt hr_pos) hr_zero
      simp [Real.sign_of_neg hr_neg, abs_of_neg hr_neg]

/-- Helper for Lemma 8.5: right-multiplying by the real sign also recovers the absolute value. -/
private lemma real_mul_sign_eq_abs (r : ℝ) : r * Real.sign r = |r| := by
  -- This is the commuted version of `real_sign_mul_eq_abs`.
  simpa [mul_comm] using real_sign_mul_eq_abs r

/-- Helper for Lemma 8.5: the square of a real sign is at most `1`. -/
lemma real_sign_sq_le_one (r : ℝ) : Real.sign r ^ 2 ≤ 1 := by
  -- The real sign can only be `-1`, `0`, or `1`.
  rcases Real.sign_apply_eq r with hneg | hzero | hpos
  · nlinarith [hneg]
  · nlinarith [hzero]
  · nlinarith [hpos]

/-- Helper for Lemma 8.5: away from the origin, the square of the real sign is exactly `1`. -/
lemma real_sign_sq_eq_one {r : ℝ} (hr : r ≠ 0) : Real.sign r ^ 2 = 1 := by
  -- A nonzero real sign is either `-1` or `1`.
  rcases Real.sign_apply_eq_of_ne_zero r hr with hneg | hpos
  · nlinarith [hneg]
  · nlinarith [hpos]

/-- Helper for Lemma 8.5: the ellipsoidal inequality
`y₁^2 + y₂^2 / γ ≤ 1` bounds the pairing by the ellipsoidal norm
`√(x₁^2 + γ x₂^2)`. -/
lemma wolfe_example_pairing_le_ellipsoid_norm
    (γ : ℝ) (hγ : 0 < γ) (x y : E)
    (hy : y 0 ^ 2 + y 1 ^ 2 / γ ≤ 1) :
    ((toDualMap ℝ E x) y : ℝ) ≤ Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) := by
  have hsq_weighted :
      γ * (x 0 * y 0 + x 1 * y 1) ^ 2 ≤
        (x 0 ^ 2 + γ * x 1 ^ 2) * (γ * y 0 ^ 2 + y 1 ^ 2) := by
    -- The weighted Cauchy-Schwarz inequality is the expanded nonnegativity of a square.
    have haux : 0 ≤ (x 0 * y 1 - γ * x 1 * y 0) ^ 2 := sq_nonneg _
    nlinarith
  have hy_scaled : γ * y 0 ^ 2 + y 1 ^ 2 ≤ γ := by
    -- Rewriting the ellipsoidal constraint clears the denominator `γ`.
    have hy_mul := mul_le_mul_of_nonneg_left hy (le_of_lt hγ)
    have hrewrite : γ * (y 0 ^ 2 + y 1 ^ 2 / γ) = γ * y 0 ^ 2 + y 1 ^ 2 := by
      field_simp [hγ.ne']
    simpa [hrewrite] using hy_mul
  have hmul :
      γ * (x 0 * y 0 + x 1 * y 1) ^ 2 ≤ γ * (x 0 ^ 2 + γ * x 1 ^ 2) := by
    -- The ellipsoidal constraint bounds the weighted quadratic form by `γ`.
    calc
      γ * (x 0 * y 0 + x 1 * y 1) ^ 2
          ≤ (x 0 ^ 2 + γ * x 1 ^ 2) * (γ * y 0 ^ 2 + y 1 ^ 2) := hsq_weighted
      _ ≤ (x 0 ^ 2 + γ * x 1 ^ 2) * γ := by
        have hx_nonneg : 0 ≤ x 0 ^ 2 + γ * x 1 ^ 2 := by
          positivity
        gcongr
      _ = γ * (x 0 ^ 2 + γ * x 1 ^ 2) := by
        ring
  have hsq0 : (x 0 * y 0 + x 1 * y 1) ^ 2 ≤ x 0 ^ 2 + γ * x 1 ^ 2 := by
    -- Divide the previous estimate by the positive weight `γ`.
    nlinarith [hmul]
  have hsq : (((toDualMap ℝ E x) y : ℝ)) ^ 2 ≤ x 0 ^ 2 + γ * x 1 ^ 2 := by
    -- Re-express the coordinate quadratic estimate in pairing form.
    rw [wolfe_example_pairing_eq]
    exact hsq0
  have hsqrt_sq :
      Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) ^ 2 = x 0 ^ 2 + γ * x 1 ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have habs :
      |((toDualMap ℝ E x) y : ℝ)| ≤ Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) := by
    -- Squaring transfers the estimate from the pairing to the square root bound.
    have hsq' :
        (((toDualMap ℝ E x) y : ℝ)) ^ 2 ≤
          Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) ^ 2 := by
      simpa [hsqrt_sq] using hsq
    simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using (sq_le_sq.1 hsq')
  exact le_trans (le_abs_self _) habs

/-- Helper for Lemma 8.5: every point of the truncated ellipsoid satisfies
`y₁ + |y₂| ≤ √(1 + γ)`. This is the supporting-line estimate behind the active-boundary branch. -/
lemma wolfe_example_support_set_sum_abs_le
    (γ : ℝ) (hγ : 0 < γ) {y : E}
    (hy : y ∈ wolfe_example_support_set γ) :
    y 0 + |y 1| ≤ Real.sqrt (1 + γ) := by
  let x : E := toLp 2 ![(1 : ℝ), Real.sign (y 1)]
  have hpair :
      ((toDualMap ℝ E x) y : ℝ) ≤ Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) :=
    wolfe_example_pairing_le_ellipsoid_norm γ hγ x y hy.1
  have hpair_eq : ((toDualMap ℝ E x) y : ℝ) = y 0 + |y 1| := by
    -- Choosing the second coefficient as `sign(y₂)` turns the pairing into `y₁ + |y₂|`.
    dsimp [x]
    change ((toDualMap ℝ E (toLp 2 ![(1 : ℝ), Real.sign (y 1)] : E)) y : ℝ) =
      y 0 + |y 1|
    rw [wolfe_example_pairing_eq]
    simp
    rw [real_sign_mul_eq_abs]
  have hsqrt_eq :
      Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) =
        Real.sqrt (1 + γ * Real.sign (y 1) ^ 2) := by
    -- The chosen witness has first coordinate `1` and second coordinate `sign(y₂)`.
    congr 1
    dsimp [x]
    ring
  have hsqrt_le :
      Real.sqrt (1 + γ * Real.sign (y 1) ^ 2) ≤ Real.sqrt (1 + γ) := by
    have hsign_sq_nonneg : 0 ≤ Real.sign (y 1) ^ 2 := sq_nonneg _
    have hsign_sq_le : Real.sign (y 1) ^ 2 ≤ 1 := real_sign_sq_le_one (y 1)
    have hmul : γ * Real.sign (y 1) ^ 2 ≤ γ * 1 := by
      gcongr
    have harg : 1 + γ * Real.sign (y 1) ^ 2 ≤ 1 + γ := by
      nlinarith [hmul]
    exact Real.sqrt_le_sqrt harg
  calc
    y 0 + |y 1| = ((toDualMap ℝ E x) y : ℝ) := by
      rw [hpair_eq]
    _ ≤ Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) := hpair
    _ = Real.sqrt (1 + γ * Real.sign (y 1) ^ 2) := hsqrt_eq
    _ ≤ Real.sqrt (1 + γ) := hsqrt_le

/-- Helper for Lemma 8.5: on the branch `|x₂| ≤ x₁`, the normalized ellipsoidal point is a
maximizer of the pairing over the truncated ellipsoid and yields the value
`√(x₁^2 + γ x₂^2)`. -/
lemma argmax_wolfe_support_set_on_ellipsoidal_region
    (γ : ℝ) (hγ : 0 < γ) (x : E)
    (hx_region : |x 1| ≤ x 0) (hx_ne : x ≠ 0) :
    IsGreatest
      ((fun y : E ↦ (((toDualMap ℝ E x) y : ℝ) : EReal)) '' wolfe_example_support_set γ)
      ((Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) : ℝ) : EReal) := by
  let s : ℝ := x 0 ^ 2 + γ * x 1 ^ 2
  let yStar : E := toLp 2 ![(x 0 / Real.sqrt s), ((γ * x 1) / Real.sqrt s)]
  have hx0_nonneg : 0 ≤ x 0 := by
    linarith [abs_nonneg (x 1), hx_region]
  have hx1_sq : x 1 ^ 2 ≤ x 0 ^ 2 := by
    have habs_le : |x 1| ≤ |x 0| := by
      simpa [abs_of_nonneg hx0_nonneg] using hx_region
    exact (sq_le_sq.2 habs_le)
  have hs_pos : 0 < s := by
    -- In the active-ellipsoid branch, the weighted radius vanishes only at the excluded origin.
    by_cases hx0_zero : x 0 = 0
    · have hx1_zero : x 1 = 0 := by
        have : |x 1| ≤ 0 := by
          simpa [hx0_zero] using hx_region
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
      apply False.elim
      apply hx_ne
      ext i
      fin_cases i
      · simp [hx0_zero]
      · simp [hx1_zero]
    · have hx0_sq_pos : 0 < x 0 ^ 2 := by
        positivity
      dsimp [s]
      nlinarith
  have hyStar_mem : yStar ∈ wolfe_example_support_set γ := by
    -- Route correction: we certify the source proof's normalized ellipsoidal maximizer directly,
    -- rather than switching to a different optimization route.
    dsimp [yStar, s]
    have hs_ne : Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hs_pos
    constructor
    · -- The witness lies on the ellipsoidal boundary.
      have hellipsoid_eq :
          (x 0 / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2)) ^ 2 +
              ((γ * x 1) / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2)) ^ 2 / γ = 1 := by
        field_simp [hs_ne, hγ.ne']
        ring_nf
        rw [Real.sq_sqrt]
        positivity
      exact le_of_eq hellipsoid_eq
    · -- The region hypothesis is exactly the feasibility test for the truncation inequality.
      have hsqrt1_pos : 0 < Real.sqrt (1 + γ) := by
        apply Real.sqrt_pos.2
        linarith
      have hbound :
          1 / Real.sqrt (1 + γ) ≤ x 0 / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) := by
        have hsqrt_pos : 0 < Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) := Real.sqrt_pos.2 hs_pos
        have hbound_core :
            Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) ≤ x 0 * Real.sqrt (1 + γ) := by
          have haux : x 0 ^ 2 + γ * x 1 ^ 2 ≤ x 0 ^ 2 * (1 + γ) := by
            nlinarith
          have hsqrt1_sq : Real.sqrt (1 + γ) ^ 2 = 1 + γ := by
            rw [Real.sq_sqrt]
            linarith
          have hsqrt_sq :
              Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) ^ 2 = x 0 ^ 2 + γ * x 1 ^ 2 := by
            rw [Real.sq_sqrt]
            positivity
          have hsq :
              Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) ^ 2 ≤
                (x 0 * Real.sqrt (1 + γ)) ^ 2 := by
            nlinarith [haux, hsqrt1_sq, hsqrt_sq]
          have habs :
              |Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2)| ≤ |x 0 * Real.sqrt (1 + γ)| :=
            (sq_le_sq.1 hsq)
          have hnonneg_rhs : 0 ≤ x 0 * Real.sqrt (1 + γ) := by
            positivity
          simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hnonneg_rhs] using habs
        have hdiv :
            Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) / Real.sqrt (1 + γ) ≤ x 0 := by
          exact (div_le_iff₀ hsqrt1_pos).2 hbound_core
        apply (le_div_iff₀ hsqrt_pos).2
        simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv
      simpa [yStar] using hbound
  have hyStar_val :
      (((toDualMap ℝ E x) yStar : ℝ) : EReal) = ((Real.sqrt s : ℝ) : EReal) := by
    -- Evaluating the pairing at the normalized point collapses to the ellipsoidal norm.
    exact_mod_cast (by
      rw [wolfe_example_pairing_eq]
      simp
      have hs_ne : Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 hs_pos
      field_simp [hs_ne]
      ring_nf
      rw [Real.sq_sqrt]
      positivity :
        ((toDualMap ℝ E x)
          (toLp 2 ![x 0 / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2),
            (γ * x 1) / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2)] : E) : ℝ) =
          Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2))
  refine ⟨?_, ?_⟩
  · exact ⟨yStar, hyStar_mem, hyStar_val⟩
  · rintro _ ⟨y, hy, rfl⟩
    change (((toDualMap ℝ E x) y : ℝ) : EReal) ≤ ((Real.sqrt s : ℝ) : EReal)
    exact_mod_cast wolfe_example_pairing_le_ellipsoid_norm γ hγ x y hy.1

/-- Helper for Lemma 8.5: on the active-truncation branch `x₁ < |x₂|` with `x₂ ≠ 0`, the
maximizer is the exposed boundary point
`(1 / √(1 + γ), γ sign(x₂) / √(1 + γ))`. -/
lemma argmax_wolfe_support_set_on_truncation_boundary
    (γ : ℝ) (hγ : 0 < γ) (x : E)
    (hx_region : x 0 < |x 1|) (hx1 : x 1 ≠ 0) :
    IsGreatest
      ((fun y : E ↦ (((toDualMap ℝ E x) y : ℝ) : EReal)) '' wolfe_example_support_set γ)
      ((((x 0 + γ * |x 1|) / Real.sqrt (1 + γ) : ℝ) : EReal)) := by
  let yStar : E := toLp 2 ![(1 / Real.sqrt (1 + γ)),
    ((γ * Real.sign (x 1)) / Real.sqrt (1 + γ))]
  have hyStar_mem : yStar ∈ wolfe_example_support_set γ := by
    -- The displayed boundary point lies on the truncation slice of the ellipsoid.
    dsimp [yStar]
    constructor
    · have hsqrt_ne : Real.sqrt (1 + γ) ≠ 0 := by
        apply Real.sqrt_ne_zero'.2
        linarith
      have hsign_sq : Real.sign (x 1) ^ 2 = 1 := real_sign_sq_eq_one hx1
      have hellipsoid_eq :
          (1 / Real.sqrt (1 + γ)) ^ 2 +
              ((γ * Real.sign (x 1)) / Real.sqrt (1 + γ)) ^ 2 / γ = 1 := by
        field_simp [hsqrt_ne, hγ.ne']
        rw [hsign_sq]
        ring_nf
        rw [Real.sq_sqrt]
        linarith
      exact le_of_eq hellipsoid_eq
    · simp
  have hyStar_val :
      (((toDualMap ℝ E x) yStar : ℝ) : EReal) =
        ((((x 0 + γ * |x 1|) / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal) := by
    -- The sign choice aligns the second coordinate with the objective coefficient `x₂`.
    dsimp [yStar]
    exact_mod_cast (by
      have hsqrt_ne : Real.sqrt (1 + γ) ≠ 0 := by
        apply Real.sqrt_ne_zero'.2
        linarith
      change ((toDualMap ℝ E x)
          (toLp 2 ![(1 / Real.sqrt (1 + γ)),
            (γ * Real.sign (x 1)) / Real.sqrt (1 + γ)] : E) : ℝ) =
          (x 0 + γ * |x 1|) / Real.sqrt (1 + γ)
      rw [wolfe_example_pairing_eq]
      simp
      field_simp [hsqrt_ne]
      rw [mul_assoc, real_mul_sign_eq_abs]
      )
  refine ⟨?_, ?_⟩
  · exact ⟨yStar, hyStar_mem, hyStar_val⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hsum_abs : y 0 + |y 1| ≤ Real.sqrt (1 + γ) :=
      wolfe_example_support_set_sum_abs_le γ hγ hy
    have htail :
        y 0 - 1 / Real.sqrt (1 + γ) + |y 1| ≤ γ / Real.sqrt (1 + γ) := by
      -- The support-set estimate rewrites the residual budget after fixing the first coordinate.
      have hsqrt_eq :
          Real.sqrt (1 + γ) = 1 / Real.sqrt (1 + γ) + γ / Real.sqrt (1 + γ) := by
        have hsqrt_ne : Real.sqrt (1 + γ) ≠ 0 := by
          apply Real.sqrt_ne_zero'.2
          linarith
        field_simp [hsqrt_ne]
        rw [Real.sq_sqrt]
        linarith
      nlinarith [hsum_abs, hsqrt_eq]
    have hobj_eq :
        ((toDualMap ℝ E x) y : ℝ) =
          x 0 / Real.sqrt (1 + γ) +
            x 0 * (y 0 - 1 / Real.sqrt (1 + γ)) + x 1 * y 1 := by
      rw [wolfe_example_pairing_eq]
      ring
    have hupper_real :
        ((toDualMap ℝ E x) y : ℝ) ≤ (x 0 + γ * |x 1|) / Real.sqrt (1 + γ) := by
      rw [hobj_eq]
      have hgap_nonneg : 0 ≤ y 0 - 1 / Real.sqrt (1 + γ) := by
        linarith [hy.2]
      have hstep1 :
          x 0 * (y 0 - 1 / Real.sqrt (1 + γ)) ≤
            |x 1| * (y 0 - 1 / Real.sqrt (1 + γ)) := by
        nlinarith [hx_region.le, hgap_nonneg]
      have hstep2 : x 1 * y 1 ≤ |x 1| * |y 1| := by
        calc
          x 1 * y 1 ≤ |x 1 * y 1| := le_abs_self _
          _ = |x 1| * |y 1| := by rw [abs_mul]
      have hsum_gap :
          |x 1| * (y 0 - 1 / Real.sqrt (1 + γ)) + |x 1| * |y 1| ≤
            |x 1| * (γ / Real.sqrt (1 + γ)) := by
        have htail_mul :
            |x 1| * (y 0 - 1 / Real.sqrt (1 + γ) + |y 1|) ≤
              |x 1| * (γ / Real.sqrt (1 + γ)) := by
          exact mul_le_mul_of_nonneg_left htail (abs_nonneg (x 1))
        nlinarith [htail_mul]
      have hmid :
          x 0 / Real.sqrt (1 + γ) + x 0 * (y 0 - 1 / Real.sqrt (1 + γ)) + x 1 * y 1 ≤
            x 0 / Real.sqrt (1 + γ) +
              (|x 1| * (y 0 - 1 / Real.sqrt (1 + γ)) + |x 1| * |y 1|) := by
        nlinarith [hstep1, hstep2]
      calc
        x 0 / Real.sqrt (1 + γ) + x 0 * (y 0 - 1 / Real.sqrt (1 + γ)) + x 1 * y 1
            ≤ x 0 / Real.sqrt (1 + γ) +
                (|x 1| * (y 0 - 1 / Real.sqrt (1 + γ)) + |x 1| * |y 1|) := hmid
        _ ≤ x 0 / Real.sqrt (1 + γ) + |x 1| * (γ / Real.sqrt (1 + γ)) := by
          gcongr
        _ = (x 0 + γ * |x 1|) / Real.sqrt (1 + γ) := by
          ring
    change (((toDualMap ℝ E x) y : ℝ) : EReal) ≤
      ((((x 0 + γ * |x 1|) / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal)
    exact_mod_cast hupper_real

/-- Helper for Lemma 8.5: on the negative `x₁`-axis, the support value is attained at the point
`(1 / √(1 + γ), 0)` on the truncation boundary. -/
lemma argmax_wolfe_support_set_on_negative_axis
    (γ : ℝ) (hγ : 0 < γ) (x : E)
    (hx0 : x 0 < 0) (hx1 : x 1 = 0) :
    IsGreatest
      ((fun y : E ↦ (((toDualMap ℝ E x) y : ℝ) : EReal)) '' wolfe_example_support_set γ)
      (((x 0 / Real.sqrt (1 + γ) : ℝ) : EReal)) := by
  let yStar : E := toLp 2 ![(1 / Real.sqrt (1 + γ)), (0 : ℝ)]
  have hyStar_mem : yStar ∈ wolfe_example_support_set γ := by
    -- On the negative axis only the truncation constraint remains active.
    dsimp [yStar]
    constructor
    · have hsqrt_ne : Real.sqrt (1 + γ) ≠ 0 := by
        apply Real.sqrt_ne_zero'.2
        linarith
      have hsq_eq :
          (1 / Real.sqrt (1 + γ)) ^ 2 + (0 : ℝ) ^ 2 / γ = 1 / (1 + γ) := by
        field_simp [hsqrt_ne, hγ.ne']
        rw [Real.sq_sqrt]
        · linarith
        · linarith
      have hsq : (1 / Real.sqrt (1 + γ)) ^ 2 + (0 : ℝ) ^ 2 / γ ≤ 1 := by
        rw [hsq_eq]
        have hfrac : (1 + γ)⁻¹ ≤ 1 := by
          exact (inv_le_one₀ (by linarith)).2 (by linarith)
        simpa [one_div] using hfrac
      exact hsq
    · simp
  have hyStar_val :
      (((toDualMap ℝ E x) yStar : ℝ) : EReal) =
        ((((x 0 / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal)) := by
    -- The second coordinate vanishes because `x₂ = 0`.
    dsimp [yStar]
    exact_mod_cast (by
      change ((toDualMap ℝ E x) (toLp 2 ![(1 / Real.sqrt (1 + γ)), (0 : ℝ)] : E) : ℝ) =
          x 0 / Real.sqrt (1 + γ)
      rw [wolfe_example_pairing_eq, hx1]
      simp
      ring)
  refine ⟨?_, ?_⟩
  · exact ⟨yStar, hyStar_mem, hyStar_val⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy0_ge : 1 / Real.sqrt (1 + γ) ≤ y 0 := hy.2
    have hupper_real : x 0 * y 0 ≤ x 0 / Real.sqrt (1 + γ) := by
      have hmul :
          x 0 * y 0 ≤ x 0 * (1 / Real.sqrt (1 + γ)) := by
        exact mul_le_mul_of_nonpos_left hy0_ge hx0.le
      simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hmul
    change (((toDualMap ℝ E x) y : ℝ) : EReal) ≤
      ((((x 0 / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal))
    rw [wolfe_example_pairing_eq, hx1]
    have hupper_ereal :
        (((x 0 * y 0 : ℝ) : EReal)) ≤
          ((((x 0 / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal)) := by
      exact_mod_cast hupper_real
    simpa using hupper_ereal

-- Proof sketch: solve the support-function maximization problem over
-- `wolfe_example_support_set γ` by splitting into the same two cases as in the textbook proof.
-- In the region `|x₂| ≤ x₁`, the active point is the normalized ellipsoidal boundary point; in
-- the complementary region, the linear constraint `y₁ = 1 / √(1 + γ)` is active and the
-- remaining one-dimensional maximization gives the affine branch.
/-- Lemma 8.5 (1): for `γ > 0`, the piecewise Wolfe example function from equation (8.5) is the
support function `σ_C` of the set
`C = {(y₁, y₂) | y₁^2 + y₂^2 / γ ≤ 1, y₁ ≥ 1 / √(1 + γ)}`. -/
theorem wolfe_example_function_eq_support_function
    (γ : ℝ) (hγ : 0 < γ) :
    (fun x : E ↦ (wolfe_example_function γ x : EReal)) =
      fun x : E ↦ support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) :=
by
  funext x
  by_cases hx_zero : x = 0
  · subst x
    rcases (wolfe_example_support_set_nonempty_closed_convex γ hγ).1 with ⟨y, hy⟩
    have hgreatest :
        IsGreatest
          ((fun z : E ↦ (((toDualMap ℝ E (0 : E)) z : ℝ) : EReal)) ''
            wolfe_example_support_set γ)
          (0 : EReal) := by
      -- At the origin the objective is constantly zero, so every feasible point is maximizing.
      refine ⟨?_, ?_⟩
      · exact ⟨y, hy, by simp⟩
      · rintro _ ⟨z, hz, rfl⟩
        simp
    have hsupport :
        support_function (wolfe_example_support_set γ) (toDualMap ℝ E (0 : E)) = 0 := by
      exact support_function_eq_of_isGreatest_image _ _ hgreatest
    simpa [wolfe_example_function] using hsupport.symm
  · by_cases hx_region : |x 1| ≤ x 0
    · -- This is Case I of the source proof: the normalized ellipsoidal maximizer remains feasible.
      have hsupport :
          support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) =
            ((Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) : ℝ) : EReal) := by
        exact support_function_eq_of_isGreatest_image _ _
          (argmax_wolfe_support_set_on_ellipsoidal_region γ hγ x hx_region hx_zero)
      simpa [wolfe_example_function, hx_region] using hsupport.symm
    · have hx_boundary : x 0 < |x 1| := lt_of_not_ge hx_region
      by_cases hx1 : x 1 = 0
      · have hx0_neg : x 0 < 0 := by
          simpa [hx1, abs_zero] using hx_boundary
        -- This is the `x₂ = 0` subcase of Case II from the source proof.
        have hx_not : ¬ |x 1| ≤ x 0 := by
          simpa [hx1, abs_zero] using not_le_of_gt hx0_neg
        have hx0_not_nonneg : ¬ 0 ≤ x 0 := not_le_of_gt hx0_neg
        have hsupport :
            support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) =
              ((((x 0 / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal)) := by
          exact support_function_eq_of_isGreatest_image _ _
            (argmax_wolfe_support_set_on_negative_axis γ hγ x hx0_neg hx1)
        simpa [wolfe_example_function, hx1, abs_zero, hx_not, hx0_not_nonneg] using hsupport.symm
      · -- This is the exposed-point subcase of Case II from the source proof.
        have hx_not : ¬ |x 1| ≤ x 0 := not_le_of_gt hx_boundary
        have hsupport :
            support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) =
              ((((x 0 + γ * |x 1|) / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal) := by
          exact support_function_eq_of_isGreatest_image _ _
            (argmax_wolfe_support_set_on_truncation_boundary γ hγ x hx_boundary hx1)
        simpa [wolfe_example_function, hx_not] using hsupport.symm

-- Proof sketch: combine part (1) with the chapter theorem
-- `support_function_closed_and_convex` for the Euclidean specialization of support functions, then
-- project to the lower-semicontinuity component.
/-- Lemma 8.5 (2): for `γ > 0`, the Wolfe example function is closed, i.e. lower
semicontinuous. -/
theorem wolfe_example_function_lowerSemicontinuous
    (γ : ℝ) (hγ : 0 < γ) :
    LowerSemicontinuous (fun x : E ↦ (wolfe_example_function γ x : EReal)) := by
  -- Rewrite the function as a support function and apply the chapter support-function theorem.
  rw [wolfe_example_function_eq_support_function γ hγ]
  exact (support_function_closed_and_convex (wolfe_example_support_set γ)).1

-- Proof sketch: combine part (1) with the chapter theorem
-- `support_function_closed_and_convex` for the Euclidean specialization of support functions, then
-- project to the convexity component.
/-- Lemma 8.5 (3): for `γ > 0`, the Wolfe example function is convex in the chapter owner
sense. -/
theorem wolfe_example_function_is_convex
    (γ : ℝ) (hγ : 0 < γ) :
    is_convex_function (fun x : E ↦ (wolfe_example_function γ x : EReal)) := by
  -- Rewrite the function as a support function and keep the convexity component of the same API.
  rw [wolfe_example_function_eq_support_function γ hγ]
  exact (support_function_closed_and_convex (wolfe_example_support_set γ)).2

/-- Helper for Lemma 8.5: the conjugate of the Wolfe support function is the indicator of the
support set itself, because that set is already closed and convex for `γ > 0`. -/
lemma wolfe_example_support_function_conjugate_eq_indicator
    (γ : ℝ) (hγ : 0 < γ) (z : E) :
    conjugate_function
        (fun y : E ↦ support_function (wolfe_example_support_set γ) (toDualMap ℝ E y))
        (toDualMap ℝ E z) =
      extendedIndicator (wolfe_example_support_set γ) z := by
  -- The chapter support-function conjugacy theorem collapses `closure (convexHull C)` back to `C`.
  rcases wolfe_example_support_set_nonempty_closed_convex γ hγ with ⟨_, hclosed, hconvex⟩
  have h :=
    conjugate_function_support_function_apply_eq_extendedIndicator_closure_convexHull
      (wolfe_example_support_set γ) z
  simpa only [conjugate_function_primal_apply, closure_eq_iff_isClosed.mpr hclosed,
    hconvex.convexHull_eq] using h

/-- Helper for Lemma 8.5: the Euclidean pairing is symmetric in the two arguments. -/
lemma wolfe_example_pairing_comm (x z : E) :
    (((toDualMap ℝ E z) x : ℝ) : EReal) = (((toDualMap ℝ E x) z : ℝ) : EReal) := by
  -- Both sides are the same coordinate formula `x₁ z₁ + x₂ z₂`.
  exact_mod_cast (by
    rw [wolfe_example_pairing_eq, wolfe_example_pairing_eq]
    ring)

/-- Helper for Lemma 8.5: Euclidean subgradients of the Wolfe example are exactly the support-set
points where the pairing with `x` attains the support value. -/
lemma mem_euclideanSubdifferentialAt_wolfe_example_function_iff
    (γ : ℝ) (hγ : 0 < γ) (x z : E) :
    z ∈ euclideanSubdifferentialAt (wolfe_example_function γ) x ↔
      z ∈ wolfe_example_support_set γ ∧
        (((toDualMap ℝ E x) z : ℝ) : EReal) =
          support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) := by
  -- Rewrite `f` as the support function `σ_C`, then apply Fenchel--Young equality and collapse
  -- the conjugate to the indicator of `C`.
  rcases wolfe_example_support_set_nonempty_closed_convex γ hγ with ⟨hCne, _, _⟩
  have hne_bot :
      ∀ w : E,
        (fun y : E ↦ support_function (wolfe_example_support_set γ) (toDualMap ℝ E y)) w ≠ ⊥ := by
    intro w
    simpa using
      support_function_ne_bot (wolfe_example_support_set γ) hCne
        (toDualMap ℝ E w : Module.Dual ℝ E)
  constructor
  · intro hz
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential] at hz
    have hz_support :
        ((toDualMap ℝ E z : StrongDual ℝ E) : Module.Dual ℝ E) ∈
          subdifferential
            (fun y : E ↦ support_function (wolfe_example_support_set γ) (toDualMap ℝ E y)) x := by
      -- Part (a) identifies the real-valued Wolfe example with the same support function.
      simpa [wolfe_example_function_eq_support_function γ hγ] using hz
    have hfenchel :=
      (pairing_eq_add_conjugate_iff_mem_subdifferential
        (fun y : E ↦ support_function (wolfe_example_support_set γ) (toDualMap ℝ E y))
        hne_bot x (((toDualMap ℝ E z : StrongDual ℝ E) : Module.Dual ℝ E))).2 hz_support
    by_cases hzC : z ∈ wolfe_example_support_set γ
    · refine ⟨hzC, ?_⟩
      -- On `C`, the indicator term vanishes, so Fenchel--Young equality becomes the argmax equation.
      have hindicator :
          extendedIndicator (wolfe_example_support_set γ) z = 0 := by
        simp [extendedIndicator, hzC]
      rw [wolfe_example_support_function_conjugate_eq_indicator γ hγ z, hindicator, add_zero] at hfenchel
      calc
        (((toDualMap ℝ E x) z : ℝ) : EReal)
            = (((toDualMap ℝ E z) x : ℝ) : EReal) := by
              symm
              exact wolfe_example_pairing_comm x z
        _ = support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) := hfenchel
    · -- Outside `C`, the indicator is `⊤`, which cannot match the finite pairing on the left.
      have hindicator :
          extendedIndicator (wolfe_example_support_set γ) z = ⊤ := by
        simp [extendedIndicator, hzC]
      rw [wolfe_example_support_function_conjugate_eq_indicator γ hγ z, hindicator] at hfenchel
      have htop :
          support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) + ⊤ = ⊤ :=
        EReal.add_top_of_ne_bot (hne_bot x)
      rw [htop] at hfenchel
      exfalso
      simp at hfenchel
  · rintro ⟨hzC, hpair⟩
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential]
    have hfenchel :
        (((toDualMap ℝ E z) x : ℝ) : EReal) =
          support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) +
            conjugate_function
              (fun y : E ↦ support_function (wolfe_example_support_set γ) (toDualMap ℝ E y))
              (((toDualMap ℝ E z : StrongDual ℝ E) : Module.Dual ℝ E)) := by
      -- Membership in `C` turns the conjugate back into `0`, so the given support-value equality
      -- is exactly Fenchel--Young equality.
      have hindicator :
          extendedIndicator (wolfe_example_support_set γ) z = 0 := by
        simp [extendedIndicator, hzC]
      rw [wolfe_example_support_function_conjugate_eq_indicator γ hγ z, hindicator, add_zero]
      calc
        (((toDualMap ℝ E z) x : ℝ) : EReal)
            = (((toDualMap ℝ E x) z : ℝ) : EReal) := wolfe_example_pairing_comm x z
        _ = support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) := hpair
    have hz_support :
        ((toDualMap ℝ E z : StrongDual ℝ E) : Module.Dual ℝ E) ∈
          subdifferential
            (fun y : E ↦ support_function (wolfe_example_support_set γ) (toDualMap ℝ E y)) x :=
      (pairing_eq_add_conjugate_iff_mem_subdifferential
        (fun y : E ↦ support_function (wolfe_example_support_set γ) (toDualMap ℝ E y))
        hne_bot x (((toDualMap ℝ E z : StrongDual ℝ E) : Module.Dual ℝ E))).1 hfenchel
    -- Return from the support-function model to the original real-valued Wolfe example.
    simpa [wolfe_example_function_eq_support_function γ hγ] using hz_support

-- Proof sketch: use part (1) to rewrite the function as the support function of
-- `wolfe_example_support_set γ`, then identify Euclidean subgradients of a support function with
-- argmax points. The origin case yields the full support set.
/-- Lemma 8.5 (4): for `γ > 0`, the Euclidean/vector-side subdifferential of the Wolfe example
function at the origin is the support set `C`. -/
theorem euclidean_subdifferentialAt_wolfe_example_function_at_zero
    (γ : ℝ) (hγ : 0 < γ) :
    euclideanSubdifferentialAt (wolfe_example_function γ) (0 : E) =
      wolfe_example_support_set γ := by
  ext z
  constructor
  · intro hz
    -- At the origin, every subgradient must lie in the support set by the Fenchel bridge.
    exact (mem_euclideanSubdifferentialAt_wolfe_example_function_iff γ hγ (0 : E) z).1 hz |>.1
  · intro hzC
    have hsupport_zero :
        support_function (wolfe_example_support_set γ) (toDualMap ℝ E (0 : E)) = 0 := by
      -- Part (a) already computes the support value at the origin as the zero branch of `f`.
      have hzero :=
        congrArg (fun f : E → EReal => f (0 : E)) (wolfe_example_function_eq_support_function γ hγ)
      simpa [wolfe_example_function] using hzero.symm
    have hz_argmax :
        z ∈ wolfe_example_support_set γ ∧
          (((toDualMap ℝ E (0 : E)) z : ℝ) : EReal) =
            support_function (wolfe_example_support_set γ) (toDualMap ℝ E (0 : E)) := by
      refine ⟨hzC, ?_⟩
      simpa using hsupport_zero.symm
    -- Conversely, every point of `C` attains the zero support value at the origin.
    exact (mem_euclideanSubdifferentialAt_wolfe_example_function_iff γ hγ (0 : E) z).2 hz_argmax

/-- Helper for Lemma 8.5: if a support-set point attains the ellipsoidal support value on the
branch `|x₂| ≤ x₁`, then it is the normalized ellipsoidal boundary point. -/
lemma eq_normalized_ellipsoid_point_of_mem_support_set_of_pairing_eq
    (γ : ℝ) (hγ : 0 < γ) (x z : E)
    (hx_region : |x 1| ≤ x 0) (hx0 : x 0 ≠ 0)
    (hz : z ∈ wolfe_example_support_set γ)
    (hpair :
      (((toDualMap ℝ E x) z : ℝ) : EReal) =
        ((Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) : ℝ) : EReal)) :
    z = toLp 2 ![(x 0 / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2)),
      ((γ * x 1) / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2))] := by
  let s : ℝ := x 0 ^ 2 + γ * x 1 ^ 2
  have hx0_nonneg : 0 ≤ x 0 := by
    linarith [abs_nonneg (x 1), hx_region]
  have hx0_pos : 0 < x 0 := by
    -- The active ellipsoidal branch together with `x₁ ≠ 0` forces the first coordinate positive.
    by_cases hx0_pos : 0 < x 0
    · exact hx0_pos
    · have hx0_eq : x 0 = 0 := by
        linarith
      exact False.elim (hx0 hx0_eq)
  have hs_pos : 0 < s := by
    -- The weighted ellipsoidal radius is strictly positive because `x₁ > 0`.
    dsimp [s]
    nlinarith [hx0_pos, hγ]
  have hsqrt_pos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs_pos
  have hpair_coord : x 0 * z 0 + x 1 * z 1 = Real.sqrt s := by
    -- Convert the `EReal` maximizing equation back to the real coordinate pairing.
    have hpair_real : ((toDualMap ℝ E x) z : ℝ) = Real.sqrt s := by
      exact_mod_cast hpair
    calc
      x 0 * z 0 + x 1 * z 1 = ((toDualMap ℝ E x) z : ℝ) := by
        rw [wolfe_example_pairing_eq]
      _ = Real.sqrt s := hpair_real
  have hz_scaled : γ * z 0 ^ 2 + z 1 ^ 2 ≤ γ := by
    -- Clearing the denominator in the ellipsoidal constraint gives the weighted quadratic bound.
    have hz_mul := mul_le_mul_of_nonneg_left hz.1 (le_of_lt hγ)
    have hrewrite : γ * (z 0 ^ 2 + z 1 ^ 2 / γ) = γ * z 0 ^ 2 + z 1 ^ 2 := by
      field_simp [hγ.ne']
    simpa [hrewrite] using hz_mul
  have hweighted :
      γ * (x 0 * z 0 + x 1 * z 1) ^ 2 ≤
        s * (γ * z 0 ^ 2 + z 1 ^ 2) := by
    -- This is the same weighted Cauchy-Schwarz estimate used for the support-value upper bound.
    have haux : 0 ≤ (x 0 * z 1 - γ * x 1 * z 0) ^ 2 := sq_nonneg _
    dsimp [s]
    nlinarith
  have hmid :
      s * (γ * z 0 ^ 2 + z 1 ^ 2) ≤ s * γ := by
    have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
    nlinarith [hz_scaled, hs_nonneg]
  have hpair_sq : (x 0 * z 0 + x 1 * z 1) ^ 2 = s := by
    -- Squaring the attained support value fixes the pairing norm exactly.
    have hsqrt_sq : Real.sqrt s ^ 2 = s := by
      rw [Real.sq_sqrt]
      exact le_of_lt hs_pos
    nlinarith [hpair_coord, hsqrt_sq]
  have hz_boundary : γ * z 0 ^ 2 + z 1 ^ 2 = γ := by
    -- Equality in the upper-bound chain forces `z` onto the ellipsoidal boundary.
    nlinarith [hweighted, hmid, hpair_sq, hs_pos]
  have hcross_sq : (x 0 * z 1 - γ * x 1 * z 0) ^ 2 = 0 := by
    -- Equality in weighted Cauchy-Schwarz gives the cross-relation between the coordinates.
    have haux : 0 ≤ (x 0 * z 1 - γ * x 1 * z 0) ^ 2 := sq_nonneg _
    dsimp [s] at hpair_sq
    nlinarith [haux, hpair_sq, hz_boundary]
  have hcross : x 0 * z 1 = γ * x 1 * z 0 := by
    nlinarith [hcross_sq]
  have hz0_mul : s * z 0 = x 0 * Real.sqrt s := by
    -- Multiply the pairing equation by `x₁` and use the cross-relation to isolate `z₁`.
    have hx0_pair :
        x 0 * (x 0 * z 0 + x 1 * z 1) = x 0 * Real.sqrt s := by
      exact congrArg (fun t : ℝ ↦ x 0 * t) hpair_coord
    have hcross_mul : x 0 * (x 1 * z 1) = γ * x 1 ^ 2 * z 0 := by
      nlinarith [hcross]
    dsimp [s]
    nlinarith [hx0_pair, hcross_mul]
  have hz0_eq : z 0 = x 0 / Real.sqrt s := by
    -- The positive square root allows us to solve uniquely for the first coordinate.
    have hsqrt_sq : (Real.sqrt s) ^ 2 = s := by
      rw [Real.sq_sqrt]
      exact le_of_lt hs_pos
    have hz0_times : z 0 * Real.sqrt s = x 0 := by
      apply (mul_right_cancel₀ hsqrt_pos.ne')
      calc
        (z 0 * Real.sqrt s) * Real.sqrt s = z 0 * (Real.sqrt s) ^ 2 := by
          ring
        _ = z 0 * s := by
          rw [hsqrt_sq]
        _ = x 0 * Real.sqrt s := by
          simpa [mul_comm] using hz0_mul
    apply (eq_div_iff hsqrt_pos.ne').2
    simpa [mul_comm] using hz0_times
  have hz1_eq : z 1 = (γ * x 1) / Real.sqrt s := by
    -- The cross-relation now determines the second coordinate as well.
    have hz0_times : z 0 * Real.sqrt s = x 0 := by
      exact (eq_div_iff hsqrt_pos.ne').1 hz0_eq
    have hx0_mul :
        x 0 * (z 1 * Real.sqrt s) = x 0 * (γ * x 1) := by
      calc
        x 0 * (z 1 * Real.sqrt s) = (x 0 * z 1) * Real.sqrt s := by
          ring
        _ = (γ * x 1 * z 0) * Real.sqrt s := by
          rw [hcross]
        _ = γ * x 1 * x 0 := by
          calc
            (γ * x 1 * z 0) * Real.sqrt s = γ * x 1 * (z 0 * Real.sqrt s) := by
              ring
            _ = γ * x 1 * x 0 := by
              rw [hz0_times]
        _ = x 0 * (γ * x 1) := by
          ring
    have hz1_times : z 1 * Real.sqrt s = γ * x 1 := by
      exact mul_left_cancel₀ hx0 hx0_mul
    apply (eq_div_iff hsqrt_pos.ne').2
    simpa [mul_comm] using hz1_times
  ext i
  fin_cases i
  · simpa [hz0_eq, s]
  · simpa [hz1_eq, s]

-- Proof sketch: in the region `|x₂| ≤ x₁` with `x₁ ≠ 0`, the support-function maximizer is the
-- normalized ellipsoidal boundary point `(x₁, γ x₂) / √(x₁^2 + γ x₂^2)`, so the Euclidean
-- subdifferential is the corresponding singleton.
/-- Lemma 8.5 (5): for `γ > 0`, in the region `|x₂| ≤ x₁` with `x₁ ≠ 0`, the Euclidean
subdifferential is the singleton normalized boundary point
`(x₁, γ x₂) / √(x₁^2 + γ x₂^2)`. -/
theorem euclidean_subdifferentialAt_wolfe_example_function_on_ellipsoidal_region
    (γ : ℝ) (hγ : 0 < γ) (x : E) (hx_region : |x 1| ≤ x 0) (hx0 : x 0 ≠ 0) :
    euclideanSubdifferentialAt (wolfe_example_function γ) x =
      {toLp 2 ![(x 0 / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2)),
        ((γ * x 1) / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2))]} := by
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    apply hx0
    simpa [hx_zero]
  have hgreatest :=
    argmax_wolfe_support_set_on_ellipsoidal_region γ hγ x hx_region hx_ne
  have hsupport :
      support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) =
        ((Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) : ℝ) : EReal) := by
    exact support_function_eq_of_isGreatest_image _ _ hgreatest
  ext z
  constructor
  · intro hzsub
    -- Use the Fenchel bridge and then collapse the maximizer set with the equality-case lemma.
    rcases (mem_euclideanSubdifferentialAt_wolfe_example_function_iff γ hγ x z).1 hzsub with
      ⟨hzC, hzpair⟩
    have hzpair_value :
        (((toDualMap ℝ E x) z : ℝ) : EReal) =
          ((Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) : ℝ) : EReal) := by
      rw [hsupport] at hzpair
      exact hzpair
    have hz_eq :
        z = toLp 2 ![(x 0 / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2)),
          ((γ * x 1) / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2))] :=
      eq_normalized_ellipsoid_point_of_mem_support_set_of_pairing_eq
        γ hγ x z hx_region hx0 hzC hzpair_value
    simpa [Set.mem_singleton_iff] using hz_eq
  · intro hzsingle
    rcases Set.mem_singleton_iff.1 hzsingle with rfl
    -- Conversely, read the explicit maximizer back from the already-proved support-value theorem.
    have hmem_image :
        ((Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2) : ℝ) : EReal) ∈
          ((fun y : E ↦ (((toDualMap ℝ E x) y : ℝ) : EReal)) ''
            wolfe_example_support_set γ) := hgreatest.1
    rcases hmem_image with ⟨y, hyC, hyval⟩
    have hy_eq :
        y = toLp 2 ![(x 0 / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2)),
          ((γ * x 1) / Real.sqrt (x 0 ^ 2 + γ * x 1 ^ 2))] :=
      eq_normalized_ellipsoid_point_of_mem_support_set_of_pairing_eq
        γ hγ x y hx_region hx0 hyC hyval
    refine (mem_euclideanSubdifferentialAt_wolfe_example_function_iff γ hγ x _).2 ?_
    refine ⟨?_, ?_⟩
    · simpa [hy_eq] using hyC
    · rw [hsupport]
      simpa [hy_eq] using hyval

/-- Helper for Lemma 8.5: fixing the first coordinate to the truncation boundary turns the support
set condition into the vertical interval constraint on the second coordinate. -/
lemma mem_wolfe_example_support_set_truncation_face_iff
    (γ : ℝ) (hγ : 0 < γ) {z : E}
    (hz0 : z 0 = 1 / Real.sqrt (1 + γ)) :
    z ∈ wolfe_example_support_set γ ↔
      z 1 ∈ Set.Icc (-(γ / Real.sqrt (1 + γ))) (γ / Real.sqrt (1 + γ)) := by
  have hsqrt_pos : 0 < Real.sqrt (1 + γ) := Real.sqrt_pos.2 (by linarith)
  have hsqrt_ne : Real.sqrt (1 + γ) ≠ 0 := hsqrt_pos.ne'
  have hone_add_ne : 1 + γ ≠ 0 := by
    linarith
  have hbound_nonneg : 0 ≤ γ / Real.sqrt (1 + γ) := by
    positivity
  have hsqrt_sq : Real.sqrt (1 + γ) ^ 2 = 1 + γ := by
    rw [Real.sq_sqrt]
    linarith
  have hface_sq : (1 / Real.sqrt (1 + γ)) ^ 2 = 1 / (1 + γ) := by
    field_simp [hsqrt_ne]
    rw [hsqrt_sq]
  have hsq_bound : (γ / Real.sqrt (1 + γ)) ^ 2 = γ ^ 2 / (1 + γ) := by
    field_simp [hsqrt_ne]
    rw [hsqrt_sq]
  rw [mem_wolfe_example_support_set_iff]
  constructor
  · intro hz
    -- On the truncation face, the quadratic feasibility condition is exactly a one-dimensional
    -- square bound on `z₂`.
    have hzdiv : z 1 ^ 2 / γ ≤ γ / (1 + γ) := by
      rw [hz0, hface_sq] at hz
      have hsum_eq : 1 - 1 / (1 + γ) = γ / (1 + γ) := by
        field_simp [hone_add_ne]
        ring
      have htmp : z 1 ^ 2 / γ ≤ 1 - 1 / (1 + γ) := by
        nlinarith [hz.1]
      calc
        z 1 ^ 2 / γ ≤ 1 - 1 / (1 + γ) := htmp
        _ = γ / (1 + γ) := hsum_eq
    have hzsq : z 1 ^ 2 ≤ (γ / Real.sqrt (1 + γ)) ^ 2 := by
      have hzmul := mul_le_mul_of_nonneg_left hzdiv (le_of_lt hγ)
      have hzsq' : z 1 ^ 2 ≤ γ ^ 2 / (1 + γ) := by
        have hzlhs : γ * (z 1 ^ 2 / γ) = z 1 ^ 2 := by
          field_simp [hγ.ne']
        have hzrhs : γ * (γ / (1 + γ)) = γ ^ 2 / (1 + γ) := by
          field_simp [hone_add_ne]
        simpa [hzlhs, hzrhs] using hzmul
      simpa [hsq_bound] using hzsq'
    have habs : |z 1| ≤ γ / Real.sqrt (1 + γ) := by
      have habs' : |z 1| ≤ |γ / Real.sqrt (1 + γ)| := (sq_le_sq.1 hzsq)
      simpa [abs_of_nonneg hbound_nonneg] using habs'
    simpa [Set.mem_Icc, abs_le] using habs
  · intro hz1
    -- Conversely, squaring the interval bound recovers the ellipsoidal inequality.
    have habs : |z 1| ≤ γ / Real.sqrt (1 + γ) := by
      simpa [Set.mem_Icc, abs_le] using hz1
    have hzsq : z 1 ^ 2 ≤ (γ / Real.sqrt (1 + γ)) ^ 2 := by
      have habs' : |z 1| ≤ |γ / Real.sqrt (1 + γ)| := by
        simpa [abs_of_nonneg hbound_nonneg] using habs
      exact sq_le_sq.2 habs'
    have hzsq' : z 1 ^ 2 ≤ γ ^ 2 / (1 + γ) := by
      simpa [hsq_bound] using hzsq
    constructor
    · rw [hz0, hface_sq]
      have hzdiv := div_le_div_of_nonneg_right hzsq' (le_of_lt hγ)
      have hrhs : (γ ^ 2 / (1 + γ)) / γ = γ / (1 + γ) := by
        field_simp [hγ.ne', hone_add_ne]
      have hzdiv' : z 1 ^ 2 / γ ≤ γ / (1 + γ) := by
        simpa [hrhs] using hzdiv
      have hsum : 1 / (1 + γ) + z 1 ^ 2 / γ ≤ 1 / (1 + γ) + γ / (1 + γ) := by
        gcongr
      have hsum_eq : 1 / (1 + γ) + γ / (1 + γ) = 1 := by
        field_simp [hone_add_ne]
      nlinarith [hsum, hsum_eq]
    · simpa [hz0]

/-- Helper for Lemma 8.5: if a support-set point attains the active truncation support value, then
it is the exposed sign point on that truncation face. -/
lemma eq_truncation_sign_point_of_mem_support_set_of_pairing_eq
    (γ : ℝ) (hγ : 0 < γ) (x z : E)
    (hx_region : x 0 < |x 1|) (hx1 : x 1 ≠ 0)
    (hz : z ∈ wolfe_example_support_set γ)
    (hpair :
      (((toDualMap ℝ E x) z : ℝ) : EReal) =
        ((((x 0 + γ * |x 1|) / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal)) :
    z = toLp 2 ![(1 / Real.sqrt (1 + γ)),
      ((γ * Real.sign (x 1)) / Real.sqrt (1 + γ))] := by
  let a : ℝ := 1 / Real.sqrt (1 + γ)
  let b : ℝ := γ / Real.sqrt (1 + γ)
  have hsqrt_pos : 0 < Real.sqrt (1 + γ) := Real.sqrt_pos.2 (by linarith)
  have hpair_real :
      ((toDualMap ℝ E x) z : ℝ) = (x 0 + γ * |x 1|) / Real.sqrt (1 + γ) := by
    exact_mod_cast hpair
  have hgap_nonneg : 0 ≤ z 0 - a := by
    -- The support-set constraint says the first coordinate lies to the right of the truncation face.
    dsimp [a]
    linarith [hz.2]
  have hsum_abs : z 0 + |z 1| ≤ Real.sqrt (1 + γ) :=
    wolfe_example_support_set_sum_abs_le γ hγ hz
  have htail : z 0 - a + |z 1| ≤ b := by
    -- Subtract the fixed truncation offset from the supporting-line inequality.
    have hsqrt_eq :
        Real.sqrt (1 + γ) = 1 / Real.sqrt (1 + γ) + γ / Real.sqrt (1 + γ) := by
      field_simp [hsqrt_pos.ne']
      rw [Real.sq_sqrt]
      linarith
    dsimp [a, b]
    nlinarith [hsum_abs, hsqrt_eq]
  have hpair_gap : x 0 * (z 0 - a) + x 1 * z 1 = |x 1| * b := by
    -- Rewrite the attained value as a budget identity on the truncation face residual.
    rw [wolfe_example_pairing_eq] at hpair_real
    calc
      x 0 * (z 0 - a) + x 1 * z 1 = (x 0 * z 0 + x 1 * z 1) - x 0 * a := by
        ring
      _ = (x 0 + γ * |x 1|) / Real.sqrt (1 + γ) - x 0 * a := by
        rw [hpair_real]
      _ = |x 1| * b := by
        dsimp [a, b]
        field_simp [hsqrt_pos.ne']
        ring
  have hz1_budget : |z 1| ≤ b - (z 0 - a) := by
    nlinarith [htail]
  have hstep1 : x 1 * z 1 ≤ |x 1| * |z 1| := by
    calc
      x 1 * z 1 ≤ |x 1 * z 1| := le_abs_self _
      _ = |x 1| * |z 1| := by rw [abs_mul]
  have hstep2 : |x 1| * |z 1| ≤ |x 1| * (b - (z 0 - a)) := by
    -- The remaining vertical budget is bounded by the truncation-face interval length.
    have hbudget_nonneg : 0 ≤ b - (z 0 - a) := by
      nlinarith [htail, abs_nonneg (z 1)]
    gcongr
  have hupper :
      x 0 * (z 0 - a) + x 1 * z 1 ≤
        |x 1| * b + (x 0 - |x 1|) * (z 0 - a) := by
    -- The strict inequality `x₁ < |x₂|` makes any positive first-coordinate gap impossible.
    nlinarith [hstep1, hstep2]
  have hz0_eq : z 0 = a := by
    have hcoeff_neg : x 0 - |x 1| < 0 := by
      linarith
    have hgap_zero : z 0 - a = 0 := by
      nlinarith [hpair_gap, hupper, hcoeff_neg, hgap_nonneg]
    dsimp [a] at hgap_zero ⊢
    linarith
  have hpair_z1 : x 1 * z 1 = |x 1| * b := by
    -- Once the first-coordinate gap vanishes, the entire support value comes from the second
    -- coordinate term.
    calc
      x 1 * z 1 = |x 1| * b - x 0 * (z 0 - a) := by
        nlinarith [hpair_gap]
      _ = |x 1| * b := by
        rw [hz0_eq]
        ring
  have hz1_eq : z 1 = (γ * Real.sign (x 1)) / Real.sqrt (1 + γ) := by
    -- The sign of the exposed point follows from the sign of `x₂`.
    rcases lt_or_gt_of_ne hx1 with hx1_neg | hx1_pos
    · have hz1_eq_neg : z 1 = -b := by
        rw [abs_of_neg hx1_neg] at hpair_z1
        nlinarith
      calc
        z 1 = -b := hz1_eq_neg
        _ = (γ * Real.sign (x 1)) / Real.sqrt (1 + γ) := by
          rw [Real.sign_of_neg hx1_neg]
          dsimp [b]
          ring
    · have hz1_eq_pos : z 1 = b := by
        rw [abs_of_pos hx1_pos] at hpair_z1
        nlinarith
      calc
        z 1 = b := hz1_eq_pos
        _ = (γ * Real.sign (x 1)) / Real.sqrt (1 + γ) := by
          rw [Real.sign_of_pos hx1_pos]
          dsimp [b]
          ring
  ext i
  fin_cases i
  · simpa [a] using hz0_eq
  · simpa using hz1_eq

-- Proof sketch: in the region `x₁ < |x₂|` with `x₂ ≠ 0`, the linear truncation constraint is
-- active, and the exposed maximizer is the boundary point
-- `(1 / √(1 + γ), γ sign(x₂) / √(1 + γ))`.
/-- Lemma 8.5 (6): for `γ > 0`, in the region `x₁ < |x₂|` with `x₂ ≠ 0`, the Euclidean
subdifferential is the singleton boundary point
`(1 / √(1 + γ), γ sign(x₂) / √(1 + γ))`. -/
theorem euclidean_subdifferentialAt_wolfe_example_function_on_truncation_boundary
    (γ : ℝ) (hγ : 0 < γ) (x : E) (hx_region : x 0 < |x 1|) (hx1 : x 1 ≠ 0) :
    euclideanSubdifferentialAt (wolfe_example_function γ) x =
      {toLp 2 ![(1 / Real.sqrt (1 + γ)),
        ((γ * Real.sign (x 1)) / Real.sqrt (1 + γ))]} :=
by
  have hgreatest :=
    argmax_wolfe_support_set_on_truncation_boundary γ hγ x hx_region hx1
  have hsupport :
      support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) =
        ((((x 0 + γ * |x 1|) / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal) := by
    exact support_function_eq_of_isGreatest_image _ _ hgreatest
  ext z
  constructor
  · intro hzsub
    -- The Fenchel bridge reduces the subgradient computation to the exposed-point argmax equation.
    rcases (mem_euclideanSubdifferentialAt_wolfe_example_function_iff γ hγ x z).1 hzsub with
      ⟨hzC, hzpair⟩
    have hzpair_value :
        (((toDualMap ℝ E x) z : ℝ) : EReal) =
          ((((x 0 + γ * |x 1|) / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal) := by
      rw [hsupport] at hzpair
      exact hzpair
    have hz_eq :
        z = toLp 2 ![(1 / Real.sqrt (1 + γ)),
          ((γ * Real.sign (x 1)) / Real.sqrt (1 + γ))] :=
      eq_truncation_sign_point_of_mem_support_set_of_pairing_eq
        γ hγ x z hx_region hx1 hzC hzpair_value
    simpa [Set.mem_singleton_iff] using hz_eq
  · intro hzsingle
    rcases Set.mem_singleton_iff.1 hzsingle with rfl
    -- Conversely, recover the explicit maximizing witness from the already-proved support-value
    -- theorem and identify it by the same equality-case lemma.
    have hmem_image :
        ((((x 0 + γ * |x 1|) / Real.sqrt (1 + γ) : ℝ) : ℝ) : EReal) ∈
          ((fun y : E ↦ (((toDualMap ℝ E x) y : ℝ) : EReal)) ''
            wolfe_example_support_set γ) := hgreatest.1
    rcases hmem_image with ⟨y, hyC, hyval⟩
    have hy_eq :
        y = toLp 2 ![(1 / Real.sqrt (1 + γ)),
          ((γ * Real.sign (x 1)) / Real.sqrt (1 + γ))] :=
      eq_truncation_sign_point_of_mem_support_set_of_pairing_eq
        γ hγ x y hx_region hx1 hyC hyval
    refine (mem_euclideanSubdifferentialAt_wolfe_example_function_iff γ hγ x _).2 ?_
    refine ⟨?_, ?_⟩
    · simpa [hy_eq] using hyC
    · rw [hsupport]
      simpa [hy_eq] using hyval

-- Proof sketch: on the negative `x₁`-axis, the active supporting points are exactly those on the
-- vertical truncation segment with first coordinate `1 / √(1 + γ)` and second coordinate between
-- `-γ / √(1 + γ)` and `γ / √(1 + γ)`.
/-- Lemma 8.5 (7): for `γ > 0`, on the negative `x₁`-axis, the Euclidean subdifferential is the
vertical segment `{1 / √(1 + γ)} × [-γ / √(1 + γ), γ / √(1 + γ)]`. -/
theorem euclidean_subdifferentialAt_wolfe_example_function_on_negative_axis
    (γ : ℝ) (hγ : 0 < γ) (x : E) (hx0 : x 0 < 0) (hx1 : x 1 = 0) :
    euclideanSubdifferentialAt (wolfe_example_function γ) x =
      {z : E |
        z 0 = 1 / Real.sqrt (1 + γ) ∧
          z 1 ∈ Set.Icc (-(γ / Real.sqrt (1 + γ))) (γ / Real.sqrt (1 + γ))} :=
by
  have hgreatest := argmax_wolfe_support_set_on_negative_axis γ hγ x hx0 hx1
  have hsupport :
      support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) =
        (((x 0 / Real.sqrt (1 + γ) : ℝ) : EReal)) := by
    exact support_function_eq_of_isGreatest_image _ _ hgreatest
  ext z
  constructor
  · intro hzsub
    -- On the negative axis, the support value determines the first coordinate, and the support
    -- set itself determines the remaining interval.
    rcases (mem_euclideanSubdifferentialAt_wolfe_example_function_iff γ hγ x z).1 hzsub with
      ⟨hzC, hzpair⟩
    have hzpair_value :
        (((toDualMap ℝ E x) z : ℝ) : EReal) =
          (((x 0 / Real.sqrt (1 + γ) : ℝ) : EReal)) := by
      rw [hsupport] at hzpair
      exact hzpair
    have hzpair_real : ((toDualMap ℝ E x) z : ℝ) = x 0 / Real.sqrt (1 + γ) := by
      exact_mod_cast hzpair_value
    have hz0_eq : z 0 = 1 / Real.sqrt (1 + γ) := by
      rw [wolfe_example_pairing_eq, hx1] at hzpair_real
      have hx0_ne : x 0 ≠ 0 := by
        linarith
      exact mul_left_cancel₀ hx0_ne (by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hzpair_real)
    refine ⟨hz0_eq, ?_⟩
    exact (mem_wolfe_example_support_set_truncation_face_iff γ hγ hz0_eq).1 hzC
  · rintro ⟨hz0_eq, hz1_mem⟩
    -- Every point on the vertical truncation segment lies in `C` and attains the same support
    -- value because the second coordinate coefficient vanishes.
    have hzC : z ∈ wolfe_example_support_set γ := by
      exact (mem_wolfe_example_support_set_truncation_face_iff γ hγ hz0_eq).2 hz1_mem
    have hz_argmax :
        z ∈ wolfe_example_support_set γ ∧
          (((toDualMap ℝ E x) z : ℝ) : EReal) =
            support_function (wolfe_example_support_set γ) (toDualMap ℝ E x) := by
      refine ⟨hzC, ?_⟩
      rw [hsupport]
      exact_mod_cast (by
        rw [wolfe_example_pairing_eq, hx1, hz0_eq]
        ring :
          ((toDualMap ℝ E x) z : ℝ) = x 0 / Real.sqrt (1 + γ))
    exact (mem_euclideanSubdifferentialAt_wolfe_example_function_iff γ hγ x z).2 hz_argmax

end
