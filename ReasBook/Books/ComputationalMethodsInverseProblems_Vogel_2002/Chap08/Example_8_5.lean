/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Example_8_5.Penalty
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4.Conjugate

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- The whole-space conjugate functional of `smoothNormPenalty β` is the
supremum from Example 8.5. -/
theorem smoothNormPenalty_conjugateFunctional_univ_def
    (β : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    conjugateFunctional Set.univ (smoothNormPenalty β) y =
      sSup (Set.range fun x : EuclideanSpace ℝ (Fin d) ↦
        ((inner ℝ x y - smoothNormPenalty β x : ℝ) : EReal)) := by
  simpa using conjugateFunctional_univ_eq_sSup_range (smoothNormPenalty β) y

/-- Helper for Example 8.5: squaring `smoothNormPenalty β x` removes the outer
square root. -/
lemma smoothNormPenalty_sq
    (β : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    (smoothNormPenalty β x) ^ 2 = ‖x‖ ^ 2 + β ^ 2 := by
  -- Unfold the definition and square the defining square root.
  simpa [smoothNormPenalty_def, pow_two] using
    Real.sq_sqrt (show 0 ≤ ‖x‖ ^ 2 + β ^ 2 by positivity)

/-- Helper for Example 8.5: `smoothNormPenalty β x` is positive when `β > 0`. -/
lemma smoothNormPenalty_pos
    (β : ℝ) (hβ : 0 < β) (x : EuclideanSpace ℝ (Fin d)) :
    0 < smoothNormPenalty β x := by
  -- The radicand contains the strictly positive term `β ^ 2`.
  rw [smoothNormPenalty_def]
  refine Real.sqrt_pos.2 ?_
  nlinarith [sq_pos_of_pos hβ]

/-- Helper for Example 8.5: the smooth penalty dominates the Euclidean norm. -/
lemma norm_le_smoothNormPenalty
    (β : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ≤ smoothNormPenalty β x := by
  -- Compare squares; both sides are nonnegative.
  rw [smoothNormPenalty_def]
  have hrad : 0 ≤ ‖x‖ ^ 2 + β ^ 2 := by
    positivity
  refine (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 ?_
  have hsq : ‖x‖ ^ 2 ≤ (Real.sqrt (‖x‖ ^ 2 + β ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt hrad]
    nlinarith
  simpa [pow_two] using hsq

/-- Helper for Example 8.5: each dual term over the closed unit ball is bounded
above by `smoothNormPenalty β x`. -/
lemma smoothNormPenaltyBoundsDualTerm
    (β : ℝ) (hβ : 0 < β) (x y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 1) :
    inner ℝ x y + β * Real.sqrt (1 - ‖y‖ ^ 2) ≤ smoothNormPenalty β x := by
  have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
  have hy' : 0 ≤ 1 - ‖y‖ ^ 2 := by
    nlinarith
  have hsq :
      (‖x‖ * ‖y‖ + β * Real.sqrt (1 - ‖y‖ ^ 2)) ^ 2 ≤ ‖x‖ ^ 2 + β ^ 2 := by
    -- This is the two-dimensional Cauchy-Schwarz inequality after squaring.
    nlinarith [sq_nonneg (‖x‖ * Real.sqrt (1 - ‖y‖ ^ 2) - β * ‖y‖),
      Real.sq_sqrt hy']
  have hbound :
      ‖x‖ * ‖y‖ + β * Real.sqrt (1 - ‖y‖ ^ 2) ≤ Real.sqrt (‖x‖ ^ 2 + β ^ 2) := by
    -- Both sides are nonnegative, so square comparison is enough.
    have hsq' :
        (‖x‖ * ‖y‖ + β * Real.sqrt (1 - ‖y‖ ^ 2)) ^ 2
          ≤ (Real.sqrt (‖x‖ ^ 2 + β ^ 2)) ^ 2 := by
      simpa [Real.sq_sqrt (show 0 ≤ ‖x‖ ^ 2 + β ^ 2 by positivity)] using hsq
    refine (sq_le_sq₀ ?_ (Real.sqrt_nonneg _)).1 ?_
    · positivity
    · exact hsq'
  -- First bound the inner product by Cauchy-Schwarz, then apply the scalar estimate.
  calc
    inner ℝ x y + β * Real.sqrt (1 - ‖y‖ ^ 2)
      ≤ ‖x‖ * ‖y‖ + β * Real.sqrt (1 - ‖y‖ ^ 2) := by
        gcongr
        exact real_inner_le_norm x y
    _ ≤ Real.sqrt (‖x‖ ^ 2 + β ^ 2) := hbound
    _ = smoothNormPenalty β x := by rw [smoothNormPenalty_def]

/-- Helper for Example 8.5: the explicit vector
`(smoothNormPenalty β x)⁻¹ • x` lies in the closed unit ball and attains the
closed-ball supremum formula. -/
lemma smoothNormPenaltyDualWitnessAttains
    (β : ℝ) (hβ : 0 < β) (x : EuclideanSpace ℝ (Fin d)) :
    let y0 : EuclideanSpace ℝ (Fin d) := (smoothNormPenalty β x)⁻¹ • x
    y0 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
      inner ℝ x y0 + β * Real.sqrt (1 - ‖y0‖ ^ 2) = smoothNormPenalty β x := by
  let s := smoothNormPenalty β x
  let y0 : EuclideanSpace ℝ (Fin d) := s⁻¹ • x
  have hs_pos : 0 < s := by
    -- The denominator is strictly positive because `β > 0`.
    simpa [s] using smoothNormPenalty_pos β hβ x
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hs_sq : s ^ 2 = ‖x‖ ^ 2 + β ^ 2 := by
    simpa [s] using smoothNormPenalty_sq β x
  have hy0_norm : ‖y0‖ = ‖x‖ / s := by
    -- The witness is a positive scalar multiple of `x`.
    simp [y0, s, norm_smul, abs_of_pos hs_pos, div_eq_mul_inv, mul_comm]
  have hy0_mem : y0 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    -- Membership reduces to `‖x‖ ≤ smoothNormPenalty β x`.
    rw [mem_closedBall_zero_iff, hy0_norm]
    rw [div_le_one hs_pos]
    simpa [s] using norm_le_smoothNormPenalty β x
  have hy0_sq : ‖y0‖ ^ 2 = ‖x‖ ^ 2 / s ^ 2 := by
    rw [hy0_norm, div_eq_mul_inv, pow_two]
    ring
  have hradicand :
      1 - ‖y0‖ ^ 2 = β ^ 2 / s ^ 2 := by
    refine (eq_div_iff_mul_eq (pow_ne_zero 2 hs_ne)).2 ?_
    rw [hy0_sq]
    field_simp [hs_ne]
    nlinarith [hs_sq]
  have hsqrt :
      Real.sqrt (1 - ‖y0‖ ^ 2) = β / s := by
    have hdivsq : β ^ 2 / s ^ 2 = (β / s) ^ 2 := by
      field_simp [pow_two, hs_ne]
    have hβs_nonneg : 0 ≤ β / s := by
      positivity
    -- Rewrite the radicand as the square of `β / s`.
    rw [hradicand, hdivsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hβs_nonneg]
  have hinner :
      inner ℝ x y0 = ‖x‖ ^ 2 / s := by
    -- Expanding the inner product isolates the scalar factor `s⁻¹`.
    calc
      inner ℝ x y0 = inner ℝ x (s⁻¹ • x) := by rfl
      _ = s⁻¹ * inner ℝ x x := by rw [real_inner_smul_right]
      _ = s⁻¹ * ‖x‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = ‖x‖ ^ 2 / s := by rw [div_eq_mul_inv, mul_comm]
  refine by
    subst y0
    constructor
    · exact hy0_mem
    · -- The witness value collapses to `s = smoothNormPenalty β x`.
      calc
        inner ℝ x (s⁻¹ • x) + β * Real.sqrt (1 - ‖s⁻¹ • x‖ ^ 2)
          = ‖x‖ ^ 2 / s + β * (β / s) := by rw [hinner, hsqrt]
        _ = (‖x‖ ^ 2 + β ^ 2) / s := by
          ring_nf
        _ = s ^ 2 / s := by rw [hs_sq]
        _ = s := by rw [pow_two, mul_div_cancel_left₀ s hs_ne]
        _ = smoothNormPenalty β x := by rfl

/-- Helper for Example 8.5: the explicit optimizer
`(β / √(1 - ‖y‖ ^ 2)) • y` attains the finite conjugate value when `‖y‖ < 1`. -/
lemma smoothNormPenaltyConjugateInteriorWitness
    (β : ℝ) (hβ : 0 < β) (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ < 1) :
    let x0 : EuclideanSpace ℝ (Fin d) := (β / Real.sqrt (1 - ‖y‖ ^ 2)) • y
    inner ℝ x0 y - smoothNormPenalty β x0 = (-β) * Real.sqrt (1 - ‖y‖ ^ 2) := by
  let c := Real.sqrt (1 - ‖y‖ ^ 2)
  let x0 : EuclideanSpace ℝ (Fin d) := (β / c) • y
  have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
  have hc_pos : 0 < c := by
    -- Strict interior points give a positive square-root denominator.
    apply Real.sqrt_pos.2
    nlinarith
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hnormsq : c ^ 2 = 1 - ‖y‖ ^ 2 := by
    simpa [c, pow_two] using
      Real.sq_sqrt (show 0 ≤ 1 - ‖y‖ ^ 2 by nlinarith)
  have hx0_norm : ‖x0‖ = (β / c) * ‖y‖ := by
    -- The scaling factor is positive, so absolute values disappear.
    simp [x0, c, norm_smul, Real.norm_eq_abs, abs_of_nonneg, hβ.le, hc_pos.le, mul_comm]
  have hsmooth_sq :
      (smoothNormPenalty β x0) ^ 2 = (β / c) ^ 2 := by
    -- Squaring reduces the identity to a rational expression in `‖y‖` and `c`.
    rw [smoothNormPenalty_sq, hx0_norm]
    field_simp [pow_two, hc_ne]
    nlinarith [hnormsq]
  have hsmooth :
      smoothNormPenalty β x0 = β / c := by
    -- Both sides are positive, so equality follows from equality of squares.
    refine (sq_eq_sq₀ (le_of_lt (smoothNormPenalty_pos β hβ x0)) (by positivity)).1 ?_
    simpa [pow_two] using hsmooth_sq
  have hinner :
      inner ℝ x0 y = (β / c) * ‖y‖ ^ 2 := by
    -- Evaluating the inner product isolates the same scalar factor.
    calc
      inner ℝ x0 y = inner ℝ ((β / c) • y) y := by rfl
      _ = (β / c) * inner ℝ y y := by rw [real_inner_smul_left]
      _ = (β / c) * ‖y‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  refine by
    subst x0
    calc
      inner ℝ ((β / c) • y) y - smoothNormPenalty β ((β / c) • y)
          = (β / c) * ‖y‖ ^ 2 - β / c := by rw [hinner, hsmooth]
      _ = (β / c) * (‖y‖ ^ 2 - 1) := by ring
      _ = (β / c) * (-(c ^ 2)) := by
            congr 1
            nlinarith [hnormsq]
      _ = (-β) * c := by
            field_simp [hc_ne]
      _ = (-β) * Real.sqrt (1 - ‖y‖ ^ 2) := by rfl

/-- Helper for Example 8.5: on the boundary `‖y‖ = 1`, the ray `t • y`
produces conjugate values arbitrarily close to `0` from below. -/
lemma existsInnerSubSmoothNormPenaltyGtOfNormEqOne
    (β : ℝ) (hβ : 0 < β) (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ = 1) :
    ∀ M : ℝ, M < 0 → ∃ x : EuclideanSpace ℝ (Fin d),
      M < inner ℝ x y - smoothNormPenalty β x := by
  intro M hM
  let t : ℝ := max 0 (β ^ 2 / (-2 * M)) + 1
  have hMneg : 0 < -2 * M := by
    nlinarith
  have htbound : β ^ 2 / (-2 * M) < t := by
    dsimp [t]
    nlinarith [le_max_right 0 (β ^ 2 / (-2 * M))]
  have ht_pos : 0 < t := by
    dsimp [t]
    nlinarith [le_max_left 0 (β ^ 2 / (-2 * M))]
  have hsqrt_lt : Real.sqrt (t ^ 2 + β ^ 2) < t - M := by
    -- The choice of `t` forces the square-root term strictly below `t - M`.
    have htm_nonneg : 0 ≤ t - M := by
      nlinarith
    rw [Real.sqrt_lt (by positivity) htm_nonneg]
    have hβbound : β ^ 2 < (-2 * M) * t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((div_lt_iff₀ hMneg).1 htbound)
    nlinarith [hβbound]
  refine ⟨t • y, ?_⟩
  -- Along the boundary ray, the value simplifies to `t - √(t^2 + β^2)`.
  calc
    M < t - Real.sqrt (t ^ 2 + β ^ 2) := by nlinarith
    _ = inner ℝ (t • y) y - smoothNormPenalty β (t • y) := by
          have hy_sq : ‖y‖ ^ 2 = 1 := by nlinarith [hy]
          have hmul_sq : (t * ‖y‖) ^ 2 = t ^ 2 := by rw [hy, mul_one]
          calc
            t - Real.sqrt (t ^ 2 + β ^ 2)
                = t * ‖y‖ ^ 2 - Real.sqrt (t ^ 2 + β ^ 2) := by rw [hy_sq]; ring
            _ = t * ‖y‖ ^ 2 - Real.sqrt ((t * ‖y‖) ^ 2 + β ^ 2) := by rw [hmul_sq]
            _ = inner ℝ (t • y) y - smoothNormPenalty β (t • y) := by
                    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, smoothNormPenalty_def,
                      norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]

/-- Helper for Example 8.5: when `1 < ‖y‖`, the ray
`t • (‖y‖⁻¹ • y)` forces `inner ℝ x y - smoothNormPenalty β x` above any
prescribed threshold. -/
lemma existsInnerSubSmoothNormPenaltyGtOfOneLtNorm
    (β : ℝ) (hβ : 0 < β) (y : EuclideanSpace ℝ (Fin d)) (hy : 1 < ‖y‖) :
    ∀ M : ℝ, ∃ x : EuclideanSpace ℝ (Fin d),
      M < inner ℝ x y - smoothNormPenalty β x := by
  intro M
  have hy_gap : 0 < ‖y‖ - 1 := sub_pos.mpr hy
  have hynz : y ≠ 0 := by
    intro hy0
    have : ¬ (1 < ‖(0 : EuclideanSpace ℝ (Fin d))‖) := by simp
    exact this (by simpa [hy0] using hy)
  let t : ℝ := max 0 ((M + β) / (‖y‖ - 1)) + 1
  let u : EuclideanSpace ℝ (Fin d) := ‖y‖⁻¹ • y
  have htbound : (M + β) / (‖y‖ - 1) < t := by
    dsimp [t]
    nlinarith [le_max_right 0 ((M + β) / (‖y‖ - 1))]
  have ht_pos : 0 < t := by
    dsimp [t]
    nlinarith [le_max_left 0 ((M + β) / (‖y‖ - 1))]
  have hu_norm : ‖u‖ = 1 := by
    -- Normalizing by `‖y‖` produces a unit vector because `y ≠ 0`.
    simp [u, norm_smul, norm_ne_zero_iff.2 hynz]
  have huy : inner ℝ u y = ‖y‖ := by
    -- The normalized direction extracts the full norm in the inner product.
    calc
      inner ℝ u y = inner ℝ (‖y‖⁻¹ • y) y := by rfl
      _ = ‖y‖⁻¹ * inner ℝ y y := by rw [real_inner_smul_left]
      _ = ‖y‖⁻¹ * ‖y‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = ‖y‖ := by
            field_simp [pow_two, norm_ne_zero_iff.2 hynz]
  have hsmooth_le : smoothNormPenalty β (t • u) ≤ t + β := by
    -- On the unit ray, `√(t^2 + β^2)` is bounded above by `t + β`.
    rw [smoothNormPenalty_def, norm_smul, hu_norm, Real.norm_eq_abs, abs_of_pos ht_pos]
    have hsq :
        (Real.sqrt (t ^ 2 + β ^ 2)) ^ 2 ≤ (t + β) ^ 2 := by
      rw [Real.sq_sqrt]
      · nlinarith
      · positivity
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1 (by simpa [pow_two] using hsq)
  refine ⟨t • u, ?_⟩
  -- The linear term grows like `t * ‖y‖`, while the penalty grows at most like `t + β`.
  calc
    M < t * ‖y‖ - (t + β) := by
          have hmul : M + β < t * (‖y‖ - 1) := by
            rwa [div_lt_iff₀ hy_gap] at htbound
          nlinarith
    _ ≤ inner ℝ (t • u) y - smoothNormPenalty β (t • u) := by
          rw [real_inner_smul_left, huy]
          nlinarith [hsmooth_le]

/-- First part of Example 8.5. For `0 < β` and `‖y‖ ≤ 1`, the whole-space conjugate
functional of `smoothNormPenalty β` at `y` is
`(-β) * Real.sqrt (1 - ‖y‖ ^ 2)`. -/
theorem smoothNormPenalty_conjugateFunctional_eq_of_norm_le_one
    (β : ℝ) (hβ : 0 < β) (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 1) :
    conjugateFunctional Set.univ (smoothNormPenalty β) y =
      (((-β) * Real.sqrt (1 - ‖y‖ ^ 2) : ℝ) : EReal) := by
  rw [smoothNormPenalty_conjugateFunctional_univ_def]
  refine le_antisymm ?_ ?_
  · -- Every point of the range is controlled by the closed-ball upper bound.
    refine sSup_le fun z hz ↦ ?_
    rcases hz with ⟨x, rfl⟩
    exact EReal.coe_le_coe (by
      have hbound := smoothNormPenaltyBoundsDualTerm β hβ x y hy
      nlinarith)
  · by_cases hylt : ‖y‖ < 1
    · -- Inside the open ball, the explicit optimizer attains the value.
      refine le_sSup ?_
      refine ⟨(β / Real.sqrt (1 - ‖y‖ ^ 2)) • y, ?_⟩
      simpa [EReal.coe_sub] using
        congrArg (fun r : ℝ => (r : EReal))
          (smoothNormPenaltyConjugateInteriorWitness β hβ y hylt)
    · -- On the boundary, values along the ray `t • y` approach `0` from below.
      have hyeq : ‖y‖ = 1 := by
        nlinarith
      have htarget :
          (((-β) * Real.sqrt (1 - ‖y‖ ^ 2) : ℝ) : EReal) = 0 := by
        simp [hyeq]
      rw [htarget]
      refine le_of_forall_lt fun c hc ↦ ?_
      rcases EReal.exists_rat_btwn_of_lt hc with ⟨q, hcq, hq0⟩
      have hqreal : (q : ℝ) < 0 := EReal.coe_lt_coe_iff.1 hq0
      rcases existsInnerSubSmoothNormPenaltyGtOfNormEqOne β hβ y hyeq (q : ℝ) hqreal with
        ⟨x, hx⟩
      exact lt_of_lt_of_le (lt_trans hcq (EReal.coe_lt_coe hx)) (le_sSup ⟨x, rfl⟩)

/-- Second part of Example 8.5. For `0 < β` and `1 < ‖y‖`, the whole-space conjugate
functional of `smoothNormPenalty β` at `y` is `⊤`. -/
theorem smoothNormPenalty_conjugateFunctional_eq_top_of_one_lt_norm
    (β : ℝ) (hβ : 0 < β) (y : EuclideanSpace ℝ (Fin d)) (hy : 1 < ‖y‖) :
    conjugateFunctional Set.univ (smoothNormPenalty β) y = ⊤ := by
  rw [smoothNormPenalty_conjugateFunctional_univ_def, EReal.eq_top_iff_forall_lt]
  intro M
  rcases existsInnerSubSmoothNormPenaltyGtOfOneLtNorm β hβ y hy M with ⟨x, hx⟩
  -- A real witness above `M` yields an `EReal` witness below the supremum.
  refine lt_of_lt_of_le ?_ (le_sSup ⟨x, rfl⟩)
  exact EReal.coe_lt_coe hx

/-- For `0 < β`, the conjugate set of `smoothNormPenalty β` on `Set.univ` is
exactly the closed unit ball. -/
theorem smoothNormPenalty_mem_conjugateSet_iff_norm_le_one
    (β : ℝ) (hβ : 0 < β) (y : EuclideanSpace ℝ (Fin d)) :
    y ∈ conjugateSet Set.univ (smoothNormPenalty β) ↔ ‖y‖ ≤ 1 := by
  rw [mem_conjugateSet_iff]
  constructor
  · -- A finite conjugate value cannot coincide with the `⊤` case.
    intro hyfin
    by_contra hy'
    have hygt : 1 < ‖y‖ := lt_of_not_ge hy'
    rw [smoothNormPenalty_conjugateFunctional_eq_top_of_one_lt_norm β hβ y hygt] at hyfin
    simp at hyfin
  · -- Inside the closed unit ball, the explicit finite-value formula is below `⊤`.
    intro hy'
    rw [smoothNormPenalty_conjugateFunctional_eq_of_norm_le_one β hβ y hy']
    exact EReal.coe_lt_top _

/-- Example 8.5. For `0 < β`, the penalty `smoothNormPenalty β x` is the
supremum of `y ↦ inner ℝ x y + β * Real.sqrt (1 - ‖y‖ ^ 2)` over the closed
unit ball `Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1`. -/
theorem smoothNormPenalty_eq_sSup_closedUnitBall
    (β : ℝ) (hβ : 0 < β) (x : EuclideanSpace ℝ (Fin d)) :
    smoothNormPenalty β x =
      sSup ((fun y : EuclideanSpace ℝ (Fin d) ↦
        inner ℝ x y + β * Real.sqrt (1 - ‖y‖ ^ 2)) ''
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  let s : Set ℝ :=
    (fun y : EuclideanSpace ℝ (Fin d) ↦ inner ℝ x y + β * Real.sqrt (1 - ‖y‖ ^ 2)) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  have hs_nonempty : s.Nonempty := by
    rcases smoothNormPenaltyDualWitnessAttains β hβ x with ⟨hy0, hvalue⟩
    refine ⟨smoothNormPenalty β x, ⟨_, hy0, ?_⟩⟩
    simpa using hvalue
  have hs_bdd : BddAbove s := by
    refine ⟨smoothNormPenalty β x, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact smoothNormPenaltyBoundsDualTerm β hβ x y (mem_closedBall_zero_iff.1 hy)
  refine le_antisymm ?_ ?_
  · -- The explicit witness attains the supremum value.
    change smoothNormPenalty β x ≤ sSup s
    refine le_csSup hs_bdd ?_
    rcases smoothNormPenaltyDualWitnessAttains β hβ x with ⟨hy0, hvalue⟩
    refine ⟨_, hy0, ?_⟩
    simpa using hvalue
  · -- Every point of the image set is bounded above by `smoothNormPenalty β x`.
    change sSup s ≤ smoothNormPenalty β x
    refine csSup_le hs_nonempty ?_
    rintro z ⟨y, hy, rfl⟩
    exact smoothNormPenaltyBoundsDualTerm β hβ x y (mem_closedBall_zero_iff.1 hy)

end VariationalRegularization
