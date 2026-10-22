/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_17
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp)
open scoped RealInnerProductSpace

noncomputable section

section

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/- Proposition 12.10 is `source-facing`: it gives the closed proximal formula for the
two-coordinate penalty `(u, v) ↦ λ |u - v|` on the chapter's canonical Euclidean `ℝ²` owner
`EuclideanSpace ℝ (Fin 2)`.

Domain sampling against Definition 6.1, Definition 6.2, Lemma 6.5, and Example 6.17 identifies:

- `source-facing`: the penalty `pair_difference_penalty λ` and its explicit proximal point;
- `core/canonical`: `prox[...]`, `absolute_value_penalty`, `innerSL`, and `𝒯[·]`;
- `bridge/view`: the identification of `pair_difference_penalty λ` with the rank-one penalty
  `absolute_value_penalty 1 ∘ innerSL ℝ (toLp 2 ![λ, -λ])` when `λ ≥ 0`.

The public API therefore keeps the concrete two-coordinate penalty and the explicit proximal
point, while the proof reuses the Chapter 6 rank-one owner instead of introducing a parallel
local wheel. -/

/-- The Euclidean two-coordinate penalty `(u, v) ↦ λ |u - v|`. -/
def pair_difference_penalty (lam : ℝ) : E2 → EReal :=
  fun x ↦ ((lam * |x 0 - x 1| : ℝ) : EReal)

/-- For `λ ≥ 0`, the two-coordinate penalty is the rank-one absolute-value penalty attached to the
vector `(λ, -λ)`. -/
theorem pair_difference_penalty_eq_abs_inner (lam : ℝ) (hlam : 0 ≤ lam) :
    pair_difference_penalty lam =
      absolute_value_penalty 1 ∘ innerSL ℝ (toLp 2 ![lam, -lam]) := by
  funext x
  have hinner : ⟪toLp 2 ![lam, -lam], x⟫ = lam * x 0 - lam * x 1 := by
    simpa [dotProduct, Fin.sum_univ_two, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      EuclideanSpace.inner_toLp_toLp ![lam, -lam] x
  change ((lam * |x 0 - x 1| : ℝ) : EReal) =
    (((1 : ℝ) * |⟪toLp 2 ![lam, -lam], x⟫| : ℝ) : EReal)
  rw [hinner, one_mul]
  exact_mod_cast
    (show lam * |x 0 - x 1| = |lam * x 0 - lam * x 1| by
      calc
        lam * |x 0 - x 1| = |lam * (x 0 - x 1)| := by rw [abs_mul, abs_of_nonneg hlam]
        _ = |lam * x 0 - lam * x 1| := by congr 1; ring)

/-- The scalar shrinkage correction in Proposition 12.10. -/
def pair_difference_prox_correction (lam y z : ℝ) : ℝ :=
  (((|y - z| - 2 * lam)⁺ * Real.sign (y - z) - (y - z)) / 2)

/-- The explicit proximal point from Proposition 12.10. -/
def pair_difference_prox_point (lam y z : ℝ) : E2 :=
  toLp 2
    ![
      y + pair_difference_prox_correction lam y z,
      z - pair_difference_prox_correction lam y z
    ]

private lemma pair_difference_posPart_scale (lam t : ℝ) (hlam : 0 ≤ lam) :
    (lam * t)⁺ = lam * t⁺ := by
  simpa [mul_comm] using (max_mul_of_nonneg t 0 hlam).symm

private lemma pair_difference_sign_scale (lam y z : ℝ) (hlam : 0 < lam) :
    Real.sign (lam * y - lam * z) = Real.sign (y - z) := by
  by_cases hneg : y - z < 0
  · have hlamneg : lam * y - lam * z < 0 := by
      nlinarith
    simp [Real.sign, hneg, hlamneg]
  · have hnonneg : 0 ≤ y - z := le_of_not_gt hneg
    by_cases hyz : y = z
    · subst hyz
      simp
    · have hpos : 0 < y - z := by
        exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using (sub_ne_zero.mpr hyz))
      have hlampos : 0 < lam * y - lam * z := by
        nlinarith
      have hlamnotneg : ¬ lam * y - lam * z < 0 := by
        linarith
      simp [Real.sign, hneg, hlamnotneg, hpos, hlampos]

private lemma pair_difference_real_sign_eq_signType (r : ℝ) :
    Real.sign r = (((SignType.sign r : SignType) : ℝ)) := by
  by_cases hr_neg : r < 0
  · simp [Real.sign, hr_neg]
  · by_cases hr_pos : 0 < r
    · simp [Real.sign, hr_neg, hr_pos]
    · have hr_zero : r = 0 := by
        linarith
      simp [Real.sign, hr_zero]

private lemma pair_difference_scaled_numerator (lam y z : ℝ) (hlam : 0 < lam) :
    (|lam * y - lam * z| - 2 * lam ^ 2)⁺ *
        (((SignType.sign (lam * y - lam * z) : SignType) : ℝ)) -
        (lam * y - lam * z) =
      lam * (((|y - z| - 2 * lam)⁺ * (((SignType.sign (y - z) : SignType) : ℝ))) - (y - z)) := by
  have harg : |lam * y - lam * z| - 2 * lam ^ 2 = lam * (|y - z| - 2 * lam) := by
    calc
      |lam * y - lam * z| - 2 * lam ^ 2 = lam * |y - z| - 2 * lam ^ 2 := by
        rw [show lam * y - lam * z = lam * (y - z) by ring, abs_mul, abs_of_nonneg hlam.le]
      _ = lam * (|y - z| - 2 * lam) := by
        ring_nf
  have hsign :
      (((SignType.sign (lam * y - lam * z) : SignType) : ℝ)) =
        (((SignType.sign (y - z) : SignType) : ℝ)) := by
    rw [← pair_difference_real_sign_eq_signType, ← pair_difference_real_sign_eq_signType,
      pair_difference_sign_scale lam y z hlam]
  rw [harg, pair_difference_posPart_scale lam (|y - z| - 2 * lam) hlam.le, hsign]
  ring

-- Proof sketch: specialize Example 6.17 to the rank-one vector `(λ, -λ)` in the chapter's
-- Euclidean `ℝ²`. Under `λ > 0`, the source penalty equals the rank-one penalty, and the Chapter 6
-- singleton formula gives the displayed soft-thresholding correction.
/-- Proposition 12.10 (1) in the Chapter 6 soft-thresholding form: for `λ > 0`, the proximal mapping
of `(u, v) ↦ λ |u - v|` at `(y, z)` is the singleton given by the rank-one soft-thresholding
correction along `(λ, -λ)`. -/
theorem prox_pair_difference_penalty_eq_singleton_soft_thresholding
    (lam y z : ℝ) (hlam : 0 < lam) :
    prox[pair_difference_penalty lam] (toLp 2 ![y, z]) =
      {(toLp 2 ![y, z]) +
        (((𝒯[2 * lam ^ 2] (lam * y - lam * z) - (lam * y - lam * z)) / (2 * lam ^ 2)) •
          (toLp 2 ![lam, -lam]))} := by
  have hlam0 : (toLp 2 ![lam, -lam]) ≠ 0 := by
    intro h
    have h0 : lam = 0 := by
      simpa using congrArg (fun v : E2 ↦ v 0) h
    exact hlam.ne' h0
  have hinner :
      ⟪toLp 2 ![lam, -lam], toLp 2 ![y, z]⟫ = lam * y - lam * z := by
    simpa [dotProduct, Fin.sum_univ_two, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      EuclideanSpace.inner_toLp_toLp ![lam, -lam] ![y, z]
  have hnorm : ‖toLp 2 ![lam, -lam]‖ ^ 2 = 2 * lam ^ 2 := by
    have hnorm' := EuclideanSpace.real_norm_sq_eq (toLp 2 ![lam, -lam])
    simp [Fin.sum_univ_two, pow_two] at hnorm'
    linarith
  rw [pair_difference_penalty_eq_abs_inner lam hlam.le]
  simpa [hinner, hnorm] using
    prox_abs_inner_eq_singleton_soft_thresholding_correction
      (toLp 2 ![lam, -lam])
      (toLp 2 ![y, z]) hlam0

-- Proof sketch: for `λ = 0`, the penalty is identically zero so the proximal mapping is the
-- singleton `{(y, z)}`. For `λ > 0`, rewrite the Chapter 6 soft-thresholding formula from the
-- preceding theorem with `𝒯[2 λ²](λ (y - z)) = (|y - z| - 2 λ)⁺ sign (y - z)`.
/-- Proposition 12.10 (2): for `λ ≥ 0`, the proximal mapping of `(u, v) ↦ λ |u - v|` at `(y, z)` is
the singleton containing the explicit shrinkage point from the textbook sign/positive-part
formula. -/
theorem prox_pair_difference_penalty_eq_singleton
    (lam : ℝ) (hlam : 0 ≤ lam) (y z : ℝ) :
    prox[pair_difference_penalty lam] (toLp 2 ![y, z]) =
      {pair_difference_prox_point lam y z} := by
  by_cases hzero : lam = 0
  · subst hzero
    have hzero_expr : |y - z| * Real.sign (y - z) - (y - z) = 0 := by
      have hsign : |y - z| * Real.sign (y - z) = y - z := by
        by_cases hneg : y - z < 0
        · simp [Real.sign, hneg, abs_of_neg hneg]
        · have hnonneg : 0 ≤ y - z := le_of_not_gt hneg
          by_cases hyz : y = z
          · simp [hyz]
          · have hpos : 0 < y - z := by
              exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using (sub_ne_zero.mpr hyz))
            simp [Real.sign, hneg, abs_of_nonneg hnonneg, hpos]
      linarith
    have hcorr : pair_difference_prox_correction 0 y z = 0 := by
      simp [pair_difference_prox_correction, hzero_expr]
    have hpoint : pair_difference_prox_point 0 y z = toLp 2 ![y, z] := by
      ext i
      fin_cases i <;> simp [pair_difference_prox_point, pair_difference_prox_correction, hzero_expr]
    have hpen0 : pair_difference_penalty 0 = (0 : E2 → EReal) := by
      funext x
      simp [pair_difference_penalty]
    calc
      prox[pair_difference_penalty 0] (toLp 2 ![y, z]) = {toLp 2 ![y, z]} := by
        rw [hpen0]
        simpa using prox_zero_eq_singleton (toLp 2 ![y, z])
      _ = {pair_difference_prox_point 0 y z} := by rw [hpoint]
  · have hpos : 0 < lam := lt_of_le_of_ne hlam (by simpa [eq_comm] using hzero)
    calc
      prox[pair_difference_penalty lam] (toLp 2 ![y, z]) =
          ({(toLp 2 ![y, z]) +
              (((𝒯[2 * lam ^ 2] (lam * y - lam * z) - (lam * y - lam * z)) / (2 * lam ^ 2)) •
                (toLp 2 ![lam, -lam]))} : Set E2) :=
            prox_pair_difference_penalty_eq_singleton_soft_thresholding lam y z hpos
      _ = {pair_difference_prox_point lam y z} := by
            congr 1
            ext i
            fin_cases i
            · simp [pair_difference_prox_point, pair_difference_prox_correction,
                soft_thresholding_apply, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_add,
                add_mul, mul_assoc, mul_left_comm, mul_comm]
              field_simp [hpos.ne']
              have habs : |lam * y + -(lam * z)| = lam * |y + -z| := by
                calc
                  |lam * y + -(lam * z)| = |lam * (y + -z)| := by congr 1; ring
                  _ = lam * |y + -z| := by rw [abs_mul, abs_of_nonneg hpos.le]
              have hlin : lam * y + -(lam * z) = lam * (y + -z) := by
                ring
              have hneglin : -(lam * (y + -z)) = lam * (z + -y) := by
                ring
              have hnum' :
                  (|lam * (y + -z)| + -(lam ^ 2 * 2))⁺ *
                      (((SignType.sign (lam * (y + -z)) : SignType) : ℝ)) +
                    lam * (z + -y) =
                      lam * ((|y + -z| + -(lam * 2))⁺ * (y + -z).sign + (z + -y)) := by
                simpa [sub_eq_add_neg, habs, hlin, hneglin, abs_mul, abs_of_nonneg hpos.le,
                  mul_comm, mul_left_comm, mul_assoc, pair_difference_real_sign_eq_signType] using
                  pair_difference_scaled_numerator lam y z hpos
              exact hnum'
            · simp [pair_difference_prox_point, pair_difference_prox_correction,
                soft_thresholding_apply, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_add,
                add_mul, mul_assoc, mul_left_comm, mul_comm]
              field_simp [hpos.ne']
              have habs : |lam * y + -(lam * z)| = lam * |y + -z| := by
                calc
                  |lam * y + -(lam * z)| = |lam * (y + -z)| := by congr 1; ring
                  _ = lam * |y + -z| := by rw [abs_mul, abs_of_nonneg hpos.le]
              have hlin : lam * y + -(lam * z) = lam * (y + -z) := by
                ring
              have hneglin : -(lam * (y + -z)) = lam * (z + -y) := by
                ring
              have hnum :
                  (|lam * (y + -z)| + -(lam ^ 2 * 2))⁺ *
                      (((SignType.sign (lam * (y + -z)) : SignType) : ℝ)) +
                    lam * (z + -y) =
                    lam * ((|y + -z| + -(lam * 2))⁺ * (y + -z).sign + (z + -y)) := by
                simpa [sub_eq_add_neg, habs, hlin, hneglin, abs_mul, abs_of_nonneg hpos.le,
                  mul_comm, mul_left_comm, mul_assoc, pair_difference_real_sign_eq_signType] using
                  pair_difference_scaled_numerator lam y z hpos
              have hnum' :
                  -((|lam * (y + -z)| + -(lam ^ 2 * 2))⁺ *
                      (((SignType.sign (lam * (y + -z)) : SignType) : ℝ))) +
                    lam * (-z + y) =
                    lam * (y + -z + -((|y + -z| + -(lam * 2))⁺ * (y + -z).sign)) := by
                nlinarith [hnum]
              exact hnum'

end
