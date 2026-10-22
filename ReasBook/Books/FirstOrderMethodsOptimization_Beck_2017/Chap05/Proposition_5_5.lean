/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Proposition_1_9
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open Asymptotics Topology
open scoped Gradient
open WithLp (ofLp toLp)

variable {n : ℕ} {p : ℝ}

local notation "E" => WithLp (ENNReal.ofReal p) (Fin n → ℝ)

/-- The half-squared `ℓ_p` norm on the canonical `WithLp (ENNReal.ofReal p) (Fin n → ℝ)` model of
`ℝ^n`. -/
def halfSquaredLpNorm (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    WithLp (ENNReal.ofReal p) (Fin n → ℝ) → ℝ :=
  fun z ↦ ‖z‖ ^ (2 : ℕ) / 2

/-- Helper for Proposition 5.5: `halfSquaredLpNorm` unfolds to the half-squared ambient norm. -/
@[simp] theorem halfSquaredLpNorm_apply [Fact (1 ≤ ENNReal.ofReal p)] (x : E) :
    halfSquaredLpNorm n p x = ‖x‖ ^ (2 : ℕ) / 2 :=
  rfl

/-- Helper for Proposition 5.5: the hypothesis `2 ≤ p` implies the `WithLp` side condition
`1 ≤ ENNReal.ofReal p`. -/
private theorem one_le_ofReal_of_two_le (hp : 2 ≤ p) : 1 ≤ ENNReal.ofReal p := by
  calc
    1 ≤ ENNReal.ofReal (2 : ℝ) := by norm_num
    _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp

/-- Helper for Proposition 5.5: package `one_le_ofReal_of_two_le` as the `Fact` instance used by
the canonical `WithLp` owner. -/
private instance factOneLeOfRealOfTwoLe (hp : 2 ≤ p) : Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨one_le_ofReal_of_two_le hp⟩

/-- Helper for Proposition 5.5: the canonical `p = 2` exponent satisfies the `WithLp`
typeclass side condition. -/
private instance factOneLeOfRealTwo : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) :=
  ⟨by norm_num⟩

/-- Helper for Proposition 5.5: on a real inner product space, the half-squared norm has
gradient `x`. -/
private theorem hasGradientAt_halfSquaredNorm {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] (x : F) :
    HasGradientAt (fun y : F ↦ ‖y‖ ^ (2 : ℕ) / 2) x x := by
  -- Differentiate `‖y‖²` and absorb the factor `1 / 2` into the derivative.
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (1 / 2 : ℝ) using 1
  · ext y
    simp [div_eq_mul_inv, mul_comm]
  · ext y
    simp [InnerProductSpace.toDual_apply_apply]

/-- Helper for Proposition 5.5: in a real Hilbert space, `x ↦ ‖x‖² / 2` is globally
`1`-smooth. -/
private theorem halfSquaredNorm_isLSmooth_inner {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :
    is_l_smooth_on (fun y : F ↦ ‖y‖ ^ (2 : ℕ) / 2) Set.univ 1 := by
  -- Rewrite smoothness in terms of the gradient field and use that the gradient is the identity.
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  refine ⟨?_, ?_⟩
  · intro x _
    exact (hasGradientAt_halfSquaredNorm x).differentiableAt
  · intro x _ y _
    rw [(hasGradientAt_halfSquaredNorm x).gradient, (hasGradientAt_halfSquaredNorm y).gradient]
    simp

/-- Helper for Proposition 5.5: the exact owner `WithLp (ENNReal.ofReal 2)` still satisfies the
Euclidean norm-square identity. -/
private theorem withLpOfRealTwo_norm_sq_eq_sum
    (x : WithLp (2 : ENNReal) (Fin n → ℝ)) :
    ‖x‖ ^ (2 : ℕ) = ∑ i : Fin n, ‖x i‖ ^ (2 : ℕ) :=
  by
    -- Route correction: work directly on the Euclidean `PiLp` endpoint, where mathlib already
    -- exposes the coordinate norm-square formula.
    simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin n ↦ ℝ) x)

/-- Helper for Proposition 5.5: any `WithLp q` owner whose exponent is identified with `2`
inherits the Hilbert-space `1`-smoothness of the half-squared norm. -/
private theorem halfSquaredNorm_withLpExponentEqTwo_isLSmooth {n : ℕ} {q : ENNReal}
    [Fact (1 ≤ q)]
    (hq : q = (2 : ENNReal)) :
    is_l_smooth_on (fun y : WithLp q (Fin n → ℝ) ↦ ‖y‖ ^ (2 : ℕ) / 2) Set.univ 1 := by
  -- Normalize the exponent parameter first so the exact Euclidean endpoint theorem applies
  -- without any theorem-local transport afterwards.
  subst q
  exact halfSquaredNorm_isLSmooth_inner (F := WithLp (2 : ENNReal) (Fin n → ℝ))

/-- Helper for Proposition 5.5: the Euclidean endpoint `p = 2` is exactly the inner-product-space
case. -/
private theorem halfSquaredLpNorm_two_isLSmooth :
    is_l_smooth_on (halfSquaredLpNorm n (2 : ℝ)) Set.univ 1 :=
  by
    -- Route correction: specialize the Hilbert-space theorem on the exact `WithLp 2` owner and
    -- discharge the target by normalizing the owner exponent before unfolding `halfSquaredLpNorm`.
    have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by
      norm_num
    letI := factOneLeOfRealTwo
    have hsmooth :
        is_l_smooth_on
          (fun y : WithLp (ENNReal.ofReal (2 : ℝ)) (Fin n → ℝ) ↦ ‖y‖ ^ (2 : ℕ) / 2)
          Set.univ 1 :=
      halfSquaredNorm_withLpExponentEqTwo_isLSmooth (n := n) (q := ENNReal.ofReal (2 : ℝ)) htwo
    simpa [halfSquaredLpNorm] using hsmooth

/-- Helper for Proposition 5.5: the canonical coordinate duality vector for the half-squared
`ℓ_p` norm, with the singular `x = 0` branch built into the definition. -/
private def halfSquaredLpNormDualVector [Fact (1 ≤ ENNReal.ofReal p)] (x : E) : Fin n → ℝ :=
  if x = 0 then 0 else fun i ↦ ‖x‖ ^ (2 - p) * Real.sign (x i) * |x i| ^ (p - 1)

/-- Helper for Proposition 5.5: the duality vector vanishes at the singular point `x = 0`. -/
@[simp] private theorem halfSquaredLpNormDualVector_zero [Fact (1 ≤ ENNReal.ofReal p)] :
    halfSquaredLpNormDualVector (0 : E) = 0 := by
  simp [halfSquaredLpNormDualVector]

/-- Helper for Proposition 5.5: away from `0`, the duality vector unfolds to the textbook
coordinate formula. -/
private theorem halfSquaredLpNormDualVector_eq_of_ne_zero [Fact (1 ≤ ENNReal.ofReal p)]
    (x : E) (hx : x ≠ 0) :
    halfSquaredLpNormDualVector x =
      fun i ↦ ‖x‖ ^ (2 - p) * Real.sign (x i) * |x i| ^ (p - 1) := by
  simp [halfSquaredLpNormDualVector, hx]

/-- Helper for Proposition 5.5: each coordinate of the duality vector unfolds to the textbook
formula away from `0`. -/
private theorem halfSquaredLpNormDualVector_apply_of_ne_zero [Fact (1 ≤ ENNReal.ofReal p)]
    (x : E) (hx : x ≠ 0) (i : Fin n) :
    halfSquaredLpNormDualVector x i =
      ‖x‖ ^ (2 - p) * Real.sign (x i) * |x i| ^ (p - 1) := by
  simp [halfSquaredLpNormDualVector, hx]

/-- Helper for Proposition 5.5: the duality vector is homogeneous of degree one. -/
private theorem halfSquaredLpNormDualVector_map_smul [Fact (1 ≤ ENNReal.ofReal p)]
    (a : ℝ) (x : E) :
    halfSquaredLpNormDualVector (a • x) = a • halfSquaredLpNormDualVector x :=
  by
    by_cases ha : a = 0
    · -- The zero scalar kills both sides by definition.
      subst ha
      simp
    · by_cases hx : x = 0
      · -- The singular vector branch is also trivial after reducing to `x = 0`.
        subst hx
        simp [halfSquaredLpNormDualVector]
      · -- Away from the singular branches, compare coordinates and normalize the scalar factor.
        ext i
        have hax : a • x ≠ 0 := by
          exact fun hzero ↦ (smul_eq_zero.mp hzero).elim ha hx
        have ha_abs_pos : 0 < |a| := abs_pos.mpr ha
        have hnorm_rpow :
            ‖a • x‖ ^ (2 - p) = |a| ^ (2 - p) * ‖x‖ ^ (2 - p) := by
          rw [norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg a) (norm_nonneg x)]
        have hcoord_rpow :
            |(a • x) i| ^ (p - 1) = |a| ^ (p - 1) * |x i| ^ (p - 1) := by
          simp [abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg (x i))]
        have hsign_mul :
            Real.sign (a * x i) = Real.sign a * Real.sign (x i) := by
          rcases lt_trichotomy a 0 with ha_neg | rfl | ha_pos
          · rcases lt_trichotomy (x i) 0 with hxi_neg | hxi_zero | hxi_pos
            · have hm : 0 < a * x i := mul_pos_of_neg_of_neg ha_neg hxi_neg
              simp [Real.sign_of_neg ha_neg, Real.sign_of_neg hxi_neg, Real.sign_of_pos hm]
            · simp [hxi_zero, Real.sign_of_neg ha_neg]
            · have hm : a * x i < 0 := mul_neg_of_neg_of_pos ha_neg hxi_pos
              simp [Real.sign_of_neg ha_neg, Real.sign_of_pos hxi_pos, Real.sign_of_neg hm]
          · simp
          · rcases lt_trichotomy (x i) 0 with hxi_neg | hxi_zero | hxi_pos
            · have hm : a * x i < 0 := mul_neg_of_pos_of_neg ha_pos hxi_neg
              simp [Real.sign_of_pos ha_pos, Real.sign_of_neg hxi_neg, Real.sign_of_neg hm]
            · simp [hxi_zero, Real.sign_of_pos ha_pos]
            · have hm : 0 < a * x i := mul_pos ha_pos hxi_pos
              simp [Real.sign_of_pos ha_pos, Real.sign_of_pos hxi_pos, Real.sign_of_pos hm]
        have hsign :
            Real.sign ((a • x) i) = Real.sign a * Real.sign (x i) := by
          simpa [Pi.smul_apply] using hsign_mul
        have habs_split : |a| ^ (2 - p) * |a| ^ (p - 1) = |a| := by
          calc
            |a| ^ (2 - p) * |a| ^ (p - 1) = |a| ^ ((2 - p) + (p - 1)) := by
              rw [← Real.rpow_add ha_abs_pos]
            _ = |a| ^ (1 : ℝ) := by
              congr 1
              ring_nf
            _ = |a| := by simp
        have hsign_abs : |a| * Real.sign a = a := by
          rcases lt_trichotomy a 0 with hneg | rfl | hpos
          · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
          · simp
          · simp [Real.sign_of_pos hpos, abs_of_pos hpos]
        rw [halfSquaredLpNormDualVector_apply_of_ne_zero (x := a • x) hax i, Pi.smul_apply,
          halfSquaredLpNormDualVector_apply_of_ne_zero (x := x) hx i, hnorm_rpow, hcoord_rpow,
          hsign]
        calc
          (|a| ^ (2 - p) * ‖x‖ ^ (2 - p)) * (Real.sign a * Real.sign (x i)) *
              (|a| ^ (p - 1) * |x i| ^ (p - 1))
              =
              (|a| ^ (2 - p) * |a| ^ (p - 1)) *
                (‖x‖ ^ (2 - p) * Real.sign a * (Real.sign (x i) * |x i| ^ (p - 1))) := by
                  ring_nf
          _ = |a| * (‖x‖ ^ (2 - p) * Real.sign a * (Real.sign (x i) * |x i| ^ (p - 1))) := by
                rw [habs_split]
          _ = (|a| * Real.sign a) * (‖x‖ ^ (2 - p) * (Real.sign (x i) * |x i| ^ (p - 1))) := by
                ring_nf
          _ = a * (‖x‖ ^ (2 - p) * (Real.sign (x i) * |x i| ^ (p - 1))) := by
                rw [hsign_abs]
          _ = a * (‖x‖ ^ (2 - p) * Real.sign (x i) * |x i| ^ (p - 1)) := by
                ring_nf

/-- Helper for Proposition 5.5: the real sign function has absolute value at most `1`. -/
private theorem abs_real_sign_le_one (t : ℝ) : |Real.sign t| ≤ 1 := by
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · simp [Real.sign_of_neg hneg]
  · simp
  · simp [Real.sign_of_pos hpos]

/-- Helper for Proposition 5.5: subtracting two pairing duals is pairing against the coordinate
difference. -/
private theorem lpPairingDual_sub_eq (q : ENNReal) (u v : Fin n → ℝ) :
    lpPairingDual q u - lpPairingDual q v = lpPairingDual q (u - v) := by
  ext x
  simp [lpPairingDual_apply, dotProduct_sub]

/-- Helper for Proposition 5.5: the operator norm of a pairing-dual difference is the `ℓ_q` norm
of the coefficient difference. -/
private theorem lpPairingDual_sub_norm_eq (q : ENNReal) [Fact (1 ≤ q)] (u v : Fin n → ℝ) :
    ‖LinearMap.toContinuousLinearMap (lpPairingDual q u) -
        LinearMap.toContinuousLinearMap (lpPairingDual q v)‖ =
      ‖toLp (ENNReal.conjExponent q) (u - v)‖ := by
  -- Collapse the difference of the two functionals to a single `lpPairingDual`.
  have hclm_sub :
      LinearMap.toContinuousLinearMap (lpPairingDual q u) -
          LinearMap.toContinuousLinearMap (lpPairingDual q v) =
        LinearMap.toContinuousLinearMap (lpPairingDual q (u - v)) :=
    congrArg LinearMap.toContinuousLinearMap (lpPairingDual_sub_eq q u v)
  rw [hclm_sub, ← dualNorm_eq_toContinuousLinearMap_norm]
  exact dualNorm_lpPairingDual_eq_conjExponent_lp_norm (p := q) (u - v)

/-- Helper for Proposition 5.5: the duality vector has exactly the conjugate-exponent norm
`‖x‖`, which is the normalization needed before converting to an operator norm. -/
private theorem halfSquaredLpNormDualVector_conjExponent_norm_eq [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (x : E) :
    ‖toLp (ENNReal.conjExponent (ENNReal.ofReal p)) (halfSquaredLpNormDualVector x)‖ = ‖x‖ := by
  letI : Fact (1 ≤ ENNReal.conjExponent (ENNReal.ofReal p)) :=
    ⟨ENNReal.HolderConjugate.oneLeRight
      (p := ENNReal.ofReal p)
      (q := ENNReal.conjExponent (ENNReal.ofReal p))
      inferInstance⟩
  by_cases hx : x = 0
  · -- At the singular point, both the duality vector and its conjugate norm are zero.
    subst hx
    calc
      ‖toLp (ENNReal.conjExponent (ENNReal.ofReal p)) (halfSquaredLpNormDualVector (0 : E))‖
          = ‖(0 : WithLp (ENNReal.conjExponent (ENNReal.ofReal p)) (Fin n → ℝ))‖ := by
              simp [halfSquaredLpNormDualVector]
      _ = 0 := by simp
      _ = ‖(0 : E)‖ := by simp
  · -- Away from `0`, normalize the coordinate formula and collapse the conjugate exponent algebra.
    have hpPos : 0 < p := lt_of_lt_of_le zero_lt_two hp
    have hpOne : 1 < p := lt_of_lt_of_le one_lt_two hp
    have hnorm_pos : 0 < ‖(x : E)‖ := by
      simpa using (norm_pos_iff.mpr hx : 0 < ‖x‖)
    let q : ℝ := (ENNReal.conjExponent (ENNReal.ofReal p)).toReal
    have hpqReal : p.HolderConjugate q := by
      simpa [q, ENNReal.toReal_ofReal hpPos.le] using
        (ENNReal.HolderConjugate.toReal
          (p := ENNReal.ofReal p)
          (q := ENNReal.conjExponent (ENNReal.ofReal p))
          (by simpa [ENNReal.toReal_ofReal hpPos.le] using hpOne))
    have hqPos : 0 < q := hpqReal.symm.pos
    have hmul : (p - 1) * q = p := hpqReal.sub_one_mul_conj
    have hnorm_eq_sum :
        ‖x‖ = (∑ i : Fin n, |x i| ^ p) ^ (1 / p) := by
      simpa [q, PiLp.toLp_apply, Real.norm_eq_abs, ENNReal.toReal_ofReal hpPos.le] using
        (PiLp.norm_eq_sum
          (by simpa [ENNReal.toReal_ofReal hpPos.le] using hpPos)
          (toLp (ENNReal.ofReal p) (WithLp.ofLp x)))
    have hnorm_pow :
        ‖x‖ ^ p = ∑ i : Fin n, |x i| ^ p := by
      calc
        ‖x‖ ^ p = ((∑ i : Fin n, |x i| ^ p) ^ (1 / p)) ^ p := by rw [hnorm_eq_sum]
        _ = ∑ i : Fin n, |x i| ^ p := by
          rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _)]
          rw [one_div, inv_mul_cancel₀ hpPos.ne', Real.rpow_one]
    have habs_coord :
        ∀ i : Fin n,
          |halfSquaredLpNormDualVector x i| = ‖x‖ ^ (2 - p) * |x i| ^ (p - 1) := by
      intro i
      rw [halfSquaredLpNormDualVector_apply_of_ne_zero (x := x) hx i]
      have hnorm_nonneg : 0 ≤ ‖x‖ ^ (2 - p) := Real.rpow_nonneg (norm_nonneg x) _
      have hcoord_nonneg : 0 ≤ |x i| ^ (p - 1) := Real.rpow_nonneg (abs_nonneg _) _
      have habs_sign :
          |Real.sign (x i) * |x i| ^ (p - 1)| = |x i| ^ (p - 1) := by
        by_cases hxi : x i = 0
        · rw [hxi]
          simp [Real.zero_rpow (sub_pos.mpr hpOne).ne']
        · have hsign_abs : |Real.sign (x i)| = 1 := by
            rcases lt_or_gt_of_ne hxi with hneg | hpos
            · simp [Real.sign_of_neg hneg]
            · simp [Real.sign_of_pos hpos]
          rw [abs_mul, hsign_abs, one_mul, abs_of_nonneg hcoord_nonneg]
      rw [mul_assoc, abs_mul, abs_of_nonneg hnorm_nonneg, habs_sign]
    have hsum_dual :
        ∑ i : Fin n, |halfSquaredLpNormDualVector x i| ^ q = ‖x‖ ^ q := by
      calc
        ∑ i : Fin n, |halfSquaredLpNormDualVector x i| ^ q
            = ∑ i : Fin n, (‖x‖ ^ ((2 - p) * q)) * |x i| ^ p := by
                refine Finset.sum_congr rfl ?_
                intro i _
                rw [habs_coord i, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg x) _)
                  (Real.rpow_nonneg (abs_nonneg _) _)]
                rw [← Real.rpow_mul (norm_nonneg x) (2 - p) q,
                  ← Real.rpow_mul (abs_nonneg (x i)) (p - 1) q, hmul]
        _ = ‖x‖ ^ ((2 - p) * q) * ∑ i : Fin n, |x i| ^ p := by
              rw [Finset.mul_sum]
        _ = ‖x‖ ^ ((2 - p) * q) * ‖x‖ ^ p := by rw [hnorm_pow]
        _ = ‖x‖ ^ (((2 - p) * q) + p) := by
              rw [Real.rpow_add hnorm_pos]
        _ = ‖x‖ ^ q := by
              congr 1
              linarith
    calc
      ‖toLp (ENNReal.conjExponent (ENNReal.ofReal p)) (halfSquaredLpNormDualVector x)‖
          = (∑ i : Fin n, |halfSquaredLpNormDualVector x i| ^ q) ^ (1 / q) := by
              simpa [q, PiLp.toLp_apply, Real.norm_eq_abs] using
                (PiLp.norm_eq_sum hqPos
                  (toLp (ENNReal.conjExponent (ENNReal.ofReal p))
                    (halfSquaredLpNormDualVector x)))
      _ = (‖x‖ ^ q) ^ (1 / q) := by rw [hsum_dual]
      _ = ‖x‖ := by
            rw [← Real.rpow_mul (norm_nonneg x) q (1 / q), one_div, mul_inv_cancel₀ hqPos.ne',
              Real.rpow_one]

/-- Helper for Proposition 5.5: the pairing functional generated by the duality vector has operator
norm at most `‖x‖`. -/
private theorem halfSquaredLpNormDualVector_pairingOpNorm_le [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 ≤ p) (x : E) :
    ‖LinearMap.toContinuousLinearMap
        (lpPairingDual (ENNReal.ofReal p)
          (halfSquaredLpNormDualVector x))‖ ≤ ‖x‖ := by
  -- Route correction: compute the pairing norm through Proposition 1.9 first, then rewrite the
  -- conjugate-exponent norm with the exact dual-vector normalization above.
  rw [← dualNorm_eq_toContinuousLinearMap_norm]
  calc
    dualNorm (lpPairingDual (ENNReal.ofReal p) (halfSquaredLpNormDualVector x))
        = ‖toLp (ENNReal.conjExponent (ENNReal.ofReal p)) (halfSquaredLpNormDualVector x)‖ := by
            exact dualNorm_lpPairingDual_eq_conjExponent_lp_norm
              (p := ENNReal.ofReal p) (halfSquaredLpNormDualVector x)
    _ = ‖x‖ := halfSquaredLpNormDualVector_conjExponent_norm_eq hp x
    _ ≤ ‖x‖ := le_rfl

/-- Helper for Proposition 5.5: at the origin of any real normed space, the half-squared norm has
zero Fréchet derivative. -/
private theorem halfSquaredNorm_hasFDerivAt_zero {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    HasFDerivAt (fun y : F ↦ ‖y‖ ^ (2 : ℕ) / 2) (0 : F →L[ℝ] ℝ) 0 := by
  -- The quadratic remainder is `o(‖h‖)`, so the zero map is the derivative at the origin.
  refine HasFDerivAt.of_isLittleO ?_
  calc
    (fun y : F ↦ ‖y‖ ^ (2 : ℕ) / 2 - ‖(0 : F)‖ ^ (2 : ℕ) / 2 - (0 : F →L[ℝ] ℝ) y)
        = (fun y : F ↦ (1 / 2 : ℝ) * (‖y‖ * ‖y‖)) := by
            ext y
            simp [pow_two, div_eq_mul_inv, mul_assoc]
            ring_nf
    _ =o[nhds (0 : F)] (fun y : F ↦ ‖y‖ * 1) := by
          have hsmall : (fun y : F ↦ ‖y‖) =o[nhds (0 : F)] (fun _ : F ↦ (1 : ℝ)) := by
            refine (isLittleO_const_iff (by simp : (1 : ℝ) ≠ 0)).mpr ?_
            simpa using
              (continuousAt_id.norm : ContinuousAt (fun y : F ↦ ‖y‖) (0 : F)).tendsto
          exact
            (isBigO_refl (fun y : F ↦ ‖y‖) (nhds (0 : F))).mul_isLittleO hsmall
              |>.const_mul_left (1 / 2 : ℝ)
    _ =O[nhds (0 : F)] (fun y : F ↦ y - 0) := by
          simp_rw [mul_one, isBigO_norm_left (f' := fun y : F ↦ y), sub_zero, isBigO_refl]

/-- Helper for Proposition 5.5: the half-squared `ℓ_p` norm is the textbook coordinate formula
away from the ambient `WithLp` notation. -/
private theorem halfSquaredLpNorm_eq_coordinateFormula [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_pos : 0 < p) (x : E) :
    halfSquaredLpNorm n p x = (1 / 2 : ℝ) * (∑ i : Fin n, |x i| ^ p) ^ (2 / p) := by
  -- Rewrite the ambient `WithLp` norm using the standard finite `ℓ_p` coordinate formula.
  have hnorm_eq_sum :
      ‖x‖ = (∑ i : Fin n, |x i| ^ p) ^ (1 / p) := by
    have hp_toReal : 0 < (ENNReal.ofReal p).toReal := by
      simpa [ENNReal.toReal_ofReal hp_pos.le] using hp_pos
    simpa [PiLp.toLp_apply, Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le] using
      (PiLp.norm_eq_sum (p := ENNReal.ofReal p) hp_toReal x)
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, |x i| ^ p := by
    exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  rw [halfSquaredLpNorm_apply]
  calc
    ‖x‖ ^ (2 : ℕ) / 2 = (1 / 2 : ℝ) * (‖x‖ ^ (2 : ℕ)) := by ring_nf
    _ = (1 / 2 : ℝ) * (((∑ i : Fin n, |x i| ^ p) ^ (1 / p)) ^ (2 : ℕ)) := by rw [hnorm_eq_sum]
    _ = (1 / 2 : ℝ) * (∑ i : Fin n, |x i| ^ p) ^ ((1 / p) * 2) := by
          have hrpow_mul :
              ((((∑ i : Fin n, |x i| ^ p) ^ (1 / p)) ^ (2 : ℕ)) : ℝ) =
                (∑ i : Fin n, |x i| ^ p) ^ ((1 / p) * 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hsum_nonneg]
            norm_num
          rw [hrpow_mul]
    _ = (1 / 2 : ℝ) * (∑ i : Fin n, |x i| ^ p) ^ (2 / p) := by
          congr 2
          field_simp [hp_pos.ne']

/-- Helper for Proposition 5.5: the nonzero branch forces the coordinate `p`-power sum to be
nonzero, so later `rpow` exponents may be moved across it safely. -/
private theorem sumAbsRpow_ne_zero_of_ne_zero [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_pos : 0 < p) {x : E} (hx : x ≠ 0) :
    ∑ i : Fin n, |x i| ^ p ≠ 0 := by
  -- Convert the ambient norm identity to a contradiction with `x ≠ 0`.
  have hcoord :
      halfSquaredLpNorm n p x = (1 / 2 : ℝ) * (∑ i : Fin n, |x i| ^ p) ^ (2 / p) :=
    halfSquaredLpNorm_eq_coordinateFormula (n := n) (p := p) hp_pos x
  intro hsum
  have hhalf : halfSquaredLpNorm n p x = 0 := by
    rw [hcoord, hsum]
    simp [hp_pos.ne']
  have hnorm_sq : ‖x‖ ^ (2 : ℕ) = 0 := by
    simpa [halfSquaredLpNorm] using hhalf
  exact hx <| norm_eq_zero.mp <| sq_eq_zero_iff.mp hnorm_sq

/-- Helper for Proposition 5.5: on the nonzero branch, the coordinate power factor collapses to
the ambient norm factor `‖x‖^(2-p)`. -/
private theorem coordinatePowerFactor_eq_normFactor [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_gt : 2 < p) {x : E} (hx : x ≠ 0) :
    (∑ i : Fin n, |x i| ^ p) ^ (2 / p - 1) = ‖x‖ ^ (2 - p) := by
  -- Rewrite the coordinate sum as `‖x‖^p` and then move the exponent through the product.
  have hp_pos : 0 < p := lt_trans zero_lt_two hp_gt
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, |x i| ^ p := by
    exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hsum_ne : ∑ i : Fin n, |x i| ^ p ≠ 0 :=
    sumAbsRpow_ne_zero_of_ne_zero (n := n) (p := p) hp_pos hx
  have hnorm_eq_sum :
      ‖x‖ = (∑ i : Fin n, |x i| ^ p) ^ (1 / p) := by
    have hp_toReal : 0 < (ENNReal.ofReal p).toReal := by
      simpa [ENNReal.toReal_ofReal hp_pos.le] using hp_pos
    simpa [PiLp.toLp_apply, Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le] using
      (PiLp.norm_eq_sum (p := ENNReal.ofReal p) hp_toReal x)
  calc
    (∑ i : Fin n, |x i| ^ p) ^ (2 / p - 1)
        = (∑ i : Fin n, |x i| ^ p) ^ ((1 / p) * (2 - p)) := by
            congr 1
            field_simp [hp_pos.ne']
    _ = ((∑ i : Fin n, |x i| ^ p) ^ (1 / p)) ^ (2 - p) := by
          rw [Real.rpow_mul hsum_nonneg]
    _ = ‖x‖ ^ (2 - p) := by rw [hnorm_eq_sum]

/-- Helper for Proposition 5.5: for `p > 2`, the scalar derivative coefficient
`|t|^(p-2) * t` is the same as the textbook `sign(t) * |t|^(p-1)` form. -/
private theorem absRpow_mul_eq_sign_mul_absRpow [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_gt : 2 < p) (t : ℝ) :
    |t| ^ (p - 2) * t = Real.sign t * |t| ^ (p - 1) := by
  -- Split off the singular coordinate `t = 0`; away from zero, both sides are just the same
  -- `abs` power multiplied by one additional copy of `|t|`.
  by_cases ht : t = 0
  · subst ht
    have hp_one : 1 < p := by linarith
    simp [Real.zero_rpow (sub_pos.mpr hp_gt).ne', Real.zero_rpow (sub_pos.mpr hp_one).ne']
  · rcases lt_or_gt_of_ne ht with ht_neg | ht_pos
    · calc
        |t| ^ (p - 2) * t = (-t) ^ (p - 2) * (-(-t)) := by simp [abs_of_neg ht_neg]
        _ = -((-t) ^ (p - 2) * (-t)) := by ring_nf
        _ = -(((-t) ^ (p - 2)) * (-t) ^ (1 : ℝ)) := by simp
        _ = -((-t) ^ ((p - 2) + 1)) := by
              rw [← Real.rpow_add (neg_pos.mpr ht_neg)]
        _ = -((-t) ^ (p - 1)) := by
              congr 1
              ring_nf
        _ = Real.sign t * |t| ^ (p - 1) := by
              simp [Real.sign_of_neg ht_neg, abs_of_neg ht_neg]
    · calc
        |t| ^ (p - 2) * t = t ^ (p - 2) * t := by simp [abs_of_pos ht_pos]
        _ = t ^ (p - 2) * t ^ (1 : ℝ) := by simp
        _ = t ^ ((p - 2) + 1) := by rw [← Real.rpow_add ht_pos]
        _ = t ^ (p - 1) := by
              congr 1
              ring_nf
        _ = Real.sign t * |t| ^ (p - 1) := by
              simp [Real.sign_of_pos ht_pos, abs_of_pos ht_pos]

/-- Helper for Proposition 5.5: the coordinate duality-map scalar
`t ↦ sign(t) * |t|^(p-1)` has derivative `(p - 1) * |t|^(p - 2)` when `p > 2`. -/
private theorem hasDerivAt_sign_mul_absRpow [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_gt : 2 < p) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.sign u * |u| ^ (p - 1))
      ((p - 1) * |t| ^ (p - 2)) t := by
  by_cases ht : t = 0
  · -- At the origin, rewrite the coordinate scalar as `|u|^(p-2) * u` and use that
    -- `|u|^(p-2) → 0`, so the whole function is `o(u)`.
    subst ht
    have hp_sub_pos : 0 < p - 2 := sub_pos.mpr hp_gt
    have hfactor_tendsto :
        Filter.Tendsto (fun u : ℝ ↦ |u| ^ (p - 2)) (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
      have hcont :
          ContinuousAt (fun u : ℝ ↦ |u| ^ (p - 2)) (0 : ℝ) := by
        exact
          (continuousAt_id.abs).rpow_const
            (Or.inr (show 0 ≤ p - 2 by linarith))
      simpa [Real.zero_rpow hp_sub_pos.ne'] using hcont.tendsto
    have hsmall :
        (fun u : ℝ ↦ |u| ^ (p - 2)) =o[nhds (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) := by
      refine (isLittleO_const_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr ?_
      simpa using hfactor_tendsto
    have hprod :
        (fun u : ℝ ↦ |u| ^ (p - 2) * u) =o[nhds (0 : ℝ)] (fun u : ℝ ↦ u) := by
      simpa [one_mul] using
        hsmall.mul_isBigO (isBigO_refl (fun u : ℝ ↦ u) (nhds (0 : ℝ)))
    have hrewritten :
        (fun u : ℝ ↦
          Real.sign u * |u| ^ (p - 1) -
            Real.sign (0 : ℝ) * |(0 : ℝ)| ^ (p - 1) - (u - 0) • (0 : ℝ)) =o[nhds (0 : ℝ)]
          (fun u : ℝ ↦ u - 0) := by
      convert hprod using 1
      · funext u
        rw [show Real.sign u * |u| ^ (p - 1) = |u| ^ (p - 2) * u by
          symm
          exact absRpow_mul_eq_sign_mul_absRpow (p := p) (hp_gt := hp_gt) u]
        simp [sub_eq_add_neg, smul_eq_mul]
      · funext u
        simp
    simpa [Real.zero_rpow hp_sub_pos.ne'] using HasDerivAt.of_isLittleO hrewritten
  · rcases lt_or_gt_of_ne ht with ht_neg | ht_pos
    · -- On a negative neighborhood, the scalar duality map is just `u ↦ -((-u)^(p-1))`.
      have heq :
          (fun u : ℝ ↦ Real.sign u * |u| ^ (p - 1)) =ᶠ[nhds t]
            (fun u : ℝ ↦ -((-u) ^ (p - 1))) := by
        filter_upwards [Iio_mem_nhds ht_neg] with u hu
        simp [Real.sign_of_neg hu, abs_of_neg (show u < 0 from hu)]
      have hneg_id : HasDerivAt (fun u : ℝ ↦ -u) (-1) t := by
        simpa using (hasDerivAt_id t).neg
      have hpow :
          HasDerivAt (fun u : ℝ ↦ (-u) ^ (p - 1))
            (((p - 1) * (-t) ^ ((p - 1) - 1)) * (-1)) t := by
        simpa [Function.comp] using
          (Real.hasDerivAt_rpow_const (x := -t) (p := p - 1)
            (Or.inl (neg_ne_zero.mpr ht))).comp t hneg_id
      have hpow' :
          HasDerivAt (fun u : ℝ ↦ (-u) ^ (p - 1))
            (((p - 1) * (-t) ^ (p - 2)) * (-1)) t := by
        convert hpow using 1
        ring_nf
      have hmodel' :
          HasDerivAt (fun u : ℝ ↦ -((-u) ^ (p - 1)))
            (-(((p - 1) * (-t) ^ (p - 2)) * (-1))) t := by
        simpa using hpow'.neg
      have hmodel :
          HasDerivAt (fun u : ℝ ↦ -((-u) ^ (p - 1)))
            ((p - 1) * |t| ^ (p - 2)) t := by
        simpa [abs_of_neg ht_neg] using hmodel'
      simpa using hmodel.congr_of_eventuallyEq heq
    · -- On a positive neighborhood, the scalar duality map is `u ↦ u^(p-1)`.
      have heq :
          (fun u : ℝ ↦ Real.sign u * |u| ^ (p - 1)) =ᶠ[nhds t]
            (fun u : ℝ ↦ u ^ (p - 1)) := by
        filter_upwards [Ioi_mem_nhds ht_pos] with u hu
        simp [Real.sign_of_pos hu, abs_of_pos (show 0 < u from hu)]
      have hpow :
          HasDerivAt (fun u : ℝ ↦ u ^ (p - 1))
            ((p - 1) * t ^ ((p - 1) - 1)) t := by
        exact Real.hasDerivAt_rpow_const (x := t) (p := p - 1) (Or.inl ht)
      have hpow' :
          HasDerivAt (fun u : ℝ ↦ u ^ (p - 1))
            ((p - 1) * t ^ (p - 2)) t := by
        convert hpow using 1
        ring_nf
      have hmodel :
          HasDerivAt (fun u : ℝ ↦ u ^ (p - 1))
            ((p - 1) * |t| ^ (p - 2)) t := by
        simpa [abs_of_pos ht_pos] using hpow'
      simpa using hmodel.congr_of_eventuallyEq heq

/-- Helper for Proposition 5.5: the textbook weighted Hölder step bounds
`∑ |ξ_i|^(p-2) |v_i|²` by the product of the `ℓ_{p/(p-2)}` norm of the weights and the
`ℓ_{p/2}` norm of the squared coordinates. -/
private theorem weightedCoordinateQuadratic_le_lpNorm_sq [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_gt : 2 < p) (ξ v : E) :
    ∑ i : Fin n, |ξ i| ^ (p - 2) * |v i| ^ (2 : ℝ) ≤
      (∑ i : Fin n, |ξ i| ^ p) ^ ((p - 2) / p) *
        (∑ i : Fin n, |v i| ^ p) ^ (2 / p) := by
  let a : ℝ := p / (p - 2)
  let b : ℝ := p / 2
  have hp_pos : 0 < p := lt_trans zero_lt_two hp_gt
  have hp_sub_pos : 0 < p - 2 := sub_pos.mpr hp_gt
  have ha_holder : a.HolderConjugate b := by
    rw [Real.holderConjugate_iff]
    constructor
    · dsimp [a]
      refine (one_lt_div_iff).2 ?_
      left
      exact ⟨hp_sub_pos, by linarith⟩
    · dsimp [a, b]
      field_simp [hp_pos.ne', hp_sub_pos.ne']
      ring_nf
  have hholder :=
    Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
      (p := a) (q := b) ha_holder
      (f := fun i : Fin n ↦ |ξ i| ^ (p - 2))
      (g := fun i : Fin n ↦ |v i| ^ (2 : ℝ))
      (fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
      (fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
  have hξ_norm :
      (∑ i : Fin n, (|ξ i| ^ (p - 2)) ^ a) ^ (1 / a) =
        (∑ i : Fin n, |ξ i| ^ p) ^ ((p - 2) / p) := by
    have hsum :
        ∑ i : Fin n, (|ξ i| ^ (p - 2)) ^ a = ∑ i : Fin n, |ξ i| ^ p := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      dsimp [a]
      calc
        (|ξ i| ^ (p - 2)) ^ (p / (p - 2)) = |ξ i| ^ ((p - 2) * (p / (p - 2))) := by
          rw [Real.rpow_mul (abs_nonneg (ξ i))]
        _ = |ξ i| ^ p := by
          congr 1
          field_simp [hp_sub_pos.ne']
    rw [hsum]
    dsimp [a]
    field_simp [hp_pos.ne', hp_sub_pos.ne']
  have hv_norm :
      (∑ i : Fin n, (|v i| ^ (2 : ℝ)) ^ b) ^ (1 / b) =
        (∑ i : Fin n, |v i| ^ p) ^ (2 / p) := by
    have hsum :
        ∑ i : Fin n, (|v i| ^ (2 : ℝ)) ^ b = ∑ i : Fin n, |v i| ^ p := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      dsimp [b]
      calc
        (|v i| ^ (2 : ℝ)) ^ (p / 2) = |v i| ^ ((2 : ℝ) * (p / 2)) := by
          rw [Real.rpow_mul (abs_nonneg (v i))]
        _ = |v i| ^ p := by
          congr 1
          ring_nf
    rw [hsum]
    dsimp [b]
    field_simp [hp_pos.ne']
  calc
    ∑ i : Fin n, |ξ i| ^ (p - 2) * |v i| ^ (2 : ℝ)
        ≤ (∑ i : Fin n, (|ξ i| ^ (p - 2)) ^ a) ^ (1 / a) *
            (∑ i : Fin n, (|v i| ^ (2 : ℝ)) ^ b) ^ (1 / b) := hholder
    _ = (∑ i : Fin n, |ξ i| ^ p) ^ ((p - 2) / p) *
          (∑ i : Fin n, |v i| ^ p) ^ (2 / p) := by
          rw [hξ_norm, hv_norm]

/-- Helper for Proposition 5.5: the square of a real number agrees with the `rpow` square of its
absolute value. -/
private theorem abs_rpow_two_eq_sq (t : ℝ) : |t| ^ (2 : ℝ) = t ^ (2 : ℕ) := by
  calc
    |t| ^ (2 : ℝ) = |t| ^ (2 : ℕ) := by exact Real.rpow_natCast |t| 2
    _ = t ^ (2 : ℕ) := by simp [sq_abs]

/-- Helper for Proposition 5.5: the positive coordinate power factor `(∑ |x_i|^p)^((p-2)/p)`
recovers the ambient norm factor `‖x‖^(p-2)`. -/
private theorem coordinatePositivePowerFactor_eq_normFactor [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_gt : 2 < p) (x : E) :
    (∑ i : Fin n, |x i| ^ p) ^ ((p - 2) / p) = ‖x‖ ^ (p - 2) := by
  have hp_pos : 0 < p := lt_trans zero_lt_two hp_gt
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, |x i| ^ p := by
    exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hnorm_eq_sum :
      ‖x‖ = (∑ i : Fin n, |x i| ^ p) ^ (1 / p) := by
    have hp_toReal : 0 < (ENNReal.ofReal p).toReal := by
      simpa [ENNReal.toReal_ofReal hp_pos.le] using hp_pos
    simpa [PiLp.toLp_apply, Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le] using
      (PiLp.norm_eq_sum (p := ENNReal.ofReal p) hp_toReal x)
  calc
    (∑ i : Fin n, |x i| ^ p) ^ ((p - 2) / p)
        = (∑ i : Fin n, |x i| ^ p) ^ ((1 / p) * (p - 2)) := by
            congr 1
            field_simp [hp_pos.ne']
    _ = ((∑ i : Fin n, |x i| ^ p) ^ (1 / p)) ^ (p - 2) := by
          rw [Real.rpow_mul hsum_nonneg]
    _ = ‖x‖ ^ (p - 2) := by rw [hnorm_eq_sum]

/-- Helper for Proposition 5.5: the finite `ℓ_p` coordinate power `2 / p` recovers the squared
ambient `WithLp` norm. -/
private theorem sumAbsRpow_two_div_eq_norm_sq [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_pos : 0 < p) (x : E) :
    (∑ i : Fin n, |x i| ^ p) ^ (2 / p) = ‖x‖ ^ (2 : ℕ) := by
  -- Rewrite the source coordinate expression through the already-normalized owner formula.
  have hcoord := halfSquaredLpNorm_eq_coordinateFormula (n := n) (p := p) hp_pos x
  calc
    (∑ i : Fin n, |x i| ^ p) ^ (2 / p)
        = (2 : ℝ) * ((1 / 2 : ℝ) * (∑ i : Fin n, |x i| ^ p) ^ (2 / p)) := by ring_nf
    _ = (2 : ℝ) * (halfSquaredLpNorm n p x) := by rw [hcoord]
    _ = (2 : ℝ) * (‖x‖ ^ (2 : ℕ) / 2) := by rw [halfSquaredLpNorm_apply]
    _ = ‖x‖ ^ (2 : ℕ) := by ring_nf

/-- Helper for Proposition 5.5: the weighted coordinate bilinear form satisfies the finite
Cauchy-Schwarz square estimate. -/
private theorem weightedCoordinateBilinear_sq_le [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_gt : 2 < p) (ξ u v : E) :
    (∑ i : Fin n, |ξ i| ^ (p - 2) * u i * v i) ^ (2 : ℕ) ≤
      (∑ i : Fin n, |ξ i| ^ (p - 2) * u i ^ (2 : ℕ)) *
        (∑ i : Fin n, |ξ i| ^ (p - 2) * v i ^ (2 : ℕ)) := by
  let a : ℝ := (p - 2) / 2
  have hadd_eq : ((p - 2) / 2) + ((p - 2) / 2) = p - 2 := by ring_nf
  have hadd_ne : ((p - 2) / 2) + ((p - 2) / 2) ≠ 0 := by
    rw [hadd_eq]
    linarith
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin n ↦ |ξ i| ^ a * u i)
      (fun i : Fin n ↦ |ξ i| ^ a * v i)
  have hleft :
      ∑ i : Fin n, |ξ i| ^ (p - 2) * u i * v i =
        ∑ i : Fin n, (|ξ i| ^ a * u i) * (|ξ i| ^ a * v i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [a]
    have hweight :
        |ξ i| ^ ((p - 2) / 2) * |ξ i| ^ ((p - 2) / 2) = |ξ i| ^ (p - 2) := by
      calc
        |ξ i| ^ ((p - 2) / 2) * |ξ i| ^ ((p - 2) / 2)
            = |ξ i| ^ (((p - 2) / 2) + ((p - 2) / 2)) := by
                rw [← Real.rpow_add' (abs_nonneg (ξ i)) hadd_ne]
        _ = |ξ i| ^ (p - 2) := by rw [hadd_eq]
    calc
      |ξ i| ^ (p - 2) * u i * v i = |ξ i| ^ (p - 2) * (u i * v i) := by ring_nf
      _ = (|ξ i| ^ ((p - 2) / 2) * |ξ i| ^ ((p - 2) / 2)) * (u i * v i) := by
            rw [hweight]
      _ = (|ξ i| ^ ((p - 2) / 2) * u i) * (|ξ i| ^ ((p - 2) / 2) * v i) := by ring_nf
  have huu :
      ∑ i : Fin n, |ξ i| ^ (p - 2) * u i ^ (2 : ℕ) =
        ∑ i : Fin n, (|ξ i| ^ a * u i) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [a]
    have hweight :
        |ξ i| ^ ((p - 2) / 2) * |ξ i| ^ ((p - 2) / 2) = |ξ i| ^ (p - 2) := by
      calc
        |ξ i| ^ ((p - 2) / 2) * |ξ i| ^ ((p - 2) / 2)
            = |ξ i| ^ (((p - 2) / 2) + ((p - 2) / 2)) := by
                rw [← Real.rpow_add' (abs_nonneg (ξ i)) hadd_ne]
        _ = |ξ i| ^ (p - 2) := by rw [hadd_eq]
    calc
      |ξ i| ^ (p - 2) * u i ^ (2 : ℕ)
          = (|ξ i| ^ ((p - 2) / 2) * |ξ i| ^ ((p - 2) / 2)) * u i ^ (2 : ℕ) := by
              rw [hweight]
      _ = (|ξ i| ^ a * u i) ^ (2 : ℕ) := by
            dsimp [a]
            ring_nf
  have hvv :
      ∑ i : Fin n, |ξ i| ^ (p - 2) * v i ^ (2 : ℕ) =
        ∑ i : Fin n, (|ξ i| ^ a * v i) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [a]
    have hweight :
        |ξ i| ^ ((p - 2) / 2) * |ξ i| ^ ((p - 2) / 2) = |ξ i| ^ (p - 2) := by
      calc
        |ξ i| ^ ((p - 2) / 2) * |ξ i| ^ ((p - 2) / 2)
            = |ξ i| ^ (((p - 2) / 2) + ((p - 2) / 2)) := by
                rw [← Real.rpow_add' (abs_nonneg (ξ i)) hadd_ne]
        _ = |ξ i| ^ (p - 2) := by rw [hadd_eq]
    calc
      |ξ i| ^ (p - 2) * v i ^ (2 : ℕ)
          = (|ξ i| ^ ((p - 2) / 2) * |ξ i| ^ ((p - 2) / 2)) * v i ^ (2 : ℕ) := by
              rw [hweight]
      _ = (|ξ i| ^ a * v i) ^ (2 : ℕ) := by
            dsimp [a]
            ring_nf
  calc
    (∑ i : Fin n, |ξ i| ^ (p - 2) * u i * v i) ^ (2 : ℕ)
        = (∑ i : Fin n, (|ξ i| ^ a * u i) * (|ξ i| ^ a * v i)) ^ (2 : ℕ) := by rw [hleft]
    _ ≤ (∑ i : Fin n, (|ξ i| ^ a * u i) ^ (2 : ℕ)) *
          ∑ i : Fin n, (|ξ i| ^ a * v i) ^ (2 : ℕ) := hcs
    _ = (∑ i : Fin n, |ξ i| ^ (p - 2) * u i ^ (2 : ℕ)) *
          ∑ i : Fin n, |ξ i| ^ (p - 2) * v i ^ (2 : ℕ) := by
            rw [← huu, ← hvv]

/-- Helper for Proposition 5.5: in the normalized weighted bilinear form from the source Hessian,
the rank-one perturbation still has operator norm at most `p - 1`. -/
private theorem weightedRankOnePerturbation_le [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_gt : 2 < p) {ξ : E} (hξ : ‖ξ‖ = 1) (s d : E) :
    |(p - 1) * (∑ i : Fin n, |ξ i| ^ (p - 2) * s i * d i) +
        (2 - p) * (∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * s i) *
          (∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i)| ≤
      (p - 1) * ‖s‖ * ‖d‖ := by
  let B : E → E → ℝ := fun u v ↦ ∑ i : Fin n, |ξ i| ^ (p - 2) * u i * v i
  let a : ℝ := B ξ s
  let adjustedS : E := (p - 1) • s + ((2 - p) * a) • ξ
  have hp_pos : 0 < p := lt_trans zero_lt_two hp_gt
  have hp_one_nonneg : 0 ≤ p - 1 := by linarith
  have hBξξ_le : B ξ ξ ≤ 1 := by
    -- Normalize the textbook weighted quadratic form by `‖ξ‖ = 1`.
    have hquad :
        B ξ ξ ≤ (∑ i : Fin n, |ξ i| ^ p) ^ ((p - 2) / p) *
          (∑ i : Fin n, |ξ i| ^ p) ^ (2 / p) := by
      simpa [B, abs_rpow_two_eq_sq, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (weightedCoordinateQuadratic_le_lpNorm_sq (n := n) (p := p) hp_gt ξ ξ)
    have hfactor :
        (∑ i : Fin n, |ξ i| ^ p) ^ ((p - 2) / p) = 1 := by
      simpa [hξ] using
        (coordinatePositivePowerFactor_eq_normFactor (n := n) (p := p) hp_gt ξ)
    have hnorm_sq : (∑ i : Fin n, |ξ i| ^ p) ^ (2 / p) = 1 := by
      rw [sumAbsRpow_two_div_eq_norm_sq (n := n) (p := p) hp_pos ξ, hξ]
      norm_num
    calc
      B ξ ξ ≤ (∑ i : Fin n, |ξ i| ^ p) ^ ((p - 2) / p) *
          (∑ i : Fin n, |ξ i| ^ p) ^ (2 / p) := hquad
      _ = 1 := by rw [hfactor, hnorm_sq]; ring_nf
  have hBss_le : B s s ≤ ‖s‖ ^ (2 : ℕ) := by
    -- The same normalized weighted quadratic estimate controls `B(s,s)`.
    have hquad :
        B s s ≤ (∑ i : Fin n, |ξ i| ^ p) ^ ((p - 2) / p) *
          (∑ i : Fin n, |s i| ^ p) ^ (2 / p) := by
      simpa [B, abs_rpow_two_eq_sq, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (weightedCoordinateQuadratic_le_lpNorm_sq (n := n) (p := p) hp_gt ξ s)
    have hfactor :
        (∑ i : Fin n, |ξ i| ^ p) ^ ((p - 2) / p) = 1 := by
      simpa [hξ] using
        (coordinatePositivePowerFactor_eq_normFactor (n := n) (p := p) hp_gt ξ)
    have hnorm_sq :
        (∑ i : Fin n, |s i| ^ p) ^ (2 / p) = ‖s‖ ^ (2 : ℕ) :=
      sumAbsRpow_two_div_eq_norm_sq (n := n) (p := p) hp_pos s
    simpa [hfactor, hnorm_sq] using hquad
  have hBdd_le : B d d ≤ ‖d‖ ^ (2 : ℕ) := by
    -- The same weighted quadratic control also applies to the line direction.
    have hquad :
        B d d ≤ (∑ i : Fin n, |ξ i| ^ p) ^ ((p - 2) / p) *
          (∑ i : Fin n, |d i| ^ p) ^ (2 / p) := by
      simpa [B, abs_rpow_two_eq_sq, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (weightedCoordinateQuadratic_le_lpNorm_sq (n := n) (p := p) hp_gt ξ d)
    have hfactor :
        (∑ i : Fin n, |ξ i| ^ p) ^ ((p - 2) / p) = 1 := by
      simpa [hξ] using
        (coordinatePositivePowerFactor_eq_normFactor (n := n) (p := p) hp_gt ξ)
    have hnorm_sq :
        (∑ i : Fin n, |d i| ^ p) ^ (2 / p) = ‖d‖ ^ (2 : ℕ) :=
      sumAbsRpow_two_div_eq_norm_sq (n := n) (p := p) hp_pos d
    simpa [hfactor, hnorm_sq] using hquad
  have hsym (u v : E) : B u v = B v u := by
    unfold B
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring_nf
  have hBself_nonneg (u : E) : 0 ≤ B u u := by
    unfold B
    refine Finset.sum_nonneg ?_
    intro i hi
    have hweight_nonneg : 0 ≤ |ξ i| ^ (p - 2) := Real.rpow_nonneg (abs_nonneg _) _
    nlinarith [hweight_nonneg, sq_nonneg (u i)]
  have hExpr (w : E) : B adjustedS w = (p - 1) * B s w + (2 - p) * B ξ s * B ξ w := by
    unfold B adjustedS
    calc
      ∑ i : Fin n, |ξ i| ^ (p - 2) * (((p - 1) • s + ((2 - p) * a) • ξ) i) * w i
          = ∑ i : Fin n,
              ((p - 1) * (|ξ i| ^ (p - 2) * s i * w i) +
                ((2 - p) * a) * (|ξ i| ^ (p - 2) * ξ i * w i)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  simp
                  ring_nf
      _ = (p - 1) * ∑ i : Fin n, |ξ i| ^ (p - 2) * s i * w i +
            ((2 - p) * a) * ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * w i := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (p - 1) * ∑ i : Fin n, |ξ i| ^ (p - 2) * s i * w i +
            (∑ i : Fin n, (2 - p) * (|ξ i| ^ (p - 2) * ξ i * s i)) *
              ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * w i := by
                rw [show ((2 - p) * a) = ∑ i : Fin n, (2 - p) * (|ξ i| ^ (p - 2) * ξ i * s i) by
                  simp [a, B, Finset.mul_sum]]
      _ = (p - 1) * B s w + (2 - p) * B ξ s * B ξ w := by
            simp [B, Finset.mul_sum]
  have hAdjustedS_le : B adjustedS adjustedS ≤ (p - 1) ^ (2 : ℕ) * B s s := by
    have hAdjustedS_eq :
        B adjustedS adjustedS =
          (p - 1) ^ (2 : ℕ) * B s s +
            (2 - p) * (2 * (p - 1) + (2 - p) * B ξ ξ) * a ^ (2 : ℕ) := by
      calc
        B adjustedS adjustedS
            = (p - 1) * B s adjustedS + (2 - p) * B ξ s * B ξ adjustedS := hExpr adjustedS
        _ = (p - 1) * B adjustedS s + (2 - p) * B ξ s * B adjustedS ξ := by
              rw [hsym s adjustedS, hsym ξ adjustedS]
        _ = (p - 1) * ((p - 1) * B s s + (2 - p) * B ξ s * B ξ s) +
              (2 - p) * B ξ s * ((p - 1) * B s ξ + (2 - p) * B ξ s * B ξ ξ) := by
                rw [hExpr s, hExpr ξ]
        _ = (p - 1) ^ (2 : ℕ) * B s s +
              (2 - p) * (2 * (p - 1) + (2 - p) * B ξ ξ) * a ^ (2 : ℕ) := by
                rw [hsym s ξ]
                simp [a]
                ring_nf
    rw [hAdjustedS_eq]
    have hcoeff_nonpos :
        (2 - p) * (2 * (p - 1) + (2 - p) * B ξ ξ) ≤ 0 := by
      have hinner_nonneg : 0 ≤ 2 * (p - 1) + (2 - p) * B ξ ξ := by
        have hBp : B ξ ξ ≤ 1 := hBξξ_le
        have hmul_ge :
            (2 - p) * 1 ≤ (2 - p) * B ξ ξ := by
          exact mul_le_mul_of_nonpos_left hBp (by linarith)
        have h2mp_nonneg : 0 ≤ 2 * (p - 1) + (2 - p) * 1 := by linarith
        linarith
      have h2mp_nonpos : 2 - p ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg h2mp_nonpos hinner_nonneg
    have ha_sq_nonneg : 0 ≤ a ^ (2 : ℕ) := sq_nonneg a
    nlinarith
  have hsq :
      ((p - 1) * B s d + (2 - p) * B ξ s * B ξ d) ^ (2 : ℕ) ≤
        ((p - 1) * ‖s‖ * ‖d‖) ^ (2 : ℕ) := by
    rw [← hExpr d]
    have hCauchy :
        (B adjustedS d) ^ (2 : ℕ) ≤ B adjustedS adjustedS * B d d := by
      simpa [B, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (weightedCoordinateBilinear_sq_le (n := n) (p := p) hp_gt ξ adjustedS d)
    have hp_sq_nonneg : 0 ≤ (p - 1) ^ (2 : ℕ) := by positivity
    have hmul1 :
        B adjustedS adjustedS * B d d ≤ ((p - 1) ^ (2 : ℕ) * B s s) * B d d := by
      exact mul_le_mul_of_nonneg_right hAdjustedS_le (hBself_nonneg d)
    have hmul2 :
        ((p - 1) ^ (2 : ℕ) * B s s) * B d d ≤
          ((p - 1) ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) * B d d := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBss_le hp_sq_nonneg) (hBself_nonneg d)
    have hmul3 :
        ((p - 1) ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) * B d d ≤
          ((p - 1) ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) * ‖d‖ ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hBdd_le
        (mul_nonneg hp_sq_nonneg (sq_nonneg ‖s‖))
    have hbound :
        B adjustedS adjustedS * B d d ≤ ((p - 1) * ‖s‖ * ‖d‖) ^ (2 : ℕ) := by
      calc
        B adjustedS adjustedS * B d d
            ≤ ((p - 1) ^ (2 : ℕ) * B s s) * B d d := hmul1
        _ ≤ ((p - 1) ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) * B d d := hmul2
        _ ≤ ((p - 1) ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) * ‖d‖ ^ (2 : ℕ) := hmul3
        _ = ((p - 1) * ‖s‖ * ‖d‖) ^ (2 : ℕ) := by ring_nf
    exact le_trans hCauchy hbound
  have hrhs_nonneg : 0 ≤ (p - 1) * ‖s‖ * ‖d‖ := by
    exact mul_nonneg (mul_nonneg hp_one_nonneg (norm_nonneg _)) (norm_nonneg _)
  exact abs_le_of_sq_le_sq hsq hrhs_nonneg

/-- Helper for Proposition 5.5: away from `0`, the Fréchet derivative of the half-squared `ℓ_p`
norm is the pairing functional induced by the duality vector. -/
private theorem halfSquaredLpNorm_hasFDerivAt_nonzero [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_gt : 2 < p) (x : E) (hx : x ≠ 0) :
    HasFDerivAt (halfSquaredLpNorm n p)
      (LinearMap.toContinuousLinearMap
        (lpPairingDual (ENNReal.ofReal p)
          (halfSquaredLpNormDualVector x))) x := by
  let sumAbsP : E → ℝ := fun z ↦ ∑ i : Fin n, |z i| ^ p
  let derivSum : E →L[ℝ] ℝ :=
    ∑ i : Fin n,
      (p * |x i| ^ (p - 2) * x i) •
        (PiLp.proj (ENNReal.ofReal p) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)
  have hp_pos : 0 < p := lt_trans zero_lt_two hp_gt
  have hp_one : 1 < p := lt_trans one_lt_two hp_gt
  have hsum_ne : sumAbsP x ≠ 0 := by
    simpa [sumAbsP] using
      sumAbsRpow_ne_zero_of_ne_zero (n := n) (p := p) hp_pos hx
  have hsum :
      HasFDerivAt sumAbsP derivSum x := by
    -- Differentiate the coordinate power sum one coordinate at a time.
    simp only [sumAbsP, derivSum]
    refine HasFDerivAt.fun_sum ?_
    intro i hi
    have happly :
        HasFDerivAt (fun z : E ↦ z.ofLp i)
          (PiLp.proj (ENNReal.ofReal p) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ) x := by
      simpa using PiLp.hasFDerivAt_apply (ENNReal.ofReal p) x i
    have hcoord_i_raw :=
      (((hasDerivAt_abs_rpow (x.ofLp i) hp_one).hasFDerivAt).comp x happly)
    have hcoord_i :
        HasFDerivAt (fun z : E ↦ |z.ofLp i| ^ p)
          ((ContinuousLinearMap.toSpanSingleton ℝ
              (p * |x.ofLp i| ^ (p - 2) * x.ofLp i)).comp
            (PiLp.proj (ENNReal.ofReal p) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)) x := by
      simpa [Function.comp] using hcoord_i_raw
    have hproj_eq :
        ((ContinuousLinearMap.toSpanSingleton ℝ
            (p * |x.ofLp i| ^ (p - 2) * x.ofLp i)).comp
          (PiLp.proj (ENNReal.ofReal p) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)) =
          ((p * |x.ofLp i| ^ (p - 2) * x.ofLp i) •
            (PiLp.proj (ENNReal.ofReal p) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)) := by
      ext v
      simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
    rw [hproj_eq] at hcoord_i
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcoord_i
  have hpow :
      HasFDerivAt (fun z : E ↦ (sumAbsP z) ^ (2 / p))
        (((2 / p) * (sumAbsP x) ^ (2 / p - 1)) • derivSum) x := by
    -- The outer power is differentiable because the inner sum is nonzero on the nonzero branch.
    simpa using hsum.rpow_const (Or.inl hsum_ne)
  have hcoord :
      HasFDerivAt (fun z : E ↦ (1 / 2 : ℝ) * (sumAbsP z) ^ (2 / p))
        (((1 / 2 : ℝ) * ((2 / p) * (sumAbsP x) ^ (2 / p - 1))) • derivSum) x := by
    -- Scale the chain-rule result by the constant factor `1 / 2`.
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc, smul_eq_mul] using
      hpow.const_smul (1 / 2 : ℝ)
  have hfun :
      halfSquaredLpNorm n p = fun z : E ↦ (1 / 2 : ℝ) * (sumAbsP z) ^ (2 / p) := by
    -- Rewrite the owner function in the textbook coordinate form.
    funext z
    simpa [sumAbsP] using halfSquaredLpNorm_eq_coordinateFormula (n := n) (p := p) hp_pos z
  have hcoeff :
      ∀ i : Fin n,
        ((1 / 2 : ℝ) * ((2 / p) * (sumAbsP x) ^ (2 / p - 1))) *
            (p * |x i| ^ (p - 2) * x i) =
          halfSquaredLpNormDualVector x i := by
    intro i
    rw [halfSquaredLpNormDualVector_apply_of_ne_zero (x := x) hx i]
    rw [coordinatePowerFactor_eq_normFactor (n := n) (p := p) hp_gt hx]
    calc
      ((1 / 2 : ℝ) * ((2 / p) * ‖x‖ ^ (2 - p))) *
          (p * |x i| ^ (p - 2) * x i)
          = ‖x‖ ^ (2 - p) * (|x i| ^ (p - 2) * x i) := by
            field_simp [hp_pos.ne']
      _ = ‖x‖ ^ (2 - p) * (Real.sign (x i) * |x i| ^ (p - 1)) := by
            rw [absRpow_mul_eq_sign_mul_absRpow (hp_gt := hp_gt) (t := x i)]
      _ = ‖x‖ ^ (2 - p) * Real.sign (x i) * |x i| ^ (p - 1) := by ring_nf
  have hderiv_eq :
      (((1 / 2 : ℝ) * ((2 / p) * (sumAbsP x) ^ (2 / p - 1))) • derivSum) =
        LinearMap.toContinuousLinearMap
          (lpPairingDual (ENNReal.ofReal p) (halfSquaredLpNormDualVector x)) := by
    -- Route correction: compare the chain-rule linear map and the canonical pairing functional
    -- only after all scalar normalization has been pushed into the coordinate coefficients.
    ext v
    calc
      ((((1 / 2 : ℝ) * ((2 / p) * (sumAbsP x) ^ (2 / p - 1))) • derivSum) v)
          =
        ((1 / 2 : ℝ) * ((2 / p) * (sumAbsP x) ^ (2 / p - 1))) *
          ∑ i : Fin n, (p * |x i| ^ (p - 2) * x i) * v i := by
            simp [derivSum, smul_eq_mul]
      _ = ∑ i : Fin n,
            (((1 / 2 : ℝ) * ((2 / p) * (sumAbsP x) ^ (2 / p - 1))) *
              (p * |x i| ^ (p - 2) * x i)) * v i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring_nf
      _ = ∑ i : Fin n, halfSquaredLpNormDualVector x i * v i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hcoeff i]
      _ = dotProduct (halfSquaredLpNormDualVector x) (WithLp.ofLp v) := by
            simp [dotProduct]
      _ = dotProduct (WithLp.ofLp v) (halfSquaredLpNormDualVector x) := by
            rw [dotProduct_comm]
      _ = LinearMap.toContinuousLinearMap
            (lpPairingDual (ENNReal.ofReal p) (halfSquaredLpNormDualVector x)) v := by
            simp [lpPairingDual_apply]
  rw [hfun]
  rw [hderiv_eq] at hcoord
  simpa using hcoord

/-- Helper for Proposition 5.5: for `p > 2`, the Fréchet derivative of the half-squared `ℓ_p`
norm is the pairing functional induced by the duality vector. -/
private theorem halfSquaredLpNorm_hasFDerivAt [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_gt : 2 < p) (x : E) :
    HasFDerivAt (halfSquaredLpNorm n p)
      (LinearMap.toContinuousLinearMap
        (lpPairingDual (ENNReal.ofReal p)
          (halfSquaredLpNormDualVector x))) x :=
  by
    by_cases hx : x = 0
    · -- The singular point is purely quadratic, so the zero pairing functional is the derivative.
      subst hx
      have hpairing_zero :
          LinearMap.toContinuousLinearMap
              (lpPairingDual (ENNReal.ofReal p) (halfSquaredLpNormDualVector (0 : E))) =
            (0 : E →L[ℝ] ℝ) := by
        ext z
        simp [lpPairingDual_apply]
      rw [hpairing_zero]
      simpa [halfSquaredLpNorm] using (halfSquaredNorm_hasFDerivAt_zero (F := E))
    · -- The nonzero branch is isolated so the remaining blocker is exactly the
      -- coordinate-chain-rule computation, not a mixed singular/non-singular proof.
      exact halfSquaredLpNorm_hasFDerivAt_nonzero (n := n) (hp_gt := hp_gt) x hx

/-- Helper for Proposition 5.5: pairing against the duality vector factors into the scalar
coordinate sum from the source proof. -/
private theorem halfSquaredLpNormDualVector_pairing_eq_sumAbsPFactor
    [Fact (1 ≤ ENNReal.ofReal p)] (hp_gt : 2 < p) (z s : E) (hz : z ≠ 0) :
    dotProduct (WithLp.ofLp s) (halfSquaredLpNormDualVector z) =
      (∑ i : Fin n, |z i| ^ p) ^ (2 / p - 1) *
        ∑ i : Fin n, s i * (Real.sign (z i) * |z i| ^ (p - 1)) := by
  -- Rewrite the pairing into the scalar `coef * num` shape before differentiating along the
  -- segment.
  rw [halfSquaredLpNormDualVector_eq_of_ne_zero (x := z) hz, dotProduct]
  calc
    ∑ i : Fin n, s i * (‖z‖ ^ (2 - p) * Real.sign (z i) * |z i| ^ (p - 1))
        = ‖z‖ ^ (2 - p) * ∑ i : Fin n, s i * (Real.sign (z i) * |z i| ^ (p - 1)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring_nf
    _ = (∑ i : Fin n, |z i| ^ p) ^ (2 / p - 1) *
          ∑ i : Fin n, s i * (Real.sign (z i) * |z i| ^ (p - 1)) := by
            rw [← coordinatePowerFactor_eq_normFactor (n := n) (p := p) hp_gt hz]

/-- Helper for Proposition 5.5: the normalized scalar derivative model along the affine segment
from `x` to `y`. -/
private def halfSquaredLpNormDualVectorPairingLineDerivExpr
    [Fact (1 ≤ ENNReal.ofReal p)] (x y s : E) (t : ℝ) : ℝ :=
  let ξ : E := ‖AffineMap.lineMap x y t‖⁻¹ • AffineMap.lineMap x y t
  (p - 1) * (∑ i : Fin n, |ξ i| ^ (p - 2) * s i * (y - x) i) +
    (2 - p) * (∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * s i) *
      (∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * (y - x) i)

/-- Helper for Proposition 5.5: at a fixed nonzero point of the affine segment, the scalar
pairing with the duality vector has the normalized derivative predicted by the source Hessian
formula. -/
private theorem halfSquaredLpNormDualVector_pairing_hasDerivAt_line_nonzero
    [Fact (1 ≤ ENNReal.ofReal p)] (hp_gt : 2 < p) (x y s : E) (t : ℝ)
    (hz : AffineMap.lineMap x y t ≠ 0) :
    HasDerivAt
      (fun u : ℝ ↦
        dotProduct (WithLp.ofLp s)
          (halfSquaredLpNormDualVector (AffineMap.lineMap x y u)))
      (halfSquaredLpNormDualVectorPairingLineDerivExpr (p := p) x y s t) t := by
  let z : ℝ → E := AffineMap.lineMap x y
  let zt : E := z t
  let d : E := y - x
  let ξ : E := ‖zt‖⁻¹ • zt
  let coef : ℝ → ℝ := fun u ↦ (∑ i : Fin n, |z u i| ^ p) ^ (2 / p - 1)
  let num : ℝ → ℝ := fun u ↦
    ∑ i : Fin n, s i * (Real.sign (z u i) * |z u i| ^ (p - 1))
  have hp_pos : 0 < p := lt_trans zero_lt_two hp_gt
  have hp_one : 1 < p := lt_trans one_lt_two hp_gt
  have hline : HasDerivAt z d t := by
    -- Differentiate the affine segment once so every later scalar derivative can reuse it.
    simpa [z, d] using
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) :
        HasDerivAt (AffineMap.lineMap x y) (y - x) t)
  have hz_cont : ContinuousAt z t := hline.continuousAt
  have hz_ne : z t ≠ 0 := by
    simpa [z] using hz
  have hnonzero :
      ∀ᶠ u in 𝓝 t, z u ≠ 0 := by
    -- Route correction: rewrite to the scalar `coef * num` model only on the nonzero branch near
    -- the current segment point `z t`.
    exact hz_cont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hz_ne)
  have hrewrite :
      (fun u : ℝ ↦
        dotProduct (WithLp.ofLp s) (halfSquaredLpNormDualVector (z u))) =ᶠ[𝓝 t]
        (fun u : ℝ ↦ coef u * num u) := by
    filter_upwards [hnonzero] with u hu
    rw [halfSquaredLpNormDualVector_pairing_eq_sumAbsPFactor
      (n := n) (p := p) hp_gt (z u) s hu]
  have hcoord_apply (i : Fin n) :
      HasDerivAt (fun u : ℝ ↦ z u i) (d i) t := by
    -- Evaluate the affine-segment derivative on a single coordinate before applying the scalar
    -- one-variable derivative formulas.
    simpa [z, d] using
      HasFDerivAt.comp_hasDerivAt t
        (PiLp.hasFDerivAt_apply (ENNReal.ofReal p) (z t) i)
        hline
  have hsum :
      HasDerivAt
        (fun u : ℝ ↦ ∑ i : Fin n, |z u i| ^ p)
        (p * ∑ i : Fin n, |zt i| ^ (p - 2) * zt i * d i) t := by
    -- Differentiate the `p`-power coordinate sum term-by-term along the affine segment.
    have hsum_raw :
        HasDerivAt
          (fun u : ℝ ↦ ∑ i : Fin n, |z u i| ^ p)
          (∑ i : Fin n, (p * |zt i| ^ (p - 2) * zt i) * d i) t := by
      refine HasDerivAt.fun_sum (u := Finset.univ) ?_
      intro i hi
      simpa [zt, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_abs_rpow (zt i) hp_one).comp t (hcoord_apply i))
    convert hsum_raw using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring_nf
  have hsum_ne : ∑ i : Fin n, |zt i| ^ p ≠ 0 := by
    -- The nonzero branch keeps the scalar power sum away from `0`, so the outer `rpow`
    -- derivative is legitimate.
    simpa [zt] using
      (sumAbsRpow_ne_zero_of_ne_zero (n := n) (p := p) hp_pos (x := zt) hz_ne)
  have hcoef_raw :
      HasDerivAt coef
        ((p * ∑ i : Fin n, |zt i| ^ (p - 2) * zt i * d i) *
          (2 / p - 1) * (∑ i : Fin n, |zt i| ^ p) ^ (2 / p - 2)) t := by
    -- Apply the one-variable `rpow` chain rule to the scalar coefficient.
    have hexp : 2 / p - 1 - 1 = 2 / p - 2 := by ring_nf
    have hcoef_raw' := hsum.rpow_const (p := 2 / p - 1) (Or.inl hsum_ne)
    suffices
        HasDerivAt
          (fun u : ℝ ↦ (∑ i : Fin n, |z u i| ^ p) ^ (2 / p - 1))
          ((p * ∑ i : Fin n, |zt i| ^ (p - 2) * zt i * d i) *
            (2 / p - 1) * (∑ i : Fin n, |zt i| ^ p) ^ (2 / p - 2)) t by
      simpa [coef] using this
    convert hcoef_raw' using 1
    simp [zt, hexp]
  have hnum_raw :
      HasDerivAt num
        (∑ i : Fin n, s i * ((p - 1) * |zt i| ^ (p - 2) * d i)) t := by
    -- Differentiate the coordinate scalar `sign(z_i) * |z_i|^(p-1)` term-by-term.
    refine HasDerivAt.fun_sum (u := Finset.univ) ?_
    intro i hi
    simpa [num, zt, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_sign_mul_absRpow (p := p) hp_gt (zt i)).comp t
        (hcoord_apply i)).const_mul (s i)
  have hnum :
      HasDerivAt num
        ((p - 1) * ∑ i : Fin n, |zt i| ^ (p - 2) * s i * d i) t := by
    -- Pull the common scalar factor `(p - 1)` outside the coordinate sum.
    convert hnum_raw using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring_nf
  have hzt_pos : 0 < ‖zt‖ := norm_pos_iff.mpr hz_ne
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, |zt i| ^ p := by
    exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hnorm_eq_sum :
      ‖zt‖ = (∑ i : Fin n, |zt i| ^ p) ^ (1 / p) := by
    -- Use the canonical finite-dimensional `ℓ_p` norm formula at the fixed segment point `zt`.
    have hp_toReal : 0 < (ENNReal.ofReal p).toReal := by
      simpa [ENNReal.toReal_ofReal hp_pos.le] using hp_pos
    simpa [zt, PiLp.toLp_apply, Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le] using
      (PiLp.norm_eq_sum (p := ENNReal.ofReal p) hp_toReal zt)
  have hsum_pow :
      (∑ i : Fin n, |zt i| ^ p) ^ (2 / p - 2) = ‖zt‖ ^ (2 - 2 * p) := by
    -- Normalize the outer scalar coefficient to the ambient norm of `zt`.
    calc
      (∑ i : Fin n, |zt i| ^ p) ^ (2 / p - 2)
          = (∑ i : Fin n, |zt i| ^ p) ^ ((1 / p) * (2 - 2 * p)) := by
              congr 1
              field_simp [hp_pos.ne']
      _ = ((∑ i : Fin n, |zt i| ^ p) ^ (1 / p)) ^ (2 - 2 * p) := by
            rw [Real.rpow_mul hsum_nonneg]
      _ = ‖zt‖ ^ (2 - 2 * p) := by rw [hnorm_eq_sum]
  have hcoord_eq (i : Fin n) : zt i = ‖zt‖ * ξ i := by
    -- Rewrite each coordinate through the normalized point `ξ = ‖zt‖⁻¹ • zt`.
    calc
      zt i = ‖zt‖ * (‖zt‖⁻¹ * zt i) := by
        field_simp [hzt_pos.ne']
      _ = ‖zt‖ * ξ i := by
        simp [ξ]
  have hweighted_coord (i : Fin n) :
      |zt i| ^ (p - 2) * zt i = ‖zt‖ ^ (p - 1) * (|ξ i| ^ (p - 2) * ξ i) := by
    -- Move the mixed `|zt_i|^(p-2) * zt_i` weight to the normalized coordinates.
    have hnorm_factor : ‖zt‖ ^ (p - 2) * ‖zt‖ = ‖zt‖ ^ (p - 1) := by
      calc
        ‖zt‖ ^ (p - 2) * ‖zt‖ = ‖zt‖ ^ ((p - 2) + 1) := by
          simpa using (Real.rpow_add hzt_pos (p - 2) 1).symm
        _ = ‖zt‖ ^ (p - 1) := by
              congr 1
              ring_nf
    rw [hcoord_eq i, abs_mul, abs_of_nonneg (norm_nonneg zt),
      Real.mul_rpow (norm_nonneg zt) (abs_nonneg (ξ i))]
    calc
      (‖zt‖ ^ (p - 2) * |ξ i| ^ (p - 2)) * (‖zt‖ * ξ i)
          = (‖zt‖ ^ (p - 2) * ‖zt‖) * (|ξ i| ^ (p - 2) * ξ i) := by ring_nf
      _ = ‖zt‖ ^ (p - 1) * (|ξ i| ^ (p - 2) * ξ i) := by rw [hnorm_factor]
  have hpairing_coord (i : Fin n) :
      Real.sign (zt i) * |zt i| ^ (p - 1) =
        ‖zt‖ ^ (p - 1) * (|ξ i| ^ (p - 2) * ξ i) := by
    -- The pairing numerator carries the same normalized weight after factoring out `‖zt‖`.
    calc
      Real.sign (zt i) * |zt i| ^ (p - 1) = |zt i| ^ (p - 2) * zt i := by
        symm
        exact absRpow_mul_eq_sign_mul_absRpow (hp_gt := hp_gt) (t := zt i)
      _ = ‖zt‖ ^ (p - 1) * (|ξ i| ^ (p - 2) * ξ i) := hweighted_coord i
  have hpow_coord (i : Fin n) :
      |zt i| ^ (p - 2) = ‖zt‖ ^ (p - 2) * |ξ i| ^ (p - 2) := by
    -- The pure `|zt_i|^(p-2)` weight also factors through `ξ`.
    rw [hcoord_eq i]
    rw [abs_mul, abs_of_nonneg (norm_nonneg zt),
      Real.mul_rpow (norm_nonneg zt) (abs_nonneg (ξ i))]
  have hweighted_sum :
      ∑ i : Fin n, |zt i| ^ (p - 2) * zt i * d i =
        ‖zt‖ ^ (p - 1) *
          ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i := by
    -- Factor the common `‖zt‖^(p-1)` from the weighted derivative coefficient.
    calc
      ∑ i : Fin n, |zt i| ^ (p - 2) * zt i * d i
          = ∑ i : Fin n, ‖zt‖ ^ (p - 1) * (|ξ i| ^ (p - 2) * ξ i * d i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hweighted_coord i]
              ring_nf
      _ = ‖zt‖ ^ (p - 1) * ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i := by
            symm
            rw [Finset.mul_sum]
  have hweighted_sum_comm :
      ∑ i : Fin n, d i * (zt i * |zt i| ^ (p - 2)) =
        ‖zt‖ ^ (p - 1) * ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i := by
    calc
      ∑ i : Fin n, d i * (zt i * |zt i| ^ (p - 2))
          = ∑ i : Fin n, |zt i| ^ (p - 2) * zt i * d i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring_nf
      _ = ‖zt‖ ^ (p - 1) * ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i := hweighted_sum
  have hpairing_sum :
      num t = ‖zt‖ ^ (p - 1) * ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * s i := by
    -- Evaluate the scalar numerator at `t` in the normalized coordinates.
    calc
      num t = ∑ i : Fin n, s i * (Real.sign (zt i) * |zt i| ^ (p - 1)) := by
        simp [num, zt]
      _ = ∑ i : Fin n, ‖zt‖ ^ (p - 1) * (|ξ i| ^ (p - 2) * ξ i * s i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hpairing_coord i]
            ring_nf
      _ = ‖zt‖ ^ (p - 1) * ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * s i := by
            symm
            rw [Finset.mul_sum]
  have hquadratic_sum :
      ∑ i : Fin n, |zt i| ^ (p - 2) * s i * d i =
        ‖zt‖ ^ (p - 2) * ∑ i : Fin n, |ξ i| ^ (p - 2) * s i * d i := by
    -- Normalize the first weighted bilinear term in the same way.
    calc
      ∑ i : Fin n, |zt i| ^ (p - 2) * s i * d i
          = ∑ i : Fin n, ‖zt‖ ^ (p - 2) * (|ξ i| ^ (p - 2) * s i * d i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hpow_coord i]
              ring_nf
      _ = ‖zt‖ ^ (p - 2) * ∑ i : Fin n, |ξ i| ^ (p - 2) * s i * d i := by
            symm
            rw [Finset.mul_sum]
  have hcancel_pairing : ‖zt‖ ^ (1 - p) * ‖zt‖ ^ (p - 1) = 1 := by
    calc
      ‖zt‖ ^ (1 - p) * ‖zt‖ ^ (p - 1) = ‖zt‖ ^ ((1 - p) + (p - 1)) := by
        rw [← Real.rpow_add hzt_pos]
      _ = ‖zt‖ ^ (0 : ℝ) := by
            congr 1
            ring_nf
      _ = 1 := by simp
  have hcancel_quadratic : ‖zt‖ ^ (2 - p) * ‖zt‖ ^ (p - 2) = 1 := by
    calc
      ‖zt‖ ^ (2 - p) * ‖zt‖ ^ (p - 2) = ‖zt‖ ^ ((2 - p) + (p - 2)) := by
        rw [← Real.rpow_add hzt_pos]
      _ = ‖zt‖ ^ (0 : ℝ) := by
            congr 1
            ring_nf
      _ = 1 := by simp
  have hcoef_val : coef t = ‖zt‖ ^ (2 - p) := by
    -- Evaluate the scalar coefficient at `t` before the final product-rule simplification.
    simpa [coef, zt] using
      (coordinatePowerFactor_eq_normFactor (n := n) (p := p) hp_gt (x := zt) hz_ne)
  have hcoef :
      HasDerivAt coef
        ((2 - p) * ‖zt‖ ^ (1 - p) *
          ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i) t := by
    -- Rewrite the scalar coefficient derivative completely in the normalized `ξ` coordinates.
    have hcoeff : (2 / p - 1) * p = 2 - p := by
      field_simp [hp_pos.ne']
    have hnorm_factor :
        ‖zt‖ ^ (2 - 2 * p) * ‖zt‖ ^ (p - 1) = ‖zt‖ ^ (1 - p) := by
      calc
        ‖zt‖ ^ (2 - 2 * p) * ‖zt‖ ^ (p - 1) = ‖zt‖ ^ ((2 - 2 * p) + (p - 1)) := by
          rw [← Real.rpow_add hzt_pos]
        _ = ‖zt‖ ^ (1 - p) := by
              congr 1
              ring_nf
    have hcoef_eq :
        ((p * (‖zt‖ ^ (p - 1) * ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i)) *
            (2 / p - 1)) * ‖zt‖ ^ (2 - 2 * p) =
          (2 - p) * ‖zt‖ ^ (1 - p) *
            ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i := by
      calc
        ((p * (‖zt‖ ^ (p - 1) * ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i)) *
            (2 / p - 1)) * ‖zt‖ ^ (2 - 2 * p)
            =
          p * ((2 / p - 1) *
            ((‖zt‖ ^ (2 - 2 * p) * ‖zt‖ ^ (p - 1)) *
              ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i)) := by
                ring_nf
        _ = p *
            ((2 / p - 1) *
              (‖zt‖ ^ (1 - p) * ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i)) := by
              rw [hnorm_factor]
        _ = (2 - p) * ‖zt‖ ^ (1 - p) *
            ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i := by
              field_simp [hp_pos.ne']
    convert hcoef_raw using 1
    rw [hweighted_sum, hsum_pow]
    exact hcoef_eq.symm
  have hprod :
      HasDerivAt (fun u : ℝ ↦ coef u * num u)
        (halfSquaredLpNormDualVectorPairingLineDerivExpr (p := p) x y s t) t := by
    -- Finish the product rule and cancel the ambient norm powers against the normalized sums.
    set A : ℝ := ∑ i : Fin n, |ξ i| ^ (p - 2) * s i * d i
    set B : ℝ := ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * s i
    set C : ℝ := ∑ i : Fin n, |ξ i| ^ (p - 2) * ξ i * d i
    have hprod_eq :
        ‖zt‖ ^ (2 - p) * ((p - 1) * (‖zt‖ ^ (p - 2) * A)) +
          ((2 - p) * ‖zt‖ ^ (1 - p) * C) * (‖zt‖ ^ (p - 1) * B) =
          (p - 1) * A + (2 - p) * B * C := by
      calc
        ‖zt‖ ^ (2 - p) * ((p - 1) * (‖zt‖ ^ (p - 2) * A)) +
            ((2 - p) * ‖zt‖ ^ (1 - p) * C) * (‖zt‖ ^ (p - 1) * B)
            =
          (p - 1) * (‖zt‖ ^ (2 - p) * ‖zt‖ ^ (p - 2)) * A +
            (2 - p) * (‖zt‖ ^ (1 - p) * ‖zt‖ ^ (p - 1)) * (C * B) := by
                ring_nf
        _ = (p - 1) * A + (2 - p) * B * C := by
              rw [hcancel_quadratic, hcancel_pairing]
              ring_nf
    have htarget :
        (p - 1) * A + (2 - p) * B * C =
          halfSquaredLpNormDualVectorPairingLineDerivExpr (p := p) x y s t := by
      simp [A, B, C, halfSquaredLpNormDualVectorPairingLineDerivExpr, z, zt, ξ, d]
    convert hcoef.mul hnum using 1
    rw [hcoef_val, hpairing_sum, hquadratic_sum]
    calc
      halfSquaredLpNormDualVectorPairingLineDerivExpr (p := p) x y s t
          = (p - 1) * A + (2 - p) * B * C := htarget.symm
      _ = ‖zt‖ ^ (2 - p) * ((p - 1) * (‖zt‖ ^ (p - 2) * A)) +
            ((2 - p) * ‖zt‖ ^ (1 - p) * C) * (‖zt‖ ^ (p - 1) * B) := hprod_eq.symm
      _ = ((2 - p) * ‖zt‖ ^ (1 - p) * C) * (‖zt‖ ^ (p - 1) * B) +
            ‖zt‖ ^ (2 - p) * ((p - 1) * (‖zt‖ ^ (p - 2) * A)) := by ring_nf
  exact hprod.congr_of_eventuallyEq hrewrite

/-- Helper for Proposition 5.5: once the affine-segment point is normalized to unit norm, the
scalar derivative expression is bounded by `(p - 1) * ‖y - x‖`. -/
private theorem halfSquaredLpNormDualVector_pairingDeriv_bound_nonzero
    [Fact (1 ≤ ENNReal.ofReal p)] (hp_gt : 2 < p) (x y s : E) (t : ℝ)
    (hz : AffineMap.lineMap x y t ≠ 0) (hs : ‖s‖ ≤ 1) :
    |halfSquaredLpNormDualVectorPairingLineDerivExpr (p := p) x y s t| ≤
      (p - 1) * ‖y - x‖ := by
  let zt : E := AffineMap.lineMap x y t
  let ξ : E := ‖zt‖⁻¹ • zt
  have hp_one_nonneg : 0 ≤ p - 1 := by
    linarith
  have hzt_pos : 0 < ‖zt‖ := norm_pos_iff.mpr (by simpa [zt] using hz)
  have hξ_norm : ‖ξ‖ = 1 := by
    -- Normalize the affine-segment point to the unit sphere before invoking the weighted
    -- rank-one estimate.
    rw [show ξ = ‖zt‖⁻¹ • zt by rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hzt_pos), inv_mul_cancel₀ hzt_pos.ne']
  have hbase := weightedRankOnePerturbation_le (n := n) (p := p) hp_gt hξ_norm s (y - x)
  have hs_le :
      (p - 1) * ‖s‖ * ‖y - x‖ ≤ (p - 1) * 1 * ‖y - x‖ := by
    have hleft : (p - 1) * ‖s‖ ≤ (p - 1) * 1 := by
      exact mul_le_mul_of_nonneg_left hs hp_one_nonneg
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hleft (norm_nonneg (y - x))
  calc
    |halfSquaredLpNormDualVectorPairingLineDerivExpr (p := p) x y s t|
        ≤ (p - 1) * ‖s‖ * ‖y - x‖ := by
            simpa [halfSquaredLpNormDualVectorPairingLineDerivExpr, zt, ξ]
              using hbase
    _ ≤ (p - 1) * 1 * ‖y - x‖ := hs_le
    _ = (p - 1) * ‖y - x‖ := by ring_nf

/-- Helper for Proposition 5.5: on a segment that avoids `0`, the scalar pairing with the duality
vector is `(p - 1)`-Lipschitz against every unit test vector. -/
private theorem halfSquaredLpNormDualVector_pairingBound_nonzeroSegment
    [Fact (1 ≤ ENNReal.ofReal p)] (hp_gt : 2 < p) (x y s : E)
    (hseg : (0 : E) ∉ segment ℝ x y) (hs : ‖s‖ ≤ 1) :
    |dotProduct (WithLp.ofLp s)
      (halfSquaredLpNormDualVector y - halfSquaredLpNormDualVector x)| ≤
      (p - 1) * ‖x - y‖ :=
  by
    let z : ℝ → E := AffineMap.lineMap x y
    let φ : ℝ → ℝ := fun t ↦
      dotProduct (WithLp.ofLp s) (halfSquaredLpNormDualVector (z t))
    -- Route correction: the only remaining calculus input is the fixed-`t` derivative formula.
    -- Once that is packaged, the segment argument is the same one-dimensional mean-value step as
    -- in Proposition 5.9.
    have hz :
        ∀ t ∈ Set.Icc (0 : ℝ) 1, z t ≠ 0 := by
      intro t ht hzero
      apply hseg
      rw [segment_eq_image_lineMap]
      refine ⟨t, ht, ?_⟩
      simpa [z] using hzero
    have hdiff :
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivWithinAt φ
            (halfSquaredLpNormDualVectorPairingLineDerivExpr (p := p) x y s t)
            (Set.Icc (0 : ℝ) 1) t := by
      intro t ht
      -- Restrict the fixed-`t` derivative formula to the segment domain `[0, 1]`.
      exact
        (halfSquaredLpNormDualVector_pairing_hasDerivAt_line_nonzero
          (n := n) (p := p) hp_gt x y s t (hz t ht)).hasDerivWithinAt
    have hbound :
        ∀ t ∈ Set.Ico (0 : ℝ) 1,
          ‖halfSquaredLpNormDualVectorPairingLineDerivExpr (p := p) x y s t‖ ≤
            (p - 1) * ‖x - y‖ := by
      intro t ht
      rw [Real.norm_eq_abs]
      have hbound_t :=
        halfSquaredLpNormDualVector_pairingDeriv_bound_nonzero
          (n := n) (p := p) hp_gt x y s t
          (hz t ⟨ht.1, le_of_lt ht.2⟩) hs
      simpa [norm_sub_rev] using hbound_t
    have hMv := norm_image_sub_le_of_norm_deriv_le_segment_01' hdiff hbound
    have hrewrite :
        φ 1 - φ 0 =
          dotProduct (WithLp.ofLp s)
            (halfSquaredLpNormDualVector y - halfSquaredLpNormDualVector x) := by
      -- Evaluate the line map at the endpoints and collapse the pairing difference.
      rw [show φ 1 = dotProduct (WithLp.ofLp s) (halfSquaredLpNormDualVector y) by
        simp [φ, z, AffineMap.lineMap_apply_one]]
      rw [show φ 0 = dotProduct (WithLp.ofLp s) (halfSquaredLpNormDualVector x) by
        simp [φ, z, AffineMap.lineMap_apply_zero]]
      exact (dotProduct_sub (WithLp.ofLp s) (halfSquaredLpNormDualVector y)
        (halfSquaredLpNormDualVector x)).symm
    rw [Real.norm_eq_abs] at hMv
    simpa [hrewrite] using hMv

/-- Helper for Proposition 5.5: for `p > 2`, the derivative field of the half-squared `ℓ_p` norm
is globally `(p - 1)`-Lipschitz in operator norm. -/
private theorem halfSquaredLpNorm_fderiv_sub_opNorm_le [Fact (1 ≤ ENNReal.ofReal p)]
    (hp_gt : 2 < p) (x y : E) :
    ‖fderiv ℝ (halfSquaredLpNorm n p) x - fderiv ℝ (halfSquaredLpNorm n p) y‖ ≤
      (p - 1) * ‖x - y‖ := by
  -- Route correction: the nonzero-segment branch comes from the scalar pairing estimate via
  -- `opNorm_le_bound`, while the zero-crossing branch is controlled by homogeneity and the exact
  -- `ℓ_q` norm of the duality vector.
  let q : ENNReal := ENNReal.conjExponent (ENNReal.ofReal p)
  letI : Fact (1 ≤ q) :=
    ⟨ENNReal.HolderConjugate.oneLeRight
      (p := ENNReal.ofReal p) (q := ENNReal.conjExponent (ENNReal.ofReal p)) inferInstance⟩
  have hp_nonneg : 0 ≤ p - 1 := by linarith
  by_cases hseg : (0 : E) ∈ segment ℝ x y
  · have hsame : SameRay ℝ x (-y) := by
      rw [← sameRay_neg_iff]
      simpa using (sameRay_of_mem_segment hseg : SameRay ℝ ((0 : E) - x) (y - (0 : E)))
    have hnorm_sub :
        ‖x - y‖ = ‖x‖ + ‖y‖ := by
      calc
        ‖x - y‖ = ‖x + (-y)‖ := by simp [sub_eq_add_neg]
        _ = ‖x‖ + ‖-y‖ := hsame.norm_add
        _ = ‖x‖ + ‖y‖ := by simp
    rw [norm_sub_rev, (halfSquaredLpNorm_hasFDerivAt (n := n) (hp_gt := hp_gt) y).fderiv,
      (halfSquaredLpNorm_hasFDerivAt (n := n) (hp_gt := hp_gt) x).fderiv,
      lpPairingDual_sub_norm_eq (q := ENNReal.ofReal p)
        (u := halfSquaredLpNormDualVector y) (v := halfSquaredLpNormDualVector x)]
    calc
      ‖toLp q (halfSquaredLpNormDualVector y - halfSquaredLpNormDualVector x)‖
          = ‖toLp q (halfSquaredLpNormDualVector y) - toLp q (halfSquaredLpNormDualVector x)‖ := by
              rfl
      _ ≤ ‖toLp q (halfSquaredLpNormDualVector y)‖ + ‖toLp q (halfSquaredLpNormDualVector x)‖ := by
            exact norm_sub_le _ _
      _ = ‖y‖ + ‖x‖ := by
            rw [halfSquaredLpNormDualVector_conjExponent_norm_eq (n := n) (p := p) hp_gt.le y,
              halfSquaredLpNormDualVector_conjExponent_norm_eq (n := n) (p := p) hp_gt.le x]
      _ ≤ (p - 1) * ‖x - y‖ := by
            have hp_one : 1 ≤ p - 1 := by linarith
            calc
              ‖y‖ + ‖x‖ = ‖x‖ + ‖y‖ := by ring_nf
              _ ≤ (p - 1) * (‖x‖ + ‖y‖) := by
                    nlinarith [norm_nonneg x, norm_nonneg y]
              _ = (p - 1) * ‖x - y‖ := by rw [hnorm_sub]
  · rw [norm_sub_rev, (halfSquaredLpNorm_hasFDerivAt (n := n) (hp_gt := hp_gt) y).fderiv,
      (halfSquaredLpNorm_hasFDerivAt (n := n) (hp_gt := hp_gt) x).fderiv]
    have hsub :
        LinearMap.toContinuousLinearMap
            (lpPairingDual (ENNReal.ofReal p) (halfSquaredLpNormDualVector y)) -
          LinearMap.toContinuousLinearMap
            (lpPairingDual (ENNReal.ofReal p) (halfSquaredLpNormDualVector x)) =
        LinearMap.toContinuousLinearMap
          (lpPairingDual (ENNReal.ofReal p)
            (halfSquaredLpNormDualVector y - halfSquaredLpNormDualVector x)) :=
      congrArg LinearMap.toContinuousLinearMap <|
        lpPairingDual_sub_eq (ENNReal.ofReal p)
          (halfSquaredLpNormDualVector y) (halfSquaredLpNormDualVector x)
    rw [hsub]
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hp_nonneg (norm_nonneg _)) ?_
    intro s
    by_cases hs0 : s = 0
    · subst hs0
      simp [lpPairingDual_apply]
    · have hs_norm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
      let t : E := (‖s‖)⁻¹ • s
      have ht_norm : ‖t‖ ≤ 1 := by
        -- Normalize the test vector so the scalar segment estimate applies.
        dsimp [t]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
          inv_mul_cancel₀ hs_norm_pos.ne']
      have hpair_t :=
        halfSquaredLpNormDualVector_pairingBound_nonzeroSegment
          (n := n) (p := p) hp_gt x y t hseg ht_norm
      have hscale_abs :
          |dotProduct (WithLp.ofLp t)
              (halfSquaredLpNormDualVector y - halfSquaredLpNormDualVector x)| =
            ‖s‖⁻¹ *
              |dotProduct (WithLp.ofLp s)
                (halfSquaredLpNormDualVector y - halfSquaredLpNormDualVector x)| := by
        dsimp [t]
        rw [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
      have hpair_s :
          |dotProduct (WithLp.ofLp s)
              (halfSquaredLpNormDualVector y - halfSquaredLpNormDualVector x)| ≤
            ((p - 1) * ‖x - y‖) * ‖s‖ := by
        rw [hscale_abs] at hpair_t
        have hmul := mul_le_mul_of_nonneg_left hpair_t hs_norm_pos.le
        simpa [mul_assoc, hs_norm_pos.ne', mul_left_comm, mul_comm] using hmul
      simpa [lpPairingDual_apply] using hpair_s

/-- Helper for Proposition 5.5: the internal owner theorem giving global `(p - 1)`-smoothness for
the half-squared `ℓ_p` norm. -/
private theorem halfSquaredLpNorm_isLSmooth_internal [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) :
    is_l_smooth_on (halfSquaredLpNorm n p) Set.univ (Real.toNNReal (p - 1)) :=
  by
    by_cases h_two : p = 2
    · -- The Euclidean endpoint is already covered by the Hilbert-space smoothness theorem.
      subst h_two
      norm_num
      simpa using halfSquaredLpNorm_two_isLSmooth (n := n)
    · -- Away from the Euclidean endpoint, smoothness is exactly differentiability plus global
      -- Lipschitz control of the Fréchet derivative field.
      have hp_gt : 2 < p := lt_of_le_of_ne hp (fun h => h_two h.symm)
      rw [is_l_smooth_on_iff]
      refine ⟨?_, ?_⟩
      · intro x hx
        exact (halfSquaredLpNorm_hasFDerivAt (n := n) (hp_gt := hp_gt) x).differentiableAt
      · intro x hx y hy
        have h_nonneg : 0 ≤ p - 1 := by linarith
        simpa [Real.toNNReal_of_nonneg h_nonneg] using
          (halfSquaredLpNorm_fderiv_sub_opNorm_le
            (n := n) (hp_gt := hp_gt) x y)

namespace HalfSquaredLpNorm

/-- Canonical Chapter 5 owner theorem: for `p ≥ 2`, the half-squared `ℓ_p` norm on the canonical
`WithLp` model is globally `(p - 1)`-smooth. -/
theorem isLSmooth [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) :
    is_l_smooth_on (halfSquaredLpNorm n p) Set.univ (Real.toNNReal (p - 1)) :=
  halfSquaredLpNorm_isLSmooth_internal hp

/-- Banach-space quadratic upper-model companion for `halfSquaredLpNorm`, stated with `fderiv` on
the canonical `WithLp` model. -/
theorem upperModel [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 ≤ p) (x y : E) :
    halfSquaredLpNorm n p y ≤
      halfSquaredLpNorm n p x
        + fderiv ℝ (halfSquaredLpNorm n p) x (y - x)
        + ((p - 1) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  have h_nonneg : 0 ≤ p - 1 := by linarith
  simpa [Real.toNNReal_of_nonneg h_nonneg, norm_sub_rev] using
    is_l_smooth_on_univ_fderiv_descent (isLSmooth hp) x y

/-- Source-facing Proposition 5.5 smoothness statement, with the `WithLp` side condition hidden
behind the hypothesis `2 ≤ p`. -/
def IsLSmooth (n : ℕ) (p : ℝ) (hp : 2 ≤ p) : Prop :=
  letI := factOneLeOfRealOfTwoLe hp
  is_l_smooth_on (halfSquaredLpNorm n p) Set.univ (Real.toNNReal (p - 1))

/-- Unfolding `HalfSquaredLpNorm.IsLSmooth` recovers the canonical owner statement with the
hidden `WithLp` side condition restored from `2 ≤ p`. -/
@[simp] theorem IsLSmooth_iff (hp : 2 ≤ p) :
    IsLSmooth n p hp ↔
      letI := factOneLeOfRealOfTwoLe hp
      is_l_smooth_on (halfSquaredLpNorm n p) Set.univ (Real.toNNReal (p - 1)) := by
  simp [IsLSmooth]

/-- A `HalfSquaredLpNorm.IsLSmooth` hypothesis may be applied directly as the canonical owner
statement. -/
theorem IsLSmooth.apply {hp : 2 ≤ p} (h : IsLSmooth n p hp) :
    letI := factOneLeOfRealOfTwoLe hp
    is_l_smooth_on (halfSquaredLpNorm n p) Set.univ (Real.toNNReal (p - 1)) := by
  simpa using h

/-- Source-facing quadratic upper-model statement for the half-squared `ℓ_p` norm, with the
`WithLp` side condition derived internally from `2 ≤ p`. -/
def SatisfiesUpperModel (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (x y : WithLp (ENNReal.ofReal p) (Fin n → ℝ)) : Prop :=
  letI := factOneLeOfRealOfTwoLe hp
  halfSquaredLpNorm n p y ≤
    halfSquaredLpNorm n p x
      + fderiv ℝ (halfSquaredLpNorm n p) x (y - x)
      + ((p - 1) / 2) * ‖x - y‖ ^ (2 : ℕ)

/-- Unfolding `HalfSquaredLpNorm.SatisfiesUpperModel` recovers the displayed quadratic upper-model
inequality with the hidden `WithLp` side condition restored from `2 ≤ p`. -/
@[simp] theorem SatisfiesUpperModel_iff (hp : 2 ≤ p) (x y : E) :
    SatisfiesUpperModel n p hp x y ↔
      letI := factOneLeOfRealOfTwoLe hp
      halfSquaredLpNorm n p y ≤
        halfSquaredLpNorm n p x
          + fderiv ℝ (halfSquaredLpNorm n p) x (y - x)
          + ((p - 1) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  simp [SatisfiesUpperModel]

/-- A `HalfSquaredLpNorm.SatisfiesUpperModel` hypothesis may be applied directly as the displayed
quadratic upper-model inequality. -/
theorem SatisfiesUpperModel.apply {hp : 2 ≤ p} {x y : E}
    (h : SatisfiesUpperModel n p hp x y) :
    letI := factOneLeOfRealOfTwoLe hp
    halfSquaredLpNorm n p y ≤
      halfSquaredLpNorm n p x
        + fderiv ℝ (halfSquaredLpNorm n p) x (y - x)
        + ((p - 1) / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  simpa using h

end HalfSquaredLpNorm

/- Proposition 5.5 is `source-facing`: the textbook object is the half-squared `ℓ_p` norm on
`ℝ^n`. Domain sampling identifies the ambient owner object as the canonical `WithLp` model and
the chapter owner property as `is_l_smooth_on`; the quadratic upper model is a companion
`bridge/view` consequence of that owner-level smoothness statement. The file names the source
function itself as `halfSquaredLpNorm`, keeps the canonical owner theorems under
`HalfSquaredLpNorm`, and exposes source-facing wrappers `HalfSquaredLpNorm.IsLSmooth` and
`HalfSquaredLpNorm.SatisfiesUpperModel` so the public label theorems do not need theorem-local
`letI` scaffolding. -/

-- Proof sketch: prove first that `x ↦ ‖x‖² / 2` on `E` is differentiable for `p ≥ 2`, compute
-- its Fréchet derivative in the canonical `WithLp` normed-space model, and then bound the
-- derivative difference by `p - 1` using the coordinate estimates from the textbook proof
-- together with Hölder/Cauchy-Schwarz.
/-- Proposition 5.5: for `p ≥ 2`, the half-squared `ℓ_p` norm on `ℝ^n`, viewed on the canonical
`WithLp` model, is globally `(p - 1)`-smooth with respect to the `ℓ_p` norm. This is the
owner-level Chapter 5 formulation of the textbook statement. -/
theorem half_squared_lp_norm_is_l_smooth (hp : 2 ≤ p) :
    HalfSquaredLpNorm.IsLSmooth n p hp := by
  dsimp [HalfSquaredLpNorm.IsLSmooth]
  letI := factOneLeOfRealOfTwoLe hp
  simpa using HalfSquaredLpNorm.isLSmooth hp

-- Proof sketch: combine the owner-level smoothness theorem with the standard second-order upper
-- model estimate for an `L`-smooth function. Here this is the global bridge
-- `is_l_smooth_on_univ_fderiv_descent`, specialized to `halfSquaredLpNorm n p` on the canonical
-- `WithLp` model.
/-- Companion upper-model theorem: the half-squared `ℓ_p` norm satisfies the textbook quadratic
model with constant `p - 1`. -/
theorem half_squared_lp_norm_upper_model (hp : 2 ≤ p) (x y : E) :
    HalfSquaredLpNorm.SatisfiesUpperModel n p hp x y := by
  dsimp [HalfSquaredLpNorm.SatisfiesUpperModel]
  letI := factOneLeOfRealOfTwoLe hp
  simpa using HalfSquaredLpNorm.upperModel hp x y

end
