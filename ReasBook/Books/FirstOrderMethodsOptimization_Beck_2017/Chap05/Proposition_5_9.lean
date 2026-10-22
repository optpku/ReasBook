/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Proposition_1_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_35
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_17
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

section

variable {n : ℕ}

local notation "E" => WithLp (⊤ : ENNReal) (Fin n → ℝ)

/-- Helper for Proposition 5.9: in positive dimension, the softmax denominator
`∑ j, exp (x j)` is strictly positive. -/
private theorem expSum_pos [NeZero n] (x : Fin n → ℝ) :
    0 < ∑ j : Fin n, Real.exp (x j) := by
  -- Use one coordinate of the finite sum to witness strict positivity.
  let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  refine lt_of_lt_of_le (Real.exp_pos (x i0)) ?_
  exact Finset.single_le_sum (fun j _ ↦ le_of_lt (Real.exp_pos (x j))) (by simp)

/-- Helper for Proposition 5.9: the `ℓ∞/ℓ¹` pairing functional has operator norm equal to the
`ℓ₁` norm of its coefficient vector. -/
private theorem lpPairingDual_top_operatorNorm_eq_l1 (a : WithLp 1 (Fin n → ℝ)) :
    ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (WithLp.ofLp a))‖ = ‖a‖ := by
  -- Specialize Proposition 1.9 to the endpoint pair `(∞, 1)`.
  letI : Fact (1 ≤ (⊤ : ENNReal)) := ⟨by simp⟩
  have hconj : ENNReal.conjExponent (⊤ : ENNReal) = 1 := by
    simp [ENNReal.conjExponent]
  have hnorm :
      ‖WithLp.toLp (ENNReal.conjExponent (⊤ : ENNReal)) (WithLp.ofLp a)‖ = ‖a‖ := by
    rw [hconj]
  simpa [dualNorm] using
    (dualNorm_lpPairingDual_eq_conjExponent_lp_norm
      (p := (⊤ : ENNReal)) (y := WithLp.ofLp a)).trans hnorm

/-- Helper for Proposition 5.9: every softmax coordinate lies in `[0, 1]`. -/
private theorem softmax_point_le_one [NeZero n] (x : E) (i : Fin n) :
    softmax_point x.ofLp i ≤ 1 := by
  -- Compare one nonnegative coordinate with the simplex sum of all coordinates.
  have hle_sum : softmax_point x.ofLp i ≤ ∑ j, softmax_point x.ofLp j := by
    simpa using
      (Finset.single_le_sum
        (fun j _ ↦ le_of_lt (softmax_point_pos x.ofLp j))
        (by simp : i ∈ (Finset.univ : Finset (Fin n))))
  simpa using hle_sum.trans_eq (sum_softmax_point x.ofLp)

/-- Helper for Proposition 5.9: two numbers in `[-1, 1]` satisfy
`|a - b| ≤ 1 - a * b`. -/
private theorem abs_sub_le_one_sub_mul {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a - b| ≤ 1 - a * b := by
  have hab : |a * b| ≤ 1 := by
    rw [abs_mul]
    simpa using (mul_le_mul ha hb (by positivity) (by positivity))
  have hnonneg : 0 ≤ 1 - a * b := by
    have hab' : a * b ≤ 1 := (le_abs_self (a * b)).trans hab
    linarith
  have ha2 : a ^ (2 : ℕ) ≤ 1 := by
    have hleft : 0 ≤ 1 - a := by
      have ha' : a ≤ 1 := (le_abs_self a).trans ha
      linarith
    have hright : 0 ≤ 1 + a := by
      have ha' : -1 ≤ a := by
        exact (abs_le.mp ha).1
      linarith
    have haux : 0 ≤ (1 - a) * (1 + a) := mul_nonneg hleft hright
    nlinarith
  have hb2 : b ^ (2 : ℕ) ≤ 1 := by
    have hleft : 0 ≤ 1 - b := by
      have hb' : b ≤ 1 := (le_abs_self b).trans hb
      linarith
    have hright : 0 ≤ 1 + b := by
      have hb' : -1 ≤ b := by
        exact (abs_le.mp hb).1
      linarith
    have haux : 0 ≤ (1 - b) * (1 + b) := mul_nonneg hleft hright
    nlinarith
  have hsq : (a - b) ^ (2 : ℕ) ≤ (1 - a * b) ^ (2 : ℕ) := by
    have hleft : 0 ≤ 1 - a ^ (2 : ℕ) := by
      linarith
    have hright : 0 ≤ 1 - b ^ (2 : ℕ) := by
      linarith
    have haux : 0 ≤ (1 - a ^ (2 : ℕ)) * (1 - b ^ (2 : ℕ)) := mul_nonneg hleft hright
    nlinarith
  have hsq' : |a - b| ≤ |1 - a * b| := by
    exact (sq_le_sq).1 (by simpa [sq_abs] using hsq)
  simpa [abs_of_nonneg hnonneg] using hsq'

/-- Helper for Proposition 5.9: the Fréchet derivative of the log-sum-exp scalar field on the
`ℓ∞` model is the canonical `ℓ∞/ℓ¹` pairing against the softmax vector. -/
private theorem logSumExpLinfty_hasFDerivAt [NeZero n] (x : E) :
    HasFDerivAt
      (fun z : E ↦ (log_sum_exp_function z.ofLp).toReal)
      (LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (softmax_point x.ofLp)))
      x := by
  let sumExp : E → ℝ := fun z ↦ ∑ i, Real.exp (z.ofLp i)
  have hsumExp_pos : 0 < sumExp x := by
    simpa [sumExp] using expSum_pos x.ofLp
  -- Differentiate the partition function coordinatewise, then apply the logarithmic chain rule.
  have hsumExp :
      HasFDerivAt sumExp
        (∑ i, Real.exp (x.ofLp i) •
          (PiLp.proj (⊤ : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)) x := by
    simpa [sumExp] using
      (HasFDerivAt.fun_sum
        (u := Finset.univ)
        (fun i _ ↦ (PiLp.hasFDerivAt_apply (⊤ : ENNReal) x i).exp))
  have hlog :
      HasFDerivAt (fun z : E ↦ Real.log (sumExp z))
        ((sumExp x)⁻¹ • ∑ i, Real.exp (x.ofLp i) •
          (PiLp.proj (⊤ : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)) x := by
    exact hsumExp.log hsumExp_pos.ne'
  have hfun :
      (fun z : E ↦ (log_sum_exp_function z.ofLp).toReal) = fun z : E ↦ Real.log (sumExp z) := by
    funext z
    simp [sumExp, log_sum_exp_function_apply]
  rw [hfun]
  have hderiv_eq :
      LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (softmax_point x.ofLp)) =
        ((sumExp x)⁻¹ • ∑ i, Real.exp (x.ofLp i) •
          (PiLp.proj (⊤ : ENNReal) (fun _ : Fin n ↦ ℝ) i : E →L[ℝ] ℝ)) := by
    ext v
    simp [sumExp, lpPairingDual_apply, softmax_point, dotProduct, Finset.mul_sum,
      mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  simpa [hderiv_eq] using hlog

/-- Helper for Proposition 5.9: the centered softmax weights have weighted `ℓ₁` mass at most `1`
against every `ℓ∞` unit vector. -/
private theorem softmaxWeightedDeviation_le_one [NeZero n]
    (x s : E) (hs : ‖s‖ ≤ 1) :
    ∑ i, softmax_point x.ofLp i *
        |WithLp.ofLp s i - dotProduct (WithLp.ofLp s) (softmax_point x.ofLp)| ≤ 1 := by
  have hα_abs :
      |dotProduct (WithLp.ofLp s) (softmax_point x.ofLp)| ≤ 1 := by
    calc
      |dotProduct (WithLp.ofLp s) (softmax_point x.ofLp)|
          ≤ ∑ i, |WithLp.ofLp s i * softmax_point x.ofLp i| := by
              simpa [dotProduct] using
                Finset.abs_sum_le_sum_abs (s := Finset.univ)
                  (f := fun i : Fin n ↦ WithLp.ofLp s i * softmax_point x.ofLp i)
      _ = ∑ i, |WithLp.ofLp s i| * softmax_point x.ofLp i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [abs_mul, abs_of_nonneg (le_of_lt (softmax_point_pos x.ofLp i))]
      _ ≤ ∑ i, 1 * softmax_point x.ofLp i := by
            refine Finset.sum_le_sum ?_
            intro i _
            exact mul_le_mul_of_nonneg_right
              ((PiLp.norm_apply_le s i).trans hs)
              (le_of_lt (softmax_point_pos x.ofLp i))
      _ = 1 := by
            simp
  let α : ℝ := dotProduct (WithLp.ofLp s) (softmax_point x.ofLp)
  calc
    ∑ i, softmax_point x.ofLp i * |WithLp.ofLp s i - α|
        ≤ ∑ i, softmax_point x.ofLp i * (1 - WithLp.ofLp s i * α) := by
              refine Finset.sum_le_sum ?_
              intro i _
              exact mul_le_mul_of_nonneg_left
                (abs_sub_le_one_sub_mul ((PiLp.norm_apply_le s i).trans hs) hα_abs)
                (le_of_lt (softmax_point_pos x.ofLp i))
    _ = 1 - α * α := by
          calc
            ∑ i, softmax_point x.ofLp i * (1 - WithLp.ofLp s i * α)
                = ∑ i,
                    (softmax_point x.ofLp i -
                      softmax_point x.ofLp i * (WithLp.ofLp s i * α)) := by
                        refine Finset.sum_congr rfl ?_
                        intro i _
                        ring
            _ = ∑ i, softmax_point x.ofLp i -
                  ∑ i, softmax_point x.ofLp i * (WithLp.ofLp s i * α) := by
                    rw [Finset.sum_sub_distrib]
            _ = 1 - ∑ i, softmax_point x.ofLp i * (WithLp.ofLp s i * α) := by
                  simp
            _ = 1 - α * dotProduct (WithLp.ofLp s) (softmax_point x.ofLp) := by
                  have hsum :
                      ∑ i, softmax_point x.ofLp i * (WithLp.ofLp s i * α) =
                        α * dotProduct (WithLp.ofLp s) (softmax_point x.ofLp) := by
                    calc
                      ∑ i, softmax_point x.ofLp i * (WithLp.ofLp s i * α)
                          = ∑ i, α * (softmax_point x.ofLp i * WithLp.ofLp s i) := by
                              refine Finset.sum_congr rfl ?_
                              intro i _
                              ring
                      _ = α * ∑ i, softmax_point x.ofLp i * WithLp.ofLp s i := by
                            rw [Finset.mul_sum]
                      _ = α * dotProduct (WithLp.ofLp s) (softmax_point x.ofLp) := by
                            simp [dotProduct, mul_comm]
                  rw [hsum]
            _ = 1 - α * α := by
                  simp [α]
    _ ≤ 1 := by
          nlinarith

/-- Helper for Proposition 5.9: pairing the softmax difference with an `ℓ∞` unit vector is
controlled by the `ℓ∞` distance of the base points. -/
private theorem softmaxDifference_pairing_bound [NeZero n]
    (x y s : E) (hs : ‖s‖ ≤ 1) :
    |dotProduct (WithLp.ofLp s) (fun i ↦ softmax_point y.ofLp i - softmax_point x.ofLp i)| ≤
      ‖y - x‖ := by
  let z : ℝ → E := AffineMap.lineMap x y
  let numerator : ℝ → ℝ := fun t ↦ ∑ i, WithLp.ofLp s i * Real.exp ((z t).ofLp i)
  let denominator : ℝ → ℝ := fun t ↦ ∑ i, Real.exp ((z t).ofLp i)
  let φ : ℝ → ℝ := fun t ↦ dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)
  have hden_pos : ∀ t : ℝ, 0 < denominator t := by
    intro t
    simpa [denominator] using expSum_pos ((z t).ofLp)
  have hφ_deriv :
      ∀ t : ℝ,
        HasDerivAt φ
          (dotProduct (WithLp.ofLp (y - x))
            (fun i ↦ softmax_point (z t).ofLp i *
              (WithLp.ofLp s i -
                dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)))) t := by
    intro t
    have hz' : HasDerivAt z (y - x) t := by
      simpa [z] using (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
    have hcoord :
        ∀ i : Fin n, HasDerivAt (fun u : ℝ ↦ (z u).ofLp i) ((y - x).ofLp i) t := by
      intro i
      simpa using
        HasFDerivAt.comp_hasDerivAt t
          (PiLp.hasFDerivAt_apply (⊤ : ENNReal) (z t) i) hz'
    have hnum :
        HasDerivAt numerator
          (∑ i, WithLp.ofLp s i * Real.exp ((z t).ofLp i) * (y - x).ofLp i) t := by
      convert
        (HasDerivAt.sum (u := Finset.univ)
          (fun i _ ↦ ((hcoord i).exp.const_mul (WithLp.ofLp s i)))) using 1
      · ext u
        simp [numerator]
      · ring
    have hden :
        HasDerivAt denominator
          (∑ i, Real.exp ((z t).ofLp i) * (y - x).ofLp i) t := by
      convert (HasDerivAt.sum (u := Finset.univ) fun i _ ↦ (hcoord i).exp) using 1
      · ext u
        simp [denominator]
    have hquot :
        HasDerivAt (fun u : ℝ ↦ numerator u / denominator u)
          (((∑ i, WithLp.ofLp s i * Real.exp ((z t).ofLp i) * (y - x).ofLp i) * denominator t -
              numerator t * ∑ i, Real.exp ((z t).ofLp i) * (y - x).ofLp i) /
            denominator t ^ (2 : ℕ)) t := by
      exact hnum.div hden (hden_pos t).ne'
    have hfun :
        φ = fun u : ℝ ↦ numerator u / denominator u := by
      funext u
      simp [φ, numerator, denominator, z, softmax_point, dotProduct, Finset.mul_sum,
        div_eq_mul_inv, mul_comm, mul_assoc]
    rw [hfun]
    convert hquot using 1
    · rw [dotProduct]
      set D : ℝ := denominator t with hD
      set A : ℝ := numerator t with hA
      set B : ℝ := ∑ i, WithLp.ofLp s i * Real.exp ((z t).ofLp i) * (y - x).ofLp i with hB
      set C : ℝ := ∑ i, Real.exp ((z t).ofLp i) * (y - x).ofLp i with hC
      have hD0 : D ≠ 0 := by
        rw [hD]
        exact (hden_pos t).ne'
      have havg :
          dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp) = A * D⁻¹ := by
        rw [hA, hD]
        simp [numerator, denominator, z, softmax_point, dotProduct, div_eq_mul_inv,
          Finset.mul_sum, mul_assoc, mul_comm]
      have hB' :
          ∑ i,
              (y.ofLp i * s.ofLp i * Real.exp ((z t).ofLp i) -
                x.ofLp i * s.ofLp i * Real.exp ((z t).ofLp i)) = B := by
        rw [hB]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [show (y - x).ofLp i = y.ofLp i - x.ofLp i by rfl]
        ring
      have hC' :
          ∑ i,
              (y.ofLp i * Real.exp ((z t).ofLp i) -
                x.ofLp i * Real.exp ((z t).ofLp i)) = C := by
        rw [hC]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [show (y - x).ofLp i = y.ofLp i - x.ofLp i by rfl]
        ring
      calc
        ∑ i,
            (y.ofLp i - x.ofLp i) *
              (softmax_point (z t).ofLp i *
                (s.ofLp i - dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)))
            = ∑ i,
                (y.ofLp i - x.ofLp i) *
                  ((Real.exp ((z t).ofLp i) * D⁻¹) * (s.ofLp i - A * D⁻¹)) := by
                    rw [havg]
                    refine Finset.sum_congr rfl ?_
                    intro i _
                    rw [softmax_point, hD]
                    simp [denominator, div_eq_mul_inv, mul_assoc, mul_comm]
        _ = ∑ i,
              ((y.ofLp i * s.ofLp i * Real.exp ((z t).ofLp i) -
                  x.ofLp i * s.ofLp i * Real.exp ((z t).ofLp i)) * D⁻¹ -
                (y.ofLp i * Real.exp ((z t).ofLp i) -
                  x.ofLp i * Real.exp ((z t).ofLp i)) * (A * D⁻¹ * D⁻¹)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              ring
        _ =
            (∑ i,
                (y.ofLp i * s.ofLp i * Real.exp ((z t).ofLp i) -
                  x.ofLp i * s.ofLp i * Real.exp ((z t).ofLp i))) * D⁻¹ -
              (∑ i,
                  (y.ofLp i * Real.exp ((z t).ofLp i) -
                    x.ofLp i * Real.exp ((z t).ofLp i))) * (A * D⁻¹ * D⁻¹) := by
                rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        _ = B * D⁻¹ - C * (A * D⁻¹ * D⁻¹) := by rw [hB', hC']
        _ = (B * D - A * C) / D ^ (2 : ℕ) := by
              field_simp [hD0]
  have hdiff :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ
        (dotProduct (WithLp.ofLp (y - x))
          (fun i ↦ softmax_point (z t).ofLp i *
            (WithLp.ofLp s i -
              dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)))) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    exact (hφ_deriv t).hasDerivWithinAt
  have hbound :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        ‖dotProduct (WithLp.ofLp (y - x))
          (fun i ↦ softmax_point (z t).ofLp i *
            (WithLp.ofLp s i -
              dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)))‖ ≤ ‖y - x‖ := by
    intro t ht
    calc
      ‖dotProduct (WithLp.ofLp (y - x))
          (fun i ↦ softmax_point (z t).ofLp i *
            (WithLp.ofLp s i -
              dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)))‖
          = |dotProduct (WithLp.ofLp (y - x))
              (fun i ↦ softmax_point (z t).ofLp i *
                (WithLp.ofLp s i -
                  dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)))| := by
                rw [Real.norm_eq_abs]
      _ ≤ ∑ i,
            |WithLp.ofLp (y - x) i *
              (softmax_point (z t).ofLp i *
                (WithLp.ofLp s i -
                  dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)))| := by
                  simpa [dotProduct] using
                    Finset.abs_sum_le_sum_abs (s := Finset.univ)
                      (f := fun i : Fin n ↦
                        WithLp.ofLp (y - x) i *
                          (softmax_point (z t).ofLp i *
                            (WithLp.ofLp s i -
                              dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp))))
      _ = ∑ i,
            |WithLp.ofLp (y - x) i| *
              (softmax_point (z t).ofLp i *
                |WithLp.ofLp s i -
                  dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)|) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  rw [abs_mul, abs_mul,
                    abs_of_nonneg (le_of_lt (softmax_point_pos ((z t).ofLp) i))]
      _ ≤ ∑ i,
            ‖y - x‖ *
              (softmax_point (z t).ofLp i *
                |WithLp.ofLp s i -
                  dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)|) := by
                  refine Finset.sum_le_sum ?_
                  intro i _
                  exact mul_le_mul_of_nonneg_right
                    (PiLp.norm_apply_le (y - x) i)
                    (mul_nonneg (le_of_lt (softmax_point_pos ((z t).ofLp) i)) (abs_nonneg _))
      _ = ‖y - x‖ *
            ∑ i, softmax_point (z t).ofLp i *
              |WithLp.ofLp s i -
                dotProduct (WithLp.ofLp s) (softmax_point (z t).ofLp)| := by
                  rw [Finset.mul_sum]
      _ ≤ ‖y - x‖ * 1 := by
            gcongr
            exact softmaxWeightedDeviation_le_one (x := z t) (s := s) hs
      _ = ‖y - x‖ := by ring
  have hMv :=
    norm_image_sub_le_of_norm_deriv_le_segment_01' hdiff hbound
  have hrewrite :
      φ 1 - φ 0 =
        dotProduct (WithLp.ofLp s) (fun i ↦ softmax_point y.ofLp i - softmax_point x.ofLp i) := by
    rw [show φ 1 = dotProduct (WithLp.ofLp s) (softmax_point y.ofLp) by
      simp [φ, z, AffineMap.lineMap_apply_one]]
    rw [show φ 0 = dotProduct (WithLp.ofLp s) (softmax_point x.ofLp) by
      simp [φ, z, AffineMap.lineMap_apply_zero]]
    rw [dotProduct, dotProduct, dotProduct]
    calc
      ∑ i, s.ofLp i * softmax_point y.ofLp i - ∑ i, s.ofLp i * softmax_point x.ofLp i
          = ∑ i, (s.ofLp i * softmax_point y.ofLp i - s.ofLp i * softmax_point x.ofLp i) := by
              rw [← Finset.sum_sub_distrib]
      _ = ∑ i, s.ofLp i * (softmax_point y.ofLp i - softmax_point x.ofLp i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
  rw [Real.norm_eq_abs] at hMv
  simpa [hrewrite] using hMv

/- Proposition 5.9 is `source-facing`: the textbook object is the concrete log-sum-exp function on
`ℝ^n`, now viewed on the canonical `l_∞` normed model `WithLp ⊤ (Fin n → ℝ)`.
Domain sampling: the Chapter 5 owner predicate is `is_l_smooth_on`, while the existing Chapter 4
owner declaration for the function itself is `log_sum_exp_function`. This file therefore keeps the
source-facing smoothness statement as a `bridge/view`, reusing that earlier owner through the
canonical coordinate-forgetting map `WithLp.ofLp` and `EReal.toReal` instead of introducing a
parallel local copy of log-sum-exp. -/

recall log_sum_exp_function

-- Proof sketch: compute the Hessian of `fun x : E ↦ (log_sum_exp_function x.ofLp).toReal` as
-- `diag(w) - w wᵀ`, where `w_i = exp (x_i) / ∑ j, exp (x_j)`. For every direction `d`, the
-- associated quadratic form is bounded above by `‖d‖_∞^2`. Then apply the second-order
-- characterization of smoothness to deduce that the Fréchet derivative is globally
-- `1`-Lipschitz.
/-- Proposition 5.9: the log-sum-exp function
`x ↦ log (e^{x_1} + e^{x_2} + ⋯ + e^{x_n})` is globally `1`-smooth with respect to the
`l_∞` norm on `ℝ^n`, modeled as `WithLp ⊤ (Fin n → ℝ)`. -/
theorem log_sum_exp_linfty_function_is_one_smooth (n : ℕ) :
    is_l_smooth_on
      (fun x : WithLp (⊤ : ENNReal) (Fin n → ℝ) ↦ (log_sum_exp_function x.ofLp).toReal)
      Set.univ
      1 := by
  by_cases hzero : n = 0
  · -- In dimension zero the domain is a singleton, so the function and its derivative are constant.
    subst n
    have hconst :
        (fun x : WithLp (⊤ : ENNReal) (Fin 0 → ℝ) ↦ (log_sum_exp_function x.ofLp).toReal) =
          fun _ : WithLp (⊤ : ENNReal) (Fin 0 → ℝ) ↦ 0 := by
      ext x
      simp [log_sum_exp_function_apply]
    rw [is_l_smooth_on_iff, hconst]
    constructor
    · intro x hx
      exact differentiableAt_const (𝕜 := ℝ) (x := x) (c := (0 : ℝ))
    · intro x hx y hy
      simp
  · haveI : NeZero n := ⟨hzero⟩
    rw [is_l_smooth_on_iff]
    constructor
    · intro x hx
      exact (logSumExpLinfty_hasFDerivAt x).differentiableAt
    · intro x hx y hy
      rw [(logSumExpLinfty_hasFDerivAt x).fderiv, (logSumExpLinfty_hasFDerivAt y).fderiv]
      have hpairing_sub :
          lpPairingDual (⊤ : ENNReal) (softmax_point x.ofLp) -
              lpPairingDual (⊤ : ENNReal) (softmax_point y.ofLp) =
            lpPairingDual (⊤ : ENNReal)
              (fun i ↦ softmax_point x.ofLp i - softmax_point y.ofLp i) := by
        ext s
        simp [lpPairingDual_apply, dotProduct, Finset.sum_sub_distrib, mul_sub]
      have hclm_sub :
          LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (softmax_point x.ofLp)) -
              LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (softmax_point y.ofLp)) =
            LinearMap.toContinuousLinearMap
              (lpPairingDual (⊤ : ENNReal)
                (fun i ↦ softmax_point x.ofLp i - softmax_point y.ofLp i)) :=
        congrArg LinearMap.toContinuousLinearMap hpairing_sub
      rw [hclm_sub]
      refine ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg zero_le_one (norm_nonneg (x - y))) ?_
      intro s
      by_cases hs0 : s = 0
      · simp [hs0]
      · have hs_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
        have hs_unit : ‖‖s‖⁻¹ • s‖ ≤ 1 := by
          have hnorm : ‖‖s‖⁻¹ • s‖ = 1 := by
            calc
              ‖‖s‖⁻¹ • s‖ = ‖s‖⁻¹ * ‖s‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
              _ = 1 := by
                field_simp [hs_pos.ne']
          rw [hnorm]
        have hbound :=
          softmaxDifference_pairing_bound y x (‖s‖⁻¹ • s) hs_unit
        have hs_repr : ‖s‖ • (‖s‖⁻¹ • s) = s := by
          simp [smul_smul, mul_inv_cancel₀ hs_pos.ne']
        calc
          ‖LinearMap.toContinuousLinearMap
              (lpPairingDual (⊤ : ENNReal)
                (fun i ↦ softmax_point x.ofLp i - softmax_point y.ofLp i)) s‖ =
              ‖LinearMap.toContinuousLinearMap
                  (lpPairingDual (⊤ : ENNReal)
                    (fun i ↦ softmax_point x.ofLp i - softmax_point y.ofLp i))
                  (‖s‖ • (‖s‖⁻¹ • s))‖ := by
              rw [hs_repr]
          _ = ‖‖s‖ •
                LinearMap.toContinuousLinearMap
                  (lpPairingDual (⊤ : ENNReal)
                    (fun i ↦ softmax_point x.ofLp i - softmax_point y.ofLp i))
                  (‖s‖⁻¹ • s)‖ := by
                rw [map_smul]
          _ = ‖s‖ *
                ‖LinearMap.toContinuousLinearMap
                    (lpPairingDual (⊤ : ENNReal)
                      (fun i ↦ softmax_point x.ofLp i - softmax_point y.ofLp i))
                    (‖s‖⁻¹ • s)‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          _ ≤ ‖s‖ * ‖x - y‖ := by
                gcongr
                simpa [lpPairingDual_apply, Real.norm_eq_abs] using hbound
          _ ≤ (1 : ℝ) * ‖x - y‖ * ‖s‖ := by
                nlinarith [norm_nonneg s, norm_nonneg (x - y)]

end
