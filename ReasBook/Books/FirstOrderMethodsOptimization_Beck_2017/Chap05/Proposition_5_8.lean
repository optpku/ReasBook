/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_17
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 5.8 is `source-facing`: it records the Chapter 5 smoothness statement for the
concrete log-sum-exp function on Euclidean `ℝ^n`. The smoothness owner is already
`is_l_smooth_on` from Definition 5.1, while the function owner is already Chapter 4's
`log_sum_exp_function : (Fin n → ℝ) → EReal`. This file therefore keeps only the Euclidean
smoothness statement as a `bridge/view` to that earlier owner. -/

recall log_sum_exp_function

/-- Helper for Proposition 5.8: the softmax point, viewed back in Euclidean `ℝ^n`. -/
private abbrev softmaxVec (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (softmax_point x.ofLp)

/-- Helper for Proposition 5.8: every softmax coordinate lies in `[0, 1]`. -/
private theorem softmax_point_le_one [NeZero n] (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    softmax_point x.ofLp i ≤ 1 := by
  -- Compare a single nonnegative softmax coordinate with the full simplex sum.
  have hle_sum : softmax_point x.ofLp i ≤ ∑ j, softmax_point x.ofLp j := by
    simpa using
      (Finset.single_le_sum
        (fun j _ ↦ le_of_lt (softmax_point_pos x.ofLp j))
        (by simp : i ∈ (Finset.univ : Finset (Fin n))))
  simpa using hle_sum.trans_eq (sum_softmax_point x.ofLp)

/-- Helper for Proposition 5.8: on `[0, 1]`, the logarithm gap dominates the coordinate gap. -/
private theorem sq_le_sub_mul_log_sub
    {a b : ℝ} (ha_pos : 0 < a) (hb_pos : 0 < b) (ha_le_one : a ≤ 1) (hb_le_one : b ≤ 1) :
    (a - b) ^ 2 ≤ (a - b) * (Real.log a - Real.log b) := by
  by_cases hba : b ≤ a
  · -- On `(0, 1]`, `t ↦ log t - t` is increasing, so the log gap dominates the coordinate gap.
    have hratio_ge : 1 ≤ a / b := by
      rwa [one_le_div hb_pos]
    have hratio_nonneg : 0 ≤ Real.log (a / b) := Real.log_nonneg hratio_ge
    have hscaled :
        a * (1 - (a / b)⁻¹) ≤ a * Real.log (a / b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.one_sub_inv_le_log_of_pos (div_pos ha_pos hb_pos))
        ha_pos.le
    have hgap_le_log : a - b ≤ Real.log (a / b) := by
      have hscaled' : a * Real.log (a / b) ≤ Real.log (a / b) := by
        nlinarith
      have hleft : a * (1 - (a / b)⁻¹) = a - b := by
        field_simp [ha_pos.ne', hb_pos.ne']
      linarith
    have hgap_le : a - b ≤ Real.log a - Real.log b := by
      simpa [Real.log_div ha_pos.ne' hb_pos.ne'] using hgap_le_log
    have hgap_nonneg : 0 ≤ a - b := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hgap_le hgap_nonneg
    simpa [pow_two] using hmul
  · -- The opposite order is symmetric.
    have hab : a ≤ b := le_of_not_ge hba
    have hratio_ge : 1 ≤ b / a := by
      rwa [one_le_div ha_pos]
    have hratio_nonneg : 0 ≤ Real.log (b / a) := Real.log_nonneg hratio_ge
    have hscaled :
        b * (1 - (b / a)⁻¹) ≤ b * Real.log (b / a) := by
      exact mul_le_mul_of_nonneg_left
        (Real.one_sub_inv_le_log_of_pos (div_pos hb_pos ha_pos))
        hb_pos.le
    have hgap_le_log : b - a ≤ Real.log (b / a) := by
      have hscaled' : b * Real.log (b / a) ≤ Real.log (b / a) := by
        nlinarith
      have hleft : b * (1 - (b / a)⁻¹) = b - a := by
        field_simp [ha_pos.ne', hb_pos.ne']
      linarith
    have hlog_le_gap : Real.log a - Real.log b ≤ a - b := by
      have hgap_le' : b - a ≤ Real.log b - Real.log a := by
        simpa [Real.log_div hb_pos.ne' ha_pos.ne'] using hgap_le_log
      linarith
    have hgap_nonpos : a - b ≤ 0 := by
      linarith
    have hmul := mul_le_mul_of_nonpos_left hlog_le_gap hgap_nonpos
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Helper for Proposition 5.8: the Euclidean inner product is the coordinate sum
`∑ i, u_i * v_i`. -/
private theorem realInner_eq_sum_mul_ofLp
    (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u v = ∑ i, u.ofLp i * v.ofLp i := by
  -- Rewrite the Euclidean inner product through the `PiLp` coordinate model.
  simpa [dotProduct, mul_comm] using
    (EuclideanSpace.inner_eq_star_dotProduct (x := u) (y := v))

/-- Helper for Proposition 5.8: applying the Euclidean dual of `softmaxVec x` is the softmax
coordinate pairing. -/
private theorem softmaxVec_toDual_apply
    (x v : EuclideanSpace ℝ (Fin n)) :
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (softmaxVec x)) v =
      ∑ i, softmax_point x.ofLp i * v.ofLp i := by
  -- Identify the dual application with the Euclidean inner product, then expand coordinates.
  rw [InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  rw [InnerProductSpace.toDualMap_apply_apply]
  simpa [softmaxVec, mul_comm] using realInner_eq_sum_mul_ofLp (u := softmaxVec x) (v := v)

/-- Helper for Proposition 5.8: the softmax logarithmic monotonicity sum is exactly the Euclidean
pairing `⟪softmaxVec x - softmaxVec y, x - y⟫_ℝ`. -/
private theorem softmaxLogPairing_eq_realInner
    (hn : 0 < n) (x y : EuclideanSpace ℝ (Fin n)) :
    ∑ i,
      (softmax_point x.ofLp i - softmax_point y.ofLp i) *
        (Real.log (softmax_point x.ofLp i) - Real.log (softmax_point y.ofLp i)) =
      inner ℝ (softmaxVec x - softmaxVec y) (x - y) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let sx : ℝ := ∑ j : Fin n, Real.exp (x.ofLp j)
  let sy : ℝ := ∑ j : Fin n, Real.exp (y.ofLp j)
  have hsum_diff :
      ∑ i, (softmax_point x.ofLp i - softmax_point y.ofLp i) = 0 := by
    rw [Finset.sum_sub_distrib, sum_softmax_point, sum_softmax_point, sub_self]
  have hsum_eq :
      ∑ i,
        (softmax_point x.ofLp i - softmax_point y.ofLp i) *
          (Real.log (softmax_point x.ofLp i) - Real.log (softmax_point y.ofLp i)) =
        ∑ i,
          (softmax_point x.ofLp i - softmax_point y.ofLp i) * (x.ofLp i - y.ofLp i) := by
    -- Expand the softmax logarithms and cancel the common normalization constants.
    calc
      ∑ i,
          (softmax_point x.ofLp i - softmax_point y.ofLp i) *
            (Real.log (softmax_point x.ofLp i) - Real.log (softmax_point y.ofLp i))
          =
          ∑ i,
            (softmax_point x.ofLp i - softmax_point y.ofLp i) *
              ((x.ofLp i - y.ofLp i) - (Real.log sx - Real.log sy)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            have harg :
                (x.ofLp i - Real.log (∑ j : Fin n, Real.exp (x.ofLp j))) -
                    (y.ofLp i - Real.log (∑ j : Fin n, Real.exp (y.ofLp j))) =
                  (x.ofLp i - y.ofLp i) -
                    (Real.log (∑ j : Fin n, Real.exp (x.ofLp j)) -
                      Real.log (∑ j : Fin n, Real.exp (y.ofLp j))) := by
              ring
            rw [softmax_point_log (y := x.ofLp) i, softmax_point_log (y := y.ofLp) i]
            simpa using
              congrArg
                (fun t ↦
                  (softmax_point x.ofLp i - softmax_point y.ofLp i) * t)
                harg
      _ =
          ∑ i,
            ((softmax_point x.ofLp i - softmax_point y.ofLp i) * (x.ofLp i - y.ofLp i) -
              (softmax_point x.ofLp i - softmax_point y.ofLp i) * (Real.log sx - Real.log sy)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
      _ =
          (∑ i, (softmax_point x.ofLp i - softmax_point y.ofLp i) * (x.ofLp i - y.ofLp i)) -
            ∑ i,
              (softmax_point x.ofLp i - softmax_point y.ofLp i) * (Real.log sx - Real.log sy) := by
            rw [Finset.sum_sub_distrib]
      _ =
          (∑ i, (softmax_point x.ofLp i - softmax_point y.ofLp i) * (x.ofLp i - y.ofLp i)) -
            (Real.log sx - Real.log sy) *
              ∑ i, (softmax_point x.ofLp i - softmax_point y.ofLp i) := by
            congr 1
            calc
              ∑ i,
                  (softmax_point x.ofLp i - softmax_point y.ofLp i) *
                    (Real.log sx - Real.log sy)
                  =
                  (∑ i, (softmax_point x.ofLp i - softmax_point y.ofLp i)) *
                    (Real.log sx - Real.log sy) := by
                      rw [Finset.sum_mul]
              _ =
                  (Real.log sx - Real.log sy) *
                    ∑ i, (softmax_point x.ofLp i - softmax_point y.ofLp i) := by
                      ring
      _ = ∑ i, (softmax_point x.ofLp i - softmax_point y.ofLp i) * (x.ofLp i - y.ofLp i) := by
            rw [hsum_diff]
            ring
  calc
    ∑ i,
        (softmax_point x.ofLp i - softmax_point y.ofLp i) *
          (Real.log (softmax_point x.ofLp i) - Real.log (softmax_point y.ofLp i))
      =
        ∑ i, (softmax_point x.ofLp i - softmax_point y.ofLp i) * (x.ofLp i - y.ofLp i) :=
      hsum_eq
    _ = inner ℝ (softmaxVec x - softmaxVec y) (x - y) := by
      simpa [softmaxVec] using
        (realInner_eq_sum_mul_ofLp (u := softmaxVec x - softmaxVec y) (v := x - y)).symm

/-- Helper for Proposition 5.8: the real log-sum-exp function has gradient `softmax_point`. -/
private theorem hasGradientAt_logSumExpToReal (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt
      (fun y : EuclideanSpace ℝ (Fin n) ↦ (log_sum_exp_function y.ofLp).toReal)
      (softmaxVec x) x := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let sumExp : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦ ∑ i, Real.exp (y.ofLp i)
  have hsumExp_pos : 0 < sumExp x := by
    -- Use one coordinate of the finite exponential sum to witness positivity.
    let i0 : Fin n := ⟨0, hn⟩
    refine lt_of_lt_of_le (Real.exp_pos (x.ofLp i0)) ?_
    simpa [sumExp] using
      (Finset.single_le_sum
        (fun j _ ↦ le_of_lt (Real.exp_pos (x.ofLp j)))
        (by simp : i0 ∈ (Finset.univ : Finset (Fin n))))
  -- Route correction: first normalize the Euclidean dual pairing, then the derivative
  -- identification is a single `ext` argument rather than repeated coercion rewrites.
  rw [hasGradientAt_iff_hasFDerivAt]
  have hsumExp :
      HasFDerivAt sumExp
        (∑ i,
          Real.exp (x.ofLp i) •
            (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) i :
              EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        x := by
    -- Differentiate the partition function coordinatewise.
    simpa [sumExp] using
      (HasFDerivAt.fun_sum
        (u := Finset.univ)
        (fun i _ ↦ (PiLp.hasFDerivAt_apply 2 x i).exp))
  have hlog :
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) ↦ Real.log (sumExp y))
        ((sumExp x)⁻¹ •
          ∑ i,
            Real.exp (x.ofLp i) •
              (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) i :
                EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        x := by
    exact hsumExp.log hsumExp_pos.ne'
  have hfun :
      (fun y : EuclideanSpace ℝ (Fin n) ↦ (log_sum_exp_function y.ofLp).toReal) =
        fun y : EuclideanSpace ℝ (Fin n) ↦ Real.log (sumExp y) := by
    funext y
    simp [sumExp, log_sum_exp_function_apply]
  rw [hfun]
  have hderiv_eq :
      InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (softmaxVec x) =
        ((sumExp x)⁻¹ •
          ∑ i,
            Real.exp (x.ofLp i) •
              (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) i :
                EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) := by
    -- Compare the two candidate derivatives by evaluating them on an arbitrary direction.
    ext v
    rw [softmaxVec_toDual_apply]
    simp [sumExp, softmax_point, Finset.mul_sum, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc]
  simpa [hderiv_eq] using hlog

/-- Helper for Proposition 5.8: the softmax map is `1`-Lipschitz in the Euclidean norm. -/
private theorem norm_softmax_point_sub_le
    (hn : 0 < n) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖softmaxVec x - softmaxVec y‖ ≤ ‖x - y‖ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Δs : EuclideanSpace ℝ (Fin n) := softmaxVec x - softmaxVec y
  let Δx : EuclideanSpace ℝ (Fin n) := x - y
  have hsq_coord :
      ∑ i, (softmax_point x.ofLp i - softmax_point y.ofLp i) ^ 2 ≤
        ∑ i,
          (softmax_point x.ofLp i - softmax_point y.ofLp i) *
            (Real.log (softmax_point x.ofLp i) - Real.log (softmax_point y.ofLp i)) := by
    -- Sum the one-dimensional logarithmic monotonicity inequality over coordinates.
    refine Finset.sum_le_sum ?_
    intro i _
    exact sq_le_sub_mul_log_sub
      (softmax_point_pos x.ofLp i)
      (softmax_point_pos y.ofLp i)
      (softmax_point_le_one x i)
      (softmax_point_le_one y i)
  have hsq_inner :
      ‖Δs‖ ^ 2 ≤ inner ℝ Δs Δx := by
    -- Rewrite the summed coordinate inequality as a Euclidean norm-square estimate.
    calc
      ‖Δs‖ ^ 2 = inner ℝ Δs Δs := by
        simpa [Δs] using (real_inner_self_eq_norm_sq Δs).symm
      _ = ∑ i, (softmax_point x.ofLp i - softmax_point y.ofLp i) ^ 2 := by
        rw [realInner_eq_sum_mul_ofLp]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [Δs, softmaxVec, pow_two]
      _ ≤
          ∑ i,
            (softmax_point x.ofLp i - softmax_point y.ofLp i) *
              (Real.log (softmax_point x.ofLp i) - Real.log (softmax_point y.ofLp i)) :=
        hsq_coord
      _ = inner ℝ Δs Δx := by
        simpa [Δs, Δx] using softmaxLogPairing_eq_realInner hn x y
  have hmul :
      ‖Δs‖ ^ 2 ≤ ‖Δs‖ * ‖Δx‖ := by
    exact le_trans hsq_inner (real_inner_le_norm Δs Δx)
  by_cases hzero : ‖Δs‖ = 0
  · -- If the softmax gap vanishes, the desired Lipschitz bound is immediate.
    simp [Δs, hzero]
  · -- Otherwise divide the norm-square inequality by the positive factor `‖Δs‖`.
    have hzero' : 0 ≠ ‖Δs‖ := by
      simpa [eq_comm] using hzero
    have hpos : 0 < ‖Δs‖ := lt_of_le_of_ne (norm_nonneg Δs) hzero'
    have hnonneg : 0 ≤ ‖Δx‖ := norm_nonneg Δx
    nlinarith [hmul]

/-- Proposition 5.8: the log-sum-exp function
`x ↦ log (e^{x_1} + e^{x_2} + ⋯ + e^{x_n})` on Euclidean `ℝ^n` is globally `1`-smooth with
respect to the `l_2` norm. -/
theorem log_sum_exp_l2_function_is_one_smooth (n : ℕ) :
    is_l_smooth_on
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (log_sum_exp_function x).toReal)
      Set.univ 1 := by
  -- Route correction: use the direct gradient-difference characterization once the Euclidean
  -- softmax transport lemmas are available, rather than packaging a separate Lipschitz object.
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  by_cases h0 : n = 0
  · subst n
    have hconst :
        (fun x : EuclideanSpace ℝ (Fin 0) ↦ (log_sum_exp_function x).toReal) =
          fun _ : EuclideanSpace ℝ (Fin 0) ↦ 0 := by
      funext x
      simp [log_sum_exp_function_apply]
    rw [hconst]
    constructor
    · intro x _
      simpa using
        (differentiableAt_const (c := (0 : ℝ)) :
          DifferentiableAt ℝ (fun _ : EuclideanSpace ℝ (Fin 0) ↦ 0) x)
    · intro x _ y _
      simp
  · have hn : 0 < n := Nat.pos_of_ne_zero h0
    constructor
    · intro x _
      simpa using (hasGradientAt_logSumExpToReal hn x).differentiableAt
    · intro x _ y _
      have hx :
          ∇ (fun z : EuclideanSpace ℝ (Fin n) ↦ (log_sum_exp_function z).toReal) x =
            softmaxVec x := by
        simpa using (hasGradientAt_logSumExpToReal hn x).gradient
      have hy :
          ∇ (fun z : EuclideanSpace ℝ (Fin n) ↦ (log_sum_exp_function z).toReal) y =
            softmaxVec y := by
        simpa using (hasGradientAt_logSumExpToReal hn y).gradient
      rw [hx, hy]
      simpa using norm_softmax_point_sub_le hn x y
