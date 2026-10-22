/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set intervalIntegral

/-- Helper for Lemma 26.9: derivative of the exponential kernel `x ↦ exp (C * (t - x))`. -/
lemma hasDerivAt_expKernel (C t x : ℝ) :
    HasDerivAt (fun y ↦ Real.exp (C * (t - y))) (-C * Real.exp (C * (t - x))) x := by
  -- Differentiate the affine exponent and compose with `Real.exp`.
  simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm] using
    (Real.hasDerivAt_exp (C * (t - x))).comp x (((hasDerivAt_id x).const_sub t).const_mul C)

/-- Helper for Lemma 26.9: derivative of the weight `x ↦ exp (-C * x)`. -/
lemma deriv_expNegMul (C x : ℝ) :
    deriv (fun y ↦ Real.exp (-C * y)) x = -C * Real.exp (-C * x) := by
  simpa using (hasDerivAt_expKernel C 0 x).deriv

/-- Helper for Lemma 26.9: the weight `x ↦ exp (-C * x)` is absolutely continuous on `0..t`. -/
lemma expNegMul_absolutelyContinuousOnInterval {t C : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C) :
    AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (-C * x)) 0 t := by
  -- A uniform derivative bound on `[0,t]` makes the weight Lipschitz, hence absolutely continuous.
  have hlip :
      LipschitzOnWith ⟨C, hC⟩ (fun x ↦ Real.exp (C * (0 - x))) (Icc 0 t) := by
    refine (convex_Icc 0 t).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ ↦ (hasDerivAt_expKernel C 0 x).differentiableAt) ?_
    intro x hx
    have hexp_le_one : Real.exp (-C * x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hC, hx.1]
    have hnorm : ‖deriv (fun y ↦ Real.exp (-C * y)) x‖ ≤ C := by
      rw [deriv_expNegMul, Real.norm_eq_abs, abs_mul, abs_of_nonpos, abs_of_nonneg]
      · nlinarith
      · positivity
      · linarith
    simpa [zero_sub] using hnorm
  have hlip_uIcc :
      LipschitzOnWith ⟨C, hC⟩ (fun x ↦ Real.exp (C * (0 - x))) (uIcc 0 t) := by
    simpa [uIcc_of_le ht] using hlip
  simpa [zero_sub] using hlip_uIcc.absolutelyContinuousOnInterval

/-- Helper for Lemma 26.9: integrating the weighted primitive of `f` by parts isolates the
Gronwall primitive term. -/
lemma weightedPrimitiveIntegrationByParts {f : ℝ → ℝ} {t C : ℝ}
    (ht : 0 ≤ t) (hC : 0 ≤ C) (hf : IntervalIntegrable f volume 0 t) :
    let F := fun u ↦ ∫ s in 0..u, f s
    ∫ x in 0..t, Real.exp (-C * x) * f x
      = Real.exp (-C * t) * F t + C * ∫ x in 0..t, Real.exp (-C * x) * F x := by
  let F := fun u ↦ ∫ s in 0..u, f s
  let w := fun x ↦ Real.exp (-C * x)
  have hF_ac : AbsolutelyContinuousOnInterval F 0 t :=
    hf.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp [ht])
  have hw_ac : AbsolutelyContinuousOnInterval w 0 t :=
    expNegMul_absolutelyContinuousOnInterval ht hC
  have hleft :
      ∫ x in 0..t, w x * deriv F x = ∫ x in 0..t, w x * f x := by
    -- Replace the derivative of the primitive by the original integrand a.e.
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx
    intro hx_mem
    have hx_mem' : x ∈ uIcc 0 t := ⟨le_of_lt hx_mem.1, hx_mem.2⟩
    rw [(hx hx_mem' 0 (by simp [ht])).deriv]
  have hright :
      ∫ x in 0..t, deriv w x * F x = (-C) * ∫ x in 0..t, w x * F x := by
    -- Rewrite the derivative of the exponential weight and pull out the constant factor.
    calc
      ∫ x in 0..t, deriv w x * F x
          = ∫ x in 0..t, (-C) * (w x * F x) := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards with x hx
              rw [deriv_expNegMul]
              ring
      _ = (-C) * ∫ x in 0..t, w x * F x := by
            rw [intervalIntegral.integral_const_mul]
  -- Combine integration by parts with the two derivative identifications.
  calc
    ∫ x in 0..t, Real.exp (-C * x) * f x
        = ∫ x in 0..t, w x * deriv F x := by
            simpa [w] using hleft.symm
    _ = w t * F t - w 0 * F 0 - ∫ x in 0..t, deriv w x * F x := by
          exact hw_ac.integral_mul_deriv_eq_deriv_mul hF_ac
    _ = w t * F t + C * ∫ x in 0..t, w x * F x := by
          rw [hright]
          simp [F, w]
    _ = Real.exp (-C * t) * F t + C * ∫ x in 0..t, Real.exp (-C * x) * F x := by
          simp [w]

/-- Helper for Lemma 26.9: the primitive `t ↦ ∫ s in 0..t, f s` is bounded by the exponential
convolution with `g`. -/
lemma primitiveLeExponentialConvolution
    {f g : ℝ → ℝ} {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 < C)
    (hf : IntervalIntegrable f volume 0 T)
    (hg : IntervalIntegrable g volume 0 T)
    (hfg : ∀ t ∈ Icc 0 T, f t ≤ g t + C * ∫ s in 0..t, f s) :
    ∀ t ∈ Icc 0 T, ∫ s in 0..t, f s ≤ ∫ s in 0..t, Real.exp (C * (t - s)) * g s := by
  intro t ht
  let F := fun u ↦ ∫ s in 0..u, f s
  let w := fun x ↦ Real.exp (-C * x)
  have hf_t : IntervalIntegrable f volume 0 t := by
    refine hf.mono_set' ?_
    intro x hx
    rw [uIoc_of_le ht.1] at hx
    rw [uIoc_of_le hT]
    exact ⟨hx.1, le_trans hx.2 ht.2⟩
  have hg_t : IntervalIntegrable g volume 0 t := by
    refine hg.mono_set' ?_
    intro x hx
    rw [uIoc_of_le ht.1] at hx
    rw [uIoc_of_le hT]
    exact ⟨hx.1, le_trans hx.2 ht.2⟩
  have hF_ac : AbsolutelyContinuousOnInterval F 0 t :=
    hf_t.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp [ht.1])
  have hw_cont : ContinuousOn w (uIcc 0 t) := by
    have hw : Continuous w := by
      dsimp [w]
      continuity
    exact hw.continuousOn
  have hF_cont : ContinuousOn F (uIcc 0 t) := hF_ac.continuousOn
  have hwf : IntervalIntegrable (fun x ↦ w x * f x) volume 0 t :=
    hf_t.continuousOn_mul hw_cont
  have hwg : IntervalIntegrable (fun x ↦ w x * g x) volume 0 t :=
    hg_t.continuousOn_mul hw_cont
  have hwF : IntervalIntegrable (fun x ↦ w x * F x) volume 0 t :=
    (hF_cont.intervalIntegrable).continuousOn_mul hw_cont
  have hweighted :
      ∫ x in 0..t, w x * f x ≤
        (∫ x in 0..t, w x * g x) + C * ∫ x in 0..t, w x * F x := by
    -- Integrate the pointwise hypothesis against the positive weight `w`.
    have hmono :
        ∀ x ∈ Icc 0 t, w x * f x ≤ w x * g x + C * (w x * F x) := by
      intro x hx
      have hxT : x ∈ Icc 0 T := ⟨hx.1, le_trans hx.2 ht.2⟩
      have hw_nonneg : 0 ≤ w x := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (hfg x hxT) hw_nonneg]
    have hraw :=
      intervalIntegral.integral_mono_on ht.1 hwf (hwg.add (hwF.const_mul C)) hmono
    rw [intervalIntegral.integral_add hwg (hwF.const_mul C),
      intervalIntegral.integral_const_mul] at hraw
    change
      ∫ x in 0..t, w x * f x ≤
        (∫ x in 0..t, w x * g x) + C * ∫ x in 0..t, w x * F x
    exact hraw
  have hparts := weightedPrimitiveIntegrationByParts (C := C) ht.1 hC.le hf_t
  have hprimitiveWeighted : Real.exp (-C * t) * F t ≤ ∫ x in 0..t, w x * g x := by
    -- The identical `C * ∫ w * F` term cancels from both sides.
    rw [hparts] at hweighted
    nlinarith
  have hscaled :
      F t ≤ Real.exp (C * t) * ∫ x in 0..t, w x * g x := by
    -- Multiply by `exp (C * t)` and use `exp (C * t) * exp (-C * t) = 1`.
    have := mul_le_mul_of_nonneg_left hprimitiveWeighted (by positivity : 0 ≤ Real.exp (C * t))
    calc
      F t = Real.exp (C * t) * (Real.exp (-C * t) * F t) := by
        rw [← mul_assoc, show Real.exp (C * t) * Real.exp (-C * t) = 1 by
          rw [← Real.exp_add]
          rw [show C * t + -C * t = 0 by ring]
          simp]
        simp
      _ ≤ Real.exp (C * t) * ∫ x in 0..t, w x * g x := this
  -- Push the factor `exp (C * t)` under the integral and combine exponents.
  calc
    ∫ s in 0..t, f s = F t := rfl
    _ ≤ Real.exp (C * t) * ∫ x in 0..t, w x * g x := hscaled
    _ = ∫ x in 0..t, Real.exp (C * (t - x)) * g x := by
          calc
            Real.exp (C * t) * ∫ x in 0..t, w x * g x
                = ∫ x in 0..t, Real.exp (C * t) * (w x * g x) := by
                    symm
                    rw [intervalIntegral.integral_const_mul]
            _ = ∫ x in 0..t, Real.exp (C * (t - x)) * g x := by
                  apply intervalIntegral.integral_congr_ae
                  filter_upwards with x hx
                  dsimp [w]
                  rw [← mul_assoc, ← Real.exp_add]
                  rw [show C * t + -C * x = C * (t - x) by ring]

/-- Helper for Lemma 26.9: the constant exponential kernel has the expected closed form. -/
lemma constantExponentialKernelIntegral {C G t : ℝ} (ht : 0 ≤ t) (hC : 0 < C) :
    ∫ s in 0..t, Real.exp (C * (t - s)) * G = G * (Real.exp (C * t) - 1) / C := by
  let H := fun s ↦ -(G / C) * Real.exp (C * (t - s))
  have hcont : ContinuousOn H (Icc 0 t) := by
    have hH : Continuous H := by
      dsimp [H]
      continuity
    exact hH.continuousOn
  have hint : IntervalIntegrable (fun s ↦ Real.exp (C * (t - s)) * G) volume 0 t := by
    have hkernelCont : Continuous fun s ↦ Real.exp (C * (t - s)) * G := by
      continuity
    exact hkernelCont.intervalIntegrable 0 t
  have hderiv :
      ∀ s ∈ Ioo 0 t, HasDerivAt H (Real.exp (C * (t - s)) * G) s := by
    intro s hs
    dsimp [H]
    convert (hasDerivAt_expKernel C t s).const_mul (-(G / C)) using 1
    field_simp [hC.ne']
  -- Use an explicit antiderivative of the kernel.
  calc
    ∫ s in 0..t, Real.exp (C * (t - s)) * G = H t - H 0 := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
    _ = G * (Real.exp (C * t) - 1) / C := by
          dsimp [H]
          simp
          field_simp [hC.ne']
          ring

-- Proof sketch: define `F t = ∫ s in 0..t, f s` and differentiate
-- `t ↦ Real.exp (-C * t) * F t`. The hypothesis gives
-- `(Real.exp (-C * t) * F t)' ≤ Real.exp (-C * t) * g t`; integrate this differential inequality
-- from `0` to `t`, then substitute the resulting bound for `F t` back into the original estimate.
/-- Lemma 26.9: if `f` is bounded above on `[0,T]` by `g` plus `C` times its accumulated integral,
then `f` is bounded by the corresponding Gronwall convolution with `g`. -/
theorem gronwall_intervalIntegral_le
    {f g : ℝ → ℝ} {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 < C)
    (hf : IntervalIntegrable f volume 0 T)
    (hg : IntervalIntegrable g volume 0 T)
    (hfg : ∀ t ∈ Icc 0 T, f t ≤ g t + C * ∫ s in 0..t, f s) :
    ∀ t ∈ Icc 0 T, f t ≤ g t + C * ∫ s in 0..t, Real.exp (C * (t - s)) * g s := by
  intro t ht
  have hprimitive :=
    primitiveLeExponentialConvolution hT hC hf hg hfg t ht
  -- Substitute the primitive bound back into the original pointwise inequality.
  have hscaled :
      C * ∫ s in 0..t, f s ≤ C * ∫ s in 0..t, Real.exp (C * (t - s)) * g s :=
    mul_le_mul_of_nonneg_left hprimitive hC.le
  nlinarith [hfg t ht, hscaled]

-- Proof sketch: apply `gronwall_intervalIntegral_le` with the constant function `g(t) = G`, then
-- compute the resulting exponential convolution explicitly to obtain `G * Real.exp (C * t)`.
/-- Constant-forcing specialization of the integral Gronwall inequality. -/
theorem gronwall_intervalIntegral_le_const
    {f : ℝ → ℝ} {T C G : ℝ}
    (hT : 0 ≤ T) (hC : 0 < C)
    (hf : IntervalIntegrable f volume 0 T)
    (hfg : ∀ t ∈ Icc 0 T, f t ≤ G + C * ∫ s in 0..t, f s) :
    ∀ t ∈ Icc 0 T, f t ≤ G * Real.exp (C * t) := by
  intro t ht
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ G) volume 0 T := _root_.intervalIntegrable_const
  have hmain :=
    gronwall_intervalIntegral_le hT hC hf hconst
      (fun t ht ↦ by simpa using hfg t ht) t ht
  -- Rewrite the constant convolution explicitly and simplify the resulting algebra.
  calc
    f t ≤ G + C * ∫ s in 0..t, Real.exp (C * (t - s)) * G := by
      simpa using hmain
    _ = G + C * (G * (Real.exp (C * t) - 1) / C) := by
      rw [constantExponentialKernelIntegral ht.1 hC]
    _ = G * Real.exp (C * t) := by
      field_simp [hC.ne']
      ring
