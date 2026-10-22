/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part6

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

/-- If both scalar endpoints are finite-valued, the primitive increment between them is the
interval integral of the profile. -/
lemma helperForTheorem_5_24_4_primitiveValue_sub_eq_integral_of_finite_endpoints
    (φ : ℝ → EReal) (a x y : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hy : y ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    oneDimensionalIntervalIntegralPrimitiveValue φ a y -
      oneDimensionalIntervalIntegralPrimitiveValue φ a x =
        (((∫ t in x..y, (φ t).toReal) : ℝ) : EReal) := by
  have hIntAy :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a y :=
    (helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono ha hy).intervalIntegrable
  have hIntAx :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a x :=
    (helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono ha hx).intervalIntegrable
  have hSub :
      (((∫ t in a..y, (φ t).toReal) : ℝ) : EReal) -
          (((∫ t in a..x, (φ t).toReal) : ℝ) : EReal) =
        (((((∫ t in a..y, (φ t).toReal) : ℝ) -
            ∫ t in a..x, (φ t).toReal) : ℝ) : EReal) := by
    simp [EReal.coe_sub]
  calc
    oneDimensionalIntervalIntegralPrimitiveValue φ a y -
        oneDimensionalIntervalIntegralPrimitiveValue φ a x
      = (((∫ t in a..y, (φ t).toReal) : ℝ) : EReal) -
          (((∫ t in a..x, (φ t).toReal) : ℝ) : EReal) := by
          rw [helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
                φ a y hmono ha hy,
              helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
                φ a x hmono ha hx]
    _ = (((((∫ t in a..y, (φ t).toReal) : ℝ) -
            ∫ t in a..x, (φ t).toReal) : ℝ) : EReal) := hSub
    _ = (((∫ t in x..y, (φ t).toReal) : ℝ) : EReal) := by
      exact congrArg (fun r : ℝ => (r : EReal))
        (intervalIntegral.integral_interval_sub_left hIntAy hIntAx)

/-- On a finite-valued interval, the primitive increment dominates the left endpoint profile. -/
lemma helperForTheorem_5_24_4_profile_mul_sub_le_primitiveIncrement_of_finite_lt
    (φ : ℝ → EReal) (x y : ℝ) (hmono : Monotone φ)
    (hxy : x < y)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hy : y ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    ((((y - x) * (φ x).toReal : ℝ) : EReal)) ≤
      oneDimensionalIntervalIntegralPrimitiveValue φ x y := by
  have hMonoToReal :
      MonotoneOn (fun t : ℝ => (φ t).toReal) (Set.uIcc x y) :=
    helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono hx hy
  have hInt :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume x y :=
    hMonoToReal.intervalIntegrable
  have hLe :
      (∫ t in x..y, (φ x).toReal) ≤
        ∫ t in x..y, (φ t).toReal := by
    refine intervalIntegral.integral_mono_on (a := x) (b := y)
      (f := fun _ : ℝ => (φ x).toReal) (g := fun t : ℝ => (φ t).toReal)
      (le_of_lt hxy) ?_ hInt ?_
    · simp
    · intro t ht
      have htFinite :
          t ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
        helperForTheorem_5_24_4_finiteValueSet_mem_between φ hmono hx hy
          (Set.Icc_subset_uIcc ht)
      exact EReal.toReal_le_toReal (hmono ht.1) hx.2 htFinite.1
  have hConst :
      (((∫ t in x..y, (φ x).toReal) : ℝ) : EReal) =
        ((((y - x) * (φ x).toReal : ℝ)) : EReal) := by
    norm_num [intervalIntegral.integral_const, hxy.le, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc]
  have hEval :
      oneDimensionalIntervalIntegralPrimitiveValue φ x y =
        (((∫ t in x..y, (φ t).toReal) : ℝ) : EReal) :=
    helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
      φ x y hmono hx hy
  calc
    ((((y - x) * (φ x).toReal : ℝ) : EReal))
      = (((∫ t in x..y, (φ x).toReal) : ℝ) : EReal) := by
          symm
          exact hConst
    _ ≤ (((∫ t in x..y, (φ t).toReal) : ℝ) : EReal) := by
      exact_mod_cast hLe
    _ = oneDimensionalIntervalIntegralPrimitiveValue φ x y := by
      simpa [hEval] using hEval.symm

/-- On a finite-valued interval, the primitive increment is bounded above by the right endpoint
profile times the interval length. -/
lemma helperForTheorem_5_24_4_primitiveIncrement_le_profile_mul_sub_of_finite_lt
    (φ : ℝ → EReal) (x y : ℝ) (hmono : Monotone φ)
    (hxy : x < y)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hy : y ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    oneDimensionalIntervalIntegralPrimitiveValue φ x y ≤
      ((((y - x) * (φ y).toReal : ℝ) : EReal)) := by
  have hMonoToReal :
      MonotoneOn (fun t : ℝ => (φ t).toReal) (Set.uIcc x y) :=
    helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono hx hy
  have hInt :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume x y :=
    hMonoToReal.intervalIntegrable
  have hLe :
      (∫ t in x..y, (φ t).toReal) ≤
        ∫ t in x..y, (φ y).toReal := by
    refine intervalIntegral.integral_mono_on (a := x) (b := y)
      (f := fun t : ℝ => (φ t).toReal) (g := fun _ : ℝ => (φ y).toReal)
      (le_of_lt hxy) hInt ?_ ?_
    · simp
    · intro t ht
      have htFinite :
          t ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
        helperForTheorem_5_24_4_finiteValueSet_mem_between φ hmono hx hy
          (Set.Icc_subset_uIcc ht)
      exact EReal.toReal_le_toReal (hmono ht.2) htFinite.2 hy.1
  have hConst :
      (((∫ t in x..y, (φ y).toReal) : ℝ) : EReal) =
        ((((y - x) * (φ y).toReal : ℝ)) : EReal) := by
    norm_num [intervalIntegral.integral_const, hxy.le, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc]
  have hEval :
      oneDimensionalIntervalIntegralPrimitiveValue φ x y =
        (((∫ t in x..y, (φ t).toReal) : ℝ) : EReal) :=
    helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
      φ x y hmono hx hy
  calc
    oneDimensionalIntervalIntegralPrimitiveValue φ x y
      = (((∫ t in x..y, (φ t).toReal) : ℝ) : EReal) := hEval
    _ ≤ (((∫ t in x..y, (φ y).toReal) : ℝ) : EReal) := by
      exact_mod_cast hLe
    _ = ((((y - x) * (φ y).toReal : ℝ) : EReal)) := hConst

/-- At a finite-valued base point, every positive finite step produces a right difference quotient
bounded below by the left endpoint profile. -/
lemma helperForTheorem_5_24_4_profile_le_rightDifferenceQuotient_of_positive_finite_step
    (φ : ℝ → EReal) (a x t : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (ht : 0 < t)
    (hxt : x + t ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    (((φ x).toReal : ℝ) : EReal) ≤
      directionalDifferenceQuotientAt (oneDimensionalIntervalIntegralPrimitive φ a)
        (scalarPoint x) (scalarPoint 1) t := by
  have hstep :
      scalarPoint x + t • scalarPoint 1 = scalarPoint (x + t) := by
    ext i
    simp [scalarPoint]
  have hSubEq :
      oneDimensionalIntervalIntegralPrimitiveValue φ a (x + t) -
          oneDimensionalIntervalIntegralPrimitiveValue φ a x =
        oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t) := by
    calc
      oneDimensionalIntervalIntegralPrimitiveValue φ a (x + t) -
          oneDimensionalIntervalIntegralPrimitiveValue φ a x
        = (((∫ s in x..x + t, (φ s).toReal) : ℝ) : EReal) := by
            exact helperForTheorem_5_24_4_primitiveValue_sub_eq_integral_of_finite_endpoints
              φ a x (x + t) hmono ha hx hxt
      _ = oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t) := by
        symm
        exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
          φ x (x + t) hmono hx hxt
  have hMulLe :
      (((φ x).toReal : ℝ) : EReal) * (t : EReal) ≤
        oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t) := by
    calc
      (((φ x).toReal : ℝ) : EReal) * (t : EReal)
        = ((((x + t - x) * (φ x).toReal : ℝ) : EReal)) := by
            simpa [mul_comm]
      _ ≤ oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t) :=
        helperForTheorem_5_24_4_profile_mul_sub_le_primitiveIncrement_of_finite_lt
          φ x (x + t) hmono (by linarith) hx hxt
  have htPosE : (0 : EReal) < (t : EReal) := by
    exact_mod_cast ht
  have htNeTop : (t : EReal) ≠ ⊤ := by
    simp
  have hDQ :
      directionalDifferenceQuotientAt (oneDimensionalIntervalIntegralPrimitive φ a)
          (scalarPoint x) (scalarPoint 1) t =
        (oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t)) / (t : EReal) := by
    rw [directionalDifferenceQuotientAt, oneDimensionalIntervalIntegralPrimitive]
    change
      (oneDimensionalIntervalIntegralPrimitiveValue φ a (x + t * 1) -
          oneDimensionalIntervalIntegralPrimitiveValue φ a x) / (t : EReal) =
        (oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t)) / (t : EReal)
    simpa using congrArg (fun z : EReal => z / (t : EReal)) hSubEq
  rw [hDQ]
  exact (EReal.le_div_iff_mul_le htPosE htNeTop).2 hMulLe

/-- At a finite-valued base point, every positive finite step produces a right difference quotient
bounded above by the right endpoint profile. -/
lemma helperForTheorem_5_24_4_rightDifferenceQuotient_le_profile_of_positive_finite_step
    (φ : ℝ → EReal) (a x t : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (ht : 0 < t)
    (hxt : x + t ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    directionalDifferenceQuotientAt (oneDimensionalIntervalIntegralPrimitive φ a)
        (scalarPoint x) (scalarPoint 1) t ≤
      (((φ (x + t)).toReal : ℝ) : EReal) := by
  have hstep :
      scalarPoint x + t • scalarPoint 1 = scalarPoint (x + t) := by
    ext i
    simp [scalarPoint]
  have hSubEq :
      oneDimensionalIntervalIntegralPrimitiveValue φ a (x + t) -
          oneDimensionalIntervalIntegralPrimitiveValue φ a x =
        oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t) := by
    calc
      oneDimensionalIntervalIntegralPrimitiveValue φ a (x + t) -
          oneDimensionalIntervalIntegralPrimitiveValue φ a x
        = (((∫ s in x..x + t, (φ s).toReal) : ℝ) : EReal) := by
            exact helperForTheorem_5_24_4_primitiveValue_sub_eq_integral_of_finite_endpoints
              φ a x (x + t) hmono ha hx hxt
      _ = oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t) := by
        symm
        exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
          φ x (x + t) hmono hx hxt
  have hLeMul :
      oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t) ≤
        (((φ (x + t)).toReal : ℝ) : EReal) * (t : EReal) := by
    calc
      oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t)
        ≤ ((((x + t - x) * (φ (x + t)).toReal : ℝ) : EReal)) :=
          helperForTheorem_5_24_4_primitiveIncrement_le_profile_mul_sub_of_finite_lt
            φ x (x + t) hmono (by linarith) hx hxt
      _ = (((φ (x + t)).toReal : ℝ) : EReal) * (t : EReal) := by
        simpa [mul_comm]
  have htPosE : (0 : EReal) < (t : EReal) := by
    exact_mod_cast ht
  have htNeTop : (t : EReal) ≠ ⊤ := by
    simp
  have hDQ :
      directionalDifferenceQuotientAt (oneDimensionalIntervalIntegralPrimitive φ a)
          (scalarPoint x) (scalarPoint 1) t =
        (oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t)) / (t : EReal) := by
    rw [directionalDifferenceQuotientAt, oneDimensionalIntervalIntegralPrimitive]
    change
      (oneDimensionalIntervalIntegralPrimitiveValue φ a (x + t * 1) -
          oneDimensionalIntervalIntegralPrimitiveValue φ a x) / (t : EReal) =
        (oneDimensionalIntervalIntegralPrimitiveValue φ x (x + t)) / (t : EReal)
    simpa using congrArg (fun z : EReal => z / (t : EReal)) hSubEq
  rw [hDQ]
  exact (EReal.div_le_iff_le_mul htPosE htNeTop).2 (by simpa [mul_comm] using hLeMul)

/-- On the finite-valued interval of a monotone profile, the interval-integral primitive satisfies
the convex-combination inequality from the proof of Theorem 5.24.4. -/
lemma helperForTheorem_5_24_4_primitiveValue_convexCombo_of_finite_lt
    (φ : ℝ → EReal) (a x y θ : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxy : x < y)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hy : y ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let z := (1 - θ) * x + θ * y
    oneDimensionalIntervalIntegralPrimitiveValue φ a z ≤
      ((1 - θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a x +
        ((θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a y := by
  dsimp
  let z := (1 - θ) * x + θ * y
  have hz_left : x ≤ z := by
    dsimp [z]
    nlinarith
  have hz_right : z ≤ y := by
    dsimp [z]
    nlinarith
  have hz :
      z ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
    helperForTheorem_5_24_4_finiteValueSet_mem_between φ hmono hx hy
      (by simpa [Set.uIcc_of_le hxy.le] using (show z ∈ Set.Icc x y from ⟨hz_left, hz_right⟩))
  by_cases hθx : θ = 0
  · subst hθx
    have hz0 :
        ((1 - (0 : ℝ)) * x + (0 : ℝ) * y) = x := by
      ring
    have hL :
        oneDimensionalIntervalIntegralPrimitiveValue φ a ((1 - (0 : ℝ)) * x + (0 : ℝ) * y) =
          oneDimensionalIntervalIntegralPrimitiveValue φ a x := by
      simp [hz0]
    calc
      oneDimensionalIntervalIntegralPrimitiveValue φ a ((1 - (0 : ℝ)) * x + (0 : ℝ) * y)
        = oneDimensionalIntervalIntegralPrimitiveValue φ a x := hL
      _ ≤ ((1 - (0 : ℝ)) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a x +
            ((0 : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a y := by
          simp
  by_cases hθy : θ = 1
  · subst hθy
    have hz1 :
        ((1 - (1 : ℝ)) * x + (1 : ℝ) * y) = y := by
      ring
    have hL :
        oneDimensionalIntervalIntegralPrimitiveValue φ a ((1 - (1 : ℝ)) * x + (1 : ℝ) * y) =
          oneDimensionalIntervalIntegralPrimitiveValue φ a y := by
      simp [hz1]
    have hzeroR : (1 - (1 : ℝ)) = 0 := by ring
    have hzero : ((1 - (1 : ℝ)) : EReal) = 0 := by
      exact_mod_cast hzeroR
    rw [hL, hzero]
    simp
  have hθlt : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθx)
  have hθgt : θ < 1 := lt_of_le_of_ne hθ1 hθy
  have hz_repr : z = x + θ * (y - x) := by
    dsimp [z]
    ring
  have hxz : x < z := by
    rw [hz_repr]
    nlinarith
  have hzy : z < y := by
    rw [hz_repr]
    nlinarith
  let Fx : ℝ := ∫ t in a..x, (φ t).toReal
  let Fy : ℝ := ∫ t in a..y, (φ t).toReal
  let Fz : ℝ := ∫ t in a..z, (φ t).toReal
  have hUpperE :
      (((∫ t in x..z, (φ t).toReal) : ℝ) : EReal) ≤
        ((((z - x) * (φ z).toReal : ℝ) : EReal)) := by
    calc
      (((∫ t in x..z, (φ t).toReal) : ℝ) : EReal)
        = oneDimensionalIntervalIntegralPrimitiveValue φ x z := by
            symm
            exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
              φ x z hmono hx hz
      _ ≤ ((((z - x) * (φ z).toReal : ℝ) : EReal)) :=
        helperForTheorem_5_24_4_primitiveIncrement_le_profile_mul_sub_of_finite_lt
          φ x z hmono hxz hx hz
  have hLowerE :
      ((((y - z) * (φ z).toReal : ℝ) : EReal)) ≤
        (((∫ t in z..y, (φ t).toReal) : ℝ) : EReal) := by
    calc
      ((((y - z) * (φ z).toReal : ℝ) : EReal))
        ≤ oneDimensionalIntervalIntegralPrimitiveValue φ z y :=
          helperForTheorem_5_24_4_profile_mul_sub_le_primitiveIncrement_of_finite_lt
            φ z y hmono hzy hz hy
      _ = (((∫ t in z..y, (φ t).toReal) : ℝ) : EReal) := by
        exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
          φ z y hmono hz hy
  have hUpper :
      ∫ t in x..z, (φ t).toReal ≤ (z - x) * (φ z).toReal := by
    exact_mod_cast hUpperE
  have hLower :
      (y - z) * (φ z).toReal ≤ ∫ t in z..y, (φ t).toReal := by
    exact_mod_cast hLowerE
  have hzEq1 : z - x = θ * (y - x) := by
    dsimp [z]
    ring
  have hzEq2 : y - z = (1 - θ) * (y - x) := by
    dsimp [z]
    ring
  have hBalance : (1 - θ) * (z - x) = θ * (y - z) := by
    rw [hzEq1, hzEq2]
    ring
  have hWeighted :
      (1 - θ) * (∫ t in x..z, (φ t).toReal) ≤
        θ * (∫ t in z..y, (φ t).toReal) := by
    have h1 :
        (1 - θ) * (∫ t in x..z, (φ t).toReal) ≤
          (1 - θ) * ((z - x) * (φ z).toReal) :=
      mul_le_mul_of_nonneg_left hUpper (sub_nonneg.mpr hθ1)
    have h2 :
        θ * ((y - z) * (φ z).toReal) ≤
          θ * (∫ t in z..y, (φ t).toReal) :=
      mul_le_mul_of_nonneg_left hLower hθ0
    calc
      (1 - θ) * (∫ t in x..z, (φ t).toReal)
        ≤ (1 - θ) * ((z - x) * (φ z).toReal) := h1
      _ = ((1 - θ) * (z - x)) * (φ z).toReal := by ring
      _ = (θ * (y - z)) * (φ z).toReal := by rw [hBalance]
      _ = θ * ((y - z) * (φ z).toReal) := by ring
      _ ≤ θ * (∫ t in z..y, (φ t).toReal) := h2
  have hIntAz :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a z :=
    (helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono ha hz).intervalIntegrable
  have hIntAy :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a y :=
    (helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono ha hy).intervalIntegrable
  have hIntAx :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a x :=
    (helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono ha hx).intervalIntegrable
  have hIntzy :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume z y :=
    (helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono hz hy).intervalIntegrable
  have hIntxz :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume x z :=
    (helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono hx hz).intervalIntegrable
  have hSub1 : Fz - Fx = ∫ t in x..z, (φ t).toReal := by
    dsimp [Fx, Fz]
    exact intervalIntegral.integral_interval_sub_left hIntAz hIntAx
  have hSub2 : Fy - Fz = ∫ t in z..y, (φ t).toReal := by
    dsimp [Fy, Fz]
    exact intervalIntegral.integral_interval_sub_left hIntAy hIntAz
  have hReal :
      Fz ≤ (1 - θ) * Fx + θ * Fy := by
    have hWeighted' : (1 - θ) * (Fz - Fx) ≤ θ * (Fy - Fz) := by
      simpa [hSub1, hSub2] using hWeighted
    nlinarith
  have hFx :
      oneDimensionalIntervalIntegralPrimitiveValue φ a x = ((Fx : ℝ) : EReal) := by
    dsimp [Fx]
    exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
      φ a x hmono ha hx
  have hFy :
      oneDimensionalIntervalIntegralPrimitiveValue φ a y = ((Fy : ℝ) : EReal) := by
    dsimp [Fy]
    exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
      φ a y hmono ha hy
  have hFz :
      oneDimensionalIntervalIntegralPrimitiveValue φ a z = ((Fz : ℝ) : EReal) := by
    dsimp [Fz]
    exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
      φ a z hmono ha hz
  rw [hFx, hFy, hFz]
  exact_mod_cast hReal

/-- The same convex-combination inequality also covers the degenerate endpoint case `x = y`. -/
lemma helperForTheorem_5_24_4_primitiveValue_convexCombo_of_finite_le
    (φ : ℝ → EReal) (a x y θ : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxy : x ≤ y)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hy : y ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let z := (1 - θ) * x + θ * y
    oneDimensionalIntervalIntegralPrimitiveValue φ a z ≤
      ((1 - θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a x +
        ((θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a y := by
  rcases lt_or_eq_of_le hxy with hxy' | rfl
  · simpa using
      helperForTheorem_5_24_4_primitiveValue_convexCombo_of_finite_lt
        φ a x y θ hmono ha hxy' hx hy hθ0 hθ1
  · dsimp
    let Fx : ℝ := ∫ t in a..x, (φ t).toReal
    have hFx :
        oneDimensionalIntervalIntegralPrimitiveValue φ a x = ((Fx : ℝ) : EReal) := by
      dsimp [Fx]
      exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
        φ a x hmono ha hx
    have hzEq : ((1 - θ) * x + θ * x) = x := by ring
    have hReal :
        Fx ≤ (1 - θ) * Fx + θ * Fx := by
      have hEq : (1 - θ) * Fx + θ * Fx = Fx := by
        ring
      rw [hEq]
    calc
      oneDimensionalIntervalIntegralPrimitiveValue φ a ((1 - θ) * x + θ * x)
        = ((Fx : ℝ) : EReal) := by
            rw [hzEq, hFx]
      _ ≤ ((1 - θ : ℝ) : EReal) * ((Fx : ℝ) : EReal) +
            ((θ : ℝ) : EReal) * ((Fx : ℝ) : EReal) := by
              exact_mod_cast hReal
      _ = ((1 - θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a x +
            ((θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a x := by
            rw [hFx]



end Section24
end Chap05
