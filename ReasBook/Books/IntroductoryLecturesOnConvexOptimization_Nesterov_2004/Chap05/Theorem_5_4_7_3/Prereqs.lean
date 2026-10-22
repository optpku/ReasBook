/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_2

noncomputable section

attribute [local instance 10000] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance 10000] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance 10000] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instCompleteSpaceRealProdProd

namespace Nesterov.Chap05.Theorem_5_4_7_3.Prereqs

/-- Helper for Theorem 5.4.7.3: a short owner alias for the raw outer logarithmic barrier on
`powerConeQ2`. -/
abbrev powerConeQ2OuterBarrier : (ℝ × ℝ) → ℝ :=
  (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0) +
    (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0)

/-- Helper for Theorem 5.4.7.3: the orthant domain `powerConeQ1` is closed. -/
private theorem powerConeQ1IsClosed : IsClosed (powerConeQ1 : Set (ℝ × ℝ)) := by
  have hfst : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hsnd : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} :=
    isClosed_le continuous_const continuous_snd
  -- Rewrite the orthant owner to the two closed coordinate half-spaces.
  rw [powerConeQ1_eq_coordinate_halfspaces]
  exact hfst.inter hsnd

/-- Helper for Theorem 5.4.7.3: the affine line `t ↦ x + t • h` has derivative `h`. -/
private theorem affineLineHasDerivAt
    {x h : ℝ × ℝ} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const h).const_add x

/-- Helper for Theorem 5.4.7.3: the affine line has vanishing second iterated derivative. -/
private theorem affineLineIteratedDerivTwo
    {x h : ℝ × ℝ} :
    iteratedDeriv 2 (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ (0 : ℝ × ℝ) := by
  -- Differentiate the affine line once to a constant, then differentiate that constant again.
  funext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ h := by
    funext s
    exact (affineLineHasDerivAt (x := x) (h := h) s).deriv
  rw [hderiv, deriv_const]

/-- Helper for Theorem 5.4.7.3: the second derivative of the line slice of `f` is the packaged
repeated second Fréchet derivative `vectorSecondDirectionalDerivative f x h`. -/
private theorem lineSliceIteratedDerivTwoEqVectorSecondDirectionalDerivative
    {f : (ℝ × ℝ) → ℝ} {x h : ℝ × ℝ} (hf : ContDiffAt ℝ 3 f x) :
    iteratedDeriv 2 (fun s : ℝ ↦ f (x + s • h)) 0 =
      vectorSecondDirectionalDerivative f x h := by
  let line : ℝ → ℝ × ℝ := fun s ↦ x + s • h
  have hf₂ : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hline₂ : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  -- The quadratic chain rule collapses because the affine line has zero second derivative.
  have hcomp :=
    iteratedDeriv_vcomp_two (g := f) (f := line) (x := 0) (by simpa [line] using hf₂) hline₂
  have hline_deriv : deriv line 0 = h := by
    simpa [line] using (affineLineHasDerivAt (x := x) (h := h) 0).deriv
  simpa [line, Function.comp, hline_deriv, affineLineIteratedDerivTwo,
    vectorSecondDirectionalDerivative] using hcomp

/-- Helper for Theorem 5.4.7.3: for scalar maps on `ℝ × ℝ`, the repeated second Fréchet
derivative agrees with the chapter's scalar second directional derivative. -/
private theorem vectorSecondDirectionalDerivativeEqSecondDirectionalDerivative
    {f : (ℝ × ℝ) → ℝ} {x h : ℝ × ℝ} (hf : ContDiffAt ℝ 3 f x) :
    vectorSecondDirectionalDerivative f x h = secondDirectionalDerivative f x h := by
  rw [secondDirectionalDerivative]
  symm
  simpa [directionalSlice] using
    (lineSliceIteratedDerivTwoEqVectorSecondDirectionalDerivative (f := f) (x := x) (h := h) hf)

/-- Helper for Theorem 5.4.7.3: the weighted geometric mean is the concave `C^3` map required by
the cone-composition theorem on the orthant `powerConeQ1` in the chapter's `RealProdL2`
ambient. -/
theorem power_cone_geometric_mean_is_three_times_cont_diff_concave_on_with
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    @IsThreeTimesContDiffConcaveOnWith
      (ℝ × ℝ)
      ℝ
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instNormedSpaceRealProd
      Real.normedAddCommGroup
      RCLike.toInnerProductSpaceReal.toNormedSpace
      powerConeQ1
      (ConvexCone.positive ℝ ℝ)
      (powerConeGeometricMean α) := by
  refine
    { out := by
        simpa [ConvexCone.mem_positive] using (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ)))
      isClosed_domain := powerConeQ1IsClosed
      convex_domain := powerConeQ1_convex
      contDiffOn := powerConeGeometricMean_contDiffOn_interior α
      neg_second_directional_derivative_mem := ?_ }
  intro x hx h
  have hx₁ : 0 < x.1 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.1
  have hx₂ : 0 < x.2 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.2
  have hcontAt : ContDiffAt ℝ 3 (powerConeGeometricMean α) x :=
    (powerConeGeometricMean_contDiffOn_interior α).contDiffAt (isOpen_interior.mem_nhds hx)
  have hcontAt₂ : ContDiffAt ℝ 2 (powerConeGeometricMean α) x :=
    hcontAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hiterWithin :
      iteratedFDerivWithin ℝ 2 (powerConeGeometricMean α) (interior powerConeQ1) x =
        iteratedFDeriv ℝ 2 (powerConeGeometricMean α) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv isOpen_interior.uniqueDiffOn hcontAt₂ hx
  have hiter :
      iteratedFDerivWithin ℝ 2 (powerConeGeometricMean α) (interior powerConeQ1) x (fun _ ↦ h) =
        secondDirectionalDerivative (powerConeGeometricMean α) x h := by
    -- On the open orthant interior, the within-domain derivative is the ambient derivative.
    calc
      iteratedFDerivWithin ℝ 2 (powerConeGeometricMean α) (interior powerConeQ1) x (fun _ ↦ h) =
          vectorSecondDirectionalDerivative (powerConeGeometricMean α) x h := by
            simpa [vectorSecondDirectionalDerivative] using
              congrArg (fun T ↦ T (fun _ ↦ h)) hiterWithin
      _ = secondDirectionalDerivative (powerConeGeometricMean α) x h := by
        exact vectorSecondDirectionalDerivativeEqSecondDirectionalDerivative hcontAt
  have hgeom_nonneg : 0 ≤ powerConeGeometricMean α x := by
    -- The weighted geometric mean is nonnegative on the strict orthant.
    rw [show powerConeGeometricMean α x =
      Real.rpow x.1 α * Real.rpow x.2 (1 - α) by
      simpa using powerConeGeometricMean_apply α x.1 x.2]
    exact mul_nonneg (Real.rpow_nonneg hx₁.le α) (Real.rpow_nonneg hx₂.le (1 - α))
  rw [ConvexCone.mem_positive]
  -- Route correction: use the explicit second-derivative formula for `xi[α]`, then rewrite the
  -- class field's within-domain derivative to that scalar directional derivative.
  calc
    0 ≤ α * (1 - α) * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ) * powerConeGeometricMean α x := by
      have hα : 0 ≤ α := le_of_lt hα₀
      have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα₁.le
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hα h1α) (sq_nonneg (h.1 / x.1 - h.2 / x.2)))
        hgeom_nonneg
    _ = -secondDirectionalDerivative (powerConeGeometricMean α) x h := by
      calc
        α * (1 - α) * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ) * powerConeGeometricMean α x =
            -((-α * (1 - α) * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ)) *
              powerConeGeometricMean α x) := by
              ring
        _ = -secondDirectionalDerivative (powerConeGeometricMean α) x h := by
          exact
            (congrArg Neg.neg
              (powerConeGeometricMean_secondDirectionalDerivative
                (α := α) (x := x) (h := h) hx₁ hx₂)).symm
    _ = -iteratedFDerivWithin ℝ 2 (powerConeGeometricMean α) (interior powerConeQ1) x
          (fun _ ↦ h) := by
      rw [hiter]

/-- Helper for Theorem 5.4.7.3: the planar comparison set `powerConeQ2 = {(y, z) | y >= |z|}` is
closed. -/
theorem powerConeQ2_closed : IsClosed (powerConeQ2 : Set (ℝ × ℝ)) := by
  have hset : (powerConeQ2 : Set (ℝ × ℝ)) = {yz : ℝ × ℝ | |yz.2| ≤ yz.1} := by
    ext yz
    rcases yz with ⟨y, z⟩
    simpa [ge_iff_le] using (mem_powerConeQ2_iff y z)
  rw [hset]
  exact isClosed_le (continuous_abs.comp continuous_snd) continuous_fst

/-- Helper for Theorem 5.4.7.3: the planar comparison set `powerConeQ2 = {(y, z) | y >= |z|}` is
convex. -/
theorem powerConeQ2_convex : Convex ℝ (powerConeQ2 : Set (ℝ × ℝ)) := by
  intro x hx y hy a b ha hb hab
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rw [mem_powerConeQ2_iff] at hx hy ⊢
  -- Use convexity of the absolute value bound `|a z₁ + b z₂| ≤ a |z₁| + b |z₂|`.
  calc
    |a * x₂ + b * y₂| ≤ |a * x₂| + |b * y₂| := by
      exact abs_add_le (a * x₂) (b * y₂)
    _ = a * |x₂| + b * |y₂| := by
      rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hb]
    _ ≤ a * x₁ + b * y₁ := by
      gcongr

/-- Helper for Theorem 5.4.7.3: the half-space barrier `-log (y - z)` has parameter `mu = 1`
on the strict domain `y > z`. -/
private theorem powerConeQ2MinusSlackIsOneSelfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (interior {yz : ℝ × ℝ | yz.2 ≤ yz.1})
      (1 : NNReal)
      (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0) := by
  let gapLinear : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ) - (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let gapMap : (ℝ × ℝ) →ᴬ[ℝ] ℝ := gapLinear.toContinuousAffineMap
  have hpull :
      IsSelfConcordantBarrierOnWith
        (gapMap ⁻¹' Set.Ioi (0 : ℝ))
        1
        (fun yz : ℝ × ℝ ↦ -Real.log (yz.1 - yz.2)) := by
    -- Pull back the scalar `-log` barrier along the affine slack `y - z`.
    simpa [gapMap, gapLinear, Function.comp] using
      (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap gapMap)
  have hsurj : Function.Surjective gapLinear := by
    rintro t
    refine ⟨(t, 0), ?_⟩
    simp [gapLinear]
  have hdom : gapMap ⁻¹' Set.Ioi (0 : ℝ) = interior {yz : ℝ × ℝ | yz.2 ≤ yz.1} := by
    calc
      gapMap ⁻¹' Set.Ioi (0 : ℝ) = gapLinear ⁻¹' interior (Set.Ici (0 : ℝ)) := by
        ext yz
        simp [gapMap, gapLinear]
      _ = interior (gapLinear ⁻¹' Set.Ici (0 : ℝ)) := by
        symm
        simpa using gapLinear.interior_preimage hsurj (Set.Ici (0 : ℝ))
      _ = interior {yz : ℝ × ℝ | yz.2 ≤ yz.1} := by
        congr 1
        ext yz
        rcases yz with ⟨y, z⟩
        simp [gapLinear, sub_eq_add_neg]
  have hfun :
      (fun yz : ℝ × ℝ ↦ -Real.log (yz.1 - yz.2)) =
        sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0 := by
    funext yz
    rcases yz with ⟨y, z⟩
    -- Normalize the canonical sublevel barrier to the textbook logarithmic formula.
    rw [sublevelLogBarrier_apply]
    ring_nf
  simpa [hdom, hfun] using hpull

/-- Helper for Theorem 5.4.7.3: the half-space barrier `-log (y + z)` has parameter `mu = 1`
on the strict domain `y + z > 0`. -/
private theorem powerConeQ2PlusSlackIsOneSelfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (interior {yz : ℝ × ℝ | 0 ≤ yz.1 + yz.2})
      (1 : NNReal)
      (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0) := by
  let gapLinear : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ) + (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let gapMap : (ℝ × ℝ) →ᴬ[ℝ] ℝ := gapLinear.toContinuousAffineMap
  have hpull :
      IsSelfConcordantBarrierOnWith
        (gapMap ⁻¹' Set.Ioi (0 : ℝ))
        1
        (fun yz : ℝ × ℝ ↦ -Real.log (yz.1 + yz.2)) := by
    -- Pull back the scalar `-log` barrier along the affine slack `y + z`.
    simpa [gapMap, gapLinear, Function.comp] using
      (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap gapMap)
  have hsurj : Function.Surjective gapLinear := by
    intro t
    refine ⟨(t, 0), ?_⟩
    simp [gapLinear]
  have hdom : gapMap ⁻¹' Set.Ioi (0 : ℝ) = interior {yz : ℝ × ℝ | 0 ≤ yz.1 + yz.2} := by
    calc
      gapMap ⁻¹' Set.Ioi (0 : ℝ) = gapLinear ⁻¹' interior (Set.Ici (0 : ℝ)) := by
        ext yz
        simp [gapMap, gapLinear]
      _ = interior (gapLinear ⁻¹' Set.Ici (0 : ℝ)) := by
        symm
        simpa using gapLinear.interior_preimage hsurj (Set.Ici (0 : ℝ))
      _ = interior {yz : ℝ × ℝ | 0 ≤ yz.1 + yz.2} := by
        rw [show gapLinear ⁻¹' Set.Ici (0 : ℝ) = {yz : ℝ × ℝ | 0 ≤ yz.1 + yz.2} by
          ext yz
          simp [gapLinear]]
  have hfun :
      (fun yz : ℝ × ℝ ↦ -Real.log (yz.1 + yz.2)) =
        sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0 := by
    funext yz
    rcases yz with ⟨y, z⟩
    -- Normalize the canonical sublevel barrier to the textbook logarithmic formula.
    rw [sublevelLogBarrier_apply]
    ring_nf
  simpa [hdom, hfun] using hpull

/-- Helper for Theorem 5.4.7.3: the interior of the half-space `z <= y` is the strict region
`z < y`. -/
private theorem memInteriorPowerConeQ2MinusSlackIff (y z : ℝ) :
    (y, z) ∈ interior {yz : ℝ × ℝ | yz.2 ≤ yz.1} ↔ z < y := by
  let gapLinear : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ) - (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hsurj : Function.Surjective gapLinear := by
    intro t
    refine ⟨(t, 0), ?_⟩
    simp [gapLinear]
  have hset : {yz : ℝ × ℝ | yz.2 ≤ yz.1} = gapLinear ⁻¹' Set.Ici (0 : ℝ) := by
    ext yz
    rcases yz with ⟨y', z'⟩
    simp [gapLinear, sub_eq_add_neg]
  have hpre :
      interior (gapLinear ⁻¹' Set.Ici (0 : ℝ)) = gapLinear ⁻¹' interior (Set.Ici (0 : ℝ)) := by
    simpa using gapLinear.interior_preimage hsurj (Set.Ici (0 : ℝ))
  rw [hset, hpre]
  simp [gapLinear, sub_eq_add_neg]

/-- Helper for Theorem 5.4.7.3: the interior of the half-space `0 <= y + z` is the strict region
`0 < y + z`. -/
private theorem memInteriorPowerConeQ2PlusSlackIff (y z : ℝ) :
    (y, z) ∈ interior {yz : ℝ × ℝ | 0 ≤ yz.1 + yz.2} ↔ 0 < y + z := by
  let gapLinear : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ) + (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hsurj : Function.Surjective gapLinear := by
    intro t
    refine ⟨(t, 0), ?_⟩
    simp [gapLinear]
  have hset : {yz : ℝ × ℝ | 0 ≤ yz.1 + yz.2} = gapLinear ⁻¹' Set.Ici (0 : ℝ) := by
    ext yz
    rcases yz with ⟨y', z'⟩
    simp [gapLinear]
  have hpre :
      interior (gapLinear ⁻¹' Set.Ici (0 : ℝ)) = gapLinear ⁻¹' interior (Set.Ici (0 : ℝ)) := by
    simpa using gapLinear.interior_preimage hsurj (Set.Ici (0 : ℝ))
  rw [hset, hpre]
  simp [gapLinear]

/-- Helper for Theorem 5.4.7.3: the interior of `powerConeQ2 = {(y, z) | y >= |z|}` is the strict
region `y > |z|`. -/
private theorem memInteriorPowerConeQ2Iff (y z : ℝ) :
    (y, z) ∈ interior powerConeQ2 ↔ |z| < y := by
  let swapLinear : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap
  have hsurj : Function.Surjective swapLinear :=
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).surjective
  have hset :
      powerConeQ2 = swapLinear ⁻¹' (secondOrderCone ℝ : Set (ℝ × ℝ)) := by
    rfl
  have hpre :
      interior (swapLinear ⁻¹' (secondOrderCone ℝ : Set (ℝ × ℝ))) =
        swapLinear ⁻¹' interior (secondOrderCone ℝ : Set (ℝ × ℝ)) := by
    simpa using swapLinear.interior_preimage hsurj (secondOrderCone ℝ : Set (ℝ × ℝ))
  rw [hset, hpre]
  simpa [swapLinear, Real.norm_eq_abs] using
    (mem_interior_secondOrderCone_iff (swapLinear (y, z)))

/-- Helper for Theorem 5.4.7.3: the raw outer owner is a `mu = 2` self-concordant barrier on
`interior powerConeQ2`. -/
theorem powerConeQ2RawBarrierIsTwoSelfConcordantBarrier :
    @IsSelfConcordantBarrierOnWith
      (ℝ × ℝ)
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      (interior powerConeQ2)
      (2 : NNReal)
      powerConeQ2OuterBarrier := by
  have hsum := powerConeQ2MinusSlackIsOneSelfConcordantBarrier.add
    powerConeQ2PlusSlackIsOneSelfConcordantBarrier
  have hdom :
      interior {yz : ℝ × ℝ | yz.2 ≤ yz.1} ∩ interior {yz : ℝ × ℝ | 0 ≤ yz.1 + yz.2} =
        interior powerConeQ2 := by
    ext yz
    rcases yz with ⟨y, z⟩
    rw [Set.mem_inter_iff, memInteriorPowerConeQ2MinusSlackIff,
      memInteriorPowerConeQ2PlusSlackIff, memInteriorPowerConeQ2Iff]
    constructor
    · rintro ⟨hminus, hplus⟩
      refine abs_lt.mpr ?_
      constructor
      · linarith
      · exact hminus
    · intro hstrict
      refine ⟨(abs_lt.mp hstrict).2, ?_⟩
      linarith [(abs_lt.mp hstrict).1]
  have hparam : (1 : NNReal) + 1 = 2 := by
    norm_num
  -- Add the two half-space barriers and rewrite the common domain to `interior powerConeQ2`.
  simpa [hdom, powerConeQ2OuterBarrier, hparam] using hsum

/-- Helper for Theorem 5.4.7.3: every positive-cone direction `(s, 0)` is a recession direction
of `powerConeQ2`. -/
theorem powerConeQ2_positive_recession
    {s : ℝ} (hs : s ∈ (ConvexCone.positive ℝ ℝ : Set ℝ))
    {p : ℝ × ℝ} (hp : p ∈ powerConeQ2) (τ : ℝ) (hτ : 0 ≤ τ) :
    p + τ • (s, (0 : ℝ)) ∈ powerConeQ2 := by
  have hs' : 0 ≤ s := by
    simpa [ConvexCone.mem_positive] using hs
  rcases p with ⟨y, z⟩
  rw [mem_powerConeQ2_iff] at hp ⊢
  -- Adding nonnegative mass to the `y` coordinate preserves the inequality `|z| <= y`.
  have hτs : 0 ≤ τ * s := mul_nonneg hτ hs'
  have hineq : |z + τ * 0| ≤ y + τ * s := by
    calc
      |z + τ * 0| = |z| := by simp
      _ ≤ y := hp
      _ ≤ y + τ * s := by linarith
  simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hineq

end Nesterov.Chap05.Theorem_5_4_7_3.Prereqs
