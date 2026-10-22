/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_5
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

open scoped QTwoPlus

/-- Helper for Theorem 5.4.7.4: a short owner alias for the explicit `Q₂⁺` cone-composition
feasible set. -/
private abbrev powerConePlusCoreSet (α : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  coneCompositionFeasibleSet
    powerConeQ1
    (ConvexCone.positive ℝ ℝ)
    (powerConeGeometricMean α)
    Q₂⁺

/-- Helper for Theorem 5.4.7.4: a short owner alias for the outer `Q₂⁺` logarithmic barrier. -/
private abbrev powerConePlusOuterBarrier : (ℝ × ℝ) → ℝ :=
  sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0

/-- Helper for Theorem 5.4.7.4: a short owner alias for the specialized composed barrier. -/
private abbrev powerConePlusCoreBarrier (α : ℝ) : ((ℝ × ℝ) × ℝ) → ℝ :=
  coneCompositionBarrier
    powerConeBarrier
    powerConePlusOuterBarrier
    (powerConeGeometricMean α)
    1

/-- Helper for Theorem 5.4.7.4: the orthant domain `powerConeQ1` is closed. -/
private theorem powerConeQ1IsClosed : IsClosed (powerConeQ1 : Set (ℝ × ℝ)) := by
  have hfst : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hsnd : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} :=
    isClosed_le continuous_const continuous_snd
  -- Rewrite the orthant owner to the two coordinate half-spaces.
  rw [powerConeQ1_eq_coordinate_halfspaces]
  exact hfst.inter hsnd

/-- Helper for Theorem 5.4.7.4: the affine line `t ↦ x + t • h` has derivative `h`. -/
private theorem affineLineHasDerivAt
    {x h : ℝ × ℝ} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const h).const_add x

/-- Helper for Theorem 5.4.7.4: the affine line has vanishing second iterated derivative. -/
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

/-- Helper for Theorem 5.4.7.4: the second derivative of the line slice of `f` is the packaged
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

/-- Helper for Theorem 5.4.7.4: for scalar maps on `ℝ × ℝ`, the repeated second Fréchet
derivative agrees with the chapter's scalar second directional derivative. -/
private theorem vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative
    {f : (ℝ × ℝ) → ℝ} {x h : ℝ × ℝ} (hf : ContDiffAt ℝ 3 f x) :
    vectorSecondDirectionalDerivative f x h = secondDirectionalDerivative f x h := by
  rw [secondDirectionalDerivative]
  symm
  simpa [directionalSlice] using
    (lineSliceIteratedDerivTwoEqVectorSecondDirectionalDerivative (f := f) (x := x) (h := h) hf)

/-- Helper for Theorem 5.4.7.4: the weighted geometric mean is the concave `C³` map required by
the cone-composition theorem on the orthant `powerConeQ1`. -/
private theorem powerConeGeometricMeanIsThreeTimesContDiffConcaveOnWith
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsThreeTimesContDiffConcaveOnWith
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
        exact vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative hcontAt
  have hgeom_nonneg : 0 ≤ powerConeGeometricMean α x := by
    -- The weighted geometric mean is nonnegative on the strict orthant.
    rw [show powerConeGeometricMean α x =
      Real.rpow x.1 α * Real.rpow x.2 (1 - α) by
      simpa using powerConeGeometricMean_apply α x.1 x.2]
    exact mul_nonneg (Real.rpow_nonneg hx₁.le α) (Real.rpow_nonneg hx₂.le (1 - α))
  rw [ConvexCone.mem_positive]
  -- Route correction: use the explicit second-derivative formula for `ξ[α]` and then rewrite
  -- the class field's within-domain derivative to that scalar directional derivative.
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
            -((-α * (1 - α) * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ)) * powerConeGeometricMean α x) := by
              ring
        _ = -secondDirectionalDerivative (powerConeGeometricMean α) x h := by
          exact
            (congrArg Neg.neg
              (powerConeGeometricMean_secondDirectionalDerivative
                (α := α) (x := x) (h := h) hx₁ hx₂)).symm
    _ =
        -iteratedFDerivWithin ℝ 2 (powerConeGeometricMean α) (interior powerConeQ1) x
          (fun _ ↦ h) := by
      rw [hiter]

/-- Helper for Theorem 5.4.7.4: the half-space `Q₂⁺ = {(y, z) | z ≤ y}` is convex. -/
private theorem qTwoPlusConvex : Convex ℝ (Q₂⁺ : Set (ℝ × ℝ)) := by
  -- Rewrite the goal into the scalar inequality on the second coordinate.
  intro x hx y hy a b ha hb hab
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rw [mem_qTwoPlus_iff] at hx hy ⊢
  have hineq : a * x₂ + b * y₂ ≤ a * x₁ + b * y₁ := by
    nlinarith
  simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    hineq

/-- Helper for Theorem 5.4.7.4: the half-space `Q₂⁺ = {(y, z) | z ≤ y}` is closed. -/
private theorem qTwoPlusIsClosed : IsClosed (Q₂⁺ : Set (ℝ × ℝ)) := by
  -- Rewrite the owner to the coordinate inequality cut out by continuous projections.
  simpa [qTwoPlus] using
    (isClosed_le continuous_snd continuous_fst : IsClosed {yz : ℝ × ℝ | yz.2 ≤ yz.1})

/-- Helper for Theorem 5.4.7.4: the strict half-space `interior Q₂⁺` is the affine preimage of
the positive ray under the slack map `(y, z) ↦ y - z`. -/
private theorem qTwoPlusInterior_eq_gapPreimageIoi :
    let gapLinear : (ℝ × ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ) - (ContinuousLinearMap.snd ℝ ℝ ℝ)
    let gapMap : (ℝ × ℝ) →ᴬ[ℝ] ℝ := gapLinear.toContinuousAffineMap
    gapMap ⁻¹' Set.Ioi (0 : ℝ) = interior Q₂⁺ := by
  let gapLinear : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ) - (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let gapMap : (ℝ × ℝ) →ᴬ[ℝ] ℝ := gapLinear.toContinuousAffineMap
  have hsurj : Function.Surjective gapLinear := by
    rintro t
    exact ⟨(t, 0), by simp [gapLinear]⟩
  -- Normalize the strict half-space once so the outer barrier proof can reuse the exact domain.
  calc
    gapMap ⁻¹' Set.Ioi (0 : ℝ) = gapLinear ⁻¹' interior (Set.Ici (0 : ℝ)) := by
      ext yz
      simp [gapMap, gapLinear]
    _ = interior (gapLinear ⁻¹' Set.Ici (0 : ℝ)) := by
      symm
      simpa using gapLinear.interior_preimage hsurj (Set.Ici (0 : ℝ))
    _ = interior Q₂⁺ := by
      congr 1
      ext yz
      rcases yz with ⟨y, z⟩
      rw [mem_qTwoPlus_iff]
      simp [gapLinear, sub_eq_add_neg]

/-- Helper for Theorem 5.4.7.4: the outer `Q₂⁺` logarithmic barrier has parameter `μ = 1`. -/
private theorem qTwoPlusSublevelLogBarrierIsOneSelfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (interior Q₂⁺)
      (1 : NNReal)
      powerConePlusOuterBarrier := by
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
    exact ⟨(t, 0), by simp [gapLinear]⟩
  have hdom : gapMap ⁻¹' Set.Ioi (0 : ℝ) = interior Q₂⁺ := by
    simpa [gapLinear, gapMap] using qTwoPlusInterior_eq_gapPreimageIoi
  have hfun :
      (fun yz : ℝ × ℝ ↦ -Real.log (yz.1 - yz.2)) = powerConePlusOuterBarrier := by
    funext yz
    rcases yz with ⟨y, z⟩
    -- Normalize the canonical sublevel barrier to the textbook logarithmic formula.
    rw [powerConePlusOuterBarrier, sublevelLogBarrier_apply]
    ring_nf
  simpa [hdom, hfun] using hpull

/-- Helper for Theorem 5.4.7.4: positive-cone directions preserve membership in `Q₂⁺`. -/
private theorem qTwoPlusPositiveRecession
    {s : ℝ} (hs : s ∈ (ConvexCone.positive ℝ ℝ : Set ℝ))
    {p : ℝ × ℝ} (hp : p ∈ Q₂⁺) (τ : ℝ) (hτ : 0 ≤ τ) :
    p + τ • (s, (0 : ℝ)) ∈ Q₂⁺ := by
  have hs' : 0 ≤ s := by
    simpa [ConvexCone.mem_positive] using hs
  rcases p with ⟨y, z⟩
  rw [mem_qTwoPlus_iff] at hp ⊢
  -- Adding nonnegative mass to the `y` coordinate preserves the half-space inequality.
  have hτs : 0 ≤ τ * s := mul_nonneg hτ hs'
  have hineq : z + τ * 0 ≤ y + τ * s := by
    simpa using add_le_add hp hτs
  simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hineq

/-- Helper for Theorem 5.4.7.4: restate the orthant logarithmic barrier in the chapter
`RealProdL2` pair ambient consumed by the generic cone-composition theorem. -/
private theorem powerConeBarrierIsTwoSelfConcordantBarrierL2 :
    @IsSelfConcordantBarrierOnWith
      (ℝ × ℝ)
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      (interior powerConeQ1)
      (2 : NNReal)
      powerConeBarrier := by
  -- The orthant barrier theorem already matches the current geometry once the owner is pinned.
  simpa using power_cone_barrier_is_two_self_concordant_barrier

/-- Helper for Theorem 5.4.7.4: restate the `β = 1` compatibility witness in the chapter
`RealProdL2` pair ambient consumed by the generic cone-composition theorem. -/
private theorem powerConeGeometricMeanIsOneCompatibleWithPowerConeBarrierL2
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    @IsBetaCompatibleWith
      (ℝ × ℝ)
      ℝ
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      Real.normedAddCommGroup
      RCLike.toInnerProductSpaceReal.toNormedSpace
      powerConeQ1
      (ConvexCone.positive ℝ ℝ)
      powerConeBarrier
      (1 : NNReal)
      (powerConeGeometricMean α) := by
  -- The compatibility theorem already has the right mathematics; this wrapper only pins the
  -- ambient geometry consumed by the specialization boundary.
  exact powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier hα₀ hα₁

/-- Helper for Theorem 5.4.7.4: pin the outer `Q₂⁺` barrier theorem to the current chapter
`RealProdL2` ambient before feeding it to the generic cone-composition theorem. -/
private theorem qTwoPlusOuterBarrierIsOneSelfConcordantBarrierL2 :
    IsSelfConcordantBarrierOnWith
      (interior Q₂⁺)
      (1 : NNReal)
      powerConePlusOuterBarrier := by
  -- The outer barrier theorem already has the right mathematics; this lemma freezes the current
  -- ambient geometry so the later specialization does not backtrack into the raw-product world.
  simpa using qTwoPlusSublevelLogBarrierIsOneSelfConcordantBarrier

-- Proof sketch: keep the heavy theorem application in this tiny support file, rewrite the target
-- to short aliases, and then specialize the chapter cone-composition theorem once.
/-- Helper for Theorem 5.4.7.4: the generic cone-composition theorem specializes to the
one-sided power-cone data with parameter `1 + 1^3 * 2`. -/
theorem coneCompositionBarrier_powerConePlusQTwoPlus_isSelfConcordantBarrierOnWith
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior
        (coneCompositionFeasibleSet
          powerConeQ1
          (ConvexCone.positive ℝ ℝ)
          (powerConeGeometricMean α)
          Q₂⁺))
      ((1 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
        (coneCompositionBarrier
        powerConeBarrier
        (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0)
        (powerConeGeometricMean α)
        1) := by
  have hξ :
      @IsThreeTimesContDiffConcaveOnWith
        (ℝ × ℝ)
        ℝ
        Chap05RealProdL2.instNormedAddCommGroupRealProd
        Chap05RealProdL2.instNormedSpaceRealProd
        Real.normedAddCommGroup
        RCLike.toInnerProductSpaceReal.toNormedSpace
        powerConeQ1
        (ConvexCone.positive ℝ ℝ)
        (powerConeGeometricMean α) :=
    powerConeGeometricMeanIsThreeTimesContDiffConcaveOnWith hα₀ hα₁
  have hβ :
      @IsBetaCompatibleWith
        (ℝ × ℝ)
        ℝ
        Chap05RealProdL2.instNormedAddCommGroupRealProd
        Chap05RealProdL2.instInnerProductSpaceRealProd
        Chap05RealProdL2.instCompleteSpaceRealProd
        Real.normedAddCommGroup
        RCLike.toInnerProductSpaceReal.toNormedSpace
        powerConeQ1
        (ConvexCone.positive ℝ ℝ)
        powerConeBarrier
        (1 : NNReal)
        (powerConeGeometricMean α) :=
    powerConeGeometricMeanIsOneCompatibleWithPowerConeBarrierL2 hα₀ hα₁
  have hF :
      IsSelfConcordantBarrierOnWith
        (interior powerConeQ1)
        (2 : NNReal)
        powerConeBarrier :=
    powerConeBarrierIsTwoSelfConcordantBarrierL2
  have hΦ :
      IsSelfConcordantBarrierOnWith
        (interior Q₂⁺)
        (1 : NNReal)
        powerConePlusOuterBarrier :=
    qTwoPlusOuterBarrierIsOneSelfConcordantBarrierL2
  -- Route correction: keep the specialization in the chapter `RealProdL2` owner world by
  -- passing the pair and triple ambient structures explicitly at the generic theorem boundary.
  have hSpecialized :
      IsSelfConcordantBarrierOnWith
        (interior (powerConePlusCoreSet α))
        ((1 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
        (powerConePlusCoreBarrier α) :=
    @coneCompositionBarrier_isSelfConcordantBarrierOnWith
      (ℝ × ℝ)
      ℝ
      ℝ
      _
      _
      _
      _
      _
      _
      _
      powerConeQ1
      Q₂⁺
      (ConvexCone.positive ℝ ℝ)
      powerConeBarrier
      powerConePlusOuterBarrier
      (powerConeGeometricMean α)
      (1 : NNReal)
      (1 : NNReal)
      (2 : NNReal)
      Chap05RealProdL2.instNormedAddCommGroupRealProdProd
      Chap05RealProdL2.instInnerProductSpaceRealProdProd
      Chap05RealProdL2.instCompleteSpaceRealProdProd
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      hξ
      hβ
      qTwoPlusIsClosed
      qTwoPlusConvex
      hF
      hΦ
      (fun {s} hs {p} hp τ hτ ↦ qTwoPlusPositiveRecession hs hp τ hτ)
  -- Rewrite the short aliases back to the explicit source-facing function spelling.
  simpa [powerConePlusCoreSet, powerConePlusCoreBarrier, powerConePlusOuterBarrier] using
    hSpecialized
