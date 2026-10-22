/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_3_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient HessianLocalNorm PowerConeGeometricMean

/- Theorem 5.4.7.2 lies in the Chapter 5 power-cone compatibility domain.

Sampled owner declarations:
* `powerConeGeometricMean`, `powerConeQ1`, and `powerConeBarrier` from `Definition_5_4_7_1`, the
  earlier source-facing power-cone data on raw pairs;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for compatibility;
* `Chap05RealProdL2.instInnerProductSpaceRealProd` from `RealProdL2`, the chapter owner bridge
  equipping the raw pair model `ℝ × ℝ` with the canonical Euclidean `L²` ambient structure;
* `entropyEpigraphRelativeEntropy_isOneCompatibleWith_powerConeBarrier` from
  `Theorem_5_4_7_6`, the nearby compatibility theorem on the same raw-pair orthant owner.

Source/core/bridge triage:
* source-facing: the `β = 1` compatibility theorem for the weighted geometric mean on `Q₁`;
* core/canonical: `IsBetaCompatibleWith` together with the raw-pair owners from
  `Definition_5_4_7_1`;
* bridge/view: the chapter `RealProdL2` owner activation that realizes the raw pair ambient
  structure through the canonical `L²` model.

Primitive data:
* the orthant `powerConeQ1`;
* the orthant barrier `powerConeBarrier`;
* the scalar cone `ConvexCone.positive ℝ ℝ`;
* the weighted geometric mean `ξ[α]`.

Derived API:
* the `β = 1` compatibility theorem below.

This file therefore reuses the raw-pair owners directly and keeps no parallel `WithLp` pullback
copy of the same compatibility statement. -/

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd

/-- Helper for Theorem 5.4.7.2: the orthant `powerConeQ1` is exactly the intersection of the two
coordinate half-spaces `x₁ ≥ 0` and `x₂ ≥ 0`. -/
lemma powerConeQ1_eq_coordinate_halfspaces :
    powerConeQ1 =
      {p : ℝ × ℝ | 0 ≤ p.1} ∩ {p : ℝ × ℝ | 0 ≤ p.2} := by
  ext p
  rcases p with ⟨x₁, x₂⟩
  -- Rewrite the source-facing orthant owner into the two coordinate inequalities.
  simpa [Set.mem_setOf_eq, Set.mem_inter_iff] using (mem_powerConeQ1_iff x₁ x₂)

/-- Helper for Theorem 5.4.7.2: the interior of `powerConeQ1` is the strict positive orthant
`x₁ > 0`, `x₂ > 0`. -/
lemma mem_interior_powerConeQ1_iff (x₁ x₂ : ℝ) :
    (x₁, x₂) ∈ interior powerConeQ1 ↔ 0 < x₁ ∧ 0 < x₂ := by
  have hfst :
      interior {p : ℝ × ℝ | 0 ≤ p.1} = {p : ℝ × ℝ | 0 < p.1} := by
    calc
      interior {p : ℝ × ℝ | 0 ≤ p.1}
          = interior ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ici (0 : ℝ)) := by
              rfl
      _ = (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' interior (Set.Ici (0 : ℝ)) := by
            symm
            exact
              isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst (Set.Ici (0 : ℝ))
      _ = {p : ℝ × ℝ | 0 < p.1} := by
            ext p
            simp
  have hsnd :
      interior {p : ℝ × ℝ | 0 ≤ p.2} = {p : ℝ × ℝ | 0 < p.2} := by
    calc
      interior {p : ℝ × ℝ | 0 ≤ p.2}
          = interior ((Prod.snd : ℝ × ℝ → ℝ) ⁻¹' Set.Ici (0 : ℝ)) := by
              rfl
      _ = (Prod.snd : ℝ × ℝ → ℝ) ⁻¹' interior (Set.Ici (0 : ℝ)) := by
            symm
            exact
              isOpenMap_snd.preimage_interior_eq_interior_preimage continuous_snd (Set.Ici (0 : ℝ))
      _ = {p : ℝ × ℝ | 0 < p.2} := by
            ext p
            simp
  -- Rewrite the orthant interior through the coordinate-halfspace normal form.
  rw [powerConeQ1_eq_coordinate_halfspaces, interior_inter, hfst, hsnd]
  simp [Set.mem_setOf_eq, Set.mem_inter_iff]

/-- Helper for Theorem 5.4.7.2: the orthant domain `powerConeQ1` is convex. -/
lemma powerConeQ1_convex : Convex ℝ (powerConeQ1 : Set (ℝ × ℝ)) := by
  have hfst : Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1} := by
    -- Each coordinate half-space is the linear preimage of the convex ray `[0, ∞)`.
    simpa using
      (convex_Ici (0 : ℝ)).linear_preimage (ContinuousLinearMap.fst ℝ ℝ ℝ).toLinearMap
  have hsnd : Convex ℝ {p : ℝ × ℝ | 0 ≤ p.2} := by
    -- The same argument applies to the second coordinate.
    simpa using
      (convex_Ici (0 : ℝ)).linear_preimage (ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap
  rw [powerConeQ1_eq_coordinate_halfspaces]
  exact hfst.inter hsnd

/-- Helper for Theorem 5.4.7.2: the affine line `t ↦ x + t • h` in `ℝ × ℝ` has derivative `h`. -/
private theorem affineLineHasDerivAt
    {x h : ℝ × ℝ} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const h).const_add x

/-- Helper for Theorem 5.4.7.2: the affine line has vanishing second iterated derivative. -/
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

/-- Helper for Theorem 5.4.7.2: the affine line has vanishing third iterated derivative. -/
private theorem affineLineIteratedDerivThree
    {x h : ℝ × ℝ} :
    iteratedDeriv 3 (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ (0 : ℝ × ℝ) := by
  -- Once the second iterated derivative is zero, one more derivative stays zero.
  funext t
  rw [iteratedDeriv_succ, affineLineIteratedDerivTwo, deriv_const]

/-- Helper for Theorem 5.4.7.2: the second derivative of the line slice of `f` is the packaged
repeated second Fréchet derivative `vectorSecondDirectionalDerivative f x h`. -/
private theorem lineSlice_iteratedDerivTwo_eq_vectorSecondDirectionalDerivative
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

/-- Helper for Theorem 5.4.7.2: the third derivative of the line slice of `f` is the packaged
repeated third Fréchet derivative `vectorThirdDirectionalDerivative f x h`. -/
private theorem lineSlice_iteratedDerivThree_eq_vectorThirdDirectionalDerivative
    {f : (ℝ × ℝ) → ℝ} {x h : ℝ × ℝ} (hf : ContDiffAt ℝ 3 f x) :
    iteratedDeriv 3 (fun s : ℝ ↦ f (x + s • h)) 0 =
      vectorThirdDirectionalDerivative f x h := by
  let line : ℝ → ℝ × ℝ := fun s ↦ x + s • h
  have hline₃ : ContDiffAt ℝ 3 line 0 := by
    fun_prop
  -- The cubic chain rule collapses because every higher derivative of the affine line vanishes.
  have hcomp :=
    iteratedDeriv_vcomp_three (g := f) (f := line) (x := 0) (by simpa [line] using hf) hline₃
  have hline_deriv : deriv line 0 = h := by
    simpa [line] using (affineLineHasDerivAt (x := x) (h := h) 0).deriv
  have hzero_left : iteratedFDeriv ℝ 2 f x ![(0 : ℝ × ℝ), h] = 0 := by
    exact (iteratedFDeriv ℝ 2 f x).map_coord_zero 0 rfl
  have hzero_right : iteratedFDeriv ℝ 2 f x ![h, (0 : ℝ × ℝ)] = 0 := by
    exact (iteratedFDeriv ℝ 2 f x).map_coord_zero 1 rfl
  calc
    iteratedDeriv 3 (fun s : ℝ ↦ f (x + s • h)) 0
        = iteratedFDeriv ℝ 3 f x (fun _ ↦ h) +
            iteratedFDeriv ℝ 2 f x ![(0 : ℝ × ℝ), h] +
            2 • iteratedFDeriv ℝ 2 f x ![h, (0 : ℝ × ℝ)] := by
              simpa [line, Function.comp, hline_deriv, affineLineIteratedDerivTwo,
                affineLineIteratedDerivThree] using hcomp
    _ = vectorThirdDirectionalDerivative f x h := by
          simp [hzero_left, hzero_right, vectorThirdDirectionalDerivative]

/-- Helper for Theorem 5.4.7.2: the orthant barrier `F(x) = -log x₁ - log x₂` is the sum of the
two coordinate pullbacks of the scalar `-log` barrier, so it has barrier parameter `ν = 2` on
`interior powerConeQ1`. -/
lemma power_cone_barrier_is_two_self_concordant_barrier :
    IsSelfConcordantBarrierOnWith (interior powerConeQ1) (2 : NNReal) powerConeBarrier := by
  let fstMap : (ℝ × ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let sndMap : (ℝ × ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hfst :
      IsSelfConcordantBarrierOnWith
        (fstMap ⁻¹' Set.Ioi (0 : ℝ))
        1
        (fun p : ℝ × ℝ ↦ -Real.log p.1) := by
    -- Pull back the scalar `-log` barrier along the first-coordinate projection.
    simpa [fstMap, Function.comp] using
      (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap fstMap)
  have hsnd :
      IsSelfConcordantBarrierOnWith
        (sndMap ⁻¹' Set.Ioi (0 : ℝ))
        1
        (fun p : ℝ × ℝ ↦ -Real.log p.2) := by
    -- Pull back the same scalar barrier along the second-coordinate projection.
    simpa [sndMap, Function.comp] using
      (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap sndMap)
  have hdom :
      (fstMap ⁻¹' Set.Ioi (0 : ℝ)) ∩ (sndMap ⁻¹' Set.Ioi (0 : ℝ)) =
        interior powerConeQ1 := by
    ext p
    rcases p with ⟨x₁, x₂⟩
    -- The orthant interior is exactly the conjunction of the two strict coordinate inequalities.
    simpa [fstMap, sndMap] using (mem_interior_powerConeQ1_iff x₁ x₂).symm
  have hfun :
      (fun p : ℝ × ℝ ↦ -Real.log p.1) + (fun p : ℝ × ℝ ↦ -Real.log p.2) =
        powerConeBarrier := by
    funext p
    rcases p with ⟨x₁, x₂⟩
    -- Rewrite the pulled-back sum to the source-facing orthant barrier formula.
    simpa [Pi.add_apply] using (powerConeBarrier_apply x₁ x₂).symm
  have hparam : (1 : NNReal) + 1 = 2 := by
    norm_num
  simpa [hdom, hfun, hparam] using hfst.add hsnd

/-- Helper for Theorem 5.4.7.2: the weighted geometric mean is `C³` on the strict orthant
`interior powerConeQ1`. -/
lemma powerConeGeometricMean_contDiffOn_interior (α : ℝ) :
    ContDiffOn ℝ 3 (powerConeGeometricMean α) (interior powerConeQ1) := by
  have hfst : ContDiffOn ℝ 3 (Prod.fst : ℝ × ℝ → ℝ) (interior powerConeQ1) := by
    intro x hx
    have hfstAt : ContDiffAt ℝ 3 (Prod.fst : ℝ × ℝ → ℝ) x := by
      simpa using
        (ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ ℝ ℝ)).contDiffAt
    exact hfstAt.contDiffWithinAt
  have hsnd : ContDiffOn ℝ 3 (Prod.snd : ℝ × ℝ → ℝ) (interior powerConeQ1) := by
    intro x hx
    have hsndAt : ContDiffAt ℝ 3 (Prod.snd : ℝ × ℝ → ℝ) x := by
      simpa using
        (ContinuousLinearMap.contDiff (ContinuousLinearMap.snd ℝ ℝ ℝ)).contDiffAt
    exact hsndAt.contDiffWithinAt
  have hfstPow : ContDiffOn ℝ 3 (fun x : ℝ × ℝ ↦ Real.rpow x.1 α) (interior powerConeQ1) := by
    -- On the interior, the first coordinate never vanishes, so `x₁ ↦ x₁^α` is `C³`.
    exact hfst.rpow_const_of_ne fun x hx ↦
      (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.1.ne'
  have hsndPow :
      ContDiffOn ℝ 3 (fun x : ℝ × ℝ ↦ Real.rpow x.2 (1 - α)) (interior powerConeQ1) := by
    -- The same nonvanishing argument applies to the second coordinate.
    exact hsnd.rpow_const_of_ne fun x hx ↦
      (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.2.ne'
  -- Multiply the two coordinate power factors to recover the weighted geometric mean.
  simpa [powerConeGeometricMean_apply] using hfstPow.mul hsndPow

/-- Helper for Theorem 5.4.7.2: at a positive point, the scalar `-log` barrier has second
directional derivative `u² / x²`. -/
lemma negLog_secondDirectionalDerivative_eq_sq_div_sq {x u : ℝ} (hx : 0 < x) :
    secondDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u = u ^ (2 : ℕ) / x ^ (2 : ℕ) := by
  have hcont : ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y) x := by
    -- Positive points stay away from the logarithmic singularity.
    simpa using (Real.contDiffAt_log.2 hx.ne').neg
  have hdiff : DifferentiableAt ℝ (fun y : ℝ ↦ -Real.log y) x :=
    hcont.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ fun y : ℝ ↦ -Real.log y) x :=
    differentiableAt_gradient_of_contDiffAt_two hcont
  -- Transport the scalar Hessian formula back to the chapter's second directional derivative.
  calc
    secondDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u =
        inner ℝ u (hessian (fun y : ℝ ↦ -Real.log y) x u) := by
          exact secondDirectionalDerivative_eq_hessian_quadratic_form hcont
    _ = u ^ (2 : ℕ) / x ^ (2 : ℕ) := by
          simpa using negLog_hessian_quadratic_form_eq (x := x) (u := u) hx

/-- Helper for Theorem 5.4.7.2: the second directional derivative of the orthant barrier is the
sum of the two scaled coordinate squares. -/
lemma powerConeBarrier_secondDirectionalDerivative_eq
    {x h : ℝ × ℝ} (hx : x ∈ interior powerConeQ1) :
    secondDirectionalDerivative powerConeBarrier x h =
      (h.1 / x.1) ^ (2 : ℕ) + (h.2 / x.2) ^ (2 : ℕ) := by
  have hx₁ : 0 < x.1 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.1
  have hx₂ : 0 < x.2 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.2
  have hslice₁ : ContDiffAt ℝ 2 (directionalSlice (fun y : ℝ ↦ -Real.log y) x.1 h.1) 0 := by
    -- The first coordinate slice is an affine pullback of the scalar `-log` barrier.
    have hcont : ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y) x.1 := by
      simpa using (Real.contDiffAt_log.2 hx₁.ne').neg
    have hcont0 : ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y) (x.1 + 0 * h.1) := by
      simpa using hcont
    have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ x.1 + t * h.1) 0 := by
      fun_prop
    simpa [directionalSlice, smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_comm,
      mul_left_comm, mul_assoc] using
      hcont0.comp 0 hline
  have hslice₂ : ContDiffAt ℝ 2 (directionalSlice (fun y : ℝ ↦ -Real.log y) x.2 h.2) 0 := by
    -- The same affine-pullback argument handles the second coordinate.
    have hcont : ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y) x.2 := by
      simpa using (Real.contDiffAt_log.2 hx₂.ne').neg
    have hcont0 : ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y) (x.2 + 0 * h.2) := by
      simpa using hcont
    have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ x.2 + t * h.2) 0 := by
      fun_prop
    simpa [directionalSlice, smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_comm,
      mul_left_comm, mul_assoc] using
      hcont0.comp 0 hline
  have hslice :
      directionalSlice powerConeBarrier x h =
        directionalSlice (fun y : ℝ ↦ -Real.log y) x.1 h.1 +
          directionalSlice (fun y : ℝ ↦ -Real.log y) x.2 h.2 := by
    funext t
    -- Unfold the source-facing barrier formula on the affine line `x + t h`.
    rw [directionalSlice, powerConeBarrier_apply]
    simpa [directionalSlice, smul_eq_mul, sub_eq_add_neg]
  -- Differentiate the slice sum coordinatewise and use the scalar `-log` second-derivative formula.
  rw [secondDirectionalDerivative, hslice, iteratedDeriv_add hslice₁ hslice₂]
  have hsq₁ :
      iteratedDeriv 2 (directionalSlice (fun y : ℝ ↦ -Real.log y) x.1 h.1) 0 =
        (h.1 / x.1) ^ (2 : ℕ) := by
    simpa [secondDirectionalDerivative, ← div_pow] using
      negLog_secondDirectionalDerivative_eq_sq_div_sq (x := x.1) (u := h.1) hx₁
  have hsq₂ :
      iteratedDeriv 2 (directionalSlice (fun y : ℝ ↦ -Real.log y) x.2 h.2) 0 =
        (h.2 / x.2) ^ (2 : ℕ) := by
    simpa [secondDirectionalDerivative, ← div_pow] using
      negLog_secondDirectionalDerivative_eq_sq_div_sq (x := x.2) (u := h.2) hx₂
  rw [hsq₁, hsq₂]

/-- Helper for Theorem 5.4.7.2: the orthant barrier local norm is the Euclidean norm of the
scaled direction coordinates. -/
lemma powerConeBarrier_local_norm_eq
    {x h : ℝ × ℝ} (hx : x ∈ interior powerConeQ1) :
    ‖h‖[powerConeBarrier; x] =
      Real.sqrt ((h.1 / x.1) ^ (2 : ℕ) + (h.2 / x.2) ^ (2 : ℕ)) := by
  have hcontAt : ContDiffAt ℝ 3 powerConeBarrier x := by
    -- The barrier instance already packages the needed interior smoothness.
    have hcontWithin :
        ContDiffWithinAt ℝ 3 powerConeBarrier (interior powerConeQ1) x :=
      power_cone_barrier_is_two_self_concordant_barrier.toIsStandardSelfConcordantOn.contDiffOn x hx
    exact hcontWithin.contDiffAt (isOpen_interior.mem_nhds hx)
  have hdiff : DifferentiableAt ℝ powerConeBarrier x := hcontAt.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ powerConeBarrier) x := by
    exact
      differentiableAt_gradient_of_contDiffAt_two
        (hcontAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  -- Route correction: compute the local norm via the explicit second directional derivative of the
  -- barrier, then identify that quadratic form with the Hessian local norm owner.
  rw [hessianLocalNorm_def]
  rw [← secondDirectionalDerivative_eq_hessian_quadratic_form
    (hcontAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))]
  rw [powerConeBarrier_secondDirectionalDerivative_eq hx]

/-- Helper for Theorem 5.4.7.2: the compatibility inequality for `ξ[α]` reduces to a scalar
nonnegativity estimate on the strict orthant. -/
lemma powerConeGeometricMean_compatibility_bound
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    {x : ℝ × ℝ} (hx : x ∈ interior powerConeQ1) (h : ℝ × ℝ) :
    (3 * ‖h‖[powerConeBarrier; x]) • (-vectorSecondDirectionalDerivative ξ[α] x h) -
      vectorThirdDirectionalDerivative ξ[α] x h ∈ ConvexCone.positive ℝ ℝ := by
  have hx₁ : 0 < x.1 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.1
  have hx₂ : 0 < x.2 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.2
  have hcontAt : ContDiffAt ℝ 3 ξ[α] x := by
    exact (powerConeGeometricMean_contDiffOn_interior α).contDiffAt (isOpen_interior.mem_nhds hx)
  have h2 :
      vectorSecondDirectionalDerivative ξ[α] x h = secondDirectionalDerivative ξ[α] x h := by
    rw [secondDirectionalDerivative]
    symm
    simpa [directionalSlice] using
      (lineSlice_iteratedDerivTwo_eq_vectorSecondDirectionalDerivative
        (f := ξ[α]) (x := x) (h := h) hcontAt)
  have h3 :
      vectorThirdDirectionalDerivative ξ[α] x h = thirdDirectionalDerivative ξ[α] x h := by
    rw [thirdDirectionalDerivative]
    symm
    simpa [directionalSlice] using
      (lineSlice_iteratedDerivThree_eq_vectorThirdDirectionalDerivative
        (f := ξ[α]) (x := x) (h := h) hcontAt)
  let a : ℝ := h.1 / x.1
  let b : ℝ := h.2 / x.2
  let L : ℝ := (2 - α) * a + (1 + α) * b
  let S : ℝ := a ^ (2 : ℕ) + b ^ (2 : ℕ)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (sq_nonneg a) (sq_nonneg b)
  have hnorm_eq : ‖h‖[powerConeBarrier; x] = Real.sqrt S := by
    -- Rewrite the barrier local norm into the scaled-coordinate Euclidean norm.
    rw [powerConeBarrier_local_norm_eq hx]

  have hξ_pos : 0 < ξ[α] x := by
    -- The weighted geometric mean is strictly positive on the strict orthant.
    rw [show ξ[α] x = Real.rpow x.1 α * Real.rpow x.2 (1 - α) by
      simpa using powerConeGeometricMean_apply α x.1 x.2]
    exact mul_pos (Real.rpow_pos_of_pos hx₁ α) (Real.rpow_pos_of_pos hx₂ (1 - α))
  have hs_nonneg : 0 ≤ -secondDirectionalDerivative ξ[α] x h := by
    -- The explicit second-derivative formula is a nonnegative multiple of `ξ[α] x`.
    have hsecond_eq :
        secondDirectionalDerivative ξ[α] x h =
          (-α * (1 - α) * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ)) * ξ[α] x :=
      powerConeGeometricMean_secondDirectionalDerivative (α := α) (x := x) (h := h) hx₁ hx₂
    rw [hsecond_eq]
    have hα : 0 ≤ α := le_of_lt hα₀
    have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα₁.le
    have hsquare : 0 ≤ (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ) := sq_nonneg _
    have hfactor : 0 ≤ α * (1 - α) * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ) := by
      exact mul_nonneg (mul_nonneg hα h1α) hsquare
    have hgeom : 0 ≤ ξ[α] x := hξ_pos.le
    nlinarith [mul_nonneg hfactor hgeom]
  have hLsq :
      L ^ (2 : ℕ) ≤ ((2 - α) ^ (2 : ℕ) + (1 + α) ^ (2 : ℕ)) * S := by
    -- This is the two-dimensional Cauchy--Schwarz inequality after expansion.
    dsimp [L, S]
    nlinarith [sq_nonneg ((1 + α) * a - (2 - α) * b)]
  have hcoeff_bound : (2 - α) ^ (2 : ℕ) + (1 + α) ^ (2 : ℕ) ≤ 9 := by
    -- The coefficient norm is uniformly bounded by `3` when `0 < α < 1`.
    nlinarith [le_of_lt hα₀, hα₁.le]
  have habsL : |L| ≤ 3 * Real.sqrt S := by
    have hsq : (abs L) ^ (2 : ℕ) ≤ (3 * Real.sqrt S) ^ (2 : ℕ) := by
      have hsq' : L ^ (2 : ℕ) ≤ (3 : ℝ) ^ (2 : ℕ) * S := by
        nlinarith [hLsq, hcoeff_bound]
      have hthree : (3 : ℝ) ^ (2 : ℕ) * S = (3 * Real.sqrt S) ^ (2 : ℕ) := by
        rw [show (3 : ℝ) ^ (2 : ℕ) = 9 by norm_num,
          show (3 * Real.sqrt S) ^ (2 : ℕ) = 9 * (Real.sqrt S) ^ (2 : ℕ) by ring]
        rw [Real.sq_sqrt hS_nonneg]
      simpa [sq_abs, hthree] using hsq'
    have habs_nonneg : 0 ≤ |L| := abs_nonneg L
    have hright_nonneg : 0 ≤ 3 * Real.sqrt S := by
      positivity
    nlinarith
  have hL_le : L ≤ 3 * Real.sqrt S := le_trans (le_abs_self L) habsL
  rw [ConvexCone.mem_positive]
  -- Rewrite the abstract compatibility bound into the scalar factorization
  -- `(-D²ξ) * (3 ‖h‖[F; x] - L)`.
  rw [h2, h3]
  have hthird_eq :
      thirdDirectionalDerivative ξ[α] x h =
        -secondDirectionalDerivative ξ[α] x h *
          ((2 - α) * (h.1 / x.1) + (1 + α) * (h.2 / x.2)) :=
    powerConeGeometricMean_thirdDirectionalDerivative (α := α) (x := x) (h := h) hx₁ hx₂
  rw [hthird_eq, hnorm_eq]
  simp only [smul_eq_mul]
  rw [show ((2 - α) * (h.1 / x.1) + (1 + α) * (h.2 / x.2)) = L by rfl]
  nlinarith

-- Proof sketch: use the explicit formula for `D³ξ(x)[h,h,h]` in terms of `-D²ξ(x)[h,h]`, and
-- compute `hessianLocalNorm powerConeBarrier x h` as
-- `((h.1 / x.1)^2 + (h.2 / x.2)^2)^(1/2)` on the positive orthant. Cauchy--Schwarz then bounds
-- the linear factor `((2 - α) (h.1 / x.1) + (1 + α) (h.2 / x.2))` by
-- `3 * hessianLocalNorm powerConeBarrier x h` when `0 < α < 1`, yielding the defining cone-order
-- inequality in the positive cone of `ℝ`.
/-- Theorem 5.4.7.2: for `0 < α < 1`, the weighted geometric mean
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` is `1`-compatible with the logarithmic barrier
`F(x) = -log x^(1) - log x^(2)` on the orthant `Q₁ = ℝ_+²`, relative to the scalar cone
`ℝ_+`. -/
theorem powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsBetaCompatibleWith powerConeQ1 (ConvexCone.positive ℝ ℝ)
      powerConeBarrier (1 : NNReal) ξ[α] := by
  refine
    { convex_domain := powerConeQ1_convex
      interior_nonempty := ?_
      one_le_parameter := ?_
      selfConcordantBarrier := ?_
      contDiffOn := powerConeGeometricMean_contDiffOn_interior α
      compatibility_bound := ?_ }
  · -- The strict orthant contains `(1, 1)`.
    refine ⟨(1, 1), ?_⟩
    exact (mem_interior_powerConeQ1_iff 1 1).2 ⟨zero_lt_one, zero_lt_one⟩
  · -- The target compatibility parameter is exactly `β = 1`.
    simp
  · -- The orthant barrier is the sum of two scalar `-log` barriers, hence has parameter `2`.
    exact ⟨2, power_cone_barrier_is_two_self_concordant_barrier⟩
  · -- The remaining field is precisely the explicit scalar compatibility inequality.
    intro x hx h
    simpa using powerConeGeometricMean_compatibility_bound hα₀ hα₁ hx h
