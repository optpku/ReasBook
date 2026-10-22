/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_3_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_2

noncomputable section

open scoped EntropyEpigraph Gradient HessianLocalNorm

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

section ScalarAffineTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Theorem 5.4.7.6: the affine line in an arbitrary normed space has derivative equal
to its direction vector. -/
private theorem affineLineHasDerivAt_generic
    {x h : E} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const h).const_add x

/-- Helper for Theorem 5.4.7.6: the affine line has vanishing second iterated derivative in every
normed space. -/
private theorem affineLineIteratedDerivTwo_generic
    {x h : E} :
    iteratedDeriv 2 (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ (0 : E) := by
  -- Differentiate the affine line once to a constant, then differentiate that constant again.
  funext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ h := by
    funext s
    exact (affineLineHasDerivAt_generic (x := x) (h := h) s).deriv
  rw [hderiv, deriv_const]

/-- Helper for Theorem 5.4.7.6: the affine line has vanishing third iterated derivative in every
normed space. -/
private theorem affineLineIteratedDerivThree_generic
    {x h : E} :
    iteratedDeriv 3 (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ (0 : E) := by
  -- Once the second iterated derivative is zero, one more derivative stays zero.
  funext t
  rw [iteratedDeriv_succ, affineLineIteratedDerivTwo_generic, deriv_const]

/-- Helper for Theorem 5.4.7.6: for scalar maps on any normed domain, the packaged repeated second
Fréchet derivative agrees with the scalar second directional derivative. -/
private theorem vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative_of_contDiffAt
    {f : E → ℝ} {x h : E} (hf : ContDiffAt ℝ 3 f x) :
    vectorSecondDirectionalDerivative f x h = secondDirectionalDerivative f x h := by
  let line : ℝ → E := fun s ↦ x + s • h
  have hf₂ : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hline₂ : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  -- The quadratic chain rule collapses because the affine line has zero second derivative.
  have hcomp :=
    iteratedDeriv_vcomp_two (g := f) (f := line) (x := 0) (by simpa [line] using hf₂) hline₂
  have hline_deriv : deriv line 0 = h := by
    simpa [line] using (affineLineHasDerivAt_generic (x := x) (h := h) 0).deriv
  rw [secondDirectionalDerivative]
  symm
  simpa [line, directionalSlice, Function.comp, hline_deriv, affineLineIteratedDerivTwo_generic,
    vectorSecondDirectionalDerivative] using hcomp

/-- Helper for Theorem 5.4.7.6: for scalar maps on any normed domain, the packaged repeated third
Fréchet derivative agrees with the scalar third directional derivative. -/
private theorem vectorThirdDirectionalDerivative_eq_thirdDirectionalDerivative_of_contDiffAt
    {f : E → ℝ} {x h : E} (hf : ContDiffAt ℝ 3 f x) :
    vectorThirdDirectionalDerivative f x h = thirdDirectionalDerivative f x h := by
  let line : ℝ → E := fun s ↦ x + s • h
  have hline₃ : ContDiffAt ℝ 3 line 0 := by
    fun_prop
  -- The cubic chain rule collapses because every higher derivative of the affine line vanishes.
  have hcomp :=
    iteratedDeriv_vcomp_three (g := f) (f := line) (x := 0) (by simpa [line] using hf) hline₃
  have hline_deriv : deriv line 0 = h := by
    simpa [line] using (affineLineHasDerivAt_generic (x := x) (h := h) 0).deriv
  have hzero_left : iteratedFDeriv ℝ 2 f x ![(0 : E), h] = 0 := by
    exact (iteratedFDeriv ℝ 2 f x).map_coord_zero 0 rfl
  have hzero_right : iteratedFDeriv ℝ 2 f x ![h, (0 : E)] = 0 := by
    exact (iteratedFDeriv ℝ 2 f x).map_coord_zero 1 rfl
  rw [thirdDirectionalDerivative]
  symm
  calc
    iteratedDeriv 3 (fun s : ℝ ↦ f (x + s • h)) 0
        = iteratedFDeriv ℝ 3 f x (fun _ ↦ h) +
            iteratedFDeriv ℝ 2 f x ![(0 : E), h] +
            2 • iteratedFDeriv ℝ 2 f x ![h, (0 : E)] := by
              simpa [line, directionalSlice, Function.comp, hline_deriv,
                affineLineIteratedDerivTwo_generic, affineLineIteratedDerivThree_generic] using
                hcomp
    _ = vectorThirdDirectionalDerivative f x h := by
          simp [hzero_left, hzero_right, vectorThirdDirectionalDerivative]

end ScalarAffineTransport

/-- Helper for Theorem 5.4.7.6: continuous affine pullbacks rewrite the directional slice by
acting on the base point and direction through the affine map. -/
private theorem directionalSlice_comp_affine_generic
    {E : Type*} {E₁ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    (f : E₁ → ℝ) (g : E →ᴬ[ℝ] E₁) (x u : E) :
    directionalSlice (f ∘ g) x u = directionalSlice f (g x) (g.contLinear u) := by
  funext t
  -- Expand the affine update once so both slices become definitionally identical.
  simpa [directionalSlice, vadd_eq_add, add_comm, add_left_comm, add_assoc] using
    congrArg f (g.map_vadd x (t • u))

/-- Helper for Theorem 5.4.7.6: continuous affine pullbacks preserve scalar second directional
derivatives. -/
private theorem secondDirectionalDerivative_comp_affine
    {E : Type*} {E₁ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    (f : E₁ → ℝ) (g : E →ᴬ[ℝ] E₁) (x u : E) :
    secondDirectionalDerivative (f ∘ g) x u =
      secondDirectionalDerivative f (g x) (g.contLinear u) := by
  simp [secondDirectionalDerivative, directionalSlice_comp_affine_generic]

/-- Helper for Theorem 5.4.7.6: a self-concordant function can be transferred across functions
that agree on the open self-concordant domain. -/
private theorem selfConcordantOnWith_congrEqOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {dom : Set E} {Mf : NNReal} {F G : E → ℝ}
    (h : IsSelfConcordantOnWith dom Mf F) (hEq : Set.EqOn F G dom) :
    IsSelfConcordantOnWith dom Mf G := by
  refine
    { isOpen_domain := h.isOpen_domain
      contDiffOn := (contDiffOn_congr fun x hx ↦ (hEq hx).symm).2 h.contDiffOn
      convexOn := h.convexOn.congr hEq
      third_deriv_bound := ?_ }
  intro x hx u
  have hEqAt : G =ᶠ[nhds x] F := by
    refine Filter.mem_of_superset (h.isOpen_domain.mem_nhds hx) ?_
    intro y hy
    exact (hEq hy).symm
  have hFcontAt : ContDiffAt ℝ 3 F x :=
    h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hGcontAt : ContDiffAt ℝ 3 G x :=
    hFcontAt.congr_of_eventuallyEq hEqAt
  -- Rewrite the cubic derivative and Hessian local norm through neighborhood equality.
  have hthird :
      thirdDirectionalDerivative G x u = thirdDirectionalDerivative F x u := by
    have hiter : iteratedFDeriv ℝ 3 G x = iteratedFDeriv ℝ 3 F x :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hEqAt 3).eq_of_nhds
    simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hGcontAt,
      thirdDirectionalDerivative_eq_iteratedFDeriv hFcontAt] using
      congrArg (fun A ↦ A fun _ ↦ u) hiter
  have hhess : hessian G x = hessian F x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  have hnorm : hessianLocalNorm G x u = hessianLocalNorm F x u := by
    simp [hessianLocalNorm_def, hhess]
  calc
    |thirdDirectionalDerivative G x u| = |thirdDirectionalDerivative F x u| := by
      rw [hthird]
    _ ≤ 2 * (Mf : ℝ) * hessianLocalNorm F x u ^ (3 : ℕ) := h.third_deriv_bound hx u
    _ = 2 * (Mf : ℝ) * hessianLocalNorm G x u ^ (3 : ℕ) := by
      rw [hnorm]

/-- Helper for Theorem 5.4.7.6: a self-concordant barrier can be transferred across functions
that agree on the open barrier domain. -/
private theorem barrierCongrEqOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {dom : Set E} {ν : NNReal} {F G : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν F) (hEq : Set.EqOn F G dom) :
    IsSelfConcordantBarrierOnWith dom ν G := by
  refine
    { toIsStandardSelfConcordantOn := by
        simpa using selfConcordantOnWith_congrEqOn h.toIsStandardSelfConcordantOn hEq
      barrier_parameter_bound := ?_ }
  intro x hx u
  have hEqAt : G =ᶠ[nhds x] F := by
    refine Filter.mem_of_superset (h.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hx) ?_
    intro y hy
    exact (hEq hy).symm
  -- Rewrite the barrier parameter inequality through the neighborhood equality on the open domain.
  have hgrad : ∇ G x = ∇ F x := hEqAt.gradient_eq
  have hhess : hessian G x = hessian F x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  simpa [hgrad, hhess] using h.barrier_parameter_bound hx u

-- Route correction: move the stable entropy derivative and compatibility API into a theorem-local
-- support file so the raw cone-composition specialization can import it without an owner cycle.
/-- Helper for Theorem 5.4.7.6: the strict orthant `powerConeQ1` is closed. -/
private theorem powerConeQ1IsClosed : IsClosed (powerConeQ1 : Set (ℝ × ℝ)) := by
  have hfst : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hsnd : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} :=
    isClosed_le continuous_const continuous_snd
  -- Rewrite the orthant owner to the two coordinate half-spaces.
  rw [powerConeQ1_eq_coordinate_halfspaces]
  exact hfst.inter hsnd

/-- Helper for Theorem 5.4.7.6: the affine line `t ↦ x + t • h` in `ℝ × ℝ` has derivative `h`. -/
private theorem affineLineHasDerivAt
    {x h : ℝ × ℝ} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const h).const_add x

/-- Helper for Theorem 5.4.7.6: the affine line has vanishing second iterated derivative. -/
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

/-- Helper for Theorem 5.4.7.6: the affine line has vanishing third iterated derivative. -/
private theorem affineLineIteratedDerivThree
    {x h : ℝ × ℝ} :
    iteratedDeriv 3 (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ (0 : ℝ × ℝ) := by
  -- Once the second iterated derivative is zero, one more derivative stays zero.
  funext t
  rw [iteratedDeriv_succ, affineLineIteratedDerivTwo, deriv_const]

/-- Helper for Theorem 5.4.7.6: the second derivative of the line slice of `f` is the packaged
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

/-- Helper for Theorem 5.4.7.6: the third derivative of the line slice of `f` is the packaged
repeated third Fréchet derivative `vectorThirdDirectionalDerivative f x h`. -/
private theorem lineSliceIteratedDerivThreeEqVectorThirdDirectionalDerivative
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

/-- Helper for Theorem 5.4.7.6: for scalar maps on `ℝ × ℝ`, the repeated second Fréchet
derivative agrees with the chapter's scalar second directional derivative. -/
private theorem vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative
    {f : (ℝ × ℝ) → ℝ} {x h : ℝ × ℝ} (hf : ContDiffAt ℝ 3 f x) :
    vectorSecondDirectionalDerivative f x h = secondDirectionalDerivative f x h := by
  rw [secondDirectionalDerivative]
  symm
  simpa [directionalSlice] using
    (lineSliceIteratedDerivTwoEqVectorSecondDirectionalDerivative (f := f) (x := x) (h := h) hf)

/-- Helper for Theorem 5.4.7.6: for scalar maps on `ℝ × ℝ`, the repeated third Fréchet
derivative agrees with the chapter's scalar third directional derivative. -/
private theorem vectorThirdDirectionalDerivative_eq_thirdDirectionalDerivative
    {f : (ℝ × ℝ) → ℝ} {x h : ℝ × ℝ} (hf : ContDiffAt ℝ 3 f x) :
    vectorThirdDirectionalDerivative f x h = thirdDirectionalDerivative f x h := by
  rw [thirdDirectionalDerivative]
  symm
  simpa [directionalSlice] using
    (lineSliceIteratedDerivThreeEqVectorThirdDirectionalDerivative
      (f := f) (x := x) (h := h) hf)

/-- Helper for Theorem 5.4.7.6: on the positive orthant, `ξ` equals the expanded entropy formula
`-x₁ log x₁ + x₁ log x₂`. -/
private def entropyExpanded : (ℝ × ℝ) → ℝ :=
  fun x ↦ -(x.1 * Real.log x.1) + x.1 * Real.log x.2

/-- Helper for Theorem 5.4.7.6: `ξ` agrees with `entropyExpanded` on the strict orthant. -/
private theorem entropyEpigraphRelativeEntropy_eq_entropyExpanded_on_interior :
    Set.EqOn ξ entropyExpanded (interior powerConeQ1) := by
  intro x hx
  have hx₁ : 0 < x.1 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.1
  have hx₂ : 0 < x.2 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.2
  -- Rewrite the quotient logarithm to the source-normalized difference of logs.
  rw [entropyExpanded, entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub hx₁ hx₂]
  ring

/-- Helper for Theorem 5.4.7.6: the scalar affine map `t ↦ x + t * u` has derivative `u`. -/
private theorem scalarAffineHasDerivAt
    {x u : ℝ} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s * u) u t := by
  -- Differentiate the scalar multiplication first and then add the base point.
  simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
    (((hasDerivAt_id t).mul_const u).const_add x)

/-- Helper for Theorem 5.4.7.6: the scalar affine map has vanishing second iterated derivative. -/
private theorem scalarAffineIteratedDerivTwo
    {x u : ℝ} :
    iteratedDeriv 2 (fun s : ℝ ↦ x + s * u) = fun _ : ℝ ↦ (0 : ℝ) := by
  -- The derivative is constant, so the second derivative vanishes.
  funext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ ↦ x + s * u) = fun _ : ℝ ↦ u := by
    funext s
    exact (scalarAffineHasDerivAt (x := x) (u := u) s).deriv
  rw [hderiv, deriv_const]

/-- Helper for Theorem 5.4.7.6: the scalar affine map has vanishing third iterated derivative. -/
private theorem scalarAffineIteratedDerivThree
    {x u : ℝ} :
    iteratedDeriv 3 (fun s : ℝ ↦ x + s * u) = fun _ : ℝ ↦ (0 : ℝ) := by
  -- Once the second iterated derivative is zero, one more derivative stays zero.
  funext t
  rw [iteratedDeriv_succ, scalarAffineIteratedDerivTwo, deriv_const]

/-- Helper for Theorem 5.4.7.6: the `-log` of a positive affine scalar slice has derivative
`-(u / x)` at the base point. -/
private theorem affineNegLogDeriv
    {x u : ℝ} (hx : 0 < x) :
    deriv (fun t : ℝ ↦ -Real.log (x + t * u)) 0 = -(u / x) := by
  have haff : HasDerivAt (fun t : ℝ ↦ x + t * u) u 0 :=
    scalarAffineHasDerivAt (x := x) (u := u) 0
  have hnegLog : HasDerivAt (fun y : ℝ ↦ -Real.log y) (-(x + 0 * u)⁻¹) (x + 0 * u) := by
    simpa using (Real.hasDerivAt_log (show x + 0 * u ≠ 0 by simpa using hx.ne')).neg
  -- Compose the scalar `-log` derivative with the affine slice.
  calc
    deriv (fun t : ℝ ↦ -Real.log (x + t * u)) 0
        = deriv (((fun y : ℝ ↦ -Real.log y) ∘ fun t : ℝ ↦ x + t * u)) 0 := by rfl
    _ = -(u / x) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            (hnegLog.comp 0 haff).deriv

/-- Helper for Theorem 5.4.7.6: the `-log` of a positive affine scalar slice has second
iterated derivative `(u / x)^2` at the base point. -/
private theorem affineNegLogSecondDeriv
    {x u : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (fun t : ℝ ↦ -Real.log (x + t * u)) 0 = (u / x) ^ (2 : ℕ) := by
  -- Route correction: use the scalar `-log` owner directly instead of transporting back to
  -- `Real.log`.
  change secondDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u = (u / x) ^ (2 : ℕ)
  simpa only [directionalSlice, smul_eq_mul, div_pow] using
    (negLog_secondDirectionalDerivative_eq_sq_div_sq (x := x) (u := u) hx)

/-- Helper for Theorem 5.4.7.6: the `-log` of a positive affine scalar slice has third iterated
derivative `-2 (u / x)^3` at the base point. -/
private theorem affineNegLogThirdDeriv
    {x u : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 (fun t : ℝ ↦ -Real.log (x + t * u)) 0 = -2 * (u / x) ^ (3 : ℕ) := by
  -- Route correction: keep the cubic slice in the same `-Real.log` spelling as the quadratic
  -- helper.
  have hthird :
      thirdDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u =
        -2 * u ^ (3 : ℕ) / x ^ (3 : ℕ) := by
    simpa only [directionalSlice, smul_eq_mul] using
      (negLog_thirdDirectionalDerivative_eq (x := x) (u := u) hx)
  calc
    iteratedDeriv 3 (fun t : ℝ ↦ -Real.log (x + t * u)) 0 =
        thirdDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u := by
          rfl
    _ = -2 * u ^ (3 : ℕ) / x ^ (3 : ℕ) := hthird
    _ = -2 * (u / x) ^ (3 : ℕ) := by
          rw [div_eq_mul_inv]
          rw [div_pow]
          ring

/-- Helper for Theorem 5.4.7.6: the logarithm of a positive affine scalar slice has derivative
`u / x` at the base point. -/
private theorem affineLogDeriv
    {x u : ℝ} (hx : 0 < x) :
    deriv (fun t : ℝ ↦ Real.log (x + t * u)) 0 = u / x := by
  have haff : HasDerivAt (fun t : ℝ ↦ x + t * u) u 0 :=
    scalarAffineHasDerivAt (x := x) (u := u) 0
  have hlog : HasDerivAt Real.log ((x + 0 * u)⁻¹) (x + 0 * u) := by
    simpa using (Real.hasDerivAt_log (show x + 0 * u ≠ 0 by simpa using hx.ne'))
  -- Compose the scalar logarithm derivative with the affine slice.
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using (hlog.comp 0 haff).deriv

/-- Helper for Theorem 5.4.7.6: the logarithm of a positive affine scalar slice has second
iterated derivative `-(u / x)^2` at the base point. -/
private theorem affineLogSecondDeriv
    {x u : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (fun t : ℝ ↦ Real.log (x + t * u)) 0 = -((u / x) ^ (2 : ℕ)) := by
  -- The positive `log` formula is the negation of the stabilized `-log` slice identity.
  have hneg := congrArg Neg.neg (affineNegLogSecondDeriv (x := x) (u := u) hx)
  simpa using hneg

/-- Helper for Theorem 5.4.7.6: the logarithm of a positive affine scalar slice has third
iterated derivative `2 (u / x)^3` at the base point. -/
private theorem affineLogThirdDeriv
    {x u : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 (fun t : ℝ ↦ Real.log (x + t * u)) 0 = 2 * (u / x) ^ (3 : ℕ) := by
  -- The cubic `log` formula is the negation of the stabilized `-log` slice identity.
  have hneg := congrArg Neg.neg (affineNegLogThirdDeriv (x := x) (u := u) hx)
  simpa using hneg

/-- Helper for Theorem 5.4.7.6: multiplying an affine factor by a logarithmic affine slice has
the expected quadratic product-rule expansion at the base point. -/
private theorem affineMulLogSecondDeriv
    {a b x u : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (fun t : ℝ ↦ (a + t * b) * Real.log (x + t * u)) 0 =
      a * (-(u / x) ^ (2 : ℕ)) + 2 * b * (u / x) := by
  have haff : ContDiffAt ℝ 2 (fun t : ℝ ↦ a + t * b) 0 := by
    fun_prop
  have hlog : ContDiffAt ℝ 2 (fun t : ℝ ↦ Real.log (x + t * u)) 0 := by
    have hbase : ContDiffAt ℝ 2 (fun y : ℝ ↦ Real.log y) x := by
      simpa using (Real.contDiffAt_log.2 hx.ne' : ContDiffAt ℝ 2 (fun y : ℝ ↦ Real.log y) x)
    have haff' : ContDiffAt ℝ 2 (fun t : ℝ ↦ x + t * u) 0 := by
      fun_prop
    have hbase0 : ContDiffAt ℝ 2 (fun y : ℝ ↦ Real.log y) (x + 0 * u) := by
      simpa using hbase
    exact hbase0.comp 0 haff'
  have haffDeriv : deriv (fun t : ℝ ↦ a + t * b) 0 = b := by
    exact (scalarAffineHasDerivAt (x := a) (u := b) 0).deriv
  have hlogDeriv : deriv (fun t : ℝ ↦ Real.log (x + t * u)) 0 = u / x := by
    exact affineLogDeriv (x := x) (u := u) hx
  have haffTwo : iteratedDeriv 2 (fun t : ℝ ↦ a + t * b) 0 = 0 := by
    simpa using congrArg (fun f : ℝ → ℝ ↦ f 0) (scalarAffineIteratedDerivTwo (x := a) (u := b))
  have hlogTwo : iteratedDeriv 2 (fun t : ℝ ↦ Real.log (x + t * u)) 0 = -((u / x) ^ (2 : ℕ)) := by
    exact affineLogSecondDeriv (x := x) (u := u) hx
  -- Expand the quadratic Leibniz sum and collapse the vanishing higher affine derivatives.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ (a + t * b) * Real.log (x + t * u)) 0
        = ∑ i ∈ Finset.range (2 + 1),
            Nat.choose 2 i *
              iteratedDeriv i (fun t : ℝ ↦ a + t * b) 0 *
              iteratedDeriv (2 - i) (fun t : ℝ ↦ Real.log (x + t * u)) 0 := by
              simpa using
                (iteratedDeriv_mul (x := 0) (n := 2) (f := fun t : ℝ ↦ a + t * b)
                  (g := fun t : ℝ ↦ Real.log (x + t * u)) haff hlog)
    _ = a * (-(u / x) ^ (2 : ℕ)) + 2 * b * (u / x) := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          simp [iteratedDeriv_zero, iteratedDeriv_one, haffDeriv, hlogDeriv, haffTwo, hlogTwo]

/-- Helper for Theorem 5.4.7.6: multiplying an affine factor by a logarithmic affine slice has
the expected cubic product-rule expansion at the base point. -/
private theorem affineMulLogThirdDeriv
    {a b x u : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 (fun t : ℝ ↦ (a + t * b) * Real.log (x + t * u)) 0 =
      a * (2 * (u / x) ^ (3 : ℕ)) + 3 * b * (-(u / x) ^ (2 : ℕ)) := by
  have haff : ContDiffAt ℝ 3 (fun t : ℝ ↦ a + t * b) 0 := by
    fun_prop
  have hlog : ContDiffAt ℝ 3 (fun t : ℝ ↦ Real.log (x + t * u)) 0 := by
    have hbase : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) x := by
      simpa using (Real.contDiffAt_log.2 hx.ne' : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) x)
    have haff' : ContDiffAt ℝ 3 (fun t : ℝ ↦ x + t * u) 0 := by
      fun_prop
    have hbase0 : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) (x + 0 * u) := by
      simpa using hbase
    exact hbase0.comp 0 haff'
  have haffDeriv : deriv (fun t : ℝ ↦ a + t * b) 0 = b := by
    exact (scalarAffineHasDerivAt (x := a) (u := b) 0).deriv
  have hlogDeriv : deriv (fun t : ℝ ↦ Real.log (x + t * u)) 0 = u / x := by
    exact affineLogDeriv (x := x) (u := u) hx
  have haffTwo : iteratedDeriv 2 (fun t : ℝ ↦ a + t * b) 0 = 0 := by
    simpa using congrArg (fun f : ℝ → ℝ ↦ f 0) (scalarAffineIteratedDerivTwo (x := a) (u := b))
  have haffThree : iteratedDeriv 3 (fun t : ℝ ↦ a + t * b) 0 = 0 := by
    simpa using congrArg (fun f : ℝ → ℝ ↦ f 0) (scalarAffineIteratedDerivThree (x := a) (u := b))
  have hlogTwo : iteratedDeriv 2 (fun t : ℝ ↦ Real.log (x + t * u)) 0 = -((u / x) ^ (2 : ℕ)) := by
    exact affineLogSecondDeriv (x := x) (u := u) hx
  have hlogThree :
      iteratedDeriv 3 (fun t : ℝ ↦ Real.log (x + t * u)) 0 = 2 * (u / x) ^ (3 : ℕ) := by
    exact affineLogThirdDeriv (x := x) (u := u) hx
  -- Expand the cubic Leibniz sum and again use that the affine factor has no higher derivatives.
  calc
    iteratedDeriv 3 (fun t : ℝ ↦ (a + t * b) * Real.log (x + t * u)) 0
        = ∑ i ∈ Finset.range (3 + 1),
            Nat.choose 3 i *
              iteratedDeriv i (fun t : ℝ ↦ a + t * b) 0 *
              iteratedDeriv (3 - i) (fun t : ℝ ↦ Real.log (x + t * u)) 0 := by
              simpa using
                (iteratedDeriv_mul (x := 0) (n := 3) (f := fun t : ℝ ↦ a + t * b)
                  (g := fun t : ℝ ↦ Real.log (x + t * u)) haff hlog)
    _ = a * (2 * (u / x) ^ (3 : ℕ)) - 3 * b * (u / x) ^ (2 : ℕ) := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
          simp [iteratedDeriv_zero, iteratedDeriv_one, haffDeriv, hlogDeriv, haffTwo, haffThree,
            hlogTwo, hlogThree, sub_eq_add_neg]
    _ = a * (2 * (u / x) ^ (3 : ℕ)) + 3 * b * (-(u / x) ^ (2 : ℕ)) := by
          ring

/-- Helper for Theorem 5.4.7.6: the expanded entropy formula is `C³` on the strict orthant. -/
private theorem entropyExpanded_contDiffOn_interior :
    ContDiffOn ℝ 3 entropyExpanded (interior powerConeQ1) := by
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
  have hfstLog : ContDiffOn ℝ 3 (fun x : ℝ × ℝ ↦ Real.log x.1) (interior powerConeQ1) := by
    intro x hx
    have hx₁ : 0 < x.1 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.1
    have hfstAt : ContDiffAt ℝ 3 (Prod.fst : ℝ × ℝ → ℝ) x := by
      simpa using
        (ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ ℝ ℝ)).contDiffAt
    have hlogAt : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) x.1 := by
      simpa using (Real.contDiffAt_log.2 hx₁.ne' : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) x.1)
    exact (hlogAt.comp x hfstAt).contDiffWithinAt
  have hsndLog : ContDiffOn ℝ 3 (fun x : ℝ × ℝ ↦ Real.log x.2) (interior powerConeQ1) := by
    intro x hx
    have hx₂ : 0 < x.2 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.2
    have hsndAt : ContDiffAt ℝ 3 (Prod.snd : ℝ × ℝ → ℝ) x := by
      simpa using
        (ContinuousLinearMap.contDiff (ContinuousLinearMap.snd ℝ ℝ ℝ)).contDiffAt
    have hlogAt : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) x.2 := by
      simpa using (Real.contDiffAt_log.2 hx₂.ne' : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) x.2)
    exact (hlogAt.comp x hsndAt).contDiffWithinAt
  have hterm1 : ContDiffOn ℝ 3 (fun x : ℝ × ℝ ↦ -x.1 * Real.log x.1) (interior powerConeQ1) := by
    -- Multiply the first coordinate with its logarithm and negate the result.
    simpa using hfst.neg.mul hfstLog
  have hterm2 : ContDiffOn ℝ 3 (fun x : ℝ × ℝ ↦ x.1 * Real.log x.2) (interior powerConeQ1) := by
    -- Multiply the first coordinate with the second-coordinate logarithm.
    simpa using hfst.mul hsndLog
  simpa [entropyExpanded] using hterm1.add hterm2

/-- Helper for Theorem 5.4.7.6: the expanded entropy formula has the explicit second directional
derivative `-x₁ (h₁ / x₁ - h₂ / x₂)^2` on the strict orthant. -/
private theorem entropyExpanded_secondDirectionalDerivative_eq
    {x h : ℝ × ℝ} (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) :
    secondDirectionalDerivative entropyExpanded x h =
      -x.1 * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ) := by
  have hterm1Cont : ContDiffAt ℝ 2
      (fun t : ℝ ↦ -((x.1 + t * h.1) * Real.log (x.1 + t * h.1))) 0 := by
    have haff : ContDiffAt ℝ 2 (fun t : ℝ ↦ x.1 + t * h.1) 0 := by
      fun_prop
    have hlog : ContDiffAt ℝ 2 (fun t : ℝ ↦ Real.log (x.1 + t * h.1)) 0 := by
      have hbase : ContDiffAt ℝ 2 (fun y : ℝ ↦ Real.log y) x.1 := by
        simpa using (Real.contDiffAt_log.2 hx₁.ne' : ContDiffAt ℝ 2 (fun y : ℝ ↦ Real.log y) x.1)
      have hbase0 : ContDiffAt ℝ 2 (fun y : ℝ ↦ Real.log y) (x.1 + 0 * h.1) := by
        simpa using hbase
      exact hbase0.comp 0 haff
    exact (haff.mul hlog).neg
  have hterm2Cont : ContDiffAt ℝ 2
      (fun t : ℝ ↦ (x.1 + t * h.1) * Real.log (x.2 + t * h.2)) 0 := by
    have haff₁ : ContDiffAt ℝ 2 (fun t : ℝ ↦ x.1 + t * h.1) 0 := by
      fun_prop
    have hlog₂ : ContDiffAt ℝ 2 (fun t : ℝ ↦ Real.log (x.2 + t * h.2)) 0 := by
      have hbase : ContDiffAt ℝ 2 (fun y : ℝ ↦ Real.log y) x.2 := by
        simpa using (Real.contDiffAt_log.2 hx₂.ne' : ContDiffAt ℝ 2 (fun y : ℝ ↦ Real.log y) x.2)
      have haff₂ : ContDiffAt ℝ 2 (fun t : ℝ ↦ x.2 + t * h.2) 0 := by
        fun_prop
      have hbase0 : ContDiffAt ℝ 2 (fun y : ℝ ↦ Real.log y) (x.2 + 0 * h.2) := by
        simpa using hbase
      exact hbase0.comp 0 haff₂
    exact haff₁.mul hlog₂
  have hslice :
      directionalSlice entropyExpanded x h =
        (fun t : ℝ ↦ -((x.1 + t * h.1) * Real.log (x.1 + t * h.1))) +
          fun t : ℝ ↦ (x.1 + t * h.1) * Real.log (x.2 + t * h.2) := by
    funext t
    -- Route correction: keep the whole slice in a single affine-product normal form.
    simp [directionalSlice, entropyExpanded, smul_eq_mul]
  -- Differentiate the two affine-log products separately, then normalize the resulting rational identity.
  rw [secondDirectionalDerivative, hslice, iteratedDeriv_add hterm1Cont hterm2Cont,
    iteratedDeriv_fun_neg]
  rw [affineMulLogSecondDeriv (a := x.1) (b := h.1) (x := x.1) (u := h.1) hx₁]
  rw [affineMulLogSecondDeriv (a := x.1) (b := h.1) (x := x.2) (u := h.2) hx₂]
  field_simp [hx₁.ne', hx₂.ne']
  ring_nf

/-- Helper for Theorem 5.4.7.6: the expanded entropy formula has the explicit third directional
derivative factorization needed for compatibility with the orthant barrier. -/
private theorem entropyExpanded_thirdDirectionalDerivative_eq
    {x h : ℝ × ℝ} (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) :
    thirdDirectionalDerivative entropyExpanded x h =
      -secondDirectionalDerivative entropyExpanded x h *
        (h.1 / x.1 + 2 * (h.2 / x.2)) := by
  have hterm1Cont : ContDiffAt ℝ 3
      (fun t : ℝ ↦ -((x.1 + t * h.1) * Real.log (x.1 + t * h.1))) 0 := by
    have haff : ContDiffAt ℝ 3 (fun t : ℝ ↦ x.1 + t * h.1) 0 := by
      fun_prop
    have hlog : ContDiffAt ℝ 3 (fun t : ℝ ↦ Real.log (x.1 + t * h.1)) 0 := by
      have hbase : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) x.1 := by
        simpa using (Real.contDiffAt_log.2 hx₁.ne' : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) x.1)
      have hbase0 : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) (x.1 + 0 * h.1) := by
        simpa using hbase
      exact hbase0.comp 0 haff
    exact (haff.mul hlog).neg
  have hterm2Cont : ContDiffAt ℝ 3
      (fun t : ℝ ↦ (x.1 + t * h.1) * Real.log (x.2 + t * h.2)) 0 := by
    have haff₁ : ContDiffAt ℝ 3 (fun t : ℝ ↦ x.1 + t * h.1) 0 := by
      fun_prop
    have hlog₂ : ContDiffAt ℝ 3 (fun t : ℝ ↦ Real.log (x.2 + t * h.2)) 0 := by
      have hbase : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) x.2 := by
        simpa using (Real.contDiffAt_log.2 hx₂.ne' : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) x.2)
      have haff₂ : ContDiffAt ℝ 3 (fun t : ℝ ↦ x.2 + t * h.2) 0 := by
        fun_prop
      have hbase0 : ContDiffAt ℝ 3 (fun y : ℝ ↦ Real.log y) (x.2 + 0 * h.2) := by
        simpa using hbase
      exact hbase0.comp 0 haff₂
    exact haff₁.mul hlog₂
  have hslice :
      directionalSlice entropyExpanded x h =
        (fun t : ℝ ↦ -((x.1 + t * h.1) * Real.log (x.1 + t * h.1))) +
          fun t : ℝ ↦ (x.1 + t * h.1) * Real.log (x.2 + t * h.2) := by
    funext t
    -- Route correction: reuse the same normalized affine-product slice as in the quadratic case.
    simp [directionalSlice, entropyExpanded, smul_eq_mul]
  -- Differentiate the normalized slice once more, then factor the cubic expression through the
  -- already-proved quadratic formula.
  rw [thirdDirectionalDerivative, hslice, iteratedDeriv_add hterm1Cont hterm2Cont,
    iteratedDeriv_fun_neg]
  rw [affineMulLogThirdDeriv (a := x.1) (b := h.1) (x := x.1) (u := h.1) hx₁]
  rw [affineMulLogThirdDeriv (a := x.1) (b := h.1) (x := x.2) (u := h.2) hx₂]
  rw [entropyExpanded_secondDirectionalDerivative_eq hx₁ hx₂]
  field_simp [hx₁.ne', hx₂.ne']
  ring_nf

/-- Helper for Theorem 5.4.7.6: `ξ` inherits the explicit second directional derivative formula
from the expanded entropy expression on the strict orthant. -/
lemma entropyEpigraphRelativeEntropy_secondDirectionalDerivative_eq
    {x h : ℝ × ℝ} (hx : x ∈ interior powerConeQ1) :
    secondDirectionalDerivative ξ x h =
      -x.1 * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ) := by
  have hx₁ : 0 < x.1 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.1
  have hx₂ : 0 < x.2 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.2
  have hcontExpanded : ContDiffAt ℝ 3 entropyExpanded x :=
    entropyExpanded_contDiffOn_interior.contDiffAt (isOpen_interior.mem_nhds hx)
  have hcontXi : ContDiffAt ℝ 3 ξ x := by
    have hcontEq :
        ContDiffOn ℝ 3 ξ (interior powerConeQ1) := by
      -- Replace `ξ` by the expanded entropy formula on the strict orthant.
      exact (contDiffOn_congr entropyEpigraphRelativeEntropy_eq_entropyExpanded_on_interior).2
        entropyExpanded_contDiffOn_interior
    exact hcontEq.contDiffAt (isOpen_interior.mem_nhds hx)
  have hEq : ξ =ᶠ[nhds x] entropyExpanded := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact entropyEpigraphRelativeEntropy_eq_entropyExpanded_on_interior hy
  have hvector :
      vectorSecondDirectionalDerivative ξ x h =
        vectorSecondDirectionalDerivative entropyExpanded x h := by
    have hderivEq :
        iteratedFDeriv ℝ 2 ξ x = iteratedFDeriv ℝ 2 entropyExpanded x := by
      exact (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq 2).eq_of_nhds
    exact congrArg (fun T ↦ T (fun _ ↦ h)) hderivEq
  -- Transfer the second directional derivative through the neighborhood equality with `entropyExpanded`.
  calc
    secondDirectionalDerivative ξ x h = vectorSecondDirectionalDerivative ξ x h := by
      symm
      exact vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative hcontXi
    _ = vectorSecondDirectionalDerivative entropyExpanded x h := hvector
    _ = secondDirectionalDerivative entropyExpanded x h := by
      exact vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative hcontExpanded
    _ = -x.1 * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ) := by
      exact entropyExpanded_secondDirectionalDerivative_eq hx₁ hx₂

/-- Helper for Theorem 5.4.7.6: `ξ` inherits the explicit third directional derivative
factorization from the expanded entropy expression on the strict orthant. -/
lemma entropyEpigraphRelativeEntropy_thirdDirectionalDerivative_eq
    {x h : ℝ × ℝ} (hx : x ∈ interior powerConeQ1) :
    thirdDirectionalDerivative ξ x h =
      -secondDirectionalDerivative ξ x h * (h.1 / x.1 + 2 * (h.2 / x.2)) := by
  have hx₁ : 0 < x.1 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.1
  have hx₂ : 0 < x.2 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.2
  have hcontExpanded : ContDiffAt ℝ 3 entropyExpanded x :=
    entropyExpanded_contDiffOn_interior.contDiffAt (isOpen_interior.mem_nhds hx)
  have hcontXi : ContDiffAt ℝ 3 ξ x := by
    have hcontEq :
        ContDiffOn ℝ 3 ξ (interior powerConeQ1) := by
      -- Replace `ξ` by the expanded entropy formula on the strict orthant.
      exact (contDiffOn_congr entropyEpigraphRelativeEntropy_eq_entropyExpanded_on_interior).2
        entropyExpanded_contDiffOn_interior
    exact hcontEq.contDiffAt (isOpen_interior.mem_nhds hx)
  have hEq : ξ =ᶠ[nhds x] entropyExpanded := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact entropyEpigraphRelativeEntropy_eq_entropyExpanded_on_interior hy
  have hvector :
      vectorThirdDirectionalDerivative ξ x h =
        vectorThirdDirectionalDerivative entropyExpanded x h := by
    have hderivEq :
        iteratedFDeriv ℝ 3 ξ x = iteratedFDeriv ℝ 3 entropyExpanded x := by
      exact (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq 3).eq_of_nhds
    exact congrArg (fun T ↦ T (fun _ ↦ h)) hderivEq
  have hsecond :
      secondDirectionalDerivative ξ x h =
        secondDirectionalDerivative entropyExpanded x h := by
    calc
      secondDirectionalDerivative ξ x h = vectorSecondDirectionalDerivative ξ x h := by
        symm
        exact vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative hcontXi
      _ = vectorSecondDirectionalDerivative entropyExpanded x h := by
        have hderivEq :
            iteratedFDeriv ℝ 2 ξ x = iteratedFDeriv ℝ 2 entropyExpanded x := by
          exact (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hEq 2).eq_of_nhds
        exact congrArg (fun T ↦ T (fun _ ↦ h)) hderivEq
      _ = secondDirectionalDerivative entropyExpanded x h := by
        exact vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative hcontExpanded
  -- Transfer the third directional derivative through the neighborhood equality with `entropyExpanded`.
  calc
    thirdDirectionalDerivative ξ x h = vectorThirdDirectionalDerivative ξ x h := by
      symm
      exact vectorThirdDirectionalDerivative_eq_thirdDirectionalDerivative hcontXi
    _ = vectorThirdDirectionalDerivative entropyExpanded x h := hvector
    _ = thirdDirectionalDerivative entropyExpanded x h := by
      exact vectorThirdDirectionalDerivative_eq_thirdDirectionalDerivative hcontExpanded
    _ = -secondDirectionalDerivative entropyExpanded x h *
          (h.1 / x.1 + 2 * (h.2 / x.2)) := by
          exact entropyExpanded_thirdDirectionalDerivative_eq hx₁ hx₂
    _ = -secondDirectionalDerivative ξ x h * (h.1 / x.1 + 2 * (h.2 / x.2)) := by
          rw [← hsecond]

/-- Helper for Theorem 5.4.7.6: the relative-entropy map `ξ` is the `C³` cone-concave input
required by the cone-composition barrier theorem on the orthant `powerConeQ1`. -/
lemma entropyEpigraphRelativeEntropy_is_three_times_cont_diff_concave_on_with :
    IsThreeTimesContDiffConcaveOnWith
      powerConeQ1
      (ConvexCone.positive ℝ ℝ)
      ξ := by
  refine
    { out := by
        simpa [ConvexCone.mem_positive] using (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ)))
      isClosed_domain := powerConeQ1IsClosed
      convex_domain := powerConeQ1_convex
      contDiffOn := ?_
      neg_second_directional_derivative_mem := ?_ }
  · -- Replace `ξ` by the expanded entropy formula on the strict orthant.
    exact (contDiffOn_congr entropyEpigraphRelativeEntropy_eq_entropyExpanded_on_interior).2
      entropyExpanded_contDiffOn_interior
  · intro x hx h
    have hx₁ : 0 < x.1 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.1
    -- Route correction: convert the within-domain second derivative to the scalar directional
    -- derivative, then use the explicit entropy formula.
    have hcontEq :
        ContDiffOn ℝ 3 ξ (interior powerConeQ1) := by
      exact (contDiffOn_congr entropyEpigraphRelativeEntropy_eq_entropyExpanded_on_interior).2
        entropyExpanded_contDiffOn_interior
    have hcontAt : ContDiffAt ℝ 3 ξ x :=
      hcontEq.contDiffAt (isOpen_interior.mem_nhds hx)
    have hiter :
        iteratedFDerivWithin ℝ 2 ξ (interior powerConeQ1) x (fun _ ↦ h) =
          secondDirectionalDerivative ξ x h := by
      calc
        iteratedFDerivWithin ℝ 2 ξ (interior powerConeQ1) x (fun _ ↦ h) =
            vectorSecondDirectionalDerivative ξ x h := by
              simpa [vectorSecondDirectionalDerivative] using
                congrArg (fun T ↦ T (fun _ ↦ h))
                  (iteratedFDerivWithin_eq_iteratedFDeriv
                    isOpen_interior.uniqueDiffOn
                    (hcontAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
                    hx)
        _ = secondDirectionalDerivative ξ x h := by
          exact vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative hcontAt
    rw [ConvexCone.mem_positive]
    rw [hiter, entropyEpigraphRelativeEntropy_secondDirectionalDerivative_eq hx]
    simpa using mul_nonneg hx₁.le (sq_nonneg (h.1 / x.1 - h.2 / x.2))

/-- Helper for Theorem 5.4.7.6: the outer half-space barrier
`(y, z) ↦ -log (y + z)` is the affine pullback of the scalar `-log` barrier, so it has
parameter `μ = 1` on `interior Q₂`. -/
lemma entropyEpigraphQ2_sublevel_log_barrier_is_one_self_concordant_barrier :
    @IsSelfConcordantBarrierOnWith
      (ℝ × ℝ)
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      (interior Q₂)
      (1 : NNReal)
      (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0) := by
  letI : SeminormedAddCommGroup (ℝ × ℝ) := Chap05RealProdL2.instSeminormedAddCommGroupRealProd
  letI : NormedAddCommGroup (ℝ × ℝ) := Chap05RealProdL2.instNormedAddCommGroupRealProd
  letI : NormedSpace ℝ (ℝ × ℝ) := Chap05RealProdL2.instNormedSpaceRealProd
  letI : InnerProductSpace ℝ (ℝ × ℝ) := Chap05RealProdL2.instInnerProductSpaceRealProd
  letI : CompleteSpace (ℝ × ℝ) := Chap05RealProdL2.instCompleteSpaceRealProd
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
  have hdom : gapMap ⁻¹' Set.Ioi (0 : ℝ) = interior Q₂ := by
    calc
      gapMap ⁻¹' Set.Ioi (0 : ℝ) = gapLinear ⁻¹' interior (Set.Ici (0 : ℝ)) := by
        ext yz
        simp [gapMap, gapLinear]
      _ = interior (gapLinear ⁻¹' Set.Ici (0 : ℝ)) := by
        symm
        simpa using gapLinear.interior_preimage hsurj (Set.Ici (0 : ℝ))
      _ = interior Q₂ := by
        rw [show gapLinear ⁻¹' Set.Ici (0 : ℝ) = Q₂ by
          ext yz
          simp [entropyEpigraphQ2, gapLinear]]
  have hfun :
      (fun yz : ℝ × ℝ ↦ -Real.log (yz.1 + yz.2)) =
        sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0 := by
    funext yz
    rcases yz with ⟨y, z⟩
    -- Normalize the canonical sublevel barrier to the textbook logarithmic formula.
    rw [sublevelLogBarrier_apply]
    ring_nf
  simpa [hdom, hfun] using hpull

/-- Helper for Theorem 5.4.7.6: the half-space `Q₂ = {(y, z) | 0 ≤ y + z}` is convex. -/
lemma entropyEpigraphQ2_convex : Convex ℝ (Q₂ : Set (ℝ × ℝ)) := by
  let gapLinear : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ) + (ContinuousLinearMap.snd ℝ ℝ ℝ)).toLinearMap
  -- `Q₂` is the preimage of the convex ray `[0, ∞)` under the sum map `(y, z) ↦ y + z`.
  simpa [entropyEpigraphQ2, gapLinear] using
    (convex_Ici (0 : ℝ)).linear_preimage gapLinear

/-- Helper for Theorem 5.4.7.6: the half-space `Q₂ = {(y, z) | 0 ≤ y + z}` is closed. -/
lemma entropyEpigraphQ2_closed : IsClosed (Q₂ : Set (ℝ × ℝ)) := by
  -- `Q₂` is the superlevel set of the continuous sum map `(y, z) ↦ y + z`.
  simpa [entropyEpigraphQ2] using
    isClosed_le continuous_const (continuous_fst.add continuous_snd)

/-- Helper for Theorem 5.4.7.6: every positive-cone direction `(s, 0)` is a recession direction
of the half-space `Q₂`. -/
lemma entropyEpigraphQ2_positive_recession
    {s : ℝ} (hs : s ∈ (ConvexCone.positive ℝ ℝ : Set ℝ))
    {p : ℝ × ℝ} (hp : p ∈ Q₂) (τ : ℝ) (hτ : 0 ≤ τ) :
    p + τ • (s, (0 : ℝ)) ∈ Q₂ := by
  have hs' : 0 ≤ s := by
    simpa [ConvexCone.mem_positive] using hs
  rcases p with ⟨y, z⟩
  rw [mem_entropyEpigraphQ2_iff] at hp ⊢
  -- Adding nonnegative mass to the `y` coordinate preserves the half-space inequality.
  have hτs : 0 ≤ τ * s := mul_nonneg hτ hs'
  have hsum : 0 ≤ y + z + τ * s := by
    nlinarith
  simpa only [Prod.smul_mk, smul_eq_mul, mul_zero, Prod.mk_add_mk, add_zero, add_assoc,
    add_left_comm, add_comm] using hsum

-- Route correction: this support file closes the entropy derivative and compatibility layer once,
-- so the target file can keep the public cone-barrier theorem as a thin owner rewrite.
/-- Helper for Theorem 5.4.7.6: the entropy-specific derivative inequality needed for
`β = 1` compatibility with the orthant barrier. -/
lemma entropyEpigraphRelativeEntropy_compatibility_bound
    {x : ℝ × ℝ} (hx : x ∈ interior powerConeQ1) (h : ℝ × ℝ) :
    (3 * ‖h‖[powerConeBarrier; x]) • (-vectorSecondDirectionalDerivative ξ x h) -
      vectorThirdDirectionalDerivative ξ x h ∈ ConvexCone.positive ℝ ℝ := by
  have hcontAt : ContDiffAt ℝ 3 ξ x :=
    entropyEpigraphRelativeEntropy_is_three_times_cont_diff_concave_on_with.contDiffOn.contDiffAt
      (isOpen_interior.mem_nhds hx)
  have h2 :
      vectorSecondDirectionalDerivative ξ x h = secondDirectionalDerivative ξ x h := by
    exact vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative hcontAt
  have h3 :
      vectorThirdDirectionalDerivative ξ x h = thirdDirectionalDerivative ξ x h := by
    exact vectorThirdDirectionalDerivative_eq_thirdDirectionalDerivative hcontAt
  let a : ℝ := h.1 / x.1
  let b : ℝ := h.2 / x.2
  let L : ℝ := a + 2 * b
  let S : ℝ := a ^ (2 : ℕ) + b ^ (2 : ℕ)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (sq_nonneg a) (sq_nonneg b)
  have hnorm_eq : ‖h‖[powerConeBarrier; x] = Real.sqrt S := by
    -- Rewrite the barrier local norm into the scaled-coordinate Euclidean norm.
    simpa [S] using powerConeBarrier_local_norm_eq hx
  have hs_nonneg : 0 ≤ -secondDirectionalDerivative ξ x h := by
    have hx₁ : 0 < x.1 := (mem_interior_powerConeQ1_iff x.1 x.2).1 hx |>.1
    -- The explicit second-derivative formula is a nonnegative multiple of `x.1`.
    rw [entropyEpigraphRelativeEntropy_secondDirectionalDerivative_eq hx]
    simpa using mul_nonneg hx₁.le (sq_nonneg (h.1 / x.1 - h.2 / x.2))
  have hLsq : L ^ (2 : ℕ) ≤ 5 * S := by
    -- This is the two-dimensional Cauchy--Schwarz inequality after expansion.
    dsimp [L, S]
    nlinarith [sq_nonneg (2 * a - b)]
  have habsL : |L| ≤ 3 * Real.sqrt S := by
    have hsq : (abs L) ^ (2 : ℕ) ≤ (3 * Real.sqrt S) ^ (2 : ℕ) := by
      have hsq' : L ^ (2 : ℕ) ≤ (3 : ℝ) ^ (2 : ℕ) * S := by
        nlinarith [hLsq]
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
  rw [ConvexCone.mem_positive, h2, h3]
  have hthird_eq :
      thirdDirectionalDerivative ξ x h =
        -secondDirectionalDerivative ξ x h *
          (h.1 / x.1 + 2 * (h.2 / x.2)) :=
    entropyEpigraphRelativeEntropy_thirdDirectionalDerivative_eq hx
  rw [hthird_eq, hnorm_eq]
  simp only [smul_eq_mul]
  rw [show (h.1 / x.1 + 2 * (h.2 / x.2)) = L by rfl]
  nlinarith

-- Proof sketch: package the orthant-side convexity/interior/barrier API together with the
-- entropy-specific compatibility bound extracted above.
/-- Theorem 5.4.7.6 (1): the relative-entropy map
`ξ(x) = -x^(1) \log (x^(1) / x^(2))` is `1`-compatible with the orthant barrier
`F(x) = -\log x^(1) - \log x^(2)` relative to the scalar cone `ℝ_+`. -/
theorem entropyEpigraphRelativeEntropy_isOneCompatibleWith_powerConeBarrier :
    IsBetaCompatibleWith powerConeQ1 (ConvexCone.positive ℝ ℝ)
      powerConeBarrier (1 : NNReal) ξ := by
  refine
    { convex_domain := powerConeQ1_convex
      interior_nonempty := ?_
      one_le_parameter := ?_
      selfConcordantBarrier := ?_
      contDiffOn :=
        entropyEpigraphRelativeEntropy_is_three_times_cont_diff_concave_on_with.contDiffOn
      compatibility_bound := ?_ }
  · -- The strict orthant contains `(1, 1)`.
    refine ⟨(1, 1), ?_⟩
    exact (mem_interior_powerConeQ1_iff 1 1).2 ⟨zero_lt_one, zero_lt_one⟩
  · -- The target compatibility parameter is exactly `β = 1`.
    simp
  · -- Reuse the orthant logarithmic barrier from Theorem 5.4.7.2.
    exact ⟨2, power_cone_barrier_is_two_self_concordant_barrier⟩
  · -- The remaining field is precisely the local entropy derivative inequality.
    intro x hx h
    simpa using entropyEpigraphRelativeEntropy_compatibility_bound hx h

-- Route correction: an owner-stable raw specialization still needs an explicit bridge between the
-- generic theorem's raw `Prod` ambient and the chapter `RealProdL2` geometry on `Q₂`.
