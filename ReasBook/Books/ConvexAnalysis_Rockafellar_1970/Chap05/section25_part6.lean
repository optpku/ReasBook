/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part5

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- Helper for Theorem 25.5: differentiability makes the chosen Euclidean gradient a point of the
vectorized subdifferential. -/
lemma helperForTheorem_25_5_gradient_mem_subdifferentialPreimage
    {n : Nat} {f : (Fin n → Real) → EReal} (hf : ConvexFunction f)
    {x : Fin n → Real} (hdiff : ERealDifferentiableAt f x) :
    erealGradientAt hdiff ∈
      ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) := by
  have hxFinite :
      f x ≠ ⊤ ∧ f x ≠ ⊥ :=
    ERealDifferentiableAt.finiteAt hdiff
  have hcore :=
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      f hf x hxFinite).1 hdiff
  -- Theorem 25.1 packages the gradient as a Euclidean subgradient, which is exactly the
  -- vectorized preimage statement used in the continuity proof.
  simpa using (hcore.1 : _)

/-- Helper for Theorem 25.5: at a differentiability point, every vectorized subgradient agrees
with the chosen Euclidean gradient. -/
lemma helperForTheorem_25_5_subgradientPreimage_eq_gradient
    {n : Nat} {f : (Fin n → Real) → EReal} (hf : ConvexFunction f)
    {x : Fin n → Real} (hdiff : ERealDifferentiableAt f x)
    {u : Fin n → Real}
    (hu : u ∈ ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x)) :
    u = erealGradientAt hdiff := by
  have hxFinite :
      f x ≠ ⊤ ∧ f x ≠ ⊥ :=
    ERealDifferentiableAt.finiteAt hdiff
  have hcore :=
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      f hf x hxFinite).1 hdiff
  have huSub : IsSubgradientAt f x (dotProductEquiv Real (Fin n) u) := by
    -- Membership in the Euclideanized preimage is just the subgradient predicate in vector form.
    simpa [subdifferentialAt] using hu
  -- The uniqueness clause from Theorem 25.1 now identifies the candidate vector with `∇ f(x)`.
  exact hcore.2.2 u huSub

/-- Helper for Theorem 25.5: continuity of the gradient on the differentiability set follows from
the closed-graph/local-boundedness argument for the subdifferential. -/
lemma helperForTheorem_25_5_gradient_continuousOn_differentiabilitySet
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    let D : Set (Fin n → Real) := {x | x ∈ U ∧ ERealDifferentiableAt f x}
    Continuous (fun x : {x // x ∈ D} => erealGradientAt x.2.2) := by
  intro U D
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  rw [Metric.continuous_iff]
  intro x ε hε
  -- Route correction: use Corollary 5.24.2 directly instead of the earlier closed-graph route.
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (properConvex_upperSemicontinuousOn_upperDirectionalDerivative_and_subdifferential_subset
      (f := f) hproper).2 x.2.1 (ε / 2) (by linarith)
  refine ⟨δ, hδpos, ?_⟩
  intro y hxy
  have hyClosedBall : y.1 ∈ Metric.closedBall x.1 δ := by
    change dist y.1 x.1 ≤ δ
    exact le_of_lt (by simpa using hxy)
  have hyGradPreimage :
      erealGradientAt y.2.2 ∈
        ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f y.1) := by
    -- The nearby differentiability point contributes its gradient as a genuine Euclidean
    -- subgradient, exactly in the preimage form required by Corollary 5.24.2.
    exact helperForTheorem_25_5_gradient_mem_subdifferentialPreimage
      (f := f) hf (x := y.1) y.2.2
  have hyNear :
      erealGradientAt y.2.2 ∈
        Set.image2 (fun u v : Fin n → Real => u + v)
          ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x.1)
          (Metric.closedBall (0 : Fin n → Real) (ε / 2)) :=
    hδsub hyClosedBall hyGradPreimage
  rcases hyNear with ⟨u, hu, v, hv, huv⟩
  have huEq : u = erealGradientAt x.2.2 := by
    -- Differentiability at the base point collapses every translated subgradient back to the
    -- unique value `∇ f(x)`.
    exact helperForTheorem_25_5_subgradientPreimage_eq_gradient
      (f := f) hf (x := x.1) x.2.2 (u := u) hu
  have hvNorm :
      ‖v‖ ≤ ε / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv
  have hdist :
      dist (erealGradientAt y.2.2) (erealGradientAt x.2.2) < ε := by
    have hvlt : ‖v‖ < ε := by
      linarith
    calc
      dist (erealGradientAt y.2.2) (erealGradientAt x.2.2) =
          dist (u + v) (erealGradientAt x.2.2) := by
            rw [← huv]
      _ = ‖v‖ := by
            rw [huEq, dist_eq_norm]
            abel_nf
      _ < ε := hvlt
  simpa using hdist

/-- Theorem 25.5: if `f` is a proper convex function on `ℝ^n` and
`D = {x | f is differentiable at x}`, then `D` is dense in `int (dom f)`, the complement
`int (dom f) \ D` has Lebesgue measure zero, and the gradient mapping is continuous on `D`. -/
theorem properConvexFunction_differentiabilitySet_dense_null_complement_and_gradient_continuous
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    let D : Set (Fin n → Real) := {x | x ∈ U ∧ ERealDifferentiableAt f x}
    U ⊆ closure D ∧
      MeasureTheory.volume (U \ D) = 0 ∧
      Continuous (fun x : {x // x ∈ D} => erealGradientAt x.2.2) := by
  intro U D
  have hDenseNull :
      U ⊆ closure D ∧ MeasureTheory.volume (U \ D) = 0 := by
    -- The dense/null package is isolated in a dedicated helper because the remaining work is the
    -- slice/Fubini argument, not the final assembly of the theorem.
    simpa [U, D] using
      helperForTheorem_25_5_differentiabilitySet_dense_and_null
        (f := f) hproper
  have hGradCont :
      Continuous (fun x : {x // x ∈ D} => erealGradientAt x.2.2) := by
    -- Continuity is handled separately through the closed-graph argument for the subdifferential.
    simpa [U, D] using
      helperForTheorem_25_5_gradient_continuousOn_differentiabilitySet
        (f := f) hproper
  exact ⟨hDenseNull.1, hDenseNull.2, hGradCont⟩

-- Proof sketch: apply Theorem 25.5 to the proper convex `EReal`-valued extension of the
-- real-valued convex function `f` on the open convex set `C`. Since `f` is differentiable at
-- every point of `C`, the differentiability locus there is all of `C`, so the gradient map is
-- continuous on `C`; on an open set this is exactly the `C¹` conclusion `ContDiffOn ℝ 1 f C`.
/-- Helper for Corollary 25.5.1: the `+∞` extension of a real-valued convex function on a nonempty
open convex set is proper convex on all of `ℝⁿ`, and its effective-domain interior is exactly the
original open set. -/
lemma helperForCorollary_25_5_1_properConvexExtension
    {n : Nat} {C : Set (Fin n → Real)} {f : (Fin n → Real) → Real}
    (hCopen : IsOpen C) (_hCconv : Convex ℝ C) (hCne : C.Nonempty) (hf : ConvexOn ℝ C f) :
    let fExt : (Fin n → Real) → EReal := fun x => (f x : EReal) + indicatorFunction C x
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fExt ∧
      interior (effectiveDomain (Set.univ : Set (Fin n → Real)) fExt) = C := by
  classical
  intro fExt
  have hEq :
      fExt = fun x : Fin n → Real => if x ∈ C then (f x : EReal) else (⊤ : EReal) := by
    -- Rewrite the extension into the standard "finite on `C`, `⊤` off `C`" form.
    funext x
    simpa [fExt] using (add_indicatorFunction_eq (f := f) (C := C) x)
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real)) fExt := by
    -- Convexity is exactly the textbook extension-by-`⊤` construction.
    rw [hEq]
    simpa using (convexFunctionOn_univ_if_top (C := C) (g := f) hf)
  rcases hCne with ⟨x0, hx0⟩
  have hnonempty :
      Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) fExt) := by
    refine ⟨(x0, f x0), ?_⟩
    -- A point of `C` gives a finite epigraph point for the extension.
    exact (mem_epigraph_univ_iff (f := fExt)).2 (by simp [fExt, indicatorFunction, hx0])
  have hnotBot :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)), fExt x ≠ (⊥ : EReal) := by
    intro x _hx
    -- The extension is finite on `C` and `⊤` off `C`, so it never hits `⊥`.
    by_cases hx : x ∈ C
    · simp [fExt, indicatorFunction, hx]
    · simp [fExt, indicatorFunction, hx]
  have hDom :
      effectiveDomain (Set.univ : Set (Fin n → Real)) fExt = C := by
    -- Finite-valued points of the extension are exactly the points of `C`.
    ext x
    rw [effectiveDomain_eq]
    by_cases hx : x ∈ C
    · simp [fExt, add_indicatorFunction_eq, hx]
    · simp [fExt, add_indicatorFunction_eq, hx]
  refine ⟨⟨hconv, hnonempty, hnotBot⟩, ?_⟩
  -- Taking interiors now recovers the original open set.
  simpa [hDom] using hCopen.interior_eq

/-- Helper for Corollary 25.5.1: turn a Euclidean vector into the corresponding continuous linear
functional given by the dot product. -/
noncomputable def helperForCorollary_25_5_1_dotProductContinuousLinearMap
    {n : Nat} (v : Fin n → Real) : (Fin n → Real) →L[ℝ] Real :=
  ⟨dotProductEquiv ℝ (Fin n) v, (dotProductEquiv ℝ (Fin n) v).continuous_of_finiteDimensional⟩

/-- Helper for Corollary 25.5.1: the dot-product functional depends continuously on its vector
parameter. -/
lemma helperForCorollary_25_5_1_dotProductContinuousLinearMap_continuous
    {n : Nat} :
    Continuous
      (fun v : Fin n → Real =>
        helperForCorollary_25_5_1_dotProductContinuousLinearMap v) :=
  by
  let L : (Fin n → Real) →ₗ[ℝ] ((Fin n → Real) →L[ℝ] Real) :=
    { toFun := helperForCorollary_25_5_1_dotProductContinuousLinearMap
      map_add' := by
        intro v w
        ext y
        -- Evaluate both continuous linear maps on an arbitrary test vector.
        simp [helperForCorollary_25_5_1_dotProductContinuousLinearMap,
          dotProductEquiv_apply_apply]
      map_smul' := by
        intro a v
        ext y
        -- Scalar multiplication distributes through the dot product in the first argument.
        simp [helperForCorollary_25_5_1_dotProductContinuousLinearMap,
          dotProductEquiv_apply_apply] }
  -- Finite-dimensional linear maps are automatically continuous.
  simpa [L] using L.continuous_of_finiteDimensional

/-- Helper for Corollary 25.5.1: differentiability at a point identifies the Fréchet derivative
with the dot-product functional of the Euclidean gradient. -/
lemma helperForCorollary_25_5_1_hasFDerivAt_dotProductContinuousLinearMap
    {n : Nat} {f : (Fin n → Real) → Real} {x : Fin n → Real}
    (hdiffAt : DifferentiableAt ℝ f x) :
    HasFDerivAt f
      (helperForCorollary_25_5_1_dotProductContinuousLinearMap (euclideanGradientAt f x)) x := by
  -- Compare the candidate derivative with the actual Fréchet derivative on every direction.
  have hEq :
      fderiv ℝ f x =
        helperForCorollary_25_5_1_dotProductContinuousLinearMap (euclideanGradientAt f x) := by
    ext y
    have hlineFDeriv :
        HasDerivAt (fun t : Real => f (x + t • y)) ((fderiv ℝ f x) y) 0 := by
      simpa [HasLineDerivAt] using hdiffAt.hasFDerivAt.hasLineDerivAt y
    have hlineGrad :
        HasDerivAt (fun t : Real => f (x + t • y))
          (euclideanGradientAt f x ⬝ᵥ y) 0 :=
      directionalDerivative_eq_dot_euclideanGradient_of_differentiableAt
        (f := f) (x := x) (y := y) hdiffAt
    -- Uniqueness of the line derivative pins down the candidate continuous linear map.
    calc
      (fderiv ℝ f x) y = euclideanGradientAt f x ⬝ᵥ y := hlineFDeriv.unique hlineGrad
      _ =
          helperForCorollary_25_5_1_dotProductContinuousLinearMap
            (euclideanGradientAt f x) y := by
            symm
            simp [helperForCorollary_25_5_1_dotProductContinuousLinearMap,
              dotProductEquiv_apply_apply]
  simpa [hEq] using hdiffAt.hasFDerivAt

/-- Helper for Corollary 25.5.1: on the open set `C`, the Fréchet derivative is the dot-product
functional associated to the Euclidean gradient vector. -/
lemma helperForCorollary_25_5_1_fderivWithin_eq_dotProductContinuousLinearMap
    {n : Nat} {C : Set (Fin n → Real)} {f : (Fin n → Real) → Real}
    (hCopen : IsOpen C) (hdiff : DifferentiableOn ℝ f C) :
    ∀ x ∈ C,
      fderivWithin ℝ f C x =
        helperForCorollary_25_5_1_dotProductContinuousLinearMap (euclideanGradientAt f x) := by
  intro x hx
  ext y
  -- On an open set, the within-derivative is the ordinary derivative.
  rw [fderivWithin_of_isOpen hCopen hx]
  have hdiffAt : DifferentiableAt ℝ f x :=
    (hdiff x hx).differentiableAt (hCopen.mem_nhds hx)
  have hlineFDeriv :
      HasDerivAt (fun t : Real => f (x + t • y)) ((fderiv ℝ f x) y) 0 := by
    simpa [HasLineDerivAt] using hdiffAt.hasFDerivAt.hasLineDerivAt y
  have hlineGrad :
      HasDerivAt (fun t : Real => f (x + t • y))
        (euclideanGradientAt f x ⬝ᵥ y) 0 :=
    directionalDerivative_eq_dot_euclideanGradient_of_differentiableAt
      (f := f) (x := x) (y := y) hdiffAt
  -- Uniqueness of the one-dimensional derivative identifies the two linear functionals.
  calc
    (fderiv ℝ f x) y = euclideanGradientAt f x ⬝ᵥ y := hlineFDeriv.unique hlineGrad
    _ =
        helperForCorollary_25_5_1_dotProductContinuousLinearMap
          (euclideanGradientAt f x) y := by
          symm
          simpa [helperForCorollary_25_5_1_dotProductContinuousLinearMap] using
            (dotProductEquiv_apply_apply ℝ (Fin n) (euclideanGradientAt f x) y)

/-- Helper for Corollary 25.5.1: once the Euclidean gradient is known to be continuous on `C`,
the usual `ContDiffOn ℝ 1` criterion on an open set applies. -/
lemma helperForCorollary_25_5_1_contDiffOn_one_of_gradient_continuousOn
    {n : Nat} {C : Set (Fin n → Real)} {f : (Fin n → Real) → Real}
    (hCopen : IsOpen C) (hdiff : DifferentiableOn ℝ f C)
    (hgrad : ContinuousOn (fun x => euclideanGradientAt f x) C) :
    ContDiffOn ℝ 1 f C :=
  by
  have hDerivativeCont :
      ContinuousOn
        (fun x =>
          helperForCorollary_25_5_1_dotProductContinuousLinearMap (euclideanGradientAt f x))
        C :=
    -- Compose the continuous gradient field with the continuous dot-product parametrization.
    (helperForCorollary_25_5_1_dotProductContinuousLinearMap_continuous
      (n := n)).comp_continuousOn' hgrad
  have hFDerivCont :
      ContinuousOn (fderivWithin ℝ f C) C := by
    -- Replace the within-derivative by the already identified dot-product formula.
    refine hDerivativeCont.congr ?_
    intro x hx
    simpa using
      helperForCorollary_25_5_1_fderivWithin_eq_dotProductContinuousLinearMap
        (hCopen := hCopen) (hdiff := hdiff) x hx
  -- The open-set `C¹` criterion reduces the goal to continuity of `fderivWithin`.
  simpa using
    ((contDiffOn_succ_iff_fderivWithin (hs := hCopen.uniqueDiffOn) (n := 0) (f := f)
      (s := C)).2 <|
      by
        refine ⟨hdiff, ?_, ?_⟩
        · intro hzero
          exfalso
          simp at hzero
        · simpa [contDiffOn_zero] using hFDerivCont)

/-- Helper for Corollary 25.5.1: on an open neighborhood where the extension is finite-valued, the
`+∞` extension has the same first-order error quotient as the original real-valued function. -/
lemma helperForCorollary_25_5_1_extension_hasERealGradientAt
    {n : Nat} {C : Set (Fin n → Real)} {f : (Fin n → Real) → Real}
    (hCopen : IsOpen C) {x : Fin n → Real} (hx : x ∈ C)
    (hdiffAt : DifferentiableAt ℝ f x) :
    let fExt : (Fin n → Real) → EReal := fun y => (f y : EReal) + indicatorFunction C y
    HasERealGradientAt fExt x (euclideanGradientAt f x) ∧
      (∀ᶠ z in nhdsWithin x ({z | z ≠ x}),
        z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) fExt ∧ fExt z ≠ ⊥) := by
  intro fExt
  let g : Fin n → Real := euclideanGradientAt f x
  have hxTop : fExt x ≠ ⊤ := by
    -- At the base point, the extension is just the finite real value `f x`.
    simp [fExt, add_indicatorFunction_eq, hx]
  have hxBot : fExt x ≠ ⊥ := by
    -- The extension never takes the value `⊥` on points of `C`.
    simp [fExt, add_indicatorFunction_eq, hx]
  have hHasFDeriv :
      HasFDerivAt f (helperForCorollary_25_5_1_dotProductContinuousLinearMap g) x := by
    -- Ordinary differentiability gives the precise Fréchet derivative at `x`.
    simpa [g] using
      helperForCorollary_25_5_1_hasFDerivAt_dotProductContinuousLinearMap
        (f := f) (x := x) hdiffAt
  have hRealLittle :
      (fun z => f z - f x - g ⬝ᵥ (z - x)) =o[𝓝 x] fun z => ‖z - x‖ := by
    have hLittle :
        (fun z => f z - f x -
            helperForCorollary_25_5_1_dotProductContinuousLinearMap g (z - x)) =o[𝓝 x]
          fun z => z - x := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hHasFDeriv.isLittleO
    -- Rewrite the linear part as the explicit dot product with the gradient vector.
    simpa [helperForCorollary_25_5_1_dotProductContinuousLinearMap,
      dotProductEquiv_apply_apply] using hLittle.norm_right
  have hRealTendsto :
      Filter.Tendsto (fun z => (f z - f x - g ⬝ᵥ (z - x)) / ‖z - x‖)
        (𝓝 x) (𝓝 0) :=
    hRealLittle.tendsto_div_nhds_zero
  have hRealTendstoWithin :
      Filter.Tendsto (fun z => (f z - f x - g ⬝ᵥ (z - x)) / ‖z - x‖)
        (nhdsWithin x
          ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) fExt))
        (𝓝 0) :=
    hRealTendsto.mono_left nhdsWithin_le_nhds
  have hEventuallyEq :
      (fun z => erealGradientErrorQuotient fExt x g z) =ᶠ[nhdsWithin x
        ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) fExt)]
        fun z => (f z - f x - g ⬝ᵥ (z - x)) / ‖z - x‖ := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro z hz
    have hzDom :
        z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) fExt := hz.2
    have hzTop : fExt z ≠ ⊤ :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := fExt) hzDom
    have hzC : z ∈ C := by
      by_contra hzC
      have hzExtTop : fExt z = ⊤ := by
        simp [fExt, add_indicatorFunction_eq, hzC]
      exact hzTop hzExtTop
    have hzBot : fExt z ≠ ⊥ := by
      simp [fExt, add_indicatorFunction_eq, hzC]
    have hToRealSub :
        (fExt z - fExt x).toReal = f z - f x := by
      calc
        (fExt z - fExt x).toReal = (fExt z).toReal - (fExt x).toReal := by
          simpa using EReal.toReal_sub hzTop hzBot hxTop hxBot
        _ = f z - f x := by
          simp [fExt, add_indicatorFunction_eq, hzC, hx]
    -- On finite-valued points of the extension, the `EReal` quotient is the ordinary real quotient.
    simp [erealGradientErrorQuotient, hToRealSub]
  have hFiniteEventually :
      ∀ᶠ z in nhdsWithin x ({z | z ≠ x}),
        z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) fExt ∧ fExt z ≠ ⊥ := by
    have hCWithin :
        C ∈ nhdsWithin x ({z | z ≠ x}) :=
      mem_nhdsWithin_of_mem_nhds (hCopen.mem_nhds hx)
    refine Filter.mem_of_superset hCWithin ?_
    intro z hzC
    constructor
    · -- Inside `C`, the extension is finite and therefore belongs to its effective domain.
      simp [effectiveDomain_eq, fExt, add_indicatorFunction_eq, hzC]
    · -- Inside `C`, the extension is a real number, so it is never `⊥`.
      simp [fExt, add_indicatorFunction_eq, hzC]
  refine ⟨⟨hxTop, hxBot, ?_⟩, hFiniteEventually⟩
  -- Transfer the real differentiability limit to the `EReal` error quotient along the finite-valued
  -- punctured filter used in the definition.
  exact Filter.Tendsto.congr' hEventuallyEq.symm hRealTendstoWithin

/-- Helper for Corollary 25.5.1: the local `EReal` differentiability witness for the extension has
the same gradient as the original real-valued function. -/
lemma helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
    {n : Nat} {C : Set (Fin n → Real)} {f : (Fin n → Real) → Real}
    (hCopen : IsOpen C) {x : Fin n → Real} (hx : x ∈ C)
    (hdiffAt : DifferentiableAt ℝ f x) :
    let fExt : (Fin n → Real) → EReal := fun y => (f y : EReal) + indicatorFunction C y
    ∃ hExt : ERealDifferentiableAt fExt x, erealGradientAt hExt = euclideanGradientAt f x := by
  intro fExt
  rcases helperForCorollary_25_5_1_extension_hasERealGradientAt
      (hCopen := hCopen) (f := f) (x := x) hx hdiffAt with
    ⟨hHasGrad, hFinite⟩
  let hExt : ERealDifferentiableAt fExt x := ⟨euclideanGradientAt f x, hHasGrad, hFinite⟩
  refine ⟨hExt, ?_⟩
  -- Uniqueness of the extension gradient identifies the chosen witness with the Euclidean one.
  exact
    erealGradient_unique hFinite
      (ERealDifferentiableAt.hasERealGradientAt hExt) hHasGrad

/-- Helper for Corollary 25.5.1: the differentiability set of the `+∞` extension inside its
effective-domain interior is exactly the original open set `C`. -/
lemma helperForCorollary_25_5_1_extension_differentiabilitySet_eq
    {n : Nat} {C : Set (Fin n → Real)} {f : (Fin n → Real) → Real}
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (hf : ConvexOn ℝ C f)
    (hdiff : DifferentiableOn ℝ f C) (hCne : C.Nonempty) :
    let fExt : (Fin n → Real) → EReal := fun y => (f y : EReal) + indicatorFunction C y
    let U : Set (Fin n → Real) :=
      interior (effectiveDomain (Set.univ : Set (Fin n → Real)) fExt)
    let D : Set (Fin n → Real) := {x | x ∈ U ∧ ERealDifferentiableAt fExt x}
    D = C := by
  intro fExt U D
  obtain ⟨_, hInterior⟩ :=
    helperForCorollary_25_5_1_properConvexExtension
      (hCopen := hCopen) (_hCconv := hCconv) hCne hf
  ext x
  constructor
  · intro hxD
    -- Differentiability for the extension is only recorded on the effective-domain interior.
    exact hInterior ▸ hxD.1
  · intro hxC
    have hdiffAt : DifferentiableAt ℝ f x :=
      (hdiff x hxC).differentiableAt (hCopen.mem_nhds hxC)
    rcases helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
        (hCopen := hCopen) (f := f) (x := x) hxC hdiffAt with
      ⟨hExt, _⟩
    -- Every point of `C` yields an extension differentiability witness, so it lies in `D`.
    have hxU : x ∈ U := by
      change x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) fExt)
      exact hInterior.symm ▸ hxC
    exact ⟨hxU, hExt⟩

/-- Helper for Corollary 25.5.1: Theorem 25.5 applied to the `+∞` extension shows that the
Euclidean gradient of `f` varies continuously on `C`. -/
lemma helperForCorollary_25_5_1_gradient_continuousOn
    {n : Nat} {C : Set (Fin n → Real)} {f : (Fin n → Real) → Real}
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (hf : ConvexOn ℝ C f)
    (hdiff : DifferentiableOn ℝ f C) :
    ContinuousOn (fun x => euclideanGradientAt f x) C :=
  by
  classical
  by_cases hCempty : C = ∅
  · simp [hCempty]
  · have hCne : C.Nonempty := by
      by_contra hCnone
      exact hCempty (Set.eq_empty_iff_forall_notMem.mpr (by
        intro x hx
        exact hCnone ⟨x, hx⟩))
    let fExt : (Fin n → Real) → EReal := fun y => (f y : EReal) + indicatorFunction C y
    obtain ⟨hproper, hInterior⟩ :=
      helperForCorollary_25_5_1_properConvexExtension
        (hCopen := hCopen) (_hCconv := hCconv) hCne hf
    let U : Set (Fin n → Real) :=
      interior (effectiveDomain (Set.univ : Set (Fin n → Real)) fExt)
    let D : Set (Fin n → Real) := {x | x ∈ U ∧ ERealDifferentiableAt fExt x}
    have hTheorem25 :
        U ⊆ closure D ∧
          MeasureTheory.volume (U \ D) = 0 ∧
          Continuous (fun x : {x // x ∈ D} => erealGradientAt x.2.2) := by
      simpa [U, D] using
        properConvexFunction_differentiabilitySet_dense_null_complement_and_gradient_continuous
          (f := fExt) hproper
    have hD_eq_C : D = C := by
      -- Theorem 25.5 sees exactly the original open set because every point of `C` differentiates
      -- the extension and the extension is finite precisely on `C`.
      simpa [U, D] using
        helperForCorollary_25_5_1_extension_differentiabilitySet_eq
          (hCopen := hCopen) (hCconv := hCconv) (hf := hf) (hdiff := hdiff) hCne
    rw [continuousOn_iff_continuous_restrict]
    let toD : {x // x ∈ C} → {x // x ∈ D} :=
      fun x => ⟨x.1, hD_eq_C.symm ▸ x.2⟩
    have hToDContinuous : Continuous toD :=
      (Homeomorph.setCongr hD_eq_C.symm).continuous_toFun
    have hGradContD :
        Continuous (fun x : {x // x ∈ D} => erealGradientAt x.2.2) :=
      hTheorem25.2.2
    have hGradContC :
        Continuous (fun x : {x // x ∈ C} => erealGradientAt (toD x).2.2) :=
      hGradContD.comp hToDContinuous
    have hGradEq :
        (fun x : {x // x ∈ C} => erealGradientAt (toD x).2.2) =
          fun x : {x // x ∈ C} => euclideanGradientAt f x.1 := by
      funext x
      have hdiffAt : DifferentiableAt ℝ f x.1 :=
        (hdiff x.1 x.2).differentiableAt (hCopen.mem_nhds x.2)
      rcases helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
          (hCopen := hCopen) (f := f) (x := x.1) x.2 hdiffAt with
        ⟨hExt, hExtGrad⟩
      have hUnique :
          erealGradientAt (toD x).2.2 = erealGradientAt hExt := by
        exact
          erealGradient_unique
            (ERealDifferentiableAt.eventually_finiteValuedWithin_punctured hExt)
            (ERealDifferentiableAt.hasERealGradientAt ((toD x).2.2))
            (ERealDifferentiableAt.hasERealGradientAt hExt)
      -- Uniqueness removes the dependence on the particular differentiability proof stored in `D`.
      exact hUnique.trans hExtGrad
    simpa [hGradEq] using hGradContC

/-- Corollary 25.5.1: a finite convex function on an open convex set `C` that is differentiable
on all of `C` is continuously differentiable on `C`. -/
theorem convexOn_contDiffOn_one_of_differentiableOn_open
    {n : Nat} {C : Set (Fin n → Real)} {f : (Fin n → Real) → Real}
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (hf : ConvexOn ℝ C f)
    (hdiff : DifferentiableOn ℝ f C) :
    ContDiffOn ℝ 1 f C := by
  by_cases hCempty : C = ∅
  · -- The empty-set case is immediate.
    simp [hCempty]
  · have hgrad :
        ContinuousOn (fun x => euclideanGradientAt f x) C :=
        helperForCorollary_25_5_1_gradient_continuousOn hCopen hCconv hf hdiff
    -- Once gradient continuity is available, the open-set `C¹` criterion is routine.
    exact
      helperForCorollary_25_5_1_contDiffOn_one_of_gradient_continuousOn
        hCopen hdiff hgrad

-- Proof sketch: view the differentiability set as the continuity set of the convex subgradient
-- selection/coordinate directional-derivative data on `interior (dom f)`, then apply the
-- metrizable-space fact that continuity sets are `Gδ`. The equality
-- `D = ⋂ j, D_j` follows from Theorem 25.2 together with the existence of the ordinary partial
-- derivatives furnished by Theorem 25.1.2 at differentiability points.
/-- Helper for Corollary 25.5.2: fixing the direction variable in the upper-semicontinuous
directional-derivative map preserves upper semicontinuity on `int (dom f)`. -/
lemma helperForCorollary_25_5_2_upperSemicontinuousOn_upperDirectionalDerivative_fixedDirection
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    ∀ y : Fin n → Real,
      UpperSemicontinuousOn (fun x => upperDirectionalDerivativeAt f x y) U := by
  intro U y
  have huscPair :
      UpperSemicontinuousOn
        (fun p : (Fin n → Real) × (Fin n → Real) => upperDirectionalDerivativeAt f p.1 p.2)
        (U ×ˢ (Set.univ : Set (Fin n → Real))) :=
    (properConvex_upperSemicontinuousOn_upperDirectionalDerivative_and_subdifferential_subset
      (f := f) hproper).1
  have hcont :
      ContinuousOn (fun x : Fin n → Real => (x, y)) U := by
    intro x hx
    -- The fixed-direction slice is a continuous map into the product domain.
    exact (show ContinuousAt (fun x : Fin n → Real => (x, y)) x by fun_prop).continuousWithinAt
  have hmaps :
      Set.MapsTo (fun x : Fin n → Real => (x, y)) U (U ×ˢ (Set.univ : Set (Fin n → Real))) :=
    fun x hx => ⟨hx, by simp⟩
  -- Compose the product-space upper semicontinuity result with the constant-direction slice.
  simpa [Function.comp] using huscPair.comp hcont hmaps

/-- Helper for Corollary 25.5.2: at interior-domain points, every fixed-direction upper
directional derivative avoids `⊥` as well as `⊤`. -/
lemma helperForCorollary_25_5_2_upperDirectionalDerivative_ne_bot_of_mem_interior
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x : Fin n → Real}
    (hxU : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∀ y : Fin n → Real, upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite :
      f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
    helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
      (f := f) hproper hxU
  have hDirTop :
      ∀ y : Fin n → Real, upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) :=
    helperForTheorem_23_4_directionalDerivative_ne_top_of_mem_interior
      (f := f) hproper x hxU
  have hsymm :
      ∀ y : Fin n → Real,
        -(upperDirectionalDerivativeAt f x (-y)) ≤ upperDirectionalDerivativeAt f x y :=
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite).2.2.2.2
  intro y hyBot
  have htop : (⊤ : EReal) ≤ upperDirectionalDerivativeAt f x (-y) := by
    -- If `f'(x; y)` were `⊥`, the basic convex symmetry inequality would force
    -- `f'(x; -y) = ⊤`, contradicting interior finiteness.
    simpa [hyBot] using hsymm (-y)
  exact hDirTop (-y) (top_le_iff.mp htop)

/-- Helper for Corollary 25.5.2: the coordinate-partial existence set is exactly the zero set of
the sum of the two opposite-direction upper directional derivatives. -/
lemma helperForCorollary_25_5_2_coordinatePartialSet_eq_directionalZeroSet
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    let Dj : Fin n → Set (Fin n → Real) :=
      fun j => {x | x ∈ U ∧ ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal)}
    ∀ j : Fin n,
      Dj j =
        {x |
          x ∈ U ∧
            upperDirectionalDerivativeAt f x (Pi.single j (1 : Real)) +
              upperDirectionalDerivativeAt f x (-Pi.single j (1 : Real)) = 0} := by
  intro U Dj j
  let e : Fin n → Real := Pi.single j (1 : Real)
  ext x
  constructor
  · rintro ⟨hxU, L, hpartial⟩
    have hf : ConvexFunction f := by
      simpa [ConvexFunction] using hproper.1
    have hxFinite :
        f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
      helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
        (f := f) hproper hxU
    rcases helperForTheorem_25_2_basisValues_of_coordinatePartials hf hxFinite j L hpartial with
      ⟨hpos, hneg⟩
    refine ⟨hxU, ?_⟩
    -- A genuine bilateral coordinate derivative forces the two opposite one-sided derivatives to
    -- be exact negatives of one another.
    calc
      upperDirectionalDerivativeAt f x e + upperDirectionalDerivativeAt f x (-e)
          = (L : EReal) + (((-L : Real) : Real) : EReal) := by
            rw [hpos, hneg]
      _ = 0 := by
            rw [← EReal.coe_add]
            norm_num
  · rintro ⟨hxU, hzero⟩
    have hf : ConvexFunction f := by
      simpa [ConvexFunction] using hproper.1
    have hxFinite :
        f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
      helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
        (f := f) hproper hxU
    have hDirTop :
        ∀ y : Fin n → Real, upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) :=
      helperForTheorem_23_4_directionalDerivative_ne_top_of_mem_interior
        (f := f) hproper x hxU
    have hDirBot :
        ∀ y : Fin n → Real, upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal) :=
      helperForCorollary_25_5_2_upperDirectionalDerivative_ne_bot_of_mem_interior
        (f := f) hproper hxU
    lift upperDirectionalDerivativeAt f x e to Real using ⟨hDirTop e, hDirBot e⟩ with r hr
    lift upperDirectionalDerivativeAt f x (-e) to Real using ⟨hDirTop (-e), hDirBot (-e)⟩ with s hs
    have hsumReal : r + s = 0 := by
      -- The zero-set condition is now a real identity because both directional derivatives are
      -- finite at interior-domain points.
      apply EReal.coe_eq_zero.mp
      simpa [e, hr, hs] using hzero
    have hsEq : s = -r := by
      linarith
    have hright :
        Filter.Tendsto (directionalDifferenceQuotientAt f x e)
          (𝓝[>] (0 : Real)) (𝓝 (r : EReal)) := by
      -- The right derivative along `e_j` is always the upper directional derivative.
      simpa [hr] using
        (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite).1 e |>.2.1
    have hrightNeg :
        Filter.Tendsto (directionalDifferenceQuotientAt f x (-e))
          (𝓝[>] (0 : Real)) (𝓝 (s : EReal)) := by
      -- The opposite right derivative is the upper directional derivative in direction `-e_j`.
      simpa [hs] using
        (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite).1 (-e) |>.2.1
    have hleft :
        Filter.Tendsto (directionalDifferenceQuotientAt f x e)
          (𝓝[<] (0 : Real)) (𝓝 (r : EReal)) := by
      -- Rewriting the left quotient along `e_j` through the right quotient along `-e_j`
      -- recovers the same real value because `r + s = 0`.
      have hleftRaw :
          Filter.Tendsto (directionalDifferenceQuotientAt f x e)
            (𝓝[<] (0 : Real)) (𝓝 (-(s : EReal))) :=
        (bilateralDirectionalDerivative_iff_exists_neg_direction
          (f := f) (x := x) (y := e) hxFinite).1 (s : EReal) hrightNeg
      simpa [hsEq] using hleftRaw
    refine ⟨hxU, r, ?_⟩
    -- Combining the right and left limits gives the ordinary two-sided coordinate derivative.
    change
      Filter.Tendsto (directionalDifferenceQuotientAt f x (Pi.single j (1 : Real)))
          (𝓝[>] (0 : Real)) (𝓝 (r : EReal)) ∧
        Filter.Tendsto (directionalDifferenceQuotientAt f x (Pi.single j (1 : Real)))
          (𝓝[<] (0 : Real)) (𝓝 (r : EReal))
    simpa [e] using And.intro hright hleft

/-- Helper for Corollary 25.5.2: the zero set of a nonnegative upper-semicontinuous `EReal`-valued
function on an open set is `Gδ`. -/
lemma helperForCorollary_25_5_2_zeroSet_isGδ_of_nonneg_upperSemicontinuousOn
    {n : Nat} {U : Set (Fin n → Real)} {k : (Fin n → Real) → EReal}
    (hUopen : IsOpen U) (husc : UpperSemicontinuousOn k U)
    (hnonneg : ∀ x ∈ U, (0 : EReal) ≤ k x) :
    IsGδ {x | x ∈ U ∧ k x = 0} := by
  let V : ℕ → Set (Fin n → Real) :=
    fun m => U ∩ k ⁻¹' Set.Iio ((((1 : Real) / (m + 1 : Real) : Real) : EReal))
  have hVopen : ∀ m : ℕ, IsOpen (V m) := by
    intro m
    rcases (upperSemicontinuousOn_iff_preimage_Iio (f := k) (s := U)).1 husc
        ((((1 : Real) / (m + 1 : Real) : Real) : EReal)) with
      ⟨u, huOpen, hEq⟩
    -- Upper semicontinuity makes each small positive sublevel open inside `U`.
    dsimp [V]
    rw [hEq]
    exact hUopen.inter huOpen
  have hEq :
      {x | x ∈ U ∧ k x = 0} = ⋂ m : ℕ, V m := by
    ext x
    constructor
    · rintro ⟨hxU, hxZero⟩
      refine Set.mem_iInter.2 ?_
      intro m
      refine ⟨hxU, ?_⟩
      -- A zero value lies below every positive threshold `1 / (m + 1)`.
      simpa [hxZero] using
        (show (0 : EReal) <
            ((((1 : Real) / (m + 1 : Real) : Real) : Real) : EReal) by
          exact_mod_cast one_div_pos.mpr (show (0 : Real) < (m + 1 : Real) by positivity))
    · intro hxAll
      have hx0 : x ∈ V 0 := Set.mem_iInter.1 hxAll 0
      have hxU : x ∈ U := hx0.1
      have hkNonneg : (0 : EReal) ≤ k x := hnonneg x hxU
      by_cases hkZero : k x = 0
      · exact ⟨hxU, hkZero⟩
      · have hkLtOne : k x < (1 : EReal) := by
          simpa [V] using hx0.2
        have hkNeTop : k x ≠ (⊤ : EReal) := ne_top_of_lt hkLtOne
        have hkNeBot : k x ≠ (⊥ : EReal) := by
          have hbot : (⊥ : EReal) < k x := by
            exact lt_of_lt_of_le (EReal.bot_lt_coe (0 : Real)) hkNonneg
          exact ne_of_gt hbot
        lift k x to Real using ⟨hkNeTop, hkNeBot⟩ with r hr
        have hrNonneg : 0 ≤ r := by
          exact EReal.coe_le_coe_iff.mp (by simpa [hr] using hkNonneg)
        have hrPos : 0 < r := by
          have hrNeZero : r ≠ 0 := by
            intro hrZero
            exact hkZero (by simpa [hr, hrZero])
          exact lt_of_le_of_ne hrNonneg (Ne.symm hrNeZero)
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hrPos
        have hxm : x ∈ V m := Set.mem_iInter.1 hxAll m
        have hkSmall : (r : EReal) <
            ((((1 : Real) / (m + 1 : Real) : Real) : Real) : EReal) := by
          simpa [V, hr] using hxm.2
        have hkSmallReal : r < (1 : Real) / (m + 1 : Real) :=
          EReal.coe_lt_coe_iff.mp hkSmall
        exact False.elim ((not_lt_of_gt hm) hkSmallReal)
  -- Express the zero set as a countable intersection of open positive sublevel sets.
  rw [hEq]
  exact IsGδ.iInter fun m => (hVopen m).isGδ

/-- Helper for Corollary 25.5.2: each coordinate-partial existence set is `Gδ`. -/
lemma helperForCorollary_25_5_2_coordinatePartialSet_isGδ
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    let Dj : Fin n → Set (Fin n → Real) :=
      fun j => {x | x ∈ U ∧ ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal)}
    ∀ j : Fin n, IsGδ (Dj j) := by
  intro U Dj j
  let e : Fin n → Real := Pi.single j (1 : Real)
  let k : (Fin n → Real) → EReal :=
    fun x => upperDirectionalDerivativeAt f x e + upperDirectionalDerivativeAt f x (-e)
  have hDjEq :
      Dj j = {x | x ∈ U ∧ k x = 0} := by
    -- The per-coordinate set is the zero set of the opposite-direction derivative sum.
    simpa [Dj, U, e, k] using
      (helperForCorollary_25_5_2_coordinatePartialSet_eq_directionalZeroSet
        (f := f) hproper) j
  have hkUSC :
      UpperSemicontinuousOn k U := by
    have hUSCPos :
        UpperSemicontinuousOn (fun x => upperDirectionalDerivativeAt f x e) U := by
      simpa [U, e] using
        (helperForCorollary_25_5_2_upperSemicontinuousOn_upperDirectionalDerivative_fixedDirection
          (f := f) hproper) e
    have hUSCNeg :
        UpperSemicontinuousOn (fun x => upperDirectionalDerivativeAt f x (-e)) U := by
      simpa [U, e] using
        (helperForCorollary_25_5_2_upperSemicontinuousOn_upperDirectionalDerivative_fixedDirection
          (f := f) hproper) (-e)
    -- Addition is continuous at the interior-domain values because those directional derivatives
    -- are finite from both sides.
    refine hUSCPos.add' hUSCNeg ?_
    intro x hxU
    have hDirTop :
        ∀ y : Fin n → Real, upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) :=
      helperForTheorem_23_4_directionalDerivative_ne_top_of_mem_interior
        (f := f) hproper x hxU
    have hDirBot :
        ∀ y : Fin n → Real, upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal) :=
      helperForCorollary_25_5_2_upperDirectionalDerivative_ne_bot_of_mem_interior
        (f := f) hproper hxU
    exact EReal.continuousAt_add (Or.inl (hDirTop e)) (Or.inl (hDirBot e))
  have hkNonneg :
      ∀ x ∈ U, (0 : EReal) ≤ k x := by
    intro x hxU
    have hf : ConvexFunction f := by
      simpa [ConvexFunction] using hproper.1
    have hxFinite :
        f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
      helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
        (f := f) hproper hxU
    have hsymm :
        ∀ y : Fin n → Real,
          -(upperDirectionalDerivativeAt f x (-y)) ≤ upperDirectionalDerivativeAt f x y :=
      (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite).2.2.2.2
    have hDirTop :
        ∀ y : Fin n → Real, upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) :=
      helperForTheorem_23_4_directionalDerivative_ne_top_of_mem_interior
        (f := f) hproper x hxU
    have hDirBot :
        ∀ y : Fin n → Real, upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal) :=
      helperForCorollary_25_5_2_upperDirectionalDerivative_ne_bot_of_mem_interior
        (f := f) hproper hxU
    lift upperDirectionalDerivativeAt f x e to Real using ⟨hDirTop e, hDirBot e⟩ with r hr
    lift upperDirectionalDerivativeAt f x (-e) to Real using ⟨hDirTop (-e), hDirBot (-e)⟩ with s hs
    have hsumRealNonneg : 0 ≤ r + s := by
      have hineqReal : -s ≤ r := by
        exact EReal.coe_le_coe_iff.mp (by simpa [hr, hs] using hsymm e)
      linarith
    -- The convex one-dimensional symmetry inequality is exactly the nonnegativity of the sum.
    simpa [k, e, hr, hs, EReal.coe_add] using
      (show ((0 : Real) : EReal) ≤ ((r + s : Real) : EReal) by
        exact_mod_cast hsumRealNonneg)
  -- Apply the generic zero-set lemma to the nonnegative upper-semicontinuous sum.
  rw [hDjEq]
  exact
    helperForCorollary_25_5_2_zeroSet_isGδ_of_nonneg_upperSemicontinuousOn
      isOpen_interior hkUSC hkNonneg

/-- Corollary 25.5.2: for a proper convex function `f` on `ℝ^n`, the set
`D = {x ∈ int (dom f) | f is differentiable at x}` is a `G_δ` set. Moreover, if
`D_j = {x ∈ int (dom f) | the ordinary two-sided partial derivative ∂f(x) / ∂ξ_j exists}`,
then `D = ⋂ j, D_j`, and each `D_j` is a `G_δ` set. -/
theorem properConvexFunction_differentiabilitySet_isGδ_and_coordinatePartialSet_isGδ
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    let D : Set (Fin n → Real) := {x | x ∈ U ∧ ERealDifferentiableAt f x}
    let Dj : Fin n → Set (Fin n → Real) :=
      fun j => {x | x ∈ U ∧ ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal)}
    IsGδ D ∧
      (D = ⋂ j, Dj j) ∧
      (∀ j, IsGδ (Dj j)) := by
  intro U D Dj
  have hD_eq :
      D = ⋂ j, Dj j := by
    -- Theorem 25.5 already identified differentiability with the intersection of the coordinate
    -- partial-existence sets.
    simpa [U, D, Dj] using
      helperForTheorem_25_5_differentiabilitySet_eq_iInter_coordinatePartialSets
        (f := f) hproper
  have hDjGδ : ∀ j : Fin n, IsGδ (Dj j) := by
    -- Each coordinate set is a `Gδ` zero set of a nonnegative upper-semicontinuous function.
    simpa [U, Dj] using
      helperForCorollary_25_5_2_coordinatePartialSet_isGδ
        (f := f) hproper
  have hDGδ : IsGδ D := by
    -- A countable intersection of `Gδ` sets is again `Gδ`; here the index type is finite.
    rw [hD_eq]
    exact IsGδ.iInter hDjGδ
  exact ⟨hDGδ, hD_eq, hDjGδ⟩

/-- The set of all Euclidean gradient vectors that arise as limits of gradients at nearby
differentiability points of `f`. -/
noncomputable def gradientLimitVectorsAt {n : Nat} (f : (Fin n → Real) → EReal)
    (x : Fin n → Real) : Set (Fin n → Real) :=
  {g | ∃ xSeq : ℕ → Fin n → Real,
      ∃ hdiff : ∀ i, ERealDifferentiableAt f (xSeq i),
        Filter.Tendsto xSeq Filter.atTop (nhds x) ∧
          Filter.Tendsto (fun i => erealGradientAt (hdiff i)) Filter.atTop (nhds g)}

/-- Helper for Theorem 25.6: outside the effective domain, both the Euclideanized
subdifferential and the normal-cone term are empty, so the theorem is immediate there. -/
lemma helperForTheorem_25_6_preimage_eq_empty_of_not_mem_effectiveDomain
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → Real)) f)
    {x : Fin n → Real}
    (hx : x ∉ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    ((dotProductEquiv Real (Fin n)) ⁻¹' subdifferentialAt f x) =
      closure (convexHull Real (gradientLimitVectorsAt f x)) +
        ((dotProductEquiv Real (Fin n)) ⁻¹'
          normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x) := by
  have hfxTop : f x = ⊤ := by
    -- Off the effective domain of a univ-defined function, the function value must be `⊤`.
    by_contra hfxTop
    apply hx
    rw [effectiveDomain_eq]
    simp [lt_top_iff_ne_top, hfxTop]
  have hsubEmpty : subdifferentialAt f x = ∅ := by
    ext xStar
    constructor
    · intro hxStar
      rcases hf.1.2 with ⟨x0, hx0Top⟩
      have hineq := hxStar x0
      -- Evaluating the subgradient inequality at a finite point contradicts `f x = ⊤`.
      rw [hfxTop, EReal.top_add_coe] at hineq
      have htopLe : (⊤ : EReal) ≤ f x0 := hineq
      exact (hx0Top <| top_le_iff.mp htopLe)
    · intro hxStar
      simp at hxStar
  have hnormalEmpty :
      ((dotProductEquiv Real (Fin n)) ⁻¹'
          normalConeAt (effectiveDomain (Set.univ : Set (Fin n → Real)) f) x) = ∅ := by
    -- The normal cone is empty away from the base set because membership records `x ∈ dom f`.
    ext v
    simp [Set.preimage, mem_normalConeAt_iff, hx]
  -- Once the normal-cone term vanishes, the Minkowski sum on the right is empty as well.
  rw [hsubEmpty, hnormalEmpty]
  simp


end Section25
end Chap05
