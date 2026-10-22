/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_39
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_42.Taylor
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Positive

public section

open Asymptotics

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Theorem 2.42: differentiating the restriction of `J` to an affine line rewrites
the derivative in gradient form. -/
lemma hasDerivAt_lineRestriction (J : H → ℝ) {x y : H} {t : ℝ}
    (hJt : ContDiffAt ℝ 2 J (AffineMap.lineMap x y t)) :
    HasDerivAt (fun r : ℝ ↦ J (AffineMap.lineMap x y r))
      (inner ℝ (gradient J (AffineMap.lineMap x y t)) (y - x)) t := by
  -- Differentiate `J` through the affine line map.
  have hcomp :
      HasDerivAt (fun r : ℝ ↦ J (AffineMap.lineMap x y r))
        ((fderiv ℝ J (AffineMap.lineMap x y t)) (y - x)) t := by
    exact (hJt.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap
  -- Rewrite the Fréchet derivative using the gradient.
  convert hcomp using 1
  rw [← inner_gradient_left (f := J) (x := AffineMap.lineMap x y t) (y := y - x)]

/-- Helper for Theorem 2.42: the derivative of the segment-gradient is the Hessian quadratic form
along the segment direction. -/
lemma hasDerivAt_segmentGradient (J : H → ℝ) {x y : H} {t : ℝ}
    (hJt : ContDiffAt ℝ 2 J (AffineMap.lineMap x y t)) :
    HasDerivAt (fun r : ℝ ↦ inner ℝ (gradient J (AffineMap.lineMap x y r)) (y - x))
      (inner ℝ (hessian J (AffineMap.lineMap x y t) (y - x)) (y - x)) t := by
  -- Differentiate the Fréchet derivative of `J` along the line.
  rcases hasSecondDerivativeData_of_contDiffAt J (AffineMap.lineMap x y t) hJt with ⟨_, hJ₂⟩
  have hcomp :
      HasDerivAt (fun r : ℝ ↦ fderiv ℝ J (AffineMap.lineMap x y r))
        ((fderiv ℝ (fderiv ℝ J) (AffineMap.lineMap x y t)) (y - x)) t := by
    exact hJ₂.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
  have happly :
      HasDerivAt (fun r : ℝ ↦ (fderiv ℝ J (AffineMap.lineMap x y r)) (y - x))
        (((fderiv ℝ (fderiv ℝ J) (AffineMap.lineMap x y t)) (y - x)) (y - x)) t := by
    simpa using hcomp.clm_apply (hasDerivAt_const t (y - x))
  -- Rewrite both the first and second derivatives through gradient and Hessian.
  convert happly using 1
  · ext r
    rw [← inner_gradient_left (f := J) (x := AffineMap.lineMap x y r) (y := y - x)]
  · rw [← hessian_inner J (AffineMap.lineMap x y t) (y - x) (y - x)]

/-- Helper for Theorem 2.42: positive-semidefinite Hessians make the gradient monotone on `C`. -/
lemma gradientMonotoneOn_of_hessian_isPositive (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hOpen : IsOpen C) (hJ : ContDiffOn ℝ 2 J C)
    (hHess : ∀ f ∈ C, (hessian J f).IsPositive) :
    GradientMonotoneOn J C := by
  rw [gradientMonotoneOn_iff]
  intro f₁ f₂ hf₁ hf₂
  let g : ℝ → ℝ := fun t ↦ inner ℝ (gradient J (AffineMap.lineMap f₂ f₁ t)) (f₁ - f₂)
  have hgCont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    -- The segment-gradient is differentiable at every point of the closed interval.
    exact (hasDerivAt_segmentGradient J
      (hJ.contDiffAt (hOpen.mem_nhds (hC.lineMap_mem hf₂ hf₁ ht)))).continuousAt.continuousWithinAt
  have hgMono : MonotoneOn g (Set.Icc (0 : ℝ) 1) := by
    -- Nonnegative Hessian quadratic forms force monotonicity of the segment-gradient.
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t ↦
      inner ℝ (hessian J (AffineMap.lineMap f₂ f₁ t) (f₁ - f₂)) (f₁ - f₂))
      (convex_Icc (0 : ℝ) 1) hgCont
      ?_ ?_
    · intro t ht
      exact (hasDerivAt_segmentGradient J
        (hJ.contDiffAt
          (hOpen.mem_nhds (hC.lineMap_mem hf₂ hf₁ (interior_subset ht))))).hasDerivWithinAt
    · intro t ht
      exact (hHess _ (hC.lineMap_mem hf₂ hf₁ (interior_subset ht))).inner_nonneg_left (f₁ - f₂)
  have h01 : g 0 ≤ g 1 := hgMono (by simp) (by simp) zero_le_one
  -- Evaluate the monotonicity inequality at the segment endpoints.
  simpa [g, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, inner_sub_left, sub_nonneg]
    using h01

/-- Helper for Theorem 2.42: strictly positive Hessian quadratic forms make the gradient strictly
monotone on `C`. -/
lemma gradientStrictMonotoneOn_of_hessian_inner_pos (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hOpen : IsOpen C) (hJ : ContDiffOn ℝ 2 J C)
    (hHess : ∀ f ∈ C, ∀ v : H, v ≠ 0 → 0 < inner ℝ (hessian J f v) v) :
    GradientStrictMonotoneOn J C := by
  rw [gradientStrictMonotoneOn_iff]
  intro f₁ f₂ hf₁ hf₂ hf₁₂
  let g : ℝ → ℝ := fun t ↦ inner ℝ (gradient J (AffineMap.lineMap f₂ f₁ t)) (f₁ - f₂)
  have hgCont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    -- The segment-gradient remains differentiable all along the closed interval.
    exact (hasDerivAt_segmentGradient J
      (hJ.contDiffAt (hOpen.mem_nhds (hC.lineMap_mem hf₂ hf₁ ht)))).continuousAt.continuousWithinAt
  have hdir : f₁ - f₂ ≠ 0 := sub_ne_zero.mpr hf₁₂
  have hgStrict : StrictMonoOn g (Set.Icc (0 : ℝ) 1) := by
    -- Strict positivity of the Hessian quadratic form gives strict growth of the segment-gradient.
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun t ↦
      inner ℝ (hessian J (AffineMap.lineMap f₂ f₁ t) (f₁ - f₂)) (f₁ - f₂))
      (convex_Icc (0 : ℝ) 1) hgCont
      ?_ ?_
    · intro t ht
      exact (hasDerivAt_segmentGradient J
        (hJ.contDiffAt
          (hOpen.mem_nhds (hC.lineMap_mem hf₂ hf₁ (interior_subset ht))))).hasDerivWithinAt
    · intro t ht
      exact hHess _ (hC.lineMap_mem hf₂ hf₁ (interior_subset ht)) (f₁ - f₂) hdir
  have h01 : g 0 < g 1 := hgStrict (by simp) (by simp) zero_lt_one
  -- Evaluate the strict monotonicity inequality at the segment endpoints.
  simpa [g, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, inner_sub_left, sub_pos]
    using h01

/-- Helper for Theorem 2.42: convexity forces the Hessian to be positive at every point of `C`. -/
lemma hessian_isPositive_of_convexOn (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hOpen : IsOpen C) (hJ : ContDiffOn ℝ 2 J C)
    (hconv : ConvexOn ℝ C J) :
    ∀ f ∈ C, (hessian J f).IsPositive := by
  intro f hf
  have hJf : ContDiffAt ℝ 2 J f := hJ.contDiffAt (hOpen.mem_nhds hf)
  refine (ContinuousLinearMap.isPositive_iff' (hessian J f)).2 ?_
  constructor
  · -- A `C²` functional has a self-adjoint Hessian.
    exact hessian_isSelfAdjoint_of_contDiffAt J f hJf
  · intro v
    by_cases hv : v = 0
    · -- The quadratic form vanishes on the zero vector.
      simp [hv]
    · -- Route correction: rather than using the Taylor expansion, restrict `J` to a short segment
      -- inside `C` and differentiate the convex line restriction at its left endpoint.
      obtain ⟨ε, hεpos, hεC⟩ := Metric.mem_nhds_iff.mp (hOpen.mem_nhds hf)
      have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let δ : ℝ := ε / (2 * ‖v‖)
      have hδpos : 0 < δ := by
        dsimp [δ]
        positivity
      have hδmul : δ * ‖v‖ = ε / 2 := by
        dsimp [δ]
        field_simp [hvnorm.ne']
      have hy : f + δ • v ∈ C := by
        apply hεC
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        calc
          ‖δ • v‖ = |δ| * ‖v‖ := norm_smul _ _
          _ = δ * ‖v‖ := by rw [abs_of_pos hδpos]
          _ = ε / 2 := hδmul
          _ < ε := by linarith
      let y : H := f + δ • v
      let j : ℝ → ℝ := J ∘ AffineMap.lineMap f y
      let g : ℝ → ℝ := fun t ↦ inner ℝ (gradient J (AffineMap.lineMap f y t)) (y - f)
      have hpre :
          Set.Icc (0 : ℝ) 1 ⊆ (AffineMap.lineMap f y) ⁻¹' C := by
        intro t ht
        exact hC.lineMap_mem hf hy ht
      have hjConvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) j := by
        -- Restrict the convex functional to the short segment joining `f` and `y`.
        simpa [j] using
          (hconv.comp_affineMap (AffineMap.lineMap f y)).subset hpre (convex_Icc (0 : ℝ) 1)
      have hjDiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ j t := by
        intro t ht
        -- Every point of the segment stays in `C`, so the restriction is differentiable there.
        simpa [j, Function.comp_def] using
          ((hJ.contDiffAt (hOpen.mem_nhds (hC.lineMap_mem hf hy ht))).differentiableAt
            (by norm_num)).comp t (AffineMap.lineMap f y).differentiableAt
      have hderivEq : Set.EqOn (deriv j) g (Set.Icc (0 : ℝ) 1) := by
        intro t ht
        -- Identify the derivative of the line restriction with the segment-gradient.
        exact (hasDerivAt_lineRestriction J
          (hJ.contDiffAt (hOpen.mem_nhds (hC.lineMap_mem hf hy ht)))).deriv
      have hgMono : MonotoneOn g (Set.Icc (0 : ℝ) 1) := by
        -- Convexity of the restriction implies monotonicity of its derivative.
        intro s hs t ht hst
        simpa [hderivEq hs, hderivEq ht] using (hjConvex.monotoneOn_deriv hjDiff hs ht hst)
      have hacc : AccPt (0 : ℝ) (Filter.principal (Set.Icc (0 : ℝ) 1)) := by
        exact (uniqueDiffOn_Icc zero_lt_one 0 (by simp)).accPt
      have hnonnegSeg :
          0 ≤ inner ℝ (hessian J f (y - f)) (y - f) := by
        -- The derivative of a monotone segment-gradient is nonnegative at the left endpoint.
        simpa [g, AffineMap.lineMap_apply_zero] using
          (hasDerivAt_segmentGradient (J := J) (x := f) (y := y) (t := 0)
            (by simpa using hJf)).hasDerivWithinAt.nonneg_of_monotoneOn hacc hgMono
      have hyf : y - f = δ • v := by
        simp [y]
      have hscale :
          inner ℝ (hessian J f (y - f)) (y - f) = δ ^ 2 * inner ℝ (hessian J f v) v := by
        calc
          inner ℝ (hessian J f (y - f)) (y - f)
              = inner ℝ (hessian J f (δ • v)) (δ • v) := by rw [hyf]
          _ = inner ℝ (δ • hessian J f v) (δ • v) := by rw [map_smul]
          _ = δ * inner ℝ (hessian J f v) (δ • v) := by
                rw [real_inner_smul_left]
          _ = δ * (δ * inner ℝ (hessian J f v) v) := by rw [inner_smul_right]
          _ = δ ^ 2 * inner ℝ (hessian J f v) v := by ring
      have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδpos
      have hscaled : 0 ≤ δ ^ 2 * inner ℝ (hessian J f v) v := by
        rw [← hscale]
        exact hnonnegSeg
      nlinarith

/-- Theorem 2.42 (1). Let `J` be twice Fréchet differentiable on a convex open set `C`.
Then `J` is convex on `C` if and only if `hessian J f` is positive
semidefinite for every `f ∈ C`. -/
theorem convexOn_iff_hessian_isPositive (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hOpen : IsOpen C) (hJ : ContDiffOn ℝ 2 J C) :
    ConvexOn ℝ C J ↔ ∀ f ∈ C, (hessian J f).IsPositive := by
  have hDiff : ∀ x ∈ C, DifferentiableAt ℝ J x := by
    intro x hx
    -- The `C²` hypothesis supplies the differentiability needed by Theorem 2.39.
    exact (hJ.contDiffAt (hOpen.mem_nhds hx)).differentiableAt (by norm_num)
  constructor
  · -- Convexity implies Hessian positivity pointwise.
    intro hconv
    exact hessian_isPositive_of_convexOn J hC hOpen hJ hconv
  · -- Positive Hessians imply convexity via gradient monotonicity.
    intro hHess
    exact (convexOn_iff_gradientMonotoneOn J hC hDiff).2
      (gradientMonotoneOn_of_hessian_isPositive J hC hOpen hJ hHess)

/-- Interior-point reformulation of Theorem 2.42 (1). For an open set `C`,
the source condition `f ∈ interior C` is equivalent to `f ∈ C`. -/
theorem convexOn_iff_hessian_isPositiveOnInterior (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hOpen : IsOpen C) (hJ : ContDiffOn ℝ 2 J C) :
    ConvexOn ℝ C J ↔ ∀ f ∈ interior C, (hessian J f).IsPositive := by
  simpa [hOpen.interior_eq] using convexOn_iff_hessian_isPositive J hC hOpen hJ

/-- Theorem 2.42 (2). Let `J` be twice Fréchet differentiable on a convex open set `C`.
If the quadratic form of `hessian J f` is strictly positive on nonzero vectors
for every `f ∈ C`, then `J` is strictly convex on `C`. -/
theorem strictConvexOn_of_hessian_inner_pos (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hOpen : IsOpen C) (hJ : ContDiffOn ℝ 2 J C)
    (hHess : ∀ f ∈ C, ∀ v : H, v ≠ 0 → 0 < inner ℝ (hessian J f v) v) :
    StrictConvexOn ℝ C J := by
  have hDiff : ∀ x ∈ C, DifferentiableAt ℝ J x := by
    intro x hx
    -- The `C²` hypothesis supplies the differentiability needed by Theorem 2.39.
    exact (hJ.contDiffAt (hOpen.mem_nhds hx)).differentiableAt (by norm_num)
  -- Strict positivity of the Hessian makes the gradient strictly monotone, hence `J` strictly
  -- convex by the Chapter 2 gradient criterion.
  exact (strictConvexOn_iff_gradientStrictMonotoneOn J hC hDiff).2
    (gradientStrictMonotoneOn_of_hessian_inner_pos J hC hOpen hJ hHess)

/-- Interior-point reformulation of Theorem 2.42 (2). For an open set `C`,
the source condition `f ∈ interior C` is equivalent to `f ∈ C`. -/
theorem strictConvexOn_of_hessian_inner_posOnInterior (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hOpen : IsOpen C) (hJ : ContDiffOn ℝ 2 J C)
    (hHess : ∀ f ∈ interior C, ∀ v : H, v ≠ 0 → 0 < inner ℝ (hessian J f v) v) :
    StrictConvexOn ℝ C J := by
  apply strictConvexOn_of_hessian_inner_pos J hC hOpen hJ
  intro f hf v hv
  exact hHess f (by simpa [hOpen.interior_eq] using hf) v hv

/-- Theorem 2.42 (3). If `J` is twice Fréchet differentiable at `f`, then
`J (f + h) = J f + inner ℝ (gradient J f) h +
(1 / 2 : ℝ) * inner ℝ (hessian J f h) h + r h`
for some remainder `r` satisfying `r =o[nhds (0 : H)] (fun h ↦ ‖h‖ ^ 2)`. -/
theorem secondOrderTaylorFormulaAt_of_contDiffAt (J : H → ℝ) (f : H)
    (hJ : ContDiffAt ℝ 2 J f) :
    ∃ r : H → ℝ,
      r =o[nhds (0 : H)] (fun h ↦ ‖h‖ ^ 2) ∧
      ∀ h : H,
        J (f + h) = J f + inner ℝ (gradient J f) h +
          (1 / 2 : ℝ) * inner ℝ (hessian J f h) h + r h := by
  rcases hasSecondDerivativeData_of_contDiffAt J f hJ with ⟨hJ₁, hJ₂⟩
  exact secondOrderTaylorFormulaAt J f hJ₁ hJ₂
