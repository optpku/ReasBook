module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.InnerProductSpace.Calculus

public section

universe u

/-- The affine-line restriction after subtracting its tangent and a quadratic has the
expected first derivative. -/
private lemma hasDerivAt_lineSubQuadratic
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hf : Differentiable ℝ f) (x v : E) (m t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ f (x + s • v) - s * Inner.inner ℝ (gradient f x) v -
        m / (2 : ℝ) * s ^ 2 * ‖v‖ ^ 2)
      (Inner.inner ℝ (gradient f (x + t • v)) v - Inner.inner ℝ (gradient f x) v -
        m * t * ‖v‖ ^ 2) t := by
  -- First differentiate the restriction of `f` to the affine line.
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
    simpa using (hasDerivAt_id' t).smul_const v |>.const_add x
  have hfunction :
      HasDerivAt (fun s : ℝ ↦ f (x + s • v))
        (Inner.inner ℝ (gradient f (x + t • v)) v) t := by
    have hcomp := (hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline
    -- `convert!` identifies the canonical real normed-space instance used by `HasDerivAt`.
    convert! hcomp using 1
    simp only [inner_gradient_left]
  -- The remaining two terms are elementary scalar polynomials.
  have htangent :
      HasDerivAt (fun s : ℝ ↦ s * Inner.inner ℝ (gradient f x) v)
        (Inner.inner ℝ (gradient f x) v) t := by
    simpa only [one_mul] using
      (hasDerivAt_id' t).mul_const (Inner.inner ℝ (gradient f x) v)
  have hquadraticRaw :
      HasDerivAt (fun s : ℝ ↦ m / (2 : ℝ) * s ^ 2 * ‖v‖ ^ 2)
        (m / (2 : ℝ) * (2 * t ^ (2 - 1) * 1) * ‖v‖ ^ 2) t := by
    convert! ((hasDerivAt_id' t).pow 2).const_mul (m / (2 : ℝ)) |>.mul_const (‖v‖ ^ 2)
      using 1
  have hquadratic :
      HasDerivAt (fun s : ℝ ↦ m / (2 : ℝ) * s ^ 2 * ‖v‖ ^ 2)
        (m * t * ‖v‖ ^ 2) t := by
    have hderivative :
        m / (2 : ℝ) * (2 * t ^ (2 - 1) * 1) * ‖v‖ ^ 2 = m * t * ‖v‖ ^ 2 := by
      ring
    exact hquadraticRaw.congr_deriv hderivative
  exact (hfunction.sub htangent).sub hquadratic

/-- The derivative of an adjusted affine-line restriction has derivative equal to the
Hessian quadratic form minus the prescribed quadratic curvature. -/
private lemma hasDerivAt_lineSubQuadraticDerivative
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hgradient : Differentiable ℝ (gradient f))
    (x v : E) (m t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ Inner.inner ℝ (gradient f (x + s • v)) v -
        Inner.inner ℝ (gradient f x) v - m * s * ‖v‖ ^ 2)
      (Inner.inner ℝ (fderiv ℝ (gradient f) (x + t • v) v) v - m * ‖v‖ ^ 2) t := by
  -- Differentiate the gradient along the same affine line.
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
    simpa using (hasDerivAt_id' t).smul_const v |>.const_add x
  have hgradientLine :
      HasDerivAt (fun s : ℝ ↦ gradient f (x + s • v))
        (fderiv ℝ (gradient f) (x + t • v) v) t := by
    simpa only [Function.comp_def] using
      (hgradient (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline
  have hinner :
      HasDerivAt (fun s : ℝ ↦ Inner.inner ℝ (gradient f (x + s • v)) v)
        (Inner.inner ℝ (fderiv ℝ (gradient f) (x + t • v) v) v) t := by
    simpa using hgradientLine.inner ℝ (hasDerivAt_const t v)
  -- Subtracting the fixed tangent and the linear curvature term gives the claimed formula.
  have hlinear :
      HasDerivAt (fun s : ℝ ↦ m * s * ‖v‖ ^ 2) (m * ‖v‖ ^ 2) t := by
    simpa only [mul_one] using
      ((hasDerivAt_id' t).const_mul m).mul_const (‖v‖ ^ 2)
  exact (hinner.sub_const _).sub hlinear

/-- A Hessian lower bound along one affine line makes the tangent- and quadratic-adjusted
restriction convex. -/
private lemma ContDiff.convexOn_lineSubQuadraticOfHessianLowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) (m : ℝ)
    (h_lower : ∀ t : ℝ,
      m * ‖v‖ ^ 2 ≤ Inner.inner ℝ (fderiv ℝ (gradient f) (x + t • v) v) v) :
    ConvexOn ℝ Set.univ
      (fun t : ℝ ↦ f (x + t • v) - t * Inner.inner ℝ (gradient f x) v -
        m / (2 : ℝ) * t ^ 2 * ‖v‖ ^ 2) := by
  -- A `C²` function has a differentiable gradient; keep this bridge in the gradient spelling.
  have horder : 1 + 1 ≤ (2 : WithTop ℕ∞) := by
    norm_num
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right horder
  have hgradientContDiff : ContDiff ℝ 1 (gradient f) := by
    have hgradient_eq : gradient f = fun z ↦
        (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv (fderiv ℝ f z) := by
      funext z
      rfl
    rw [hgradient_eq]
    exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hfderiv
  have hgradient : Differentiable ℝ (gradient f) := hgradientContDiff.differentiable_one
  have htwo_ne : (2 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hfunction : Differentiable ℝ f := hf.differentiable htwo_ne
  -- Feed the two explicit derivative formulas to the scalar second-derivative criterion.
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fun t ↦ Inner.inner ℝ (gradient f (x + t • v)) v -
      Inner.inner ℝ (gradient f x) v - m * t * ‖v‖ ^ 2)
    (f'' := fun t ↦ Inner.inner ℝ (fderiv ℝ (gradient f) (x + t • v) v) v -
      m * ‖v‖ ^ 2) convex_univ ?_ ?_ ?_ ?_
  · exact (continuous_iff_continuousAt.mpr fun t ↦
      (hasDerivAt_lineSubQuadratic hfunction x v m t).continuousAt).continuousOn
  · intro t ht
    simpa only [interior_univ] using
      (hasDerivAt_lineSubQuadratic hfunction x v m t).hasDerivWithinAt
  · intro t ht
    simpa only [interior_univ] using
      (hasDerivAt_lineSubQuadraticDerivative hgradient x v m t).hasDerivWithinAt
  · intro t ht
    exact sub_nonneg.mpr (h_lower t)

/-- A function admitting a supporting affine functional at every point of a convex set is
convex on that set. -/
private lemma convexOn_of_firstOrderInner
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set E} {f : E → ℝ} {g : E → E} (hs : Convex ℝ s)
    (hfirst : ∀ x ∈ s, ∀ y ∈ s,
      f x + Inner.inner ℝ (g x) (y - x) ≤ f y) :
    ConvexOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Apply both supporting inequalities at the convex combination.
  have hz : a • x + b • y ∈ s := hs hx hy ha hb hab
  have hxbound := hfirst (a • x + b • y) hz x hx
  have hybound := hfirst (a • x + b • y) hz y hy
  have hweighted := add_le_add
    (mul_le_mul_of_nonneg_left hxbound ha)
    (mul_le_mul_of_nonneg_left hybound hb)
  -- The weighted displacement from the convex combination is zero, so its inner term cancels.
  have hdisplacement :
      a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) = 0 := by
    have hb_eq : b = 1 - a := by
      linarith
    rw [hb_eq]
    module
  have hinner :
      a * Inner.inner ℝ (g (a • x + b • y)) (x - (a • x + b • y)) +
        b * Inner.inner ℝ (g (a • x + b • y)) (y - (a • x + b • y)) = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right,
      hdisplacement, inner_zero_right]
  simpa only [smul_eq_mul] using
    (calc
      f (a • x + b • y) =
          a * f (a • x + b • y) + b * f (a • x + b • y) := by
        rw [← add_mul, hab, one_mul]
      _ = a * (f (a • x + b • y) +
            Inner.inner ℝ (g (a • x + b • y)) (x - (a • x + b • y))) +
          b * (f (a • x + b • y) +
            Inner.inner ℝ (g (a • x + b • y)) (y - (a • x + b • y))) := by
        rw [mul_add, mul_add]
        linarith
      _ ≤ a * f x + b * f y := hweighted)

/-- A global positive lower bound on the Hessian quadratic form of a twice continuously
differentiable function gives its first-order strong-convexity inequality. -/
theorem ContDiff.firstOrderOfHessianLowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (m : ℝ) (hf : ContDiff ℝ 2 f) (hm : 0 < m)
    (h_lower : ∀ x v : E,
      m * ‖v‖ ^ 2 ≤ Inner.inner ℝ (fderiv ℝ (gradient f) x v) v) :
    ∀ x y : E,
      f x + Inner.inner ℝ (gradient f x) (y - x) +
          m / (2 : ℝ) * ‖y - x‖ ^ 2 ≤ f y := by
  intro x y
  have hm_nonneg : 0 ≤ m := hm.le
  -- Convexity of the adjusted restriction makes its tangent at `0` lie below its value at `1`.
  have hconvex := hf.convexOn_lineSubQuadraticOfHessianLowerBound x (y - x) m
    (fun t ↦ h_lower (x + t • (y - x)) (y - x))
  have htwo_ne : (2 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hfunction : Differentiable ℝ f := hf.differentiable htwo_ne
  have hderivZero :
      HasDerivAt
        (fun t : ℝ ↦ f (x + t • (y - x)) -
          t * Inner.inner ℝ (gradient f x) (y - x) -
          m / (2 : ℝ) * t ^ 2 * ‖y - x‖ ^ 2) 0 0 := by
    simpa using hasDerivAt_lineSubQuadratic hfunction x (y - x) m 0
  have hslope := hconvex.le_slope_of_hasDerivAt
    (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hderivZero
  -- Evaluating the two endpoints turns the scalar slope estimate into the desired inequality.
  simp only [slope_def_field] at hslope
  norm_num at hslope
  simp only [inner_gradient_left, map_sub]
  linarith [hm_nonneg]

/-- A twice continuously differentiable function with a global positive lower bound on
its Hessian quadratic form is strongly convex on the whole space. -/
theorem ContDiff.strongConvexOnOfHessianLowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (m : ℝ) (hf : ContDiff ℝ 2 f) (hm : 0 < m)
    (h_lower : ∀ x v : E, m * ‖v‖ ^ 2 ≤ Inner.inner ℝ (fderiv ℝ (gradient f) x v) v) :
    StrongConvexOn Set.univ m f := by
  -- Shift by the quadratic; the first-order estimate becomes an affine supporting inequality.
  rw [strongConvexOn_iff_convex]
  refine convexOn_of_firstOrderInner
    (g := fun x ↦ gradient f x - m • x) convex_univ ?_
  intro x hx y hy
  have hfirst := hf.firstOrderOfHessianLowerBound f m hm h_lower x y
  have hnorm := norm_add_sq_real x (y - x)
  have hpoint : x + (y - x) = y := by
    abel
  rw [hpoint] at hnorm
  -- The norm-square polarization identity exactly absorbs the quadratic remainder.
  simp only [inner_sub_left, real_inner_smul_left]
  nlinarith
