module

public import ReasLib.Optimization.BFGS.MinimumQOrder
public import ReasLib.Optimization.Broyden.Trajectory

public section

namespace BFGS.IsOrderOneExample

variable {n : ℕ} {ε R : ℝ}
variable {F : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
variable {x : ℕ → EuclideanSpace ℝ (Fin n)} {B : ℕ → Matrix (Fin n) (Fin n) ℝ}
variable {α : ℕ → ℝ}

/-- Positive rescaling of a search direction inversely rescales its exact-search
parameter. -/
private theorem exactLineSearch_smul_iff
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (F : E → ℝ) (z d : E) (a c : ℝ) (hc : 0 < c) :
    LineSearch.IsExact F z (c • d) a ↔ LineSearch.IsExact F z d (c * a) := by
  -- Rewrite both ray-minimization problems by the order isomorphism `t ↦ c * t`.
  rw [LineSearch.isExact_iff, LineSearch.isExact_iff]
  constructor
  · rintro ⟨ha, hmin⟩
    refine ⟨mul_nonneg hc.le ha, ?_⟩
    intro t ht
    have htDiv : 0 ≤ t / c := div_nonneg ht hc.le
    have hbound := hmin htDiv
    calc
      F (z + (c * a) • d) = F (z + a • (c • d)) := by
        rw [smul_smul, mul_comm]
      _ ≤ F (z + (t / c) • (c • d)) := hbound
      _ = F (z + t • d) := by
        rw [smul_smul, div_mul_cancel₀ t hc.ne']
  · rintro ⟨hca, hmin⟩
    have hcNonneg : 0 ≤ c := hc.le
    have ha : 0 ≤ a := by
      apply nonneg_of_mul_nonneg_left
      · simpa only [mul_comm] using hca
      · exact hc
    refine ⟨ha, ?_⟩
    intro t ht
    have hct : 0 ≤ c * t := mul_nonneg hcNonneg ht
    have hbound := hmin hct
    calc
      F (z + a • c • d) = F (z + (c * a) • d) := by
        rw [smul_smul, mul_comm]
      _ ≤ F (z + (c * t) • d) := hbound
      _ = F (z + t • c • d) := by
        rw [smul_smul, mul_comm]

/-- A differentiable objective restricted to an affine ray has derivative given by
pairing its gradient with the ray direction. -/
private theorem hasDerivAt_line
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : E → ℝ} (hF : Differentiable ℝ F) (z d : E) (t : ℝ) :
    HasDerivAt (fun a : ℝ ↦ F (z + a • d))
      (inner ℝ (gradient F (z + t • d)) d) t := by
  -- Apply the chain rule to the affine parametrization of the ray.
  have hOuter := hF.differentiableAt
    (x := AffineMap.lineMap z (z + d) t) |>.hasGradientAt.hasFDerivAt
  have hInner : HasDerivAt (AffineMap.lineMap z (z + d)) d t := by
    simpa only [add_sub_cancel_left] using
      (AffineMap.hasDerivAt_lineMap (a := z) (b := z + d) (x := t))
  have hChain := hOuter.comp_hasDerivAt t hInner
  have hLineFunction : F ∘ AffineMap.lineMap z (z + d) =
      fun a : ℝ ↦ F (z + a • d) := by
    funext a
    simp only [Function.comp_apply, AffineMap.lineMap_apply_module', add_sub_cancel_left]
    rw [add_comm]
  have hLinePoint : AffineMap.lineMap z (z + d) t = z + t • d := by
    simp only [AffineMap.lineMap_apply_module', add_sub_cancel_left]
    rw [add_comm]
  rw [hLineFunction, hLinePoint] at hChain
  simpa only [InnerProductSpace.toDual_apply_apply] using hChain

/-- A differentiable convex objective with zero gradient is globally minimized at that
point. -/
private theorem isMinOn_univ_of_gradient_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : E → ℝ} (hF : Differentiable ℝ F) (hconvex : ConvexOn ℝ Set.univ F)
    {z : E} (hz : gradient F z = 0) : IsMinOn F Set.univ z := by
  -- Minimize on every affine line through `z`, where the derivative at zero vanishes.
  intro w _
  let f : ℝ → ℝ := fun t ↦ F (z + t • (w - z))
  have hLine (t : ℝ) : AffineMap.lineMap z w t = z + t • (w - z) := by
    rw [AffineMap.lineMap_apply_module']
    exact add_comm _ _
  have hfConvex : ConvexOn ℝ Set.univ f := by
    have hcomp := hconvex.comp_affineMap (AffineMap.lineMap z w)
    have hLineFunction : F ∘ AffineMap.lineMap z w = f := by
      funext t
      exact congrArg F (hLine t)
    rw [hLineFunction] at hcomp
    simpa only [Set.preimage_univ] using hcomp
  have hDerivative : HasDerivAt f 0 0 := by
    have hLine := hasDerivAt_line hF z (w - z) 0
    simpa only [f, zero_smul, add_zero, hz, inner_zero_left] using hLine
  have hRight : derivWithin f (Set.Ioi 0) 0 = 0 := by
    rw [hDerivative.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0)]
  have hZeroInterior : (0 : ℝ) ∈ interior Set.univ := by
    rw [interior_univ]
    exact Set.mem_univ 0
  have hMinimum : IsMinOn f Set.univ 0 :=
    hfConvex.isMinOn_of_rightDeriv_eq_zero hZeroInterior hRight
  have hOneMem : (1 : ℝ) ∈ Set.univ := Set.mem_univ 1
  have hOne := hMinimum hOneMem
  have hEndpoint : z + (w - z) = w := by abel
  dsimp only [f] at hOne
  have hOne' : F z ≤ F (z + (1 : ℝ) • (w - z)) := by
    simpa only [Set.mem_setOf_eq, zero_smul, add_zero] using hOne
  calc
    F z ≤ F (z + (1 : ℝ) • (w - z)) := hOne'
    _ = F w := by rw [one_smul, hEndpoint]

/-- Strict convexity makes exact line-search parameters unique on a nonzero ray. -/
private theorem exactLineSearch_parameter_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → ℝ} (hstrict : StrictConvexOn ℝ Set.univ F)
    {z d : E} (hd : d ≠ 0) {a b : ℝ}
    (ha : LineSearch.IsExact F z d a) (hb : LineSearch.IsExact F z d b) : a = b := by
  -- Pull strict convexity back along the injective affine parametrization of the ray.
  let f : ℝ → ℝ := F ∘ AffineMap.lineMap z (z + d)
  have hEndpointsNe : z ≠ z + d := by
    intro hzd
    apply hd
    calc
      d = (z + d) - z := by abel
      _ = z - z := by rw [← hzd]
      _ = 0 := sub_self z
  have hLineInjective :
      Function.Injective (AffineMap.lineMap (k := ℝ) z (z + d)) := by
    exact AffineMap.lineMap_injective (V1 := E) (P1 := E) ℝ hEndpointsNe
  have hfStrict : StrictConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro r _ t _ hrt c e hc he hce
    have hImageNe : AffineMap.lineMap z (z + d) r ≠
        AffineMap.lineMap z (z + d) t := hLineInjective.ne hrt
    have h := hstrict.2 (Set.mem_univ _) (Set.mem_univ _) hImageNe hc he hce
    simpa only [f, Function.comp_apply, Convex.combo_affine_apply hce] using h
  have hLine (t : ℝ) : AffineMap.lineMap z (z + d) t = z + t • d := by
    rw [AffineMap.lineMap_apply_module']
    module
  have hfLine : f = fun t : ℝ ↦ F (z + t • d) := by
    funext t
    exact congrArg F (hLine t)
  have haData := (LineSearch.isExact_iff F z d a).mp ha
  have hbData := (LineSearch.isExact_iff F z d b).mp hb
  have haMin : IsMinOn f (Set.Ici 0) a := by
    rw [hfLine]
    exact haData.2
  have hbMin : IsMinOn f (Set.Ici 0) b := by
    rw [hfLine]
    exact hbData.2
  have hfRay : StrictConvexOn ℝ (Set.Ici 0) f := by
    refine ⟨convex_Ici 0, ?_⟩
    intro r _ t _ hrt c e hc he hce
    exact hfStrict.2 (Set.mem_univ _) (Set.mem_univ _) hrt hc he hce
  exact hfRay.eq_of_isMinOn haMin hbMin haData.1 hbData.1

/-- A nonnegative stationary point of a differentiable convex ray restriction is an
exact line-search parameter. -/
private theorem exactLineSearch_of_inner_gradient_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : E → ℝ) (hF : Differentiable ℝ F) (hconvex : ConvexOn ℝ Set.univ F)
    (z d : E) {a : ℝ} (ha : 0 ≤ a)
    (hstationary : inner ℝ (gradient F (z + a • d)) d = 0) :
    LineSearch.IsExact F z d a := by
  -- Convexity upgrades the vanishing derivative of the line restriction to global minimality.
  let f : ℝ → ℝ := F ∘ AffineMap.lineMap z (z + d)
  have hLine (t : ℝ) : AffineMap.lineMap z (z + d) t = z + t • d := by
    rw [AffineMap.lineMap_apply_module']
    module
  have hfEq : f = fun t : ℝ ↦ F (z + t • d) := by
    funext t
    exact congrArg F (hLine t)
  have hfConvex : ConvexOn ℝ Set.univ f := by
    simpa only [Set.preimage_univ] using
      hconvex.comp_affineMap (AffineMap.lineMap z (z + d))
  have hDerivative : HasDerivAt f (inner ℝ (gradient F (z + a • d)) d) a := by
    rw [hfEq]
    exact hasDerivAt_line hF z d a
  have hRight : derivWithin f (Set.Ioi a) a = 0 := by
    rw [hDerivative.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi a), hstationary]
  have haInterior : a ∈ interior Set.univ := by
    rw [interior_univ]
    exact Set.mem_univ a
  have hMinimumUniv : IsMinOn f Set.univ a :=
    hfConvex.isMinOn_of_rightDeriv_eq_zero haInterior hRight
  refine (LineSearch.isExact_iff F z d a).mpr ⟨ha, ?_⟩
  rw [← hfEq]
  exact hMinimumUniv.on_subset (Set.subset_univ _)

/-- On a differentiable strictly convex objective, the gradient difference has positive
pairing with every nontrivial chord. -/
private theorem innerGradientSubPosOfStrictConvexOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : E → ℝ) (hF : Differentiable ℝ F)
    (hstrict : StrictConvexOn ℝ Set.univ F) {a b : E} (hab : a ≠ b) :
    0 < inner ℝ (gradient F b - gradient F a) (b - a) := by
  -- Compare the endpoint derivatives of the strictly convex line restriction.
  let f : ℝ → ℝ := F ∘ AffineMap.lineMap a b
  have hfStrict : StrictConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro r _ t _ hrt c d hc hd hcd
    have hLineNe : AffineMap.lineMap a b r ≠ AffineMap.lineMap a b t :=
      (AffineMap.lineMap_injective ℝ hab).ne hrt
    have h := hstrict.2 (Set.mem_univ _) (Set.mem_univ _) hLineNe hc hd hcd
    simpa only [f, Function.comp_apply, Convex.combo_affine_apply hcd] using h
  have hfDifferentiable : Differentiable ℝ f :=
    hF.comp (AffineMap.lineMap a b).differentiable
  have hfDeriv (t : ℝ) :
      deriv f t = inner ℝ (gradient F (AffineMap.lineMap a b t)) (b - a) := by
    have hOuter := hF.differentiableAt
      (x := AffineMap.lineMap a b t) |>.hasGradientAt.hasFDerivAt
    have hInner : HasDerivAt (AffineMap.lineMap a b) (b - a) t :=
      AffineMap.hasDerivAt_lineMap
    have hChain := hOuter.comp_hasDerivAt t hInner
    rw [hChain.deriv]
    rfl
  have hMono := hfStrict.strictMonoOn_deriv
    (fun t _ ↦ hfDifferentiable.differentiableAt)
    (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
  rw [hfDeriv 0, hfDeriv 1, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] at hMono
  simpa only [inner_sub_left, sub_pos] using hMono

/-- Every step of a nonterminating exact-search BFGS trajectory has positive length,
the secant equation before updating, exact-search orthogonality, and positive curvature. -/
private theorem bfgsStepGeometry
    (h : BFGS.IsOrderOneExample ε R F x₀ x B α) (k : ℕ) :
    0 < α k ∧
      BFGS.searchDirection (B k) (gradient F (x k)) ≠ 0 ∧
      x (k + 1) - x k =
        α k • BFGS.searchDirection (B k) (gradient F (x k)) ∧
      Matrix.mulVec (B k) (x (k + 1) - x k).ofLp =
        -(α k • gradient F (x k)).ofLp ∧
      inner ℝ (gradient F (x (k + 1))) (x (k + 1) - x k) = 0 ∧
      0 < dotProduct (x (k + 1) - x k).ofLp
        (gradient F (x (k + 1)) - gradient F (x k)).ofLp := by
  -- Read the BFGS recurrence and exact-search law from the bundled trajectory.
  have hRun := (BFGS.isTrajectory_iff F 1 x B α).mp h.trajectory
  have hF : Differentiable ℝ F := hRun.2.1
  obtain ⟨m, hm, hStrong⟩ := h.strongConvex
  have hStrict : StrictConvexOn ℝ Set.univ F := hStrong.strictConvexOn hm
  have hConvex : ConvexOn ℝ Set.univ F := hStrict.convexOn
  let g : EuclideanSpace ℝ (Fin n) := gradient F (x k)
  let d : EuclideanSpace ℝ (Fin n) := BFGS.searchDirection (B k) g
  let s : EuclideanSpace ℝ (Fin n) := x (k + 1) - x k
  have hg : g ≠ 0 := by
    intro hgZero
    have hMin : IsMinOn F Set.univ (x k) :=
      isMinOn_univ_of_gradient_eq_zero hF hConvex hgZero
    have hxZero : x k = 0 := (h.uniqueMinimizer (x k)).mp hMin
    exact h.nonterminating k hxZero
  have hBpos : (B k).PosDef := hRun.2.2.1 k
  have hDirectionSpec := BFGS.searchDirection_spec hBpos g
  have hDirectionSpec' : Matrix.mulVec (B k) d.ofLp = -g.ofLp := by
    simpa only [d, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
      hDirectionSpec
  have hd : d ≠ 0 := by
    intro hdZero
    have hdOf : d.ofLp = 0 := by
      simpa only [WithLp.ofLp_zero] using congrArg WithLp.ofLp hdZero
    rw [hdOf, Matrix.mulVec_zero] at hDirectionSpec'
    have hgOf : g.ofLp = 0 := neg_eq_zero.mp hDirectionSpec'.symm
    apply hg
    apply WithLp.ofLp_injective 2
    simpa only [WithLp.ofLp_zero] using hgOf
  have hDescent : inner ℝ g d < 0 := by
    have hPositive := BFGS.quadraticDenominator_pos hBpos hd
    have hPair : dotProduct d.ofLp (Matrix.mulVec (B k) d.ofLp) =
        -inner ℝ g d := by
      rw [hDirectionSpec']
      simp only [dotProduct_neg, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    linarith
  have hExact := hRun.2.2.2.1 k
  have hExactData := (LineSearch.isExact_iff F (x k) d (α k)).mp hExact
  have hα : 0 < α k := by
    refine lt_of_le_of_ne hExactData.1 ?_
    intro hαZero
    have hαEq : α k = 0 := hαZero.symm
    have hDerivative := hasDerivAt_line hF (x k) d 0
    have hCone : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) 0 := by
      apply mem_posTangentConeAt_of_segment_subset
      simp only [zero_add]
      rw [segment_eq_Icc zero_le_one]
      exact Set.Icc_subset_Ici_self
    have hMinZero : IsMinOn (fun t : ℝ ↦ F (x k + t • d)) (Set.Ici 0) 0 := by
      simpa only [hαEq] using hExactData.2
    have hNonnegative := hMinZero.localize.hasFDerivWithinAt_nonneg
      hDerivative.hasFDerivAt.hasFDerivWithinAt hCone
    have hNonnegative' : 0 ≤ inner ℝ g d := by
      simpa only [g, zero_smul, add_zero, ContinuousLinearMap.toSpanSingleton_apply,
        one_smul] using hNonnegative
    exact (not_lt_of_ge hNonnegative' hDescent)
  have hs : s = α k • d := by
    dsimp only [s, d]
    rw [hRun.2.2.2.2.1 k]
    abel
  have hBs : Matrix.mulVec (B k) s.ofLp = -(α k • g).ofLp := by
    rw [hs]
    simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, hDirectionSpec', smul_neg]
  have hStationaryDirection : inner ℝ (gradient F (x (k + 1))) d = 0 := by
    have hDerivative := hasDerivAt_line hF (x k) d (α k)
    rw [← hRun.2.2.2.2.1 k] at hDerivative
    have hLocal := hExactData.2.isLocalMin (Ici_mem_nhds hα)
    exact hLocal.hasDerivAt_eq_zero hDerivative
  have hOrthogonal : inner ℝ (gradient F (x (k + 1))) s = 0 := by
    rw [hs, inner_smul_right, hStationaryDirection, mul_zero]
  have hxDistinct : x k ≠ x (k + 1) := by
    intro hx
    have hsZero : s = 0 := sub_eq_zero.mpr hx.symm
    rw [hs, smul_eq_zero] at hsZero
    exact hd (hsZero.resolve_left hα.ne')
  have hCurvature : 0 < inner ℝ
      (gradient F (x (k + 1)) - gradient F (x k)) s := by
    exact innerGradientSubPosOfStrictConvexOn F hF hStrict hxDistinct
  refine ⟨hα, hd, hs, hBs, hOrthogonal, ?_⟩
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hCurvature

/-- Under exact-search orthogonality, a convex-Broyden update is the BFGS update
plus an explicit rank-one correction in the new gradient. -/
private theorem broydenUpdate_eq_bfgsUpdate_add_rankOne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {s g y : EuclideanSpace ℝ ι} {a φ : ℝ}
    (hCs : Matrix.mulVec C s.ofLp = -(a • g).ofLp)
    (horth : dotProduct s.ofLp (g + y).ofLp = 0)
    (hcurv : 0 < dotProduct s.ofLp y.ofLp) :
    Broyden.update φ C s y = BFGS.update C s y +
      (φ * a / dotProduct s.ofLp y.ofLp) •
        Matrix.vecMulVec (g + y).ofLp (g + y).ofLp := by
  -- Normalize all matrix products through `C *ᵥ s` before scalar field algebra.
  let r : ℝ := dotProduct s.ofLp y.ofLp
  have hr : 0 < r := by simpa only [r] using hcurv
  have hr0 : r ≠ 0 := hr.ne'
  have hCt : Matrix.transpose C = C := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.1.eq
  have hrow : Matrix.vecMul s.ofLp C = -(a • g).ofLp := by
    rw [← Matrix.mulVec_transpose, hCt]
    exact hCs
  have hrEq : r = -dotProduct s.ofLp g.ofLp := by
    have horth' : dotProduct s.ofLp g.ofLp + dotProduct s.ofLp y.ofLp = 0 := by
      simpa only [WithLp.ofLp_add, dotProduct_add] using horth
    dsimp only [r]
    linarith
  have hq : dotProduct s.ofLp (Matrix.mulVec C s.ofLp) = a * r := by
    rw [hCs]
    simp only [WithLp.ofLp_smul, dotProduct_neg, dotProduct_smul, smul_eq_mul, hrEq]
    ring
  have hquadratic : C * Matrix.vecMulVec s.ofLp s.ofLp * C =
      (a ^ 2) • Matrix.vecMulVec g.ofLp g.ofLp := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hCs, hrow]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.neg_apply, Pi.smul_apply,
      WithLp.ofLp_smul, smul_eq_mul]
    ring
  have hright : C * Matrix.vecMulVec s.ofLp y.ofLp =
      (-a) • Matrix.vecMulVec g.ofLp y.ofLp := by
    rw [Matrix.mul_vecMulVec, hCs]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.neg_apply, Pi.smul_apply,
      smul_eq_mul, WithLp.ofLp_smul]
    ring
  have hleft : Matrix.vecMulVec y.ofLp s.ofLp * C =
      (-a) • Matrix.vecMulVec y.ofLp g.ofLp := by
    rw [Matrix.vecMulVec_mul, hrow]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.neg_apply, Pi.smul_apply,
      smul_eq_mul, WithLp.ofLp_smul]
    ring
  have hcross : Matrix.vecMulVec y.ofLp s.ofLp * C *
      Matrix.vecMulVec s.ofLp y.ofLp =
        (a * r) • Matrix.vecMulVec y.ofLp y.ofLp := by
    rw [hleft, Matrix.smul_mul, Matrix.vecMulVec_mul_vecMulVec]
    have hgDot : dotProduct g.ofLp s.ofLp = -r := by
      rw [dotProduct_comm]
      linarith [hrEq]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
      hgDot, Matrix.vecMulVec_smul]
    ring
  have hprojection :
      (1 - r⁻¹ • Matrix.vecMulVec y.ofLp s.ofLp) * C *
          (1 - r⁻¹ • Matrix.vecMulVec s.ofLp y.ofLp) =
        C + (a / r) • (Matrix.vecMulVec g.ofLp y.ofLp +
          Matrix.vecMulVec y.ofLp g.ofLp + Matrix.vecMulVec y.ofLp y.ofLp) := by
    calc
      (1 - r⁻¹ • Matrix.vecMulVec y.ofLp s.ofLp) * C *
          (1 - r⁻¹ • Matrix.vecMulVec s.ofLp y.ofLp) =
          (C - r⁻¹ • (Matrix.vecMulVec y.ofLp s.ofLp * C)) *
            (1 - r⁻¹ • Matrix.vecMulVec s.ofLp y.ofLp) := by
        rw [sub_mul, one_mul, Matrix.smul_mul]
      _ = C - r⁻¹ • (Matrix.vecMulVec y.ofLp s.ofLp * C) -
          r⁻¹ • (C * Matrix.vecMulVec s.ofLp y.ofLp -
            r⁻¹ • (Matrix.vecMulVec y.ofLp s.ofLp * C *
              Matrix.vecMulVec s.ofLp y.ofLp)) := by
        rw [mul_sub, mul_one, Matrix.mul_smul, sub_mul, Matrix.smul_mul]
      _ = C + (a / r) • (Matrix.vecMulVec g.ofLp y.ofLp +
          Matrix.vecMulVec y.ofLp g.ofLp + Matrix.vecMulVec y.ofLp y.ofLp) := by
        rw [hcross, hleft, hright]
        ext i j
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        field_simp [hr0]
        ring
  have hNewGradient : Matrix.vecMulVec (g + y).ofLp (g + y).ofLp =
      Matrix.vecMulVec g.ofLp g.ofLp + Matrix.vecMulVec g.ofLp y.ofLp +
        Matrix.vecMulVec y.ofLp g.ofLp + Matrix.vecMulVec y.ofLp y.ofLp := by
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.add_apply, WithLp.ofLp_add, Pi.add_apply]
    ring
  have hys : dotProduct y.ofLp s.ofLp = r := by
    rw [dotProduct_comm]
  have hsy : dotProduct s.ofLp y.ofLp = r := rfl
  rw [Broyden.update_def, DFP.update_def, BFGS.update_def]
  rw [hys, hsy, hprojection, hq, hquadratic]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  have hNewGradientEntry := congrFun₂ hNewGradient i j
  simp only [Matrix.add_apply] at hNewGradientEntry
  simp only [smul_eq_mul]
  field_simp [hr0]
  rw [hNewGradientEntry]
  ring

/-- Adding a nonnegative self outer product to a positive-definite real matrix
preserves positive definiteness. -/
private theorem posDef_add_gradientRankOne
    {ι : Type*} [Finite ι]
    {B : Matrix ι ι ℝ} (hB : B.PosDef) (g : EuclideanSpace ℝ ι)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (B + τ • Matrix.vecMulVec g.ofLp g.ofLp).PosDef := by
  -- The outer product is positive semidefinite, so its nonnegative multiple can be added.
  classical
  -- Local instance justification (finite indexing): the matrix positivity API requires a
  -- concrete enumeration of the finite index type.
  letI : Fintype ι := Fintype.ofFinite ι
  have hRank : (Matrix.vecMulVec g.ofLp g.ofLp).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star g.ofLp
  exact hB.add_posSemidef (hRank.smul hτ)

/-- A gradient-rank-one perturbation sends an exact-search displacement to the
correspondingly rescaled negative gradient. -/
private theorem addGradientRankOne_mulVec_step
    {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) {s g y : EuclideanSpace ℝ ι} {a τ : ℝ}
    (hBs : Matrix.mulVec B s.ofLp = -(a • g).ofLp)
    (horth : dotProduct s.ofLp (g + y).ofLp = 0) :
    Matrix.mulVec (B + τ • Matrix.vecMulVec g.ofLp g.ofLp) s.ofLp =
      -((a + τ * dotProduct s.ofLp y.ofLp) • g).ofLp := by
  -- Orthogonality says `g ⬝ s = -(s ⬝ y)`, which determines the rank-one action.
  have hgDot : dotProduct g.ofLp s.ofLp = -dotProduct s.ofLp y.ofLp := by
    have hsum : dotProduct s.ofLp g.ofLp + dotProduct s.ofLp y.ofLp = 0 := by
      simpa only [WithLp.ofLp_add, dotProduct_add] using horth
    rw [dotProduct_comm]
    linarith
  rw [Matrix.add_mulVec, hBs, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, WithLp.ofLp_smul,
    smul_eq_mul, hgDot, op_smul_eq_smul, smul_smul]
  ring

/-- A positive-definite matrix equation `C s = -a g` identifies `s` as `a` times
the search direction for `g`. -/
private theorem eq_smul_searchDirection_of_mulVec_eq_neg_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosDef) {s g : EuclideanSpace ℝ ι} {a : ℝ}
    (hCs : Matrix.mulVec C s.ofLp = -(a • g).ofLp) :
    s = a • BFGS.searchDirection C g := by
  -- Apply the injective positive-definite matrix to both sides and use the solve equation.
  apply (EuclideanSpace.equiv ι ℝ).injective
  simp only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv,
    WithLp.ofLp_smul]
  apply Matrix.mulVec_injective_of_isUnit hC.isUnit
  have hDirectionSpec : Matrix.mulVec C (BFGS.searchDirection C g).ofLp = -g.ofLp := by
    simpa only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
      BFGS.searchDirection_spec hC g
  rw [hCs]
  simp only [Matrix.mulVec_smul, hDirectionSpec, smul_neg]
  rw [WithLp.ofLp_smul]

/-- A gradient-rank-one perturbation cancels from the BFGS update under exact-search
orthogonality. -/
private theorem bfgsUpdate_add_gradientRankOne
    {ι : Type*} [Fintype ι]
    {B C : Matrix ι ι ℝ} (hB : B.PosDef) (hC : C.PosDef)
    {s g y : EuclideanSpace ℝ ι} {a τ : ℝ}
    (ha : 0 < a) (hτ : 0 ≤ τ)
    (hCeq : C = B + τ • Matrix.vecMulVec g.ofLp g.ofLp)
    (hBs : Matrix.mulVec B s.ofLp = -(a • g).ofLp)
    (horth : dotProduct s.ofLp (g + y).ofLp = 0)
    (hcurv : 0 < dotProduct s.ofLp y.ofLp) :
    BFGS.update C s y = BFGS.update B s y := by
  -- Normalize both rank-two corrections to scalar multiples of `g gᵀ`.
  classical
  let r : ℝ := dotProduct s.ofLp y.ofLp
  let aC : ℝ := a + τ * r
  have hr : 0 < r := by simpa only [r] using hcurv
  have haC : 0 < aC := by
    dsimp only [aC]
    exact add_pos_of_pos_of_nonneg ha (mul_nonneg hτ hr.le)
  have hCs : Matrix.mulVec C s.ofLp = -(aC • g).ofLp := by
    rw [hCeq]
    exact addGradientRankOne_mulVec_step B hBs horth
  have hBt : Matrix.transpose B = B := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.1.eq
  have hCt : Matrix.transpose C = C := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.1.eq
  have hBrow : Matrix.vecMul s.ofLp B = -(a • g).ofLp := by
    rw [← Matrix.mulVec_transpose, hBt]
    exact hBs
  have hCrow : Matrix.vecMul s.ofLp C = -(aC • g).ofLp := by
    rw [← Matrix.mulVec_transpose, hCt]
    exact hCs
  have hqB : dotProduct s.ofLp (Matrix.mulVec B s.ofLp) = a * r := by
    have hgDot : dotProduct s.ofLp g.ofLp = -r := by
      have hsum : dotProduct s.ofLp g.ofLp + dotProduct s.ofLp y.ofLp = 0 := by
        simpa only [WithLp.ofLp_add, dotProduct_add] using horth
      linarith
    rw [hBs]
    simp only [WithLp.ofLp_smul, dotProduct_neg, dotProduct_smul, smul_eq_mul,
      hgDot]
    ring
  have hqC : dotProduct s.ofLp (Matrix.mulVec C s.ofLp) = aC * r := by
    have hgDot : dotProduct s.ofLp g.ofLp = -r := by
      have hsum : dotProduct s.ofLp g.ofLp + dotProduct s.ofLp y.ofLp = 0 := by
        simpa only [WithLp.ofLp_add, dotProduct_add] using horth
      linarith
    rw [hCs]
    simp only [WithLp.ofLp_smul, dotProduct_neg, dotProduct_smul, smul_eq_mul,
      hgDot]
    ring
  have hquadraticB : B * Matrix.vecMulVec s.ofLp s.ofLp * B =
      (a ^ 2) • Matrix.vecMulVec g.ofLp g.ofLp := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hBs, hBrow]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.neg_apply, Pi.smul_apply,
      WithLp.ofLp_smul, smul_eq_mul]
    ring
  have hquadraticC : C * Matrix.vecMulVec s.ofLp s.ofLp * C =
      (aC ^ 2) • Matrix.vecMulVec g.ofLp g.ofLp := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hCs, hCrow]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.neg_apply, Pi.smul_apply,
      WithLp.ofLp_smul, smul_eq_mul]
    ring
  have hr0 : r ≠ 0 := hr.ne'
  rw [BFGS.update_def, BFGS.update_def, hqB, hqC, hquadraticB, hquadraticC, hCeq]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp [ha.ne', haC.ne', hr0]
  dsimp only [aC]
  ring

/-- The convex-Broyden matrices obtained by updating along a prescribed point sequence. -/
private noncomputable def broydenMatricesAlong (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (φ : ℕ → ℝ) (B₀ : Matrix (Fin n) (Fin n) ℝ)
    (z : ℕ → EuclideanSpace ℝ (Fin n)) : ℕ → Matrix (Fin n) (Fin n) ℝ :=
  fun k ↦ Nat.rec B₀ (fun j C ↦ Broyden.update (φ j) C
    (z (j + 1) - z j) (gradient F (z (j + 1)) - gradient F (z j))) k

/-- The prescribed Broyden matrix sequence starts at its supplied initial matrix. -/
private theorem broydenMatricesAlong_zero
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (φ : ℕ → ℝ)
    (B₀ : Matrix (Fin n) (Fin n) ℝ) (z : ℕ → EuclideanSpace ℝ (Fin n)) :
    broydenMatricesAlong F φ B₀ z 0 = B₀ := by
  -- This is the zero equation of the defining natural-number recursion.
  rfl

/-- Successive prescribed Broyden matrices satisfy the convex-Broyden update law. -/
private theorem broydenMatricesAlong_succ
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (φ : ℕ → ℝ)
    (B₀ : Matrix (Fin n) (Fin n) ℝ) (z : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    broydenMatricesAlong F φ B₀ z (k + 1) =
      Broyden.update (φ k) (broydenMatricesAlong F φ B₀ z k)
        (z (k + 1) - z k) (gradient F (z (k + 1)) - gradient F (z k)) := by
  -- This is the successor equation of the defining natural-number recursion.
  rfl

/-- The rank-one coefficient propagated by convex-Broyden updates along a BFGS point
sequence. -/
private noncomputable def dixonCoefficientAlong
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (φ α : ℕ → ℝ)
    (z : ℕ → EuclideanSpace ℝ (Fin n)) : ℕ → ℝ :=
  fun k ↦ Nat.rec 0 (fun j τ ↦ φ j *
    (α j + τ * dotProduct (z (j + 1) - z j).ofLp
      (gradient F (z (j + 1)) - gradient F (z j)).ofLp) /
    dotProduct (z (j + 1) - z j).ofLp
      (gradient F (z (j + 1)) - gradient F (z j)).ofLp) k

/-- The initial Dixon rank-one coefficient is zero. -/
private theorem dixonCoefficientAlong_zero
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (φ α : ℕ → ℝ)
    (z : ℕ → EuclideanSpace ℝ (Fin n)) :
    dixonCoefficientAlong F φ α z 0 = 0 := by
  -- This is the zero equation of the coefficient recursion.
  rfl

/-- The Dixon rank-one coefficient obeys the scalar recurrence forced by the
convex-Broyden update. -/
private theorem dixonCoefficientAlong_succ
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (φ α : ℕ → ℝ)
    (z : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    dixonCoefficientAlong F φ α z (k + 1) = φ k *
      (α k + dixonCoefficientAlong F φ α z k *
        dotProduct (z (k + 1) - z k).ofLp
          (gradient F (z (k + 1)) - gradient F (z k)).ofLp) /
      dotProduct (z (k + 1) - z k).ofLp
        (gradient F (z (k + 1)) - gradient F (z k)).ofLp := by
  -- This is the successor equation of the coefficient recursion.
  rfl

/-- Along the BFGS points, the canonical convex-Broyden matrices differ from the
BFGS matrices by a nonnegative outer product of the current gradient. -/
private theorem broydenMatricesAlong_dixonInvariant
    (h : BFGS.IsOrderOneExample ε R F x₀ x B α)
    (φ : ℕ → ℝ) (hφ : ∀ k, φ k ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    0 ≤ dixonCoefficientAlong F φ α x k ∧
      (broydenMatricesAlong F φ 1 x k).PosDef ∧
      broydenMatricesAlong F φ 1 x k =
        B k + dixonCoefficientAlong F φ α x k •
          Matrix.vecMulVec (gradient F (x k)).ofLp (gradient F (x k)).ofLp := by
  -- Induct simultaneously on coefficient nonnegativity, definiteness, and rank-one form.
  have hRun := (BFGS.isTrajectory_iff F 1 x B α).mp h.trajectory
  induction k with
  | zero =>
      constructor
      · rw [dixonCoefficientAlong_zero]
      constructor
      · rw [broydenMatricesAlong_zero]
        simpa only [hRun.1] using hRun.2.2.1 0
      · rw [broydenMatricesAlong_zero, dixonCoefficientAlong_zero, zero_smul, add_zero,
          hRun.1]
  | succ k ih =>
      let s : EuclideanSpace ℝ (Fin n) := x (k + 1) - x k
      let g : EuclideanSpace ℝ (Fin n) := gradient F (x k)
      let y : EuclideanSpace ℝ (Fin n) := gradient F (x (k + 1)) - g
      let r : ℝ := dotProduct s.ofLp y.ofLp
      let τ : ℝ := dixonCoefficientAlong F φ α x k
      let C : Matrix (Fin n) (Fin n) ℝ := broydenMatricesAlong F φ 1 x k
      have hGeometry := bfgsStepGeometry h k
      have ha : 0 < α k := hGeometry.1
      have hBs : Matrix.mulVec (B k) s.ofLp = -(α k • g).ofLp := by
        simpa only [s, g] using hGeometry.2.2.2.1
      have horth : dotProduct s.ofLp (g + y).ofLp = 0 := by
        have hGradientSum : g + y = gradient F (x (k + 1)) := by
          dsimp only [g, y]
          abel
        calc
          dotProduct s.ofLp (g + y).ofLp =
              dotProduct s.ofLp (gradient F (x (k + 1))).ofLp := by rw [hGradientSum]
          _ = 0 := by
            simpa only [s, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
              hGeometry.2.2.2.2.1
      have hr : 0 < r := by
        simpa only [r, s, y, g] using hGeometry.2.2.2.2.2
      have hτ : 0 ≤ τ := by simpa only [τ] using ih.1
      have hCpos : C.PosDef := by simpa only [C] using ih.2.1
      have hCeq : C = B k + τ • Matrix.vecMulVec g.ofLp g.ofLp := by
        simpa only [C, τ, g] using ih.2.2
      let aC : ℝ := α k + τ * r
      have haC : 0 < aC := by
        dsimp only [aC]
        exact add_pos_of_pos_of_nonneg ha (mul_nonneg hτ hr.le)
      have hCs : Matrix.mulVec C s.ofLp = -(aC • g).ofLp := by
        rw [hCeq]
        exact addGradientRankOne_mulVec_step (B k) hBs horth
      have hBfgsSame : BFGS.update C s y = BFGS.update (B k) s y :=
        bfgsUpdate_add_gradientRankOne (hRun.2.2.1 k) hCpos ha hτ hCeq hBs horth hr
      have hBroyden := broydenUpdate_eq_bfgsUpdate_add_rankOne hCpos hCs horth hr
        (φ := φ k)
      have hCoefficientNonnegative : 0 ≤ φ k * aC / r :=
        div_nonneg (mul_nonneg (hφ k).1 haC.le) hr.le
      have hBsucc : B (k + 1) = BFGS.update (B k) s y := by
        simpa only [s, y, g] using hRun.2.2.2.2.2 k
      have hCname : broydenMatricesAlong F φ 1 x k = C := rfl
      have hsName : x (k + 1) - x k = s := rfl
      have hyName : gradient F (x (k + 1)) - gradient F (x k) = y := rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [dixonCoefficientAlong_succ]
        simpa only [τ, aC, r, s, y, g] using hCoefficientNonnegative
      · rw [broydenMatricesAlong_succ]
        exact Broyden.update_posDef (hφ k) hCpos hr
      · rw [broydenMatricesAlong_succ, dixonCoefficientAlong_succ]
        rw [hBsucc, hCname, hsName, hyName]
        rw [hBroyden, hBfgsSame]
        congr 2
        have hGradientSum : g + y = gradient F (x (k + 1)) := by
          dsimp only [g, y]
          abel
        rw [hGradientSum]

/-- BFGS.IsOrderOneExample.existsBroydenTrajectory: every parameter sequence in
`Set.Icc 0 1` admits an identity-initialized
exact-line-search convex Broyden trajectory on the point sequence of an order-one BFGS
example. -/
theorem existsBroydenTrajectory (h : BFGS.IsOrderOneExample ε R F x₀ x B α)
    (φ : ℕ → ℝ) (hφ : ∀ k, φ k ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (Bφ : ℕ → Matrix (Fin n) (Fin n) ℝ) (αφ : ℕ → ℝ),
      Broyden.IsTrajectory F φ (1 : Matrix (Fin n) (Fin n) ℝ) x Bφ αφ := by
  -- Use the canonical matrices and the explicit Dixon scaling of each line-search step.
  let C : ℕ → Matrix (Fin n) (Fin n) ℝ := broydenMatricesAlong F φ 1 x
  let τ : ℕ → ℝ := dixonCoefficientAlong F φ α x
  let αφ : ℕ → ℝ := fun k ↦ α k + τ k *
    dotProduct (x (k + 1) - x k).ofLp
      (gradient F (x (k + 1)) - gradient F (x k)).ofLp
  have hRun := (BFGS.isTrajectory_iff F 1 x B α).mp h.trajectory
  obtain ⟨m, hm, hStrong⟩ := h.strongConvex
  have hConvex : ConvexOn ℝ Set.univ F := (hStrong.strictConvexOn hm).convexOn
  refine ⟨C, αφ, Broyden.IsTrajectory.ofConditions ?_ hRun.2.1 hφ ?_ ?_ ?_ ?_⟩
  · -- The canonical recursion starts from the identity matrix.
    exact broydenMatricesAlong_zero F φ 1 x
  · -- Positive definiteness is one component of the global rank-one invariant.
    intro k
    simpa only [C] using (broydenMatricesAlong_dixonInvariant h φ hφ k).2.1
  · -- Orthogonality at the known next point certifies the rescaled exact search.
    intro k
    let s : EuclideanSpace ℝ (Fin n) := x (k + 1) - x k
    let g : EuclideanSpace ℝ (Fin n) := gradient F (x k)
    let y : EuclideanSpace ℝ (Fin n) := gradient F (x (k + 1)) - g
    let r : ℝ := dotProduct s.ofLp y.ofLp
    have hInvariant := broydenMatricesAlong_dixonInvariant h φ hφ k
    have hGeometry := bfgsStepGeometry h k
    have hCpos : (C k).PosDef := by simpa only [C] using hInvariant.2.1
    have hCeq : C k = B k + τ k • Matrix.vecMulVec g.ofLp g.ofLp := by
      simpa only [C, τ, g] using hInvariant.2.2
    have horthDot : dotProduct s.ofLp (g + y).ofLp = 0 := by
      have hGradientSum : g + y = gradient F (x (k + 1)) := by
        dsimp only [g, y]
        abel
      rw [hGradientSum]
      simpa only [s, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
        hGeometry.2.2.2.2.1
    have hBs : Matrix.mulVec (B k) s.ofLp = -(α k • g).ofLp := by
      simpa only [s, g] using hGeometry.2.2.2.1
    have hCs : Matrix.mulVec (C k) s.ofLp = -(αφ k • g).ofLp := by
      rw [hCeq]
      simpa only [αφ, τ, r, s, y, g] using
        addGradientRankOne_mulVec_step (B k) hBs horthDot
    have hsDirection : s = αφ k • BFGS.searchDirection (C k) g :=
      eq_smul_searchDirection_of_mulVec_eq_neg_smul hCpos hCs
    have hαφ : 0 < αφ k := by
      have hr : 0 < r := by
        simpa only [r, s, y, g] using hGeometry.2.2.2.2.2
      have hτ : 0 ≤ τ k := by
        simpa only [τ] using hInvariant.1
      dsimp only [αφ]
      exact add_pos_of_pos_of_nonneg hGeometry.1 (mul_nonneg hτ hr.le)
    have hStationary : inner ℝ (gradient F (x (k + 1)))
        (BFGS.searchDirection (C k) g) = 0 := by
      have hOrthogonal := hGeometry.2.2.2.2.1
      have hsName : x (k + 1) - x k = s := rfl
      rw [hsName, hsDirection, inner_smul_right] at hOrthogonal
      exact (mul_eq_zero.mp hOrthogonal).resolve_left hαφ.ne'
    apply exactLineSearch_of_inner_gradient_eq_zero F hRun.2.1 hConvex
    · exact hαφ.le
    · have hEndpoint : x k + s = x (k + 1) := by
        dsimp only [s]
        abel
      rw [← hsDirection, hEndpoint]
      simpa only [g] using hStationary
  · -- The chosen step length reproduces the prescribed BFGS displacement.
    intro k
    let s : EuclideanSpace ℝ (Fin n) := x (k + 1) - x k
    let g : EuclideanSpace ℝ (Fin n) := gradient F (x k)
    let y : EuclideanSpace ℝ (Fin n) := gradient F (x (k + 1)) - g
    have hInvariant := broydenMatricesAlong_dixonInvariant h φ hφ k
    have hGeometry := bfgsStepGeometry h k
    have hCpos : (C k).PosDef := by simpa only [C] using hInvariant.2.1
    have hCeq : C k = B k + τ k • Matrix.vecMulVec g.ofLp g.ofLp := by
      simpa only [C, τ, g] using hInvariant.2.2
    have horthDot : dotProduct s.ofLp (g + y).ofLp = 0 := by
      have hGradientSum : g + y = gradient F (x (k + 1)) := by
        dsimp only [g, y]
        abel
      rw [hGradientSum]
      simpa only [s, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
        hGeometry.2.2.2.2.1
    have hBs : Matrix.mulVec (B k) s.ofLp = -(α k • g).ofLp := by
      simpa only [s, g] using hGeometry.2.2.2.1
    have hCs : Matrix.mulVec (C k) s.ofLp = -(αφ k • g).ofLp := by
      rw [hCeq]
      simpa only [αφ, τ, s, y, g] using
        addGradientRankOne_mulVec_step (B k) hBs horthDot
    have hsDirection : s = αφ k • BFGS.searchDirection (C k) g :=
      eq_smul_searchDirection_of_mulVec_eq_neg_smul hCpos hCs
    calc
      x (k + 1) = x k + s := by dsimp only [s]; abel
      _ = x k + αφ k • BFGS.searchDirection (C k) (gradient F (x k)) := by
        rw [hsDirection]
  · -- The canonical matrix recursion is exactly the required Broyden update.
    intro k
    exact broydenMatricesAlong_succ F φ 1 x k

/-- Every identity-initialized exact-line-search convex Broyden trajectory starting at
the same point has the point sequence of the order-one BFGS example. -/
theorem broydenPoints_eq (h : BFGS.IsOrderOneExample ε R F x₀ x B α)
    {φ : ℕ → ℝ} {xφ : ℕ → EuclideanSpace ℝ (Fin n)}
    {Bφ : ℕ → Matrix (Fin n) (Fin n) ℝ} {αφ : ℕ → ℝ}
    (hRun : Broyden.IsTrajectory F φ (1 : Matrix (Fin n) (Fin n) ℝ) xφ Bφ αφ)
    (h_initial : xφ 0 = x₀) : xφ = x := by
  -- Couple point equality with the Dixon rank-one matrix relation at every index.
  have hBfgsRun := (BFGS.isTrajectory_iff F 1 x B α).mp h.trajectory
  obtain ⟨m, hm, hStrong⟩ := h.strongConvex
  have hStrict : StrictConvexOn ℝ Set.univ F := hStrong.strictConvexOn hm
  have hConvex : ConvexOn ℝ Set.univ F := hStrict.convexOn
  have hInvariant (k : ℕ) : ∃ τ : ℝ, 0 ≤ τ ∧ xφ k = x k ∧
      Bφ k = B k + τ • Matrix.vecMulVec (gradient F (x k)).ofLp
        (gradient F (x k)).ofLp := by
    induction k with
    | zero =>
        refine ⟨0, le_rfl, h_initial.trans h.initial.symm, ?_⟩
        rw [hRun.initial, hBfgsRun.1, zero_smul, add_zero]
    | succ k ih =>
        obtain ⟨τ, hτ, hx, hMatrix⟩ := ih
        let s : EuclideanSpace ℝ (Fin n) := x (k + 1) - x k
        let g : EuclideanSpace ℝ (Fin n) := gradient F (x k)
        let y : EuclideanSpace ℝ (Fin n) := gradient F (x (k + 1)) - g
        let r : ℝ := dotProduct s.ofLp y.ofLp
        let C : Matrix (Fin n) (Fin n) ℝ := Bφ k
        let aC : ℝ := α k + τ * r
        have hGeometry := bfgsStepGeometry h k
        have ha : 0 < α k := hGeometry.1
        have hr : 0 < r := by
          simpa only [r, s, y, g] using hGeometry.2.2.2.2.2
        have haC : 0 < aC := by
          dsimp only [aC]
          exact add_pos_of_pos_of_nonneg ha (mul_nonneg hτ hr.le)
        have hCpos : C.PosDef := by simpa only [C] using hRun.posDef k
        have hCeq : C = B k + τ • Matrix.vecMulVec g.ofLp g.ofLp := by
          simpa only [C, g] using hMatrix
        have horthDot : dotProduct s.ofLp (g + y).ofLp = 0 := by
          have hGradientSum : g + y = gradient F (x (k + 1)) := by
            dsimp only [g, y]
            abel
          rw [hGradientSum]
          simpa only [s, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
            hGeometry.2.2.2.2.1
        have hBs : Matrix.mulVec (B k) s.ofLp = -(α k • g).ofLp := by
          simpa only [s, g] using hGeometry.2.2.2.1
        have hCs : Matrix.mulVec C s.ofLp = -(aC • g).ofLp := by
          rw [hCeq]
          exact addGradientRankOne_mulVec_step (B k) hBs horthDot
        have hsDirection : s = aC • BFGS.searchDirection C g :=
          eq_smul_searchDirection_of_mulVec_eq_neg_smul hCpos hCs
        have hsNe : s ≠ 0 := by
          have hScaledNe :
              α k • BFGS.searchDirection (B k) (gradient F (x k)) ≠ 0 :=
            smul_ne_zero ha.ne' hGeometry.2.1
          intro hsZero
          apply hScaledNe
          have hsZeroRaw : x (k + 1) - x k = 0 := by
            simpa only [s] using hsZero
          exact hGeometry.2.2.1.symm.trans hsZeroRaw
        have hDirectionNe : BFGS.searchDirection C g ≠ 0 := by
          intro hdZero
          rw [hdZero, smul_zero] at hsDirection
          exact hsNe hsDirection
        have hStationary : inner ℝ (gradient F (x (k + 1)))
            (BFGS.searchDirection C g) = 0 := by
          have hOrthogonal := hGeometry.2.2.2.2.1
          have hsName : x (k + 1) - x k = s := rfl
          rw [hsName, hsDirection, inner_smul_right] at hOrthogonal
          exact (mul_eq_zero.mp hOrthogonal).resolve_left haC.ne'
        have hCandidateExact : LineSearch.IsExact F (x k)
            (BFGS.searchDirection C g) aC := by
          apply exactLineSearch_of_inner_gradient_eq_zero F hBfgsRun.2.1 hConvex
          · exact haC.le
          · have hEndpoint : x k + s = x (k + 1) := by
              dsimp only [s]
              abel
            rw [← hsDirection, hEndpoint]
            simpa only [g] using hStationary
        have hRunExact : LineSearch.IsExact F (x k)
            (BFGS.searchDirection C g) (αφ k) := by
          simpa only [C, g, hx] using hRun.exact k
        have hParameter : αφ k = aC :=
          exactLineSearch_parameter_eq hStrict hDirectionNe hRunExact hCandidateExact
        have hxNext : xφ (k + 1) = x (k + 1) := by
          calc
            xφ (k + 1) = xφ k + αφ k •
                BFGS.searchDirection (Bφ k) (gradient F (xφ k)) := hRun.point k
            _ = x k + aC • BFGS.searchDirection C g := by
              rw [hx, hParameter]
            _ = x k + s := by rw [← hsDirection]
            _ = x (k + 1) := by dsimp only [s]; abel
        have hBfgsSame : BFGS.update C s y = BFGS.update (B k) s y :=
          bfgsUpdate_add_gradientRankOne (hBfgsRun.2.2.1 k) hCpos ha hτ hCeq hBs
            horthDot hr
        have hBroyden := broydenUpdate_eq_bfgsUpdate_add_rankOne hCpos hCs
          horthDot hr (φ := φ k)
        let τNext : ℝ := φ k * aC / r
        have hτNext : 0 ≤ τNext := by
          dsimp only [τNext]
          exact div_nonneg (mul_nonneg (hRun.parameter_mem k).1 haC.le) hr.le
        have hUpdateRun := hRun.update k
        rw [hx, hxNext] at hUpdateRun
        have hBsucc : B (k + 1) = BFGS.update (B k) s y := by
          simpa only [s, y, g] using hBfgsRun.2.2.2.2.2 k
        have hMatrixNext : Bφ (k + 1) = B (k + 1) + τNext •
            Matrix.vecMulVec (gradient F (x (k + 1))).ofLp
              (gradient F (x (k + 1))).ofLp := by
          rw [hUpdateRun]
          have hCname : Bφ k = C := rfl
          have hsName : x (k + 1) - x k = s := rfl
          have hyName : gradient F (x (k + 1)) - gradient F (x k) = y := rfl
          rw [hCname, hsName, hyName, hBroyden, hBfgsSame, ← hBsucc]
          have hGradientSum : g + y = gradient F (x (k + 1)) := by
            dsimp only [g, y]
            abel
          rw [hGradientSum]
        exact ⟨τNext, hτNext, hxNext, hMatrixNext⟩
  funext k
  obtain ⟨τ, hτ, hx, hMatrix⟩ := hInvariant k
  exact hx

/-- An equally initialized exact-line-search convex Broyden trajectory for an order-one
BFGS example never reaches the origin. -/
theorem broydenNonterminating (h : BFGS.IsOrderOneExample ε R F x₀ x B α)
    {φ : ℕ → ℝ} {xφ : ℕ → EuclideanSpace ℝ (Fin n)}
    {Bφ : ℕ → Matrix (Fin n) (Fin n) ℝ} {αφ : ℕ → ℝ}
    (hRun : Broyden.IsTrajectory F φ (1 : Matrix (Fin n) (Fin n) ℝ) xφ Bφ αφ)
    (h_initial : xφ 0 = x₀) : ∀ k, xφ k ≠ 0 := by
  -- Transfer nontermination through equality with the BFGS point sequence.
  rw [broydenPoints_eq h hRun h_initial]
  exact h.nonterminating

/-- An equally initialized exact-line-search convex Broyden trajectory for an order-one
BFGS example converges Q-superlinearly to the origin. -/
theorem broydenSuperlinear (h : BFGS.IsOrderOneExample ε R F x₀ x B α)
    {φ : ℕ → ℝ} {xφ : ℕ → EuclideanSpace ℝ (Fin n)}
    {Bφ : ℕ → Matrix (Fin n) (Fin n) ℝ} {αφ : ℕ → ℝ}
    (hRun : Broyden.IsTrajectory F φ (1 : Matrix (Fin n) (Fin n) ℝ) xφ Bφ αφ)
    (h_initial : xφ 0 = x₀) : QConvergence.IsSuperlinear xφ 0 := by
  -- Transfer Q-superlinear convergence through equality of point sequences.
  rw [broydenPoints_eq h hRun h_initial]
  exact h.superlinear

/-- An equally initialized exact-line-search convex Broyden trajectory for an order-one
BFGS example has Q-order exactly one at the origin. -/
theorem broydenOrder_eq_one (h : BFGS.IsOrderOneExample ε R F x₀ x B α)
    {φ : ℕ → ℝ} {xφ : ℕ → EuclideanSpace ℝ (Fin n)}
    {Bφ : ℕ → Matrix (Fin n) (Fin n) ℝ} {αφ : ℕ → ℝ}
    (hRun : Broyden.IsTrajectory F φ (1 : Matrix (Fin n) (Fin n) ℝ) xφ Bφ αφ)
    (h_initial : xφ 0 = x₀) : QConvergence.order xφ 0 = (1 : ENNReal) := by
  -- Transfer the exact Q-order through equality of point sequences.
  rw [broydenPoints_eq h hRun h_initial]
  exact h.orderEqOne

end BFGS.IsOrderOneExample
