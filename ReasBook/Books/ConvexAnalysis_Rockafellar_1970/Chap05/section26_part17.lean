/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part16

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

/-- The real-valued branch of `f(ξ₁, ξ₂) = ξ₂^2 / (2 ξ₁) - 2 √ξ₂` used on the open positive
quadrant. -/
noncomputable def quadraticOverLinearMinusSqrtCore (x : Fin 2 → ℝ) : ℝ :=
  x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1)

/-- The explicit gradient map of `quadraticOverLinearMinusSqrtCore` on the open positive quadrant,
written in the coordinates `(ξ₁*, ξ₂*)`. -/
noncomputable def quadraticOverLinearMinusSqrtGradientMap : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  fun x => ![
    -((x 1) ^ 2 / (2 * (x 0) ^ 2)),
    x 1 / x 0 - 1 / Real.sqrt (x 1)
  ]

/-- The dual domain `C*` for the quadratic-over-linear-minus-square-root example. -/
def quadraticOverLinearMinusSqrtDualDomain : Set (Fin 2 → ℝ) :=
  {xStar | xStar 0 < 0 ∧ xStar 1 < Real.sqrt (-2 * xStar 0)}

/-- The explicit inverse of the gradient map on the dual domain `C*`, obtained by writing
`s = (-2 ξ₁*)^{1/2}`, solving `ξ₂ / ξ₁ = s` and `ξ₂* = s - ξ₂^{-1/2}`, and hence
`ξ₂ = 1 / (s - ξ₂*)^2` and `ξ₁ = 1 / (s * (s - ξ₂*)^2)`. -/
noncomputable def quadraticOverLinearMinusSqrtGradientInverse : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  fun xStar =>
    let s := Real.sqrt (-2 * xStar 0)
    ![
      1 / (s * (s - xStar 1) ^ 2),
      1 / ((s - xStar 1) ^ 2)
    ]

/-- The explicit Fenchel conjugate formula on the dual domain of the
quadratic-over-linear-minus-square-root example, extended by `+∞` outside that domain. -/
noncomputable def quadraticOverLinearMinusSqrtDualConjugateFunction : (Fin 2 → ℝ) → EReal :=
  fun xStar =>
    if xStar ∈ quadraticOverLinearMinusSqrtDualDomain then
      ((1 / (Real.sqrt (-2 * xStar 0) - xStar 1) : ℝ) : EReal)
    else
      ⊤

/-- Helper for Example 26.5.0.1: the Chapter 26.2 closure package already shows that
`quadraticOverLinearMinusSqrtFunction` is proper convex and lower semicontinuous, and the
explicit domain computation reduces its interior effective domain to the open positive quadrant. -/
lemma helperForExample_26_5_0_1_closedProper_lsc_and_interiorDomain :
    ProperConvexERealFunction (F := (Fin 2 → ℝ)) quadraticOverLinearMinusSqrtFunction ∧
      LowerSemicontinuous quadraticOverLinearMinusSqrtFunction ∧
      interior (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
        quadraticOverLinearMinusSqrtFunction) = openPositiveQuadrantR2 := by
  rcases helperForExample_26_2_1_openQuadrantExtension_package with ⟨hproperExt, _⟩
  have hclosurePkg :=
    convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
      (f := helperForExample_26_2_1_openQuadrantExtension) hproperExt
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
        quadraticOverLinearMinusSqrtFunction := by
    -- The textbook function is the closed convex closure of the open-quadrant extension.
    simpa [helperForExample_26_2_1_openQuadrantExtension_closure_eq_target] using hclosurePkg.1.2
  have hproperEReal :
      ProperConvexERealFunction (F := (Fin 2 → ℝ))
        quadraticOverLinearMinusSqrtFunction :=
    helperForLemma_26_2_properConvexERealFunction hproper
  have hclosed : LowerSemicontinuous quadraticOverLinearMinusSqrtFunction := by
    -- Lower semicontinuity is inherited from the same closure package.
    simpa [helperForExample_26_2_1_openQuadrantExtension_closure_eq_target] using
      hclosurePkg.1.1.2
  rcases helperForExample_26_2_1_effectiveDomain_and_axisValues with ⟨hdom, _haxis⟩
  have hinterior :
      interior (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
        quadraticOverLinearMinusSqrtFunction) = openPositiveQuadrantR2 := by
    -- Rewriting the effective domain leaves exactly the explicit interior computed earlier.
    simpa [hdom] using helperForExample_26_2_2_explicitDomain_interior_eq_openQuadrant
  exact ⟨hproperEReal, hclosed, hinterior⟩

/-- Helper for Example 26.5.0.1: on the dual domain `C*`, the displayed inverse formula lands in
the open positive quadrant and evaluates the explicit gradient back to the original dual point. -/
lemma helperForExample_26_5_0_1_explicitInverse_mem_and_rightInv
    {xStar : Fin 2 → ℝ} (hxStar : xStar ∈ quadraticOverLinearMinusSqrtDualDomain) :
    quadraticOverLinearMinusSqrtGradientInverse xStar ∈ openPositiveQuadrantR2 ∧
      quadraticOverLinearMinusSqrtGradientMap
          (quadraticOverLinearMinusSqrtGradientInverse xStar) = xStar := by
  rcases hxStar with ⟨hx0neg, hx1lt⟩
  set s : ℝ := Real.sqrt (-2 * xStar 0)
  set d : ℝ := s - xStar 1
  have hs_pos : 0 < s := by
    apply Real.sqrt_pos.2
    nlinarith
  have hd_pos : 0 < d := by
    dsimp [d]
    linarith
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hs_sq : s ^ 2 = -2 * xStar 0 := by
    dsimp [s]
    simpa [pow_two] using Real.sq_sqrt (show 0 ≤ -2 * xStar 0 by nlinarith)
  have hsqrt_inv_sq : Real.sqrt (1 / d ^ 2) = 1 / d := by
    have hrewrite : 1 / d ^ 2 = (1 / d) ^ 2 := by
      field_simp [hd_ne]
    rw [hrewrite, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  constructor
  · -- Both coordinates of the inverse point are positive because `s > 0` and `d > 0`.
    constructor <;> dsimp [quadraticOverLinearMinusSqrtGradientInverse, s, d] <;> positivity
  · -- The inverse formulas solve the two gradient equations exactly.
    ext i
    fin_cases i
    · change -((1 / d ^ 2) ^ 2 / (2 * (1 / (s * d ^ 2)) ^ 2)) = xStar 0
      have hcalc : -((1 / d ^ 2) ^ 2 / (2 * (1 / (s * d ^ 2)) ^ 2)) = -(s ^ 2 / 2) := by
        field_simp [hs_ne, hd_ne]
      rw [hcalc, hs_sq]
      ring
    · change 1 / d ^ 2 / (1 / (s * d ^ 2)) - 1 / Real.sqrt (1 / d ^ 2) = xStar 1
      rw [hsqrt_inv_sq]
      have hcalc : 1 / d ^ 2 / (1 / (s * d ^ 2)) - 1 / (1 / d) = s - d := by
        field_simp [hs_ne, hd_ne]
      rw [hcalc]
      dsimp [d]
      ring

/-- Helper for Example 26.5.0.1: the coordinate gradient of the real core is the displayed map
on the open positive quadrant. -/
lemma helperForExample_26_5_0_1_coordinateGradient_formula
    {x : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) :
    euclideanGradientAt quadraticOverLinearMinusSqrtCore x =
      quadraticOverLinearMinusSqrtGradientMap x := by
  rcases hx with ⟨hx0, hx1⟩
  have hx : x ∈ openPositiveQuadrantR2 := ⟨hx0, hx1⟩
  have hdiff : DifferentiableAt ℝ quadraticOverLinearMinusSqrtCore x := by
    -- The previously established differentiability of the real core applies verbatim here.
    simpa [quadraticOverLinearMinusSqrtCore] using
      helperForExample_26_2_1_coreDifferentiableAt_openQuadrant hx
  ext i
  fin_cases i
  · -- Along the first basis direction only the denominator changes, so the quotient rule gives
    -- the negative `ξ₂² / (2 ξ₁²)` coordinate.
    change
      (fderiv ℝ quadraticOverLinearMinusSqrtCore x)
          (Pi.single (i := (0 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)) =
        -((x 1) ^ 2 / (2 * (x 0) ^ 2))
    have hline_from_fderiv :
        HasDerivAt
          (fun t : ℝ =>
            quadraticOverLinearMinusSqrtCore
              (x + t • Pi.single (i := (0 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
          ((fderiv ℝ quadraticOverLinearMinusSqrtCore x)
            (Pi.single (i := (0 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ))) 0 := by
      simpa [HasLineDerivAt, quadraticOverLinearMinusSqrtCore] using
        (hdiff.hasFDerivAt.hasLineDerivAt
          (Pi.single (i := (0 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
    have hline_explicit :
        HasDerivAt
          (fun t : ℝ =>
            quadraticOverLinearMinusSqrtCore
              (x + t • Pi.single (i := (0 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
          (-(x 1 ^ 2 / (2 * x 0 ^ 2))) 0 := by
      have hnum : HasDerivAt (fun _t : ℝ => x 1 ^ 2) 0 0 := by
        simpa using (hasDerivAt_const (x := 0) (c := x 1 ^ 2))
      have hden_base : HasDerivAt (fun t : ℝ => x 0 + t) 1 0 := by
        simpa using (hasDerivAt_id 0).const_add (x 0)
      have hden : HasDerivAt (fun t : ℝ => 2 * (x 0 + t)) 2 0 := by
        simpa [mul_add, add_comm, add_left_comm, add_assoc] using hden_base.const_mul (2 : ℝ)
      have hquot :
          HasDerivAt (fun t : ℝ => x 1 ^ 2 / (2 * (x 0 + t)))
            ((0 * (2 * (x 0 + 0)) - x 1 ^ 2 * 2) / (2 * (x 0 + 0)) ^ 2) 0 := by
        simpa using hnum.div hden (by positivity)
      have hquot' :
          HasDerivAt (fun t : ℝ => x 1 ^ 2 / (2 * (x 0 + t)))
            (-(x 1 ^ 2 / (2 * x 0 ^ 2))) 0 := by
        convert hquot using 1
        field_simp [hx0.ne']
        ring
      have hsqrtConst : HasDerivAt (fun _t : ℝ => 2 * Real.sqrt (x 1)) 0 0 := by
        simpa using (hasDerivAt_const (x := 0) (c := 2 * Real.sqrt (x 1)))
      simpa [quadraticOverLinearMinusSqrtCore, Pi.add_apply, Pi.smul_apply] using hquot'
    exact hline_from_fderiv.unique hline_explicit
  · -- Along the second basis direction both the quadratic-over-linear term and the square-root
    -- term vary, and their derivatives combine to `ξ₂ / ξ₁ - ξ₂^{-1/2}`.
    change
      (fderiv ℝ quadraticOverLinearMinusSqrtCore x)
          (Pi.single (i := (1 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)) =
        x 1 / x 0 - 1 / Real.sqrt (x 1)
    have hline_from_fderiv :
        HasDerivAt
          (fun t : ℝ =>
            quadraticOverLinearMinusSqrtCore
              (x + t • Pi.single (i := (1 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
          ((fderiv ℝ quadraticOverLinearMinusSqrtCore x)
            (Pi.single (i := (1 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ))) 0 := by
      simpa [HasLineDerivAt, quadraticOverLinearMinusSqrtCore] using
        (hdiff.hasFDerivAt.hasLineDerivAt
          (Pi.single (i := (1 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
    have hline_explicit :
        HasDerivAt
          (fun t : ℝ =>
            quadraticOverLinearMinusSqrtCore
              (x + t • Pi.single (i := (1 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
          (x 1 / x 0 - 1 / Real.sqrt (x 1)) 0 := by
      have hbase : HasDerivAt (fun t : ℝ => x 1 + t) 1 0 := by
        simpa using (hasDerivAt_id 0).const_add (x 1)
      have hpow : HasDerivAt (fun t : ℝ => (x 1 + t) ^ 2) (2 * x 1) 0 := by
        simpa [two_mul] using hbase.pow 2
      have hquot : HasDerivAt (fun t : ℝ => (x 1 + t) ^ 2 / (2 * x 0))
          ((2 * x 1) / (2 * x 0)) 0 := by
        exact hpow.div_const (2 * x 0)
      have hquot' : HasDerivAt (fun t : ℝ => (x 1 + t) ^ 2 / (2 * x 0))
          (x 1 / x 0) 0 := by
        convert hquot using 1
        field_simp [hx0.ne']
      have hx1_add_ne : x 1 + 0 ≠ 0 := by
        simpa using hx1.ne'
      have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (x 1 + t))
          (1 / (2 * Real.sqrt (x 1))) 0 := by
        simpa using hbase.sqrt hx1_add_ne
      have hsqrt' : HasDerivAt (fun t : ℝ => 2 * Real.sqrt (x 1 + t))
          (1 / Real.sqrt (x 1)) 0 := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsqrt.const_mul (2 : ℝ)
      simpa [quadraticOverLinearMinusSqrtCore, Pi.add_apply, Pi.smul_apply] using
        hquot'.sub hsqrt'
    exact hline_from_fderiv.unique hline_explicit

/-- Helper for Example 26.5.0.1: the Euclidean gradient of the real core is the displayed map
on the open positive quadrant. -/
lemma helperForExample_26_5_0_1_core_hasGradientAt_formula
    {x : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) :
    euclideanGradientAt quadraticOverLinearMinusSqrtCore x =
      quadraticOverLinearMinusSqrtGradientMap x := by
  -- This repackages the coordinate computation in the exact form used by the extension lemmas.
  exact helperForExample_26_5_0_1_coordinateGradient_formula hx

/-- Helper for Example 26.5.0.1: the displayed gradient vector is an actual Euclidean
subgradient of the closed extension at every interior point. -/
lemma helperForExample_26_5_0_1_explicitGradient_mem_subdifferential
    {x : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) :
    dotProductEquiv ℝ (Fin 2) (quadraticOverLinearMinusSqrtGradientMap x) ∈
      subdifferentialAt quadraticOverLinearMinusSqrtFunction x := by
  rcases helperForExample_26_2_1_openQuadrantExtension_package with ⟨hproperExt, _hInterior⟩
  have hdiffOn :
      DifferentiableOn ℝ quadraticOverLinearMinusSqrtCore openPositiveQuadrantR2 := by
    intro y hy
    -- The real core is differentiable at every point of the open quadrant.
    exact
      (show DifferentiableAt ℝ quadraticOverLinearMinusSqrtCore y by
        simpa [quadraticOverLinearMinusSqrtCore] using
          helperForExample_26_2_1_coreDifferentiableAt_openQuadrant hy).differentiableWithinAt
  have hsub :
      IsEuclideanSubgradientAt quadraticOverLinearMinusSqrtFunction x
        (euclideanGradientAt quadraticOverLinearMinusSqrtCore x) := by
    -- The general closure-extension lemma applies to the open-quadrant extension of the core.
    exact
      helperForText_26_4_0_2_closedExtension_subgradient_at_coordinateGradient
        (hC_open := helperForExample_26_2_1_openQuadrant_isOpen) (hf_diff := hdiffOn)
        (hfExt := rfl)
        (hF := helperForExample_26_2_1_openQuadrantExtension_closure_eq_target.symm)
        hproperExt hx
  -- Rewrite the chosen Euclidean gradient with the explicit coordinate formula.
  simpa [IsEuclideanSubgradientAt,
    helperForExample_26_5_0_1_coordinateGradient_formula hx] using hsub

/-- Helper for Example 26.5.0.1: on the open positive quadrant the closed extension has the
explicit singleton subdifferential fiber. -/
lemma helperForExample_26_5_0_1_openQuadrant_subdifferential_eq_explicitSingleton
    {x : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) :
    subdifferentialAt quadraticOverLinearMinusSqrtFunction x =
      {dotProductEquiv ℝ (Fin 2) (quadraticOverLinearMinusSqrtGradientMap x)} := by
  rcases helperForExample_26_2_1_openQuadrant_subdifferential_singleton hx with ⟨g, hg⟩
  have hmemExplicit :
      dotProductEquiv ℝ (Fin 2) (quadraticOverLinearMinusSqrtGradientMap x) ∈
        subdifferentialAt quadraticOverLinearMinusSqrtFunction x :=
    helperForExample_26_5_0_1_explicitGradient_mem_subdifferential hx
  have hmemChosen :
      dotProductEquiv ℝ (Fin 2) g ∈
        subdifferentialAt quadraticOverLinearMinusSqrtFunction x := by
    simp [hg]
  have hEqDual :
      dotProductEquiv ℝ (Fin 2) g =
        dotProductEquiv ℝ (Fin 2) (quadraticOverLinearMinusSqrtGradientMap x) := by
    -- The existing singleton-fiber lemma forces the chosen witness to equal the explicit one.
    rw [hg] at hmemExplicit hmemChosen
    exact (Set.mem_singleton_iff.1 hmemExplicit).symm
  have hEqVec : g = quadraticOverLinearMinusSqrtGradientMap x :=
    (dotProductEquiv ℝ (Fin 2)).injective hEqDual
  -- Substituting the identified fiber element yields the explicit singleton description.
  simpa [hEqVec] using hg

/-- Helper for Example 26.5.0.1: any subgradient selector on the open positive quadrant must
coincide with the displayed explicit gradient map. -/
lemma helperForExample_26_5_0_1_subgradient_selector_eq_explicitGradient
    {grad : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hgrad :
      ∀ x ∈ openPositiveQuadrantR2,
        dotProductEquiv ℝ (Fin 2) (grad x) ∈
          subdifferentialAt quadraticOverLinearMinusSqrtFunction x) :
    ∀ x ∈ openPositiveQuadrantR2, grad x = quadraticOverLinearMinusSqrtGradientMap x := by
  intro x hx
  have hmem :
      dotProductEquiv ℝ (Fin 2) (grad x) ∈
        subdifferentialAt quadraticOverLinearMinusSqrtFunction x :=
    hgrad x hx
  have hsingleton :=
    helperForExample_26_5_0_1_openQuadrant_subdifferential_eq_explicitSingleton hx
  rw [hsingleton] at hmem
  exact
    (dotProductEquiv ℝ (Fin 2)).injective
      (by simpa using Set.mem_singleton_iff.1 hmem)

/-- Helper for Example 26.5.0.1: the displayed gradient map lands in the explicit dual domain
`C*`. -/
lemma helperForExample_26_5_0_1_gradient_mem_dualDomain
    {x : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) :
    quadraticOverLinearMinusSqrtGradientMap x ∈ quadraticOverLinearMinusSqrtDualDomain := by
  rcases hx with ⟨hx0, hx1⟩
  constructor
  · -- The first coordinate is `- ξ₂² / (2 ξ₁²)`, hence strictly negative on the open quadrant.
    have hpos : 0 < x 1 ^ 2 / (2 * x 0 ^ 2) := by positivity
    dsimp [quadraticOverLinearMinusSqrtGradientMap]
    linarith
  · have hratio_pos : 0 < x 1 / x 0 := by positivity
    have hsqrt :
        Real.sqrt (-2 * (quadraticOverLinearMinusSqrtGradientMap x) 0) = x 1 / x 0 := by
      have hcalc : -2 * (quadraticOverLinearMinusSqrtGradientMap x) 0 = (x 1 / x 0) ^ 2 := by
        calc
          -2 * (quadraticOverLinearMinusSqrtGradientMap x) 0
              = -2 * (-((x 1) ^ 2 / (2 * (x 0) ^ 2))) := by
                  simp [quadraticOverLinearMinusSqrtGradientMap]
          _ = (x 1 / x 0) ^ 2 := by
                field_simp [hx0.ne']
      rw [hcalc, Real.sqrt_sq_eq_abs, abs_of_nonneg hratio_pos.le]
    -- The second coordinate is exactly `ξ₂ / ξ₁` minus a positive correction term.
    rw [hsqrt]
    dsimp [quadraticOverLinearMinusSqrtGradientMap]
    exact sub_lt_self _ (by positivity)

/-- Helper for Example 26.5.0.1: evaluating the Fenchel-Young expression at the explicit inverse
point reduces to the displayed reciprocal formula on the dual domain `C*`. -/
lemma helperForExample_26_5_0_1_conjugate_value_at_explicitInverse
    {xStar : Fin 2 → ℝ} (hxStar : xStar ∈ quadraticOverLinearMinusSqrtDualDomain) :
    (((euclideanPairing (n := 2)
        (quadraticOverLinearMinusSqrtGradientInverse xStar) xStar : ℝ) : EReal) -
      quadraticOverLinearMinusSqrtFunction
        (quadraticOverLinearMinusSqrtGradientInverse xStar)) =
      ((1 / (Real.sqrt (-2 * xStar 0) - xStar 1) : ℝ) : EReal) := by
  rcases hxStar with ⟨hx0neg, hx1lt⟩
  set s : ℝ := Real.sqrt (-2 * xStar 0)
  set d : ℝ := s - xStar 1
  have hs_pos : 0 < s := by
    apply Real.sqrt_pos.2
    nlinarith
  have hd_pos : 0 < d := by
    dsimp [d]
    linarith
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hx0_eq : xStar 0 = -(s ^ 2) / 2 := by
    have hs_sq : s ^ 2 = -2 * xStar 0 := by
      dsimp [s]
      simpa [pow_two] using Real.sq_sqrt (show 0 ≤ -2 * xStar 0 by nlinarith)
    nlinarith
  have hx1_eq : xStar 1 = s - d := by
    dsimp [d]
    ring
  have hsqrt_inv_sq : Real.sqrt (1 / d ^ 2) = 1 / d := by
    have hrewrite : 1 / d ^ 2 = (1 / d) ^ 2 := by
      field_simp [hd_ne]
    rw [hrewrite, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hpair :
      (euclideanPairing (n := 2)
        (quadraticOverLinearMinusSqrtGradientInverse xStar) xStar : ℝ) =
        s / (2 * d ^ 2) - 1 / d := by
    -- Expanding the pairing and rewriting the dual coordinates leaves a rational identity in
    -- the auxiliary variables `s = √(-2 ξ₁*)` and `d = s - ξ₂*`.
    simp [euclideanPairing, quadraticOverLinearMinusSqrtGradientInverse, dotProduct,
      Fin.sum_univ_two, s, d]
    rw [hx0_eq, hx1_eq]
    field_simp [hs_ne, hd_ne]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hs_pos.le]
    ring
  have hmem :
      quadraticOverLinearMinusSqrtGradientInverse xStar ∈ openPositiveQuadrantR2 :=
    (helperForExample_26_5_0_1_explicitInverse_mem_and_rightInv
      (xStar := xStar) ⟨hx0neg, hx1lt⟩).1
  have hfun :
      quadraticOverLinearMinusSqrtFunction
          (quadraticOverLinearMinusSqrtGradientInverse xStar) =
        (((s / (2 * d ^ 2) - 2 / d : ℝ)) : EReal) := by
    -- On the inverse point we are back in the real branch of the primal function.
    rw [quadraticOverLinearMinusSqrtFunction, if_pos ⟨hmem.1, hmem.2.le⟩]
    have hvalueReal :
        ((quadraticOverLinearMinusSqrtGradientInverse xStar) 1 ^ 2 /
            (2 * (quadraticOverLinearMinusSqrtGradientInverse xStar) 0) -
          2 * Real.sqrt ((quadraticOverLinearMinusSqrtGradientInverse xStar) 1) : ℝ) =
          s / (2 * d ^ 2) - 2 / d := by
      change ((1 / d ^ 2) ^ 2 / (2 * (1 / (s * d ^ 2))) - 2 * Real.sqrt (1 / d ^ 2) : ℝ) =
          s / (2 * d ^ 2) - 2 / d
      rw [hsqrt_inv_sq]
      field_simp [hs_ne, hd_ne]
    exact congrArg (fun r : ℝ => (r : EReal)) hvalueReal
  -- The Fenchel-Young subtraction collapses to a single reciprocal after one final field
  -- calculation in `d = √(-2 ξ₁*) - ξ₂*`.
  rw [hpair, hfun, EReal.coe_sub]
  have hreal :
      s / (2 * d ^ 2) - 1 / d - (s / (2 * d ^ 2) - 2 / d) = 1 / d := by
    field_simp [hd_ne]
    ring
  exact congrArg (fun r : ℝ => (r : EReal)) hreal

-- Proof sketch: combine Example 26.2.1 with Theorem 26.5. Use the explicit gradient formulas on
-- the open positive quadrant to identify the image and solve for the inverse map, then evaluate
-- the Legendre-transform identity `f*(x*) = ⟪(∇f)⁻¹ x*, x*⟫ - f((∇f)⁻¹ x*)` to obtain the stated
-- conjugate formula and package the resulting dual pair as an involutive Legendre conjugacy.
/-- Example 26.5.0.1: for
`f(ξ₁, ξ₂) = ξ₂^2 / (2 ξ₁) - 2 √ξ₂` on `C = {(ξ₁, ξ₂) | ξ₁ > 0, ξ₂ > 0}`, extended by
`f(0, 0) = 0` and `f = +∞` elsewhere, the pair `(C, f)` is of Legendre type. Its gradient on `C`
is given by
`ξ₁* = - ξ₂^2 / (2 ξ₁^2)` and `ξ₂* = ξ₂ / ξ₁ - ξ₂^{-1/2}`, the image of this gradient is
`C* = {(ξ₁*, ξ₂*) | ξ₁* < 0, ξ₂* < (-2 ξ₁*)^{1/2}} = int (dom f*)`, and writing
`s := (-2 ξ₁*)^{1/2}`, one has `ξ₂^{-1/2} = s - ξ₂*`, hence
`ξ₂ = 1 / (s - ξ₂*)^2` and `ξ₁ = 1 / (s * (s - ξ₂*)^2)` for `(∇ f)⁻¹(x*)`. Moreover,
`f*(x*) = 1 / ((-2 ξ₁*)^{1/2} - ξ₂*)` on `C*`, this agrees there with the Fenchel conjugate of
`f`, and `(C*, f*)` is also of Legendre type and is the Legendre conjugate of `(C, f)`. -/
theorem quadraticOverLinearMinusSqrtFunction_has_explicit_legendre_dual_data :
    IsLegendreTypeOn openPositiveQuadrantR2 quadraticOverLinearMinusSqrtFunction ∧
      (∀ x ∈ openPositiveQuadrantR2,
        (quadraticOverLinearMinusSqrtGradientMap x) 0 =
            -((x 1) ^ 2 / (2 * (x 0) ^ 2)) ∧
          (quadraticOverLinearMinusSqrtGradientMap x) 1 =
            x 1 / x 0 - 1 / Real.sqrt (x 1)) ∧
      quadraticOverLinearMinusSqrtGradientMap '' openPositiveQuadrantR2 =
        quadraticOverLinearMinusSqrtDualDomain ∧
      quadraticOverLinearMinusSqrtDualDomain =
        interior
          (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
            (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)) ∧
      (∀ xStar ∈ quadraticOverLinearMinusSqrtDualDomain,
        let s := Real.sqrt (-2 * xStar 0)
        quadraticOverLinearMinusSqrtGradientInverse xStar ∈ openPositiveQuadrantR2 ∧
          quadraticOverLinearMinusSqrtGradientMap
              (quadraticOverLinearMinusSqrtGradientInverse xStar) = xStar ∧
          (quadraticOverLinearMinusSqrtGradientInverse xStar) 0 =
            1 / (s * (s - xStar 1) ^ 2) ∧
          (quadraticOverLinearMinusSqrtGradientInverse xStar) 1 =
            1 / ((s - xStar 1) ^ 2)) ∧
      Set.EqOn
        (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)
        quadraticOverLinearMinusSqrtDualConjugateFunction
        quadraticOverLinearMinusSqrtDualDomain ∧
      (∀ xStar ∈ quadraticOverLinearMinusSqrtDualDomain,
        quadraticOverLinearMinusSqrtDualConjugateFunction xStar =
          ((1 / (Real.sqrt (-2 * xStar 0) - xStar 1) : ℝ) : EReal)) ∧
      IsLegendreTypeOn quadraticOverLinearMinusSqrtDualDomain
        quadraticOverLinearMinusSqrtDualConjugateFunction ∧
      ∃ L : InvolutiveLegendreTransformationOn (euclideanPairing (n := 2))
          openPositiveQuadrantR2 quadraticOverLinearMinusSqrtFunction,
        L.target = quadraticOverLinearMinusSqrtDualDomain ∧
          L.toFun = quadraticOverLinearMinusSqrtGradientMap ∧
          L.invFun = quadraticOverLinearMinusSqrtGradientInverse ∧
          Set.EqOn L.conjFun quadraticOverLinearMinusSqrtDualConjugateFunction
            quadraticOverLinearMinusSqrtDualDomain := by
  rcases helperForExample_26_5_0_1_closedProper_lsc_and_interiorDomain with
    ⟨hproper, hclosed, hinterior⟩
  rcases
      quadraticOverLinearMinusSqrtFunction_has_positiveQuadrantSubdifferentialDomain_and_essential_properties
    with ⟨_hSubdom, hstrict, _haxis, _hnotStrict, _hessStrict, hessSmooth⟩
  have hLegendre :
      IsLegendreTypeOn openPositiveQuadrantR2 quadraticOverLinearMinusSqrtFunction := by
    -- The earlier Example 26.2.1 package supplies strict convexity and essential smoothness,
    -- while the interior-domain helper rewrites Theorem 26.4.1.5 to the present open quadrant.
    have hstrictInterior :
        StrictConvexOn ℝ
          (interior (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
            quadraticOverLinearMinusSqrtFunction))
          (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal) := by
      simpa [hinterior] using hstrict
    have hLegInterior :
        IsLegendreTypeOn
          (interior (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
            quadraticOverLinearMinusSqrtFunction))
          quadraticOverLinearMinusSqrtFunction := by
      exact
        (helperForProposition_26_4_1_5_isLegendreTypeOn_interior_iff_strictConvexOn_and_essentiallySmooth
          (f := quadraticOverLinearMinusSqrtFunction) hproper).2
          ⟨hstrictInterior, hessSmooth⟩
    simpa [hinterior] using hLegInterior
  have hGradientCoords :
      ∀ x ∈ openPositiveQuadrantR2,
        (quadraticOverLinearMinusSqrtGradientMap x) 0 =
            -((x 1) ^ 2 / (2 * (x 0) ^ 2)) ∧
          (quadraticOverLinearMinusSqrtGradientMap x) 1 =
            x 1 / x 0 - 1 / Real.sqrt (x 1) := by
    intro x hx
    -- The coordinate formulas are already built into the explicit gradient definition.
    simp [quadraticOverLinearMinusSqrtGradientMap]
  have hInverseData :
      ∀ xStar ∈ quadraticOverLinearMinusSqrtDualDomain,
        let s := Real.sqrt (-2 * xStar 0)
        quadraticOverLinearMinusSqrtGradientInverse xStar ∈ openPositiveQuadrantR2 ∧
          quadraticOverLinearMinusSqrtGradientMap
              (quadraticOverLinearMinusSqrtGradientInverse xStar) = xStar ∧
          (quadraticOverLinearMinusSqrtGradientInverse xStar) 0 =
            1 / (s * (s - xStar 1) ^ 2) ∧
          (quadraticOverLinearMinusSqrtGradientInverse xStar) 1 =
            1 / ((s - xStar 1) ^ 2) := by
    intro xStar hxStar
    -- The explicit inverse formula is algebraically correct on `C*`, and its coordinates are
    -- definitionally the displayed ones.
    dsimp
    rcases helperForExample_26_5_0_1_explicitInverse_mem_and_rightInv hxStar with
      ⟨hmem, hright⟩
    exact ⟨hmem, hright, rfl, rfl⟩
  have hproperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
        quadraticOverLinearMinusSqrtFunction :=
    helperForTheorem_25_6_properConvexFunctionOn (f := quadraticOverLinearMinusSqrtFunction) hproper
  have hconv :
      ConvexFunction quadraticOverLinearMinusSqrtFunction := by
    simpa [ConvexFunction] using hproperOn.1
  have hclosedConv :
      ClosedConvexFunction quadraticOverLinearMinusSqrtFunction := ⟨hconv, hclosed⟩
  have hLegendrePackageRaw :=
    legendreTypeOn_interior_iff_conjugate_legendreTypeOn_interior_with_mutualLegendreConjugacy
      (f := quadraticOverLinearMinusSqrtFunction) hproper hclosed
  have hLegendrePackage :=
    hLegendrePackageRaw.2
      (show
        IsLegendreTypeOn
          (interior (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
            quadraticOverLinearMinusSqrtFunction))
          quadraticOverLinearMinusSqrtFunction from by
          simpa [hinterior] using hLegendre)
  rcases hLegendrePackage with
    ⟨L, hLtarget, hLconj, LStar, hLStarTarget, hLStarConj,
      grad, gradStar, hLfun, hLStarFun, hGradMem, hGradUnique,
      hGradStarMem, hGradStarUnique, hHomeomorphPkg⟩
  have hGradEq :
      ∀ x ∈ openPositiveQuadrantR2,
        grad x = quadraticOverLinearMinusSqrtGradientMap x := by
    have hGradMemOpen :
        ∀ x ∈ openPositiveQuadrantR2,
          dotProductEquiv ℝ (Fin 2) (grad x) ∈
            subdifferentialAt quadraticOverLinearMinusSqrtFunction x := by
      intro x hx
      have hxInterior :
          x ∈
            interior
              (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
                quadraticOverLinearMinusSqrtFunction) := by
        simpa [hinterior] using hx
      exact hGradMem x hxInterior
    -- The explicit singleton fiber on the primal side identifies the abstract selector uniquely.
    exact
      helperForExample_26_5_0_1_subgradient_selector_eq_explicitGradient
        (grad := grad) hGradMemOpen
  have hImage :
      quadraticOverLinearMinusSqrtGradientMap '' openPositiveQuadrantR2 =
        quadraticOverLinearMinusSqrtDualDomain := by
    ext xStar
    constructor
    · intro hxStar
      rcases hxStar with ⟨x, hx, rfl⟩
      exact helperForExample_26_5_0_1_gradient_mem_dualDomain hx
    · intro hxStar
      refine ⟨quadraticOverLinearMinusSqrtGradientInverse xStar, ?_, ?_⟩
      · exact (helperForExample_26_5_0_1_explicitInverse_mem_and_rightInv hxStar).1
      · exact (helperForExample_26_5_0_1_explicitInverse_mem_and_rightInv hxStar).2
  have hImageInterior :
      quadraticOverLinearMinusSqrtGradientMap '' openPositiveQuadrantR2 =
        interior
          (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
            (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)) := by
    -- The abstract image equality from Theorem 26.5 becomes explicit after identifying `L.toFun`
    -- with the displayed gradient on the primal open quadrant.
    calc
      quadraticOverLinearMinusSqrtGradientMap '' openPositiveQuadrantR2 =
          L.toFun ''
            interior
              (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
                quadraticOverLinearMinusSqrtFunction) := by
        ext xStar
        constructor
        · intro hxStar
          rcases hxStar with ⟨x, hx, rfl⟩
          refine ⟨x, ?_, ?_⟩
          · simpa [hinterior] using hx
          · simpa [hLfun] using hGradEq x hx
        · intro hxStar
          rcases hxStar with ⟨x, hx, rfl⟩
          refine ⟨x, ?_, ?_⟩
          · simpa [hinterior] using hx
          · have hxOpen : x ∈ openPositiveQuadrantR2 := by simpa [hinterior] using hx
            simpa [hLfun] using (hGradEq x hxOpen).symm
      _ = L.target := L.image_eq.symm
      _ = interior
            (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)) := hLtarget
  have hDualDomainInterior :
      quadraticOverLinearMinusSqrtDualDomain =
        interior
          (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
            (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)) := by
    -- The explicit dual-domain inequalities agree with the abstract target because both sets are
    -- the image of the same explicit gradient map.
    calc
      quadraticOverLinearMinusSqrtDualDomain =
          quadraticOverLinearMinusSqrtGradientMap '' openPositiveQuadrantR2 := hImage.symm
      _ = interior
            (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)) := hImageInterior
  have hGradStarEq :
      ∀ xStar ∈ quadraticOverLinearMinusSqrtDualDomain,
        gradStar xStar = quadraticOverLinearMinusSqrtGradientInverse xStar := by
    intro xStar hxStar
    rcases helperForExample_26_5_0_1_explicitInverse_mem_and_rightInv hxStar with
      ⟨hy, hright⟩
    have hySub :
        dotProductEquiv ℝ (Fin 2) xStar ∈
          subdifferentialAt quadraticOverLinearMinusSqrtFunction
            (quadraticOverLinearMinusSqrtGradientInverse xStar) := by
      have hyExplicit :
          dotProductEquiv ℝ (Fin 2)
              (quadraticOverLinearMinusSqrtGradientMap
                (quadraticOverLinearMinusSqrtGradientInverse xStar)) ∈
            subdifferentialAt quadraticOverLinearMinusSqrtFunction
              (quadraticOverLinearMinusSqrtGradientInverse xStar) :=
        helperForExample_26_5_0_1_explicitGradient_mem_subdifferential hy
      simpa [hright] using hyExplicit
    have hyEuclidean :
        IsEuclideanSubgradientAt quadraticOverLinearMinusSqrtFunction
          (quadraticOverLinearMinusSqrtGradientInverse xStar) xStar := by
      simpa [IsEuclideanSubgradientAt] using hySub
    have hxStarEuclidean :
        IsEuclideanSubgradientAt
          (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction) xStar
          (quadraticOverLinearMinusSqrtGradientInverse xStar) :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := quadraticOverLinearMinusSqrtFunction) hclosedConv hproperOn
        (quadraticOverLinearMinusSqrtGradientInverse xStar) xStar).2 hyEuclidean
    have hxStarSub :
        dotProductEquiv ℝ (Fin 2)
            (quadraticOverLinearMinusSqrtGradientInverse xStar) ∈
          subdifferentialAt
            (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction) xStar := by
      simpa [IsEuclideanSubgradientAt] using hxStarEuclidean
    have hxStarInterior :
        xStar ∈
          interior
            (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)) := by
      simpa [hDualDomainInterior] using hxStar
    exact (hGradStarUnique hxStarInterior hxStarSub).symm
  have hEqOnFenchelDual :
      Set.EqOn
        (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)
        quadraticOverLinearMinusSqrtDualConjugateFunction
        quadraticOverLinearMinusSqrtDualDomain := by
    intro xStar hxStar
    have hxStarInterior :
        xStar ∈
          interior
            (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)) := by
      simpa [hDualDomainInterior] using hxStar
    have hy :
        quadraticOverLinearMinusSqrtGradientInverse xStar ∈ openPositiveQuadrantR2 :=
      (helperForExample_26_5_0_1_explicitInverse_mem_and_rightInv hxStar).1
    have hyInterior :
        quadraticOverLinearMinusSqrtGradientInverse xStar ∈
          interior
            (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              quadraticOverLinearMinusSqrtFunction) := by
      simpa [hinterior] using hy
    have hto :
        L.toFun (quadraticOverLinearMinusSqrtGradientInverse xStar) = xStar := by
      calc
        L.toFun (quadraticOverLinearMinusSqrtGradientInverse xStar)
            = grad (quadraticOverLinearMinusSqrtGradientInverse xStar) := by
                simp [hLfun]
        _ = quadraticOverLinearMinusSqrtGradientMap
              (quadraticOverLinearMinusSqrtGradientInverse xStar) := by
              exact hGradEq _ hy
        _ = xStar :=
              (helperForExample_26_5_0_1_explicitInverse_mem_and_rightInv hxStar).2
    have hLegendreValue :
        L.conjFun xStar =
          (((euclideanPairing (n := 2)
              (quadraticOverLinearMinusSqrtGradientInverse xStar) xStar : ℝ) : EReal) -
            quadraticOverLinearMinusSqrtFunction
              (quadraticOverLinearMinusSqrtGradientInverse xStar)) := by
      simpa [hto, euclideanPairing, dotProduct, Fin.sum_univ_two] using L.value_eq hyInterior
    calc
      fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction xStar = L.conjFun xStar := by
        exact (hLconj hxStarInterior).symm
      _ =
          (((euclideanPairing (n := 2)
              (quadraticOverLinearMinusSqrtGradientInverse xStar) xStar : ℝ) : EReal) -
            quadraticOverLinearMinusSqrtFunction
              (quadraticOverLinearMinusSqrtGradientInverse xStar)) := hLegendreValue
      _ = ((1 / (Real.sqrt (-2 * xStar 0) - xStar 1) : ℝ) : EReal) :=
            helperForExample_26_5_0_1_conjugate_value_at_explicitInverse hxStar
      _ = quadraticOverLinearMinusSqrtDualConjugateFunction xStar := by
            simp [quadraticOverLinearMinusSqrtDualConjugateFunction, hxStar]
  have hDualValueExplicit :
      ∀ xStar ∈ quadraticOverLinearMinusSqrtDualDomain,
        quadraticOverLinearMinusSqrtDualConjugateFunction xStar =
          ((1 / (Real.sqrt (-2 * xStar 0) - xStar 1) : ℝ) : EReal) := by
    intro xStar hxStar
    -- The explicit extension agrees with its displayed real formula on the dual domain by
    -- definition.
    simp [quadraticOverLinearMinusSqrtDualConjugateFunction, hxStar]
  refine
    ⟨hLegendre, hGradientCoords, hImage, hDualDomainInterior, hInverseData, hEqOnFenchelDual,
      hDualValueExplicit, ?_, ?_⟩
  -- Route correction: the explicit Fenchel-value computation is now isolated in
  -- `helperForExample_26_5_0_1_conjugate_value_at_explicitInverse`, and the on-domain
  -- Fenchel-conjugate equality is now proved as `hEqOnFenchelDual`. The remaining work is to
  -- make the explicit dual extension convex on its own terms, identify its singleton fibers on
  -- `C*`, and then reuse the abstract Theorem 26.5 package only for the blowup and conjugacy
  -- bookkeeping.
  · let dualRealBranch : (Fin 2 → ℝ) → ℝ :=
      fun xStar => 1 / (Real.sqrt (-2 * xStar 0) - xStar 1)
    let dualExt : (Fin 2 → ℝ) → EReal :=
      fun xStar => (dualRealBranch xStar : EReal) +
        indicatorFunction quadraticOverLinearMinusSqrtDualDomain xStar
    have hLegendreDualAbstractInterior :
        IsLegendreTypeOn
          (interior
            (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)))
          (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction) :=
      (hLegendrePackageRaw.1).1
        (show
          IsLegendreTypeOn
            (interior
              (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
                quadraticOverLinearMinusSqrtFunction))
            quadraticOverLinearMinusSqrtFunction from by
            simpa [hinterior] using hLegendre)
    have hLegendreDualAbstract :
        IsLegendreTypeOn quadraticOverLinearMinusSqrtDualDomain
          (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction) := by
      simpa [hDualDomainInterior] using hLegendreDualAbstractInterior
    rcases hLegendreDualAbstract with
      ⟨hCStar_nonempty, hCStar_open, hCStar_convex, hCStar_finite, hCStar_strict, hSmoothStar⟩
    rcases hSmoothStar with
      ⟨hproperCStarFenchel, gradAbs, hgradAbsMem, hgradAbsUnique, hgradAbsBlowup⟩
    have hFenchelLeExplicit :
        ∀ xStar : Fin 2 → ℝ,
          fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction xStar ≤
            quadraticOverLinearMinusSqrtDualConjugateFunction xStar := by
      intro xStar
      by_cases hxStar : xStar ∈ quadraticOverLinearMinusSqrtDualDomain
      · exact le_of_eq (hEqOnFenchelDual hxStar)
      · simp [quadraticOverLinearMinusSqrtDualConjugateFunction, hxStar]
    have hEqOnFenchelToDualBranch :
        Set.EqOn
          (fun xStar =>
            (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction xStar).toReal)
          dualRealBranch quadraticOverLinearMinusSqrtDualDomain := by
      intro xStar hxStar
      have hvalue :
          fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction xStar =
            ((dualRealBranch xStar : ℝ) : EReal) := by
        calc
          fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction xStar =
              quadraticOverLinearMinusSqrtDualConjugateFunction xStar := hEqOnFenchelDual hxStar
          _ = ((dualRealBranch xStar : ℝ) : EReal) := by
              simp [dualRealBranch, quadraticOverLinearMinusSqrtDualConjugateFunction, hxStar]
      simpa using congrArg EReal.toReal hvalue
    have hDualBranch_convex :
        ConvexOn ℝ quadraticOverLinearMinusSqrtDualDomain dualRealBranch := by
      -- The explicit real branch inherits convexity from the abstract dual strict-convexity
      -- package because the two real-valued formulas agree on `C*`.
      exact (hCStar_strict.convexOn).congr hEqOnFenchelToDualBranch
    have hDualProperExtRaw :
        ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ)) dualExt ∧
          interior (effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) dualExt) =
            quadraticOverLinearMinusSqrtDualDomain := by
      -- Extending the real branch by `+∞` outside the open convex domain produces a proper convex
      -- ambient function whose interior effective domain is exactly `C*`.
      simpa [dualExt, dualRealBranch] using
        (helperForCorollary_25_5_1_properConvexExtension
          (hCopen := hCStar_open) (_hCconv := hCStar_convex)
          hCStar_nonempty hDualBranch_convex)
    have hDualExtEq :
        dualExt = quadraticOverLinearMinusSqrtDualConjugateFunction := by
      funext xStar
      by_cases hxStar : xStar ∈ quadraticOverLinearMinusSqrtDualDomain
      · simp [dualExt, dualRealBranch, quadraticOverLinearMinusSqrtDualConjugateFunction,
          indicatorFunction, hxStar]
      · simp [dualExt, dualRealBranch, quadraticOverLinearMinusSqrtDualConjugateFunction,
          indicatorFunction, hxStar]
    have hDualProperExt :
        ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
            quadraticOverLinearMinusSqrtDualConjugateFunction ∧
          interior (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
            quadraticOverLinearMinusSqrtDualConjugateFunction) =
            quadraticOverLinearMinusSqrtDualDomain := by
      simpa [hDualExtEq] using hDualProperExtRaw
    have hDualSingletonFiber :
        ∀ xStar ∈ quadraticOverLinearMinusSqrtDualDomain,
          subdifferentialAt quadraticOverLinearMinusSqrtDualConjugateFunction xStar =
            {dotProductEquiv ℝ (Fin 2)
              (quadraticOverLinearMinusSqrtGradientInverse xStar)} := by
      intro xStar hxStar
      have hDualBranch_diff : DifferentiableAt ℝ dualRealBranch xStar := by
        -- The branch `x* ↦ 1 / (√(-2 ξ₁*) - ξ₂*)` is differentiable on `C*` because the square-root
        -- argument and the denominator stay strictly positive there.
        have hsqrtArg_pos : 0 < -2 * xStar 0 := by
          rcases hxStar with ⟨hx0neg, _hx1lt⟩
          nlinarith
        have hsqrtDiff :
            DifferentiableAt ℝ (fun y : Fin 2 → ℝ => Real.sqrt (-2 * y 0)) xStar := by
          refine DifferentiableAt.sqrt ?_ ?_
          · fun_prop
          · nlinarith
        have hden_pos : 0 < Real.sqrt (-2 * xStar 0) - xStar 1 := by
          rcases hxStar with ⟨_hx0neg, hx1lt⟩
          linarith [Real.sqrt_pos.2 hsqrtArg_pos]
        have hdenDiff :
            DifferentiableAt ℝ (fun y : Fin 2 → ℝ => Real.sqrt (-2 * y 0) - y 1) xStar := by
          exact hsqrtDiff.sub ((differentiable_apply 1).differentiableAt)
        simpa [dualRealBranch, one_div] using hdenDiff.inv (ne_of_gt hden_pos)
      rcases
          helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
            (hCopen := hCStar_open) (C := quadraticOverLinearMinusSqrtDualDomain)
            (f := dualRealBranch) (x := xStar) hxStar hDualBranch_diff with
        ⟨hExtDiff, _hExtGradEq⟩
      have hDualConv :
          ConvexFunction dualExt := by
        simpa [ConvexFunction] using hDualProperExtRaw.1.1
      have hpreimage :
          ((dotProductEquiv ℝ (Fin 2)) ⁻¹'
              subdifferentialAt quadraticOverLinearMinusSqrtDualConjugateFunction xStar) =
            ({erealGradientAt hExtDiff} : Set (Fin 2 → ℝ)) := by
        -- Differentiability of the explicit extension collapses its Euclideanized fiber to a
        -- singleton.
        simpa [hDualExtEq] using
          (helperForTheorem_25_7_subdifferentialPreimage_eq_singleton_gradient
            hDualConv hExtDiff)
      have hxStarInterior :
          xStar ∈
            interior
              (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
                (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)) := by
        simpa [hDualDomainInterior] using hxStar
      have hGradStarMemExplicit :
          dotProductEquiv ℝ (Fin 2) (gradStar xStar) ∈
            subdifferentialAt quadraticOverLinearMinusSqrtDualConjugateFunction xStar := by
        have hGradStarMemFenchel :
            dotProductEquiv ℝ (Fin 2) (gradStar xStar) ∈
              subdifferentialAt
                (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction) xStar :=
          hGradStarMem xStar hxStarInterior
        rw [mem_subdifferentialAt_iff] at hGradStarMemFenchel ⊢
        intro z
        -- Dominating the abstract conjugate by the explicit `+∞` extension keeps the abstract
        -- chosen subgradient valid for the explicit dual.
        calc
          quadraticOverLinearMinusSqrtDualConjugateFunction z ≥
              fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction z :=
            hFenchelLeExplicit z
          _ ≥
              fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction xStar +
                (((dotProductEquiv ℝ (Fin 2) (gradStar xStar)) (z - xStar) : ℝ) : EReal) :=
              hGradStarMemFenchel z
          _ =
              quadraticOverLinearMinusSqrtDualConjugateFunction xStar +
                (((dotProductEquiv ℝ (Fin 2) (gradStar xStar)) (z - xStar) : ℝ) : EReal) := by
              rw [hEqOnFenchelDual hxStar]
      have hGradStarEqGradient :
          gradStar xStar = erealGradientAt hExtDiff := by
        have hmemPreimage :
            gradStar xStar ∈
              ((dotProductEquiv ℝ (Fin 2)) ⁻¹'
                subdifferentialAt quadraticOverLinearMinusSqrtDualConjugateFunction xStar) := by
          simpa using hGradStarMemExplicit
        simpa [hpreimage] using hmemPreimage
      have hExplicitGradient :
          erealGradientAt hExtDiff =
            quadraticOverLinearMinusSqrtGradientInverse xStar := by
        calc
          erealGradientAt hExtDiff = gradStar xStar := hGradStarEqGradient.symm
          _ = quadraticOverLinearMinusSqrtGradientInverse xStar := hGradStarEq xStar hxStar
      ext ξ
      constructor
      · intro hξ
        have hpre :
            (dotProductEquiv ℝ (Fin 2)).symm ξ ∈
              ((dotProductEquiv ℝ (Fin 2)) ⁻¹'
                subdifferentialAt quadraticOverLinearMinusSqrtDualConjugateFunction xStar) := by
          simpa using hξ
        have hs :
            (dotProductEquiv ℝ (Fin 2)).symm ξ =
              quadraticOverLinearMinusSqrtGradientInverse xStar := by
          simpa [hpreimage, hExplicitGradient] using hpre
        rw [Set.mem_singleton_iff]
        have hdualEq := congrArg (dotProductEquiv ℝ (Fin 2)) hs
        simpa using hdualEq
      · intro hξ
        rw [Set.mem_singleton_iff] at hξ
        rw [hξ]
        have hpre :
            quadraticOverLinearMinusSqrtGradientInverse xStar ∈
              ((dotProductEquiv ℝ (Fin 2)) ⁻¹'
                subdifferentialAt quadraticOverLinearMinusSqrtDualConjugateFunction xStar) := by
          simpa [hpreimage, hExplicitGradient]
        simpa using hpre
    have hEqOnFenchelToExplicitToReal :
        Set.EqOn
          (fun xStar =>
            (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction xStar).toReal)
          (fun xStar =>
            (quadraticOverLinearMinusSqrtDualConjugateFunction xStar).toReal)
          quadraticOverLinearMinusSqrtDualDomain := by
      intro xStar hxStar
      simpa using congrArg EReal.toReal (hEqOnFenchelDual hxStar)
    have hDualStrictExplicit :
        StrictConvexOn ℝ quadraticOverLinearMinusSqrtDualDomain
          (fun xStar => (quadraticOverLinearMinusSqrtDualConjugateFunction xStar).toReal) := by
      -- Strict convexity transfers directly because the abstract dual and the explicit formula
      -- agree pointwise on `C*`.
      exact hCStar_strict.congr hEqOnFenchelToExplicitToReal
    have hDualProperEReal :
        ProperConvexERealFunction (F := (Fin 2 → ℝ))
          quadraticOverLinearMinusSqrtDualConjugateFunction :=
      helperForLemma_26_2_properConvexERealFunction hDualProperExt.1
    have hDualProperOnInterior :
        ProperConvexFunctionOn
          (interior
            (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              quadraticOverLinearMinusSqrtDualConjugateFunction))
          quadraticOverLinearMinusSqrtDualConjugateFunction := by
      have hInteriorNonempty :
          (interior
            (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              quadraticOverLinearMinusSqrtDualConjugateFunction)).Nonempty := by
        simpa [hDualProperExt.2] using hCStar_nonempty
      exact
        (helperForProposition_26_4_1_5_properConvexFunctionOn_interior
          (f := quadraticOverLinearMinusSqrtDualConjugateFunction) hDualProperEReal)
          hInteriorNonempty
    have hDualProperOn :
        ProperConvexFunctionOn quadraticOverLinearMinusSqrtDualDomain
          quadraticOverLinearMinusSqrtDualConjugateFunction := by
      simpa [hDualProperExt.2] using hDualProperOnInterior
    have hGradAbsEqExplicit :
        ∀ xStar ∈ quadraticOverLinearMinusSqrtDualDomain,
          gradAbs xStar = quadraticOverLinearMinusSqrtGradientInverse xStar := by
      intro xStar hxStar
      have hGradAbsMemExplicit :
          dotProductEquiv ℝ (Fin 2) (gradAbs xStar) ∈
            subdifferentialAt quadraticOverLinearMinusSqrtDualConjugateFunction xStar := by
        have hGradAbsMemFenchel :
            dotProductEquiv ℝ (Fin 2) (gradAbs xStar) ∈
              subdifferentialAt
                (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction) xStar :=
          hgradAbsMem xStar hxStar
        rw [mem_subdifferentialAt_iff] at hGradAbsMemFenchel ⊢
        intro z
        -- The domination bridge again transfers the abstract subgradient witness to the explicit
        -- dual extension.
        calc
          quadraticOverLinearMinusSqrtDualConjugateFunction z ≥
              fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction z :=
            hFenchelLeExplicit z
          _ ≥
              fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction xStar +
                (((dotProductEquiv ℝ (Fin 2) (gradAbs xStar)) (z - xStar) : ℝ) : EReal) :=
              hGradAbsMemFenchel z
          _ =
              quadraticOverLinearMinusSqrtDualConjugateFunction xStar +
                (((dotProductEquiv ℝ (Fin 2) (gradAbs xStar)) (z - xStar) : ℝ) : EReal) := by
              rw [hEqOnFenchelDual hxStar]
      have hsingleton := hDualSingletonFiber xStar hxStar
      rw [hsingleton] at hGradAbsMemExplicit
      exact
        (dotProductEquiv ℝ (Fin 2)).injective
          (by simpa using Set.mem_singleton_iff.1 hGradAbsMemExplicit)
    refine
      ⟨hCStar_nonempty, hCStar_open, hCStar_convex, ?_, hDualStrictExplicit, ?_⟩
    · -- On `C*` the explicit dual is by definition a finite real value.
      intro xStar hxStar
      simp [quadraticOverLinearMinusSqrtDualConjugateFunction, hxStar]
    · refine ⟨hDualProperOn, quadraticOverLinearMinusSqrtGradientInverse, ?_, ?_, ?_⟩
      · intro xStar hxStar
        rw [hDualSingletonFiber xStar hxStar]
        simp
      · intro xStar x hxStar hxSub
        rw [hDualSingletonFiber xStar hxStar] at hxSub
        exact
          (dotProductEquiv ℝ (Fin 2)).injective
            (by simpa using Set.mem_singleton_iff.1 hxSub)
      · intro xSeq x hxSeq hxTend hxFrontier
        have hBlowupAbs :
            Filter.Tendsto (fun i : ℕ => ‖gradAbs (xSeq i)‖) Filter.atTop Filter.atTop :=
          hgradAbsBlowup xSeq x hxSeq hxTend hxFrontier
        have hEventuallyEq :
            (fun i : ℕ => ‖quadraticOverLinearMinusSqrtGradientInverse (xSeq i)‖) =ᶠ[Filter.atTop]
              (fun i : ℕ => ‖gradAbs (xSeq i)‖) := by
          filter_upwards [Filter.Eventually.of_forall
            (fun i : ℕ => hGradAbsEqExplicit (xSeq i) (hxSeq i))] with i hi
          simpa [hi]
        exact Filter.Tendsto.congr' hEventuallyEq.symm hBlowupAbs
  · let LExplicit :
        InvolutiveLegendreTransformationOn (euclideanPairing (n := 2))
          openPositiveQuadrantR2 quadraticOverLinearMinusSqrtFunction :=
      { target := quadraticOverLinearMinusSqrtDualDomain
        conjFun := L.conjFun
        toFun := quadraticOverLinearMinusSqrtGradientMap
        image_eq := hImage.symm
        fiber_well_defined := by
          intro x₁ x₂ xStar hx₁ hx₂ hx₁eq hx₂eq
          have hx₁Interior :
              x₁ ∈
                interior
                  (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
                    quadraticOverLinearMinusSqrtFunction) := by
            simpa [hinterior] using hx₁
          have hx₂Interior :
              x₂ ∈
                interior
                  (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
                    quadraticOverLinearMinusSqrtFunction) := by
            simpa [hinterior] using hx₂
          have hx₁L :
              L.toFun x₁ = quadraticOverLinearMinusSqrtGradientMap x₁ := by
            rw [hLfun]
            exact hGradEq x₁ hx₁
          have hx₂L :
              L.toFun x₂ = quadraticOverLinearMinusSqrtGradientMap x₂ := by
            rw [hLfun]
            exact hGradEq x₂ hx₂
          have hx₁Final : L.toFun x₁ = xStar := by
            calc
              L.toFun x₁ = quadraticOverLinearMinusSqrtGradientMap x₁ := hx₁L
              _ = xStar := hx₁eq
          have hx₂Final : L.toFun x₂ = xStar := by
            calc
              L.toFun x₂ = quadraticOverLinearMinusSqrtGradientMap x₂ := hx₂L
              _ = xStar := hx₂eq
          simpa [euclideanPairing, dotProduct, Fin.sum_univ_two] using
            L.fiber_well_defined hx₁Interior hx₂Interior hx₁Final hx₂Final
        value_eq := by
          intro x hx
          have hxInterior :
              x ∈
                interior
                  (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
                    quadraticOverLinearMinusSqrtFunction) := by
            simpa [hinterior] using hx
          have hxTo :
              L.toFun x = quadraticOverLinearMinusSqrtGradientMap x := by
            rw [hLfun]
            exact hGradEq x hx
          calc
            L.conjFun (quadraticOverLinearMinusSqrtGradientMap x) =
                L.conjFun (L.toFun x) := by rw [hxTo.symm]
            _ =
                (((euclideanPairing (n := 2) x (L.toFun x) : ℝ) : EReal) -
                  quadraticOverLinearMinusSqrtFunction x) := L.value_eq hxInterior
            _ =
                (((euclideanPairing (n := 2) x
                    (quadraticOverLinearMinusSqrtGradientMap x) : ℝ) : EReal) -
                  quadraticOverLinearMinusSqrtFunction x) := by
                  rw [hxTo]
        invFun := quadraticOverLinearMinusSqrtGradientInverse
        left_inv := by
          intro x hx
          have hxSub :
              dotProductEquiv ℝ (Fin 2) (quadraticOverLinearMinusSqrtGradientMap x) ∈
                subdifferentialAt quadraticOverLinearMinusSqrtFunction x :=
            helperForExample_26_5_0_1_explicitGradient_mem_subdifferential hx
          have hxEuclidean :
              IsEuclideanSubgradientAt quadraticOverLinearMinusSqrtFunction x
                (quadraticOverLinearMinusSqrtGradientMap x) := by
            simpa [IsEuclideanSubgradientAt] using hxSub
          have hxDualEuclidean :
              IsEuclideanSubgradientAt
                (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)
                (quadraticOverLinearMinusSqrtGradientMap x) x :=
            (euclidean_subgradient_fenchelConjugate_iff
              (f := quadraticOverLinearMinusSqrtFunction) hclosedConv hproperOn
              x (quadraticOverLinearMinusSqrtGradientMap x)).2 hxEuclidean
          have hxDualSub :
              dotProductEquiv ℝ (Fin 2) x ∈
                subdifferentialAt
                  (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)
                  (quadraticOverLinearMinusSqrtGradientMap x) := by
            simpa [IsEuclideanSubgradientAt] using hxDualEuclidean
          have hxDualDomain :
              quadraticOverLinearMinusSqrtGradientMap x ∈
                quadraticOverLinearMinusSqrtDualDomain :=
            helperForExample_26_5_0_1_gradient_mem_dualDomain hx
          have hxDualInterior :
              quadraticOverLinearMinusSqrtGradientMap x ∈
                interior
                  (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
                    (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)) := by
            simpa [hDualDomainInterior] using hxDualDomain
          have hxEq : x = gradStar (quadraticOverLinearMinusSqrtGradientMap x) :=
            hGradStarUnique hxDualInterior hxDualSub
          calc
            quadraticOverLinearMinusSqrtGradientInverse
                (quadraticOverLinearMinusSqrtGradientMap x) =
              gradStar (quadraticOverLinearMinusSqrtGradientMap x) := by
                symm
                exact hGradStarEq _ hxDualDomain
            _ = x := by simpa using hxEq.symm
        inv_mem := by
          intro xStar hxStar
          exact
            (helperForExample_26_5_0_1_explicitInverse_mem_and_rightInv
              (xStar := xStar) hxStar).1
        right_inv := by
          intro xStar hxStar
          exact
            (helperForExample_26_5_0_1_explicitInverse_mem_and_rightInv
              (xStar := xStar) hxStar).2 }
    refine ⟨LExplicit, ?_⟩
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rfl
    · intro xStar hxStar
      have hxStarInterior :
          xStar ∈
            interior
              (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
                (fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction)) := by
        simpa [hDualDomainInterior] using hxStar
      calc
        L.conjFun xStar = fenchelConjugate 2 quadraticOverLinearMinusSqrtFunction xStar :=
          hLconj hxStarInterior
        _ = quadraticOverLinearMinusSqrtDualConjugateFunction xStar := hEqOnFenchelDual hxStar

end Section26
end Chap05
