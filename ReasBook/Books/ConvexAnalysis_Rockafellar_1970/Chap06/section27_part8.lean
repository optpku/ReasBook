/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part7

section Chap06
section Section27
/-- Helper for Theorem 6.27.6: decode a packed separating normal into affine coefficients on the
epigraph and auxiliary generators, while recording the forbidden-vector dot product as `-t`. -/
lemma helperForTheorem_6_27_6_decodePackedConeSeparator
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    {w : Fin (n + 2) → ℝ}
    (hHalfspace :
      (ConvexCone.hull ℝ
          (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C) :
            Set (Fin (n + 2) → ℝ)) ⊆
        {z : Fin (n + 2) → ℝ | dotProduct z w ≤ 0}) :
    ∃ a : ℝ, ∃ b : Fin n → ℝ, ∃ t : ℝ,
      (∀ p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h,
        a + p.1 ⬝ᵥ b + t * p.2 ≤ 0) ∧
      (∀ q ∈ constrainedMinimumAuxiliarySet h C,
        0 ≤ a + q.1 ⬝ᵥ b + t * q.2) ∧
      dotProduct (helperForTheorem_6_27_6_encodedNegativeVerticalPoint (n := n)) w = -t := by
  let q : (Fin (n + 1) → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n + 1)).symm w
  let p : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm q.1
  have hdotPacked :
      ∀ (lam : ℝ) (x : Fin n → ℝ) (μ : ℝ),
        dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
            w =
          x ⬝ᵥ p.1 + μ * p.2 + lam * q.2 := by
    intro lam x μ
    -- Unpack the two appended coordinates one layer at a time.
    calc
      dotProduct
          (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
          w
          =
        dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
            (prodLinearEquiv_append_coord (n := n + 1) q) := by
              simp [q]
      _ =
        dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ)) q.1 + lam * q.2 := by
          simpa [q] using
            helperForText_19_0_9_dotProduct_prodLinearEquivAppendCoord
              (n := n + 1)
              (p := (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
              (q := q)
      _ = x ⬝ᵥ p.1 + μ * p.2 + lam * q.2 := by
          have hInner :
              dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ)) q.1 =
                x ⬝ᵥ p.1 + μ * p.2 := by
            calc
              dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ)) q.1
                  =
                dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ))
                  (prodLinearEquiv_append_coord (n := n) p) := by
                    simp [p]
              _ = x ⬝ᵥ p.1 + μ * p.2 := by
                  simpa [p] using
                    helperForText_19_0_9_dotProduct_prodLinearEquivAppendCoord
                      (n := n) (p := (x, μ)) (q := p)
          rw [hInner]
  refine ⟨q.2, p.1, p.2, ?_, ?_, ?_⟩
  · intro r hr
    -- Upper generators already lie in the raw cone hull, so the half-space inequality applies.
    have hy :
        prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (r.1, r.2), (1 : ℝ)) ∈
          helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C :=
      helperForTheorem_6_27_6_mem_encodedSeparatorGeneratorSet_upper
        (h := h) (C := C) hr
    have hyHull :
        prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (r.1, r.2), (1 : ℝ)) ∈
          (ConvexCone.hull ℝ
            (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C) :
              Set (Fin (n + 2) → ℝ)) := by
      exact ConvexCone.subset_hull (R := ℝ) (s := _) hy
    have hyLe :
        dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (r.1, r.2), (1 : ℝ)))
            w ≤ 0 :=
      hHalfspace hyHull
    -- Evaluate the packed dot product on the upper branch.
    rw [hdotPacked (1 : ℝ) r.1 r.2, one_mul] at hyLe
    change q.2 + r.1 ⬝ᵥ p.1 + p.2 * r.2 ≤ 0
    linarith [hyLe]
  · intro r hr
    -- Lower generators contribute the negated affine expression.
    have hy :
        prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-r.1, -r.2), (-1 : ℝ)) ∈
          helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C :=
      helperForTheorem_6_27_6_mem_encodedSeparatorGeneratorSet_lower
        (h := h) (C := C) hr
    have hyHull :
        prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-r.1, -r.2), (-1 : ℝ)) ∈
          (ConvexCone.hull ℝ
            (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C) :
              Set (Fin (n + 2) → ℝ)) := by
      exact ConvexCone.subset_hull (R := ℝ) (s := _) hy
    have hyLe :
        dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (-r.1, -r.2), (-1 : ℝ)))
            w ≤ 0 :=
      hHalfspace hyHull
    -- The lower packed generator flips all affine coefficients at once.
    rw [hdotPacked (-1 : ℝ) (-r.1) (-r.2)] at hyLe
    rw [neg_dotProduct, neg_one_mul, mul_comm (-r.2) p.2] at hyLe
    linarith
  · -- The forbidden packed vector is exactly the pure negative vertical direction.
    rw [helperForTheorem_6_27_6_encodedNegativeVerticalPoint]
    rw [hdotPacked (0 : ℝ) (0 : Fin n → ℝ) (-1 : ℝ)]
    simp

/-- Helper for Theorem 6.27.6: once a packed separator with strictly negative vertical
coefficient is available, its inequalities already imply the desired linear lower bound on the
zero-balance slice gap. -/
lemma helperForTheorem_6_27_6_support_from_packedStrictSeparator
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (α : ℝ) {a : ℝ} {b : Fin n → ℝ} {t : ℝ} (htneg : t < 0)
    (hUpper : ∀ p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h,
      a + p.1 ⬝ᵥ b + t * p.2 ≤ 0)
    (hLower : ∀ q ∈ constrainedMinimumAuxiliarySet h C,
      0 ≤ a + q.1 ⬝ᵥ b + t * q.2) :
    ∃ xStar : Fin n → ℝ,
      ∀ z : Fin n → ℝ,
        ((z ⬝ᵥ xStar : ℝ) : EReal) ≤ helperForTheorem_6_27_6_zeroBalanceSliceGap α h C z := by
  let xStar : Fin n → ℝ := ((-t)⁻¹) • b
  refine ⟨xStar, ?_⟩
  intro z
  -- Compare every admissible epigraph/auxiliary pair against the strict packed separator.
  rw [helperForTheorem_6_27_6_zeroBalanceSliceGap]
  refine le_iInf ?_
  intro p
  refine le_iInf ?_
  intro q
  by_cases hzPair : p.1.1 - q.1.1 = z
  · have hgap :
        (p.1.1 - q.1.1) ⬝ᵥ b ≤ (-t) * (p.1.2 - q.1.2) := by
      have hpLe : a + p.1.1 ⬝ᵥ b + t * p.1.2 ≤ 0 := hUpper p.1 p.2
      have hqGe : 0 ≤ a + q.1.1 ⬝ᵥ b + t * q.1.2 := hLower q.1 q.2
      have hdiff :
          p.1.1 ⬝ᵥ b - q.1.1 ⬝ᵥ b ≤ (-t) * (p.1.2 - q.1.2) := by
        linarith
      simpa [sub_dotProduct] using hdiff
    have htpos : 0 < -t := by linarith
    have hreal :
        z ⬝ᵥ xStar ≤ p.1.2 - q.1.2 := by
      have hdiv :
          ((p.1.1 - q.1.1) ⬝ᵥ b) / (-t) ≤ p.1.2 - q.1.2 := by
        have : ((p.1.1 - q.1.1) ⬝ᵥ b) ≤ (p.1.2 - q.1.2) * (-t) := by
          simpa [mul_comm] using hgap
        exact (_root_.div_le_iff₀ htpos).2 this
      calc
        z ⬝ᵥ xStar = ((p.1.1 - q.1.1) ⬝ᵥ b) / (-t) := by
          simp [xStar, hzPair, dotProduct_smul, smul_eq_mul, div_eq_mul_inv,
            mul_comm, mul_left_comm, mul_assoc]
        _ ≤ p.1.2 - q.1.2 := hdiv
    have hereal :
        ((z ⬝ᵥ xStar : ℝ) : EReal) ≤ (((p.1.2 - q.1.2 : ℝ) : EReal)) :=
      (EReal.coe_le_coe_iff).2 hreal
    simpa [hzPair] using hereal
  · simp [hzPair]

/-- Helper for Theorem 6.27.6: a subgradient of a perturbation function at the origin gives a
zero-intercept linear minorant once the function vanishes at the origin. -/
lemma helperForTheorem_6_27_6_support_from_zero_subgradient
    {n : ℕ} {Γ : (Fin n → ℝ) → EReal} {xStar : Fin n → ℝ}
    (hΓ0 : Γ (0 : Fin n → ℝ) = 0)
    (hSub : dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt Γ 0) :
    ∀ z : Fin n → ℝ, ((z ⬝ᵥ xStar : ℝ) : EReal) ≤ Γ z := by
  intro z
  -- Specialize the subgradient inequality at `0` and use `Γ 0 = 0` to remove the intercept.
  have hz :
      Γ 0 + ((((dotProductEquiv ℝ (Fin n) xStar) (z - 0) : ℝ) : EReal)) ≤ Γ z :=
    hSub z
  simpa [hΓ0, dotProductEquiv_apply_apply, dotProduct_comm] using hz

/-- Helper for Theorem 6.27.6: an `ε`-subgradient at the origin gives an affine minorant whose
intercept is exactly `-ε`. -/
lemma helperForTheorem_6_27_6_support_from_zero_approximateSubgradient
    {n : ℕ} {Γ : (Fin n → ℝ) → EReal} {xStar : Fin n → ℝ} {ε : NNReal}
    (hΓconv : ConvexFunction Γ)
    (hΓ0 : Γ (0 : Fin n → ℝ) = 0)
    (hApprox : dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt Γ 0 ε) :
    ∀ z : Fin n → ℝ, (((z ⬝ᵥ xStar - ε : ℝ) : EReal) ≤ Γ z) := by
  have hΓ0finite : Γ (0 : Fin n → ℝ) ≠ (⊤ : EReal) ∧ Γ (0 : Fin n → ℝ) ≠ (⊥ : EReal) := by
    constructor <;> simpa [hΓ0]
  -- Rewrite the approximate-subgradient membership as the translated affine-minorant inequality.
  have hMinorant :
      ∀ y : Fin n → ℝ,
        (((dotProduct y xStar - ε : ℝ) : EReal) ≤ translatedDifferenceFunctionAt Γ 0 y) := by
    exact
      (helperForProposition_23_6_1_mem_approximateSubdifferential_iff_affine_minorant
        (f := Γ) hΓconv 0 hΓ0finite ε xStar).1 hApprox
  intro z
  -- At the origin, the translated-difference function is just `Γ` itself.
  simpa [translatedDifferenceFunctionAt, hΓ0, dotProduct_comm] using hMinorant z

/-- Helper for Theorem 6.27.6: if one vector belongs to every positive approximate
subdifferential of `Γ` at the origin, then it is an actual subgradient there and therefore gives
the desired supporting linear minorant. -/
lemma helperForTheorem_6_27_6_support_from_uniformApproximateSubgradientFamily
    {n : ℕ} {Γ : (Fin n → ℝ) → EReal} {xStar : Fin n → ℝ}
    (hΓconv : ConvexFunction Γ)
    (hΓ0 : Γ (0 : Fin n → ℝ) = 0)
    (hApprox :
      ∀ ε : {ε : NNReal // 0 < ε},
        dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt Γ 0 ε.1) :
    ∀ z : Fin n → ℝ, ((z ⬝ᵥ xStar : ℝ) : EReal) ≤ Γ z := by
  have hΓ0finite : Γ (0 : Fin n → ℝ) ≠ (⊤ : EReal) ∧ Γ (0 : Fin n → ℝ) ≠ (⊥ : EReal) := by
    constructor <;> simpa [hΓ0]
  have hApproxTheory :=
    approximateSubdifferential_iff_translatedDifferenceConjugate_le_and_basic_properties
      Γ hΓconv 0 hΓ0finite
  have hMemInter :
      dotProductEquiv ℝ (Fin n) xStar ∈
        ⋂ ε : {ε : NNReal // 0 < ε}, approximateSubdifferentialAt Γ 0 ε.1 := by
    -- Package the uniform approximate-subgradient hypothesis as membership in the canonical
    -- positive-`ε` intersection.
    exact Set.mem_iInter.2 hApprox
  have hSub :
      dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt Γ 0 := by
    -- Proposition 23.6.1 identifies that intersection with the exact subdifferential.
    rw [← hApproxTheory.2.2.2.2.2]
    exact hMemInter
  exact helperForTheorem_6_27_6_support_from_zero_subgradient hΓ0 hSub

/-- Helper for Theorem 6.27.6: once the zero-balance slice gap is known to be proper convex with
`0` in the relative interior of its effective domain, Theorem 23.4 supplies a subgradient at the
origin, and that subgradient is exactly the desired supporting linear minorant. -/
lemma helperForTheorem_6_27_6_support_from_relativeInteriorSubgradientCriterion
    {n : ℕ} {Γ : (Fin n → ℝ) → EReal}
    (hΓproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) Γ)
    (h0ri :
      (0 : Fin n → ℝ) ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) Γ))
    (hΓ0 : Γ (0 : Fin n → ℝ) = 0) :
    ∃ xStar : Fin n → ℝ,
      ∀ z : Fin n → ℝ, ((z ⬝ᵥ xStar : ℝ) : EReal) ≤ Γ z := by
  have hSubNonempty : Set.Nonempty (subdifferentialAt Γ 0) := by
    -- Theorem 23.4 turns the relative-interior hypothesis into subdifferentiability at `0`.
    exact
      ((subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        Γ hΓproper 0).2.1 h0ri).1
  rcases hSubNonempty with ⟨xStarDual, hSub⟩
  let xStar : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xStarDual
  refine ⟨xStar, ?_⟩
  -- Rewrite the dual witness in Euclidean coordinates and invoke the zero-subgradient helper.
  have hSubVec : dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt Γ 0 := by
    simpa [xStar] using hSub
  exact helperForTheorem_6_27_6_support_from_zero_subgradient hΓ0 hSubVec

/-- Helper for Theorem 6.27.6: the attained minimizing contact point `xBar` is a constrained
relative minimizer of `h` on `C`. -/
lemma helperForTheorem_6_27_6_relativeMinimizerOn_contactPoint
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    IsRelativeMinimizerOn h C xBar := by
  refine ⟨hxBarC, ?_⟩
  -- Rewrite the restricted infimum using the attained minimizing value `α`.
  calc
    h xBar = (α : EReal) := hxBar
    _ = ⨅ y : C, h y := by
          symm
          exact
            helperForTheorem_6_27_6_restrictedInf_eq_alpha
              (h := h) (C := C) α hxBarC hα_lower hxBar

/-- Helper for Theorem 6.27.6: the qualification hypothesis at the attained constrained minimum
produces a subgradient/normal-cone witness, and that witness supports the zero-balance slice gap
at the origin. -/
lemma helperForTheorem_6_27_6_boundarySupport_zeroBalanceSliceGap_at_origin
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) ∩
          euclideanRelativeInterior_fin n C))
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    ∃ xStar : Fin n → ℝ,
      ∀ z : Fin n → ℝ,
        ((z ⬝ᵥ xStar : ℝ) : EReal) ≤ helperForTheorem_6_27_6_zeroBalanceSliceGap α h C z := by
  -- Route correction: the old support helper incorrectly dropped the qualification hypothesis.
  -- The faithful route is to use Theorem 6.27.5 with `Or.inl hri` at the contact minimizer `xBar`.
  let _ := hclosed
  let _ := hCclosed
  have hmin : IsRelativeMinimizerOn h C xBar :=
    helperForTheorem_6_27_6_relativeMinimizerOn_contactPoint
      (h := h) (C := C) α hxBarC hα_lower hxBar
  have hqual : HasRelativeMinimizerSubgradientQualification h C := Or.inl hri
  have hiff :=
    (relativeMinimizerOn_iff_exists_subgradient_neg_mem_normalCone_under_qualification
      h C xBar hproper hCne hCconvex).2 hqual
  rcases hiff.mp hmin with ⟨xStarDual, hxSub, hxNormal⟩
  rcases (mem_normalConeAt_iff.1 hxNormal) with ⟨_hxBarC', hxNormalIneq⟩
  let xStar : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xStarDual
  refine ⟨xStar, ?_⟩
  intro z
  -- Compare the subgradient inequality at `p.1` with the normal-cone inequality at `q.1`.
  have hxStarDual_apply :
      ∀ y : Fin n → ℝ, xStarDual y = xStar ⬝ᵥ y := by
    intro y
    simpa [xStar] using (dotProductEquiv_apply_apply ℝ (Fin n) xStar y)
  rw [helperForTheorem_6_27_6_zeroBalanceSliceGap]
  refine le_iInf ?_
  intro p
  refine le_iInf ?_
  intro q
  by_cases hzPair : p.1.1 - q.1.1 = z
  · have hAuxEq :
        constrainedMinimumAuxiliarySet h C =
          {r : (Fin n → ℝ) × ℝ | r.1 ∈ C ∧ r.2 ≤ α} :=
      helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
        (h := h) (C := C) α hxBarC hα_lower hxBar
    have hqText : q.1 ∈ {r : (Fin n → ℝ) × ℝ | r.1 ∈ C ∧ r.2 ≤ α} := by
      simpa [hAuxEq] using q.2
    have hqC : q.1.1 ∈ C := hqText.1
    have hqLeAlpha : q.1.2 ≤ α := hqText.2
    have hpSub :
        (α : EReal) + ((((p.1.1 ⬝ᵥ xStar - xBar ⬝ᵥ xStar : ℝ) : ℝ) : EReal)) ≤ h p.1.1 := by
      -- Rewrite the dual-space subgradient at `xBar` in Euclidean coordinates.
      have hpSubDual :
          h xBar + ((((xStarDual (p.1.1 - xBar) : ℝ) : EReal))) ≤ h p.1.1 :=
        hxSub p.1.1
      have hpSubVec :
          h xBar + ((((p.1.1 - xBar) ⬝ᵥ xStar : ℝ) : EReal)) ≤ h p.1.1 := by
        simpa [hxStarDual_apply, dotProduct_comm] using hpSubDual
      rw [hxBar] at hpSubVec
      simpa [sub_dotProduct] using hpSubVec
    have hpEpi : h p.1.1 ≤ (p.1.2 : EReal) :=
      (mem_epigraph_univ_iff (f := h)).1 p.2
    have hpReal : α + (p.1.1 ⬝ᵥ xStar - xBar ⬝ᵥ xStar) ≤ p.1.2 := by
      exact_mod_cast le_trans hpSub hpEpi
    have hqNormalReal : xBar ⬝ᵥ xStar ≤ q.1.1 ⬝ᵥ xStar := by
      -- The auxiliary point lies in `C`, so the normal-cone inequality controls its translate.
      have hqNormalDual : (-xStarDual) (q.1.1 - xBar) ≤ 0 := hxNormalIneq q.1.1 hqC
      have hqNormalDualEval : -(xStarDual (q.1.1 - xBar)) ≤ 0 := by
        simpa using hqNormalDual
      have hqNormalDual' : 0 ≤ xStarDual (q.1.1 - xBar) := by
        have := hqNormalDualEval
        linarith
      have hqNormalVec : 0 ≤ (q.1.1 - xBar) ⬝ᵥ xStar := by
        simpa [hxStarDual_apply, dotProduct_comm] using hqNormalDual'
      have hqNormalVec' : 0 ≤ q.1.1 ⬝ᵥ xStar - xBar ⬝ᵥ xStar := by
        simpa [sub_dotProduct] using hqNormalVec
      linarith
    have hReal : z ⬝ᵥ xStar ≤ p.1.2 - q.1.2 := by
      have hzRewrite : z ⬝ᵥ xStar = p.1.1 ⬝ᵥ xStar - q.1.1 ⬝ᵥ xStar := by
        calc
          z ⬝ᵥ xStar = (p.1.1 - q.1.1) ⬝ᵥ xStar := by rw [← hzPair]
          _ = p.1.1 ⬝ᵥ xStar - q.1.1 ⬝ᵥ xStar := by
                simp [sub_dotProduct]
      rw [hzRewrite]
      linarith
    have hCast :
        ((z ⬝ᵥ xStar : ℝ) : EReal) ≤ (((p.1.2 - q.1.2 : ℝ) : EReal)) := by
      exact_mod_cast hReal
    simpa [hzPair] using hCast
  · simp [hzPair]

/-- Helper for Theorem 6.27.6: the perturbation function `Γ` admits a supporting linear
minorant at the origin. -/
lemma helperForTheorem_6_27_6_supportingLinearMinorant_zeroBalanceSliceGap_at_origin
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) ∩
          euclideanRelativeInterior_fin n C))
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    ∃ xStar : Fin n → ℝ,
      ∀ z : Fin n → ℝ,
        ((z ⬝ᵥ xStar : ℝ) : EReal) ≤ helperForTheorem_6_27_6_zeroBalanceSliceGap α h C z := by
  -- The repaired boundary-support helper already gives the desired origin-anchored minorant.
  exact
    helperForTheorem_6_27_6_boundarySupport_zeroBalanceSliceGap_at_origin
      (h := h) (C := C) hclosed hproper hCne hCclosed hCconvex hri α hxBarC hα_lower hxBar

/-- Helper for Theorem 6.27.6: a linear lower bound on the zero-balance slice gap decodes
directly into the textbook separating hyperplane. -/
lemma helperForTheorem_6_27_6_separator_from_zeroBalanceSliceGapSupport
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal))
    {xStar : Fin n → ℝ}
    (hSupport :
      ∀ z : Fin n → ℝ,
        ((z ⬝ᵥ xStar : ℝ) : EReal) ≤ helperForTheorem_6_27_6_zeroBalanceSliceGap α h C z) :
    ∃ β : ℝ,
      (∀ p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h,
        p.1 ⬝ᵥ xStar + β ≤ p.2) ∧
      ∀ q ∈ constrainedMinimumAuxiliarySet h C,
        q.2 ≤ q.1 ⬝ᵥ xStar + β := by
  let β : ℝ := α - xBar ⬝ᵥ xStar
  have hContactEpi :
      (xBar, α) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h :=
    helperForTheorem_6_27_6_contactPoint_mem_epigraph (h := h) α hxBar
  have hContactAux :
      (xBar, α) ∈ constrainedMinimumAuxiliarySet h C :=
    helperForTheorem_6_27_6_contactPoint_mem_auxiliarySet
      (h := h) (C := C) α hxBarC hα_lower hxBar
  refine ⟨β, ?_, ?_⟩
  · intro p hp
    -- Compare the support inequality with the contact auxiliary point `(xBar, α)`.
    have hGapLe :
        helperForTheorem_6_27_6_zeroBalanceSliceGap α h C (p.1 - xBar) ≤
          ((p.2 - α : ℝ) : EReal) := by
      simpa using
        helperForTheorem_6_27_6_zeroBalanceSliceGap_le_of_admissiblePair
          (α := α) (h := h) (C := C) (p := p) (q := (xBar, α))
          hp hContactAux (by simp)
    have hReal :
        (p.1 - xBar) ⬝ᵥ xStar ≤ p.2 - α := by
      exact_mod_cast le_trans (hSupport (p.1 - xBar)) hGapLe
    have hDiff :
        p.1 ⬝ᵥ xStar - xBar ⬝ᵥ xStar ≤ p.2 - α := by
      simpa [sub_dotProduct] using hReal
    dsimp [β]
    linarith
  · intro q hq
    -- Compare the same support inequality with the contact epigraph point `(xBar, α)`.
    have hGapLe :
        helperForTheorem_6_27_6_zeroBalanceSliceGap α h C (xBar - q.1) ≤
          ((α - q.2 : ℝ) : EReal) := by
      simpa using
        helperForTheorem_6_27_6_zeroBalanceSliceGap_le_of_admissiblePair
          (α := α) (h := h) (C := C) (p := (xBar, α)) (q := q)
          hContactEpi hq (by simp)
    have hReal :
        (xBar - q.1) ⬝ᵥ xStar ≤ α - q.2 := by
      exact_mod_cast le_trans (hSupport (xBar - q.1)) hGapLe
    have hDiff :
        xBar ⬝ᵥ xStar - q.1 ⬝ᵥ xStar ≤ α - q.2 := by
      simpa [sub_dotProduct] using hReal
    dsimp [β]
    linarith

/-- Helper for Theorem 6.27.6: once the perturbation function admits a supporting linear
minorant, the separator can be encoded in the packed affine-coefficient format with `t = -1`. -/
lemma helperForTheorem_6_27_6_existsPackedAffineSeparator
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) ∩
          euclideanRelativeInterior_fin n C))
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    ∃ a : ℝ, ∃ b : Fin n → ℝ, ∃ t : ℝ,
      t < 0 ∧
        (∀ p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h,
          a + p.1 ⬝ᵥ b + t * p.2 ≤ 0) ∧
        (∀ q ∈ constrainedMinimumAuxiliarySet h C,
          0 ≤ a + q.1 ⬝ᵥ b + t * q.2) := by
  -- Encode the supporting linear minorant of the perturbation function with the fixed choice `t = -1`.
  obtain ⟨xStar, hSupport⟩ :=
    helperForTheorem_6_27_6_supportingLinearMinorant_zeroBalanceSliceGap_at_origin
      (h := h) (C := C) hclosed hproper hCne hCclosed hCconvex hri α hxBarC hα_lower hxBar
  obtain ⟨β, hUpper, hLower⟩ :=
    helperForTheorem_6_27_6_separator_from_zeroBalanceSliceGapSupport
      (h := h) (C := C) α hxBarC hα_lower hxBar hSupport
  refine ⟨β, xStar, -1, by norm_num, ?_, ?_⟩
  · intro p hp
    -- Rewrite the non-vertical separator inequality into the packed affine form.
    have hpSep : p.1 ⬝ᵥ xStar + β ≤ p.2 := hUpper p hp
    linarith
  · intro q hq
    -- The auxiliary-side separator inequality gives the same packed form with `t = -1`.
    have hqSep : q.2 ≤ q.1 ⬝ᵥ xStar + β := hLower q hq
    linarith

/-- Helper for Theorem 6.27.6: a packed separator with negative vertical coefficient normalizes to
the non-vertical graph inequalities of the theorem. -/
lemma helperForTheorem_6_27_6_normalizePackedAffineSeparator
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    {a : ℝ} {b : Fin n → ℝ} {t : ℝ} (ht : t < 0)
    (hUpper : ∀ p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h,
      a + p.1 ⬝ᵥ b + t * p.2 ≤ 0)
    (hLower : ∀ q ∈ constrainedMinimumAuxiliarySet h C,
      0 ≤ a + q.1 ⬝ᵥ b + t * q.2) :
    ∃ xStar : Fin n → ℝ, ∃ β : ℝ,
      (∀ p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h,
        p.1 ⬝ᵥ xStar + β ≤ p.2) ∧
      ∀ q ∈ constrainedMinimumAuxiliarySet h C,
        q.2 ≤ q.1 ⬝ᵥ xStar + β := by
  refine ⟨(-1 / t : ℝ) • b, -(a / t), ?_⟩
  have hrepr :
      ∀ x : Fin n → ℝ,
        x ⬝ᵥ ((-1 / t : ℝ) • b) + -(a / t) = -(a + x ⬝ᵥ b) / t := by
    intro x
    simp [dotProduct_smul, smul_eq_mul, div_eq_mul_inv]
    ring
  refine ⟨?_, ?_⟩
  · intro p hp
    -- Divide the epigraph inequality by the negative vertical coefficient.
    have hSlice : a + p.1 ⬝ᵥ b + t * p.2 ≤ 0 := hUpper p hp
    have hNumerator : p.2 * t ≤ -(a + p.1 ⬝ᵥ b) := by
      have hSlice' : a + p.1 ⬝ᵥ b + p.2 * t ≤ 0 := by
        simpa [mul_comm, add_assoc, add_left_comm, add_comm] using hSlice
      linarith
    rw [hrepr p.1]
    exact (div_le_iff_of_neg ht).2 hNumerator
  · intro q hq
    -- Divide the auxiliary-set inequality by the same negative coefficient.
    have hSlice : 0 ≤ a + q.1 ⬝ᵥ b + t * q.2 := hLower q hq
    have hNumerator : -(a + q.1 ⬝ᵥ b) ≤ q.2 * t := by
      have hSlice' : 0 ≤ a + q.1 ⬝ᵥ b + q.2 * t := by
        simpa [mul_comm, add_assoc, add_left_comm, add_comm] using hSlice
      linarith
    rw [hrepr q.1]
    exact (le_div_iff_of_neg ht).2 (by simpa [mul_comm] using hNumerator)

/-- Theorem 6.27.6 (Weak separation by a non-vertical hyperplane): let `h : ℝ^n → ℝ ∪ {±∞}` be a
closed proper convex function, let `C` be a nonempty closed convex set, and let `α : ℝ` be a
finite minimum value of `h` on `C`, attained at some `xBar ∈ C`. Assume further that
`ri (dom h) ∩ ri C ≠ ∅`, modeled here by the Euclidean relative-interior intersection
`euclideanRelativeInterior_fin n (dom h) ∩ euclideanRelativeInterior_fin n C`. Then there exist
`xStar ∈ ℝ^n` and `β ∈ ℝ` such that the non-vertical hyperplane `μ = x ⬝ᵥ xStar + β` weakly
separates the epigraph of `h` from the auxiliary set `constrainedMinimumAuxiliarySet h C`, which
in the textbook notation is `{(x, μ) | x ∈ C, μ ≤ α}`, and moreover passes through the contact
point `(xBar, α)`. -/
theorem exists_nonverticalHyperplane_separating_epigraph_and_constrainedMinimumAuxiliarySet
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) ∩
          euclideanRelativeInterior_fin n C))
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    ∃ xStar : Fin n → ℝ, ∃ β : ℝ,
      (∀ p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h,
        p.1 ⬝ᵥ xStar + β ≤ p.2) ∧
      (∀ p ∈ constrainedMinimumAuxiliarySet h C,
        p.2 ≤ p.1 ⬝ᵥ xStar + β) ∧
      α = xBar ⬝ᵥ xStar + β := by
  -- Route correction: use the qualification hypothesis `hri` to obtain the supporting minorant
  -- for `Γ = helperForTheorem_6_27_6_zeroBalanceSliceGap α h C`, then decode it into a separator.
  obtain ⟨a, b, t, ht, hUpper, hLower⟩ :=
    helperForTheorem_6_27_6_existsPackedAffineSeparator
      (h := h) (C := C) hclosed hproper hCne hCclosed hCconvex hri α hxBarC hα_lower hxBar
  -- Normalize the packed half-space coefficients into the graph form `μ = x ⬝ᵥ xStar + β`.
  rcases
    helperForTheorem_6_27_6_normalizePackedAffineSeparator
      (h := h) (C := C) ht hUpper hLower with
    ⟨xStar, β, hsep_epi, hsep_aux⟩
  refine ⟨xStar, β, hsep_epi, hsep_aux, ?_⟩
  have hContactEpi :
      (xBar, α) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h :=
    helperForTheorem_6_27_6_contactPoint_mem_epigraph (h := h) α hxBar
  have hContactAux :
      (xBar, α) ∈ constrainedMinimumAuxiliarySet h C :=
    helperForTheorem_6_27_6_contactPoint_mem_auxiliarySet
      (h := h) (C := C) α hxBarC hα_lower hxBar
  have hEqLe : xBar ⬝ᵥ xStar + β ≤ α := hsep_epi (xBar, α) hContactEpi
  have hEqGe : α ≤ xBar ⬝ᵥ xStar + β := hsep_aux (xBar, α) hContactAux
  exact le_antisymm hEqGe hEqLe

-- Proof sketch: evaluate the separating inequalities at the contact point `(xBar, α)` to force
-- equality `α = xBar ⬝ᵥ xStar + β`. Then rewrite the epigraph inequality as the subgradient
-- inequality for `h` at `xBar`, and rewrite the auxiliary-set inequality on points `(x, α)` with
-- `x ∈ C` as the normal-cone inequality for `-xStar` at `xBar`.
/-- Helper for Corollary 6.27.6: evaluating the two separator inequalities at the common contact
point `(xBar, α)` forces the separator to pass through that point. -/
lemma helperForCorollary_6_27_6_contactPoint_liesOn_separator
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal))
    (xStar : Fin n → ℝ) (β : ℝ)
    (hsep_epi : ∀ p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h,
      p.1 ⬝ᵥ xStar + β ≤ p.2)
    (hsep_aux : ∀ p ∈ constrainedMinimumAuxiliarySet h C,
      p.2 ≤ p.1 ⬝ᵥ xStar + β) :
    α = xBar ⬝ᵥ xStar + β := by
  -- The epigraph separator gives the upper bound at the contact point.
  have hContactEpi :
      (xBar, α) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h :=
    helperForTheorem_6_27_6_contactPoint_mem_epigraph (h := h) α hxBar
  -- The auxiliary-set separator gives the matching lower bound at the same point.
  have hContactAux :
      (xBar, α) ∈ constrainedMinimumAuxiliarySet h C :=
    helperForTheorem_6_27_6_contactPoint_mem_auxiliarySet
      (h := h) (C := C) α hxBarC hα_lower hxBar
  have hEqLe : xBar ⬝ᵥ xStar + β ≤ α := hsep_epi (xBar, α) hContactEpi
  have hEqGe : α ≤ xBar ⬝ᵥ xStar + β := hsep_aux (xBar, α) hContactAux
  exact le_antisymm hEqGe hEqLe

/-- Helper for Corollary 6.27.6: a finite value of `h` can be rewritten with `toReal`, and the
corresponding point lies on the epigraph with the same ordinate. -/
lemma helperForCorollary_6_27_6_finiteValue_toReal_mem_epigraph
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (z : Fin n → ℝ)
    (hzTop : h z ≠ (⊤ : EReal)) (hzBot : h z ≠ (⊥ : EReal)) :
    (z, (h z).toReal) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h ∧
      h z = (((h z).toReal : ℝ) : EReal) := by
  -- Recover the finite extended-real value from `toReal` before packaging the epigraph point.
  have hzEq : h z = (((h z).toReal : ℝ) : EReal) := by
    simpa using (EReal.coe_toReal (x := h z) hzTop hzBot).symm
  constructor
  · -- The epigraph condition is exactly the inequality obtained from the recovered value.
    exact
      (mem_epigraph_univ_iff (f := h) (x := z) (μ := (h z).toReal)).2
        (EReal.le_coe_toReal hzTop)
  · exact hzEq

/-- Helper for Corollary 6.27.6: the epigraph-side separator inequality rewrites into the
subgradient inequality for `h` at `xBar`. -/
lemma helperForCorollary_6_27_6_subgradient_from_epigraph_separator
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (α : ℝ) {xBar : Fin n → ℝ} (hxBar : h xBar = (α : EReal))
    (xStar : Fin n → ℝ) (β : ℝ)
    (hEq : α = xBar ⬝ᵥ xStar + β)
    (hsep_epi : ∀ p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h,
      p.1 ⬝ᵥ xStar + β ≤ p.2) :
    xStar ∈ euclideanSubdifferentialAt h xBar := by
  -- Change to the dual-space formulation so the separator inequality can be read directly.
  change dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt h xBar
  rw [subdifferentialAt]
  intro z
  by_cases hzTop : h z = (⊤ : EReal)
  · -- If `h z = ⊤`, the defining subgradient inequality is immediate.
    simp [hzTop]
  · have hzBot : h z ≠ (⊥ : EReal) := hproper.2.2 z (by simp)
    -- Package the finite `EReal` value as an actual epigraph point with real ordinate.
    rcases
      helperForCorollary_6_27_6_finiteValue_toReal_mem_epigraph
        (h := h) z hzTop hzBot with
      ⟨hzEpi, hzEq⟩
    let μ : ℝ := (h z).toReal
    have hzSep : z ⬝ᵥ xStar + β ≤ μ := hsep_epi (z, μ) hzEpi
    -- Substituting the contact equality turns the separator inequality into the subgradient bound.
    have hReal :
        α + (z - xBar) ⬝ᵥ xStar ≤ μ := by
      calc
        α + (z - xBar) ⬝ᵥ xStar
            = α + (z ⬝ᵥ xStar - xBar ⬝ᵥ xStar) := by
                simp [sub_dotProduct]
        _ = z ⬝ᵥ xStar + β := by
              linarith [hEq]
        _ ≤ μ := hzSep
    have hReal' :
        α + xStar ⬝ᵥ (z - xBar) ≤ μ := by
      simpa [dotProduct_comm] using hReal
    have hCast :
        (((α + xStar ⬝ᵥ (z - xBar) : ℝ) : ℝ) : EReal) ≤ (μ : EReal) := by
      exact_mod_cast hReal'
    have hEReal :
        h xBar + (((dotProductEquiv ℝ (Fin n) xStar) (z - xBar) : ℝ) : EReal) ≤ h z := by
      rw [hxBar, hzEq]
      simpa [dotProductEquiv_apply_apply] using hCast
    simpa [dotProductEquiv_apply_apply] using hEReal

/-- Helper for Corollary 6.27.6: restricting the auxiliary-set separator inequality to the slice
`μ = α` yields the normal-cone inequality for `-xStar` at `xBar`. -/
lemma helperForCorollary_6_27_6_neg_normal_from_auxiliary_separator
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal))
    (xStar : Fin n → ℝ) (β : ℝ)
    (hEq : α = xBar ⬝ᵥ xStar + β)
    (hsep_aux : ∀ p ∈ constrainedMinimumAuxiliarySet h C,
      p.2 ≤ p.1 ⬝ᵥ xStar + β) :
    -xStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt C xBar) := by
  -- First prove the corresponding statement in the dual space `normalConeAt C xBar`.
  have hNormal : dotProductEquiv ℝ (Fin n) (-xStar) ∈ normalConeAt C xBar := by
    refine (mem_normalConeAt_iff).2 ?_
    constructor
    · exact hxBarC
    · intro z hzC
      have hAuxEq :
          constrainedMinimumAuxiliarySet h C =
            {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ p.2 ≤ α} :=
        helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
          (h := h) (C := C) α hxBarC hα_lower hxBar
      have hzPair : z ∈ C ∧ α ≤ α := ⟨hzC, le_rfl⟩
      have hzAux : (z, α) ∈ constrainedMinimumAuxiliarySet h C := by
        simpa [hAuxEq] using hzPair
      have hzSep : α ≤ z ⬝ᵥ xStar + β := hsep_aux (z, α) hzAux
      -- Substituting the contact equality isolates the normal-cone sign condition.
      have hzNonneg : 0 ≤ (z - xBar) ⬝ᵥ xStar := by
        calc
          0 = α - (xBar ⬝ᵥ xStar + β) := by simp [hEq]
          _ ≤ z ⬝ᵥ xStar - (xBar ⬝ᵥ xStar) := by linarith [hzSep]
          _ = (z - xBar) ⬝ᵥ xStar := by simp [sub_dotProduct]
      have hzNonneg' : 0 ≤ xStar ⬝ᵥ (z - xBar) := by
        simpa [dotProduct_comm] using hzNonneg
      simpa [dotProductEquiv_apply_apply] using neg_nonpos.mpr hzNonneg'
  -- Convert the dual-space statement back through `dotProductEquiv`.
  simpa [Set.mem_preimage, map_neg, dotProductEquiv_apply_apply] using hNormal

/-- Corollary 6.27.6 (The separating hyperplane yields a subgradient and a normal vector): under
the assumptions of Theorem 6.27.6, let `xBar ∈ C` satisfy `h xBar = α = inf_{x ∈ C} h x`, and let
`xStar ∈ ℝ^n` and `β ∈ ℝ` be given by the separating hyperplane theorem above. Then
`α = xBar ⬝ᵥ xStar + β`, the vector `xStar` belongs to the Euclidean subdifferential of `h` at
`xBar`, and `-xStar` belongs to the Euclidean normal cone of `C` at `xBar`. -/
theorem separatingHyperplane_yields_subgradient_and_normalVector
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal))
    (xStar : Fin n → ℝ) (β : ℝ)
    (hsep_epi : ∀ p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h,
      p.1 ⬝ᵥ xStar + β ≤ p.2)
    (hsep_aux : ∀ p ∈ constrainedMinimumAuxiliarySet h C,
      p.2 ≤ p.1 ⬝ᵥ xStar + β) :
    α = xBar ⬝ᵥ xStar + β ∧
      xStar ∈ euclideanSubdifferentialAt h xBar ∧
      -xStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt C xBar) := by
  -- First recover the contact equality from the two separator inequalities.
  have hEq : α = xBar ⬝ᵥ xStar + β :=
    helperForCorollary_6_27_6_contactPoint_liesOn_separator
      (h := h) (C := C) α hxBarC hα_lower hxBar xStar β hsep_epi hsep_aux
  -- Then read each separator inequality in the geometric language of the corollary.
  refine ⟨hEq, ?_, ?_⟩
  · exact
      helperForCorollary_6_27_6_subgradient_from_epigraph_separator
        (h := h) hproper α hxBar xStar β hEq hsep_epi
  · exact
      helperForCorollary_6_27_6_neg_normal_from_auxiliary_separator
        (h := h) (C := C) α hxBarC hα_lower hxBar xStar β hEq hsep_aux

/-- An `EReal`-valued function is bounded below on `C` when it admits a real lower bound at every
point of `C`. -/
def HasRealLowerBoundOn {n : ℕ} (f : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℝ, ∀ x ∈ C, (m : EReal) ≤ f x

/-- A function is affine along the recession ray generated by `y` when translating any point of
its effective domain by a nonnegative multiple of `y` changes the value by a fixed real slope
times the step size. -/
def IsAffineAlongRayDirection {n : ℕ} (f : (Fin n → ℝ) → EReal) (y : Fin n → ℝ) : Prop :=
  ∃ a : ℝ, ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f, ∀ t : ℝ, 0 ≤ t →
    f (x + t • y) = f x + ((t * a : ℝ) : EReal)

/-- Every recession direction of `f` is a direction along which `f` is affine on rays. -/
def EveryRecessionDirectionIsAffineAlongRay {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ∀ y : Fin n → ℝ, IsRecessionDirection f y → IsAffineAlongRayDirection f y

/-- Helper for Corollary 6.27.3: if a finite extended-real value satisfies
`r + a ≤ r`, then the added real slope is nonpositive. -/
lemma helperForCorollary_6_27_3_nonpositive_of_addReal_le
    {r : EReal} {a : ℝ} (hrTop : r ≠ (⊤ : EReal)) (hrBot : r ≠ (⊥ : EReal))
    (hle : r + (a : EReal) ≤ r) :
    a ≤ 0 := by
  -- Rewrite the finite extended-real value as a real number and compare inside `ℝ`.
  lift r to ℝ using ⟨hrTop, hrBot⟩ with rReal hr
  have hreal :
      (((rReal + a : ℝ) : EReal)) ≤ ((rReal : ℝ) : EReal) := by
    simpa [hr, add_comm, add_left_comm, add_assoc] using hle
  exact by
    have : rReal + a ≤ rReal := EReal.coe_le_coe_iff.mp hreal
    linarith

/-- Helper for Corollary 6.27.3: a uniform real lower bound along an affine ray forces the ray
slope to be nonnegative. -/
lemma helperForCorollary_6_27_3_nonnegative_of_uniform_rayLowerBound
    {r m a : ℝ} (hbound : ∀ t : ℝ, 0 ≤ t → m ≤ r + t * a) :
    0 ≤ a := by
  -- A negative slope would eventually push the affine ray below the fixed lower bound.
  by_contra haNeg
  have hden : 0 < -a := by linarith
  obtain ⟨k, hkNat⟩ : ∃ k : ℕ, (r - m) / (-a) < k := by
    exact exists_nat_gt ((r - m) / (-a))
  have hk : (r - m) / (-a) < (k : ℝ) := by
    exact_mod_cast hkNat
  have hkMul : r - m < (k : ℝ) * (-a) := by
    exact (div_lt_iff₀ hden).mp hk
  have hboundk : m ≤ r + (k : ℝ) * a := by
    exact hbound k (by exact_mod_cast (Nat.zero_le k))
  have hkUpper : r + (k : ℝ) * a < m := by
    nlinarith
  exact (not_le_of_gt hkUpper) hboundk

/-- Helper for Corollary 6.27.3: the indicator extension `x ↦ h x + δ_C(x)` is closed and proper
once `C` is polyhedral and there is a feasible point where `h` is finite. -/
lemma helperForCorollary_6_27_3_indicatorExtension_closedProper
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCne : Set.Nonempty C) (hCpoly : IsPolyhedralConvexSet n C)
    {x0 : Fin n → ℝ} (hx0C : x0 ∈ C) (hx0Top : h x0 < (⊤ : EReal)) :
    let g : (Fin n → ℝ) → EReal := fun x => h x + indicatorFunction C x
    ClosedConvexFunction g ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
  let g : (Fin n → ℝ) → EReal := fun x => h x + indicatorFunction C x
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal :=
    fun i => Fin.cases h (fun _ => indicatorFunction C) i
  have hCclosed : IsClosed C :=
    helperForTheorem_19_1_polyhedral_isClosed (n := n) (C := C) hCpoly
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hNegCne : Set.Nonempty (-C) := by
    rcases hCne with ⟨x, hxC⟩
    refine ⟨-x, ?_⟩
    simpa using hxC
  have hNegCclosed : IsClosed (-C) := by
    have hcont : Continuous fun x : Fin n → ℝ => -x := by
      continuity
    have hpre : IsClosed ((fun x : Fin n → ℝ => -x) ⁻¹' C) := hCclosed.preimage hcont
    simpa [Set.preimage, Set.neg] using hpre
  have hNegCconv : Convex ℝ (-C) := by
    simpa using hCconv.neg
  have hIndicatorNeg :
      ClosedConvexFunction (indicatorFunction (-(-C))) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (indicatorFunction (-(-C))) := by
    simpa using
      (closedConvexFunction_indicator_neg (C := -C) hNegCne hNegCclosed hNegCconv)
  have hIndicatorClosed : ClosedConvexFunction (indicatorFunction C) := by
    simpa using hIndicatorNeg.1
  have hIndicatorProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction C) := by
    simpa using hIndicatorNeg.2
  have hclosedTwo : ∀ i : Fin 2, ClosedConvexFunction (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hclosed
    · simpa [fTwo] using hIndicatorClosed
  have hproperTwo : ∀ i : Fin 2,
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hproper
    · simpa [fTwo] using hIndicatorProper
  have hgClosed : ClosedConvexFunction g := by
    -- The indicator extension is the two-term sum of the original function and `δ_C`.
    simpa [g, fTwo, Fin.sum_univ_two] using
      (closedConvexFunction_sum_of_closed (f := fTwo) hclosedTwo hproperTwo)
  have hx0gTop : g x0 < (⊤ : EReal) := by
    -- At the finite feasible point, the indicator term vanishes.
    simpa [g, indicatorFunction, hx0C] using hx0Top
  have hsumTop :
      (∑ i : Fin 2, fTwo i x0) < (⊤ : EReal) := by
    simpa [g, fTwo, Fin.sum_univ_two] using hx0gTop
  have hgProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    -- Properness of the sum follows from properness of each summand and one finite common point.
    simpa [g, fTwo, Fin.sum_univ_two] using
      (properConvexFunctionOn_sum_of_exists_ne_top
        (f := fTwo) hproperTwo ⟨x0, (lt_top_iff_ne_top.mp hsumTop)⟩)
  exact ⟨hgClosed, hgProper⟩

/-- Helper for Corollary 6.27.3: along a genuine recession direction of `h`, the affine ray slope
forced by `haffine` cannot be positive. -/
lemma helperForCorollary_6_27_3_affineSlope_nonpositive_of_recessionDirection
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    {y x0 : Fin n → ℝ} (hyRec : IsRecessionDirection h y)
    (hx0Top : h x0 < (⊤ : EReal))
    {a : ℝ}
    (ha :
      ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h, ∀ t : ℝ, 0 ≤ t →
        h (x + t • y) = h x + ((t * a : ℝ) : EReal)) :
    a ≤ 0 := by
  have hx0Dom : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [effectiveDomain_eq] using hx0Top
  have hx0Top' : h x0 ≠ (⊤ : EReal) := lt_top_iff_ne_top.mp hx0Top
  have hx0Bot : h x0 ≠ (⊥ : EReal) := hproper.2.2 x0 (by simp)
  have hdiff :
      h (x0 + 1 • y) - h x0 ≤ recessionFunction h y := by
    simpa [one_smul] using (le_sSup ⟨x0, hx0Dom, rfl⟩ :
      h (x0 + y) - h x0 ≤ recessionFunction h y)
  have hshiftLe :
      h (x0 + 1 • y) ≤ recessionFunction h y + h x0 := by
    exact
      (EReal.sub_le_iff_le_add
        (a := h (x0 + 1 • y)) (b := h x0) (c := recessionFunction h y)
        (Or.inl hx0Bot) (Or.inl hx0Top')).1 hdiff
  have haddLe :
      h x0 + ((a : ℝ) : EReal) ≤ h x0 := by
    calc
      h x0 + ((a : ℝ) : EReal) = h (x0 + 1 • y) := by
        symm
        simpa [one_smul] using ha x0 hx0Dom 1 (by norm_num)
      _ ≤ recessionFunction h y + h x0 := hshiftLe
      _ ≤ (0 : EReal) + h x0 := by
        simpa [add_comm] using add_le_add_right hyRec (h x0)
      _ = h x0 := by simp
  exact
    helperForCorollary_6_27_3_nonpositive_of_addReal_le
      hx0Top' hx0Bot haddLe

/-- Helper for Corollary 6.27.3: if a recession ray of the feasible set stays inside `C`, then
the lower bound of `h` on `C` prevents the affine ray slope from being negative. -/
lemma helperForCorollary_6_27_3_affineSlope_nonnegative_on_feasible_ray
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (C : Set (Fin n → ℝ)) {y x0 : Fin n → ℝ}
    (hyC : y ∈ Set.recessionCone C) (hx0C : x0 ∈ C) (hx0Top : h x0 < (⊤ : EReal))
    {a : ℝ}
    (ha :
      ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h, ∀ t : ℝ, 0 ≤ t →
        h (x + t • y) = h x + ((t * a : ℝ) : EReal))
    (hbounded : HasRealLowerBoundOn h C) :
    0 ≤ a := by
  rcases hbounded with ⟨m, hm⟩
  have hx0Dom : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [effectiveDomain_eq] using hx0Top
  have hx0Top' : h x0 ≠ (⊤ : EReal) := lt_top_iff_ne_top.mp hx0Top
  have hx0Bot : h x0 ≠ (⊥ : EReal) := hproper.2.2 x0 (by simp)
  lift h x0 to ℝ using ⟨hx0Top', hx0Bot⟩ with r hr
  have hboundReal : ∀ t : ℝ, 0 ≤ t → m ≤ r + t * a := by
    intro t ht
    have hxtC : x0 + t • y ∈ C := hyC hx0C ht
    have hxtLower : (m : EReal) ≤ h (x0 + t • y) := hm _ hxtC
    have hxtEq : h (x0 + t • y) = h x0 + ((t * a : ℝ) : EReal) := ha x0 hx0Dom t ht
    have hreal :
        ((m : ℝ) : EReal) ≤ (((r + t * a : ℝ) : EReal)) := by
      calc
        (m : EReal) ≤ h (x0 + t • y) := hxtLower
        _ = h x0 + ((t * a : ℝ) : EReal) := hxtEq
        _ = (((r + t * a : ℝ) : EReal)) := by
          simp [hr, add_comm, add_left_comm, add_assoc]
    exact EReal.coe_le_coe_iff.mp hreal
  exact
    helperForCorollary_6_27_3_nonnegative_of_uniform_rayLowerBound hboundReal

/-- Helper for Corollary 6.27.3: a real lower bound on `C` also forces a nonnegative affine
ray slope when one only knows that the single ray starting at `x0` stays inside `C`. -/
lemma helperForCorollary_6_27_3_affineSlope_nonnegative_on_pointedFeasibleRay
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (C : Set (Fin n → ℝ)) {y x0 : Fin n → ℝ}
    (hRay : ∀ t : ℝ, 0 ≤ t → x0 + t • y ∈ C) (hx0Top : h x0 < (⊤ : EReal))
    {a : ℝ}
    (ha :
      ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h, ∀ t : ℝ, 0 ≤ t →
        h (x + t • y) = h x + ((t * a : ℝ) : EReal))
    (hbounded : HasRealLowerBoundOn h C) :
    0 ≤ a := by
  rcases hbounded with ⟨m, hm⟩
  have hx0Dom : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [effectiveDomain_eq] using hx0Top
  have hx0Top' : h x0 ≠ (⊤ : EReal) := lt_top_iff_ne_top.mp hx0Top
  have hx0Bot : h x0 ≠ (⊥ : EReal) := hproper.2.2 x0 (by simp)
  lift h x0 to ℝ using ⟨hx0Top', hx0Bot⟩ with r hr
  have hboundReal : ∀ t : ℝ, 0 ≤ t → m ≤ r + t * a := by
    intro t ht
    have hxtC : x0 + t • y ∈ C := hRay t ht
    have hxtLower : (m : EReal) ≤ h (x0 + t • y) := hm _ hxtC
    have hxtEq : h (x0 + t • y) = h x0 + ((t * a : ℝ) : EReal) := ha x0 hx0Dom t ht
    have hreal :
        ((m : ℝ) : EReal) ≤ (((r + t * a : ℝ) : EReal)) := by
      calc
        (m : EReal) ≤ h (x0 + t • y) := hxtLower
        _ = h x0 + ((t * a : ℝ) : EReal) := hxtEq
        _ = (((r + t * a : ℝ) : EReal)) := by
          simp [hr, add_comm, add_left_comm, add_assoc]
    exact EReal.coe_le_coe_iff.mp hreal
  -- A negative slope would eventually violate the fixed lower bound along the feasible ray.
  exact
    helperForCorollary_6_27_3_nonnegative_of_uniform_rayLowerBound hboundReal


end Section27
end Chap06
