/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part8

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 5.24.4: the interval-integral primitive is convex. This is the formal
version of the textbook argument on the finite interval `J`, extended trivially to exterior points
where the primitive equals `+∞`. -/


lemma helperForTheorem_5_24_4_intervalIntegralPrimitive_convex
    (φ : ℝ → EReal) (a : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    ConvexFunction (oneDimensionalIntervalIntegralPrimitive φ a) := by
  let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin 1 → ℝ)), f x ≠ (⊥ : EReal) := by
    intro x hx
    exact helperForTheorem_5_24_4_primitive_ne_bot φ a x
  refine
    (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin 1 → ℝ))) (f := f)
      (hC := convex_univ) (hnotbot := hnotbot)).2 ?_
  intro x hx y hy t ht0 ht1
  have hxScalar : x = scalarPoint (x 0) :=
    helperForTheorem_5_24_2_direction_eq_scalarPoint_apply_zero x
  have hyScalar : y = scalarPoint (y 0) :=
    helperForTheorem_5_24_2_direction_eq_scalarPoint_apply_zero y
  have hzScalar :
      (1 - t) • x + t • y = scalarPoint ((1 - t) * (x 0) + t * (y 0)) := by
    ext i
    fin_cases i
    simp [scalarPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hzScalar' :
      (1 - t) • scalarPoint (x 0) + t • scalarPoint (y 0) =
        scalarPoint ((1 - t) * (x 0) + t * (y 0)) := by
    ext i
    fin_cases i
    simp [scalarPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hxDom : x 0 ∈ scalarEffectiveDomain f
  · by_cases hyDom : y 0 ∈ scalarEffectiveDomain f
    · by_cases hxy : x 0 ≤ y 0
      · rw [hxScalar, hyScalar, hzScalar']
        simpa [f, helperForTheorem_5_24_4_scalarPoint_primitive_eval] using
          helperForTheorem_5_24_4_primitiveValue_convexCombo_of_domain_le
            φ a (x 0) (y 0) t hmono ha hxy hxDom hyDom (le_of_lt ht0) (le_of_lt ht1)
      · have hyx : y 0 ≤ x 0 := le_of_not_ge hxy
        have hseg :=
          helperForTheorem_5_24_4_primitiveValue_convexCombo_of_domain_le
            φ a (y 0) (x 0) (1 - t) hmono ha hyx hyDom hxDom
            (sub_nonneg.mpr (le_of_lt ht1)) (by linarith : 1 - t ≤ 1)
        have hzEq :
            (1 - (1 - t)) * (y 0) + (1 - t) * (x 0) = (1 - t) * (x 0) + t * (y 0) := by
          ring
        rw [hxScalar, hyScalar, hzScalar']
        simpa [f, hzEq, add_comm, add_left_comm, add_assoc,
          helperForTheorem_5_24_4_scalarPoint_primitive_eval] using hseg
    · have hyTop : f y = (⊤ : EReal) := by
        by_contra hyNotTop
        have hyLtTop : f y < (⊤ : EReal) := (lt_top_iff_ne_top).2 hyNotTop
        have hyEff :
            y ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f := by
          simpa [effectiveDomain_eq] using
            (show y ∈ {u | u ∈ (Set.univ : Set (Fin 1 → ℝ)) ∧ f u < (⊤ : EReal)} from
              ⟨by simp, hyLtTop⟩)
        have hyDom' : y 0 ∈ scalarEffectiveDomain f := by
          change scalarPoint (y 0) ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f
          exact hyScalar ▸ hyEff
        exact hyDom hyDom'
      have hxterm_ne_bot : ((1 - t : ℝ) : EReal) * f x ≠ (⊥ : EReal) := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl ?_, Or.inr ?_, Or.inl ?_, Or.inl ?_⟩
        · exact EReal.coe_ne_bot (1 - t)
        · exact hnotbot x hx
        · exact EReal.coe_ne_top (1 - t)
        · exact_mod_cast sub_nonneg.mpr (le_of_lt ht1)
      have hyterm_top : ((t : ℝ) : EReal) * f y = (⊤ : EReal) := by
        simpa [hyTop] using (EReal.mul_top_of_pos ((EReal.coe_pos).2 ht0))
      have hsumTop :
          ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y = (⊤ : EReal) := by
        rw [hyterm_top]
        exact EReal.add_top_of_ne_bot hxterm_ne_bot
      calc
        f ((1 - t) • x + t • y) ≤ (⊤ : EReal) := le_top
        _ = ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y := by
          symm
          exact hsumTop
  · have hxTop : f x = (⊤ : EReal) := by
      by_contra hxNotTop
      have hxLtTop : f x < (⊤ : EReal) := (lt_top_iff_ne_top).2 hxNotTop
      have hxEff :
          x ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f := by
        simpa [effectiveDomain_eq] using
          (show x ∈ {u | u ∈ (Set.univ : Set (Fin 1 → ℝ)) ∧ f u < (⊤ : EReal)} from
            ⟨by simp, hxLtTop⟩)
      have hxDom' : x 0 ∈ scalarEffectiveDomain f := by
        change scalarPoint (x 0) ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f
        exact hxScalar ▸ hxEff
      exact hxDom hxDom'
    have hyterm_ne_bot : ((t : ℝ) : EReal) * f y ≠ (⊥ : EReal) := by
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl ?_, Or.inr ?_, Or.inl ?_, Or.inl ?_⟩
      · exact EReal.coe_ne_bot t
      · exact hnotbot y hy
      · exact EReal.coe_ne_top t
      · exact_mod_cast le_of_lt ht0
    have hxterm_top : ((1 - t : ℝ) : EReal) * f x = (⊤ : EReal) := by
      simpa [hxTop] using (EReal.mul_top_of_pos ((EReal.coe_pos).2 (sub_pos.mpr ht1)))
    have hsumTop :
        ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y = (⊤ : EReal) := by
      rw [hxterm_top]
      exact EReal.top_add_of_ne_bot hyterm_ne_bot
    calc
      f ((1 - t) • x + t • y) ≤ (⊤ : EReal) := le_top
      _ = ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y := by
        symm
        exact hsumTop

/-- On the scalar effective-domain interval `J`, a finite profile value is a lower bound for the
extended right derivative of the primitive. This is the right-hand half of the textbook band
argument. -/
lemma helperForTheorem_5_24_4_profile_le_rightDerivative_on_domain_of_finite_profile
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    (((φ x).toReal : ℝ) : EReal) ≤
      rightDerivativeExtension (oneDimensionalIntervalIntegralPrimitive φ a) x := by
  let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
  have hxDom : x ∈ scalarEffectiveDomain f :=
    helperForTheorem_5_24_4_mem_scalarEffectiveDomain_of_finite_profile φ a x hmono ha hx
  have hconv : ConvexFunction f := by
    simpa [f] using helperForTheorem_5_24_4_intervalIntegralPrimitive_convex φ a hmono ha
  have hxFiniteF : f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
    refine ⟨?_, ?_⟩
    · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hxDom
    · exact helperForTheorem_5_24_4_primitive_ne_bot φ a (scalarPoint x)
  have hxFiniteVal :
      oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊤ : EReal) ∧
        oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊥ : EReal) := by
    simpa [f] using hxFiniteF
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hxDom
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      f hconv (scalarPoint x) hxFiniteF with
    ⟨hdirRight, _hposRight, _hconvRight, _hzeroRight, _hsymmRight⟩
  have hquotLower :
      ∀ {t : ℝ}, 0 < t →
        (((φ x).toReal : ℝ) : EReal) ≤
          directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t := by
    intro t ht
    let y : ℝ := x + t
    by_cases hyDom : y ∈ scalarEffectiveDomain f
    · have hyEq : y - x = t := by
        dsimp [y]
        ring
      have hySub : ((((y - x) * (φ x).toReal : ℝ) : EReal)) =
          (((φ x).toReal : ℝ) : EReal) * (t : EReal) := by
        simp [hyEq, mul_comm]
      have hMulLe :
          (((φ x).toReal : ℝ) : EReal) * (t : EReal) ≤
            oneDimensionalIntervalIntegralPrimitiveValue φ a y -
              oneDimensionalIntervalIntegralPrimitiveValue φ a x := by
        calc
          (((φ x).toReal : ℝ) : EReal) * (t : EReal)
            = ((((y - x) * (φ x).toReal : ℝ) : EReal)) := by
                simpa using hySub.symm
          _ ≤ (((∫ s in x..y, (φ s).toReal) : ℝ) : EReal) :=
            helperForTheorem_5_24_4_profile_mul_sub_le_integral_of_domain_lt
              φ a x y hmono ha hxDom hyDom hx (by dsimp [y]; linarith)
          _ =
              oneDimensionalIntervalIntegralPrimitiveValue φ a y -
                oneDimensionalIntervalIntegralPrimitiveValue φ a x := by
                symm
                exact helperForTheorem_5_24_4_primitiveValue_sub_eq_integral_of_domain_points
                  φ a x y hxDom hyDom
      have htPosE : (0 : EReal) < (t : EReal) := by
        exact_mod_cast ht
      have htNeTop : (t : EReal) ≠ (⊤ : EReal) := by
        simp
      have hDQ :
          directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t =
            (oneDimensionalIntervalIntegralPrimitiveValue φ a y -
                oneDimensionalIntervalIntegralPrimitiveValue φ a x) / (t : EReal) := by
        dsimp [y]
        rw [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant]
        simp [f, helperForTheorem_5_24_4_scalarPoint_primitive_eval]
      rw [hDQ]
      exact (EReal.le_div_iff_mul_le htPosE htNeTop).2 hMulLe
    · have hyTop : f (scalarPoint y) = (⊤ : EReal) := by
        dsimp [y, f]
        exact helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain
          φ a (x + t) hyDom
      rw [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant, hyTop]
      rw [EReal.top_sub hxFiniteF.1]
      have htPosE : (0 : EReal) < (t : EReal) := by
        exact_mod_cast ht
      rw [EReal.top_div_of_pos_ne_top htPosE (by simp : (t : EReal) ≠ (⊤ : EReal))]
      exact le_top
  have hnonempty :
      ((Set.Ioi (0 : ℝ)).image fun t : ℝ =>
        directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t).Nonempty := by
    refine ⟨directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) 1, ?_⟩
    exact ⟨1, by simp, rfl⟩
  have hlower :
      (((φ x).toReal : ℝ) : EReal) ≤
        sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ =>
          directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t) := by
    refine le_csInf hnonempty ?_
    intro q hq
    rcases hq with ⟨t, ht, rfl⟩
    exact hquotLower ht
  have hupper :
      (((φ x).toReal : ℝ) : EReal) ≤ upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint 1) := by
    simpa [(hdirRight (scalarPoint 1)).2.2] using hlower
  rw [rightDerivativeExtension, if_neg hxNot.2, if_neg hxNot.1]
  exact hupper

/-- On the scalar effective-domain interval `J`, a finite profile value also dominates the
extended left derivative of the primitive. This is the left-hand half of the textbook band
argument. -/
lemma helperForTheorem_5_24_4_leftDerivative_le_profile_on_domain_of_finite_profile
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    leftDerivativeExtension (oneDimensionalIntervalIntegralPrimitive φ a) x ≤
      (((φ x).toReal : ℝ) : EReal) := by
  let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
  have hxDom : x ∈ scalarEffectiveDomain f :=
    helperForTheorem_5_24_4_mem_scalarEffectiveDomain_of_finite_profile φ a x hmono ha hx
  have hconv : ConvexFunction f := by
    simpa [f] using helperForTheorem_5_24_4_intervalIntegralPrimitive_convex φ a hmono ha
  have hxFiniteF : f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
    refine ⟨?_, ?_⟩
    · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hxDom
    · exact helperForTheorem_5_24_4_primitive_ne_bot φ a (scalarPoint x)
  have hxFiniteVal :
      oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊤ : EReal) ∧
        oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊥ : EReal) := by
    simpa [f] using hxFiniteF
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hxDom
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      f hconv (scalarPoint x) hxFiniteF with
    ⟨hdirLeft, _hposLeft, _hconvLeft, _hzeroLeft, _hsymmLeft⟩
  have hquotLower :
      ∀ {t : ℝ}, 0 < t →
        -((((φ x).toReal : ℝ) : EReal)) ≤
          directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint (-1)) t := by
    intro t ht
    let y : ℝ := x - t
    have htPosE : (0 : EReal) < (t : EReal) := by
      exact_mod_cast ht
    have htNeTop : (t : EReal) ≠ (⊤ : EReal) := by
      simp
    have hDQ :
        directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint (-1)) t =
          (oneDimensionalIntervalIntegralPrimitiveValue φ a y -
              oneDimensionalIntervalIntegralPrimitiveValue φ a x) / (t : EReal) := by
      have hstepToY : scalarPoint x + t • scalarPoint (-1) = scalarPoint y := by
        ext i
        fin_cases i
        simp [scalarPoint, y, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      rw [directionalDifferenceQuotientAt, hstepToY]
      simp [f, helperForTheorem_5_24_4_scalarPoint_primitive_eval]
    by_cases hyDom : y ∈ scalarEffectiveDomain f
    · have hIncLe :
          oneDimensionalIntervalIntegralPrimitiveValue φ a x -
              oneDimensionalIntervalIntegralPrimitiveValue φ a y ≤
            (t : EReal) * ((((φ x).toReal : ℝ) : EReal)) := by
        have hyx : y < x := by
          dsimp [y]
          linarith
        have hIntLe :
            (((∫ s in y..x, (φ s).toReal) : ℝ) : EReal) ≤
              ((((x - y) * (φ x).toReal : ℝ) : EReal)) :=
          helperForTheorem_5_24_4_integral_le_profile_mul_sub_of_domain_lt
            φ a y x hmono ha hyDom hxDom hx hyx
        calc
          oneDimensionalIntervalIntegralPrimitiveValue φ a x -
              oneDimensionalIntervalIntegralPrimitiveValue φ a y
            = (((∫ s in y..x, (φ s).toReal) : ℝ) : EReal) := by
                exact helperForTheorem_5_24_4_primitiveValue_sub_eq_integral_of_domain_points
                  φ a y x hyDom hxDom
          _ ≤ ((((x - y) * (φ x).toReal : ℝ) : EReal)) := hIntLe
          _ = (t : EReal) * ((((φ x).toReal : ℝ) : EReal)) := by
              have hyEq : x - y = t := by
                dsimp [y]
                ring
              simp [hyEq, mul_comm]
      have hyFiniteF : f (scalarPoint y) ≠ (⊤ : EReal) ∧ f (scalarPoint y) ≠ (⊥ : EReal) := by
        refine ⟨?_, ?_⟩
        · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hyDom
        · exact helperForTheorem_5_24_4_primitive_ne_bot φ a (scalarPoint y)
      have hyFiniteVal :
          oneDimensionalIntervalIntegralPrimitiveValue φ a y ≠ (⊤ : EReal) ∧
            oneDimensionalIntervalIntegralPrimitiveValue φ a y ≠ (⊥ : EReal) := by
        simpa [f] using hyFiniteF
      have hnegDQ :
          -directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint (-1)) t =
            (oneDimensionalIntervalIntegralPrimitiveValue φ a x -
                oneDimensionalIntervalIntegralPrimitiveValue φ a y) / (t : EReal) := by
        rw [hDQ]
        have htmp :
            -((oneDimensionalIntervalIntegralPrimitiveValue φ a y -
                  oneDimensionalIntervalIntegralPrimitiveValue φ a x) / (t : EReal)) =
              (oneDimensionalIntervalIntegralPrimitiveValue φ a x -
                  oneDimensionalIntervalIntegralPrimitiveValue φ a y) / (t : EReal) := by
          rw [EReal.div_eq_inv_mul, EReal.div_eq_inv_mul, neg_mul_eq_mul_neg]
          rw [EReal.neg_sub (Or.inl hyFiniteVal.2) (Or.inl hyFiniteVal.1)]
          simp [sub_eq_add_neg, add_comm]
        exact htmp
      have hnegDQLe :
          -directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint (-1)) t ≤
            (((φ x).toReal : ℝ) : EReal) := by
        rw [hnegDQ]
        exact (EReal.div_le_iff_le_mul htPosE htNeTop).2 hIncLe
      rw [← EReal.neg_le_neg_iff, neg_neg]
      exact hnegDQLe
    · have hyTop : f (scalarPoint y) = (⊤ : EReal) := by
        dsimp [y, f]
        exact helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain
          φ a (x - t) hyDom
      have hyTop' : oneDimensionalIntervalIntegralPrimitiveValue φ a y = (⊤ : EReal) := by
        simpa [f] using hyTop
      rw [hDQ, hyTop', EReal.top_sub hxFiniteVal.1]
      rw [EReal.top_div_of_pos_ne_top htPosE htNeTop]
      exact le_top
  have hnonempty :
      ((Set.Ioi (0 : ℝ)).image fun t : ℝ =>
        directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint (-1)) t).Nonempty := by
    refine ⟨directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint (-1)) 1, ?_⟩
    exact ⟨1, by simp, rfl⟩
  have hlower :
      -((((φ x).toReal : ℝ) : EReal)) ≤
        sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ =>
          directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint (-1)) t) := by
    refine le_csInf hnonempty ?_
    intro q hq
    rcases hq with ⟨t, ht, rfl⟩
    exact hquotLower ht
  have hupper :
      -((((φ x).toReal : ℝ) : EReal)) ≤
        upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint (-1)) := by
    simpa [(hdirLeft (scalarPoint (-1))).2.2] using hlower
  rw [leftDerivativeExtension, if_neg hxNot.2, if_neg hxNot.1]
  rw [← EReal.neg_le_neg_iff, neg_neg]
  exact hupper

/-- At a scalar domain point where the profile already equals `+∞`, the primitive has no domain
points to the right, so every positive-step secant slope is `+∞` and hence the extended right
derivative is also `+∞`. -/
lemma helperForTheorem_5_24_4_rightDerivative_eq_top_on_domain_of_top_profile
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hxTop : φ x = (⊤ : EReal)) :
    rightDerivativeExtension (oneDimensionalIntervalIntegralPrimitive φ a) x = (⊤ : EReal) := by
  let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
  have hconv : ConvexFunction f := by
    simpa [f] using helperForTheorem_5_24_4_intervalIntegralPrimitive_convex φ a hmono ha
  have hxFiniteF : f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
    refine ⟨?_, ?_⟩
    · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hxDom
    · exact helperForTheorem_5_24_4_primitive_ne_bot φ a (scalarPoint x)
  have hxFiniteVal :
      oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊤ : EReal) ∧
        oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊥ : EReal) := by
    simpa [f] using hxFiniteF
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hxDom
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      f hconv (scalarPoint x) hxFiniteF with
    ⟨hdirRight, _hposRight, _hconvRight, _hzeroRight, _hsymmRight⟩
  have hquotTop :
      ∀ {t : ℝ}, 0 < t →
        directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t = (⊤ : EReal) := by
    intro t ht
    have hyOff : x + t ∉ scalarEffectiveDomain f := by
      exact
        helperForTheorem_5_24_4_no_domain_point_to_right_of_top_profile
          φ a x (x + t) hmono ha hxDom (by linarith) hxTop
    have hyTop :
        oneDimensionalIntervalIntegralPrimitiveValue φ a (x + t) = (⊤ : EReal) := by
      exact helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain
        φ a (x + t) hyOff
    rw [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant]
    change
      (oneDimensionalIntervalIntegralPrimitiveValue φ a (x + t) -
          oneDimensionalIntervalIntegralPrimitiveValue φ a x) / (t : EReal) = (⊤ : EReal)
    rw [hyTop]
    rw [EReal.top_sub hxFiniteVal.1]
    rw [EReal.top_div_of_pos_ne_top (by exact_mod_cast ht) (by simp : (t : EReal) ≠ (⊤ : EReal))]
  have hSet :
      ((Set.Ioi (0 : ℝ)).image fun t : ℝ =>
        directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t) = ({⊤} : Set EReal) := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨t, ht, rfl⟩
      simp [hquotTop ht]
    · intro hq
      simp at hq
      subst hq
      refine ⟨1, by simp, ?_⟩
      exact hquotTop (by norm_num)
  have hupperTop :
      upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint 1) = (⊤ : EReal) := by
    rw [(hdirRight (scalarPoint 1)).2.2, hSet]
    simp
  rw [rightDerivativeExtension, if_neg hxNot.2, if_neg hxNot.1, hupperTop]

/-- At a scalar domain point where the profile already equals `-∞`, the primitive has no domain
points to the left, so every positive-step quotient in direction `-1` is `+∞`; negating gives an
extended left derivative equal to `-∞`. -/
lemma helperForTheorem_5_24_4_leftDerivative_eq_bot_on_domain_of_bot_profile
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hxBot : φ x = (⊥ : EReal)) :
    leftDerivativeExtension (oneDimensionalIntervalIntegralPrimitive φ a) x = (⊥ : EReal) := by
  let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
  have hconv : ConvexFunction f := by
    simpa [f] using helperForTheorem_5_24_4_intervalIntegralPrimitive_convex φ a hmono ha
  have hxFiniteF : f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
    refine ⟨?_, ?_⟩
    · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hxDom
    · exact helperForTheorem_5_24_4_primitive_ne_bot φ a (scalarPoint x)
  have hxFiniteVal :
      oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊤ : EReal) ∧
        oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊥ : EReal) := by
    simpa [f] using hxFiniteF
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hxDom
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      f hconv (scalarPoint x) hxFiniteF with
    ⟨hdirLeft, _hposLeft, _hconvLeft, _hzeroLeft, _hsymmLeft⟩
  have hquotTop :
      ∀ {t : ℝ}, 0 < t →
        directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint (-1)) t = (⊤ : EReal) := by
    intro t ht
    let y : ℝ := x - t
    have hyOff : y ∉ scalarEffectiveDomain f := by
      exact
        helperForTheorem_5_24_4_no_domain_point_to_left_of_bot_profile
          φ a x y hmono ha hxDom (by dsimp [y]; linarith) hxBot
    have hyTop :
        oneDimensionalIntervalIntegralPrimitiveValue φ a y = (⊤ : EReal) := by
      exact helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain
        φ a y hyOff
    have hDQ :
        directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint (-1)) t =
          (oneDimensionalIntervalIntegralPrimitiveValue φ a y -
              oneDimensionalIntervalIntegralPrimitiveValue φ a x) / (t : EReal) := by
      have hstepToY : scalarPoint x + t • scalarPoint (-1) = scalarPoint y := by
        ext i
        fin_cases i
        simp [scalarPoint, y, sub_eq_add_neg]
      rw [directionalDifferenceQuotientAt, hstepToY]
      simp [f, helperForTheorem_5_24_4_scalarPoint_primitive_eval]
    rw [hDQ, hyTop, EReal.top_sub hxFiniteVal.1]
    rw [EReal.top_div_of_pos_ne_top (by exact_mod_cast ht) (by simp : (t : EReal) ≠ (⊤ : EReal))]
  have hSet :
      ((Set.Ioi (0 : ℝ)).image fun t : ℝ =>
        directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint (-1)) t) = ({⊤} : Set EReal) := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨t, ht, rfl⟩
      simp [hquotTop ht]
    · intro hq
      simp at hq
      subst hq
      refine ⟨1, by simp, ?_⟩
      exact hquotTop (by norm_num)
  have hupperTop :
      upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint (-1)) = (⊤ : EReal) := by
    rw [(hdirLeft (scalarPoint (-1))).2.2, hSet]
    simp
  rw [leftDerivativeExtension, if_neg hxNot.2, if_neg hxNot.1, hupperTop]
  simp

/-- The full derivative band on the scalar effective domain `J`: finite profile values are handled
by the integral secant estimates, while `±∞` profile values force the corresponding endpoint
derivatives to be `±∞`. -/
lemma helperForTheorem_5_24_4_scalarBand_on_scalarEffectiveDomain
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :
    leftDerivativeExtension (oneDimensionalIntervalIntegralPrimitive φ a) x ≤ φ x ∧
      φ x ≤ rightDerivativeExtension (oneDimensionalIntervalIntegralPrimitive φ a) x := by
  by_cases hxTop : φ x = (⊤ : EReal)
  · constructor
    · rw [hxTop]
      exact le_top
    · rw [hxTop,
        helperForTheorem_5_24_4_rightDerivative_eq_top_on_domain_of_top_profile
          φ a x hmono ha hxDom hxTop]
  · by_cases hxBot : φ x = (⊥ : EReal)
    · constructor
      · rw [helperForTheorem_5_24_4_leftDerivative_eq_bot_on_domain_of_bot_profile
          φ a x hmono ha hxDom hxBot, hxBot]
      · rw [hxBot]
        exact bot_le
    · have hxFinite : x ∈ oneDimensionalPrimitiveFiniteValueSet φ := ⟨hxTop, hxBot⟩
      have hxCoe : (((φ x).toReal : ℝ) : EReal) = φ x := EReal.coe_toReal hxTop hxBot
      constructor
      · simpa [hxCoe] using
          helperForTheorem_5_24_4_leftDerivative_le_profile_on_domain_of_finite_profile
            φ a x hmono ha hxFinite
      · simpa [hxCoe] using
          helperForTheorem_5_24_4_profile_le_rightDerivative_on_domain_of_finite_profile
            φ a x hmono ha hxFinite

/-- A point strictly to the right of the scalar effective domain is still a
lower-semicontinuity point of the primitive. Away from the actual right endpoint this is
immediate because a whole left neighborhood already lies outside the domain. At the endpoint
itself, failure of lower semicontinuity would produce bounded primitive values along a sequence
approaching from the left; shifting by the finite anchor value `φ(a)` turns the integrand
nonnegative, and the bounded improper integrals then force integrability up to `x`, contradicting
that `x` lies strictly right of the domain. -/
lemma helperForTheorem_5_24_4_primitiveValue_lowerSemicontinuousAt_of_rightOfScalarEffectiveDomain
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxRight : IsRightOfScalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) x) :
    LowerSemicontinuousAt (oneDimensionalIntervalIntegralPrimitiveValue φ a) x := by
  let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
  let F : ℝ → EReal := oneDimensionalIntervalIntegralPrimitiveValue φ a
  have haDom : a ∈ scalarEffectiveDomain f :=
    helperForTheorem_5_24_4_scalarBasePoint_mem_scalarEffectiveDomain φ a
  have hax : a < x := hxRight a haDom
  have hxOff : x ∉ scalarEffectiveDomain f := by
    intro hxDom
    exact (lt_irrefl x) (hxRight x hxDom)
  have hxTop : F x = (⊤ : EReal) := by
    simpa [F, f] using
      helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain φ a x hxOff
  intro b hb
  have hbTop : b < (⊤ : EReal) := hxTop ▸ hb
  by_cases hbBot : b = (⊥ : EReal)
  · subst hbBot
    refine Filter.mem_of_superset Filter.univ_mem ?_
    intro z _hz
    simpa [F] using
      (bot_lt_iff_ne_bot.2 (helperForTheorem_5_24_4_primitiveValue_ne_bot φ a z))
  have hbCoe : (((b.toReal : ℝ) : EReal)) = b := by
    simpa using (EReal.coe_toReal hbTop.ne hbBot)
  by_cases hgap : ∃ y, y ∈ Set.Ioo a x ∧ y ∉ scalarEffectiveDomain f
  · rcases hgap with ⟨y, hy, hyOff⟩
    have hyRight :
        IsRightOfScalarEffectiveDomain f y := by
      rcases
          helperForTheorem_5_24_4_off_scalarEffectiveDomain_is_exterior
            φ a y hmono ha hyOff with
        hyRight | hyLeft
      · exact hyRight
      · exfalso
        exact (not_lt_of_ge hy.1.le) (hyLeft a haDom)
    refine Filter.mem_of_superset (Ioi_mem_nhds hy.2) ?_
    intro z hz
    have hzOff : z ∉ scalarEffectiveDomain f := by
      intro hzDom
      exact (not_lt_of_ge hz.le) (hyRight z hzDom)
    have hzTop : F z = (⊤ : EReal) := by
      simpa [F, f] using
        helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain φ a z hzOff
    simpa [F, hzTop] using hbTop
  · have hAllDom : ∀ y ∈ Set.Ioo a x, y ∈ scalarEffectiveDomain f := by
      intro y hy
      by_contra hyOff
      exact hgap ⟨y, hy, hyOff⟩
    by_contra hNotEventually
    have hfreqLe : ∃ᶠ z in nhds x, F z ≤ ((b.toReal : ℝ) : EReal) := by
      have hfreqNot : ∃ᶠ z in nhds x, ¬ b < F z :=
        (Filter.not_eventually.1 hNotEventually)
      exact hfreqNot.mono (fun z hz => by simpa [hbCoe] using not_lt.mp hz)
    have hfreqBounded :
        ∃ᶠ z in nhds x, z ∈ {z : ℝ | F z ≤ ((b.toReal : ℝ) : EReal)} ∩ Set.Ioi a := by
      exact
        (hfreqLe.and_eventually (Ioi_mem_nhds hax)).mono
          (fun z hz => ⟨hz.1, hz.2⟩)
    have hxClosure :
        x ∈ closure ({z : ℝ | F z ≤ ((b.toReal : ℝ) : EReal)} ∩ Set.Ioi a) :=
      (mem_closure_iff_frequently.2 hfreqBounded)
    rcases (mem_closure_iff_seq_limit.1 hxClosure) with ⟨u, hu_mem, hu_tend⟩
    have hu_a : ∀ n, a < u n := fun n => (hu_mem n).2
    have hu_le :
        ∀ n, F (u n) ≤ ((b.toReal : ℝ) : EReal) := fun n => (hu_mem n).1
    have huDom : ∀ n, u n ∈ scalarEffectiveDomain f := by
      intro n
      have huLtTop : F (u n) < (⊤ : EReal) :=
        lt_of_le_of_lt (hu_le n) (by simp)
      have huEff :
          scalarPoint (u n) ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f := by
        simpa [effectiveDomain_eq, f, F] using
          (show scalarPoint (u n) ∈
              {v : Fin 1 → ℝ | v ∈ (Set.univ : Set (Fin 1 → ℝ)) ∧ f v < (⊤ : EReal)} from
            ⟨by simp, by simpa [f, F] using huLtTop⟩)
      simpa [scalarEffectiveDomain] using huEff
    have hu_lt_x : ∀ n, u n < x := fun n => hxRight (u n) (huDom n)
    let c : ℝ := (φ a).toReal
    let ψ : ℝ → ℝ := fun t => (φ t).toReal - c
    have hfi : ∀ n, MeasureTheory.IntegrableOn ψ (Set.Ioc a (u n)) := by
      intro n
      have hInt :
          IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a (u n) :=
        (helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
          φ a (u n) (huDom n)).2
      have hConst :
          IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a (u n) := by
        simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c)
          MeasureTheory.volume a (u n))
      have hPsi : IntervalIntegrable ψ MeasureTheory.volume a (u n) := hInt.sub hConst
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hu_a n).le] at hPsi
      simpa [ψ] using hPsi
    have hbound :
        ∀ᶠ n in Filter.atTop,
          (∫ t in Set.Ioc a (u n), ‖ψ t‖) ≤ b.toReal + |c| * (x - a) := by
      refine Filter.Eventually.of_forall ?_
      intro n
      have hOpenUn :
          ∀ t ∈ Set.uIoo a (u n), φ t ≠ (⊤ : EReal) ∧ φ t ≠ (⊥ : EReal) :=
        (helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
          φ a (u n) (huDom n)).1
      have hNormEq :
          ∫ t in Set.Ioc a (u n), ‖ψ t‖ = ∫ t in Set.Ioc a (u n), ψ t := by
        calc
          ∫ t in Set.Ioc a (u n), ‖ψ t‖ =
              ∫ t in Set.Ioo a (u n), ‖ψ t‖ := by
                simpa using
                  (MeasureTheory.integral_Ioc_eq_integral_Ioo
                    (μ := MeasureTheory.volume) (f := fun t : ℝ => ‖ψ t‖)
                    (x := a) (y := u n))
          _ = ∫ t in Set.Ioo a (u n), ψ t := by
                refine MeasureTheory.integral_congr_ae ?_
                refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2 ?_
                refine Filter.Eventually.of_forall ?_
                intro t ht
                have htFinite :
                    t ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
                  hOpenUn t (by
                    simpa [Set.uIoo_of_lt (hu_a n)] using ht)
                have hnonneg : 0 ≤ ψ t := by
                  dsimp [ψ, c]
                  exact sub_nonneg.mpr
                    (EReal.toReal_le_toReal (hmono ht.1.le) ha.2 htFinite.1)
                simp [Real.norm_eq_abs, ψ, abs_of_nonneg hnonneg]
          _ = ∫ t in Set.Ioc a (u n), ψ t := by
                symm
                simpa using
                  (MeasureTheory.integral_Ioc_eq_integral_Ioo
                    (μ := MeasureTheory.volume) (f := ψ)
                    (x := a) (y := u n))
      have huEq :
          F (u n) = (((∫ t in a..u n, (φ t).toReal) : ℝ) : EReal) := by
        simpa [F, f] using
          helperForTheorem_5_24_4_primitiveValue_eq_integral_of_mem_scalarEffectiveDomain
            φ a (u n) (huDom n)
      have hIntLe :
          ∫ t in a..u n, (φ t).toReal ≤ b.toReal := by
        have hE :
            (((∫ t in a..u n, (φ t).toReal) : ℝ) : EReal) ≤ ((b.toReal : ℝ) : EReal) := by
          simpa [huEq] using hu_le n
        exact EReal.toReal_le_toReal hE (by simp) (by simp)
      let I : ℝ := ∫ t in a..u n, (φ t).toReal
      have hIntLe' : I ≤ b.toReal := by
        simpa [I] using hIntLe
      have hEqInterval :
          ∫ t in Set.Ioc a (u n), ψ t = ∫ t in a..u n, ψ t := by
        symm
        exact intervalIntegral.integral_of_le (hu_a n).le
      have hEqDiff :
          ∫ t in a..u n, ψ t =
            I - c * (u n - a) := by
        have hConstInt :
            IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a (u n) := by
          simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c)
            MeasureTheory.volume a (u n))
        have hConstEval :
            ∫ t in a..u n, (fun _ : ℝ => c) t = c * (u n - a) := by
          rw [intervalIntegral.integral_const]
          simpa [smul_eq_mul, sub_mul, mul_comm]
        rw [show ψ = fun t : ℝ => (φ t).toReal - (fun _ : ℝ => c) t by
          funext t
          simp [ψ]]
        rw [intervalIntegral.integral_sub
          ((helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
            φ a (u n) (huDom n)).2) hConstInt]
        rw [hConstEval]
      have hlen_nonneg : 0 ≤ u n - a := sub_nonneg.mpr (hu_a n).le
      have hlen_le : u n - a ≤ x - a := by
        exact sub_le_sub_right (hu_lt_x n).le a
      have hterm :
          -(c * (u n - a)) ≤ |c| * (x - a) := by
        have hterm1 : (-c) * (u n - a) ≤ |c| * (u n - a) := by
          exact mul_le_mul_of_nonneg_right (neg_le_abs c) hlen_nonneg
        have hterm2 : |c| * (u n - a) ≤ |c| * (x - a) := by
          exact mul_le_mul_of_nonneg_left hlen_le (abs_nonneg c)
        simpa [neg_mul] using le_trans hterm1 hterm2
      calc
        ∫ t in Set.Ioc a (u n), ‖ψ t‖ = ∫ t in a..u n, ψ t := by
          rw [hNormEq, hEqInterval]
        _ = I - c * (u n - a) := hEqDiff
        _ ≤ b.toReal - c * (u n - a) := by
          exact sub_le_sub_right hIntLe' (c * (u n - a))
        _ ≤ b.toReal + |c| * (x - a) := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (add_le_add_left hterm b.toReal)
    have hIntOn :
        MeasureTheory.IntegrableOn ψ (Set.Ioc a x) := by
      exact
        MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
          (I := b.toReal + |c| * (x - a)) (a := a) (b₀ := x)
          (f := ψ) hfi hu_tend hbound
    have hConstOn : MeasureTheory.IntegrableOn (fun _ : ℝ => c) (Set.Ioc a x) := by
      simpa using
        (MeasureTheory.integrableOn_const (s := Set.Ioc a x) (C := c) (μ := MeasureTheory.volume))
    have hToRealOn :
        MeasureTheory.IntegrableOn (fun t : ℝ => (φ t).toReal) (Set.Ioc a x) := by
      have hEq :
          (fun t : ℝ => (φ t).toReal) = fun t : ℝ => ψ t + c := by
        funext t
        dsimp [ψ, c]
        ring
      rw [hEq]
      exact hIntOn.add hConstOn
    have hFiniteOpenX :
        ∀ t ∈ Set.uIoo a x, φ t ≠ (⊤ : EReal) ∧ φ t ≠ (⊥ : EReal) := by
      intro t ht
      have htIoo : t ∈ Set.Ioo a x := by
        simpa [Set.uIoo_of_lt hax] using ht
      let y : ℝ := (t + x) / 2
      have hyIoo : y ∈ Set.Ioo a x := by
        dsimp [y]
        constructor <;> nlinarith [htIoo.1, htIoo.2]
      have hyDom : y ∈ scalarEffectiveDomain f := hAllDom y hyIoo
      have hOpenY :
          ∀ s ∈ Set.uIoo a y, φ s ≠ (⊤ : EReal) ∧ φ s ≠ (⊥ : EReal) :=
        (helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
          φ a y hyDom).1
      exact hOpenY t (by
        have hty : t < y := by
          dsimp [y]
          nlinarith [htIoo.2]
        simpa [Set.uIoo_of_lt (lt_trans htIoo.1 hty)] using (show t ∈ Set.Ioo a y from ⟨htIoo.1, hty⟩))
    have hIntX :
        IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a x := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hax.le]
      exact hToRealOn
    have hxVal :
        F x = (((∫ t in a..x, (φ t).toReal) : ℝ) : EReal) := by
      dsimp [F, oneDimensionalIntervalIntegralPrimitiveValue]
      rw [if_pos hFiniteOpenX, if_pos hIntX]
    have hxNotTop' : F x ≠ (⊤ : EReal) := by
      rw [hxVal]
      simp
    exact hxNotTop' hxTop

/-- The left-exterior case is the mirror image of the previous lemma: if a point lies strictly to
the left of the scalar effective domain, then bounded primitive values approaching from the right
would force the primitive-defining integral to extend up to that point, contradicting exteriority.
-/
lemma helperForTheorem_5_24_4_primitiveValue_lowerSemicontinuousAt_of_leftOfScalarEffectiveDomain
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxLeft : IsLeftOfScalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) x) :
    LowerSemicontinuousAt (oneDimensionalIntervalIntegralPrimitiveValue φ a) x := by
  let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
  let F : ℝ → EReal := oneDimensionalIntervalIntegralPrimitiveValue φ a
  have haDom : a ∈ scalarEffectiveDomain f :=
    helperForTheorem_5_24_4_scalarBasePoint_mem_scalarEffectiveDomain φ a
  have hxa : x < a := hxLeft a haDom
  have hxOff : x ∉ scalarEffectiveDomain f := by
    intro hxDom
    exact (lt_irrefl x) (hxLeft x hxDom)
  have hxTop : F x = (⊤ : EReal) := by
    simpa [F, f] using
      helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain φ a x hxOff
  intro b hb
  have hbTop : b < (⊤ : EReal) := hxTop ▸ hb
  by_cases hbBot : b = (⊥ : EReal)
  · subst hbBot
    refine Filter.mem_of_superset Filter.univ_mem ?_
    intro z _hz
    simpa [F] using
      (bot_lt_iff_ne_bot.2 (helperForTheorem_5_24_4_primitiveValue_ne_bot φ a z))
  have hbCoe : (((b.toReal : ℝ) : EReal)) = b := by
    simpa using (EReal.coe_toReal hbTop.ne hbBot)
  by_cases hgap : ∃ y, y ∈ Set.Ioo x a ∧ y ∉ scalarEffectiveDomain f
  · rcases hgap with ⟨y, hy, hyOff⟩
    have hyLeft :
        IsLeftOfScalarEffectiveDomain f y := by
      rcases
          helperForTheorem_5_24_4_off_scalarEffectiveDomain_is_exterior
            φ a y hmono ha hyOff with
        hyRight | hyLeft
      · exfalso
        exact (not_lt_of_ge hy.2.le) (hyRight a haDom)
      · exact hyLeft
    refine Filter.mem_of_superset (Iio_mem_nhds hy.1) ?_
    intro z hz
    have hzOff : z ∉ scalarEffectiveDomain f := by
      intro hzDom
      exact (not_lt_of_ge hz.le) (hyLeft z hzDom)
    have hzTop : F z = (⊤ : EReal) := by
      simpa [F, f] using
        helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain φ a z hzOff
    simpa [F, hzTop] using hbTop
  · have hAllDom : ∀ y ∈ Set.Ioo x a, y ∈ scalarEffectiveDomain f := by
      intro y hy
      by_contra hyOff
      exact hgap ⟨y, hy, hyOff⟩
    by_contra hNotEventually
    have hfreqLe : ∃ᶠ z in nhds x, F z ≤ ((b.toReal : ℝ) : EReal) := by
      have hfreqNot : ∃ᶠ z in nhds x, ¬ b < F z :=
        (Filter.not_eventually.1 hNotEventually)
      exact hfreqNot.mono (fun z hz => by simpa [hbCoe] using not_lt.mp hz)
    have hfreqBounded :
        ∃ᶠ z in nhds x, z ∈ {z : ℝ | F z ≤ ((b.toReal : ℝ) : EReal)} ∩ Set.Iio a := by
      exact
        (hfreqLe.and_eventually (Iio_mem_nhds hxa)).mono
          (fun z hz => ⟨hz.1, hz.2⟩)
    have hxClosure :
        x ∈ closure ({z : ℝ | F z ≤ ((b.toReal : ℝ) : EReal)} ∩ Set.Iio a) :=
      (mem_closure_iff_frequently.2 hfreqBounded)
    rcases (mem_closure_iff_seq_limit.1 hxClosure) with ⟨u, hu_mem, hu_tend⟩
    have hu_a : ∀ n, u n < a := fun n => (hu_mem n).2
    have hu_le :
        ∀ n, F (u n) ≤ ((b.toReal : ℝ) : EReal) := fun n => (hu_mem n).1
    have huDom : ∀ n, u n ∈ scalarEffectiveDomain f := by
      intro n
      have huLtTop : F (u n) < (⊤ : EReal) :=
        lt_of_le_of_lt (hu_le n) (by simp)
      have huEff :
          scalarPoint (u n) ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f := by
        simpa [effectiveDomain_eq, f, F] using
          (show scalarPoint (u n) ∈
              {v : Fin 1 → ℝ | v ∈ (Set.univ : Set (Fin 1 → ℝ)) ∧ f v < (⊤ : EReal)} from
            ⟨by simp, by simpa [f, F] using huLtTop⟩)
      simpa [scalarEffectiveDomain] using huEff
    have hx_lt_u : ∀ n, x < u n := fun n => hxLeft (u n) (huDom n)
    let c : ℝ := (φ a).toReal
    let ψ : ℝ → ℝ := fun t => c - (φ t).toReal
    have hfi : ∀ n, MeasureTheory.IntegrableOn ψ (Set.Ioc (u n) a) := by
      intro n
      have hInt :
          IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume (u n) a :=
        (helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
          φ a (u n) (huDom n)).2.symm
      have hConst :
          IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume (u n) a := by
        simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c)
          MeasureTheory.volume (u n) a)
      have hPsi : IntervalIntegrable ψ MeasureTheory.volume (u n) a := hConst.sub hInt
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hu_a n).le] at hPsi
      simpa [ψ] using hPsi
    have hbound :
        ∀ᶠ n in Filter.atTop,
          (∫ t in Set.Ioc (u n) a, ‖ψ t‖) ≤ b.toReal + |c| * (a - x) := by
      refine Filter.Eventually.of_forall ?_
      intro n
      have hOpenUn :
          ∀ t ∈ Set.uIoo a (u n), φ t ≠ (⊤ : EReal) ∧ φ t ≠ (⊥ : EReal) :=
        (helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
          φ a (u n) (huDom n)).1
      have hNormEq :
          ∫ t in Set.Ioc (u n) a, ‖ψ t‖ = ∫ t in Set.Ioc (u n) a, ψ t := by
        calc
          ∫ t in Set.Ioc (u n) a, ‖ψ t‖ =
              ∫ t in Set.Ioo (u n) a, ‖ψ t‖ := by
                simpa using
                  (MeasureTheory.integral_Ioc_eq_integral_Ioo
                    (μ := MeasureTheory.volume) (f := fun t : ℝ => ‖ψ t‖)
                    (x := u n) (y := a))
          _ = ∫ t in Set.Ioo (u n) a, ψ t := by
                refine MeasureTheory.integral_congr_ae ?_
                refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2 ?_
                refine Filter.Eventually.of_forall ?_
                intro t ht
                have htFinite :
                    t ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
                  hOpenUn t (by
                    simpa [Set.uIoo_of_ge (hu_a n).le] using ht)
                have hnonneg : 0 ≤ ψ t := by
                  dsimp [ψ, c]
                  exact sub_nonneg.mpr
                    (EReal.toReal_le_toReal (hmono ht.2.le) htFinite.2 ha.1)
                simp [Real.norm_eq_abs, ψ, abs_of_nonneg hnonneg]
          _ = ∫ t in Set.Ioc (u n) a, ψ t := by
                symm
                simpa using
                  (MeasureTheory.integral_Ioc_eq_integral_Ioo
                    (μ := MeasureTheory.volume) (f := ψ)
                    (x := u n) (y := a))
      have huEq :
          F (u n) = (((∫ t in a..u n, (φ t).toReal) : ℝ) : EReal) := by
        simpa [F, f] using
          helperForTheorem_5_24_4_primitiveValue_eq_integral_of_mem_scalarEffectiveDomain
            φ a (u n) (huDom n)
      have hIntLe :
          ∫ t in a..u n, (φ t).toReal ≤ b.toReal := by
        have hE :
            (((∫ t in a..u n, (φ t).toReal) : ℝ) : EReal) ≤ ((b.toReal : ℝ) : EReal) := by
          simpa [huEq] using hu_le n
        exact EReal.toReal_le_toReal hE (by simp) (by simp)
      let I : ℝ := ∫ t in a..u n, (φ t).toReal
      have hIntLe' : I ≤ b.toReal := by
        simpa [I] using hIntLe
      have hEqInterval :
          ∫ t in Set.Ioc (u n) a, ψ t = ∫ t in u n..a, ψ t := by
        symm
        exact intervalIntegral.integral_of_le (hu_a n).le
      have hEqDiff :
          ∫ t in u n..a, ψ t = c * (a - u n) + I := by
        have hConstInt :
            IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume (u n) a := by
          simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c)
            MeasureTheory.volume (u n) a)
        have hConstEval :
            ∫ t in u n..a, (fun _ : ℝ => c) t = c * (a - u n) := by
          rw [intervalIntegral.integral_const]
          simp [smul_eq_mul, mul_comm]
        rw [show ψ = fun t : ℝ => (fun _ : ℝ => c) t - (φ t).toReal by
          funext t
          simp [ψ]]
        rw [intervalIntegral.integral_sub hConstInt
          ((helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
            φ a (u n) (huDom n)).2.symm)]
        rw [hConstEval]
        have hSymm :
            ∫ t in u n..a, (φ t).toReal = -I := by
          rw [intervalIntegral.integral_symm]
        rw [hSymm]
        ring
      have hlen_nonneg : 0 ≤ a - u n := sub_nonneg.mpr (hu_a n).le
      have hlen_le : a - u n ≤ a - x := by
        exact sub_le_sub_left (hx_lt_u n).le a
      have hterm :
          c * (a - u n) ≤ |c| * (a - x) := by
        have hterm1 : c * (a - u n) ≤ |c| * (a - u n) := by
          exact mul_le_mul_of_nonneg_right (le_abs_self c) hlen_nonneg
        have hterm2 : |c| * (a - u n) ≤ |c| * (a - x) := by
          exact mul_le_mul_of_nonneg_left hlen_le (abs_nonneg c)
        exact le_trans hterm1 hterm2
      calc
        ∫ t in Set.Ioc (u n) a, ‖ψ t‖ = ∫ t in u n..a, ψ t := by
          rw [hNormEq, hEqInterval]
        _ = c * (a - u n) + I := hEqDiff
        _ ≤ c * (a - u n) + b.toReal := by
          linarith
        _ ≤ b.toReal + |c| * (a - x) := by
          linarith
    have hIntOn :
        MeasureTheory.IntegrableOn ψ (Set.Ioc x a) := by
      exact
        MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_left
          (I := b.toReal + |c| * (a - x)) (a := u) (a₀ := x) (b := a)
          (f := ψ) hfi hu_tend hbound
    have hConstOn : MeasureTheory.IntegrableOn (fun _ : ℝ => c) (Set.Ioc x a) := by
      simpa using
        (MeasureTheory.integrableOn_const (s := Set.Ioc x a) (C := c) (μ := MeasureTheory.volume))
    have hToRealOn :
        MeasureTheory.IntegrableOn (fun t : ℝ => (φ t).toReal) (Set.Ioc x a) := by
      have hEq :
          (fun t : ℝ => (φ t).toReal) = fun t : ℝ => c - ψ t := by
        funext t
        dsimp [ψ, c]
        ring
      rw [hEq]
      exact hConstOn.sub hIntOn
    have hFiniteOpenX :
        ∀ t ∈ Set.uIoo a x, φ t ≠ (⊤ : EReal) ∧ φ t ≠ (⊥ : EReal) := by
      intro t ht
      have htIoo : t ∈ Set.Ioo x a := by
        simpa [Set.uIoo_of_gt hxa] using ht
      let y : ℝ := (x + t) / 2
      have hyIoo : y ∈ Set.Ioo x a := by
        dsimp [y]
        constructor <;> nlinarith [htIoo.1, htIoo.2]
      have hyDom : y ∈ scalarEffectiveDomain f := hAllDom y hyIoo
      have hOpenY :
          ∀ s ∈ Set.uIoo a y, φ s ≠ (⊤ : EReal) ∧ φ s ≠ (⊥ : EReal) :=
        (helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
          φ a y hyDom).1
      exact hOpenY t (by
        have hyt : y < t := by
          dsimp [y]
          nlinarith [htIoo.1]
        simpa [Set.uIoo_of_ge hyIoo.2.le] using (show t ∈ Set.Ioo y a from ⟨hyt, htIoo.2⟩))
    have hIntX' :
        IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume x a := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxa.le]
      exact hToRealOn
    have hIntX :
        IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a x := hIntX'.symm
    have hxVal :
        F x = (((∫ t in a..x, (φ t).toReal) : ℝ) : EReal) := by
      dsimp [F, oneDimensionalIntervalIntegralPrimitiveValue]
      rw [if_pos hFiniteOpenX, if_pos hIntX]
    have hxNotTop' : F x ≠ (⊤ : EReal) := by
      rw [hxVal]
      simp
    exact hxNotTop' hxTop

end Section24
end Chap05
