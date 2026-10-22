/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part20
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part22
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section36_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part6

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Theorem 37.4: this is the affine tilt
`K - ⟨\cdot,u^*⟩ - ⟨\cdot,v^*⟩` whose saddle points characterize
`productSubdifferentialAt K u v`. -/
noncomputable def helperForTheorem_37_4_affineTiltKernel
    (K : SaddleFunction m n) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ) :
    SaddleFunction m n :=
  fun u v =>
    K u v - (((finDot u uStar : ℝ) : EReal)) - (((finDot v vStar : ℝ) : EReal))

/-- Helper for Theorem 37.4: the first-variable partial increment is the difference of the two
corresponding dot products. -/
lemma helperForTheorem_37_4_coe_firstPartialIncrement_eq_finDot_sub
    (u : Fin m → ℝ) (u' : Fin m → ℝ) (uStar : Fin m → ℝ) :
    (((∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) =
      (((finDot u' uStar - finDot u uStar : ℝ)) : EReal) := by
  -- Expand the finite sum and regroup it into the difference of the two dot products.
  rw [EReal.coe_sub]
  -- After unfolding `finDot`, this is the usual distributivity identity for finite sums.
  simp [finDot, dotProduct, sub_eq_add_neg, left_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, add_comm, mul_comm]

/-- Helper for Theorem 37.4: the second-variable partial increment is the difference of the two
corresponding dot products. -/
lemma helperForTheorem_37_4_coe_secondPartialIncrement_eq_finDot_sub
    (v : Fin n → ℝ) (v' : Fin n → ℝ) (vStar : Fin n → ℝ) :
    (((∑ i : Fin n, vStar i * (v' i - v i) : ℝ)) : EReal) =
      (((finDot v' vStar - finDot v vStar : ℝ)) : EReal) := by
  -- Expand the finite sum and regroup it into the difference of the two dot products.
  rw [EReal.coe_sub]
  -- The second-variable formula is the same finite-sum identity with `v` in place of `u`.
  simp [finDot, dotProduct, sub_eq_add_neg, left_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, add_comm, mul_comm]

/-- Helper for Theorem 37.4: on `Fin k → ℝ`, intrinsic-interior points are also points of the
transported Euclidean relative interior. -/
lemma helperForTheorem_37_4_mem_euclideanRelativeInterior_fin_of_mem_intrinsicInterior
    {k : ℕ} {C : Set (Fin k → ℝ)} {x : Fin k → ℝ}
    (hx : x ∈ intrinsicInterior ℝ C) :
    x ∈ euclideanRelativeInterior_fin k C := by
  let e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] (Fin k → ℝ) :=
    EuclideanSpace.equiv (ι := Fin k) (𝕜 := ℝ)
  let CE : Set (EuclideanSpace ℝ (Fin k)) := e.symm '' C
  have hIntrinsic :
      intrinsicInterior ℝ C = e '' intrinsicInterior ℝ CE := by
    simpa [CE] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := CE))
  have hxImage : x ∈ e '' intrinsicInterior ℝ CE := by
    simpa [hIntrinsic] using hx
  rcases hxImage with ⟨y, hyIntrinsic, rfl⟩
  exact ⟨y, intrinsicInterior_subset_euclideanRelativeInterior k CE hyIntrinsic, rfl⟩

/-- Helper for Theorem 37.4: the `EReal` sum of coordinatewise affine products is the coercion of
the corresponding real sum. -/
lemma helperForTheorem_37_4_sumERealProducts_eq_coe_sum
    {k : ℕ} (a x y : Fin k → ℝ) :
    (∑ i : Fin k, (((a i : ℝ) : EReal) * ((((x i - y i : ℝ)) : EReal)))) =
      (((∑ i : Fin k, a i * (x i - y i) : ℝ)) : EReal) := by
  symm
  simpa [EReal.coe_mul, EReal.coe_sub] using
    (helperForTheorem_25_2_coe_finset_sum_real_toEReal
      (s := Finset.univ) (f := fun i : Fin k => a i * (x i - y i)))

/-- Helper for Theorem 37.4: the coordinatewise `EReal` products that occur after unfolding the
partial subdifferentials sum to the same coerced real affine increment. -/
lemma helperForTheorem_37_4_sumERealProducts_subtractedCoordinates_eq_coe_sum
    {k : ℕ} (a x y : Fin k → ℝ) :
    (∑ i : Fin k, (((a i : ℝ) : EReal) * (((x i : ℝ) : EReal) - (((y i : ℝ) : EReal))))) =
      (((∑ i : Fin k, a i * (x i - y i) : ℝ)) : EReal) := by
  simpa [EReal.coe_sub] using
    helperForTheorem_37_4_sumERealProducts_eq_coe_sum (a := a) (x := x) (y := y)

/-- Helper for Theorem 37.4: membership in the product subdifferential is exactly the saddle-point
condition for the affine tilt by `(uStar, vStar)`. -/
lemma helperForTheorem_37_4_mem_productSubdifferential_iff_saddlePoint_affineTilt
    (K : SaddleFunction m n)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (uStar : Fin m → ℝ) (vStar : Fin n → ℝ) :
    (uStar, vStar) ∈ productSubdifferentialAt K u v ↔
      IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
        (helperForTheorem_37_4_affineTiltKernel K uStar vStar) u v := by
  -- First rewrite the saddle-point condition as the two one-variable optimality inequalities.
  rw [helperForProposition_36_5_2_saddle_iff_split_zero_partialSubdifferentials]
  constructor
  · intro hMem
    rcases (by simpa [productSubdifferentialAt] using hMem) with ⟨huStar, hvStar⟩
    constructor
    · intro v'
      -- Convert the second partial-subgradient inequality into the tilted saddle inequality.
      have hShift :
          K u v + ((((finDot v' vStar - finDot v vStar : ℝ)) : EReal)) ≤ K u v' := by
        have hShiftRaw := hvStar v'
        have hShiftRaw' :
            K u v' ≥ K u v + (((∑ i : Fin n, vStar i * (v' i - v i) : ℝ)) : EReal) := by
          simpa [helperForTheorem_37_4_sumERealProducts_subtractedCoordinates_eq_coe_sum]
            using hShiftRaw
        rw [helperForTheorem_37_4_coe_secondPartialIncrement_eq_finDot_sub] at hShiftRaw'
        exact hShiftRaw'
      have hBase :
          K u v - (((finDot v vStar : ℝ) : EReal)) ≤
            K u v' - (((finDot v' vStar : ℝ) : EReal)) := by
        apply (EReal.le_sub_iff_add_le (Or.inl (by simp)) (Or.inl (by simp))).2
        simpa [EReal.coe_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hShift
      have hTilt :
          (K u v - (((finDot v vStar : ℝ) : EReal))) +
              (((-(finDot u uStar : ℝ)) : EReal)) ≤
            (K u v' - (((finDot v' vStar : ℝ) : EReal))) +
              (((-(finDot u uStar : ℝ)) : EReal)) :=
        (EReal.addLECancellable_coe (-(finDot u uStar : ℝ))).add_le_add_iff_right.2 hBase
      simpa [helperForTheorem_37_4_affineTiltKernel, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hTilt
    · intro u'
      -- Convert the first partial-subgradient inequality into the tilted saddle inequality.
      have hShift :
          K u' v ≤ K u v + ((((finDot u' uStar - finDot u uStar : ℝ)) : EReal)) := by
        have hShiftRaw := huStar u'
        have hShiftRaw' :
            K u' v ≤ K u v + (((∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) := by
          simpa [helperForTheorem_37_4_sumERealProducts_subtractedCoordinates_eq_coe_sum]
            using hShiftRaw
        rw [helperForTheorem_37_4_coe_firstPartialIncrement_eq_finDot_sub] at hShiftRaw'
        exact hShiftRaw'
      have hBase :
          K u' v - (((finDot u' uStar : ℝ) : EReal)) ≤
            K u v - (((finDot u uStar : ℝ) : EReal)) := by
        apply (EReal.sub_le_iff_le_add (Or.inl (by simp)) (Or.inl (by simp))).2
        simpa [EReal.coe_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hShift
      have hTilt :
          (K u' v - (((finDot u' uStar : ℝ) : EReal))) +
              (((-(finDot v vStar : ℝ)) : EReal)) ≤
            (K u v - (((finDot u uStar : ℝ) : EReal))) +
              (((-(finDot v vStar : ℝ)) : EReal)) :=
        (EReal.addLECancellable_coe (-(finDot v vStar : ℝ))).add_le_add_iff_right.2 hBase
      simpa [helperForTheorem_37_4_affineTiltKernel, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hTilt
  · intro hSaddle
    rcases hSaddle with ⟨hSecond, hFirst⟩
    -- Repackage the two affine-tilt inequalities back into the product subdifferential.
    refine (show (uStar, vStar) ∈ productSubdifferentialAt K u v from by
      simpa [productSubdifferentialAt] using
        (show uStar ∈ partialSubdifferentialInFirstVariable K u v ∧
            vStar ∈ partialSubdifferentialInSecondVariable K u v from by
      constructor
      · refine (show uStar ∈ partialSubdifferentialInFirstVariable K u v from ?_)
        intro u'
        have hTilt :
            (K u' v - (((finDot u' uStar : ℝ) : EReal))) +
                (((-(finDot v vStar : ℝ)) : EReal)) ≤
              (K u v - (((finDot u uStar : ℝ) : EReal))) +
                (((-(finDot v vStar : ℝ)) : EReal)) := by
          simpa [helperForTheorem_37_4_affineTiltKernel, sub_eq_add_neg, add_assoc,
            add_left_comm, add_comm] using hFirst u'
        have hBase :
            K u' v - (((finDot u' uStar : ℝ) : EReal)) ≤
              K u v - (((finDot u uStar : ℝ) : EReal)) := by
          exact
            (EReal.addLECancellable_coe (-(finDot v vStar : ℝ))).add_le_add_iff_right.1 hTilt
        have hShift :
            K u' v ≤ K u v + ((((finDot u' uStar - finDot u uStar : ℝ)) : EReal)) := by
          rw [EReal.sub_le_iff_le_add (Or.inl (by simp)) (Or.inl (by simp))] at hBase
          simpa [EReal.coe_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hBase
        rw [← helperForTheorem_37_4_coe_firstPartialIncrement_eq_finDot_sub] at hShift
        simpa [helperForTheorem_37_4_sumERealProducts_subtractedCoordinates_eq_coe_sum] using hShift
      · refine (show vStar ∈ partialSubdifferentialInSecondVariable K u v from ?_)
        intro v'
        have hTilt :
            (K u v - (((finDot v vStar : ℝ) : EReal))) +
                (((-(finDot u uStar : ℝ)) : EReal)) ≤
              (K u v' - (((finDot v' vStar : ℝ) : EReal))) +
                (((-(finDot u uStar : ℝ)) : EReal)) := by
          simpa [helperForTheorem_37_4_affineTiltKernel, sub_eq_add_neg, add_assoc,
            add_left_comm, add_comm] using hSecond v'
        have hBase :
            K u v - (((finDot v vStar : ℝ) : EReal)) ≤
              K u v' - (((finDot v' vStar : ℝ) : EReal)) := by
          exact
            (EReal.addLECancellable_coe (-(finDot u uStar : ℝ))).add_le_add_iff_right.1 hTilt
        have hShift :
            K u v + ((((finDot v' vStar - finDot v vStar : ℝ)) : EReal)) ≤ K u v' := by
          have hShiftBase :
              (K u v - (((finDot v vStar : ℝ) : EReal))) +
                  (((finDot v' vStar : ℝ) : EReal)) ≤
                K u v' :=
            EReal.add_le_of_le_sub hBase
          simpa [EReal.coe_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hShiftBase
        rw [← helperForTheorem_37_4_coe_secondPartialIncrement_eq_finDot_sub] at hShift
        simpa [helperForTheorem_37_4_sumERealProducts_subtractedCoordinates_eq_coe_sum] using hShift))

/-- Helper for Theorem 37.4: a closed proper saddle-function has nonempty product
subdifferential at every point of `ri (dom K)`. -/
lemma helperForTheorem_37_4_nonempty_productSubdifferential_of_mem_saddleKernelDomain
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (huv : (u, v) ∈ saddleKernelDomain K) :
    Set.Nonempty (productSubdifferentialAt K u v) := by
  rcases Set.mem_prod.mp huv with ⟨hu, hv⟩
  have hFiniteuv :
      K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := by
    constructor
    · -- Relative-interior points belong to `dom₂ K`, so the base value avoids `⊤`.
      exact lt_top_iff_ne_top.mp ((intrinsicInterior_subset (𝕜 := ℝ) (s := effectiveDomain₂ K) hv) u)
    · -- Relative-interior points belong to `dom₁ K`, so the base value avoids `⊥`.
      exact bot_lt_iff_ne_bot.mp ((intrinsicInterior_subset (𝕜 := ℝ) (s := effectiveDomain₁ K) hu) v)
  have hSecondProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (K u) :=
    helperForTheorem_37_2_convexSlice_properOn_univ
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu
  have hSecondDomain :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u) = effectiveDomain₂ K := by
    have hSlice :=
      helperForTheorem_37_2_convexSlice_on_intrinsicInterior
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu
    -- The Section 37.2 slice package identifies the slice effective domain with `dom₂ K`.
    simpa [convexFunctionEffectiveDomain, effectiveDomain_eq] using hSlice.2.2.2
  have hvri :
      v ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u)) := by
    -- Rewrite `ri (dom₂ K)` into the Chapter 23 relative-interior convention on the slice domain.
    have hvriDom :
        v ∈ euclideanRelativeInterior_fin n (effectiveDomain₂ K) := by
      exact
        helperForTheorem_37_4_mem_euclideanRelativeInterior_fin_of_mem_intrinsicInterior
          (C := effectiveDomain₂ K) hv
    simpa [hSecondDomain] using hvriDom
  have hSecondSubEff :
      v ∈ subdifferentialEffectiveDomain (K u) :=
    helperForRemark_5_24_1_subdifferentiable_of_mem_relativeInterior
      (f := K u) hSecondProper hvri
  have hSecondSub :
      Set.Nonempty (subdifferentialAt (K u) v) :=
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty (K u) v).1
      hSecondSubEff
  rcases hSecondSub with ⟨vDual, hvDual⟩
  let vStar : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm vDual
  have hvDual' : dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt (K u) v := by
    -- Re-express the dual witness in coordinate-vector form before switching to partials.
    simpa [vStar] using hvDual
  have hvStarMem : vStar ∈ partialSubdifferentialInSecondVariable K u v := by
    -- Translate the Chapter 23 slice subgradient back to the textbook second partial.
    simpa [vStar] using
      (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
        (K := K) (u := u) (v := v) (vStar := vStar)).1 hvDual'
  have hFirstProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun u' => -K u' v) :=
    helperForTheorem_37_2_negatedFirstSlice_properOn_univ
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hv
  have hFirstDomain :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u' => -K u' v) = effectiveDomain₁ K := by
    have hSlice :=
      helperForTheorem_37_2_negatedFirstSlice_on_intrinsicInterior
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hv
    -- The negated first-slice package identifies its effective domain with `dom₁ K`.
    simpa [convexFunctionEffectiveDomain, effectiveDomain_eq] using hSlice.2.2.2
  have huri :
      u ∈ euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u' => -K u' v)) := by
    -- Rewrite `ri (dom₁ K)` into the Chapter 23 relative-interior convention on the negated slice.
    have huriDom :
        u ∈ euclideanRelativeInterior_fin m (effectiveDomain₁ K) := by
      exact
        helperForTheorem_37_4_mem_euclideanRelativeInterior_fin_of_mem_intrinsicInterior
          (C := effectiveDomain₁ K) hu
    simpa [hFirstDomain] using huriDom
  have hFirstSubEff :
      u ∈ subdifferentialEffectiveDomain (fun u' => -K u' v) :=
    helperForRemark_5_24_1_subdifferentiable_of_mem_relativeInterior
      (f := fun u' => -K u' v) hFirstProper huri
  have hFirstSub :
      Set.Nonempty (subdifferentialAt (fun u' => -K u' v) u) :=
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
      (fun u' => -K u' v) u).1 hFirstSubEff
  rcases hFirstSub with ⟨uDual, huDual⟩
  let uStar : Fin m → ℝ := -(dotProductEquiv ℝ (Fin m)).symm uDual
  have huStarSub :
      IsSubgradientAt (fun x : Fin m → ℝ => -K x v) u
        (dotProductEquiv ℝ (Fin m) (-uStar)) := by
    -- Choose the vector representative so that the dual covector is exactly `dotProductEquiv (-uStar)`.
    simpa [uStar] using huDual
  have huStarMem : uStar ∈ partialSubdifferentialInFirstVariable K u v := by
    -- Convert the slice subgradient into the textbook first partial-subgradient inequality.
    exact
      (helperForCorollary_35_8_1_negFirstSliceSubgradient_iff_partialFirstMem
        (K := K) (u := u) (v := v) hFiniteuv uStar).1 huStarSub
  -- Package the two slice witnesses into one witness for the product subdifferential.
  exact ⟨(uStar, vStar), by simpa [productSubdifferentialAt] using And.intro huStarMem hvStarMem⟩

/-- Helper for Theorem 37.4: for a proper saddle-function, any nonempty product subdifferential
can only occur on `dom K = dom₁ K × dom₂ K`. -/
lemma helperForTheorem_37_4_mem_saddleEffectiveDomain_of_nonempty_productSubdifferential
    (K : SaddleFunction m n)
    (hKproper : IsProperSaddleFunction K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hSub : Set.Nonempty (productSubdifferentialAt K u v)) :
    (u, v) ∈ saddleEffectiveDomain K := by
  rcases helperForTheorem_37_2_firstDomain_nonempty (K := K) hKproper with ⟨u0, hu0⟩
  rcases helperForTheorem_37_2_secondDomain_nonempty (K := K) hKproper with ⟨v0, hv0⟩
  rcases hSub with ⟨⟨uStar, vStar⟩, hMem⟩
  rcases (by simpa [productSubdifferentialAt] using hMem) with ⟨huStarMem, hvStarMem⟩
  have hBaseNotBot : K u v ≠ (⊥ : EReal) := by
    intro hBot
    have hAtu0 :
        K u0 v ≤ K u v + (((∑ i : Fin m, uStar i * (u0 i - u i) : ℝ)) : EReal) := by
      simpa [helperForTheorem_25_2_coe_finset_sum_real_toEReal] using huStarMem u0
    have hBotBound : K u0 v ≤ (⊥ : EReal) := by
      simpa [hBot] using hAtu0
    exact (not_le_of_gt (hu0 v)) hBotBound
  have hBaseNotTop : K u v ≠ (⊤ : EReal) := by
    intro hTop
    have hAtv0 :
        K u v0 ≥ K u v + (((∑ i : Fin n, vStar i * (v0 i - v i) : ℝ)) : EReal) := by
      simpa [helperForTheorem_25_2_coe_finset_sum_real_toEReal] using hvStarMem v0
    have hTopBound : (⊤ : EReal) ≤ K u v0 := by
      simpa [hTop] using hAtv0
    exact (not_le_of_gt (hv0 u)) hTopBound
  have huEff : u ∈ effectiveDomain₁ K := by
    intro v'
    have hAtv' :
        K u v' ≥ K u v + (((∑ i : Fin n, vStar i * (v' i - v i) : ℝ)) : EReal) := by
      simpa [helperForTheorem_25_2_coe_finset_sum_real_toEReal] using hvStarMem v'
    have hBaseCoe : (((K u v).toReal : ℝ) : EReal) = K u v := by
      exact EReal.coe_toReal (x := K u v) hBaseNotTop hBaseNotBot
    have hLowerFinite :
        (⊥ : EReal) < K u v + (((∑ i : Fin n, vStar i * (v' i - v i) : ℝ)) : EReal) := by
      rw [← hBaseCoe]
      rw [← EReal.coe_add]
      simp
    -- The right-hand side dominates a finite real number, so it lies strictly above `⊥`.
    exact lt_of_lt_of_le hLowerFinite hAtv'
  have hvEff : v ∈ effectiveDomain₂ K := by
    intro u'
    have hAtu' :
        K u' v ≤ K u v + (((∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) := by
      simpa [helperForTheorem_25_2_coe_finset_sum_real_toEReal] using huStarMem u'
    have hBaseCoe : (((K u v).toReal : ℝ) : EReal) = K u v := by
      exact EReal.coe_toReal (x := K u v) hBaseNotTop hBaseNotBot
    have hUpperFinite :
        K u v + (((∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) < (⊤ : EReal) := by
      rw [← hBaseCoe]
      apply lt_top_iff_ne_top.mpr
      intro hTop
      have hAdd :
          (((K u v).toReal : ℝ) : EReal) +
              (((∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) =
            ((((K u v).toReal + ∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) := by
        simpa using (EReal.coe_add (K u v).toReal (∑ i : Fin m, uStar i * (u' i - u i)))
      have hTop' :
          ((((K u v).toReal + ∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) = (⊤ : EReal) := by
        calc
          ((((K u v).toReal + ∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) =
              (((K u v).toReal : ℝ) : EReal) +
                (((∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) := hAdd.symm
          _ = (⊤ : EReal) := hTop
      exact EReal.coe_ne_top _ hTop'
    -- The left-hand side is bounded above by a finite real number, so it lies strictly below `⊤`.
    exact lt_of_le_of_lt hAtu' hUpperFinite
  exact ⟨huEff, hvEff⟩

/-- Theorem 37.4: a pair `(uStar, vStar)` lies in `∂K(u, v)` exactly when the affine tilt
`K - ⟨\cdot,u^*⟩ - ⟨\cdot,v^*⟩` has `(u, v)` as a saddle point; for closed proper `K` one has
`ri (dom K) ⊆ dom ∂K ⊆ dom K`. -/
theorem section37_theorem37_4
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    (∀ u v uStar vStar,
        (uStar, vStar) ∈ productSubdifferentialAt K u v ↔
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
            (helperForTheorem_37_4_affineTiltKernel K uStar vStar) u v) ∧
      saddleKernelDomain K ⊆ {p | Set.Nonempty (productSubdifferentialAt K p.1 p.2)} ∧
      {p | Set.Nonempty (productSubdifferentialAt K p.1 p.2)} ⊆ saddleEffectiveDomain K := by
  constructor
  · intro u v uStar vStar
    -- The characterization clause is exactly the affine-tilt helper.
    exact
      helperForTheorem_37_4_mem_productSubdifferential_iff_saddlePoint_affineTilt
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
  constructor
  · intro p hp
    -- On `ri (dom K)`, Section 37.2 and Chapter 23 produce both partial subdifferentials.
    exact
      helperForTheorem_37_4_nonempty_productSubdifferential_of_mem_saddleKernelDomain
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hp
  · intro p hp
    -- Any nonempty product subdifferential forces the base point back into `dom K`.
    exact
      helperForTheorem_37_4_mem_saddleEffectiveDomain_of_nonempty_productSubdifferential
        (K := K) (hKproper := hKproper) hp

/-- Helper for Corollary 37.4.1: equivalence of saddle-functions is symmetric. -/
lemma helperForCorollary_37_4_1_equivalentSaddleFunctions_symm
    {K L : SaddleFunction m n}
    (hKL : EquivalentSaddleFunctions K L) :
    EquivalentSaddleFunctions L K := by
  rcases hKL with ⟨hKbdry, hLbdry, hDom1, hDom2, hAgree⟩
  refine ⟨hLbdry, hKbdry, hDom1.symm, hDom2.symm, ?_⟩
  intro u v hu hv
  -- Transport the common-domain equality back through the shared domain identities.
  exact
    (hAgree u v (by simpa [hDom1] using hu) (by simpa [hDom2] using hv)).symm

/-- Helper for Corollary 37.4.1: a saddle point of the affine tilt can occur only at a point of
the original common saddle domain. -/
lemma helperForCorollary_37_4_1_mem_originalSaddleDom_of_isSaddlePoint_affineTilt
    {K L : SaddleFunction m n}
    (hKL : EquivalentSaddleFunctions K L)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hSaddle :
      IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
        (helperForTheorem_37_4_affineTiltKernel K uStar vStar) u v) :
    u ∈ saddleDom1 K ∧ v ∈ saddleDom2 K := by
  rcases hKL with ⟨hKbdry, -, -, -, -⟩
  rcases hKbdry with ⟨hDom1NE, hDom2NE, hBotStrip, hTopStrip⟩
  rcases hDom1NE with ⟨u0, hu0⟩
  rcases hDom2NE with ⟨v0, hv0⟩
  rcases hSaddle with ⟨hLeft, hRight⟩
  constructor
  · by_contra hu
    have hCenterBot :
        helperForTheorem_37_4_affineTiltKernel K uStar vStar u v = (⊥ : EReal) := by
      have hAtv0 :
          helperForTheorem_37_4_affineTiltKernel K uStar vStar u v ≤
            helperForTheorem_37_4_affineTiltKernel K uStar vStar u v0 :=
        hRight v0
      -- Outside `dom₁ K`, the `v0`-column is forced to `-∞`, so the tilted value is also `-∞`.
      refine le_antisymm ?_ bot_le
      simpa [helperForTheorem_37_4_affineTiltKernel, hBotStrip u v0 hu hv0] using hAtv0
    have hAtu0 :
        helperForTheorem_37_4_affineTiltKernel K uStar vStar u0 v ≤
          helperForTheorem_37_4_affineTiltKernel K uStar vStar u v :=
      hLeft u0
    have hKu0v :
        (⊥ : EReal) < K u0 v :=
      lt_of_lt_of_le hu0 (iInf_le (fun v' : Fin n → ℝ => K u0 v') v)
    have hTiltu0v :
        (⊥ : EReal) <
          helperForTheorem_37_4_affineTiltKernel K uStar vStar u0 v := by
      -- Subtracting finite affine terms preserves strict inequality with `-∞`.
      have hShift :=
        (section13_addRightOrderIso (-(finDot u0 uStar + finDot v vStar : ℝ))).strictMono hKu0v
      simpa [section13_addRightOrderIso, helperForTheorem_37_4_affineTiltKernel, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm, EReal.coe_add] using hShift
    have hContra : (⊥ : EReal) < (⊥ : EReal) := by
      exact lt_of_lt_of_le hTiltu0v (by simpa [hCenterBot] using hAtu0)
    exact (lt_irrefl (⊥ : EReal)) hContra
  · by_contra hv
    have hAtu0 :
        helperForTheorem_37_4_affineTiltKernel K uStar vStar u0 v ≤
          helperForTheorem_37_4_affineTiltKernel K uStar vStar u v :=
      hLeft u0
    have hCenterTop :
        helperForTheorem_37_4_affineTiltKernel K uStar vStar u v = (⊤ : EReal) := by
      -- Outside `dom₂ K`, the `u0`-row is forced to `+∞`, so the center must also be `+∞`.
      refine le_antisymm le_top ?_
      simpa [helperForTheorem_37_4_affineTiltKernel, hTopStrip u0 v hu0 hv] using hAtu0
    have hKuv0 :
        K u v0 < (⊤ : EReal) :=
      lt_of_le_of_lt (le_iSup (fun u' : Fin m → ℝ => K u' v0) u) hv0
    have hTiltuv0 :
        helperForTheorem_37_4_affineTiltKernel K uStar vStar u v0 < (⊤ : EReal) := by
      -- Subtracting finite affine terms preserves strict inequality with `+∞`.
      have hShift :=
        (section13_addRightOrderIso (-(finDot u uStar + finDot v0 vStar : ℝ))).strictMono hKuv0
      simpa [section13_addRightOrderIso, helperForTheorem_37_4_affineTiltKernel, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm, EReal.coe_add] using hShift
    have hAtv0 :
        helperForTheorem_37_4_affineTiltKernel K uStar vStar u v ≤
          helperForTheorem_37_4_affineTiltKernel K uStar vStar u v0 :=
      hRight v0
    have hContra : (⊤ : EReal) < (⊤ : EReal) := by
      exact lt_of_le_of_lt (by simpa [hCenterTop] using hAtv0) hTiltuv0
    exact (lt_irrefl (⊤ : EReal)) hContra

/-- Helper for Corollary 37.4.1: once the second coordinate lies in the common saddle domain,
the affine tilts of equivalent saddle-functions agree on the whole corresponding row. -/
lemma helperForCorollary_37_4_1_affineTilt_eq_on_row_of_mem_saddleDom2
    {K L : SaddleFunction m n}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hKL : EquivalentSaddleFunctions K L)
    {v : Fin n → ℝ} (hv : v ∈ saddleDom2 K) :
    ∀ u : Fin m → ℝ,
      helperForTheorem_37_4_affineTiltKernel K uStar vStar u v =
        helperForTheorem_37_4_affineTiltKernel L uStar vStar u v := by
  rcases hKL with ⟨hKbdry, hLbdry, hDom1, hDom2, hAgree⟩
  rcases hKbdry with ⟨-, -, hKbot, -⟩
  rcases hLbdry with ⟨-, -, hLbot, -⟩
  have hvL : v ∈ saddleDom2 L := by
    simpa [hDom2] using hv
  intro u
  by_cases hu : u ∈ saddleDom1 K
  · -- On the common saddle domain, the original kernels agree pointwise.
    simpa [helperForTheorem_37_4_affineTiltKernel, hAgree u v hu hv]
  · have huL : u ∉ saddleDom1 L := by
      simpa [hDom1] using hu
    -- Off the first saddle domain, both kernels take the same forced `-∞` value.
    simpa [helperForTheorem_37_4_affineTiltKernel, hKbot u v hu hv, hLbot u v huL hvL]

/-- Helper for Corollary 37.4.1: once the first coordinate lies in the common saddle domain,
the affine tilts of equivalent saddle-functions agree on the whole corresponding column. -/
lemma helperForCorollary_37_4_1_affineTilt_eq_on_col_of_mem_saddleDom1
    {K L : SaddleFunction m n}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hKL : EquivalentSaddleFunctions K L)
    {u : Fin m → ℝ} (hu : u ∈ saddleDom1 K) :
    ∀ v : Fin n → ℝ,
      helperForTheorem_37_4_affineTiltKernel K uStar vStar u v =
        helperForTheorem_37_4_affineTiltKernel L uStar vStar u v := by
  rcases hKL with ⟨hKbdry, hLbdry, hDom1, hDom2, hAgree⟩
  rcases hKbdry with ⟨-, -, -, hKtop⟩
  rcases hLbdry with ⟨-, -, -, hLtop⟩
  have huL : u ∈ saddleDom1 L := by
    simpa [hDom1] using hu
  intro v
  by_cases hv : v ∈ saddleDom2 K
  · -- On the common saddle domain, the original kernels agree pointwise.
    simpa [helperForTheorem_37_4_affineTiltKernel, hAgree u v hu hv]
  · have hvL : v ∉ saddleDom2 L := by
      simpa [hDom2] using hv
    -- Off the second saddle domain, both kernels take the same forced `+∞` value.
    simpa [helperForTheorem_37_4_affineTiltKernel, hKtop u v hu hv, hLtop u v huL hvL]

/-- Helper for Corollary 37.4.1: if one affine tilt has a saddle point at `(u,v)`, the
corresponding affine tilt of an equivalent saddle-function has the same saddle point. -/
lemma helperForCorollary_37_4_1_saddlePoint_affineTilt_transport
    {K L : SaddleFunction m n}
    (hKL : EquivalentSaddleFunctions K L)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hSaddle :
      IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
        (helperForTheorem_37_4_affineTiltKernel K uStar vStar) u v) :
    IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
      (helperForTheorem_37_4_affineTiltKernel L uStar vStar) u v := by
  obtain ⟨hu, hv⟩ :=
    helperForCorollary_37_4_1_mem_originalSaddleDom_of_isSaddlePoint_affineTilt
      (hKL := hKL) hSaddle
  rcases hSaddle with ⟨hLeft, hRight⟩
  refine ⟨?_, ?_⟩
  · intro u'
    -- The entire `v`-row agrees between the two affine tilts, so the left saddle inequality transports.
    calc
      helperForTheorem_37_4_affineTiltKernel L uStar vStar u' v =
          helperForTheorem_37_4_affineTiltKernel K uStar vStar u' v := by
            symm
            exact
              helperForCorollary_37_4_1_affineTilt_eq_on_row_of_mem_saddleDom2
                (hKL := hKL) (hv := hv) u'
      _ ≤ helperForTheorem_37_4_affineTiltKernel K uStar vStar u v := hLeft u'
      _ = helperForTheorem_37_4_affineTiltKernel L uStar vStar u v := by
            exact
              helperForCorollary_37_4_1_affineTilt_eq_on_row_of_mem_saddleDom2
                (hKL := hKL) (hv := hv) u
  · intro v'
    -- The entire `u`-column agrees between the two affine tilts, so the right saddle inequality transports.
    calc
      helperForTheorem_37_4_affineTiltKernel L uStar vStar u v =
          helperForTheorem_37_4_affineTiltKernel K uStar vStar u v := by
            symm
            exact
              helperForCorollary_37_4_1_affineTilt_eq_on_col_of_mem_saddleDom1
                (hKL := hKL) (hu := hu) v
      _ ≤ helperForTheorem_37_4_affineTiltKernel K uStar vStar u v' := hRight v'
      _ = helperForTheorem_37_4_affineTiltKernel L uStar vStar u v' := by
            exact
              helperForCorollary_37_4_1_affineTilt_eq_on_col_of_mem_saddleDom1
                (hKL := hKL) (hu := hu) v'

/-- Helper for Corollary 37.4.1: the affine-tilt saddle-point predicate is identical for
equivalent saddle-functions. -/
lemma helperForCorollary_37_4_1_saddlePoint_affineTilt_iff_of_equivalentSaddleFunctions
    {K L : SaddleFunction m n}
    (hKL : EquivalentSaddleFunctions K L)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (uStar : Fin m → ℝ) (vStar : Fin n → ℝ) :
    IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
        (helperForTheorem_37_4_affineTiltKernel K uStar vStar) u v ↔
      IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
        (helperForTheorem_37_4_affineTiltKernel L uStar vStar) u v := by
  constructor
  · intro hSaddle
    -- Transport the saddle point forward using row- and columnwise equality on the common saddle domain.
    exact
      helperForCorollary_37_4_1_saddlePoint_affineTilt_transport
        (hKL := hKL) hSaddle
  · intro hSaddle
    -- The reverse implication is the same argument applied to the symmetric equivalence.
    exact
      helperForCorollary_37_4_1_saddlePoint_affineTilt_transport
        (K := L) (L := K)
        (hKL := helperForCorollary_37_4_1_equivalentSaddleFunctions_symm hKL) hSaddle

/-- Helper for Corollary 37.4.1: equivalent saddle-functions have the same product
subdifferential at every point. -/
lemma helperForCorollary_37_4_1_productSubdifferential_eq_of_equivalentSaddleFunctions
    {K L : SaddleFunction m n}
    (hKL : EquivalentSaddleFunctions K L) :
    ∀ u v, productSubdifferentialAt K u v = productSubdifferentialAt L u v := by
  intro u v
  ext g
  rcases g with ⟨uStar, vStar⟩
  constructor
  · intro hMem
    have hSaddleK :
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
          (helperForTheorem_37_4_affineTiltKernel K uStar vStar) u v :=
      (helperForTheorem_37_4_mem_productSubdifferential_iff_saddlePoint_affineTilt
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)).1 hMem
    have hSaddleL :
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
          (helperForTheorem_37_4_affineTiltKernel L uStar vStar) u v :=
      (helperForCorollary_37_4_1_saddlePoint_affineTilt_iff_of_equivalentSaddleFunctions
        (hKL := hKL) (u := u) (v := v) (uStar := uStar) (vStar := vStar)).1 hSaddleK
    -- Convert the transported saddle point back into product-subdifferential membership.
    exact
      (helperForTheorem_37_4_mem_productSubdifferential_iff_saddlePoint_affineTilt
        (K := L) (u := u) (v := v) (uStar := uStar) (vStar := vStar)).2 hSaddleL
  · intro hMem
    have hSaddleL :
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
          (helperForTheorem_37_4_affineTiltKernel L uStar vStar) u v :=
      (helperForTheorem_37_4_mem_productSubdifferential_iff_saddlePoint_affineTilt
        (K := L) (u := u) (v := v) (uStar := uStar) (vStar := vStar)).1 hMem
    have hSaddleK :
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
          (helperForTheorem_37_4_affineTiltKernel K uStar vStar) u v :=
      (helperForCorollary_37_4_1_saddlePoint_affineTilt_iff_of_equivalentSaddleFunctions
        (hKL := hKL) (u := u) (v := v) (uStar := uStar) (vStar := vStar)).2 hSaddleL
    -- Convert the transported saddle point back into product-subdifferential membership.
    exact
      (helperForTheorem_37_4_mem_productSubdifferential_iff_saddlePoint_affineTilt
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)).2 hSaddleK

/-- Helper for Corollary 37.4.1: on every point where the product subdifferential is nonempty,
equivalent saddle-functions already agree in value. -/
lemma helperForCorollary_37_4_1_value_eq_on_productSubdifferentialDomain
    {K L : SaddleFunction m n}
    (hKL : EquivalentSaddleFunctions K L) :
    ∀ u v, Set.Nonempty (productSubdifferentialAt K u v) → K u v = L u v := by
  rcases hKL with ⟨hKbdry, hLbdry, hDom1, hDom2, hAgree⟩
  intro u v hSub
  rcases hSub with ⟨⟨uStar, vStar⟩, hMem⟩
  have hSaddle :
      IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
        (helperForTheorem_37_4_affineTiltKernel K uStar vStar) u v :=
    (helperForTheorem_37_4_mem_productSubdifferential_iff_saddlePoint_affineTilt
      (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)).1 hMem
  obtain ⟨hu, hv⟩ :=
    helperForCorollary_37_4_1_mem_originalSaddleDom_of_isSaddlePoint_affineTilt
      (hKL := ⟨hKbdry, hLbdry, hDom1, hDom2, hAgree⟩) hSaddle
  -- Once the base point lies in the common saddle domain, value equality is part of equivalence.
  exact hAgree u v hu hv

/-- Corollary 37.4.1: equivalent saddle-functions have the same product subdifferential, and
their values agree on the common domain where this product subdifferential is nonempty. -/
theorem corollary37_4_1_equivalentSaddleFunctions_have_same_productSubdifferential
    {K L : SaddleFunction m n}
    (hKL : EquivalentSaddleFunctions K L) :
    (∀ u v, productSubdifferentialAt K u v = productSubdifferentialAt L u v) ∧
      ({p : (Fin m → ℝ) × (Fin n → ℝ) |
          Set.Nonempty (productSubdifferentialAt K p.1 p.2)} =
        {p : (Fin m → ℝ) × (Fin n → ℝ) |
          Set.Nonempty (productSubdifferentialAt L p.1 p.2)}) ∧
      (∀ u v, Set.Nonempty (productSubdifferentialAt K u v) → K u v = L u v) := by
  have hSubEq :
      ∀ u v, productSubdifferentialAt K u v = productSubdifferentialAt L u v :=
    helperForCorollary_37_4_1_productSubdifferential_eq_of_equivalentSaddleFunctions
      (hKL := hKL)
  constructor
  · -- The first clause is the pointwise equality `∂K(u,v) = ∂L(u,v)`.
    exact hSubEq
  constructor
  · ext p
    constructor
    · rintro ⟨g, hg⟩
      -- Rewrite the witness through the already-proved pointwise equality of the product subdifferentials.
      exact ⟨g, by simpa [hSubEq p.1 p.2] using hg⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, by simpa [hSubEq p.1 p.2] using hg⟩
  · -- On the common subdifferential domain, value equality follows from membership in the common saddle domain.
    exact
      helperForCorollary_37_4_1_value_eq_on_productSubdifferentialDomain
        (hKL := hKL)

/-- Helper for Corollary 37.5.1: the graph of the product subdifferential of `K`, written in the
four-block coordinates `(u, v, uStar, vStar)`. -/
def helperForCorollary_37_5_1_productSubdifferentialGraph
    (K : SaddleFunction m n) :
    Set (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) :=
  {p | p.2 ∈ productSubdifferentialAt K p.1.1 p.1.2}

/-- Helper for Corollary 37.5.1: the textbook map sending a graph point
`(u, v, uStar, vStar)` to `(u - uStar, v + vStar)`. -/
def helperForCorollary_37_5_1_bookMap :
    (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) →
      ((Fin m → ℝ) × (Fin n → ℝ)) :=
  fun p => (p.1.1 - p.2.1, p.1.2 + p.2.2)

/-- Helper for Corollary 37.5.1: after packing the primal variables with `Fin.append`, the
textbook map becomes the packed addition map with the first dual block sign-twisted. -/
lemma helperForCorollary_37_5_1_appendHomeomorph_bookMap_eq_packedAddition
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ) :
    (Fin.appendHomeomorph (X := ℝ) m n)
        (helperForCorollary_37_5_1_bookMap (((u, v), (uStar, vStar)))) =
      Fin.append u v + Fin.append (-uStar) vStar := by
  -- Check the identity blockwise: the first coordinates subtract `uStar`, while the second
  -- coordinates add `vStar`.
  ext i
  by_cases hi : i.1 < m
  · simp [helperForCorollary_37_5_1_bookMap, Fin.appendHomeomorph, Fin.append, Fin.addCases, hi,
      sub_eq_add_neg]
  · simp [helperForCorollary_37_5_1_bookMap, Fin.appendHomeomorph, Fin.append, Fin.addCases, hi,
      sub_eq_add_neg]

/-- Helper for Corollary 37.5.1: unpacking the packed addition map recovers exactly the textbook
map `(u - uStar, v + vStar)`. -/
lemma helperForCorollary_37_5_1_bookMap_eq_appendHomeomorph_symm_packedAddition
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ) :
    helperForCorollary_37_5_1_bookMap (((u, v), (uStar, vStar))) =
      (Fin.appendHomeomorph (X := ℝ) m n).symm (Fin.append u v + Fin.append (-uStar) vStar) := by
  -- Apply the inverse of `Fin.appendHomeomorph` to the already-proved packed identity.
  apply (Fin.appendHomeomorph (X := ℝ) m n).injective
  rw [(Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply]
  exact
    helperForCorollary_37_5_1_appendHomeomorph_bookMap_eq_packedAddition
      (u := u) (v := v) (uStar := uStar) (vStar := vStar)

/-- Helper for Corollary 37.5.1: package the four-block graph coordinates
`(u, v, uStar, vStar)` into the corrected packed coordinates
`((u, vStar), (-uStar, v))`. -/
def helperForCorollary_37_5_1_packGraphCoordinates :
    (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) →
      ((Fin (m + n) → ℝ) × (Fin (m + n) → ℝ)) :=
  fun p => (Fin.append p.1.1 p.2.2, Fin.append (-p.2.1) p.1.2)

/-- Helper for Corollary 37.5.1: this is the ordinary subdifferential graph of the packed graph
function attached to a convex bifunction. -/
def helperForCorollary_37_5_1_packedSubdifferentialGraph
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    Set ((Fin (m + n) → ℝ) × (Fin (m + n) → ℝ)) :=
  {q | dotProductEquiv ℝ (Fin (m + n)) q.2 ∈ subdifferentialAt (graphFunctionOfBifunction F) q.1}

/-- Helper for Corollary 37.5.1: the packed coordinate swap/sign map is continuous, so closedness
can be transported by preimages once the graph-bridge is known. -/
lemma helperForCorollary_37_5_1_packGraphCoordinates_continuous :
    Continuous (helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n)) := by
  -- Each packed block is `Fin.append` composed with a continuous projection/sign-change map.
  have hFirst :
      Continuous
        (fun p :
          (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) =>
            Fin.append p.1.1 p.2.2) := by
    have hBase :
        Continuous
          (fun p :
            (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) =>
              (p.1.1, p.2.2)) := by
      fun_prop
    exact (Fin.appendHomeomorph (X := ℝ) m n).continuous_toFun.comp hBase
  have hSecond :
      Continuous
        (fun p :
          (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) =>
            Fin.append (-p.2.1) p.1.2) := by
    have hBase :
        Continuous
          (fun p :
            (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) =>
              (-p.2.1, p.1.2)) := by
      fun_prop
    exact (Fin.appendHomeomorph (X := ℝ) m n).continuous_toFun.comp hBase
  exact hFirst.prodMk hSecond

/-- Helper for Corollary 37.5.1: a closed proper convex bifunction gives a closed proper packed
convex graph function on `ℝ^(m+n)`. -/
lemma helperForCorollary_37_5_1_graphFunction_properConvex
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (hFproper : IsProperConvexBifunction F) :
    ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
      (graphFunctionOfBifunction F) := by
  have hF_closed := hF
  rcases hF with ⟨_, hNoBotF, _⟩
  rcases hFproper with ⟨_, hDomainNonempty⟩
  have hGraphConv :
      ConvexFunction (graphFunctionOfBifunction F) :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction
      (by
        have hGraphConvex : IsGraphConvexBifunction F :=
          helperForCorollary_37_1_1_closedConvex_isGraphConvex (F := F) (hF := hF_closed)
        simpa [IsGraphConvexBifunction] using hGraphConvex)
  refine ⟨?_, ?_, ?_⟩
  · -- The graph function is convex on all of `ℝ^(m+n)` because the representative is graph-convex.
    simpa [ConvexFunctionOn] using hGraphConv
  · rcases hDomainNonempty with ⟨u₀, x₀, hx₀⟩
    let z₀ : Fin (m + n) → ℝ := Fin.append u₀ x₀
    have hz₀Dom :
        z₀ ∈ effectiveDomain
          (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
      rw [effectiveDomain_eq]
      refine ⟨by simp [z₀], ?_⟩
      simpa [z₀, graphFunctionOfBifunction] using hx₀
    exact
      (nonempty_epigraph_iff_nonempty_effectiveDomain
        (S := (Set.univ : Set (Fin (m + n) → ℝ))) (f := graphFunctionOfBifunction F)).2
        ⟨z₀, hz₀Dom⟩
  · intro z _hz
    -- The graph function inherits the no-`⊥` convention coordinatewise from `F`.
    simpa [graphFunctionOfBifunction] using
      hNoBotF (fun i : Fin m => z (Fin.castAdd n i))
        (fun j : Fin n => z (Fin.natAdd m j))

/-- Explicit infinite-value qualification needed by the canonical Section 34 witness route used
to recover a graph-closed convex representative. -/
def Section37ClosedRepresentativeQualification
    (K : SaddleFunction m n) (hKclosed : IsClosedSaddleFunction K) : Prop :=
  HasNoBotValuesBifunction K ∧
    HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K hKclosed.1.1)

/-- Helper for Corollary 37.5.1: a closed proper saddle-function admits a representative that is
closed in the Chapter 6 graph-function sense as well as proper in the Section 34 image-closed
sense. -/
lemma helperForCorollary_37_5_1_closedProperRepresentativeWithClosedWitness
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hRepresentative : Section37ClosedRepresentativeQualification K hKclosed)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      ∃ hF : IsClosedConvexBifunction F,
        ClosedConvexBifunction F ∧
          IsProperConvexBifunction F ∧
            K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩ := by
  -- Reuse the mixed-closure formulas that identify a closed saddle-function with its lower
  -- representative in the Section 34 equivalence class.
  have hKcc : IsConcaveConvex K := hKclosed.1.1
  have hKclosedCharacterization :
      partialClosure₁ (partialClosure₂ K) = partialClosure₁ K ∧
        partialClosure₂ (partialClosure₁ K) = partialClosure₂ K :=
    helperForText_34_1_9_mixedClosureIdentities_of_isClosed hKclosed
  rcases helperForText_34_0_1_mixedClosure_formulas K hKcc with
    ⟨hLowerFormula, hUpperFormula⟩
  have hKLowerEquiv :
      saddleEquivalent K (lowerClosureConcaveConvex K hKcc) := by
    -- Closedness collapses the mixed lower closure back to the original saddle-function.
    simpa [hLowerFormula, hKclosedCharacterization.2] using hKclosed.2
  rcases helperForText_34_1_4_closedConvexWitness_exists_for_canonicalUpperPartner
      K hKcc hRepresentative.1 hRepresentative.2 hGlobal.canonicalClosureRealization with
    ⟨F, hClosed, hNoBot, hLowerRep, _hUpperRep⟩
  have hRock : IsRockafellarConvexBifunction F :=
    helperForLemma33_0_22_graphConvex_gives_rockafellarConvex
      (helperForCorollary33_3_1_rockafellarConvex_and_graphFunctionClosed_of_closedConvexWitness
        (F := F) hClosed hNoBot).1
  have hGraphClosed :
      IsFunctionConvexClosed (graphFunctionOfBifunction F) :=
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
      (f := graphFunctionOfBifunction F) (by simpa [bifunctionGraphFunction, graphFunctionOfBifunction]
        using hClosed.2.2)
  have hF : IsClosedConvexBifunction F := by
    -- Package the closed-graph witness into the weaker image-closed API used by Section 37.
    refine ⟨hRock, hNoBot, ?_⟩
    exact helperForLemma33_0_22_section_isFunctionConvexClosed hGraphClosed
  have hKGenerated :
      K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩ := by
    -- Once the lower closure is rewritten as the canonical pairing, equivalence is exactly
    -- generated-class membership.
    simpa [EquivalenceClassGeneratedByConvexBifunction, convexBifunctionClosedKernel, hLowerRep]
      using hKLowerEquiv
  have hPairingProper :
      IsProperSaddleFunction (convexBifunctionPairing F) := by
    -- Closed equivalent saddle-functions have the same saddle effective domain.
    have hSameDomain :
        saddleEffectiveDomain (convexBifunctionPairing F) = saddleEffectiveDomain K :=
      (closed_equivalent_saddle_functions_have_same_domain_and_agree_on_relativeInterior
        (K := K) (L := convexBifunctionPairing F) hKclosed
        (by simpa [hLowerRep] using hKLowerEquiv) hGlobal).1
    simpa [IsProperSaddleFunction, hSameDomain] using hKproper
  have hPairingDomainNonempty :
      (saddleEffectiveDomain (convexBifunctionPairing F)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hPairingProper
  rcases hPairingDomainNonempty with ⟨⟨u₀, xStar₀⟩, hu₀xStar₀⟩
  have hu₀ : u₀ ∈ effectiveDomain₁ (convexBifunctionPairing F) :=
    (Set.mem_prod.mp hu₀xStar₀).1
  have hFiniteSection : ∃ x : Fin n → ℝ, F u₀ x < (⊤ : EReal) := by
    by_contra hNoFiniteSection
    have hAllTop : ∀ x : Fin n → ℝ, F u₀ x = (⊤ : EReal) := by
      intro x
      by_contra hxTop
      have hxFinite : F u₀ x < (⊤ : EReal) := by
        simpa [lt_top_iff_ne_top] using hxTop
      exact hNoFiniteSection ⟨x, hxFinite⟩
    have hPairingBot :
        convexBifunctionPairing F u₀ = fun _ : Fin n → ℝ => (⊥ : EReal) := by
      -- If the whole primal section were `⊤`, its conjugate pairing would be constantly `⊥`.
      funext y
      rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
      apply le_antisymm
      · refine iSup_le ?_
        intro z
        simp [hAllTop]
      · exact bot_le
    have hu₀zero : (⊥ : EReal) < convexBifunctionPairing F u₀ (0 : Fin n → ℝ) := by
      simpa using hu₀ (0 : Fin n → ℝ)
    rw [hPairingBot] at hu₀zero
    exact (lt_irrefl (⊥ : EReal)) hu₀zero
  have hFproper : IsProperConvexBifunction F := by
    -- Properness is exactly nonemptiness of one finite primal section together with the no-`⊥`
    -- convention already built into the closed witness.
    refine ⟨hNoBot, ?_⟩
    rcases hFiniteSection with ⟨x₀, hx₀⟩
    exact ⟨u₀, x₀, hx₀⟩
  exact ⟨F, hF, hClosed, hFproper, hKGenerated⟩

/-- Helper for Corollary 37.5.1: a closed proper convex bifunction gives a closed proper packed
convex graph function on `ℝ^(m+n)`. -/
lemma helperForCorollary_37_5_1_graphFunction_closedProperConvex
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (hClosed : ClosedConvexBifunction F)
    (hFproper : IsProperConvexBifunction F) :
    ClosedConvexFunction (graphFunctionOfBifunction F) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (graphFunctionOfBifunction F) := by
  constructor
  · -- The closed graph-function package is exactly the graph half of `ClosedConvexBifunction`.
    simpa [bifunctionGraphFunction, graphFunctionOfBifunction] using hClosed.2
  · -- Properness was already established in the weaker Section 34 API, so reuse that proof.
    exact
      helperForCorollary_37_5_1_graphFunction_properConvex
        (F := F) (hF := hF) (hFproper := hFproper)

/-- Helper for Corollary 37.5.1: generated-class membership is exactly saddle-equivalence with the
canonical pairing kernel of the representing convex bifunction. -/
lemma helperForCorollary_37_5_1_generatedClass_gives_saddleEquivalent
    (K : SaddleFunction m n)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (hKGenerated : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩) :
    saddleEquivalent K (convexBifunctionPairing F) := by
  -- This is just the generated-class definition rewritten in the present representative notation.
  simpa [EquivalenceClassGeneratedByConvexBifunction, convexBifunctionClosedKernel] using
    hKGenerated

/-- Helper for Corollary 37.5.1: the corrected packing map is an ambient homeomorphism before
restricting to either graph. -/
lemma helperForCorollary_37_5_1_packGraphCoordinates_homeomorph :
    ∃ e :
      (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) ≃ₜ
        ((Fin (m + n) → ℝ) × (Fin (m + n) → ℝ)),
      ∀ p, e p = helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n) p := by
  let eShuffle :
      (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) ≃ₜ
        (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) :=
    { toFun := fun p => ((p.1.1, p.2.2), (-p.2.1, p.1.2))
      invFun := fun p => ((p.1.1, p.2.2), (-p.2.1, p.1.2))
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro p
        ext <;> simp
      continuous_toFun := by
        -- The shuffle only permutes blocks and negates the first dual coordinate.
        apply Continuous.prodMk
        · apply Continuous.prodMk <;> fun_prop
        · apply Continuous.prodMk <;> fun_prop
      continuous_invFun := by
        -- The inverse is the same shuffle/sign map because double negation cancels.
        apply Continuous.prodMk
        · apply Continuous.prodMk <;> fun_prop
        · apply Continuous.prodMk <;> fun_prop }
  let eAppend :
      (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) ≃ₜ
        ((Fin (m + n) → ℝ) × (Fin (m + n) → ℝ)) :=
    Homeomorph.prodCongr
      (Fin.appendHomeomorph (X := ℝ) m n)
      (Fin.appendHomeomorph (X := ℝ) m n)
  refine ⟨eShuffle.trans eAppend, ?_⟩
  intro p
  rcases p with ⟨⟨u, v⟩, ⟨uStar, vStar⟩⟩
  -- After the shuffle, each block is packed by the corresponding `Fin.append` homeomorphism.
  rfl

/-- Helper for Corollary 37.5.1: the packed dual pairing with
`((u', x') - (u, vStar), (-uStar, v))` is exactly the split affine term
`⟪x', v⟫ - ⟪vStar, v⟫ - (⟪u', uStar⟫ - ⟪u, uStar⟫)`. -/
lemma helperForCorollary_37_5_1_packedDotIncrement_eq_splitAffineTerm
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ)
    (u' : Fin m → ℝ) (x' : Fin n → ℝ) :
    (((dotProductEquiv ℝ (Fin (m + n)) (Fin.append (-uStar) v)
          (Fin.append u' x' - Fin.append u vStar) : ℝ)) : EReal) =
      (((dotProduct x' v : ℝ) : EReal) - ((dotProduct vStar v : ℝ) : EReal)) -
        (((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct u uStar : ℝ) : EReal)) := by
  -- Split the packed dot product into its first and second coordinate blocks before regrouping.
  rw [dotProductEquiv_apply_apply]
  rw [helperForCorollary33_1_3_dotProduct_append (u := -uStar) (v := v)
    (b := Fin.append u' x' - Fin.append u vStar)]
  have hFirstProj :
      (fun i => (Fin.append u' x' - Fin.append u vStar) (Fin.castAdd n i)) = u' - u := by
    -- The first `m` coordinates of the packed difference are exactly `u' - u`.
    funext i
    simp
  have hSecondProj :
      (fun j => (Fin.append u' x' - Fin.append u vStar) (Fin.natAdd m j)) = x' - vStar := by
    -- The last `n` coordinates of the packed difference are exactly `x' - vStar`.
    funext j
    simp
  rw [hFirstProj, hSecondProj, dotProduct_sub, dotProduct_sub]
  change ((((-uStar) ⬝ᵥ u' - (-uStar) ⬝ᵥ u + (v ⬝ᵥ x' - v ⬝ᵥ vStar) : ℝ)) : EReal) = _
  have hreal :
      (((-uStar) ⬝ᵥ u' - (-uStar) ⬝ᵥ u + (v ⬝ᵥ x' - v ⬝ᵥ vStar) : ℝ)) =
        (x' ⬝ᵥ v - vStar ⬝ᵥ v) - (u' ⬝ᵥ uStar - u ⬝ᵥ uStar) := by
    -- Commutativity of the real dot product reduces the packed identity to `ring`.
    rw [neg_dotProduct, neg_dotProduct]
    rw [dotProduct_comm x' v, dotProduct_comm vStar v, dotProduct_comm u' uStar,
      dotProduct_comm u uStar]
    ring
  rw [hreal, EReal.coe_sub, EReal.coe_sub]
  -- The coercions now match the target split affine term exactly.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]


end Section37
end Chap07
