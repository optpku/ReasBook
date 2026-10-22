/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part16

section Chap05
section Section24

open scoped ConvexAnalysis
open scoped Topology
open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 5.24.12: translating a proper convex function by a relative-interior anchor
places the origin in the relative interior of the translated effective domain. -/
lemma helperForTheorem_5_24_12_zero_mem_ri_effectiveDomain_translatedDifferenceAt_anchor
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x0 : Fin n → ℝ}
    (hx0ri : x0 ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    (0 : Fin n → ℝ) ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (translatedDifferenceFunctionAt f x0)) := by
  have hx0riE :
      (EuclideanSpace.equiv (Fin n) ℝ).symm x0 ∈
        euclideanRelativeInterior n
          ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    rw [helperForTheorem_23_4_preimage_eq_symmImage]
    exact
      (mem_euclideanRelativeInterior_fin_iff
        (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) (x := x0)).1 hx0ri
  have hx0FiniteRaw :=
    properConvexFunctionOn_ne_top_on_ri_effectiveDomain (f := f) hproper
      ((EuclideanSpace.equiv (Fin n) ℝ).symm x0) hx0riE
  have hx0Finite : f x0 ≠ (⊤ : EReal) ∧ f x0 ≠ (⊥ : EReal) := ⟨hx0FiniteRaw.2, hx0FiniteRaw.1⟩
  have hdomConv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    -- Proper convexity keeps the effective domain convex, so relative interior behaves well under
    -- translation by the singleton `{-x0}`.
    exact
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f)
        (by simpa [ConvexFunction] using hproper.1)
  have hDomTranslate :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (translatedDifferenceFunctionAt f x0) =
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) f + ({-x0} : Set (Fin n → ℝ)) := by
    ext z
    constructor
    · intro hz
      refine ⟨x0 + z, ?_, -x0, by simp, by simp⟩
      have hzTop :
          translatedDifferenceFunctionAt f x0 z ≠ (⊤ : EReal) :=
        (lt_top_iff_ne_top.1 (by simpa [effectiveDomain_eq] using hz))
      have hshiftTop : f (x0 + z) ≠ (⊤ : EReal) := by
        intro htop
        exact hzTop (by simpa [translatedDifferenceFunctionAt, htop] using EReal.top_sub hx0Finite.1)
      simpa [effectiveDomain_eq] using (lt_top_iff_ne_top.2 hshiftTop)
    · rintro ⟨u, hu, v, hv, hz⟩
      have hv' : v = -x0 := by simpa using hv
      subst hv'
      have huTop : f u ≠ (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using
          (lt_top_iff_ne_top.1 (by simpa [effectiveDomain_eq] using hu))
      have hz' : z = u - x0 := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz.symm
      have hTransTop :
          translatedDifferenceFunctionAt f x0 z ≠ (⊤ : EReal) := by
        have hnegBaseTop : (-f x0) ≠ (⊤ : EReal) := by
          simpa [EReal.neg_eq_top_iff] using hx0Finite.2
        rw [hz', translatedDifferenceFunctionAt, sub_eq_add_neg]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (EReal.add_ne_top huTop hnegBaseTop)
      simpa [effectiveDomain_eq] using (lt_top_iff_ne_top.2 hTransTop)
  have hTranslatedRi :
      (0 : Fin n → ℝ) ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f + ({-x0} : Set (Fin n → ℝ))) := by
    -- The translated effective domain has relative interior equal to the translated relative
    -- interior, and `x0 + (-x0) = 0`.
    rw [euclideanRelativeInterior_fin_add_eq_and_closure_add_superset hdomConv
      (by simp)]
    refine ⟨x0, hx0ri, -x0, ?_, by simp⟩
    simp [euclideanRelativeInterior_fin_singleton]
  simpa [hDomTranslate] using hTranslatedRi


/-- Helper for Theorem 5.24.12: after translating at the anchor, Theorem 23.9 pulls every scalar
subgradient of a line restriction back to an ambient translated subgradient, so ambient fiber
inclusion descends to the scalar restriction. -/
lemma helperForTheorem_5_24_12_lineRestrictionFiberSubset_of_translatedDifferenceFiberSubset
    {n : ℕ} (f g : (Fin n → ℝ) → EReal) (x0 : Fin n → ℝ)
    (A : (Fin 1 → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hx0FiniteF : f x0 ≠ (⊤ : EReal) ∧ f x0 ≠ (⊥ : EReal))
    (hx0FiniteG : g x0 ≠ (⊤ : EReal) ∧ g x0 ≠ (⊥ : EReal))
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hx0ri : x0 ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hTranslatedSubset : ∀ z : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          subdifferentialAt (translatedDifferenceFunctionAt f x0) z) ⊆
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          subdifferentialAt (translatedDifferenceFunctionAt g x0) z)) :
    ∀ t : ℝ,
      {ξ : ℝ |
        dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈
          subdifferentialAt
            (fun s => translatedDifferenceFunctionAt f x0 (A s)) (scalarPoint t)} ⊆
        {ξ : ℝ |
          dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈
            subdifferentialAt
              (fun s => translatedDifferenceFunctionAt g x0 (A s)) (scalarPoint t)} := by
  intro t ξ hξ
  let F : (Fin n → ℝ) → EReal := translatedDifferenceFunctionAt f x0
  let G : (Fin n → ℝ) → EReal := translatedDifferenceFunctionAt g x0
  have hFproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_5_24_12_translatedDifference_properConvex (f := f) hproperF x0 hx0FiniteF
  have hGproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) G :=
    helperForTheorem_5_24_12_translatedDifference_properConvex (f := g) hproperG x0 hx0FiniteG
  have hRangeRiF : RangeMeetsRelativeInteriorEffectiveDomain A F := by
    -- The translated anchor normalizes the qualification witness to the origin, which always lies
    -- in the range of the line map.
    exact
      ⟨0, ⟨0, by simp⟩, by
        simpa [F] using
          helperForTheorem_5_24_12_zero_mem_ri_effectiveDomain_translatedDifferenceAt_anchor
            (hproper := hproperF) hx0ri⟩
  have hEqF :
      subdifferentialAt (fun s => F (A s)) (scalarPoint t) =
        A.dualMap '' subdifferentialAt F (A (scalarPoint t)) := by
    -- Use the equality branch of Theorem 23.9 to pull the scalar subgradient back to the ambient
    -- translated-difference fiber of `f`.
    simpa [F] using
      (subdifferential_precomp_linearMap_contains_dualMapImage_and_eq_under_qualification
        A F hFproper).2 (Or.inl hRangeRiF) (scalarPoint t)
  have hImage :
      dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈
        A.dualMap '' subdifferentialAt F (A (scalarPoint t)) := by
    rw [← hEqF]
    exact hξ
  rcases hImage with ⟨yStar, hyStarF, hyDual⟩
  have hyVecF :
      (dotProductEquiv ℝ (Fin n)).symm yStar ∈
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt F (A (scalarPoint t))) := by
    -- Convert the ambient dual witness back to Euclidean coordinates before applying the
    -- translated fiber inclusion.
    simpa using hyStarF
  have hyVecG :
      (dotProductEquiv ℝ (Fin n)).symm yStar ∈
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt G (A (scalarPoint t))) :=
    hTranslatedSubset (A (scalarPoint t)) hyVecF
  have hyStarG : yStar ∈ subdifferentialAt G (A (scalarPoint t)) := by
    -- The same Euclidean witness is therefore a translated ambient subgradient for `g`.
    simpa using hyVecG
  have hPushG :
      A.dualMap yStar ∈ subdifferentialAt (fun s => G (A s)) (scalarPoint t) := by
    -- Push the common ambient translated subgradient forward along the same line restriction.
    exact
      (subdifferential_precomp_linearMap_contains_dualMapImage_and_eq_under_qualification
        A G hGproper).1 (scalarPoint t) ⟨yStar, hyStarG, rfl⟩
  simpa [G] using hyDual ▸ hPushG

/-- Helper for Theorem 5.24.12: scalar line restrictions of translated differences stay closed
proper convex, and the translation normalization makes them vanish at the scalar origin. -/
lemma helperForTheorem_5_24_12_lineRestriction_closedProper_data
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x0 : Fin n → ℝ)
    (A : (Fin 1 → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hx0Finite : f x0 ≠ (⊤ : EReal) ∧ f x0 ≠ (⊥ : EReal)) :
    ClosedConvexFunction (fun s => translatedDifferenceFunctionAt f x0 (A s)) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun s => translatedDifferenceFunctionAt f x0 (A s)) ∧
      (fun s => translatedDifferenceFunctionAt f x0 (A s)) (scalarPoint 0) = 0 := by
  let H : (Fin n → ℝ) → EReal := translatedDifferenceFunctionAt f x0
  have hHclosed : ClosedConvexFunction H :=
    helperForTheorem_5_24_12_translatedDifference_closed (f := f) hclosed hproper x0 hx0Finite
  have hHproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) H :=
    helperForTheorem_5_24_12_translatedDifference_properConvex (f := f) hproper x0 hx0Finite
  have hRangeDom : ∃ z : Fin n → ℝ, z ∈ Set.range A ∧ z ∈ effectiveDomain Set.univ H := by
    -- The origin is in the range of `A`, and the translated difference is normalized to be zero
    -- there, so the scalar restriction is proper.
    refine ⟨0, ⟨0, by simp⟩, ?_⟩
    have hZero : H 0 = 0 := helperForTheorem_5_24_12_translatedDifference_zero (f := f) x0 hx0Finite
    simp [effectiveDomain_eq, H, hZero]
  have hPrecompClosed : ClosedConvexFunction (fun s => H (A s)) := by
    -- Closedness is just convexity plus lower semicontinuity, both stable under continuous linear
    -- precomposition.
    refine ⟨convexFunctionOn_precomp_linearMap (A := A) (g := H) hHclosed.1, ?_⟩
    exact hHclosed.2.comp_continuous (show Continuous fun s : Fin 1 → ℝ => A s by fun_prop)
  have hPrecompProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (fun s => H (A s)) :=
    helperForTheorem_23_9_precomp_proper_of_range_meets_effectiveDomain A H hHproper hRangeDom
  have hZero : (fun s => H (A s)) (scalarPoint 0) = 0 := by
    -- Evaluating at the scalar origin lands at the translated origin because `A 0 = 0`.
    change H (A (scalarPoint 0)) = 0
    have hScalarZero : scalarPoint 0 = (0 : Fin 1 → ℝ) := by
      ext i
      simp [scalarPoint]
    have hA0 : A (scalarPoint 0) = 0 := by
      rw [hScalarZero, A.map_zero]
    rw [hA0]
    exact helperForTheorem_5_24_12_translatedDifference_zero (f := f) x0 hx0Finite
  simpa [H] using ⟨hPrecompClosed, hPrecompProper, hZero⟩

/-- Helper for Theorem 5.24.12: once two normalized scalar restrictions agree on the open segment
`Set.Ioo (0 : ℝ) 1`, closedness identifies their endpoint values at `t = 1`. -/
lemma helperForTheorem_5_24_12_translatedLine_eq_on_Ioo_imply_endpoint_equality
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    (hF0 : F (scalarPoint 0) = 0)
    (hG0 : G (scalarPoint 0) = 0)
    (hEqIoo : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F (scalarPoint t) = G (scalarPoint t)) :
    F (scalarPoint 1) = G (scalarPoint 1) := by
  have h0F : (0 : ℝ) ∈ scalarEffectiveDomain F := by
    -- The scalar normalization makes the base point finite for the segment-limit theorem.
    simp [scalarEffectiveDomain, effectiveDomain_eq, hF0]
  have h0G : (0 : ℝ) ∈ scalarEffectiveDomain G := by
    -- The same normalization is available on the `G` side.
    simp [scalarEffectiveDomain, effectiveDomain_eq, hG0]
  let e : EuclideanSpace Real (Fin 1) ≃L[Real] (Fin 1 → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
  let x0E : EuclideanSpace Real (Fin 1) := e.symm (scalarPoint 0)
  let x1E : EuclideanSpace Real (Fin 1) := e.symm (scalarPoint 1)
  have hsegF0 :
      Filter.Tendsto
        (fun t : ℝ => F ((1 - t) • scalarPoint 0 + t • scalarPoint 1))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (F (scalarPoint 1))) := by
    -- Corollary 7.5.1 computes the left limit at the endpoint `1` along the scalar segment.
    simpa [x0E, x1E, e] using
      (closedProperConvexFunction_eq_limit_along_segment
        (f := F) hclosedF hproperF (x := x0E) h0F x1E)
  have hsegF :
      Filter.Tendsto (fun t : ℝ => F (scalarPoint t)) (nhdsWithin 1 (Set.Iio 1))
        (nhds (F (scalarPoint 1))) := by
    -- Along the normalized segment, the affine interpolation is exactly `scalarPoint t`.
    convert hsegF0 using 1
    funext t
    congr 1
    ext i
    fin_cases i
    simp [scalarPoint]
  have hsegG0 :
      Filter.Tendsto
        (fun t : ℝ => G ((1 - t) • scalarPoint 0 + t • scalarPoint 1))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (G (scalarPoint 1))) := by
    -- The same scalar endpoint limit holds for `G`.
    simpa [x0E, x1E, e] using
      (closedProperConvexFunction_eq_limit_along_segment
        (f := G) hclosedG hproperG (x := x0E) h0G x1E)
  have hsegG :
      Filter.Tendsto (fun t : ℝ => G (scalarPoint t)) (nhdsWithin 1 (Set.Iio 1))
        (nhds (G (scalarPoint 1))) := by
    -- Again, the interpolating path is just the scalar point itself.
    convert hsegG0 using 1
    funext t
    congr 1
    ext i
    fin_cases i
    simp [scalarPoint]
  have hEventuallyEq :
      (fun t : ℝ => F (scalarPoint t)) =ᶠ[nhdsWithin 1 (Set.Iio 1)]
        (fun t : ℝ => G (scalarPoint t)) := by
    have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 1 (Set.Iio 1) := by
      -- Points sufficiently close to `1` from the left automatically lie in `Set.Ioo (0,1)`.
      rw [nhdsWithin]
      show Set.Ioo (0 : ℝ) 1 ∈ nhds (1 : ℝ) ⊓ Filter.principal (Set.Iio (1 : ℝ))
      refine Filter.mem_inf_of_inter
        (s := Set.Ioi (0 : ℝ)) (t := Set.Iio (1 : ℝ)) (u := Set.Ioo (0 : ℝ) 1)
        (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)) ?_ ?_
      · simp
      · intro t ht
        exact ht
    filter_upwards [hIoo] with t ht
    exact hEqIoo t ht
  have hEqLimitF :
      Filter.Tendsto (fun t : ℝ => F (scalarPoint t)) (nhdsWithin 1 (Set.Iio 1))
        (nhds (G (scalarPoint 1))) := by
    -- Replace `F` by the eventually equal profile `G` before taking the endpoint limit.
    exact Filter.Tendsto.congr' hEventuallyEq.symm hsegG
  -- A `T₂` target has unique limits along the same nontrivial filter.
  exact tendsto_nhds_unique hsegF hEqLimitF

/-- Helper for Theorem 5.24.12: scalar `toReal` profiles are convex on `Set.Ioo (0 : ℝ) 1` as
soon as every point of that open segment is known to be finite. -/
lemma helperForTheorem_5_24_12_scalarToReal_convexOn_Ioo
    (F : (Fin 1 → ℝ) → EReal)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hDomF : ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain F) :
    ConvexOn ℝ (Set.Ioo (0 : ℝ) 1) (fun u : ℝ => (F (scalarPoint u)).toReal) := by
  have hConvF : ConvexFunction F := by
    -- Proper convexity provides the ambient convexity needed for the epigraph argument.
    simpa [ConvexFunction] using hproperF.1
  refine ⟨by simpa using convex_Ioo (0 : ℝ) 1, ?_⟩
  intro u hu v hv a b ha hb hab
  have hb_le_one : b ≤ (1 : ℝ) := by
    linarith
  have h_one_sub_b_nonneg : 0 ≤ 1 - b := by
    linarith
  have h_one_sub_b_sum : (1 - b) + b = 1 := by
    ring
  have huv : (1 - b) • u + b • v ∈ Set.Ioo (0 : ℝ) 1 := by
    -- The scalar interval is convex, so every convex combination stays inside it.
    have hconv : Convex ℝ (Set.Ioo (0 : ℝ) 1) := by
      simpa using convex_Ioo (0 : ℝ) 1
    exact hconv hu hv h_one_sub_b_nonneg hb h_one_sub_b_sum
  have hFiniteUV :
      F (scalarPoint ((1 - b) • u + b • v)) ≠ (⊤ : EReal) ∧
        F (scalarPoint ((1 - b) • u + b • v)) ≠ (⊥ : EReal) := by
    -- Finiteness on the open segment is exactly the scalar-domain hypothesis.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF _ huv),
        hproperF.2.2 _ (by simp)⟩
  have hFiniteU : F (scalarPoint u) ≠ (⊤ : EReal) ∧ F (scalarPoint u) ≠ (⊥ : EReal) := by
    -- Endpoints of the convexity estimate are also finite by the same domain witness.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF _ hu),
        hproperF.2.2 _ (by simp)⟩
  have hFiniteV : F (scalarPoint v) ≠ (⊤ : EReal) ∧ F (scalarPoint v) ≠ (⊥ : EReal) := by
    -- The second endpoint is treated identically.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF _ hv),
        hproperF.2.2 _ (by simp)⟩
  have hμ : F (scalarPoint u) ≤ (((F (scalarPoint u)).toReal : ℝ) : EReal) := by
    -- Finite extended-real values coincide with their real coercions.
    simpa using le_of_eq (EReal.coe_toReal hFiniteU.1 hFiniteU.2).symm
  have hν : F (scalarPoint v) ≤ (((F (scalarPoint v)).toReal : ℝ) : EReal) := by
    -- The same coercion rewrite is available at `v`.
    simpa using le_of_eq (EReal.coe_toReal hFiniteV.1 hFiniteV.2).symm
  have hcond :=
    convexFunctionOn_epigraph_condition
      (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F)
      (by simpa [ConvexFunction] using hConvF)
      (scalarPoint u) (by simp) (scalarPoint v) (by simp)
      (F (scalarPoint u)).toReal (F (scalarPoint v)).toReal hμ hν b hb hb_le_one
  rcases hcond with ⟨_hmem, hle⟩
  have hScalarPoint :
      scalarPoint ((1 - b) • u + b • v) = (1 - b) • scalarPoint u + b • scalarPoint v := by
    -- The `Fin 1` embedding preserves the affine scalar interpolation verbatim.
    ext i
    simp [scalarPoint, smul_eq_mul, add_comm]
  have hreal :
      (F (scalarPoint ((1 - b) • u + b • v))).toReal ≤
        (1 - b) * (F (scalarPoint u)).toReal + b * (F (scalarPoint v)).toReal := by
    have hrhsTop :
        ¬(1 - (b : EReal)) * ((F (scalarPoint u)).toReal : EReal) +
            (b : EReal) * ((F (scalarPoint v)).toReal : EReal) = (⊤ : EReal) := by
      -- The real-valued convex combination on the right cannot jump to `⊤`.
      simpa [EReal.coe_mul, EReal.coe_sub] using
        EReal.add_ne_top
          (by
            simpa [EReal.coe_mul, EReal.coe_sub] using
              (EReal.coe_ne_top ((1 - b) * (F (scalarPoint u)).toReal)))
          (by
            simpa [EReal.coe_mul] using
              (EReal.coe_ne_top (b * (F (scalarPoint v)).toReal)))
    have hle' :
        F ((1 - b) • scalarPoint u + b • scalarPoint v) ≤
          (1 - (b : EReal)) * ((F (scalarPoint u)).toReal : EReal) +
            (b : EReal) * ((F (scalarPoint v)).toReal : EReal) := by
      -- This is the epigraph form of convexity specialized to the chosen real upper bounds.
      simpa [smul_eq_mul] using hle
    have hle'' :
        F (scalarPoint ((1 - b) • u + b • v)) ≤
          (1 - (b : EReal)) * ((F (scalarPoint u)).toReal : EReal) +
            (b : EReal) * ((F (scalarPoint v)).toReal : EReal) := by
      -- Rewrite the scalar affine combination back into the `scalarPoint` notation.
      simpa [hScalarPoint] using hle'
    exact EReal.toReal_le_toReal hle'' hFiniteUV.2 hrhsTop
  have hab' : a = 1 - b := by
    linarith
  -- Replace `a` by `1 - b` to match the scalar convexity formula.
  simpa [hab', smul_eq_mul, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
    sub_eq_add_neg] using hreal

/-- Helper for Theorem 5.24.12: at an interior scalar point, the right derivative of the real
`toReal` profile agrees with the `toReal` image of the extended right derivative. -/
lemma helperForTheorem_5_24_12_derivWithin_scalarToReal_eq_rightDerivativeExtension_toReal
    (F : (Fin 1 → ℝ) → EReal)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hDomF : ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain F)
    {u : ℝ} (huIoo : u ∈ Set.Ioo (0 : ℝ) 1) :
    derivWithin (fun v : ℝ => (F (scalarPoint v)).toReal) (Set.Ioi u) u =
      (rightDerivativeExtension F u).toReal := by
  have hf : ConvexFunction F := by
    -- Proper convexity on the whole line is the ambient convexity needed for directional quotients.
    simpa [ConvexFunction] using hproperF.1
  have hsubsetDom : Set.Ioo (0 : ℝ) 1 ⊆ scalarEffectiveDomain F := by
    -- The hypotheses already identify every interior scalar point with a finite point of `F`.
    intro v hv
    exact hDomF v hv
  have huInterior : u ∈ interior (scalarEffectiveDomain F) := by
    -- The full open interval `(0,1)` sits inside the scalar effective domain, so every point of it
    -- is an interior-domain point for the scalar restriction.
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo huIoo) hsubsetDom
  have huFiniteValue : F (scalarPoint u) ≠ (⊤ : EReal) ∧ F (scalarPoint u) ≠ (⊥ : EReal) := by
    -- Domain membership turns the base value into a genuine real number.
    exact
      ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF u huIoo),
        hproperF.2.2 _ (by simp)⟩
  have hRightFinite :=
    helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives F hproperF huInterior
  have huNot :
      ¬ IsLeftOfScalarEffectiveDomain F u ∧ ¬ IsRightOfScalarEffectiveDomain F u :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain F (hDomF u huIoo)
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      F hf (scalarPoint u) huFiniteValue with
    ⟨hdirRight, _hpos, _hconv, _hzero, _hsymm⟩
  have hRightTendsto :
      Filter.Tendsto
        (directionalDifferenceQuotientAt F (scalarPoint u) (scalarPoint 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (upperDirectionalDerivativeAt F (scalarPoint u) (scalarPoint 1))) := by
    -- Theorem 23.1 gives the right-quotient limit in the distinguished direction `1`.
    simpa using (hdirRight (scalarPoint 1)).2.1
  have hRightToReal :
      Filter.Tendsto
        (fun t : ℝ => (directionalDifferenceQuotientAt F (scalarPoint u) (scalarPoint 1) t).toReal)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds ((rightDerivativeExtension F u).toReal)) := by
    -- At an interior-domain point, the extended right derivative is finite, so `toReal` preserves
    -- the directional-quotient limit.
    have hUpperFiniteTop :
        upperDirectionalDerivativeAt F (scalarPoint u) (scalarPoint 1) ≠ (⊤ : EReal) := by
      simpa [rightDerivativeExtension, huNot.2, huNot.1] using hRightFinite.1
    have hUpperFiniteBot :
        upperDirectionalDerivativeAt F (scalarPoint u) (scalarPoint 1) ≠ (⊥ : EReal) := by
      simpa [rightDerivativeExtension, huNot.2, huNot.1] using hRightFinite.2.1
    have hRightToRealRaw :
        Filter.Tendsto
          (fun t : ℝ => (directionalDifferenceQuotientAt F (scalarPoint u) (scalarPoint 1) t).toReal)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
          (nhds ((upperDirectionalDerivativeAt F (scalarPoint u) (scalarPoint 1)).toReal)) :=
      (EReal.tendsto_toReal hUpperFiniteTop hUpperFiniteBot).comp hRightTendsto
    have hUpperEq :
        (upperDirectionalDerivativeAt F (scalarPoint u) (scalarPoint 1)).toReal =
          (rightDerivativeExtension F u).toReal := by
      simp [rightDerivativeExtension, huNot.2, huNot.1]
    simpa [hUpperEq] using hRightToRealRaw
  have hSubTendsto :
      Filter.Tendsto (fun v : ℝ => v - u) (nhdsWithin u (Set.Ioi u))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
    -- Translating by `u` turns the strict-right neighborhood of `u` into the positive half-line.
    have hSubTendstoRaw :
        Filter.Tendsto (fun v : ℝ => v - u) (nhdsWithin u (Set.Ioi u))
          (nhdsWithin (u - u) (Set.Ioi (0 : ℝ))) := by
      exact
        (show ContinuousWithinAt (fun v : ℝ => v - u) (Set.Ioi u) u by fun_prop).tendsto_nhdsWithin
          (by
            intro v hv
            show v - u ∈ Set.Ioi (0 : ℝ)
            simpa [Set.Ioi, sub_pos] using hv)
    simpa using hSubTendstoRaw
  have hSmall : Set.Ioo u 1 ∈ nhdsWithin u (Set.Ioi u) := by
    -- Close to `u`, every strict-right point still lies inside the ambient interval `(0,1)`.
    have hIoi : Set.Ioi u ∈ nhdsWithin u (Set.Ioi u) := self_mem_nhdsWithin
    have hIio : Set.Iio (1 : ℝ) ∈ nhdsWithin u (Set.Ioi u) :=
      nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio huIoo.2)
    have hInter : (Set.Ioi u ∩ Set.Iio (1 : ℝ)) ∈ nhdsWithin u (Set.Ioi u) :=
      Filter.inter_mem hIoi hIio
    have hEqSet : Set.Ioo u 1 = Set.Ioi u ∩ Set.Iio (1 : ℝ) := by
      ext x
      simp [Set.Ioo, Set.Ioi, Set.Iio]
    rw [hEqSet]
    exact hInter
  have hSlopeEq :
      (fun v : ℝ => slope (fun x : ℝ => (F (scalarPoint x)).toReal) u v) =ᶠ[
          nhdsWithin u (Set.Ioi u)]
        fun v : ℝ => (directionalDifferenceQuotientAt F (scalarPoint u) (scalarPoint 1) (v - u)).toReal := by
    -- On a sufficiently small strict-right neighborhood, the ordinary real slope is exactly the
    -- `toReal` image of the vector directional quotient.
    filter_upwards [hSmall] with v hv
    have hvIoo : v ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · exact lt_trans huIoo.1 hv.1
      · exact hv.2
    have hvFinite : F (scalarPoint v) ≠ (⊤ : EReal) ∧ F (scalarPoint v) ≠ (⊥ : EReal) := by
      -- The neighborhood restriction keeps the comparison point in the scalar effective domain.
      exact
        ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF v hvIoo),
          hproperF.2.2 _ (by simp)⟩
    have hvu : v - u = -u + v := by
      ring
    have hSlopeRewrite :
        slope (fun x : ℝ => (F (scalarPoint x)).toReal) u v =
          ((F (scalarPoint (u + (-u + v))) - F (scalarPoint u)) / (((-u + v : ℝ)) : EReal)).toReal := by
      have hEqEReal :
          ((((F (scalarPoint v)).toReal - (F (scalarPoint u)).toReal) / (-u + v : ℝ) : ℝ) : EReal) =
            (F (scalarPoint v) - F (scalarPoint u)) / (((-u + v : ℝ)) : EReal) := by
        rw [EReal.coe_div, EReal.coe_sub, EReal.coe_toReal hvFinite.1 hvFinite.2,
          EReal.coe_toReal huFiniteValue.1 huFiniteValue.2]
      have hEqReal := congrArg EReal.toReal hEqEReal
      simpa [slope_def_field, hvu] using hEqReal
    simpa [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant, hvu] using
      hSlopeRewrite
  have hSlopeTendsto :
      Filter.Tendsto (fun v : ℝ => slope (fun x : ℝ => (F (scalarPoint x)).toReal) u v)
        (nhdsWithin u (Set.Ioi u))
        (nhds ((rightDerivativeExtension F u).toReal)) := by
    -- Transport the directional-quotient limit through the translation `v ↦ v - u`.
    exact (hRightToReal.comp hSubTendsto).congr' hSlopeEq.symm
  have hHasDeriv :
      HasDerivWithinAt (fun v : ℝ => (F (scalarPoint v)).toReal)
        ((rightDerivativeExtension F u).toReal) (Set.Ioi u) u := by
    -- The slope characterization of one-sided differentiability packages the previous limit as the
    -- desired right derivative statement.
    exact (hasDerivWithinAt_iff_tendsto_slope' (by simp)).2 hSlopeTendsto
  -- The right half-line has unique tangent direction, so the derivative value is uniquely
  -- determined.
  exact hHasDeriv.derivWithin (uniqueDiffWithinAt_Ioi u)

/-- Helper for Theorem 5.24.12: equal right derivative extensions on `Set.Ioo (0 : ℝ) 1`
already force equal value increments between any two interior points. -/
lemma helperForTheorem_5_24_12_translatedLine_incrementEq_on_Ioo_of_rightDerivativeExtensionEq
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    (hDomF : ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain F)
    (hDomG : ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain G)
    (hRightEq : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      rightDerivativeExtension F u = rightDerivativeExtension G u)
    {s t : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (F (scalarPoint t)).toReal - (F (scalarPoint s)).toReal =
      (G (scalarPoint t)).toReal - (G (scalarPoint s)).toReal := by
  have hConvRealF :=
    helperForTheorem_5_24_12_scalarToReal_convexOn_Ioo F hproperF hDomF
  have hConvRealG :=
    helperForTheorem_5_24_12_scalarToReal_convexOn_Ioo G hproperG hDomG
  have hIntegralF :=
    (convexOn_Ioo_sub_eq_intervalIntegral_rightDerivWithin_and_leftDerivWithin
      (a := 0) (b := 1) (by norm_num)
      (f := fun u : ℝ => (F (scalarPoint u)).toReal) hConvRealF hs ht).1
  have hIntegralG :=
    (convexOn_Ioo_sub_eq_intervalIntegral_rightDerivWithin_and_leftDerivWithin
      (a := 0) (b := 1) (by norm_num)
      (f := fun u : ℝ => (G (scalarPoint u)).toReal) hConvRealG hs ht).1
  calc
    (F (scalarPoint t)).toReal - (F (scalarPoint s)).toReal =
        ∫ u in s..t, derivWithin (fun v : ℝ => (F (scalarPoint v)).toReal) (Set.Ioi u) u := hIntegralF
    _ = ∫ u in s..t, (rightDerivativeExtension F u).toReal := by
      -- On the open unit interval, the right derivative of the real profile is exactly the
      -- `toReal` image of the extended right derivative.
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro u hu
      have huIoo : u ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor
        · exact lt_of_lt_of_le (lt_min hs.1 ht.1) (le_of_lt hu.1)
        · exact lt_of_le_of_lt hu.2 (max_lt hs.2 ht.2)
      have hDerivEq :
          derivWithin (fun v : ℝ => (F (scalarPoint v)).toReal) (Set.Ioi u) u =
            (rightDerivativeExtension F u).toReal := by
        -- Invoke the dedicated scalar derivative bridge proved just above.
        exact
          helperForTheorem_5_24_12_derivWithin_scalarToReal_eq_rightDerivativeExtension_toReal
            F hproperF hDomF huIoo
      exact hDerivEq
    _ = ∫ u in s..t, (rightDerivativeExtension G u).toReal := by
      -- Substitute the assumed equality of right derivative extensions pointwise on the interval.
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro u hu
      have huIoo : u ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor
        · exact lt_of_lt_of_le (lt_min hs.1 ht.1) (le_of_lt hu.1)
        · exact lt_of_le_of_lt hu.2 (max_lt hs.2 ht.2)
      exact congrArg EReal.toReal (hRightEq u huIoo)
    _ = ∫ u in s..t, derivWithin (fun v : ℝ => (G (scalarPoint v)).toReal) (Set.Ioi u) u := by
      -- The same derivative identification holds for `G`.
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro u hu
      have huIoo : u ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor
        · exact lt_of_lt_of_le (lt_min hs.1 ht.1) (le_of_lt hu.1)
        · exact lt_of_le_of_lt hu.2 (max_lt hs.2 ht.2)
      have hDerivEq :
          derivWithin (fun v : ℝ => (G (scalarPoint v)).toReal) (Set.Ioi u) u =
            (rightDerivativeExtension G u).toReal := by
        -- The same scalar derivative bridge applies verbatim to `G`.
        exact
          helperForTheorem_5_24_12_derivWithin_scalarToReal_eq_rightDerivativeExtension_toReal
            G hproperG hDomG huIoo
      exact hDerivEq.symm
    _ = (G (scalarPoint t)).toReal - (G (scalarPoint s)).toReal := hIntegralG.symm

/-- Helper for Theorem 5.24.12: once two normalized scalar restrictions have the same right
derivative extension on `Set.Ioo (0 : ℝ) 1`, they agree at every interior point of that segment. -/
lemma helperForTheorem_5_24_12_translatedLine_rightDerivativeExtensionEq_on_Ioo_and_zero_imply_eq_on_Ioo
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    (hF0 : F (scalarPoint 0) = 0)
    (hG0 : G (scalarPoint 0) = 0)
    (hDomF : ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain F)
    (hDomG : ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain G)
    (hRightEq : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      rightDerivativeExtension F u = rightDerivativeExtension G u) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, F (scalarPoint t) = G (scalarPoint t) := by
  intro t ht
  have hZeroFiniteF : F (scalarPoint 0) ≠ (⊤ : EReal) ∧ F (scalarPoint 0) ≠ (⊥ : EReal) := by
    -- The normalization at the scalar origin provides a finite base point for `F`.
    simp [hF0]
  have hZeroFiniteG : G (scalarPoint 0) ≠ (⊤ : EReal) ∧ G (scalarPoint 0) ≠ (⊥ : EReal) := by
    -- The same normalization is available for `G`.
    simp [hG0]
  have hTFiniteF : F (scalarPoint t) ≠ (⊤ : EReal) ∧ F (scalarPoint t) ≠ (⊥ : EReal) := by
    -- Interior scalar-domain membership makes the endpoint value finite.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF t ht),
        hproperF.2.2 _ (by simp)⟩
  have hTFiniteG : G (scalarPoint t) ≠ (⊤ : EReal) ∧ G (scalarPoint t) ≠ (⊥ : EReal) := by
    -- The same finiteness clause holds for `G`.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin 1 → ℝ))) (f := G) (hDomG t ht),
        hproperG.2.2 _ (by simp)⟩
  have hLimitF :
      Filter.Tendsto (fun s : ℝ => F (scalarPoint s)) (nhdsWithin 0 (Set.Ioo (0 : ℝ) t))
        (nhds (F (scalarPoint 0))) :=
    helperForTheorem_5_24_1_segmentLimit_transport_to_Ioo F hclosedF hproperF (hDomF t ht) ht.1
  have hLimitG :
      Filter.Tendsto (fun s : ℝ => G (scalarPoint s)) (nhdsWithin 0 (Set.Ioo (0 : ℝ) t))
        (nhds (G (scalarPoint 0))) :=
    helperForTheorem_5_24_1_segmentLimit_transport_to_Ioo G hclosedG hproperG (hDomG t ht) ht.1
  have hToRealF :
      Filter.Tendsto (fun s : ℝ => (F (scalarPoint s)).toReal) (nhdsWithin 0 (Set.Ioo (0 : ℝ) t))
        (nhds ((F (scalarPoint 0)).toReal)) := by
    -- Transport the segment limit through `toReal` at the finite base point of `F`.
    exact (EReal.tendsto_toReal hZeroFiniteF.1 hZeroFiniteF.2).comp hLimitF
  have hToRealG :
      Filter.Tendsto (fun s : ℝ => (G (scalarPoint s)).toReal) (nhdsWithin 0 (Set.Ioo (0 : ℝ) t))
        (nhds ((G (scalarPoint 0)).toReal)) := by
    -- The same `toReal` transport applies to `G`.
    exact (EReal.tendsto_toReal hZeroFiniteG.1 hZeroFiniteG.2).comp hLimitG
  let HF : ℝ → ℝ := fun s => (F (scalarPoint t)).toReal - (F (scalarPoint s)).toReal
  let HG : ℝ → ℝ := fun s => (G (scalarPoint t)).toReal - (G (scalarPoint s)).toReal
  have hHF :
      Filter.Tendsto HF (nhdsWithin 0 (Set.Ioo (0 : ℝ) t)) (nhds ((F (scalarPoint t)).toReal)) := by
    -- Sending the left endpoint to `0` collapses the increment of `F` to the value at `t`.
    have :
        Filter.Tendsto (fun s : ℝ => (F (scalarPoint t)).toReal - (F (scalarPoint s)).toReal)
          (nhdsWithin 0 (Set.Ioo (0 : ℝ) t))
          (nhds ((F (scalarPoint t)).toReal - (F (scalarPoint 0)).toReal)) := by
      exact tendsto_const_nhds.sub hToRealF
    simpa [HF, hF0] using this
  have hHG :
      Filter.Tendsto HG (nhdsWithin 0 (Set.Ioo (0 : ℝ) t)) (nhds ((G (scalarPoint t)).toReal)) := by
    -- The same endpoint degeneration holds for `G`.
    have :
        Filter.Tendsto (fun s : ℝ => (G (scalarPoint t)).toReal - (G (scalarPoint s)).toReal)
          (nhdsWithin 0 (Set.Ioo (0 : ℝ) t))
          (nhds ((G (scalarPoint t)).toReal - (G (scalarPoint 0)).toReal)) := by
      exact tendsto_const_nhds.sub hToRealG
    simpa [HG, hG0] using this
  have hEventuallyEq : HF =ᶠ[nhdsWithin 0 (Set.Ioo (0 : ℝ) t)] HG := by
    -- Every strict-left endpoint `s` gives equal increments by the previous helper.
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsUnit : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hInc :=
      helperForTheorem_5_24_12_translatedLine_incrementEq_on_Ioo_of_rightDerivativeExtensionEq
        F G hclosedF hproperF hclosedG hproperG hDomF hDomG hRightEq hsUnit ht
    simpa [HF, HG] using hInc
  have hnebot : (nhdsWithin 0 (Set.Ioo (0 : ℝ) t)).NeBot := by
    -- The left endpoint belongs to the closure of every nontrivial open segment `(0,t)` with `t > 0`.
    exact
      (mem_closure_iff_nhdsWithin_neBot).1 (by
        have hclosure : closure (Set.Ioo (0 : ℝ) t) = Set.Icc (0 : ℝ) t := by
          simpa [min_eq_left (le_of_lt ht.1), max_eq_right (le_of_lt ht.1)] using
            (closure_Ioo (a := (0 : ℝ)) (b := t) ht.1.ne'.symm)
        simpa [hclosure] using (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) t by simp [le_of_lt ht.1]))
  letI := hnebot
  have hHF' :
      Filter.Tendsto HF (nhdsWithin 0 (Set.Ioo (0 : ℝ) t)) (nhds ((G (scalarPoint t)).toReal)) := by
    -- Replace the increment profile of `F` by the eventually equal increment profile of `G`.
    exact Filter.Tendsto.congr' hEventuallyEq.symm hHG
  have hEqReal : (F (scalarPoint t)).toReal = (G (scalarPoint t)).toReal :=
    tendsto_nhds_unique hHF hHF'
  calc
    F (scalarPoint t) = (((F (scalarPoint t)).toReal : ℝ) : EReal) := by
      rw [EReal.coe_toReal hTFiniteF.1 hTFiniteF.2]
    _ = (((G (scalarPoint t)).toReal : ℝ) : EReal) := by
      exact congrArg (fun r : ℝ => (r : EReal)) hEqReal
    _ = G (scalarPoint t) := by
      rw [EReal.coe_toReal hTFiniteG.1 hTFiniteG.2]

/-- Helper for Theorem 5.24.12: scalar `toReal` profiles are convex on an arbitrary cutoff
segment `Set.Ioo (0 : ℝ) τ` once every point of that segment is finite. -/
lemma helperForTheorem_5_24_12_scalarToReal_convexOn_Ioo_cutoff
    (F : (Fin 1 → ℝ) → EReal)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    {τ : ℝ} (_hTauPos : 0 < τ)
    (hDomF : ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain F) :
    ConvexOn ℝ (Set.Ioo (0 : ℝ) τ) (fun u : ℝ => (F (scalarPoint u)).toReal) := by
  have hConvF : ConvexFunction F := by
    -- Proper convexity provides the ambient convexity needed for the epigraph argument.
    simpa [ConvexFunction] using hproperF.1
  refine ⟨by simpa using convex_Ioo (0 : ℝ) τ, ?_⟩
  intro u hu v hv a b ha hb hab
  have hb_le_tau : b ≤ (1 : ℝ) := by
    linarith
  have h_one_sub_b_nonneg : 0 ≤ 1 - b := by
    linarith
  have h_one_sub_b_sum : (1 - b) + b = 1 := by
    ring
  have huv : (1 - b) • u + b • v ∈ Set.Ioo (0 : ℝ) τ := by
    -- The cutoff interval is convex, so every convex combination stays inside it.
    have hconv : Convex ℝ (Set.Ioo (0 : ℝ) τ) := by
      simpa using convex_Ioo (0 : ℝ) τ
    exact hconv hu hv h_one_sub_b_nonneg hb h_one_sub_b_sum
  have hFiniteUV :
      F (scalarPoint ((1 - b) • u + b • v)) ≠ (⊤ : EReal) ∧
        F (scalarPoint ((1 - b) • u + b • v)) ≠ (⊥ : EReal) := by
    -- Finiteness on the open segment is exactly the scalar-domain hypothesis.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF _ huv),
        hproperF.2.2 _ (by simp)⟩
  have hFiniteU : F (scalarPoint u) ≠ (⊤ : EReal) ∧ F (scalarPoint u) ≠ (⊥ : EReal) := by
    -- Endpoints of the convexity estimate are finite by the same domain witness.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF _ hu),
        hproperF.2.2 _ (by simp)⟩
  have hFiniteV : F (scalarPoint v) ≠ (⊤ : EReal) ∧ F (scalarPoint v) ≠ (⊥ : EReal) := by
    -- The second endpoint is treated identically.
    exact
      ⟨mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF _ hv),
        hproperF.2.2 _ (by simp)⟩
  have hμ : F (scalarPoint u) ≤ (((F (scalarPoint u)).toReal : ℝ) : EReal) := by
    -- Finite extended-real values coincide with their real coercions.
    simpa using le_of_eq (EReal.coe_toReal hFiniteU.1 hFiniteU.2).symm
  have hν : F (scalarPoint v) ≤ (((F (scalarPoint v)).toReal : ℝ) : EReal) := by
    -- The same coercion rewrite is available at `v`.
    simpa using le_of_eq (EReal.coe_toReal hFiniteV.1 hFiniteV.2).symm
  have hcond :=
    convexFunctionOn_epigraph_condition
      (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F)
      (by simpa [ConvexFunction] using hConvF)
      (scalarPoint u) (by simp) (scalarPoint v) (by simp)
      (F (scalarPoint u)).toReal (F (scalarPoint v)).toReal hμ hν b hb hb_le_tau
  rcases hcond with ⟨_hmem, hle⟩
  have hScalarPoint :
      scalarPoint ((1 - b) • u + b • v) = (1 - b) • scalarPoint u + b • scalarPoint v := by
    -- The `Fin 1` embedding preserves the affine scalar interpolation verbatim.
    ext i
    simp [scalarPoint, smul_eq_mul, add_comm]
  have hreal :
      (F (scalarPoint ((1 - b) • u + b • v))).toReal ≤
        (1 - b) * (F (scalarPoint u)).toReal + b * (F (scalarPoint v)).toReal := by
    have hrhsTop :
        ¬(1 - (b : EReal)) * ((F (scalarPoint u)).toReal : EReal) +
            (b : EReal) * ((F (scalarPoint v)).toReal : EReal) = (⊤ : EReal) := by
      -- The real-valued convex combination on the right cannot jump to `⊤`.
      simpa [EReal.coe_mul, EReal.coe_sub] using
        EReal.add_ne_top
          (by
            simpa [EReal.coe_mul, EReal.coe_sub] using
              (EReal.coe_ne_top ((1 - b) * (F (scalarPoint u)).toReal)))
          (by
            simpa [EReal.coe_mul] using
              (EReal.coe_ne_top (b * (F (scalarPoint v)).toReal)))
    have hle' :
        F ((1 - b) • scalarPoint u + b • scalarPoint v) ≤
          (1 - (b : EReal)) * ((F (scalarPoint u)).toReal : EReal) +
            (b : EReal) * ((F (scalarPoint v)).toReal : EReal) := by
      -- This is the epigraph form of convexity specialized to the chosen real upper bounds.
      simpa [smul_eq_mul] using hle
    have hle'' :
        F (scalarPoint ((1 - b) • u + b • v)) ≤
          (1 - (b : EReal)) * ((F (scalarPoint u)).toReal : EReal) +
            (b : EReal) * ((F (scalarPoint v)).toReal : EReal) := by
      -- Rewrite the scalar affine combination back into the `scalarPoint` notation.
      simpa [hScalarPoint] using hle'
    exact EReal.toReal_le_toReal hle'' hFiniteUV.2 hrhsTop
  have hab' : a = 1 - b := by
    linarith
  -- Replace `a` by `1 - b` to match the scalar convexity formula.
  simpa [hab', smul_eq_mul, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
    sub_eq_add_neg] using hreal

/-- Helper for Theorem 5.24.12: at an interior cutoff-segment point, the right derivative of the
real `toReal` profile agrees with the `toReal` image of the extended right derivative. -/
lemma helperForTheorem_5_24_12_derivWithin_scalarToReal_eq_rightDerivativeExtension_toReal_cutoff
    (F : (Fin 1 → ℝ) → EReal)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    {τ : ℝ} (_hTauPos : 0 < τ)
    (hDomF : ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain F)
    {u : ℝ} (huIoo : u ∈ Set.Ioo (0 : ℝ) τ) :
    derivWithin (fun v : ℝ => (F (scalarPoint v)).toReal) (Set.Ioi u) u =
      (rightDerivativeExtension F u).toReal := by
  have hf : ConvexFunction F := by
    -- Proper convexity on the whole line is the ambient convexity needed for directional quotients.
    simpa [ConvexFunction] using hproperF.1
  have hsubsetDom : Set.Ioo (0 : ℝ) τ ⊆ scalarEffectiveDomain F := by
    -- The hypotheses already identify every cutoff-segment point with a finite point of `F`.
    intro v hv
    exact hDomF v hv
  have huInterior : u ∈ interior (scalarEffectiveDomain F) := by
    -- The whole open segment `(0,τ)` sits inside the scalar effective domain.
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo huIoo) hsubsetDom
  have huFiniteValue : F (scalarPoint u) ≠ (⊤ : EReal) ∧ F (scalarPoint u) ≠ (⊥ : EReal) := by
    -- Domain membership turns the base value into a genuine real number.
    exact
      ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF u huIoo),
        hproperF.2.2 _ (by simp)⟩
  have hRightFinite :=
    helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives F hproperF huInterior
  have huNot :
      ¬ IsLeftOfScalarEffectiveDomain F u ∧ ¬ IsRightOfScalarEffectiveDomain F u :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain F (hDomF u huIoo)
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      F hf (scalarPoint u) huFiniteValue with
    ⟨hdirRight, _hpos, _hconv, _hzero, _hsymm⟩
  have hRightTendsto :
      Filter.Tendsto
        (directionalDifferenceQuotientAt F (scalarPoint u) (scalarPoint 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (upperDirectionalDerivativeAt F (scalarPoint u) (scalarPoint 1))) := by
    -- Theorem 23.1 gives the right-quotient limit in the distinguished direction `1`.
    simpa using (hdirRight (scalarPoint 1)).2.1
  have hRightToReal :
      Filter.Tendsto
        (fun t : ℝ => (directionalDifferenceQuotientAt F (scalarPoint u) (scalarPoint 1) t).toReal)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds ((rightDerivativeExtension F u).toReal)) := by
    -- At an interior-domain point, the extended right derivative is finite, so `toReal` preserves
    -- the directional-quotient limit.
    have hUpperFiniteTop :
        upperDirectionalDerivativeAt F (scalarPoint u) (scalarPoint 1) ≠ (⊤ : EReal) := by
      simpa [rightDerivativeExtension, huNot.2, huNot.1] using hRightFinite.1
    have hUpperFiniteBot :
        upperDirectionalDerivativeAt F (scalarPoint u) (scalarPoint 1) ≠ (⊥ : EReal) := by
      simpa [rightDerivativeExtension, huNot.2, huNot.1] using hRightFinite.2.1
    have hRightToRealRaw :
        Filter.Tendsto
          (fun t : ℝ => (directionalDifferenceQuotientAt F (scalarPoint u) (scalarPoint 1) t).toReal)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
          (nhds ((upperDirectionalDerivativeAt F (scalarPoint u) (scalarPoint 1)).toReal)) :=
      (EReal.tendsto_toReal hUpperFiniteTop hUpperFiniteBot).comp hRightTendsto
    have hUpperEq :
        (upperDirectionalDerivativeAt F (scalarPoint u) (scalarPoint 1)).toReal =
          (rightDerivativeExtension F u).toReal := by
      simp [rightDerivativeExtension, huNot.2, huNot.1]
    simpa [hUpperEq] using hRightToRealRaw
  have hSubTendsto :
      Filter.Tendsto (fun v : ℝ => v - u) (nhdsWithin u (Set.Ioi u))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
    -- Translating by `u` turns the strict-right neighborhood of `u` into the positive half-line.
    have hSubTendstoRaw :
        Filter.Tendsto (fun v : ℝ => v - u) (nhdsWithin u (Set.Ioi u))
          (nhdsWithin (u - u) (Set.Ioi (0 : ℝ))) := by
      exact
        (show ContinuousWithinAt (fun v : ℝ => v - u) (Set.Ioi u) u by fun_prop).tendsto_nhdsWithin
          (by
            intro v hv
            show v - u ∈ Set.Ioi (0 : ℝ)
            simpa [Set.Ioi, sub_pos] using hv)
    simpa using hSubTendstoRaw
  have hSmall : Set.Ioo u τ ∈ nhdsWithin u (Set.Ioi u) := by
    -- Close to `u`, every strict-right point still lies inside the ambient cutoff interval.
    have hIoi : Set.Ioi u ∈ nhdsWithin u (Set.Ioi u) := self_mem_nhdsWithin
    have hIio : Set.Iio τ ∈ nhdsWithin u (Set.Ioi u) :=
      nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio huIoo.2)
    have hInter : (Set.Ioi u ∩ Set.Iio τ) ∈ nhdsWithin u (Set.Ioi u) :=
      Filter.inter_mem hIoi hIio
    have hEqSet : Set.Ioo u τ = Set.Ioi u ∩ Set.Iio τ := by
      ext x
      simp [Set.Ioo, Set.Ioi, Set.Iio]
    rw [hEqSet]
    exact hInter
  have hSlopeEq :
      (fun v : ℝ => slope (fun x : ℝ => (F (scalarPoint x)).toReal) u v) =ᶠ[
          nhdsWithin u (Set.Ioi u)]
        fun v : ℝ => (directionalDifferenceQuotientAt F (scalarPoint u) (scalarPoint 1) (v - u)).toReal := by
    -- On a sufficiently small strict-right neighborhood, the ordinary real slope is exactly the
    -- `toReal` image of the vector directional quotient.
    filter_upwards [hSmall] with v hv
    have hvIoo : v ∈ Set.Ioo (0 : ℝ) τ := by
      constructor
      · exact lt_of_lt_of_le huIoo.1 (le_of_lt hv.1)
      · exact hv.2
    have hvFinite : F (scalarPoint v) ≠ (⊤ : EReal) ∧ F (scalarPoint v) ≠ (⊥ : EReal) := by
      -- The neighborhood restriction keeps the comparison point in the scalar effective domain.
      exact
        ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) (hDomF v hvIoo),
          hproperF.2.2 _ (by simp)⟩
    have hvu : v - u = -u + v := by
      ring
    have hSlopeRewrite :
        slope (fun x : ℝ => (F (scalarPoint x)).toReal) u v =
          ((F (scalarPoint (u + (-u + v))) - F (scalarPoint u)) / (((-u + v : ℝ)) : EReal)).toReal := by
      have hEqEReal :
          ((((F (scalarPoint v)).toReal - (F (scalarPoint u)).toReal) / (-u + v : ℝ) : ℝ) : EReal) =
            (F (scalarPoint v) - F (scalarPoint u)) / (((-u + v : ℝ)) : EReal) := by
        rw [EReal.coe_div, EReal.coe_sub, EReal.coe_toReal hvFinite.1 hvFinite.2,
          EReal.coe_toReal huFiniteValue.1 huFiniteValue.2]
      have hEqReal := congrArg EReal.toReal hEqEReal
      simpa [slope_def_field, hvu] using hEqReal
    simpa [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant, hvu] using
      hSlopeRewrite
  have hSlopeTendsto :
      Filter.Tendsto (fun v : ℝ => slope (fun x : ℝ => (F (scalarPoint x)).toReal) u v)
        (nhdsWithin u (Set.Ioi u))
        (nhds ((rightDerivativeExtension F u).toReal)) := by
    -- Transport the directional-quotient limit through the translation `v ↦ v - u`.
    exact (hRightToReal.comp hSubTendsto).congr' hSlopeEq.symm
  have hHasDeriv :
      HasDerivWithinAt (fun v : ℝ => (F (scalarPoint v)).toReal)
        ((rightDerivativeExtension F u).toReal) (Set.Ioi u) u := by
    -- The slope characterization of one-sided differentiability packages the previous limit as the
    -- desired right derivative statement.
    exact (hasDerivWithinAt_iff_tendsto_slope' (by simp)).2 hSlopeTendsto
  -- The right half-line has unique tangent direction, so the derivative value is uniquely
  -- determined.
  exact hHasDeriv.derivWithin (uniqueDiffWithinAt_Ioi u)


end Section24
end Chap05
