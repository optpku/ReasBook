/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part18

section Chap05
section Section24

open scoped ConvexAnalysis
open scoped Topology
open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 5.24.12: the translated scalar line restriction has a nonempty scalar
subdifferential at `0` because the ambient translated difference has nonempty subdifferential at
the relative-interior anchor and linear precomposition pushes that witness to the line. -/
lemma helperForTheorem_5_24_12_translatedLine_subdifferentialNonempty_at_zero
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x0 : Fin n → ℝ)
    (A : (Fin 1 → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hx0FiniteF : f x0 ≠ (⊤ : EReal) ∧ f x0 ≠ (⊥ : EReal))
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hx0ri : x0 ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    Set.Nonempty
      (subdifferentialAt
        (fun s => translatedDifferenceFunctionAt f x0 (A s)) (scalarPoint 0)) := by
  let H : (Fin n → ℝ) → EReal := translatedDifferenceFunctionAt f x0
  have hHproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) H :=
    helperForTheorem_5_24_12_translatedDifference_properConvex (f := f) hproperF x0 hx0FiniteF
  have hZeroRi :
      (0 : Fin n → ℝ) ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) H) := by
    -- Translating the relative-interior anchor sends `x0` to the origin.
    simpa [H] using
      helperForTheorem_5_24_12_zero_mem_ri_effectiveDomain_translatedDifferenceAt_anchor
        (hproper := hproperF) hx0ri
  have hSubNonemptyH : Set.Nonempty (subdifferentialAt H 0) := by
    -- The relative-interior clause of Theorem 23.4 supplies a nonempty ambient subdifferential.
    exact
      (subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        H hHproper 0).2.1 hZeroRi |>.1
  rcases hSubNonemptyH with ⟨yStar, hyStar⟩
  have hA0 : A (scalarPoint 0) = 0 := by
    have hScalarZero : scalarPoint 0 = (0 : Fin 1 → ℝ) := by
      ext i
      simp [scalarPoint]
    rw [hScalarZero, A.map_zero]
  have hyStarAtA0 : yStar ∈ subdifferentialAt H (A (scalarPoint 0)) := by
    simpa [hA0] using hyStar
  refine ⟨A.dualMap yStar, ?_⟩
  -- Push the ambient subgradient forward along the line map `A`.
  have hPush :
      A.dualMap yStar ∈ subdifferentialAt (fun s => H (A s)) (scalarPoint 0) := by
    exact
      (subdifferential_precomp_linearMap_contains_dualMapImage_and_eq_under_qualification
        A H hHproper).1 (scalarPoint 0) ⟨yStar, hyStarAtA0, rfl⟩
  simpa [H] using hPush

/-- Helper for Theorem 5.24.12: in the genuine cutoff case `τ = 0`, a finite endpoint value of
`G` would force an upper bound on the scalar fiber of `G` at `0`, while the translated scalar
fiber of `F` at `0` contains arbitrarily large slopes once `rightDerivativeExtension F 0 = ⊤`. -/
lemma helperForTheorem_5_24_12_tauZero_contradiction_of_offDomainEndpointAssumption
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    (hF0 : F (scalarPoint 0) = 0)
    (hG0 : G (scalarPoint 0) = 0)
    (hLineSubset :
      ∀ t : ℝ,
        {ξ : ℝ |
          dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint t)} ⊆
          {ξ : ℝ |
            dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt G (scalarPoint t)})
    (hSub0F : Set.Nonempty (subdifferentialAt F (scalarPoint 0)))
    (hRightF0 : rightDerivativeExtension F 0 = (⊤ : EReal))
    (h1DomG : (1 : ℝ) ∈ scalarEffectiveDomain G) :
    False := by
  have h0DomG : (0 : ℝ) ∈ scalarEffectiveDomain G := by
    -- The normalization at `0` keeps the scalar origin in the effective domain of `G`.
    simp [scalarEffectiveDomain, effectiveDomain_eq, hG0]
  have hG1FiniteTop :
      G (scalarPoint 1) ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := G) h1DomG
  have hG1FiniteBot :
      G (scalarPoint 1) ≠ (⊥ : EReal) :=
    hproperG.2.2 (scalarPoint 1) (by simp)
  have hRightG0Le :
      rightDerivativeExtension G 0 ≤ G (scalarPoint 1) := by
    -- The secant slope from `0` to `1` bounds the right derivative of `G` at `0`.
    simpa [hG0] using
      (helperForTheorem_5_24_1_secantSlope_between_rightAndLeftDerivatives
        G hproperG (by norm_num) h0DomG h1DomG).1
  have hBandsF0 :
      {ξ : ℝ |
        dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint 0)} =
          {ξ : ℝ |
            leftDerivativeExtension F 0 ≤ ((ξ : ℝ) : EReal) ∧
              (((ξ : ℝ) : EReal) ≤ rightDerivativeExtension F 0)} := by
    -- Rewrite the fiber of `F` at `0` as the interval between its scalar derivative endpoints.
    simpa using
      oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
        F hclosedF hproperF 0
  have hBandsG0 :
      {ξ : ℝ |
        dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt G (scalarPoint 0)} =
          {ξ : ℝ |
            leftDerivativeExtension G 0 ≤ ((ξ : ℝ) : EReal) ∧
              (((ξ : ℝ) : EReal) ≤ rightDerivativeExtension G 0)} := by
    -- The same interval description applies to `G`.
    simpa using
      oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
        G hclosedG hproperG 0
  rcases hSub0F with ⟨x0Star, hx0StarF⟩
  let ξ : ℝ := ((dotProductEquiv ℝ (Fin 1)).symm x0Star) 0
  have hScalarPointξ :
      scalarPoint ξ = (dotProductEquiv ℝ (Fin 1)).symm x0Star := by
    ext i
    fin_cases i
    simp [ξ, scalarPoint]
  have hξMemF :
      ξ ∈ {ξ : ℝ |
        dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint 0)} := by
    -- Rewrite the scalar witness in coordinates on `Fin 1`.
    simpa [hScalarPointξ] using hx0StarF
  have hξBandF :
      leftDerivativeExtension F 0 ≤ ((ξ : ℝ) : EReal) ∧
        (((ξ : ℝ) : EReal) ≤ rightDerivativeExtension F 0) := by
    rw [hBandsF0] at hξMemF
    exact hξMemF
  let η : ℝ := max ξ (G (scalarPoint 1)).toReal + 1
  have hξLeEta : ξ ≤ η := by
    dsimp [η]
    linarith [le_max_left ξ (G (scalarPoint 1)).toReal]
  have hEtaMemF :
      η ∈ {ξ : ℝ |
        dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint 0)} := by
    rw [hBandsF0]
    constructor
    · calc
        leftDerivativeExtension F 0 ≤ ((ξ : ℝ) : EReal) := hξBandF.1
        _ ≤ ((η : ℝ) : EReal) := by
          exact_mod_cast hξLeEta
    · calc
        ((η : ℝ) : EReal) ≤ (⊤ : EReal) := by simp
        _ = rightDerivativeExtension F 0 := by rw [hRightF0]
  have hEtaMemG :
      η ∈ {ξ : ℝ |
        dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt G (scalarPoint 0)} :=
    hLineSubset 0 hEtaMemF
  have hEtaLeRightG0 :
      ((η : ℝ) : EReal) ≤ rightDerivativeExtension G 0 := by
    rw [hBandsG0] at hEtaMemG
    exact hEtaMemG.2
  have hEtaLeG1 : ((η : ℝ) : EReal) ≤ G (scalarPoint 1) := le_trans hEtaLeRightG0 hRightG0Le
  have hG1Coe :
      G (scalarPoint 1) = (((G (scalarPoint 1)).toReal : ℝ) : EReal) := by
    rw [EReal.coe_toReal hG1FiniteTop hG1FiniteBot]
  have hEtaLeReal : η ≤ (G (scalarPoint 1)).toReal := by
    rw [hG1Coe] at hEtaLeG1
    exact_mod_cast hEtaLeG1
  have hEtaGtReal : (G (scalarPoint 1)).toReal < η := by
    dsimp [η]
    linarith [le_max_right ξ (G (scalarPoint 1)).toReal]
  exact (not_le_of_gt hEtaGtReal) hEtaLeReal

/-- Helper for Theorem 5.24.12: in the off-domain branch of the globalization argument, it
remains to prove that the translated scalar restriction for `g` also blows up at the endpoint
`t = 1`. -/
lemma helperForTheorem_5_24_12_offDomainTarget_valueEqTop_of_primalFiberSubset
    {n : ℕ} (f g : (Fin n → ℝ) → EReal) (x0 y : Fin n → ℝ)
    (hx0FiniteF : f x0 ≠ (⊤ : EReal) ∧ f x0 ≠ (⊥ : EReal))
    (hx0FiniteG : g x0 ≠ (⊤ : EReal) ∧ g x0 ≠ (⊥ : EReal))
    (hyOffF : y ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (hclosedF : ClosedConvexFunction f)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hclosedG : ClosedConvexFunction g)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hx0ri : x0 ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hTranslatedSubset : ∀ z : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          subdifferentialAt (translatedDifferenceFunctionAt f x0) z) ⊆
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          subdifferentialAt (translatedDifferenceFunctionAt g x0) z)) :
    g y = (⊤ : EReal) := by
  let A : (Fin 1 → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun s => (s 0) • (y - x0)
      map_add' := by
        intro s t
        simp [add_smul]
      map_smul' := by
        intro r s
        simp [smul_smul] }
  let F : (Fin 1 → ℝ) → EReal := fun s => translatedDifferenceFunctionAt f x0 (A s)
  let G : (Fin 1 → ℝ) → EReal := fun s => translatedDifferenceFunctionAt g x0 (A s)
  have hLineSubset :
      ∀ t : ℝ,
        {ξ : ℝ |
          dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint t)} ⊆
          {ξ : ℝ |
            dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt G (scalarPoint t)} := by
    -- Pull scalar subgradients back to the translated ambient fibers and re-push them after
    -- applying the given translated primal-fiber inclusion.
    simpa [F, G] using
      helperForTheorem_5_24_12_lineRestrictionFiberSubset_of_translatedDifferenceFiberSubset
        f g x0 A hx0FiniteF hx0FiniteG hproperF hproperG hx0ri hTranslatedSubset
  rcases
      helperForTheorem_5_24_12_lineRestriction_closedProper_data
        f x0 A hclosedF hproperF hx0FiniteF with
    ⟨hclosedLineF, hproperLineF, hF0⟩
  rcases
      helperForTheorem_5_24_12_lineRestriction_closedProper_data
        g x0 A hclosedG hproperG hx0FiniteG with
    ⟨hclosedLineG, hproperLineG, hG0⟩
  have hA1 : A (scalarPoint 1) = y - x0 := by
    -- The scalar endpoint `1` lands exactly at the target difference vector.
    ext i
    simp [A, scalarPoint]
  have hyTopF : f y = (⊤ : EReal) := by
    -- Leaving the effective domain forces the original function value to be `⊤`.
    by_contra hyNotTop
    have hyLtTop : f y < (⊤ : EReal) := (lt_top_iff_ne_top.2 hyNotTop)
    have hyEff : y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
      simpa [effectiveDomain_eq] using
        (show y ∈ {u : Fin n → ℝ | u ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f u < (⊤ : EReal)} from
          ⟨by simp, hyLtTop⟩)
    exact hyOffF hyEff
  have hF1Top : F (scalarPoint 1) = (⊤ : EReal) := by
    -- Evaluating the translated scalar restriction at `1` reaches the off-domain target `y`.
    rw [show F (scalarPoint 1) = translatedDifferenceFunctionAt f x0 (y - x0) by simp [F, hA1]]
    simpa [translatedDifferenceFunctionAt, hyTopF, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]
      using (EReal.top_add_of_ne_bot (by simpa [EReal.neg_eq_bot_iff] using hx0FiniteF.1))
  have h1OffF : (1 : ℝ) ∉ scalarEffectiveDomain F := by
    -- The endpoint is outside the scalar effective domain exactly because its value is `⊤`.
    intro h1Dom
    have h1NeTop : F (scalarPoint 1) ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := F) h1Dom
    exact h1NeTop hF1Top
  have _h1RightF :
      IsRightOfScalarEffectiveDomain F 1 :=
    helperForTheorem_5_24_12_translatedLine_endpoint_rightExterior_of_offDomainTarget
      F hproperLineF hF0 h1OffF
  have _hLineSubsetAtOne := hLineSubset 1
  let _ := hclosedLineF
  let _ := hclosedLineG
  let _ := hproperLineG
  let _ := hG0
  by_cases h1DomG : (1 : ℝ) ∈ scalarEffectiveDomain G
  · have hCutoffData :=
      helperForTheorem_5_24_12_cutoffData_of_offDomainEndpointAssumption
        F G hproperLineF hproperLineG hF0 h1OffF hG0 h1DomG
    dsimp only at hCutoffData
    rcases hCutoffData with ⟨hTauNonneg, hTauLeOne, hInitialSegmentF, hTauDomG, hRightOfCutoff⟩
    let τ : ℝ := sSup (scalarEffectiveDomain F ∩ Set.Icc (0 : ℝ) 1)
    by_cases hTauOne : τ = 1
    · have hDomFUnit :
        ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain F := by
        intro u hu
        -- When `τ = 1`, the cutoff package already says that all interior unit-segment points lie
        -- in the scalar effective domain of `F`.
        have huTau : u ∈ Set.Ioo (0 : ℝ) τ := by
          simpa [τ, hTauOne] using hu
        exact hInitialSegmentF u huTau
      have hEqEndpoint :
          F (scalarPoint 1) = G (scalarPoint 1) :=
        helperForTheorem_5_24_12_translatedLine_endpointEquality_of_scalarFiberSubset_on_unitInterval
          F G hclosedLineF hproperLineF hclosedLineG hproperLineG hF0 hG0 hDomFUnit hLineSubset
      have hG1NeTop :
          G (scalarPoint 1) ≠ (⊤ : EReal) :=
        mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := G) h1DomG
      -- If the cutoff reaches `1`, closedness forces endpoint equality, contradicting that `F`
      -- already equals `⊤` there while `G` is still finite.
      exact False.elim (hG1NeTop (hEqEndpoint.symm.trans hF1Top))
    · have hTauLtOne : τ < 1 := lt_of_le_of_ne hTauLeOne hTauOne
      have hRightTauTop :
          rightDerivativeExtension F τ = (⊤ : EReal) :=
        helperForTheorem_5_24_12_rightDerivativeExtension_eq_top_at_cutoff_of_rightExteriorTail
          F hclosedLineF hproperLineF hTauLtOne hRightOfCutoff
      by_cases hTauZero : τ = 0
      · have hSub0F :
          Set.Nonempty (subdifferentialAt F (scalarPoint 0)) :=
          helperForTheorem_5_24_12_translatedLine_subdifferentialNonempty_at_zero
            f x0 A hx0FiniteF hproperF hx0ri
        -- When `τ = 0`, the contradiction comes from the scalar fiber at the anchor itself.
        exact
          False.elim
            (helperForTheorem_5_24_12_tauZero_contradiction_of_offDomainEndpointAssumption
              F G hclosedLineF hproperLineF hclosedLineG hproperLineG hF0 hG0 hLineSubset
              hSub0F (by simpa [τ, hTauZero] using hRightTauTop) h1DomG)
      · have hTauPos : 0 < τ := lt_of_le_of_ne hTauNonneg (by simpa [eq_comm] using hTauZero)
        have hEqInitialSegment :
            ∀ u ∈ Set.Ioo (0 : ℝ) τ, F (scalarPoint u) = G (scalarPoint u) :=
          helperForTheorem_5_24_12_translatedLine_eq_on_initialSegment_of_primalFiberSubset_allowingZeroCutoff
            F G hclosedLineF hproperLineF hclosedLineG hproperLineG
            hTauNonneg hTauLeOne hF0 hG0 hInitialSegmentF hTauDomG hLineSubset
        have hEqTau :
            F (scalarPoint τ) = G (scalarPoint τ) :=
          helperForTheorem_5_24_12_translatedLine_cutoffEndpointEquality_of_primalFiberSubset
            F G hclosedLineF hproperLineF hclosedLineG hproperLineG hTauPos hF0 hG0
            hEqInitialSegment
        have hTauNeTopG :
            G (scalarPoint τ) ≠ (⊤ : EReal) :=
          mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := G) hTauDomG
        have hTauNeTopF :
            F (scalarPoint τ) ≠ (⊤ : EReal) := by
          rw [hEqTau]
          exact hTauNeTopG
        have hTauDomF : τ ∈ scalarEffectiveDomain F := by
          simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top] using
            (lt_top_iff_ne_top.2 hTauNeTopF)
        have h0DomG : (0 : ℝ) ∈ scalarEffectiveDomain G := by
          -- The normalization at the scalar origin keeps `0` in the effective domain of `G`.
          have hG0' : G (scalarPoint 0) = 0 := by
            exact hG0
          have hZeroLtTop : ((0 : ℝ) : EReal) < (⊤ : EReal) := by
            simp
          simpa [scalarEffectiveDomain, effectiveDomain_eq, hG0'] using hZeroLtTop
        have hConvDomG :
            Convex ℝ (scalarEffectiveDomain G) :=
          helperForTheorem_5_24_1_scalarEffectiveDomain_convex G hproperLineG
        have hDomGUnit :
            ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain G := by
          intro u hu
          -- Convexity fills in the whole unit segment between the known domain points `0` and `1`.
          exact (hConvDomG.ordConnected.out h0DomG h1DomG) ⟨le_of_lt hu.1, le_of_lt hu.2⟩
        have hTauInteriorG : τ ∈ interior (scalarEffectiveDomain G) := by
          -- Since `0 < τ < 1` and `G` is finite on the whole open unit segment, `τ` is an
          -- interior-domain point for `G`.
          rw [mem_interior_iff_mem_nhds]
          exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo ⟨hTauPos, hTauLtOne⟩)
            (fun v hv => hDomGUnit v hv)
        have hDomGSeg :
            ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain G := by
          intro u hu
          exact (hConvDomG.ordConnected.out h0DomG hTauDomG) ⟨le_of_lt hu.1, le_of_lt hu.2⟩
        have hInteriorFSeg :
            ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ interior (scalarEffectiveDomain F) := by
          intro u hu
          -- The whole cutoff segment `(0,τ)` lies in `dom F`.
          rw [mem_interior_iff_mem_nhds]
          exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hu)
            (fun v hv => hInitialSegmentF v hv)
        have hInteriorGSeg :
            ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ interior (scalarEffectiveDomain G) := by
          intro u hu
          -- The same interior-domain argument applies to `G` on the cutoff segment.
          rw [mem_interior_iff_mem_nhds]
          exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hu)
            (fun v hv => hDomGSeg v hv)
        have hBandSeg :
            ∀ u ∈ Set.Ioo (0 : ℝ) τ,
              leftDerivativeExtension G u ≤ leftDerivativeExtension F u ∧
                rightDerivativeExtension F u ≤ rightDerivativeExtension G u := by
          intro u hu
          -- Compare scalar fibers on `(0,τ)` before passing to derivative equality.
          exact
            helperForTheorem_5_24_12_scalarRestrictionDerivativeBandBounds_of_primalFiberSubset
              F G hclosedLineF hproperLineF hclosedLineG hproperLineG
              (hInteriorFSeg u hu) (hInteriorGSeg u hu) (hLineSubset u)
        have hDerivativeEqSeg :
            ∀ u ∈ Set.Ioo (0 : ℝ) τ,
              leftDerivativeExtension G u = leftDerivativeExtension F u ∧
                rightDerivativeExtension F u = rightDerivativeExtension G u :=
          helperForTheorem_5_24_12_derivativeBandBounds_on_Ioo_imply_scalarDerivativeExtensionsEq
            F G hclosedLineF hproperLineF hclosedLineG hproperLineG hTauPos hBandSeg
        rcases
            oneDimensional_derivativeExtensions_monotone_ordered_and_oneSidedContinuous
              F hclosedLineF hproperLineF with
          ⟨_hmonoRightF, _hmonoLeftF, _hfiniteF, _horderedF,
            _hRightRightF, hRightLeftF, _hLeftRightF, _hLeftLeftF⟩
        rcases
            oneDimensional_derivativeExtensions_monotone_ordered_and_oneSidedContinuous
              G hclosedLineG hproperLineG with
          ⟨_hmonoRightG, _hmonoLeftG, hfiniteG, _horderedG,
            _hRightRightG, hRightLeftG, _hLeftRightG, _hLeftLeftG⟩
        have hIooLeft :
            Set.Ioo (0 : ℝ) τ ∈ nhdsWithin τ (Set.Iio τ) := by
          -- Because `0 < τ`, a sufficiently small left neighborhood of `τ` stays inside `(0,τ)`.
          rw [nhdsWithin]
          show Set.Ioo (0 : ℝ) τ ∈ nhds τ ⊓ Filter.principal (Set.Iio τ)
          refine Filter.mem_inf_of_inter
            (s := Set.Ioi (0 : ℝ)) (t := Set.Iio τ) (u := Set.Ioo (0 : ℝ) τ)
            (Ioi_mem_nhds hTauPos) ?_ ?_
          · simp
          · intro z hz
            exact hz
        have hEventuallyRightEq :
            (fun z : ℝ => rightDerivativeExtension F z) =ᶠ[nhdsWithin τ (Set.Iio τ)]
              (fun z : ℝ => rightDerivativeExtension G z) := by
          -- On points just to the left of `τ`, the right derivative extensions already agree.
          filter_upwards [hIooLeft] with z hz
          exact (hDerivativeEqSeg z hz).2
        have hLeftEqTau :
            leftDerivativeExtension F τ = leftDerivativeExtension G τ := by
          have hLeftLimitF :
              Filter.Tendsto (fun z : ℝ => rightDerivativeExtension F z) (nhdsWithin τ (Set.Iio τ))
                (nhds (leftDerivativeExtension F τ)) :=
            hRightLeftF τ
          have hLeftLimitG :
              Filter.Tendsto (fun z : ℝ => rightDerivativeExtension G z) (nhdsWithin τ (Set.Iio τ))
                (nhds (leftDerivativeExtension G τ)) :=
            hRightLeftG τ
          have hLeftLimitF' :
              Filter.Tendsto (fun z : ℝ => rightDerivativeExtension F z) (nhdsWithin τ (Set.Iio τ))
                (nhds (leftDerivativeExtension G τ)) := by
            exact Filter.Tendsto.congr' hEventuallyRightEq.symm hLeftLimitG
          exact tendsto_nhds_unique hLeftLimitF hLeftLimitF'
        have hFiniteDirG :
            rightDerivativeExtension G τ ≠ (⊤ : EReal) ∧
              rightDerivativeExtension G τ ≠ (⊥ : EReal) ∧
              leftDerivativeExtension G τ ≠ (⊤ : EReal) ∧
              leftDerivativeExtension G τ ≠ (⊥ : EReal) :=
          hfiniteG τ hTauInteriorG
        have hBandsFτ :
            {ξ : ℝ |
              dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint τ)} =
              {ξ : ℝ |
                leftDerivativeExtension F τ ≤ ((ξ : ℝ) : EReal) ∧
                  (((ξ : ℝ) : EReal) ≤ rightDerivativeExtension F τ)} := by
          -- Rewrite the fiber of `F` at `τ` as the interval between its scalar derivative endpoints.
          simpa using
            oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
              F hclosedLineF hproperLineF τ
        have hBandsGτ :
            {ξ : ℝ |
              dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt G (scalarPoint τ)} =
              {ξ : ℝ |
                leftDerivativeExtension G τ ≤ ((ξ : ℝ) : EReal) ∧
                  (((ξ : ℝ) : EReal) ≤ rightDerivativeExtension G τ)} := by
          -- The same interval description applies to `G`.
          simpa using
            oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
              G hclosedLineG hproperLineG τ
        have hLeftLeRightGReal :
            (leftDerivativeExtension G τ).toReal ≤ (rightDerivativeExtension G τ).toReal := by
          have hLe :
              (((leftDerivativeExtension G τ).toReal : ℝ) : EReal) ≤
                (((rightDerivativeExtension G τ).toReal : ℝ) : EReal) := by
            calc
              (((leftDerivativeExtension G τ).toReal : ℝ) : EReal) = leftDerivativeExtension G τ := by
                rw [EReal.coe_toReal hFiniteDirG.2.2.1 hFiniteDirG.2.2.2]
              _ ≤ rightDerivativeExtension G τ :=
                helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
                  G hproperLineG τ
              _ = (((rightDerivativeExtension G τ).toReal : ℝ) : EReal) := by
                rw [EReal.coe_toReal hFiniteDirG.1 hFiniteDirG.2.1]
          exact_mod_cast hLe
        let η : ℝ := (rightDerivativeExtension G τ).toReal + 1
        have hEtaMemF :
            η ∈ {ξ : ℝ |
              dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint τ)} := by
          rw [hBandsFτ]
          constructor
          · calc
              leftDerivativeExtension F τ = leftDerivativeExtension G τ := hLeftEqTau
              _ = (((leftDerivativeExtension G τ).toReal : ℝ) : EReal) := by
                rw [EReal.coe_toReal hFiniteDirG.2.2.1 hFiniteDirG.2.2.2]
              _ ≤ ((η : ℝ) : EReal) := by
                dsimp [η]
                exact_mod_cast (show (leftDerivativeExtension G τ).toReal ≤
                  (rightDerivativeExtension G τ).toReal + 1 by linarith [hLeftLeRightGReal])
          · calc
              ((η : ℝ) : EReal) ≤ (⊤ : EReal) := by simp
              _ = rightDerivativeExtension F τ := by rw [hRightTauTop]
        have hEtaMemG :
            η ∈ {ξ : ℝ |
              dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt G (scalarPoint τ)} :=
          hLineSubset τ hEtaMemF
        have hEtaLeRightG :
            ((η : ℝ) : EReal) ≤ rightDerivativeExtension G τ := by
          rw [hBandsGτ] at hEtaMemG
          exact hEtaMemG.2
        have hEtaLeRightGReal :
            η ≤ (rightDerivativeExtension G τ).toReal := by
          have hEtaLeRightGCoe :
              ((η : ℝ) : EReal) ≤ (((rightDerivativeExtension G τ).toReal : ℝ) : EReal) := by
            calc
              ((η : ℝ) : EReal) ≤ rightDerivativeExtension G τ := hEtaLeRightG
              _ = (((rightDerivativeExtension G τ).toReal : ℝ) : EReal) := by
                rw [EReal.coe_toReal hFiniteDirG.1 hFiniteDirG.2.1]
          exact_mod_cast hEtaLeRightGCoe
        have hEtaGtRightGReal :
            (rightDerivativeExtension G τ).toReal < η := by
          dsimp [η]
          linarith
        exact False.elim ((not_le_of_gt hEtaGtRightGReal) hEtaLeRightGReal)
  · have hG1Top : G (scalarPoint 1) = (⊤ : EReal) :=
      helperForTheorem_5_24_12_scalarValue_eq_top_of_not_mem_scalarEffectiveDomain G h1DomG
    -- If `1` is already outside the scalar effective domain of `G`, the translated endpoint value
    -- is `⊤`, so the original target value `g y` must also be `⊤`.
    by_contra hyNotTopG
    have hnegBaseTop : (-g x0) ≠ (⊤ : EReal) := by
      simpa [EReal.neg_eq_top_iff] using hx0FiniteG.2
    have hG1NeTop : G (scalarPoint 1) ≠ (⊤ : EReal) := by
      rw [show G (scalarPoint 1) = translatedDifferenceFunctionAt g x0 (y - x0) by simp [G, hA1]]
      simpa [translatedDifferenceFunctionAt, hyNotTopG, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using (EReal.add_ne_top hyNotTopG hnegBaseTop)
    exact hG1NeTop hG1Top


/-- Helper for Theorem 5.24.12: the missing globalization step should upgrade pointwise
Euclideanized primal-fiber inclusion between closed proper convex functions to a single additive
constant. -/
lemma helperForTheorem_5_24_12_primalFiberSubset_implies_eq_up_to_constant
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction f)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hclosedG : ClosedConvexFunction g)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hsubset : ∀ x : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ⊆
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x)) :
    ∃ α : ℝ, ∀ x : Fin n → ℝ,
      g x = f x + ((α : ℝ) : EReal) := by
  have hf : ConvexFunction f := by
    -- The effective domain of `f` is convex, so it admits a relative-interior anchor point.
    simpa [ConvexFunction] using hproperF.1
  have _hconjSubset :=
    helperForTheorem_5_24_12_conjugateFiberSubset_of_primalFiberSubset
      f g hclosedF hproperF hclosedG hproperG hsubset
  have hdomConv : Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hf
  obtain ⟨xFin, rFin, hxFinEq⟩ :=
    properConvexFunctionOn_exists_finite_point (n := n) (f := f) hproperF
  have hxFinDom : xFin ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    -- A finite value of `f` is exactly membership in the effective domain.
    simp [effectiveDomain_eq, hxFinEq]
  obtain ⟨x0, hx0ri⟩ :=
    helperForText_19_0_7_exists_mem_euclideanRelativeInterior_fin_of_convex_nonempty
      hdomConv ⟨xFin, hxFinDom⟩
  have hx0Sub : Set.Nonempty (subdifferentialAt f x0) := by
    -- The relative-interior clause of Theorem 23.4 supplies a nonempty primal fiber at `x0`.
    exact
      (subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        f hproperF x0).2.1 hx0ri |>.1
  obtain ⟨x0Dual, hx0Dual⟩ := hx0Sub
  let x0Star : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm x0Dual
  have hx0StarF : x0Star ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x0) := by
    -- Rewrite the dual witness in Euclidean coordinates before applying the inclusion hypothesis.
    simpa [x0Star] using hx0Dual
  have hx0StarG : x0Star ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x0) :=
    hsubset x0 hx0StarF
  obtain ⟨α, hα0⟩ :=
    helperForTheorem_5_24_12_additive_constant_exists_at_common_graph_point
      f g hproperF hproperG hx0StarF hx0StarG
  have hx0FiniteF :=
    helperForTheorem_23_4_finiteAt_of_subdifferentiable f hproperF x0 ⟨x0Dual, hx0Dual⟩
  have hx0SubG : Set.Nonempty (subdifferentialAt g x0) := by
    exact ⟨dotProductEquiv ℝ (Fin n) x0Star, by simpa [IsEuclideanSubgradientAt] using hx0StarG⟩
  have hx0FiniteG :=
    helperForTheorem_23_4_finiteAt_of_subdifferentiable g hproperG x0 hx0SubG
  have hTranslatedSubset :=
    helperForTheorem_5_24_12_translatedDifferenceFiberSubset_of_primalFiberSubset
      f g x0 hx0FiniteF hx0FiniteG hsubset
  have hZeroRi :
      (0 : Fin n → ℝ) ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (translatedDifferenceFunctionAt f x0)) :=
    helperForTheorem_5_24_12_zero_mem_ri_effectiveDomain_translatedDifferenceAt_anchor
      (hproper := hproperF) hx0ri
  refine ⟨α, ?_⟩
  intro y
  by_cases hyDomF : y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  · -- On `dom f`, the translated line-restriction machinery globalizes the anchor constant from
    -- `x0` to the target point `y`.
    have hEndpoint :
        translatedDifferenceFunctionAt f x0 (y - x0) =
          translatedDifferenceFunctionAt g x0 (y - x0) :=
      helperForTheorem_5_24_12_translatedLine_endpointEquality_of_primalFiberSubset
        f g x0 y hx0FiniteF hx0FiniteG hyDomF hclosedF hproperF hclosedG hproperG hx0ri
        hTranslatedSubset
    exact
      helperForTheorem_5_24_12_translatedEndpointEquality_implies_valueEqualityAtTarget
        f g x0 y α hx0FiniteF hEndpoint hα0
  · -- Route correction: the translated-line assembly above now settles every point of `dom f`.
    -- The remaining blocker is now isolated in the dedicated scalar off-domain helper below.
    have hyTopF : f y = (⊤ : EReal) := by
      -- Leaving the effective domain forces the original value to be `⊤` on the universal set.
      by_contra hyNotTop
      have hyLtTop : f y < (⊤ : EReal) := (lt_top_iff_ne_top.2 hyNotTop)
      have hyEff : y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
        simpa [effectiveDomain_eq] using
          (show y ∈ {u : Fin n → ℝ | u ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f u < (⊤ : EReal)} from
            ⟨by simp, hyLtTop⟩)
      exact hyDomF hyEff
    have hyTopG : g y = (⊤ : EReal) :=
      helperForTheorem_5_24_12_offDomainTarget_valueEqTop_of_primalFiberSubset
        f g x0 y hx0FiniteF hx0FiniteG hyDomF hclosedF hproperF hclosedG hproperG hx0ri
        hTranslatedSubset
    calc
      g y = (⊤ : EReal) := hyTopG
      _ = f y + ((α : ℝ) : EReal) := by rw [hyTopF]; simp

/-- Helper for Theorem 5.24.12: once the stronger inclusion-to-constant engine is available,
pointwise Euclideanized subdifferential inclusion collapses to equality. -/
lemma helperForTheorem_5_24_12_subdifferentialSubset_between_closedProperConvex_isEquality
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction f)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hclosedG : ClosedConvexFunction g)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hsubset : ∀ x : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ⊆
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x)) :
    ∀ x : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x) := by
  rcases
      helperForTheorem_5_24_12_primalFiberSubset_implies_eq_up_to_constant
        f g hclosedF hproperF hclosedG hproperG hsubset with
    ⟨α, hα⟩
  -- After globalizing to `g = f + α`, constant-shift invariance identifies the fibers.
  exact helperForTheorem_5_24_12_subdifferential_eq_of_eq_add_constant hα

/-- Helper for Theorem 5.24.12: the Euclideanized subdifferential of a closed proper convex
function is maximal cyclically monotone. -/
lemma helperForTheorem_5_24_12_realizedSubdifferential_isMaximal
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsMaximalCyclicallyMonotone
      (fun x : Fin n → ℝ =>
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) := by
  constructor
  · -- The realized subdifferential is cyclically monotone by Proposition 5.24.3.
    exact properConvexFunctionOn_isCyclicallyMonotone_subdifferential f hproper
  · intro σ hσ hgraphSubset
    rcases
        (exists_closedProperConvex_subdifferential_superset_iff_isCyclicallyMonotone
          (ρ := σ)).2 hσ with
      ⟨g, hclosedG, hproperG, hsubset⟩
    have hsubsetFG : ∀ x : Fin n → ℝ,
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ⊆
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x) := by
      intro x v hv
      -- Read subdifferential-fiber membership as a graph point, then pass to the cyclically
      -- monotone supergraph `σ` and finally to the realizing potential `g`.
      have hp :
          (x, v) ∈
            multivaluedMappingGraph
              (fun y : Fin n → ℝ =>
                ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f y)) := by
        simpa [multivaluedMappingGraph] using hv
      have hpσ : (x, v) ∈ multivaluedMappingGraph σ := hgraphSubset hp
      exact hsubset x (by simpa [multivaluedMappingGraph] using hpσ)
    have hEqFibers :=
      helperForTheorem_5_24_12_subdifferentialSubset_between_closedProperConvex_isEquality
        f g hclosed hproper hclosedG hproperG hsubsetFG
    ext p
    constructor
    · intro hp
      have hpσ : p.2 ∈ σ p.1 := by
        simpa [multivaluedMappingGraph] using hp
      have hpMem : p.2 ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g p.1) :=
        hsubset p.1 hpσ
      -- Collapse the realizing supergraph back to the original graph using fiber equality.
      have hpMemF : p.2 ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f p.1) := by
        simpa [hEqFibers p.1] using hpMem
      simpa [multivaluedMappingGraph] using hpMemF
    · intro hp
      -- The original graph inclusion into `σ` was part of the maximality test data.
      exact hgraphSubset hp

/-- Helper for Theorem 5.24.12: equal Euclideanized subdifferential mappings force closed proper
convex functions to differ by an additive real constant. -/
lemma helperForTheorem_5_24_12_equalSubdifferentials_imply_eq_up_to_constant
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction f)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hclosedG : ClosedConvexFunction g)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hEq : ∀ x : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x)) :
    ∃ α : ℝ, ∀ x : Fin n → ℝ,
      g x = f x + ((α : ℝ) : EReal) := by
  -- Reduce the equality case to the stronger one-sided globalization engine.
  exact
    helperForTheorem_5_24_12_primalFiberSubset_implies_eq_up_to_constant
      f g hclosedF hproperF hclosedG hproperG (fun x => (hEq x).subset)

/-- Theorem 5.24.12: the Euclideanized subdifferential mappings of closed proper convex functions
on `ℝ^n` are exactly the maximal cyclically monotone mappings `ρ : ℝ^n ⇉ ℝ^n`. Moreover, a closed
proper convex function is uniquely determined by its Euclideanized subdifferential mapping up to
an additive real constant. -/
theorem isMaximalCyclicallyMonotone_iff_exists_closedProperConvex_subdifferential_eq_and_unique_up_to_constant
    {n : ℕ} (ρ : (Fin n → ℝ) → Set (Fin n → ℝ)) :
    (IsMaximalCyclicallyMonotone ρ ↔
      ∃ f : (Fin n → ℝ) → EReal,
        ClosedConvexFunction f ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
          ∀ x : Fin n → ℝ,
            ρ x = ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) ∧
      (∀ f g : (Fin n → ℝ) → EReal,
        ClosedConvexFunction f →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g →
        (∀ x : Fin n → ℝ,
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) =
            ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x)) →
        ∃ α : ℝ, ∀ x : Fin n → ℝ,
          g x = f x + ((α : ℝ) : EReal)) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hmax
      rcases
          (exists_closedProperConvex_subdifferential_superset_iff_isCyclicallyMonotone
            (ρ := ρ)).2 hmax.1 with
        ⟨f, hclosed, hproper, hsubset⟩
      let σ : (Fin n → ℝ) → Set (Fin n → ℝ) :=
        fun x => ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
      have hσMax : IsMaximalCyclicallyMonotone σ :=
        helperForTheorem_5_24_12_realizedSubdifferential_isMaximal f hclosed hproper
      have hgraphSubset : multivaluedMappingGraph ρ ⊆ multivaluedMappingGraph σ := by
        -- The realization from Theorem 5.24.11 already gives the required graph inclusion.
        intro p hp
        exact hsubset p.1 hp
      have hgraphEq : multivaluedMappingGraph σ = multivaluedMappingGraph ρ :=
        hmax.2 hσMax.1 hgraphSubset
      refine ⟨f, hclosed, hproper, ?_⟩
      intro x
      ext v
      constructor
      · intro hv
        -- Read membership in the graph of `ρ`, then transport it through maximality equality.
        have hp : (x, v) ∈ multivaluedMappingGraph ρ := by
          simpa [multivaluedMappingGraph] using hv
        have hp' : (x, v) ∈ multivaluedMappingGraph σ := by
          rw [hgraphEq]
          exact hp
        simpa [σ, multivaluedMappingGraph] using hp'
      · intro hv
        -- The converse transport along the same graph equality recovers the original fiber.
        have hp : (x, v) ∈ multivaluedMappingGraph σ := by
          simpa [σ, multivaluedMappingGraph] using hv
        have hp' : (x, v) ∈ multivaluedMappingGraph ρ := by
          rw [← hgraphEq]
          exact hp
        simpa [multivaluedMappingGraph] using hp'
    · intro hwitness
      rcases hwitness with ⟨f, hclosed, hproper, hEq⟩
      let σ : (Fin n → ℝ) → Set (Fin n → ℝ) :=
        fun x => ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
      have hσMax : IsMaximalCyclicallyMonotone σ :=
        helperForTheorem_5_24_12_realizedSubdifferential_isMaximal f hclosed hproper
      have hσρ : σ = ρ := by
        -- The witness already identifies the realized subdifferential with `ρ` fiberwise.
        funext x
        exact (hEq x).symm
      exact hσρ ▸ hσMax
  · intro f g hclosedF hproperF hclosedG hproperG hEq
    -- The uniqueness clause is exactly the dedicated additive-constant helper.
    exact
      helperForTheorem_5_24_12_equalSubdifferentials_imply_eq_up_to_constant
        f g hclosedF hproperF hclosedG hproperG hEq

end Section24
end Chap05
