/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part17

section Chap05
section Section24

open scoped ConvexAnalysis
open scoped Topology
open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 5.24.12: equal right derivative extensions on a cutoff interval
`Set.Ioo (0 : ℝ) τ` already force equal value increments between any two points of that segment.
-/
lemma helperForTheorem_5_24_12_translatedLine_incrementEq_on_Ioo_of_rightDerivativeExtensionEq_cutoff
    (F G : (Fin 1 → ℝ) → EReal)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    {τ : ℝ} (hTauPos : 0 < τ)
    (hDomF : ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain F)
    (hDomG : ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain G)
    (hRightEq : ∀ u ∈ Set.Ioo (0 : ℝ) τ,
      rightDerivativeExtension F u = rightDerivativeExtension G u)
    {s t : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) τ) (ht : t ∈ Set.Ioo (0 : ℝ) τ) :
    (F (scalarPoint t)).toReal - (F (scalarPoint s)).toReal =
      (G (scalarPoint t)).toReal - (G (scalarPoint s)).toReal := by
  have hConvRealF :=
    helperForTheorem_5_24_12_scalarToReal_convexOn_Ioo_cutoff F hproperF hTauPos hDomF
  have hConvRealG :=
    helperForTheorem_5_24_12_scalarToReal_convexOn_Ioo_cutoff G hproperG hTauPos hDomG
  have hIntegralF :=
    (convexOn_Ioo_sub_eq_intervalIntegral_rightDerivWithin_and_leftDerivWithin
      (a := 0) (b := τ) hTauPos
      (f := fun u : ℝ => (F (scalarPoint u)).toReal) hConvRealF hs ht).1
  have hIntegralG :=
    (convexOn_Ioo_sub_eq_intervalIntegral_rightDerivWithin_and_leftDerivWithin
      (a := 0) (b := τ) hTauPos
      (f := fun u : ℝ => (G (scalarPoint u)).toReal) hConvRealG hs ht).1
  calc
    (F (scalarPoint t)).toReal - (F (scalarPoint s)).toReal =
        ∫ u in s..t, derivWithin (fun v : ℝ => (F (scalarPoint v)).toReal) (Set.Ioi u) u := hIntegralF
    _ = ∫ u in s..t, (rightDerivativeExtension F u).toReal := by
      -- On the open cutoff interval, the right derivative of the real profile is exactly the
      -- `toReal` image of the extended right derivative.
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro u hu
      have huIoo : u ∈ Set.Ioo (0 : ℝ) τ := by
        constructor
        · exact lt_of_lt_of_le (lt_min hs.1 ht.1) (le_of_lt hu.1)
        · exact lt_of_le_of_lt hu.2 (max_lt hs.2 ht.2)
      exact
        helperForTheorem_5_24_12_derivWithin_scalarToReal_eq_rightDerivativeExtension_toReal_cutoff
          F hproperF hTauPos hDomF huIoo
    _ = ∫ u in s..t, (rightDerivativeExtension G u).toReal := by
      -- Substitute the assumed equality of right derivative extensions pointwise on the interval.
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro u hu
      have huIoo : u ∈ Set.Ioo (0 : ℝ) τ := by
        constructor
        · exact lt_of_lt_of_le (lt_min hs.1 ht.1) (le_of_lt hu.1)
        · exact lt_of_le_of_lt hu.2 (max_lt hs.2 ht.2)
      exact congrArg EReal.toReal (hRightEq u huIoo)
    _ = ∫ u in s..t, derivWithin (fun v : ℝ => (G (scalarPoint v)).toReal) (Set.Ioi u) u := by
      -- The same derivative identification holds for `G`.
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro u hu
      have huIoo : u ∈ Set.Ioo (0 : ℝ) τ := by
        constructor
        · exact lt_of_lt_of_le (lt_min hs.1 ht.1) (le_of_lt hu.1)
        · exact lt_of_le_of_lt hu.2 (max_lt hs.2 ht.2)
      exact
        (helperForTheorem_5_24_12_derivWithin_scalarToReal_eq_rightDerivativeExtension_toReal_cutoff
          G hproperG hTauPos hDomG huIoo).symm
    _ = (G (scalarPoint t)).toReal - (G (scalarPoint s)).toReal := hIntegralG.symm

/-- Helper for Theorem 5.24.12: once two normalized scalar restrictions have the same right
derivative extension on `Set.Ioo (0 : ℝ) τ`, they agree at every interior point of that cutoff
segment. -/
lemma helperForTheorem_5_24_12_translatedLine_rightDerivativeExtensionEq_on_Ioo_and_zero_imply_eq_on_Ioo_cutoff
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    {τ : ℝ} (hTauPos : 0 < τ)
    (hF0 : F (scalarPoint 0) = 0)
    (hG0 : G (scalarPoint 0) = 0)
    (hDomF : ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain F)
    (hDomG : ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain G)
    (hRightEq : ∀ u ∈ Set.Ioo (0 : ℝ) τ,
      rightDerivativeExtension F u = rightDerivativeExtension G u) :
    ∀ t ∈ Set.Ioo (0 : ℝ) τ, F (scalarPoint t) = G (scalarPoint t) := by
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
    -- Every strict-left endpoint `s` gives equal increments by the cutoff increment lemma.
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsCutoff : s ∈ Set.Ioo (0 : ℝ) τ := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hInc :=
      helperForTheorem_5_24_12_translatedLine_incrementEq_on_Ioo_of_rightDerivativeExtensionEq_cutoff
        F G hproperF hproperG hTauPos hDomF hDomG hRightEq hsCutoff ht
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


/-- Helper for Theorem 5.24.12: the scalar fiber inclusion on a cutoff interval `(0,τ)` already
forces equality of the two translated scalar restrictions on that whole initial segment; the case
`τ = 0` is vacuous. -/
lemma helperForTheorem_5_24_12_translatedLine_eq_on_initialSegment_of_primalFiberSubset_allowingZeroCutoff
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    {τ : ℝ} (hTauNonneg : 0 ≤ τ) (_hTauLeOne : τ ≤ 1)
    (hF0 : F (scalarPoint 0) = 0)
    (hG0 : G (scalarPoint 0) = 0)
    (hDomF : ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain F)
    (hTauDomG : τ ∈ scalarEffectiveDomain G)
    (hLineSubset :
      ∀ t : ℝ,
        {ξ : ℝ |
          dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint t)} ⊆
          {ξ : ℝ |
            dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt G (scalarPoint t)}) :
    ∀ u ∈ Set.Ioo (0 : ℝ) τ, F (scalarPoint u) = G (scalarPoint u) := by
  by_cases hTauZero : τ = 0
  · intro u hu
    exfalso
    linarith [hu.1, hu.2]
  · have hTauPos : 0 < τ := lt_of_le_of_ne hTauNonneg (by simpa [eq_comm] using hTauZero)
    have h0DomG : (0 : ℝ) ∈ scalarEffectiveDomain G := by
      -- The normalization at `0` keeps the scalar origin in the effective domain of `G`.
      simp [scalarEffectiveDomain, effectiveDomain_eq, hG0]
    have hConvDomG :
        Convex ℝ (scalarEffectiveDomain G) :=
      helperForTheorem_5_24_1_scalarEffectiveDomain_convex G hproperG
    have hDomG :
        ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain G := by
      intro u hu
      -- Convexity of the scalar effective domain fills in every point between `0` and `τ`.
      exact (hConvDomG.ordConnected.out h0DomG hTauDomG) ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    have hInteriorF :
        ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ interior (scalarEffectiveDomain F) := by
      intro u hu
      -- The whole open cutoff segment lies in the scalar effective domain of `F`.
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hu) (fun v hv => hDomF v hv)
    have hInteriorG :
        ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ interior (scalarEffectiveDomain G) := by
      intro u hu
      -- The same interior-domain argument applies to `G`.
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hu) (fun v hv => hDomG v hv)
    have hBandBounds :
        ∀ u ∈ Set.Ioo (0 : ℝ) τ,
          leftDerivativeExtension G u ≤ leftDerivativeExtension F u ∧
            rightDerivativeExtension F u ≤ rightDerivativeExtension G u := by
      intro u hu
      -- Compare the scalar fibers pointwise on the cutoff segment.
      exact
        helperForTheorem_5_24_12_scalarRestrictionDerivativeBandBounds_of_primalFiberSubset
          F G hclosedF hproperF hclosedG hproperG
          (hInteriorF u hu) (hInteriorG u hu) (hLineSubset u)
    have hDerivativeEq :
        ∀ u ∈ Set.Ioo (0 : ℝ) τ,
          leftDerivativeExtension G u = leftDerivativeExtension F u ∧
            rightDerivativeExtension F u = rightDerivativeExtension G u :=
      helperForTheorem_5_24_12_derivativeBandBounds_on_Ioo_imply_scalarDerivativeExtensionsEq
        F G hclosedF hproperF hclosedG hproperG hTauPos hBandBounds
    -- Once the right derivatives agree on `(0,τ)` and both scalar restrictions are normalized at
    -- `0`, the value gap vanishes on the whole initial segment.
    exact
      helperForTheorem_5_24_12_translatedLine_rightDerivativeExtensionEq_on_Ioo_and_zero_imply_eq_on_Ioo_cutoff
        F G hclosedF hproperF hclosedG hproperG hTauPos hF0 hG0 hDomF hDomG
        (fun u hu => (hDerivativeEq u hu).2)

/-- Helper for Theorem 5.24.12: equality of two translated scalar restrictions on the open cutoff
segment `(0,τ)` propagates to equality at the cutoff endpoint itself. -/
lemma helperForTheorem_5_24_12_translatedLine_cutoffEndpointEquality_of_primalFiberSubset
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    {τ : ℝ} (hTauPos : 0 < τ)
    (hF0 : F (scalarPoint 0) = 0)
    (hG0 : G (scalarPoint 0) = 0)
    (hEqIoo : ∀ u ∈ Set.Ioo (0 : ℝ) τ, F (scalarPoint u) = G (scalarPoint u)) :
    F (scalarPoint τ) = G (scalarPoint τ) := by
  have h0F : (0 : ℝ) ∈ scalarEffectiveDomain F := by
    -- The scalar normalization makes the base point finite for the segment-limit theorem.
    simp [scalarEffectiveDomain, effectiveDomain_eq, hF0]
  have h0G : (0 : ℝ) ∈ scalarEffectiveDomain G := by
    -- The same normalization is available on the `G` side.
    simp [scalarEffectiveDomain, effectiveDomain_eq, hG0]
  let e : EuclideanSpace Real (Fin 1) ≃L[Real] (Fin 1 → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
  let x0E : EuclideanSpace Real (Fin 1) := e.symm (scalarPoint 0)
  let xτE : EuclideanSpace Real (Fin 1) := e.symm (scalarPoint τ)
  have hsegF0 :
      Filter.Tendsto
        (fun t : ℝ => F ((1 - t) • scalarPoint 0 + t • scalarPoint τ))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (F (scalarPoint τ))) := by
    -- Corollary 7.5.1 computes the left limit at the cutoff endpoint along the scalar segment.
    simpa [x0E, xτE, e] using
      (closedProperConvexFunction_eq_limit_along_segment
        (f := F) hclosedF hproperF (x := x0E) h0F xτE)
  have hsegF :
      Filter.Tendsto (fun t : ℝ => F (scalarPoint (t * τ))) (nhdsWithin 1 (Set.Iio 1))
        (nhds (F (scalarPoint τ))) := by
    -- Along the normalized segment, the affine interpolation is exactly `scalarPoint (t * τ)`.
    convert hsegF0 using 1
    funext t
    congr 1
    ext i
    fin_cases i
    simp [scalarPoint, mul_comm, mul_left_comm, mul_assoc]
  have hsegG0 :
      Filter.Tendsto
        (fun t : ℝ => G ((1 - t) • scalarPoint 0 + t • scalarPoint τ))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (G (scalarPoint τ))) := by
    -- The same scalar endpoint limit holds for `G`.
    simpa [x0E, xτE, e] using
      (closedProperConvexFunction_eq_limit_along_segment
        (f := G) hclosedG hproperG (x := x0E) h0G xτE)
  have hsegG :
      Filter.Tendsto (fun t : ℝ => G (scalarPoint (t * τ))) (nhdsWithin 1 (Set.Iio 1))
        (nhds (G (scalarPoint τ))) := by
    -- Again, the interpolating path is just the rescaled scalar point itself.
    convert hsegG0 using 1
    funext t
    congr 1
    ext i
    fin_cases i
    simp [scalarPoint, mul_comm, mul_left_comm, mul_assoc]
  have hEventuallyEq :
      (fun t : ℝ => F (scalarPoint (t * τ))) =ᶠ[nhdsWithin 1 (Set.Iio 1)]
        (fun t : ℝ => G (scalarPoint (t * τ))) := by
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
    have htTau : t * τ ∈ Set.Ioo (0 : ℝ) τ := by
      constructor
      · nlinarith [ht.1, hTauPos]
      · nlinarith [ht.2, hTauPos]
    exact hEqIoo (t * τ) htTau
  have hEqLimitF :
      Filter.Tendsto (fun t : ℝ => F (scalarPoint (t * τ))) (nhdsWithin 1 (Set.Iio 1))
        (nhds (G (scalarPoint τ))) := by
    -- Replace `F` by the eventually equal profile `G` before taking the cutoff-endpoint limit.
    exact Filter.Tendsto.congr' hEventuallyEq.symm hsegG
  -- A `T₂` target has unique limits along the same nontrivial filter.
  exact tendsto_nhds_unique hsegF hEqLimitF

/-- Helper for Theorem 5.24.12: if the target point lies in `dom f`, the translated scalar line
restriction from the anchor `x0` to that point has the same endpoint value for `f` and `g`. -/
lemma helperForTheorem_5_24_12_translatedLine_endpointEquality_of_primalFiberSubset
    {n : ℕ} (f g : (Fin n → ℝ) → EReal) (x0 y : Fin n → ℝ)
    (hx0FiniteF : f x0 ≠ (⊤ : EReal) ∧ f x0 ≠ (⊥ : EReal))
    (hx0FiniteG : g x0 ≠ (⊤ : EReal) ∧ g x0 ≠ (⊥ : EReal))
    (hyDomF : y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
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
    translatedDifferenceFunctionAt f x0 (y - x0) =
      translatedDifferenceFunctionAt g x0 (y - x0) := by
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
  have hA0 : A (scalarPoint 0) = 0 := by
    ext i
    simp [A, scalarPoint]
  have hA1 : A (scalarPoint 1) = y - x0 := by
    ext i
    simp [A, scalarPoint]
  have hDomF0 : (0 : ℝ) ∈ scalarEffectiveDomain F := by
    -- The translated normalization at the scalar origin gives a finite base point.
    simp [scalarEffectiveDomain, effectiveDomain_eq, F, hF0]
  have hDomF1 : (1 : ℝ) ∈ scalarEffectiveDomain F := by
    -- At the scalar endpoint, the translated restriction lands at `y`, which is assumed to lie in
    -- the effective domain of `f`.
    have hyTop : f y ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hyDomF
    have hnegBaseTop : (-f x0) ≠ (⊤ : EReal) := by
      simpa [EReal.neg_eq_top_iff] using hx0FiniteF.2
    have hF1Top : F (scalarPoint 1) ≠ (⊤ : EReal) := by
      rw [show F (scalarPoint 1) = translatedDifferenceFunctionAt f x0 (y - x0) by simp [F, hA1]]
      simpa [translatedDifferenceFunctionAt, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using (EReal.add_ne_top hyTop hnegBaseTop)
    simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top] using
      (lt_top_iff_ne_top.2 hF1Top)
  have hConvDomF : Convex ℝ (scalarEffectiveDomain F) :=
    helperForTheorem_5_24_1_scalarEffectiveDomain_convex F hproperLineF
  have hIccDomF : Set.Icc (0 : ℝ) 1 ⊆ scalarEffectiveDomain F := by
    intro u hu
    have h0 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
    have h1 : 0 ≤ u := hu.1
    have hsum : (1 - u) + u = 1 := by ring
    simpa [smul_eq_mul, scalarPoint] using hConvDomF hDomF0 hDomF1 h0 h1 hsum
  have hDomF :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain F := by
    intro u hu
    exact hIccDomF ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hInteriorF :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ interior (scalarEffectiveDomain F) := by
    intro u hu
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hu) ?_
    intro v hv
    exact hDomF v hv
  have hBandsF :
      ∀ u : ℝ,
        {ξ : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ ∂ F (scalarPoint u)} =
          {ξ : ℝ |
            leftDerivativeExtension F u ≤ ((ξ : ℝ) : EReal) ∧
              (((ξ : ℝ) : EReal) ≤ rightDerivativeExtension F u)} := by
    intro u
    simpa using
      oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
        F hclosedLineF hproperLineF u
  have hDomG :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain G := by
    intro u hu
    have huInteriorF : u ∈ interior (scalarEffectiveDomain F) := hInteriorF u hu
    have hFiniteDirF :=
      helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives F hproperLineF huInteriorF
    let ξ : ℝ :=
      ((leftDerivativeExtension F u).toReal + (rightDerivativeExtension F u).toReal) / 2
    have hMidpointLeF :
        (leftDerivativeExtension F u).toReal ≤ ξ := by
      dsimp [ξ]
      have hLe :
          (((leftDerivativeExtension F u).toReal : ℝ) : EReal) ≤
            (((rightDerivativeExtension F u).toReal : ℝ) : EReal) := by
        calc
          (((leftDerivativeExtension F u).toReal : ℝ) : EReal) = leftDerivativeExtension F u := by
            rw [EReal.coe_toReal hFiniteDirF.2.2.1 hFiniteDirF.2.2.2]
          _ ≤ rightDerivativeExtension F u :=
            helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
              F hproperLineF u
          _ = (((rightDerivativeExtension F u).toReal : ℝ) : EReal) := by
            rw [EReal.coe_toReal hFiniteDirF.1 hFiniteDirF.2.1]
      have hLeReal :
          (leftDerivativeExtension F u).toReal ≤ (rightDerivativeExtension F u).toReal := by
        exact_mod_cast hLe
      linarith
    have hMidpointGeF :
        ξ ≤ (rightDerivativeExtension F u).toReal := by
      dsimp [ξ]
      have hLe :
          (((leftDerivativeExtension F u).toReal : ℝ) : EReal) ≤
            (((rightDerivativeExtension F u).toReal : ℝ) : EReal) := by
        calc
          (((leftDerivativeExtension F u).toReal : ℝ) : EReal) = leftDerivativeExtension F u := by
            rw [EReal.coe_toReal hFiniteDirF.2.2.1 hFiniteDirF.2.2.2]
          _ ≤ rightDerivativeExtension F u :=
            helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
              F hproperLineF u
          _ = (((rightDerivativeExtension F u).toReal : ℝ) : EReal) := by
            rw [EReal.coe_toReal hFiniteDirF.1 hFiniteDirF.2.1]
      have hLeReal :
          (leftDerivativeExtension F u).toReal ≤ (rightDerivativeExtension F u).toReal := by
        exact_mod_cast hLe
      linarith
    have hξMemF :
        dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint u) := by
      have hξMemFSet :
          ξ ∈ {ξ : ℝ |
            dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint u)} := by
        rw [hBandsF u]
        constructor
        · calc
            leftDerivativeExtension F u =
                (((leftDerivativeExtension F u).toReal : ℝ) : EReal) := by
                  rw [EReal.coe_toReal hFiniteDirF.2.2.1 hFiniteDirF.2.2.2]
            _ ≤ ((ξ : ℝ) : EReal) := by
                  exact_mod_cast hMidpointLeF
        · calc
            ((ξ : ℝ) : EReal) ≤ (((rightDerivativeExtension F u).toReal : ℝ) : EReal) := by
                  exact_mod_cast hMidpointGeF
            _ = rightDerivativeExtension F u := by
                  rw [EReal.coe_toReal hFiniteDirF.1 hFiniteDirF.2.1]
      simpa using hξMemFSet
    have hξMemG :
        dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt G (scalarPoint u) :=
      hLineSubset u hξMemF
    have hSubNonemptyG : Set.Nonempty (subdifferentialAt G (scalarPoint u)) := by
      exact ⟨dotProductEquiv ℝ (Fin 1) (scalarPoint ξ), hξMemG⟩
    have hFiniteG :=
      helperForTheorem_23_4_finiteAt_of_subdifferentiable G hproperLineG (scalarPoint u) hSubNonemptyG
    simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top] using
      (lt_top_iff_ne_top.2 hFiniteG.1)
  have hBandBounds :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1,
        leftDerivativeExtension G u ≤ leftDerivativeExtension F u ∧
          rightDerivativeExtension F u ≤ rightDerivativeExtension G u := by
    intro u hu
    -- Compare the scalar fibers at each interior point of the translated segment via the
    -- one-dimensional derivative-band description.
    exact
      helperForTheorem_5_24_12_scalarRestrictionDerivativeBandBounds_of_primalFiberSubset
        F G hclosedLineF hproperLineF hclosedLineG hproperLineG
        (hInteriorF u hu)
        (by
          rw [mem_interior_iff_mem_nhds]
          refine Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hu) ?_
          intro v hv
          exact hDomG v hv)
        (hLineSubset u)
  have hDerivativeEq :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1,
        leftDerivativeExtension G u = leftDerivativeExtension F u ∧
          rightDerivativeExtension F u = rightDerivativeExtension G u :=
    helperForTheorem_5_24_12_derivativeBandBounds_on_Ioo_imply_scalarDerivativeExtensionsEq
      F G hclosedLineF hproperLineF hclosedLineG hproperLineG (by norm_num) hBandBounds
  have hEqIoo :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, F (scalarPoint u) = G (scalarPoint u) := by
    -- Once the right derivative extensions agree on the open segment and both restrictions are
    -- normalized at `0`, the value gap vanishes everywhere on that open segment.
    exact
      helperForTheorem_5_24_12_translatedLine_rightDerivativeExtensionEq_on_Ioo_and_zero_imply_eq_on_Ioo
        F G hclosedLineF hproperLineF hclosedLineG hproperLineG hF0 hG0 hDomF hDomG
        (fun u hu => (hDerivativeEq u hu).2)
  -- Closedness transports the open-segment equality to the endpoint `t = 1`.
  simpa [F, G, hA1] using
    helperForTheorem_5_24_12_translatedLine_eq_on_Ioo_imply_endpoint_equality
      F G hclosedLineF hproperLineF hclosedLineG hproperLineG hF0 hG0 hEqIoo

/-- Helper for Theorem 5.24.12: once the translated endpoint values agree, the common anchor
relation `g x0 = f x0 + α` unfolds that equality into `g y = f y + α`. -/
lemma helperForTheorem_5_24_12_translatedEndpointEquality_implies_valueEqualityAtTarget
    {n : ℕ} (f g : (Fin n → ℝ) → EReal) (x0 y : Fin n → ℝ) (α : ℝ)
    (hx0FiniteF : f x0 ≠ (⊤ : EReal) ∧ f x0 ≠ (⊥ : EReal))
    (hEndpoint :
      translatedDifferenceFunctionAt f x0 (y - x0) =
        translatedDifferenceFunctionAt g x0 (y - x0))
    (hα0 : g x0 = f x0 + ((α : ℝ) : EReal)) :
    g y = f y + ((α : ℝ) : EReal) := by
  let β : ℝ := (f x0).toReal
  have hβ : f x0 = ((β : ℝ) : EReal) := by
    -- Finiteness at the anchor lets us rewrite the base value of `f` as a real constant.
    simp [β, EReal.coe_toReal, hx0FiniteF.1, hx0FiniteF.2]
  have hγ : g x0 = (((β + α : ℝ)) : EReal) := by
    -- The anchor equality therefore rewrites the base value of `g` as the shifted real constant.
    calc
      g x0 = f x0 + ((α : ℝ) : EReal) := hα0
      _ = (((β : ℝ) : EReal) + ((α : ℝ) : EReal)) := by rw [hβ]
      _ = (((β + α : ℝ)) : EReal) := by rw [EReal.coe_add]
  have hEndpoint' :
      f y - ((β : ℝ) : EReal) = g y - (((β + α : ℝ)) : EReal) := by
    -- Unfold the translated differences only at the endpoint vector `y - x0`.
    simpa [translatedDifferenceFunctionAt, hβ, hγ, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm, sub_eq_add_neg]
      using hEndpoint
  calc
    g y = (g y - (((β + α : ℝ)) : EReal)) + (((β + α : ℝ)) : EReal) := by
      rw [EReal.sub_add_cancel]
    _ = (f y - ((β : ℝ) : EReal)) + (((β + α : ℝ)) : EReal) := by rw [← hEndpoint']
    _ = ((f y - ((β : ℝ) : EReal)) + ((β : ℝ) : EReal)) + ((α : ℝ) : EReal) := by
      rw [EReal.coe_add]
      simp [add_assoc]
    _ = f y + ((α : ℝ) : EReal) := by
      rw [EReal.sub_add_cancel]

/-- Helper for Theorem 5.24.12: outside the scalar effective domain of a proper one-dimensional
restriction, the value must already be `⊤` because properness forbids `⊥`. -/
lemma helperForTheorem_5_24_12_scalarValue_eq_top_of_not_mem_scalarEffectiveDomain
    (H : (Fin 1 → ℝ) → EReal)
    {t : ℝ} (htOff : t ∉ scalarEffectiveDomain H) :
    H (scalarPoint t) = (⊤ : EReal) := by
  by_contra hNotTop
  have htLtTop : H (scalarPoint t) < (⊤ : EReal) := (lt_top_iff_ne_top.2 hNotTop)
  have htEff : scalarPoint t ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) H := by
    -- Membership in the effective domain is exactly finiteness below `⊤` on the universal set.
    simpa [effectiveDomain_eq] using
      (show scalarPoint t ∈
          {u : Fin 1 → ℝ | u ∈ (Set.univ : Set (Fin 1 → ℝ)) ∧ H u < (⊤ : EReal)} from
        ⟨by simp, htLtTop⟩)
  have htDom : t ∈ scalarEffectiveDomain H := by
    -- Unwrap the scalar embedding back into the one-dimensional domain predicate.
    simpa [scalarEffectiveDomain] using htEff
  exact htOff htDom

/-- Helper for Theorem 5.24.12: once the translated scalar restriction is finite at `0` but not at
`1`, convexity forces the endpoint `1` to lie strictly to the right of the scalar effective
domain. -/
lemma helperForTheorem_5_24_12_translatedLine_endpoint_rightExterior_of_offDomainTarget
    (F : (Fin 1 → ℝ) → EReal)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hF0 : F (scalarPoint 0) = 0)
    (h1Off : (1 : ℝ) ∉ scalarEffectiveDomain F) :
    IsRightOfScalarEffectiveDomain F 1 := by
  have h0Dom : (0 : ℝ) ∈ scalarEffectiveDomain F := by
    -- The scalar origin is in the effective domain because the translated restriction vanishes there.
    simp [scalarEffectiveDomain, effectiveDomain_eq, hF0]
  have h1NotLeft : ¬ IsLeftOfScalarEffectiveDomain F 1 := by
    -- A point cannot be strictly left of the domain while `0` is already a domain point below it.
    intro hLeft
    exact (not_lt_of_ge (show (0 : ℝ) ≤ 1 by norm_num)) (hLeft 0 h0Dom)
  by_contra h1NotRight
  have h1Dom : (1 : ℝ) ∈ scalarEffectiveDomain F :=
    helperForTheorem_5_24_1_mem_scalarEffectiveDomain_of_not_left_not_right
      F hproperF h1NotLeft h1NotRight
  exact h1Off h1Dom

/-- Helper for Theorem 5.24.12: if `τ` is the supremum of the scalar effective domain of `F`
cut back to `[0,1]`, then every point of `(0,τ)` still lies in the scalar effective domain. -/
lemma helperForTheorem_5_24_12_mem_scalarEffectiveDomain_of_lt_cutoff
    (F : (Fin 1 → ℝ) → EReal)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hF0 : F (scalarPoint 0) = 0)
    {u : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) (sSup (scalarEffectiveDomain F ∩ Set.Icc (0 : ℝ) 1))) :
    u ∈ scalarEffectiveDomain F := by
  let S : Set ℝ := scalarEffectiveDomain F ∩ Set.Icc (0 : ℝ) 1
  have h0DomF : (0 : ℝ) ∈ scalarEffectiveDomain F := by
    -- The normalization at `0` gives the base point of the cutoff set.
    simp [scalarEffectiveDomain, effectiveDomain_eq, hF0]
  have h0MemS : (0 : ℝ) ∈ S := by
    -- The cutoff set is nonempty because it contains the origin.
    exact ⟨h0DomF, by simp⟩
  have hSNonempty : S.Nonempty := ⟨0, h0MemS⟩
  rcases exists_lt_of_lt_csSup hSNonempty hu.2 with ⟨w, hwS, huw⟩
  have hwDomF : w ∈ scalarEffectiveDomain F := hwS.1
  have hConvDomF :
      Convex ℝ (scalarEffectiveDomain F) :=
    helperForTheorem_5_24_1_scalarEffectiveDomain_convex F hproperF
  -- Convexity fills in every point between the known domain points `0` and `w`.
  exact
    (hConvDomF.ordConnected.out h0DomF hwDomF)
      ⟨le_of_lt hu.1, le_of_lt huw⟩

/-- Helper for Theorem 5.24.12: if `τ` is the cutoff supremum of the scalar effective domain of
`F` inside `[0,1]` and `G` stays finite at `1`, then `τ` lies in the scalar effective domain of
`G`, every point of `(0,τ)` lies in the scalar effective domain of `F`, and every point of
`(τ,1)` is strictly to the right of the scalar effective domain of `F`. -/
lemma helperForTheorem_5_24_12_cutoffData_of_offDomainEndpointAssumption
    (F G : (Fin 1 → ℝ) → EReal)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    (hF0 : F (scalarPoint 0) = 0)
    (h1OffF : (1 : ℝ) ∉ scalarEffectiveDomain F)
    (hG0 : G (scalarPoint 0) = 0)
    (h1DomG : (1 : ℝ) ∈ scalarEffectiveDomain G) :
    let τ := sSup (scalarEffectiveDomain F ∩ Set.Icc (0 : ℝ) 1)
    0 ≤ τ ∧ τ ≤ 1 ∧
      (∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain F) ∧
      τ ∈ scalarEffectiveDomain G ∧
      (∀ z ∈ Set.Ioo τ 1, IsRightOfScalarEffectiveDomain F z) := by
  let S : Set ℝ := scalarEffectiveDomain F ∩ Set.Icc (0 : ℝ) 1
  let τ : ℝ := sSup S
  have h0DomF : (0 : ℝ) ∈ scalarEffectiveDomain F := by
    -- The cutoff set starts at the normalized base point.
    simp [scalarEffectiveDomain, effectiveDomain_eq, hF0]
  have h0MemS : (0 : ℝ) ∈ S := by
    -- Hence the cutoff set is nonempty.
    exact ⟨h0DomF, by simp⟩
  have hSNonempty : S.Nonempty := ⟨0, h0MemS⟩
  have hSBddAbove : BddAbove S := ⟨1, by
    intro t ht
    exact ht.2.2⟩
  have hTauNonneg : 0 ≤ τ := by
    -- The supremum dominates the known point `0`.
    exact le_csSup hSBddAbove h0MemS
  have hTauLeOne : τ ≤ 1 := by
    -- Every point of the cutoff set lies in `[0,1]`.
    exact csSup_le hSNonempty (fun t ht => ht.2.2)
  have hInitialSegment :
      ∀ u ∈ Set.Ioo (0 : ℝ) τ, u ∈ scalarEffectiveDomain F := by
    intro u hu
    -- Any strict-left point can be recovered from a slightly larger cutoff witness.
    simpa [τ, S] using
      helperForTheorem_5_24_12_mem_scalarEffectiveDomain_of_lt_cutoff
        F hproperF hF0 hu
  have h0DomG : (0 : ℝ) ∈ scalarEffectiveDomain G := by
    -- The same normalization puts `0` in the scalar effective domain of `G`.
    simp [scalarEffectiveDomain, effectiveDomain_eq, hG0]
  have hConvDomG :
      Convex ℝ (scalarEffectiveDomain G) :=
    helperForTheorem_5_24_1_scalarEffectiveDomain_convex G hproperG
  have hTauDomG : τ ∈ scalarEffectiveDomain G := by
    -- Since `G` is finite at both `0` and `1`, convexity keeps it finite at the cutoff.
    exact (hConvDomG.ordConnected.out h0DomG h1DomG) ⟨hTauNonneg, hTauLeOne⟩
  have hRightAtOne :
      IsRightOfScalarEffectiveDomain F 1 :=
    helperForTheorem_5_24_12_translatedLine_endpoint_rightExterior_of_offDomainTarget
      F hproperF hF0 h1OffF
  have hRightOfCutoff :
      ∀ z ∈ Set.Ioo τ 1, IsRightOfScalarEffectiveDomain F z := by
    intro z hz
    -- Any domain point of `F` lies either at or left of `0`, or else inside the cutoff set `S`.
    intro w hwDomF
    by_cases hwNonpos : w ≤ 0
    · exact lt_of_le_of_lt hwNonpos (lt_of_le_of_lt hTauNonneg hz.1)
    · have hwPos : 0 < w := lt_of_not_ge hwNonpos
      have hwLtOne : w < 1 := hRightAtOne w hwDomF
      have hwMemS : w ∈ S := ⟨hwDomF, ⟨le_of_lt hwPos, le_of_lt hwLtOne⟩⟩
      have hwLeTau : w ≤ τ := le_csSup hSBddAbove hwMemS
      exact lt_of_le_of_lt hwLeTau hz.1
  -- Package the cutoff geometry for the remaining contradiction-at-`τ` argument.
  exact ⟨hTauNonneg, hTauLeOne, hInitialSegment, hTauDomG, hRightOfCutoff⟩

/-- Helper for Theorem 5.24.12: if the scalar effective domain of `F` already fills the open unit
segment and the scalar fibers of `F` are pointwise contained in those of `G`, then closedness
forces the endpoint values at `t = 1` to agree. -/
lemma helperForTheorem_5_24_12_translatedLine_endpointEquality_of_scalarFiberSubset_on_unitInterval
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    (hF0 : F (scalarPoint 0) = 0)
    (hG0 : G (scalarPoint 0) = 0)
    (hDomF : ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain F)
    (hLineSubset :
      ∀ t : ℝ,
        {ξ : ℝ |
          dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint t)} ⊆
          {ξ : ℝ |
            dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt G (scalarPoint t)}) :
    F (scalarPoint 1) = G (scalarPoint 1) := by
  have hInteriorF :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ interior (scalarEffectiveDomain F) := by
    intro u hu
    -- The whole open unit segment is inside `dom F`, so every interior scalar point is an
    -- interior-domain point for the derivative-band comparison.
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hu) ?_
    intro v hv
    exact hDomF v hv
  have hBandsF :
      ∀ u : ℝ,
        {ξ : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ ∂ F (scalarPoint u)} =
          {ξ : ℝ |
            leftDerivativeExtension F u ≤ ((ξ : ℝ) : EReal) ∧
              (((ξ : ℝ) : EReal) ≤ rightDerivativeExtension F u)} := by
    intro u
    -- Theorem 5.24.2 rewrites every scalar fiber as its derivative interval.
    simpa using
      oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
        F hclosedF hproperF u
  have hDomG :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain G := by
    intro u hu
    have huInteriorF : u ∈ interior (scalarEffectiveDomain F) := hInteriorF u hu
    have hFiniteDirF :=
      helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives F hproperF huInteriorF
    let ξ : ℝ :=
      ((leftDerivativeExtension F u).toReal + (rightDerivativeExtension F u).toReal) / 2
    have hMidpointLeF :
        (leftDerivativeExtension F u).toReal ≤ ξ := by
      dsimp [ξ]
      have hLe :
          (((leftDerivativeExtension F u).toReal : ℝ) : EReal) ≤
            (((rightDerivativeExtension F u).toReal : ℝ) : EReal) := by
        calc
          (((leftDerivativeExtension F u).toReal : ℝ) : EReal) = leftDerivativeExtension F u := by
            rw [EReal.coe_toReal hFiniteDirF.2.2.1 hFiniteDirF.2.2.2]
          _ ≤ rightDerivativeExtension F u :=
            helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
              F hproperF u
          _ = (((rightDerivativeExtension F u).toReal : ℝ) : EReal) := by
            rw [EReal.coe_toReal hFiniteDirF.1 hFiniteDirF.2.1]
      have hLeReal :
          (leftDerivativeExtension F u).toReal ≤ (rightDerivativeExtension F u).toReal := by
        exact_mod_cast hLe
      linarith
    have hMidpointGeF :
        ξ ≤ (rightDerivativeExtension F u).toReal := by
      dsimp [ξ]
      have hLe :
          (((leftDerivativeExtension F u).toReal : ℝ) : EReal) ≤
            (((rightDerivativeExtension F u).toReal : ℝ) : EReal) := by
        calc
          (((leftDerivativeExtension F u).toReal : ℝ) : EReal) = leftDerivativeExtension F u := by
            rw [EReal.coe_toReal hFiniteDirF.2.2.1 hFiniteDirF.2.2.2]
          _ ≤ rightDerivativeExtension F u :=
            helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
              F hproperF u
          _ = (((rightDerivativeExtension F u).toReal : ℝ) : EReal) := by
            rw [EReal.coe_toReal hFiniteDirF.1 hFiniteDirF.2.1]
      have hLeReal :
          (leftDerivativeExtension F u).toReal ≤ (rightDerivativeExtension F u).toReal := by
        exact_mod_cast hLe
      linarith
    have hξMemF :
        dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint u) := by
      have hξMemFSet :
          ξ ∈ {ξ : ℝ |
            dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt F (scalarPoint u)} := by
        rw [hBandsF u]
        constructor
        · calc
            leftDerivativeExtension F u =
                (((leftDerivativeExtension F u).toReal : ℝ) : EReal) := by
                  rw [EReal.coe_toReal hFiniteDirF.2.2.1 hFiniteDirF.2.2.2]
            _ ≤ ((ξ : ℝ) : EReal) := by
                  exact_mod_cast hMidpointLeF
        · calc
            ((ξ : ℝ) : EReal) ≤ (((rightDerivativeExtension F u).toReal : ℝ) : EReal) := by
                  exact_mod_cast hMidpointGeF
            _ = rightDerivativeExtension F u := by
                  rw [EReal.coe_toReal hFiniteDirF.1 hFiniteDirF.2.1]
      simpa using hξMemFSet
    have hξMemG :
        dotProductEquiv ℝ (Fin 1) (scalarPoint ξ) ∈ subdifferentialAt G (scalarPoint u) :=
      hLineSubset u hξMemF
    have hSubNonemptyG : Set.Nonempty (subdifferentialAt G (scalarPoint u)) := by
      exact ⟨dotProductEquiv ℝ (Fin 1) (scalarPoint ξ), hξMemG⟩
    have hFiniteG :=
      helperForTheorem_23_4_finiteAt_of_subdifferentiable G hproperG (scalarPoint u) hSubNonemptyG
    -- A nonempty scalar subgradient of `G` at `u` forces `G` to be finite there.
    simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top] using
      (lt_top_iff_ne_top.2 hFiniteG.1)
  have hBandBounds :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1,
        leftDerivativeExtension G u ≤ leftDerivativeExtension F u ∧
          rightDerivativeExtension F u ≤ rightDerivativeExtension G u := by
    intro u hu
    -- Compare the scalar fibers pointwise on the open unit segment.
    exact
      helperForTheorem_5_24_12_scalarRestrictionDerivativeBandBounds_of_primalFiberSubset
        F G hclosedF hproperF hclosedG hproperG
        (hInteriorF u hu)
        (by
          rw [mem_interior_iff_mem_nhds]
          refine Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hu) ?_
          intro v hv
          exact hDomG v hv)
        (hLineSubset u)
  have hDerivativeEq :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1,
        leftDerivativeExtension G u = leftDerivativeExtension F u ∧
          rightDerivativeExtension F u = rightDerivativeExtension G u :=
    helperForTheorem_5_24_12_derivativeBandBounds_on_Ioo_imply_scalarDerivativeExtensionsEq
      F G hclosedF hproperF hclosedG hproperG (by norm_num) hBandBounds
  have hEqIoo :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, F (scalarPoint u) = G (scalarPoint u) := by
    -- Once the right derivatives agree on `(0,1)` and both scalar restrictions are normalized at
    -- `0`, the value gap vanishes on the whole open segment.
    exact
      helperForTheorem_5_24_12_translatedLine_rightDerivativeExtensionEq_on_Ioo_and_zero_imply_eq_on_Ioo
        F G hclosedF hproperF hclosedG hproperG hF0 hG0 hDomF hDomG
        (fun u hu => (hDerivativeEq u hu).2)
  -- Closedness upgrades the open-segment equality to the endpoint `t = 1`.
  exact
    helperForTheorem_5_24_12_translatedLine_eq_on_Ioo_imply_endpoint_equality
      F G hclosedF hproperF hclosedG hproperG hF0 hG0 hEqIoo

/-- Helper for Theorem 5.24.12: if every point strictly to the right of a cutoff `τ < 1` already
lies to the right of the scalar effective domain, then the extended right derivative at `τ` is
forced to be `⊤` by right continuity. -/
lemma helperForTheorem_5_24_12_rightDerivativeExtension_eq_top_at_cutoff_of_rightExteriorTail
    (F : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    {τ : ℝ} (hTauLtOne : τ < 1)
    (hRightOfCutoff : ∀ z ∈ Set.Ioo τ 1, IsRightOfScalarEffectiveDomain F z) :
    rightDerivativeExtension F τ = (⊤ : EReal) := by
  rcases
      oneDimensional_derivativeExtensions_monotone_ordered_and_oneSidedContinuous
        F hclosedF hproperF with
    ⟨_hmonoRightF, _hmonoLeftF, _hfiniteF, _horderedF,
      hRightRightF, _hRightLeftF, _hLeftRightF, _hLeftLeftF⟩
  have hIoo : Set.Ioo τ 1 ∈ nhdsWithin τ (Set.Ioi τ) := by
    -- Because `τ < 1`, a sufficiently small strict-right neighborhood stays inside `(τ,1)`.
    have hIoi : Set.Ioi τ ∈ nhdsWithin τ (Set.Ioi τ) := self_mem_nhdsWithin
    have hIio : Set.Iio (1 : ℝ) ∈ nhdsWithin τ (Set.Ioi τ) :=
      nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio hTauLtOne)
    have hInter : (Set.Ioi τ ∩ Set.Iio (1 : ℝ)) ∈ nhdsWithin τ (Set.Ioi τ) :=
      Filter.inter_mem hIoi hIio
    have hEqSet : Set.Ioo τ 1 = Set.Ioi τ ∩ Set.Iio (1 : ℝ) := by
      ext x
      simp [Set.Ioo, Set.Ioi, Set.Iio]
    simpa [hEqSet] using hInter
  have hEventuallyTop :
      (fun z : ℝ => rightDerivativeExtension F z) =ᶠ[nhdsWithin τ (Set.Ioi τ)]
        fun _ : ℝ => (⊤ : EReal) := by
    -- On the punctured right neighborhood `(τ,1)`, the right derivative is definitionally `⊤`.
    filter_upwards [hIoo] with z hz
    simp [rightDerivativeExtension, hRightOfCutoff z hz]
  have hTopLimit :
      Filter.Tendsto (fun z : ℝ => rightDerivativeExtension F z) (nhdsWithin τ (Set.Ioi τ))
        (nhds (⊤ : EReal)) := by
    exact Filter.Tendsto.congr' hEventuallyTop.symm tendsto_const_nhds
  -- The right limit at `τ` is unique, so the actual right derivative value at `τ` must be `⊤`.
  exact tendsto_nhds_unique (hRightRightF τ) hTopLimit


end Section24
end Chap05
