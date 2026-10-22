/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part23
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part9

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Corollary 37.5.1: for the canonical pairing saddle-function attached to `F`, the
four-block graph point `((u, v), (uStar, vStar))` is exactly the packed ordinary subgradient
point `((u, vStar), (-uStar, v))` of the graph function of `F`. -/
lemma helperForCorollary_37_5_1_pairingGraphPoint_iff_packedSubdifferentialGraphPoint
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ) :
    (((u, v), (uStar, vStar)) ∈
        helperForCorollary_37_5_1_productSubdifferentialGraph
          (m := m) (n := n) (convexBifunctionPairing F)) ↔
      (helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n)
          (((u, v), (uStar, vStar))) ∈
        helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) F) := by
  constructor
  · intro hGraph
    rcases
        (by
          simpa [helperForCorollary_37_5_1_productSubdifferentialGraph, productSubdifferentialAt]
            using hGraph) with
      ⟨huStar, hvStar⟩
    have hCenter :
        convexBifunctionPairing F u v =
          (((dotProduct vStar v : ℝ) : EReal) - F u vStar) := by
      -- The second partial of the pairing is exactly the attainment identity at `vStar`.
      exact
        (helperForCorollary_37_5_1_secondPartialMem_iff_pairingAttainment
          (hF := hF) (u := u) (v := v) (vStar := vStar)).1 hvStar
    have hPackedLower :
        ∀ u' x',
          F u' x' - ((dotProduct x' v : ℝ) : EReal) + ((dotProduct u' uStar : ℝ) : EReal) ≥
            F u vStar - ((dotProduct vStar v : ℝ) : EReal) + ((dotProduct u uStar : ℝ) : EReal) := by
      intro u' x'
      have hEndpoint :
          (((dotProduct x' v : ℝ) : EReal) - F u' x') ≤ convexBifunctionPairing F u' v := by
        -- Every primal point contributes one kernel term in the supremum defining the pairing.
        exact helperForLemma33_0_14_endpointKernel_le_convexBifunctionPairing F u' x' v
      have hFirst :
          convexBifunctionPairing F u' v ≤
            convexBifunctionPairing F u v +
              (((dotProduct u' uStar - dotProduct u uStar : ℝ)) : EReal) := by
        have hFirstRaw :
            convexBifunctionPairing F u' v ≤
              convexBifunctionPairing F u v +
                (((∑ i : Fin m, uStar i * (u' i - u i) : ℝ)) : EReal) := by
          simpa [helperForTheorem_37_4_sumERealProducts_subtractedCoordinates_eq_coe_sum] using
            huStar u'
        rw [helperForTheorem_37_4_coe_firstPartialIncrement_eq_finDot_sub] at hFirstRaw
        exact hFirstRaw
      have hBound :
          (((dotProduct x' v : ℝ) : EReal) - F u' x') ≤
            convexBifunctionPairing F u v +
              (((dotProduct u' uStar - dotProduct u uStar : ℝ)) : EReal) := by
        exact le_trans hEndpoint hFirst
      -- Undo the same exact `EReal` normalization to recover the textbook tilted-fiber lower
      -- bound.
      exact
        (helperForCorollary_37_5_1_exactERealKernelTiltNormalization
          (u := u) (v := v) (uStar := uStar) (vStar := vStar) (u' := u') (x' := x')).1 <|
          by simpa [hCenter] using hBound
    have hPacked :
        dotProductEquiv ℝ (Fin (m + n)) (Fin.append (-uStar) v) ∈
          subdifferentialAt (graphFunctionOfBifunction F) (Fin.append u vStar) := by
      -- The packed ordinary subgradient criterion is exactly the tilted-fiber lower bound.
      exact
        (helperForCorollary_37_5_1_packedSubgradientMem_iff_tiltedFiberLowerBound
          (u := u) (v := v) (uStar := uStar) (vStar := vStar)).2 hPackedLower
    simpa [helperForCorollary_37_5_1_packGraphCoordinates,
      helperForCorollary_37_5_1_packedSubdifferentialGraph] using hPacked
  · intro hPackedGraph
    have hPacked :
        dotProductEquiv ℝ (Fin (m + n)) (Fin.append (-uStar) v) ∈
          subdifferentialAt (graphFunctionOfBifunction F) (Fin.append u vStar) := by
      -- Unpack the corrected coordinate shuffle back to the ordinary packed subgradient.
      simpa [helperForCorollary_37_5_1_packGraphCoordinates,
        helperForCorollary_37_5_1_packedSubdifferentialGraph] using hPackedGraph
    have hLower :
        ∀ u' x',
          F u' x' - ((dotProduct x' v : ℝ) : EReal) + ((dotProduct u' uStar : ℝ) : EReal) ≥
            F u vStar - ((dotProduct vStar v : ℝ) : EReal) + ((dotProduct u uStar : ℝ) : EReal) := by
      -- The packed subgradient hypothesis is already equivalent to the tilted-fiber lower bound.
      exact
        (helperForCorollary_37_5_1_packedSubgradientMem_iff_tiltedFiberLowerBound
          (u := u) (v := v) (uStar := uStar) (vStar := vStar)).1 hPacked
    have hCenterLe :
        convexBifunctionPairing F u v ≤
          (((dotProduct vStar v : ℝ) : EReal) - F u vStar) := by
      -- Specialize the tilted-fiber lower bound to the fixed `u`-fiber, convert each pointwise
      -- inequality into a kernel bound, and then take the supremum over that fiber.
      rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
      refine iSup_le ?_
      intro x'
      have hKernel :
          (((dotProduct x' v : ℝ) : EReal) - F u x') ≤
            (((dotProduct vStar v : ℝ) : EReal) - F u vStar) +
              (((dotProduct u uStar - dotProduct u uStar : ℝ)) : EReal) := by
        exact
          (helperForCorollary_37_5_1_exactERealKernelTiltNormalization
            (u := u) (v := v) (uStar := uStar) (vStar := vStar) (u' := u) (x' := x')).2
            (hLower u x')
      simpa using hKernel
    have hCenterGe :
        (((dotProduct vStar v : ℝ) : EReal) - F u vStar) ≤ convexBifunctionPairing F u v := by
      -- The witness `x' = vStar` appears in the supremum defining the pairing slice.
      exact helperForLemma33_0_14_endpointKernel_le_convexBifunctionPairing F u vStar v
    have hCenter :
        convexBifunctionPairing F u v =
          (((dotProduct vStar v : ℝ) : EReal) - F u vStar) := by
      -- The lower bound and the witness value pin down the center exactly.
      exact le_antisymm hCenterLe hCenterGe
    have huStar :
        uStar ∈ partialSubdifferentialInFirstVariable (convexBifunctionPairing F) u v := by
      -- Once the center is identified, the tilted-fiber lower bound reconstructs the first
      -- partial subgradient.
      exact
        helperForCorollary_37_5_1_tiltedFiberLowerBound_implies_pairingFirstPartial
          (u := u) (v := v) (uStar := uStar) (vStar := vStar) hCenter hLower
    have hvStar :
        vStar ∈ partialSubdifferentialInSecondVariable (convexBifunctionPairing F) u v := by
      -- The same center identity is the second-partial attainment criterion.
      exact
        (helperForCorollary_37_5_1_secondPartialMem_iff_pairingAttainment
          (hF := hF) (u := u) (v := v) (vStar := vStar)).2 hCenter
    simpa [helperForCorollary_37_5_1_productSubdifferentialGraph, productSubdifferentialAt] using
      And.intro huStar hvStar

/-- Helper for Corollary 37.5.1: the canonical pairing representative of a closed convex
bifunction is already fixed by both mixed partial closures. -/
lemma helperForCorollary_37_5_1_pairing_fixed_by_partialClosures
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (hQ : Section34Theorem34_2Qualification F) :
    partialClosure₁ (convexBifunctionPairing F) = convexBifunctionPairing F ∧
      partialClosure₂ (convexBifunctionPairing F) = convexBifunctionPairing F := by
  rcases section34_theorem34_2_qualified F hF hQ with
    ⟨_, _, hKernelInOmega, _, hAllPartials⟩
  have hKernelPartials :
      partialClosure₁ (convexBifunctionClosedKernel F) = convexBifunctionClosedKernel F ∧
        partialClosure₂ (convexBifunctionClosedKernel F) = convexBifunctionClosedKernel F := by
    -- The Section 34 canonical kernel lies in its own generated class, so both mixed closures
    -- immediately collapse back to that kernel.
    exact ⟨(hAllPartials (convexBifunctionClosedKernel F) hKernelInOmega).1,
      (hAllPartials (convexBifunctionClosedKernel F) hKernelInOmega).2.1⟩
  -- Rewrite the closed-kernel notation back to the pairing representative used in this corollary.
  simpa [convexBifunctionClosedKernel] using hKernelPartials

/-- Helper for Corollary 37.5.1: generated-class membership forces the given closed saddle kernel
to coincide pointwise with the canonical pairing representative. -/
lemma helperForCorollary_37_5_1_generatedRepresentative_eq_pairing
    (K : SaddleFunction m n)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (hQ : Section34Theorem34_2Qualification F)
    (hKGenerated : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩) :
    K = convexBifunctionPairing F := by
  have hEquivalent :
      saddleEquivalent K (convexBifunctionPairing F) :=
    helperForCorollary_37_5_1_generatedClass_gives_saddleEquivalent
      (K := K) (hF := hF) hKGenerated
  have hPairingPartials :
      partialClosure₁ (convexBifunctionPairing F) = convexBifunctionPairing F ∧
        partialClosure₂ (convexBifunctionPairing F) = convexBifunctionPairing F :=
    helperForCorollary_37_5_1_pairing_fixed_by_partialClosures (hF := hF) hQ
  have hClosure₁ :
      partialClosure₁ K = convexBifunctionPairing F := by
    -- Saddle-equivalent kernels have the same first mixed closure, and the pairing kernel is
    -- itself first-closed.
    exact hEquivalent.2.2.1.trans hPairingPartials.1
  have hClosure₂ :
      partialClosure₂ K = convexBifunctionPairing F := by
    -- The same argument identifies the second mixed closure with the pairing representative.
    exact hEquivalent.2.2.2.trans hPairingPartials.2
  have hLe : K ≤ convexBifunctionPairing F := by
    intro u v
    -- Squeeze `K` above by its first partial closure and then rewrite that closure to the
    -- canonical pairing representative.
    calc
      K u v ≤ partialClosure₁ K u v := helperForText_34_0_1_le_partialClosure₁ K u v
      _ = convexBifunctionPairing F u v := by rw [hClosure₁]
  have hGe : convexBifunctionPairing F ≤ K := by
    intro u v
    -- Squeeze `K` below by its second partial closure and rewrite the closure in the opposite
    -- direction.
    calc
      convexBifunctionPairing F u v = partialClosure₂ K u v := by rw [hClosure₂]
      _ ≤ K u v := helperForText_34_0_1_partialClosure₂_le K u v
  -- Pointwise antisymmetry upgrades the two inequalities to literal equality of saddle kernels.
  exact le_antisymm hLe hGe

/-- Helper for Corollary 37.5.1: once `K` is represented by a closed proper convex bifunction
`F`, the graph of `∂K` should match the ordinary subdifferential graph of
`graphFunctionOfBifunction F` under the corrected swap/sign packed coordinates. -/
lemma helperForCorollary_37_5_1_originalGraphPoint_iff_packedSubdifferentialGraphPoint
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (hQ : Section34Theorem34_2Qualification F)
    (hFproper : IsProperConvexBifunction F)
    (hKGenerated : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩)
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ) :
    (((u, v), (uStar, vStar)) ∈
        helperForCorollary_37_5_1_productSubdifferentialGraph (m := m) (n := n) K) ↔
      (helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n)
          (((u, v), (uStar, vStar))) ∈
        helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) F) := by
  -- Route correction: the packed base point is `(u, vStar)` and the packed dual point is
  -- `(-uStar, v)`, so we rewrite `K` to its canonical pairing representative and then apply
  -- the corrected pairing bridge directly.
  let _ := hKclosed
  let _ := hKproper
  let _ := hFproper
  have hKeq : K = convexBifunctionPairing F :=
    helperForCorollary_37_5_1_generatedRepresentative_eq_pairing
      (K := K) (hF := hF) hQ (hKGenerated := hKGenerated)
  -- After the Section 34 squeeze identifies the two kernels, the graph statement is exactly the
  -- pairing-side graph bridge.
  simpa [hKeq] using
    (helperForCorollary_37_5_1_pairingGraphPoint_iff_packedSubdifferentialGraphPoint
      (hF := hF) (u := u) (v := v) (uStar := uStar) (vStar := vStar))

/-- Helper for Corollary 37.5.1: the ambient packing homeomorphism restricts to a homeomorphism
between the original four-block graph of `∂K` and the packed ordinary subdifferential graph of
`graphFunctionOfBifunction F`. -/
lemma helperForCorollary_37_5_1_restrictedPackHomeomorph
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (hQ : Section34Theorem34_2Qualification F)
    (hFproper : IsProperConvexBifunction F)
    (hKGenerated : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩) :
    ∃ e :
      {p // p ∈ helperForCorollary_37_5_1_productSubdifferentialGraph (m := m) (n := n) K} ≃ₜ
        {q // q ∈ helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) F},
      ∀ p, (e p).1 = helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n) p.1 := by
  rcases
      helperForCorollary_37_5_1_packGraphCoordinates_homeomorph (m := m) (n := n) with
    ⟨ePack, hePack⟩
  have hBridge :
      ∀ p,
        p ∈ helperForCorollary_37_5_1_productSubdifferentialGraph (m := m) (n := n) K ↔
          ePack p ∈ helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) F := by
    intro p
    rcases p with ⟨⟨u, v⟩, ⟨uStar, vStar⟩⟩
    -- The pointwise bridge is exactly the subtype-membership criterion for the restricted map.
    simpa [hePack, helperForCorollary_37_5_1_packGraphCoordinates] using
      helperForCorollary_37_5_1_originalGraphPoint_iff_packedSubdifferentialGraphPoint
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
        (hF := hF) hQ (hFproper := hFproper) (hKGenerated := hKGenerated)
        (u := u) (v := v) (uStar := uStar) (vStar := vStar)
  refine ⟨ePack.subtype
      (p := fun p =>
        p ∈ helperForCorollary_37_5_1_productSubdifferentialGraph (m := m) (n := n) K)
      (q := fun q =>
        q ∈ helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) F)
      hBridge, ?_⟩
  intro p
  -- On the underlying points, the restricted homeomorphism is still the ambient packing map.
  simpa [Homeomorph.subtype, hePack] using congrArg Subtype.val rfl

/-- Corollary 37.5.1: if `K` is a closed proper saddle-function, the graph of `∂K` is closed, and
the textbook map `(u, v, uStar, vStar) ↦ (u - uStar, v + vStar)` is a homeomorphism from that
graph onto `ℝ^m × ℝ^n`. -/
theorem corollary37_5_1_productSubdifferentialGraph_closed_homeomorphic
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hRepresentative : Section37ClosedRepresentativeQualification K hKclosed)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    IsClosed (helperForCorollary_37_5_1_productSubdifferentialGraph (m := m) (n := n) K) ∧
      ∃ h :
        {p // p ∈ helperForCorollary_37_5_1_productSubdifferentialGraph (m := m) (n := n) K} ≃ₜ
          ((Fin m → ℝ) × (Fin n → ℝ)),
        ∀ p, h p = helperForCorollary_37_5_1_bookMap p.1 := by
  rcases
      helperForCorollary_37_5_1_closedProperRepresentativeWithClosedWitness
        (K := K) hKclosed hKproper hRepresentative hGlobal with
    ⟨F, hF, hClosedF, hFproper, hKGenerated⟩
  have hGraphData :
      ClosedConvexFunction (graphFunctionOfBifunction F) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
          (graphFunctionOfBifunction F) :=
    helperForCorollary_37_5_1_graphFunction_closedProperConvex
      (hF := hF) (hClosed := hClosedF) (hFproper := hFproper)
  let packedGraph :
      Set ((Fin (m + n) → ℝ) × (Fin (m + n) → ℝ)) :=
    helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) F
  constructor
  · have hPackedClosed : IsClosed packedGraph := by
      -- Chapter 24 gives closedness of the ordinary subdifferential graph on the packed side.
      exact
        (subdifferential_limit_mem_and_isClosed_graph
          (f := graphFunctionOfBifunction F) hGraphData.1 hGraphData.2).2
    have hPackedPreimageClosed :
        IsClosed
          ((helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n)) ⁻¹' packedGraph) :=
      hPackedClosed.preimage
        (helperForCorollary_37_5_1_packGraphCoordinates_continuous (m := m) (n := n))
    have hGraphEq :
        helperForCorollary_37_5_1_productSubdifferentialGraph (m := m) (n := n) K =
          (helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n)) ⁻¹' packedGraph := by
      ext p
      rcases p with ⟨⟨u, v⟩, ⟨uStar, vStar⟩⟩
      -- This is the corrected Section 37.5 bridge from the product graph to the packed graph.
      simpa [packedGraph] using
        helperForCorollary_37_5_1_originalGraphPoint_iff_packedSubdifferentialGraphPoint
          (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
          (hF := hF) (hGlobal.qualification F hF) (hFproper := hFproper)
          (hKGenerated := hKGenerated)
          (u := u) (v := v) (uStar := uStar) (vStar := vStar)
    simpa [hGraphEq] using hPackedPreimageClosed
  · rcases
        helperForCorollary_37_5_1_restrictedPackHomeomorph
          (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
          (hF := hF) (hGlobal.qualification F hF) (hFproper := hFproper)
          (hKGenerated := hKGenerated) with
      ⟨eGraph, heGraph⟩
    rcases
        subdifferentialGraph_addition_homeomorph
          (f := graphFunctionOfBifunction F) hGraphData.1 hGraphData.2 with
      ⟨eAdd, heAdd⟩
    let h :
        {p // p ∈ helperForCorollary_37_5_1_productSubdifferentialGraph (m := m) (n := n) K} ≃ₜ
          ((Fin m → ℝ) × (Fin n → ℝ)) :=
      eGraph.trans eAdd |>.trans (Fin.appendHomeomorph (X := ℝ) m n).symm
    refine ⟨h, ?_⟩
    intro p
    rcases p with ⟨⟨⟨u, v⟩, ⟨uStar, vStar⟩⟩, hp⟩
    have hPackedPoint :
        (eGraph ⟨((u, v), (uStar, vStar)), hp⟩).1 =
          (Fin.append u vStar, Fin.append (-uStar) v) := by
      simpa [helperForCorollary_37_5_1_packGraphCoordinates] using
        heGraph ⟨((u, v), (uStar, vStar)), hp⟩
    have hAddPoint :
        eAdd (eGraph ⟨((u, v), (uStar, vStar)), hp⟩) =
          Fin.append u vStar + Fin.append (-uStar) v := by
      -- After transport to the packed graph, Corollary 31.5.1 is just the addition map.
      simpa [hPackedPoint] using heAdd (eGraph ⟨((u, v), (uStar, vStar)), hp⟩)
    have hPackedBook :
        (Fin.appendHomeomorph (X := ℝ) m n).symm
            (Fin.append u vStar + Fin.append (-uStar) v) =
          helperForCorollary_37_5_1_bookMap (((u, v), (uStar, vStar))) := by
      -- The corrected packing stores `(vStar, v)`, so commute the second block addition back to
      -- the textbook order before unpacking.
      apply (Fin.appendHomeomorph (X := ℝ) m n).injective
      rw [(Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply]
      ext i
      by_cases hi : i.1 < m
      · simp [helperForCorollary_37_5_1_bookMap, Fin.appendHomeomorph, Fin.append, Fin.addCases,
          hi, sub_eq_add_neg]
      · simp [helperForCorollary_37_5_1_bookMap, Fin.appendHomeomorph, Fin.append, Fin.addCases,
          hi, sub_eq_add_neg, add_comm]
    -- Compose the restricted packing, the packed addition homeomorphism, and the unpacking map.
    simpa [h, hPackedBook] using congrArg ((Fin.appendHomeomorph (X := ℝ) m n).symm) hAddPoint

/-- Helper for Corollary 37.5.3: the origin fiber of any product subdifferential is a closed
convex subset of `ℝ^m × ℝ^n`. -/
lemma helperForCorollary_37_5_3_origin_fiber_closed_convex
    (KStar : SaddleFunction m n) :
    IsClosed (productSubdifferentialAt KStar (0 : Fin m → ℝ) (0 : Fin n → ℝ)) ∧
      Convex ℝ (productSubdifferentialAt KStar (0 : Fin m → ℝ) (0 : Fin n → ℝ)) := by
  have hFirst :=
    helperForText_35_6_5_firstPartial_isClosed_convex
      KStar (0 : Fin m → ℝ) (0 : Fin n → ℝ)
  have hSecond :=
    helperForText_35_6_5_secondPartial_isClosed_convex
      KStar (0 : Fin m → ℝ) (0 : Fin n → ℝ)
  constructor
  · -- Closedness is preserved under products of the two partial fibers at the origin.
    simpa [productSubdifferentialAt] using hFirst.1.prod hSecond.1
  · -- Convexity is preserved under products of the same two origin fibers.
    simpa [productSubdifferentialAt] using hFirst.2.prod hSecond.2

end Section37
end Chap07
