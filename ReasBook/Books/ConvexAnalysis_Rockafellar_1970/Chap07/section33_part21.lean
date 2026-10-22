/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part20

section Chap07
section Section33

attribute [local instance] Classical.propDecidable

/-- Helper for Corollary33.3.3: the canonical witness's genuine adjoint has the textbook
branchwise dual formula obtained by restricting the concave conjugate of the primal pairing
to the primal domain `C`. -/
lemma helperForCorollary33_3_3_canonicalWitness_dualFormula_split
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_nonempty : C.Nonempty)
    (hF_primalPairing :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        lowerSimpleExtensionOfReal C D K u xStar =
          convexBifunctionPairing (helperForCorollary33_3_3_canonicalWitness C D K) u xStar) :
    ∀ (xStar : Fin n → ℝ) (uStar : Fin m → ℝ),
      genuineConvexBifunctionAdjoint
          (helperForCorollary33_3_3_canonicalWitness C D K) xStar uStar =
        if _hxStar : xStar ∈ D then
          sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
        else ⊥ := by
  intro xStar uStar
  by_cases hxStar : xStar ∈ D
  · -- Step 1: on `D`, the genuine adjoint is the concave conjugate of the primal pairing
    -- section, and the off-`C` branch contributes only `⊤` to the defining infimum.
    calc
      genuineConvexBifunctionAdjoint
          (helperForCorollary33_3_3_canonicalWitness C D K) xStar uStar
          = convexBifunctionAdjointPairing
              (helperForCorollary33_3_3_canonicalWitness C D K) xStar uStar := by
                exact
                  helperForCorollary33_0_40_genuineAdjoint_eq_closureSideAdjointPairing
                    (F := helperForCorollary33_3_3_canonicalWitness C D K) xStar uStar
      _ = concaveConjugate
            (fun u : Fin m → ℝ =>
              convexBifunctionPairing (helperForCorollary33_3_3_canonicalWitness C D K) u xStar)
            uStar := by
              rfl
      _ = iInf (fun u : Fin m → ℝ =>
            ↑(u ⬝ᵥ uStar) + -convexBifunctionPairing
              (helperForCorollary33_3_3_canonicalWitness C D K) u xStar) := by
              rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
      _ = iInf (fun u : Fin m → ℝ =>
            ((↑(u ⬝ᵥ uStar) : EReal) -
              convexBifunctionPairing (helperForCorollary33_3_3_canonicalWitness C D K) u xStar)) := by
              rfl
      _ = iInf (fun u : Fin m → ℝ =>
            ((↑(u ⬝ᵥ uStar) : EReal) - lowerSimpleExtensionOfReal C D K u xStar)) := by
              congr with u
              rw [← hF_primalPairing u xStar]
      _ = iInf (fun u : C => ((↑(↑u ⬝ᵥ uStar - K (↑u) xStar) : EReal))) := by
            calc
              iInf (fun u : Fin m → ℝ =>
                    ((↑(u ⬝ᵥ uStar) : EReal) - lowerSimpleExtensionOfReal C D K u xStar))
                  = iInf (fun u : Fin m → ℝ =>
                      iInf (fun hu : u ∈ C =>
                        ((↑(u ⬝ᵥ uStar) : EReal) - lowerSimpleExtensionOfReal C D K u xStar))) := by
                          congr with u
                          by_cases hu : u ∈ C
                          · simp [hu]
                          · have hOff :
                              ((↑(u ⬝ᵥ uStar) : EReal) - lowerSimpleExtensionOfReal C D K u xStar) = ⊤ := by
                              simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu]
                            simp [hu, hOff]
              _ = iInf (fun u : C =>
                    ((↑(↑u ⬝ᵥ uStar) : EReal) - lowerSimpleExtensionOfReal C D K (↑u) xStar)) := by
                    rw [iInf_subtype']
              _ = iInf (fun u : C => ((↑(↑u ⬝ᵥ uStar - K (↑u) xStar) : EReal))) := by
                    congr with u
                    simp [lowerSimpleExtensionOfReal, lowerSimpleExtension,
                      erealOfRealBifunction, hxStar, u.2]
      _ = sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar)) := by
            rw [sInf_range]
      _ = if hxStar : xStar ∈ D then
            sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
          else ⊥ := by
            simp [hxStar]
  · rcases hC_nonempty with ⟨u0, hu0⟩
    -- Step 2: off `D`, the chosen witness `u₀ ∈ C` makes one infimum term equal `⊥`,
    -- so the whole genuine adjoint section collapses.
    calc
      genuineConvexBifunctionAdjoint
          (helperForCorollary33_3_3_canonicalWitness C D K) xStar uStar
          = convexBifunctionAdjointPairing
              (helperForCorollary33_3_3_canonicalWitness C D K) xStar uStar := by
                exact
                  helperForCorollary33_0_40_genuineAdjoint_eq_closureSideAdjointPairing
                    (F := helperForCorollary33_3_3_canonicalWitness C D K) xStar uStar
      _ = concaveConjugate
            (fun u : Fin m → ℝ =>
              convexBifunctionPairing (helperForCorollary33_3_3_canonicalWitness C D K) u xStar)
            uStar := by
              rfl
      _ = iInf (fun u : Fin m → ℝ =>
            ↑(u ⬝ᵥ uStar) + -convexBifunctionPairing
              (helperForCorollary33_3_3_canonicalWitness C D K) u xStar) := by
              rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
      _ = iInf (fun u : Fin m → ℝ =>
            ((↑(u ⬝ᵥ uStar) : EReal) -
              convexBifunctionPairing (helperForCorollary33_3_3_canonicalWitness C D K) u xStar)) := by
              rfl
      _ = iInf (fun u : Fin m → ℝ =>
            ((↑(u ⬝ᵥ uStar) : EReal) - lowerSimpleExtensionOfReal C D K u xStar)) := by
              congr with u
              rw [← hF_primalPairing u xStar]
      _ = ⊥ := by
            apply le_antisymm
            · refine iInf_le_of_le u0 ?_
              have hTop : lowerSimpleExtensionOfReal C D K u0 xStar = ⊤ := by
                simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu0, hxStar]
              simp [hTop]
            · exact bot_le
      _ = if hxStar : xStar ∈ D then
            sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
          else ⊥ := by
            simp [hxStar]

/-- Helper for Corollary33.3.3: for a fixed `xStar ∈ D`, the affine graph integrand from the
canonical witness formula is lower semicontinuous on `ℝ^(m+n)`, with the `u ∉ C` branch
collapsed to `⊤`. -/
lemma helperForCorollary33_3_3_fixedDual_graphIntegrand_lowerSemicontinuous
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_closed : IsClosed C)
    (hK_cont : ContinuousOn (fun p => K p.1 p.2) (C.prod D))
    (xStar : D) :
    LowerSemicontinuous
      (fun z : Fin (m + n) → ℝ =>
        if (fun i : Fin m => z (Fin.castAdd n i)) ∈ C then
          ↑(((fun j : Fin n => z (Fin.natAdd m j)) ⬝ᵥ ↑xStar) -
              K (fun i : Fin m => z (Fin.castAdd n i)) ↑xStar)
        else (⊤ : EReal)) := by
  let uProj : (Fin (m + n) → ℝ) → (Fin m → ℝ) :=
    fun z i => z (Fin.castAdd n i)
  let xProj : (Fin (m + n) → ℝ) → (Fin n → ℝ) :=
    fun z j => z (Fin.natAdd m j)
  let proj : (Fin (m + n) → ℝ) → (Fin m → ℝ) × (Fin n → ℝ) :=
    fun z => (uProj z, xProj z)
  let affine : ((Fin m → ℝ) × (Fin n → ℝ)) → ℝ :=
    fun p => p.2 ⬝ᵥ ↑xStar - K p.1 ↑xStar
  let affineSubtype : C.prod (Set.univ : Set (Fin n → ℝ)) → EReal :=
    fun p => ↑(affine p.1)
  have hContUProj : Continuous uProj := by
    -- Step 1: the two coordinate projections from `ℝ^(m+n)` to the primal and image blocks
    -- are continuous.
    exact continuous_pi fun i => continuous_apply (Fin.castAdd n i)
  have hContXProj : Continuous xProj := by
    exact continuous_pi fun j => continuous_apply (Fin.natAdd m j)
  have hContProj : Continuous proj := by
    exact hContUProj.prodMk hContXProj
  have hAffineContOn :
      ContinuousOn affine (C.prod (Set.univ : Set (Fin n → ℝ))) := by
    -- Step 2: on `C × ℝ^n`, the fixed-`xStar` tilt is a continuous real affine perturbation
    -- of the frozen kernel section `u ↦ K u xStar`.
    have hContDot :
        Continuous (fun p : (Fin m → ℝ) × (Fin n → ℝ) => dotProduct p.2 ↑xStar) := by
      simpa using
        (continuous_snd.dotProduct
          (continuous_const : Continuous fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (↑xStar : Fin n → ℝ)))
    have hPairContOn :
        ContinuousOn
          (fun p : (Fin m → ℝ) × (Fin n → ℝ) => (p.1, (↑xStar : Fin n → ℝ)))
          (C.prod (Set.univ : Set (Fin n → ℝ))) := by
      exact (continuous_fst.prodMk continuous_const).continuousOn
    have hMapsTo :
        Set.MapsTo
          (fun p : (Fin m → ℝ) × (Fin n → ℝ) => (p.1, (↑xStar : Fin n → ℝ)))
          (C.prod (Set.univ : Set (Fin n → ℝ))) (C.prod D) := by
      intro p hp
      exact ⟨hp.1, xStar.2⟩
    have hKFixedContOn :
        ContinuousOn (fun p : (Fin m → ℝ) × (Fin n → ℝ) => K p.1 ↑xStar)
          (C.prod (Set.univ : Set (Fin n → ℝ))) := by
      simpa [Function.comp] using hK_cont.comp hPairContOn hMapsTo
    exact hContDot.continuousOn.sub hKFixedContOn
  have hAffineSubtypeCont : Continuous affineSubtype := by
    -- Step 3: after restricting to the closed primal strip `C × ℝ^n`, the real affine term
    -- becomes a continuous `EReal`-valued function.
    rw [continuousOn_iff_continuous_restrict] at hAffineContOn
    simpa [affineSubtype, affine] using continuous_coe_real_ereal.comp hAffineContOn
  -- Step 4: every real sublevel set is the continuous preimage of a closed set inside the
  -- closed strip `C × ℝ^n`, transported back along the coordinate projection.
  change LowerSemicontinuous
    (fun z : Fin (m + n) → ℝ =>
      if uProj z ∈ C then ↑(affine (proj z)) else (⊤ : EReal))
  refine (lowerSemicontinuous_iff_closed_sublevel
    (f := fun z : Fin (m + n) → ℝ =>
      if uProj z ∈ C then ↑(affine (proj z)) else (⊤ : EReal))).2 ?_
  intro α
  have hClosedSubtype :
      IsClosed {p : C.prod (Set.univ : Set (Fin n → ℝ)) | affineSubtype p ≤ (α : EReal)} := by
    simpa [Set.preimage, Set.mem_Iic, affineSubtype] using
      (isClosed_Iic : IsClosed (Set.Iic (α : EReal))).preimage hAffineSubtypeCont
  have hClosedImage :
      IsClosed
        (Subtype.val '' {p : C.prod (Set.univ : Set (Fin n → ℝ)) |
          affineSubtype p ≤ (α : EReal)} :
          Set ((Fin m → ℝ) × (Fin n → ℝ))) := by
    exact (hC_closed.prod isClosed_univ).isClosedMap_subtype_val _ hClosedSubtype
  have hSublevelEq :
      {z : Fin (m + n) → ℝ |
          (if uProj z ∈ C then ↑(affine (proj z)) else (⊤ : EReal)) ≤ (α : EReal)} =
        proj ⁻¹' (Subtype.val '' {p : C.prod (Set.univ : Set (Fin n → ℝ)) |
          affineSubtype p ≤ (α : EReal)}) := by
    ext z
    constructor
    · intro hz
      by_cases hu : uProj z ∈ C
      · -- Inside `C`, the sublevel condition is exactly the frozen affine inequality.
        refine ⟨⟨proj z, ⟨hu, by simp⟩⟩, ?_, rfl⟩
        simpa [affineSubtype, affine, proj, hu] using hz
      · -- Outside `C`, the function takes the value `⊤`, so no real sublevel can occur.
        have hTopLe : (⊤ : EReal) ≤ (α : EReal) := by
          have hz' : (if uProj z ∈ C then ↑(affine (proj z)) else (⊤ : EReal)) ≤ (α : EReal) := by
            exact hz
          simp [hu] at hz'
        exact (not_top_le_coe α hTopLe).elim
    · rintro ⟨p, hp, hpEq⟩
      -- Pull the closed-strip witness back to the original graph point and rewrite the value.
      have huEq : uProj z = p.1.1 := by
        simpa [proj, uProj] using (congrArg Prod.fst hpEq).symm
      have hxEq : xProj z = p.1.2 := by
        simpa [proj, xProj] using (congrArg Prod.snd hpEq).symm
      have hu : uProj z ∈ C := by
        rw [huEq]
        exact p.2.1
      have hp' : ↑(affine (proj z)) ≤ (α : EReal) := by
        simpa [affineSubtype, affine, proj, huEq, hxEq] using hp
      simpa [hu] using hp'
  rw [hSublevelEq]
  exact hClosedImage.preimage hContProj

/-- Helper for Corollary33.3.3: the textbook primal formula rewrites the graph function as the
pointwise supremum of the fixed-dual affine integrands indexed by `D`. -/
lemma helperForCorollary33_3_3_graphFunction_eq_iSup_fixedDualIntegrands
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hD_nonempty : D.Nonempty)
    (hF_primalFormula :
      ∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
        F u x =
          if _hu : u ∈ C then
            sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
          else (⊤ : EReal)) :
    let uProj : (Fin (m + n) → ℝ) → (Fin m → ℝ) :=
      fun z i => z (Fin.castAdd n i)
    let xProj : (Fin (m + n) → ℝ) → (Fin n → ℝ) :=
      fun z j => z (Fin.natAdd m j)
    let graphIntegrand : D → (Fin (m + n) → ℝ) → EReal :=
      fun xStar z =>
        if uProj z ∈ C then
          ↑((xProj z) ⬝ᵥ ↑xStar - K (uProj z) ↑xStar)
        else (⊤ : EReal)
    graphFunctionOfBifunction F = fun z => iSup (fun xStar : D => graphIntegrand xStar z) := by
  rcases hD_nonempty with ⟨xStar, hxStar⟩
  let _ : Nonempty D := ⟨⟨xStar, hxStar⟩⟩
  -- Step 1: unfold the coordinate split and compare the graph function pointwise with the
  -- displayed primal formula for `F`.
  dsimp
  funext z
  by_cases hu : (fun i : Fin m => z (Fin.castAdd n i)) ∈ C
  · -- Step 2: on `C`, both sides are the supremum of the same fixed-dual affine family.
    simp [graphFunctionOfBifunction, hF_primalFormula, hu, sSup_range]
  · -- Step 3: off `C`, both sides collapse to `⊤`.
    simp [graphFunctionOfBifunction, hF_primalFormula, hu]

/-- Helper for Corollary33.3.3: the graph function of the canonical witness is the pointwise
supremum of the fixed-dual affine integrands, so lower semicontinuity follows by taking the
supremum of the previously closed sublevel families. -/
lemma helperForCorollary33_3_3_canonicalWitness_graphClosed
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hD_nonempty : D.Nonempty)
    (hC_closed : IsClosed C)
    (hK_cont : ContinuousOn (fun p => K p.1 p.2) (C.prod D))
    (hF_primalFormula :
      ∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
        F u x =
          if _hu : u ∈ C then
            sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
          else (⊤ : EReal)) :
    IsFunctionConvexClosed (graphFunctionOfBifunction F) := by
  let uProj : (Fin (m + n) → ℝ) → (Fin m → ℝ) :=
    fun z i => z (Fin.castAdd n i)
  let xProj : (Fin (m + n) → ℝ) → (Fin n → ℝ) :=
    fun z j => z (Fin.natAdd m j)
  let graphIntegrand : D → (Fin (m + n) → ℝ) → EReal :=
    fun xStar z =>
      if uProj z ∈ C then
        ↑((xProj z) ⬝ᵥ ↑xStar - K (uProj z) ↑xStar)
      else (⊤ : EReal)
  have hD_nonempty' : Nonempty D := by
    rcases hD_nonempty with ⟨xStar, hxStar⟩
    exact ⟨⟨xStar, hxStar⟩⟩
  let _ : Nonempty D := hD_nonempty'
  have hIntegrandLsc :
      ∀ xStar : D, LowerSemicontinuous (graphIntegrand xStar) := by
    intro xStar
    -- Step 1: each fixed-dual integrand is lower semicontinuous by the closed-sublevel
    -- argument proved just above.
    simpa [graphIntegrand, uProj, xProj] using
      helperForCorollary33_3_3_fixedDual_graphIntegrand_lowerSemicontinuous
        (C := C) (D := D) (K := K) hC_closed hK_cont xStar
  have hGraphEq :
      graphFunctionOfBifunction F = fun z => iSup (fun xStar : D => graphIntegrand xStar z) := by
    -- Step 2: rewrite the graph function through the dedicated primal-formula helper so the
    -- lower-semicontinuity step only sees the `iSup` family.
    simpa [graphIntegrand, uProj, xProj] using
      helperForCorollary33_3_3_graphFunction_eq_iSup_fixedDualIntegrands
        (C := C) (D := D) (K := K) (F := F) hD_nonempty hF_primalFormula
  have hGraphLsc : LowerSemicontinuous (graphFunctionOfBifunction F) := by
    -- Step 3: the pointwise supremum of the lower-semicontinuous frozen integrands is still
    -- lower semicontinuous.
    rw [hGraphEq]
    exact lowerSemicontinuous_iSup hIntegrandLsc
  -- Step 4: Section 33 identifies lower semicontinuity with fixedness under the raw convex
  -- closure, which is exactly the graph-closedness predicate used downstream.
  simpa using
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hGraphLsc

/-- Helper for Corollary33.3.3: once a bifunction pairing already identifies `K1` with the
Rockafellar pairing of a sectionwise convex witness and the first-variable concave closure of
`K1` is exact, the standard pairing correspondence upgrades `K1` to a lower closed saddle
function. -/
lemma helperForCorollary33_3_3_lowerClosed_of_pairingCorrespondence
    {m n : ℕ}
    {K1 : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_rock : IsRockafellarConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_primalPairing :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        K1 u xStar = convexBifunctionPairing F u xStar)
    (hK1_firstClosed : IsConcaveClosedInFirst K1) :
    IsLowerClosedSaddleFunction K1 := by
  have hK1_eq : K1 = convexBifunctionPairing F := by
    -- Step 1: repackage the pointwise primal pairing identity as a function equality.
    funext u
    funext xStar
    exact hF_primalPairing u xStar
  rcases
      (convexBifunction_pairing_correspondence (m := m) (n := n)).1 F hF_rock hF_noBot with
    ⟨hK1_shape_raw, hK1_secondClosed_raw, _hSectionFormula⟩
  have hK1_shape : IsConcaveConvexOn Set.univ Set.univ K1 := by
    -- Step 2: the forward pairing correspondence supplies the ambient concave-convex shape.
    simpa [hK1_eq] using hK1_shape_raw
  have hK1_secondClosed : IsConvexClosedInSecond K1 := by
    -- Step 3: the same correspondence also gives the required second-variable convex closure.
    simpa [hK1_eq] using hK1_secondClosed_raw
  have hLowerIdentity :
      convexClosureInSecond (concaveClosureInFirst K1) = K1 :=
    -- Step 4: once both closure coordinates are fixed, the Chapter 33 lower-closed identity
    -- follows directly.
    helperForLemma33_0_43_lowerClosedIdentity_of_firstConcaveClosed_and_secondConvexClosed
      (K := K1) hK1_firstClosed hK1_secondClosed
  -- Step 5: package the shape and closure identity into the lower-closed saddle predicate.
  dsimp [IsLowerClosedSaddleFunction, saddleClosednessPredicates]
  exact Or.inl ⟨hK1_shape, hLowerIdentity⟩

/-- Helper for Corollary33.3.3: if `xStar ∈ D`, then the corresponding first section of the
lower simple extension never takes the value `⊤`. On `C` the section agrees with the finite
kernel value, while off `C` the simple extension collapses to `⊥`. -/
lemma helperForCorollary33_3_3_lowerSimpleExtension_firstSection_ne_top_onDualDomain
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ D) :
    ∀ u : Fin m → ℝ, lowerSimpleExtensionOfReal C D K u xStar ≠ (⊤ : EReal) := by
  intro u
  by_cases hu : u ∈ C
  · -- Step 1: on the primal domain, the lower simple extension is just the finite kernel value.
    simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu, hxStar,
      erealOfRealBifunction]
  · -- Step 2: off the primal domain, the lower simple extension is `⊥`, hence still not `⊤`.
    simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu]

/-- Helper for Corollary33.3.3: isolate the remaining specialized converse bridge for the
canonical witness of the simple extensions. The dependency-closed part of the file already
supplies the explicit primal formula, the no-`⊥` property, and the exact non-`⊥`/non-`⊤`
slice domains of the two simple extensions. -/
lemma helperForCorollary33_3_3_canonicalWitnessPackage
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_nonempty : C.Nonempty)
    (hD_nonempty : D.Nonempty)
    (hC_closed : IsClosed C)
    (hD_closed : IsClosed D)
    (hC_convex : Convex ℝ C)
    (hD_convex : Convex ℝ D)
    (hK_cont : ContinuousOn (fun p => K p.1 p.2) (C.prod D))
    (hK_concaveConvex : IsConcaveConvexOn C D (erealOfRealBifunction K)) :
    let K1 := lowerSimpleExtensionOfReal C D K
    let K2 := upperSimpleExtensionOfReal C D K
    let F := helperForCorollary33_3_3_canonicalWitness C D K
    IsLowerClosedSaddleFunction K1 ∧
      IsRockafellarConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
          IsFunctionConvexClosed (graphFunctionOfBifunction F) ∧
            (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
              K1 u xStar = convexBifunctionPairing F u xStar) ∧
            (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
              K2 u xStar = genuineConvexBifunctionAdjointPairing F u xStar) ∧
              (∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
                F u x =
                  if _hu : u ∈ C then
                    sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
                  else ⊤) ∧
                (∀ (xStar : Fin n → ℝ) (uStar : Fin m → ℝ),
                  genuineConvexBifunctionAdjoint F xStar uStar =
                    if _hxStar : xStar ∈ D then
                      sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
                    else ⊥) ∧
                  convexBifunctionParameterDomain F = C ∧
                    {xStar | ∃ uStar,
                        genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥} = D := by
  let K1 := lowerSimpleExtensionOfReal C D K
  let K2 := upperSimpleExtensionOfReal C D K
  let F := helperForCorollary33_3_3_canonicalWitness C D K
  -- Step 1: mark the geometric assumptions as part of the intended bridge interface; the
  -- specialized converse theorem still has to consume them together with the simple-extension
  -- structure.
  let _ := hC_closed
  let _ := hD_closed
  let _ := hC_convex
  let _ := hD_convex
  let _ := hK_cont
  let _ := hK_concaveConvex
  -- Step 2: the real-valued kernel is finite everywhere after coercion, and its two simple
  -- extensions already satisfy the elementary order/agreement facts on `C × D`.
  have hKernelNoTopOrBot :
      HasNoTopOrBotValuesBifunction (erealOfRealBifunction K) := by
    simpa [erealOfRealBifunction] using
      helperForCorollary33_3_3_realKernel_hasNoTopOrBotValues (K := K)
  have hSimpleExtensionFacts :
      (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ), K1 u xStar ≤ K2 u xStar) ∧
        ∀ ⦃u : Fin m → ℝ⦄ ⦃xStar : Fin n → ℝ⦄,
          u ∈ C →
            xStar ∈ D →
              K1 u xStar = ↑(K u xStar) ∧
                K2 u xStar = ↑(K u xStar) := by
    simpa [K1, K2, lowerSimpleExtensionOfReal, upperSimpleExtensionOfReal,
      erealOfRealBifunction] using
      helperForCorollary33_3_3_realKernel_simpleExtensions_areOrdered_and_agreeOnProduct
        (C := C) (D := D) (K := K)
  -- Step 3: the exact slice domains of the simple extensions are already settled locally.
  have hSimpleExtensionSliceDomains :
      ({u : Fin m → ℝ | ∃ xStar : Fin n → ℝ, K1 u xStar ≠ ⊥} = C) ∧
        ({xStar : Fin n → ℝ | ∃ u : Fin m → ℝ, K2 u xStar ≠ ⊤} = D) := by
    constructor
    · simpa [K1] using
        helperForCorollary33_3_3_lowerSimpleExtensionOfReal_nonbotSlice_set_eq
          (C := C) (D := D) (K := K) hD_nonempty
    · simpa [K2] using
        helperForCorollary33_3_3_upperSimpleExtensionOfReal_nontopSlice_set_eq
          (C := C) (D := D) (K := K) hC_nonempty
  -- Step 4: the canonical witness already carries the explicit textbook primal formula, hence
  -- also the easy no-`⊥` and parameter-domain inclusion facts.
  have hF_noBot : HasNoBotValuesBifunction F := by
    simpa [F] using
      helperForCorollary33_3_3_canonicalWitness_hasNoBotValues
        (C := C) (D := D) (K := K) hD_nonempty
  have hF_primalFormula :
      ∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
        F u x =
          if hu : u ∈ C then
            sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
          else ⊤ := by
    intro u x
    simpa [F] using
      helperForCorollary33_3_3_canonicalWitness_primalFormula
        (C := C) (D := D) (K := K) u x
  have hF_parameterDomain_subset : convexBifunctionParameterDomain F ⊆ C := by
    simpa [F] using
      helperForCorollary33_3_3_canonicalWitness_parameterDomain_subset
        (C := C) (D := D) (K := K)
  -- Step 5: the direct sectionwise part of the witness package is already available: every
  -- section is convex-closed, and the off-`C` branch of the primal pairing has the expected
  -- collapsed value.
  have hF_sectionClosureExact :
      ∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
        convexFunctionClosure (F u) x = F u x := by
    intro u x
    simpa [F] using
      helperForCorollary33_3_3_canonicalWitness_sectionConvexClosure_exact
        (C := C) (D := D) (K := K) hD_nonempty u x
  have hF_primalPairing_offC :
      ∀ ⦃u : Fin m → ℝ⦄, u ∉ C →
        ∀ xStar : Fin n → ℝ, convexBifunctionPairing F u xStar = K1 u xStar := by
    intro u hu xStar
    simpa [F, K1] using
      helperForCorollary33_3_3_canonicalWitness_primalPairing_eq_lowerSimpleExtension_off_domain
        (C := C) (D := D) (K := K) hu xStar
  have hSolvedPrefix :
      HasNoTopOrBotValuesBifunction (erealOfRealBifunction K) ∧
        (∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
          F u x =
            if hu : u ∈ C then
              sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
            else ⊤) ∧
          HasNoBotValuesBifunction F ∧
            convexBifunctionParameterDomain F ⊆ C ∧
              (∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
                convexFunctionClosure (F u) x = F u x) ∧
                (∀ ⦃u : Fin m → ℝ⦄, u ∉ C →
                  ∀ xStar : Fin n → ℝ, convexBifunctionPairing F u xStar = K1 u xStar) := by
    exact
      ⟨hKernelNoTopOrBot, hF_primalFormula, hF_noBot, hF_parameterDomain_subset,
        hF_sectionClosureExact, hF_primalPairing_offC⟩
  let _ := hSimpleExtensionFacts
  let _ := hSimpleExtensionSliceDomains
  let _ := hSolvedPrefix
  -- Step 6: the primal pairing identity is now fully settled, including the previously
  -- missing on-`C` Fenchel-Moreau branch.
  have hF_primalPairing :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        K1 u xStar = convexBifunctionPairing F u xStar := by
    intro u xStar
    symm
    simpa [F, K1] using
      helperForCorollary33_3_3_canonicalWitness_primalPairing_eq_lowerSimpleExtension
        (C := C) (D := D) (K := K) hD_closed hD_convex hK_cont hK_concaveConvex u xStar
  -- Step 7: the same primal identity now yields the genuine Rockafellar convexity package for
  -- the canonical witness, because the lower simple extension has concave first-variable
  -- sections and each canonical witness section is a convex conjugate.
  have hK1_firstSectionsConcave :
      ∀ xStar : Fin n → ℝ,
        IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K1 u xStar) := by
    intro xStar
    simpa [K1] using
      helperForCorollary33_3_3_lowerSimpleExtension_firstSections_areConcave
        (C := C) (D := D) (K := K) hC_convex hK_concaveConvex xStar
  have hF_sectionwiseConvex : IsRockafellarSectionwiseConvexBifunction F := by
    intro u
    by_cases hu : u ∈ C
    · rcases hD_nonempty with ⟨xStar, hxStar⟩
      -- Step 7a: on `C`, the defining section is a convex conjugate with a finite point.
      have hPoint :
          lowerSimpleExtensionOfReal C D K u xStar ≠ (⊤ : EReal) := by
        have hValue :
            lowerSimpleExtensionOfReal C D K u xStar = ↑(K u xStar) := by
          simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu, hxStar,
            erealOfRealBifunction]
        rw [hValue]
        exact EReal.coe_ne_top (K u xStar)
      simpa [F] using
        (helperForTheorem33_1_convexConjugate_isERealConvexOn_of_point
          (f := lowerSimpleExtensionOfReal C D K u) (x₀ := xStar) hPoint)
    · -- Step 7b: off `C`, the explicit primal formula makes the whole section constantly `⊤`.
      intro x y _ _ a b ha hb hab _
      have hSectionTop : F u = fun _ : Fin n → ℝ => (⊤ : EReal) := by
        funext x
        simpa [hu] using hF_primalFormula u x
      have hRightTop :
          (a : EReal) * F u x + (b : EReal) * F u y = (⊤ : EReal) := by
        have hEqx : F u x = (⊤ : EReal) := by simp [hSectionTop]
        have hEqy : F u y = (⊤ : EReal) := by simp [hSectionTop]
        rw [hEqx, hEqy]
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          simp [ha0, hb1]
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          by_cases hb0 : b = 0
          · have hbTerm : ((b : EReal) * (⊤ : EReal)) = 0 := by simp [hb0]
            rw [EReal.mul_top_of_pos (by exact_mod_cast ha_pos), hbTerm]
            simp
          · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
            rw [EReal.mul_top_of_pos (by exact_mod_cast ha_pos),
              EReal.mul_top_of_pos (by exact_mod_cast hb_pos)]
            simp
      have hLeftTop : F u (a • x + b • y) = (⊤ : EReal) := by
        simp [hSectionTop]
      rw [hLeftTop, hRightTop]
  have hF_pairingConcave : HasConcaveParameterConvexPairing F := by
    intro xStar
    have hEq : (fun u : Fin m → ℝ => convexBifunctionPairing F u xStar) =
        (fun u : Fin m → ℝ => K1 u xStar) := by
      funext u
      exact (hF_primalPairing u xStar).symm
    simpa [hEq] using hK1_firstSectionsConcave xStar
  have hF_rock : IsRockafellarConvexBifunction F := ⟨hF_sectionwiseConvex, hF_pairingConcave⟩
  have hOffDualFirstClosure :
      ∀ ⦃u : Fin m → ℝ⦄ ⦃xStar : Fin n → ℝ⦄, xStar ∉ D →
        concaveClosureInFirst K1 u xStar = K1 u xStar := by
    intro u xStar hxStar
    simpa [K1] using
      helperForCorollary33_3_3_offDualDomain_lowerSimpleExtension_firstClosure_eq
        (C := C) (D := D) (K := K) hC_closed hxStar u
  have hOnDualFirstClosure :
      ∀ ⦃u : Fin m → ℝ⦄ ⦃xStar : Fin n → ℝ⦄, xStar ∈ D →
        concaveClosureInFirst K1 u xStar = K1 u xStar := by
    intro u xStar hxStar
    simpa [K1] using
      helperForCorollary33_3_3_onDualDomain_lowerSimpleExtension_firstClosure_eq
        (C := C) (D := D) (K := K) hC_closed hK_cont hxStar u
  let _ := hF_rock
  let _ := hOnDualFirstClosure
  let _ := hOffDualFirstClosure
  -- Step 8: the corrected split route finishes the entire dual side. On `D`, the genuine
  -- adjoint is the concave conjugate of the primal section, so biconjugation collapses back to
  -- `K1` via `hOnDualFirstClosure`; off `D`, the genuine adjoint section is identically `⊥`,
  -- so the genuine adjoint pairing is identically `⊤`.
  have hF_dualFormula :
      ∀ (xStar : Fin n → ℝ) (uStar : Fin m → ℝ),
        genuineConvexBifunctionAdjoint F xStar uStar =
          if hxStar : xStar ∈ D then
            sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
          else ⊥ := by
    simpa [F, K1] using
      helperForCorollary33_3_3_canonicalWitness_dualFormula_split
        (C := C) (D := D) (K := K) hC_nonempty hF_primalPairing
  have hF_dualPairing :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        K2 u xStar = genuineConvexBifunctionAdjointPairing F u xStar := by
    intro u xStar
    by_cases hxStar : xStar ∈ D
    · have hAdjointAsClosure :
          ∀ uStar : Fin m → ℝ,
            genuineConvexBifunctionAdjoint F xStar uStar =
              concaveConjugate (fun u' : Fin m → ℝ => K1 u' xStar) uStar := by
        intro uStar
        -- Step 8a: on `D`, replace the genuine adjoint by the closure-side pairing and
        -- then rewrite the primal pairing section through `K1`.
        calc
          genuineConvexBifunctionAdjoint F xStar uStar =
              convexBifunctionAdjointPairing F xStar uStar := by
                exact
                  helperForCorollary33_0_40_genuineAdjoint_eq_closureSideAdjointPairing
                    (F := F) xStar uStar
          _ = concaveConjugate
                (fun u' : Fin m → ℝ => convexBifunctionPairing F u' xStar) uStar := by
                  rfl
          _ = concaveConjugate (fun u' : Fin m → ℝ => K1 u' xStar) uStar := by
                congr 1
                funext u'
                exact (hF_primalPairing u' xStar).symm
      have hK1_sectionNoTop :
          ∀ u' : Fin m → ℝ, K1 u' xStar ≠ ⊤ := by
        intro u'
        -- Step 8a.0: reuse the dedicated on-`D` finiteness helper instead of reproving the
        -- same sectionwise fact inside each closure conversion.
        simpa [K1] using
          helperForCorollary33_3_3_lowerSimpleExtension_firstSection_ne_top_onDualDomain
            (C := C) (D := D) (K := K) (xStar := xStar) hxStar u'
      calc
        K2 u xStar = K1 u xStar := by
          by_cases hu : u ∈ C
          · simp [K1, K2, lowerSimpleExtensionOfReal, upperSimpleExtensionOfReal,
              lowerSimpleExtension, upperSimpleExtension, hu, hxStar]
          · simp [K1, K2, lowerSimpleExtensionOfReal, upperSimpleExtensionOfReal,
              lowerSimpleExtension, upperSimpleExtension, hu, hxStar]
        _ = concaveClosureInFirst K1 u xStar := by
          symm
          exact hOnDualFirstClosure hxStar
        _ = functionConcaveClosure (fun u' : Fin m → ℝ => K1 u' xStar) u := by
          rfl
        _ = concaveClosure (fun u' : Fin m → ℝ => K1 u' xStar) u := by
          have hNegNoBot :
              ∀ u' : Fin m → ℝ, (fun z : Fin m → ℝ => -K1 z xStar) u' ≠ (⊥ : EReal) := by
            intro u'
            simpa using hK1_sectionNoTop u'
          -- Step 8a.i: for sections with no `⊤` values, the Chapter 6 concave closure equals
          -- the Section 33 upper-semicontinuous concave regularization.
          calc
            functionConcaveClosure (fun u' : Fin m → ℝ => K1 u' xStar) u
                = -functionConvexClosure (fun z : Fin m → ℝ => -K1 z xStar) u := by
                    simpa using
                      congrFun
                        (helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg
                          (g := fun u' : Fin m → ℝ => K1 u' xStar))
                        u
            _ = -convexClosure (fun z : Fin m → ℝ => -K1 z xStar) u := by
                  congr 1
                  simpa [convexClosure] using
                    congrFun
                      (helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
                        (f := fun z : Fin m → ℝ => -K1 z xStar) hNegNoBot)
                      u
            _ = concaveClosure (fun u' : Fin m → ℝ => K1 u' xStar) u := by
                  symm
                  simpa using
                    congrFun
                      (concaveClosure_eq_neg_convexClosure_neg
                        (g := fun u' : Fin m → ℝ => K1 u' xStar))
                      u
        _ = concaveConjugate (concaveConjugate (fun u' : Fin m → ℝ => K1 u' xStar)) u := by
          symm
          simpa using
            congrFun
              (concaveConjugate_biconjugate_eq_concaveClosure
                (g := fun u' : Fin m → ℝ => K1 u' xStar)
                (hg :=
                  helperForCorollary33_3_3_concaveFunction_of_firstSectionConcavity
                    (K1 := K1) (xStar := xStar) (hSection := hK1_firstSectionsConcave xStar)
                    (hNoTop := hK1_sectionNoTop)))
              u
        _ = concaveConjugate (genuineConvexBifunctionAdjoint F xStar) u := by
          congr 1
          funext uStar
          symm
          exact hAdjointAsClosure uStar
        _ = genuineConvexBifunctionAdjointPairing F u xStar := by
          symm
          exact
            helperForCorollary33_0_40_genuinePairing_eq_concaveConjugate_genuineAdjoint
              (F := F) u xStar
    · have hAllBot :
          ∀ uStar : Fin m → ℝ, genuineConvexBifunctionAdjoint F xStar uStar = ⊥ := by
        intro uStar
        simpa [hxStar] using hF_dualFormula xStar uStar
      -- Step 8b: off `D`, the genuine adjoint section is constantly `⊥`, so its pairing is
      -- constantly `⊤`, which matches the upper simple extension.
      calc
        K2 u xStar = ⊤ := by
          by_cases hu : u ∈ C
          · simp [K2, upperSimpleExtensionOfReal, upperSimpleExtension, hxStar]
          · simp [K2, upperSimpleExtensionOfReal, upperSimpleExtension, hxStar]
        _ = genuineConvexBifunctionAdjointPairing F u xStar := by
          symm
          exact
            helperForLemma33_0_37_genuineAdjointPairing_eq_top_of_allBotAdjointSection
              (F := F) (xStar := xStar) hAllBot u
  have hF_adjDom_subset :
      {xStar | ∃ uStar, genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥} ⊆ D := by
    exact
      helperForCorollary33_3_3_genuineAdjointDomain_subset_of_dualFormula
        (C := C) (D := D) (K := K) (F := F) hF_dualFormula
  have hF_adjDom :
      {xStar | ∃ uStar, genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥} = D := by
    ext xStar
    constructor
    · intro hxStar
      exact hF_adjDom_subset hxStar
    · intro hxStar
      by_cases hExists : ∃ uStar, genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥
      · exact hExists
      · push_neg at hExists
        rcases hC_nonempty with ⟨u0, hu0⟩
        have hPairTop :
            genuineConvexBifunctionAdjointPairing F u0 xStar = ⊤ :=
          helperForLemma33_0_37_genuineAdjointPairing_eq_top_of_allBotAdjointSection
            (F := F) (xStar := xStar) hExists u0
        have hK2Finite : K2 u0 xStar = ↑(K u0 xStar) := by
          simp [K2, upperSimpleExtensionOfReal, upperSimpleExtension, erealOfRealBifunction,
            hu0, hxStar]
        have hNotTop : K2 u0 xStar ≠ ⊤ := by
          rw [hK2Finite]
          exact EReal.coe_ne_top (K u0 xStar)
        have hEq := hF_dualPairing u0 xStar
        rw [hPairTop] at hEq
        exfalso
        exact hNotTop hEq
  -- Route correction: the false global identity
  -- `K2 = concaveClosureInFirst K1` has now been fully replaced by the correct split
  -- dual package `hF_dualFormula`, `hF_dualPairing`, and `hF_adjDom`.
  have hSolvedDualPackage :
      (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        K2 u xStar = genuineConvexBifunctionAdjointPairing F u xStar) ∧
        (∀ (xStar : Fin n → ℝ) (uStar : Fin m → ℝ),
          genuineConvexBifunctionAdjoint F xStar uStar =
            if hxStar : xStar ∈ D then
              sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
            else ⊥) ∧
          ({xStar | ∃ uStar, genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥} = D) := by
    exact ⟨hF_dualPairing, hF_dualFormula, hF_adjDom⟩
  let _ := hSolvedDualPackage
  have hGraphClosedAndLowerClosed :
      IsLowerClosedSaddleFunction K1 ∧
        IsFunctionConvexClosed (graphFunctionOfBifunction F) := by
    have hK1_firstClosed : IsConcaveClosedInFirst K1 := by
      -- Step 1: the split first-coordinate closure formulas already show that every frozen
      -- first section of `K1` is fixed by the Section 33 concave closure.
      unfold IsConcaveClosedInFirst
      funext u
      funext xStar
      by_cases hxStar : xStar ∈ D
      · exact (hOnDualFirstClosure hxStar).symm
      · exact (hOffDualFirstClosure hxStar).symm
    have hLowerClosed : IsLowerClosedSaddleFunction K1 := by
      -- Step 2: the dedicated pairing helper now packages the lower-closed bridge in one
      -- reusable step.
      exact
        helperForCorollary33_3_3_lowerClosed_of_pairingCorrespondence
          (K1 := K1) (F := F) hF_rock hF_noBot hF_primalPairing hK1_firstClosed
    have hF_graphClosed : IsFunctionConvexClosed (graphFunctionOfBifunction F) := by
      -- Step 3: the graph function is the supremum of the fixed-dual affine integrands from
      -- the textbook primal formula, so the dedicated lower-semicontinuity helper closes the
      -- Section 33 graph-closure predicate directly.
      exact
        helperForCorollary33_3_3_canonicalWitness_graphClosed
          (C := C) (D := D) (K := K) (F := F)
          hD_nonempty hC_closed hK_cont hF_primalFormula
    exact ⟨hLowerClosed, hF_graphClosed⟩
  rcases hGraphClosedAndLowerClosed with ⟨hLowerClosed, hF_graphClosed⟩
  exact ⟨hLowerClosed, hF_rock, hF_noBot, hF_graphClosed, hF_primalPairing,
    hF_dualPairing, hF_primalFormula, hF_dualFormula,
    helperForCorollary33_3_3_parameterDomain_eq_of_primalPairing_and_nonbotSlice
      (C := C) (K1 := K1) (F := F)
      hSimpleExtensionSliceDomains.1 hF_parameterDomain_subset hF_primalPairing,
    hF_adjDom⟩

/-- Helper for Corollary33.3.3: once one bifunction satisfies the full textbook package, the
displayed primal formula determines the witness uniquely. -/
lemma helperForCorollary33_3_3_existsUniqueWitness_of_fullPackage
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {K1 K2 : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_rock : IsRockafellarConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_graphClosed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hF_primalPairing :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        K1 u xStar = convexBifunctionPairing F u xStar)
    (hF_dualPairing :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        K2 u xStar = genuineConvexBifunctionAdjointPairing F u xStar)
    (hF_primalFormula :
      ∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
        F u x =
          if _hu : u ∈ C then
            sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
          else ⊤)
    (hF_dualFormula :
      ∀ (xStar : Fin n → ℝ) (uStar : Fin m → ℝ),
        genuineConvexBifunctionAdjoint F xStar uStar =
          if _hxStar : xStar ∈ D then
            sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
          else ⊥)
    (hF_dom : convexBifunctionParameterDomain F = C)
    (hF_adjDom :
      {xStar | ∃ uStar, genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥} = D) :
    ∃! G,
      IsRockafellarConvexBifunction G ∧
        HasNoBotValuesBifunction G ∧
          IsFunctionConvexClosed (graphFunctionOfBifunction G) ∧
            (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
              K1 u xStar = convexBifunctionPairing G u xStar) ∧
            (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
              K2 u xStar = genuineConvexBifunctionAdjointPairing G u xStar) ∧
              (∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
                G u x =
                  if _hu : u ∈ C then
                    sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
                  else ⊤) ∧
                (∀ (xStar : Fin n → ℝ) (uStar : Fin m → ℝ),
                  genuineConvexBifunctionAdjoint G xStar uStar =
                    if _hxStar : xStar ∈ D then
                      sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
                    else ⊥) ∧
                  convexBifunctionParameterDomain G = C ∧
                    {xStar | ∃ uStar,
                        genuineConvexBifunctionAdjoint G xStar uStar ≠ ⊥} = D := by
  -- Step 1: use the supplied witness `F` to populate the existence half of the `∃!` claim.
  refine ⟨F, ?_, ?_⟩
  · exact ⟨hF_rock, hF_noBot, hF_graphClosed, hF_primalPairing, hF_dualPairing,
      hF_primalFormula, hF_dualFormula, hF_dom, hF_adjDom⟩
  · intro G hG
    rcases hG with
      ⟨_hG_rock, _hG_noBot, _hG_graphClosed, _hG_primalPairing, _hG_dualPairing,
        hG_primalFormula, _hG_dualFormula, _hG_dom, _hG_adjDom⟩
    -- Step 2: the explicit primal formula already determines the bifunction pointwise.
    exact
      helperForCorollary33_3_3_unique_of_primalFormula
        (C := C) (D := D) (K := K) (F := G) (G := F) hG_primalFormula hF_primalFormula

/-- Compatibility wrapper so the proof pipeline can target Corollary 33.3.3 in the
earliest dependency-closed split file. The actual packaged theorem is reused later
verbatim. -/
theorem «Corollary33.3.3» :
    ∀ {m n : ℕ}
      {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
      {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ},
      C.Nonempty →
        D.Nonempty →
          IsClosed C →
            IsClosed D →
              Convex ℝ C →
                Convex ℝ D →
                  ContinuousOn (fun p => K p.1 p.2) (C.prod D) →
                    IsConcaveConvexOn C D (erealOfRealBifunction K) →
                      let K1 := lowerSimpleExtensionOfReal C D K
                      let K2 := upperSimpleExtensionOfReal C D K
                      IsLowerClosedSaddleFunction K1 ∧
                        ∃! F,
                          IsRockafellarConvexBifunction F ∧
                            HasNoBotValuesBifunction F ∧
                              IsFunctionConvexClosed (graphFunctionOfBifunction F) ∧
                                (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
                                  K1 u xStar = convexBifunctionPairing F u xStar) ∧
                                  (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
                                    K2 u xStar = genuineConvexBifunctionAdjointPairing F u xStar) ∧
                                    (∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
                                      F u x =
                  if _hu : u ∈ C then
                                          sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
                                        else ⊤) ∧
                                      (∀ (xStar : Fin n → ℝ) (uStar : Fin m → ℝ),
                                        genuineConvexBifunctionAdjoint F xStar uStar =
                    if _hxStar : xStar ∈ D then
                                            sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
                                          else ⊥) ∧
                                        convexBifunctionParameterDomain F = C ∧
                                          {xStar | ∃ uStar,
                                              genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥} = D :=
  by
    intro m n C D K hC_nonempty hD_nonempty hC_closed hD_closed hC_convex hD_convex hK_cont
      hK_concaveConvex
    -- Step 1: name the two simple extensions and the canonical witness so the extracted
    -- witness-package helper can be applied literally to the textbook objects.
    let K1 := lowerSimpleExtensionOfReal C D K
    let K2 := upperSimpleExtensionOfReal C D K
    let F := helperForCorollary33_3_3_canonicalWitness C D K
    -- Step 2: invoke the extracted canonical-witness bridge. The only remaining unresolved
    -- work is concentrated in that helper; the present theorem only packages uniqueness once
    -- the witness data are available.
    have hCanonicalWitnessPackage :
        IsLowerClosedSaddleFunction K1 ∧
          IsRockafellarConvexBifunction F ∧
            HasNoBotValuesBifunction F ∧
              IsFunctionConvexClosed (graphFunctionOfBifunction F) ∧
                (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
                  K1 u xStar = convexBifunctionPairing F u xStar) ∧
                (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
                  K2 u xStar = genuineConvexBifunctionAdjointPairing F u xStar) ∧
                  (∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
                    F u x =
                                        if _hu : u ∈ C then
                        sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
                      else ⊤) ∧
                    (∀ (xStar : Fin n → ℝ) (uStar : Fin m → ℝ),
                      genuineConvexBifunctionAdjoint F xStar uStar =
                                          if _hxStar : xStar ∈ D then
                          sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
                        else ⊥) ∧
                      convexBifunctionParameterDomain F = C ∧
                        {xStar | ∃ uStar,
                            genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥} = D := by
      simpa [K1, K2, F] using
        helperForCorollary33_3_3_canonicalWitnessPackage
          (C := C) (D := D) (K := K) hC_nonempty hD_nonempty hC_closed hD_closed hC_convex
          hD_convex hK_cont hK_concaveConvex
    rcases hCanonicalWitnessPackage with
      ⟨hLowerClosed, hF_rock, hF_noBot, hF_graphClosed, hF_primalPairing,
        hF_dualPairing, hF_primalFormula, hF_dualFormula, hF_dom, hF_adjDom⟩
    -- Step 3: the lower-closed part is already extracted, and the remaining `∃!` package is
    -- exactly the dedicated uniqueness helper proved just above.
    refine ⟨hLowerClosed, ?_⟩
    exact
      helperForCorollary33_3_3_existsUniqueWitness_of_fullPackage
        (C := C) (D := D) (K := K) (K1 := K1) (K2 := K2) (F := F)
        hF_rock hF_noBot hF_graphClosed hF_primalPairing hF_dualPairing hF_primalFormula
        hF_dualFormula hF_dom hF_adjDom



end Section33
end Chap07
