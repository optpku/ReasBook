/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part13

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- Helper for Lemma33.0.22: second-variable convex-closedness of the sign-swapped adjoint
kernel is exactly the family of one-variable convex-closedness statements for the tilted
projection sections. -/
lemma helperForLemma33_0_22_swappedNegatedAdjointKernel_isConvexClosedInSecond_iff_tiltedProjectionSectionsClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    IsConvexClosedInSecond (fun xStar u => -convexBifunctionAdjoint F xStar u) ↔
      ∀ xStar : Fin n → ℝ,
        IsFunctionConvexClosed
          (fun u : Fin m → ℝ =>
            imageUnderLinearMap
              (projectionLinearMap (Nat.le_add_right m n))
              (fun z : Fin (m + n) → ℝ =>
                graphFunctionOfBifunction F z -
                  ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
              u) := by
  constructor
  · intro hClosed xStar
    -- Step 1: rewrite the tilted projection section as the sign-swapped adjoint section.
    have hSectionEq :
        (fun u : Fin m → ℝ =>
          imageUnderLinearMap
            (projectionLinearMap (Nat.le_add_right m n))
            (fun z : Fin (m + n) → ℝ =>
              graphFunctionOfBifunction F z -
                ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
            u) =
          fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u :=
      helperForLemma33_0_22_swappedNegatedAdjointSection_eq_projectionImage_tiltedGraph
        (F := F) xStar
    -- Step 2: specialize the kernel-level closedness identity to the chosen `xStar`.
    have hClosedSection :
        (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) =
          functionConvexClosure (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) := by
      funext u
      have hPoint :
          (fun xStar u => -convexBifunctionAdjoint F xStar u) xStar u =
            convexClosureInSecond (fun xStar u => -convexBifunctionAdjoint F xStar u) xStar u :=
        congrArg (fun G => G xStar u) hClosed
      simpa [convexClosureInSecond, functionConvexClosure] using hPoint
    -- Step 3: transport the one-variable fixed-point identity across the projection formula.
    calc
      (fun u : Fin m → ℝ =>
        imageUnderLinearMap
          (projectionLinearMap (Nat.le_add_right m n))
          (fun z : Fin (m + n) → ℝ =>
            graphFunctionOfBifunction F z -
              ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
          u)
          =
        (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) := hSectionEq
      _ = functionConvexClosure (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) :=
        hClosedSection
      _ = functionConvexClosure
            (fun u : Fin m → ℝ =>
              imageUnderLinearMap
                (projectionLinearMap (Nat.le_add_right m n))
                (fun z : Fin (m + n) → ℝ =>
                  graphFunctionOfBifunction F z -
                    ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
                u) := by
          rw [← hSectionEq]
  · intro hClosedSections
    -- Step 1: unfold kernel-level second-variable closedness and freeze `xStar`.
    unfold IsConvexClosedInSecond
    funext xStar
    funext u
    change
      (fun u' : Fin m → ℝ => -convexBifunctionAdjoint F xStar u') u =
        functionConvexClosure (fun u' : Fin m → ℝ => -convexBifunctionAdjoint F xStar u') u
    have hSectionEq :
        (fun u' : Fin m → ℝ =>
          imageUnderLinearMap
            (projectionLinearMap (Nat.le_add_right m n))
            (fun z : Fin (m + n) → ℝ =>
              graphFunctionOfBifunction F z -
                ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
            u') =
          fun u' : Fin m → ℝ => -convexBifunctionAdjoint F xStar u' :=
      helperForLemma33_0_22_swappedNegatedAdjointSection_eq_projectionImage_tiltedGraph
        (F := F) xStar
    have hClosedSection :
        (fun u' : Fin m → ℝ =>
          imageUnderLinearMap
            (projectionLinearMap (Nat.le_add_right m n))
            (fun z : Fin (m + n) → ℝ =>
              graphFunctionOfBifunction F z -
                ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
            u') =
          functionConvexClosure
            (fun u' : Fin m → ℝ =>
              imageUnderLinearMap
                (projectionLinearMap (Nat.le_add_right m n))
                (fun z : Fin (m + n) → ℝ =>
                  graphFunctionOfBifunction F z -
                    ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
                u') :=
      hClosedSections xStar
    -- Step 2: rewrite both sides using the projection formula and the assumed sectionwise
    -- convex-closedness.
    calc
      (fun u' : Fin m → ℝ => -convexBifunctionAdjoint F xStar u') u =
        (fun u' : Fin m → ℝ =>
          imageUnderLinearMap
            (projectionLinearMap (Nat.le_add_right m n))
            (fun z : Fin (m + n) → ℝ =>
              graphFunctionOfBifunction F z -
                ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
            u') u := by
              simpa using congrArg (fun G => G u) hSectionEq.symm
      _ =
        functionConvexClosure
          (fun u' : Fin m → ℝ =>
            imageUnderLinearMap
              (projectionLinearMap (Nat.le_add_right m n))
              (fun z : Fin (m + n) → ℝ =>
                graphFunctionOfBifunction F z -
                  ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
              u') u := by
                exact congrArg (fun G => G u) hClosedSection
      _ = functionConvexClosure (fun u' : Fin m → ℝ => -convexBifunctionAdjoint F xStar u') u := by
            rw [hSectionEq]

/-- Helper for Lemma33.0.22: the unresolved textbook closedness clause is exactly first-variable
concave-closedness of the adjoint kernel. -/
lemma helperForLemma33_0_22_adjointKernel_isConcaveClosedInFirst_of_tiltedProjectionSectionsClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosedSections :
      ∀ xStar : Fin n → ℝ,
        IsFunctionConvexClosed
          (fun u : Fin m → ℝ =>
            imageUnderLinearMap
              (projectionLinearMap (Nat.le_add_right m n))
              (fun z : Fin (m + n) → ℝ =>
                graphFunctionOfBifunction F z -
                  ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
              u)) :
    IsConcaveClosedInFirst (fun u xStar => convexBifunctionAdjoint F xStar u) := by
  -- Step 1: reduce first-variable concave closedness to second-variable convex closedness of
  -- the sign-swapped kernel.
  rw [helperForLemma33_0_22_adjointKernel_isConcaveClosedInFirst_iff_swappedNegated_isConvexClosedInSecond]
  -- Step 2: identify that transformed kernel statement with the family of tilted projection
  -- section identities.
  exact
    (helperForLemma33_0_22_swappedNegatedAdjointKernel_isConvexClosedInSecond_iff_tiltedProjectionSectionsClosed
      (F := F)).2 hClosedSections

/-- Helper for Lemma33.0.22: the primal value of the tilted bifunction is exactly the
negative of the fixed-dual pairing section.

This is the textbook identity
`inf_x (F u x - ⟪x, x^*⟫) = -⟪F u, x^*⟫`, written using the Chapter 6 primal-value notation
for the tilted bifunction. -/
lemma helperForLemma33_0_22_tiltedPrimalValue_eq_negPairingSection
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ) :
    convexProgramAssociatedWith
      (fun u : Fin m → ℝ => fun x : Fin n → ℝ =>
        F u x - ((dotProduct x xStar : ℝ) : EReal)) =
      fun u : Fin m → ℝ => -convexBifunctionPairing F u xStar := by
  funext u
  -- Step 1: unfold the primal value at the frozen parameter `u`.
  unfold convexProgramAssociatedWith
  -- Step 2: reuse the earlier tilted-fiber computation of Corollary 33.1.3.
  simpa [graphFunctionOfBifunction] using
    helperForCorollary33_1_3_sInf_tiltedFiber_eq_negSup_pairing (F := F) u xStar

/-- Helper for Lemma33.0.22: translating the parameter variable commutes with the tilted
primal-value formula.

For the translated tilted bifunction `v ↦ F (u + v) - ⟪·, x^*⟫`, the associated primal
value function is the shifted negative pairing section
`v ↦ -⟪F (u + v), x^*⟫`. -/
lemma helperForLemma33_0_22_translatedTiltedPrimalValue_eq_shiftedNegPairingSection
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    convexProgramAssociatedWith
      (fun v : Fin m → ℝ => fun x : Fin n → ℝ =>
        F (u + v) x - ((dotProduct x xStar : ℝ) : EReal)) =
      fun v : Fin m → ℝ => -convexBifunctionPairing F (u + v) xStar := by
  funext v
  -- Step 1: unfold the translated primal value at the frozen translation parameter `u`.
  unfold convexProgramAssociatedWith
  -- Step 2: apply the same tilted-fiber identity to the translated bifunction.
  simpa [graphFunctionOfBifunction, convexBifunctionPairing] using
    helperForCorollary33_1_3_sInf_tiltedFiber_eq_negSup_pairing
      (F := fun v : Fin m → ℝ => fun x : Fin n → ℝ => F (u + v) x) v xStar

/-- Helper for Lemma33.0.22: every translated tilted primal program is already consistent at
the origin.

The only consistency input needed later is that the origin slice of the translated tilted
program avoids `⊤`; this follows because the origin value is the negative of a pairing
section that already avoids `⊥`. -/
lemma helperForLemma33_0_22_translatedTiltedPrimalValue_atOrigin_ne_top
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    convexProgramAssociatedWith
      (fun v : Fin m → ℝ => fun x : Fin n → ℝ =>
        F (u + v) x - ((dotProduct x xStar : ℝ) : EReal)) 0 ≠ (⊤ : EReal) := by
  -- Step 1: rewrite the translated origin value as the negative pairing at `(u, xStar)`.
  have hValueAtZero :
      convexProgramAssociatedWith
          (fun v : Fin m → ℝ => fun x : Fin n → ℝ =>
            F (u + v) x - ((dotProduct x xStar : ℝ) : EReal)) 0 =
        -convexBifunctionPairing F u xStar := by
    simpa using
      congrFun
        (helperForLemma33_0_22_translatedTiltedPrimalValue_eq_shiftedNegPairingSection
          (F := F) u xStar)
        (0 : Fin m → ℝ)
  rw [hValueAtZero]
  -- Step 2: the corresponding pairing section already avoids `⊥`, so its negation avoids `⊤`.
  have hPairNoBot : convexBifunctionPairing F u xStar ≠ (⊥ : EReal) :=
    helperForLemma33_0_22_pairingSection_hasNoBot
      (F := F) hF_notTop xStar u
  simpa using hPairNoBot

/-- Helper for Lemma33.0.22: translating the tilted graph in the parameter variable produces a
closed convex bifunction for the shifted primal-value program.

This is the Chapter 6 packaging needed for the local normality argument: after freezing `u` and
`xStar`, the translated objective `(v, x) ↦ F (u + v) x - ⟪x, xStar⟫` still has a closed convex
graph because the original tilted graph is closed convex and translation preserves both
convexity and lower semicontinuity. -/
lemma helperForLemma33_0_22_translatedTiltedBifunction_isClosedConvex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    ClosedConvexBifunction
      (fun v : Fin m → ℝ => fun x : Fin n → ℝ =>
        F (u + v) x - ((dotProduct x xStar : ℝ) : EReal)) := by
  let G : (Fin (m + n) → ℝ) → EReal :=
    fun z : Fin (m + n) → ℝ =>
      graphFunctionOfBifunction F z -
        ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal)
  let a : Fin (m + n) → ℝ := Fin.append u 0
  let Gtranslate : (Fin (m + n) → ℝ) → EReal := fun z => G (z + a)
  let H : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
    fun v : Fin m → ℝ => fun x : Fin n → ℝ =>
      F (u + v) x - ((dotProduct x xStar : ℝ) : EReal)
  -- Step 1: start from the closed proper convex package for the unshifted tilted graph.
  have hTiltedClosedProper :
      ClosedConvexFunction G ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) G := by
    simpa [G] using
      helperForLemma33_0_22_tiltedGraph_isClosedProperConvex
        (F := F) (hF_convex := hF_convex) (hF_closed := hF_closed)
        (hF_noBot := hF_noBot) (hF_notTop := hF_notTop) xStar
  -- Step 2: translate the tilted graph by `Fin.append u 0`.
  have hTranslateProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) Gtranslate :=
    helperForTheorem_6_29_4_translate_properConvexFunctionOn
      (hgproper := hTiltedClosedProper.2) a
  have hTranslateConv : ConvexFunction Gtranslate := by
    simpa [ConvexFunction, Gtranslate] using hTranslateProper.1
  have hTranslateLsc : LowerSemicontinuous Gtranslate := by
    have hContTranslate : Continuous (fun z : Fin (m + n) → ℝ => z + a) :=
      continuous_id.add continuous_const
    exact hTiltedClosedProper.1.2.comp_continuous hContTranslate
  have hTranslateClosed : ClosedConvexFunction Gtranslate :=
    (properConvexFunction_closed_iff_lowerSemicontinuous
      (f := Gtranslate) hTranslateProper).2 hTranslateLsc
  have hGraphEq : bifunctionGraphFunction H = Gtranslate := by
    funext z
    have hFront :
        u + (fun i : Fin m => z (Fin.castAdd n i)) =
          fun i : Fin m => u i + z (Fin.castAdd n i) := by
      funext i
      simp [Pi.add_apply]
    have hFrontComm :
        (fun i : Fin m => u i + z (Fin.castAdd n i)) =
          fun i : Fin m => z (Fin.castAdd n i) + u i := by
      funext i
      simp [add_comm]
    simp [H, Gtranslate, G, a, bifunctionGraphFunction, graphFunctionOfBifunction,
      Pi.add_apply, Fin.append, hFront, hFrontComm]
  -- Step 3: rewrite the translated graph back into bifunction language.
  have hConvGraph : ConvexFunction (bifunctionGraphFunction H) := by
    simpa [hGraphEq] using hTranslateConv
  have hClosedGraph : ClosedConvexFunction (bifunctionGraphFunction H) := by
    simpa [hGraphEq] using hTranslateClosed
  exact ⟨hConvGraph, hClosedGraph⟩

/-- Helper for Lemma33.0.22: each fixed-dual negative pairing section is lower semicontinuous.

The proof follows the translated primal-value route from Chapter 6. Around any base point `u`,
the shifted section `v ↦ -⟪F (u + v), xStar⟫` is the primal-value function of a translated closed
convex bifunction. Because that translated program is strictly consistent on all of `ℝ^m`, its
value at the origin agrees with its convex closure there, and this pointwise closure equality
upgrades to lower semicontinuity at the original base point `u`. -/
lemma helperForLemma33_0_22_negPairingSection_isLowerSemicontinuous
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    ∀ xStar : Fin n → ℝ,
      LowerSemicontinuous (fun u : Fin m → ℝ => -convexBifunctionPairing F u xStar) := by
  intro xStar u y hy
  let p : (Fin m → ℝ) → EReal := fun v : Fin m → ℝ =>
    -convexBifunctionPairing F (u + v) xStar
  let G : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
    fun v : Fin m → ℝ => fun x : Fin n → ℝ =>
      F (u + v) x - ((dotProduct x xStar : ℝ) : EReal)
  -- Step 1: package the translated tilted objective as a closed convex bifunction.
  have hGClosed :
      ClosedConvexBifunction G :=
    helperForLemma33_0_22_translatedTiltedBifunction_isClosedConvex
      (F := F) (hF_convex := hF_convex) (hF_closed := hF_closed)
      (hF_noBot := hF_noBot) (hF_notTop := hF_notTop) u xStar
  have hPrimalEq :
      convexProgramAssociatedWith G = p :=
    helperForLemma33_0_22_translatedTiltedPrimalValue_eq_shiftedNegPairingSection
      (F := F) u xStar
  have hAllNeTop :
      ∀ v : Fin m → ℝ, convexProgramAssociatedWith G v ≠ (⊤ : EReal) := by
    intro v
    rw [hPrimalEq]
    have hPairNoBot :
        convexBifunctionPairing F (u + v) xStar ≠ (⊥ : EReal) :=
      helperForLemma33_0_22_pairingSection_hasNoBot
        (F := F) hF_notTop xStar (u + v)
    simpa [p] using hPairNoBot
  have hEffectiveDomainUniv :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) (convexProgramAssociatedWith G) =
        Set.univ := by
    ext v
    rw [effectiveDomain_eq]
    constructor
    · intro _hv
      simp
    · intro _hv
      exact ⟨by simp, lt_top_iff_ne_top.2 (hAllNeTop v)⟩
  -- Step 2: the translated program is strictly consistent because its perturbation-value
  -- function is everywhere different from `⊤`.
  have hStrictCons :
      IsStrictlyConsistentConvexProgram ⟨G, hGClosed.1⟩ := by
    refine ⟨hAllNeTop 0, ?_⟩
    simp [hEffectiveDomainUniv]
  -- Step 3: Chapter 6 then identifies the origin value with the convex closure at the origin.
  have hValueEq :
      convexProgramAssociatedWith G 0 = dualProgramOfConvexProgram ⟨G, hGClosed.1⟩ :=
    helperForTheorem_6_30_17_valueEquality_of_primalStrongOrStrictConsistency
      (F := ⟨G, hGClosed⟩) (Or.inr hStrictCons)
  have hClosureEq :
      convexClosure p 0 = p 0 := by
    calc
      convexClosure p 0 = convexClosure (convexProgramAssociatedWith G) 0 := by
        rw [hPrimalEq]
      _ = dualProgramOfConvexProgram ⟨G, hGClosed.1⟩ := by
        simpa [dualProgramOfConvexProgram] using
          (corollary_6_30_2_2 (F := ⟨G, hGClosed⟩)).1
      _ = convexProgramAssociatedWith G 0 := hValueEq.symm
      _ = p 0 := by
        rw [← hPrimalEq]
  -- Step 4: closure equality at the translated origin upgrades the shifted section to be
  -- lower semicontinuous at `0`.
  have hClosureAtZero :
      LowerSemicontinuousAt (convexClosure p) 0 :=
    (helperForCorollary_6_30_3_convexClosure_lowerSemicontinuous (p := p)) 0
  have hShiftedAtZero : LowerSemicontinuousAt p 0 := by
    apply lowerSemicontinuousAt_of_le_of_eq hClosureAtZero
    · intro v
      simpa [convexClosure] using convexFunctionClosure_le_self (f := p) v
    · exact hClosureEq
  -- Step 5: translate the origin statement back to lower semicontinuity at the original base
  -- point `u`.
  have hSubTendsto :
      Filter.Tendsto (fun u' : Fin m → ℝ => u' - u) (nhds u) (nhds (0 : Fin m → ℝ)) := by
    have hContSub : Continuous (fun u' : Fin m → ℝ => u' - u) :=
      continuous_id.sub continuous_const
    simpa using (hContSub.continuousAt : ContinuousAt (fun u' : Fin m → ℝ => u' - u) u).tendsto
  have hShiftedEventually :
      ∀ᶠ u' in nhds u, y < p (u' - u) :=
    hSubTendsto.eventually (hShiftedAtZero y (by simpa [p] using hy))
  refine hShiftedEventually.mono ?_
  intro u' hu'
  simpa [p, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu'

/-- Helper for Lemma33.0.22: each fixed-dual pairing section is already concave-closed.

After proving lower semicontinuity of the negated section, the Section 33 sign-flip lemma turns
that convex-closed statement into the desired concave-closed one for
`u ↦ convexBifunctionPairing F u xStar`. -/
lemma helperForLemma33_0_22_pairingSection_isFunctionConcaveClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    ∀ xStar : Fin n → ℝ,
      IsFunctionConcaveClosed (fun u : Fin m → ℝ => convexBifunctionPairing F u xStar) := by
  intro xStar
  have hNegLsc :
      LowerSemicontinuous (fun u : Fin m → ℝ => -convexBifunctionPairing F u xStar) :=
    helperForLemma33_0_22_negPairingSection_isLowerSemicontinuous
      (F := F) (hF_convex := hF_convex) (hF_closed := hF_closed)
      (hF_noBot := hF_noBot) (hF_notTop := hF_notTop) xStar
  have hNegClosed :
      IsFunctionConvexClosed (fun u : Fin m → ℝ => -convexBifunctionPairing F u xStar) := by
    -- Step 1: lower semicontinuity fixes the negated section under the Section 33 convex closure.
    unfold IsFunctionConvexClosed
    simpa using
      helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hNegLsc
  -- Step 2: flip signs back to obtain concave-closedness of the original section.
  exact
    (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed
      (g := fun u : Fin m → ℝ => convexBifunctionPairing F u xStar)).2 hNegClosed

/-- Helper for Lemma33.0.22: the unresolved textbook closedness clause is exactly first-variable
concave-closedness of the adjoint kernel. -/
lemma helperForLemma33_0_22_adjointKernel_isConcaveClosedInFirst
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    IsConcaveClosedInFirst (fun u xStar => convexBifunctionAdjoint F xStar u) := by
  -- Route correction: the valid dependency-closed route is the translated primal-value
  -- argument from Chapter 6. For each fixed `xStar`, we first prove that the pairing section
  -- `u ↦ ⟪F u, xStar⟫` is concave-closed, then evaluate that sectionwise fixed-point identity.
  have hPairingClosed :
      ∀ xStar : Fin n → ℝ,
        IsFunctionConcaveClosed (fun u : Fin m → ℝ => convexBifunctionPairing F u xStar) :=
    helperForLemma33_0_22_pairingSection_isFunctionConcaveClosed
      (F := F) (hF_convex := hF_convex) (hF_closed := hF_closed)
      (hF_noBot := hF_noBot) (hF_notTop := hF_notTop)
  -- Step 1: unfold the kernel-level first-variable closure predicate.
  unfold IsConcaveClosedInFirst
  funext u xStar
  -- Step 2: specialize the sectionwise concave-closure fixed-point identity at the chosen
  -- dual parameter `xStar` and base point `u`.
  have hPoint :
      (fun u' : Fin m → ℝ => convexBifunctionPairing F u' xStar) u =
        functionConcaveClosure
          (fun u' : Fin m → ℝ => convexBifunctionPairing F u' xStar) u := by
    have hClosedSection := hPairingClosed xStar
    exact congrArg (fun g => g u) hClosedSection
  -- Step 3: rewrite the pairing notation back into the adjoint notation used in the theorem.
  simpa [convexBifunctionAdjoint, concaveClosureInFirst, functionConcaveClosure] using hPoint

-- Proof sketch: identify the adjoint with the partial convex conjugate of the proper closed
-- convex graph function `f (u, x) = (F u) x` in the `x`-variable, where properness on the
-- convex side is modeled by the no-`⊥` hypothesis together with the requirement that each
-- section `F u` is not identically `⊤`. Fenchel conjugacy in that variable gives convexity
-- in `x^*`, while the convex-bifunction hypothesis gives concavity in `u`; closedness of the
-- resulting `u`-sections follows from the closedness of the graph function.
/-- Lemma33.0.22 (Adjoint of a convex bifunction): if `F` has a proper closed convex graph
function, with properness on the convex side modeled by the conditions that `F` takes no
value `⊥` and that each section `F u` is nontrivial in the sense that it is not identically
`⊤`, then its adjoint `x^* ↦ (u ↦ sup_x (⟪x, x^*⟫ - (F u) x))` is a closed concave
bifunction. That is, for each `x^*`, the section `u ↦ (F^* x^*)(u)` is concave and
concave-closed, and the graph function `(u, x^*) ↦ (F^* x^*)(u)` is concave in `u` and
convex in `x^*`. -/
theorem convexBifunctionAdjoint_isClosedConcave
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    (∀ xStar : Fin n → ℝ,
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (convexBifunctionAdjoint F xStar) ∧
        IsFunctionConcaveClosed (convexBifunctionAdjoint F xStar)) ∧
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (fun u xStar => convexBifunctionAdjoint F xStar u) := by
  classical
  -- Step 1: package every adjoint-kernel property already derivable in the current
  -- dependency closure. This isolates the remaining work to first-variable closedness.
  have hKernelPackage :
      IsConvexClosedConcaveConvexKernel
        (fun u xStar => convexBifunctionAdjoint F xStar u) :=
    helperForLemma33_0_22_adjointKernel_isConvexClosedConcaveConvexKernel
      (F := F) (hF_convex := hF_convex) (hF_noBot := hF_noBot) (hF_notTop := hF_notTop)
  -- Step 2: extract the joint concave-convex statement needed in the theorem conclusion.
  have hKernelConcConv :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (fun u xStar => convexBifunctionAdjoint F xStar u) := hKernelPackage.1
  -- Step 3: isolate the remaining closedness bridge as the kernel-level first-variable
  -- fixed-point identity.
  have hKernelClosed :
      IsConcaveClosedInFirst (fun u xStar => convexBifunctionAdjoint F xStar u) :=
    helperForLemma33_0_22_adjointKernel_isConcaveClosedInFirst
      (F := F) (hF_convex := hF_convex) (hF_closed := hF_closed)
      (hF_noBot := hF_noBot) (hF_notTop := hF_notTop)
  refine ⟨?_, hKernelConcConv⟩
  intro xStar
  -- Step 4: freeze the dual variable in the kernel package to obtain the textbook sectionwise
  -- conclusion.
  have hSection :
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (convexBifunctionAdjoint F xStar) ∧
        IsFunctionConcaveClosed (convexBifunctionAdjoint F xStar) := by
    simpa [convexBifunctionAdjoint] using
      helperForLemma33_0_22_frozenSecondVariable_isConcaveAndFunctionConcaveClosed
        (K := fun u xStar => convexBifunctionAdjoint F xStar u)
        (hKernelConcConv := hKernelConcConv) (hKernelClosed := hKernelClosed) xStar
  simpa [convexBifunctionAdjoint] using hSection

-- Proof sketch: apply Lemma33.0.22 to the adjoint `F*`. Its second conclusion gives the
-- concave-convex property of `(u, x^*) ↦ (F^* x^*)(u)`, while the first conclusion gives for
-- each fixed `x^*` that `u ↦ (F^* x^*)(u)` is concave and agrees with its concave closure.
/-- Helper for Corollary33.0.23: Lemma33.0.22 already contains the global concave-convex
statement for the adjoint pairing kernel. -/
lemma helperForCorollary33_0_23_jointConcaveConvex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
      (fun u xStar => convexBifunctionAdjoint F xStar u) := by
  -- Step 1: apply the adjoint closed-concavity theorem and keep only its global kernel field.
  exact
    (convexBifunctionAdjoint_isClosedConcave
      (F := F) (hF_convex := hF_convex) (hF_closed := hF_closed)
      (hF_noBot := hF_noBot) (hF_notTop := hF_notTop)).2

/-- Helper for Corollary33.0.23: Lemma33.0.22 already yields concave-closedness of each
fixed-dual adjoint section. -/
lemma helperForCorollary33_0_23_sectionConcaveClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    ∀ xStar : Fin n → ℝ,
      IsFunctionConcaveClosed (convexBifunctionAdjoint F xStar) := by
  -- Step 1: unpack the sectionwise output of the adjoint closed-concavity theorem.
  intro xStar
  have hSections :=
    (convexBifunctionAdjoint_isClosedConcave
      (F := F) (hF_convex := hF_convex) (hF_closed := hF_closed)
      (hF_noBot := hF_noBot) (hF_notTop := hF_notTop)).1
  -- Step 2: freeze the dual parameter and project the concave-closed half of the section data.
  exact (hSections xStar).2

/-- Corollary33.0.23 (Concavity/closedness of `⟨u, F^* x^*⟩`): under the same hypotheses as
Lemma33.0.22, the function `(u, x^*) ↦ (F^* x^*)(u)`, represented here by
`(u, x^*) ↦ convexBifunctionAdjoint F x^* u`, is concave-convex, and for each fixed `x^*`
the section `u ↦ (F^* x^*)(u)` is concave-closed. -/
theorem convexBifunctionAdjoint_pairing_isConcaveConvex_concaveClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
      (fun u xStar => convexBifunctionAdjoint F xStar u) ∧
      ∀ xStar : Fin n → ℝ,
        IsFunctionConcaveClosed (convexBifunctionAdjoint F xStar) := by
  -- Step 1: use the dedicated extraction lemma for the global concave-convex statement.
  refine ⟨?_, ?_⟩
  exact
    helperForCorollary33_0_23_jointConcaveConvex
      (F := F) (hF_convex := hF_convex) (hF_closed := hF_closed)
      (hF_noBot := hF_noBot) (hF_notTop := hF_notTop)
  -- Step 2: use the dedicated extraction lemma for the fixed-section concave-closedness.
  exact
    helperForCorollary33_0_23_sectionConcaveClosed
      (F := F) (hF_convex := hF_convex) (hF_closed := hF_closed)
      (hF_noBot := hF_noBot) (hF_notTop := hF_notTop)

/-- The pairing attached to the adjoint of a convex bifunction, i.e. the textbook quantity
`⟨u, F^* x^*⟩ = (F^* x^*)(u)`. -/
noncomputable abbrev convexBifunctionAdjointPairing {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) (u : Fin m → ℝ) : EReal :=
  concaveConjugate (convexBifunctionAdjoint F xStar) u

/-- The pairing attached to the adjoint of a concave bifunction, i.e. the textbook quantity
`⟨u, F^* x^*⟩ = (F^* x^*)(u)`. -/
noncomputable abbrev concaveBifunctionAdjointPairing {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) (u : Fin m → ℝ) : EReal :=
  convexConjugate (concaveBifunctionAdjoint F xStar) u

/-- The sectionwise convex regularization of a bifunction, obtained by closing each image
function `F u` in the second variable. This is recorded separately from the book's global
closure notation `(cl F)`. -/
noncomputable def sectionwiseConvexClosureBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => functionConvexClosure (F u) x

/-- The sectionwise concave regularization of a bifunction, obtained by closing each image
function `F u` in the second variable with the concave closure operator. This is recorded
separately from the book's global closure notation `(cl F)`. -/
noncomputable def sectionwiseConcaveClosureBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => functionConcaveClosure (F u) x

end Section33
end Chap07
