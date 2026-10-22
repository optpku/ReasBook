/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part17

section Chap07
section Section34

open Set

section SaddleAmbient

variable {m n : ℕ}

/-!
Helpers for Text 34.2.3: identify the two effective-domain objects attached to the canonical
Section 34 kernel `⟨F u, x^*⟩ = ⟨u, F^* x^*⟩`, and record the elementary projection argument
that converts nonempty saddle effective domain into nonempty factor domains.
-/

/-- Helper for Text 34.2.3: the first effective domain of the canonical Section 34 kernel is
exactly the ordinary effective domain `dom F` of the convex bifunction `F`. -/
lemma helperForText_34_2_3_firstKernelDomain_eq_convexBifunctionEffectiveDomain
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    effectiveDomain₁ (convexBifunctionClosedKernel F) = convexBifunctionEffectiveDomain F := by
  ext u
  constructor
  · intro hu
    have hu0 :
        u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (fun u' => -convexBifunctionPairing F u' (0 : Fin n → ℝ)) := by
      rw [effectiveDomain_eq]
      constructor
      · simp
      have hPairNeBot : convexBifunctionPairing F u (0 : Fin n → ℝ) ≠ (⊥ : EReal) := by
        simpa [convexBifunctionClosedKernel] using
          (bot_lt_iff_ne_bot.mp (hu (0 : Fin n → ℝ)))
      exact
        lt_top_iff_ne_top.2
          (show -convexBifunctionPairing F u (0 : Fin n → ℝ) ≠ (⊤ : EReal) by
            simpa using hPairNeBot)
    rw [_root_.helperForCorollary33_2_1_negConvexPairingSection_effectiveDomain_eq
      (F := F) (0 : Fin n → ℝ)] at hu0
    simpa [convexBifunctionEffectiveDomain] using hu0
  · intro hu xStar
    have hx :
        u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (fun u' => -convexBifunctionPairing F u' xStar) := by
      rw [_root_.helperForCorollary33_2_1_negConvexPairingSection_effectiveDomain_eq
        (F := F) xStar]
      simpa [convexBifunctionEffectiveDomain] using hu
    have hxlt : -convexBifunctionPairing F u xStar < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hx
    exact
      bot_lt_iff_ne_bot.mpr
        (by simpa [convexBifunctionClosedKernel] using (lt_top_iff_ne_top.mp hxlt))

/-- Helper for Text 34.2.3: the second effective domain of the canonical Section 34 kernel is
exactly the effective domain `dom F*` of the Section 34 concave adjoint bifunction. -/
lemma helperForText_34_2_3_secondKernelDomain_eq_concaveAdjointEffectiveDomain
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hQ : Section34Theorem34_2Qualification F) :
    effectiveDomain₂ (convexBifunctionClosedKernel F) =
      concaveBifunctionEffectiveDomain (section34ConcaveBifunctionAdjoint F) := by
  have hKernelEq :
      convexBifunctionClosedKernel F = section34ConcaveBifunctionAdjointPairing F :=
    hQ.adjointPairing_eq
  ext xStar
  constructor
  · intro hx
    have hx0 :
        xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x' =>
            concaveBifunctionPairing (section34ConcaveBifunctionAdjoint F) x'
              (0 : Fin m → ℝ)) := by
      rw [effectiveDomain_eq]
      constructor
      · simp
      have hPoint :
          section34ConcaveBifunctionAdjointPairing F
              (0 : Fin m → ℝ) xStar < (⊤ : EReal) := by
        rw [← hKernelEq]
        exact hx (0 : Fin m → ℝ)
      simpa [section34ConcaveBifunctionAdjointPairing, concaveBifunctionPairing] using hPoint
    rw [_root_.helperForCorollary33_2_1_concavePairingSection_effectiveDomain_eq
      (m := n) (n := m) (F := section34ConcaveBifunctionAdjoint F) (0 : Fin m → ℝ)] at hx0
    simpa [concaveBifunctionEffectiveDomain, bot_lt_iff_ne_bot] using hx0
  · intro hx uStar
    have hxu :
        xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x' =>
            concaveBifunctionPairing (section34ConcaveBifunctionAdjoint F) x' uStar) := by
      rw [_root_.helperForCorollary33_2_1_concavePairingSection_effectiveDomain_eq
        (m := n) (n := m) (F := section34ConcaveBifunctionAdjoint F) uStar]
      simpa [concaveBifunctionEffectiveDomain, bot_lt_iff_ne_bot] using hx
    have hPairFinite :
        concaveBifunctionPairing (section34ConcaveBifunctionAdjoint F) xStar uStar < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hxu
    have hPoint :
        section34ConcaveBifunctionAdjointPairing F uStar xStar < (⊤ : EReal) := by
      simpa [section34ConcaveBifunctionAdjointPairing, concaveBifunctionPairing] using hPairFinite
    rw [hKernelEq]
    exact hPoint

/-- Helper for Text 34.2.3: once the saddle effective domain of the canonical Section 34 kernel
is nonempty, both projected factor domains are nonempty as well. -/
lemma helperForText_34_2_3_projectedDomainsNonempty_of_kernelDomain
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (saddleEffectiveDomain (convexBifunctionClosedKernel F)).Nonempty →
      (convexBifunctionDomain F).Nonempty ∧
        (convexBifunctionKernelAdjointDomain F).Nonempty := by
  rintro ⟨⟨u, xStar⟩, hux⟩
  refine ⟨?_, ?_⟩
  · refine ⟨u, ?_⟩
    simpa [convexBifunctionDomain, saddleEffectiveDomain] using (Set.mem_prod.mp hux).1
  · refine ⟨xStar, ?_⟩
    simpa [convexBifunctionKernelAdjointDomain, saddleEffectiveDomain] using
      (Set.mem_prod.mp hux).2

/-- Helper for Text 34.2.3: one finite primal witness already forces the Section 34 adjoint
bifunction `F*` to avoid the value `⊤` everywhere. -/
lemma helperForText_34_2_3_adjoint_hasNoTopValues_of_proper
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hproper : IsProperConvexBifunction F) :
    HasNoTopValuesBifunction (section34ConcaveBifunctionAdjoint F) := by
  rcases hproper with ⟨_hNoBot, hDom⟩
  rcases hDom with ⟨u₀, x₀, hx₀lt⟩
  have hx₀NeTop : F u₀ x₀ ≠ (⊤ : EReal) := lt_top_iff_ne_top.mp hx₀lt
  intro xStar uStar
  have hPairNeBot :
      convexBifunctionPairing F u₀ xStar ≠ (⊥ : EReal) := by
    simpa [convexBifunctionPairing, bifunctionPairingNotation, convexConjugate] using
      helperForTheorem33_1_convexConjugate_ne_bot_of_point
        (f := F u₀) (x₀ := x₀) hx₀NeTop xStar
  have hConjNeBot :
      convexConjugate (fun u => -convexBifunctionPairing F u xStar) (-uStar) ≠ (⊥ : EReal) := by
    simpa [convexConjugate] using
      helperForTheorem33_1_convexConjugate_ne_bot_of_point
        (f := fun u => -convexBifunctionPairing F u xStar) (x₀ := u₀)
        (by simpa using hPairNeBot) (-uStar)
  rw [section34ConcaveBifunctionAdjoint]
  rw [helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted]
  simpa [convexConjugate] using hConjNeBot

/-- Helper for Text 34.2.3: a closed proper convex bifunction has a proper packed graph
function on `ℝ^(m+n)`. -/
lemma helperForText_34_2_3_graphFunction_properConvex
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hproper : IsProperConvexBifunction F) :
    ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
      (graphFunctionOfBifunction F) := by
  rcases hF with ⟨hRock, hNoBot, hClosedSections⟩
  rcases hproper with ⟨_hNoBot', hDom⟩
  have hSectionClosureExact :
      ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ, convexFunctionClosure (F u) x = F u x := by
    intro u
    intro x
    have hClosureEq : F u = functionConvexClosure (F u) := hClosedSections u
    calc
      convexFunctionClosure (F u) x = functionConvexClosure (F u) x := by
        rw [← helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
          (hNoBot := hNoBot u)]
      _ = F u x := (congrArg (fun g => g x) hClosureEq).symm
  have hGraphConvex :
      IsGraphConvexBifunction F :=
    helperForLemma33_0_14_graphConvex_of_rockafellar_with_exactSectionwiseClosure
      (F := F) hRock hSectionClosureExact hNoBot
  have hGraphConv :
      ConvexFunction (graphFunctionOfBifunction F) :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction
      (by simpa [IsGraphConvexBifunction] using hGraphConvex)
  refine ⟨?_, ?_, ?_⟩
  · simpa [ConvexFunctionOn] using hGraphConv
  · rcases hDom with ⟨u₀, x₀, hx₀⟩
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
    simpa [graphFunctionOfBifunction] using
      hNoBot (fun i : Fin m => z (Fin.castAdd n i))
        (fun j : Fin n => z (Fin.natAdd m j))

-- Proof sketch: combine the closed-convex hypothesis with the correspondence from Theorem 34.2
-- to identify the book's adjoint `F*`, then transport the one-sided finiteness convention from
-- `F` to `F*` and read off nonemptiness of the two existential effective domains.
/-- Text 34.2.3: if `F` is a closed convex bifunction and `F` is proper in the bifunction sense,
then its conjugate bifunction `F*` is proper as well. Consequently, both effective domains are
nonempty: `dom F ≠ ∅` and `dom F* ≠ ∅`. -/
theorem closed_convex_bifunction_proper_implies_adjoint_proper
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hproper : IsProperConvexBifunction F) :
    IsProperConcaveBifunction (section34ConcaveBifunctionAdjoint F) ∧
      (convexBifunctionEffectiveDomain F).Nonempty ∧
      (concaveBifunctionEffectiveDomain (section34ConcaveBifunctionAdjoint F)).Nonempty := by
  rcases hproper with ⟨hNoBot, hDom⟩
  have hAdjNoTop :
      HasNoTopValuesBifunction (section34ConcaveBifunctionAdjoint F) :=
    helperForText_34_2_3_adjoint_hasNoTopValues_of_proper (F := F) ⟨hNoBot, hDom⟩
  have hAdjDom :
      (concaveBifunctionEffectiveDomain (section34ConcaveBifunctionAdjoint F)).Nonempty := by
    have hGraphProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
          (graphFunctionOfBifunction F) :=
      helperForText_34_2_3_graphFunction_properConvex (F := F) hF ⟨hNoBot, hDom⟩
    obtain ⟨b, β, hb⟩ :=
      properConvexFunctionOn_exists_linear_lowerBound
        (n := m + n) (f := graphFunctionOfBifunction F) hGraphProper
    let uStar0 : Fin m → ℝ := fun i => b (Fin.castAdd n i)
    let xStar0 : Fin n → ℝ := fun j => b (Fin.natAdd m j)
    refine ⟨xStar0, -uStar0, ?_⟩
    rw [section34ConcaveBifunctionAdjoint]
    rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
    have hLower :
        (((-β : ℝ)) : EReal) ≤
          iInf
            (fun u : Fin m → ℝ =>
              (((dotProduct u (-uStar0) : ℝ)) : EReal) +
                -convexBifunctionPairing F u xStar0) := by
      refine le_iInf ?_
      intro u
      have hPairUpper :
          convexBifunctionPairing F u xStar0 ≤ (((β - dotProduct u uStar0 : ℝ)) : EReal) := by
        rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
        refine iSup_le ?_
        intro x
        by_cases hTop : F u x = (⊤ : EReal)
        · simp [hTop]
        · have hNoBotux : F u x ≠ (⊥ : EReal) := hNoBot u x
          have hDot :
              dotProduct (Fin.append u x) b =
                dotProduct u uStar0 + dotProduct x xStar0 := by
            simpa [uStar0, xStar0] using
              (helperForCorollary33_1_3_dotProduct_append
                (m := m) (k := n) (u := u) (v := x) (b := b))
          have hGraphLower :
              (((dotProduct u uStar0 + dotProduct x xStar0 - β : ℝ)) : EReal) ≤ F u x := by
            simpa [graphFunctionOfBifunction, hDot] using hb (Fin.append u x)
          have hFx :
              (((F u x).toReal : ℝ) : EReal) = F u x := by
            exact EReal.coe_toReal (x := F u x) hTop hNoBotux
          have hGraphLowerReal :
              dotProduct u uStar0 + dotProduct x xStar0 - β ≤ (F u x).toReal := by
            exact
              EReal.coe_le_coe_iff.mp (by simpa [hFx] using hGraphLower)
          have hTermReal :
              dotProduct x xStar0 - (F u x).toReal ≤ β - dotProduct u uStar0 := by
            linarith
          have hTermEReal :
              (((dotProduct x xStar0 - (F u x).toReal : ℝ)) : EReal) ≤
                (((β - dotProduct u uStar0 : ℝ)) : EReal) := by
            exact EReal.coe_le_coe_iff.mpr hTermReal
          simpa [hFx, sub_eq_add_neg] using hTermEReal
      have hNeg :
          -((((β - dotProduct u uStar0 : ℝ)) : EReal)) ≤
            -convexBifunctionPairing F u xStar0 := by
        exact EReal.neg_le_neg_iff.mpr hPairUpper
      have hCoeff :
          (((-β : ℝ)) : EReal) =
            (((dotProduct u (-uStar0) : ℝ)) : EReal) +
              -((((β - dotProduct u uStar0 : ℝ)) : EReal)) := by
        have hCoeffReal :
            (-β : ℝ) = dotProduct u (-uStar0) - (β - dotProduct u uStar0) := by
          rw [dotProduct_neg]
          ring
        exact_mod_cast hCoeffReal
      calc
        (((-β : ℝ)) : EReal) =
            (((dotProduct u (-uStar0) : ℝ)) : EReal) +
              -((((β - dotProduct u uStar0 : ℝ)) : EReal)) := hCoeff
        _ ≤
            (((dotProduct u (-uStar0) : ℝ)) : EReal) +
              -convexBifunctionPairing F u xStar0 := by
                simpa [add_comm] using
                  add_le_add_right hNeg ((((dotProduct u (-uStar0) : ℝ)) : EReal))
    exact
      lt_of_lt_of_le
        (by
          apply bot_lt_iff_ne_bot.mpr
          have hNeBot : -((β : ℝ) : EReal) ≠ (⊥ : EReal) := by
            simp [EReal.neg_eq_bot_iff]
          exact hNeBot)
        (by simpa using hLower)
  exact ⟨⟨hAdjNoTop, hAdjDom⟩, hDom, hAdjDom⟩

-- Proof sketch: use Theorem 34.2 to identify the generated class `Ω(F)` with the
-- `saddleEquivalent`-class of the canonical kernel and to read off the common saddle effective
-- domain of any member `K`; then apply Text 34.2.3 to the proper closed convex bifunction `F`
-- to obtain nonemptiness of the two factor domains, which makes the common saddle effective
-- domain nonempty.
/-- Text 34.2.4: if a closed convex bifunction `F` is proper, then every saddle-function `K` in
the generated equivalence class `Ω(F)` is proper. -/
theorem proper_convex_bifunction_has_proper_generated_saddle_functions
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsImageClosedConvexBifunction F)
    (hproper : IsProperConvexBifunction F)
    (K : SaddleFunction m n)
    (hK : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩)
    (hQ : Section34Theorem34_2Qualification F) :
    IsProperSaddleFunction K := by
  rcases section34_theorem34_2_qualified F hF hQ with
    ⟨_hKernelEq, _hOmegaEq, _hKernelMem, _hClosedMembers, hOmegaData⟩
  have hKomega : K ∈ omegaClassOfConvexBifunction F := by
    exact mem_omegaClassOfConvexBifunction_of_mem_generatedClass (F := F) hF hK
  rcases hOmegaData K hKomega with
    ⟨_hPc1, _hPc2, hKdom, _hConvSlices, _hConcSlices, _hAgree⟩
  rcases closed_convex_bifunction_proper_implies_adjoint_proper F hF hproper with
    ⟨_hAdjProper, hDomF, hDomFstar⟩
  have hFirstKernel :
      (convexBifunctionDomain F).Nonempty := by
    simpa [convexBifunctionDomain] using
      (helperForText_34_2_3_firstKernelDomain_eq_convexBifunctionEffectiveDomain
        (F := F)).symm ▸ hDomF
  have hSecondKernel :
      (convexBifunctionKernelAdjointDomain F).Nonempty := by
    simpa [convexBifunctionKernelAdjointDomain] using
      (helperForText_34_2_3_secondKernelDomain_eq_concaveAdjointEffectiveDomain
        (F := F) hF hQ).symm ▸ hDomFstar
  rw [IsProperSaddleFunction, hKdom]
  apply Set.nonempty_iff_ne_empty.mp
  rcases hFirstKernel with ⟨u, hu⟩
  rcases hSecondKernel with ⟨xStar, hxStar⟩
  exact ⟨(u, xStar), Set.mem_prod.mpr ⟨hu, hxStar⟩⟩

end SaddleAmbient

end Section34
end Chap07
