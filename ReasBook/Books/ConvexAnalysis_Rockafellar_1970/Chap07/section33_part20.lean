/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part19

section Chap07
section Section33

attribute [local instance] Classical.propDecidable

/-- Helper for Corollary33.3.3: any two bifunctions satisfying the displayed primal
formula of the corollary must coincide. -/
lemma helperForCorollary33_3_3_unique_of_primalFormula
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {F G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF :
      ∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
        F u x =
          if u ∈ C then
            sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
          else ⊤)
    (hG :
      ∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
        G u x =
          if u ∈ C then
            sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
          else ⊤) :
    F = G := by
  -- Step 1: the two displayed formulas are literally the same pointwise expression, so
  -- extensionality reduces uniqueness to transitivity of equality.
  funext u x
  exact (hF u x).trans (hG u x).symm

/-- Helper for Corollary33.3.3: the displayed primal formula already shows that the
parameter domain cannot contain points outside `C`. -/
lemma helperForCorollary33_3_3_parameterDomain_subset_of_primalFormula
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF :
      ∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
        F u x =
          if u ∈ C then
            sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
          else ⊤) :
    convexBifunctionParameterDomain F ⊆ C := by
  intro u huDom
  -- Step 1: a point outside `C` forces every value of the section `F u` to be `⊤`, so
  -- such a point cannot belong to the parameter domain.
  by_contra huNot
  rcases huDom with ⟨x, hx⟩
  have hValue : F u x = ⊤ := by
    simpa [huNot] using hF u x
  exact hx hValue

/-- Helper for Corollary33.3.3: the displayed dual formula already shows that the genuine
adjoint domain cannot contain points outside `D`. -/
lemma helperForCorollary33_3_3_genuineAdjointDomain_subset_of_dualFormula
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF :
      ∀ (xStar : Fin n → ℝ) (uStar : Fin m → ℝ),
        genuineConvexBifunctionAdjoint F xStar uStar =
          if xStar ∈ D then
            sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
          else ⊥) :
    {xStar | ∃ uStar, genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥} ⊆ D := by
  intro xStar hxDom
  -- Step 1: a point outside `D` makes the whole genuine adjoint section identically `⊥`,
  -- so it cannot belong to the adjoint domain.
  by_contra hxNot
  rcases hxDom with ⟨uStar, huStar⟩
  have hValue : genuineConvexBifunctionAdjoint F xStar uStar = ⊥ := by
    simpa [hxNot] using hF xStar uStar
  exact huStar hValue

/-- Helper for Corollary33.3.3: the canonical witness already satisfies the easy inclusion
`dom F ⊆ C` coming from its explicit primal formula. -/
lemma helperForCorollary33_3_3_canonicalWitness_parameterDomain_subset
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ} :
    convexBifunctionParameterDomain (helperForCorollary33_3_3_canonicalWitness C D K) ⊆ C := by
  -- Step 1: instantiate the general domain-subset lemma with the canonical witness formula.
  exact
    helperForCorollary33_3_3_parameterDomain_subset_of_primalFormula
      (C := C) (D := D) (K := K)
      (F := helperForCorollary33_3_3_canonicalWitness C D K)
      (fun u x => helperForCorollary33_3_3_canonicalWitness_primalFormula
        (C := C) (D := D) (K := K) u x)

/-- Helper for Corollary33.3.3: once the represented primal kernel has exactly `C` as its
non-`⊥` slice, the primal pairing formula upgrades the easy inclusion `dom F ⊆ C` to the
exact identity `dom F = C`. -/
lemma helperForCorollary33_3_3_parameterDomain_eq_of_primalPairing_and_nonbotSlice
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {K1 : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSliceDomain : {u : Fin m → ℝ | ∃ xStar : Fin n → ℝ, K1 u xStar ≠ ⊥} = C)
    (hParameterDomainSubset : convexBifunctionParameterDomain F ⊆ C)
    (hPrimalPairing :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        K1 u xStar = convexBifunctionPairing F u xStar) :
    convexBifunctionParameterDomain F = C := by
  apply Set.Subset.antisymm
  · exact hParameterDomainSubset
  · intro u hu
    -- Step 1: use the exact non-`⊥` slice description of `K1` to choose a dual witness at
    -- which the primal kernel does not collapse to `⊥`.
    have huSlice : u ∈ {u : Fin m → ℝ | ∃ xStar : Fin n → ℝ, K1 u xStar ≠ ⊥} := by
      simpa [hSliceDomain] using hu
    rcases huSlice with ⟨xStar, hxStar⟩
    -- Step 2: if `u` lay outside `dom F`, the standard off-domain pairing collapse would
    -- force the same `K1` value to be `⊥`, contradicting the chosen slice witness.
    by_contra huOut
    have hPairBot :
        convexBifunctionPairing F u xStar = ⊥ :=
      helperForCorollary33_2_2_convex_pairing_eq_bot_of_off_parameterDomain
        (G := F) huOut xStar
    have hK1Bot : K1 u xStar = ⊥ := by
      rw [hPrimalPairing u xStar, hPairBot]
    exact hxStar hK1Bot

/-- Helper for Corollary33.3.3: outside the primal constraint set `C`, the canonical witness
already has the correct collapsed primal pairing, namely the everywhere-`⊥` lower simple
extension section. -/
lemma helperForCorollary33_3_3_canonicalWitness_primalPairing_eq_lowerSimpleExtension_off_domain
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {u : Fin m → ℝ}
    (hu : u ∉ C) :
    ∀ xStar : Fin n → ℝ,
      convexBifunctionPairing (helperForCorollary33_3_3_canonicalWitness C D K) u xStar =
        lowerSimpleExtensionOfReal C D K u xStar := by
  intro xStar
  -- Step 1: the domain-subset lemma shows that `u` lies outside the parameter domain of the
  -- canonical witness.
  have huOutside :
      u ∉ convexBifunctionParameterDomain
        (helperForCorollary33_3_3_canonicalWitness C D K) := by
    intro huDom
    exact
      hu
        (helperForCorollary33_3_3_canonicalWitness_parameterDomain_subset
          (C := C) (D := D) (K := K) huDom)
  -- Step 2: off `dom F`, every primal pairing value is `⊥`, which matches the off-`C`
  -- value of the lower simple extension.
  calc
    convexBifunctionPairing (helperForCorollary33_3_3_canonicalWitness C D K) u xStar = ⊥ := by
      exact
        helperForCorollary33_2_2_convex_pairing_eq_bot_of_off_parameterDomain
          (G := helperForCorollary33_3_3_canonicalWitness C D K) huOutside xStar
    _ = lowerSimpleExtensionOfReal C D K u xStar := by
      simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu]

/-- Helper for Corollary33.3.3: every section of the canonical witness is already
convex-closed. On `C` this comes from the general closedness of convex conjugates, while off
`C` the section is the constant `⊤` function. -/
lemma helperForCorollary33_3_3_canonicalWitness_sections_areFunctionConvexClosed
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hD_nonempty : D.Nonempty) :
    ∀ u : Fin m → ℝ,
      IsFunctionConvexClosed (helperForCorollary33_3_3_canonicalWitness C D K u) := by
  intro u
  by_cases hu : u ∈ C
  · rcases hD_nonempty with ⟨xStar, hxStar⟩
    -- Step 1: on `C`, the lower simple extension section has a finite point on `D`, so its
    -- convex conjugate is convex-closed.
    have hPoint :
        lowerSimpleExtensionOfReal C D K u xStar ≠ ⊤ := by
      have hValue :
          lowerSimpleExtensionOfReal C D K u xStar = ↑(K u xStar) := by
        simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu, hxStar,
          erealOfRealBifunction]
      rw [hValue]
      exact EReal.coe_ne_top (K u xStar)
    simpa [helperForCorollary33_3_3_canonicalWitness] using
      (helperForTheorem33_1_convexConjugate_isFunctionConvexClosed_of_point
        (f := lowerSimpleExtensionOfReal C D K u) (x₀ := xStar) hPoint)
  · -- Step 1: off `C`, the explicit primal formula makes the whole section constantly `⊤`,
    -- and constant functions are fixed by the raw convex closure.
    have hTopSection :
        helperForCorollary33_3_3_canonicalWitness C D K u =
          fun _ : Fin n → ℝ => (⊤ : EReal) := by
      funext x
      simpa [hu] using
        helperForCorollary33_3_3_canonicalWitness_primalFormula
          (C := C) (D := D) (K := K) u x
    unfold IsFunctionConvexClosed
    rw [hTopSection]
    exact
      helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
        (lowerSemicontinuous_const :
          LowerSemicontinuous (fun _ : Fin n → ℝ => (⊤ : EReal)))

/-- Helper for Corollary33.3.3: because every section of the canonical witness is
convex-closed and avoids `⊥`, its Chapter 2 convex closure agrees pointwise with the
section itself. -/
lemma helperForCorollary33_3_3_canonicalWitness_sectionConvexClosure_exact
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hD_nonempty : D.Nonempty) :
    ∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
      convexFunctionClosure (helperForCorollary33_3_3_canonicalWitness C D K u) x =
        helperForCorollary33_3_3_canonicalWitness C D K u x := by
  intro u x
  -- Step 1: use the already-proved no-`⊥` property to replace the Chapter 2 closure by the
  -- local raw convex closure.
  have hNoBotSection :
      ∀ y : Fin n → ℝ,
        helperForCorollary33_3_3_canonicalWitness C D K u y ≠ (⊥ : EReal) := by
    intro y
    exact
      helperForCorollary33_3_3_canonicalWitness_hasNoBotValues
        (C := C) (D := D) (K := K) hD_nonempty u y
  have hSectionClosed :
      IsFunctionConvexClosed (helperForCorollary33_3_3_canonicalWitness C D K u) :=
    helperForCorollary33_3_3_canonicalWitness_sections_areFunctionConvexClosed
      (C := C) (D := D) (K := K) hD_nonempty u
  calc
    convexFunctionClosure (helperForCorollary33_3_3_canonicalWitness C D K u) x =
        functionConvexClosure (helperForCorollary33_3_3_canonicalWitness C D K u) x := by
          rw [← helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
            (f := helperForCorollary33_3_3_canonicalWitness C D K u) hNoBotSection]
    _ = helperForCorollary33_3_3_canonicalWitness C D K u x := by
          exact
            helperForLemma33_0_18_functionConvexClosure_eq_self
              (f := helperForCorollary33_3_3_canonicalWitness C D K u) hSectionClosed x

/-- Helper for Corollary33.3.3: on the primal domain `C`, the frozen lower simple-extension
section is convex and lower semicontinuous in the dual variable. -/
lemma helperForCorollary33_3_3_onDomain_lowerSimpleExtension_section_convexClosed
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D)
    (hK_cont : ContinuousOn (fun p => K p.1 p.2) (C.prod D))
    (hK_concaveConvex : IsConcaveConvexOn C D (erealOfRealBifunction K))
    {u : Fin m → ℝ}
    (hu : u ∈ C) :
    IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (lowerSimpleExtensionOfReal C D K u) ∧
      LowerSemicontinuous (lowerSimpleExtensionOfReal C D K u) := by
  constructor
  · -- Step 1: prove convexity directly from the convexity of the original section on `D`,
    -- splitting off the zero-coefficient cases when one endpoint lies outside `D`.
    intro x y _ _ a b ha hb hab _
    by_cases hx : x ∈ D
    · by_cases hy : y ∈ D
      · have hxy : a • x + b • y ∈ D := hD_convex hx hy ha hb hab
        have hConvSection :
            (erealOfRealBifunction K) u (a • x + b • y) ≤
              (a : EReal) * (erealOfRealBifunction K) u x +
                (b : EReal) * (erealOfRealBifunction K) u y :=
          hK_concaveConvex.2 u hu hx hy ha hb hab hxy
        simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
          hu, hx, hy, hxy] using hConvSection
      · by_cases hb0 : b = 0
        · have ha1 : a = 1 := by linarith
          have hxy : a • x + b • y = x := by
            subst hb0
            simp [ha1]
          simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
            hu, hx, hy, hb0, ha1, hxy]
        · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          have hBotNe :
              ((a : EReal) * lowerSimpleExtensionOfReal C D K u x) ≠ (⊥ : EReal) := by
            rw [show lowerSimpleExtensionOfReal C D K u x = (↑(K u x) : EReal) by
              simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                hu, hx]]
            exact (EReal.mul_ne_bot _ _).2 (by constructor <;> constructor <;> simp [ha])
          have hRightTop :
              (a : EReal) * lowerSimpleExtensionOfReal C D K u x +
                  (b : EReal) * lowerSimpleExtensionOfReal C D K u y =
                (⊤ : EReal) := by
            rw [show (b : EReal) * lowerSimpleExtensionOfReal C D K u y = (⊤ : EReal) by
              rw [show lowerSimpleExtensionOfReal C D K u y = (⊤ : EReal) by
                simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                  hu, hy]]
              exact EReal.mul_top_of_pos (by exact_mod_cast hb_pos)]
            exact EReal.add_top_of_ne_bot hBotNe
          exact le_trans le_top (by simpa [hRightTop])
    · by_cases hy : y ∈ D
      · by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          have hxy : a • x + b • y = y := by
            subst ha0
            simp [hb1]
          simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
            hu, hx, hy, ha0, hb1, hxy]
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have hBotNe :
              ((b : EReal) * lowerSimpleExtensionOfReal C D K u y) ≠ (⊥ : EReal) := by
            rw [show lowerSimpleExtensionOfReal C D K u y = (↑(K u y) : EReal) by
              simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                hu, hy]]
            exact (EReal.mul_ne_bot _ _).2 (by constructor <;> constructor <;> simp [hb])
          have hRightTop :
              (a : EReal) * lowerSimpleExtensionOfReal C D K u x +
                  (b : EReal) * lowerSimpleExtensionOfReal C D K u y =
                (⊤ : EReal) := by
            rw [show (a : EReal) * lowerSimpleExtensionOfReal C D K u x = (⊤ : EReal) by
              rw [show lowerSimpleExtensionOfReal C D K u x = (⊤ : EReal) by
                simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                  hu, hx]]
              exact EReal.mul_top_of_pos (by exact_mod_cast ha_pos)]
            exact EReal.top_add_of_ne_bot hBotNe
          exact le_trans le_top (by simpa [hRightTop])
      · by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          have hxy : a • x + b • y = y := by
            subst ha0
            simp [hb1]
          simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
            hu, hx, hy, ha0, hb1, hxy]
        · by_cases hb0 : b = 0
          · have ha1 : a = 1 := by linarith
            have hxy : a • x + b • y = x := by
              subst hb0
              simp [ha1]
            simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
              hu, hx, hy, hb0, ha1, hxy]
          · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
            have hRightTop :
                (a : EReal) * lowerSimpleExtensionOfReal C D K u x +
                    (b : EReal) * lowerSimpleExtensionOfReal C D K u y =
                  (⊤ : EReal) := by
              rw [show (a : EReal) * lowerSimpleExtensionOfReal C D K u x = (⊤ : EReal) by
                rw [show lowerSimpleExtensionOfReal C D K u x = (⊤ : EReal) by
                  simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                    hu, hx]]
                exact EReal.mul_top_of_pos (by exact_mod_cast ha_pos)]
              rw [show (b : EReal) * lowerSimpleExtensionOfReal C D K u y = (⊤ : EReal) by
                rw [show lowerSimpleExtensionOfReal C D K u y = (⊤ : EReal) by
                  simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                    hu, hy]]
                exact EReal.mul_top_of_pos (by exact_mod_cast hb_pos)]
              simp
            exact le_trans le_top (by simpa [hRightTop])
  · -- Step 2: identify every real sublevel with a closed image of the continuous frozen
    -- section restricted to the closed set `D`.
    refine (lowerSemicontinuous_iff_closed_sublevel
      (f := lowerSimpleExtensionOfReal C D K u)).2 ?_
    intro α
    let g : (Fin n → ℝ) → EReal := fun xStar => (↑(K u xStar) : EReal)
    let gD : D → EReal := fun xStar => g ↑xStar
    have hSectionContOn :
        ContinuousOn (fun xStar : Fin n → ℝ => K u xStar) D := by
      have hPairContOn : ContinuousOn (fun xStar : Fin n → ℝ => (u, xStar)) D :=
        (continuous_const.prodMk continuous_id).continuousOn
      have hMapsTo : Set.MapsTo (fun xStar : Fin n → ℝ => (u, xStar)) D (C.prod D) := by
        intro xStar hxStar
        exact ⟨hu, hxStar⟩
      simpa [Function.comp] using hK_cont.comp hPairContOn hMapsTo
    have hContSubtype : Continuous gD := by
      rw [continuousOn_iff_continuous_restrict] at hSectionContOn
      simpa [gD, g] using continuous_coe_real_ereal.comp hSectionContOn
    have hClosedSubtype :
        IsClosed {xStar : D | gD xStar ≤ (α : EReal)} := by
      simpa [Set.preimage, gD, Set.mem_Iic] using
        (isClosed_Iic : IsClosed (Set.Iic (α : EReal))).preimage hContSubtype
    have hClosedImage :
        IsClosed (Subtype.val '' {xStar : D | gD xStar ≤ (α : EReal)} : Set (Fin n → ℝ)) :=
      hD_closed.isClosedMap_subtype_val _ hClosedSubtype
    have hSetEq :
        {xStar : Fin n → ℝ | lowerSimpleExtensionOfReal C D K u xStar ≤ (α : EReal)} =
          (Subtype.val '' {xStar : D | gD xStar ≤ (α : EReal)} : Set (Fin n → ℝ)) := by
      ext xStar
      constructor
      · intro hxStar
        have hxD : xStar ∈ D := by
          by_cases hxD : xStar ∈ D
          · exact hxD
          · have hTopLe :
              (⊤ : EReal) ≤ (α : EReal) := by
              simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                hu, hxD] using hxStar
            exact (not_top_le_coe α hTopLe).elim
        refine ⟨⟨xStar, hxD⟩, ?_⟩
        simpa [gD, g, lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
          hu, hxD] using hxStar
      · rintro ⟨xStar, hxStar, rfl⟩
        simpa [gD, g, lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
          hu, xStar.2] using hxStar
    simpa [hSetEq] using hClosedImage

/-- Helper for Corollary33.3.3: the canonical witness pairs back with the lower simple
extension everywhere. -/
lemma helperForCorollary33_3_3_canonicalWitness_primalPairing_eq_lowerSimpleExtension
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D)
    (hK_cont : ContinuousOn (fun p => K p.1 p.2) (C.prod D))
    (hK_concaveConvex : IsConcaveConvexOn C D (erealOfRealBifunction K)) :
    ∀ u xStar,
      convexBifunctionPairing (helperForCorollary33_3_3_canonicalWitness C D K) u xStar =
        lowerSimpleExtensionOfReal C D K u xStar := by
  intro u xStar
  by_cases hu : u ∈ C
  · -- Step 1: on `C`, the pairing is the biconjugate of a convex lower-semicontinuous
    -- section, so Fenchel-Moreau returns the section itself.
    rcases
        helperForCorollary33_3_3_onDomain_lowerSimpleExtension_section_convexClosed
          (C := C) (D := D) (K := K) hD_closed hD_convex hK_cont hK_concaveConvex hu with
      ⟨hConv, hLower⟩
    have hNoBotSection :
        ∀ y : Fin n → ℝ, lowerSimpleExtensionOfReal C D K u y ≠ (⊥ : EReal) := by
      intro y
      by_cases hy : y ∈ D
      · simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction, hu, hy]
      · simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction, hu, hy]
    have hClosureEq :
        functionConvexClosure (lowerSimpleExtensionOfReal C D K u) =
          lowerSimpleExtensionOfReal C D K u := by
      simpa using
        (helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hLower).symm
    calc
      convexBifunctionPairing (helperForCorollary33_3_3_canonicalWitness C D K) u xStar
          = convexConjugate (convexConjugate (lowerSimpleExtensionOfReal C D K u)) xStar := by
              simp [convexBifunctionPairing, helperForCorollary33_3_3_canonicalWitness]
      _ = functionConvexClosure (lowerSimpleExtensionOfReal C D K u) xStar := by
            exact
              helperForTheorem33_1_biconjugate_eq_functionConvexClosure_of_convex
                (f := lowerSimpleExtensionOfReal C D K u)
                (hConv := hConv) (hNoBot := hNoBotSection) xStar
      _ = lowerSimpleExtensionOfReal C D K u xStar := by
            exact congrArg (fun f => f xStar) hClosureEq
  · -- Step 2: outside `C`, the off-domain collapse was already proved separately.
    simpa using
      helperForCorollary33_3_3_canonicalWitness_primalPairing_eq_lowerSimpleExtension_off_domain
        (C := C) (D := D) (K := K) hu xStar

/-- Helper for Corollary33.3.3: whenever a kernel `K1` is represented as the primal pairing of
`F`, the closure-side adjoint pairing is exactly the first-variable concave closure of `K1`. -/
lemma helperForCorollary33_3_3_closureSideAdjointPairing_eq_firstClosure
    {m n : ℕ}
    {K1 : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_graph : IsGraphConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F)
    (hPair :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        K1 u xStar = convexBifunctionPairing F u xStar) :
    ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
      convexBifunctionCanonicalAdjointPairing F xStar u =
        canonicalConcaveClosureInFirst K1 u xStar := by
  rcases
      (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).1 F
        ⟨hF_graph, hF_noBot⟩ with
    ⟨hFirst, _hSecond⟩
  intro u xStar
  -- Step 1: Theorem 33.2 identifies the closure-side adjoint pairing with the raw
  -- first-variable concave closure of the represented primal pairing section.
  calc
    convexBifunctionCanonicalAdjointPairing F xStar u =
        concaveClosure (fun u' : Fin m → ℝ => convexBifunctionPairing F u' xStar) u :=
      hFirst xStar u
    -- Step 2: rewrite the pairing section through the represented kernel `K1`.
    _ = concaveClosure (fun u' : Fin m → ℝ => K1 u' xStar) u := by
          congr 1
          funext u'
          exact (hPair u' xStar).symm
    -- Step 3: repack the one-variable closure as the kernel-level first closure.
    _ = canonicalConcaveClosureInFirst K1 u xStar := by
          rfl

/-- Helper for Corollary33.3.3: upper semicontinuity fixes the one-variable first-coordinate
concave closure. -/
lemma helperForCorollary33_3_3_functionConcaveClosure_eq_self_of_upperSemicontinuous
    {m : ℕ}
    {g : (Fin m → ℝ) → EReal}
    (hUpper : UpperSemicontinuous g) :
    functionConcaveClosure g = g := by
  -- Step 1: upper semicontinuity of `g` is lower semicontinuity of `-g`.
  have hNegLsc : LowerSemicontinuous (fun u => -g u) :=
    (helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg
      (g := g)).1 hUpper
  -- Step 2: the Chapter 33 convex closure therefore fixes the negated section.
  have hNegClosed :
      (fun u => -g u) = functionConvexClosure (fun u' => -g u') :=
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hNegLsc
  -- Step 3: undo the sign change pointwise to recover the concave-closure identity.
  funext u
  have hPoint :
      functionConvexClosure (fun u' => -g u') u = -g u :=
    congrArg (fun h => h u) hNegClosed.symm
  calc
    functionConcaveClosure g u
        = -functionConvexClosure (fun u' => -g u') u := by
            exact
              congrArg (fun h => h u)
                (helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg
                  (g := g))
    _ = -(-g u) := by rw [hPoint]
    _ = g u := by simp

/-- Helper for Corollary33.3.3: every frozen first-variable section of the lower simple
extension is concave. This is the direct concavity input for the canonical witness's primal
pairing, and it keeps the off-`D` branch separate instead of forcing an incorrect global
closure identity with the upper simple extension. -/
lemma helperForCorollary33_3_3_lowerSimpleExtension_firstSections_areConcave
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_convex : Convex ℝ C)
    (hK_concaveConvex : IsConcaveConvexOn C D (erealOfRealBifunction K)) :
    ∀ xStar : Fin n → ℝ,
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ))
        (fun u => lowerSimpleExtensionOfReal C D K u xStar) := by
  intro xStar
  by_cases hxStar : xStar ∈ D
  · -- Step 1: on `D`, the first-variable section is the original concave section on `C`
    -- and collapses to `⊥` off `C`, so only the zero-coefficient edge cases need splitting.
    intro u v _ _ a b ha hb hab _
    by_cases hu : u ∈ C
    · by_cases hv : v ∈ C
      · have huv : a • u + b • v ∈ C := hC_convex hu hv ha hb hab
        have hConcSection :
            (a : EReal) * (erealOfRealBifunction K) u xStar +
                (b : EReal) * (erealOfRealBifunction K) v xStar ≤
              (erealOfRealBifunction K) (a • u + b • v) xStar :=
          hK_concaveConvex.1 xStar hxStar hu hv ha hb hab huv
        simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
          hu, hv, huv, hxStar] using hConcSection
      · by_cases hb0 : b = 0
        · have ha1 : a = 1 := by linarith
          have huv : a • u + b • v = u := by
            subst hb0
            simp [ha1]
          simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
            hu, hv, hxStar, hb0, ha1, huv]
        · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          have hLeftBot :
              (a : EReal) * lowerSimpleExtensionOfReal C D K u xStar +
                  (b : EReal) * lowerSimpleExtensionOfReal C D K v xStar =
                (⊥ : EReal) := by
            rw [show lowerSimpleExtensionOfReal C D K v xStar = (⊥ : EReal) by
              simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                hv, hxStar]]
            rw [EReal.mul_bot_of_pos (by exact_mod_cast hb_pos), EReal.add_bot]
          exact hLeftBot ▸ bot_le
    · by_cases hv : v ∈ C
      · by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          have huv : a • u + b • v = v := by
            subst ha0
            simp [hb1]
          simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
            hu, hv, hxStar, ha0, hb1, huv]
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have hLeftBot :
              (a : EReal) * lowerSimpleExtensionOfReal C D K u xStar +
                  (b : EReal) * lowerSimpleExtensionOfReal C D K v xStar =
                (⊥ : EReal) := by
            rw [show lowerSimpleExtensionOfReal C D K u xStar = (⊥ : EReal) by
              simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                hu, hxStar]]
            rw [EReal.mul_bot_of_pos (by exact_mod_cast ha_pos), EReal.bot_add]
          exact hLeftBot ▸ bot_le
      · by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          have huv : a • u + b • v = v := by
            subst ha0
            simp [hb1]
          simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
            hu, hv, hxStar, ha0, hb1, huv]
        · by_cases hb0 : b = 0
          · have ha1 : a = 1 := by linarith
            have huv : a • u + b • v = u := by
              subst hb0
              simp [ha1]
            simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
              hu, hv, hxStar, hb0, ha1, huv]
          · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            have hLeftBot :
                (a : EReal) * lowerSimpleExtensionOfReal C D K u xStar +
                    (b : EReal) * lowerSimpleExtensionOfReal C D K v xStar =
                  (⊥ : EReal) := by
              rw [show lowerSimpleExtensionOfReal C D K u xStar = (⊥ : EReal) by
                simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                  hu, hxStar]]
              rw [EReal.mul_bot_of_pos (by exact_mod_cast ha_pos), EReal.bot_add]
            exact hLeftBot ▸ bot_le
  · -- Step 2: off `D`, the section only takes the values `⊤` on `C` and `⊥` off `C`.
    intro u v _ _ a b ha hb hab _
    by_cases hu : u ∈ C
    · by_cases hv : v ∈ C
      · have huv : a • u + b • v ∈ C := hC_convex hu hv ha hb hab
        simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
          hu, hv, huv, hxStar]
      · by_cases hb0 : b = 0
        · have ha1 : a = 1 := by linarith
          have huv : a • u + b • v = u := by
            subst hb0
            simp [ha1]
          simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
            hu, hv, hxStar, hb0, ha1, huv]
        · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          by_cases huv : a • u + b • v ∈ C
          · simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu, huv, hxStar]
          · have hLeftBot :
              (a : EReal) * lowerSimpleExtensionOfReal C D K u xStar +
                  (b : EReal) * lowerSimpleExtensionOfReal C D K v xStar =
                (⊥ : EReal) := by
              rw [show lowerSimpleExtensionOfReal C D K v xStar = (⊥ : EReal) by
                simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                  hv, hxStar]]
              rw [EReal.mul_bot_of_pos (by exact_mod_cast hb_pos), EReal.add_bot]
            rw [hLeftBot]
            simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, huv, hxStar]
    · by_cases hv : v ∈ C
      · by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          have huv : a • u + b • v = v := by
            subst ha0
            simp [hb1]
          simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
            hu, hv, hxStar, ha0, hb1, huv]
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          by_cases huv : a • u + b • v ∈ C
          · simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, hv, huv, hxStar]
          · have hLeftBot :
              (a : EReal) * lowerSimpleExtensionOfReal C D K u xStar +
                  (b : EReal) * lowerSimpleExtensionOfReal C D K v xStar =
                (⊥ : EReal) := by
              rw [show lowerSimpleExtensionOfReal C D K u xStar = (⊥ : EReal) by
                simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                  hu, hxStar]]
              rw [EReal.mul_bot_of_pos (by exact_mod_cast ha_pos), EReal.bot_add]
            rw [hLeftBot]
            simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, huv, hxStar]
      · by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          have huv : a • u + b • v = v := by
            subst ha0
            simp [hb1]
          simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
            hu, hv, hxStar, ha0, hb1, huv]
        · by_cases hb0 : b = 0
          · have ha1 : a = 1 := by linarith
            have huv : a • u + b • v = u := by
              subst hb0
              simp [ha1]
            simpa [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
              hu, hv, hxStar, hb0, ha1, huv]
          · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            have hLeftBot :
                (a : EReal) * lowerSimpleExtensionOfReal C D K u xStar +
                    (b : EReal) * lowerSimpleExtensionOfReal C D K v xStar =
                  (⊥ : EReal) := by
              rw [show lowerSimpleExtensionOfReal C D K u xStar = (⊥ : EReal) by
                simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, erealOfRealBifunction,
                  hu, hxStar]]
              rw [EReal.mul_bot_of_pos (by exact_mod_cast ha_pos), EReal.bot_add]
            exact hLeftBot ▸ bot_le

/-- Helper for Corollary33.3.3: off the dual constraint set `D`, the frozen lower simple
extension section is already upper semicontinuous, so its first-variable concave closure
stays equal to the lower simple extension itself. This records the obstruction to the
proposed global identity `upperSimpleExtension = concaveClosureInFirst lowerSimpleExtension`. -/
lemma helperForCorollary33_3_3_offDualDomain_lowerSimpleExtension_firstClosure_eq
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_closed : IsClosed C)
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∉ D) :
    ∀ u : Fin m → ℝ,
      concaveClosureInFirst (lowerSimpleExtensionOfReal C D K) u xStar =
        lowerSimpleExtensionOfReal C D K u xStar := by
  have hUpper :
      UpperSemicontinuous (fun u : Fin m → ℝ => lowerSimpleExtensionOfReal C D K u xStar) := by
    rw [helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg]
    exact
      (helperForTheorem_6_30_2_closedUpperLevelSet_iff_neg_lsc
        (g := fun u : Fin m → ℝ => lowerSimpleExtensionOfReal C D K u xStar)).1
        (fun α => by
          have hSetEq :
              concaveUpperLevelSet
                  (fun u : Fin m → ℝ => lowerSimpleExtensionOfReal C D K u xStar) α = C := by
            ext u
            by_cases hu : u ∈ C
            · simp [concaveUpperLevelSet, lowerSimpleExtensionOfReal, lowerSimpleExtension,
                erealOfRealBifunction, hxStar, hu]
            · simp [concaveUpperLevelSet, lowerSimpleExtensionOfReal, lowerSimpleExtension,
                erealOfRealBifunction, hxStar, hu]
          simpa [hSetEq] using hC_closed)
  have hClosureEq :
      functionConcaveClosure (fun u : Fin m → ℝ => lowerSimpleExtensionOfReal C D K u xStar) =
        (fun u : Fin m → ℝ => lowerSimpleExtensionOfReal C D K u xStar) :=
    helperForCorollary33_3_3_functionConcaveClosure_eq_self_of_upperSemicontinuous hUpper
  intro u
  simpa [concaveClosureInFirst, functionConcaveClosure] using congrArg (fun h => h u) hClosureEq

/-- Helper for Corollary33.3.3: on the dual constraint set `D`, the frozen lower simple
extension section is already upper semicontinuous in the first variable, so its first-variable
concave closure is exact. -/
lemma helperForCorollary33_3_3_onDualDomain_lowerSimpleExtension_firstClosure_eq
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_closed : IsClosed C)
    (hK_cont : ContinuousOn (fun p => K p.1 p.2) (C.prod D))
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ D) :
    ∀ u : Fin m → ℝ,
      concaveClosureInFirst (lowerSimpleExtensionOfReal C D K) u xStar =
        lowerSimpleExtensionOfReal C D K u xStar := by
  have hUpper :
      UpperSemicontinuous (fun u : Fin m → ℝ => lowerSimpleExtensionOfReal C D K u xStar) := by
    rw [helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg]
    exact
      (helperForTheorem_6_30_2_closedUpperLevelSet_iff_neg_lsc
        (g := fun u : Fin m → ℝ => lowerSimpleExtensionOfReal C D K u xStar)).1
        (fun α => by
          let g : (Fin m → ℝ) → EReal := fun u => (↑(K u xStar) : EReal)
          let gC : C → EReal := fun u => g ↑u
          have hSectionContOn :
              ContinuousOn (fun u : Fin m → ℝ => K u xStar) C := by
            have hPairContOn : ContinuousOn (fun u : Fin m → ℝ => (u, xStar)) C :=
              (continuous_id.prodMk continuous_const).continuousOn
            have hMapsTo : Set.MapsTo (fun u : Fin m → ℝ => (u, xStar)) C (C.prod D) := by
              intro u hu
              exact ⟨hu, hxStar⟩
            simpa [Function.comp] using hK_cont.comp hPairContOn hMapsTo
          have hContSubtype : Continuous gC := by
            rw [continuousOn_iff_continuous_restrict] at hSectionContOn
            simpa [gC, g] using continuous_coe_real_ereal.comp hSectionContOn
          have hClosedSubtype :
              IsClosed {u : C | (α : EReal) ≤ gC u} := by
            simpa [Set.preimage, gC, Set.mem_Ici] using
              (isClosed_Ici : IsClosed (Set.Ici (α : EReal))).preimage hContSubtype
          have hClosedImage :
              IsClosed (Subtype.val '' {u : C | (α : EReal) ≤ gC u} : Set (Fin m → ℝ)) :=
            hC_closed.isClosedMap_subtype_val _ hClosedSubtype
          have hSetEq :
              concaveUpperLevelSet
                  (fun u : Fin m → ℝ => lowerSimpleExtensionOfReal C D K u xStar) α =
                (Subtype.val '' {u : C | (α : EReal) ≤ gC u} : Set (Fin m → ℝ)) := by
            ext u
            constructor
            · intro hu
              have huC : u ∈ C := by
                by_cases huC : u ∈ C
                · exact huC
                · have hLeBot :
                    (α : EReal) ≤ (⊥ : EReal) := by
                    simpa [concaveUpperLevelSet, lowerSimpleExtensionOfReal, lowerSimpleExtension,
                      erealOfRealBifunction, huC, hxStar] using hu
                  exact False.elim ((not_le_of_gt (EReal.bot_lt_coe α)) hLeBot)
              refine ⟨⟨u, huC⟩, ?_⟩
              simpa [concaveUpperLevelSet, gC, g, lowerSimpleExtensionOfReal, lowerSimpleExtension,
                erealOfRealBifunction, huC, hxStar] using hu
            · rintro ⟨u, hu, rfl⟩
              simpa [concaveUpperLevelSet, gC, g, lowerSimpleExtensionOfReal, lowerSimpleExtension,
                erealOfRealBifunction, u.2, hxStar] using hu
          simpa [hSetEq] using hClosedImage)
  have hClosureEq :
      functionConcaveClosure (fun u : Fin m → ℝ => lowerSimpleExtensionOfReal C D K u xStar) =
        (fun u : Fin m → ℝ => lowerSimpleExtensionOfReal C D K u xStar) :=
    helperForCorollary33_3_3_functionConcaveClosure_eq_self_of_upperSemicontinuous hUpper
  intro u
  simpa [concaveClosureInFirst, functionConcaveClosure] using congrArg (fun h => h u) hClosureEq

/-- Helper for Corollary33.3.3: a globally concave frozen first-variable section is a
Chapter 6 concave function, so the concave biconjugate theorem applies to it directly. -/
lemma helperForCorollary33_3_3_concaveFunction_of_firstSectionConcavity
    {m n : ℕ}
    {K1 : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {xStar : Fin n → ℝ}
    (hSection :
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u : Fin m → ℝ => K1 u xStar))
    (hNoTop : ∀ u : Fin m → ℝ, K1 u xStar ≠ ⊤) :
    ConcaveFunction (fun u : Fin m → ℝ => K1 u xStar) := by
  -- Step 1: reinterpret the univ-domain Jensen inequality as convexity of the negated
  -- section. The added `⊤`-avoidance hypothesis is exactly what lets `EReal.neg_add`
  -- distribute across the weighted sum without hitting exceptional branches.
  unfold ConcaveFunction
  apply helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction
  intro x y _ _ a b ha hb hab _
  have hConc :
      (a : EReal) * K1 x xStar + (b : EReal) * K1 y xStar ≤
        K1 (a • x + b • y) xStar :=
    hSection (x := x) (y := y) (by simp) (by simp) ha hb hab (by simp)
  have hTerm1_ne_top : (a : EReal) * K1 x xStar ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inl ?_, Or.inl (EReal.coe_ne_top a), ?_⟩
    · exact_mod_cast ha
    · by_cases hZero : a = 0
      · left
        simp [hZero]
      · right
        exact hNoTop x
  have hTerm2_ne_top : (b : EReal) * K1 y xStar ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot b), Or.inl ?_, Or.inl (EReal.coe_ne_top b), ?_⟩
    · exact_mod_cast hb
    · by_cases hZero : b = 0
      · left
        simp [hZero]
      · right
        exact hNoTop y
  have hNegJensen :
      -K1 (a • x + b • y) xStar ≤
        -((a : EReal) * K1 x xStar + (b : EReal) * K1 y xStar) := by
    simpa using (EReal.neg_le_neg_iff.2 hConc)
  have hNegWeighted :
      -((a : EReal) * K1 x xStar + (b : EReal) * K1 y xStar) =
        (a : EReal) * (-K1 x xStar) + (b : EReal) * (-K1 y xStar) := by
    -- Step 2: with both weighted terms away from `⊤`, negation distributes over the sum.
    have hNegAdd :=
      EReal.neg_add (x := (a : EReal) * K1 x xStar) (y := (b : EReal) * K1 y xStar)
        (Or.inr hTerm2_ne_top) (Or.inl hTerm1_ne_top)
    simpa [sub_eq_add_neg, mul_neg, neg_mul, add_comm] using hNegAdd
  -- Step 3: chaining the negated Jensen inequality with the exact negated-sum rewrite yields
  -- the convexity inequality for the negated section.
  calc
    -K1 (a • x + b • y) xStar ≤ -((a : EReal) * K1 x xStar + (b : EReal) * K1 y xStar) :=
      hNegJensen
    _ = (a : EReal) * (-K1 x xStar) + (b : EReal) * (-K1 y xStar) := hNegWeighted


end Section33
end Chap07
