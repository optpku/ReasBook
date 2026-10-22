/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part4

section Chap07
section Section34

open Set

section SaddleAmbient

variable {m n : ℕ}

/-- Helper for Text 34.1.4: the textbook upper closure agrees with the canonical upper
partner exactly when the raw mixed-order comparison holds. -/
lemma helperForText_34_1_4_textbookUpper_eq_canonicalUpper_iff_rawMixedClosureOrder
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K) :
    upperClosureConcaveConvex K h = partialClosure₁ (lowerClosureConcaveConvex K h) ↔
      partialClosure₂ (partialClosure₁ K) ≤ partialClosure₁ (partialClosure₂ K) := by
  constructor
  · intro hUpperEqCanonical
    have hOrder :
        lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h :=
      calc
        lowerClosureConcaveConvex K h ≤ partialClosure₁ (lowerClosureConcaveConvex K h) :=
          helperForText_34_1_4_lowerClosure_below_canonicalUpperPartner K h
        _ = upperClosureConcaveConvex K h := hUpperEqCanonical.symm
    exact
      (helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).1 hOrder
  · intro hRawOrder
    have hOrder :
        lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h :=
      (helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).2 hRawOrder
    have hRecover :
        partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h :=
      helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_mixedClosure_order K h hNoBotK hOrder
    exact
      (helperForText_34_1_4_firstClosureOfLower_eq_upper_of_secondClosure_eq_lower K h
        hNoBotK hRecover).symm

/-- Helper for Text 34.1.4: once the exact recovery `cl₂ overline(K) = underline(K)` is
available, the textbook upper closure is the canonical Section 33 upper partner. -/
lemma helperForText_34_1_4_textbookUpper_eq_canonicalUpper_of_secondClosure_eq_lower
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hRecover :
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h) :
    upperClosureConcaveConvex K h = partialClosure₁ (lowerClosureConcaveConvex K h) := by
  exact
    (helperForText_34_1_4_firstClosureOfLower_eq_upper_of_secondClosure_eq_lower K h
      hNoBotK hRecover).symm

/-- Helper for Text 34.1.4: the mixed-order comparison identifies the textbook upper
closure with the canonical upper partner. -/
lemma helperForText_34_1_4_textbookUpper_eq_canonicalUpper_of_mixedClosure_order
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h) :
    upperClosureConcaveConvex K h = partialClosure₁ (lowerClosureConcaveConvex K h) := by
  have hRecover :
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h :=
    helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_mixedClosure_order K h hNoBotK hOrder
  exact
    helperForText_34_1_4_textbookUpper_eq_canonicalUpper_of_secondClosure_eq_lower K h
      hNoBotK hRecover

/-- Helper for Text 34.1.4: the raw mixed-order comparison identifies the textbook upper
closure with the canonical upper partner. -/
lemma helperForText_34_1_4_textbookUpper_eq_canonicalUpper_of_rawMixedClosureOrder
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hRawOrder : partialClosure₂ (partialClosure₁ K) ≤ partialClosure₁ (partialClosure₂ K)) :
    upperClosureConcaveConvex K h = partialClosure₁ (lowerClosureConcaveConvex K h) := by
  have hOrder :
      lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h :=
    (helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).2 hRawOrder
  exact
    helperForText_34_1_4_textbookUpper_eq_canonicalUpper_of_mixedClosure_order K h hNoBotK hOrder

/-- The translated-tilted value equality rewrites its primal value at the origin as the
corresponding Chapter 6 dual-program value. -/
lemma helperForText_34_1_4_translatedTilted_originPrimal_eq_dualProgram
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) 0 =
      dualProgramOfConvexProgram
        ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ := by
  have hDualRange :
      Set.range
          (fun vStar : Fin m → ℝ =>
            adjointOfConvexBifunction
              ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩
              (0 : Fin n → ℝ) vStar) =
        Set.range
          (fun vStar : Fin m → ℝ =>
            genuineConvexBifunctionAdjoint F xStar vStar - ↑(u ⬝ᵥ vStar)) := by
    simpa [adjointOfConvexBifunction, genuineConvexBifunctionAdjoint] using
      helperForLemma33_0_35_translatedTiltedDualRange_eq_targetDualRange
        (F := F) u xStar
  unfold HasEqualOptimalValuesForTranslatedTiltedPrograms at hEqualValues
  calc
    convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) 0
        = sInf (Set.range fun y : Fin n → ℝ => F u y - ↑(y ⬝ᵥ xStar)) := by
            simp [convexProgramAssociatedWith, translatedTiltedBifunction]
    _ = sSup
          (Set.range fun vStar : Fin m → ℝ =>
            genuineConvexBifunctionAdjoint F xStar vStar - ↑(u ⬝ᵥ vStar)) := hEqualValues
    _ = dualProgramOfConvexProgram
          ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ := by
            symm
            unfold dualProgramOfConvexProgram dualPerturbationFunctionOfConvexProgram
              concaveProgramAssociatedWith
            simpa using congrArg sSup hDualRange

/-- Equal translated primal and dual values exclude the exceptional `(top, bottom)` branch. -/
lemma helperForText_34_1_4_translatedTilted_notBothInconsistent
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    ¬ (convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) 0 = (⊤ : EReal) ∧
        dualProgramOfConvexProgram
            ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ = (⊥ : EReal)) := by
  have hValueEq :
      convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) 0 =
        dualProgramOfConvexProgram
          ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ :=
    helperForText_34_1_4_translatedTilted_originPrimal_eq_dualProgram
      (F := F) u xStar hGClosed hEqualValues
  intro hBad
  have : (⊤ : EReal) = (⊥ : EReal) := by
    calc
      (⊤ : EReal)
          = convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) 0 := hBad.1.symm
      _ = dualProgramOfConvexProgram
            ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ := hValueEq
      _ = (⊥ : EReal) := hBad.2
  exact top_ne_bot this

/-- Corollary 6.30.3 applied after excluding the exceptional translated branch. -/
lemma helperForText_34_1_4_translatedTilted_liminf_limsup_package
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hGClosed : ClosedConvexBifunction (translatedTiltedBifunction F u xStar))
    (hEqualValues : HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar) :
    Filter.liminf
        (convexProgramAssociatedWith (translatedTiltedBifunction F u xStar))
        (nhds (0 : Fin m → ℝ)) =
        dualPerturbationFunctionOfConvexProgram
          ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ 0 ∧
      Filter.limsup
          (dualPerturbationFunctionOfConvexProgram
            ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩)
          (nhds (0 : Fin n → ℝ)) =
        convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) 0 := by
  have hNotBothInconsistent :
      ¬ (convexProgramAssociatedWith (translatedTiltedBifunction F u xStar) 0 = (⊤ : EReal) ∧
          dualProgramOfConvexProgram
              ⟨translatedTiltedBifunction F u xStar, hGClosed.1⟩ = (⊥ : EReal)) :=
    helperForText_34_1_4_translatedTilted_notBothInconsistent
      (F := F) u xStar hGClosed hEqualValues
  exact
    corollary_6_30_2_3
      (F := ⟨translatedTiltedBifunction F u xStar, hGClosed⟩) hNotBothInconsistent

end SaddleAmbient

end Section34
end Chap07
