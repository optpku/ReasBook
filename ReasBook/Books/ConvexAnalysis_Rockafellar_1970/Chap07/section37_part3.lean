/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part2

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Corollary 37.1.3: at zero tilt, the upper Section 37 conjugate is exactly the
negative of the textbook minimax value. -/
lemma helperForCorollary_37_1_3_zeroTilt_upperConjugate_eq_neg_minimaxValue
    (K : SaddleFunction m n) :
    theorem37ValueSupInf K 0 0 =
      - minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
  -- The existing Proposition 37.1.3 helper already computes the negated zero-tilt value.
  have hNeg :
      -theorem37ValueSupInf K 0 0 =
        minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
    simpa [minimaxValue] using helperForProposition_37_1_3_zeroLowerConjugateValue (K := K)
  exact neg_injective (by simpa using hNeg)

/-- Helper for Corollary 37.1.3: at zero tilt, the lower Section 37 conjugate is exactly the
negative of the textbook maximin value. -/
lemma helperForCorollary_37_1_3_zeroTilt_lowerConjugate_eq_neg_maximinValue
    (K : SaddleFunction m n) :
    theorem37ValueInfSup K 0 0 =
      - maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
  -- The companion Proposition 37.1.3 helper computes the negated zero-tilt value as well.
  have hNeg :
      -theorem37ValueInfSup K 0 0 =
        maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
    simpa [maximinValue] using helperForProposition_37_1_3_zeroUpperConjugateValue (K := K)
  exact neg_injective (by simpa using hNeg)

/-- Helper for Corollary 37.1.3: equality of the two zero-tilt Section 37 conjugates already
forces the textbook minimax identity. -/
lemma helperForCorollary_37_1_3_originConjugateAgreement_implies_minimax
    (K : SaddleFunction m n)
    (hEq0 : theorem37ValueSupInf K 0 0 = theorem37ValueInfSup K 0 0) :
    minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
      maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
  -- Rewrite the two origin conjugates as negatives of the textbook minimax and maximin values.
  have hUpperRewrite :
      theorem37ValueSupInf K 0 0 =
        - minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K :=
    helperForCorollary_37_1_3_zeroTilt_upperConjugate_eq_neg_minimaxValue (K := K)
  have hLowerRewrite :
      theorem37ValueInfSup K 0 0 =
        - maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K :=
    helperForCorollary_37_1_3_zeroTilt_lowerConjugate_eq_neg_maximinValue (K := K)
  have hNegEq :
      - minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
        - maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := by
    -- The assumed origin agreement becomes equality of the two negated saddle values.
    calc
      - minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K
          = theorem37ValueSupInf K 0 0 := hUpperRewrite.symm
      _ = theorem37ValueInfSup K 0 0 := hEq0
      _ = - maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := hLowerRewrite
  -- Negation is injective on `EReal`, so the original saddle values are equal as well.
  exact neg_injective hNegEq

/-- Helper for Corollary 37.1.3: Corollary 37.1.2 identifies a common relative-interior point of
the two zero-tilt effective domains with equality of the two conjugate values at the origin. -/
lemma helperForCorollary_37_1_3_zeroConjugates_agree_of_originInCommonRelativeInterior
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (hOrigin :
      (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ
          (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) ∨
        (0 : Fin n → ℝ) ∈ intrinsicInterior ℝ
          (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x))) :
    theorem37ValueSupInf K 0 0 = theorem37ValueInfSup K 0 0 := by
  rcases corollary37_1_2_lower_upper_conjugates_structure K hKclosed hKproper hGlobal with
    ⟨CStar, DStar, _, _, _, _, hDom1Lower, hDom2Lower, _, _, _, _, hAgree⟩
  -- Replace the abstract witness domains by the concrete effective domains before specializing
  -- the agreement statement, so no intrinsic-interior transport remains to solve.
  subst CStar
  subst DStar
  -- The relative-interior agreement theorem can now be applied directly at `(0, 0)`.
  exact hAgree 0 0 hOrigin

/-- Helper for Corollary 37.1.3: origin membership in the two coordinate effective domains is
exactly the pair of strict lower and upper bounds on the zero-tilt saddle value. -/
lemma helperForCorollary_37_1_3_originEffectiveDomain_membership_gives_zeroTilt_strictBounds
    (K : SaddleFunction m n)
    (hMem1 :
      (0 : Fin m → ℝ) ∈ effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x))
    (hMem2 :
      (0 : Fin n → ℝ) ∈ effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) :
    (⊥ : EReal) < theorem37ValueSupInf K 0 0 ∧
      theorem37ValueSupInf K 0 0 < (⊤ : EReal) := by
  constructor
  · -- First-coordinate domain membership means every second-coordinate slice stays above `⊥`.
    exact hMem1 0
  · -- Second-coordinate domain membership means every first-coordinate slice stays below `⊤`.
    exact hMem2 0

/-- Helper for Corollary 37.1.3: once the zero-tilt saddle value is squeezed strictly between
`⊥` and `⊤`, it is finite in the extended-real sense. -/
lemma helperForCorollary_37_1_3_zeroTilt_strictBounds_imply_finiteness
    (K : SaddleFunction m n)
    (hBounds :
      (⊥ : EReal) < theorem37ValueSupInf K 0 0 ∧
        theorem37ValueSupInf K 0 0 < (⊤ : EReal)) :
    theorem37ValueSupInf K 0 0 ≠ (⊤ : EReal) ∧ theorem37ValueSupInf K 0 0 ≠ (⊥ : EReal) := by
  constructor
  · -- Anything strictly below `⊤` cannot equal `⊤`.
    exact ne_of_lt hBounds.2
  · -- Anything strictly above `⊥` cannot equal `⊥`.
    exact ne_of_gt hBounds.1

/-- Helper for Corollary 37.1.3: if the origin lies in both common relative interiors, then the
zero-tilt saddle value avoids both `⊤` and `⊥`. -/
lemma helperForCorollary_37_1_3_zeroSaddleValue_finite_of_originInBothRelativeInteriors
    (K : SaddleFunction m n)
    (hOrigin1 :
      (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ
        (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)))
    (hOrigin2 :
      (0 : Fin n → ℝ) ∈ intrinsicInterior ℝ
        (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x))) :
    theorem37ValueSupInf K 0 0 ≠ (⊤ : EReal) ∧ theorem37ValueSupInf K 0 0 ≠ (⊥ : EReal) := by
  -- Relative-interior membership drops to honest effective-domain membership in each coordinate.
  have hMem1 :
      (0 : Fin m → ℝ) ∈ effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x) := by
    exact intrinsicInterior_subset (𝕜 := ℝ)
      (s := effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) hOrigin1
  have hMem2 :
      (0 : Fin n → ℝ) ∈ effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x) := by
    exact intrinsicInterior_subset (𝕜 := ℝ)
      (s := effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) hOrigin2
  -- Read the two effective-domain memberships as the strict lower and upper bounds at `(0, 0)`.
  have hBounds :
      (⊥ : EReal) < theorem37ValueSupInf K 0 0 ∧
        theorem37ValueSupInf K 0 0 < (⊤ : EReal) :=
    helperForCorollary_37_1_3_originEffectiveDomain_membership_gives_zeroTilt_strictBounds
      (K := K) hMem1 hMem2
  -- Convert those strict bounds into the advertised finiteness statement.
  exact helperForCorollary_37_1_3_zeroTilt_strictBounds_imply_finiteness (K := K) hBounds

/-- Helper for Corollary 37.1.3: finiteness of the zero-tilt upper conjugate transports to the
textbook minimax value because Proposition 37.1.3 identifies that conjugate with its negation. -/
lemma helperForCorollary_37_1_3_zeroTiltUpperConjugate_finite_implies_minimaxFinite
    (K : SaddleFunction m n)
    (hFiniteZero :
      theorem37ValueSupInf K 0 0 ≠ (⊤ : EReal) ∧
        theorem37ValueSupInf K 0 0 ≠ (⊥ : EReal)) :
    minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊤ : EReal) ∧
      minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊥ : EReal) := by
  have hUpperRewrite :
      theorem37ValueSupInf K 0 0 =
        - minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K :=
    helperForCorollary_37_1_3_zeroTilt_upperConjugate_eq_neg_minimaxValue (K := K)
  have hFiniteNeg :
      - minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊤ : EReal) ∧
        - minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊥ : EReal) := by
    -- Rewrite the zero-tilt value as the negated minimax quantity before transporting
    -- the two finiteness inequalities.
    simpa [hUpperRewrite] using hFiniteZero
  constructor
  · intro hTop
    -- `-⊤ = ⊥`, so a top minimax value would contradict the lower component of `hFiniteNeg`.
    exact hFiniteNeg.2 (by simp [hTop])
  · intro hBot
    -- `-⊥ = ⊤`, so a bottom minimax value would contradict the upper component of `hFiniteNeg`.
    exact hFiniteNeg.1 (by simp [hBot])

/-- Corollary 37.1.3: if the origin lies in the relative interior of either common effective
domain of the two Section 37 conjugates, then the minimax and maximin values of `K` coincide; if
it lies in both, then this common saddle-value is finite. -/
theorem corollary37_1_3_origin_relativeInterior_yields_minimax
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    let KLowerStar : SaddleFunction m n := fun uStar x => theorem37ValueSupInf K uStar x
    let CStar : Set (Fin m → ℝ) := effectiveDomain₁ KLowerStar
    let DStar : Set (Fin n → ℝ) := effectiveDomain₂ KLowerStar
    (((0 : Fin m → ℝ) ∈ intrinsicInterior ℝ CStar) ∨
        ((0 : Fin n → ℝ) ∈ intrinsicInterior ℝ DStar)) →
      minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
        maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ∧
        ((((0 : Fin m → ℝ) ∈ intrinsicInterior ℝ CStar) ∧
            ((0 : Fin n → ℝ) ∈ intrinsicInterior ℝ DStar)) →
          minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊤ : EReal) ∧
            minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊥ : EReal)) := by
  dsimp
  intro hOrigin
  constructor
  · -- First identify the zero-tilt conjugates via the common-domain package from Corollary 37.1.2.
    have hZeroAgree :
        theorem37ValueSupInf K 0 0 = theorem37ValueInfSup K 0 0 :=
      helperForCorollary_37_1_3_zeroConjugates_agree_of_originInCommonRelativeInterior
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hOrigin
    -- The first sentence is exactly the abstract origin-agreement bridge proved above.
    exact helperForCorollary_37_1_3_originConjugateAgreement_implies_minimax
      (K := K) hZeroAgree
  · intro hOriginBoth
    -- The stronger two-sided origin hypothesis makes the zero-tilt saddle value finite.
    have hFiniteZero :
        theorem37ValueSupInf K 0 0 ≠ (⊤ : EReal) ∧
          theorem37ValueSupInf K 0 0 ≠ (⊥ : EReal) :=
      helperForCorollary_37_1_3_zeroSaddleValue_finite_of_originInBothRelativeInteriors
        (K := K) (hOrigin1 := hOriginBoth.1) (hOrigin2 := hOriginBoth.2)
    -- Transport the zero-tilt finiteness bounds through the zero-tilt rewrite to the minimax
    -- value itself.
    exact
      helperForCorollary_37_1_3_zeroTiltUpperConjugate_finite_implies_minimaxFinite
        (K := K) hFiniteZero

end Section37
end Chap07
