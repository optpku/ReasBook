/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part6

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Theorem 37.3: condition (a) transports the origin from the ordinary interior of
`D*` to the intrinsic interior needed by Corollary 37.1.3. -/
lemma helperForTheorem_37_3_origin_mem_intrinsicInterior_secondDual_of_noCommonSecondRecession
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hNoCommonSecond :
      ∀ w : Fin n → ℝ, w ≠ 0 →
        ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
          ¬ IsRecessionDirection (K u.1) w) :
    (0 : Fin n → ℝ) ∈ intrinsicInterior ℝ
      (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) := by
  have h3721 :=
    corollary37_2_1_origin_interior_iff_no_common_recession_direction
      K hKclosed hKproper hQ
  dsimp at h3721
  -- Corollary 37.2.1 rewrites condition (a) as ordinary interior membership in `D*`.
  have hOriginInterior :
      (0 : Fin n → ℝ) ∈
        interior (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) :=
    h3721.1.mpr hNoCommonSecond
  -- Ordinary interior points automatically lie in the intrinsic interior.
  exact
    interior_subset_intrinsicInterior
      (s := effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x))
      hOriginInterior

/-- Helper for Theorem 37.3: condition (b) transports the origin from the ordinary interior of
`C*` to the intrinsic interior needed by Corollary 37.1.3. -/
lemma helperForTheorem_37_3_origin_mem_intrinsicInterior_firstDual_of_noCommonFirstRecession
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hNoCommonFirst :
      ∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) :
    (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ
      (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) := by
  have h3721 :=
    corollary37_2_1_origin_interior_iff_no_common_recession_direction
      K hKclosed hKproper hQ
  dsimp at h3721
  -- Corollary 37.2.1 rewrites condition (b) as ordinary interior membership in `C*`.
  have hOriginInterior :
      (0 : Fin m → ℝ) ∈
        interior (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) :=
    h3721.2.mpr hNoCommonFirst
  -- Ordinary interior points automatically lie in the intrinsic interior.
  exact
    interior_subset_intrinsicInterior
      (s := effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x))
      hOriginInterior

/-- Helper for Theorem 37.3: when both recession-direction conditions hold, Corollary 37.1.3
gives finiteness of the common saddle-value. -/
lemma helperForTheorem_37_3_finiteSaddleValue_of_bothNoCommonRecessionConditions
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hNoCommonSecond :
      ∀ w : Fin n → ℝ, w ≠ 0 →
        ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
          ¬ IsRecessionDirection (K u.1) w)
    (hNoCommonFirst :
      ∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) :
    minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊤ : EReal) ∧
      minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊥ : EReal) := by
  have hSecondDual :
      (0 : Fin n → ℝ) ∈ intrinsicInterior ℝ
        (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) :=
    helperForTheorem_37_3_origin_mem_intrinsicInterior_secondDual_of_noCommonSecondRecession
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hNoCommonSecond
  have hFirstDual :
      (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ
        (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) :=
    helperForTheorem_37_3_origin_mem_intrinsicInterior_firstDual_of_noCommonFirstRecession
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hNoCommonFirst
  have h3713 :=
    corollary37_1_3_origin_relativeInterior_yields_minimax
      K hKclosed hKproper hQ.primalGlobal (Or.inr hSecondDual)
  exact h3713.2 ⟨hFirstDual, hSecondDual⟩

/-- Theorem 37.3: either recession-direction condition from Corollary 37.2.1 implies existence
of the saddle-value of `K`, and if both hold then this common value is finite. -/
theorem section37_theorem37_3
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K) :
    let C : Set (Fin m → ℝ) := effectiveDomain₁ K
    let D : Set (Fin n → ℝ) := effectiveDomain₂ K
    ((∀ w : Fin n → ℝ, w ≠ 0 →
        ∃ u : {u // u ∈ intrinsicInterior ℝ C}, ¬ IsRecessionDirection (K u.1) w) ∨
      (∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ D},
          ¬ IsRecessionDirection (fun u => -K u v.1) z)) →
      minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
        maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ∧
        (((∀ w : Fin n → ℝ, w ≠ 0 →
            ∃ u : {u // u ∈ intrinsicInterior ℝ C}, ¬ IsRecessionDirection (K u.1) w) ∧
          (∀ z : Fin m → ℝ, z ≠ 0 →
            ∃ v : {v // v ∈ intrinsicInterior ℝ D},
              ¬ IsRecessionDirection (fun u => -K u v.1) z)) →
          minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊤ : EReal) ∧
            minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊥ : EReal)) := by
  dsimp
  intro hNoCommon
  rcases hNoCommon with hNoCommonSecond | hNoCommonFirst
  · have hSecondDual :
        (0 : Fin n → ℝ) ∈ intrinsicInterior ℝ
          (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) :=
      helperForTheorem_37_3_origin_mem_intrinsicInterior_secondDual_of_noCommonSecondRecession
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hNoCommonSecond
    have h3713 :=
      corollary37_1_3_origin_relativeInterior_yields_minimax
        K hKclosed hKproper hQ.primalGlobal (Or.inr hSecondDual)
    refine ⟨h3713.1, ?_⟩
    intro hBoth
    exact
      helperForTheorem_37_3_finiteSaddleValue_of_bothNoCommonRecessionConditions
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hBoth.1 hBoth.2
  · have hFirstDual :
        (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ
          (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) :=
      helperForTheorem_37_3_origin_mem_intrinsicInterior_firstDual_of_noCommonFirstRecession
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hNoCommonFirst
    have h3713 :=
      corollary37_1_3_origin_relativeInterior_yields_minimax
        K hKclosed hKproper hQ.primalGlobal (Or.inl hFirstDual)
    refine ⟨h3713.1, ?_⟩
    intro hBoth
    exact
      helperForTheorem_37_3_finiteSaddleValue_of_bothNoCommonRecessionConditions
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hBoth.1 hBoth.2

end Section37
end Chap07
