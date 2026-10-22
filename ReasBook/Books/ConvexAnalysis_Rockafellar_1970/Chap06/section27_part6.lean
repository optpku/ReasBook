/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part5

section Chap06
section Section27

-- Proof sketch: minimize the restricted problem by replacing it with the unconstrained function
-- `h + δ_C`. The first part applies the no-common-recession hypothesis to rule out recession
-- directions of the sum; the polyhedral part uses the weaker constancy hypothesis for common
-- recession directions when `C` is polyhedral, then invokes the corresponding unconstrained
-- attainment theorem.
/-- Theorem 6.27.4: let `h` be a closed proper convex function, and let `C` be a nonempty closed
convex set. If `h` and `C` have no common recession direction, then `h` attains its infimum on
`C`. If moreover `C` is polyhedral, then it is enough to assume that every common recession
direction of `h` and `C` is a direction of constancy of `h`. -/
theorem attainsInfimumOn_closedConvexSet_of_commonRecessionHypotheses
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C) :
    (HasNoCommonRecessionDirections h C → AttainsInfimumOn h C) ∧
      (IsPolyhedralConvexSet n C →
        CommonRecessionDirectionsAreDirectionsOfConstancy h C →
        AttainsInfimumOn h C) := by
  classical
  by_cases hallTop : ∀ x : Fin n → ℝ, x ∈ C → h x = (⊤ : EReal)
  · constructor
    · intro _hNoCommon
      -- If `h` is everywhere `⊤` on `C`, the constrained infimum is trivially attained.
      exact
        helperForTheorem_6_27_4_trivial_attainment_of_all_top_on_C
          (h := h) (C := C) hCne hallTop
    · intro _hCpoly _hConstCommon
      -- The same degenerate argument works in the polyhedral branch as well.
      exact
        helperForTheorem_6_27_4_trivial_attainment_of_all_top_on_C
          (h := h) (C := C) hCne hallTop
  · have hnotbot : ∀ x : Fin n → ℝ, h x ≠ (⊥ : EReal) := by
      intro x
      exact hproper.2.2 x (by simp)
    have hfinitePoint : ∃ x0 : Fin n → ℝ, x0 ∈ C ∧ h x0 < (⊤ : EReal) := by
      by_contra hNoFinite
      push_neg at hNoFinite
      apply hallTop
      intro x hxC
      by_contra hxneTop
      exact (not_le_of_gt (lt_top_iff_ne_top.mpr hxneTop)) (hNoFinite x hxC)
    rcases hfinitePoint with ⟨x0, hx0C, hx0Top⟩
    rcases closedProperConvexFunction_minimum_characterizations h hclosed hproper with
      ⟨_hA, _hB, _hC, _hD, _hE, hF, _hG, _hH, _hI⟩
    rcases hF with ⟨_hSublevelEq, hFrest⟩
    rcases hFrest with ⟨_hMinBridge, hFrest'⟩
    rcases hFrest' with ⟨hSublevelRec, _hPolar⟩
    let familyOfLevels : (ℕ → ℝ) → Option ℕ → Set (Fin n → ℝ) :=
      fun β i =>
        match i with
        | none => C
        | some k => sublevelSetEReal h (β k)
    have hSubClosed : ∀ α : ℝ, IsClosed (sublevelSetEReal h α) := by
      intro α
      exact (lowerSemicontinuous_iff_closed_sublevel (f := h)).1 hclosed.2 α
    have hSubConvex : ∀ α : ℝ, Convex ℝ (sublevelSetEReal h α) := by
      intro α
      simpa [sublevelSetEReal] using
        (convexFunction_level_sets_convex (f := h) hclosed.1 (α := (α : EReal))).2
    have hSublevelRecDir :
        ∀ α : ℝ, (sublevelSetEReal h α).Nonempty →
          ∀ {d : Fin n → ℝ},
            d ∈ Set.recessionCone (sublevelSetEReal h α) → IsRecessionDirection h d := by
      intro α hα d hd
      have hdE : d ∈ recessionConeEReal (F := Fin n → ℝ) h := by
        rw [hSublevelRec α hα] at hd
        exact hd
      simpa [recessionConeEReal, IsRecessionDirection, recessionFunctionEReal,
        recessionFunction, erealDom, effectiveDomain_eq] using hdE
    have hRecDirSublevel :
        ∀ α : ℝ, (sublevelSetEReal h α).Nonempty →
          ∀ {d : Fin n → ℝ},
            IsRecessionDirection h d → d ∈ Set.recessionCone (sublevelSetEReal h α) := by
      intro α hα d hd
      have hdE : d ∈ recessionConeEReal (F := Fin n → ℝ) h := by
        simpa [recessionConeEReal, IsRecessionDirection, recessionFunctionEReal,
          recessionFunction, erealDom, effectiveDomain_eq] using hd
      rw [hSublevelRec α hα]
      exact hdE
    have hConstToLineality :
        ∀ α : ℝ, (sublevelSetEReal h α).Nonempty →
          ∀ {d : Fin n → ℝ},
            IsDirectionOfConstancy h d →
              d ∈ (-Set.recessionCone (sublevelSetEReal h α)) ∩
                Set.recessionCone (sublevelSetEReal h α) := by
      intro α hα d hconst
      have hdRec : IsRecessionDirection h d := by
        simpa [IsRecessionDirection, hconst.1]
      have hdPos :
          d ∈ Set.recessionCone (sublevelSetEReal h α) :=
        hRecDirSublevel α hα hdRec
      have hdNegRec : IsRecessionDirection h (-d) := by
        simpa [IsRecessionDirection, hconst.2]
      have hdNeg :
          -d ∈ Set.recessionCone (sublevelSetEReal h α) :=
        hRecDirSublevel α hα hdNegRec
      exact ⟨by simpa [Set.mem_neg] using hdNeg, hdPos⟩
    have hFamilyNonempty :
        ∀ β : ℕ → ℝ,
          (∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∧ h x ≤ (β k : EReal)) →
            ∀ i : Option ℕ, (familyOfLevels β i).Nonempty := by
      intro β hβpts i
      cases i with
      | none =>
          simpa [familyOfLevels] using hCne
      | some k =>
          rcases hβpts k with ⟨x, hxC, hxLe⟩
          exact ⟨x, by simpa [familyOfLevels, sublevelSetEReal] using hxLe⟩
    have hFamilyClosed : ∀ β : ℕ → ℝ, ∀ i : Option ℕ, IsClosed (familyOfLevels β i) := by
      intro β i
      cases i with
      | none =>
          simpa [familyOfLevels] using hCclosed
      | some k =>
          simpa [familyOfLevels] using hSubClosed (β k)
    have hFamilyConvex : ∀ β : ℕ → ℝ, ∀ i : Option ℕ, Convex ℝ (familyOfLevels β i) := by
      intro β i
      cases i with
      | none =>
          simpa [familyOfLevels] using hCconvex
      | some k =>
          simpa [familyOfLevels] using hSubConvex (β k)
    have hFiniteIntersectionForFamily :
        ∀ β : ℕ → ℝ,
          (∀ {k l : ℕ}, k ≤ l → (β l : EReal) ≤ (β k : EReal)) →
            (∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∧ h x ≤ (β k : EReal)) →
              ∀ s : Finset (Option ℕ), s.card ≤ n + 1 →
                ∃ x : Fin n → ℝ, ∀ i ∈ s, x ∈ familyOfLevels β i := by
      intro β hβmono hβpts s _hs
      let γ : Option ℕ → ℕ := fun i =>
        match i with
        | none => 0
        | some k => k + 1
      let K : ℕ := s.sup γ
      by_cases hK : K = 0
      · rcases hCne with ⟨x, hxC⟩
        refine ⟨x, ?_⟩
        intro i hi
        cases i with
        | none =>
            simpa [familyOfLevels] using hxC
        | some k =>
            have hkLe : k + 1 ≤ K := by
              simpa [γ, K] using (Finset.le_sup hi : γ (some k) ≤ s.sup γ)
            exact False.elim (by omega)
      · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
        let kMax : ℕ := K - 1
        rcases hβpts kMax with ⟨x, hxC, hxLeMax⟩
        refine ⟨x, ?_⟩
        intro i hi
        cases i with
        | none =>
            simpa [familyOfLevels] using hxC
        | some k =>
            have hkSuccLe : k + 1 ≤ K := by
              simpa [γ, K] using (Finset.le_sup hi : γ (some k) ≤ s.sup γ)
            have hkLeMax : k ≤ kMax := by
              dsimp [kMax]
              exact Nat.le_pred_of_lt (Nat.succ_le_iff.mp hkSuccLe)
            have hxLek : h x ≤ (β k : EReal) :=
              le_trans hxLeMax (hβmono hkLeMax)
            simpa [familyOfLevels, sublevelSetEReal] using hxLek
    have hNoCommonForFamily :
        ∀ β : ℕ → ℝ,
          (∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∧ h x ≤ (β k : EReal)) →
            HasNoCommonRecessionDirections h C →
              ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧
                ∀ i : Option ℕ, d ∈ Set.recessionCone (familyOfLevels β i) := by
      intro β hβpts hNoCommon hBad
      rcases hBad with ⟨d, hdne, hdAll⟩
      have hdC : d ∈ Set.recessionCone C := by
        simpa [familyOfLevels] using hdAll none
      rcases hβpts 0 with ⟨x1, hx1C, hx1Le⟩
      have hβ0ne : (sublevelSetEReal h (β 0)).Nonempty := ⟨x1, by
        simpa [sublevelSetEReal] using hx1Le⟩
      have hdSub : d ∈ Set.recessionCone (sublevelSetEReal h (β 0)) := by
        simpa [familyOfLevels] using hdAll (some 0)
      have hdRec : IsRecessionDirection h d :=
        hSublevelRecDir (β 0) hβ0ne hdSub
      exact hdne (hNoCommon d hdRec hdC)
    have hWeakRecessionForFamily :
        ∀ β : ℕ → ℝ,
          (∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∧ h x ≤ (β k : EReal)) →
            IsPolyhedralConvexSet n C →
              CommonRecessionDirectionsAreDirectionsOfConstancy h C →
              HasHellyWeakRecessionHypothesis (n := n) (familyOfLevels β) := by
      intro β hβpts hCpoly hConstCommon
      refine ⟨({none} : Finset (Option ℕ)), ?_, ?_⟩
      · intro i hi
        cases i with
        | none =>
            simpa [familyOfLevels] using hCpoly
        | some k =>
            simp at hi
      · intro d hdAll i hi
        cases i with
        | none =>
            simp at hi
        | some k =>
            have hdC : d ∈ Set.recessionCone C := by
              simpa [familyOfLevels] using hdAll none
            rcases hβpts 0 with ⟨x1, hx1C, hx1Le⟩
            have hβ0ne : (sublevelSetEReal h (β 0)).Nonempty := ⟨x1, by
              simpa [sublevelSetEReal] using hx1Le⟩
            have hdSub0 : d ∈ Set.recessionCone (sublevelSetEReal h (β 0)) := by
              simpa [familyOfLevels] using hdAll (some 0)
            have hdRec : IsRecessionDirection h d :=
              hSublevelRecDir (β 0) hβ0ne hdSub0
            have hConst : IsDirectionOfConstancy h d :=
              hConstCommon d hdRec hdC
            rcases hβpts k with ⟨xk, hxkC, hxkLe⟩
            have hβkne : (sublevelSetEReal h (β k)).Nonempty := ⟨xk, by
              simpa [sublevelSetEReal] using hxkLe⟩
            simpa [familyOfLevels] using
              hConstToLineality (β k) hβkne hConst
    constructor
    · intro hNoCommon
      have hBelowEveryLevel_of_not_lower :
          (¬ ∃ m : ℝ, ∀ x : Fin n → ℝ, x ∈ C → (m : EReal) ≤ h x) →
            ∀ m : ℝ, ∃ x : Fin n → ℝ, x ∈ C ∧ h x < (m : EReal) := by
        intro hNoLower m
        by_contra hNoPoint
        push_neg at hNoPoint
        exact hNoLower ⟨m, by
          intro x hxC
          exact hNoPoint x hxC⟩
      have hLowerBound : ∃ m : ℝ, ∀ x : Fin n → ℝ, x ∈ C → (m : EReal) ≤ h x := by
        by_contra hNoLower
        have hBelowEveryLevel := hBelowEveryLevel_of_not_lower hNoLower
        let βLower : ℕ → ℝ := fun k => -(k : ℝ)
        have hβLowerMono :
            ∀ {k l : ℕ}, k ≤ l → (βLower l : EReal) ≤ (βLower k : EReal) := by
          intro k l hkl
          simpa [βLower] using
            (show ((-(l : ℝ)) : EReal) ≤ ((-(k : ℝ)) : EReal) by
              exact_mod_cast
                (neg_le_neg (show (k : ℝ) ≤ l by exact_mod_cast hkl)))
        have hβLowerPts :
            ∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∧ h x ≤ (βLower k : EReal) := by
          intro k
          rcases hBelowEveryLevel (βLower k) with ⟨x, hxC, hxLt⟩
          exact ⟨x, hxC, le_of_lt hxLt⟩
        obtain ⟨xBad, hxBadAll⟩ :=
          corollary21_3_2_helly_theorem
            (C := familyOfLevels βLower)
            (hCnonempty := hFamilyNonempty βLower hβLowerPts)
            (hCclosed := hFamilyClosed βLower)
            (hCconvex := hFamilyConvex βLower)
            (hNoCommonRecession := hNoCommonForFamily βLower hβLowerPts hNoCommon)
            (hFiniteIntersectionNonempty :=
              hFiniteIntersectionForFamily βLower hβLowerMono hβLowerPts)
        have hxBadLeZero : h xBad ≤ (0 : EReal) := by
          simpa [familyOfLevels, βLower, sublevelSetEReal] using hxBadAll (some 0)
        have hxBadTop : h xBad ≠ (⊤ : EReal) := by
          intro hxTop
          have : (⊤ : EReal) ≤ (0 : EReal) := by
            simpa [hxTop] using hxBadLeZero
          exact (not_top_le_coe 0) this
        have hxBadBot : h xBad ≠ (⊥ : EReal) := hnotbot xBad
        let a : ℝ := (h xBad).toReal
        let k : ℕ := Nat.ceil (-a) + 1
        have hkNot : ¬ h xBad ≤ ((-(k : ℝ)) : EReal) := by
          have hacoe : (((a : ℝ) : EReal)) = h xBad := by
            simpa [a] using EReal.coe_toReal (x := h xBad) hxBadTop hxBadBot
          have hkReal : -a < (k : ℝ) := by
            have : -a < ((Nat.ceil (-a) : ℕ) + 1 : ℕ) := by
              have hceil : -a ≤ Nat.ceil (-a) := Nat.le_ceil (-a)
              have : -a < (Nat.ceil (-a) : ℝ) + 1 := by
                linarith
              exact_mod_cast this
            simpa [k] using this
          have hkReal' : (-(k : ℝ)) < a := by
            linarith
          have hkLt : ((-(k : ℝ)) : EReal) < h xBad := by
            rw [← hacoe]
            exact_mod_cast hkReal'
          exact not_le_of_gt hkLt
        have hxBadAtK : h xBad ≤ (βLower k : EReal) := by
          simpa [familyOfLevels, sublevelSetEReal] using hxBadAll (some k)
        exact hkNot (by simpa [βLower] using hxBadAtK)
      let infC : EReal := ⨅ y : C, h y
      have hInfFinite : IsFiniteEReal infC := by
        constructor
        · have hUpper : infC ≤ h x0 := by
            simpa [infC] using (iInf_le (fun y : C => h y) ⟨x0, hx0C⟩)
          exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hUpper hx0Top)
        · rcases hLowerBound with ⟨m, hm⟩
          have hLower : (m : EReal) ≤ infC := by
            refine le_iInf ?_
            intro y
            exact hm y y.property
          exact ne_of_gt (lt_of_lt_of_le (by simp) hLower)
      let βApprox : ℕ → ℝ := fun k => infC.toReal + 1 / (k + 1 : ℝ)
      have hβApproxMono :
          ∀ {k l : ℕ}, k ≤ l → (βApprox l : EReal) ≤ (βApprox k : EReal) := by
        intro k l hkl
        have hkpos : (0 : ℝ) < k + 1 := by positivity
        have hkle : (k + 1 : ℝ) ≤ l + 1 := by
          exact_mod_cast Nat.succ_le_succ hkl
        have hdiv : 1 / (l + 1 : ℝ) ≤ 1 / (k + 1 : ℝ) := by
          exact one_div_le_one_div_of_le hkpos hkle
        exact_mod_cast (show βApprox l ≤ βApprox k by
          dsimp [βApprox]
          linarith)
      have hβApproxPts :
          ∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∧ h x ≤ (βApprox k : EReal) := by
        intro k
        refine
          helperForTheorem_6_27_4_exists_point_of_restrictedInf_lt_level
            (h := h) (C := C) (βApprox k) ?_
        have hInfCoe : (((infC.toReal : ℝ)) : EReal) = infC := by
          simpa [infC] using EReal.coe_toReal (x := infC) hInfFinite.1 hInfFinite.2
        have hRealLt : infC.toReal < βApprox k := by
          dsimp [βApprox]
          have hpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
          linarith
        have hERealLt : (((infC.toReal : ℝ)) : EReal) < (βApprox k : EReal) := by
          exact_mod_cast hRealLt
        calc
          infC = (((infC.toReal : ℝ)) : EReal) := hInfCoe.symm
          _ < (βApprox k : EReal) := hERealLt
      obtain ⟨xBar, hxBarAll⟩ :=
        corollary21_3_2_helly_theorem
          (C := familyOfLevels βApprox)
          (hCnonempty := hFamilyNonempty βApprox hβApproxPts)
          (hCclosed := hFamilyClosed βApprox)
          (hCconvex := hFamilyConvex βApprox)
          (hNoCommonRecession := hNoCommonForFamily βApprox hβApproxPts hNoCommon)
          (hFiniteIntersectionNonempty :=
            hFiniteIntersectionForFamily βApprox hβApproxMono hβApproxPts)
      have hxBarC : xBar ∈ C := by
        simpa [familyOfLevels] using hxBarAll none
      have hxBarApprox :
          ∀ k : ℕ, h xBar ≤ (βApprox k : EReal) := by
        intro k
        simpa [familyOfLevels, sublevelSetEReal] using hxBarAll (some k)
      have hxBarEq :
          h xBar = infC :=
        helperForTheorem_6_27_4_eq_restrictedInf_of_mem_all_approximateSublevels
          (h := h) (C := C) xBar hxBarC hInfFinite hxBarApprox (hnotbot xBar)
      exact ⟨⟨xBar, hxBarC⟩, by simpa [infC] using hxBarEq⟩
    · intro hCpoly hConstCommon
      have hBelowEveryLevel_of_not_lower :
          (¬ ∃ m : ℝ, ∀ x : Fin n → ℝ, x ∈ C → (m : EReal) ≤ h x) →
            ∀ m : ℝ, ∃ x : Fin n → ℝ, x ∈ C ∧ h x < (m : EReal) := by
        intro hNoLower m
        by_contra hNoPoint
        push_neg at hNoPoint
        exact hNoLower ⟨m, by
          intro x hxC
          exact hNoPoint x hxC⟩
      have hLowerBound : ∃ m : ℝ, ∀ x : Fin n → ℝ, x ∈ C → (m : EReal) ≤ h x := by
        by_contra hNoLower
        have hBelowEveryLevel := hBelowEveryLevel_of_not_lower hNoLower
        let βLower : ℕ → ℝ := fun k => -(k : ℝ)
        have hβLowerMono :
            ∀ {k l : ℕ}, k ≤ l → (βLower l : EReal) ≤ (βLower k : EReal) := by
          intro k l hkl
          simpa [βLower] using
            (show ((-(l : ℝ)) : EReal) ≤ ((-(k : ℝ)) : EReal) by
              exact_mod_cast
                (neg_le_neg (show (k : ℝ) ≤ l by exact_mod_cast hkl)))
        have hβLowerPts :
            ∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∧ h x ≤ (βLower k : EReal) := by
          intro k
          rcases hBelowEveryLevel (βLower k) with ⟨x, hxC, hxLt⟩
          exact ⟨x, hxC, le_of_lt hxLt⟩
        obtain ⟨xBad, hxBadAll⟩ :=
          theorem21_5_helly_theorem_under_weaker_recession_hypothesis
            (C := familyOfLevels βLower)
            (hCnonempty := hFamilyNonempty βLower hβLowerPts)
            (hCclosed := hFamilyClosed βLower)
            (hCconvex := hFamilyConvex βLower)
            (hWeakerRecession := hWeakRecessionForFamily βLower hβLowerPts hCpoly hConstCommon)
            (hFiniteIntersectionNonempty :=
              hFiniteIntersectionForFamily βLower hβLowerMono hβLowerPts)
        have hxBadLeZero : h xBad ≤ (0 : EReal) := by
          simpa [familyOfLevels, βLower, sublevelSetEReal] using hxBadAll (some 0)
        have hxBadTop : h xBad ≠ (⊤ : EReal) := by
          intro hxTop
          have : (⊤ : EReal) ≤ (0 : EReal) := by
            simpa [hxTop] using hxBadLeZero
          exact (not_top_le_coe 0) this
        have hxBadBot : h xBad ≠ (⊥ : EReal) := hnotbot xBad
        let a : ℝ := (h xBad).toReal
        let k : ℕ := Nat.ceil (-a) + 1
        have hkNot : ¬ h xBad ≤ ((-(k : ℝ)) : EReal) := by
          have hacoe : (((a : ℝ) : EReal)) = h xBad := by
            simpa [a] using EReal.coe_toReal (x := h xBad) hxBadTop hxBadBot
          have hkReal : -a < (k : ℝ) := by
            have : -a < ((Nat.ceil (-a) : ℕ) + 1 : ℕ) := by
              have hceil : -a ≤ Nat.ceil (-a) := Nat.le_ceil (-a)
              have : -a < (Nat.ceil (-a) : ℝ) + 1 := by
                linarith
              exact_mod_cast this
            simpa [k] using this
          have hkReal' : (-(k : ℝ)) < a := by
            linarith
          have hkLt : ((-(k : ℝ)) : EReal) < h xBad := by
            rw [← hacoe]
            exact_mod_cast hkReal'
          exact not_le_of_gt hkLt
        have hxBadAtK : h xBad ≤ (βLower k : EReal) := by
          simpa [familyOfLevels, sublevelSetEReal] using hxBadAll (some k)
        exact hkNot (by simpa [βLower] using hxBadAtK)
      let infC : EReal := ⨅ y : C, h y
      have hInfFinite : IsFiniteEReal infC := by
        constructor
        · have hUpper : infC ≤ h x0 := by
            simpa [infC] using (iInf_le (fun y : C => h y) ⟨x0, hx0C⟩)
          exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hUpper hx0Top)
        · rcases hLowerBound with ⟨m, hm⟩
          have hLower : (m : EReal) ≤ infC := by
            refine le_iInf ?_
            intro y
            exact hm y y.property
          exact ne_of_gt (lt_of_lt_of_le (by simp) hLower)
      let βApprox : ℕ → ℝ := fun k => infC.toReal + 1 / (k + 1 : ℝ)
      have hβApproxMono :
          ∀ {k l : ℕ}, k ≤ l → (βApprox l : EReal) ≤ (βApprox k : EReal) := by
        intro k l hkl
        have hkpos : (0 : ℝ) < k + 1 := by positivity
        have hkle : (k + 1 : ℝ) ≤ l + 1 := by
          exact_mod_cast Nat.succ_le_succ hkl
        have hdiv : 1 / (l + 1 : ℝ) ≤ 1 / (k + 1 : ℝ) := by
          exact one_div_le_one_div_of_le hkpos hkle
        exact_mod_cast (show βApprox l ≤ βApprox k by
          dsimp [βApprox]
          linarith)
      have hβApproxPts :
          ∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∧ h x ≤ (βApprox k : EReal) := by
        intro k
        refine
          helperForTheorem_6_27_4_exists_point_of_restrictedInf_lt_level
            (h := h) (C := C) (βApprox k) ?_
        have hInfCoe : (((infC.toReal : ℝ)) : EReal) = infC := by
          simpa [infC] using EReal.coe_toReal (x := infC) hInfFinite.1 hInfFinite.2
        have hRealLt : infC.toReal < βApprox k := by
          dsimp [βApprox]
          have hpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
          linarith
        have hERealLt : (((infC.toReal : ℝ)) : EReal) < (βApprox k : EReal) := by
          exact_mod_cast hRealLt
        calc
          infC = (((infC.toReal : ℝ)) : EReal) := hInfCoe.symm
          _ < (βApprox k : EReal) := hERealLt
      obtain ⟨xBar, hxBarAll⟩ :=
        theorem21_5_helly_theorem_under_weaker_recession_hypothesis
          (C := familyOfLevels βApprox)
          (hCnonempty := hFamilyNonempty βApprox hβApproxPts)
          (hCclosed := hFamilyClosed βApprox)
          (hCconvex := hFamilyConvex βApprox)
          (hWeakerRecession := hWeakRecessionForFamily βApprox hβApproxPts hCpoly hConstCommon)
          (hFiniteIntersectionNonempty :=
            hFiniteIntersectionForFamily βApprox hβApproxMono hβApproxPts)
      have hxBarC : xBar ∈ C := by
        simpa [familyOfLevels] using hxBarAll none
      have hxBarApprox :
          ∀ k : ℕ, h xBar ≤ (βApprox k : EReal) := by
        intro k
        simpa [familyOfLevels, sublevelSetEReal] using hxBarAll (some k)
      have hxBarEq :
          h xBar = infC :=
        helperForTheorem_6_27_4_eq_restrictedInf_of_mem_all_approximateSublevels
          (h := h) (C := C) xBar hxBarC hInfFinite hxBarApprox (hnotbot xBar)
      exact ⟨⟨xBar, hxBarC⟩, by simpa [infC] using hxBarEq⟩

/-- A point `x` is a minimizer of `h` relative to `C` when `x ∈ C` and `h x` realizes the
infimum of the restriction of `h` to `C`. -/
def IsRelativeMinimizerOn {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : Prop :=
  x ∈ C ∧ h x = ⨅ y : C, h y

/-- Definition 6.27.10 (Auxiliary set associated with a constrained minimum): for a nonempty set
`C ⊆ ℝ^n` and an `EReal`-valued function `h`, let `α = inf_{x ∈ C} h x`. The auxiliary set
`C₂` is the subset of `ℝ^(n+1)`, modeled as `(Fin n → ℝ) × ℝ`, consisting of pairs `(x, μ)`
with `x ∈ C` and `μ ≤ α`. The Lean definition below keeps the same set formula for arbitrary
`C`, and in the textbook setup it is intended to be used with `Set.Nonempty C`. -/
def constrainedMinimumAuxiliarySet {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (C : Set (Fin n → ℝ)) : Set ((Fin n → ℝ) × ℝ) :=
  {p | p.1 ∈ C ∧ (p.2 : EReal) ≤ ⨅ x : C, h x}

/-- Definition 6.27.11 (Non-vertical hyperplane): a subset of `ℝ^(n+1)`, modeled as
`(Fin n → ℝ) × ℝ`, is non-vertical when it is the graph of an affine function on `ℝ^n`,
so it has the form `μ = ⟪x, x*⟫ + β`, equivalently `μ = x ⬝ᵥ xStar + β`, for some
`xStar ∈ ℝ^n` and `β ∈ ℝ`. -/
def IsNonverticalHyperplane {n : ℕ} (H : Set ((Fin n → ℝ) × ℝ)) : Prop :=
  ∃ xStar : Fin n → ℝ, ∃ β : ℝ, H = {p | p.2 = p.1 ⬝ᵥ xStar + β}

/-- A constraint qualification for the normal-cone characterization of constrained minimizers:
either `ri (dom h)` meets `ri C`, or `C` is polyhedral and `ri (dom h)` meets `C`. -/
def HasRelativeMinimizerSubgradientQualification {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (C : Set (Fin n → ℝ)) : Prop :=
  Set.Nonempty
      (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) ∩
        euclideanRelativeInterior_fin n C) ∨
    (IsPolyhedralConvexSet n C ∧
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) ∩ C))

/-- Helper for Theorem 6.27.5: a subgradient of `h` balanced by an opposite normal vector of `C`
forces `x` to attain the constrained infimum. -/
lemma helperForTheorem_6_27_5_relativeMinimizer_of_subgradient_and_neg_normal
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    {xStar : Module.Dual ℝ (Fin n → ℝ)}
    (hxSub : xStar ∈ subdifferentialAt h x)
    (hxNormal : -xStar ∈ normalConeAt C x) :
    IsRelativeMinimizerOn h C x := by
  rcases (mem_normalConeAt_iff.1 hxNormal) with ⟨hxC, hxNormalIneq⟩
  refine ⟨hxC, le_antisymm ?_ ?_⟩
  · -- Compare `h x` with every feasible value using the subgradient and normal-cone inequalities.
    refine le_iInf ?_
    intro z
    have hzNormal : xStar (z.1 - x) ≥ 0 := by
      have hnegLe : (-xStar) (z.1 - x) ≤ 0 := hxNormalIneq z.1 z.2
      simpa using neg_nonneg.mpr hnegLe
    have hzSub : h z.1 ≥ h x + (((xStar (z.1 - x) : ℝ) : EReal)) := hxSub z.1
    have hzNormalEReal : ((0 : ℝ) : EReal) ≤ (((xStar (z.1 - x) : ℝ) : EReal)) := by
      exact_mod_cast hzNormal
    have hzStep : h x + (0 : EReal) ≤ h x + (((xStar (z.1 - x) : ℝ) : EReal)) := by
      calc
        h x + (0 : EReal) = (0 : EReal) + h x := by simp
        _ ≤ (((xStar (z.1 - x) : ℝ) : EReal)) + h x := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right hzNormalEReal (h x)
        _ = h x + (((xStar (z.1 - x) : ℝ) : EReal)) := by simp [add_comm]
    calc
      h x = h x + (0 : EReal) := by simp
      _ ≤ h x + (((xStar (z.1 - x) : ℝ) : EReal)) := hzStep
      _ ≤ h z.1 := hzSub
  · -- The restricted infimum is always bounded above by the value at the feasible point `x`.
    exact iInf_le (fun z : C => h z) ⟨x, hxC⟩

/-- Helper for Theorem 6.27.5: the qualification hypotheses provide a feasible point where `h` is
finite. -/
lemma helperForTheorem_6_27_5_exists_feasible_finitePoint_of_qualification
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (hqual : HasRelativeMinimizerSubgradientQualification h C) :
    ∃ z : Fin n → ℝ, z ∈ C ∧ h z < (⊤ : EReal) := by
  rcases hqual with hri | hpoly
  · rcases hri with ⟨z, hz⟩
    refine ⟨z, ?_, ?_⟩
    · exact helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin hz.2
    · have hzDom :
          z ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h :=
        helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin hz.1
      simpa [effectiveDomain_eq] using hzDom
  · rcases hpoly with ⟨_hCpoly, ⟨z, hz⟩⟩
    refine ⟨z, hz.2, ?_⟩
    have hzDom :
        z ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h :=
      helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin hz.1
    simpa [effectiveDomain_eq] using hzDom

/-- Helper for Theorem 6.27.5: the constrained qualification turns into the two-summand
qualification needed for the subdifferential sum rule for `h + δ_C`. -/
lemma helperForTheorem_6_27_5_indicatorExtension_sumQualification
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (hqual : HasRelativeMinimizerSubgradientQualification h C) :
    let fTwo : Fin 2 → (Fin n → ℝ) → EReal :=
      fun i => Fin.cases h (fun _ => indicatorFunction C) i
    let Ipoly : Set (Fin 2) := {i | IsPolyhedralConvexFunction n (fTwo i)}
    SubdifferentialSumQualification fTwo Ipoly := by
  classical
  dsimp
  rcases hqual with hallri | hmixed
  · -- In the relative-interior branch, both summands inherit relative-interior feasibility.
    rcases hallri with ⟨z, hz⟩
    refine Or.inl ?_
    refine ⟨z, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hz.1
    · simpa [effectiveDomain_indicatorFunction_eq] using hz.2
  · -- In the polyhedral branch, the indicator is the polyhedral summand and the original
    -- function keeps the relative-interior witness.
    rcases hmixed with ⟨hCpoly, ⟨z, hz⟩⟩
    have hIndicatorPoly :
        IsPolyhedralConvexFunction n (indicatorFunction C) :=
      helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet hCpoly
    refine Or.inr ?_
    refine ⟨z, ?_, ?_⟩
    · intro i hi
      refine Fin.cases ?_ ?_ i
      · exact helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin hz.1
      · simpa [effectiveDomain_indicatorFunction_eq] using hz.2
    · intro i hi
      fin_cases i
      · simpa using hz.1
      · exfalso
        exact hi (by simpa using hIndicatorPoly)

/-- Helper for Theorem 6.27.5: a constrained minimizer of `h` yields the zero subgradient of the
indicator extension `h + δ_C` at the same point. -/
lemma helperForTheorem_6_27_5_zero_mem_subdifferential_indicatorExtension_of_relativeMinimizer
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ)) (x : Fin n → ℝ)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hmin : IsRelativeMinimizerOn h C x)
    (hfeasible : ∃ z : Fin n → ℝ, z ∈ C ∧ h z < (⊤ : EReal)) :
    let g : (Fin n → ℝ) → EReal := fun y => h y + indicatorFunction C y
    (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt g x := by
  dsimp
  rcases hmin with ⟨hxC, hxMin⟩
  rcases hfeasible with ⟨z0, hz0C, hz0Top⟩
  have _hg0Top : h z0 + indicatorFunction C z0 < (⊤ : EReal) := by
    simpa [indicatorFunction, hz0C] using hz0Top
  have hInfEq :
      functionInfimumEReal (fun y => h y + indicatorFunction C y) = ⨅ y : C, h y := by
    apply le_antisymm
    · -- Every feasible value of `h` is also a value of the indicator extension.
      refine le_iInf ?_
      intro yC
      have hle : functionInfimumEReal (fun y => h y + indicatorFunction C y) ≤
          h yC + indicatorFunction C yC := by
        simpa [functionInfimumEReal] using
          (iInf_le (fun y => h y + indicatorFunction C y) yC)
      simpa [indicatorFunction, yC.property] using hle
    · -- Off `C` the indicator extension equals `⊤`, so only feasible points matter.
      refine le_iInf ?_
      intro z
      by_cases hzC : z ∈ C
      · have hle : (⨅ y : C, h y) ≤ h z := iInf_le (fun y : C => h y) ⟨z, hzC⟩
        simpa [indicatorFunction, hzC] using hle
      · have hle : (⨅ y : C, h y) ≤ (⊤ : EReal) := le_top
        have hzBot : h z ≠ (⊥ : EReal) := hproper.2.2 z (by simp)
        simpa [indicatorFunction, hzC, hzBot] using hle
  have hxMinG : x ∈ minimumSetEReal (fun y => h y + indicatorFunction C y) := by
    -- The minimizer identity for `h` on `C` becomes the global minimizer identity for `h + δ_C`.
    rw [minimumSetEReal]
    calc
      h x + indicatorFunction C x = h x := by simp [indicatorFunction, hxC]
      _ = ⨅ y : C, h y := hxMin
      _ = functionInfimumEReal (fun y => h y + indicatorFunction C y) := hInfEq.symm
  exact
    (helperForTheorem_6_27_1_mem_minimumSet_iff_zero_mem_subdifferentialAt
      (fun y => h y + indicatorFunction C y) x).1 hxMinG

-- Proof sketch: encode the constrained problem by the sum `h + δ_C`. If a subgradient
-- `xStar ∈ ∂h(x)` satisfies `-xStar ∈ N_C(x)`, then `0 ∈ ∂(h + δ_C)(x)`, so `x` minimizes `h`
-- on `C`. Under the stated qualification, the sum rule for subdifferentials gives the converse by
-- decomposing `0 ∈ ∂(h + δ_C)(x)` as `xStar + (-xStar)` with `xStar ∈ ∂h(x)` and
-- `-xStar ∈ N_C(x)`.
/-- Theorem 6.27.5: let `h` be a proper convex function and let `C` be a nonempty convex set.
If there exists `xStar ∈ ∂h(x)` such that `-xStar` is normal to `C` at `x`, then `x` is a point
where the infimum of `h` relative to `C` is attained. This condition is also necessary,
equivalently gives an iff characterization, whenever `ri (dom h)` intersects `ri C`, or whenever
`C` is polyhedral and `ri (dom h)` intersects `C`. -/
theorem relativeMinimizerOn_iff_exists_subgradient_neg_mem_normalCone_under_qualification
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ)) (x : Fin n → ℝ)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCne : Set.Nonempty C) (hCconvex : Convex ℝ C) :
    ((∃ xStar ∈ subdifferentialAt h x, -xStar ∈ normalConeAt C x) →
      IsRelativeMinimizerOn h C x) ∧
      (HasRelativeMinimizerSubgradientQualification h C →
        (IsRelativeMinimizerOn h C x ↔
          ∃ xStar ∈ subdifferentialAt h x, -xStar ∈ normalConeAt C x)) := by
  classical
  constructor
  · intro hxWitness
    rcases hxWitness with ⟨xStar, hxSub, hxNormal⟩
    -- The defining inequalities already show that `h x` is below every feasible value.
    exact
      helperForTheorem_6_27_5_relativeMinimizer_of_subgradient_and_neg_normal
        hxSub hxNormal
  · intro hqual
    constructor
    · intro hmin
      have hfeasible :
          ∃ z : Fin n → ℝ, z ∈ C ∧ h z < (⊤ : EReal) :=
        helperForTheorem_6_27_5_exists_feasible_finitePoint_of_qualification hqual
      let fTwo : Fin 2 → (Fin n → ℝ) → EReal :=
        fun i => Fin.cases h (fun _ => indicatorFunction C) i
      let Ipoly : Set (Fin 2) := {i | IsPolyhedralConvexFunction n (fTwo i)}
      have hqualSum : SubdifferentialSumQualification fTwo Ipoly := by
        exact
          helperForTheorem_6_27_5_indicatorExtension_sumQualification h C hqual
      have hproperTwo : ∀ i : Fin 2, ProperConvexFunctionOn Set.univ (fTwo i) := by
        have hIndicatorProper :
            ProperConvexFunctionOn Set.univ (indicatorFunction C) :=
          properConvexFunctionOn_indicator_of_convex_of_nonempty (C := C) hCconvex hCne
        intro i
        refine Fin.cases hproper
          (fun i : Fin 1 => by
            simpa [fTwo] using hIndicatorProper) i
      have hpoly : ∀ i : Fin 2, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (fTwo i) := by
        intro i
        simp [Ipoly]
      have hzeroSub :
          (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
            subdifferentialAt (fun y => ∑ i, fTwo i y) x := by
        -- Replace constrained minimality with a zero subgradient of `h + δ_C`.
        simpa [fTwo, Fin.sum_univ_two] using
          helperForTheorem_6_27_5_zero_mem_subdifferential_indicatorExtension_of_relativeMinimizer
            h C x hproper hmin hfeasible
      have hdecomp :
          IsSubdifferentialSumDecompositionAt fTwo x
            (0 : Module.Dual ℝ (Fin n → ℝ)) :=
        ((subdifferential_sum_contains_sum_and_eq_under_qualification
            fTwo hproperTwo Ipoly hpoly).2 hqualSum x 0).1 hzeroSub
      rcases hdecomp with ⟨parts, hparts, hsum⟩
      refine ⟨parts 0, ?_, ?_⟩
      · -- The first summand of the decomposition is the required subgradient of `h`.
        simpa [fTwo] using hparts 0
      · -- The second summand is a normal vector for `C`, and the sum identity identifies it with
        -- `-parts 0`.
        have hxC : x ∈ C := hmin.1
        have hpart1Normal : parts 1 ∈ normalConeAt C x := by
          have hpart1Indicator : parts 1 ∈ subdifferentialAt (indicatorFunction C) x := by
            simpa [fTwo] using hparts 1
          rwa [subdifferential_indicatorFunction_eq_normalConeAt_of_mem hxC] at hpart1Indicator
        have hsum01 : (0 : Module.Dual ℝ (Fin n → ℝ)) = parts 0 + parts 1 := by
          simpa [Fin.sum_univ_two] using hsum
        have hpart1Eq : parts 1 = -parts 0 := by
          rw [eq_neg_iff_add_eq_zero]
          simpa [add_comm] using hsum01.symm
        simpa [hpart1Eq] using hpart1Normal
    · intro hxWitness
      rcases hxWitness with ⟨xStar, hxSub, hxNormal⟩
      -- The converse implication inside the iff is the same direct sufficiency argument.
      exact
        helperForTheorem_6_27_5_relativeMinimizer_of_subgradient_and_neg_normal
          hxSub hxNormal

-- Proof sketch: the attained finite minimum gives a point of contact between the epigraph of `h`
-- and the auxiliary set below the minimizing level. Since these sets are closed, convex, disjoint,
-- and one has nonempty interior in the ambient space, a separating-hyperplane theorem yields an
-- affine separator. The contact at the minimizer rules out a vertical separator, so the separating
-- hyperplane can be written in the non-vertical form `μ = x ⬝ᵥ xStar + β`.
/-- Helper for Theorem 6.27.6: the restricted infimum over `C` equals the attained minimum value
`α`. -/
lemma helperForTheorem_6_27_6_restrictedInf_eq_alpha
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    (⨅ x : C, h x) = (α : EReal) := by
  -- Compare the subtype infimum with the attained value at `xBar`.
  apply le_antisymm
  · have hle : (⨅ x : C, h x) ≤ h xBar := by
      exact iInf_le (fun x : C => h x) ⟨xBar, hxBarC⟩
    calc
      ⨅ x : C, h x ≤ h xBar := hle
      _ = (α : EReal) := by simpa using hxBar
  · -- The lower-bound hypothesis already places `α` below every feasible value.
    refine le_iInf ?_
    intro x
    exact hα_lower x x.property

/-- Helper for Theorem 6.27.6: the auxiliary set matches the textbook description
`{(x, μ) | x ∈ C, μ ≤ α}` once the restricted infimum is rewritten as `α`. -/
lemma helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    constrainedMinimumAuxiliarySet h C = {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ p.2 ≤ α} := by
  -- Rewrite the infimum in the definition of `constrainedMinimumAuxiliarySet`.
  ext p
  have hInfEq :
      (⨅ x : C, h x) = (α : EReal) :=
    helperForTheorem_6_27_6_restrictedInf_eq_alpha
      (h := h) (C := C) α hxBarC hα_lower hxBar
  simp [constrainedMinimumAuxiliarySet, hInfEq]

/-- Helper for Theorem 6.27.6: the attained minimizing point `(xBar, α)` lies in the epigraph of
`h`. -/
lemma helperForTheorem_6_27_6_contactPoint_mem_epigraph
    {n : ℕ} {h : (Fin n → ℝ) → EReal} (α : ℝ) {xBar : Fin n → ℝ}
    (hxBar : h xBar = (α : EReal)) :
    (xBar, α) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h := by
  -- The contact point lies exactly on the graph level `μ = h xBar = α`.
  refine (mem_epigraph_univ_iff (f := h)).2 ?_
  simpa [hxBar]

/-- Helper for Theorem 6.27.6: the attained minimizing point `(xBar, α)` also lies in the
auxiliary set. -/
lemma helperForTheorem_6_27_6_contactPoint_mem_auxiliarySet
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    (xBar, α) ∈ constrainedMinimumAuxiliarySet h C := by
  -- After rewriting the auxiliary set into textbook form, membership is immediate.
  have hEq :
      constrainedMinimumAuxiliarySet h C = {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ p.2 ≤ α} :=
    helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
      (h := h) (C := C) α hxBarC hα_lower hxBar
  rw [hEq]
  exact ⟨hxBarC, le_rfl⟩

/-- Helper for Theorem 6.27.6: the auxiliary set is closed, convex, and nonempty. -/
lemma helperForTheorem_6_27_6_auxiliarySet_geometry
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal))
    (hCclosed : IsClosed C) (hCconvex : Convex ℝ C) :
    Convex ℝ (constrainedMinimumAuxiliarySet h C) ∧
      IsClosed (constrainedMinimumAuxiliarySet h C) ∧
      Set.Nonempty (constrainedMinimumAuxiliarySet h C) := by
  have hEq :
      constrainedMinimumAuxiliarySet h C = {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ p.2 ≤ α} :=
    helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
      (h := h) (C := C) α hxBarC hα_lower hxBar
  have hProdEq :
      {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ p.2 ≤ α} = C ×ˢ Set.Iic α := by
    ext p
    simp
  refine ⟨?_, ?_, ?_⟩
  · -- In textbook form, the auxiliary set is a product of convex sets.
    rw [hEq, hProdEq]
    exact hCconvex.prod (convex_Iic α)
  · -- The same product description shows that the auxiliary set is closed.
    rw [hEq, hProdEq]
    exact hCclosed.prod isClosed_Iic
  · -- The minimizing contact point witnesses nonemptiness.
    exact ⟨(xBar, α), helperForTheorem_6_27_6_contactPoint_mem_auxiliarySet
      (h := h) (C := C) α hxBarC hα_lower hxBar⟩

/-- Helper for Theorem 6.27.6: the epigraph is stable under vertical upward translation. -/
lemma helperForTheorem_6_27_6_epigraph_vertical_upward_closed
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {p : (Fin n → ℝ) × ℝ} {s : ℝ}
    (hp : p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h) (hs : 0 ≤ s) :
    (p.1, p.2 + s) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h := by
  -- Raising the last coordinate weakens the defining epigraph inequality.
  refine (mem_epigraph_univ_iff (f := h)).2 ?_
  have hpLe : h p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := h)).1 hp
  have hmono : ((p.2 : ℝ) : EReal) ≤ ((p.2 + s : ℝ) : EReal) := by
    exact_mod_cast (show p.2 ≤ p.2 + s by linarith)
  exact le_trans hpLe hmono

/-- Helper for Theorem 6.27.6: the auxiliary set is stable under vertical downward translation. -/
lemma helperForTheorem_6_27_6_auxiliarySet_vertical_downward_closed
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal))
    {p : (Fin n → ℝ) × ℝ} {s : ℝ}
    (hp : p ∈ constrainedMinimumAuxiliarySet h C) (hs : 0 ≤ s) :
    (p.1, p.2 - s) ∈ constrainedMinimumAuxiliarySet h C := by
  -- Lowering the height coordinate preserves the inequality `μ ≤ α`.
  have hEq :
      constrainedMinimumAuxiliarySet h C = {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ p.2 ≤ α} :=
    helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
      (h := h) (C := C) α hxBarC hα_lower hxBar
  rw [hEq] at hp ⊢
  exact ⟨hp.1, by linarith [hp.2, hs]⟩

/-- Helper for Theorem 6.27.6: every continuous linear functional on `(ℝ^n) × ℝ` splits into a
horizontal dot product plus a last-coordinate term. -/
lemma helperForTheorem_6_27_6_continuousLinearMap_decomposition
    {n : ℕ} (l : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ) :
    ∃ xStar : Fin n → ℝ, ∃ t : ℝ, ∀ p : (Fin n → ℝ) × ℝ,
      l p = p.1 ⬝ᵥ xStar + p.2 * t := by
  let φ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    l.toLinearMap.comp (LinearMap.inl ℝ (Fin n → ℝ) ℝ)
  let t : ℝ := l (0, 1)
  rcases linearMap_exists_dotProduct_representation (φ := φ) with ⟨xStar, hxStar⟩
  refine ⟨xStar, t, ?_⟩
  intro p
  have hpSplit : p = (p.1, (0 : ℝ)) + (0, p.2) := by
    ext <;> simp
  have hpSplit_symm : (p.1, (0 : ℝ)) + (0, p.2) = p := by
    simpa using hpSplit.symm
  have hpVertical : (0, p.2) = p.2 • ((0 : Fin n → ℝ), (1 : ℝ)) := by
    ext <;> simp [smul_eq_mul]
  -- Split the product functional into its horizontal and vertical contributions.
  have hHoriz : l (p.1, (0 : ℝ)) = φ p.1 := by
    simp [φ]
  have hVert : l (0, p.2) = p.2 * t := by
    rw [hpVertical, map_smul]
    simp [t, smul_eq_mul]
  calc
    l p = l ((p.1, (0 : ℝ)) + (0, p.2)) := by rw [hpSplit_symm]
    _ = l (p.1, (0 : ℝ)) + l (0, p.2) := by rw [map_add]
    _ = φ p.1 + p.2 * t := by rw [hHoriz, hVert]
    _ = p.1 ⬝ᵥ xStar + p.2 * t := by simpa [hxStar p.1]

/-- Helper for Theorem 6.27.6: the packed generator set homogenizes upper epigraph points and
lower auxiliary-set points in `Fin (n + 2)` coordinates. -/
noncomputable def helperForTheorem_6_27_6_encodedSeparatorGeneratorSet {n : ℕ}
    (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ)) :
    Set (Fin (n + 2) → ℝ) :=
  {z |
    (∃ p : (Fin n → ℝ) × ℝ,
      p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h ∧
      z =
        prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (p.1, p.2), (1 : ℝ))) ∨
    ∃ q : (Fin n → ℝ) × ℝ,
      q ∈ constrainedMinimumAuxiliarySet h C ∧
      z =
        prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (-q.1, -q.2), (-1 : ℝ))}

/-- Helper for Theorem 6.27.6: the upper epigraph generators remain visible after packing the
cone data into `Fin (n + 2)` coordinates. -/
lemma helperForTheorem_6_27_6_mem_encodedSeparatorGeneratorSet_upper
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    {p : (Fin n → ℝ) × ℝ}
    (hp : p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h) :
    prodLinearEquiv_append_coord (n := n + 1)
        (prodLinearEquiv_append_coord (n := n) (p.1, p.2), (1 : ℝ)) ∈
      helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C := by
  -- Package an epigraph point as an upper generator of the homogenized cone.
  exact Or.inl ⟨p, hp, rfl⟩

/-- Helper for Theorem 6.27.6: the lower auxiliary-set generators remain visible after packing the
cone data into `Fin (n + 2)` coordinates. -/
lemma helperForTheorem_6_27_6_mem_encodedSeparatorGeneratorSet_lower
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    {q : (Fin n → ℝ) × ℝ}
    (hq : q ∈ constrainedMinimumAuxiliarySet h C) :
    prodLinearEquiv_append_coord (n := n + 1)
        (prodLinearEquiv_append_coord (n := n) (-q.1, -q.2), (-1 : ℝ)) ∈
      helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C := by
  -- Package an auxiliary-set point as a lower generator with opposite sign.
  exact Or.inr ⟨q, hq, rfl⟩

/-- Helper for Theorem 6.27.6: in the packed coordinates, the forbidden vector is the negative
vertical direction with zero primal and balance components. -/
noncomputable def helperForTheorem_6_27_6_encodedNegativeVerticalPoint {n : ℕ} :
    Fin (n + 2) → ℝ :=
  prodLinearEquiv_append_coord (n := n + 1)
    (prodLinearEquiv_append_coord (n := n) (0, (-1 : ℝ)), (0 : ℝ))

/-- Helper for Theorem 6.27.6: pack a zero-balance point with horizontal defect `0` and vertical
gap `δ` into `Fin (n + 2)` coordinates. -/
noncomputable def helperForTheorem_6_27_6_encodedZeroBalancePoint {n : ℕ}
    (δ : ℝ) : Fin (n + 2) → ℝ :=
  prodLinearEquiv_append_coord (n := n + 1)
    (prodLinearEquiv_append_coord (n := n) (0, δ), (0 : ℝ))

/-- Helper for Theorem 6.27.6: `Γ z` is the infimum of all vertical gaps `p.2 - q.2` realized by
an epigraph point `p` and an auxiliary point `q` with horizontal defect `p.1 - q.1 = z`. -/
noncomputable def helperForTheorem_6_27_6_zeroBalanceSliceGap {n : ℕ}
    (α : ℝ) (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ)) (z : Fin n → ℝ) : EReal :=
  ⨅ p : {p : (Fin n → ℝ) × ℝ // p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h},
    ⨅ q : {q : (Fin n → ℝ) × ℝ // q ∈ constrainedMinimumAuxiliarySet h C},
      if p.1.1 - q.1.1 = z then (((p.1.2 - q.1.2 : ℝ) : EReal)) else ⊤

/-- Helper for Theorem 6.27.6: on the exact zero-defect slice, every epigraph point lies at or
above every auxiliary point, so the slice-gap infimum is nonnegative. -/
lemma helperForTheorem_6_27_6_zeroBalanceSliceGap_nonnegative_at_zero
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    (0 : EReal) ≤ helperForTheorem_6_27_6_zeroBalanceSliceGap α h C 0 := by
  -- Check each admissible epigraph/auxiliary pair on the zero-defect slice separately.
  refine le_iInf ?_
  intro p
  refine le_iInf ?_
  intro q
  by_cases hz : p.1.1 - q.1.1 = (0 : Fin n → ℝ)
  · -- On the diagonal slice, the primal coordinates coincide, so minimality forces
    -- the auxiliary height below the epigraph height.
    have hAuxEq :
        constrainedMinimumAuxiliarySet h C = {r : (Fin n → ℝ) × ℝ | r.1 ∈ C ∧ r.2 ≤ α} :=
      helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
        (h := h) (C := C) α hxBarC hα_lower hxBar
    have hpEpi : h p.1.1 ≤ (p.1.2 : EReal) := by
      exact (mem_epigraph_univ_iff (f := h)).1 p.2
    have hqAux : q.1.1 ∈ C ∧ q.1.2 ≤ α := by
      have hqAuxMem : q.1 ∈ {r : (Fin n → ℝ) × ℝ | r.1 ∈ C ∧ r.2 ≤ α} := by
        simpa [hAuxEq] using q.2
      exact hqAuxMem
    have hSame : p.1.1 = q.1.1 := sub_eq_zero.mp hz
    have hpLowerAtQ : h q.1.1 ≤ (p.1.2 : EReal) := by
      simpa [hSame] using hpEpi
    have hqLeP_EReal : ((q.1.2 : ℝ) : EReal) ≤ ((p.1.2 : ℝ) : EReal) := by
      calc
        ((q.1.2 : ℝ) : EReal) ≤ ((α : ℝ) : EReal) := by
          exact_mod_cast hqAux.2
        _ ≤ h q.1.1 := hα_lower q.1.1 hqAux.1
        _ ≤ (p.1.2 : EReal) := hpLowerAtQ
    have hqLeP : q.1.2 ≤ p.1.2 := by
      exact_mod_cast hqLeP_EReal
    have hGapNonneg : 0 ≤ p.1.2 - q.1.2 := sub_nonneg.mpr hqLeP
    simpa [hz] using (show (0 : EReal) ≤ (((p.1.2 - q.1.2 : ℝ) : EReal)) by
      exact_mod_cast hGapNonneg)
  · -- Outside the exact slice, this branch contributes `⊤`, which is automatically nonnegative.
    simp [hz]


end Section27
end Chap06
