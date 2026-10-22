/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part6

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

section Chap08
section Section39

namespace ConvexProcess

/-- Helper for Theorem 39.3: the local upper closure is the negative of the lower closure of the
negated function. -/
lemma helperForTheorem_39_3_eRealUpperClosure_eq_neg_eRealLowerClosure_neg {k : ℕ}
    (f : (Fin k → ℝ) → EReal) :
    eRealUpperClosure f = fun x => -eRealLowerClosure (fun x => -f x) x := by
  let flipHeight : ((Fin k → ℝ) × ℝ) ≃ₜ ((Fin k → ℝ) × ℝ) :=
    { toEquiv :=
        { toFun := fun p => (p.1, -p.2)
          invFun := fun p => (p.1, -p.2)
          left_inv := by
            intro p
            ext <;> simp
          right_inv := by
            intro p
            ext <;> simp }
      continuous_toFun := by
        change Continuous fun p : (Fin k → ℝ) × ℝ => (p.1, -p.2)
        continuity
      continuous_invFun := by
        change Continuous fun p : (Fin k → ℝ) × ℝ => (p.1, -p.2)
        continuity }
  have hHypographPreimage :
      eRealHypograph f = flipHeight ⁻¹' eRealEpigraph (fun x => -f x) := by
    -- Step 1: the hypograph of `f` is the preimage of the epigraph of `-f` under height negation.
    ext p
    constructor
    · intro hp
      change ((p.2 : EReal) ≤ f p.1) at hp
      change (-f p.1) ≤ ((-p.2 : ℝ) : EReal)
      exact EReal.neg_le_neg_iff.mpr hp
    · intro hp
      change (-f p.1) ≤ ((-p.2 : ℝ) : EReal) at hp
      change ((p.2 : EReal) ≤ f p.1)
      exact EReal.neg_le_neg_iff.mp hp
  have hClosurePreimage :
      closure (eRealHypograph f) = flipHeight ⁻¹' closure (eRealEpigraph (fun x => -f x)) := by
    -- Step 2: the height-flip homeomorphism transports closures of these graph sets exactly.
    calc
      closure (eRealHypograph f) =
          closure (flipHeight ⁻¹' eRealEpigraph (fun x => -f x)) := by
            rw [hHypographPreimage]
      _ = flipHeight ⁻¹' closure (eRealEpigraph (fun x => -f x)) := by
            simpa using
              (Homeomorph.preimage_closure
                (h := flipHeight)
                (s := eRealEpigraph (fun x => -f x))).symm
  funext x
  let T : Set EReal :=
    ((fun r : ℝ => (r : EReal)) '' {r : ℝ | (x, r) ∈ closure (eRealEpigraph (fun x => -f x))})
  have hSetEq :
      ((fun r : ℝ => (r : EReal)) '' {r : ℝ | (x, r) ∈ closure (eRealHypograph f)}) =
        Neg.neg '' T := by
    -- Step 3: fiberwise, the real heights in the closed hypograph are exactly the negatives of
    -- the real heights in the closed epigraph of `-f`.
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨(((-r : ℝ) : EReal)), ?_, ?_⟩
      · refine ⟨-r, ?_, rfl⟩
        rw [hClosurePreimage] at hr
        simpa [flipHeight] using hr
      · simp
    · rintro ⟨w, hw, rfl⟩
      rcases hw with ⟨r, hr, rfl⟩
      refine ⟨-r, ?_, ?_⟩
      · rw [hClosurePreimage]
        change flipHeight (x, -r) ∈ closure (eRealEpigraph fun x => -f x)
        simpa [flipHeight] using hr
      · simp
  -- Step 4: transport the fiber infimum through the `EReal` negation order isomorphism.
  have hNegSInf : -sInf T = sSup (Neg.neg '' T) := by
    change EReal.negOrderIso (sInf T) = sInf (EReal.negOrderIso '' T)
    simpa using (OrderIso.map_sInf EReal.negOrderIso T)
  calc
    eRealUpperClosure f x =
        sSup ((fun r : ℝ => (r : EReal)) '' {r : ℝ | (x, r) ∈ closure (eRealHypograph f)}) := by
          rfl
    _ =
        sSup (Neg.neg '' T) := by
          rw [hSetEq]
    _ =
        -sInf T := by
          exact hNegSInf.symm
    _ = -eRealLowerClosure (fun x => -f x) x := by
          rfl

/-- Helper for Theorem 39.3: the Section 33 one-variable concave closure is exactly the local
upper closure used in this file. -/
lemma helperForTheorem_39_3_concaveClosure_eq_eRealUpperClosure {k : ℕ}
    (g : (Fin k → ℝ) → EReal) :
    functionConcaveClosure g = eRealUpperClosure g := by
  -- Step 1: both Section 33 and the local hypograph closure use the same sign-flip recipe.
  calc
    functionConcaveClosure g = fun x => -functionConvexClosure (fun x => -g x) x := by
      exact helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg
    _ = fun x => -eRealLowerClosure (fun x => -g x) x := by
      funext x
      rw [helperForTheorem_39_3_functionConvexClosure_eq_eRealLowerClosure (f := fun x => -g x)]
    _ = eRealUpperClosure g := by
      symm
      exact helperForTheorem_39_3_eRealUpperClosure_eq_neg_eRealLowerClosure_neg (f := g)

/-- Helper for Theorem 39.3: the Section 33 coordinatewise closure operators should match the
local oriented closure notation used in this file. -/
lemma helperForTheorem_39_3_coordinatewiseClosure_eq_eRealClosureOriented {k : ℕ}
    (o : ConvexSetOrientation) (f : (Fin k → ℝ) → EReal) :
    (match o with
      | .supremum => functionConvexClosure f
      | .infimum => functionConcaveClosure f) =
      eRealClosureOriented o f := by
  -- Route correction: Theorem 39.3 is stated with the local epigraph/hypograph closures
  -- `eRealClosureOriented`, while the imported Section 33 theorems produce the raw
  -- coordinatewise closures `functionConvexClosure` / `functionConcaveClosure`.
  -- TODO: prove that these two closure formalisms agree on `Fin k → ℝ` by comparing the
  -- neighborhood formulas with the epigraph/hypograph closure definitions.
  cases o
  · -- Step 1: the supremum-oriented closure is exactly the lower epigraph closure.
    simpa [eRealClosureOriented] using
      helperForTheorem_39_3_functionConvexClosure_eq_eRealLowerClosure (f := f)
  · -- Step 2: reuse the corrected one-variable closure bridge on the infimum branch.
    simpa [eRealClosureOriented] using
      helperForTheorem_39_3_concaveClosure_eq_eRealUpperClosure (g := f)

/-- Helper for Theorem 39.3: once the raw convex closure of a parameter section hits `⊥` at one
point, convexity forces that raw closure to be identically `⊥`. -/
lemma helperForTheorem_39_3_functionConvexClosure_eq_bot_of_rawBotPoint {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {x0 : Fin n → ℝ}
    (hRawConv :
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (functionConvexClosure f))
    (hx0Bot : functionConvexClosure f x0 = (⊥ : EReal)) :
    functionConvexClosure f = fun _ => (⊥ : EReal) := by
  -- Step 1: classify the raw closure values into the improper alternatives `⊤` or `⊥`.
  have hRawConvFun : ConvexFunction (functionConvexClosure f) :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hRawConv
  have hRawConv' :
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ))
        (fun z =>
          ⨆ ε : {r : ℝ // 0 < r},
            ⨅ w : {w : Fin n → ℝ // ‖w - z‖ < ε.1}, f w.1) := by
    simpa [functionConvexClosure] using hRawConv
  have hRawLsc : LowerSemicontinuous (functionConvexClosure f) := by
    simpa [functionConvexClosure] using
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := f)
  have hTopOrBot :
      ∀ y, functionConvexClosure f y = (⊤ : EReal) ∨
        functionConvexClosure f y = (⊥ : EReal) :=
    helperForLemma33_0_5_closedImproperConvex_values_top_or_bot
      (g := functionConvexClosure f) hRawConvFun hRawLsc ⟨x0, hx0Bot⟩
  -- Step 2: rule out `⊤` by transporting a top neighborhood to a mixed `(⊥, ⊤)` contradiction.
  have hNoTop : ∀ y, functionConvexClosure f y ≠ (⊤ : EReal) := by
    intro y hyTop
    rcases
        helperForLemma33_0_5_functionConvexClosure_top_has_topNeighborhood
          (f := f) (y := y) hTopOrBot hyTop with
      ⟨δ, hδTop⟩
    let δ' : {r : ℝ // 0 < r} := ⟨min δ.1 1, lt_min_iff.mpr ⟨δ.2, by norm_num⟩⟩
    let a : ℝ := δ'.1 / (2 * (‖x0 - y‖ + 1))
    let b : ℝ := 1 - a
    let z : Fin n → ℝ := a • x0 + b • y
    have hPosA : 0 < a := by
      dsimp [a]
      exact div_pos δ'.2 (by positivity)
    have hA_mul_plus_one : a * (‖x0 - y‖ + 1) = δ'.1 / 2 := by
      dsimp [a]
      field_simp [show (‖x0 - y‖ + 1 : ℝ) ≠ 0 by positivity]
    have hA_le_half : a ≤ (1 / 2 : ℝ) := by
      have hPlusOne_ge_one : 1 ≤ ‖x0 - y‖ + 1 := by
        nlinarith [norm_nonneg (x0 - y)]
      have hDeltaLeOne : δ'.1 ≤ 1 := by
        exact min_le_right _ _
      nlinarith [hA_mul_plus_one, hPlusOne_ge_one, hDeltaLeOne]
    have hPosB : 0 < b := by
      dsimp [b]
      nlinarith
    have hzRewrite : z - y = a • (x0 - y) := by
      ext i
      dsimp [z, b]
      ring
    have hA_mul_norm_le : a * ‖x0 - y‖ ≤ δ'.1 / 2 := by
      have hNormLe : ‖x0 - y‖ ≤ ‖x0 - y‖ + 1 := by
        nlinarith [norm_nonneg (x0 - y)]
      have hMulLe :
          a * ‖x0 - y‖ ≤ a * (‖x0 - y‖ + 1) := by
        exact mul_le_mul_of_nonneg_left hNormLe hPosA.le
      simpa [hA_mul_plus_one] using hMulLe
    have hzBall' : ‖z - y‖ < δ'.1 := by
      have hHalfLt : δ'.1 / 2 < δ'.1 := by
        nlinarith [δ'.2]
      calc
        ‖z - y‖ = ‖a • (x0 - y)‖ := by rw [hzRewrite]
        _ = |a| * ‖x0 - y‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = a * ‖x0 - y‖ := by simp [abs_of_nonneg hPosA.le]
        _ ≤ δ'.1 / 2 := hA_mul_norm_le
        _ < δ'.1 := hHalfLt
    have hzBall : ‖z - y‖ < δ.1 := by
      exact lt_of_lt_of_le hzBall' (min_le_left _ _)
    have hzTop : functionConvexClosure f z = (⊤ : EReal) := by
      exact hδTop ⟨z, hzBall⟩
    have hzBot : functionConvexClosure f z = (⊥ : EReal) := by
      have hCollapse :
          (⨆ ε : {r : ℝ // 0 < r},
            ⨅ w : {w : Fin n → ℝ // ‖w - (a • x0 + b • y)‖ < ε.1}, f w.1) = (⊥ : EReal) :=
        helperForLemma33_0_5_functionConvexClosure_mixedBotTop_collapse_from_rawClassification
          (f := f) (x := x0) (y := y) hRawConv' hPosA.le hPosB.le
          (by dsimp [b]; linarith) hPosA hPosB hx0Bot hyTop
      simpa [functionConvexClosure, z] using hCollapse
    rw [hzTop] at hzBot
    simp at hzBot
  -- Step 3: the `⊤/⊥` classification now leaves `⊥` as the only possible value.
  funext y
  rcases hTopOrBot y with hyTop | hyBot
  · exact False.elim (hNoTop y hyTop)
  · exact hyBot

/-- The finite-support qualification under which the oriented adjoint bracket has the canonical
Section 33 interpretation.  It rules out exactly the endpoint cases where raw neighborhood
closure and biconjugate closure need not agree. -/
structure Section39Theorem39_3Qualification : Prop where
  parameterFinite : ∀ {m n : ℕ} (o : ConvexSetOrientation) (A : ConvexProcess m n)
    (xStar : Fin n → ℝ) (u : Fin m → ℝ),
    match o with
    | .supremum =>
        setBracketVec o (A.toSetValued u) xStar ≠ (⊤ : EReal)
    | .infimum =>
        setBracketVec o (A.toSetValued u) xStar ≠ (⊥ : EReal)

/-- Helper for Theorem 39.3: the actual adjoint-fiber bracket is obtained directly as the
appropriate closure of the primal parameter section, without routing through the obsolete
Section 33 pairing bridge. -/
lemma helperForTheorem_39_3_parameterClosure_eq_adjointBracket_direct {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n)
    (hQualification : Section39Theorem39_3Qualification)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    setBracketVec o.opposite ((adjointVecOriented o A).toSetValued xStar) u =
      eRealClosureOriented o.opposite (fun u' => setBracketVec o (A.toSetValued u') xStar) u := by
  -- Step 1: prove the two orientations separately, because the supremum branch is controlled by
  -- the concave biconjugate while the infimum branch needs the convex raw closure.
  cases o
  · let q : (Fin m → ℝ) → EReal :=
      fun u' =>
        setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar
    have hActual :
        setBracketVec ConvexSetOrientation.infimum
            ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar) u =
          concaveConjugate (concaveConjugate q) u := by
      simpa [q] using
        helperForTheorem_39_3_actualAdjointBracket_eq_parameterBiconjugate
          ConvexSetOrientation.supremum A u xStar
    have hRock : IsRockafellarConvexBifunction (ConvexProcess.indicatorBifunction A) :=
      (indicatorBifunction_rockafellarPackage A).1
    have hNoBot : HasNoBotValuesBifunction (ConvexProcess.indicatorBifunction A) :=
      (indicatorBifunction_rockafellarPackage A).2.1
    rcases
        (convexBifunction_pairing_correspondence (m := m) (n := n)).1
          (ConvexProcess.indicatorBifunction A) hRock hNoBot with
      ⟨hConcConv, _, _⟩
    have hPairConc :
        IsERealConcaveOn (Set.univ : Set (Fin m → ℝ))
          (fun u' =>
            convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u' xStar) :=
      hConcConv.1 xStar (by simp)
    have hBracketEq :
        q =
          (fun u' =>
            convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u' xStar) := by
      funext u'
      simpa [q] using
        helperForTheorem_39_3_bracket_eq_orientedPairing
          ConvexSetOrientation.supremum A u' xStar
    have hConcQ :
        IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) q := by
      rw [hBracketEq]
      exact hPairConc
    by_cases hTopPoint : ∃ u0 : Fin m → ℝ, q u0 = (⊤ : EReal)
    · rcases hTopPoint with ⟨u0, hu0Top⟩
      exact False.elim
        (hQualification.parameterFinite ConvexSetOrientation.supremum A xStar u0
          (by simpa [q] using hu0Top))
    · have hNoTop : ∀ u' : Fin m → ℝ, q u' ≠ (⊤ : EReal) := by
        exact not_exists.mp hTopPoint
      have hNegNoBot : ∀ u' : Fin m → ℝ, (fun z => -q z) u' ≠ (⊥ : EReal) := by
        intro u'
        simpa using hNoTop u'
      have hConcQFun : ConcaveFunction q :=
        helperForTheorem_39_3_isConcaveEReal_to_ConcaveFunction
          (f := q) (hConc := helperForTheorem_39_3_isERealConcaveOn_univ_to_IsConcaveEReal hConcQ)
      have hConcClosureEq :
          concaveClosure q u = functionConcaveClosure q u := by
        calc
          concaveClosure q u = -convexClosure (fun z => -q z) u := by
            simpa using congrFun (concaveClosure_eq_neg_convexClosure_neg (g := q)) u
          _ = -functionConvexClosure (fun z => -q z) u := by
            congr 1
            symm
            simpa [convexClosure] using
              congrFun
                (helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
                  (f := fun z => -q z) hNegNoBot)
                u
          _ = functionConcaveClosure q u := by
            symm
            simpa using
              congrFun
                (helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg
                  (g := q))
                u
      -- Step 2: once the support section avoids `⊤`, Chapter 6 and Section 33 closures coincide
      -- after the standard sign-flip rewrite.
      calc
        setBracketVec ConvexSetOrientation.infimum
            ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar) u =
            concaveConjugate (concaveConjugate q) u := hActual
        _ = concaveClosure q u := by
              simpa using
                congrFun
                  (concaveConjugate_biconjugate_eq_concaveClosure (g := q) hConcQFun)
                  u
        _ = functionConcaveClosure q u := hConcClosureEq
        _ = eRealUpperClosure q u := by
              simpa using
                congrFun (helperForTheorem_39_3_concaveClosure_eq_eRealUpperClosure (g := q)) u
        _ = eRealClosureOriented ConvexSetOrientation.infimum q u := by
              rfl
  · let q : (Fin m → ℝ) → EReal :=
      fun u' =>
        setBracketVec ConvexSetOrientation.infimum (A.toSetValued u') xStar
    have hActual :
        setBracketVec ConvexSetOrientation.supremum
            ((adjointVecOriented ConvexSetOrientation.infimum A).toSetValued xStar) u =
          convexConjugate (convexConjugate q) u := by
      simpa [q] using
        helperForTheorem_39_3_actualAdjointBracket_eq_parameterBiconjugate
          ConvexSetOrientation.infimum A u xStar
    have hRock : IsRockafellarConcaveBifunction (ConvexProcess.negIndicatorBifunction A) :=
      (helperForTheorem_39_3_indicator_infimum_package A).1 (by
        intro u' xStar'
        have hBracketEq :=
          helperForTheorem_39_3_bracket_eq_orientedPairing
            ConvexSetOrientation.supremum A u' xStar'
        intro hTop
        apply hQualification.parameterFinite ConvexSetOrientation.supremum A xStar' u'
        calc
          setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar' =
              convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u' xStar' := by
                simpa using hBracketEq
          _ = ⊤ := hTop)
    have hNoTop : HasNoTopValuesBifunction (ConvexProcess.negIndicatorBifunction A) :=
      (helperForTheorem_39_3_indicator_infimum_package A).2.1
    rcases
        (concaveBifunction_pairing_correspondence (m := m) (n := n)).1
          (ConvexProcess.negIndicatorBifunction A) hRock hNoTop with
      ⟨hConvConc, _, _⟩
    have hPairConv :
        IsERealConvexOn (Set.univ : Set (Fin m → ℝ))
          (fun u' =>
            concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u' xStar) :=
      hConvConc.1 xStar (by simp)
    have hBracketEq :
        q =
          (fun u' =>
            concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u' xStar) := by
      funext u'
      simpa [q] using
        helperForTheorem_39_3_bracket_eq_orientedPairing
          ConvexSetOrientation.infimum A u' xStar
    have hConvQ : IsERealConvexOn (Set.univ : Set (Fin m → ℝ)) q := by
      rw [hBracketEq]
      exact hPairConv
    by_cases hBotPoint : ∃ u0 : Fin m → ℝ, q u0 = (⊥ : EReal)
    · rcases hBotPoint with ⟨u0, hu0Bot⟩
      exact False.elim
        (hQualification.parameterFinite ConvexSetOrientation.infimum A xStar u0
          (by simpa [q] using hu0Bot))
    · have hNoBot : ∀ u' : Fin m → ℝ, q u' ≠ (⊥ : EReal) := by
        exact not_exists.mp hBotPoint
      calc
        setBracketVec ConvexSetOrientation.supremum
            ((adjointVecOriented ConvexSetOrientation.infimum A).toSetValued xStar) u =
            convexConjugate (convexConjugate q) u := hActual
        _ = functionConvexClosure q u := by
              exact
                helperForTheorem33_1_biconjugate_eq_functionConvexClosure_of_convex
                  (f := q) hConvQ hNoBot u
        _ = eRealLowerClosure q u := by
              simpa using
                congrFun (helperForTheorem_39_3_functionConvexClosure_eq_eRealLowerClosure
                  (f := q)) u
        _ = eRealClosureOriented ConvexSetOrientation.supremum q u := by
              rfl

/-- The indicator of the graph cone of a convex process is jointly graph-convex. -/
lemma helperForTheorem_39_3_indicatorBifunction_graphConvex {m n : ℕ}
    (A : ConvexProcess m n) :
    IsGraphConvexBifunction (ConvexProcess.indicatorBifunction A) := by
  let graphSet : Set (Fin (m + n) → ℝ) :=
    {z | (fun j => z (Fin.natAdd m j)) ∈ A.toSetValued (fun i => z (Fin.castAdd n i))}
  have hGraphSetConvex : Convex ℝ graphSet := by
    have hGraphConv : Convex ℝ (setValuedGraph A.toSetValued) :=
      (helperForProposition_39_0_1_graphConvexCone_ofConvexProcess A).convex
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    have hz₁' :
        ((fun i => z₁ (Fin.castAdd n i)), (fun j => z₁ (Fin.natAdd m j))) ∈
          setValuedGraph A.toSetValued := by
      simpa [graphSet, setValuedGraph] using hz₁
    have hz₂' :
        ((fun i => z₂ (Fin.castAdd n i)), (fun j => z₂ (Fin.natAdd m j))) ∈
          setValuedGraph A.toSetValued := by
      simpa [graphSet, setValuedGraph] using hz₂
    have hCombo :
        a • ((fun i => z₁ (Fin.castAdd n i)), (fun j => z₁ (Fin.natAdd m j))) +
            b • ((fun i => z₂ (Fin.castAdd n i)), (fun j => z₂ (Fin.natAdd m j))) ∈
          setValuedGraph A.toSetValued :=
      hGraphConv hz₁' hz₂' ha hb hab
    simpa [graphSet, setValuedGraph, Pi.add_apply, Pi.smul_apply] using hCombo
  have hIndicatorConvex : ConvexFunction (indicatorFunction graphSet) :=
    convexFunction_indicator_of_convex (C := graphSet) hGraphSetConvex
  have hIndicatorNoBot :
      ∀ z : Fin (m + n) → ℝ, indicatorFunction graphSet z ≠ (⊥ : EReal) := by
    intro z
    by_cases hz : z ∈ graphSet <;> simp [indicatorFunction, hz]
  have hGraphIndicatorConvex :
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
        (indicatorFunction graphSet) :=
    helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
      (f := indicatorFunction graphSet) hIndicatorConvex hIndicatorNoBot
  have hGraphEq :
      graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A) =
        indicatorFunction graphSet := by
    funext z
    by_cases hz : z ∈ graphSet
    · have hz' :
          (fun j => z (Fin.natAdd m j)) ∈
            A.toSetValued (fun i => z (Fin.castAdd n i)) := by
        simpa [graphSet] using hz
      simp [graphFunctionOfBifunction, ConvexProcess.indicatorBifunction, indicatorEReal,
        indicatorFunction, graphSet, hz, hz']
    · have hz' :
          (fun j => z (Fin.natAdd m j)) ∉
            A.toSetValued (fun i => z (Fin.castAdd n i)) := by
        simpa [graphSet] using hz
      simp [graphFunctionOfBifunction, ConvexProcess.indicatorBifunction, indicatorEReal,
        indicatorFunction, graphSet, hz, hz']
  simpa [IsGraphConvexBifunction, hGraphEq] using hGraphIndicatorConvex

/-- Negating the graph indicator gives the jointly graph-concave negative indicator. -/
lemma helperForTheorem_39_3_negIndicatorBifunction_graphConcave {m n : ℕ}
    (A : ConvexProcess m n) :
    IsGraphConcaveBifunction (ConvexProcess.negIndicatorBifunction A) := by
  have hConc := helperForLemma33_0_5_convexNegation_isConcave
    (helperForTheorem_39_3_indicatorBifunction_graphConvex A)
  have hEq :
      graphFunctionOfBifunction (ConvexProcess.negIndicatorBifunction A) =
        fun z => -graphFunctionOfBifunction (ConvexProcess.indicatorBifunction A) z := by
    funext z
    by_cases hz :
        (fun j => z (Fin.natAdd m j)) ∈
          A.toSetValued (fun i => z (Fin.castAdd n i))
    · simp [graphFunctionOfBifunction, ConvexProcess.negIndicatorBifunction,
        ConvexProcess.indicatorBifunction, negIndicatorEReal, indicatorEReal, hz]
    · simp [graphFunctionOfBifunction, ConvexProcess.negIndicatorBifunction,
        ConvexProcess.indicatorBifunction, negIndicatorEReal, indicatorEReal, hz]
  simpa [IsGraphConcaveBifunction, hEq] using hConc

/-- Helper for Theorem 39.3: the old Section 33 adjoint-pairing bridge is reconstructed from the
actual adjoint-fiber bracket and the direct closure identity just proved. -/
lemma helperForTheorem_39_3_adjointBracket_eq_orientedAdjointPairing {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n)
    (hQualification : Section39Theorem39_3Qualification)
    (xStar : Fin n → ℝ) (u : Fin m → ℝ) :
    setBracketVec o.opposite ((adjointVecOriented o A).toSetValued xStar) u =
      match o with
      | .supremum =>
          convexBifunctionCanonicalAdjointPairing
            (ConvexProcess.indicatorBifunction A) xStar u
      | .infimum =>
          concaveBifunctionCanonicalAdjointPairing
            (ConvexProcess.negIndicatorBifunction A) xStar u := by
  -- Route correction: the earlier raw `iInf`/`iSup` comparison is unnecessary. Once the actual
  -- adjoint-fiber bracket and the Section 33 adjoint pairing are both rewritten as the same
  -- one-variable closure of the same primal parameter section, the bridge is immediate.
  cases o
  · change
      setBracketVec ConvexSetOrientation.infimum
          ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar) u =
        convexBifunctionCanonicalAdjointPairing
          (ConvexProcess.indicatorBifunction A) xStar u
    have hDirect :
        setBracketVec ConvexSetOrientation.infimum
            ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar) u =
          eRealClosureOriented ConvexSetOrientation.infimum
            (fun u' =>
              setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar) u := by
      simpa using
        helperForTheorem_39_3_parameterClosure_eq_adjointBracket_direct
          ConvexSetOrientation.supremum A hQualification u xStar
    have hGraph : IsGraphConvexBifunction (ConvexProcess.indicatorBifunction A) :=
      helperForTheorem_39_3_indicatorBifunction_graphConvex A
    have hNoBot : HasNoBotValuesBifunction (ConvexProcess.indicatorBifunction A) :=
      (indicatorBifunction_rockafellarPackage A).2.1
    rcases
        (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).1
          (ConvexProcess.indicatorBifunction A) ⟨hGraph, hNoBot⟩ with
      ⟨hFirst, _⟩
    have hClosureEq :
        functionConcaveClosure
            (fun u' =>
              setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar) =
          eRealClosureOriented ConvexSetOrientation.infimum
            (fun u' =>
              setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar) :=
      helperForTheorem_39_3_coordinatewiseClosure_eq_eRealClosureOriented
        ConvexSetOrientation.infimum
        (fun u' =>
          setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar)
    have hBracketEq :
        (fun u' =>
          setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar) =
          fun u' =>
            convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u' xStar := by
      funext u'
      simpa using
        helperForTheorem_39_3_bracket_eq_orientedPairing
          ConvexSetOrientation.supremum A u' xStar
    calc
      setBracketVec ConvexSetOrientation.infimum
          ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar) u =
          eRealClosureOriented ConvexSetOrientation.infimum
            (fun u' =>
              setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar) u := hDirect
      _ =
          functionConcaveClosure
            (fun u' =>
              setBracketVec ConvexSetOrientation.supremum (A.toSetValued u') xStar) u := by
              exact (congrFun hClosureEq u).symm
      _ =
          functionConcaveClosure
            (fun u' =>
              convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u' xStar) u := by
              rw [hBracketEq]
      _ =
          concaveClosure
            (fun u' =>
              convexBifunctionPairing (ConvexProcess.indicatorBifunction A) u' xStar) u := by
              exact congrFun
                (helperForTheorem33_2_functionConcaveClosure_eq_concaveClosure_of_concave
                  (helperForTheorem33_2_convexPairingSection_concaveFunction hGraph xStar)
                  (by
                    intro u'
                    have hBracket :
                        setBracketVec ConvexSetOrientation.supremum
                            (A.toSetValued u') xStar =
                          convexBifunctionPairing
                            (ConvexProcess.indicatorBifunction A) u' xStar := by
                      simpa using
                      helperForTheorem_39_3_bracket_eq_orientedPairing
                        ConvexSetOrientation.supremum A u' xStar
                    rw [← hBracket]
                    exact
                      hQualification.parameterFinite ConvexSetOrientation.supremum
                        A xStar u')) u
      _ =
          convexBifunctionCanonicalAdjointPairing
            (ConvexProcess.indicatorBifunction A) xStar u := by
              exact (hFirst xStar u).symm
  · change
      setBracketVec ConvexSetOrientation.supremum
          ((adjointVecOriented ConvexSetOrientation.infimum A).toSetValued xStar) u =
        concaveBifunctionCanonicalAdjointPairing
          (ConvexProcess.negIndicatorBifunction A) xStar u
    have hDirect :
        setBracketVec ConvexSetOrientation.supremum
            ((adjointVecOriented ConvexSetOrientation.infimum A).toSetValued xStar) u =
          eRealClosureOriented ConvexSetOrientation.supremum
            (fun u' =>
              setBracketVec ConvexSetOrientation.infimum (A.toSetValued u') xStar) u := by
      simpa using
        helperForTheorem_39_3_parameterClosure_eq_adjointBracket_direct
          ConvexSetOrientation.infimum A hQualification u xStar
    have hGraph : IsGraphConcaveBifunction (ConvexProcess.negIndicatorBifunction A) :=
      helperForTheorem_39_3_negIndicatorBifunction_graphConcave A
    have hNoTop : HasNoTopValuesBifunction (ConvexProcess.negIndicatorBifunction A) :=
      (helperForTheorem_39_3_indicator_infimum_package A).2.1
    rcases
        (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).2
          (ConvexProcess.negIndicatorBifunction A) ⟨hGraph, hNoTop⟩ with
      ⟨hFirst, _⟩
    have hClosureEq :
        functionConvexClosure
            (fun u' =>
              setBracketVec ConvexSetOrientation.infimum (A.toSetValued u') xStar) =
          eRealClosureOriented ConvexSetOrientation.supremum
            (fun u' =>
              setBracketVec ConvexSetOrientation.infimum (A.toSetValued u') xStar) :=
      helperForTheorem_39_3_coordinatewiseClosure_eq_eRealClosureOriented
        ConvexSetOrientation.supremum
        (fun u' =>
          setBracketVec ConvexSetOrientation.infimum (A.toSetValued u') xStar)
    have hBracketEq :
        (fun u' =>
          setBracketVec ConvexSetOrientation.infimum (A.toSetValued u') xStar) =
          fun u' =>
            concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u' xStar := by
      funext u'
      simpa using
        helperForTheorem_39_3_bracket_eq_orientedPairing
          ConvexSetOrientation.infimum A u' xStar
    calc
      setBracketVec ConvexSetOrientation.supremum
          ((adjointVecOriented ConvexSetOrientation.infimum A).toSetValued xStar) u =
          eRealClosureOriented ConvexSetOrientation.supremum
            (fun u' =>
              setBracketVec ConvexSetOrientation.infimum (A.toSetValued u') xStar) u := hDirect
      _ =
          functionConvexClosure
            (fun u' =>
              setBracketVec ConvexSetOrientation.infimum (A.toSetValued u') xStar) u := by
              exact (congrFun hClosureEq u).symm
      _ =
          functionConvexClosure
            (fun u' =>
              concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u' xStar) u := by
              rw [hBracketEq]
      _ =
          convexFunctionClosure
            (fun u' =>
              concaveBifunctionPairing (ConvexProcess.negIndicatorBifunction A) u' xStar) u := by
              exact congrFun
                (helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
                  (by
                    intro u'
                    have hBracket :
                        setBracketVec ConvexSetOrientation.infimum
                            (A.toSetValued u') xStar =
                          concaveBifunctionPairing
                            (ConvexProcess.negIndicatorBifunction A) u' xStar := by
                      simpa using
                      helperForTheorem_39_3_bracket_eq_orientedPairing
                        ConvexSetOrientation.infimum A u' xStar
                    rw [← hBracket]
                    exact
                      hQualification.parameterFinite ConvexSetOrientation.infimum
                        A xStar u')) u
      _ =
          concaveBifunctionCanonicalAdjointPairing
            (ConvexProcess.negIndicatorBifunction A) xStar u := by
              exact (hFirst xStar u).symm

/-- Helper for Theorem 39.3: a supremum-oriented bracket is finite exactly when the underlying
fiber is nonempty. -/
lemma helperForTheorem_39_3_supremumBracket_ne_bot_iff_nonempty {m : ℕ}
    (S : Set (Fin m → ℝ)) (u : Fin m → ℝ) :
    setBracketVec ConvexSetOrientation.supremum S u ≠ ⊥ ↔ S.Nonempty := by
  constructor
  · intro hBracket
    -- Step 1: if the fiber were empty, the bracket would be the empty supremum.
    by_contra hEmpty
    have hSEmpty : S = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hEmpty
    have hEq : setBracketVec ConvexSetOrientation.supremum S u = ⊥ := by
      unfold setBracketVec
      simp [hSEmpty]
    exact hBracket hEq
  · rintro ⟨x, hx⟩ hBot
    -- Step 2: any witness in the fiber contributes a finite lower bound to the supremum bracket.
    have hLe :
        (((finDot x u : ℝ) : EReal)) ≤
          setBracketVec ConvexSetOrientation.supremum S u := by
      unfold setBracketVec
      exact le_sSup ⟨x, hx, rfl⟩
    have : (((finDot x u : ℝ) : EReal)) ≤ (⊥ : EReal) := by
      simpa [hBot] using hLe
    simpa using this

/-- Helper for Theorem 39.3: in the closed infimum-oriented branch, `xStar ∈ ri (dom A*)`
can be handled by applying the already-proved supremum `ri (dom)` equality to the adjoint
process `A*` and then rewriting `A** = A`. -/
lemma helperForTheorem_39_3_infimum_closed_eq_on_ri_domAstar_via_adjointProcess {m n : ℕ}
    (A : ConvexProcess m n) (hAClosed : A.IsClosed)
    (hQualification : Section39Theorem39_3Qualification)
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ ri (setValuedDom (adjointVecOriented ConvexSetOrientation.infimum A).toSetValued))
    (u : Fin m → ℝ) :
    setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar =
      setBracketVec ConvexSetOrientation.supremum
        ((adjointVecOriented ConvexSetOrientation.infimum A).toSetValued xStar) u := by
  let B : OrientedSetValuedMap (Fin n → ℝ) (Fin m → ℝ) :=
    adjointVecOriented ConvexSetOrientation.infimum A
  rcases
      adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint
        ConvexSetOrientation.infimum A with
    ⟨hBConvex, _hBClosed, _hBOrient, hDoubleAdjoint, _hBIndicator⟩
  let Bcp : ConvexProcess n m :=
    { toSetValued := B.toSetValued
      map_add_superset := hBConvex.1
      map_smul_pos := hBConvex.2.1
      zero_mem := hBConvex.2.2 }
  have hxStarDom : xStar ∈ intrinsicInterior ℝ Bcp.dom := by
    change xStar ∈
      intrinsicInterior ℝ
        (setValuedDom (adjointVecOriented ConvexSetOrientation.infimum A).toSetValued)
    exact hxStar
  have hPairEq :
      convexBifunctionPairing (ConvexProcess.indicatorBifunction Bcp) xStar u =
        convexBifunctionCanonicalAdjointPairing
          (ConvexProcess.indicatorBifunction Bcp) u xStar := by
    have hGraph : IsGraphConvexBifunction (ConvexProcess.indicatorBifunction Bcp) :=
      helperForTheorem_39_3_indicatorBifunction_graphConvex Bcp
    have hNoBot : HasNoBotValuesBifunction (ConvexProcess.indicatorBifunction Bcp) :=
      (indicatorBifunction_rockafellarPackage Bcp).2.1
    exact
      ((adjoint_pairing_eq_on_relativeInterior_domains (m := n) (n := m)).1
        (F := ConvexProcess.indicatorBifunction Bcp) ⟨hGraph, hNoBot⟩).1
        (by
          rw [helperForTheorem_39_3_indicator_parameterDomain_eq_dom Bcp]
          exact hxStarDom) u
  have hClosedToSetValued :
      (A.cl).toSetValued = A.toSetValued :=
    congrArg ConvexProcess.toSetValued hAClosed
  have hDoubleFiber :
      ((adjointVecOriented ConvexSetOrientation.supremum Bcp).toSetValued u) = A.toSetValued u := by
    -- Step 1: identify the double adjoint of `A` with the adjoint of the adjoint process `B`.
    calc
      ((adjointVecOriented ConvexSetOrientation.supremum Bcp).toSetValued u) =
          doubleAdjointVecSetValuedOriented ConvexSetOrientation.infimum A u := by
            rfl
      _ = (A.cl).toSetValued u := by
            exact congrFun hDoubleAdjoint u
      _ = A.toSetValued u := by
            exact congrFun hClosedToSetValued u
  -- Step 2: rewrite the supremum pairing identity for `B` back into the bracket notation of
  -- `A` and `A*`.
  calc
    setBracketVec ConvexSetOrientation.infimum (A.toSetValued u) xStar =
        setBracketVec ConvexSetOrientation.infimum
          ((adjointVecOriented ConvexSetOrientation.supremum Bcp).toSetValued u) xStar := by
            rw [hDoubleFiber]
    _ =
        convexBifunctionCanonicalAdjointPairing
          (ConvexProcess.indicatorBifunction Bcp) u xStar := by
          simpa [B, Bcp] using
            helperForTheorem_39_3_adjointBracket_eq_orientedAdjointPairing
              ConvexSetOrientation.supremum Bcp hQualification u xStar
    _ =
        convexBifunctionPairing (ConvexProcess.indicatorBifunction Bcp) xStar u := by
          exact hPairEq.symm
    _ =
        setBracketVec ConvexSetOrientation.supremum (B.toSetValued xStar) u := by
          simpa [B, Bcp] using
            (helperForTheorem_39_3_bracket_eq_orientedPairing
              ConvexSetOrientation.supremum Bcp xStar u).symm

-- Proof sketch: Use Theorem 39.2 to identify the adjoint and double adjoint with polarity/bipolar
-- operations on the graph cone. The bracket is a (oriented) support function of fibers, hence
-- positively homogeneous; convexity/concavity comes from taking `sup`/`inf` of affine functions.
-- The closure identities are partial conjugacy statements (Theorems 33.1, 33.2 and Corollary
-- 33.2.1 in the book) applied to the oriented indicator bifunction of the graph; the `ri`-equality
-- is the standard “no-closure-needed on relative interior of the domain” principle.

end ConvexProcess
end Section39
end Chap08
