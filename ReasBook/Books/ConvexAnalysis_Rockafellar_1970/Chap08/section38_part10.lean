/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part12

open scoped Pointwise

section Chap08
section Section38

attribute [local instance] instTopologicalSpace_moduleDual_weak_part3

/-- Helper for Theorem 38.5: every fixed dual pair satisfies the basic weak-duality estimate that
the textbook dual supremum is bounded above by the translated value at `0`. -/
lemma helperForTheorem_38_5_textbookDualSupremum_le_translatedDifferenceValueAtZero
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    fenchelDualSupremum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) ≤
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 := by
  -- Rewrite the already-proved pointwise inequality into the translated-value language.
  calc
    fenchelDualSupremum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) =
      bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        yStar uStar := by
          symm
          exact
            helperForTheorem_38_5_composeSupGeneric_eq_fenchelDualSupremum
              (F := F) (G := G) (yStar := yStar) (uStar := uStar)
    _ ≤ bifunctionAdjoint (bifunctionCompose G F) yStar uStar :=
      helperForTheorem_38_5_composeSupGeneric_le_adjoint_compose F G yStar uStar
    _ =
      fenchelPrimalInfimum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
          exact
            helperForTheorem_38_5_adjoint_compose_eq_fenchelPrimalInfimum
              (F := F) (G := G) (yStar := yStar) (uStar := uStar)
    _ = helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 := by
          symm
          exact
            helperForTheorem_38_5_textbookTranslatedDifferenceValueAtZero_eq_fenchelPrimalInfimum
              (F := F) (G := G) (yStar := yStar) (uStar := uStar)

/-- Helper for Theorem 38.5: the corrected guarded value at `0` matches the original translated
value because both are the same primal infimum. -/
lemma helperForTheorem_38_5_translatedDifferenceValueAtZero_eq_secondShiftGuardedValueAtZero
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 =
      helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0 := by
  -- Both value functions are normalized to the same Fenchel primal infimum at the origin.
  calc
    helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 =
      fenchelPrimalInfimum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
          exact
            helperForTheorem_38_5_textbookTranslatedDifferenceValueAtZero_eq_fenchelPrimalInfimum
              (F := F) (G := G) (yStar := yStar) (uStar := uStar)
    _ = helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0 := by
          symm
          exact
            helperForTheorem_38_5_textbookSecondShiftGuardedValueAtZero_eq_fenchelPrimalInfimum
              (F := F) (G := G) (yStar := yStar) (uStar := uStar)

/-- Helper for Theorem 38.5: every explicit middle dual vector contributes a dual objective value
below the textbook dual supremum. -/
lemma helperForTheorem_38_5_fenchelDualObjective_le_supremum
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (xStarVec : Fin n → ℝ) :
    fenchelDualObjective
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
        xStarVec ≤
      fenchelDualSupremum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
  -- Unfold the supremum and use the canonical bound of an indexed term by the corresponding `iSup`.
  rw [fenchelDualSupremum]
  exact le_iSup (fun zStarVec : Fin n → ℝ =>
    fenchelDualObjective
      (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
      (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
      zStarVec) xStarVec

/-- Helper for Theorem 38.5: a single middle dual vector whose objective value lies between the
translated value at `0` and the dual supremum already yields both the textbook strong-duality
equality and an attainment witness. -/
lemma helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality_of_sandwich
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (zStar : Fin n → ℝ)
    (hP0LeDualObj :
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 ≤
        fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          zStar)
    (hDualLeP0 :
      fenchelDualSupremum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) ≤
        helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0) :
    helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality F G yStar uStar := by
  have hObjLeSup :
      fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          zStar ≤
        fenchelDualSupremum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) :=
    -- Any explicit dual objective contributes one term to the defining supremum.
    helperForTheorem_38_5_fenchelDualObjective_le_supremum
      (F := F) (G := G) (yStar := yStar) (uStar := uStar) (xStarVec := zStar)
  have hDualEqP0 :
      fenchelDualSupremum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) =
        helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 := by
    -- The lower bound from the chosen witness and the universal weak-duality upper bound pin down
    -- the dual supremum exactly.
    apply le_antisymm hDualLeP0
    exact le_trans hP0LeDualObj hObjLeSup
  have hAttains :
      fenchelDualSupremum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) =
        fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          zStar := by
    -- The same sandwich shows that this witness actually attains the supremum.
    apply le_antisymm
    · calc
        fenchelDualSupremum
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) =
          helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 :=
            hDualEqP0
        _ ≤
          fenchelDualObjective
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
            zStar := hP0LeDualObj
    · exact hObjLeSup
  constructor
  · -- The first field is the textbook equality between the translated value and the dual supremum.
    exact hDualEqP0.symm
  · -- The chosen middle dual vector is already the required attaining witness.
    exact ⟨zStar, hAttains⟩

/-- Helper for Theorem 38.5: if the translated value at `0` is already `⊥`, then the dual
supremum also collapses to `⊥`, and the attainment clause is witnessed by the zero middle dual
vector. -/
lemma helperForTheorem_38_5_textbookSpecialPairStrongDuality_botBranch
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hp0_bot :
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 =
        (⊥ : EReal)) :
    helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality F G yStar uStar := by
  have hDualLe :
      fenchelDualSupremum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) ≤
        helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 :=
    helperForTheorem_38_5_textbookDualSupremum_le_translatedDifferenceValueAtZero
      (F := F) (G := G) (yStar := yStar) (uStar := uStar)
  have hDualEqBot :
      fenchelDualSupremum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) =
        (⊥ : EReal) := by
    -- The dual supremum lies below `p(0) = ⊥`, so it must itself equal `⊥`.
    exact (le_bot_iff.mp <| by simpa [hp0_bot] using hDualLe)
  constructor
  · -- The translated strong-duality equality is exactly the common collapse to `⊥`.
    simpa [hDualEqBot] using hp0_bot
  · -- Once the supremum is `⊥`, the objective at any point is forced to be `⊥` as well.
    refine ⟨0, ?_⟩
    have hObjectiveZeroLe :
        fenchelDualObjective
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
            (0 : Fin n → ℝ) ≤
          fenchelDualSupremum
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) :=
      -- Reuse the theorem-local monotonicity helper at the zero witness.
      helperForTheorem_38_5_fenchelDualObjective_le_supremum
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) (xStarVec := 0)
    have hObjectiveZeroEqBot :
        fenchelDualObjective
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
            (0 : Fin n → ℝ) =
          (⊥ : EReal) := by
      exact le_bot_iff.mp <| by simpa [hDualEqBot] using hObjectiveZeroLe
    -- The chosen witness already attains the collapsed dual value.
    simp [hDualEqBot, hObjectiveZeroEqBot]

/-- Helper for Theorem 38.5: the finite translated-value branch should now pivot to the corrected
second-shift guarded perturbation from the original text. The old common-shift bundle is kept only
as a temporary surrogate while the final Chapter 29 witness-extraction step is migrated. -/
lemma helperForTheorem_38_5_textbookTranslatedDifference_finiteBranch_dualityAndAttainment
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (hp0_finite :
      IsFiniteEReal
        (helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0)) :
    helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality F G yStar uStar := by
  rcases
      helperForTheorem_38_5_textbookSecondShiftGuarded_supportingVector_of_legacyFiniteAtZero_and_hri
        (F := F) (G := G) (yStar := yStar) (uStar := uStar)
        hF_properConvex hG_properConvex hri hp0_finite with
    ⟨zStar, hzStarSupport⟩
  have hDualObjLower :
      helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0 ≤
        fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          zStar := by
    -- The supporting vector is already the affine minorant needed for the dual lower bound.
    exact
      helperForTheorem_38_5_textbookSecondShiftGuarded_dualObjectiveLowerBound_of_supportingVector
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) hri hzStarSupport
  have hP0EqCorr :
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 =
        helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0 :=
    helperForTheorem_38_5_translatedDifferenceValueAtZero_eq_secondShiftGuardedValueAtZero
      (F := F) (G := G) (yStar := yStar) (uStar := uStar)
  have hP0LeDualObj :
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 ≤
        fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          zStar := by
    simpa [hP0EqCorr] using hDualObjLower
  have hDualLeOpt :
      fenchelDualSupremum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) ≤
        helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 :=
    helperForTheorem_38_5_textbookDualSupremum_le_translatedDifferenceValueAtZero
      (F := F) (G := G) (yStar := yStar) (uStar := uStar)
  -- The supporting vector now provides the lower bound that, together with weak duality, forces
  -- both equality and attainment.
  exact
    helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality_of_sandwich
      (F := F) (G := G) (yStar := yStar) (uStar := uStar) (zStar := zStar)
      hP0LeDualObj hDualLeOpt

/-- Helper for Theorem 38.5: under the qualification hypothesis, the translated value at the
origin is either already `⊥` or else finite. This is the exact branch split used in the textbook
strong-duality argument. -/
lemma helperForTheorem_38_5_textbookTranslatedDifferenceValueAtZero_bot_or_finite_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 =
        (⊥ : EReal) ∨
      IsFiniteEReal
        (helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0) := by
  have hp0_ne_top :
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 ≠
        (⊤ : EReal) :=
    helperForTheorem_38_5_textbookTranslatedDifferenceValueAtZero_ne_top_of_hri
      (F := F) (G := G) (yStar := yStar) (uStar := uStar) hri
  by_cases hp0_bot :
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 =
        (⊥ : EReal)
  · exact Or.inl hp0_bot
  · -- Once the origin value is neither `⊤` nor `⊥`, it is finite by definition.
    exact Or.inr ⟨hp0_ne_top, hp0_bot⟩

/-- Helper for Theorem 38.5: the entire remaining dual-half proof under the qualification
hypothesis, isolated as the textbook special-pair strong-duality statement. This is exactly the
original-text step still missing after all bifunction-side rewrites have been completed. -/
lemma helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality F G yStar uStar := by
  -- Book route for the dual half: the bifunction-side rewrites are already finished.
  -- The remaining theorem-local target is anchored at the corrected second-shift translated value
  -- at `0`, and the proof now follows the textbook `⊥`/finite branch split.
  rcases
      helperForTheorem_38_5_textbookTranslatedDifferenceValueAtZero_bot_or_finite_of_hri
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) hri
    with hp0_bot | hp0_finite
  · -- When `p(0) = ⊥`, the already-proved dual inequality forces the dual supremum to collapse.
    exact
      helperForTheorem_38_5_textbookSpecialPairStrongDuality_botBranch
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) hp0_bot
  · -- The finite branch is exactly the guarded-perturbation argument isolated earlier.
    exact
      helperForTheorem_38_5_textbookTranslatedDifference_finiteBranch_dualityAndAttainment
        (F := F) (G := G) (yStar := yStar) (uStar := uStar)
        hF_properConvex hG_properConvex hri hp0_finite

/-- Helper for Theorem 38.5: the entire remaining dual-half proof under the qualification
hypothesis, isolated as the textbook special-pair strong-duality statement. This is exactly the
original-text step still missing after all bifunction-side rewrites have been completed. -/
lemma helperForTheorem_38_5_textbookSpecialPairStrongDuality_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    ∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
      helperForTheorem_38_5_textbookSpecialPairStrongDuality F G yStar uStar := by
  intro yStar uStar
  have hTranslated :
      helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality F G yStar uStar := by
    -- Route correction: the first conjunct was repaired from the stronger Chapter 29 predicate
    -- `IsConvexBifunction` to the Chapter 30 graph-convex predicate `ConvexBifunction`.
    -- The explicit actual-hypotheses counterexample still records why this change is necessary:
    -- it satisfies the theorem's proper-convex assumptions, its composition is
    -- `ConvexBifunction`, but it is not `IsConvexBifunction`.
    -- Book route for the dual half: the bifunction-side rewrites are already finished.
    -- The remaining theorem-local target is now anchored at the corrected second-shift
    -- translated value at `0`, while the displayed strong-duality proposition is still phrased via
    -- the legacy zero-slice surrogate because both coincide there with the same primal infimum.
    -- Route correction: a naive final step via `fenchel_duality_theorem` is too optimistic here.
    -- For fixed `uStar` and `yStar`, these textbook middle functions need not be proper in the
    -- Chapter 31 sense. This is now recorded explicitly by
    -- `helperForTheorem_38_5_actualCounterexample_textbookPrimalMiddle_not_properConvexFunctionOn`,
    -- and symmetrically by
    -- `helperForTheorem_38_5_actualCounterexample_textbookDualMiddle_not_properConcaveFunctionOn`,
    -- where the theorem's current bifunction hypotheses hold but the textbook primal middle
    -- function is identically `⊥` while a textbook dual middle function is identically `⊤`.
    -- Reuse the theorem-local translated-difference package proved just above.
    exact
      helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality_of_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hri := hri) (yStar := yStar) (uStar := uStar)
  exact
    (helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality_iff_specialPairStrongDuality
      (F := F) (G := G) (yStar := yStar) (uStar := uStar)).1 hTranslated

/-- Helper for Theorem 38.5: the graph function of `bifunctionCompose G F` is the fiber infimum
of the packed three-variable objective over the eliminated middle variable. -/
lemma helperForTheorem_38_5_packedTripleFiberSet_eq_middleRange
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (z : Fin (m + p) → ℝ) :
    {r : EReal |
        ∃ w : Fin (n + (m + p)) → ℝ,
          projLamLinearMap (n := n) (m := m + p) w = z ∧
            r = helperForTheorem_38_5_packedTripleObjective F G w} =
      Set.range (fun x : Fin n → ℝ =>
        F.toFun (projXLinearMap (n := m) (m := p) z) x +
          G.toFun x (projLamLinearMap (n := m) (m := p) z)) := by
  ext r
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨projXLinearMap (n := n) (m := m + p) w, ?_⟩
    -- Once the retained `(u, y)` coordinates are fixed to `z`, the packed objective collapses
    -- to the textbook middle-variable summand.
    simp [helperForTheorem_38_5_packedTripleObjective,
      helperForTheorem_38_5_threeVariableObjective, hw]
  · rintro ⟨x, rfl⟩
    refine ⟨Fin.append x z, ?_, ?_⟩
    · -- Appending the eliminated middle block leaves the visible `(u, y)` coordinates unchanged.
      ext i
      simp [projLamLinearMap]
    · -- Evaluating the packed objective at that witness recovers the same range element.
      simp [helperForTheorem_38_5_packedTripleObjective,
        helperForTheorem_38_5_threeVariableObjective, projXLinearMap, projLamLinearMap]

/-- Helper for Theorem 38.5: the graph function of `bifunctionCompose G F` is the fiber infimum
of the packed three-variable objective over the eliminated middle variable. -/
lemma helperForTheorem_38_5_graphFunctionComposeEqInfFiber_local
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p) :
    (fun z : Fin (m + p) → ℝ =>
        sInf {r : EReal |
          ∃ w : Fin (n + (m + p)) → ℝ,
            projLamLinearMap (n := n) (m := m + p) w = z ∧
              r = helperForTheorem_38_5_packedTripleObjective F G w}) =
      bifunctionGraphFunction (bifunctionCompose G F) := by
  -- First replace the packed fiber by the explicit range over the eliminated middle variable.
  funext z
  rw [helperForTheorem_38_5_packedTripleFiberSet_eq_middleRange (F := F) (G := G) (z := z)]
  -- The remaining `sInf` over that range is exactly the defining infimum of the composed graph
  -- function.
  rw [sInf_range, bifunctionGraphFunction, bifunctionCompose]
  simp [projXLinearMap, projLamLinearMap]

/-- Helper for Theorem 38.5: product-space proper convexity of the graph functions of `F` and `G`
implies graph convexity of the composition `bifunctionCompose G F`. -/
lemma helperForTheorem_38_5_composeConvexBifunction_local
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    ConvexBifunction (bifunctionCompose G F) := by
  let tripleObjective : (Fin (n + (m + p)) → ℝ) → EReal :=
    helperForTheorem_38_5_packedTripleObjective F G
  let packedFMap : (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
    { toFun := fun w =>
        Fin.append
          (projXLinearMap (n := m) (m := p)
            (projLamLinearMap (n := n) (m := m + p) w))
          (projXLinearMap (n := n) (m := m + p) w)
      map_add' := by
        intro w₁ w₂
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_left, Pi.add_apply]
        | right i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_right, Pi.add_apply]
      map_smul' := by
        intro a w
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_left, Pi.smul_apply]
        | right i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_right, Pi.smul_apply] }
  let packedGMap : (Fin (n + (m + p)) → ℝ) →ₗ[ℝ] (Fin (n + p) → ℝ) :=
    { toFun := fun w =>
        Fin.append
          (projXLinearMap (n := n) (m := m + p) w)
          (projLamLinearMap (n := m) (m := p)
            (projLamLinearMap (n := n) (m := m + p) w))
      map_add' := by
        intro w₁ w₂
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_left, Pi.add_apply]
        | right i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_right, Pi.add_apply]
      map_smul' := by
        intro a w
        ext i
        cases i using Fin.addCases with
        | left i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_left, Pi.smul_apply]
        | right i =>
            simp [projLamLinearMap, projXLinearMap, Fin.append_right, Pi.smul_apply] }
  have hPackedF_surj : Function.Surjective packedFMap := by
    intro z
    refine ⟨Fin.append (fun j : Fin n => z (Fin.natAdd m j))
      (Fin.append (fun i : Fin m => z (Fin.castAdd n i)) (0 : Fin p → ℝ)), ?_⟩
    ext i
    cases i using Fin.addCases with
    | left i =>
        simp [packedFMap, projLamLinearMap, projXLinearMap, Fin.append_left]
    | right i =>
        simp [packedFMap, projLamLinearMap, projXLinearMap, Fin.append_right]
  have hPackedG_surj : Function.Surjective packedGMap := by
    intro z
    refine ⟨Fin.append (fun i : Fin n => z (Fin.castAdd p i))
      (Fin.append (0 : Fin m → ℝ) (fun j : Fin p => z (Fin.natAdd n j))), ?_⟩
    ext i
    cases i using Fin.addCases with
    | left i =>
        simp [packedGMap, projLamLinearMap, projXLinearMap, Fin.append_left]
    | right i =>
        simp [packedGMap, projLamLinearMap, projXLinearMap, Fin.append_right]
  have hFGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (bifunctionGraphFunction F.toFun) := by
    -- Convert graph-level proper convexity into the Chapter 1 proper-convex package on `Set.univ`.
    exact
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction F.toFun) hF_properConvex.2
  have hGGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + p) → ℝ))
        (bifunctionGraphFunction G.toFun) := by
    -- Apply the same graph-function conversion to `G`.
    exact
      helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
        (f := bifunctionGraphFunction G.toFun) hG_properConvex.2
  have hLiftedFProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ))
        (fun w => bifunctionGraphFunction F.toFun (packedFMap w)) := by
    -- Lift the graph function of `F` to the combined `(x, u, y)` coordinates.
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := packedFMap) hPackedF_surj hFGraphProper
  have hLiftedGProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ))
        (fun w => bifunctionGraphFunction G.toFun (packedGMap w)) := by
    -- Lift the graph function of `G` by the projection that keeps the `(x, y)` block.
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := packedGMap) hPackedG_surj hGGraphProper
  have hTripleConv :
      ConvexFunctionOn (Set.univ : Set (Fin (n + (m + p)) → ℝ)) tripleObjective := by
    -- The three-variable objective is the sum of the two lifted proper convex graph functions.
    simpa [tripleObjective, packedFMap, packedGMap, bifunctionGraphFunction] using
      (convexFunctionOn_add_of_proper
        (n := n + (m + p)) hLiftedFProper hLiftedGProper)
  have hFiberConv :
      ConvexFunctionOn (Set.univ : Set (Fin (m + p) → ℝ))
        (fun z : Fin (m + p) → ℝ =>
          sInf {r : EReal |
            ∃ w : Fin (n + (m + p)) → ℝ,
              projLamLinearMap (n := n) (m := m + p) w = z ∧ r = tripleObjective w}) := by
    -- Theorem 5.7 preserves convexity under the partial infimum over the eliminated middle block.
    simpa using
      (convexFunctionOn_inf_fiber_linearMap (A := projLamLinearMap (n := n) (m := m + p))
        (h := tripleObjective) hTripleConv)
  have hGraphEq :
      (fun z : Fin (m + p) → ℝ =>
        sInf {r : EReal |
          ∃ w : Fin (n + (m + p)) → ℝ,
            projLamLinearMap (n := n) (m := m + p) w = z ∧ r = tripleObjective w}) =
        bifunctionGraphFunction (bifunctionCompose G F) := by
    -- Rewrite the fiber-infimum formula back into the graph function of the composed bifunction.
    simpa [tripleObjective] using
      helperForTheorem_38_5_graphFunctionComposeEqInfFiber_local (F := F) (G := G)
  have hGraphConv :
      ConvexFunctionOn (Set.univ : Set (Fin (m + p) → ℝ))
        (bifunctionGraphFunction (bifunctionCompose G F)) := by
    -- Substitute the graph-function identity into the convex fiber-infimum result.
    simpa [hGraphEq] using hFiberConv
  -- Translate the Chapter 1 convex-function statement back to Chapter 30 graph convexity.
  simpa [ConvexBifunction, ConvexFunction] using hGraphConv

/-- Helper for Theorem 38.5: under the relative-interior qualification, the existing
special-pair strong-duality package yields both the displayed adjoint identity and the
attainment statement. -/
lemma helperForTheorem_38_5_pointwiseDualEqualityAndAttainment_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri : (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionAdjoint (bifunctionCompose G F) yStar uStar =
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
            yStar uStar ∧
      ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
            yStar uStar =
          (bifunctionAdjoint G.toFun) yStar xStar + (bifunctionAdjoint F.toFun) xStar uStar := by
  -- First obtain the textbook special-pair strong-duality statement for this fixed dual pair.
  have hStrong :
      helperForTheorem_38_5_textbookSpecialPairStrongDuality F G yStar uStar :=
    helperForTheorem_38_5_textbookSpecialPairStrongDuality_of_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
      hri yStar uStar
  -- Then use the established bridge from the textbook scalar statement back to bifunction
  -- adjoints and the attaining middle dual vector.
  exact
    helperForTheorem_38_5_pointwiseConclusion_of_textbookSpecialPairStrongDuality
      (F := F) (G := G) (yStar := yStar) (uStar := uStar) hStrong

/-- Helper for Theorem 38.5: under the relative-interior qualification, the existing
special-pair strong-duality package yields both the displayed adjoint identity and the
attainment statement. -/
lemma helperForTheorem_38_5_dualEqualityAndAttainment_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri : (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    bifunctionAdjoint (bifunctionCompose G F) =
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun) ∧
      (∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
        ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
          bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
              yStar uStar =
            (bifunctionAdjoint G.toFun) yStar xStar + (bifunctionAdjoint F.toFun) xStar uStar) := by
  constructor
  · -- Apply the new pointwise qualified bridge and package its first projection as equality of
    -- bifunctions.
    funext yStar
    funext uStar
    exact
      (helperForTheorem_38_5_pointwiseDualEqualityAndAttainment_of_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hri := hri) yStar uStar).1
  · -- Reuse the same pointwise bridge for the attainment clause.
    intro yStar uStar
    exact
      (helperForTheorem_38_5_pointwiseDualEqualityAndAttainment_of_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex)
        (hri := hri) yStar uStar).2

/-- Helper for Theorem 38.5: the qualification hypothesis already yields one primal pair where the
composition `GF` is not `⊤`. This is the exact primal-side witness extracted from the common-domain
point in the original text. -/
lemma helperForTheorem_38_5_compose_exists_ne_top_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hri : (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    ∃ u : Fin m → ℝ, ∃ y : Fin p → ℝ, bifunctionCompose G F u y ≠ (⊤ : EReal) := by
  have hFenchelA :
      FenchelConditionA (n := n)
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F
          (0 : Module.Dual ℝ (Fin m → ℝ)))
        (helperForTheorem_38_5_textbookDualMiddleFunction G
          (0 : Module.Dual ℝ (Fin p → ℝ))) := by
    simpa using
      (helperForTheorem_38_5_hri_implies_fenchelConditionA
        (F := F) (G := G)
        (yStar := (0 : Module.Dual ℝ (Fin p → ℝ)))
        (uStar := (0 : Module.Dual ℝ (Fin m → ℝ))) hri)
  rcases hFenchelA with ⟨x0, hx0riF, hx0riG⟩
  have hx0F :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F
          (0 : Module.Dual ℝ (Fin m → ℝ))) :=
    helperForTheorem_21_1_riFin_subset_C (n := n)
      (effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F
          (0 : Module.Dual ℝ (Fin m → ℝ)))) hx0riF
  have hx0G :
      x0 ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G
          (0 : Module.Dual ℝ (Fin p → ℝ))) :=
    helperForTheorem_21_1_riFin_subset_C (n := n)
      (concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G
          (0 : Module.Dual ℝ (Fin p → ℝ)))) hx0riG
  have hx0F_dom : x0 ∈ bifunctionDomBot (bifunctionInverse F.toFun) := by
    simpa [helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain] using hx0F
  have hx0G_dom : x0 ∈ bifunctionDom G.toFun := by
    simpa [helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain] using hx0G
  rcases hx0F_dom with ⟨u, huInv⟩
  have hu : F.toFun u x0 ≠ (⊤ : EReal) := by
    simpa [bifunctionInverse] using huInv
  rcases hx0G_dom with ⟨y, hy⟩
  refine ⟨u, y, ?_⟩
  have hSum_ne_top : F.toFun u x0 + G.toFun x0 y ≠ (⊤ : EReal) :=
    EReal.add_ne_top hu hy
  intro hTop
  have hLe : bifunctionCompose G F u y ≤ F.toFun u x0 + G.toFun x0 y := by
    rw [bifunctionCompose]
    exact iInf_le (fun x : Fin n → ℝ => F.toFun u x + G.toFun x y) x0
  have hTopLe : (⊤ : EReal) ≤ F.toFun u x0 + G.toFun x0 y := by
    simpa [hTop] using hLe
  exact hSum_ne_top (top_le_iff.mp hTopLe)

/-- Helper for Theorem 38.5: under the qualification hypothesis, the theorem's convexity conclusion
and its qualified dual package can be assembled from the existing local helper chain in one place. -/
lemma helperForTheorem_38_5_mainConclusions_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri : (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    ConvexBifunction (bifunctionCompose G F) ∧
      bifunctionAdjoint (bifunctionCompose G F) =
          bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun) ∧
      (∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
        ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
          bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
              yStar uStar =
            (bifunctionAdjoint G.toFun) yStar xStar + (bifunctionAdjoint F.toFun) xStar uStar) := by
  have hComposeConvexBifunction :
      ConvexBifunction (bifunctionCompose G F) :=
    -- The graph-function argument from Theorem 5.7 already proves the unconditional convexity
    -- half of the theorem.
    helperForTheorem_38_5_composeConvexBifunction_local F G hF_properConvex hG_properConvex
  have hDualPackage :
      bifunctionAdjoint (bifunctionCompose G F) =
          bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun) ∧
      (∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
        ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
          bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
              yStar uStar =
            (bifunctionAdjoint G.toFun) yStar xStar + (bifunctionAdjoint F.toFun) xStar uStar) :=
    -- The qualified dual equality and the attained supremum are already packaged by the
    -- theorem-local strong-duality helper.
    helperForTheorem_38_5_dualEqualityAndAttainment_of_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex) hri
  rcases hDualPackage with ⟨hDualEq, hAttains⟩
  -- Bundle the convexity half with the qualified dual data so the main theorem can project out the
  -- exact pieces it needs.
  exact ⟨hComposeConvexBifunction, hDualEq, hAttains⟩

/-- Helper for Theorem 38.5: once the qualification hypothesis is fixed, the bundled local
conclusions immediately reduce to the exact dual-equality and attainment package used in the
theorem statement. -/
lemma helperForTheorem_38_5_qualifiedDualPackage_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri : (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    bifunctionAdjoint (bifunctionCompose G F) =
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun) ∧
      (∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
        ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
          bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
              yStar uStar =
            (bifunctionAdjoint G.toFun) yStar xStar + (bifunctionAdjoint F.toFun) xStar uStar) := by
  -- Discard the already-separate convexity projection and retain only the qualified dual package.
  rcases
      helperForTheorem_38_5_mainConclusions_of_hri
        (F := F) (G := G)
        (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex) hri with
    ⟨_, hDualEq, hAttains⟩
  exact ⟨hDualEq, hAttains⟩

/-- Helper for Theorem 38.5: under the qualification hypothesis, the displayed adjoint identity is
the equality projection of the packaged dual conclusion. -/
lemma helperForTheorem_38_5_qualifiedDualEquality_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri : (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    bifunctionAdjoint (bifunctionCompose G F) =
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun) := by
  -- Reuse the theorem-local qualified package and keep only its displayed equality field.
  exact
    (helperForTheorem_38_5_qualifiedDualPackage_of_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex) hri).1

/-- Helper for Theorem 38.5: under the qualification hypothesis, the supremum in the displayed
composition-of-adjoints formula is attained for every outer dual pair. -/
lemma helperForTheorem_38_5_qualifiedAttainment_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri : (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    ∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
      ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
            yStar uStar =
          (bifunctionAdjoint G.toFun) yStar xStar + (bifunctionAdjoint F.toFun) xStar uStar := by
  intro yStar uStar
  -- The same packaged theorem-local conclusion already contains the universal attainment witness.
  exact
    (helperForTheorem_38_5_qualifiedDualPackage_of_hri
      (F := F) (G := G)
      (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex) hri).2
      yStar uStar

/-- Theorem 38.5: Let `F` be a proper convex bifunction from `ℝ^m` to `ℝ^n`, and let `G` be a
proper convex bifunction from `ℝ^n` to `ℝ^p`. Then the composition `GF` is a convex bifunction
from `ℝ^m` to `ℝ^p`.

If `ri (dom F_*)` and `ri (dom G)` have a point in common, then

`(GF)^* = F^* G^*`,

and the supremum in the definition of `((F^* G^*) y*)(u*)` is attained for each `u*` and `y*`.

In Lean:
- `GF` is `bifunctionCompose G F`;
- `F_*` is `bifunctionInverse F.toFun`;
- the book's "proper convex bifunction" assumptions are modeled by the extra hypotheses
  `ProperConvexBifunction F.toFun` and `ProperConvexBifunction G.toFun`;
- the first conclusion "GF is a convex bifunction" follows the book's graph-function proof via
  Theorem 5.7, so it is currently modeled by the Chapter 30 graph-convex predicate
  `ConvexBifunction`;
- `ri` is modeled by `intrinsicInterior`, applied to
  `bifunctionDomBot (bifunctionInverse F.toFun)` and `bifunctionDom G.toFun`;
- `F^*` and `(GF)^*` are modeled by `bifunctionAdjoint`;
- the product `F^* G^*` is modeled by `bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun)
    (bifunctionAdjoint G.toFun)`. -/

theorem theorem38_5_compose_convex_and_adjoint_eq_composeSup_adjoint
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    ConvexBifunction (bifunctionCompose G F) ∧
      ((intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
            intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty →
        bifunctionAdjoint (bifunctionCompose G F) =
            bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun) ∧
          (∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
            ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
              bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
                  yStar uStar =
                (bifunctionAdjoint G.toFun) yStar xStar + (bifunctionAdjoint F.toFun) xStar uStar)) :=
  by
    constructor
    · -- The first conjunct is exactly the graph-convex composition statement proved above.
      exact helperForTheorem_38_5_composeConvexBifunction_local F G hF_properConvex hG_properConvex
    · intro hri
      -- Split the qualification conclusion into the exact equality and attainment clauses that
      -- appear explicitly in the theorem statement.
      refine ⟨?_, ?_⟩
      · exact
          helperForTheorem_38_5_qualifiedDualEquality_of_hri
            (F := F) (G := G)
            (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex) hri
      · exact
          helperForTheorem_38_5_qualifiedAttainment_of_hri
            (F := F) (G := G)
            (hF_properConvex := hF_properConvex) (hG_properConvex := hG_properConvex) hri

-- Proof sketch: Apply Theorem 38.5 to the dual pair `F^*` and `G^*`, exactly as in the text.
-- Since `F` and `G` are closed, Theorems 6.6 and 6.8 identify the double adjoints with the
-- original bifunctions, so `(F^* G^*)^* = GF`. Because an adjoint is closed, this yields
-- closedness of `GF`; the attainment statement comes from the attained supremum in Theorem 38.5
-- after dualizing back to the primal infimum. The final formula `(GF)^* = cl (F^* G^*)` is then
-- the closed-envelope version of the dual identity, with `cl` modeled by `bifunctionClosure`.
/-- Helper for Corollary 38.5.1: product lower semicontinuity upgrades a proper convex bifunction
to the Chapter 6 closed-convex package on its graph function. -/
lemma helperForCorollary_38_5_1_closedProper_implies_closedConvex
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun) :
    ClosedConvexBifunction F.toFun := by
  have hClosedGraphF : LowerSemicontinuous (bifunctionGraphFunction F.toFun) := by
    -- Convert product lower semicontinuity of `F` into graph lower semicontinuity in Chapter 6
    -- coordinates.
    simpa [IsProductLowerSemicontinuousBifunction, bifunctionGraphFunction] using
      hF_closed.comp
        (show Continuous
            (fun z : Fin (m + n) → ℝ =>
              ((fun i : Fin m => z (Fin.castAdd n i)), (fun j : Fin n => z (Fin.natAdd m j))))
          by
            continuity)
  -- Package convexity and graph closedness into the standard closed-convex bifunction predicate.
  refine ⟨hF_properConvex.1, ?_⟩
  exact ⟨hF_properConvex.1, hClosedGraphF⟩

/-- Helper for Corollary 38.5.1: the Chapter 6 packaged adjoint of a closed proper convex
bifunction is already closed and proper on the concave side. -/
lemma helperForCorollary_38_5_1_packagedAdjoint_closedProperConcave
    {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun) :
    ClosedConcaveBifunction
        (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) ∧
      ProperConcaveBifunction
        (adjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩) := by
  have hClosedConvexF : ClosedConvexBifunction F.toFun :=
    helperForCorollary_38_5_1_closedProper_implies_closedConvex
      (F := F) (hF_properConvex := hF_properConvex) (hF_closed := hF_closed)
  rcases
      (adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality (F := F.toFun)).1
        hF_properConvex.1 with
    ⟨_, _, _, _, hClosedProperAdjoint, _⟩
  -- Apply the closed-proper branch of the Chapter 6 adjoint theorem to the closedness package
  -- just constructed.
  exact hClosedProperAdjoint ⟨hClosedConvexF, hF_properConvex⟩

/-- Helper for Corollary 38.5.1: closed properness identifies the Chapter 6 biadjoints of `F`
and `G` with the original primal bifunctions. -/
lemma helperForCorollary_38_5_1_closedProper_biadjoint_rewrites
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hF_closed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hG_closed : IsProductLowerSemicontinuousBifunction G.toFun) :
    biadjointOfConvexBifunction ⟨F.toFun, hF_properConvex.1⟩ = F.toFun ∧
      biadjointOfConvexBifunction ⟨(G.toFun : (Fin n → ℝ) → (Fin p → ℝ) → EReal), hG_properConvex.1⟩ = G.toFun := by
  constructor
  · -- Turn product lower semicontinuity into graph closedness, then collapse the biadjoint.
    have hClosedConvexF : ClosedConvexBifunction F.toFun :=
      helperForCorollary_38_5_1_closedProper_implies_closedConvex
        (F := F) (hF_properConvex := hF_properConvex) (hF_closed := hF_closed)
    have hClosureFixedF : convexBifunctionClosure F.toFun = F.toFun := by
      -- Closed proper convex bifunctions are fixed by the Chapter 6 closure operator.
      exact
        helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed_proper
          (hClosed := hClosedConvexF) (hProper := hF_properConvex)
    -- The Chapter 6 biconjugation theorem now rewrites `F**` back to `F`.
    exact
      helperForTheorem_6_30_11_convex_biadjoint_eq_self_of_closure_eq_self
        (hF := hF_properConvex.1) hClosureFixedF
  · -- Repeat the same closed-proper biconjugation argument for `G`.
    have hClosedConvexG : ClosedConvexBifunction G.toFun :=
      helperForCorollary_38_5_1_closedProper_implies_closedConvex
        (F := G) (hF_properConvex := hG_properConvex) (hF_closed := hG_closed)
    have hClosureFixedG : convexBifunctionClosure G.toFun = G.toFun := by
      -- Closed proper convex bifunctions are fixed by the Chapter 6 closure operator.
      exact
        helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed_proper
          (hClosed := hClosedConvexG) (hProper := hG_properConvex)
    -- The Chapter 6 biconjugation theorem now rewrites `G**` back to `G`.
    exact
      helperForTheorem_6_30_11_convex_biadjoint_eq_self_of_closure_eq_self
        (hF := hG_properConvex.1) hClosureFixedG

/-- Helper for Corollary 38.5.1: lower-semicontinuous hull commutes with precomposition by a
homeomorphism. -/
lemma helperForCorollary_38_5_1_erealLowerSemicontinuousHull_precomp_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (f : Y → EReal) :
    erealLowerSemicontinuousHull (fun x => f (e x)) =
      fun x => erealLowerSemicontinuousHull f (e x) := by
  funext x
  unfold erealLowerSemicontinuousHull
  apply le_antisymm
  · rw [iSup_le_iff]
    intro h
    refine le_iSup_of_le ⟨fun y => h.1 (e.symm y), ?_⟩ ?_
    · constructor
      · simpa [Function.comp] using h.2.1.comp_continuous e.symm.continuous
      · intro y
        simpa using h.2.2 (e.symm y)
    · simp
  · rw [iSup_le_iff]
    intro h
    refine le_iSup_of_le ⟨fun x => h.1 (e x), ?_⟩ ?_
    · constructor
      · simpa [Function.comp] using h.2.1.comp_continuous e.continuous
      · intro y
        simpa using h.2.2 (e y)
    · simp

/-- Helper for Corollary 38.5.1: the book-style `erealFunctionClosure` commutes with
precomposition by a homeomorphism. -/
lemma helperForCorollary_38_5_1_erealFunctionClosure_precomp_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (f : Y → EReal) :
    erealFunctionClosure (fun x => f (e x)) =
      fun x => erealFunctionClosure f (e x) := by
  classical
  unfold erealFunctionClosure
  by_cases h : ∀ y, f y ≠ (⊥ : EReal)
  · have hpre : ∀ x, f (e x) ≠ (⊥ : EReal) := by
      intro x
      exact h (e x)
    simp [h,
      helperForCorollary_38_5_1_erealLowerSemicontinuousHull_precomp_homeomorph]
  · have hpre : ¬ ∀ x, f (e x) ≠ (⊥ : EReal) := by
      intro hpre
      apply h
      intro y
      simpa using hpre (e.symm y)
    simp [h, hpre]

/-- Helper for Corollary 38.5.1: `bifunctionClosure` commutes with precomposition by product
homeomorphisms. -/
lemma helperForCorollary_38_5_1_bifunctionClosure_precomp_homeomorph
    {U U' X X' : Type*}
    [TopologicalSpace U] [TopologicalSpace U'] [TopologicalSpace X] [TopologicalSpace X']
    (eU : U ≃ₜ U') (eX : X ≃ₜ X') (F : U' → X' → EReal) :
    bifunctionClosure (fun u x => F (eU u) (eX x)) =
      fun u x => bifunctionClosure F (eU u) (eX x) := by
  let eProd : U × X ≃ₜ U' × X' := Homeomorph.prodCongr eU eX
  funext u x
  change erealFunctionClosure (fun p : U × X => F (eU p.1) (eX p.2)) (u, x) =
    erealFunctionClosure (fun p : U' × X' => F p.1 p.2) (eU u, eX x)
  simpa [eProd, Prod.map] using
    congrFun
      (helperForCorollary_38_5_1_erealFunctionClosure_precomp_homeomorph
        (e := eProd) (f := fun p : U' × X' => F p.1 p.2))
      (u, x)



end Section38
end Chap08
