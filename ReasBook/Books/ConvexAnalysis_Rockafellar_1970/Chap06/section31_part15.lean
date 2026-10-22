/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part14

open scoped Topology

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Helper for Lemma 31.0.13: the one-dimensional counterexample convex function is the
singleton indicator `δ_{ {0} }`. -/
noncomputable def helperForLemma_31_0_13_counterexampleF : (Fin 1 → ℝ) → EReal :=
  indicatorFunction ({0} : Set (Fin 1 → ℝ))

/-- Helper for Lemma 31.0.13: the one-dimensional counterexample closed function is the
constant-zero function. -/
noncomputable def helperForLemma_31_0_13_counterexampleG : (Fin 1 → ℝ) → EReal :=
  fun _ => (0 : EReal)

/-- Helper for Lemma 31.0.13: the counterexample primal infimum is exactly `0`. -/
lemma helperForLemma_31_0_13_counterexample_primalInfimum_eq_zero :
    functionInfimumEReal
        (fun x : Fin 1 → ℝ =>
          helperForLemma_31_0_13_counterexampleF x -
            helperForLemma_31_0_13_counterexampleG x) =
      (0 : EReal) := by
  -- Sampling the origin gives the upper bound `inf ≤ 0`.
  apply le_antisymm
  · simpa [functionInfimumEReal, helperForLemma_31_0_13_counterexampleF,
      helperForLemma_31_0_13_counterexampleG, indicatorFunction] using
      (iInf_le
        (fun x : Fin 1 → ℝ =>
          helperForLemma_31_0_13_counterexampleF x -
            helperForLemma_31_0_13_counterexampleG x)
        (0 : Fin 1 → ℝ))
  · -- Every objective value is either `0` at the origin or `⊤` away from it, so `0` is a lower
    -- bound for the whole family.
    rw [functionInfimumEReal]
    refine le_iInf ?_
    intro x
    by_cases hx : x = (0 : Fin 1 → ℝ)
    · simp [helperForLemma_31_0_13_counterexampleF, helperForLemma_31_0_13_counterexampleG,
        indicatorFunction, hx]
    · simp [helperForLemma_31_0_13_counterexampleF, helperForLemma_31_0_13_counterexampleG,
        indicatorFunction, hx]

/-- Helper for Lemma 31.0.13: translating the constant-zero `g` leaves the value function
identically equal to `0` in the counterexample. -/
lemma helperForLemma_31_0_13_counterexample_translatedValue_eq_zero (u : Fin 1 → ℝ) :
    translatedDifferenceValueFunction
        (n := 1) helperForLemma_31_0_13_counterexampleF
        helperForLemma_31_0_13_counterexampleG u =
      (0 : EReal) := by
  -- The translation parameter disappears because `g` is constant.
  simpa [translatedDifferenceValueFunction, helperForLemma_31_0_13_counterexampleF,
    helperForLemma_31_0_13_counterexampleG] using
    helperForLemma_31_0_13_counterexample_primalInfimum_eq_zero

/-- Helper for Lemma 31.0.13: the upper directional derivative of the constant-zero function is
`0` in every direction. -/
lemma helperForLemma_31_0_13_upperDirectionalDerivative_counterexampleG_eq_zero
    (x y : Fin 1 → ℝ) :
    upperDirectionalDerivativeAt helperForLemma_31_0_13_counterexampleG x y = (0 : EReal) := by
  -- The positive-step quotients of a constant function are identically `0`, so their infimum is
  -- also `0`.
  have hmono :
      MonotoneOn (directionalDifferenceQuotientAt helperForLemma_31_0_13_counterexampleG x y)
        (Set.Ioi (0 : ℝ)) := by
    intro s hs t ht hst
    simp [directionalDifferenceQuotientAt, helperForLemma_31_0_13_counterexampleG]
  rw [helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients
    helperForLemma_31_0_13_counterexampleG x y hmono]
  simp [directionalDifferenceQuotientAt, helperForLemma_31_0_13_counterexampleG]

/-- Helper for Lemma 31.0.13: the counterexample satisfies the directional-derivative condition
`p'(0; y) > -∞` for every direction `y`. -/
lemma helperForLemma_31_0_13_counterexample_directionalCondition_holds :
    ∀ y : Fin 1 → ℝ,
      upperDirectionalDerivativeAt
          (translatedDifferenceValueFunction
            (n := 1) helperForLemma_31_0_13_counterexampleF
            helperForLemma_31_0_13_counterexampleG)
          (0 : Fin 1 → ℝ) y > (⊥ : EReal) := by
  -- Rewrite the translated value function as the constant-zero function and use the explicit
  -- directional-derivative computation above.
  intro y
  have hConst :
      translatedDifferenceValueFunction
          (n := 1) helperForLemma_31_0_13_counterexampleF
          helperForLemma_31_0_13_counterexampleG =
        helperForLemma_31_0_13_counterexampleG := by
    funext u
    exact helperForLemma_31_0_13_counterexample_translatedValue_eq_zero u
  rw [hConst]
  rw [helperForLemma_31_0_13_upperDirectionalDerivative_counterexampleG_eq_zero]
  simp

/-- Helper for Lemma 31.0.13: at the nonzero dual vector `(1)`, the counterexample dual
objective takes the value `⊤`. -/
lemma helperForLemma_31_0_13_counterexample_dualValue_at_one_eq_top :
    fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG (fun _ : Fin 1 => (1 : ℝ)) -
      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF (fun _ : Fin 1 => (1 : ℝ)) =
    (⊤ : EReal) := by
  -- The conjugate identities from Chapter 16 turn the dual gap into `⊤ - 0`.
  have hConjG :
      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG =
        indicatorFunction ({0} : Set (Fin 1 → ℝ)) := by
    simpa [helperForLemma_31_0_13_counterexampleG] using
      (section16_fenchelConjugate_const_zero (n := 1))
  have hConjF :
      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF =
        (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
    simpa [helperForLemma_31_0_13_counterexampleF] using
      (section16_fenchelConjugate_indicator_singleton_zero (n := 1))
  have hone_ne_zero : (fun _ : Fin 1 => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
    intro h
    have hCoord : (1 : ℝ) = 0 := by
      have h0 := congrArg (fun v : Fin 1 → ℝ => v (0 : Fin 1)) h
      simpa using h0
    norm_num at hCoord
  simp [hConjG, hConjF, indicatorFunction, hone_ne_zero]

/-- Helper for Lemma 31.0.13: the counterexample dual supremum is `⊤`. -/
lemma helperForLemma_31_0_13_counterexample_dualSup_eq_top :
    (⨆ xStar : Fin 1 → ℝ,
      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
        fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar) =
      (⊤ : EReal) := by
  -- A single nonzero dual vector already attains the value `⊤`, so the supremum is forced to be
  -- `⊤`.
  apply top_unique
  let xStarOne : Fin 1 → ℝ := fun _ => 1
  have hOne :
      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStarOne -
        fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStarOne =
      (⊤ : EReal) := by
    simpa [xStarOne] using helperForLemma_31_0_13_counterexample_dualValue_at_one_eq_top
  calc
    (⊤ : EReal) =
        fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStarOne -
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStarOne := by
      symm
      exact hOne
    _ ≤ ⨆ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar := by
      exact le_iSup
        (fun xStar : Fin 1 → ℝ =>
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar)
        xStarOne

/-- Helper for Lemma 31.0.13: the counterexample has no Kuhn-Tucker vector satisfying the
displayed dual-attainment and primal-equality conditions. -/
lemma helperForLemma_31_0_13_counterexample_no_kuhnTuckerVector :
    ¬ ∃ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
              (⨆ z : Fin 1 → ℝ,
                fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
                  fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) ∧
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
            functionInfimumEReal
              (fun x : Fin 1 → ℝ =>
                helperForLemma_31_0_13_counterexampleF x -
                  helperForLemma_31_0_13_counterexampleG x) := by
  -- If such a vector existed, the dual supremum and primal infimum would coincide. The explicit
  -- evaluations above show they are `⊤` and `0`, respectively.
  intro hExists
  rcases hExists with ⟨xStar, hxSup, hxInf⟩
  have hTopEqZero : (⊤ : EReal) = (0 : EReal) := by
    calc
      (⊤ : EReal) =
          (⨆ z : Fin 1 → ℝ,
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) :=
        helperForLemma_31_0_13_counterexample_dualSup_eq_top.symm
      _ =
          functionInfimumEReal
            (fun x : Fin 1 → ℝ =>
              helperForLemma_31_0_13_counterexampleF x -
                helperForLemma_31_0_13_counterexampleG x) := by
        rw [← hxSup, hxInf]
      _ = (0 : EReal) := helperForLemma_31_0_13_counterexample_primalInfimum_eq_zero
  simp at hTopEqZero

/-- Helper for Lemma 31.0.13: the specialized `iff` conclusion already fails for the explicit
one-dimensional counterexample. -/
lemma helperForLemma_31_0_13_counterexample_iff_fails :
    ¬
      ((∃ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                (⨆ z : Fin 1 → ℝ,
                  fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
                    fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) ∧
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
              functionInfimumEReal
                (fun x : Fin 1 → ℝ =>
                  helperForLemma_31_0_13_counterexampleF x -
                    helperForLemma_31_0_13_counterexampleG x)) ↔
        ∀ y : Fin 1 → ℝ,
          upperDirectionalDerivativeAt
              (translatedDifferenceValueFunction
                (n := 1) helperForLemma_31_0_13_counterexampleF
                helperForLemma_31_0_13_counterexampleG)
              (0 : Fin 1 → ℝ) y > (⊥ : EReal)) := by
  -- The right-hand side holds by direct computation, while the left-hand side is impossible.
  intro hIff
  have hExists :
      ∃ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
              (⨆ z : Fin 1 → ℝ,
                fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
                  fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) ∧
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
            functionInfimumEReal
              (fun x : Fin 1 → ℝ =>
                helperForLemma_31_0_13_counterexampleF x -
                  helperForLemma_31_0_13_counterexampleG x) :=
    hIff.mpr helperForLemma_31_0_13_counterexample_directionalCondition_holds
  exact helperForLemma_31_0_13_counterexample_no_kuhnTuckerVector hExists

/-- Helper for Lemma 31.0.13: the explicit one-dimensional counterexample already satisfies every
hypothesis in the current theorem header, so the obstruction really lies in the theorem
statement. -/
lemma helperForLemma_31_0_13_counterexample_satisfies_currentHypotheses :
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_13_counterexampleF ∧
      ClosedConvexFunction helperForLemma_31_0_13_counterexampleF ∧
      ClosedERealFunction helperForLemma_31_0_13_counterexampleG ∧
      (∀ x, helperForLemma_31_0_13_counterexampleG x ≠ (⊥ : EReal)) ∧
      (Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              helperForLemma_31_0_13_counterexampleF ∩
            effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              helperForLemma_31_0_13_counterexampleG) ∨
        Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF) ∩
            effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG))) ∧
      IsFiniteEReal
        (functionInfimumEReal
          (fun x : Fin 1 → ℝ =>
            helperForLemma_31_0_13_counterexampleF x -
              helperForLemma_31_0_13_counterexampleG x)) := by
  have hIndicator :
      ClosedConvexFunction (indicatorFunction ({0} : Set (Fin 1 → ℝ))) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
          (indicatorFunction ({0} : Set (Fin 1 → ℝ))) := by
    -- The singleton `{0}` is closed, convex, and nonempty, so its indicator is closed proper
    -- convex.
    simpa using
      (closedConvexFunction_indicator_neg (n := 1) (C := ({0} : Set (Fin 1 → ℝ)))
        (by simp)
        (by simp)
        (by simp))
  have hProperF :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_13_counterexampleF := by
    -- Unfolding `helperForLemma_31_0_13_counterexampleF` recovers the singleton indicator.
    simpa [helperForLemma_31_0_13_counterexampleF] using hIndicator.2
  have hClosedF :
      ClosedConvexFunction helperForLemma_31_0_13_counterexampleF := by
    -- The same singleton-indicator calculation also gives the closedness needed in the header.
    simpa [helperForLemma_31_0_13_counterexampleF] using hIndicator.1
  have hClosedG :
      ClosedERealFunction helperForLemma_31_0_13_counterexampleG := by
    -- The constant-zero function is lower semicontinuous, hence closed in the textbook sense.
    simpa [ClosedERealFunction, helperForLemma_31_0_13_counterexampleG] using
      (lowerSemicontinuous_const :
        LowerSemicontinuous (fun _ : Fin 1 → ℝ => (0 : EReal)))
  have hG_ne_bot :
      ∀ x, helperForLemma_31_0_13_counterexampleG x ≠ (⊥ : EReal) := by
    -- The constant value `0` never equals `-∞`.
    intro x
    simp [helperForLemma_31_0_13_counterexampleG]
  have hdom :
      Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              helperForLemma_31_0_13_counterexampleF ∩
            effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              helperForLemma_31_0_13_counterexampleG) ∨
        Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF) ∩
            effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG)) := by
    -- The origin belongs to the primal effective domains of both counterexample functions.
    left
    refine ⟨(0 : Fin 1 → ℝ), ?_⟩
    constructor
    · simp [effectiveDomain_eq, helperForLemma_31_0_13_counterexampleF, indicatorFunction]
    · simp [effectiveDomain_eq, helperForLemma_31_0_13_counterexampleG]
  have hInfFinite :
      IsFiniteEReal
        (functionInfimumEReal
          (fun x : Fin 1 → ℝ =>
            helperForLemma_31_0_13_counterexampleF x -
              helperForLemma_31_0_13_counterexampleG x)) := by
    -- The explicit infimum computation reduces the finiteness check to the value `0`.
    rw [helperForLemma_31_0_13_counterexample_primalInfimum_eq_zero]
    simp [IsFiniteEReal]
  exact ⟨hProperF, hClosedF, hClosedG, hG_ne_bot, hdom, hInfFinite⟩

/-- Helper for Lemma 31.0.13: the current theorem header admits an explicit one-dimensional
counterexample where the directional-derivative condition holds but no Kuhn-Tucker vector
exists. -/
lemma helperForLemma_31_0_13_currentHeader_hasCounterexample :
    ∃ f g : (Fin 1 → ℝ) → EReal,
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
        ClosedConvexFunction f ∧
        ClosedERealFunction g ∧
        (∀ x, g x ≠ (⊥ : EReal)) ∧
        (Set.Nonempty
            (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f ∩
              effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) g) ∨
          Set.Nonempty
            (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 f) ∩
              effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 g))) ∧
        IsFiniteEReal (functionInfimumEReal (fun x => f x - g x)) ∧
        (∀ y : Fin 1 → ℝ,
          upperDirectionalDerivativeAt
              (translatedDifferenceValueFunction (n := 1) f g)
              (0 : Fin 1 → ℝ) y > (⊥ : EReal)) ∧
        ¬ ∃ xStar : Fin 1 → ℝ,
            fenchelConjugate 1 g xStar - fenchelConjugate 1 f xStar =
                (⨆ z : Fin 1 → ℝ, fenchelConjugate 1 g z - fenchelConjugate 1 f z) ∧
              fenchelConjugate 1 g xStar - fenchelConjugate 1 f xStar =
                functionInfimumEReal (fun x => f x - g x) := by
  -- Use the explicit indicator/zero pair as the witness satisfying the current header.
  refine ⟨helperForLemma_31_0_13_counterexampleF, helperForLemma_31_0_13_counterexampleG, ?_⟩
  rcases helperForLemma_31_0_13_counterexample_satisfies_currentHypotheses with
    ⟨hProperF, hClosedF, hClosedG, hG_ne_bot, hdom, hInfFinite⟩
  refine ⟨hProperF, hClosedF, hClosedG, hG_ne_bot, hdom, hInfFinite, ?_, ?_⟩
  · -- The translated value function is constant zero, so every directional derivative is finite.
    exact helperForLemma_31_0_13_counterexample_directionalCondition_holds
  · -- The dual supremum is `⊤` while the primal infimum is `0`, ruling out any Kuhn-Tucker
    -- vector under the current statement.
    exact helperForLemma_31_0_13_counterexample_no_kuhnTuckerVector

/-- Helper for Lemma 31.0.13: the singleton-indicator self-pair `f = g = δ_{ {0} }` does not
have finite primal infimum. Away from the origin, the raw difference is `⊤ - ⊤ = ⊥`, so the
infimum of `x ↦ f x - g x` is `⊥`. -/
lemma helperForLemma_31_0_13_indicatorSelfPair_primalInfimum_eq_bot :
    functionInfimumEReal
        (fun x : Fin 1 → ℝ =>
          helperForLemma_31_0_13_counterexampleF x -
            helperForLemma_31_0_13_counterexampleF x) =
      (⊥ : EReal) := by
  rw [functionInfimumEReal]
  apply le_antisymm
  · let xOne : Fin 1 → ℝ := fun _ : Fin 1 => (1 : ℝ)
    -- Evaluating the infimum at a nonzero point already produces the value `⊥`.
    calc
      (⨅ x : Fin 1 → ℝ,
        helperForLemma_31_0_13_counterexampleF x -
          helperForLemma_31_0_13_counterexampleF x) ≤
          helperForLemma_31_0_13_counterexampleF xOne -
            helperForLemma_31_0_13_counterexampleF xOne := by
        exact iInf_le _ xOne
      _ = (⊥ : EReal) := by
        have hxOne : xOne ≠ (0 : Fin 1 → ℝ) := by
          -- The constant-one vector is visibly not the origin.
          intro h
          have hOne := congrArg (fun v : Fin 1 → ℝ => v 0) h
          norm_num at hOne
        simp [xOne, helperForLemma_31_0_13_counterexampleF, indicatorFunction, hxOne]
  · -- Every `EReal` is bounded below by `⊥`.
    exact bot_le

/-- Helper for Lemma 31.0.13: consequently, the singleton-indicator self-pair cannot satisfy the
extra Lean-side hypothesis `hInfFinite`; this route cannot witness failure of the current header. -/
lemma helperForLemma_31_0_13_indicatorSelfPair_not_hInfFinite :
    ¬ IsFiniteEReal
        (functionInfimumEReal
          (fun x : Fin 1 → ℝ =>
            helperForLemma_31_0_13_counterexampleF x -
              helperForLemma_31_0_13_counterexampleF x)) := by
  -- Rewriting the infimum to `⊥` makes the non-finiteness immediate.
  rw [helperForLemma_31_0_13_indicatorSelfPair_primalInfimum_eq_bot]
  simp [IsFiniteEReal]

/-- Helper for Lemma 31.0.13: the same singleton-indicator self-pair still has raw dual supremum
`0`, because both Fenchel conjugates are the constant-zero function. The failure comes only from
the primal-infimum side, not from the dual supremum. -/
lemma helperForLemma_31_0_13_indicatorSelfPair_dualSup_eq_zero :
    (⨆ xStar : Fin 1 → ℝ,
      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar -
        fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar) =
      (0 : EReal) := by
  have hConj :
      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF =
        (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
    -- Chapter 16 identifies the conjugate of the singleton indicator with the constant-zero map.
    simpa [helperForLemma_31_0_13_counterexampleF] using
      (section16_fenchelConjugate_indicator_singleton_zero (n := 1))
  -- After rewriting both conjugates to `0`, the supremum becomes the constant value `0`.
  rw [hConj]
  simp

/-- Helper for Lemma 31.0.13: the strengthened counterexample uses the one-dimensional quadratic
self-pair `q(x) = (x 0)^2`. -/
noncomputable def helperForLemma_31_0_13_quadraticSelfPairFunction :
    (Fin 1 → ℝ) → EReal :=
  fun x => (((x 0)^2 : ℝ) : EReal)

/-- Helper for Lemma 31.0.13: the quadratic self-pair has primal infimum `0`, because the pointwise
difference `q - q` vanishes everywhere. -/
lemma helperForLemma_31_0_13_quadraticSelfPair_primalInfimum_eq_zero :
    functionInfimumEReal
        (fun x : Fin 1 → ℝ =>
          helperForLemma_31_0_13_quadraticSelfPairFunction x -
            helperForLemma_31_0_13_quadraticSelfPairFunction x) =
      (0 : EReal) := by
  -- Rewrite the entire infimum family to the constant-zero function.
  have hPointwise :
      (fun x : Fin 1 → ℝ =>
        helperForLemma_31_0_13_quadraticSelfPairFunction x -
          helperForLemma_31_0_13_quadraticSelfPairFunction x) =
        fun _ : Fin 1 → ℝ => (0 : EReal) := by
    funext x
    have hx_ne_top :
        helperForLemma_31_0_13_quadraticSelfPairFunction x ≠ (⊤ : EReal) := by
      exact EReal.coe_ne_top ((x 0)^2)
    have hx_ne_bot :
        helperForLemma_31_0_13_quadraticSelfPairFunction x ≠ (⊥ : EReal) := by
      exact EReal.coe_ne_bot ((x 0)^2)
    simpa using EReal.sub_self hx_ne_top hx_ne_bot
  -- The infimum of the constant-zero family is `0`.
  rw [functionInfimumEReal, hPointwise]
  simp

/-- Helper for Lemma 31.0.13: the quadratic self-pair has dual supremum `0`, attained at the
origin, because the dual objective is pointwise `q⋆ - q⋆ ≤ 0`. -/
lemma helperForLemma_31_0_13_quadraticSelfPair_dualSup_eq_zero :
    (⨆ xStar : Fin 1 → ℝ,
      fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction xStar -
        fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction xStar) =
      (0 : EReal) := by
  have hConjZero :
      fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0 = (0 : EReal) := by
    -- The earlier quadratic-conjugate computation already evaluates the origin exactly.
    simpa [helperForLemma_31_0_13_quadraticSelfPairFunction] using
      helperForLemma_31_0_12_counterexampleSquareFunction_fenchelConjugate_at_zero
  have hAtZero :
      fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0 -
          fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0 =
        (0 : EReal) := by
    -- At the origin both conjugate values are the same finite real.
    rw [hConjZero]
    simp
  apply le_antisymm
  · -- Every pointwise self-difference is at most `0`.
    refine iSup_le ?_
    intro xStar
    exact EReal.sub_self_le_zero
  · -- The origin witness already reaches the value `0`.
    calc
      (0 : EReal) =
          fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0 -
            fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0 :=
        hAtZero.symm
      _ ≤ ⨆ xStar : Fin 1 → ℝ,
            fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction xStar -
              fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction xStar := by
        exact le_iSup
          (fun xStar : Fin 1 → ℝ =>
            fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction xStar -
              fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction xStar)
          0

/-- Helper for Lemma 31.0.13: the quadratic self-pair satisfies every strengthened hypothesis in
the current Lean header, including finiteness of the primal infimum and dual supremum. -/
lemma helperForLemma_31_0_13_quadraticSelfPair_satisfies_strengthenedHypotheses :
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_13_quadraticSelfPairFunction ∧
      ClosedConvexFunction helperForLemma_31_0_13_quadraticSelfPairFunction ∧
      ClosedERealFunction helperForLemma_31_0_13_quadraticSelfPairFunction ∧
      (∀ x, helperForLemma_31_0_13_quadraticSelfPairFunction x ≠ (⊥ : EReal)) ∧
      (Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              helperForLemma_31_0_13_quadraticSelfPairFunction ∩
            effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              helperForLemma_31_0_13_quadraticSelfPairFunction) ∨
        Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction) ∩
            effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction))) ∧
      IsFiniteEReal
        (functionInfimumEReal
          (fun x : Fin 1 → ℝ =>
            helperForLemma_31_0_13_quadraticSelfPairFunction x -
              helperForLemma_31_0_13_quadraticSelfPairFunction x)) ∧
      IsFiniteEReal
        (⨆ z : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction z -
            fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction z) := by
  rcases helperForLemma_31_0_12_counterexampleSquareFunction_closed_and_proper with
    ⟨hClosedQ, hProperQ⟩
  have hQ_ne_bot :
      ∀ x, helperForLemma_31_0_13_quadraticSelfPairFunction x ≠ (⊥ : EReal) := by
    -- The quadratic self-pair only takes finite real values.
    intro x
    exact EReal.coe_ne_bot ((x 0)^2)
  have hDom :
      Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              helperForLemma_31_0_13_quadraticSelfPairFunction ∩
            effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              helperForLemma_31_0_13_quadraticSelfPairFunction) ∨
        Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction) ∩
            effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction)) := by
    -- The origin lies in the primal effective domain of the quadratic.
    left
    refine ⟨(0 : Fin 1 → ℝ), ?_⟩
    constructor <;> rw [effectiveDomain_eq] <;> simp [helperForLemma_31_0_13_quadraticSelfPairFunction]
  have hInfFinite :
      IsFiniteEReal
        (functionInfimumEReal
          (fun x : Fin 1 → ℝ =>
            helperForLemma_31_0_13_quadraticSelfPairFunction x -
              helperForLemma_31_0_13_quadraticSelfPairFunction x)) := by
    -- The explicit infimum computation identifies the value as `0`.
    rw [helperForLemma_31_0_13_quadraticSelfPair_primalInfimum_eq_zero]
    simp [IsFiniteEReal]
  have hDualFinite :
      IsFiniteEReal
        (⨆ z : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction z -
            fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction z) := by
    -- The same is true for the dual supremum, again because it is exactly `0`.
    rw [helperForLemma_31_0_13_quadraticSelfPair_dualSup_eq_zero]
    simp [IsFiniteEReal]
  exact ⟨hProperQ, hClosedQ, hClosedQ.2, hQ_ne_bot, hDom, hInfFinite, hDualFinite⟩

/-- Helper for Lemma 31.0.13: the quadratic self-pair makes the left-hand Kuhn-Tucker existence
clause true, already with the witness `xStar = 0`. -/
lemma helperForLemma_31_0_13_quadraticSelfPair_leftSide_holds :
    ∃ xStar : Fin 1 → ℝ,
      fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction xStar -
          fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction xStar =
            (⨆ z : Fin 1 → ℝ,
              fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction z -
                fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction z) ∧
        fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction xStar -
            fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction xStar =
          functionInfimumEReal
            (fun x : Fin 1 → ℝ =>
              helperForLemma_31_0_13_quadraticSelfPairFunction x -
                helperForLemma_31_0_13_quadraticSelfPairFunction x) := by
  refine ⟨0, ?_, ?_⟩
  · -- Both the attained dual value and the dual supremum compute to `0`.
    have hConjZero :
        fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0 = (0 : EReal) := by
      simpa [helperForLemma_31_0_13_quadraticSelfPairFunction] using
        helperForLemma_31_0_12_counterexampleSquareFunction_fenchelConjugate_at_zero
    calc
      fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0 -
          fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0
          = (0 : EReal) := by rw [hConjZero]; simp
      _ =
          (⨆ z : Fin 1 → ℝ,
            fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction z -
              fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction z) := by
        symm
        exact helperForLemma_31_0_13_quadraticSelfPair_dualSup_eq_zero
  · -- The same attained value also matches the primal infimum.
    have hConjZero :
        fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0 = (0 : EReal) := by
      simpa [helperForLemma_31_0_13_quadraticSelfPairFunction] using
        helperForLemma_31_0_12_counterexampleSquareFunction_fenchelConjugate_at_zero
    calc
      fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0 -
          fenchelConjugate 1 helperForLemma_31_0_13_quadraticSelfPairFunction 0
          = (0 : EReal) := by rw [hConjZero]; simp
      _ =
          functionInfimumEReal
            (fun x : Fin 1 → ℝ =>
              helperForLemma_31_0_13_quadraticSelfPairFunction x -
                helperForLemma_31_0_13_quadraticSelfPairFunction x) := by
        symm
        exact helperForLemma_31_0_13_quadraticSelfPair_primalInfimum_eq_zero

/-- Helper for Lemma 31.0.13: at the origin, the translated value function of the quadratic
self-pair is still the primal infimum `0`. -/
lemma helperForLemma_31_0_13_quadraticSelfPair_translatedValue_eq_zero_at_zero :
    translatedDifferenceValueFunction
        (n := 1) helperForLemma_31_0_13_quadraticSelfPairFunction
        helperForLemma_31_0_13_quadraticSelfPairFunction
        (0 : Fin 1 → ℝ) =
      (0 : EReal) := by
  -- Evaluating the translated value at `0` recovers the already computed primal infimum.
  calc
    translatedDifferenceValueFunction
        (n := 1) helperForLemma_31_0_13_quadraticSelfPairFunction
        helperForLemma_31_0_13_quadraticSelfPairFunction
        (0 : Fin 1 → ℝ) =
      functionInfimumEReal
        (fun x : Fin 1 → ℝ =>
          helperForLemma_31_0_13_quadraticSelfPairFunction x -
            helperForLemma_31_0_13_quadraticSelfPairFunction x) :=
      helperForLemma_31_0_12_translatedDifferenceValueFunction_at_zero_eq_functionInfimum
        (n := 1) helperForLemma_31_0_13_quadraticSelfPairFunction
          helperForLemma_31_0_13_quadraticSelfPairFunction
    _ = (0 : EReal) :=
      helperForLemma_31_0_13_quadraticSelfPair_primalInfimum_eq_zero

/-- Helper for Lemma 31.0.13: if the translation vector `u` is nonzero, then the quadratic
self-pair integrand `x ↦ q(x) - q(x + u)` has no real lower bound. -/
lemma helperForLemma_31_0_13_quadraticSelfPair_differenceHasNoRealLowerBound_of_ne_zero
    (u : Fin 1 → ℝ) (hu : u ≠ 0) :
    ¬ HasRealLowerBound
      (fun x : Fin 1 → ℝ =>
        helperForLemma_31_0_13_quadraticSelfPairFunction x -
          helperForLemma_31_0_13_quadraticSelfPairFunction (x + u)) := by
  have hu0 : u 0 ≠ 0 := by
    -- In `Fin 1`, a nonzero vector must have nonzero sole coordinate.
    intro hu0
    apply hu
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using hu0
  intro hLower
  rcases hLower with ⟨m, hm⟩
  let a : ℝ := u 0
  let t : ℝ := (|m| + 1) / (2 * a)
  let x : Fin 1 → ℝ := fun _ => t
  have hx_le := hm x
  have htwo_a_mul_t : 2 * a * t = |m| + 1 := by
    -- The chosen test point normalizes the nonzero affine slope to the size `|m| + 1`.
    have ha_ne : a ≠ 0 := by
      simpa [a] using hu0
    dsimp [t]
    field_simp [ha_ne]
  have hx_eval :
      (fun x : Fin 1 → ℝ =>
        helperForLemma_31_0_13_quadraticSelfPairFunction x -
          helperForLemma_31_0_13_quadraticSelfPairFunction (x + u)) x =
        (((-(|m| + 1) - a^2 : ℝ)) : EReal) := by
    -- In one dimension the translated difference is the affine function `-2 a x - a^2`.
    have hreal :
        (x 0)^2 - ((x + u) 0)^2 = -(|m| + 1) - a^2 := by
      calc
        (x 0)^2 - ((x + u) 0)^2
            = t^2 - (t + a)^2 := by
              simp [x, a]
        _ = -(2 * a * t) - a^2 := by ring
        _ = -(|m| + 1) - a^2 := by rw [htwo_a_mul_t]
    have hreal_ereal :
        ((((x 0)^2 - ((x + u) 0)^2 : ℝ)) : EReal) =
          (((-(|m| + 1) - a^2 : ℝ)) : EReal) := by
      exact_mod_cast hreal
    simpa [helperForLemma_31_0_13_quadraticSelfPairFunction, EReal.coe_sub] using hreal_ereal
  have hx_le' : (m : EReal) ≤ (((-(|m| + 1) - a^2 : ℝ)) : EReal) := by
    -- Evaluate the lower-bound inequality at the specifically chosen test point.
    simpa [a, hx_eval] using hx_le
  have hx_real : m ≤ -(|m| + 1) - a^2 := by
    exact_mod_cast hx_le'
  have hstrict : -(|m| + 1) - a^2 < m := by
    -- The sampled value is strictly below `-|m|`, hence strictly below `m`.
    nlinarith [neg_abs_le m, sq_nonneg a]
  exact (not_le_of_gt hstrict) hx_real

/-- Helper for Lemma 31.0.13: away from the origin, the translated value function of the
quadratic self-pair collapses to `⊥`. -/
lemma helperForLemma_31_0_13_quadraticSelfPair_translatedValue_eq_bot_of_ne_zero
    (u : Fin 1 → ℝ) (hu : u ≠ 0) :
    translatedDifferenceValueFunction
        (n := 1) helperForLemma_31_0_13_quadraticSelfPairFunction
        helperForLemma_31_0_13_quadraticSelfPairFunction u =
      (⊥ : EReal) := by
  -- A non-bottom infimum would contradict the explicit absence of any real lower bound.
  by_contra hne
  exact
    helperForLemma_31_0_13_quadraticSelfPair_differenceHasNoRealLowerBound_of_ne_zero u hu <|
      (helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot _).2 <|
        by
          simpa [translatedDifferenceValueFunction, functionInfimumEReal,
            helperForLemma_31_0_13_quadraticSelfPairFunction] using hne

/-- Helper for Lemma 31.0.13: along the direction `y = (1)`, every positive-step directional
difference quotient of the quadratic self-pair equals `⊥`. -/
lemma helperForLemma_31_0_13_quadraticSelfPair_directionalDifferenceQuotient_eq_bot
    {t : ℝ} (ht : 0 < t) :
    directionalDifferenceQuotientAt
        (translatedDifferenceValueFunction
          (n := 1) helperForLemma_31_0_13_quadraticSelfPairFunction
          helperForLemma_31_0_13_quadraticSelfPairFunction)
        (0 : Fin 1 → ℝ) (fun _ : Fin 1 => (1 : ℝ)) t =
      (⊥ : EReal) := by
  have hStep_ne_zero : t • (fun _ : Fin 1 => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
    -- A positive scalar multiple of the constant-one vector is still nonzero.
    intro hZero
    have hCoord := congrArg (fun v : Fin 1 → ℝ => v 0) hZero
    simp [ht.ne', Pi.smul_apply] at hCoord
  have hAtStep :
      translatedDifferenceValueFunction
          (n := 1) helperForLemma_31_0_13_quadraticSelfPairFunction
          helperForLemma_31_0_13_quadraticSelfPairFunction
          (t • (fun _ : Fin 1 => (1 : ℝ))) =
        (⊥ : EReal) := by
    exact
      helperForLemma_31_0_13_quadraticSelfPair_translatedValue_eq_bot_of_ne_zero
        (t • (fun _ : Fin 1 => (1 : ℝ))) hStep_ne_zero
  have hAtZero :
      translatedDifferenceValueFunction
          (n := 1) helperForLemma_31_0_13_quadraticSelfPairFunction
          helperForLemma_31_0_13_quadraticSelfPairFunction
          (0 : Fin 1 → ℝ) =
        (0 : EReal) :=
    helperForLemma_31_0_13_quadraticSelfPair_translatedValue_eq_zero_at_zero
  -- The numerator is `⊥ - 0 = ⊥`, so dividing by a positive real keeps the value at `⊥`.
  have htE : (0 : EReal) < (t : EReal) := by
    exact_mod_cast ht
  simpa [directionalDifferenceQuotientAt, hAtStep, hAtZero] using
    (EReal.bot_div_of_pos_ne_top htE (by simp : (t : EReal) ≠ (⊤ : EReal)))

/-- Helper for Lemma 31.0.13: the quadratic self-pair has upper directional derivative `⊥` in
the direction `y = (1)`, so the theorem's right-hand clause fails. -/
lemma helperForLemma_31_0_13_quadraticSelfPair_directionalDerivative_eq_bot :
    upperDirectionalDerivativeAt
        (translatedDifferenceValueFunction
          (n := 1) helperForLemma_31_0_13_quadraticSelfPairFunction
          helperForLemma_31_0_13_quadraticSelfPairFunction)
        (0 : Fin 1 → ℝ) (fun _ : Fin 1 => (1 : ℝ)) =
      (⊥ : EReal) := by
  let p := translatedDifferenceValueFunction
    (n := 1) helperForLemma_31_0_13_quadraticSelfPairFunction
    helperForLemma_31_0_13_quadraticSelfPairFunction
  let yOne : Fin 1 → ℝ := fun _ => (1 : ℝ)
  have hmono :
      MonotoneOn (directionalDifferenceQuotientAt p (0 : Fin 1 → ℝ) yOne)
        (Set.Ioi (0 : ℝ)) := by
    -- The positive-step quotients are all the same value `⊥`.
    intro s hs t ht hst
    have hs_bot :
        directionalDifferenceQuotientAt p (0 : Fin 1 → ℝ) yOne s = (⊥ : EReal) :=
      helperForLemma_31_0_13_quadraticSelfPair_directionalDifferenceQuotient_eq_bot
        (t := s) hs
    have ht_bot :
        directionalDifferenceQuotientAt p (0 : Fin 1 → ℝ) yOne t = (⊥ : EReal) :=
      helperForLemma_31_0_13_quadraticSelfPair_directionalDifferenceQuotient_eq_bot
        (t := t) ht
    rw [hs_bot, ht_bot]
  rw [helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients p
    (0 : Fin 1 → ℝ) yOne hmono]
  have hImage :
      (Set.Ioi (0 : ℝ)).image
          (fun t : ℝ => directionalDifferenceQuotientAt p (0 : Fin 1 → ℝ) yOne t) =
        ({⊥} : Set EReal) := by
    -- Every positive step contributes exactly the value `⊥`, and `t = 1` supplies membership.
    ext q
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hbot :
          directionalDifferenceQuotientAt p (0 : Fin 1 → ℝ) yOne t = (⊥ : EReal) := by
        simpa [p, yOne] using
          helperForLemma_31_0_13_quadraticSelfPair_directionalDifferenceQuotient_eq_bot
            (t := t) ht
      simpa [hbot]
    · intro hq
      have hq' : q = (⊥ : EReal) := by
        simpa using hq
      refine ⟨1, by norm_num, ?_⟩
      rw [hq']
      simpa [p, yOne] using
        helperForLemma_31_0_13_quadraticSelfPair_directionalDifferenceQuotient_eq_bot
          (t := (1 : ℝ)) (by norm_num : 0 < (1 : ℝ))
  rw [hImage]
  simp

-- Proof sketch: stay in the convex/closed setting inherited from `Lemma 31.0.12`, use that
-- lemma to identify the dual supremum with the translated value function at `u = 0`, and then
-- apply the Chapter 23 directional-derivative criterion to characterize when the supremum is
-- attained by a Kuhn-Tucker vector.
/-- Lemma 31.0.13 (Existence of Kuhn-Tucker Vectors): in the Fenchel-duality setting of §31, let
`f : ℝ^n → ℝ ∪ {+∞}` be proper convex and let `g : ℝ^n → ℝ ∪ {-∞}` be proper concave. Let
`F` be the bundled translated perturbation `(u, x) ↦ f x - g (x + u)` and
`p(u) = inf_x (f x - g (x + u))`. If `inf_x (f x - g x)` is finite, then there exists a
Kuhn-Tucker vector for `F` if and only if every origin directional derivative of `p` is
strictly above `-∞`. -/
lemma exists_kuhn_tucker_vector_iff_translatedDifferenceValueFunction_directionalDerivative_gt_bot
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hInfFinite : IsFiniteEReal (functionInfimumEReal (fun x => f x - g x))) :
    let F := helperForTheorem_31_2_translatedDifference_bifunction f g hf hg
    let p := translatedDifferenceValueFunction (n := n) f g
    (∃ uStar : Fin n → ℝ, IsKuhnTuckerVector F uStar) ↔
      ∀ y : Fin n → ℝ,
        upperDirectionalDerivativeAt p (0 : Fin n → ℝ) y > (⊥ : EReal) := by
  dsimp
  let F := helperForTheorem_31_2_translatedDifference_bifunction f g hf hg
  let p := translatedDifferenceValueFunction (n := n) f g
  have hfinite :
      IsFiniteEReal (generalizedConvexProgramOptimalValue F) := by
    have hOptEq :
        generalizedConvexProgramOptimalValue F =
          functionInfimumEReal (fun x => f x - g x) := by
      calc
        generalizedConvexProgramOptimalValue F =
            generalizedConvexProgramPerturbationFunction F (0 : Fin n → ℝ) :=
          helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero F
        _ = translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) := by
            symm
            exact
              helperForLemma_31_0_10_translatedDifferenceValue_eq_generalizedPerturbation_apply
                (f := f) (g := g) (hf := hf) (hg := hg) (u := 0)
        _ = functionInfimumEReal (fun x => f x - g x) :=
          helperForLemma_31_0_12_translatedDifferenceValueFunction_at_zero_eq_functionInfimum
            f g
    simpa [hOptEq] using hInfFinite
  constructor
  · rintro ⟨uStar, huStar⟩ y
    have hMinorRaw :
        ((dotProduct (-y) uStar : ℝ) : EReal) ≤
          generalizedConvexProgramOriginDirectionalDerivative F (-(-y)) :=
      (helperForCorollary_6_29_1_kuhnTucker_iff_negatedDirectionalDerivative_minorant
        F hfinite uStar).1 huStar (-y)
    have hMinor :
        ((dotProduct (-y) uStar : ℝ) : EReal) ≤
          generalizedConvexProgramOriginDirectionalDerivative F y := by
      simpa using hMinorRaw
    have hBotLt :
        (⊥ : EReal) < ((dotProduct (-y) uStar : ℝ) : EReal) :=
      EReal.bot_lt_coe (dotProduct (-y) uStar)
    exact lt_of_lt_of_le hBotLt <|
      by
        simpa [p, F, generalizedConvexProgramOriginDirectionalDerivative,
          helperForTheorem_31_2_translatedDifferenceValue_eq_generalizedPerturbation f g hf hg]
          using hMinor
  · intro hDir
    by_contra hNoKT
    rcases
        (generalizedConvexProgram_noKuhnTuckerVector_iff_exists_bilateralDirectionalDerivative_eq_bot
          F hfinite).1 hNoKT with
      ⟨u, hRight, _hLeft⟩
    have hBot :
        generalizedConvexProgramOriginDirectionalDerivative F u = (⊥ : EReal) :=
      helperForCorollary_6_29_2_originDirectionalDerivative_eq_bot_of_rightLimit
        F hfinite u hRight
    have hu := hDir u
    rw [show upperDirectionalDerivativeAt p (0 : Fin n → ℝ) u = (⊥ : EReal) by
      simpa [p, F, generalizedConvexProgramOriginDirectionalDerivative,
        helperForTheorem_31_2_translatedDifferenceValue_eq_generalizedPerturbation f g hf hg]
        using hBot] at hu
    simp at hu

end Section31
end Chap06
