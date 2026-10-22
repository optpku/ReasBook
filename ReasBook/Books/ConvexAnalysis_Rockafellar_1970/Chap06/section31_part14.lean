/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part13

open scoped Topology

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Helper for Lemma 31.0.12: in the one-dimensional counterexample, the left-hand dual supremum
is exactly `0`. The origin contributes `0`, while every nonzero dual vector contributes `⊥`
because the conjugate of the constant-zero function is the singleton indicator at the origin. -/
lemma helperForLemma_31_0_12_counterexample_dualSup_eq_zero :
    (⨆ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) xStar -
          fenchelConjugate 1 (fun _ => (0 : EReal)) xStar) =
      (0 : EReal) := by
  let dualGap : (Fin 1 → ℝ) → EReal := fun xStar =>
    fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) xStar -
      fenchelConjugate 1 (fun _ => (0 : EReal)) xStar
  have hSquareConjZero :
      fenchelConjugate 1 (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) 0 = (0 : EReal) := by
    -- The previous helper isolates the only finite value needed from the quadratic conjugate.
    exact helperForLemma_31_0_12_counterexampleSquareFunction_fenchelConjugate_at_zero
  have hZeroConj :
      fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)) =
        indicatorFunction ({0} : Set (Fin 1 → ℝ)) := by
    -- The conjugate of the constant-zero function is the singleton indicator at the origin.
    simpa using section16_fenchelConjugate_const_zero (n := 1)
  have hZeroConjAtZero :
      fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)) 0 = (0 : EReal) := by
    -- Evaluating the indicator at the origin removes the exceptional `⊤` branch.
    simpa [indicatorFunction] using congrArg (fun h => h 0) hZeroConj
  have hDualGapAtZero : dualGap 0 = (0 : EReal) := by
    -- The origin gives a concrete lower-bound witness for the supremum.
    change
      fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) 0 -
          fenchelConjugate 1 (fun _ => (0 : EReal)) 0 =
        (0 : EReal)
    rw [hZeroConjAtZero, sub_eq_add_neg, neg_zero, add_zero]
    exact hSquareConjZero
  apply le_antisymm
  · refine iSup_le ?_
    intro xStar
    by_cases hxStar : xStar = 0
    · -- At the origin the dual gap is exactly `0`.
      subst hxStar
      change
        fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) 0 -
            fenchelConjugate 1 (fun _ => (0 : EReal)) 0 ≤
          (0 : EReal)
      rw [hZeroConjAtZero, sub_eq_add_neg, neg_zero, add_zero]
      simpa [EReal.coe_pow] using (show
        fenchelConjugate 1 (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) 0 ≤ (0 : EReal) from
          le_of_eq hSquareConjZero)
    · have hZeroConjAway :
          fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)) xStar = (⊤ : EReal) := by
        -- Away from `0`, the singleton indicator equals `⊤`.
        simpa [indicatorFunction, hxStar] using congrArg (fun h => h xStar) hZeroConj
      -- Subtracting `⊤` collapses the dual gap to `⊥`, so it is certainly at most `0`.
      change
        fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) xStar -
            fenchelConjugate 1 (fun _ => (0 : EReal)) xStar ≤
          (0 : EReal)
      rw [hZeroConjAway]
      simp
  · -- The origin witness already forces `0 ≤ sup dualGap`.
    calc
      (0 : EReal) = dualGap 0 := hDualGapAtZero.symm
      _ ≤ ⨆ xStar : Fin 1 → ℝ, dualGap xStar := le_iSup dualGap 0
      _ =
          (⨆ xStar : Fin 1 → ℝ,
              fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) xStar -
                fenchelConjugate 1 (fun _ => (0 : EReal)) xStar) := by
            rfl

/-- Helper for Lemma 31.0.12: any proof of the current theorem schema specializes to the explicit
counterexample and forces the impossible identity `0 = ⊥`. -/
lemma helperForLemma_31_0_12_targetHeaderSpecializesToZeroEqBot
    (hFenchel :
      ∀ {n : ℕ} (f g : (Fin n → ℝ) → EReal)
        (_hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
        (_hf_closed : ClosedConvexFunction f)
        (_hg_closed : ClosedERealFunction g)
        (_hg_ne_bot : ∀ x, g x ≠ (⊥ : EReal))
        (_hdom :
          Set.Nonempty
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) ∨
            Set.Nonempty
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) ∩
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g))),
        (⨆ xStar : Fin n → ℝ, fenchelConjugate n g xStar - fenchelConjugate n f xStar) =
            Filter.liminf (translatedDifferenceValueFunction (n := n) f g)
              (𝓝 (0 : Fin n → ℝ)) ∧
          Filter.liminf (translatedDifferenceValueFunction (n := n) f g) (𝓝 (0 : Fin n → ℝ)) ≤
            translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) ∧
          translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) =
            functionInfimumEReal (fun x => f x - g x)) :
    (0 : EReal) = (⊥ : EReal) := by
  rcases helperForLemma_31_0_12_counterexample_satisfiesTargetHypotheses with
    ⟨hZeroProper, hZeroClosed, hSquareClosed, hSquareNeBot, hDom⟩
  have hSpecialized :
      (⨆ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) xStar -
            fenchelConjugate 1 (fun _ => (0 : EReal)) xStar) =
        Filter.liminf
          (translatedDifferenceValueFunction (n := 1)
            (fun _ => (0 : EReal))
            (fun x => (((x 0)^2 : ℝ) : EReal)))
          (𝓝 (0 : Fin 1 → ℝ)) := by
    -- Specialize the claimed theorem schema to the explicit quadratic/zero witness and keep only
    -- the leading equality, which is the part that fails.
    exact
      (hFenchel (n := 1)
        (fun _ : Fin 1 → ℝ => (0 : EReal))
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal))
        hZeroProper hZeroClosed hSquareClosed hSquareNeBot (Or.inl hDom)).1
  -- The counterexample computes the left side as `0` and the right side as `⊥`.
  calc
    (0 : EReal) =
        (⨆ xStar : Fin 1 → ℝ,
            fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) xStar -
              fenchelConjugate 1 (fun _ => (0 : EReal)) xStar) :=
      helperForLemma_31_0_12_counterexample_dualSup_eq_zero.symm
    _ =
        Filter.liminf
          (translatedDifferenceValueFunction (n := 1)
            (fun _ => (0 : EReal))
            (fun x => (((x 0)^2 : ℝ) : EReal)))
          (𝓝 (0 : Fin 1 → ℝ)) := hSpecialized
    _ = (⊥ : EReal) := helperForLemma_31_0_12_counterexampleLiminf_eq_bot

/-- Helper for Lemma 31.0.12: the one-dimensional quadratic/zero counterexample already falsifies
the leading equality claimed in the target theorem. -/
lemma helperForLemma_31_0_12_counterexampleLeadingEqualityFalse :
    ¬ ((⨆ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) xStar -
            fenchelConjugate 1 (fun _ => (0 : EReal)) xStar) =
        Filter.liminf
          (translatedDifferenceValueFunction (n := 1)
            (fun _ => (0 : EReal))
            (fun x => (((x 0)^2 : ℝ) : EReal)))
          (𝓝 (0 : Fin 1 → ℝ))) := by
  intro hEq
  -- Compute both sides of the specialized equality and compare the resulting constants.
  have hZeroEqBot : (0 : EReal) = (⊥ : EReal) := by
    calc
      (0 : EReal) =
          (⨆ xStar : Fin 1 → ℝ,
              fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) xStar -
                fenchelConjugate 1 (fun _ => (0 : EReal)) xStar) :=
        helperForLemma_31_0_12_counterexample_dualSup_eq_zero.symm
      _ =
          Filter.liminf
            (translatedDifferenceValueFunction (n := 1)
              (fun _ => (0 : EReal))
              (fun x => (((x 0)^2 : ℝ) : EReal)))
            (𝓝 (0 : Fin 1 → ℝ)) := hEq
      _ = (⊥ : EReal) := helperForLemma_31_0_12_counterexampleLiminf_eq_bot
  -- The extended-real constants `0` and `⊥` are distinct.
  have hZeroNeBot : (0 : EReal) ≠ (⊥ : EReal) := by
    simp
  exact hZeroNeBot hZeroEqBot

/-- Helper for Lemma 31.0.12: the one-dimensional quadratic/zero counterexample still satisfies
the valid tail inequalities `liminf p ≤ p(0)` and `p(0) = inf_x (f x - g x)`, so the obstruction
is isolated to the leading equality. -/
lemma helperForLemma_31_0_12_counterexampleTailRelationsHold :
    Filter.liminf
        (translatedDifferenceValueFunction (n := 1)
          (fun _ => (0 : EReal))
          (fun x => (((x 0)^2 : ℝ) : EReal)))
        (𝓝 (0 : Fin 1 → ℝ)) ≤
      translatedDifferenceValueFunction (n := 1)
        (fun _ => (0 : EReal))
        (fun x => (((x 0)^2 : ℝ) : EReal))
        (0 : Fin 1 → ℝ) ∧
      translatedDifferenceValueFunction (n := 1)
        (fun _ => (0 : EReal))
        (fun x => (((x 0)^2 : ℝ) : EReal))
        (0 : Fin 1 → ℝ) =
          functionInfimumEReal
            (fun x : Fin 1 → ℝ =>
              (0 : EReal) - ((((x 0)^2 : ℝ) : EReal))) := by
  rcases helperForLemma_31_0_12_counterexample_tailChain_eq_bot with ⟨hAtZero, hInf⟩
  constructor
  · -- Both sides evaluate to `⊥`, so the liminf inequality is immediate.
    rw [helperForLemma_31_0_12_counterexampleLiminf_eq_bot, hAtZero]
  · -- The value at `0` and the primal infimum share the same explicit counterexample value.
    calc
      translatedDifferenceValueFunction (n := 1)
          (fun _ => (0 : EReal))
          (fun x => (((x 0)^2 : ℝ) : EReal))
          (0 : Fin 1 → ℝ) = (⊥ : EReal) := hAtZero
      _ = functionInfimumEReal
            (fun x : Fin 1 → ℝ =>
              (0 : EReal) - ((((x 0)^2 : ℝ) : EReal))) := hInf.symm

/-- Helper for Lemma 31.0.12: the one-dimensional quadratic/zero counterexample falsifies the
entire displayed conclusion, even though the tail inequalities remain valid there. -/
lemma helperForLemma_31_0_12_counterexampleFullConclusionFalse :
    ¬ ((⨆ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) xStar -
            fenchelConjugate 1 (fun _ => (0 : EReal)) xStar) =
        Filter.liminf
          (translatedDifferenceValueFunction (n := 1)
            (fun _ => (0 : EReal))
            (fun x => (((x 0)^2 : ℝ) : EReal)))
          (𝓝 (0 : Fin 1 → ℝ)) ∧
      Filter.liminf
          (translatedDifferenceValueFunction (n := 1)
            (fun _ => (0 : EReal))
            (fun x => (((x 0)^2 : ℝ) : EReal)))
          (𝓝 (0 : Fin 1 → ℝ)) ≤
        translatedDifferenceValueFunction (n := 1)
          (fun _ => (0 : EReal))
          (fun x => (((x 0)^2 : ℝ) : EReal))
          (0 : Fin 1 → ℝ) ∧
      translatedDifferenceValueFunction (n := 1)
          (fun _ => (0 : EReal))
          (fun x => (((x 0)^2 : ℝ) : EReal))
          (0 : Fin 1 → ℝ) =
        functionInfimumEReal
          (fun x : Fin 1 → ℝ =>
            (0 : EReal) - ((((x 0)^2 : ℝ) : EReal)))) := by
  intro hConclusion
  -- The specialized counterexample keeps the tail valid, so the contradiction comes entirely
  -- from the first conjunct.
  exact helperForLemma_31_0_12_counterexampleLeadingEqualityFalse hConclusion.1

/-- Helper for Lemma 31.0.12: the explicit quadratic/zero counterexample refutes the current
universal theorem schema, so no local proof can exist until the leading equality is repaired. -/
lemma helperForLemma_31_0_12_targetHeaderSchemaIsFalse :
    ¬ ∀ {n : ℕ} (f g : (Fin n → ℝ) → EReal)
        (_hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
        (_hf_closed : ClosedConvexFunction f)
        (_hg_closed : ClosedERealFunction g)
        (_hg_ne_bot : ∀ x, g x ≠ (⊥ : EReal))
        (_hdom :
          Set.Nonempty
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) ∨
            Set.Nonempty
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) ∩
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g))),
        (⨆ xStar : Fin n → ℝ, fenchelConjugate n g xStar - fenchelConjugate n f xStar) =
            Filter.liminf (translatedDifferenceValueFunction (n := n) f g)
              (𝓝 (0 : Fin n → ℝ)) ∧
          Filter.liminf (translatedDifferenceValueFunction (n := n) f g) (𝓝 (0 : Fin n → ℝ)) ≤
            translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) ∧
          translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) =
            functionInfimumEReal (fun x => f x - g x) := by
  rcases helperForLemma_31_0_12_counterexample_satisfiesTargetHypotheses with
    ⟨hZeroProper, hZeroClosed, hSquareClosed, hSquareNeBot, hDom⟩
  intro hFenchel
  have hSpecialized :
      ((⨆ xStar : Fin 1 → ℝ,
            fenchelConjugate 1 (fun x => (((x 0)^2 : ℝ) : EReal)) xStar -
              fenchelConjugate 1 (fun _ => (0 : EReal)) xStar) =
          Filter.liminf
            (translatedDifferenceValueFunction (n := 1)
              (fun _ => (0 : EReal))
              (fun x => (((x 0)^2 : ℝ) : EReal)))
            (𝓝 (0 : Fin 1 → ℝ)) ∧
        Filter.liminf
            (translatedDifferenceValueFunction (n := 1)
              (fun _ => (0 : EReal))
              (fun x => (((x 0)^2 : ℝ) : EReal)))
            (𝓝 (0 : Fin 1 → ℝ)) ≤
          translatedDifferenceValueFunction (n := 1)
            (fun _ => (0 : EReal))
            (fun x => (((x 0)^2 : ℝ) : EReal))
            (0 : Fin 1 → ℝ) ∧
        translatedDifferenceValueFunction (n := 1)
            (fun _ => (0 : EReal))
            (fun x => (((x 0)^2 : ℝ) : EReal))
            (0 : Fin 1 → ℝ) =
          functionInfimumEReal
            (fun x : Fin 1 → ℝ =>
              (0 : EReal) - ((((x 0)^2 : ℝ) : EReal)))) := by
    -- Specialize the claimed universal theorem to the explicit quadratic/zero witness.
    exact
      hFenchel (n := 1)
        (fun _ : Fin 1 → ℝ => (0 : EReal))
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal))
        hZeroProper hZeroClosed hSquareClosed hSquareNeBot (Or.inl hDom)
  -- The specialized full conclusion is impossible even though the tail relations remain valid.
  have _hTailValid :
      Filter.liminf
          (translatedDifferenceValueFunction (n := 1)
            (fun _ => (0 : EReal))
            (fun x => (((x 0)^2 : ℝ) : EReal)))
          (𝓝 (0 : Fin 1 → ℝ)) ≤
        translatedDifferenceValueFunction (n := 1)
          (fun _ => (0 : EReal))
          (fun x => (((x 0)^2 : ℝ) : EReal))
          (0 : Fin 1 → ℝ) ∧
        translatedDifferenceValueFunction (n := 1)
          (fun _ => (0 : EReal))
          (fun x => (((x 0)^2 : ℝ) : EReal))
          (0 : Fin 1 → ℝ) =
          functionInfimumEReal
            (fun x : Fin 1 → ℝ =>
              (0 : EReal) - ((((x 0)^2 : ℝ) : EReal))) :=
    helperForLemma_31_0_12_counterexampleTailRelationsHold
  exact helperForLemma_31_0_12_counterexampleFullConclusionFalse hSpecialized

/-- Helper for Lemma 31.0.12: the direct counterexample to the current theorem header uses the
singleton indicator at the origin as the convex function `f`. -/
noncomputable def helperForLemma_31_0_12_currentHeaderCounterexampleF :
    (Fin 1 → ℝ) → EReal :=
  indicatorFunction ({0} : Set (Fin 1 → ℝ))

/-- Helper for Lemma 31.0.12: the direct counterexample to the current theorem header uses the
quadratic function `x ↦ (x 0)^2` as `g`. -/
noncomputable def helperForLemma_31_0_12_currentHeaderCounterexampleG :
    (Fin 1 → ℝ) → EReal :=
  fun x => (((x 0)^2 : ℝ) : EReal)

/-- Helper for Lemma 31.0.12: the explicit indicator/quadratic pair already satisfies the actual
current theorem hypotheses, so any obstruction must come from the theorem conclusion itself. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexample_satisfiesTargetHypotheses :
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_12_currentHeaderCounterexampleF ∧
      ClosedConvexFunction helperForLemma_31_0_12_currentHeaderCounterexampleF ∧
      ClosedERealFunction helperForLemma_31_0_12_currentHeaderCounterexampleG ∧
      (∀ x, helperForLemma_31_0_12_currentHeaderCounterexampleG x ≠ (⊥ : EReal)) ∧
      (Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              helperForLemma_31_0_12_currentHeaderCounterexampleF ∩
            effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              helperForLemma_31_0_12_currentHeaderCounterexampleG) ∨
        Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 helperForLemma_31_0_12_currentHeaderCounterexampleF) ∩
            effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 helperForLemma_31_0_12_currentHeaderCounterexampleG))) := by
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
        helperForLemma_31_0_12_currentHeaderCounterexampleF := by
    -- Unfold the dedicated counterexample function back to the singleton indicator.
    simpa [helperForLemma_31_0_12_currentHeaderCounterexampleF] using hIndicator.2
  have hClosedF :
      ClosedConvexFunction helperForLemma_31_0_12_currentHeaderCounterexampleF := by
    -- The same singleton-indicator package supplies the closedness clause.
    simpa [helperForLemma_31_0_12_currentHeaderCounterexampleF] using hIndicator.1
  rcases helperForLemma_31_0_12_counterexampleSquareFunction_closed_and_proper with
    ⟨hSquareClosed, _hSquareProper⟩
  have hClosedG :
      ClosedERealFunction helperForLemma_31_0_12_currentHeaderCounterexampleG := by
    -- The quadratic model is already known to be closed from the earlier counterexample helpers.
    simpa [helperForLemma_31_0_12_currentHeaderCounterexampleG] using hSquareClosed.2
  have hG_ne_bot :
      ∀ x, helperForLemma_31_0_12_currentHeaderCounterexampleG x ≠ (⊥ : EReal) := by
    -- The quadratic model only takes real values, so it never reaches `⊥`.
    intro x
    exact EReal.coe_ne_bot ((x 0)^2)
  have hDom :
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
            helperForLemma_31_0_12_currentHeaderCounterexampleF ∩
          effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
            helperForLemma_31_0_12_currentHeaderCounterexampleG) := by
    -- Both model functions are finite at the origin, so the primal effective domains intersect.
    refine ⟨(0 : Fin 1 → ℝ), ?_⟩
    constructor
    · simp [effectiveDomain_eq, helperForLemma_31_0_12_currentHeaderCounterexampleF,
        indicatorFunction]
    · simp [effectiveDomain_eq, helperForLemma_31_0_12_currentHeaderCounterexampleG]
  -- Package the current-header hypotheses in the order used by the specialization lemmas below.
  exact ⟨hProperF, hClosedF, hClosedG, hG_ne_bot, Or.inl hDom⟩

/-- Helper for Lemma 31.0.12: for every dual vector `x⋆`, the affine perturbation
`x ↦ ⟪x, x⋆⟫ - (x 0)^2` is unbounded below on `ℝ^1`. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexample_affineMinusQuadratic_hasNoRealLowerBound
    (xStar : Fin 1 → ℝ) :
    ¬ HasRealLowerBound
      (fun x : Fin 1 → ℝ =>
        (((x ⬝ᵥ xStar : ℝ) : EReal) -
          helperForLemma_31_0_12_currentHeaderCounterexampleG x)) := by
  intro hLower
  rcases hLower with ⟨m, hm⟩
  let t : ℝ := |xStar 0| + |m| + 1
  let x : Fin 1 → ℝ := fun _ => t
  have hx_le := hm x
  have hx_eval :
      (((x ⬝ᵥ xStar : ℝ) : EReal) -
          helperForLemma_31_0_12_currentHeaderCounterexampleG x) =
        (((t * xStar 0 - t^2 : ℝ)) : EReal) := by
    -- In one dimension the affine term is exactly `t * x⋆₀`, and the quadratic term is `t^2`.
    simp [x, t, helperForLemma_31_0_12_currentHeaderCounterexampleG, dotProduct]
  have hx_le' : (m : EReal) ≤ (((t * xStar 0 - t^2 : ℝ)) : EReal) := by
    -- Rewrite the sampled inequality using the explicit one-dimensional evaluation.
    simpa [hx_eval] using hx_le
  have hx_real : m ≤ t * xStar 0 - t^2 := by
    -- This sampled `EReal` inequality is just an ordinary real inequality.
    exact_mod_cast hx_le'
  have ht_nonneg : 0 ≤ t := by
    -- The chosen test point is visibly nonnegative.
    dsimp [t]
    positivity
  have hMul :
      t * xStar 0 ≤ t * |xStar 0| := by
    -- Replacing `x⋆₀` by `|x⋆₀|` only enlarges the linear term because `t ≥ 0`.
    exact mul_le_mul_of_nonneg_left (le_abs_self (xStar 0)) ht_nonneg
  have hExpand :
      t * |xStar 0| - t^2 = -(t * (|m| + 1)) := by
    -- Expanding `t = |x⋆₀| + |m| + 1` isolates a manifestly negative quantity.
    dsimp [t]
    ring
  have hProdGt : |m| < t * (|m| + 1) := by
    -- Since `t ≥ 1`, multiplying by `|m| + 1` pushes strictly past `|m|`.
    have ht_ge_one : 1 ≤ t := by
      dsimp [t]
      nlinarith [abs_nonneg (xStar 0), abs_nonneg m]
    nlinarith [abs_nonneg m, ht_ge_one]
  have hAbsStrict :
      t * |xStar 0| - t^2 < m := by
    -- The explicit expansion is below `-|m|`, hence below `m`.
    rw [hExpand]
    nlinarith [hProdGt, neg_abs_le m]
  have hStrict :
      t * xStar 0 - t^2 < m := by
    -- The original affine term is no larger than the absolute-value majorant just estimated.
    exact lt_of_le_of_lt (sub_le_sub_right hMul _) hAbsStrict
  exact (not_le_of_gt hStrict) hx_real

/-- Helper for Lemma 31.0.12: the concave conjugate of the quadratic counterexample is `⊥`
everywhere, because each affine-minus-quadratic slice is unbounded below. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexample_concaveConjugate_eq_bot
    (xStar : Fin 1 → ℝ) :
    concaveFenchelConjugate helperForLemma_31_0_12_currentHeaderCounterexampleG xStar =
      (⊥ : EReal) := by
  -- Rewrite the concave conjugate as an infimum over affine-minus-quadratic slices.
  rw [helperForLemma_31_0_11_concaveFenchelConjugate_eq_iInf]
  by_contra hne
  -- A non-bottom infimum would produce a real lower bound, contradicting the previous lemma.
  exact
    helperForLemma_31_0_12_currentHeaderCounterexample_affineMinusQuadratic_hasNoRealLowerBound
      xStar <|
      (helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot _).2 <|
        by
          simpa [functionInfimumEReal,
            helperForLemma_31_0_12_currentHeaderCounterexampleG] using hne

/-- Helper for Lemma 31.0.12: the Fenchel conjugate of the singleton indicator counterexample is
the constant-zero function. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexample_indicatorConjugate_eq_zero :
    fenchelConjugate 1 helperForLemma_31_0_12_currentHeaderCounterexampleF =
      (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
  -- This is the standard Chapter 16 conjugacy formula for `δ_{ {0} }`.
  simpa [helperForLemma_31_0_12_currentHeaderCounterexampleF] using
    (section16_fenchelConjugate_indicator_singleton_zero (n := 1))

/-- Helper for Lemma 31.0.12: in the actual current theorem header, the direct indicator/quadratic
counterexample has dual supremum `⊥`. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexample_dualSup_eq_bot :
    (⨆ xStar : Fin 1 → ℝ,
        fenchelDualObjective
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG
          xStar) =
      (⊥ : EReal) := by
  have hDualPointwise :
      ∀ xStar : Fin 1 → ℝ,
        fenchelDualObjective
            helperForLemma_31_0_12_currentHeaderCounterexampleF
            helperForLemma_31_0_12_currentHeaderCounterexampleG
            xStar =
          (⊥ : EReal) := by
    intro xStar
    have hConjFAt :
        fenchelConjugate 1 helperForLemma_31_0_12_currentHeaderCounterexampleF xStar =
          (0 : EReal) := by
      -- Evaluate the constant-zero conjugate identity at the current dual point.
      simpa using congrArg
        (fun h => h xStar)
        helperForLemma_31_0_12_currentHeaderCounterexample_indicatorConjugate_eq_zero
    -- The quadratic concave conjugate is `⊥`, and subtracting `0` leaves `⊥`.
    rw [fenchelDualObjective,
      helperForLemma_31_0_12_currentHeaderCounterexample_concaveConjugate_eq_bot, hConjFAt]
    simp
  apply le_antisymm
  · refine iSup_le ?_
    intro xStar
    simp [hDualPointwise xStar]
  · exact bot_le

/-- Helper for Lemma 31.0.12: for the direct indicator/quadratic counterexample, the translated
value function is the negative square `u ↦ -(u 0)^2`. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexample_translatedValue_eq_negSquare
    (u : Fin 1 → ℝ) :
    translatedDifferenceValueFunction
        (n := 1)
        helperForLemma_31_0_12_currentHeaderCounterexampleF
        helperForLemma_31_0_12_currentHeaderCounterexampleG
        u =
      (((-((u 0)^2) : ℝ) : EReal)) := by
  -- Expand the translated value as an infimum over `x`.
  rw [translatedDifferenceValueFunction, functionInfimumEReal]
  let integrand : (Fin 1 → ℝ) → EReal := fun x =>
    helperForLemma_31_0_12_currentHeaderCounterexampleF x -
      helperForLemma_31_0_12_currentHeaderCounterexampleG (x + u)
  apply le_antisymm
  · -- Sampling the origin gives the explicit upper bound `-(u 0)^2`.
    simpa [integrand, helperForLemma_31_0_12_currentHeaderCounterexampleF,
      helperForLemma_31_0_12_currentHeaderCounterexampleG, indicatorFunction] using
      (iInf_le integrand (0 : Fin 1 → ℝ))
  · -- Every other `x` contributes `⊤`, so the sampled origin value is the infimum.
    refine le_iInf ?_
    intro x
    by_cases hx : x = 0
    · -- At `x = 0` the integrand is exactly the negative square.
      subst hx
      simp [helperForLemma_31_0_12_currentHeaderCounterexampleF,
        helperForLemma_31_0_12_currentHeaderCounterexampleG, indicatorFunction]
    · have hIndicatorTop :
          helperForLemma_31_0_12_currentHeaderCounterexampleF x = (⊤ : EReal) := by
        -- Away from the origin the singleton indicator takes the value `⊤`.
        simp [helperForLemma_31_0_12_currentHeaderCounterexampleF, indicatorFunction, hx]
      have hQuadraticNeTop :
          helperForLemma_31_0_12_currentHeaderCounterexampleG (x + u) ≠ (⊤ : EReal) := by
        -- The quadratic model remains finite at every translated point.
        change ((((x + u) 0)^2 : ℝ) : EReal) ≠ (⊤ : EReal)
        exact EReal.coe_ne_top (((x + u) 0)^2)
      -- Therefore the off-origin integrand is `⊤`, which is certainly above `-(u 0)^2`.
      calc
        (((-((u 0)^2) : ℝ) : EReal)) ≤ (⊤ : EReal) := by simp
        _ =
            helperForLemma_31_0_12_currentHeaderCounterexampleF x -
              helperForLemma_31_0_12_currentHeaderCounterexampleG (x + u) := by
                rw [hIndicatorTop]
                symm
                simpa using (EReal.top_sub hQuadraticNeTop)

/-- Helper for Lemma 31.0.12: the liminf side of the actual current theorem header evaluates to
`0` on the direct indicator/quadratic counterexample. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexample_liminf_eq_zero :
    Filter.liminf
        (translatedDifferenceValueFunction
          (n := 1)
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG)
        (𝓝 (0 : Fin 1 → ℝ)) =
      (0 : EReal) := by
  have hValue :
      translatedDifferenceValueFunction
          (n := 1)
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG =
        fun u : Fin 1 → ℝ => (((-((u 0)^2) : ℝ) : EReal)) := by
    -- Promote the pointwise translated-value computation to a function identity.
    funext u
    exact
      helperForLemma_31_0_12_currentHeaderCounterexample_translatedValue_eq_negSquare u
  rw [hValue]
  have hContReal :
      Continuous (fun u : Fin 1 → ℝ => (-((u 0)^2 : ℝ))) := by
    -- The negative square is an ordinary continuous real-valued map.
    continuity
  have hCont :
      Continuous (fun u : Fin 1 → ℝ => (((-((u 0)^2 : ℝ)) : EReal))) := by
    -- Coercing a continuous real-valued function into `EReal` preserves continuity.
    simpa using
      (EReal.continuous_coe_iff (f := fun u : Fin 1 → ℝ => (-((u 0)^2 : ℝ)))).2 hContReal
  have hTendsto :
      Filter.Tendsto
          (fun u : Fin 1 → ℝ => (((-((u 0)^2 : ℝ)) : EReal)))
          (𝓝 (0 : Fin 1 → ℝ))
          (𝓝 (0 : EReal)) := by
    -- Continuity at the origin gives the required convergence to `0`.
    simpa using
      ((hCont.continuousAt :
        ContinuousAt (fun u : Fin 1 → ℝ => (((-((u 0)^2 : ℝ)) : EReal)))
          (0 : Fin 1 → ℝ)).tendsto)
  -- The liminf of a convergent `EReal`-valued function equals its limit.
  simpa using Filter.Tendsto.liminf_eq hTendsto

/-- Helper for Lemma 31.0.12: the direct indicator/quadratic counterexample evaluates the two
sides of the disputed leading equality to the incompatible constants `⊥` and `0`. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexample_dualSupAndLiminfValues :
    (⨆ xStar : Fin 1 → ℝ,
        fenchelDualObjective
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG
          xStar) =
      (⊥ : EReal) ∧
      Filter.liminf
          (translatedDifferenceValueFunction
            (n := 1)
            helperForLemma_31_0_12_currentHeaderCounterexampleF
            helperForLemma_31_0_12_currentHeaderCounterexampleG)
          (𝓝 (0 : Fin 1 → ℝ)) =
        (0 : EReal) := by
  constructor
  · -- The dual supremum computation was already isolated in the previous helper.
    exact helperForLemma_31_0_12_currentHeaderCounterexample_dualSup_eq_bot
  · -- The liminf computation was already isolated in the previous helper.
    exact helperForLemma_31_0_12_currentHeaderCounterexample_liminf_eq_zero

/-- Helper for Lemma 31.0.12: the valid tail relations `liminf p ≤ p(0)` and
`p(0) = inf_x (f x - g x)` still hold for the direct indicator/quadratic counterexample used
against the current theorem header. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexampleTailRelationsHold :
    Filter.liminf
        (translatedDifferenceValueFunction
          (n := 1)
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG)
        (𝓝 (0 : Fin 1 → ℝ)) ≤
      translatedDifferenceValueFunction
        (n := 1)
        helperForLemma_31_0_12_currentHeaderCounterexampleF
        helperForLemma_31_0_12_currentHeaderCounterexampleG
        (0 : Fin 1 → ℝ) ∧
      translatedDifferenceValueFunction
        (n := 1)
        helperForLemma_31_0_12_currentHeaderCounterexampleF
        helperForLemma_31_0_12_currentHeaderCounterexampleG
        (0 : Fin 1 → ℝ) =
        functionInfimumEReal
          (fun x : Fin 1 → ℝ =>
            helperForLemma_31_0_12_currentHeaderCounterexampleF x -
              helperForLemma_31_0_12_currentHeaderCounterexampleG x) := by
  -- These are exactly the general tail relations from part 13, specialized to the current
  -- indicator/quadratic counterexample.
  exact
    helperForLemma_31_0_12_liminf_tail_relations
      helperForLemma_31_0_12_currentHeaderCounterexampleF
      helperForLemma_31_0_12_currentHeaderCounterexampleG

/-- Helper for Lemma 31.0.12: the direct indicator/quadratic counterexample already falsifies the
leading equality in the actual current theorem header. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexample_dualSup_ne_liminf :
    (⨆ xStar : Fin 1 → ℝ,
        fenchelDualObjective
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG
          xStar) ≠
      Filter.liminf
        (translatedDifferenceValueFunction
          (n := 1)
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG)
        (𝓝 (0 : Fin 1 → ℝ)) := by
  -- Compute the two counterexample values explicitly before comparing them.
  rw [helperForLemma_31_0_12_currentHeaderCounterexample_dualSup_eq_bot,
    helperForLemma_31_0_12_currentHeaderCounterexample_liminf_eq_zero]
  simp

/-- Helper for Lemma 31.0.12: the direct indicator/quadratic counterexample already falsifies the
leading equality in the actual current theorem header. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexampleLeadingEqualityFalse :
    ¬ ((⨆ xStar : Fin 1 → ℝ,
          fenchelDualObjective
            helperForLemma_31_0_12_currentHeaderCounterexampleF
            helperForLemma_31_0_12_currentHeaderCounterexampleG
            xStar) =
        Filter.liminf
          (translatedDifferenceValueFunction
            (n := 1)
            helperForLemma_31_0_12_currentHeaderCounterexampleF
            helperForLemma_31_0_12_currentHeaderCounterexampleG)
          (𝓝 (0 : Fin 1 → ℝ))) := by
  -- Repackage the explicit value computation as a direct disequality.
  exact helperForLemma_31_0_12_currentHeaderCounterexample_dualSup_ne_liminf

/-- Helper for Lemma 31.0.12: for the direct indicator/quadratic counterexample, the full current
theorem conclusion is false even though the tail relations remain valid. -/
lemma helperForLemma_31_0_12_currentHeaderCounterexampleFullConclusionFalse :
    ¬ ((⨆ xStar : Fin 1 → ℝ,
          fenchelDualObjective
            helperForLemma_31_0_12_currentHeaderCounterexampleF
            helperForLemma_31_0_12_currentHeaderCounterexampleG
            xStar) =
        Filter.liminf
          (translatedDifferenceValueFunction
            (n := 1)
            helperForLemma_31_0_12_currentHeaderCounterexampleF
            helperForLemma_31_0_12_currentHeaderCounterexampleG)
          (𝓝 (0 : Fin 1 → ℝ)) ∧
      Filter.liminf
          (translatedDifferenceValueFunction
            (n := 1)
            helperForLemma_31_0_12_currentHeaderCounterexampleF
            helperForLemma_31_0_12_currentHeaderCounterexampleG)
          (𝓝 (0 : Fin 1 → ℝ)) ≤
        translatedDifferenceValueFunction
          (n := 1)
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG
          (0 : Fin 1 → ℝ) ∧
      translatedDifferenceValueFunction
          (n := 1)
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG
          (0 : Fin 1 → ℝ) =
        functionInfimumEReal
          (fun x : Fin 1 → ℝ =>
            helperForLemma_31_0_12_currentHeaderCounterexampleF x -
              helperForLemma_31_0_12_currentHeaderCounterexampleG x)) := by
  intro hConclusion
  have _hTailValid :
      Filter.liminf
          (translatedDifferenceValueFunction
            (n := 1)
            helperForLemma_31_0_12_currentHeaderCounterexampleF
            helperForLemma_31_0_12_currentHeaderCounterexampleG)
          (𝓝 (0 : Fin 1 → ℝ)) ≤
        translatedDifferenceValueFunction
          (n := 1)
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG
          (0 : Fin 1 → ℝ) ∧
        translatedDifferenceValueFunction
          (n := 1)
          helperForLemma_31_0_12_currentHeaderCounterexampleF
          helperForLemma_31_0_12_currentHeaderCounterexampleG
          (0 : Fin 1 → ℝ) =
          functionInfimumEReal
            (fun x : Fin 1 → ℝ =>
              helperForLemma_31_0_12_currentHeaderCounterexampleF x -
                helperForLemma_31_0_12_currentHeaderCounterexampleG x) :=
    -- Keep the valid suffix available explicitly; the contradiction is only in the first conjunct.
    helperForLemma_31_0_12_currentHeaderCounterexampleTailRelationsHold
  exact helperForLemma_31_0_12_currentHeaderCounterexampleLeadingEqualityFalse hConclusion.1

/-- Helper for Lemma 31.0.12: the actual current theorem schema is already refuted by the direct
indicator/quadratic counterexample, so no proof can exist without repairing the statement
upstream. -/
lemma helperForLemma_31_0_12_currentHeaderSchemaIsFalse :
    ¬ ∀ {n : ℕ} (f g : (Fin n → ℝ) → EReal)
        (_hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
        (_hf_closed : ClosedConvexFunction f)
        (_hg_closed : ClosedERealFunction g)
        (_hg_ne_bot : ∀ x, g x ≠ (⊥ : EReal))
        (_hdom :
          Set.Nonempty
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) ∨
            Set.Nonempty
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) ∩
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g))),
        (⨆ xStar : Fin n → ℝ, fenchelDualObjective f g xStar) =
            Filter.liminf (translatedDifferenceValueFunction (n := n) f g)
              (𝓝 (0 : Fin n → ℝ)) ∧
          Filter.liminf (translatedDifferenceValueFunction (n := n) f g) (𝓝 (0 : Fin n → ℝ)) ≤
            translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) ∧
          translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) =
            functionInfimumEReal (fun x => f x - g x) := by
  rcases helperForLemma_31_0_12_currentHeaderCounterexample_satisfiesTargetHypotheses with
    ⟨hProperF, hClosedF, hClosedG, hG_ne_bot, hDom⟩
  intro hFenchel
  have hSpecialized :
      ((⨆ xStar : Fin 1 → ℝ,
            fenchelDualObjective
              helperForLemma_31_0_12_currentHeaderCounterexampleF
              helperForLemma_31_0_12_currentHeaderCounterexampleG
              xStar) =
          Filter.liminf
            (translatedDifferenceValueFunction
              (n := 1)
              helperForLemma_31_0_12_currentHeaderCounterexampleF
              helperForLemma_31_0_12_currentHeaderCounterexampleG)
            (𝓝 (0 : Fin 1 → ℝ)) ∧
        Filter.liminf
            (translatedDifferenceValueFunction
              (n := 1)
              helperForLemma_31_0_12_currentHeaderCounterexampleF
              helperForLemma_31_0_12_currentHeaderCounterexampleG)
            (𝓝 (0 : Fin 1 → ℝ)) ≤
          translatedDifferenceValueFunction
            (n := 1)
            helperForLemma_31_0_12_currentHeaderCounterexampleF
            helperForLemma_31_0_12_currentHeaderCounterexampleG
            (0 : Fin 1 → ℝ) ∧
        translatedDifferenceValueFunction
            (n := 1)
            helperForLemma_31_0_12_currentHeaderCounterexampleF
            helperForLemma_31_0_12_currentHeaderCounterexampleG
            (0 : Fin 1 → ℝ) =
          functionInfimumEReal
            (fun x : Fin 1 → ℝ =>
              helperForLemma_31_0_12_currentHeaderCounterexampleF x -
                helperForLemma_31_0_12_currentHeaderCounterexampleG x)) := by
    -- Specialize the claimed theorem to the explicit indicator/quadratic counterexample and keep
    -- the entire displayed conclusion, which the next helper shows is impossible.
    exact
      hFenchel (n := 1)
        helperForLemma_31_0_12_currentHeaderCounterexampleF
        helperForLemma_31_0_12_currentHeaderCounterexampleG
        hProperF hClosedF hClosedG hG_ne_bot hDom
  exact helperForLemma_31_0_12_currentHeaderCounterexampleFullConclusionFalse hSpecialized

/-- Lemma 31.0.12 (Inequality Between the Dual Objective and `p(u)`): let
`f : ℝ^n → ℝ ∪ {+∞}` be proper convex and let `g : ℝ^n → ℝ ∪ {-∞}` be proper concave. Assume
`f` and `g` are closed, and either `dom f ∩ dom g ≠ ∅` or `dom f⋆ ∩ dom g⋆ ≠ ∅`, encoded here by
the nonemptiness of `effectiveDomain ∩ concaveEffectiveDomain` or of
`effectiveDomain(f⋆) ∩ concaveConjugateEffectiveDomain(g)`. For the translated value function
`p(u) = inf_x (f x - g (x + u))`, represented by `translatedDifferenceValueFunction f g`, one has
`sup_xStar φ(xStar) = liminf_{u → 0} p(u) ≤ p(0) = inf_x (f x - g x)`, where
`φ = fenchelDualObjective f g`. -/
lemma fenchelDualSupremum_eq_liminf_translatedDifferenceValueFunction_le_at_zero {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hclosed : ClosedConvexFunction f ∧ ClosedConcaveFunction g)
    (hdom :
      Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩ concaveEffectiveDomain g) ∨
        Set.Nonempty
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) ∩
            concaveConjugateEffectiveDomain g)) :
    (⨆ xStar : Fin n → ℝ, fenchelDualObjective f g xStar) =
        Filter.liminf (translatedDifferenceValueFunction (n := n) f g) (𝓝 (0 : Fin n → ℝ)) ∧
      Filter.liminf (translatedDifferenceValueFunction (n := n) f g) (𝓝 (0 : Fin n → ℝ)) ≤
        translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) ∧
      translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) =
        functionInfimumEReal (fun x => f x - g x) := by
  let _ := hclosed
  let p : (Fin n → ℝ) → EReal := translatedDifferenceValueFunction (n := n) f g
  let q : (Fin n → ℝ) → EReal := fun u => -(p u)
  have hpConv : ConvexFunction p := by
    simpa [p] using
      helperForTheorem_31_2_translatedDifferenceValue_convexFunction f g hf hg
  have hqConc : ConcaveFunction q := by
    simpa [ConcaveFunction, q] using hpConv
  have hConjEq :
      ∀ xStar : Fin n → ℝ, concaveConjugate q xStar = fenchelDualObjective f g xStar := by
    intro xStar
    calc
      concaveConjugate q xStar
          = (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) + (-q v))) := by
              simpa using
                helperForTheorem_6_30_4_concaveConjugate_eq_iInf (g := q) xStar
      _ = (⨅ v : Fin n → ℝ, (((v ⬝ᵥ xStar : ℝ) : EReal) - q v)) := by
            simp [sub_eq_add_neg]
      _ = concaveFenchelConjugate q xStar := by
            simpa using
              (helperForLemma_31_0_11_concaveFenchelConjugate_eq_iInf (g := q) xStar).symm
      _ = fenchelDualObjective f g xStar := by
            symm
            simpa [p, q] using
              fenchelDualObjective_eq_concaveConjugate_neg_translatedDifferenceValueFunction
                (f := f) (g := g) hf hg xStar
  have hDualSupEqClosure :
      (⨆ xStar : Fin n → ℝ, fenchelDualObjective f g xStar) = convexClosure p (0 : Fin n → ℝ) := by
    have hBi0 :=
      congrFun (concaveConjugate_biconjugate_eq_concaveClosure (g := q) hqConc)
        (0 : Fin n → ℝ)
    have hLeft :
        concaveConjugate (concaveConjugate q) (0 : Fin n → ℝ) =
          -(⨆ xStar : Fin n → ℝ, fenchelDualObjective f g xStar) := by
      calc
        concaveConjugate (concaveConjugate q) (0 : Fin n → ℝ)
            = (⨅ xStar : Fin n → ℝ,
                (((xStar ⬝ᵥ (0 : Fin n → ℝ) : ℝ) : EReal) +
                  (-(concaveConjugate q xStar)))) := by
                simpa using
                  helperForTheorem_6_30_4_concaveConjugate_eq_iInf
                    (g := concaveConjugate q) (0 : Fin n → ℝ)
        _ = (⨅ xStar : Fin n → ℝ, -(concaveConjugate q xStar)) := by
              simp
        _ = (⨅ xStar : Fin n → ℝ, -(fenchelDualObjective f g xStar)) := by
              refine iInf_congr ?_
              intro xStar
              rw [hConjEq xStar]
        _ = -(⨆ xStar : Fin n → ℝ, fenchelDualObjective f g xStar) := by
              have htmp :
                  -(⨅ xStar : Fin n → ℝ, -(fenchelDualObjective f g xStar)) =
                    ⨆ xStar : Fin n → ℝ, fenchelDualObjective f g xStar := by
                simpa using
                  helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg
                    (φ := fun xStar : Fin n → ℝ => -(fenchelDualObjective f g xStar))
              simpa using congrArg Neg.neg htmp
    have hRight : concaveClosure q (0 : Fin n → ℝ) = -(convexClosure p (0 : Fin n → ℝ)) := by
      simp [concaveClosure, convexClosure, p, q]
    have hNegEq :
        -(⨆ xStar : Fin n → ℝ, fenchelDualObjective f g xStar) =
          -(convexClosure p (0 : Fin n → ℝ)) := by
      calc
        -(⨆ xStar : Fin n → ℝ, fenchelDualObjective f g xStar)
            = concaveConjugate (concaveConjugate q) (0 : Fin n → ℝ) := hLeft.symm
        _ = concaveClosure q (0 : Fin n → ℝ) := hBi0
        _ = -(convexClosure p (0 : Fin n → ℝ)) := hRight
    simpa using congrArg Neg.neg hNegEq
  have hpNotExceptional :
      ¬ (p (0 : Fin n → ℝ) = (⊤ : EReal) ∧ convexClosure p (0 : Fin n → ℝ) = (⊥ : EReal)) := by
    intro hBad
    rcases hdom with hPrimal | hDual
    · rcases hPrimal with ⟨x, hx⟩
      have hfx_lt_top : f x < (⊤ : EReal) := by
        have hxDomF : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := hx.1
        simpa [effectiveDomain_eq] using hxDomF
      have hfx_ne_top : f x ≠ (⊤ : EReal) := (lt_top_iff_ne_top).1 hfx_lt_top
      have hnegGx_lt_top : -(g x) < (⊤ : EReal) := by
        have hxDomNegG : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun y => -(g y)) := by
          simpa [concaveEffectiveDomain] using hx.2
        simpa [effectiveDomain_eq] using hxDomNegG
      have hnegGx_ne_top : -(g x) ≠ (⊤ : EReal) := (lt_top_iff_ne_top).1 hnegGx_lt_top
      have hvalue_ne_top : f x - g x ≠ (⊤ : EReal) := by
        simpa [sub_eq_add_neg] using EReal.add_ne_top hfx_ne_top hnegGx_ne_top
      have hp0_le : p (0 : Fin n → ℝ) ≤ f x - g x := by
        simpa [p, translatedDifferenceValueFunction, functionInfimumEReal] using
          (iInf_le (fun y : Fin n → ℝ => f y - g (y + (0 : Fin n → ℝ))) x)
      have htop_le : (⊤ : EReal) ≤ f x - g x := by
        simpa [hBad.1] using hp0_le
      exact hvalue_ne_top (top_unique htop_le)
    · rcases hDual with ⟨xStar, hxStar⟩
      have hFstar_lt_top : fenchelConjugate n f xStar < (⊤ : EReal) := by
        have hxDomFStar :
            xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := hxStar.1
        simpa [effectiveDomain_eq] using hxDomFStar
      have hFstar_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) :=
        (lt_top_iff_ne_top).1 hFstar_lt_top
      have hGstar_ne_bot : concaveFenchelConjugate g xStar ≠ (⊥ : EReal) := by
        have hneg_lt_top : -(concaveFenchelConjugate g xStar) < (⊤ : EReal) := by
          simpa [concaveConjugateEffectiveDomain, effectiveDomain_eq] using hxStar.2
        exact fun hbot =>
          (lt_top_iff_ne_top.mp hneg_lt_top) <| by simpa [hbot]
      have hNegFstar_ne_bot : -(fenchelConjugate n f xStar) ≠ (⊥ : EReal) := by
        exact fun hbot => hFstar_ne_top <| by simpa using hbot
      have hDualAt_ne_bot : fenchelDualObjective f g xStar ≠ (⊥ : EReal) := by
        simpa [fenchelDualObjective, sub_eq_add_neg] using
          add_ne_bot_of_notbot hGstar_ne_bot hNegFstar_ne_bot
      have hSup_ne_bot :
          (⨆ y : Fin n → ℝ, fenchelDualObjective f g y) ≠ (⊥ : EReal) := by
        intro hSupBot
        have hx_le :
            fenchelDualObjective f g xStar ≤ (⊥ : EReal) := by
          rw [← hSupBot]
          exact le_iSup (fun y : Fin n → ℝ => fenchelDualObjective f g y) xStar
        exact hDualAt_ne_bot (le_bot_iff.mp hx_le)
      exact hSup_ne_bot <| by simpa [hDualSupEqClosure] using hBad.2
  have hClosureLiminf :
      convexClosure p (0 : Fin n → ℝ) = Filter.liminf p (𝓝 (0 : Fin n → ℝ)) := by
    exact
      helperForCorollary_6_30_3_convexClosure_eq_liminf_nhds_at_zero_nonexceptional
        (p := p) hpConv hpNotExceptional
  constructor
  · calc
      (⨆ xStar : Fin n → ℝ, fenchelDualObjective f g xStar)
          = convexClosure p (0 : Fin n → ℝ) := hDualSupEqClosure
      _ = Filter.liminf p (𝓝 (0 : Fin n → ℝ)) := hClosureLiminf
      _ = Filter.liminf (translatedDifferenceValueFunction (n := n) f g)
            (𝓝 (0 : Fin n → ℝ)) := by
              simp [p]
  · simpa [p] using helperForLemma_31_0_12_liminf_tail_relations (f := f) (g := g)


end Section31
end Chap06
