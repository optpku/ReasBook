/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part15

open scoped Topology

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

-- Proof sketch: reuse the one-dimensional indicator/zero counterexample from `Lemma 31.0.13`.
-- Its translated value function is identically `0`, so the right-hand side of the uniqueness
-- theorem is true, while the left-hand unique-existence clause fails because there is no
-- Kuhn-Tucker vector at all.
/-- Helper for Lemma 31.0.14: the one-dimensional indicator/zero counterexample makes the
translated value function finite and differentiable at the origin. -/
lemma helperForLemma_31_0_14_counterexample_finite_and_differentiableAt_zero :
    let p := translatedDifferenceValueFunction (n := 1)
      helperForLemma_31_0_13_counterexampleF
      helperForLemma_31_0_13_counterexampleG
    IsFiniteEReal (p (0 : Fin 1 → ℝ)) ∧
      ERealDifferentiableAt p (0 : Fin 1 → ℝ) := by
  dsimp
  have hAtZero :
      translatedDifferenceValueFunction (n := 1)
          helperForLemma_31_0_13_counterexampleF
          helperForLemma_31_0_13_counterexampleG
          (0 : Fin 1 → ℝ) =
        (0 : EReal) :=
    helperForLemma_31_0_13_counterexample_translatedValue_eq_zero (0 : Fin 1 → ℝ)
  have hErrorZero :
      erealGradientErrorQuotient
          (translatedDifferenceValueFunction (n := 1)
            helperForLemma_31_0_13_counterexampleF
            helperForLemma_31_0_13_counterexampleG)
          (0 : Fin 1 → ℝ)
          (0 : Fin 1 → ℝ) =
        fun _ => (0 : ℝ) := by
    -- The translated value function is constant, so the first-order error quotient vanishes.
    funext z
    simp [erealGradientErrorQuotient,
      helperForLemma_31_0_13_counterexample_translatedValue_eq_zero]
  constructor
  · -- The translated value function is constantly `0`, so its value at the origin is finite.
    simp [IsFiniteEReal, hAtZero]
  · -- The same constant-zero computation gives a gradient witness `0` at the origin.
    refine ⟨0, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · -- The value at the origin is `0`, hence in particular not `⊤`.
        rw [hAtZero]
        simp
      · -- The value at the origin is `0`, hence in particular not `⊥`.
        rw [hAtZero]
        simp
      · -- For a constant function the normalized first-order error quotient is identically `0`.
        rw [hErrorZero]
        simpa using
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : Fin 1 → ℝ => (0 : ℝ)) _ _)
    · -- Every point lies in the effective domain because the translated value stays equal to `0`.
      filter_upwards [Filter.univ_mem] with z hz
      constructor
      · simp [effectiveDomain_eq, helperForLemma_31_0_13_counterexample_translatedValue_eq_zero]
      · rw [helperForLemma_31_0_13_counterexample_translatedValue_eq_zero z]
        simp

/-- Helper for Lemma 31.0.14: the same counterexample has no unique Kuhn-Tucker vector because it
has no Kuhn-Tucker vector at all. -/
lemma helperForLemma_31_0_14_counterexample_no_unique_kuhnTuckerVector :
    ¬ ∃! xStar : Fin 1 → ℝ,
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
  intro hUnique
  -- Unique existence implies existence, contradicting the previously computed counterexample.
  exact helperForLemma_31_0_13_counterexample_no_kuhnTuckerVector hUnique.exists

/-- Helper for Lemma 31.0.14: the singleton-indicator/zero counterexample only refutes the
textbook predicate bridge, because its ordinary dual supremum is `⊤` and hence it does not satisfy
the added `hDualSupFinite` hypothesis from the final theorem header. -/
lemma helperForLemma_31_0_14_counterexample_not_hDualSupFinite :
    ¬ IsFiniteEReal
        (⨆ z : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) := by
  -- Reuse the explicit dual-supremum computation from Lemma 31.0.13 and rewrite the finiteness
  -- test to the concrete value `⊤`.
  rw [helperForLemma_31_0_13_counterexample_dualSup_eq_top]
  simp [IsFiniteEReal]

/-- Helper for Lemma 31.0.14: the constant-zero counterexample function is proper concave on the
whole space, so the valid Section 29 uniqueness theorem applies to the bundled translated
perturbation. -/
lemma helperForLemma_31_0_14_counterexampleG_properConcave :
    ProperConcaveFunctionOn (Set.univ : Set (Fin 1 → ℝ))
      helperForLemma_31_0_13_counterexampleG := by
  -- The constant-zero function is both proper convex and proper concave.
  simpa [ProperConcaveFunctionOn, helperForLemma_31_0_13_counterexampleG] using
    (properConvexFunctionOn_const (n := 1) (c := (0 : ℝ)))

/-- Helper for Lemma 31.0.14: at the dual vector `(1)`, the theorem's displayed ordinary
`fenchelConjugate g - fenchelConjugate f` term already disagrees with the actual Fenchel dual
objective `concaveFenchelConjugate g - fenchelConjugate f` on the singleton-indicator/zero
counterexample. -/
lemma helperForLemma_31_0_14_counterexample_dualLanguageMismatch_at_one :
    let xStarOne : Fin 1 → ℝ := fun _ => (1 : ℝ)
    fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStarOne -
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStarOne = (⊤ : EReal) ∧
      fenchelDualObjective
          helperForLemma_31_0_13_counterexampleF
          helperForLemma_31_0_13_counterexampleG xStarOne = (⊥ : EReal) := by
  dsimp
  constructor
  · -- The current textbook predicate uses the ordinary conjugate of `g`, which gives `⊤` here.
    exact helperForLemma_31_0_13_counterexample_dualValue_at_one_eq_top
  · have hone_ne_zero : (fun _ : Fin 1 => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
      -- The constant-one vector is visibly nonzero in dimension `1`.
      intro h
      have h0 := congrArg (fun v : Fin 1 → ℝ => v 0) h
      norm_num at h0
    have hConcaveConj :
        concaveFenchelConjugate helperForLemma_31_0_13_counterexampleG
          (fun _ : Fin 1 => (1 : ℝ)) = (⊥ : EReal) := by
      -- The correct dual objective uses the concave conjugate of `g`, which gives `⊥` away from
      -- the origin for the constant-zero counterexample.
      simp [concaveFenchelConjugate, helperForLemma_31_0_13_counterexampleG,
        section16_fenchelConjugate_const_zero, indicatorFunction, hone_ne_zero]
    have hConvConj :
        fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF
          (fun _ : Fin 1 => (1 : ℝ)) = (0 : EReal) := by
      -- The singleton indicator has constant-zero conjugate.
      simpa [helperForLemma_31_0_13_counterexampleF] using
        congrArg (fun h => h (fun _ : Fin 1 => (1 : ℝ)))
          (section16_fenchelConjugate_indicator_singleton_zero (n := 1))
    -- Combining the two pointwise evaluations computes the bundled dual objective exactly.
    rw [fenchelDualObjective, hConcaveConj, hConvConj]
    simp

/-- Helper for Lemma 31.0.14: the full displayed conclusion already fails for the explicit
indicator/zero counterexample. -/
lemma helperForLemma_31_0_14_counterexample_fullConclusionFalse :
    let p := translatedDifferenceValueFunction (n := 1)
      helperForLemma_31_0_13_counterexampleF
      helperForLemma_31_0_13_counterexampleG
    ¬ (((∃! xStar : Fin 1 → ℝ,
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                  (⨆ z : Fin 1 → ℝ,
                    fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
                      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) ∧
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                  fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                functionInfimumEReal
                  (fun x =>
                    helperForLemma_31_0_13_counterexampleF x -
                      helperForLemma_31_0_13_counterexampleG x)) ↔
          IsFiniteEReal (p (0 : Fin 1 → ℝ)) ∧
            ERealDifferentiableAt p (0 : Fin 1 → ℝ)) ∧
        (∀ hDiff : ERealDifferentiableAt p (0 : Fin 1 → ℝ),
          IsFiniteEReal (p (0 : Fin 1 → ℝ)) →
            ∃! xStar : Fin 1 → ℝ,
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                  fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                    (⨆ z : Fin 1 → ℝ,
                      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
                        fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) ∧
                  fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                    functionInfimumEReal
                      (fun x =>
                        helperForLemma_31_0_13_counterexampleF x -
                          helperForLemma_31_0_13_counterexampleG x) ∧
                xStar = -erealGradientAt hDiff)) := by
  dsimp
  intro hConclusion
  have hFiniteDiff :
      IsFiniteEReal
          ((translatedDifferenceValueFunction (n := 1)
              helperForLemma_31_0_13_counterexampleF
              helperForLemma_31_0_13_counterexampleG) (0 : Fin 1 → ℝ)) ∧
        ERealDifferentiableAt
          (translatedDifferenceValueFunction (n := 1)
            helperForLemma_31_0_13_counterexampleF
            helperForLemma_31_0_13_counterexampleG)
          (0 : Fin 1 → ℝ) := by
    -- This is exactly the specialized right-hand side of the bad `iff`.
    simpa using helperForLemma_31_0_14_counterexample_finite_and_differentiableAt_zero
  have hUnique :
      ∃! xStar : Fin 1 → ℝ,
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
    -- The first conjunct of the displayed conclusion already forces unique existence.
    exact hConclusion.1.mpr hFiniteDiff
  -- The counterexample has no Kuhn-Tucker vector, so even the weakened first conjunct is false.
  exact helperForLemma_31_0_14_counterexample_no_unique_kuhnTuckerVector hUnique

/-- Helper for Lemma 31.0.14: the weaker uniqueness schema without the explicit
`hDualSupFinite` hypothesis is false, because the indicator/zero counterexample makes the
right-hand side true while the unique Kuhn-Tucker clause is false. -/
lemma helperForLemma_31_0_14_targetHeaderSchemaIsFalse :
    ¬ ∀ {m : ℕ} (f g : (Fin m → ℝ) → EReal)
        (_hf : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f)
        (_hf_closed : ClosedConvexFunction f)
        (_hg_closed : ClosedERealFunction g)
        (_hg_ne_bot : ∀ x, g x ≠ (⊥ : EReal))
        (_hdom :
          Set.Nonempty
              (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f ∩
                effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) ∨
            Set.Nonempty
              (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fenchelConjugate m f) ∩
                effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fenchelConjugate m g))),
        let p := translatedDifferenceValueFunction (n := m) f g
        (((∃! xStar : Fin m → ℝ,
            fenchelConjugate m g xStar - fenchelConjugate m f xStar =
                (⨆ z : Fin m → ℝ, fenchelConjugate m g z - fenchelConjugate m f z) ∧
              fenchelConjugate m g xStar - fenchelConjugate m f xStar =
                functionInfimumEReal (fun x => f x - g x)) ↔
          IsFiniteEReal (p (0 : Fin m → ℝ)) ∧
            ERealDifferentiableAt p (0 : Fin m → ℝ)) ∧
        (∀ hDiff : ERealDifferentiableAt p (0 : Fin m → ℝ),
          IsFiniteEReal (p (0 : Fin m → ℝ)) →
            ∃! xStar : Fin m → ℝ,
              fenchelConjugate m g xStar - fenchelConjugate m f xStar =
                  (⨆ z : Fin m → ℝ, fenchelConjugate m g z - fenchelConjugate m f z) ∧
                fenchelConjugate m g xStar - fenchelConjugate m f xStar =
                  functionInfimumEReal (fun x => f x - g x) ∧
                xStar = -erealGradientAt hDiff)) := by
  intro hUniversal
  rcases helperForLemma_31_0_13_counterexample_satisfies_currentHypotheses with
    ⟨hProperF, hClosedF, hClosedG, hG_ne_bot, hdom, _hInfFinite⟩
  have hSpecialized :
      let p := translatedDifferenceValueFunction (n := 1)
        helperForLemma_31_0_13_counterexampleF
        helperForLemma_31_0_13_counterexampleG
      (((∃! xStar : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                (⨆ z : Fin 1 → ℝ,
                  fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
                    fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) ∧
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
              functionInfimumEReal
                (fun x =>
                  helperForLemma_31_0_13_counterexampleF x -
                    helperForLemma_31_0_13_counterexampleG x)) ↔
        IsFiniteEReal (p (0 : Fin 1 → ℝ)) ∧
          ERealDifferentiableAt p (0 : Fin 1 → ℝ)) ∧
      (∀ hDiff : ERealDifferentiableAt p (0 : Fin 1 → ℝ),
        IsFiniteEReal (p (0 : Fin 1 → ℝ)) →
          ∃! xStar : Fin 1 → ℝ,
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                  (⨆ z : Fin 1 → ℝ,
                    fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
                      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) ∧
                fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                    fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                  functionInfimumEReal
                    (fun x =>
                      helperForLemma_31_0_13_counterexampleF x -
                        helperForLemma_31_0_13_counterexampleG x) ∧
              xStar = -erealGradientAt hDiff)) :=
    hUniversal (m := 1)
      helperForLemma_31_0_13_counterexampleF
      helperForLemma_31_0_13_counterexampleG
      hProperF hClosedF hClosedG hG_ne_bot hdom
  -- The specialized conclusion is exactly the impossible counterexample package proved above.
  exact helperForLemma_31_0_14_counterexample_fullConclusionFalse hSpecialized

/-- Helper for Lemma 31.0.14: the bundled optimal value of the translated bifunction agrees with
the primal infimum `inf_x (f x - g x)`. -/
lemma helperForLemma_31_0_14_translatedDifference_optimalValue_eq_functionInfimum
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    generalizedConvexProgramOptimalValue
        (helperForTheorem_31_2_translatedDifference_bifunction f g hf hg) =
      functionInfimumEReal (fun x => f x - g x) := by
  let F := helperForTheorem_31_2_translatedDifference_bifunction f g hf hg
  -- Re-express the bundled optimal value as the perturbation at `u = 0`.
  calc
    generalizedConvexProgramOptimalValue
        (helperForTheorem_31_2_translatedDifference_bifunction f g hf hg) =
      generalizedConvexProgramOptimalValue F := by
        simp [F]
    _ = generalizedConvexProgramPerturbationFunction F (0 : Fin n → ℝ) :=
      helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero F
    _ = translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) := by
        -- The translated value function is exactly the bundled perturbation function.
        symm
        exact
          helperForLemma_31_0_10_translatedDifferenceValue_eq_generalizedPerturbation_apply
            (f := f) (g := g) (hf := hf) (hg := hg) (u := 0)
    _ = functionInfimumEReal (fun x => f x - g x) :=
      helperForLemma_31_0_12_translatedDifferenceValueFunction_at_zero_eq_functionInfimum f g

/-- Helper for Lemma 31.0.14: finiteness of `inf_x (f x - g x)` is exactly the Section 29
finiteness hypothesis for the bundled translated bifunction. -/
lemma helperForLemma_31_0_14_translatedDifference_optimalValue_isFinite
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hInfFinite : IsFiniteEReal (functionInfimumEReal (fun x => f x - g x))) :
    IsFiniteEReal
      (generalizedConvexProgramOptimalValue
        (helperForTheorem_31_2_translatedDifference_bifunction f g hf hg)) := by
  -- Transport finiteness across the optimal-value/primal-infimum identity proved above.
  rw [helperForLemma_31_0_14_translatedDifference_optimalValue_eq_functionInfimum
    (f := f) (g := g) hf hg]
  exact hInfFinite

/-- Helper for Lemma 31.0.14: after strengthening the header to a proper-concave translated
perturbation with finite primal value, Section 29 gives the bundled uniqueness-versus-
differentiability statement directly. -/
lemma helperForLemma_31_0_14_translatedDifference_uniqueBundledKuhnTucker_iff_differentiableAt_zero
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hInfFinite : IsFiniteEReal (functionInfimumEReal (fun x => f x - g x))) :
    let F := helperForTheorem_31_2_translatedDifference_bifunction f g hf hg
    let p := translatedDifferenceValueFunction (n := n) f g
    ((∃! uStar : Fin n → ℝ, IsKuhnTuckerVector F uStar) ↔
      ERealDifferentiableAt p (0 : Fin n → ℝ)) ∧
    (∀ hDiff : ERealDifferentiableAt p (0 : Fin n → ℝ),
      ∃! uStar : Fin n → ℝ,
        IsKuhnTuckerVector F uStar ∧
          ∀ i : Fin n, uStar i = -(erealGradientAt hDiff i)) := by
  dsimp
  let F := helperForTheorem_31_2_translatedDifference_bifunction f g hf hg
  let p := translatedDifferenceValueFunction (n := n) f g
  have hfinite :
      IsFiniteEReal (generalizedConvexProgramOptimalValue F) := by
    -- Reuse the dedicated transport lemma from the primal infimum to the bundled optimal value.
    simpa [F] using
      helperForLemma_31_0_14_translatedDifference_optimalValue_isFinite
        (f := f) (g := g) hf hg hInfFinite
  have hSection29 :
      ((∃! uStar : Fin n → ℝ, IsKuhnTuckerVector F uStar) ↔
          ERealDifferentiableAt (generalizedConvexProgramPerturbationFunction F) 0) ∧
        (∀ hDiff :
            ERealDifferentiableAt (generalizedConvexProgramPerturbationFunction F) 0,
          ∃! uStar : Fin n → ℝ,
            IsKuhnTuckerVector F uStar ∧
              ∀ i : Fin n, uStar i = -(erealGradientAt hDiff i)) :=
    generalizedConvexProgram_uniqueKuhnTuckerVector_iff_differentiableAt_zero F hfinite
  constructor
  · -- Replace the bundled perturbation function by the textbook translated value function `p`.
    simpa [p, F,
      helperForTheorem_31_2_translatedDifferenceValue_eq_generalizedPerturbation f g hf hg] using
      hSection29.1
  · intro hDiff
    have hDiffBundled :
        ERealDifferentiableAt (generalizedConvexProgramPerturbationFunction F) 0 := by
      -- The differentiability witness is unchanged under the perturbation/value-function rewrite.
      simpa [p, F,
        helperForTheorem_31_2_translatedDifferenceValue_eq_generalizedPerturbation f g hf hg]
        using hDiff
    rcases hSection29.2 hDiffBundled with ⟨uStar, huStar, huUnique⟩
    refine ⟨uStar, ?_, ?_⟩
    · constructor
      · -- Keep the bundled Kuhn-Tucker witness produced by Section 29.
        exact huStar.1
      · -- Rewrite the coordinate formula back to the gradient of `p`.
        intro i
        simpa [p, F,
          helperForTheorem_31_2_translatedDifferenceValue_eq_generalizedPerturbation f g hf hg]
          using huStar.2 i
    · intro v hv
      have hvBundled :
          IsKuhnTuckerVector F v ∧
            ∀ i : Fin n, v i = -(erealGradientAt hDiffBundled i) := by
        constructor
        · -- The Kuhn-Tucker side is already expressed in the bundled language.
          exact hv.1
        · -- Rewrite the competing coordinate identity into the bundled perturbation form.
          intro i
          simpa [p, F,
            helperForTheorem_31_2_translatedDifferenceValue_eq_generalizedPerturbation
              f g hf hg] using hv.2 i
      exact huUnique v hvBundled

/-- Helper for Lemma 31.0.14: once the singleton-indicator/zero example is translated into the
bundled Section 29 language, the valid uniqueness theorem really does produce a unique Kuhn-Tucker
vector. -/
lemma helperForLemma_31_0_14_counterexample_uniqueBundledKuhnTuckerVector :
    ∃! uStar : Fin 1 → ℝ,
      IsKuhnTuckerVector
        (helperForTheorem_31_2_translatedDifference_bifunction
          helperForLemma_31_0_13_counterexampleF
          helperForLemma_31_0_13_counterexampleG
          helperForLemma_31_0_13_counterexample_satisfies_currentHypotheses.1
          helperForLemma_31_0_14_counterexampleG_properConcave)
        uStar := by
  rcases helperForLemma_31_0_13_counterexample_satisfies_currentHypotheses with
    ⟨hProperF, _hClosedF, _hClosedG, _hG_ne_bot, _hdom, hInfFinite⟩
  have hBundled :=
    helperForLemma_31_0_14_translatedDifference_uniqueBundledKuhnTucker_iff_differentiableAt_zero
      helperForLemma_31_0_13_counterexampleF
      helperForLemma_31_0_13_counterexampleG
      hProperF
      helperForLemma_31_0_14_counterexampleG_properConcave
      hInfFinite
  have hDiff :
      ERealDifferentiableAt
        (translatedDifferenceValueFunction (n := 1)
          helperForLemma_31_0_13_counterexampleF
          helperForLemma_31_0_13_counterexampleG)
        (0 : Fin 1 → ℝ) := by
    -- The translated value function is the constant-zero map, hence differentiable at the origin.
    exact helperForLemma_31_0_14_counterexample_finite_and_differentiableAt_zero.2
  -- The bundled Section 29 criterion now converts differentiability into unique Kuhn-Tucker
  -- data for the translated perturbation.
  simpa using hBundled.1.mpr hDiff

/-- Helper for Lemma 31.0.14: the requested bridge from the current textbook explicit unique
predicate to bundled Kuhn-Tucker uniqueness is false on the singleton-indicator/zero
counterexample. -/
lemma helperForLemma_31_0_14_counterexample_textbookUniquePredicate_not_iff_bundledKuhnTucker :
    let F := helperForTheorem_31_2_translatedDifference_bifunction
      helperForLemma_31_0_13_counterexampleF
      helperForLemma_31_0_13_counterexampleG
      helperForLemma_31_0_13_counterexample_satisfies_currentHypotheses.1
      helperForLemma_31_0_14_counterexampleG_properConcave
    ¬ (((∃! xStar : Fin 1 → ℝ,
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                  (⨆ z : Fin 1 → ℝ,
                    fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
                      fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) ∧
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                  fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                functionInfimumEReal
                  (fun x =>
                    helperForLemma_31_0_13_counterexampleF x -
                      helperForLemma_31_0_13_counterexampleG x)) ↔
          ∃! uStar : Fin 1 → ℝ, IsKuhnTuckerVector F uStar)) := by
  dsimp
  intro hBridge
  have hBundled :
      ∃! uStar : Fin 1 → ℝ,
        IsKuhnTuckerVector
          (helperForTheorem_31_2_translatedDifference_bifunction
            helperForLemma_31_0_13_counterexampleF
            helperForLemma_31_0_13_counterexampleG
            helperForLemma_31_0_13_counterexample_satisfies_currentHypotheses.1
            helperForLemma_31_0_14_counterexampleG_properConcave)
          uStar :=
    helperForLemma_31_0_14_counterexample_uniqueBundledKuhnTuckerVector
  have hTextbook :
      ∃! xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
              (⨆ z : Fin 1 → ℝ,
                fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
                  fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) ∧
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
            functionInfimumEReal
              (fun x =>
                helperForLemma_31_0_13_counterexampleF x -
                  helperForLemma_31_0_13_counterexampleG x) :=
    hBridge.mpr hBundled
  -- The ordinary textbook predicate has no witness here, even though the bundled theorem has one.
  exact helperForLemma_31_0_14_counterexample_no_unique_kuhnTuckerVector hTextbook

/-- Helper for Lemma 31.0.14: the singleton-indicator/zero counterexample simultaneously shows
that the translated value function is finite and differentiable at `0`, that the valid bundled
Section 29 theorem yields a unique Kuhn-Tucker vector, that the current textbook explicit
predicate still has no unique witness, and that the added `hDualSupFinite` hypothesis fails. -/
lemma helperForLemma_31_0_14_counterexample_separatesBundledRouteFromTextbookPredicate :
    let p := translatedDifferenceValueFunction (n := 1)
      helperForLemma_31_0_13_counterexampleF
      helperForLemma_31_0_13_counterexampleG
    let F := helperForTheorem_31_2_translatedDifference_bifunction
      helperForLemma_31_0_13_counterexampleF
      helperForLemma_31_0_13_counterexampleG
      helperForLemma_31_0_13_counterexample_satisfies_currentHypotheses.1
      helperForLemma_31_0_14_counterexampleG_properConcave
    (IsFiniteEReal (p (0 : Fin 1 → ℝ)) ∧
        ERealDifferentiableAt p (0 : Fin 1 → ℝ)) ∧
      (∃! uStar : Fin 1 → ℝ, IsKuhnTuckerVector F uStar) ∧
      (¬ ∃! xStar : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
                (⨆ z : Fin 1 → ℝ,
                  fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
                    fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) ∧
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG xStar -
                fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF xStar =
              functionInfimumEReal
                (fun x =>
                  helperForLemma_31_0_13_counterexampleF x -
                    helperForLemma_31_0_13_counterexampleG x)) ∧
      ¬ IsFiniteEReal
          (⨆ z : Fin 1 → ℝ,
            fenchelConjugate 1 helperForLemma_31_0_13_counterexampleG z -
              fenchelConjugate 1 helperForLemma_31_0_13_counterexampleF z) := by
  dsimp
  refine ⟨?_, ?_⟩
  · -- The translated value side is exactly the constant-zero differentiability package.
    simpa using helperForLemma_31_0_14_counterexample_finite_and_differentiableAt_zero
  · refine ⟨?_, ?_⟩
    · -- The bundled Section 29 formulation really does have a unique Kuhn-Tucker vector here.
      exact helperForLemma_31_0_14_counterexample_uniqueBundledKuhnTuckerVector
    · refine ⟨?_, ?_⟩
      · -- The ordinary textbook explicit predicate still has no witness at all.
        exact helperForLemma_31_0_14_counterexample_no_unique_kuhnTuckerVector
      · -- The ordinary dual supremum is `⊤`, so the extra finiteness assumption fails.
        exact helperForLemma_31_0_14_counterexample_not_hDualSupFinite

-- Proof sketch: combine `Lemma 31.0.13` with the Chapter 27 singleton-minimum criterion applied
-- to the convex value function `p = translatedDifferenceValueFunction f g`. The equality
-- `sup (g⋆ - f⋆) = p(0) = inf (f - g)` identifies Kuhn-Tucker vectors with minimizers of the
-- convex conjugate picture, and the singleton criterion converts uniqueness of that vector into
-- differentiability of `p` at `0`; the gradient identification yields `x⋆ = -∇p(0)`.
/-- Lemma 31.0.14 (Uniqueness of Kuhn-Tucker Vectors): in the same translated-perturbation
setting as Lemma 31.0.13, let `F` be the bundled bifunction `(u, x) ↦ f x - g (x + u)` and
`p(u) = inf_x (f x - g (x + u))`. If `inf_x (f x - g x)` is finite, then there exists a unique
Kuhn-Tucker vector for `F` if and only if `p` is differentiable at `0`; in that case the unique
vector is `-∇ p(0)`. -/
lemma unique_kuhn_tucker_vector_iff_translatedDifferenceValueFunction_finite_and_differentiableAt_zero
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hInfFinite : IsFiniteEReal (functionInfimumEReal (fun x => f x - g x))) :
    let p := translatedDifferenceValueFunction (n := n) f g
    let F := helperForTheorem_31_2_translatedDifference_bifunction f g hf hg
    ((∃! uStar : Fin n → ℝ, IsKuhnTuckerVector F uStar) ↔
      ERealDifferentiableAt p (0 : Fin n → ℝ)) ∧
    (∀ hDiff : ERealDifferentiableAt p (0 : Fin n → ℝ),
        ∃! uStar : Fin n → ℝ,
          IsKuhnTuckerVector F uStar ∧
            ∀ i : Fin n, uStar i = -(erealGradientAt hDiff i)) := by
  simpa [and_left_comm, and_assoc] using
    helperForLemma_31_0_14_translatedDifference_uniqueBundledKuhnTucker_iff_differentiableAt_zero
      (f := f) (g := g) hf hg hInfFinite

end Section31
end Chap06
