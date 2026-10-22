/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Exercise 1.5.2: there exists a probability measure on `ℝ × Bool` for which the first
coordinate and the signed first coordinate are both Gaussian random variables, but their pair is
not a two-dimensional Gaussian random variable. -/
-- Proof sketch: take a standard Gaussian variable `Z` together with an independent Rademacher
-- sign `ε`, and set `X = Z` and `Y = εZ`. Then `Y` is again Gaussian, while `(X, Y)` is supported
-- on the two lines `y = x` and `y = -x`, so its joint law is not Gaussian.
theorem exists_gaussian_marginals_without_gaussian_pair :
    ∃ P : ProbabilityMeasure (ℝ × Bool),
      HasGaussianLaw (fun ω : ℝ × Bool ↦ ω.1) (P : Measure (ℝ × Bool)) ∧
      HasGaussianLaw (fun ω ↦ if ω.2 then ω.1 else -ω.1) (P : Measure (ℝ × Bool)) ∧
      ¬ HasGaussianLaw (fun ω ↦ (ω.1, if ω.2 then ω.1 else -ω.1)) (P : Measure (ℝ × Bool)) :=
  by
    let μ : Measure ℝ := gaussianReal 0 1
    let Pm : Measure (ℝ × Bool) :=
      (1 / 2 : ℝ≥0∞) • μ.map (fun z ↦ (z, true)) +
        (1 / 2 : ℝ≥0∞) • μ.map (fun z ↦ (-z, false))
    -- The witness is a half-half mixture of the two Gaussian branches.
    have hPm_prob : IsProbabilityMeasure Pm := by
      refine ⟨?_⟩
      have hBranchPos : (Measure.map (fun z : ℝ ↦ (z, true)) (gaussianReal 0 1)) Set.univ = 1 := by
        rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
        simp
      have hBranchNeg :
          (Measure.map (fun z : ℝ ↦ (-z, false)) (gaussianReal 0 1)) Set.univ = 1 := by
        rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
        simp
      dsimp [Pm, μ]
      rw [hBranchPos, hBranchNeg]
      simpa using ENNReal.inv_two_add_inv_two
    let P : ProbabilityMeasure (ℝ × Bool) := ⟨Pm, hPm_prob⟩
    refine ⟨P, ?_, ?_, ?_⟩
    · have hFirstMap : Pm.map (fun ω : ℝ × Bool ↦ ω.1) = gaussianReal 0 1 := by
        -- The first projection sees `z` on one branch and `-z` on the other, so both laws agree.
        have hFirstCompPos :
            (fun ω : ℝ × Bool ↦ ω.1) ∘ (fun z : ℝ ↦ (z, true)) = fun z : ℝ ↦ z := by
          ext z
          rfl
        have hFirstCompNeg :
            (fun ω : ℝ × Bool ↦ ω.1) ∘ (fun z : ℝ ↦ (-z, false)) = fun z : ℝ ↦ -z := by
          ext z
          rfl
        have hId : (fun z : ℝ ↦ z) = id := rfl
        have hNegZero : Measure.map (fun z : ℝ ↦ -z) (gaussianReal 0 1) = gaussianReal 0 1 := by
          simpa using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
        dsimp [Pm]
        rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
          Measure.map_map measurable_fst (by fun_prop),
          Measure.map_map measurable_fst (by fun_prop), hFirstCompPos, hFirstCompNeg, hId,
          Measure.map_id]
        dsimp [μ]
        rw [hNegZero, ← add_smul]
        have hHalf : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
          simpa using ENNReal.inv_two_add_inv_two
        rw [hHalf, one_smul]
      have hGaussianStd : IsGaussian (gaussianReal 0 1) := inferInstance
      refine ⟨?_⟩
      simpa [P, hFirstMap] using hGaussianStd
    · have hSignedMap : Pm.map (fun ω : ℝ × Bool ↦ if ω.2 then ω.1 else -ω.1) =
          gaussianReal 0 1 := by
        -- The signed coordinate is `z` on both branches by construction.
        have hTrueSet : MeasurableSet {ω : ℝ × Bool | ω.2 = true} := by
          change MeasurableSet ((fun ω : ℝ × Bool ↦ ω.2) ⁻¹' ({true} : Set Bool))
          exact measurable_snd (MeasurableSet.singleton true)
        have hSignedMeas : Measurable (fun ω : ℝ × Bool ↦ if ω.2 then ω.1 else -ω.1) := by
          simpa using Measurable.ite hTrueSet measurable_fst measurable_fst.neg
        have hSignedCompPos :
            (fun ω : ℝ × Bool ↦ if ω.2 then ω.1 else -ω.1) ∘
              (fun z : ℝ ↦ (z, true)) = fun z : ℝ ↦ z := by
          ext z
          simp
        have hSignedCompNeg :
            (fun ω : ℝ × Bool ↦ if ω.2 then ω.1 else -ω.1) ∘
              (fun z : ℝ ↦ (-z, false)) = fun z : ℝ ↦ z := by
          ext z
          simp
        dsimp [Pm]
        rw [Measure.map_add _ _ hSignedMeas, Measure.map_smul, Measure.map_smul,
          Measure.map_map hSignedMeas (by fun_prop), Measure.map_map hSignedMeas (by fun_prop),
          hSignedCompPos, hSignedCompNeg, ← add_smul]
        have hHalf : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
          simpa using ENNReal.inv_two_add_inv_two
        rw [hHalf, one_smul]
        have hMapId : Measure.map (fun z : ℝ ↦ z) μ = μ := by
          simp
        rw [hMapId]
      have hGaussianStd : IsGaussian (gaussianReal 0 1) := inferInstance
      refine ⟨?_⟩
      simpa [P, hSignedMap] using hGaussianStd
    · intro hPair
      have hPair' :
          HasGaussianLaw (fun ω : ℝ × Bool ↦ (ω.1, if ω.2 then ω.1 else -ω.1)) Pm := by
        simpa [P] using hPair
      have hSum :
          HasGaussianLaw (fun ω : ℝ × Bool ↦ ω.1 + if ω.2 then ω.1 else -ω.1) Pm := by
        -- A Gaussian pair stays Gaussian under the linear map `(x, y) ↦ x + y`.
        simpa using hPair'.fun_add
      let ν : Measure ℝ :=
        (1 / 2 : ℝ≥0∞) • Measure.dirac 0 +
          (1 / 2 : ℝ≥0∞) • μ.map (fun z ↦ z * (2 : ℝ))
      have hSumMap :
          Pm.map (fun ω : ℝ × Bool ↦ ω.1 + if ω.2 then ω.1 else -ω.1) = ν := by
        -- The sum is `0` on the reflected branch and `2z` on the unreﬂected branch.
        have hTrueSet : MeasurableSet {ω : ℝ × Bool | ω.2 = true} := by
          change MeasurableSet ((fun ω : ℝ × Bool ↦ ω.2) ⁻¹' ({true} : Set Bool))
          exact measurable_snd (MeasurableSet.singleton true)
        have hSignedMeas : Measurable (fun ω : ℝ × Bool ↦ if ω.2 then ω.1 else -ω.1) := by
          simpa using Measurable.ite hTrueSet measurable_fst measurable_fst.neg
        have hSumMeas : Measurable (fun ω : ℝ × Bool ↦ ω.1 + if ω.2 then ω.1 else -ω.1) := by
          exact measurable_fst.add hSignedMeas
        have hSumCompPos :
            (fun ω : ℝ × Bool ↦ ω.1 + if ω.2 then ω.1 else -ω.1) ∘
              (fun z : ℝ ↦ (z, true)) = fun z : ℝ ↦ z * (2 : ℝ) := by
          ext z
          simp
          ring
        have hSumCompNeg :
            (fun ω : ℝ × Bool ↦ ω.1 + if ω.2 then ω.1 else -ω.1) ∘
              (fun z : ℝ ↦ (-z, false)) = fun _ : ℝ ↦ 0 := by
          ext z
          simp
        dsimp [Pm]
        rw [Measure.map_add _ _ hSumMeas, Measure.map_smul, Measure.map_smul,
          Measure.map_map hSumMeas (by fun_prop), Measure.map_map hSumMeas (by fun_prop),
          hSumCompPos, hSumCompNeg, Measure.map_const]
        have hMuUniv : μ Set.univ = 1 := by
          dsimp [μ]
          simp
        rw [hMuUniv, smul_smul]
        simp [ν, add_comm]
      have hGaussianNu : IsGaussian ν := by
        rw [← hSumMap]
        exact hSum.isGaussian_map
      let vDouble : NNReal := (⟨(2 : ℝ) ^ 2, sq_nonneg (2 : ℝ)⟩ : NNReal)
      have hDoubleMap :
          μ.map (fun z ↦ z * (2 : ℝ)) = gaussianReal 0 vDouble := by
        simpa [μ] using gaussianReal_map_mul_const (μ := 0) (v := (1 : NNReal)) (c := (2 : ℝ))
      have hDoubleZero : μ.map (fun z ↦ z * (2 : ℝ)) ({0} : Set ℝ) = 0 := by
        rw [hDoubleMap]
        have hVDoubleNeZero : vDouble ≠ 0 := by
          intro h
          have hReal : ((vDouble : NNReal) : ℝ) = 0 := by
            exact congrArg (fun x : NNReal ↦ (x : ℝ)) h
          norm_num [vDouble] at hReal
        letI : NoAtoms (gaussianReal 0 vDouble) :=
          noAtoms_gaussianReal (μ := 0) (v := vDouble) hVDoubleNeZero
        exact measure_singleton (μ := gaussianReal 0 vDouble) (0 : ℝ)
      have hNuZero : ν ({0} : Set ℝ) = (1 / 2 : ℝ≥0∞) := by
        -- The explicit atom at `0` comes from the reflected branch only.
        simp [ν, hDoubleZero, Measure.dirac_apply']
      have hNotDirac : ∀ x : ℝ, ν ≠ Measure.dirac x := by
        intro x hx
        have hxZero : (Measure.dirac x) ({0} : Set ℝ) = (1 / 2 : ℝ≥0∞) := by
          rw [← hx, hNuZero]
        by_cases hx0 : x = 0
        · subst hx0
          have hxZero' : (1 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by
            simpa [Measure.dirac_apply'] using hxZero
          have hReal : (1 : ℝ) = 1 / 2 := by
            simpa using congrArg ENNReal.toReal hxZero'
          have hFalse : False := by
            norm_num at hReal
          exact hFalse
        · have hxZero' : (0 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by
            simpa [Measure.dirac_apply', hx0] using hxZero
          have hReal : (0 : ℝ) = 1 / 2 := by
            simpa using congrArg ENNReal.toReal hxZero'
          have hFalse : False := by
            norm_num at hReal
          exact hFalse
      letI : IsGaussian ν := hGaussianNu
      have hNoAtoms : NoAtoms ν := ProbabilityTheory.IsGaussian.noAtoms hNotDirac
      have : ν ({0} : Set ℝ) = 0 := hNoAtoms.measure_singleton 0
      rw [hNuZero] at this
      norm_num at this
