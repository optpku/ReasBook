/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Example_26_15

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

/-- Helper for Example 26.19: pathwise uniqueness compares strong realizations on the same
filtered probability space with the same Brownian path and almost surely the same initial datum.
-/
def GeneralizedWeakSDESolution.IsPathwiseUnique
    {n m : ℕ}
    {μ₀ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ₀]
    {σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ}
    {b : NNReal → (Fin n → ℝ) → Fin n → ℝ}
    (L : GeneralizedWeakSDESolution μ₀ σ b) : Prop :=
  ∀ ⦃ξ' : L.Ω → Fin n → ℝ⦄ (X' : L.Ω → EuclideanPathSpace n),
    ξ' =ᵐ[L.μ] L.ξ →
    SolvesStrongGeneralizedSDE σ b L.μ L.ℱ ξ' L.Wpath X' →
    X' =ᵐ[L.μ] L.X

private abbrev signInitialLaw : Measure (Fin 1 → ℝ) :=
  Measure.dirac (oneDimensionalState (0 : ℝ))

/-- Helper for Example 26.19: coercing a closure witness back to ambient `L²(μ ⊗ dt)` recovers
the `Lp` class selected by `Classical.choose`. -/
private theorem memPredictableStepProcessClosure_coe_toClosure
    {Ω : Type u} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} {H : NNReal → Ω → ℝ}
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    ((MemPredictableStepProcessClosure.toClosure hH :
        MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
      Lp ℝ 2 (processMeasure μ)) =
      (Classical.choose hH).toLp (processToTimeSpaceFun H) :=
  rfl

/-- Helper for Example 26.19: stopping a process before a stopping time commutes with
deterministic scalar multiplication. -/
private theorem processBeforeStoppingTime_const_mul
    {Ω : Type u} [MeasurableSpace Ω]
    (c : ℝ) (H : NNReal → Ω → ℝ) (τ : Ω → ENNReal) :
    processBeforeStoppingTime (fun t ω ↦ c * H t ω) τ =
      fun t ω ↦ c * processBeforeStoppingTime H τ t ω := by
  funext t ω
  by_cases hτω : (t : ENNReal) ≤ τ ω
  · simp [processBeforeStoppingTime_apply, hτω]
  · simp [processBeforeStoppingTime_apply, hτω]

/-- Helper for Example 26.19: scaling both the integrand and the realized process by the same
deterministic constant preserves the Chapter 26 Brownian local Itô owner. -/
private theorem isBrownianLocalItoIntegral_const_mul
    {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {W H I : NNReal → Ω → ℝ} (c : ℝ)
    (hI : IsBrownianLocalItoIntegral ℱ μ W H I) :
    IsBrownianLocalItoIntegral ℱ μ W
      (fun t ω ↦ c * H t ω)
      (fun t ω ↦ c * I t ω) := by
  have hProg :
      ProgMeasurable ℱ (fun t ω ↦ c * H t ω) := by
    exact (progMeasurable_const ℱ c).mul hI.locally_square_integrable.1
  have hInterval :
      ∀ T : NNReal,
        ∀ᵐ ω ∂μ,
          IntegrableOn
            (fun s : ℝ ↦ ((fun t ω ↦ c * H t ω) s.toNNReal ω) ^ 2)
            (Set.Icc (0 : ℝ) (T : ℝ)) := by
    intro T
    filter_upwards [hI.locally_square_integrable.2 T] with ω hω
    simpa [IntegrableOn, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (hω.const_mul c).const_mul c
  have hLocal :
      MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ (fun t ω ↦ c * H t ω) := by
    exact ⟨hProg, hInterval⟩
  refine
    { locally_square_integrable := hLocal
      brownian_motion := hI.brownian_motion
      zero := ?_
      continuous_paths := ?_
      canonical_local_integral := ?_ }
  · ext ω
    simp [hI.zero]
  · filter_upwards [hI.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using (continuous_const.mul hω)
  · rcases hI.canonical_local_integral with ⟨hIto, τSeq, hτSeq, hτClosure, hτLimit⟩
    let hτClosureScaled : ∀ n : ℕ,
        MemPredictableStepProcessClosure ℱ μ
          (processBeforeStoppingTime (fun t ω ↦ c * H t ω) (τSeq n)) :=
      fun n ↦ by
        let K := processBeforeStoppingTime H (τSeq n)
        have hBaseMemLp := Classical.choose (hτClosure n)
        have hScaledMemLp :
            MemLp
              (processToTimeSpaceFun
                (processBeforeStoppingTime (fun t ω ↦ c * H t ω) (τSeq n)))
              2
              (processMeasure μ) := by
          simpa [K, processBeforeStoppingTime_const_mul, processToTimeSpaceFun] using
            hBaseMemLp.const_mul c
        have hScaledLpEq :
            hScaledMemLp.toLp
                (processToTimeSpaceFun
                  (processBeforeStoppingTime (fun t ω ↦ c * H t ω) (τSeq n))) =
              c • hBaseMemLp.toLp (processToTimeSpaceFun K) := by
          have hPointwise :
              processToTimeSpaceFun
                  (processBeforeStoppingTime (fun t ω ↦ c * H t ω) (τSeq n)) =
                c • processToTimeSpaceFun K := by
            funext x
            rcases x with ⟨ω, s⟩
            simp [K, processBeforeStoppingTime_const_mul, processToTimeSpaceFun]
          rw [Lp.ext_iff]
          exact hScaledMemLp.coeFn_toLp.trans <|
            (Filter.EventuallyEq.of_eq hPointwise).trans <|
              ((hBaseMemLp.coeFn_toLp.const_smul c).symm.trans
                (Lp.coeFn_smul c (hBaseMemLp.toLp (processToTimeSpaceFun K))).symm)
        refine ⟨hScaledMemLp, ?_⟩
        have hBaseMem :
            hBaseMemLp.toLp (processToTimeSpaceFun K) ∈
              MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
          Classical.choose_spec (hτClosure n)
        rw [hScaledLpEq]
        exact (MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ).smul_mem c hBaseMem
    refine ⟨hIto, τSeq, hτSeq, hτClosureScaled, ?_⟩
    intro t
    have hClosureEq :
        ∀ n,
          MemPredictableStepProcessClosure.toClosure (hτClosureScaled n) =
            c • MemPredictableStepProcessClosure.toClosure (hτClosure n) := by
      intro n
      apply Subtype.ext
      let K := processBeforeStoppingTime H (τSeq n)
      have hBaseMemLp := Classical.choose (hτClosure n)
      have hScaledMemLp :
          MemLp
            (processToTimeSpaceFun
              (processBeforeStoppingTime (fun t ω ↦ c * H t ω) (τSeq n)))
            2
            (processMeasure μ) := by
        simpa [K, processBeforeStoppingTime_const_mul, processToTimeSpaceFun] using
          hBaseMemLp.const_mul c
      have hScaledLpEq :
          hScaledMemLp.toLp
              (processToTimeSpaceFun
                (processBeforeStoppingTime (fun t ω ↦ c * H t ω) (τSeq n))) =
            c • hBaseMemLp.toLp (processToTimeSpaceFun K) := by
        have hPointwise :
            processToTimeSpaceFun
                (processBeforeStoppingTime (fun t ω ↦ c * H t ω) (τSeq n)) =
              c • processToTimeSpaceFun K := by
          funext x
          rcases x with ⟨ω, s⟩
          simp [K, processBeforeStoppingTime_const_mul, processToTimeSpaceFun]
        rw [Lp.ext_iff]
        exact hScaledMemLp.coeFn_toLp.trans <|
          (Filter.EventuallyEq.of_eq hPointwise).trans <|
            ((hBaseMemLp.coeFn_toLp.const_smul c).symm.trans
              (Lp.coeFn_smul c (hBaseMemLp.toLp (processToTimeSpaceFun K))).symm)
      rw [memPredictableStepProcessClosure_coe_toClosure, hScaledLpEq]
      change
        c • hBaseMemLp.toLp (processToTimeSpaceFun K) =
          c •
            (((MemPredictableStepProcessClosure.toClosure (hτClosure n) :
                MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                Lp ℝ 2 (processMeasure μ)))
      rw [memPredictableStepProcessClosure_coe_toClosure]
    have hSeqSmul :
        ∀ᵐ ω ∂μ,
          ∀ n,
            hIto.toContinuousLinearMap
                (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
                  (MemPredictableStepProcessClosure.toClosure (hτClosureScaled n))) ω =
              c * hIto.toContinuousLinearMap
                (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
                  (MemPredictableStepProcessClosure.toClosure (hτClosure n))) ω := by
      refine ae_all_iff.2 ?_
      intro n
      rw [hClosureEq n, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
      exact
        (Lp.coeFn_smul c
          (hIto.toContinuousLinearMap
            (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
              (MemPredictableStepProcessClosure.toClosure (hτClosure n))))).mono
          fun ω hω ↦ by
            simpa [Pi.smul_apply] using hω
    filter_upwards [hτLimit t, hSeqSmul] with ω hω hωsmul
    have hSeqEq :
        (fun n ↦
          hIto.toContinuousLinearMap
            (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
              (MemPredictableStepProcessClosure.toClosure (hτClosureScaled n))) ω) =
          fun n ↦
            c * hIto.toContinuousLinearMap
              (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
                (MemPredictableStepProcessClosure.toClosure (hτClosure n))) ω := by
      funext n
      exact hωsmul n
    rw [hSeqEq]
    exact hω.const_mul c

/-- Helper for Example 26.19: scaling the vector Itô term and its matrix coefficient by the same
deterministic constant preserves the Chapter 26 matrix Itô owner. -/
private theorem isMatrixBrownianLocalItoIntegral_const_mul
    {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {W : NNReal → Ω → Fin 1 → ℝ}
    {H : NNReal → Ω → Fin 1 → Fin 1 → ℝ}
    {N : NNReal → Ω → Fin 1 → ℝ}
    (c : ℝ)
    (hN : IsMatrixBrownianLocalItoIntegral ℱ μ W H N) :
    IsMatrixBrownianLocalItoIntegral
      ℱ
      μ
      W
      (fun t ω i j ↦ c * H t ω i j)
      (fun t ω i ↦ c * N t ω i) := by
  rcases hN with ⟨Nij, hNij, hSum⟩
  refine ⟨fun i j t ω ↦ c * Nij i j t ω, ?_, ?_⟩
  · intro i j
    exact isBrownianLocalItoIntegral_const_mul c (hNij i j)
  · intro t ω i
    simp [hSum]

/-- Helper for Example 26.19: the sign-SDE competitor obtained by negating the witness path. -/
private abbrev negatedSignWitnessPath
    (L :
      GeneralizedWeakSDESolution
        signInitialLaw
        (oneDimensionalDiffusion (fun _ x ↦ Real.sign x))
        (oneDimensionalDrift (fun _ _ ↦ (0 : ℝ)))) :
    L.Ω → EuclideanPathSpace 1 :=
  fun ω ↦ -((L : L.Ω → EuclideanPathSpace 1) ω)

/-- Helper for Example 26.19: negating the explicit initial datum preserves it almost surely,
because the sign-SDE witness starts from `0` almost surely. -/
private theorem negatedSignWitness_initialDatum_ae_eq_original
    (L :
      GeneralizedWeakSDESolution
        signInitialLaw
        (oneDimensionalDiffusion (fun _ x ↦ Real.sign x))
        (oneDimensionalDrift (fun _ _ ↦ (0 : ℝ)))) :
    (fun ω ↦ -L.ξ ω) =ᵐ[L.μ] L.ξ := by
  filter_upwards [signWeakSolution_initialDatum_ae_eq_zero L] with ω hω
  ext i
  simp [hω]

/-- Helper for Example 26.19: the negated path still solves the sign SDE on the same filtered
space, with the negated initial datum. -/
private theorem negatedSignWitnessPath_solvesStrong
    (L :
      GeneralizedWeakSDESolution
        signInitialLaw
        (oneDimensionalDiffusion (fun _ x ↦ Real.sign x))
        (oneDimensionalDrift (fun _ _ ↦ (0 : ℝ)))) :
    SolvesStrongGeneralizedSDE
      (oneDimensionalDiffusion (fun _ x ↦ Real.sign x))
      (oneDimensionalDrift (fun _ _ ↦ (0 : ℝ)))
      L.μ
      L.ℱ
      (fun ω ↦ -L.ξ ω)
      L.Wpath
      (negatedSignWitnessPath L) := by
  rcases L.solvesGeneralizedDiffusion with ⟨hBrownian, N, hIto, _, _, hStateEq⟩
  refine ⟨inferInstance, ?_⟩
  refine ⟨by simpa [pathProcess, L.w_eq] using hBrownian, ?_⟩
  refine ⟨fun t ω i ↦ -N t ω i, ?_, ?_, ?_, ?_⟩
  · simpa [pathProcess, L.w_eq, negatedSignWitnessPath, oneDimensionalDiffusion_apply,
      Real.sign_neg] using
      isMatrixBrownianLocalItoIntegral_const_mul (-1 : ℝ) hIto
  · intro i
    fin_cases i
    simpa [oneDimensionalDrift_apply] using progMeasurable_const L.ℱ (0 : ℝ)
  · intro i T
    fin_cases i
    filter_upwards with ω
    simp [oneDimensionalDrift_apply]
  · ext t ω i
    fin_cases i
    have hState :
        L ω t 0 =
          L.ξ ω 0 +
            N t ω 0 +
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (0 : ℝ) := by
      simpa [oneDimensionalDrift_apply] using
        congrFun (congrFun (congrFun hStateEq t) ω) 0
    calc
      negatedSignWitnessPath L ω t 0 = -(L ω t 0) := by
        rfl
      _ = -(L.ξ ω 0 + N t ω 0 + ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (0 : ℝ)) := by
        rw [hState]
      _ = -L.ξ ω 0 - N t ω 0 - ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (0 : ℝ) := by
        ring
      _ = -L.ξ ω 0 + -N t ω 0 := by
        simp [sub_eq_add_neg]
      _ = -L.ξ ω 0 + -N t ω 0 +
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              oneDimensionalDrift
                (fun _ _ ↦ (0 : ℝ))
                s.toNNReal
                (fun k ↦ negatedSignWitnessPath L ω s.toNNReal k)
                0 := by
          simp [oneDimensionalDrift_apply]

/-- Helper for Example 26.19: there is a sign-SDE weak solution for which pathwise uniqueness
fails. -/
theorem existsSignSdeWitnessNotPathwiseUnique :
    ∃ L :
        GeneralizedWeakSDESolution
          signInitialLaw
          (oneDimensionalDiffusion (fun _ x ↦ Real.sign x))
          (oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))),
      ¬ L.IsPathwiseUnique := by
  rcases existsSignSdeWeakSolution with ⟨L, hReverseIto⟩
  refine ⟨L, ?_⟩
  intro hPathwiseUnique
  have hNegEq :
      negatedSignWitnessPath L =ᵐ[L.μ] (L : L.Ω → EuclideanPathSpace 1) :=
    hPathwiseUnique
      (ξ' := fun ω ↦ -L.ξ ω)
      (negatedSignWitnessPath L)
      (negatedSignWitness_initialDatum_ae_eq_original L)
      (negatedSignWitnessPath_solvesStrong L)
  have hStateZero :
      ∀ᵐ ω ∂L.μ, L ω 1 0 = 0 := by
    -- Proof comment: if the negated path agrees with the original path, then the unique scalar
    -- coordinate at time `1` must satisfy `-x = x`, hence vanish.
    filter_upwards [hNegEq] with ω hω
    have hCoord : -(L ω 1 0) = L ω 1 0 := by
      simpa [negatedSignWitnessPath] using congrFun (DFunLike.congr_fun hω 1) 0
    linarith
  have hCoordMeas :
      Measurable (fun ω : L.Ω ↦ L ω 1 0) := by
    exact
      Measurable.mono
        (signWeakSolution_stateCoordinate_adaptedToAmbientFiltration L 1)
        (L.ℱ.le 1)
        le_rfl
  have hProbOne :
      L.μ {ω | L ω 1 0 = 0} = 1 := by
    exact (mem_ae_iff_prob_eq_one (hCoordMeas (MeasurableSet.singleton 0))).1 hStateZero
  have hProbZero :
      L.μ {ω | L ω 1 0 = 0} = 0 := by
    simpa using
      brownianEval_zero_prob_eq_zero
        hReverseIto.brownian_motion
        (show (0 : ℝ) < 1 by norm_num)
  exact zero_ne_one (hProbZero.symm.trans hProbOne)

/-- Example 26.19: negating a weak solution of the one-dimensional sign SDE gives another weak
solution on the same filtered probability space, so pathwise uniqueness fails for this equation. -/
theorem sign_sde_pathwiseUniqueness_fails :
    ∃ L :
        GeneralizedWeakSDESolution
          signInitialLaw
          (oneDimensionalDiffusion (fun _ x ↦ Real.sign x))
          (oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))),
      ¬ L.IsPathwiseUnique := by
  exact existsSignSdeWitnessNotPathwiseUnique

end ProbabilityTheory
