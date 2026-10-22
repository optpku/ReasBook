/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_29
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} {Ω : Type v}

section

variable [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
variable [MeasurableSpace Ω]
variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {τ : Ω → Ω}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/- Example 20.17 is `source-facing`: the Chapter 20 owner theorem
`stationary_shift_ergodic_of_irreducible_positiveRecurrent` already takes the Chapter 17
irreducibility predicate `IsIrreducibleMarkovChain P X` as its main input. The occupation-frequency
limit below is a companion consequence obtained from that owner statement via Birkhoff's ergodic
theorem and the Chapter 12 owner `empiricalDistribution`. -/

-- Proof sketch: apply the Chapter 20 owner theorem
-- `stationary_shift_ergodic_of_irreducible_positiveRecurrent` for the stationary shift system
-- under the canonical stationary law `stationaryLaw P π = P_π`. For the source-facing
-- occupation count, use the Chapter 12 owner `empiricalDistribution (Nat.succPNat n) (fun i ↦ X i)
-- ω`; its singleton mass at `x` is exactly the occupation frequency of `x` in the first `n + 1`
-- observations. Then apply Birkhoff's ergodic theorem to the observable
-- `ω ↦ 𝟙_{ {x} } (X 0 ω)` and rewrite along `X n = X 0 ∘ τ^[n]`.
/-- Helper for Example 20.17: evaluating the singleton `{x}` under the empirical distribution of
the first `n + 1` observations matches the Birkhoff average of the time-zero singleton indicator,
transported from `ℝ` to `NNReal`. -/
private lemma empiricalDistributionSingleton_eq_ofReal_birkhoffAverageZeroIndicator
    (hshift : ∀ n : ℕ, X n = X 0 ∘ τ^[n]) (x : E) (n : ℕ) (ω : Ω) :
    (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω) {x} =
      Real.toNNReal
        (birkhoffAverage ℝ τ
          (fun ω' ↦ ({x} : Set E).indicator (fun _ ↦ (1 : ℝ)) (X 0 ω'))
          (n + 1) ω) := by
  have hEmpirical :
      (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω : Measure E) =
        ((n + 1 : ℕ) : ENNReal)⁻¹ • ∑ i : Fin (n + 1), Measure.dirac (X i ω) := by
    simpa [Nat.succPNat, Nat.succ_eq_add_one] using
      (@empiricalDistribution_toMeasure Ω E _ _ (Nat.succPNat n) (fun i ↦ X i) ω)
  have hInv :
      ((n + 1 : ℕ) : ENNReal)⁻¹ = ENNReal.ofReal ((n + 1 : ℝ)⁻¹) := by
    have hpos : (0 : ℝ) < n + 1 := by positivity
    have hcast : ((n + 1 : ℕ) : ENNReal) = ENNReal.ofReal (n + 1 : ℝ) := by
      simpa using (ENNReal.ofReal_natCast (n + 1)).symm
    rw [hcast]
    exact (ENNReal.ofReal_inv_of_pos hpos).symm
  have hDirac :
      ∀ i : Fin (n + 1),
        (Measure.dirac (X i ω)) {x} =
          ENNReal.ofReal
            ((({x} : Set E).indicator (fun _ ↦ (1 : ℝ))) (X 0 ((τ^[i]) ω))) := by
    intro i
    have hi : X i ω = X 0 ((τ^[i]) ω) := by
      simpa [Function.comp] using congrFun (hshift i) ω
    by_cases hx : X 0 ((τ^[i]) ω) = x
    · simp [Measure.dirac_apply', hi, hx]
    · simp [Measure.dirac_apply', hi, hx]
  have hIndicatorNonneg :
      0 ≤ ∑ i : Fin (n + 1),
        (({x} : Set E).indicator (fun _ ↦ (1 : ℝ))) (X 0 ((τ^[i]) ω)) := by
    refine Finset.sum_nonneg ?_
    intro i hi
    by_cases hx : X 0 ((τ^[i]) ω) = x
    · simp [hx]
    · simp [hx]
  have hENN :
      (((empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω) {x} : NNReal) : ℝ≥0∞) =
        ENNReal.ofReal
          (birkhoffAverage ℝ τ
            (fun ω' ↦ ({x} : Set E).indicator (fun _ ↦ (1 : ℝ)) (X 0 ω'))
            (n + 1) ω) := by
  -- Proof comment: rewrite the empirical law as an averaged Dirac sum, then identify each Dirac
  -- singleton mass with the time-zero singleton indicator along the `τ`-orbit.
    calc
    (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω) {x} =
        ((n + 1 : ℕ) : ENNReal)⁻¹ * ∑ i : Fin (n + 1), (Measure.dirac (X i ω)) {x} := by
      simpa [Measure.smul_apply] using
        congrArg (fun μ : Measure E ↦ μ ({x} : Set E)) hEmpirical
    _ = ENNReal.ofReal ((n + 1 : ℝ)⁻¹) *
          ∑ i : Fin (n + 1),
            ENNReal.ofReal
              ((({x} : Set E).indicator (fun _ ↦ (1 : ℝ))) (X 0 ((τ^[i]) ω))) := by
      simp_rw [hInv, hDirac]
    _ = ENNReal.ofReal
          (((n + 1 : ℝ)⁻¹) *
            ∑ i : Fin (n + 1),
              (({x} : Set E).indicator (fun _ ↦ (1 : ℝ))) (X 0 ((τ^[i]) ω))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [← ENNReal.ofReal_mul' hIndicatorNonneg]
      · intro i hi
        by_cases hx : X 0 ((τ^[i]) ω) = x
        · simp [hx]
        · simp [hx]
    _ = ENNReal.ofReal
          (birkhoffAverage ℝ τ
            (fun ω' ↦ ({x} : Set E).indicator (fun _ ↦ (1 : ℝ)) (X 0 ω'))
            (n + 1) ω) := by
      rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
      congr 1
      rw [← Fin.sum_univ_eq_sum_range]
      norm_num
  simpa using congrArg ENNReal.toNNReal hENN

/-- Helper for Example 20.17: under the stationary mixture law `stationaryLaw P π`, the time-zero
singleton event `{ω | X 0 ω = x}` has probability `π {x}`. -/
private lemma stationaryLaw_zeroCoordinateSingleton_eq_invariantMass
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {π : ProbabilityMeasure E} (x : E) :
    stationaryLaw P π (X 0 ⁻¹' ({x} : Set E)) = π {x} := by
  have hX0Meas : Measurable (X 0) :=
    (inferInstance : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 0
  have hInitial :
      ∀ y : E, (P y : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = (Measure.dirac y) {x} := by
    intro y
    simpa [Measure.map_apply hX0Meas (measurableSet_singleton x)] using
      congrArg (fun μ : Measure E ↦ μ ({x} : Set E))
        ((inferInstance : IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).initial_eq y)
  have hA : MeasurableSet (X 0 ⁻¹' ({x} : Set E)) :=
    hX0Meas (measurableSet_singleton x)
  -- Proof comment: expand the stationary law as the weighted sum `∑ y, π{y} P_y`, then use the
  -- realization axiom at time `0` so the sum collapses to the Dirac singleton mass at `x`.
  rw [stationaryLaw_eq_sum, Measure.sum_apply _ hA]
  calc
    ∑' i : E, (((π : Measure E) ({i} : Set E)) • (P i : Measure Ω))
        (X 0 ⁻¹' ({x} : Set E)) =
        ∑' i : E, (((π : Measure E) ({i} : Set E)) • Measure.dirac i) ({x} : Set E) := by
      simp_rw [Measure.smul_apply, hInitial]
    _ =
        (Measure.sum fun i : E ↦ ((π : Measure E) ({i} : Set E)) • Measure.dirac i)
          ({x} : Set E) := by
      rw [Measure.sum_apply _ (measurableSet_singleton x)]
    _ = π {x} := by
      exact
        (Measure.sum_smul_dirac_singleton
          (f := fun y : E ↦ ((π : Measure E) ({y} : Set E))) (a := x)).trans
          (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure π ({x} : Set E)).symm

/-- Helper for Example 20.17: the expectation of the time-zero singleton indicator under the
stationary law is exactly the invariant singleton mass `π {x}`. -/
private lemma stationaryLawExpectation_zeroIndicator_eq_invariantMass
    (p : E → E → ℝ≥0∞)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {π : ProbabilityMeasure E} (x : E) :
    Real.toNNReal
      (∫ ω, ({x} : Set E).indicator (fun _ ↦ (1 : ℝ)) (X 0 ω) ∂stationaryLaw P π) = π {x} := by
  let A : Set Ω := X 0 ⁻¹' ({x} : Set E)
  have hA : MeasurableSet A :=
    by
      simpa [A] using
        ((inferInstance : IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 0)
          (measurableSet_singleton x)
  have hIndicator :
      (fun ω ↦ ({x} : Set E).indicator (fun _ ↦ (1 : ℝ)) (X 0 ω)) =
        A.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases hx : X 0 ω = x
    · simp [A, hx]
    · simp [A, hx]
  -- Proof comment: rewrite the observable as the event indicator of `{X 0 = x}`, convert its
  -- expectation to the set integral of `1`, and then evaluate that event under the stationary law.
  have hENN :
      ENNReal.ofReal
        (∫ ω, ({x} : Set E).indicator (fun _ ↦ (1 : ℝ)) (X 0 ω) ∂stationaryLaw P π) =
        (π {x} : ℝ≥0∞) := by
    calc
      ENNReal.ofReal
          (∫ ω, ({x} : Set E).indicator (fun _ ↦ (1 : ℝ)) (X 0 ω) ∂stationaryLaw P π) =
        ENNReal.ofReal (∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω ∂stationaryLaw P π) := by
        simp [hIndicator]
      _ = ENNReal.ofReal (∫ ω in A, (1 : ℝ) ∂stationaryLaw P π) := by
        rw [integral_indicator hA]
      _ = stationaryLaw P π A := by
        rw [ofReal_setIntegral_one (stationaryLaw P π) A]
      _ = π {x} := by
        simpa [A] using stationaryLaw_zeroCoordinateSingleton_eq_invariantMass
          (P := P) (X := X) p (x := x) (π := π)
  simpa using congrArg ENNReal.toNNReal hENN

/-- Example 20.17: under the stationary law `P_π`, the singleton mass of the
empirical distribution of the first `n + 1` observations, equivalently the empirical occupation
frequency of each state, converges almost surely to the invariant mass of that state. -/
theorem occupationFrequency_ae_tendsto_invariantMass_of_irreducibleMarkovChain_positiveRecurrent
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure)
    (hshift : ∀ n : ℕ, X n = X 0 ∘ τ^[n]) (x : E) :
    ∀ᵐ ω ∂stationaryLaw P π,
      Tendsto
        (fun n : ℕ ↦ (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω) {x})
        atTop
        (nhds (π {x})) := by
  let μ : Measure Ω := stationaryLaw P π
  let f : Ω → ℝ := fun ω ↦ ({x} : Set E).indicator (fun _ ↦ (1 : ℝ)) (X 0 ω)
  have hA : MeasurableSet (X 0 ⁻¹' ({x} : Set E)) :=
    ((inferInstance : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 0)
      (measurableSet_singleton x)
  have hf_integrable : Integrable f (stationaryLaw P π) := by
    -- Proof comment: `f` is a bounded indicator on the probability space `stationaryLaw P π`.
    simpa [f] using (integrable_const (1 : ℝ)).indicator hA
  have hErgodic : Ergodic τ μ := by
    simpa [μ] using
      stationary_shift_ergodic_of_irreducible_positiveRecurrent hirr hπ hshift
  have hAverageAe :
      ∀ᵐ ω ∂μ, Tendsto (birkhoffAverage ℝ τ f · ω) atTop (nhds (μ[f])) := by
    simpa [μ] using
      (birkhoffAverage_tendsto_ae_expectation_of_ergodic
        (P := μ) (τ := τ) (f := f) hErgodic hf_integrable)
  have hAverageShiftAe :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ birkhoffAverage ℝ τ f (n + 1) ω) atTop (nhds (μ[f])) := by
    filter_upwards [hAverageAe] with ω hω
    -- Proof comment: the empirical law uses the first `n + 1` coordinates, so shift the Birkhoff
    -- convergence along `n ↦ n + 1`.
    simpa [Function.comp] using hω.comp (tendsto_add_atTop_nat 1)
  filter_upwards [hAverageShiftAe] with ω hω
  have hOfReal :
      Tendsto (fun n ↦ Real.toNNReal (birkhoffAverage ℝ τ f (n + 1) ω)) atTop
        (nhds (Real.toNNReal (μ[f]))) :=
    (continuous_real_toNNReal.tendsto _).comp hω
  have hEmpirical :
      (fun n : ℕ ↦ (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω) {x}) =
        fun n : ℕ ↦ Real.toNNReal (birkhoffAverage ℝ τ f (n + 1) ω) := by
    funext n
    simpa [f] using
      empiricalDistributionSingleton_eq_ofReal_birkhoffAverageZeroIndicator
        (X := X) (τ := τ) hshift x n ω
  have hExpectation : Real.toNNReal (μ[f]) = π {x} := by
    simpa [μ, f] using stationaryLawExpectation_zeroIndicator_eq_invariantMass
      (P := P) (X := X) p (x := x) (π := π)
  -- Proof comment: rewrite the pointwise empirical singleton masses via the Birkhoff bridge and
  -- identify the limiting expectation with the stationary singleton mass.
  have hOfReal' :
      Tendsto (fun n : ℕ ↦ (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω) {x}) atTop
        (nhds (Real.toNNReal (μ[f]))) := by
    refine hOfReal.congr' ?_
    exact Filter.Eventually.of_forall fun n => (congrFun hEmpirical n).symm
  simpa [hExpectation] using hOfReal'

end

end ProbabilityTheory
