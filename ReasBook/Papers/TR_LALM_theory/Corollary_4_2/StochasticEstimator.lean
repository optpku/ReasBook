/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StochasticMoments

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace LALM.Correction.StochasticRun

universe u v

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+}

/-- Helper for Corollary 4.2: the corrected point-displacement mean square is
the expected squared distance between consecutive corrected points. -/
@[expose] noncomputable def pointDisplacementMeanSquare
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) : ℝ :=
  ∫ ω, ‖run.point (k + 1) ω - run.point k ω‖ ^ 2 ∂P

/-- Helper for Corollary 4.2: the corrected point-displacement moment exposes
its defining Bochner integral. -/
theorem pointDisplacementMeanSquare_def
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) :
    run.pointDisplacementMeanSquare k =
      ∫ ω, ‖run.point (k + 1) ω - run.point k ω‖ ^ 2 ∂P := by
  -- Expose the proof-free displacement-moment definition.
  rfl

/-- Helper for Corollary 4.2: an admissible corrected transition is dominated
pointwise by the corrected displacement factor times its base step. -/
theorem pointDisplacementSquare_le_baseStep
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N) (hk : k < N)
    (ω : Ω) :
    ‖run.point (k + 1) ω - run.point k ω‖ ^ 2 ≤
      displacementFactor h params.delta ^ 2 * ‖run.baseStep k ω‖ ^ 2 := by
  -- Apply the deterministic corrected-displacement estimate on this sample path.
  have hadmissible :=
    (run.isAdmissiblePrefix_iff N).mp h_admissible k hk ω
  have hstep := (run.admissiblePrefix_normBounds N h_admissible).1 k hk ω
  have hdisplacement := displacement_le h params.delta
    (run.point k ω) (run.baseStep k ω) hadmissible hstep
  rw [← run.point_succ k ω] at hdisplacement
  have hfactorNonneg : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def]
    have hstepConstantNonneg : 0 ≤ stepConstant h := by
      rw [stepConstant_def]
      positivity
    exact add_nonneg (by norm_num)
      (mul_nonneg hstepConstantNonneg (NNReal.coe_nonneg params.delta))
  have hrightNonneg :
      0 ≤ displacementFactor h params.delta * ‖run.baseStep k ω‖ :=
    mul_nonneg hfactorNonneg (norm_nonneg _)
  -- Square the nonnegative norm comparison and normalize the product.
  calc
    ‖run.point (k + 1) ω - run.point k ω‖ ^ 2 ≤
        (displacementFactor h params.delta * ‖run.baseStep k ω‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hrightNonneg).2 hdisplacement
    _ = displacementFactor h params.delta ^ 2 * ‖run.baseStep k ω‖ ^ 2 := by
      ring

/-- Helper for Corollary 4.2: corrected point-displacement squares are
integrable below a pathwise admissible horizon. -/
theorem integrable_pointDisplacementSquare
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N) (hk : k < N) :
    Integrable (fun ω ↦ ‖run.point (k + 1) ω - run.point k ω‖ ^ 2) P := by
  -- Use the integrable corrected base-step square as a pointwise majorant.
  have hmajorant : Integrable (fun ω ↦
      displacementFactor h params.delta ^ 2 * ‖run.baseStep k ω‖ ^ 2) P :=
    (run.integrable_baseStepSquare h_admissible hk).const_mul
      (displacementFactor h params.delta ^ 2)
  have hmeasurable : AEStronglyMeasurable (fun ω ↦
      ‖run.point (k + 1) ω - run.point k ω‖ ^ 2) P :=
    (((run.aemeasurable_point (k + 1)).sub
      (run.aemeasurable_point k)).norm.pow_const 2).aestronglyMeasurable
  refine Integrable.mono' hmajorant hmeasurable ?_
  filter_upwards [] with ω
  have hbound := run.pointDisplacementSquare_le_baseStep h_admissible hk ω
  have hleftNonneg :
      0 ≤ ‖run.point (k + 1) ω - run.point k ω‖ ^ 2 := sq_nonneg _
  have hrightNonneg :
      0 ≤ displacementFactor h params.delta ^ 2 * ‖run.baseStep k ω‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  simpa only [Real.norm_of_nonneg hleftNonneg,
    Real.norm_of_nonneg hrightNonneg] using hbound

/-- Helper for Corollary 4.2: every corrected point-displacement mean square
is nonnegative. -/
theorem pointDisplacementMeanSquare_nonneg
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) :
    0 ≤ run.pointDisplacementMeanSquare k := by
  -- Integrate the pointwise nonnegative squared norm.
  rw [run.pointDisplacementMeanSquare_def]
  exact integral_nonneg fun ω ↦ sq_nonneg _

/-- Helper for Corollary 4.2: one admissible corrected displacement moment is
bounded by the corresponding corrected base-step moment. -/
theorem pointDisplacementMeanSquare_le_baseStep
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N) (hk : k < N) :
    run.pointDisplacementMeanSquare k ≤
      displacementFactor h params.delta ^ 2 * run.baseStepMeanSquare k := by
  -- Integrate the pointwise displacement estimate using the base-step majorant.
  rw [run.pointDisplacementMeanSquare_def, run.baseStepMeanSquare_def]
  have hbaseIntegrable := run.integrable_baseStepSquare h_admissible hk
  have hmajorant : Integrable (fun ω ↦
      displacementFactor h params.delta ^ 2 * ‖run.baseStep k ω‖ ^ 2) P :=
    hbaseIntegrable.const_mul (displacementFactor h params.delta ^ 2)
  calc
    (∫ ω, ‖run.point (k + 1) ω - run.point k ω‖ ^ 2 ∂P) ≤
        ∫ ω, displacementFactor h params.delta ^ 2 *
          ‖run.baseStep k ω‖ ^ 2 ∂P :=
      integral_mono_of_nonneg
        (ae_of_all P fun ω ↦ sq_nonneg _)
        hmajorant
        (ae_of_all P fun ω ↦
          run.pointDisplacementSquare_le_baseStep h_admissible hk ω)
    _ = displacementFactor h params.delta ^ 2 *
        ∫ ω, ‖run.baseStep k ω‖ ^ 2 ∂P := by
      rw [integral_const_mul]

/-- Helper for Corollary 4.2: accumulated corrected point displacement is
bounded by the corrected displacement factor times accumulated base-step size. -/
theorem sumPointDisplacementMeanSquare_le_baseStep
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) (h_admissible : run.IsAdmissiblePrefix K) :
    ∑ k ∈ Finset.range K, run.pointDisplacementMeanSquare k ≤
      displacementFactor h params.delta ^ 2 *
        ∑ k ∈ Finset.range K, run.baseStepMeanSquare k := by
  -- Sum the fixed-index displacement estimates over the common prefix.
  calc
    ∑ k ∈ Finset.range K, run.pointDisplacementMeanSquare k ≤
        ∑ k ∈ Finset.range K,
          displacementFactor h params.delta ^ 2 * run.baseStepMeanSquare k := by
      exact Finset.sum_le_sum fun k hk ↦
        run.pointDisplacementMeanSquare_le_baseStep h_admissible
          (Finset.mem_range.mp hk)
    _ = displacementFactor h params.delta ^ 2 *
        ∑ k ∈ Finset.range K, run.baseStepMeanSquare k := by
      rw [Finset.mul_sum]

/-- Helper for Corollary 4.2: summing the prefixes since each latest refresh
counts every nonnegative moment at most once per position in a refresh block. -/
lemma sumBlockPrefixes_le (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (q K : ℕ) (hq : 0 < q) :
    ∑ k ∈ Finset.range K, ∑ j ∈ Finset.Ico (k - k % q) k, a j ≤
      (q : ℝ) * ∑ j ∈ Finset.range K, a j := by
  classical
  -- Rewrite every block prefix as a filtered sum over the common horizon.
  have interval_eq_filter (k : ℕ) (hk : k ∈ Finset.range K) :
      Finset.Ico (k - k % q) k =
        (Finset.range K).filter (fun j ↦ j ∈ Finset.Ico (k - k % q) k) := by
    have hk' : k < K := Finset.mem_range.mp hk
    ext j
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    omega
  calc
    ∑ k ∈ Finset.range K, ∑ j ∈ Finset.Ico (k - k % q) k, a j =
        ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
          if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        ∑ j ∈ Finset.Ico (k - k % q) k, a j =
            ∑ j ∈ (Finset.range K).filter
              (fun j ↦ j ∈ Finset.Ico (k - k % q) k), a j :=
          congrArg (fun s : Finset ℕ ↦ ∑ j ∈ s, a j) (interval_eq_filter k hk)
        _ = ∑ j ∈ Finset.range K,
              if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
          exact Finset.sum_filter (fun j ↦ j ∈ Finset.Ico (k - k % q) k) a
    _ = ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
          if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ Finset.range K, (q : ℝ) * a j := by
      apply Finset.sum_le_sum
      intro j hj
      have hsubset :
          (Finset.range K).filter (fun k ↦ j ∈ Finset.Ico (k - k % q) k) ⊆
            Finset.Ioc j (j + q) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
          Finset.mem_Ioc] at hk ⊢
        have hmod : k % q < q := Nat.mod_lt k hq
        omega
      have hcard :
          ((Finset.range K).filter
            (fun k ↦ j ∈ Finset.Ico (k - k % q) k)).card ≤ q := by
        calc
          ((Finset.range K).filter
              (fun k ↦ j ∈ Finset.Ico (k - k % q) k)).card ≤
              (Finset.Ioc j (j + q)).card := Finset.card_le_card hsubset
          _ = q := by simp
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hcard) (ha j)
    _ = (q : ℝ) * ∑ j ∈ Finset.range K, a j := by
      rw [Finset.mul_sum]

/-- Helper for Corollary 4.2: once the raw SPIDER recursion is bounded since
the latest refresh, block counting and corrected displacement control give the
full accumulated gradient-error estimate. -/
theorem accumulatedGradientErrorMeanSquare_le_of_lastRefresh
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) (h_admissible : run.IsAdmissiblePrefix K)
    (h_lastRefresh : ∀ k < K,
      run.gradientErrorMeanSquare k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k,
              run.pointDisplacementMeanSquare j) :
    ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
      (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
        ((Q : ℝ) * (oracle.meanSquareLipschitz : ℝ) ^ 2 *
            displacementFactor h params.delta ^ 2 / (b : ℝ)) *
          ∑ k ∈ Finset.range K, run.baseStepMeanSquare k := by
  classical
  have hblockCount := sumBlockPrefixes_le run.pointDisplacementMeanSquare
    run.pointDisplacementMeanSquare_nonneg Q K Q.pos
  have hdisplacement := run.sumPointDisplacementMeanSquare_le_baseStep K h_admissible
  have hvarianceCoefficient :
      0 ≤ (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) := by
    positivity
  have hblockCoefficient :
      0 ≤ (Q : ℝ) * ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) hvarianceCoefficient
  -- Sum the latest-refresh estimates, count blocks, then transport displacement
  -- moments to corrected base-step moments exactly once.
  calc
    ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        ∑ k ∈ Finset.range K,
          ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                run.pointDisplacementMeanSquare j) := by
      exact Finset.sum_le_sum fun k hk ↦
        h_lastRefresh k (Finset.mem_range.mp hk)
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ k ∈ Finset.range K,
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                run.pointDisplacementMeanSquare j := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ((Q : ℝ) *
              ∑ k ∈ Finset.range K, run.pointDisplacementMeanSquare k) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left hblockCount hvarianceCoefficient) _
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          ((Q : ℝ) * ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))) *
            ∑ k ∈ Finset.range K, run.pointDisplacementMeanSquare k := by
      ring
    _ ≤ (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          ((Q : ℝ) * ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))) *
            (displacementFactor h params.delta ^ 2 *
              ∑ k ∈ Finset.range K, run.baseStepMeanSquare k) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left hdisplacement hblockCoefficient) _
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          ((Q : ℝ) * (oracle.meanSquareLipschitz : ℝ) ^ 2 *
              displacementFactor h params.delta ^ 2 / (b : ℝ)) *
            ∑ k ∈ Finset.range K, run.baseStepMeanSquare k := by
      ring

end LALM.Correction.StochasticRun

end
