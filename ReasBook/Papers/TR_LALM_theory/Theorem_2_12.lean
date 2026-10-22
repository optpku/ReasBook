/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import TR_LALM_theory.Assumption_2_5.Region
public import TR_LALM_theory.Definition_2_2.KKT
public import TR_LALM_theory.Lemma_2_11.Residual
public import TR_LALM_theory.Theorem_2_9.Lyapunov
public import TR_LALM_theory.Theorem_2_12.OperationalTrace
import TR_LALM_theory.Lemma_2_11
import TR_LALM_theory.Theorem_2_10

public section

open scoped BigOperators NNReal

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {ρ β : ℝ}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- The deterministic residual-complexity constant `C_det`, independent of the
iteration budget and target tolerance. -/
@[expose] noncomputable def deterministicComplexityConstant
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) : ℝ :=
  residualComparisonConstant h params.delta params.beta params.rho
      params.multiplierBound *
    (params.delta ^ 2 +
      8 * (run.lyapunov h params 1 - lyapunovLowerBound h params) / params.beta)

/-- The deterministic complexity constant has the source's explicit formula. -/
theorem deterministicComplexityConstant_def
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    deterministicComplexityConstant h params run =
      residualComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (params.delta ^ 2 +
          8 * (run.lyapunov h params 1 - lyapunovLowerBound h params) / params.beta) := rfl

/-- Under the deterministic-region condition, the deterministic complexity
constant is nonnegative. -/
theorem deterministicComplexityConstant_nonneg
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    0 ≤ deterministicComplexityConstant h params run := by
  -- Theorem 2.10 makes the first Lyapunov value admissible, so its gap is nonnegative.
  have hgap :
      0 ≤ run.lyapunov h params 1 - lyapunovLowerBound h params := by
    have hone : 1 ≤ (1 : ℕ) := Nat.le_refl 1
    have hlower :
        lyapunovLowerBound h params ≤ run.lyapunov h params 1 :=
      run.lyapunovLowerBound_le h params
        (run.allPrefixesAdmissible h params h_region 1) hone hone
    linarith
  -- Every factor in the residual comparison constant is nonnegative.
  have hmultiplierComparison :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hresidualComparison :
      0 ≤ residualComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [residualComparisonConstant_def]
    exact add_nonneg (sq_nonneg _)
      (div_nonneg hmultiplierComparison (sq_nonneg (params.rho : ℝ)))
  -- Multiply the nonnegative comparison factor by the nonnegative energy budget.
  have hbudgetNonneg :
      0 ≤ params.delta ^ 2 +
        8 * (run.lyapunov h params 1 - lyapunovLowerBound h params) / params.beta := by
    positivity
  rw [deterministicComplexityConstant_def]
  exact mul_nonneg hresidualComparison hbudgetNonneg

/-- A concrete deterministic iteration budget satisfying the source threshold,
with two initial iterations included so that the sampled interval is nonempty. -/
@[expose] noncomputable def deterministicIterationBudget
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (ε : ℝ≥0) : ℕ :=
  Nat.ceil (deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2) + 2

/-- The deterministic iteration budget is the ceiling of the exact residual
threshold, followed by two iterations ensuring a nonempty output range. -/
theorem deterministicIterationBudget_def
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (ε : ℝ≥0) :
    deterministicIterationBudget h params run ε =
      Nat.ceil (deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2) + 2 := rfl

/-- The concrete budget is at least two and meets the exact residual threshold
used by the `ε`-KKT theorem. -/
theorem deterministicIterationBudget_spec
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (ε : ℝ≥0) :
    2 ≤ deterministicIterationBudget h params run ε ∧
      deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2 ≤
        (deterministicIterationBudget h params run ε : ℝ) - 1 := by
  -- The two added initial iterations give the natural-number lower bound immediately.
  constructor
  · rw [deterministicIterationBudget_def]
    omega
  -- The ceiling dominates its real argument, and the extra two leave one unit of slack.
  · rw [deterministicIterationBudget_def]
    have hceiling := Nat.le_ceil
      (deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2)
    norm_num at hceiling ⊢
    linarith

/-- Helper for Theorem 2.12: adjoining the preceding terms of a nonnegative
sequence costs at most its initial term and one further copy of the sampled sum. -/
private lemma sumAdjacent_le (a : ℕ → ℝ) (K : ℕ) (hK : 2 ≤ K)
    (ha : ∀ k, 0 ≤ a k) :
    (∑ k ∈ Finset.Icc 1 (K - 1), (a k + a (k - 1))) ≤
      a 0 + 2 * ∑ k ∈ Finset.Icc 1 (K - 1), a k := by
  -- Rewrite the closed interval as the half-open interval used by range sums.
  have hinterval : Finset.Icc 1 (K - 1) = Finset.Ico 1 K := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hshift :
      (∑ k ∈ Finset.Icc 1 (K - 1), a (k - 1)) =
        ∑ k ∈ Finset.range (K - 1), a k := by
    rw [hinterval, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    omega
  -- Nonnegativity lets the shorter range embed in the range ending at `K`.
  have hrangeIndex : K - 1 ≤ K := by omega
  have hrange :
      (∑ k ∈ Finset.range (K - 1), a k) ≤ ∑ k ∈ Finset.range K, a k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hrangeIndex) (fun k _ _ ↦ ha k)
  have honeLeK : 1 ≤ K := by omega
  have hrangeSplit :
      (∑ k ∈ Finset.range K, a k) =
        a 0 + ∑ k ∈ Finset.Icc 1 (K - 1), a k := by
    rw [hinterval, Finset.sum_range_eq_add_Ico a honeLeK]
  -- Split the adjacent sum and apply the shifted-range estimate.
  rw [Finset.sum_add_distrib, hshift]
  linarith

/-- Helper for Theorem 2.12: a ceiling of a fixed multiple of `ε⁻²`, with a
fixed additive overhead, is `O(ε⁻²)` as `ε → 0⁺`. -/
private lemma natCeilQuadraticBudget_isBigO (C : ℝ) :
    (fun ε : ℝ≥0 ↦ ((Nat.ceil (C * (ε : ℝ)⁻¹ ^ 2) + 2 : ℕ) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- On the right neighborhood `0 < ε < 1`, the comparison function is at least one.
  refine Asymptotics.IsBigO.of_bound (|C| + 3) ?_
  have hzeroLtOne : (0 : ℝ≥0) < 1 := by norm_num
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds hzeroLtOne)] with ε hεpos hεone
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast hεpos
  have hεrealOne : (ε : ℝ) ≤ 1 := by
    exact_mod_cast hεone.le
  have hinverse : 1 ≤ (ε : ℝ)⁻¹ := (one_le_inv₀ hεreal).2 hεrealOne
  have hinverseSq : 1 ≤ (ε : ℝ)⁻¹ ^ 2 := by
    nlinarith
  have hinverseSqNonneg : 0 ≤ (ε : ℝ)⁻¹ ^ 2 := sq_nonneg _
  -- For nonnegative `C`, the ceiling estimate is absorbed by `(|C| + 3) ε⁻²`.
  by_cases hC : 0 ≤ C
  · have hargument : 0 ≤ C * (ε : ℝ)⁻¹ ^ 2 :=
      mul_nonneg hC hinverseSqNonneg
    have hceiling := Nat.ceil_lt_add_one hargument
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), Nat.cast_add, Nat.cast_ofNat,
      Real.norm_eq_abs, abs_of_nonneg hinverseSqNonneg, abs_of_nonneg hC]
    have hcoefficient : 0 ≤ C + 3 := by positivity
    nlinarith [mul_nonneg hcoefficient (sub_nonneg.mpr hinverseSq)]
  -- For negative `C`, the natural ceiling vanishes and only the fixed overhead remains.
  · have hargument : C * (ε : ℝ)⁻¹ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hinverseSqNonneg
    have hceiling : Nat.ceil (C * (ε : ℝ)⁻¹ ^ 2) = 0 :=
      Nat.ceil_eq_zero.mpr hargument
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    rw [hceiling, Nat.zero_add, Nat.cast_ofNat, Real.norm_eq_abs,
      abs_of_nonneg htwo, Real.norm_eq_abs, abs_of_nonneg hinverseSqNonneg]
    have hcoefficient : 0 ≤ |C| + 3 := by positivity
    calc
      (2 : ℝ) ≤ |C| + 3 := by linarith [abs_nonneg C]
      _ = (|C| + 3) * 1 := (mul_one _).symm
      _ ≤ (|C| + 3) * (ε : ℝ)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left hinverseSq hcoefficient

namespace Run

/-- Helper for Theorem 2.12: Lyapunov descent telescopes to a bound on all
sampled squared primal steps. -/
private lemma summedStepSq_le_lyapunovGap
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (K : ℕ) (hK : 2 ≤ K) :
    (∑ k ∈ Finset.Icc 1 (K - 1), ‖run.step k‖ ^ 2) ≤
      4 * (run.lyapunov h params 1 - lyapunovLowerBound h params) / params.beta := by
  have hinterval : Finset.Icc 1 (K - 1) = Finset.Ico 1 K := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  -- Sum the one-step descent inequalities over the complete sampled interval.
  have hdescent :
      (∑ k ∈ Finset.Icc 1 (K - 1),
          (params.beta / 4) * ‖run.step k‖ ^ 2) ≤
        ∑ k ∈ Finset.Icc 1 (K - 1),
          (run.lyapunov h params k - run.lyapunov h params (k + 1)) := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkBounds := Finset.mem_Icc.mp hk
    have hklt : k < K := by omega
    have hstep := run.lyapunovDescent h params
      (run.allPrefixesAdmissible h params h_region K) hkBounds.1 hklt
    linarith
  -- Range telescoping leaves exactly the initial-to-terminal Lyapunov gap.
  have htelescope :
      (∑ k ∈ Finset.Icc 1 (K - 1),
          (run.lyapunov h params k - run.lyapunov h params (k + 1))) =
        run.lyapunov h params 1 - run.lyapunov h params K := by
    have hendpointLeft : 1 + (K - 1) = K := by omega
    have hendpointRight : K - 1 + 1 = K := by omega
    rw [hinterval, Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hendpointLeft, hendpointRight] using
      (Finset.sum_range_sub' (fun k ↦ run.lyapunov h params (k + 1)) (K - 1))
  have hKpos : 1 ≤ K := by omega
  have hlower : lyapunovLowerBound h params ≤ run.lyapunov h params K :=
    run.lyapunovLowerBound_le h params
      (run.allPrefixesAdmissible h params h_region K) hKpos (Nat.le_refl K)
  have henergy :
      (params.beta / 4) *
          (∑ k ∈ Finset.Icc 1 (K - 1), ‖run.step k‖ ^ 2) ≤
        run.lyapunov h params 1 - lyapunovLowerBound h params := by
    rw [← Finset.mul_sum, htelescope] at hdescent
    linarith
  -- Divide by the positive proximal coefficient.
  have hscalingNonneg : 0 ≤ 4 / (params.beta : ℝ) := by positivity
  calc
    (∑ k ∈ Finset.Icc 1 (K - 1), ‖run.step k‖ ^ 2) =
        (4 / params.beta) *
          ((params.beta / 4) *
            ∑ k ∈ Finset.Icc 1 (K - 1), ‖run.step k‖ ^ 2) := by
      field_simp [run.beta_pos.ne']
    _ ≤ (4 / params.beta) *
        (run.lyapunov h params 1 - lyapunovLowerBound h params) :=
      mul_le_mul_of_nonneg_left henergy hscalingNonneg
    _ = 4 * (run.lyapunov h params 1 - lyapunovLowerBound h params) /
        params.beta := by ring

/-- Companion for Theorem 2.12: the minimum squared residual among iterations `1` through
`K - 1` is at most its uniform finite expectation. -/
theorem min_residual_sq_le_expect
    (run : Run f c ρ β x₀ multiplier₀) (K : ℕ) (hK : 2 ≤ K) :
    (Finset.Icc 1 (K - 1)).inf'
      (Finset.nonempty_Icc.mpr (Nat.le_sub_of_add_le hK))
      (fun k ↦ KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2) ≤
      𝔼 k ∈ Finset.Icc 1 (K - 1),
        KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 := by
  -- The finite infimum is below every sampled value, hence below their expectation.
  refine Finset.le_expect (Finset.nonempty_Icc.mpr (Nat.le_sub_of_add_le hK)) ?_
  intro k hk
  exact Finset.inf'_le _ hk

/-- Helper for Theorem 2.12: the sampled squared residuals are bounded by the
deterministic complexity constant before normalization by the sample count. -/
private lemma sumResidualSq_le_deterministicComplexityConstant
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (K : ℕ) (hK : 2 ≤ K) :
    (∑ k ∈ Finset.Icc 1 (K - 1),
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2) ≤
        deterministicComplexityConstant h params run := by
  have hresidualComparison :
      0 ≤ residualComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [residualComparisonConstant_def, multiplierPrimalConstant_def]
    positivity
  -- Sum Lemma 2.11 pointwise, keeping the residual construction opaque.
  have hpointwise :
      (∑ k ∈ Finset.Icc 1 (K - 1),
        KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2) ≤
      ∑ k ∈ Finset.Icc 1 (K - 1),
        residualComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkBounds := Finset.mem_Icc.mp hk
    have hklt : k < K := by omega
    exact run.residual_sq_le h params
      (run.allPrefixesAdmissible h params h_region K) hkBounds.1 hklt
  have hadjacent := sumAdjacent_le (fun k ↦ ‖run.step k‖ ^ 2) K hK
    (fun k ↦ sq_nonneg ‖run.step k‖)
  have hsteps := summedStepSq_le_lyapunovGap h params h_region run K hK
  have hdeltaNonneg : 0 ≤ (params.delta : ℝ) := by positivity
  have hinitial : ‖run.step 0‖ ^ 2 ≤ params.delta ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hdeltaNonneg).2
      (run.norm_step_le_global h params h_region 0)
  -- The adjacent-step estimate and the telescoped energy bound give the source constant.
  calc
    (∑ k ∈ Finset.Icc 1 (K - 1),
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2) ≤
        ∑ k ∈ Finset.Icc 1 (K - 1),
          residualComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound *
            (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := hpointwise
    _ = residualComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound *
          ∑ k ∈ Finset.Icc 1 (K - 1),
            (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ residualComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (‖run.step 0‖ ^ 2 +
            2 * ∑ k ∈ Finset.Icc 1 (K - 1), ‖run.step k‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hadjacent hresidualComparison
    _ ≤ residualComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (params.delta ^ 2 +
            2 * (4 * (run.lyapunov h params 1 - lyapunovLowerBound h params) /
              params.beta)) := by
      gcongr
    _ = deterministicComplexityConstant h params run := by
      rw [deterministicComplexityConstant_def]
      ring

/-- Theorem 2.12: under the deterministic assumptions, the uniform expected
squared residual decays as `C_det / (K - 1)`. -/
theorem expect_residual_sq_le
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (K : ℕ) (hK : 2 ≤ K) :
    (𝔼 k ∈ Finset.Icc 1 (K - 1),
        KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2) ≤
      deterministicComplexityConstant h params run / ((K : ℝ) - 1) := by
  have hsum :=
    sumResidualSq_le_deterministicComplexityConstant h params h_region run K hK
  have hcard : (Finset.Icc 1 (K - 1)).card = K - 1 := by
    simp only [Nat.card_Icc]
    omega
  have hKnat : 1 < K := by omega
  have hKreal : (1 : ℝ) < K := by exact_mod_cast hKnat
  have hdenominator : 0 < (K : ℝ) - 1 := by
    linarith
  -- Uniform expectation is the residual sum divided by the positive sample count.
  have honeLeK : 1 ≤ K := by omega
  rw [Finset.expect_eq_sum_div_card, hcard, Nat.cast_sub honeLeK, Nat.cast_one]
  exact (div_le_div_iff_of_pos_right hdenominator).2 hsum

/-- Consequence of Theorem 2.12: once the exact iteration threshold is met, a squared-residual
minimizer in the sampled range is an `ε`-KKT pair. -/
theorem existsApproximatePair_of_iterationBound
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (K : ℕ) (hK : 2 ≤ K) (ε : ℝ≥0) (ε_pos : 0 < ε)
    (h_iterations :
      deterministicComplexityConstant h params run * ε⁻¹ ^ 2 ≤ (K : ℝ) - 1) :
    ∃ k ∈ Finset.Icc 1 (K - 1),
      IsMinOn
          (fun j ↦ KKT.residual f c (run.point (j + 1)) (run.multiplier (j + 1)) ^ 2)
          (Finset.Icc 1 (K - 1)) k ∧
        KKT.IsApproximatePair f c ε (run.point (k + 1)) (run.multiplier (k + 1)) := by
  have hsample : (Finset.Icc 1 (K - 1)).Nonempty :=
    Finset.nonempty_Icc.mpr (Nat.le_sub_of_add_le hK)
  obtain ⟨k, hk, hmin⟩ := (Finset.Icc 1 (K - 1)).exists_min_image
    (fun j ↦ KKT.residual f c (run.point (j + 1)) (run.multiplier (j + 1)) ^ 2)
    hsample
  refine ⟨k, hk, hmin, ?_⟩
  -- Minimality bounds the chosen squared residual by the uniform expectation.
  have hminExpectation := Finset.le_expect hsample hmin
  have hrate := run.expect_residual_sq_le h params h_region K hK
  have hsquaredRate :
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 ≤
        deterministicComplexityConstant h params run / ((K : ℝ) - 1) :=
    hminExpectation.trans hrate
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast ε_pos
  have hKnat : 1 < K := by omega
  have hKreal : (1 : ℝ) < K := by exact_mod_cast hKnat
  have hdenominator : 0 < (K : ℝ) - 1 := by
    linarith
  -- Multiply the iteration threshold by `ε²` to cancel its inverse-square factor.
  have hiterationsReal :
      deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2 ≤
        (K : ℝ) - 1 := by
    simpa only [NNReal.coe_inv] using h_iterations
  have hscaled := mul_le_mul_of_nonneg_right hiterationsReal (sq_nonneg (ε : ℝ))
  have hinverseCancellation :
      deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2 * (ε : ℝ) ^ 2 =
        deterministicComplexityConstant h params run := by
    field_simp [hεreal.ne']
  rw [hinverseCancellation] at hscaled
  have hconstantDiv :
      deterministicComplexityConstant h params run / ((K : ℝ) - 1) ≤ (ε : ℝ) ^ 2 := by
    apply (div_le_iff₀ hdenominator).2
    nlinarith
  have hsquared :
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 ≤
        (ε : ℝ) ^ 2 := hsquaredRate.trans hconstantDiv
  -- Nonnegativity turns the squared estimate into the aggregate residual bound.
  have hresidualNonneg :
      0 ≤ KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) := by
    rw [KKT.residual_def]
    positivity
  have hresidual :
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ≤ (ε : ℝ) :=
    (sq_le_sq₀ hresidualNonneg ε.coe_nonneg).mp hsquared
  exact KKT.IsApproximatePair.of_residual_le hresidual

/-- Complexity consequence of Theorem 2.12: for fixed parameters and the
classical multiplier update, the concrete number of LALM iterations is
`O(ε⁻²)` as `ε → 0⁺`. -/
theorem iterationCount_isBigO
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    (fun ε : ℝ≥0 ↦
      (run.iterationCount (deterministicIterationBudget h params run ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- The operational specification identifies the count with the shared ceiling budget.
  simpa only [iterationCount_spec, deterministicIterationBudget_def] using
    natCeilQuadraticBudget_isBigO (deterministicComplexityConstant h params run)

/-- Complexity consequence of Theorem 2.12: for fixed parameters and the
classical multiplier update, the exact-gradient first-order oracle evaluation
count is `O(ε⁻²)` as `ε → 0⁺`. -/
theorem firstOrderOracleEvaluationCount_isBigO
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    (fun ε : ℝ≥0 ↦
      (run.firstOrderOracleEvaluationCount (deterministicIterationBudget h params run ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- One exact gradient evaluation is recorded at each transition in the shared budget.
  simpa only [firstOrderOracleEvaluationCount_spec, deterministicIterationBudget_def] using
    natCeilQuadraticBudget_isBigO (deterministicComplexityConstant h params run)

/-- Complexity consequence of Theorem 2.12: for fixed parameters and the
classical multiplier update, the exact Jacobian-induced linear-system solve
count is `O(ε⁻²)` as `ε → 0⁺`. -/
theorem jacobianLinearSystemSolveCount_isBigO
    (h : EqualityConstrained.Regularity f c) (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    (fun ε : ℝ≥0 ↦
      (run.jacobianLinearSystemSolveCount (deterministicIterationBudget h params run ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- One certified Jacobian-induced solve is recorded at each transition in the budget.
  simpa only [jacobianLinearSystemSolveCount_spec, deterministicIterationBudget_def] using
    natCeilQuadraticBudget_isBigO (deterministicComplexityConstant h params run)

end Run

end LALM

end
