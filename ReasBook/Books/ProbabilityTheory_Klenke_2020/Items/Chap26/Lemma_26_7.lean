/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n m : ℕ}

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "State" => EuclideanSpace ℝ (Fin n)
local notation "DriverState" => EuclideanSpace ℝ (Fin m)
local notation "ScalarProcess" => NNReal → Ω → ℝ
local notation "VectorProcess" => NNReal → Ω → State
local notation "BrownianProcess" => NNReal → Ω → DriverState
local notation "MatrixProcess" => NNReal → Ω → Matrix (Fin n) (Fin m) ℝ

variable {ℱ : TimeFiltration}

/-- Helper for Lemma 26.7: the deterministic-horizon stopped second moment of a scalar process is
the integrability of the time-integrated square up to that horizon. -/
def HasFiniteDeterministicSecondMoment
    (μ : Measure Ω) (H : ScalarProcess) (τ : Ω → ENNReal) : Prop :=
  Integrable (fun ω ↦
    ∫ s in Set.Icc (0 : ℝ) ((τ ω).toReal), (H s.toNNReal ω) ^ 2
    ) μ

/-- Helper for Lemma 26.7: the deterministic energy process of the matrix entry `(i,j)`. -/
def matrixEntryEnergyProcess
    (H : MatrixProcess) (i : Fin n) (j : Fin m) : ScalarProcess :=
  fun t ω ↦ ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (H s.toNNReal ω i j) ^ 2

/-- A `State`-valued process `N` realizes the matrix-valued Brownian Itô integral of `H`
against `W` when it is assembled coordinatewise from scalar processes whose compensated squares
and off-diagonal products have the martingale identities expected of scalar Itô integrals. -/
structure IsMatrixBrownianLocalItoIntegral
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : BrownianProcess) (H : MatrixProcess)
    (N : VectorProcess) where
  /-- The coordinate scalar processes whose row sums form the vector integral. -/
  Nij : Fin n → Fin m → ScalarProcess
  /-- Each scalar coordinate integral starts from `0`. -/
  zero : ∀ i : Fin n, ∀ j : Fin m, Nij i j 0 = 0
  /-- Each scalar coordinate integral has an `L²` terminal marginal at every deterministic time. -/
  terminal_memLpTwo :
    ∀ i : Fin n, ∀ j : Fin m, ∀ T : NNReal, MemLp (fun ω ↦ Nij i j T ω) 2 μ
  /-- The scalar compensated square is a martingale. -/
  squareCompensator_martingale :
    ∀ i : Fin n, ∀ j : Fin m,
      Martingale
        (fun t ω ↦ (Nij i j t ω) ^ 2 - matrixEntryEnergyProcess H i j t ω)
        ℱ μ
  /-- Distinct driver coordinates yield martingale cross products. -/
  crossProduct_martingale :
    ∀ i : Fin n, ∀ j k : Fin m, j ≠ k →
      Martingale
        (fun t ω ↦ Nij i j t ω * Nij i k t ω)
        ℱ μ
  /-- The vector-valued integral is the rowwise sum of the scalar coordinate integrals. -/
  sum_eq :
    ∀ t : NNReal, ∀ ω : Ω, ∀ i : Fin n, N t ω i = ∑ j : Fin m, Nij i j t ω

/-- Helper for Lemma 26.7: the squared Frobenius norm of a real matrix is the sum of the entry
squares. -/
lemma frobeniusNorm_sq_eq_sum_entries_sq
    (A : Matrix (Fin n) (Fin m) ℝ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  have hnonneg : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
    refine Finset.sum_nonneg fun i _ ↦ ?_
    exact Finset.sum_nonneg fun j _ ↦ by positivity
  calc
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
      rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
    _ = ∑ i, ∑ j, (A i j) ^ 2 := by
      simp [sq_abs]

/-- Helper for Lemma 26.7: the scalar terminal second moment equals the time-integrated entry
energy when the compensated square is a martingale. -/
lemma scalarIntegralSecondMoment_eq_energy
    {W : BrownianProcess} {H : MatrixProcess} {N : VectorProcess}
    (hN :
      IsMatrixBrownianLocalItoIntegral ℱ μ W H N)
    (hH_second :
      ∀ i : Fin n, ∀ j : Fin m, ∀ T : NNReal, 0 < T →
        HasFiniteDeterministicSecondMoment μ (fun t ω ↦ H t ω i j) fun _ ↦ (T : ENNReal))
    (i : Fin n) (j : Fin m) (T : NNReal) :
    ∫ ω, (hN.Nij i j T ω) ^ 2 ∂μ =
      ∫ ω, matrixEntryEnergyProcess H i j T ω ∂μ := by
  have hSqInt : Integrable (fun ω ↦ (hN.Nij i j T ω) ^ 2) μ :=
    (hN.terminal_memLpTwo i j T).integrable_sq
  have hEnergyInt :
      Integrable (fun ω ↦ matrixEntryEnergyProcess H i j T ω) μ := by
    by_cases hT0 : T = 0
    · subst hT0
      simp [matrixEntryEnergyProcess]
    · have hTpos : 0 < T := pos_iff_ne_zero.mpr hT0
      simpa [HasFiniteDeterministicSecondMoment, matrixEntryEnergyProcess] using
        hH_second i j T hTpos
  have hCompInt :
      Integrable
        (fun ω ↦ (hN.Nij i j T ω) ^ 2 - matrixEntryEnergyProcess H i j T ω) μ :=
    (hN.squareCompensator_martingale i j).integrable T
  have hCompZero :
      ∫ ω, ((hN.Nij i j T ω) ^ 2 - matrixEntryEnergyProcess H i j T ω) ∂μ = 0 := by
    calc
      ∫ ω, ((hN.Nij i j T ω) ^ 2 - matrixEntryEnergyProcess H i j T ω) ∂μ =
          ∫ ω, ((hN.Nij i j 0 ω) ^ 2 - matrixEntryEnergyProcess H i j 0 ω) ∂μ := by
            simpa using
              ((hN.squareCompensator_martingale i j).setIntegral_eq
                (i := (0 : NNReal)) (j := T)
                (show (0 : NNReal) ≤ T from zero_le T)
                (s := Set.univ) MeasurableSet.univ).symm
      _ = 0 := by
        simp [matrixEntryEnergyProcess, hN.zero i j]
  have hDiff :
      ∫ ω, ((hN.Nij i j T ω) ^ 2 - matrixEntryEnergyProcess H i j T ω) ∂μ =
        ∫ ω, (hN.Nij i j T ω) ^ 2 ∂μ -
          ∫ ω, matrixEntryEnergyProcess H i j T ω ∂μ := by
    simpa using integral_sub hSqInt hEnergyInt
  linarith

/-- Helper for Lemma 26.7: the off-diagonal terminal mixed moment vanishes once the product
process is a martingale. -/
lemma scalarIntegralCrossMoment_eq_zero
    {W : BrownianProcess} {H : MatrixProcess} {N : VectorProcess}
    (hN :
      IsMatrixBrownianLocalItoIntegral ℱ μ W H N)
    (i : Fin n) (j k : Fin m) (T : NNReal) (hjk : j ≠ k) :
    (∫ ω, hN.Nij i j T ω * hN.Nij i k T ω ∂μ : ℝ) = 0 := by
  -- Proof comment: the martingale product has the same integral at time `T` as at time `0`,
  -- and both factors vanish at time `0`.
  calc
    (∫ ω, hN.Nij i j T ω * hN.Nij i k T ω ∂μ : ℝ) =
        ∫ ω, hN.Nij i j 0 ω * hN.Nij i k 0 ω ∂μ := by
          simpa using
            ((hN.crossProduct_martingale i j k hjk).setIntegral_eq
              (i := (0 : NNReal)) (j := T)
              (show (0 : NNReal) ≤ T from zero_le T)
              (s := Set.univ) MeasurableSet.univ).symm
    _ = 0 := by
      simp [hN.zero i j, hN.zero i k]

/-- Helper for Lemma 26.7: a fixed row contributes the sum of the entrywise scalar energies once
the off-diagonal mixed moments vanish. -/
lemma rowIntegralSecondMoment_eq_sumEntryEnergies
    {W : BrownianProcess} {H : MatrixProcess} {N : VectorProcess}
    (hN :
      IsMatrixBrownianLocalItoIntegral ℱ μ W H N)
    (hH_second :
      ∀ i : Fin n, ∀ j : Fin m, ∀ T : NNReal, 0 < T →
        HasFiniteDeterministicSecondMoment μ (fun t ω ↦ H t ω i j) fun _ ↦ (T : ENNReal))
    (i : Fin n) (T : NNReal) :
    ∫ ω, (N T ω i) ^ 2 ∂μ =
      ∑ j : Fin m, ∫ ω, matrixEntryEnergyProcess H i j T ω ∂μ := by
  calc
    ∫ ω, (N T ω i) ^ 2 ∂μ = ∫ ω, (∑ j : Fin m, hN.Nij i j T ω) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [hN.sum_eq T ω i]
    _ = ∫ ω, ∑ j : Fin m, ∑ k : Fin m, hN.Nij i j T ω * hN.Nij i k T ω ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [pow_two, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ j : Fin m, ∑ k : Fin m, ∫ ω, hN.Nij i j T ω * hN.Nij i k T ω ∂μ := by
      rw [integral_finset_sum]
      intro j _hj
      rw [integral_finset_sum]
      intro k _hk
      exact
        (hN.terminal_memLpTwo i j T).integrable_mul
          (hN.terminal_memLpTwo i k T).integrable
    _ = ∑ j : Fin m, ∫ ω, (hN.Nij i j T ω) ^ 2 ∂μ := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _hk hkj
        exact scalarIntegralCrossMoment_eq_zero (hN := hN) i j k T hkj
      · simp
    _ = ∑ j : Fin m, ∫ ω, matrixEntryEnergyProcess H i j T ω ∂μ := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      exact scalarIntegralSecondMoment_eq_energy (hN := hN) hH_second i j T

/-- Helper for Lemma 26.7: the full vector integral satisfies the Hilbert--Schmidt energy identity
once the coordinatewise martingale identities are available. -/
lemma matrixIntegralSecondMoment_eq_hilbertSchmidt_energy
    {W : BrownianProcess} {H : MatrixProcess} {N : VectorProcess}
    (hN :
      IsMatrixBrownianLocalItoIntegral ℱ μ W H N)
    (hH_second :
      ∀ i : Fin n, ∀ j : Fin m, ∀ T : NNReal, 0 < T →
        HasFiniteDeterministicSecondMoment μ (fun t ω ↦ H t ω i j) fun _ ↦ (T : ENNReal))
    (T : NNReal) :
    ∫ ω, ‖N T ω‖ ^ 2 ∂μ =
      ∫ ω, ∫ s in Set.Icc (0 : ℝ) (T : ℝ), ‖H s.toNNReal ω‖ ^ 2 ∂volume ∂μ := by
  have hRowsMemLp :
      ∀ i : Fin n, MemLp (fun ω ↦ N T ω i) 2 μ := by
    intro i
    have hEq :
        (fun ω ↦ N T ω i) = fun ω ↦ ∑ j : Fin m, hN.Nij i j T ω := by
      funext ω
      rw [hN.sum_eq T ω i]
    rw [hEq]
    refine memLp_finset_sum _ fun j _hj ↦ ?_
    exact hN.terminal_memLpTwo i j T
  have hEnergyExpanded :
      ∫ ω, ∫ s in Set.Icc (0 : ℝ) (T : ℝ), ‖H s.toNNReal ω‖ ^ 2 ∂volume ∂μ =
        ∑ i : Fin n, ∑ j : Fin m, ∫ ω, matrixEntryEnergyProcess H i j T ω ∂μ := by
    calc
      ∫ ω, ∫ s in Set.Icc (0 : ℝ) (T : ℝ), ‖H s.toNNReal ω‖ ^ 2 ∂volume ∂μ =
          ∫ ω, ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            ∑ i : Fin n, ∑ j : Fin m, (H s.toNNReal ω i j) ^ 2 ∂volume ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              apply integral_congr_ae
              filter_upwards with s
              simpa [matrixEntryEnergyProcess] using
                frobeniusNorm_sq_eq_sum_entries_sq (H s.toNNReal ω)
      _ =
          ∫ ω,
            ∑ i : Fin n, ∑ j : Fin m,
              ∫ s in Set.Icc (0 : ℝ) (T : ℝ), (H s.toNNReal ω i j) ^ 2 ∂volume ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [integral_finset_sum]
          intro i _hi
          rw [integral_finset_sum]
          intro j _hj
          by_cases hT0 : T = 0
          · subst hT0
            simp
          · have hTpos : 0 < T := pos_iff_ne_zero.mpr hT0
            exact (hH_second i j T hTpos).integrableOn
      _ =
          ∑ i : Fin n, ∑ j : Fin m, ∫ ω, matrixEntryEnergyProcess H i j T ω ∂μ := by
          rw [integral_finset_sum]
          intro i _hi
          rw [integral_finset_sum]
          intro j _hj
          by_cases hT0 : T = 0
          · subst hT0
            simp [matrixEntryEnergyProcess]
          · have hTpos : 0 < T := pos_iff_ne_zero.mpr hT0
            simpa [HasFiniteDeterministicSecondMoment, matrixEntryEnergyProcess] using
              hH_second i j T hTpos
  calc
    ∫ ω, ‖N T ω‖ ^ 2 ∂μ = ∫ ω, ∑ i : Fin n, (N T ω i) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      simpa [EuclideanSpace.real_norm_sq_eq]
    _ = ∑ i : Fin n, ∫ ω, (N T ω i) ^ 2 ∂μ := by
      rw [integral_finset_sum]
      intro i _hi
      exact (hRowsMemLp i).integrable_sq
    _ = ∑ i : Fin n, ∑ j : Fin m, ∫ ω, matrixEntryEnergyProcess H i j T ω ∂μ := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simpa using rowIntegralSecondMoment_eq_sumEntryEnergies (hN := hN) hH_second i T
    _ = ∫ ω, ∫ s in Set.Icc (0 : ℝ) (T : ℝ), ‖H s.toNNReal ω‖ ^ 2 ∂volume ∂μ := by
      exact hEnergyExpanded.symm

-- Proof sketch: the hypothesis `hN` already packages the coordinatewise scalar Itô identities
-- needed for the vector-valued isometry, so the proof is the finite-dimensional expansion of the
-- Euclidean norm together with the Frobenius expansion of the Hilbert--Schmidt norm.
/-- Lemma 26.7: if `H` is a progressively measurable `n × m`-valued integrand whose entries have
finite expected time-integrated squares on every deterministic interval `[0,T]`, then the
terminal `ℝⁿ`-valued Brownian Itô integral `N` of the matrix integrand `H` has second moment
equal to the expected time integral of the squared Hilbert--Schmidt norm of `H`, expressed
canonically as the squared Frobenius norm of the matrix-valued integrand. -/
theorem matrix_brownianItoIntegral_secondMoment_eq_hilbertSchmidt_energy
    {W : BrownianProcess} {H : MatrixProcess} {N : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (hN : IsMatrixBrownianLocalItoIntegral ℱ μ W H N)
    (hH_second :
      ∀ i : Fin n, ∀ j : Fin m, ∀ T : NNReal, 0 < T →
        HasFiniteDeterministicSecondMoment μ (fun t ω ↦ H t ω i j) fun _ ↦ (T : ENNReal))
    (T : NNReal) :
    ∫ ω, ‖N T ω‖ ^ 2 ∂μ =
      ∫ ω, ∫ s in Set.Icc (0 : ℝ) (T : ℝ), ‖H s.toNNReal ω‖ ^ 2 ∂volume ∂μ := by
  let _ := hW
  exact matrixIntegralSecondMoment_eq_hilbertSchmidt_energy (hN := hN) hH_second T

end ProbabilityTheory
