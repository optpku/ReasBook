/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory.DiscreteMarkovChain

/-- The transition matrix of the three-state chain from Exercise 18.4.4, written on `Fin 3` with
indices `0`, `1`, `2` corresponding to the textbook states `1`, `2`, `3`. -/
def three_state_transition_matrix : Fin 3 → Fin 3 → ℝ≥0∞ :=
  ![![(1 : ℝ≥0∞) / 2, (1 : ℝ≥0∞) / 3, (1 : ℝ≥0∞) / 6],
    ![(1 : ℝ≥0∞) / 3, (1 : ℝ≥0∞) / 3, (1 : ℝ≥0∞) / 3],
    ![0, (3 : ℝ≥0∞) / 4, (1 : ℝ≥0∞) / 4]]

/-- The same transition matrix regarded as a real matrix for spectral computations. -/
abbrev three_state_transition_matrix_real : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j ↦ (three_state_transition_matrix i j).toReal

/-- The one-step kernel associated with the Exercise 18.4.4 transition matrix. -/
abbrev three_state_transition_kernel : Kernel (Fin 3) (Fin 3) :=
  discreteMatrixKernel three_state_transition_matrix

/-- Helper for Exercise 18.4.4: the `toReal` of a finite three-term `ℝ≥0∞` sum is the sum of the
three real masses. -/
theorem toReal_add_three {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) (hc : c ≠ ∞) :
    (a + b + c).toReal = a.toReal + b.toReal + c.toReal := by
  -- Proof comment: peel off the outer sum first and then rewrite the inner two-term sum.
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ha, hb⟩) hc, ENNReal.toReal_add ha hb]

-- Proof sketch: evaluate the three row sums of `three_state_transition_matrix`; they are
-- `1 / 2 + 1 / 3 + 1 / 6`, `1 / 3 + 1 / 3 + 1 / 3`, and `0 + 3 / 4 + 1 / 4`, each equal to `1`.
/-- The Exercise 18.4.4 transition matrix is stochastic. -/
theorem three_state_transition_matrix_isStochastic :
    IsStochasticMatrix three_state_transition_matrix := by
  intro i
  -- Proof comment: expand the `Fin 3` row sum and check the three rows by direct arithmetic.
  rw [tsum_fintype, Fin.sum_univ_three]
  fin_cases i
  · change ((1 : ℝ≥0∞) / 2 + (1 : ℝ≥0∞) / 3 + (1 : ℝ≥0∞) / 6 = 1)
    apply (ENNReal.toReal_eq_toReal_iff'
      (by simp) (by simp)).mp
    rw [toReal_add_three (by simp) (by simp) (by simp)]
    norm_num
  · change ((1 : ℝ≥0∞) / 3 + (1 : ℝ≥0∞) / 3 + (1 : ℝ≥0∞) / 3 = 1)
    apply (ENNReal.toReal_eq_toReal_iff'
      (by simp) (by simp)).mp
    rw [toReal_add_three (by simp) (by simp) (by simp)]
    norm_num
  · change (0 + (3 : ℝ≥0∞) / 4 + (1 : ℝ≥0∞) / 4 = 1)
    apply (ENNReal.toReal_eq_toReal_iff'
      (by simp [ENNReal.div_ne_top]) (by simp)).mp
    rw [toReal_add_three
      (by simp)
      (by exact ENNReal.div_ne_top (by simp) (by norm_num))
      (by exact ENNReal.div_ne_top (by simp) (by norm_num))]
    norm_num

/-- The weights of the invariant distribution of the three-state chain. -/
def three_state_invariant_weights : Fin 3 → ℝ≥0∞ :=
  ![(18 : ℝ≥0∞) / 61, (27 : ℝ≥0∞) / 61, (16 : ℝ≥0∞) / 61]

-- Proof sketch: evaluate the finite sum over the three states and simplify
-- `18 / 61 + 27 / 61 + 16 / 61 = 1`.
/-- The explicit invariant weights form a probability vector. -/
theorem three_state_invariant_weights_sum :
    Finset.univ.sum three_state_invariant_weights = 1 := by
  -- Proof comment: the finite sum over the three states is exactly `18 / 61 + 27 / 61 + 16 / 61`.
  rw [Fin.sum_univ_three]
  change ((18 : ℝ≥0∞) / 61 + (27 : ℝ≥0∞) / 61 + (16 : ℝ≥0∞) / 61 = 1)
  apply (ENNReal.toReal_eq_toReal_iff'
    (by simp [ENNReal.div_ne_top]) (by simp)).mp
  rw [toReal_add_three
    (by exact ENNReal.div_ne_top (by simp) (by norm_num))
    (by exact ENNReal.div_ne_top (by simp) (by norm_num))
    (by exact ENNReal.div_ne_top (by simp) (by norm_num))]
  norm_num

/-- For Exercise 18.4.4, the invariant distribution of the chain is the probability law assigning
masses `18 / 61`, `27 / 61`, and `16 / 61` to the states `1`, `2`, and `3`. -/
def three_state_invariant_distribution : ProbabilityMeasure (Fin 3) :=
  ⟨(PMF.ofFintype three_state_invariant_weights three_state_invariant_weights_sum).toMeasure,
    inferInstance⟩

/-- Helper for Exercise 18.4.4: evaluating the discrete kernel of the three-state chain on a
singleton recovers the corresponding transition-matrix entry. -/
theorem threeStateTransitionKernel_apply_singleton (i j : Fin 3) :
    three_state_transition_kernel i {j} = three_state_transition_matrix i j := by
  -- Proof comment: expand the kernel row as a weighted sum of Dirac masses and keep the `j`th
  -- summand.
  rw [three_state_transition_kernel, discreteMatrixKernel_apply]
  simpa using
    (Measure.sum_smul_dirac_singleton
      (f := fun k : Fin 3 ↦ three_state_transition_matrix i k) (a := j))

/-- Helper for Exercise 18.4.4: the explicit invariant distribution assigns singleton mass
`three_state_invariant_weights i` to the state `i`. -/
theorem threeStateInvariantDistribution_apply_singleton (i : Fin 3) :
    (three_state_invariant_distribution : Measure (Fin 3)) {i} =
      three_state_invariant_weights i := by
  -- Proof comment: unfold the probability measure and read off the singleton mass from the
  -- defining PMF.
  change
    ((PMF.ofFintype three_state_invariant_weights
      three_state_invariant_weights_sum).toMeasure) {i} =
      three_state_invariant_weights i
  exact
    PMF.toMeasure_apply_singleton
      (PMF.ofFintype three_state_invariant_weights three_state_invariant_weights_sum)
      i (measurableSet_singleton i)

/-- Helper for Exercise 18.4.4: the explicit weight vector is a stationary left eigenvector of the
three-state transition matrix. -/
theorem threeStateStationaryColumnMass (j : Fin 3) :
    ∑ i : Fin 3, three_state_invariant_weights i * three_state_transition_matrix i j =
      three_state_invariant_weights j := by
  -- Proof comment: check the three column-balance equations by expanding the finite sum.
  rw [Fin.sum_univ_three]
  fin_cases j
  · change
      (18 : ℝ≥0∞) / 61 * ((1 : ℝ≥0∞) / 2) +
          (27 : ℝ≥0∞) / 61 * ((1 : ℝ≥0∞) / 3) +
            (16 : ℝ≥0∞) / 61 * 0 =
        (18 : ℝ≥0∞) / 61
    apply
      (ENNReal.toReal_eq_toReal_iff'
        (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])
        (by exact ENNReal.div_ne_top (by simp) (by norm_num))).mp
    rw [toReal_add_three
      (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])
      (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])
      (by simp)]
    norm_num
  · change
      (18 : ℝ≥0∞) / 61 * ((1 : ℝ≥0∞) / 3) +
          (27 : ℝ≥0∞) / 61 * ((1 : ℝ≥0∞) / 3) +
            (16 : ℝ≥0∞) / 61 * ((3 : ℝ≥0∞) / 4) =
        (27 : ℝ≥0∞) / 61
    apply
      (ENNReal.toReal_eq_toReal_iff'
        (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])
        (by exact ENNReal.div_ne_top (by simp) (by norm_num))).mp
    rw [toReal_add_three
      (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])
      (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])
      (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])]
    norm_num
  · change
      (18 : ℝ≥0∞) / 61 * ((1 : ℝ≥0∞) / 6) +
          (27 : ℝ≥0∞) / 61 * ((1 : ℝ≥0∞) / 3) +
            (16 : ℝ≥0∞) / 61 * ((1 : ℝ≥0∞) / 4) =
        (16 : ℝ≥0∞) / 61
    apply
      (ENNReal.toReal_eq_toReal_iff'
        (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])
        (by exact ENNReal.div_ne_top (by simp) (by norm_num))).mp
    rw [toReal_add_three
      (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])
      (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])
      (by simp [ENNReal.mul_ne_top, ENNReal.div_ne_top])]
    norm_num

-- Proof sketch: compute the image of `three_state_invariant_distribution` under the one-step
-- kernel `three_state_transition_kernel`; the stationarity equations reduce to the three linear
-- identities defining the weights `18 / 61`, `27 / 61`, and `16 / 61`.
/-- The explicit law with weights `18 / 61`, `27 / 61`, and `16 / 61` is invariant for the
one-step kernel of the chain. -/
theorem three_state_invariant_distribution_isInvariant :
    Kernel.Invariant three_state_transition_kernel
      (three_state_invariant_distribution : Measure (Fin 3)) := by
  rw [Kernel.Invariant]
  refine Measure.ext_of_singleton ?_
  intro j
  -- Proof comment: compare singleton masses after one step and reduce the claim to the stationary
  -- column identity for the explicit weight vector.
  rw [Measure.bind_apply (measurableSet_singleton j) (Kernel.aemeasurable _)]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [threeStateTransitionKernel_apply_singleton,
    threeStateInvariantDistribution_apply_singleton]
  calc
    ∑ i : Fin 3, three_state_transition_matrix i j * three_state_invariant_weights i =
        ∑ i : Fin 3, three_state_invariant_weights i * three_state_transition_matrix i j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [mul_comm]
    _ = three_state_invariant_weights j := threeStateStationaryColumnMass j

/-- For Exercise 18.4.4, the exponential convergence rate of the chain is
`(1 + √41) / 24`. -/
def three_state_exponential_convergence_rate : ℝ :=
  (1 + Real.sqrt 41) / 24

/-- Helper for Exercise 18.4.4: the real matrix used for the spectral calculation is exactly the
explicit `3 × 3` matrix with the stated rational entries. -/
theorem threeStateTransitionMatrixReal_eq_explicit :
    three_state_transition_matrix_real =
      !![(1 : ℝ) / 2, (1 : ℝ) / 3, (1 : ℝ) / 6;
        (1 : ℝ) / 3, (1 : ℝ) / 3, (1 : ℝ) / 3;
        0, (3 : ℝ) / 4, (1 : ℝ) / 4] := by
  -- Proof comment: evaluate the `ENNReal.toReal` entries of the transition matrix one by one.
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [three_state_transition_matrix_real,
    three_state_transition_matrix]

/-- Helper for Exercise 18.4.4: the characteristic polynomial of the real transition matrix splits
with roots `1`, `(1 - √41) / 24`, and `three_state_exponential_convergence_rate`. -/
theorem threeStateTransitionMatrixReal_charpoly :
    three_state_transition_matrix_real.charpoly =
      (Polynomial.X - Polynomial.C (1 : ℝ)) *
        (Polynomial.X - Polynomial.C ((1 - Real.sqrt 41) / 24)) *
          (Polynomial.X - Polynomial.C three_state_exponential_convergence_rate) := by
  have hsqrt : (0 : ℝ) ≤ 41 := by positivity
  -- Proof comment: first compute the characteristic polynomial of the explicit matrix, then
  -- normalize the factored form by the quadratic identities for the two nontrivial roots.
  calc
    three_state_transition_matrix_real.charpoly =
        Polynomial.X ^ 3 - Polynomial.C (13 / 12 : ℝ) * Polynomial.X ^ 2 +
          Polynomial.C (1 / 72 : ℝ) * Polynomial.X + Polynomial.C (5 / 72 : ℝ) := by
          apply Polynomial.funext
          intro x
          rw [threeStateTransitionMatrixReal_eq_explicit]
          simp [Matrix.charpoly, Matrix.det_fin_three, pow_two]
          ring_nf
    _ =
        (Polynomial.X - Polynomial.C (1 : ℝ)) *
          (Polynomial.X - Polynomial.C ((1 - Real.sqrt 41) / 24)) *
            (Polynomial.X - Polynomial.C three_state_exponential_convergence_rate) := by
          apply Polynomial.funext
          intro x
          rw [three_state_exponential_convergence_rate]
          simp
          field_simp [Real.sq_sqrt hsqrt]
          ring_nf
          rw [Real.sq_sqrt hsqrt]
          ring_nf

-- Proof sketch: compute the characteristic polynomial of `three_state_transition_matrix_real`,
-- factor it as `(x - 1) * (72 x^2 - 6 x - 5) / 72`, and solve the quadratic factor. The two
-- nontrivial eigenvalues are `(1 ± √41) / 24`, so the spectral decay rate is the larger modulus
-- `(1 + √41) / 24`.
/-- Exercise 18.4.4: the real spectrum of the transition matrix consists of `1` and the two
nontrivial eigenvalues `(1 - √41) / 24` and `(1 + √41) / 24`. -/
theorem three_state_spectrum_eq :
    spectrum ℝ three_state_transition_matrix_real =
      ({1, (1 - Real.sqrt 41) / 24, three_state_exponential_convergence_rate} : Set ℝ) := by
  ext x
  -- Proof comment: transport spectrum membership to the characteristic polynomial and split the
  -- resulting product of linear factors.
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, threeStateTransitionMatrixReal_charpoly]
  simp only [Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [mul_eq_zero, mul_eq_zero]
  constructor
  · intro hx
    rcases hx with (h1 | h2) | h3
    · exact Or.inl <| sub_eq_zero.mp h1
    · exact Or.inr <| Or.inl <| sub_eq_zero.mp h2
    · exact Or.inr <| Or.inr <| sub_eq_zero.mp h3
  · intro hx
    rcases hx with h1 | (h2 | h3)
    · exact Or.inl <| Or.inl <| sub_eq_zero.mpr h1
    · exact Or.inl <| Or.inr <| sub_eq_zero.mpr h2
    · exact Or.inr <| sub_eq_zero.mpr h3

end ProbabilityTheory.DiscreteMarkovChain
