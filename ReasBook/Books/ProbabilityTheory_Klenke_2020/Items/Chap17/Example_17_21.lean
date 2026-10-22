/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Remark_17_44
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped BigOperators ENNReal ProbabilityTheory unitInterval

noncomputable section

universe u

namespace ProbabilityTheory

variable (N : ℕ+)

/-- The type-`A` gene frequency corresponding to the count state `i ∈ {0, ..., N}`. -/
def wrightFrequency (i : Fin (N + 1)) : ℝ :=
  (i : ℝ) / N

/-- The Wright frequency lies in the unit interval. -/
theorem wrightFrequency_le_one (i : Fin (N + 1)) :
    Real.toNNReal (wrightFrequency N i) ≤ 1 := by
  have hN : (0 : ℝ) < N := by
    exact_mod_cast N.pos
  have hi_le : (i : ℝ) ≤ N := by
    exact_mod_cast Nat.le_of_lt_succ i.2
  have hfreq_le : wrightFrequency N i ≤ 1 := by
    calc
      wrightFrequency N i = (i : ℝ) / N := by rw [wrightFrequency]
      _ ≤ N / N := by
        exact div_le_div_of_nonneg_right hi_le hN.le
      _ = 1 := by
        field_simp [hN.ne']
  exact Real.toNNReal_le_one.2 hfreq_le

/-- Helper for Example 17.21: Wright frequencies are nonnegative because counts are nonnegative. -/
theorem wrightFrequency_nonneg (i : Fin (N + 1)) :
    0 ≤ wrightFrequency N i := by
  -- Proof comment: the frequency is the nonnegative count `i` divided by the positive population
  -- size `N`.
  rw [wrightFrequency]
  positivity

/-- Helper for Example 17.21: in Wright's evolution model with population size `N`, if the current type-`A`
frequency is `x = i / N`, then the next generation count has the canonical binomial law
`PMF.binomial x N`. This gives the one-step transition matrix on the finite state space
`Fin (N + 1)`. -/
def wrightTransitionMatrix : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞ :=
  fun i j ↦
    PMF.binomial (Real.toNNReal (wrightFrequency N i)) (wrightFrequency_le_one N i) N j

/-- Expanding `wrightTransitionMatrix` gives the canonical binomial row law of Wright's model. -/
theorem wrightTransitionMatrix_def (i j : Fin (N + 1)) :
    wrightTransitionMatrix N i j =
      PMF.binomial (Real.toNNReal (wrightFrequency N i)) (wrightFrequency_le_one N i) N j :=
  rfl

/-- The Wright transition matrix is stochastic. -/
theorem wrightTransitionMatrix_isStochasticMatrix :
    IsStochasticMatrix (wrightTransitionMatrix N) := by
  intro i
  simpa [wrightTransitionMatrix_def] using
    (PMF.tsum_coe
      (PMF.binomial (Real.toNNReal (wrightFrequency N i)) (wrightFrequency_le_one N i) N))

/-- The Wright frequency has bounded range on the finite state space. -/
theorem wrightFrequency_isBounded :
    Bornology.IsBounded (Set.range (wrightFrequency N)) := by
  exact (Set.toFinite _).isBounded

/-- Helper for Example 17.21: the finite binomial mass function on `range (n + 1)` has first
moment `x * n`. -/
private theorem binomialMeanSum (n : ℕ) {x : NNReal} (hx : x ≤ 1) :
    Finset.sum (Finset.range (n + 1))
      (fun k ↦ ((n.choose k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (n - k)) * (k : ℝ)) =
        (x : ℝ) * (n : ℝ) := by
  let p : unitInterval := ⟨(x : ℝ), by exact_mod_cast x.2, hx⟩
  calc
    Finset.sum (Finset.range (n + 1))
        (fun k ↦ ((n.choose k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (n - k)) * (k : ℝ))
      = ∫ t, t ∂Bin(ℝ, n, p) := by
          symm
          have hNat : ∀ᵐ k : ℕ ∂Bin(n, p), k ≤ n := by
            simpa using
              (ProbabilityTheory.ae_le_of_hasLaw_binomial (n := n) (p := p)
                (X := id) (P := Bin(n, p)) (ProbabilityTheory.HasLaw.id (μ := Bin(n, p))))
          have hInt : Integrable (fun k : ℕ ↦ (k : ℝ)) (Bin(n, p)) := by
            refine Integrable.of_bound (by fun_prop) (n : ℝ) ?_
            filter_upwards [hNat] with k hk
            simpa [Real.norm_eq_abs,
              abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by exact_mod_cast Nat.zero_le k)] using
              (show (k : ℝ) ≤ (n : ℝ) by exact_mod_cast hk)
          rw [show Bin(ℝ, n, p) = Measure.map (Nat.cast : ℕ → ℝ) (Bin(n, p)) by rfl]
          rw [integral_map measurableNatCastReal.aemeasurable (by fun_prop)]
          rw [integral_countable hInt]
          simp_rw [smul_eq_mul, Measure.real, binomial_apply_singleton_toReal]
          have htail :
              ∀ k, k ∉ Finset.range (n + 1) →
                ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) * k = 0 := by
            intro k hk
            have hk' : n < k := Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hk)
            simp [Nat.choose_eq_zero_of_lt hk']
          rw [tsum_eq_sum htail]
    _ = (x : ℝ) * (n : ℝ) := by
          simpa [p] using (binomialRealIntegralId_eq n p)

/-- Helper for Example 17.21: the real-form binomial mass is nonnegative on the unit interval. -/
private lemma binomialMassReal_nonneg (n k : ℕ) {x : NNReal} (hx : x ≤ 1) :
    0 ≤ (Nat.choose n k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (n - k) := by
  have hchoose_nonneg : 0 ≤ (Nat.choose n k : ℝ) := by
    exact_mod_cast Nat.zero_le (Nat.choose n k)
  have hx_nonneg : 0 ≤ (x : ℝ) := by
    exact_mod_cast x.2
  have hone_sub_nonneg : 0 ≤ 1 - (x : ℝ) := by
    exact sub_nonneg.mpr (show (x : ℝ) ≤ 1 by exact_mod_cast hx)
  -- Proof comment: each factor in the real binomial mass is nonnegative on `x ∈ [0, 1]`.
  exact mul_nonneg
    (mul_nonneg hchoose_nonneg (pow_nonneg hx_nonneg k))
    (pow_nonneg hone_sub_nonneg (n - k))

/-- Helper for Example 17.21: one Wright transition preserves the expected gene frequency. -/
lemma wrightFrequencyMeanStep (i : Fin (N + 1)) :
    (wrightTransitionMatrix N ⋆ᶠ wrightFrequency N) i = wrightFrequency N i := by
  have hsum :
      Summable (fun y : Fin (N + 1) ↦
        (wrightTransitionMatrix N i y).toReal * ‖wrightFrequency N y‖) := by
    simpa using
      (Summable.of_finite :
        Summable (fun y : Fin (N + 1) ↦
          (wrightTransitionMatrix N i y).toReal * ‖wrightFrequency N y‖))
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast N.ne_zero
  set x : NNReal := Real.toNNReal (wrightFrequency N i)
  have hx : x ≤ 1 := by
    simpa [x] using wrightFrequency_le_one N i
  have hx_nonneg : 0 ≤ wrightFrequency N i := by
    exact wrightFrequency_nonneg N i
  have hx_real : (x : ℝ) = wrightFrequency N i := by
    simp [x, Real.toNNReal_of_nonneg hx_nonneg]
  rw [integral_discreteMatrixKernel_eq_tsum
      (p := wrightTransitionMatrix N)
      (hp := wrightTransitionMatrix_isStochasticMatrix N)
      (f := wrightFrequency N) (x := i) hsum,
    tsum_fintype]
  have hrewrite :
      (∑ b : Fin (N + 1), (wrightTransitionMatrix N i b).toReal * wrightFrequency N b) =
        ∑ b : Fin (N + 1),
          ((Nat.choose N b : ℝ) * (x : ℝ) ^ (b : ℕ) * (1 - (x : ℝ)) ^ (N - (b : ℕ))) *
            ((b : ℝ) / N) := by
    refine Finset.sum_congr rfl ?_
    intro b hb
    have hb_le : (b : ℕ) ≤ N := Nat.le_of_lt_succ b.2
    have hprob :
        (wrightTransitionMatrix N i b).toReal =
          (Nat.choose N b : ℝ) * (x : ℝ) ^ (b : ℕ) * (1 - (x : ℝ)) ^ (N - (b : ℕ)) := by
      have hbin :
          wrightTransitionMatrix N i b =
            ENNReal.ofReal
              ((Nat.choose N b : ℝ) * (x : ℝ) ^ (b : ℕ) * (1 - (x : ℝ)) ^ (N - (b : ℕ))) := by
        simpa [wrightTransitionMatrix_def, mul_comm, mul_left_comm, mul_assoc] using
          (PMF.binomial_apply_of_le (b := N) (k := (b : ℕ)) (x := x) hb_le hx).symm
      have hbin_nonneg :
          0 ≤ (Nat.choose N b : ℝ) * (x : ℝ) ^ (b : ℕ) * (1 - (x : ℝ)) ^ (N - (b : ℕ)) := by
        -- Proof comment: rewrite the pmf mass through `ENNReal.toReal_ofReal` using the shared
        -- binomial nonnegativity bridge.
        exact binomialMassReal_nonneg N (b : ℕ) hx
      rw [hbin, ENNReal.toReal_ofReal hbin_nonneg]
    have hfreq :
        wrightFrequency N b = (b : ℝ) / N := by
      rw [wrightFrequency]
    rw [hprob, hfreq]
  calc
    ∑ b : Fin (N + 1), (wrightTransitionMatrix N i b).toReal * wrightFrequency N b
      = ∑ b : Fin (N + 1),
          ((Nat.choose N b : ℝ) * (x : ℝ) ^ (b : ℕ) * (1 - (x : ℝ)) ^ (N - (b : ℕ))) *
            ((b : ℝ) / N) := hrewrite
    _ = Finset.sum (Finset.range (N + 1))
          (fun k ↦ ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) * ((k : ℝ) / N)) := by
            simpa using
              (Fin.sum_univ_eq_sum_range
                (fun k : ℕ ↦
                  ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                    ((k : ℝ) / N)) (N + 1))
    _ = (1 / N : ℝ) *
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) * (k : ℝ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [div_eq_mul_inv]
            ring
    _ = (1 / N : ℝ) * (x * N) := by
          rw [binomialMeanSum N hx]
    _ = (x : ℝ) := by
          field_simp [hN]
    _ = wrightFrequency N i := by
          simpa [hx_real] using hx_real

/-- The Wright frequency is harmonic for the Wright transition matrix. -/
theorem wrightFrequency_isHarmonic :
    IsHarmonic (discreteMatrixKernel (wrightTransitionMatrix N)) (wrightFrequency N) := by
  refine (isHarmonic_iff_rightEigenvectorAtOne
    (p := wrightTransitionMatrix N)
    (hp := wrightTransitionMatrix_isStochasticMatrix N)
    (f := wrightFrequency N)).2 ?_
  intro i
  refine ⟨?_, wrightFrequencyMeanStep N i⟩
  simpa using
    (Summable.of_finite :
      Summable (fun y : Fin (N + 1) ↦
        (wrightTransitionMatrix N i y).toReal * wrightFrequency N y))

/-- Helper for Example 17.21: the second moment of the finite Wright binomial row is
`(x * n)² + x * (1 - x) * n`. -/
private theorem binomialSquareSum (n : ℕ) {x : NNReal} (hx : x ≤ 1) :
    Finset.sum (Finset.range (n + 1))
      (fun k ↦ ((n.choose k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (n - k)) * (k : ℝ) ^ 2) =
      (((x : ℝ) * (n : ℝ)) ^ 2 + (x : ℝ) * (1 - (x : ℝ)) * (n : ℝ)) := by
  let p : unitInterval := ⟨(x : ℝ), by exact_mod_cast x.2, hx⟩
  calc
    Finset.sum (Finset.range (n + 1))
        (fun k ↦ ((n.choose k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (n - k)) * (k : ℝ) ^ 2)
      = ∫ t, t ^ 2 ∂Bin(ℝ, n, p) := by
          symm
          have hNat : ∀ᵐ k : ℕ ∂Bin(n, p), k ≤ n := by
            simpa using
              (ProbabilityTheory.ae_le_of_hasLaw_binomial (n := n) (p := p)
                (X := id) (P := Bin(n, p)) (ProbabilityTheory.HasLaw.id (μ := Bin(n, p))))
          have hInt : Integrable (fun k : ℕ ↦ (k : ℝ) ^ 2) (Bin(n, p)) := by
            refine Integrable.of_bound (by fun_prop) ((n : ℝ) ^ (2 : ℕ)) ?_
            filter_upwards [hNat] with k hk
            have hk_nonneg : 0 ≤ (k : ℝ) := by
              exact_mod_cast Nat.zero_le k
            have hk_le : (k : ℝ) ≤ n := by
              exact_mod_cast hk
            have hsq_le : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
              nlinarith
            simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (k : ℝ))] using hsq_le
          rw [show Bin(ℝ, n, p) = Measure.map (Nat.cast : ℕ → ℝ) (Bin(n, p)) by rfl]
          rw [integral_map measurableNatCastReal.aemeasurable (by fun_prop)]
          rw [integral_countable hInt]
          simp_rw [smul_eq_mul, Measure.real, binomial_apply_singleton_toReal]
          have htail :
              ∀ k, k ∉ Finset.range (n + 1) →
                ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) * (k : ℝ) ^ 2 = 0 := by
            intro k hk
            have hk' : n < k := Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hk)
            simp [Nat.choose_eq_zero_of_lt hk']
          rw [tsum_eq_sum htail]
    _ = ((x : ℝ) * (n : ℝ)) ^ 2 + (x : ℝ) * (1 - (x : ℝ)) * (n : ℝ) := by
          simpa [p] using (binomialRealIntegralSq_eq n p)

/-- Helper for Example 17.21: the defect polynomial `x ↦ x * (1 - x)` contracts by the factor
`1 - 1 / N` under one Wright step. -/
private def wrightFrequencyDefect (i : Fin (N + 1)) : ℝ :=
  wrightFrequency N i * (1 - wrightFrequency N i)

section RealizationInterface

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Fin (N + 1) → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → Fin (N + 1)}

/-- Helper for Example 17.21: a discrete-time Markov realization packages the realized kernel
semigroup, coordinate measurability, one-time marginals, and the Markov property used below. This
local owner copy is needed because the earlier Chapter 17 owner module is currently not importable
from this target file. -/
class IsMarkovProcessRealization
    (κ : ℕ → Kernel (Fin (N + 1)) (Fin (N + 1)))
    (P : Fin (N + 1) → ProbabilityMeasure Ω) (X : ℕ → Ω → Fin (N + 1)) : Prop where
  /-- The prescribed kernels form a Markov semigroup. -/
  semigroup : IsMarkovSemigroup κ
  /-- Every time slice of the realization is measurable. -/
  measurable_process : ∀ t : ℕ, Measurable (X t)
  /-- The time-`t` marginal under `P x` is the kernel row `κ t x`. -/
  transition_eq : ∀ x : Fin (N + 1), ∀ t : ℕ, (P x : Measure Ω).map (X t) = κ t x
  /-- Conditioning a future state on the generated history gives the homogeneous transition
  kernel applied to the present state. -/
  markov_property :
    ∀ x ⦃A : Set (Fin (N + 1))⦄, MeasurableSet A → ∀ s t : ℕ,
      (P x)⟦X (t + s) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ((κ t) (X s ω)).real A

end RealizationInterface

/-- Helper for Example 17.21: one Wright transition multiplies the expected defect polynomial by
`1 - 1 / N`. -/
lemma wrightEndpointDefectStep (i : Fin (N + 1)) :
    (wrightTransitionMatrix N ⋆ᶠ wrightFrequencyDefect N) i =
      (1 - 1 / (N : ℝ)) * wrightFrequencyDefect N i := by
  have hsum :
      Summable (fun y : Fin (N + 1) ↦
        (wrightTransitionMatrix N i y).toReal * ‖wrightFrequencyDefect N y‖) := by
    simpa using
      (Summable.of_finite :
        Summable (fun y : Fin (N + 1) ↦
          (wrightTransitionMatrix N i y).toReal * ‖wrightFrequencyDefect N y‖))
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast N.ne_zero
  set x : NNReal := Real.toNNReal (wrightFrequency N i)
  have hx : x ≤ 1 := by
    simpa [x] using wrightFrequency_le_one N i
  have hx_nonneg : 0 ≤ wrightFrequency N i := by
    exact wrightFrequency_nonneg N i
  have hx_real : (x : ℝ) = wrightFrequency N i := by
    simp [x, Real.toNNReal_of_nonneg hx_nonneg]
  rw [integral_discreteMatrixKernel_eq_tsum
      (p := wrightTransitionMatrix N)
      (hp := wrightTransitionMatrix_isStochasticMatrix N)
      (f := wrightFrequencyDefect N) (x := i) hsum,
    tsum_fintype]
  have hrewrite :
      (∑ b : Fin (N + 1), (wrightTransitionMatrix N i b).toReal * wrightFrequencyDefect N b) =
        ∑ b : Fin (N + 1),
          ((Nat.choose N b : ℝ) * (x : ℝ) ^ (b : ℕ) * (1 - (x : ℝ)) ^ (N - (b : ℕ))) *
            (((b : ℝ) / N) * (1 - (b : ℝ) / N)) := by
    refine Finset.sum_congr rfl ?_
    intro b hb
    have hb_le : (b : ℕ) ≤ N := Nat.le_of_lt_succ b.2
    have hprob :
        (wrightTransitionMatrix N i b).toReal =
          (Nat.choose N b : ℝ) * (x : ℝ) ^ (b : ℕ) * (1 - (x : ℝ)) ^ (N - (b : ℕ)) := by
      have hbin :
          wrightTransitionMatrix N i b =
            ENNReal.ofReal
              ((Nat.choose N b : ℝ) * (x : ℝ) ^ (b : ℕ) * (1 - (x : ℝ)) ^ (N - (b : ℕ))) := by
        simpa [wrightTransitionMatrix_def, mul_comm, mul_left_comm, mul_assoc] using
          (PMF.binomial_apply_of_le (b := N) (k := (b : ℕ)) (x := x) hb_le hx).symm
      have hbin_nonneg :
          0 ≤ (Nat.choose N b : ℝ) * (x : ℝ) ^ (b : ℕ) * (1 - (x : ℝ)) ^ (N - (b : ℕ)) := by
        -- Proof comment: the same nonnegativity bridge handles the second-moment normalization.
        exact binomialMassReal_nonneg N (b : ℕ) hx
      rw [hbin, ENNReal.toReal_ofReal hbin_nonneg]
    have hfreq :
        wrightFrequency N b = (b : ℝ) / N := by
      rw [wrightFrequency]
    rw [hprob, wrightFrequencyDefect, hfreq]
  calc
    ∑ b : Fin (N + 1), (wrightTransitionMatrix N i b).toReal * wrightFrequencyDefect N b
      = ∑ b : Fin (N + 1),
          ((Nat.choose N b : ℝ) * (x : ℝ) ^ (b : ℕ) * (1 - (x : ℝ)) ^ (N - (b : ℕ))) *
            (((b : ℝ) / N) * (1 - (b : ℝ) / N)) := hrewrite
    _ = Finset.sum (Finset.range (N + 1))
          (fun k ↦
            ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
              (((k : ℝ) / N) * (1 - (k : ℝ) / N))) := by
            simpa using
              (Fin.sum_univ_eq_sum_range
                (fun k : ℕ ↦
                  ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                    (((k : ℝ) / N) * (1 - (k : ℝ) / N))) (N + 1))
    _ = (1 / N : ℝ) *
          Finset.sum (Finset.range (N + 1))
            (fun k ↦ ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) * (k : ℝ))
          - (1 / (N : ℝ) ^ 2) *
            Finset.sum (Finset.range (N + 1))
              (fun k ↦ ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                (k : ℝ) ^ 2) := by
            have hfirst :
                Finset.sum (Finset.range (N + 1))
                  (fun k ↦
                    ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                      ((k : ℝ) / N)) =
                  (1 / N : ℝ) *
                    Finset.sum (Finset.range (N + 1))
                      (fun k ↦ ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                        (k : ℝ)) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  rw [div_eq_mul_inv]
                  ring
            have hsecond :
                Finset.sum (Finset.range (N + 1))
                  (fun k ↦
                    ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                      (((k : ℝ) / N) ^ 2)) =
                  (1 / (N : ℝ) ^ 2) *
                    Finset.sum (Finset.range (N + 1))
                      (fun k ↦ ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                        (k : ℝ) ^ 2) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  field_simp [hN]
            calc
              Finset.sum (Finset.range (N + 1))
                  (fun k ↦
                    ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                      (((k : ℝ) / N) * (1 - (k : ℝ) / N)))
                  =
                  Finset.sum (Finset.range (N + 1))
                    (fun k ↦
                      ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                        ((k : ℝ) / N) -
                      ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                        (((k : ℝ) / N) ^ 2)) := by
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    ring
              _ =
                  Finset.sum (Finset.range (N + 1))
                    (fun k ↦
                      ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                        ((k : ℝ) / N))
                    -
                  Finset.sum (Finset.range (N + 1))
                    (fun k ↦
                      ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                        (((k : ℝ) / N) ^ 2)) := by
                    rw [Finset.sum_sub_distrib]
              _ = (1 / N : ℝ) *
                    Finset.sum (Finset.range (N + 1))
                      (fun k ↦ ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                        (k : ℝ))
                  -
                    Finset.sum (Finset.range (N + 1))
                      (fun k ↦
                        ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                          (((k : ℝ) / N) ^ 2)) := by
                    rw [hfirst]
              _ = (1 / N : ℝ) *
                    Finset.sum (Finset.range (N + 1))
                      (fun k ↦ ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                        (k : ℝ))
                  -
                    (1 / (N : ℝ) ^ 2) *
                      Finset.sum (Finset.range (N + 1))
                        (fun k ↦ ((Nat.choose N k : ℝ) * (x : ℝ) ^ k * (1 - (x : ℝ)) ^ (N - k)) *
                          (k : ℝ) ^ 2) := by
                    rw [hsecond]
    _ = (1 / N : ℝ) * (x * N) -
          (1 / (N : ℝ) ^ 2) * ((x * N) ^ 2 + x * (1 - x) * N) := by
            rw [binomialMeanSum N hx, binomialSquareSum N hx]
    _ = (1 - 1 / (N : ℝ)) * (x : ℝ) * (1 - (x : ℝ)) := by
          field_simp [hN]
          ring
    _ = (1 - 1 / (N : ℝ)) * wrightFrequencyDefect N i := by
          rw [wrightFrequencyDefect, ← hx_real]
          ring

/-- Helper for Example 17.21: the `n`-step Wright kernel contracts the defect polynomial by the
geometric factor `(1 - 1 / N)^n`. -/
private theorem wrightEndpointDefectKernelIntegral (i : Fin (N + 1)) (n : ℕ) :
    ∫ y, wrightFrequencyDefect N y
      ∂((discreteMatrixKernel (wrightTransitionMatrix N) ^ n) i) =
      (1 - 1 / (N : ℝ)) ^ n * wrightFrequencyDefect N i := by
  let κ : Kernel (Fin (N + 1)) (Fin (N + 1)) := discreteMatrixKernel (wrightTransitionMatrix N)
  letI : IsMarkovKernel κ :=
    discreteMatrixKernel_isMarkovKernel _ (wrightTransitionMatrix_isStochasticMatrix N)
  have hpow_markov : ∀ m : ℕ, IsMarkovKernel (κ ^ m) := by
    intro m
    induction m with
    | zero =>
        simpa [pow_zero] using
          (inferInstance : IsMarkovKernel (Kernel.id : Kernel (Fin (N + 1)) (Fin (N + 1))))
    | succ m ihm =>
        letI : IsMarkovKernel (κ ^ m) := ihm
        simpa [pow_succ'] using (inferInstance : IsMarkovKernel (κ ∘ₖ (κ ^ m)))
  induction n with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity kernel, so the integral collapses to
      -- evaluation at the starting state.
      simp [pow_zero]
      change ∫ y, wrightFrequencyDefect N y ∂Kernel.id i = wrightFrequencyDefect N i
      rw [Kernel.id_apply, integral_dirac]
  | succ n ihn =>
      letI : IsMarkovKernel (κ ^ n) := hpow_markov n
      letI : IsFiniteKernel (κ ^ n) := inferInstance
      letI : IsFiniteKernel (κ ∘ₖ (κ ^ n)) := inferInstance
      have hint :
          Integrable (wrightFrequencyDefect N) (((κ) ∘ₖ (κ ^ n)) i) := by
        -- Proof comment: the composite law is supported on the finite state space
        -- `Fin (N + 1)`, so every real-valued function is integrable.
        exact Integrable.of_finite (μ := ((κ ∘ₖ (κ ^ n)) i)) (f := wrightFrequencyDefect N)
      have hstep :
          ∀ x : Fin (N + 1),
            ∫ y, wrightFrequencyDefect N y ∂κ x =
              (1 - 1 / (N : ℝ)) * wrightFrequencyDefect N x := by
        intro x
        simpa [κ, matrixFunctionAction_apply] using wrightEndpointDefectStep N x
      -- Proof comment: rewrite the `(n + 1)`-step law in the composition order used by
      -- `Kernel.integral_comp`, then apply the one-step defect contraction inside the outer
      -- integral.
      calc
        ∫ y, wrightFrequencyDefect N y
            ∂((discreteMatrixKernel (wrightTransitionMatrix N) ^ (n + 1)) i)
          = ∫ x, ∫ y, wrightFrequencyDefect N y ∂κ x ∂((κ ^ n) i) := by
              rw [pow_succ']
              simpa [κ] using
                (ProbabilityTheory.Kernel.integral_comp (η := κ) (κ := κ ^ n) (a := i) hint)
        _ = ∫ x, (1 - 1 / (N : ℝ)) * wrightFrequencyDefect N x ∂((κ ^ n) i) := by
              refine integral_congr_ae ?_
              exact ae_of_all _ hstep
        _ = (1 - 1 / (N : ℝ)) *
              ∫ x, wrightFrequencyDefect N x ∂((κ ^ n) i) := by
              rw [integral_const_mul]
        _ = (1 - 1 / (N : ℝ)) *
              ((1 - 1 / (N : ℝ)) ^ n * wrightFrequencyDefect N i) := by
              rw [ihn]
        _ = (1 - 1 / (N : ℝ)) ^ (n + 1) * wrightFrequencyDefect N i := by
              rw [pow_succ']
              ring

section

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Fin (N + 1) → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → Fin (N + 1)}
variable [IsMarkovProcessRealization (N := N)
  (fun n : ℕ ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n) P X]

local notation "M" => fun n ω ↦ wrightFrequency N (X n ω)
local notation "ℱ" => processFiltration X

/-- Helper for Example 17.21: bounded range makes each sampled Wright frequency integrable under
the realization measure `(P i : Measure Ω)`. -/
private lemma integrableWrightFrequencyProcess
    (i : Fin (N + 1)) :
    ∀ n, Integrable (M n) (P i : Measure Ω) := by
  intro n
  obtain ⟨R, hR⟩ := (wrightFrequency_isBounded N).exists_norm_le
  refine Integrable.mono' (integrable_const R) ?_ ?_
  · change AEStronglyMeasurable (fun ω ↦ wrightFrequency N (X n ω)) (P i : Measure Ω)
    exact ((Measurable.of_discrete : Measurable (wrightFrequency N)).comp
      (IsMarkovProcessRealization.measurable_process
        (N := N)
        (κ := fun n : ℕ ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n)
        (P := P) (X := X) n)).aestronglyMeasurable
  · filter_upwards with ω
    simpa using hR (wrightFrequency N (X n ω)) ⟨X n ω, rfl⟩

/-- Helper for Example 17.21: on an event from the natural filtration, the restricted law of the
next Wright state is obtained by composing the restricted current-state law with the one-step
Wright kernel. -/
private lemma restrictMapSuccEqWrightKernelComp
    (i : Fin (N + 1)) (n : ℕ) {s : Set Ω} (hs : MeasurableSet[ℱ n] s) :
    ((P i : Measure Ω).restrict s).map (X (n + 1)) =
      (discreteMatrixKernel (wrightTransitionMatrix N)) ∘ₘ (((P i : Measure Ω).restrict s).map (X n)) := by
  let μ : Measure Ω := (P i : Measure Ω)
  let hReal :
      IsMarkovProcessRealization (N := N)
        (fun n : ℕ ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel (wrightTransitionMatrix N)) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hX_meas : ∀ k : ℕ, Measurable (X k) := hReal.measurable_process
  have hs_meas : MeasurableSet s := hs.1
  have hs_generated : MeasurableSet[generatedFiltrationSpace X n] s := hs.2
  have hgenerated_le : generatedFiltrationSpace X n ≤ mΩ := by
    refine iSup₂_le fun k hk ↦ ?_
    exact (hX_meas k).comap_le
  refine Measure.ext fun A hA ↦ ?_
  have hleft_real :
      (((μ.restrict s).map (X (n + 1))).real A) =
        ∫ ω in s, ((discreteMatrixKernel (wrightTransitionMatrix N)) (X n ω)).real A ∂μ := by
    let B : Set Ω := X (n + 1) ⁻¹' A
    have hB_meas : MeasurableSet B := by
      simpa [B] using (hX_meas (n + 1)) hA
    have hIndicatorInt : Integrable (Set.indicator B (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hB_meas
    have hmarkov :
        μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
          fun ω ↦ ((discreteMatrixKernel (wrightTransitionMatrix N)) (X n ω)).real A := by
      -- Proof comment: the realization Markov property rewrites the future state event as the
      -- Wright one-step transition probability from the present state.
      simpa [B, add_comm] using hReal.markov_property i (A := A) hA n 1
    have hmass :
        μ.real (s ∩ B) =
          ∫ ω in s, ((discreteMatrixKernel (wrightTransitionMatrix N)) (X n ω)).real A ∂μ := by
      calc
        μ.real (s ∩ B)
            = ∫ ω in s, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂μ := by
                rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hs_generated,
                  ← MeasureTheory.integral_indicator hs_meas]
                simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                  Set.inter_comm, smul_eq_mul] using
                  (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                    (hs_meas.inter hB_meas)).symm
        _ = ∫ ω in s, ((discreteMatrixKernel (wrightTransitionMatrix N)) (X n ω)).real A ∂μ := by
              exact MeasureTheory.integral_congr_ae hmarkov.restrict
    calc
      (((μ.restrict s).map (X (n + 1))).real A)
          = (μ.restrict s).real ((X (n + 1)) ⁻¹' A) := by
              simpa using MeasureTheory.map_measureReal_apply
                (μ := μ.restrict s) (f := X (n + 1)) (hX_meas (n + 1)) hA
      _ = μ.real (((X (n + 1)) ⁻¹' A) ∩ s) := by
            simpa [B] using
              (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := s) (t := B) hB_meas)
      _ = ∫ ω in s, ((discreteMatrixKernel (wrightTransitionMatrix N)) (X n ω)).real A ∂μ := by
            simpa [B, Set.inter_comm] using hmass
  have hright_real :
      (((discreteMatrixKernel (wrightTransitionMatrix N)) ∘ₘ ((μ.restrict s).map (X n))).real A) =
        ∫ ω in s, ((discreteMatrixKernel (wrightTransitionMatrix N)) (X n ω)).real A ∂μ := by
    let ν : Measure (Fin (N + 1)) := ((μ.restrict s).map (X n))
    have hkernel_int :
        Integrable (fun y : Fin (N + 1) ↦
          ((discreteMatrixKernel (wrightTransitionMatrix N)) y).real A) ν := by
      simpa [ν] using
        (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
          (μ := ν) (κ := discreteMatrixKernel (wrightTransitionMatrix N)) hA)
    have hkernel_nonneg :
        0 ≤ᵐ[ν] fun y : Fin (N + 1) ↦
          ((discreteMatrixKernel (wrightTransitionMatrix N)) y).real A :=
      Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
    have hcomp_real :
      (((discreteMatrixKernel (wrightTransitionMatrix N)) ∘ₘ ν).real A) =
          ∫ y, ((discreteMatrixKernel (wrightTransitionMatrix N)) y).real A ∂ν := by
      rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
        (ProbabilityTheory.Kernel.aemeasurable _)]
      have hlintegral :
          ∫⁻ y, ((discreteMatrixKernel (wrightTransitionMatrix N)) y) A ∂ν =
            ENNReal.ofReal
              (∫ y, ((discreteMatrixKernel (wrightTransitionMatrix N)) y).real A ∂ν) := by
        calc
          ∫⁻ y, ((discreteMatrixKernel (wrightTransitionMatrix N)) y) A ∂ν
              = ∫⁻ y, ENNReal.ofReal
                  (((discreteMatrixKernel (wrightTransitionMatrix N)) y).real A) ∂ν := by
                  refine lintegral_congr_ae ?_
                  filter_upwards with y
                  rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
                  exact measure_ne_top _ _
          _ = ENNReal.ofReal
                (∫ y, ((discreteMatrixKernel (wrightTransitionMatrix N)) y).real A ∂ν) := by
                symm
                exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                  hkernel_int hkernel_nonneg
      rw [hlintegral, ENNReal.toReal_ofReal]
      exact integral_nonneg_of_ae hkernel_nonneg
    have hmap_real :
        ∫ y, ((discreteMatrixKernel (wrightTransitionMatrix N)) y).real A ∂ν =
          ∫ ω in s, ((discreteMatrixKernel (wrightTransitionMatrix N)) (X n ω)).real A ∂μ := by
      -- Proof comment: push the one-step Wright kernel masses back through the restricted law of
      -- the current state.
      change
        ∫ y, ((discreteMatrixKernel (wrightTransitionMatrix N)) y).real A
            ∂((μ.restrict s).map (X n)) =
          ∫ ω, ((discreteMatrixKernel (wrightTransitionMatrix N)) (X n ω)).real A
            ∂(μ.restrict s)
      rw [MeasureTheory.integral_map
        (IsMarkovProcessRealization.measurable_process
          (N := N)
          (κ := fun n : ℕ ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n)
          (P := P) (X := X) n).aemeasurable
        hkernel_int.aestronglyMeasurable]
    calc
      (((discreteMatrixKernel (wrightTransitionMatrix N)) ∘ₘ
          ((μ.restrict s).map (X n))).real A)
          = ∫ y, ((discreteMatrixKernel (wrightTransitionMatrix N)) y).real A ∂ν := by
              simpa [ν] using hcomp_real
      _ = ∫ ω in s, ((discreteMatrixKernel (wrightTransitionMatrix N)) (X n ω)).real A ∂μ := by
            simpa [ν] using hmap_real
  have hleft_ne_top : (((μ.restrict s).map (X (n + 1))) A) ≠ ∞ := by
    finiteness
  have hright_ne_top :
      (((discreteMatrixKernel (wrightTransitionMatrix N)) ∘ₘ (((μ.restrict s).map (X n)))) A) ≠ ∞ := by
    finiteness
  exact
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := ((μ.restrict s).map (X (n + 1))))
      (ν := (discreteMatrixKernel (wrightTransitionMatrix N)) ∘ₘ (((μ.restrict s).map (X n))))
      (s := A) (t := A) hleft_ne_top hright_ne_top).mp
      (hleft_real.trans hright_real.symm)

/-- Helper for Example 17.21: integrating the next-step Wright frequency over an
`ℱ n`-measurable set agrees with integrating the current-step frequency. -/
lemma wrightFrequencySetIntegralSuccEq
    (i : Fin (N + 1)) (n : ℕ) {s : Set Ω} (hs_meas : MeasurableSet[ℱ n] s) :
    ∫ ω in s, M (n + 1) ω ∂(P i : Measure Ω) =
      ∫ ω in s, M n ω ∂(P i : Measure Ω) := by
  let μ : Measure Ω := (P i : Measure Ω)
  let ν : Measure (Fin (N + 1)) := ((μ.restrict s).map (X n))
  let hReal :
      IsMarkovProcessRealization (N := N)
        (fun n : ℕ ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel (wrightTransitionMatrix N)) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  rcases (isHarmonic_iff (p := discreteMatrixKernel (wrightTransitionMatrix N))
      (f := wrightFrequency N)).mp (wrightFrequency_isHarmonic N) with ⟨_, hharmonic⟩
  have hcurrent_int : Integrable (wrightFrequency N) ν := by
    -- Proof comment: boundedness of the Wright frequency gives integrability after restricting to
    -- the current-history event and pushing forward along `X n`.
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict s) (f := X n) (g := wrightFrequency N)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process n).aemeasurable).2 <|
        (integrableWrightFrequencyProcess (N := N) (P := P) (X := X) i n).restrict
  have hnext_int : Integrable (wrightFrequency N) (((μ.restrict s).map (X (n + 1)))) := by
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict s) (f := X (n + 1)) (g := wrightFrequency N)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process (n + 1)).aemeasurable).2 <|
        (integrableWrightFrequencyProcess (N := N) (P := P) (X := X) i (n + 1)).restrict
  have hcomp_int :
      Integrable (wrightFrequency N)
        ((discreteMatrixKernel (wrightTransitionMatrix N)) ∘ₘ ν) := by
    -- Proof comment: the restricted next-step law already agrees with the one-step Wright kernel
    -- applied to the restricted current-state law.
    simpa [ν] using
      (restrictMapSuccEqWrightKernelComp (N := N) (P := P) (X := X) i n hs_meas ▸ hnext_int)
  have hcurrent_map :
      ∫ y, wrightFrequency N y ∂ν = ∫ ω in s, M n ω ∂μ := by
    change ∫ y, wrightFrequency N y ∂((μ.restrict s).map (X n)) =
      ∫ ω, wrightFrequency N (X n ω) ∂(μ.restrict s)
    rw [MeasureTheory.integral_map (hReal.measurable_process n).aemeasurable
      hcurrent_int.aestronglyMeasurable]
  have hnext_map :
      ∫ y, wrightFrequency N y ∂(((μ.restrict s).map (X (n + 1)))) =
        ∫ ω in s, M (n + 1) ω ∂μ := by
    change ∫ y, wrightFrequency N y ∂((μ.restrict s).map (X (n + 1))) =
      ∫ ω, wrightFrequency N (X (n + 1) ω) ∂(μ.restrict s)
    rw [MeasureTheory.integral_map (hReal.measurable_process (n + 1)).aemeasurable
      hnext_int.aestronglyMeasurable]
  have hcomp_integral :
      ∫ y, wrightFrequency N y ∂((μ.restrict s).map (X (n + 1))) =
        ∫ y, ∫ z, wrightFrequency N z ∂discreteMatrixKernel (wrightTransitionMatrix N) y ∂ν := by
    rw [restrictMapSuccEqWrightKernelComp (N := N) (P := P) (X := X) i n hs_meas]
    calc
      ∫ y, wrightFrequency N y ∂((discreteMatrixKernel (wrightTransitionMatrix N)) ∘ₘ ν)
          =
            ∫ y, wrightFrequency N y
              ∂((discreteMatrixKernel (wrightTransitionMatrix N) ∘ₖ
                ProbabilityTheory.Kernel.const Unit ν) ()) := by
              rw [ProbabilityTheory.Kernel.comp_const, ProbabilityTheory.Kernel.const_apply]
      _ = ∫ y, ∫ z, wrightFrequency N z ∂discreteMatrixKernel (wrightTransitionMatrix N) y ∂ν := by
            exact
              ProbabilityTheory.Kernel.integral_comp
                (η := discreteMatrixKernel (wrightTransitionMatrix N))
                (κ := ProbabilityTheory.Kernel.const Unit ν)
                (a := ()) <| by
                  rw [ProbabilityTheory.Kernel.comp_const, ProbabilityTheory.Kernel.const_apply]
                  exact hcomp_int
  have hharmonic_integral :
      ∫ y, ∫ z, wrightFrequency N z ∂discreteMatrixKernel (wrightTransitionMatrix N) y ∂ν =
        ∫ y, wrightFrequency N y ∂ν := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun y ↦ (hharmonic y).symm
  -- Proof comment: rewrite the restricted next-step law as a kernel average over the current
  -- state and collapse that average using harmonicity of the frequency observable.
  calc
    ∫ ω in s, M (n + 1) ω ∂μ
        = ∫ y, wrightFrequency N y ∂(((μ.restrict s).map (X (n + 1)))) := hnext_map.symm
    _ = ∫ y, ∫ z, wrightFrequency N z ∂discreteMatrixKernel (wrightTransitionMatrix N) y ∂ν := by
          exact hcomp_integral
    _ = ∫ y, wrightFrequency N y ∂ν := hharmonic_integral
    _ = ∫ ω in s, M n ω ∂μ := hcurrent_map

/-- For any realization of Wright's model, the gene-frequency process is a martingale. -/
theorem wrightFrequency_martingale
    (i : Fin (N + 1)) :
    Martingale M ℱ (P i : Measure Ω) := by
  let μ : Measure Ω := (P i : Measure Ω)
  have hX_meas : ∀ n : ℕ, Measurable (X n) :=
    IsMarkovProcessRealization.measurable_process
      (N := N)
      (κ := fun n : ℕ ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n)
      (P := P) (X := X)
  have hX_adapted : Adapted ℱ X := by
    intro n
    -- Proof comment: the time-`n` Wright state is one of the generators of the natural
    -- filtration.
    refine measurable_iff_comap_le.2 ?_
    exact le_inf (measurable_iff_comap_le.1 (hX_meas n)) <| by
      refine le_iSup_of_le n ?_
      refine le_iSup_of_le le_rfl ?_
      exact le_rfl
  have hM_stronglyAdapted : StronglyAdapted ℱ M := by
    have hM_adapted : Adapted ℱ M := by
      intro n
      exact (Measurable.of_discrete : Measurable (wrightFrequency N)).comp (hX_adapted n)
    intro n
    -- Proof comment: composing the adapted state process with the discrete Wright frequency keeps
    -- the process strongly adapted.
    simpa using (hM_adapted.stronglyAdapted n)
  have hM_integrable : ∀ n, Integrable (M n) μ :=
    integrableWrightFrequencyProcess (N := N) (P := P) (X := X) i
  -- Proof comment: the one-step set-integral identity is exactly the martingale constructor
  -- hypothesis.
  exact MeasureTheory.martingale_of_setIntegral_eq_succ hM_stronglyAdapted hM_integrable
    (fun n s hs ↦ (wrightFrequencySetIntegralSuccEq (N := N) (P := P) (X := X) i n hs).symm)

/-- The Wright frequency process converges almost surely to its canonical martingale limit. -/
theorem wrightFrequency_ae_tendsto_limitProcess
    (i : Fin (N + 1)) :
    ∀ᵐ ω ∂(P i : Measure Ω),
      Tendsto (fun n ↦ M n ω) atTop
        (nhds (Filtration.limitProcess M ℱ (P i : Measure Ω) ω)) := by
  exact (wrightFrequency_martingale (N := N) (P := P) (X := X) i).submartingale
    |>.ae_tendsto_limitProcess fun n ↦ by
      have hbound :
          ∀ᵐ ω ∂(P i : Measure Ω), ‖M n ω‖ ≤ 1 := by
        filter_upwards with ω
        have hnonneg : 0 ≤ M n ω := by
          change 0 ≤ wrightFrequency N (X n ω)
          rw [wrightFrequency]
          positivity
        have hle : M n ω ≤ 1 := by
          exact Real.toNNReal_le_one.1 (wrightFrequency_le_one N (X n ω))
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
      simpa using
        (eLpNorm_le_of_ae_bound (μ := (P i : Measure Ω)) (p := (1 : ℝ≥0∞)) (C := 1) hbound)

/-- Helper for Example 17.21: the `n`-time expectation of the defect polynomial is the geometric
decay given by the `n`-step Wright kernel. -/
lemma wrightEndpointDefectIntegralAtTime
    (i : Fin (N + 1)) (n : ℕ) :
    ∫ ω, wrightFrequencyDefect N (X n ω) ∂(P i : Measure Ω) =
      (1 - 1 / (N : ℝ)) ^ n * wrightFrequencyDefect N i := by
  calc
    ∫ ω, wrightFrequencyDefect N (X n ω) ∂(P i : Measure Ω)
        = ∫ y, wrightFrequencyDefect N y ∂((P i : Measure Ω).map (X n)) := by
            symm
            exact MeasureTheory.integral_map
              ((IsMarkovProcessRealization.measurable_process
                (N := N)
                (κ := fun n : ℕ ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n)
                (P := P) (X := X) n).aemeasurable)
              ((Measurable.of_discrete : Measurable (wrightFrequencyDefect N)).aestronglyMeasurable)
    _ = ∫ y, wrightFrequencyDefect N y
          ∂((discreteMatrixKernel (wrightTransitionMatrix N) ^ n) i) := by
            rw [IsMarkovProcessRealization.transition_eq
              (N := N)
              (κ := fun n : ℕ ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n)
              (P := P) (X := X) i n]
    _ = (1 - 1 / (N : ℝ)) ^ n * wrightFrequencyDefect N i := by
          exact wrightEndpointDefectKernelIntegral N i n

/-- Helper for Example 17.21: the canonical martingale limit stays in the closed unit interval
almost surely. -/
lemma wrightLimitProcess_ae_memUnitInterval
    (i : Fin (N + 1)) :
    ∀ᵐ ω ∂(P i : Measure Ω),
      Filtration.limitProcess M ℱ (P i : Measure Ω) ω ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [wrightFrequency_ae_tendsto_limitProcess (N := N) (P := P) (X := X) i] with ω hω
  refine isClosed_Icc.mem_of_tendsto hω ?_
  exact Filter.Eventually.of_forall fun n ↦ by
    constructor
    · change 0 ≤ wrightFrequency N (X n ω)
      rw [wrightFrequency]
      positivity
    · exact Real.toNNReal_le_one.1 (wrightFrequency_le_one N (X n ω))

/-- Helper for Example 17.21: the defect polynomial of the martingale limit has zero integral. -/
lemma wrightEndpointDefectLimitIntegralEqZero
    (i : Fin (N + 1)) :
    ∫ ω,
      Filtration.limitProcess M ℱ (P i : Measure Ω) ω *
        (1 - Filtration.limitProcess M ℱ (P i : Measure Ω) ω) ∂(P i : Measure Ω) = 0 := by
  let μ : Measure Ω := (P i : Measure Ω)
  let L : Ω → ℝ := Filtration.limitProcess M ℱ μ
  let g : ℝ → ℝ := fun x ↦ x * (1 - x)
  have hg_cont : Continuous g := by
    simpa [g] using continuous_id.mul (continuous_const.sub continuous_id)
  have hF_meas : ∀ n, AEStronglyMeasurable (fun ω ↦ g (M n ω)) μ := by
    intro n
    have hMn_meas : Measurable (M n) := by
      change Measurable (fun ω ↦ wrightFrequency N (X n ω))
      exact (Measurable.of_discrete : Measurable (wrightFrequency N)).comp
        (IsMarkovProcessRealization.measurable_process
          (N := N)
          (κ := fun n : ℕ ↦ discreteMatrixKernel (wrightTransitionMatrix N) ^ n)
          (P := P) (X := X) n)
    exact (hg_cont.measurable.comp hMn_meas).stronglyMeasurable.aestronglyMeasurable
  have hLimit_mem : ∀ᵐ ω ∂μ, L ω ∈ Set.Icc (0 : ℝ) 1 :=
    wrightLimitProcess_ae_memUnitInterval (N := N) (P := P) (X := X) i
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖g (M n ω)‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with ω
    have h0 : 0 ≤ M n ω := by
      change 0 ≤ wrightFrequency N (X n ω)
      rw [wrightFrequency]
      positivity
    have h1 : M n ω ≤ 1 := by
      exact Real.toNNReal_le_one.1 (wrightFrequency_le_one N (X n ω))
    have hnonneg : 0 ≤ g (M n ω) := by
      dsimp [g]
      exact mul_nonneg h0 (sub_nonneg.mpr h1)
    have hle : g (M n ω) ≤ 1 := by
      dsimp [g]
      nlinarith
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hlim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ g (M n ω)) atTop (nhds (g (L ω))) := by
    filter_upwards [wrightFrequency_ae_tendsto_limitProcess (N := N) (P := P) (X := X) i] with ω hω
    exact hg_cont.continuousAt.tendsto.comp hω
  have hIntegralTendsto :
      Tendsto (fun n ↦ ∫ ω, g (M n ω) ∂μ) atTop (nhds (∫ ω, g (L ω) ∂μ)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : Ω ↦ (1 : ℝ)) hF_meas (integrable_const (1 : ℝ)) hbound hlim
  have hN_pos : (0 : ℝ) < N := by
    exact_mod_cast N.pos
  have hfactor_nonneg : 0 ≤ 1 - 1 / (N : ℝ) := by
    have hN_ge_one : (1 : ℝ) ≤ N := by
      exact_mod_cast N.pos
    have hdiv_le : (1 : ℝ) / N ≤ 1 := by
      simpa [one_div] using (inv_le_one_of_one_le₀ hN_ge_one)
    linarith
  have hfactor_abs_lt : |1 - 1 / (N : ℝ)| < 1 := by
    rw [abs_of_nonneg hfactor_nonneg]
    have hdiv_pos : (0 : ℝ) < 1 / (N : ℝ) := by
      positivity
    linarith
  have hFormulaTendsto :
      Tendsto (fun n ↦ ∫ ω, g (M n ω) ∂μ) atTop (nhds 0) := by
    have hpow :
        Tendsto (fun n : ℕ ↦ (1 - 1 / (N : ℝ)) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one hfactor_abs_lt
    have hEq :
        (fun n ↦ ∫ ω, g (M n ω) ∂μ) =
          fun n : ℕ ↦ (1 - 1 / (N : ℝ)) ^ n * wrightFrequencyDefect N i := by
      funext n
      change ∫ ω, wrightFrequency N (X n ω) * (1 - wrightFrequency N (X n ω)) ∂μ =
          (1 - 1 / (N : ℝ)) ^ n * wrightFrequencyDefect N i
      simpa [g, wrightFrequencyDefect] using
        wrightEndpointDefectIntegralAtTime (N := N) (P := P) (X := X) i n
    rw [hEq]
    simpa using hpow.mul tendsto_const_nhds
  have hzero :
      ∫ ω, g (L ω) ∂μ = 0 := by
    exact tendsto_nhds_unique hIntegralTendsto hFormulaTendsto
  simpa [L, g] using hzero

/-- The canonical almost-sure limit of Wright's frequency martingale takes values in `{0, 1}`. -/
theorem wrightFrequency_limitProcess_ae_mem_endpoints
    (i : Fin (N + 1)) :
    ∀ᵐ ω ∂(P i : Measure Ω),
      Filtration.limitProcess M ℱ (P i : Measure Ω) ω ∈ ({0, 1} : Set ℝ) := by
  let μ : Measure Ω := (P i : Measure Ω)
  let L : Ω → ℝ := Filtration.limitProcess M ℱ μ
  change ∀ᵐ ω ∂μ, L ω ∈ ({0, 1} : Set ℝ)
  have hL_mem : ∀ᵐ ω ∂μ, L ω ∈ Set.Icc (0 : ℝ) 1 :=
    wrightLimitProcess_ae_memUnitInterval (N := N) (P := P) (X := X) i
  have hL_meas : AEStronglyMeasurable L μ :=
    by
      have hL_sm : StronglyMeasurable (Filtration.limitProcess M ℱ μ) := by
        simpa using
          (MeasureTheory.Filtration.stronglyMeasurable_limit_process' :
            StronglyMeasurable (Filtration.limitProcess M ℱ μ))
      simpa [L] using hL_sm.aestronglyMeasurable
  have hDefect_meas : AEStronglyMeasurable (fun ω ↦ L ω * (1 - L ω)) μ := by
    simpa using
      hL_meas.mul
        ((aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω ↦ (1 : ℝ)) μ).sub hL_meas)
  have hnonneg : 0 ≤ᵐ[μ] fun ω ↦ L ω * (1 - L ω) := by
    filter_upwards [hL_mem] with ω hω
    exact mul_nonneg hω.1 (sub_nonneg.mpr hω.2)
  have hL_integrable : Integrable (fun ω ↦ L ω * (1 - L ω)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hDefect_meas ?_
    filter_upwards [hL_mem] with ω hω
    have hnonnegω : 0 ≤ L ω * (1 - L ω) := mul_nonneg hω.1 (sub_nonneg.mpr hω.2)
    have hleω : L ω * (1 - L ω) ≤ 1 := by
      nlinarith [sq_nonneg (L ω - 1 / 2)]
    have hL_abs : |L ω| = L ω := abs_of_nonneg hω.1
    have hOneSub_abs : |1 - L ω| = 1 - L ω := abs_of_nonneg (sub_nonneg.mpr hω.2)
    simpa [Real.norm_eq_abs, abs_mul, hL_abs, hOneSub_abs] using hleω
  have hzero_ae : (fun ω ↦ L ω * (1 - L ω)) =ᵐ[μ] 0 := by
    exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hL_integrable).mp
      (wrightEndpointDefectLimitIntegralEqZero (N := N) (P := P) (X := X) i)
  filter_upwards [hL_mem, hzero_ae] with ω hω_mem hω_zero
  have hEq : L ω * (1 - L ω) = 0 := by
    simpa using hω_zero
  rcases mul_eq_zero.mp hEq with hleft | hright
  · simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (Or.inl hleft : L ω = 0 ∨ L ω = 1)
  · have hone : L ω = 1 := by
      linarith
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (Or.inr hone : L ω = 0 ∨ L ω = 1)

/-- Example 17.21: in Wright's evolution model, the type-`A` gene frequency is a martingale and
converges almost surely to a limit taking only the absorbing values `0` and `1`. -/
theorem wrightFrequency_ae_tendsto_zero_or_one
    (i : Fin (N + 1)) :
    (∀ᵐ ω ∂(P i : Measure Ω),
      Tendsto (fun n ↦ M n ω) atTop
        (nhds (Filtration.limitProcess M ℱ (P i : Measure Ω) ω))) ∧
      (∀ᵐ ω ∂(P i : Measure Ω),
        Filtration.limitProcess M ℱ (P i : Measure Ω) ω ∈ ({0, 1} : Set ℝ)) := by
  exact ⟨wrightFrequency_ae_tendsto_limitProcess (N := N) (P := P) (X := X) i,
    wrightFrequency_limitProcess_ae_mem_endpoints (N := N) (P := P) (X := X) i⟩

end

end ProbabilityTheory
