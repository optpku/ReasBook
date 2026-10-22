/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_9.Scaling
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.SingularSystem
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

public section

noncomputable section

namespace ContinuousLinearMap.SingularSystem

universe u v

variable {H₁ : Type u} {H₂ : Type v}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable {K : H₁ →L[ℝ] H₂}

/-- The weighted source-condition series from `(7.54)`, formed from the quotient
of the squared generalized Fourier coefficients by the squared singular values. -/
@[expose]
def weightedSourceSeries
    (S : SingularSystem K) (h_length : S.length = ⊤) (fTrue : H₁) : ℕ+ → ℝ :=
  fun i ↦
    S.generalizedFourierCoefficientSequence h_length fTrue i ^ 2 /
      (S.singularValueSequence h_length i ^ 2)

@[simp] theorem weightedSourceSeries_apply
    (S : SingularSystem K) (h_length : S.length = ⊤) (fTrue : H₁) (i : ℕ+) :
    S.weightedSourceSeries h_length fTrue i =
      S.generalizedFourierCoefficientSequence h_length fTrue i ^ 2 /
        (S.singularValueSequence h_length i ^ 2) :=
  rfl

/-- Remark 7.11 companion. Under the Chapter 7 algebraic square-decay laws
`(7.49)` and `(7.53)`, the weighted source series `(7.54)` is summable exactly
when the decay exponents cross the source threshold `q > p + 1`, provided the
Fourier-side prefactor is nonzero. This records the source-prose continuation
from `(7.53)` and `(7.54)` toward `(7.55)` without choosing a specific Lean
encoding of the still-disputed displayed formula `(7.55)`. -/
theorem weightedSourceSeriesSummable_iff_decayThreshold
    (S : SingularSystem K) (h_length : S.length = ⊤) (fTrue : H₁)
    {b c p q : ℝ}
    (h_singularDecay : S.HasAlgebraicSingularValueSquareDecay h_length c p)
    (h_fourierDecay : S.HasAlgebraicFourierCoefficientSquareDecay h_length fTrue b q)
    (hb : b ≠ 0) :
    Summable (S.weightedSourceSeries h_length fTrue) ↔ q > p + 1 := by
  have hσ_pos : 0 < S.singularValueSequence h_length 1 := by
    simpa using S.singularValue_pos (S.positiveIndex h_length 1)
  have hc_pos : 0 < c := by
    have h_at_one : S.singularValueSequence h_length 1 ^ 2 = c := by
      simpa using h_singularDecay 1
    exact h_at_one ▸ sq_pos_of_pos hσ_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hbc_ne : b / c ≠ 0 := div_ne_zero hb hc_ne
  have hterm :
      ∀ i : ℕ+,
        S.weightedSourceSeries h_length fTrue i =
          (b / c) * (((i : ℝ) ^ (q - p))⁻¹) := by
    intro i
    have hi_pos : 0 < (i : ℝ) := by
      exact_mod_cast i.2
    have hi_ne : (i : ℝ) ≠ 0 := ne_of_gt hi_pos
    -- Rewrite the weighted coefficient using the decay laws and combine powers once.
    rw [weightedSourceSeries_apply, h_fourierDecay i, h_singularDecay i]
    calc
      b * (i : ℝ) ^ (-q) / (c * (i : ℝ) ^ (-p))
          = b * (i : ℝ) ^ (-q) * (((i : ℝ) ^ (-p))⁻¹ * c⁻¹) := by
              rw [div_eq_mul_inv, mul_inv_rev]
      _ = b * (i : ℝ) ^ (-q) * ((i : ℝ) ^ p * c⁻¹) := by
            rw [Real.rpow_neg (le_of_lt hi_pos) p]
            simp
      _ = (b / c) * ((i : ℝ) ^ (-q) * (i : ℝ) ^ p) := by
            rw [div_eq_mul_inv]
            ring
      _ = ((i : ℝ) ^ (p - q)) * (b / c) := by
            rw [mul_comm, ← Real.rpow_add hi_pos]
            simp [sub_eq_add_neg, add_comm]
      _ = (b / c) * ((i : ℝ) ^ (p - q)) := by
            ring
      _ = (b / c) * (((i : ℝ) ^ (q - p))⁻¹) := by
            rw [show p - q = -(q - p) by ring, Real.rpow_neg (le_of_lt hi_pos) (q - p)]
  have habs :
      (fun n : ℕ ↦ (b / c) * (1 / |(n : ℝ) + 1| ^ (q - p))) =
        fun n : ℕ ↦ (b / c) * ((((n : ℝ) + 1) ^ (q - p))⁻¹) := by
    funext n
    have hn_nonneg : 0 ≤ (n : ℝ) + 1 := by
      positivity
    simp [one_div, abs_of_nonneg hn_nonneg]
  have hs_shift :
      Summable (fun n : ℕ ↦ (b / c) * ((((n : ℝ) + 1) ^ (q - p))⁻¹)) ↔
        1 < q - p := by
    rw [← habs]
    exact
      (summable_mul_left_iff (a := b / c) (f := fun n : ℕ ↦ 1 / |(n : ℝ) + 1| ^ (q - p))
        hbc_ne).trans (Real.summable_one_div_nat_add_rpow 1 (q - p))
  have hreindex :
      (fun n : ℕ => S.weightedSourceSeries h_length fTrue (Equiv.pnatEquivNat.symm n)) =
        fun n : ℕ ↦ (b / c) * ((((n : ℝ) + 1) ^ (q - p))⁻¹) := by
    funext n
    simpa [Equiv.pnatEquivNat, Nat.succPNat_coe] using
      hterm (Equiv.pnatEquivNat.symm n)
  have hs_pnat :
      Summable (S.weightedSourceSeries h_length fTrue) ↔
        Summable (fun n : ℕ ↦ (b / c) * ((((n : ℝ) + 1) ^ (q - p))⁻¹)) := by
    constructor <;> intro hs
    · have hs' :
          Summable fun n : ℕ =>
            S.weightedSourceSeries h_length fTrue (Equiv.pnatEquivNat.symm n) :=
        Equiv.pnatEquivNat.symm.summable_iff.mpr hs
      exact hreindex ▸ hs'
    · have hs' :
          Summable fun n : ℕ =>
            S.weightedSourceSeries h_length fTrue (Equiv.pnatEquivNat.symm n) :=
        hreindex.symm ▸ hs
      exact Equiv.pnatEquivNat.symm.summable_iff.mp hs'
  calc
    Summable (S.weightedSourceSeries h_length fTrue)
        ↔ Summable (fun n : ℕ ↦ (b / c) * ((((n : ℝ) + 1) ^ (q - p))⁻¹)) := hs_pnat
    _ ↔ 1 < q - p := hs_shift
    _ ↔ q > p + 1 := by
          constructor <;> intro h <;> linarith

end ContinuousLinearMap.SingularSystem
