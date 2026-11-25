/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

import Mathlib.Analysis.MeanInequalities

/-!
# A finite spectral model for Theorem 7.29

The effective parameter of the book's discrete filter is `τ = N * α`.
For a matched source, whose squared solution coefficients all equal `σ² / κ`,
the expected GCV score and the actual predictive risk have the same minimizer
`τ = κ`.  These finite sum statements require no quadrature approximation.
Two distinct eigenvalues are necessary for GCV uniqueness: for a scalar
influence matrix GCV is constant in the parameter.
-/

noncomputable section

open scoped BigOperators

namespace TikhonovGcv.MatchedSource

variable {ι : Type*} [Fintype ι]

/-- Expected GCV after removal of its positive parameter-independent factor. -/
def gcvScore (κ : ℝ) (eig : ι → ℝ) (τ : ℝ) : ℝ :=
  (∑ i, (κ + eig i) / (τ + eig i) ^ 2) / (∑ i, 1 / (τ + eig i)) ^ 2

/-- True prediction error after removal of its positive noise/size factor. -/
def predictiveScore (κ : ℝ) (eig : ι → ℝ) (τ : ℝ) : ℝ :=
  ∑ i, eig i * (τ ^ 2 / κ + eig i) / (τ + eig i) ^ 2

private lemma weighted_residual_sum
    (a w : ι → ℝ) (hw : ∀ i, 0 < w i) (hS : (∑ i, w i) ≠ 0) :
    (∑ i, (a i - (∑ j, a j) / (∑ j, w j) * w i) ^ 2 / w i) =
      (∑ i, a i ^ 2 / w i) - (∑ i, a i) ^ 2 / (∑ i, w i) := by
  have hterm (i : ι) :
      (a i - (∑ j, a j) / (∑ j, w j) * w i) ^ 2 / w i =
        a i ^ 2 / w i - 2 * ((∑ j, a j) / (∑ j, w j)) * a i +
          ((∑ j, a j) / (∑ j, w j)) ^ 2 * w i := by
    field_simp [ne_of_gt (hw i)]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  field_simp [hS]
  ring

private lemma weighted_quotient_equality
    (a w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hS : (∑ i, w i) ≠ 0) (hT : (∑ i, a i) ≠ 0)
    (heq : (∑ i, a i ^ 2 / w i) / (∑ i, a i) ^ 2 = 1 / (∑ i, w i)) :
    ∀ i, a i = (∑ j, a j) / (∑ j, w j) * w i := by
  have hQ : (∑ i, a i ^ 2 / w i) = (∑ i, a i) ^ 2 / (∑ i, w i) := by
    apply (div_eq_iff (pow_ne_zero 2 hT)).mp at heq
    simpa [div_eq_mul_inv, mul_comm] using heq
  have hzero :
      (∑ i, (a i - (∑ j, a j) / (∑ j, w j) * w i) ^ 2 / w i) = 0 := by
    rw [weighted_residual_sum a w hw hS, hQ, sub_self]
  have hnonneg (i : ι) :
      0 ≤ (a i - (∑ j, a j) / (∑ j, w j) * w i) ^ 2 / w i :=
    div_nonneg (sq_nonneg _) (hw i).le
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hnonneg j)).mp hzero i
    (Finset.mem_univ i)
  have : (a i - (∑ j, a j) / (∑ j, w j) * w i) ^ 2 = 0 :=
    (div_eq_zero_iff).mp hi |>.resolve_right (ne_of_gt (hw i))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)

lemma gcvScore_at_match
    (κ : ℝ) (eig : ι → ℝ) (hκ : 0 < κ) (heig : ∀ i, 0 ≤ eig i)
    [Nonempty ι] :
    gcvScore κ eig κ = 1 / (∑ i, 1 / (κ + eig i)) := by
  have hpos (i : ι) : 0 < κ + eig i := add_pos_of_pos_of_nonneg hκ (heig i)
  have hsum : 0 < ∑ i, 1 / (κ + eig i) :=
    Finset.sum_pos (fun i _ ↦ one_div_pos.mpr (hpos i)) Finset.univ_nonempty
  unfold gcvScore
  have hterm (i : ι) : (κ + eig i) / (κ + eig i) ^ 2 = 1 / (κ + eig i) := by
    field_simp [ne_of_gt (hpos i)]
  simp_rw [hterm]
  field_simp [ne_of_gt hsum]

lemma gcvScore_min
    (κ : ℝ) (eig : ι → ℝ) (hκ : 0 < κ) (heig : ∀ i, 0 ≤ eig i)
    [Nonempty ι] {τ : ℝ} (hτ : 0 < τ) :
    gcvScore κ eig κ ≤ gcvScore κ eig τ := by
  have hκeig (i : ι) : 0 < κ + eig i := add_pos_of_pos_of_nonneg hκ (heig i)
  have hτeig (i : ι) : 0 < τ + eig i := add_pos_of_pos_of_nonneg hτ (heig i)
  have hS : 0 < ∑ i, 1 / (κ + eig i) :=
    Finset.sum_pos (fun i _ ↦ one_div_pos.mpr (hκeig i)) Finset.univ_nonempty
  have hT : 0 < ∑ i, 1 / (τ + eig i) :=
    Finset.sum_pos (fun i _ ↦ one_div_pos.mpr (hτeig i)) Finset.univ_nonempty
  have hcs := Finset.sq_sum_div_le_sum_sq_div Finset.univ
    (fun i ↦ 1 / (τ + eig i)) (fun i _ ↦ one_div_pos.mpr (hκeig i))
  have hterm (i : ι) : (1 / (τ + eig i)) ^ 2 / (1 / (κ + eig i)) =
      (κ + eig i) / (τ + eig i) ^ 2 := by
    field_simp
  simp_rw [hterm] at hcs
  rw [gcvScore_at_match κ eig hκ heig]
  unfold gcvScore
  apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
  simpa [div_eq_mul_inv, mul_comm] using hcs

lemma gcvScore_eq_min_iff
    (κ : ℝ) (eig : ι → ℝ) (hκ : 0 < κ) (heig : ∀ i, 0 ≤ eig i)
    (hdistinct : ∃ i j, eig i ≠ eig j) {τ : ℝ} (hτ : 0 < τ) :
    gcvScore κ eig τ = gcvScore κ eig κ ↔ τ = κ := by
  obtain ⟨i, j, hij⟩ := hdistinct
  letI : Nonempty ι := ⟨i⟩
  have hκeig (i : ι) : 0 < κ + eig i := add_pos_of_pos_of_nonneg hκ (heig i)
  have hτeig (i : ι) : 0 < τ + eig i := add_pos_of_pos_of_nonneg hτ (heig i)
  constructor
  · intro heq
    rw [gcvScore_at_match κ eig hκ heig] at heq
    have hS : 0 < ∑ i, 1 / (κ + eig i) :=
      Finset.sum_pos (fun i _ ↦ one_div_pos.mpr (hκeig i)) Finset.univ_nonempty
    have hT : 0 < ∑ i, 1 / (τ + eig i) :=
      Finset.sum_pos (fun i _ ↦ one_div_pos.mpr (hτeig i)) Finset.univ_nonempty
    have hterm (i : ι) : (1 / (τ + eig i)) ^ 2 / (1 / (κ + eig i)) =
        (κ + eig i) / (τ + eig i) ^ 2 := by field_simp
    have heq' :
        (∑ i, (1 / (τ + eig i)) ^ 2 / (1 / (κ + eig i))) /
          (∑ i, 1 / (τ + eig i)) ^ 2 = 1 / (∑ i, 1 / (κ + eig i)) := by
      simpa only [hterm, gcvScore] using heq
    have hratio := weighted_quotient_equality
      (fun i ↦ 1 / (τ + eig i)) (fun i ↦ 1 / (κ + eig i))
      (fun i ↦ one_div_pos.mpr (hκeig i)) (ne_of_gt hS) (ne_of_gt hT) heq'
    have hcross :
        (1 / (τ + eig i)) * (1 / (κ + eig j)) =
          (1 / (τ + eig j)) * (1 / (κ + eig i)) := by
      rw [hratio i, hratio j]
      ring
    field_simp [ne_of_gt (hτeig i), ne_of_gt (hτeig j),
      ne_of_gt (hκeig i), ne_of_gt (hκeig j)] at hcross
    have hmul : (τ - κ) * (eig i - eig j) = 0 := by nlinarith [hcross]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hij))
  · rintro rfl
    rfl

private lemma predictive_term_gap
    {κ τ x : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (hx : 0 ≤ x) :
    x * (τ ^ 2 / κ + x) / (τ + x) ^ 2 -
        x * (κ ^ 2 / κ + x) / (κ + x) ^ 2 =
      x ^ 2 * (τ - κ) ^ 2 / (κ * (κ + x) * (τ + x) ^ 2) := by
  have hκx : κ + x ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hκ hx)
  have hτx : τ + x ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hτ hx)
  field_simp [ne_of_gt hκ, hκx, hτx]
  ring

lemma predictiveScore_min
    (κ : ℝ) (eig : ι → ℝ) (hκ : 0 < κ) (heig : ∀ i, 0 ≤ eig i)
    {τ : ℝ} (hτ : 0 < τ) :
    predictiveScore κ eig κ ≤ predictiveScore κ eig τ := by
  apply Finset.sum_le_sum
  intro i _
  have hgap := predictive_term_gap hκ hτ (heig i)
  have hden : 0 < κ * (κ + eig i) * (τ + eig i) ^ 2 :=
    mul_pos (mul_pos hκ (add_pos_of_pos_of_nonneg hκ (heig i)))
      (sq_pos_of_pos (add_pos_of_pos_of_nonneg hτ (heig i)))
  have hnonneg :
      0 ≤ (eig i) ^ 2 * (τ - κ) ^ 2 / (κ * (κ + eig i) * (τ + eig i) ^ 2) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hden.le
  linarith

lemma predictiveScore_eq_min_iff
    (κ : ℝ) (eig : ι → ℝ) (hκ : 0 < κ) (heig : ∀ i, 0 ≤ eig i)
    (hpositive : ∃ i, 0 < eig i) {τ : ℝ} (hτ : 0 < τ) :
    predictiveScore κ eig τ = predictiveScore κ eig κ ↔ τ = κ := by
  constructor
  · intro heq
    obtain ⟨i, hi⟩ := hpositive
    have hgap (j : ι) := predictive_term_gap hκ hτ (heig j)
    have hnonneg (j : ι) :
        0 ≤ (eig j) ^ 2 * (τ - κ) ^ 2 / (κ * (κ + eig j) * (τ + eig j) ^ 2) := by
      apply div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      exact le_of_lt (mul_pos (mul_pos hκ
        (add_pos_of_pos_of_nonneg hκ (heig j)))
        (sq_pos_of_pos (add_pos_of_pos_of_nonneg hτ (heig j))))
    have hsum :
        (∑ j, (eig j) ^ 2 * (τ - κ) ^ 2 /
          (κ * (κ + eig j) * (τ + eig j) ^ 2)) = 0 := by
      simp_rw [← hgap]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr heq
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hnonneg j)).mp hsum i
      (Finset.mem_univ i)
    have hden : κ * (κ + eig i) * (τ + eig i) ^ 2 ≠ 0 := by positivity
    have hnum : (eig i) ^ 2 * (τ - κ) ^ 2 = 0 :=
      (div_eq_zero_iff.mp hz).resolve_right hden
    have ht : (τ - κ) ^ 2 = 0 :=
      (mul_eq_zero.mp hnum).resolve_left (ne_of_gt (sq_pos_of_pos hi))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ht)
  · rintro rfl
    rfl

/-- Normalize the exact finite expected GCV formula.  In particular the
parameter is `τ`, rather than the unscaled discrete parameter `α`. -/
lemma spectralGcv_eq
    [Nonempty ι] (κ σ : ℝ) (eig : ι → ℝ)
    (hκ : 0 < κ) (heig : ∀ i, 0 ≤ eig i) {τ : ℝ} (hτ : 0 < τ) :
    (((1 / (Fintype.card ι : ℝ)) *
        ∑ i, (eig i / (eig i + τ) - 1) ^ 2 * eig i * (σ ^ 2 / κ) +
      (σ ^ 2 / (Fintype.card ι : ℝ)) *
        ∑ i, (eig i / (eig i + τ) - 1) ^ 2) /
      ((((Fintype.card ι : ℝ) - ∑ i, eig i / (eig i + τ)) /
        (Fintype.card ι : ℝ)) ^ 2)) =
      ((Fintype.card ι : ℝ) * σ ^ 2 / κ) * gcvScore κ eig τ := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (∑ i, 1 / (τ + eig i)) ≠ 0 := by
    apply ne_of_gt
    exact Finset.sum_pos
      (fun i _ ↦ one_div_pos.mpr (add_pos_of_pos_of_nonneg hτ (heig i)))
      Finset.univ_nonempty
  have hdev (i : ι) : (eig i / (eig i + τ) - 1) ^ 2 =
      τ ^ 2 * (1 / (τ + eig i) ^ 2) := by
    have hden : eig i + τ ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (heig i) hτ)
    field_simp [hden, add_comm τ (eig i)]
    ring
  have hdef : (Fintype.card ι : ℝ) - ∑ i, eig i / (eig i + τ) =
      τ * ∑ i, 1 / (τ + eig i) := by
    rw [Finset.mul_sum]
    have hNsum : (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
    rw [hNsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hden : eig i + τ ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (heig i) hτ)
    field_simp [hden, add_comm τ (eig i)]
    ring
  have hnum :
      (1 / (Fintype.card ι : ℝ)) *
          ∑ i, (eig i / (eig i + τ) - 1) ^ 2 * eig i * (σ ^ 2 / κ) +
        (σ ^ 2 / (Fintype.card ι : ℝ)) *
          ∑ i, (eig i / (eig i + τ) - 1) ^ 2 =
      (σ ^ 2 * τ ^ 2 / ((Fintype.card ι : ℝ) * κ)) *
        ∑ i, (κ + eig i) / (τ + eig i) ^ 2 := by
    simp_rw [hdev, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt hκ]
    ring
  rw [hnum, hdef]
  unfold gcvScore
  field_simp [hN, ne_of_gt hκ, ne_of_gt hτ, hsum]

/-- Normalize the actual finite spectral prediction-error formula. -/
lemma spectralPredictive_eq
    (κ σ : ℝ) (eig : ι → ℝ)
    (hκ : 0 < κ) (heig : ∀ i, 0 ≤ eig i) {τ : ℝ} (hτ : 0 < τ) :
    (1 / (Fintype.card ι : ℝ)) *
        (∑ i, (eig i / (eig i + τ) - 1) ^ 2 * eig i * (σ ^ 2 / κ)) +
      (σ ^ 2 / (Fintype.card ι : ℝ)) *
        (∑ i, (eig i / (eig i + τ)) ^ 2) =
      (σ ^ 2 / (Fintype.card ι : ℝ)) * predictiveScore κ eig τ := by
  unfold predictiveScore
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hden : eig i + τ ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (heig i) hτ)
  field_simp [hden, ne_of_gt hκ, add_comm τ (eig i)]
  ring

end TikhonovGcv.MatchedSource
