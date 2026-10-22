/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Lemma_5_18

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: rewrite `𝔼[Y_n^2]` as a tail integral of the truncated square, bound the tail by
-- the tail of `|X₁|`, interchange the positive series with the integral, and apply the preceding
-- tail-sum estimate from Lemma 5.19.
omit [MeasurableSpace Ω] in
/-- Helper for Lemma 5.20: the absolute value of the strong-law truncation matches the standard
nonnegative truncation. -/
private theorem abs_strongLawTruncation_eq_truncation_abs
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    |strongLawTruncation X n ω| =
      truncation (fun ω ↦ |X (n + 1) ω|) (n + 1 : ℝ) ω := by
  -- Proof comment: rewrite the nonnegative truncation as an indicator on `(0, n + 1]` and compare
  -- it pointwise with the absolute value of the textbook truncation.
  rw [truncation_eq_of_nonneg fun x ↦ abs_nonneg (X (n + 1) x)]
  by_cases h : |X (n + 1) ω| ≤ (n + 1 : ℝ)
  · by_cases hzero : X (n + 1) ω = 0
    · simp [strongLawTruncation_apply, Function.comp, Set.indicator, hzero]
    · have hmem : |X (n + 1) ω| ∈ Set.Ioc (0 : ℝ) (n + 1 : ℝ) := by
        refine ⟨abs_pos.mpr hzero, h⟩
      simp [strongLawTruncation_apply, Function.comp, Set.indicator, h, hmem]
  · have hnotmem : |X (n + 1) ω| ∉ Set.Ioc (0 : ℝ) (n + 1 : ℝ) := by
      simp [Set.mem_Ioc, h, not_false_eq_true]
    simp [strongLawTruncation_apply, Function.comp, Set.indicator, h, hnotmem]

/-- Helper for Lemma 5.20: the squared truncation moment depends only on the common law of the
sequence. -/
private theorem expectation_sq_strongLawTruncation_eq_expectation_sq_truncation_abs_X1
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (n : ℕ) :
    P[fun ω ↦ strongLawTruncation X n ω ^ 2] =
      P[fun ω ↦ truncation (fun ω ↦ |X 1 ω|) (n + 1 : ℝ) ω ^ 2] := by
  have h_ident_trunc_sq :
      IdentDistrib
        (fun ω ↦ truncation (fun ω ↦ |X (n + 1) ω|) (n + 1 : ℝ) ω ^ 2)
        (fun ω ↦ truncation (fun ω ↦ |X 1 ω|) (n + 1 : ℝ) ω ^ 2)
        P P := by
    -- Proof comment: identical distribution is preserved by absolute value, truncation, and
    -- squaring, so the two truncated second moments have the same integral.
    simpa [Function.comp] using (((hX_ident n).norm.truncation).sq)
  calc
    P[fun ω ↦ strongLawTruncation X n ω ^ 2]
        = P[fun ω ↦ |strongLawTruncation X n ω| ^ 2] := by
            -- Proof comment: replace the square by the square of the absolute value.
            congr 1
            ext ω
            exact (sq_abs (strongLawTruncation X n ω)).symm
    _ = P[fun ω ↦ truncation (fun ω ↦ |X (n + 1) ω|) (n + 1 : ℝ) ω ^ 2] := by
            -- Proof comment: the previous helper identifies the absolute truncation pointwise.
            congr 1
            ext ω
            exact congrArg (fun t : ℝ ↦ t ^ 2)
              (abs_strongLawTruncation_eq_truncation_abs X n ω)
    _ = P[fun ω ↦ truncation (fun ω ↦ |X 1 ω|) (n + 1 : ℝ) ω ^ 2] := by
            exact h_ident_trunc_sq.integral_eq

/-- Helper for Lemma 5.20: every finite weighted partial sum of the truncated second moments is
bounded by `2 𝔼[|X₁|]`. -/
private theorem partial_sum_expectation_sq_strongLawTruncation_le_two_mul_expectation_abs
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_integrable : Integrable (X 1) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (K : ℕ) :
    ∑ n ∈ Finset.range K, P[fun ω ↦ strongLawTruncation X n ω ^ 2] / ((n + 1 : ℝ) ^ 2)
      ≤ 2 * P[fun ω ↦ |X 1 ω|] := by
  letI : MeasureSpace Ω := ⟨P⟩
  letI : IsProbabilityMeasure (ℙ : Measure Ω) := by
    simpa [MeasureSpace.volume] using (inferInstance : IsProbabilityMeasure P)
  let Z := fun ω ↦ |X 1 ω|
  have hsum := sum_variance_truncation_le
    (by simpa [Z] using hX_integrable.norm)
    (by intro ω; simp) (K + 1)
  calc
    ∑ n ∈ Finset.range K, P[fun ω ↦ strongLawTruncation X n ω ^ 2] / ((n + 1 : ℝ) ^ 2)
      = ∑ n ∈ Finset.range K,
          (((n + 1 : ℝ) ^ 2)⁻¹ *
            P[fun ω ↦ truncation Z (n + 1 : ℝ) ω ^ 2]) := by
            -- Proof comment: rewrite each term using the law-invariant truncation moment identity.
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [expectation_sq_strongLawTruncation_eq_expectation_sq_truncation_abs_X1 P X
              hX_ident]
            rw [div_eq_mul_inv, mul_comm]
    _ = ∑ j ∈ Finset.range (K + 1),
          (((j : ℝ) ^ 2)⁻¹ * P[fun ω ↦ truncation Z j ω ^ 2]) := by
          -- Proof comment: add the harmless `j = 0` term to match mathlib's truncation estimate.
          symm
          rw [Finset.sum_range_succ']
          simp [truncation_zero, Z]
    _ ≤ 2 * P[fun ω ↦ |X 1 ω|] := by
          simpa [Z] using hsum

/-- Lemma 5.20: for an identically distributed real sequence, the normalized second moments of the
truncated variables `Yₙ = Xₙ 1_{|Xₙ| ≤ n}` form a series bounded by `4 𝔼[|X₁|]`. -/
theorem tsum_expectation_sq_strongLawTruncation_le_four_mul_expectation_abs
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_integrable : Integrable (X 1) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P) :
    (∑' n : ℕ, P[fun ω ↦ strongLawTruncation X n ω ^ 2] / ((n + 1 : ℝ) ^ 2)) ≤
      4 * P[fun ω ↦ |X 1 ω|] := by
  have hnonneg_term :
      ∀ n : ℕ, 0 ≤ P[fun ω ↦ strongLawTruncation X n ω ^ 2] / ((n + 1 : ℝ) ^ 2) := by
    intro n
    have hnum : 0 ≤ P[fun ω ↦ strongLawTruncation X n ω ^ 2] := by
      exact integral_nonneg fun ω ↦ sq_nonneg (strongLawTruncation X n ω)
    exact div_nonneg hnum (sq_nonneg ((n + 1 : ℝ)))
  have hpartial :
      ∀ K : ℕ,
        ∑ n ∈ Finset.range K, P[fun ω ↦ strongLawTruncation X n ω ^ 2] / ((n + 1 : ℝ) ^ 2) ≤
          4 * P[fun ω ↦ |X 1 ω|] := by
    intro K
    have htwo := partial_sum_expectation_sq_strongLawTruncation_le_two_mul_expectation_abs
      P X hX_integrable hX_ident K
    have habs_nonneg : 0 ≤ P[fun ω ↦ |X 1 ω|] := by
      exact integral_nonneg fun ω ↦ abs_nonneg (X 1 ω)
    linarith
  -- Proof comment: the finite partial sums are nonnegative and uniformly bounded, so the series
  -- is bounded by the same constant; the stronger intermediate factor `2` implies the stated `4`.
  exact Real.tsum_le_of_sum_range_le hnonneg_term hpartial
