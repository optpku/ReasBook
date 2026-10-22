/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.FirmlyNonexpansiveOn

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped BigOperators InnerProductSpace

variable {ι : Type u} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 4.8: rewrite the exchanged cross terms as diagonal terms minus the
pairwise correction inner product. -/
-- Proof step: expand the pairwise correction by bilinearity and simplify the resulting scalar
-- identity.
private lemma pairwise_inner_exchange_eq_diag_sub_pairwise
    (x u : ι → H) (i j : ι) :
    ⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ =
      ⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ - ⟪x i - x j, u i - u j⟫_ℝ := by
  have h_expand :
      ⟪x i - x j, u i - u j⟫_ℝ =
        ⟪x i, u i⟫_ℝ - ⟪x i, u j⟫_ℝ - ⟪x j, u i⟫_ℝ + ⟪x j, u j⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  nlinarith [h_expand]

/-- Helper for Proposition 4.8: doubling the inner product of two weighted affine combinations
produces the symmetric double sum of exchanged cross terms. -/
-- Proof step: expand the weighted sums by bilinearity, then commute the second double sum so the
-- exchanged cross term appears pointwise.
private lemma two_mul_weighted_inner_eq_sum_exchange
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ) :
    2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ =
      ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) := by
  have h_single :
      ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ =
        ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ := by
    -- First expand both weighted sums inside the real inner product.
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    ring_nf
  calc
    2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ
        = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ) +
            (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ) := by
              rw [h_single]
              ring
    _ = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ) +
          (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x j, u i⟫_ℝ) := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j hj
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [mul_comm (α j) (α i), real_inner_comm]
    _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring

/-- Helper for Proposition 4.8: the diagonal double sum collapses to twice the weighted diagonal
sum when the weights add up to `1`. -/
-- Proof step: separate the two diagonal contributions, then use the weight-sum hypothesis on each
-- of the two inner sums.
private lemma weighted_double_sum_diag_eq_two_mul
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ)
    (hα : ∑ i ∈ s, α i = 1) :
    ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ) =
      2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
  calc
    ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ)
        = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u i⟫_ℝ) +
            (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x j, u j⟫_ℝ) := by
              simp_rw [mul_add, Finset.sum_add_distrib]
    _ = (∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ) + (∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              ∑ j ∈ s, α i * α j * ⟪x i, u i⟫_ℝ
                  = α i * ∑ j ∈ s, α j * ⟪x i, u i⟫_ℝ := by
                      simpa [mul_assoc] using
                        (Finset.mul_sum s (fun j ↦ α j * ⟪x i, u i⟫_ℝ) (α i)).symm
              _ = α i * ((∑ j ∈ s, α j) * ⟪x i, u i⟫_ℝ) := by rw [Finset.sum_mul]
              _ = α i * ⟪x i, u i⟫_ℝ := by rw [hα, one_mul]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j hj
            calc
              ∑ i ∈ s, α i * α j * ⟪x j, u j⟫_ℝ
                  = (∑ i ∈ s, α i) * (α j * ⟪x j, u j⟫_ℝ) := by
                      simpa [mul_assoc] using
                        (Finset.sum_mul s (fun i ↦ α i) (α j * ⟪x j, u j⟫_ℝ)).symm
              _ = α j * ⟪x j, u j⟫_ℝ := by rw [hα, one_mul]
    _ = 2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by ring

/-- Helper for Proposition 4.8: the weighted affine inner product splits into the weighted diagonal
sum minus the half pairwise correction term. -/
-- Proof step: expand the doubled affine-combination inner product, rewrite the exchanged terms by
-- the previous helper, and use the weight sum `1` to collapse the diagonal double sum.
private theorem weighted_affine_inner_eq_sum_inner_add_half_pairwise
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ) (hα : ∑ i ∈ s, α i = 1) :
    ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ =
      ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
  have h_two :
      2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
          ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ =
        2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
    calc
      2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
          ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ
          = (∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ)) +
              ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ := by
              rw [two_mul_weighted_inner_eq_sum_exchange]
      _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j *
            ((⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) + ⟪x i - x j, u i - u j⟫_ℝ) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [pairwise_inner_exchange_eq_diag_sub_pairwise]
              ring
      _ = 2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ :=
            weighted_double_sum_diag_eq_two_mul s x u α hα
  -- Divide the doubled identity by `2` to recover the stated weighted decomposition.
  linarith

/-- Helper for Proposition 4.8: a weighted sum of centered vectors can be rewritten as the weighted
sum minus the center when the coefficients add up to `1`. -/
-- Proof step: distribute the scalar through subtraction and collapse the constant weighted sum with
-- the hypothesis `∑ αᵢ = 1`.
private lemma weighted_sub_eq_sub_of_sum_eq_one
    (s : Finset ι) (α : ι → ℝ) (f : ι → H) (c : H)
    (hα : ∑ i ∈ s, α i = 1) :
    ∑ i ∈ s, α i • (f i - c) = (∑ i ∈ s, α i • f i) - c := by
  calc
    ∑ i ∈ s, α i • (f i - c) = ∑ i ∈ s, (α i • f i - α i • c) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [smul_sub]
    _ = (∑ i ∈ s, α i • f i) - ∑ i ∈ s, α i • c := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ s, α i • f i) - (∑ i ∈ s, α i) • c := by
      rw [← Finset.sum_smul]
    _ = (∑ i ∈ s, α i • f i) - c := by
      rw [hα, one_smul]

/-- Helper for Proposition 4.8: firm nonexpansiveness makes the residual cross term nonnegative. -/
-- Proof step: rewrite the residual difference as `(x - y) - (T x - T y)` and subtract the firm
-- inequality from the resulting inner product expansion.
private lemma firmly_nonexpansiveOn_residual_inner_nonneg
    {T : H → H} {D : Set H} (hT : FirmlyNonexpansiveOn D (fun z : D ↦ T z))
    {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
    0 ≤ ⟪T x - T y, (x - T x) - (y - T y)⟫_ℝ := by
  have hfirm : ‖T x - T y‖ ^ (2 : ℕ) ≤ ⟪T x - T y, x - y⟫_ℝ :=
    by
      simpa [real_inner_comm] using hT ⟨x, hx⟩ ⟨y, hy⟩
  have hres :
      (x - T x) - (y - T y) = (x - y) - (T x - T y) := by
    abel_nf
  -- After expanding the residual term, the target is exactly the firm defect.
  rw [hres, inner_sub_right, real_inner_self_eq_norm_sq]
  linarith

/-- Helper for Proposition 4.8: the inner product of the average and half-difference of `a` and
`b` is one quarter of the corresponding squared-norm gap. -/
-- Proof step: expand `⟪a + b, a - b⟫_ℝ` and observe that the mixed terms cancel by symmetry of the
-- real inner product.
private lemma average_pairing_eq_quarter_norm_gap (a b : H) :
    ⟪(1 / 2 : ℝ) • (a + b), (1 / 2 : ℝ) • (a - b)⟫_ℝ =
      (1 / 4 : ℝ) * (‖a‖ ^ (2 : ℕ) - ‖b‖ ^ (2 : ℕ)) := by
  have h_expand : ⟪a + b, a - b⟫_ℝ = ‖a‖ ^ (2 : ℕ) - ‖b‖ ^ (2 : ℕ) := by
    rw [inner_sub_right, inner_add_left, inner_add_left, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm b a]
    ring
  -- Scaling both arguments by `1/2` contributes the expected quarter factor.
  rw [real_inner_smul_left, real_inner_smul_right, h_expand]
  ring

/-- Helper for Proposition 4.8: scaling a vector by `1/2` scales its squared norm by `1/4`. -/
-- Proof step: rewrite the norm of a scalar multiple and simplify the resulting real identity.
private lemma half_smul_norm_sq (a : H) :
    ‖(1 / 2 : ℝ) • a‖ ^ (2 : ℕ) = (1 / 4 : ℝ) * ‖a‖ ^ (2 : ℕ) := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
  nlinarith [norm_nonneg a]

/-- Proposition 4.8 (1): Zarantonello's weighted identity for the family
`i ↦ (T (x i), x i - T (x i))` at the affine combination `y = ∑ i ∈ s, α i • x i`. -/
-- Proof sketch: apply Lemma 2.14 to the families `i ↦ T (x i) - T y` and
-- `i ↦ (x i - T (x i)) - (y - T y)`, then use `hy` and `hα_sum` to rewrite the barycenters.
theorem zarantonello_weighted_firm_identity
    (s : Finset ι) (T : H → H) (x : ι → H) (α : ι → ℝ) (y : H)
    (hy : y = ∑ i ∈ s, α i • x i) (hα_sum : ∑ i ∈ s, α i = 1) :
    ‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) +
      ∑ i ∈ s, α i * ⟪T y - T (x i), (y - T y) - (x i - T (x i))⟫_ℝ =
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
        α i * α j * ⟪T (x i) - T (x j), (x i - T (x i)) - (x j - T (x j))⟫_ℝ := by
  let u : ι → H := fun i ↦ T (x i) - T y
  let v : ι → H := fun i ↦ (x i - T (x i)) - (y - T y)
  have hcore :
      ⟪∑ i ∈ s, α i • u i, ∑ j ∈ s, α j • v j⟫_ℝ +
          (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪u i - u j, v i - v j⟫_ℝ =
        ∑ i ∈ s, α i * ⟪u i, v i⟫_ℝ :=
    weighted_affine_inner_eq_sum_inner_add_half_pairwise s u v α hα_sum
  have hu_sum :
      ∑ i ∈ s, α i • u i = (∑ i ∈ s, α i • T (x i)) - T y := by
    -- Rewrite the centered image family using the weight sum `1`.
    simpa [u] using weighted_sub_eq_sub_of_sum_eq_one s α (fun i ↦ T (x i)) (T y) hα_sum
  have hv_sum :
      ∑ i ∈ s, α i • v i = T y - ∑ i ∈ s, α i • T (x i) := by
    -- Rewrite the centered residual family and then use the barycenter identity for `y`.
    calc
      ∑ i ∈ s, α i • v i
          = (∑ i ∈ s, α i • (x i - T (x i))) - (y - T y) := by
              simpa [v] using
                weighted_sub_eq_sub_of_sum_eq_one s α
                  (fun i ↦ x i - T (x i)) (y - T y) hα_sum
      _ = ((∑ i ∈ s, α i • x i) - ∑ i ∈ s, α i • T (x i)) - (y - T y) := by
            have hsplit :
                ∑ i ∈ s, α i • (x i - T (x i)) =
                  (∑ i ∈ s, α i • x i) - ∑ i ∈ s, α i • T (x i) := by
              calc
                ∑ i ∈ s, α i • (x i - T (x i))
                    = ∑ i ∈ s, (α i • x i - α i • T (x i)) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        rw [smul_sub]
                _ = (∑ i ∈ s, α i • x i) - ∑ i ∈ s, α i • T (x i) := by
                      rw [Finset.sum_sub_distrib]
            rw [hsplit]
      _ = T y - ∑ i ∈ s, α i • T (x i) := by
            rw [hy]
            abel_nf
  have hpairwise :
      ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪u i - u j, v i - v j⟫_ℝ =
        ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * ⟪T (x i) - T (x j), (x i - T (x i)) - (x j - T (x j))⟫_ℝ := by
    -- The pairwise differences lose the centered basepoint `y`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    have huij : u i - u j = T (x i) - T (x j) := by
      dsimp [u]
      abel_nf
    have hvij : v i - v j = (x i - T (x i)) - (x j - T (x j)) := by
      dsimp [v]
      abel_nf
    rw [huij, hvij]
  have hdiag :
      ∑ i ∈ s, α i * ⟪u i, v i⟫_ℝ =
        ∑ i ∈ s, α i * ⟪T y - T (x i), (y - T y) - (x i - T (x i))⟫_ℝ := by
    -- Each diagonal term is unchanged because both arguments are simultaneously negated.
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hinner :
        ⟪u i, v i⟫_ℝ = ⟪T y - T (x i), (y - T y) - (x i - T (x i))⟫_ℝ := by
      dsimp [u, v]
      have hterm : T (x i) - T y = -(T y - T (x i)) := by
        abel_nf
      have hres : (x i - T (x i)) - (y - T y) = -((y - T y) - (x i - T (x i))) := by
        abel_nf
      rw [hterm, hres, inner_neg_left, inner_neg_right]
      ring
    rw [hinner]
  rw [hu_sum, hv_sum, hpairwise, hdiag] at hcore
  have hinner :
      ⟪(∑ i ∈ s, α i • T (x i)) - T y, T y - ∑ i ∈ s, α i • T (x i)⟫_ℝ =
        -‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) := by
    have hneg :
        T y - ∑ i ∈ s, α i • T (x i) =
          -((∑ i ∈ s, α i • T (x i)) - T y) := by
      abel_nf
    -- The two centered barycenters are negatives of one another.
    rw [hneg, inner_neg_right, real_inner_self_eq_norm_sq, norm_neg, norm_sub_rev]
  rw [hinner] at hcore
  -- Move the negative squared norm to the other side to obtain the displayed identity.
  linarith

/-- Proposition 4.8 (2): if `T` is firmly nonexpansive on a convex set containing the weighted
family and the barycenter `y` of nonnegative weights summing to `1`, in the canonical
restricted-map sense, then
Zarantonello's identity yields the stated upper bound. -/
-- Proof sketch: use `Convex.sum_mem` and the nonnegativity of the weights to place the barycenter in
-- `D`, apply part (1), and estimate the correction term by firm nonexpansiveness.
theorem zarantonello_weighted_firm_inequality
    (s : Finset ι) (D : Set H) (hD : Convex ℝ D) (T : H → H) (x : ι → H) (α : ι → ℝ) (y : H)
    (hy : y = ∑ i ∈ s, α i • x i) (hα_nonneg : ∀ i ∈ s, 0 ≤ α i)
    (hα_sum : ∑ i ∈ s, α i = 1) (hx : ∀ i ∈ s, x i ∈ D)
    (hT : FirmlyNonexpansiveOn D (fun z : D ↦ T z)) :
    ‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
        α i * α j * ⟪T (x i) - T (x j), (x i - T (x i)) - (x j - T (x j))⟫_ℝ := by
  have hy_mem : y ∈ D := by
    -- Nonnegative coefficients summing to `1` keep the barycenter inside the convex set.
    rw [hy]
    exact hD.sum_mem hα_nonneg hα_sum hx
  have hcorrection_nonneg :
      0 ≤ ∑ i ∈ s, α i * ⟪T y - T (x i), (y - T y) - (x i - T (x i))⟫_ℝ := by
    -- Each correction term is nonnegative by firm nonexpansiveness, and each weight is nonnegative.
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg (hα_nonneg i hi)
      (firmly_nonexpansiveOn_residual_inner_nonneg hT hy_mem (hx i hi))
  have hidentity :=
    zarantonello_weighted_firm_identity s T x α y hy hα_sum
  -- Drop the nonnegative correction sum from the exact identity.
  linarith

/-- Proposition 4.8 (3): the weighted identity from part (1) can be rewritten as a difference of
squared norms for `T` and the identity map. -/
-- Proof sketch: apply part (1) to the averaged map `fun z ↦ (z + T z) / 2` and simplify the
-- resulting inner products into differences of squared norms.
theorem zarantonello_weighted_nonexpansive_identity
    (s : Finset ι) (T : H → H) (x : ι → H) (α : ι → ℝ) (y : H)
    (hy : y = ∑ i ∈ s, α i • x i) (hα_sum : ∑ i ∈ s, α i = 1) :
    ‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) +
      ∑ i ∈ s, α i * (‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ)) =
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
        α i * α j * (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ)) := by
  let S : H → H := fun z ↦ (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • T z
  have hidentity := zarantonello_weighted_firm_identity s S x α y hy hα_sum
  have hsumS :
      ∑ i ∈ s, α i • S (x i) =
        (1 / 2 : ℝ) • (∑ i ∈ s, α i • x i) + (1 / 2 : ℝ) • (∑ i ∈ s, α i • T (x i)) := by
    -- Expand the weighted average map into the two weighted component sums.
    calc
      ∑ i ∈ s, α i • S (x i)
          = ∑ i ∈ s, ((1 / 2 : ℝ) • (α i • x i) + (1 / 2 : ℝ) • (α i • T (x i))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              dsimp [S]
              rw [smul_add]
              simp [smul_smul, mul_comm]
      _ = (∑ i ∈ s, (1 / 2 : ℝ) • (α i • x i)) +
            ∑ i ∈ s, (1 / 2 : ℝ) • (α i • T (x i)) := by
              rw [Finset.sum_add_distrib]
      _ = (1 / 2 : ℝ) • (∑ i ∈ s, α i • x i) + (1 / 2 : ℝ) • (∑ i ∈ s, α i • T (x i)) := by
              rw [← Finset.smul_sum, ← Finset.smul_sum]
  have hleft :
      S y - ∑ i ∈ s, α i • S (x i) =
        (1 / 2 : ℝ) • (T y - ∑ i ∈ s, α i • T (x i)) := by
    -- The `x`-part cancels because `y` is the weighted barycenter.
    rw [hsumS, hy]
    dsimp [S]
    rw [← smul_add, ← smul_add, ← smul_sub]
    congr 1
    abel_nf
  have hnorm :
      ‖S y - ∑ i ∈ s, α i • S (x i)‖ ^ (2 : ℕ) =
        (1 / 4 : ℝ) * ‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) := by
    rw [hleft, half_smul_norm_sq]
  have hcorrection :
      ∑ i ∈ s, α i * ⟪S y - S (x i), (y - S y) - (x i - S (x i))⟫_ℝ =
        (1 / 4 : ℝ) * ∑ i ∈ s,
          α i * (‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ)) := by
    -- Each correction term for `S` is one quarter of the corresponding norm gap.
    have hresidual (z : H) : z - S z = (1 / 2 : ℝ) • (z - T z) := by
      dsimp [S]
      nth_rewrite 1 [show z = (1 : ℝ) • z by rw [one_smul]]
      have hone : (1 : ℝ) = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
        norm_num
      rw [hone, add_smul]
      norm_num
      simpa [sub_eq_add_neg] using (smul_sub (1 / 2 : ℝ) z (T z)).symm
    calc
      ∑ i ∈ s, α i * ⟪S y - S (x i), (y - S y) - (x i - S (x i))⟫_ℝ
          = ∑ i ∈ s,
              α i * ((1 / 4 : ℝ) *
                (‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ))) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have havg :
                      S y - S (x i) =
                        (1 / 2 : ℝ) • ((y - x i) + (T y - T (x i))) := by
                    dsimp [S]
                    rw [← smul_add, ← smul_add, ← smul_sub]
                    congr 1
                    abel_nf
                  have hres :
                      (y - S y) - (x i - S (x i)) =
                        (1 / 2 : ℝ) • ((y - x i) - (T y - T (x i))) := by
                    rw [hresidual, hresidual, ← smul_sub]
                    congr 1
                    abel_nf
                  rw [havg, hres, average_pairing_eq_quarter_norm_gap]
      _ = (1 / 4 : ℝ) * ∑ i ∈ s,
            α i * (‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
  have hpairwise_sum :
      ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * ⟪S (x i) - S (x j), (x i - S (x i)) - (x j - S (x j))⟫_ℝ =
        (1 / 4 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ)) := by
    have hresidual (z : H) : z - S z = (1 / 2 : ℝ) • (z - T z) := by
      dsimp [S]
      nth_rewrite 1 [show z = (1 : ℝ) • z by rw [one_smul]]
      have hone : (1 : ℝ) = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
        norm_num
      rw [hone, add_smul]
      norm_num
      simpa [sub_eq_add_neg] using (smul_sub (1 / 2 : ℝ) z (T z)).symm
    calc
      ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * ⟪S (x i) - S (x j), (x i - S (x i)) - (x j - S (x j))⟫_ℝ
          = ∑ i ∈ s, ∑ j ∈ s,
              α i * α j * ((1 / 4 : ℝ) *
                (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ))) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  have havg :
                      S (x i) - S (x j) =
                        (1 / 2 : ℝ) • ((x i - x j) + (T (x i) - T (x j))) := by
                    dsimp [S]
                    rw [← smul_add, ← smul_add, ← smul_sub]
                    congr 1
                    abel_nf
                  have hres :
                      (x i - S (x i)) - (x j - S (x j)) =
                        (1 / 2 : ℝ) • ((x i - x j) - (T (x i) - T (x j))) := by
                    rw [hresidual, hresidual, ← smul_sub]
                    congr 1
                    abel_nf
                  rw [havg, hres, average_pairing_eq_quarter_norm_gap]
      _ = (1 / 4 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
            α i * α j * (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
  have hpairwise :
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * ⟪S (x i) - S (x j), (x i - S (x i)) - (x j - S (x j))⟫_ℝ =
        (1 / 8 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ)) := by
    -- Combine the quarter factor from the pairwise rewrite with the outer prefactor `1/2`.
    rw [hpairwise_sum]
    ring
  rw [hnorm, hcorrection, hpairwise] at hidentity
  -- Clearing the quarter factor recovers the announced norm-difference identity.
  linarith

/-- Proposition 4.8 (4): if `T` is nonexpansive on a convex set containing the weighted family and
the barycenter `y` of nonnegative weights summing to `1`, then part (3) yields the corresponding
upper bound. -/
-- Proof sketch: use `Convex.sum_mem` to place the barycenter in `D`, apply part
-- (3), and estimate each squared-norm difference by the nonexpansive bound.
theorem zarantonello_weighted_nonexpansive_inequality
    (s : Finset ι) (D : Set H) (hD : Convex ℝ D) (T : H → H) (x : ι → H) (α : ι → ℝ) (y : H)
    (hy : y = ∑ i ∈ s, α i • x i) (hα_nonneg : ∀ i ∈ s, 0 ≤ α i)
    (hα_sum : ∑ i ∈ s, α i = 1) (hx : ∀ i ∈ s, x i ∈ D) (hT : LipschitzOnWith 1 T D) :
    ‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
        α i * α j * (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ)) := by
  have hy_mem : y ∈ D := by
    -- Nonnegative coefficients summing to `1` keep the barycenter inside the convex set.
    rw [hy]
    exact hD.sum_mem hα_nonneg hα_sum hx
  have hcorrection_nonneg :
      0 ≤ ∑ i ∈ s, α i * (‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ)) := by
    -- Each gap is nonnegative because `T` is `1`-Lipschitz on `D`.
    refine Finset.sum_nonneg ?_
    intro i hi
    have hdist' : dist (T y) (T (x i)) ≤ dist y (x i) := by
      simpa [edist_dist] using hT hy_mem (hx i hi)
    have hdist : ‖T y - T (x i)‖ ≤ ‖y - x i‖ := by
      simpa [dist_eq_norm] using hdist'
    have hsq :
        ‖T y - T (x i)‖ ^ (2 : ℕ) ≤ ‖y - x i‖ ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hdist
    have hgap : 0 ≤ ‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ) := by
      linarith
    exact mul_nonneg (hα_nonneg i hi) hgap
  have hidentity :=
    zarantonello_weighted_nonexpansive_identity s T x α y hy hα_sum
  -- Drop the nonnegative correction sum from the exact norm-gap identity.
  linarith
