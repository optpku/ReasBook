/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H]
variable {D : Set H}

/-- Helper for Proposition 4.35: on a subtype domain, `LipschitzWith 1` is equivalent to the
pairwise nonexpansive norm inequality. -/
-- Proof sketch: rewrite the metric Lipschitz estimate using `Subtype.dist_eq` and `dist_eq_norm`.
private lemma lipschitzWith_one_iff_pairwise_norm_sub_le {T : D → H} :
    LipschitzWith 1 T ↔ ∀ x y : D, ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
  constructor
  · intro hT x y
    -- Convert the ambient metric bound into the norm estimate on `H`.
    simpa [Subtype.dist_eq, dist_eq_norm] using hT.dist_le_mul x y
  · intro hT
    -- Repackage the pointwise norm control as a Lipschitz estimate.
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [Subtype.dist_eq, dist_eq_norm] using hT x y

/-- Helper for Proposition 4.35: comparing the squared norms of two vectors is equivalent to
comparing their norms. -/
-- Proof sketch: use `sq_le_sq` and the nonnegativity of norms to remove absolute values.
private lemma norm_sq_le_norm_sq_iff {x y : H} : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 ↔ ‖x‖ ≤ ‖y‖ := by
  constructor
  · intro h
    have hsq := sq_le_sq.mp h
    -- Norms are nonnegative, so the square comparison reduces to the usual order comparison.
    simpa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg y)] using hsq
  · intro h
    -- Squaring preserves the inequality because both norms are nonnegative.
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg y)] using h

/-- Helper for Proposition 4.35: the residual difference `((Id - T) x) - ((Id - T) y)` is
`(x - y) - (T x - T y)`. -/
-- Proof sketch: expand both subtractions and reassociate the resulting sum.
private lemma residual_difference_eq {T : D → H} (x y : D) :
    ((x : H) - T x) - (y - T y) = ((x : H) - y) - (T x - T y) := by
  -- This is the canonical regrouping of the residual terms.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {D : Set H}

/-- Helper for Proposition 4.35: subtracting the affine transform at two points produces the
expected affine combination of the input and output differences. -/
-- Proof sketch: expand the subtraction and regroup the two scalar multiples separately.
private lemma averaging_transform_sub {α : ℝ} {T : D → H} (x y : D) :
    ((1 - 1 / α) • (x : H) + (1 / α) • T x) -
        ((1 - 1 / α) • (y : H) + (1 / α) • T y) =
      (1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y) := by
  -- Both sides are the same affine difference after distributing subtraction over addition.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add]

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H}

/-- Helper for Proposition 4.35: the affine transform is nonexpansive exactly when the residual
quadratic inequality from clause (3) holds. -/
-- Proof sketch: translate nonexpansiveness into a squared norm comparison, apply the identity from
-- Lemma 2.17, and divide by the positive scalar `α`.
private theorem averaging_transform_lipschitz_iff_residual_ineq
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {T : D → H} :
    LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • T x) ↔
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 -
            ((1 - α) / α) * ‖((x : H) - T x) - (y - T y)‖ ^ 2 := by
  rw [lipschitzWith_one_iff_pairwise_norm_sub_le]
  constructor
  · intro hS x y
    -- First square the nonexpansive estimate for the affine transform.
    have hSxy := hS x y
    rw [averaging_transform_sub] at hSxy
    have hsq :
        ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
      exact (norm_sq_le_norm_sq_iff).2 hSxy
    have hnonneg :
        0 ≤ α ^ 2 *
          (‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2) := by
      -- Multiplying by the positive factor `α^2` preserves nonnegativity.
      nlinarith [hsq, hα.1]
    have hrewrite :
        0 ≤ α *
          (‖(x : H) - y‖ ^ 2 -
            α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 -
              ‖T x - T y‖ ^ 2) := by
      -- Lemma 2.17 rewrites the scaled squared-norm gap into the residual expression.
      rwa [alpha_sq_norm_sq_sub_inv_affine_combination_eq_norm_sub
        ((x : H) - y) (T x - T y) hα] at hnonneg
    have hgap :
        0 ≤ ‖(x : H) - y‖ ^ 2 -
          α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 -
            ‖T x - T y‖ ^ 2 := by
      -- Divide by the positive scalar `α`.
      nlinarith [hrewrite, hα.1]
    have htarget :
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 -
            α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 := by
      -- Rearranging isolates the `‖T x - T y‖^2` term.
      nlinarith [hgap]
    -- Rewrite the residual difference into the displayed `(Id - T)` form.
    simpa [div_eq_mul_inv, mul_comm, residual_difference_eq] using htarget
  · intro hS x y
    -- Start from clause (3) and rewrite it in the `d - t` form from the quadratic identity.
    have htarget :
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 -
            α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 := by
      simpa [div_eq_mul_inv, mul_comm, residual_difference_eq] using hS x y
    have hgap :
        0 ≤ ‖(x : H) - y‖ ^ 2 -
          α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 -
            ‖T x - T y‖ ^ 2 := by
      -- Move the right-hand side of clause (3) to the left.
      nlinarith [htarget]
    have hnonneg :
        0 ≤ α *
          (‖(x : H) - y‖ ^ 2 -
            α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 -
              ‖T x - T y‖ ^ 2) := by
      -- Multiply by the positive scalar `α`.
      nlinarith [hgap, hα.1]
    have hrewrite :
        0 ≤ α ^ 2 *
          (‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2) := by
      -- Lemma 2.17 identifies the same quadratic quantity.
      rw [alpha_sq_norm_sq_sub_inv_affine_combination_eq_norm_sub
        ((x : H) - y) (T x - T y) hα]
      exact hnonneg
    have hsq :
        ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
      -- Remove the positive factor `α^2`.
      have hgap' :
          0 ≤ ‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 := by
        have hαsq : 0 < α ^ 2 := by
          nlinarith [hα.1]
        nlinarith [hrewrite, hαsq]
      nlinarith [hgap']
    -- Finally unsquare the estimate to recover the Lipschitz bound.
    have hsq' :
        ‖((1 - 1 / α) • (x : H) + (1 / α) • T x) -
            ((1 - 1 / α) • (y : H) + (1 / α) • T y)‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 := by
      rw [averaging_transform_sub]
      simpa using hsq
    exact (norm_sq_le_norm_sq_iff).1 hsq'

/-- Helper for Proposition 4.35: the affine transform is nonexpansive exactly when the inner
product inequality from clause (4) holds. -/
-- Proof sketch: reuse the squared nonexpansive estimate and rewrite the same quadratic gap with
-- the rearranged identity from Lemma 2.17.
private theorem averaging_transform_lipschitz_iff_inner_ineq
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {T : D → H} :
    LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • T x) ↔
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 + (1 - 2 * α) * ‖(x : H) - y‖ ^ 2 ≤
          2 * (1 - α) * inner ℝ ((x : H) - y) (T x - T y) := by
  rw [lipschitzWith_one_iff_pairwise_norm_sub_le]
  constructor
  · intro hS x y
    -- Square the pairwise nonexpansive estimate for the affine transform.
    have hSxy := hS x y
    rw [averaging_transform_sub] at hSxy
    have hsq :
        ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
      exact (norm_sq_le_norm_sq_iff).2 hSxy
    have hnonneg :
        0 ≤ α ^ 2 *
          (‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2) := by
      -- Multiplying by `α^2 > 0` preserves the squared comparison.
      nlinarith [hsq, hα.1]
    have hrewrite :
        0 ≤
          2 * (1 - α) * inner ℝ ((x : H) - y) (T x - T y) -
            (‖T x - T y‖ ^ 2 + (1 - 2 * α) * ‖(x : H) - y‖ ^ 2) := by
      -- Lemma 2.17 rewrites the scaled gap into the inner-product expression.
      rw [← alpha_sq_norm_sq_sub_inv_affine_combination_eq_rearranged
        ((x : H) - y) (T x - T y) hα]
      exact hnonneg
    -- Rearranging gives clause (4).
    nlinarith [hrewrite]
  · intro hS x y
    have hrewrite :
        0 ≤
          2 * (1 - α) * inner ℝ ((x : H) - y) (T x - T y) -
            (‖T x - T y‖ ^ 2 + (1 - 2 * α) * ‖(x : H) - y‖ ^ 2) := by
      -- Move clause (4) into the nonnegative form matching Lemma 2.17.
      nlinarith [hS x y]
    have hnonneg :
        0 ≤ α ^ 2 *
          (‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2) := by
      -- Rewrite the quadratic quantity back into the scaled norm gap.
      rw [alpha_sq_norm_sq_sub_inv_affine_combination_eq_rearranged
        ((x : H) - y) (T x - T y) hα]
      exact hrewrite
    have hsq :
        ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
      -- The positivity of `α^2` lets us remove the scalar factor.
      have hgap :
          0 ≤ ‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 := by
        have hαsq : 0 < α ^ 2 := by
          nlinarith [hα.1]
        nlinarith [hnonneg, hαsq]
      nlinarith [hgap]
    -- Unsquare the estimate to recover nonexpansiveness.
    have hsq' :
        ‖((1 - 1 / α) • (x : H) + (1 / α) • T x) -
            ((1 - 1 / α) • (y : H) + (1 / α) • T y)‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 := by
      rw [averaging_transform_sub]
      simpa using hsq
    exact (norm_sq_le_norm_sq_iff).1 hsq'

/-- Proposition 4.35, clause `(1) ↔ (2)`: for `α ∈ (0, 1)`, a map is `α`-averaged exactly when
the standard affine transform `x ↦ (1 - 1 / α) x + (1 / α) T x` is nonexpansive. -/
private theorem averagedWith_iff_lipschitz_transform
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) {T : D → H} :
    AveragedWith α T ↔
      LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • T x) := by
  let S : D → H := fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • T x
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  constructor
  · intro hT
    rcases averagedWith_iff.mp hT with ⟨_, R, hR, hTR⟩
    have hSR : S = R := by
      ext x
      dsimp [S]
      rw [hTR]
      calc
        (1 - 1 / α) • (x : H) + (1 / α) • ((1 - α) • (x : H) + α • R x)
            = (1 - 1 / α) • (x : H) +
                (((1 / α) * (1 - α)) • (x : H) + ((1 / α) * α) • R x) := by
            rw [smul_add, smul_smul, smul_smul]
        _ = ((1 - 1 / α) + (1 / α) * (1 - α)) • (x : H) + ((1 / α) * α) • R x := by
            rw [← add_assoc, ← add_smul]
        _ = R x := by
            have hleft : (1 - 1 / α) + (1 / α) * (1 - α) = 0 := by
              field_simp [hα0]
              ring
            have hright : (1 / α) * α = 1 := by
              field_simp [hα0]
            rw [hleft, hright]
            simp
    change LipschitzWith 1 S
    rw [hSR]
    exact hR
  · intro hS
    have hTS : T = fun x : D ↦ (1 - α) • (x : H) + α • S x := by
      ext x
      symm
      calc
        (1 - α) • (x : H) + α • S x
            = (1 - α) • (x : H) + α • ((1 - 1 / α) • (x : H) + (1 / α) • T x) := by
                simp [S]
        _ = (1 - α) • (x : H) + ((α * (1 - 1 / α)) • (x : H) + (α * (1 / α)) • T x) := by
            rw [smul_add, smul_smul, smul_smul]
        _ = ((1 - α) + α * (1 - 1 / α)) • (x : H) + (α * (1 / α)) • T x := by
            rw [← add_assoc, ← add_smul]
        _ = T x := by
            have hleft : (1 - α) + α * (1 - 1 / α) = 0 := by
              field_simp [hα0]
              ring
            have hright : α * (1 / α) = 1 := by
              field_simp [hα0]
            rw [hleft, hright]
            simp
    exact averagedWith_iff.mpr ⟨hα, S, hS, hTS⟩

/-- Proposition 4.35, clause `(1) ↔ (3)`: for `α ∈ (0, 1)`, averagedness is equivalent to the
quadratic residual inequality. -/
theorem averagedWith_iff_residual_sqnorm_ineq
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) {T : D → H} :
    AveragedWith α T ↔
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 -
            ((1 - α) / α) * ‖((x : H) - T x) - (y - T y)‖ ^ 2 := by
  rw [averagedWith_iff_lipschitz_transform hα, averaging_transform_lipschitz_iff_residual_ineq hα]

/-- Proposition 4.35, clause `(1) ↔ (4)`: for `α ∈ (0, 1)`, averagedness is equivalent to the
displayed inner-product inequality. -/
private theorem averagedWith_iff_inner_ineq
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) {T : D → H} :
    AveragedWith α T ↔
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 + (1 - 2 * α) * ‖(x : H) - y‖ ^ 2 ≤
          2 * (1 - α) * inner ℝ ((x : H) - y) (T x - T y) := by
  rw [averagedWith_iff_lipschitz_transform hα, averaging_transform_lipschitz_iff_inner_ineq hα]

/-- Proposition 4.35: for `α ∈ (0,1)`, the four standard characterizations of an
`α`-averaged operator on a subset of a real Hilbert space are equivalent. -/
-- Proof sketch: prove `(1) ↔ (2)` by solving the affine identity for the companion map,
-- prove `(2) ↔ (3)` by expanding the norm of
-- `((1 - 1 / α) • (x - y) + (1 / α) • (T x - T y))`, and obtain `(3) ↔ (4)` by expanding
-- `‖((x - T x) - (y - T y))‖ ^ 2`.
theorem averagedWith_tfae (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (T : D → H) :
    [ AveragedWith α T,
      LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • T x),
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 -
            ((1 - α) / α) * ‖((x : H) - T x) - (y - T y)‖ ^ 2,
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 + (1 - 2 * α) * ‖(x : H) - y‖ ^ 2 ≤
          2 * (1 - α) * inner ℝ ((x : H) - y) (T x - T y) ].TFAE := by
  tfae_have 1 ↔ 2 := by
    exact averagedWith_iff_lipschitz_transform hα
  tfae_have 2 ↔ 3 := by
    exact averaging_transform_lipschitz_iff_residual_ineq hα
  tfae_have 2 ↔ 4 := by
    exact averaging_transform_lipschitz_iff_inner_ineq hα
  tfae_finish

end
