/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {I : Type v} [Fintype I]

/-- Helper for Proposition 4.47: a quasinonexpansive map yields the residual inner-product
inequality from the textbook proof against any of its fixed points. -/
private lemma quasinonexpansive_residual_inner_nonpos {S : D → H} (hS : IsQuasinonexpansiveOn S)
    (x y : D) (hy : S y = (y : H)) :
    2 * inner ℝ (S x - (x : H)) ((x : H) - (y : H)) ≤ - ‖S x - (x : H)‖ ^ 2 := by
  -- First square the quasinonexpansive estimate relative to the fixed point `y`.
  have hsq : ‖S x - (y : H)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hS x y hy)
  -- Then expand the residual square and isolate the inner-product term.
  have hexpand :
      ‖S x - (x : H)‖ ^ 2 =
        ‖S x - (y : H)‖ ^ 2 - 2 * inner ℝ (S x - (y : H)) ((x : H) - (y : H)) +
          ‖(x : H) - y‖ ^ 2 := by
    have h := norm_sub_sq_real (S x - (y : H)) ((x : H) - (y : H))
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hinner :
      inner ℝ (S x - (y : H)) ((x : H) - (y : H)) =
        inner ℝ (S x - (x : H)) ((x : H) - (y : H)) + ‖(x : H) - y‖ ^ 2 := by
    calc
      inner ℝ (S x - (y : H)) ((x : H) - (y : H)) =
          inner ℝ ((S x - (x : H)) + ((x : H) - (y : H))) ((x : H) - (y : H)) := by
            congr 1
            abel
      _ = inner ℝ (S x - (x : H)) ((x : H) - (y : H)) +
            inner ℝ ((x : H) - (y : H)) ((x : H) - (y : H)) := by
            rw [inner_add_left]
      _ = inner ℝ (S x - (x : H)) ((x : H) - (y : H)) + ‖(x : H) - y‖ ^ 2 := by
            rw [real_inner_self_eq_norm_sq]
  nlinarith [hsq, hexpand, hinner]

/-- Helper for Proposition 4.47: if `x` is fixed by the weighted average, then the weighted sum of
the residual vectors `T i x - x` is zero. -/
private lemma weighted_residual_eq_zero_of_mem_fixedPointsWithin (ω : I → ℝ) (T : I → D → H)
    (hω_sum : ∑ i, ω i = 1) {x : D}
    (hx : x ∈ fixedPointsWithin (fun z : D ↦ ∑ i, ω i • T i z)) :
    ∑ i, ω i • (T i x - (x : H)) = 0 := by
  classical
  -- Rewrite the fixed-point equation of the average into the corresponding residual identity.
  have hfix : (∑ i, ω i • T i x) = (x : H) := (mem_fixedPointsWithin_iff _).mp hx
  calc
    ∑ i, ω i • (T i x - (x : H)) = (∑ i, ω i • T i x) - (∑ i, ω i) • (x : H) := by
      calc
        ∑ i, ω i • (T i x - (x : H)) = ∑ i, (ω i • T i x - ω i • (x : H)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [smul_sub]
        _ = (∑ i, ω i • T i x) - ∑ i, ω i • (x : H) := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ i, ω i • T i x) - (∑ i, ω i) • (x : H) := by
          rw [Finset.sum_smul]
    _ = (x : H) - (1 : ℝ) • (x : H) := by
      rw [hfix, hω_sum]
    _ = 0 := by
      simp

-- Proof sketch: the inclusion from right to left is immediate since every common fixed point is
-- fixed by the weighted average when the weights sum to `1`. For the reverse inclusion, choose a
-- common fixed point `y`, apply quasinonexpansiveness of each `T i` relative to `y`, expand the
-- polarization identity for `T i x - x` against `x - y`, sum with the positive weights `ω i`, and
-- use `∑ i, ω i = 1` to force each residual `T i x - x` to vanish.
/-- Proposition 4.47: the fixed points in `D` of the finite weighted average
`x ↦ ∑ i, ω i • T i x` of quasinonexpansive maps are exactly the common fixed points of the
family, provided the weights are positive, sum to `1`, and the family has a common fixed point. -/
theorem fixedPointsWithin_weightedAverage_eq_iInter
    (ω : I → ℝ) (T : I → D → H) (hT : ∀ i, IsQuasinonexpansiveOn (T i))
    (hFix : (⋂ i, fixedPointsWithin (T i)).Nonempty) (hω_pos : ∀ i, 0 < ω i)
    (hω_sum : ∑ i, ω i = 1) :
    fixedPointsWithin (fun x : D ↦ ∑ i, ω i • T i x) = ⋂ i, fixedPointsWithin (T i) := by
  classical
  ext x
  constructor
  · intro hx
    rcases hFix with ⟨y, hy⟩
    have hyi : ∀ i, T i y = (y : H) := by
      intro i
      exact (mem_fixedPointsWithin_iff _).mp ((Set.mem_iInter.mp hy) i)
    -- A fixed point of the average makes the weighted residual sum vanish.
    have hres0 : ∑ i, ω i • (T i x - (x : H)) = 0 :=
      weighted_residual_eq_zero_of_mem_fixedPointsWithin ω T hω_sum hx
    have hsum_inner_eq_zero :
        ∑ i, ω i * inner ℝ (T i x - (x : H)) ((x : H) - (y : H)) = 0 := by
      have hinner0 :
          inner ℝ (∑ i, ω i • (T i x - (x : H))) ((x : H) - (y : H)) = 0 := by
        rw [hres0, inner_zero_left]
      rw [sum_inner] at hinner0
      simpa [real_inner_smul_left] using hinner0
    -- Sum the pointwise residual inequalities against the positive weights.
    have hsum_sq_nonpos : ∑ i, ω i * ‖T i x - (x : H)‖ ^ 2 ≤ 0 := by
      have hpointwise :
          ∀ i, 2 * (ω i * inner ℝ (T i x - (x : H)) ((x : H) - (y : H))) ≤
            -(ω i * ‖T i x - (x : H)‖ ^ 2) := by
        intro i
        have hi := quasinonexpansive_residual_inner_nonpos (hT i) x y (hyi i)
        have hωi_nonneg : 0 ≤ ω i := (hω_pos i).le
        nlinarith
      have hsum_le :
          ∑ i, 2 * (ω i * inner ℝ (T i x - (x : H)) ((x : H) - (y : H))) ≤
            ∑ i, -(ω i * ‖T i x - (x : H)‖ ^ 2) := by
        exact Finset.sum_le_sum fun i hi ↦ hpointwise i
      have hleft_zero :
          ∑ i, 2 * (ω i * inner ℝ (T i x - (x : H)) ((x : H) - (y : H))) = 0 := by
        rw [← Finset.mul_sum, hsum_inner_eq_zero]
        ring
      have hright :
          ∑ i, -(ω i * ‖T i x - (x : H)‖ ^ 2) = - ∑ i, ω i * ‖T i x - (x : H)‖ ^ 2 := by
        rw [Finset.sum_neg_distrib]
      rw [hright] at hsum_le
      nlinarith [hsum_le, hleft_zero]
    -- Nonnegativity forces each weighted square to vanish, hence every residual is zero.
    have hsum_sq_nonneg : 0 ≤ ∑ i, ω i * ‖T i x - (x : H)‖ ^ 2 := by
      exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (hω_pos i).le (sq_nonneg _)
    have hsum_sq_eq_zero : ∑ i, ω i * ‖T i x - (x : H)‖ ^ 2 = 0 := by
      linarith
    rw [Set.mem_iInter]
    intro i
    rw [mem_fixedPointsWithin_iff]
    have hterm_zero : ω i * ‖T i x - (x : H)‖ ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj ↦ mul_nonneg (hω_pos j).le (sq_nonneg _))).1 hsum_sq_eq_zero i
        (Finset.mem_univ i)
    have hnorm_sq_zero : ‖T i x - (x : H)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm_zero with hωi_zero | hsq_zero
      · exact (ne_of_gt (hω_pos i) hωi_zero).elim
      · exact hsq_zero
    have hnorm_zero : ‖T i x - (x : H)‖ = 0 := by
      have hnorm_nonneg : 0 ≤ ‖T i x - (x : H)‖ := norm_nonneg _
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
  · intro hx
    -- Every common fixed point is fixed by the weighted average because the weights sum to `1`.
    rw [Set.mem_iInter] at hx
    rw [mem_fixedPointsWithin_iff]
    calc
      ∑ i, ω i • T i x = ∑ i, ω i • (x : H) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact congrArg (fun z : H ↦ ω i • z) ((mem_fixedPointsWithin_iff _).mp (hx i))
      _ = (∑ i, ω i) • (x : H) := by
        rw [Finset.sum_smul]
      _ = (x : H) := by
        simp [hω_sum]

end
