/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_5
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Proposition_5_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function Set
open scoped BigOperators Topology

universe u

section

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- The relaxed fixed-point iteration attached to a family of operators `Tₙ`, relaxation
parameters `λₙ`, and an initial point `x₀`. -/
def relaxedOperatorIteration (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H) : ℕ → H
  | 0 => x0
  | n + 1 =>
      let xn := relaxedOperatorIteration T lam x0 n
      xn + lam n • (T n xn - xn)

-- Proof sketch: unfold the recursive definition at index `0`.
/-- The relaxed iteration starts from the prescribed initial point `x₀`. -/
@[simp] theorem relaxedOperatorIteration_zero (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H) :
    relaxedOperatorIteration T lam x0 0 = x0 := by
  -- Unfold the recursion at the initial index.
  rfl

-- Proof sketch: unfold the recursive definition at the successor index `n + 1`.
/-- The relaxed iteration satisfies the defining recursion
`xₙ₊₁ = xₙ + λₙ • (Tₙ xₙ - xₙ)`. -/
@[simp] theorem relaxedOperatorIteration_succ (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H) (n : ℕ) :
    relaxedOperatorIteration T lam x0 (n + 1) =
      let xn := relaxedOperatorIteration T lam x0 n
      xn + lam n • (T n xn - xn) := by
  -- Unfold the recursion at the successor index.
  rfl

/-- Helper for Proposition 5.13: each relaxed successor step rewrites as the affine combination
`(1 - λₙ) xₙ + λₙ Tₙ xₙ`. -/
theorem relaxedOperatorIteration_succ_eq_affineCombination
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H) (n : ℕ) :
    relaxedOperatorIteration T lam x0 (n + 1) =
      (1 - lam n) • relaxedOperatorIteration T lam x0 n +
        lam n • T n (relaxedOperatorIteration T lam x0 n) := by
  -- Rewrite the recursion and collect the two `xₙ` contributions into `(1 - λₙ) • xₙ`.
  rw [relaxedOperatorIteration_succ]
  let xn := relaxedOperatorIteration T lam x0 n
  change xn + lam n • (T n xn - xn) = (1 - lam n) • xn + lam n • T n xn
  simp [sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 5.13: the increment of the relaxed iteration is the scaled residual
`λₙ (Tₙ xₙ - xₙ)`. -/
theorem relaxedOperatorIteration_sub_eq_smul_residual
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H) (n : ℕ) :
    relaxedOperatorIteration T lam x0 (n + 1) - relaxedOperatorIteration T lam x0 n =
      lam n •
        (T n (relaxedOperatorIteration T lam x0 n) - relaxedOperatorIteration T lam x0 n) := by
  -- Subtract the previous iterate from the recursive step.
  rw [relaxedOperatorIteration_succ]
  let xn := relaxedOperatorIteration T lam x0 n
  change xn + lam n • (T n xn - xn) - xn = lam n • (T n xn - xn)
  abel_nf

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 5.13: rewrite the relaxed affine displacement from a fixed point as the
original displacement plus a scaled residual. -/
theorem relaxed_sub_fixedPoint_eq_add_smul_residual {D : Set H} (T : D → H) (lam : ℝ)
    (x y : D) :
    ((1 - lam) • (x : H) + lam • T x) - (y : H) =
      ((x : H) - y) + lam • (T x - (x : H)) := by
  -- This is the textbook affine-displacement identity behind Proposition 4.3.
  simp [sub_eq_add_neg, add_smul, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 5.13: firm quasinonexpansiveness forces the cross term in the relaxed
norm expansion to be at most the negative residual norm square. -/
theorem inner_le_neg_residual_norm_sq_of_firmly_quasinonexpansive {D : Set H} {T : D → H}
    (hT : IsFirmlyQuasinonexpansiveOn T) (x y : D) (hy : T y = (y : H)) :
    inner ℝ ((x : H) - y) (T x - (x : H)) ≤ -‖T x - (x : H)‖ ^ 2 := by
  have hineq := hT x y hy
  have hexpand :
      ‖T x - (y : H)‖ ^ 2 =
        ‖(x : H) - y‖ ^ 2 +
          2 * inner ℝ ((x : H) - y) (T x - (x : H)) +
          ‖T x - (x : H)‖ ^ 2 := by
    -- Rewrite `T x - y` as `(x - y) + (T x - x)` and expand the squared norm.
    rw [show T x - (y : H) = ((x : H) - y) + (T x - (x : H)) by
      abel_nf]
    simpa using norm_add_sq_real ((x : H) - y) (T x - (x : H))
  have hres : ‖(x : H) - T x‖ ^ 2 = ‖T x - (x : H)‖ ^ 2 := by
    rw [norm_sub_rev]
  -- Cancelling the common `‖x - y‖²` term isolates the desired cross-term bound.
  nlinarith [hineq, hexpand, hres]

/-- Helper for Proposition 5.13: exact quadratic expansion of the relaxed displacement squared
norm. -/
theorem sq_norm_relaxed_sub_fixedPoint_eq {D : Set H} {T : D → H} (lam : ℝ) (x y : D) :
    ‖((1 - lam) • (x : H) + lam • T x) - (y : H)‖ ^ 2 =
      ‖(x : H) - y‖ ^ 2 +
        2 * lam * inner ℝ ((x : H) - y) (T x - (x : H)) +
        lam ^ 2 * ‖T x - (x : H)‖ ^ 2 := by
  rw [relaxed_sub_fixedPoint_eq_add_smul_residual]
  -- Expand `‖u + lam • v‖²` and normalize the scalar factors.
  rw [norm_add_sq_real]
  rw [real_inner_smul_right]
  rw [show ‖lam • (T x - (x : H))‖ ^ 2 = lam ^ 2 * ‖T x - (x : H)‖ ^ 2 by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]]
  ring

/-- Helper for Proposition 5.13: the one-step relaxed-map estimate from Proposition 4.3, proved
locally so the target file does not depend on an unbuilt chapter module. -/
theorem sq_norm_relaxedMap_sub_fixedPoint_le {D : Set H} {T : D → H}
    (hT : IsFirmlyQuasinonexpansiveOn T) {lam : ℝ} (hlam : 0 ≤ lam) (x y : D)
    (hy : T y = (y : H)) :
    ‖((1 - lam) • (x : H) + lam • T x) - (y : H)‖ ^ 2 ≤
      ‖(x : H) - y‖ ^ 2 - lam * (2 - lam) * ‖T x - (x : H)‖ ^ 2 := by
  rw [sq_norm_relaxed_sub_fixedPoint_eq]
  have hinner :=
    inner_le_neg_residual_norm_sq_of_firmly_quasinonexpansive hT x y hy
  have hcross :
      2 * lam * inner ℝ ((x : H) - y) (T x - (x : H)) ≤
        -(2 * lam) * ‖T x - (x : H)‖ ^ 2 := by
    nlinarith
  nlinarith [hcross]

/-- Helper for Proposition 5.13: a firmly quasinonexpansive self-map on the whole space is
quasinonexpansive on `Set.univ`. -/
theorem quasinonexpansiveOn_univ_of_firmlyQuasinonexpansive
    (S : H → H) (hS : FirmlyQuasinonexpansive S) :
    QuasinonexpansiveOn (Set.univ : Set H) S := by
  rw [quasinonexpansiveOn_iff]
  intro x _ y hy
  rcases mem_fixedPointSetOn_iff.mp hy with ⟨-, hyfix⟩
  rw [firmlyQuasinonexpansive_iff] at hS
  have hsq : ‖S x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    have hineq := hS x y hyfix
    nlinarith [sq_nonneg ‖S x - x‖]
  -- Compare norms by comparing their squares, which are nonnegative.
  have hnorm := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg (S x - y)), abs_of_nonneg (norm_nonneg (x - y))] using hnorm

/-- Helper for Proposition 5.13: the common fixed-point set of a firmly quasinonexpansive family is
closed. -/
theorem isClosed_commonFixedPointSet_of_firmlyQuasinonexpansive_family
    (T : ℕ → H → H) (hT : ∀ n, FirmlyQuasinonexpansive (T n)) :
    IsClosed (⋂ n, fixedPoints (T n)) := by
  have hclosed_fixed : ∀ n, IsClosed (fixedPoints (T n)) := by
    intro n
    have hqne : QuasinonexpansiveOn (Set.univ : Set H) (T n) :=
      quasinonexpansiveOn_univ_of_firmlyQuasinonexpansive (T n) (hT n)
    rw [← closure_subset_iff_isClosed]
    intro y hyclosure
    rw [Function.mem_fixedPoints_iff]
    by_contra hy_not_fixed
    have hy_dist_pos : 0 < dist (T n y) y := dist_pos.mpr hy_not_fixed
    obtain ⟨z, hzmem, hzclose⟩ :=
      (Metric.mem_closure_iff.mp hyclosure) (dist (T n y) y / 2) (by positivity)
    have hstep : dist (T n y) z ≤ dist y z := by
      rw [quasinonexpansiveOn_iff] at hqne
      have hzfixOn : z ∈ fixedPointSetOn (Set.univ : Set H) (T n) := by
        exact mem_fixedPointSetOn_iff.mpr ⟨Set.mem_univ z, Function.mem_fixedPoints_iff.mp hzmem⟩
      simpa [dist_eq_norm, dist_comm y z] using hqne y (by simp) z hzfixOn
    have hdist : dist (T n y) y ≤ 2 * dist y z := by
      calc
        dist (T n y) y ≤ dist (T n y) z + dist z y := by
          simpa [dist_comm z y] using dist_triangle_right (T n y) y z
        _ ≤ dist y z + dist z y := add_le_add hstep le_rfl
        _ = 2 * dist y z := by
              rw [dist_comm z y]
              ring
    have hcontra : dist (T n y) y < dist (T n y) y := by
      calc
        dist (T n y) y ≤ 2 * dist y z := hdist
        _ < dist (T n y) y := by nlinarith [hzclose]
    have hfalse : False := (lt_irrefl (dist (T n y) y)) hcontra
    exact hfalse.elim
  -- Closed intersections preserve the common fixed-point set.
  exact isClosed_iInter hclosed_fixed

/-- Helper for Proposition 5.13: applying the square function to the infimum distance rewrites as
the infimum of the squared distances. -/
theorem sq_infDist_eq_iInf_sq_dist (x : H) (C : Set H) (hC : C.Nonempty) :
    Metric.infDist x C ^ 2 = ⨅ z : C, dist x z ^ 2 := by
  let f : ℝ → ℝ := fun r ↦ max r 0 ^ 2
  letI : Nonempty C := hC.to_subtype
  rw [Metric.infDist_eq_iInf]
  have hinf_nonneg : 0 ≤ ⨅ z : C, dist x z := by
    refine le_ciInf fun z ↦ ?_
    exact dist_nonneg
  have hf_cont : ContinuousAt f (⨅ z : C, dist x z) := by
    dsimp [f]
    exact ((continuousAt_id.max continuousAt_const).pow 2)
  have hf_mono : Monotone f := by
    intro a b hab
    dsimp [f]
    have hmax : max a 0 ≤ max b 0 := max_le_max hab le_rfl
    nlinarith [hmax, le_max_right a 0, le_max_right b 0]
  have hmap :
      f (⨅ z : C, dist x z) = ⨅ z : C, f (dist x z) := by
    refine Monotone.map_ciInf_of_continuousAt hf_cont hf_mono ?_
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact dist_nonneg
  -- The cutoff is inactive because every distance term is already nonnegative.
  simpa [f, hinf_nonneg, dist_nonneg] using hmap

/-- Helper for Proposition 5.13: telescoping the one-step descent inequality yields the textbook
finite-sum estimate (5.11). -/
theorem sq_norm_sub_commonFixedPoint_le_sq_norm_sub_initial_sub_sum
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (hlam : ∀ n, 0 ≤ lam n) (z : H) (hz : z ∈ ⋂ n, fixedPoints (T n)) :
    ∀ n : ℕ,
      ‖relaxedOperatorIteration T lam x0 (n + 1) - z‖ ^ 2 ≤
        ‖x0 - z‖ ^ 2 -
          ∑ k ∈ Finset.range (n + 1),
            lam k * (2 - lam k) *
              ‖T k (relaxedOperatorIteration T lam x0 k) -
                relaxedOperatorIteration T lam x0 k‖ ^ 2 := by
  have hone :
      ∀ m : ℕ,
        ‖relaxedOperatorIteration T lam x0 (m + 1) - z‖ ^ 2 ≤
          ‖relaxedOperatorIteration T lam x0 m - z‖ ^ 2 -
            lam m * (2 - lam m) *
              ‖T m (relaxedOperatorIteration T lam x0 m) -
                relaxedOperatorIteration T lam x0 m‖ ^ 2 := by
    intro m
    let xm := relaxedOperatorIteration T lam x0 m
    have hzfix : T m z = z := by
      exact Function.mem_fixedPoints_iff.mp (Set.mem_iInter.mp hz m)
    have hineq :=
      sq_norm_relaxedMap_sub_fixedPoint_le
        (D := Set.univ) (T := fun x : Set.univ ↦ T m x)
        (hT := by
          change FirmlyQuasinonexpansiveOn (Set.univ : Set H) (T m)
          simpa using hT m)
        (lam := lam m) (hlam m) ⟨xm, Set.mem_univ xm⟩ ⟨z, Set.mem_univ z⟩ hzfix
    -- Rewrite the affine combination back to the recursive iterate.
    rw [relaxedOperatorIteration_succ_eq_affineCombination]
    simpa [xm] using hineq
  intro n
  induction n with
  | zero =>
      -- Start the telescope with the one-step estimate at index `0`.
      simpa [Finset.sum_range_one] using hone 0
  | succ n ih =>
      have hstep := hone (n + 1)
      -- Append the new residual term to the finite sum and combine the previous bound.
      rw [Finset.sum_range_succ] at ⊢
      calc
        ‖relaxedOperatorIteration T lam x0 (n + 1 + 1) - z‖ ^ 2
            ≤ ‖relaxedOperatorIteration T lam x0 (n + 1) - z‖ ^ 2 -
                lam (n + 1) * (2 - lam (n + 1)) *
                  ‖T (n + 1) (relaxedOperatorIteration T lam x0 (n + 1)) -
                    relaxedOperatorIteration T lam x0 (n + 1)‖ ^ 2 := hstep
        _ ≤
            (‖x0 - z‖ ^ 2 -
                ∑ x ∈ Finset.range (n + 1),
                  lam x * (2 - lam x) *
                    ‖T x (relaxedOperatorIteration T lam x0 x) -
                      relaxedOperatorIteration T lam x0 x‖ ^ 2) -
              lam (n + 1) * (2 - lam (n + 1)) *
                ‖T (n + 1) (relaxedOperatorIteration T lam x0 (n + 1)) -
                  relaxedOperatorIteration T lam x0 (n + 1)‖ ^ 2 := by
              exact sub_le_sub_right ih _
        _ = ‖x0 - z‖ ^ 2 -
              (∑ x ∈ Finset.range (n + 1),
                lam x * (2 - lam x) *
                  ‖T x (relaxedOperatorIteration T lam x0 x) -
                    relaxedOperatorIteration T lam x0 x‖ ^ 2 +
                lam (n + 1) * (2 - lam (n + 1)) *
                  ‖T (n + 1) (relaxedOperatorIteration T lam x0 (n + 1)) -
                    relaxedOperatorIteration T lam x0 (n + 1)‖ ^ 2) := by
              ring

/-- Helper for Proposition 5.13: the weighted squared increment equals the weighted squared
residual term. -/
theorem weighted_increment_sq_eq_weighted_residual_sq
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hlam : ∀ n, lam n ∈ Ioc (0 : ℝ) 2) (n : ℕ) :
    (2 / lam n - 1) *
        ‖relaxedOperatorIteration T lam x0 (n + 1) - relaxedOperatorIteration T lam x0 n‖ ^ 2 =
      lam n * (2 - lam n) *
        ‖T n (relaxedOperatorIteration T lam x0 n) - relaxedOperatorIteration T lam x0 n‖ ^ 2 := by
  have hlam0 : lam n ≠ 0 := (hlam n).1.ne'
  -- Rewrite the increment as the scaled residual and simplify the scalar coefficient.
  calc
    (2 / lam n - 1) *
        ‖relaxedOperatorIteration T lam x0 (n + 1) - relaxedOperatorIteration T lam x0 n‖ ^ 2
        =
        (2 / lam n - 1) *
          ((lam n) ^ 2 *
            ‖T n (relaxedOperatorIteration T lam x0 n) - relaxedOperatorIteration T lam x0 n‖ ^ 2) := by
          rw [relaxedOperatorIteration_sub_eq_smul_residual, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    _ =
        lam n * (2 - lam n) *
          ‖T n (relaxedOperatorIteration T lam x0 n) - relaxedOperatorIteration T lam x0 n‖ ^ 2 := by
          field_simp [hlam0]

-- Proof sketch: apply Proposition 4.3 to the `n`th firmly quasinonexpansive self-map at the
-- iterate `xₙ` and the common fixed point `z`, then rewrite the relaxed step with the recursive
-- formula defining `relaxedOperatorIteration`.
/-- Proposition 5.13 (1): (i) every relaxed step decreases the squared distance to each common
fixed point by the residual term `λₙ (2 - λₙ) ‖Tₙ xₙ - xₙ‖²`. -/
theorem sq_norm_sub_commonFixedPoint_le_of_relaxedOperatorIteration
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (z : H) (hz : z ∈ ⋂ n, fixedPoints (T n)) (n : ℕ) (hlam : 0 ≤ lam n) :
    ‖relaxedOperatorIteration T lam x0 (n + 1) - z‖ ^ 2 ≤
      ‖relaxedOperatorIteration T lam x0 n - z‖ ^ 2 -
        lam n * (2 - lam n) * ‖T n (relaxedOperatorIteration T lam x0 n) -
          relaxedOperatorIteration T lam x0 n‖ ^ 2 := by
  let xn := relaxedOperatorIteration T lam x0 n
  have hzfix : T n z = z := by
    exact Function.mem_fixedPoints_iff.mp (Set.mem_iInter.mp hz n)
  have hineq :=
    sq_norm_relaxedMap_sub_fixedPoint_le
      (D := Set.univ) (T := fun x : Set.univ ↦ T n x)
      (hT := by
        change FirmlyQuasinonexpansiveOn (Set.univ : Set H) (T n)
        simpa using hT n)
      (lam := lam n) hlam ⟨xn, Set.mem_univ xn⟩ ⟨z, Set.mem_univ z⟩ hzfix
  -- Rewrite the relaxed affine combination back to the recursive iterate.
  rw [relaxedOperatorIteration_succ_eq_affineCombination]
  simpa [xn] using hineq

-- Proof sketch: use clause (i) to drop the nonnegative residual term and then take square roots to
-- obtain the one-step distance inequality defining Fejér monotonicity.
/-- Proposition 5.13 (2): (ii) the relaxed iteration is Fejér monotone with respect to the common
fixed-point set. -/
theorem fejerMonotone_commonFixedPointSet_of_relaxedOperatorIteration
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (hlam : ∀ n, lam n ∈ Icc (0 : ℝ) 2) :
    FejerMonotone (⋂ n, fixedPoints (T n)) (relaxedOperatorIteration T lam x0) := by
  intro z hz n
  have hstep :=
    sq_norm_sub_commonFixedPoint_le_of_relaxedOperatorIteration
      T lam x0 hT z hz n (hlam n).1
  have hnonneg :
      0 ≤
        lam n * (2 - lam n) *
          ‖T n (relaxedOperatorIteration T lam x0 n) -
            relaxedOperatorIteration T lam x0 n‖ ^ 2 := by
    have hsq : 0 ≤
        ‖T n (relaxedOperatorIteration T lam x0 n) -
          relaxedOperatorIteration T lam x0 n‖ ^ 2 := sq_nonneg _
    exact mul_nonneg (mul_nonneg (hlam n).1 (sub_nonneg.mpr (hlam n).2)) hsq
  have hsq :
      ‖relaxedOperatorIteration T lam x0 (n + 1) - z‖ ^ 2 ≤
        ‖relaxedOperatorIteration T lam x0 n - z‖ ^ 2 := by
    linarith
  have hnorm :
      ‖relaxedOperatorIteration T lam x0 (n + 1) - z‖ ≤
        ‖relaxedOperatorIteration T lam x0 n - z‖ := by
    have hsq' := sq_le_sq.mp hsq
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using hsq'
  -- Translating the norm estimate into distances gives the Fejér step.
  simpa [dist_eq_norm] using hnorm

-- Proof sketch: telescope the inequality from clause (i) from `k = 0` to `k = n` and then take
-- the infimum over all common fixed points to rewrite the left-hand side by `Metric.infDist`.
/-- Proposition 5.13 (3): (iii) the squared distance to the common fixed-point set is bounded above
by the initial squared distance minus the finite residual sum. -/
theorem sq_infDist_le_sq_infDist_sub_sum_of_relaxedOperatorIteration
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (hC : (⋂ n, fixedPoints (T n)).Nonempty) (hlam : ∀ n, lam n ∈ Icc (0 : ℝ) 2) (n : ℕ) :
    Metric.infDist (relaxedOperatorIteration T lam x0 (n + 1)) (⋂ n, fixedPoints (T n)) ^ 2 ≤
      Metric.infDist x0 (⋂ n, fixedPoints (T n)) ^ 2 -
        (∑ k ∈ Finset.range (n + 1),
          lam k * (2 - lam k) * ‖T k (relaxedOperatorIteration T lam x0 k) -
            relaxedOperatorIteration T lam x0 k‖ ^ 2) := by
  let C : Set H := ⋂ n, fixedPoints (T n)
  let xNext := relaxedOperatorIteration T lam x0 (n + 1)
  let s : ℝ :=
    ∑ k ∈ Finset.range (n + 1),
      lam k * (2 - lam k) *
        ‖T k (relaxedOperatorIteration T lam x0 k) - relaxedOperatorIteration T lam x0 k‖ ^ 2
  letI : Nonempty C := hC.to_subtype
  have hpointwise :
      Metric.infDist xNext C ^ 2 + s ≤ ⨅ z : C, dist x0 z ^ 2 := by
    refine le_ciInf fun z ↦ ?_
    have htel :=
      sq_norm_sub_commonFixedPoint_le_sq_norm_sub_initial_sub_sum
        T lam x0 hT (fun k ↦ (hlam k).1) (z : H) z.property n
    have hleft :
        Metric.infDist xNext C ^ 2 ≤ dist xNext (z : H) ^ 2 := by
      have hdist_le : Metric.infDist xNext C ≤ dist xNext (z : H) :=
        Metric.infDist_le_dist_of_mem z.property
      have habs :
          |Metric.infDist xNext C| ≤ |dist xNext (z : H)| := by
        simpa [abs_of_nonneg Metric.infDist_nonneg,
          abs_of_nonneg (show 0 ≤ dist xNext (z : H) from dist_nonneg)] using hdist_le
      exact sq_le_sq.mpr habs
    have hright :
        dist xNext (z : H) ^ 2 ≤ dist x0 (z : H) ^ 2 - s := by
      simpa [C, xNext, s, dist_eq_norm] using htel
    -- The left distance-to-set term is controlled by the pointwise telescope against `z`.
    nlinarith
  have hinitial :
      (⨅ z : C, dist x0 z ^ 2) = Metric.infDist x0 C ^ 2 := by
    symm
    exact sq_infDist_eq_iInf_sq_dist x0 C hC
  rw [hinitial] at hpointwise
  -- Rearranging the infimum bound gives the textbook estimate for `d_C(xₙ₊₁)^2`.
  have hfinal : Metric.infDist xNext C ^ 2 ≤ Metric.infDist x0 C ^ 2 - s := by
    nlinarith [hpointwise]
  simpa [C, xNext, s] using hfinal

-- Proof sketch: clause (iii) gives a nondecreasing family of partial sums bounded above by the
-- initial squared distance, so pass to the supremum of the partial sums.
/-- Proposition 5.13 (4): (iv) the infinite residual series is bounded above by the squared
distance from the initial point to the common fixed-point set. -/
theorem tsum_residual_sq_le_sq_infDist_of_relaxedOperatorIteration
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (hC : (⋂ n, fixedPoints (T n)).Nonempty) (hlam : ∀ n, lam n ∈ Icc (0 : ℝ) 2) :
    ∑' n : ℕ,
        lam n * (2 - lam n) * ‖T n (relaxedOperatorIteration T lam x0 n) -
          relaxedOperatorIteration T lam x0 n‖ ^ 2 ≤
      Metric.infDist x0 (⋂ n, fixedPoints (T n)) ^ 2 := by
  let C : Set H := ⋂ n, fixedPoints (T n)
  let a : ℕ → ℝ := fun n ↦
    lam n * (2 - lam n) *
      ‖T n (relaxedOperatorIteration T lam x0 n) - relaxedOperatorIteration T lam x0 n‖ ^ 2
  have ha_nonneg : ∀ n, 0 ≤ a n := by
    intro n
    have hsq : 0 ≤
        ‖T n (relaxedOperatorIteration T lam x0 n) - relaxedOperatorIteration T lam x0 n‖ ^ 2 :=
      sq_nonneg _
    exact mul_nonneg (mul_nonneg (hlam n).1 (sub_nonneg.mpr (hlam n).2)) hsq
  have hpartial :
      ∀ N : ℕ, ∑ k ∈ Finset.range N, a k ≤ Metric.infDist x0 C ^ 2 := by
    intro N
    cases N with
    | zero =>
        simpa [a] using (sq_nonneg (Metric.infDist x0 C))
    | succ n =>
        have hbound :=
          sq_infDist_le_sq_infDist_sub_sum_of_relaxedOperatorIteration T lam x0 hT hC hlam n
        have hnonneg :
            0 ≤ Metric.infDist (relaxedOperatorIteration T lam x0 (n + 1)) C ^ 2 := sq_nonneg _
        -- Clause (iii) bounds each partial sum uniformly by the initial distance energy.
        simpa [C, a] using
          (show ∑ k ∈ Finset.range (n + 1), a k ≤ Metric.infDist x0 C ^ 2 by
            nlinarith [hbound, hnonneg])
  exact Real.tsum_le_of_sum_range_le ha_nonneg hpartial

-- Proof sketch: rewrite the increment by the recursion
-- `xₙ₊₁ - xₙ = λₙ • (Tₙ xₙ - xₙ)` and substitute this identity into clause (iv).
/-- Proposition 5.13 (5): (v) the weighted series of squared increments is bounded above by the
squared distance from the initial point to the common fixed-point set. -/
theorem tsum_increment_sq_le_sq_infDist_of_relaxedOperatorIteration
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (hC : (⋂ n, fixedPoints (T n)).Nonempty) (hlam : ∀ n, lam n ∈ Ioc (0 : ℝ) 2) :
    ∑' n : ℕ,
        (2 / lam n - 1) *
          ‖relaxedOperatorIteration T lam x0 (n + 1) - relaxedOperatorIteration T lam x0 n‖ ^ 2 ≤
      Metric.infDist x0 (⋂ n, fixedPoints (T n)) ^ 2 := by
  have hlam' : ∀ n, lam n ∈ Icc (0 : ℝ) 2 := by
    intro n
    exact ⟨(hlam n).1.le, (hlam n).2⟩
  have hterm :
      (fun n : ℕ ↦
        (2 / lam n - 1) *
          ‖relaxedOperatorIteration T lam x0 (n + 1) - relaxedOperatorIteration T lam x0 n‖ ^ 2) =
      (fun n : ℕ ↦
        lam n * (2 - lam n) *
          ‖T n (relaxedOperatorIteration T lam x0 n) -
            relaxedOperatorIteration T lam x0 n‖ ^ 2) := by
    funext n
    exact weighted_increment_sq_eq_weighted_residual_sq T lam x0 hlam n
  -- Rewrite each increment energy into the residual energy from part (iv).
  rw [hterm]
  exact tsum_residual_sq_le_sq_infDist_of_relaxedOperatorIteration T lam x0 hT hC hlam'

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace Proposition513Fejer

namespace FejerMonotone

/-- Helper for Proposition 5.13: the interior-direction auxiliary point lies in the chosen open
ball. This is the geometric step used in the proof of Proposition 5.10. -/
lemma auxiliary_point_mem_ball {C : Set H} {xₙ : ℕ → H}
    {c d : H} {ρ ε : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) :
    (if ‖d‖ = 0 then c else c - ρ • ‖d‖⁻¹ • d) ∈ Metric.ball c ε := by
  by_cases hdnorm : ‖d‖ = 0
  · have hε : 0 < ε := lt_trans hρ hρε
    simp [Metric.mem_ball, hdnorm, hε]
  · have hdist :
        dist (if ‖d‖ = 0 then c else c - ρ • ‖d‖⁻¹ • d) c = ρ := by
      calc
        dist (if ‖d‖ = 0 then c else c - ρ • ‖d‖⁻¹ • d) c
            = ‖ρ • ‖d‖⁻¹ • d‖ := by
                rw [dist_eq_norm]
                simp [hdnorm]
        _ = ρ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg hρ.le,
                Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg d)),
                inv_mul_cancel₀ hdnorm, mul_one]
    have hdist_lt : dist (if ‖d‖ = 0 then c else c - ρ • ‖d‖⁻¹ • d) c < ε := by
      rw [hdist]
      exact hρε
    simpa [Metric.mem_ball] using hdist_lt

/-- Helper for Proposition 5.13: Fejér monotonicity against an interior-direction auxiliary point
produces the textbook squared-distance drop used in Proposition 5.10. -/
lemma fejer_sqnorm_drop_of_interior_direction {C : Set H} {xₙ : ℕ → H}
    (hxₙ : FejerMonotone C xₙ)
    {c : H} {ρ ε : ℝ} (hball : Metric.ball c ε ⊆ C) (hρ : 0 < ρ) (hρε : ρ < ε) (n : ℕ) :
    2 * ρ * ‖xₙ (n + 1) - xₙ n‖ ≤ ‖xₙ n - c‖ ^ 2 - ‖xₙ (n + 1) - c‖ ^ 2 := by
  let d := xₙ (n + 1) - xₙ n
  let z := if ‖d‖ = 0 then c else c - ρ • ‖d‖⁻¹ • d
  have hz_ball : z ∈ Metric.ball c ε :=
    auxiliary_point_mem_ball (C := C) (xₙ := xₙ) (c := c) (d := d) hρ hρε
  have hzC : z ∈ C := hball hz_ball
  have hstep : ‖xₙ (n + 1) - z‖ ≤ ‖xₙ n - z‖ := by
    simpa [dist_eq_norm] using hxₙ.step z hzC n
  have hstep_sq : ‖xₙ (n + 1) - z‖ ^ 2 ≤ ‖xₙ n - z‖ ^ 2 := by
    nlinarith [hstep, norm_nonneg (xₙ (n + 1) - z), norm_nonneg (xₙ n - z)]
  by_cases hd : d = 0
  · have hsucc : xₙ (n + 1) = xₙ n := by
      simpa [d, sub_eq_zero] using hd
    simp [hsucc]
  · have hdnorm : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    have hz_eq : z = c - ρ • ‖d‖⁻¹ • d := by
      simp [z, d, norm_ne_zero_iff.mpr hd]
    have hsub_sq :
        ‖xₙ n - z‖ ^ 2 =
          ‖xₙ (n + 1) - z‖ ^ 2 - 2 * inner ℝ (xₙ (n + 1) - z) d + ‖d‖ ^ 2 := by
      have hnorm := norm_sub_sq_real (xₙ (n + 1) - z) d
      have hrewrite : xₙ n - z = (xₙ (n + 1) - z) - d := by
        simp [d]
      simpa [hrewrite] using hnorm
    have hinner_bound : 2 * inner ℝ (xₙ (n + 1) - z) d ≤ ‖d‖ ^ 2 := by
      nlinarith [hstep_sq, hsub_sq]
    have hz_inner :
        inner ℝ (xₙ (n + 1) - z) d =
          inner ℝ (xₙ (n + 1) - c) d + ρ * ‖d‖ := by
      calc
        inner ℝ (xₙ (n + 1) - z) d
            = inner ℝ (xₙ (n + 1) - c + (ρ • ‖d‖⁻¹ • d)) d := by
                rw [hz_eq]
                congr
                abel
        _ = inner ℝ (xₙ (n + 1) - c) d + inner ℝ (ρ • ‖d‖⁻¹ • d) d := by
              rw [inner_add_left]
        _ = inner ℝ (xₙ (n + 1) - c) d + (ρ * ‖d‖⁻¹) * inner ℝ d d := by
              rw [real_inner_smul_left, real_inner_smul_left]
              ring
        _ = inner ℝ (xₙ (n + 1) - c) d + (ρ * ‖d‖⁻¹) * ‖d‖ ^ 2 := by
              rw [real_inner_self_eq_norm_sq]
        _ = inner ℝ (xₙ (n + 1) - c) d + ρ * ‖d‖ := by
              field_simp [hdnorm]
    have hdrop_eq :
        ‖xₙ n - c‖ ^ 2 - ‖xₙ (n + 1) - c‖ ^ 2 =
          -2 * inner ℝ (xₙ (n + 1) - c) d + ‖d‖ ^ 2 := by
      have hnorm := norm_sub_sq_real (xₙ (n + 1) - c) d
      have hrewrite : xₙ n - c = (xₙ (n + 1) - c) - d := by
        simp [d]
      nlinarith [show ‖xₙ n - c‖ ^ 2 =
          ‖xₙ (n + 1) - c‖ ^ 2 - 2 * inner ℝ (xₙ (n + 1) - c) d + ‖d‖ ^ 2 by
          simpa [hrewrite] using hnorm]
    -- Route correction: use the inner-product estimate first, then convert it into the desired
    -- squared-distance drop.
    nlinarith [hinner_bound, hz_inner, hdrop_eq]

/-- Helper for Proposition 5.13: the interior-point drop estimate telescopes to a uniform bound on
the partial sums of the increment norms. -/
lemma partial_sum_norm_sub_le_of_fejer_sqnorm_drop {C : Set H} {xₙ : ℕ → H}
    (hxₙ : FejerMonotone C xₙ)
    {c : H} {ρ ε : ℝ} (hball : Metric.ball c ε ⊆ C) (hρ : 0 < ρ) (hρε : ρ < ε) (N : ℕ) :
    Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - xₙ i‖) ≤ ‖xₙ 0 - c‖ ^ 2 / (2 * ρ) := by
  have hsum_drop :
      2 * ρ * Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - xₙ i‖) ≤
        Finset.sum (Finset.range N) (fun i ↦ ‖xₙ i - c‖ ^ 2 - ‖xₙ (i + 1) - c‖ ^ 2) := by
    calc
      2 * ρ * Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - xₙ i‖)
          = Finset.sum (Finset.range N) (fun i ↦ 2 * ρ * ‖xₙ (i + 1) - xₙ i‖) := by
              rw [Finset.mul_sum]
      _ ≤ Finset.sum (Finset.range N) (fun i ↦ ‖xₙ i - c‖ ^ 2 - ‖xₙ (i + 1) - c‖ ^ 2) := by
            refine Finset.sum_le_sum fun i hi ↦ ?_
            exact fejer_sqnorm_drop_of_interior_direction hxₙ hball hρ hρε i
  have htel :
      Finset.sum (Finset.range N) (fun i ↦ ‖xₙ i - c‖ ^ 2 - ‖xₙ (i + 1) - c‖ ^ 2) =
        ‖xₙ 0 - c‖ ^ 2 - ‖xₙ N - c‖ ^ 2 := by
    let a : ℕ → ℝ := fun i ↦ ‖xₙ i - c‖ ^ 2
    have htel_raw := Finset.sum_range_sub a N
    rw [Finset.sum_sub_distrib] at htel_raw
    have htel_swap :
        Finset.sum (Finset.range N) (fun i ↦ a i) -
            Finset.sum (Finset.range N) (fun i ↦ a (i + 1)) =
          a 0 - a N := by
      calc
        Finset.sum (Finset.range N) (fun i ↦ a i) -
            Finset.sum (Finset.range N) (fun i ↦ a (i + 1))
            = -(Finset.sum (Finset.range N) (fun i ↦ a (i + 1)) -
                Finset.sum (Finset.range N) (fun i ↦ a i)) := by
                  ring
        _ = -(a N - a 0) := by rw [htel_raw]
        _ = a 0 - a N := by ring
    calc
      Finset.sum (Finset.range N) (fun i ↦ ‖xₙ i - c‖ ^ 2 - ‖xₙ (i + 1) - c‖ ^ 2)
          = Finset.sum (Finset.range N) (fun i ↦ ‖xₙ i - c‖ ^ 2) -
              Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - c‖ ^ 2) := by
                rw [Finset.sum_sub_distrib]
      _ = a 0 - a N := htel_swap
      _ = ‖xₙ 0 - c‖ ^ 2 - ‖xₙ N - c‖ ^ 2 := by rfl
  have hbound :
      2 * ρ * Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - xₙ i‖) ≤ ‖xₙ 0 - c‖ ^ 2 := by
    rw [htel] at hsum_drop
    nlinarith [hsum_drop, sq_nonneg (‖xₙ N - c‖)]
  have h2ρ : 0 < 2 * ρ := by positivity
  exact (le_div_iff₀ h2ρ).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbound)

/-- Helper for Proposition 5.13: the Fejér-monotone strong-convergence theorem from Proposition
5.10, reproved locally because the workspace lacks a built import for that module. -/
theorem exists_tendsto_and_summable_norm_sub_of_interior_nonempty
    {C : Set H} {xₙ : ℕ → H} (hxₙ : FejerMonotone C xₙ) (hC_int : (interior C).Nonempty) :
    ∃ x : H, Tendsto xₙ atTop (𝓝 x) ∧ Summable (fun n ↦ ‖xₙ (n + 1) - xₙ n‖) := by
  rcases hC_int with ⟨c, hc_int⟩
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hc_int) with ⟨ε, hε, hball⟩
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρε : ρ < ε := by
    dsimp [ρ]
    linarith
  have hpartial :
      ∀ N : ℕ, Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - xₙ i‖) ≤
        ‖xₙ 0 - c‖ ^ 2 / (2 * ρ) := by
    intro N
    exact partial_sum_norm_sub_le_of_fejer_sqnorm_drop hxₙ hball hρ hρε N
  have hsummable : Summable (fun n ↦ ‖xₙ (n + 1) - xₙ n‖) :=
    summable_of_sum_range_le (fun n ↦ norm_nonneg _) hpartial
  have hsummable_dist : Summable (fun n ↦ dist (xₙ n) (xₙ (n + 1))) := by
    simpa [dist_eq_norm, norm_sub_rev] using hsummable
  have hcauchy : CauchySeq xₙ := cauchySeq_of_summable_dist hsummable_dist
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨x, hx⟩
  exact ⟨x, hx, hsummable⟩

end FejerMonotone

end Proposition513Fejer

-- Proof sketch: clause (ii) supplies Fejér monotonicity of the relaxed iteration, and then
-- Theorem 5.5 applies once all weak sequential cluster points are known to lie in the common
-- fixed-point set.
/-- Proposition 5.13 (6): (vi) if every weak sequential cluster point of the relaxed iteration
belongs to the common fixed-point set, then the relaxed iteration converges weakly to a point of
that set. -/
theorem exists_tendsto_weakly_to_commonFixedPoint_of_relaxedOperatorIteration
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (hC : (⋂ n, fixedPoints (T n)).Nonempty) (hlam : ∀ n, lam n ∈ Icc (0 : ℝ) 2)
    (hcluster :
      ∀ z : H,
        IsSequentialClusterPt
            (fun n ↦ toWeakSpace ℝ H (relaxedOperatorIteration T lam x0 n))
            (toWeakSpace ℝ H z) →
          z ∈ ⋂ n, fixedPoints (T n)) :
    ∃ z ∈ ⋂ n, fixedPoints (T n),
      Tendsto (fun n ↦ toWeakSpace ℝ H (relaxedOperatorIteration T lam x0 n)) atTop
        (𝓝 (toWeakSpace ℝ H z)) := by
  have hfejer :=
    fejerMonotone_commonFixedPointSet_of_relaxedOperatorIteration T lam x0 hT hlam
  -- Apply the chapter weak-convergence theorem to the Fejér-monotone relaxed orbit.
  exact tendsto_weakly_of_fejerMonotone_of_weakSequentialClusterPts_mem
    hC (relaxedOperatorIteration T lam x0) hfejer hcluster

-- Proof sketch: clause (ii) gives Fejér monotonicity of the relaxed iteration, so Proposition 5.10
-- yields strong convergence once the common fixed-point set has nonempty interior.
/-- Proposition 5.13 (7): (vii) if the common fixed-point set has nonempty interior, then the
relaxed iteration converges strongly. -/
theorem exists_tendsto_of_relaxedOperatorIteration_of_interior_nonempty
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (hlam : ∀ n, lam n ∈ Icc (0 : ℝ) 2)
    (hCint : (interior (⋂ n, fixedPoints (T n))).Nonempty) :
    ∃ z : H, Tendsto (relaxedOperatorIteration T lam x0) atTop (𝓝 z) := by
  have hfejer :=
    fejerMonotone_commonFixedPointSet_of_relaxedOperatorIteration T lam x0 hT hlam
  rcases
      FejerMonotone.exists_tendsto_and_summable_norm_sub_of_interior_nonempty
        (C := ⋂ n, fixedPoints (T n)) (xₙ := relaxedOperatorIteration T lam x0) hfejer hCint
    with ⟨z, hz, -⟩
  -- Proposition 5.10 gives strong convergence directly from the interior hypothesis.
  exact ⟨z, hz⟩

-- Proof sketch: use clause (vii) to get a strong limit `z`; a strong sequential cluster point of
-- the full sequence must equal `z`, so if one such cluster point belongs to the common fixed-point
-- set then the strong limit also belongs to that set.
/-- Proposition 5.13 (8): (vii) if the common fixed-point set has nonempty interior and some
strong sequential cluster point of the relaxed iteration belongs to that set, then the strong
limit belongs to the common fixed-point set. -/
theorem exists_tendsto_to_commonFixedPoint_of_interior_nonempty_of_strongSequentialClusterPt
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (hlam : ∀ n, lam n ∈ Icc (0 : ℝ) 2)
    (hCint : (interior (⋂ n, fixedPoints (T n))).Nonempty)
    (hcluster :
      ∃ z : H,
        IsSequentialClusterPt (relaxedOperatorIteration T lam x0) z ∧
          z ∈ ⋂ n, fixedPoints (T n)) :
    ∃ z ∈ ⋂ n, fixedPoints (T n),
      Tendsto (relaxedOperatorIteration T lam x0) atTop (𝓝 z) := by
  rcases exists_tendsto_of_relaxedOperatorIteration_of_interior_nonempty T lam x0 hT hlam hCint
    with ⟨w, hw⟩
  rcases hcluster with ⟨z, hzcluster, hzC⟩
  rcases hzcluster.exists_subseq_tendsto with ⟨φ, hφmono, hφtendsto⟩
  have hw_subseq :
      Tendsto ((relaxedOperatorIteration T lam x0) ∘ φ) atTop (𝓝 w) :=
    hw.comp hφmono.tendsto_atTop
  -- A subsequence of a convergent sequence has the same limit, so the cluster point is `w`.
  have hzw : z = w := tendsto_nhds_unique hφtendsto hw_subseq
  exact ⟨w, by simpa [hzw] using hzC, hw⟩

-- Proof sketch: combine clause (vii) with clause (vi): nonempty interior gives strong convergence,
-- and the weak sequential cluster-point hypothesis identifies the strong limit as a common fixed
-- point.
/-- Proposition 5.13 (9): (vii) if the common fixed-point set has nonempty interior and every weak
sequential cluster point of the relaxed iteration belongs to that set, then the relaxed iteration
converges strongly to a point of the common fixed-point set. -/
theorem exists_tendsto_to_commonFixedPoint_of_interior_nonempty_of_weakSequentialClusterPts_mem
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (hlam : ∀ n, lam n ∈ Icc (0 : ℝ) 2)
    (hCint : (interior (⋂ n, fixedPoints (T n))).Nonempty)
    (hcluster :
      ∀ z : H,
        IsSequentialClusterPt
            (fun n ↦ toWeakSpace ℝ H (relaxedOperatorIteration T lam x0 n))
            (toWeakSpace ℝ H z) →
          z ∈ ⋂ n, fixedPoints (T n)) :
    ∃ z ∈ ⋂ n, fixedPoints (T n),
      Tendsto (relaxedOperatorIteration T lam x0) atTop (𝓝 z) := by
  rcases exists_tendsto_of_relaxedOperatorIteration_of_interior_nonempty T lam x0 hT hlam hCint
    with ⟨z, hz⟩
  rcases
      exists_tendsto_weakly_to_commonFixedPoint_of_relaxedOperatorIteration
        T lam x0 hT
        (by
          rcases hCint with ⟨c, hc⟩
          exact ⟨c, interior_subset hc⟩)
        hlam hcluster
    with ⟨w, hwC, hw⟩
  have hzWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (relaxedOperatorIteration T lam x0 n)) atTop
        (𝓝 (toWeakSpace ℝ H z)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto z).comp hz
  -- The strong limit and the weak limit coincide after transport to `WeakSpace`.
  have hzw_weak : toWeakSpace ℝ H z = toWeakSpace ℝ H w :=
    tendsto_nhds_unique hzWeak hw
  have hzw : z = w := (toWeakSpace ℝ H).injective hzw_weak
  exact ⟨z, by simpa [hzw] using hwC, hz⟩

-- Proof sketch: clause (ii) gives Fejér monotonicity, and the assumption that the liminf of the
-- distances to the common fixed-point set is `0` identifies the only possible strong limit point;
-- then apply the chapter’s strong convergence criterion for Fejér-monotone sequences.
/-- Proposition 5.13 (10): (viii) if the liminf of the distances from the relaxed iteration to the
common fixed-point set is `0`, then the relaxed iteration converges strongly to a point of that
set. -/
theorem exists_tendsto_to_commonFixedPoint_of_relaxedOperatorIteration_of_liminf_infDist_eq_zero
    (T : ℕ → H → H) (lam : ℕ → ℝ) (x0 : H)
    (hT : ∀ n, FirmlyQuasinonexpansive (T n))
    (hC : (⋂ n, fixedPoints (T n)).Nonempty) (hlam : ∀ n, lam n ∈ Icc (0 : ℝ) 2)
    (hliminf :
      Filter.liminf
          (fun n ↦ Metric.infDist (relaxedOperatorIteration T lam x0 n) (⋂ n, fixedPoints (T n)))
          atTop = 0) :
    ∃ z ∈ ⋂ n, fixedPoints (T n),
      Tendsto (relaxedOperatorIteration T lam x0) atTop (𝓝 z) := by
  let C : Set H := ⋂ n, fixedPoints (T n)
  let x : ℕ → H := relaxedOperatorIteration T lam x0
  have hfejer : FejerMonotone C x :=
    fejerMonotone_commonFixedPointSet_of_relaxedOperatorIteration T lam x0 hT hlam
  rcases hfejer.infDist_tendsto with ⟨l, hl⟩
  have hliminf_real :
      Filter.liminf (fun n ↦ Metric.infDist (x n) C) atTop = l := by
    simpa [x, C] using hl.liminf_eq
  have hl_zero : l = 0 := by
    simpa [hliminf_real, x, C] using hliminf
  have hzero : Tendsto (fun n ↦ Metric.infDist (x n) C) atTop (𝓝 0) := by
    simpa [hl_zero] using hl
  have hcauchy : CauchySeq x :=
    FejerMonotone.cauchySeq_of_infDist_tendsto_zero hfejer hC hzero
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨z, hz⟩
  have hC_closed : IsClosed C :=
    isClosed_commonFixedPointSet_of_firmlyQuasinonexpansive_family T hT
  have hzC : z ∈ C :=
    FejerMonotone.limit_mem_of_closed_of_infDist_tendsto_zero hz hzero hC_closed hC
  exact ⟨z, hzC, hz⟩

end
