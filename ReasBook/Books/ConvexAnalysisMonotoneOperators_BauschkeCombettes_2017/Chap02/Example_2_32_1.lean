/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Remark_2_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open Filter

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Example 2.32.1: every fixed coordinate of an orthonormal sequence tends to `0`. -/
private lemma orthonormal_inner_right_tendsto_zero (x : ℕ → H) (hx : Orthonormal ℝ x) (u : H) :
    Tendsto (fun n ↦ ⟪x n, u⟫_ℝ) atTop (nhds 0) := by
  -- Bessel's inequality makes the squared coordinates summable, so they vanish at infinity.
  have hs : Summable (fun n ↦ ‖⟪x n, u⟫_ℝ‖ ^ 2) :=
    hx.inner_products_summable u
  have hs0 : Tendsto (fun n ↦ ‖⟪x n, u⟫_ℝ‖ ^ 2) atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  -- Taking square roots recovers the norms of the coordinates.
  have hsqrt : Tendsto (fun n ↦ Real.sqrt (‖⟪x n, u⟫_ℝ‖ ^ 2)) atTop
      (nhds (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hs0
  have hnorm : Tendsto (fun n ↦ ‖⟪x n, u⟫_ℝ‖) atTop (nhds 0) := by
    convert hsqrt using 1
    · ext n
      rw [Real.sqrt_sq]
      positivity
    · simp
  -- Norm convergence to `0` is equivalent to convergence to `0` in `ℝ`.
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm

/-- Example 2.32.1: an orthonormal sequence in a real Hilbert space converges weakly to `0`. -/
-- Proof sketch: for each `u : H`, Bessel's inequality implies that
-- `n ↦ ‖inner ℝ (x n) u‖ ^ 2` is summable, so `inner ℝ (x n) u → 0`. By the Hilbert-space
-- description of the weak topology from Remark 2.31, this is exactly convergence to `0` in
-- `WeakSpace ℝ H`.
theorem orthonormal_sequence_tendsto_zero_weakly (x : ℕ → H) (hx : Orthonormal ℝ x) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)) := by
  simpa using
    (weakConvergence_iff_forall_tendsto_inner_right x (0 : H)).2
      fun u ↦ by simpa using orthonormal_inner_right_tendsto_zero x hx u

omit [CompleteSpace H] in
/-- An orthonormal sequence does not converge strongly to `0`. -/
-- Proof sketch: if `x` converged to `0` in norm, then `‖x n‖ → 0`; this contradicts the fact
-- that every term has norm `1`.
theorem orthonormal_sequence_not_tendsto_zero_strongly (x : ℕ → H) (hx : Orthonormal ℝ x) :
    ¬ Tendsto x atTop (nhds (0 : H)) := by
  intro hx0
  -- Strong convergence to `0` forces the norms to converge to `0`.
  have hnorm : Tendsto (fun n ↦ ‖x n‖) atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).mp hx0
  -- Rewriting the norms with orthonormality turns this into the impossible limit `1 → 0`.
  have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 0) := by
    convert hnorm using 1
    ext n
    simp [hx.norm_eq_one]
  have hconst' : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hone : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hconst hconst'
  norm_num at hone

omit [CompleteSpace H] in
/-- Helper for Example 2.32.1: distinct terms of an orthonormal sequence have squared distance `2`.
-/
private lemma orthonormal_norm_sub_sq_eq_two (x : ℕ → H) (hx : Orthonormal ℝ x) {m n : ℕ}
    (hmn : m ≠ n) :
    ‖x m - x n‖ ^ 2 = 2 := by
  -- Expand the squared norm and simplify the two norm terms and the cross term separately.
  rw [norm_sub_sq_real]
  have hm : ‖x m‖ = 1 := hx.norm_eq_one m
  have hn : ‖x n‖ = 1 := hx.norm_eq_one n
  have hinner : inner ℝ (x m) (x n) = 0 := hx.inner_eq_zero hmn
  nlinarith [hm, hn, hinner]

omit [CompleteSpace H] in
/-- An orthonormal sequence has no Cauchy subsequence. -/
-- Proof sketch: for distinct `m` and `n`, orthonormality gives
-- `‖x m - x n‖ ^ 2 = ‖x m‖ ^ 2 + ‖x n‖ ^ 2 = 2`, so distinct subsequence terms stay a fixed
-- positive distance apart and cannot satisfy the Cauchy criterion.
theorem orthonormal_sequence_not_exists_cauchy_subsequence (x : ℕ → H) (hx : Orthonormal ℝ x) :
    ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (x ∘ φ) := by
  rintro ⟨φ, hφ, hcauchy⟩
  -- A Cauchy subsequence would eventually have all later terms within distance `1` of one anchor.
  rcases (Metric.cauchySeq_iff'.1 hcauchy) 1 zero_lt_one with ⟨N, hN⟩
  have hdist : dist ((x ∘ φ) (N + 1)) ((x ∘ φ) N) < 1 :=
    hN (N + 1) (Nat.le_succ N)
  -- Consecutive subsequence terms are still distinct, so orthonormality keeps them separated.
  have hsq : ‖x (φ (N + 1)) - x (φ N)‖ ^ 2 = 2 := by
    apply orthonormal_norm_sub_sq_eq_two x hx
    exact (hφ (Nat.lt_succ_self N)).ne'
  rw [dist_eq_norm] at hdist
  have hsq_lt : ‖x (φ (N + 1)) - x (φ N)‖ ^ 2 < 1 := by
    simpa using
      (pow_lt_pow_left₀ hdist (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0))
  linarith
