/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Function

variable {X : Type u} [MetricSpace X] [Nonempty X] [CompleteSpace X]
variable {β : NNReal} {T : X → X}

private theorem fixedPoints_eq_singleton_fixedPoint (hT : ContractingWith β T) :
    fixedPoints T = {hT.fixedPoint T} := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_singleton_iff]
    exact hT.fixedPoint_unique hy
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hT.fixedPoint_isFixedPt

private theorem dist_iterate_succ_fixedPoint_le (hT : ContractingWith β T) (x₀ : X) :
    ∀ n : ℕ,
      dist (T^[n + 1] x₀) (hT.fixedPoint T) ≤ β * dist (T^[n] x₀) (hT.fixedPoint T) := by
  intro n
  simpa [iterate_succ_apply', hT.fixedPoint_isFixedPt.eq] using
    hT.dist_le_mul (T^[n] x₀) (hT.fixedPoint T)

private theorem dist_iterate_fixedPoint_le_geometric (hT : ContractingWith β T) (x₀ : X) :
    ∀ n : ℕ,
      dist (T^[n] x₀) (hT.fixedPoint T) ≤ β ^ n * dist x₀ (hT.fixedPoint T) := by
  intro n
  simpa [(hT.fixedPoint_isFixedPt.iterate n).eq] using
    (hT.toLipschitzWith.iterate n).dist_le_mul x₀ (hT.fixedPoint T)

private theorem initial_error_bounds (hT : ContractingWith β T) (x₀ : X) :
    dist x₀ (T x₀) / (1 + β) ≤ dist x₀ (hT.fixedPoint T) ∧
      dist x₀ (hT.fixedPoint T) ≤ dist x₀ (T x₀) / (1 - β) := by
  constructor
  · have hstep :
        dist (hT.fixedPoint T) (T x₀) ≤ β * dist x₀ (hT.fixedPoint T) := by
      simpa [iterate_zero, iterate_succ_apply', dist_comm] using
        dist_iterate_succ_fixedPoint_le hT x₀ 0
    have hsum :
        dist x₀ (T x₀) ≤ (1 + β) * dist x₀ (hT.fixedPoint T) := by
      calc
        dist x₀ (T x₀) ≤ dist x₀ (hT.fixedPoint T) + dist (hT.fixedPoint T) (T x₀) :=
          dist_triangle _ _ _
        _ ≤ dist x₀ (hT.fixedPoint T) + β * dist x₀ (hT.fixedPoint T) := by
          gcongr
        _ = (1 + β) * dist x₀ (hT.fixedPoint T) := by
          ring
    have hpos : (0 : ℝ) < 1 + β := by
      positivity
    exact (div_le_iff₀ hpos).2 (by simpa [mul_comm] using hsum)
  · simpa using hT.apriori_dist_iterate_fixedPoint_le x₀ 0

/-- Theorem 1.50 (Banach-Picard): a contraction on a nonempty complete metric space has a unique
fixed point, expressed canonically as `fixedPoints T = {x}`, and this point satisfies the
textbook one-step, geometric, a priori, a posteriori, and initial two-sided bounds for every
starting point `x₀`. -/
-- Proof sketch: take the canonical fixed point supplied by `ContractingWith.fixedPoint`; the
-- singleton fixed-point set follows from `fixedPoint_unique`. The one-step and geometric bounds
-- come from the contraction inequality and the Lipschitz control of iterates, the a priori and
-- a posteriori estimates are the corresponding mathlib theorems, and the initial two-sided bound
-- combines the one-step estimate at `n = 0` with the a priori estimate at `n = 0`.
theorem exists_fixedPoint_with_banach_picard_estimates (hT : ContractingWith β T) :
    ∃ x : X,
      fixedPoints T = {x} ∧
      (∀ x₀ : X, ∀ n : ℕ, dist (T^[n + 1] x₀) x ≤ β * dist (T^[n] x₀) x) ∧
      (∀ x₀ : X, ∀ n : ℕ, dist (T^[n] x₀) x ≤ β ^ n * dist x₀ x) ∧
      (∀ x₀ : X, ∀ n : ℕ,
        dist (T^[n] x₀) x ≤ dist x₀ (T x₀) * (β : ℝ) ^ n / (1 - β)) ∧
      (∀ x₀ : X, ∀ n : ℕ,
        dist (T^[n] x₀) x ≤ dist (T^[n] x₀) (T^[n + 1] x₀) / (1 - β)) ∧
      ∀ x₀ : X,
        dist x₀ (T x₀) / (1 + β) ≤ dist x₀ x ∧
          dist x₀ x ≤ dist x₀ (T x₀) / (1 - β) := by
  refine ⟨hT.fixedPoint T, fixedPoints_eq_singleton_fixedPoint hT, ?_, ?_, ?_, ?_, ?_⟩
  · intro x₀ n
    exact dist_iterate_succ_fixedPoint_le hT x₀ n
  · intro x₀ n
    exact dist_iterate_fixedPoint_le_geometric hT x₀ n
  · intro x₀ n
    simpa using hT.apriori_dist_iterate_fixedPoint_le x₀ n
  · intro x₀ n
    simpa using hT.aposteriori_dist_iterate_fixedPoint_le x₀ n
  · intro x₀
    exact initial_error_bounds hT x₀
