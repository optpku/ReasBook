/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

section

variable {X : Type u} [PseudoMetricSpace X]
variable {C : Set X} {u : ℕ → X}

namespace FejerMonotone

/-- Helper for Proposition 5.4: the distance from a Fejér-monotone sequence to a fixed point of
`C` is antitone. -/
lemma dist_antitone_of_mem (h : FejerMonotone C u) {x : X} (hx : x ∈ C) :
    Antitone (fun n ↦ dist (u n) x) := by
  -- The one-step Fejér inequality upgrades to all later indices on `ℕ`.
  exact antitone_nat_of_succ_le (fun n ↦ h.step x hx n)

/-- Helper for Proposition 5.4: every term of a Fejér-monotone sequence stays in the closed ball
centered at a chosen point of `C` with radius its initial distance to that point. -/
lemma range_subset_closedBall_of_mem (h : FejerMonotone C u) {x : X} (hx : x ∈ C) :
    Set.range u ⊆ Metric.closedBall x (dist (u 0) x) := by
  intro y hy
  rcases hy with ⟨n, rfl⟩
  -- Antitonicity bounds the `n`th iterate by the initial distance to `x`.
  exact Metric.mem_closedBall.2 ((h.dist_antitone_of_mem hx) (Nat.zero_le n))

/-- Helper for Proposition 5.4: the distance to `C` decreases at each successor step when `C` is
nonempty. -/
lemma infDist_succ_le (h : FejerMonotone C u) (hC : C.Nonempty) (n : ℕ) :
    Metric.infDist (u (n + 1)) C ≤ Metric.infDist (u n) C := by
  -- Compare `Metric.infDist (u (n + 1)) C` to the distance from `u n` to an arbitrary point of `C`.
  refine (Metric.le_infDist hC).2 (fun x hx ↦ ?_)
  exact (Metric.infDist_le_dist_of_mem hx).trans (h.step x hx n)

/-- Helper for Proposition 5.4: each forward difference is at most twice every distance from
`u n` to a point of `C`, hence its half is below `Metric.infDist (u n) C`. -/
lemma half_dist_le_infDist (h : FejerMonotone C u) (hC : C.Nonempty) (m n : ℕ) :
    dist (u (n + m)) (u n) / 2 ≤ Metric.infDist (u n) C := by
  -- It suffices to prove the bound against every point of `C` and then take the infimum.
  refine (Metric.le_infDist hC).2 (fun x hx ↦ ?_)
  have htail : dist (u (n + m)) x ≤ dist (u n) x :=
    (h.dist_antitone_of_mem hx) (Nat.le_add_right n m)
  have hdist :
      dist (u (n + m)) (u n) ≤ 2 * dist (u n) x := by
    -- The triangle inequality and Fejér monotonicity reduce the forward difference to one radius.
    calc
      dist (u (n + m)) (u n) ≤ dist (u (n + m)) x + dist (u n) x :=
        dist_triangle_right _ _ _
      _ ≤ dist (u n) x + dist (u n) x :=
        add_le_add htail le_rfl
      _ = 2 * dist (u n) x := by ring
  linarith

-- Proof sketch: choose a point of `C`, use Fejér monotonicity to bound every term by the initial
-- distance to that point, and then bound the whole range by a fixed ball.
/-- Proposition 5.4 (1): (i) a Fejér-monotone sequence with respect to a nonempty set is bounded. -/
theorem isBounded (h : FejerMonotone C u) (hC : C.Nonempty) :
    Bornology.IsBounded (Set.range u) := by
  rcases hC with ⟨x, hx⟩
  -- Bounding the range by one closed ball gives boundedness immediately.
  exact Metric.isBounded_closedBall.subset (h.range_subset_closedBall_of_mem hx)

-- Proof sketch: for a fixed `x ∈ C`, the sequence `n ↦ dist (u n) x` is decreasing by Fejér
-- monotonicity and bounded below by `0`, hence it converges in `ℝ`.
/-- Proposition 5.4 (2): (ii) for every `x ∈ C`, the distance sequence `n ↦ dist (u n) x`
converges. -/
theorem dist_tendsto (h : FejerMonotone C u) {x : X} (hx : x ∈ C) :
    ∃ l : ℝ, Tendsto (fun n ↦ dist (u n) x) atTop (𝓝 l) := by
  refine ⟨sInf ((fun n ↦ dist (u n) x) '' Set.Ici 0), ?_⟩
  -- The distance sequence is antitone and bounded below by `0`,
  -- so real monotone convergence applies.
  refine Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici (k := 0) ?_ ?_
  · intro m hm n hn hmn
    exact (h.dist_antitone_of_mem hx) hmn
  · refine ⟨0, ?_⟩
    rintro _ ⟨n, hn, rfl⟩
    exact dist_nonneg

-- Proof sketch: Fejér monotonicity gives `Metric.infDist (u (n + 1)) C ≤ dist (u (n + 1)) x` for
-- every `x ∈ C`, and taking the infimum over `x` yields monotonicity of
-- `n ↦ Metric.infDist (u n) C`.
/-- Proposition 5.4 (3): (iii) the sequence `n ↦ Metric.infDist (u n) C` is decreasing. -/
theorem infDist_antitone (h : FejerMonotone C u) :
    Antitone (fun n ↦ Metric.infDist (u n) C) := by
  by_cases hC : C.Nonempty
  · -- The successor-step estimate determines antitonicity on `ℕ`.
    exact antitone_nat_of_succ_le (fun n ↦ h.infDist_succ_le hC n)
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
    -- For the empty set, `Metric.infDist` is constantly zero.
    simpa [hCempty, Metric.infDist_empty] using
      (antitone_const : Antitone fun _ : ℕ ↦ (0 : ℝ))

-- Proof sketch: the sequence `n ↦ Metric.infDist (u n) C` is decreasing by the previous clause
-- and bounded below by `0`, so monotone convergence in `ℝ` gives a limit.
/-- Proposition 5.4 (4): (iv) the sequence `n ↦ Metric.infDist (u n) C` converges. -/
theorem infDist_tendsto (h : FejerMonotone C u) :
    ∃ l : ℝ, Tendsto (fun n ↦ Metric.infDist (u n) C) atTop (𝓝 l) := by
  refine ⟨sInf ((fun n ↦ Metric.infDist (u n) C) '' Set.Ici 0), ?_⟩
  -- Apply monotone convergence to the antitone infimum-distance sequence.
  refine Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici (k := 0) ?_ ?_
  · intro m hm n hn hmn
    exact h.infDist_antitone hmn
  · refine ⟨0, ?_⟩
    rintro _ ⟨n, hn, rfl⟩
    exact Metric.infDist_nonneg

-- Proof sketch: apply the triangle inequality with an arbitrary `x ∈ C`, bound both terms by
-- `dist (u n) x` using repeated Fejér monotonicity, and then take the infimum over `x ∈ C`.
/-- Proposition 5.4 (5): (v) every forward difference is bounded by twice the distance from
`u n` to `C`. -/
theorem dist_le_two_mul_infDist (h : FejerMonotone C u) (hC : C.Nonempty) (m n : ℕ) :
    dist (u (n + m)) (u n) ≤ 2 * Metric.infDist (u n) C := by
  -- First bound the half-distance by the infimum distance, then clear the factor `1 / 2`.
  have hhalf := h.half_dist_le_infDist hC m n
  linarith

end FejerMonotone

end
