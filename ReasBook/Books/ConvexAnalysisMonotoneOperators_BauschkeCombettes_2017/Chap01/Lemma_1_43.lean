/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Filter

variable {X : Type u} [MetricSpace X]

/-- Helper for Lemma 1.43: antitonicity pushes the boundedness of the initial set to every later
set in the chain. -/
lemma bounded_of_antitone_base
    (C : ℕ → Set X) (hanti : Antitone C) (hbdd : Bornology.IsBounded (C 0)) :
    ∀ n, Bornology.IsBounded (C n) := by
  -- Every `C n` sits inside `C 0`, so the bounded initial set controls all later sets.
  intro n
  exact Bornology.IsBounded.subset hbdd (hanti (Nat.zero_le n))

/-- Helper for Lemma 1.43: every finite intersection in an antitone nonempty family is nonempty. -/
lemma finite_intersection_nonempty_of_antitone
    (C : ℕ → Set X) (hnonempty : ∀ n, (C n).Nonempty) (hanti : Antitone C) :
    ∀ N, (⋂ n ≤ N, C n).Nonempty := by
  -- A point of `C N` belongs to each earlier `C n` because the family is decreasing.
  intro N
  rcases hnonempty N with ⟨x, hx⟩
  refine ⟨x, mem_iInter.2 (fun n ↦ mem_iInter.2 (fun hn ↦ ?_))⟩
  exact hanti hn hx

/-- Helper for Lemma 1.43: two points lying in all sets of the chain must coincide once the
diameters converge to `0`. -/
lemma eq_of_mem_iInter_of_diam_tendsto_zero
    (C : ℕ → Set X) (hbounded : ∀ n, Bornology.IsBounded (C n))
    (hdiam : Tendsto (Metric.diam ∘ C) atTop (nhds 0))
    {x y : X} (hx : x ∈ ⋂ n, C n) (hy : y ∈ ⋂ n, C n) :
    x = y := by
  -- If `x ≠ y`, the positive distance `dist x y` eventually dominates the diameters.
  by_contra hxy
  have hxy_pos : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hdiam (dist x y) hxy_pos
  have hxN : x ∈ C N := mem_iInter.mp hx N
  have hyN : y ∈ C N := mem_iInter.mp hy N
  have hdist_le : dist x y ≤ Metric.diam (C N) :=
    Metric.dist_le_diam_of_mem (hbounded N) hxN hyN
  have hdiam_lt : Metric.diam (C N) < dist x y := by
    -- The convergence hypothesis turns the metric-neighborhood statement into a real inequality.
    have hsmall := hN N le_rfl
    simpa [Function.comp, Real.dist_eq,
      abs_of_nonneg (Metric.diam_nonneg : 0 ≤ Metric.diam (C N))] using hsmall
  exact not_lt_of_ge hdist_le hdiam_lt

variable [CompleteSpace X]

/-- Lemma 1.43 (Cantor): in a complete metric space, a bounded antitone sequence of nonempty
closed sets whose diameters converge to `0` has intersection equal to a singleton. -/
-- Proof sketch: choose points `x n ∈ C n`; the nesting and diameter hypothesis make `(x n)` Cauchy,
-- so completeness gives a limit `x`; closedness puts `x` in every `C n`; uniqueness follows because
-- any two points in every `C n` have distance bounded by `Metric.diam (C n)`, which tends to `0`;
-- the boundedness hypothesis ensures that `Metric.diam` has its intended metric meaning.
theorem exists_eq_singleton_iInter_of_nonempty_isClosed_antitone_diam_tendsto_zero
    (C : ℕ → Set X) (hnonempty : ∀ n, (C n).Nonempty) (hclosed : ∀ n, IsClosed (C n))
    (hanti : Antitone C) (hbdd : Bornology.IsBounded (C 0))
    (hdiam : Tendsto (Metric.diam ∘ C) atTop (nhds 0)) :
    ∃ x : X, (⋂ n, C n) = {x} := by
  -- Route correction: use mathlib's packaged Cantor-intersection existence theorem, then prove
  -- uniqueness separately from the vanishing-diameter estimate.
  let hbounded : ∀ n, Bornology.IsBounded (C n) :=
    bounded_of_antitone_base C hanti hbdd
  let hfinite : ∀ N, (⋂ n ≤ N, C n).Nonempty :=
    finite_intersection_nonempty_of_antitone C hnonempty hanti
  have hnonempty_iInter : (⋂ n, C n).Nonempty :=
    Metric.nonempty_iInter_of_nonempty_biInter hclosed hbounded hfinite <|
      by simpa [Function.comp] using hdiam
  rcases hnonempty_iInter with ⟨x, hx⟩
  refine ⟨x, Set.eq_singleton_iff_unique_mem.2 ⟨hx, ?_⟩⟩
  -- Any other point in the total intersection equals `x` by the diameter-collapse argument.
  intro y hy
  exact (eq_of_mem_iInter_of_diam_tendsto_zero C hbounded hdiam (x := x) (y := y) hx hy).symm

/-- Lemma 1.43 (Cantor), in the textbook successor-step formulation with bounded initial set. -/
theorem exists_eq_singleton_iInter_of_nonempty_isClosed_succ_subset_diam_tendsto_zero
    (C : ℕ → Set X) (hnonempty : ∀ n, (C n).Nonempty) (hclosed : ∀ n, IsClosed (C n))
    (hnest : ∀ n, C (n + 1) ⊆ C n) (hbdd : Bornology.IsBounded (C 0))
    (hdiam : Tendsto (fun n ↦ Metric.diam (C n)) atTop (nhds 0)) :
    ∃ x : X, (⋂ n, C n) = {x} := by
  simpa [Function.comp] using
    exists_eq_singleton_iInter_of_nonempty_isClosed_antitone_diam_tendsto_zero
      C hnonempty hclosed (antitone_nat_of_succ_le hnest) hbdd hdiam
