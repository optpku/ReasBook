/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open Function Set

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] {D : Set H}

/-- Proposition 4.9 (1): a finite convex weighted average of nonexpansive operators on `D` is
nonexpansive. -/
-- Proof sketch: write the difference of the weighted averages as the weighted sum of the
-- differences, apply the triangle inequality, bound each term by nonexpansiveness of `T i`, and
-- use that the nonnegative weights sum to `1`.
theorem lipschitzWith_weightedOperator {n : ℕ} (ω : Fin (n + 1) → ℝ)
    (T : Fin (n + 1) → D → H) (hT : ∀ i, LipschitzWith 1 (T i))
    (hω : ∀ i, ω i ∈ Set.Icc (0 : ℝ) 1) (hω_sum : ∑ i, ω i = 1) :
    LipschitzWith 1 (weightedOperatorAverage ω T) := by
  -- Control the weighted average by rewriting its distance as a norm of a finite sum.
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  calc
    dist (weightedOperatorAverage ω T x) (weightedOperatorAverage ω T y)
        = ‖(∑ i, ω i • T i x) - ∑ i, ω i • T i y‖ := by
          rw [weightedOperatorAverage_apply, weightedOperatorAverage_apply, dist_eq_norm]
    _ = ‖∑ i, ω i • (T i x - T i y)‖ := by
          simp [smul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖ω i • (T i x - T i y)‖ := norm_sum_le _ _
    _ = ∑ i, ω i * ‖T i x - T i y‖ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hω i).1]
    -- Apply the nonexpansive estimate termwise and keep the nonnegative weights outside.
    _ ≤ ∑ i, ω i * dist x y := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hTi : ‖T i x - T i y‖ ≤ dist x y := by
            simpa [dist_eq_norm] using (hT i).dist_le_mul x y
          exact mul_le_mul_of_nonneg_left hTi (hω i).1
    -- Collapse the remaining scalar sum using that the weights add up to one.
    _ = (∑ i, ω i) * dist x y := by
          rw [Finset.sum_mul]
    _ = 1 * dist x y := by
          rw [hω_sum]

end

section

variable {H : Type u}

/-- The ordered composition of a finite family `T 0, ..., T (m - 1)` of operators. -/
def finiteComposition : {m : ℕ} → (Fin m → H → H) → H → H
  | 0, _ => id
  | _ + 1, T => T 0 ∘ finiteComposition (fun i ↦ T i.succ)

/-- The ordered composition over `Fin (n + 1)` splits into the head map composed with the
ordered composition of the tail family. -/
theorem finiteComposition_succ {n : ℕ} (T : Fin (n + 1) → H → H) :
    finiteComposition T = T 0 ∘ finiteComposition (fun i ↦ T i.succ) := rfl

/-- The ordered composition of self-maps of `D` is again a self-map of `D`. -/
theorem finiteComposition_mapsTo (D : Set H) {m : ℕ} (T : Fin m → H → H)
    (hT : ∀ i, MapsTo (T i) D D) :
    MapsTo (finiteComposition T) D D := by
  induction m with
  | zero =>
      intro x hx
      simpa [finiteComposition] using hx
  | succ n ih =>
      rw [finiteComposition_succ]
      intro x hx
      exact hT 0 (ih (fun i ↦ T i.succ) (fun i ↦ hT i.succ) hx)

end

section

variable {H : Type u} [PseudoMetricSpace H] {D : Set H}

/-- Helper for Proposition 4.9: composing a list of `1`-Lipschitz self-maps preserves the same
Lipschitz constant. -/
private theorem finiteComposition_lipschitz :
    {m : ℕ} → (T : Fin m → D → D) →
      (∀ i, LipschitzWith 1 (T i)) → LipschitzWith 1 (finiteComposition T)
  | 0, _, _ => by
      simpa [finiteComposition] using (LipschitzWith.id : LipschitzWith 1 (id : D → D))
  | _ + 1, T, hT => by
      simpa [finiteComposition_succ] using
        (hT 0).comp (finiteComposition_lipschitz (fun i ↦ T i.succ) (fun i ↦ hT i.succ))

/-- Proposition 4.9 (2): the ordered composition of finitely many nonexpansive self-maps of `D`
is nonexpansive. -/
theorem lipschitzWith_finiteComposition {m : ℕ} (T : Fin m → D → D)
    (hT : ∀ i, LipschitzWith 1 (T i)) :
    LipschitzWith 1 (finiteComposition T) :=
  finiteComposition_lipschitz T hT

end
