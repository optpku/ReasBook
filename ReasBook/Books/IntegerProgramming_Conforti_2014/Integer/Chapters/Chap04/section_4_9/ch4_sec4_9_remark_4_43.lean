/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_theorem_4_42

open scoped BigOperators Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: Balas convexification for finite unions of matrix polyhedra
-- * core/canonical owner: `closure_convexHull_iUnion_matrix_polyhedra_eq_balas_x_projection_iff`
-- * supporting owners inspected upstream: `balas_nonempty_family` and `PointedCone.hull`
-- This file therefore keeps only the source-facing all-nonempty specialization of Theorem 4.42.

section Remark443

/-- Remark 4.43. If the `k` input polyhedra `Pᵢ = {x ∈ ℝ^n | Aᵢ x ≤ bⁱ}` are all nonempty, then
the closure of the convex hull of `⋃ i, Pᵢ` is the projection of the Balas lifted polyhedron `Y`
onto the `x`-space. -/
theorem closure_convexHull_iUnion_matrix_polyhedra_eq_balas_x_projection_of_all_nonempty
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (R : Fin k → Finset (Fin n → ℝ))
    (h_nonempty : ∀ i : Fin k, (polyhedron_le_set (A i) (b i)).Nonempty)
    (hR :
      ∀ i : Fin k,
        polyhedron_le_set (A i) 0 =
          (PointedCone.hull ℝ ((R i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :
            Set (Fin n → ℝ))) :
    closure (convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i))) =
      balas_x_projection m A b := by
  by_cases hk : k = 0
  · subst hk
    ext x
    simp [balas_x_projection, balas_lifted_polyhedron]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk
    refine
      (closure_convexHull_iUnion_matrix_polyhedra_eq_balas_x_projection_iff m A b R ?_ hR).2 ?_
    · obtain ⟨x, hx⟩ := h_nonempty ⟨0, hk⟩
      exact ⟨x, Set.mem_iUnion.2 ⟨⟨0, hk⟩, hx⟩⟩
    · intro j
      rw [hR j]
      change PointedCone.hull ℝ (R j : Set (Fin n → ℝ)) ≤
        PointedCone.hull ℝ (balas_nonempty_family m A b R)
      exact Submodule.span_mono <| by
        intro x hx
        rw [mem_balas_nonempty_family_iff]
        exact ⟨j, (h_nonempty j).ne_empty, hx⟩

end Remark443
