/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_theorem_3_30

open scoped Matrix

-- Domain sampling for this corollary:
-- * primary domain: minimal mixed equality/inequality representations of polyhedra in `ℝ^n`
-- * source-facing owner: `mixed_constraint_polyhedron`
-- * core/canonical owner: `is_minimal_representation`
-- * exact canonical recall for parts (1) and (3):
--   `is_minimal_representation.full_row_rank`,
--   `minimal_representation_facet_rows_count`
-- * sampled bridge API for part (2): `minimal_representation_eq_rows_count`
-- * primitive data: the mixed system matrices and right-hand sides
-- * derived API: the rank and facet-count consequences for its solution polyhedron

section Corollary_3_32

variable {n meq mineq : ℕ}
variable
  (Aeq : Matrix (Fin meq) (Fin n) ℝ)
  (beq : Fin meq → ℝ)
  (Aineq : Matrix (Fin mineq) (Fin n) ℝ)
  (bineq : Fin mineq → ℝ)

local notation "P" => mixed_constraint_polyhedron Aineq bineq Aeq beq

/- Corollary 3.32 (1): if the mixed system `Aeq *ᵥ x = beq`, `Aineq *ᵥ x ≤ bineq` is a minimal
representation of its solution polyhedron, then `Aeq` has full row rank. This is the owner field
`is_minimal_representation.full_row_rank`. -/
recall is_minimal_representation.full_row_rank

/-- Corollary 3.32 (2): if the mixed system `Aeq *ᵥ x = beq`, `Aineq *ᵥ x ≤ bineq` is a minimal
representation of its nonempty solution polyhedron `P`, then `rank Aeq = n - dim P`, where
`dim P` is the affine dimension of `P`. -/
theorem minimal_representation_solution_set_rank_eq_ambient_sub_polyhedron_dim
    (hP_nonempty : Set.Nonempty P)
    (hmin : is_minimal_representation P Aeq beq Aineq bineq) :
    Aeq.rank =
      n - Module.finrank ℝ (affineSpan ℝ P).direction := by
  calc
    Aeq.rank = meq := hmin.full_row_rank
    _ = n - Module.finrank ℝ (affineSpan ℝ P).direction :=
      minimal_representation_eq_rows_count P Aeq beq Aineq bineq hP_nonempty hmin

/- Corollary 3.32 (3): if the mixed system `Aeq *ᵥ x = beq`, `Aineq *ᵥ x ≤ bineq` is a minimal
representation of its solution polyhedron `P`, then the inequality subsystem has as many rows as
`P` has facets. This is the canonical theorem `minimal_representation_facet_rows_count`. -/
recall minimal_representation_facet_rows_count

/- Corollary 3.32 (4): the rank and facet-count equalities above are necessary consequences of a
minimal representation, but they are not by themselves a converse criterion for the owner
`is_minimal_representation`. That owner also contains the affine-hull equation description
`eq_affine_hull` and the rowwise/facetwise correspondence fields `row_is_facet` and
`facets_exhausted`, so this file does not introduce a converse theorem from the numerical
equalities alone. -/

end Corollary_3_32
