/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free

open Set
open scoped MixedIntegerNotation

section Remark67

variable {n p : ℕ} {K : Set (Fin p → ℝ)}

/-- Remark 6.7 (1). The cylinder over a closed set is closed. -/
theorem remark_6_7_cylinder_isClosed
    (hK_closed : IsClosed K) :
    IsClosed (K ×ˢ (univ : Set (Fin (n - p) → ℝ))) := by
  simpa using hK_closed.prod isClosed_univ

/-- Remark 6.7 (2). The cylinder over a convex set is convex. -/
theorem remark_6_7_cylinder_convex
    (hK_convex : Convex ℝ K) :
    Convex ℝ (K ×ˢ (univ : Set (Fin (n - p) → ℝ))) := by
  simpa using hK_convex.prod convex_univ

variable {xbar : MixedRealPoint p (n - p)}

/-- Remark 6.7 (3). If the projection of `xbar` onto `ℝ^p` lies in `interior K`, then `xbar`
belongs to the interior of `K × ℝ^(n - p)`. -/
theorem remark_6_7_projection_interior_mem_cylinder_interior
    (hxbar : xbar.1 ∈ interior K) :
    xbar ∈ interior (K ×ˢ (univ : Set (Fin (n - p) → ℝ))) := by
  rw [interior_prod_eq, interior_univ]
  exact ⟨hxbar, mem_univ _⟩

/-- Remark 6.7 (4), canonical bridge form. If `K` is `ℤ^p`-free, then the cylinder
`K × ℝ^(n - p)` is free of the mixed-integer lattice `ℤ^p × ℝ^(n - p)`. -/
theorem remark_6_7_cylinder_is_free_of_mixed_integer_lattice
    (hK_lattice_free : is_lattice_free K) :
    is_free_of (ℤ^p×ℝ^(n - p)) (K ×ˢ (univ : Set (Fin (n - p) → ℝ))) := by
  rw [is_free_of_iff]
  intro x hx_lattice
  rw [interior_prod_eq, interior_univ]
  rintro ⟨hxK, -⟩
  exact hK_lattice_free.not_mem_interior (mem_mixed_integer_lattice_iff.mp hx_lattice) hxK

/-- Remark 6.7 (4). If `K` is `ℤ^p`-free, then the interior of `K × ℝ^(n - p)` contains no
point of `ℤ^p × ℝ^(n - p)`. -/
theorem remark_6_7_cylinder_interior_disjoint_mixed_integer_points
    (hK_lattice_free : is_lattice_free K) :
    Disjoint
      (interior (K ×ˢ (univ : Set (Fin (n - p) → ℝ))))
      (ℤ^p×ℝ^(n - p)) := by
  simpa [is_free_of] using
    remark_6_7_cylinder_is_free_of_mixed_integer_lattice hK_lattice_free

end Remark67
