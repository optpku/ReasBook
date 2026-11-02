import Mathlib.Analysis.Convex.Hull
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_11.ch2_sec2_11_proposition_2_19.LiftedPolyhedron

open scoped BigOperators Matrix

section Proposition219

variable {n k : ℕ}
variable (m : Fin k → ℕ)
variable (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
variable (b : ∀ i : Fin k, Fin (m i) → ℝ)

/-- Proposition 2.19: the convex hull of `⋃ i : Fin k, polyhedron_le_set (A i) (b i)` lies in the
canonical Balas projection set `balas_x_projection m A b`. -/
theorem convexHull_iUnion_matrix_polyhedra_subset_balas_x_projection :
    convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i)) ⊆ balas_x_projection m A b := by
  refine convexHull_min ?_ (convex_balas_x_projection m A b)
  intro y hy
  rcases Set.mem_iUnion.1 hy with ⟨i, hyi⟩
  exact polyhedron_le_set_subset_balas_x_projection m A b i hyi

/-- A point of `convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i))` lies in the canonical
Balas projection `balas_x_projection m A b`. -/
theorem mem_convexHull_iUnion_matrix_polyhedra_imp_mem_balas_x_projection
    (y : Fin n → ℝ)
    (hy : y ∈ convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i))) :
    y ∈ balas_x_projection m A b :=
  (convexHull_iUnion_matrix_polyhedra_subset_balas_x_projection m A b) hy

/-- A point of `convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i))` admits Balas block
witnesses satisfying the source system of Proposition 2.19. -/
theorem mem_convexHull_iUnion_matrix_polyhedra_imp_exists_parts
    (y : Fin n → ℝ)
    (hy : y ∈ convexHull ℝ (⋃ i : Fin k, polyhedron_le_set (A i) (b i))) :
    ∃ yParts : Fin k → Fin n → ℝ, ∃ x : Fin k → ℝ,
      (∀ i : Fin k, A i *ᵥ yParts i ≤ x i • b i) ∧
        (∑ i : Fin k, yParts i = y) ∧
        (∑ i : Fin k, x i = 1) ∧
        (∀ i : Fin k, 0 ≤ x i) := by
  have hyProj :
      y ∈ balas_x_projection m A b :=
    (convexHull_iUnion_matrix_polyhedra_subset_balas_x_projection m A b) hy
  rcases (mem_balas_x_projection_iff m A b y).1 hyProj with ⟨yParts, x, hLifted⟩
  exact ⟨yParts, x, (mem_balas_lifted_polyhedron_iff m A b y yParts x).1 hLifted⟩

end Proposition219
