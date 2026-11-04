/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Hull
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1.MatrixPolyhedron

open scoped BigOperators Matrix Pointwise

section Proposition219LiftedPolyhedron

/-- The lifted polyhedron in Balas' formulation, with variables `(x, xParts, δ)`. -/
def balas_lifted_polyhedron
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ) :
    Set ((Fin n → ℝ) × (Fin k → Fin n → ℝ) × (Fin k → ℝ)) :=
  {y |
    (∀ i : Fin k, A i *ᵥ y.2.1 i ≤ y.2.2 i • b i) ∧
      (∑ i : Fin k, y.2.1 i = y.1) ∧
      (∑ i : Fin k, y.2.2 i = 1) ∧
      (∀ i : Fin k, 0 ≤ y.2.2 i)}

/-- Membership in the Balas lifted polyhedron is exactly the system
`Aᵢ xⁱ ≤ δᵢ bⁱ`, `∑ xⁱ = x`, `∑ δᵢ = 1`, and `δᵢ ≥ 0`. -/
theorem mem_balas_lifted_polyhedron_iff
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (x : Fin n → ℝ)
    (xParts : Fin k → Fin n → ℝ)
    (δ : Fin k → ℝ) :
    (x, xParts, δ) ∈ balas_lifted_polyhedron m A b ↔
      (∀ i : Fin k, A i *ᵥ xParts i ≤ δ i • b i) ∧
        (∑ i : Fin k, xParts i = x) ∧
        (∑ i : Fin k, δ i = 1) ∧
        (∀ i : Fin k, 0 ≤ δ i) := by
  rfl

/-- The projection of the Balas lifted polyhedron onto the `x`-coordinates. -/
def balas_x_projection
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ) : Set (Fin n → ℝ) :=
  Prod.fst '' balas_lifted_polyhedron m A b

/-- Membership in the `x`-projection of the Balas lifted polyhedron is existence of compatible
auxiliary variables `(xParts, δ)`. -/
theorem mem_balas_x_projection_iff
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (x : Fin n → ℝ) :
    x ∈ balas_x_projection m A b ↔
      ∃ xParts : Fin k → Fin n → ℝ, ∃ δ : Fin k → ℝ,
        (x, xParts, δ) ∈ balas_lifted_polyhedron m A b := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2.1, y.2.2, hy⟩
  · rintro ⟨xParts, δ, hLifted⟩
    exact ⟨(x, xParts, δ), hLifted, rfl⟩

/-- Activating only the `i`-th block shows that each input polyhedron `Aᵢ x ≤ bⁱ` lies inside
the Balas `x`-projection. -/
theorem polyhedron_le_set_subset_balas_x_projection
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (i : Fin k) :
    polyhedron_le_set (A i) (b i) ⊆ balas_x_projection m A b := by
  intro x hx
  rw [mem_balas_x_projection_iff]
  refine ⟨Pi.single i x, Pi.single i (1 : ℝ), ?_⟩
  rw [mem_balas_lifted_polyhedron_iff m A b x (Pi.single i x) (Pi.single i (1 : ℝ))]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst hji
      simpa using hx
    · simp [hji]
  · ext t
    rw [Fintype.sum_eq_single i]
    · simp
    · intro j hji
      simp [hji]
  · simp
  · intro j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]

/-- A point of one input polyhedron belongs to the Balas `x`-projection by activating only its
own block. -/
theorem mem_balas_x_projection_of_mem_polyhedron_le_set
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    {i : Fin k}
    {x : Fin n → ℝ}
    (hx : x ∈ polyhedron_le_set (A i) (b i)) :
    x ∈ balas_x_projection m A b :=
  polyhedron_le_set_subset_balas_x_projection m A b i hx

/-- The Balas `x`-projection is convex because convex combinations of lifted witnesses remain
lifted witnesses. -/
theorem convex_balas_x_projection
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ) :
    Convex ℝ (balas_x_projection m A b) := by
  intro x hx y hy a c ha hc hac
  rw [mem_balas_x_projection_iff] at hx hy ⊢
  rcases hx with ⟨xParts, δ, hLiftedX⟩
  rcases hy with ⟨yParts, ε, hLiftedY⟩
  rcases (mem_balas_lifted_polyhedron_iff m A b x xParts δ).1 hLiftedX with
    ⟨hineqX, hsumX, hsumδ, hδnonneg⟩
  rcases (mem_balas_lifted_polyhedron_iff m A b y yParts ε).1 hLiftedY with
    ⟨hineqY, hsumY, hsumε, hεnonneg⟩
  let zParts : Fin k → Fin n → ℝ := fun i ↦ a • xParts i + c • yParts i
  let ζ : Fin k → ℝ := fun i ↦ a * δ i + c * ε i
  refine ⟨zParts, ζ, ?_⟩
  rw [mem_balas_lifted_polyhedron_iff m A b (a • x + c • y) zParts ζ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    have hxij : (A i *ᵥ xParts i) j ≤ δ i * b i j := by
      simpa [Pi.smul_apply, smul_eq_mul] using hineqX i j
    have hyij : (A i *ᵥ yParts i) j ≤ ε i * b i j := by
      simpa [Pi.smul_apply, smul_eq_mul] using hineqY i j
    have hax : a * (A i *ᵥ xParts i) j ≤ a * (δ i * b i j) := by
      exact mul_le_mul_of_nonneg_left hxij ha
    have hcy : c * (A i *ᵥ yParts i) j ≤ c * (ε i * b i j) := by
      exact mul_le_mul_of_nonneg_left hyij hc
    have hsum := add_le_add hax hcy
    simpa [zParts, ζ, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
      left_distrib, right_distrib, mul_add, add_mul, mul_assoc] using hsum
  · calc
      ∑ i : Fin k, zParts i = ∑ i : Fin k, (a • xParts i + c • yParts i) := by
        rfl
      _ = a • ∑ i : Fin k, xParts i + c • ∑ i : Fin k, yParts i := by
        rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]
      _ = a • x + c • y := by
        rw [hsumX, hsumY]
  · calc
      ∑ i : Fin k, ζ i = ∑ i : Fin k, (a * δ i + c * ε i) := by
        rfl
      _ = a * ∑ i : Fin k, δ i + c * ∑ i : Fin k, ε i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = 1 := by
        simpa [hsumδ, hsumε] using hac
  · intro i
    exact add_nonneg (mul_nonneg ha (hδnonneg i)) (mul_nonneg hc (hεnonneg i))

end Proposition219LiftedPolyhedron
