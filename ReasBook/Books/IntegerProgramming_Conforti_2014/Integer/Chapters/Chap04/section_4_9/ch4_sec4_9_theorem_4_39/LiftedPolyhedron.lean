/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_11.ch2_sec2_11_proposition_2_19.LiftedPolyhedron

open scoped BigOperators Matrix Pointwise

section Theorem439

/-- Scaling a positive Balas block by `δᵢ⁻¹` recovers a point of the original polyhedron
`Aᵢ x ≤ bⁱ`. -/
lemma scaled_part_mem_input_polyhedron_of_positive_delta
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    {x : Fin n → ℝ}
    {xParts : Fin k → Fin n → ℝ}
    {δ : Fin k → ℝ}
    {i : Fin k}
    (hLifted : (x, xParts, δ) ∈ balas_lifted_polyhedron m A b)
    (hδ : 0 < δ i) :
    (δ i)⁻¹ • xParts i ∈ polyhedron_le_set (A i) (b i) := by
  rcases (mem_balas_lifted_polyhedron_iff m A b x xParts δ).1 hLifted with
    ⟨hineq, -, -, -⟩
  change A i *ᵥ ((δ i)⁻¹ • xParts i) ≤ b i
  intro j
  have hij : (A i *ᵥ xParts i) j ≤ δ i * b i j := by
    simpa [Pi.smul_apply, smul_eq_mul] using hineq i j
  have hdiv : (A i *ᵥ xParts i) j / δ i ≤ b i j := by
    refine (div_le_iff₀ hδ).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hij
  simpa [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hdiv

end Theorem439
