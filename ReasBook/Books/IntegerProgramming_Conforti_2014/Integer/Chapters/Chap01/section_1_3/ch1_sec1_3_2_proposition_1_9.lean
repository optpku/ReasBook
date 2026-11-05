/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9.LinearSystem

@[expose] public section

open scoped Matrix

/-- Proposition 1.9. If `A : Matrix (Fin n) (Fin n) ℚ` is nonsingular, `b : Fin n → ℚ`, and
`x : Fin n → ℚ` satisfies `A *ᵥ x = b`, then the binary encoding size of `x` is bounded above by a
polynomial in the binary encoding size of `(A, b)`. -/
theorem nonsingular_rational_linear_system_solution_encoding_size_bound :
    ∃ p : Polynomial ℕ,
      ∀ n (A : Matrix (Fin n) (Fin n) ℚ) (b x : Fin n → ℚ),
        IsUnit A.det →
        A *ᵥ x = b →
        EncodingSize.rationalVector x ≤ p.eval (rational_linear_system_encoding_size A b) := by
  obtain ⟨p, hp⟩ := rational_linear_system_has_small_rational_solution
  refine ⟨p, ?_⟩
  intro n A b x hA hx
  have h_real_solution :
      ∃ xbar : Fin n → ℝ, (A.map (Rat.castHom ℝ)) *ᵥ xbar = fun i ↦ (b i : ℝ) := by
    refine ⟨fun i ↦ (x i : ℝ), ?_⟩
    ext i
    exact (RingHom.map_mulVec (Rat.castHom ℝ) A x i).symm.trans (by simp [hx])
  obtain ⟨y, hy, hy_bound⟩ := hp n n A b h_real_solution
  have h_injective : Function.Injective (fun y ↦ A *ᵥ y) := by
    simpa using
      (Matrix.mulVec_injective_iff_isUnit.mpr (A.isUnit_iff_isUnit_det.mpr hA))
  exact (h_injective (hx.trans hy.symm)) ▸ hy_bound

end
