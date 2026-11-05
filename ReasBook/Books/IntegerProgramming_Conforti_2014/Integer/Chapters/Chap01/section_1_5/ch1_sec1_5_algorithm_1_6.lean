/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Mul
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_definition_1_37

public section

open scoped Matrix

namespace RationalLinearSystem

variable {m n m' : ℕ}

/-- Helper for Algorithm 1.6: casting an integer matrix-vector product to `ℚ` agrees
with multiplying the cast matrix by the cast vector. -/
lemma cast_mulVec_eq_map_mulVec
    (U : Matrix (Fin n) (Fin n) ℤ)
    (y : Fin n → ℤ) :
    (fun j ↦ ((U *ᵥ y) j : ℚ)) =
      U.map (Int.castRingHom ℚ) *ᵥ (fun j ↦ (y j : ℚ)) := by
  -- Compare the two vectors coordinatewise using the standard `map_mulVec` identity.
  ext j
  simpa using (RingHom.map_mulVec (Int.castRingHom ℚ) U y j)

/-- Helper for Algorithm 1.6: a solution of the transformed system `H *ᵥ y = b₁`
induces a solution of the cleaned system after applying the unimodular transport `U`. -/
lemma cleanedSystem_solution_of_transformedSolution
    (A₁ : Matrix (Fin m') (Fin n) ℚ)
    (b₁ : Fin m' → ℚ)
    (U : Matrix (Fin n) (Fin n) ℤ)
    (H : Matrix (Fin m') (Fin n) ℚ)
    (hH : H = A₁ * U.map (Int.castRingHom ℚ))
    (y : Fin n → ℤ)
    (hy : H *ᵥ (fun j ↦ (y j : ℚ)) = b₁) :
    A₁ *ᵥ (fun j ↦ ((U *ᵥ y) j : ℚ)) = b₁ := by
  -- Rewrite `H` through the factorization `A₁ * U` and reassociate the matrix action.
  calc
    A₁ *ᵥ (fun j ↦ ((U *ᵥ y) j : ℚ))
      = A₁ *ᵥ (U.map (Int.castRingHom ℚ) *ᵥ (fun j ↦ (y j : ℚ))) := by
          rw [cast_mulVec_eq_map_mulVec]
    _ = (A₁ * U.map (Int.castRingHom ℚ)) *ᵥ (fun j ↦ (y j : ℚ)) := by
          rw [← Matrix.mulVec_mulVec]
    _ = H *ᵥ (fun j ↦ (y j : ℚ)) := by
          rw [hH]
    _ = b₁ := hy

/-- Helper for Algorithm 1.6: an integer system equation over `ℤ` can be recovered from
its casted rational equation by injectivity of the integer cast into `ℚ`. -/
lemma integerSolution_of_castedIntegerSolution
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    (x : Fin n → ℤ)
    (hx :
      (A.map (Int.castRingHom ℚ)) *ᵥ (fun j ↦ (x j : ℚ)) =
        fun i ↦ (b i : ℚ)) :
    A *ᵥ x = b := by
  -- Reduce to coordinatewise equality after casting both sides to `ℚ`.
  ext i
  have hcast :
      (((A *ᵥ x) i : ℤ) : ℚ) = (b i : ℚ) := by
    have hi := congrArg (fun v ↦ v i) hx
    exact (RingHom.map_mulVec (Int.castRingHom ℚ) A x i).trans hi
  exact Int.cast_injective hcast

/-- Algorithm 1.6 (1). If step 1 replaces `A *ᵥ x = b` by a cleaned rational system
`A₁ *ᵥ x = b₁` with the same integer solution set, and step 2 produces a transformed
system `H = A₁ * U`, then any integer solution `ȳ` of `H *ᵥ y = b₁` transports to the
original integer solution `x̄ = U *ᵥ ȳ`. -/
theorem hnfSolution_transport
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    (A₁ : Matrix (Fin m') (Fin n) ℚ)
    (b₁ : Fin m' → ℚ)
    (hcleanup :
      integerSolutionSet A₁ b₁ =
        integerSolutionSet (A.map (Int.castRingHom ℚ)) (fun i ↦ (b i : ℚ)))
    (U : Matrix (Fin n) (Fin n) ℤ)
    (H : Matrix (Fin m') (Fin n) ℚ)
    (hH : H = A₁ * U.map (Int.castRingHom ℚ))
    (ybar : Fin n → ℤ)
    (hybar : H *ᵥ (fun j ↦ (ybar j : ℚ)) = b₁) :
    A *ᵥ (U *ᵥ ybar) = b := by
  -- First transport the HNF solution back to the cleaned system.
  have hclean :
      A₁ *ᵥ (fun j ↦ (((U *ᵥ ybar) j : ℤ) : ℚ)) = b₁ := by
    exact cleanedSystem_solution_of_transformedSolution A₁ b₁ U H hH ybar hybar
  have hmemClean : U *ᵥ ybar ∈ integerSolutionSet A₁ b₁ := by
    exact (mem_integerSolutionSet_iff A₁ b₁ (U *ᵥ ybar)).2 hclean
  -- Then rewrite membership across the cleanup equivalence to recover the original system.
  have hmemOriginal :
      U *ᵥ ybar ∈
        integerSolutionSet (A.map (Int.castRingHom ℚ)) (fun i ↦ (b i : ℚ)) := by
    rw [← hcleanup]
    exact hmemClean
  have hcast :
      (A.map (Int.castRingHom ℚ)) *ᵥ
          (fun j ↦ (((U *ᵥ ybar) j : ℤ) : ℚ)) =
        fun i ↦ (b i : ℚ) := by
    exact (mem_integerSolutionSet_iff
      (A.map (Int.castRingHom ℚ)) (fun i ↦ (b i : ℚ)) (U *ᵥ ybar)).1 hmemOriginal
  -- Finally drop the casts to recover the integer equation.
  exact integerSolution_of_castedIntegerSolution A b (U *ᵥ ybar) hcast

/-- Algorithm 1.6 (2). If step 1 replaces `A *ᵥ x = b` by a cleaned rational system
`A₁ *ᵥ x = b₁` with the same integer solution set and the cleaned system is infeasible
over `ℤ`, then the original integer system is infeasible as well. -/
theorem equivalentCleanedSystem_infeasible
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ)
    (A₁ : Matrix (Fin m') (Fin n) ℚ)
    (b₁ : Fin m' → ℚ)
    (hcleanup :
      integerSolutionSet A₁ b₁ =
        integerSolutionSet (A.map (Int.castRingHom ℚ)) (fun i ↦ (b i : ℚ)))
    (h_infeasible : ¬ hasIntegerSolution A₁ b₁) :
    ¬ hasIntegerSolution (A.map (Int.castRingHom ℚ)) (fun i ↦ (b i : ℚ)) := by
  -- Any original-system solution would transport back to the cleaned system.
  intro horig
  exact h_infeasible ((hasIntegerSolution_congr hcleanup).mpr horig)

end RationalLinearSystem

end
