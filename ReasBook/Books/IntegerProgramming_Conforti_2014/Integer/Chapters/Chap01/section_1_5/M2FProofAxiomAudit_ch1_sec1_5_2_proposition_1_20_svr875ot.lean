/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_definition_1_37

public section

open scoped Matrix

namespace RationalLinearSystem

variable {m p : ℕ}

/-- Helper for Proposition 1.20: multiplication by the block matrix `(D 0)` depends only on
the head coordinates of the vector. -/
lemma appendZeroBlock_mulVec_head
    {R : Type*} [CommSemiring R]
    (D : Matrix (Fin m) (Fin m) R)
    (x : Fin (m + p) → R) :
    (fun i ↦ Fin.append (D i) (0 : Fin p → R)) *ᵥ x =
      D *ᵥ (fun j ↦ x (Fin.castAdd p j)) := by
  -- Split the finite sum into the head and tail blocks; every tail summand vanishes.
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]

/-- Helper for Proposition 1.20: mapping coefficients across a ring homomorphism preserves a
matrix consisting of a head block and a zero tail block. -/
lemma map_appendZeroBlock
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S)
    (D : Matrix (Fin m) (Fin m) R) :
    Matrix.map (fun i ↦ Fin.append (D i) (0 : Fin p → R)) f =
      fun i ↦ Fin.append ((D.map f) i) (0 : Fin p → S) := by
  -- Check the mapped entries separately on the head and tail summands.
  ext i j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · simp [Matrix.map_apply]
  · simp [Matrix.map_apply]

/-- Helper for Proposition 1.20: an invertible head block uniquely determines the head of every
solution of the associated block system. -/
lemma blockSolution_head_eq
    (A : Matrix (Fin m) (Fin (m + p)) ℚ)
    (D : Matrix (Fin m) (Fin m) ℚ)
    [Invertible D]
    (hA : A = fun i ↦ Fin.append (D i) (0 : Fin p → ℚ))
    (b ybar : Fin m → ℚ)
    (hybar : D *ᵥ ybar = b)
    (x : Fin (m + p) → ℚ)
    (hx : A *ᵥ x = b) :
    (fun i ↦ x (Fin.castAdd p i)) = ybar := by
  -- Normalize the block equation, then cancel the invertible matrix `D`.
  apply Matrix.mulVec_injective_of_invertible D
  calc
    D *ᵥ (fun i ↦ x (Fin.castAdd p i)) = A *ᵥ x := by
      rw [hA, appendZeroBlock_mulVec_head]
    _ = b := hx
    _ = D *ᵥ ybar := hybar.symm

/-- Helper for Proposition 1.20: after casting the block system to `ℝ`, invertibility still
forces the head of every real solution to be the cast of the distinguished rational solution. -/
lemma realBlockSolution_head_eq
    (A : Matrix (Fin m) (Fin (m + p)) ℚ)
    (D : Matrix (Fin m) (Fin m) ℚ)
    [Invertible D]
    (hA : A = fun i ↦ Fin.append (D i) (0 : Fin p → ℚ))
    (b ybar : Fin m → ℚ)
    (hybar : D *ᵥ ybar = b)
    (x : Fin (m + p) → ℝ)
    (hx : (A.map (Rat.castHom ℝ)) *ᵥ x = fun i ↦ (b i : ℝ)) :
    (fun i ↦ x (Fin.castAdd p i)) = fun i ↦ (ybar i : ℝ) := by
  -- Mapping the canonical inverse supplies precisely the invertibility needed over `ℝ`.
  -- Local instance justification (mapped invertibility): `Invertible.map` transports the given
  -- inverse of `D`, while no global instance can select a coefficient homomorphism.
  letI : Invertible (D.map (Rat.castHom ℝ)) :=
    Invertible.map (Rat.castHom ℝ).mapMatrix D
  have hblock :
      A.map (Rat.castHom ℝ) =
        fun i ↦ Fin.append ((D.map (Rat.castHom ℝ)) i) (0 : Fin p → ℝ) := by
    -- Cast each entry of the rational block presentation.
    rw [hA]
    exact map_appendZeroBlock (Rat.castHom ℝ) D
  have hybarReal :
      D.map (Rat.castHom ℝ) *ᵥ (fun i ↦ (ybar i : ℝ)) = fun i ↦ (b i : ℝ) := by
    -- Apply the coefficient homomorphism pointwise to `hybar`.
    funext i
    calc
      (D.map (Rat.castHom ℝ) *ᵥ (fun i ↦ (ybar i : ℝ))) i =
          (Rat.castHom ℝ) ((D *ᵥ ybar) i) := by
            simpa only [Function.comp_apply] using
              (RingHom.map_mulVec (Rat.castHom ℝ) D ybar i).symm
      _ = (Rat.castHom ℝ) (b i) := congrArg (Rat.castHom ℝ) (congrFun hybar i)
      _ = (b i : ℝ) := rfl
  -- Normalize the real block equation and cancel the mapped invertible head block.
  apply Matrix.mulVec_injective_of_invertible (D.map (Rat.castHom ℝ))
  calc
    D.map (Rat.castHom ℝ) *ᵥ (fun i ↦ x (Fin.castAdd p i)) =
        A.map (Rat.castHom ℝ) *ᵥ x := by
          rw [hblock, appendZeroBlock_mulVec_head]
    _ = (fun i ↦ (b i : ℝ)) := hx
    _ = D.map (Rat.castHom ℝ) *ᵥ (fun i ↦ (ybar i : ℝ)) := hybarReal.symm

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_proposition_1_20.lean.
Proposition 1.20 (1): if `A = (D 0)` with `D` invertible and `ȳ` solves `D *ᵥ ȳ = b`, then the
real solution set of `A x = b` consists exactly of the vectors `Fin.append ȳ k` with arbitrary
tail `k : Fin p → ℝ`. -/
theorem realSolutionSet_eq_range_append
    (A : Matrix (Fin m) (Fin (m + p)) ℚ)
    (D : Matrix (Fin m) (Fin m) ℚ)
    [Invertible D]
    (hA : A = fun i ↦ Fin.append (D i) (0 : Fin p → ℚ))
    (b ybar : Fin m → ℚ)
    (hybar : D *ᵥ ybar = b) :
    {x : Fin (m + p) → ℝ | (A.map (Rat.castHom ℝ)) *ᵥ x = fun i ↦ (b i : ℝ)} =
      Set.range (fun k : Fin p → ℝ ↦ Fin.append (fun i ↦ (ybar i : ℝ)) k) := by
  -- Compare membership pointwise: uniqueness fixes the head and leaves the tail arbitrary.
  ext x
  constructor
  · intro hx
    have hhead := realBlockSolution_head_eq A D hA b ybar hybar x hx
    refine ⟨fun j ↦ x (Fin.natAdd m j), ?_⟩
    calc
      Fin.append (fun i ↦ (ybar i : ℝ)) (fun j ↦ x (Fin.natAdd m j)) =
          Fin.append (fun i ↦ x (Fin.castAdd p i)) (fun j ↦ x (Fin.natAdd m j)) := by
            rw [hhead]
      _ = x := Fin.append_castAdd_natAdd
  · rintro ⟨k, rfl⟩
    have hybarReal :
        D.map (Rat.castHom ℝ) *ᵥ (fun i ↦ (ybar i : ℝ)) = fun i ↦ (b i : ℝ) := by
      -- Cast the rational head equation before restoring the zero tail block.
      funext i
      calc
        (D.map (Rat.castHom ℝ) *ᵥ (fun i ↦ (ybar i : ℝ))) i =
            (Rat.castHom ℝ) ((D *ᵥ ybar) i) := by
              simpa only [Function.comp_apply] using
                (RingHom.map_mulVec (Rat.castHom ℝ) D ybar i).symm
        _ = (Rat.castHom ℝ) (b i) := congrArg (Rat.castHom ℝ) (congrFun hybar i)
        _ = (b i : ℝ) := rfl
    rw [hA]
    calc
      (Matrix.map (fun i ↦ Fin.append (D i) (0 : Fin p → ℚ)) (Rat.castHom ℝ)) *ᵥ
          Fin.append (fun i ↦ (ybar i : ℝ)) k =
          D.map (Rat.castHom ℝ) *ᵥ (fun i ↦ (ybar i : ℝ)) := by
            rw [map_appendZeroBlock]
            simpa only [Fin.append_left] using
              appendZeroBlock_mulVec_head
                (D := D.map (Rat.castHom ℝ))
                (x := Fin.append (fun i ↦ (ybar i : ℝ)) k)
      _ = (fun i ↦ (b i : ℝ)) := hybarReal

/-- Proposition 1.20 (2): under the same block presentation, `A x = b` has an integer solution
exactly when the head solution `ȳ` is integral. -/
theorem hasIntegerSolution_iff_headSolution_integral
    (A : Matrix (Fin m) (Fin (m + p)) ℚ)
    (D : Matrix (Fin m) (Fin m) ℚ)
    [Invertible D]
    (hA : A = fun i ↦ Fin.append (D i) (0 : Fin p → ℚ))
    (b ybar : Fin m → ℚ)
    (hybar : D *ᵥ ybar = b) :
    hasIntegerSolution A b ↔ ∃ zbar : Fin m → ℤ, (fun i ↦ (zbar i : ℚ)) = ybar := by
  -- Expand feasibility and use head uniqueness in the forward direction.
  rw [hasIntegerSolution_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun i ↦ x (Fin.castAdd p i), ?_⟩
    exact blockSolution_head_eq A D hA b ybar hybar (fun j ↦ (x j : ℚ)) hx
  · rintro ⟨zbar, hzbar⟩
    -- Append a zero tail; block normalization reduces its equation to `hybar`.
    refine ⟨Fin.append zbar (0 : Fin p → ℤ), ?_⟩
    rw [hA, appendZeroBlock_mulVec_head]
    simpa only [Fin.append_left, hzbar] using hybar

/-- Proposition 1.20 (3): when the head solution `ȳ` is represented by the integer vector
`zbar`, the integer solution set of `A x = b` consists exactly of the vectors
`Fin.append zbar k` with arbitrary tail `k : Fin p → ℤ`. -/
theorem integerSolutionSet_eq_range_append
    (A : Matrix (Fin m) (Fin (m + p)) ℚ)
    (D : Matrix (Fin m) (Fin m) ℚ)
    [Invertible D]
    (hA : A = fun i ↦ Fin.append (D i) (0 : Fin p → ℚ))
    (b ybar : Fin m → ℚ)
    (hybar : D *ᵥ ybar = b)
    (zbar : Fin m → ℤ)
    (hzbar : (fun i ↦ (zbar i : ℚ)) = ybar) :
    integerSolutionSet A b = Set.range (fun k : Fin p → ℤ ↦ Fin.append zbar k) := by
  -- Compare membership pointwise, identifying the head by invertibility and retaining the tail.
  ext x
  rw [mem_integerSolutionSet_iff]
  constructor
  · intro hx
    have hheadQ :
        (fun i ↦ (x (Fin.castAdd p i) : ℚ)) = ybar :=
      blockSolution_head_eq A D hA b ybar hybar (fun j ↦ (x j : ℚ)) hx
    have hhead : (fun i ↦ x (Fin.castAdd p i)) = zbar := by
      -- Injectivity of the integer cast turns the rational head equality into an integer one.
      funext i
      exact_mod_cast congrFun (hheadQ.trans hzbar.symm) i
    refine ⟨fun j ↦ x (Fin.natAdd m j), ?_⟩
    calc
      Fin.append zbar (fun j ↦ x (Fin.natAdd m j)) =
          Fin.append (fun i ↦ x (Fin.castAdd p i)) (fun j ↦ x (Fin.natAdd m j)) := by
            rw [hhead]
      _ = x := Fin.append_castAdd_natAdd
  · rintro ⟨k, rfl⟩
    -- Every appended tail solves the system because the zero block annihilates it.
    rw [hA, appendZeroBlock_mulVec_head]
    simpa only [Fin.append_left, hzbar] using hybar

end RationalLinearSystem

end

#print axioms RationalLinearSystem.realSolutionSet_eq_range_append

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_9ac5b1e77d37797b992a"
#print axioms _root_.RationalLinearSystem.realSolutionSet_eq_range_append
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_9ac5b1e77d37797b992a"
