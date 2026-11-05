/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Sign.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

namespace Matrix

section Definition140

variable {m n : ℕ}

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_definition_1_40.lean.
Definition 1.40. An integer matrix `A : Matrix (Fin m) (Fin n) ℤ` is unimodular when it has full
row rank and every `m × m` column submatrix has determinant in `Set.range SignType.cast`. -/
structure IsUnimodular (A : Matrix (Fin m) (Fin n) ℤ) : Prop where
  /-- The matrix `A` has full row rank. -/
  rank_eq : A.rank = m
  /-- Every `m × m` column submatrix of `A` has determinant in `Set.range SignType.cast`. -/
  det_submatrix_mem :
    ∀ cols : Fin m ↪ Fin n,
      (A.submatrix id cols).det ∈ Set.range (SignType.cast : SignType → ℤ)

/-- Build a unimodularity witness from the rank condition and the determinant condition on all
`m × m` column submatrices. -/
def IsUnimodular.ofConditions {A : Matrix (Fin m) (Fin n) ℤ} (hRank : A.rank = m)
    (hDet :
      ∀ cols : Fin m ↪ Fin n,
        (A.submatrix id cols).det ∈ Set.range (SignType.cast : SignType → ℤ)) :
    A.IsUnimodular where
  rank_eq := hRank
  det_submatrix_mem := hDet

/-- Expanding `A.IsUnimodular` recovers the textbook rank condition together with the determinant
condition on every `m × m` column submatrix. -/
theorem isUnimodular_iff (A : Matrix (Fin m) (Fin n) ℤ) :
    A.IsUnimodular ↔
      A.rank = m ∧
        ∀ cols : Fin m ↪ Fin n,
          (A.submatrix id cols).det ∈ Set.range (SignType.cast : SignType → ℤ) := by
  constructor
  · -- Read the rank and minor conditions from the bundled witness.
    intro hA
    exact ⟨hA.rank_eq, hA.det_submatrix_mem⟩
  · -- Reassemble the witness from precisely those two conditions.
    rintro ⟨hRank, hDet⟩
    exact IsUnimodular.ofConditions hRank hDet

/-- A unimodular `m × n` integer matrix has at least as many columns as rows. -/
theorem IsUnimodular.width_le {A : Matrix (Fin m) (Fin n) ℤ}
    (hA : A.IsUnimodular) :
    m ≤ n := by
  -- Replace the row count by the full rank and apply the general width bound.
  calc
    m = A.rank := hA.rank_eq.symm
    _ ≤ n := Matrix.rank_le_width A

/-- For a unimodular integer matrix, every `m × m` column submatrix has determinant in
`Set.range SignType.cast`. -/
theorem IsUnimodular.det_mem {A : Matrix (Fin m) (Fin n) ℤ}
    (hA : A.IsUnimodular) (cols : Fin m ↪ Fin n) :
    (A.submatrix id cols).det ∈ Set.range (SignType.cast : SignType → ℤ) := by
  -- Specialize the determinant condition stored in the unimodularity witness.
  exact hA.det_submatrix_mem cols

/-- In the square case, `A.IsUnimodular` recovers the usual `IsUnit A.det` criterion for an
integral unimodular matrix. -/
theorem isUnimodular_iff_isUnit_det (A : Matrix (Fin n) (Fin n) ℤ) :
    A.IsUnimodular ↔ IsUnit A.det := by
  classical
  constructor
  · intro hA
    -- Full square rank makes the columns independent, hence the determinant is nonzero.
    have hCols : LinearIndependent ℤ A.col := by
      apply linearIndependent_iff_card_eq_finrank_span.mpr
      calc
        Fintype.card (Fin n) = n := Fintype.card_fin n
        _ = A.rank := hA.rank_eq.symm
        _ = Module.finrank ℤ (Submodule.span ℤ (Set.range A.col)) :=
          A.rank_eq_finrank_span_cols
    have hDetNe : A.det ≠ 0 := by
      intro hDetZero
      obtain ⟨v, hv, hKernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hDetZero
      apply hv
      apply Matrix.mulVec_injective_iff.mpr hCols
      simpa using hKernel
    -- The identity minor lies in the sign range; only the two nonzero signs remain.
    have hDetMem : A.det ∈ Set.range (SignType.cast : SignType → ℤ) := by
      simpa using hA.det_mem (Function.Embedding.refl (Fin n))
    obtain ⟨s, hs⟩ := hDetMem
    cases s with
    | zero =>
        exfalso
        apply hDetNe
        simpa using hs.symm
    | neg =>
        rw [← hs]
        simp
    | pos =>
        rw [← hs]
        simp
  · intro hDet
    -- An invertible determinant makes the square matrix invertible and therefore full-rank.
    have hMatrix : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hDet
    refine IsUnimodular.ofConditions ?_ ?_
    · simpa using Matrix.rank_of_isUnit A hMatrix
    · intro cols
      -- Every self-embedding of `Fin n` is a permutation, so its minor changes by a unit sign.
      let e : Equiv.Perm (Fin n) := cols.equivOfFiniteSelfEmbedding
      have hMinor :
          (A.submatrix id cols).det = (Equiv.Perm.sign e : ℤ) * A.det := by
        simpa only [e, Function.Embedding.toEmbedding_equivOfFiniteSelfEmbedding] using
          Matrix.det_permute' e A
      have hMinorUnit : IsUnit (A.submatrix id cols).det := by
        rw [hMinor]
        exact (Units.isUnit (Equiv.Perm.sign e)).mul hDet
      -- Integer units are exactly the positive and negative signs.
      rcases Int.isUnit_iff.mp hMinorUnit with hOne | hNegOne
      · have hPosCast : (SignType.cast SignType.pos : ℤ) = (A.submatrix id cols).det := by
          simpa using hOne.symm
        exact ⟨SignType.pos, hPosCast⟩
      · have hNegCast : (SignType.cast SignType.neg : ℤ) = (A.submatrix id cols).det := by
          simpa using hNegOne.symm
        exact ⟨SignType.neg, hNegCast⟩

end Definition140

end Matrix

end

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_a854324b892aef4c68a2"
#print axioms _root_.Matrix.IsUnimodular
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_a854324b892aef4c68a2"
