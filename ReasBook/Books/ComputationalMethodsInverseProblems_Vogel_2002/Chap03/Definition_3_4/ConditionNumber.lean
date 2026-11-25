/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum

public section

noncomputable section

namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The condition number of a nonzero real matrix, defined as the ratio of its
largest singular value to its smallest nonzero singular value. -/
def conditionNumber (A : Matrix n n ℝ) (hA : A ≠ 0) : ℝ :=
  let _ : A ≠ 0 := hA
  A.toEuclideanLin.singularValues 0 /
    A.toEuclideanLin.singularValues (Module.finrank ℝ A.toEuclideanLin.range - 1)

/-- The condition number of a positive-definite real matrix. The nonzero witness
needed by `Matrix.conditionNumber` is discharged from positive definiteness once
the index type is nonempty. -/
def posDefConditionNumber [Nonempty n] (A : Matrix n n ℝ) (hA : A.PosDef) : ℝ :=
  A.conditionNumber hA.isUnit.ne_zero

/-- Rewrites `conditionNumber` as the ratio of the extremal nonzero singular
values of `A.toEuclideanLin`. -/
theorem conditionNumber_eq_singularValueRatio (A : Matrix n n ℝ) (hA : A ≠ 0) :
    A.conditionNumber hA =
      A.toEuclideanLin.singularValues 0 /
        A.toEuclideanLin.singularValues (Module.finrank ℝ A.toEuclideanLin.range - 1) := by
  -- Unfold the definition of the condition number.
  rfl

/-- `Matrix.posDefConditionNumber` is the usual condition number specialized to
positive-definite matrices. -/
theorem posDefConditionNumber_eq_conditionNumber [Nonempty n] (A : Matrix n n ℝ)
    (hA : A.PosDef) :
    A.posDefConditionNumber hA = A.conditionNumber hA.isUnit.ne_zero := by
  simp [Matrix.posDefConditionNumber]

/-- For a positive operator, the singular values up to the dimension exhaust its spectrum. -/
private lemma spectrum_eq_range_singularValues_of_isPositive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsPositive) :
    spectrum ℝ T = Set.range (fun i : Fin (Module.finrank ℝ E) ↦ T.singularValues i) := by
  have hsq : T.adjoint ∘ₗ T = T ^ 2 := by
    rw [hT.adjoint_eq, pow_two]
    rfl
  ext μ
  constructor
  · intro hμ
    have heigen := Module.End.HasEigenvalue.of_mem_spectrum hμ
    obtain ⟨j, hj⟩ := hT.isSymmetric.exists_eigenvalues_eq rfl heigen
    change hT.isSymmetric.eigenvalues rfl j = μ at hj
    have hμ_nonneg : 0 ≤ μ := by
      simpa only [hj] using hT.nonneg_eigenvalues rfl j
    have heigen_sq : Module.End.HasEigenvalue (T.adjoint ∘ₗ T) (μ ^ 2) := by
      rw [hsq]
      exact heigen.pow 2
    obtain ⟨i, hi⟩ := T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl heigen_sq
    refine ⟨i, (sq_eq_sq₀ (T.singularValues_nonneg i) hμ_nonneg).1 ?_⟩
    exact (T.sq_singularValues_fin rfl i).trans hi
  · rintro ⟨i, rfl⟩
    obtain ⟨v, hv⟩ :=
      (T.hasEigenvalue_adjoint_comp_self_sq_singularValues i.isLt).exists_hasEigenvector
    let b := hT.isSymmetric.eigenvectorBasis rfl
    have hv_repr : b.repr v ≠ 0 := by
      exact fun h ↦ hv.2 (b.repr.injective (by simpa using h))
    have hv_coord : ∃ j, b.repr v j ≠ 0 := by
      by_contra! h
      exact hv_repr (by ext j; exact h j)
    obtain ⟨j, hj⟩ := hv_coord
    have hcoord := congrArg (fun w ↦ b.repr w j) hv.apply_eq_smul
    have hsq_coord :
        (hT.isSymmetric.eigenvalues rfl j) ^ 2 * b.repr v j =
          (T.singularValues i) ^ 2 * b.repr v j := by
      simpa only [hsq, pow_two, Module.End.mul_apply, LinearIsometryEquiv.map_smul,
        PiLp.smul_apply, smul_eq_mul, b, hT.isSymmetric.eigenvectorBasis_apply_self_apply,
        mul_assoc] using! hcoord
    have heq : hT.isSymmetric.eigenvalues rfl j = T.singularValues i :=
      (sq_eq_sq₀ (hT.nonneg_eigenvalues rfl j) (T.singularValues_nonneg i)).1
        (mul_right_cancel₀ hj hsq_coord)
    change T.singularValues (i : ℕ) ∈ spectrum ℝ T
    rw [← heq]
    exact (hT.isSymmetric.hasEigenvalue_eigenvalues rfl j).mem_spectrum

/-- For a positive-definite real matrix, the condition number is the ratio of
the largest and smallest spectral values. -/
theorem conditionNumber_eq_spectralExtrema_of_posDef (A : Matrix n n ℝ) (hA : A ≠ 0)
    (hspd : A.PosDef) :
    A.conditionNumber hA = sSup (spectrum ℝ A) / sInf (spectrum ℝ A) := by
  haveI : Nonempty n := by
    by_contra h
    haveI : IsEmpty n := not_nonempty_iff.1 h
    exact hA (Subsingleton.elim _ _)
  let T := A.toEuclideanLin
  have hT : T.IsPositive := isPositive_toEuclideanLin_iff.2 hspd.posSemidef
  have hspec : spectrum ℝ A =
      Set.range (fun i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) ↦ T.singularValues i) := by
    rw [← spectrum_toLpLin (A := A) 2]
    exact spectrum_eq_range_singularValues_of_isPositive T hT
  have hdim : 0 < Module.finrank ℝ (EuclideanSpace ℝ n) := by
    simpa only [finrank_euclideanSpace] using Fintype.card_pos (α := n)
  have hinj : Function.Injective T := by
    exact (Module.End.isUnit_iff T).1
      (hspd.isUnit.map
        (Matrix.toLinAlgEquiv (EuclideanSpace.basisFun n ℝ).toBasis).toMonoidHom) |>.1
  have hrank : Module.finrank ℝ T.range = Module.finrank ℝ (EuclideanSpace ℝ n) :=
    LinearMap.finrank_range_of_inj hinj
  have hmax : IsGreatest (spectrum ℝ A) (T.singularValues 0) := by
    rw [hspec]
    refine ⟨⟨⟨0, hdim⟩, rfl⟩, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact T.singularValues_antitone (Nat.zero_le i)
  have hmin : IsLeast (spectrum ℝ A)
      (T.singularValues (Module.finrank ℝ T.range - 1)) := by
    rw [hspec, hrank]
    refine ⟨⟨⟨Module.finrank ℝ (EuclideanSpace ℝ n) - 1, Nat.sub_lt hdim (by decide)⟩, rfl⟩, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact T.singularValues_antitone (Nat.le_sub_one_of_lt i.isLt)
  rw [hmax.csSup_eq, hmin.csInf_eq]
  rfl

/-- For a positive-definite real matrix, `Matrix.posDefConditionNumber` is the
ratio of the largest and smallest spectral values. -/
theorem posDefConditionNumber_eq_spectralExtrema [Nonempty n] (A : Matrix n n ℝ)
    (hA : A.PosDef) :
    A.posDefConditionNumber hA = sSup (spectrum ℝ A) / sInf (spectrum ℝ A) := by
  exact A.conditionNumber_eq_spectralExtrema_of_posDef hA.isUnit.ne_zero hA

end Matrix
