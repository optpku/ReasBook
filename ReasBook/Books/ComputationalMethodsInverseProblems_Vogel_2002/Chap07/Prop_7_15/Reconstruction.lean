/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.SingularSystem
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

noncomputable section

open scoped BigOperators

namespace TsvdEstimation

universe u v

section

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A reconstruction family `R n m` is the Chapter 7 TSVD truncation family
when it is the partial singular-system sum over the first `m` modes of `S n`.
This packages the source truncation-index surface without introducing a local
wrapper structure. -/
@[expose] def IsTsvdReconstructionFamily
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (R : ℕ → ℕ → F →L[ℝ] H) : Prop :=
  ∀ n m g,
    R n m g =
      Finset.sum (Finset.range m) fun i ↦
        (((1 / (S n).singularValue ((S n).natIndex (h_length n) i)) *
            inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) g) •
          ((S n).rightBasis ((S n).natIndex (h_length n) i) : H))

/-- Specification lemma for `IsTsvdReconstructionFamily`. -/
@[simp] theorem isTsvdReconstructionFamily_iff
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (R : ℕ → ℕ → F →L[ℝ] H) :
    IsTsvdReconstructionFamily K S h_length R ↔
      ∀ n m g,
        R n m g =
          Finset.sum (Finset.range m) fun i ↦
            (((1 / (S n).singularValue ((S n).natIndex (h_length n) i)) *
                inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) g) •
              ((S n).rightBasis ((S n).natIndex (h_length n) i) : H)) := by
  rfl

end

end TsvdEstimation
