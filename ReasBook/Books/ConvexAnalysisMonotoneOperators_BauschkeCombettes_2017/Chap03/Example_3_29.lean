/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped InnerProductSpace
open ContinuousLinearMap

variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

private noncomputable abbrev normalEquationInverseCompAdjoint (T : 𝓗 →L[ℝ] 𝓚) :
    𝓚 →L[ℝ] 𝓗 :=
  (T.adjoint ∘L T).inverse ∘L T.adjoint

private lemma normalOperator_ker_eq_bot (T : 𝓗 →L[ℝ] 𝓚)
    [Fact (IsUnit (T.adjoint ∘L T))] :
    (T.adjoint ∘L T).ker = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 ?_
  intro x hx
  have hcancel :
      (T.adjoint ∘L T).inverse ((T.adjoint ∘L T) x) = x := by
    simpa [← ringInverse_eq_inverse, one_def] using
      congrArg (fun A : 𝓗 →L[ℝ] 𝓗 ↦ A x)
        (Ring.inverse_mul_cancel (T.adjoint ∘L T) (Fact.out : IsUnit (T.adjoint ∘L T)))
  calc
    x = (T.adjoint ∘L T).inverse ((T.adjoint ∘L T) x) := by simpa using hcancel.symm
    _ = (T.adjoint ∘L T).inverse 0 := by
      exact congrArg ((T.adjoint ∘L T).inverse) hx
    _ = 0 := by simp

private lemma ker_eq_bot_of_isUnit_normalOperator (T : 𝓗 →L[ℝ] 𝓚)
    [Fact (IsUnit (T.adjoint ∘L T))] :
    T.ker = ⊥ := by
  rw [← ker_adjoint_comp_self]
  exact normalOperator_ker_eq_bot T

private lemma normalEquationPseudoinverse_mem_orthogonalKer (T : 𝓗 →L[ℝ] 𝓚)
    [Fact (IsUnit (T.adjoint ∘L T))] (y : 𝓚) :
    normalEquationInverseCompAdjoint T y ∈ T.kerᗮ := by
  rw [ker_eq_bot_of_isUnit_normalOperator T]
  simp

-- Proof sketch: invertibility of `T†T` forces `ker T = ⊥`, so the orthogonality condition in
-- `IsMoorePenroseInverse` is automatic; the normal equation is the cancellation identity
-- `(T†T) (T†T)⁻¹ T† = T†`.
/-- Example 3.29: if `T†T` is invertible, then the operator `(T†T)⁻¹ T†` is the Moore-Penrose
inverse of `T`. -/
theorem normalEquationPseudoinverse_isMoorePenroseInverse
    (T : 𝓗 →L[ℝ] 𝓚) [Fact (IsUnit (T.adjoint ∘L T))] :
    IsMoorePenroseInverse T ((T.adjoint ∘L T).inverse ∘L T.adjoint) := by
  refine ⟨?_, ?_⟩
  · exact normalEquationPseudoinverse_mem_orthogonalKer T
  · intro y
    have hcomp :
        (T.adjoint ∘L T) ∘L normalEquationInverseCompAdjoint T = T.adjoint := by
      simpa [normalEquationInverseCompAdjoint, comp_assoc, ← ringInverse_eq_inverse, one_def]
        using
          congrArg (fun A : 𝓗 →L[ℝ] 𝓗 ↦ A ∘L T.adjoint)
            (Ring.mul_inverse_cancel (T.adjoint ∘L T) (Fact.out : IsUnit (T.adjoint ∘L T)))
    simpa using congrArg (fun A : 𝓚 →L[ℝ] 𝓗 ↦ A y) hcomp

/-- The normal-equation pseudoinverse can be used through typeclass search when `T†T` is
invertible. -/
instance (T : 𝓗 →L[ℝ] 𝓚) [Fact (IsUnit (T.adjoint ∘L T))] :
    IsMoorePenroseInverse T ((T.adjoint ∘L T).inverse ∘L T.adjoint) :=
  normalEquationPseudoinverse_isMoorePenroseInverse T
