/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProduct InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem ker_le_adjoint_ker_of_isMonotone
    (A : H →L[ℝ] H) (hA : A.toLinearMap.IsMonotone) :
    A.ker ≤ A†.ker := by
  rw [← A.orthogonal_range]
  intro x hx
  refine (Submodule.mem_orthogonal' A.range x).2 ?_
  rintro _ ⟨y, rfl⟩
  by_contra hxy
  have hx0 : A x = 0 := LinearMap.mem_ker.mp hx
  have hxy' : ⟪A y, x⟫_ℝ ≠ 0 := by
    simpa [real_inner_comm] using hxy
  let t : ℝ := -(⟪A y, y⟫_ℝ + 1) / ⟪A y, x⟫_ℝ
  have ht : 0 ≤ ⟪A y, y⟫_ℝ + t * ⟪A y, x⟫_ℝ := by
    have := hA (y + t • x)
    simpa [t, hx0, inner_add_right, inner_smul_right] using this
  have hEq : ⟪A y, y⟫_ℝ + t * ⟪A y, x⟫_ℝ = -1 := by
    dsimp [t]
    field_simp [hxy']
    ring_nf
  linarith

-- Proof sketch: if `x ∈ ker A`, then monotonicity applied to `α • x + y` shows that `x` is
-- orthogonal to every vector in `range A`, so `x ∈ A†.ker` by the orthogonal-range
-- identity. The same argument applies to `A.adjoint` because `⟪A.adjoint x, x⟫_ℝ = ⟪A x, x⟫_ℝ`,
-- giving the reverse inclusion, and the closure-of-range equality then follows from the
-- orthogonal-kernel and orthogonal-range identities.
/-- Proposition 20.17: if a bounded linear operator on a real Hilbert space is monotone, then its
kernel agrees with the kernel of its adjoint, and the closures of the ranges of the operator and
of its adjoint coincide. -/
theorem ker_eq_adjoint_ker_and_closure_range_eq_closure_adjoint_range_of_isMonotone
    (A : H →L[ℝ] H) (hA : A.toLinearMap.IsMonotone) :
    A.ker = A†.ker ∧
      A.range.topologicalClosure = A†.range.topologicalClosure := by
  have hker : A.ker = A†.ker := by
    refine le_antisymm ?_ ?_
    · exact ker_le_adjoint_ker_of_isMonotone A hA
    · intro x hx
      have hAadj : A†.toLinearMap.IsMonotone :=
        (isMonotone_iff_adjoint_isMonotone A).mp hA
      simpa [adjoint_adjoint] using ker_le_adjoint_ker_of_isMonotone (A†) hAadj hx
  have hker_orthogonal :=
    congrArg (fun K : Submodule ℝ H ↦ Kᗮ) hker
  refine ⟨hker, ?_⟩
  simpa [ContinuousLinearMap.orthogonal_ker, adjoint_adjoint] using hker_orthogonal.symm

end ContinuousLinearMap
