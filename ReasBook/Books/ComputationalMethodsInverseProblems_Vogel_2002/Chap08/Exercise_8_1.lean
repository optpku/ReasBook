/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Remark_5_32.NeumannLaplacian
public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

open scoped Matrix

namespace VariationalRegularization

/-!
Exercise 8.1.

The source asks for two claims about the Chapter 8 matrix `L(f)` from `(8.17)`:
that it is positive semidefinite, and that its null space can be identified
explicitly.

In the current repository snapshot, there is still no checked Chapter 8 owner
for that exact matrix and no checked bridge identifying `(8.17)` with the
verified two-dimensional homogeneous-Neumann owner already available in Chapter
5. This target therefore must remain a source-facing blocker/check-only surface
rather than asserting the exercise on an unverified identification, but its
verified backend anchors should cite the Chapter 5 grid operator directly.
-/

/- Exercise 8.1. Main labeled source-facing blocker entry.

Until the repository exposes a checked Chapter 8 owner for `(8.17)` or a
checked equality identifying that formula with `Matrix.neumannLaplacian`,
the safe statement-stage surface is to keep the source-shaped two-dimensional
grid matrix binder
`L : (Fin n_y × Fin n_x → ℝ) → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ`
explicit and record only the proposition surfaces of the two clauses, together
with the verified Chapter 5 homogeneous-Neumann backend anchors that a later
faithful repair should reuse. -/

/- Exercise 8.1 (1). Source-facing proposition surface for the claim that the
Chapter 8 matrix `L(f)` from `(8.17)` is positive semidefinite. -/
#check
  fun {n_x n_y : ℕ}
    (L :
      (Fin n_y × Fin n_x → ℝ) →
        Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (f : Fin n_y × Fin n_x → ℝ) ↦
    Matrix.PosSemidef (L f)

/- Exercise 8.1 (2). Source-facing proposition surface for the claim that the
null space of the Chapter 8 matrix `L(f)` consists of the constant vectors. -/
#check
  fun {n_x n_y : ℕ}
    (L :
      (Fin n_y × Fin n_x → ℝ) →
        Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (f x : Fin n_y × Fin n_x → ℝ) ↦
    Matrix.mulVec (L f) x = 0 ↔ ∃ c : ℝ, x = fun _ ↦ c

/- Verified Chapter 5 backend anchors for the surviving blocker surface. These
are not checked identifications of the source matrix `(8.17)` itself. -/
#check Matrix.neumannLaplacian
#check Matrix.neumannLaplacian_posSemidef
#check Matrix.neumannLaplacian_mulVecEqZero_iffExistsConst
#check Matrix.PosSemidef

end VariationalRegularization
