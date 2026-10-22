/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.LinearAlgebra.Matrix.Hadamard

public section

/- Definition 5.5. For vectors, the book's componentwise multiplication and
division are the canonical pointwise operations on `Fin n → ℂ`: `Pi.mul_apply`
gives `(f * g) i = f i * g i`, and `Pi.div_apply` gives `(f / g) i = f i / g i`.
For two-dimensional arrays represented as `Matrix (Fin n_x) (Fin n_y) ℂ`,
componentwise multiplication is `Matrix.hadamard` (notation `⊙`), with
`Matrix.hadamard_apply` giving `(A ⊙ B) i j = A i j * B i j`. Componentwise
division is still the inherited pointwise `/` on the nested function type
`Fin n_x → Fin n_y → ℂ`, so it is obtained by applying `Pi.div_apply` in the
row and column coordinates. The source side condition `g i ≠ 0` remains a
use-condition for the total division operation on `ℂ`. -/
#check Pi.mul_apply
#check Pi.div_apply
#check Matrix.hadamard
#check Matrix.hadamard_apply
