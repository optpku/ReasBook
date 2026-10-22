/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Notation_5_2.Coordinates

public section

open scoped Complex.FiniteDimensional

/- Notation 5.2-extra-1 (1). The textbook finite complex vector space `ℂ^n`
is represented by the scoped notation `ℂ^[n]`, that is,
`EuclideanSpace ℂ (Fin n)`. The Euclidean inner product and induced norm in
equation `(5.16)` are the canonical mathlib formulas checked below. The
textbook component indices `0, ..., n - 1` are realized by `Fin n`.
-/
section

variable (n : ℕ)

#check ℂ^[n]

end

#check EuclideanSpace.inner_eq_star_dotProduct
#check EuclideanSpace.norm_eq

/- Notation 5.2-extra-1 (2). Complex conjugation is the canonical star
operation on `ℂ`; its ring endomorphism is `starRingEnd ℂ`. The textbook
magnitude `|z| = sqrt (α^2 + β^2)` is Lean's existing norm notation on `ℂ`,
so no new magnitude wrapper is introduced here.
-/
#check (norm : ℂ → ℝ)
#check starRingEnd ℂ

/- Notation 5.2-extra-1 (3). A complex-valued `n_x × n_y` array is represented
by the scoped notation `ℂ^[n_x, n_y]`, that is,
`Matrix (Fin n_x) (Fin n_y) ℂ`. The indices `i = 0, ..., n_x - 1` and
`j = 0, ..., n_y - 1` are realized by `Fin n_x` and `Fin n_y`, and the entry
`f_{ij}` is written in Lean as `f i j`.
-/
section

variable (n_x n_y : ℕ)

#check ℂ^[n_x, n_y]

end
