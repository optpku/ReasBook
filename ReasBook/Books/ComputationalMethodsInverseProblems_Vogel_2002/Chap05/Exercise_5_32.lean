/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_19
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_27.BCCB

public section

/-!
Exercise 5.32. Statement-stage blocker.

The source item asks for the Section 5.3.4 numerical study to be rerun after
replacing the level-1 and level-2 block circulant preconditioners by block
cosine preconditioners.

The current repository snapshot does not yet provide checked Lean owners for
those level-1/level-2 block cosine preconditioners themselves, and it also does
not provide a checked owner for the full §5.3.4 benchmark setup or its
numerical outputs. A source-faithful formalization of the exercise would have to
state that specific benchmark surface rather than introduce a guessed
preconditioner wrapper or a fake theorem about repeated computations.

The `#check` entries below therefore record only the verified backend owners
already present in the repository that a later faithful formalization should
reuse: the explicit cosine transform matrix from Exercise 5.19, its orthogonal
group membership theorem, and the Chapter 5 BCCB owner `Matrix.bccb` for the
block-circulant side of the earlier comparison.
-/

/- Exercise 5.32. Main labeled source-facing entry for the current blocked-item
state: the repository exposes the cosine-matrix backend and the BCCB backend,
but not yet the source-level block cosine preconditioners or the §5.3.4
benchmark surface needed to state the exercise itself. -/
#check cosineMatrix

#check cosineMatrix_mem_orthogonalGroup

#check Matrix.bccb
