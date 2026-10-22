/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Remark_5_2_1.Split

public section

/-!
Exercise 5.8.

The source derives the FFT multiplication-count recurrence `(5.34)` and its closed form `(5.35)`
from the radix-2 split identities of `Book.Ch5.Remark_5_2_1.Split`.

The current repository snapshot exposes the split formulas for
`Matrix.FFT.unnormalizedDft`, but it still does not provide a checked owner for
an actual radix-2 FFT algorithm together with its multiplication count.
Replacing the exercise by an ad hoc recursively defined cost function would
change the mathematics from a statement about the FFT itself to a statement
about unrelated standalone data.

This file therefore remains a labeled blocker/anchor entry until the repository
contains a checked FFT cost owner that Exercise `5.8` can reuse directly.
-/

/- Exercise 5.8. Main labeled source-facing entry for the current blocked-item
state: the exercise asks for multiplication-count formulas for the radix-2 FFT,
but the current repository only provides the algebraic split identities and not
a checked FFT cost owner. The `#check` anchors below record the verified split
API that a later faithful cost formalization should reuse.
-/

#check Matrix.FFT.unnormalizedDft
#check Matrix.FFT.firstHalf
#check Matrix.FFT.secondHalf
#check Matrix.FFT.evenPart
#check Matrix.FFT.oddPart
#check Matrix.FFT.splitFirstHalf
#check Matrix.FFT.splitSecondHalf
#check Matrix.FFT.firstHalf_unnormalizedDft_eq
#check Matrix.FFT.secondHalf_unnormalizedDft_eq
