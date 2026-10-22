/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_24.BTTB
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_24.HTTB

public section

/- Definition 5.24. A block Toeplitz with Toeplitz blocks matrix is represented
by the canonical owner `Matrix.bttb`; `Matrix.bttb_apply` gives the entrywise
formula, `Matrix.bttb_block_eq_toeplitzByDiag` recovers the displayed Toeplitz
block structure with block `(j, l)` depending only on `j - l`, and the thin
compatibility bridge `Matrix.httb` remains available for existing consumers. -/
#check Matrix.bttb
#check Matrix.httb
#check Matrix.bttb_apply
#check Matrix.toeplitzByDiag
#check Matrix.bttb_block_eq_toeplitzByDiag
