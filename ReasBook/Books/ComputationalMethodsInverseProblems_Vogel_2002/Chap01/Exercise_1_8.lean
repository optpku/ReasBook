/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_1

public section

/-!
Exercise 1.8. Source-facing blocker.

The source asks for an explicit vector `z` for which equality holds in the TSVD
source-condition estimate `(1.26)`. In the current repository snapshot,
equation `(1.26)` is formalized by
`tsvdSourceCondition_truncationErrorSq_le`, whose scalar input uses the local
TSVD convention `SpectralFilter.tsvd α λ = if α ≤ λ then 1 else 0`. Under that
convention, the scalar coefficient in the proof of `(1.26)` is either `0` or
`σ ^ 2 < α`, so the present owner does not expose the requested nontrivial
equality-attaining witness.

The item therefore remains blocked until the inherited source setup or equality
convention is made explicit enough to state the exercise faithfully.
-/

/- Exercise 1.8. Main labeled source-facing blocker entry.

The current canonical repository owner for `(1.26)` is
`tsvdSourceCondition_truncationErrorSq_le`, together with the scalar coefficient
lemma `tsvdBiasCoeff_sq_mul_le_alpha`. The source-facing task is stronger: it
asks for a concrete equality witness `z`. Since the current local TSVD
convention does not yet support that equality case faithfully, this file records
the exact canonical owners that the eventual repair should reuse instead of
keeping a false local theorem.
-/
#check SpectralFilter.tsvd
#check tsvdBiasCoeff_sq_mul_le_alpha
#check tsvdSourceCondition_truncationErrorSq_le
