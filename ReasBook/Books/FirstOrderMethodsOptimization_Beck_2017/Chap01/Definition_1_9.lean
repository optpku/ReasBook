/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable (s : Set E) (Q : AffineSubspace ℝ E)

/- Definition 1.9 (1): an affine subset of a real vector space is represented in mathlib by an
`AffineSubspace ℝ E`. -/
#check AffineSubspace ℝ E

/- Definition 1.9 (2): the affine hull of a set `s` is the canonical affine subspace
`affineSpan ℝ s`. Since its codomain is `AffineSubspace ℝ E`, the affine hull is itself affine. -/
#check (affineSpan ℝ : Set E → AffineSubspace ℝ E)

/- Definition 1.9 (3): every set is contained in its affine hull, via the canonical theorem
`subset_affineSpan`. -/
#check (subset_affineSpan ℝ s : s ⊆ affineSpan ℝ s)

/- Definition 1.9 (4): the affine hull is the smallest affine subspace containing `s`; equivalently,
`affineSpan ℝ s ≤ Q` if and only if `s ⊆ Q`. -/
#check (affineSpan_le : affineSpan ℝ s ≤ Q ↔ s ⊆ Q)

/- Definition 1.9 (5): the affine hull is the intersection of all affine subspaces containing the
given set, as expressed by `AffineSubspace.affineSpan_eq_sInf`. -/
#check (AffineSubspace.affineSpan_eq_sInf ℝ E s :
  affineSpan ℝ s = sInf {Q : AffineSubspace ℝ E | s ⊆ Q})

end
