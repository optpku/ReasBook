/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {ι : Type*}
variable {α : Type*} [Zero α]

/-
Definition 6.12 is `source-facing` in the Chapter 6 sparse-optimization API.

Domain sampling:
- `Function.support` from mathlib is the `core/canonical` owner of the nonzero-coordinate set of a
  vector-valued function;
- `Set.encard` is the canonical cardinality owner for “at most `s` nonzero coordinates,” because
  it does not collapse infinite support to the junk value `0`;
- on finite index types, mathlib’s `hammingNorm` is the canonical cardinality bridge for the same
  notion, so the finite-dimensional `ℝ^n` surface should be derived from the support owner rather
  than rebuilt separately;
- Chapter 6 specializes this owner to `Fin n → ℝ`, but the source-facing notion itself is the
  support-cardinality condition rather than the concrete coordinate model;
- later Chapter 6 files `Lemma_6_71` and `Example_6_72` should recover the textbook `ℝ^n`
  presentation by specialization of this owner and its notation, not by a parallel local copy.

Primitive data:
- `source-facing`: only the sparsity level `s` and the vector `x`;
- `derived API`: the membership characterization, which is definitional.

Layer triage:
- `source-facing`: the sparse-vector set `sSparseVectors`;
- `core/canonical`: the pair `Function.support` and `Set.encard`;
- `bridge/view`: the notation `C_[s]` together with the finite-index `hammingNorm` bridge, whose
  specialization to `Fin n → ℝ` recovers the textbook `ℝ^n` presentation.

There is no higher project owner for this textbook set beyond the support-cardinality condition
itself, so the public owner here should remain the source-facing set `sSparseVectors`. -/

/-- Definition 6.12: the set `C_s = {x | ‖x‖₀ ≤ s}` of `s`-sparse vectors, defined as the
functions with at most `s` nonzero coordinates. The textbook `ℝ^n` formulation is the
specialization `ι = Fin n`, `α = ℝ`, while the canonical Lean owner itself only needs a codomain
with zero and uses `Set.encard` so the support count stays faithful even on infinite index types. -/
def sSparseVectors (s : ℕ) : Set (ι → α) :=
  {x | (Function.support x).encard ≤ s}

notation "C_[" s "]" => sSparseVectors s

-- Proof sketch: unfold `sSparseVectors`; membership in `C_[s]` is definitionally the statement
-- that the support set `{i | x i ≠ 0}` has cardinality at most `s`.
/-- A vector belongs to `C_s` exactly when it has at most `s` nonzero coordinates. -/
@[simp]
theorem mem_sSparseVectors_iff (s : ℕ) (x : ι → α) :
    x ∈ C_[s] ↔ (Function.support x).encard ≤ s :=
  Iff.rfl

section Finite

variable [Fintype ι] [DecidableEq α]

-- Proof sketch: on a finite index type, `Set.encard` agrees with `Finset.card`, and
-- `Function.support x` becomes the same finite set counted by mathlib's `hammingNorm x`.
/-- On a finite index type, the support cardinality used in `C_s` is exactly `hammingNorm`. -/
theorem support_encard_eq_hammingNorm (x : ι → α) :
    (Function.support x).encard = hammingNorm x := by
  classical
  rw [Set.encard_eq_coe_toFinset_card, hammingNorm]
  congr
  ext i
  simp [Function.support]

-- Proof sketch: combine the definitional membership theorem with
-- `support_encard_eq_hammingNorm`.
/-- Over a finite index type, `x ∈ C_s` exactly when its Hamming weight is at most `s`. -/
@[simp]
theorem mem_sSparseVectors_iff_hammingNorm_le (s : ℕ) (x : ι → α) :
    x ∈ C_[s] ↔ hammingNorm x ≤ s := by
  rw [mem_sSparseVectors_iff, support_encard_eq_hammingNorm]
  simp

end Finite

end
