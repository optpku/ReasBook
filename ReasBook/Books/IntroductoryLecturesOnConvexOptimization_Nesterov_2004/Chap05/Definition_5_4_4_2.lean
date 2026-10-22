/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped RealSymmetricMatrixSpace

/- Definition 5.4.4.2 is a source-facing owner item in the symmetric-matrix Frobenius domain.

Layer targeted by this refinement:
- source-facing: the Frobenius pairing and norm on the chapter owner `𝕊^n`.

Primary domain:
- the Frobenius pairing and Frobenius norm on real square matrices and their restriction to
  `𝕊^n`.

Sampled owner-style declarations:
- mathlib `Matrix.trace`
- mathlib `norm_eq_sqrt_real_inner`
- mathlib `real_inner_self_nonneg`
- mathlib `Matrix.toMatrixInnerProductSpace`
- mathlib `Submodule.innerProductSpace`
- mathlib `Submodule.coe_norm`
- Chapter 5 `selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)` from Definition 5.4.4.1
- the source-facing notation `𝕊^n`

Best owner abstraction:
- source-facing: the Frobenius inner product and norm on symmetric matrices;
- core/canonical: the inherited real inner-product-space structure on `𝕊^n`;
- bridge/view: the coercion `↥(𝕊^n) → Matrix (Fin n) (Fin n) ℝ` and the trace identity
  `trace (Y Xᵀ) = trace (Xᵀ Y)`.

Primitive data:
- `n : ℕ`
- `X Y : 𝕊^n`

Derived API:
- the restricted pairing owner `RealSymmetricMatrixSpace.frobeniusInner`
- the source-facing notation `⟪X, Y⟫_F`
- the inherited Frobenius inner-product structure on `𝕊^n`
- the bridge theorem `‖X‖ = Real.sqrt ⟪X, X⟫_F`
- the ambient multiplication bridges `RealSymmetricMatrixSpace.sandwich X Y` and
  `RealSymmetricMatrixSpace.cube X` on `𝕊^n`

Source/core/bridge triage:
- source-facing: the Frobenius inner product and norm on `𝕊^n`;
- core/canonical: the inherited real inner product on `𝕊^n`;
- bridge/view: the coercion from `𝕊^n` to matrices.

This file keeps the Chapter 5 owner `⟪·, ·⟫_F` and the inherited Frobenius normed-space
structure on `𝕊^n`, while exposing only the thin ambient-multiplication bridges actually needed by
the downstream Chapter 5 semidefinite files.
-/

noncomputable section

namespace RealSymmetricMatrixSpace

private instance ambientMatrixNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) :=
  toMatrixNormedAddCommGroup (1 : Matrix (Fin n) (Fin n) ℝ) PosDef.one

private instance ambientMatrixInnerProductSpace {n : ℕ} :
    InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  toMatrixInnerProductSpace (1 : Matrix (Fin n) (Fin n) ℝ) PosDef.one.posSemidef

/-- The Chapter 5 carrier `𝕊^n` inherits the ambient Frobenius normed-group structure. -/
noncomputable instance symmetricMatrixNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (𝕊^n) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := ambientMatrixNormedAddCommGroup
  exact Submodule.normedAddCommGroup (𝕊^n)

/-- The Chapter 5 carrier `𝕊^n` inherits the ambient Frobenius normed-space structure. -/
noncomputable instance symmetricMatrixNormedSpace {n : ℕ} :
    NormedSpace ℝ (𝕊^n) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := ambientMatrixNormedAddCommGroup
  exact Submodule.normedSpace (𝕊^n)

/-- The Chapter 5 carrier `𝕊^n` inherits the ambient Frobenius inner-product structure. -/
noncomputable instance symmetricMatrixInnerProductSpace {n : ℕ} : InnerProductSpace ℝ (𝕊^n) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := ambientMatrixNormedAddCommGroup
  letI : InnerProductSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := ambientMatrixInnerProductSpace
  exact Submodule.innerProductSpace (𝕊^n)

/-- Definition 5.4.4.2: on `𝕊^n`, the Frobenius inner product is the inherited real inner product,
written on the theorem surface in Frobenius notation. -/
abbrev frobeniusInner {n : ℕ} (X Y : 𝕊^n) : ℝ :=
  inner ℝ X Y

scoped[RealSymmetricMatrixSpace] notation "⟪" X ", " Y "⟫_F" =>
  RealSymmetricMatrixSpace.frobeniusInner X Y

/-- Expanding the Frobenius pairing on `𝕊^n` gives the ambient trace formula. -/
theorem frobeniusInner_def {n : ℕ} (X Y : 𝕊^n) :
    ⟪X, Y⟫_F =
      Matrix.trace
        ((X : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Y : Matrix (Fin n) (Fin n) ℝ)) := by
  change inner ℝ X Y =
    Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Y : Matrix (Fin n) (Fin n) ℝ))
  change Matrix.trace ((Y : Matrix (Fin n) (Fin n) ℝ) * 1 * (X : Matrix (Fin n) (Fin n) ℝ)ᵀ) =
    Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Y : Matrix (Fin n) (Fin n) ℝ))
  simpa using
    (Matrix.trace_mul_comm (Y : Matrix (Fin n) (Fin n) ℝ)
      ((X : Matrix (Fin n) (Fin n) ℝ)ᵀ))

/-- The symmetric-matrix carrier `𝕊^n` inherits the ambient uniform additive-group structure. -/
instance symmetricMatrixIsUniformAddGroup {n : ℕ} : IsUniformAddGroup (𝕊^n) := by
  refine IsUniformAddGroup.mk' ?_ ?_
  · exact
      ((uniformContinuous_subtype_val.comp uniformContinuous_fst).add
        (uniformContinuous_subtype_val.comp uniformContinuous_snd)).subtype_mk
        fun p ↦ (𝕊^n).add_mem p.1.2 p.2.2
  · exact (uniformContinuous_subtype_val.neg).subtype_mk fun X ↦ (𝕊^n).neg_mem X.2

/-- In Frobenius scope, the norm on `𝕊^n` is the ambient matrix Frobenius norm. -/
@[simp] theorem norm_coe {n : ℕ} (X : 𝕊^n) :
    ‖X‖ = ‖(X : Matrix (Fin n) (Fin n) ℝ)‖ := by
  exact Submodule.coe_norm X

/-- The induced inner product on `𝕊^n` is exactly the Chapter 5 Frobenius pairing. -/
@[simp] theorem inner_eq_frobeniusInner {n : ℕ} (X Y : 𝕊^n) :
    inner ℝ X Y = ⟪X, Y⟫_F :=
  rfl

-- Proof sketch: rewrite the inherited norm by the real inner-product-space identity
-- `‖X‖ = Real.sqrt (inner ℝ X X)` and then use `inner_eq_frobeniusInner`.
/-- The Frobenius norm on `𝕊^n` is the square root of the Frobenius self-pairing. -/
theorem norm_eq_sqrt_frobeniusInner {n : ℕ} (X : 𝕊^n) :
    ‖X‖ = Real.sqrt (⟪X, X⟫_F) := by
  change ‖X‖ = Real.sqrt (inner ℝ X X)
  exact norm_eq_sqrt_real_inner X

-- Proof sketch: combine the positivity of `inner ℝ X X` in the inherited inner-product space
-- with `inner_eq_frobeniusInner`.
/-- The Frobenius self-pairing on `𝕊^n` is nonnegative. -/
theorem frobeniusInner_self_nonneg {n : ℕ} (X : 𝕊^n) :
    0 ≤ ⟪X, X⟫_F := by
  change 0 ≤ inner ℝ X X
  exact real_inner_self_nonneg

private theorem sandwich_mem {n : ℕ} (X Y : 𝕊^n) :
    ((X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ) *
        (X : Matrix (Fin n) (Fin n) ℝ)) ∈ 𝕊^n := by
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  rw [Matrix.IsSymm]
  simp [Matrix.transpose_mul, Matrix.mul_assoc, (isSymm X).eq, (isSymm Y).eq]

/-- The ambient sandwich product `XYX`, viewed back in the symmetric carrier `𝕊^n`. -/
def sandwich {n : ℕ} (X Y : 𝕊^n) : 𝕊^n :=
  ⟨(X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ) *
      (X : Matrix (Fin n) (Fin n) ℝ), sandwich_mem X Y⟩

@[simp] theorem coe_sandwich {n : ℕ} (X Y : 𝕊^n) :
    ((RealSymmetricMatrixSpace.sandwich X Y : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ) =
      (X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ) *
        (X : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

private theorem cube_mem {n : ℕ} (X : 𝕊^n) :
    (((X : Matrix (Fin n) (Fin n) ℝ) ^ (3 : ℕ)) : Matrix (Fin n) (Fin n) ℝ) ∈ 𝕊^n := by
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa using (isSymm X).pow (3 : ℕ)

/-- The ambient cube `X^3`, viewed back in the symmetric carrier `𝕊^n`. -/
def cube {n : ℕ} (X : 𝕊^n) : 𝕊^n :=
  ⟨(X : Matrix (Fin n) (Fin n) ℝ) ^ (3 : ℕ), cube_mem X⟩

@[simp] theorem coe_cube {n : ℕ} (X : 𝕊^n) :
    ((RealSymmetricMatrixSpace.cube X : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ) =
      (X : Matrix (Fin n) (Fin n) ℝ) ^ (3 : ℕ) :=
  rfl

/-- The Frobenius symmetric-matrix carrier `𝕊^n` is complete. -/
noncomputable instance symmetricMatrixCompleteSpace {n : ℕ} : CompleteSpace (𝕊^n) := by
  letI : IsUniformAddGroup (𝕊^n) := symmetricMatrixIsUniformAddGroup
  exact FiniteDimensional.complete ℝ (𝕊^n)

end RealSymmetricMatrixSpace
