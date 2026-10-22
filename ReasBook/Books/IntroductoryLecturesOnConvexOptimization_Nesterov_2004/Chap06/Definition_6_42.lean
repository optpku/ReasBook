/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

/- Definition 6.42 lies in the chapter's symmetric-matrix trace-power/Frobenius domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 5 `RealSymmetricMatrixSpace.frobeniusInner` in `Definition_5_4_4_2`, the established
  Frobenius owner on `𝕊^n`;
- mathlib `Matrix.trace`, the canonical ambient owner for `X ↦ Trace (X^k)`;
- `iteratedFDeriv` in `Theorem_6_9`, the canonical Hessian owner for the trace-power map.

Best owner abstraction:
- source-facing: the textbook quantity `π_k(X)` on the canonical symmetric-matrix carrier `𝕊^n`,
  exposed below as `RealSymmetricMatrixSpace.powerTrace` with Lean surface `π[k] X`;
- core/canonical: `fun X : Matrix (Fin n) (Fin n) ℝ ↦ Matrix.trace (X ^ k)`;
- bridge/view: coercion from `𝕊^n` to matrices together with the Frobenius identity
  `π_k(X) = ⟪1, X^k⟫_F`.

Primitive data:
- `k : ℕ`
- `X : 𝕊^n`

Derived API:
- the restricted symmetric-matrix owner `RealSymmetricMatrixSpace.powerTrace`
- the Lean surface notation `π[k] X`
- the canonical symmetric-matrix power notation `X ^ k`
- the textbook Frobenius identity below.

Source/core/bridge triage:
- source-facing: `RealSymmetricMatrixSpace.powerTrace`, written `π[k] X`;
- core/canonical: `Matrix.trace ((·) ^ k)`;
- bridge/view: the `Pow (𝕊^n) ℕ` instance and the Frobenius-pairing formula.

This refinement keeps the source-facing symmetric-matrix owner `π[k] X`, but defines it directly by
the canonical ambient trace expression instead of routing it through a parallel ambient wrapper.
-/

namespace RealSymmetricMatrixSpace

/-- The canonical power notation on `𝕊^n` is induced by ambient matrix powers. -/
instance {n : ℕ} : Pow (𝕊^n) ℕ where
  pow X k :=
    ⟨(X : Matrix (Fin n) (Fin n) ℝ) ^ k, by
      rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
      simpa using (isSymm X).pow k⟩

@[simp] theorem coe_pow {n : ℕ} (X : 𝕊^n) (k : ℕ) :
    ((X ^ k : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ) =
      (X : Matrix (Fin n) (Fin n) ℝ) ^ k :=
  rfl

/-- Definition 6.42: on `𝕊^n`, the textbook quantity `π_k(X)` is the ambient trace-power
expression `Trace (X^k)`. -/
abbrev powerTrace (k : ℕ) (X : 𝕊^n) : ℝ :=
  Matrix.trace (((X ^ k : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ))

/- Lean surface notation for the textbook quantity `π_k(X)` on `𝕊^n`. -/
scoped[RealSymmetricMatrixSpace] notation "π[" k "]" => RealSymmetricMatrixSpace.powerTrace k

/-- Expanding `π[k] X` recovers the trace of the `k`-th ambient matrix power. -/
theorem powerTrace_def (k : ℕ) (X : 𝕊^n) :
    π[k] X = Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ) ^ k) := by
  rw [powerTrace, coe_pow]

end RealSymmetricMatrixSpace

/-- Definition 6.42, source-facing bridge: on `𝕊^n`, the ambient trace-power expression agrees
with the textbook Frobenius-pairing formula `π_k(X) = ⟪1, X^k⟫_F`. -/
theorem powerTrace_eq_frobeniusInner_one
    (k : ℕ) (X : 𝕊^n) :
    π[k] X = ⟪(1 : 𝕊^n), X ^ k⟫_F := by
  rw [RealSymmetricMatrixSpace.powerTrace_def, frobeniusInner_def]
  simp
