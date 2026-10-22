/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open LinearMap
open scoped LinearMap.BilinForm.BInducedNorm

/- Proposition 5.0.21 lies in the bilinear-form / induced-norm duality domain.

Sampled owner-style declarations:
* `LinearMap.BilinForm.primalSeminorm` in `Chap04/Definition_4_3_4`, the canonical primal
  seminorm induced by a symmetric positive-definite bilinear form;
* `LinearMap.BilinForm.dualNorm` in `Chap04/Definition_4_3_4`, the corresponding dual norm on
  `Module.Dual ℝ E`;
* `Seminorm.inner_le_dualNorm_mul` in `Chap02/Definition_2_5`, the owner-level dual-pairing
  estimate for a separated seminorm and its dual norm;
* the notation layer `‖·‖[B]` / `‖·‖[B,*]` in `Chap04/Definition_4_3_4`, together with the direct
  owner call `B.dualNorm Fact.out` on `Module.Dual ℝ E`;
* `LinearMap.BilinForm.dualNorm_apply` in `Chap04/Definition_4_3_4`, the `B.toDual` bridge for
  the dual norm.

Best owner abstraction:
* core/canonical: the bilinear-form owners `B.primalSeminorm` and `B.dualNorm`.

Primitive data:
* a bilinear form `B`;
* symmetry and positive-definiteness of `B.toQuadraticMap`.

Derived API:
* the induced primal seminorm and dual norm;
* the pairing estimate of Proposition 5.0.21.
* as a source-facing bridge, positive-definiteness from nonnegativity plus nondegeneracy.

The local Chapter 5 wrappers `localNormOfBilin` and `dualLocalNormOfBilin` were duplicate wheel
definitions: they carried no mathematics beyond the Chapter 4 bilinear-form owners. This file now
uses the owner abstraction directly and keeps only the source-faithful bridge from the proposition's
semidefinite plus nondegenerate hypotheses to that owner layer. -/

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

namespace LinearMap.BilinForm

/-- A symmetric nonnegative bilinear form is positive definite as soon as it is nondegenerate. -/
theorem posDef_of_nonneg_of_nondegenerate (B : LinearMap.BilinForm ℝ E)
    (hB_nonneg : ∀ v : E, 0 ≤ B v v) (hB_symm : B.IsSymm) (hB_nondeg : B.Nondegenerate) :
    B.toQuadraticMap.PosDef := by
  let hLinearSymm : LinearMap.IsSymm B := LinearMap.BilinForm.isSymm_iff.1 hB_symm
  have hB_pos : ∀ v : E, v ≠ 0 → 0 < B v v :=
    (LinearMap.BilinForm.nondegenerate_iff' B hB_nonneg hLinearSymm).1 hB_nondeg
  exact hB_pos

end LinearMap.BilinForm

variable [FiniteDimensional ℝ E]

private theorem abs_apply_le_dualNorm_mul_primalSeminorm_of_posDef
    (B : LinearMap.BilinForm ℝ E) (hB_symm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef)
    (g : Module.Dual ℝ E) (h : E) :
    |g h| ≤ ‖g‖*[B | hPos] * ‖h‖[B | hPos] := by
  let v := B.dualPreimage hPos g
  let hLinearSymm : LinearMap.IsSymm B := LinearMap.BilinForm.isSymm_iff.1 hB_symm
  have hsq : (B v h) ^ 2 ≤ (B v v) * (B h h) :=
    B.apply_sq_le_of_symm hPos.nonneg hLinearSymm v h
  have habs_sq : |B v h| ^ 2 ≤ (Real.sqrt (B v v) * Real.sqrt (B h h)) ^ 2 := by
    have hv_sq : (Real.sqrt (B v v)) ^ 2 = B v v := by
      simpa [BilinMap.toQuadraticMap_apply] using Real.sq_sqrt (hPos.nonneg v)
    have hh_sq : (Real.sqrt (B h h)) ^ 2 = B h h := by
      simpa [BilinMap.toQuadraticMap_apply] using Real.sq_sqrt (hPos.nonneg h)
    calc
      |B v h| ^ 2 = (B v h) ^ 2 := by rw [sq_abs]
      _ ≤ (B v v) * (B h h) := hsq
      _ = (Real.sqrt (B v v) * Real.sqrt (B h h)) ^ 2 := by
        calc
          (B v v) * (B h h) = (Real.sqrt (B v v)) ^ 2 * (Real.sqrt (B h h)) ^ 2 := by
            rw [hv_sq, hh_sq]
          _ = (Real.sqrt (B v v) * Real.sqrt (B h h)) ^ 2 := by ring
  have habs : |B v h| ≤ Real.sqrt (B v v) * Real.sqrt (B h h) := by
    exact le_of_sq_le_sq habs_sq (by positivity)
  have hv : B v v = g v := by
    simp [v]
  calc
    |g h| = |B v h| := by
      simp [v]
    _ ≤ Real.sqrt (B v v) * Real.sqrt (B h h) := habs
    _ = Real.sqrt (g v) * ‖h‖[B | hPos] := by
      rw [hv, B.primalSeminorm_apply]
    _ = ‖g‖*[B | hPos] * ‖h‖[B | hPos] := by
      simpa [v] using
        congrArg (fun t : ℝ ↦ t * ‖h‖[B | hPos]) (B.dualNorm_apply hB_symm hPos g).symm

/-- Proposition 5.0.21: if `B` is symmetric, nonnegative on diagonal values, and nondegenerate,
then the pairing between a covector and a vector is bounded by the `B`-dual norm of the covector
times the `B`-primal norm of the vector. The positive-definite owner data are obtained canonically
from these textbook hypotheses. -/
theorem abs_apply_le_dualNorm_mul_primalSeminorm (B : LinearMap.BilinForm ℝ E)
    (hB_nonneg : ∀ v : E, 0 ≤ B v v) (hB_symm : B.IsSymm) (hB_nondeg : B.Nondegenerate)
    (g : Module.Dual ℝ E) (h : E) :
    let hPos := B.posDef_of_nonneg_of_nondegenerate hB_nonneg hB_symm hB_nondeg
    |g h| ≤ ‖g‖*[B | hPos] * ‖h‖[B | hPos] := by
  let hPos : B.toQuadraticMap.PosDef :=
    B.posDef_of_nonneg_of_nondegenerate hB_nonneg hB_symm hB_nondeg
  simpa [hPos] using abs_apply_le_dualNorm_mul_primalSeminorm_of_posDef B hB_symm hPos g h
