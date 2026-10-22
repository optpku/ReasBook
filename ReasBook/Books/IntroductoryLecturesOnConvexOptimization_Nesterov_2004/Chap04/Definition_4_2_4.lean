/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_2

noncomputable section

open Module
open scoped BigOperators

universe u v

/- Definition 4.2.4 lies in the finite-dimensional basis-coordinate / dual-basis domain.

Sampled owner-style declarations:
- `Basis.equivFun`
- `Basis.equivFun_symm_apply`
- `Basis.dualBasis`
- `Basis.dualBasis_equivFun`

Best owner abstraction:
- core/canonical: the basis coordinate equivalence `B.equivFun` and the dual-basis coordinate
  equivalence `B.dualBasis.equivFun`;
- bridge/view: the textbook `ℝⁿ` model via `EuclideanSpace.equiv`.

Primitive data:
- a basis `B : Basis (Fin n) ℝ E`;
- a coordinate vector `x : EuclideanSpace ℝ (Fin n)`;
- a covector `s : Dual ℝ E`.

Derived API:
- the source-facing basis operator `B : ℝⁿ → E`, canonically realized as
  `B.equivFun.symm ∘ EuclideanSpace.equiv (Fin n) ℝ`;
- the source-facing dual operator `B* : E* → ℝⁿ`, canonically realized as
  `(EuclideanSpace.equiv (Fin n) ℝ).symm ∘ B.dualBasis.equivFun`.

Source/core/bridge triage:
- source-facing: Definition 4.2.4's two maps `B` and `B*`;
- core/canonical: `Basis.equivFun`, `Basis.dualBasis`, and `Basis.dualBasis_equivFun`;
- bridge/view: transport between `Fin n → ℝ` and `EuclideanSpace ℝ (Fin n)` via
  `EuclideanSpace.equiv`.

This file therefore recalls the canonical basis/dual-basis coordinate owners and keeps only the
thin Euclidean bridge theorems matching the textbook formulas. -/

section Intrinsic

/- Definition 4.2.4 uses the canonical basis coordinate equivalence `B.equivFun`, whose inverse is
the basis operator from coordinates to vectors. -/
#check Basis.equivFun

/- The forward coordinate formula is the standard theorem `Basis.equivFun_symm_apply`. -/
#check Basis.equivFun_symm_apply

/- The dual object `B*` is the canonical dual basis `B.dualBasis`. -/
#check Basis.dualBasis

/- The dual-coordinate formula is the standard theorem `Basis.dualBasis_equivFun`. -/
#check Basis.dualBasis_equivFun

end Intrinsic

section EuclideanBridge

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {n : ℕ}

/-- Definition 4.2.4: in the textbook `ℝⁿ` model, the basis operator attached to `B` is the
canonical inverse coordinate map `B.equivFun.symm`, transported through `EuclideanSpace.equiv`. -/
theorem basis_equivFun_symm_apply (B : Basis (Fin n) ℝ E) (x : EuclideanSpace ℝ (Fin n)) :
    B.equivFun.symm (EuclideanSpace.equiv (Fin n) ℝ x) = ∑ i : Fin n, x i • B i := by
  rw [Basis.equivFun_symm_apply]
  simp [EuclideanSpace.equiv]

/-- Definition 4.2.4: in the textbook `ℝⁿ` model, the dual basis operator `B*` has `i`th
coordinate `⟪s, B i⟫ = s (B i)`. -/
theorem dualBasis_equivFun_apply (B : Basis (Fin n) ℝ E) (s : Dual ℝ E) (i : Fin n) :
    ((EuclideanSpace.equiv (Fin n) ℝ).symm (B.dualBasis.equivFun s)) i = s (B i) := by
  change B.dualBasis.equivFun s i = s (B i)
  rw [Basis.dualBasis_equivFun]

end EuclideanBridge

end
