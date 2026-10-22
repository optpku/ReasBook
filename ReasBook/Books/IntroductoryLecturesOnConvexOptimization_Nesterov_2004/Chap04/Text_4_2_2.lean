/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module

universe u v

/-
Text 4.2.2 lies in the finite-dimensional basis-coordinate / dual-basis duality domain.

Sampled owner-style declarations:
- `Basis.equivFun`
- `Basis.sum_equivFun`
- `Basis.dualBasis_equivFun`
- `Matrix.dotProduct`
- `EuclideanSpace.inner_eq_star_dotProduct`

Best owner abstraction:
- a finite basis `B : Basis ι R E`, with the canonical coordinate map `B.equivFun`
  and the dual-coordinate bridge theorem `Basis.dualBasis_equivFun`

Primitive data:
- `B : Basis ι R E`
- `s : Dual R E`
- `x : E`

Derived API:
- the coordinate dot product `(fun i ↦ s (B i)) ⬝ᵥ B.equivFun x`
- the corresponding Euclidean inner-product form obtained by transporting those coordinate
  functions through `EuclideanSpace.equiv` in the real `Fin n` specialization

Source/core/bridge triage:
- source-facing: the coordinate formula for the duality pairing
- core/canonical: `Module.dualPairing`, `Basis.equivFun`, and the bridge theorem
  `Basis.dualBasis_equivFun`
- bridge/view: transport between `Fin n → ℝ` and `EuclideanSpace ℝ (Fin n)` via
  `EuclideanSpace.equiv`

This file therefore keeps only the source-facing theorem and a thin theorem-level bridge, rather
than owning duplicate public coordinate operators built by composing the canonical maps.
-/

section CoordinateDuality

variable {R : Type v} {ι : Type*} {E : Type u}
variable [CommSemiring R] [Fintype ι] [AddCommMonoid E] [Module R E]

/-- In basis/dual-basis coordinates, the duality pairing is the standard dot product. -/
theorem dualityPairing_eq_coordinateDotProduct
    (B : Basis ι R E) (s : Dual R E) (x : E) :
    Module.dualPairing R E s x = (fun i ↦ s (B i)) ⬝ᵥ B.equivFun x := by
  classical
  rw [Module.dualPairing_apply]
  calc
    s x = s (∑ i : ι, B.equivFun x i • B i) := by
      exact congrArg s (B.sum_equivFun x).symm
    _ = ∑ i : ι, s (B i) * B.equivFun x i := by
      simp_rw [map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = (fun i ↦ s (B i)) ⬝ᵥ B.equivFun x := by
      simp [dotProduct]

end CoordinateDuality

section EuclideanBridge

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: expand `x` in the basis `B` and `s` in the dual basis `B*`; evaluation of `s`
-- on the resulting linear combination reduces to the sum of coordinatewise products, which is the
-- Euclidean dot product of the two coordinate vectors.
/-- Text 4.2.2: the duality pairing equals the Euclidean inner product of the coordinate vectors
`B* s` and `B⁻¹ x`. -/
theorem dualityPairing_eq_inner_coordinateVectors {n : ℕ}
    (B : Basis (Fin n) ℝ E) (s : Dual ℝ E) (x : E) :
    Module.dualPairing ℝ E s x =
      inner ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm (B.dualBasis.equivFun s))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (B.equivFun x)) := by
  have hdual : (fun i : Fin n ↦ s (B i)) = B.dualBasis.equivFun s := by
    ext i
    rw [Basis.dualBasis_equivFun]
  calc
    Module.dualPairing ℝ E s x = (fun i : Fin n ↦ s (B i)) ⬝ᵥ B.equivFun x :=
      dualityPairing_eq_coordinateDotProduct B s x
    _ = B.dualBasis.equivFun s ⬝ᵥ B.equivFun x := by
      rw [hdual]
    _ = inner ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm (B.dualBasis.equivFun s))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (B.equivFun x)) := by
      have hinner :
          ∀ u v : EuclideanSpace ℝ (Fin n), inner ℝ u v = u ⬝ᵥ v := fun u v ↦ by
            simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct u v)
      rw [hinner]
      simp [EuclideanSpace.equiv]

end EuclideanBridge

end
