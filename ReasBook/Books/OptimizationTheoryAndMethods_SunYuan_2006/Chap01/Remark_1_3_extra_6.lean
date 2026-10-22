/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Affine
open scoped RealInnerProductSpace

-- Semantic recall hits verified for this item: this remark is `source-facing`, while the
-- `core/canonical` owner of its conclusion is `S.directionᗮ`. The needed primitives are
-- `AffineSubspace.vadd_mem_of_mem_direction`, `AffineSubspace.vsub_mem_direction`, and
-- `Submodule.mem_orthogonal'`; no projection or minimizer bridge is needed.

section Remark13Extra6

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [AffineSpace V P]

/-- Chapter01 Remark 1.3-extra-6: if `S` is an affine subspace, `xbar ∈ S`, and
`⟪y -ᵥ xbar, x -ᵥ xbar⟫ ≤ 0` for every `x ∈ S`, then `y -ᵥ xbar` is orthogonal to the direction
subspace of `S`. This is the canonical formalization of the source conclusion
`(y -ᵥ xbar) ⟂ S`. -/
theorem sub_mem_direction_orthogonal_of_forall_inner_sub_nonpos
    {S : AffineSubspace ℝ P} {xbar y : P} (hxbar : xbar ∈ S)
    (h_nonpos : ∀ x ∈ S, ⟪y -ᵥ xbar, x -ᵥ xbar⟫ ≤ (0 : ℝ)) :
    y -ᵥ xbar ∈ S.directionᗮ := by
  rw [Submodule.mem_orthogonal']
  intro z hz
  have h_plus : ⟪y -ᵥ xbar, z⟫ ≤ (0 : ℝ) := by
    simpa [vadd_vsub_assoc] using
      h_nonpos (z +ᵥ xbar) (AffineSubspace.vadd_mem_of_mem_direction hz hxbar)
  have h_minus : (0 : ℝ) ≤ ⟪y -ᵥ xbar, z⟫ := by
    have h_neg : -⟪y -ᵥ xbar, z⟫ ≤ (0 : ℝ) := by
      simpa [vadd_vsub_assoc, inner_neg_right] using
        h_nonpos ((-z) +ᵥ xbar)
          (AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hz) hxbar)
    exact neg_nonpos.mp h_neg
  exact le_antisymm h_plus h_minus

/-- Membership in `S.directionᗮ` expands to the pointwise orthogonality identity
`⟪y -ᵥ xbar, x -ᵥ xbar⟫ = 0` for all `x ∈ S`. -/
theorem inner_sub_eq_zero_of_mem_direction_orthogonal
    {S : AffineSubspace ℝ P} {xbar y : P} (hxbar : xbar ∈ S)
    (hy : y -ᵥ xbar ∈ S.directionᗮ) :
    ∀ x ∈ S, ⟪y -ᵥ xbar, x -ᵥ xbar⟫ = (0 : ℝ) := by
  intro x hx
  exact Submodule.inner_left_of_mem_orthogonal
    (AffineSubspace.vsub_mem_direction hx hxbar) hy

/-- For an affine subspace, the source hypothesis forces the pointwise identity
`⟪y -ᵥ xbar, x -ᵥ xbar⟫ = 0` for all `x ∈ S`. -/
theorem inner_sub_eq_zero_of_forall_inner_sub_nonpos
    {S : AffineSubspace ℝ P} {xbar y : P} (hxbar : xbar ∈ S)
    (h_nonpos : ∀ x ∈ S, ⟪y -ᵥ xbar, x -ᵥ xbar⟫ ≤ (0 : ℝ)) :
    ∀ x ∈ S, ⟪y -ᵥ xbar, x -ᵥ xbar⟫ = (0 : ℝ) :=
  inner_sub_eq_zero_of_mem_direction_orthogonal hxbar
    (sub_mem_direction_orthogonal_of_forall_inner_sub_nonpos hxbar h_nonpos)

end Remark13Extra6
