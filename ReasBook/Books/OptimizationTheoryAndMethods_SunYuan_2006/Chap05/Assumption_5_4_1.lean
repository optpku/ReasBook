/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section

section Chapter05Assumption541

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall: `lean_leansearch` surfaced local-inverse and local Lipschitz lemmas for
-- `ContDiffAt`/`ContDiffOn`, but no canonical bundled owner for this exact assumption package,
-- so this item keeps the source-faithful `ContDiffOn`/`fderiv` formulation explicit.

/-- Chapter05 Assumption 5.4.1: `F : ℝ^n → ℝ^n` is continuously differentiable on an open convex
set `D`, there is `xStar ∈ D` with `F xStar = 0` and invertible derivative `fderiv ℝ F xStar`,
and there is a constant `gamma` such that
`‖fderiv ℝ F x - fderiv ℝ F xStar‖ ≤ gamma * ‖x - xStar‖` for every `x ∈ D`. -/
structure HasQuasiNewtonLocalConvergenceAssumptions
    (D : Set Point) (F : Point → Point) where
  open_domain : IsOpen D
  convex_domain : Convex ℝ D
  contDiffOn : ContDiffOn ℝ 1 F D
  xStar : Point
  xStar_mem : xStar ∈ D
  map_xStar : F xStar = 0
  fderiv_isInvertible : (fderiv ℝ F xStar).IsInvertible
  gamma : ℝ
  lipschitz_fderiv :
    ∀ x ∈ D, ‖fderiv ℝ F x - fderiv ℝ F xStar‖ ≤ gamma * ‖x - xStar‖

/-- Membership in the local-convergence assumption package is membership in its ambient
domain `D`. -/
instance instMembershipPointHasQuasiNewtonLocalConvergenceAssumptions
    {D : Set Point} {F : Point → Point} :
    Membership Point (HasQuasiNewtonLocalConvergenceAssumptions D F) where
  mem _ x := x ∈ D

namespace HasQuasiNewtonLocalConvergenceAssumptions

@[simp] theorem mem_iff
    {D : Set Point} {F : Point → Point}
    (h : HasQuasiNewtonLocalConvergenceAssumptions D F) (x : Point) :
    x ∈ h ↔ x ∈ D :=
  Iff.rfl

@[simp] theorem mem_xStar
    {D : Set Point} {F : Point → Point}
    (h : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    h.xStar ∈ h :=
  h.xStar_mem

/-- The distinguished solution `xStar` from Chapter05 Assumption 5.4.1 as a point of `D`. -/
def xStarInDomain
    {D : Set Point} {F : Point → Point}
    (h : HasQuasiNewtonLocalConvergenceAssumptions D F) : D :=
  ⟨h.xStar, h.xStar_mem⟩

/-- The inverse derivative `F'(x*)⁻¹` attached canonically to the local-convergence assumption
owner. -/
noncomputable def referenceInverse
    {D : Set Point} {F : Point → Point}
    (h : HasQuasiNewtonLocalConvergenceAssumptions D F) : Point →L[ℝ] Point :=
  (fderiv ℝ F h.xStar).inverse

@[simp] theorem coe_xStarInDomain
    {D : Set Point} {F : Point → Point}
    (h : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    ((xStarInDomain h : D) : Point) = h.xStar :=
  rfl

@[simp] theorem xStarInDomain_mem
    {D : Set Point} {F : Point → Point}
    (h : HasQuasiNewtonLocalConvergenceAssumptions D F) :
    (xStarInDomain h : Point) ∈ D :=
  h.xStar_mem

end HasQuasiNewtonLocalConvergenceAssumptions

end Chapter05Assumption541
