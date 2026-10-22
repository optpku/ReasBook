/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

public section

universe u

/-- Finite-dimensionality transports along the canonical linear equivalence
`toWeakSpace ℝ H : H ≃ₗ[ℝ] WeakSpace ℝ H`. -/
instance weakSpaceFiniteDimensional
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] :
    FiniteDimensional ℝ (WeakSpace ℝ H) :=
  (toWeakSpace ℝ H).finiteDimensional
