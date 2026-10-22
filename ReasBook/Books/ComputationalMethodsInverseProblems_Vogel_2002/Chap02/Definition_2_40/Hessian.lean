/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Hessian of `J` at `f`, defined as the bounded operator representing the bilinear second
Fréchet derivative via the Fréchet-Riesz theorem. -/
def hessian (J : H → ℝ) (f : H) : H →L[ℝ] H :=
  InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ J) f)

/-- Rewrites `hessian J f` as the representing operator for the second Fréchet derivative. -/
theorem hessian_inner (J : H → ℝ) (f h k : H) :
    inner ℝ (hessian J f h) k = fderiv ℝ (fderiv ℝ J) f h k := by
  rw [hessian]
  exact InnerProductSpace.continuousLinearMapOfBilin_apply
    (B := fderiv ℝ (fderiv ℝ J) f) h k

/-- A symmetric second Fréchet derivative induces a self-adjoint Hessian operator. -/
theorem hessian_isSelfAdjoint_of_isSymmSndFDerivAt
    (J : H → ℝ) (f : H) (hJ : IsSymmSndFDerivAt ℝ J f) :
    IsSelfAdjoint (hessian J f) := by
  -- Symmetry of the bilinear second derivative is exactly the symmetry relation for the
  -- representing operator under the real inner product.
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro h k
  calc
    inner ℝ ((hessian J f) h) k = fderiv ℝ (fderiv ℝ J) f h k := hessian_inner J f h k
    _ = fderiv ℝ (fderiv ℝ J) f k h := hJ h k
    _ = inner ℝ ((hessian J f) k) h := (hessian_inner J f k h).symm
    _ = inner ℝ h ((hessian J f) k) := real_inner_comm _ _

/-- A `C²` functional has self-adjoint Hessian at each point. -/
theorem hessian_isSelfAdjoint_of_contDiffAt
    (J : H → ℝ) (f : H) (hJ : ContDiffAt ℝ 2 J f) :
    IsSelfAdjoint (hessian J f) := by
  exact hessian_isSelfAdjoint_of_isSymmSndFDerivAt J f (hJ.isSymmSndFDerivAt (by simp))
