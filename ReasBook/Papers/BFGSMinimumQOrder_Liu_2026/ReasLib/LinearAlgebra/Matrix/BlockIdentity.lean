module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

universe u

namespace Matrix

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A matrix has block form `B|V ⊕ 1` when its associated Euclidean endomorphism
preserves `V` and is the identity on `Vᗮ`. -/
def IsBlockIdentityOn (B : Matrix ι ι ℝ)
    (V : Submodule ℝ (EuclideanSpace ℝ ι)) : Prop :=
  V ∈ Module.End.invtSubmodule (Matrix.toLpLin 2 2 B) ∧
    ∀ z, z ∈ Vᗮ → Matrix.toLpLin 2 2 B z = z

/-- Block identity on a subspace is equivalent to invariance of that subspace together
with identity action on its orthogonal complement. -/
theorem isBlockIdentityOn_iff (B : Matrix ι ι ℝ)
    (V : Submodule ℝ (EuclideanSpace ℝ ι)) :
    IsBlockIdentityOn B V ↔
      V ∈ Module.End.invtSubmodule (Matrix.toLpLin 2 2 B) ∧
        ∀ z, z ∈ Vᗮ → Matrix.toLpLin 2 2 B z = z := by
  -- Unfolding the predicate exposes exactly the stated conjunction.
  rfl

namespace IsBlockIdentityOn

/-- The endomorphism induced on an invariant subspace by a block-identity matrix. -/
noncomputable def restriction {B : Matrix ι ι ℝ}
    {V : Submodule ℝ (EuclideanSpace ℝ ι)} (h : IsBlockIdentityOn B V) :
    V →ₗ[ℝ] V :=
  LinearMap.restrict (Matrix.toLpLin 2 2 B) h.1

/-- Including the restricted action into the ambient Euclidean space recovers the
matrix endomorphism. -/
theorem restriction_apply {B : Matrix ι ι ℝ}
    {V : Submodule ℝ (EuclideanSpace ℝ ι)} (h : IsBlockIdentityOn B V) (z : V) :
    V.subtype (h.restriction z) = Matrix.toLpLin 2 2 B z := by
  -- Restriction preserves the ambient value; the subtype map then forgets membership.
  rfl

end IsBlockIdentityOn

end Matrix
