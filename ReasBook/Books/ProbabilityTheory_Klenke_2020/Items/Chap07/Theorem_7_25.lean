/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

-- Proof sketch: a closed subspace of a complete inner product space has an orthogonal projection.
-- The canonical decomposition is therefore given by the projections onto `W` and `Wᗮ`, and the
-- textbook `∃!` formulation is the corresponding uniqueness corollary.
/- Theorem 7.25: the canonical orthogonal decomposition is already the owner theorem
`Submodule.starProjection_add_starProjection_orthogonal`, specialized in this chapter to closed
subspaces of complete real inner product spaces. -/
recall Submodule.starProjection_add_starProjection_orthogonal

/-- Theorem 7.25: Every vector in a Hilbert space has a unique decomposition into a vector in a
closed subspace and a vector in its orthogonal complement. This is the textbook existence-and-
uniqueness form of the canonical decomposition above. -/
theorem existsUnique_orthogonal_decomposition (W : ClosedSubmodule ℝ V) (x : V) :
    ∃! yz : W × Wᗮ, (yz.1 : V) + (yz.2 : V) = x := by
  simpa using
    Submodule.existsUnique_add_of_isCompl_prod
      W.toSubmodule.isCompl_orthogonal_of_hasOrthogonalProjection x
