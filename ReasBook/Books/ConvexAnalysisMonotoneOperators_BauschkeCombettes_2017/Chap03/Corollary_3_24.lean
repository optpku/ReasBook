/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable (V : ClosedSubmodule ℝ 𝓗) (x p : 𝓗)

-- Proof sketch: use the uniqueness characterization of orthogonal projection onto a complete
-- subspace. One direction combines `starProjection_apply_mem` with
-- `sub_starProjection_mem_orthogonal`; the converse uses
-- `eq_starProjection_of_mem_orthogonal`.
/-- Corollary 3.24 (1): textbook clause (i). A point is the orthogonal projection of `x` onto the
closed subspace `V` exactly when it lies in `V` and the residual vector lies in `Vᗮ`. -/
theorem starProjection_eq_iff_mem_and_sub_mem_orthogonal :
    V.starProjection x = p ↔ p ∈ V ∧ x - p ∈ Vᗮ := by
  -- The forward implication is exactly the packaged membership and orthogonality
  -- of `starProjection`.
  constructor
  · intro hp
    rw [← hp]
    exact
      ⟨(V : Submodule ℝ 𝓗).starProjection_apply_mem x,
        (V : Submodule ℝ 𝓗).sub_starProjection_mem_orthogonal x⟩
  · rintro ⟨hpV, horth⟩
    -- Uniqueness of orthogonal projection gives the converse direction.
    exact (V : Submodule ℝ 𝓗).eq_starProjection_of_mem_orthogonal hpV horth

-- Proof sketch: rewrite the left inner product using
-- `inner_orthogonalProjection_eq_of_mem_left` with the projected vector, then identify
-- `⟪P_V x, P_V x⟫` with `‖P_V x‖ ^ 2`.
/-- Corollary 3.24 (2): textbook clause (ii). The squared norm of the orthogonal projection equals
its inner product with the original vector. -/
theorem norm_sq_orthogonalProjection_eq_inner_starProjection :
    ‖V.orthogonalProjection x‖ ^ 2 = ⟪V.starProjection x, x⟫_ℝ := by
  -- Mathlib already identifies the real part of this inner product with the squared norm.
  simpa using ((V : Submodule ℝ 𝓗).re_inner_starProjection_eq_normSq x).symm

-- Proof sketch: the orthogonal projector is already a continuous linear map, and the standard
-- norm estimate `orthogonalProjection_norm_le` yields operator norm at most `1`.
/-- Corollary 3.24 (3): textbook clause (iii). The orthogonal projector onto `V` is bounded, with
operator norm at most `1`. -/
theorem norm_starProjection_le_one :
    ‖V.starProjection‖ ≤ 1 := by
  -- The orthogonal projector is a contraction.
  exact (V : Submodule ℝ 𝓗).starProjection_norm_le

-- Proof sketch: apply the standard operator-norm formula for orthogonal projection onto a
-- nontrivial subspace.
/-- Corollary 3.24 (4): textbook clause (iii). If `V` is nontrivial, then the orthogonal
projector onto `V` has operator norm `1`. -/
theorem norm_starProjection_eq_one_of_ne_bot (hV : V ≠ ⊥) :
    ‖V.starProjection‖ = 1 := by
  -- Translate nontriviality from closed submodules to ordinary submodules.
  have hV' : (V : Submodule ℝ 𝓗) ≠ ⊥ := by
    intro h
    exact hV (ClosedSubmodule.toSubmodule_injective h)
  -- Then apply the standard norm formula for orthogonal projection.
  exact (V : Submodule ℝ 𝓗).norm_starProjection hV'

-- Proof sketch: if `V = ⊥`, rewrite the projector as the zero projection and simplify its norm.
/-- Corollary 3.24 (5): textbook clause (iii). If `V = {0}`, then the orthogonal projector onto
`V` has operator norm `0`. -/
theorem norm_starProjection_eq_zero_of_eq_bot (hV : V = ⊥) :
    ‖V.starProjection‖ = 0 := by
  -- The projector onto the zero subspace is the zero map.
  rw [hV]
  simp

-- Proof sketch: use the closed-subspace identity `(Vᗮ)ᗮ = V`.
/-- Corollary 3.24 (6): textbook clause (iv). The double orthogonal complement of a closed subspace
is the subspace itself. -/
theorem orthogonal_orthogonal_eq :
    Vᗮᗮ = V := by
  -- Closed subspaces are equal to their double orthogonal complements.
  exact ClosedSubmodule.orthogonal_orthogonal_eq V

-- Proof sketch: apply the canonical decomposition of the identity into the projections onto `V`
-- and `Vᗮ`.
/-- Corollary 3.24 (7): textbook clause (v). The orthogonal projector onto `Vᗮ` is `Id - P_V`. -/
theorem starProjection_orthogonal_eq_one_sub :
    Vᗮ.starProjection = 1 - V.starProjection := by
  -- Mathlib packages the decomposition `Id = P_V + P_{Vᗮ}` as this projection identity.
  exact (V : Submodule ℝ 𝓗).starProjection_orthogonal'

-- Proof sketch: combine the symmetry of orthogonal projection with the standard equivalence
-- between symmetry and equality to the adjoint for continuous linear maps.
/-- Corollary 3.24 (8): textbook clause (vi). The orthogonal projector onto `V` is self-adjoint. -/
theorem adjoint_starProjection_eq :
    V.starProjection.adjoint = V.starProjection := by
  -- Orthogonal projections are self-adjoint operators.
  simpa using (isSelfAdjoint_starProjection (V : Submodule ℝ 𝓗)).adjoint_eq

-- Proof sketch: apply the Pythagorean identity coming from the decomposition
-- `x = P_V x + P_{Vᗮ} x`.
/-- Corollary 3.24 (9): textbook clause (vii). The norm of `x` splits as the sum of the squared
norms of its projections onto `V` and `Vᗮ`. -/
theorem norm_sq_eq_add_norm_sq_orthogonalProjection :
    ‖x‖ ^ 2 =
      ‖V.orthogonalProjection x‖ ^ 2 + ‖Vᗮ.orthogonalProjection x‖ ^ 2 := by
  -- This is the Pythagorean theorem for the orthogonal decomposition of `x`.
  exact Submodule.norm_sq_eq_add_norm_sq_projection x (V : Submodule ℝ 𝓗)

-- Helper for Corollary 3.24: the distance from `x` to `V` equals the norm of the residual
-- `x - P_V x`.
private theorem infDist_eq_norm_sub_starProjection :
    Metric.infDist x (V : Set 𝓗) = ‖x - V.starProjection x‖ := by
  -- Expand `infDist` into the infimum of distances to points of `V`.
  rw [Metric.infDist_eq_iInf]
  -- Rewrite those distances as ambient-space norms.
  simp_rw [dist_eq_norm]
  -- The residual of the orthogonal projection realizes the infimum.
  simpa using ((V : Submodule ℝ 𝓗).starProjection_minimal x).symm

-- Proof sketch: identify the distance from `x` to `V` with the norm of `x - P_V x`, then use the
-- formula `P_{Vᗮ} = Id - P_V`.
/-- Corollary 3.24 (10): textbook clause (vii). The distance from `x` to `V` is the norm of the
orthogonal component of `x` along `Vᗮ`. -/
theorem infDist_eq_norm_orthogonalProjection_orthogonal :
    Metric.infDist x (V : Set 𝓗) = ‖Vᗮ.orthogonalProjection x‖ := by
  -- First rewrite the distance as the norm of the orthogonal residual.
  rw [infDist_eq_norm_sub_starProjection]
  -- Then identify that residual with the projection onto `Vᗮ`.
  exact (congrArg norm ((V : Submodule ℝ 𝓗).orthogonalProjection_orthogonal x)).symm

-- Proof sketch: apply the previous distance formula to the closed subspace `Vᗮ`, then use
-- `(Vᗮ)ᗮ = V`.
/-- Corollary 3.24 (11): textbook clause (vii). The distance from `x` to `Vᗮ` is the norm of the
projection of `x` onto `V`. -/
theorem infDist_orthogonal_eq_norm_orthogonalProjection :
    Metric.infDist x (Vᗮ : Set 𝓗) = ‖V.orthogonalProjection x‖ := by
  -- Apply the distance formula to `Vᗮ`.
  rw [infDist_eq_norm_sub_starProjection]
  -- The residual to `Vᗮ` is exactly the projection onto `V`.
  simp

end
