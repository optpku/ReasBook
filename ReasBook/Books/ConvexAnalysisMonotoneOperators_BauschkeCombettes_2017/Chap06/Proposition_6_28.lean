/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

noncomputable def properConeProjectionChebyshev (K : ProperCone ℝ 𝓗) :
    IsChebyshev (K : Set 𝓗) :=
  isChebyshev_of_nonempty_isClosed_convex K.nonempty K.isClosed K.convex

-- Proof sketch: unfold the projection characterization from Theorem 3.16.2 for the closed convex
-- set underlying `K`.
/-- Proposition 6.28 (1): if `p` is the projection of `x` onto the proper cone `K`, then
`p ∈ K`. -/
theorem mem_of_eq_projectionPoint_on_properCone
    (K : ProperCone ℝ 𝓗) {x p : 𝓗}
    (hp : p = projectionPoint (K : Set 𝓗) (properConeProjectionChebyshev K) x) :
    p ∈ K := by
  -- Rewrite the projection equation through Theorem 3.16.2 and read off cone membership.
  exact
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      K.nonempty K.isClosed K.convex).1
      (by simpa [properConeProjectionChebyshev] using hp) |>.1

-- Proof sketch: apply the variational inequality for the projection to the cone points `0` and
-- `2 • p`; subtract the two resulting inequalities to force orthogonality.
/-- Proposition 6.28 (2): if `p` is the projection of `x` onto `K`, then the residual `x - p` is
orthogonal to `p`. -/
theorem inner_eq_zero_of_eq_projectionPoint_on_properCone
    (K : ProperCone ℝ 𝓗) {x p : 𝓗}
    (hp : p = projectionPoint (K : Set 𝓗) (properConeProjectionChebyshev K) x) :
    ⟪x - p, p⟫_ℝ = 0 := by
  -- Rewrite the projection hypothesis as the variational inequality from Theorem 3.16.2.
  have hproj :=
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      K.nonempty K.isClosed K.convex).1
      (by simpa [properConeProjectionChebyshev] using hp)
  have hpK : p ∈ K := hproj.1
  -- Test the variational inequality at `0 ∈ K`.
  have hzero : ⟪-p, x - p⟫_ℝ ≤ 0 := by
    simpa using hproj.2 0 K.zero_mem
  -- Test the same inequality at `2 • p ∈ K`.
  have htwo : ⟪p, x - p⟫_ℝ ≤ 0 := by
    have htwo_mem : (2 : ℝ) • p ∈ K := by
      exact K.smul_mem hpK (by norm_num)
    simpa [two_smul, sub_eq_add_neg, add_assoc] using
      hproj.2 ((2 : ℝ) • p) htwo_mem
  have hnonneg : 0 ≤ ⟪p, x - p⟫_ℝ := by
    have hzero' : -⟪p, x - p⟫_ℝ ≤ 0 := by
      simpa [inner_neg_left] using hzero
    linarith
  have hinner : ⟪p, x - p⟫_ℝ = 0 := by
    linarith
  -- Commute the real inner product to match the statement.
  simpa [real_inner_comm] using hinner

-- Proof sketch: after obtaining `p ∈ K` from the projection criterion, the variational inequality
-- against arbitrary `y ∈ K` rewrites as membership in the polar cone `Kᵒ⊖`.
/-- Proposition 6.28 (3): if `p` is the projection of `x` onto `K`, then the residual `x - p`
belongs to the polar cone of `K`. -/
theorem sub_mem_polarCone_of_eq_projectionPoint_on_properCone
    (K : ProperCone ℝ 𝓗) {x p : 𝓗}
    (hp : p = projectionPoint (K : Set 𝓗) (properConeProjectionChebyshev K) x) :
    x - p ∈ (K : Set 𝓗)ᵒ⊖ := by
  -- Rewrite the projection hypothesis as the same variational inequality used in the source proof.
  have hproj :=
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      K.nonempty K.isClosed K.convex).1
      (by simpa [properConeProjectionChebyshev] using hp)
  have horth : ⟪p, x - p⟫_ℝ = 0 := by
    simpa [real_inner_comm] using inner_eq_zero_of_eq_projectionPoint_on_properCone K hp
  -- Route correction: convert `⟪y - p, x - p⟫ ≤ 0` into the polar inequality by removing
  -- the zero `p`-term furnished by orthogonality.
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  intro y hy
  have hyproj : ⟪y - p, x - p⟫_ℝ ≤ 0 := hproj.2 y hy
  simpa [inner_sub_left, horth] using hyproj

-- Proof sketch: start from Theorem 3.16's variational characterization for convex sets. The
-- hypotheses `p ∈ K`, `⟪x - p, p⟫_ℝ = 0`, and `x - p ∈ Kᵒ⊖` together give the
-- required inner-product inequality for every `y ∈ K`, so `p` is the projection.
/-- Proposition 6.28 (4): conversely, if `p ∈ K`, the residual `x - p` is orthogonal to `p`, and
the residual belongs to the polar cone of `K`, then `p` is the projection of `x` onto `K`. -/
theorem eq_projectionPoint_on_properCone_of_mem_of_inner_eq_zero_of_sub_mem_polarCone
    (K : ProperCone ℝ 𝓗) {x p : 𝓗}
    (hp : p ∈ K) (horth : ⟪x - p, p⟫_ℝ = 0)
    (hpolar : x - p ∈ (K : Set 𝓗)ᵒ⊖) :
    p = projectionPoint (K : Set 𝓗) (properConeProjectionChebyshev K) x := by
  rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hpolar
  have hproj :
      p =
        projectionPoint (K : Set 𝓗)
          (isChebyshev_of_nonempty_isClosed_convex K.nonempty K.isClosed K.convex) x := by
    -- Rebuild the Chapter 3 variational inequality from polar membership and orthogonality.
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        K.nonempty K.isClosed K.convex).2 ?_
    refine ⟨hp, ?_⟩
    intro y hy
    have hy_nonpos : ⟪y, x - p⟫_ℝ ≤ 0 := hpolar y hy
    have horth' : ⟪p, x - p⟫_ℝ = 0 := by
      simpa [real_inner_comm] using horth
    simpa [inner_sub_left, horth'] using hy_nonpos
  simpa [properConeProjectionChebyshev] using hproj

/-- Proposition 6.28: projection onto a proper cone is characterized by membership in the cone,
orthogonality to the residual, and membership of the residual in the polar cone. -/
theorem eq_projectionPoint_on_properCone_iff
    (K : ProperCone ℝ 𝓗) {x p : 𝓗} :
    p = projectionPoint (K : Set 𝓗) (properConeProjectionChebyshev K) x ↔
      p ∈ K ∧ ⟪x - p, p⟫_ℝ = 0 ∧ x - p ∈ (K : Set 𝓗)ᵒ⊖ := by
  constructor
  · intro hp
    -- Collect the three forward consequences established above.
    refine ⟨?_, ?_, ?_⟩
    · exact mem_of_eq_projectionPoint_on_properCone K hp
    · exact inner_eq_zero_of_eq_projectionPoint_on_properCone K hp
    · exact sub_mem_polarCone_of_eq_projectionPoint_on_properCone K hp
  · rintro ⟨hp, horth, hpolar⟩
    -- The converse direction is exactly the reverse implication proved above.
    exact
      eq_projectionPoint_on_properCone_of_mem_of_inner_eq_zero_of_sub_mem_polarCone
        K hp horth hpolar

end
