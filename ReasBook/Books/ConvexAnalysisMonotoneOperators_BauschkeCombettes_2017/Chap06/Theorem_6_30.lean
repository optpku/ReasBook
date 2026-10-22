/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

-- Proof sketch: a proper cone is nonempty, closed, and convex, so apply
-- `isChebyshev_of_nonempty_isClosed_convex`.
/-- Helper for Theorem 6.30: a proper cone in a real Hilbert space is a Chebyshev set. -/
theorem isChebyshev_of_properCone (K : ProperCone ℝ 𝓗) :
    IsChebyshev (K : Set 𝓗) := by
  -- A proper cone already carries the nonempty, closed, and convex structure needed in Chapter 3.
  exact isChebyshev_of_nonempty_isClosed_convex K.nonempty K.isClosed K.convex

-- Proof sketch: `Set.negativePolar K` is nonempty, closed, and convex by Proposition 6.24, so
-- apply `isChebyshev_of_nonempty_isClosed_convex`.
/-- Helper for Theorem 6.30: the negative polar cone of a proper cone in a real Hilbert space is
a Chebyshev set. -/
theorem isChebyshev_negativePolar (K : ProperCone ℝ 𝓗) :
    IsChebyshev (Set.negativePolar (K : Set 𝓗)) := by
  -- Proposition 6.24 gives the nonempty, closed, and convex structure of the negative polar cone.
  exact
    isChebyshev_of_nonempty_isClosed_convex
      (Set.negativePolar_nonempty (K : Set 𝓗))
      (Set.negativePolar_isClosed (K : Set 𝓗))
      (Set.negativePolar_convex (K : Set 𝓗))

/-- Helper for Theorem 6.30: every point of a proper cone lies in the polar cone of its negative
polar cone. -/
lemma mem_polarCone_negativePolar_of_mem (K : ProperCone ℝ 𝓗) {u : 𝓗}
    (hu : u ∈ (K : Set 𝓗)) :
    u ∈ Set.polarCone (Set.negativePolar (K : Set 𝓗)) := by
  -- Unfold the polar-cone condition and test it on an arbitrary vector from the negative polar.
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  intro v hv
  rw [Set.mem_negativePolar] at hv
  simpa [real_inner_comm] using hv u hu

-- Proof sketch: apply Proposition 6.28 to the projection of `x` onto `K`, identify the residual
-- with the projection onto `Kᵒ⊖`, and rewrite the resulting decomposition.
/-- Theorem 6.30 (1): textbook clause (i). Every vector decomposes as the sum of its projections
onto a proper cone and its negative polar cone. -/
theorem eq_projectionPoint_add_projectionPoint_negativePolar
    (K : ProperCone ℝ 𝓗) (x : 𝓗) :
    x =
      projectionPoint (K : Set 𝓗) (isChebyshev_of_properCone K) x +
        projectionPoint (Set.negativePolar (K : Set 𝓗)) (isChebyshev_negativePolar K) x := by
  set p : 𝓗 := projectionPoint (K : Set 𝓗) (isChebyshev_of_properCone K) x with hp_def
  set q : 𝓗 := x - p with hq_def
  have hp_best : IsBestApproximation x (K : Set 𝓗) p := by
    -- The chosen projection onto `K` is a best approximation independently of the witness used.
    simpa [hp_def] using
      projectionPoint_isBestApproximation
        (K : Set 𝓗) (isChebyshev_of_properCone K) x
  have hp_proj :
      p = projectionPoint (K : Set 𝓗) (properConeProjectionChebyshev K) x := by
    -- Bridge from the local Chebyshev witness to Proposition 6.28's canonical witness.
    exact
      eq_projectionPoint_of_isBestApproximation
        (K : Set 𝓗) (properConeProjectionChebyshev K) hp_best
  have hp_mem : p ∈ (K : Set 𝓗) := by
    -- Proposition 6.28 first places the projection point back in the cone.
    exact mem_of_eq_projectionPoint_on_properCone K hp_proj
  have horth : ⟪x - p, p⟫_ℝ = 0 := by
    -- Proposition 6.28 also supplies the key orthogonality of the residual to the cone point.
    exact inner_eq_zero_of_eq_projectionPoint_on_properCone K hp_proj
  have hq_mem : q ∈ Set.negativePolar (K : Set 𝓗) := by
    -- The same proposition identifies the residual as lying in the polar, i.e. negative polar,
    -- cone of `K`.
    have hq_polar : q ∈ Set.polarCone (K : Set 𝓗) := by
      simpa [hq_def] using sub_mem_polarCone_of_eq_projectionPoint_on_properCone K hp_proj
    rw [Set.polarCone_eq_innerDual_neg (K : Set 𝓗)] at hq_polar
    simpa [Set.negativePolar] using hq_polar
  have hx_sub_q : x - q = p := by
    -- This is the textbook residual identity `x - (x - p) = p`.
    rw [hq_def]
    abel
  have hq_orth : ⟪x - q, q⟫_ℝ = 0 := by
    -- Route correction: rewrite the new orthogonality goal back to the original pair `(p, x - p)`.
    simpa [hq_def, hx_sub_q, real_inner_comm] using horth
  have hx_sub_q_polar : x - q ∈ Set.polarCone (Set.negativePolar (K : Set 𝓗)) := by
    -- The point `p ∈ K` lies in the polar cone of the negative polar, exactly as in the source
    -- proof's inclusion `K ⊆ Kᵒ⊖ᵒ⊖`.
    simpa [hx_sub_q] using mem_polarCone_negativePolar_of_mem K hp_mem
  have hq_proj_innerDual :
      q =
        projectionPoint (Set.negativePolar (K : Set 𝓗))
          (properConeProjectionChebyshev (ProperCone.innerDual (- (K : Set 𝓗)))) x := by
    -- Apply Proposition 6.28 in reverse on the proper cone whose carrier is `negativePolar K`.
    exact
      eq_projectionPoint_on_properCone_of_mem_of_inner_eq_zero_of_sub_mem_polarCone
        (ProperCone.innerDual (- (K : Set 𝓗)))
        (by simpa [Set.negativePolar] using hq_mem)
        hq_orth
        hx_sub_q_polar
  have hq_best : IsBestApproximation x (Set.negativePolar (K : Set 𝓗)) q := by
    -- Once `q` is identified as the canonical projection for the inner-dual cone, it is a best
    -- approximation to `x` from `negativePolar K`.
    simpa [Set.negativePolar, hq_proj_innerDual] using
      projectionPoint_isBestApproximation
        (Set.negativePolar (K : Set 𝓗))
        (properConeProjectionChebyshev (ProperCone.innerDual (- (K : Set 𝓗)))) x
  have hq_proj :
      q =
        projectionPoint (Set.negativePolar (K : Set 𝓗))
          (isChebyshev_negativePolar K) x := by
    -- Switch back from the canonical inner-dual witness to this file's Chebyshev witness.
    exact
      eq_projectionPoint_of_isBestApproximation
        (Set.negativePolar (K : Set 𝓗))
        (isChebyshev_negativePolar K)
        hq_best
  -- Rewrite `x` as `p + q`, then replace `q` by the negative-polar projection.
  calc
    x = p + q := by
      rw [hq_def]
      abel
    _ =
        projectionPoint (K : Set 𝓗) (isChebyshev_of_properCone K) x +
          projectionPoint (Set.negativePolar (K : Set 𝓗))
            (isChebyshev_negativePolar K) x := by
      rw [hp_def, hq_proj]

-- Proof sketch: combine Proposition 6.28 with clause (i), which identifies the residual
-- `x - P_K x` with the projection onto the negative polar cone.
/-- Theorem 6.30 (2): textbook clause (ii). The projections of a vector onto a proper cone and its
negative polar cone are orthogonal. -/
theorem inner_projectionPoint_projectionPoint_negativePolar_eq_zero
    (K : ProperCone ℝ 𝓗) (x : 𝓗) :
    ⟪projectionPoint (K : Set 𝓗) (isChebyshev_of_properCone K) x,
        projectionPoint (Set.negativePolar (K : Set 𝓗)) (isChebyshev_negativePolar K) x⟫_ℝ = 0 :=
  by
  set p : 𝓗 := projectionPoint (K : Set 𝓗) (isChebyshev_of_properCone K) x with hp_def
  set q : 𝓗 := projectionPoint (Set.negativePolar (K : Set 𝓗))
      (isChebyshev_negativePolar K) x with hq_def
  have hp_best : IsBestApproximation x (K : Set 𝓗) p := by
    -- The cone projection is again a best approximation, now used to access Proposition 6.28.
    simpa [hp_def] using
      projectionPoint_isBestApproximation
        (K : Set 𝓗) (isChebyshev_of_properCone K) x
  have hp_proj :
      p = projectionPoint (K : Set 𝓗) (properConeProjectionChebyshev K) x := by
    -- Bridge to Proposition 6.28's preferred Chebyshev witness.
    exact
      eq_projectionPoint_of_isBestApproximation
        (K : Set 𝓗) (properConeProjectionChebyshev K) hp_best
  have horth : ⟪x - p, p⟫_ℝ = 0 := by
    -- Proposition 6.28 supplies orthogonality between the cone projection and its residual.
    exact inner_eq_zero_of_eq_projectionPoint_on_properCone K hp_proj
  have hdecomp : x = p + q := by
    -- Clause (i) gives the full decomposition of `x` into its cone and negative-polar parts.
    simpa [hp_def, hq_def] using eq_projectionPoint_add_projectionPoint_negativePolar K x
  have hresidual :
      x - p = q := by
    -- Clause (i) identifies the residual with the projection onto the negative polar cone.
    calc
      x - p = (p + q) - p := by rw [hdecomp]
      _ = q := by abel
  have horth_comm : ⟪p, x - p⟫_ℝ = 0 := by
    -- Commute the inner product so the residual appears in the second slot.
    simpa [real_inner_comm] using horth
  -- Replace the residual in Proposition 6.28 by the negative-polar projection.
  calc
    ⟪projectionPoint (K : Set 𝓗) (isChebyshev_of_properCone K) x,
        projectionPoint (Set.negativePolar (K : Set 𝓗)) (isChebyshev_negativePolar K) x⟫_ℝ =
        ⟪p, q⟫_ℝ := by
      rw [hp_def, hq_def]
    _ = ⟪p, x - p⟫_ℝ := by
      rw [← hresidual]
    _ = 0 := horth_comm

-- Proof sketch: use the orthogonal decomposition from clauses (i) and (ii), then rewrite the two
-- squared norms as the squared distances to `K` and `Kᵒ⊖`.
/-- Theorem 6.30 (3): textbook clause (iii). The squared norm of a vector is the sum of the
squared distances to a proper cone and to its negative polar cone. -/
theorem norm_sq_eq_infDist_sq_add_infDist_sq_negativePolar
    (K : ProperCone ℝ 𝓗) (x : 𝓗) :
    ‖x‖ ^ 2 =
      Metric.infDist x (K : Set 𝓗) ^ 2 +
        Metric.infDist x (Set.negativePolar (K : Set 𝓗)) ^ 2 := by
  set p : 𝓗 := projectionPoint (K : Set 𝓗) (isChebyshev_of_properCone K) x with hp_def
  set q : 𝓗 := projectionPoint (Set.negativePolar (K : Set 𝓗))
      (isChebyshev_negativePolar K) x with hq_def
  have hdecomp : x = p + q := by
    simpa [hp_def, hq_def] using eq_projectionPoint_add_projectionPoint_negativePolar K x
  have horth : ⟪p, q⟫_ℝ = 0 := by
    simpa [hp_def, hq_def] using
      inner_projectionPoint_projectionPoint_negativePolar_eq_zero K x
  have hdist_K : Metric.infDist x (K : Set 𝓗) = ‖q‖ := by
    -- Clause (i) turns the distance to `K` into the norm of the negative-polar projection.
    calc
      Metric.infDist x (K : Set 𝓗) = dist x p := by
        symm
        simpa [hp_def] using
          (projectionPoint_isBestApproximation (K : Set 𝓗) (isChebyshev_of_properCone K) x).2
      _ = ‖x - p‖ := by
        rw [dist_eq_norm]
      _ = ‖q‖ := by
        have hresidual : x - p = q := by
          calc
            x - p = (p + q) - p := by rw [hdecomp]
            _ = q := by abel
        rw [hresidual]
  have hdist_neg : Metric.infDist x (Set.negativePolar (K : Set 𝓗)) = ‖p‖ := by
    -- The same decomposition turns the distance to the negative polar cone into the norm of `P x`.
    calc
      Metric.infDist x (Set.negativePolar (K : Set 𝓗)) = dist x q := by
        symm
        simpa [hq_def] using
          (projectionPoint_isBestApproximation
            (Set.negativePolar (K : Set 𝓗)) (isChebyshev_negativePolar K) x).2
      _ = ‖x - q‖ := by
        rw [dist_eq_norm]
      _ = ‖p‖ := by
        have hcone_part : x - q = p := by
          calc
            x - q = (p + q) - q := by rw [hdecomp]
            _ = p := by abel
        rw [hcone_part]
  -- Expand the orthogonal sum from clause (i), then rewrite each norm by the corresponding
  -- distance furnished by the metric projection characterization.
  calc
    ‖x‖ ^ 2 = ‖p + q‖ ^ 2 := by
      simp [hdecomp]
    _ = ‖p‖ ^ 2 + 2 * ⟪p, q⟫_ℝ + ‖q‖ ^ 2 := by
      simpa using norm_add_sq_real p q
    _ = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
      rw [horth]
      ring
    _ =
        Metric.infDist x (Set.negativePolar (K : Set 𝓗)) ^ 2 +
          Metric.infDist x (K : Set 𝓗) ^ 2 := by
      rw [← hdist_neg, ← hdist_K]
    _ =
        Metric.infDist x (K : Set 𝓗) ^ 2 +
          Metric.infDist x (Set.negativePolar (K : Set 𝓗)) ^ 2 := by
      ring

end
