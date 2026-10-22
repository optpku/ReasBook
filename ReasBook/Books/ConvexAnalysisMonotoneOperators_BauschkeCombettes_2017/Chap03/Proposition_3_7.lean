/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

-- Proof sketch: if `C` contained distinct points `x` and `y`, convexity would place their midpoint
-- in `C`; applying `norm_combo_lt_of_ne` to the coefficients `1 / 2` and `1 / 2` would then force
-- the midpoint to have norm strictly less than the common radius `(β : ℝ)`, contradicting the
-- constant-norm hypothesis. Use `hC_nonempty` together with `Set.Subsingleton.eq_singleton_of_mem`
-- to turn the resulting subsingleton conclusion into an equality `C = {z}`.
/- The midpoint norm computation is local proof scaffolding for Proposition 3.7. -/
private lemma midpoint_norm_eq_radius_of_mem
    (C : Set 𝓗) (β : NNReal) (hC_convex : Convex ℝ C)
    (hC_norm : ∀ x ∈ C, ‖x‖ = (β : ℝ)) {x y : 𝓗}
    (hx : x ∈ C) (hy : y ∈ C) : ‖midpoint ℝ x y‖ = (β : ℝ) := by
  -- Convexity keeps the midpoint inside `C`, so the constant-norm hypothesis applies there.
  exact hC_norm _ (hC_convex.midpoint_mem hx hy)

/- Distinct points of a common sphere have midpoint of strictly smaller norm. -/
private lemma midpoint_norm_lt_radius_of_ne_mem
    (C : Set 𝓗) (β : NNReal) (hC_norm : ∀ x ∈ C, ‖x‖ = (β : ℝ)) {x y : 𝓗}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) : ‖midpoint ℝ x y‖ < (β : ℝ) := by
  have h_norm_eq : ‖x‖ = ‖y‖ := by
    -- Both endpoints lie on the same sphere of radius `(β : ℝ)`.
    rw [hC_norm x hx, hC_norm y hy]
  have h_midpoint_lt : ‖(1 / 2 : ℝ) • (x + y)‖ < ‖x‖ :=
      (norm_midpoint_lt_iff h_norm_eq).2 hxy
  -- Rewrite the midpoint and the endpoint norm into the radius `(β : ℝ)`.
  simpa [midpoint_eq_smul_add, hC_norm x hx] using h_midpoint_lt

/-- A convex subset of a real Hilbert space on which the norm is constantly `(β : ℝ)` is
subsingleton. -/
theorem subsingleton_of_convex_of_forall_norm_eq
    (C : Set 𝓗) (β : NNReal) (hC_convex : Convex ℝ C)
    (hC_norm : ∀ x ∈ C, ‖x‖ = (β : ℝ)) : C.Subsingleton := by
  intro x hx y hy
  -- Distinct points would give a midpoint with two incompatible norm estimates.
  by_contra hxy
  have h_midpoint_eq :
      ‖midpoint ℝ x y‖ = (β : ℝ) :=
    midpoint_norm_eq_radius_of_mem C β hC_convex hC_norm hx hy
  have h_midpoint_lt :
      ‖midpoint ℝ x y‖ < (β : ℝ) :=
    midpoint_norm_lt_radius_of_ne_mem C β hC_norm hx hy hxy
  exact (lt_irrefl (β : ℝ)) (h_midpoint_eq ▸ h_midpoint_lt)

/-- Proposition 3.7: a nonempty convex subset of a real Hilbert space on which every point has the
same norm `(β : ℝ)` is a singleton. -/
theorem exists_eq_singleton_of_nonempty_convex_of_forall_norm_eq
    (C : Set 𝓗) (β : NNReal) (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C)
    (hC_norm : ∀ x ∈ C, ‖x‖ = (β : ℝ)) : ∃ z : 𝓗, C = {z} := by
  rcases hC_nonempty with ⟨z, hz⟩
  -- Once `C` is known to be subsingleton, any point of `C` determines the whole set.
  refine ⟨z, ?_⟩
  exact (subsingleton_of_convex_of_forall_norm_eq C β hC_convex hC_norm).eq_singleton_of_mem hz
