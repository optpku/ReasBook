/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_49
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] in
/-- Helper for Theorem 7.4: a point of `C` whose norm distance realizes the subtype infimum is a
best approximation in the project API. -/
private theorem isBestApproximation_of_mem_and_norm_eq_iInf {C : Set 𝓗} {x p : 𝓗}
    (hpC : p ∈ C) (hpmin : ‖x - p‖ = ⨅ y : C, ‖x - y‖) : IsBestApproximation x C p := by
  -- Rewrite the metric distance to a set as the subtype infimum from the minimizer theorem.
  constructor
  · exact hpC
  rw [Metric.infDist_eq_iInf]
  simpa [dist_eq_norm] using hpmin

/-- Helper for Theorem 7.4: every point admits at least one best approximation in a nonempty
closed convex set. -/
private theorem exists_isBestApproximation_of_nonempty_isClosed_convex {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ∀ x : 𝓗, ∃ p : 𝓗, IsBestApproximation x C p := by
  intro x
  -- Apply the Hilbert projection theorem and translate its conclusion to `IsBestApproximation`.
  rcases exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_closed.isComplete hC_convex x with
    ⟨p, hpC, hpmin⟩
  exact ⟨p, isBestApproximation_of_mem_and_norm_eq_iInf hpC hpmin⟩

omit [CompleteSpace 𝓗] in
/-- Helper for Theorem 7.4: convexity forces two best approximations to coincide. -/
private theorem eq_of_isBestApproximation_of_convex {C : Set 𝓗} (hC_convex : Convex ℝ C)
    {x p q : 𝓗}
    (hp : IsBestApproximation x C p) (hq : IsBestApproximation x C q) : p = q := by
  -- Rewrite both best-approximation statements to the minimizer equality used by the projection
  -- characterization theorem.
  have hpmin : ‖x - p‖ = ⨅ y : C, ‖x - y‖ := by
    simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hp.2
  have hqmin : ‖x - q‖ = ⨅ y : C, ‖x - y‖ := by
    simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hq.2
  have hp_inner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mp hpmin q hq.1
  have hq_inner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hq.1).mp hqmin p hp.1
  have hq_inner' : 0 ≤ ⟪x - q, q - p⟫_ℝ := by
    rw [show q - p = -(p - q) by abel, inner_neg_right]
    exact neg_nonneg.mpr hq_inner
  have hp_expand :
      ⟪x - p, q - p⟫_ℝ = ⟪x - q, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by
    calc
      ⟪x - p, q - p⟫_ℝ = ⟪(x - q) + (q - p), q - p⟫_ℝ := by
        congr 1
        abel
      _ = ⟪x - q, q - p⟫_ℝ + ⟪q - p, q - p⟫_ℝ := by
        rw [inner_add_left]
      _ = ⟪x - q, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq, sq]
  have hpq_sq : ‖q - p‖ ^ 2 ≤ 0 := by
    rw [hp_expand] at hp_inner
    nlinarith
  have hpq_eq : q - p = 0 := by
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp <| le_antisymm hpq_sq (sq_nonneg ‖q - p‖)
  exact (sub_eq_zero.mp hpq_eq).symm

-- Proof sketch: this is the Hilbert-space projection theorem specialized to nonempty closed convex
-- sets.
/-- A nonempty closed convex subset of a complete real Hilbert space is Chebyshev. -/
theorem isChebyshev_of_nonempty_isClosed_convex {𝓗 : Type u} [NormedAddCommGroup 𝓗]
    [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] {C : Set 𝓗} (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    IsChebyshev C := by
  -- Combine the Hilbert projection theorem for existence with the convex minimizer uniqueness.
  intro x
  rcases exists_isBestApproximation_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex x with
    ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact (eq_of_isBestApproximation_of_convex hC_convex hp hq).symm

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {C : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

/-- Helper for Theorem 7.4: in a convex set, best approximations are exactly the points satisfying
the standard variational inequality. -/
theorem isBestApproximation_iff_mem_and_inner_sub_right_nonpos (hC_convex : Convex ℝ C)
    {x p : 𝓗} :
    IsBestApproximation x C p ↔ p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
  -- Rewrite the metric equality to the minimizer statement packaged by mathlib's projection
  -- characterization.
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
  constructor
  · intro hp
    rw [dist_eq_norm, Metric.infDist_eq_iInf] at hp
    simp_rw [dist_eq_norm] at hp
    have hinner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mp hp.2
    refine ⟨hp.1, ?_⟩
    intro y hy
    simpa [real_inner_comm] using hinner y hy
  · intro hp
    refine ⟨hp.1, ?_⟩
    rw [dist_eq_norm, Metric.infDist_eq_iInf]
    simp_rw [dist_eq_norm]
    refine (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mpr ?_
    intro y hy
    simpa [real_inner_comm] using hp.2 y hy

/-- Helper for Theorem 7.4: the metric projection onto `C` is characterized by the same
variational inequality. -/
theorem eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos {y p : 𝓗} :
    p = P y ↔ p ∈ C ∧ ∀ z ∈ C, ⟪z - p, y - p⟫_ℝ ≤ 0 := by
  -- Reduce the projection statement to the best-approximation characterization proved above.
  constructor
  · intro hp
    exact
      (isBestApproximation_iff_mem_and_inner_sub_right_nonpos
        (hC_convex := hC_convex) (C := C) (x := y) (p := p)).mp <|
        by
          simpa [hp] using
            projectionPoint_isBestApproximation C
              (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y
  · intro hp
    have hp_best : IsBestApproximation y C p :=
      (isBestApproximation_iff_mem_and_inner_sub_right_nonpos
        (hC_convex := hC_convex) (C := C) (x := y) (p := p)).mpr hp
    exact
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex y).unique hp_best
        (projectionPoint_isBestApproximation C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) y)

/-- Helper for Theorem 7.4: a support point is exactly a point of `C` admitting a nonzero support
direction with nonpositive translated inner products on all of `C`. -/
theorem mem_supportPoints_iff_exists_nonzero_inner_sub_right_nonpos {x : 𝓗} :
    x ∈ supportPoints C ↔ x ∈ C ∧ ∃ u : 𝓗, u ≠ 0 ∧ ∀ y ∈ C, ⟪y - x, u⟫_ℝ ≤ 0 := by
  -- Rewrite the support-value equality into pointwise upper bounds and use `x ∈ C` for the
  -- reverse inequality.
  rw [mem_supportPoints_iff]
  constructor
  · rintro ⟨hxC, u, hu_ne, hu_le⟩
    refine ⟨hxC, u, hu_ne, ?_⟩
    intro y hy
    have hy_le : (⟪y, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
      rw [innerSupremumOn_eq_sSup_image]
      exact le_sSup ⟨y, hy, rfl⟩
    have hyx_le : (⟪y, u⟫_ℝ : EReal) ≤ (⟪x, u⟫_ℝ : EReal) := by
      exact hy_le.trans hu_le
    have hyx_le' : ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ := by
      exact_mod_cast hyx_le
    simpa [inner_sub_left] using sub_nonpos.mpr hyx_le'
  · rintro ⟨hxC, u, hu_ne, hu_nonpos⟩
    refine ⟨hxC, u, hu_ne, ?_⟩
    rw [innerSupremumOn_eq_sSup_image]
    refine (isLUB_sSup _).2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hyx_le : ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ := by
      have := hu_nonpos y hy
      simpa [inner_sub_left] using this
    exact show ((⟪y, u⟫_ℝ : EReal) ≤ (⟪x, u⟫_ℝ : EReal)) by
      exact_mod_cast hyx_le

/-- Helper for Theorem 7.4: every support point lies on the frontier of the ambient set. -/
theorem supportPoints_subset_frontier :
    supportPoints C ⊆ frontier C := by
  intro x hx
  rcases
      (mem_supportPoints_iff_exists_nonzero_inner_sub_right_nonpos
        (C := C)).mp hx with
    ⟨hxC, u, hu_ne, hu_nonpos⟩
  rw [mem_frontier_iff_notMem_interior hxC]
  intro hx_int
  -- An interior point would admit a short outward step staying inside `C`, contradicting the
  -- support inequality in the witness direction.
  rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx_int) with ⟨ε, hε_pos, hball_subset⟩
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  let t : ℝ := ε / (2 * ‖u‖)
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have hy_ball : x + t • u ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖(x + t • u) - x‖ = ‖t • u‖ := by
        rw [add_sub_cancel_left]
      _ = |t| * ‖u‖ := norm_smul t u
      _ = t * ‖u‖ := by
        rw [abs_of_pos ht_pos]
      _ = ε / 2 := by
        dsimp [t]
        field_simp [hu_norm_pos.ne']
      _ < ε := by
        linarith
  have hyC : x + t • u ∈ C := hball_subset hy_ball
  have hnonpos : ⟪(x + t • u) - x, u⟫_ℝ ≤ 0 := hu_nonpos (x + t • u) hyC
  have hrewrite : ⟪(x + t • u) - x, u⟫_ℝ = t * ‖u‖ ^ (2 : ℕ) := by
    calc
      ⟪(x + t • u) - x, u⟫_ℝ = ⟪t • u, u⟫_ℝ := by
        congr 1
        abel_nf
      _ = t * ⟪u, u⟫_ℝ := by
        rw [real_inner_smul_left]
      _ = t * ‖u‖ ^ (2 : ℕ) := by
        rw [real_inner_self_eq_norm_sq]
  rw [hrewrite] at hnonpos
  have hpositive : 0 < t * ‖u‖ ^ (2 : ℕ) := by
    refine mul_pos ht_pos ?_
    exact pow_pos hu_norm_pos 2
  linarith

/-- Helper for Theorem 7.4: projection onto `C` does not increase the distance to a point already
in `C`. -/
theorem norm_projectionPoint_sub_le_norm_sub_of_mem (y z : 𝓗) (hz : z ∈ C) :
    ‖P y - z‖ ≤ ‖y - z‖ := by
  have hp :
      P y ∈ C ∧ ∀ w ∈ C, ⟪w - P y, y - P y⟫_ℝ ≤ 0 :=
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
      (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
      (y := y) (p := P y)).mp rfl
  have hinner_nonneg : 0 ≤ ⟪P y - z, y - P y⟫_ℝ := by
    have hz_nonpos : ⟪z - P y, y - P y⟫_ℝ ≤ 0 := hp.2 z hz
    have hneg :
        ⟪z - P y, y - P y⟫_ℝ = -⟪P y - z, y - P y⟫_ℝ := by
      rw [show z - P y = -(P y - z) by abel_nf, inner_neg_left]
    linarith
  have hsplit :
      ⟪P y - z, y - z⟫_ℝ = ‖P y - z‖ ^ (2 : ℕ) + ⟪P y - z, y - P y⟫_ℝ := by
    calc
      ⟪P y - z, y - z⟫_ℝ = ⟪P y - z, (y - P y) + (P y - z)⟫_ℝ := by
        congr 1
        abel_nf
      _ = ⟪P y - z, y - P y⟫_ℝ + ⟪P y - z, P y - z⟫_ℝ := by
        rw [inner_add_right]
      _ = ⟪P y - z, y - P y⟫_ℝ + ‖P y - z‖ ^ (2 : ℕ) := by
        rw [real_inner_self_eq_norm_sq]
      _ = ‖P y - z‖ ^ (2 : ℕ) + ⟪P y - z, y - P y⟫_ℝ := by
        ring
  have hsq_le_inner : ‖P y - z‖ ^ (2 : ℕ) ≤ ⟪P y - z, y - z⟫_ℝ := by
    rw [hsplit]
    nlinarith
  have hsq_le : ‖P y - z‖ ^ (2 : ℕ) ≤ ‖P y - z‖ * ‖y - z‖ := by
    exact le_trans hsq_le_inner (real_inner_le_norm _ _)
  by_cases hzero : ‖P y - z‖ = 0
  · simp [hzero]
  · have hpos : 0 < ‖P y - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    rw [pow_two] at hsq_le
    nlinarith

-- Proof sketch: for `x ∈ supportPoints C`, use Proposition 7.3 to obtain a nonzero normal
-- vector `u ∈ N[C] x \ {0}`. Proposition 6.47 then identifies `x` as the metric projection of
-- `x + u`, and `u ≠ 0` ensures `x + u ∉ C`. Conversely, if `x = P y` with `y ∉ C`, then the
-- residual `y - x` is a nonzero normal vector at `x`, so Proposition 7.3 gives `x ∈ supportPoints
-- C`.
/-- Theorem 7.4 (1): Bishop--Phelps. For a nonempty closed convex subset `C` of a real Hilbert
space, the support points of `C` are exactly the metric projections of points outside `C`,
formalized as `supportPoints C = P '' Cᶜ`. -/
theorem supportPoints_eq_projectionPoint_image_compl :
    supportPoints C = P '' Cᶜ := by
  ext x
  constructor
  · intro hx
    rcases
        (mem_supportPoints_iff_exists_nonzero_inner_sub_right_nonpos
          (C := C)).mp hx with
      ⟨hxC, u, hu_ne, hu_nonpos⟩
    -- Move in the support direction to produce an exterior point whose projection is `x`.
    refine ⟨x + u, ?_, ?_⟩
    · intro hxuC
      have hnonpos : ⟪(x + u) - x, u⟫_ℝ ≤ 0 := hu_nonpos (x + u) hxuC
      have hrewrite : ⟪(x + u) - x, u⟫_ℝ = ‖u‖ ^ (2 : ℕ) := by
        calc
          ⟪(x + u) - x, u⟫_ℝ = ⟪u, u⟫_ℝ := by
            congr 1
            abel_nf
          _ = ‖u‖ ^ (2 : ℕ) := by
            rw [real_inner_self_eq_norm_sq]
      rw [hrewrite] at hnonpos
      have hpositive : 0 < ‖u‖ ^ (2 : ℕ) := by
        exact pow_pos (norm_pos_iff.mpr hu_ne) 2
      linarith
    · have hx_proj : x = P (x + u) := by
        refine
          (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
            (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
            (y := x + u) (p := x)).mpr ?_
        refine ⟨hxC, ?_⟩
        intro z hz
        have hz_nonpos : ⟪z - x, u⟫_ℝ ≤ 0 := hu_nonpos z hz
        simpa using hz_nonpos
      simpa using hx_proj.symm
  · rintro ⟨y, hy_out, hy_proj⟩
    have hx_proj : x = P y := by
      simpa using hy_proj.symm
    have hproj :
        x ∈ C ∧ ∀ z ∈ C, ⟪z - x, y - x⟫_ℝ ≤ 0 :=
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
        (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex)
        (y := y) (p := x)).mp hx_proj
    have hyx_ne : y - x ≠ 0 := by
      intro hyx_zero
      have hy_eq : y = x := sub_eq_zero.mp hyx_zero
      exact hy_out (hy_eq.symm ▸ hproj.1)
    -- The projection residual is a nonzero support direction at `x`.
    exact
      (mem_supportPoints_iff_exists_nonzero_inner_sub_right_nonpos
        (C := C)).mpr
        ⟨hproj.1, y - x, hyx_ne, hproj.2⟩

-- Proof sketch: the first clause shows that every support point is the projection of some point
-- outside `C`, hence lies on `frontier C`; this gives `closure (supportPoints C) ⊆ frontier C`.
-- For the reverse inclusion, approximate a boundary point by points of `Cᶜ`, project them onto
-- `C`, apply the first clause to land in `supportPoints C`, and use nonexpansiveness of the metric
-- projection to pass to the limit.
/-- Theorem 7.4 (2): Bishop--Phelps. The closure of the support points of a nonempty closed convex
subset `C` of a real Hilbert space is the boundary of `C`, formalized as
`closure (supportPoints C) = frontier C`. -/
theorem closure_supportPoints_eq_frontier (hC_nonempty' : C.Nonempty) (hC_closed' : IsClosed C)
    (hC_convex' : Convex ℝ C) :
    closure (supportPoints C) = frontier C := by
  let P' :=
    projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty' hC_closed' hC_convex')
  apply Subset.antisymm
  · -- The frontier is closed, so the support-point inclusion upgrades to their closure.
    exact
      closure_minimal
        (supportPoints_subset_frontier (C := C))
        isClosed_frontier
  · intro z hz
    rw [frontier_eq_closure_inter_closure] at hz
    have hzC : z ∈ C := by
      simpa [IsClosed.closure_eq hC_closed'] using hz.1
    -- Approximate the boundary point by exterior points and project them back onto `C`.
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases Metric.mem_closure_iff.1 hz.2 ε hε with ⟨y, hy_out, hy_dist⟩
    let p := P' y
    have hp_support : p ∈ supportPoints C := by
      rw [supportPoints_eq_projectionPoint_image_compl
        (hC_nonempty := hC_nonempty') (hC_closed := hC_closed') (hC_convex := hC_convex')]
      exact ⟨y, hy_out, rfl⟩
    have hp_dist : ‖p - z‖ < ε := by
      have hproj_le :
          ‖P' y - z‖ ≤ ‖y - z‖ :=
        norm_projectionPoint_sub_le_norm_sub_of_mem
          (hC_nonempty := hC_nonempty') (hC_closed := hC_closed') (hC_convex := hC_convex') y z hzC
      have hy_norm_lt : ‖y - z‖ < ε := by
        simpa [dist_eq_norm, norm_sub_rev] using hy_dist
      exact lt_of_le_of_lt hproj_le hy_norm_lt
    exact ⟨p, hp_support, by simpa [p, dist_eq_norm, norm_sub_rev] using hp_dist⟩

end

end Set
