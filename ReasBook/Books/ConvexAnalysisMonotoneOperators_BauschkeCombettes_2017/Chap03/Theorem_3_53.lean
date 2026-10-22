/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_49

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open Filter

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
  [FiniteDimensional ℝ 𝓗]

omit [FiniteDimensional ℝ 𝓗] in
/-- Helper for Theorem 3.53: any nonzero vector with pointwise strict separation can be normalized
to unit norm while preserving those strict inequalities. -/
private lemma unit_separator_of_pointwise_strict {C D : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (hpoint : ∃ u : 𝓗, ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ < ⟪y, u⟫_ℝ) :
    ∃ v : 𝓗, ‖v‖ = 1 ∧ ∀ x ∈ C, ∀ y ∈ D, ⟪x, v⟫_ℝ < ⟪y, v⟫_ℝ := by
  -- Extract a pointwise strict separator and show it is nonzero by evaluating it on one pair of points.
  rcases hpoint with ⟨u, hu_point⟩
  obtain ⟨x0, hx0⟩ := hC_nonempty
  obtain ⟨y0, hy0⟩ := hD_nonempty
  have hu_ne : u ≠ 0 := by
    intro hu0
    have : (0 : ℝ) < 0 := by
      simpa [hu0] using hu_point x0 hx0 y0 hy0
    exact lt_irrefl _ this
  -- Rescale the normal vector to norm one; positivity of the scale preserves the strict inequalities.
  let v : 𝓗 := ‖u‖⁻¹ • u
  have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hv_norm : ‖v‖ = 1 := by
    simp [v, norm_smul, hnorm_pos.ne']
  refine ⟨v, hv_norm, ?_⟩
  intro x hx y hy
  have hu_lt : ⟪x, u⟫_ℝ < ⟪y, u⟫_ℝ := hu_point x hx y hy
  simp only [v, inner_smul_right]
  nlinarith [hu_lt, inv_pos.mpr hnorm_pos]

omit [FiniteDimensional ℝ 𝓗] in
/-- Helper for Theorem 3.53: eventual strict separation inequalities along a convergent subsequence
pass to a weak inequality at the limit. -/
private lemma inner_le_of_eventually_lt_along_subseq {v : ℕ → 𝓗} {φ : ℕ → ℕ} {u x y : 𝓗}
    (hvu : Tendsto (fun n ↦ v (φ n)) atTop (nhds u))
    (hevent : ∀ᶠ n in atTop, ⟪x, v (φ n)⟫_ℝ < ⟪y, v (φ n)⟫_ℝ) :
    ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
  -- Apply continuity of the inner product to both coordinate functionals.
  have hx_tendsto : Tendsto (fun n ↦ ⟪x, v (φ n)⟫_ℝ) atTop (nhds ⟪x, u⟫_ℝ) :=
    ((continuous_const.inner continuous_id).tendsto u).comp hvu
  have hy_tendsto : Tendsto (fun n ↦ ⟪y, v (φ n)⟫_ℝ) atTop (nhds ⟪y, u⟫_ℝ) :=
    ((continuous_const.inner continuous_id).tendsto u).comp hvu
  -- The order is closed, so eventual strict inequalities yield a weak inequality at the limit.
  exact le_of_tendsto_of_tendsto hx_tendsto hy_tendsto (hevent.mono fun n hn ↦ hn.le)

-- Proof sketch: intersect `D` with larger and larger closed balls to obtain nonempty compact convex
-- truncations, separate `C` from each truncation by the compact/closed separation theorem, and then
-- extract a convergent subsequence of unit normal vectors using finite dimensionality.
/-- Theorem 3.53: in a finite-dimensional real Hilbert space, two nonempty closed convex sets with
empty intersection are separated in the sense of `AreSeparated`. -/
theorem finiteDimensional_closed_convex_areSeparated_of_disjoint
    {C D : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hCD : Disjoint C D) :
    AreSeparated C D := by
  classical
  obtain ⟨y0, hy0D⟩ := hD_nonempty
  let Dn : ℕ → Set 𝓗 := fun n ↦ D ∩ Metric.closedBall y0 (n : ℝ)
  -- Exhaust `D` by bounded closed convex truncations centered at a fixed point of `D`.
  have hDn_nonempty : ∀ n, (Dn n).Nonempty := by
    intro n
    refine ⟨y0, hy0D, ?_⟩
    simp [Metric.mem_closedBall]
  have hDn_closed : ∀ n, IsClosed (Dn n) := by
    intro n
    exact hD_closed.inter
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall y0 (n : ℝ)))
  have hDn_convex : ∀ n, Convex ℝ (Dn n) := by
    intro n
    exact hD_convex.inter (convex_closedBall y0 (n : ℝ))
  have hDn_compact : ∀ n, IsCompact (Dn n) := by
    intro n
    exact (isCompact_closedBall y0 (n : ℝ)).of_isClosed_subset (hDn_closed n) fun z hz ↦ hz.2
  have hDn_disjoint : ∀ n, Disjoint C (Dn n) := by
    intro n
    exact hCD.inter_right (Metric.closedBall y0 (n : ℝ))
  -- Apply mathlib's compact/closed Hahn-Banach separation theorem to each truncation, then convert
  -- the separating functional to an inner-product vector using Riesz representation.
  have hstrict : ∀ n, ∃ u : 𝓗, ∀ x ∈ C, ∀ y ∈ Dn n, ⟪x, u⟫_ℝ < ⟪y, u⟫_ℝ := by
    intro n
    obtain ⟨f, a, b, hCside, hab, hDside⟩ :=
      geometric_hahn_banach_closed_compact hC_convex hC_closed (hDn_convex n) (hDn_compact n)
        (hDn_disjoint n)
    let u : 𝓗 := (InnerProductSpace.toDual ℝ 𝓗).symm f
    refine ⟨u, ?_⟩
    intro x hx y hy
    have hxy : f x < f y := lt_trans (hCside x hx) (lt_trans hab (hDside y hy))
    have hx_eval : f x = ⟪u, x⟫_ℝ := by
      simp [u]
    have hy_eval : f y = ⟪u, y⟫_ℝ := by
      simp [u]
    have hu_lt : ⟪u, x⟫_ℝ < ⟪u, y⟫_ℝ := by
      simpa [hx_eval, hy_eval] using hxy
    change ⟪x, u⟫_ℝ < ⟪y, u⟫_ℝ
    rw [real_inner_comm u x, real_inner_comm u y]
    exact hu_lt
  choose v hv_norm hv_lt using fun n ↦
    unit_separator_of_pointwise_strict hC_nonempty (hDn_nonempty n) (hstrict n)
  have hv_mem : ∀ n, v n ∈ Metric.closedBall (0 : 𝓗) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [hv_norm n]
  -- Extract a convergent subsequence of unit normals from the bounded sequence.
  obtain ⟨u, -, φ, hφmono, hφtendsto⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hv_mem
  have hu_norm : ‖u‖ = 1 := by
    have hnorm_tendsto : Tendsto (fun n ↦ ‖v (φ n)‖) atTop (nhds ‖u‖) := hφtendsto.norm
    have hconst : Tendsto (fun n ↦ ‖v (φ n)‖) atTop (nhds 1) := by
      refine tendsto_const_nhds.congr' ?_
      exact Filter.Eventually.of_forall fun n ↦ by simp [hv_norm (φ n)]
    exact tendsto_nhds_unique hnorm_tendsto hconst
  have hu_ne : u ≠ 0 := by
    intro hu0
    simp [hu0] at hu_norm
  -- For fixed `x ∈ C` and `y ∈ D`, the truncations eventually contain `y`, so the strict
  -- subsequence inequalities pass to the limit.
  have hlimit : ∀ x ∈ C, ∀ y ∈ D, ⟪x, u⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
    intro x hx y hy
    have hy_event : ∀ᶠ n in atTop, y ∈ Dn (φ n) := by
      let N : ℕ := ⌈dist y0 y⌉₊
      filter_upwards [eventually_ge_atTop N] with n hn
      change y ∈ D ∩ Metric.closedBall y0 (φ n : ℝ)
      refine ⟨hy, ?_⟩
      rw [Metric.mem_closedBall, dist_comm]
      calc
        dist y0 y ≤ N := Nat.le_ceil _
        _ ≤ n := by exact_mod_cast hn
        _ ≤ φ n := by exact_mod_cast (hφmono.id_le n)
    have hstrict_event : ∀ᶠ n in atTop, ⟪x, v (φ n)⟫_ℝ < ⟪y, v (φ n)⟫_ℝ := by
      exact hy_event.mono fun n hyn ↦ hv_lt (φ n) x hx y hyn
    exact inner_le_of_eventually_lt_along_subseq hφtendsto hstrict_event
  -- Convert the pointwise inequalities for the limit vector into the definition of separation.
  exact areSeparated_of_forall_inner_le hu_ne hlimit
