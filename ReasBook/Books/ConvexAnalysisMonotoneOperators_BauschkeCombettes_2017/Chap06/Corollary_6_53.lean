/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_48

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology InnerProductSpace Pointwise

universe u

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Corollary 6.53: translating a point of `C` repeatedly by a recession direction keeps
the whole natural ray inside `C`. -/
lemma nat_ray_point_mem_of_mem_recessionCone_basic {C : Set 𝓗} {x y : 𝓗}
    (hx : x ∈ rec C) (hy : y ∈ C) :
    ∀ n : ℕ, ((n : ℝ) • x + y) ∈ C := by
  intro n
  induction n with
  | zero =>
      simpa using hy
  | succ n ihn =>
      have hstep : x + ((n : ℝ) • x + y) ∈ C := by
        exact (mem_recessionCone_iff.1 hx) (Set.mem_add.2 ⟨x, by simp, (n : ℝ) • x + y, ihn, rfl⟩)
      simpa [Nat.cast_add, add_smul, one_smul, add_assoc, add_left_comm, add_comm] using hstep

/-- Helper for Corollary 6.53: every recession direction admits an explicit strong approximation by
points of `cone C`, hence belongs to the closure of `cone C`. -/
lemma mem_closure_cone_of_mem_recessionCone {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C)
    {x : 𝓗} (hx : x ∈ rec C) :
    x ∈ closure (cone C) := by
  rcases hC_nonempty with ⟨y, hy⟩
  let z : ℕ → 𝓗 := fun n ↦ (1 / ((n : ℝ) + 1)) • ((((n + 1 : ℕ) : ℝ) • x) + y)
  have hz_mem : ∀ n, z n ∈ cone C := by
    intro n
    have hray_mem : ((((n + 1 : ℕ) : ℝ) • x) + y) ∈ C :=
      nat_ray_point_mem_of_mem_recessionCone_basic hx hy (n + 1)
    -- Each approximating point is a positive multiple of a point in `C`, hence lies in `cone C`.
    simpa [z, Nat.cast_add] using
      (ConvexCone.mem_hull_of_convex hC_convex).2
        ⟨1 / ((n : ℝ) + 1), by positivity,
          Set.mem_smul_set.mpr ⟨(((n + 1 : ℕ) : ℝ) • x + y), hray_mem, rfl⟩⟩
  have hα_tendsto : Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa [Nat.cast_add] using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (0 : ℝ)))
  have hz_model :
      z = fun n : ℕ ↦ x + (1 / (n + 1 : ℝ)) • y := by
    funext n
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
      norm_num [Nat.cast_add]
    have hmul : (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = 1 := by
      field_simp
    calc
      z n = (1 / ((n : ℝ) + 1)) • ((((n + 1 : ℕ) : ℝ) • x) + y) := rfl
      _ = ((1 / ((n : ℝ) + 1)) * (((n + 1 : ℕ) : ℝ))) • x + (1 / ((n : ℝ) + 1)) • y := by
        rw [smul_add, smul_smul]
      _ = x + (1 / (n + 1 : ℝ)) • y := by
        rw [hcast, hmul]
        simp
  have hy_tendsto : Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ)) • y) atTop (𝓝 ((0 : ℝ) • y)) := by
    simpa using hα_tendsto.smul_const y
  have hz_tendsto : Tendsto z atTop (𝓝 x) := by
    rw [hz_model]
    simpa using tendsto_const_nhds.add hy_tendsto
  -- The explicit recession-ray model sequence converges strongly to `x`.
  exact mem_closure_of_tendsto hz_tendsto (Eventually.of_forall hz_mem)

/-- Helper for Corollary 6.53: if `α n • y n` converges and `0 ∉ C`, then the positive
coefficients `α n` are uniformly bounded above. -/
lemma bddAbove_coefficients_of_tendsto_smul_of_zero_not_mem {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (h0C : (0 : 𝓗) ∉ C) {x : 𝓗}
    {y : ℕ → 𝓗} {α : ℕ → ℝ} (hyC : ∀ n, y n ∈ C) (hα_pos : ∀ n, 0 < α n)
    (hz_tendsto : Tendsto (fun n ↦ α n • y n) atTop (𝓝 x)) :
    BddAbove (Set.range α) := by
  let d : ℝ := Metric.infDist (0 : 𝓗) C
  have hd_pos : 0 < d := by
    exact (hC_closed.notMem_iff_infDist_pos hC_nonempty).1 h0C
  have hz_bdd : Bornology.IsBounded (Set.range fun n ↦ α n • y n) :=
    Metric.isBounded_range_of_tendsto _ hz_tendsto
  obtain ⟨R, hR_pos, hR⟩ := hz_bdd.subset_closedBall_lt 0 (0 : 𝓗)
  refine ⟨R / d, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hd_le_norm : d ≤ ‖y n‖ := by
    have hdist : Metric.infDist (0 : 𝓗) C ≤ dist (0 : 𝓗) (y n) :=
      Metric.infDist_le_dist_of_mem (hyC n)
    simpa [d, dist_eq_norm] using hdist
  have hz_norm_le : ‖α n • y n‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR ⟨n, rfl⟩
  have hmul_le : α n * d ≤ R := by
    have hα_nonneg : 0 ≤ α n := (hα_pos n).le
    have hmul_compare : α n * d ≤ α n * ‖y n‖ := by
      gcongr
    have hz_norm_eq : ‖α n • y n‖ = α n * ‖y n‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hα_pos n)]
    exact le_trans hmul_compare (hz_norm_eq ▸ hz_norm_le)
  exact (le_div_iff₀ hd_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_le)

/-- Helper for Corollary 6.53: a positive scaled sequence converging strongly to `x` with
coefficients tending to `0` yields `x ∈ rec C` after tail-shifting into `]0, 1]`. -/
lemma mem_recessionCone_of_tendsto_zero_pos_smul {C : Set 𝓗}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {x : 𝓗}
    {y : ℕ → 𝓗} {α : ℕ → ℝ} (hyC : ∀ n, y n ∈ C) (hα_pos : ∀ n, 0 < α n)
    (hα_tendsto : Tendsto α atTop (𝓝 (0 : ℝ)))
    (hz_tendsto : Tendsto (fun n ↦ α n • y n) atTop (𝓝 x)) :
    x ∈ rec C := by
  rw [mem_recessionCone_iff]
  have hα_lt_one : ∀ᶠ n in atTop, α n < 1 := by
    exact hα_tendsto (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hα_lt_one
  have hshift : Tendsto (fun n : ℕ ↦ n + N) atTop atTop := Filter.tendsto_add_atTop_nat N
  intro z hz
  rcases Set.mem_add.1 hz with ⟨w, hw, v, hv, rfl⟩
  have hwx : w = x := by simpa using hw
  subst w
  let u : ℕ → 𝓗 := fun n ↦ α (n + N) • y (n + N) + (1 - α (n + N)) • v
  have hu_mem : ∀ n, u n ∈ C := by
    intro n
    have hα_nonneg : 0 ≤ α (n + N) := (hα_pos (n + N)).le
    have hOneSub_nonneg : 0 ≤ 1 - α (n + N) := by
      linarith [hN (n + N) (Nat.le_add_left N n)]
    -- The tail coefficients now lie in `[0, 1]`, so each `u n` is a convex combination in `C`.
    exact (convex_iff_add_mem.1 hC_convex) (hyC (n + N)) hv hα_nonneg hOneSub_nonneg (by ring)
  have hfirst_tendsto : Tendsto (fun n ↦ α (n + N) • y (n + N)) atTop (𝓝 x) := by
    simpa using hz_tendsto.comp hshift
  have hcoeff_tendsto : Tendsto (fun n ↦ 1 - α (n + N)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (hα_tendsto.comp hshift)
  have hsecond_tendsto : Tendsto (fun n ↦ (1 - α (n + N)) • v) atTop (𝓝 v) := by
    simpa using hcoeff_tendsto.smul_const v
  have hu_tendsto : Tendsto u atTop (𝓝 (x + v)) := by
    -- The first term converges to `x` and the complementary convex weight converges to `1`.
    simpa [u] using hfirst_tendsto.add hsecond_tendsto
  exact hC_closed.mem_of_tendsto hu_tendsto (Eventually.of_forall hu_mem)

/-- Helper for Corollary 6.53: if the positive coefficients converge to a positive limit, then the
unscaled points converge to a point of `C`, so the limit lies in `cone C`. -/
lemma mem_cone_of_tendsto_pos_limit_smul {C : Set 𝓗}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {a : ℝ} {u : 𝓗} {y : ℕ → 𝓗} {α : ℕ → ℝ}
    (hyC : ∀ n, y n ∈ C) (hα_pos : ∀ n, 0 < α n) (hα_tendsto : Tendsto α atTop (𝓝 a))
    (ha : 0 < a) (hz_tendsto : Tendsto (fun n ↦ α n • y n) atTop (𝓝 u)) :
    u ∈ cone C := by
  have hαinv_tendsto : Tendsto (fun n ↦ (α n)⁻¹) atTop (𝓝 a⁻¹) :=
    (tendsto_inv₀ ha.ne').comp hα_tendsto
  have hy_tendsto : Tendsto y atTop (𝓝 (a⁻¹ • u)) := by
    have hy_eq : y = fun n ↦ (α n)⁻¹ • (α n • y n) := by
      funext n
      rw [inv_smul_smul₀ (hα_pos n).ne']
    rw [hy_eq]
    exact hαinv_tendsto.smul hz_tendsto
  have hlimit_mem : a⁻¹ • u ∈ C := by
    -- Closedness returns the strong limit of the subsequence of points in `C`.
    exact hC_closed.mem_of_tendsto hy_tendsto (Eventually.of_forall hyC)
  -- Repackage `u = a • (a⁻¹ • u)` with a positive scalar and a point of `C`.
  simpa [Set.cone] using
    (ConvexCone.mem_hull_of_convex hC_convex).2
      ⟨a, ha, Set.mem_smul_set.mpr ⟨a⁻¹ • u, hlimit_mem, by
        rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]⟩⟩

-- Proof sketch: the inclusion `cone C ⊆ closure (cone C)` is immediate. For
-- `rec C ⊆ closure (cone C)`, use the explicit recession-ray sequence
-- `(1 / (n + 1)) • (((n + 1) • x) + y)` with `y ∈ C`. For the reverse inclusion, start from a
-- convergent sequence in `cone C`, decompose each term as a positive multiple of a point in `C`,
-- bound the coefficients away from `+∞` using the positive distance from `0` to `C`, and split on
-- the subsequential coefficient limit.
/-- Corollary 6.53: if `C` is a nonempty closed convex subset of a real inner-product space and
`0 ∉ C`, then `cone C ∪ rec C` is the closure of `cone C`. -/
theorem cone_union_recessionCone_eq_closure_cone_of_nonempty_isClosed_convex_zero_not_mem
    (C : Set 𝓗) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (h0C : (0 : 𝓗) ∉ C) :
    cone C ∪ rec C = closure (cone C) := by
  apply le_antisymm
  · intro x hx
    rcases hx with hx | hx
    · -- The cone is contained in its own closure.
      exact subset_closure hx
    · -- Recession directions admit an explicit strong approximation by cone points.
      exact mem_closure_cone_of_mem_recessionCone hC_nonempty hC_convex hx
  · intro x hx
    rcases mem_closure_iff_seq_limit.mp hx with ⟨z, hz_mem, hz_tendsto⟩
    have hz_repr : ∀ n, ∃ a : ℝ, 0 < a ∧ ∃ y ∈ C, z n = a • y := by
      intro n
      rcases (ConvexCone.mem_hull_of_convex hC_convex).1 (by simpa [Set.cone] using hz_mem n) with
        ⟨a, ha, hzsmul⟩
      rcases Set.mem_smul_set.mp hzsmul with ⟨y, hy, hyEq⟩
      exact ⟨a, ha, y, hy, hyEq.symm⟩
    choose α hα_pos y hyC hz_eq using hz_repr
    have hz_fun : z = fun n ↦ α n • y n := by
      funext n
      exact hz_eq n
    have hscaled_tendsto : Tendsto (fun n ↦ α n • y n) atTop (𝓝 x) := by
      simpa [hz_fun] using hz_tendsto
    have hα_bdd :
        BddAbove (Set.range α) :=
      bddAbove_coefficients_of_tendsto_smul_of_zero_not_mem (C := C) hC_nonempty hC_closed h0C
        (y := y) (α := α) hyC hα_pos hscaled_tendsto
    rcases hα_bdd with ⟨M, hM⟩
    have hM_pos : 0 < M := lt_of_lt_of_le (hα_pos 0) (hM ⟨0, rfl⟩)
    have hα_mem_ball : ∀ n, α n ∈ Metric.closedBall (0 : ℝ) M := by
      intro n
      rw [Metric.mem_closedBall, Real.dist_eq]
      simpa [abs_of_nonneg (hα_pos n).le] using hM ⟨n, rfl⟩
    obtain ⟨a, -, φ, hφ, hα_subseq⟩ :=
      tendsto_subseq_of_bounded Metric.isBounded_closedBall hα_mem_ball
    have ha_nonneg : 0 ≤ a := by
      exact isClosed_Ici.mem_of_tendsto hα_subseq
        (Eventually.of_forall fun n ↦ (hα_pos (φ n)).le)
    have hscaled_subseq : Tendsto (fun n ↦ α (φ n) • y (φ n)) atTop (𝓝 x) := by
      simpa using hscaled_tendsto.comp hφ.tendsto_atTop
    by_cases ha_zero : a = 0
    · -- When the coefficient limit is `0`, the tail convex-combination argument yields `x ∈ rec C`.
      have hx_rec : x ∈ rec C :=
        mem_recessionCone_of_tendsto_zero_pos_smul hC_closed hC_convex
          (fun n ↦ hyC (φ n)) (fun n ↦ hα_pos (φ n)) (by simpa [ha_zero] using hα_subseq)
          hscaled_subseq
      exact Or.inr hx_rec
    · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (Ne.symm ha_zero)
      -- When the coefficient limit is positive, divide out the limit and land back in `cone C`.
      have hx_cone : x ∈ cone C :=
        mem_cone_of_tendsto_pos_limit_smul hC_closed hC_convex (fun n ↦ hyC (φ n))
          (fun n ↦ hα_pos (φ n)) hα_subseq ha_pos hscaled_subseq
      exact Or.inl hx_cone

end

end Set
