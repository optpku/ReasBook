/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 5.7: distances from a Fejér-monotone sequence to a point of `C`
decrease along every tail. -/
private lemma dist_le_dist_of_fejerMonotone_le
    (xₙ : ℕ → H) (hxₙ : FejerMonotone C xₙ) {c : H} (hc : c ∈ C) {n m : ℕ} (hnm : n ≤ m) :
    dist (xₙ m) c ≤ dist (xₙ n) c := by
  -- Upgrade the one-step Fejér inequality to an antitone distance sequence.
  have hanti : Antitone fun k ↦ dist (xₙ k) c := by
    exact antitone_nat_of_succ_le (fun k ↦ hxₙ.step c hc k)
  exact hanti hnm

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 5.7: the distance-to-`C` function decreases along a Fejér-monotone
sequence. -/
private theorem infDist_antitone_of_fejerMonotone
    (hC_nonempty : C.Nonempty) (xₙ : ℕ → H) (hxₙ : FejerMonotone C xₙ) :
    Antitone (fun n ↦ Metric.infDist (xₙ n) C) := by
  have hinf_succ : ∀ n, Metric.infDist (xₙ (n + 1)) C ≤ Metric.infDist (xₙ n) C := by
    intro n
    refine (Metric.le_infDist hC_nonempty).2 (fun x hx ↦ ?_)
    exact (Metric.infDist_le_dist_of_mem hx).trans (hxₙ.step x hx n)
  exact antitone_nat_of_succ_le hinf_succ

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 5.7: the distance-to-`C` energy of a Fejér-monotone sequence converges.
-/
private theorem infDist_tendsto_of_fejerMonotone
    (hC_nonempty : C.Nonempty) (xₙ : ℕ → H) (hxₙ : FejerMonotone C xₙ) :
    ∃ l : ℝ, Tendsto (fun n ↦ Metric.infDist (xₙ n) C) atTop (𝓝 l) := by
  refine ⟨sInf ((fun n ↦ Metric.infDist (xₙ n) C) '' Set.Ici 0), ?_⟩
  -- Apply real monotone convergence to the antitone distance-to-set sequence.
  refine Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici (k := 0) ?_ ?_
  · intro m hm n hn hmn
    exact (infDist_antitone_of_fejerMonotone hC_nonempty xₙ hxₙ) hmn
  · refine ⟨0, ?_⟩
    rintro _ ⟨n, hn, rfl⟩
    exact Metric.infDist_nonneg

/-- Helper for Proposition 5.7: the squared gap between two projection shadows is controlled by the
drop in the squared distance-to-`C` energy. -/
private theorem shadow_gap_sq_le_infDist_sq_sub
    (xₙ : ℕ → H) (hxₙ : FejerMonotone C xₙ) (n m : ℕ) :
    ‖P (xₙ n) - P (xₙ (n + m))‖ ^ 2 ≤
      Metric.infDist (xₙ n) C ^ 2 - Metric.infDist (xₙ (n + m)) C ^ 2 := by
  let pn := P (xₙ n)
  let pm := P (xₙ (n + m))
  have hpnC : pn ∈ C := by
    simp [pn]
  have hpmC : pm ∈ C := by
    simp [pm]
  -- Fejér monotonicity compares the tail point `xₙ (n + m)` to the earlier shadow `pn`.
  have hfejer :
      ‖xₙ (n + m) - pn‖ ≤ ‖xₙ n - pn‖ := by
    simpa [pn, dist_eq_norm] using
      dist_le_dist_of_fejerMonotone_le
        (xₙ := xₙ) hxₙ hpnC (Nat.le_add_right n m)
  -- The projection variational inequality makes the cross term nonnegative.
  have hcross_nonneg : 0 ≤ ⟪xₙ (n + m) - pm, pm - pn⟫_ℝ := by
    have hinner :
        ⟪pn - pm, xₙ (n + m) - pm⟫_ℝ ≤ 0 := by
      exact
        ((eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
            hC_nonempty hC_closed hC_convex).mp rfl).2 pn hpnC
    have hinner' :
        ⟪xₙ (n + m) - pm, pn - pm⟫_ℝ ≤ 0 := by
      simpa [real_inner_comm] using hinner
    have hrewrite :
        ⟪xₙ (n + m) - pm, pm - pn⟫_ℝ =
          -⟪xₙ (n + m) - pm, pn - pm⟫_ℝ := by
      rw [show pm - pn = -(pn - pm) by abel_nf, inner_neg_right]
    rw [hrewrite]
    exact neg_nonneg.mpr hinner'
  -- Expand the distance to `pn` through the later projection `pm`.
  have hsq_expand :
      ‖xₙ (n + m) - pn‖ ^ 2 =
        ‖xₙ (n + m) - pm‖ ^ 2 +
          2 * ⟪xₙ (n + m) - pm, pm - pn⟫_ℝ + ‖pm - pn‖ ^ 2 := by
    have hdecomp : xₙ (n + m) - pn = (xₙ (n + m) - pm) + (pm - pn) := by
      abel_nf
    calc
      ‖xₙ (n + m) - pn‖ ^ 2 = ‖(xₙ (n + m) - pm) + (pm - pn)‖ ^ 2 := by rw [hdecomp]
      _ = ‖xₙ (n + m) - pm‖ ^ 2 +
            2 * ⟪xₙ (n + m) - pm, pm - pn⟫_ℝ + ‖pm - pn‖ ^ 2 :=
        norm_add_sq_real (xₙ (n + m) - pm) (pm - pn)
  have hlower :
      ‖xₙ (n + m) - pm‖ ^ 2 + ‖pm - pn‖ ^ 2 ≤ ‖xₙ (n + m) - pn‖ ^ 2 := by
    nlinarith [hsq_expand, hcross_nonneg]
  have hfejer_sq :
      ‖xₙ (n + m) - pn‖ ^ 2 ≤ ‖xₙ n - pn‖ ^ 2 := by
    nlinarith [hfejer, norm_nonneg (xₙ (n + m) - pn), norm_nonneg (xₙ n - pn)]
  have hdist_n :
      ‖xₙ n - pn‖ = Metric.infDist (xₙ n) C := by
    simpa [pn, dist_eq_norm] using
      (projectionPoint_isBestApproximation C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) (xₙ n)).2
  have hdist_m :
      ‖xₙ (n + m) - pm‖ = Metric.infDist (xₙ (n + m)) C := by
    simpa [pm, dist_eq_norm] using
      (projectionPoint_isBestApproximation C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
        (xₙ (n + m))).2
  have hmain :
      ‖pm - pn‖ ^ 2 ≤ Metric.infDist (xₙ n) C ^ 2 - Metric.infDist (xₙ (n + m)) C ^ 2 := by
    rw [← hdist_n, ← hdist_m]
    nlinarith
  simpa [pn, pm, norm_sub_rev] using hmain

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 5.7: squaring preserves the distance-to-`C` convergence supplied by
Fejér monotonicity. -/
private theorem sq_infDist_tendsto_of_fejerMonotone
    (hC_nonempty : C.Nonempty) (xₙ : ℕ → H) (hxₙ : FejerMonotone C xₙ) :
    ∃ L : ℝ, Tendsto (fun n ↦ Metric.infDist (xₙ n) C ^ 2) atTop (𝓝 L) := by
  -- Move the convergent distance-to-set energy onto the squared scale used in the textbook proof.
  rcases infDist_tendsto_of_fejerMonotone hC_nonempty xₙ hxₙ with ⟨l, hl⟩
  refine ⟨l ^ 2, ?_⟩
  simpa using hl.pow 2

-- Proof sketch: use the Fejer monotonicity inequalities and the firm nonexpansiveness estimate for
-- metric projections onto nonempty closed convex sets to prove that the shadow sequence is Cauchy
-- in `C`; completeness then yields a limit point `z ∈ C`.
/-- Proposition 5.7 (1): if `C` is a nonempty closed convex subset of a real Hilbert space and
`xₙ` is Fejer monotone with respect to `C`, then the projection shadow `n ↦ P (xₙ n)` converges
strongly to some `z ∈ C`, where
`P := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)`.
-/
theorem exists_shadowLimit_of_fejerMonotone
    (xₙ : ℕ → H) (hxₙ : FejerMonotone C xₙ) :
    ∃ z ∈ C,
      Tendsto (fun n ↦ P (xₙ n)) atTop (𝓝 z) := by
  rcases sq_infDist_tendsto_of_fejerMonotone hC_nonempty xₙ hxₙ with ⟨L, hL⟩
  let s : ℕ → ℝ := fun n ↦ Metric.infDist (xₙ n) C ^ 2
  have hs_antitone : Antitone s := by
    have hinf_antitone := infDist_antitone_of_fejerMonotone hC_nonempty xₙ hxₙ
    intro n m hnm
    dsimp [s]
    have hn_nonneg : 0 ≤ Metric.infDist (xₙ n) C := Metric.infDist_nonneg
    have hm_nonneg : 0 ≤ Metric.infDist (xₙ m) C := Metric.infDist_nonneg
    nlinarith [hinf_antitone hnm, hn_nonneg, hm_nonneg]
  have hs_lim : Tendsto s atTop (𝓝 L) := by
    simpa [s] using hL
  have hL_le_s : ∀ N : ℕ, L ≤ s N := by
    intro N
    exact le_of_tendsto_of_tendsto hs_lim tendsto_const_nhds <|
      Filter.eventually_atTop.2 ⟨N, fun m hm ↦ hs_antitone hm⟩
  have hsqrt_lim : Tendsto (fun N ↦ Real.sqrt (s N - L)) atTop (𝓝 0) := by
    have hsub_lim : Tendsto (fun N ↦ s N - L) atTop (𝓝 0) := by
      simpa using hs_lim.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ L) atTop (𝓝 L))
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hsub_lim
  have hcauchy : CauchySeq (fun n ↦ P (xₙ n)) := by
    refine cauchySeq_of_le_tendsto_0 (fun N ↦ Real.sqrt (s N - L)) ?_ hsqrt_lim
    intro n m N hNn hNm
    by_cases hnm : n ≤ m
    · rcases Nat.exists_eq_add_of_le hnm with ⟨k, rfl⟩
      have hgap :
          ‖P (xₙ n) - P (xₙ (n + k))‖ ^ 2 ≤ s n - s (n + k) := by
        simpa [s] using
          shadow_gap_sq_le_infDist_sq_sub hC_nonempty hC_closed hC_convex xₙ hxₙ n k
      have htail_nonneg : 0 ≤ s N - L := sub_nonneg.mpr (hL_le_s N)
      have htail_sq :
          ‖P (xₙ n) - P (xₙ (n + k))‖ ^ 2 ≤ s N - L := by
        have hsNn : s n ≤ s N := hs_antitone hNn
        have hLsm : L ≤ s (n + k) := hL_le_s (n + k)
        nlinarith
      -- Compare the shadow distance with the square root of the tail energy.
      rw [dist_eq_norm]
      nlinarith [htail_sq, Real.sq_sqrt htail_nonneg,
        norm_nonneg (P (xₙ n) - P (xₙ (n + k))), Real.sqrt_nonneg (s N - L)]
    · have hmn : m ≤ n := le_of_not_ge hnm
      rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
      have hgap :
          ‖P (xₙ m) - P (xₙ (m + k))‖ ^ 2 ≤ s m - s (m + k) := by
        simpa [s] using
          shadow_gap_sq_le_infDist_sq_sub hC_nonempty hC_closed hC_convex xₙ hxₙ m k
      have htail_nonneg : 0 ≤ s N - L := sub_nonneg.mpr (hL_le_s N)
      have htail_sq :
          ‖P (xₙ m) - P (xₙ (m + k))‖ ^ 2 ≤ s N - L := by
        have hsNm : s m ≤ s N := hs_antitone hNm
        have hLsn : L ≤ s (m + k) := hL_le_s (m + k)
        nlinarith
      -- The symmetric tail estimate yields the same Cauchy bound.
      rw [dist_eq_norm, norm_sub_rev]
      nlinarith [htail_sq, Real.sq_sqrt htail_nonneg,
        norm_nonneg (P (xₙ m) - P (xₙ (m + k))), Real.sqrt_nonneg (s N - L)]
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨z, hz⟩
  have hzC : z ∈ C := by
    exact hC_closed.mem_of_tendsto hz <|
      Filter.Eventually.of_forall fun n ↦
        projectionPoint_mem C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) (xₙ n)
  exact ⟨z, hzC, hz⟩

end

section

variable {H : Type u} [NormedAddCommGroup H]
variable {C : Set H}

/-- Helper for Proposition 5.7: for every fixed point of `C`, the distance sequence of a
Fejér-monotone orbit converges. -/
private theorem dist_tendsto_of_fejerMonotone
    (xₙ : ℕ → H) (hxₙ : FejerMonotone C xₙ) {x : H} (hx : x ∈ C) :
    ∃ l : ℝ, Tendsto (fun n ↦ dist (xₙ n) x) atTop (𝓝 l) := by
  refine ⟨sInf ((fun n ↦ dist (xₙ n) x) '' Set.Ici 0), ?_⟩
  -- The distance sequence is antitone and bounded below by `0`.
  refine Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici (k := 0) ?_ ?_
  · intro m hm n hn hmn
    have hanti : Antitone fun n ↦ dist (xₙ n) x := by
      exact antitone_nat_of_succ_le (fun k ↦ hxₙ.step x hx k)
    exact hanti hmn
  · refine ⟨0, ?_⟩
    rintro _ ⟨n, hn, rfl⟩
    exact dist_nonneg

-- Proof sketch: apply `FejerMonotone.dist_tendsto` at the two points `z, x ∈ C`, then compose the
-- resulting distance limits with squaring.
/-- Proposition 5.7 (2): for a Fejér-monotone sequence and any two points `z, x ∈ C`, the
squared-distance sequences from `xₙ` to `z` and to `x` admit real limits. This is the source-facing
two-point packaging of the canonical one-point owner theorem `FejerMonotone.dist_tendsto`. -/
theorem exists_sqNorm_limits_of_fejerMonotone
    (xₙ : ℕ → H) (hxₙ : FejerMonotone C xₙ) {z x : H} (hz : z ∈ C) (hx : x ∈ C) :
    ∃ a b : ℝ,
      Tendsto (fun n ↦ ‖xₙ n - z‖ ^ 2) atTop (𝓝 a) ∧
        Tendsto (fun n ↦ ‖xₙ n - x‖ ^ 2) atTop (𝓝 b) := by
  -- Package the one-point distance convergence theorem at the two comparison points.
  rcases dist_tendsto_of_fejerMonotone xₙ hxₙ hz with ⟨az, haz⟩
  rcases dist_tendsto_of_fejerMonotone xₙ hxₙ hx with ⟨ax, hax⟩
  refine ⟨az ^ 2, ax ^ 2, ?_, ?_⟩
  · simpa [dist_eq_norm] using haz.pow 2
  · simpa [dist_eq_norm] using hax.pow 2

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

/-- Helper for Proposition 5.7: metric projection yields the Pythagorean lower bound against any
comparison point in `C`. -/
private theorem projection_pythagorean_lower_bound
    (y x : H) (hx : x ∈ C) :
    ‖y - x‖ ^ 2 ≥ ‖y - P y‖ ^ 2 + ‖P y - x‖ ^ 2 := by
  -- The projection variational inequality controls the cross term in the norm expansion.
  have hcross_nonneg : 0 ≤ ⟪y - P y, P y - x⟫_ℝ := by
    have hinner :
        ⟪x - P y, y - P y⟫_ℝ ≤ 0 := by
      exact
        ((eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
            hC_nonempty hC_closed hC_convex).mp rfl).2 x hx
    have hinner' :
        ⟪y - P y, x - P y⟫_ℝ ≤ 0 := by
      simpa [real_inner_comm] using hinner
    have hrewrite :
        ⟪y - P y, P y - x⟫_ℝ = -⟪y - P y, x - P y⟫_ℝ := by
      rw [show P y - x = -(x - P y) by abel_nf, inner_neg_right]
    rw [hrewrite]
    exact neg_nonneg.mpr hinner'
  -- Expand `‖y - x‖²` through the projection point `P y`.
  have hsq_expand :
      ‖y - x‖ ^ 2 =
        ‖y - P y‖ ^ 2 + 2 * ⟪y - P y, P y - x⟫_ℝ + ‖P y - x‖ ^ 2 := by
    have hdecomp : y - x = (y - P y) + (P y - x) := by
      abel_nf
    calc
      ‖y - x‖ ^ 2 = ‖(y - P y) + (P y - x)‖ ^ 2 := by rw [hdecomp]
      _ = ‖y - P y‖ ^ 2 + 2 * ⟪y - P y, P y - x⟫_ℝ + ‖P y - x‖ ^ 2 :=
        norm_add_sq_real (y - P y) (P y - x)
  nlinarith [hsq_expand, hcross_nonneg]

/-- Helper for Proposition 5.7: once the shadow `P (xₙ n)` converges to `z`, the residual squared
norms `‖xₙ n - P (xₙ n)‖²` converge to the same limit as `‖xₙ n - z‖²`. -/
private theorem shadow_residual_sq_tendsto_of_shadowLimit
    (xₙ : ℕ → H) {z : H} (hz : Tendsto (fun n ↦ P (xₙ n)) atTop (𝓝 z))
    {a : ℝ} (ha : Tendsto (fun n ↦ ‖xₙ n - z‖ ^ 2) atTop (𝓝 a)) :
    Tendsto (fun n ↦ ‖xₙ n - P (xₙ n)‖ ^ 2) atTop (𝓝 a) := by
  have ha_nonneg : 0 ≤ a := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ha <|
      Filter.Eventually.of_forall fun n ↦ sq_nonneg ‖xₙ n - z‖
  -- The shadow convergence forces the shadow defect `‖P (xₙ n) - z‖` to vanish.
  have hshadow_norm :
      Tendsto (fun n ↦ ‖P (xₙ n) - z‖) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg] using
      ((hz.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ z) atTop (𝓝 z))).norm)
  have hsqrt_tendsto :
      Tendsto (fun n ↦ Real.sqrt (‖xₙ n - z‖ ^ 2)) atTop (𝓝 (Real.sqrt a)) := by
    exact Real.continuous_sqrt.continuousAt.tendsto.comp ha
  have hxz_norm :
      Tendsto (fun n ↦ ‖xₙ n - z‖) atTop (𝓝 (Real.sqrt a)) := by
    simpa [Real.sqrt_sq_eq_abs, ha_nonneg] using hsqrt_tendsto
  have hshadow_sq :
      Tendsto (fun n ↦ ‖z - P (xₙ n)‖ ^ 2) atTop (𝓝 0) := by
    simpa [norm_sub_rev] using hshadow_norm.pow 2
  have hcross_bound :
      Tendsto (fun n ↦ 2 * ‖xₙ n - z‖ * ‖P (xₙ n) - z‖) atTop (𝓝 0) := by
    simpa [mul_assoc] using (hxz_norm.mul hshadow_norm).const_mul 2
  have hcross_abs_le :
      ∀ n, |2 * ⟪xₙ n - z, z - P (xₙ n)⟫_ℝ| ≤ 2 * ‖xₙ n - z‖ * ‖P (xₙ n) - z‖ := by
    intro n
    have hinner : |⟪xₙ n - z, z - P (xₙ n)⟫_ℝ| ≤ ‖xₙ n - z‖ * ‖P (xₙ n) - z‖ := by
      simpa [norm_sub_rev] using abs_real_inner_le_norm (xₙ n - z) (z - P (xₙ n))
    calc
      |2 * ⟪xₙ n - z, z - P (xₙ n)⟫_ℝ|
          = 2 * |⟪xₙ n - z, z - P (xₙ n)⟫_ℝ| := by
              rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      _ ≤ 2 * (‖xₙ n - z‖ * ‖P (xₙ n) - z‖) := by
        gcongr
      _ = 2 * ‖xₙ n - z‖ * ‖P (xₙ n) - z‖ := by ring
  have hcross_tendsto :
      Tendsto (fun n ↦ 2 * ⟪xₙ n - z, z - P (xₙ n)⟫_ℝ) atTop (𝓝 0) := by
    have habs_tendsto :
        Tendsto (fun n ↦ |2 * ⟪xₙ n - z, z - P (xₙ n)⟫_ℝ|) atTop (𝓝 0) := by
      exact squeeze_zero (fun n ↦ abs_nonneg _) hcross_abs_le hcross_bound
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs_tendsto
  -- Expand the residual through the limit point `z` and send the vanishing error terms to `0`.
  have hsq_rewrite :
      (fun n ↦ ‖xₙ n - P (xₙ n)‖ ^ 2) =
        (fun n ↦ ‖xₙ n - z‖ ^ 2 + 2 * ⟪xₙ n - z, z - P (xₙ n)⟫_ℝ + ‖z - P (xₙ n)‖ ^ 2) := by
    funext n
    have hdecomp : xₙ n - P (xₙ n) = (xₙ n - z) + (z - P (xₙ n)) := by
      abel_nf
    calc
      ‖xₙ n - P (xₙ n)‖ ^ 2 = ‖(xₙ n - z) + (z - P (xₙ n))‖ ^ 2 := by rw [hdecomp]
      _ = ‖xₙ n - z‖ ^ 2 + 2 * ⟪xₙ n - z, z - P (xₙ n)⟫_ℝ + ‖z - P (xₙ n)‖ ^ 2 :=
        norm_add_sq_real (xₙ n - z) (z - P (xₙ n))
  rw [hsq_rewrite]
  simpa using (ha.add hcross_tendsto).add hshadow_sq

-- Proof sketch: combine the textbook projection inequality with the convergence of the shadow
-- sequence to identify the limit of the residual squared norms with `a`, then use the
-- Pythagorean inequality for metric projections against `x ∈ C` and pass to the limit.
/-- Proposition 5.7 (3): if the shadow sequence converges strongly to `z` and `a`, `b` are the
limits of the squared-distance sequences from `xₙ` to `z` and to `x ∈ C`, then
`a + ‖x - z‖ ^ 2 ≤ b`. -/
theorem sqNorm_limit_add_sqNorm_le_limit_of_shadowLimit
    (xₙ : ℕ → H) {z : H} (hz : Tendsto (fun n ↦ P (xₙ n)) atTop (𝓝 z)) {x : H} (hx : x ∈ C)
    {a b : ℝ}
    (ha : Tendsto (fun n ↦ ‖xₙ n - z‖ ^ 2) atTop (𝓝 a))
    (hb : Tendsto (fun n ↦ ‖xₙ n - x‖ ^ 2) atTop (𝓝 b)) :
    a + ‖x - z‖ ^ 2 ≤ b := by
  have hresidual :
      Tendsto (fun n ↦ ‖xₙ n - P (xₙ n)‖ ^ 2) atTop (𝓝 a) :=
    shadow_residual_sq_tendsto_of_shadowLimit hC_nonempty hC_closed hC_convex xₙ hz ha
  have hshadow_to_x :
      Tendsto (fun n ↦ ‖P (xₙ n) - x‖ ^ 2) atTop (𝓝 (‖z - x‖ ^ 2)) := by
    simpa [sub_eq_add_neg] using
      ((hz.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x))).norm.pow 2)
  have hsum_tendsto :
      Tendsto
        (fun n ↦ ‖xₙ n - P (xₙ n)‖ ^ 2 + ‖P (xₙ n) - x‖ ^ 2)
        atTop (𝓝 (a + ‖z - x‖ ^ 2)) := by
    simpa using hresidual.add hshadow_to_x
  have hineq :
      ∀ n, ‖xₙ n - P (xₙ n)‖ ^ 2 + ‖P (xₙ n) - x‖ ^ 2 ≤ ‖xₙ n - x‖ ^ 2 := by
    intro n
    have hpyth :=
      projection_pythagorean_lower_bound hC_nonempty hC_closed hC_convex (y := xₙ n) (x := x) hx
    nlinarith
  have hlimit_le : a + ‖z - x‖ ^ 2 ≤ b := by
    exact le_of_tendsto_of_tendsto hsum_tendsto hb <|
      Filter.Eventually.of_forall hineq
  simpa [norm_sub_rev] using hlimit_le

end
