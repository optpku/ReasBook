/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.TangentCone.Seq

section Chapter08Definition823

open Filter
open scoped Pointwise

-- Domain sampling:
-- * primary domain: one-sided tangent directions in real normed spaces
-- * inspected mathlib owners:
--   `posTangentConeAt`
--   `tangentConeAt NNReal`
--   `mem_tangentConeAt_iff_exists_seq`
-- * source/core/bridge triage:
--   `source-facing`: the textbook set `SFD(xStar, X)`, represented here only through the
--     sequence-membership bridge below
--   `core/canonical`: `posTangentConeAt X xStar`
--   `bridge/view`: `mem_posTangentConeAt_iff_exists_seq_pos`

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Chapter08 Definition 8.2.3: the source set `SFD(xStar, X)` is realized by the canonical
positive tangent cone `posTangentConeAt X xStar`. -/
#check (posTangentConeAt : Set E → E → Set E)

/-- Helper for Chapter08 Definition 8.2.3: from positive tangent-cone membership, every small
radius and every positive lower bound admit a feasible increment whose positive rescaling lands
within the prescribed radius around a nonzero target direction. -/
lemma exists_scaled_feasible_step_near
    {X : Set E} {xStar d : E} (hd : d ∈ posTangentConeAt X xStar) (hd0 : d ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (R : NNReal) :
    ∃ c : NNReal, ∃ e : E,
      R < c ∧ xStar + e ∈ X ∧ ‖e‖ < ε ∧ ‖(c : ℝ) • e - d‖ < ε := by
  let η : ℝ := min ε (‖d‖ / (2 * ((R : ℝ) + 1)))
  have hη_pos : 0 < η := by
    refine lt_min hε ?_
    have hd_norm : 0 < ‖d‖ := norm_pos_iff.mpr hd0
    positivity
  rw [posTangentConeAt, tangentConeAt_def, Set.mem_setOf, clusterPt_iff_nonempty] at hd
  let feasibleSteps : Set E := (xStar + ·) ⁻¹' X ∩ Metric.ball (0 : E) η
  let scaledSteps : Set E := (Set.univ : Set NNReal) • feasibleSteps
  have hscaled :
      scaledSteps ∈ ((⊤ : Filter NNReal) • nhdsWithin (0 : E) ((xStar + ·) ⁻¹' X)) := by
    refine Filter.mem_smul.2 ?_
    refine ⟨Set.univ, by simp, feasibleSteps, ?_, ?_⟩
    · dsimp [feasibleSteps]
      exact inter_mem_nhdsWithin ((xStar + ·) ⁻¹' X) (Metric.ball_mem_nhds (0 : E) hη_pos)
    · intro y hy
      simpa [scaledSteps] using hy
  have hnonempty : (Metric.ball d η ∩ scaledSteps).Nonempty := by
    exact hd (U := Metric.ball d η) (Metric.ball_mem_nhds d hη_pos) (V := scaledSteps) hscaled
  rcases hnonempty with ⟨y, hy, hscaledY⟩
  rcases hscaledY with ⟨c, -, e, he, rfl⟩
  rcases he with ⟨hfeasible, heBall⟩
  have he_small_η : ‖e‖ < η := by
    simpa [Metric.mem_ball, dist_eq_norm] using heBall
  have hclose_η : ‖(c : ℝ) • e - d‖ < η := by
    simpa [Metric.mem_ball, dist_eq_norm, NNReal.smul_def] using hy
  have hc_gt : R < c := by
    by_contra hCR
    have hc_le : c ≤ R := le_of_not_gt hCR
    have htriangle : ‖d‖ ≤ ‖(c : ℝ) • e - d‖ + ‖(c : ℝ) • e‖ := by
      calc
        ‖d‖ = ‖(d - (c : ℝ) • e) + (c : ℝ) • e‖ := by
          simp [sub_eq_add_neg, add_assoc]
        _ ≤ ‖d - (c : ℝ) • e‖ + ‖(c : ℝ) • e‖ := norm_add_le _ _
        _ = ‖(c : ℝ) • e - d‖ + ‖(c : ℝ) • e‖ := by rw [norm_sub_rev]
    have hscale_le : ‖(c : ℝ) • e‖ ≤ (R : ℝ) * η := by
      rw [norm_smul]
      have hc_le' : ‖(c : ℝ)‖ ≤ (R : ℝ) := by
        simpa [Real.norm_of_nonneg c.2] using (show (c : ℝ) ≤ R by exact_mod_cast hc_le)
      exact le_trans
        (mul_le_mul_of_nonneg_right hc_le' (norm_nonneg _))
        (mul_le_mul_of_nonneg_left he_small_η.le (by positivity))
    have hsum_lt : ‖(c : ℝ) • e - d‖ + ‖(c : ℝ) • e‖ < η + (R : ℝ) * η :=
      add_lt_add_of_lt_of_le hclose_η hscale_le
    have hη_bound : η ≤ ‖d‖ / (2 * ((R : ℝ) + 1)) := min_le_right _ _
    have hbound' : ((R : ℝ) + 1) * η ≤ ‖d‖ / 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_left hη_bound (show 0 ≤ (R : ℝ) + 1 by positivity)
      have hR1 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
      calc
        ((R : ℝ) + 1) * η
            ≤ ((R : ℝ) + 1) * (‖d‖ / (2 * ((R : ℝ) + 1))) := hmul
        _ = ‖d‖ / 2 := by
            field_simp [hR1.ne']
    have hbound : η + (R : ℝ) * η ≤ ‖d‖ / 2 := by
      simpa [add_mul, one_mul, add_comm, add_left_comm, add_assoc] using hbound'
    have hd_norm : 0 < ‖d‖ := norm_pos_iff.mpr hd0
    have hhalf_lt : ‖d‖ / 2 < ‖d‖ := by nlinarith
    have hsum_lt_d : ‖(c : ℝ) • e - d‖ + ‖(c : ℝ) • e‖ < ‖d‖ := by
      exact lt_of_lt_of_le hsum_lt (le_of_lt (lt_of_le_of_lt hbound hhalf_lt))
    exact (lt_irrefl ‖d‖) (lt_of_le_of_lt htriangle hsum_lt_d)
  refine ⟨c, e, hc_gt, hfeasible, ?_, ?_⟩
  · exact lt_of_lt_of_le he_small_η (min_le_left _ _)
  · exact lt_of_lt_of_le hclose_η (min_le_left _ _)

/-- Helper for Chapter08 Definition 8.2.3: reciprocals of positive scalars that dominate `k + 1`
tend to zero. -/
lemma tendsto_reciprocal_of_linear_lower_bound {c : ℕ → NNReal}
    (hc : ∀ k, (((k + 1 : ℕ) : NNReal)) < c k) :
    Tendsto (fun k ↦ ((c k : ℝ))⁻¹) atTop (nhds (0 : ℝ)) := by
  refine squeeze_zero (fun k ↦ by positivity) ?_ tendsto_one_div_add_atTop_nhds_zero_nat
  intro k
  have hk_pos : (0 : ℝ) < k + 1 := by positivity
  have hck : (k + 1 : ℝ) ≤ c k := by
    exact_mod_cast (hc k).le
  simpa [one_div] using one_div_le_one_div_of_le hk_pos hck

/-- Helper for Chapter08 Definition 8.2.3: the textbook sequential feasible-direction witnesses
immediately give positive tangent-cone membership. -/
lemma mem_posTangentConeAt_of_exists_seq_pos
    {X : Set E} {xStar d : E}
    (h :
      ∃ dSeq : ℕ → E, ∃ delta : ℕ → ℝ,
        (∀ k, 0 < delta k) ∧
        (∀ k, xStar + delta k • dSeq k ∈ X) ∧
        Tendsto dSeq atTop (nhds d) ∧
        Tendsto delta atTop (nhds (0 : ℝ))) :
    d ∈ posTangentConeAt X xStar := by
  rcases h with ⟨dSeq, delta, hdelta_pos, hmem, hdSeq, hdelta⟩
  let c : ℕ → NNReal := fun k ↦ ⟨(delta k)⁻¹, inv_nonneg.mpr (le_of_lt (hdelta_pos k))⟩
  have hstep_zero : Tendsto (fun k ↦ delta k • dSeq k) atTop (nhds (0 : E)) := by
    -- The feasible increments vanish because scalar multiplication is continuous at `(0, d)`.
    simpa using hdelta.smul hdSeq
  have hscaled :
      Tendsto (fun k ↦ c k • (delta k • dSeq k)) atTop (nhds d) := by
    -- Rescaling by the reciprocal positive scalar recovers the original sequence `dSeq`.
    have hEq : (fun k ↦ c k • (delta k • dSeq k)) = dSeq := by
      funext k
      have hk : delta k ≠ 0 := ne_of_gt (hdelta_pos k)
      rw [NNReal.smul_def, smul_smul]
      change ((((delta k)⁻¹ : ℝ) * delta k) • dSeq k) = dSeq k
      simp [hk]
    simpa [hEq] using hdSeq
  rw [posTangentConeAt]
  exact mem_tangentConeAt_of_seq atTop c (fun k ↦ delta k • dSeq k) hstep_zero
    (Filter.Eventually.of_forall hmem) hscaled

/-- Helper for Chapter08 Definition 8.2.3: when the target direction is zero, closure of the set
already provides textbook witnesses with positive step sizes. -/
lemma exists_seq_pos_of_mem_posTangentConeAt_zero
    {X : Set E} {xStar : E} (hd : (0 : E) ∈ posTangentConeAt X xStar) :
    ∃ dSeq : ℕ → E, ∃ delta : ℕ → ℝ,
      (∀ k, 0 < delta k) ∧
      (∀ k, xStar + delta k • dSeq k ∈ X) ∧
      Tendsto dSeq atTop (nhds (0 : E)) ∧
      Tendsto delta atTop (nhds (0 : ℝ)) := by
  have hx_closure : xStar ∈ closure X := by
    rw [posTangentConeAt] at hd
    exact mem_closure_of_nonempty_tangentConeAt ⟨0, hd⟩
  rw [Metric.mem_closure_iff] at hx_closure
  have hchoose :
      ∀ k : ℕ,
        ∃ e : E, xStar + e ∈ X ∧ ‖e‖ < (((k + 1 : ℝ))⁻¹)^2 := by
    intro k
    rcases hx_closure ((((k + 1 : ℝ))⁻¹)^2) (by positivity) with ⟨y, hyX, hyBall⟩
    refine ⟨y - xStar, ?_, ?_⟩
    · simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hyX
    · simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hyBall
  choose e hmem he_small using hchoose
  refine ⟨fun k ↦ (k + 1 : ℝ) • e k, fun k ↦ ((k + 1 : ℝ))⁻¹, ?_, ?_, ?_, ?_⟩
  · intro k
    positivity
  · intro k
    have hk : (k + 1 : ℝ) ≠ 0 := by positivity
    simpa [smul_smul, hk] using hmem k
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun k ↦ norm_nonneg _) ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    intro k
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hmul :
        (k + 1 : ℝ) * ‖e k‖ ≤ (k + 1 : ℝ) * (((k + 1 : ℝ))⁻¹)^2 := by
      exact mul_le_mul_of_nonneg_left (he_small k).le (by positivity)
    have hk : (0 : ℝ) < k + 1 := by positivity
    calc
      (k + 1 : ℝ) * ‖e k‖ ≤ (k + 1 : ℝ) * (((k + 1 : ℝ))⁻¹)^2 := hmul
      _ = ((k + 1 : ℝ))⁻¹ := by
          field_simp [hk.ne']
      _ = 1 / ((k + 1 : ℝ)) := by rw [one_div]
  · simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)))

/-- Helper for Chapter08 Definition 8.2.3: a positive tangent-cone direction admits the textbook
sequences of positive step sizes and limiting feasible directions. -/
lemma exists_seq_pos_of_mem_posTangentConeAt
    {X : Set E} {xStar d : E} (hd : d ∈ posTangentConeAt X xStar) :
    ∃ dSeq : ℕ → E, ∃ delta : ℕ → ℝ,
      (∀ k, 0 < delta k) ∧
      (∀ k, xStar + delta k • dSeq k ∈ X) ∧
      Tendsto dSeq atTop (nhds d) ∧
      Tendsto delta atTop (nhds (0 : ℝ)) := by
  rcases eq_or_ne d 0 with rfl | hd0
  · exact exists_seq_pos_of_mem_posTangentConeAt_zero hd
  have hchoose :
      ∀ k : ℕ,
        ∃ c : NNReal, ∃ e : E,
          (((k + 1 : ℕ) : NNReal)) < c ∧
          xStar + e ∈ X ∧
          ‖e‖ < ((k + 1 : ℝ))⁻¹ ∧
          ‖(c : ℝ) • e - d‖ < ((k + 1 : ℝ))⁻¹ := by
    intro k
    exact exists_scaled_feasible_step_near
      (d := d) hd hd0 (ε := ((k + 1 : ℝ))⁻¹) (by positivity) (((k + 1 : ℕ) : NNReal))
  choose c e hc hmem he_small hclose using hchoose
  refine ⟨fun k ↦ (c k : ℝ) • e k, fun k ↦ ((c k : ℝ))⁻¹, ?_, ?_, ?_, ?_⟩
  · intro k
    have hc_pos : (0 : ℝ) < c k := by
      exact lt_trans (by positivity) (show (k + 1 : ℝ) < c k by exact_mod_cast hc k)
    positivity
  · intro k
    -- The reciprocal step size exactly cancels the positive rescaling `c k`.
    have hc_ne : (c k : ℝ) ≠ 0 := by
      have hc_pos : (0 : ℝ) < c k := by
        exact lt_trans (by positivity) (show (k + 1 : ℝ) < c k by exact_mod_cast hc k)
      exact ne_of_gt hc_pos
    simpa [smul_smul, hc_ne] using hmem k
  · -- The rescaled directions approach `d` with the prescribed `1 / (k + 1)` error.
    apply tendsto_iff_norm_sub_tendsto_zero.2
    refine squeeze_zero (fun k ↦ norm_nonneg _) ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    intro k
    simpa using (hclose k).le
  · -- The reciprocal positive step sizes go to zero because `c k ≥ k + 1`.
    exact tendsto_reciprocal_of_linear_lower_bound hc
/-- Chapter08 Definition 8.2.3 (source-language bridge): a vector `d` belongs to the canonical
positive tangent cone `posTangentConeAt X xStar` exactly when there exist sequences `dSeq` and
positive step sizes `delta` such that `xStar + delta k • dSeq k ∈ X` for all `k`, `dSeq ⟶ d`,
and `delta ⟶ 0`. -/
theorem mem_posTangentConeAt_iff_exists_seq_pos
    {X : Set E} {xStar d : E} :
    d ∈ posTangentConeAt X xStar ↔
      ∃ dSeq : ℕ → E, ∃ delta : ℕ → ℝ,
        (∀ k, 0 < delta k) ∧
        (∀ k, xStar + delta k • dSeq k ∈ X) ∧
        Tendsto dSeq atTop (nhds d) ∧
        Tendsto delta atTop (nhds (0 : ℝ)) := by
  constructor
  · -- Route correction: use the cluster-point tangent-cone definition to manufacture
    -- arbitrarily small feasible increments with arbitrarily large positive rescaling.
    exact exists_seq_pos_of_mem_posTangentConeAt
  · -- The converse is the canonical sequential criterion for tangent-cone membership.
    exact mem_posTangentConeAt_of_exists_seq_pos

end Chapter08Definition823
