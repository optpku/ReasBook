/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15.Banach
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15.TV

public section

namespace VariationalRegularization

variable {d : ℕ}
variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}

/-!
Theorem 8.15.

This source-facing bridge file re-exports the canonical Chapter 8 declarations
for the normed-space, Banach-space, and total-variation-seminorm structures on
`BV(Ω)`.
-/

/- Theorem 8.15 (1). The Chapter 8 bounded-variation space `BV(Ω)` carries its canonical normed
real vector-space structure. -/
#check instNormedAddCommGroupBV
#check instNormedSpaceBV

/-- Theorem 8.15 (2). The Chapter 8 bounded-variation space `BV(Ω)` is complete for its
canonical BV norm. -/
theorem completeSpaceBV :
    CompleteSpace (BV(Ω)) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  -- First pass to the `L¹(Ω)` limit through the continuous projection.
  have hCauchyL1 : CauchySeq (fun n ↦ (u n).toL1) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    rcases hu ε hε with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hdist : dist (u m) (u n) < ε := hN m hm n hn
    have hnorm : ‖u m - u n‖ < ε := by simpa [dist_eq_norm] using hdist
    have hL1 : ‖(u m - u n).toL1‖ ≤ ‖u m - u n‖ := BV.normToL1_le (u m - u n)
    have : ‖(u m).toL1 - (u n).toL1‖ < ε := by
      simpa [BV.toL1_sub] using lt_of_le_of_lt hL1 hnorm
    simpa [dist_eq_norm] using this
  obtain ⟨g, hg⟩ :
      ∃ g : MeasureTheory.Lp ℝ 1 (domainMeasure Ω),
        Filter.Tendsto (fun n ↦ (u n).toL1) Filter.atTop (nhds g) :=
    cauchySeq_tendsto_of_complete hCauchyL1
  -- A Cauchy BV sequence has an eventually bounded BV norm, hence an eventually bounded raw TV.
  rcases Metric.cauchySeq_iff'.1 hu 1 zero_lt_one with ⟨N, hN⟩
  let B : ℝ := ‖u N‖ + 1
  have hnorm_tail : ∀ᶠ n in Filter.atTop, ‖u n‖ ≤ B := by
    refine Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    have hdist : dist (u n) (u N) < 1 := hN n hn
    have hnorm : ‖u n - u N‖ < 1 := by simpa [dist_eq_norm] using hdist
    exact le_of_lt <| calc
      ‖u n‖ ≤ ‖u n - u N‖ + ‖u N‖ := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (_root_.norm_add_le (u n - u N) (u N))
      _ < 1 + ‖u N‖ := by linarith
      _ = B := by simp [B, add_comm]
  have htv_tail :
      ∀ᶠ n in Filter.atTop, totalVariation ((u n).toL1) ≤ (B : EReal) := by
    filter_upwards [hnorm_tail] with n hn
    exact (BV.lpTotalVariation_le_coe_norm (u n)).trans (by exact_mod_cast hn)
  have hliminf_bound :
      Filter.liminf (fun n ↦ totalVariation ((u n).toL1)) Filter.atTop ≤ (B : EReal) := by
    refine Filter.liminf_le_of_le
      (u := fun n ↦ totalVariation ((u n).toL1)) (by isBoundedDefault) ?_
    intro b hb
    rcases (hb.and htv_tail).exists with ⟨n, hbn, hntv⟩
    exact hbn.trans hntv
  -- Lower semicontinuity keeps the `L¹(Ω)` limit inside `BV(Ω)`.
  have htv_g :
      totalVariation g ≤ Filter.liminf (fun n ↦ totalVariation ((u n).toL1)) Filter.atTop :=
    lpTotalVariation_le_liminf_of_tendstoL1 (Ω := Ω) (u := fun n ↦ (u n).toL1) (g := g) hg
  have htv_g_top : totalVariation g < ⊤ := by
    have hB_top : ((B : ℝ) : EReal) < ⊤ := by
      unfold B
      exact EReal.add_lt_top (EReal.coe_ne_top ‖u N‖) (EReal.coe_ne_top 1)
    exact lt_of_le_of_lt htv_g <| lt_of_le_of_lt hliminf_bound hB_top
  have hgBV : IsBV g := by
    -- The `L¹` norm is finite by construction, so the finiteness of `TV(g)` closes the BV test.
    rw [IsBV]
    exact EReal.add_lt_top (EReal.coe_ne_top ‖g‖) htv_g_top.ne
  let v : BV(Ω) := ⟨g, hgBV⟩
  refine ⟨v, ?_⟩
  -- Prove convergence in the BV norm directly from the Cauchy tail estimate and the liminf
  -- bound applied to the fixed-`n` difference sequence.
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases Metric.cauchySeq_iff.1 hu (ε / 4) (by linarith) with ⟨Nε, hNε⟩
  refine ⟨Nε, fun n hn ↦ ?_⟩
  have hdiffL1 :
      Filter.Tendsto (fun m ↦ (u n - u m).toL1) Filter.atTop (nhds ((u n).toL1 - g)) := by
    simpa [BV.toL1_sub, v] using (tendsto_const_nhds.sub hg)
  have htv_diff :
      totalVariation ((u n).toL1 - g) ≤
        Filter.liminf (fun m ↦ totalVariation ((u n - u m).toL1)) Filter.atTop :=
    lpTotalVariation_le_liminf_of_tendstoL1 (Ω := Ω)
      (u := fun m ↦ (u n - u m).toL1) (g := (u n).toL1 - g) hdiffL1
  have htv_tail_diff :
      ∀ᶠ m in Filter.atTop, totalVariation ((u n - u m).toL1) ≤ (((ε / 4) : ℝ) : EReal) := by
    refine Filter.eventually_atTop.2 ⟨max Nε n, fun m hm ↦ ?_⟩
    have hNm : Nε ≤ m := le_trans (le_max_left _ _) hm
    have hdist : dist (u n) (u m) < ε / 4 := hNε n hn m hNm
    have hnorm : ‖u n - u m‖ < ε / 4 := by simpa [dist_eq_norm] using hdist
    exact (BV.lpTotalVariation_le_coe_norm (u n - u m)).trans (by exact_mod_cast hnorm.le)
  have hliminf_diff :
      Filter.liminf (fun m ↦ totalVariation ((u n - u m).toL1)) Filter.atTop ≤
        (((ε / 4) : ℝ) : EReal) := by
    refine Filter.liminf_le_of_le
      (u := fun m ↦ totalVariation ((u n - u m).toL1)) (by isBoundedDefault) ?_
    intro b hb
    rcases (hb.and htv_tail_diff).exists with ⟨m, hbm, hmtv⟩
    exact hbm.trans hmtv
  have htv_limit :
      totalVariation ((u n).toL1 - g) ≤ (((ε / 4) : ℝ) : EReal) :=
    htv_diff.trans hliminf_diff
  have htv_limit_real :
      (totalVariation ((u n).toL1 - g)).toReal ≤ ε / 4 := by
    have hbot :
        totalVariation ((u n).toL1 - g) ≠ ⊥ := by
      exact ne_of_gt <| lt_of_lt_of_le (by simp) (lpTotalVariationNonneg ((u n).toL1 - g))
    exact EReal.toReal_le_toReal htv_limit hbot (EReal.coe_ne_top (ε / 4))
  have hnorm_tail_diff :
      ∀ᶠ m in Filter.atTop, ‖(u n - u m).toL1‖ ≤ ε / 4 := by
    refine Filter.eventually_atTop.2 ⟨max Nε n, fun m hm ↦ ?_⟩
    have hNm : Nε ≤ m := le_trans (le_max_left _ _) hm
    have hdist : dist (u n) (u m) < ε / 4 := hNε n hn m hNm
    have hnorm : ‖u n - u m‖ < ε / 4 := by simpa [dist_eq_norm] using hdist
    exact (BV.normToL1_le (u n - u m)).trans hnorm.le
  have hnorm_limit :
      ‖(u n).toL1 - g‖ ≤ ε / 4 := by
    have hnorm_tendsto :
        Filter.Tendsto (fun m ↦ ‖(u n - u m).toL1‖) Filter.atTop
          (nhds ‖(u n).toL1 - g‖) :=
      (continuous_norm.tendsto _).comp hdiffL1
    exact isClosed_Iic.mem_of_tendsto hnorm_tendsto hnorm_tail_diff
  have hv_toL1 : v.toL1 = g := by rfl
  have hnorm_v :
      ‖u n - v‖ =
        ‖(u n).toL1 - v.toL1‖ + (totalVariation ((u n).toL1 - v.toL1)).toReal := by
    simpa [BV.toL1_sub] using BV.norm_eq_normToL1_add_lpTotalVariation (u n - v)
  have hsum_lt : ε / 4 + ε / 4 < ε := by
    linarith
  calc
    dist (u n) v = ‖u n - v‖ := dist_eq_norm _ _
    _ = ‖(u n).toL1 - v.toL1‖ + (totalVariation ((u n).toL1 - v.toL1)).toReal := hnorm_v
    _ = ‖(u n).toL1 - g‖ + (totalVariation ((u n).toL1 - g)).toReal := by rw [hv_toL1]
    _ ≤ ε / 4 + ε / 4 := add_le_add hnorm_limit htv_limit_real
    _ < ε := hsum_lt

/-- The canonical `CompleteSpace` instance for the Chapter 8 bounded-variation space `BV(Ω)`. -/
instance instCompleteSpaceBV :
    CompleteSpace (BV(Ω)) :=
  completeSpaceBV

/- Theorem 8.15 (3). The restricted Chapter 8 total variation on `BV(Ω)` is packaged as a real
seminorm, with the source-facing subadditivity and homogeneity companions exposed directly. -/
#check BV.totalVariation
#check BV.totalVariation_def
#check BV.totalVariation_add_le
#check BV.totalVariation_smul
#check BV.tvSeminorm
#check BV.tvSeminorm_apply

end VariationalRegularization
