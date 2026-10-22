/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_59Support

open Filter
open Set
open scoped BigOperators ENNReal Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

/-- Helper for Remark 21.59: the pointwise Chapter 21 `p`-variation owner on `[0,T]`, defined
from the dyadic `p`-variation sums by taking their `limsup`. -/
noncomputable def pVariationUpTo (p : ℝ) (G : PathSpace) (T : NNReal) : ℝ≥0∞ :=
  limsup (fun n ↦ ENNReal.ofReal (dyadic_p_variation_sum p G T n)) atTop

/-- Helper for Remark 21.59: every contributing dyadic partition point lies in `Icc 0 T`. -/
lemma dyadicPartitionPoint_mem_Icc_of_lt_partitionBoundIndex
    (n k : ℕ) (T : NNReal)
    (hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    Definition2158.dyadicPartitionSequence n k ∈ Icc 0 T := by
  -- Proof comment: the dyadic row starts at `0`, and every active point lies strictly before `T`.
  constructor
  · exact bot_le
  · exact le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex n hk)

/-- Helper for Remark 21.59: a clipped dyadic successor interval has size at most one dyadic mesh
width. -/
lemma edist_dyadicPartitionPoint_partitionNextPointUpTo_le_mesh
    (n k : ℕ) (T : NNReal)
    (hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    edist (Definition2158.dyadicPartitionSequence n k)
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ≤
      partitionMesh Definition2158.dyadicPartitionSequence n := by
  let P := Definition2158.dyadicPartitionSequence
  have hleft : P n k ≤ partitionNextPointUpTo P n k T := by
    rw [partitionNextPointUpTo]
    refine le_min ?_ ?_
    · exact le_of_lt ((instStrictMono_of_isAdmissiblePartitionSequence P n)
        (Nat.lt_succ_self k))
    · exact le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex n hk)
  have hright : partitionNextPointUpTo P n k T ≤ P n (k + 1) := by
    -- Proof comment: truncation by `min T` can only move the successor point to the left.
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hdist :
      edist (P n k) (partitionNextPointUpTo P n k T) ≤ edist (P n k) (P n (k + 1)) := by
    have hsucc : P n k < P n (k + 1) := by
      exact (instStrictMono_of_isAdmissiblePartitionSequence P n) (Nat.lt_succ_self k)
    rw [edist_nndist, edist_nndist, NNReal.nndist_eq, NNReal.nndist_eq,
      tsub_eq_zero_of_le hleft, tsub_eq_zero_of_le (le_of_lt hsucc), max_eq_right, max_eq_right]
    · exact_mod_cast tsub_le_tsub_right hright _
    · simp
    · simp
  calc
    edist (P n k) (partitionNextPointUpTo P n k T) ≤ edist (P n k) (P n (k + 1)) := hdist
    _ ≤ partitionMesh P n := by
      rw [partitionMesh]
      exact le_iSup (fun j ↦ edist (P n j) (P n (j + 1))) k

/-- Helper for Remark 21.59: finiteness of `pVariationUpTo p G T` eventually bounds the dyadic
`p`-variation rows by `pVariationUpTo p G T.toReal + 1`. -/
lemma eventually_dyadicPVariationSum_lt_toReal_pVariationUpTo_add_one
    {p : ℝ} {G : PathSpace} (T : NNReal) (hfinite : pVariationUpTo p G T ≠ ∞) :
    ∀ᶠ n in atTop, dyadic_p_variation_sum p G T n < (pVariationUpTo p G T).toReal + 1 := by
  have hbound :
      ∀ᶠ n in atTop,
        ENNReal.ofReal (dyadic_p_variation_sum p G T n) < pVariationUpTo p G T + 1 := by
    -- Proof comment: a strict upper bound above the limsup eventually dominates the dyadic rows.
    have hlt_lim : pVariationUpTo p G T < pVariationUpTo p G T + 1 :=
      ENNReal.lt_add_right hfinite (by simp)
    simpa [pVariationUpTo] using
      (eventually_lt_of_limsup_lt
        (u := fun n : ℕ ↦ ENNReal.ofReal (dyadic_p_variation_sum p G T n))
        (b := pVariationUpTo p G T + 1) hlt_lim)
  -- Proof comment: convert the eventual ENNReal strict bound back to `ℝ` with `toReal`.
  exact hbound.mono fun n hn ↦ by
    have hsum_nonneg : 0 ≤ dyadic_p_variation_sum p G T n := by
      rw [dyadic_p_variation_sum, partitionPVariationSum]
      refine Finset.sum_nonneg ?_
      intro k hk
      exact Real.rpow_nonneg (abs_nonneg _) _
    have hupper_ne_top : pVariationUpTo p G T + 1 ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨hfinite, by simp⟩
    have htoReal :
        (ENNReal.ofReal (dyadic_p_variation_sum p G T n)).toReal <
          (pVariationUpTo p G T + 1).toReal :=
      (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hupper_ne_top).2 hn
    simpa [ENNReal.toReal_ofReal hsum_nonneg, ENNReal.toReal_add hfinite ENNReal.one_ne_top] using
      htoReal

/-- Helper for Remark 21.59: uniform continuity on `Icc 0 T` makes every active dyadic increment
eventually smaller than any prescribed positive scale. -/
lemma eventually_small_dyadicIncrements
    {G : PathSpace} (T : NNReal) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop,
      ∀ k,
        k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T →
          |G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              G (Definition2158.dyadicPartitionSequence n k)| ≤ η := by
  have hUC :
      UniformContinuousOn G (Icc 0 T) :=
    (isCompact_Icc : IsCompact (Icc (0 : NNReal) T)).uniformContinuousOn_of_continuous
      G.continuous.continuousOn
  rcases (Metric.uniformContinuousOn_iff_le.mp hUC) η hη with ⟨δ, hδ, hδclose⟩
  have hmesh :
      ∀ᶠ n in atTop,
        partitionMesh Definition2158.dyadicPartitionSequence n ≤ ENNReal.ofReal δ := by
    rcases
        (ENNReal.tendsto_atTop_zero.mp
          Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
          (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) with
      ⟨N, hN⟩
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  filter_upwards [hmesh] with n hn k hk
  have hx_mem :
      Definition2158.dyadicPartitionSequence n k ∈ Icc 0 T :=
    dyadicPartitionPoint_mem_Icc_of_lt_partitionBoundIndex n k T hk
  have hy_mem :
      partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T ∈ Icc 0 T := by
    constructor
    · exact bot_le
    · exact min_le_right _ _
  have hdist :
      edist (Definition2158.dyadicPartitionSequence n k)
          (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ≤
        ENNReal.ofReal δ := by
    exact le_trans (edist_dyadicPartitionPoint_partitionNextPointUpTo_le_mesh n k T hk) hn
  have hdist' :
      dist (Definition2158.dyadicPartitionSequence n k)
          (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ≤ δ := by
    exact (ENNReal.ofReal_le_ofReal_iff hδ.le).mp <| by
      simpa [edist_dist] using hdist
  -- Proof comment: once the mesh is below the uniform-continuity modulus, every active increment
  -- on the dyadic row is bounded by `η`.
  simpa [Real.dist_eq, abs_sub_comm] using
    hδclose (Definition2158.dyadicPartitionSequence n k) hx_mem
      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) hy_mem hdist'

/-- Helper for Remark 21.59: if each dyadic increment is bounded by `η`, then the dyadic
`p'`-variation row is controlled by `η^(p' - p)` times the dyadic `p`-variation row. -/
lemma dyadicPVariationSum_higherExponent_le_scale_mul_lowerExponentSum
    {p p' η : ℝ} (hp0 : 0 ≤ p) (hpp : p ≤ p')
    {G : PathSpace} (T : NNReal) (n : ℕ)
    (hinc : ∀ k, k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T →
      |G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
          G (Definition2158.dyadicPartitionSequence n k)| ≤ η) :
    dyadic_p_variation_sum p' G T n ≤ η ^ (p' - p) * dyadic_p_variation_sum p G T n := by
  let P := Definition2158.dyadicPartitionSequence
  let Δ : ℕ → ℝ := fun k ↦ G (partitionNextPointUpTo P n k T) - G (P n k)
  have hterm :
      ∀ k ∈ Finset.range (partitionBoundIndex P n T),
        Real.rpow (|Δ k|) p' ≤ η ^ (p' - p) * Real.rpow (|Δ k|) p := by
    intro k hk
    have hk_lt : k < partitionBoundIndex P n T := Finset.mem_range.mp hk
    have hΔ_le : |Δ k| ≤ η := by
      simpa [Δ, P] using hinc k hk_lt
    have hΔ_nonneg : 0 ≤ |Δ k| := abs_nonneg _
    have hgap_nonneg : 0 ≤ p' - p := sub_nonneg.mpr hpp
    have hsplit : p + (p' - p) = p' := by ring
    calc
      Real.rpow (|Δ k|) p' = Real.rpow (|Δ k|) (p + (p' - p)) := by rw [hsplit]
      _ = Real.rpow (|Δ k|) p * Real.rpow (|Δ k|) (p' - p) := by
            simpa using (Real.rpow_add_of_nonneg hΔ_nonneg hp0 hgap_nonneg)
      _ ≤ Real.rpow (|Δ k|) p * η ^ (p' - p) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hΔ_nonneg hΔ_le hgap_nonneg)
              (Real.rpow_nonneg hΔ_nonneg _)
      _ = η ^ (p' - p) * Real.rpow (|Δ k|) p := by
            rw [mul_comm]
  -- Proof comment: sum the termwise exponent comparison across the active dyadic row.
  rw [dyadic_p_variation_sum, partitionPVariationSum]
  calc
    Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦ Real.rpow (|Δ k|) p')
        ≤ Finset.sum (Finset.range (partitionBoundIndex P n T))
            (fun k ↦ η ^ (p' - p) * Real.rpow (|Δ k|) p) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact hterm k hk
    _ = η ^ (p' - p) *
          Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦ Real.rpow (|Δ k|) p) := by
            rw [Finset.mul_sum]
    _ = η ^ (p' - p) * dyadic_p_variation_sum p G T n := by
          simp [dyadic_p_variation_sum, partitionPVariationSum, Δ, P]

/-- Remark 21.59: if `0 < p`, `p' > p`, and `V_T^p(G) < ∞`, then `V_T^{p'}(G) = 0`. -/
theorem pVariationUpTo_eq_zero_of_lt_exponent_of_ne_top
    {p p' : ℝ} (hp : 0 < p) (hpp' : p < p') {G : PathSpace} (T : NNReal)
    (hfinite : pVariationUpTo p G T ≠ ∞) :
    pVariationUpTo p' G T = 0 := by
  let L : ℝ := (pVariationUpTo p G T).toReal
  have hp0 : 0 ≤ p := hp.le
  have hgap : 0 < p' - p := sub_pos.mpr hpp'
  have hlower :
      ∀ᶠ n in atTop, dyadic_p_variation_sum p G T n < L + 1 := by
    simpa [L] using eventually_dyadicPVariationSum_lt_toReal_pVariationUpTo_add_one T hfinite
  have hlim : Tendsto (dyadic_p_variation_sum p' G T) atTop (nhds 0) := by
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    have hscaled :
        Tendsto (fun η : ℝ ↦ η ^ (p' - p) * (L + 1)) (𝓝[>] 0) (𝓝 0) := by
      -- Proof comment: the scaling factor tends to `0` with the increment bound `η`.
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      simpa [Real.zero_rpow hgap.ne', zero_mul] using
        (((Real.continuous_rpow_const hgap.le).mul
          (continuous_const : Continuous fun _ : ℝ ↦ L + 1)).tendsto 0)
    have hscaled_small :
        ∀ᶠ η : ℝ in 𝓝[>] 0, |η ^ (p' - p) * (L + 1)| < ε := by
      simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 hscaled ε hε)
    have hpositive_window : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT zero_lt_one
    rcases (hscaled_small.and hpositive_window).exists with ⟨η, hη_small_abs, hη_mem⟩
    have hη_pos : 0 < η := hη_mem.1
    have hη_nonneg : 0 ≤ η := hη_pos.le
    have hη_small :
        η ^ (p' - p) * (L + 1) < ε := by
      have hnonneg : 0 ≤ η ^ (p' - p) * (L + 1) := by
        refine mul_nonneg (Real.rpow_nonneg hη_nonneg _) ?_
        linarith [ENNReal.toReal_nonneg (a := pVariationUpTo p G T)]
      simpa [abs_of_nonneg hnonneg] using hη_small_abs
    have hsmooth :
        ∀ᶠ n in atTop,
          ∀ k,
            k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T →
              |G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)| ≤ η :=
      eventually_small_dyadicIncrements T hη_pos
    have hfinal :
        ∀ᶠ n in atTop, dist (dyadic_p_variation_sum p' G T n) 0 < ε := by
      filter_upwards [hsmooth, hlower] with n hninc hnlow
      have hrow_le :
          dyadic_p_variation_sum p' G T n ≤
            η ^ (p' - p) * dyadic_p_variation_sum p G T n :=
        dyadicPVariationSum_higherExponent_le_scale_mul_lowerExponentSum
          hp0 hpp'.le T n hninc
      have hrow_nonneg : 0 ≤ dyadic_p_variation_sum p' G T n := by
        rw [dyadic_p_variation_sum, partitionPVariationSum]
        refine Finset.sum_nonneg ?_
        intro k hk
        exact Real.rpow_nonneg (abs_nonneg _) _
      have hlt :
          dyadic_p_variation_sum p' G T n < ε := by
        have hηpow_pos : 0 < η ^ (p' - p) := Real.rpow_pos_of_pos hη_pos _
        calc
          dyadic_p_variation_sum p' G T n ≤
              η ^ (p' - p) * dyadic_p_variation_sum p G T n := hrow_le
          _ < η ^ (p' - p) * (L + 1) := by
                exact mul_lt_mul_of_pos_left hnlow hηpow_pos
          _ < ε := hη_small
      rw [Real.dist_eq]
      simpa [abs_of_nonneg hrow_nonneg] using hlt
    rcases Filter.Eventually.exists_forall_of_atTop hfinal with ⟨N, hN⟩
    exact ⟨N, hN⟩
  have hOfReal :
      Tendsto (fun n ↦ ENNReal.ofReal (dyadic_p_variation_sum p' G T n)) atTop (𝓝 0) := by
    -- Proof comment: `ENNReal.ofReal` transports the real convergence of the dyadic sums to `0`.
    simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hlim
  -- Proof comment: the defining `limsup` of the higher-exponent dyadic sums is therefore `0`.
  simpa [pVariationUpTo] using hOfReal.limsup_eq

/-- Helper for Remark 21.59: the dyadic `p = 1` sum on `[0, T]` is controlled by the total
variation of `G` on `Icc 0 T`. -/
lemma dyadicPVariationSumOne_le_eVariationOn_Icc_toReal
    {G : PathSpace} (T : NNReal) (n : ℕ)
    (hvar_finite : eVariationOn G (Icc 0 T) ≠ ∞) :
    dyadic_p_variation_sum 1 G T n ≤ (eVariationOn G (Icc 0 T)).toReal := by
  -- Proof comment: convert the clipped ENNReal first-variation bound to `ℝ` using finiteness of
  -- the total variation.
  have hmono :=
    ENNReal.toReal_mono hvar_finite (dyadicVariationSumUpTo_le_eVariationOn_Icc G T n)
  simpa [dyadicVariationSumUpTo_toReal_eq_dyadicPVariationSumOne G T n] using hmono

/-- Helper for Remark 21.59: for paths of locally finite variation, the dyadic quadratic
variation sums on `[0, T]` converge to `0`. -/
theorem dyadicPVariationSumTwo_tendsto_zero_of_locallyBoundedVariationOn
    {G : PathSpace} (hG : LocallyBoundedVariationOn G univ) (T : NNReal) :
    Tendsto (dyadic_p_variation_sum 2 G T) atTop (nhds 0) := by
  have hvar_finite : eVariationOn G (Icc 0 T) ≠ ∞ := by
    simpa using hG 0 T (mem_univ _) (mem_univ _)
  have hAbsSum_le :
      ∀ n : ℕ, dyadic_p_variation_sum 1 G T n ≤ (eVariationOn G (Icc 0 T)).toReal := by
    intro n
    -- Proof comment: the `p = 1` dyadic row is one admissible first-variation approximation.
    exact dyadicPVariationSumOne_le_eVariationOn_Icc_toReal T n hvar_finite
  rw [Metric.tendsto_atTop]
  intro ε hε
  let varT : ℝ := (eVariationOn G (Icc 0 T)).toReal
  let η : ℝ := ε / (varT + 1)
  have hη_pos : 0 < η := by
    dsimp [η, varT]
    positivity
  have hUC :
      UniformContinuousOn G (Icc 0 T) :=
    (isCompact_Icc : IsCompact (Icc (0 : NNReal) T)).uniformContinuousOn_of_continuous
      G.continuous.continuousOn
  rcases (Metric.uniformContinuousOn_iff_le.mp hUC) η hη_pos with ⟨δ, hδ, hδclose⟩
  have hmesh :
      ∀ᶠ n in atTop,
        partitionMesh Definition2158.dyadicPartitionSequence n ≤ ENNReal.ofReal δ := by
    rcases
        (ENNReal.tendsto_atTop_zero.mp
          Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
          (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) with
      ⟨N, hN⟩
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  rcases Filter.Eventually.exists_forall_of_atTop hmesh with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hnN
  have hn : partitionMesh Definition2158.dyadicPartitionSequence n ≤ ENNReal.ofReal δ := hN n hnN
  let P := Definition2158.dyadicPartitionSequence
  let Δ : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo P n k T) - G (P n k)
  have hsq_repr :
      dyadic_p_variation_sum 2 G T n =
        Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦ (Δ k) ^ 2) := by
    -- Proof comment: at exponent `2`, the dyadic `rpow` sum is exactly the sum of squares of the
    -- clipped increments.
    rw [dyadic_p_variation_sum, partitionPVariationSum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [← Real.rpow_natCast]
    simp [Δ, P, sq_abs]
  have hsq_nonneg : 0 ≤ dyadic_p_variation_sum 2 G T n := by
    rw [hsq_repr]
    exact Finset.sum_nonneg fun k hk ↦ sq_nonneg (Δ k)
  have hsq_lt : dyadic_p_variation_sum 2 G T n < ε := by
    calc
      dyadic_p_variation_sum 2 G T n =
          Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦ (Δ k) ^ 2) := hsq_repr
      _ ≤ Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦ η * |Δ k|) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            have hk_lt : k < partitionBoundIndex P n T := Finset.mem_range.mp hk
            have hx_mem : P n k ∈ Icc 0 T :=
              dyadicPartitionPoint_mem_Icc_of_lt_partitionBoundIndex n k T <| by
                simpa [P] using hk_lt
            have hy_mem : partitionNextPointUpTo P n k T ∈ Icc 0 T := by
              constructor
              · exact bot_le
              · exact min_le_right _ _
            have hdist :
                edist (P n k) (partitionNextPointUpTo P n k T) ≤ ENNReal.ofReal δ := by
              exact le_trans
                (edist_dyadicPartitionPoint_partitionNextPointUpTo_le_mesh n k T <| by
                  simpa [P] using hk_lt) hn
            have hdist' : dist (P n k) (partitionNextPointUpTo P n k T) ≤ δ := by
              exact (ENNReal.ofReal_le_ofReal_iff hδ.le).mp <| by
                simpa [edist_dist] using hdist
            have hΔ_le : |Δ k| ≤ η := by
              simpa [Δ, Real.dist_eq, abs_sub_comm] using hδclose (P n k) hx_mem
                (partitionNextPointUpTo P n k T) hy_mem hdist'
            rw [← sq_abs]
            nlinarith [hΔ_le, abs_nonneg (Δ k)]
      _ = η * dyadic_p_variation_sum 1 G T n := by
            rw [dyadic_p_variation_sum, partitionPVariationSum, Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [Real.rpow_one, Δ, P]
      _ ≤ η * (eVariationOn G (Icc 0 T)).toReal := by
            exact mul_le_mul_of_nonneg_left (hAbsSum_le n) hη_pos.le
      _ < η * (varT + 1) := by
            have hvar_lt : (eVariationOn G (Icc 0 T)).toReal < varT + 1 := by
              dsimp [varT]
              linarith
            exact mul_lt_mul_of_pos_left hvar_lt hη_pos
      _ = ε := by
            dsimp [η, varT]
            field_simp [show (eVariationOn G (Icc 0 T)).toReal + 1 ≠ 0 by positivity]
  have hdist_eq : dist (dyadic_p_variation_sum 2 G T n) 0 = dyadic_p_variation_sum 2 G T n := by
    -- Proof comment: the dyadic quadratic sum is nonnegative, so its distance to `0` is itself.
    rw [Real.dist_eq]
    simpa using abs_of_nonneg hsq_nonneg
  rw [hdist_eq]
  exact hsq_lt

/-- Helper for Remark 21.59: a continuous path of locally finite variation has identically
vanishing canonical quadratic variation. -/
theorem pVariationUpTo_two_eq_zero_of_locallyBoundedVariationOn
    {G : PathSpace} (hG : LocallyBoundedVariationOn G univ) :
    pVariationUpTo 2 G = 0 := by
  funext T
  have hlim :
      Tendsto (dyadic_p_variation_sum 2 G T) atTop (nhds 0) :=
    dyadicPVariationSumTwo_tendsto_zero_of_locallyBoundedVariationOn hG T
  have hOfReal :
      Tendsto (fun n ↦ ENNReal.ofReal (dyadic_p_variation_sum 2 G T n)) atTop (𝓝 0) := by
    -- Proof comment: `ENNReal.ofReal` preserves the real convergence to `0`.
    simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hlim
  -- Proof comment: the defining `limsup` of the dyadic square sums is therefore `0`.
  simpa [pVariationUpTo] using hOfReal.limsup_eq

/-- Helper for Remark 21.59: if `G` has locally finite variation, then the zero path realizes
its dyadic square variation. -/
theorem hasSquareVariationAlong_zero_of_locallyBoundedVariationOn
    {G : PathSpace} (hG : LocallyBoundedVariationOn G univ) :
    HasSquareVariationAlong G 0 := by
  intro T
  -- Proof comment: the preceding dyadic quadratic sums already converge to `0` as real numbers.
  simpa using dyadicPVariationSumTwo_tendsto_zero_of_locallyBoundedVariationOn hG T

/-- Helper for Remark 21.59: any dyadic first-variation realization agrees with the canonical
total variation on `[0,T]`. -/
theorem oneVariationUpTo_eq_eVariationOn_Icc
    {G : PathSpace} {V : PathwiseProcess} (hV : HasPVariationAlong 1 G V) :
    ∀ T : NNReal, V T = (eVariationOn G (Icc 0 T)).toReal := by
  intro T
  have hV_ofReal :
      Tendsto (fun n ↦ ENNReal.ofReal (dyadic_p_variation_sum 1 G T n)) atTop
        (𝓝 (ENNReal.ofReal (V T))) := by
    -- Proof comment: apply `ENNReal.ofReal` to the defining `p = 1` variation convergence.
    exact (ENNReal.continuous_ofReal.tendsto _).comp (HasPVariationAlong.tendsto_partition_sum hV T)
  have hDyadic :
      Tendsto (fun n ↦ ENNReal.ofReal (dyadic_p_variation_sum 1 G T n)) atTop
        (𝓝 (eVariationOn G (Icc 0 T))) := by
    -- Proof comment: replace the real-valued dyadic sums by the equivalent clipped `ENNReal`
    -- variation sums and then use the canonical clipped-dyadic convergence theorem.
    simpa [dyadicVariationSumUpTo_eq_ofReal_dyadicPVariationSumOne_fun G T] using
      (dyadicVariationSumUpTo_tendsto_eVariationOn_Icc G T)
  have hEq :
      eVariationOn G (Icc 0 T) = ENNReal.ofReal (V T) := by
    -- Proof comment: both ENNReal-valued sequences are identical, so uniqueness of limits fixes
    -- the canonical variation value.
    exact tendsto_nhds_unique hDyadic hV_ofReal
  have hV_nonneg : 0 ≤ V T := by
    -- Proof comment: each dyadic `p = 1` partition sum is nonnegative, hence so is its limit.
    exact ge_of_tendsto' (HasPVariationAlong.tendsto_partition_sum hV T) fun n ↦ by
      rw [← dyadicVariationSumUpTo_toReal_eq_dyadicPVariationSumOne]
      exact ENNReal.toReal_nonneg
  have htoReal := congrArg ENNReal.toReal hEq
  simpa [ENNReal.toReal_ofReal hV_nonneg] using htoReal.symm
