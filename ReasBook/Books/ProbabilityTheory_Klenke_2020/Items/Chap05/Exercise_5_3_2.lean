/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Theorem_4_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Exercise 5.3.2: the normalized `(n + 1)`st term is the difference between the
successive empirical averages needed to control large jumps from almost-sure convergence of the
averages. -/
lemma normalizedTerm_eq_succAverage_sub_scaledAverage
    (u : ℕ → ℝ) (n : ℕ) :
    u (n + 1) / (n + 1 : ℝ) =
      (∑ i ∈ Finset.range (n + 1), u (i + 1)) / (n + 1 : ℝ) -
        ((n : ℝ) / (n + 1 : ℝ)) * ((∑ i ∈ Finset.range n, u (i + 1)) / n) := by
  cases n with
  | zero =>
      -- Proof comment: the first average has one summand and the zeroth average is empty.
      simp
  | succ k =>
      -- Proof comment: expand the last term of the longer average and simplify algebraically.
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hk' : ((k : ℝ) + 2) ≠ 0 := by positivity
      rw [Finset.sum_range_succ]
      field_simp [hk, hk']
      ring

/-- Helper for Exercise 5.3.2: independent measurable coordinates yield an independent family of
coordinatewise threshold events. -/
lemma iIndepSet_preimage_of_iIndepFun
    {E : Type*} [MeasurableSpace E] (μ : Measure Ω) (Y : ℕ → Ω → E)
    (hY_meas : ∀ n, Measurable (Y n)) (hY_indep : iIndepFun Y μ)
    (s : ℕ → Set E) (hs : ∀ n, MeasurableSet (s n)) :
    iIndepSet (fun n ↦ Y n ⁻¹' s n) μ := by
  -- Proof comment: reduce set independence to the finite-product identity already packaged for
  -- independent random variables.
  rw [ProbabilityTheory.iIndepSet_iff_meas_biInter fun i => by
    simpa using (hY_meas i) (hs i)]
  intro t
  simpa using hY_indep.measure_inter_preimage_eq_mul t fun i _ ↦ hs i

/-- Helper for Exercise 5.3.2: for a nonnegative real random variable, divergence of the shifted
tail-probability series follows from nonintegrability. -/
lemma tsum_prob_mem_Ioi_succ_eq_top_of_notIntegrable_of_nonneg
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ_meas : Measurable Z) (hZ_nonneg : 0 ≤ᵐ[μ] Z) (hZ_not_int : ¬ Integrable Z μ) :
    (∑' n : ℕ, μ {ω | Z ω ∈ Set.Ioi (((n + 1 : ℕ) : ℝ))}) = ⊤ := by
  by_contra htail
  have hzero_ne_top : μ {ω | Z ω ∈ Set.Ioi (((0 : ℕ) : ℝ))} ≠ ⊤ := by simp
  have hfull_ne_top : (∑' n : ℕ, μ {ω | Z ω ∈ Set.Ioi (n : ℝ)}) ≠ ⊤ := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    exact ENNReal.add_ne_top.2 ⟨hzero_ne_top, htail⟩
  have hlintegral_lt_top :
      ∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ < ⊤ := by
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hfull_ne_top)
    simpa [Set.mem_Ioi] using
      (lintegral_le_tsum_measure_strict_superlevel_nat (μ := μ) hZ_meas hZ_nonneg)
  have hZ_int : Integrable Z μ := by
    -- Proof comment: finite `lintegral` is the missing integrability component for an
    -- a.e.-nonnegative real random variable.
    refine ⟨hZ_meas.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hZ_nonneg]
    exact hlintegral_lt_top
  exact hZ_not_int hZ_int

/-- Helper for Exercise 5.3.2: integrability of one coordinate forces summability of the large-jump
probabilities `P[(n + 1) < |Xₙ|]`. -/
lemma largeJumpSeries_lt_top_of_integrable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX_iid : IsIID X P)
    (hX0_int : Integrable (X 0) P) :
    (∑' n : ℕ, P {ω | (((n + 1 : ℕ) : ℝ)) < |X n ω|}) < ⊤ := by
  let _ : MeasureSpace Ω := ⟨P⟩
  have hAbs_int : Integrable (fun ω ↦ |X 0 ω|) P := by
    simpa [Real.norm_eq_abs] using hX0_int.norm
  have hbase_unshift :
      (∑' n : ℕ, P {ω | |X 0 ω| ∈ Set.Ioi (n : ℝ)}) < ⊤ := by
    simpa using ProbabilityTheory.tsum_prob_mem_Ioi_lt_top hAbs_int fun ω ↦ abs_nonneg (X 0 ω)
  have hshift_le :
      (∑' n : ℕ, P {ω | |X 0 ω| ∈ Set.Ioi (((n + 1 : ℕ) : ℝ))}) ≤
        ∑' n : ℕ, P {ω | |X 0 ω| ∈ Set.Ioi (n : ℝ)} := by
    refine ENNReal.tsum_le_tsum ?_
    intro n
    refine measure_mono ?_
    intro ω hω
    have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ n
    have hω' : ((n + 1 : ℕ) : ℝ) < |X 0 ω| := by
      simpa [Set.mem_Ioi] using hω
    simpa [Set.mem_Ioi] using lt_of_le_of_lt hn hω'
  have hbase_shift :
      (∑' n : ℕ, P {ω | |X 0 ω| ∈ Set.Ioi (((n + 1 : ℕ) : ℝ))}) < ⊤ :=
    lt_of_le_of_lt hshift_le hbase_unshift
  calc
    (∑' n : ℕ, P {ω | (((n + 1 : ℕ) : ℝ)) < |X n ω|})
        = ∑' n : ℕ, P {ω | |X 0 ω| ∈ Set.Ioi (((n + 1 : ℕ) : ℝ))} := by
            refine tsum_congr fun n ↦ ?_
            simpa [Set.mem_Ioi] using
              ((hX_iid.identDistrib n 0).comp measurable_abs).measure_mem_eq measurableSet_Ioi
    _ < ⊤ := hbase_shift

/-- Helper for Exercise 5.3.2: after replacing the coordinates by measurable versions, the
large-jump events form an independent family. -/
lemma largeJumpEvents_iIndepSet
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, Measurable (X n)) (hX_iid : IsIID X P) :
    iIndepSet (fun n ↦ {ω | (((n + 1 : ℕ) : ℝ)) < |X n ω|}) P := by
  -- Proof comment: compose the independent family with `abs` and then take threshold preimages.
  refine iIndepSet_preimage_of_iIndepFun (μ := P) (Y := fun n ω ↦ |X n ω|) ?_ ?_
    (fun n ↦ Set.Ioi (((n + 1 : ℕ) : ℝ))) ?_
  · intro n
    fun_prop
  · simpa using hX_iid.iIndepFun.comp (fun _ ↦ abs) (fun _ ↦ measurable_abs)
  · intro n
    exact measurableSet_Ioi

/-- Helper for Exercise 5.3.2: if `X₀` is not integrable, then the large-jump probability series
`∑ P[(n + 1) < |Xₙ|]` diverges. -/
lemma notIntegrable_imp_largeJumpSeries_eq_top
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, Measurable (X n)) (hX_iid : IsIID X P)
    (hX0_not_int : ¬ Integrable (X 0) P) :
    (∑' n : ℕ, P {ω | (((n + 1 : ℕ) : ℝ)) < |X n ω|}) = ⊤ := by
  have hX0_aestronglyMeasurable : AEStronglyMeasurable (X 0) P :=
    (hX_iid.identDistrib 0 0).aemeasurable_fst.aestronglyMeasurable
  have hAbs_not_int : ¬ Integrable (fun ω ↦ |X 0 ω|) P := by
    intro hAbs_int
    have hX0_int : Integrable (X 0) P := by
      exact (integrable_norm_iff hX0_aestronglyMeasurable).1 <| by
        simpa [Real.norm_eq_abs] using hAbs_int
    exact hX0_not_int hX0_int
  have hAbs_eq_top :
      (∑' n : ℕ, P {ω | |X 0 ω| ∈ Set.Ioi (((n + 1 : ℕ) : ℝ))}) = ⊤ := by
    exact tsum_prob_mem_Ioi_succ_eq_top_of_notIntegrable_of_nonneg
      P ((hX_meas 0).norm) (Filter.Eventually.of_forall fun ω ↦ abs_nonneg (X 0 ω)) hAbs_not_int
  calc
    (∑' n : ℕ, P {ω | (((n + 1 : ℕ) : ℝ)) < |X n ω|})
        = ∑' n : ℕ, P {ω | |X 0 ω| ∈ Set.Ioi (((n + 1 : ℕ) : ℝ))} := by
            refine tsum_congr fun n ↦ ?_
            simpa [Set.mem_Ioi] using
              ((hX_iid.identDistrib n 0).comp measurable_abs).measure_mem_eq measurableSet_Ioi
    _ = ⊤ := hAbs_eq_top

/-- Helper for Exercise 5.3.2: almost-sure convergence of the empirical averages forces the
large-jump event `|(X_{n+1})| > n + 1` to occur only finitely often almost surely. -/
lemma measure_limsup_abs_gt_linear_shift_eq_zero_of_ae_tendsto_average
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (h_tendsto :
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n) atTop (𝓝 (Y ω))) :
    P (limsup (fun n : ℕ ↦ {ω | (((n + 1 : ℕ) : ℝ)) < |X (n + 1) ω|}) atTop) = 0 := by
  let A : ℕ → Set Ω := fun n ↦ {ω | (((n + 1 : ℕ) : ℝ)) < |X (n + 1) ω|}
  have hAE :
      ∀ᵐ ω ∂P, ω ∉ limsup A atTop := by
    filter_upwards [h_tendsto] with ω hω
    have hω_shift :
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range (n + 1), X (i + 1) ω) / (n + 1 : ℝ))
          atTop (𝓝 (Y ω)) := by
      -- Proof comment: shifting the empirical-average sequence by one index preserves its limit.
      convert hω.comp (tendsto_add_atTop_nat 1) using 1
      ext n
      simp [Function.comp, Nat.cast_add, Nat.cast_one]
    have hratio :
        Tendsto (fun n : ℕ ↦ (n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 1) := by
      simpa [Nat.cast_add, Nat.cast_one] using (tendsto_natCast_div_add_atTop (1 : ℝ))
    have hscaled :
        Tendsto
          (fun n : ℕ ↦
            ((n : ℝ) / (n + 1 : ℝ)) * ((∑ i ∈ Finset.range n, X (i + 1) ω) / n))
          atTop (𝓝 (Y ω)) := by
      -- Proof comment: multiply the convergent averages by a scalar factor tending to `1`.
      simpa using hratio.mul hω
    have hterm :
        Tendsto (fun n : ℕ ↦ X (n + 1) ω / (n + 1 : ℝ)) atTop (𝓝 0) := by
      -- Proof comment: each normalized term is the difference of two expressions converging to
      -- the same limit `Y ω`.
      have h_eq :
          (fun n : ℕ ↦ X (n + 1) ω / (n + 1 : ℝ)) =
            fun n : ℕ ↦
              (∑ i ∈ Finset.range (n + 1), X (i + 1) ω) / (n + 1 : ℝ) -
                ((n : ℝ) / (n + 1 : ℝ)) * ((∑ i ∈ Finset.range n, X (i + 1) ω) / n) := by
        funext n
        simpa using normalizedTerm_eq_succAverage_sub_scaledAverage (u := fun k ↦ X k ω) n
      rw [h_eq]
      simpa using hω_shift.sub hscaled
    have hsmall :
        ∀ᶠ n : ℕ in atTop, |X (n + 1) ω / (n + 1 : ℝ)| < (1 : ℝ) := by
      have hmem :
          ∀ᶠ n : ℕ in atTop, X (n + 1) ω / (n + 1 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 :=
        hterm (isOpen_Ioo.mem_nhds <| by constructor <;> norm_num)
      filter_upwards [hmem] with n hn
      simpa [Set.mem_Ioo, abs_lt] using hn
    have hnot_eventually :
        ∀ᶠ n : ℕ in atTop, ω ∉ A n := by
      filter_upwards [hsmall] with n hn hA
      have hpos : (0 : ℝ) < n + 1 := by positivity
      have habs_gt :
          1 < |X (n + 1) ω / (n + 1 : ℝ)| := by
        have hA' : (n + 1 : ℝ) < |X (n + 1) ω| := by
          simpa [A] using hA
        rw [abs_div, abs_of_pos hpos]
        exact (one_lt_div_iff).2 <| Or.inl ⟨hpos, hA'⟩
      exact (not_lt_of_ge (le_of_lt hn)) habs_gt
    have hnot_freq : ¬ ∃ᶠ n : ℕ in atTop, ω ∈ A n := by
      rw [Filter.not_frequently]
      exact hnot_eventually
    simpa [A, Filter.mem_limsup_iff_frequently_mem] using hnot_freq
  -- Proof comment: almost sure exclusion from the limsup is exactly the zero-measure conclusion.
  rw [ae_iff] at hAE
  simpa [A] using hAE

-- Proof sketch: rewrite the event “`|X n| > n + 1` infinitely often” as membership in the limsup
-- of the tail events. For the forward implication, use the second Borel--Cantelli lemma together
-- with the i.i.d. hypothesis to force a divergent tail-probability series to give limsup measure
-- `1`; for the reverse implication, apply the first Borel--Cantelli lemma using the classical
-- tail characterization of integrability. This is internal bridge material for
-- `integrable_and_ae_eq_expectation_of_iid_ae_tendsto_average`, not a separate source-facing
-- chapter theorem.
private theorem measure_limsup_abs_gt_linear_eq_zero_iff_integrable_of_iid
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX_iid : IsIID X P) :
    P (limsup (fun n : ℕ ↦ {ω | (((n + 1 : ℕ) : ℝ)) < |X n ω|}) atTop) = 0 ↔ Integrable (X 0) P :=
  by
  classical
  let Y : ℕ → Ω → ℝ := fun n ↦ ((hX_iid.identDistrib n 0).aemeasurable_fst).mk (X n)
  let A : ℕ → Set Ω := fun n ↦ {ω | (((n + 1 : ℕ) : ℝ)) < |X n ω|}
  let B : ℕ → Set Ω := fun n ↦ {ω | (((n + 1 : ℕ) : ℝ)) < |Y n ω|}
  have hY_meas : ∀ n, Measurable (Y n) := by
    intro n
    exact ((hX_iid.identDistrib n 0).aemeasurable_fst).measurable_mk
  have hY_ae : ∀ n, X n =ᵐ[P] Y n := by
    intro n
    exact ((hX_iid.identDistrib n 0).aemeasurable_fst).ae_eq_mk
  have hY_iid : IsIID Y P := by
    refine ⟨hX_iid.iIndepFun.congr hY_ae, ?_⟩
    intro i j
    refine
      (IdentDistrib.of_ae_eq ((hX_iid.identDistrib i j).aemeasurable_fst) (hY_ae i)).symm.trans ?_
    refine (hX_iid.identDistrib i j).trans ?_
    exact IdentDistrib.of_ae_eq ((hX_iid.identDistrib i j).aemeasurable_snd) (hY_ae j)
  have hAeqB : ∀ n, A n =ᵐ[P] B n := by
    intro n
    exact (hY_ae n).mono fun ω hω ↦ by
      change ((((n + 1 : ℕ) : ℝ) < |X n ω|) = (((n + 1 : ℕ) : ℝ) < |Y n ω|))
      simp [hω]
  have hlimsup_eq :
      limsup (α := Set Ω) A atTop =ᵐ[P] limsup (α := Set Ω) B atTop := by
    refine eventuallyEq_set.2 ?_
    have hAll : ∀ᵐ ω ∂P, ∀ n, ω ∈ A n ↔ ω ∈ B n := by
      rw [ae_all_iff]
      intro n
      simpa [eventuallyEq_set] using hAeqB n
    filter_upwards [hAll] with ω hω
    have hfreq :
        (∃ᶠ n : ℕ in atTop, ω ∈ A n) ↔ ∃ᶠ n : ℕ in atTop, ω ∈ B n := by
      have hAB : (fun n : ℕ ↦ ω ∈ A n) = fun n : ℕ ↦ ω ∈ B n := by
        funext n
        exact propext (hω n)
      simp [hAB]
    rw [Filter.mem_limsup_iff_frequently_mem, Filter.mem_limsup_iff_frequently_mem]
    exact hfreq
  constructor
  · intro hlimsup_zero
    by_contra hX0_not_int
    have hY0_not_int : ¬ Integrable (Y 0) P := by
      intro hY0_int
      exact hX0_not_int (hY0_int.congr (hY_ae 0).symm)
    have hseries_eq_top :
        (∑' n : ℕ, P (B n)) = ⊤ := by
      simpa [B] using notIntegrable_imp_largeJumpSeries_eq_top P Y hY_meas hY_iid hY0_not_int
    have hB_meas : ∀ n, MeasurableSet (B n) := by
      intro n
      change MeasurableSet ((fun ω ↦ |Y n ω|) ⁻¹' Set.Ioi (((n + 1 : ℕ) : ℝ)))
      simpa using (hY_meas n).norm measurableSet_Ioi
    have hlimsup_one :
        P (limsup B atTop) = 1 := by
      exact ProbabilityTheory.measure_limsup_eq_one
        (μ := P) (s := B) hB_meas
        (largeJumpEvents_iIndepSet P Y hY_meas hY_iid) hseries_eq_top
    have hA_zero : P (limsup A atTop) = 0 := by
      simpa [A] using hlimsup_zero
    have hmeasure_eq :
        P (limsup (α := Set Ω) A atTop) = P (limsup (α := Set Ω) B atTop) :=
      measure_congr hlimsup_eq
    have hlimsup_zero_B :
        P (limsup B atTop) = 0 := by
      exact hmeasure_eq.symm.trans hA_zero
    have : (0 : ENNReal) = 1 := hlimsup_zero_B.symm.trans hlimsup_one
    exact zero_ne_one this
  · intro hX0_int
    have hY0_int : Integrable (Y 0) P := by
      exact hX0_int.congr (hY_ae 0)
    have hseries_lt_top :
        (∑' n : ℕ, P (B n)) < ⊤ := by
      simpa [B] using largeJumpSeries_lt_top_of_integrable P Y hY_iid hY0_int
    have hlimsup_zero_B :
        P (limsup B atTop) = 0 := by
      exact MeasureTheory.measure_limsup_atTop_eq_zero (ne_of_lt hseries_lt_top)
    have hmeasure_eq :
        P (limsup (α := Set Ω) A atTop) = P (limsup (α := Set Ω) B atTop) :=
      measure_congr hlimsup_eq
    have hA_zero : P (limsup A atTop) = 0 := by
      exact hmeasure_eq.trans hlimsup_zero_B
    simpa [A] using hA_zero

-- Proof sketch: apply the hint theorem to the shifted i.i.d. sequence `n ↦ X (n + 1)` to obtain
-- `Integrable (X 1) P` from the assumed almost sure convergence of the empirical averages. Then
-- apply the strong law of large numbers to the same shifted i.i.d. sequence and compare its almost
-- sure limit `P[X 1]` with the given almost sure limit `Y`, yielding `Y = P[X 1]` almost surely.
/-- Exercise 5.3.2: if the empirical averages of an independent identically distributed real
sequence `X₁, X₂, …` converge almost surely to a random variable `Y`, then `X₁` is integrable and
the limit `Y` is almost surely equal to the common expectation `𝔼[X₁]`. -/
theorem integrable_and_ae_eq_expectation_of_iid_ae_tendsto_average
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (h_tendsto :
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n) atTop (𝓝 (Y ω))) :
    Integrable (X 1) P ∧ Y =ᵐ[P] fun _ ↦ P[X 1] := by
  have hX1_int :
      Integrable (X 1) P := by
    -- Proof comment: the private large-jump criterion applies directly to the shifted i.i.d.
    -- sequence from the statement.
    refine
      (measure_limsup_abs_gt_linear_eq_zero_iff_integrable_of_iid
        P (fun n ↦ X (n + 1)) hX_iid).mp ?_
    exact measure_limsup_abs_gt_linear_shift_eq_zero_of_ae_tendsto_average P X Y h_tendsto
  have hX_pairwise : Pairwise fun i j ↦ X (i + 1) ⟂ᵢ[P] X (j + 1) := by
    intro i j hij
    exact hX_iid.iIndepFun.indepFun hij
  have hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P := by
    intro n
    simpa using hX_iid.identDistrib n 0
  have hSLLN :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n) atTop (𝓝 P[X 1]) := by
    -- Proof comment: once integrability is known, the strong law supplies the canonical limit.
    simpa using
      ProbabilityTheory.strong_law_ae_real (fun n ↦ X (n + 1)) hX1_int hX_pairwise hX_ident
  -- Proof comment: almost-sure limits in `ℝ` are unique, so the given limit agrees with the
  -- strong-law limit.
  exact ⟨hX1_int, MeasureTheory.AEEqFun.tendsto_ae_unique h_tendsto hSLLN⟩
