/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

variable (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
variable (hX_iid : IsIID (fun n ↦ X (n + 1)) P)

/-- Helper for Exercise 5.1.3: convergence of the shifted empirical averages forces the
normalized shifted terms to converge to `0`. -/
lemma normalizedTerm_tendsto_zero_of_average_tendsto
    (u : ℕ → ℝ) {a : ℝ}
    (havg : Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, u (i + 1)) / n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ u (n + 1) / (n + 1 : ℝ)) atTop (𝓝 0) := by
  let avg : ℕ → ℝ := fun n ↦ (∑ i ∈ Finset.range n, u (i + 1)) / n
  have havg_succ : Tendsto (fun n : ℕ ↦ avg (n + 1)) atTop (𝓝 a) := by
    -- Proof comment: shifting the averaging index preserves the same `atTop` limit.
    simpa [Function.comp] using havg.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n : ℕ ↦ (n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 1) := by
    -- Proof comment: the deterministic prefactor converges to `1`.
    simpa using (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hscaled : Tendsto (fun n : ℕ ↦ ((n : ℝ) / (n + 1 : ℝ)) * avg n) atTop (𝓝 (1 * a)) := by
    -- Proof comment: multiplying by an asymptotically unit factor preserves the limit.
    exact hratio.mul havg
  have hdiff :
      Tendsto
        (fun n : ℕ ↦ avg (n + 1) - ((n : ℝ) / (n + 1 : ℝ)) * avg n)
        atTop (𝓝 (a - 1 * a)) := by
    -- Proof comment: the normalized term is the difference of two asymptotically equal pieces.
    exact havg_succ.sub hscaled
  simpa [avg, normalizedTerm_eq_succAverage_sub_scaledAverage, one_mul] using hdiff

-- Proof sketch: apply `ProbabilityTheory.strong_law_ae_real` to the shifted sequence
-- `n ↦ X (n + 1)` and then pass from convergence of the empirical averages to convergence of the
-- normalized individual terms by the deterministic average-difference identity above.
include hX_iid
/-- First part of Exercise 5.1.3: the source-facing limsup conclusion is a canonical consequence of the
strong law for integrable i.i.d. real random variables, so the normalized sequence `Xₙ / n`,
represented in Lean by the terms `X 1 / 1, X 2 / 2, …`, has almost-sure limsup `0` without any
extra nonnegativity hypothesis. -/
theorem ae_limsup_normalized_iid_eq_zero_of_integrable
    (hX1_integrable : Integrable (X 1) P) :
    ∀ᵐ ω ∂P, limsup (fun n ↦ (((X (n + 1) ω) / (n + 1 : ℝ)) : EReal)) atTop = 0 := by
  have _ : P Set.univ = 1 := by
    simp
  have hX_pairwise : Pairwise fun i j ↦ X (i + 1) ⟂ᵢ[P] X (j + 1) := by
    -- Proof comment: pairwise independence is the pairwise shadow of the `IsIID` hypothesis.
    intro i j hij
    exact hX_iid.iIndepFun.indepFun hij
  have hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P := by
    -- Proof comment: every shifted coordinate has the same law as `X 1`.
    intro n
    simpa using hX_iid.identDistrib n 0
  have havg :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n) atTop (𝓝 P[X 1]) := by
    -- Proof comment: the strong law gives the almost-sure limit of the shifted empirical means.
    simpa using
      ProbabilityTheory.strong_law_ae_real (fun n ↦ X (n + 1)) hX1_integrable hX_pairwise hX_ident
  have hreal :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ X (n + 1) ω / (n + 1 : ℝ)) atTop (𝓝 0) := by
    -- Proof comment: pointwise on the strong-law event, convert average convergence to term
    -- convergence by the deterministic identity above.
    filter_upwards [havg] with ω hω
    exact normalizedTerm_tendsto_zero_of_average_tendsto (u := fun n ↦ X n ω) hω
  have hereal :
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (((X (n + 1) ω) / (n + 1 : ℝ)) : EReal)) atTop (𝓝 0) := by
    -- Proof comment: coercion from `ℝ` to `EReal` preserves the limit.
    filter_upwards [hreal] with ω hω
    simpa using (EReal.tendsto_coe.2 hω)
  filter_upwards [hereal] with ω hω
  simpa using hω.limsup_eq

omit hX_iid

/-- Helper for Exercise 5.1.3: the shifted i.i.d. family admits measurable representatives while
preserving the i.i.d. structure. -/
lemma measurableShiftedIidVersion
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P) :
    ∃ Y : ℕ → Ω → ℝ, (∀ n, Measurable (Y n)) ∧ (∀ n, Y n =ᵐ[P] X (n + 1)) ∧ IsIID Y P := by
  let Y : ℕ → Ω → ℝ := fun n ↦ (hX_iid.identDistrib n 0).aemeasurable_fst.mk (X (n + 1))
  have hY_meas : ∀ n, Measurable (Y n) := by
    -- Proof comment: each coordinate is replaced by its canonical measurable representative.
    intro n
    exact ((hX_iid.identDistrib n 0).aemeasurable_fst).measurable_mk
  have hY_ae : ∀ n, Y n =ᵐ[P] X (n + 1) := by
    -- Proof comment: the measurable representative agrees almost everywhere with the source
    -- coordinate.
    intro n
    exact ((hX_iid.identDistrib n 0).aemeasurable_fst).ae_eq_mk.symm
  have hY_indep : iIndepFun Y P := by
    -- Proof comment: coordinatewise almost-everywhere equality preserves independence.
    exact hX_iid.iIndepFun.congr (fun n ↦ (hY_ae n).symm)
  have hY_ident : ∀ i j, IdentDistrib (Y i) (Y j) P P := by
    -- Proof comment: compare both measurable representatives back to their original shifted
    -- coordinates and compose the distribution equalities.
    intro i j
    have hXi : IdentDistrib (X (i + 1)) (Y i) P P :=
      ((hX_iid.identDistrib i 0).aemeasurable_fst).identDistrib_mk
    have hXj : IdentDistrib (X (j + 1)) (Y j) P P :=
      ((hX_iid.identDistrib j 0).aemeasurable_fst).identDistrib_mk
    exact hXi.symm.trans ((hX_iid.identDistrib i j).trans hXj)
  exact ⟨Y, hY_meas, hY_ae, ⟨hY_indep, hY_ident⟩⟩

/-- Helper for Exercise 5.1.3: the limsup of measurable sets indexed by `ℕ` is measurable. -/
lemma measurableSet_limsup_nat {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet (s n)) :
    MeasurableSet (limsup s atTop) := by
  -- Proof comment: along `ℕ`, `limsup` is a countable intersection of countable unions.
  rw [limsup_eq_iInf_iSup_of_nat]
  exact MeasurableSet.iInter fun n ↦ MeasurableSet.iUnion fun m ↦
    MeasurableSet.iUnion fun _ ↦ hs m

/-- Helper for Exercise 5.1.3: in a probability space, a measurable set of measure `1` holds
almost surely. -/
lemma ae_mem_of_measure_eq_one
    (P : Measure Ω) [IsProbabilityMeasure P] {s : Set Ω}
    (hs : MeasurableSet s) (hP : P s = 1) :
    ∀ᵐ ω ∂P, ω ∈ s := by
  -- Proof comment: rewrite the almost-everywhere statement as vanishing measure of the
  -- complement.
  rw [ae_iff]
  have hcompl : P sᶜ = 0 := by
    rw [measure_compl hs (measure_ne_top P _), hP, measure_univ]
    simp
  simpa [Set.setOf_mem_eq] using hcompl

/-- Helper for Exercise 5.1.3: nonnegativity transfers across identical distribution. -/
lemma ae_nonneg_of_identDistrib
    (P : Measure Ω) [IsProbabilityMeasure P] {Y Z : Ω → ℝ}
    (hY_meas : Measurable Y) (hident : IdentDistrib Y Z P P) (hZ_nonneg : 0 ≤ᵐ[P] Z) :
    0 ≤ᵐ[P] Y := by
  -- Proof comment: it suffices to show that the negative set of `Y` has measure zero.
  have hZ_not_neg : ∀ᵐ ω ∂P, ¬ Z ω < 0 := by
    filter_upwards [hZ_nonneg] with ω hω
    exact not_lt_of_ge hω
  have hZ_neg : P {ω | Z ω < 0} = 0 := by
    rw [ae_iff] at hZ_not_neg
    simpa using hZ_not_neg
  have hYZ : P {ω | Y ω < 0} = P {ω | Z ω < 0} := by
    have _ := hY_meas
    simpa [Set.mem_Iio] using hident.measure_mem_eq measurableSet_Iio
  have hY_neg : P {ω | Y ω < 0} = 0 := hYZ.trans hZ_neg
  have hY_not_neg : ∀ᵐ ω ∂P, ¬ Y ω < 0 := by
    simpa [ae_iff] using hY_neg
  filter_upwards [hY_not_neg] with ω hω
  exact le_of_not_gt hω

/-- Helper for Exercise 5.1.3: after scaling by a fixed positive integer level, the second
Borel-Cantelli lemma forces the corresponding absolute tail events to occur infinitely often almost
surely. -/
lemma scaledAbsTailEvents_ae_mem_limsup_of_notIntegrable
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (m : ℕ)
    (hY_meas : ∀ n, Measurable (Y n)) (hY_iid : IsIID Y P)
    (hY0_not_integrable : ¬ Integrable (Y 0) P) :
    ∀ᵐ ω ∂P,
      ω ∈ limsup (fun n ↦ {ω | ((n + 1 : ℕ) : ℝ) < |Y n ω / (m + 1 : ℝ)|}) atTop := by
  let c : ℝ := m + 1
  let W : ℕ → Ω → ℝ := fun n ω ↦ Y n ω / c
  let B : ℕ → Set Ω := fun n ↦ {ω | ((n + 1 : ℕ) : ℝ) < |W n ω|}
  have hc : 0 < c := by
    -- Proof comment: the scaling constant is the positive level `m + 1`.
    positivity
  have hW_meas : ∀ n, Measurable (W n) := by
    -- Proof comment: dividing each coordinate by a fixed scalar preserves measurability.
    intro n
    simpa [W, c] using (hY_meas n).div_const c
  have hW_iid : IsIID W P := by
    refine ⟨?_, ?_⟩
    · -- Proof comment: independence is preserved under coordinatewise composition by the same
      -- measurable map.
      refine hY_iid.iIndepFun.comp (fun _ x ↦ x / c) ?_
      intro n
      exact measurable_id.div_const c
    · -- Proof comment: identical distribution is preserved under the same scalar division.
      intro i j
      simpa [W, c] using (hY_iid.identDistrib i j).div_const c
  have hW0_not_integrable : ¬ Integrable (W 0) P := by
    -- Proof comment: integrability of the scaled variable would imply integrability of `Y 0`
    -- after multiplying back by `c`.
    intro hW0_integrable
    have hW_mul_eq : (fun ω ↦ W 0 ω * c) = Y 0 := by
      funext ω
      dsimp [W]
      field_simp [hc.ne']
    have hY0_integrable : Integrable (Y 0) P := by
      simpa [hW_mul_eq] using hW0_integrable.mul_const c
    exact hY0_not_integrable hY0_integrable
  have hB_meas : ∀ n, MeasurableSet (B n) := by
    -- Proof comment: each tail event is the preimage of a strict upper ray under `|W n|`.
    intro n
    change MeasurableSet ((fun ω ↦ |W n ω|) ⁻¹' Set.Ioi (((n + 1 : ℕ) : ℝ)))
    simpa using (hW_meas n).norm measurableSet_Ioi
  have hB_indep : iIndepSet B P := by
    -- Proof comment: the large-jump events for the scaled i.i.d. family remain independent.
    simpa [B, W] using largeJumpEvents_iIndepSet P W hW_meas hW_iid
  have hB_tsum : (∑' n : ℕ, P (B n)) = ⊤ := by
    -- Proof comment: nonintegrability forces divergence of the large-jump probability series.
    simpa [B, W] using notIntegrable_imp_largeJumpSeries_eq_top P W hW_meas hW_iid
      hW0_not_integrable
  have hB_limsup_one : P (limsup B atTop) = 1 := by
    -- Proof comment: apply the second Borel-Cantelli lemma to the independent tail events.
    simpa using ProbabilityTheory.measure_limsup_eq_one (μ := P) (s := B) hB_meas hB_indep hB_tsum
  exact ae_mem_of_measure_eq_one P (measurableSet_limsup_nat hB_meas) hB_limsup_one

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 5.1.3: membership in the scaled absolute-tail limsup yields a frequent
lower bound for the normalized sequence once the path is nonnegative. -/
lemma frequently_ge_normalized_of_mem_scaledAbsTailLimsup
    {Y : ℕ → Ω → ℝ} {ω : Ω} {m : ℕ}
    (hnonneg : ∀ n, 0 ≤ Y n ω)
    (hω : ω ∈ limsup (fun n ↦ {ω | ((n + 1 : ℕ) : ℝ) < |Y n ω / (m + 1 : ℝ)|}) atTop) :
    ∃ᶠ n in atTop, ((((m + 1 : ℕ) : ℝ) : EReal)) ≤ (((Y n ω) / (n + 1 : ℝ)) : EReal) := by
  rw [mem_limsup_iff_frequently_mem] at hω
  refine hω.mono ?_
  intro n hn
  have hm_pos : 0 < (m + 1 : ℝ) := by positivity
  have hn_pos : 0 < (n + 1 : ℝ) := by positivity
  have hy_nonneg : 0 ≤ Y n ω / (m + 1 : ℝ) := by
    exact div_nonneg (hnonneg n) hm_pos.le
  have hn' : (n + 1 : ℝ) < Y n ω / (m + 1 : ℝ) := by
    simpa [abs_of_nonneg hy_nonneg] using hn
  have hscaled' : (n + 1 : ℝ) * (m + 1 : ℝ) < Y n ω := by
    exact (lt_div_iff₀ hm_pos).1 hn'
  have hscaled : (m + 1 : ℝ) * (n + 1 : ℝ) < Y n ω := by
    simpa [mul_comm] using hscaled'
  have hreal : (m + 1 : ℝ) < Y n ω / (n + 1 : ℝ) := by
    exact (lt_div_iff₀ hn_pos).2 hscaled
  have hEReal :
      ((((m + 1 : ℕ) : ℝ) : EReal)) <
        ((((Y n ω) / (n + 1 : ℝ) : ℝ) : EReal)) := by
    exact_mod_cast hreal
  have hEReal' :
      ((((m + 1 : ℕ) : ℝ) : EReal)) < (((Y n ω) / (n + 1 : ℝ)) : EReal) := by
    simpa using hEReal
  exact le_of_lt hEReal'

/-- Helper for Exercise 5.1.3: frequent lower bounds by every positive integer level force the
`EReal` limsup to be `⊤`. -/
lemma ereal_limsup_eq_top_of_forall_nat_frequently_ge
    {u : ℕ → EReal}
    (hu : ∀ m : ℕ, ∃ᶠ n in atTop, ((((m + 1 : ℕ) : ℝ) : EReal)) ≤ u n) :
    limsup u atTop = ⊤ := by
  -- Proof comment: every real number lies below some integer level, and that level is below the
  -- limsup by the frequent-lower-bound hypothesis.
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  rcases exists_nat_gt y with ⟨m, hm⟩
  have hm_succ : (m : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self m
  have hm' : y < ((m + 1 : ℕ) : ℝ) := by
    exact lt_trans hm hm_succ
  have hlim : ((((m + 1 : ℕ) : ℝ) : EReal)) ≤ limsup u atTop :=
    le_limsup_of_frequently_le (hu m)
  exact lt_of_lt_of_le (by exact_mod_cast hm') hlim

-- Proof sketch: replace the shifted i.i.d. sequence by measurable representatives, apply the
-- large-jump/Borel-Cantelli machinery from Exercise 5.3.2 to every scaled family
-- `n ↦ Y n / (m + 1)`, and then convert the resulting frequent lower bounds for all integer
-- levels into the statement that the `EReal` limsup is `⊤`.
include hX_iid
/-- Exercise 5.1.3 (2): For i.i.d. nonnegative real random variables with infinite nonnegative
expectation, it is enough to assume the source-facing condition `0 ≤ᵐ[P] X 1`, since the
chapter's canonical i.i.d. abstraction `IsIID (fun n ↦ X (n + 1)) P` propagates this to every
coordinate. Then the normalized sequence `Xₙ / n`, represented in Lean by the terms
`X 1 / 1, X 2 / 2, …`, has almost-sure limsup `⊤`. -/
theorem ae_limsup_normalized_iid_nonnegative_eq_top_of_not_integrable
    (hX1_nonneg : 0 ≤ᵐ[P] X 1) (hX1_not_integrable : ¬ Integrable (X 1) P) :
    ∀ᵐ ω ∂P, limsup (fun n ↦ (((X (n + 1) ω) / (n + 1 : ℝ)) : EReal)) atTop = ⊤ := by
  rcases measurableShiftedIidVersion (P := P) (X := X) hX_iid with ⟨Y, hY_meas, hY_ae, hY_iid⟩
  have hY0_nonneg : 0 ≤ᵐ[P] Y 0 := by
    -- Proof comment: the measurable representative of `X 1` preserves the source-facing
    -- nonnegativity assumption.
    filter_upwards [hX1_nonneg, hY_ae 0] with ω hω hEq
    simpa [hEq] using hω
  have hY_nonneg : ∀ n, 0 ≤ᵐ[P] Y n := by
    -- Proof comment: identical distribution transfers the almost-sure nonnegativity of `Y 0` to
    -- every coordinate.
    intro n
    exact ae_nonneg_of_identDistrib P (hY_meas n) (hY_iid.identDistrib n 0) hY0_nonneg
  have hY0_not_integrable : ¬ Integrable (Y 0) P := by
    -- Proof comment: integrability of the measurable representative would transfer back to `X 1`.
    intro hY0_integrable
    exact hX1_not_integrable (hY0_integrable.congr (hY_ae 0))
  have hscaled_all :
      ∀ᵐ ω ∂P, ∀ m : ℕ,
        ω ∈ limsup (fun n ↦ {ω | ((n + 1 : ℕ) : ℝ) < |Y n ω / (m + 1 : ℝ)|}) atTop := by
    -- Proof comment: for each fixed level `m + 1`, the large-jump series diverges and
    -- Borel-Cantelli yields infinitely many exceedances almost surely.
    rw [ae_all_iff]
    intro m
    exact scaledAbsTailEvents_ae_mem_limsup_of_notIntegrable P Y m hY_meas hY_iid
      hY0_not_integrable
  have hY_all : ∀ᵐ ω ∂P, ∀ n : ℕ, Y n ω = X (n + 1) ω := by
    -- Proof comment: package the coordinatewise measurable-replacement equalities into one
    -- full-measure event.
    exact ae_all_iff.2 hY_ae
  have hY_nonneg_all : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 ≤ Y n ω := by
    -- Proof comment: package the coordinatewise nonnegativity statements into one full-measure
    -- event as well.
    exact ae_all_iff.2 hY_nonneg
  filter_upwards [hscaled_all, hY_all, hY_nonneg_all] with ω hω hEq hnonneg
  have hY_top :
      limsup (fun n ↦ (((Y n ω) / (n + 1 : ℝ)) : EReal)) atTop = ⊤ := by
    -- Proof comment: every positive integer level is attained frequently by the normalized path.
    refine ereal_limsup_eq_top_of_forall_nat_frequently_ge ?_
    intro m
    exact frequently_ge_normalized_of_mem_scaledAbsTailLimsup hnonneg (hω m)
  have hseq_eq :
      (fun n ↦ (((X (n + 1) ω) / (n + 1 : ℝ)) : EReal)) =
        fun n ↦ (((Y n ω) / (n + 1 : ℝ)) : EReal) := by
    -- Proof comment: after the probabilistic argument is complete, rewrite the measurable
    -- representatives back to the original coordinates.
    funext n
    rw [← hEq n]
  calc
    limsup (fun n ↦ (((X (n + 1) ω) / (n + 1 : ℝ)) : EReal)) atTop
        = limsup (fun n ↦ (((Y n ω) / (n + 1 : ℝ)) : EReal)) atTop := by
            exact congrArg (fun f ↦ limsup f atTop) hseq_eq
    _ = ⊤ := hY_top

omit hX_iid
