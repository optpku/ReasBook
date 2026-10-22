/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Moments.Variance
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_1_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Exercise_7_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_39
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_43

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

/- Theorem 15.50 is `source-facing`: it states Kolmogorov's three-series criterion for the
textbook truncations `Yₙ = Xₙ 𝟙_{|Xₙ| ≤ K}`. The primitive data are just the shifted sequence
`X₁, X₂, …`, the cutoff `K`, and the indicator-cutoff random variables themselves. There is no
upstream owner declaration for the whole three-condition package in this chapter or in mathlib, so
the public API is kept as the direct conjunction of the source-faithful three-series clauses
instead of a parallel wrapper class. For the large-jump condition, the canonical owner abstraction
is the real probability mass `P.real A`; using `Summable` directly on `P A : ℝ≥0∞` would be
vacuous. The source only asks for ordered convergence of the partial sums of `∑ Xₙ` and
`∑ E[Yₙ]`, not unconditional `Summable` over arbitrary finite subsets. -/

-- Proof sketch: for the forward implication, use Borel--Cantelli for the large-jump events, then
-- combine almost-sure convergence of the truncated centered series with convergence of the series
-- of expectations. For the reverse implication, deduce the tail-probability summability from
-- almost-sure convergence, then apply the centered-series criterion to the truncated variables and
-- recover convergence of the expectation series from the deterministic part of the partial sums.
/-- Helper for Theorem 15.50: summable real-valued event probabilities imply almost-sure eventual
avoidance of those events by the first Borel--Cantelli lemma. -/
private lemma ae_eventually_notMem_of_summable_measureReal
    (P : Measure Ω) [IsProbabilityMeasure P] {s : ℕ → Set Ω}
    (hs : Summable (fun n : ℕ ↦ (P (s n)).toReal)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ s n := by
  have htsum : (∑' n, P (s n)) ≠ ⊤ := by
    -- Proof comment: summability of the real masses lifts to finiteness of the ENNReal series.
    simpa [ENNReal.ofReal_toReal, measure_ne_top] using hs.tsum_ofReal_ne_top
  exact MeasureTheory.ae_eventually_notMem htsum

/-- Helper for Theorem 15.50: the textbook truncation `Xₙ 𝟙_{|Xₙ| ≤ K}` written in the shifted
`n + 1` indexing convention used by this chapter. -/
private def threeSeriesTruncation (K : ℝ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω ↦ Set.indicator {ω | |X (n + 1) ω| ≤ K} (X (n + 1)) ω

/-- Helper for Theorem 15.50: replacing a real series by an eventually equal one only changes the
limit of its partial sums by a fixed prefix correction. -/
private lemma exists_tendsto_sum_range_of_eventuallyEq
    {x y : ℕ → ℝ} (hxy : ∀ᶠ n in atTop, x n = y n)
    (hy : ∃ s : ℝ,
      Tendsto (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ y k) atTop (𝓝 s)) :
    ∃ s : ℝ,
      Tendsto (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ x k) atTop (𝓝 s) := by
  rcases Filter.eventually_atTop.1 hxy with ⟨N, hN⟩
  rcases hy with ⟨s, hs⟩
  let c : ℝ :=
    Finset.sum (Finset.range N) (fun k ↦ x k) -
      Finset.sum (Finset.range N) (fun k ↦ y k)
  have hsum_eq :
      ∀ᶠ n in atTop,
        Finset.sum (Finset.range n) (fun k ↦ x k) =
          c + Finset.sum (Finset.range n) (fun k ↦ y k) := by
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hxsplit := Finset.sum_range_add_sum_Ico x hn
    have hysplit := Finset.sum_range_add_sum_Ico y hn
    have htail :
        Finset.sum (Finset.Ico N n) (fun k ↦ x k) =
          Finset.sum (Finset.Ico N n) (fun k ↦ y k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact hN k (Finset.mem_Ico.mp hk).1
    -- Proof comment: after index `N`, the two tails agree termwise, so only the prefix differs.
    calc
      Finset.sum (Finset.range n) (fun k ↦ x k)
          = Finset.sum (Finset.range N) (fun k ↦ x k) +
              Finset.sum (Finset.Ico N n) (fun k ↦ x k) := hxsplit.symm
      _ = Finset.sum (Finset.range N) (fun k ↦ x k) +
            Finset.sum (Finset.Ico N n) (fun k ↦ y k) := by rw [htail]
      _ = c + Finset.sum (Finset.range n) (fun k ↦ y k) := by
            rw [hysplit.symm]
            dsimp [c]
            ring
  refine ⟨c + s, ?_⟩
  have hconst :
      Tendsto
        (fun n : ℕ ↦ c + Finset.sum (Finset.range n) (fun k ↦ y k))
        atTop (𝓝 (c + s)) :=
    tendsto_const_nhds.add hs
  exact (tendsto_congr' hsum_eq).2 hconst

/-- Helper for Theorem 15.50: if the shifted partial sums converge, then the shifted summands tend
to `0`. -/
private lemma tendsto_zero_of_tendsto_sum_range
    {x : ℕ → ℝ} {s : ℝ}
    (hs :
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ x (k + 1))
        atTop (𝓝 s)) :
    Tendsto (fun n : ℕ ↦ x (n + 1)) atTop (𝓝 0) := by
  have hshift :
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range (n + 1)) fun k ↦ x (k + 1))
        atTop (𝓝 s) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hs
  have hsub :
      Tendsto
        (fun n : ℕ ↦
          Finset.sum (Finset.range (n + 1)) (fun k ↦ x (k + 1)) -
            Finset.sum (Finset.range n) (fun k ↦ x (k + 1)))
        atTop (𝓝 (s - s)) :=
    hshift.sub hs
  have hsum_eq :
      (fun n : ℕ ↦
        Finset.sum (Finset.range (n + 1)) (fun k ↦ x (k + 1)) -
          Finset.sum (Finset.range n) (fun k ↦ x (k + 1))) =
        fun n ↦ x (n + 1) := by
    funext n
    rw [Finset.sum_range_succ_sub_sum]
  -- Proof comment: consecutive partial sums differ by exactly the new summand.
  simpa [hsum_eq] using hsub

/-- Helper for Theorem 15.50: if the large-jump probabilities are not summable, then the large-jump
events occur infinitely often on an almost-sure set by the second Borel--Cantelli lemma. -/
private lemma ae_mem_largeJumpLimsup_of_not_summable_measureReal
    (P : Measure Ω) [IsProbabilityMeasure P] {E : ℕ → Set Ω}
    (hE_meas : ∀ n, MeasurableSet (E n)) (hE_indep : iIndepSet E P)
    (hE_notSummable : ¬ Summable (fun n : ℕ ↦ P.real (E n))) :
    ∀ᵐ ω ∂P, ω ∈ Filter.limsup E atTop := by
  have hE_tsum : (∑' n : ℕ, P (E n)) = ⊤ := by
    apply not_not.mp
    intro hE_tsum
    -- Proof comment: a finite ENNReal series would make the real masses summable,
    -- contradicting the assumed failure of condition (i).
    exact hE_notSummable <| by
      simpa [Measure.real_def] using (ENNReal.summable_toReal hE_tsum)
  have hLimsup_one : P (Filter.limsup E atTop) = 1 := by
    simpa using
      ProbabilityTheory.measure_limsup_eq_one (μ := P) (s := E) hE_meas hE_indep hE_tsum
  have hLimsup_meas : MeasurableSet (Filter.limsup E atTop) := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun n =>
      MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hE_meas m
  rw [ae_iff]
  have hcompl : P ((Filter.limsup E atTop)ᶜ) = 0 := by
    rw [measure_compl hLimsup_meas (measure_ne_top P _), hLimsup_one, measure_univ]
    simp
  simpa [Set.setOf_mem_eq] using hcompl

/-- Helper for Theorem 15.50: any real sequence converging to `0` is eventually inside the
interval `(-K, K)` for every `K > 0`. -/
private lemma eventually_abs_lt_of_tendsto_zero
    {x : ℕ → ℝ} (K : ℝ) (hK : 0 < K)
    (hx : Tendsto x atTop (𝓝 0)) :
    ∀ᶠ n in atTop, |x n| < K := by
  rcases Metric.tendsto_atTop.1 hx K hK with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  -- Proof comment: in the real metric, `dist (xₙ, 0) < K` is exactly the estimate `|xₙ| < K`.
  simpa [Real.dist_eq] using hN n hn

/-- Helper for Theorem 15.50: along a sample path where the shifted partial sums converge, the
shifted summands are eventually bounded by the truncation threshold `K`. -/
private lemma eventually_abs_lt_of_tendsto_sum_range
    (K : ℝ) (hK : 0 < K) (X : ℕ → Ω → ℝ) {ω : Ω}
    (hω :
      ∃ s : ℝ,
        Tendsto
          (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ X (k + 1) ω)
          atTop (𝓝 s)) :
    ∀ᶠ n in atTop, |X (n + 1) ω| < K := by
  rcases hω with ⟨s, hs⟩
  let x : ℕ → ℝ := fun n ↦ X n ω
  have hs' :
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ x (k + 1))
        atTop (𝓝 s) := by
    -- Proof comment: freeze the shifted summand spelling before applying the generic summand-to-zero
    -- lemma, so later rewrites stay in a single normal form.
    simpa [x] using hs
  have hZero : Tendsto (fun n : ℕ ↦ x (n + 1)) atTop (𝓝 0) :=
    tendsto_zero_of_tendsto_sum_range hs'
  -- Route correction: first prove the generic `xₙ → 0` to `|xₙ| < K` bridge, then spend a fresh
  -- heartbeat budget instantiating it with the shifted summand sequence.
  simpa [x] using eventually_abs_lt_of_tendsto_zero K hK hZero

/-- Helper for Theorem 15.50: almost-sure convergence of the shifted partial sums forces the
large-jump probabilities at level `K` to be summable. -/
private lemma tailProbSummable_of_ae_tendsto_sum_range
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℝ) (hK : 0 < K) (X : ℕ → Ω → ℝ)
    (hX_measurable : ∀ n, Measurable (X (n + 1)))
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ae :
      ∀ᵐ ω ∂P, ∃ s : ℝ,
        Tendsto
          (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ X (k + 1) ω)
          atTop (𝓝 s)) :
    Summable (fun n : ℕ ↦ P.real {ω | K < |X (n + 1) ω|}) := by
  let E : ℕ → Set Ω := fun n ↦ {ω | K < |X (n + 1) ω|}
  have hE_meas : ∀ n, MeasurableSet (E n) := by
    intro n
    simpa [E, Set.setOf_mem_eq] using measurableSet_lt measurable_const (hX_measurable n).abs
  have hE_indep : iIndepSet E P := by
    -- Proof comment: the large-jump events are measurable coordinatewise threshold preimages of
    -- the independent coordinates.
    simpa [E] using
      iIndepSet_preimage_of_iIndepFun (μ := P) (Y := fun n ↦ X (n + 1))
        hX_measurable hX_indep (s := fun _ ↦ {x : ℝ | K < |x|})
        (fun _ ↦ measurableSet_lt measurable_const measurable_abs)
  by_contra hTail
  have hMem :
      ∀ᵐ ω ∂P, ω ∈ Filter.limsup E atTop :=
    ae_mem_largeJumpLimsup_of_not_summable_measureReal P hE_meas hE_indep hTail
  have hNotMem :
      ∀ᵐ ω ∂P, ω ∉ Filter.limsup E atTop := by
    filter_upwards [hX_ae] with ω hω
    -- Proof comment: pathwise convergence makes the large-jump event eventually false, so the
    -- sample point cannot lie in the limsup event.
    have hEventually_lt := eventually_abs_lt_of_tendsto_sum_range K hK X hω
    have hEventually_notMem :
        ∀ᶠ n in atTop, ¬ ω ∈ E n := by
      filter_upwards [hEventually_lt] with n hn
      simpa [E, Set.mem_setOf_eq] using not_lt_of_ge hn.le
    simpa [Filter.mem_limsup_iff_frequently_mem] using
      (Filter.not_frequently.2 hEventually_notMem)
  have hFalse : ∀ᵐ ω ∂P, False := by
    filter_upwards [hMem, hNotMem] with ω hω_mem hω_notMem
    exact hω_notMem hω_mem
  have hNotFalse : ¬ ∀ᵐ ω ∂P, False := by
    rw [ae_iff]
    simpa [IsProbabilityMeasure.measure_univ]
  exact hNotFalse hFalse

/-- Helper for Theorem 15.50: summable large-jump probabilities make the truncation agree with
the original sequence eventually almost surely. -/
private lemma ae_eventually_truncation_eq_original_of_tailProbSummable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℝ) (X : ℕ → Ω → ℝ)
    (hTail : Summable (fun n : ℕ ↦ P.real {ω | K < |X (n + 1) ω|})) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      threeSeriesTruncation K X n ω = X (n + 1) ω := by
  have hAvoid :
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ {ω | K < |X (n + 1) ω|} :=
    ae_eventually_notMem_of_summable_measureReal (P := P)
      (s := fun n ↦ {ω | K < |X (n + 1) ω|}) <| by
        simpa [Measure.real_def] using hTail
  filter_upwards [hAvoid] with ω hω
  filter_upwards [hω] with n hn
  have hle : |X (n + 1) ω| ≤ K := not_lt.mp hn
  -- Proof comment: once the tail event fails, the truncation is definitionally the original term.
  simpa [threeSeriesTruncation, Set.indicator, hle]

/-- Helper for Theorem 15.50: an independent uniformly bounded real sequence has almost-surely
convergent centered partial sums once its variances are summable. -/
private lemma ae_tendsto_centeredPartialSums_of_varianceSummable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y P)
    (hY_bound : ∀ n ω, |Y n ω| ≤ B)
    (hVar : Summable (fun n : ℕ ↦ Var[Y n; P])) :
    ∀ᵐ ω ∂P, ∃ s : ℝ,
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ (Y k ω - P[Y k]))
        atTop (𝓝 s) := by
  let Z : ℕ → Ω → ℝ := fun n ω ↦ Y n ω - P[Y n]
  have hY_memLp : ∀ n, MemLp (Y n) 2 P := by
    intro n
    -- Proof comment: the finite probability measure turns the uniform bound into an `L²` bound.
    refine MemLp.of_bound (p := (2 : ENNReal)) (hY_meas n).aestronglyMeasurable |B| ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [Real.norm_eq_abs] using le_trans (hY_bound n ω) (le_abs_self B)
  have hZ_memLp : ∀ n, MemLp (Z n) 2 P := by
    intro n
    -- Proof comment: subtracting the deterministic mean preserves `L²` membership.
    exact (hY_memLp n).sub (memLp_const (P[Y n]))
  have hZ_centered : ∀ n, P[Z n] = 0 := by
    intro n
    have hY_int : Integrable (Y n) P := (hY_memLp n).integrable one_le_two
    -- Proof comment: the centered variable is `Yₙ - E[Yₙ]`, so its expectation vanishes.
    change ∫ ω, (Y n ω - P[Y n]) ∂P = 0
    rw [integral_sub hY_int (integrable_const _)]
    simp
  have hZ_indep : iIndepFun Z P := by
    -- Proof comment: centering each coordinate is a measurable coordinatewise transform.
    simpa [Z, sub_eq_add_neg] using
      hY_indep.comp (fun n x ↦ x - P[Y n]) (fun _ ↦ measurable_id.sub measurable_const)
  have hZ_var : Summable (fun n : ℕ ↦ Var[Z n; P]) := by
    -- Proof comment: translating by a constant does not change variance.
    refine hVar.congr ?_
    intro n
    symm
    simpa [Z] using
      ProbabilityTheory.variance_sub_const
        (μ := P) (X := Y n) ((hY_meas n).aestronglyMeasurable) (P[Y n])
  rcases hasAETendstoPartialSums_of_iIndepFun_summable_variance P Z hZ_indep hZ_memLp
      hZ_centered hZ_var with ⟨Zlim, _, hZlim⟩
  filter_upwards [hZlim] with ω hω
  -- Proof comment: the Chapter 7 theorem already returns convergence of the centered partial sums.
  have hω' :
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ Z k ω)
        atTop (𝓝 (Zlim ω)) := by
    simpa [partialSum] using hω
  exact ⟨Zlim ω, by simpa [Z, Finset.sum_sub_distrib] using hω'⟩

/-- Helper for Theorem 15.50: an independent uniformly bounded real sequence has almost-surely
convergent partial sums once its expectation partial sums converge and its variances are summable. -/
private lemma ae_tendsto_partialSums_of_expectationTendsto_and_varianceSummable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y P)
    (hY_bound : ∀ n ω, |Y n ω| ≤ B)
    (hExp :
      ∃ s : ℝ,
        Tendsto
          (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ P[Y k])
          atTop (𝓝 s))
    (hVar : Summable (fun n : ℕ ↦ Var[Y n; P])) :
    ∀ᵐ ω ∂P, ∃ s : ℝ,
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ Y k ω)
        atTop (𝓝 s) := by
  rcases hExp with ⟨sExp, hsExp⟩
  have hCentered :
      ∀ᵐ ω ∂P, ∃ s : ℝ,
        Tendsto
          (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ (Y k ω - P[Y k]))
          atTop (𝓝 s) :=
    ae_tendsto_centeredPartialSums_of_varianceSummable P Y B hY_meas hY_indep hY_bound hVar
  filter_upwards [hCentered] with ω hω
  rcases hω with ⟨sCentered, hsCentered⟩
  refine ⟨sCentered + sExp, ?_⟩
  have hsum_eq :
      ∀ n : ℕ,
        Finset.sum (Finset.range n) (fun k ↦ Y k ω) =
          Finset.sum (Finset.range n) (fun k ↦ (Y k ω - P[Y k])) +
            Finset.sum (Finset.range n) (fun k ↦ P[Y k]) := by
    intro n
    -- Proof comment: decompose each partial sum into its centered part plus the mean correction.
    calc
      Finset.sum (Finset.range n) (fun k ↦ Y k ω)
          = Finset.sum (Finset.range n) (fun k ↦ (Y k ω - P[Y k]) + P[Y k]) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
      _ = Finset.sum (Finset.range n) (fun k ↦ (Y k ω - P[Y k])) +
            Finset.sum (Finset.range n) (fun k ↦ P[Y k]) := by
              rw [Finset.sum_add_distrib]
  have hsum_eventually :
      (fun n : ℕ ↦ Finset.sum (Finset.range n) (fun k ↦ Y k ω)) =ᶠ[atTop]
        fun n ↦
          Finset.sum (Finset.range n) (fun k ↦ (Y k ω - P[Y k])) +
            Finset.sum (Finset.range n) (fun k ↦ P[Y k]) :=
    Filter.Eventually.of_forall hsum_eq
  refine (tendsto_congr' hsum_eventually).2 ?_
  -- Proof comment: add the deterministic mean partial sums back to the centered convergence.
  exact hsCentered.add hsExp

/-- Helper for Theorem 15.50: if the variance series is not summable, then some variance term is
strictly positive. -/
private lemma exists_variance_pos_of_not_summable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ)
    (hVar_notSummable : ¬ Summable (fun n : ℕ ↦ Var[Y n; P])) :
    ∃ N0 : ℕ, 0 < Var[Y N0; P] := by
  by_contra hNone
  have hZero : ∀ n : ℕ, Var[Y n; P] = 0 := by
    intro n
    have hEq : ¬ 0 < Var[Y n; P] := by
      exact fun hpos ↦ hNone ⟨n, hpos⟩
    exact le_antisymm (le_of_not_gt hEq) (ProbabilityTheory.variance_nonneg (Y n) P)
  exact hVar_notSummable <| by
    simpa [hZero] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))

/-- Helper for Theorem 15.50: the canonical variance normalizer for the tail starting at `N₀`. -/
private def tailVarianceNormalizer
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (N0 : ℕ) : ℕ → ℝ :=
  fun n ↦ Real.sqrt (Finset.sum (Finset.range (n + 1)) fun k ↦ Var[Y (N0 + k); P])

/-- Helper for Theorem 15.50: once one tail variance is positive, every cumulative tail
normalizer is positive. -/
private lemma tailVarianceNormalizer_pos
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) {N0 : ℕ}
    (hVar0 : 0 < Var[Y N0; P]) :
    ∀ n : ℕ, 0 < tailVarianceNormalizer P Y N0 n := by
  intro n
  have hsum_pos :
      0 < Finset.sum (Finset.range (n + 1)) (fun k ↦ Var[Y (N0 + k); P]) := by
    have hterm_nonneg :
        ∀ k : ℕ, 0 ≤ Var[Y (N0 + k); P] := by
      intro k
      exact ProbabilityTheory.variance_nonneg (Y (N0 + k)) P
    have hle :
        Var[Y N0; P] ≤ Finset.sum (Finset.range (n + 1)) (fun k ↦ Var[Y (N0 + k); P]) := by
      have hmem : 0 ∈ Finset.range (n + 1) := by simp
      simpa using
        (Finset.single_le_sum
          (f := fun k : ℕ ↦ Var[Y (N0 + k); P])
          (s := Finset.range (n + 1))
          (fun k hk ↦ hterm_nonneg k) hmem)
    exact lt_of_lt_of_le hVar0 hle
  -- Proof comment: the square root preserves positivity on the cumulative positive variance sum.
  exact Real.sqrt_pos.2 hsum_pos

/-- Helper for Theorem 15.50: non-summability of the shifted tail variances makes the tail
normalizer tend to `+∞`. -/
private lemma tailVarianceNormalizer_tendsto_atTop
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (N0 : ℕ)
    (hTail_notSummable : ¬ Summable (fun n : ℕ ↦ Var[Y (N0 + n); P])) :
    Tendsto (tailVarianceNormalizer P Y N0) atTop atTop := by
  have hsum :
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ Var[Y (N0 + k); P])
        atTop atTop := by
    rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
    · exact hTail_notSummable
    · intro n
      exact ProbabilityTheory.variance_nonneg (Y (N0 + n)) P
  have hsum_shift :
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range (n + 1)) fun k ↦ Var[Y (N0 + k); P])
        atTop atTop := by
    exact hsum.comp (tendsto_add_atTop_nat 1)
  -- Proof comment: the normalizer is the square root of the divergent cumulative tail variance.
  simpa [tailVarianceNormalizer] using Real.tendsto_sqrt_atTop.comp hsum_shift

/-- Helper for Theorem 15.50: the expectation of a uniformly bounded real random variable is
bounded by the same absolute constant. -/
private lemma abs_expectation_le_absBound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ)
    (hY_bound : ∀ n ω, |Y n ω| ≤ B) :
    ∀ n : ℕ, |P[Y n]| ≤ |B| := by
  intro n
  have hbound :
      ∀ᵐ ω ∂P, ‖Y n ω‖ ≤ |B| := by
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    simpa [Real.norm_eq_abs] using le_trans (hY_bound n ω) (le_abs_self B)
  -- Proof comment: on a probability space, the integral norm is controlled by the uniform bound.
  calc
    |P[Y n]| = ‖∫ ω, Y n ω ∂P‖ := by simp [Real.norm_eq_abs]
    _ ≤ |B| * P.real Set.univ := by
          exact MeasureTheory.norm_integral_le_of_norm_le_const hbound
    _ = |B| := by simp [IsProbabilityMeasure.measure_univ]

/-- Helper for Theorem 15.50: after centering, the truncation entries are still uniformly bounded
by `2 * |B|`. -/
private lemma abs_centered_le_two_mul_absBound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ)
    (hY_bound : ∀ n ω, |Y n ω| ≤ B) :
    ∀ n ω, |Y n ω - P[Y n]| ≤ 2 * |B| := by
  intro n ω
  have hExp : |P[Y n]| ≤ |B| := abs_expectation_le_absBound P Y B hY_bound n
  -- Proof comment: the centered term splits into the sample value plus the deterministic mean.
  calc
    |Y n ω - P[Y n]| ≤ |Y n ω| + |P[Y n]| := by
          simpa [sub_eq_add_neg, abs_neg] using abs_add_le (Y n ω) (-P[Y n])
    _ ≤ |B| + |B| := by
          exact add_le_add
            (le_trans (hY_bound n ω) (le_abs_self B))
            hExp
    _ = 2 * |B| := by ring

/-- Helper for Theorem 15.50: the normalized centered tail entry is measurable in every row. -/
private lemma tailStandardizedCenteredArray_measurable_entry
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (N0 : ℕ)
    (hY_meas : ∀ n, Measurable (Y n))
    (n : ℕ) (i : Fin (n + 1)) :
    Measurable
      (fun ω ↦
        (tailVarianceNormalizer P Y N0 n)⁻¹ *
          (Y (N0 + i.1) ω - P[Y (N0 + i.1)])) := by
  -- Proof comment: each entry is a fixed scalar multiple of a measurable centered coordinate.
  simpa using ((hY_meas (N0 + i.1)).sub measurable_const).const_mul
    ((tailVarianceNormalizer P Y N0 n)⁻¹)

/-- Helper for Theorem 15.50: the centered normalized tail variables packaged as a triangular
array. -/
private def tailStandardizedCenteredArray
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (N0 : ℕ)
    (hY_meas : ∀ n, Measurable (Y n)) :
    RealRandomVariableArray Ω where
  rowLength n := n + 1
  entry n i ω :=
    (tailVarianceNormalizer P Y N0 n)⁻¹ * (Y (N0 + i.1) ω - P[Y (N0 + i.1)])
  measurable_entry n i := tailStandardizedCenteredArray_measurable_entry P Y N0 hY_meas n i

/-- Helper for Theorem 15.50: the `n`-th row sum of the standardized tail array is the normalized
centered tail partial sum. -/
private lemma tailStandardizedCenteredArray_rowSum_eq
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (N0 : ℕ)
    (hY_meas : ∀ n, Measurable (Y n))
    (n : ℕ) (ω : Ω) :
    (tailStandardizedCenteredArray P Y N0 hY_meas).rowSum n ω =
      (tailVarianceNormalizer P Y N0 n)⁻¹ *
        Finset.sum (Finset.range (n + 1)) (fun k ↦ Y (N0 + k) ω - P[Y (N0 + k)]) := by
  -- Proof comment: unfold the owner row sum and rewrite the `Fin (n + 1)` index as `range (n + 1)`.
  have hrow :
      (tailStandardizedCenteredArray P Y N0 hY_meas).rowSum n =
        fun ω' ↦
          ∑ i : Fin (n + 1),
            (tailVarianceNormalizer P Y N0 n)⁻¹ *
              (Y (N0 + i.1) ω' - P[Y (N0 + i.1)]) := by
    funext ω'
    rw [RealRandomVariableArray.rowSum]
    simp [tailStandardizedCenteredArray]
    rfl
  calc
    (tailStandardizedCenteredArray P Y N0 hY_meas).rowSum n ω
        = (∑ i : Fin (n + 1),
            (tailVarianceNormalizer P Y N0 n)⁻¹ *
              (Y (N0 + i.1) ω - P[Y (N0 + i.1)])) := by
            simpa using congrFun hrow ω
    _ = Finset.sum (Finset.range (n + 1)) (fun k ↦
          (tailVarianceNormalizer P Y N0 n)⁻¹ *
            (Y (N0 + k) ω - P[Y (N0 + k)])) := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun k : ℕ ↦
                (tailVarianceNormalizer P Y N0 n)⁻¹ *
                  (Y (N0 + k) ω - P[Y (N0 + k)]))
              (n + 1))
    _ = (tailVarianceNormalizer P Y N0 n)⁻¹ *
          Finset.sum (Finset.range (n + 1)) (fun k ↦ Y (N0 + k) ω - P[Y (N0 + k)]) := by
            symm
            rw [Finset.mul_sum]

/-- Helper for Theorem 15.50: each entry in the normalized centered tail array is bounded by the
rowwise scale `(tailVarianceNormalizer P Y N0 n)⁻¹ * (2 * |B|)`. -/
private lemma tailStandardizedCenteredArray_abs_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ) (N0 : ℕ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_bound : ∀ n ω, |Y n ω| ≤ B)
    (hVar0 : 0 < Var[Y N0; P])
    (n : ℕ) (i : Fin (n + 1)) (ω : Ω) :
    |tailStandardizedCenteredArray P Y N0 hY_meas n i ω| ≤
      (tailVarianceNormalizer P Y N0 n)⁻¹ * (2 * |B|) := by
  have hσ_pos : 0 < tailVarianceNormalizer P Y N0 n :=
    tailVarianceNormalizer_pos P Y hVar0 n
  have hcentered :
      |Y (N0 + i.1) ω - P[Y (N0 + i.1)]| ≤ 2 * |B| :=
    abs_centered_le_two_mul_absBound P Y B hY_bound (N0 + i.1) ω
  -- Proof comment: positivity of the row normalizer lets the absolute value pass through the scalar.
  calc
    |tailStandardizedCenteredArray P Y N0 hY_meas n i ω|
        = (tailVarianceNormalizer P Y N0 n)⁻¹ *
            |Y (N0 + i.1) ω - P[Y (N0 + i.1)]| := by
              simp [tailStandardizedCenteredArray, abs_of_pos, hσ_pos]
    _ ≤ (tailVarianceNormalizer P Y N0 n)⁻¹ * (2 * |B|) := by
          exact mul_le_mul_of_nonneg_left hcentered (by positivity)

/-- Helper for Theorem 15.50: every row of the standardized centered tail array is an independent
finite family. -/
private lemma tailStandardizedCenteredArray_isIndependent
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (N0 : ℕ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y P) :
    (tailStandardizedCenteredArray P Y N0 hY_meas).IsIndependent P := by
  refine ⟨fun n ↦ ?_⟩
  have hshift_inj : Function.Injective (fun i : Fin (n + 1) ↦ N0 + i.1) := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel hij
  let hrow : iIndepFun (fun i : Fin (n + 1) ↦ Y (N0 + i.1)) P :=
    hY_indep.precomp hshift_inj
  let g : Fin (n + 1) → ℝ → ℝ :=
    fun i x ↦ (tailVarianceNormalizer P Y N0 n)⁻¹ * (x - P[Y (N0 + i.1)])
  have hg : ∀ i, Measurable (g i) := by
    intro i
    simpa [g] using (measurable_id.sub measurable_const).const_mul
      ((tailVarianceNormalizer P Y N0 n)⁻¹)
  -- Proof comment: row independence is preserved under measurable coordinatewise centering and scaling.
  simpa [tailStandardizedCenteredArray, g] using hrow.comp g hg

/-- Helper for Theorem 15.50: the standardized centered tail array is centered entrywise. -/
private lemma tailStandardizedCenteredArray_isCentered
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ) (N0 : ℕ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_bound : ∀ n ω, |Y n ω| ≤ B) :
    (tailStandardizedCenteredArray P Y N0 hY_meas).IsCentered P := by
  refine ⟨fun n i ↦ ?_⟩
  have hYi_memLp : MemLp (Y (N0 + i.1)) 2 P := by
    -- Proof comment: the finite probability measure turns the uniform bound into an `L²` bound.
    refine MemLp.of_bound
      (p := (2 : ENNReal))
      (hY_meas (N0 + i.1)).aestronglyMeasurable
      |B| ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [Real.norm_eq_abs] using
        le_trans (hY_bound (N0 + i.1) ω) (le_abs_self B)
  have hcentered_memLp :
      MemLp (fun ω ↦ Y (N0 + i.1) ω - P[Y (N0 + i.1)]) 2 P :=
    hYi_memLp.sub (memLp_const (P[Y (N0 + i.1)]))
  have hmean_zero :
      P[fun ω ↦ Y (N0 + i.1) ω - P[Y (N0 + i.1)]] = 0 := by
    have hYi_int : Integrable (Y (N0 + i.1)) P := hYi_memLp.integrable one_le_two
    -- Proof comment: subtracting the deterministic expectation centers the variable exactly.
    change ∫ ω, (Y (N0 + i.1) ω - P[Y (N0 + i.1)]) ∂P = 0
    rw [integral_sub hYi_int (integrable_const _)]
    simp
  refine ⟨?_, ?_⟩
  · simpa [tailStandardizedCenteredArray, div_eq_mul_inv] using
      hcentered_memLp.const_mul ((tailVarianceNormalizer P Y N0 n)⁻¹) |>.integrable one_le_two
  · -- Proof comment: a scalar multiple of a centered variable remains centered.
    change
      ∫ ω,
        (tailVarianceNormalizer P Y N0 n)⁻¹ *
          (Y (N0 + i.1) ω - P[Y (N0 + i.1)]) ∂P = 0
    rw [integral_const_mul]
    simp [hmean_zero]

/-- Helper for Theorem 15.50: the standardized centered tail array is normed rowwise. -/
private lemma tailStandardizedCenteredArray_isNormed
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ) (N0 : ℕ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_bound : ∀ n ω, |Y n ω| ≤ B)
    (hVar0 : 0 < Var[Y N0; P]) :
    (tailStandardizedCenteredArray P Y N0 hY_meas).IsNormed P := by
  refine ⟨?_, ?_⟩
  · intro n i
    have hYi_memLp : MemLp (Y (N0 + i.1)) 2 P := by
      -- Proof comment: the bounded tail coordinates stay square-integrable.
      refine MemLp.of_bound
        (p := (2 : ENNReal))
        (hY_meas (N0 + i.1)).aestronglyMeasurable
        |B| ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        simpa [Real.norm_eq_abs] using
          le_trans (hY_bound (N0 + i.1) ω) (le_abs_self B)
    have hcentered_memLp :
        MemLp (fun ω ↦ Y (N0 + i.1) ω - P[Y (N0 + i.1)]) 2 P :=
      hYi_memLp.sub (memLp_const (P[Y (N0 + i.1)]))
    simpa [tailStandardizedCenteredArray, div_eq_mul_inv] using
      hcentered_memLp.const_mul ((tailVarianceNormalizer P Y N0 n)⁻¹)
  · intro n
    have hσ_pos : 0 < tailVarianceNormalizer P Y N0 n :=
      tailVarianceNormalizer_pos P Y hVar0 n
    have hσ_sq :
        (tailVarianceNormalizer P Y N0 n) ^ 2 =
          Finset.sum (Finset.range (n + 1)) (fun k ↦ Var[Y (N0 + k); P]) := by
      -- Proof comment: the normalizer squares back to the cumulative tail variance by definition.
      rw [tailVarianceNormalizer]
      rw [Real.sq_sqrt]
      exact Finset.sum_nonneg fun k hk ↦ ProbabilityTheory.variance_nonneg (Y (N0 + k)) P
    calc
      ∑ i : Fin ((tailStandardizedCenteredArray P Y N0 hY_meas).rowLength n),
          Var[tailStandardizedCenteredArray P Y N0 hY_meas n i; P]
        = ∑ i : Fin (n + 1),
            Var[Y (N0 + i.1); P] * (tailVarianceNormalizer P Y N0 n)⁻¹ ^ 2 := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              calc
                Var[tailStandardizedCenteredArray P Y N0 hY_meas n i; P]
                    = Var[fun ω ↦ (Y (N0 + i.1) ω - P[Y (N0 + i.1)]) *
                        (tailVarianceNormalizer P Y N0 n)⁻¹; P] := by
                          congr 1
                          funext ω
                          simp [tailStandardizedCenteredArray]
                          ring
                _ = Var[fun ω ↦ Y (N0 + i.1) ω - P[Y (N0 + i.1)]; P] *
                      (tailVarianceNormalizer P Y N0 n)⁻¹ ^ 2 := by
                        rw [variance_mul_const]
                _ = Var[Y (N0 + i.1); P] * (tailVarianceNormalizer P Y N0 n)⁻¹ ^ 2 := by
                      rw [variance_sub_const ((hY_meas (N0 + i.1)).aestronglyMeasurable)]
      _ = (∑ i : Fin (n + 1), Var[Y (N0 + i.1); P]) *
            (tailVarianceNormalizer P Y N0 n)⁻¹ ^ 2 := by
            rw [Finset.sum_mul]
      _ = 1 := by
            have hsum_fin :
                (∑ i : Fin (n + 1), Var[Y (N0 + i.1); P]) =
                  Finset.sum (Finset.range (n + 1)) (fun k ↦ Var[Y (N0 + k); P]) := by
              simpa using
                (Fin.sum_univ_eq_sum_range
                  (fun k : ℕ ↦ Var[Y (N0 + k); P])
                  (n + 1))
            have hσ_ne : tailVarianceNormalizer P Y N0 n ≠ 0 := ne_of_gt hσ_pos
            rw [hsum_fin, ← hσ_sq]
            field_simp [hσ_ne]

/-- Helper for Theorem 15.50: the bounded normalized centered tail array satisfies the Lindeberg
condition. -/
private lemma tailStandardizedCenteredArray_satisfiesLindeberg
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ) (N0 : ℕ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y P)
    (hY_bound : ∀ n ω, |Y n ω| ≤ B)
    (hVar0 : 0 < Var[Y N0; P])
    (hTail_notSummable : ¬ Summable (fun n : ℕ ↦ Var[Y (N0 + n); P])) :
    (tailStandardizedCenteredArray P Y N0 hY_meas).SatisfiesLindebergCondition P := by
  let A := tailStandardizedCenteredArray P Y N0 hY_meas
  have hA_indep : A.IsIndependent P :=
    tailStandardizedCenteredArray_isIndependent P Y N0 hY_meas hY_indep
  have hA_centered : A.IsCentered P :=
    tailStandardizedCenteredArray_isCentered P Y B N0 hY_meas hY_bound
  have hA_normed : A.IsNormed P :=
    tailStandardizedCenteredArray_isNormed P Y B N0 hY_meas hY_bound hVar0
  letI : A.IsIndependent P := hA_indep
  letI : A.IsCentered P := hA_centered
  letI : A.IsNormed P := hA_normed
  refine (RealRandomVariableArray.satisfiesLindebergCondition_iff (A := A) (μ := P)).2 ?_
  intro ε hε
  have hσ_tendsto :
      Tendsto (tailVarianceNormalizer P Y N0) atTop atTop :=
    tailVarianceNormalizer_tendsto_atTop P Y N0 hTail_notSummable
  have hscaled_zero :
      Tendsto
        (fun n : ℕ ↦ (tailVarianceNormalizer P Y N0 n)⁻¹ * (2 * |B|))
        atTop (𝓝 0) := by
    -- Proof comment: the deterministic rowwise entry bound shrinks to `0` because `σₙ → ∞`.
    simpa [mul_comm] using
      (tendsto_inv_atTop_zero.comp hσ_tendsto).mul_const (2 * |B|)
  have hsmall :
      ∀ᶠ n in atTop,
        (tailVarianceNormalizer P Y N0 n)⁻¹ * (2 * |B|) < ε :=
    hscaled_zero.eventually (Iio_mem_nhds hε)
  have hEqZero :
      (fun n ↦
        ∑ i : Fin (A.rowLength n),
          ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂P) =ᶠ[atTop]
        fun _ ↦ 0 := by
    filter_upwards [hsmall] with n hn
    have hterm :
        ∀ i : Fin (A.rowLength n),
          ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂P = 0 := by
      intro i
      have hpoint : ∀ ω, ¬ ε < |A n i ω| := by
        intro ω
        exact not_lt_of_ge ((tailStandardizedCenteredArray_abs_le
          P Y B N0 hY_meas hY_bound hVar0 n i ω).trans hn.le)
      have hzero :
          Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) =
            fun _ : Ω ↦ (0 : ℝ) := by
        funext ω
        simp [hpoint ω]
      rw [hzero, integral_zero]
    simp [hterm]
  -- Proof comment: once every row entry is uniformly below `ε`, the truncated second moments vanish.
  exact (tendsto_congr' hEqZero).2 tendsto_const_nhds

/-- Helper for Theorem 15.50: on almost every sample path, the normalized raw tail partial sums
converge to `0`. -/
private lemma ae_tendsto_normalizedTailRawSums_zero
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (N0 : ℕ)
    (hY_ae :
      ∀ᵐ ω ∂P, ∃ s : ℝ,
        Tendsto
          (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ Y k ω)
          atTop (𝓝 s))
    (hσ_tendsto : Tendsto (tailVarianceNormalizer P Y N0) atTop atTop) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ ↦
          (tailVarianceNormalizer P Y N0 n)⁻¹ *
            Finset.sum (Finset.range (n + 1)) (fun k ↦ Y (N0 + k) ω))
        atTop (𝓝 0) := by
  filter_upwards [hY_ae] with ω hω
  rcases hω with ⟨s, hs⟩
  have hTail_eq :
      (fun n : ℕ ↦ Finset.sum (Finset.range (n + 1)) (fun k ↦ Y (N0 + k) ω)) =
        fun n ↦
          Finset.sum (Finset.range (N0 + (n + 1))) (fun k ↦ Y k ω) -
            Finset.sum (Finset.range N0) (fun k ↦ Y k ω) := by
    funext n
    have hdiff := partialSum_sub_eq_sum_Ico Y (Nat.le_add_right N0 (n + 1)) ω
    simpa [partialSum, Finset.sum_Ico_eq_sum_range] using hdiff.symm
  have hTail_tendsto :
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range (n + 1)) (fun k ↦ Y (N0 + k) ω))
        atTop
        (𝓝
          (s - Finset.sum (Finset.range N0) (fun k ↦ Y k ω))) := by
    have hshift :
        Tendsto
          (fun n : ℕ ↦ Finset.sum (Finset.range (N0 + (n + 1))) (fun k ↦ Y k ω))
          atTop (𝓝 s) := by
      simpa [Function.comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hs.comp (tendsto_add_atTop_nat (N0 + 1))
    simpa [hTail_eq] using hshift.sub tendsto_const_nhds
  have hinv :
      Tendsto (fun n : ℕ ↦ (tailVarianceNormalizer P Y N0 n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hσ_tendsto
  -- Proof comment: the tail sums converge to a finite value while the normalizer diverges.
  simpa [mul_comm] using hinv.mul hTail_tendsto

/-- Helper for Theorem 15.50: a sequence of Dirac probability laws cannot converge weakly to the
standard Gaussian law. -/
private lemma not_tendsto_gaussian_of_diracSequence
    (c : ℕ → ℝ) :
    ¬ Tendsto
      (fun n ↦ diracProba (c n))
      atTop
      (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) := by
  intro h
  have hchar := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 h (1 : ℝ)
  have hchar' :
      Tendsto
        (fun n ↦ charFun (((diracProba (c n) : ProbabilityMeasure ℝ) : Measure ℝ)) (1 : ℝ))
        atTop
        (𝓝
          (charFun (((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ))
            (1 : ℝ))) := by
    simpa using hchar
  have hnorm :
      Tendsto
        (fun n ↦ ‖charFun (((diracProba (c n) : ProbabilityMeasure ℝ) : Measure ℝ)) (1 : ℝ)‖)
        atTop
        (𝓝
          ‖charFun (((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ))
            (1 : ℝ)‖) :=
    hchar'.norm
  have hnorm' :
      Tendsto
        (fun _ : ℕ ↦ (1 : ℝ))
        atTop
        (𝓝 (Real.exp (-(1 ^ 2 / 2 : ℝ)))) := by
    simpa [MeasureTheory.diracProba, MeasureTheory.charFun_dirac,
      ProbabilityTheory.charFun_gaussianReal, Complex.norm_exp] using hnorm
  have hEq : (1 : ℝ) = Real.exp (-(1 ^ 2 / 2 : ℝ)) :=
    tendsto_nhds_unique tendsto_const_nhds hnorm'
  have hexp_lt : Real.exp (-(1 ^ 2 / 2 : ℝ)) < 1 := by
    have hneg : (-(1 ^ 2 / 2 : ℝ)) < 0 := by norm_num
    exact Real.exp_lt_one_iff.mpr hneg
  exact (ne_of_lt hexp_lt) hEq.symm

/-- Helper for Theorem 15.50: if an independent uniformly bounded truncation sequence has
almost-surely convergent partial sums, then its variance series must be summable. -/
private lemma varianceSummable_of_ae_tendsto_truncation
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y P)
    (hY_bound : ∀ n ω, |Y n ω| ≤ B)
    (hY_ae :
      ∀ᵐ ω ∂P, ∃ s : ℝ,
        Tendsto
          (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ Y k ω)
          atTop (𝓝 s)) :
    Summable (fun n : ℕ ↦ Var[Y n; P]) := by
  by_contra hVar_notSummable
  rcases exists_variance_pos_of_not_summable P Y hVar_notSummable with ⟨N0, hVar0⟩
  have hTail_notSummable : ¬ Summable (fun n : ℕ ↦ Var[Y (N0 + n); P]) := by
    intro hTail
    apply hVar_notSummable
    have hTail' : Summable (fun n : ℕ ↦ Var[Y (n + N0); P]) := by
      refine hTail.congr ?_
      intro n
      rw [Nat.add_comm]
    exact (summable_nat_add_iff (f := fun n : ℕ ↦ Var[Y n; P]) N0).1 hTail'
  let A := tailStandardizedCenteredArray P Y N0 hY_meas
  have hσ_tendsto :
      Tendsto (tailVarianceNormalizer P Y N0) atTop atTop :=
    tailVarianceNormalizer_tendsto_atTop P Y N0 hTail_notSummable
  have hA_indep : A.IsIndependent P :=
    tailStandardizedCenteredArray_isIndependent P Y N0 hY_meas hY_indep
  have hA_centered : A.IsCentered P :=
    tailStandardizedCenteredArray_isCentered P Y B N0 hY_meas hY_bound
  have hA_normed : A.IsNormed P :=
    tailStandardizedCenteredArray_isNormed P Y B N0 hY_meas hY_bound hVar0
  letI : A.IsIndependent P := hA_indep
  letI : A.IsCentered P := hA_centered
  letI : A.IsNormed P := hA_normed
  have hA_lindeberg : A.SatisfiesLindebergCondition P :=
    tailStandardizedCenteredArray_satisfiesLindeberg
      P Y B N0 hY_meas hY_indep hY_bound hVar0 hTail_notSummable
  have hGaussianLaw :
      Tendsto (fun n ↦ A.rowSumLaw P n) atTop
        (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) := by
    exact
      ((RealRandomVariableArray.lindeberg_feller_central_limit_theorem
        (A := A) (μ := P)).1 hA_lindeberg).2
  have hRowSumDist :
      TendstoInDistribution (fun n ↦ A.rowSum n) atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    exact
      (tendstoInDistribution_iff_tendsto_limit_law
        (X := fun n ↦ A.rowSum n) (l := atTop) (μ := fun _ ↦ P)
        (Z := id) (μ' := gaussianReal 0 1)
        (ν := ⟨gaussianReal 0 1, inferInstance⟩)
        (hX := fun n ↦ (A.measurable_rowSum n).aemeasurable) HasLaw.id).2
        hGaussianLaw
  let raw : ℕ → Ω → ℝ := fun n ω ↦
    (tailVarianceNormalizer P Y N0 n)⁻¹ *
      Finset.sum (Finset.range (n + 1)) (fun k ↦ Y (N0 + k) ω)
  have hRaw_ae :
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ raw n ω) atTop (𝓝 0) :=
    ae_tendsto_normalizedTailRawSums_zero P Y N0 hY_ae hσ_tendsto
  have hRaw_tendsto :
      TendstoInMeasure P raw atTop (fun _ ↦ (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae ?_ hRaw_ae
    intro n
    exact
      ((partialSum_measurable (fun k ↦ Y (N0 + k)) (fun k ↦ hY_meas (N0 + k)) (n + 1)).const_mul
        ((tailVarianceNormalizer P Y N0 n)⁻¹)).aestronglyMeasurable
  let c : ℕ → ℝ := fun n ↦
    -((tailVarianceNormalizer P Y N0 n)⁻¹ *
      Finset.sum (Finset.range (n + 1)) (fun k ↦ P[Y (N0 + k)]))
  have hRow_eq :
      ∀ n, A.rowSum n =ᵐ[P] fun ω ↦ raw n ω + c n := by
    intro n
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    -- Proof comment: split the centered row sum into the raw tail sum and the deterministic mean correction.
    calc
      A.rowSum n ω
          = (tailVarianceNormalizer P Y N0 n)⁻¹ *
              Finset.sum (Finset.range (n + 1)) (fun k ↦ Y (N0 + k) ω - P[Y (N0 + k)]) := by
                simpa [A] using tailStandardizedCenteredArray_rowSum_eq P Y N0 hY_meas n ω
      _ = (tailVarianceNormalizer P Y N0 n)⁻¹ *
            (Finset.sum (Finset.range (n + 1)) (fun k ↦ Y (N0 + k) ω) -
              Finset.sum (Finset.range (n + 1)) (fun k ↦ P[Y (N0 + k)])) := by
              rw [Finset.sum_sub_distrib]
      _ = raw n ω + c n := by
            simp [raw, c]
            ring
  have hSumDist :
      TendstoInDistribution (fun n ↦ fun ω ↦ raw n ω + c n)
        atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    refine MeasureTheory.TendstoInDistribution.congr
      (fun n ↦ hRow_eq n) (Filter.Eventually.of_forall fun x ↦ rfl) hRowSumDist
  have hNegRaw_ae :
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ -raw n ω) atTop (𝓝 0) := by
    filter_upwards [hRaw_ae] with ω hω
    simpa using hω.neg
  have hNegRaw_tendsto :
      TendstoInMeasure P (fun n ↦ fun ω ↦ -raw n ω) atTop (fun _ ↦ (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae ?_ hNegRaw_ae
    intro n
    exact
      (((partialSum_measurable (fun k ↦ Y (N0 + k)) (fun k ↦ hY_meas (N0 + k)) (n + 1)).const_mul
        ((tailVarianceNormalizer P Y N0 n)⁻¹)).aestronglyMeasurable).neg
  have hConstDist :
      TendstoInDistribution (fun n ↦ fun _ : Ω ↦ c n)
        atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    have hcancel :
        TendstoInDistribution
          (fun n ↦ fun ω ↦ (raw n ω + c n) + (-raw n ω))
          atTop (fun ω ↦ id ω + 0) (fun _ ↦ P) (gaussianReal 0 1) :=
      hSumDist.add_of_tendstoInMeasure_const hNegRaw_tendsto
        (fun n ↦
          (((partialSum_measurable (fun k ↦ Y (N0 + k)) (fun k ↦ hY_meas (N0 + k)) (n + 1)).const_mul
            ((tailVarianceNormalizer P Y N0 n)⁻¹)).aemeasurable).neg)
    simpa [raw, Pi.add_def, Pi.neg_def] using hcancel
  have hConstLaw :
      Tendsto (fun n ↦ diracProba (c n)) atTop
        (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) := by
    have hLaw :=
      (tendstoInDistribution_iff_tendsto_limit_law
        (X := fun n ↦ fun _ : Ω ↦ c n) (l := atTop) (μ := fun _ ↦ P)
        (Z := id) (μ' := gaussianReal 0 1)
        (ν := ⟨gaussianReal 0 1, inferInstance⟩)
        (hX := fun n ↦ measurable_const.aemeasurable) HasLaw.id).1 hConstDist
    simpa [MeasureTheory.diracProba] using hLaw
  -- Route correction: the forward implication needs the tail-started normalized-array
  -- contradiction from Theorem 15.43, not more theorem-body algebra. The tail start `N₀` and the
  -- positive normalizer `σₙ` are now stabilized; the remaining work is to pass from
  -- `¬ Summable (fun n ↦ Var[Y (N0 + n); P])` to `tailVarianceNormalizer P Y N0 → ∞`, then package
  -- the centered normalized tail array, verify its Lindeberg condition from `|Yₙ| ≤ B`, and
  -- compare its Gaussian row-sum law with the `diracProba 0` limit of the normalized uncentered
  -- tail sums.
  exact not_tendsto_gaussian_of_diracSequence c hConstLaw

/-- Theorem 15.50: for independent real random variables `X₁, X₂, …` and the truncations
`Yₙ = Xₙ 𝟙_{|Xₙ| ≤ K}` with `K > 0`, the series `∑ Xₙ` converges almost surely exactly when the
real tail probabilities `∑ P(|Xₙ| > K)` are summable, the series of expectations `∑ E[Yₙ]`
converges, and the series of variances `∑ Var[Yₙ]` is summable. -/
theorem ae_summable_iff_three_series_conditions
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℝ) (hK : 0 < K) (X : ℕ → Ω → ℝ)
    (hX_measurable : ∀ n, Measurable (X (n + 1)))
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P) :
    (∀ᵐ ω ∂P, ∃ s : ℝ,
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ X (k + 1) ω)
        atTop (𝓝 s)) ↔
      Summable (fun n : ℕ ↦ P.real {ω | K < |X (n + 1) ω|}) ∧
        (∃ s : ℝ,
          Tendsto
            (fun n : ℕ ↦
              Finset.sum (Finset.range n) fun k ↦
                P[Set.indicator {ω | |X (k + 1) ω| ≤ K} (X (k + 1))])
            atTop (𝓝 s)) ∧
          Summable
            (fun n : ℕ ↦
              Var[Set.indicator {ω | |X (n + 1) ω| ≤ K} (X (n + 1)); P]) := by
  constructor
  · intro hX_ae
    -- Route correction: the converse is not a local algebraic cleanup; it needs the
    -- independent-event Borel--Cantelli converse for the large-jump events and then the
    -- normalized-array contradiction from Theorem 15.43 to force truncated variance summability.
    let Y : ℕ → Ω → ℝ := threeSeriesTruncation K X
    let trunc : ℝ → ℝ := fun x ↦ if |x| ≤ K then x else 0
    have hTail :
        Summable (fun n : ℕ ↦ P.real {ω | K < |X (n + 1) ω|}) :=
      tailProbSummable_of_ae_tendsto_sum_range P K hK X hX_measurable hX_indep hX_ae
    have hTailEq :
        ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
          Y n ω = X (n + 1) ω := by
      simpa [Y] using ae_eventually_truncation_eq_original_of_tailProbSummable P K X hTail
    have hY_ae :
        ∀ᵐ ω ∂P, ∃ s : ℝ,
          Tendsto
            (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ Y k ω)
            atTop (𝓝 s) := by
      filter_upwards [hX_ae, hTailEq] with ω hω hEq
      -- Proof comment: once the tails agree almost surely, convergence transfers to the
      -- truncated partial sums by a fixed prefix correction.
      exact
        exists_tendsto_sum_range_of_eventuallyEq
          (x := fun n ↦ Y n ω)
          (y := fun n ↦ X (n + 1) ω)
          hEq hω
    have htrunc_meas : Measurable trunc := by
      -- Proof comment: the scalar truncation is the measurable piecewise map `x ↦ x` / `0`.
      refine measurable_id.piecewise (measurableSet_le measurable_abs measurable_const) measurable_const
    have hY_meas : ∀ n, Measurable (Y n) := by
      intro n
      simpa [Y, threeSeriesTruncation, trunc, Set.indicator] using
        (hX_measurable n).piecewise (measurableSet_le (hX_measurable n).abs measurable_const)
          measurable_const
    have hY_indep : iIndepFun Y P := by
      -- Proof comment: `Yₙ` is a measurable coordinatewise transform of `Xₙ`.
      simpa [Y, threeSeriesTruncation, trunc, Set.indicator] using
        hX_indep.comp (fun _ ↦ trunc) (fun _ ↦ htrunc_meas)
    have hY_bound : ∀ n ω, |Y n ω| ≤ K := by
      intro n ω
      by_cases hω : |X (n + 1) ω| ≤ K
      · simpa [Y, threeSeriesTruncation, Set.indicator, hω] using hω
      · simpa [Y, threeSeriesTruncation, Set.indicator, hω] using hK.le
    have hVar :
        Summable (fun n : ℕ ↦ Var[Y n; P]) := by
      -- Proof comment: isolate the forward variance contradiction in a dedicated helper so the
      -- main theorem only consumes the finished variance criterion.
      exact varianceSummable_of_ae_tendsto_truncation P Y K hY_meas hY_indep hY_bound hY_ae
    have hCentered_ae :
        ∀ᵐ ω ∂P, ∃ s : ℝ,
          Tendsto
            (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ (Y k ω - P[Y k]))
            atTop (𝓝 s) :=
      ae_tendsto_centeredPartialSums_of_varianceSummable
        P Y K hY_meas hY_indep hY_bound hVar
    have hExp_ae :
        ∀ᵐ ω ∂P, ∃ s : ℝ,
          Tendsto
            (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ P[Y k])
            atTop (𝓝 s) := by
      filter_upwards [hY_ae, hCentered_ae] with ω hω_trunc hω_centered
      rcases hω_trunc with ⟨sTrunc, hsTrunc⟩
      rcases hω_centered with ⟨sCentered, hsCentered⟩
      refine ⟨sTrunc - sCentered, ?_⟩
      have hsum_eq :
          ∀ n : ℕ,
            Finset.sum (Finset.range n) (fun k ↦ P[Y k]) =
              Finset.sum (Finset.range n) (fun k ↦ Y k ω) -
                Finset.sum (Finset.range n) (fun k ↦ (Y k ω - P[Y k])) := by
        intro n
        -- Proof comment: the deterministic expectation partial sum is the difference between the
        -- truncated partial sum and the centered truncated partial sum.
        calc
          Finset.sum (Finset.range n) (fun k ↦ P[Y k])
              = Finset.sum (Finset.range n) (fun k ↦ Y k ω - (Y k ω - P[Y k])) := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  ring
          _ = Finset.sum (Finset.range n) (fun k ↦ Y k ω) -
                Finset.sum (Finset.range n) (fun k ↦ (Y k ω - P[Y k])) := by
                  rw [Finset.sum_sub_distrib]
      refine (tendsto_congr' (Filter.Eventually.of_forall hsum_eq)).2 ?_
      exact hsTrunc.sub hsCentered
    have hExp :
        ∃ s : ℝ,
          Tendsto
            (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ P[Y k])
            atTop (𝓝 s) := by
      by_contra hExp
      have hnot_ae :
          ¬ ∀ᵐ ω ∂P, ∃ s : ℝ,
              Tendsto
                (fun n : ℕ ↦ Finset.sum (Finset.range n) fun k ↦ P[Y k])
                atTop (𝓝 s) := by
        rw [ae_iff]
        simpa [hExp, IsProbabilityMeasure.measure_univ]
      exact hnot_ae hExp_ae
    refine ⟨hTail, ?_, ?_⟩
    · simpa [Y, threeSeriesTruncation] using hExp
    · simpa [Y, threeSeriesTruncation] using hVar
  · rintro ⟨hTail, hExp, hVar⟩
    let Y : ℕ → Ω → ℝ := threeSeriesTruncation K X
    let trunc : ℝ → ℝ := fun x ↦ if |x| ≤ K then x else 0
    have htrunc_meas : Measurable trunc := by
      -- Proof comment: the scalar truncation is the measurable piecewise map `x ↦ x` / `0`.
      refine measurable_id.piecewise (measurableSet_le measurable_abs measurable_const) measurable_const
    have hY_meas : ∀ n, Measurable (Y n) := by
      intro n
      exact (hX_measurable n).indicator (measurableSet_le (hX_measurable n).abs measurable_const)
    have hY_indep : iIndepFun Y P := by
      -- Proof comment: `Yₙ` is the truncation of `Xₙ` by the measurable scalar cutoff map.
      simpa [Y, threeSeriesTruncation, trunc, Set.indicator] using
        hX_indep.comp (fun _ ↦ trunc) (fun _ ↦ htrunc_meas)
    have hY_bound : ∀ n ω, |Y n ω| ≤ K := by
      intro n ω
      by_cases hω : |X (n + 1) ω| ≤ K
      · simpa [Y, threeSeriesTruncation, Set.indicator, hω] using hω
      · simpa [Y, threeSeriesTruncation, Set.indicator, hω] using hK.le
    have hExpTrunc :
        ∃ s : ℝ,
          Tendsto
            (fun n : ℕ ↦
              Finset.sum (Finset.range n) fun k ↦ P[threeSeriesTruncation K X k])
            atTop (𝓝 s) := by
      simpa [threeSeriesTruncation] using hExp
    have hVarTrunc :
        Summable (fun n : ℕ ↦ Var[threeSeriesTruncation K X n; P]) := by
      simpa [threeSeriesTruncation] using hVar
    have hTrunc_ae :
        ∀ᵐ ω ∂P, ∃ s : ℝ,
          Tendsto
            (fun n : ℕ ↦
              Finset.sum (Finset.range n) fun k ↦ Y k ω)
            atTop (𝓝 s) :=
      ae_tendsto_partialSums_of_expectationTendsto_and_varianceSummable
        P Y K hY_meas hY_indep hY_bound hExpTrunc hVarTrunc
    have hTailEq :
        ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
          threeSeriesTruncation K X n ω = X (n + 1) ω :=
      ae_eventually_truncation_eq_original_of_tailProbSummable P K X hTail
    filter_upwards [hTrunc_ae, hTailEq] with ω hTrunc hEq
    -- Proof comment: eventual equality of the terms makes the original and truncated partial sums
    -- differ by a fixed prefix correction, so convergence transfers from `Yₙ` back to `Xₙ`.
    exact
      exists_tendsto_sum_range_of_eventuallyEq
        (x := fun n ↦ X (n + 1) ω)
        (y := fun n ↦ Y n ω)
        (hEq.mono fun _ hn ↦ hn.symm) hTrunc
