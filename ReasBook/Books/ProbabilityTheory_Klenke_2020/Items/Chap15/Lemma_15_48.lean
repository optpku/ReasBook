/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_40

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

section

variable (A : RealRandomVariableArray Ω) (P : Measure Ω)

/-- The variance-weighted row measure `νₙ` obtained from the `n`-th row by summing the pushforwards
of the measures with density `Xₙ,ᵢ^2`. -/
def varianceWeightedRowMeasure (A : RealRandomVariableArray Ω) (P : Measure Ω) (n : ℕ) :
    Measure ℝ :=
  ∑ i : Fin (A.rowLength n),
    (P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)

end

section

variable (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
variable [A.IsNormed P]

-- Proof sketch: unfold `varianceWeightedRowMeasure`, evaluate the pushforward-with-density sum on
-- the Borel set `{x | ε < |x|}`, and rewrite each summand as the corresponding truncated second
-- moment.
/-- The tail of `νₙ` outside `(-ε, ε)` is the `n`-th Lindeberg truncated second-moment sum. -/
theorem varianceWeightedRowMeasure_tail_eq
    (ε : ℝ) (n : ℕ) :
    (A.varianceWeightedRowMeasure P n).real {x | ε < |x|} =
      ∑ i : Fin (A.rowLength n),
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂P := by
  classical
  let s : Set ℝ := {x | ε < |x|}
  have hs : MeasurableSet s := by
    -- Proof comment: the tail set is measurable because `x ↦ |x|` is measurable.
    exact measurableSet_lt measurable_const measurable_abs
  -- Proof comment: expand the finite weighted-row measure sum and compute each pushforward term on
  -- the tail set.
  rw [varianceWeightedRowMeasure, Measure.real_def]
  have hsum :
      ((∑ i : Fin (A.rowLength n),
          (P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal =
        ∑ i : Fin (A.rowLength n),
          (((P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal := by
    calc
      ((∑ i : Fin (A.rowLength n),
          (P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal =
          (∑ i : Fin (A.rowLength n),
            ((P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal := by
            simpa using
              congrArg ENNReal.toReal
                (Measure.sum_apply
                  (f := fun i : Fin (A.rowLength n) ↦
                    (P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i))
                  hs)
      _ = ∑ i : Fin (A.rowLength n),
            (((P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal := by
            rw [ENNReal.toReal_sum]
            intro i hi
            have hSqInt :
                HasFiniteIntegral (fun ω ↦ (A n i ω) ^ 2) P := by
              have hIntegrableSq :
                  Integrable (fun ω ↦ (A n i ω) ^ 2) P := by
                simpa using
                  (RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := P) n i).integrable_sq
              exact hIntegrableSq.hasFiniteIntegral
            letI :
                IsFiniteMeasure (P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)) :=
              MeasureTheory.isFiniteMeasure_withDensity_ofReal hSqInt
            exact measure_ne_top _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hs_pre : MeasurableSet ((A n i) ⁻¹' s) :=
    (A.measurable_entry n i) hs
  have hDensity_meas :
      AEMeasurable (fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)) (P.restrict ((A n i) ⁻¹' s)) := by
    exact (((A.measurable_entry n i).pow_const 2).ennreal_ofReal.aemeasurable).restrict
  have hDensity_lt_top :
      ∀ᵐ ω ∂(P.restrict ((A n i) ⁻¹' s)), ENNReal.ofReal ((A n i ω) ^ 2) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by simp
  calc
    ((((P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal) =
        (∫⁻ ω in (A n i) ⁻¹' s, ENNReal.ofReal ((A n i ω) ^ 2) ∂P).toReal := by
          rw [Measure.map_apply (A.measurable_entry n i) hs, withDensity_apply _ hs_pre]
    _ = ∫ ω in (A n i) ⁻¹' s, (A n i ω) ^ 2 ∂P := by
          -- Proof comment: the density is finite everywhere, so `integral_toReal` converts the
          -- lower integral over the restricted measure into the corresponding set integral.
          simpa [ENNReal.toReal_ofReal, sq_nonneg] using
            (MeasureTheory.integral_toReal (μ := P.restrict ((A n i) ⁻¹' s))
              hDensity_meas hDensity_lt_top).symm
    _ = ∫ ω, Set.indicator ((A n i) ⁻¹' s) (fun ω ↦ (A n i ω) ^ 2) ω ∂P := by
          rw [MeasureTheory.integral_indicator hs_pre]
    _ = ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂P := by
          simp [s]

end

section

variable (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
variable [A.IsCentered P] [A.IsNormed P]

/-- Helper for Lemma 15.48: the variance-weighted row measure has total mass `1`. -/
private lemma varianceWeightedRowMeasure_real_univ
    (n : ℕ) :
    (A.varianceWeightedRowMeasure P n).real Set.univ = 1 := by
  have hTail :=
    varianceWeightedRowMeasure_tail_eq (A := A) (P := P) (-1) n
  have hUniv : {x : ℝ | (-1 : ℝ) < |x|} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    linarith [abs_nonneg x]
  rw [hUniv] at hTail
  -- Proof comment: evaluating the tail identity at `ε = -1` turns the tail set into all of
  -- `ℝ`, so the total mass becomes the sum of the entry second moments.
  calc
    (A.varianceWeightedRowMeasure P n).real Set.univ =
        ∑ i : Fin (A.rowLength n),
          ∫ ω, Set.indicator {ω | (-1 : ℝ) < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂P := by
          simpa [hUniv] using hTail
    _ = ∑ i : Fin (A.rowLength n), ∫ ω, (A n i ω) ^ 2 ∂P := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hAll : {ω : Ω | (-1 : ℝ) < |A n i ω|} = Set.univ := by
            ext ω
            simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
            linarith [abs_nonneg (A n i ω)]
          simp [hAll]
    _ = ∑ i : Fin (A.rowLength n), Var[A n i; P] := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact
            (ProbabilityTheory.variance_of_integral_eq_zero
              (A.measurable_entry n i).aemeasurable
              (RealRandomVariableArray.IsCentered.expectation_eq_zero
                (A := A) (μ := P) n i)).symm
    _ = 1 := RealRandomVariableArray.IsNormed.variance_sum_eq_one (A := A) (μ := P) n

-- Proof sketch: evaluate `varianceWeightedRowMeasure A P n` on `Set.univ`, rewrite each summand
-- as the second moment of `A.entry n i`, use centering to identify it with the variance, and then
-- apply the row-normalization hypothesis.
/-- The variance-weighted row measure has total mass `1` under the centered and normed
hypotheses. -/
theorem varianceWeightedRowMeasure_isProbabilityMeasure
    (n : ℕ) :
    IsProbabilityMeasure (A.varianceWeightedRowMeasure P n) := by
  -- Proof comment: `real Set.univ = 1` is the canonical criterion for being a probability
  -- measure.
  rw [MeasureTheory.isProbabilityMeasure_iff_real]
  exact varianceWeightedRowMeasure_real_univ (A := A) (P := P) n

/-- The probability measure `νₙ` attached to the `n`-th row by weighting each entry law with
`x^2`. -/
noncomputable def varianceWeightedRowLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨A.varianceWeightedRowMeasure P n, varianceWeightedRowMeasure_isProbabilityMeasure A P n⟩

/-- The underlying measure of `varianceWeightedRowLaw` is `varianceWeightedRowMeasure`. -/
@[simp] theorem varianceWeightedRowLaw_toMeasure (n : ℕ) :
    (A.varianceWeightedRowLaw P n : Measure ℝ) = A.varianceWeightedRowMeasure P n := rfl

end

section

variable (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
variable [A.IsIndependent P] [A.IsNormed P]

section

variable [A.IsCentered P]

-- Route correction: avoid importing `Theorem_15_43` directly because the external chapter module
-- is not dependency-clean in this workspace; only the local Lindeberg/truncated-moment bridge is
-- needed for Lemma 15.48.
/-- Helper for Lemma 15.48: under the independent centered normed hypotheses, every row sum has
variance `1`. -/
private lemma rowSumVarianceEqOne
    (n : ℕ) :
    Var[A.rowSum n; P] = 1 := by
  have hPairwise : Pairwise fun i j : Fin (A.rowLength n) ↦ A n i ⟂ᵢ[P] A n j := by
    intro i j hij
    exact (RealRandomVariableArray.IsIndependent.rowwise (A := A) (μ := P) n).indepFun hij
  -- Proof comment: rowwise independence identifies the row-sum variance with the sum of the entry
  -- variances, and the normed-array hypothesis normalizes that sum to `1`.
  calc
    Var[A.rowSum n; P] = ∑ i : Fin (A.rowLength n), Var[A n i; P] := by
      simpa [RealRandomVariableArray.rowSum] using
        ProbabilityTheory.IndepFun.variance_sum
          (μ := P) (X := fun i : Fin (A.rowLength n) ↦ A n i) (s := Finset.univ)
          (hs := fun i _ ↦ RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := P) n i)
          (by
            intro i _ j _ hij
            exact hPairwise hij)
    _ = 1 := RealRandomVariableArray.IsNormed.variance_sum_eq_one (A := A) (μ := P) n

/-- Helper for Lemma 15.48: once `Var[A.rowSum n; P] = 1`, the Lindeberg quantity `Lₙ(ε)` is
exactly the truncated second-moment sum over the tail event `{ω | ε < |A n i ω|}`. -/
private lemma lindebergFunction_eq_rowTruncatedSecondMoment
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    A.lindebergFunction P ε n =
      ∑ i : Fin (A.rowLength n),
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂P := by
  -- Proof comment: normalize `Var[A.rowSum n; P]` to `1` and rewrite `ε^2 < X^2` as
  -- `ε < |X|` because `ε > 0`.
  rw [RealRandomVariableArray.lindebergFunction_def]
  rw [rowSumVarianceEqOne (A := A) (P := P) n, inv_one, one_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hs :
      {ω | ε ^ 2 * (1 : ℝ) < (A n i ω) ^ 2} = {ω | ε < |A n i ω|} := by
    ext ω
    simp [sq_lt_sq, abs_of_pos hε]
  rw [hs]

/-- Helper for Lemma 15.48: in the centered normed setting, the Lindeberg condition is equivalent
to the vanishing of the rowwise truncated second moments. -/
private lemma satisfiesLindebergCondition_iff_truncatedSecondMoment
    :
    A.SatisfiesLindebergCondition P ↔
      ∀ ⦃ε : ℝ⦄, 0 < ε →
        Tendsto
          (fun n ↦
            ∑ i : Fin (A.rowLength n),
              ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂P)
          atTop (𝓝 0) := by
  constructor
  · intro hLindeberg ε hε
    -- Proof comment: rewrite the defining Lindeberg quantity into the textbook truncated
    -- second-moment expression row by row.
    simpa [lindebergFunction_eq_rowTruncatedSecondMoment (A := A) (P := P) hε] using
      hLindeberg.lindeberg_tendsto hε
  · intro hTrunc
    -- Proof comment: package the same rowwise rewrite back into the structure fields of
    -- `SatisfiesLindebergCondition`.
    refine
      { toIsCentered := inferInstance
        memLp_two := RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := P)
        lindeberg_tendsto := ?_ }
    intro ε hε
    simpa [lindebergFunction_eq_rowTruncatedSecondMoment (A := A) (P := P) hε] using hTrunc hε

end

/-- Helper for Lemma 15.48: the weighted-row-law tails vanish outside every neighborhood of `0`
once the Lindeberg condition holds. -/
private lemma varianceWeightedRowLaw_tail_tendsto_zero_of_satisfiesLindebergCondition
    (hLindeberg : A.SatisfiesLindebergCondition P)
    {ε : ℝ} (hε : 0 < ε) :
    letI : A.IsCentered P := hLindeberg.toIsCentered
    Tendsto
      (fun n ↦ (A.varianceWeightedRowLaw P n : Measure ℝ).real {x | ε < |x|})
      atTop (𝓝 0) := by
  letI : A.IsCentered P := hLindeberg.toIsCentered
  -- Proof comment: rewrite the weighted-row law back to its underlying measure and identify the
  -- tail with the textbook Lindeberg truncated second-moment sum.
  have hEq :
      (fun n ↦ (A.varianceWeightedRowLaw P n : Measure ℝ).real {x | ε < |x|}) =
        (fun n ↦
          ∑ i : Fin (A.rowLength n),
            ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂P) := by
    funext n
    simpa [varianceWeightedRowLaw_toMeasure (A := A) (P := P) n] using
      varianceWeightedRowMeasure_tail_eq (A := A) (P := P) ε n
  rw [hEq]
  exact
    (satisfiesLindebergCondition_iff_truncatedSecondMoment
      (A := A) (P := P)).1 hLindeberg hε

/-- Helper for Lemma 15.48: tail concentration near `0` forces convergence of bounded continuous
integrals to evaluation at `0`. -/
private lemma tendsto_integral_boundedContinuous_of_tail_tendsto_zero
    {ν : ℕ → ProbabilityMeasure ℝ}
    (hTail : ∀ ⦃ε : ℝ⦄, 0 < ε →
      Tendsto (fun n ↦ (ν n : Measure ℝ).real {x | ε < |x|}) atTop (𝓝 0))
    (f : BoundedContinuousFunction ℝ ℂ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(ν n : Measure ℝ)) atTop (𝓝 (f 0)) := by
  let g : BoundedContinuousFunction ℝ ℂ := f - BoundedContinuousFunction.const ℝ (f 0)
  have hg0 : g 0 = 0 := by
    -- Proof comment: subtracting the constant `f 0` centers the test function at the limiting
    -- point `0`.
    simp [g]
  have hIntegralEq :
      (fun n ↦ ∫ x, f x ∂(ν n : Measure ℝ)) =
        fun n ↦ ∫ x, g x ∂(ν n : Measure ℝ) + f 0 := by
    funext n
    have hgInt : Integrable g (ν n : Measure ℝ) :=
      BoundedContinuousFunction.integrable (μ := (ν n : Measure ℝ)) g
    have hConstInt : Integrable (fun _ : ℝ ↦ (f 0 : ℂ)) (ν n : Measure ℝ) :=
      integrable_const _
    -- Proof comment: decompose `f` into its centered part plus the constant value at `0`.
    calc
      ∫ x, f x ∂(ν n : Measure ℝ) = ∫ x, (g x + f 0) ∂(ν n : Measure ℝ) := by
        congr 1 with x
        simp [g]
      _ = ∫ x, g x ∂(ν n : Measure ℝ) + ∫ x, (f 0 : ℂ) ∂(ν n : Measure ℝ) := by
        rw [integral_add hgInt hConstInt]
      _ = ∫ x, g x ∂(ν n : Measure ℝ) + f 0 := by
        simp
  rw [hIntegralEq]
  have hCentered :
      Tendsto (fun n ↦ ∫ x, g x ∂(ν n : Measure ℝ)) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.1 g.continuous.continuousAt (ε / 4) (by positivity)
    let r : ℝ := δ / 2
    let s : Set ℝ := {x | r < |x|}
    have hrpos : 0 < r := by
      -- Proof comment: choose a smaller radius so points outside the tail set stay in the
      -- continuity-control ball around `0`.
      dsimp [r]
      exact half_pos hδpos
    have hs : MeasurableSet s := by
      exact measurableSet_lt measurable_const measurable_abs
    let C : ℝ := ‖g‖ + 1
    have hCpos : 0 < C := by
      dsimp [C]
      positivity
    have hTailSmall : ∀ᶠ n in atTop, (ν n : Measure ℝ).real s < ε / (4 * C) := by
      have hTail' : Tendsto (fun n ↦ (ν n : Measure ℝ).real s) atTop (𝓝 0) := by
        simpa [s, r] using hTail hrpos
      exact hTail' (Iio_mem_nhds (by positivity : 0 < ε / (4 * C)))
    filter_upwards [hTailSmall] with n hn
    have hgInt : Integrable g (ν n : Measure ℝ) :=
      BoundedContinuousFunction.integrable (μ := (ν n : Measure ℝ)) g
    have hs_lt_top : (ν n : Measure ℝ) s < ⊤ := by
      simp [s]
    have hscompl_lt_top : (ν n : Measure ℝ) sᶜ < ⊤ := by
      simp [s]
    have hSmallOnCompl : ∀ x ∈ sᶜ, ‖g x‖ ≤ ε / 4 := by
      intro x hx
      have hxle : |x| ≤ r := by
        dsimp [s] at hx
        exact le_of_not_gt hx
      have hrlt : r < δ := by
        dsimp [r]
        linarith
      have hxdist : dist x 0 < δ := by
        simpa [Real.dist_eq, abs_sub_comm] using lt_of_le_of_lt hxle hrlt
      have hxcont : dist (g x) (g 0) < ε / 4 := hδ hxdist
      -- Proof comment: outside the tail set, the centered test function is uniformly small.
      simpa [hg0, dist_eq_norm] using le_of_lt hxcont
    have hTailIntegral :
        ‖∫ x in s, g x ∂(ν n : Measure ℝ)‖ < ε / 4 := by
      have hBase :
          ‖∫ x in s, g x ∂(ν n : Measure ℝ)‖ ≤ ‖g‖ * (ν n : Measure ℝ).real s :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hs_lt_top
          (fun x _ ↦ BoundedContinuousFunction.norm_coe_le_norm g x)
      have hCmul :
          ‖g‖ * (ν n : Measure ℝ).real s ≤ C * (ν n : Measure ℝ).real s := by
        dsimp [C]
        gcongr
        linarith
      have hScaled :
          C * (ν n : Measure ℝ).real s < C * (ε / (4 * C)) := by
        gcongr
      have hRewrite : C * (ε / (4 * C)) = ε / 4 := by
        field_simp [hCpos.ne']
      exact lt_of_le_of_lt (hBase.trans hCmul) (hScaled.trans_eq hRewrite)
    have hComplIntegral :
        ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ ≤ ε / 4 := by
      have hBase :
          ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ ≤
            (ε / 4) * (ν n : Measure ℝ).real sᶜ :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hscompl_lt_top hSmallOnCompl
      have hMassLeOne : (ν n : Measure ℝ).real sᶜ ≤ 1 := by
        calc
          (ν n : Measure ℝ).real sᶜ ≤ (ν n : Measure ℝ).real Set.univ := by
            exact MeasureTheory.measureReal_mono (by intro x _; simp)
          _ = 1 := by
            simp
      calc
        ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ ≤ (ε / 4) * (ν n : Measure ℝ).real sᶜ := hBase
        _ ≤ (ε / 4) * 1 := by
          gcongr
        _ = ε / 4 := by ring
    have hSplit := (integral_add_compl hs hgInt).symm
    -- Proof comment: split the centered integral into its tail part and near-zero part, each of
    -- which is small for large `n`.
    calc
      dist (∫ x, g x ∂(ν n : Measure ℝ)) 0 = ‖∫ x, g x ∂(ν n : Measure ℝ)‖ := by
        simp [dist_eq_norm]
      _ = ‖∫ x in s, g x ∂(ν n : Measure ℝ) + ∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ := by
        rw [← hSplit]
      _ ≤ ‖∫ x in s, g x ∂(ν n : Measure ℝ)‖ + ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ := by
        exact norm_add_le _ _
      _ ≤ ε / 4 + ε / 4 := by
        linarith [le_of_lt hTailIntegral, hComplIntegral]
      _ = ε / 2 := by ring
      _ < ε := by linarith
  simpa [zero_add] using hCentered.add tendsto_const_nhds

/-- Helper for Lemma 15.48: vanishing tails outside every neighborhood of `0` force weak
convergence to `diracProba 0`. -/
private lemma tendsto_diracProba_zero_of_tail_tendsto_zero
    {ν : ℕ → ProbabilityMeasure ℝ}
    (hTail : ∀ ⦃ε : ℝ⦄, 0 < ε →
      Tendsto (fun n ↦ (ν n : Measure ℝ).real {x | ε < |x|}) atTop (𝓝 0)) :
    Tendsto ν atTop (𝓝 (diracProba (0 : ℝ))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  have hIntegral :=
    tendsto_integral_boundedContinuous_of_tail_tendsto_zero hTail f
  have hDirac :
      (∫ x, f x ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = f 0 := by
    rw [show (((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = Measure.dirac (0 : ℝ)
      by rfl]
    rw [integral_dirac]
  convert hIntegral using 1
  exact congrArg nhds hDirac

-- Proof sketch: `varianceWeightedRowMeasure_tail_eq` identifies the tails of `νₙ` with the
-- rowwise truncated second moments, and under the independent centered normed hypotheses of
-- Theorem 15.43 the normalization in `Lₙ(ε)` is `Var[A.rowSum n; P] = 1`; `h_lindeberg` supplies
-- the centered instance needed to view each `νₙ` as a probability measure, and vanishing mass
-- outside every neighborhood of `0` yields weak convergence to `δ₀`.
/-- Lemma 15.48: if the Lindeberg condition from Theorem 15.43 (i) holds, then the variance-weighted
row laws `νₙ` of an independent normed array converge weakly to the Dirac probability measure at
`0`. -/
theorem varianceWeightedRowLaw_tendsto_diracProba_zero_of_satisfiesLindebergCondition
    (h_lindeberg : A.SatisfiesLindebergCondition P) :
    letI : A.IsCentered P := h_lindeberg.toIsCentered
    Tendsto (fun n ↦ A.varianceWeightedRowLaw P n) atTop (𝓝 (diracProba (0 : ℝ))) := by
  letI : A.IsCentered P := h_lindeberg.toIsCentered
  -- Proof comment: the weighted-row laws are probability measures whose tails coincide with the
  -- Lindeberg truncated second-moment sums, so the generic tail criterion identifies the weak
  -- limit as `δ₀`.
  refine tendsto_diracProba_zero_of_tail_tendsto_zero ?_
  intro ε hε
  exact
    varianceWeightedRowLaw_tail_tendsto_zero_of_satisfiesLindebergCondition
      (A := A) (P := P) h_lindeberg hε

end

end RealRandomVariableArray
