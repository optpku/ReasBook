/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Example_8_12.Boundary
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

public section

noncomputable section

/-- Helper for Example 8.12: inner regularity of the codimension-`1` Euclidean
Hausdorff measure approximates `frontier E` from inside by compact subsets whose
mass exceeds any prescribed positive `EReal` lower bar. -/
lemma frontierHausdorffCompactExhaustion
    {d : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    {b : EReal}
    (hb :
      b ∈ Set.Ioo 0
        (((MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1))
          (frontier E) : EReal))) :
    ∃ K, K ⊆ frontier E ∧ IsCompact K ∧
      b <
        (((MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1))
          K : EReal)) := by
  let s : ℕ → Set (EuclideanSpace ℝ (Fin d)) :=
    fun n => frontier E ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) n
  have hs_mono : Monotone s := by
    intro m n hmn x hx
    refine ⟨hx.1, ?_⟩
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hmn) hx.2
  have hs_union : (⋃ n, s n) = frontier E := by
    -- Exhaust the closed frontier by nested closed balls centered at the origin.
    simpa [s] using
      (Metric.iUnion_inter_closedBall_nat (frontier E)
        (0 : EuclideanSpace ℝ (Fin d)))
  have hb_toENNReal :
      b.toENNReal <
        (MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) (frontier E) := by
    -- Translate the positive `EReal` threshold to the native `ENNReal` measure order.
    simpa [EReal.coe_toENNReal hb.1.le] using
      (EReal.toENNReal_lt_toENNReal hb.1.le hb.2)
  have hs_measure :
      (MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) (frontier E) =
        ⨆ n, (MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)) (s n) := by
    rw [← hs_union]
    exact hs_mono.measure_iUnion
  rw [hs_measure] at hb_toENNReal
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hb_toENNReal
  refine ⟨s n, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · -- Each stage of the exhaustion is compact as a closed subset of a compact closed ball.
    refine (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) n).of_isClosed_subset ?_ ?_
    · exact isClosed_frontier.inter Metric.isClosed_closedBall
    · intro x hx
      exact hx.2
  -- Convert the chosen closed-ball stage back to the `EReal` inequality expected downstream.
  rw [← EReal.coe_toENNReal hb.1.le]
  simpa using hn

/-- Helper for Example 8.12: after the compact-boundary lower bound is available
in the owned support scope, inner regularity upgrades it to the full frontier
measure. -/
lemma frontierMeasure_le_totalVariationIndicatorConst
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    {f₀ : ℝ}
    (hE_meas : MeasurableSet E)
    (hE_finite : VariationalRegularization.domainMeasure Ω E ≠ ⊤)
    (h_boundary : VariationalRegularization.HasC2BoundaryIn Ω E) :
    ((|f₀| : ℝ) : EReal) *
        ((MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1))
          (frontier E) : EReal) ≤
      VariationalRegularization.totalVariation
        (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) := by
  let tv :
      EReal :=
    VariationalRegularization.totalVariation
      (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀)
  let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) :=
    MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)
  by_cases hf₀ : f₀ = 0
  · -- The zero-amplitude datum gives the trivial lower bound `0 ≤ TV`.
    subst hf₀
    simpa [μ] using
      VariationalRegularization.HasC2BoundaryIn.totalVariation_nonneg
        (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite 0)
  have htv_nonneg : 0 ≤ tv := by
    -- The total variation side stays nonnegative throughout the compact exhaustion.
    simpa [tv] using
      VariationalRegularization.HasC2BoundaryIn.totalVariation_nonneg
        (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀)
  have hcompact :
      ∀ ⦃K : Set (EuclideanSpace ℝ (Fin d))⦄,
        IsCompact K →
        K ⊆ frontier E →
        ((|f₀| : ℝ) : EReal) * (μ K : EReal) ≤ tv := by
    intro K hK_compact hK_subset
    -- Route correction: the compact case is now delegated to the owned support theorem,
    -- so the target file only performs the compact-exhaustion assembly.
    simpa [tv, μ] using
      h_boundary.compactFrontierMeasure_le_totalVariationIndicatorConst
        (f₀ := f₀) (hE_meas := hE_meas) (hE_finite := hE_finite)
        hK_compact hK_subset
  have habs_nonneg : 0 ≤ ((|f₀| : ℝ) : EReal) := by
    exact_mod_cast abs_nonneg f₀
  have hfrontier_exhaust :
      ∀ ⦃b : EReal⦄,
        b ∈ Set.Ioo 0 (μ (frontier E) : EReal) →
        ∃ K, K ⊆ frontier E ∧ IsCompact K ∧ b < (μ K : EReal) := by
    intro b hb
    -- The target file now delegates the regularity step to a dedicated Hausdorff-measure helper.
    simpa [μ] using frontierHausdorffCompactExhaustion (d := d) (E := E) hb
  -- Once compact subsets with arbitrarily large boundary mass are available,
  -- the compact estimate upgrades to the full frontier by density of `EReal` multiplication.
  refine EReal.mul_le_of_forall_lt_of_nonneg habs_nonneg htv_nonneg ?_
  intro a ha b hb
  obtain ⟨K, hK_subset, hK_compact, hb_lt_compact⟩ := hfrontier_exhaust hb
  have hab_le : a ≤ ((|f₀| : ℝ) : EReal) := ha.2.le
  have hmul_le :
      a * b ≤ ((|f₀| : ℝ) : EReal) * (μ K : EReal) := by
    exact mul_le_mul hab_le hb_lt_compact.le hb.1.le habs_nonneg
  exact hmul_le.trans (hcompact hK_compact hK_subset)

/-- example_8_12. Example 8.12. Let `E ⊆ Ω ⊆ ℝ^d` with `2 ≤ d`, and assume that `frontier E`
is a `C²` boundary in `Ω` with the outward unit normal recorded by
`VariationalRegularization.HasC2BoundaryIn Ω E`. If `f` is the indicator datum
equal to `f₀` on `E` and `0` outside, then the Chapter 8 total variation of `f`
is `|f₀|` times the surface area of `frontier E`, expressed as the
codimension-`1` Euclidean Hausdorff measure in `EReal`. -/
theorem example_8_12
    {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {E : Set (EuclideanSpace ℝ (Fin d))}
    {f₀ : ℝ}
    (hd : 2 ≤ d)
    (hE_meas : MeasurableSet E)
    (hE_finite : VariationalRegularization.domainMeasure Ω E ≠ ⊤)
    (h_boundary : VariationalRegularization.HasC2BoundaryIn Ω E) :
    VariationalRegularization.totalVariation
        (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) =
      ((|f₀| : ℝ) : EReal) *
        ((MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1))
          (frontier E) : EReal) := by
  have _hd1 : 1 ≤ d := le_trans (by norm_num) hd
  let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) :=
    MeasureTheory.Measure.euclideanHausdorffMeasure (d - 1)
  have h_upper :
      VariationalRegularization.totalVariation
          (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) ≤
        ((|f₀| : ℝ) : EReal) * (μ (frontier E) : EReal) := by
    -- The already packaged boundary estimate gives the global upper bound.
    refine VariationalRegularization.totalVariation_le_of_forall_admissibleDivergencePairing_le _ ?_
    intro v
    simpa [μ] using
      VariationalRegularization.indicatorConst_pairing_le_surfaceArea_of_boundaryFormula
        h_boundary hE_meas hE_finite v
  have h_lower :
      ((|f₀| : ℝ) : EReal) * (μ (frontier E) : EReal) ≤
        VariationalRegularization.totalVariation
          (MeasureTheory.indicatorConstLp 1 hE_meas hE_finite f₀) := by
    -- Reduce the main theorem to the named compact-exhaustion lower bound helper.
    simpa [μ] using
      frontierMeasure_le_totalVariationIndicatorConst hE_meas hE_finite h_boundary
  exact le_antisymm h_upper h_lower
