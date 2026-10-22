/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology BigOperators

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable section

section PseudoMetric

variable {E : Type v} [PseudoMetricSpace E]

/-- The weighted truncated integral distance attached to a measurable exhaustion `(A n)` of the
underlying measure space. -/
def measureExhaustionDist (μ : Measure Ω) (A : ℕ → Set Ω) (f g : Ω →ₘ[μ] E) : ℝ :=
  ∑' n,
    (((1 / 2 : ℝ) ^ (n + 1)) / (1 + (μ (A n)).toReal)) *
      ∫ ω in A n, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ

/-- The exhaustion distance is nonnegative. -/
theorem measureExhaustionDist_nonneg
    (μ : Measure Ω) (A : ℕ → Set Ω) (f g : Ω →ₘ[μ] E) :
    0 ≤ measureExhaustionDist μ A f g := by
  -- Each weighted truncated integral is nonnegative, so the whole series is nonnegative.
  refine tsum_nonneg fun n ↦ by positivity

/-- The exhaustion distance from a point to itself vanishes. -/
@[simp] theorem measureExhaustionDist_self
    (μ : Measure Ω) (A : ℕ → Set Ω) (f : Ω →ₘ[μ] E) :
    measureExhaustionDist μ A f f = 0 := by
  -- Every truncated integrand vanishes pointwise when the two arguments agree.
  simp [measureExhaustionDist]

/-- The exhaustion distance is symmetric. -/
theorem measureExhaustionDist_comm
    (μ : Measure Ω) (A : ℕ → Set Ω) (f g : Ω →ₘ[μ] E) :
    measureExhaustionDist μ A f g = measureExhaustionDist μ A g f := by
  -- Symmetry is inherited from the ambient metric inside each summand.
  simp [measureExhaustionDist, dist_comm]

end PseudoMetric

section Metric

variable {E : Type v} [MetricSpace E]

/-- Helper for Theorem 6.7: on a finite restricted measure, the truncated distance is integrable
because it is bounded by the integrable constant `1`. -/
lemma truncated_dist_integrable_restrict_of_finiteMeasure
    (s : Set Ω) (hs_finite : μ s < ∞) (f g : Ω →ₘ[μ] E) :
    Integrable (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (μ.restrict s) := by
  haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs_finite.ne
  have h_meas :
      AEStronglyMeasurable (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (μ.restrict s) := by
    -- The restricted integrand is still a.e.-strongly measurable after passing to the distance
    -- and truncating by the measurable map `x ↦ min 1 x`.
    exact
      (aemeasurable_const.min
        ((f.aestronglyMeasurable.restrict).dist
          (g.aestronglyMeasurable.restrict)).aemeasurable).aestronglyMeasurable
  -- The pointwise bound `min 1 (dist ...) ≤ 1` transfers integrability from the constant
  -- function on the finite restricted measure.
  refine Integrable.mono' (integrable_const (1 : ℝ)) h_meas ?_
  filter_upwards with ω
  have h_nonneg : 0 ≤ min (1 : ℝ) (dist (f ω) (g ω)) := by
    positivity
  have h_le : min (1 : ℝ) (dist (f ω) (g ω)) ≤ 1 := min_le_left _ _
  simp [Real.norm_of_nonneg h_nonneg, h_le]

/-- Helper for Theorem 6.7: the truncated distance integrand on one exhaustion piece is
integrable because it is bounded by `1` on a finite-measure set. -/
lemma truncated_piece_integrable
    (A : ℕ → Set Ω) (hA_finite : ∀ n, μ (A n) < ∞)
    (N : ℕ) (f g : Ω →ₘ[μ] E) :
    IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (A N) μ := by
  -- The set integral is just the restricted integral on `μ.restrict (A N)`.
  simpa [IntegrableOn] using
    truncated_dist_integrable_restrict_of_finiteMeasure (A N) (hA_finite N) f g

/-- Helper for Theorem 6.7: the `N`-th weighted truncated integral is bounded by the geometric
weight `2 ^ -(N+1)`. -/
lemma weighted_truncated_piece_le_geometric
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_finite : ∀ n, μ (A n) < ∞)
    (N : ℕ) (f g : Ω →ₘ[μ] E) :
    (((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal)) *
        ∫ ω in A N, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ
      ≤ ((1 / 2 : ℝ) ^ (N + 1)) := by
  have h_int :
      IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (A N) μ :=
    truncated_piece_integrable A hA_finite N f g
  have h_int_le :
      ∫ ω in A N, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ ≤ μ.real (A N) := by
    -- On `A N`, the truncated distance is bounded above by the constant function `1`.
    simpa using
      setIntegral_mono_on h_int
        (integrableOn_const (hA_finite N).ne)
        (hA_meas N) (fun ω hω ↦ min_le_left _ _)
  have hfrac_le_one : (μ (A N)).toReal / (1 + (μ (A N)).toReal) ≤ (1 : ℝ) := by
    have hden_pos : 0 < 1 + (μ (A N)).toReal := by
      positivity
    have hdiv_nonneg : 0 ≤ 1 / (1 + (μ (A N)).toReal) := by
      positivity
    -- The normalizing factor is at most `1`.
    calc
      (μ (A N)).toReal / (1 + (μ (A N)).toReal)
          = 1 - 1 / (1 + (μ (A N)).toReal) := by
              field_simp [hden_pos.ne']
              ring
      _ ≤ 1 := by
            linarith
  calc
    (((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal)) *
        ∫ ω in A N, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ
      ≤ (((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal)) * μ.real (A N) := by
          gcongr
    _ = ((1 / 2 : ℝ) ^ (N + 1)) * ((μ (A N)).toReal / (1 + (μ (A N)).toReal)) := by
          rw [measureReal_def]
          ring_nf
    _ ≤ ((1 / 2 : ℝ) ^ (N + 1)) * 1 := by
          gcongr
    _ = ((1 / 2 : ℝ) ^ (N + 1)) := by
          ring

/-- Helper for Theorem 6.7: the weighted truncated-distance series is summable on a
finite-measure exhaustion. -/
lemma measureExhaustionDist_summable
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_finite : ∀ n, μ (A n) < ∞)
    (f g : Ω →ₘ[μ] E) :
    Summable
      (fun n ↦
        (((1 / 2 : ℝ) ^ (n + 1)) / (1 + (μ (A n)).toReal)) *
          ∫ ω in A n, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ) := by
  have hgeom :
      Summable (fun n ↦ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n)) :=
    (summable_geometric_of_abs_lt_one (show |(1 / 2 : ℝ)| < 1 by norm_num)).mul_left (1 / 2)
  -- The defining series is dominated by the summable geometric series `∑ (1 / 2)^(n+1)`.
  refine Summable.of_nonneg_of_le
    (fun n ↦ by positivity) (fun n ↦ ?_) hgeom
  · simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      weighted_truncated_piece_le_geometric A hA_meas hA_finite n f g

/-- Helper for Theorem 6.7: a single weighted truncation term is bounded above by the full
exhaustion distance. -/
lemma measureExhaustionDist_piece_le
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_finite : ∀ n, μ (A n) < ∞)
    (N : ℕ) (f g : Ω →ₘ[μ] E) :
    (((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal)) *
        ∫ ω in A N, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ
      ≤ measureExhaustionDist μ A f g := by
  have hsum := measureExhaustionDist_summable A hA_meas hA_finite f g
  -- A nonnegative summand is bounded by the sum of the whole nonnegative series.
  simpa [measureExhaustionDist] using
    hsum.le_tsum N (fun j hj ↦ by positivity)

/-- Helper for Theorem 6.7: equality almost everywhere on every exhaustion piece globalizes to
equality in `AEEqFun`. -/
lemma ae_eq_of_restrict_ae_on_exhaustion
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_univ : (⋃ n, A n) = Set.univ)
    {f g : Ω →ₘ[μ] E}
    (hfg : ∀ n, f =ᵐ[μ.restrict (A n)] g) :
    f = g := by
  -- The disagreement set is null on every exhaustion piece, hence null globally.
  let C : Set (Set Ω) := Set.range A
  have hspan : IsCountablySpanning C := by
    refine ⟨A, ?_, ?_⟩
    · intro n
      exact Set.mem_range_self n
    · simpa [C] using hA_univ
  have hnull :
      μ {ω | f ω ≠ g ω} = 0 := by
    refine hspan.null_of_forall_restrict_null ?_ ?_
    · rintro t ⟨n, rfl⟩
      exact hA_meas n
    · rintro t ⟨n, rfl⟩
      simpa [ae_iff] using hfg n
  -- Conclude by extensionality of almost-everywhere classes.
  exact AEEqFun.ext <| by
    simpa [ae_iff] using hnull

/-- Helper for Theorem 6.7: the truncated distance on one exhaustion piece is subadditive. -/
lemma truncated_dist_triangle
    (x y z : E) :
    min (1 : ℝ) (dist x z) ≤ min (1 : ℝ) (dist x y) + min (1 : ℝ) (dist y z) := by
  have hxy_nonneg : 0 ≤ dist x y := dist_nonneg
  have hyz_nonneg : 0 ≤ dist y z := dist_nonneg
  calc
    min (1 : ℝ) (dist x z) ≤ min (1 : ℝ) (dist x y + dist y z) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ min (1 : ℝ) (dist x y) + min (1 : ℝ) (dist y z) := by
      by_cases hxy : dist x y ≤ 1
      · by_cases hyz : dist y z ≤ 1
        · rw [min_eq_right hxy, min_eq_right hyz]
          by_cases hsum : dist x y + dist y z ≤ 1
          · simp [min_eq_right hsum]
          · have hsum' : 1 ≤ dist x y + dist y z := le_of_not_ge hsum
            rw [min_eq_left hsum']
            linarith
        · have hyz' : 1 ≤ dist y z := le_of_not_ge hyz
          rw [min_eq_left hyz']
          have hleft : min (1 : ℝ) (dist x y + dist y z) ≤ 1 := min_le_left _ _
          have hright : 0 ≤ min (1 : ℝ) (dist x y) := le_min zero_le_one hxy_nonneg
          linarith
      · have hxy' : 1 ≤ dist x y := le_of_not_ge hxy
        rw [min_eq_left hxy']
        have hleft : min (1 : ℝ) (dist x y + dist y z) ≤ 1 := min_le_left _ _
        have hright : 0 ≤ min (1 : ℝ) (dist y z) := le_min zero_le_one hyz_nonneg
        linarith

/-- Helper for Theorem 6.7: the fixed-piece truncated integral is controlled by the deviation
measure plus the small constant term from the textbook estimate. -/
lemma truncated_piece_integral_le_deviation_add
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_finite : ∀ n, μ (A n) < ∞)
    (N : ℕ) {f g : Ω →ₘ[μ] E} {ε : ℝ} (hε_pos : 0 < ε) :
    ∫ ω in A N, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ
      ≤ (μ.restrict (A N)).real {ω | ε ≤ dist (f ω) (g ω)} + ε * μ.real (A N) := by
  let dev : Set Ω := {ω | ε ≤ dist (f ω) (g ω)}
  have h_int :
      IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (A N) μ :=
    truncated_piece_integrable A hA_finite N f g
  have h_dev_null : NullMeasurableSet dev μ := by
    -- The deviation set is null measurable because the distance is a.e.-measurable.
    simpa [dev] using
      ((f.aestronglyMeasurable.dist g.aestronglyMeasurable).aemeasurable.nullMeasurableSet_preimage
        measurableSet_Ici)
  have h_split := integral_inter_add_diff₀ h_dev_null h_int
  have h_int_inter :
      IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (A N ∩ dev) μ :=
    h_int.mono_set (by
      intro ω hω
      exact hω.1)
  have h_int_diff :
      IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (A N \ dev) μ :=
    h_int.mono_set (by
      intro ω hω
      exact hω.1)
  have h_inter_le :
      ∫ ω in A N ∩ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ ≤ μ.real (A N ∩ dev) := by
    -- On the deviation set, the truncation is still bounded above by `1`.
    calc
      ∫ ω in A N ∩ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ
        ≤ ∫ ω in A N ∩ dev, (1 : ℝ) ∂μ := by
            exact
              setIntegral_mono_on₀ h_int_inter
                (integrableOn_const
                  ((measure_mono (by
                    intro ω hω
                    exact hω.1)).trans_lt (hA_finite N)).ne)
                ((hA_meas N).nullMeasurableSet.inter h_dev_null)
                (fun ω hω ↦ min_le_left _ _)
      _ = μ.real (A N ∩ dev) := by
            rw [setIntegral_one_eq_measureReal]
  have h_diff_le :
      ∫ ω in A N \ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ ≤ ε * μ.real (A N) := by
    have h_aux :
        ∫ ω in A N \ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ ≤
          ∫ ω in A N \ dev, ε ∂μ := by
      -- Outside the deviation set we have `dist < ε`, hence also `min 1 dist ≤ ε`.
      exact
        setIntegral_mono_on₀ h_int_diff
          (integrableOn_const
            ((measure_mono (by
              intro ω hω
              exact hω.1)).trans_lt (hA_finite N)).ne)
          ((hA_meas N).nullMeasurableSet.diff h_dev_null)
          (fun ω hω ↦ by
            have hω_not : ω ∉ dev := hω.2
            have hdist_lt : dist (f ω) (g ω) < ε := by
              exact lt_of_not_ge hω_not
            calc
              min (1 : ℝ) (dist (f ω) (g ω)) ≤ dist (f ω) (g ω) := min_le_right _ _
              _ ≤ ε := le_of_lt hdist_lt)
    calc
      ∫ ω in A N \ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ
        ≤ ∫ ω in A N \ dev, ε ∂μ := h_aux
      _ = ε * μ.real (A N \ dev) := by
            rw [setIntegral_const]
            simp [smul_eq_mul, mul_comm]
      _ ≤ ε * μ.real (A N) := by
            have hmono : μ.real (A N \ dev) ≤ μ.real (A N) := by
              exact measureReal_mono (by
                rintro ω ⟨hωA, hωdev⟩
                exact hωA) (hA_finite N).ne
            exact mul_le_mul_of_nonneg_left hmono (le_of_lt hε_pos)
  have h_dev_null_restrict : NullMeasurableSet dev (μ.restrict (A N)) := by
    exact h_dev_null.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have h_dev_real :
      μ.real (A N ∩ dev) = (μ.restrict (A N)).real dev := by
    simpa [Set.inter_comm] using (measureReal_restrict_apply₀ h_dev_null_restrict).symm
  -- Split the integral into the deviation part and its complement, then apply the two bounds.
  calc
    ∫ ω in A N, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ
      =
        ∫ ω in A N ∩ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ +
          ∫ ω in A N \ dev, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ := by
            symm
            exact h_split
    _ ≤ μ.real (A N ∩ dev) + ε * μ.real (A N) := add_le_add h_inter_le h_diff_le
    _ = (μ.restrict (A N)).real dev + ε * μ.real (A N) := by
          rw [h_dev_real]
    _ = (μ.restrict (A N)).real {ω | ε ≤ dist (f ω) (g ω)} + ε * μ.real (A N) := by
          rfl

/-- Helper for Theorem 6.7: the deviation measure on one finite-measure exhaustion piece is
controlled by the truncated distance integral. -/
lemma deviation_measureReal_le_truncated_piece_integral
    (A : ℕ → Set Ω) (hA_finite : ∀ n, μ (A n) < ∞)
    (N : ℕ) {f g : Ω →ₘ[μ] E} {ε : ℝ} (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    (μ.restrict (A N)).real {ω | ε ≤ dist (f ω) (g ω)}
      ≤ ε⁻¹ * ∫ ω in A N, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ := by
  have h_int :
      IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (A N) μ :=
    truncated_piece_integrable A hA_finite N f g
  have h_nonneg :
      0 ≤ᵐ[μ.restrict (A N)] fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω)) := by
    filter_upwards with ω
    positivity
  have h_markov :=
    mul_meas_ge_le_integral_of_nonneg h_nonneg
      (by simpa [IntegrableOn] using h_int) ε
  have hε_inv_nonneg : 0 ≤ ε⁻¹ := by
    positivity
  have hset :
      {ω | ε ≤ 1 ∧ ε ≤ dist (f ω) (g ω)} = {ω | ε ≤ dist (f ω) (g ω)} := by
    ext ω
    simp [hε_le]
  -- This is exactly the restricted-measure Markov inequality for the truncated distance.
  by_cases hε_zero : ε = 0
  · exact (hε_pos.ne' hε_zero).elim
  have hε_ne : ε ≠ 0 := hε_zero
  have hε_mul :
      ε * (μ.restrict (A N)).real {ω | ε ≤ dist (f ω) (g ω)}
        ≤ ∫ ω in A N, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ := by
    simpa [IntegrableOn, hset] using h_markov
  have := mul_le_mul_of_nonneg_left hε_mul hε_inv_nonneg
  simpa [hε_ne, mul_comm, mul_left_comm, mul_assoc] using this

/-- For a measurable family of finite-measure sets, the exhaustion distance satisfies the
triangle inequality. -/
theorem measureExhaustionDist_triangle
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_finite : ∀ n, μ (A n) < ∞)
    (f g h : Ω →ₘ[μ] E) :
    measureExhaustionDist μ A f h ≤
      measureExhaustionDist μ A f g + measureExhaustionDist μ A g h := by
  let lhs : ℕ → ℝ := fun n ↦
    (((1 / 2 : ℝ) ^ (n + 1)) / (1 + (μ (A n)).toReal)) *
      ∫ ω in A n, min (1 : ℝ) (dist (f ω) (h ω)) ∂μ
  let rhs₁ : ℕ → ℝ := fun n ↦
    (((1 / 2 : ℝ) ^ (n + 1)) / (1 + (μ (A n)).toReal)) *
      ∫ ω in A n, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ
  let rhs₂ : ℕ → ℝ := fun n ↦
    (((1 / 2 : ℝ) ^ (n + 1)) / (1 + (μ (A n)).toReal)) *
      ∫ ω in A n, min (1 : ℝ) (dist (g ω) (h ω)) ∂μ
  have hsum_lhs : Summable lhs :=
    measureExhaustionDist_summable A hA_meas hA_finite f h
  have hsum_rhs₁ : Summable rhs₁ :=
    measureExhaustionDist_summable A hA_meas hA_finite f g
  have hsum_rhs₂ : Summable rhs₂ :=
    measureExhaustionDist_summable A hA_meas hA_finite g h
  have hterm :
      ∀ n, lhs n ≤ rhs₁ n + rhs₂ n := by
    intro n
    have h_int_lhs :
        IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (h ω))) (A n) μ :=
      truncated_piece_integrable A hA_finite n f h
    have h_int_rhs :
        IntegrableOn
          (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω)) + min (1 : ℝ) (dist (g ω) (h ω)))
          (A n) μ := by
      exact
        (truncated_piece_integrable A hA_finite n f g).add
          (truncated_piece_integrable A hA_finite n g h)
    have h_piece :
        ∫ ω in A n, min (1 : ℝ) (dist (f ω) (h ω)) ∂μ
          ≤ ∫ ω in A n,
              (min (1 : ℝ) (dist (f ω) (g ω)) + min (1 : ℝ) (dist (g ω) (h ω))) ∂μ := by
      -- The pointwise triangle inequality for the truncated distance integrates on each piece.
      exact
        setIntegral_mono_on h_int_lhs h_int_rhs (hA_meas n)
          (fun ω hω ↦ truncated_dist_triangle (f ω) (g ω) (h ω))
    have hweight_nonneg :
        0 ≤ (((1 / 2 : ℝ) ^ (n + 1)) / (1 + (μ (A n)).toReal)) := by
      positivity
    have h_int_fg :
        Integrable (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (μ.restrict (A n)) := by
      simpa [IntegrableOn] using truncated_piece_integrable A hA_finite n f g
    have h_int_gh :
        Integrable (fun ω ↦ min (1 : ℝ) (dist (g ω) (h ω))) (μ.restrict (A n)) := by
      simpa [IntegrableOn] using truncated_piece_integrable A hA_finite n g h
    have h_add :
        ∫ ω in A n,
            (min (1 : ℝ) (dist (f ω) (g ω)) + min (1 : ℝ) (dist (g ω) (h ω))) ∂μ
          =
            ∫ ω in A n, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ +
              ∫ ω in A n, min (1 : ℝ) (dist (g ω) (h ω)) ∂μ := by
      simpa [IntegrableOn] using integral_add h_int_fg h_int_gh
    calc
      lhs n
        ≤ (((1 / 2 : ℝ) ^ (n + 1)) / (1 + (μ (A n)).toReal)) *
            ∫ ω in A n,
              (min (1 : ℝ) (dist (f ω) (g ω)) + min (1 : ℝ) (dist (g ω) (h ω))) ∂μ := by
              exact mul_le_mul_of_nonneg_left h_piece hweight_nonneg
      _ = rhs₁ n + rhs₂ n := by
            rw [h_add]
            ring
  -- Summing the termwise estimate gives the global triangle inequality.
  calc
    measureExhaustionDist μ A f h = ∑' n, lhs n := by
      rfl
    _ ≤ ∑' n, (rhs₁ n + rhs₂ n) := by
          exact Summable.tsum_le_tsum hterm hsum_lhs (hsum_rhs₁.add hsum_rhs₂)
    _ = (∑' n, rhs₁ n) + ∑' n, rhs₂ n := by
          exact hsum_rhs₁.tsum_add hsum_rhs₂
    _ = measureExhaustionDist μ A f g + measureExhaustionDist μ A g h := by
          rfl

/-- For a measurable exhaustion by finite-measure sets, the exhaustion distance separates
almost-everywhere classes. -/
theorem measureExhaustionDist_eq_zero_iff
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_univ : (⋃ n, A n) = Set.univ)
    (hA_finite : ∀ n, μ (A n) < ∞)
    {f g : Ω →ₘ[μ] E} :
    measureExhaustionDist μ A f g = 0 ↔ f = g := by
  refine ⟨fun hdist ↦ ?_, fun hfg ↦ by simp [hfg]⟩
  have h_restrict :
      ∀ n, f =ᵐ[μ.restrict (A n)] g := by
    intro n
    let piece : ℝ :=
      (((1 / 2 : ℝ) ^ (n + 1)) / (1 + (μ (A n)).toReal)) *
        ∫ ω in A n, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ
    have hpiece_le :
        piece ≤ 0 := by
      -- Each summand is bounded above by the full distance, which is `0` by hypothesis.
      simpa [piece, hdist] using
        measureExhaustionDist_piece_le A hA_meas hA_finite n f g
    have hpiece_nonneg : 0 ≤ piece := by
      -- Every summand is nonnegative because the weight and the integral are nonnegative.
      unfold piece
      positivity
    have hpiece_eq : piece = 0 := le_antisymm hpiece_le hpiece_nonneg
    have hweight_pos :
        0 < (((1 / 2 : ℝ) ^ (n + 1)) / (1 + (μ (A n)).toReal)) := by
      positivity
    have h_integral_eq :
        ∫ ω in A n, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ = 0 := by
      unfold piece at hpiece_eq
      nlinarith
    have h_nonneg :
        0 ≤ᵐ[μ.restrict (A n)] fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω)) := by
      filter_upwards with ω
      positivity
    have h_int :
        IntegrableOn (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) (A n) μ :=
      truncated_piece_integrable A hA_finite n f g
    have h_zero_ae :
        (fun ω ↦ min (1 : ℝ) (dist (f ω) (g ω))) =ᶠ[ae (μ.restrict (A n))] 0 := by
      -- A nonnegative integrable function with zero integral vanishes a.e.
      exact (setIntegral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).mp h_integral_eq
    -- Vanishing truncated distance means the actual distance vanishes, hence the functions agree.
    filter_upwards [h_zero_ae] with ω hω
    by_cases hdist_zero : dist (f ω) (g ω) = 0
    · exact dist_eq_zero.mp hdist_zero
    · have hdist_pos : 0 < dist (f ω) (g ω) := by
        exact lt_of_le_of_ne dist_nonneg (by simpa [eq_comm] using hdist_zero)
      have hmin_pos : 0 < min (1 : ℝ) (dist (f ω) (g ω)) := by
        by_cases hle : dist (f ω) (g ω) ≤ 1
        · simpa [min_eq_right hle] using hdist_pos
        · have hone_le : 1 ≤ dist (f ω) (g ω) := le_of_not_ge hle
          have : min (1 : ℝ) (dist (f ω) (g ω)) = 1 := by
            simp [min_eq_left hone_le]
          linarith [show (0 : ℝ) < 1 by norm_num]
      have hzero : min (1 : ℝ) (dist (f ω) (g ω)) = 0 := by
        simpa using hω
      linarith
  exact ae_eq_of_restrict_ae_on_exhaustion A hA_meas hA_univ h_restrict

-- Proof sketch: prove that each summand defines a bounded pseudometric on `Ω →ₘ[μ] E`, sum these
-- pseudometrics with the absolutely summable positive weights `2^{-(n+1)} / (1 + μ(A n))`, and
-- use the exhaustion `⋃ n, A n = Ω` together with the separation of `E` to show that vanishing
-- distance forces equality in `AEEqFun`, i.e. equality almost everywhere.
/-- Theorem 6.7 (1): For a measurable cover `(A n)` of `Ω` by finite-measure sets, the weighted
truncated integral distance defines a metric on the almost-everywhere function space `Ω →ₘ[μ] E`.
This is a named metric structure, since different covers can induce different metrics on the same
type. -/
@[reducible] noncomputable def measureExhaustionMetricSpace
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_univ : (⋃ n, A n) = Set.univ)
    (hA_finite : ∀ n, μ (A n) < ∞) :
    MetricSpace (Ω →ₘ[μ] E) where
  dist := measureExhaustionDist μ A
  dist_self := measureExhaustionDist_self μ A
  dist_comm := measureExhaustionDist_comm μ A
  dist_triangle := measureExhaustionDist_triangle A hA_meas hA_finite
  eq_of_dist_eq_zero := fun hfg ↦ (measureExhaustionDist_eq_zero_iff
    A hA_meas hA_univ hA_finite).mp hfg

/-- Helper for Theorem 6.7: after the first `K` exhaustion pieces, the remaining series is
uniformly bounded by the geometric tail `2^{-K}`. -/
private lemma measureExhaustionDist_le_sum_range_add_geometric_tail
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_finite : ∀ n, μ (A n) < ∞)
    (K : ℕ) (f g : Ω →ₘ[μ] E) :
    measureExhaustionDist μ A f g ≤
      (Finset.sum (Finset.range K) fun i ↦
        (((1 / 2 : ℝ) ^ (i + 1)) / (1 + (μ (A i)).toReal)) *
          ∫ ω in A i, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ) +
        (1 / 2 : ℝ) ^ K := by
  let term : ℕ → ℝ := fun n ↦
    (((1 / 2 : ℝ) ^ (n + 1)) / (1 + (μ (A n)).toReal)) *
      ∫ ω in A n, min (1 : ℝ) (dist (f ω) (g ω)) ∂μ
  have hsum : Summable term :=
    measureExhaustionDist_summable A hA_meas hA_finite f g
  have hsum_tail : Summable (fun n ↦ term (n + K)) := by
    simpa using (summable_nat_add_iff K).2 hsum
  have hgeom : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (show |(1 / 2 : ℝ)| < 1 by norm_num)
  have hgeom_tail_sum :
      (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + K + 1)) = (1 / 2 : ℝ) ^ K := by
    have hgeom_one :
        (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1)) = 1 := by
      have hsplit := hgeom.sum_add_tsum_nat_add 1
      have htwo : (∑' n : ℕ, (1 / 2 : ℝ) ^ n) = 2 := by
        simpa using (tsum_geometric_two : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = 2)
      rw [htwo] at hsplit
      norm_num at hsplit
      linarith
    -- Factor out the first `K` geometric weights from the tail.
    calc
      ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + K + 1)
        = ∑' n : ℕ, ((1 / 2 : ℝ) ^ K) * ((1 / 2 : ℝ) ^ (n + 1)) := by
            congr with n
            simp [pow_add, add_assoc, add_comm, mul_left_comm, mul_comm]
      _ = ((1 / 2 : ℝ) ^ K) * ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) := by
            rw [tsum_mul_left]
      _ = (1 / 2 : ℝ) ^ K := by
            rw [hgeom_one, mul_one]
  have hterm_tail :
      ∀ n, term (n + K) ≤ (1 / 2 : ℝ) ^ (n + K + 1) := by
    intro n
    simpa [term, add_assoc] using
      weighted_truncated_piece_le_geometric A hA_meas hA_finite (n + K) f g
  have htail_le :
      ∑' n : ℕ, term (n + K) ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + K + 1) := by
    have hgeom_tail : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + K + 1)) := by
      simpa [add_assoc] using (summable_nat_add_iff (K + 1)).2 hgeom
    exact Summable.tsum_le_tsum hterm_tail hsum_tail hgeom_tail
  -- Split the series into a finite head and a geometric tail.
  calc
    measureExhaustionDist μ A f g
      = Finset.sum (Finset.range K) term + ∑' n : ℕ, term (n + K) := by
          simpa [measureExhaustionDist, term] using (hsum.sum_add_tsum_nat_add K).symm
    _ ≤ Finset.sum (Finset.range K) term + ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + K + 1) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left htail_le (Finset.sum (Finset.range K) term)
    _ = Finset.sum (Finset.range K) term + (1 / 2 : ℝ) ^ K := by
          rw [hgeom_tail_sum]

/-- Helper for Theorem 6.7: on a fixed finite exhaustion piece, local convergence in measure
forces the corresponding weighted truncation term to tend to `0`. -/
private lemma weighted_truncated_piece_tendsto_zero_of_tendstoInMeasure
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_finite : ∀ n, μ (A n) < ∞)
    (N : ℕ) {fSeq : ℕ → Ω →ₘ[μ] E} {f : Ω →ₘ[μ] E}
    (h_local : TendstoInMeasure (μ.restrict (A N)) (fun n ω ↦ fSeq n ω) atTop f) :
    Tendsto
      (fun n ↦
        (((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal)) *
          ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ)
      atTop (𝓝 0) := by
  letI : IsFiniteMeasure (μ.restrict (A N)) := isFiniteMeasure_restrict.2 (hA_finite N).ne
  have h_local_real := (tendstoInMeasure_iff_measureReal_dist.1 h_local)
  refine Metric.tendsto_atTop.2 ?_
  intro δ hδ
  let weight : ℝ := (((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal))
  let mass : ℝ := μ.real (A N)
  let η : ℝ := min (1 / 2 : ℝ) (δ / (2 * (weight * mass + 1)))
  have hweight_nonneg : 0 ≤ weight := by
    positivity
  have hweight_pos : 0 < weight := by
    positivity
  have hmass_nonneg : 0 ≤ mass := by
    exact measureReal_nonneg
  have hη_pos : 0 < η := by
    unfold η
    refine lt_min ?_ ?_
    · norm_num
    · positivity
  have hη_le : η ≤ 1 := by
    unfold η
    calc
      min (1 / 2 : ℝ) (δ / (2 * (weight * mass + 1))) ≤ 1 / 2 := min_le_left _ _
      _ ≤ 1 := by norm_num
  have hη_error_le : weight * (η * mass) ≤ δ / 2 := by
    have hmass_le : weight * mass ≤ weight * mass + 1 := by linarith
    have hη_upper : η ≤ δ / (2 * (weight * mass + 1)) := by
      unfold η
      exact min_le_right _ _
    calc
      weight * (η * mass) = η * (weight * mass) := by ring
      _ ≤ η * (weight * mass + 1) := by
            gcongr
      _ ≤ (δ / (2 * (weight * mass + 1))) * (weight * mass + 1) := by
            gcongr
      _ = δ / 2 := by
            field_simp
  have h_scaled_dev :
      Tendsto
        (fun n ↦ weight * (μ.restrict (A N)).real {ω | η ≤ dist (fSeq n ω) (f ω)})
        atTop (𝓝 0) := by
    simpa using (h_local_real η hη_pos).const_mul weight
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 h_scaled_dev) (δ / 2) (by linarith)
  refine ⟨M, fun n hn ↦ ?_⟩
  have h_piece :
      weight *
          ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ
        ≤
          weight * (μ.restrict (A N)).real {ω | η ≤ dist (fSeq n ω) (f ω)} +
            weight * (η * μ.real (A N)) := by
    -- Apply the textbook one-piece estimate and multiply by the fixed positive weight.
    have h_bound :
        ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ
          ≤ (μ.restrict (A N)).real {ω | η ≤ dist (fSeq n ω) (f ω)} + η * μ.real (A N) :=
      truncated_piece_integral_le_deviation_add A hA_meas hA_finite N hη_pos
    have := mul_le_mul_of_nonneg_left h_bound hweight_nonneg
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using this
  have h_head : weight * (μ.restrict (A N)).real {ω | η ≤ dist (fSeq n ω) (f ω)} < δ / 2 :=
    by
      have h_head_dist :
          dist (weight * (μ.restrict (A N)).real {ω | η ≤ dist (fSeq n ω) (f ω)}) 0 < δ / 2 :=
        hM n hn
      have h_nonneg_scaled :
          0 ≤ weight * (μ.restrict (A N)).real {ω | η ≤ dist (fSeq n ω) (f ω)} := by
        positivity
      rw [Real.dist_eq] at h_head_dist
      simpa [abs_of_nonneg h_nonneg_scaled] using h_head_dist
  have h_nonneg :
      0 ≤
        weight *
          ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ := by
    positivity
  -- The deviation contribution is eventually small, and the deterministic error is already small.
  have h_lt :
      weight * ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ < δ := by
    calc
      weight * ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ
        ≤
          weight * (μ.restrict (A N)).real {ω | η ≤ dist (fSeq n ω) (f ω)} +
            weight * (η * μ.real (A N)) := h_piece
      _ < δ / 2 + δ / 2 := add_lt_add_of_lt_of_le h_head hη_error_le
      _ = δ := by ring
  rw [Real.dist_eq]
  have h_term_nonneg :
      0 ≤
        (((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal)) *
          ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ := by
    positivity
  have h_abs :
      |((((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal)) *
          ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ) - 0|
        =
          (((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal)) *
            ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ := by
    have h_weight_nonneg_explicit :
        0 ≤ (((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal)) := by
      positivity
    have h_int_nonneg :
        0 ≤ ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ := by
      positivity
    rw [sub_zero, abs_mul, abs_of_nonneg h_weight_nonneg_explicit, abs_of_nonneg h_int_nonneg]
  rw [h_abs]
  simpa [weight] using h_lt

/-- Helper for Theorem 6.7: every finite-measure measurable set is approximated in real measure
by a sufficiently large exhaustion piece. -/
private lemma exists_exhaustion_piece_diff_lt_of_finiteMeasure
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_mono : Monotone A) (hA_univ : (⋃ n, A n) = Set.univ)
    {B : Set Ω} (hB_finite : μ B < ∞)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, μ.real (B \ A N) < δ := by
  let s : ℕ → Set Ω := fun n ↦ B ∩ A n
  have hs_mono : Monotone s := by
    intro m n hmn ω hω
    exact ⟨hω.1, hA_mono hmn hω.2⟩
  have hs_union : (⋃ n, s n) = B := by
    ext ω
    constructor
    · intro hω
      exact (Set.mem_iUnion.mp hω).choose_spec.1
    · intro hωB
      have hω_univ : ω ∈ ⋃ n, A n := by simp [hA_univ]
      rcases Set.mem_iUnion.mp hω_univ with ⟨N, hωN⟩
      exact Set.mem_iUnion.2 ⟨N, ⟨hωB, hωN⟩⟩
  have hs_tendsto : Tendsto (fun n ↦ μ.real (s n)) atTop (𝓝 (μ.real B)) := by
    have hμ_tendsto : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n, s n))) :=
      tendsto_measure_iUnion_atTop hs_mono
    rw [hs_union] at hμ_tendsto
    change Tendsto (fun n ↦ μ (s n)) atTop (𝓝 (μ B)) at hμ_tendsto
    rw [← ENNReal.tendsto_toReal_iff
      (fun n ↦ ne_top_of_le_ne_top hB_finite.ne (measure_mono (show s n ⊆ B by
        intro ω hω
        exact hω.1)))
      hB_finite.ne] at hμ_tendsto
    simpa [s] using hμ_tendsto
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hs_tendsto) δ hδ
  refine ⟨N, ?_⟩
  have hdist : dist (μ.real (s N)) (μ.real B) < δ := hN N le_rfl
  have hs_le : μ.real (s N) ≤ μ.real B := by
    exact measureReal_mono (show s N ⊆ B by
      intro ω hω
      exact hω.1) hB_finite.ne
  have hdiff_eq : μ.real (B \ A N) = μ.real B - μ.real (s N) := by
    have hsum := measureReal_inter_add_diff (hA_meas N) hB_finite.ne
    linarith
  -- Since `B ∩ A N ⊆ B`, the distance to the limit is just the missing tail mass.
  have hdist' : dist (μ.real B) (μ.real (s N)) < δ := by
    simpa [dist_comm] using hdist
  rw [hdiff_eq]
  simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs_le), s] using hdist'

-- Proof sketch: for each `N`, the `N`-th summand controls the truncated distance integral on
-- `A N`, and the weighted series tends to `0` iff every fixed summand tends to `0`. The forward
-- implication uses the textbook estimate by the deviation set plus `ε μ(A N)`, while the reverse
-- implication approximates any finite-measure measurable set by a large exhaustion set `A N`.
/-- Theorem 6.7 (2): For almost-everywhere measurable classes `f, fₙ : Ω →ₘ[μ] E`, convergence of
the exhaustion metric to `0` is equivalent to convergence in `μ`-measure on every set of finite
`μ`-measure for their representatives. -/
theorem tendsto_zero_measureExhaustionDist_iff_tendstoInMeasureOnFiniteMeasureSets
    (A : ℕ → Set Ω) (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_mono : Monotone A) (hA_univ : (⋃ n, A n) = Set.univ)
    (hA_finite : ∀ n, μ (A n) < ∞) {fSeq : ℕ → Ω →ₘ[μ] E} {f : Ω →ₘ[μ] E} :
    Tendsto
      (fun n ↦ measureExhaustionDist μ A (fSeq n) f)
      atTop (𝓝 0) ↔
      TendstoInMeasureOnFiniteMeasureSets μ (fun n ↦ fSeq n) f := by
  -- Route correction: the metric and single-piece estimates are now in place; the remaining work
  -- is the head-tail summation argument and the finite-measure approximation of an arbitrary set.
  refine ⟨fun hdist ↦ ?_, fun h_meas ↦ ?_⟩
  · intro B hB_finite
    letI : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.2 hB_finite.ne
    refine (tendstoInMeasure_iff_measureReal_dist).2 ?_
    intro ε hε
    refine Metric.tendsto_atTop.2 ?_
    intro δ hδ
    have hδ_half : 0 < δ / 2 := by linarith
    obtain ⟨N, hN_diff⟩ :=
      exists_exhaustion_piece_diff_lt_of_finiteMeasure A hA_meas hA_mono hA_univ
        hB_finite hδ_half
    let ε₀ : ℝ := min ε 1
    let weight : ℝ := (((1 / 2 : ℝ) ^ (N + 1)) / (1 + (μ (A N)).toReal))
    let C : ℝ := ε₀⁻¹ / weight
    have hweight_pos : 0 < weight := by
      positivity
    have hC_nonneg : 0 ≤ C := by
      positivity
    have hscaled :
        Tendsto (fun n ↦ C * measureExhaustionDist μ A (fSeq n) f) atTop (𝓝 0) := by
      simpa using hdist.const_mul C
    obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 hscaled) (δ / 2) hδ_half
    refine ⟨max N M, fun n hn ↦ ?_⟩
    let dev : Set Ω := {ω | ε ≤ dist (fSeq n ω) (f ω)}
    let dev₀ : Set Ω := {ω | ε₀ ≤ dist (fSeq n ω) (f ω)}
    have hε₀_pos : 0 < ε₀ := by
      unfold ε₀
      exact lt_min hε (by norm_num)
    have hε₀_le : ε₀ ≤ 1 := by
      unfold ε₀
      exact min_le_right _ _
    have hε₀_le_ε : ε₀ ≤ ε := by
      unfold ε₀
      exact min_le_left _ _
    have h_dev_subset : dev ⊆ dev₀ := by
      intro ω hω
      exact le_trans hε₀_le_ε hω
    have h_dev₀_null : NullMeasurableSet dev₀ μ := by
      -- The deviation set is null measurable because the distance is a.e.-measurable.
      have h_aemeas :
          AEMeasurable (fun ω ↦ dist (fSeq n ω) (f ω)) μ := by
        exact ((fSeq n).aestronglyMeasurable.dist f.aestronglyMeasurable).aemeasurable
      simpa [dev₀] using h_aemeas.nullMeasurableSet_preimage measurableSet_Ici
    have h_dev₀_null_B : NullMeasurableSet dev₀ (μ.restrict B) := by
      exact h_dev₀_null.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    have h_dev₀_null_A : NullMeasurableSet dev₀ (μ.restrict (A N)) := by
      exact h_dev₀_null.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    have h_restrict_B :
        (μ.restrict B).real dev₀ = μ.real (B ∩ dev₀) := by
      simpa [Set.inter_comm] using
        measureReal_restrict_apply₀ h_dev₀_null_B
    have h_restrict_A :
        (μ.restrict (A N)).real dev₀ = μ.real (A N ∩ dev₀) := by
      simpa [Set.inter_comm] using
        measureReal_restrict_apply₀ h_dev₀_null_A
    have h_subset :
        B ∩ dev₀ ⊆ (B \ A N) ∪ (A N ∩ dev₀) := by
      intro ω hω
      by_cases hωA : ω ∈ A N
      · exact Or.inr ⟨hωA, hω.2⟩
      · exact Or.inl ⟨hω.1, hωA⟩
    have h_dev_piece :
        (μ.restrict (A N)).real dev₀ ≤ C * measureExhaustionDist μ A (fSeq n) f := by
      have h_markov :
          (μ.restrict (A N)).real dev₀
            ≤ ε₀⁻¹ * ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ :=
        deviation_measureReal_le_truncated_piece_integral A hA_finite N hε₀_pos hε₀_le
      have h_piece :=
        measureExhaustionDist_piece_le A hA_meas hA_finite N (fSeq n) f
      have h_int_le :
          ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ
            ≤ measureExhaustionDist μ A (fSeq n) f / weight := by
        rw [le_div_iff₀ hweight_pos]
        simpa [weight, mul_comm, mul_left_comm, mul_assoc] using h_piece
      calc
        (μ.restrict (A N)).real dev₀
          ≤ ε₀⁻¹ * ∫ ω in A N, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ := h_markov
        _ ≤ ε₀⁻¹ * (measureExhaustionDist μ A (fSeq n) f / weight) := by
              gcongr
        _ = C * measureExhaustionDist μ A (fSeq n) f := by
              calc
                ε₀⁻¹ * (measureExhaustionDist μ A (fSeq n) f / weight)
                  = (ε₀⁻¹ / weight) * measureExhaustionDist μ A (fSeq n) f := by ring
                _ = C * measureExhaustionDist μ A (fSeq n) f := by rfl
    have h_scaled_small : C * measureExhaustionDist μ A (fSeq n) f < δ / 2 :=
      by
        have h_scaled_dist :
            dist (C * measureExhaustionDist μ A (fSeq n) f) 0 < δ / 2 :=
          hM n (le_trans (le_max_right _ _) hn)
        have h_dist_nonneg :
            0 ≤ C * measureExhaustionDist μ A (fSeq n) f := by
          exact mul_nonneg hC_nonneg
            (measureExhaustionDist_nonneg μ A (fSeq n) f)
        rw [Real.dist_eq] at h_scaled_dist
        simpa [abs_of_nonneg h_dist_nonneg] using h_scaled_dist
    have h_restrict_B_mono :
        (μ.restrict B).real dev ≤ (μ.restrict B).real dev₀ := by
      exact measureReal_mono h_dev_subset
    have h_main :
        (μ.restrict B).real dev < δ := by
      calc
        (μ.restrict B).real dev ≤ (μ.restrict B).real dev₀ := h_restrict_B_mono
        _ = μ.real (B ∩ dev₀) := h_restrict_B
        _ ≤ μ.real ((B \ A N) ∪ (A N ∩ dev₀)) := by
              have h_union_subset : (B \ A N) ∪ (A N ∩ dev₀) ⊆ B ∪ A N := by
                intro ω hω
                rcases hω with hω | hω
                · exact Or.inl hω.1
                · exact Or.inr hω.1
              have h_union_finite : μ ((B \ A N) ∪ (A N ∩ dev₀)) ≠ ∞ := by
                exact ((measure_mono h_union_subset).trans_lt
                  (measure_union_lt_top hB_finite (hA_finite N))).ne
              exact measureReal_mono h_subset h_union_finite
        _ ≤ μ.real (B \ A N) + μ.real (A N ∩ dev₀) := measureReal_union_le _ _
        _ = μ.real (B \ A N) + (μ.restrict (A N)).real dev₀ := by
              rw [← h_restrict_A]
        _ ≤ μ.real (B \ A N) + C * measureExhaustionDist μ A (fSeq n) f := by
              gcongr
        _ < δ / 2 + δ / 2 := add_lt_add hN_diff h_scaled_small
        _ = δ := by ring
    rw [Real.dist_eq]
    simpa [abs_of_nonneg measureReal_nonneg] using h_main
  · refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    have hε_half : 0 < ε / 2 := by linarith
    have hgeom_zero :
        Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hgeom_zero) (ε / 2) hε_half
    let head : ℕ → ℝ := fun n ↦
      Finset.sum (Finset.range K) fun i ↦
        (((1 / 2 : ℝ) ^ (i + 1)) / (1 + (μ (A i)).toReal)) *
          ∫ ω in A i, min (1 : ℝ) (dist (fSeq n ω) (f ω)) ∂μ
    have h_head_tendsto :
        Tendsto head atTop (𝓝 (Finset.sum (Finset.range K) fun _ ↦ (0 : ℝ))) := by
      -- Each fixed exhaustion piece contributes a term that tends to `0`.
      refine tendsto_finset_sum (Finset.range K) ?_
      intro i hi
      have h_local_piece :
          TendstoInMeasure (μ.restrict (A i)) (fun n ω ↦ fSeq n ω) atTop f := by
        simpa using h_meas (A i) (hA_finite i)
      simpa [head] using
        weighted_truncated_piece_tendsto_zero_of_tendstoInMeasure A hA_meas hA_finite
          i h_local_piece
    have h_head_tendsto_zero : Tendsto head atTop (𝓝 0) := by
      simpa using h_head_tendsto
    obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 h_head_tendsto_zero) (ε / 2) hε_half
    refine ⟨M, fun n hn ↦ ?_⟩
    have h_head_small : head n < ε / 2 := by
      have h_head_nonneg : 0 ≤ head n := by
        unfold head
        positivity
      simpa [Real.dist_eq, abs_of_nonneg h_head_nonneg] using hM n hn
    have h_tail_small : (1 / 2 : ℝ) ^ K < ε / 2 := by
      simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) ^ K)] using hK K le_rfl
    have h_dist_nonneg : 0 ≤ measureExhaustionDist μ A (fSeq n) f :=
      measureExhaustionDist_nonneg μ A (fSeq n) f
    have h_upper :=
      measureExhaustionDist_le_sum_range_add_geometric_tail A hA_meas hA_finite K
        (fSeq n) f
    have h_lt :
        measureExhaustionDist μ A (fSeq n) f < ε := by
      calc
        measureExhaustionDist μ A (fSeq n) f ≤ head n + (1 / 2 : ℝ) ^ K := by
          simpa [head] using h_upper
        _ < ε / 2 + ε / 2 := add_lt_add h_head_small h_tail_small
        _ = ε := by ring
    simpa [Real.dist_eq, abs_of_nonneg h_dist_nonneg] using h_lt

end Metric
