/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/-- First assertion of Corollary 13.7: Lebesgue measure on `ℝ^d`, formalized as
`volume` on `EuclideanSpace ℝ (Fin d)`, is a regular measure in the sense of
Definition 13.3. -/
theorem lebesgueMeasure_isRegular (d : ℕ) :
    IsRegularMeasure (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  IsRegularMeasure.of_owner volume

/-- Second assertion of Corollary 13.7: Lebesgue measure on `ℝ^d`, formalized as
`volume` on `EuclideanSpace ℝ (Fin d)`, is a Radon measure in the sense of
Definition 13.3. -/
theorem lebesgueMeasure_isRadon (d : ℕ) :
    IsRadonMeasure (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  IsRadonMeasure.of_owner volume

/-- Helper for Corollary 13.7: the atomic support points accumulate at `0` along the `i0`-axis. -/
private noncomputable def axisReciprocalPoint (i0 : Fin d) : ℕ → EuclideanSpace ℝ (Fin d) :=
  fun n ↦ EuclideanSpace.single i0 (1 / (n + 1 : ℝ))

/-- Helper for Corollary 13.7: the reciprocal axis sequence is a measurable embedding. -/
private lemma axisReciprocalPoint_measurableEmbedding (i0 : Fin d) :
    MeasurableEmbedding (axisReciprocalPoint (d := d) i0) := by
  -- Reading the distinguished coordinate reduces equality to equality of reciprocals.
  refine (measurable_of_countable _).measurableEmbedding ?_
  intro m n hmn
  have hcoord :=
    congrArg (fun x : EuclideanSpace ℝ (Fin d) ↦ x i0) hmn
  have hdiv :
      (1 / (m + 1 : ℝ)) = 1 / (n + 1 : ℝ) := by
    simpa [axisReciprocalPoint] using hcoord
  have hsucc : m + 1 = n + 1 := by
    exact_mod_cast eq_of_one_div_eq_one_div hdiv
  exact Nat.succ.inj hsucc

/-- Helper for Corollary 13.7: the reciprocal axis sequence never hits `0`. -/
private lemma axisReciprocalPoint_preimage_zero (i0 : Fin d) :
    axisReciprocalPoint (d := d) i0 ⁻¹' ({0} : Set (EuclideanSpace ℝ (Fin d))) = ∅ := by
  -- Every support point has a nonzero `i0`-coordinate, so the singleton fiber at `0` is empty.
  ext n
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  intro hn
  have hcoord :=
    congrArg (fun x : EuclideanSpace ℝ (Fin d) ↦ x i0) hn
  have hdiv : (1 / (n + 1 : ℝ)) = 0 := by
    simpa [axisReciprocalPoint] using hcoord
  exact one_div_ne_zero (by positivity) hdiv

/-- Helper for Corollary 13.7: every open neighborhood of `0` contains infinitely many support
points of the reciprocal axis sequence. -/
private lemma axisReciprocalPoint_preimage_infinite_of_isOpen (i0 : Fin d)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (h0U : (0 : EuclideanSpace ℝ (Fin d)) ∈ U) :
    (axisReciprocalPoint (d := d) i0 ⁻¹' U).Infinite := by
  -- Openness at `0` gives a small ball inside `U`.
  rcases Metric.mem_nhds_iff.1 (hU.mem_nhds h0U) with ⟨ε, hεpos, hεU⟩
  rcases exists_nat_one_div_lt hεpos with ⟨N, hNε⟩
  have htail :
      Set.Ici N ⊆ axisReciprocalPoint (d := d) i0 ⁻¹' U := by
    intro n hn
    have hdiv_le : (1 / (n + 1 : ℝ)) ≤ 1 / (N + 1 : ℝ) := by
      have hsucc : N + 1 ≤ n + 1 := Nat.succ_le_succ hn
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hsucc)
    have hdiv_nonneg : 0 ≤ 1 / (n + 1 : ℝ) := by
      exact le_of_lt (Nat.one_div_pos_of_nat : 0 < 1 / (n + 1 : ℝ))
    have hnorm_lt : ‖axisReciprocalPoint (d := d) i0 n‖ < ε := by
      calc
        ‖axisReciprocalPoint (d := d) i0 n‖ = ‖1 / (n + 1 : ℝ)‖ := by
          simp [axisReciprocalPoint]
        _ = 1 / (n + 1 : ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hdiv_nonneg]
        _ ≤ 1 / (N + 1 : ℝ) := hdiv_le
        _ < ε := hNε
    have hmemBall : axisReciprocalPoint (d := d) i0 n ∈ Metric.ball 0 ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt
    exact hεU hmemBall
  -- A whole infinite tail lies in the preimage, so the preimage is infinite.
  exact Set.Infinite.mono htail (Set.Ici_infinite N)

/-- Corollary 13.7: in positive dimension, there exists a `σ`-finite measure on `ℝ^d`
that is not regular in the textbook sense, i.e. it does not satisfy
`IsRegularMeasure`. -/
-- Route correction: instead of a dense rational support, use an injective reciprocal sequence on
-- one coordinate axis. This keeps the bad set equal to `{0}` and makes the outer-regularity
-- contradiction a direct neighborhood argument.
theorem exists_sigmaFinite_not_regular_measure_on_euclidean (d : ℕ) (hd : 0 < d) :
    ∃ μ : Measure (EuclideanSpace ℝ (Fin d)),
      SigmaFinite μ ∧ ¬ IsRegularMeasure μ := by
  let i0 : Fin d := ⟨0, hd⟩
  let f : ℕ → EuclideanSpace ℝ (Fin d) := axisReciprocalPoint (d := d) i0
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := (Measure.count : Measure ℕ).map f
  let A : Set (EuclideanSpace ℝ (Fin d)) := {0}
  have hf : MeasurableEmbedding f := axisReciprocalPoint_measurableEmbedding (d := d) i0
  have hσ : SigmaFinite μ := by
    -- A measurable embedding preserves `σ`-finiteness under pushforward.
    have hmap : SigmaFinite ((Measure.count : Measure ℕ).map f) := hf.sigmaFinite_map
    simpa [μ] using hmap
  have hzero : μ A = 0 := by
    -- The singleton `{0}` has empty preimage under the support map.
    calc
      μ A = (Measure.count : Measure ℕ) (f ⁻¹' A) := by
              rw [show μ = (Measure.count : Measure ℕ).map f by rfl, hf.map_apply]
      _ = (Measure.count : Measure ℕ) ∅ := by
            rw [show A = ({0} : Set (EuclideanSpace ℝ (Fin d))) by rfl,
              show f = axisReciprocalPoint (d := d) i0 by rfl,
              axisReciprocalPoint_preimage_zero (d := d) i0]
      _ = 0 := measure_empty
  have hopen_top {U : Set (EuclideanSpace ℝ (Fin d))}
      (hU : IsOpen U) (h0U : (0 : EuclideanSpace ℝ (Fin d)) ∈ U) := by
    have hpre :
        (f ⁻¹' U).Infinite := by
      simpa [f] using
        axisReciprocalPoint_preimage_infinite_of_isOpen (d := d) i0 hU h0U
    -- Any neighborhood of `0` contains infinitely many atoms, so its mass is infinite.
    calc
      μ U = (Measure.count : Measure ℕ) (f ⁻¹' U) := by
        rw [show μ = (Measure.count : Measure ℕ).map f by rfl, hf.map_apply]
      _ = ⊤ := by
            exact Measure.count_apply_eq_top.2 hpre
  refine ⟨μ, hσ, ?_⟩
  intro hreg
  have houter : Measure.OuterRegular μ := IsRegularMeasure.outerRegular hreg
  have hzero_lt_one : μ A < 1 := by
    rw [hzero]
    simp
  -- Outer regularity would provide a small open neighborhood of `{0}`.
  letI : Measure.OuterRegular μ := houter
  have hOpenWitness :
      ∃ U, U ⊇ A ∧ IsOpen U ∧ (μ U < 1) :=
    Set.exists_isOpen_lt_of_lt (μ := μ) A 1 hzero_lt_one
  rcases hOpenWitness with ⟨U, hUzero, hUopen, hUone⟩
  have h0A : (0 : EuclideanSpace ℝ (Fin d)) ∈ A := by
    simp [A]
  have h0U : (0 : EuclideanSpace ℝ (Fin d)) ∈ U := hUzero h0A
  have hUtop : μ U = ⊤ := hopen_top hUopen h0U
  rw [hUtop] at hUone
  simp at hUone
