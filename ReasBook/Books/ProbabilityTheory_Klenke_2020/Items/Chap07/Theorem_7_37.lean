/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Filter Set
open scoped MeasureTheory ENNReal

universe u

namespace MeasureTheory
namespace Measure

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ ν : Measure Ω}

/-- Helper for Theorem 7.37: a totally continuous measure vanishes on measurable `μ`-null
sets. -/
private lemma totallyContinuous_null_of_null (h : TotallyContinuous ν μ) {s : Set Ω}
    (hs : MeasurableSet s) (hμs : μ s = 0) :
    ν s = 0 := by
  by_cases hνs : ν s = 0
  · exact hνs
  · -- Use the set's own `ν`-mass as `ε`; total continuity would then force `ν s < ν s`.
    have hνs_pos : 0 < ν s := pos_iff_ne_zero.mpr hνs
    obtain ⟨δ, hδ_pos, hδ_spec⟩ := h hνs_pos
    have hμs_lt : μ s < δ := by
      simpa [hμs] using hδ_pos
    exfalso
    exact lt_irrefl _ (hδ_spec hs hμs_lt)

-- Proof sketch: apply total continuity to a `μ`-null measurable set and vary `ε > 0`; the
-- resulting bounds `ν s < ε` for every positive `ε` force `ν s = 0`.
/-- Theorem 7.37 (1): If `ν` is totally continuous with respect to `μ`, then `ν` is absolutely
continuous with respect to `μ`. -/
theorem totallyContinuous_absolutelyContinuous (h : TotallyContinuous ν μ) : ν ≪ μ := by
  -- Reduce absolute continuity to the measurable-null-set case handled by the helper.
  refine AbsolutelyContinuous.mk fun s hs hμs ↦ ?_
  exact totallyContinuous_null_of_null h hs hμs

/-- Helper for Theorem 7.37: failure of total continuity yields a geometric witness sequence whose
`μ`-masses go to zero while the `ν`-masses stay uniformly positive. -/
private lemma not_totallyContinuous_exists_geometric_witness (h : ¬ TotallyContinuous ν μ) :
    ∃ ε > 0, ∃ A : ℕ → Set Ω,
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n, μ (A n) < (2⁻¹ : ℝ≥0∞) ^ n) ∧
      (∀ n, ε ≤ ν (A n)) := by
  classical
  change
    ¬ ∀ ⦃ε : ℝ≥0∞⦄, 0 < ε →
      ∃ δ > 0, ∀ ⦃s : Set Ω⦄, MeasurableSet s → μ s < δ → ν s < ε at h
  push Not at h
  rcases h with ⟨ε, hε_pos, hε⟩
  have hpow_pos : ∀ n : ℕ, 0 < (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    simpa using ENNReal.pow_pos (by simp) n
  choose A hA_meas hAμ hAν using fun n ↦ hε ((2⁻¹ : ℝ≥0∞) ^ n) (hpow_pos n)
  -- The geometric choice `δₙ = 2^{-n}` packages the entire contraposition witness.
  exact ⟨ε, hε_pos, A, hA_meas, hAμ, hAν⟩

/-- Helper for Theorem 7.37: a geometric upper bound on the measures of `A n` forces the limsup
to be `μ`-null. -/
private lemma measure_limsup_eq_zero_of_geometric_witness {A : ℕ → Set Ω}
    (hAμ : ∀ n, μ (A n) < (2⁻¹ : ℝ≥0∞) ^ n) :
    μ (limsup A atTop) = 0 := by
  have hseries_le :
      (∑' n : ℕ, μ (A n)) ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n :=
    ENNReal.tsum_le_tsum fun n ↦ (hAμ n).le
  have hgeom_ne_top : (∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) ≠ ∞ := by
    rw [ENNReal.tsum_geometric_two]
    simp
  -- Compare the given series with the convergent geometric series.
  exact measure_limsup_atTop_eq_zero <| ne_top_of_le_ne_top hgeom_ne_top hseries_le

/-- Helper for Theorem 7.37: if all `A n` carry at least `ε` mass for a finite measure `ν`, then
their limsup also carries at least `ε` mass. -/
private lemma le_measure_limsup_of_finite_and_lower_bound (hν_finite : ν univ < ∞)
    {A : ℕ → Set Ω}
    (hA_meas : ∀ n, MeasurableSet (A n)) {ε : ℝ≥0∞}
    (hAν : ∀ n, ε ≤ ν (A n)) :
    ε ≤ ν (limsup A atTop) := by
  let T : ℕ → Set Ω := fun n ↦ ⋃ m ≥ n, A m
  have hT_antitone : Antitone T := by
    intro n m hnm
    exact iUnion₂_mono' fun k hmk ↦ ⟨k, le_trans hnm hmk, Subset.rfl⟩
  have hT_meas : ∀ n, MeasurableSet (T n) := by
    intro n
    exact MeasurableSet.iUnion fun m ↦ MeasurableSet.iUnion fun _ ↦ hA_meas m
  have hT_finite : ν (T 0) < ∞ := by
    refine (measure_mono ?_).trans_lt hν_finite
    exact subset_univ _
  have hA_tail : ∀ n, ε ≤ ν (T n) := by
    intro n
    refine (hAν n).trans <| measure_mono ?_
    intro x hx
    exact mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨le_rfl, hx⟩⟩
  have hlimsup : limsup A atTop = ⋂ n : ℕ, T n := by
    ext x
    simp [T, limsup_eq_iInf_iSup_of_nat]
  -- Tail unions decrease to the limsup, so continuity from above transfers the lower bound.
  calc
    ε ≤ ⨅ n : ℕ, ν (T n) := by
      exact le_iInf hA_tail
    _ = ν (⋂ n : ℕ, T n) := by
      symm
      exact hT_antitone.measure_iInter (fun n ↦ (hT_meas n).nullMeasurableSet)
        ⟨0, hT_finite.ne⟩
    _ = ν (limsup A atTop) := by
      simp [hlimsup]

-- Proof sketch: argue by contraposition. If total continuity fails, choose measurable sets
-- `Aₙ` with `μ Aₙ` summable to zero but `ν Aₙ` bounded below by some `ε > 0`; then the limsup of
-- these sets has `μ`-measure zero and, by finiteness of `ν` plus continuity from above,
-- positive `ν`-measure, contradicting `ν ≪ μ`.
/-- Theorem 7.37 (2): If `ν (Ω) < ∞`, then absolute continuity of `ν` with respect to `μ`
implies total continuity of `ν` with respect to `μ`. -/
theorem absolutelyContinuous_totallyContinuous_of_finite (h : ν ≪ μ) (hν_finite : ν univ < ∞) :
    TotallyContinuous ν μ := by
  classical
  by_contra hnot_tc
  obtain ⟨ε, hε_pos, A, hA_meas, hAμ, hAν⟩ :=
    not_totallyContinuous_exists_geometric_witness hnot_tc
  have hμ_limsup : μ (limsup A atTop) = 0 :=
    measure_limsup_eq_zero_of_geometric_witness hAμ
  have hν_limsup : ε ≤ ν (limsup A atTop) :=
    le_measure_limsup_of_finite_and_lower_bound hν_finite hA_meas hAν
  have hν_zero : ν (limsup A atTop) = 0 := h hμ_limsup
  -- The limsup is `μ`-null but still has `ν`-mass at least `ε > 0`, contradicting `ν ≪ μ`.
  have : ε ≤ 0 := by
    simpa [hν_zero] using hν_limsup
  exact (not_le_of_gt hε_pos) this

-- Proof sketch: combine Theorem 7.37 (1) with Theorem 7.37 (2).
/-- Theorem 7.37: for a finite measure `ν`, absolute continuity of `ν` with respect to `μ` is
equivalent to total continuity of `ν` with respect to `μ`. -/
theorem absolutelyContinuous_iff_totallyContinuous [IsFiniteMeasure ν] :
    ν ≪ μ ↔ TotallyContinuous ν μ := by
  constructor
  · intro h
    exact absolutelyContinuous_totallyContinuous_of_finite h (measure_lt_top ν univ)
  · exact totallyContinuous_absolutelyContinuous

end Measure
end MeasureTheory
