/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Exercise_7_4_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_58
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_60

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

namespace ProbabilityTheory

/-- Helper for Exercise 17.7.1: an almost-sure nat order is equivalent to mass `1` on the ordered
set. -/
lemma measure_eq_one_of_ae_natOrder (π : ProbabilityMeasure (ℕ × ℕ))
    (hOrdered : ∀ᵐ z ∂(π : Measure (ℕ × ℕ)), z.1 ≤ z.2) :
    (π : Measure (ℕ × ℕ)) {z | z.1 ≤ z.2} = 1 := by
  -- Proof comment: `ae_iff_prob_eq_one` converts the almost-sure order statement into the exact
  -- probability-one event required by the exercise.
  simpa using
    (MeasureTheory.ae_iff_prob_eq_one
      (μ := (π : Measure (ℕ × ℕ)))
      (p := fun z : ℕ × ℕ ↦ z.1 ≤ z.2)
      (by fun_prop)).1 hOrdered

/-- Helper for Exercise 17.7.1: recover a natural number from the unique coordinate of
`Fin 1 → ℝ` by flooring. -/
def decodeNatFin1 (z : Fin 1 → ℝ) : ℕ :=
  Nat.floor (z 0)

/-- Helper for Exercise 17.7.1: the coordinate-floor decoder `decodeNatFin1` is measurable. -/
lemma measurable_decodeNatFin1 : Measurable decodeNatFin1 := by
  -- Proof comment: evaluate the unique coordinate and compose with the measurable floor map.
  exact Nat.measurable_floor.comp (continuous_apply 0).measurable

/-- Helper for Exercise 17.7.1: decoding the singleton vector `![n]` recovers `n`. -/
lemma decodeNatFin1_natEmbed (n : ℕ) :
    decodeNatFin1 (![n] : Fin 1 → ℝ) = n := by
  -- Proof comment: the only coordinate of `![n]` is `n`, and `Nat.floor` fixes natural casts.
  simp [decodeNatFin1]

/-- Helper for Exercise 17.7.1: decoding the embedded nat law `μ.toFin1Real` returns `μ`. -/
lemma map_decodeNatFin1_toFin1Real (μ : ProbabilityMeasure ℕ) :
    μ.toFin1Real.map measurable_decodeNatFin1.aemeasurable = μ := by
  have hNatEmbedMeas : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)) := by
    simpa using (Measurable.of_discrete : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)))
  -- Proof comment: `toFin1Real` is a pushforward along the singleton-vector embedding, and
  -- `decodeNatFin1` is its left inverse on natural points.
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map decodeNatFin1 (Measure.map (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)) (μ : Measure ℕ)) =
    (μ : Measure ℕ)
  rw [Measure.map_map measurable_decodeNatFin1 hNatEmbedMeas]
  simpa [Function.comp] using
    (Measure.map_congr (μ := (μ : Measure ℕ))
      (Filter.Eventually.of_forall decodeNatFin1_natEmbed))

/-- Helper for Exercise 17.7.1: an ordered coupling of the embedded one-dimensional laws yields an
ordered coupling of the original nat-valued laws after decoding each coordinate. -/
lemma existsNatOrderedCoupling_of_toFin1Real
    {μ₁ μ₂ : ProbabilityMeasure ℕ}
    (hStochastic : StochasticLE μ₁.toFin1Real μ₂.toFin1Real) :
    ∃ π : ProbabilityMeasure (ℕ × ℕ),
      IsCoupling π μ₁ μ₂ ∧
        (π : Measure (ℕ × ℕ)) {z | z.1 ≤ z.2} = 1 := by
  rcases
      (stochasticLE_iff_exists_ordered_coupling
        (μ1 := μ₁.toFin1Real) (μ2 := μ₂.toFin1Real)).1 hStochastic with
    ⟨φ, hCoupling, hOrderedMass⟩
  let decodePair : (Fin 1 → ℝ) × (Fin 1 → ℝ) → ℕ × ℕ :=
    fun z ↦ (decodeNatFin1 z.1, decodeNatFin1 z.2)
  have hDecodePairMeas : Measurable decodePair := by
    -- Proof comment: decode the two coordinates separately and pair the results.
    exact (measurable_decodeNatFin1.comp measurable_fst).prodMk
      (measurable_decodeNatFin1.comp measurable_snd)
  let π : ProbabilityMeasure (ℕ × ℕ) := φ.map hDecodePairMeas.aemeasurable
  rcases hCoupling with ⟨hfst, hsnd⟩
  refine ⟨π, ?_, ?_⟩
  · constructor
    · -- Proof comment: after projecting the decoded pair to the first coordinate, only the first
      -- embedded marginal remains, and decoding that marginal recovers `μ₁`.
      calc
        (π : Measure (ℕ × ℕ)).fst
            = Measure.map (fun z : (Fin 1 → ℝ) × (Fin 1 → ℝ) ↦ decodeNatFin1 z.1)
                (φ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) := by
                  rw [Measure.fst, ProbabilityMeasure.toMeasure_map]
                  rw [Measure.map_map measurable_fst hDecodePairMeas]
                  rfl
        _ = Measure.map decodeNatFin1 ((φ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))).fst) := by
            rw [Measure.fst, Measure.map_map measurable_decodeNatFin1 measurable_fst]
            rfl
        _ = Measure.map decodeNatFin1 (μ₁.toFin1Real : Measure (Fin 1 → ℝ)) := by
            rw [hfst]
        _ = (μ₁ : Measure ℕ) := by
            simpa using
              congrArg (fun ν : ProbabilityMeasure ℕ ↦ (ν : Measure ℕ))
                (map_decodeNatFin1_toFin1Real μ₁)
    · -- Proof comment: the second marginal is transported in exactly the same way.
      calc
        (π : Measure (ℕ × ℕ)).snd
            = Measure.map (fun z : (Fin 1 → ℝ) × (Fin 1 → ℝ) ↦ decodeNatFin1 z.2)
                (φ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))) := by
                  rw [Measure.snd, ProbabilityMeasure.toMeasure_map]
                  rw [Measure.map_map measurable_snd hDecodePairMeas]
                  rfl
        _ = Measure.map decodeNatFin1 ((φ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ))).snd) := by
            rw [Measure.snd, Measure.map_map measurable_decodeNatFin1 measurable_snd]
            rfl
        _ = Measure.map decodeNatFin1 (μ₂.toFin1Real : Measure (Fin 1 → ℝ)) := by
            rw [hsnd]
        _ = (μ₂ : Measure ℕ) := by
            simpa using
              congrArg (fun ν : ProbabilityMeasure ℕ ↦ (ν : Measure ℕ))
                (map_decodeNatFin1_toFin1Real μ₂)
  · have hOrderedSet : MeasurableSet ({z : ℕ × ℕ | z.1 ≤ z.2} : Set (ℕ × ℕ)) := by
      exact measurableSet_le measurable_fst measurable_snd
    -- Proof comment: coordinatewise order in `Fin 1 → ℝ` implies order after flooring the unique
    -- coordinate, so the ordered event still has full mass after decoding.
    change
      Measure.map decodePair (φ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ)))
        ({z : ℕ × ℕ | z.1 ≤ z.2} : Set (ℕ × ℕ)) = 1
    rw [Measure.map_apply_of_aemeasurable hDecodePairMeas.aemeasurable hOrderedSet]
    have hsubset :
        ({z : (Fin 1 → ℝ) × (Fin 1 → ℝ) | z.1 ≤ z.2} : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ))) ⊆
          decodePair ⁻¹' ({z : ℕ × ℕ | z.1 ≤ z.2} : Set (ℕ × ℕ)) := by
      intro z hz
      change decodeNatFin1 z.1 ≤ decodeNatFin1 z.2
      exact Nat.floor_mono (hz 0)
    exact le_antisymm MeasureTheory.prob_le_one <|
      calc
        1 =
            (φ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ)))
              ({z : (Fin 1 → ℝ) × (Fin 1 → ℝ) | z.1 ≤ z.2} :
                Set ((Fin 1 → ℝ) × (Fin 1 → ℝ))) := hOrderedMass.symm
        _ ≤
            (φ : Measure ((Fin 1 → ℝ) × (Fin 1 → ℝ)))
              (decodePair ⁻¹' ({z : ℕ × ℕ | z.1 ≤ z.2} : Set (ℕ × ℕ))) :=
            measure_mono hsubset

-- Proof sketch: write `n₂ = k n₁`, partition the `n₂` Bernoulli trials into `k` blocks of length
-- `n₁`, choose the block-success parameter so that the zero-count probability matches
-- `(1 - p₂) ^ n₂`, and couple the `n₁`-count with the number of nonempty blocks to obtain an
-- ordered coupling supported on `{(x₁, x₂) : ℕ × ℕ | x₁ ≤ x₂}`.
/-- Exercise 17.7.1: when `n₁ ∣ n₂`, the condition
`(1 - p₁) ^ n₁ ≥ (1 - p₂) ^ n₂` yields a direct coupling of the binomial laws
`Bin(n₁, p₁)` and `Bin(n₂, p₂)` that is supported on the order relation `x₁ ≤ x₂`, and hence
proves the divisible-case claim of Theorem 17.60. -/
theorem exists_ordered_binomial_coupling_of_pow_condition_of_dvd
    (n₁ n₂ : ℕ+) (p₁ p₂ : I)
    (hdiv : (n₁ : ℕ) ∣ n₂) (hpow : (1 - (p₁ : ℝ)) ^ (n₁ : ℕ) ≥ (1 - (p₂ : ℝ)) ^ (n₂ : ℕ)) :
    ∃ π : ProbabilityMeasure (ℕ × ℕ),
      IsCoupling π
        (⟨Bin((n₁ : ℕ), p₁), inferInstance⟩ : ProbabilityMeasure ℕ)
        (⟨Bin((n₂ : ℕ), p₂), inferInstance⟩ : ProbabilityMeasure ℕ) ∧
        π {x | x.1 ≤ x.2} = 1 := by
  let μ₂ : ProbabilityMeasure ℕ := ⟨Bin((n₂ : ℕ), p₂), inferInstance⟩
  have hn₁₂ : (n₁ : ℕ) ≤ (n₂ : ℕ) := Nat.le_of_dvd n₂.2 hdiv
  by_cases hp₁0 : (p₁ : ℝ) = 0
  · have hp₁_eq_zero : p₁ = (0 : I) := by
      apply Subtype.ext
      simpa using hp₁0
    subst hp₁_eq_zero
    let π : ProbabilityMeasure (ℕ × ℕ) :=
      μ₂.map (show AEMeasurable (fun y : ℕ ↦ (0, y)) (μ₂ : Measure ℕ) by fun_prop)
    refine ⟨π, ?_, ?_⟩
    · rw [isCoupling_iff]
      constructor
      · -- Proof comment: the first projection of the deterministic map is constant `0`, which is
        -- exactly the `Bin(n₁, 0)` law.
        apply ProbabilityMeasure.toMeasure_injective
        change
          Measure.map Prod.fst (Measure.map (fun y : ℕ ↦ (0, y)) (μ₂ : Measure ℕ)) =
            (Bin((n₁ : ℕ), (0 : I)) : Measure ℕ)
        rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (by fun_prop)]
        simp only [Prod.fst_comp_mk, Function.const_zero, binomial_zero_right]
        have hmapZero : Measure.map (fun _ : ℕ ↦ (0 : ℕ)) (μ₂ : Measure ℕ) = Measure.dirac 0 := by
          ext s hs
          rw [Measure.map_apply (by fun_prop) hs, Measure.dirac_apply' 0 hs]
          by_cases h0 : (0 : ℕ) ∈ s <;> simp [h0]
        -- Proof comment: after simplification, this is exactly the constant-map identity.
        exact hmapZero
      · -- Proof comment: the second projection is the identity, so the right marginal is
        -- unchanged.
        apply ProbabilityMeasure.toMeasure_injective
        change
          Measure.map Prod.snd (Measure.map (fun y : ℕ ↦ (0, y)) (μ₂ : Measure ℕ)) =
            (μ₂ : Measure ℕ)
        rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable (by fun_prop)]
        exact Measure.map_id (μ := (μ₂ : Measure ℕ))
    · have hOrderedSet : MeasurableSet ({z : ℕ × ℕ | z.1 ≤ z.2} : Set (ℕ × ℕ)) := by
        exact measurableSet_le measurable_fst measurable_snd
      -- Proof comment: every point in the image has first coordinate `0`, so the ordered event is
      -- the whole image.
      have hMass :
          ((π : Measure (ℕ × ℕ)) ({x : ℕ × ℕ | x.1 ≤ x.2} : Set (ℕ × ℕ))) = 1 := by
        rw [show (π : Measure (ℕ × ℕ)) = Measure.map (fun y : ℕ ↦ (0, y)) (μ₂ : Measure ℕ) by rfl]
        rw [Measure.map_apply_of_aemeasurable (by fun_prop) hOrderedSet]
        have hpre :
            (fun y : ℕ ↦ (0, y)) ⁻¹' ({z : ℕ × ℕ | z.1 ≤ z.2} : Set (ℕ × ℕ)) = Set.univ := by
          ext y
          simp
        rw [hpre, measure_univ]
      simpa [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
        congrArg ENNReal.toNNReal hMass
  · by_cases hp₁1 : (p₁ : ℝ) = 1
    · have hp₁_eq_one : p₁ = (1 : I) := by
        apply Subtype.ext
        simpa using hp₁1
      have hpowZero : (1 - (p₂ : ℝ)) ^ (n₂ : ℕ) = 0 := by
        have hbase_nonneg : 0 ≤ 1 - (p₂ : ℝ) := by
          linarith [p₂.2.2]
        have hnonneg : 0 ≤ (1 - (p₂ : ℝ)) ^ (n₂ : ℕ) := by
          exact pow_nonneg hbase_nonneg _
        have hle : (1 - (p₂ : ℝ)) ^ (n₂ : ℕ) ≤ 0 := by
          have hn₁_ne_zero : (n₁ : ℕ) ≠ 0 := Nat.ne_of_gt n₁.2
          simpa [hp₁1, hn₁_ne_zero] using hpow
        exact le_antisymm hle hnonneg
      have hbase_zero : 1 - (p₂ : ℝ) = 0 := by
        by_contra hbase
        exact (pow_ne_zero (n₂ : ℕ) hbase) hpowZero
      have hp₂_eq_one : p₂ = (1 : I) := by
        apply Subtype.ext
        have hp₂_real : (p₂ : ℝ) = 1 := by
          linarith [hbase_zero]
        simpa using hp₂_real
      subst hp₁_eq_one
      subst hp₂_eq_one
      rcases binomial_monotone_in_number_of_trials hn₁₂ (1 : I) with ⟨π, hCoupling, hOrdered⟩
      refine ⟨π, hCoupling, ?_⟩
      simpa [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
        congrArg ENNReal.toNNReal (measure_eq_one_of_ae_natOrder π hOrdered)
    · have hp₁_pos : 0 < (p₁ : ℝ) := by
        exact lt_of_le_of_ne p₁.2.1 (by simpa [eq_comm] using hp₁0)
      have hp₁_lt_one : (p₁ : ℝ) < 1 := by
        exact lt_of_le_of_ne p₁.2.2 hp₁1
      -- Route correction: rather than rebuilding the divisible-case block coupling locally, use
      -- Theorem 17.60 to get stochastic order in the ambient one-dimensional space and then
      -- decode the resulting ordered coupling back to `ℕ × ℕ`.
      have hStochastic :
          StochasticLE
            (ProbabilityMeasure.toFin1Real
              (⟨Bin((n₁ : ℕ), p₁), inferInstance⟩ : ProbabilityMeasure ℕ))
            (ProbabilityMeasure.toFin1Real
              (⟨Bin((n₂ : ℕ), p₂), inferInstance⟩ : ProbabilityMeasure ℕ)) := by
        exact
          (binomial_stochasticLE_iff (n₁ := (n₁ : ℕ)) (n₂ := (n₂ : ℕ))
            (p₁ := p₁) (p₂ := p₂) hp₁_pos hp₁_lt_one).2 ⟨hpow, hn₁₂⟩
      rcases existsNatOrderedCoupling_of_toFin1Real hStochastic with ⟨π, hCoupling, hMass⟩
      refine ⟨π, hCoupling, ?_⟩
      simpa [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
        congrArg ENNReal.toNNReal hMass

end ProbabilityTheory
