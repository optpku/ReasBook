/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set Filter
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

private theorem abs_apply_le_totalVariation_real
    (φ : SignedMeasure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    |φ A| ≤ φ.totalVariation.real A := by
  have hφ' :
      φ.toJordanDecomposition.toSignedMeasure A =
        φ.toJordanDecomposition.posPart.real A - φ.toJordanDecomposition.negPart.real A := by
    simpa [JordanDecomposition.toSignedMeasure] using
      (show
        (φ.toJordanDecomposition.posPart.toSignedMeasure -
            φ.toJordanDecomposition.negPart.toSignedMeasure) A =
          φ.toJordanDecomposition.posPart.real A - φ.toJordanDecomposition.negPart.real A from
        Measure.toSignedMeasure_sub_apply hA)
  have hφ : φ A = φ.toJordanDecomposition.posPart.real A - φ.toJordanDecomposition.negPart.real A := by
    simpa [SignedMeasure.toSignedMeasure_toJordanDecomposition φ, hA] using hφ'
  have htv : φ.totalVariation.real A =
      φ.toJordanDecomposition.posPart.real A + φ.toJordanDecomposition.negPart.real A := by
    have htv' :
        (φ.toJordanDecomposition.posPart + φ.toJordanDecomposition.negPart).real A =
          φ.toJordanDecomposition.posPart.real A + φ.toJordanDecomposition.negPart.real A :=
      measureReal_add_apply
    simpa [SignedMeasure.totalVariation] using htv'
  have hpos : 0 ≤ φ.toJordanDecomposition.posPart.real A := by simp
  have hneg : 0 ≤ φ.toJordanDecomposition.negPart.real A := by simp
  rw [hφ, htv]
  simpa [abs_of_nonneg hpos, abs_of_nonneg hneg] using
    abs_sub (φ.toJordanDecomposition.posPart.real A) (φ.toJordanDecomposition.negPart.real A)

-- Proof sketch: view a signed measure as the canonical real-valued vector measure, use
-- `VectorMeasure.of_disjoint_iUnion` to identify the series with the measure of the union for every
-- rearrangement, and apply the real-series rearrangement theorem to deduce absolute convergence.
/-- Remark 7.41 (1): Part (i). For pairwise disjoint measurable sets, the series of signed-measure
values converges absolutely. -/
theorem signedMeasure_summable_abs_of_pairwise_disjoint
    (φ : SignedMeasure Ω) (A : ℕ → Set Ω) (hmeas : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j ↦ Disjoint (A i) (A j)) :
    Summable (fun n ↦ |φ (A n)|) := by
  have htv_eq : φ.totalVariation (⋃ n, A n) = ∑' n, φ.totalVariation (A n) :=
    measure_iUnion hdisj hmeas
  have htv : Summable (fun n ↦ φ.totalVariation.real (A n)) := by
    have hne : φ.totalVariation (⋃ n, A n) ≠ ⊤ := by
      change
        φ.toJordanDecomposition.posPart (⋃ n, A n) +
            φ.toJordanDecomposition.negPart (⋃ n, A n) ≠
          ⊤
      have := ENNReal.add_ne_top.2
        ⟨(measure_lt_top φ.toJordanDecomposition.posPart (⋃ n, A n)).ne,
          (measure_lt_top φ.toJordanDecomposition.negPart (⋃ n, A n)).ne⟩
      exact this
    refine ENNReal.summable_toReal ?_
    rw [← htv_eq]
    exact hne
  refine Summable.of_nonneg_of_le (fun n ↦ abs_nonneg _) (fun n ↦ ?_) htv
  exact abs_apply_le_totalVariation_real φ (hmeas n)

-- Proof sketch: apply the vanishing-tail theorem for absolutely summable real series to
-- `fun n ↦ |φ (A n)|`, using the absolute convergence from
-- `signedMeasure_summable_abs_of_pairwise_disjoint`.
/-- Remark 7.41 (2): Part (i). The tails of the absolute-value series of a pairwise disjoint
family have limit `0`. -/
theorem tendsto_signedMeasure_abs_tail_of_pairwise_disjoint
    (φ : SignedMeasure Ω) (A : ℕ → Set Ω) (hmeas : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j ↦ Disjoint (A i) (A j)) :
    Tendsto (fun n ↦ ∑' k : ℕ, |φ (A (k + n))|) atTop (𝓝 0) := by
  let _ := signedMeasure_summable_abs_of_pairwise_disjoint φ A hmeas hdisj
  simpa using tendsto_sum_nat_add (fun n ↦ |φ (A n)|)

/- Remark 7.41 (ii): Every signed measure vanishes on the empty set, i.e. `φ ∅ = 0`. This is the
canonical vector-measure identity `VectorMeasure.empty`, specialized to
`MeasureTheory.SignedMeasure`. -/
recall VectorMeasure.empty

-- Proof sketch: choose a signed measure with negative total mass and a measurable sequence with
-- only finitely many nonempty terms; duplicating a negative-mass measurable set gives a direct
-- finite-support counterexample.
/-- Remark 7.41 (3): Part (iii). In general, signed measures are not `σ`-subadditive: there is a
measurable space, a signed measure, and a summable measurable sequence whose union has strictly
larger signed mass than the series sum. -/
theorem exists_signedMeasure_not_sigmaSubadditive :
    ∃ (X : Type u) (_ : MeasurableSpace X) (φ : SignedMeasure X) (A : ℕ → Set X),
      (∀ n, MeasurableSet (A n)) ∧
        Summable (fun n ↦ φ (A n)) ∧
          φ (⋃ n, A n) > ∑' n, φ (A n) := by
  let φ : SignedMeasure (ULift Unit) := -((Measure.dirac (ULift.up ())).toSignedMeasure)
  let A : ℕ → Set (ULift Unit) :=
    fun n ↦ if n = 0 then Set.univ else if n = 1 then Set.univ else ∅
  have hsum : HasSum (fun n ↦ φ (A n)) (φ Set.univ + φ Set.univ) := by
    have hfun : (fun n ↦ φ (A n)) =
        fun n ↦ (if n = 0 then φ Set.univ else 0) + if n = 1 then φ Set.univ else 0 := by
      funext n
      by_cases h0 : n = 0
      · simp [A, h0]
      · by_cases h1 : n = 1
        · simp [A, h1]
        · simp [A, h0, h1]
    rw [hfun]
    exact (hasSum_ite_eq 0 (φ Set.univ)).add (hasSum_ite_eq 1 (φ Set.univ))
  refine ⟨ULift Unit, ⊤, φ, A, ?_⟩
  constructor
  · intro n
    by_cases h0 : n = 0
    · simp [A, h0]
    · by_cases h1 : n = 1
      · simp [A, h1]
      · simp [A, h0, h1]
  constructor
  · exact hsum.summable
  · have hAuniv : (⋃ n, A n) = Set.univ := by
      exact Set.eq_univ_iff_forall.2 fun x ↦ mem_iUnion.2 ⟨0, by simp [A]⟩
    rw [hAuniv, hsum.tsum_eq]
    simp [φ]
