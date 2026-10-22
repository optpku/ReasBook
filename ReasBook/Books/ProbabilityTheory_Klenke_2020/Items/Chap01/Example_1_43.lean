/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory MeasurableSpace

/-- The modified finite interval `F_n = [-n / 2, (n + 1) / 2] ∩ ℤ` from the example, written as an
interval in `ℤ`. -/
def integerAlternatingSegment (n : ℕ) : Set ℤ :=
  Set.Icc (-((n : ℤ) / 2)) (((n : ℤ) + 1) / 2)

/-- The modified family from Example 1.43, namely
`F_n = [-n / 2, (n + 1) / 2] ∩ ℤ` on `ℤ`, used as a `π`-system generator of the full powerset with
finite exhausting pieces. -/
def integerAlternatingGenerator : Set (Set ℤ) :=
  Set.range integerAlternatingSegment

-- Proof sketch: the left endpoint moves weakly left and the right endpoint moves weakly right
-- with `n`, so the intervals form an increasing sequence.
/-- The modified intervals `F_n` form an increasing sequence. -/
theorem integerAlternatingSegment_monotone :
    Monotone integerAlternatingSegment := by
  intro m n hmn x hx
  -- Rewrite membership in both intervals as endpoint inequalities and compare the endpoints.
  rw [integerAlternatingSegment, Set.mem_Icc] at hx ⊢
  omega

-- Proof sketch: intervals in `ℤ` are finite because `ℤ` is a locally finite order.
/-- Each modified interval `F_n` is a finite subset of `ℤ`. -/
theorem integerAlternatingSegment_finite (n : ℕ) :
    (integerAlternatingSegment n).Finite := by
  -- The generator sets are closed integer intervals, hence finite.
  rw [integerAlternatingSegment]
  exact Set.finite_Icc (-((n : ℤ) / 2)) (((n : ℤ) + 1) / 2)

-- Proof sketch: any two members of the increasing chain have nonempty intersection, since they all
-- contain `0`.
/-- The modified generator family is a `π`-system. -/
theorem integerAlternatingGenerator_isPiSystem :
    IsPiSystem integerAlternatingGenerator := by
  intro s hs t ht _
  rcases hs with ⟨m, rfl⟩
  rcases ht with ⟨n, rfl⟩
  by_cases hmn : m ≤ n
  · -- In the monotone branch, the smaller interval is exactly the intersection.
    have hsubset : integerAlternatingSegment m ⊆ integerAlternatingSegment n :=
      integerAlternatingSegment_monotone hmn
    rw [Set.inter_eq_left.mpr hsubset]
    exact Set.mem_range_self m
  · -- Otherwise the other interval is smaller and controls the intersection.
    have hsubset : integerAlternatingSegment n ⊆ integerAlternatingSegment m :=
      integerAlternatingSegment_monotone (le_of_not_ge hmn)
    rw [Set.inter_eq_right.mpr hsubset]
    exact Set.mem_range_self n

private theorem zero_mem_integerAlternatingSegment (n : ℕ) :
    (0 : ℤ) ∈ integerAlternatingSegment n := by
  rw [integerAlternatingSegment, Set.mem_Icc]
  omega

/-- Helper for Example 1.43: the even-indexed alternating segment is the symmetric interval
`[-k, k] ∩ ℤ`. -/
private theorem integerAlternatingSegment_even (k : ℕ) :
    integerAlternatingSegment (2 * k) = Set.Icc (-(k : ℤ)) (k : ℤ) := by
  -- Normalize the integer-division endpoints in the even case.
  ext z
  rw [integerAlternatingSegment, Set.mem_Icc, Set.mem_Icc]
  omega

/-- Helper for Example 1.43: the odd-indexed alternating segment is the interval
`[-k, k + 1] ∩ ℤ`. -/
private theorem integerAlternatingSegment_odd (k : ℕ) :
    integerAlternatingSegment (2 * k + 1) = Set.Icc (-(k : ℤ)) ((k : ℤ) + 1) := by
  -- Normalize the integer-division endpoints in the odd case.
  ext z
  rw [integerAlternatingSegment, Set.mem_Icc, Set.mem_Icc]
  omega

/-- Helper for Example 1.43: the first alternating segment is exactly the singleton `{0}`. -/
private theorem integerAlternatingSegment_zero :
    integerAlternatingSegment 0 = ({0} : Set ℤ) := by
  -- The initial interval is exactly `[-0, 0]`.
  ext z
  rw [integerAlternatingSegment, Set.mem_Icc]
  simp
  omega

/-- Textbook companion: the modified generator family is intersection-closed. -/
theorem integerAlternatingGenerator_isInterClosed :
    IsInterClosed integerAlternatingGenerator := by
  refine ⟨?_⟩
  intro s t hs ht
  rcases hs with ⟨m, rfl⟩
  rcases ht with ⟨n, rfl⟩
  exact integerAlternatingGenerator_isPiSystem _ (mem_range_self m) _ (mem_range_self n)
    ⟨0, zero_mem_integerAlternatingSegment m, zero_mem_integerAlternatingSegment n⟩

/-- Helper for Example 1.43: each odd step adds exactly the next positive integer. -/
private theorem integerAlternatingSegment_rightStepSingleton (k : ℕ) :
    integerAlternatingSegment (2 * k + 1) \ integerAlternatingSegment (2 * k) =
      ({((k : ℤ) + 1)} : Set ℤ) := by
  -- Compare the normalized odd and even intervals pointwise.
  ext z
  rw [integerAlternatingSegment_odd, integerAlternatingSegment_even]
  rw [Set.mem_diff, Set.mem_Icc, Set.mem_Icc]
  simp
  omega

/-- Helper for Example 1.43: each even step after an odd one adds exactly the next negative
integer. -/
private theorem integerAlternatingSegment_leftStepSingleton (k : ℕ) :
    integerAlternatingSegment (2 * k + 2) \ integerAlternatingSegment (2 * k + 1) =
      ({-((k : ℤ) + 1)} : Set ℤ) := by
  -- Compare the normalized neighboring intervals pointwise.
  ext z
  rw [show 2 * k + 2 = 2 * (k + 1) by omega]
  rw [integerAlternatingSegment_even (k + 1), integerAlternatingSegment_odd]
  rw [Set.mem_diff, Set.mem_Icc, Set.mem_Icc]
  simp
  omega

/-- Helper for Example 1.43: every singleton in `ℤ` is measurable in the sigma-algebra generated
by the alternating segments. -/
private theorem singleton_measurable_generateFrom_integerAlternatingGenerator (z : ℤ) :
    MeasurableSet[MeasurableSpace.generateFrom integerAlternatingGenerator] ({z} : Set ℤ) := by
  have h_segment :
      ∀ n : ℕ,
        MeasurableSet[MeasurableSpace.generateFrom integerAlternatingGenerator]
          (integerAlternatingSegment n) :=
    fun n ↦ MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self n)
  by_cases hz0 : z = 0
  · -- The origin already appears as the first generator set.
    rw [hz0]
    simpa [integerAlternatingSegment_zero] using h_segment 0
  · by_cases hzpos : 0 < z
    · -- A positive integer appears as the new point added at an odd step.
      let k : ℕ := z.toNat - 1
      have hz_eq : z = (k : ℤ) + 1 := by
        -- Convert the positive integer to its predecessor in `ℕ`.
        calc
          z = ((z.toNat : ℕ) : ℤ) := by
            symm
            exact Int.toNat_of_nonneg (le_of_lt hzpos)
          _ = (k : ℤ) + 1 := by
            dsimp [k]
            rw [Int.toNat_pred_coe_of_pos hzpos]
            omega
      have h_singleton :
          MeasurableSet[MeasurableSpace.generateFrom integerAlternatingGenerator]
            ({((k : ℤ) + 1)} : Set ℤ) := by
        -- Take the difference of two consecutive measurable generator sets.
        simpa [integerAlternatingSegment_rightStepSingleton] using
          (h_segment (2 * k + 1)).diff (h_segment (2 * k))
      simpa [hz_eq] using h_singleton
    · -- A negative integer appears as the new point added at the next even step.
      have hzneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hzpos) (by simpa [eq_comm] using hz0)
      let k : ℕ := (-z).toNat - 1
      have hz_eq : z = -((k : ℤ) + 1) := by
        -- Convert the positive integer `-z` to its predecessor in `ℕ`.
        have hneg : 0 < -z := by omega
        calc
          z = -(-z) := by simp
          _ = -(((-z).toNat : ℕ) : ℤ) := by
            rw [Int.toNat_of_nonneg (by omega : 0 ≤ -z)]
          _ = -((k : ℤ) + 1) := by
            dsimp [k]
            rw [Int.toNat_pred_coe_of_pos hneg]
            omega
      have h_singleton :
          MeasurableSet[MeasurableSpace.generateFrom integerAlternatingGenerator]
            ({-((k : ℤ) + 1)} : Set ℤ) := by
        -- Again use the successive difference inside the generating chain.
        simpa [integerAlternatingSegment_leftStepSingleton] using
          (h_segment (2 * k + 2)).diff (h_segment (2 * k + 1))
      simpa [hz_eq] using h_singleton

-- Proof sketch: the family is increasing and `F_{2k}` and `F_{2k+1}` add one new singleton at a
-- time, so every singleton is measurable in the generated `σ`-algebra; then Exercise 1.1.4 gives
-- the full powerset on the countable discrete space `ℤ`.
/-- The modified generator family generates the full measurable space on `ℤ`. -/
theorem generateFrom_integerAlternatingGenerator_eq_top :
    MeasurableSpace.generateFrom integerAlternatingGenerator = ⊤ := by
  rw [eq_top_iff]
  intro s hs
  -- Every subset of `ℤ` is a countable union of measurable singletons.
  rw [← Set.biUnion_of_singleton s]
  refine MeasurableSet.biUnion (Set.to_countable s) fun z hz ↦ ?_
  exact singleton_measurable_generateFrom_integerAlternatingGenerator z

-- Proof sketch: the intervals are increasing and their endpoints tend to `-∞` and `+∞`, so every
-- integer eventually lies in the chain.
/-- The modified intervals exhaust `ℤ`. -/
theorem iUnion_integerAlternatingSegment_eq_univ :
    (⋃ n : ℕ, integerAlternatingSegment n) = (Set.univ : Set ℤ) := by
  ext z
  constructor
  · intro hz
    simp
  · intro hz
    -- The even segment indexed by `2 * |z|` already contains `z`.
    refine Set.mem_iUnion.mpr ⟨2 * Int.natAbs z, ?_⟩
    rw [integerAlternatingSegment_even]
    rw [Set.mem_Icc]
    constructor
    · have hleft' : -z ≤ (Int.natAbs (-z) : ℤ) := by
        exact Int.le_natAbs
      have hleft : -z ≤ (Int.natAbs z : ℤ) := by
        simpa using hleft'
      omega
    · have hright : z ≤ (Int.natAbs z : ℤ) := by
        exact Int.le_natAbs
      exact hright

/-- Helper for Example 1.43: a sigma-finite measure is finite on every finite set. -/
private theorem measure_lt_top_of_finite {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {s : Set α} (hs : s.Finite) :
    μ s < ⊤ := by
  -- Reduce finite sets to repeated unions of singletons.
  refine Set.Finite.induction_on (s := s) hs ?_ ?_
  · simp
  · intro a s ha hs' ih
    have h_singleton : μ ({a} : Set α) < ⊤ := MeasureTheory.measure_singleton_lt_top
    have h_insert : μ (insert a s) < ⊤ := by
      simpa [Set.singleton_union, ha] using MeasureTheory.measure_union_lt_top h_singleton ih
    simpa using h_insert

-- Proof sketch: on the countable space `ℤ`, `SigmaFinite` is equivalent to finite mass on each
-- singleton; combine this with finiteness of `F_n` and finite additivity on finite unions.
/-- Every sigma-finite measure on `ℤ` assigns finite mass to each modified interval `F_n`. -/
theorem measure_integerAlternatingSegment_lt_top (μ : Measure ℤ) [SigmaFinite μ] (n : ℕ) :
    μ (integerAlternatingSegment n) < ⊤ := by
  -- Each generator set is finite, so the generic finite-set lemma applies directly.
  exact measure_lt_top_of_finite μ (integerAlternatingSegment_finite n)

-- Proof sketch: Example 1.43 verifies the standard uniqueness-theorem hypothesis by taking the
-- concrete spanning sequence `F_n` itself.
/-- Example 1.43: every sigma-finite measure on `ℤ` has finite spanning sets inside the modified
generator family, witnessed by the sequence `F_n`. -/
def finiteSpanningSetsIn_integerAlternatingGenerator (μ : Measure ℤ) [SigmaFinite μ] :
    μ.FiniteSpanningSetsIn integerAlternatingGenerator :=
  .mk integerAlternatingSegment
    (fun n ↦ ⟨n, rfl⟩)
    (measure_integerAlternatingSegment_lt_top μ)
    iUnion_integerAlternatingSegment_eq_univ
