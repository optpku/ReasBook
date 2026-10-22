/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Data.Set.Accumulate
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory

open scoped ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: each measure in the sequence vanishes on `∅`, so the constant zero sequence is the
-- unique limit of the values on `∅`.
private theorem finiteMeasurePointwiseLimit_empty
    (μ : ℕ → Measure Ω)
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x)) :
    limUnder atTop (fun n ↦ μ n ∅) = 0 := by
  have hμlim : Tendsto (fun n ↦ μ n ∅) atTop (𝓝 (limUnder atTop (fun n ↦ μ n ∅))) :=
    tendsto_nhds_limUnder (hlim ∅ MeasurableSet.empty)
  have hμ : Tendsto (fun n ↦ μ n ∅) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simp
  exact tendsto_nhds_unique hμlim hμ

-- Proof sketch: for each `n`, use countable additivity of `μ n` on the disjoint measurable family
-- `f`; then pass to the limit in `n`. Finiteness of the measures gives the continuity-from-above
-- control needed to justify exchanging the setwise limit with the infinite sum.
/-- Helper for Exercise 1.3.3: the pointwise limit set-function is finitely additive on measurable
disjoint unions. -/
private theorem finiteMeasurePointwiseLimit_union
    (μ : ℕ → Measure Ω)
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x))
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    limUnder atTop (fun n ↦ μ n (A ∪ B)) =
      limUnder atTop (fun n ↦ μ n A) + limUnder atTop (fun n ↦ μ n B) := by
  -- Both sides are limits of the same sequence after rewriting `μ n (A ∪ B)` by finite additivity.
  have hUnion :
      Tendsto (fun n ↦ μ n (A ∪ B)) atTop
        (𝓝 (limUnder atTop (fun n ↦ μ n (A ∪ B)))) :=
    tendsto_nhds_limUnder (hlim (A ∪ B) (hA.union hB))
  have hA' : Tendsto (fun n ↦ μ n A) atTop (𝓝 (limUnder atTop (fun n ↦ μ n A))) :=
    tendsto_nhds_limUnder (hlim A hA)
  have hB' : Tendsto (fun n ↦ μ n B) atTop (𝓝 (limUnder atTop (fun n ↦ μ n B))) :=
    tendsto_nhds_limUnder (hlim B hB)
  have hAdd :
      Tendsto (fun n ↦ μ n (A ∪ B)) atTop
        (𝓝 (limUnder atTop (fun n ↦ μ n A) + limUnder atTop (fun n ↦ μ n B))) := by
    simpa [measure_union hAB hB] using hA'.add hB'
  exact tendsto_nhds_unique hUnion hAdd

/-- Helper for Exercise 1.3.3: the pointwise limit set-function agrees with finite accumulated
prefix sums on a pairwise disjoint measurable family. -/
private theorem finiteMeasurePointwiseLimit_prefixUnion
    (μ : ℕ → Measure Ω)
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x))
    (f : ℕ → Set Ω) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (fun i j ↦ Disjoint (f i) (f j))) :
    ∀ n : ℕ,
      limUnder atTop (fun k ↦ μ k (Set.accumulate f n)) =
        ∑ i ∈ Finset.range (n + 1), limUnder atTop (fun k ↦ μ k (f i)) := by
  intro n
  induction n with
  | zero =>
      -- The empty prefix contributes no mass on either side.
      simp [Set.accumulate_zero_nat]
  | succ n ih =>
      -- Split the next accumulated prefix into the old prefix and the new disjoint set `f (n + 1)`.
      have hPrefixMeas : MeasurableSet (Set.accumulate f n) := by
        rw [Set.accumulate_eq_biInter_lt]
        measurability
      have hDisj : Disjoint (Set.accumulate f n) (f (n + 1)) := by
        exact Set.disjoint_accumulate hd (Nat.lt_succ_self n)
      calc
        limUnder atTop (fun k ↦ μ k (Set.accumulate f (n + 1)))
            = limUnder atTop (fun k ↦ μ k (Set.accumulate f n ∪ f (n + 1))) := by
              simp [Set.accumulate_succ]
        _ = limUnder atTop (fun k ↦ μ k (Set.accumulate f n))
              + limUnder atTop (fun k ↦ μ k (f (n + 1))) :=
              finiteMeasurePointwiseLimit_union μ hlim hPrefixMeas (hf (n + 1)) hDisj
        _ = ∑ i ∈ Finset.range (n + 1), limUnder atTop (fun k ↦ μ k (f i))
              + limUnder atTop (fun k ↦ μ k (f (n + 1))) := by rw [ih]
        _ = ∑ i ∈ Finset.range ((n + 1) + 1), limUnder atTop (fun k ↦ μ k (f i)) := by
              simp [Finset.sum_range_succ, add_assoc]

/-- Helper for Exercise 1.3.3: continuity at `∅` for the pointwise limit set-function on a
decreasing measurable sequence. -/
private theorem finiteMeasurePointwiseLimit_antitoneValues
    (μ : ℕ → Measure Ω)
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x))
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hanti : Antitone s) :
    Antitone (fun n ↦ limUnder atTop (fun k ↦ μ k (s n))) := by
  intro m n hmn
  -- Pass the pointwise monotonicity of `μ k (s n)` to the setwise limit `ν (s n)`.
  have hm :
      Tendsto (fun k ↦ μ k (s m)) atTop
        (𝓝 (limUnder atTop (fun k ↦ μ k (s m)))) :=
    tendsto_nhds_limUnder (hlim (s m) (hs m))
  have hn :
      Tendsto (fun k ↦ μ k (s n)) atTop
        (𝓝 (limUnder atTop (fun k ↦ μ k (s n)))) :=
    tendsto_nhds_limUnder (hlim (s n) (hs n))
  exact le_of_tendsto_of_tendsto' hn hm fun k ↦ measure_mono (hanti hmn)

/-- Helper for Exercise 1.3.3: an antitone `ℝ≥0∞` sequence that does not converge to `0` stays
uniformly away from `0`. -/
private theorem finiteMeasurePointwiseLimit_existsPosLowerBound
    (a : ℕ → ℝ≥0∞) (hanti : Antitone a)
    (hzero : ¬ Tendsto a atTop (𝓝 0)) :
    ∃ ε > 0, ∀ n, ε ≤ a n := by
  -- Rewrite the convergence failure using the antitone characterization of `a n → 0`.
  rw [ENNReal.tendsto_atTop_zero_iff_lt_of_antitone hanti] at hzero
  push Not at hzero
  exact hzero

/-- Helper for Exercise 1.3.3: each fixed finite measure vanishes on a decreasing measurable family
with empty intersection. -/
private theorem finiteMeasurePointwiseLimit_fixedMeasureTendstoZero
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hanti : Antitone s) (h_empty : (⋂ n, s n) = ∅) :
    Tendsto (fun n ↦ ν (s n)) atTop (𝓝 0) := by
  -- Apply continuity from above to the fixed measure `ν`.
  have hcont :
      Tendsto (fun n ↦ ν (s n)) atTop (𝓝 (ν (⋂ n, s n))) :=
    tendsto_measure_iInter_atTop
      (fun n ↦ (hs n).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
  simpa [h_empty] using hcont

/-- Helper for Exercise 1.3.3: on the countable discrete space `ℕ`, a setwise limit is determined
by the limits of the singleton masses. -/
private theorem countableSetwiseLimit_finsetApply
    (νNat : ℕ → Measure ℕ)
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (s : Finset ℕ) :
    limUnder atTop (fun n ↦ νNat n (s : Set ℕ)) =
      ∑ i ∈ s, limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ)) := by
  classical
  let hlimMeas : ∀ A : Set ℕ, MeasurableSet A → ∃ x : ℝ≥0∞,
      Tendsto (fun n ↦ νNat n A) atTop (𝓝 x) := fun A _ ↦ hlim A
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty finite block has zero mass for every measure in the sequence.
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0)).limUnder_eq
  | @insert a s ha ih =>
      have hDisj : Disjoint ({a} : Set ℕ) (s : Set ℕ) := by
        -- Proof comment: `a` is outside the old finite block, so the new singleton is disjoint.
        refine Set.disjoint_left.2 ?_
        intro x hx hx'
        simp only [Set.mem_singleton_iff] at hx
        subst hx
        exact ha hx'
      -- Proof comment: rewrite the inserted finite block as a disjoint union and use finite
      -- additivity of the pointwise limit set-function.
      calc
        limUnder atTop (fun n ↦ νNat n ((insert a s : Finset ℕ) : Set ℕ))
            = limUnder atTop (fun n ↦ νNat n ({a} ∪ (s : Set ℕ))) := by
              simp [Finset.coe_insert]
        _ = limUnder atTop (fun n ↦ νNat n ({a} : Set ℕ))
              + limUnder atTop (fun n ↦ νNat n (s : Set ℕ)) :=
              finiteMeasurePointwiseLimit_union νNat hlimMeas
                MeasurableSet.of_discrete MeasurableSet.of_discrete hDisj
        _ = limUnder atTop (fun n ↦ νNat n ({a} : Set ℕ))
              + ∑ i ∈ s, limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ)) := by
              rw [ih]
        _ = ∑ i ∈ insert a s, limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ)) := by
              simp [Finset.sum_insert, ha]

/-- Helper for Exercise 1.3.3: finite prefixes of a discrete set give lower bounds for the full
setwise limit. -/
private theorem countableSetwiseLimit_tsumLe
    (νNat : ℕ → Measure ℕ)
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ) :
    (∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) ≤
      limUnder atTop (fun n ↦ νNat n A) := by
  classical
  let a : ℕ → ℝ≥0∞ := fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N ↦ ?_
  let s : Finset ℕ := (Finset.range N).filter fun i ↦ i ∈ A
  have hs_subset : ((s : Set ℕ) ⊆ A) := by
    -- Proof comment: the filtered finite prefix only keeps points that already belong to `A`.
    intro i hi
    exact (Finset.mem_filter.1 hi).2
  have hs_le :
      limUnder atTop (fun n ↦ νNat n (s : Set ℕ)) ≤
        limUnder atTop (fun n ↦ νNat n A) := by
    have hs_tendsto :
        Tendsto (fun n ↦ νNat n (s : Set ℕ)) atTop
          (𝓝 (limUnder atTop (fun n ↦ νNat n (s : Set ℕ)))) :=
      tendsto_nhds_limUnder (hlim (s : Set ℕ))
    have hA_tendsto :
        Tendsto (fun n ↦ νNat n A) atTop (𝓝 (limUnder atTop (fun n ↦ νNat n A))) :=
      tendsto_nhds_limUnder (hlim A)
    -- Proof comment: pointwise monotonicity on the finite prefix survives in the setwise limit.
    exact le_of_tendsto_of_tendsto' hs_tendsto hA_tendsto fun n ↦ measure_mono hs_subset
  -- Proof comment: identify the finite prefix by the finite-set formula, then compare with `A`.
  calc
    ∑ i ∈ Finset.range N, A.indicator a i = ∑ i ∈ s, a i := by
      simp [a, s, Finset.sum_filter, Set.indicator]
    _ = limUnder atTop (fun n ↦ νNat n (s : Set ℕ)) := by
      rw [countableSetwiseLimit_finsetApply νNat hlim s]
    _ ≤ limUnder atTop (fun n ↦ νNat n A) := hs_le

/-- Helper for Exercise 1.3.3: if the singleton-mass series on `A` is infinite, then the setwise
limit on `A` is already `⊤`. -/
private theorem countableSetwiseLimit_eqTopOfTsumEqTop
    (νNat : ℕ → Measure ℕ)
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ)
    (hA : ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i = ⊤) :
    limUnder atTop (fun n ↦ νNat n A) = ⊤ := by
  -- Proof comment: every finite prefix is bounded by the full limit, so an infinite singleton sum
  -- forces the full limit value to be `⊤`.
  apply top_unique
  rw [← hA]
  exact countableSetwiseLimit_tsumLe νNat hlim A

/-- Helper for Exercise 1.3.3: the atomic candidate on `A` built from the singleton limits. -/
private noncomputable abbrev countableSetwiseLimitAtomicMeasure
    (νNat : ℕ → Measure ℕ) (A : Set ℕ) : Measure ℕ :=
  Measure.sum
    (fun i ↦
      A.indicator (fun j ↦ limUnder atTop (fun n ↦ νNat n ({j} : Set ℕ))) i • Measure.dirac i)

/-- Helper for Exercise 1.3.3: package the restricted measures `νNat n | A` as finite measures. -/
private noncomputable abbrev countableSetwiseLimitRestrictFiniteMeasure
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)] (A : Set ℕ) (n : ℕ) :
    FiniteMeasure ℕ :=
  ⟨(νNat n).restrict A, inferInstance⟩

/-- Helper for Exercise 1.3.3: the atomic candidate has the prescribed singleton masses. -/
private theorem countableSetwiseLimit_atomicMeasure_singleton
    (νNat : ℕ → Measure ℕ) (A : Set ℕ) (i : ℕ) :
    countableSetwiseLimitAtomicMeasure νNat A ({i} : Set ℕ) =
      A.indicator (fun j ↦ limUnder atTop (fun n ↦ νNat n ({j} : Set ℕ))) i := by
  -- Proof comment: only the Dirac mass at `i` contributes on the singleton `{i}`.
  simpa [countableSetwiseLimitAtomicMeasure] using
    (Measure.sum_smul_dirac_singleton :
      Measure.sum
          (fun j : ℕ ↦
            A.indicator (fun k ↦ limUnder atTop (fun n ↦ νNat n ({k} : Set ℕ))) j •
              Measure.dirac j)
          ({i} : Set ℕ) =
        A.indicator (fun k ↦ limUnder atTop (fun n ↦ νNat n ({k} : Set ℕ))) i)

/-- Helper for Exercise 1.3.3: the atomic candidate evaluates on any set by summing its singleton
masses over that set. -/
private theorem countableSetwiseLimit_atomicMeasure_apply
    (νNat : ℕ → Measure ℕ) (A s : Set ℕ) :
    countableSetwiseLimitAtomicMeasure νNat A s =
      ∑' i, s.indicator
        (fun j ↦ A.indicator (fun k ↦ limUnder atTop (fun n ↦ νNat n ({k} : Set ℕ))) j) i := by
  -- Proof comment: on a countable discrete space, a measure is the sum of its singleton values.
  calc
    countableSetwiseLimitAtomicMeasure νNat A s
      = ∑' i, s.indicator
          (fun j ↦ countableSetwiseLimitAtomicMeasure νNat A ({j} : Set ℕ)) i := by
            symm
            exact Measure.tsum_indicator_apply_singleton
              (countableSetwiseLimitAtomicMeasure νNat A) s MeasurableSet.of_discrete
    _ = ∑' i, s.indicator
          (fun j ↦ A.indicator (fun k ↦ limUnder atTop (fun n ↦ νNat n ({k} : Set ℕ))) j) i := by
            refine tsum_congr ?_
            intro i
            by_cases hi : i ∈ s
            · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
              exact countableSetwiseLimit_atomicMeasure_singleton νNat A i
            · simp [Set.indicator, hi]

/-- Helper for Exercise 1.3.3: the total mass of the atomic candidate is the singleton series on
`A`. -/
private theorem countableSetwiseLimit_atomicMeasure_univ
    (νNat : ℕ → Measure ℕ) (A : Set ℕ) :
    countableSetwiseLimitAtomicMeasure νNat A Set.univ =
      ∑' i, A.indicator (fun j ↦ limUnder atTop (fun n ↦ νNat n ({j} : Set ℕ))) i := by
  -- Proof comment: evaluating on `univ` removes the outer indicator from the set argument.
  rw [countableSetwiseLimit_atomicMeasure_apply]
  simp

/-- Helper for Exercise 1.3.3: finiteness of the singleton series makes the atomic candidate a
finite measure. -/
private theorem countableSetwiseLimit_atomicMeasure_isFinite
    (νNat : ℕ → Measure ℕ) (A : Set ℕ)
    (hAfinite :
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i < ⊤) :
    IsFiniteMeasure (countableSetwiseLimitAtomicMeasure νNat A) := by
  -- Proof comment: the total mass of the atomic candidate is exactly the assumed finite series.
  refine ⟨?_⟩
  rw [countableSetwiseLimit_atomicMeasure_univ]
  exact hAfinite

/-- Helper for Exercise 1.3.3: package the atomic candidate as a finite measure once the singleton
series on `A` is finite. -/
private noncomputable abbrev countableSetwiseLimitAtomicFiniteMeasure
    (νNat : ℕ → Measure ℕ) (A : Set ℕ)
    (hAfinite :
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i < ⊤) :
    FiniteMeasure ℕ :=
  ⟨countableSetwiseLimitAtomicMeasure νNat A,
    countableSetwiseLimit_atomicMeasure_isFinite νNat A hAfinite⟩

/-- Helper for Exercise 1.3.3: the restricted finite measure has mass `νNat n A`. -/
private theorem countableSetwiseLimit_restrictFiniteMeasure_mass
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)] (A : Set ℕ) (n : ℕ) :
    (((countableSetwiseLimitRestrictFiniteMeasure νNat A n).mass : ℝ≥0∞)) = νNat n A := by
  -- Proof comment: the mass of the restriction is the value of the original measure on `A`.
  simp [countableSetwiseLimitRestrictFiniteMeasure, FiniteMeasure.ennreal_mass,
    Measure.restrict_apply]

/-- Helper for Exercise 1.3.3: the atomic finite measure has total mass equal to the singleton
series on `A`. -/
private theorem countableSetwiseLimit_atomicFiniteMeasure_mass
    (νNat : ℕ → Measure ℕ) (A : Set ℕ)
    (hAfinite :
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i < ⊤) :
    (((countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite).mass : ℝ≥0∞)) =
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i := by
  -- Proof comment: convert the finite-measure mass back to the underlying measure on `univ`.
  rw [FiniteMeasure.ennreal_mass]
  exact countableSetwiseLimit_atomicMeasure_univ νNat A

/-- Helper for Exercise 1.3.3: restricting to `A` turns a singleton mass into the indicator-weighted
singleton mass. -/
private theorem countableSetwiseLimit_restrictSingleton
    (νNat : ℕ → Measure ℕ) (A : Set ℕ) (n i : ℕ) :
    ((νNat n).restrict A) ({i} : Set ℕ) =
      A.indicator (fun j ↦ νNat n ({j} : Set ℕ)) i := by
  -- Proof comment: on a singleton, restriction either keeps the original mass or kills it.
  by_cases hi : i ∈ A
  · simp [Measure.restrict_apply, Set.indicator, hi]
  · simp [Measure.restrict_apply, Set.indicator, hi]

/-- Helper for Exercise 1.3.3: the singleton limits for the restricted measures are the
indicator-weighted singleton limits on `A`. -/
private theorem countableSetwiseLimit_restrictSingletonLimit
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)]
    (A : Set ℕ) (i : ℕ) :
    limUnder atTop (fun n ↦ ((νNat n).restrict A) ({i} : Set ℕ)) =
      A.indicator (fun j ↦ limUnder atTop (fun n ↦ νNat n ({j} : Set ℕ))) i := by
  -- Proof comment: after restriction, the singleton sequence is either unchanged or constantly
  -- zero depending on membership in `A`.
  by_cases hi : i ∈ A
  · have hEq :
        (fun n ↦ ((νNat n).restrict A) ({i} : Set ℕ)) =
          fun n ↦ νNat n ({i} : Set ℕ) := by
        funext n
        simp [Measure.restrict_apply, hi]
    rw [hEq]
    simp [Set.indicator, hi]
  · have hEq :
        (fun n ↦ ((νNat n).restrict A) ({i} : Set ℕ)) =
          fun _ : ℕ ↦ (0 : ℝ≥0∞) := by
        funext n
        simp [Measure.restrict_apply, hi]
    rw [hEq]
    simpa [Set.indicator, hi] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0)).limUnder_eq

/-- Helper for Exercise 1.3.3: finite blocks already satisfy the restricted atomic formula. -/
private theorem countableSetwiseLimit_finsetRestrictApply
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)]
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ) (s : Finset ℕ) :
    limUnder atTop (fun n ↦ ((νNat n).restrict A) (s : Set ℕ)) =
      ∑ i ∈ s, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i := by
  classical
  let νA : ℕ → Measure ℕ := fun n ↦ (νNat n).restrict A
  have hlimA : ∀ B : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νA n B) atTop (𝓝 x) := by
    intro B
    rcases hlim (B ∩ A) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [νA, Measure.restrict_apply, Set.inter_comm] using hx
  -- Proof comment: finite additivity already identifies the restricted finite blocks.
  calc
    limUnder atTop (fun n ↦ ((νNat n).restrict A) (s : Set ℕ))
      = ∑ i ∈ s, limUnder atTop (fun n ↦ νA n ({i} : Set ℕ)) := by
          simpa [νA] using countableSetwiseLimit_finsetApply νA hlimA s
    _ = ∑ i ∈ s, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact countableSetwiseLimit_restrictSingletonLimit νNat A i

/-- Helper for Exercise 1.3.3: split the limit on a subset of `Nat` into a finite prefix and the
remaining tail. -/
private theorem countableSetwiseLimit_splitPrefixTail
    (νNat : ℕ → Measure ℕ)
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ) (M : ℕ) :
    limUnder atTop (fun n ↦ νNat n A) =
      (∑ i ∈ Finset.range M,
          A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) +
        limUnder atTop (fun n ↦ νNat n (A ∩ Set.Ici M)) := by
  classical
  let sM : Finset ℕ := (Finset.range M).filter fun i ↦ i ∈ A
  have hDecomp : A = (sM : Set ℕ) ∪ (A ∩ Set.Ici M) := by
    -- Proof comment: every point of `A` lies either in the first `M` points or in the tail.
    ext i
    constructor
    · intro hiA
      by_cases hiM : i < M
      · left
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hiM, hiA⟩
      · right
        exact ⟨hiA, le_of_not_gt hiM⟩
    · intro hi
      rcases hi with hi | hi
      · exact (Finset.mem_filter.1 hi).2
      · exact hi.1
  have hDisj : Disjoint (sM : Set ℕ) (A ∩ Set.Ici M) := by
    -- Proof comment: the filtered prefix only contains indices `< M`, while the tail starts at
    -- `M`.
    refine Set.disjoint_left.2 ?_
    intro i hiPrefix hiTail
    have hiPrefix' : i ∈ sM := hiPrefix
    have hiLt : i < M := by
      exact Finset.mem_range.1 (Finset.mem_filter.1 hiPrefix').1
    have hiGe : M ≤ i := hiTail.2
    exact (Nat.not_lt_of_ge hiGe hiLt).elim
  -- Proof comment: finite additivity isolates the already-known finite prefix from the unknown
  -- tail.
  calc
    limUnder atTop (fun n ↦ νNat n A)
      = limUnder atTop (fun n ↦ νNat n ((sM : Set ℕ) ∪ (A ∩ Set.Ici M))) := by
          congr 1
          funext n
          exact congrArg (νNat n) hDecomp
    _ = limUnder atTop (fun n ↦ νNat n (sM : Set ℕ)) +
          limUnder atTop (fun n ↦ νNat n (A ∩ Set.Ici M)) :=
          finiteMeasurePointwiseLimit_union νNat (fun B _ ↦ hlim B)
            MeasurableSet.of_discrete MeasurableSet.of_discrete hDisj
    _ = (∑ i ∈ Finset.range M,
          A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) +
          limUnder atTop (fun n ↦ νNat n (A ∩ Set.Ici M)) := by
          rw [countableSetwiseLimit_finsetApply νNat hlim sM]
          simp [sM, Finset.sum_filter, Set.indicator]

/-- Helper for Exercise 1.3.3: a strict gap between the singleton series on `A` and the full
setwise limit on `A` forces every tail of `A` to keep uniformly positive limiting mass. -/
private theorem countableSetwiseLimit_eventuallyLargeTail
    (νNat : ℕ → Measure ℕ)
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ)
    (hAfinite :
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i < ⊤)
    (hGap :
      (∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) <
        limUnder atTop (fun n ↦ νNat n A)) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧
      ∀ M : ℕ, ε < limUnder atTop (fun n ↦ νNat n (A ∩ Set.Ici M)) := by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hGap with ⟨ε, hεpos, hεlt⟩
  refine ⟨(ε : ℝ≥0∞), by exact_mod_cast hεpos, ?_⟩
  intro M
  set prefMass :=
    ∑ i ∈ Finset.range M,
      A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i with hprefix_def
  have hprefix_le :
      prefMass ≤
        ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i := by
    -- Proof comment: every finite prefix is dominated by the full singleton series.
    rw [ENNReal.tsum_eq_iSup_nat]
    exact le_iSup (fun N ↦
      ∑ i ∈ Finset.range N,
        A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) M
  have hprefix_lt_top : prefMass < ⊤ := lt_of_le_of_lt hprefix_le hAfinite
  have hprefix_add_lt :
      prefMass + (ε : ℝ≥0∞) < limUnder atTop (fun n ↦ νNat n A) := by
    -- Proof comment: the chosen gap survives after replacing the full singleton sum by a prefix.
    exact lt_of_le_of_lt (add_le_add_left hprefix_le (ε : ℝ≥0∞)) hεlt
  have htail_lt :
      prefMass + (ε : ℝ≥0∞) <
        prefMass + limUnder atTop (fun n ↦ νNat n (A ∩ Set.Ici M)) := by
    -- Proof comment: substitute the prefix-tail decomposition of the total limit.
    rw [countableSetwiseLimit_splitPrefixTail νNat hlim A M] at hprefix_add_lt
    simpa [hprefix_def, add_comm, add_left_comm, add_assoc] using hprefix_add_lt
  exact (ENNReal.add_lt_add_iff_left (lt_top_iff_ne_top.1 hprefix_lt_top)).1 htail_lt

/-- Helper for Exercise 1.3.3: if one concrete tail already has mass `> ε` for one fixed measure,
then a finite block inside that tail still has mass `> ε`. -/
private theorem countableSetwiseLimit_extractFiniteBlock
    (νNat : ℕ → Measure ℕ)
    (A : Set ℕ) (n M : ℕ) {ε : ℝ≥0∞}
    (hε : ε < νNat n (A ∩ Set.Ici M)) :
    ∃ t : Finset ℕ, ((t : Set ℕ) ⊆ A ∩ Set.Ici M) ∧ ε < νNat n (t : Set ℕ) := by
  classical
  have hTsum :
      ∑' i, (A ∩ Set.Ici M).indicator (fun i ↦ νNat n ({i} : Set ℕ)) i =
        νNat n (A ∩ Set.Ici M) :=
    Measure.tsum_indicator_apply_singleton (νNat n) (A ∩ Set.Ici M) MeasurableSet.of_discrete
  have hPrefixWitness :
      ε <
        ⨆ N : ℕ,
          ∑ i ∈ Finset.range N,
            (A ∩ Set.Ici M).indicator (fun i ↦ νNat n ({i} : Set ℕ)) i := by
    -- Proof comment: the tail mass is the supremum of its finite singleton prefixes.
    rw [← hTsum, ENNReal.tsum_eq_iSup_nat] at hε
    exact hε
  rcases lt_iSup_iff.1 hPrefixWitness with ⟨N, hN⟩
  let t : Finset ℕ := (Finset.range N).filter fun i ↦ i ∈ A ∩ Set.Ici M
  have ht_subset : ((t : Set ℕ) ⊆ A ∩ Set.Ici M) := by
    -- Proof comment: the extracted prefix block stays inside the chosen tail.
    intro i hi
    exact (Finset.mem_filter.1 hi).2
  have hBlockMass :
      ∑ i ∈ Finset.range N, (A ∩ Set.Ici M).indicator (fun i ↦ νNat n ({i} : Set ℕ)) i =
        νNat n (t : Set ℕ) := by
    -- Proof comment: on a finite set, the tail mass is the sum of the singleton masses.
    calc
      ∑ i ∈ Finset.range N, (A ∩ Set.Ici M).indicator (fun i ↦ νNat n ({i} : Set ℕ)) i
        = ∑ i ∈ t, νNat n ({i} : Set ℕ) := by
            simp [t, Finset.sum_filter, Set.indicator]
      _ = νNat n (t : Set ℕ) := by
            exact (sum_measure_singleton : ∑ i ∈ t, νNat n ({i} : Set ℕ) = νNat n (t : Set ℕ))
  refine ⟨t, ht_subset, ?_⟩
  rw [← hBlockMass]
  exact hN

/-- Helper for Exercise 1.3.3: a positive tail limit yields one concrete finite block with large
mass for one selected measure. -/
private theorem countableSetwiseLimit_chooseLargeTailBlock
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)]
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ) (M : ℕ) {ε : ℝ≥0∞}
    (hε : ε < limUnder atTop (fun n ↦ νNat n (A ∩ Set.Ici M))) :
    ∃ n : ℕ, ∃ t : Finset ℕ, ((t : Set ℕ) ⊆ A ∩ Set.Ici M) ∧ ε < νNat n (t : Set ℕ) := by
  classical
  have hTailTendsto :
      Tendsto (fun n ↦ νNat n (A ∩ Set.Ici M)) atTop
        (𝓝 (limUnder atTop (fun n ↦ νNat n (A ∩ Set.Ici M)))) :=
    tendsto_nhds_limUnder (hlim (A ∩ Set.Ici M))
  have hEventually :
      ∀ᶠ n in atTop, ε < νNat n (A ∩ Set.Ici M) :=
    hTailTendsto (Ioi_mem_nhds hε)
  rcases Filter.eventually_atTop.1 hEventually with ⟨n, hn⟩
  have hTailMass : ε < νNat n (A ∩ Set.Ici M) := hn n le_rfl
  rcases countableSetwiseLimit_extractFiniteBlock νNat A n M hTailMass with ⟨t, ht, hmass⟩
  exact ⟨n, t, ht, hmass⟩

/-- Helper for Exercise 1.3.3: singleton convergence already determines the limit on every finite
subset of `ℕ`. -/
private theorem finiteMeasureNat_finsetApplyTendsto
    (μs : ℕ → FiniteMeasure ℕ) (μ : FiniteMeasure ℕ)
    (hs :
      ∀ i : ℕ,
        Tendsto (fun n ↦ ((μs n : Measure ℕ) ({i} : Set ℕ))) atTop
          (𝓝 ((μ : Measure ℕ) ({i} : Set ℕ))))
    (s : Finset ℕ) :
    Tendsto (fun n ↦ ((μs n : Measure ℕ) (s : Set ℕ))) atTop
      (𝓝 ((μ : Measure ℕ) (s : Set ℕ))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: every measure gives mass `0` to the empty finite set.
      simp
  | @insert a s ha ih =>
      have hDisj : Disjoint ({a} : Set ℕ) (s : Set ℕ) := by
        -- Proof comment: the new singleton is disjoint from the old finite block.
        refine Set.disjoint_left.2 ?_
        intro x hx hx'
        simp only [Set.mem_singleton_iff] at hx
        subst hx
        exact ha hx'
      have hUnionLeft :
          (fun n ↦ ((μs n : Measure ℕ) ((insert a s : Finset ℕ) : Set ℕ))) =
            fun n ↦
              ((μs n : Measure ℕ) ({a} : Set ℕ)) + ((μs n : Measure ℕ) (s : Set ℕ)) := by
        funext n
        simpa [Finset.coe_insert] using
          (measure_union hDisj MeasurableSet.of_discrete :
            ((μs n : Measure ℕ) ({a} ∪ (s : Set ℕ))) =
              ((μs n : Measure ℕ) ({a} : Set ℕ)) + ((μs n : Measure ℕ) (s : Set ℕ)))
      have hUnionRight :
          ((μ : Measure ℕ) (((insert a s : Finset ℕ) : Set ℕ))) =
            ((μ : Measure ℕ) ({a} : Set ℕ)) + ((μ : Measure ℕ) (s : Set ℕ)) := by
        simpa [Finset.coe_insert] using
          (measure_union hDisj MeasurableSet.of_discrete :
            ((μ : Measure ℕ) ({a} ∪ (s : Set ℕ))) =
              ((μ : Measure ℕ) ({a} : Set ℕ)) + ((μ : Measure ℕ) (s : Set ℕ)))
      -- Proof comment: rewrite the inserted block as a disjoint union and combine the singleton
      -- and finite-block limits.
      rw [hUnionLeft, hUnionRight]
      exact (hs a).add ih

/-- Helper for Exercise 1.3.3: singleton convergence plus total-mass convergence control the
full tail masses `Set.Ici M`. -/
private theorem finiteMeasureNat_tailMassTendstoOfSingletonMass
    (μs : ℕ → FiniteMeasure ℕ) (μ : FiniteMeasure ℕ)
    (hs :
      ∀ i : ℕ,
        Tendsto (fun n ↦ ((μs n : Measure ℕ) ({i} : Set ℕ))) atTop
          (𝓝 ((μ : Measure ℕ) ({i} : Set ℕ))))
    (hmass :
      Tendsto (fun n ↦ (((μs n).mass : ℝ≥0∞))) atTop (𝓝 ((μ.mass : ℝ≥0∞))))
    (M : ℕ) :
    Tendsto (fun n ↦ ((μs n : Measure ℕ) (Set.Ici M))) atTop
      (𝓝 ((μ : Measure ℕ) (Set.Ici M))) := by
  let sM : Finset ℕ := Finset.range M
  have hPrefix :
      Tendsto (fun n ↦ ((μs n : Measure ℕ) (sM : Set ℕ))) atTop
        (𝓝 ((μ : Measure ℕ) (sM : Set ℕ))) :=
    finiteMeasureNat_finsetApplyTendsto μs μ hs sM
  have hTailEq :
      ∀ ν : FiniteMeasure ℕ,
        ((ν : Measure ℕ) (Set.Ici M)) =
          (((ν.mass : ℝ≥0∞))) - ((ν : Measure ℕ) (sM : Set ℕ)) := by
    intro ν
    have hDisj : Disjoint (sM : Set ℕ) (Set.Ici M) := by
      -- Proof comment: `range M` and `Ici M` partition `ℕ` into the finite prefix and tail.
      refine Set.disjoint_left.2 ?_
      intro i hiPrefix hiTail
      have hiLt : i < M := Finset.mem_range.1 hiPrefix
      exact (Nat.not_lt_of_ge hiTail hiLt).elim
    have hUnion : (sM : Set ℕ) ∪ Set.Ici M = Set.univ := by
      -- Proof comment: every natural number lies either before `M` or inside the tail `Ici M`.
      ext i
      simp [sM]
    have hAdd :
        (((ν.mass : ℝ≥0∞))) =
          ((ν : Measure ℕ) (sM : Set ℕ)) + ((ν : Measure ℕ) (Set.Ici M)) := by
      calc
        (((ν.mass : ℝ≥0∞))) = (ν : Measure ℕ) Set.univ := by
          simp [FiniteMeasure.ennreal_mass]
        _ = (ν : Measure ℕ) ((sM : Set ℕ) ∪ Set.Ici M) := by rw [hUnion]
        _ = ((ν : Measure ℕ) (sM : Set ℕ)) + ((ν : Measure ℕ) (Set.Ici M)) := by
          rw [measure_union hDisj MeasurableSet.of_discrete]
    exact (ENNReal.sub_eq_of_eq_add_rev (measure_ne_top (ν : Measure ℕ) (sM : Set ℕ)) hAdd).symm
  -- Proof comment: identify each tail as total mass minus a convergent finite prefix.
  simpa [hTailEq] using
    ENNReal.Tendsto.sub hmass hPrefix (Or.inl (by simp : ((μ.mass : ℝ≥0∞)) ≠ ∞))

/-- Helper for Exercise 1.3.3: the tails `Set.Ici M` of a finite measure on `ℕ` vanish. -/
private theorem finiteMeasureNat_tailTendstoZero
    (μ : FiniteMeasure ℕ) :
    Tendsto (fun M ↦ ((μ : Measure ℕ) (Set.Ici M))) atTop (𝓝 0) := by
  -- Proof comment: the tails `Ici M` decrease to `∅`, so continuity from above forces their
  -- masses to converge to `0`.
  simpa using
    finiteMeasurePointwiseLimit_fixedMeasureTendstoZero
      (μ : Measure ℕ) (fun M ↦ Set.Ici M)
      (fun _ ↦ MeasurableSet.of_discrete)
      (fun _ _ hmn ↦ Set.Ici_subset_Ici.mpr hmn)
      (by
        ext i
        constructor
        · intro hi
          have hi' : ∀ n, i ∈ Set.Ici n := by
            simpa [Set.mem_iInter] using hi
          exact (Nat.not_succ_le_self i) (hi' (i + 1))
        · intro hi
          exact False.elim hi)

/-- Helper for Exercise 1.3.3: one can choose a far enough tail of `A` that is small both for the
atomic limit measure and for finitely many protected measures from the sequence. -/
private theorem countableSetwiseLimit_chooseProtectedTail
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)]
    (A : Set ℕ)
    (hAfinite :
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i < ⊤)
    (s : Finset ℕ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ M : ℕ,
      (∑' i, (A ∩ Set.Ici M).indicator
        (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) < δ ∧
      ∀ m ∈ s, νNat m (A ∩ Set.Ici M) < δ := by
  classical
  have hAtomicTail :
      Tendsto
        (fun M ↦
          ∑' i, (A ∩ Set.Ici M).indicator
            (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i)
        atTop (𝓝 0) := by
    -- Proof comment: the atomic finite measure has vanishing tails on `ℕ`, and its tail values are
    -- exactly the singleton-limit series on `A ∩ Ici M`.
    have hTailZero :
        Tendsto
          (fun M ↦
            ((countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite : FiniteMeasure ℕ) :
              Measure ℕ) (Set.Ici M))
          atTop (𝓝 0) :=
      finiteMeasureNat_tailTendstoZero
        (countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite)
    have hTailEq :
        ∀ M : ℕ,
          (((countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite : FiniteMeasure ℕ) :
            Measure ℕ) (Set.Ici M)) =
            ∑' i, (A ∩ Set.Ici M).indicator
              (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i := by
      intro M
      simpa [countableSetwiseLimitAtomicFiniteMeasure, Set.indicator_indicator,
        Set.inter_assoc, Set.inter_left_comm, Set.inter_comm, one_mul, mul_comm, mul_left_comm,
        mul_assoc] using countableSetwiseLimit_atomicMeasure_apply νNat A (Set.Ici M)
    exact Tendsto.congr' (Filter.Eventually.of_forall hTailEq) hTailZero
  have hAtomicEventually :
      ∀ᶠ M in atTop,
        (∑' i, (A ∩ Set.Ici M).indicator
          (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) < δ :=
    hAtomicTail (Iio_mem_nhds hδ)
  have hMeasuresEventually :
      ∀ᶠ M in atTop, ∀ m ∈ s, νNat m (A ∩ Set.Ici M) < δ := by
    induction s using Finset.induction_on with
    | empty =>
        exact Filter.Eventually.of_forall fun M m hm ↦ by
          simp at hm
    | @insert a s ha ih =>
        have hTailA :
            Tendsto (fun M ↦ νNat a (A ∩ Set.Ici M)) atTop (𝓝 0) := by
          -- Proof comment: every fixed finite measure from the sequence vanishes on the shrinking
          -- tails `A ∩ Ici M`.
          exact finiteMeasurePointwiseLimit_fixedMeasureTendstoZero
            (νNat a) (fun M ↦ A ∩ Set.Ici M)
            (fun _ ↦ MeasurableSet.of_discrete)
            (fun _ _ hMN ↦ by
              intro i hi
              exact ⟨hi.1, Set.Ici_subset_Ici.mpr hMN hi.2⟩)
            (by
              ext i
              constructor
              · intro hi
                have hiAll : ∀ M, i ∈ A ∩ Set.Ici M := by
                  simpa [Set.mem_iInter] using hi
                exact (Nat.not_succ_le_self i) (hiAll (i + 1)).2
              · intro hi
                exact False.elim hi)
        have hAEventually : ∀ᶠ M in atTop, νNat a (A ∩ Set.Ici M) < δ :=
          hTailA (Iio_mem_nhds hδ)
        filter_upwards [hAEventually, ih] with M hM hsM
        intro m hm
        rcases Finset.mem_insert.1 hm with rfl | hm'
        · exact hM
        · exact hsM m hm'
  have hEventually :
      ∀ᶠ M in atTop,
        (∑' i, (A ∩ Set.Ici M).indicator
          (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) < δ ∧
        ∀ m ∈ s, νNat m (A ∩ Set.Ici M) < δ :=
    hAtomicEventually.and hMeasuresEventually
  rcases Filter.eventually_atTop.1 hEventually with ⟨M, hM⟩
  exact ⟨M, hM M le_rfl⟩

/-- Helper for Exercise 1.3.3: if a finite block of `A` has atomic singleton sum `< δ`, then the
sequence of measures is eventually `< δ` on that block. -/
private theorem countableSetwiseLimit_finsetEventuallySmallOfAtomicBound
    (νNat : ℕ → Measure ℕ)
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ) (t : Finset ℕ) {δ : ℝ≥0∞}
    (htA : ((t : Set ℕ) ⊆ A))
    (hδ :
      (∑ i ∈ t, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) < δ) :
    ∀ᶠ n in atTop, νNat n (t : Set ℕ) < δ := by
  have hBlock :
      Tendsto (fun n ↦ νNat n (t : Set ℕ)) atTop
        (𝓝 (∑ i ∈ t,
          A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i)) := by
    have hApply :
        Tendsto (fun n ↦ νNat n (t : Set ℕ)) atTop
          (𝓝 (∑ i ∈ t, limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ)))) := by
      rw [← countableSetwiseLimit_finsetApply νNat hlim t]
      exact tendsto_nhds_limUnder (hlim (t : Set ℕ))
    have hSumEq :
        (∑ i ∈ t, limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) =
          ∑ i ∈ t, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [Set.indicator, htA (by simpa using hi)]
    simpa [hSumEq] using hApply
  exact hBlock (Iio_mem_nhds hδ)

/-- Helper for Exercise 1.3.3: convergence of singleton masses implies convergence of bounded
nonnegative integrals on every finite prefix. -/
private theorem finiteMeasureNat_finsetLintegralTendsto
    (μs : ℕ → FiniteMeasure ℕ) (μ : FiniteMeasure ℕ)
    (hs :
      ∀ i : ℕ,
        Tendsto (fun n ↦ ((μs n : Measure ℕ) ({i} : Set ℕ))) atTop
          (𝓝 ((μ : Measure ℕ) ({i} : Set ℕ))))
    (f : BoundedContinuousFunction ℕ NNReal) (s : Finset ℕ) :
    Tendsto (fun n ↦ ∫⁻ x in (s : Set ℕ), ↑(f x) ∂(μs n : Measure ℕ)) atTop
      (𝓝 (∫⁻ x in (s : Set ℕ), ↑(f x) ∂(μ : Measure ℕ))) := by
  have hTerms :
      ∀ i ∈ s,
        Tendsto (fun n ↦ (↑(f i) : ℝ≥0∞) * ((μs n : Measure ℕ) ({i} : Set ℕ))) atTop
          (𝓝 ((↑(f i) : ℝ≥0∞) * ((μ : Measure ℕ) ({i} : Set ℕ)))) := by
    intro i hi
    exact ENNReal.Tendsto.const_mul (hs i) (Or.inr ENNReal.coe_ne_top)
  -- Proof comment: on a finite prefix, the lintegral is exactly the finite weighted singleton sum.
  simpa [MeasureTheory.lintegral_finset] using tendsto_finset_sum s hTerms

/-- Helper for Exercise 1.3.3: split a bounded nonnegative integral on `ℕ` into a finite prefix and
the complementary tail. -/
private theorem finiteMeasureNat_lintegralPrefixTail
    (f : BoundedContinuousFunction ℕ NNReal) (ν : FiniteMeasure ℕ) (M : ℕ) :
    ∫⁻ x, ↑(f x) ∂(ν : Measure ℕ) =
      ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(ν : Measure ℕ) +
        ∫⁻ x in Set.Ici M, ↑(f x) ∂(ν : Measure ℕ) := by
  have hCompl : ((((Finset.range M : Finset ℕ) : Set ℕ))ᶜ) = Set.Ici M := by
    -- Proof comment: the complement of the first `M` naturals is exactly the tail `Ici M`.
    ext i
    simp
  -- Proof comment: partition the discrete integral into the prefix and its measurable complement.
  calc
    ∫⁻ x, ↑(f x) ∂(ν : Measure ℕ)
      = ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(ν : Measure ℕ) +
          ∫⁻ x in ((((Finset.range M : Finset ℕ) : Set ℕ))ᶜ), ↑(f x) ∂(ν : Measure ℕ) := by
            symm
            exact MeasureTheory.lintegral_add_compl
              (fun x ↦ (↑(f x) : ℝ≥0∞)) MeasurableSet.of_discrete
    _ = ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(ν : Measure ℕ) +
          ∫⁻ x in Set.Ici M, ↑(f x) ∂(ν : Measure ℕ) := by
            rw [hCompl]

/-- Helper for Exercise 1.3.3: the tail integral of a bounded nonnegative function is controlled
by the sup norm times the tail mass. -/
private theorem finiteMeasureNat_lintegralTailLe
    (f : BoundedContinuousFunction ℕ NNReal) (ν : FiniteMeasure ℕ) (M : ℕ) :
    ∫⁻ x in Set.Ici M, ↑(f x) ∂(ν : Measure ℕ) ≤
      (nndist f 0 : ℝ≥0∞) * ((ν : Measure ℕ) (Set.Ici M)) := by
  have hBound : ∀ x : ℕ, (↑(f x) : ℝ≥0∞) ≤ (nndist f 0 : ℝ≥0∞) := by
    -- Proof comment: a bounded continuous nonnegative function is pointwise bounded by its
    -- distance to `0`, i.e. its sup norm.
    intro x
    exact ENNReal.coe_le_coe.2 <| by
      simpa [nndist_comm] using BoundedContinuousFunction.apply_le_nndist_zero f x
  -- Proof comment: compare the tail integrand with the tail constant bound and integrate.
  calc
    ∫⁻ x in Set.Ici M, ↑(f x) ∂(ν : Measure ℕ)
      ≤ ∫⁻ x in Set.Ici M, (nndist f 0 : ℝ≥0∞) ∂(ν : Measure ℕ) := by
          exact MeasureTheory.lintegral_mono hBound
    _ = (nndist f 0 : ℝ≥0∞) * ((ν : Measure ℕ) (Set.Ici M)) := by
          rw [MeasureTheory.setLIntegral_const]

/-- Helper for Exercise 1.3.3: on `ℕ`, singleton convergence and total-mass convergence imply
setwise convergence on every subset. -/
private theorem finiteMeasureNat_applyTendstoOfSingletonMass
    (μs : ℕ → FiniteMeasure ℕ) (μ : FiniteMeasure ℕ)
    (hs :
      ∀ i : ℕ,
        Tendsto (fun n ↦ ((μs n : Measure ℕ) ({i} : Set ℕ))) atTop
          (𝓝 ((μ : Measure ℕ) ({i} : Set ℕ))))
    (hmass :
      Tendsto (fun n ↦ (((μs n).mass : ℝ≥0∞))) atTop (𝓝 ((μ.mass : ℝ≥0∞))))
    (S : Set ℕ) :
    Tendsto (fun n ↦ ((μs n : Measure ℕ) S)) atTop (𝓝 ((μ : Measure ℕ) S)) := by
  classical
  -- Proof comment: split `S` into a finite prefix and a tail. The prefix converges from the
  -- singleton limits, while the tail is controlled uniformly by the tail masses `μs n (Ici M)`.
  have hSplit :
      ∀ M : ℕ, ∀ ν : FiniteMeasure ℕ,
        ((ν : Measure ℕ) S) =
          ((ν : Measure ℕ) (((Finset.range M).filter fun i ↦ i ∈ S) : Set ℕ)) +
            ((ν : Measure ℕ) (S ∩ Set.Ici M)) := by
    intro M ν
    let sM : Finset ℕ := (Finset.range M).filter fun i ↦ i ∈ S
    have hDecomp : S = (sM : Set ℕ) ∪ (S ∩ Set.Ici M) := by
      -- Proof comment: every point of `S` lies either in the first `M` indices or in the tail.
      ext i
      constructor
      · intro hiS
        by_cases hiM : i < M
        · left
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hiM, hiS⟩
        · right
          exact ⟨hiS, le_of_not_gt hiM⟩
      · intro hi
        rcases hi with hi | hi
        · exact (Finset.mem_filter.1 hi).2
        · exact hi.1
    have hDisj : Disjoint (sM : Set ℕ) (S ∩ Set.Ici M) := by
      -- Proof comment: the filtered prefix contains only indices `< M`, while the tail starts at
      -- `M`.
      refine Set.disjoint_left.2 ?_
      intro i hiPrefix hiTail
      have hiLt : i < M := Finset.mem_range.1 (Finset.mem_filter.1 hiPrefix).1
      exact (Nat.not_lt_of_ge hiTail.2 hiLt).elim
    calc
      ((ν : Measure ℕ) S) = ((ν : Measure ℕ) ((sM : Set ℕ) ∪ (S ∩ Set.Ici M))) := by
        exact congrArg (fun t : Set ℕ ↦ (ν : Measure ℕ) t) hDecomp
      _ = ((ν : Measure ℕ) (sM : Set ℕ)) + ((ν : Measure ℕ) (S ∩ Set.Ici M)) := by
        exact measure_union hDisj MeasurableSet.of_discrete
  have hPrefixTendsto :
      ∀ M : ℕ,
        Tendsto
          (fun n ↦
            ((μs n : Measure ℕ) (((Finset.range M).filter fun i ↦ i ∈ S) : Set ℕ)))
          atTop
          (𝓝 ((μ : Measure ℕ) (((Finset.range M).filter fun i ↦ i ∈ S) : Set ℕ))) := by
    intro M
    exact finiteMeasureNat_finsetApplyTendsto μs μ hs
      ((Finset.range M).filter fun i ↦ i ∈ S)
  rw [tendsto_order]
  constructor
  · intro a ha
    rcases ENNReal.lt_iff_exists_add_pos_lt.1 ha with ⟨ε, hεpos, hεlt⟩
    have hTailSmall :
        ∀ᶠ M in atTop, ((μ : Measure ℕ) (Set.Ici M)) < (ε : ℝ≥0∞) := by
      have hTailZero := finiteMeasureNat_tailTendstoZero μ
      exact hTailZero (Iio_mem_nhds (by exact_mod_cast hεpos))
    rcases Filter.eventually_atTop.1 hTailSmall with ⟨M, hM⟩
    let sM : Finset ℕ := (Finset.range M).filter fun i ↦ i ∈ S
    have hsM_subset : ((sM : Set ℕ) ⊆ S) := by
      intro i hi
      exact (Finset.mem_filter.1 hi).2
    have hTailLimit :
        ((μ : Measure ℕ) (S ∩ Set.Ici M)) < (ε : ℝ≥0∞) := by
      exact lt_of_le_of_lt (measure_mono (by intro i hi; exact hi.2)) (hM M le_rfl)
    have hPrefixGt : a < ((μ : Measure ℕ) (sM : Set ℕ)) := by
      by_contra hPrefix
      have hPrefixLe : ((μ : Measure ℕ) (sM : Set ℕ)) ≤ a := le_of_not_gt hPrefix
      have ha_ne_top : a ≠ ∞ := by
        have hμS_lt_top : ((μ : Measure ℕ) S) < ∞ :=
          lt_top_iff_ne_top.mpr (measure_ne_top (μ : Measure ℕ) S)
        exact ne_of_lt (lt_of_lt_of_le ha hμS_lt_top.le)
      have hUpper :
          ((μ : Measure ℕ) S) < a + (ε : ℝ≥0∞) := by
        have hLe :
            ((μ : Measure ℕ) S) ≤ a + ((μ : Measure ℕ) (S ∩ Set.Ici M)) := by
          rw [hSplit M μ]
          exact add_le_add hPrefixLe le_rfl
        exact lt_of_le_of_lt hLe
          (ENNReal.add_lt_add_left ha_ne_top hTailLimit)
      exact (not_lt_of_ge hUpper.le) hεlt
    have hEventuallyPrefix :
        ∀ᶠ n in atTop, a < ((μs n : Measure ℕ) (sM : Set ℕ)) :=
      (hPrefixTendsto M) (Ioi_mem_nhds hPrefixGt)
    filter_upwards [hEventuallyPrefix] with n hn
    exact lt_of_lt_of_le hn (measure_mono hsM_subset)
  · intro b hb
    rcases ENNReal.lt_iff_exists_add_pos_lt.1 hb with ⟨ε, hεpos, hεlt⟩
    have hTailSmall :
        ∀ᶠ M in atTop, ((μ : Measure ℕ) (Set.Ici M)) < (ε : ℝ≥0∞) / 2 := by
      have hTailZero := finiteMeasureNat_tailTendstoZero μ
      exact hTailZero (Iio_mem_nhds <| ENNReal.half_pos (by exact_mod_cast hεpos.ne'))
    rcases Filter.eventually_atTop.1 hTailSmall with ⟨M, hM⟩
    let sM : Finset ℕ := (Finset.range M).filter fun i ↦ i ∈ S
    have hsM_le : ((μ : Measure ℕ) (sM : Set ℕ)) ≤ ((μ : Measure ℕ) S) :=
      measure_mono (by
        intro i hi
        exact (Finset.mem_filter.1 hi).2)
    have hTailMass :
        Tendsto (fun n ↦ ((μs n : Measure ℕ) (Set.Ici M))) atTop
          (𝓝 ((μ : Measure ℕ) (Set.Ici M))) :=
      finiteMeasureNat_tailMassTendstoOfSingletonMass μs μ hs hmass M
    have hEventuallyTail :
        ∀ᶠ n in atTop, ((μs n : Measure ℕ) (Set.Ici M)) < (ε : ℝ≥0∞) / 2 :=
      hTailMass (Iio_mem_nhds (hM M le_rfl))
    have hEventuallyPrefix :
        ∀ᶠ n in atTop,
          ((μs n : Measure ℕ) (sM : Set ℕ)) <
            ((μ : Measure ℕ) (sM : Set ℕ)) + (ε : ℝ≥0∞) / 2 := by
      have hBound :
          ((μ : Measure ℕ) (sM : Set ℕ)) <
            ((μ : Measure ℕ) (sM : Set ℕ)) + (ε : ℝ≥0∞) / 2 :=
        ENNReal.lt_add_right
          (measure_ne_top (μ : Measure ℕ) (sM : Set ℕ))
          (by
            intro hZero
            exact (ENNReal.half_pos (by exact_mod_cast hεpos.ne')).ne' hZero)
      exact (hPrefixTendsto M) (Iio_mem_nhds hBound)
    filter_upwards [hEventuallyPrefix, hEventuallyTail] with n hnPrefix hnTail
    have hUpper :
        ((μs n : Measure ℕ) S) <
          ((μ : Measure ℕ) (sM : Set ℕ)) + (ε : ℝ≥0∞) := by
      have hTailSubset :
          ((μs n : Measure ℕ) (S ∩ Set.Ici M)) ≤ ((μs n : Measure ℕ) (Set.Ici M)) :=
        measure_mono (by intro i hi; exact hi.2)
      calc
        ((μs n : Measure ℕ) S)
          = ((μs n : Measure ℕ) (sM : Set ℕ)) + ((μs n : Measure ℕ) (S ∩ Set.Ici M)) := by
              rw [hSplit M (μs n)]
        _ ≤ ((μs n : Measure ℕ) (sM : Set ℕ)) + ((μs n : Measure ℕ) (Set.Ici M)) := by
              exact add_le_add_right hTailSubset _
        _ < (((μ : Measure ℕ) (sM : Set ℕ)) + (ε : ℝ≥0∞) / 2) + (ε : ℝ≥0∞) / 2 := by
              exact ENNReal.add_lt_add hnPrefix hnTail
        _ = ((μ : Measure ℕ) (sM : Set ℕ)) + (ε : ℝ≥0∞) := by
              rw [add_assoc, ENNReal.add_halves]
    have hAddLe :
        ((μ : Measure ℕ) (sM : Set ℕ)) + (ε : ℝ≥0∞) ≤
          ((μ : Measure ℕ) S) + (ε : ℝ≥0∞) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hsM_le (ε : ℝ≥0∞)
    have hUpper' :
        ((μs n : Measure ℕ) S) < ((μ : Measure ℕ) S) + (ε : ℝ≥0∞) :=
      lt_of_lt_of_le hUpper hAddLe
    exact lt_trans hUpper' hεlt

/-- Helper for Exercise 1.3.3: on the discrete space `ℕ`, singleton convergence together with
total-mass convergence upgrades to weak convergence of finite measures. -/
private theorem finiteMeasureNat_tendstoOfSingletonMass
    (μs : ℕ → FiniteMeasure ℕ) (μ : FiniteMeasure ℕ)
    (hs :
      ∀ i : ℕ,
        Tendsto (fun n ↦ ((μs n : Measure ℕ) ({i} : Set ℕ))) atTop
          (𝓝 ((μ : Measure ℕ) ({i} : Set ℕ))))
    (hmass :
      Tendsto (fun n ↦ (((μs n).mass : ℝ≥0∞))) atTop (𝓝 ((μ.mass : ℝ≥0∞)))) :
    Tendsto μs atTop (𝓝 μ) := by
  -- Route correction: prove weak convergence through the `lintegral` characterization, then split
  -- every bounded continuous test function into a finite prefix and a small tail.
  rw [MeasureTheory.FiniteMeasure.tendsto_iff_forall_lintegral_tendsto]
  intro f
  let c : ℝ≥0∞ := nndist f 0
  have hc_ne_top : c ≠ ∞ := by
    -- Proof comment: the sup norm of a bounded continuous `NNReal` function is finite.
    dsimp [c]
    exact ENNReal.coe_ne_top
  have hPrefixLeFull :
      ∀ M : ℕ, ∀ ν : FiniteMeasure ℕ,
        ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(ν : Measure ℕ) ≤
          ∫⁻ x, ↑(f x) ∂(ν : Measure ℕ) := by
    intro M ν
    -- Proof comment: the full integral is the prefix contribution plus a nonnegative tail.
    rw [finiteMeasureNat_lintegralPrefixTail f ν M]
    exact le_add_right le_rfl
  have hFullLtTop :
      ∫⁻ x, ↑(f x) ∂(μ : Measure ℕ) < ∞ :=
    BoundedContinuousFunction.lintegral_lt_top_of_nnreal (μ : Measure ℕ) f
  rw [tendsto_order]
  constructor
  · intro a ha
    rcases ENNReal.lt_iff_exists_add_pos_lt.1 ha with ⟨ε, hεpos, hεlt⟩
    have hTailScaled :
        Tendsto (fun M ↦ c * ((μ : Measure ℕ) (Set.Ici M))) atTop (𝓝 0) := by
      simpa [c, zero_mul] using
        ENNReal.Tendsto.const_mul (finiteMeasureNat_tailTendstoZero μ) (Or.inr hc_ne_top)
    have hTailSmall :
        ∀ᶠ M in atTop, c * ((μ : Measure ℕ) (Set.Ici M)) < (ε : ℝ≥0∞) :=
      hTailScaled (Iio_mem_nhds (by exact_mod_cast hεpos))
    rcases Filter.eventually_atTop.1 hTailSmall with ⟨M, hM⟩
    have hTailLt :
        ∫⁻ x in Set.Ici M, ↑(f x) ∂(μ : Measure ℕ) < (ε : ℝ≥0∞) := by
      exact lt_of_le_of_lt (finiteMeasureNat_lintegralTailLe f μ M) (hM M le_rfl)
    have hPrefixGt :
        a <
          ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μ : Measure ℕ) := by
      by_contra hPrefix
      have hPrefixLe :
          ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μ : Measure ℕ) ≤ a :=
        le_of_not_gt hPrefix
      have ha_ne_top : a ≠ ∞ := by
        exact ne_of_lt (lt_of_lt_of_le ha hFullLtTop.le)
      have hUpper :
          ∫⁻ x, ↑(f x) ∂(μ : Measure ℕ) < a + (ε : ℝ≥0∞) := by
        have hLe :
            ∫⁻ x, ↑(f x) ∂(μ : Measure ℕ) ≤
              a + ∫⁻ x in Set.Ici M, ↑(f x) ∂(μ : Measure ℕ) := by
          rw [finiteMeasureNat_lintegralPrefixTail f μ M]
          exact add_le_add hPrefixLe le_rfl
        exact lt_of_le_of_lt hLe (ENNReal.add_lt_add_left ha_ne_top hTailLt)
      exact (not_lt_of_ge hUpper.le) hεlt
    have hPrefixEventually :
        ∀ᶠ n in atTop,
          a <
            ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μs n : Measure ℕ) :=
      (finiteMeasureNat_finsetLintegralTendsto μs μ hs f (Finset.range M))
        (Ioi_mem_nhds hPrefixGt)
    filter_upwards [hPrefixEventually] with n hn
    exact lt_of_lt_of_le hn (hPrefixLeFull M (μs n))
  · intro b hb
    rcases ENNReal.lt_iff_exists_add_pos_lt.1 hb with ⟨ε, hεpos, hεlt⟩
    have hHalfPos : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := by
      exact ENNReal.half_pos (by exact_mod_cast hεpos.ne')
    have hTailScaled :
        Tendsto (fun M ↦ c * ((μ : Measure ℕ) (Set.Ici M))) atTop (𝓝 0) := by
      simpa [c, zero_mul] using
        ENNReal.Tendsto.const_mul (finiteMeasureNat_tailTendstoZero μ) (Or.inr hc_ne_top)
    have hTailSmall :
        ∀ᶠ M in atTop, c * ((μ : Measure ℕ) (Set.Ici M)) < (ε : ℝ≥0∞) / 2 :=
      hTailScaled (Iio_mem_nhds hHalfPos)
    rcases Filter.eventually_atTop.1 hTailSmall with ⟨M, hM⟩
    have hTailLt :
        ∫⁻ x in Set.Ici M, ↑(f x) ∂(μ : Measure ℕ) < (ε : ℝ≥0∞) / 2 := by
      exact lt_of_le_of_lt (finiteMeasureNat_lintegralTailLe f μ M) (hM M le_rfl)
    have hTailMass :
        Tendsto (fun n ↦ ((μs n : Measure ℕ) (Set.Ici M))) atTop
          (𝓝 ((μ : Measure ℕ) (Set.Ici M))) :=
      finiteMeasureNat_tailMassTendstoOfSingletonMass μs μ hs hmass M
    have hTailScaledSeq :
        Tendsto (fun n ↦ c * ((μs n : Measure ℕ) (Set.Ici M))) atTop
          (𝓝 (c * ((μ : Measure ℕ) (Set.Ici M)))) := by
      exact ENNReal.Tendsto.const_mul hTailMass (Or.inr hc_ne_top)
    have hTailEventually :
        ∀ᶠ n in atTop, c * ((μs n : Measure ℕ) (Set.Ici M)) < (ε : ℝ≥0∞) / 2 :=
      hTailScaledSeq (Iio_mem_nhds (hM M le_rfl))
    have hPrefixLt :
        ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μ : Measure ℕ) <
          ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μ : Measure ℕ) +
            (ε : ℝ≥0∞) / 2 := by
      have hPrefixLtTop :
          ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μ : Measure ℕ) < ∞ :=
        lt_of_le_of_lt (hPrefixLeFull M μ) hFullLtTop
      exact ENNReal.lt_add_right hPrefixLtTop.ne
        hHalfPos.ne'
    have hPrefixEventually :
        ∀ᶠ n in atTop,
          ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μs n : Measure ℕ) <
            ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μ : Measure ℕ) +
              (ε : ℝ≥0∞) / 2 :=
      (finiteMeasureNat_finsetLintegralTendsto μs μ hs f (Finset.range M))
        (Iio_mem_nhds hPrefixLt)
    filter_upwards [hPrefixEventually, hTailEventually] with n hnPrefix hnTail
    have hUpper :
        ∫⁻ x, ↑(f x) ∂(μs n : Measure ℕ) <
          ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μ : Measure ℕ) +
            (ε : ℝ≥0∞) := by
      calc
        ∫⁻ x, ↑(f x) ∂(μs n : Measure ℕ)
          = ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μs n : Measure ℕ) +
              ∫⁻ x in Set.Ici M, ↑(f x) ∂(μs n : Measure ℕ) := by
                rw [finiteMeasureNat_lintegralPrefixTail f (μs n) M]
        _ ≤ ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μs n : Measure ℕ) +
              c * ((μs n : Measure ℕ) (Set.Ici M)) := by
                exact add_le_add_right (finiteMeasureNat_lintegralTailLe f (μs n) M) _
        _ < (∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μ : Measure ℕ) +
              (ε : ℝ≥0∞) / 2) + (ε : ℝ≥0∞) / 2 := by
                exact ENNReal.add_lt_add hnPrefix hnTail
        _ = ∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μ : Measure ℕ) +
              (ε : ℝ≥0∞) := by
                rw [add_assoc, ENNReal.add_halves]
    have hAddLe :
        (∫⁻ x in (((Finset.range M : Finset ℕ) : Set ℕ)), ↑(f x) ∂(μ : Measure ℕ)) +
            (ε : ℝ≥0∞) ≤
          (∫⁻ x, ↑(f x) ∂(μ : Measure ℕ)) + (ε : ℝ≥0∞) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (hPrefixLeFull M μ) (ε : ℝ≥0∞)
    have hUpper' :
        ∫⁻ x, ↑(f x) ∂(μs n : Measure ℕ) <
          (∫⁻ x, ↑(f x) ∂(μ : Measure ℕ)) + (ε : ℝ≥0∞) :=
      lt_of_lt_of_le hUpper hAddLe
    exact lt_trans hUpper' hεlt

/-- Helper for Exercise 1.3.3: one stage of the protected finite-block construction used in the
finite-mass contradiction argument. -/
private structure countableSetwiseLimitStage where
  rank : ℕ
  cutoff : ℕ
  index : ℕ
  block : Finset ℕ
deriving DecidableEq

/-- Helper for Exercise 1.3.3: one may choose the protected tail beyond any prescribed lower
bound. -/
private theorem countableSetwiseLimit_chooseProtectedTailAbove
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)]
    (A : Set ℕ)
    (hAfinite :
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i < ⊤)
    (s : Finset ℕ) (L : ℕ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ M : ℕ, L ≤ M ∧
      (∑' i, (A ∩ Set.Ici M).indicator
        (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) < δ ∧
      ∀ m ∈ s, νNat m (A ∩ Set.Ici M) < δ := by
  rcases countableSetwiseLimit_chooseProtectedTail νNat A hAfinite s hδ with
    ⟨M0, hAtomic0, hSmall0⟩
  refine ⟨max L M0, le_max_left _ _, ?_, ?_⟩
  · exact lt_of_le_of_lt
      (ENNReal.tsum_le_tsum fun i ↦ by
        by_cases hi : i ∈ A ∩ Set.Ici (max L M0)
        · have hi' : i ∈ A ∩ Set.Ici M0 := by
            refine ⟨hi.1, ?_⟩
            exact le_trans (le_max_right _ _) (show max L M0 ≤ i from hi.2)
          simp [Set.indicator, hi, hi']
        · simp [Set.indicator, hi])
      hAtomic0
  · intro m hm
    exact lt_of_le_of_lt (measure_mono <| by
      intro i hi
      have hi' : i ∈ A ∩ Set.Ici M0 := by
        refine ⟨hi.1, ?_⟩
        exact le_trans (le_max_right _ _) (show max L M0 ≤ i from hi.2)
      exact hi') (hSmall0 m hm)

/-- Helper for Exercise 1.3.3: once a tail has positive limiting mass, one can realize that mass
above any prescribed index. -/
private theorem countableSetwiseLimit_chooseLargeTailBlockAbove
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)]
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ) (M N : ℕ) {ε : ℝ≥0∞}
    (hε : ε < limUnder atTop (fun n ↦ νNat n (A ∩ Set.Ici M))) :
    ∃ n : ℕ, N ≤ n ∧
      ∃ t : Finset ℕ, ((t : Set ℕ) ⊆ A ∩ Set.Ici M) ∧ ε < νNat n (t : Set ℕ) := by
  have hTailTendsto :
      Tendsto (fun n ↦ νNat n (A ∩ Set.Ici M)) atTop
        (𝓝 (limUnder atTop (fun n ↦ νNat n (A ∩ Set.Ici M)))) :=
    tendsto_nhds_limUnder (hlim (A ∩ Set.Ici M))
  have hEventually :
      ∀ᶠ n in atTop, ε < νNat n (A ∩ Set.Ici M) :=
    hTailTendsto (Ioi_mem_nhds hε)
  rcases Filter.eventually_atTop.1 hEventually with ⟨N0, hN0⟩
  let n := max N N0
  have hTailMass : ε < νNat n (A ∩ Set.Ici M) := hN0 n (le_max_right _ _)
  rcases countableSetwiseLimit_extractFiniteBlock νNat A n M hTailMass with ⟨t, ht, hmass⟩
  exact ⟨n, le_max_left _ _, t, ht, hmass⟩

/-- Helper for Exercise 1.3.3: a sequence with one subsequence staying above `ε` and the
interleaving subsequence staying below `ε / 2` cannot converge. -/
private theorem countableSetwiseLimit_notTendstoOfSeparatedSubsequence
    (a : ℕ → ℝ≥0∞) {ε : ℝ≥0∞} (hε : 0 < ε) (nSeq : ℕ → ℕ)
    (hnSeq : Tendsto nSeq atTop atTop)
    (hEven : ∀ k, ε < a (nSeq (2 * k)))
    (hOdd : ∀ k, a (nSeq (2 * k + 1)) < ε / 2) :
    ¬ ∃ x, Tendsto a atTop (𝓝 x) := by
  intro hConv
  rcases hConv with ⟨x, hx⟩
  have hEvenMap : Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ Filter.eventually_atTop.2 ?_
    exact ⟨b, fun n hn ↦ by omega⟩
  have hOddMap : Tendsto (fun k : ℕ ↦ 2 * k + 1) atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ Filter.eventually_atTop.2 ?_
    exact ⟨b, fun n hn ↦ by omega⟩
  have hEvenTendsto :
      Tendsto (fun k ↦ a (nSeq (2 * k))) atTop (𝓝 x) :=
    hx.comp (hnSeq.comp hEvenMap)
  have hOddTendsto :
      Tendsto (fun k ↦ a (nSeq (2 * k + 1))) atTop (𝓝 x) :=
    hx.comp (hnSeq.comp hOddMap)
  have hε_le : ε ≤ x :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hEvenTendsto fun k ↦ (hEven k).le
  have hx_le : x ≤ ε / 2 :=
    le_of_tendsto_of_tendsto' hOddTendsto tendsto_const_nhds fun k ↦ (hOdd k).le
  have hε_top : ε ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp <| lt_of_lt_of_le (hEven 0) le_top
  exact (not_le_of_gt (ENNReal.half_lt_self hε.ne' hε_top)) (hε_le.trans hx_le)

/-- Helper for Exercise 1.3.3: the only unresolved finite-branch input is the equality between the
full limiting mass on `A` and the singleton series on `A`. -/
private theorem countableSetwiseLimit_massEqAtomicMass
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)]
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ)
    (hAfinite :
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i < ⊤) :
    limUnder atTop (fun n ↦ νNat n A) =
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i := by
  classical
  let atom : ℕ → ℝ≥0∞ := fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))
  have hLower :
      (∑' i, A.indicator atom i) ≤ limUnder atTop (fun n ↦ νNat n A) :=
    countableSetwiseLimit_tsumLe νNat hlim A
  refine le_antisymm ?_ hLower
  by_contra hUpper
  -- Route correction: instead of unfolding the later weak-convergence wrapper, build a sequence of
  -- protected finite blocks whose even/odd measures force an oscillating subsequence on one set.
  have hGap : (∑' i, A.indicator atom i) < limUnder atTop (fun n ↦ νNat n A) :=
    lt_of_not_ge hUpper
  rcases countableSetwiseLimit_eventuallyLargeTail νNat hlim A hAfinite hGap with
    ⟨ε, hε, hTailPos⟩
  rcases ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos hε.ne').ne' ℕ with
    ⟨η, hηpos, hηsum⟩
  let P : countableSetwiseLimitStage → Prop := fun y ↦
    y.rank ≤ y.index ∧
      ((y.block : Set ℕ) ⊆ A ∩ Set.Ici y.cutoff) ∧
      ε < νNat y.index (y.block : Set ℕ) ∧
      (∑ i ∈ y.block, A.indicator atom i) < η y.rank
  let r : countableSetwiseLimitStage → countableSetwiseLimitStage → Prop := fun x y ↦
    x.rank < y.rank ∧
      (∀ i ∈ x.block, i < y.cutoff) ∧
      νNat x.index (y.block : Set ℕ) < η y.rank ∧
      νNat y.index (x.block : Set ℕ) < η x.rank
  have hStep :
      ∀ s : Finset countableSetwiseLimitStage, (∀ x ∈ s, P x) → ∃ y, P y ∧ ∀ x ∈ s, r x y := by
    intro s hs
    let rank : ℕ := s.sup countableSetwiseLimitStage.rank + 1
    let L : ℕ := s.sup fun x ↦ x.block.sup id + 1
    rcases countableSetwiseLimit_chooseProtectedTailAbove νNat A hAfinite
        (s.image countableSetwiseLimitStage.index) L (hηpos rank) with
      ⟨M, hLM, hAtomicTail, hSmallTail⟩
    have hPastSmallAux :
        ∀ t : Finset countableSetwiseLimitStage, (∀ x ∈ t, P x) →
          ∀ᶠ n in atTop, ∀ x ∈ t, νNat n (x.block : Set ℕ) < η x.rank := by
      intro t ht
      induction t using Finset.induction_on with
      | empty =>
          exact Filter.Eventually.of_forall fun n x hx ↦ False.elim (by simp at hx)
      | @insert a t ha ih =>
          have hPa : P a := ht a (Finset.mem_insert_self _ _)
          have ht' : ∀ x ∈ t, P x := fun x hx ↦ ht x (Finset.mem_insert_of_mem hx)
          have hAevent : ∀ᶠ n in atTop, νNat n (a.block : Set ℕ) < η a.rank := by
            have hBlockSubsetA : ((a.block : Set ℕ) ⊆ A) := by
              intro i hi
              exact (hPa.2.1 hi).1
            exact countableSetwiseLimit_finsetEventuallySmallOfAtomicBound νNat hlim A a.block
              hBlockSubsetA hPa.2.2.2
          filter_upwards [hAevent, ih ht'] with n hnA hnT
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx'
          · exact hnA
          · exact hnT x hx'
    have hPastSmall :
        ∀ᶠ n in atTop, ∀ x ∈ s, νNat n (x.block : Set ℕ) < η x.rank :=
      hPastSmallAux s hs
    rcases Filter.eventually_atTop.1 hPastSmall with ⟨N, hN⟩
    rcases countableSetwiseLimit_chooseLargeTailBlockAbove νNat hlim A M (max rank N)
        (hTailPos M) with ⟨n, hn, t, htSubset, hMass⟩
    let y : countableSetwiseLimitStage :=
      { rank := rank, cutoff := M, index := n, block := t }
    have hAtomicBlock :
        (∑ i ∈ t, A.indicator atom i) < η rank := by
      have hLe :
          ∑ i ∈ t, A.indicator atom i ≤
            ∑' i, (A ∩ Set.Ici M).indicator atom i := by
        calc
          ∑ i ∈ t, A.indicator atom i
            = ∑ i ∈ t, (A ∩ Set.Ici M).indicator atom i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hiTail : i ∈ A ∩ Set.Ici M := htSubset (by simpa using hi)
                simp [Set.indicator, hiTail, hiTail.1]
          _ ≤ ∑' i, (A ∩ Set.Ici M).indicator atom i := ENNReal.sum_le_tsum _
      exact lt_of_le_of_lt hLe hAtomicTail
    refine ⟨y, ?_, ?_⟩
    · -- Proof comment: the new stage keeps a large finite block in a far tail and records its tiny
      -- atomic mass budget.
      exact ⟨le_trans (le_max_left _ _) hn, htSubset, hMass, hAtomicBlock⟩
    · intro x hx
      have hPx : P x := hs x hx
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hxSup : x.rank ≤ s.sup countableSetwiseLimitStage.rank := Finset.le_sup hx
        simpa [y, rank] using Nat.lt_succ_of_le hxSup
      · intro i hi
        have hiBlock : i ≤ x.block.sup id := by
          exact @Finset.le_sup ℕ ℕ _ _ x.block id i hi
        have hBlockSup : x.block.sup id + 1 ≤ L := by
          exact @Finset.le_sup ℕ countableSetwiseLimitStage _ _
            s (fun z ↦ z.block.sup id + 1) x hx
        have : i < L := lt_of_lt_of_le (Nat.lt_succ_of_le hiBlock) hBlockSup
        exact lt_of_lt_of_le this hLM
      · have hxImage :
            x.index ∈ s.image countableSetwiseLimitStage.index :=
          Finset.mem_image.2 ⟨x, hx, rfl⟩
        exact lt_of_le_of_lt (measure_mono htSubset) (hSmallTail x.index hxImage)
      · exact hN n (le_trans (le_max_right _ _) hn) x hx
  rcases exists_seq_of_forall_finset_exists P r hStep with ⟨f, hfP, hfRel⟩
  let B : Set ℕ := ⋃ k, (((f (2 * k)).block : Finset ℕ) : Set ℕ)
  have hRankMono : StrictMono fun n ↦ (f n).rank := fun m n hmn ↦ (hfRel m n hmn).1
  have hIndexAtTop : Tendsto (fun n ↦ (f n).index) atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ Filter.eventually_atTop.2 ?_
    exact ⟨b, fun n hn ↦ le_trans (le_trans hn (StrictMono.id_le hRankMono n)) (hfP n).1⟩
  have hBlockDisj :
      ∀ ⦃m n : ℕ⦄, m < n →
        Disjoint (((f m).block : Finset ℕ) : Set ℕ) (((f n).block : Finset ℕ) : Set ℕ) := by
    intro m n hmn
    have hSubsetN : ((((f n).block : Finset ℕ) : Set ℕ) ⊆ A ∩ Set.Ici (f n).cutoff) :=
      (hfP n).2.1
    have hCut : ∀ i ∈ (f m).block, i < (f n).cutoff := (hfRel m n hmn).2.1
    refine Set.disjoint_left.2 ?_
    intro i hi hj
    exact (Nat.not_lt_of_ge (hSubsetN hj).2) (hCut i hi)
  have hEvenDisj :
      Pairwise (fun k l ↦
        Disjoint (((f (2 * k)).block : Finset ℕ) : Set ℕ)
          ((((f (2 * l)).block : Finset ℕ) : Set ℕ))) := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · exact hBlockDisj (by omega)
    · exact (hBlockDisj (by omega)).symm
  have hEvenLarge : ∀ k, ε < νNat (f (2 * k)).index B := by
    intro k
    have hPk : P (f (2 * k)) := hfP (2 * k)
    have hBlockSubset : (((f (2 * k)).block : Finset ℕ) : Set ℕ) ⊆ B := by
      intro i hi
      exact Set.mem_iUnion.2 ⟨k, hi⟩
    exact lt_of_lt_of_le hPk.2.2.1
      (measure_mono hBlockSubset)
  have hOddSmall : ∀ k, νNat (f (2 * k + 1)).index B < ε / 2 := by
    intro k
    have hApply :
        νNat (f (2 * k + 1)).index B =
          ∑' j, νNat (f (2 * k + 1)).index ((((f (2 * j)).block : Finset ℕ) : Set ℕ)) := by
      simpa [B] using
        (measure_iUnion hEvenDisj fun _ ↦ MeasurableSet.of_discrete :
          νNat (f (2 * k + 1)).index (⋃ j, ((((f (2 * j)).block : Finset ℕ) : Set ℕ))) =
            ∑' j, νNat (f (2 * k + 1)).index ((((f (2 * j)).block : Finset ℕ) : Set ℕ)))
    have hTerm :
        ∀ j, νNat (f (2 * k + 1)).index ((((f (2 * j)).block : Finset ℕ) : Set ℕ)) ≤
          η ((f (2 * j)).rank) := by
      intro j
      by_cases hj : j ≤ k
      · have hRel := hfRel (2 * j) (2 * k + 1) (by omega)
        exact hRel.2.2.2.le
      · have hRel := hfRel (2 * k + 1) (2 * j) (by omega)
        exact hRel.2.2.1.le
    have hEvenRankInj : Function.Injective (fun j ↦ (f (2 * j)).rank) := by
      refine (show StrictMono (fun j ↦ (f (2 * j)).rank) from ?_).injective
      intro i j hij
      exact (hfRel (2 * i) (2 * j) (by omega)).1
    have hBudget :
        ∑' j, η ((f (2 * j)).rank) < ε / 2 :=
      lt_of_le_of_lt
        (ENNReal.summable.tsum_le_tsum_of_inj (fun j ↦ (f (2 * j)).rank) hEvenRankInj
          (fun _ _ ↦ zero_le _) (fun _ ↦ le_rfl) ENNReal.summable)
        hηsum
    have hLe :
        νNat (f (2 * k + 1)).index B ≤ ∑' j, η ((f (2 * j)).rank) := by
      rw [hApply]
      exact ENNReal.tsum_le_tsum hTerm
    exact lt_of_le_of_lt hLe hBudget
  have hNoTendsto :
      ¬ ∃ x, Tendsto (fun n ↦ νNat n B) atTop (𝓝 x) :=
    countableSetwiseLimit_notTendstoOfSeparatedSubsequence
      (fun n ↦ νNat n B) hε (fun n ↦ (f n).index) hIndexAtTop
      hEvenLarge hOddSmall
  exact hNoTendsto
    ⟨limUnder atTop (fun n ↦ νNat n B), tendsto_nhds_limUnder (hlim B)⟩

/-- Helper for Exercise 1.3.3: the real remaining task in the finite singleton-mass branch is to
show that the restricted finite measures converge to the atomic candidate. -/
private theorem countableSetwiseLimit_restrictTendstoFiniteMeasure
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)]
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ)
    (hAfinite :
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i < ⊤) :
    Tendsto (fun n ↦ countableSetwiseLimitRestrictFiniteMeasure νNat A n) atTop
      (𝓝 (countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite)) := by
  have hs :
      ∀ i : ℕ,
        Tendsto
          (fun n ↦
            (((countableSetwiseLimitRestrictFiniteMeasure νNat A n : FiniteMeasure ℕ) :
              Measure ℕ) ({i} : Set ℕ)))
          atTop
          (𝓝 ((((countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite : FiniteMeasure ℕ) :
            Measure ℕ) ({i} : Set ℕ)))) := by
    intro i
    have hRestrict :
        Tendsto
          (fun n ↦
            (((countableSetwiseLimitRestrictFiniteMeasure νNat A n : FiniteMeasure ℕ) :
              Measure ℕ) ({i} : Set ℕ)))
          atTop
          (𝓝 (limUnder atTop (fun n ↦ ((νNat n).restrict A) ({i} : Set ℕ)))) := by
      simpa [countableSetwiseLimitRestrictFiniteMeasure] using
        tendsto_nhds_limUnder
          (hlim ({i} ∩ A))
    have hAtomicSingleton :
        (((countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite : FiniteMeasure ℕ) :
          Measure ℕ) ({i} : Set ℕ)) =
          A.indicator (fun j ↦ limUnder atTop (fun n ↦ νNat n ({j} : Set ℕ))) i := by
      simpa [countableSetwiseLimitAtomicFiniteMeasure] using
        countableSetwiseLimit_atomicMeasure_singleton νNat A i
    -- Proof comment: both the source and target singleton masses are already identified explicitly.
    have hLimitEq :
        limUnder atTop (fun n ↦ ((νNat n).restrict A) ({i} : Set ℕ)) =
          (((countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite : FiniteMeasure ℕ) :
            Measure ℕ) ({i} : Set ℕ)) := by
      rw [countableSetwiseLimit_restrictSingletonLimit νNat A i, ← hAtomicSingleton]
    exact hLimitEq ▸ hRestrict
  have hMassEq :
      limUnder atTop (fun n ↦ νNat n A) =
        ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i :=
    countableSetwiseLimit_massEqAtomicMass νNat hlim A hAfinite
  have hmass :
      Tendsto
        (fun n ↦
          (((countableSetwiseLimitRestrictFiniteMeasure νNat A n).mass : ℝ≥0∞)))
        atTop
        (𝓝 (((countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite).mass : ℝ≥0∞))) := by
    -- Proof comment: after the finite-branch mass identity, the masses of the restricted sequence
    -- converge to the mass of the atomic finite measure.
    simpa [countableSetwiseLimit_restrictFiniteMeasure_mass,
      countableSetwiseLimit_atomicFiniteMeasure_mass, hMassEq] using
      (tendsto_nhds_limUnder (hlim A))
  exact finiteMeasureNat_tendstoOfSingletonMass
    (fun n ↦ countableSetwiseLimitRestrictFiniteMeasure νNat A n)
    (countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite) hs hmass

/-- Helper for Exercise 1.3.3: the finite singleton-mass branch now reduces to the convergence of
restricted finite measures to the atomic limit. -/
private theorem countableSetwiseLimit_leTsumOfLtTop
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)]
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ)
    (hAfinite :
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i < ⊤) :
    limUnder atTop (fun n ↦ νNat n A) ≤
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i := by
  have hRestrict :
      Tendsto (fun n ↦ countableSetwiseLimitRestrictFiniteMeasure νNat A n) atTop
        (𝓝 (countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite)) :=
    countableSetwiseLimit_restrictTendstoFiniteMeasure νNat hlim A hAfinite
  have hMass :
      Tendsto
        (fun n ↦
          (((countableSetwiseLimitRestrictFiniteMeasure νNat A n).mass : ℝ≥0∞)))
        atTop
        (𝓝 (((countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite).mass : ℝ≥0∞))) :=
    (ENNReal.continuous_coe.tendsto _).comp
      ((FiniteMeasure.continuous_mass.tendsto
        (countableSetwiseLimitAtomicFiniteMeasure νNat A hAfinite)).comp hRestrict)
  have hMass' :
      Tendsto (fun n ↦ νNat n A) atTop
        (𝓝 (∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i)) := by
    -- Proof comment: both masses are explicit on the restricted and atomic finite measures.
    simpa [countableSetwiseLimit_restrictFiniteMeasure_mass,
      countableSetwiseLimit_atomicFiniteMeasure_mass] using hMass
  have hEq :
      limUnder atTop (fun n ↦ νNat n A) =
        ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i :=
    tendsto_nhds_unique (tendsto_nhds_limUnder (hlim A)) hMass'
  -- Proof comment: the finite-branch upper bound is now just the equality of the two mass limits.
  exact hEq.le

private theorem countableSetwiseLimit_apply
    (νNat : ℕ → Measure ℕ) [∀ n, IsFiniteMeasure (νNat n)]
    (hlim : ∀ A : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n A) atTop (𝓝 x))
    (A : Set ℕ) :
    limUnder atTop (fun n ↦ νNat n A) =
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i := by
  by_cases hA :
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i = ⊤
  · -- Proof comment: the infinite-mass branch closes from the finite-prefix lower bounds alone.
    simpa [hA] using countableSetwiseLimit_eqTopOfTsumEqTop νNat hlim A hA
  · have hLower :
        (∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i) ≤
          limUnder atTop (fun n ↦ νNat n A) :=
      countableSetwiseLimit_tsumLe νNat hlim A
    have hUpper :
        limUnder atTop (fun n ↦ νNat n A) ≤
          ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i :=
      countableSetwiseLimit_leTsumOfLtTop νNat hlim A (lt_top_iff_ne_top.2 hA)
    -- Proof comment: once the finite-`tsum` upper bound is available, the two inequalities match.
    exact le_antisymm hUpper hLower

/-- Helper for Exercise 1.3.3: transport the countable discrete reconstruction theorem back to a
pairwise disjoint measurable family in `Ω`. -/
private theorem finiteMeasurePointwiseLimit_subsetBiUnion
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x))
    (f : ℕ → Set Ω) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (fun i j ↦ Disjoint (f i) (f j)))
    (A : Set ℕ) :
    limUnder atTop (fun n ↦ μ n (⋃ i ∈ A, f i)) =
      ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ μ n (f i))) i := by
  let U : Set ℕ → Set Ω := fun B ↦ ⋃ i ∈ B, f i
  have hUmeas : ∀ B : Set ℕ, MeasurableSet (U B) := by
    intro B
    exact MeasurableSet.biUnion (Set.to_countable B) fun i _ ↦ hf i
  have hUsingleton : ∀ i : ℕ, U ({i} : Set ℕ) = f i := by
    intro i
    ext x
    simp [U]
  let νNat : ℕ → Measure ℕ := fun n ↦
    Measure.ofMeasurable
      (fun B _ ↦ μ n (U B))
      (by simp [U])
      (by
        intro s hs hdisj
        have hUdisj : Pairwise (fun i j ↦ Disjoint (U (s i)) (U (s j))) := by
          intro i j hij
          refine Set.disjoint_left.2 ?_
          intro x hx hx'
          simp only [U, Set.mem_iUnion, exists_prop] at hx hx'
          rcases hx with ⟨a, ha, hxa⟩
          rcases hx' with ⟨b, hb, hxb⟩
          have hab : a ≠ b := by
            intro hab
            subst hab
            exact (Set.disjoint_left.1 (hdisj hij) ha hb).elim
          exact (Set.disjoint_left.1 (hd hab) hxa hxb).elim
        have hUnion : U (⋃ i, s i) = ⋃ i, U (s i) := by
          ext x
          simp only [U, Set.mem_iUnion, exists_prop]
          constructor
          · rintro ⟨j, ⟨i, hij⟩, hxj⟩
            exact ⟨i, j, hij, hxj⟩
          · rintro ⟨i, j, hj, hxj⟩
            exact ⟨j, ⟨i, hj⟩, hxj⟩
        -- Rewrite the `Nat`-indexed union through `U`, then use countable additivity of `μ n`.
        calc
          μ n (U (⋃ i, s i)) = μ n (⋃ i, U (s i)) := by rw [hUnion]
          _ = ∑' i, μ n (U (s i)) := measure_iUnion hUdisj fun i ↦ hUmeas (s i))
  have hNuNatApply : ∀ n B, νNat n B = μ n (U B) := by
    intro n B
    exact Measure.ofMeasurable_apply B MeasurableSet.of_discrete
  have hNuNatLim : ∀ B : Set ℕ, ∃ x : ℝ≥0∞, Tendsto (fun n ↦ νNat n B) atTop (𝓝 x) := by
    intro B
    rcases hlim (U B) (hUmeas B) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [hNuNatApply, U] using hx
  have hNuNatFinite : ∀ n, IsFiniteMeasure (νNat n) := by
    intro n
    refine ⟨?_⟩
    rw [hNuNatApply]
    exact measure_lt_top (μ n) (U Set.univ)
  letI : ∀ n, IsFiniteMeasure (νNat n) := hNuNatFinite
  -- Apply the discrete countable-space theorem to the transported measures `νNat n`.
  calc
    limUnder atTop (fun n ↦ μ n (U A)) = limUnder atTop (fun n ↦ νNat n A) := by
      congr 1
      funext n
      rw [hNuNatApply]
    _ = ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ νNat n ({i} : Set ℕ))) i :=
      countableSetwiseLimit_apply νNat hNuNatLim A
    _ = ∑' i, A.indicator (fun i ↦ limUnder atTop (fun n ↦ μ n (f i))) i := by
      refine tsum_congr ?_
      intro i
      by_cases hi : i ∈ A
      · simp [hi, hNuNatApply, hUsingleton, U]
      · simp [hi]

private theorem finiteMeasurePointwiseLimit_iUnion
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x))
    (f : ℕ → Set Ω) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (fun i j ↦ Disjoint (f i) (f j))) :
    limUnder atTop (fun n ↦ μ n (⋃ i, f i)) =
      ∑' i, limUnder atTop (fun n ↦ μ n (f i)) := by
  -- Route correction: reduce the disjoint-family union to a countable discrete set-function on
  -- subsets of `Nat`, instead of forcing continuity from above for arbitrary tails.
  simpa [Set.iUnion_true] using
    finiteMeasurePointwiseLimit_subsetBiUnion μ hlim f hf hd (Set.univ : Set ℕ)

/-- Exercise 1.3.3: If a sequence of finite measures converges setwise on every measurable set,
then the pointwise limit set-function `A ↦ limUnder atTop (fun n ↦ μ n A)` is a measure, namely
`finiteMeasurePointwiseLimitMeasure μ hlim`. -/
noncomputable def finiteMeasurePointwiseLimitMeasure
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x)) :
    Measure Ω :=
  Measure.ofMeasurable
    (fun A _ ↦ limUnder atTop (fun n ↦ μ n A))
    (finiteMeasurePointwiseLimit_empty μ hlim)
    (fun f hf hd ↦ finiteMeasurePointwiseLimit_iUnion μ hlim f hf hd)

/-- On each measurable set, `finiteMeasurePointwiseLimitMeasure μ hlim` is given by the setwise
limit of the values `μ n A`. -/
theorem finiteMeasurePointwiseLimitMeasure_apply
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x))
    (A : Set Ω) (hA : MeasurableSet A) :
    finiteMeasurePointwiseLimitMeasure μ hlim A = limUnder atTop (fun n ↦ μ n A) := by
  rw [finiteMeasurePointwiseLimitMeasure]
  exact Measure.ofMeasurable_apply A hA

-- Proof sketch: combine `finiteMeasurePointwiseLimitMeasure_apply` with the general fact that a
-- convergent net tends to its `limUnder` value.
/-- On each measurable set, the original sequence converges to the value of
`finiteMeasurePointwiseLimitMeasure μ hlim`. -/
theorem tendsto_finiteMeasurePointwiseLimitMeasure_apply
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x))
    (A : Set Ω) (hA : MeasurableSet A) :
    Tendsto (fun n ↦ μ n A) atTop (𝓝 (finiteMeasurePointwiseLimitMeasure μ hlim A)) := by
  rw [finiteMeasurePointwiseLimitMeasure_apply μ hlim A hA]
  exact tendsto_nhds_limUnder (hlim A hA)
