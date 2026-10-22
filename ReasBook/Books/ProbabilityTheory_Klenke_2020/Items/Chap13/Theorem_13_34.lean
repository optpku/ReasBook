/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_29

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

universe u

namespace MeasureTheory
namespace FiniteMeasure

variable {E : Type u} [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/-- Helper for Theorem 13.34: all bounded continuous real-valued tests separate subprobability
finite measures once they are viewed as ambient measures. -/
private theorem allBoundedContinuous_isSeparatingFamilyForSubprobabilities :
    IsSeparatingFamilyFor
        (((↑) : FiniteMeasure E → Measure E) '' {ν : FiniteMeasure E | ν.mass ≤ 1})
        (((↑) : (E →ᵇ ℝ) → E → ℝ) '' (Set.univ : Set (E →ᵇ ℝ))) := by
  unfold IsSeparatingFamilyFor
  constructor
  · intro f hf
    -- Proof comment: membership in the image family means `f` is the underlying function of a
    -- bounded continuous map, hence measurable.
    rcases hf with ⟨g, -, rfl⟩
    exact g.continuous.measurable
  · intro μ ν hμ hν hInt
    -- Proof comment: unwrap the subprobability finite measures behind `μ` and `ν`, then use the
    -- owner extensionality theorem for finite measures tested on all bounded continuous functions.
    rcases hμ with ⟨μ', hμ', rfl⟩
    rcases hν with ⟨ν', hν', rfl⟩
    exact congrArg ((↑) : FiniteMeasure E → Measure E) <|
      FiniteMeasure.ext_of_forall_integral_eq fun g ↦
        hInt (by exact ⟨g, Set.mem_univ g, rfl⟩) (g.integrable (μ' : Measure E))
          (g.integrable (ν' : Measure E))

/-- Helper for Theorem 13.34: a weak limit of subprobability finite measures is again a
subprobability. -/
private theorem limitMass_le_one_of_tendsto_subprobability
    {νs : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (hν : Tendsto νs atTop (𝓝 ν)) (hνs : ∀ n, (νs n).mass ≤ 1) :
    ν.mass ≤ 1 := by
  let S : Set (FiniteMeasure E) := {η : FiniteMeasure E | η.mass ≤ 1}
  have hS_closed : IsClosed S := isClosed_le FiniteMeasure.continuous_mass continuous_const
  have hS_eventually : ∀ᶠ n in atTop, νs n ∈ S := Filter.Eventually.of_forall hνs
  -- Proof comment: the subprobability condition is closed because mass is continuous.
  exact hS_closed.mem_of_tendsto hν hS_eventually

/-- Helper for Theorem 13.34: a weak subsequential limit agreeing with `μ` on a separating family
must equal `μ`. -/
private theorem limit_eq_of_tendsto_on_separatingFamily
    {νs : ℕ → FiniteMeasure E} {ν μ : FiniteMeasure E} {𝒞 : Set (E →ᵇ ℝ)}
    (hsep :
      IsSeparatingFamilyFor
        (((↑) : FiniteMeasure E → Measure E) '' {η : FiniteMeasure E | η.mass ≤ 1})
        (((↑) : (E →ᵇ ℝ) → E → ℝ) '' 𝒞))
    (hν : Tendsto νs atTop (𝓝 ν)) (hνs : ∀ n, (νs n).mass ≤ 1) (hμ : μ.mass ≤ 1)
    (hInt :
      ∀ ⦃f : E →ᵇ ℝ⦄, f ∈ 𝒞 →
        Tendsto (fun n ↦ ∫ x, f x ∂(νs n : Measure E)) atTop
          (𝓝 (∫ x, f x ∂(μ : Measure E)))) :
    ν = μ := by
  have hν_mass : ν.mass ≤ 1 := limitMass_le_one_of_tendsto_subprobability hν hνs
  apply FiniteMeasure.toMeasure_injective
  -- Proof comment: both limit measures lie in the subprobability class, so the separating-family
  -- axiom reduces equality to the agreement of all test integrals from `𝒞`.
  exact IsSeparatingFamilyFor.eq_of_forall_integral_eq hsep
    (by exact ⟨ν, hν_mass, rfl⟩) (by exact ⟨μ, hμ, rfl⟩) <| by
      intro f hf _ _
      rcases hf with ⟨g, hg, rfl⟩
      -- Proof comment: the same real sequence of integrals converges both to the `ν`-integral,
      -- by weak convergence, and to the `μ`-integral, by the separating-family hypothesis.
      exact tendsto_nhds_unique
        ((FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν) g) (hInt hg)

/-- Helper for Theorem 13.34: an infinite set of chosen indices contains a strictly monotone
subsequence whose values dominate the identity. -/
private theorem exists_strictMono_subseq_ge_of_infinite_range
    (k : ℕ → ℕ) (hRangeInfinite : (Set.range k).Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, n ≤ k (φ n) := by
  have hFreq :
      ∀ N : ℕ, ∃ᶠ n in atTop, N ≤ k n := by
    intro N
    have hLarge : {n : ℕ | N ≤ k n}.Infinite := by
      by_contra hLargeFinite
      have hRangeSubset :
          Set.range k ⊆ Set.Iio N ∪ k '' {n : ℕ | N ≤ k n} := by
        rintro m ⟨n, rfl⟩
        by_cases hN : N ≤ k n
        · exact Or.inr ⟨n, hN, rfl⟩
        · exact Or.inl (lt_of_not_ge hN)
      have hLargeFinite' : {n : ℕ | N ≤ k n}.Finite := by
        by_contra hLargeInfinite
        exact hLargeFinite hLargeInfinite
      have hRangeFinite : (Set.range k).Finite :=
        ((Set.finite_Iio N).union (hLargeFinite'.image k)).subset hRangeSubset
      exact hRangeInfinite hRangeFinite
    simpa [Nat.cofinite_eq_atTop] using
      (Set.Infinite.frequently_cofinite hLarge :
        ∃ᶠ n in cofinite, n ∈ {n : ℕ | N ≤ k n})
  exact extraction_forall_of_frequently hFreq

/-- Helper for Theorem 13.34: if the chosen indices take only finitely many values, then one value
occurs along a strictly monotone constant subsequence. -/
private theorem exists_constant_subseq_of_finite_range
    (k : ℕ → ℕ) (hRangeFinite : (Set.range k).Finite) :
    ∃ m : ℕ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, k (φ n) = m := by
  classical
  letI := hRangeFinite.fintype
  obtain ⟨m, hmInfinite⟩ :=
    Finite.exists_infinite_fiber (fun n ↦ (⟨k n, ⟨n, rfl⟩⟩ : Set.range k))
  have hmInfiniteSet :
      ((fun n ↦ (⟨k n, ⟨n, rfl⟩⟩ : Set.range k)) ⁻¹' {m}).Infinite := by
    exact infinite_coe_iff.mp hmInfinite
  have hFreqSubtype : ∃ᶠ n in atTop, (⟨k n, ⟨n, rfl⟩⟩ : Set.range k) = m := by
    simpa [Nat.cofinite_eq_atTop] using
      (Set.Infinite.frequently_cofinite hmInfiniteSet :
        ∃ᶠ n in cofinite, n ∈ ((fun n ↦ (⟨k n, ⟨n, rfl⟩⟩ : Set.range k)) ⁻¹' {m}))
  have hFreq : ∃ᶠ n in atTop, k n = m.1 := by
    exact hFreqSubtype.mono fun n hn ↦ congrArg Subtype.val hn
  obtain ⟨φ, hφ, hφconst⟩ := extraction_of_frequently_atTop hFreq
  exact ⟨m.1, φ, hφ, hφconst⟩

/-- Helper for Theorem 13.34: every sequence taking values in the range of a weakly convergent
subprobability sequence admits a weakly convergent subsequence. -/
private theorem exists_convergent_subseq_of_sequence_in_range_of_tendsto
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (hweak : Tendsto μs atTop (𝓝 μ))
    (νs : ℕ → FiniteMeasure E) (hνs : ∀ n, νs n ∈ Set.range μs) :
    ∃ ν : FiniteMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (νs ∘ φ) atTop (𝓝 ν) := by
  classical
  choose k hk using hνs
  by_cases hRangeInfinite : (Set.range k).Infinite
  · obtain ⟨φ, hφ, hφbound⟩ := exists_strictMono_subseq_ge_of_infinite_range k hRangeInfinite
    have hkTendsto : Tendsto (fun n ↦ k (φ n)) atTop atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro N
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro n hn
      exact (hn.trans (hφbound n))
    -- Proof comment: unbounded chosen indices inherit the original weak limit `μ`.
    refine ⟨μ, φ, hφ, ?_⟩
    have hEq : νs ∘ φ = μs ∘ (k ∘ φ) := by
      funext n
      rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, ← hk (φ n)]
    rw [hEq]
    exact hweak.comp hkTendsto
  · have hRangeFinite : (Set.range k).Finite := by
      by_contra hRangeInfinite'
      exact hRangeInfinite hRangeInfinite'
    obtain ⟨m, φ, hφ, hφconst⟩ := exists_constant_subseq_of_finite_range k hRangeFinite
    -- Proof comment: a finite index range yields a constant subsequence.
    refine ⟨μs m, φ, hφ, ?_⟩
    have hConst : νs ∘ φ = fun _ ↦ μs m := by
      funext n
      rw [Function.comp_apply, ← hk (φ n), hφconst n]
    rw [hConst]
    exact tendsto_const_nhds

/-- Helper for Theorem 13.34: every sequence in a tight subprobability family has a weakly
convergent subsequence. -/
private theorem exists_subseq_tendsto_of_tight_family
    (ℱ : Set (FiniteMeasure E))
    (hTight : IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' ℱ))
    (hℱ : ∀ η ∈ ℱ, η.mass ≤ 1)
    (νs : ℕ → FiniteMeasure E) (hνs : ∀ n, νs n ∈ ℱ) :
    ∃ ν : FiniteMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (νs ∘ φ) atTop (𝓝 ν) := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable E
  exact
    isWeaklyRelativelySequentiallyCompactFamily_of_isTightMeasureSet
      (ℱ := ℱ) hℱ hTight νs hνs

-- Proof sketch: weak convergence implies tightness by Prohorov's theorem and gives convergence of
-- the integrals of every bounded continuous test function, hence of any separating subfamily. For
-- the converse, combine tightness with relative sequential compactness, pass to weakly convergent
-- subsequences, and use the separating family to identify every subsequential limit with `μ`.
/-- Theorem 13.34: for subprobability finite measures on a Polish space, weak convergence to `μ`
is equivalent to tightness of the sequence together with convergence of the integrals on some
separating family of bounded continuous real-valued test functions. -/
theorem tendsto_iff_isTightFamily_and_exists_separating_boundedContinuousFamily
    (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) (hμ : μ.mass ≤ 1)
    (hμs : ∀ n, (μs n).mass ≤ 1) :
    Tendsto μs atTop (𝓝 μ) ↔
      IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' Set.range μs) ∧
        ∃ 𝒞 : Set (E →ᵇ ℝ),
          IsSeparatingFamilyFor
              (((↑) : FiniteMeasure E → Measure E) ''
                {ν : FiniteMeasure E | ν.mass ≤ 1})
              (((↑) : (E →ᵇ ℝ) → E → ℝ) '' 𝒞) ∧
            ∀ ⦃f : E →ᵇ ℝ⦄, f ∈ 𝒞 →
              Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
                (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  constructor
  · intro hweak
    letI := TopologicalSpace.upgradeIsCompletelyMetrizable E
    have hRangeMass : ∀ η ∈ Set.range μs, η.mass ≤ 1 := by
      intro η hη
      rcases hη with ⟨n, rfl⟩
      exact hμs n
    have hRangeSeq :
        ∀ νs : ℕ → FiniteMeasure E, (∀ n, νs n ∈ Set.range μs) →
          ∃ ν : FiniteMeasure E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (νs ∘ φ) atTop (𝓝 ν) := by
      intro νs hνs
      exact exists_convergent_subseq_of_sequence_in_range_of_tendsto hweak νs hνs
    have hTightRange :
        IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' Set.range μs) :=
      isTightMeasureSet_of_isWeaklyRelativelySequentiallyCompactFamily
        (ℱ := Set.range μs) hRangeMass hRangeSeq
    refine ⟨hTightRange, Set.univ,
      allBoundedContinuous_isSeparatingFamilyForSubprobabilities, ?_⟩
    intro f _
    -- Proof comment: weak convergence is exactly convergence of the integrals of every bounded
    -- continuous test function.
    exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) f
  · rintro ⟨hTight, 𝒞, hsep, hTest⟩
    -- Proof comment: use the subsequence criterion, then identify every extracted weak limit with
    -- `μ` via the separating family.
    refine Filter.tendsto_of_subseq_tendsto ?_
    intro ns hns
    have hRangeMass : ∀ η ∈ Set.range μs, η.mass ≤ 1 := by
      intro η hη
      rcases hη with ⟨n, rfl⟩
      exact hμs n
    obtain ⟨ν, φ, hφ, hν⟩ :=
      exists_subseq_tendsto_of_tight_family (Set.range μs) hTight hRangeMass (μs ∘ ns) (by
        intro n
        exact ⟨ns n, rfl⟩)
    have hν_eq : ν = μ := by
      refine limit_eq_of_tendsto_on_separatingFamily hsep hν
        (fun n ↦ hμs (ns (φ n))) hμ ?_
      intro f hf
      exact (hTest hf).comp (hns.comp hφ.tendsto_atTop)
    refine ⟨φ, ?_⟩
    simpa [Function.comp, hν_eq] using hν

end FiniteMeasure
end MeasureTheory
