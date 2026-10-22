/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_34
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

universe u v

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {E : Type u}

/- Layering for Lemma 19.24:
- `source-facing`: the finite-boundary effective conductances
  `conductance C x₁ * escapeToSetProbability P X x₁ A₀`.
- `core/canonical`: `conductance`, `escapeToSetProbability`, and
  `effectiveConductanceToInfinity C P X x₁` from Definition 19.23.
- `bridge/view`: `Set.DecreasesTo A₀ ∅` encodes the decreasing cofinite exhaustion used in the
  limit statement. -/

-- Proof sketch: unfold `effectiveConductanceToInfinity`; it is the infimum of the finite-boundary
-- conductances `conductance C x₁ * escapeToSetProbability P X x₁ A₀` over cofinite `A₀`
-- avoiding `x₁`. A decreasing exhaustion `A₀ n ↓ ∅` is cofinal in that family, and monotonicity
-- of `A₀ ↦ escapeToSetProbability P X x₁ A₀`, supplied by the owner theorem
-- `escapeToSetProbability_mono`, identifies the limit with the same infimum. The extra hypothesis
-- `conductance C x₁ < ∞` is the minimal condition ensuring multiplication by `conductance C x₁`
-- preserves that decreasing limit in `ℝ≥0∞`.
/-- Helper for Lemma 19.24: a decreasing sequence of sets with empty intersection and one finite
stage is eventually empty. -/
private theorem eventually_eq_empty_of_antitone_iInter_eq_empty_of_finite
    {s : ℕ → Set E} (hanti : Antitone s) (hInter : (⋂ n, s n) = (∅ : Set E))
    {N : ℕ} (hfinite : (s N).Finite) :
    ∃ M, ∀ n ≥ M, s n = ∅ := by
  classical
  -- Every point in the finite stage disappears at some later time, otherwise it would survive in
  -- the intersection.
  have hEventuallyNotMem : ∀ x ∈ s N, ∃ m ≥ N, x ∉ s m := by
    intro x hx
    by_contra hxDisappear
    push Not at hxDisappear
    have hxInter : x ∈ ⋂ n, s n := by
      refine mem_iInter.mpr ?_
      intro n
      by_cases hn : n < N
      · exact hanti (Nat.le_of_lt hn) hx
      · exact hxDisappear n (le_of_not_gt hn)
    simp [hInter] at hxInter
  let witness : E → ℕ := fun x ↦
    if hx : x ∈ s N then Nat.find (hEventuallyNotMem x hx) else N
  let M := max N (hfinite.toFinset.sup witness)
  refine ⟨M, ?_⟩
  intro n hn
  ext x
  constructor
  · intro hx
    -- A point in a late stage lies in the finite stage `s N`, so its witness index is bounded by
    -- `n` and antitonicity forces a contradiction.
    have hNn : N ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hxN : x ∈ s N := hanti hNn hx
    have hxFinset : x ∈ hfinite.toFinset := by
      simpa using hxN
    have hw_le : witness x ≤ n := by
      exact le_trans (Finset.le_sup hxFinset) (le_trans (Nat.le_max_right _ _) hn)
    have hw_eq : witness x = Nat.find (hEventuallyNotMem x hxN) := by
      simp [witness, hxN]
    have hxWitnessNot : x ∉ s (witness x) := by
      rw [hw_eq]
      exact (Nat.find_spec (hEventuallyNotMem x hxN)).2
    exact (hxWitnessNot (hanti hw_le hx)).elim
  · simp

/-- Helper for Lemma 19.24: a decreasing exhaustion of `∅` eventually lies inside every cofinite
set. -/
private theorem exists_subset_of_cofinite_of_decreasesTo_empty
    {A₀ : ℕ → Set E} (hA₀ : Set.DecreasesTo A₀ (∅ : Set E))
    {B : Set E} (hBfinite : Bᶜ.Finite) :
    ∃ n, A₀ n ⊆ B := by
  classical
  let s : ℕ → Set E := fun n ↦ A₀ n ∩ Bᶜ
  -- Intersect the exhaustion with the finite complement and apply the eventual-emptiness lemma.
  have hsanti : Antitone s := by
    intro m n hmn x hx
    exact ⟨hA₀.antitone hmn hx.1, hx.2⟩
  have hsInter : (⋂ n, s n) = (∅ : Set E) := by
    ext x
    constructor
    · intro hx
      have hxA : x ∈ ⋂ n, A₀ n := by
        refine mem_iInter.mpr ?_
        intro n
        exact (mem_iInter.mp hx n).1
      simp [hA₀.iInter_eq] at hxA
    · simp
  have hsFinite : (s 0).Finite := by
    refine hBfinite.subset ?_
    intro x hx
    exact hx.2
  obtain ⟨n, hn⟩ :=
    eventually_eq_empty_of_antitone_iInter_eq_empty_of_finite hsanti hsInter hsFinite
  refine ⟨n, ?_⟩
  intro x hxA
  by_contra hxB
  have hxS : x ∈ s n := ⟨hxA, hxB⟩
  have hsEmpty : s n = ∅ := hn n le_rfl
  simp [hsEmpty] at hxS

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- Helper for Lemma 19.24: the infimum along a decreasing cofinite exhaustion matches the cofinite
infimum from `effectiveConductanceToInfinity`. -/
private theorem iInf_escapeToSetProbability_eq_sInf_cofinite
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {x₁ : E} {A₀ : ℕ → Set E}
    (hA₀ : Set.DecreasesTo A₀ (∅ : Set E))
    (hfinite : ∀ n, (A₀ n)ᶜ.Finite)
    (hx₁ : ∀ n, x₁ ∉ A₀ n) :
    (⨅ n, escapeToSetProbability P X x₁ (A₀ n)) =
      sInf {r : ℝ≥0∞ |
        ∃ B : Set E, Bᶜ.Finite ∧ x₁ ∉ B ∧ r = escapeToSetProbability P X x₁ B} := by
  let f : ℕ → ℝ≥0∞ := fun n ↦ escapeToSetProbability P X x₁ (A₀ n)
  have hmono : Monotone (escapeToSetProbability P X x₁) := escapeToSetProbability_mono P X x₁
  -- One inequality is immediate because every exhaustion term is an admissible cofinite set.
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    intro r hr
    rcases hr with ⟨B, hBfinite, -, rfl⟩
    obtain ⟨n, hn⟩ := exists_subset_of_cofinite_of_decreasesTo_empty hA₀ hBfinite
    exact le_trans (iInf_le f n) (hmono hn)
  · refine le_iInf ?_
    intro n
    exact sInf_le ⟨A₀ n, hfinite n, hx₁ n, rfl⟩

/-- Helper for Lemma 19.24: the escape-to-set probabilities along a decreasing cofinite exhaustion
converge to the cofinite infimum from Definition 19.23. -/
private theorem tendsto_escapeToSetProbability_of_decreasing_finite_complement
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {x₁ : E} {A₀ : ℕ → Set E}
    (hA₀ : Set.DecreasesTo A₀ (∅ : Set E))
    (hfinite : ∀ n, (A₀ n)ᶜ.Finite)
    (hx₁ : ∀ n, x₁ ∉ A₀ n) :
    Tendsto (fun n ↦ escapeToSetProbability P X x₁ (A₀ n)) atTop
      (nhds (sInf {r : ℝ≥0∞ |
        ∃ B : Set E, Bᶜ.Finite ∧ x₁ ∉ B ∧ r = escapeToSetProbability P X x₁ B})) := by
  have hmono : Monotone (escapeToSetProbability P X x₁) := escapeToSetProbability_mono P X x₁
  have hanti : Antitone (fun n ↦ escapeToSetProbability P X x₁ (A₀ n)) := by
    intro m n hmn
    exact hmono (hA₀.antitone hmn)
  -- Monotone convergence identifies the decreasing sequence with its infimum.
  simpa [iInf_escapeToSetProbability_eq_sInf_cofinite hA₀ hfinite hx₁] using
    (tendsto_atTop_iInf hanti :
      Tendsto (fun n ↦ escapeToSetProbability P X x₁ (A₀ n)) atTop
        (nhds (⨅ n, escapeToSetProbability P X x₁ (A₀ n))))

/-- Lemma 19.24: if `A₀ n` decreases to `∅`, each complement `A₀ nᶜ` is finite,
`x₁ ∉ A₀ n`, and `conductance C x₁ < ∞`, then the finite-boundary effective conductances from `x₁`
to `A₀ n` converge to the effective conductance from `x₁` to infinity. -/
theorem effectiveConductanceToInfinity_tendsto_of_decreasing_finite_complement
    {C : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {x₁ : E}
    {A₀ : ℕ → Set E}
    (hA₀ : Set.DecreasesTo A₀ (∅ : Set E))
    (hfinite : ∀ n, (A₀ n)ᶜ.Finite)
    (hx₁ : ∀ n, x₁ ∉ A₀ n)
    (hconductance : conductance C x₁ < ∞) :
    Tendsto (fun n ↦ conductance C x₁ * escapeToSetProbability P X x₁ (A₀ n)) atTop
      (nhds (effectiveConductanceToInfinity C P X x₁)) := by
  -- First identify the limiting escape probability with the cofinite infimum from the definition.
  have hEscape :
      Tendsto (fun n ↦ escapeToSetProbability P X x₁ (A₀ n)) atTop
        (nhds (sInf {r : ℝ≥0∞ |
          ∃ B : Set E, Bᶜ.Finite ∧ x₁ ∉ B ∧ r = escapeToSetProbability P X x₁ B})) :=
    tendsto_escapeToSetProbability_of_decreasing_finite_complement hA₀ hfinite hx₁
  -- Then multiply the limit by the fixed conductance factor and unfold Definition 19.23.
  simpa [effectiveConductanceToInfinity_def] using
    ENNReal.Tendsto.const_mul hEscape (Or.inr hconductance.ne)

end ProbabilityTheory
