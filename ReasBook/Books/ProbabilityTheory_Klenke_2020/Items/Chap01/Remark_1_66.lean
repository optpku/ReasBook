/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_65

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal symmDiff

universe u

-- Proof sketch: apply the `σ(𝒜)`-approximation hypotheses to the measurable lower and upper hulls
-- supplied by the null-sandwich assumption, then transfer the error estimates across the null gap
-- between those hulls and the original `μ`-Carathéodory measurable set.
/-- Remark 1.66: If the countable-cover and finite symmetric-difference approximation statements
hold on `σ(𝒜)` and every `μ`-Carathéodory measurable set is sandwiched between
`σ(𝒜)`-measurable sets with null outer-measure gap, then the same approximation conclusions hold
for all `μ`-Carathéodory measurable sets. -/
theorem caratheodory_approximation_extends_from_generateFrom {Ω : Type u}
    (μ : OuterMeasure Ω) (𝒜 : Set (Set Ω))
    (hcover :
      ∀ A : Set Ω, MeasurableSet[MeasurableSpace.generateFrom 𝒜] A →
        ∀ ε : ℝ, 0 < ε →
          ∃ s : ℕ → Set Ω,
            (∀ n, s n ∈ 𝒜) ∧
            Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧
            A ⊆ ⋃ n, s n ∧
            μ ((⋃ n, s n) \ A) < ENNReal.ofReal ε)
    (hfin :
      ∀ A : Set Ω, MeasurableSet[MeasurableSpace.generateFrom 𝒜] A → μ A < ∞ →
        ∀ ε : ℝ, 0 < ε →
          ∃ (n : ℕ) (s : Fin n → Set Ω),
            (∀ i, s i ∈ 𝒜) ∧
            Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧
            μ (A ∆ ⋃ i, s i) < ENNReal.ofReal ε)
    (hsandwich :
      ∀ A : Set Ω, MeasurableSet[μ.caratheodory] A →
        ∃ Aminus Aplus : Set Ω,
          MeasurableSet[MeasurableSpace.generateFrom 𝒜] Aminus ∧
          MeasurableSet[MeasurableSpace.generateFrom 𝒜] Aplus ∧
          Aminus ⊆ A ∧
          A ⊆ Aplus ∧
          μ (Aplus \ Aminus) = 0) :
    (∀ A : Set Ω, MeasurableSet[μ.caratheodory] A →
      ∀ ε : ℝ, 0 < ε →
        ∃ s : ℕ → Set Ω,
          (∀ n, s n ∈ 𝒜) ∧
          Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧
          A ⊆ ⋃ n, s n ∧
          μ ((⋃ n, s n) \ A) < ENNReal.ofReal ε) ∧
      (∀ A : Set Ω, MeasurableSet[μ.caratheodory] A → μ A < ∞ →
        ∀ ε : ℝ, 0 < ε →
          ∃ (n : ℕ) (s : Fin n → Set Ω),
            (∀ i, s i ∈ 𝒜) ∧
            Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧
            μ (A ∆ ⋃ i, s i) < ENNReal.ofReal ε) := by
  constructor
  · intro A hA ε hε
    rcases hsandwich A hA with ⟨Aminus, Aplus, hAminus, hAplus, hAminusA, hAAplus, hgap⟩
    rcases hcover Aplus hAplus ε hε with ⟨s, hs_mem, hs_disjoint, hAplus_subset, hs_diff_lt⟩
    refine ⟨s, hs_mem, hs_disjoint, hAAplus.trans hAplus_subset, ?_⟩
    have hAplus_diff_zero : μ (Aplus \ A) = 0 := by
      refine measure_mono_null ?_ hgap
      intro x hx
      exact ⟨hx.1, fun hxAminus ↦ hx.2 (hAminusA hxAminus)⟩
    have hsubset :
        (⋃ n, s n) \ A ⊆ ((⋃ n, s n) \ Aplus) ∪ (Aplus \ A) := by
      intro x hx
      by_cases hxAplus : x ∈ Aplus
      · exact Or.inr ⟨hxAplus, hx.2⟩
      · exact Or.inl ⟨hx.1, hxAplus⟩
    calc
      μ ((⋃ n, s n) \ A) ≤ μ (((⋃ n, s n) \ Aplus) ∪ (Aplus \ A)) := measure_mono hsubset
      _ ≤ μ ((⋃ n, s n) \ Aplus) + μ (Aplus \ A) := measure_union_le _ _
      _ = μ ((⋃ n, s n) \ Aplus) := by rw [hAplus_diff_zero, add_zero]
      _ < ENNReal.ofReal ε := hs_diff_lt
  · intro A hA hμA ε hε
    rcases hsandwich A hA with ⟨Aminus, Aplus, hAminus, hAplus, hAminusA, hAAplus, hgap⟩
    have hAminus_finite : μ Aminus < ∞ := lt_of_le_of_lt (measure_mono hAminusA) hμA
    rcases hfin Aminus hAminus hAminus_finite ε hε with ⟨n, s, hs_mem, hs_disjoint, hs_diff_lt⟩
    refine ⟨n, s, hs_mem, hs_disjoint, ?_⟩
    have hA_diff_zero : μ (A \ Aminus) = 0 := by
      refine measure_mono_null ?_ hgap
      intro x hx
      exact ⟨hAAplus hx.1, hx.2⟩
    have hsubset :
        A ∆ ⋃ i, s i ⊆ (A \ Aminus) ∪ (Aminus ∆ ⋃ i, s i) := by
      intro x hx
      rcases hx with hx | hx
      · by_cases hxAminus : x ∈ Aminus
        · exact Or.inr (Or.inl ⟨hxAminus, hx.2⟩)
        · exact Or.inl ⟨hx.1, hxAminus⟩
      · exact Or.inr (Or.inr ⟨hx.1, fun hxAminus ↦ hx.2 (hAminusA hxAminus)⟩)
    calc
      μ (A ∆ ⋃ i, s i) ≤ μ ((A \ Aminus) ∪ (Aminus ∆ ⋃ i, s i)) := measure_mono hsubset
      _ ≤ μ (A \ Aminus) + μ (Aminus ∆ ⋃ i, s i) := measure_union_le _ _
      _ = μ (Aminus ∆ ⋃ i, s i) := by rw [hA_diff_zero, zero_add]
      _ < ENNReal.ofReal ε := hs_diff_lt

-- Proof sketch: `Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite` says that every
-- measurable set of finite measure can be approximated in symmetric-difference measure by members
-- of the algebra. Therefore the set of values `μ (A ∆ B)` with `B ∈ 𝒜` has infimum `0`.
/-- In the sigma-finite algebra case, the symmetric-difference distances from a measurable set of
finite measure to members of the algebra have infimum `0`. -/
theorem symmDiff_sInf_eq_zero_of_generateFrom_isSetAlgebra_sigmaFinite {Ω : Type u}
    [m : MeasurableSpace Ω] (μ : Measure Ω) (𝒜 : Set (Set Ω)) (h𝒜 : IsSetAlgebra 𝒜)
    (S : μ.FiniteSpanningSetsIn 𝒜) (hgen : m = MeasurableSpace.generateFrom 𝒜)
    (A : Set Ω) (hA : MeasurableSet A) (hμA : μ A < ∞) :
    sInf ((fun B : Set Ω ↦ μ (A ∆ B)) '' 𝒜) = 0 := by
  let hDense : μ.MeasureDense 𝒜 :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite h𝒜 S hgen
  apply ennreal_eq_zero_of_le_inv_succ
  intro k
  have hk_pos : 0 < 1 / (k + 1 : ℝ) := by
    positivity
  rcases hDense.approx A hA hμA.ne (1 / (k + 1 : ℝ)) hk_pos with ⟨B, hB, hBA⟩
  exact le_trans (sInf_le ⟨B, hB, rfl⟩) hBA.le
