/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set Filter
open scoped ENNReal Topology

universe u

variable {Ω : Type u} {C : Set (Set Ω)} {μ : AddContent ℝ≥0∞ C}

namespace AddContent

/-- Countable additivity of a content on pairwise disjoint sequences whose union stays in the ring
of sets. -/
def IsSigmaAdditiveOnRing (μ : AddContent ℝ≥0∞ C) : Prop :=
  ∀ ⦃s : ℕ → Set Ω⦄, (∀ n, s n ∈ C) → Pairwise (fun i j ↦ Disjoint (s i) (s j)) →
    (⋃ n, s n) ∈ C → μ (⋃ n, s n) = ∑' n, μ (s n)

/-- Finiteness of a content on the whole ring of sets. -/
def IsFiniteOnRing (μ : AddContent ℝ≥0∞ C) : Prop :=
  ∀ s ∈ C, μ s < ⊤

end AddContent

-- Proof sketch: use the standard ring-of-sets theorem turning sigma-subadditivity into countable
-- additivity on pairwise disjoint unions, derive lower semicontinuity from sigma-additivity via
-- continuity from below of partial unions, and recover sigma-additivity from lower
-- semicontinuity using the disjoint accumulated unions.
/-- Theorem 1.36: For a content on a ring of sets, countable additivity on pairwise disjoint
unions, `σ`-subadditivity, and lower semicontinuity are equivalent. -/
theorem content_tfae_isSigmaAdditive_isSigmaSubadditive_isLowerSemicontinuous
    (hC : IsSetRing C) (μ : AddContent ℝ≥0∞ C) :
    List.TFAE
      [AddContent.IsSigmaAdditiveOnRing μ, μ.IsSigmaSubadditive,
        AddContent.IsLowerSemicontinuous μ] := by
  -- The equivalence is organized exactly as in the textbook: use the ring-of-sets
  -- `σ`-subadditivity theorem, continuity from below for monotone unions, and
  -- finite accumulated unions for the converse implication.
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hσ
      -- Reuse the standard ring-of-sets theorem once countable additivity is in the
      -- expected `iUnion = tsum` form.
      have hσ' :
          ∀ (f : ℕ → Set Ω), (∀ i, f i ∈ C) → (⋃ i, f i) ∈ C →
            Pairwise (Function.onFun Disjoint f) → μ (⋃ i, f i) = ∑' i, μ (f i) := by
        intro f hf hUnion hdisj
        exact hσ hf hdisj hUnion
      exact MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum hC hσ'
    · intro hsub s hs hdisj hUnion
      -- For pairwise disjoint unions, the existing semiring theorem upgrades
      -- `σ`-subadditivity back to countable additivity.
      exact MeasureTheory.addContent_iUnion_eq_tsum_of_disjoint_of_IsSigmaSubadditive
        hC.isSetSemiring hsub s hs hUnion hdisj
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hσ
      refine ⟨?_⟩
      intro A hA s hs hs_inc
      -- Continuity from below is the monotone-union theorem for additive contents.
      have hUnion : (⋃ n, s n) ∈ C := by simpa [hs_inc.iUnion_eq] using hA
      have hσ' :
          ∀ (f : ℕ → Set Ω), (∀ i, f i ∈ C) → (⋃ i, f i) ∈ C →
            Pairwise (Function.onFun Disjoint f) → μ (⋃ i, f i) = ∑' i, μ (f i) := by
        intro f hf hUnion' hdisj
        exact hσ hf hdisj hUnion'
      simpa [hs_inc.iUnion_eq] using
        (MeasureTheory.tendsto_atTop_addContent_iUnion_of_addContent_iUnion_eq_tsum
          hC hσ' hs_inc.mono hs hUnion)
    · intro hlower s hs hdisj hUnion
      -- Apply lower semicontinuity to the increasing accumulated unions.
      have h_acc_tendsto :
          Tendsto (μ ∘ Set.accumulate s) atTop (𝓝 (μ (⋃ n, s n))) := by
        simpa using hlower.tendsto_of_monotone hUnion (fun n ↦ hC.accumulate_mem hs n)
          monotone_accumulate
          (Set.iUnion_accumulate (s := s))
      -- Each accumulated union has content equal to the corresponding finite partial sum.
      have h_partial :
          ∀ n, μ (Set.accumulate s n) = ∑ i ∈ Finset.range (n + 1), μ (s i) := by
        intro n
        simpa using MeasureTheory.addContent_accumulate μ hC hdisj hs n
      have h_sum_tendsto :
          Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + 1), μ (s i)) atTop
            (𝓝 (∑' n, μ (s n))) := by
        rw [tendsto_add_atTop_iff_nat (f := fun k ↦ ∑ i ∈ Finset.range k, μ (s i)) 1]
        exact ENNReal.tendsto_nat_tsum fun n ↦ μ (s n)
      have h_partial_tendsto :
          Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + 1), μ (s i)) atTop
            (𝓝 (μ (⋃ n, s n))) := by
        refine h_acc_tendsto.congr' ?_
        exact Filter.Eventually.of_forall fun n ↦ by
          simpa [Function.comp] using h_partial n
      exact tendsto_nhds_unique h_partial_tendsto h_sum_tendsto
  tfae_finish

-- Proof sketch: apply lower semicontinuity to the increasing sequence `s 0 \ s n`, whose union
-- is `s 0`, and then rewrite `μ (s 0 \ s n)` using finite additivity on the ring.
/-- A lower-semicontinuous content on a ring of sets is continuous at the empty set. -/
theorem addContent_isContinuousAtEmpty_of_isLowerSemicontinuous
    (hC : IsSetRing C) {μ : AddContent ℝ≥0∞ C}
    (hμ : AddContent.IsLowerSemicontinuous μ) :
    AddContent.IsContinuousAtEmpty μ := by
  refine ⟨?_⟩
  intro s hs hs_decr hfin
  rcases hfin with ⟨N, hN⟩
  let t : ℕ → Set Ω := fun n ↦ s N \ s (N + n)
  have ht_mem : ∀ n, t n ∈ C := by
    intro n
    exact hC.diff_mem (hs N) (hs (N + n))
  have ht_mono : Monotone t := by
    intro i j hij x hx
    exact ⟨hx.1, fun hxj ↦ hx.2 (by
      exact hs_decr.antitone (Nat.add_le_add_left hij N) hxj)⟩
  have ht_union : (⋃ n, t n) = s N := by
    classical
    ext x
    constructor
    · intro hx
      have hx' := (mem_iUnion.mp hx).choose_spec
      rw [mem_diff] at hx'
      exact hx'.1
    · intro hx
      have hx_not_mem : x ∉ ⋂ n, s n := by
        intro hx_inter
        simp [hs_decr.iInter_eq] at hx_inter
      simp only [mem_iInter, not_forall] at hx_not_mem
      rcases hx_not_mem with ⟨n, hn⟩
      have htail : x ∉ s (N + n) := by
        intro hxn
        exact hn (hs_decr.antitone (Nat.le_add_left n N) hxn)
      exact mem_iUnion.mpr ⟨n, ⟨hx, htail⟩⟩
  -- Lower semicontinuity controls the increasing difference sequence.
  have ht_tendsto : Tendsto (μ ∘ t) atTop (𝓝 (μ (s N))) := by
    simpa [t] using hμ.tendsto_of_monotone (hs N) ht_mem ht_mono ht_union
  have ht_le : ∀ n, μ (t n) ≤ μ (s N) := by
    intro n
    exact MeasureTheory.addContent_mono hC.isSetSemiring (ht_mem n) (hs N) diff_subset
  have h_sub_tendsto : Tendsto (fun n ↦ μ (s N) - μ (t n)) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_const_sub_nhds_zero_iff (ne_of_lt hN) ht_le).2 ht_tendsto
  have h_rewrite : ∀ n, μ (s N) - μ (t n) = μ (s (N + n)) := by
    intro n
    have hsubset : s (N + n) ⊆ s N := hs_decr.antitone (Nat.le_add_right N n)
    have ht_finite : μ (t n) < ⊤ := lt_of_le_of_lt (ht_le n) hN
    have h_add : μ (s N) = μ (s (N + n)) + μ (t n) := by
      simpa [t, Set.union_eq_right.mpr hsubset] using
        (addContent_union hC (hs (N + n)) (ht_mem n) disjoint_sdiff_self_right)
    exact (ENNReal.eq_sub_of_add_eq (ne_of_lt ht_finite) h_add.symm).symm
  -- Rewriting the complement terms recovers the original decreasing sequence.
  have h_tail_tendsto : Tendsto (fun n ↦ μ (s (N + n))) atTop (𝓝 0) := by
    simpa [h_rewrite] using h_sub_tendsto
  have h_tail_tendsto' : Tendsto (fun n ↦ μ (s (n + N))) atTop (𝓝 0) := by
    simpa [Nat.add_comm] using h_tail_tendsto
  simpa [Function.comp] using (tendsto_add_atTop_iff_nat N).mp h_tail_tendsto'

-- Proof sketch: for the forward implication, apply `∅`-continuity to the decreasing sequence
-- `s n \ A`; for the reverse implication, specialize upper semicontinuity to the limit set `∅`.
/-- On a ring of sets, continuity at the empty set is equivalent to upper semicontinuity. -/
theorem addContent_isContinuousAtEmpty_iff_isUpperSemicontinuous
    (hC : IsSetRing C) (μ : AddContent ℝ≥0∞ C) :
    AddContent.IsContinuousAtEmpty μ ↔ AddContent.IsUpperSemicontinuous μ := by
  constructor
  · intro hμ
    refine ⟨?_⟩
    intro A hA s hs hs_decr hfin
    rcases hfin with ⟨N, hN⟩
    let t : ℕ → Set Ω := fun n ↦ s (N + n) \ A
    have hA_subset : ∀ n, A ⊆ s n := by
      intro n x hx
      have hx : x ∈ ⋂ m, s m := by
        simpa [hs_decr.iInter_eq] using hx
      exact mem_iInter.mp hx n
    have ht_mem : ∀ n, t n ∈ C := by
      intro n
      exact hC.diff_mem (hs (N + n)) hA
    have ht_anti : Antitone t := by
      intro i j hij x hx
      exact ⟨by
        exact hs_decr.antitone (Nat.add_le_add_left hij N) hx.1, hx.2⟩
    have ht0_finite : μ (t 0) < ⊤ := by
      have ht0_le : μ (t 0) ≤ μ (s N) := by
        exact MeasureTheory.addContent_mono hC.isSetSemiring (ht_mem 0) (hs N) fun x hx ↦ hx.1
      exact lt_of_le_of_lt ht0_le hN
    have ht_inter : (⋂ n, t n) = (∅ : Set Ω) := by
      ext x
      constructor
      · intro hx
        have hxA : x ∈ A := by
          have hx_inter : x ∈ ⋂ n, s n := by
            refine mem_iInter.mpr ?_
            intro n
            have hx' := mem_iInter.mp hx n
            rw [mem_diff] at hx'
            exact hs_decr.antitone (Nat.le_add_left n N) hx'.1
          simpa [hs_decr.iInter_eq] using hx_inter
        have hx0 := mem_iInter.mp hx 0
        rw [mem_diff] at hx0
        exact hx0.2 hxA
      · intro hx
        simp at hx
    -- Continuity at `∅` applied to the difference sequence yields the error term tends to zero.
    have ht_tendsto : Tendsto (μ ∘ t) atTop (𝓝 0) := by
      exact hμ.tendsto ht_mem ⟨ht_anti, ht_inter⟩ ⟨0, ht0_finite⟩
    have h_add : ∀ n, μ (s (N + n)) = μ A + μ (t n) := by
      intro n
      simpa [t, Set.union_eq_right.mpr (hA_subset (N + n))] using
        (addContent_union hC hA (ht_mem n) disjoint_sdiff_self_right)
    -- Reassemble each `μ (s n)` as the limit set plus a vanishing remainder.
    have h_sum_tendsto : Tendsto (fun n ↦ μ A + μ (t n)) atTop (𝓝 (μ A)) := by
      simpa using (tendsto_const_nhds.add ht_tendsto)
    have hs_tendsto : Tendsto (fun n ↦ μ (s (N + n))) atTop (𝓝 (μ A)) := by
      refine h_sum_tendsto.congr' ?_
      exact Filter.Eventually.of_forall fun n ↦ by
        simpa using (h_add n).symm
    have hs_tendsto' : Tendsto (fun n ↦ μ (s (n + N))) atTop (𝓝 (μ A)) := by
      simpa [Nat.add_comm] using hs_tendsto
    simpa [Function.comp] using (tendsto_add_atTop_iff_nat N).mp hs_tendsto'
  · intro hμ
    -- Upper semicontinuity specialized to the limit set `∅` is exactly continuity at `∅`.
    exact hμ.isContinuousAtEmpty hC.empty_mem

-- Proof sketch: apply `∅`-continuity to the decreasing sequence `A \ s n`, whose intersection is
-- empty, and rewrite `μ (A \ s n)` as `μ A - μ (s n)` using finiteness of `μ A`.
/-- A finite content on a ring of sets that is continuous at the empty set is lower
semicontinuous. -/
theorem addContent_isLowerSemicontinuous_of_finite_isContinuousAtEmpty
    (hC : IsSetRing C) {μ : AddContent ℝ≥0∞ C} (hμfin : AddContent.IsFiniteOnRing μ)
    (hμ : AddContent.IsContinuousAtEmpty μ) :
    AddContent.IsLowerSemicontinuous μ := by
  refine ⟨?_⟩
  intro A hA s hs hs_inc
  let t : ℕ → Set Ω := fun n ↦ A \ s n
  have ht_mem : ∀ n, t n ∈ C := by
    intro n
    exact hC.diff_mem hA (hs n)
  have ht_anti : Antitone t := by
    intro i j hij x hx
    exact ⟨hx.1, fun hxi ↦ hx.2 (hs_inc.mono hij hxi)⟩
  have ht_inter : (⋂ n, t n) = (∅ : Set Ω) := by
    ext x
    constructor
    · intro hx
      have hx0 := mem_iInter.mp hx 0
      rw [mem_diff] at hx0
      have hxA : x ∈ A := hx0.1
      have hx_not_union : x ∉ ⋃ n, s n := by
        intro hx_union
        rcases mem_iUnion.mp hx_union with ⟨n, hn⟩
        have hxn := mem_iInter.mp hx n
        rw [mem_diff] at hxn
        exact hxn.2 hn
      have : x ∈ ⋃ n, s n := by simpa [hs_inc.iUnion_eq] using hxA
      exact hx_not_union this
    · intro hx
      simp at hx
  -- Apply continuity at `∅` to the decreasing complements inside `A`.
  have ht_tendsto : Tendsto (μ ∘ t) atTop (𝓝 0) := by
    exact hμ.tendsto ht_mem ⟨ht_anti, ht_inter⟩ ⟨0, hμfin _ (ht_mem 0)⟩
  have hs_subset : ∀ n, s n ⊆ A := by
    intro n x hx
    have : x ∈ ⋃ i, s i := mem_iUnion.mpr ⟨n, hx⟩
    simpa [hs_inc.iUnion_eq] using this
  have hs_le : ∀ n, μ (s n) ≤ μ A := by
    intro n
    exact MeasureTheory.addContent_mono hC.isSetSemiring (hs n) hA (hs_subset n)
  have h_diff : ∀ n, μ (t n) = μ A - μ (s n) := by
    intro n
    simpa [t] using MeasureTheory.addContent_diff_of_ne_top μ hC
      (fun u hu ↦ ne_of_lt (hμfin u hu)) hA (hs n) (hs_subset n)
  -- The difference identity converts the zero-limit back into continuity from below.
  refine (ENNReal.tendsto_const_sub_nhds_zero_iff (ne_of_lt (hμfin A hA)) hs_le).1 ?_
  refine Tendsto.congr' ?_ ht_tendsto
  exact Filter.Eventually.of_forall h_diff
