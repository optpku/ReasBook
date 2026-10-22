/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_27

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory
open scoped ENNReal BigOperators

universe u

variable {Ω : Type u}

-- Proof sketch: unfold `MeasureTheory.inducedOuterMeasure` as `OuterMeasure.ofFunction` applied to
-- the extension of `μ`, then use `OuterMeasure.ofFunction_eq_iInf_mem` for the predicate
-- `fun s ↦ s ∈ 𝒜` to restrict the infimum to covers by sets in `𝒜`.
/-- Lemma 1.47 (1): The outer measure induced from a nonnegative set function on a class `𝒜` is
given by the infimum of the sums over countable coverings by sets of `𝒜`, so this construction
indeed yields an outer measure. -/
theorem class_inducedOuterMeasure_eq_iInf_coverings
    (𝒜 : Set (Set Ω)) (μ : Subtype (fun s : Set Ω ↦ s ∈ 𝒜) → ℝ≥0∞)
    (h_empty : ∅ ∈ 𝒜) (hμ_empty : μ ⟨∅, h_empty⟩ = 0) (A : Set Ω) :
    inducedOuterMeasure (fun s hs ↦ μ ⟨s, hs⟩) h_empty hμ_empty A =
      ⨅ (cover : ℕ → Set Ω) (hcover : ∀ n, cover n ∈ 𝒜) (_ : A ⊆ ⋃ n, cover n),
        ∑' n, μ ⟨cover n, hcover n⟩ := by
  -- Unfold the induced outer measure to the generic `ofFunction` construction.
  rw [MeasureTheory.inducedOuterMeasure]
  -- Restrict the infimum to covers by members of `𝒜`, since non-members contribute `∞`.
  rw [MeasureTheory.OuterMeasure.ofFunction_eq_iInf_mem
    (m := MeasureTheory.extend (fun s hs ↦ μ ⟨s, hs⟩))
    (m_empty := MeasureTheory.extend_empty h_empty hμ_empty)
    (P := fun s : Set Ω ↦ s ∈ 𝒜)
    (m_top := fun s hs ↦ MeasureTheory.extend_eq_top (m := fun t ht ↦ μ ⟨t, ht⟩) hs)]
  -- On admissible covers, the extension agrees with the original set function.
  refine iInf_congr fun cover ↦ ?_
  refine iInf_congr_Prop Iff.rfl fun hcover ↦ ?_
  refine iInf_congr_Prop Iff.rfl fun _ ↦ ?_
  refine congrArg (fun f : ℕ → ℝ≥0∞ ↦ ∑' n, f n) ?_
  funext n
  rw [MeasureTheory.extend_eq (m := fun s hs ↦ μ ⟨s, hs⟩) (hcover n)]

/-- Helper for Lemma 1.47: a set in the class is a one-piece cover of itself, so the induced outer
measure is bounded above by the original set function. -/
lemma class_inducedOuterMeasure_le_of_mem
    (𝒜 : Set (Set Ω)) (μ : Subtype (fun s : Set Ω ↦ s ∈ 𝒜) → ℝ≥0∞)
    (h_empty : ∅ ∈ 𝒜) (hμ_empty : μ ⟨∅, h_empty⟩ = 0) {A : Set Ω} (hA : A ∈ 𝒜) :
    inducedOuterMeasure (fun s hs ↦ μ ⟨s, hs⟩) h_empty hμ_empty A ≤ μ ⟨A, hA⟩ := by
  -- Use the singleton cover coming from `OuterMeasure.ofFunction_le`.
  simpa [MeasureTheory.inducedOuterMeasure, MeasureTheory.extend_eq (m := fun s hs ↦ μ ⟨s, hs⟩) hA]
    using
      (MeasureTheory.OuterMeasure.ofFunction_le
        (m := MeasureTheory.extend (fun s hs ↦ μ ⟨s, hs⟩))
        (m_empty := MeasureTheory.extend_empty h_empty hμ_empty) A)

/-- Helper for Lemma 1.47: `σ`-subadditivity forces every admissible cover-sum to dominate the
value of the covered set. -/
lemma le_class_inducedOuterMeasure_of_sigmaSubadditive
    (𝒜 : Set (Set Ω)) (μ : Subtype (fun s : Set Ω ↦ s ∈ 𝒜) → ℝ≥0∞)
    (h_empty : ∅ ∈ 𝒜) (hμ_empty : μ ⟨∅, h_empty⟩ = 0)
    (hμσ : IsSigmaSubadditiveSetFunction 𝒜 μ) {A : Set Ω} (hA : A ∈ 𝒜) :
    μ ⟨A, hA⟩ ≤ inducedOuterMeasure (fun s hs ↦ μ ⟨s, hs⟩) h_empty hμ_empty A := by
  -- Rewrite the induced outer measure as the infimum over all admissible countable covers.
  rw [class_inducedOuterMeasure_eq_iInf_coverings 𝒜 μ h_empty hμ_empty A]
  -- It is enough to bound the value of `A` by each candidate cover-sum.
  refine le_iInf fun cover ↦ le_iInf fun hcover ↦ le_iInf fun hAcover ↦ ?_
  -- Apply `σ`-subadditivity to the subtype-valued version of the cover.
  simpa using hμσ.le_tsum ⟨A, hA⟩ (fun n ↦ ⟨cover n, hcover n⟩) hAcover

-- Proof sketch: the singleton cover `{A}` gives the inequality `≤`; for the reverse inequality,
-- use `IsSigmaSubadditiveSetFunction.le_tsum` on every countable cover of `A` by sets in `𝒜` and
-- compare with the infimum formula from `class_inducedOuterMeasure_eq_iInf_coverings`.
/-- Lemma 1.47 (2): If the set function on `𝒜` is `σ`-subadditive, then the induced outer measure
agrees with the original function on every set of `𝒜`. -/
theorem class_inducedOuterMeasure_eq_of_sigmaSubadditive
    (𝒜 : Set (Set Ω)) (μ : Subtype (fun s : Set Ω ↦ s ∈ 𝒜) → ℝ≥0∞)
    (h_empty : ∅ ∈ 𝒜) (hμ_empty : μ ⟨∅, h_empty⟩ = 0)
    (hμσ : IsSigmaSubadditiveSetFunction 𝒜 μ) {A : Set Ω} (hA : A ∈ 𝒜) :
    inducedOuterMeasure (fun s hs ↦ μ ⟨s, hs⟩) h_empty hμ_empty A = μ ⟨A, hA⟩ := by
  -- Compare the induced outer measure with `μ` via the two inequalities from the textbook proof.
  refine le_antisymm ?_ ?_
  · -- The singleton cover `{A}` gives the easy upper bound.
    exact class_inducedOuterMeasure_le_of_mem 𝒜 μ h_empty hμ_empty hA
  · -- Every countable cover of `A` has total weight at least `μ(A)` by `σ`-subadditivity.
    exact le_class_inducedOuterMeasure_of_sigmaSubadditive 𝒜 μ h_empty hμ_empty hμσ hA
