/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_34

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set Filter
open scoped ENNReal Topology

universe u

variable {Ω : Type u} {C : Set (Set Ω)}

namespace AddContent

/-- Definition 1.35 (1): A content on a ring of sets is lower semicontinuous if for every
`A ∈ C` and every increasing sequence of sets in `C` with union `A`, the values `μ (s n)` tend to
`μ A`. -/
class IsLowerSemicontinuous (μ : AddContent ℝ≥0∞ C) : Prop where
  /-- A lower-semicontinuous content is continuous from below along sequences that increase to
  their limit set inside `C`. -/
  tendsto :
    ∀ ⦃A : Set Ω⦄, A ∈ C → ∀ ⦃s : ℕ → Set Ω⦄, (∀ n, s n ∈ C) → Set.IncreasesTo s A →
      Tendsto (μ ∘ s) atTop (𝓝 (μ A))

-- Proof sketch: this is exactly the defining continuity-from-below property.
/-- The lower-semicontinuity predicate gives convergence of `μ (s n)` along any sequence in `C`
that increases to the target set. -/
theorem IsLowerSemicontinuous.tendsto_of_monotone {μ : AddContent ℝ≥0∞ C}
    (hμ : IsLowerSemicontinuous μ) {A : Set Ω} (hA : A ∈ C) {s : ℕ → Set Ω}
    (hs : ∀ n, s n ∈ C) (hmono : Monotone s) (hUnion : (⋃ n, s n) = A) :
    Tendsto (μ ∘ s) atTop (𝓝 (μ A)) :=
  hμ.tendsto hA hs ⟨hmono, hUnion⟩

/-- Definition 1.35 (2): A content on a ring of sets is upper semicontinuous if for every
`A ∈ C` and every decreasing sequence of sets in `C` with `μ (s n) < ∞` for some index and
intersection `A`, the values `μ (s n)` tend to `μ A`. -/
class IsUpperSemicontinuous (μ : AddContent ℝ≥0∞ C) : Prop where
  /-- An upper-semicontinuous content is continuous from above along sequences that decrease to
  their limit set inside `C`, provided some term has finite mass. -/
  tendsto :
    ∀ ⦃A : Set Ω⦄, A ∈ C → ∀ ⦃s : ℕ → Set Ω⦄, (∀ n, s n ∈ C) → Set.DecreasesTo s A →
      (∃ n, μ (s n) < ⊤) → Tendsto (μ ∘ s) atTop (𝓝 (μ A))

-- Proof sketch: this is exactly the defining continuity-from-above property.
/-- The upper-semicontinuity predicate gives convergence of `μ (s n)` along any sequence in `C`
that decreases to the target set and has some finite term. -/
theorem IsUpperSemicontinuous.tendsto_of_antitone {μ : AddContent ℝ≥0∞ C}
    (hμ : IsUpperSemicontinuous μ) {A : Set Ω} (hA : A ∈ C) {s : ℕ → Set Ω}
    (hs : ∀ n, s n ∈ C) (hanti : Antitone s) (hfin : ∃ n, μ (s n) < ⊤)
    (hInter : (⋂ n, s n) = A) :
    Tendsto (μ ∘ s) atTop (𝓝 (μ A)) :=
  hμ.tendsto hA hs ⟨hanti, hInter⟩ hfin

/-- Definition 1.35 (3): A content is `∅`-continuous if the upper-semicontinuity condition holds
for the limit set `∅`. -/
class IsContinuousAtEmpty (μ : AddContent ℝ≥0∞ C) : Prop where
  /-- `∅`-continuity is continuity from above for sequences in `C` that decrease to `∅` and have
  some finite term. -/
  tendsto :
    ∀ ⦃s : ℕ → Set Ω⦄, (∀ n, s n ∈ C) → Set.DecreasesTo s (∅ : Set Ω) →
      (∃ n, μ (s n) < ⊤) → Tendsto (μ ∘ s) atTop (𝓝 0)

-- Proof sketch: specialize the upper-semicontinuity hypothesis to the set `∅`.
/-- An upper-semicontinuous content is continuous at the empty set. -/
theorem IsUpperSemicontinuous.isContinuousAtEmpty {μ : AddContent ℝ≥0∞ C}
    (hμ : IsUpperSemicontinuous μ) (h_empty : (∅ : Set Ω) ∈ C) :
    IsContinuousAtEmpty μ where
  tendsto := by
    intro s hs hdecr hfin
    simpa [addContent_empty] using hμ.tendsto h_empty hs hdecr hfin

-- Proof sketch: this is exactly the defining `∅`-continuity property.
/-- The `∅`-continuity predicate gives convergence of `μ (s n)` for decreasing sequences in `C`
with empty intersection and eventually finite mass. -/
theorem IsContinuousAtEmpty.tendsto_of_antitone {μ : AddContent ℝ≥0∞ C}
    (hμ : IsContinuousAtEmpty μ) {s : ℕ → Set Ω} (hs : ∀ n, s n ∈ C) (hanti : Antitone s)
    (hfin : ∃ n, μ (s n) < ⊤) (hInter : (⋂ n, s n) = (∅ : Set Ω)) :
    Tendsto (μ ∘ s) atTop (𝓝 0) :=
  hμ.tendsto hs ⟨hanti, hInter⟩ hfin

end AddContent
