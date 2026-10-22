/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [TopologicalSpace E]

-- Proof sketch: the textbook monotone finite-measure exhaustion is stronger than needed here; the
-- actual almost-everywhere equivalence is exactly the canonical restricted-measure `iUnion`
-- statement.
/-- Remark 6.3: if a countable family of sets `A n` covers `univ`, then `f n` converges to `g`
almost everywhere with respect to `μ` if and only if this convergence holds almost everywhere with
respect to each restricted measure `μ.restrict (A n)`. -/
theorem ae_tendsto_iff_forall_ae_restrict_of_iUnion_eq_univ
    (μ : Measure Ω) (A : ℕ → Set Ω) {f : ℕ → Ω → E} {g : Ω → E}
    (hA_union : (⋃ n, A n) = univ) :
    (∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) ↔
      ∀ n, ∀ᵐ x ∂μ.restrict (A n), Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  let P : Ω → Prop := fun x ↦ Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))
  simpa [P, hA_union] using ae_restrict_iUnion_iff A P
