/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

-- Semantic recall hits verified for this item:
-- `ConvexOn.smul`, `ConvexOn.add`, `convexOn_const`.

section Theorem1311

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-
Chapter01 Theorem 1.3.11 (1) and (2): if `f` is convex on `S ⊆ ℝ^n` and `α ≥ 0`, then `α • f`
is convex on `S`; if `f` and `g` are convex on `S`, then `f + g` is convex on `S`.

These are direct `Point = EuclideanSpace ℝ (Fin n)` specializations of mathlib's exact owner
theorems `ConvexOn.smul` and `ConvexOn.add`, so this file records them as recall entries instead
of keeping parallel local wrappers.
-/
#check fun {S : Set Point} {f : Point → ℝ} {α : ℝ} (hf : ConvexOn ℝ S f) (hα : 0 ≤ α) ↦
  (hf.smul hα : ConvexOn ℝ S (α • f))
#check fun {S : Set Point} {f g : Point → ℝ} (hf : ConvexOn ℝ S f) (hg : ConvexOn ℝ S g) ↦
  (hf.add hg : ConvexOn ℝ S (f + g))

variable {𝕜 E β ι : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

/-- Chapter01 Theorem 1.3.11 (3), core/canonical layer: a finite nonnegative linear combination
of convex functions is convex on a convex set. The source statement on `S ⊆ ℝ^n` is the
specialization `𝕜 = ℝ`, `E = EuclideanSpace ℝ (Fin n)`, `β = ℝ`. The source sum `∑ αᵢ fᵢ` is
formalized as the `Finset`-indexed function sum `∑ i in t, α i • f i`. -/
theorem convexOn_nonneg_finset_sum (t : Finset ι) (S : Set E) (f : ι → E → β) (α : ι → 𝕜)
    (hS : Convex 𝕜 S) (hf : ∀ i ∈ t, ConvexOn 𝕜 S (f i)) (hα : ∀ i ∈ t, 0 ≤ α i) :
    ConvexOn 𝕜 S (∑ i ∈ t, α i • f i) := by
  classical
  have hsum :
      ∀ u : Finset ι, (∀ j ∈ u, ConvexOn 𝕜 S (f j)) → (∀ j ∈ u, 0 ≤ α j) →
        ConvexOn 𝕜 S (∑ j ∈ u, α j • f j) := by
    intro u hu hαu
    induction u using Finset.cons_induction_on with
    | empty =>
        change ConvexOn 𝕜 S (fun _ : E ↦ (0 : β))
        exact convexOn_const (0 : β) hS
    | cons j u hj ihu =>
        rw [Finset.forall_mem_cons] at hu hαu
        rw [Finset.sum_cons]
        exact (hu.1).smul hαu.1 |>.add (ihu hu.2 hαu.2)
  exact hsum t hf hα

end Theorem1311
