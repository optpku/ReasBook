/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Data.Real.Basic

public section

universe u v

variable {E : Type u} {ι : Type v} [AddCommGroup E] [Module ℝ E]

/-- Exercise 4.18 (1). A globally convex functional satisfies the finite Jensen
inequality. The book's global convexity assumption is expressed by
`ConvexOn ℝ Set.univ J`. -/
theorem jensen_sum_le_of_convexOn_univ (J : E → ℝ) {s : Finset ι} {w : ι → ℝ}
    {p : ι → E} (hJ : ConvexOn ℝ Set.univ J) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : Finset.sum s (fun i ↦ w i) = 1) :
    J (Finset.sum s (fun i ↦ w i • p i)) ≤ Finset.sum s (fun i ↦ w i * J (p i)) := by
  simpa [smul_eq_mul] using
    hJ.map_sum_le hw_nonneg hw_sum (fun _ _ ↦ Set.mem_univ _)

/-- Exercise 4.18 (2). A globally strictly convex functional satisfies a
strict finite Jensen inequality for positive weights whenever the family is
nonconstant. -/
theorem jensen_sum_lt_of_strictConvexOn_univ (J : E → ℝ) {s : Finset ι}
    {w : ι → ℝ} {p : ι → E} (hJ : StrictConvexOn ℝ Set.univ J)
    (hw_pos : ∀ i ∈ s, 0 < w i) (hw_sum : Finset.sum s (fun i ↦ w i) = 1)
    (hnonconst : ∃ j ∈ s, ∃ k ∈ s, p j ≠ p k) :
    J (Finset.sum s (fun i ↦ w i • p i)) < Finset.sum s (fun i ↦ w i * J (p i)) := by
  have hiff :
      J (Finset.sum s (fun i ↦ w i • p i)) < Finset.sum s (fun i ↦ w i * J (p i)) ↔
        ∃ j ∈ s, ∃ k ∈ s, p j ≠ p k := by
    simpa [smul_eq_mul] using
      hJ.map_sum_lt_iff_of_pos hw_pos hw_sum (fun _ _ ↦ Set.mem_univ _)
  exact hiff.2 hnonconst

/-- Companion to Exercise 4.18 (2): under positive weights, the strict Jensen
inequality is equivalent to the family being nonconstant. -/
theorem jensen_sum_lt_iff_of_strictConvexOn_univ (J : E → ℝ) {s : Finset ι}
    {w : ι → ℝ} {p : ι → E} (hJ : StrictConvexOn ℝ Set.univ J)
    (hw_pos : ∀ i ∈ s, 0 < w i) (hw_sum : Finset.sum s (fun i ↦ w i) = 1) :
    J (Finset.sum s (fun i ↦ w i • p i)) < Finset.sum s (fun i ↦ w i * J (p i)) ↔
      ∃ j ∈ s, ∃ k ∈ s, p j ≠ p k := by
  simpa [smul_eq_mul] using
    hJ.map_sum_lt_iff_of_pos hw_pos hw_sum (fun _ _ ↦ Set.mem_univ _)
