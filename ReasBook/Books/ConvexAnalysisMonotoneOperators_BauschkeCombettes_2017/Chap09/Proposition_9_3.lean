/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [SequentialSpace H] [AddCommGroup H] [Module ℝ H]
variable {I : Type v}

/-- Helper for Proposition 9.3: a weighted pointwise supremum is bounded by the corresponding
weighted sum of the separate suprema when the weights are nonnegative. -/
-- Proof sketch: bound each weighted supremum termwise by monotonicity of multiplication, then use
-- `iSup_add_le_add_iSup` to combine the two bounds.
lemma weighted_iSup_le_weighted_iSup {u v : I → EReal} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (⨆ i, (a : EReal) * u i + (b : EReal) * v i) ≤
      (a : EReal) * (⨆ i, u i) + (b : EReal) * (⨆ i, v i) := by
  have haE : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hbE : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  -- Each weighted `iSup` is controlled by the corresponding weighted supremum.
  have hu : (⨆ i, (a : EReal) * u i) ≤ (a : EReal) * (⨆ i, u i) := by
    refine iSup_le fun i ↦ ?_
    exact mul_le_mul_of_nonneg_left (le_iSup u i) haE
  have hv : (⨆ i, (b : EReal) * v i) ≤ (b : EReal) * (⨆ i, v i) := by
    refine iSup_le fun i ↦ ?_
    exact mul_le_mul_of_nonneg_left (le_iSup v i) hbE
  -- The supremum of sums is bounded by the sum of suprema, so the two one-sided bounds combine.
  calc
    (⨆ i, (a : EReal) * u i + (b : EReal) * v i)
        ≤ (⨆ i, (a : EReal) * u i) + ⨆ i, (b : EReal) * v i := EReal.iSup_add_le_add_iSup
    _ ≤ (a : EReal) * (⨆ i, u i) + (b : EReal) * (⨆ i, v i) := add_le_add hu hv

/-- Helper for Proposition 9.3: the pointwise supremum of Jensen-convex extended-real-valued
functions is Jensen-convex. -/
-- Proof sketch: apply the Jensen inequality for each member of the family, take `iSup` over the
-- resulting pointwise bounds, and then estimate the weighted supremum on the right.
lemma isConvex_iSup_of_isConvex (f : I → H → EReal) (hf : ∀ i, IsConvex (f i)) :
    IsConvex (fun x ↦ ⨆ i, f i x) := by
  intro x y a ha0 ha1
  -- Taking the supremum preserves the familywise Jensen bounds.
  have hpointwise :
      (⨆ i, f i (a • x + (1 - a) • y)) ≤
        ⨆ i, (a : EReal) * f i x + (1 - a : EReal) * f i y := by
    refine iSup_le fun i ↦ ?_
    exact (hf i ha0 ha1).trans
      (le_iSup (fun i ↦ (a : EReal) * f i x + (1 - a : EReal) * f i y) i)
  have hone_sub : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  -- The weighted supremum estimate matches the Jensen form required by `IsConvex`.
  calc
    (⨆ i, f i (a • x + (1 - a) • y))
        ≤ ⨆ i, (a : EReal) * f i x + (1 - a : EReal) * f i y := hpointwise
    _ ≤ (a : EReal) * (⨆ i, f i x) + (1 - a : EReal) * (⨆ i, f i y) :=
      weighted_iSup_le_weighted_iSup ha0 hone_sub

/-- Helper for Proposition 9.3: the pointwise supremum of a family in `gamma H` is lower
semicontinuous. -/
-- Proof sketch: extract lower semicontinuity from each `gamma` hypothesis and apply
-- `lowerSemicontinuous_iSup`.
lemma lowerSemicontinuous_iSup_of_mem_gamma (f : I → H → EReal) (hf : ∀ i, f i ∈ gamma H) :
    LowerSemicontinuous (fun x ↦ ⨆ i, f i x) := by
  -- The chapter definition of `gamma` stores lower semicontinuity directly.
  refine lowerSemicontinuous_iSup fun i ↦ ?_
  exact (mem_gamma_iff (f i)).mp (hf i) |>.2

-- Proof sketch: apply `lowerSemicontinuous_iSup` to the family of lower semicontinuous functions.
-- For convexity, combine the convexity part of each `hf i` with the pointwise-supremum argument
-- behind Proposition 8.16. Since the formalized `gamma` predicate records only Jensen convexity
-- and lower semicontinuity, no separate properness hypothesis is needed here.
/-- Proposition 9.3: the pointwise supremum of a family of functions in `Γ(ℋ)` again belongs to
`Γ(ℋ)`. -/
theorem iSup_mem_gamma (f : I → H → EReal)
    (hf : ∀ i, f i ∈ gamma H) :
    (fun x ↦ ⨆ i, f i x) ∈ gamma H := by
  -- The formal `gamma` predicate is exactly Jensen convexity together with lower semicontinuity.
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · -- The textbook convexity proof is the supremum of the familywise Jensen inequalities.
    exact isConvex_iSup_of_isConvex f fun i ↦ (mem_gamma_iff (f i)).mp (hf i) |>.1
  · -- Lower semicontinuity is inherited from the family through `lowerSemicontinuous_iSup`.
    exact lowerSemicontinuous_iSup_of_mem_gamma f hf

end ERealFunction
