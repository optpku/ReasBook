/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9

open scoped BigOperators

-- Domain sampling for this refinement:
-- * primary domain: single-node flow-cover inequalities and their facet faces
-- * core/canonical owner: `flow_cover_excess`, `flow_cover_value`, and `flow_cover_face`
--   on `single_node_flow_set`
-- * source-facing bridge kept here: the explicit excess parameter `lam` satisfying
--   `Finset.sum C a = b + lam`
-- * primitive data: the Chapter 7 single-node flow-set owner and its canonical flow-cover API
-- * derived API removed: local zero-lifted value/face wrappers duplicating those owners
-- * reusable companion kept here: the zero-lifted facet-defining owner for downstream reuse

section Theorem79Part2

variable {n : ℕ}

/-- Under the source equation `∑_{j ∈ C} a_j = b + λ`, the canonical excess owner from
Theorem 7.9 is exactly the textbook excess parameter `λ`. -/
theorem flow_cover_excess_eq_of_sum_eq_add
    (a : Fin n → ℝ) (b lam : ℝ) (C : Finset (Fin n))
    (hcover : C.sum a = b + lam) :
    flow_cover_excess a b C = lam := by
  rw [flow_cover_excess_eq_sum_sub, hcover, add_sub_cancel_left]

/-- Under the source equation `Finset.sum C a = b + lam`, the canonical owner
`flow_cover_value a b C p` is the textbook zero-lifted flow-cover left-hand side
`∑_{j ∈ C} y_j + ∑_{j ∈ C} (a_j - λ)^+ (1 - x_j)`. -/
theorem flow_cover_value_eq_zero_lifted_value
    (a : Fin n → ℝ) (b lam : ℝ) (C : Finset (Fin n))
    (hcover : C.sum a = b + lam)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_value a b C p =
      C.sum (fun j ↦ p.2 j) +
        C.sum (fun j ↦ max (a j - lam) 0 * (1 - p.1 j)) := by
  rw [flow_cover_value_eq, flow_cover_excess_eq_of_sum_eq_add a b lam C hcover]

/-- The zero-lifted flow-cover inequality attached to `C` is facet-defining for the single-node
flow set `T = single_node_flow_set a b` when it is valid on `conv(T)` and the equality face it
cuts out is a facet of `conv(T)`. -/
def flow_cover_inequality_facet_defining
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) : Prop :=
  (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
      p ∈ convexHull ℝ (single_node_flow_set a b) →
        flow_cover_value a b C p ≤ b) ∧
    IsFacetOf
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_face a b C)

/-- `flow_cover_inequality_facet_defining a b C` unfolds to validity on `conv(T)` together with
facetness of the corresponding equality face. -/
theorem flow_cover_inequality_facet_defining_iff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    flow_cover_inequality_facet_defining a b C ↔
      (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
          p ∈ convexHull ℝ (single_node_flow_set a b) →
            flow_cover_value a b C p ≤ b) ∧
        IsFacetOf
          (convexHull ℝ (single_node_flow_set a b))
          (flow_cover_face a b C) :=
  Iff.rfl

/-- A facet-defining zero-lifted flow-cover inequality is valid on `conv(T)`. -/
theorem flow_cover_inequality_valid
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hfacet : flow_cover_inequality_facet_defining a b C)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ convexHull ℝ (single_node_flow_set a b)) :
    flow_cover_value a b C p ≤ b :=
  hfacet.1 hp

/-- A facet-defining zero-lifted flow-cover inequality cuts out a facet of `conv(T)`. -/
theorem flow_cover_inequality_face_isFacet
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hfacet : flow_cover_inequality_facet_defining a b C) :
    IsFacetOf
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_face a b C) :=
  hfacet.2

/-- The source condition `λ < max_{j ∈ C} a_j` is the max-form of the canonical owner theorem
from Theorem 7.9 (2), and therefore already implies that the canonical flow-cover face is a
facet of `conv(T)`. -/
theorem flow_cover_face_isFacet_of_excess_lt_cover_max
    (b : ℝ) (a : Fin n → ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hFlowCover : IsFlowCover a b C)
    (hC : C.Nonempty)
    (hmax : flow_cover_excess a b C < C.sup' hC a) :
    IsFacetOf
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_face a b C) := by
  have hlt :
      flow_cover_excess a b C < C.sup' hC a ↔
        ∃ j ∈ C, flow_cover_excess a b C < a j := by
    exact
      (Finset.lt_sup'_iff hC :
        flow_cover_excess a b C < C.sup' hC a ↔
          ∃ j ∈ C, flow_cover_excess a b C < a j)
  refine single_node_flow_cover_inequality_facet a b C ha_nonneg hFlowCover ?_
  exact hlt.mp hmax

/-- Theorem 7.9. Let `T` be the single-node flow set with capacities `a` and right-hand side `b`.
If the capacities are nonnegative, `C` is a flow cover with excess `λ`, meaning
`∑_{j ∈ C} a_j = b + λ` and `0 < λ`, and `λ < max_{j ∈ C} a_j`, then the flow-cover inequality
`∑_{j ∈ C} y_j + ∑_{j ∈ C} (a_j - λ)^+ (1 - x_j) ≤ b` is facet-defining for `conv(T)`;
equivalently, the coefficients of `x_j` and `y_j` for `j ∉ C` are taken to be `0`. The reusable
public owner is `flow_cover_inequality_facet_defining a b C`, built from the canonical
`flow_cover_value a b C` / `flow_cover_face a b C`; the explicit `λ` presentation is recovered by
`flow_cover_value_eq_zero_lifted_value`. -/
theorem flow_cover_zero_lifting_facet_defining_of_lt_max
    (b : ℝ) (a : Fin n → ℝ) (C : Finset (Fin n)) (lam : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : C.Nonempty)
    (hcover : C.sum a = b + lam)
    (hlam_pos : 0 < lam)
    (hlam_max : lam < C.sup' hC a) :
    flow_cover_inequality_facet_defining a b C := by
  have hFlowCover : IsFlowCover a b C := by
    refine ⟨?_⟩
    calc
      b < b + lam := by linarith
      _ = C.sum a := hcover.symm
  have hExcess : flow_cover_excess a b C = lam :=
    flow_cover_excess_eq_of_sum_eq_add a b lam C hcover
  refine ⟨?_, flow_cover_face_isFacet_of_excess_lt_cover_max b a C ha_nonneg hFlowCover hC ?_⟩
  · intro p hp
    exact flow_cover_value_le_of_mem_convexHull a b C ha_nonneg hFlowCover hp
  · simpa [hExcess] using hlam_max

end Theorem79Part2
