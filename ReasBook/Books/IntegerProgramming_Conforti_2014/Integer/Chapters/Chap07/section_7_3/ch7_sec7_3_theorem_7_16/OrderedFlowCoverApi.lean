/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_13.OrderedCover

open scoped BigOperators

section Theorem716OrderedFlowCoverApi

variable {n : ℕ}

/-
Theorem 7.16-specific lifted flow-cover API built on the ordered-cover primitives from
Lemma 7.13.
-/
namespace OrderedFlowCover

/-- `admissiblePair a b C coverOrder r i αᵢ βᵢ` records the four source coefficient patterns from
Theorem 7.16 for a noncover index `i`, using the ordered cover coefficients `a_{j_h}` and their
partial sums `μ_h` derived from `coverOrder`. -/
def admissiblePair
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n) (r : ℕ)
    (i : Fin n) (αᵢ βᵢ : ℝ) : Prop :=
  let lam := flow_cover_excess a b C
  let coverWeight := weight C a coverOrder
  let μ := partialSum C a coverOrder
  (αᵢ = 0 ∧ βᵢ = 0) ∨
    (∃ h : ℕ,
      2 ≤ h ∧
        h ≤ r ∧
          μ h - lam ≤ a i ∧
            αᵢ = lam / coverWeight h ∧
              βᵢ =
                lam * (((h - 1 : ℕ) : ℝ) - (μ h - lam) / coverWeight h)) ∨
      (∃ ℓ : ℕ,
        a i > μ ℓ - lam ∧
          (ℓ = r ∨ (ℓ < r ∧ a i ≤ μ ℓ)) ∧
            αᵢ = 1 ∧
              βᵢ = (ℓ : ℝ) * lam - μ ℓ) ∨
        ∃ ℓ : ℕ,
          1 ≤ ℓ ∧
            ℓ < r ∧
            μ ℓ < a i ∧
              a i ≤ μ (ℓ + 1) - lam ∧
                αᵢ = lam / (a i + lam - μ ℓ) ∧
                  βᵢ =
                    (ℓ : ℝ) * lam - (lam * a i) / (a i + lam - μ ℓ)

/-- The left-hand side of the lifted flow-cover inequality `(7.16)`, written as the canonical
zero-lifted flow-cover owner `flow_cover_value a b C` on `C` together with the lifting
coefficients `(α_i, β_i)` on `N \ C`. -/
def flow_cover_lifted_value
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  flow_cover_value a b C p +
    Finset.sum (Finset.univ \ C) (fun i ↦ α i * p.2 i + β i * p.1 i)

/-- `flow_cover_lifted_value a b C α β p` expands to the zero-lifted cover value on `C` plus the
lifting contribution on `Finset.univ \ C`. -/
theorem flow_cover_lifted_value_eq
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_lifted_value a b C α β p =
      flow_cover_value a b C p +
        Finset.sum (Finset.univ \ C) (fun i ↦ α i * p.2 i + β i * p.1 i) :=
  rfl

/-- With zero lifting coefficients on `N \ C`, the lifted owner reduces to the canonical
zero-lifted flow-cover owner from Theorem 7.9. -/
theorem flow_cover_lifted_value_zero
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_lifted_value a b C (fun _ ↦ 0) (fun _ ↦ 0) p = flow_cover_value a b C p := by
  simp [flow_cover_lifted_value]

/-- The equality face cut out on `conv(T)` by a lifted flow-cover inequality over the single-node
flow set `T = single_node_flow_set a b` with right-hand side `δ`. -/
def flow_cover_lifted_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ) (δ : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
    p ∈ convexHull ℝ (single_node_flow_set a b) ∧
      flow_cover_lifted_value a b C α β p = δ}

/-- Membership in `flow_cover_lifted_face a b C α β δ` means lying in `conv(T)` and meeting the
lifted flow-cover inequality at equality. -/
theorem mem_flow_cover_lifted_face_iff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ) (δ : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ flow_cover_lifted_face a b C α β δ ↔
      p ∈ convexHull ℝ (single_node_flow_set a b) ∧
        flow_cover_lifted_value a b C α β p = δ :=
  Iff.rfl

/-- The lifted flow-cover inequality `(7.16)` is facet-defining for the single-node flow set
`T = single_node_flow_set a b` when it is valid on `conv(T)` with right-hand side `δ` and the
equality face it cuts out is a facet of `conv(T)`. -/
def flow_cover_lifted_inequality_facet_defining
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ) (δ : ℝ) : Prop :=
  (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
      p ∈ convexHull ℝ (single_node_flow_set a b) →
        flow_cover_lifted_value a b C α β p ≤ δ) ∧
    IsFacetOf
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_lifted_face a b C α β δ)

/-- `flow_cover_lifted_inequality_facet_defining a b C α β δ` unfolds to validity on `conv(T)`
together with facetness of the corresponding equality face. -/
theorem flow_cover_lifted_inequality_facet_defining_iff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ) (δ : ℝ) :
    flow_cover_lifted_inequality_facet_defining a b C α β δ ↔
      (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
          p ∈ convexHull ℝ (single_node_flow_set a b) →
            flow_cover_lifted_value a b C α β p ≤ δ) ∧
        IsFacetOf
          (convexHull ℝ (single_node_flow_set a b))
          (flow_cover_lifted_face a b C α β δ) :=
  Iff.rfl

end OrderedFlowCover

end Theorem716OrderedFlowCoverApi
