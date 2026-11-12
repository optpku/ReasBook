/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_example_3_36
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_example_3_29
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19.Cuts
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_theorem_2_3.LinearFunctional
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_4.ch7_sec7_4_theorem_7_18

noncomputable section

open SimpleGraph
open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

-- This file keeps the source-facing subtour-elimination cut objects, but reuses the Chapter 3
-- complete-graph cut owner `cutIncidenceVector`, the Chapter 7 traveling-salesman owner
-- `travelingSalesmanPolytope`, and the Chapter 3 facet owner `IsFacetOf`.

section Theorem719

namespace Theorem719Support

/-- Helper for Theorem 7.19: split the ambient position set into two consecutive blocks. -/
def subtourBlockIndexEquiv {n p : ℕ} (hp : p ≤ n) :
    Fin n ≃ Fin p ⊕ Fin (n - p) :=
  (Fin.castOrderIso (Nat.add_sub_of_le hp)).symm.toEquiv.trans finSumFinEquiv.symm

/-- Helper for Theorem 7.19: the position occupied by a vertex of the first block. -/
def subtourLeftPosition {n p : ℕ} (hp : p ≤ n) (i : Fin p) : Fin n :=
  (subtourBlockIndexEquiv hp).symm (Sum.inl i)

/-- Helper for Theorem 7.19: the position occupied by a vertex of the second block. -/
def subtourRightPosition {n p : ℕ} (hp : p ≤ n) (i : Fin (n - p)) : Fin n :=
  (subtourBlockIndexEquiv hp).symm (Sum.inr i)

/-- Helper for Theorem 7.19: first-block positions keep their natural indices. -/
@[simp] lemma subtourLeftPosition_val {n p : ℕ} (hp : p ≤ n) (i : Fin p) :
    (subtourLeftPosition hp i : ℕ) = i := by
  -- The sum-to-`Fin` equivalence places the left summand before the right one.
  simp [subtourLeftPosition, subtourBlockIndexEquiv]

/-- Helper for Theorem 7.19: second-block positions are offset by the first block size. -/
@[simp] lemma subtourRightPosition_val {n p : ℕ} (hp : p ≤ n)
    (i : Fin (n - p)) :
    (subtourRightPosition hp i : ℕ) = p + i := by
  -- The sum-to-`Fin` equivalence offsets the right summand by `p`.
  simp [subtourRightPosition, subtourBlockIndexEquiv]

/-- Helper for Theorem 7.19: independently permute the two consecutive position blocks. -/
def subtourBlockPositionPerm {n p : ℕ} (hp : p ≤ n)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) : Equiv.Perm (Fin n) :=
  (subtourBlockIndexEquiv hp).trans
    ((Equiv.sumCongr ρ₁ ρ₂).trans (subtourBlockIndexEquiv hp).symm)

/-- Helper for Theorem 7.19: a block tour first permutes within each shore and then applies the
chosen shore enumeration. -/
def subtourBlockTourPerm {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) : Equiv.Perm (Fin n) :=
  (subtourBlockPositionPerm hp ρ₁ ρ₂).trans σ

/-- Helper for Theorem 7.19: the block tour acts by `ρ₁` on first-block positions. -/
@[simp] lemma subtourBlockTourPerm_apply_left
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) (i : Fin p) :
    subtourBlockTourPerm hp σ ρ₁ ρ₂ (subtourLeftPosition hp i) =
      σ (subtourLeftPosition hp (ρ₁ i)) := by
  -- Conjugating the sum permutation by the block chart gives the claimed action.
  simp [subtourBlockTourPerm, subtourBlockPositionPerm, subtourLeftPosition]

/-- Helper for Theorem 7.19: the block tour acts by `ρ₂` on second-block positions. -/
@[simp] lemma subtourBlockTourPerm_apply_right
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) (i : Fin (n - p)) :
    subtourBlockTourPerm hp σ ρ₁ ρ₂ (subtourRightPosition hp i) =
      σ (subtourRightPosition hp (ρ₂ i)) := by
  -- This is the right-summand companion of the preceding computation.
  simp [subtourBlockTourPerm, subtourBlockPositionPerm, subtourRightPosition]

/-- Helper for Theorem 7.19: a block permutation preserves the initial-segment shore
description. -/
lemma subtourBlockTourPerm_mem_iff
    {n p : ℕ} (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) (t : Fin n) :
    subtourBlockTourPerm hp σ ρ₁ ρ₂ t ∈ S ↔ (t : ℕ) < p := by
  -- Split the position through the two-block chart and compute on its summand.
  generalize ht : subtourBlockIndexEquiv hp t = z
  rcases z with i | j
  · have ht' : t = subtourLeftPosition hp i := by
      apply (subtourBlockIndexEquiv hp).injective
      simp [ht, subtourLeftPosition]
    subst t
    rw [subtourBlockTourPerm_apply_left, hσ]
    simp
  · have ht' : t = subtourRightPosition hp j := by
      apply (subtourBlockIndexEquiv hp).injective
      simp [ht, subtourRightPosition]
    subst t
    rw [subtourBlockTourPerm_apply_right, hσ]
    simp

/-- Helper for Theorem 7.19: the first-shore vertex map into ambient coordinates is injective. -/
lemma subtourLeftVertexMap_injective {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun i : Fin p ↦ σ (subtourLeftPosition hp i)) := by
  -- Reflect equality through the ambient permutation and then through the block chart.
  intro i j hij
  have hpos := σ.injective hij
  have hsum := congrArg (subtourBlockIndexEquiv hp) hpos
  simpa [subtourLeftPosition] using hsum

/-- Helper for Theorem 7.19: mapping a first-shore edge into ambient coordinates preserves
non-diagonality. -/
lemma subtourLeftEdge_notDiag {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges p) :
    ¬ (e.1.map (fun i ↦ σ (subtourLeftPosition hp i))).IsDiag := by
  -- Injectivity of the block chart reflects any diagonal ambient edge back to the local edge.
  intro hdiag
  exact e.2 ((Sym2.isDiag_map (subtourLeftVertexMap_injective hp σ)).1 hdiag)

/-- Helper for Theorem 7.19: inject the first shore's complete-graph coordinates into the ambient
edge space. -/
def subtourLeftEdge {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges p) : complete_graph_edges n :=
  ⟨e.1.map (fun i ↦ σ (subtourLeftPosition hp i)), subtourLeftEdge_notDiag hp σ e⟩

/-- Helper for Theorem 7.19: the second-shore vertex map into ambient coordinates is injective. -/
lemma subtourRightVertexMap_injective {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun i : Fin (n - p) ↦ σ (subtourRightPosition hp i)) := by
  -- Reflect equality through the ambient permutation and then through the block chart.
  intro i j hij
  have hpos := σ.injective hij
  have hsum := congrArg (subtourBlockIndexEquiv hp) hpos
  simpa [subtourRightPosition] using hsum

/-- Helper for Theorem 7.19: mapping a second-shore edge into ambient coordinates preserves
non-diagonality. -/
lemma subtourRightEdge_notDiag {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges (n - p)) :
    ¬ (e.1.map (fun i ↦ σ (subtourRightPosition hp i))).IsDiag := by
  -- The right-summand block chart is injective for the same reason as the left chart.
  intro hdiag
  exact e.2 ((Sym2.isDiag_map (subtourRightVertexMap_injective hp σ)).1 hdiag)

/-- Helper for Theorem 7.19: inject the second shore's complete-graph coordinates into the ambient
edge space. -/
def subtourRightEdge {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges (n - p)) : complete_graph_edges n :=
  ⟨e.1.map (fun i ↦ σ (subtourRightPosition hp i)), subtourRightEdge_notDiag hp σ e⟩

/-- Helper for Theorem 7.19: the first-shore edge injection is injective. -/
lemma subtourLeftEdge_injective
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (subtourLeftEdge hp σ) := by
  intro e f hef
  apply Subtype.ext
  -- Injectivity of `Sym2.map` lifts the vertex-map result to undirected edges.
  exact (Sym2.map.injective (subtourLeftVertexMap_injective hp σ))
    (congrArg Subtype.val hef)

/-- Helper for Theorem 7.19: the second-shore edge injection is injective. -/
lemma subtourRightEdge_injective
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (subtourRightEdge hp σ) := by
  intro e f hef
  apply Subtype.ext
  -- Injectivity of `Sym2.map` lifts the vertex-map result to undirected edges.
  exact (Sym2.map.injective (subtourRightVertexMap_injective hp σ))
    (congrArg Subtype.val hef)

/-- Helper for Theorem 7.19: internal restriction preserves addition. -/
lemma subtourInternalRestriction_map_add {n p : ℕ} (hp : p ≤ n)
    (σ : Equiv.Perm (Fin n)) (x y : complete_graph_edges n → ℝ) :
    (fun e ↦ (x + y) (subtourLeftEdge hp σ e),
      fun e ↦ (x + y) (subtourRightEdge hp σ e)) =
      (fun e ↦ x (subtourLeftEdge hp σ e), fun e ↦ x (subtourRightEdge hp σ e)) +
        (fun e ↦ y (subtourLeftEdge hp σ e), fun e ↦ y (subtourRightEdge hp σ e)) := by
  -- Both product coordinates preserve addition pointwise.
  ext e <;> rfl

/-- Helper for Theorem 7.19: internal restriction preserves scalar multiplication. -/
lemma subtourInternalRestriction_map_smul {n p : ℕ} (hp : p ≤ n)
    (σ : Equiv.Perm (Fin n)) (a : ℝ) (x : complete_graph_edges n → ℝ) :
    (fun e ↦ (a • x) (subtourLeftEdge hp σ e),
      fun e ↦ (a • x) (subtourRightEdge hp σ e)) =
      a • (fun e ↦ x (subtourLeftEdge hp σ e),
        fun e ↦ x (subtourRightEdge hp σ e)) := by
  -- Both product coordinates preserve scalar multiplication pointwise.
  ext e <;> rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19/PrefixCheck.lean

Restrict an ambient edge vector to the two internal shore graphs. -/
def subtourInternalRestriction {n p : ℕ} (hp : p ≤ n)
    (σ : Equiv.Perm (Fin n)) :
    (complete_graph_edges n → ℝ) →ₗ[ℝ]
      (complete_graph_edges p → ℝ) × (complete_graph_edges (n - p) → ℝ) where
  toFun x := (fun e ↦ x (subtourLeftEdge hp σ e), fun e ↦ x (subtourRightEdge hp σ e))
  map_add' := subtourInternalRestriction_map_add hp σ
  map_smul' := subtourInternalRestriction_map_smul hp σ

end Theorem719Support
end Theorem719

#print axioms Theorem719Support.subtourInternalRestriction
