/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Algebra.Order.Chebyshev
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_4

open Matrix
open scoped BigOperators

noncomputable section

/- Exercise 10.6 is a `bridge/view` item. The canonical Chapter 10.6 max-cut SDP owners are
`goemans_williamson_feasible`, `goemans_williamson_objective`, and `goemans_williamson_value`
from Exercise 10.4, so this file only specializes that owner surface to the complete graph on
`Fin n` with unit edge weights and keeps the textbook double-sum formula as a companion theorem. -/

section Exercise_10_6

variable (n : ℕ)

/-- The unit edge-weight function on unordered vertex pairs of the complete graph on `Fin n`. -/
def complete_graph_unit_edge_weight : Sym2 (Fin n) → ℝ :=
  fun _ ↦ 1

/-- The complete-graph unit edge weight is constantly `1`. -/
@[simp] theorem complete_graph_unit_edge_weight_apply (e : Sym2 (Fin n)) :
    complete_graph_unit_edge_weight n e = 1 :=
  rfl

/-- Helper for Exercise 10.6: swapping ordered off-diagonal pairs preserves the total sum. -/
lemma sumOffDiagSwap
    (f : Fin n → Fin n → ℝ) :
    Finset.sum Finset.univ.offDiag (fun p ↦ f p.2 p.1) =
      Finset.sum Finset.univ.offDiag (fun p ↦ f p.1 p.2) :=
by
  classical
  -- Reindex the ordered off-diagonal pairs by the swap involution.
  refine Finset.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) ?_ ?_
  · intro p
    simp [Finset.mem_offDiag, ne_comm]
  · intro p hp
    rfl

/-- Helper for Exercise 10.6: a symmetric function on ordered off-diagonal pairs is twice the
sum over the strictly ordered half. -/
lemma sumOffDiag_eq_twiceSumFilterLt
    (f : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, f i j = f j i) :
    Finset.sum Finset.univ.offDiag (fun p ↦ f p.1 p.2) =
      2 * Finset.sum (Finset.univ.offDiag.filter fun p ↦ p.1 < p.2) (fun p ↦ f p.1 p.2) :=
by
  classical
  have hsplit :
      Finset.univ.offDiag =
        (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2) ∪
          (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.2 < p.1) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_offDiag.mp hp with ⟨hp₁, hp₂, hpne⟩
      rw [Finset.mem_union]
      rcases lt_or_gt_of_ne hpne with hlt | hgt
      · left
        simp [Finset.mem_filter, hp₁, hp₂, hpne, hlt]
      · right
        simp [Finset.mem_filter, hp₁, hp₂, hpne, hgt]
    · intro hp
      rw [Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hp).1
  have hdisj :
      Disjoint
        (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
        (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.2 < p.1) := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp₁ hp₂
    simp only [Finset.mem_filter, Finset.mem_offDiag] at hp₁ hp₂
    exact (lt_asymm hp₁.2 hp₂.2)
  have hswapLt :
      Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.2 < p.1)
          (fun p ↦ f p.1 p.2) =
        Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
          (fun p ↦ f p.1 p.2) := by
    -- The `j < i` half matches the `i < j` half after swapping coordinates.
    calc
      Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.2 < p.1)
          (fun p ↦ f p.1 p.2) =
        Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.2 < p.1)
          (fun p ↦ f p.2 p.1) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            symm
            exact hsymm _ _
      _ =
        Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
          (fun p ↦ f p.1 p.2) := by
            refine Finset.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) ?_ ?_
            · intro p
              simp [Finset.mem_filter, Finset.mem_offDiag, ne_comm, and_assoc]
            · intro p hp
              rfl
  -- Partition the ordered off-diagonal sum into its `i < j` and `j < i` halves.
  calc
    Finset.sum Finset.univ.offDiag (fun p ↦ f p.1 p.2) =
      Finset.sum
        ((Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2) ∪
          (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.2 < p.1))
        (fun p ↦ f p.1 p.2) := by
          rw [← hsplit]
    _ =
      Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
          (fun p ↦ f p.1 p.2) +
        Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.2 < p.1)
          (fun p ↦ f p.1 p.2) := by
            rw [Finset.sum_union hdisj]
    _ =
      Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
          (fun p ↦ f p.1 p.2) +
        Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
          (fun p ↦ f p.1 p.2) := by
            rw [hswapLt]
    _ =
      2 * Finset.sum (Finset.univ.offDiag.filter fun p ↦ p.1 < p.2) (fun p ↦ f p.1 p.2) := by
          ring

/-- Helper for Exercise 10.6: the complete-graph edge sum is half the ordered off-diagonal sum
for any symmetric edge term. -/
lemma completeGraphEdgeSum_eq_halfOffDiagSum
    (g : Sym2 (Fin n) → ℝ) :
    Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset g =
      (1 / 2 : ℝ) * Finset.sum Finset.univ.offDiag (fun p ↦ g (Sym2.mk.uncurry p)) :=
by
  classical
  have hEdgeFinset :
      (⊤ : SimpleGraph (Fin n)).edgeFinset =
        (Finset.univ.sym2.filter fun e : Sym2 (Fin n) ↦ ¬ e.IsDiag) := by
    ext e
    simp [SimpleGraph.edgeFinset_top, Finset.sym2_univ]
  have hSymm : ∀ i j : Fin n, g (s(i, j)) = g (s(j, i)) := by
    intro i j
    rw [Sym2.eq_swap]
  have hOrdered :
      Finset.sum Finset.univ.offDiag (fun p ↦ g (Sym2.mk.uncurry p)) =
        2 *
          Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
            (fun p ↦ g (Sym2.mk.uncurry p)) := by
    simpa using
      (sumOffDiag_eq_twiceSumFilterLt (n := n) (f := fun i j ↦ g (s(i, j))) hSymm)
  -- Move from unordered edges to the strictly ordered half of `offDiag`.
  calc
    Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset g =
      Finset.sum (Finset.univ.sym2.filter fun e : Sym2 (Fin n) ↦ ¬ e.IsDiag) g := by
        rw [hEdgeFinset]
    _ =
      Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
        (fun p ↦ g (Sym2.mk.uncurry p)) := by
          simpa [Finset.sum_filter] using
            (Finset.sum_sym2_filter_not_isDiag (s := (Finset.univ : Finset (Fin n))) (p := g))
    _ =
      (1 / 2 : ℝ) * (2 *
        Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
          (fun p ↦ g (Sym2.mk.uncurry p))) := by
            ring
    _ =
      (1 / 2 : ℝ) * Finset.sum Finset.univ.offDiag (fun p ↦ g (Sym2.mk.uncurry p)) := by
        rw [← hOrdered]

/-- Helper for Exercise 10.6: the regular-simplex Gram witness has diagonal `1` and constant
off-diagonal entry `-(n - 1)⁻¹`. -/
def completeGraphSimplexWitness : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if i = j then 1 else -((1 : ℝ) / (n - 1))

/-- Helper for Exercise 10.6: entrywise form of the regular-simplex witness. -/
@[simp] lemma completeGraphSimplexWitness_apply
    (i j : Fin n) :
    completeGraphSimplexWitness n i j = if i = j then 1 else -((1 : ℝ) / (n - 1)) :=
  rfl

/-- Helper for Exercise 10.6: under `2 ≤ n`, the entrywise witness matches the affine projector
formula used for the PSD proof. -/
lemma completeGraphSimplexWitness_eq_affine
    (hn : 2 ≤ n) :
    completeGraphSimplexWitness n =
      ((n : ℝ) / (n - 1)) •
        ((1 : Matrix (Fin n) (Fin n) ℝ) -
          ((1 : ℝ) / n) • Matrix.vecMulVec (fun _ : Fin n ↦ 1) (fun _ : Fin n ↦ 1)) :=
by
  ext i j
  have hnReal : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by
    nlinarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    nlinarith
  -- Compare the diagonal and off-diagonal entries separately.
  by_cases hij : i = j
  · subst hij
    simp [completeGraphSimplexWitness, Matrix.vecMulVec_apply]
    field_simp [hn0.ne', hn1.ne']
  · simp [completeGraphSimplexWitness, Matrix.vecMulVec_apply, hij]
    field_simp [hn0.ne', hn1.ne']

/-- Helper for Exercise 10.6: the regular-simplex witness quadratic form is the centered
sum-of-squares expression. -/
lemma completeGraphSimplexWitness_quadraticForm
    (hn : 2 ≤ n) (x : Fin n → ℝ) :
    x ⬝ᵥ (completeGraphSimplexWitness n *ᵥ x) =
      ((n : ℝ) / (n - 1)) *
        ((∑ i : Fin n, x i ^ 2) - ((1 : ℝ) / n) * (∑ i : Fin n, x i) ^ 2) :=
by
  let ones : Fin n → ℝ := fun _ ↦ 1
  have hScale :
      x ⬝ᵥ ((((n : ℝ) / (n - 1)) •
        ((1 : Matrix (Fin n) (Fin n) ℝ) -
          ((1 : ℝ) / n) • Matrix.vecMulVec ones ones)) *ᵥ x) =
      ((n : ℝ) / (n - 1)) *
        (x ⬝ᵥ
          (((1 : Matrix (Fin n) (Fin n) ℝ) -
            ((1 : ℝ) / n) • Matrix.vecMulVec ones ones) *ᵥ x)) := by
    rw [Matrix.smul_mulVec, dotProduct_smul]
    simp [smul_eq_mul]
  have hOne :
      x ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = ∑ i : Fin n, x i ^ 2 := by
    rw [Matrix.one_mulVec]
    simp [dotProduct]
    ring_nf
  have hn0 : (n : ℝ) ≠ 0 := by
    have hnReal : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
    linarith
  have hProj :
      x ⬝ᵥ ((((1 : ℝ) / n) • Matrix.vecMulVec ones ones) *ᵥ x) =
        ((1 : ℝ) / n) * (∑ i : Fin n, x i) ^ 2 := by
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_smul]
    simp [dotProduct, ones, pow_two, hn0]
    rw [Finset.sum_mul]
  -- Rewrite once through the affine-projector form and then evaluate its quadratic form.
  rw [completeGraphSimplexWitness_eq_affine (n := n) hn]
  calc
    x ⬝ᵥ ((((n : ℝ) / (n - 1)) •
        ((1 : Matrix (Fin n) (Fin n) ℝ) -
          ((1 : ℝ) / n) • Matrix.vecMulVec ones ones)) *ᵥ x) =
      ((n : ℝ) / (n - 1)) *
        (x ⬝ᵥ
          (((1 : Matrix (Fin n) (Fin n) ℝ) -
            ((1 : ℝ) / n) • Matrix.vecMulVec ones ones) *ᵥ x)) := hScale
    _ =
      ((n : ℝ) / (n - 1)) *
        (x ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) -
          x ⬝ᵥ ((((1 : ℝ) / n) • Matrix.vecMulVec ones ones) *ᵥ x)) := by
            rw [Matrix.sub_mulVec, dotProduct_sub]
    _ =
      ((n : ℝ) / (n - 1)) *
        ((∑ i : Fin n, x i ^ 2) -
          x ⬝ᵥ ((((1 : ℝ) / n) • Matrix.vecMulVec ones ones) *ᵥ x)) := by
            rw [hOne]
    _ =
      ((n : ℝ) / (n - 1)) *
        ((∑ i : Fin n, x i ^ 2) - ((1 : ℝ) / n) * (∑ i : Fin n, x i) ^ 2) := by
            rw [hProj]

/-- Helper for Exercise 10.6: every feasible Goemans-Williamson matrix on the complete graph has
nonnegative total entry sum. -/
lemma goemansWilliamsonDoubleSum_nonneg
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : goemans_williamson_feasible X) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, X i j :=
by
  -- Evaluate the PSD quadratic form on the all-ones vector.
  have hOnes :
      0 ≤ (fun _ : Fin n ↦ (1 : ℝ)) ⬝ᵥ (X *ᵥ fun _ : Fin n ↦ (1 : ℝ)) := by
    simpa using
      (goemans_williamson_feasible.posSemidef hX).dotProduct_mulVec_nonneg
        (fun _ : Fin n ↦ (1 : ℝ))
  -- Over `ℝ`, this quadratic form is exactly the total sum of the entries of `X`.
  simpa [dotProduct, Matrix.mulVec] using hOnes

/-- For a matrix on the complete graph with unit edge weights and unit diagonal, the canonical
Goemans-Williamson objective is the textbook quarter-scaled double sum of `1 - X i j`. -/
theorem goemans_williamson_objective_complete_graph_unit_edge_weight_eq
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hDiag : ∀ v : Fin n, X v v = 1) :
    goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) (complete_graph_unit_edge_weight n) X =
      (1 / 4 : ℝ) * ∑ i : Fin n, ∑ j : Fin n, (1 - X i j) :=
by
  classical
  let _ : DecidableRel ((⊤ : SimpleGraph (Fin n)).Adj) := instDecidableRelAdj_integer_2 ⊤
  have hQuarter :
      Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ (1 - X p.1 p.2) / 4) =
        (1 / 4 : ℝ) * Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) := by
    -- Pull the constant factor `1/4` out of the ordered off-diagonal sum.
    calc
      Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ (1 - X p.1 p.2) / 4) =
        Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ (1 / 4 : ℝ) * (1 - X p.1 p.2)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          ring
      _ =
        (1 / 4 : ℝ) * Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) := by
          rw [← Finset.mul_sum]
  have hEdgeTerm :
      Finset.sum Finset.univ.offDiag
          (fun p : Fin n × Fin n ↦ ((2 : ℝ) - X p.1 p.2 - X p.2 p.1) / 4) =
        (1 / 2 : ℝ) * Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) := by
    -- Average the two ordered edge terms and then use the swap involution.
    calc
      Finset.sum Finset.univ.offDiag
          (fun p : Fin n × Fin n ↦ ((2 : ℝ) - X p.1 p.2 - X p.2 p.1) / 4) =
        Finset.sum Finset.univ.offDiag
          (fun p : Fin n × Fin n ↦ (1 - X p.1 p.2) / 4 + (1 - X p.2 p.1) / 4) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            ring
      _ =
        Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ (1 - X p.1 p.2) / 4) +
          Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ (1 - X p.2 p.1) / 4) := by
            rw [Finset.sum_add_distrib]
      _ =
        Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ (1 - X p.1 p.2) / 4) +
          Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ (1 - X p.1 p.2) / 4) := by
            rw [sumOffDiagSwap (n := n) (f := fun i j ↦ (1 - X i j) / 4)]
      _ =
        (1 / 2 : ℝ) * Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) := by
          rw [hQuarter]
          ring
  have hDiagZero :
      Finset.sum Finset.univ.diag (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) = 0 := by
    -- The diagonal contribution vanishes because `X ii = 1`.
    refine Finset.sum_eq_zero ?_
    intro p hp
    rcases p with ⟨i, j⟩
    simp only [Finset.mem_diag] at hp
    rcases hp with ⟨_, hij⟩
    subst hij
    simp [hDiag]
  have hOffToFull :
      Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) =
        ∑ i : Fin n, ∑ j : Fin n, (1 - X i j) := by
    -- Add the zero diagonal back to recover the full double sum.
    calc
      Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) =
        Finset.sum Finset.univ.diag (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) +
          Finset.sum Finset.univ.offDiag (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) := by
            rw [hDiagZero]
            simp
      _ =
        Finset.sum (Finset.univ.diag ∪ Finset.univ.offDiag) (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) := by
            symm
            rw [Finset.sum_union (Finset.disjoint_diag_offDiag (s := (Finset.univ : Finset (Fin n))))]
      _ =
        Finset.sum (Finset.univ ×ˢ Finset.univ) (fun p : Fin n × Fin n ↦ 1 - X p.1 p.2) := by
            rw [Finset.diag_union_offDiag]
      _ = ∑ i : Fin n, ∑ j : Fin n, (1 - X i j) := by
            rw [Finset.sum_product]
  have hLift :
      Finset.sum Finset.univ.offDiag
          (fun p ↦
            Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              (Sym2.mk.uncurry p)) =
        Finset.sum Finset.univ.offDiag
          (fun p : Fin n × Fin n ↦ ((2 : ℝ) - X p.1 p.2 - X p.2 p.1) / 4) := by
    -- Evaluate the lifted symmetric edge term on each ordered pair.
    refine Finset.sum_congr rfl ?_
    intro p hp
    rcases p with ⟨i, j⟩
    simp [Sym2.lift_mk]
  have hEdgeHalf :
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset
          (fun e ↦
            Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              e) =
        (1 / 2 : ℝ) *
          Finset.sum Finset.univ.offDiag
            (fun p ↦
              Sym2.lift
                ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                  intro u v
                  ring⟩
                (Sym2.mk.uncurry p)) := by
    have hEdgeFinset :
        (⊤ : SimpleGraph (Fin n)).edgeFinset =
          (Finset.univ.sym2.filter fun e : Sym2 (Fin n) ↦ ¬ e.IsDiag) := by
      ext e
      simp [SimpleGraph.edgeFinset_top, Finset.sym2_univ]
    have hSymm :
        ∀ i j : Fin n,
          Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              (s(i, j)) =
            Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              (s(j, i)) := by
      intro i j
      rw [Sym2.eq_swap]
    have hOrdered :
        Finset.sum Finset.univ.offDiag
            (fun p ↦
              Sym2.lift
                ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                  intro u v
                  ring⟩
                (Sym2.mk.uncurry p)) =
          2 *
            Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
              (fun p ↦
                Sym2.lift
                  ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                    intro u v
                    ring⟩
                  (Sym2.mk.uncurry p)) := by
      simpa using
        (sumOffDiag_eq_twiceSumFilterLt (n := n)
          (f := fun i j ↦
            Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              (s(i, j)))
          hSymm)
    calc
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset
          (fun e ↦
            Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              e) =
        Finset.sum (Finset.univ.sym2.filter fun e : Sym2 (Fin n) ↦ ¬ e.IsDiag)
          (fun e ↦
            Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              e) := by
            rw [hEdgeFinset]
      _ =
        Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
          (fun p ↦
            Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              (Sym2.mk.uncurry p)) := by
            simpa [Finset.sum_filter] using
              (Finset.sum_sym2_filter_not_isDiag
                (s := (Finset.univ : Finset (Fin n)))
                (p := fun e ↦
                  Sym2.lift
                    ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                      intro u v
                      ring⟩
                    e))
      _ =
        (1 / 2 : ℝ) * (2 *
          Finset.sum (Finset.univ.offDiag.filter fun p : Fin n × Fin n ↦ p.1 < p.2)
            (fun p ↦
              Sym2.lift
                ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                  intro u v
                  ring⟩
                (Sym2.mk.uncurry p))) := by
              ring
      _ =
        (1 / 2 : ℝ) *
          Finset.sum Finset.univ.offDiag
            (fun p ↦
              Sym2.lift
                ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                  intro u v
                  ring⟩
                (Sym2.mk.uncurry p)) := by
            rw [← hOrdered]
  -- Normalize the complete-graph objective to the full double-sum formula.
  rw [goemans_williamson_objective_eq_sum]
  have hWeight :
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset
          (fun e ↦
            complete_graph_unit_edge_weight n e *
              Sym2.lift
                ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                  intro u v
                  ring⟩
                e) =
        Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset
          (fun e ↦
            Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              e) := by
    refine Finset.sum_congr rfl ?_
    intro e he
    simp [complete_graph_unit_edge_weight_apply]
  calc
    Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset
        (fun e ↦
          complete_graph_unit_edge_weight n e *
            Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              e) =
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset
        (fun e ↦
          Sym2.lift
            ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
              intro u v
              ring⟩
            e) := hWeight
    _ =
      (1 / 2 : ℝ) *
        Finset.sum Finset.univ.offDiag
          (fun p ↦
            Sym2.lift
              ⟨fun u v : Fin n ↦ ((2 : ℝ) - X u v - X v u) / 4, by
                intro u v
                ring⟩
              (Sym2.mk.uncurry p)) := hEdgeHalf
    _ =
      (1 / 2 : ℝ) *
        Finset.sum Finset.univ.offDiag
          (fun p : Fin n × Fin n ↦ ((2 : ℝ) - X p.1 p.2 - X p.2 p.1) / 4) := by
            rw [hLift]
    _ = (1 / 4 : ℝ) * ∑ i : Fin n, ∑ j : Fin n, (1 - X i j) := by
          rw [hEdgeTerm, hOffToFull]
          ring

/-- Helper for Exercise 10.6: the regular-simplex witness has `1 - X i j = 0` on the diagonal and
constant off-diagonal gap `n / (n - 1)`. -/
lemma one_sub_completeGraphSimplexWitness_apply
    (hn : 2 ≤ n) (i j : Fin n) :
    1 - completeGraphSimplexWitness n i j =
      if i = j then 0 else (n : ℝ) / (n - 1) :=
by
  have hnReal : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    nlinarith
  -- Separate the diagonal and off-diagonal cases.
  by_cases hij : i = j
  · subst hij
    simp [completeGraphSimplexWitness]
  · simp [completeGraphSimplexWitness, hij, hn1]
    field_simp [hn1.ne']
    ring

/-- Helper for Exercise 10.6: the regular-simplex witness satisfies the canonical feasibility
conditions of the Goemans-Williamson relaxation. -/
lemma completeGraphSimplexWitness_feasible
    (hn : 2 ≤ n) :
    goemans_williamson_feasible (completeGraphSimplexWitness n) :=
by
  have hnReal : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by
    nlinarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    nlinarith
  have hHerm : (completeGraphSimplexWitness n).IsHermitian := by
    -- Over `ℝ`, the witness is Hermitian because its entrywise formula is symmetric.
    refine Matrix.IsHermitian.ext ?_
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [completeGraphSimplexWitness]
    · simp [completeGraphSimplexWitness, hij, eq_comm]
  refine goemans_williamson_feasible.mk ?_ ?_
  · -- The centered quadratic-form formula reduces PSD to Cauchy-Schwarz/Chebyshev.
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm ?_
    intro x
    have hSq :
        (∑ i : Fin n, x i) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, x i ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := x))
    have hScaled :
        ((1 : ℝ) / n) * (∑ i : Fin n, x i) ^ 2 ≤ ∑ i : Fin n, x i ^ 2 := by
      have hMul :
          (∑ i : Fin n, x i) ^ 2 * ((1 : ℝ) / n) ≤
            ((n : ℝ) * ∑ i : Fin n, x i ^ 2) * ((1 : ℝ) / n) := by
        exact mul_le_mul_of_nonneg_right hSq (by positivity)
      calc
        ((1 : ℝ) / n) * (∑ i : Fin n, x i) ^ 2 =
          (∑ i : Fin n, x i) ^ 2 * ((1 : ℝ) / n) := by ring
        _ ≤ ((n : ℝ) * ∑ i : Fin n, x i ^ 2) * ((1 : ℝ) / n) := hMul
        _ = ∑ i : Fin n, x i ^ 2 := by
              field_simp [hn0.ne']
    have hCentered :
        0 ≤ (∑ i : Fin n, x i ^ 2) - ((1 : ℝ) / n) * (∑ i : Fin n, x i) ^ 2 := by
      linarith
    have hQf :
        star x ⬝ᵥ (completeGraphSimplexWitness n *ᵥ x) =
          ((n : ℝ) / (n - 1)) *
            ((∑ i : Fin n, x i ^ 2) - ((1 : ℝ) / n) * (∑ i : Fin n, x i) ^ 2) := by
      simpa using completeGraphSimplexWitness_quadraticForm (n := n) hn x
    rw [hQf]
    have hScale : 0 ≤ ((n : ℝ) / (n - 1)) := le_of_lt (div_pos hn0 hn1)
    nlinarith
  · -- The witness was built with unit diagonal.
    intro i
    simp [completeGraphSimplexWitness]

/-- Helper for Exercise 10.6: evaluating the canonical objective on the regular-simplex witness
gives the complete-graph value `(n / 2)^2`. -/
lemma completeGraphSimplexWitness_objective
    (hn : 2 ≤ n) :
    goemans_williamson_objective (⊤ : SimpleGraph (Fin n))
      (complete_graph_unit_edge_weight n) (completeGraphSimplexWitness n) =
        ((n : ℝ) / 2) ^ 2 :=
by
  classical
  have hDiag :
      ∀ v : Fin n, completeGraphSimplexWitness n v v = 1 := by
    intro v
    simp [completeGraphSimplexWitness]
  have hDiagZero :
      Finset.sum Finset.univ.diag
        (fun p : Fin n × Fin n ↦ 1 - completeGraphSimplexWitness n p.1 p.2) = 0 := by
    -- The diagonal part vanishes because the witness has unit diagonal.
    refine Finset.sum_eq_zero ?_
    intro p hp
    rcases p with ⟨i, j⟩
    simp only [Finset.mem_diag] at hp
    rcases hp with ⟨_, hij⟩
    subst hij
    simp [hDiag]
  have hOffConst :
      Finset.sum Finset.univ.offDiag
          (fun p : Fin n × Fin n ↦ 1 - completeGraphSimplexWitness n p.1 p.2) =
        (((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) * ((n : ℝ) / (n - 1))) := by
    -- Off the diagonal the gap `1 - X i j` is constant.
    calc
      Finset.sum Finset.univ.offDiag
          (fun p : Fin n × Fin n ↦ 1 - completeGraphSimplexWitness n p.1 p.2) =
        Finset.sum Finset.univ.offDiag (fun _ : Fin n × Fin n ↦ (n : ℝ) / (n - 1)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
          simpa [hpne] using
            (one_sub_completeGraphSimplexWitness_apply (n := n) hn p.1 p.2)
      _ = (((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) * ((n : ℝ) / (n - 1))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hFull :
      ∑ i : Fin n, ∑ j : Fin n, (1 - completeGraphSimplexWitness n i j) =
        (((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) * ((n : ℝ) / (n - 1))) := by
    -- Reassemble the full double sum from the zero diagonal and constant off-diagonal part.
    calc
      ∑ i : Fin n, ∑ j : Fin n, (1 - completeGraphSimplexWitness n i j) =
        Finset.sum (Finset.univ ×ˢ Finset.univ)
          (fun p : Fin n × Fin n ↦ 1 - completeGraphSimplexWitness n p.1 p.2) := by
            rw [Finset.sum_product]
      _ =
        Finset.sum (Finset.univ.diag ∪ Finset.univ.offDiag)
          (fun p : Fin n × Fin n ↦ 1 - completeGraphSimplexWitness n p.1 p.2) := by
            rw [Finset.diag_union_offDiag]
      _ =
        Finset.sum Finset.univ.diag
            (fun p : Fin n × Fin n ↦ 1 - completeGraphSimplexWitness n p.1 p.2) +
          Finset.sum Finset.univ.offDiag
            (fun p : Fin n × Fin n ↦ 1 - completeGraphSimplexWitness n p.1 p.2) := by
              rw [Finset.sum_union (Finset.disjoint_diag_offDiag (s := (Finset.univ : Finset (Fin n))))]
      _ = 0 +
          Finset.sum Finset.univ.offDiag
            (fun p : Fin n × Fin n ↦ 1 - completeGraphSimplexWitness n p.1 p.2) := by
              rw [hDiagZero]
      _ = (((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) * ((n : ℝ) / (n - 1))) := by
            rw [hOffConst]
            simp
  have hnReal : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    nlinarith
  have hCardNat : (Finset.univ : Finset (Fin n)).offDiag.card = n * (n - 1) := by
    rw [Finset.offDiag_card]
    simp
    calc
      n * n - n = n * n - n * 1 := by rw [Nat.mul_one]
      _ = n * (n - 1) := by rw [← Nat.mul_sub_left_distrib]
  have hCard :
      (((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) =
        (n : ℝ) * (((n - 1 : ℕ) : ℝ))) := by
    exact_mod_cast hCardNat
  have hSub : (((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1) := by
    have hSubNat : n - 1 + 1 = n := by
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hn))
    have hSubAdd : (((n - 1 : ℕ) : ℝ)) + 1 = n := by
      exact_mod_cast hSubNat
    nlinarith
  -- Evaluate the objective on the explicit regular-simplex witness.
  rw [goemans_williamson_objective_complete_graph_unit_edge_weight_eq (n := n) hDiag, hFull, hCard, hSub]
  field_simp [hn1.ne']
  ring

/-- Exercise 10.6. For the complete graph on `n` nodes with all edge weights equal to `1`, the
optimal value `z_sdp` of the standard semidefinite max-cut relaxation is `(n / 2)^2`, expressed
here through the canonical Goemans-Williamson owner. -/
theorem complete_graph_unit_weight_z_sdp_eq
    (hn : 2 ≤ n) :
    goemans_williamson_value (⊤ : SimpleGraph (Fin n)) (complete_graph_unit_edge_weight n) =
      ((n : ℝ) / 2) ^ 2 :=
by
  classical
  have hBdd :
      BddAbove
        (goemans_williamson_objective_values
          (⊤ : SimpleGraph (Fin n)) (complete_graph_unit_edge_weight n)) :=
    goemansWilliamsonObjectiveValues_bddAbove
      (G := (⊤ : SimpleGraph (Fin n))) (w := complete_graph_unit_edge_weight n)
  have hNonempty :
      (goemans_williamson_objective_values
        (⊤ : SimpleGraph (Fin n)) (complete_graph_unit_edge_weight n)).Nonempty := by
    refine ⟨((n : ℝ) / 2) ^ 2, ?_⟩
    exact ⟨completeGraphSimplexWitness n, completeGraphSimplexWitness_feasible (n := n) hn,
      completeGraphSimplexWitness_objective (n := n) hn⟩
  rw [goemans_williamson_value_eq_sSup]
  refine le_antisymm ?_ ?_
  · -- Any feasible matrix is bounded above by the complete-graph SDP value `(n / 2)^2`.
    refine csSup_le hNonempty ?_
    intro r hr
    rcases hr with ⟨X, hX, rfl⟩
    rw [goemans_williamson_objective_complete_graph_unit_edge_weight_eq
      (n := n) (hDiag := goemans_williamson_feasible.diag_eq_one hX)]
    have hExpand :
        ∑ i : Fin n, ∑ j : Fin n, (1 - X i j) =
          (n : ℝ) ^ 2 - ∑ i : Fin n, ∑ j : Fin n, X i j := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, (1 - X i j) =
          ∑ i : Fin n, ((∑ j : Fin n, (1 : ℝ)) - ∑ j : Fin n, X i j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.sum_sub_distrib]
        _ = ∑ i : Fin n, ((n : ℝ) - ∑ j : Fin n, X i j) := by
              simp
        _ = (n : ℝ) * n - ∑ i : Fin n, ∑ j : Fin n, X i j := by
              rw [Finset.sum_sub_distrib]
              simp [Finset.sum_const, nsmul_eq_mul]
        _ = (n : ℝ) ^ 2 - ∑ i : Fin n, ∑ j : Fin n, X i j := by
              ring
    rw [hExpand]
    nlinarith [goemansWilliamsonDoubleSum_nonneg (n := n) hX]
  · -- The regular-simplex witness attains the claimed value, so the supremum is at least that.
    refine le_csSup hBdd ?_
    exact ⟨completeGraphSimplexWitness n, completeGraphSimplexWitness_feasible (n := n) hn,
      completeGraphSimplexWitness_objective (n := n) hn⟩

end Exercise_10_6

end
