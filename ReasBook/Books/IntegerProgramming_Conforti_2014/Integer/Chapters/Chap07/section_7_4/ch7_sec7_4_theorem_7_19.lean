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

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: split the ambient position set into two consecutive blocks. -/
def subtourBlockIndexEquiv {n p : ℕ} (hp : p ≤ n) :
    Fin n ≃ Fin p ⊕ Fin (n - p) :=
  (Fin.castOrderIso (Nat.add_sub_of_le hp)).symm.toEquiv.trans finSumFinEquiv.symm

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the position occupied by a vertex of the first block. -/
def subtourLeftPosition {n p : ℕ} (hp : p ≤ n) (i : Fin p) : Fin n :=
  (subtourBlockIndexEquiv hp).symm (Sum.inl i)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the position occupied by a vertex of the second block. -/
def subtourRightPosition {n p : ℕ} (hp : p ≤ n) (i : Fin (n - p)) : Fin n :=
  (subtourBlockIndexEquiv hp).symm (Sum.inr i)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: first-block positions keep their natural indices. -/
@[simp] lemma subtourLeftPosition_val {n p : ℕ} (hp : p ≤ n) (i : Fin p) :
    (subtourLeftPosition hp i : ℕ) = i := by
  -- The sum-to-`Fin` equivalence places the left summand before the right one.
  simp [subtourLeftPosition, subtourBlockIndexEquiv]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: second-block positions are offset by the first block size. -/
@[simp] lemma subtourRightPosition_val {n p : ℕ} (hp : p ≤ n)
    (i : Fin (n - p)) :
    (subtourRightPosition hp i : ℕ) = p + i := by
  -- The sum-to-`Fin` equivalence offsets the right summand by `p`.
  simp [subtourRightPosition, subtourBlockIndexEquiv]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: independently permute the two consecutive position blocks. -/
def subtourBlockPositionPerm {n p : ℕ} (hp : p ≤ n)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) : Equiv.Perm (Fin n) :=
  (subtourBlockIndexEquiv hp).trans
    ((Equiv.sumCongr ρ₁ ρ₂).trans (subtourBlockIndexEquiv hp).symm)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: a block tour first permutes within each shore and then applies the
chosen shore enumeration. -/
def subtourBlockTourPerm {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) : Equiv.Perm (Fin n) :=
  (subtourBlockPositionPerm hp ρ₁ ρ₂).trans σ

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the block tour acts by `ρ₁` on first-block positions. -/
@[simp] lemma subtourBlockTourPerm_apply_left
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) (i : Fin p) :
    subtourBlockTourPerm hp σ ρ₁ ρ₂ (subtourLeftPosition hp i) =
      σ (subtourLeftPosition hp (ρ₁ i)) := by
  -- Conjugating the sum permutation by the block chart gives the claimed action.
  simp [subtourBlockTourPerm, subtourBlockPositionPerm, subtourLeftPosition]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the block tour acts by `ρ₂` on second-block positions. -/
@[simp] lemma subtourBlockTourPerm_apply_right
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) (i : Fin (n - p)) :
    subtourBlockTourPerm hp σ ρ₁ ρ₂ (subtourRightPosition hp i) =
      σ (subtourRightPosition hp (ρ₂ i)) := by
  -- This is the right-summand companion of the preceding computation.
  simp [subtourBlockTourPerm, subtourBlockPositionPerm, subtourRightPosition]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: a block permutation preserves the initial-segment shore
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

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: mapping a first-shore edge into ambient coordinates preserves non-diagonality. -/
lemma subtourLeftEdge_notDiag {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges p) :
    ¬ (e.1.map (fun i ↦ σ (subtourLeftPosition hp i))).IsDiag := by
  -- Injectivity of the block chart reflects any diagonal ambient edge back to the local edge.
  have hinj : Function.Injective (fun i : Fin p ↦ σ (subtourLeftPosition hp i)) := by
    intro i j hij
    have hpos := σ.injective hij
    have hsum := congrArg (subtourBlockIndexEquiv hp) hpos
    simpa [subtourLeftPosition] using hsum
  intro hdiag
  exact e.2 ((Sym2.isDiag_map hinj).1 hdiag)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: inject the first shore's complete-graph coordinates into the ambient edge space. -/
def subtourLeftEdge {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges p) : complete_graph_edges n :=
  ⟨e.1.map (fun i ↦ σ (subtourLeftPosition hp i)), subtourLeftEdge_notDiag hp σ e⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: mapping a second-shore edge into ambient coordinates preserves non-diagonality. -/
lemma subtourRightEdge_notDiag {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges (n - p)) :
    ¬ (e.1.map (fun i ↦ σ (subtourRightPosition hp i))).IsDiag := by
  -- The right-summand block chart is injective for the same reason as the left chart.
  have hinj : Function.Injective
      (fun i : Fin (n - p) ↦ σ (subtourRightPosition hp i)) := by
    intro i j hij
    have hpos := σ.injective hij
    have hsum := congrArg (subtourBlockIndexEquiv hp) hpos
    simpa [subtourRightPosition] using hsum
  intro hdiag
  exact e.2 ((Sym2.isDiag_map hinj).1 hdiag)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: inject the second shore's complete-graph coordinates into the ambient
edge space. -/
def subtourRightEdge {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges (n - p)) : complete_graph_edges n :=
  ⟨e.1.map (fun i ↦ σ (subtourRightPosition hp i)), subtourRightEdge_notDiag hp σ e⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the first-shore edge injection is injective. -/
lemma subtourLeftEdge_injective
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (subtourLeftEdge hp σ) := by
  intro e f hef
  apply Subtype.ext
  have hinj : Function.Injective (fun i : Fin p ↦ σ (subtourLeftPosition hp i)) := by
    intro i j hij
    have hpos := σ.injective hij
    have hsum := congrArg (subtourBlockIndexEquiv hp) hpos
    simpa [subtourLeftPosition] using hsum
  exact (Sym2.map.injective hinj) (congrArg Subtype.val hef)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the second-shore edge injection is injective. -/
lemma subtourRightEdge_injective
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (subtourRightEdge hp σ) := by
  intro e f hef
  apply Subtype.ext
  have hinj : Function.Injective
      (fun i : Fin (n - p) ↦ σ (subtourRightPosition hp i)) := by
    intro i j hij
    have hpos := σ.injective hij
    have hsum := congrArg (subtourBlockIndexEquiv hp) hpos
    simpa [subtourRightPosition] using hsum
  exact (Sym2.map.injective hinj) (congrArg Subtype.val hef)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: internal restriction preserves addition. -/
lemma subtourInternalRestriction_map_add {n p : ℕ} (hp : p ≤ n)
    (σ : Equiv.Perm (Fin n)) (x y : complete_graph_edges n → ℝ) :
    (fun e ↦ (x + y) (subtourLeftEdge hp σ e),
      fun e ↦ (x + y) (subtourRightEdge hp σ e)) =
      (fun e ↦ x (subtourLeftEdge hp σ e), fun e ↦ x (subtourRightEdge hp σ e)) +
        (fun e ↦ y (subtourLeftEdge hp σ e), fun e ↦ y (subtourRightEdge hp σ e)) := by
  -- Both product coordinates preserve addition pointwise.
  ext e <;> rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: internal restriction preserves scalar multiplication. -/
lemma subtourInternalRestriction_map_smul {n p : ℕ} (hp : p ≤ n)
    (σ : Equiv.Perm (Fin n)) (a : ℝ) (x : complete_graph_edges n → ℝ) :
    (fun e ↦ (a • x) (subtourLeftEdge hp σ e),
      fun e ↦ (a • x) (subtourRightEdge hp σ e)) =
      a • (fun e ↦ x (subtourLeftEdge hp σ e),
        fun e ↦ x (subtourRightEdge hp σ e)) := by
  -- Both product coordinates preserve scalar multiplication pointwise.
  ext e <;> rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: restrict an ambient edge vector to the two internal shore graphs. -/
def subtourInternalRestriction {n p : ℕ} (hp : p ≤ n)
    (σ : Equiv.Perm (Fin n)) :
    (complete_graph_edges n → ℝ) →ₗ[ℝ]
      (complete_graph_edges p → ℝ) × (complete_graph_edges (n - p) → ℝ) where
  toFun x := (fun e ↦ x (subtourLeftEdge hp σ e), fun e ↦ x (subtourRightEdge hp σ e))
  map_add' := subtourInternalRestriction_map_add hp σ
  map_smul' := subtourInternalRestriction_map_smul hp σ

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the two projections of an
element of a product submodule lie in their respective factors. -/
lemma submoduleProd_fst_mem
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) (x : ↥(P.prod Q)) : x.1.1 ∈ P := by
  -- Product-submodule membership records membership of each coordinate.
  exact (Submodule.mem_prod.mp x.2).1

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the second projection of a
product-submodule element lies in the second factor. -/
lemma submoduleProd_snd_mem
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) (x : ↥(P.prod Q)) : x.1.2 ∈ Q := by
  -- Product-submodule membership records membership of each coordinate.
  exact (Submodule.mem_prod.mp x.2).2

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: pairing elements of two
submodules gives an element of their product submodule. -/
lemma submoduleProd_pair_mem
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) (x : P × Q) :
    ((x.1 : M), (x.2 : N)) ∈ P.prod Q := by
  -- Both coordinates carry precisely the membership certificates required by `Submodule.prod`.
  exact Submodule.mem_prod.mpr ⟨x.1.2, x.2.2⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the subtype of a product
submodule maps linearly to the product of the two subtypes. -/
def submoduleProdToProd
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) : ↥(P.prod Q) →ₗ[𝕜] P × Q :=
  (LinearMap.codRestrict P
      ((LinearMap.fst 𝕜 M N).comp (P.prod Q).subtype)
      (submoduleProd_fst_mem P Q)).prod
    (LinearMap.codRestrict Q
      ((LinearMap.snd 𝕜 M N).comp (P.prod Q).subtype)
      (submoduleProd_snd_mem P Q))

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the canonical linear map from
a product submodule to the product of its factors is bijective. -/
lemma submoduleProdToProd_bijective
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) :
    Function.Bijective (submoduleProdToProd P Q) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : P × Q ↦ ((z.1 : M), (z.2 : N))) hxy
  · intro y
    let x : ↥(P.prod Q) :=
      ⟨((y.1 : M), (y.2 : N)), submoduleProd_pair_mem P Q y⟩
    refine ⟨x, ?_⟩
    -- The two coordinate projections recover the original subtype elements.
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the finrank of a product
submodule is the sum of the finranks of its factors. -/
lemma finrank_submoduleProd
    {𝕜 M N : Type*} [Field 𝕜] [AddCommGroup M] [AddCommGroup N]
    [Module 𝕜 M] [Module 𝕜 N] [Module.Finite 𝕜 M] [Module.Finite 𝕜 N]
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) :
    Module.finrank 𝕜 ↥(P.prod Q) = Module.finrank 𝕜 P + Module.finrank 𝕜 Q := by
  let e := LinearEquiv.ofBijective (submoduleProdToProd P Q)
    (submoduleProdToProd_bijective P Q)
  -- Transport finrank across the canonical equivalence, then use the ambient product formula.
  calc
    Module.finrank 𝕜 ↥(P.prod Q) = Module.finrank 𝕜 (P × Q) := e.finrank_eq
    _ = Module.finrank 𝕜 P + Module.finrank 𝕜 Q := Module.finrank_prod

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: positions from opposite blocks determine a non-diagonal ambient
edge. -/
lemma subtourCrossEdge_notDiag
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (i : Fin p) (j : Fin (n - p)) :
    ¬ (s(σ (subtourLeftPosition hp i), σ (subtourRightPosition hp j)) :
        Sym2 (Fin n)).IsDiag := by
  -- Equality of the endpoints would identify the two distinct summands of the block chart.
  rw [Sym2.mk_isDiag_iff]
  intro hij
  have hpos := σ.injective hij
  have hchart := congrArg (subtourBlockIndexEquiv hp) hpos
  simp [subtourLeftPosition, subtourRightPosition] at hchart

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the ambient edge joining one position from each shore block. -/
def subtourCrossEdge
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n))
    (i : Fin p) (j : Fin (n - p)) : complete_graph_edges n :=
  ⟨s(σ (subtourLeftPosition hp i), σ (subtourRightPosition hp j)),
    subtourCrossEdge_notDiag hp σ i j⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the two local endpoints uniquely determine an ambient cross edge. -/
lemma subtourCrossEdge_injective
    {n p : ℕ} (hp : p ≤ n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective
      (fun z : Fin p × Fin (n - p) ↦ subtourCrossEdge hp σ z.1 z.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hedge
  have hsym := congrArg Subtype.val hedge
  simp only [subtourCrossEdge] at hsym
  rw [Sym2.eq_iff] at hsym
  rcases hsym with hdirect | hswap
  · apply Prod.ext
    · apply Fin.ext
      have hpos := σ.injective hdirect.1
      simpa using congrArg Fin.val hpos
    · apply Fin.ext
      have hpos := σ.injective hdirect.2
      have hval := congrArg Fin.val hpos
      simp at hval
      omega
  · have hpos := σ.injective hswap.1
    have hval := congrArg Fin.val hpos
    simp at hval
    omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: a path index is also a valid left endpoint position in the tour. -/
private lemma pathEdgeLeftPosition_lt
    {n : ℕ} (k : Fin (n - 1)) : k.1 < n := by
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the successor of a path index is a valid right endpoint position. -/
private lemma pathEdgeRightPosition_lt
    {n : ℕ} (k : Fin (n - 1)) : k.1 + 1 < n := by
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the left tour position of a path edge. -/
private def pathEdgeLeftPosition
    {n : ℕ} (k : Fin (n - 1)) : Fin n :=
  ⟨k.1, pathEdgeLeftPosition_lt k⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the right tour position of a path edge. -/
private def pathEdgeRightPosition
    {n : ℕ} (k : Fin (n - 1)) : Fin n :=
  ⟨k.1 + 1, pathEdgeRightPosition_lt k⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the endpoints of a path edge are its two consecutive tour positions. -/
private lemma mem_pathEdgeOfIndex_iff
    {n : ℕ} (v : Fin n) (σ : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    v ∈ ((path_edge_of_index σ k : complete_graph_edges n) : Sym2 (Fin n)) ↔
      v = σ (pathEdgeLeftPosition k) ∨ v = σ (pathEdgeRightPosition k) := by
  -- Expose the two consecutive positions while keeping their bound proofs behind named helpers.
  change
    v ∈ (s(σ (pathEdgeLeftPosition k), σ (pathEdgeRightPosition k)) : Sym2 (Fin n)) ↔
      v = σ (pathEdgeLeftPosition k) ∨ v = σ (pathEdgeRightPosition k)
  simp [Sym2.mem_iff]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: a consecutive edge crosses an initial block exactly at its boundary. -/
private lemma cutIncidenceVector_pathEdgeOfIndex_of_initialSegment
    {n : ℕ} (S : Finset (Fin n)) (p : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (k : Fin (n - 1)) :
    cutIncidenceVector S (path_edge_of_index σ k) =
      if ((k : ℕ) < p) = ((k : ℕ) + 1 < p) then 0 else 1 := by
  -- Rewrite both endpoint memberships using the initial-segment description.
  unfold path_edge_of_index
  rw [cutIncidenceVector_apply_pair]
  simp only [hσ]
  rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: every edge between the two blocks has cut value one. -/
private lemma subtourCrossEdge_cutValue
    {n p : ℕ} (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (i : Fin p) (j : Fin (n - p)) :
    cutIncidenceVector S (subtourCrossEdge hp σ i j) = 1 := by
  -- The block chart places exactly the left endpoint in the shore.
  unfold subtourCrossEdge
  rw [cutIncidenceVector_apply_pair]
  have hleft : (subtourLeftPosition hp i : ℕ) < p := by
    simp
  have hi : σ (subtourLeftPosition hp i) ∈ S := (hσ _).2 hleft
  have hj : σ (subtourRightPosition hp j) ∉ S := by
    rw [hσ]
    simp
  simp [hi, hj]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: a block of size at least two has a first position. -/
lemma subtourFirstPosition_lt {m : ℕ} (hm : 2 ≤ m) : 0 < m := by
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: a block of size at least two has a final position. -/
lemma subtourLastPosition_lt {m : ℕ} (hm : 2 ≤ m) : m - 1 < m := by
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: successor indices in `Fin (m - 1)` give positions in `Fin m`. -/
lemma subtourNonzeroPosition_lt
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) : i.1 + 1 < m := by
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the first position of a nontrivial block. -/
def subtourFirstPosition {m : ℕ} (hm : 2 ≤ m) : Fin m :=
  ⟨0, subtourFirstPosition_lt hm⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the final position of a nontrivial block. -/
def subtourLastPosition {m : ℕ} (hm : 2 ≤ m) : Fin m :=
  ⟨m - 1, subtourLastPosition_lt hm⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the nonzero block position indexed by `i : Fin (m - 1)`. -/
def subtourNonzeroPosition
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) : Fin m :=
  ⟨i.1 + 1, subtourNonzeroPosition_lt hm i⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the first block position has value zero. -/
@[simp] lemma subtourFirstPosition_val
    {m : ℕ} (hm : 2 ≤ m) : (subtourFirstPosition hm : ℕ) = 0 := by
  -- This is the defining value of the first position.
  rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the last block position has value `m - 1`. -/
@[simp] lemma subtourLastPosition_val
    {m : ℕ} (hm : 2 ≤ m) : (subtourLastPosition hm : ℕ) = m - 1 := by
  -- This is the defining value of the last position.
  rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the nonzero block position indexed by `i` has value `i + 1`. -/
@[simp] lemma subtourNonzeroPosition_val
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    (subtourNonzeroPosition hm i : ℕ) = i.1 + 1 := by
  -- This is the defining value of the successor position.
  rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the first block position is distinct from every nonzero position. -/
@[simp] lemma subtourFirstPosition_ne_nonzero
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    subtourFirstPosition hm ≠ subtourNonzeroPosition hm i := by
  -- Their natural-number values are respectively zero and a successor.
  intro h
  have hval := congrArg Fin.val h
  simp at hval

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: every nonzero block position is distinct from the first position. -/
@[simp] lemma subtourNonzeroPosition_ne_first
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    subtourNonzeroPosition hm i ≠ subtourFirstPosition hm :=
  (subtourFirstPosition_ne_nonzero hm i).symm

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the nonzero-position chart is injective. -/
lemma subtourNonzeroPosition_injective
    {m : ℕ} (hm : 2 ≤ m) : Function.Injective (subtourNonzeroPosition hm) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp at hval
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: equality of nonzero block positions is equality of their indices. -/
@[simp] lemma subtourNonzeroPosition_eq_iff
    {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m - 1)) :
    subtourNonzeroPosition hm i = subtourNonzeroPosition hm j ↔ i = j :=
  (subtourNonzeroPosition_injective hm).eq_iff

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: reversal exchanges the first and last positions of a nontrivial
block. -/
@[simp] lemma subtourFirstPosition_rev
    {m : ℕ} (hm : 2 ≤ m) :
    (subtourFirstPosition hm).rev = subtourLastPosition hm := by
  -- Compare the explicit values of the two positions.
  apply Fin.ext
  simp [Fin.val_rev]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: reversal exchanges the last and first positions of a nontrivial
block. -/
@[simp] lemma subtourLastPosition_rev
    {m : ℕ} (hm : 2 ≤ m) :
    (subtourLastPosition hm).rev = subtourFirstPosition hm := by
  -- Compare the explicit values of the two positions.
  apply Fin.ext
  simp [Fin.val_rev]
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the upper shore-size bound leaves at least two vertices in the
complement block. -/
lemma subtourRightBlock_two_le
    {n p : ℕ} (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2) : 2 ≤ n - p := by
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: swap the last position of a block with a prescribed nonzero
position, while fixing the first position. -/
def subtourEndpointPerm
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) : Equiv.Perm (Fin m) :=
  Equiv.swap (subtourLastPosition hm) (subtourNonzeroPosition hm i)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: `subtourEndpointPerm` fixes the first block position. -/
@[simp] lemma subtourEndpointPerm_apply_zero
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    subtourEndpointPerm hm i (subtourFirstPosition hm) = subtourFirstPosition hm := by
  -- Both positions swapped by the permutation are nonzero.
  have hlast : subtourFirstPosition hm ≠ subtourLastPosition hm := by
    intro h
    have hval := congrArg Fin.val h
    simp [subtourFirstPosition, subtourLastPosition] at hval
    omega
  have hnonzero : subtourFirstPosition hm ≠ subtourNonzeroPosition hm i := by
    intro h
    have hval := congrArg Fin.val h
    simp [subtourFirstPosition, subtourNonzeroPosition] at hval
  exact Equiv.swap_apply_of_ne_of_ne hlast hnonzero

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: `subtourEndpointPerm` sends the last block position to the prescribed
nonzero position. -/
@[simp] lemma subtourEndpointPerm_apply_last
    {m : ℕ} (hm : 2 ≤ m) (i : Fin (m - 1)) :
    subtourEndpointPerm hm i (subtourLastPosition hm) = subtourNonzeroPosition hm i := by
  -- This is the defining left endpoint of the transposition.
  exact Equiv.swap_apply_left _ _

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: every endpoint of a left internal edge lies in the shore. -/
lemma mem_shore_of_mem_subtourLeftEdge
    {n p : ℕ} (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (e : complete_graph_edges p) {v : Fin n}
    (hv : v ∈ ((subtourLeftEdge hp σ e : complete_graph_edges n) : Sym2 (Fin n))) :
    v ∈ S := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      simp only [subtourLeftEdge, Sym2.map_mk, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact (hσ _).2 (by simp)
      · exact (hσ _).2 (by simp)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: every endpoint of a right internal edge lies outside the shore. -/
lemma not_mem_shore_of_mem_subtourRightEdge
    {n p : ℕ} (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (e : complete_graph_edges (n - p)) {v : Fin n}
    (hv : v ∈ ((subtourRightEdge hp σ e : complete_graph_edges n) : Sym2 (Fin n))) :
    v ∉ S := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      simp only [subtourRightEdge, Sym2.map_mk, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · rw [hσ]
        simp
      · rw [hσ]
        simp

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: a local left path edge becomes the corresponding global path edge
of the block tour. -/
lemma subtourLeftEdge_pathEdge
    {n p : ℕ} (hpUpper : p ≤ n - 2) (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) (k : Fin (p - 1)) :
    subtourLeftEdge (by omega) σ (path_edge_of_index ρ₁ k) =
      path_edge_of_index (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        ⟨k.1, by omega⟩ := by
  -- Both sides are the unordered pair at local consecutive positions `k,k+1`.
  have hkSucc : k.1 + 1 < p := by
    have hk := k.2
    omega
  apply Subtype.ext
  change
    Sym2.map (fun i ↦ σ (subtourLeftPosition (by omega) i))
        (s(ρ₁ (⟨k.1, by omega⟩ : Fin p), ρ₁ ⟨k.1 + 1, hkSucc⟩)) =
      s(subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨k.1, by omega⟩,
        subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨k.1 + 1, by omega⟩)
  have hleft : (⟨k.1, by omega⟩ : Fin n) =
      subtourLeftPosition (by omega) (⟨k.1, by omega⟩ : Fin p) := by
    ext
    simp
  have hright : (⟨k.1 + 1, by omega⟩ : Fin n) =
      subtourLeftPosition (by omega) ⟨k.1 + 1, hkSucc⟩ := by
    ext
    simp
  rw [Sym2.map_mk, Sym2.eq_iff]
  left
  constructor
  · calc
      σ (subtourLeftPosition (by omega) (ρ₁ ⟨k.1, by omega⟩)) =
          subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
            (subtourLeftPosition (by omega) ⟨k.1, by omega⟩) :=
        (subtourBlockTourPerm_apply_left (by omega) σ ρ₁ ρ₂ _).symm
      _ = subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨k.1, by omega⟩ := by rw [hleft]
  · calc
      σ (subtourLeftPosition (by omega) (ρ₁ ⟨k.1 + 1, hkSucc⟩)) =
          subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
            (subtourLeftPosition (by omega) ⟨k.1 + 1, hkSucc⟩) :=
        (subtourBlockTourPerm_apply_left (by omega) σ ρ₁ ρ₂ _).symm
      _ = subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨k.1 + 1, by omega⟩ := by rw [hright]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: a local right path edge becomes the offset global path edge of the
block tour. -/
lemma subtourRightEdge_pathEdge
    {n p : ℕ} (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p)))
    (k : Fin ((n - p) - 1)) :
    subtourRightEdge (by omega) σ (path_edge_of_index ρ₂ k) =
      path_edge_of_index (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        ⟨p + k.1, by omega⟩ := by
  -- Offset by `p`; the two consecutive right-block positions remain consecutive globally.
  have hq : 2 ≤ n - p := by omega
  have hkSucc : k.1 + 1 < n - p := by
    have hk := k.2
    omega
  apply Subtype.ext
  change
    Sym2.map (fun i ↦ σ (subtourRightPosition (by omega) i))
        (s(ρ₂ (⟨k.1, by omega⟩ : Fin (n - p)), ρ₂ ⟨k.1 + 1, hkSucc⟩)) =
      s(subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨p + k.1, by omega⟩,
        subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨p + k.1 + 1, by omega⟩)
  have hleft : (⟨p + k.1, by omega⟩ : Fin n) =
      subtourRightPosition (by omega) (⟨k.1, by omega⟩ : Fin (n - p)) := by
    ext
    simp
  have hright : (⟨p + k.1 + 1, by omega⟩ : Fin n) =
      subtourRightPosition (by omega) ⟨k.1 + 1, hkSucc⟩ := by
    ext
    simp [Nat.add_assoc]
  rw [Sym2.map_mk, Sym2.eq_iff]
  left
  constructor
  · calc
      σ (subtourRightPosition (by omega) (ρ₂ ⟨k.1, by omega⟩)) =
          subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
            (subtourRightPosition (by omega) ⟨k.1, by omega⟩) :=
        (subtourBlockTourPerm_apply_right (by omega) σ ρ₁ ρ₂ _).symm
      _ = subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨p + k.1, by omega⟩ := by rw [hleft]
  · calc
      σ (subtourRightPosition (by omega) (ρ₂ ⟨k.1 + 1, hkSucc⟩)) =
          subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
            (subtourRightPosition (by omega) ⟨k.1 + 1, hkSucc⟩) :=
        (subtourBlockTourPerm_apply_right (by omega) σ ρ₁ ρ₂ _).symm
      _ = subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ ⟨p + k.1 + 1, by omega⟩ := by rw [hright]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the unique path edge between the two blocks is the edge joining the
last left endpoint to the first right endpoint. -/
lemma subtourBlockTour_boundaryEdge
    {n p : ℕ} (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (σ : Equiv.Perm (Fin n))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) :
    path_edge_of_index (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        ⟨p - 1, by omega⟩ =
      subtourCrossEdge (by omega) σ (ρ₁ (subtourLastPosition hpLower))
        (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) := by
  -- Identify the two path endpoints through the block chart, then use endpoint extensionality.
  let τ := subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
  apply Subtype.ext
  apply Sym2.ext
  intro v
  have hleft : (⟨p - 1, by omega⟩ : Fin n) =
      subtourLeftPosition (by omega) (subtourLastPosition hpLower) := by
    ext
    simp
  have hright : (⟨p, by omega⟩ : Fin n) =
      subtourRightPosition (by omega)
        (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper)) := by
    ext
    simp
  have hleftEval : τ ⟨p - 1, by omega⟩ =
      σ (subtourLeftPosition (by omega) (ρ₁ (subtourLastPosition hpLower))) := by
    rw [hleft]
    exact subtourBlockTourPerm_apply_left (by omega) σ ρ₁ ρ₂ _
  have hrightEval : τ ⟨p, by omega⟩ =
      σ (subtourRightPosition (by omega)
        (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper)))) := by
    rw [hright]
    exact subtourBlockTourPerm_apply_right (by omega) σ ρ₁ ρ₂ _
  have hrightEval' : τ ⟨p - 1 + 1, by omega⟩ =
      σ (subtourRightPosition (by omega)
        (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper)))) := by
    have hpos : (⟨p - 1 + 1, by omega⟩ : Fin n) = ⟨p, by omega⟩ := by
      apply Fin.ext
      exact Nat.sub_add_cancel (by omega)
    rw [hpos, hrightEval]
  let boundary : Fin (n - 1) := ⟨p - 1, by omega⟩
  have hleftNamed : τ (pathEdgeLeftPosition boundary) =
      σ (subtourLeftPosition (by omega) (ρ₁ (subtourLastPosition hpLower))) := by
    calc
      τ (pathEdgeLeftPosition boundary) =
          τ (subtourLeftPosition (by omega) (subtourLastPosition hpLower)) := by
            apply congrArg τ
            apply Fin.ext
            simp [boundary, pathEdgeLeftPosition]
      _ = σ (subtourLeftPosition (by omega) (ρ₁ (subtourLastPosition hpLower))) :=
        subtourBlockTourPerm_apply_left (by omega) σ ρ₁ ρ₂ _
  have hrightNamed : τ (pathEdgeRightPosition boundary) =
      σ (subtourRightPosition (by omega)
        (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper)))) := by
    calc
      τ (pathEdgeRightPosition boundary) =
          τ (subtourRightPosition (by omega)
            (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) := by
              apply congrArg τ
              apply Fin.ext
              simp [boundary, pathEdgeRightPosition]
              omega
      _ = σ (subtourRightPosition (by omega)
          (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper)))) :=
        subtourBlockTourPerm_apply_right (by omega) σ ρ₁ ρ₂ _
  rw [mem_pathEdgeOfIndex_iff]
  unfold subtourCrossEdge
  simp only [Sym2.mem_iff]
  rw [hleftNamed, hrightNamed]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the closing edge of a block tour joins the first left endpoint to the
last right endpoint. -/
lemma subtourBlockTour_closingEdge
    {m p : ℕ} (hpLower : 2 ≤ p) (hpUpper : p ≤ m + 2 - 2)
    (σ : Equiv.Perm (Fin (m + 2)))
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (m + 2 - p))) :
    hamiltonian_tour_closing_edge (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) =
      subtourCrossEdge (by omega) σ (ρ₁ (subtourFirstPosition hpLower))
        (ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper))) := by
  -- The first and last global positions are the first left and last right block positions.
  apply Subtype.ext
  change
      s(subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ 0,
        subtourBlockTourPerm (by omega) σ ρ₁ ρ₂ (hamiltonian_tour_last_position m)) =
      s(σ (subtourLeftPosition (by omega) (ρ₁ (subtourFirstPosition hpLower))),
        σ (subtourRightPosition (by omega)
          (ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper)))))
  have hfirst : (0 : Fin (m + 2)) =
      subtourLeftPosition (by omega) (subtourFirstPosition hpLower) := by
    ext
    simp
  have hlast : hamiltonian_tour_last_position m =
      subtourRightPosition (by omega)
        (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper)) := by
    ext
    simp [hamiltonian_tour_last_position]
    omega
  rw [Sym2.eq_iff]
  left
  constructor
  · rw [hfirst, subtourBlockTourPerm_apply_left]
  · rw [hlast, subtourBlockTourPerm_apply_right]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: a cross edge belongs to a block tour exactly when it is one of the
two connector edges. -/
lemma subtourCrossEdge_mem_blockTour_iff
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p)))
    (i : Fin p) (j : Fin (n - p)) :
    subtourCrossEdge (by omega) σ i j ∈
        hamiltonian_tour_edge_finset (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) ↔
      subtourCrossEdge (by omega) σ i j =
          subtourCrossEdge (by omega) σ (ρ₁ (subtourLastPosition hpLower))
            (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) ∨
        subtourCrossEdge (by omega) σ i j =
          subtourCrossEdge (by omega) σ (ρ₁ (subtourFirstPosition hpLower))
            (ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper))) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  rw [Nat.add_comm] at hm
  subst n
  let τ := subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
  have hτ : ∀ t : Fin (m + 2), τ t ∈ S ↔ (t : ℕ) < p :=
    subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂
  rw [hamiltonian_tour_edge_finset, Finset.mem_insert]
  constructor
  · rintro (hclosing | hpath)
    · right
      exact hclosing.trans
        (subtourBlockTour_closingEdge hpLower hpUpper σ ρ₁ ρ₂)
    · rw [hamiltonian_path_edge_finset, Finset.mem_image] at hpath
      rcases hpath with ⟨k, hkU, hk⟩
      have hkCut : cutIncidenceVector S (path_edge_of_index τ k) = 1 := by
        rw [hk]
        exact subtourCrossEdge_cutValue (by omega) S σ hσ i j
      rw [cutIncidenceVector_pathEdgeOfIndex_of_initialSegment S p τ hτ] at hkCut
      have hkBoundary : k.1 = p - 1 := by
        by_cases hkp : k.1 < p
        · by_cases hkSucc : k.1 + 1 < p
          · simp [hkp, hkSucc] at hkCut
          · omega
        · simp [hkp] at hkCut
          omega
      have hkEq : k = (⟨p - 1, by omega⟩ : Fin (m + 2 - 1)) := Fin.ext hkBoundary
      rw [hkEq] at hk
      left
      exact hk.symm.trans (subtourBlockTour_boundaryEdge hpLower hpUpper σ ρ₁ ρ₂)
  · rintro (hboundary | hclosing)
    · right
      rw [hamiltonian_path_edge_finset, Finset.mem_image]
      refine ⟨(⟨p - 1, by omega⟩ : Fin (m + 2 - 1)), Finset.mem_univ _, ?_⟩
      exact (subtourBlockTour_boundaryEdge hpLower hpUpper σ ρ₁ ρ₂).trans hboundary.symm
    · left
      exact hclosing.trans
        (subtourBlockTour_closingEdge hpLower hpUpper σ ρ₁ ρ₂).symm

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the cross coordinate of a block-tour incidence vector is the
indicator of its two connector pairs. -/
lemma subtourBlockTour_crossCoordinate
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p)))
    (i : Fin p) (j : Fin (n - p)) :
    hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        (subtourCrossEdge (by omega) σ i j) =
      if (i, j) = (ρ₁ (subtourLastPosition hpLower),
            ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) ∨
          (i, j) = (ρ₁ (subtourFirstPosition hpLower),
            ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper))) then 1 else 0 := by
  -- Reduce tour membership to the two connector edges, then use injectivity of the cross chart.
  rw [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge,
    subtourCrossEdge_mem_blockTour_iff hn hpLower hpUpper S σ hσ]
  let f : Fin p × Fin (n - p) → complete_graph_edges n :=
    fun z ↦ subtourCrossEdge (by omega) σ z.1 z.2
  have hinj : Function.Injective f := subtourCrossEdge_injective (by omega) σ
  have hconditions :
      (subtourCrossEdge (by omega) σ i j =
            subtourCrossEdge (by omega) σ (ρ₁ (subtourLastPosition hpLower))
              (ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) ∨
          subtourCrossEdge (by omega) σ i j =
            subtourCrossEdge (by omega) σ (ρ₁ (subtourFirstPosition hpLower))
              (ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper)))) ↔
        ((i, j) = (ρ₁ (subtourLastPosition hpLower),
              ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) ∨
          (i, j) = (ρ₁ (subtourFirstPosition hpLower),
              ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper)))) := by
    constructor
    · rintro (h | h)
      · left
        apply hinj
        simpa [f] using h
      · right
        apply hinj
        simpa [f] using h
    · rintro (h | h)
      · left
        simpa [f] using congrArg f h
      · right
        simpa [f] using congrArg f h
  rw [hconditions]
  by_cases h :
      (i, j) = (ρ₁ (subtourLastPosition hpLower),
            ρ₂ (subtourFirstPosition (subtourRightBlock_two_le hpLower hpUpper))) ∨
        (i, j) = (ρ₁ (subtourFirstPosition hpLower),
            ρ₂ (subtourLastPosition (subtourRightBlock_two_le hpLower hpUpper)))
  · simp
  · simp

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: every path edge belongs to the tour obtained by adding the closing
edge. -/
lemma hamiltonianPathEdge_mem_tour
    {n : ℕ} (hn : 2 ≤ n) (τ : Equiv.Perm (Fin n)) {e : complete_graph_edges n}
    (he : e ∈ hamiltonian_path_edge_finset τ) :
    e ∈ hamiltonian_tour_edge_finset τ := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hm
  subst n
  simp [hamiltonian_tour_edge_finset, he]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: reversing the position order of a Hamiltonian path preserves its
edge-incidence vector. -/
lemma hamiltonianPathIncidence_reverse
    {n : ℕ} (hn : 2 ≤ n) (ρ : Equiv.Perm (Fin n)) :
    hamiltonian_path_incidence_vector (Fin.revPerm.trans ρ) =
      hamiltonian_path_incidence_vector ρ := by
  have hedge (k : Fin (n - 1)) :
      path_edge_of_index (Fin.revPerm.trans ρ) k.rev = path_edge_of_index ρ k := by
    -- Compare endpoint membership, using the public path-edge interface to avoid unfolding its
    -- private position wrappers.
    apply Subtype.ext
    apply Sym2.ext
    intro v
    rw [mem_pathEdgeOfIndex_iff, mem_pathEdgeOfIndex_iff]
    have hleft :
        (Fin.revPerm.trans ρ) (pathEdgeLeftPosition k.rev) =
          ρ (pathEdgeRightPosition k) := by
      apply congrArg ρ
      apply Fin.ext
      simp only [Fin.revPerm_apply, Fin.val_rev,
        pathEdgeLeftPosition, pathEdgeRightPosition]
      omega
    have hright :
        (Fin.revPerm.trans ρ) (pathEdgeRightPosition k.rev) =
          ρ (pathEdgeLeftPosition k) := by
      apply congrArg ρ
      apply Fin.ext
      simp only [Fin.revPerm_apply, Fin.val_rev,
        pathEdgeLeftPosition, pathEdgeRightPosition]
      omega
    rw [hleft, hright]
    tauto
  funext e
  simp only [hamiltonian_path_incidence_vector]
  congr 1
  apply propext
  simp only [hamiltonian_path_edge_finset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k.rev, ?_⟩
    -- Normalize the double reversal before composing with the membership witness.
    calc
      path_edge_of_index ρ k.rev =
          path_edge_of_index (Fin.revPerm.trans ρ) k := by
            simpa using (hedge k.rev).symm
      _ = e := hk
  · rintro ⟨k, hk⟩
    refine ⟨k.rev, ?_⟩
    calc
      path_edge_of_index (Fin.revPerm.trans ρ) k.rev =
          path_edge_of_index ρ k := hedge k
      _ = e := hk

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: restricting a block tour to its first shore recovers the first
Hamiltonian-path incidence vector. -/
lemma subtourBlockTour_leftCoordinate
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p)))
    (e : complete_graph_edges p) :
    hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        (subtourLeftEdge (by omega) σ e) =
      hamiltonian_path_incidence_vector ρ₁ e := by
  let τ := subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
  have hiff : subtourLeftEdge (by omega) σ e ∈ hamiltonian_tour_edge_finset τ ↔
      e ∈ hamiltonian_path_edge_finset ρ₁ := by
    constructor
    · intro htour
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
      rw [Nat.add_comm] at hm
      subst n
      simp only [hamiltonian_tour_edge_finset, Finset.mem_insert] at htour
      rcases htour with hclose | hpath
      · have hlastEdge :
            τ (hamiltonian_tour_last_position m) ∈
              ((subtourLeftEdge (by omega) σ e : complete_graph_edges (m + 2)) :
                Sym2 (Fin (m + 2))) := by
          rw [hclose]
          simp [hamiltonian_tour_closing_edge, Sym2.mem_iff]
        have hlastS := mem_shore_of_mem_subtourLeftEdge (by omega) S σ hσ e hlastEdge
        have hlt := (subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂ _).1 hlastS
        simp [hamiltonian_tour_last_position] at hlt
        omega
      · rw [hamiltonian_path_edge_finset, Finset.mem_image] at hpath
        rcases hpath with ⟨k, hkU, hk⟩
        have hrightEdge :
            τ ⟨k.1 + 1, by omega⟩ ∈
              ((subtourLeftEdge (by omega) σ e : complete_graph_edges (m + 2)) :
                Sym2 (Fin (m + 2))) := by
          rw [← hk]
          refine (mem_pathEdgeOfIndex_iff _ τ k).2 (Or.inr ?_)
          apply congrArg τ
          apply Fin.ext
          rfl
        have hrightS := mem_shore_of_mem_subtourLeftEdge (by omega) S σ hσ e hrightEdge
        have hklt :=
          (subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂ _).1 hrightS
        have hkSuccLt : k.1 + 1 < p := by
          simpa using hklt
        let k' : Fin (p - 1) := ⟨k.1, by omega⟩
        have hedge : e = path_edge_of_index ρ₁ k' := by
          apply subtourLeftEdge_injective (by omega) σ
          calc
            subtourLeftEdge (by omega) σ e = path_edge_of_index τ k := hk.symm
            _ = subtourLeftEdge (by omega) σ (path_edge_of_index ρ₁ k') := by
              symm
              simpa [τ, k'] using subtourLeftEdge_pathEdge hpUpper σ ρ₁ ρ₂ k'
        rw [hamiltonian_path_edge_finset, Finset.mem_image]
        exact ⟨k', Finset.mem_univ _, hedge.symm⟩
    · intro hpath
      rw [hamiltonian_path_edge_finset, Finset.mem_image] at hpath
      rcases hpath with ⟨k, hkU, hk⟩
      have hglobal : subtourLeftEdge (by omega) σ e ∈
          hamiltonian_path_edge_finset τ := by
        rw [hamiltonian_path_edge_finset, Finset.mem_image]
        refine ⟨(⟨k.1, by omega⟩ : Fin (n - 1)), Finset.mem_univ _, ?_⟩
        rw [← hk]
        exact (subtourLeftEdge_pathEdge hpUpper σ ρ₁ ρ₂ k).symm
      exact hamiltonianPathEdge_mem_tour (by omega) τ hglobal
  -- Compare the two indicator functions propositionally, avoiding decidable-instance transport.
  by_cases hpath : e ∈ hamiltonian_path_edge_finset ρ₁
  · have htour := hiff.2 hpath
    have htour' : subtourLeftEdge (by omega) σ e ∈
        hamiltonian_tour_edge_finset (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) := by
      simpa [τ] using htour
    simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge,
      hamiltonian_path_incidence_vector, htour', hpath]
  · have htour : subtourLeftEdge (by omega) σ e ∉
        hamiltonian_tour_edge_finset τ := fun h ↦ hpath (hiff.1 h)
    have htour' : subtourLeftEdge (by omega) σ e ∉
        hamiltonian_tour_edge_finset (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) := by
      simpa [τ] using htour
    simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge,
      hamiltonian_path_incidence_vector, htour', hpath]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: restricting a block tour to its second shore recovers the second
Hamiltonian-path incidence vector. -/
lemma subtourBlockTour_rightCoordinate
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p)))
    (e : complete_graph_edges (n - p)) :
    hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
        (subtourRightEdge (by omega) σ e) =
      hamiltonian_path_incidence_vector ρ₂ e := by
  let τ := subtourBlockTourPerm (by omega) σ ρ₁ ρ₂
  have hiff : subtourRightEdge (by omega) σ e ∈ hamiltonian_tour_edge_finset τ ↔
      e ∈ hamiltonian_path_edge_finset ρ₂ := by
    constructor
    · intro htour
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
      rw [Nat.add_comm] at hm
      subst n
      simp only [hamiltonian_tour_edge_finset, Finset.mem_insert] at htour
      rcases htour with hclose | hpath
      · have hfirstEdge : τ 0 ∈
            ((subtourRightEdge (by omega) σ e : complete_graph_edges (m + 2)) :
              Sym2 (Fin (m + 2))) := by
          rw [hclose]
          simp [hamiltonian_tour_closing_edge, Sym2.mem_iff]
        have hfirstNot := not_mem_shore_of_mem_subtourRightEdge
          (by omega) S σ hσ e hfirstEdge
        have hzeroLt : (0 : ℕ) < p := by omega
        have hfirstMem : τ 0 ∈ S :=
          (subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂ 0).2 hzeroLt
        exact (hfirstNot hfirstMem).elim
      · rw [hamiltonian_path_edge_finset, Finset.mem_image] at hpath
        rcases hpath with ⟨k, hkU, hk⟩
        have hleftEdge : τ ⟨k.1, by omega⟩ ∈
            ((subtourRightEdge (by omega) σ e : complete_graph_edges (m + 2)) :
              Sym2 (Fin (m + 2))) := by
          rw [← hk]
          refine (mem_pathEdgeOfIndex_iff _ τ k).2 (Or.inl ?_)
          apply congrArg τ
          apply Fin.ext
          rfl
        have hleftNot := not_mem_shore_of_mem_subtourRightEdge
          (by omega) S σ hσ e hleftEdge
        have hkge : p ≤ k.1 := by
          by_contra h
          have hkltP : k.1 < p := by omega
          exact hleftNot
            ((subtourBlockTourPerm_mem_iff (by omega) S σ hσ ρ₁ ρ₂ _).2 hkltP)
        let k' : Fin ((m + 2 - p) - 1) := ⟨k.1 - p, by omega⟩
        have hedge : e = path_edge_of_index ρ₂ k' := by
          apply subtourRightEdge_injective (by omega) σ
          calc
            subtourRightEdge (by omega) σ e = path_edge_of_index τ k := hk.symm
            _ = subtourRightEdge (by omega) σ (path_edge_of_index ρ₂ k') := by
              symm
              simpa [τ, k', Nat.add_sub_of_le hkge] using
                subtourRightEdge_pathEdge hpLower hpUpper σ ρ₁ ρ₂ k'
        rw [hamiltonian_path_edge_finset, Finset.mem_image]
        exact ⟨k', Finset.mem_univ _, hedge.symm⟩
    · intro hpath
      rw [hamiltonian_path_edge_finset, Finset.mem_image] at hpath
      rcases hpath with ⟨k, hkU, hk⟩
      have hglobal : subtourRightEdge (by omega) σ e ∈
          hamiltonian_path_edge_finset τ := by
        rw [hamiltonian_path_edge_finset, Finset.mem_image]
        refine ⟨(⟨p + k.1, by omega⟩ : Fin (n - 1)), Finset.mem_univ _, ?_⟩
        rw [← hk]
        exact (subtourRightEdge_pathEdge hpLower hpUpper σ ρ₁ ρ₂ k).symm
      exact hamiltonianPathEdge_mem_tour (by omega) τ hglobal
  -- Compare the two indicator functions propositionally, avoiding decidable-instance transport.
  by_cases hpath : e ∈ hamiltonian_path_edge_finset ρ₂
  · have htour := hiff.2 hpath
    have htour' : subtourRightEdge (by omega) σ e ∈
        hamiltonian_tour_edge_finset (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) := by
      simpa [τ] using htour
    simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge,
      hamiltonian_path_incidence_vector, htour', hpath]
  · have htour : subtourRightEdge (by omega) σ e ∉
        hamiltonian_tour_edge_finset τ := fun h ↦ hpath (hiff.1 h)
    have htour' : subtourRightEdge (by omega) σ e ∉
        hamiltonian_tour_edge_finset (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) := by
      simpa [τ] using htour
    simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge,
      hamiltonian_path_incidence_vector, htour', hpath]

end Theorem719Support

open Theorem719Support

/-- The boundary edge set `δ(S)` of a vertex subset `S` in the complete graph on `Fin n`. -/
abbrev edge_boundary_finset {n : ℕ} (S : Finset (Fin n)) : Finset (complete_graph_edges n) :=
  Finset.univ.filter
    fun e ↦ completeGraphEdge e ∈ δ[completeGraph (Fin n)] (S : Set (Fin n))

notation "δ(" S ")" => edge_boundary_finset S

/-- The complete-graph cut notation `δ(S)` is the Chapter 4 cut-edge finset specialized to
`completeGraph (Fin n)` and reindexed along `completeGraphEdge`. -/
theorem mem_edge_boundary_finset_iff_mem_cutEdgeFinset
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔ completeGraphEdge e ∈ δ[completeGraph (Fin n)] (S : Set (Fin n)) := by
  simp [edge_boundary_finset]

/-- Membership in `δ(S)` means that the edge admits one endpoint in `S` and the other outside
`S`. -/
theorem mem_edge_boundary_finset_iff_mixed_endpoints
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = e.1 := by
  simpa [completeGraphEdge] using
    (mem_cutEdgeFinset_iff (completeGraph (Fin n)) :
      completeGraphEdge e ∈ δ[completeGraph (Fin n)] (S : Set (Fin n)) ↔
        ∃ u ∈ (S : Set (Fin n)), ∃ v ∉ (S : Set (Fin n)), s(u, v) = completeGraphEdge e)

/-- Membership in `δ(S)` is equivalent to saying that the two canonical `Sym2.out` endpoints of
`e` lie on opposite sides of the cut. -/
theorem mem_edge_boundary_finset_iff_out_endpoints
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔
      (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.2 ∈ S ∧ e.1.out.1 ∉ S) := by
  constructor
  · intro he
    rcases (mem_edge_boundary_finset_iff_mixed_endpoints S e).1 he with ⟨u, hu, v, hv, huv⟩
    rw [← e.1.out_eq] at huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact (mem_edge_boundary_finset_iff_mixed_endpoints S e).2
        ⟨e.1.out.1, h₁, e.1.out.2, h₂, e.1.out_eq⟩
    · exact (mem_edge_boundary_finset_iff_mixed_endpoints S e).2
        ⟨e.1.out.2, h₁, e.1.out.1, h₂, Sym2.eq_swap.trans e.1.out_eq⟩

/-- Membership in `δ(S)` means that the canonical cut-incidence vector of `S` takes value `1` on
that edge coordinate. -/
theorem mem_edge_boundary_finset_iff
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    e ∈ δ(S) ↔ cutIncidenceVector S e = 1 := by
  rw [mem_edge_boundary_finset_iff_out_endpoints]
  have hpair :
      cutIncidenceVector S e =
        if (e.1.out.1 ∈ S) = (e.1.out.2 ∈ S) then 0 else 1 := by
    simpa [e.1.out_eq] using
      (cutIncidenceVector_apply_pair S e.1.out.1 e.1.out.2 (by simpa [e.1.out_eq] using e.2))
  rw [hpair]
  by_cases h₁ : e.1.out.1 ∈ S
  · by_cases h₂ : e.1.out.2 ∈ S
    · have hsame :
          (e.1.out.1 ∈ S) = (e.1.out.2 ∈ S) := by
        exact propext (by simp [h₁, h₂])
      simp [h₁, h₂]
    · have hdiff :
          (e.1.out.1 ∈ S) ≠ (e.1.out.2 ∈ S) := by
        intro hsame
        exact h₂ (hsame ▸ h₁)
      simp [h₁, h₂]
  · by_cases h₂ : e.1.out.2 ∈ S
    · have hdiff :
          (e.1.out.1 ∈ S) ≠ (e.1.out.2 ∈ S) := by
        intro hsame
        exact h₁ (hsame ▸ h₂)
      simp [h₁, h₂]
    · have hsame :
          (e.1.out.1 ∈ S) = (e.1.out.2 ∈ S) := by
        exact propext (by simp [h₁, h₂])
      simp [h₁, h₂]

/-- The left-hand side `∑_{e ∈ δ(S)} x_e` of the subtour-elimination constraint associated with
`S`. -/
def subtour_elimination_value
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) : ℝ :=
  Finset.sum (δ(S)) x

/-- Every coordinate of the canonical cut-incidence vector is either `0` or `1`. -/
theorem cutIncidenceVector_eq_zero_or_one
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    cutIncidenceVector S e = 0 ∨ cutIncidenceVector S e = 1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      rw [cutIncidenceVector_apply_pair S u v he]
      by_cases huv : (u ∈ S) = (v ∈ S) <;> simp [huv]

/-- The canonical cut-incidence vector is the indicator of the boundary-edge finset `δ(S)`. -/
theorem cutIncidenceVector_eq_indicator_edge_boundary
    {n : ℕ} (S : Finset (Fin n)) (e : complete_graph_edges n) :
    cutIncidenceVector S e = if e ∈ δ(S) then 1 else 0 := by
  by_cases he : e ∈ δ(S)
  · simpa [he] using (mem_edge_boundary_finset_iff S e).mp he
  · rcases cutIncidenceVector_eq_zero_or_one S e with hzero | hone
    · simp [he, hzero]
    · exfalso
      exact he ((mem_edge_boundary_finset_iff S e).2 hone)

/-- `subtour_elimination_value S x` is the sum of the coordinates of `x` over the cut `δ(S)`. -/
theorem subtour_elimination_value_eq
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    subtour_elimination_value S x = Finset.sum (δ(S)) x :=
  rfl

/-- The source-facing subtour-elimination sum is the canonical dot product with the cut-incidence
vector of `S`. -/
theorem subtour_elimination_value_eq_dotProduct
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    subtour_elimination_value S x = cutIncidenceVector S ⬝ᵥ x := by
  symm
  calc
    cutIncidenceVector S ⬝ᵥ x
        = ∑ e : complete_graph_edges n, (if e ∈ δ(S) then 1 else 0) * x e := by
            simp [dotProduct, cutIncidenceVector_eq_indicator_edge_boundary]
    _ = Finset.sum (δ(S)) x := by
          calc
            ∑ e : complete_graph_edges n, (if e ∈ δ(S) then 1 else 0) * x e
                = ∑ e : complete_graph_edges n, if e ∈ δ(S) then x e else 0 := by
                    refine Finset.sum_congr rfl fun e _ ↦ ?_
                    by_cases he : e ∈ δ(S) <;> simp [he]
            _ = Finset.sum (δ(S)) x := by
                  have huniv :
                      Finset.univ.filter
                          (fun e : complete_graph_edges n ↦ e ∈ δ(S)) = δ(S) := by
                    ext e
                    simp
                  rw [← huniv, Finset.sum_filter]
                  simp
    _ = subtour_elimination_value S x := by
          rw [subtour_elimination_value]

/-- The equality face of the traveling salesman polytope cut out by the subtour-elimination
constraint for `S`. -/
def subtour_elimination_face (n : ℕ) (S : Finset (Fin n)) :
    Set (complete_graph_edges n → ℝ) :=
  {x | x ∈ travelingSalesmanPolytope n ∧ subtour_elimination_value S x = 2}

/-- Membership in `subtour_elimination_face n S` means belonging to the traveling salesman
polytope and meeting the subtour-elimination inequality at equality. -/
theorem mem_subtour_elimination_face_iff
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    x ∈ subtour_elimination_face n S ↔
      x ∈ travelingSalesmanPolytope n ∧ subtour_elimination_value S x = 2 :=
  Iff.rfl

/-- The source-facing equality face is equivalently the equality set of the canonical valid
inequality `(-cutIncidenceVector S) ⬝ᵥ x ≤ -2`. -/
theorem mem_subtour_elimination_face_iff_neg_cutIncidence
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    x ∈ subtour_elimination_face n S ↔
      x ∈ travelingSalesmanPolytope n ∧ (-cutIncidenceVector S) ⬝ᵥ x = -2 := by
  rw [mem_subtour_elimination_face_iff, subtour_elimination_value_eq_dotProduct]
  constructor
  · rintro ⟨hx, hxeq⟩
    exact ⟨hx, by rw [neg_dotProduct, hxeq]⟩
  · rintro ⟨hx, hxeq⟩
    have hxeq' : cutIncidenceVector S ⬝ᵥ x = 2 := by
      simpa [neg_dotProduct] using congrArg Neg.neg hxeq
    exact ⟨hx, hxeq'⟩

/-- Helper for Theorem 7.19: the local complete-graph incident-edge owner at the vertex `v`. -/
private def completeGraphIncidentEdgeFinset {n : ℕ} (v : Fin n) :
    Finset (complete_graph_edges n) :=
  Finset.univ.filter fun e ↦ v ∈ (e : Sym2 (Fin n))

/-- Helper for Theorem 7.19: the local incident-edge filter view agrees with the shared
Section 7.4 owner. -/
private theorem completeGraphIncidentEdgeFinset_eq
    {n : ℕ} (v : Fin n) :
    completeGraphIncidentEdgeFinset v =
      (incidentEdgeFinset (completeGraph (Fin n)) v).map
        completeGraphEdgeEquiv.symm.toEmbedding := by
  -- Both owners record exactly the complete-graph edges whose unordered pair contains `v`.
  ext e
  simpa [completeGraphIncidentEdgeFinset] using
    (mem_completeGraph_incidentEdgeFinset_iff (i := v) (e := e)).symm

/-- Helper for Theorem 7.19: membership in the local incident-edge owner means that `v` is an
endpoint of the edge coordinate. -/
private theorem mem_completeGraphIncidentEdgeFinset_iff
    {n : ℕ} {v : Fin n} {e : complete_graph_edges n} :
    e ∈ completeGraphIncidentEdgeFinset v ↔ v ∈ (e : Sym2 (Fin n)) := by
  -- This is just the defining filter condition.
  simp [completeGraphIncidentEdgeFinset]

/-- Helper for Theorem 7.19: the induced complete-graph edges on `S`, recorded in the
`complete_graph_edges n` coordinates. -/
private def subtourInducedEdgeFinset {n : ℕ} (S : Finset (Fin n)) :
    Finset (complete_graph_edges n) :=
  Finset.univ.filter fun e ↦
    ((completeGraphEdge e : (completeGraph (Fin n)).edgeSet) : Sym2 (Fin n)) ∈
      ((⊤ : (completeGraph (Fin n)).Subgraph).induce (S : Set (Fin n))).edgeSet

/-- Helper for Theorem 7.19: a complete-graph indicator sum rewrites to the corresponding filtered
edge owner sum. -/
private lemma completeGraphSumIte_eq_sumFilter
    {n : ℕ} (p : complete_graph_edges n → Prop) [DecidablePred p]
    (f : complete_graph_edges n → ℝ) :
    (∑ e : complete_graph_edges n, if p e then f e else 0) = (Finset.univ.filter p).sum f := by
  -- Rewrite the filtered sum into the matching indicator sum over `Finset.univ`.
  let _ : Fintype (complete_graph_edges n) := Fintype.ofFinite (complete_graph_edges n)
  rw [Finset.sum_filter]

/-- Helper for Theorem 7.19: filtering `S` by the endpoints of an edge matches filtering the
edge-endpoint finset by membership in `S`. -/
private lemma completeGraphEdgeFilter_eq_endpointFilter
    {n : ℕ} (S : Finset (Fin n))
    (e : complete_graph_edges n) :
    S.filter (fun v ↦ v ∈ (e : Sym2 (Fin n))) =
      ((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ (S : Set (Fin n))) := by
  -- Both filters enforce the same pair of conditions: lying in `S` and lying on the edge.
  ext v
  simp [Sym2.mem_toFinset, and_comm]

/-- Helper for Theorem 7.19: membership in `subtourInducedEdgeFinset S` means that both canonical
endpoints of `e` lie in `S`. -/
private lemma mem_subtourInducedEdgeFinset_iff
    {n : ℕ} (S : Finset (Fin n))
    (e : complete_graph_edges n) :
    e ∈ subtourInducedEdgeFinset S ↔ e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S := by
  have hneq : e.1.out.1 ≠ e.1.out.2 := by
    -- Complete-graph edge coordinates are non-diagonal unordered pairs.
    intro hout_eq
    apply e.2
    rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
    exact hout_eq
  rw [subtourInducedEdgeFinset, Finset.mem_filter]
  constructor
  · intro he
    rw [completeGraphEdge_coe, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet] at he
    simpa [SimpleGraph.Subgraph.induce, hneq] using he.2
  · intro he
    refine ⟨by simp, ?_⟩
    rw [completeGraphEdge_coe, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
    simpa [SimpleGraph.Subgraph.induce, hneq] using he

/-- Helper for Theorem 7.19: an induced edge of `S` cannot also lie in the boundary `δ(S)`. -/
private lemma not_mem_edgeBoundary_of_mem_induced
    {n : ℕ} (S : Finset (Fin n))
    (e : complete_graph_edges n)
    (he : e ∈ subtourInducedEdgeFinset S) :
    e ∉ δ(S) := by
  -- The cut `δ(S)` requires exactly one endpoint in `S`, while an induced edge has both.
  rw [mem_subtourInducedEdgeFinset_iff] at he
  intro hcut
  rcases (mem_edge_boundary_finset_iff_out_endpoints S e).1 hcut with
    (⟨_, h₂⟩ | ⟨_, h₁⟩)
  · exact h₂ he.2
  · exact h₁ he.1

/-- Helper for Theorem 7.19: the filtered two-endpoint finset has cardinality `2`, `1`, or `0`
according to how many endpoints lie in `S`. -/
private lemma pairFilterCard_of_ne
    {n : ℕ} (a b : Fin n)
    (hab : a ≠ b)
    (S : Finset (Fin n)) :
    (((({a, b} : Finset (Fin n)).filter fun v ↦ v ∈ (S : Set (Fin n))).card : ℕ) : ℝ) =
      if a ∈ (S : Set (Fin n)) ∧ b ∈ (S : Set (Fin n)) then 2
      else if a ∈ (S : Set (Fin n)) ∨ b ∈ (S : Set (Fin n)) then 1 else 0 := by
  -- Split into the four endpoint-membership cases.
  by_cases ha : a ∈ (S : Set (Fin n))
  · by_cases hb : b ∈ (S : Set (Fin n))
    · have hfilter :
          ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ (S : Set (Fin n))) = {a, b} := by
        ext v
        constructor
        · intro hv
          exact (Finset.mem_filter.mp hv).1
        · intro hv
          refine Finset.mem_filter.mpr ⟨hv, ?_⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · simp [ha]
          · rw [Finset.mem_singleton.mp hv']
            simp [hb]
      rw [hfilter]
      simp [ha, hb, hab]
    · have hfilter :
          ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ (S : Set (Fin n))) = {a} := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · simp
          · exfalso
            rw [Finset.mem_singleton.mp hv'] at hvS
            exact hb hvS
        · intro hv
          rcases Finset.mem_singleton.mp hv with rfl
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · simp
          · simpa using ha
      rw [hfilter]
      simp [ha, hb]
  · by_cases hb : b ∈ (S : Set (Fin n))
    · have hfilter :
          ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ (S : Set (Fin n))) = {b} := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with hv' | hvb
          · exfalso
            exact ha (hv' ▸ hvS)
          · simpa using hvb
        · intro hv
          rcases Finset.mem_singleton.mp hv with rfl
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · simp
          · simpa using hb
      rw [hfilter]
      simp [ha, hb]
    · have hfilter :
          ({a, b} : Finset (Fin n)).filter (fun v ↦ v ∈ (S : Set (Fin n))) = ∅ := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_filter.mp hv with ⟨hv, hvS⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact (ha hvS).elim
          · exact (hb (by rw [Finset.mem_singleton.mp hv'] at hvS; exact hvS)).elim
        · intro hv
          simp at hv
      rw [hfilter]
      simp [ha, hb]

/-- Helper for Theorem 7.19: the endpoint finset of a complete-graph edge is the unordered pair
of its canonical `Sym2.out` endpoints. -/
private lemma completeGraphEdge_toFinset_eq_pair
    {n : ℕ} (e : complete_graph_edges n) :
    ((e : Sym2 (Fin n)).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the underlying `Sym2` edge by its canonical `out` representative.
  calc
    ((e : Sym2 (Fin n)).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simp [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Theorem 7.19: the filtered endpoint-cardinality of an edge is `2` for an
induced edge, `1` for a cut edge, and `0` otherwise. -/
private lemma endpointFilterCard_eq_induced_or_cut
    {n : ℕ} (S : Finset (Fin n))
    (e : complete_graph_edges n) :
    (((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ (S : Set (Fin n))).card : ℝ) =
      if e ∈ subtourInducedEdgeFinset S then 2
      else if e ∈ δ(S) then 1 else 0 := by
  -- First compute the filtered two-endpoint cardinality, then classify the endpoint cases.
  have hout_ne : e.1.out.1 ≠ e.1.out.2 := by
    intro hout_eq
    apply e.2
    rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
    exact hout_eq
  rw [completeGraphEdge_toFinset_eq_pair]
  rw [pairFilterCard_of_ne (a := e.1.out.1) (b := e.1.out.2) (hab := hout_ne) (S := S)]
  by_cases hfst : e.1.out.1 ∈ S
  · by_cases hsnd : e.1.out.2 ∈ S
    · have hind : e ∈ subtourInducedEdgeFinset S :=
        (mem_subtourInducedEdgeFinset_iff S e).2 ⟨hfst, hsnd⟩
      simp [hfst, hsnd, hind]
    · have hnotind : e ∉ subtourInducedEdgeFinset S := by
        intro hind
        exact hsnd ((mem_subtourInducedEdgeFinset_iff S e).1 hind).2
      have hcut : e ∈ δ(S) := by
        exact (mem_edge_boundary_finset_iff_out_endpoints S e).2 (Or.inl ⟨hfst, hsnd⟩)
      simp [hfst, hsnd, hnotind, hcut]
  · by_cases hsnd : e.1.out.2 ∈ S
    · have hnotind : e ∉ subtourInducedEdgeFinset S := by
        intro hind
        exact hfst ((mem_subtourInducedEdgeFinset_iff S e).1 hind).1
      have hcut : e ∈ δ(S) := by
        exact (mem_edge_boundary_finset_iff_out_endpoints S e).2 (Or.inr ⟨hsnd, hfst⟩)
      simp [hfst, hsnd, hnotind, hcut]
    · have hnotind : e ∉ subtourInducedEdgeFinset S := by
        intro hind
        exact hfst ((mem_subtourInducedEdgeFinset_iff S e).1 hind).1
      have hnotcut : e ∉ δ(S) := by
        intro hcut
        rcases (mem_edge_boundary_finset_iff_out_endpoints S e).1 hcut with
          (⟨h₁, _⟩ | ⟨h₂, _⟩)
        · exact hfst h₁
        · exact hsnd h₂
      simp [hfst, hsnd, hnotind, hnotcut]

/-- Helper for Theorem 7.19: the contribution of one edge to the summed degree equations on `S`
is `2 * x e` for induced edges, `x e` for cut edges, and `0` otherwise. -/
private lemma endpointContribution_eq_induced_and_cut
    {n : ℕ} (S : Finset (Fin n))
    (e : complete_graph_edges n)
    (x : complete_graph_edges n → ℝ) :
    Finset.sum S (fun v ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0) =
      (if e ∈ subtourInducedEdgeFinset S then 2 * x e else 0) +
        if e ∈ δ(S) then x e else 0 := by
  -- Rewrite the vertex sum as a constant sum over the filtered endpoint finset of `e`.
  calc
    Finset.sum S (fun v ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0) =
        Finset.sum (S.filter fun v ↦ v ∈ (e : Sym2 (Fin n))) (fun _ ↦ x e) := by
          rw [Finset.sum_filter]
    _ = Finset.sum (((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ (S : Set (Fin n))))
          (fun _ ↦ x e) := by
            rw [completeGraphEdgeFilter_eq_endpointFilter]
    _ = ((((e : Sym2 (Fin n)).toFinset.filter fun v ↦ v ∈ (S : Set (Fin n))).card : ℝ) * x e) := by
          simp [Finset.sum_const, mul_comm]
    _ = (if e ∈ subtourInducedEdgeFinset S then 2 * x e else 0) +
          if e ∈ δ(S) then x e else 0 := by
            rw [endpointFilterCard_eq_induced_or_cut]
            by_cases hind : e ∈ subtourInducedEdgeFinset S
            · have hnotcut : e ∉ δ(S) := not_mem_edgeBoundary_of_mem_induced S e hind
              simp [hind, hnotcut]
            · by_cases hcut : e ∈ δ(S)
              · simp [hind, hcut]
              · simp [hind, hcut]

/-- Helper for Theorem 7.19: summing the degree equations on a vertex set counts each induced
edge twice and each cut edge once. -/
private lemma sumIncidentEdgesOnSet_eq_twiceInducedEdges_add_subtour
    {n : ℕ} (S : Finset (Fin n))
    (x : complete_graph_edges n → ℝ) :
    Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset v).sum x) =
      2 * Finset.sum (subtourInducedEdgeFinset S) x +
        subtour_elimination_value S x := by
  -- Rewrite each degree sum as a complete-graph `if`-sum, then swap the vertex and edge sums.
  calc
    Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset v).sum x) =
        Finset.sum S (fun v ↦
          (Finset.univ : Finset (complete_graph_edges n)).sum
            (fun e ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          calc
            (completeGraphIncidentEdgeFinset v).sum x =
                (Finset.univ : Finset (complete_graph_edges n)).sum
                  (fun e ↦ if e ∈ completeGraphIncidentEdgeFinset v then x e else 0) := by
                  simp
            _ = (Finset.univ : Finset (complete_graph_edges n)).sum
                  (fun e ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  by_cases h : e ∈ completeGraphIncidentEdgeFinset v
                  · have hv' : v ∈ (e : Sym2 (Fin n)) :=
                      (mem_completeGraphIncidentEdgeFinset_iff (v := v) (e := e)).1 h
                    simp [h, hv']
                  · have hv' : v ∉ (e : Sym2 (Fin n)) := by
                      intro hv'
                      exact h ((mem_completeGraphIncidentEdgeFinset_iff (v := v) (e := e)).2 hv')
                    simp [h, hv']
    _ = (Finset.univ : Finset (complete_graph_edges n)).sum
          (fun e ↦ Finset.sum S (fun v ↦ if v ∈ (e : Sym2 (Fin n)) then x e else 0)) := by
          -- Swapping the vertex and edge sums isolates the contribution of each edge.
          rw [Finset.sum_comm]
    _ = ∑ e : complete_graph_edges n,
          ((if e ∈ subtourInducedEdgeFinset S then 2 * x e else 0) + if e ∈ δ(S) then x e else 0) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simpa using endpointContribution_eq_induced_and_cut (S := S) (e := e) (x := x)
    _ = (Finset.univ.filter fun e : complete_graph_edges n ↦ e ∈ subtourInducedEdgeFinset S).sum
          (fun e ↦ 2 * x e) +
          (Finset.univ.filter fun e : complete_graph_edges n ↦ e ∈ δ(S)).sum x := by
          rw [Finset.sum_add_distrib]
          congr 1
          · exact completeGraphSumIte_eq_sumFilter
              (p := fun e : complete_graph_edges n ↦ e ∈ subtourInducedEdgeFinset S)
              (f := fun e ↦ 2 * x e)
          · exact completeGraphSumIte_eq_sumFilter
              (p := fun e : complete_graph_edges n ↦ e ∈ δ(S))
              (f := x)
    _ = (subtourInducedEdgeFinset S).sum (fun e ↦ 2 * x e) +
          (δ(S)).sum x := by
          simp [subtourInducedEdgeFinset]
    _ = 2 * Finset.sum (subtourInducedEdgeFinset S) x +
          subtour_elimination_value S x := by
          rw [← Finset.mul_sum, subtour_elimination_value_eq]

/-- Helper for Theorem 7.19: summing the tour indicator over any edge finset counts exactly the
tour edges lying in that finset. -/
private theorem edgeIndicatorSum_eq_card_inter_of_tour
    {n : ℕ} (T : Finset (complete_graph_edges n))
    (σ : Equiv.Perm (Fin n)) :
    T.sum (hamiltonian_tour_incidence_vector σ) =
      (((T ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
  -- Rewrite the `0/1` Hamiltonian-tour indicator as the cardinality of the matching intersection.
  calc
    T.sum (hamiltonian_tour_incidence_vector σ) =
        T.sum (fun e ↦ if e ∈ hamiltonian_tour_edge_finset σ then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simp [hamiltonian_tour_incidence_vector, is_hamiltonian_tour_edge]
    _ = ((T.filter fun e ↦ e ∈ hamiltonian_tour_edge_finset σ).sum fun _ ↦ (1 : ℝ)) := by
          rw [Finset.sum_filter]
    _ = (((T.filter fun e ↦ e ∈ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
          simp
    _ = (((T ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
          have hfilter :
              T.filter (fun e ↦ e ∈ hamiltonian_tour_edge_finset σ) =
                T ∩ hamiltonian_tour_edge_finset σ := by
            ext e
            simp [Finset.mem_inter]
          rw [hfilter]

/-- Helper for Theorem 7.19: every Hamiltonian-tour vertex lies in the traveling-salesman degree
slice from Theorem 7.18. -/
private theorem hamiltonianTourIncidenceVector_mem_degreeConstraintSet
    {n : ℕ} (hn : 4 ≤ n) (σ : Equiv.Perm (Fin n)) :
    hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanDegreeConstraintSet n := by
  -- Move the Hamiltonian-tour vertex into the affine hull and then use the affine-hull
  -- description from Theorem 7.18.
  have hn3 : 3 ≤ n := by
    omega
  have hx_poly :
      hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanPolytope n := by
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self σ)
  have hx_aff :
      hamiltonian_tour_incidence_vector σ ∈ affineSpan ℝ (travelingSalesmanPolytope n) := by
    exact subset_affineSpan ℝ _ hx_poly
  have hspan :
      (affineSpan ℝ (travelingSalesmanPolytope n) : Set (complete_graph_edges n → ℝ)) =
        travelingSalesmanDegreeConstraintSet n := by
    simpa using affineSpan_travelingSalesmanPolytope_eq_degreeConstraintSet n hn3
  show hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanDegreeConstraintSet n
  rw [← hspan]
  exact hx_aff

/-- Helper for Theorem 7.19: on a Hamiltonian-tour vertex, the subtour value counts the tour
edges crossing the cut `δ(S)`. -/
private theorem subtourEliminationValue_eq_cutCard
    {n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    subtour_elimination_value S (hamiltonian_tour_incidence_vector σ) =
      (((δ(S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
  -- The generic tour-indicator/cardinality adapter closes the cut-count rewrite in one step.
  simpa [subtour_elimination_value_eq] using edgeIndicatorSum_eq_card_inter_of_tour (δ(S)) σ

/-- Helper for Theorem 7.19: on a Hamiltonian-tour vertex, the induced-edge sum counts the tour
edges whose endpoints both lie in `S`. -/
private theorem inducedEdgeSum_eq_inducedCard
    {n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    Finset.sum (subtourInducedEdgeFinset S) (hamiltonian_tour_incidence_vector σ) =
      (((subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
  -- The same tour-indicator/cardinality adapter also rewrites the induced-edge sum directly.
  simpa using edgeIndicatorSum_eq_card_inter_of_tour (subtourInducedEdgeFinset S) σ

/-- Helper for Theorem 7.19: every Hamiltonian-path edge also belongs to the corresponding
Hamiltonian tour once `n ≥ 2`. -/
private theorem hamiltonianPathEdge_mem_hamiltonianTourEdgeFinset
    {n : ℕ} (hn : 2 ≤ n)
    (σ : Equiv.Perm (Fin n))
    {e : complete_graph_edges n}
    (he : e ∈ hamiltonian_path_edge_finset σ) :
    e ∈ hamiltonian_tour_edge_finset σ := by
  -- For `n ≥ 2`, the tour owner is the path owner together with one closing edge.
  obtain ⟨m, hm_eq⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hm_eq
  subst hm_eq
  simpa [hamiltonian_tour_edge_finset] using
    (Finset.mem_insert.mpr (Or.inr he) :
      e ∈ insert (hamiltonian_tour_closing_edge σ) (hamiltonian_path_edge_finset σ))

/-- Helper for Theorem 7.19: if a consecutive Hamiltonian-path edge does not cross `δ(S)`, then
its two endpoints lie on the same side of the cut. -/
private theorem pathEdgeOfIndex_not_mem_boundary_iff_same_side
    {n : ℕ} (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n))
    (k : Fin (n - 1))
    (hnot : path_edge_of_index σ k ∉ δ(S)) :
    σ ⟨k.1, by
        have hk : k.1 < n - 1 := k.2
        omega⟩ ∈ S ↔
      σ ⟨k.1 + 1, by
        have hk : k.1 < n - 1 := k.2
        omega⟩ ∈ S := by
  constructor
  · intro hleft
    by_contra hright
    exact hnot ((mem_edge_boundary_finset_iff_mixed_endpoints S (path_edge_of_index σ k)).2
      ⟨σ ⟨k.1, by
          have hk : k.1 < n - 1 := k.2
          omega⟩,
        hleft,
        σ ⟨k.1 + 1, by
            have hk : k.1 < n - 1 := k.2
            omega⟩,
        hright,
        rfl⟩)
  · intro hright
    by_contra hleft
    exact hnot ((mem_edge_boundary_finset_iff_mixed_endpoints S (path_edge_of_index σ k)).2
      ⟨σ ⟨k.1 + 1, by
            have hk : k.1 < n - 1 := k.2
            omega⟩,
        hright,
        σ ⟨k.1, by
            have hk : k.1 < n - 1 := k.2
            omega⟩,
        hleft,
        Sym2.eq_swap.trans rfl⟩)

/-- Helper for Theorem 7.19: a nonempty proper vertex set meets at least one Hamiltonian-tour
edge, so the cut cardinality is positive. -/
private theorem hamiltonianTourCutCard_pos
    {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Fin n))
    (σ : Equiv.Perm (Fin n))
    (hS_nonempty : S.Nonempty)
    (hS_proper : S.card < n) :
    0 < (δ(S) ∩ hamiltonian_tour_edge_finset σ).card := by
  by_contra hzero
  have hzero' : (δ(S) ∩ hamiltonian_tour_edge_finset σ).card = 0 := Nat.eq_zero_of_not_pos hzero
  have hempty : δ(S) ∩ hamiltonian_tour_edge_finset σ = ∅ := Finset.card_eq_zero.mp hzero'
  let zero : Fin n := ⟨0, by omega⟩
  have hno_cut : ∀ k : Fin (n - 1), path_edge_of_index σ k ∉ δ(S) := by
    intro k hkcut
    have hpath :
        path_edge_of_index σ k ∈ hamiltonian_path_edge_finset σ := by
      simpa [is_hamiltonian_path_edge] using
        ((is_hamiltonian_path_edge_iff_exists_index σ (path_edge_of_index σ k)).2 ⟨k, rfl⟩)
    have htour :
        path_edge_of_index σ k ∈ hamiltonian_tour_edge_finset σ :=
      hamiltonianPathEdge_mem_hamiltonianTourEdgeFinset hn σ hpath
    have hmem :
        path_edge_of_index σ k ∈ δ(S) ∩ hamiltonian_tour_edge_finset σ := by
      simp [hkcut, htour]
    simp [hempty] at hmem
  have hsame :
      ∀ m : ℕ, ∀ hm : m < n, σ ⟨m, hm⟩ ∈ S ↔ σ zero ∈ S := by
    intro m
    induction m with
    | zero =>
        intro hm
        simp [zero]
    | succ m ih =>
        intro hm
        have hm' : m < n := by omega
        let k : Fin (n - 1) := ⟨m, by omega⟩
        have hstep :
            σ ⟨m, hm'⟩ ∈ S ↔ σ ⟨m + 1, hm⟩ ∈ S :=
          pathEdgeOfIndex_not_mem_boundary_iff_same_side S σ k (hno_cut k)
        exact hstep.symm.trans (ih hm')
  rcases hS_nonempty with ⟨u, hu⟩
  have houtside : ∃ v : Fin n, v ∉ S := by
    by_contra houtside
    push Not at houtside
    have hEq : S = Finset.univ := by
      ext v
      simp [houtside v]
    have hcard : S.card = n := by
      simp [hEq]
    exact (Nat.ne_of_lt hS_proper) hcard
  rcases houtside with ⟨v, hv⟩
  have hzero_mem : σ zero ∈ S := by
    have hu' : σ ⟨(σ.symm u).1, (σ.symm u).2⟩ ∈ S := by
      simpa using hu
    exact (hsame (σ.symm u).1 (σ.symm u).2).mp hu'
  have hv' : σ ⟨(σ.symm v).1, (σ.symm v).2⟩ ∈ S := by
    exact (hsame (σ.symm v).1 (σ.symm v).2).mpr hzero_mem
  exact hv (by simpa using hv')

/-- Helper for Theorem 7.19: a proper subtour set induces at most `|S| - 1` edges of a
Hamiltonian tour. -/
private lemma hamiltonianTourInducedEdgeCard_le_card_sub_one
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2)
    (σ : Equiv.Perm (Fin n)) :
    ((subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) ≤ S.card - 1 := by
  -- Route correction: instead of a direct cyclic injection, use the degree double-count identity
  -- together with positivity of the cut cardinality.
  have hS_nonempty : S.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  have hS_proper : S.card < n := by
    omega
  have hx_degree :
      hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanDegreeConstraintSet n :=
    hamiltonianTourIncidenceVector_mem_degreeConstraintSet hn σ
  have hx_degree' := mem_travelingSalesmanDegreeConstraintSet_iff.mp hx_degree
  have hdegree_sum :
      Finset.sum S
          (fun v ↦
            (completeGraphIncidentEdgeFinset v).sum
              (hamiltonian_tour_incidence_vector σ)) =
        2 * (S.card : ℝ) := by
    calc
      Finset.sum S
          (fun v ↦
            (completeGraphIncidentEdgeFinset v).sum
              (hamiltonian_tour_incidence_vector σ)) =
          ∑ v ∈ S, (2 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [completeGraphIncidentEdgeFinset_eq] using hx_degree' v
      _ = 2 * (S.card : ℝ) := by
            simp [mul_comm]
  have hcount :=
    sumIncidentEdgesOnSet_eq_twiceInducedEdges_add_subtour
      (S := S) (x := hamiltonian_tour_incidence_vector σ)
  rw [inducedEdgeSum_eq_inducedCard, subtourEliminationValue_eq_cutCard] at hcount
  have hcountCard :
      2 * (((subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) +
          (((δ(S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) =
        2 * (S.card : ℝ) := by
    linarith
  have hcountNat :
      2 * ((subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) +
          ((δ(S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) =
        2 * S.card := by
    exact_mod_cast hcountCard
  have hcutPos :
      0 < (δ(S) ∩ hamiltonian_tour_edge_finset σ).card :=
    hamiltonianTourCutCard_pos (hn := by omega) S σ hS_nonempty hS_proper
  omega

/-- Helper for Theorem 7.19: every Hamiltonian-tour vertex crosses a proper subtour cut at least
twice. -/
theorem hamiltonianTour_subtourElimination_ge_two
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2)
    (σ : Equiv.Perm (Fin n)) :
    2 ≤ subtour_elimination_value S (hamiltonian_tour_incidence_vector σ) := by
  -- Route correction: force a positive cut count first, then use the degree double-count identity
  -- to upgrade positivity to the even lower bound `2`.
  have hS_nonempty : S.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  have hS_proper : S.card < n := by
    omega
  have hx_degree :
      hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanDegreeConstraintSet n :=
    hamiltonianTourIncidenceVector_mem_degreeConstraintSet hn σ
  have hx_degree' := mem_travelingSalesmanDegreeConstraintSet_iff.mp hx_degree
  have hdegree_sum :
      Finset.sum S
          (fun v ↦
            (completeGraphIncidentEdgeFinset v).sum
              (hamiltonian_tour_incidence_vector σ)) =
        2 * (S.card : ℝ) := by
    calc
      Finset.sum S
          (fun v ↦
            (completeGraphIncidentEdgeFinset v).sum
              (hamiltonian_tour_incidence_vector σ)) =
          ∑ v ∈ S, (2 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [completeGraphIncidentEdgeFinset_eq] using hx_degree' v
      _ = 2 * (S.card : ℝ) := by
            simp [mul_comm]
  have hcount :=
    sumIncidentEdgesOnSet_eq_twiceInducedEdges_add_subtour
      (S := S) (x := hamiltonian_tour_incidence_vector σ)
  rw [inducedEdgeSum_eq_inducedCard, subtourEliminationValue_eq_cutCard] at hcount
  have hsubtourCard :
      2 * (((subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) +
          (((δ(S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) =
        2 * (S.card : ℝ) := by
    linarith
  have hsubtourCard_nat :
      2 * ((subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) +
          ((δ(S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) =
        2 * S.card := by
    exact_mod_cast hsubtourCard
  have hcutPos :
      0 < (δ(S) ∩ hamiltonian_tour_edge_finset σ).card :=
    hamiltonianTourCutCard_pos (hn := by omega) S σ hS_nonempty hS_proper
  have hcut_nat :
      2 ≤ ((δ(S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) := by
    omega
  have hcut :
      (2 : ℝ) ≤ (((δ(S) ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ) := by
    exact_mod_cast hcut_nat
  simpa [subtourEliminationValue_eq_cutCard] using hcut

/-- Theorem 7.19. For `S ⊆ V = Fin n` with `2 ≤ |S| ≤ n - 2`, the subtour-elimination
constraint `∑_{e ∈ δ(S)} x_e ≥ 2` is valid on the traveling salesman polytope on `n ≥ 4`
nodes. -/
theorem subtour_elimination_constraint_valid
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2)
    {x : complete_graph_edges n → ℝ}
    (hx : x ∈ travelingSalesmanPolytope n) :
    2 ≤ subtour_elimination_value S x := by
  let halfspace : Set (complete_graph_edges n → ℝ) :=
    {y | 2 ≤ subtour_elimination_value S y}
  have hhalfspace_convex : Convex ℝ halfspace := by
    let L : (complete_graph_edges n → ℝ) →ₗ[ℝ] ℝ := dotProductLinearMap (cutIncidenceVector S)
    have hhalfspace_eq : halfspace = L ⁻¹' Set.Ici (2 : ℝ) := by
      -- Rewrite the subtour inequality as a linear halfspace in the cut-incidence coordinates.
      ext y
      simp [halfspace, L, subtour_elimination_value_eq_dotProduct]
    rw [hhalfspace_eq]
    exact (convex_Ici (2 : ℝ)).linear_preimage L
  have hpoly_subset : travelingSalesmanPolytope n ⊆ halfspace := by
    rw [travelingSalesmanPolytope_eq_convexHull]
    refine convexHull_min ?_ hhalfspace_convex
    rintro y ⟨σ, rfl⟩
    -- Check the valid inequality on the generating Hamiltonian-tour vertices.
    exact hamiltonianTour_subtourElimination_ge_two hn S hS_lower hS_upper σ
  exact hpoly_subset hx

/-- The subtour-elimination inequality in the canonical Chapter 3 valid-inequality owner form. -/
theorem subtour_elimination_is_valid_inequality
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    is_valid_inequality (travelingSalesmanPolytope n) (-cutIncidenceVector S) (-2) := by
  rw [is_valid_inequality_iff]
  intro x hx
  have hvalid := subtour_elimination_constraint_valid hn S hS_lower hS_upper hx
  simpa [subtour_elimination_value_eq_dotProduct, dotProduct_neg] using neg_le_neg hvalid

/-- Helper for Theorem 7.19: the degree-constraint slice is convex because each vertex equation is
preserved by affine combinations. -/
private theorem travelingSalesmanDegreeConstraintSet_convex
    (n : ℕ) :
    Convex ℝ (travelingSalesmanDegreeConstraintSet n) := by
  intro x hx y hy a b ha hb hab
  rw [mem_travelingSalesmanDegreeConstraintSet_iff] at hx hy ⊢
  intro i
  calc
    ((incidentEdgeFinset (completeGraph (Fin n)) i).map
        completeGraphEdgeEquiv.symm.toEmbedding).sum (a • x + b • y)
        =
          a * ((incidentEdgeFinset (completeGraph (Fin n)) i).map
              completeGraphEdgeEquiv.symm.toEmbedding).sum x +
            b * ((incidentEdgeFinset (completeGraph (Fin n)) i).map
              completeGraphEdgeEquiv.symm.toEmbedding).sum y := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum,
              smul_eq_mul]
    _ = a * 2 + b * 2 := by rw [hx i, hy i]
    _ = 2 := by linarith

/-- Helper for Theorem 7.19: every point of the traveling salesman polytope lies in the ambient
degree-constraint slice. -/
private theorem travelingSalesmanPolytope_subset_degreeConstraintSet
    {n : ℕ}
    (hn : 4 ≤ n) :
    travelingSalesmanPolytope n ⊆ travelingSalesmanDegreeConstraintSet n := by
  -- The degree slice is convex, so it suffices to check the Hamiltonian-tour generators.
  rw [travelingSalesmanPolytope_eq_convexHull]
  refine convexHull_min ?_ (travelingSalesmanDegreeConstraintSet_convex n)
  rintro _ ⟨σ, rfl⟩
  exact hamiltonianTourIncidenceVector_mem_degreeConstraintSet hn σ

/-- Helper for Theorem 7.19: every point of the traveling salesman polytope satisfies the degree
double-count identity `2 * x(E[S]) + x(δ(S)) = 2 |S|`. -/
private theorem inducedEdgeSum_two_mul_add_subtour_eq_two_card
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    {x : complete_graph_edges n → ℝ}
    (hx : x ∈ travelingSalesmanPolytope n) :
    2 * Finset.sum (subtourInducedEdgeFinset S) x + subtour_elimination_value S x =
      2 * (S.card : ℝ) := by
  -- Move `x` into the degree slice, sum the degree equations on `S`, and then rewrite the left
  -- side with the induced-edge/cut double-count identity.
  have hx_degree :
      x ∈ travelingSalesmanDegreeConstraintSet n := by
    exact travelingSalesmanPolytope_subset_degreeConstraintSet (hn := hn) hx
  have hx_degree' := mem_travelingSalesmanDegreeConstraintSet_iff.mp hx_degree
  have hdegree_sum :
      Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset v).sum x) =
        2 * (S.card : ℝ) := by
    calc
      Finset.sum S (fun v ↦ (completeGraphIncidentEdgeFinset v).sum x) =
          ∑ v ∈ S, (2 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa [completeGraphIncidentEdgeFinset_eq] using hx_degree' v
      _ = 2 * (S.card : ℝ) := by
            simp [mul_comm]
  have hcount :=
    sumIncidentEdgesOnSet_eq_twiceInducedEdges_add_subtour (S := S) (x := x)
  linarith

/-- Helper for Theorem 7.19: on the traveling salesman polytope, the subtour equality
`x(δ(S)) = 2` is equivalent to the induced-edge equality `x(E[S]) = |S| - 1`. -/
private theorem mem_subtour_elimination_face_iff_inducedEdgeSum_eq_card_sub_one
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (x : complete_graph_edges n → ℝ) :
    x ∈ subtour_elimination_face n S ↔
      x ∈ travelingSalesmanPolytope n ∧
        Finset.sum (subtourInducedEdgeFinset S) x = (S.card : ℝ) - 1 := by
  constructor
  · rintro ⟨hx, hface⟩
    have hcount :
        2 * Finset.sum (subtourInducedEdgeFinset S) x + subtour_elimination_value S x =
          2 * (S.card : ℝ) :=
      inducedEdgeSum_two_mul_add_subtour_eq_two_card (hn := hn) S hx
    refine ⟨hx, ?_⟩
    linarith
  · rintro ⟨hx, hinduced⟩
    have hcount :
        2 * Finset.sum (subtourInducedEdgeFinset S) x + subtour_elimination_value S x =
          2 * (S.card : ℝ) :=
      inducedEdgeSum_two_mul_add_subtour_eq_two_card (hn := hn) S hx
    refine ⟨hx, ?_⟩
    linarith

/-- Helper for Theorem 7.19: the induced-edge coordinate sum on `E[S]` as a linear map. -/
private def subtourInducedSumLinearMap
    {n : ℕ} (S : Finset (Fin n)) :
    (complete_graph_edges n → ℝ) →ₗ[ℝ] ℝ :=
  Finset.sum (subtourInducedEdgeFinset S) fun e ↦ (ContinuousLinearMap.proj e).toLinearMap

/-- Helper for Theorem 7.19: the induced-edge sum linear map evaluates as the expected finite
sum over `E[S]`. -/
private theorem subtourInducedSumLinearMap_apply
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    subtourInducedSumLinearMap S x = Finset.sum (subtourInducedEdgeFinset S) x := by
  -- Expanding the finite sum of coordinate projections recovers the induced-edge sum.
  simp [subtourInducedSumLinearMap]

/-- Helper for Theorem 7.19: the cut functional `x ↦ (-χ^{δ(S)}) · x` as a strong-dual element. -/
private noncomputable def subtourCutStrongDual
    {n : ℕ} (S : Finset (Fin n)) :
    StrongDual ℝ (complete_graph_edges n → ℝ) :=
  ∑ e, (-cutIncidenceVector S e) • ContinuousLinearMap.proj e

/-- Helper for Theorem 7.19: the strong-dual cut functional evaluates as the expected dot
product with `-cutIncidenceVector S`. -/
private theorem subtourCutStrongDual_apply
    {n : ℕ} (S : Finset (Fin n)) (x : complete_graph_edges n → ℝ) :
    subtourCutStrongDual S x = (-cutIncidenceVector S) ⬝ᵥ x := by
  -- Expanding the strong-dual coordinate sum gives the canonical dot-product formula.
  simp [subtourCutStrongDual, dotProduct]

/-- Helper for Theorem 7.19: the concrete complete-graph edge on two distinct vertices. -/
private theorem completeGraphEdge_not_isDiag
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ¬ (s(i, j) : Sym2 (Fin n)).IsDiag := by
  -- Distinct endpoints define a genuine complete-graph edge coordinate.
  rw [Sym2.mk_isDiag_iff]
  exact hij

/-- Helper for Theorem 7.19: the complete-graph edge joining two distinct vertices. -/
private def completeGraphEdgeBetween
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) : complete_graph_edges n :=
  ⟨s(i, j), completeGraphEdge_not_isDiag hij⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: two concrete edges differ when neither direct nor swapped endpoint matching is possible. -/
private theorem completeGraphEdgeBetween_ne
    {n : ℕ} {u v x y : Fin n}
    (huv : u ≠ v) (hxy : x ≠ y)
    (hdirect : u ≠ x ∨ v ≠ y) (hswap : u ≠ y ∨ v ≠ x) :
    completeGraphEdgeBetween u v huv ≠ completeGraphEdgeBetween x y hxy := by
  -- Equality of unordered pairs has only the direct and swapped endpoint alternatives.
  intro hedge
  have hval := congrArg Subtype.val hedge
  change s(u, v) = s(x, y) at hval
  rcases (Sym2.eq_iff.mp hval) with h | h
  · rcases hdirect with hux | hvy
    · exact hux h.1
    · exact hvy h.2
  · rcases hswap with huy | hvx
    · exact huy h.1
    · exact hvx h.2

/-- Helper for Theorem 7.19: the concrete edge `{i,j}` is incident to `v` exactly when `v` is
one of its endpoints. -/
private theorem mem_completeGraphIncidentEdgeFinset_edgeBetween_iff
    {n : ℕ} {i j v : Fin n} (hij : i ≠ j) :
    completeGraphEdgeBetween i j hij ∈ completeGraphIncidentEdgeFinset v ↔ v = i ∨ v = j := by
  -- Unfold the concrete edge and read membership in the unordered pair `{i,j}`.
  rw [mem_completeGraphIncidentEdgeFinset_iff, completeGraphEdgeBetween]
  simp [Sym2.mem_iff, eq_comm]

/-- Helper for Theorem 7.19: the concrete edge `{u,v}` is induced by `S` exactly when both
endpoints lie in `S`. -/
private theorem completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff
    {n : ℕ} (S : Finset (Fin n))
    {u v : Fin n} (huv : u ≠ v) :
    completeGraphEdgeBetween u v huv ∈ subtourInducedEdgeFinset S ↔ u ∈ S ∧ v ∈ S := by
  constructor
  · intro hmem
    rw [subtourInducedEdgeFinset, Finset.mem_filter] at hmem
    rw [completeGraphEdgeBetween, completeGraphEdge_coe,
      SimpleGraph.Subgraph.mem_edgeSet] at hmem
    simpa [SimpleGraph.Subgraph.induce, huv] using hmem.2
  · intro huvS
    rw [subtourInducedEdgeFinset, Finset.mem_filter]
    refine ⟨by simp, ?_⟩
    rw [completeGraphEdgeBetween, completeGraphEdge_coe,
      SimpleGraph.Subgraph.mem_edgeSet]
    simpa [SimpleGraph.Subgraph.induce, huv] using huvS

/-- Helper for Theorem 7.19: summing a basis edge over the incident-edge owner returns the
corresponding endpoint indicator. -/
private theorem completeGraphIncidentEdgeFinset_sum_basisFun
    {n : ℕ} (v : Fin n) (e : complete_graph_edges n) :
    (completeGraphIncidentEdgeFinset v).sum (Pi.basisFun ℝ (complete_graph_edges n) e) =
      if e ∈ completeGraphIncidentEdgeFinset v then 1 else 0 := by
  -- The basis function contributes only when its coordinate lies in the filtered owner.
  by_cases he : e ∈ completeGraphIncidentEdgeFinset v
  · simp [Pi.basisFun, he]
  · simp [Pi.basisFun, he]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: summing a finite coordinate-basis expansion over another finite set reduces to coordinate indicators. -/
private theorem finsetSum_basisExpansion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I A : Finset ι) (r : ι → ℝ) :
    I.sum (∑ e ∈ A, r e • Pi.basisFun ℝ ι e) =
      ∑ e ∈ A, r e * if e ∈ I then 1 else 0 := by
  -- Swap the two finite sums and evaluate each basis vector on the selected coordinates.
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [← Finset.mul_sum]
  by_cases heI : e ∈ I
  · simp [Pi.basisFun, heI]
  · simp [Pi.basisFun, heI]

/-- Helper for Theorem 7.19: the basic four-edge exchange vector supported on
`{ab, ij, ai, bj}`. -/
private def fourEdgeExchangeVector
    {n : ℕ} (eab eij eai ebj : complete_graph_edges n) :
    complete_graph_edges n → ℝ :=
  Pi.basisFun ℝ (complete_graph_edges n) eab +
    Pi.basisFun ℝ (complete_graph_edges n) eij -
      Pi.basisFun ℝ (complete_graph_edges n) eai -
        Pi.basisFun ℝ (complete_graph_edges n) ebj

/-- Helper for Theorem 7.19: the four-edge exchange has zero incident-edge sum at every vertex. -/
private theorem fourEdgeExchange_zeroIncidentSum
    {n : ℕ} {a b i j : Fin n}
    (hab : a ≠ b) (hij : i ≠ j) (hai : a ≠ i) (hbj : b ≠ j) (hbi : b ≠ i) (haj : a ≠ j) :
    let eab : complete_graph_edges n := completeGraphEdgeBetween a b hab
    let eij : complete_graph_edges n := completeGraphEdgeBetween i j hij
    let eai : complete_graph_edges n := completeGraphEdgeBetween a i hai
    let ebj : complete_graph_edges n := completeGraphEdgeBetween b j hbj
    let w : complete_graph_edges n → ℝ := fourEdgeExchangeVector eab eij eai ebj
    ∀ v : Fin n, (completeGraphIncidentEdgeFinset v).sum w = 0 := by
  intro eab eij eai ebj w v
  -- Split on which of the four exchange vertices `v` is; elsewhere every contribution vanishes.
  by_cases hva : v = a
  · subst v
    calc
      (completeGraphIncidentEdgeFinset a).sum w
          = (completeGraphIncidentEdgeFinset a).sum
              (Pi.basisFun ℝ (complete_graph_edges n) eab) +
            (completeGraphIncidentEdgeFinset a).sum
              (Pi.basisFun ℝ (complete_graph_edges n) eij) -
            (completeGraphIncidentEdgeFinset a).sum
              (Pi.basisFun ℝ (complete_graph_edges n) eai) -
            (completeGraphIncidentEdgeFinset a).sum
              (Pi.basisFun ℝ (complete_graph_edges n) ebj) := by
              simp [w, fourEdgeExchangeVector, Finset.sum_add_distrib, sub_eq_add_neg,
                add_assoc]
      _ = 0 := by
            simp [mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, eab, eij, eai, ebj,
              hab, hai, haj]
  · by_cases hvb : v = b
    · subst v
      calc
        (completeGraphIncidentEdgeFinset b).sum w
            = (completeGraphIncidentEdgeFinset b).sum
                (Pi.basisFun ℝ (complete_graph_edges n) eab) +
              (completeGraphIncidentEdgeFinset b).sum
                (Pi.basisFun ℝ (complete_graph_edges n) eij) -
              (completeGraphIncidentEdgeFinset b).sum
                (Pi.basisFun ℝ (complete_graph_edges n) eai) -
              (completeGraphIncidentEdgeFinset b).sum
                (Pi.basisFun ℝ (complete_graph_edges n) ebj) := by
                simp [w, fourEdgeExchangeVector, Finset.sum_add_distrib, sub_eq_add_neg,
                  add_assoc]
        _ = 0 := by
              simp [mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, eab, eij, eai, ebj,
                hbj, hbi, hva]
    · by_cases hvi : v = i
      · subst v
        calc
          (completeGraphIncidentEdgeFinset i).sum w
              = (completeGraphIncidentEdgeFinset i).sum
                  (Pi.basisFun ℝ (complete_graph_edges n) eab) +
                (completeGraphIncidentEdgeFinset i).sum
                  (Pi.basisFun ℝ (complete_graph_edges n) eij) -
                (completeGraphIncidentEdgeFinset i).sum
                  (Pi.basisFun ℝ (complete_graph_edges n) eai) -
                (completeGraphIncidentEdgeFinset i).sum
                  (Pi.basisFun ℝ (complete_graph_edges n) ebj) := by
                  simp [w, fourEdgeExchangeVector, Finset.sum_add_distrib, sub_eq_add_neg,
                    add_assoc]
          _ = 0 := by
                simp [mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, eab, eij, eai, ebj,
                  hij, hva, hvb]
      · by_cases hvj : v = j
        · subst v
          calc
            (completeGraphIncidentEdgeFinset j).sum w
                = (completeGraphIncidentEdgeFinset j).sum
                    (Pi.basisFun ℝ (complete_graph_edges n) eab) +
                  (completeGraphIncidentEdgeFinset j).sum
                    (Pi.basisFun ℝ (complete_graph_edges n) eij) -
                  (completeGraphIncidentEdgeFinset j).sum
                    (Pi.basisFun ℝ (complete_graph_edges n) eai) -
                  (completeGraphIncidentEdgeFinset j).sum
                    (Pi.basisFun ℝ (complete_graph_edges n) ebj) := by
                    simp [w, fourEdgeExchangeVector, Finset.sum_add_distrib, sub_eq_add_neg,
                      add_assoc]
            _ = 0 := by
                  simp [mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, eab, eij, eai, ebj,
                    hva, hvb, hvi]
        · calc
            (completeGraphIncidentEdgeFinset v).sum w
                = (completeGraphIncidentEdgeFinset v).sum
                    (Pi.basisFun ℝ (complete_graph_edges n) eab) +
                  (completeGraphIncidentEdgeFinset v).sum
                    (Pi.basisFun ℝ (complete_graph_edges n) eij) -
                  (completeGraphIncidentEdgeFinset v).sum
                    (Pi.basisFun ℝ (complete_graph_edges n) eai) -
                  (completeGraphIncidentEdgeFinset v).sum
                    (Pi.basisFun ℝ (complete_graph_edges n) ebj) := by
                    simp [w, fourEdgeExchangeVector, Finset.sum_add_distrib, sub_eq_add_neg,
                      add_assoc]
            _ = 0 := by
                  simp [mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, eab, eij, eai, ebj,
                    hva, hvb, hvi, hvj]

/-- Helper for Theorem 7.19: every four-edge exchange vector lies in the ambient TSP direction. -/
private theorem fourEdgeExchange_mem_ambientDirection
    {n : ℕ}
    (hn : 4 ≤ n)
    {a b i j : Fin n}
    (hab : a ≠ b) (hij : i ≠ j) (hai : a ≠ i) (hbj : b ≠ j) (hbi : b ≠ i) (haj : a ≠ j) :
    let eab : complete_graph_edges n := completeGraphEdgeBetween a b hab
    let eij : complete_graph_edges n := completeGraphEdgeBetween i j hij
    let eai : complete_graph_edges n := completeGraphEdgeBetween a i hai
    let ebj : complete_graph_edges n := completeGraphEdgeBetween b j hbj
    let w : complete_graph_edges n → ℝ := fourEdgeExchangeVector eab eij eai ebj
    w ∈ (affineSpan ℝ (travelingSalesmanPolytope n)).direction := by
  intro eab eij eai ebj w
  let x0 : complete_graph_edges n → ℝ := hamiltonian_tour_incidence_vector (Equiv.refl (Fin n))
  have hx0_poly : x0 ∈ travelingSalesmanPolytope n := by
    -- Any Hamiltonian-tour vertex already lies in the traveling salesman polytope.
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self (Equiv.refl (Fin n)))
  have hx0_aff : x0 ∈ affineSpan ℝ (travelingSalesmanPolytope n) := by
    exact subset_affineSpan ℝ _ hx0_poly
  have hspan :
      (affineSpan ℝ (travelingSalesmanPolytope n) : Set (complete_graph_edges n → ℝ)) =
        travelingSalesmanDegreeConstraintSet n := by
    have hn3 : 3 ≤ n := by
      omega
    simpa using affineSpan_travelingSalesmanPolytope_eq_degreeConstraintSet n hn3
  have hx0_degree : x0 ∈ travelingSalesmanDegreeConstraintSet n := by
    rw [← hspan]
    exact hx0_aff
  have hx0_incident_sum :
      ∀ v : Fin n, (completeGraphIncidentEdgeFinset v).sum x0 = 2 := by
    intro v
    -- Move the public degree equation to the local incident-edge owner once.
    rw [completeGraphIncidentEdgeFinset_eq]
    exact (mem_travelingSalesmanDegreeConstraintSet_iff.mp hx0_degree) v
  have hw_incident_zero :
      ∀ v : Fin n, (completeGraphIncidentEdgeFinset v).sum w = 0 := by
    -- The exchange preserves every degree equation because each involved vertex sees one `+1`
    -- edge and one `-1` edge.
    simpa [w] using
      fourEdgeExchange_zeroIncidentSum (a := a) (b := b) (i := i) (j := j)
        hab hij hai hbj hbi haj
  have hw_aff : x0 + w ∈ affineSpan ℝ (travelingSalesmanPolytope n) := by
    have hw_degree : x0 + w ∈ travelingSalesmanDegreeConstraintSet n := by
      rw [mem_travelingSalesmanDegreeConstraintSet_iff]
      intro v
      rw [← completeGraphIncidentEdgeFinset_eq]
      -- The exchange vector has zero incident sum at every vertex, so it preserves the degree
      -- slice.
      calc
        (completeGraphIncidentEdgeFinset v).sum (x0 + w)
            = (completeGraphIncidentEdgeFinset v).sum x0 +
                (completeGraphIncidentEdgeFinset v).sum w := by
                  simp [Finset.sum_add_distrib]
        _ = 2 + 0 := by rw [hx0_incident_sum v, hw_incident_zero v]
        _ = 2 := by norm_num
    change x0 + w ∈ (affineSpan ℝ (travelingSalesmanPolytope n) :
      Set (complete_graph_edges n → ℝ))
    exact hspan.symm ▸ hw_degree
  have hvsub :
      (x0 + w) - x0 ∈ (affineSpan ℝ (travelingSalesmanPolytope n)).direction := by
    -- Two points of the ambient affine hull determine a direction vector by subtraction.
    exact AffineSubspace.vsub_mem_direction hw_aff hx0_aff
  have hdiff : (x0 + w) - x0 = w := by
    abel
  rw [hdiff] at hvsub
  exact hvsub

/-- Helper for Theorem 7.19: the ambient TSP direction contains a vector on which the
induced-edge sum on `E[S]` evaluates to `1`. -/
private theorem existsAmbientDirectionEvalOne_subtourInducedSum
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    ∃ w : complete_graph_edges n → ℝ,
      w ∈ (affineSpan ℝ (travelingSalesmanPolytope n)).direction ∧
        subtourInducedSumLinearMap S w = 1 := by
  classical
  let Sc : Finset (Fin n) := Sᶜ
  have hS_nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hS_nonempty
  have hS_erase_nonempty : (S.erase a).Nonempty := by
    exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha]; omega)
  obtain ⟨b, hb_erase⟩ := hS_erase_nonempty
  have hb : b ∈ S := (Finset.mem_erase.mp hb_erase).2
  have hab : a ≠ b := by
    exact (Finset.mem_erase.mp hb_erase).1.symm
  have hSc_card : Sc.card = n - S.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hSc_lower : 2 ≤ Sc.card := by
    rw [hSc_card]
    omega
  have hSc_nonempty : Sc.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hiSc⟩ := hSc_nonempty
  have hi : i ∉ S := by
    simpa [Sc] using hiSc
  have hSc_erase_nonempty : (Sc.erase i).Nonempty := by
    exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hiSc]; omega)
  obtain ⟨j, hjSc_erase⟩ := hSc_erase_nonempty
  have hjSc : j ∈ Sc := (Finset.mem_erase.mp hjSc_erase).2
  have hj : j ∉ S := by
    simpa [Sc] using hjSc
  have hij : i ≠ j := by
    exact (Finset.mem_erase.mp hjSc_erase).1.symm
  have hai : a ≠ i := by
    intro h
    exact hi (h ▸ ha)
  have haj : a ≠ j := by
    intro h
    exact hj (h ▸ ha)
  have hbi : b ≠ i := by
    intro h
    exact hi (h ▸ hb)
  have hbj : b ≠ j := by
    intro h
    exact hj (h ▸ hb)
  let eab : complete_graph_edges n := completeGraphEdgeBetween a b hab
  let eij : complete_graph_edges n := completeGraphEdgeBetween i j hij
  let eai : complete_graph_edges n := completeGraphEdgeBetween a i hai
  let ebj : complete_graph_edges n := completeGraphEdgeBetween b j hbj
  let w : complete_graph_edges n → ℝ := fourEdgeExchangeVector eab eij eai ebj
  have hw_dir : w ∈ (affineSpan ℝ (travelingSalesmanPolytope n)).direction := by
    -- The reusable four-edge exchange helper already packages the ambient degree-slice argument.
    simpa [w] using
      fourEdgeExchange_mem_ambientDirection hn (a := a) (b := b) (i := i) (j := j)
        hab hij hai hbj hbi haj
  have heab_induced : eab ∈ subtourInducedEdgeFinset S := by
    -- Both endpoints of `ab` lie in `S`, so that edge contributes to the induced sum.
    exact (completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff S hab).2 ⟨ha, hb⟩
  have heij_not_induced : eij ∉ subtourInducedEdgeFinset S := by
    -- An edge with both endpoints outside `S` cannot belong to `E[S]`.
    intro heij_induced
    exact hi ((completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff S hij).1 heij_induced).1
  have heai_not_induced : eai ∉ subtourInducedEdgeFinset S := by
    -- A cut edge does not belong to the induced-edge owner.
    intro heai_induced
    exact hi ((completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff S hai).1 heai_induced).2
  have hebj_not_induced : ebj ∉ subtourInducedEdgeFinset S := by
    -- The second cut edge is excluded for the same reason.
    intro hebj_induced
    exact hj ((completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff S hbj).1 hebj_induced).2
  have hw_eval : subtourInducedSumLinearMap S w = 1 := by
    -- On the induced-edge sum, only the internal edge `ab` survives.
    rw [subtourInducedSumLinearMap_apply]
    simp [w, fourEdgeExchangeVector, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Pi.basisFun, heab_induced, heij_not_induced, heai_not_induced, hebj_not_induced]
  exact ⟨w, hw_dir, hw_eval⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: every tour whose shore vertices occupy the initial block is tight for the subtour face. -/
private theorem blockOrderedTour_mem_subtourFace
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < S.card) :
    hamiltonian_tour_incidence_vector σ ∈ subtour_elimination_face n S := by
  classical
  have hS_le_n : S.card ≤ n := by
    simpa [Fintype.card_fin] using (Finset.card_le_univ S)
  let initialEdges : Finset (complete_graph_edges n) :=
    Finset.univ.image fun k : Fin (S.card - 1) ↦
      path_edge_of_index σ ⟨k.1, by
        have hk : k.1 < S.card - 1 := k.2
        omega⟩
  have hinitial_subset :
      initialEdges ⊆ subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ := by
    intro e he
    rw [Finset.mem_image] at he
    rcases he with ⟨k, -, rfl⟩
    let k' : Fin (n - 1) := ⟨k.1, by
      have hk : k.1 < S.card - 1 := k.2
      omega⟩
    let left : Fin n := ⟨k'.1, by
      have hk : k'.1 < n - 1 := k'.2
      omega⟩
    let right : Fin n := ⟨k'.1 + 1, by
      have hk : k'.1 < n - 1 := k'.2
      omega⟩
    have hk_lt_card : (k : ℕ) < S.card := by
      have hk : k.1 < S.card - 1 := k.2
      omega
    have hk_succ_lt_card : (k : ℕ) + 1 < S.card := by
      have hk : k.1 < S.card - 1 := k.2
      omega
    have hleft_mem : σ left ∈ S := by
      -- Positions strictly before the block boundary correspond to vertices of `S`.
      exact (hσ _).2 (by simpa [left, k'] using hk_lt_card)
    have hright_mem : σ right ∈ S := by
      -- The next position is still inside the same block, so it also lies in `S`.
      exact (hσ _).2 (by simpa [right, k'] using hk_succ_lt_card)
    have hpath :
        path_edge_of_index σ k' ∈ hamiltonian_path_edge_finset σ := by
      -- Each consecutive edge appears in the Hamiltonian path by its defining index.
      simpa [is_hamiltonian_path_edge] using
        ((is_hamiltonian_path_edge_iff_exists_index σ (path_edge_of_index σ k')).2 ⟨k', rfl⟩)
    have htour :
        path_edge_of_index σ k' ∈ hamiltonian_tour_edge_finset σ :=
      hamiltonianPathEdge_mem_hamiltonianTourEdgeFinset (hn := by omega) σ hpath
    have hinduced : path_edge_of_index σ k' ∈ subtourInducedEdgeFinset S := by
      -- Both endpoints lie in `S`, so the path edge is induced by `S`.
      have hadj : (completeGraph (Fin n)).Adj (σ left) (σ right) := by
        have he : s(σ left, σ right) ∈ (completeGraph (Fin n)).edgeSet := by
          simp [left, right]
        exact (SimpleGraph.mem_edgeSet
          (G := completeGraph (Fin n)) (v := σ left) (w := σ right)).1 he
      have hleft_right_ne : left ≠ right := by
        intro h
        have hval : left.1 = right.1 := congrArg Fin.val h
        simp [left, right] at hval
      rw [subtourInducedEdgeFinset, Finset.mem_filter]
      refine ⟨by simp, ?_⟩
      rw [completeGraphEdge_coe, path_edge_of_index,
        SimpleGraph.Subgraph.mem_edgeSet]
      simpa [SimpleGraph.Subgraph.induce, left, right, hadj] using
        ⟨hleft_mem, hright_mem, hleft_right_ne⟩
    exact Finset.mem_inter.mpr ⟨hinduced, htour⟩
  have hinitial_card : initialEdges.card = S.card - 1 := by
    -- Distinct initial positions give distinct path edges, so the image has the expected size.
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      apply Fin.ext
      have hcast :
          (⟨a.1, by
              have ha : a.1 < S.card - 1 := a.2
              omega⟩ : Fin (n - 1)) =
            ⟨b.1, by
              have hb : b.1 < S.card - 1 := b.2
              omega⟩ := by
        exact path_edge_of_index_injective σ hab
      simpa using congrArg Fin.val hcast
  have hinitial_le :
      S.card - 1 ≤ (subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ).card := by
    -- The initial block edges inject into the induced tour edges, giving the lower bound.
    rw [← hinitial_card]
    exact Finset.card_le_card hinitial_subset
  have hupper :
      ((subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) ≤ S.card - 1 :=
    hamiltonianTourInducedEdgeCard_le_card_sub_one hn S hS_lower hS_upper σ
  have hinduced_card :
      (subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ).card = S.card - 1 := by
    omega
  have hpoly :
      hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanPolytope n := by
    -- Every Hamiltonian tour incidence vector is one of the generating TSP vertices.
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self σ)
  have hinduced_eq :
      Finset.sum (subtourInducedEdgeFinset S) (hamiltonian_tour_incidence_vector σ) =
        (S.card : ℝ) - 1 := by
    -- The induced-edge count on the block-ordered tour is exactly `|S| - 1`.
    rw [inducedEdgeSum_eq_inducedCard]
    have hS_one_le : 1 ≤ S.card := by
      omega
    calc
      (((subtourInducedEdgeFinset S ∩ hamiltonian_tour_edge_finset σ).card : ℕ) : ℝ)
          = ((S.card - 1 : ℕ) : ℝ) := by
              exact_mod_cast hinduced_card
      _ = (S.card : ℝ) - 1 := by
            calc
              ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - ((1 : ℕ) : ℝ) := by
                exact Nat.cast_sub hS_one_le
              _ = (S.card : ℝ) - 1 := by norm_num
  exact (mem_subtour_elimination_face_iff_inducedEdgeSum_eq_card_sub_one (hn := hn) S
    (hamiltonian_tour_incidence_vector σ)).2 ⟨hpoly, hinduced_eq⟩


/-- Helper for Theorem 7.19: ordering the vertices so that the `S`-vertices form one contiguous
block produces a Hamiltonian tour tight for the subtour face. -/
private theorem existsTightSubtourTour
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    ∃ σ : Equiv.Perm (Fin n), hamiltonian_tour_incidence_vector σ ∈ subtour_elimination_face n S := by
  classical
  rcases exists_block_order_permutation S with ⟨π, hπ⟩
  let σ : Equiv.Perm (Fin n) := π.symm
  refine ⟨σ, blockOrderedTour_mem_subtourFace hn S hS_lower hS_upper σ ?_⟩
  intro t
  -- Inverting the block-order permutation turns its membership test into an initial-segment test.
  simpa [σ] using hπ (σ t)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: every independently permuted two-block tour is tight for the subtour face. -/
private theorem subtourBlockTour_mem_face
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (ρ₁ : Equiv.Perm (Fin p)) (ρ₂ : Equiv.Perm (Fin (n - p))) :
    hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) ∈
      subtour_elimination_face n S := by
  have hp : p ≤ n := by omega
  have hpositionFilter :
      Finset.univ.filter (fun t : Fin n ↦ (t : ℕ) < p) =
        Finset.univ.map (Fin.castLEEmb hp) := by
    -- The initial block is precisely the image of `Fin p` in `Fin n`.
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro ht
      refine ⟨⟨t, ht⟩, ?_⟩
      exact Fin.ext rfl
    · rintro ⟨i, rfl⟩
      exact i.2
  have hshorePreimage :
      Finset.univ.filter (fun t : Fin n ↦ σ t ∈ S) = S.map σ.symm.toEmbedding := by
    -- Pulling the shore back along the tour enumeration preserves its cardinality.
    ext t
    simp
  have hcard : S.card = p := by
    -- The membership characterization identifies `S` with exactly the first `p` positions.
    calc
      S.card = (S.map σ.symm.toEmbedding).card := by rw [Finset.card_map]
      _ = (Finset.univ.filter (fun t : Fin n ↦ σ t ∈ S)).card := by rw [hshorePreimage]
      _ = (Finset.univ.filter (fun t : Fin n ↦ (t : ℕ) < p)).card := by
        congr 1
        ext t
        simp [hσ]
      _ = (Finset.univ.map (Fin.castLEEmb hp)).card := by rw [hpositionFilter]
      _ = p := by simp
  apply blockOrderedTour_mem_subtourFace hn S (by simpa [hcard] using hpLower)
    (by simpa [hcard] using hpUpper)
  intro t
  -- The generic block permutation preserves the same initial-segment membership test.
  simpa [hcard] using subtourBlockTourPerm_mem_iff hp S σ hσ ρ₁ ρ₂ t

/-- Helper for Theorem 7.19: the subtour-face direction lies in the ambient TSP direction and in
the kernel of the normalized induced-edge sum. -/
private theorem subtourFaceDirection_le_ambientDirection_inf_inducedKer
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    (affineSpan ℝ (subtour_elimination_face n S)).direction ≤
      (affineSpan ℝ (travelingSalesmanPolytope n)).direction ⊓
        LinearMap.ker (subtourInducedSumLinearMap S) := by
  rcases existsTightSubtourTour hn S hS_lower hS_upper with ⟨σ, hσ_face⟩
  have hface_subset :
      subtour_elimination_face n S ⊆ travelingSalesmanPolytope n := by
    intro x hx
    exact (mem_subtour_elimination_face_iff S x).1 hx |>.1
  have hdir_ambient :
      (affineSpan ℝ (subtour_elimination_face n S)).direction ≤
        (affineSpan ℝ (travelingSalesmanPolytope n)).direction := by
    -- Every face direction is in particular an ambient TSP direction.
    exact AffineSubspace.direction_le (affineSpan_mono ℝ hface_subset)
  have hlevel :
      ∀ ⦃x : complete_graph_edges n → ℝ⦄,
        x ∈ subtour_elimination_face n S → subtourInducedSumLinearMap S x = (S.card : ℝ) - 1 := by
    intro x hx
    -- On the face, the normalized induced-edge sum is fixed at `|S| - 1`.
    simpa [subtourInducedSumLinearMap_apply] using
      (mem_subtour_elimination_face_iff_inducedEdgeSum_eq_card_sub_one (hn := hn) S x).1 hx |>.2
  have hdir_ker :
      (affineSpan ℝ (subtour_elimination_face n S)).direction ≤
        LinearMap.ker (subtourInducedSumLinearMap S) := by
    -- A common level-set equation pushes every direction vector into the kernel.
    exact affineSpan_direction_le_ker_of_forall_eq hσ_face hlevel
  intro v hv
  exact ⟨hdir_ambient hv, hdir_ker hv⟩

/-- Helper for Theorem 7.19: one can choose two distinct anchors in `S` and two distinct anchors
outside `S` from the facet-range assumptions `2 ≤ |S| ≤ n - 2`. -/
private theorem existsSubtourAnchorPairs
    {n : ℕ}
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    ∃ a b i j : Fin n,
      a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ i ∉ S ∧ j ∉ S ∧ i ≠ j := by
  classical
  let Sc : Finset (Fin n) := Sᶜ
  have hS_nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hS_nonempty
  have hS_erase_nonempty : (S.erase a).Nonempty := by
    exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha]; omega)
  obtain ⟨b, hb_erase⟩ := hS_erase_nonempty
  have hb : b ∈ S := (Finset.mem_erase.mp hb_erase).2
  have hab : a ≠ b := by
    exact (Finset.mem_erase.mp hb_erase).1.symm
  have hSc_card : Sc.card = n - S.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hSc_lower : 2 ≤ Sc.card := by
    rw [hSc_card]
    omega
  have hSc_nonempty : Sc.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hiSc⟩ := hSc_nonempty
  have hi : i ∉ S := by
    simpa [Sc] using hiSc
  have hSc_erase_nonempty : (Sc.erase i).Nonempty := by
    exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hiSc]; omega)
  obtain ⟨j, hjSc_erase⟩ := hSc_erase_nonempty
  have hjSc : j ∈ Sc := (Finset.mem_erase.mp hjSc_erase).2
  have hj : j ∉ S := by
    simpa [Sc] using hjSc
  have hij : i ≠ j := by
    exact (Finset.mem_erase.mp hjSc_erase).1.symm
  exact ⟨a, b, i, j, ha, hb, hab, hi, hj, hij⟩

/-- Helper for Theorem 7.19: every ambient TSP direction vector has zero incident-edge sum at
every vertex. -/
private theorem ambientDirection_zeroIncidentSum
    {n : ℕ}
    (hn : 4 ≤ n)
    {v : complete_graph_edges n → ℝ}
    (hv : v ∈ (affineSpan ℝ (travelingSalesmanPolytope n)).direction) :
    ∀ i : Fin n, (completeGraphIncidentEdgeFinset i).sum v = 0 := by
  let x0 : complete_graph_edges n → ℝ := hamiltonian_tour_incidence_vector (Equiv.refl (Fin n))
  have hx0_poly : x0 ∈ travelingSalesmanPolytope n := by
    -- The identity Hamiltonian tour is one of the polytope vertices.
    rw [travelingSalesmanPolytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self (Equiv.refl (Fin n)))
  have hx0_aff : x0 ∈ affineSpan ℝ (travelingSalesmanPolytope n) := by
    exact subset_affineSpan ℝ _ hx0_poly
  have hshift_aff : v +ᵥ x0 ∈ affineSpan ℝ (travelingSalesmanPolytope n) := by
    -- Translating an affine-hull point by a direction vector stays inside the same affine hull.
    exact AffineSubspace.vadd_mem_of_mem_direction hv hx0_aff
  have hn3 : 3 ≤ n := by
    omega
  have hspan :
      (affineSpan ℝ (travelingSalesmanPolytope n) : Set (complete_graph_edges n → ℝ)) =
        travelingSalesmanDegreeConstraintSet n := by
    simpa using affineSpan_travelingSalesmanPolytope_eq_degreeConstraintSet n hn3
  have hx0_degree : x0 ∈ travelingSalesmanDegreeConstraintSet n := by
    rw [← hspan]
    exact hx0_aff
  have hshift_degree : v +ᵥ x0 ∈ travelingSalesmanDegreeConstraintSet n := by
    rw [← hspan]
    exact hshift_aff
  intro i
  have hx0_sum : (completeGraphIncidentEdgeFinset i).sum x0 = 2 := by
    -- The base tour satisfies the degree equations at every vertex.
    simpa [completeGraphIncidentEdgeFinset_eq] using
      (mem_travelingSalesmanDegreeConstraintSet_iff.mp hx0_degree) i
  have hshift_sum : (completeGraphIncidentEdgeFinset i).sum (v +ᵥ x0) = 2 := by
    -- The translated affine-hull point still lies in the same degree slice.
    simpa [vadd_eq_add, completeGraphIncidentEdgeFinset_eq] using
      (mem_travelingSalesmanDegreeConstraintSet_iff.mp hshift_degree) i
  have hadd :
      (completeGraphIncidentEdgeFinset i).sum (v +ᵥ x0) =
        (completeGraphIncidentEdgeFinset i).sum v +
          (completeGraphIncidentEdgeFinset i).sum x0 := by
    -- Finite incident sums distribute over addition coordinatewise.
    simp [vadd_eq_add, Finset.sum_add_distrib]
  linarith

/-- Helper for Theorem 7.19: a vector in the ambient direction cut by the induced-edge kernel
already satisfies the concrete zero-incident and zero-induced equations used in the source proof.
-/
private theorem ambientDirectionInfInducedKer_zeroConstraints
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    {v : complete_graph_edges n → ℝ}
    (hv :
      v ∈ (affineSpan ℝ (travelingSalesmanPolytope n)).direction ⊓
        LinearMap.ker (subtourInducedSumLinearMap S)) :
    (∀ i : Fin n, (completeGraphIncidentEdgeFinset i).sum v = 0) ∧
      subtourInducedSumLinearMap S v = 0 := by
  refine ⟨ambientDirection_zeroIncidentSum hn hv.1, ?_⟩
  -- The second component of the intersection membership is exactly the induced-edge kernel
  -- equation.
  exact LinearMap.mem_ker.mp hv.2

/-- Helper for Theorem 7.19: the genuine cut-edge swap generator
`χ_ai + χ_bj - χ_aj - χ_bi`. -/
private def cutSwapVector
    {n : ℕ}
    (eai ebj eaj ebi : complete_graph_edges n) :
    complete_graph_edges n → ℝ :=
  Pi.basisFun ℝ (complete_graph_edges n) eai +
    Pi.basisFun ℝ (complete_graph_edges n) ebj -
      Pi.basisFun ℝ (complete_graph_edges n) eaj -
        Pi.basisFun ℝ (complete_graph_edges n) ebi

/-- Helper for Theorem 7.19: once a residual vector is supported only on the six anchor edges and
satisfies the zero-incident and zero-induced equations, it is a scalar multiple of the anchored
cut swap. -/
private theorem anchorResidual_eq_smul_cutSwap_of_zeroConstraints
    {n : ℕ}
    (S : Finset (Fin n))
    {a b i j : Fin n}
    (hab : a ≠ b) (hij : i ≠ j) (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i) (hbj : b ≠ j)
    (ha : a ∈ S) (hb : b ∈ S) (hi : i ∉ S) (hj : j ∉ S)
    {r : complete_graph_edges n → ℝ}
    (hincident : ∀ v : Fin n, (completeGraphIncidentEdgeFinset v).sum r = 0)
    (hinduced : subtourInducedSumLinearMap S r = 0) :
    let eab : complete_graph_edges n := completeGraphEdgeBetween a b hab
    let eij : complete_graph_edges n := completeGraphEdgeBetween i j hij
    let eai : complete_graph_edges n := completeGraphEdgeBetween a i hai
    let eaj : complete_graph_edges n := completeGraphEdgeBetween a j haj
    let ebi : complete_graph_edges n := completeGraphEdgeBetween b i hbi
    let ebj : complete_graph_edges n := completeGraphEdgeBetween b j hbj
    let anchorSupport : Finset (complete_graph_edges n) := {eab, eij, eai, eaj, ebi, ebj}
    (∀ e, e ∉ anchorSupport → r e = 0) →
      ∃ t : ℝ, r = t • cutSwapVector eai ebj eaj ebi := by
  intro eab eij eai eaj ebi ebj anchorSupport hsupport
  -- Pairwise separation of the six anchor edges keeps the ensuing coordinate sums propositional,
  -- avoiding any large definitional reduction through unordered-edge representatives.
  have heab_ne_eij : eab ≠ eij := by
    exact completeGraphEdgeBetween_ne hab hij (Or.inl hai) (Or.inl haj)
  have heab_ne_eai : eab ≠ eai := by
    exact completeGraphEdgeBetween_ne hab hai (Or.inr hbi) (Or.inl hai)
  have heab_ne_eaj : eab ≠ eaj := by
    exact completeGraphEdgeBetween_ne hab haj (Or.inr hbj) (Or.inl haj)
  have heab_ne_ebi : eab ≠ ebi := by
    exact completeGraphEdgeBetween_ne hab hbi (Or.inl hab) (Or.inl hai)
  have heab_ne_ebj : eab ≠ ebj := by
    exact completeGraphEdgeBetween_ne hab hbj (Or.inl hab) (Or.inl haj)
  have heij_ne_eai : eij ≠ eai := by
    exact completeGraphEdgeBetween_ne hij hai (Or.inl hai.symm) (Or.inr haj.symm)
  have heij_ne_eaj : eij ≠ eaj := by
    exact completeGraphEdgeBetween_ne hij haj (Or.inl hai.symm) (Or.inl hij)
  have heij_ne_ebi : eij ≠ ebi := by
    exact completeGraphEdgeBetween_ne hij hbi (Or.inl hbi.symm) (Or.inr hbj.symm)
  have heij_ne_ebj : eij ≠ ebj := by
    exact completeGraphEdgeBetween_ne hij hbj (Or.inl hbi.symm) (Or.inl hij)
  have heai_ne_eaj : eai ≠ eaj := by
    exact completeGraphEdgeBetween_ne hai haj (Or.inr hij) (Or.inl haj)
  have heai_ne_ebi : eai ≠ ebi := by
    exact completeGraphEdgeBetween_ne hai hbi (Or.inl hab) (Or.inl hai)
  have heai_ne_ebj : eai ≠ ebj := by
    exact completeGraphEdgeBetween_ne hai hbj (Or.inl hab) (Or.inl haj)
  have heaj_ne_ebi : eaj ≠ ebi := by
    exact completeGraphEdgeBetween_ne haj hbi (Or.inl hab) (Or.inl hai)
  have heaj_ne_ebj : eaj ≠ ebj := by
    exact completeGraphEdgeBetween_ne haj hbj (Or.inl hab) (Or.inl haj)
  have hebi_ne_ebj : ebi ≠ ebj := by
    exact completeGraphEdgeBetween_ne hbi hbj (Or.inr hij) (Or.inl hbj)
  have heab_induced : eab ∈ subtourInducedEdgeFinset S := by
    -- The anchor edge `ab` lies inside `S`, so it is the only induced edge in the six-edge support.
    exact (completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff S hab).2 ⟨ha, hb⟩
  have heij_not_induced : eij ∉ subtourInducedEdgeFinset S := by
    -- The complement anchor edge `ij` has no endpoint in `S`.
    intro heij_induced
    exact hi ((completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff S hij).1 heij_induced).1
  have heai_not_induced : eai ∉ subtourInducedEdgeFinset S := by
    -- Each cut edge has exactly one endpoint in `S`, so it is not induced by `S`.
    intro heai_induced
    exact hi ((completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff S hai).1 heai_induced).2
  have heaj_not_induced : eaj ∉ subtourInducedEdgeFinset S := by
    -- The second `a`-cut edge is excluded for the same reason.
    intro heaj_induced
    exact hj ((completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff S haj).1 heaj_induced).2
  have hebi_not_induced : ebi ∉ subtourInducedEdgeFinset S := by
    -- The first `b`-cut edge is likewise not induced.
    intro hebi_induced
    exact hi ((completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff S hbi).1 hebi_induced).2
  have hebj_not_induced : ebj ∉ subtourInducedEdgeFinset S := by
    -- The second `b`-cut edge is likewise not induced.
    intro hebj_induced
    exact hj ((completeGraphEdgeBetween_mem_subtourInducedEdgeFinset_iff S hbj).1 hebj_induced).2
  have hreconstruct :
      r = (∑ e ∈ anchorSupport, r e • Pi.basisFun ℝ (complete_graph_edges n) e) := by
    -- The support hypothesis lets us rewrite `r` as a finite basis expansion over the six anchors.
    ext e
    by_cases he : e ∈ anchorSupport
    · rw [Finset.sum_apply, Finset.sum_eq_single e]
      · simp [Pi.basisFun]
      · intro e' he' hne
        simp [Pi.basisFun, hne]
      · simp [he]
    · rw [Finset.sum_apply]
      rw [hsupport e he]
      symm
      apply Finset.sum_eq_zero
      intro e' he'
      have hne : e' ≠ e := by
        intro heq
        subst e'
        exact he he'
      simp [Pi.basisFun, hne]
  have hab_zero : r eab = 0 := by
    -- Applying the induced-edge linear form to the anchored basis expansion isolates the `ab`
    -- coordinate because all five other anchors are non-induced.
    symm
    calc
      0 = subtourInducedSumLinearMap S r := hinduced.symm
      _ = subtourInducedSumLinearMap S
            (∑ e ∈ anchorSupport, r e • Pi.basisFun ℝ (complete_graph_edges n) e) := by
              exact congrArg (subtourInducedSumLinearMap S) hreconstruct
      _ = r eab := by
            rw [subtourInducedSumLinearMap_apply, finsetSum_basisExpansion]
            simp [anchorSupport, heab_induced, heij_not_induced, heai_not_induced,
              heaj_not_induced, hebi_not_induced, hebj_not_induced]
  have ha_sum :
      r eab + r eai + r eaj = 0 := by
    -- At the anchor `a`, only the three edges `ab`, `ai`, and `aj` survive in the basis
    -- expansion, so the zero-incident equation becomes a three-term relation.
    symm
    calc
      0 = (completeGraphIncidentEdgeFinset a).sum r := (hincident a).symm
      _ = (completeGraphIncidentEdgeFinset a).sum
            (∑ e ∈ anchorSupport, r e • Pi.basisFun ℝ (complete_graph_edges n) e) := by
              exact congrArg (Finset.sum (completeGraphIncidentEdgeFinset a)) hreconstruct
      _ = r eab + r eai + r eaj := by
            rw [finsetSum_basisExpansion]
            simp [anchorSupport, eab, eij, eai, eaj, ebi, ebj,
              mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, hab, hai, haj,
              heab_ne_eai, heab_ne_eaj, heai_ne_eaj]
            ring
  have hb_sum :
      r eab + r ebi + r ebj = 0 := by
    -- The same incident-edge calculation at `b` isolates `ab`, `bi`, and `bj`.
    symm
    calc
      0 = (completeGraphIncidentEdgeFinset b).sum r := (hincident b).symm
      _ = (completeGraphIncidentEdgeFinset b).sum
            (∑ e ∈ anchorSupport, r e • Pi.basisFun ℝ (complete_graph_edges n) e) := by
              exact congrArg (Finset.sum (completeGraphIncidentEdgeFinset b)) hreconstruct
      _ = r eab + r ebi + r ebj := by
            rw [finsetSum_basisExpansion]
            simp [anchorSupport, eab, eij, eai, eaj, ebi, ebj,
              mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, hab.symm, hbi, hbj,
              heab_ne_ebi, heab_ne_ebj, hebi_ne_ebj]
            ring
  have hi_sum :
      r eij + r eai + r ebi = 0 := by
    -- At the complement anchor `i`, only `ij`, `ai`, and `bi` contribute.
    symm
    calc
      0 = (completeGraphIncidentEdgeFinset i).sum r := (hincident i).symm
      _ = (completeGraphIncidentEdgeFinset i).sum
            (∑ e ∈ anchorSupport, r e • Pi.basisFun ℝ (complete_graph_edges n) e) := by
              exact congrArg (Finset.sum (completeGraphIncidentEdgeFinset i)) hreconstruct
      _ = r eij + r eai + r ebi := by
            rw [finsetSum_basisExpansion]
            simp [anchorSupport, eab, eij, eai, eaj, ebi, ebj,
              mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, hij, hai.symm, hbi.symm,
              heij_ne_eai, heij_ne_ebi, heai_ne_ebi]
            ring
  have hj_sum :
      r eij + r eaj + r ebj = 0 := by
    -- The last anchor equation at `j` gives the companion three-term relation.
    symm
    calc
      0 = (completeGraphIncidentEdgeFinset j).sum r := (hincident j).symm
      _ = (completeGraphIncidentEdgeFinset j).sum
            (∑ e ∈ anchorSupport, r e • Pi.basisFun ℝ (complete_graph_edges n) e) := by
              exact congrArg (Finset.sum (completeGraphIncidentEdgeFinset j)) hreconstruct
      _ = r eij + r eaj + r ebj := by
            rw [finsetSum_basisExpansion]
            simp [anchorSupport, eab, eij, eai, eaj, ebi, ebj,
              mem_completeGraphIncidentEdgeFinset_edgeBetween_iff, hij.symm, haj.symm, hbj.symm,
              heij_ne_eaj, heij_ne_ebj, heaj_ne_ebj]
            ring
  have heaj_eq : r eaj = -r eai := by
    -- Removing the already-vanishing `ab` term from the `a`-equation gives the first skew-symmetry.
    linarith
  have hebi_eq : r ebi = -r eai := by
    -- The `i`- and `j`-equations force the two `i`-incident cut coefficients to cancel.
    have heij_zero : r eij = 0 := by
      linarith
    linarith
  have heij_zero : r eij = 0 := by
    -- Substituting the two skew-symmetry relations into the `j`-equation eliminates `ij`.
    linarith [hj_sum, heaj_eq, hb_sum, hab_zero, hebi_eq]
  have hebj_eq : r ebj = r eai := by
    -- The `b`-equation now gives the final cut coefficient directly.
    linarith [hb_sum, hab_zero, hebi_eq]
  refine ⟨r eai, ?_⟩
  ext e
  by_cases he : e ∈ anchorSupport
  · have he' := he
    simp [anchorSupport] at he'
    rcases he' with rfl | rfl | rfl | rfl | rfl | rfl
    · -- The induced anchor edge has coefficient `0` on both sides.
      simp [cutSwapVector, hab_zero, heab_ne_eai, heab_ne_ebj, heab_ne_eaj,
        heab_ne_ebi]
    · -- The complement anchor edge has coefficient `0` on both sides.
      simp [cutSwapVector, heij_zero, heij_ne_eai, heij_ne_ebj, heij_ne_eaj,
        heij_ne_ebi]
    · -- The leading cut edge defines the scalar factor.
      simp [cutSwapVector, heai_ne_ebj, heai_ne_eaj, heai_ne_ebi]
    · -- The second `a`-cut edge has the forced opposite sign.
      simp [cutSwapVector, heaj_eq, heai_ne_eaj, heaj_ne_ebj, heaj_ne_ebi]
    · -- The first `b`-cut edge has the same forced opposite sign.
      simp [cutSwapVector, hebi_eq, heai_ne_ebi, hebi_ne_ebj, heaj_ne_ebi]
    · -- The last cut edge matches the leading cut edge coefficient.
      simp [cutSwapVector, hebj_eq, heai_ne_ebj, heaj_ne_ebj, hebi_ne_ebj]
  · have hne := he
    simp [anchorSupport] at hne
    rcases hne with ⟨hneab, hneij, hneai, hneaj, hnebi, hnebj⟩
    -- Outside the six anchors, both the residual and the cut-swap generator vanish coordinatewise.
    simp [cutSwapVector, hsupport e he, hneai, hneaj, hnebi, hnebj]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: every left-shore coordinate-sum basis difference occurs in the
range of internal restriction on the tight-face direction. -/
private lemma subtourLeftBasisDifference_mem_internalRange
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (e : complete_graph_edges p) :
    (Pi.basisFun ℝ (complete_graph_edges p) e -
          Pi.basisFun ℝ (complete_graph_edges p) (reference_edge p hpLower), 0) ∈
      LinearMap.range
        ((subtourInternalRestriction (by omega) σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction) := by
  obtain ⟨ρ, τ, hdiff⟩ := reference_edge_difference_vertex_witness p hpLower e
  let xρ := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ ρ (Equiv.refl (Fin (n - p))))
  let xτ := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ τ (Equiv.refl (Fin (n - p))))
  have hxρ : xρ ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ ρ (Equiv.refl _))
  have hxτ : xτ ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ τ (Equiv.refl _))
  have hv : xρ - xτ ∈ (affineSpan ℝ (subtour_elimination_face n S)).direction := by
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxρ hxτ
  refine ⟨⟨xρ - xτ, hv⟩, ?_⟩
  -- The coordinate specification sends the face-direction witness to the desired left basis
  -- difference, while its unchanged right path cancels.
  apply Prod.ext
  · funext d
    change (xρ - xτ) (subtourLeftEdge (by omega) σ d) =
      (Pi.basisFun ℝ (complete_graph_edges p) e -
        Pi.basisFun ℝ (complete_graph_edges p) (reference_edge p hpLower)) d
    simp only [xρ, xτ]
    rw [Pi.sub_apply, subtourBlockTour_leftCoordinate hn hpLower hpUpper S σ hσ,
      subtourBlockTour_leftCoordinate hn hpLower hpUpper S σ hσ]
    exact congrFun hdiff d
  · funext d
    change (xρ - xτ) (subtourRightEdge (by omega) σ d) = 0
    simp only [xρ, xτ]
    rw [Pi.sub_apply, subtourBlockTour_rightCoordinate hn hpLower hpUpper S σ hσ,
      subtourBlockTour_rightCoordinate hn hpLower hpUpper S σ hσ]
    simp

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: every right-shore coordinate-sum basis difference occurs in the
range of internal restriction on the tight-face direction. -/
private lemma subtourRightBasisDifference_mem_internalRange
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (e : complete_graph_edges (n - p)) :
    (0, Pi.basisFun ℝ (complete_graph_edges (n - p)) e -
          Pi.basisFun ℝ (complete_graph_edges (n - p))
            (reference_edge (n - p) (by omega))) ∈
      LinearMap.range
        ((subtourInternalRestriction (by omega) σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction) := by
  have hq : 2 ≤ n - p := by omega
  obtain ⟨ρ, τ, hdiff⟩ := reference_edge_difference_vertex_witness (n - p) hq e
  let xρ := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ (Equiv.refl (Fin p)) ρ)
  let xτ := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ (Equiv.refl (Fin p)) τ)
  have hxρ : xρ ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ (Equiv.refl _) ρ)
  have hxτ : xτ ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ (Equiv.refl _) τ)
  have hv : xρ - xτ ∈ (affineSpan ℝ (subtour_elimination_face n S)).direction := by
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxρ hxτ
  refine ⟨⟨xρ - xτ, hv⟩, ?_⟩
  -- This time the left path is fixed and the right coordinate records the path witness.
  apply Prod.ext
  · funext d
    change (xρ - xτ) (subtourLeftEdge (by omega) σ d) = 0
    simp only [xρ, xτ]
    rw [Pi.sub_apply, subtourBlockTour_leftCoordinate hn hpLower hpUpper S σ hσ,
      subtourBlockTour_leftCoordinate hn hpLower hpUpper S σ hσ]
    simp
  · funext d
    change (xρ - xτ) (subtourRightEdge (by omega) σ d) =
      (Pi.basisFun ℝ (complete_graph_edges (n - p)) e -
        Pi.basisFun ℝ (complete_graph_edges (n - p)) (reference_edge (n - p) hq)) d
    simp only [xρ, xτ]
    rw [Pi.sub_apply, subtourBlockTour_rightCoordinate hn hpLower hpUpper S σ hσ,
      subtourBlockTour_rightCoordinate hn hpLower hpUpper S σ hσ]
    exact congrFun hdiff d

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the product of the two
internal zero-sum coordinate spaces lies in the range of restriction from the tight face. -/
private lemma subtourInternalDirections_le_range
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hp : p ≤ n)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p) :
    (LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges p)).sumCoords).prod
        (LinearMap.ker
          (Pi.basisFun ℝ (complete_graph_edges (n - p))).sumCoords) ≤
      LinearMap.range
        ((subtourInternalRestriction hp σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction) := by
  have hqLower : 2 ≤ n - p := by omega
  let Rng := LinearMap.range
    ((subtourInternalRestriction hp σ).domRestrict
      (affineSpan ℝ (subtour_elimination_face n S)).direction)
  intro x hx
  have hxLeft : x.1 ∈
      LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges p)).sumCoords :=
    (Submodule.mem_prod.mp hx).1
  have hxRight : x.2 ∈
      LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges (n - p))).sumCoords :=
    (Submodule.mem_prod.mp hx).2
  rw [sum_zero_submodule_eq_span_reference_differences
    (complete_graph_edges p) (reference_edge p hpLower)] at hxLeft
  rw [sum_zero_submodule_eq_span_reference_differences
    (complete_graph_edges (n - p)) (reference_edge (n - p) hqLower)] at hxRight
  have hleftSpan :
      ∀ y ∈ Submodule.span ℝ (Set.range fun e : complete_graph_edges p ↦
          Pi.basisFun ℝ (complete_graph_edges p) e -
            Pi.basisFun ℝ (complete_graph_edges p) (reference_edge p hpLower)),
        (y, 0) ∈ Rng := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨e, rfl⟩
      exact subtourLeftBasisDifference_mem_internalRange hn hpLower hpUpper S σ hσ e
    · exact Rng.zero_mem
    · intro u v _ _ hu hv
      simpa using Rng.add_mem hu hv
    · intro a u _ hu
      simpa using Rng.smul_mem a hu
  have hrightSpan :
      ∀ y ∈ Submodule.span ℝ (Set.range fun e : complete_graph_edges (n - p) ↦
          Pi.basisFun ℝ (complete_graph_edges (n - p)) e -
            Pi.basisFun ℝ (complete_graph_edges (n - p)) (reference_edge (n - p) hqLower)),
        (0, y) ∈ Rng := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨e, rfl⟩
      exact subtourRightBasisDifference_mem_internalRange hn hpLower hpUpper S σ hσ e
    · exact Rng.zero_mem
    · intro u v _ _ hu hv
      simpa using Rng.add_mem hu hv
    · intro a u _ hu
      simpa using Rng.smul_mem a hu
  have hleft := hleftSpan x.1 hxLeft
  have hright := hrightSpan x.2 hxRight
  -- Adding the two coordinate-axis witnesses gives the required pair.
  change x ∈ Rng
  simpa using Rng.add_mem hleft hright

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: reversing the left block of an endpoint-controlled block tour gives
an anchored cross-rectangle direction. -/
private def subtourCrossRectangleDirection
    {n p : ℕ} (hp : p ≤ n) (hpLower : 2 ≤ p) (hqLower : 2 ≤ n - p)
    (σ : Equiv.Perm (Fin n))
    (z : Fin (p - 1) × Fin (n - p - 1)) : complete_graph_edges n → ℝ :=
  let ρ₁ := subtourEndpointPerm hpLower z.1
  let ρ₂ := subtourEndpointPerm hqLower z.2
  hamiltonian_tour_incidence_vector (subtourBlockTourPerm hp σ ρ₁ ρ₂) -
    hamiltonian_tour_incidence_vector
      (subtourBlockTourPerm hp σ (Fin.revPerm.trans ρ₁) ρ₂)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: every anchored cross rectangle is a direction of the tight subtour
face. -/
private lemma subtourCrossRectangleDirection_mem_faceDirection
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z : Fin (p - 1) × Fin (n - p - 1)) :
    subtourCrossRectangleDirection (by omega) hpLower
        (subtourRightBlock_two_le hpLower hpUpper) σ z ∈
      (affineSpan ℝ (subtour_elimination_face n S)).direction := by
  let ρ₁ := subtourEndpointPerm hpLower z.1
  let ρ₂ := subtourEndpointPerm (subtourRightBlock_two_le hpLower hpUpper) z.2
  let x := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂)
  let y := hamiltonian_tour_incidence_vector
    (subtourBlockTourPerm (by omega) σ (Fin.revPerm.trans ρ₁) ρ₂)
  have hx : x ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ ρ₁ ρ₂)
  have hy : y ∈ affineSpan ℝ (subtour_elimination_face n S) := by
    exact subset_affineSpan ℝ _
      (subtourBlockTour_mem_face hn hpLower hpUpper S σ hσ
        (Fin.revPerm.trans ρ₁) ρ₂)
  -- The difference of the two tight tour vertices lies in the face direction.
  simpa [subtourCrossRectangleDirection, ρ₁, ρ₂, x, y, vsub_eq_sub] using
    AffineSubspace.vsub_mem_direction hx hy

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: cross rectangles vanish after restricting to the two internal shore
graphs. -/
private lemma subtourInternalRestriction_crossRectangle_eq_zero
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z : Fin (p - 1) × Fin (n - p - 1)) :
    subtourInternalRestriction (p := p) (by omega) σ
        (subtourCrossRectangleDirection (by omega) hpLower
          (subtourRightBlock_two_le hpLower hpUpper) σ z) = 0 := by
  let ρ₁ := subtourEndpointPerm hpLower z.1
  let ρ₂ := subtourEndpointPerm (subtourRightBlock_two_le hpLower hpUpper) z.2
  apply Prod.ext
  · funext e
    change
      (hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) -
          hamiltonian_tour_incidence_vector
            (subtourBlockTourPerm (by omega) σ (Fin.revPerm.trans ρ₁) ρ₂))
          (subtourLeftEdge (p := p) (by omega) σ e) = 0
    rw [Pi.sub_apply,
      subtourBlockTour_leftCoordinate (p := p) hn hpLower hpUpper S σ hσ,
      subtourBlockTour_leftCoordinate (p := p) hn hpLower hpUpper S σ hσ,
      hamiltonianPathIncidence_reverse hpLower ρ₁]
    simp
  · funext e
    change
      (hamiltonian_tour_incidence_vector (subtourBlockTourPerm (by omega) σ ρ₁ ρ₂) -
          hamiltonian_tour_incidence_vector
            (subtourBlockTourPerm (by omega) σ (Fin.revPerm.trans ρ₁) ρ₂))
          (subtourRightEdge (p := p) (by omega) σ e) = 0
    rw [Pi.sub_apply,
      subtourBlockTour_rightCoordinate (p := p) hn hpLower hpUpper S σ hσ,
      subtourBlockTour_rightCoordinate (p := p) hn hpLower hpUpper S σ hσ]
    simp

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: evaluating an anchored cross rectangle at a variable-variable cross
edge recovers its index coefficient. -/
private lemma subtourCrossRectangleDirection_apply
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z k : Fin (p - 1) × Fin (n - p - 1)) :
    subtourCrossRectangleDirection (by omega) hpLower
        (subtourRightBlock_two_le hpLower hpUpper) σ z
        (subtourCrossEdge (by omega) σ
          (subtourNonzeroPosition hpLower k.1)
          (subtourNonzeroPosition (subtourRightBlock_two_le hpLower hpUpper) k.2)) =
      if k = z then -1 else 0 := by
  let hqLower := subtourRightBlock_two_le hpLower hpUpper
  let ρ₁ := subtourEndpointPerm hpLower z.1
  let ρ₂ := subtourEndpointPerm hqLower z.2
  simp only [subtourCrossRectangleDirection, Pi.sub_apply]
  rw [subtourBlockTour_crossCoordinate hn hpLower hpUpper S σ hσ,
    subtourBlockTour_crossCoordinate hn hpLower hpUpper S σ hσ]
  -- The unreversed tour avoids variable-variable cross edges; the reversed tour contains exactly
  -- the coordinate indexed by `z`.
  simp [Equiv.trans_apply, Fin.revPerm_apply, Prod.ext_iff]
  split_ifs <;> norm_num

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the anchored cross-rectangle directions are linearly independent. -/
private lemma subtourCrossRectangleDirection_linearIndependent
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p) :
    LinearIndependent ℝ
      (fun z : Fin (p - 1) × Fin (n - p - 1) ↦
        subtourCrossRectangleDirection (by omega) hpLower
          (subtourRightBlock_two_le hpLower hpUpper) σ z) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum z
  have hcoord := congrArg
    (fun x : complete_graph_edges n → ℝ ↦
      x (subtourCrossEdge (by omega) σ
        (subtourNonzeroPosition hpLower z.1)
        (subtourNonzeroPosition (subtourRightBlock_two_le hpLower hpUpper) z.2))) hsum
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hcoord
  simp_rw [subtourCrossRectangleDirection_apply hn hpLower hpUpper S σ hσ] at hcoord
  simpa using neg_eq_zero.mp (by simpa using hcoord)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: an anchored cross rectangle,
regarded as a vector in the tight-face direction. -/
private def subtourCrossRectangleFaceDirection
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z : Fin (p - 1) × Fin (n - p - 1)) :
    (affineSpan ℝ (subtour_elimination_face n S)).direction :=
  ⟨subtourCrossRectangleDirection hp hpLower
      (subtourRightBlock_two_le hpLower hpUpper) σ z,
    subtourCrossRectangleDirection_mem_faceDirection hn hpLower hpUpper S σ hσ z⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: a cross-rectangle face
direction belongs to the kernel of internal-coordinate restriction. -/
private lemma subtourCrossRectangleFaceDirection_mem_internalKernel
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z : Fin (p - 1) × Fin (n - p - 1)) :
    subtourCrossRectangleFaceDirection hn hpLower hpUpper hp S σ hσ z ∈
      LinearMap.ker
        ((subtourInternalRestriction hp σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction) := by
  -- The kernel equation is exactly the previously established internal-coordinate vanishing.
  exact subtourInternalRestriction_crossRectangle_eq_zero
    hn hpLower hpUpper S σ hσ z

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: an anchored cross rectangle as
an element of the internal-restriction kernel. -/
private def subtourCrossRectangleKernelDirection
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p)
    (z : Fin (p - 1) × Fin (n - p - 1)) :
    LinearMap.ker
      ((subtourInternalRestriction hp σ).domRestrict
        (affineSpan ℝ (subtour_elimination_face n S)).direction) :=
  ⟨subtourCrossRectangleFaceDirection hn hpLower hpUpper hp S σ hσ z,
    subtourCrossRectangleFaceDirection_mem_internalKernel
      hn hpLower hpUpper hp S σ hσ z⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the anchored cross rectangles
remain linearly independent inside the internal-restriction kernel. -/
private lemma subtourCrossRectangleKernelDirection_linearIndependent
    {n p : ℕ} (hn : 4 ≤ n) (hpLower : 2 ≤ p) (hpUpper : p ≤ n - 2)
    (hp : p ≤ n) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < p) :
    LinearIndependent ℝ
      (subtourCrossRectangleKernelDirection hn hpLower hpUpper hp S σ hσ) := by
  let inclusion :
      LinearMap.ker
          ((subtourInternalRestriction hp σ).domRestrict
            (affineSpan ℝ (subtour_elimination_face n S)).direction) →ₗ[ℝ]
        (complete_graph_edges n → ℝ) :=
    (affineSpan ℝ (subtour_elimination_face n S)).direction.subtype.comp
      (LinearMap.ker
        ((subtourInternalRestriction hp σ).domRestrict
          (affineSpan ℝ (subtour_elimination_face n S)).direction)).subtype
  apply LinearIndependent.of_comp inclusion
  -- Forgetting the two subtypes recovers the already independent ambient rectangle family.
  simpa [inclusion, Function.comp_def, subtourCrossRectangleKernelDirection,
    subtourCrossRectangleFaceDirection] using
      subtourCrossRectangleDirection_linearIndependent hn hpLower hpUpper S σ hσ

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: the two internal path
dimensions and the cross-rectangle dimension add to the TSP facet dimension. -/
private lemma subtourDimensionArithmetic
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (Nat.choose p 2 - 1 + (Nat.choose q 2 - 1)) +
        (p - 1) * (q - 1) + 1 =
      Nat.choose (p + q) 2 - (p + q) := by
  have hpChoosePos : 0 < Nat.choose p 2 := Nat.choose_pos hp
  have hqChoosePos : 0 < Nat.choose q 2 := Nat.choose_pos hq
  have hpChooseSplit : Nat.choose p 2 - 1 + 1 = Nat.choose p 2 := by omega
  have hqChooseSplit : Nat.choose q 2 - 1 + 1 = Nat.choose q 2 := by omega
  have hpSplit : p - 1 + 1 = p := by omega
  have hqSplit : q - 1 + 1 = q := by omega
  have hprod :
      p * q = (p - 1) * (q - 1) + (p - 1) + (q - 1) + 1 := by
    calc
      p * q = ((p - 1) + 1) * ((q - 1) + 1) := by rw [hpSplit, hqSplit]
      _ = (p - 1) * (q - 1) + (p - 1) + (q - 1) + 1 := by ring
  have hchoose :
      Nat.choose (p + q) 2 = Nat.choose p 2 + p * q + Nat.choose q 2 := by
    rw [Nat.add_choose_eq]
    norm_num [Finset.antidiagonal]
    ring
  -- Expand the three positive predecessors and use Vandermonde's identity at rank two.
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean: internal path differences and cross rectangles give the required lower bound on the tight-face direction. -/
private theorem subtourFaceDirection_finrank_lower
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    Module.finrank ℝ (affineSpan ℝ (travelingSalesmanPolytope n)).direction ≤
      Module.finrank ℝ (affineSpan ℝ (subtour_elimination_face n S)).direction + 1 := by
  obtain ⟨π, hπ⟩ := exists_block_order_permutation S
  let σ : Equiv.Perm (Fin n) := π.symm
  have hσ : ∀ t : Fin n, σ t ∈ S ↔ (t : ℕ) < S.card := by
    intro t
    simpa [σ] using hπ (σ t)
  have hp : S.card ≤ n := by omega
  have hqLower : 2 ≤ n - S.card := by omega
  let Kleft : Submodule ℝ (complete_graph_edges S.card → ℝ) :=
    LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges S.card)).sumCoords
  let Kright : Submodule ℝ (complete_graph_edges (n - S.card) → ℝ) :=
    LinearMap.ker
      (Pi.basisFun ℝ (complete_graph_edges (n - S.card))).sumCoords
  let R :=
    (subtourInternalRestriction hp σ).domRestrict
      (affineSpan ℝ (subtour_elimination_face n S)).direction
  have hinternal : Kleft.prod Kright ≤ LinearMap.range R := by
    -- Tight block-tour differences realize both internal zero-sum coordinate spaces.
    simpa [Kleft, Kright, R] using
      subtourInternalDirections_le_range hn hS_lower hS_upper hp S σ hσ
  have hKleftEq :
      Kleft = (affineSpan ℝ (hamiltonian_path_polytope S.card)).direction := by
    apply le_antisymm
    · simpa [Kleft] using
        sumCoords_ker_le_hamiltonian_path_direction S.card hS_lower
    · simpa [Kleft] using
        hamiltonian_path_polytope_direction_le_sumCoords_ker S.card
  have hKrightEq :
      Kright =
        (affineSpan ℝ (hamiltonian_path_polytope (n - S.card))).direction := by
    apply le_antisymm
    · simpa [Kright] using
        sumCoords_ker_le_hamiltonian_path_direction (n - S.card) hqLower
    · simpa [Kright] using
        hamiltonian_path_polytope_direction_le_sumCoords_ker (n - S.card)
  have hKleftFinrank :
      Module.finrank ℝ Kleft = Nat.choose S.card 2 - 1 := by
    rw [hKleftEq]
    exact hamiltonian_path_polytope_finrank_direction_affineSpan S.card
  have hKrightFinrank :
      Module.finrank ℝ Kright = Nat.choose (n - S.card) 2 - 1 := by
    rw [hKrightEq]
    exact hamiltonian_path_polytope_finrank_direction_affineSpan (n - S.card)
  have hinternalFinrank :
      Nat.choose S.card 2 - 1 + (Nat.choose (n - S.card) 2 - 1) ≤
        Module.finrank ℝ (LinearMap.range R) := by
    calc
      Nat.choose S.card 2 - 1 + (Nat.choose (n - S.card) 2 - 1) =
          Module.finrank ℝ ↥(Kleft.prod Kright) := by
            rw [finrank_submoduleProd, hKleftFinrank, hKrightFinrank]
      _ ≤ Module.finrank ℝ (LinearMap.range R) :=
        Submodule.finrank_mono hinternal
  have hcrossIndependent :
      LinearIndependent ℝ
        (subtourCrossRectangleKernelDirection
          hn hS_lower hS_upper hp S σ hσ) := by
    exact subtourCrossRectangleKernelDirection_linearIndependent
      hn hS_lower hS_upper hp S σ hσ
  have hkernelFinrank :
      (S.card - 1) * (n - S.card - 1) ≤
        Module.finrank ℝ (LinearMap.ker R) := by
    have hcard := hcrossIndependent.fintype_card_le_finrank
    simpa [R] using hcard
  have hrankNullity :
      Module.finrank ℝ (LinearMap.range R) +
          Module.finrank ℝ (LinearMap.ker R) =
        Module.finrank ℝ
          (affineSpan ℝ (subtour_elimination_face n S)).direction := by
    simpa [R] using LinearMap.finrank_range_add_finrank_ker R
  have hfaceLower :
      (Nat.choose S.card 2 - 1 + (Nat.choose (n - S.card) 2 - 1)) +
          (S.card - 1) * (n - S.card - 1) ≤
        Module.finrank ℝ
          (affineSpan ℝ (subtour_elimination_face n S)).direction := by
    calc
      (Nat.choose S.card 2 - 1 + (Nat.choose (n - S.card) 2 - 1)) +
            (S.card - 1) * (n - S.card - 1) ≤
          Module.finrank ℝ (LinearMap.range R) +
            Module.finrank ℝ (LinearMap.ker R) :=
        Nat.add_le_add hinternalFinrank hkernelFinrank
      _ = Module.finrank ℝ
            (affineSpan ℝ (subtour_elimination_face n S)).direction := hrankNullity
  have hDfinrank :
      Module.finrank ℝ (affineSpan ℝ (travelingSalesmanPolytope n)).direction =
        Nat.choose n 2 - n := by
    exact finrank_direction_affineSpan_travelingSalesmanPolytope n (by omega)
  have hsum : S.card + (n - S.card) = n := Nat.add_sub_of_le hp
  have harithmetic := subtourDimensionArithmetic
    S.card (n - S.card) hS_lower hqLower
  rw [hsum] at harithmetic
  -- Rank-nullity combines both internal path spaces with the independent cross rectangles.
  rw [hDfinrank]
  calc
    Nat.choose n 2 - n =
        (Nat.choose S.card 2 - 1 + (Nat.choose (n - S.card) 2 - 1)) +
          (S.card - 1) * (n - S.card - 1) + 1 := harithmetic.symm
    _ ≤ Module.finrank ℝ
          (affineSpan ℝ (subtour_elimination_face n S)).direction + 1 :=
      Nat.add_le_add_right hfaceLower 1

/-- Helper for Theorem 7.19: once the anchored swap decomposition is available, the ambient
degree-slice kernel cut is contained in the subtour-face direction. -/
private theorem ambientDirectionInfInducedKer_le_subtourFaceDirection
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    (affineSpan ℝ (travelingSalesmanPolytope n)).direction ⊓
      LinearMap.ker (subtourInducedSumLinearMap S) ≤
        (affineSpan ℝ (subtour_elimination_face n S)).direction := by
  let D : Submodule ℝ (complete_graph_edges n → ℝ) :=
    (affineSpan ℝ (travelingSalesmanPolytope n)).direction
  let K : Submodule ℝ (complete_graph_edges n → ℝ) :=
    D ⊓ LinearMap.ker (subtourInducedSumLinearMap S)
  let F : Submodule ℝ (complete_graph_edges n → ℝ) :=
    (affineSpan ℝ (subtour_elimination_face n S)).direction
  have hFK : F ≤ K := by
    -- Every tight-face direction is already an ambient direction with zero induced-edge sum.
    simpa [F, K, D] using
      subtourFaceDirection_le_ambientDirection_inf_inducedKer hn S hS_lower hS_upper
  obtain ⟨w, hwD, hw_eval⟩ :=
    existsAmbientDirectionEvalOne_subtourInducedSum hn S hS_lower hS_upper
  have hKcodim : Module.finrank ℝ K + 1 = Module.finrank ℝ D := by
    -- The transverse four-edge exchange makes `K` a codimension-one subspace of `D`.
    simpa [K] using
      submodule_finrank_inf_ker_add_one_of_eval_one
        D (subtourInducedSumLinearMap S) (by simpa [D] using hwD) hw_eval
  have hDle : Module.finrank ℝ D ≤ Module.finrank ℝ F + 1 := by
    -- Internal path differences and cross rectangles attain the complementary lower bound.
    simpa [D, F] using subtourFaceDirection_finrank_lower hn S hS_lower hS_upper
  have hKle : Module.finrank ℝ K ≤ Module.finrank ℝ F := by
    omega
  have hFK_eq : F = K := Submodule.eq_of_le_of_finrank_le hFK hKle
  -- The rank equality upgrades the easy inclusion to equality, yielding the requested direction.
  simp [F, K, D, hFK_eq]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_4/ch7_sec7_4_theorem_7_19.lean.
Theorem 7.19. For `S ⊆ V = Fin n` with `2 ≤ |S| ≤ n - 2`, the equality face cut out by
`∑_{e ∈ δ(S)} x_e = 2` is a facet of the traveling salesman polytope on `n ≥ 4` nodes. -/
theorem subtour_elimination_face_isFacetOf
    {n : ℕ}
    (hn : 4 ≤ n)
    (S : Finset (Fin n))
    (hS_lower : 2 ≤ S.card)
    (hS_upper : S.card ≤ n - 2) :
    IsFacetOf (travelingSalesmanPolytope n) (subtour_elimination_face n S) := by
  -- Route correction: the face description is now split into an exposed-face shell and a separate
  -- induced-edge equality normalization, so the remaining blocker is only the witness/codimension
  -- package.
  rw [isFacetOf_iff]
  refine ⟨?_, ?_, ?_⟩
  · rcases existsTightSubtourTour hn S hS_lower hS_upper with ⟨σ, hσ_face⟩
    -- A block-ordered Hamiltonian tour is tight for the subtour inequality, so the face is nonempty.
    exact ⟨hamiltonian_tour_incidence_vector σ, hσ_face⟩
  · rcases existsTightSubtourTour hn S hS_lower hS_upper with ⟨σ, hσ_face⟩
    let l : StrongDual ℝ (complete_graph_edges n → ℝ) := subtourCutStrongDual S
    have hvalid_ineq :
        is_valid_inequality (travelingSalesmanPolytope n) (-cutIncidenceVector S) (-2) :=
      subtour_elimination_is_valid_inequality hn S hS_lower hS_upper
    have hvalid_raw := is_valid_inequality_iff.mp hvalid_ineq
    have hvalid :
        ∀ x ∈ travelingSalesmanPolytope n, l x ≤ -2 := by
      intro x hx
      -- The strong-dual cut functional is just the valid inequality written in exposed-face form.
      simpa [l, subtourCutStrongDual_apply] using hvalid_raw hx
    have hface_eq :
        subtour_elimination_face n S =
          {x | x ∈ travelingSalesmanPolytope n ∧ l x = -2} := by
      ext x
      -- Rewrite the equality face with the strong-dual cut functional.
      simpa [l, subtourCutStrongDual_apply] using
        (mem_subtour_elimination_face_iff_neg_cutIncidence S x)
    have hxσ_poly : hamiltonian_tour_incidence_vector σ ∈ travelingSalesmanPolytope n :=
      (mem_subtour_elimination_face_iff S _).1 hσ_face |>.1
    have hxσ_eq : l (hamiltonian_tour_incidence_vector σ) = -2 := by
      -- The tight witness attains the exposing functional at the required value `-2`.
      simpa [l, subtourCutStrongDual_apply] using
        (mem_subtour_elimination_face_iff_neg_cutIncidence S
          (hamiltonian_tour_incidence_vector σ)).1 hσ_face |>.2
    rw [hface_eq, separatorEqualitySet_eq_toExposed_of_mem hvalid hxσ_poly hxσ_eq]
    exact ContinuousLinearMap.toExposed.isExposed
  · -- Finish with the codimension-one count on the normalized induced-edge equality slice.
    have hface_eq :
        subtour_elimination_face n S =
          {x | x ∈ travelingSalesmanPolytope n ∧
            Finset.sum (subtourInducedEdgeFinset S) x = (S.card : ℝ) - 1} := by
      ext x
      simpa using mem_subtour_elimination_face_iff_inducedEdgeSum_eq_card_sub_one
        (hn := hn) S x
    have hdir_le :
        (affineSpan ℝ (subtour_elimination_face n S)).direction ≤
          (affineSpan ℝ (travelingSalesmanPolytope n)).direction ⊓
            LinearMap.ker (subtourInducedSumLinearMap S) := by
      -- The normalized induced-edge equation already forces the easy kernel-side inclusion.
      exact subtourFaceDirection_le_ambientDirection_inf_inducedKer hn S hS_lower hS_upper
    let D : Submodule ℝ (complete_graph_edges n → ℝ) :=
      (affineSpan ℝ (travelingSalesmanPolytope n)).direction
    obtain ⟨w, hwD, hw_eval⟩ :=
      existsAmbientDirectionEvalOne_subtourInducedSum hn S hS_lower hS_upper
    have hcodim :
        Module.finrank ℝ ↥(D ⊓ LinearMap.ker (subtourInducedSumLinearMap S)) + 1 =
          Module.finrank ℝ ↥D := by
      -- The four-edge exchange witness makes the induced-edge functional nontrivial on the ambient
      -- direction, so the ambient kernel cut has codimension one.
      simpa [D] using
        submodule_finrank_inf_ker_add_one_of_eval_one
          D (subtourInducedSumLinearMap S) hwD hw_eval
    have hreverse :
        D ⊓ LinearMap.ker (subtourInducedSumLinearMap S) ≤
          (affineSpan ℝ (subtour_elimination_face n S)).direction := by
      -- The remaining structural step is the reverse inclusion promised by the anchored-swap
      -- source proof.
      simpa [D] using
        ambientDirectionInfInducedKer_le_subtourFaceDirection hn S hS_lower hS_upper
    have hdir_eq :
        (affineSpan ℝ (subtour_elimination_face n S)).direction =
          D ⊓ LinearMap.ker (subtourInducedSumLinearMap S) := by
      -- The easy inclusion was already proved above, so the reverse inclusion gives equality.
      exact le_antisymm hdir_le hreverse
    -- With the direction equality in hand, the codimension-one kernel computation finishes the
    -- facet dimension claim immediately.
    calc
      Module.finrank ℝ (affineSpan ℝ (subtour_elimination_face n S)).direction + 1
          = Module.finrank ℝ ↥(D ⊓ LinearMap.ker (subtourInducedSumLinearMap S)) + 1 := by
              rw [hdir_eq]
      _ = Module.finrank ℝ ↥D := hcodim
      _ = Module.finrank ℝ (affineSpan ℝ (travelingSalesmanPolytope n)).direction := by
            rfl

end Theorem719

#print axioms subtour_elimination_face_isFacetOf
