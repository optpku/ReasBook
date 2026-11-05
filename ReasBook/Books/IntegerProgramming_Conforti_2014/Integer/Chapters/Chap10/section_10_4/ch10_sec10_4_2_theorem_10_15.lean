/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_4.ch10_sec10_4_2_proposition_10_13

section Theorem_10_15

universe u

variable {V : Type u} [DecidableEq V]
variable (G : SimpleGraph V)

/-- The localizing matrix for the nonnegativity constraint `x_a ≥ 0` in `FRAC(G)`. -/
def frac_vertex_nonneg_localizing_matrix
    (t : ℕ) (y : Finset V → ℝ) (a : V) :
    Matrix {I : Finset V // I.card ≤ t} {J : Finset V // J.card ≤ t} ℝ :=
  fun I J ↦ y (insert a (I ∪ J))

/-- The localizing matrix for the upper-bound constraint `1 - x_a ≥ 0` in `FRAC(G)`. -/
def frac_vertex_slack_localizing_matrix
    (t : ℕ) (y : Finset V → ℝ) (a : V) :
    Matrix {I : Finset V // I.card ≤ t} {J : Finset V // J.card ≤ t} ℝ :=
  fun I J ↦ y (I ∪ J) - y (insert a (I ∪ J))

/-- The localizing matrix for the edge inequality `1 - x_a - x_b ≥ 0` in `FRAC(G)`. -/
def frac_edge_slack_localizing_matrix
    (t : ℕ) (y : Finset V → ℝ) (a b : V) :
    Matrix {I : Finset V // I.card ≤ t} {J : Finset V // J.card ≤ t} ℝ :=
  fun I J ↦ y (I ∪ J) - y (insert a (I ∪ J)) - y (insert b (I ∪ J))

/-- The alternating sum over the subsets `S` with `I ⊆ S ⊆ I ∪ J`, parameterized by subsets of
`J`. -/
def alternating_extension_sum
    (I J : Finset V) (f : Finset V → ℝ) : ℝ :=
  Finset.sum J.powerset (fun s ↦ (-1 : ℝ) ^ s.card * f (I ∪ s))

/-- The graph-specific scalar inequalities obtained from the `FRAC(G)` localizing matrices by the
alternating-sum test used in the proof of Theorem 10.15. These are proof-side witnesses for the
localizing constraints that the source derives from the vanishing characterization of
`K_t(FRAC(G))`. -/
def SatisfiesFracConstraints
    (t : ℕ) (y : Finset V → ℝ) : Prop :=
  (∀ ⦃a b : V⦄, G.Adj a b →
    ∀ I J : Finset V, Disjoint I J → I.card + J.card ≤ t →
      0 ≤ alternating_extension_sum I J
        (fun S ↦ y S - y (insert a S) - y (insert b S))) ∧
    (∀ a : V,
      ∀ I J : Finset V, Disjoint I J → I.card + J.card ≤ t →
        0 ≤ alternating_extension_sum I J (fun S ↦ y (insert a S))) ∧
    ∀ a : V,
      ∀ I J : Finset V, Disjoint I J → I.card + J.card ≤ t →
        0 ≤ alternating_extension_sum I J (fun S ↦ y S - y (insert a S))

/-- The graph-specific Lasserre step `K_t(FRAC(G))`: a normalized order-`t + 1`
subset-moment vector in `K_t t` whose order-`t` localizing matrices for the defining
inequalities of `FRAC(G)` are positive semidefinite. Theorem 10.15 later characterizes these
points by vanishing on small non-stable sets. -/
def frac_lasserre_relaxation
    (t : ℕ) : Set (Finset V → ℝ) :=
  {y | y ∈ K_t t ∧
      (∀ a : V, (frac_vertex_nonneg_localizing_matrix t y a).PosSemidef) ∧
      (∀ a : V, (frac_vertex_slack_localizing_matrix t y a).PosSemidef) ∧
      ∀ ⦃a b : V⦄, G.Adj a b → (frac_edge_slack_localizing_matrix t y a b).PosSemidef}

/-- Membership in `frac_lasserre_relaxation G t` means belonging to the canonical order-`t + 1`
moment relaxation `K_t t` together with the order-`t` positive-semidefinite localizing-matrix
constraints for `FRAC(G)`. -/
theorem mem_frac_lasserre_relaxation_iff
    (t : ℕ) (y : Finset V → ℝ) :
    y ∈ frac_lasserre_relaxation G t ↔
      y ∈ K_t t ∧
        (∀ a : V, (frac_vertex_nonneg_localizing_matrix t y a).PosSemidef) ∧
        (∀ a : V, (frac_vertex_slack_localizing_matrix t y a).PosSemidef) ∧
        ∀ ⦃a b : V⦄, G.Adj a b → (frac_edge_slack_localizing_matrix t y a b).PosSemidef :=
  Iff.rfl

/-- Helper for Theorem 10.15: reindex the inner alternating sum over covering subsets by the
overlap with the fixed subset `h`. -/
lemma innerAlternatingCoverSum_eq
    (S h : Finset V) (hh : h ⊆ S) :
    Finset.sum (S.powerset.filter (fun k ↦ h ∪ k = S))
      (fun k ↦ (-1 : ℤ) ^ (h.card + k.card)) =
      Finset.sum h.powerset (fun t ↦ (-1 : ℤ) ^ (S.card + t.card)) := by
  classical
  -- Reindex the covering subsets `k` by their overlap `t := h ∩ k`.
  refine (Finset.sum_bij
    (fun t _ ↦ S \ h ∪ t)
    ?_
    ?_
    ?_
    ?_).symm
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · refine Finset.union_subset Finset.sdiff_subset ((Finset.mem_powerset.mp ht).trans hh)
    · rw [← Finset.union_assoc, Finset.union_sdiff_of_subset hh]
      exact Finset.union_eq_left.mpr ((Finset.mem_powerset.mp ht).trans hh)
  · intro t₁ ht₁ t₂ ht₂ hEq
    have ht₁Sub : t₁ ⊆ h := Finset.mem_powerset.mp ht₁
    have ht₂Sub : t₂ ⊆ h := Finset.mem_powerset.mp ht₂
    have hdis₁ : Disjoint (S \ h) t₁ := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxS hxT
      exact (Finset.mem_sdiff.mp hxS).2 (ht₁Sub hxT)
    have hdis₂ : Disjoint (S \ h) t₂ := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxS hxT
      exact (Finset.mem_sdiff.mp hxS).2 (ht₂Sub hxT)
    have := congrArg (fun u ↦ u \ (S \ h)) hEq
    simpa [Finset.union_sdiff_cancel_left hdis₁, Finset.union_sdiff_cancel_left hdis₂] using this
  · intro k hk
    rw [Finset.mem_filter] at hk
    refine ⟨h ∩ k, ?_, ?_⟩
    · simp
    · have hsdiff : S \ h = k \ h := by
        rw [← hk.2, Finset.union_sdiff_left]
      calc
        S \ h ∪ (h ∩ k) = k \ h ∪ (h ∩ k) := by rw [hsdiff]
        _ = k := by rw [Finset.inter_comm, Finset.sdiff_union_inter]
  · intro t ht
    have htSub : t ⊆ h := Finset.mem_powerset.mp ht
    have hdis : Disjoint (S \ h) t := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxS hxT
      exact (Finset.mem_sdiff.mp hxS).2 (htSub hxT)
    have hbase : (S \ h).card + h.card = S.card := Finset.card_sdiff_add_card_eq_card hh
    -- The reindexing preserves the exponent after collapsing the disjoint union cardinality.
    have hcard : h.card + (S \ h ∪ t).card = S.card + t.card := by
      rw [Finset.card_union_of_disjoint hdis]
      omega
    exact congrArg (fun n : ℕ ↦ (-1 : ℤ) ^ n) hcard.symm

/-- Lemma 10.16. For a finite set `S`, the alternating sum over pairs of subsets `H, K ⊆ S`
with `H ∪ K = S` is `(-1) ^ |S|`. -/
theorem alternating_cover_sum_eq
    (S : Finset V) :
    Finset.sum S.powerset
        (fun h ↦
          Finset.sum (S.powerset.filter (fun k ↦ h ∪ k = S))
            (fun k ↦ (-1 : ℤ) ^ (h.card + k.card))) =
      (-1 : ℤ) ^ S.card := by
  classical
  -- First rewrite each inner covering sum using the overlap reindexing helper.
  calc
    Finset.sum S.powerset
        (fun h ↦
          Finset.sum (S.powerset.filter (fun k ↦ h ∪ k = S))
            (fun k ↦ (-1 : ℤ) ^ (h.card + k.card)))
        = Finset.sum S.powerset (fun h ↦ (-1 : ℤ) ^ S.card * (if h = ∅ then 1 else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro h hh
            rw [innerAlternatingCoverSum_eq S h (Finset.mem_powerset.mp hh)]
            -- Collapse the reindexed powerset sum using the standard alternating identity.
            calc
              Finset.sum h.powerset (fun t ↦ (-1 : ℤ) ^ (S.card + t.card))
                  = (-1 : ℤ) ^ S.card * (Finset.sum h.powerset (fun t ↦ (-1 : ℤ) ^ t.card)) := by
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl ?_
                      intro t ht
                      rw [← Int.pow_add]
              _ = (-1 : ℤ) ^ S.card * (if h = ∅ then 1 else 0) := by
                    rw [Finset.sum_powerset_neg_one_pow_card]
    -- Only the empty subset contributes to the outer sum.
    _ = (-1 : ℤ) ^ S.card := by
          let f : Finset V → ℤ := fun h ↦ (-1 : ℤ) ^ S.card * (if h = ∅ then 1 else 0)
          have hSingle : ∑ h ∈ S.powerset, f h = f ∅ :=
            Finset.sum_eq_single_of_mem ∅ (by simp)
              (by
                intro h hh hne
                simp [f, hne])
          simp [f] at hSingle ⊢

omit [DecidableEq V] in
/-- Helper for Theorem 10.15: a finite set that is not independent contains an adjacent pair. -/
lemma exists_adj_of_not_isIndepSet
    {I : Finset V} (hI : ¬ G.IsIndepSet I) :
    ∃ a ∈ I, ∃ b ∈ I, G.Adj a b := by
  -- Rewrite non-independence into the existence of two adjacent vertices inside `I`.
  rw [SimpleGraph.isIndepSet_iff] at hI
  simp only [Set.Pairwise, Finset.mem_coe] at hI
  push Not at hI
  rcases hI with ⟨a, ha, b, hb, _, hab⟩
  exact ⟨a, ha, b, hb, hab⟩

/-- Helper for Theorem 10.15: the PSD localizing constraints force vanishing on every non-stable
set of size at most `t + 1`. -/
lemma smallNonstableMoment_eq_zero_of_memFracLasserre
    {t : ℕ} {y : Finset V → ℝ}
    (hy : y ∈ frac_lasserre_relaxation G t)
    {I : Finset V}
    (hIcard : I.card ≤ t + 1)
    (hI : ¬ G.IsIndepSet I) :
    y I = 0 := by
  obtain ⟨hyK, hVertexNonneg, _, hEdgeSlack⟩ := (mem_frac_lasserre_relaxation_iff (G := G) t y).1 hy
  obtain ⟨a, haI, b, hbI, hab⟩ := exists_adj_of_not_isIndepSet (G := G) hI
  have habne : a ≠ b := hab.ne
  have hbne : b ≠ a := by simpa [eq_comm] using habne
  have hbErase : b ∈ I.erase a := by
    simp [hbI, hbne]
  have hEraseCard : (I.erase a).card ≤ t := by
    have hCardEq : (I.erase a).card + 1 = I.card := Finset.card_erase_add_one haI
    omega
  let K : {J : Finset V // J.card ≤ t} := ⟨I.erase a, hEraseCard⟩
  have hNonnegDiag :
      0 ≤ (frac_vertex_nonneg_localizing_matrix t y a) K K :=
    (hVertexNonneg a).diag_nonneg (i := K)
  have hEdgeDiag :
      0 ≤ (frac_edge_slack_localizing_matrix t y a b) K K :=
    (hEdgeSlack hab).diag_nonneg (i := K)
  have hyNonneg : 0 ≤ y I := by
    -- The vertex nonnegativity localizing matrix reads off the `I`-coordinate on this diagonal.
    simpa [frac_vertex_nonneg_localizing_matrix, K, haI] using hNonnegDiag
  have hyNonpos : 0 ≤ -y I := by
    -- The edge-slack diagonal collapses to `-y I` because `b` is already in `I.erase a`.
    simpa [frac_edge_slack_localizing_matrix, K, haI, hbErase] using hEdgeDiag
  linarith

/-- Helper for Theorem 10.15: a small non-stable set splits as a union of two sets of size at
most `t + 1`, with one part still non-stable. -/
lemma existsSmallNonstableUnion
    {t : ℕ} (ht : 1 ≤ t)
    {I : Finset V}
    (hIcard : I.card ≤ 2 * t + 2)
    (hI : ¬ G.IsIndepSet I) :
    ∃ I₁ I₂ : Finset V,
      I = I₁ ∪ I₂ ∧
      I₁.card ≤ t + 1 ∧
      I₂.card ≤ t + 1 ∧
      ¬ G.IsIndepSet I₁ := by
  classical
  obtain ⟨a, haI, b, hbI, hab⟩ := exists_adj_of_not_isIndepSet (G := G) hI
  have habne : a ≠ b := hab.ne
  have hbne : b ≠ a := by simpa [eq_comm] using habne
  have hbErase : b ∈ I.erase a := by
    simp [hbI, hbne]
  let R : Finset V := (I.erase a).erase b
  have hRcard :
      R.card + 2 = I.card := by
    -- Removing the adjacent witnesses leaves the remaining vertices of `I`.
    have hEraseA : (I.erase a).card + 1 = I.card := Finset.card_erase_add_one haI
    have hEraseB : R.card + 1 = (I.erase a).card := by
      simpa [R] using Finset.card_erase_add_one hbErase
    omega
  by_cases hRsmall : R.card ≤ t - 1
  · -- If the remainder is already short, keep all of `I` in the non-stable part.
    refine ⟨I, ∅, by simp, ?_, by simp, hI⟩
    omega
  · -- Otherwise choose exactly `t - 1` remaining vertices to join the adjacent pair.
    have hLower : t - 1 ≤ R.card := Nat.le_of_not_ge hRsmall
    obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hLower
    let I₁ : Finset V := insert a (insert b J)
    let I₂ : Finset V := I \ I₁
    have hJInI : J ⊆ I :=
      hJsub.trans <| (Finset.erase_subset b (I.erase a)).trans (Finset.erase_subset a I)
    have haNotJ : a ∉ J := by
      intro haJ
      have : a ∈ R := hJsub haJ
      simp [R] at this
    have hbNotJ : b ∉ J := by
      intro hbJ
      have : b ∈ R := hJsub hbJ
      simp [R] at this
    have haNotInsertBJ : a ∉ insert b J := by
      simp [haNotJ, habne]
    have hI₁sub : I₁ ⊆ I := by
      intro x hx
      simp only [I₁, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact haI
      rcases hx with rfl | hx
      · exact hbI
      · exact hJInI hx
    have hI₁card : I₁.card ≤ t + 1 := by
      -- `I₁` consists of the chosen `t - 1` vertices together with the adjacent pair `a,b`.
      dsimp [I₁]
      rw [Finset.card_insert_of_notMem haNotInsertBJ, Finset.card_insert_of_notMem hbNotJ, hJcard]
      omega
    have hI₂card : I₂.card ≤ t + 1 := by
      -- The complement carries the remaining vertices inside the `2 * t + 2` bound.
      have hCardEq : I₂.card = I.card - I₁.card := by
        simp [I₂, Finset.card_sdiff_of_subset hI₁sub]
      have hI₁cardEq : I₁.card = t + 1 := by
        dsimp [I₁]
        rw [Finset.card_insert_of_notMem haNotInsertBJ, Finset.card_insert_of_notMem hbNotJ, hJcard]
        omega
      rw [hCardEq, hI₁cardEq]
      omega
    have hNonstable : ¬ G.IsIndepSet I₁ := by
      -- The adjacent pair `a,b` remains inside `I₁`.
      intro hI₁
      rw [SimpleGraph.isIndepSet_iff] at hI₁
      have haI₁ : a ∈ I₁ := by simp [I₁]
      have hbI₁ : b ∈ I₁ := by simp [I₁]
      exact (hI₁ haI₁ hbI₁ habne) hab
    refine ⟨I₁, I₂, ?_, hI₁card, hI₂card, hNonstable⟩
    -- Reassemble `I` from the chosen non-stable part and its complement.
    symm
    exact Finset.union_sdiff_of_subset hI₁sub

/-- Helper for Theorem 10.15: the `x_a ≥ 0` localizing matrix is a principal submatrix of the
moment matrix. -/
lemma fracVertexNonnegPosSemidef_of_mem_K_t
    {t : ℕ} {y : Finset V → ℝ}
    (hyK : y ∈ K_t t) (a : V) :
    (frac_vertex_nonneg_localizing_matrix t y a).PosSemidef := by
  let e :
      {I : Finset V // I.card ≤ t} →
        {J : Finset V // J.card ≤ t + 1} :=
    fun I ↦ ⟨insert a I.1, (Finset.card_insert_le a I.1).trans (Nat.succ_le_succ I.2)⟩
  have hSub :
      (lasserre_moment_matrix t y).submatrix e e =
        frac_vertex_nonneg_localizing_matrix t y a := by
    -- The chosen principal submatrix records exactly the coordinates `y (insert a (I ∪ J))`.
    ext I J
    simp [e, frac_vertex_nonneg_localizing_matrix, lasserre_moment_matrix,
      Finset.insert_union]
  -- Restrict the moment matrix along the map `I ↦ insert a I`.
  rw [← hSub]
  exact (K_t.posSemidef hyK).submatrix e

/-- Helper for Theorem 10.15: adjoining zero rows and columns to a positive semidefinite block
preserves positive semidefiniteness. -/
lemma fromBlocksZeroPosSemidef
    {α β : Type*}
    {L : Matrix α α ℝ} (hL : L.PosSemidef) :
    (Matrix.fromBlocks L 0 0 (0 : Matrix β β ℝ)).PosSemidef := by
  refine ⟨?_, ?_⟩
  · -- The zero-extension keeps the Hermitian block structure of `L`.
    have hZeroCross : Matrix.conjTranspose (0 : Matrix α β ℝ) = (0 : Matrix β α ℝ) := by
      simp
    exact Matrix.IsHermitian.fromBlocks hL.1 hZeroCross Matrix.isHermitian_zero
  · intro x
    let xL : α →₀ ℝ := Finsupp.comapDomain Sum.inl x Sum.inl_injective.injOn
    let xR : β →₀ ℝ := Finsupp.comapDomain Sum.inr x Sum.inr_injective.injOn
    have hx : xL.sumElim xR = x := by
      -- Split the test vector into its left and right components once and for all.
      simp [xL, xR]
    -- The zero blocks discard every term involving the right component.
    rw [← hx]
    simpa [Finsupp.sum, Finsupp.sumElim, Finset.sum_disjSum,
      Matrix.fromBlocks] using hL.2 xL

/-- Helper for Theorem 10.15: positive semidefiniteness of the two-block matrix with blocks
`A, B, B, B` implies positive semidefiniteness of `A - B`. -/
lemma twoBlockDifferencePosSemidef
    {α : Type*} {A B : Matrix α α ℝ}
    (hBlock : (Matrix.fromBlocks A B B B).PosSemidef) :
    (A - B).PosSemidef := by
  refine ⟨?_, ?_⟩
  · -- The diagonal principal blocks show that both `A` and `B` are Hermitian.
    have hA : A.IsHermitian := by
      simpa using hBlock.1.submatrix Sum.inl
    have hB : B.IsHermitian := by
      simpa using hBlock.1.submatrix Sum.inr
    exact hA.sub hB
  · intro x
    have hDifference :
        x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi * (A - B) i j * xj) =
          x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi * A i j * xj) -
            x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi * B i j * xj) := by
      -- Distribute the finite quadratic-form sum over matrix subtraction.
      simp [Finsupp.sum, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [hDifference, sub_nonneg]
    -- Testing the block matrix on `(-x, x)` leaves precisely the quadratic form of `A - B`.
    simpa [Finsupp.sum, Finsupp.sumElim, Finset.sum_disjSum,
      Matrix.fromBlocks, Finset.sum_add_distrib, Finset.sum_neg_distrib] using
      hBlock.2 ((-x).sumElim x)

/-- Helper for Theorem 10.15: the union of two order-`t` localizing indices has size at most
`2 * t`. -/
lemma card_union_le_two_mul
    {t : ℕ} {I J : Finset V}
    (hI : I.card ≤ t) (hJ : J.card ≤ t) :
    (I ∪ J).card ≤ 2 * t := by
  -- The union cannot be larger than the sum of the two cardinalities.
  have hUnion : (I ∪ J).card ≤ I.card + J.card := Finset.card_union_le I J
  omega

/-- Helper for Theorem 10.15: the vertex-slack entry vanishes on any set already containing
`a`. -/
lemma vertexSlackValue_eq_zero_of_mem
    {y : Finset V → ℝ} {a : V} {U : Finset V}
    (haU : a ∈ U) :
    y U - y (insert a U) = 0 := by
  -- Once `a` is already present, the two coordinates coincide.
  simp [haU]

omit [DecidableEq V] in
/-- Helper for Theorem 10.15: any small set containing the adjacent vertices `a` and `b` has
zero moment coordinate. -/
lemma momentValue_eq_zero_of_containsAdj
    {t : ℕ} {y : Finset V → ℝ}
    (hzero : ∀ I : Finset V, I.card ≤ 2 * t + 2 → ¬ G.IsIndepSet I → y I = 0)
    {a b : V} (hab : G.Adj a b)
    {U : Finset V}
    (haU : a ∈ U) (hbU : b ∈ U)
    (hU : U.card ≤ 2 * t + 2) :
    y U = 0 := by
  -- Any set containing an edge is automatically non-stable.
  apply hzero U hU
  intro hInd
  rw [SimpleGraph.isIndepSet_iff] at hInd
  exact (hInd haU hbU hab.ne) hab

/-- Helper for Theorem 10.15: the order-`t` localizing indices. -/
abbrev localizingIdx (t : ℕ) :=
  {I : Finset V // I.card ≤ t}

/-- Helper for Theorem 10.15: the order-`t` localizing indices avoiding `a`. -/
abbrev vertexAvoidIdx (t : ℕ) (a : V) :=
  {I : localizingIdx (V := V) t // a ∉ I.1}

/-- Helper for Theorem 10.15: the order-`t` localizing indices containing `a`. -/
abbrev vertexHitIdx (t : ℕ) (a : V) :=
  {I : localizingIdx (V := V) t // ¬ a ∉ I.1}

/-- Helper for Theorem 10.15: the order-`t` localizing indices avoiding both endpoints. -/
abbrev edgeAvoidIdx (t : ℕ) (a b : V) :=
  {I : localizingIdx (V := V) t // a ∉ I.1 ∧ b ∉ I.1}

/-- Helper for Theorem 10.15: the order-`t` localizing indices meeting at least one endpoint. -/
abbrev edgeHitIdx (t : ℕ) (a b : V) :=
  {I : localizingIdx (V := V) t // ¬ (a ∉ I.1 ∧ b ∉ I.1)}

/-- Helper for Theorem 10.15: the reduced vertex-slack block on indices avoiding `a`. -/
def vertexSlackReducedMatrix
    (t : ℕ) (y : Finset V → ℝ) (a : V) :
    Matrix (vertexAvoidIdx (V := V) t a) (vertexAvoidIdx (V := V) t a) ℝ :=
  fun I J ↦ y (I.1.1 ∪ J.1.1) - y (insert a (I.1.1 ∪ J.1.1))

/-- Helper for Theorem 10.15: the reduced edge-slack block on indices avoiding both endpoints. -/
def edgeSlackReducedMatrix
    (t : ℕ) (y : Finset V → ℝ) (a b : V) :
    Matrix (edgeAvoidIdx (V := V) t a b) (edgeAvoidIdx (V := V) t a b) ℝ :=
  fun I J ↦ y (I.1.1 ∪ J.1.1) - y (insert a (I.1.1 ∪ J.1.1)) -
    y (insert b (I.1.1 ∪ J.1.1))

/-- Helper for Theorem 10.15: the source `A - B - C` argument is encoded by the three-block
matrix with diagonal blocks `A`, `B`, `C` and the single nonzero off-diagonal blocks `B` and
`C`. -/
def edgeThreeBlockMatrix
    {α : Type*} (A B C : Matrix α α ℝ) :
    Matrix (α ⊕ (α ⊕ α)) (α ⊕ (α ⊕ α)) ℝ
  | Sum.inl i, Sum.inl j => A i j
  | Sum.inl i, Sum.inr (Sum.inl j) => B i j
  | Sum.inl i, Sum.inr (Sum.inr j) => C i j
  | Sum.inr (Sum.inl i), Sum.inl j => B i j
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => B i j
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 0
  | Sum.inr (Sum.inr i), Sum.inl j => C i j
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) => C i j

/-- Helper for Theorem 10.15: positive semidefiniteness of the three-block matrix implies
positive semidefiniteness of the Schur-style difference `A - B - C`. -/
lemma threeBlockDifferencePosSemidef
    {α : Type*} {A B C : Matrix α α ℝ}
    (hBlock : (edgeThreeBlockMatrix A B C).PosSemidef) :
    (A - B - C).PosSemidef := by
  refine ⟨?_, ?_⟩
  · -- Each diagonal block is Hermitian because it is a principal submatrix.
    have hA : A.IsHermitian := by
      simpa [edgeThreeBlockMatrix] using hBlock.1.submatrix Sum.inl
    have hB : B.IsHermitian := by
      simpa [edgeThreeBlockMatrix] using
        hBlock.1.submatrix (fun i ↦ Sum.inr (Sum.inl i))
    have hC : C.IsHermitian := by
      simpa [edgeThreeBlockMatrix] using
        hBlock.1.submatrix (fun i ↦ Sum.inr (Sum.inr i))
    exact (hA.sub hB).sub hC
  · intro x
    have hDifference :
        x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi * (A - B - C) i j * xj) =
          x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi * A i j * xj) -
            x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi * B i j * xj) -
              x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi * C i j * xj) := by
      -- Distribute the finite quadratic-form sum over the two matrix subtractions.
      simp [Finsupp.sum, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
    have hTest := hBlock.2 ((-x).sumElim (x.sumElim x))
    -- The test vector `(-x, x, x)` cancels both duplicated diagonal blocks.
    simp [Finsupp.sum, Finsupp.sumElim, Finset.sum_disjSum,
      edgeThreeBlockMatrix, Finset.sum_add_distrib, Finset.sum_neg_distrib] at hTest
    rw [hDifference]
    simp only [star_trivial, Finsupp.sum]
    linarith

/-- Helper for Theorem 10.15: for endpoint-avoiding localizing indices, the moment indexed by
adjoining both adjacent endpoints vanishes. -/
lemma edgeAvoidInsertedPair_eq_zero
    {t : ℕ} {y : Finset V → ℝ}
    (hzero : ∀ I : Finset V, I.card ≤ 2 * t + 2 → ¬ G.IsIndepSet I → y I = 0)
    {a b : V} (hab : G.Adj a b)
    (I J : edgeAvoidIdx (V := V) t a b) :
    y (insert a (insert b (I.1.1 ∪ J.1.1))) = 0 := by
  have hUnion : (I.1.1 ∪ J.1.1).card ≤ 2 * t := card_union_le_two_mul I.1.2 J.1.2
  have hCard :
      (insert a (insert b (I.1.1 ∪ J.1.1))).card ≤ 2 * t + 2 := by
    have hInsertB :
        (insert b (I.1.1 ∪ J.1.1)).card ≤ (I.1.1 ∪ J.1.1).card + 1 :=
      Finset.card_insert_le b (I.1.1 ∪ J.1.1)
    have hInsertA :
        (insert a (insert b (I.1.1 ∪ J.1.1))).card ≤ (insert b (I.1.1 ∪ J.1.1)).card + 1 :=
      Finset.card_insert_le a (insert b (I.1.1 ∪ J.1.1))
    omega
  -- The enlarged set contains the edge `{a,b}`, so the vanishing hypothesis applies.
  exact momentValue_eq_zero_of_containsAdj (G := G) hzero hab (by simp) (by simp) hCard

/-- Helper for Theorem 10.15: splitting the localizing indices by whether `a` is present turns
the vertex-slack matrix into a zero-extension of its endpoint-avoiding block. -/
lemma vertexSlackReindex_eq_fromBlocksZero
    {t : ℕ} {y : Finset V → ℝ} (a : V) :
    (Matrix.reindex
        (Equiv.sumCompl fun I : localizingIdx (V := V) t ↦ a ∉ I.1).symm
        (Equiv.sumCompl fun I : localizingIdx (V := V) t ↦ a ∉ I.1).symm
        (frac_vertex_slack_localizing_matrix t y a)) =
      Matrix.fromBlocks (vertexSlackReducedMatrix (V := V) t y a) 0 0
        (0 : Matrix (vertexHitIdx (V := V) t a) (vertexHitIdx (V := V) t a) ℝ) := by
  classical
  ext i j
  rcases i with I | I <;> rcases j with J | J
  · -- The endpoint-avoiding block is exactly the reduced matrix.
    simp [Matrix.reindex_apply, frac_vertex_slack_localizing_matrix, vertexSlackReducedMatrix,
      Equiv.sumCompl_apply_inl]
  · -- Any column index containing `a` forces the slack entry to vanish.
    have haJ : a ∈ J.1.1 := by simpa using J.2
    have haU : a ∈ I.1.1 ∪ J.1.1 := Finset.mem_union.mpr (Or.inr haJ)
    simpa [Matrix.reindex_apply, Matrix.fromBlocks, frac_vertex_slack_localizing_matrix,
      Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr] using
      vertexSlackValue_eq_zero_of_mem (y := y) (a := a) haU
  · -- Any row index containing `a` forces the slack entry to vanish.
    have haI : a ∈ I.1.1 := by simpa using I.2
    have haU : a ∈ I.1.1 ∪ J.1.1 := Finset.mem_union.mpr (Or.inl haI)
    simpa [Matrix.reindex_apply, Matrix.fromBlocks, frac_vertex_slack_localizing_matrix,
      Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr] using
      vertexSlackValue_eq_zero_of_mem (y := y) (a := a) haU
  · -- If both indices hit `a`, the same vanishing argument still applies.
    have haI : a ∈ I.1.1 := by simpa using I.2
    have haU : a ∈ I.1.1 ∪ J.1.1 := Finset.mem_union.mpr (Or.inl haI)
    simpa [Matrix.reindex_apply, Matrix.fromBlocks, frac_vertex_slack_localizing_matrix,
      Equiv.sumCompl_apply_inr] using
      vertexSlackValue_eq_zero_of_mem (y := y) (a := a) haU

/-- Helper for Theorem 10.15: the endpoint-avoiding vertex-slack block is positive
semidefinite. -/
lemma vertexSlackReducedPosSemidef
    {t : ℕ} {y : Finset V → ℝ}
    (hyK : y ∈ K_t t) (a : V) :
    (vertexSlackReducedMatrix (V := V) t y a).PosSemidef := by
  let A : Matrix (vertexAvoidIdx (V := V) t a) (vertexAvoidIdx (V := V) t a) ℝ :=
    fun I J ↦ y (I.1.1 ∪ J.1.1)
  let B : Matrix (vertexAvoidIdx (V := V) t a) (vertexAvoidIdx (V := V) t a) ℝ :=
    fun I J ↦ y (insert a (I.1.1 ∪ J.1.1))
  have hBaseCard (I : vertexAvoidIdx (V := V) t a) : I.1.1.card ≤ t + 1 :=
    I.1.2.trans (Nat.le_succ t)
  have hInsertCard (I : vertexAvoidIdx (V := V) t a) : (insert a I.1.1).card ≤ t + 1 :=
    (Finset.card_insert_le a I.1.1).trans (Nat.succ_le_succ I.1.2)
  let e :
      vertexAvoidIdx (V := V) t a ⊕ vertexAvoidIdx (V := V) t a →
        {I : Finset V // I.card ≤ t + 1}
    | Sum.inl I => ⟨I.1.1, hBaseCard I⟩
    | Sum.inr I => ⟨insert a I.1.1, hInsertCard I⟩
  have hBlockEq :
      (lasserre_moment_matrix t y).submatrix e e = Matrix.fromBlocks A B B B := by
    -- The two embeddings expose the moment blocks `A, B, B, B`.
    ext i j
    rcases i with I | I <;> rcases j with J | J <;>
      simp [e, A, B, lasserre_moment_matrix, Matrix.fromBlocks, Finset.union_insert,
        Finset.union_comm]
  have hBlockPsd : (Matrix.fromBlocks A B B B).PosSemidef := by
    rw [← hBlockEq]
    exact (K_t.posSemidef hyK).submatrix e
  -- The generic two-block test gives `A - B`, which is the reduced vertex-slack matrix.
  simpa [A, B, vertexSlackReducedMatrix] using twoBlockDifferencePosSemidef hBlockPsd

/-- Helper for Theorem 10.15: if a localizing union already contains `a` or `b`, then the
edge-slack scalar vanishes. -/
lemma edgeSlackValue_eq_zero_of_containsEndpoint
    {t : ℕ} {y : Finset V → ℝ}
    (hzero : ∀ I : Finset V, I.card ≤ 2 * t + 2 → ¬ G.IsIndepSet I → y I = 0)
    {a b : V} (hab : G.Adj a b)
    {U : Finset V}
    (hU : U.card ≤ 2 * t)
    (hhit : a ∈ U ∨ b ∈ U) :
    y U - y (insert a U) - y (insert b U) = 0 := by
  -- Split on which endpoint is already present and apply the vanishing hypothesis to the set
  -- that visibly contains the edge.
  by_cases haU : a ∈ U
  · by_cases hbU : b ∈ U
    · have hyU : y U = 0 := by
        exact momentValue_eq_zero_of_containsAdj (G := G) hzero hab haU hbU (by omega)
      simp [haU, hbU, hyU]
    · have hyInsertB : y (insert b U) = 0 := by
        have haInsert : a ∈ insert b U := by simp [haU]
        have hbInsert : b ∈ insert b U := by simp
        have hCardInsert : (insert b U).card ≤ 2 * t + 2 := by
          have hInsert : (insert b U).card ≤ U.card + 1 := Finset.card_insert_le b U
          omega
        exact momentValue_eq_zero_of_containsAdj (G := G) hzero hab haInsert hbInsert
          hCardInsert
      simp [haU, hyInsertB]
  · have hbU : b ∈ U := by
      rcases hhit with hhit | hhit
      · exact (haU hhit).elim
      · exact hhit
    have hyInsertA : y (insert a U) = 0 := by
      have haInsert : a ∈ insert a U := by simp
      have hbInsert : b ∈ insert a U := by simp [hbU]
      have hCardInsert : (insert a U).card ≤ 2 * t + 2 := by
        have hInsert : (insert a U).card ≤ U.card + 1 := Finset.card_insert_le a U
        omega
      exact momentValue_eq_zero_of_containsAdj (G := G) hzero hab haInsert hbInsert hCardInsert
    simp [hbU, hyInsertA]

/-- Helper for Theorem 10.15: splitting the localizing indices by whether `a` or `b` is present
turns the edge-slack matrix into a zero-extension of its endpoint-avoiding block. -/
lemma edgeSlackReindex_eq_fromBlocksZero
    {t : ℕ} {y : Finset V → ℝ}
    (hzero : ∀ I : Finset V, I.card ≤ 2 * t + 2 → ¬ G.IsIndepSet I → y I = 0)
    {a b : V} (hab : G.Adj a b) :
    (Matrix.reindex
        (Equiv.sumCompl fun I : localizingIdx (V := V) t ↦ a ∉ I.1 ∧ b ∉ I.1).symm
        (Equiv.sumCompl fun I : localizingIdx (V := V) t ↦ a ∉ I.1 ∧ b ∉ I.1).symm
        (frac_edge_slack_localizing_matrix t y a b)) =
      Matrix.fromBlocks (edgeSlackReducedMatrix (V := V) t y a b) 0 0
        (0 : Matrix (edgeHitIdx (V := V) t a b) (edgeHitIdx (V := V) t a b) ℝ) := by
  classical
  ext i j
  rcases i with I | I <;> rcases j with J | J
  · -- The endpoint-avoiding block is exactly the reduced edge-slack matrix.
    simp [Matrix.reindex_apply, frac_edge_slack_localizing_matrix, edgeSlackReducedMatrix,
      Equiv.sumCompl_apply_inl]
  · -- A hit column already contains one endpoint, so the edge-slack entry vanishes.
    have hU : (I.1.1 ∪ J.1.1).card ≤ 2 * t := card_union_le_two_mul I.1.2 J.1.2
    have hhitJ : a ∈ J.1.1 ∨ b ∈ J.1.1 := by
      by_cases haJ : a ∈ J.1.1
      · exact Or.inl haJ
      · have hbJ : b ∈ J.1.1 := by
          by_contra hbJ
          exact J.2 ⟨haJ, hbJ⟩
        exact Or.inr hbJ
    have hhitU : a ∈ I.1.1 ∪ J.1.1 ∨ b ∈ I.1.1 ∪ J.1.1 := by
      rcases hhitJ with haJ | hbJ
      · exact Or.inl (Finset.mem_union.mpr (Or.inr haJ))
      · exact Or.inr (Finset.mem_union.mpr (Or.inr hbJ))
    simpa [Matrix.reindex_apply, Matrix.fromBlocks, frac_edge_slack_localizing_matrix,
      Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr] using
      edgeSlackValue_eq_zero_of_containsEndpoint (G := G) (t := t) (y := y) hzero hab hU hhitU
  · -- A hit row already contains one endpoint, so the same vanishing applies.
    have hU : (I.1.1 ∪ J.1.1).card ≤ 2 * t := card_union_le_two_mul I.1.2 J.1.2
    have hhitI : a ∈ I.1.1 ∨ b ∈ I.1.1 := by
      by_cases haI : a ∈ I.1.1
      · exact Or.inl haI
      · have hbI : b ∈ I.1.1 := by
          by_contra hbI
          exact I.2 ⟨haI, hbI⟩
        exact Or.inr hbI
    have hhitU : a ∈ I.1.1 ∪ J.1.1 ∨ b ∈ I.1.1 ∪ J.1.1 := by
      rcases hhitI with haI | hbI
      · exact Or.inl (Finset.mem_union.mpr (Or.inl haI))
      · exact Or.inr (Finset.mem_union.mpr (Or.inl hbI))
    simpa [Matrix.reindex_apply, Matrix.fromBlocks, frac_edge_slack_localizing_matrix,
      Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr] using
      edgeSlackValue_eq_zero_of_containsEndpoint (G := G) (t := t) (y := y) hzero hab hU hhitU
  · -- When both indices hit, one endpoint is already present in the row block.
    have hU : (I.1.1 ∪ J.1.1).card ≤ 2 * t := card_union_le_two_mul I.1.2 J.1.2
    have hhitI : a ∈ I.1.1 ∨ b ∈ I.1.1 := by
      by_cases haI : a ∈ I.1.1
      · exact Or.inl haI
      · have hbI : b ∈ I.1.1 := by
          by_contra hbI
          exact I.2 ⟨haI, hbI⟩
        exact Or.inr hbI
    have hhitU : a ∈ I.1.1 ∪ J.1.1 ∨ b ∈ I.1.1 ∪ J.1.1 := by
      rcases hhitI with haI | hbI
      · exact Or.inl (Finset.mem_union.mpr (Or.inl haI))
      · exact Or.inr (Finset.mem_union.mpr (Or.inl hbI))
    simpa [Matrix.reindex_apply, Matrix.fromBlocks, frac_edge_slack_localizing_matrix,
      Equiv.sumCompl_apply_inr] using
      edgeSlackValue_eq_zero_of_containsEndpoint (G := G) (t := t) (y := y) hzero hab hU hhitU

/-- Helper for Theorem 10.15: the edge-slack block indexed by sets avoiding both endpoints is
positive semidefinite. -/
lemma edgeSlackReducedPosSemidef
    {t : ℕ} {y : Finset V → ℝ}
    (hyK : y ∈ K_t t)
    (hzero : ∀ I : Finset V, I.card ≤ 2 * t + 2 → ¬ G.IsIndepSet I → y I = 0)
    {a b : V} (hab : G.Adj a b) :
    (edgeSlackReducedMatrix (V := V) t y a b).PosSemidef := by
  let A : Matrix (edgeAvoidIdx (V := V) t a b) (edgeAvoidIdx (V := V) t a b) ℝ :=
    fun I J ↦ y (I.1.1 ∪ J.1.1)
  let B : Matrix (edgeAvoidIdx (V := V) t a b) (edgeAvoidIdx (V := V) t a b) ℝ :=
    fun I J ↦ y (insert a (I.1.1 ∪ J.1.1))
  let C : Matrix (edgeAvoidIdx (V := V) t a b) (edgeAvoidIdx (V := V) t a b) ℝ :=
    fun I J ↦ y (insert b (I.1.1 ∪ J.1.1))
  have hBaseCard (I : edgeAvoidIdx (V := V) t a b) : I.1.1.card ≤ t + 1 :=
    I.1.2.trans (Nat.le_succ t)
  have hInsertACard (I : edgeAvoidIdx (V := V) t a b) :
      (insert a I.1.1).card ≤ t + 1 :=
    (Finset.card_insert_le a I.1.1).trans (Nat.succ_le_succ I.1.2)
  have hInsertBCard (I : edgeAvoidIdx (V := V) t a b) :
      (insert b I.1.1).card ≤ t + 1 :=
    (Finset.card_insert_le b I.1.1).trans (Nat.succ_le_succ I.1.2)
  let e :
      edgeAvoidIdx (V := V) t a b ⊕
          (edgeAvoidIdx (V := V) t a b ⊕ edgeAvoidIdx (V := V) t a b) →
        {I : Finset V // I.card ≤ t + 1}
    | Sum.inl I => ⟨I.1.1, hBaseCard I⟩
    | Sum.inr (Sum.inl I) => ⟨insert a I.1.1, hInsertACard I⟩
    | Sum.inr (Sum.inr I) => ⟨insert b I.1.1, hInsertBCard I⟩
  have hBlockEq :
      (lasserre_moment_matrix t y).submatrix e e = edgeThreeBlockMatrix A B C := by
    -- The three embeddings expose the `A`, `B`, and `C` moment blocks; adjacency kills the
    -- two mixed endpoint blocks.
    ext i j
    rcases i with I | (I | I)
    · rcases j with J | (J | J)
      · simp [e, A, edgeThreeBlockMatrix, lasserre_moment_matrix]
      · simp [e, B, edgeThreeBlockMatrix, lasserre_moment_matrix, Finset.union_insert]
      · simp [e, C, edgeThreeBlockMatrix, lasserre_moment_matrix, Finset.union_insert]
    · rcases j with J | (J | J)
      · simp [e, B, edgeThreeBlockMatrix, lasserre_moment_matrix, Finset.union_insert,
          Finset.union_comm]
      · simp [e, B, edgeThreeBlockMatrix, lasserre_moment_matrix, Finset.union_insert,
          Finset.union_comm]
      · have hMixed := edgeAvoidInsertedPair_eq_zero (G := G) hzero hab I J
        simpa [e, edgeThreeBlockMatrix, lasserre_moment_matrix, Finset.union_insert,
          Finset.insert_union, Finset.insert_comm, Finset.union_assoc, Finset.union_left_comm,
          Finset.union_comm] using hMixed
    · rcases j with J | (J | J)
      · simp [e, C, edgeThreeBlockMatrix, lasserre_moment_matrix, Finset.union_insert,
          Finset.union_comm]
      · have hMixed := edgeAvoidInsertedPair_eq_zero (G := G) hzero hab J I
        simpa [e, edgeThreeBlockMatrix, lasserre_moment_matrix, Finset.union_insert,
          Finset.insert_union, Finset.insert_comm, Finset.union_assoc, Finset.union_left_comm,
          Finset.union_comm] using hMixed
      · simp [e, C, edgeThreeBlockMatrix, lasserre_moment_matrix, Finset.union_insert,
          Finset.union_comm]
  have hBlockPsd : (edgeThreeBlockMatrix A B C).PosSemidef := by
    rw [← hBlockEq]
    exact (K_t.posSemidef hyK).submatrix e
  -- The generic three-block test yields the reduced edge-slack matrix `A - B - C`.
  simpa [A, B, C, edgeSlackReducedMatrix] using threeBlockDifferencePosSemidef hBlockPsd

/-- Helper for Theorem 10.15: the reverse inclusion only needs the vertex-nonneg localizing
matrix directly from `K_t`; the slack matrices are handled separately. -/
lemma fracVertexSlackPosSemidef_of_zeroOnSmallNonstable
    {t : ℕ} {y : Finset V → ℝ}
    (hyK : y ∈ K_t t)
    (a : V) :
    (frac_vertex_slack_localizing_matrix t y a).PosSemidef := by
  classical
  -- Route correction: reduce to the block `A - B` cut from the moment matrix on sets avoiding
  -- `a`; rows indexed by sets containing `a` vanish, so the full matrix is a zero-extension.
  let Idx := {I : Finset V // I.card ≤ t}
  let p : Idx → Prop := fun I => a ∉ I.1
  have hLpsd : (vertexSlackReducedMatrix (V := V) t y a).PosSemidef := by
    simpa using vertexSlackReducedPosSemidef (V := V) hyK a
  have hReindex :
      (Matrix.reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm
          (frac_vertex_slack_localizing_matrix t y a)) =
        Matrix.fromBlocks (vertexSlackReducedMatrix (V := V) t y a) 0 0
          (0 : Matrix (vertexHitIdx (V := V) t a) (vertexHitIdx (V := V) t a) ℝ) := by
    simpa [Idx, p] using vertexSlackReindex_eq_fromBlocksZero (V := V) (y := y) (t := t) a
  have hReindexedPsd :
      (Matrix.reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm
        (frac_vertex_slack_localizing_matrix t y a)).PosSemidef := by
    rw [hReindex]
    exact fromBlocksZeroPosSemidef hLpsd
  have hSub :
      ((frac_vertex_slack_localizing_matrix t y a).submatrix
        (Equiv.sumCompl p) (Equiv.sumCompl p)).PosSemidef := by
    simpa [Matrix.reindex_apply] using hReindexedPsd
  exact (Matrix.posSemidef_submatrix_equiv (Equiv.sumCompl p)).mp hSub

/-- Helper for Theorem 10.15: vanishing on small non-stable sets kills the cross block needed for
the edge-slack localizing matrix. -/
lemma fracEdgeSlackPosSemidef_of_zeroOnSmallNonstable
    {t : ℕ} {y : Finset V → ℝ}
    (hyK : y ∈ K_t t)
    (hzero : ∀ I : Finset V, I.card ≤ 2 * t + 2 → ¬ G.IsIndepSet I → y I = 0)
    {a b : V} (hab : G.Adj a b) :
    (frac_edge_slack_localizing_matrix t y a b).PosSemidef := by
  classical
  -- Route correction: reduce to the block `A - B - C` on sets avoiding both endpoints, then use
  -- `hzero` to show the `ab`-cross block vanishes.
  let Idx := {I : Finset V // I.card ≤ t}
  let p : Idx → Prop := fun I => a ∉ I.1 ∧ b ∉ I.1
  have hLpsd : (edgeSlackReducedMatrix (V := V) t y a b).PosSemidef := by
    simpa using edgeSlackReducedPosSemidef (G := G) (V := V) hyK hzero hab
  have hReindex :
      (Matrix.reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm
          (frac_edge_slack_localizing_matrix t y a b)) =
        Matrix.fromBlocks (edgeSlackReducedMatrix (V := V) t y a b) 0 0
          (0 : Matrix (edgeHitIdx (V := V) t a b) (edgeHitIdx (V := V) t a b) ℝ) := by
    simpa [Idx, p] using
      edgeSlackReindex_eq_fromBlocksZero (G := G) (y := y) (t := t) hzero hab
  have hReindexedPsd :
      (Matrix.reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm
        (frac_edge_slack_localizing_matrix t y a b)).PosSemidef := by
    rw [hReindex]
    exact fromBlocksZeroPosSemidef hLpsd
  have hSub :
      ((frac_edge_slack_localizing_matrix t y a b).submatrix
        (Equiv.sumCompl p) (Equiv.sumCompl p)).PosSemidef := by
    simpa [Matrix.reindex_apply] using hReindexedPsd
  exact (Matrix.posSemidef_submatrix_equiv (Equiv.sumCompl p)).mp hSub

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap10/section_10_4/ch10_sec10_4_2_theorem_10_15.lean

Theorem 10.15. `K_t(FRAC(G))` is exactly the set of normalized subset-indexed moment vectors
in `K_t t` whose coordinates vanish on every non-stable vertex set of size at most
`2 * t + 2`. -/
theorem frac_lasserre_relaxation_eq_K_t_and_small_nonstable_zero_set
    {t : ℕ} (ht : 1 ≤ t) :
    frac_lasserre_relaxation G t =
      {y | y ∈ K_t t ∧
          ∀ I : Finset V, I.card ≤ 2 * t + 2 → ¬ G.IsIndepSet I → y I = 0} := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyK, -, -, -⟩ := (mem_frac_lasserre_relaxation_iff (G := G) t y).1 hy
    refine ⟨hyK, ?_⟩
    intro I hIcard hI
    obtain ⟨I₁, I₂, hUnion, hI₁card, hI₂card, hI₁⟩ :=
      existsSmallNonstableUnion (G := G) ht hIcard hI
    have hI₁zero :
        y I₁ = 0 :=
      smallNonstableMoment_eq_zero_of_memFracLasserre (G := G) hy hI₁card hI₁
    -- Proposition 10.13 propagates the vanishing from the non-stable part to the whole union.
    rw [hUnion]
    exact k_t_union_eq_zero_of_eq_zero hyK hI₁card hI₂card hI₁zero
  · intro hy
    rcases hy with ⟨hyK, hzero⟩
    refine (mem_frac_lasserre_relaxation_iff (G := G) t y).2 ?_
    refine ⟨hyK, ?_, ?_, ?_⟩
    · intro a
      exact fracVertexNonnegPosSemidef_of_mem_K_t hyK a
    · intro a
      exact fracVertexSlackPosSemidef_of_zeroOnSmallNonstable hyK a
    · intro a b hab
      exact fracEdgeSlackPosSemidef_of_zeroOnSmallNonstable (G := G) hyK hzero hab

end Theorem_10_15
