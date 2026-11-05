/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_7.ch4_sec4_7_definition_4_7_extra_1

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

-- This file reuses the canonical Section 4.7 owner `Submodular` and adds the
-- submodular polyhedron and greedy constructions built from it.

section Remark_4_7_extra_2

section Polyhedron

variable {α : Type*}

/-- The submodular polyhedron attached to a real-valued set function `f`. -/
def submodularPolyhedron (f : Finset α → ℝ) : Set (α → ℝ) :=
  {x | ∀ S : Finset α, (∑ j ∈ S, x j) ≤ f S}

/-- Membership in `submodularPolyhedron` is equivalent to satisfying all subset inequalities. -/
@[simp] theorem mem_submodularPolyhedron_iff {f : Finset α → ℝ} {x : α → ℝ} :
    x ∈ submodularPolyhedron f ↔
      ∀ S : Finset α, (∑ j ∈ S, x j) ≤ f S :=
  Iff.rfl

end Polyhedron

section Greedy

variable {n : ℕ}

/-- The `j`-th greedy prefix set on `Fin n`, namely the indices whose zero-based value is `< j`.
This is the `Fin`-indexed translation of the textbook chain `S₀ = ∅`, `Sⱼ = {1, ..., j}`. -/
def submodularGreedyPrefix (n : ℕ) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.1 < j

/-- Membership in `submodularGreedyPrefix n j` means exactly that the index lies among the first
`j` coordinates. -/
@[simp] theorem mem_submodularGreedyPrefix_iff (n : ℕ) (j : ℕ) (i : Fin n) :
    i ∈ submodularGreedyPrefix n j ↔ i.1 < j := by
  simp [submodularGreedyPrefix]

/-- The primitive greedy increments attached to an integer-valued submodular set function. -/
def submodularGreedySolutionInt (f : Finset (Fin n) → ℤ) : Fin n → ℤ :=
  fun j ↦
    f (submodularGreedyPrefix n (j.1 + 1)) - f (submodularGreedyPrefix n j.1)

/-- The real-valued greedy vector is the canonical coercion of the integer greedy increments. -/
abbrev submodularGreedySolution (f : Finset (Fin n) → ℤ) : Fin n → ℝ :=
  Int.cast ∘ submodularGreedySolutionInt f

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_7/ch4_sec4_7_remark_4_7_extra_2.lean:
each greedy prefix is obtained from the previous one by inserting its new endpoint. -/
private lemma submodularGreedyPrefix_succ_eq_insert (i : Fin n) :
    submodularGreedyPrefix n (i.1 + 1) = insert i (submodularGreedyPrefix n i.1) := by
  -- Compare membership coordinatewise, separating the newly inserted endpoint.
  ext j
  constructor
  · intro hj
    by_cases hji : j = i
    · simp [hji]
    · apply Finset.mem_insert.mpr
      right
      rw [mem_submodularGreedyPrefix_iff] at hj ⊢
      have hval : j.1 ≠ i.1 := fun h ↦ hji (Fin.ext h)
      omega
  · intro hj
    rcases Finset.mem_insert.1 hj with rfl | hj'
    · simp [mem_submodularGreedyPrefix_iff]
    · rw [mem_submodularGreedyPrefix_iff] at hj' ⊢
      omega

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_7/ch4_sec4_7_remark_4_7_extra_2.lean:
diminishing returns holds along nested finite subsets of a submodular set function. -/
private lemma submodularMarginal_le_of_subset {α : Type*} [DecidableEq α]
    (g : Finset α → ℝ) (hg : Submodular g)
    {A B : Finset α} (hAB : A ⊆ B) {e : α} (he : e ∉ B) :
    g (insert e B) - g B ≤ g (insert e A) - g A := by
  have heA : e ∉ A := fun h ↦ he (hAB h)
  have h_inter : insert e A ∩ B = A := by
    ext x
    by_cases hx : x = e
    · subst hx
      simp [he, heA]
    · constructor
      · intro hxmem
        rcases Finset.mem_insert.mp (Finset.mem_inter.mp hxmem).1 with hxe | hxA
        · exact False.elim (hx hxe)
        · exact hxA
      · intro hxA
        simp [Finset.mem_inter, Finset.mem_insert, hx, hxA, hAB hxA]
  have h_union : insert e A ∪ B = insert e B := by
    ext x
    by_cases hx : x = e
    · subst hx
      simp
    · constructor
      · intro hxmem
        rcases Finset.mem_union.mp hxmem with hxA | hxB
        · have hxA' : x ∈ A := by
            simpa [Finset.mem_insert, hx] using hxA
          simp [Finset.mem_insert, hx, hAB hxA']
        · simp [Finset.mem_insert, hx, hxB]
      · intro hxmem
        rcases Finset.mem_insert.mp hxmem with hxE | hxB
        · exact False.elim (hx hxE)
        · exact Finset.mem_union.mpr (Or.inr hxB)
  -- Rewrite the lattice inequality into the standard diminishing-returns form.
  have hsub : g A + g (insert e B) ≤ g (insert e A) + g B := by
    simpa [h_inter, h_union] using hg (insert e A) B
  linarith

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_7/ch4_sec4_7_remark_4_7_extra_2.lean:
the real greedy increments telescope on every identity-order prefix. -/
private lemma greedyPrefixSum_eq_prefixValue (g : Finset (Fin n) → ℝ)
    (h_empty : g ∅ = 0) :
    ∀ r : ℕ, r ≤ n →
      Finset.sum (submodularGreedyPrefix n r)
        (fun i ↦ g (submodularGreedyPrefix n (i.1 + 1)) - g (submodularGreedyPrefix n i.1)) =
          g (submodularGreedyPrefix n r) := by
  intro r hr
  induction r with
  | zero =>
    -- The empty prefix starts the telescoping identity at the normalization value.
    simp [submodularGreedyPrefix, h_empty]
  | succ r ihr =>
    have hrlt : r < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr
    let i : Fin n := ⟨r, hrlt⟩
    have hprefix :
        submodularGreedyPrefix n (r + 1) = insert i (submodularGreedyPrefix n r) := by
      simpa [i] using submodularGreedyPrefix_succ_eq_insert i
    have hi_not_mem : i ∉ submodularGreedyPrefix n r := by
      rw [mem_submodularGreedyPrefix_iff]
      exact lt_irrefl r
    -- Peel off the endpoint, invoke the shorter prefix, and cancel its value.
    calc
      Finset.sum (submodularGreedyPrefix n (r + 1))
          (fun j ↦ g (submodularGreedyPrefix n (j.1 + 1)) - g (submodularGreedyPrefix n j.1))
          =
          (g (submodularGreedyPrefix n (r + 1)) - g (submodularGreedyPrefix n r)) +
            Finset.sum (submodularGreedyPrefix n r)
              (fun j ↦ g (submodularGreedyPrefix n (j.1 + 1)) -
                g (submodularGreedyPrefix n j.1)) := by
            rw [hprefix, Finset.sum_insert hi_not_mem]
            simp [i, hprefix]
      _ = (g (submodularGreedyPrefix n (r + 1)) - g (submodularGreedyPrefix n r)) +
            g (submodularGreedyPrefix n r) := by
            rw [ihr (Nat.le_of_succ_le hr)]
      _ = g (submodularGreedyPrefix n (r + 1)) := by
            ring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_7/ch4_sec4_7_remark_4_7_extra_2.lean:
one greedy increment is at most its marginal over an arbitrary restricted subset. -/
private lemma greedyCoordinate_le_restrictedMarginal
    (g : Finset (Fin n) → ℝ) (hg : Submodular g)
    (S : Finset (Fin n)) (i : Fin n) :
    g (submodularGreedyPrefix n (i.1 + 1)) - g (submodularGreedyPrefix n i.1) ≤
      g (insert i (S.filter fun j ↦ j.1 < i.1)) - g (S.filter fun j ↦ j.1 < i.1) := by
  let Slt : Finset (Fin n) := S.filter fun j ↦ j.1 < i.1
  have hSlt_subset : Slt ⊆ submodularGreedyPrefix n i.1 := by
    intro j hj
    rw [mem_submodularGreedyPrefix_iff]
    exact (Finset.mem_filter.1 hj).2
  have hi_not_mem : i ∉ submodularGreedyPrefix n i.1 := by
    rw [mem_submodularGreedyPrefix_iff]
    exact lt_irrefl i.1
  -- Diminishing returns compares the restricted subset with the full prefix.
  simpa [Slt, submodularGreedyPrefix_succ_eq_insert] using
    submodularMarginal_le_of_subset g hg hSlt_subset hi_not_mem

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_7/ch4_sec4_7_remark_4_7_extra_2.lean:
erasing the maximum of a nonempty `Fin`-set leaves exactly its smaller elements. -/
private lemma eraseMax'_eq_filter_lt (S : Finset (Fin n)) (hS : S.Nonempty) :
    S.erase (S.max' hS) = S.filter (fun j ↦ j.1 < (S.max' hS).1) := by
  -- Compare membership using maximality and injectivity of `Fin.val`.
  ext j
  constructor
  · intro hj
    have hjS : j ∈ S := Finset.mem_of_mem_erase hj
    have hjne : j ≠ S.max' hS := Finset.ne_of_mem_erase hj
    have hjlt : j.1 < (S.max' hS).1 := by
      have hjle : j ≤ S.max' hS := Finset.le_max' S j hjS
      have hjval_ne : j.1 ≠ (S.max' hS).1 := by
        intro hEq
        apply hjne
        exact Fin.ext hEq
      exact lt_of_le_of_ne hjle hjval_ne
    simpa [Finset.mem_filter, hjS] using hjlt
  · intro hj
    have hjS : j ∈ S := (Finset.mem_filter.1 hj).1
    have hjlt : j.1 < (S.max' hS).1 := (Finset.mem_filter.1 hj).2
    have hjne : j ≠ S.max' hS := by
      intro hEq
      exact lt_irrefl _ (hEq ▸ hjlt)
    exact Finset.mem_erase.2 ⟨hjne, hjS⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_7/ch4_sec4_7_remark_4_7_extra_2.lean:
the identity-order greedy point is feasible for a normalized submodular function. -/
private lemma greedyPoint_mem_submodularPolyhedron_of_submodular
    (g : Finset (Fin n) → ℝ) (hg : Submodular g) (h_empty : g ∅ = 0) :
    (fun j ↦
      g (submodularGreedyPrefix n (j.1 + 1)) - g (submodularGreedyPrefix n j.1)) ∈
        submodularPolyhedron g := by
  rw [mem_submodularPolyhedron_iff]
  intro S
  classical
  refine Finset.strongInductionOn S ?_
  intro S IH
  by_cases hS_empty' : S = ∅
  · -- The empty subset inequality follows directly from normalization.
    subst hS_empty'
    simp [h_empty]
  · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS_empty'
    let m : Fin n := S.max' hS_nonempty
    have hm_mem : m ∈ S := Finset.max'_mem S hS_nonempty
    have hgm :
        g (submodularGreedyPrefix n (m.1 + 1)) - g (submodularGreedyPrefix n m.1) ≤
          g S - g (S.erase m) := by
      -- Bound the maximal coordinate by its actual marginal inside `S`.
      calc
        g (submodularGreedyPrefix n (m.1 + 1)) - g (submodularGreedyPrefix n m.1) ≤
            g (insert m (S.filter fun j ↦ j.1 < m.1)) -
              g (S.filter fun j ↦ j.1 < m.1) := by
              simpa [m] using greedyCoordinate_le_restrictedMarginal g hg S m
        _ = g S - g (S.erase m) := by
              rw [← eraseMax'_eq_filter_lt S hS_nonempty, Finset.insert_erase hm_mem]
    have hIH :
        Finset.sum (S.erase m)
          (fun i ↦ g (submodularGreedyPrefix n (i.1 + 1)) -
            g (submodularGreedyPrefix n i.1)) ≤ g (S.erase m) := by
      exact IH (S.erase m) (Finset.erase_ssubset hm_mem)
    -- Add the maximal-coordinate bound to the induction hypothesis.
    calc
      Finset.sum S
          (fun i ↦ g (submodularGreedyPrefix n (i.1 + 1)) -
            g (submodularGreedyPrefix n i.1))
          =
            (g (submodularGreedyPrefix n (m.1 + 1)) -
              g (submodularGreedyPrefix n m.1)) +
              Finset.sum (S.erase m)
                (fun i ↦ g (submodularGreedyPrefix n (i.1 + 1)) -
                  g (submodularGreedyPrefix n i.1)) := by
            rw [← Finset.insert_erase hm_mem, Finset.sum_insert (Finset.notMem_erase _ _)]
            simp
      _ ≤ (g S - g (S.erase m)) + g (S.erase m) := add_le_add hgm hIH
      _ = g S := by
            ring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_7/ch4_sec4_7_remark_4_7_extra_2.lean:
summing over a greedy prefix agrees with summing over its canonical `Fin` indexing. -/
private lemma sum_submodularGreedyPrefix_eq_sum_fin
    (x : Fin n → ℝ) {r : ℕ} (hr : r ≤ n) :
    Finset.sum (submodularGreedyPrefix n r) x = ∑ j : Fin r, x (Fin.castLE hr j) := by
  classical
  let emb : Fin r ↪ Fin n := Fin.castLEEmb hr
  have hmap : (Finset.univ : Finset (Fin r)).map emb = submodularGreedyPrefix n r := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_map.1 hi with ⟨j, -, rfl⟩
      simp [emb, mem_submodularGreedyPrefix_iff]
    · intro hi
      have hir : i.1 < r := by
        simpa [mem_submodularGreedyPrefix_iff] using hi
      refine Finset.mem_map.2 ⟨⟨i.1, hir⟩, Finset.mem_univ _, ?_⟩
      ext
      simp [emb]
  -- Transport the sum across the canonical embedding of the smaller `Fin` type.
  calc
    Finset.sum (submodularGreedyPrefix n r) x =
        Finset.sum ((Finset.univ : Finset (Fin r)).map emb) x := by
      rw [hmap.symm]
    _ = ∑ j : Fin r, x (Fin.castLE hr j) := by
      simp [emb]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_7/ch4_sec4_7_remark_4_7_extra_2.lean:
antitone nonnegative weights preserve identity-order prefix domination. -/
private lemma orderedWeightedSum_le_of_prefixDominance
    (c x y : Fin n → ℝ)
    (hSorted : Antitone c)
    (hNonneg : ∀ j : Fin n, 0 ≤ c j)
    (hPrefix :
      ∀ r : ℕ, r ≤ n →
        Finset.sum (submodularGreedyPrefix n r) x ≤
          Finset.sum (submodularGreedyPrefix n r) y) :
    c ⬝ᵥ x ≤ c ⬝ᵥ y := by
  cases n with
  | zero =>
      -- There are no coordinates in dimension zero.
      simp [dotProduct]
  | succ n =>
      let a : ℕ → ℝ := fun i ↦ if h : i < n + 1 then c ⟨i, h⟩ else 0
      let bx : ℕ → ℝ := fun i ↦ if h : i < n + 1 then x ⟨i, h⟩ else 0
      let bY : ℕ → ℝ := fun i ↦ if h : i < n + 1 then y ⟨i, h⟩ else 0
      have hxDot :
          c ⬝ᵥ x = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bx i) := by
        -- Rewrite the dot product as a range sum so Abel summation applies directly.
        calc
          c ⬝ᵥ x = Finset.sum Finset.univ (fun i : Fin (n + 1) ↦ c i * x i) := by
            simp [dotProduct]
          _ = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bx i) := by
            rw [Finset.sum_fin_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt : i < n + 1 := Finset.mem_range.1 hi
            have hi_le : i ≤ n := Nat.lt_succ_iff.mp hi_lt
            simp [a, bx, hi_lt, hi_le]
      have hyDot :
          c ⬝ᵥ y = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bY i) := by
        -- Apply the same range representation to the comparison vector.
        calc
          c ⬝ᵥ y = Finset.sum Finset.univ (fun i : Fin (n + 1) ↦ c i * y i) := by
            simp [dotProduct]
          _ = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bY i) := by
            rw [Finset.sum_fin_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt : i < n + 1 := Finset.mem_range.1 hi
            have hi_le : i ≤ n := Nat.lt_succ_iff.mp hi_lt
            simp [a, bY, hi_lt, hi_le]
      have hxPrefixRange :
          ∀ r : ℕ, ∀ hr : r ≤ n + 1,
            Finset.sum (Finset.range r) bx =
              Finset.sum (submodularGreedyPrefix (n + 1) r) x := by
        intro r hr
        -- Reindex each initial range as the corresponding greedy prefix.
        calc
          Finset.sum (Finset.range r) bx = ∑ j : Fin r, x (Fin.castLE hr j) := by
            rw [Finset.sum_fin_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt : i < r := Finset.mem_range.1 hi
            have hin : i < n + 1 := lt_of_lt_of_le hi_lt hr
            have hi_le : i ≤ n := Nat.lt_succ_iff.mp hin
            simp [bx, hi_lt, hi_le]
          _ = Finset.sum (submodularGreedyPrefix (n + 1) r) x := by
            simpa using (sum_submodularGreedyPrefix_eq_sum_fin x hr).symm
      have hyPrefixRange :
          ∀ r : ℕ, ∀ hr : r ≤ n + 1,
            Finset.sum (Finset.range r) bY =
              Finset.sum (submodularGreedyPrefix (n + 1) r) y := by
        intro r hr
        calc
          Finset.sum (Finset.range r) bY = ∑ j : Fin r, y (Fin.castLE hr j) := by
            rw [Finset.sum_fin_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt : i < r := Finset.mem_range.1 hi
            have hin : i < n + 1 := lt_of_lt_of_le hi_lt hr
            have hi_le : i ≤ n := Nat.lt_succ_iff.mp hin
            simp [bY, hi_lt, hi_le]
          _ = Finset.sum (submodularGreedyPrefix (n + 1) r) y := by
            simpa using (sum_submodularGreedyPrefix_eq_sum_fin y hr).symm
      have hxParts :
          Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bx i) =
            a n * Finset.sum (Finset.range (n + 1)) bx -
              Finset.sum (Finset.range n)
                (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bx) := by
        -- Abel summation exposes the total sum and all proper prefix sums.
        simpa [smul_eq_mul] using Finset.sum_range_by_parts a bx (n + 1)
      have hyParts :
          Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bY i) =
            a n * Finset.sum (Finset.range (n + 1)) bY -
              Finset.sum (Finset.range n)
                (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bY) := by
        simpa [smul_eq_mul] using Finset.sum_range_by_parts a bY (n + 1)
      have hxExpr :
          c ⬝ᵥ x =
            a n * Finset.sum (Finset.range (n + 1)) bx +
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bx) := by
        have hsumFlipBx :
            -Finset.sum (Finset.range n)
                (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bx) =
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bx) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        calc
          c ⬝ᵥ x = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bx i) := hxDot
          _ = a n * Finset.sum (Finset.range (n + 1)) bx -
                Finset.sum (Finset.range n)
                  (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bx) := hxParts
          _ = a n * Finset.sum (Finset.range (n + 1)) bx +
                (-Finset.sum (Finset.range n)
                  (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bx)) := by
                ring
          _ = a n * Finset.sum (Finset.range (n + 1)) bx +
                Finset.sum (Finset.range n)
                  (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bx) := by
                rw [hsumFlipBx]
      have hyExpr :
          c ⬝ᵥ y =
            a n * Finset.sum (Finset.range (n + 1)) bY +
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bY) := by
        have hsumFlipBY :
            -Finset.sum (Finset.range n)
                (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bY) =
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bY) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        calc
          c ⬝ᵥ y = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bY i) := hyDot
          _ = a n * Finset.sum (Finset.range (n + 1)) bY -
                Finset.sum (Finset.range n)
                  (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bY) := hyParts
          _ = a n * Finset.sum (Finset.range (n + 1)) bY +
                (-Finset.sum (Finset.range n)
                  (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bY)) := by
                ring
          _ = a n * Finset.sum (Finset.range (n + 1)) bY +
                Finset.sum (Finset.range n)
                  (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bY) := by
                rw [hsumFlipBY]
      have hLastNonneg : 0 ≤ a n := by
        simp [a, hNonneg]
      have hGapNonneg : ∀ i ∈ Finset.range n, 0 ≤ a i - a (i + 1) := by
        intro i hi
        have hi_lt : i < n := Finset.mem_range.1 hi
        have hi0 : i < n + 1 := lt_trans hi_lt (Nat.lt_succ_self n)
        have hi1 : i + 1 < n + 1 := Nat.succ_lt_succ hi_lt
        have hstep : c ⟨i + 1, hi1⟩ ≤ c ⟨i, hi0⟩ := by
          exact hSorted (show (⟨i, hi0⟩ : Fin (n + 1)) ≤ ⟨i + 1, hi1⟩ by
            exact Nat.le_succ i)
        have hstepAux : a (i + 1) ≤ a i := by
          have hi_le : i ≤ n := Nat.lt_succ_iff.mp hi0
          simpa [a, hi_lt, hi_le] using hstep
        linarith
      have hPrefixRange :
          ∀ r : ℕ, ∀ hr : r ≤ n + 1,
            Finset.sum (Finset.range r) bx ≤ Finset.sum (Finset.range r) bY := by
        intro r hr
        rw [hxPrefixRange r hr, hyPrefixRange r hr]
        exact hPrefix r hr
      have hLastLe :
          a n * Finset.sum (Finset.range (n + 1)) bx ≤
            a n * Finset.sum (Finset.range (n + 1)) bY := by
        exact mul_le_mul_of_nonneg_left (hPrefixRange (n + 1) le_rfl) hLastNonneg
      have hGapLe :
          Finset.sum (Finset.range n)
              (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bx) ≤
            Finset.sum (Finset.range n)
              (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bY) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (hPrefixRange (i + 1) (Nat.succ_le_succ (Nat.le_of_lt (Finset.mem_range.1 hi))))
          (hGapNonneg i hi)
      -- Every Abel coefficient is nonnegative, so prefix domination compares the objectives.
      calc
        c ⬝ᵥ x =
            a n * Finset.sum (Finset.range (n + 1)) bx +
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bx) := hxExpr
        _ ≤ a n * Finset.sum (Finset.range (n + 1)) bY +
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bY) :=
            add_le_add hLastLe hGapLe
        _ = c ⬝ᵥ y := hyExpr.symm

set_option linter.style.longLine false in
/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_7/ch4_sec4_7_remark_4_7_extra_2.lean
Remark 4.7-extra-2. If the objective coefficients are ordered so that they are antitone and
nonnegative, then the greedy vector obtained from successive prefix differences is an optimal
solution of the submodular maximization problem `(4.24)`. -/
theorem submodularGreedySolution_optimal
    (f : Finset (Fin n) → ℤ)
    (c : Fin n → ℤ)
    (h_submodular : Submodular f)
    (h_empty : f ∅ = 0)
    (h_antitone : Antitone c)
    (h_nonneg : ∀ j, 0 ≤ c j) :
    submodularGreedySolution f ∈ submodularPolyhedron (fun S ↦ (f S : ℝ)) ∧
      ∀ x : Fin n → ℝ,
        x ∈ submodularPolyhedron (fun S ↦ (f S : ℝ)) →
          (∑ j, (c j : ℝ) * x j) ≤
            ∑ j, (c j : ℝ) * submodularGreedySolution f j := by
  have h_submodular_real : Submodular (fun S ↦ (f S : ℝ)) := by
    -- Cast the integer lattice inequality once, before constructing the greedy point.
    intro S T
    dsimp only
    exact_mod_cast h_submodular S T
  have h_empty_real : (f ∅ : ℝ) = 0 := by
    exact_mod_cast h_empty
  have h_greedy_mem :=
    greedyPoint_mem_submodularPolyhedron_of_submodular
      (fun S ↦ (f S : ℝ)) h_submodular_real h_empty_real
  constructor
  · -- Feasibility is the diminishing-returns induction after casting each increment.
    simpa [submodularGreedySolution, submodularGreedySolutionInt, Function.comp_apply,
      Int.cast_sub] using h_greedy_mem
  · intro x hx
    have h_antitone_real : Antitone (fun j ↦ (c j : ℝ)) := by
      intro i j hij
      dsimp only
      exact_mod_cast h_antitone hij
    have h_nonneg_real : ∀ j : Fin n, 0 ≤ (c j : ℝ) := by
      intro j
      exact_mod_cast h_nonneg j
    have h_prefix :
        ∀ r : ℕ, ∀ hr : r ≤ n,
          Finset.sum (submodularGreedyPrefix n r) x ≤
            Finset.sum (submodularGreedyPrefix n r)
              (fun j ↦
                (f (submodularGreedyPrefix n (j.1 + 1)) : ℝ) -
                  (f (submodularGreedyPrefix n j.1) : ℝ)) := by
      intro r hr
      -- Feasibility bounds each prefix, while greedy increments are tight on it.
      calc
        Finset.sum (submodularGreedyPrefix n r) x ≤
            (f (submodularGreedyPrefix n r) : ℝ) := hx (submodularGreedyPrefix n r)
        _ = Finset.sum (submodularGreedyPrefix n r)
              (fun j ↦
                (f (submodularGreedyPrefix n (j.1 + 1)) : ℝ) -
                  (f (submodularGreedyPrefix n j.1) : ℝ)) := by
            symm
            exact greedyPrefixSum_eq_prefixValue
              (fun S ↦ (f S : ℝ)) h_empty_real r hr
    have h_weighted := orderedWeightedSum_le_of_prefixDominance
      (fun j ↦ (c j : ℝ)) x
      (fun j ↦
        (f (submodularGreedyPrefix n (j.1 + 1)) : ℝ) -
          (f (submodularGreedyPrefix n j.1) : ℝ))
      h_antitone_real h_nonneg_real h_prefix
    -- Unfold the dot products and identify real differences with cast integer increments.
    simpa [dotProduct, submodularGreedySolution, submodularGreedySolutionInt,
      Function.comp_apply, Int.cast_sub] using h_weighted

end Greedy

end Remark_4_7_extra_2
