/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_20
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_7.ch4_sec4_7_remark_4_7_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_7.ch4_sec4_7_theorem_4_29
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_25
import Mathlib.Analysis.Convex.KreinMilman

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Primary domain: subset-sum descriptions of the permutahedron.
-- Source-facing owner: `permutahedron`.
-- Core/canonical reused API: `permutahedron_subset_constant_sum_hyperplane`.
-- Structural repair: the original Example 3.29 owner is not dependency-closed in this checkout,
-- so this file localizes only the tiny subset-sum API it uses from that owner.
-- Bridge/view: the upper-bound formulation below is derived from the lower-bound formulation by
-- passing to complements.

section

variable {n : ℕ} {x : Fin n → ℝ}

/-- Helper for Exercise 4.26: the coefficient vector of the subset-sum inequality indexed by
`S`. -/
private def subsetSumIndicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i ↦ if i ∈ S then 1 else 0

/-- Helper for Exercise 4.26: the dot product with `subsetSumIndicator S` is the subset sum over
`S`. -/
private theorem dot_subsetSumIndicator_eq_sum {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) :
    subsetSumIndicator S ⬝ᵥ x = ∑ i ∈ S, x i := by
  -- Expand the indicator coefficients coordinatewise and keep only the summands indexed by `S`.
  classical
  simp [subsetSumIndicator, dotProduct]

/-- Helper for Exercise 4.26: the sum of the first `k` positive integers is the triangular number
`\binom{k + 1}{2}`. -/
private theorem sum_range_initial_segment_eq_choose (k : ℕ) :
    (∑ i ∈ Finset.range k, ((i : ℝ) + 1)) = (Nat.choose (k + 1) 2 : ℝ) := by
  induction k with
  | zero =>
      simp
  | succ k hk =>
      -- Append the last term and rewrite the triangular-number recursion.
      rw [Finset.sum_range_succ, hk]
      norm_num [Nat.choose_succ_succ, Nat.choose_one_right]
      ring

/-- Helper for Exercise 4.26: the same arithmetic progression written as a sum over `Fin k`. -/
private theorem sum_univ_initial_segment_eq_choose (k : ℕ) :
    (∑ i : Fin k, (((i : ℕ) : ℝ) + 1)) = (Nat.choose (k + 1) 2 : ℝ) := by
  -- Rewrite the `Fin k` sum as the corresponding range sum.
  rw [Fin.sum_univ_eq_sum_range fun i : ℕ ↦ ((i : ℝ) + 1)]
  exact sum_range_initial_segment_eq_choose k

/-- Helper for Exercise 4.26: among `k` distinct natural indices, the smallest possible value of
`∑ (t + 1)` is attained on the initial segment `{0, ..., k - 1}`. -/
private theorem sum_of_distinct_nat_indices_ge_triangular (S : Finset ℕ) :
    (Nat.choose (S.card + 1) 2 : ℝ) ≤ ∑ t ∈ S, ((t : ℝ) + 1) := by
  classical
  let e : Fin S.card ↪o ℕ := S.orderEmbOfFin rfl
  have hrewrite :
      ∑ t ∈ S, ((t : ℝ) + 1) = ∑ i : Fin S.card, (((e i : ℕ) : ℝ) + 1) := by
    -- Enumerate `S` in increasing order.
    calc
      ∑ t ∈ S, ((t : ℝ) + 1) = ∑ t ∈ Finset.image e Finset.univ, ((t : ℝ) + 1) := by
        simp [e]
      _ = ∑ i : Fin S.card, (((e i : ℕ) : ℝ) + 1) := by
        simpa using
          (Finset.sum_image e.injective.injOn :
            (∑ t ∈ Finset.image e Finset.univ, ((t : ℝ) + 1)) =
              ∑ i ∈ Finset.univ, (((e i : ℕ) : ℝ) + 1))
  have hindex_le : ∀ i : Fin S.card, (i : ℕ) ≤ e i := by
    intro i
    -- The increasing enumeration dominates the identity on positions.
    have haux : ∀ m (hm : m < S.card), m ≤ e ⟨m, hm⟩ := by
      intro m hm
      induction m with
      | zero =>
          exact Nat.zero_le _
      | succ m hm_ind =>
          have hm' : m < S.card := Nat.lt_of_succ_lt hm
          have hltFin : (⟨m, hm'⟩ : Fin S.card) < ⟨m + 1, hm⟩ := by
            change m < m + 1
            exact Nat.lt_succ_self m
          have hlt : e ⟨m, hm'⟩ < e ⟨m + 1, hm⟩ := by
            exact e.strictMono hltFin
          exact Nat.succ_le_of_lt (lt_of_le_of_lt (hm_ind hm') hlt)
    exact haux i.1 i.2
  have hpointwise :
      ∀ i : Fin S.card, (((i : ℕ) + 1 : ℝ)) ≤ (((e i : ℕ) : ℝ) + 1) := by
    intro i
    -- Add one to the index inequality and cast to `ℝ`.
    exact_mod_cast Nat.succ_le_succ (hindex_le i)
  have hcompare :
      (∑ i : Fin S.card, (((i : ℕ) + 1 : ℝ))) ≤
        ∑ i : Fin S.card, (((e i : ℕ) : ℝ) + 1) := by
    -- Compare the two sums termwise.
    exact Finset.sum_le_sum fun i _ ↦ hpointwise i
  calc
    (Nat.choose (S.card + 1) 2 : ℝ) = ∑ i : Fin S.card, (((i : ℕ) + 1 : ℝ)) := by
      symm
      exact sum_univ_initial_segment_eq_choose S.card
    _ ≤ ∑ i : Fin S.card, (((e i : ℕ) : ℝ) + 1) := hcompare
    _ = ∑ t ∈ S, ((t : ℝ) + 1) := hrewrite.symm

/-- Helper for Exercise 4.26: the same triangular lower bound applies to finite subsets of
`Fin n`. -/
private theorem sum_of_distinct_fin_indices_ge_triangular {n : ℕ} (S : Finset (Fin n)) :
    (Nat.choose (S.card + 1) 2 : ℝ) ≤ ∑ t ∈ S, (((t : ℕ) : ℝ) + 1) := by
  classical
  have hrewrite :
      ∑ t ∈ S, (((t : ℕ) : ℝ) + 1) =
        ∑ u ∈ S.image (fun t : Fin n ↦ (t : ℕ)), ((u : ℝ) + 1) := by
    -- Replace the `Fin n` indices by their distinct natural values.
    simpa using
      (Finset.sum_image Fin.val_injective.injOn :
        (∑ u ∈ S.image (fun t : Fin n ↦ (t : ℕ)), ((u : ℝ) + 1)) =
          ∑ t ∈ S, (((t : ℕ) : ℝ) + 1)).symm
  have hcard : (S.image fun t : Fin n ↦ (t : ℕ)).card = S.card := by
    -- Coercion `Fin n → ℕ` is injective.
    simpa using Finset.card_image_of_injective S Fin.val_injective
  calc
    (Nat.choose (S.card + 1) 2 : ℝ) =
        (Nat.choose ((S.image fun t : Fin n ↦ (t : ℕ)).card + 1) 2 : ℝ) := by
      rw [hcard]
    _ ≤ ∑ u ∈ S.image (fun t : Fin n ↦ (t : ℕ)), ((u : ℝ) + 1) :=
      sum_of_distinct_nat_indices_ge_triangular _
    _ = ∑ t ∈ S, (((t : ℕ) : ℝ) + 1) := hrewrite.symm

/-- Helper for Exercise 4.26: every permutahedron point satisfies the subset-sum lower bound
indexed by `S`. This is the only part of Example 3.29 that this file needs locally. -/
private theorem permutahedron_subset_sum_inequality_valid (n : ℕ) (S : Finset (Fin n)) :
    permutahedron n ⊆
      {y : Fin n → ℝ | (Nat.choose (S.card + 1) 2 : ℝ) ≤ ∑ i ∈ S, y i} := by
  classical
  let c : ℝ := (Nat.choose (S.card + 1) 2 : ℝ)
  let H : Set (Fin n → ℝ) := {y : Fin n → ℝ | c ≤ ∑ i ∈ S, y i}
  have hvertices : permutahedron_vertices n ⊆ H := by
    intro y hy
    rcases mem_permutahedron_vertices_iff.mp hy with ⟨σ, rfl⟩
    -- Reindex the subset sum along the permutation and then use the increasing-sequence minimum.
    change c ≤ ∑ i ∈ S, ascending_vector n (σ i)
    have hrewrite :
        ∑ i ∈ S, ascending_vector n (σ i) =
          ∑ t ∈ S.image σ, ascending_vector n t := by
      exact (Finset.sum_image σ.injective.injOn).symm
    have hcard : (S.image σ).card = S.card := by
      simpa using Finset.card_image_of_injective S σ.injective
    rw [hrewrite]
    simpa [c, ascending_vector, hcard] using
      sum_of_distinct_fin_indices_ge_triangular (S.image σ)
  have hconvex : Convex ℝ H := by
    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ S, LinearMap.proj i
    have hpreimage : H = L ⁻¹' Set.Ici c := by
      -- The subset-sum inequality is the linear preimage of a convex halfspace in `ℝ`.
      ext y
      simp [H, L, c]
    rw [hpreimage]
    exact (convex_Ici c).linear_preimage L
  -- Extend the vertex inequality from the generators to their convex hull.
  rw [permutahedron_eq_convexHull]
  exact convexHull_min hvertices hconvex

private theorem subset_sum_upper_bounds_of_lower_bounds
    (htotal : ∑ i, x i = (Nat.choose (n + 1) 2 : ℝ))
    (hlower : ∀ S : Finset (Fin n),
      (Nat.choose (S.card + 1) 2 : ℝ) ≤ ∑ i ∈ S, x i) :
    ∀ S : Finset (Fin n),
      ∑ i ∈ S, x i ≤
        (Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (n - S.card + 1) 2 : ℝ) := by
  intro S
  have hcompl :
      (Nat.choose (Sᶜ.card + 1) 2 : ℝ) ≤ ∑ i ∈ Sᶜ, x i :=
    hlower Sᶜ
  have hsum :
      ∑ i ∈ S, x i + ∑ i ∈ Sᶜ, x i = (Nat.choose (n + 1) 2 : ℝ) := by
    rw [Finset.sum_add_sum_compl]
    exact htotal
  have hupper :
      ∑ i ∈ S, x i ≤
        (Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (Sᶜ.card + 1) 2 : ℝ) := by
    linarith
  simpa [Finset.card_compl, Fintype.card_fin] using hupper

private theorem subset_sum_lower_bounds_of_upper_bounds
    (htotal : ∑ i, x i = (Nat.choose (n + 1) 2 : ℝ))
    (hupper : ∀ S : Finset (Fin n),
      ∑ i ∈ S, x i ≤
        (Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (n - S.card + 1) 2 : ℝ)) :
    ∀ S : Finset (Fin n),
      (Nat.choose (S.card + 1) 2 : ℝ) ≤ ∑ i ∈ S, x i := by
  intro S
  have hcard : n - Sᶜ.card = S.card := by
    have hcard' : S.card + Sᶜ.card = n := by
      rw [Finset.card_add_card_compl, Fintype.card_fin]
    exact (Nat.eq_sub_of_add_eq hcard').symm
  have hcompl :
      ∑ i ∈ Sᶜ, x i ≤
        (Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (S.card + 1) 2 : ℝ) := by
    simpa [hcard] using hupper Sᶜ
  have hsum :
      ∑ i ∈ S, x i + ∑ i ∈ Sᶜ, x i = (Nat.choose (n + 1) 2 : ℝ) := by
    rw [Finset.sum_add_sum_compl]
    exact htotal
  linarith

/-- Helper for Exercise 4.26: the cardinality-based rank function whose associated submodular
polyhedron is exactly the hinted upper-bound system. -/
private def permutahedron_upper_rank (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  (Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (n - S.card + 1) 2 : ℝ)

/-- Helper for Exercise 4.26: the same upper-rank function with integer values, so the Chapter 4
integrality theorem applies directly. -/
private def permutahedron_upper_rank_int (n : ℕ) (S : Finset (Fin n)) : ℤ :=
  (Nat.choose (n + 1) 2 : ℤ) - (Nat.choose (n - S.card + 1) 2 : ℤ)

/-- Helper for Exercise 4.26: casting the integer-valued upper-rank function recovers the real
owner used by the feasible-set description. -/
private theorem permutahedron_upper_rank_int_cast (n : ℕ) (S : Finset (Fin n)) :
    (permutahedron_upper_rank_int n S : ℝ) = permutahedron_upper_rank n S := by
  -- Both formulas are the same cardinality expression, just viewed in different coefficient
  -- rings.
  simp [permutahedron_upper_rank_int, permutahedron_upper_rank]

/-- Helper for Exercise 4.26:
a greedy prefix of
length at most `n` has that length as its cardinality. -/
private theorem submodularGreedyPrefix_card {n r : ℕ} (hr : r ≤ n) :
    (submodularGreedyPrefix n r).card = r := by
  -- Count the indices below `r` by the standard filtered-`Fin` cardinality formula.
  simpa [submodularGreedyPrefix, Nat.min_eq_right hr] using
    (Fin.card_filter_val_lt (n := n) (m := r))

/-- Helper for Exercise 4.26:
the upper rank is
strictly subadditive on two disjoint nonempty sets. -/
private theorem permutahedronUpperRank_strictUnion_of_disjoint
    {n : ℕ} {S T : Finset (Fin n)}
    (hdisj : Disjoint S T) (hS : S.Nonempty) (hT : T.Nonempty) :
    permutahedron_upper_rank n (S ∪ T) <
      permutahedron_upper_rank n S + permutahedron_upper_rank n T := by
  let a := S.card
  let b := T.card
  let m := n - (a + b)
  have hcard_union : (S ∪ T).card = a + b := by
    simpa [a, b] using Finset.card_union_of_disjoint hdisj
  have hab_le : a + b ≤ n := by
    rw [← hcard_union]
    simpa [Fintype.card_fin] using Finset.card_le_univ (S ∪ T)
  have hnS : n - S.card = m + b := by
    unfold m a b
    omega
  have hnT : n - T.card = m + a := by
    unfold m a b
    omega
  have hnUnion : n - (S ∪ T).card = m := by
    rw [hcard_union]
  have hn : n = m + a + b := by
    unfold m
    omega
  have hgap :
      permutahedron_upper_rank n S + permutahedron_upper_rank n T -
          permutahedron_upper_rank n (S ∪ T) = (a : ℝ) * b := by
    -- Expanding triangular numbers exhibits the positive cross term `a * b`.
    simp only [permutahedron_upper_rank, hnS, hnT, hnUnion]
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two,
      Nat.cast_choose_two]
    push_cast
    rw [hn]
    push_cast
    ring
  have ha_pos : 0 < (a : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hS)
  have hb_pos : 0 < (b : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hT)
  -- The positive gap gives the required strict inequality.
  nlinarith

/-- Helper for Exercise 4.26:
a laminar independent
active family for the upper-rank polyhedron consists of distinct nonempty sets forming a chain. -/
private theorem activeLaminarIndependentFamily_isChain
    {n : ℕ} {y : Fin n → ℝ} {T : Fin n → Finset (Fin n)}
    (hy : y ∈ submodularPolyhedron (permutahedron_upper_rank n))
    (hlaminar : IsLaminarSubsetFamily (Finset.univ.image T))
    (hactive : ∀ i, (T i).sum y = permutahedron_upper_rank n (T i))
    (hlinear : LinearIndependent ℝ
      (fun i : Fin n ↦ fun j ↦ if j ∈ T i then (1 : ℝ) else 0)) :
    (∀ i, (T i).Nonempty) ∧ Function.Injective T ∧
      ∀ i j, T i ⊆ T j ∨ T j ⊆ T i := by
  have hnonempty : ∀ i, (T i).Nonempty := by
    intro i
    by_contra hi
    have hi_empty : T i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
    have hrow_ne := hlinear.ne_zero i
    -- An empty active set would contribute the zero incidence vector.
    apply hrow_ne
    funext j
    simp [hi_empty]
  have hinjective : Function.Injective T := by
    intro i j hij
    apply hlinear.injective
    -- Equal supports have equal incidence vectors, so independence identifies their indices.
    funext k
    simp [hij]
  refine ⟨hnonempty, hinjective, ?_⟩
  intro i j
  by_cases hinter : (T i ∩ T j).Nonempty
  · -- Laminarity resolves intersecting members of the family.
    exact hlaminar
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩) hinter
  · have hinter_empty : T i ∩ T j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hinter
    have hdisj : Disjoint (T i) (T j) := Finset.disjoint_iff_inter_eq_empty.mpr hinter_empty
    have hstrict := permutahedronUpperRank_strictUnion_of_disjoint hdisj
      (hnonempty i) (hnonempty j)
    have hfeasible := hy (T i ∪ T j)
    have hsum_union : (T i ∪ T j).sum y = (T i).sum y + (T j).sum y :=
      Finset.sum_union hdisj
    rw [hsum_union, hactive i, hactive j] at hfeasible
    -- Two disjoint nonempty tight rows contradict strict subadditivity of the rank.
    exact False.elim ((not_le_of_gt hstrict) hfeasible)

/-- Helper for Exercise 4.26:
removing one from the
cardinality of a nonempty subset of `Fin n` produces an index in `Fin n`. -/
private theorem nonemptyFinset_card_sub_one_lt {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) : S.card - 1 < n := by
  have hcard_le : S.card ≤ n := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  have hcard_pos : 0 < S.card := Finset.card_pos.mpr hS
  omega

/-- Helper for Exercise 4.26:
subtracting one from a
`Fin n` value still gives a natural number below `n`. -/
private theorem finPredIndex_isLt {n : ℕ} (k : Fin n) : k.1 - 1 < n := by
  omega

/-- Helper for Exercise 4.26:
the predecessor index on
`Fin n`, with zero fixed at zero. -/
private def finPredIndex {n : ℕ} (k : Fin n) : Fin n :=
  ⟨k.1 - 1, finPredIndex_isLt k⟩

/-- Helper for Exercise 4.26:
a nonempty injective
chain of `n` subsets of `Fin n` is the image of the standard greedy-prefix chain under two
permutations. -/
private theorem existsPerm_map_greedyPrefix_eq_of_chain
    {n : ℕ} {T : Fin n → Finset (Fin n)}
    (hnonempty : ∀ i, (T i).Nonempty)
    (hinjective : Function.Injective T)
    (hchain : ∀ i j, T i ⊆ T j ∨ T j ⊆ T i) :
    ∃ τ π : Equiv.Perm (Fin n), ∀ k,
      T (τ k) = (submodularGreedyPrefix n (k.1 + 1)).map π.toEmbedding := by
  classical
  let rankIndex : Fin n → Fin n := fun i ↦
    ⟨(T i).card - 1, nonemptyFinset_card_sub_one_lt (T i) (hnonempty i)⟩
  have hrank_injective : Function.Injective rankIndex := by
    intro i j hij
    have hcard_sub : (T i).card - 1 = (T j).card - 1 := congrArg Fin.val hij
    have hcard : (T i).card = (T j).card := by
      have hi_pos : 0 < (T i).card := Finset.card_pos.mpr (hnonempty i)
      have hj_pos : 0 < (T j).card := Finset.card_pos.mpr (hnonempty j)
      omega
    rcases hchain i j with hij_subset | hji_subset
    · have hcard_le : (T j).card ≤ (T i).card := hcard.ge
      exact hinjective (Finset.eq_of_subset_of_card_le hij_subset hcard_le)
    · have hcard_le : (T i).card ≤ (T j).card := hcard.le
      exact hinjective (Finset.eq_of_subset_of_card_le hji_subset hcard_le).symm
  have hrank_bijective : Function.Bijective rankIndex :=
    Finite.injective_iff_bijective.mp hrank_injective
  let τ : Equiv.Perm (Fin n) := Equiv.ofBijective rankIndex hrank_bijective
  let C : Fin n → Finset (Fin n) := fun k ↦ T (τ.symm k)
  have hCcard : ∀ k, (C k).card = k.1 + 1 := by
    intro k
    have hrank_apply : rankIndex (τ.symm k) = k := by
      exact τ.apply_symm_apply k
    have hsub : (T (τ.symm k)).card - 1 = k.1 := congrArg Fin.val hrank_apply
    have hpos : 0 < (T (τ.symm k)).card := Finset.card_pos.mpr (hnonempty _)
    have hcard : (T (τ.symm k)).card = k.1 + 1 := by
      omega
    simpa [C] using hcard
  have hCmono : ∀ {i j}, i ≤ j → C i ⊆ C j := by
    intro i j hij
    rcases hchain (τ.symm i) (τ.symm j) with hforward | hreverse
    · exact hforward
    · have hcard_le : (C i).card ≤ (C j).card := by
        rw [hCcard i, hCcard j]
        omega
      have heq : C j = C i := by
        exact Finset.eq_of_subset_of_card_le hreverse hcard_le
      exact heq.symm.subset
  let prior : Fin n → Finset (Fin n) := fun k ↦
    (submodularGreedyPrefix n k.1).biUnion C
  have hprior_subset : ∀ k, prior k ⊆ C k := by
    intro k z hz
    rcases Finset.mem_biUnion.mp hz with ⟨i, hi, hiz⟩
    have hik : i ≤ k := by
      rw [mem_submodularGreedyPrefix_iff] at hi
      omega
    exact hCmono hik hiz
  have hprior_card_le : ∀ k, (prior k).card ≤ k.1 := by
    intro k
    by_cases hk : k.1 = 0
    · have hprefix_empty : submodularGreedyPrefix n k.1 = ∅ := by
        ext i
        simp [mem_submodularGreedyPrefix_iff, hk]
      simp [prior, hprefix_empty]
    · have hprior_pred : prior k ⊆ C (finPredIndex k) := by
        intro z hz
        rcases Finset.mem_biUnion.mp hz with ⟨i, hi, hiz⟩
        have hipred : i ≤ finPredIndex k := by
          rw [mem_submodularGreedyPrefix_iff] at hi
          change i.1 ≤ k.1 - 1
          omega
        exact hCmono hipred hiz
      have hcard_le := Finset.card_le_card hprior_pred
      rw [hCcard (finPredIndex k)] at hcard_le
      change (prior k).card ≤ k.1
      change (prior k).card ≤ k.1 - 1 + 1 at hcard_le
      omega
  have hfresh : ∀ k, ∃ z, z ∈ C k ∧ z ∉ prior k := by
    intro k
    have hcard_lt : (prior k).card < (C k).card := by
      rw [hCcard k]
      exact Nat.lt_succ_of_le (hprior_card_le k)
    exact Finset.exists_mem_notMem_of_card_lt_card hcard_lt
  let p : Fin n → Fin n := fun k ↦ Classical.choose (hfresh k)
  have hp_mem : ∀ k, p k ∈ C k := by
    intro k
    exact (Classical.choose_spec (hfresh k)).1
  have hp_not_prior : ∀ k, p k ∉ prior k := by
    intro k
    exact (Classical.choose_spec (hfresh k)).2
  have hp_injective : Function.Injective p := by
    intro i j hij
    rcases lt_trichotomy i j with hij_lt | hij_eq | hji_lt
    · have hpi_prior : p i ∈ prior j := by
        apply Finset.mem_biUnion.mpr
        refine ⟨i, ?_, hp_mem i⟩
        simpa [mem_submodularGreedyPrefix_iff] using hij_lt
      exact False.elim (hp_not_prior j (hij ▸ hpi_prior))
    · exact hij_eq
    · have hpj_prior : p j ∈ prior i := by
        apply Finset.mem_biUnion.mpr
        refine ⟨j, ?_, hp_mem j⟩
        simpa [mem_submodularGreedyPrefix_iff] using hji_lt
      exact False.elim (hp_not_prior i (hij.symm ▸ hpj_prior))
  have hp_bijective : Function.Bijective p := Finite.injective_iff_bijective.mp hp_injective
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective p hp_bijective
  have hprefix : ∀ k,
      C k = (submodularGreedyPrefix n (k.1 + 1)).map π.toEmbedding := by
    intro k
    have hmap_subset :
        (submodularGreedyPrefix n (k.1 + 1)).map π.toEmbedding ⊆ C k := by
      intro z hz
      rcases Finset.mem_map.mp hz with ⟨i, hi, rfl⟩
      have hik : i ≤ k := by
        rw [mem_submodularGreedyPrefix_iff] at hi
        omega
      simpa [π] using hCmono hik (hp_mem i)
    have hcard_le :
        (C k).card ≤ ((submodularGreedyPrefix n (k.1 + 1)).map π.toEmbedding).card := by
      rw [Finset.card_map, hCcard k,
        submodularGreedyPrefix_card (Nat.succ_le_of_lt k.2)]
    exact (Finset.eq_of_subset_of_card_le hmap_subset hcard_le).symm
  refine ⟨τ.symm, π, ?_⟩
  intro k
  simpa [C] using hprefix k

/-- Helper for Exercise 4.26:
a greedy prefix is obtained
from its predecessor by inserting the new endpoint. -/
private theorem submodularGreedyPrefix_succ_eq_insert_local {n : ℕ} (i : Fin n) :
    submodularGreedyPrefix n (i.1 + 1) = insert i (submodularGreedyPrefix n i.1) := by
  -- Compare membership coordinatewise, separating the new endpoint from earlier indices.
  ext j
  constructor
  · intro hj
    by_cases hji : j = i
    · simp [hji]
    · apply Finset.mem_insert.mpr
      right
      rw [mem_submodularGreedyPrefix_iff] at hj ⊢
      have hval_ne : j.1 ≠ i.1 := fun hval ↦ hji (Fin.ext hval)
      omega
  · intro hj
    rcases Finset.mem_insert.mp hj with hji | hjprefix
    · subst j
      simp [mem_submodularGreedyPrefix_iff]
    · rw [mem_submodularGreedyPrefix_iff] at hjprefix ⊢
      omega

/-- Helper for Exercise 4.26:
tightness of a family
identified with permuted greedy prefixes gives the corresponding prefix-sum equalities. -/
private theorem tightGreedyPrefix_sum
    {n : ℕ} {x : Fin n → ℝ} {T : Fin n → Finset (Fin n)}
    (π : Equiv.Perm (Fin n))
    (hprefix : ∀ k,
      T k = (submodularGreedyPrefix n (k.1 + 1)).map π.toEmbedding)
    (hactive : ∀ k, (T k).sum x = permutahedron_upper_rank n (T k)) :
    ∀ r, r ≤ n →
      (submodularGreedyPrefix n r).sum (x ∘ π) =
        permutahedron_upper_rank n (submodularGreedyPrefix n r) := by
  classical
  intro r hr
  by_cases hr_zero : r = 0
  · subst r
    simp [submodularGreedyPrefix, permutahedron_upper_rank]
  · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr_zero
    have hk_lt : r - 1 < n := by
      omega
    let k : Fin n := ⟨r - 1, hk_lt⟩
    have hkr : k.1 + 1 = r := by
      simp only [k]
      omega
    have htight := hactive k
    rw [hprefix k] at htight
    -- Reindex the mapped set and use that the rank depends only on cardinality.
    simpa [Finset.sum_map, Function.comp_apply, permutahedron_upper_rank, hkr] using htight

/-- Helper for Exercise 4.26:
consecutive values of the
upper rank along the greedy-prefix chain differ by the next descending coordinate. -/
private theorem permutahedronUpperRank_greedyPrefix_succ_sub
    {n : ℕ} (k : Fin n) :
    permutahedron_upper_rank n (submodularGreedyPrefix n (k.1 + 1)) -
        permutahedron_upper_rank n (submodularGreedyPrefix n k.1) =
      (n - k.1 : ℕ) := by
  let m := n - (k.1 + 1)
  have hcurrent : n - (k.1 + 1) + 1 = m + 1 := by
    rfl
  have hprevious : n - k.1 + 1 = m + 2 := by
    unfold m
    omega
  have hremaining : n - k.1 = m + 1 := by
    unfold m
    omega
  -- Cardinality normalization reduces the rank increment to a triangular-number difference.
  rw [permutahedron_upper_rank, permutahedron_upper_rank,
    submodularGreedyPrefix_card (Nat.succ_le_of_lt k.2),
    submodularGreedyPrefix_card (Nat.le_of_lt k.2), hcurrent, hprevious,
    Nat.cast_choose_two]
  simp_rw [Nat.cast_choose_two]
  push_cast
  rw [hremaining]
  push_cast
  ring

/-- Helper for Exercise 4.26:
tightness on every member
of a permuted greedy-prefix chain forces the point to be a permutahedron vertex. -/
private theorem mem_permutahedronVertices_of_tightPrefixChain
    {n : ℕ} {x : Fin n → ℝ} {T : Fin n → Finset (Fin n)}
    (π : Equiv.Perm (Fin n))
    (hprefix : ∀ k,
      T k = (submodularGreedyPrefix n (k.1 + 1)).map π.toEmbedding)
    (hactive : ∀ k, (T k).sum x = permutahedron_upper_rank n (T k)) :
    x ∈ permutahedron_vertices n := by
  classical
  have hprefix_sum := tightGreedyPrefix_sum π hprefix hactive
  have hcoordinate : ∀ k : Fin n, x (π k) = (n - k.1 : ℕ) := by
    intro k
    have hcurrent := hprefix_sum (k.1 + 1) (Nat.succ_le_of_lt k.2)
    have hprevious := hprefix_sum k.1 (Nat.le_of_lt k.2)
    have hk_not_mem : k ∉ submodularGreedyPrefix n k.1 := by
      simp [mem_submodularGreedyPrefix_iff]
    have hsum_succ :
        (submodularGreedyPrefix n (k.1 + 1)).sum (x ∘ π) =
          x (π k) + (submodularGreedyPrefix n k.1).sum (x ∘ π) := by
      rw [submodularGreedyPrefix_succ_eq_insert_local k,
        Finset.sum_insert hk_not_mem]
      rfl
    have hrank_diff := permutahedronUpperRank_greedyPrefix_succ_sub k
    -- Subtract consecutive tight prefix equations to isolate the newly entered coordinate.
    rw [hsum_succ] at hcurrent
    linarith
  refine mem_permutahedron_vertices_iff.mpr ⟨π.symm.trans Fin.revPerm, ?_⟩
  funext i
  let k : Fin n := π.symm i
  have hki : π k = i := π.apply_symm_apply i
  have hvalue : x (π k) = (n - k.1 : ℕ) := hcoordinate k
  have hreverse : n - k.1 = k.rev.1 + 1 := by
    simp only [Fin.val_rev]
    omega
  calc
    x i = x (π k) := congrArg x hki.symm
    _ = (n - k.1 : ℕ) := hvalue
    _ = ascending_vector n ((π.symm.trans Fin.revPerm) i) := by
      simp [ascending_vector, Equiv.trans_apply, k, hreverse]

/-- Helper for Exercise 4.26: the upper-rank function is submodular, so the source proof can use
the standard active-family API for submodular polyhedra. -/
private theorem permutahedron_upper_rank_submodular (n : ℕ) :
    Submodular (permutahedron_upper_rank n) := by
  intro S T
  let a : ℕ := (S \ T).card
  let b : ℕ := (T \ S).card
  let m : ℕ := n - (S ∪ T).card
  have h_union_from_S : a + T.card = (S ∪ T).card := by
    simpa [a, Finset.union_comm, add_comm] using Finset.card_sdiff_add_card S T
  have h_union_from_T : b + S.card = (S ∪ T).card := by
    simpa [b, add_comm, Finset.union_comm] using Finset.card_sdiff_add_card T S
  have h_card_S : (S ∩ T).card + a = S.card := by
    -- Split `S` into its intersection with `T` and its complement within `S`.
    simp [a]
  have h_card_T : (S ∩ T).card + b = T.card := by
    simpa [b, Finset.inter_comm] using Finset.card_inter_add_card_sdiff T S
  have h_union_le : (S ∪ T).card ≤ n := by
    simpa [Fintype.card_fin] using Finset.card_le_univ (S ∪ T)
  have hS : n - S.card = m + b := by
    -- Express the complement of `S` inside `Fin n` as the complement of `S ∪ T` plus `T \ S`.
    unfold m
    omega
  have hT : n - T.card = m + a := by
    -- The symmetric cardinality computation gives the complement size for `T`.
    unfold m
    omega
  have hInter : n - (S ∩ T).card = m + a + b := by
    -- The complement of the intersection splits into the outside of the union and both strict
    -- differences.
    have hInter' : n - (S ∩ T).card = (n - S.card) + a := by
      omega
    calc
      n - (S ∩ T).card = (n - S.card) + a := hInter'
      _ = (m + b) + a := by rw [hS]
      _ = m + a + b := by omega
  have hchoose :
      (Nat.choose (m + b + 1) 2 : ℝ) + (Nat.choose (m + a + 1) 2 : ℝ) ≤
        (Nat.choose (m + a + b + 1) 2 : ℝ) + (Nat.choose (m + 1) 2 : ℝ) := by
    have hdiff :
        ((Nat.choose (m + a + b + 1) 2 : ℝ) + (Nat.choose (m + 1) 2 : ℝ)) -
            ((Nat.choose (m + b + 1) 2 : ℝ) + (Nat.choose (m + a + 1) 2 : ℝ)) =
          (a : ℝ) * b := by
      -- After rewriting triangular numbers as quadratic polynomials, the gap is exactly `a * b`.
      rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
      push_cast
      ring
    have hdiff_nonneg :
        0 ≤ ((Nat.choose (m + a + b + 1) 2 : ℝ) + (Nat.choose (m + 1) 2 : ℝ)) -
          ((Nat.choose (m + b + 1) 2 : ℝ) + (Nat.choose (m + a + 1) 2 : ℝ)) := by
      rw [hdiff]
      positivity
    linarith
  have hsubmodular_shape :
      ((Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (m + a + b + 1) 2 : ℝ)) +
          ((Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (m + 1) 2 : ℝ)) ≤
        ((Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (m + b + 1) 2 : ℝ)) +
          ((Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (m + a + 1) 2 : ℝ)) := by
    -- Once the common constant cancels, this is exactly the triangular-number inequality above.
    linarith
  -- Route correction: keep the source proof on the upper-rank polyhedron by proving submodularity
  -- directly from the cardinality decomposition of a crossing pair.
  simpa [permutahedron_upper_rank, hS, hT, hInter, m, add_assoc, add_left_comm, add_comm]
    using hsubmodular_shape

/-- Helper for Exercise 4.26: the integer-valued upper-rank function is also submodular. -/
private theorem permutahedron_upper_rank_int_submodular (n : ℕ) :
    Submodular (permutahedron_upper_rank_int n) := by
  intro S T
  -- Route correction: transfer the already proved real-valued submodularity statement back to
  -- the integer-valued rank function needed for integrality.
  have hreal :
      ((permutahedron_upper_rank_int n (S ∩ T) : ℝ) +
          (permutahedron_upper_rank_int n (S ∪ T) : ℝ)) ≤
        ((permutahedron_upper_rank_int n S : ℝ) +
          (permutahedron_upper_rank_int n T : ℝ)) := by
    simpa [permutahedron_upper_rank_int_cast] using permutahedron_upper_rank_submodular n S T
  exact_mod_cast hreal

/-- Helper for Exercise 4.26: an extreme point of an integral set is itself an integer vector,
because extreme points of a convex hull lie in the generating set. -/
private theorem mem_integerVectors_of_mem_extremePoints_of_is_integral
    {n : ℕ} {P : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hP : is_integral P)
    (hx : x ∈ P.extremePoints ℝ) :
    x ∈ integerVectors n := by
  -- Rewrite the integral set as the convex hull of its integer points and use the standard
  -- extreme-point inclusion for convex hulls.
  rw [is_integral_iff] at hP
  have hx' : x ∈ (convexHull ℝ (P ∩ integerVectors n)).extremePoints ℝ := by
    rw [hP] at hx
    exact hx
  exact (extremePoints_convexHull_subset hx').2

/-- Helper for Exercise 4.26: the hinted upper-bound system already places every coordinate of a
feasible point in the interval `[1, n]`. -/
private theorem coordinate_bounds_of_subset_sum_upper_bounds_and_total_sum
    (htotal : ∑ i, x i = (Nat.choose (n + 1) 2 : ℝ))
    (hupper : ∀ S : Finset (Fin n), ∑ i ∈ S, x i ≤ permutahedron_upper_rank n S)
    (i : Fin n) :
    1 ≤ x i ∧ x i ≤ (n : ℝ) := by
  have hupper' :
      ∀ S : Finset (Fin n),
        ∑ i ∈ S, x i ≤
          (Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (n - S.card + 1) 2 : ℝ) := by
    -- Expand the packaged upper-rank notation back to the hinted upper-bound formula.
    intro S
    simpa [permutahedron_upper_rank] using hupper S
  have hlower :
      ∀ S : Finset (Fin n), (Nat.choose (S.card + 1) 2 : ℝ) ≤ ∑ j ∈ S, x j :=
    subset_sum_lower_bounds_of_upper_bounds htotal hupper'
  constructor
  · -- The singleton lower bound gives the universal lower coordinate bound.
    simpa using hlower ({i} : Finset (Fin n))
  · -- The singleton upper bound gives the universal upper coordinate bound.
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.1) i.2
    have hnat : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    have hcast : (Nat.choose (n + 1) 2 : ℝ) = (Nat.choose n 2 : ℝ) + n := by
      exact_mod_cast hnat
    have hcard : n - ({i} : Finset (Fin n)).card + 1 = n := by
      simpa using Nat.succ_pred_eq_of_pos hn
    have hsingleton_rank : permutahedron_upper_rank n ({i} : Finset (Fin n)) = (n : ℝ) := by
      -- The singleton upper-rank constant simplifies to the top coordinate `n`.
      rw [permutahedron_upper_rank, hcard, hcast]
      ring
    have hi := hupper ({i} : Finset (Fin n))
    -- Normalize the singleton upper bound to the closed form `x i ≤ n`.
    simpa [hsingleton_rank] using hi

/-- Helper for Exercise 4.26: package the hinted upper-bound description as a single feasible set.
-/
private def permutahedron_upper_feasible_set (n : ℕ) : Set (Fin n → ℝ) :=
  {y |
    (∀ S : Finset (Fin n), ∑ i ∈ S, y i ≤ permutahedron_upper_rank n S) ∧
      ∑ i, y i = (Nat.choose (n + 1) 2 : ℝ)}

/-- Helper for Exercise 4.26: the full-set row of the upper-rank system is exactly the prescribed
total-sum constant. -/
private theorem permutahedron_upper_rank_univ (n : ℕ) :
    permutahedron_upper_rank n (Finset.univ : Finset (Fin n)) =
      (Nat.choose (n + 1) 2 : ℝ) := by
  -- The complement term vanishes because the full set has cardinality `n`.
  simp [permutahedron_upper_rank]

/-- Helper for Exercise 4.26: the hinted upper-bound feasible set is the top equality face of the
ambient upper-rank polyhedron. -/
private theorem permutahedron_upper_feasible_set_eq_top_face (n : ℕ) :
    permutahedron_upper_feasible_set n =
      face_set (submodularPolyhedron (permutahedron_upper_rank n))
        (subsetSumIndicator (Finset.univ : Finset (Fin n)))
        (Nat.choose (n + 1) 2 : ℝ) := by
  ext y
  rw [mem_face_set_iff, mem_submodularPolyhedron_iff]
  constructor
  · rintro ⟨hy_upper, hy_total⟩
    refine ⟨hy_upper, ?_⟩
    -- The packaged total-sum equation is the active `Finset.univ` row of the face description.
    simpa [dot_subsetSumIndicator_eq_sum] using hy_total
  · rintro ⟨hy_upper, hy_total⟩
    refine ⟨hy_upper, ?_⟩
    -- Rewriting the active `Finset.univ` row recovers the original feasible-set equation.
    simpa [dot_subsetSumIndicator_eq_sum] using hy_total

/-- Helper for Exercise 4.26: the linear functional summing the coordinates indexed by `S`. -/
private def subset_sum_linearMap {n : ℕ} (S : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i ∈ S, LinearMap.proj i

/-- Helper for Exercise 4.26: the total-coordinate-sum linear functional on `Fin n → ℝ`. -/
private def total_coordinate_sum_linearMap (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i : Fin n, LinearMap.proj i

/-- Helper for Exercise 4.26: every point of the hinted upper-bound feasible set lies in the box
`[1, n]^n`. -/
private theorem permutahedron_upper_feasible_set_subset_Icc (n : ℕ) :
    permutahedron_upper_feasible_set n ⊆
      Set.Icc (fun _ : Fin n ↦ (1 : ℝ)) (fun _ : Fin n ↦ (n : ℝ)) := by
  intro y hy
  rcases hy with ⟨hy_upper, hy_total⟩
  constructor
  · -- Read the lower coordinate bounds from the singleton subset inequalities.
    intro i
    exact (coordinate_bounds_of_subset_sum_upper_bounds_and_total_sum hy_total hy_upper i).1
  · -- Read the upper coordinate bounds from the same singleton computation.
    intro i
    exact (coordinate_bounds_of_subset_sum_upper_bounds_and_total_sum hy_total hy_upper i).2

/-- Helper for Exercise 4.26: the hinted upper-bound feasible set is closed. -/
private theorem permutahedron_upper_feasible_set_isClosed (n : ℕ) :
    IsClosed (permutahedron_upper_feasible_set n) := by
  let c : ℝ := (Nat.choose (n + 1) 2 : ℝ)
  let totalMap : (Fin n → ℝ) →ₗ[ℝ] ℝ := total_coordinate_sum_linearMap n
  have hupper_closed :
      IsClosed {y : Fin n → ℝ |
        ∀ S : Finset (Fin n), ∑ i ∈ S, y i ≤ permutahedron_upper_rank n S} := by
    -- Each subset inequality is a closed halfspace, so their intersection is closed.
    have hset :
        {y : Fin n → ℝ |
          ∀ S : Finset (Fin n), ∑ i ∈ S, y i ≤ permutahedron_upper_rank n S} =
          ⋂ S : Finset (Fin n), {y : Fin n → ℝ |
            ∑ i ∈ S, y i ≤ permutahedron_upper_rank n S} := by
      ext y
      simp
    rw [hset]
    refine isClosed_iInter fun S ↦ ?_
    let subMap : (Fin n → ℝ) →ₗ[ℝ] ℝ := subset_sum_linearMap S
    have hpre :
        {y : Fin n → ℝ | ∑ i ∈ S, y i ≤ permutahedron_upper_rank n S} =
          subMap ⁻¹' Set.Iic (permutahedron_upper_rank n S) := by
      ext y
      simp [subMap, subset_sum_linearMap]
    rw [hpre]
    exact isClosed_Iic.preimage subMap.continuous_of_finiteDimensional
  have htotal_closed :
      IsClosed {y : Fin n → ℝ | ∑ i, y i = c} := by
    -- The affine-hull equation is the preimage of a singleton under a linear map.
    have hpre :
        {y : Fin n → ℝ | ∑ i, y i = c} = totalMap ⁻¹' ({c} : Set ℝ) := by
      ext y
      simp [totalMap, total_coordinate_sum_linearMap]
    rw [hpre]
    exact isClosed_singleton.preimage totalMap.continuous_of_finiteDimensional
  -- Unfold the feasible set into the intersection of the closed inequality family and the closed
  -- total-sum hyperplane.
  unfold permutahedron_upper_feasible_set
  simpa [c] using hupper_closed.inter htotal_closed

/-- Helper for Exercise 4.26: the hinted upper-bound feasible set is convex. -/
private theorem permutahedron_upper_feasible_set_convex (n : ℕ) :
    Convex ℝ (permutahedron_upper_feasible_set n) := by
  let c : ℝ := (Nat.choose (n + 1) 2 : ℝ)
  let totalMap : (Fin n → ℝ) →ₗ[ℝ] ℝ := total_coordinate_sum_linearMap n
  have hupper_convex :
      Convex ℝ {y : Fin n → ℝ |
        ∀ S : Finset (Fin n), ∑ i ∈ S, y i ≤ permutahedron_upper_rank n S} := by
    -- Each subset inequality defines a convex halfspace, and convexity survives intersections.
    have hset :
        {y : Fin n → ℝ |
          ∀ S : Finset (Fin n), ∑ i ∈ S, y i ≤ permutahedron_upper_rank n S} =
          ⋂ S : Finset (Fin n), {y : Fin n → ℝ |
            ∑ i ∈ S, y i ≤ permutahedron_upper_rank n S} := by
      ext y
      simp
    rw [hset]
    refine convex_iInter fun S ↦ ?_
    let subMap : (Fin n → ℝ) →ₗ[ℝ] ℝ := subset_sum_linearMap S
    have hpre :
        {y : Fin n → ℝ | ∑ i ∈ S, y i ≤ permutahedron_upper_rank n S} =
          subMap ⁻¹' Set.Iic (permutahedron_upper_rank n S) := by
      ext y
      simp [subMap, subset_sum_linearMap]
    rw [hpre]
    exact (convex_Iic (permutahedron_upper_rank n S)).linear_preimage subMap
  have htotal_convex :
      Convex ℝ {y : Fin n → ℝ | ∑ i, y i = c} := by
    -- The affine-hull equation is the preimage of a convex singleton.
    have hpre :
        {y : Fin n → ℝ | ∑ i, y i = c} = totalMap ⁻¹' ({c} : Set ℝ) := by
      ext y
      simp [totalMap, total_coordinate_sum_linearMap]
    rw [hpre]
    exact (convex_singleton c).linear_preimage totalMap
  -- Intersect the convex inequality region with the convex total-sum hyperplane.
  unfold permutahedron_upper_feasible_set
  simpa [c] using hupper_convex.inter htotal_convex

/-- Helper for Exercise 4.26: the hinted upper-bound feasible set is compact. -/
private theorem permutahedron_upper_feasible_set_isCompact (n : ℕ) :
    IsCompact (permutahedron_upper_feasible_set n) := by
  -- Closedness plus the coordinate box from the singleton bounds yields compactness.
  refine IsCompact.of_isClosed_subset (isCompact_Icc : IsCompact
      (Set.Icc (fun _ : Fin n ↦ (1 : ℝ)) (fun _ : Fin n ↦ (n : ℝ)))) ?_ ?_
  · exact permutahedron_upper_feasible_set_isClosed n
  · exact permutahedron_upper_feasible_set_subset_Icc n

/-- Helper for Exercise 4.26: the `Finset.univ` inequality is valid on the ambient upper-rank
polyhedron. -/
private theorem upper_rank_univ_is_valid_inequality (n : ℕ) :
    is_valid_inequality (submodularPolyhedron (permutahedron_upper_rank n))
      (subsetSumIndicator (Finset.univ : Finset (Fin n)))
      (Nat.choose (n + 1) 2 : ℝ) := by
  intro y hy
  have hy_univ := (mem_submodularPolyhedron_iff.mp hy) (Finset.univ : Finset (Fin n))
  simpa [permutahedron_upper_rank_univ, dot_subsetSumIndicator_eq_sum] using hy_univ

/-- Helper for Exercise 4.26: an extreme point of the top equality face is already an extreme
point of the ambient upper-rank polyhedron. -/
private theorem upper_face_extreme_point_is_ambient_extreme_point
    {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ (permutahedron_upper_feasible_set n).extremePoints ℝ) :
    x ∈ (submodularPolyhedron (permutahedron_upper_rank n)).extremePoints ℝ := by
  rw [permutahedron_upper_feasible_set_eq_top_face] at hx
  have hface_exposed :
      IsExposed ℝ (submodularPolyhedron (permutahedron_upper_rank n))
        (face_set (submodularPolyhedron (permutahedron_upper_rank n))
          (subsetSumIndicator (Finset.univ : Finset (Fin n)))
          (Nat.choose (n + 1) 2 : ℝ)) := by
    -- The full-set equality row is a valid inequality, so its equality slice is an exposed face.
    exact isExposed_face_set_of_valid_inequality (upper_rank_univ_is_valid_inequality n)
  -- Extreme points of an exposed face remain extreme in the ambient polyhedron.
  exact hface_exposed.isExtreme.extremePoints_subset_extremePoints hx

/-- Helper for Exercise 4.26: an extreme point of the hinted upper-bound feasible set already lies
in the ambient upper-rank polyhedron. -/
private theorem extreme_point_of_upper_feasible_set_mem_upper_polyhedron
    {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ (permutahedron_upper_feasible_set n).extremePoints ℝ) :
    x ∈ submodularPolyhedron (permutahedron_upper_rank n) := by
  rw [permutahedron_upper_feasible_set_eq_top_face] at hx
  -- Extreme points lie in the face itself, hence in the ambient polyhedron component.
  exact (mem_face_set_iff.mp (extremePoints_subset hx)).1

/-- Helper for Exercise 4.26: an extreme point of the hinted upper-bound feasible set is tight on
the full-set equality row. -/
private theorem extreme_point_of_upper_feasible_set_total_sum
    {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ (permutahedron_upper_feasible_set n).extremePoints ℝ) :
    ∑ i, x i = (Nat.choose (n + 1) 2 : ℝ) := by
  rw [permutahedron_upper_feasible_set_eq_top_face] at hx
  have hx_tight : subsetSumIndicator (Finset.univ : Finset (Fin n)) ⬝ᵥ x =
      (Nat.choose (n + 1) 2 : ℝ) :=
    (mem_face_set_iff.mp (extremePoints_subset hx)).2
  -- Expanding the full-set indicator turns the active face equation back into the total-sum form.
  simpa [dot_subsetSumIndicator_eq_sum] using hx_tight

/-- Helper for Exercise 4.26: the remaining source-faithful blocker is to classify the extreme
points of the hinted upper-bound feasible set as permutahedron vertices. -/
private theorem extreme_point_of_upper_feasible_set_mem_permutahedron
    {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ (permutahedron_upper_feasible_set n).extremePoints ℝ) :
    x ∈ permutahedron n := by
  -- Route correction: integrality alone does not classify the vertex. Instead, pass to the
  -- ambient upper-rank polyhedron and use the now-available laminar active-basis theorem.
  have hx_poly : x ∈ submodularPolyhedron (permutahedron_upper_rank n) :=
    extreme_point_of_upper_feasible_set_mem_upper_polyhedron hx
  have hx_ambient :
      x ∈ (submodularPolyhedron (permutahedron_upper_rank n)).extremePoints ℝ :=
    upper_face_extreme_point_is_ambient_extreme_point hx
  have hsubmodular : Submodular (permutahedron_upper_rank n) :=
    permutahedron_upper_rank_submodular n
  obtain ⟨T, hlaminar, hactive, hlinear⟩ :=
    vertex_submodularPolyhedron_has_laminar_active_inequalities
      (permutahedron_upper_rank n) hsubmodular hx_ambient
  obtain ⟨hnonempty, hinjective, hchain⟩ :=
    activeLaminarIndependentFamily_isChain hx_poly hlaminar hactive hlinear
  obtain ⟨τ, π, hprefix⟩ :=
    existsPerm_map_greedyPrefix_eq_of_chain hnonempty hinjective hchain
  have hvertex : x ∈ permutahedron_vertices n := by
    -- Normalize the active chain to permuted prefixes and telescope its tight equalities.
    exact mem_permutahedronVertices_of_tightPrefixChain π hprefix
      (fun k ↦ hactive (τ k))
  -- A permutation vertex belongs to the convex hull defining the permutahedron.
  rw [permutahedron_eq_convexHull]
  exact subset_convexHull ℝ (permutahedron_vertices n) hvertex

/-- Helper for Exercise 4.26: after converting to the hinted upper-bound system, the remaining
task is to show that the hinted upper-bound face is exactly the
permutahedron. -/
private theorem mem_permutahedron_of_subset_sum_upper_bounds_and_total_sum
    (htotal : ∑ i, x i = (Nat.choose (n + 1) 2 : ℝ))
    (hupper : ∀ S : Finset (Fin n), ∑ i ∈ S, x i ≤ permutahedron_upper_rank n S) :
    x ∈ permutahedron n := by
  have hx_mem : x ∈ permutahedron_upper_feasible_set n := by
    -- Bundle the upper bounds and the total-sum equality into one feasible-set membership fact.
    exact ⟨hupper, htotal⟩
  have hcompact : IsCompact (permutahedron_upper_feasible_set n) :=
    permutahedron_upper_feasible_set_isCompact n
  have hconvex : Convex ℝ (permutahedron_upper_feasible_set n) :=
    permutahedron_upper_feasible_set_convex n
  have hclosure :
      closure (convexHull ℝ ((permutahedron_upper_feasible_set n).extremePoints ℝ)) =
        permutahedron_upper_feasible_set n :=
    closure_convexHull_extremePoints hcompact hconvex
  have hperm_closed : IsClosed (permutahedron n) := by
    -- The permutahedron is the convex hull of a finite vertex set, hence compact and closed.
    have hperm_compact : IsCompact (permutahedron n) := by
      rw [permutahedron_eq_convexHull]
      simpa [permutahedron_vertices] using
        (Set.finite_range
          (fun σ : Equiv.Perm (Fin n) ↦ ascending_vector n ∘ σ)).isCompact_convexHull ℝ
    exact hperm_compact.isClosed
  have hextreme_subset :
      (permutahedron_upper_feasible_set n).extremePoints ℝ ⊆ permutahedron n := by
    -- The remaining missing input is exactly the extreme-point classification of the upper face.
    intro y hy
    exact extreme_point_of_upper_feasible_set_mem_permutahedron hy
  have hhull_subset :
      convexHull ℝ ((permutahedron_upper_feasible_set n).extremePoints ℝ) ⊆ permutahedron n := by
    -- Once the extreme points lie in `Π_n`, convexity of `Π_n` absorbs their convex hull.
    rw [permutahedron_eq_convexHull]
    exact convexHull_min hextreme_subset (convex_convexHull ℝ _)
  have hx_closure :
      x ∈ closure (convexHull ℝ ((permutahedron_upper_feasible_set n).extremePoints ℝ)) := by
    -- Krein-Milman reconstructs the compact convex feasible set from its extreme points.
    rw [hclosure]
    exact hx_mem
  -- The remaining inclusion is now reduced to showing that the extreme points are permutation
  -- vertices, which is isolated in the helper above.
  exact closure_minimal hhull_subset hperm_closed hx_closure

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_26.lean
Exercise 4.26. A point of the permutahedron `Π_n` is characterized by the subset-sum lower bound
inequalities
`∑ i ∈ S, x i ≥ \binom{|S| + 1}{2}` for every `S ⊆ Fin n`, together with the constant-sum
equation `∑ i, x i = \binom{n + 1}{2}`. The empty and full subsets are automatic from the same
formula and the total-sum constraint. -/
theorem mem_permutahedron_iff_subset_sum_lower_bounds_and_total_sum
    {n : ℕ} {x : Fin n → ℝ} :
    x ∈ permutahedron n ↔
      (∀ S : Finset (Fin n), (Nat.choose (S.card + 1) 2 : ℝ) ≤ ∑ i ∈ S, x i) ∧
      ∑ i, x i = (Nat.choose (n + 1) 2 : ℝ) := by
  constructor
  · intro hx
    refine ⟨?_, permutahedron_subset_constant_sum_hyperplane n hx⟩
    intro S
    exact permutahedron_subset_sum_inequality_valid n S hx
  · rintro ⟨hlower, htotal⟩
    -- Route correction: first move to the hinted upper-bound formulation, then isolate the
    -- remaining inclusion of that upper-bound face into the permutahedron.
    have hupper :
        ∀ S : Finset (Fin n), ∑ i ∈ S, x i ≤ permutahedron_upper_rank n S := by
      intro S
      simpa [permutahedron_upper_rank] using
        subset_sum_upper_bounds_of_lower_bounds htotal hlower S
    exact mem_permutahedron_of_subset_sum_upper_bounds_and_total_sum htotal hupper

/-- Using complements, the subset-sum description of the permutahedron is equivalently given by
the upper bounds
`∑ i ∈ S, x i ≤ \binom{n + 1}{2} - \binom{n - |S| + 1}{2}` for every `S ⊆ Fin n`, together with
the same constant-sum equation. The empty and full subsets are again automatic. -/
theorem mem_permutahedron_iff_subset_sum_upper_bounds_and_total_sum
    {n : ℕ} {x : Fin n → ℝ} :
    x ∈ permutahedron n ↔
      (∀ S : Finset (Fin n),
        ∑ i ∈ S, x i ≤
          (Nat.choose (n + 1) 2 : ℝ) - (Nat.choose (n - S.card + 1) 2 : ℝ)) ∧
      ∑ i, x i = (Nat.choose (n + 1) 2 : ℝ) := by
  rw [mem_permutahedron_iff_subset_sum_lower_bounds_and_total_sum]
  constructor
  · rintro ⟨hlower, htotal⟩
    exact ⟨subset_sum_upper_bounds_of_lower_bounds htotal hlower, htotal⟩
  · rintro ⟨hupper, htotal⟩
    exact ⟨subset_sum_lower_bounds_of_upper_bounds htotal hupper, htotal⟩

end

#print axioms mem_permutahedron_iff_subset_sum_lower_bounds_and_total_sum
