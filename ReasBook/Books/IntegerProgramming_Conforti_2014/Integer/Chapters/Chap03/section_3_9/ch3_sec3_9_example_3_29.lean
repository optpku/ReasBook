/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_20
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3

open scoped BigOperators

/-- The coefficient vector of the subset-sum inequality indexed by `K`. -/
def subsetSumIndicator {n : ℕ} (K : Finset (Fin n)) : Fin n → ℝ :=
  fun i ↦ if i ∈ K then 1 else 0

/-- `subsetSumIndicator K ⬝ᵥ x` is the sum of the coordinates of `x` over `K`. -/
lemma dot_subsetSumIndicator_eq_sum {n : ℕ} (K : Finset (Fin n)) (x : Fin n → ℝ) :
    subsetSumIndicator K ⬝ᵥ x = ∑ i ∈ K, x i := by
  classical
  simp [subsetSumIndicator, dotProduct]

/-- Membership in the subset-sum equality face means lying in `Π_n` and satisfying the
subset-sum inequality for `K` at equality. -/
theorem mem_permutahedron_subset_sum_face_iff {n : ℕ} {K : Finset (Fin n)} {x : Fin n → ℝ} :
    x ∈ face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ)) ↔
      x ∈ permutahedron n ∧ ∑ i ∈ K, x i = (Nat.choose (K.card + 1) 2 : ℝ) := by
  rw [mem_face_set_iff]
  constructor
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, ?_⟩
    simpa [dot_subsetSumIndicator_eq_sum] using congrArg Neg.neg hxEq
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, ?_⟩
    simpa [dot_subsetSumIndicator_eq_sum] using congrArg Neg.neg hxEq

/-- Helper for Example 3.29: the sum of the first `k` positive integers is
`\binom{k + 1}{2}`. -/
lemma sum_range_initial_segment_eq_choose (k : ℕ) :
    (∑ i ∈ Finset.range k, ((i : ℝ) + 1)) = (Nat.choose (k + 1) 2 : ℝ) := by
  induction k with
  | zero =>
      simp
  | succ k hk =>
      rw [Finset.sum_range_succ, hk]
      norm_num [Nat.choose_succ_succ, Nat.choose_one_right]
      ring

/-- Helper for Example 3.29: the same arithmetic progression written as a sum over `Fin k`. -/
lemma sum_univ_initial_segment_eq_choose (k : ℕ) :
    (∑ i : Fin k, (((i : ℕ) : ℝ) + 1)) = (Nat.choose (k + 1) 2 : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range fun i : ℕ ↦ ((i : ℝ) + 1)]
  exact sum_range_initial_segment_eq_choose k

/-- Helper for Example 3.29: among `k` distinct naturals, the smallest possible value of
`∑ (t + 1)` is attained on `{0, ..., k - 1}`. -/
lemma sum_of_distinct_nat_indices_ge_triangular (S : Finset ℕ) :
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
    -- The increasing enumeration of `S` dominates the identity on positions.
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
    -- Apply the previous index bound termwise after adding one.
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

/-- Helper for Example 3.29: the same lower bound applies to any finite set of distinct
indices in `Fin n`. -/
lemma sum_of_distinct_fin_indices_ge_triangular {n : ℕ} (S : Finset (Fin n)) :
    (Nat.choose (S.card + 1) 2 : ℝ) ≤ ∑ t ∈ S, (((t : ℕ) : ℝ) + 1) := by
  classical
  have hrewrite :
      ∑ t ∈ S, (((t : ℕ) : ℝ) + 1) =
        ∑ u ∈ S.image (fun t : Fin n ↦ (t : ℕ)), ((u : ℝ) + 1) := by
    -- Replace the `Fin n`-indices by their distinct natural values.
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

/-- Validity statement for Example 3.29 (1), expressed in the Chapter 3 owner
`is_valid_inequality`: the subset-sum
inequality is valid for the permutahedron `Π_n`. -/
theorem permutahedron_subset_sum_is_valid_inequality (n : ℕ) (K : Finset (Fin n)) :
    is_valid_inequality (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
  classical
  let c : ℝ := (Nat.choose (K.card + 1) 2 : ℝ)
  let H : Set (Fin n → ℝ) := {x : Fin n → ℝ | ∑ i ∈ K, x i ≥ c}
  have hvertices :
      permutahedron_vertices n ⊆ H := by
    intro x hx
    rcases mem_permutahedron_vertices_iff.mp hx with ⟨σ, rfl⟩
    -- The values on `K` are `|K|` distinct elements of `{1, ..., n}`.
    change c ≤ ∑ i ∈ K, ascending_vector n (σ i)
    have hrewrite :
        ∑ i ∈ K, ascending_vector n (σ i) =
          ∑ t ∈ K.image σ, ascending_vector n t := by
      exact (Finset.sum_image σ.injective.injOn).symm
    rw [hrewrite]
    have hcard : (K.image σ).card = K.card := by
      simpa using Finset.card_image_of_injective K σ.injective
    simpa [c, ascending_vector, hcard] using
      sum_of_distinct_fin_indices_ge_triangular (K.image σ)
  have hconvex : Convex ℝ H := by
    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ K, LinearMap.proj i
    have hpreimage : H = L ⁻¹' Set.Ici c := by
      -- The inequality is the linear preimage of a closed halfspace in `ℝ`.
      ext x
      simp [H, L, c]
    rw [hpreimage]
    exact (convex_Ici c).linear_preimage L
  -- Extend the vertex inequality from the generators to their convex hull.
  have hsubset : permutahedron n ⊆ H := by
    rw [permutahedron_eq_convexHull]
    exact convexHull_min hvertices hconvex
  intro x hx
  have hxH : c ≤ ∑ i ∈ K, x i := hsubset hx
  simpa [c, dot_subsetSumIndicator_eq_sum] using neg_le_neg hxH

/-- Set version of Example 3.29 (1): for every subset `K ⊆ {1, …, n}`, the inequality
`∑_{i ∈ K} x_i ≥ \binom{|K| + 1}{2}` is valid for the permutahedron `Π_n`. -/
theorem permutahedron_subset_sum_inequality_valid (n : ℕ) (K : Finset (Fin n)) :
    permutahedron n ⊆
      {x : Fin n → ℝ | ∑ i ∈ K, x i ≥ (Nat.choose (K.card + 1) 2 : ℝ)} := by
  intro x hx
  have hx' := permutahedron_subset_sum_is_valid_inequality n K hx
  simpa [dot_subsetSumIndicator_eq_sum] using neg_le_neg hx'

/-- Helper for Example 3.29: swapping two coordinates changes a dot product by the expected
rank-one term. -/
lemma dotProduct_comp_swap_sub_eq {n : ℕ} (c x : Fin n → ℝ) (i j : Fin n) :
    c ⬝ᵥ (x ∘ Equiv.swap i j) - c ⬝ᵥ x = (c i - c j) * (x j - x i) := by
  classical
  by_cases hij : i = j
  · -- If the swap is trivial, both sides vanish immediately.
    subst hij
    simp
  · have hswap_reindex :
        ∑ k : Fin n, c k * (x ∘ Equiv.swap i j) k =
          ∑ k : Fin n, c (Equiv.swap i j k) * x k := by
      -- Reindex the swapped sum through the involutive permutation `swap i j`.
      simpa [Function.comp_apply] using
        (Equiv.sum_comp (e := Equiv.swap i j)
          (g := fun k : Fin n ↦ c k * x (Equiv.swap i j k))).symm
    have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := by simp
    have hj_mem : j ∈ (Finset.univ : Finset (Fin n)) := by simp
    have hj_mem_erase : j ∈ (Finset.univ.erase i : Finset (Fin n)) := by
      simp [Finset.mem_erase, hij, eq_comm]
    have hswap_rest :
        Finset.sum ((Finset.univ.erase i).erase j) (fun k ↦ c (Equiv.swap i j k) * x k) =
          Finset.sum ((Finset.univ.erase i).erase j) (fun k ↦ c k * x k) := by
      -- Away from `i` and `j`, the swap fixes every index.
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk_ne_j : k ≠ j := (Finset.mem_erase.mp hk).1
      have hk_ne_i : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      simp [Equiv.swap_apply_of_ne_of_ne hk_ne_i hk_ne_j]
    have hswap_sum :
        ∑ k : Fin n, c (Equiv.swap i j k) * x k =
          c j * x i + c i * x j +
            Finset.sum ((Finset.univ.erase i).erase j) (fun k ↦ c k * x k) := by
      -- Split off the two swapped coordinates; on the remaining indices the swap is the identity.
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hi_mem]
      rw [Finset.sdiff_singleton_eq_erase]
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hj_mem_erase]
      rw [Finset.sdiff_singleton_eq_erase]
      rw [hswap_rest]
      simp [Equiv.swap_apply_left, Equiv.swap_apply_right, add_assoc]
    have hplain_sum :
        ∑ k : Fin n, c k * x k =
          c i * x i + c j * x j +
            Finset.sum ((Finset.univ.erase i).erase j) (fun k ↦ c k * x k) := by
      -- The unswapped dot product has the same common remainder after the same
      -- two-coordinate split.
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hi_mem]
      rw [Finset.sdiff_singleton_eq_erase]
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hj_mem_erase]
      rw [Finset.sdiff_singleton_eq_erase]
      ring
    -- After the common remainder cancels, only the two-coordinate rank-one contribution remains.
    calc
      c ⬝ᵥ (x ∘ Equiv.swap i j) - c ⬝ᵥ x
          = (∑ k : Fin n, c (Equiv.swap i j k) * x k) - ∑ k : Fin n, c k * x k := by
              rw [dotProduct, dotProduct, hswap_reindex]
      _ = (c j * x i + c i * x j +
            Finset.sum ((Finset.univ.erase i).erase j) (fun k ↦ c k * x k)) -
            (c i * x i + c j * x j +
              Finset.sum ((Finset.univ.erase i).erase j) (fun k ↦ c k * x k)) := by
              rw [hswap_sum, hplain_sum]
      _ = (c i - c j) * (x j - x i) := by
              ring

/-- Helper for Example 3.29: swapping two coordinates on the same side of the partition indexed by
`K` leaves the subset-sum functional unchanged. -/
lemma dot_subsetSumIndicator_comp_swap_eq_of_same_membership {n : ℕ}
    (K : Finset (Fin n)) (x : Fin n → ℝ) (i j : Fin n)
    (hmem : i ∈ K ↔ j ∈ K) :
    subsetSumIndicator K ⬝ᵥ (x ∘ Equiv.swap i j) = subsetSumIndicator K ⬝ᵥ x := by
  -- Reduce the claim to the swap formula and note that the two coefficients are equal.
  apply sub_eq_zero.mp
  rw [dotProduct_comp_swap_sub_eq (c := subsetSumIndicator K) (x := x) i j]
  by_cases hi : i ∈ K
  · have hj : j ∈ K := hmem.mp hi
    simp [subsetSumIndicator, hi, hj]
  · have hj : j ∉ K := fun hj ↦ hi (hmem.mpr hj)
    simp [subsetSumIndicator, hi, hj]

/-- Helper for Example 3.29: swapping a `K`-coordinate with a larger coordinate outside `K`
strictly increases the subset-sum functional. -/
lemma dot_subsetSumIndicator_lt_comp_swap_of_mem_not_mem {n : ℕ}
    (K : Finset (Fin n)) (x : Fin n → ℝ) (i j : Fin n)
    (hi : i ∈ K) (hj : j ∉ K) (hijx : x i < x j) :
    subsetSumIndicator K ⬝ᵥ x < subsetSumIndicator K ⬝ᵥ (x ∘ Equiv.swap i j) := by
  -- The cross-block swap replaces `x i` in the `K`-sum by the larger value `x j`.
  have hpos :
      0 < subsetSumIndicator K ⬝ᵥ (x ∘ Equiv.swap i j) - subsetSumIndicator K ⬝ᵥ x := by
    rw [dotProduct_comp_swap_sub_eq (c := subsetSumIndicator K) (x := x) i j]
    simpa [subsetSumIndicator, hi, hj] using sub_pos.mpr hijx
  exact sub_pos.mp hpos

/-- Helper for Example 3.29: the ascending vector has distinct coordinates. -/
lemma ascending_vector_injective (n : ℕ) : Function.Injective (ascending_vector n) := by
  intro i j hij
  apply Fin.ext
  -- The coordinates differ by exactly one from the `Fin` values.
  norm_num [ascending_vector] at hij ⊢
  omega

/-- Helper for Example 3.29: there is a permutation whose first `K.card` ranks are exactly the
indices in `K`. -/
lemma exists_block_order_permutation {n : ℕ} (K : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, i ∈ K ↔ (σ i : Nat) < K.card := by
  classical
  let splitIndex : Fin n ≃ ↥K ⊕ {i // i ∉ K} :=
    (Equiv.sumCompl fun i : Fin n ↦ i ∈ K).symm
  let blockIndex : ↥K ≃ Fin K.card := Finset.equivFin K
  let complSubtype :
      {i : Fin n // i ∉ K} ≃ ↥(Kᶜ) :=
    { toFun := fun i ↦
        match i with
        | ⟨j, hj⟩ => ⟨j, by simpa [Finset.mem_compl] using hj⟩
      invFun := fun i ↦
        match i with
        | ⟨j, hj⟩ => ⟨j, by simpa [Finset.mem_compl] using hj⟩
      left_inv := by
        intro i
        cases i
        rfl
      right_inv := by
        intro i
        cases i
        rfl }
  let complIndexKc : ↥(Kᶜ) ≃ Fin (n - K.card) :=
    Finset.equivFinOfCardEq (by simp [Finset.card_compl, Fintype.card_fin])
  let complIndex : {i // i ∉ K} ≃ Fin (n - K.card) :=
    complSubtype.trans complIndexKc
  have hcard_sum : K.card + (n - K.card) = n := by
    simpa [Fintype.card_fin] using Nat.add_sub_of_le (Finset.card_le_univ K)
  let σ : Equiv.Perm (Fin n) :=
    ((splitIndex.trans (Equiv.sumCongr blockIndex complIndex)).trans finSumFinEquiv).trans
      (Fin.castOrderIso hcard_sum).toEquiv
  refine ⟨σ, ?_⟩
  intro i
  constructor
  · intro hi
    -- The `K`-part of the split lands in the initial `K.card` segment after concatenation.
    simp [σ, splitIndex, blockIndex, complSubtype, complIndexKc, complIndex, hi]
  · intro hiσ
    by_contra hiK
    -- Outside `K`, the concatenated index is in the trailing block, so it cannot be `< K.card`.
    have hσi :
        (σ i : Nat) = K.card + ((complIndex ⟨i, hiK⟩ : Fin (n - K.card)) : Nat) := by
      simp [σ, splitIndex, blockIndex, complSubtype, complIndexKc, complIndex, hiK]
    omega

/-- Helper for Example 3.29: summing the ordered permutation vertex over the block `K` gives the
expected triangular number. -/
lemma sum_on_block_ordered_permutation_eq_choose
    {n : ℕ} (K : Finset (Fin n)) (hK_le : K.card ≤ n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, i ∈ K ↔ (σ i : Nat) < K.card) :
    ∑ i ∈ K, (ascending_vector n ∘ σ) i = (Nat.choose (K.card + 1) 2 : ℝ) := by
  classical
  let orderedIndex : Fin K.card → Fin n := fun j ↦ σ.symm (Fin.castLE hK_le j)
  have hordered_inj :
      Set.InjOn orderedIndex ↑(Finset.univ : Finset (Fin K.card)) := by
    -- Different ordered positions give different preimages under `σ`.
    exact (σ.symm.injective.comp (Fin.castLE_injective hK_le)).injOn
  have himage :
      Finset.image orderedIndex Finset.univ = K := by
    -- The hypothesis `hσ` says exactly that `K` is the initial segment in the `σ`-order.
    ext i
    constructor
    · intro hi
      rw [Finset.mem_image] at hi
      rcases hi with ⟨j, -, rfl⟩
      have hordered_eq : σ (orderedIndex j) = Fin.castLE hK_le j := by
        simp [orderedIndex]
      have hordered_lt : (σ (orderedIndex j) : Nat) < K.card := by
        rw [hordered_eq]
        exact j.2
      exact (hσ (orderedIndex j)).2 hordered_lt
    · intro hi
      let j : Fin K.card := ⟨(σ i : Nat), (hσ i).1 hi⟩
      refine Finset.mem_image.mpr ⟨j, by simp, ?_⟩
      apply σ.injective
      simp [orderedIndex, j]
  -- Reindex the `K`-sum through the first `K.card` ordered positions and evaluate
  -- the initial segment.
  calc
    ∑ i ∈ K, (ascending_vector n ∘ σ) i
        = Finset.sum (Finset.image orderedIndex Finset.univ)
            (fun i ↦ (ascending_vector n ∘ σ) i) := by
            rw [himage]
    _ = Finset.sum Finset.univ
          (fun j : Fin K.card ↦ (ascending_vector n ∘ σ) (orderedIndex j)) := by
          exact Finset.sum_image hordered_inj
    _ = Finset.sum Finset.univ (fun j : Fin K.card ↦ (((j : ℕ) : ℝ) + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [orderedIndex, ascending_vector]
    _ = (Nat.choose (K.card + 1) 2 : ℝ) := by
          simpa using sum_univ_initial_segment_eq_choose K.card

/-- Helper for Example 3.29: the ordered permutation vertex is tight for the subset-sum face and
its `K`-coordinates are strictly smaller than its `Kᶜ`-coordinates. -/
lemma exists_tight_permutahedron_vertex_with_block_order
    {n : ℕ} (K : Finset (Fin n)) (_hK_nonempty : K.Nonempty) (hK_proper : K.card < n) :
    ∃ xbar : Fin n → ℝ,
      xbar ∈ face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ)) ∧
      xbar ∈ permutahedron_vertices n ∧
      (∀ ⦃i j : Fin n⦄, i ∈ K → j ∈ K → i ≠ j → xbar i ≠ xbar j) ∧
      (∀ ⦃i j : Fin n⦄, i ∉ K → j ∉ K → i ≠ j → xbar i ≠ xbar j) ∧
      (∀ ⦃i j : Fin n⦄, i ∈ K → j ∉ K → xbar i < xbar j) := by
  classical
  rcases exists_block_order_permutation K with ⟨σ, hσ⟩
  let xbar : Fin n → ℝ := ascending_vector n ∘ σ
  have hx_vertices : xbar ∈ permutahedron_vertices n := by
    -- The ordered witness is one of the permutahedron vertices by construction.
    exact mem_permutahedron_vertices_iff.mpr ⟨σ, rfl⟩
  have hx_perm : xbar ∈ permutahedron n := by
    -- Every vertex of the permutahedron lies in its convex hull.
    rw [permutahedron_eq_convexHull]
    exact subset_convexHull ℝ (permutahedron_vertices n) hx_vertices
  have hx_sum :
      ∑ i ∈ K, xbar i = (Nat.choose (K.card + 1) 2 : ℝ) := by
    -- Reindex the `K`-sum through the first `K.card` positions of the ordered permutation.
    simpa [xbar] using
      sum_on_block_ordered_permutation_eq_choose K hK_proper.le σ hσ
  have hx_face :
      xbar ∈ face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
    -- The ordered vertex is tight for the subset-sum inequality by the computed equality.
    rw [mem_permutahedron_subset_sum_face_iff]
    exact ⟨hx_perm, hx_sum⟩
  refine ⟨xbar, hx_face, hx_vertices, ?_, ?_, ?_⟩
  · intro i j hi hj hij hx_eq
    -- Distinct indices inside `K` have different ranks, hence different ascending values.
    apply hij
    exact σ.injective <| ascending_vector_injective n hx_eq
  · intro i j hi hj hij hx_eq
    -- The same injectivity argument works inside the complementary block.
    apply hij
    exact σ.injective <| ascending_vector_injective n hx_eq
  · intro i j hi hj
    -- The block-order permutation makes every `K`-coordinate strictly smaller than every `Kᶜ`
    -- coordinate.
    have hi_lt : (σ i : Nat) < K.card := (hσ i).1 hi
    have hj_ge : K.card ≤ (σ j : Nat) := by
      exact Nat.le_of_not_lt fun hj_lt ↦ hj ((hσ j).2 hj_lt)
    have hij_lt : (σ i : Nat) < (σ j : Nat) := lt_of_lt_of_le hi_lt hj_ge
    change (((σ i : ℕ) : ℝ) + 1) < (((σ j : ℕ) : ℝ) + 1)
    exact_mod_cast Nat.succ_lt_succ hij_lt

/-- Helper for Example 3.29: a two-block coefficient vector rewrites into the constant-sum term
plus the subset-sum term on `K`. -/
lemma dot_two_block_coefficients_eq {n : ℕ} (K : Finset (Fin n)) (lam mu : ℝ)
    (x : Fin n → ℝ) :
    (fun i ↦ if i ∈ K then lam else mu) ⬝ᵥ x =
      mu * ∑ i, x i + (lam - mu) * ∑ i ∈ K, x i := by
  classical
  calc
    (fun i ↦ if i ∈ K then lam else mu) ⬝ᵥ x = ∑ i, (if i ∈ K then lam else mu) * x i := by
      simp [dotProduct]
    _ = ∑ i, (mu + if i ∈ K then lam - mu else 0) * x i := by
      -- Rewrite the two blockwise coefficients as the baseline `mu` plus the `K`-correction.
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hiK : i ∈ K
      · simp [hiK]
      · simp [hiK]
    _ = ∑ i, (mu * x i + (if i ∈ K then lam - mu else 0) * x i) := by
      -- Distribute the rewritten coefficient across `x i`.
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    _ = ∑ i, mu * x i + ∑ i, (if i ∈ K then lam - mu else 0) * x i := by
      rw [Finset.sum_add_distrib]
    _ = mu * ∑ i, x i + ∑ i, (if i ∈ K then lam - mu else 0) * x i := by
      rw [← Finset.mul_sum]
    _ = mu * ∑ i, x i + ∑ i ∈ K, (lam - mu) * x i := by
      congr 1
      calc
        ∑ i, (if i ∈ K then lam - mu else 0) * x i
            = ∑ i, if i ∈ K then (lam - mu) * x i else 0 := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                by_cases hiK : i ∈ K <;> simp [hiK]
        _ = ∑ i ∈ K, (lam - mu) * x i := by
          refine
            (Finset.sum_ite_mem (s := Finset.univ) (t := K)
              (f := fun i ↦ (lam - mu) * x i)).trans ?_
          simp
    _ = mu * ∑ i, x i + (lam - mu) * ∑ i ∈ K, x i := by
      have hmul : ∑ i ∈ K, (lam - mu) * x i = (lam - mu) * ∑ i ∈ K, x i := by
        rw [Finset.mul_sum]
      rw [hmul]

/-- Helper for Example 3.29: swapping two coordinates of a permutation vertex stays inside the
permutahedron. -/
lemma swap_vertex_mem_permutahedron_of_mem_vertices {n : ℕ} {x : Fin n → ℝ} {i j : Fin n}
    (hx : x ∈ permutahedron_vertices n) :
    x ∘ Equiv.swap i j ∈ permutahedron n := by
  rcases mem_permutahedron_vertices_iff.mp hx with ⟨σ, rfl⟩
  -- The swapped point is again a permuted ascending vector, hence another vertex.
  rw [permutahedron_eq_convexHull]
  exact subset_convexHull ℝ (permutahedron_vertices n)
    (mem_permutahedron_vertices_iff.mpr ⟨σ * Equiv.swap i j, rfl⟩)

/-- Helper for Example 3.29: if a point and its coordinate swap lie on the same equality face,
then the swapped coordinates have equal coefficients whenever the point distinguishes them. -/
lemma coefficient_eq_of_swap_in_face {n : ℕ} {x c : Fin n → ℝ} {δ : ℝ} {i j : Fin n}
    (hx : x ∈ face_set (permutahedron n) c δ)
    (hswap : x ∘ Equiv.swap i j ∈ face_set (permutahedron n) c δ)
    (hijx : x i ≠ x j) :
    c i = c j := by
  have hx_eq : c ⬝ᵥ x = δ := (mem_face_set_iff.mp hx).2
  have hswap_eq : c ⬝ᵥ (x ∘ Equiv.swap i j) = δ := (mem_face_set_iff.mp hswap).2
  have hmul : (c i - c j) * (x j - x i) = 0 := by
    -- The shared face equation makes the swap-difference formula vanish.
    calc
      (c i - c j) * (x j - x i) = c ⬝ᵥ (x ∘ Equiv.swap i j) - c ⬝ᵥ x := by
        symm
        exact dotProduct_comp_swap_sub_eq c x i j
      _ = 0 := by simp [hswap_eq, hx_eq]
  have hxdiff : x j - x i ≠ 0 := sub_ne_zero.mpr hijx.symm
  have hcdiff : c i - c j = 0 := (mul_eq_zero.mp hmul).resolve_right hxdiff
  exact sub_eq_zero.mp hcdiff

/-- Helper for Example 3.29: swapping two indices on the same side of `K` keeps a tight
permutation vertex on the same subset-sum face. -/
lemma swap_mem_permutahedron_subset_sum_face_of_same_membership {n : ℕ}
    {K : Finset (Fin n)} {x : Fin n → ℝ} {i j : Fin n}
    (hx : x ∈ face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ)))
    (hx_vertices : x ∈ permutahedron_vertices n)
    (hmem : i ∈ K ↔ j ∈ K) :
    x ∘ Equiv.swap i j ∈ face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
  have hx_sum :
      ∑ t ∈ K, x t = (Nat.choose (K.card + 1) 2 : ℝ) :=
    (mem_permutahedron_subset_sum_face_iff.mp hx).2
  have hswap_perm :
      x ∘ Equiv.swap i j ∈ permutahedron n :=
    swap_vertex_mem_permutahedron_of_mem_vertices (i := i) (j := j) hx_vertices
  -- Same-side swaps preserve both ambient membership and the tight subset sum.
  rw [mem_permutahedron_subset_sum_face_iff]
  refine ⟨hswap_perm, ?_⟩
  calc
    ∑ t ∈ K, (x ∘ Equiv.swap i j) t = subsetSumIndicator K ⬝ᵥ (x ∘ Equiv.swap i j) := by
      symm
      exact dot_subsetSumIndicator_eq_sum K (x ∘ Equiv.swap i j)
    _ = subsetSumIndicator K ⬝ᵥ x := by
      exact dot_subsetSumIndicator_comp_swap_eq_of_same_membership K x i j hmem
    _ = ∑ t ∈ K, x t := dot_subsetSumIndicator_eq_sum K x
    _ = (Nat.choose (K.card + 1) 2 : ℝ) := hx_sum

/-- Helper for Example 3.29: any proper face containing the subset-sum face has coefficients that
are constant on `K` and on its complement. -/
lemma coefficients_constant_on_blocks_of_containing_face {n : ℕ} {K : Finset (Fin n)}
    {xbar c : Fin n → ℝ} {δ : ℝ} {i0 j0 : Fin n}
    (hxbarF : xbar ∈ face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ)))
    (hxbar_vertices : xbar ∈ permutahedron_vertices n)
    (hFG : face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ)) ⊆
        face_set (permutahedron n) c δ)
    (hK_distinct : ∀ ⦃i j : Fin n⦄, i ∈ K → j ∈ K → i ≠ j → xbar i ≠ xbar j)
    (hKc_distinct : ∀ ⦃i j : Fin n⦄, i ∉ K → j ∉ K → i ≠ j → xbar i ≠ xbar j)
    (hi0 : i0 ∈ K) (hj0 : j0 ∉ K) :
    c = fun i ↦ if i ∈ K then c i0 else c j0 := by
  have hxbarG : xbar ∈ face_set (permutahedron n) c δ := hFG hxbarF
  -- Compare `xbar` with same-block swaps to force equality of the corresponding coefficients.
  funext i
  by_cases hi : i ∈ K
  · by_cases hii0 : i = i0
    · subst hii0
      simp [hi0]
    · have hswapF :
          xbar ∘ Equiv.swap i i0 ∈ face_set (permutahedron n) (-subsetSumIndicator K)
            (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
        exact swap_mem_permutahedron_subset_sum_face_of_same_membership hxbarF hxbar_vertices
          (by simp [hi, hi0])
      have hswapG : xbar ∘ Equiv.swap i i0 ∈ face_set (permutahedron n) c δ := hFG hswapF
      have hci : c i = c i0 :=
        coefficient_eq_of_swap_in_face hxbarG hswapG (hK_distinct hi hi0 hii0)
      simpa [hi] using hci
  · by_cases hij0 : i = j0
    · subst hij0
      simp [hj0]
    · have hswapF :
          xbar ∘ Equiv.swap i j0 ∈ face_set (permutahedron n) (-subsetSumIndicator K)
            (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
        exact swap_mem_permutahedron_subset_sum_face_of_same_membership hxbarF hxbar_vertices
          (by simp [hi, hj0])
      have hswapG : xbar ∘ Equiv.swap i j0 ∈ face_set (permutahedron n) c δ := hFG hswapF
      have hci : c i = c j0 :=
        coefficient_eq_of_swap_in_face hxbarG hswapG (hKc_distinct hi hj0 hij0)
      simpa [hi] using hci

/-- Helper for Example 3.29: once a containing face has two blockwise coefficients with the
`K`-coefficient strictly smaller, its equality face is exactly the subset-sum face. -/
lemma face_set_eq_subset_sum_face_of_two_block_coefficients {n : ℕ} {K : Finset (Fin n)}
    {xbar c : Fin n → ℝ} {δ lam mu : ℝ}
    (hxbarF : xbar ∈ face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ)))
    (hxbarG : xbar ∈ face_set (permutahedron n) c δ)
    (hc : c = fun i ↦ if i ∈ K then lam else mu)
    (hlt : lam < mu) :
    face_set (permutahedron n) c δ =
      face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
  let triK : ℝ := (Nat.choose (K.card + 1) 2 : ℝ)
  let triN : ℝ := (Nat.choose (n + 1) 2 : ℝ)
  have hxbar_perm : xbar ∈ permutahedron n := (mem_face_set_iff.mp hxbarF).1
  have hxbar_sumK : ∑ i ∈ K, xbar i = triK := by
    simpa [triK] using (mem_permutahedron_subset_sum_face_iff.mp hxbarF).2
  have hxbar_sumAll : ∑ i, xbar i = triN := by
    simpa [triN] using permutahedron_subset_constant_sum_hyperplane n hxbar_perm
  have hδ : δ = mu * triN + (lam - mu) * triK := by
    -- Evaluate the two-block functional at the common tight witness `xbar`.
    calc
      δ = c ⬝ᵥ xbar := (mem_face_set_iff.mp hxbarG).2.symm
      _ = (fun i ↦ if i ∈ K then lam else mu) ⬝ᵥ xbar := by rw [hc]
      _ = mu * ∑ i, xbar i + (lam - mu) * ∑ i ∈ K, xbar i :=
            dot_two_block_coefficients_eq K lam mu xbar
      _ = mu * triN + (lam - mu) * triK := by rw [hxbar_sumAll, hxbar_sumK]
  ext x
  constructor
  · intro hx
    have hx_perm : x ∈ permutahedron n := (mem_face_set_iff.mp hx).1
    have hx_eq : c ⬝ᵥ x = δ := (mem_face_set_iff.mp hx).2
    have hx_sumAll : ∑ i, x i = triN := by
      simpa [triN] using permutahedron_subset_constant_sum_hyperplane n hx_perm
    have hx_formula : δ = mu * triN + (lam - mu) * ∑ i ∈ K, x i := by
      -- Rewrite the containing-face equation through the constant-sum hyperplane.
      calc
        δ = c ⬝ᵥ x := hx_eq.symm
        _ = (fun i ↦ if i ∈ K then lam else mu) ⬝ᵥ x := by rw [hc]
        _ = mu * ∑ i, x i + (lam - mu) * ∑ i ∈ K, x i :=
              dot_two_block_coefficients_eq K lam mu x
        _ = mu * triN + (lam - mu) * ∑ i ∈ K, x i := by rw [hx_sumAll]
    have hcore : (lam - mu) * (∑ i ∈ K, x i - triK) = 0 := by
      nlinarith [hx_formula, hδ]
    have hcoeff_ne : lam - mu ≠ 0 := sub_ne_zero.mpr (ne_of_lt hlt)
    have hx_sumK_sub : ∑ i ∈ K, x i - triK = 0 :=
      (mul_eq_zero.mp hcore).resolve_left hcoeff_ne
    have hx_sumK : ∑ i ∈ K, x i = triK := sub_eq_zero.mp hx_sumK_sub
    simpa [triK] using (mem_permutahedron_subset_sum_face_iff).2 ⟨hx_perm, hx_sumK⟩
  · intro hx
    have hx_perm : x ∈ permutahedron n := (mem_permutahedron_subset_sum_face_iff.mp hx).1
    have hx_sumK : ∑ i ∈ K, x i = triK := by
      simpa [triK] using (mem_permutahedron_subset_sum_face_iff.mp hx).2
    have hx_sumAll : ∑ i, x i = triN := by
      simpa [triN] using permutahedron_subset_constant_sum_hyperplane n hx_perm
    -- The subset-sum equality reproduces the containing-face equality after the two-block rewrite.
    rw [mem_face_set_iff]
    refine ⟨hx_perm, ?_⟩
    calc
      c ⬝ᵥ x = (fun i ↦ if i ∈ K then lam else mu) ⬝ᵥ x := by rw [hc]
      _ = mu * ∑ i, x i + (lam - mu) * ∑ i ∈ K, x i :=
            dot_two_block_coefficients_eq K lam mu x
      _ = mu * triN + (lam - mu) * triK := by rw [hx_sumAll, hx_sumK]
      _ = δ := hδ.symm

/-- Facet statement for Example 3.29 (2): if `K` is nonempty and proper, then the
subset-sum equality face is a
facet of the permutahedron `Π_n`. -/
theorem permutahedron_subset_sum_face_is_facet
    (n : ℕ) (K : Finset (Fin n)) (hK_nonempty : K.Nonempty) (hK_proper : K.card < n) :
    is_facet (permutahedron n)
      (face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ))) := by
  classical
  let F : Set (Fin n → ℝ) :=
    face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ))
  rcases exists_tight_permutahedron_vertex_with_block_order K hK_nonempty hK_proper with
    ⟨xbar, hxbarF0, hxbar_vertices, hK_distinct, hKc_distinct, hcross⟩
  have hxbarF : xbar ∈ F := by
    simpa [F] using hxbarF0
  obtain ⟨i0, hi0⟩ := hK_nonempty
  have hKc_card_pos : 0 < Kᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨j0, hj0_mem⟩ := Finset.card_pos.mp hKc_card_pos
  have hj0 : j0 ∉ K := by
    simpa using hj0_mem
  have hxswap_perm : xbar ∘ Equiv.swap i0 j0 ∈ permutahedron n :=
    swap_vertex_mem_permutahedron_of_mem_vertices (i := i0) (j := j0) hxbar_vertices
  have hxswap_notF : xbar ∘ Equiv.swap i0 j0 ∉ F := by
    intro hxswapF
    have hxbar_sum :
        ∑ i ∈ K, xbar i = (Nat.choose (K.card + 1) 2 : ℝ) :=
      (mem_permutahedron_subset_sum_face_iff.mp hxbarF0).2
    have hxswap_sum :
        ∑ i ∈ K, (xbar ∘ Equiv.swap i0 j0) i = (Nat.choose (K.card + 1) 2 : ℝ) := by
      simpa [F] using (mem_permutahedron_subset_sum_face_iff.mp (by simpa [F] using hxswapF)).2
    have hlt_sum :
        ∑ i ∈ K, xbar i < ∑ i ∈ K, (xbar ∘ Equiv.swap i0 j0) i := by
      -- Swapping a `K`-coordinate with a larger `Kᶜ`-coordinate strictly increases the `K`-sum.
      simpa [dot_subsetSumIndicator_eq_sum] using
        dot_subsetSumIndicator_lt_comp_swap_of_mem_not_mem K xbar i0 j0 hi0 hj0
          (hcross hi0 hj0)
    linarith
  have hF_subset : F ⊆ permutahedron n := by
    intro x hx
    have hx' :
        x ∈ face_set (permutahedron n) (-subsetSumIndicator K)
          (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
      simpa [F] using hx
    exact (mem_face_set_iff.mp hx').1
  have hF_proper : is_proper_face (permutahedron n) F := by
    rw [is_proper_face_iff]
    refine ⟨?_, ⟨xbar, hxbarF⟩, ?_⟩
    · -- The target face is exposed because its defining inequality is valid and attained at `xbar`.
      have hF_exposed :
          IsExposed ℝ (permutahedron n)
            (face_set (permutahedron n) (-subsetSumIndicator K)
              (-(Nat.choose (K.card + 1) 2 : ℝ))) := by
        rw [face_set_eq_toExposed_of_mem
          (permutahedron_subset_sum_is_valid_inequality n K) hxbarF0]
        exact ContinuousLinearMap.toExposed.isExposed
      simpa [F] using hF_exposed
    · refine ⟨hF_subset, ?_⟩
      intro hPF
      exact hxswap_notF (hPF hxswap_perm)
  rw [is_facet_iff]
  refine ⟨hF_proper, ?_⟩
  intro G hG hFG
  rcases (is_proper_face_iff.mp hG) with ⟨hG_exposed, hG_nonempty, hG_ss⟩
  rcases (isExposed_iff_eq_empty_or_eq_face_set.mp hG_exposed) with hG_empty | ⟨c, δ, hvalid, hG_eq⟩
  · obtain ⟨x, hx⟩ := hG_nonempty
    simp [hG_empty] at hx
  · have hFG_face :
        face_set (permutahedron n) (-subsetSumIndicator K)
          (-(Nat.choose (K.card + 1) 2 : ℝ)) ⊆
            face_set (permutahedron n) c δ := by
        intro x hx
        have hxG : x ∈ G := by
          exact hFG (by simpa [F] using hx)
        simpa [hG_eq] using hxG
    have hxbarG : xbar ∈ face_set (permutahedron n) c δ := hFG_face hxbarF0
    have hcblock : c = fun i ↦ if i ∈ K then c i0 else c j0 :=
      coefficients_constant_on_blocks_of_containing_face hxbarF0 hxbar_vertices hFG_face
        hK_distinct hKc_distinct hi0 hj0
    have hswap_le :
        (c i0 - c j0) * (xbar j0 - xbar i0) ≤ 0 := by
      -- Validity of the containing face inequality controls the cross-block swap.
      calc
        (c i0 - c j0) * (xbar j0 - xbar i0)
            = c ⬝ᵥ (xbar ∘ Equiv.swap i0 j0) - c ⬝ᵥ xbar := by
                symm
                exact dotProduct_comp_swap_sub_eq c xbar i0 j0
        _ ≤ 0 := by
          have hxbar_eq : c ⬝ᵥ xbar = δ := (mem_face_set_iff.mp hxbarG).2
          have hswap_valid : c ⬝ᵥ (xbar ∘ Equiv.swap i0 j0) ≤ δ :=
            hvalid hxswap_perm
          linarith
    have hcoeff_le : c i0 ≤ c j0 := by
      have hpos : 0 < xbar j0 - xbar i0 := sub_pos.mpr (hcross hi0 hj0)
      nlinarith
    have hcoeff_ne : c i0 ≠ c j0 := by
      intro hEq
      have hconst_dot :
          ∀ x : Fin n → ℝ, c ⬝ᵥ x = c j0 * ∑ i, x i := by
        intro x
        -- If the two block coefficients agree, the whole functional becomes constant-coefficient.
        have hcblock_dot :
            c ⬝ᵥ x = (fun i ↦ if i ∈ K then c i0 else c j0) ⬝ᵥ x :=
          congrArg (fun d : Fin n → ℝ ↦ d ⬝ᵥ x) hcblock
        calc
          c ⬝ᵥ x = (fun i ↦ if i ∈ K then c i0 else c j0) ⬝ᵥ x := hcblock_dot
          _ = c j0 * ∑ i, x i + (c i0 - c j0) * ∑ i ∈ K, x i :=
                dot_two_block_coefficients_eq K (c i0) (c j0) x
          _ = c j0 * ∑ i, x i := by rw [hEq, sub_self, zero_mul, add_zero]
      have hxbar_sumAll :
          ∑ i, xbar i = (Nat.choose (n + 1) 2 : ℝ) := by
        simpa using permutahedron_subset_constant_sum_hyperplane n (mem_face_set_iff.mp hxbarF0).1
      have hδ_const : δ = c j0 * (Nat.choose (n + 1) 2 : ℝ) := by
        -- The equality at `xbar` pins down the right-hand side of the containing face.
        calc
          δ = c ⬝ᵥ xbar := (mem_face_set_iff.mp hxbarG).2.symm
          _ = c j0 * ∑ i, xbar i := hconst_dot xbar
          _ = c j0 * (Nat.choose (n + 1) 2 : ℝ) := by rw [hxbar_sumAll]
      have hP_subset_G : permutahedron n ⊆ G := by
        intro x hxP
        have hx_sumAll :
            ∑ i, x i = (Nat.choose (n + 1) 2 : ℝ) := by
          simpa using permutahedron_subset_constant_sum_hyperplane n hxP
        have hx_eq : c ⬝ᵥ x = δ := by
          calc
            c ⬝ᵥ x = c j0 * ∑ i, x i := hconst_dot x
            _ = c j0 * (Nat.choose (n + 1) 2 : ℝ) := by rw [hx_sumAll]
            _ = δ := hδ_const.symm
        rw [hG_eq, mem_face_set_iff]
        exact ⟨hxP, hx_eq⟩
      exact hG_ss.2 hP_subset_G
    have hcoeff_lt : c i0 < c j0 := lt_of_le_of_ne hcoeff_le hcoeff_ne
    have hface_eq :
        face_set (permutahedron n) c δ =
          face_set (permutahedron n) (-subsetSumIndicator K)
            (-(Nat.choose (K.card + 1) 2 : ℝ)) :=
      face_set_eq_subset_sum_face_of_two_block_coefficients hxbarF0 hxbarG hcblock hcoeff_lt
    simpa [F] using hG_eq.trans hface_eq

/-- Facet-defining form of Example 3.29 (2): for nonempty proper `K`, the
subset-sum inequality is facet-defining for
the permutahedron `Π_n`. -/
theorem permutahedron_subset_sum_facet_defining_inequality
    (n : ℕ) (K : Finset (Fin n)) (hK_nonempty : K.Nonempty) (hK_proper : K.card < n) :
    facet_defining_inequality (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
  exact ⟨permutahedron_subset_sum_is_valid_inequality n K,
    permutahedron_subset_sum_face_is_facet n K hK_nonempty hK_proper⟩

/-- Helper for Example 3.29: the direction of the tight subset-sum face lies in the intersection
of the total-sum and `K`-sum kernels. -/
private lemma subsetSumFaceDirection_le_sumCoordsKer_inf_sumOnKKer
    (n : ℕ) (K : Finset (Fin n)) (hK_nonempty : K.Nonempty) (hK_proper : K.card < n) :
    let F :=
      face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ))
    let sumCoords : (Fin n → ℝ) →ₗ[ℝ] ℝ := (Pi.basisFun ℝ (Fin n)).sumCoords
    let sumOnK : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ K, LinearMap.proj i
    (affineSpan ℝ F).direction ≤ LinearMap.ker sumCoords ⊓ LinearMap.ker sumOnK := by
  classical
  let F : Set (Fin n → ℝ) :=
    face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ))
  let sumCoords : (Fin n → ℝ) →ₗ[ℝ] ℝ := (Pi.basisFun ℝ (Fin n)).sumCoords
  let sumOnK : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ K, LinearMap.proj i
  let D : Submodule ℝ (Fin n → ℝ) := LinearMap.ker sumCoords ⊓ LinearMap.ker sumOnK
  rcases exists_tight_permutahedron_vertex_with_block_order K hK_nonempty hK_proper with
    ⟨xbar, hxbarF0, -, -, -, -⟩
  have hxbarF : xbar ∈ F := by
    simpa [F] using hxbarF0
  let H : AffineSubspace ℝ (Fin n → ℝ) := AffineSubspace.mk' xbar D
  have hF_le_H : F ⊆ H := by
    intro x hx
    change x ∈ H
    rw [AffineSubspace.mem_mk', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]
    have hxF :
        x ∈ face_set (permutahedron n) (-subsetSumIndicator K)
          (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
      simpa [F] using hx
    have hx_perm : x ∈ permutahedron n := (mem_permutahedron_subset_sum_face_iff.mp hxF).1
    have hx_sumK :
        ∑ i ∈ K, x i = (Nat.choose (K.card + 1) 2 : ℝ) :=
      (mem_permutahedron_subset_sum_face_iff.mp hxF).2
    have hxbar_perm : xbar ∈ permutahedron n := (mem_permutahedron_subset_sum_face_iff.mp hxbarF0).1
    have hxbar_sumK :
        ∑ i ∈ K, xbar i = (Nat.choose (K.card + 1) 2 : ℝ) :=
      (mem_permutahedron_subset_sum_face_iff.mp hxbarF0).2
    have hx_sumCoords :
        sumCoords x = (Nat.choose (n + 1) 2 : ℝ) := by
      simpa [sumCoords] using permutahedron_subset_constant_sum_hyperplane n hx_perm
    have hxbar_sumCoords :
        sumCoords xbar = (Nat.choose (n + 1) 2 : ℝ) := by
      simpa [sumCoords] using permutahedron_subset_constant_sum_hyperplane n hxbar_perm
    have hx_sumOnK :
        sumOnK x = (Nat.choose (K.card + 1) 2 : ℝ) := by
      simpa [sumOnK] using hx_sumK
    have hxbar_sumOnK :
        sumOnK xbar = (Nat.choose (K.card + 1) 2 : ℝ) := by
      simpa [sumOnK] using hxbar_sumK
    constructor
    · -- Every point of the face has the same total coordinate sum as the chosen base point.
      rw [vsub_eq_sub, map_sub, hx_sumCoords, hxbar_sumCoords, sub_self]
    · -- The face equality also fixes the `K`-coordinate sum.
      rw [vsub_eq_sub, map_sub, hx_sumOnK, hxbar_sumOnK, sub_self]
  have h_aff_le : affineSpan ℝ F ≤ H := (affineSpan_le).2 hF_le_H
  -- Passing to directions turns the affine containment into the desired linear containment.
  simpa [F, sumCoords, sumOnK, D, H] using AffineSubspace.direction_le h_aff_le

/-- Helper for Example 3.29: swapping two coordinates in the same block of the ordered tight
vertex yields the corresponding basis-difference direction. -/
private lemma basisDifference_mem_subsetSumFaceDirection_of_same_block
    (n : ℕ) (K : Finset (Fin n)) (hK_nonempty : K.Nonempty) (hK_proper : K.card < n)
    {i j : Fin n} (hij : i ≠ j) (hmem : i ∈ K ↔ j ∈ K) :
    let F :=
      face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ))
    Pi.single i (1 : ℝ) - Pi.single j 1 ∈ (affineSpan ℝ F).direction := by
  classical
  let F : Set (Fin n → ℝ) :=
    face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ))
  rcases exists_tight_permutahedron_vertex_with_block_order K hK_nonempty hK_proper with
    ⟨xbar, hxbarF0, hxbar_vertices, hK_distinct, hKc_distinct, -⟩
  have hxbarF : xbar ∈ F := by
    simpa [F] using hxbarF0
  have hbase_mem : xbar ∈ affineSpan ℝ F := subset_affineSpan ℝ F hxbarF
  have hswapF :
      xbar ∘ Equiv.swap i j ∈ F := by
    simpa [F] using
      swap_mem_permutahedron_subset_sum_face_of_same_membership hxbarF0 hxbar_vertices hmem
  have hswap_mem :
      xbar ∘ Equiv.swap i j ∈ affineSpan ℝ F := subset_affineSpan ℝ F hswapF
  have hdiff :
      xbar ∘ Equiv.swap i j - xbar ∈ (affineSpan ℝ F).direction := by
    -- Differences of two affine-span points lie in the direction subspace.
    simpa using AffineSubspace.vsub_mem_direction hswap_mem hbase_mem
  have hswap :
      xbar ∘ Equiv.swap i j - xbar =
        (xbar j - xbar i) • (Pi.single i (1 : ℝ) - Pi.single j 1) := by
    -- Only the swapped coordinates contribute to the displacement.
    ext k
    by_cases hk_i : k = i
    · subst hk_i
      simp [Function.comp_apply, hij, Equiv.swap_apply_left]
    · by_cases hk_j : k = j
      · subst hk_j
        simp [Function.comp_apply, hij, Equiv.swap_apply_right]
      · simp [Function.comp_apply, hk_i, hk_j, Equiv.swap_apply_of_ne_of_ne]
  have hscalar_ne : xbar j - xbar i ≠ 0 := by
    have hcoord_ne : xbar j ≠ xbar i := by
      by_cases hi : i ∈ K
      · have hj : j ∈ K := hmem.mp hi
        exact (hK_distinct hi hj hij).symm
      · have hj : j ∉ K := fun hj ↦ hi (hmem.mpr hj)
        exact hKc_distinct hj hi hij.symm
    exact sub_ne_zero.mpr hcoord_ne
  have hscaled :=
    Submodule.smul_mem (affineSpan ℝ F).direction (xbar j - xbar i)⁻¹ hdiff
  rw [hswap] at hscaled
  -- Inverting the nonzero swap scalar isolates the basis difference itself.
  simpa [smul_smul, hscalar_ne] using hscaled

/-- Helper for Example 3.29: a vector with zero total sum and zero `K`-sum is a sum of
within-block basis differences based at anchors in `K` and `Kᶜ`. -/
private lemma eq_sum_sameBlockBasisDifferences_of_zero_sums
    {n : ℕ} (K : Finset (Fin n)) {i0 j0 : Fin n} (hi0 : i0 ∈ K) (hj0 : j0 ∉ K)
    {v : Fin n → ℝ} (hsumAll : ∑ i : Fin n, v i = 0) (hsumK : ∑ i ∈ K, v i = 0) :
    v =
      (∑ i ∈ K.erase i0, v i • (Pi.single i (1 : ℝ) - Pi.single i0 1)) +
      ∑ j ∈ Kᶜ.erase j0, v j • (Pi.single j (1 : ℝ) - Pi.single j0 1) := by
  classical
  have hsumK_split :
      ∑ i ∈ K, v i = v i0 + ∑ i ∈ K.erase i0, v i := by
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hi0, Finset.sdiff_singleton_eq_erase]
  have hvi0 :
      v i0 = -(∑ i ∈ K.erase i0, v i) := by
    linarith
  have hsumKc :
      ∑ j ∈ Kᶜ, v j = 0 := by
    have hsplitAll :
        ∑ i ∈ K, v i + ∑ j ∈ Kᶜ, v j = 0 := by
      calc
        ∑ i ∈ K, v i + ∑ j ∈ Kᶜ, v j = ∑ i, v i := by
          rw [Finset.sum_add_sum_compl]
        _ = 0 := hsumAll
    linarith
  have hj0_mem : j0 ∈ Kᶜ := by
    simpa [Finset.mem_compl] using hj0
  have hsumKc_split :
      ∑ j ∈ Kᶜ, v j = v j0 + ∑ j ∈ Kᶜ.erase j0, v j := by
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hj0_mem, Finset.sdiff_singleton_eq_erase]
  have hvj0 :
      v j0 = -(∑ j ∈ Kᶜ.erase j0, v j) := by
    linarith
  let basisDiff : Fin n → Fin n → Fin n → ℝ := fun a b ↦ Pi.single a (1 : ℝ) - Pi.single b 1
  let vK : Fin n → ℝ :=
    ∑ x ∈ K.erase i0, v x • basisDiff x i0
  let vKc : Fin n → ℝ :=
    ∑ x ∈ Kᶜ.erase j0, v x • basisDiff x j0
  have hvK_apply (k : Fin n) :
      vK k = (∑ x ∈ K.erase i0, v x • basisDiff x i0) k := by
    rfl
  have hvKc_apply (k : Fin n) :
      vKc k = (∑ x ∈ Kᶜ.erase j0, v x • basisDiff x j0) k := by
    rfl
  -- Compare coordinates after splitting into the `K` and `Kᶜ` anchored differences.
  change v = vK + vKc
  ext k
  have hi0_ne_j0 : i0 ≠ j0 := by
    intro hij0
    subst hij0
    exact hj0 hi0
  by_cases hkK : k ∈ K
  · by_cases hk0 : k = i0
    · subst k
      have hfirst :
          vK i0 = v i0 := by
        rw [hvK_apply i0, Finset.sum_apply]
        calc
          _ = ∑ x ∈ K.erase i0, -v x := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                have hx_ne : x ≠ i0 := (Finset.mem_erase.mp hx).1
                simp [Pi.smul_apply, basisDiff, hx_ne]
          _ = -(∑ x ∈ K.erase i0, v x) := by
                rw [← Finset.sum_neg_distrib]
          _ = v i0 := hvi0.symm
      have hsecond :
          vKc i0 = 0 := by
        rw [hvKc_apply i0, Finset.sum_apply]
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hx_notK : x ∉ K := Finset.mem_compl.mp (Finset.mem_erase.mp hx).2
        have hx_ne_i0 : x ≠ i0 := by
          intro hxi0
          exact hx_notK (hxi0 ▸ hi0)
        simp [Pi.smul_apply, basisDiff, hx_ne_i0, hi0_ne_j0]
      simp [Pi.add_apply, hfirst, hsecond]
    · have hk_mem : k ∈ K.erase i0 := by
        simp [hkK, hk0]
      have hk_ne_j0 : k ≠ j0 := by
        intro hkj0
        subst hkj0
        exact hj0 hkK
      have hfirst :
          vK k = v k := by
        rw [hvK_apply k, Finset.sum_apply]
        rw [Finset.sum_eq_single k]
        · simp [Pi.smul_apply, basisDiff, hk0]
        · intro x hx hx_ne_k
          simp [Pi.smul_apply, basisDiff, hx_ne_k, hk0]
        · intro hk_not_mem
          exact False.elim (hk_not_mem hk_mem)
      have hsecond :
          vKc k = 0 := by
        rw [hvKc_apply k, Finset.sum_apply]
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hx_notK : x ∉ K := Finset.mem_compl.mp (Finset.mem_erase.mp hx).2
        have hx_ne_k : x ≠ k := by
          intro hxk
          exact hx_notK (hxk ▸ hkK)
        simp [Pi.smul_apply, basisDiff, hx_ne_k, hk_ne_j0]
      simp [Pi.add_apply, hfirst, hsecond]
  · have hkKc : k ∈ Kᶜ := by
      simpa [Finset.mem_compl] using hkK
    by_cases hkj0 : k = j0
    · subst k
      have hk_ne_i0 : j0 ≠ i0 := by
        intro hji
        subst hji
        exact hj0 hi0
      have hfirst :
          vK j0 = 0 := by
        rw [hvK_apply j0, Finset.sum_apply]
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hxK : x ∈ K := (Finset.mem_erase.mp hx).2
        have hx_ne_j0 : x ≠ j0 := by
          intro hxj0
          exact hj0 (hxj0 ▸ hxK)
        simp [Pi.smul_apply, basisDiff, hx_ne_j0, hk_ne_i0]
      have hsecond :
          vKc j0 = v j0 := by
        rw [hvKc_apply j0, Finset.sum_apply]
        calc
          _ = ∑ x ∈ Kᶜ.erase j0, -v x := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                have hx_ne : x ≠ j0 := (Finset.mem_erase.mp hx).1
                simp [basisDiff, hx_ne]
          _ = -(∑ x ∈ Kᶜ.erase j0, v x) := by
                rw [← Finset.sum_neg_distrib]
          _ = v j0 := hvj0.symm
      simp [Pi.add_apply, hfirst, hsecond]
    · have hk_ne_i0 : k ≠ i0 := by
        intro hki0
        subst hki0
        exact hkK hi0
      have hk_mem : k ∈ Kᶜ.erase j0 := by
        simp [hkKc, hkj0]
      have hfirst :
          vK k = 0 := by
        rw [hvK_apply k, Finset.sum_apply]
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hxK : x ∈ K := (Finset.mem_erase.mp hx).2
        have hx_ne_k : x ≠ k := by
          intro hxk
          exact hkK (hxk ▸ hxK)
        simp [Pi.smul_apply, basisDiff, hx_ne_k, hk_ne_i0]
      have hsecond :
          vKc k = v k := by
        rw [hvKc_apply k, Finset.sum_apply]
        rw [Finset.sum_eq_single k]
        · simp [Pi.smul_apply, basisDiff, hkj0]
        · intro x hx hx_ne_k
          simp [Pi.smul_apply, basisDiff, hx_ne_k, hkj0]
        · intro hk_not_mem
          exact False.elim (hk_not_mem hk_mem)
      simp [Pi.add_apply, hfirst, hsecond]

/-- Helper for Example 3.29: the blockwise zero-sum subspace is contained in the direction of the
tight subset-sum face. -/
private lemma sumCoordsKer_inf_sumOnKKer_le_subsetSumFaceDirection
    (n : ℕ) (K : Finset (Fin n)) (hK_nonempty : K.Nonempty) (hK_proper : K.card < n) :
    let F :=
      face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ))
    let sumCoords : (Fin n → ℝ) →ₗ[ℝ] ℝ := (Pi.basisFun ℝ (Fin n)).sumCoords
    let sumOnK : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ K, LinearMap.proj i
    LinearMap.ker sumCoords ⊓ LinearMap.ker sumOnK ≤ (affineSpan ℝ F).direction := by
  classical
  let F : Set (Fin n → ℝ) :=
    face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ))
  let sumCoords : (Fin n → ℝ) →ₗ[ℝ] ℝ := (Pi.basisFun ℝ (Fin n)).sumCoords
  let sumOnK : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ K, LinearMap.proj i
  change LinearMap.ker sumCoords ⊓ LinearMap.ker sumOnK ≤ (affineSpan ℝ F).direction
  have hsameBlock :
      ∀ {i j : Fin n}, i ≠ j → (i ∈ K ↔ j ∈ K) →
        Pi.single i (1 : ℝ) - Pi.single j 1 ∈ (affineSpan ℝ F).direction := by
    intro i j hij hmem
    exact
      basisDifference_mem_subsetSumFaceDirection_of_same_block n K hK_nonempty hK_proper hij hmem
  obtain ⟨i0, hi0⟩ := hK_nonempty
  have hKc_card_pos : 0 < Kᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨j0, hj0_mem⟩ := Finset.card_pos.mp hKc_card_pos
  have hj0 : j0 ∉ K := by
    simpa using hj0_mem
  intro v hv
  have hsumAll : ∑ i : Fin n, v i = 0 := by
    simpa [LinearMap.mem_ker, sumCoords] using hv.1
  have hsumK : ∑ i ∈ K, v i = 0 := by
    simpa [LinearMap.mem_ker, sumOnK] using hv.2
  -- Rewrite `v` into the span of same-block basis differences and place each generator in the
  -- face direction via the swap argument.
  rw [eq_sum_sameBlockBasisDifferences_of_zero_sums K hi0 hj0 hsumAll hsumK]
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.sum_mem _ fun i hi ↦ ?_
    refine Submodule.smul_mem _ _ ?_
    exact hsameBlock (Finset.mem_erase.mp hi).1 (by simp [(Finset.mem_erase.mp hi).2, hi0])
  · refine Submodule.sum_mem _ fun j hj ↦ ?_
    refine Submodule.smul_mem _ _ ?_
    have hj_not_mem : j ∉ K := Finset.mem_compl.mp ((Finset.mem_erase.mp hj).2)
    exact hsameBlock (Finset.mem_erase.mp hj).1 (by simp [hj_not_mem, hj0])

/-- Helper for Example 3.29: if a linear functional takes the value `1` on some vector of a
submodule `D`, then the kernel cut `D ⊓ ker L` has codimension one inside `D`. -/
private theorem finrank_inf_ker_add_one_of_eval_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (D : Submodule ℝ E) (L : E →ₗ[ℝ] ℝ) {w : E}
    (hwD : w ∈ D) (hw : L w = 1) :
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
  have hne : L.domRestrict D ≠ 0 := by
    -- Evaluating the restricted map on the chosen witness rules out the zero map.
    intro hzero
    have hvalue := congrArg (fun f : D →ₗ[ℝ] ℝ ↦ f ⟨w, hwD⟩) hzero
    simp [LinearMap.domRestrict_apply, hw] at hvalue
  have hdim :
      Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 =
        Module.finrank ℝ ↥D := by
    simpa using Module.Dual.finrank_ker_add_one_of_ne_zero (f := L.domRestrict D) hne
  have hmap :
      (LinearMap.ker (L.domRestrict D)).map D.subtype = D ⊓ LinearMap.ker L := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  have hfin :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) =
        Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) := by
    -- The subtype embedding identifies the restricted kernel with the ambient kernel cut.
    rw [← hmap]
    exact
      (Submodule.finrank_map_subtype_eq (R := ℝ) (p := D)
        (q := LinearMap.ker (L.domRestrict D)))
  calc
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1
        = Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 := by
            rw [hfin]
    _ = Module.finrank ℝ ↥D := hdim

/-- Example 3.29 (2): the subset-sum equality face has affine-span
dimension `n - 2`. -/
theorem permutahedron_subset_sum_face_finrank_direction_affineSpan
    (n : ℕ) (K : Finset (Fin n)) (hK_nonempty : K.Nonempty) (hK_proper : K.card < n) :
    Module.finrank ℝ
      (affineSpan ℝ
        (face_set (permutahedron n) (-subsetSumIndicator K)
          (-(Nat.choose (K.card + 1) 2 : ℝ)))).direction = n - 2 := by
  classical
  let F : Set (Fin n → ℝ) :=
    face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ))
  let sumCoords : (Fin n → ℝ) →ₗ[ℝ] ℝ := (Pi.basisFun ℝ (Fin n)).sumCoords
  let sumOnK : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ K, LinearMap.proj i
  let D : Submodule ℝ (Fin n → ℝ) := LinearMap.ker sumCoords ⊓ LinearMap.ker sumOnK
  have hK_nonempty' : K.Nonempty := hK_nonempty
  obtain ⟨i0, hi0⟩ := hK_nonempty'
  have hK_nonempty'' : K.Nonempty := ⟨i0, hi0⟩
  have hKc_card_pos : 0 < Kᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨j0, hj0_mem⟩ := Finset.card_pos.mp hKc_card_pos
  have hj0 : j0 ∉ K := by
    simpa using hj0_mem
  have hdir_le :
      (affineSpan ℝ F).direction ≤ D := by
    simpa [F, sumCoords, sumOnK, D] using
      subsetSumFaceDirection_le_sumCoordsKer_inf_sumOnKKer n K hK_nonempty'' hK_proper
  have hD_le :
      D ≤ (affineSpan ℝ F).direction := by
    simpa [F, sumCoords, sumOnK, D] using
      sumCoordsKer_inf_sumOnKKer_le_subsetSumFaceDirection n K hK_nonempty'' hK_proper
  have hdir_eq : (affineSpan ℝ F).direction = D := le_antisymm hdir_le hD_le
  have hwD : Pi.single i0 (1 : ℝ) - Pi.single j0 1 ∈ LinearMap.ker sumCoords := by
    -- The anchor basis difference already has total sum zero.
    rw [LinearMap.mem_ker]
    simp [sumCoords]
  have hw_eval : sumOnK (Pi.single i0 (1 : ℝ) - Pi.single j0 1) = 1 := by
    -- On `K`, that same witness evaluates to `1`.
    simp [sumOnK, hi0, hj0]
  have hD_add_one :
      Module.finrank ℝ D + 1 = Module.finrank ℝ (LinearMap.ker sumCoords) := by
    simpa [D] using
      finrank_inf_ker_add_one_of_eval_one (D := LinearMap.ker sumCoords) (L := sumOnK) hwD hw_eval
  have hker_dim :
      Module.finrank ℝ (LinearMap.ker sumCoords) = n - 1 := by
    -- The total-sum kernel is exactly the permutahedron direction from Example 3.20.
    rw [← permutahedron_direction_eq_sumCoords_ker n]
    exact permutahedron_finrank_direction_affineSpan n
  have hn_two : 2 ≤ n := by
    have hK_pos : 0 < K.card := Finset.card_pos.mpr hK_nonempty''
    omega
  have hD_dim : Module.finrank ℝ D = n - 2 := by
    rw [hker_dim] at hD_add_one
    omega
  -- Route correction: close the dimension computation through the identified kernel
  -- intersection, rather than rebuilding a polyhedral representation of `permutahedron n`.
  rw [hdir_eq]
  exact hD_dim
