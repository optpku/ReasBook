/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_10
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_24
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_46

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace (toDualMap)
open scoped BigOperators Pointwise
open WithLp (ofLp)

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Example 6.50 is `source-facing`: the textbook object is the sum of the `k` largest coordinates
of a vector in `ℝ^n`, and the prox formula is stated through the projection onto the capped-simplex
set `C = {y | eᵀ y = k, 0 ≤ y ≤ e}`. Domain sampling against the Chapter 1 owners
`coordinateHyperplane` and `Box[ℓ,u]`, and the Chapter 6 owners `support_function`, `prox[...]`,
and `metricProjection`, shows that the primitive data here are:

- the source-facing capped-simplex owner set itself,
- the function `sum_of_k_largest_values`.

The hyperplane/box realization is only a `bridge/view` to the upstream canonical constraint-set
API, so the public theorem surface should be centered on the named capped-simplex owner rather
than on a repeated raw preimage expression. -/

variable (ι)

/-- The capped-simplex constraint set from Example 6.50:
`{y | ∑ i, y i = k, 0 ≤ y i ≤ 1}`. -/
def sum_of_k_largest_constraint_set (k : ℕ) : Set E :=
  {y | (∑ i, y i) = k ∧ ∀ i : ι, 0 ≤ y i ∧ y i ≤ 1}

/-- A vector belongs to the capped simplex exactly when its coordinates sum to `k` and each
coordinate lies in the interval `[0, 1]`. -/
@[simp] theorem mem_sum_of_k_largest_constraint_set_iff {k : ℕ} {y : E} :
    y ∈ sum_of_k_largest_constraint_set ι k ↔
      (∑ i, y i) = k ∧ ∀ i : ι, 0 ≤ y i ∧ y i ≤ 1 :=
  Iff.rfl

-- Proof sketch: the hyperplane equation `dotProduct 1 y = k` is the coordinate-sum equation
-- `∑ i, y i = k`, and the box membership condition is exactly the pair of inequalities
-- `0 ≤ y i ≤ 1`.
/-- The capped-simplex owner agrees with the Chapter 1 hyperplane/box realization transported
through `ofLp`. -/
theorem sum_of_k_largest_constraint_set_eq_preimage_coordinateHyperplane_inter_box (k : ℕ) :
    sum_of_k_largest_constraint_set ι k =
      (ofLp ⁻¹'
        (coordinateHyperplane (1 : ι → ℝ) k ∩
          Box[(0 : ι → EReal), (1 : ι → EReal)]) : Set E) := by
  ext y
  -- Unfold the hyperplane and box views and compare them with the source-facing constraints.
  constructor
  · intro hy
    rcases hy with ⟨hsum, hbox⟩
    constructor
    · simpa [mem_coordinateHyperplane_iff, dotProduct] using hsum
    · intro i
      rcases hbox i with ⟨h0, h1⟩
      constructor
      · simpa using h0
      · change ((y i : ℝ) : EReal) ≤ (1 : EReal)
        exact_mod_cast h1
  · intro hy
    rcases hy with ⟨hhyper, hbox⟩
    constructor
    · simpa [mem_coordinateHyperplane_iff, dotProduct] using hhyper
    · intro i
      rcases hbox i with ⟨h0, h1⟩
      have h1' : ((y i : ℝ) : EReal) ≤ (1 : EReal) := by
        simpa using h1
      constructor
      · simpa using h0
      · change y i ≤ (1 : ℝ)
        exact EReal.coe_le_coe_iff.mp h1'

-- Proof sketch: choose a subset of `ι` with cardinality `k` and take its indicator vector. The
-- hypothesis `k ≤ Fintype.card ι` guarantees such a subset exists, and its indicator vector lies
-- in the capped simplex.
/-- The capped simplex is nonempty whenever `k ≤ Fintype.card ι`. -/
theorem sum_of_k_largest_constraint_set_nonempty {k : ℕ} (hk : k ≤ Fintype.card ι) :
    (sum_of_k_largest_constraint_set ι k).Nonempty := by
  classical
  obtain ⟨S, hS⟩ :
      (Finset.univ.powersetCard k).Nonempty := Finset.powersetCard_nonempty.2 hk
  refine ⟨WithLp.toLp 2 (fun i ↦ if i ∈ S then (1 : ℝ) else 0), ?_⟩
  have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
  -- The indicator of a `k`-element subset is a feasible `0/1` point of the capped simplex.
  constructor
  · simp [hScard]
  · intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi]

-- Proof sketch: the sum condition defines an affine hyperplane, and each coordinate constraint
-- `0 ≤ y i` and `y i ≤ 1` is closed. Their finite intersection is therefore closed.
/-- The capped simplex is closed. -/
theorem sum_of_k_largest_constraint_set_closed (k : ℕ) :
    IsClosed (sum_of_k_largest_constraint_set ι k) := by
  have hcoord : ∀ i : ι, Continuous fun y : E ↦ y i := by
    intro i
    -- Coordinate evaluation is continuous after transporting through `ofLp`.
    simpa using
      (continuous_apply i).comp
        (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : ι ↦ ℝ))
  have hsumClosed : IsClosed ({y : E | (∑ i, y i) = k} : Set E) := by
    have hsum : Continuous (fun y : E ↦ ∑ i, y i) := by
      refine continuous_finset_sum Finset.univ ?_
      intro i hi
      exact hcoord i
    exact isClosed_eq hsum continuous_const
  have hnonnegClosed : IsClosed ({y : E | ∀ i : ι, 0 ≤ y i} : Set E) := by
    have hset :
        ({y : E | ∀ i : ι, 0 ≤ y i} : Set E) =
          ⋂ i : ι, {y : E | 0 ≤ y i} := by
      ext y
      simp
    rw [hset]
    exact isClosed_iInter fun i ↦ isClosed_le continuous_const (hcoord i)
  have honeClosed : IsClosed ({y : E | ∀ i : ι, y i ≤ 1} : Set E) := by
    have hset :
        ({y : E | ∀ i : ι, y i ≤ 1} : Set E) =
          ⋂ i : ι, {y : E | y i ≤ 1} := by
      ext y
      simp
    rw [hset]
    exact isClosed_iInter fun i ↦ isClosed_le (hcoord i) continuous_const
  have hboxClosed : IsClosed ({y : E | ∀ i : ι, 0 ≤ y i ∧ y i ≤ 1} : Set E) := by
    have hset :
        ({y : E | ∀ i : ι, 0 ≤ y i ∧ y i ≤ 1} : Set E) =
          {y : E | ∀ i : ι, 0 ≤ y i} ∩ {y : E | ∀ i : ι, y i ≤ 1} := by
      ext y
      simp [forall_and]
    rw [hset]
    exact hnonnegClosed.inter honeClosed
  have hset :
      sum_of_k_largest_constraint_set ι k =
        ({y : E | (∑ i, y i) = k} : Set E) ∩
          {y : E | ∀ i : ι, 0 ≤ y i ∧ y i ≤ 1} := by
    ext y
    simp [sum_of_k_largest_constraint_set]
  -- Closedness is the intersection of the closed sum constraint and the closed box constraint.
  rw [hset]
  exact hsumClosed.inter hboxClosed

-- Proof sketch: the equality `∑ i, y i = k` defines an affine subspace, while the coordinate
-- intervals `[0, 1]` are convex. Intersecting these convex constraints yields a convex set.
/-- The capped simplex is convex. -/
theorem sum_of_k_largest_constraint_set_convex (k : ℕ) :
    Convex ℝ (sum_of_k_largest_constraint_set ι k) := by
  -- The sum constraint is affine, and the coordinate bounds are preserved by convex combination.
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxsum, hxbox⟩
  rcases hy with ⟨hysum, hybox⟩
  have hsumx : (∑ i, a * x i) = a * ∑ i, x i := by
    simpa using (Finset.mul_sum Finset.univ (fun i ↦ x i) a).symm
  have hsumy : (∑ i, b * y i) = b * ∑ i, y i := by
    simpa using (Finset.mul_sum Finset.univ (fun i ↦ y i) b).symm
  constructor
  · change ∑ i, (a * x i + b * y i) = (k : ℝ)
    rw [Finset.sum_add_distrib]
    rw [hsumx, hsumy, hxsum, hysum]
    nlinarith
  · intro i
    constructor
    · have hx0 : 0 ≤ x i := (hxbox i).1
      have hy0 : 0 ≤ y i := (hybox i).1
      change 0 ≤ a * x i + b * y i
      nlinarith
    · have hx1 : x i ≤ 1 := (hxbox i).2
      have hy1 : y i ≤ 1 := (hybox i).2
      change a * x i + b * y i ≤ 1
      nlinarith

variable {ι}

/-- The coordinates of `x`, enumerated through the canonical finite-index equivalence
`Fintype.equivFin ι`. This is an internal presentation device for the sorted-list formula and does
not add new mathematical structure. -/
private def coordinateList (x : E) : List ℝ :=
  List.ofFn fun i : Fin (Fintype.card ι) ↦ x ((Fintype.equivFin ι).symm i)

/-- The function `x ↦ x_[1] + ··· + x_[k]`, realized as the sum of the first `k` entries of the
decreasing rearrangement of the coordinates of `x`. The sorted-list realization stays internal to
this file through `coordinateList`; the public API is the function itself together with the
support-function and proximal formulas below. -/
def sum_of_k_largest_values (k : ℕ) (x : E) : ℝ :=
  (((coordinateList x).mergeSort (· ≥ ·)).take k).sum

/-- Helper for Example 6.50: sort the coordinate/value pairs by descending value, breaking ties by
the original coordinate order through `zipIdx`. -/
private def ranked_coordinate_pairs (x : E) : List (ℝ × ℕ) :=
  (coordinateList x).zipIdx.mergeSort (List.zipIdxLE fun a b : ℝ ↦ decide (a ≥ b))

/-- Helper for Example 6.50: the ranked coordinate/value list has one entry for each coordinate. -/
private theorem ranked_coordinate_pairs_length (x : E) :
    (ranked_coordinate_pairs x).length = Fintype.card ι := by
  -- The sorted pair list is a permutation of the `zipIdx` list, so its length is unchanged.
  simp [ranked_coordinate_pairs, coordinateList]

/-- Helper for Example 6.50: the value projection of the ranked pair list is exactly the decreasing
rearrangement used in `sum_of_k_largest_values`. -/
private theorem ranked_coordinate_pairs_map_fst (x : E) :
    (ranked_coordinate_pairs x).map Prod.fst =
      (coordinateList x).mergeSort (fun a b : ℝ ↦ decide (a ≥ b)) := by
  -- Stable sorting of `zipIdx` preserves the value projection.
  simpa [ranked_coordinate_pairs] using
    (List.mergeSort_zipIdx (le := fun a b : ℝ ↦ decide (a ≥ b)) (l := coordinateList x))

/-- Helper for Example 6.50: the ranked index list has no repetitions. -/
private theorem ranked_coordinate_pairs_indices_nodup (x : E) :
    ((ranked_coordinate_pairs x).map Prod.snd).Nodup := by
  -- Sorting only permutes the `zipIdx` list, whose indices are already pairwise distinct.
  have hperm :
      ((ranked_coordinate_pairs x).map Prod.snd).Perm (((coordinateList x).zipIdx.map Prod.snd)) := by
    simpa [ranked_coordinate_pairs] using
      (List.mergeSort_perm ((coordinateList x).zipIdx)
        (List.zipIdxLE fun a b : ℝ ↦ decide (a ≥ b))).map Prod.snd
  rw [List.zipIdx_map_snd] at hperm
  exact hperm.nodup_iff.2 (List.nodup_range')

/-- Helper for Example 6.50: every ranked pair index lies in the canonical range
`0, …, card ι - 1`. -/
private theorem ranked_coordinate_pairs_pos_lt (x : E) (i : Fin (Fintype.card ι)) :
    i.1 < (ranked_coordinate_pairs x).length := by
  -- The ranked pair list has exactly one position for each coordinate.
  simpa [ranked_coordinate_pairs_length] using i.2

/-- Helper for Example 6.50: reinterpret a rank position as an index into the ranked pair list. -/
private def ranked_coordinate_pairs_pos (x : E) (i : Fin (Fintype.card ι)) :
    Fin (ranked_coordinate_pairs x).length :=
  ⟨i.1, ranked_coordinate_pairs_pos_lt x i⟩

/-- Helper for Example 6.50: the same rank position also indexes the projected index list. -/
private theorem ranked_coordinate_pairs_snd_pos_lt (x : E) (i : Fin (Fintype.card ι)) :
    i.1 < ((ranked_coordinate_pairs x).map Prod.snd).length := by
  -- Mapping `Prod.snd` preserves the ranked list length.
  simpa using ranked_coordinate_pairs_pos_lt x i

/-- Helper for Example 6.50: reinterpret a rank position as an index into the projected index
list. -/
private def ranked_coordinate_pairs_snd_pos (x : E) (i : Fin (Fintype.card ι)) :
    Fin ((ranked_coordinate_pairs x).map Prod.snd).length :=
  ⟨i.1, ranked_coordinate_pairs_snd_pos_lt x i⟩

/-- Helper for Example 6.50: every ranked pair index lies in the canonical range
`0, …, card ι - 1`. -/
private theorem ranked_coordinate_pairs_index_lt (x : E) (i : Fin (Fintype.card ι)) :
    ((ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x i)).2 < Fintype.card ι := by
  -- Each sorted pair still comes from the original `zipIdx` list.
  have hmem :
      (ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x i) ∈ ranked_coordinate_pairs x :=
    List.get_mem _ _
  have hmem' :
      (ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x i) ∈ (coordinateList x).zipIdx := by
    simpa [ranked_coordinate_pairs] using ((List.mem_mergeSort).1 hmem)
  simpa [coordinateList] using (List.mem_zipIdx hmem').2.1

/-- Helper for Example 6.50: the ranked pair list determines a permutation of the coordinate
indices, read in descending-value order. -/
private def ranked_coordinate_perm (x : E) (i : Fin (Fintype.card ι)) : Fin (Fintype.card ι) :=
  ⟨((ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x i)).2,
    ranked_coordinate_pairs_index_lt x i⟩

/-- Helper for Example 6.50: the ranked index map is injective, so it is a genuine permutation of
the coordinate set. -/
private theorem ranked_coordinate_perm_injective (x : E) :
    Function.Injective (ranked_coordinate_perm x) := by
  -- Distinct ranks carry distinct original indices because the `zipIdx` indices are nodup.
  intro i j hij
  have hnodup : ((ranked_coordinate_pairs x).map Prod.snd).Nodup :=
    ranked_coordinate_pairs_indices_nodup x
  have hget :
      ((ranked_coordinate_pairs x).map Prod.snd).get (ranked_coordinate_pairs_snd_pos x i) =
        ((ranked_coordinate_pairs x).map Prod.snd).get (ranked_coordinate_pairs_snd_pos x j) := by
    simpa [ranked_coordinate_perm, ranked_coordinate_pairs_pos, List.get_eq_getElem] using hij
  have hij' : ranked_coordinate_pairs_snd_pos x i = ranked_coordinate_pairs_snd_pos x j :=
    hnodup.get_inj_iff.mp hget
  have hval : (i : ℕ) = j := by
    simpa [ranked_coordinate_pairs_snd_pos] using congrArg Fin.val hij'
  exact Fin.ext hval

/-- Helper for Example 6.50: evaluating `x` along the ranked permutation recovers the sorted
coordinate value stored in the ranked pair list. -/
private theorem coordinate_at_ranked_coordinate_perm_eq_ranked_value
    (x : E) (i : Fin (Fintype.card ι)) :
    x ((Fintype.equivFin ι).symm (ranked_coordinate_perm x i)) =
      ((ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x i)).1 := by
  -- Each ranked pair still comes from `coordinateList x`, so its index component points back to
  -- the original coordinate whose value is stored in the first component.
  dsimp [ranked_coordinate_perm]
  have hmem :
      (ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x i) ∈ ranked_coordinate_pairs x :=
    List.get_mem _ _
  have hmem' :
      (ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x i) ∈ (coordinateList x).zipIdx := by
    simpa [ranked_coordinate_pairs] using ((List.mem_mergeSort).1 hmem)
  have hidx :
      ((ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x i)).2 <
        (coordinateList x).length := by
    simpa [coordinateList] using ranked_coordinate_pairs_index_lt x i
  have hpair :
      ((ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x i)).1 =
        (coordinateList x)[((ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x i)).2] := by
    simpa [hidx] using (List.mem_zipIdx hmem').2.2
  simpa [coordinateList] using hpair.symm

/-- Helper for Example 6.50: the sum of the first `k` ranked values is exactly the
`mergeSort`-based definition of `sum_of_k_largest_values`. -/
private theorem sum_of_k_largest_values_eq_sum_ranked_prefix (k : ℕ) (x : E) :
    sum_of_k_largest_values k x = (((ranked_coordinate_pairs x).take k).map Prod.fst).sum := by
  -- Rewrite the sorted-value definition through the stable ranked pair list.
  unfold sum_of_k_largest_values
  rw [← ranked_coordinate_pairs_map_fst (x := x), ← List.map_take]

/-- Helper for Example 6.50: reindexing the Euclidean pairing by the ranked permutation rewrites
it as a sum against the ranked coordinate values. -/
private theorem inner_eq_sum_ranked_coordinates (x y : E) :
    ((toDualMap ℝ E x) y : ℝ) =
      ∑ j : Fin (Fintype.card ι),
        ((ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x j)).1 *
          y ((Fintype.equivFin ι).symm (ranked_coordinate_perm x j)) := by
  -- First expand the inner product in canonical coordinates.
  calc
    ((toDualMap ℝ E x) y : ℝ) = ∑ i : ι, x i * y i := by
      simpa [InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
        (EuclideanSpace.inner_toLp_toLp x.ofLp y.ofLp)
    _ = ∑ j : Fin (Fintype.card ι),
          x ((Fintype.equivFin ι).symm j) * y ((Fintype.equivFin ι).symm j) := by
        exact
          Fintype.sum_equiv (Fintype.equivFin ι)
            (fun i : ι ↦ x i * y i)
            (fun j : Fin (Fintype.card ι) ↦
              x ((Fintype.equivFin ι).symm j) * y ((Fintype.equivFin ι).symm j))
            (fun i ↦ by simp)
    -- Then reorder the sum by the ranked permutation.
    _ = ∑ i : Fin (Fintype.card ι),
          x ((Fintype.equivFin ι).symm (ranked_coordinate_perm x i)) *
            y ((Fintype.equivFin ι).symm (ranked_coordinate_perm x i)) := by
          let f : Fin (Fintype.card ι) → Fin (Fintype.card ι) := ranked_coordinate_perm x
          have hf : Function.Bijective f :=
            (Finite.injective_iff_bijective).mp (ranked_coordinate_perm_injective x)
          exact (Fintype.sum_bijective f hf _ _ fun i ↦ rfl).symm
    -- Finally replace the permuted coordinate values by the ranked pair data.
    _ = ∑ j : Fin (Fintype.card ι),
          ((ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x j)).1 *
            y ((Fintype.equivFin ι).symm (ranked_coordinate_perm x j)) := by
          refine Fintype.sum_congr _ _ ?_
          intro j
          rw [coordinate_at_ranked_coordinate_perm_eq_ranked_value (x := x) (i := j)]

/-- Helper for Example 6.50: the `j`th ranked value is the first component of the `j`th ranked
coordinate pair. -/
private def ranked_value (x : E) (j : Fin (Fintype.card ι)) : ℝ :=
  ((ranked_coordinate_pairs x).get (ranked_coordinate_pairs_pos x j)).1

/-- Helper for Example 6.50: enumerating `ranked_value x` by `List.ofFn` recovers the value
projection of the ranked coordinate pair list. -/
private theorem ofFn_ranked_value (x : E) :
    List.ofFn (ranked_value x) = (ranked_coordinate_pairs x).map Prod.fst := by
  -- Both lists have the same length, and the `j`th entries agree by construction.
  refine List.ext_get ?_ ?_
  · simp [ranked_coordinate_pairs_length]
  · intro j hj₁ hj₂
    simp [ranked_value, ranked_coordinate_pairs_pos]

/-- Helper for Example 6.50: the ranked-value function is antitone in the rank index. -/
private theorem ranked_value_antitone (x : E) : Antitone (ranked_value x) := by
  have hsorted : ((ranked_coordinate_pairs x).map Prod.fst).SortedGE := by
    -- The value projection is exactly the decreasing merge-sort already used in the definition.
    rw [ranked_coordinate_pairs_map_fst]
    simpa using ((coordinateList x).sortedGE_mergeSort)
  -- Convert the sorted list statement back to the `Fin`-indexed ranked-value function.
  rw [← List.sortedGE_ofFn_iff]
  simpa [ofFn_ranked_value] using hsorted

/-- Helper for Example 6.50: the ranked-prefix sum can be written as a `Fin`-indexed indicator
sum. -/
private theorem sum_take_ranked_values_eq_prefix_indicator (k : ℕ) (x : E) :
    (((ranked_coordinate_pairs x).take k).map Prod.fst).sum =
      ∑ j : Fin (Fintype.card ι), if (j : ℕ) < k then ranked_value x j else 0 := by
  -- Rewrite the ranked-value list as `List.ofFn`, then use the standard prefix-sum identity.
  rw [List.map_take, ← ofFn_ranked_value]
  rw [List.sum_take_ofFn]
  exact Finset.sum_filter (fun j : Fin (Fintype.card ι) ↦ (j : ℕ) < k) (ranked_value x)

/-- Helper for Example 6.50: the ranked coordinate map is a genuine permutation of
`Fin (Fintype.card ι)`. -/
private noncomputable def ranked_coordinate_equiv (x : E) :
    Fin (Fintype.card ι) ≃ Fin (Fintype.card ι) :=
  Equiv.ofBijective (ranked_coordinate_perm x)
    ((Finite.injective_iff_bijective).mp (ranked_coordinate_perm_injective x))

/-- Helper for Example 6.50: the top-`k` ranked indicator is the `0/1` vector supported on the
first `k` coordinates in ranked order. -/
private def top_ranked_indicator (x : E) (k : ℕ) : E :=
  WithLp.toLp 2 fun i ↦
    if (((ranked_coordinate_equiv x).symm (Fintype.equivFin ι i) :
          Fin (Fintype.card ι)) : ℕ) < k then (1 : ℝ) else 0

/-- Helper for Example 6.50: the top-`k` ranked indicator has coordinate sum `k`. -/
private theorem top_ranked_indicator_sum (x : E) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    ∑ i : ι, top_ranked_indicator x k i = k := by
  -- Reindex first by the canonical `equivFin`, then by the inverse ranked permutation.
  calc
    ∑ i : ι, top_ranked_indicator x k i
        = ∑ j : Fin (Fintype.card ι),
            if (((ranked_coordinate_equiv x).symm j :
                  Fin (Fintype.card ι)) : ℕ) < k then (1 : ℝ) else 0 := by
            exact
              Fintype.sum_equiv (Fintype.equivFin ι)
                (fun i : ι ↦ top_ranked_indicator x k i)
                (fun j : Fin (Fintype.card ι) ↦
                  if (((ranked_coordinate_equiv x).symm j :
                        Fin (Fintype.card ι)) : ℕ) < k then (1 : ℝ) else 0)
                (fun i ↦ by simp [top_ranked_indicator])
    _ = ∑ j : Fin (Fintype.card ι), if (j : ℕ) < k then (1 : ℝ) else 0 := by
          exact
            Fintype.sum_equiv (ranked_coordinate_equiv x).symm
              (fun j : Fin (Fintype.card ι) ↦
                if (((ranked_coordinate_equiv x).symm j :
                      Fin (Fintype.card ι)) : ℕ) < k then (1 : ℝ) else 0)
              (fun j : Fin (Fintype.card ι) ↦ if (j : ℕ) < k then (1 : ℝ) else 0)
              (fun j ↦ by simp)
    _ = k := by
          have hcard :
              (Finset.univ.filter fun j : Fin (Fintype.card ι) => (j : ℕ) < k).card = k := by
            simpa [min_eq_right hk] using
              (Fin.card_filter_val_lt (n := Fintype.card ι) (m := k))
          simp [hcard]

/-- Helper for Example 6.50: the top-`k` ranked indicator belongs to the capped-simplex
constraint set. -/
private theorem top_ranked_indicator_mem_constraint_set (x : E) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    top_ranked_indicator x k ∈ sum_of_k_largest_constraint_set ι k := by
  constructor
  · -- The indicator has exactly `k` ones after reindexing by the ranked permutation.
    exact top_ranked_indicator_sum x hk
  · -- Each coordinate is either `0` or `1`, so it satisfies the box constraints.
    intro i
    by_cases hi :
        (((ranked_coordinate_equiv x).symm (Fintype.equivFin ι i) :
            Fin (Fintype.card ι)) : ℕ) < k
    · simp [top_ranked_indicator, hi]
    · simp [top_ranked_indicator, hi]

/-- Helper for Example 6.50: evaluating the top-`k` ranked indicator at a ranked coordinate
returns the prefix indicator `1_{j < k}`. -/
private theorem top_ranked_indicator_value_at_rank (x : E) (k : ℕ)
    (j : Fin (Fintype.card ι)) :
    top_ranked_indicator x k ((Fintype.equivFin ι).symm (ranked_coordinate_perm x j)) =
      if (j : ℕ) < k then (1 : ℝ) else 0 := by
  -- The ranked permutation cancels with its inverse inside the indicator definition.
  simp [top_ranked_indicator, ranked_coordinate_equiv]

/-- Helper for Example 6.50: the top-`k` ranked indicator attains the sum of the `k` largest
values. -/
private theorem top_ranked_indicator_attains_sum_of_k_largest_values
    {k : ℕ} (x : E) :
    ((toDualMap ℝ E x) (top_ranked_indicator x k) : ℝ) = sum_of_k_largest_values k x := by
  -- Reindex the pairing by the ranked permutation and collapse the resulting indicator sum.
  calc
    ((toDualMap ℝ E x) (top_ranked_indicator x k) : ℝ)
        = ∑ j : Fin (Fintype.card ι),
            ranked_value x j * (if (j : ℕ) < k then (1 : ℝ) else 0) := by
            rw [inner_eq_sum_ranked_coordinates]
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [top_ranked_indicator_value_at_rank]
            simp [ranked_value]
    _ = ∑ j : Fin (Fintype.card ι), if (j : ℕ) < k then ranked_value x j else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j _
          by_cases hj : (j : ℕ) < k
          · simp [hj]
          · simp [hj]
    _ = (((ranked_coordinate_pairs x).take k).map Prod.fst).sum := by
          symm
          exact sum_take_ranked_values_eq_prefix_indicator k x
    _ = sum_of_k_largest_values k x := by
          symm
          exact sum_of_k_largest_values_eq_sum_ranked_prefix k x

/-- Helper for Example 6.50: for a descending sequence `a`, any boxed weights summing to `k`
produce a weighted sum bounded above by the first `k` entries of `a`. -/
private theorem sum_mul_le_ranked_prefix_of_boxed_weights
    {n k : ℕ} (hk0 : 0 < k) (hk : k ≤ n) (a b : Fin n → ℝ)
    (ha : Antitone a) (hb0 : ∀ j, 0 ≤ b j) (hb1 : ∀ j, b j ≤ 1)
    (hsum : ∑ j : Fin n, b j = k) :
    (∑ j : Fin n, a j * b j) ≤ ∑ j : Fin n, if (j : ℕ) < k then a j else 0 := by
  let i0 : Fin n :=
    ⟨k - 1, lt_of_lt_of_le (Nat.sub_lt (Nat.zero_lt_of_lt hk0) zero_lt_one) hk⟩
  let t : ℝ := a i0
  let s : Finset (Fin n) := Finset.univ.filter fun j : Fin n => (j : ℕ) < k
  let s' : Finset (Fin n) := Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < k
  have hsplit_left :
      (∑ j : Fin n, a j * b j) = (∑ j : Fin n, (a j - t) * b j) + t * k := by
    -- Shift the sequence by the threshold value `t = a_(k-1)` so that the prefix is nonnegative
    -- and the tail is nonpositive.
    calc
      (∑ j : Fin n, a j * b j)
          = ∑ j : Fin n, ((a j - t) * b j + t * b j) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = (∑ j : Fin n, (a j - t) * b j) + ∑ j : Fin n, t * b j := by
            rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin n, (a j - t) * b j) + t * ∑ j : Fin n, b j := by
            rw [← Finset.mul_sum]
      _ = (∑ j : Fin n, (a j - t) * b j) + t * k := by
            rw [hsum]
  have hprefix_decomp :
      s.sum a = s.sum (fun j ↦ a j - t) + t * k := by
    -- The same shift rewrites the prefix sum as the shifted prefix plus `k` copies of `t`.
    calc
      s.sum a = s.sum (fun j ↦ (a j - t) + t) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ = s.sum (fun j ↦ a j - t) + s.sum (fun _ ↦ t) := by
            rw [Finset.sum_add_distrib]
      _ = s.sum (fun j ↦ a j - t) + t * k := by
            have hcard : s.card = k := by
              simpa [s, min_eq_right hk] using (Fin.card_filter_val_lt (n := n) (m := k))
            rw [Finset.sum_const, nsmul_eq_mul, hcard]
            ring
  have hsplit :
      (∑ j : Fin n, (a j - t) * b j) = s.sum (fun j ↦ (a j - t) * b j) +
        s'.sum (fun j ↦ (a j - t) * b j) := by
    -- Split the shifted sum into its prefix and tail parts.
    simpa [s, s'] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j : Fin n ↦ (j : ℕ) < k) (fun j ↦ (a j - t) * b j)).symm
  have hprefix_le : s.sum (fun j ↦ (a j - t) * b j) ≤ s.sum (fun j ↦ a j - t) := by
    -- On the prefix, the shifted coefficients are nonnegative and the weights are at most `1`.
    refine Finset.sum_le_sum ?_
    intro j hj
    have hjlt : (j : ℕ) < k := (Finset.mem_filter.mp hj).2
    have hjle : j ≤ i0 := by
      exact Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt hjlt)
    have hnonneg : 0 ≤ a j - t := by
      have haj : a i0 ≤ a j := ha hjle
      dsimp [t]
      linarith
    nlinarith [hb0 j, hb1 j, hnonneg]
  have htail_point : ∀ j ∈ s', (a j - t) * b j ≤ 0 := by
    -- On the tail, the shifted coefficients are nonpositive and the weights are nonnegative.
    intro j hj
    have hjge : k ≤ (j : ℕ) := Nat.le_of_not_lt ((Finset.mem_filter.mp hj).2)
    have hi0le_nat : k - 1 ≤ (j : ℕ) := by
      omega
    have hi0le : i0 ≤ j := Fin.le_iff_val_le_val.mpr hi0le_nat
    have hnonpos : a j - t ≤ 0 := by
      have haj : a j ≤ a i0 := ha hi0le
      dsimp [t]
      linarith
    nlinarith [hb0 j, hnonpos]
  have htail_le : s'.sum (fun j ↦ (a j - t) * b j) ≤ 0 := by
    calc
      s'.sum (fun j ↦ (a j - t) * b j) ≤ s'.sum (fun _ ↦ (0 : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact htail_point j hj
      _ = 0 := by
            simp
  have hmain_shift : (∑ j : Fin n, (a j - t) * b j) ≤ s.sum (fun j ↦ a j - t) := by
    -- Combine the prefix and tail bounds for the shifted sum.
    rw [hsplit]
    have hsum_le := add_le_add hprefix_le htail_le
    linarith
  -- Undo the shift and rewrite the prefix sum back as an indicator sum.
  calc
    (∑ j : Fin n, a j * b j) ≤ s.sum a := by
      linarith [hmain_shift, hsplit_left, hprefix_decomp]
    _ = ∑ j : Fin n, if (j : ℕ) < k then a j else 0 := by
          simpa [s] using (Finset.sum_filter (fun j : Fin n ↦ (j : ℕ) < k) a)

/-- Helper for Example 6.50: every feasible capped-simplex weight vector gives a pairing bounded
above by the sum of the `k` largest values. -/
private theorem inner_le_sum_of_k_largest_values_of_mem_constraint_set
    {k : ℕ} (hk : k ≤ Fintype.card ι) (x y : E)
    (hy : y ∈ sum_of_k_largest_constraint_set ι k) :
    ((toDualMap ℝ E x) y : ℝ) ≤ sum_of_k_largest_values k x := by
  by_cases hk_zero : k = 0
  · -- When `k = 0`, the capped simplex contains only the zero vector.
    have hy_sum : ∑ i : ι, y i = 0 := by
      simpa [hk_zero] using hy.1
    have hy_coord_zero : ∀ i : ι, y i = 0 := by
      intro i
      have hnonneg : 0 ≤ y i := (hy.2 i).1
      have hle_sum : y i ≤ ∑ j : ι, y j := by
        simpa using
          (Finset.single_le_sum
            (fun j _ ↦ (hy.2 j).1) (Finset.mem_univ i) :
              y i ≤ ∑ j ∈ (Finset.univ : Finset ι), y j)
      linarith
    have hy_zero : y = 0 := by
      ext i
      exact hy_coord_zero i
    -- The pairing and the top-`0` sum both vanish.
    rw [hy_zero, hk_zero, sum_of_k_largest_values]
    simp
  · have hk_pos : 0 < k := Nat.pos_iff_ne_zero.mpr hk_zero
    let b : Fin (Fintype.card ι) → ℝ := fun j ↦
      y ((Fintype.equivFin ι).symm (ranked_coordinate_perm x j))
    have hb0 : ∀ j, 0 ≤ b j := by
      intro j
      exact (hy.2 ((Fintype.equivFin ι).symm (ranked_coordinate_perm x j))).1
    have hb1 : ∀ j, b j ≤ 1 := by
      intro j
      exact (hy.2 ((Fintype.equivFin ι).symm (ranked_coordinate_perm x j))).2
    have hsum_b : ∑ j : Fin (Fintype.card ι), b j = k := by
      -- Reindex the coordinate sum by the ranked permutation.
      calc
        ∑ j : Fin (Fintype.card ι), b j
            = ∑ j : Fin (Fintype.card ι),
                y ((Fintype.equivFin ι).symm ((ranked_coordinate_equiv x) j)) := by
                refine Fintype.sum_congr _ _ ?_
                intro j
                simp [b, ranked_coordinate_equiv]
        _ = ∑ j : Fin (Fintype.card ι), y ((Fintype.equivFin ι).symm j) := by
              exact
                Fintype.sum_equiv (ranked_coordinate_equiv x)
                  (fun j : Fin (Fintype.card ι) ↦
                    y ((Fintype.equivFin ι).symm ((ranked_coordinate_equiv x) j)))
                  (fun j : Fin (Fintype.card ι) ↦ y ((Fintype.equivFin ι).symm j))
                  (fun j ↦ by simp)
        _ = ∑ i : ι, y i := by
              exact
                Fintype.sum_equiv (Fintype.equivFin ι).symm
                  (fun j : Fin (Fintype.card ι) ↦ y ((Fintype.equivFin ι).symm j))
                  (fun i : ι ↦ y i)
                  (fun j ↦ by simp)
        _ = k := hy.1
    have hupper :
        (∑ j : Fin (Fintype.card ι), ranked_value x j * b j) ≤
          ∑ j : Fin (Fintype.card ι), if (j : ℕ) < k then ranked_value x j else 0 :=
      sum_mul_le_ranked_prefix_of_boxed_weights hk_pos hk (ranked_value x) b
        (ranked_value_antitone x) hb0 hb1 hsum_b
    -- The inner product is exactly the ranked weighted sum, so the threshold lemma closes it.
    calc
      ((toDualMap ℝ E x) y : ℝ)
          = ∑ j : Fin (Fintype.card ι), ranked_value x j * b j := by
              rw [inner_eq_sum_ranked_coordinates]
              refine Fintype.sum_congr _ _ ?_
              intro j
              simp [b, ranked_value]
      _ ≤ ∑ j : Fin (Fintype.card ι), if (j : ℕ) < k then ranked_value x j else 0 := hupper
      _ = (((ranked_coordinate_pairs x).take k).map Prod.fst).sum := by
            symm
            exact sum_take_ranked_values_eq_prefix_indicator k x
      _ = sum_of_k_largest_values k x := by
            symm
            exact sum_of_k_largest_values_eq_sum_ranked_prefix k x

-- Proof sketch: maximize the linear functional `y ↦ ⟪x, y⟫` over the owner-level
-- capped-simplex owner `sum_of_k_largest_constraint_set k`. The maximizers
-- are the `0/1` vectors with exactly `k` ones placed at the coordinates of the
-- `k` largest entries of `x`, so the support value is the
-- sum of those `k` largest coordinates.
/-- The sum of the `k` largest values is the support function of the owner-level capped-simplex
constraint set. -/
theorem sum_of_k_largest_values_eq_support_function_constraint_set
    {k : ℕ} (hk : k ≤ Fintype.card ι) (x : E) :
    (sum_of_k_largest_values k x : EReal) =
      support_function (sum_of_k_largest_constraint_set ι k) (toDualMap ℝ E x) := by
  -- Route correction: the powerset-max route is unnecessary here. The governing object is the
  -- capped simplex itself, so the proof should use a single ranked coordinate order for both the
  -- maximizing witness and the universal upper bound.
  by_cases hk_zero : k = 0
  · -- The zero-sum capped simplex contains only the zero vector, so the support value is `0`.
    rw [hk_zero, sum_of_k_largest_values]
    simp
    symm
    refine support_function_eq_of_isGreatest_image
      (sum_of_k_largest_constraint_set ι 0) (toDualMap ℝ E x) ?_
    refine ⟨?_, ?_⟩
    · refine ⟨0, ?_, by simp⟩
      constructor
      · simp
      · intro i
        simp
    · rintro _ ⟨y, hy, rfl⟩
      have hy_sum : ∑ i : ι, y i = 0 := by
        simpa [hk_zero] using hy.1
      have hy_coord_zero : ∀ i : ι, y i = 0 := by
        intro i
        have hnonneg : 0 ≤ y i := (hy.2 i).1
        have hle_sum : y i ≤ ∑ j : ι, y j := by
          simpa using
            (Finset.single_le_sum
              (fun j _ ↦ (hy.2 j).1) (Finset.mem_univ i) :
                y i ≤ ∑ j ∈ (Finset.univ : Finset ι), y j)
        linarith
      have hy_zero : y = 0 := by
        ext i
        exact hy_coord_zero i
      rw [hy_zero]
      simp
  · have hwitness_mem :
        top_ranked_indicator x k ∈ sum_of_k_largest_constraint_set ι k :=
      top_ranked_indicator_mem_constraint_set x hk
    have hwitness_value :
        ((toDualMap ℝ E x) (top_ranked_indicator x k) : ℝ) =
          sum_of_k_largest_values k x :=
      top_ranked_indicator_attains_sum_of_k_largest_values x
    have hgreatest :
        IsGreatest ((fun y : E ↦ ((toDualMap ℝ E x) y : EReal)) ''
            sum_of_k_largest_constraint_set ι k)
          (sum_of_k_largest_values k x : EReal) := by
      refine ⟨?_, ?_⟩
      · refine ⟨top_ranked_indicator x k, hwitness_mem, ?_⟩
        exact congrArg (fun r : ℝ ↦ (r : EReal)) hwitness_value
      · rintro _ ⟨y, hy, rfl⟩
        exact
          (show (((toDualMap ℝ E x) y : ℝ) : EReal) ≤
              (sum_of_k_largest_values k x : EReal) from by
                exact_mod_cast
                  inner_le_sum_of_k_largest_values_of_mem_constraint_set hk x y hy)
    -- With the maximizing witness and the universal upper bound, the support function is exact.
    symm
    exact support_function_eq_of_isGreatest_image _ _ hgreatest

-- Proof sketch: rewrite the source-facing function with
-- `sum_of_k_largest_values_eq_support_function_constraint_set`, then apply Theorem 6.46 to the
-- capped-simplex owner `sum_of_k_largest_constraint_set k`.
-- The auxiliary lemmas `sum_of_k_largest_constraint_set_nonempty`,
-- `sum_of_k_largest_constraint_set_closed`, and
-- `sum_of_k_largest_constraint_set_convex` supply the projection data for `metricProjection`.
/-- Example 6.50: for `k ≤ Fintype.card ι`, if `f(x)` is the sum of the `k` largest values of
`x : EuclideanSpace ℝ ι`, then the proximal set of `λ f` at `x` is the singleton containing
`x - λ P_C (x / λ)`, where `C = {y | ∑ i, y i = k, 0 ≤ y i ≤ 1}` and `P_C` is the metric
projection onto `C`. Specializing to `ι = Fin n` recovers the textbook `ℝ^n` statement. -/
theorem prox_sum_of_k_largest_values_eq_singleton_sub_smul_metricProjection
    {k : ℕ} (hk : k ≤ Fintype.card ι) (lam : ℝ) (hlam : 0 < lam) (x : E) :
    prox[fun y : E ↦ (lam : EReal) * (sum_of_k_largest_values k y : EReal)] x
      =
        {x - lam •
          (metricProjectionOfComplete
            (sum_of_k_largest_constraint_set ι k)
            (sum_of_k_largest_constraint_set_nonempty ι hk)
            (sum_of_k_largest_constraint_set_closed ι k).isComplete
            (sum_of_k_largest_constraint_set_convex ι k)
            (lam⁻¹ • x) : E)} := by
  let lamPos : PosReal := ⟨lam, hlam⟩
  have hpenalty :
      (fun y : E ↦ (lam : EReal) * (sum_of_k_largest_values k y : EReal)) =
        (((lam : ℝ) : EReal) • σ[sum_of_k_largest_constraint_set ι k]) := by
    funext y
    -- Rewrite the source-facing top-`k` sum as the support function of the capped simplex.
    rw [Pi.smul_apply, support_function_primal_apply,
      sum_of_k_largest_values_eq_support_function_constraint_set (ι := ι) hk y]
    simp [smul_eq_mul]
  -- With the support-function bridge in place, Theorem 6.46 applies verbatim.
  rw [hpenalty]
  simpa [lamPos] using
    prox_support_function_eq_singleton_sub_smul_metricProjection
      (C := sum_of_k_largest_constraint_set ι k)
      (hC_nonempty := sum_of_k_largest_constraint_set_nonempty ι hk)
      (hC_complete := (sum_of_k_largest_constraint_set_closed ι k).isComplete)
      (hC_convex := sum_of_k_largest_constraint_set_convex ι k)
      lamPos x

end
