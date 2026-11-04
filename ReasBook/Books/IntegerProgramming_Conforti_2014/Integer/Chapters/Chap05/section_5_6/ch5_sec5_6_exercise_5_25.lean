/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_theorem_5_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_25.PrefixClosure

open scoped CoordinateLiftProjectNotation

-- Primary domain: Chapter 5 lift-and-project closures on prefix coordinates in `ℝ^n`.
-- Core/canonical owners reused here: `is_polyhedron`, `coordinate_lift_project_hull`, and
-- `lift_project_closure`.
-- This file stays source-facing: it reuses the item-local prefix-closure and binary-point owners
-- from Exercise 5.25 while proving the `k`-subset intersection formula through the canonical
-- Chapter 5 lift-project owner.

section Exercise525

variable {n p : ℕ}

/-- Helper for Exercise 5.25: enlarging the binary index set only shrinks the admissible-point
family. -/
private lemma binaryPrefixPointsOnSubset_mono
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {K L : Finset (Fin p)}
    (hKL : K ⊆ L) :
    binary_prefix_points_on_subset hp P L ⊆
      binary_prefix_points_on_subset hp P K := by
  intro x hx
  rcases hx with ⟨hxP, hxBinary⟩
  -- Restrict the binary conditions from the larger index set `L` back to `K`.
  refine ⟨hxP, ?_⟩
  intro j hjK
  exact hxBinary j (hKL hjK)

/-- Helper for Exercise 5.25: `coordinate_lift_project_hull` is monotone in its set argument. -/
private lemma coordinateLiftProjectHull_mono
    {A B : Set (Fin n → ℝ)}
    (hAB : A ⊆ B)
    (j : Fin n) :
    coordinate_lift_project_hull A j ⊆ coordinate_lift_project_hull B j := by
  -- Push the subset relation through the defining convex hull.
  rw [coordinate_lift_project_hull_def, coordinate_lift_project_hull_def]
  exact convexHull_mono <| by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hAB hx.1, hx.2⟩
    · exact Or.inr ⟨hAB hx.1, hx.2⟩

/-- Helper for Exercise 5.25: enlarging the binary index set makes the corresponding convex hull
smaller. -/
private lemma binaryPrefixHull_mono
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {K L : Finset (Fin p)}
    (hKL : K ⊆ L) :
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ⊆
      convexHull ℝ (binary_prefix_points_on_subset hp P K) := by
  -- First shrink the generating family, then use monotonicity of `convexHull`.
  exact convexHull_mono <| binaryPrefixPointsOnSubset_mono hp P hKL

/-- Helper for Exercise 5.25: if every generator in `A` already has coordinate `j` in `[0,1]`,
then the `j`-coordinate lift-project hull of `convexHull ℝ A` is generated exactly by the
`j = 0` and `j = 1` slices of `A`. -/
private lemma coordinateLiftProjectHull_convexHull_eq_ofCoordinateBounds
    (A : Set (Fin n → ℝ))
    (j : Fin n)
    (hA_bounds : ∀ x ∈ A, 0 ≤ x j ∧ x j ≤ 1) :
    coordinate_lift_project_hull (convexHull ℝ A) j =
      convexHull ℝ
        ((A ∩ {x : Fin n → ℝ | x j = 0}) ∪
          (A ∩ {x : Fin n → ℝ | x j = 1})) := by
  let πj : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
  have hpreimageZero :
      (-πj) ⁻¹' ({0} : Set ℝ) = {x : Fin n → ℝ | x j = 0} := by
    ext x
    simp [πj]
  have hpreimageOne :
      πj ⁻¹' ({1} : Set ℝ) = {x : Fin n → ℝ | x j = 1} := by
    ext x
    simp [πj]
  -- Route correction: normalize the two hyperplane slices of `convexHull ℝ A` first, then
  -- collapse the resulting nested convex hulls.
  have hsliceZero :
      convexHull ℝ A ∩ {x : Fin n → ℝ | x j = 0} =
        convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 0}) := by
    have hA_nonpos : A ⊆ (-πj) ⁻¹' Set.Iic (0 : ℝ) := by
      intro x hx
      have hxj_nonneg := (hA_bounds x hx).1
      simpa [πj, LinearMap.proj_apply] using neg_nonpos.mpr hxj_nonneg
    calc
      convexHull ℝ A ∩ {x : Fin n → ℝ | x j = 0}
          = convexHull ℝ A ∩ (-πj) ⁻¹' ({0} : Set ℝ) := by
              rw [hpreimageZero]
      _ = convexHull ℝ (A ∩ (-πj) ⁻¹' ({0} : Set ℝ)) :=
            convexHull_inter_hyperplane_eq A (-πj) (0 : ℝ) hA_nonpos
      _ = convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 0}) := by
            rw [hpreimageZero]
  have hsliceOne :
      convexHull ℝ A ∩ {x : Fin n → ℝ | x j = 1} =
        convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 1}) := by
    have hA_le_one : A ⊆ πj ⁻¹' Set.Iic (1 : ℝ) := by
      intro x hx
      exact (hA_bounds x hx).2
    calc
      convexHull ℝ A ∩ {x : Fin n → ℝ | x j = 1}
          = convexHull ℝ A ∩ πj ⁻¹' ({1} : Set ℝ) := by
              rw [hpreimageOne]
      _ = convexHull ℝ (A ∩ πj ⁻¹' ({1} : Set ℝ)) :=
            convexHull_inter_hyperplane_eq A πj (1 : ℝ) hA_le_one
      _ = convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 1}) := by
            rw [hpreimageOne]
  calc
    coordinate_lift_project_hull (convexHull ℝ A) j
        = convexHull ℝ
            (((convexHull ℝ A) ∩ {x : Fin n → ℝ | x j = 0}) ∪
              ((convexHull ℝ A) ∩ {x : Fin n → ℝ | x j = 1})) := by
            rw [coordinate_lift_project_hull_def]
    _ = convexHull ℝ
          (convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 0}) ∪
            ((convexHull ℝ A) ∩ {x : Fin n → ℝ | x j = 1})) := by
          rw [hsliceZero]
    _ = convexHull ℝ
          (convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 0}) ∪
            convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 1})) := by
          rw [hsliceOne]
    _ = convexHull ℝ
          ((A ∩ {x : Fin n → ℝ | x j = 0}) ∪
            convexHull ℝ (A ∩ {x : Fin n → ℝ | x j = 1})) := by
          rw [convexHull_convexHull_union_left]
    _ = convexHull ℝ
          ((A ∩ {x : Fin n → ℝ | x j = 0}) ∪
            (A ∩ {x : Fin n → ℝ | x j = 1})) := by
          rw [convexHull_convexHull_union_right]

/-- Helper for Exercise 5.25: if `i ∈ L`, then the hull generated by points that are already
binary on `L` is fixed by the `i`-coordinate lift-project operator. -/
private lemma binaryPrefixHull_fixedByCoordinateHull
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {L : Finset (Fin p)}
    {i : Fin p}
    (hi : i ∈ L) :
    coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L))
        (Fin.castLE hp i) =
      convexHull ℝ (binary_prefix_points_on_subset hp P L) := by
  -- Route correction: use the owner-level slice characterization instead of reproving the fixed
  -- point statement directly from the convex-hull definition.
  calc
    coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L))
        (Fin.castLE hp i)
        = convexHull ℝ
            (((binary_prefix_points_on_subset hp P L) ∩
                {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) ∪
              ((binary_prefix_points_on_subset hp P L) ∩
                {x : Fin n → ℝ | x (Fin.castLE hp i) = 1})) := by
            refine coordinateLiftProjectHull_convexHull_eq_ofCoordinateBounds
              (binary_prefix_points_on_subset hp P L) (Fin.castLE hp i) ?_
            intro x hx
            have hxi :
                x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 := by
              exact (mem_binary_prefix_points_on_subset_iff hp P L x).mp hx |>.2 i hi
            rcases hxi with hxi | hxi <;> constructor <;> linarith
    _ = convexHull ℝ (binary_prefix_points_on_subset hp P L) := by
          refine congrArg (convexHull ℝ) ?_
          ext x
          constructor
          · intro hx
            rcases hx with ⟨hxL, hxi⟩ | ⟨hxL, hxi⟩
            · exact hxL
            · exact hxL
          · intro hxL
            have hxi :
                x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 := by
              exact (mem_binary_prefix_points_on_subset_iff hp P L x).mp hxL |>.2 i hi
            rcases hxi with hxi | hxi
            · exact Or.inl ⟨hxL, hxi⟩
            · exact Or.inr ⟨hxL, hxi⟩

/-- Helper for Exercise 5.25: every point in a coordinate lift-project hull has the split
coordinate in the interval `[0, 1]`. -/
private lemma coordinateLiftProjectHull_subset_coordinateStrip
    (A : Set (Fin n → ℝ))
    (j : Fin n) :
    coordinate_lift_project_hull A j ⊆
      {x : Fin n → ℝ | 0 ≤ x j ∧ x j ≤ 1} := by
  rw [coordinate_lift_project_hull_def]
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases hx with hx | hx
    · constructor <;> linarith [hx.2.symm]
    · constructor <;> linarith [hx.2.symm]
  · -- The strip `0 ≤ x j ≤ 1` is convex because it is an intersection of two affine halfspaces.
    let πj : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
    have hLower : Convex ℝ (πj ⁻¹' Set.Ici (0 : ℝ)) :=
      (convex_Ici (0 : ℝ)).linear_preimage πj
    have hUpper : Convex ℝ (πj ⁻¹' Set.Iic (1 : ℝ)) :=
      (convex_Iic (1 : ℝ)).linear_preimage πj
    simpa [πj, LinearMap.proj_apply, Set.preimage, Set.setOf_and] using hLower.inter hUpper

/-- Helper for Exercise 5.25: if `i ∈ L`, then every point of the corresponding binary-prefix
hull has `i`th coordinate in `[0, 1]`. -/
private lemma binaryPrefixHull_coordinateBounds
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {L : Finset (Fin p)}
    {i : Fin p}
    (hi : i ∈ L) :
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ⊆
      {x : Fin n → ℝ | 0 ≤ x (Fin.castLE hp i) ∧ x (Fin.castLE hp i) ≤ 1} := by
  intro x hx
  -- Rewrite through the fixed-point characterization so the generic strip lemma applies.
  have hxHull :
      x ∈ coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L))
        (Fin.castLE hp i) := by
    simpa [binaryPrefixHull_fixedByCoordinateHull hp P hi] using hx
  exact coordinateLiftProjectHull_subset_coordinateStrip _ _ hxHull

/-- Helper for Exercise 5.25: there is exactly one `0`-subset, namely `∅`, so the right-hand
side at `k = 0` is just `P`. -/
private lemma iInter_convexHull_binary_on_zero_subsets
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P) :
    (⋂ J : {J : Finset (Fin p) // J.card = 0},
      convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) = P := by
  have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iInter] at hx
    have hxEmpty :
        x ∈ convexHull ℝ (binary_prefix_points_on_subset hp P (∅ : Finset (Fin p))) := by
      simpa using hx ⟨∅, by simp⟩
    have hEmpty :
        binary_prefix_points_on_subset hp P (∅ : Finset (Fin p)) = P := by
      ext y
      simp [binary_prefix_points_on_subset]
    rw [hEmpty] at hxEmpty
    exact (Convex.convexHull_eq hP_convex) ▸ hxEmpty
  · intro hx
    simp only [Set.mem_iInter]
    rintro ⟨J, hJcard⟩
    -- Every `0`-subset is definitionally `∅`, so each factor is `convexHull ℝ P = P`.
    have hJ : J = ∅ := Finset.card_eq_zero.mp hJcard
    subst J
    simpa [binary_prefix_points_on_subset] using
      show x ∈ convexHull ℝ P from (Convex.convexHull_eq hP_convex).symm ▸ hx

/-- Helper for Exercise 5.25: every `k`-subset extends to a `(k + 1)`-subset whenever
`k + 1 ≤ p`. -/
private lemma existsSuperset_card_succ
    {k : ℕ}
    (K : Finset (Fin p))
    (hK : K.card = k)
    (hk : k + 1 ≤ p) :
    ∃ L : Finset (Fin p), K ⊆ L ∧ L.card = k + 1 := by
  classical
  have hKlt : K.card < (Finset.univ : Finset (Fin p)).card := by
    simpa [hK, Fintype.card_fin] using hk
  obtain ⟨i, -, hiK⟩ := Finset.exists_mem_notMem_of_card_lt_card hKlt
  refine ⟨insert i K, ?_, ?_⟩
  · intro j hjK
    exact Finset.mem_insert_of_mem hjK
  · simp [hK, hiK]

/-- Helper for Exercise 5.25: a `k`-subset extends to a `(k + 1)`-subset containing a prescribed
index `i` whenever `k + 1 ≤ p`. -/
private lemma existsSuperset_card_succ_mem
    {k : ℕ}
    (i : Fin p)
    (K : Finset (Fin p))
    (hK : K.card = k)
    (hk : k + 1 ≤ p) :
    ∃ L : Finset (Fin p), K ⊆ L ∧ i ∈ L ∧ L.card = k + 1 := by
  classical
  by_cases hiK : i ∈ K
  · obtain ⟨L, hKL, hLcard⟩ := existsSuperset_card_succ K hK hk
    exact ⟨L, hKL, hKL hiK, hLcard⟩
  · refine ⟨insert i K, ?_, by simp, ?_⟩
    · intro j hjK
      exact Finset.mem_insert_of_mem hjK
    · simp [hK, hiK]

/-- Helper for Exercise 5.25: when `0 < k ≤ p`, there is a `k`-subset of `Fin p` containing a
prescribed index `i`. -/
private lemma existsSubset_card_eq_mem
    {k : ℕ}
    (hkPos : 0 < k)
    (hk : k ≤ p)
    (i : Fin p) :
    ∃ J : Finset (Fin p), J.card = k ∧ i ∈ J := by
  have hEraseCard : (Finset.univ.erase i).card + 1 = p := by
    simpa [Fintype.card_fin] using
      Finset.card_erase_add_one (by simp : i ∈ (Finset.univ : Finset (Fin p)))
  have hkPred :
      k - 1 ≤ (Finset.univ.erase i).card := by
    have hkSucc :
        (k - 1) + 1 ≤ (Finset.univ.erase i).card + 1 := by
      calc
        (k - 1) + 1 = k := by
          exact Nat.sub_add_cancel (Nat.succ_le_of_lt hkPos)
        _ ≤ p := hk
        _ = (Finset.univ.erase i).card + 1 := hEraseCard.symm
    exact Nat.le_of_add_le_add_right hkSucc
  obtain ⟨K, hKsubset, hKcard⟩ := Finset.exists_subset_card_eq hkPred
  have hiK : i ∉ K := by
    intro hiK
    exact (Finset.mem_erase.mp (hKsubset hiK)).1 rfl
  refine ⟨insert i K, by simpa [hKcard, hiK] using Nat.sub_add_cancel (Nat.succ_le_of_lt hkPos), by simp⟩

/-- Helper for Exercise 5.25: the intersection family on the right-hand side descends with `k`.
-/
private lemma iInter_convexHull_binary_on_succ_subsets_subset
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k + 1 ≤ p) :
    (⋂ J : {J : Finset (Fin p) // J.card = k + 1},
      convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) ⊆
    ⋂ J : {J : Finset (Fin p) // J.card = k},
      convexHull ℝ (binary_prefix_points_on_subset hp P J.1) := by
  intro x hx
  simp only [Set.mem_iInter] at hx ⊢
  intro J
  obtain ⟨L, hJL, hLcard⟩ := existsSuperset_card_succ J.1 J.2 hk
  -- Compare the `(k + 1)`-subset factor indexed by `L` with the `k`-subset factor indexed by `J`.
  exact (binaryPrefixHull_mono hp P hJL) (hx ⟨L, hLcard⟩)

/-- Helper for Exercise 5.25: the binary-point family on a singleton index set is exactly the
union of the corresponding `0`- and `1`-coordinate slices of `P`. -/
private lemma binaryPrefixPointsOnSingleton_eq_coordinateSlices
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p) :
    binary_prefix_points_on_subset hp P ({i} : Finset (Fin p)) =
      ((P ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) ∪
        (P ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1})) := by
  ext x
  constructor
  · intro hx
    rcases (mem_binary_prefix_points_on_subset_iff hp P {i} x).mp hx with ⟨hxP, hxBinary⟩
    have hxi : x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 := by
      exact hxBinary i (by simp)
    rcases hxi with hxi | hxi
    · exact Or.inl ⟨hxP, hxi⟩
    · exact Or.inr ⟨hxP, hxi⟩
  · intro hx
    refine (mem_binary_prefix_points_on_subset_iff hp P {i} x).2 ?_
    rcases hx with ⟨hxP, hxi⟩ | ⟨hxP, hxi⟩
    · refine ⟨hxP, ?_⟩
      intro j hj
      have hj' : j = i := by simpa using hj
      subst j
      exact Or.inl hxi
    · refine ⟨hxP, ?_⟩
      intro j hj
      have hj' : j = i := by simpa using hj
      subst j
      exact Or.inr hxi

/-- Helper for Exercise 5.25: adding one binary coordinate splits the point family into its
`0`- and `1`-slices along that coordinate. -/
private lemma binaryPrefixPointsOnSubset_insert_eq_union_coordinateSlices
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (_hiK : i ∉ K) :
    binary_prefix_points_on_subset hp P (insert i K) =
      ((binary_prefix_points_on_subset hp P K) ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) ∪
        ((binary_prefix_points_on_subset hp P K) ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
  ext x
  constructor
  · intro hx
    rcases (mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).mp hx with
      ⟨hxP, hxBinary⟩
    have hxK : x ∈ binary_prefix_points_on_subset hp P K := by
      -- Forget the new coordinate and keep the old binary conditions on `K`.
      refine (mem_binary_prefix_points_on_subset_iff hp P K x).2 ?_
      refine ⟨hxP, ?_⟩
      intro j hjK
      exact hxBinary j (Finset.mem_insert_of_mem hjK)
    have hxi : x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 := by
      exact hxBinary i (by simp)
    rcases hxi with hxi | hxi
    · exact Or.inl ⟨hxK, hxi⟩
    · exact Or.inr ⟨hxK, hxi⟩
  · intro hx
    rcases hx with ⟨hxK, hxi0⟩ | ⟨hxK, hxi1⟩
    · rcases (mem_binary_prefix_points_on_subset_iff hp P K x).mp hxK with ⟨hxP, hxBinaryK⟩
      -- Reassemble the binary conditions on `insert i K` using the `x_i = 0` branch.
      refine (mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).2 ?_
      refine ⟨hxP, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjK
      · exact Or.inl (by simpa using hxi0)
      · exact hxBinaryK j hjK
    · rcases (mem_binary_prefix_points_on_subset_iff hp P K x).mp hxK with ⟨hxP, hxBinaryK⟩
      -- The `x_i = 1` branch is identical except for the final binary witness at `i`.
      refine (mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).2 ?_
      refine ⟨hxP, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjK
      · exact Or.inr (by simpa using hxi1)
      · exact hxBinaryK j hjK

/-- Helper for Exercise 5.25: on the `x_i = 0` hyperplane, adding `i` to the binary index set is
redundant already at the point-family level. -/
private lemma binaryPrefixPointsOnSubset_insert_inter_coordinateZero_eq
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (_hiK : i ∉ K) :
    binary_prefix_points_on_subset hp P (insert i K) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} =
      binary_prefix_points_on_subset hp P K ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} := by
  ext x
  constructor
  · rintro ⟨hxInsert, hxi⟩
    rcases (mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).mp hxInsert with
      ⟨hxP, hxBinary⟩
    refine ⟨(mem_binary_prefix_points_on_subset_iff hp P K x).2 ?_, hxi⟩
    refine ⟨hxP, ?_⟩
    intro j hjK
    exact hxBinary j (Finset.mem_insert_of_mem hjK)
  · rintro ⟨hxK, hxi⟩
    rcases (mem_binary_prefix_points_on_subset_iff hp P K x).mp hxK with ⟨hxP, hxBinaryK⟩
    refine ⟨(mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).2 ?_, hxi⟩
    refine ⟨hxP, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjK
    · exact Or.inl (by simpa using hxi)
    · exact hxBinaryK j hjK

/-- Helper for Exercise 5.25: on the `x_i = 1` hyperplane, adding `i` to the binary index set is
redundant already at the point-family level. -/
private lemma binaryPrefixPointsOnSubset_insert_inter_coordinateOne_eq
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (_hiK : i ∉ K) :
    binary_prefix_points_on_subset hp P (insert i K) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} =
      binary_prefix_points_on_subset hp P K ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} := by
  ext x
  constructor
  · rintro ⟨hxInsert, hxi⟩
    rcases (mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).mp hxInsert with
      ⟨hxP, hxBinary⟩
    refine ⟨(mem_binary_prefix_points_on_subset_iff hp P K x).2 ?_, hxi⟩
    refine ⟨hxP, ?_⟩
    intro j hjK
    exact hxBinary j (Finset.mem_insert_of_mem hjK)
  · rintro ⟨hxK, hxi⟩
    rcases (mem_binary_prefix_points_on_subset_iff hp P K x).mp hxK with ⟨hxP, hxBinaryK⟩
    refine ⟨(mem_binary_prefix_points_on_subset_iff hp P (insert i K) x).2 ?_, hxi⟩
    refine ⟨hxP, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjK
    · exact Or.inr (by simpa using hxi)
    · exact hxBinaryK j hjK

/-- Helper for Exercise 5.25: intersecting the `(k + 1)`-subset hulls that contain a fixed
coordinate `i` is contained in the global `k`-subset intersection. -/
private lemma restrictedBinaryPrefixHull_subset_predecessorFamily
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k + 1 ≤ p)
    (i : Fin p) :
    (⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1)) ⊆
    ⋂ J : {J : Finset (Fin p) // J.card = k},
      convexHull ℝ (binary_prefix_points_on_subset hp P J.1) := by
  intro x hx
  simp only [Set.mem_iInter] at hx ⊢
  intro J
  obtain ⟨L, hJL, hiL, hLcard⟩ := existsSuperset_card_succ_mem i J.1 J.2 hk
  -- Extend the target `k`-subset to a `(k + 1)`-subset containing `i`, then use monotonicity.
  exact (binaryPrefixHull_mono hp P hJL) (hx ⟨L, by exact ⟨hLcard, hiL⟩⟩)

/-- Helper for Exercise 5.25: slicing an `L`-binary hull on the hyperplane `x_i = 0` keeps
exactly the generators that already satisfy `x_i = 0`. -/
private lemma binaryPrefixHull_inter_coordinateZero
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {L : Finset (Fin p)}
    {i : Fin p}
    (hi : i ∈ L) :
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} =
      convexHull ℝ
        (binary_prefix_points_on_subset hp P L ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
  let πi : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (Fin.castLE hp i)
  have hpreimageZero :
      (-πi) ⁻¹' ({0} : Set ℝ) = {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} := by
    ext x
    simp [πi]
  have hA_nonpos :
      binary_prefix_points_on_subset hp P L ⊆ (-πi) ⁻¹' Set.Iic (0 : ℝ) := by
    intro x hx
    have hxi :
        x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 :=
      (mem_binary_prefix_points_on_subset_iff hp P L x).mp hx |>.2 i hi
    have hxi_nonneg : 0 ≤ x (Fin.castLE hp i) := by
      rcases hxi with hxi | hxi <;> linarith
    simpa [πi, LinearMap.proj_apply] using neg_nonpos.mpr hxi_nonneg
  -- Route correction: use the boundary-slice theorem at the owner level instead of unfolding
  -- the whole predecessor-family intersection.
  calc
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}
        = convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩ (-πi) ⁻¹' ({0} : Set ℝ) := by
            rw [hpreimageZero]
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P L ∩ (-πi) ⁻¹' ({0} : Set ℝ)) :=
          convexHull_inter_hyperplane_eq
            (binary_prefix_points_on_subset hp P L) (-πi) (0 : ℝ) hA_nonpos
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P L ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
          rw [hpreimageZero]

/-- Helper for Exercise 5.25: slicing an `L`-binary hull on the hyperplane `x_i = 1` keeps
exactly the generators that already satisfy `x_i = 1`. -/
private lemma binaryPrefixHull_inter_coordinateOne
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {L : Finset (Fin p)}
    {i : Fin p}
    (hi : i ∈ L) :
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} =
      convexHull ℝ
        (binary_prefix_points_on_subset hp P L ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
  let πi : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (Fin.castLE hp i)
  have hpreimageOne :
      πi ⁻¹' ({1} : Set ℝ) = {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} := by
    ext x
    simp [πi]
  have hA_le_one :
      binary_prefix_points_on_subset hp P L ⊆ πi ⁻¹' Set.Iic (1 : ℝ) := by
    intro x hx
    have hxi :
        x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1 :=
      (mem_binary_prefix_points_on_subset_iff hp P L x).mp hx |>.2 i hi
    rcases hxi with hxi | hxi <;> simpa [πi, LinearMap.proj_apply, hxi]
  -- The upper boundary slice is handled by the same owner theorem at level `1`.
  calc
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}
        = convexHull ℝ (binary_prefix_points_on_subset hp P L) ∩ πi ⁻¹' ({1} : Set ℝ) := by
            rw [hpreimageOne]
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P L ∩ πi ⁻¹' ({1} : Set ℝ)) :=
          convexHull_inter_hyperplane_eq
            (binary_prefix_points_on_subset hp P L) πi (1 : ℝ) hA_le_one
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P L ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
          rw [hpreimageOne]

/-- Helper for Exercise 5.25: the full `(k + 1)`-subset intersection is contained in each
coordinate-restricted `(k + 1)`-subset family. -/
private lemma succBinaryPrefixHull_subset_restrictedFamily
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (i : Fin p) :
    (⋂ L : {L : Finset (Fin p) // L.card = k + 1},
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1)) ⊆
    ⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1) := by
  intro x hx
  simp only [Set.mem_iInter] at hx ⊢
  intro L
  exact hx ⟨L.1, L.2.1⟩

/-- Helper for Exercise 5.25: the predecessor-family coordinate hulls on a fixed `(k + 1)`-subset
recover the hull that is binary on the whole subset. -/
private lemma binaryPrefixHull_subset_predecessorFamilyIntersection
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (L : Finset (Fin p))
    (_hL : L.card = k + 1) :
    convexHull ℝ (binary_prefix_points_on_subset hp P L) ⊆
      (⋂ j : {j : Fin p // j ∈ L},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
          (Fin.castLE hp j.1)) := by
  intro x hx
  -- Each predecessor factor already contains the full `L`-binary hull by monotonicity.
  simp only [Set.mem_iInter]
  intro j
  have hHullMono :
      convexHull ℝ (binary_prefix_points_on_subset hp P L) ⊆
        convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)) :=
    binaryPrefixHull_mono hp P (Finset.erase_subset j.1 L)
  have hxFixed :
      x ∈ coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L))
        (Fin.castLE hp j.1) := by
    -- The `j`th coordinate is already binary on the full `L`-family.
    simpa [binaryPrefixHull_fixedByCoordinateHull hp P j.2] using hx
  exact coordinateLiftProjectHull_mono hHullMono (Fin.castLE hp j.1) hxFixed

/-- Helper for Exercise 5.25: the restricted `(k + 1)`-subset family is stable under taking the
contracting direction of the `i`-coordinate lift-project hull. -/
private lemma coordinateHull_restrictedBinaryPrefixHull_subset
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (i : Fin p) :
    coordinate_lift_project_hull
        (⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
          convexHull ℝ (binary_prefix_points_on_subset hp P L.1))
        (Fin.castLE hp i) ⊆
      ⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
        convexHull ℝ (binary_prefix_points_on_subset hp P L.1) := by
  intro x hx
  -- Compare the restricted family with each factor and use factorwise coordinate stability.
  simp only [Set.mem_iInter]
  intro L
  have hFamilySubset :
      (⋂ M : {M : Finset (Fin p) // M.card = k + 1 ∧ i ∈ M},
        convexHull ℝ (binary_prefix_points_on_subset hp P M.1)) ⊆
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1) := by
    intro y hy
    have hyAll :
        ∀ M : {M : Finset (Fin p) // M.card = k + 1 ∧ i ∈ M},
          y ∈ convexHull ℝ (binary_prefix_points_on_subset hp P M.1) := by
      simpa only [Set.mem_iInter] using hy
    exact hyAll L
  have hxFactor :
      x ∈ coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L.1))
        (Fin.castLE hp i) :=
    coordinateLiftProjectHull_mono hFamilySubset (Fin.castLE hp i) hx
  simpa [binaryPrefixHull_fixedByCoordinateHull hp P L.2.2] using hxFactor

/-- Helper for Exercise 5.25: after adding `i` to the binary index set, the `0`-slice of the
resulting convex hull is the same slice already seen before adding `i`. -/
private lemma binaryPrefixHull_insert_inter_coordinateZero
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (hiK : i ∉ K) :
    convexHull ℝ (binary_prefix_points_on_subset hp P (insert i K)) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} =
      convexHull ℝ
        (binary_prefix_points_on_subset hp P K ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
  -- First identify the `0`-slice through the owner boundary-slice lemma, then rewrite the
  -- underlying point family using the insert normalization.
  calc
    convexHull ℝ (binary_prefix_points_on_subset hp P (insert i K)) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}
        = convexHull ℝ
            (binary_prefix_points_on_subset hp P (insert i K) ∩
              {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
            simpa using
              (@binaryPrefixHull_inter_coordinateZero n p hp P (insert i K) i (by simp))
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P K ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
          rw [binaryPrefixPointsOnSubset_insert_inter_coordinateZero_eq hp P i K hiK]

/-- Helper for Exercise 5.25: after adding `i` to the binary index set, the `1`-slice of the
resulting convex hull is the same slice already seen before adding `i`. -/
private lemma binaryPrefixHull_insert_inter_coordinateOne
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (hiK : i ∉ K) :
    convexHull ℝ (binary_prefix_points_on_subset hp P (insert i K)) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} =
      convexHull ℝ
        (binary_prefix_points_on_subset hp P K ∩
          {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
  -- The `1`-slice follows from the same owner-level slice theorem and point-family rewrite.
  calc
    convexHull ℝ (binary_prefix_points_on_subset hp P (insert i K)) ∩
        {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}
        = convexHull ℝ
            (binary_prefix_points_on_subset hp P (insert i K) ∩
              {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
            simpa using
              (@binaryPrefixHull_inter_coordinateOne n p hp P (insert i K) i (by simp))
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P K ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
          rw [binaryPrefixPointsOnSubset_insert_inter_coordinateOne_eq hp P i K hiK]

/-- Helper for Exercise 5.25: adding `i` to the binary index set gives a hull that already lies in
the `i`-coordinate lift-project hull of the old binary-prefix hull. -/
private lemma binaryPrefixHull_insert_subset_coordinateLiftProjectHull
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (i : Fin p)
    (K : Finset (Fin p))
    (hiK : i ∉ K) :
    convexHull ℝ (binary_prefix_points_on_subset hp P (insert i K)) ⊆
      coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P K))
        (Fin.castLE hp i) := by
  -- Route correction: this is the honest one-step inclusion available from the insert-slice
  -- description of the generators; equality would require an additional boundary theorem that
  -- is not present here.
  rw [binaryPrefixPointsOnSubset_insert_eq_union_coordinateSlices hp P i K hiK]
  rw [coordinate_lift_project_hull_def]
  refine convexHull_mono ?_
  intro x hx
  rcases hx with ⟨hxK, hxi0⟩ | ⟨hxK, hxi1⟩
  · exact Or.inl ⟨subset_convexHull ℝ _ hxK, by simpa using hxi0⟩
  · exact Or.inr ⟨subset_convexHull ℝ _ hxK, by simpa using hxi1⟩

/-- Helper for Exercise 5.25: polyhedra are closed under binary intersection. -/
private lemma isPolyhedron_inter_local
    {A B : Set (Fin n → ℝ)}
    (hA : is_polyhedron A)
    (hB : is_polyhedron B) :
    is_polyhedron (A ∩ B) := by
  rcases is_polyhedron_iff.mp hA with ⟨mA, MA, bA, rfl⟩
  rcases is_polyhedron_iff.mp hB with ⟨mB, MB, bB, rfl⟩
  -- Present both factors by matrices and stack the two systems.
  refine (is_polyhedron_iff).2 ⟨mA + mB, Fin.append MA MB, Fin.append bA bB, ?_⟩
  ext x
  constructor
  · rintro ⟨hxA, hxB⟩
    rw [mem_polyhedron_le_set_iff] at hxA hxB ⊢
    -- The appended matrix system splits into the two original row blocks.
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro iA
      simpa [Matrix.mulVec] using hxA iA
    · intro iB
      simpa [Matrix.mulVec] using hxB iB
  · intro hx
    rw [mem_polyhedron_le_set_iff] at hx
    refine ⟨?_, ?_⟩
    · -- Restrict the stacked system to the first block of rows.
      rw [mem_polyhedron_le_set_iff]
      intro iA
      simpa [Matrix.mulVec] using hx (Fin.castAdd mB iA)
    · -- Restrict the stacked system to the second block of rows.
      rw [mem_polyhedron_le_set_iff]
      intro iB
      simpa [Matrix.mulVec] using hx (Fin.natAdd mA iB)

/-- Helper for Exercise 5.25: the affine lower endpoint reconstructed from a strict-strip point
and an `x_i = 1` upper endpoint lands on the `x_i = 0` boundary and recovers the original point.
-/
private lemma strictStrip_lowerEndpoint_formula
    {x x1 : Fin n → ℝ}
    (i : Fin n)
    (hxiPos : 0 < x i)
    (hxiLtOne : x i < 1)
    (hx1 : x1 i = 1) :
    let x0 : Fin n → ℝ := (1 - x i)⁻¹ • (x - x i • x1)
    x0 i = 0 ∧
      x = (1 - x i) • x0 + x i • x1 := by
  have hxiNonneg : 0 ≤ x i := hxiPos.le
  have hden : (1 - x i : ℝ) ≠ 0 := by
    linarith
  dsimp
  constructor
  · -- The upper endpoint contributes exactly `x_i`, so the affine subtraction zeros out
    -- the distinguished coordinate.
    simp [hx1]
  · -- Expanding the affine expression shows that the reconstructed lower endpoint and the
    -- chosen upper endpoint recover `x` coordinatewise.
    ext j
    symm
    calc
      ((1 - x i) • ((1 - x i)⁻¹ • (x - x i • x1)) + x i • x1) j
          = (1 - x i) * ((1 - x i)⁻¹ * (x j - x i * x1 j)) + x i * x1 j := by
              simp [Pi.add_apply, Pi.sub_apply]
      _ = x j - x i * x1 j + x i * x1 j := by
            field_simp [hden]
      _ = x j := by
            ring

/-- Helper for Exercise 5.25: the coordinate lift-project hull of a polyhedron is again a
polyhedron. -/
private lemma coordinateLiftProjectHull_isPolyhedron_of_isPolyhedron
    {A : Set (Fin n → ℝ)}
    (hA : is_polyhedron A)
    (i : Fin n) :
    is_polyhedron (coordinate_lift_project_hull A i) := by
  rcases is_polyhedron_iff.mp hA with ⟨m, M, b, rfl⟩
  -- Reduce to the matrix owner theorem for coordinate lift-project hulls.
  simpa using coordinate_lift_project_hull_is_polyhedron M b i

/-- Helper for Exercise 5.25: a strict-strip point in a coordinate lift-project hull of a convex
set is the affine combination of points on its two coordinate boundary faces. -/
private lemma coordinateLiftProjectHull_strictStrip_hasBoundaryPair
    {A : Set (Fin n → ℝ)}
    (hA : Convex ℝ A)
    (i : Fin n)
    {x : Fin n → ℝ}
    (hx : x ∈ coordinate_lift_project_hull A i)
    (hxiPos : 0 < x i)
    (hxiLtOne : x i < 1) :
    ∃ x0 x1 : Fin n → ℝ,
      x0 ∈ A ∩ {y : Fin n → ℝ | y i = 0} ∧
      x1 ∈ A ∩ {y : Fin n → ℝ | y i = 1} ∧
      x = (1 - x i) • x0 + x i • x1 := by
  let A0 := A ∩ {y : Fin n → ℝ | y i = 0}
  let A1 := A ∩ {y : Fin n → ℝ | y i = 1}
  let πi : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i
  have hZeroConvex : Convex ℝ {y : Fin n → ℝ | y i = 0} := by
    simpa [πi, LinearMap.proj_apply] using
      (convex_singleton (0 : ℝ)).linear_preimage πi
  have hOneConvex : Convex ℝ {y : Fin n → ℝ | y i = 1} := by
    simpa [πi, LinearMap.proj_apply] using
      (convex_singleton (1 : ℝ)).linear_preimage πi
  have hA0Convex : Convex ℝ A0 := hA.inter hZeroConvex
  have hA1Convex : Convex ℝ A1 := hA.inter hOneConvex
  rw [coordinate_lift_project_hull_def] at hx
  have hA0Nonempty : A0.Nonempty := by
    by_contra hEmpty
    rw [Set.not_nonempty_iff_eq_empty] at hEmpty
    have hxOne : x ∈ convexHull ℝ A1 := by
      simpa [A0, A1, hEmpty] using hx
    have hxiOne : x i = 1 :=
      convexHull_min (fun y hy ↦ hy.2) hOneConvex hxOne
    linarith
  have hA1Nonempty : A1.Nonempty := by
    by_contra hEmpty
    rw [Set.not_nonempty_iff_eq_empty] at hEmpty
    have hxZero : x ∈ convexHull ℝ A0 := by
      simpa [A0, A1, hEmpty] using hx
    have hxiZero : x i = 0 :=
      convexHull_min (fun y hy ↦ hy.2) hZeroConvex hxZero
    linarith
  -- Convexity of the two faces turns the convex hull of their union into their convex join.
  have hxJoin : x ∈ convexJoin ℝ A0 A1 := by
    rw [hA0Convex.convexHull_union hA1Convex hA0Nonempty hA1Nonempty] at hx
    exact hx
  rcases (mem_convexJoin.mp hxJoin) with ⟨x0, hx0, x1, hx1, hxSegment⟩
  rcases hxSegment with ⟨a, b, ha, hb, hab, hcomb⟩
  have hx0Coord : x0 i = 0 := by
    simpa [A0] using hx0.2
  have hx1Coord : x1 i = 1 := by
    simpa [A1] using hx1.2
  have hbEq : b = x i := by
    have hcoord := congrFun hcomb i
    simpa [hx0Coord, hx1Coord] using hcoord
  have haEq : a = 1 - x i := by
    linarith
  refine ⟨x0, x1, hx0, hx1, ?_⟩
  calc
    x = a • x0 + b • x1 := hcomb.symm
    _ = (1 - x i) • x0 + x i • x1 := by rw [haEq, hbEq]

/-- Helper for Exercise 5.25: after erasing a coordinate from a binary index set, convexifying
again in that coordinate recovers the hull for the full index set. -/
private lemma binaryPrefixHull_erase_coordinateHull_eq
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box hp)
    {L : Finset (Fin p)}
    {i : Fin p}
    (hi : i ∈ L) :
    coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase i)))
        (Fin.castLE hp i) =
      convexHull ℝ (binary_prefix_points_on_subset hp P L) := by
  have hBounds :
      ∀ x ∈ binary_prefix_points_on_subset hp P (L.erase i),
        0 ≤ x (Fin.castLE hp i) ∧ x (Fin.castLE hp i) ≤ 1 := by
    intro x hx
    have hxP : x ∈ P :=
      (mem_binary_prefix_points_on_subset_iff hp P (L.erase i) x).mp hx |>.1
    exact (mem_prefix_unit_box_iff hp x).mp (hP_subset hxP) i
  have hiErase : i ∉ L.erase i := by
    simp
  -- Normalize the coordinate hull to its two generator slices, then insert the erased index.
  calc
    coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase i)))
        (Fin.castLE hp i)
        = convexHull ℝ
            (((binary_prefix_points_on_subset hp P (L.erase i)) ∩
                {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) ∪
              ((binary_prefix_points_on_subset hp P (L.erase i)) ∩
                {x : Fin n → ℝ | x (Fin.castLE hp i) = 1})) := by
            exact coordinateLiftProjectHull_convexHull_eq_ofCoordinateBounds
              (binary_prefix_points_on_subset hp P (L.erase i)) (Fin.castLE hp i) hBounds
    _ = convexHull ℝ
          (binary_prefix_points_on_subset hp P (insert i (L.erase i))) := by
          rw [binaryPrefixPointsOnSubset_insert_eq_union_coordinateSlices
            hp P i (L.erase i) hiErase]
    _ = convexHull ℝ (binary_prefix_points_on_subset hp P L) := by
          rw [Finset.insert_erase hi]

/-- Helper for Exercise 5.25: on the `x_i = 0` boundary, the predecessor-family intersection
already lies in the full `L`-binary hull. -/
private lemma predecessorFamily_coordinateZero_subset_binaryPrefixHull
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box hp)
    {k : ℕ}
    (L : Finset (Fin p))
    (hL : L.card = k + 1)
    {i : Fin p}
    (hi : i ∈ L) :
    let U :=
      ⋂ j : {j : Fin p // j ∈ L},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
          (Fin.castLE hp j.1)
    let B := convexHull ℝ (binary_prefix_points_on_subset hp P L)
    U ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} ⊆ B := by
  dsimp
  rintro x ⟨hxU, -⟩
  simp only [Set.mem_iInter] at hxU
  have hxFactor := hxU ⟨i, hi⟩
  -- The distinguished predecessor factor is exactly the full `L`-binary hull.
  rw [binaryPrefixHull_erase_coordinateHull_eq hp P hP_subset hi] at hxFactor
  exact hxFactor

/-- Helper for Exercise 5.25: on the `x_i = 1` boundary, the predecessor-family intersection
already lies in the full `L`-binary hull. -/
private lemma predecessorFamily_coordinateOne_subset_binaryPrefixHull
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box hp)
    {k : ℕ}
    (L : Finset (Fin p))
    (hL : L.card = k + 1)
    {i : Fin p}
    (hi : i ∈ L) :
    let U :=
      ⋂ j : {j : Fin p // j ∈ L},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
          (Fin.castLE hp j.1)
    let B := convexHull ℝ (binary_prefix_points_on_subset hp P L)
    U ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} ⊆ B := by
  dsimp
  rintro x ⟨hxU, -⟩
  simp only [Set.mem_iInter] at hxU
  have hxFactor := hxU ⟨i, hi⟩
  -- The same factor normalization handles the upper boundary.
  rw [binaryPrefixHull_erase_coordinateHull_eq hp P hP_subset hi] at hxFactor
  exact hxFactor

/-- Helper for Exercise 5.25: a strict-strip point of the predecessor family admits a boundary
pair in the full `L`-binary hull. -/
private lemma predecessorFamily_strictStrip_hasBoundaryPair
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box hp)
    {k : ℕ}
    (L : Finset (Fin p))
    (hL : L.card = k + 1)
    {i : Fin p}
    (hi : i ∈ L) :
    let U :=
      ⋂ j : {j : Fin p // j ∈ L},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
          (Fin.castLE hp j.1)
    let B := convexHull ℝ (binary_prefix_points_on_subset hp P L)
    ∀ ⦃x : Fin n → ℝ⦄,
      x ∈ U →
      0 < x (Fin.castLE hp i) →
      x (Fin.castLE hp i) < 1 →
      ∃ x0 x1 : Fin n → ℝ,
        x0 ∈ B ∩ {y : Fin n → ℝ | y (Fin.castLE hp i) = 0} ∧
        x1 ∈ B ∩ {y : Fin n → ℝ | y (Fin.castLE hp i) = 1} ∧
        x =
          (1 - x (Fin.castLE hp i)) • x0 +
            x (Fin.castLE hp i) • x1 := by
  dsimp
  intro x hxU hxiPos hxiLtOne
  have hxAll :
      ∀ j : {j : Fin p // j ∈ L},
        x ∈ coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
          (Fin.castLE hp j.1) := by
    simpa only [Set.mem_iInter] using hxU
  have hxB : x ∈ convexHull ℝ (binary_prefix_points_on_subset hp P L) := by
    have hxFactor := hxAll ⟨i, hi⟩
    rw [binaryPrefixHull_erase_coordinateHull_eq hp P hP_subset hi] at hxFactor
    exact hxFactor
  have hxCoordinate :
      x ∈ coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P L))
        (Fin.castLE hp i) := by
    rw [binaryPrefixHull_fixedByCoordinateHull hp P hi]
    exact hxB
  -- Apply the generic strict-strip decomposition directly to the full binary-prefix hull.
  exact coordinateLiftProjectHull_strictStrip_hasBoundaryPair
    (convex_convexHull ℝ _) (Fin.castLE hp i) hxCoordinate hxiPos hxiLtOne

/-- Helper for Exercise 5.25: once the predecessor-family point lies strictly inside the split
strip `0 < x_i < 1`, the boundary-pair description places it in the full `L`-binary hull. -/
private lemma predecessorFamily_strictStrip_subset_binaryPrefixHull
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box hp)
    {k : ℕ}
    (L : Finset (Fin p))
    (hL : L.card = k + 1)
    {i : Fin p}
    (hi : i ∈ L) :
    let U :=
      ⋂ j : {j : Fin p // j ∈ L},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
          (Fin.castLE hp j.1)
    let B := convexHull ℝ (binary_prefix_points_on_subset hp P L)
    U ∩ {x : Fin n → ℝ | 0 < x (Fin.castLE hp i) ∧ x (Fin.castLE hp i) < 1} ⊆ B := by
  dsimp
  intro x hx
  rcases hx with ⟨hxU, hxStrip⟩
  -- Route correction: finish the strict-strip case from a named boundary pair instead of
  -- re-running the split-polyhedron transport in the visible wrapper.
  rcases predecessorFamily_strictStrip_hasBoundaryPair
      hp P hP_subset L hL hi hxU hxStrip.1 hxStrip.2 with
    ⟨x0, x1, hx0, hx1, hxEq⟩
  have hBconvex : Convex ℝ (convexHull ℝ (binary_prefix_points_on_subset hp P L)) :=
    convex_convexHull ℝ _
  have hLeft : 0 ≤ 1 - x (Fin.castLE hp i) := by
    linarith [hxStrip.2]
  have hRight : 0 ≤ x (Fin.castLE hp i) := hxStrip.1.le
  have hSum : (1 - x (Fin.castLE hp i)) + x (Fin.castLE hp i) = 1 := by ring
  rw [hxEq]
  exact hBconvex hx0.1 hx1.1 hLeft hRight hSum

/-- Helper for Exercise 5.25: the predecessor-family coordinate hulls on a fixed `(k + 1)`-subset
recover the hull that is binary on the whole subset. -/
private lemma binaryPrefixHull_predecessorFamilyStep
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box hp)
    {k : ℕ}
    (L : Finset (Fin p))
    (hL : L.card = k + 1) :
    (⋂ j : {j : Fin p // j ∈ L},
      coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
        (Fin.castLE hp j.1)) =
    convexHull ℝ (binary_prefix_points_on_subset hp P L) := by
  let U :=
    ⋂ j : {j : Fin p // j ∈ L},
      coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
        (Fin.castLE hp j.1)
  let B := convexHull ℝ (binary_prefix_points_on_subset hp P L)
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    have hLpos : 0 < L.card := by simpa [hL]
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hLpos
    have hxAll :
        ∀ j : {j : Fin p // j ∈ L},
          x ∈ coordinate_lift_project_hull
            (convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase j.1)))
            (Fin.castLE hp j.1) := by
      simpa only [Set.mem_iInter] using hx
    have hxFactor := hxAll ⟨i, hi⟩
    -- Every predecessor factor normalizes to `B`; one factor suffices for this inclusion.
    rw [binaryPrefixHull_erase_coordinateHull_eq hp P hP_subset hi] at hxFactor
    exact hxFactor
  · -- The easy direction is factorwise monotonicity from the full `L`-binary hull.
    exact binaryPrefixHull_subset_predecessorFamilyIntersection hp P L hL

/-- Helper for Exercise 5.25: if the two boundary slices of `A` along coordinate `i` already lie
in a convex target `B`, then the whole `i`-coordinate lift-project hull of `A` lies in `B`. -/
private lemma coordinateLiftProjectHull_subset_ofBoundarySubsets
    {A B : Set (Fin n → ℝ)}
    (i : Fin n)
    (hZero : A ∩ {x : Fin n → ℝ | x i = 0} ⊆ B)
    (hOne : A ∩ {x : Fin n → ℝ | x i = 1} ⊆ B)
    (hB_convex : Convex ℝ B) :
    coordinate_lift_project_hull A i ⊆ B := by
  -- Unfold the coordinate hull once and send each boundary branch into the convex target.
  rw [coordinate_lift_project_hull_def]
  refine convexHull_min ?_ hB_convex
  intro x hx
  rcases hx with hx | hx
  · exact hZero hx
  · exact hOne hx

/-- Helper for Exercise 5.25: applying the same coordinate lift-project operator twice does not
change the set. -/
private lemma coordinateLiftProjectHull_idempotent
    (A : Set (Fin n → ℝ))
    (i : Fin n) :
    coordinate_lift_project_hull (coordinate_lift_project_hull A i) i =
      coordinate_lift_project_hull A i := by
  let U : Set (Fin n → ℝ) :=
    (A ∩ {x : Fin n → ℝ | x i = 0}) ∪ (A ∩ {x : Fin n → ℝ | x i = 1})
  have hU_bounds : ∀ x ∈ U, 0 ≤ x i ∧ x i ≤ 1 := by
    intro x hx
    rcases hx with hx | hx
    · constructor <;> linarith [hx.2.symm]
    · constructor <;> linarith [hx.2.symm]
  have hU_boundary :
      (U ∩ {x : Fin n → ℝ | x i = 0}) ∪
          (U ∩ {x : Fin n → ℝ | x i = 1}) = U := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxU, -⟩ | ⟨hxU, -⟩
      · exact hxU
      · exact hxU
    · intro hxU
      rcases hxU with hx0 | hx1
      · exact Or.inl ⟨Or.inl hx0, hx0.2⟩
      · exact Or.inr ⟨Or.inr hx1, hx1.2⟩
  have hcoord :
      coordinate_lift_project_hull A i = convexHull ℝ U := by
    rw [coordinate_lift_project_hull_def]
  -- Route correction: expose the generating boundary union `U` once and use the generic
  -- same-coordinate normalization on `convexHull ℝ U`.
  calc
    coordinate_lift_project_hull (coordinate_lift_project_hull A i) i
        = coordinate_lift_project_hull (convexHull ℝ U) i := by
            rw [hcoord]
    _ = convexHull ℝ ((U ∩ {x : Fin n → ℝ | x i = 0}) ∪
          (U ∩ {x : Fin n → ℝ | x i = 1})) := by
          exact coordinateLiftProjectHull_convexHull_eq_ofCoordinateBounds U i hU_bounds
    _ = convexHull ℝ U := by rw [hU_boundary]
    _ = coordinate_lift_project_hull A i := by
          simpa [hcoord] using hcoord.symm

/-- Helper for Exercise 5.25: slicing a coordinate lift-project hull on its own `0`-boundary
recovers the convex hull of the original `0`-slice. -/
private lemma coordinateLiftProjectHull_inter_coordinateZero
    (A : Set (Fin n → ℝ))
    (i : Fin n) :
    coordinate_lift_project_hull A i ∩ {x : Fin n → ℝ | x i = 0} =
      convexHull ℝ (A ∩ {x : Fin n → ℝ | x i = 0}) := by
  let πi : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i
  let U : Set (Fin n → ℝ) :=
    (A ∩ {x : Fin n → ℝ | x i = 0}) ∪ (A ∩ {x : Fin n → ℝ | x i = 1})
  have hpreimageZero :
      (-πi) ⁻¹' ({0} : Set ℝ) = {x : Fin n → ℝ | x i = 0} := by
    ext x
    simp [πi]
  have hU_nonpos : U ⊆ (-πi) ⁻¹' Set.Iic (0 : ℝ) := by
    intro x hx
    rcases hx with hx | hx
    · have hxi0 : x i = 0 := by simpa using hx.2
      have hxi_nonneg : 0 ≤ x i := by simpa [hxi0]
      simpa [πi, LinearMap.proj_apply] using neg_nonpos.mpr hxi_nonneg
    · have hxi1 : x i = 1 := by simpa using hx.2
      have hxi_nonneg : 0 ≤ x i := by simpa [hxi1]
      simpa [πi, LinearMap.proj_apply] using neg_nonpos.mpr hxi_nonneg
  -- Reduce the slice to a hyperplane section of the generating boundary union.
  calc
    coordinate_lift_project_hull A i ∩ {x : Fin n → ℝ | x i = 0}
        = convexHull ℝ U ∩ {x : Fin n → ℝ | x i = 0} := by
            rw [coordinate_lift_project_hull_def]
    _ = convexHull ℝ U ∩ (-πi) ⁻¹' ({0} : Set ℝ) := by
          rw [hpreimageZero]
    _ = convexHull ℝ (U ∩ (-πi) ⁻¹' ({0} : Set ℝ)) :=
          convexHull_inter_hyperplane_eq U (-πi) (0 : ℝ) hU_nonpos
    _ = convexHull ℝ (U ∩ {x : Fin n → ℝ | x i = 0}) := by
          rw [hpreimageZero]
    _ = convexHull ℝ (A ∩ {x : Fin n → ℝ | x i = 0}) := by
          refine congrArg (convexHull ℝ) ?_
          ext x
          constructor
          · rintro ⟨hxU, hxi0⟩
            rcases hxU with hx | hx
            · exact ⟨hx.1, hx.2⟩
            · exfalso
              have hx1 : x i = 1 := by simpa using hx.2
              have hx0 : x i = 0 := by simpa using hxi0
              have : (1 : ℝ) = 0 := by rw [← hx1, hx0]
              norm_num at this
          · intro hx
            exact ⟨Or.inl hx, hx.2⟩

/-- Helper for Exercise 5.25: slicing a coordinate lift-project hull on its own `1`-boundary
recovers the convex hull of the original `1`-slice. -/
private lemma coordinateLiftProjectHull_inter_coordinateOne
    (A : Set (Fin n → ℝ))
    (i : Fin n) :
    coordinate_lift_project_hull A i ∩ {x : Fin n → ℝ | x i = 1} =
      convexHull ℝ (A ∩ {x : Fin n → ℝ | x i = 1}) := by
  let πi : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i
  let U : Set (Fin n → ℝ) :=
    (A ∩ {x : Fin n → ℝ | x i = 0}) ∪ (A ∩ {x : Fin n → ℝ | x i = 1})
  have hpreimageOne :
      πi ⁻¹' ({1} : Set ℝ) = {x : Fin n → ℝ | x i = 1} := by
    ext x
    simp [πi]
  have hU_le_one : U ⊆ πi ⁻¹' Set.Iic (1 : ℝ) := by
    intro x hx
    rcases hx with hx | hx
    · have hxi0 : x i = 0 := by simpa using hx.2
      have hxi_le_one : x i ≤ 1 := by simpa [hxi0]
      simpa [πi, LinearMap.proj_apply] using hxi_le_one
    · have hxi1 : x i = 1 := by simpa using hx.2
      have hxi_le_one : x i ≤ 1 := by simpa [hxi1]
      simpa [πi, LinearMap.proj_apply] using hxi_le_one
  -- The upper boundary slice is handled by the same hyperplane-section theorem at level `1`.
  calc
    coordinate_lift_project_hull A i ∩ {x : Fin n → ℝ | x i = 1}
        = convexHull ℝ U ∩ {x : Fin n → ℝ | x i = 1} := by
            rw [coordinate_lift_project_hull_def]
    _ = convexHull ℝ U ∩ πi ⁻¹' ({1} : Set ℝ) := by
          rw [hpreimageOne]
    _ = convexHull ℝ (U ∩ πi ⁻¹' ({1} : Set ℝ)) :=
          convexHull_inter_hyperplane_eq U πi (1 : ℝ) hU_le_one
    _ = convexHull ℝ (U ∩ {x : Fin n → ℝ | x i = 1}) := by
          rw [hpreimageOne]
    _ = convexHull ℝ (A ∩ {x : Fin n → ℝ | x i = 1}) := by
          refine congrArg (convexHull ℝ) ?_
          ext x
          constructor
          · rintro ⟨hxU, hxi1⟩
            rcases hxU with hx | hx
            · exfalso
              have hx0 : x i = 0 := by simpa using hx.2
              have hx1 : x i = 1 := by simpa using hxi1
              have : (0 : ℝ) = 1 := by rw [← hx0, hx1]
              norm_num at this
            · exact ⟨hx.1, hx.2⟩
          · intro hx
            exact ⟨Or.inr hx, hx.2⟩

/-- Helper for Exercise 5.25: the restricted `(k + 1)`-subset family lies in every
`i`-coordinate hull attached to a `k`-subset factor. -/
private lemma restrictedBinaryPrefixHull_subset_iInterCoordinateHulls
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k + 1 ≤ p)
    (i : Fin p) :
    (⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1)) ⊆
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i) := by
  intro x hx
  have hxRk :
      x ∈ ⋂ J : {J : Finset (Fin p) // J.card = k},
        convexHull ℝ (binary_prefix_points_on_subset hp P J.1) :=
    restrictedBinaryPrefixHull_subset_predecessorFamily hp P hk i hx
  -- Route correction: reduce the restricted family to factorwise `i`-coordinate hull membership
  -- before facing the remaining global commuting step.
  simp only [Set.mem_iInter] at hx hxRk ⊢
  intro J
  by_cases hiJ : i ∈ J.1
  · have hxJ :
        x ∈ convexHull ℝ (binary_prefix_points_on_subset hp P J.1) :=
      hxRk J
    simpa [binaryPrefixHull_fixedByCoordinateHull hp P hiJ] using hxJ
  · have hxInsert :
        x ∈ convexHull ℝ (binary_prefix_points_on_subset hp P (insert i J.1)) :=
      hx ⟨insert i J.1, by simp [J.2, hiJ]⟩
    exact binaryPrefixHull_insert_subset_coordinateLiftProjectHull hp P i J.1 hiJ hxInsert

/-- Helper for Exercise 5.25: for a fixed coordinate `i`, the restricted `(k + 1)`-subset family
already lies in the `i`-coordinate lift-project hull of the global `k`-subset family. -/
private lemma iInterKSubsetCoordinateHulls_coordinateSlices
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (i : Fin p) :
    let Rk :=
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        convexHull ℝ (binary_prefix_points_on_subset hp P J.1)
    let Tk :=
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)
    (Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} ⊆
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) ∧
      (Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} ⊆
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
  dsimp
  constructor
  · intro x hx
    rcases hx with ⟨hxTk, hxi0⟩
    refine ⟨?_, hxi0⟩
    -- On the `x_i = 0` boundary, each factorwise coordinate hull collapses back to its source hull.
    simp only [Set.mem_iInter] at hxTk ⊢
    intro J
    have hxSlice :
        x ∈ coordinate_lift_project_hull
              (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
              (Fin.castLE hp i) ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} := ⟨hxTk J, hxi0⟩
    have hxBoundary :
        x ∈ convexHull ℝ
              (convexHull ℝ (binary_prefix_points_on_subset hp P J.1) ∩
                {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) := by
      simpa [coordinateLiftProjectHull_inter_coordinateZero
        (convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) (Fin.castLE hp i)] using hxSlice
    exact convexHull_min (by intro y hy; exact hy.1) (convex_convexHull ℝ _) hxBoundary
  · intro x hx
    rcases hx with ⟨hxTk, hxi1⟩
    refine ⟨?_, hxi1⟩
    -- The `x_i = 1` boundary reduces in the same way.
    simp only [Set.mem_iInter] at hxTk ⊢
    intro J
    have hxSlice :
        x ∈ coordinate_lift_project_hull
              (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
              (Fin.castLE hp i) ∩
            {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} := ⟨hxTk J, hxi1⟩
    have hxBoundary :
        x ∈ convexHull ℝ
              (convexHull ℝ (binary_prefix_points_on_subset hp P J.1) ∩
                {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
      simpa [coordinateLiftProjectHull_inter_coordinateOne
        (convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) (Fin.castLE hp i)] using hxSlice
    exact convexHull_min (by intro y hy; exact hy.1) (convex_convexHull ℝ _) hxBoundary

/-- Helper for Exercise 5.25: for the concrete `Rk`/`Tk` family, the `x_i = 0` and `x_i = 1`
boundary slices of the factorwise coordinate-hull intersection are exactly the corresponding
boundary slices of the original `k`-subset intersection. -/
private lemma iInterKSubsetCoordinateHulls_coordinateSlices_eq
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (i : Fin p) :
    let Rk :=
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        convexHull ℝ (binary_prefix_points_on_subset hp P J.1)
    let Tk :=
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)
    (Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} =
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0}) ∧
      (Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} =
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1}) := by
  dsimp
  constructor
  · apply Set.Subset.antisymm
    · exact (@iInterKSubsetCoordinateHulls_coordinateSlices n p hp P k i).1
    · rintro x ⟨hxRk, hxi0⟩
      refine ⟨?_, hxi0⟩
      -- On the `x_i = 0` boundary, each source factor enters its coordinate hull through the
      -- explicit `0`-branch of the defining union.
      simp only [Set.mem_iInter] at hxRk ⊢
      intro J
      rw [coordinate_lift_project_hull_def]
      apply subset_convexHull ℝ
      exact Or.inl ⟨hxRk J, hxi0⟩
  · apply Set.Subset.antisymm
    · exact (@iInterKSubsetCoordinateHulls_coordinateSlices n p hp P k i).2
    · rintro x ⟨hxRk, hxi1⟩
      refine ⟨?_, hxi1⟩
      -- The `x_i = 1` boundary enters every factor through the symmetric `1`-branch.
      simp only [Set.mem_iInter] at hxRk ⊢
      intro J
      rw [coordinate_lift_project_hull_def]
      apply subset_convexHull ℝ
      exact Or.inr ⟨hxRk J, hxi1⟩

/-- Helper for Exercise 5.25: the factorwise intersection of `i`-coordinate hulls is stable under
one more application of the same `i`-coordinate lift-project operator. -/
private lemma coordinateHull_iInterKSubsetCoordinateHulls_subset
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (i : Fin p) :
    coordinate_lift_project_hull
        (⋂ J : {J : Finset (Fin p) // J.card = k},
          coordinate_lift_project_hull
            (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
            (Fin.castLE hp i))
        (Fin.castLE hp i) ⊆
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i) := by
  intro x hx
  -- Compare the global factorwise intersection with each coordinate-hull factor separately.
  simp only [Set.mem_iInter] at hx ⊢
  intro J
  have hFamilySubset :
      (⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)) ⊆
      coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i) := by
    intro y hy
    have hyAll :
        ∀ J : {J : Finset (Fin p) // J.card = k},
          y ∈ coordinate_lift_project_hull
            (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
            (Fin.castLE hp i) := by
      simpa only [Set.mem_iInter] using hy
    exact hyAll J
  have hxFactor :
      x ∈ coordinate_lift_project_hull
        (coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i))
        (Fin.castLE hp i) :=
    coordinateLiftProjectHull_mono hFamilySubset (Fin.castLE hp i) hx
  simpa [coordinateLiftProjectHull_idempotent
    (convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) (Fin.castLE hp i)] using hxFactor

/-- Helper for Exercise 5.25: a strict-strip point of the factorwise `i`-coordinate-hull
intersection admits a boundary pair in the ambient `Rk` family. -/
private lemma iInterCoordinateHulls_strictStrip_hasBoundaryPair
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k ≤ p)
    (hkPos : 0 < k)
    (i : Fin p)
    (hCommute :
      (⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)) =
        coordinate_lift_project_hull
          (⋂ J : {J : Finset (Fin p) // J.card = k},
            convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)) :
    let Rk :=
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        convexHull ℝ (binary_prefix_points_on_subset hp P J.1)
    let Tk :=
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)
    ∀ ⦃x : Fin n → ℝ⦄,
      x ∈ Tk →
      0 < x (Fin.castLE hp i) →
      x (Fin.castLE hp i) < 1 →
      ∃ x0 x1 : Fin n → ℝ,
        x0 ∈ Rk ∩ {y : Fin n → ℝ | y (Fin.castLE hp i) = 0} ∧
        x1 ∈ Rk ∩ {y : Fin n → ℝ | y (Fin.castLE hp i) = 1} ∧
        x =
          (1 - x (Fin.castLE hp i)) • x0 +
            x (Fin.castLE hp i) • x1 := by
  dsimp
  intro x hxTk hxiPos hxiLtOne
  have hRkConvex :
      Convex ℝ
        (⋂ J : {J : Finset (Fin p) // J.card = k},
          convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) := by
    exact convex_iInter fun J ↦ convex_convexHull ℝ _
  have hxCoordinate :
      x ∈ coordinate_lift_project_hull
        (⋂ J : {J : Finset (Fin p) // J.card = k},
          convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i) := by
    rw [← hCommute]
    exact hxTk
  -- The explicit commutation premise puts the point in the coordinate hull of the convex
  -- intersection, where the generic boundary-pair lemma applies.
  exact coordinateLiftProjectHull_strictStrip_hasBoundaryPair
    hRkConvex (Fin.castLE hp i) hxCoordinate hxiPos hxiLtOne

/-- Helper for Exercise 5.25: the intersection of the factorwise `i`-coordinate hulls of the
`k`-subset family lands in the `i`-coordinate hull of the total `k`-subset intersection on the
strict strip. -/
private lemma iInterCoordinateHulls_strictStrip_subset_coordinateHull
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k ≤ p)
    (hkPos : 0 < k)
    (i : Fin p)
    (hCommute :
      (⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)) =
        coordinate_lift_project_hull
          (⋂ J : {J : Finset (Fin p) // J.card = k},
            convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)) :
    let Rk :=
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        convexHull ℝ (binary_prefix_points_on_subset hp P J.1)
    let Tk :=
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)
    Tk ∩ {x : Fin n → ℝ | 0 < x (Fin.castLE hp i) ∧ x (Fin.castLE hp i) < 1} ⊆
      coordinate_lift_project_hull Rk (Fin.castLE hp i) := by
  dsimp
  intro x hx
  rcases hx with ⟨hxTk, hxStrip⟩
  -- Route correction: consume the family-specific boundary pair directly and then finish inside
  -- `coordinate_lift_project_hull_def` by convexity of the generating boundary union.
  rcases iInterCoordinateHulls_strictStrip_hasBoundaryPair
      hp P hk hkPos i hCommute hxTk hxStrip.1 hxStrip.2 with
    ⟨x0, x1, hx0, hx1, hxEq⟩
  rw [coordinate_lift_project_hull_def]
  have hLeft : 0 ≤ 1 - x (Fin.castLE hp i) := by
    linarith [hxStrip.2]
  have hRight : 0 ≤ x (Fin.castLE hp i) := hxStrip.1.le
  have hSum : (1 - x (Fin.castLE hp i)) + x (Fin.castLE hp i) = 1 := by ring
  rw [hxEq]
  refine (convex_convexHull ℝ _) ?_ ?_ hLeft hRight hSum
  · exact subset_convexHull ℝ _ (Or.inl hx0)
  · exact subset_convexHull ℝ _ (Or.inr hx1)

/-- Helper for Exercise 5.25: the intersection of the factorwise `i`-coordinate hulls of the
`k`-subset family should land in the `i`-coordinate hull of the total `k`-subset intersection. -/
private lemma iInterKSubsetCoordinateHulls_subset_coordinateHullRk
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k ≤ p)
    (hkPos : 0 < k)
    (i : Fin p)
    (hCommute :
      (⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)) =
        coordinate_lift_project_hull
          (⋂ J : {J : Finset (Fin p) // J.card = k},
            convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)) :
    (⋂ J : {J : Finset (Fin p) // J.card = k},
      coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i)) ⊆
      coordinate_lift_project_hull
        (⋂ J : {J : Finset (Fin p) // J.card = k},
          convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i) := by
  let Rk :=
    ⋂ J : {J : Finset (Fin p) // J.card = k},
      convexHull ℝ (binary_prefix_points_on_subset hp P J.1)
  let Tk :=
    ⋂ J : {J : Finset (Fin p) // J.card = k},
      coordinate_lift_project_hull
        (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i)
  intro x hx
  have hSlices := @iInterKSubsetCoordinateHulls_coordinateSlices n p hp P k i
  have hSlicesEq := @iInterKSubsetCoordinateHulls_coordinateSlices_eq n p hp P k i
  have hZero :
      Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} ⊆
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} := by
    simpa [Rk, Tk] using hSlices.1
  have hOne :
      Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} ⊆
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} := by
    simpa [Rk, Tk] using hSlices.2
  have hTkStable :
      coordinate_lift_project_hull Tk (Fin.castLE hp i) ⊆ Tk := by
    simpa [Tk] using (@coordinateHull_iInterKSubsetCoordinateHulls_subset n p hp P k i)
  have hZeroEq :
      Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} =
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} := by
    simpa [Rk, Tk] using hSlicesEq.1
  have hOneEq :
      Tk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} =
        Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} := by
    simpa [Rk, Tk] using hSlicesEq.2
  by_cases hxi0 : x (Fin.castLE hp i) = 0
  · -- The lower boundary enters the target coordinate hull through the explicit `0`-branch.
    have hxBoundary :
        x ∈ Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 0} := by
      rw [← hZeroEq]
      exact ⟨hx, hxi0⟩
    rw [coordinate_lift_project_hull_def]
    exact subset_convexHull ℝ _ (Or.inl hxBoundary)
  by_cases hxi1 : x (Fin.castLE hp i) = 1
  · -- The upper boundary is symmetric.
    have hxBoundary :
        x ∈ Rk ∩ {x : Fin n → ℝ | x (Fin.castLE hp i) = 1} := by
      rw [← hOneEq]
      exact ⟨hx, hxi1⟩
    rw [coordinate_lift_project_hull_def]
    exact subset_convexHull ℝ _ (Or.inr hxBoundary)
  obtain ⟨J, hJcard, _hiJ⟩ := existsSubset_card_eq_mem hkPos hk i
  have hxAll :
      ∀ J' : {J : Finset (Fin p) // J.card = k},
        x ∈ coordinate_lift_project_hull
              (convexHull ℝ (binary_prefix_points_on_subset hp P J'.1))
              (Fin.castLE hp i) := by
    simpa [Tk, Set.mem_iInter] using hx
  have hxFactor :
      x ∈ coordinate_lift_project_hull
            (convexHull ℝ (binary_prefix_points_on_subset hp P J))
            (Fin.castLE hp i) := by
    exact hxAll ⟨J, hJcard⟩
  have hxiBounds :
      0 ≤ x (Fin.castLE hp i) ∧ x (Fin.castLE hp i) ≤ 1 :=
    coordinateLiftProjectHull_subset_coordinateStrip
      (convexHull ℝ (binary_prefix_points_on_subset hp P J)) (Fin.castLE hp i) hxFactor
  have hxiPos : 0 < x (Fin.castLE hp i) := by
    exact lt_of_le_of_ne hxiBounds.1 (by
      intro h
      exact hxi0 h.symm)
  have hxiLtOne : x (Fin.castLE hp i) < 1 := by
    exact lt_of_le_of_ne hxiBounds.2 hxi1
  have hxStrip :
      x ∈ Tk ∩ {x : Fin n → ℝ | 0 < x (Fin.castLE hp i) ∧ x (Fin.castLE hp i) < 1} :=
    ⟨hx, ⟨hxiPos, hxiLtOne⟩⟩
  -- Route correction: the boundary cases are finished above, so the only unresolved residue is
  -- the strict-strip transport packaged as its own helper.
  exact iInterCoordinateHulls_strictStrip_subset_coordinateHull
    hp P hk hkPos i hCommute hxStrip

/-- Helper for Exercise 5.25: for a fixed coordinate `i`, the restricted `(k + 1)`-subset family
already lies in the `i`-coordinate lift-project hull of the global `k`-subset family. -/
private lemma restrictedBinaryPrefixHull_subset_coordinateHullPredecessor
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    {k : ℕ}
    (hk : k + 1 ≤ p)
    (hkPos : 0 < k)
    (i : Fin p)
    (hCommute :
      (⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)) =
        coordinate_lift_project_hull
          (⋂ J : {J : Finset (Fin p) // J.card = k},
            convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i)) :
    (⋂ L : {L : Finset (Fin p) // L.card = k + 1 ∧ i ∈ L},
      convexHull ℝ (binary_prefix_points_on_subset hp P L.1)) ⊆
      coordinate_lift_project_hull
        (⋂ J : {J : Finset (Fin p) // J.card = k},
          convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i) := by
  intro x hx
  -- Route correction: the theorem only needs this direct bridge into the ambient `i`-coordinate
  -- hull of `Rk`, not a full fixed-point equality for the restricted family itself.
  have hxFactorwise :
      x ∈ ⋂ J : {J : Finset (Fin p) // J.card = k},
        coordinate_lift_project_hull
          (convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
          (Fin.castLE hp i) :=
    restrictedBinaryPrefixHull_subset_iInterCoordinateHulls hp P hk i hx
  -- Reduce the goal to the family-specific closing lemma for the factorwise `i`-coordinate hulls.
  exact iInterKSubsetCoordinateHulls_subset_coordinateHullRk
    hp P (Nat.le_of_succ_le hk) hkPos i hCommute hxFactorwise

/-- Helper for Exercise 5.25: one coordinate convexification of the global `k`-subset
intersection lies in the binary hull of any `(k + 1)`-subset containing that coordinate. -/
private lemma coordinateHull_kSubsetIntersection_subset_binaryPrefixHull
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_subset : P ⊆ prefix_unit_box hp)
    {k : ℕ}
    {L : Finset (Fin p)}
    (hL : L.card = k + 1)
    {i : Fin p}
    (hi : i ∈ L) :
    coordinate_lift_project_hull
        (⋂ J : {J : Finset (Fin p) // J.card = k},
          convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
        (Fin.castLE hp i) ⊆
      convexHull ℝ (binary_prefix_points_on_subset hp P L) := by
  have hEraseCard : (L.erase i).card = k := by
    rw [Finset.card_erase_of_mem hi, hL]
    omega
  have hIntersectionSubset :
      (⋂ J : {J : Finset (Fin p) // J.card = k},
        convexHull ℝ (binary_prefix_points_on_subset hp P J.1)) ⊆
        convexHull ℝ (binary_prefix_points_on_subset hp P (L.erase i)) := by
    intro x hx
    have hxAll :
        ∀ J : {J : Finset (Fin p) // J.card = k},
          x ∈ convexHull ℝ (binary_prefix_points_on_subset hp P J.1) := by
      simpa only [Set.mem_iInter] using hx
    exact hxAll ⟨L.erase i, hEraseCard⟩
  -- Monotonicity reduces the global intersection to the erased factor, which normalizes exactly.
  intro x hx
  have hxErased :=
    coordinateLiftProjectHull_mono hIntersectionSubset (Fin.castLE hp i) hx
  rw [binaryPrefixHull_erase_coordinateHull_eq hp P hP_subset hi] at hxErased
  exact hxErased

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap05/section_5_6/ch5_sec5_6_exercise_5_25.lean
Exercise 5.25. Let `P ⊆ ℝ^n` be a polyhedron contained in the unit box on the first `p`
coordinates, and let
`S := P ∩ ({0, 1}^p × ℝ^(n - p))`. Then the `k`th lift-and-project closure of `P` along the first
`p` coordinates is contained in the intersection, over all `k`-element subsets `J` of the binary
index set, of the convex hull of the points of `P` whose coordinates indexed by `J` are binary. -/
theorem kth_lift_project_closure_subset_iInter_convexHull_binary_on_k_subsets
    (hp : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_subset : P ⊆ prefix_unit_box hp)
    (k : ℕ)
    (hk : k ≤ p) :
    kth_lift_project_closure hp P k ⊆
      ⋂ J : {J : Finset (Fin p) // J.card = k},
        convexHull ℝ (binary_prefix_points_on_subset hp P J.1) := by
  induction k with
  | zero =>
      -- At rank zero both sides reduce to the original convex polyhedron `P`.
      rw [kth_lift_project_closure_zero,
        iInter_convexHull_binary_on_zero_subsets hp P hP_polyhedron]
  | succ k ih =>
      have hkPrev : k ≤ p := Nat.le_of_succ_le hk
      rw [kth_lift_project_closure_succ]
      intro x hx
      have hxEach :
          ∀ i : Fin p,
            x ∈ coordinate_lift_project_hull
              (kth_lift_project_closure hp P k) (Fin.castLE hp i) :=
        (mem_prefix_lift_project_closure_iff
          hp (kth_lift_project_closure hp P k) x).mp hx
      simp only [Set.mem_iInter]
      intro L
      have hLPos : 0 < L.1.card := by
        rw [L.2]
        omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hLPos
      have hxIntersection :
          x ∈ coordinate_lift_project_hull
            (⋂ J : {J : Finset (Fin p) // J.card = k},
              convexHull ℝ (binary_prefix_points_on_subset hp P J.1))
            (Fin.castLE hp i) :=
        coordinateLiftProjectHull_mono (ih hkPrev) (Fin.castLE hp i) (hxEach i)
      -- Erase `i` from `L`, apply the induction invariant, and normalize the resulting factor.
      exact coordinateHull_kSubsetIntersection_subset_binaryPrefixHull
        hp P hP_subset L.2 hi hxIntersection

end Exercise525
