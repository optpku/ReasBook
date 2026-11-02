import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_28
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4.ch5_sec5_4_definition_5_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_claim_5_4_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_zero_one_points

open scoped Matrix
open scoped CoordinateLiftProjectNotation

-- This file keeps the source-facing sequential-convexification recursion and binary-point sets,
-- while reusing the Chapter 3 polyhedron owner `is_polyhedron` and the Chapter 5 split-step
-- owner `coordinate_lift_project_hull`.

section Theorem522

variable {n p : ℕ}

/-- The `t`th sequential convexification of `P`, obtained by successively convexifying along the
first `t` coordinates. -/
private def sequentialConvexificationIterAux
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    (t : ℕ)
    (ht : t ≤ p) : Set (Fin n → ℝ) :=
  match t with
  | 0 => P
  | t + 1 =>
      (sequentialConvexificationIterAux hpn P t (Nat.le_of_succ_le ht))_{
        Fin.castLE hpn ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩}
termination_by t

/-- The `t`th sequential convexification of `P`, obtained by successively convexifying along the
first `t` coordinates. -/
def sequential_convexification_iter
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    {t : ℕ}
    (ht : t ≤ p) : Set (Fin n → ℝ) :=
  sequentialConvexificationIterAux hpn P t ht

/-- The zeroth sequential convexification of `P` is `P` itself. -/
theorem sequential_convexification_iter_zero
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    sequential_convexification_iter hpn P (Nat.zero_le p) = P :=
  by
    simp [sequential_convexification_iter, sequentialConvexificationIterAux]

/-- The successor sequential convexification is obtained by convexifying the previous iterate
along the next coordinate. -/
theorem sequential_convexification_iter_succ
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    {t : ℕ}
    (ht : t + 1 ≤ p) :
    sequential_convexification_iter hpn P ht =
      (sequential_convexification_iter hpn P (Nat.le_of_succ_le ht))_{
        Fin.castLE hpn ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩} :=
  by
    simp [sequential_convexification_iter, sequentialConvexificationIterAux]

/-- Helper for Theorem 5.22: when no coordinates are forced to be binary, the prefix-binary set is
just `P`. -/
private lemma prefix_binary_points_zero_eq_self
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ)) :
    prefix_binary_points hpn P (Nat.zero_le p) = P := by
  -- There are no coordinates in `Fin 0`, so the binary-side condition is vacuous.
  ext x
  simp [prefix_binary_points]

/-- Helper for Theorem 5.22: the `(t + 1)`-prefix binary points are exactly the previous
prefix-binary points cut by the next coordinate being `0` or `1`. -/
private lemma prefix_binary_points_succ_eq_union_coordinate_slices
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    {t : ℕ}
    (ht : t + 1 ≤ p) :
    prefix_binary_points hpn P ht =
      ((prefix_binary_points hpn P (Nat.le_of_succ_le ht)) ∩
          {x : Fin n → ℝ |
            x (Fin.castLE hpn ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩) = 0}) ∪
        ((prefix_binary_points hpn P (Nat.le_of_succ_le ht)) ∩
          {x : Fin n → ℝ |
            x (Fin.castLE hpn ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩) = 1}) := by
  let j : Fin n := Fin.castLE hpn ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩
  ext x
  constructor
  · intro hx
    rw [mem_prefix_binary_points_iff] at hx
    -- Restrict the binary conditions from the first `t + 1` coordinates to the first `t`.
    have hprev : x ∈ prefix_binary_points hpn P (Nat.le_of_succ_le ht) := by
      rw [mem_prefix_binary_points_iff]
      refine ⟨hx.1, ?_⟩
      intro k
      simpa using hx.2 ⟨k.1, Nat.lt_succ_of_lt k.2⟩
    -- The last binary condition is exactly the `j`th-coordinate slice.
    have hnext : x j = 0 ∨ x j = 1 := by
      simpa [j] using hx.2 ⟨t, Nat.lt_succ_self t⟩
    rcases hnext with hnext | hnext
    · exact Or.inl ⟨hprev, hnext⟩
    · exact Or.inr ⟨hprev, hnext⟩
  · -- Reassemble the `t + 1` binary conditions from the previous stage and the new slice.
    have hfinish
        (hprev : x ∈ prefix_binary_points hpn P (Nat.le_of_succ_le ht))
        (hnext : x j = 0 ∨ x j = 1) :
        x ∈ prefix_binary_points hpn P ht := by
      rw [mem_prefix_binary_points_iff]
      rw [mem_prefix_binary_points_iff] at hprev
      refine ⟨hprev.1, ?_⟩
      intro k
      have hkle : k.1 ≤ t := Nat.le_of_lt_succ k.2
      by_cases hk : k.1 = t
      · have hk' : k = ⟨t, Nat.lt_succ_self t⟩ := Fin.ext hk
        simpa [j, hk'] using hnext
      · have hklt : k.1 < t := lt_of_le_of_ne hkle hk
        simpa using hprev.2 ⟨k.1, hklt⟩
    intro hx
    rcases hx with ⟨hprev, hx0⟩ | ⟨hprev, hx1⟩
    · exact hfinish hprev (Or.inl hx0)
    · exact hfinish hprev (Or.inr hx1)

/-- Helper for Theorem 5.22: if every point of `A` has `j`th coordinate in `[0, 1]`, then the
coordinate lift-project hull of `convexHull ℝ A` is the convex hull of the `j = 0` and `j = 1`
slices of `A`. -/
private lemma coordinate_lift_project_hull_convexHull_eq_of_coordinate_bounds
    {n : ℕ}
    (A : Set (Fin n → ℝ))
    (j : Fin n)
    (hA_bounds : ∀ x ∈ A, 0 ≤ x j ∧ x j ≤ 1) :
    coordinate_lift_project_hull (convexHull ℝ A) j =
      convexHull ℝ
        ((A ∩ {x : Fin n → ℝ | x j = 0}) ∪
          (A ∩ {x : Fin n → ℝ | x j = 1})) := by
  let πj : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) j
  have hpreimageZero : (-πj) ⁻¹' ({0} : Set ℝ) = {x : Fin n → ℝ | x j = 0} := by
    ext x
    simp [πj]
  have hpreimageOne : πj ⁻¹' ({1} : Set ℝ) = {x : Fin n → ℝ | x j = 1} := by
    ext x
    simp [πj]
  -- Route correction: rather than unfold the whole induction step, first identify the two
  -- hyperplane slices of `convexHull ℝ A` via the boundary-slice theorem.
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
  -- After replacing each slice by the convex hull of its generators, collapse the nested hulls.
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

/-- Theorem 5.22 (1) (Sequential Convexification Theorem, Balas [24]). Let
`P ⊆ {x ∈ ℝ^n | 0 ≤ x_j ≤ 1 for j = 1, …, p}` be a polyhedron. Then for each `t ≤ p`,
the `t`th sequential convexification of `P` is the convex hull of the points of `P` whose first
`t` coordinates are binary. For `t = 0`, both sides are `P` because polyhedra are convex. -/
theorem sequential_convexification_iter_eq_convexHull_prefix_binary_points
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_subset : P ⊆ prefix_unit_box hpn)
    {t : ℕ}
    (ht : t ≤ p) :
    sequential_convexification_iter hpn P ht =
      convexHull ℝ (prefix_binary_points hpn P ht) := by
  induction t with
  | zero =>
      -- The zeroth iterate is `P`, and polyhedra are convex, so taking the convex hull does
      -- nothing.
      have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP_polyhedron
      simpa [sequential_convexification_iter_zero, prefix_binary_points_zero_eq_self] using
        (Convex.convexHull_eq hP_convex).symm
  | succ t ih =>
      let j : Fin n := Fin.castLE hpn ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩
      have hprefixBounds :
          ∀ x ∈ prefix_binary_points hpn P (Nat.le_of_succ_le ht), 0 ≤ x j ∧ x j ≤ 1 := by
        intro x hx
        have hxP : x ∈ P := (mem_prefix_binary_points_iff hpn P (Nat.le_of_succ_le ht) x).mp hx |>.1
        have hxBox : x ∈ prefix_unit_box hpn := hP_subset hxP
        exact (mem_prefix_unit_box_iff hpn x).mp hxBox
          ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) ht⟩
      -- Route correction: follow the recursive convexification step, insert the induction
      -- hypothesis once, and use the slice-interface lemmas instead of unfolding the construction.
      calc
        sequential_convexification_iter hpn P ht
            = (sequential_convexification_iter hpn P (Nat.le_of_succ_le ht))_{j} := by
                simpa [j] using sequential_convexification_iter_succ hpn P ht
        _ = (convexHull ℝ (prefix_binary_points hpn P (Nat.le_of_succ_le ht)))_{j} := by
              rw [ih (Nat.le_of_succ_le ht)]
        _ = convexHull ℝ
              ((prefix_binary_points hpn P (Nat.le_of_succ_le ht) ∩
                  {x : Fin n → ℝ | x j = 0}) ∪
                (prefix_binary_points hpn P (Nat.le_of_succ_le ht) ∩
                  {x : Fin n → ℝ | x j = 1})) := by
              exact coordinate_lift_project_hull_convexHull_eq_of_coordinate_bounds
                (prefix_binary_points hpn P (Nat.le_of_succ_le ht)) j hprefixBounds
        _ = convexHull ℝ (prefix_binary_points hpn P ht) := by
              rw [← prefix_binary_points_succ_eq_union_coordinate_slices hpn P ht]

/-- Theorem 5.22 (2) (Sequential Convexification Theorem, Balas [24]). With
`S = {x ∈ P : x_j ∈ {0,1} for j = 1, …, p}`, the final sequential convexification satisfies
`(P)^p = conv(S)`. -/
theorem sequential_convexification_iter_eq_convexHull_zero_one_points
    (hpn : p ≤ n)
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hP_subset : P ⊆ prefix_unit_box hpn) :
    sequential_convexification_iter hpn P (Nat.le_refl p) =
      convexHull ℝ (zero_one_points hpn P) := by
  calc
    sequential_convexification_iter hpn P (Nat.le_refl p)
        = convexHull ℝ (prefix_binary_points hpn P (Nat.le_refl p)) :=
          sequential_convexification_iter_eq_convexHull_prefix_binary_points
            hpn P hP_polyhedron hP_subset (Nat.le_refl p)
    _ = convexHull ℝ (zero_one_points hpn P) := by
        rw [prefix_binary_points_full_eq_zero_one_points]

end Theorem522
