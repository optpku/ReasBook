/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_example_3_29

open scoped BigOperators

-- This exercise reuses the canonical Section 3.9 subset-sum API for the permutahedron and then
-- adds the vertex-incident facet count specific to Exercise 3.23.

/-- Helper for Exercise 3.23: an extreme point of the permutahedron is one of the permutation
vertices of `ascending_vector n`. -/
lemma extreme_point_eq_permuted_ascending_vector
    {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ (permutahedron n).extremePoints ℝ) :
    ∃ σ : Equiv.Perm (Fin n), x = ascending_vector n ∘ σ := by
  -- Extreme points of the defining convex hull come from the generating vertex set.
  have hx_vertices : x ∈ permutahedron_vertices n := by
    rw [permutahedron_eq_convexHull] at hx
    exact extremePoints_convexHull_subset hx
  exact mem_permutahedron_vertices_iff.mp hx_vertices

/-- Helper for Exercise 3.23: the first `m` positions in the `σ`-order, viewed as indices of the
ambient coordinate set. -/
def prefix_set {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n) : Finset (Fin n) :=
  Finset.univ.image fun j : Fin m ↦ σ.symm (Fin.castLE hm j)

/-- Helper for Exercise 3.23: the prefix set indexed by `m` has exactly `m` elements. -/
lemma prefix_set_card {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n) :
    (prefix_set σ m hm).card = m := by
  -- The image description makes the cardinality computation immediate.
  unfold prefix_set
  simpa using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin m))
      (σ.symm.injective.comp (Fin.castLE_injective hm))

/-- Helper for Exercise 3.23: reindexing a prefix-set sum through the first `m` positions in the
`σ`-order. -/
lemma sum_prefix_set_eq_sum_ordered
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n) (y : Fin n → ℝ) :
    ∑ i ∈ prefix_set σ m hm, y i = ∑ j : Fin m, y (σ.symm (Fin.castLE hm j)) := by
  classical
  have h_injOn :
      Set.InjOn (fun j : Fin m ↦ σ.symm (Fin.castLE hm j))
        ↑(Finset.univ : Finset (Fin m)) :=
    (σ.symm.injective.comp (Fin.castLE_injective hm)).injOn
  -- Unfold the image description and reindex the finite sum by the ordered positions.
  unfold prefix_set
  simpa using
    (Finset.sum_image
      (s := (Finset.univ : Finset (Fin m)))
      (f := fun i : Fin n ↦ y i)
      (g := fun j : Fin m ↦ σ.symm (Fin.castLE hm j))
      h_injOn)

/-- Helper for Exercise 3.23: summing the permutation vertex over a prefix set gives the expected
triangular number. -/
lemma sum_prefix_set_values
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n) :
    ∑ i ∈ prefix_set σ m hm, (ascending_vector n ∘ σ) i =
      (Nat.choose (m + 1) 2 : ℝ) := by
  -- Rewrite the prefix-set sum as a sum over the first `m` ordered positions.
  calc
    ∑ i ∈ prefix_set σ m hm, (ascending_vector n ∘ σ) i
        = ∑ j : Fin m, (ascending_vector n ∘ σ) (σ.symm (Fin.castLE hm j)) := by
            simpa using
              sum_prefix_set_eq_sum_ordered σ m hm (ascending_vector n ∘ σ)
    _ = ∑ j : Fin m, (((j : ℕ) : ℝ) + 1) := by
      -- Applying `σ` to `σ.symm` reduces the value back to the initial segment.
      simp [ascending_vector]
    _ = (Nat.choose (m + 1) 2 : ℝ) := sum_univ_initial_segment_eq_choose m

/-- Helper for Exercise 3.23: reindex the dot product through the `σ`-ordered coordinates. -/
lemma dotProduct_eq_sum_ordered_symm
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (c y : Fin n → ℝ) :
    c ⬝ᵥ y = ∑ j : Fin n, c (σ.symm j) * y (σ.symm j) := by
  -- Reindex the dot product through the permutation order so later gap arguments can telescope.
  calc
    c ⬝ᵥ y = ∑ i : Fin n, c i * y i := by
      simp [dotProduct]
    _ = ∑ j : Fin n, c (σ.symm j) * y (σ.symm j) := by
      simpa using
        (Equiv.sum_comp (e := σ.symm) (g := fun i : Fin n ↦ c i * y i)).symm

/-- Helper for Exercise 3.23: every nonempty prefix set is nonempty as a finset. -/
lemma prefix_set_nonempty
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n) (h0 : 0 < m) :
    (prefix_set σ m hm).Nonempty := by
  let j : Fin m := ⟨0, h0⟩
  have hj_mem : σ.symm (Fin.castLE hm j) ∈ prefix_set σ m hm := by
    -- The chosen initial index is visibly in the image defining the prefix set.
    unfold prefix_set
    refine Finset.mem_image.mpr ?_
    refine ⟨j, ?_⟩
    simp [j]
  exact ⟨σ.symm (Fin.castLE hm j), hj_mem⟩

/-- Helper for Exercise 3.23: a nonempty proper subset-sum equality face of the permutahedron is a
facet in the Section 3.18 `IsFacetOf` sense. -/
lemma subset_sum_face_isFacetOf
    {n : ℕ} (K : Finset (Fin n)) (hK_nonempty : K.Nonempty) (hK_proper : K.card < n)
    {x : Fin n → ℝ}
    (hx :
      x ∈ face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ))) :
    IsFacetOf (permutahedron n)
      (face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ))) := by
  -- Repackage the canonical Section 3.9 facet description in the local `IsFacetOf` owner.
  have h_nonempty :
      (face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ))).Nonempty := ⟨x, hx⟩
  -- Convert the defining equality slice into an exposed face coming from the valid inequality.
  have h_exposed :
      IsExposed ℝ (permutahedron n)
        (face_set (permutahedron n) (-subsetSumIndicator K)
          (-(Nat.choose (K.card + 1) 2 : ℝ))) := by
    rw [face_set_eq_toExposed_of_mem
      (permutahedron_subset_sum_is_valid_inequality n K) hx]
    exact ContinuousLinearMap.toExposed.isExposed
  have h_dim :
      Module.finrank ℝ
        (affineSpan ℝ
          (face_set (permutahedron n) (-subsetSumIndicator K)
            (-(Nat.choose (K.card + 1) 2 : ℝ)))).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ (permutahedron n)).direction := by
    -- The subset-sum face has dimension `n - 2`, while the permutahedron has dimension `n - 1`.
    have hn_two : 2 ≤ n := by
      have hK_pos : 0 < K.card := Finset.card_pos.mpr hK_nonempty
      omega
    rw [permutahedron_subset_sum_face_finrank_direction_affineSpan n K hK_nonempty hK_proper,
      permutahedron_finrank_direction_affineSpan n]
    omega
  exact ⟨h_nonempty, h_exposed, h_dim⟩

/-- Helper for Exercise 3.23: each nontrivial prefix set defines a subset-sum face containing the
permutation vertex `ascending_vector n ∘ σ`. -/
lemma mem_prefix_subset_sum_face_of_permuted_vertex
    {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hmn : m < n) :
    let hm := Nat.le_of_lt hmn
    ascending_vector n ∘ σ ∈
      face_set (permutahedron n) (-subsetSumIndicator (prefix_set σ m hm))
        (-(Nat.choose ((prefix_set σ m hm).card + 1) 2 : ℝ)) := by
  let hm : m ≤ n := Nat.le_of_lt hmn
  -- First place the permutation vertex in the permutahedron itself.
  have hx_perm : ascending_vector n ∘ σ ∈ permutahedron n := by
    rw [permutahedron_eq_convexHull]
    exact subset_convexHull ℝ (permutahedron_vertices n)
      (mem_permutahedron_vertices_iff.mpr ⟨σ, rfl⟩)
  -- Then compute the tight subset-sum equality on the chosen prefix set.
  rw [mem_permutahedron_subset_sum_face_iff]
  refine ⟨hx_perm, ?_⟩
  simpa [prefix_set_card σ m hm] using sum_prefix_set_values σ m hm

/-- Helper for Exercise 3.23: every nontrivial prefix split of a permutation vertex gives an
incident facet of the permutahedron. -/
lemma prefix_face_incident
    {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (h0 : 0 < m) (hmn : m < n) :
    let hm := Nat.le_of_lt hmn
    IsFacetOf (permutahedron n)
      (face_set (permutahedron n) (-subsetSumIndicator (prefix_set σ m hm))
        (-(Nat.choose ((prefix_set σ m hm).card + 1) 2 : ℝ))) ∧
    ascending_vector n ∘ σ ∈
      face_set (permutahedron n) (-subsetSumIndicator (prefix_set σ m hm))
        (-(Nat.choose ((prefix_set σ m hm).card + 1) 2 : ℝ)) := by
  let hm : m ≤ n := Nat.le_of_lt hmn
  have hx_face :
      ascending_vector n ∘ σ ∈
        face_set (permutahedron n) (-subsetSumIndicator (prefix_set σ m hm))
          (-(Nat.choose ((prefix_set σ m hm).card + 1) 2 : ℝ)) :=
    mem_prefix_subset_sum_face_of_permuted_vertex σ hmn
  have hK_nonempty : (prefix_set σ m hm).Nonempty := prefix_set_nonempty σ m hm h0
  have hK_proper : (prefix_set σ m hm).card < n := by
    simpa [prefix_set_card σ m hm] using hmn
  -- The subset-sum facet theorem upgrades the incident equality face to `IsFacetOf`.
  exact ⟨subset_sum_face_isFacetOf (prefix_set σ m hm) hK_nonempty hK_proper hx_face, hx_face⟩

/-- Helper for Exercise 3.23: the prefix facet indexed by the boundary after position `m` in the
`σ`-order. -/
abbrev prefix_face {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : Fin (n - 1)) : Set (Fin n → ℝ) :=
  let hmn : m.1 + 1 < n := by omega
  let hm : m.1 + 1 ≤ n := Nat.le_of_lt hmn
  face_set (permutahedron n) (-subsetSumIndicator (prefix_set σ (m.1 + 1) hm))
    (-(Nat.choose ((prefix_set σ (m.1 + 1) hm).card + 1) 2 : ℝ))

/-- Helper for Exercise 3.23: the left endpoint of the `m`th boundary, viewed in `Fin n`. -/
lemma boundary_left_index_lt {n : ℕ} (m : Fin (n - 1)) : m.1 < n := by
  omega

/-- Helper for Exercise 3.23: the right endpoint of the `m`th boundary, viewed in `Fin n`. -/
lemma boundary_right_index_lt {n : ℕ} (m : Fin (n - 1)) : m.1 + 1 < n := by
  omega

/-- Helper for Exercise 3.23: the left endpoint of the `m`th boundary in the ordered coordinates. -/
abbrev boundary_left_index {n : ℕ} (m : Fin (n - 1)) : Fin n :=
  ⟨m.1, boundary_left_index_lt m⟩

/-- Helper for Exercise 3.23: the right endpoint of the `m`th boundary in the ordered
coordinates. -/
abbrev boundary_right_index {n : ℕ} (m : Fin (n - 1)) : Fin n :=
  ⟨m.1 + 1, boundary_right_index_lt m⟩

/-- Helper for Exercise 3.23: swapping the two values adjacent to the `m`th boundary in the
ordered permutation vertex. -/
abbrev boundary_swap_vertex {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : Fin (n - 1)) :
    Fin n → ℝ :=
  (ascending_vector n ∘ σ) ∘
    Equiv.swap (σ.symm (boundary_left_index m)) (σ.symm (boundary_right_index m))

/-- Helper for Exercise 3.23: any valid supporting functional through the permutation vertex has
nonnegative adjacent coefficient gaps in the `σ`-order. -/
lemma incident_face_adjacent_gap_nonneg
    {n : ℕ} (σ : Equiv.Perm (Fin n)) {c : Fin n → ℝ} {δ : ℝ} (m : Fin (n - 1))
    (h_valid : is_valid_inequality (permutahedron n) c δ)
    (hx : ascending_vector n ∘ σ ∈ face_set (permutahedron n) c δ) :
    0 ≤ c (σ.symm (boundary_right_index m)) - c (σ.symm (boundary_left_index m)) := by
  let x : Fin n → ℝ := ascending_vector n ∘ σ
  let i : Fin n := σ.symm (boundary_left_index m)
  let j : Fin n := σ.symm (boundary_right_index m)
  have hy_perm : boundary_swap_vertex σ m ∈ permutahedron n := by
    -- The adjacent swap is still a permutation vertex of the permutahedron.
    rw [permutahedron_eq_convexHull]
    exact subset_convexHull ℝ (permutahedron_vertices n)
      (mem_permutahedron_vertices_iff.mpr
        ⟨σ * Equiv.swap (σ.symm (boundary_left_index m)) (σ.symm (boundary_right_index m)), rfl⟩)
  have hx_eq : c ⬝ᵥ x = δ := (mem_face_set_iff.mp hx).2
  have hy_le : c ⬝ᵥ boundary_swap_vertex σ m ≤ δ := h_valid hy_perm
  have hswap_le :
      c ⬝ᵥ boundary_swap_vertex σ m - c ⬝ᵥ x ≤ 0 := by
    linarith [hy_le, hx_eq]
  have hswap :
      c ⬝ᵥ boundary_swap_vertex σ m - c ⬝ᵥ x = (c i - c j) * (x j - x i) := by
    -- The swap formula isolates the contribution of the crossed boundary.
    simpa [boundary_swap_vertex, x, i, j] using
      dotProduct_comp_swap_sub_eq (c := c) (x := x) i j
  have hstep : x j - x i = 1 := by
    -- The ordered permutation vertex takes consecutive values across this boundary.
    simp [x, i, j, ascending_vector]
  have hnonpos : c i - c j ≤ 0 := by
    rw [hswap, hstep, mul_one] at hswap_le
    exact hswap_le
  -- Rewriting the nonpositive difference gives the claimed nonnegative adjacent gap.
  exact sub_nonneg.mpr (sub_nonpos.mp hnonpos)

/-- Helper for Exercise 3.23: if every point of `F` lies on one dot-product level set, then the
direction of `affineSpan ℝ F` lies in the kernel of that dot-product functional. -/
lemma face_set_direction_le_dotProduct_ker
    {n : ℕ} {F : Set (Fin n → ℝ)} {c x₀ : Fin n → ℝ} {δ : ℝ}
    (hx₀ : x₀ ∈ F)
    (hlevel : ∀ ⦃x : Fin n → ℝ⦄, x ∈ F → c ⬝ᵥ x = δ) :
    (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductStrongDual c).toLinearMap := by
  have hspan_level :
      (affineSpan ℝ F : Set (Fin n → ℝ)) ⊆ {x | c ⬝ᵥ x = δ} := by
    intro x hx
    -- The face equation is affine, so it extends from `F` to its affine span.
    refine affineSpan_induction (k := ℝ) (s := F) (p := fun y ↦ c ⬝ᵥ y = δ) hx ?_ ?_
    · intro y hy
      exact hlevel hy
    · intro a u v w hu hv hw
      simp [hu, hv, hw, sub_eq_add_neg, add_comm]
  intro v hv
  have hx₀_aff : x₀ ∈ affineSpan ℝ F := subset_affineSpan ℝ _ hx₀
  rw [LinearMap.mem_ker]
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀_aff] at hv
  rcases hv with ⟨x, hx_aff, rfl⟩
  -- Two points on the same level set differ by a kernel vector.
  have hx_eq : c ⬝ᵥ x = δ := hspan_level hx_aff
  have hx₀_eq : c ⬝ᵥ x₀ = δ := hlevel hx₀
  simp [dotProductStrongDual_apply, vsub_eq_sub, hx_eq, hx₀_eq]

/-- Helper for Exercise 3.23: a codimension-one equality face through the permutation vertex has
some strictly positive adjacent coefficient gap in the `σ`-order. -/
lemma exists_positive_adjacent_gap_of_incident_face
    {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n))
    {c : Fin n → ℝ} {δ : ℝ}
    (hvalid : is_valid_inequality (permutahedron n) c δ)
    (hx : ascending_vector n ∘ σ ∈ face_set (permutahedron n) c δ)
    (hcodim :
      Module.finrank ℝ
        (affineSpan ℝ (face_set (permutahedron n) c δ)).direction + 1 =
      Module.finrank ℝ (affineSpan ℝ (permutahedron n)).direction) :
    ∃ m : Fin (n - 1),
      0 < c (σ.symm (boundary_right_index m)) - c (σ.symm (boundary_left_index m)) := by
  by_contra hpos
  push Not at hpos
  let j0 : Fin n := ⟨0, by omega⟩
  have hgap_zero :
      ∀ m : Fin (n - 1),
        c (σ.symm (boundary_right_index m)) - c (σ.symm (boundary_left_index m)) = 0 := by
    intro m
    have hnonneg := incident_face_adjacent_gap_nonneg σ m hvalid hx
    linarith [hpos m, hnonneg]
  have hconst_ordered :
      ∀ j : Fin n, c (σ.symm j) = c (σ.symm j0) := by
    have hconst_nat :
        ∀ k : ℕ, ∀ hk : k < n, c (σ.symm ⟨k, hk⟩) = c (σ.symm j0) := by
      intro k hk
      induction k with
      | zero =>
          simp [j0]
      | succ k ih =>
          have hk' : k < n := Nat.lt_of_succ_lt hk
          have hk'' : k < n - 1 := by omega
          have hstep :
              c (σ.symm ⟨k + 1, hk⟩) = c (σ.symm ⟨k, hk'⟩) := by
            have hm_zero := hgap_zero ⟨k, hk''⟩
            exact sub_eq_zero.mp (by
              simpa [boundary_left_index, boundary_right_index] using hm_zero)
          exact hstep.trans (ih hk')
    intro j
    exact hconst_nat j.1 j.2
  have hconst_dot :
      ∀ x : Fin n → ℝ, c ⬝ᵥ x = c (σ.symm j0) * ∑ i, x i := by
    intro x
    calc
      c ⬝ᵥ x = ∑ j : Fin n, c (σ.symm j) * x (σ.symm j) := dotProduct_eq_sum_ordered_symm σ c x
      _ = ∑ j : Fin n, c (σ.symm j0) * x (σ.symm j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [hconst_ordered j]
      _ = c (σ.symm j0) * ∑ j : Fin n, x (σ.symm j) := by
        rw [← Finset.mul_sum]
      _ = c (σ.symm j0) * ∑ i, x i := by
        congr 1
        simpa using (Equiv.sum_comp (e := σ.symm) (g := fun i : Fin n ↦ x i))
  have hx_total :
      ∑ i, (ascending_vector n ∘ σ) i = (Nat.choose (n + 1) 2 : ℝ) := by
    have hx_perm : ascending_vector n ∘ σ ∈ permutahedron n := (mem_face_set_iff.mp hx).1
    simpa using permutahedron_subset_constant_sum_hyperplane n hx_perm
  have hδ_const : δ = c (σ.symm j0) * (Nat.choose (n + 1) 2 : ℝ) := by
    -- Evaluating the face equation at the incident permutation vertex pins down `δ`.
    calc
      δ = c ⬝ᵥ (ascending_vector n ∘ σ) := (mem_face_set_iff.mp hx).2.symm
      _ = c (σ.symm j0) * ∑ i, (ascending_vector n ∘ σ) i := hconst_dot (ascending_vector n ∘ σ)
      _ = c (σ.symm j0) * (Nat.choose (n + 1) 2 : ℝ) := by rw [hx_total]
  have hP_subset_face : permutahedron n ⊆ face_set (permutahedron n) c δ := by
    intro x hxP
    have hx_total : ∑ i, x i = (Nat.choose (n + 1) 2 : ℝ) := by
      simpa using permutahedron_subset_constant_sum_hyperplane n hxP
    have hx_eq : c ⬝ᵥ x = δ := by
      calc
        c ⬝ᵥ x = c (σ.symm j0) * ∑ i, x i := hconst_dot x
        _ = c (σ.symm j0) * (Nat.choose (n + 1) 2 : ℝ) := by rw [hx_total]
        _ = δ := hδ_const.symm
    exact (mem_face_set_iff).2 ⟨hxP, hx_eq⟩
  have hspan_eq :
      affineSpan ℝ (face_set (permutahedron n) c δ) = affineSpan ℝ (permutahedron n) := by
    refine le_antisymm ?_ ?_
    · exact affineSpan_mono ℝ (fun x hx_face ↦ (mem_face_set_iff.mp hx_face).1)
    · exact affineSpan_mono ℝ hP_subset_face
  have hface_dim :
      Module.finrank ℝ
        (affineSpan ℝ (face_set (permutahedron n) c δ)).direction =
      Module.finrank ℝ (affineSpan ℝ (permutahedron n)).direction := by
    rw [hspan_eq]
  have hcontra :
      Module.finrank ℝ (affineSpan ℝ (permutahedron n)).direction + 1 ≠
        Module.finrank ℝ (affineSpan ℝ (permutahedron n)).direction :=
    Nat.succ_ne_self _
  have hcodim' := hcodim
  simp [hface_dim] at hcodim'

/-- Helper for Exercise 3.23: after ordering the coefficients by `σ`, Abel summation rewrites the
supporting-functional drop from the permutation vertex to any point of the permutahedron as a sum
of adjacent coefficient gaps times prefix-sum excesses. -/
lemma ordered_dotProduct_sub_permuted_vertex_eq_gap_sum
    {n : ℕ} (σ : Equiv.Perm (Fin n)) {c y : Fin n → ℝ}
    (hy_perm : y ∈ permutahedron n) :
    c ⬝ᵥ (ascending_vector n ∘ σ) - c ⬝ᵥ y =
      ∑ l : Fin (n - 1),
        (c (σ.symm (boundary_right_index l)) - c (σ.symm (boundary_left_index l))) *
          (∑ i ∈ prefix_set σ (l.1 + 1) (Nat.le_of_lt (boundary_right_index_lt l)), y i -
            (Nat.choose (l.1 + 2) 2 : ℝ)) := by
  let xσ : Fin n → ℝ := ascending_vector n ∘ σ
  let a : ℕ → ℝ := fun i ↦ if h : i < n then c (σ.symm ⟨i, h⟩) else 0
  let gx : ℕ → ℝ := fun i ↦ if h : i < n then xσ (σ.symm ⟨i, h⟩) else 0
  let gy : ℕ → ℝ := fun i ↦ if h : i < n then y (σ.symm ⟨i, h⟩) else 0
  have hxσ_perm : xσ ∈ permutahedron n := by
    -- The ordered reference point is itself a permutation vertex of the permutahedron.
    rw [permutahedron_eq_convexHull]
    exact subset_convexHull ℝ (permutahedron_vertices n)
      (mem_permutahedron_vertices_iff.mpr ⟨σ, rfl⟩)
  have hx_dot :
      c ⬝ᵥ xσ = ∑ i ∈ Finset.range n, a i * gx i := by
    -- Reindex the dot product through the `σ`-order and then replace the `Fin`-sum by a range sum.
    calc
      c ⬝ᵥ xσ = ∑ j : Fin n, c (σ.symm j) * xσ (σ.symm j) := dotProduct_eq_sum_ordered_symm σ c xσ
      _ = ∑ j : Fin n,
            (if h : (j : ℕ) < n then c (σ.symm ⟨j, h⟩) * xσ (σ.symm ⟨j, h⟩) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [j.2]
      _ = ∑ i ∈ Finset.range n,
            (if h : i < n then c (σ.symm ⟨i, h⟩) * xσ (σ.symm ⟨i, h⟩) else 0) := by
          let fx : ℕ → ℝ := fun i ↦
            if h : i < n then c (σ.symm ⟨i, h⟩) * xσ (σ.symm ⟨i, h⟩) else 0
          simpa [fx] using (Fin.sum_univ_eq_sum_range fx n)
      _ = ∑ i ∈ Finset.range n, a i * gx i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi' : i < n := Finset.mem_range.mp hi
          simp [a, gx, hi']
  have hy_dot :
      c ⬝ᵥ y = ∑ i ∈ Finset.range n, a i * gy i := by
    -- The same reindexing applies to the arbitrary point `y`.
    calc
      c ⬝ᵥ y = ∑ j : Fin n, c (σ.symm j) * y (σ.symm j) := dotProduct_eq_sum_ordered_symm σ c y
      _ = ∑ j : Fin n,
            (if h : (j : ℕ) < n then c (σ.symm ⟨j, h⟩) * y (σ.symm ⟨j, h⟩) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [j.2]
      _ = ∑ i ∈ Finset.range n,
            (if h : i < n then c (σ.symm ⟨i, h⟩) * y (σ.symm ⟨i, h⟩) else 0) := by
          let fy : ℕ → ℝ := fun i ↦
            if h : i < n then c (σ.symm ⟨i, h⟩) * y (σ.symm ⟨i, h⟩) else 0
          simpa [fy] using (Fin.sum_univ_eq_sum_range fy n)
      _ = ∑ i ∈ Finset.range n, a i * gy i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi' : i < n := Finset.mem_range.mp hi
          simp [a, gy, hi']
  have htotal_x :
      ∑ i ∈ Finset.range n, gx i = (Nat.choose (n + 1) 2 : ℝ) := by
    -- The ordered coordinates of the permutation vertex still sum to the ambient triangular total.
    calc
      ∑ i ∈ Finset.range n, gx i = ∑ j : Fin n, xσ (σ.symm j) := by
        symm
        simpa [gx] using
          (Finset.sum_fin_eq_sum_range (c := fun j : Fin n ↦ xσ (σ.symm j)))
      _ = ∑ i, xσ i := by
        simpa using (Equiv.sum_comp (e := σ.symm) (g := fun i : Fin n ↦ xσ i))
      _ = (Nat.choose (n + 1) 2 : ℝ) := by
        simpa [xσ] using permutahedron_subset_constant_sum_hyperplane n hxσ_perm
  have htotal_y :
      ∑ i ∈ Finset.range n, gy i = (Nat.choose (n + 1) 2 : ℝ) := by
    -- Every point of the permutahedron satisfies the same constant-sum equation.
    calc
      ∑ i ∈ Finset.range n, gy i = ∑ j : Fin n, y (σ.symm j) := by
        symm
        simpa [gy] using
          (Finset.sum_fin_eq_sum_range (c := fun j : Fin n ↦ y (σ.symm j)))
      _ = ∑ i, y i := by
        simpa using (Equiv.sum_comp (e := σ.symm) (g := fun i : Fin n ↦ y i))
      _ = (Nat.choose (n + 1) 2 : ℝ) := by
        simpa using permutahedron_subset_constant_sum_hyperplane n hy_perm
  have hprefix_x :
      ∀ r : ℕ, ∀ hr : r ≤ n,
        ∑ i ∈ Finset.range r, gx i = (Nat.choose (r + 1) 2 : ℝ) := by
    intro r hr
    -- Reindex the ordered prefix back to the corresponding prefix set of the permutation vertex.
    calc
      ∑ i ∈ Finset.range r, gx i = ∑ j : Fin r, xσ (σ.symm (Fin.castLE hr j)) := by
        calc
          ∑ i ∈ Finset.range r, gx i =
              ∑ i ∈ Finset.range r,
                (if h : i < r then xσ (σ.symm (Fin.castLE hr ⟨i, h⟩)) else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hir : i < r := Finset.mem_range.mp hi
                  have hin : i < n := lt_of_lt_of_le hir hr
                  simp [gx, hir, hin]
          _ = ∑ j : Fin r, xσ (σ.symm (Fin.castLE hr j)) := by
              symm
              exact Finset.sum_fin_eq_sum_range
                (c := fun j : Fin r ↦ xσ (σ.symm (Fin.castLE hr j)))
      _ = ∑ i ∈ prefix_set σ r hr, xσ i := by
        symm
        exact sum_prefix_set_eq_sum_ordered σ r hr xσ
      _ = (Nat.choose (r + 1) 2 : ℝ) := sum_prefix_set_values σ r hr
  have hprefix_y :
      ∀ r : ℕ, ∀ hr : r ≤ n,
        ∑ i ∈ Finset.range r, gy i = ∑ t ∈ prefix_set σ r hr, y t := by
    intro r hr
    -- The same range-to-prefix-set reindexing identifies ordered partial sums of `y`.
    calc
      ∑ i ∈ Finset.range r, gy i = ∑ j : Fin r, y (σ.symm (Fin.castLE hr j)) := by
        calc
          ∑ i ∈ Finset.range r, gy i =
              ∑ i ∈ Finset.range r,
                (if h : i < r then y (σ.symm (Fin.castLE hr ⟨i, h⟩)) else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hir : i < r := Finset.mem_range.mp hi
                  have hin : i < n := lt_of_lt_of_le hir hr
                  simp [gy, hir, hin]
          _ = ∑ j : Fin r, y (σ.symm (Fin.castLE hr j)) := by
              symm
              exact Finset.sum_fin_eq_sum_range
                (c := fun j : Fin r ↦ y (σ.symm (Fin.castLE hr j)))
      _ = ∑ t ∈ prefix_set σ r hr, y t := by
        symm
        exact sum_prefix_set_eq_sum_ordered σ r hr y
  have hx_parts :
      ∑ i ∈ Finset.range n, a i * gx i =
        a (n - 1) * ∑ i ∈ Finset.range n, gx i -
          ∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) * ∑ j ∈ Finset.range (i + 1), gx j := by
    -- Apply finite Abel summation to the ordered coefficient sequence against the ordered values.
    simpa [smul_eq_mul] using Finset.sum_range_by_parts a gx n
  have hy_parts :
      ∑ i ∈ Finset.range n, a i * gy i =
        a (n - 1) * ∑ i ∈ Finset.range n, gy i -
          ∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) * ∑ j ∈ Finset.range (i + 1), gy j := by
    -- Apply the same identity to the ordered coordinates of `y`.
    simpa [smul_eq_mul] using Finset.sum_range_by_parts a gy n
  calc
    c ⬝ᵥ xσ - c ⬝ᵥ y
        = -∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) * ∑ j ∈ Finset.range (i + 1), gx j +
            ∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) * ∑ j ∈ Finset.range (i + 1), gy j := by
            rw [hx_dot, hy_dot, hx_parts, hy_parts, htotal_x, htotal_y]
            ring
    _ = ∑ i ∈ Finset.range (n - 1),
          ((a (i + 1) - a i) * ∑ j ∈ Finset.range (i + 1), gy j -
            (a (i + 1) - a i) * ∑ j ∈ Finset.range (i + 1), gx j) := by
          rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = ∑ i ∈ Finset.range (n - 1),
          (a (i + 1) - a i) *
            (∑ j ∈ Finset.range (i + 1), gy j - ∑ j ∈ Finset.range (i + 1), gx j) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = ∑ i ∈ Finset.range (n - 1),
          (if h : i < n - 1 then
            (c (σ.symm (boundary_right_index ⟨i, h⟩)) -
                c (σ.symm (boundary_left_index ⟨i, h⟩))) *
              (∑ t ∈ prefix_set σ (i + 1)
                  (Nat.succ_le_of_lt (lt_of_lt_of_le h (Nat.sub_le _ _))), y t -
                (Nat.choose (i + 2) 2 : ℝ))
          else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi' : i < n - 1 := Finset.mem_range.mp hi
            have hin : i + 1 ≤ n := by omega
            have hi0 : i < n := lt_of_lt_of_le (Nat.lt_succ_self i) hin
            have hi1 : i + 1 < n := by omega
            have hgap :
                a (i + 1) - a i =
                  c (σ.symm (boundary_right_index ⟨i, hi'⟩)) -
                    c (σ.symm (boundary_left_index ⟨i, hi'⟩)) := by
              simp [a, hi0, hi1, boundary_left_index,
                boundary_right_index]
            rw [hgap, hprefix_y (i + 1) hin, hprefix_x (i + 1) hin]
            simp [hi']
    _ = ∑ l : Fin (n - 1),
          (c (σ.symm (boundary_right_index l)) - c (σ.symm (boundary_left_index l))) *
            (∑ i ∈ prefix_set σ (l.1 + 1) (Nat.le_of_lt (boundary_right_index_lt l)), y i -
              (Nat.choose (l.1 + 2) 2 : ℝ)) := by
            simpa using
              (Finset.sum_fin_eq_sum_range
                (c := fun l : Fin (n - 1) ↦
                  (c (σ.symm (boundary_right_index l)) - c (σ.symm (boundary_left_index l))) *
                    (∑ i ∈ prefix_set σ (l.1 + 1) (Nat.le_of_lt (boundary_right_index_lt l)), y i -
                      (Nat.choose (l.1 + 2) 2 : ℝ)))).symm

/-- Helper for Exercise 3.23: an index lies in a prefix set exactly when its `σ`-position is
strictly before the cut. -/
lemma mem_prefix_set_iff_order_lt
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (r : ℕ) (hr : r ≤ n) (k : Fin n) :
    k ∈ prefix_set σ r hr ↔ (σ k).1 < r := by
  constructor
  · intro hk
    -- Unfold the image description and read off the `σ`-position of the witness.
    unfold prefix_set at hk
    rcases Finset.mem_image.mp hk with ⟨j, -, rfl⟩
    simp
  · intro hk
    -- Rebuild the witnessing `Fin r` index from the ordered position of `k`.
    let j : Fin r := ⟨(σ k).1, hk⟩
    unfold prefix_set
    refine Finset.mem_image.mpr ?_
    refine ⟨j, by simp, ?_⟩
    apply σ.injective
    ext
    simp [j]

/-- Helper for Exercise 3.23: the left endpoint of the `l`th boundary lies in the first `m + 1`
positions exactly when that boundary is not to the right of `m`. -/
lemma castSucc_preimage_mem_prefix_set_iff
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (m l : Fin (n - 1)) :
    let hmn : m.1 + 1 < n := by omega
    let hm : m.1 + 1 ≤ n := Nat.le_of_lt hmn
    σ.symm (boundary_left_index l) ∈ prefix_set σ (m.1 + 1) hm ↔ l ≤ m := by
  -- Normalize prefix-set membership to the ordered position of the left boundary endpoint.
  dsimp
  rw [mem_prefix_set_iff_order_lt]
  simp

/-- Helper for Exercise 3.23: the right endpoint of the `l`th boundary lies in the first `m + 1`
positions exactly when that boundary lies strictly to the left of `m`. -/
lemma succ_preimage_mem_prefix_set_iff
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (m l : Fin (n - 1)) :
    let hmn : m.1 + 1 < n := by omega
    let hm : m.1 + 1 ≤ n := Nat.le_of_lt hmn
    σ.symm (boundary_right_index l) ∈ prefix_set σ (m.1 + 1) hm ↔ l < m := by
  -- Normalize prefix-set membership to the ordered position of the right boundary endpoint.
  dsimp
  rw [mem_prefix_set_iff_order_lt]
  simp

/-- Helper for Exercise 3.23: once one adjacent coefficient gap is strictly positive, the exposed
face through the permutation vertex is contained in the corresponding prefix facet. -/
lemma incident_face_subset_prefix_face_of_positive_gap
    {n : ℕ} (σ : Equiv.Perm (Fin n)) {c : Fin n → ℝ} {δ : ℝ}
    (hvalid : is_valid_inequality (permutahedron n) c δ)
    (hx : ascending_vector n ∘ σ ∈ face_set (permutahedron n) c δ)
    (m : Fin (n - 1))
    (hm_pos : 0 < c (σ.symm (boundary_right_index m)) - c (σ.symm (boundary_left_index m))) :
    face_set (permutahedron n) c δ ⊆ prefix_face σ m := by
  intro y hy
  let hmn : m.1 + 1 < n := by omega
  let hm : m.1 + 1 ≤ n := Nat.le_of_lt hmn
  let K : Finset (Fin n) := prefix_set σ (m.1 + 1) hm
  have hy_perm : y ∈ permutahedron n := (mem_face_set_iff.mp hy).1
  have hsum_eq :
      c ⬝ᵥ (ascending_vector n ∘ σ) - c ⬝ᵥ y = 0 := by
    -- Points on the same equality face have the same supporting-functional value.
    have hx_eq : c ⬝ᵥ (ascending_vector n ∘ σ) = δ := (mem_face_set_iff.mp hx).2
    have hy_eq : c ⬝ᵥ y = δ := (mem_face_set_iff.mp hy).2
    linarith
  have hgap_sum :=
    ordered_dotProduct_sub_permuted_vertex_eq_gap_sum σ (c := c) (y := y) hy_perm
  let term : Fin (n - 1) → ℝ := fun l ↦
    (c (σ.symm (boundary_right_index l)) - c (σ.symm (boundary_left_index l))) *
      (∑ i ∈ prefix_set σ (l.1 + 1) (Nat.le_of_lt (boundary_right_index_lt l)), y i -
        (Nat.choose (l.1 + 2) 2 : ℝ))
  have hterm_nonneg : ∀ l : Fin (n - 1), 0 ≤ term l := by
    intro l
    -- Each factor is nonnegative: the coefficient gap by adjacent-swap validity, the prefix
    -- excess by the subset-sum inequalities valid on the permutahedron.
    have hgap_nonneg := incident_face_adjacent_gap_nonneg σ l hvalid hx
    have hprefix_ge :
        (Nat.choose (l.1 + 2) 2 : ℝ) ≤
          ∑ i ∈ prefix_set σ (l.1 + 1) (Nat.le_of_lt (boundary_right_index_lt l)), y i := by
      let Kl : Finset (Fin n) :=
        prefix_set σ (l.1 + 1) (Nat.le_of_lt (boundary_right_index_lt l))
      have hKl_valid :
          (-subsetSumIndicator Kl) ⬝ᵥ y ≤ -(Nat.choose (Kl.card + 1) 2 : ℝ) :=
        permutahedron_subset_sum_is_valid_inequality n Kl hy_perm
      have hKl_sum :
          (Nat.choose (Kl.card + 1) 2 : ℝ) ≤ ∑ i ∈ Kl, y i := by
        have hneg :
            -(∑ i ∈ Kl, y i) ≤ -(Nat.choose (Kl.card + 1) 2 : ℝ) := by
          simpa [Kl, dot_subsetSumIndicator_eq_sum] using hKl_valid
        linarith
      simpa [Kl, prefix_set_card σ (l.1 + 1) (Nat.le_of_lt (boundary_right_index_lt l))]
        using hKl_sum
    have hprefix_nonneg :
        0 ≤ ∑ i ∈ prefix_set σ (l.1 + 1) (Nat.le_of_lt (boundary_right_index_lt l)), y i -
          (Nat.choose (l.1 + 2) 2 : ℝ) := by
      linarith
    exact mul_nonneg hgap_nonneg hprefix_nonneg
  have hterm_zero :
      ∀ l : Fin (n - 1), term l = 0 := by
    -- The Abel expansion is a sum of nonnegative terms, and the shared face equation makes it zero.
    have hsum_term : ∑ l, term l = 0 := by
      calc
        ∑ l, term l = c ⬝ᵥ (ascending_vector n ∘ σ) - c ⬝ᵥ y := by
          symm
          simpa [term] using hgap_sum
        _ = 0 := hsum_eq
    have hterm_eq_zero : term = 0 := (Fintype.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum_term
    intro l
    exact congrFun hterm_eq_zero l
  have hm_term_zero : term m = 0 := by
    exact hterm_zero m
  have hm_prefix_eq :
      ∑ i ∈ K, y i = (Nat.choose (K.card + 1) 2 : ℝ) := by
    -- The strictly positive gap forces equality in the matching prefix inequality.
    have hm_gap_ne :
        c (σ.symm (boundary_right_index m)) - c (σ.symm (boundary_left_index m)) ≠ 0 :=
      ne_of_gt hm_pos
    have hm_diff_zero :
        ∑ i ∈ K, y i - (Nat.choose (m.1 + 2) 2 : ℝ) = 0 := by
      have hprod_zero :
          (c (σ.symm (boundary_right_index m)) - c (σ.symm (boundary_left_index m))) *
              (∑ i ∈ K, y i - (Nat.choose (m.1 + 2) 2 : ℝ)) = 0 := by
        simpa [term, K, hm] using hm_term_zero
      exact (mul_eq_zero.mp hprod_zero).resolve_left hm_gap_ne
    have hcard : K.card = m.1 + 1 := prefix_set_card σ (m.1 + 1) hm
    rw [hcard]
    linarith
  have hy_prefix_face :
      y ∈ face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
    -- The tight prefix-sum equality is exactly the defining equation of the prefix facet.
    refine (mem_permutahedron_subset_sum_face_iff).2 ?_
    exact ⟨hy_perm, hm_prefix_eq⟩
  simpa [prefix_face, K, hmn, hm] using hy_prefix_face

/-- Helper for Exercise 3.23: swapping the values adjacent to the `m`th boundary stays inside every
other prefix facet. -/
lemma boundary_swap_vertex_mem_prefix_face_of_ne
    {n : ℕ} (σ : Equiv.Perm (Fin n)) {m l : Fin (n - 1)} (hml : m ≠ l) :
    boundary_swap_vertex σ m ∈ prefix_face σ l := by
  let hln : l.1 + 1 < n := by omega
  let hl : l.1 + 1 ≤ n := Nat.le_of_lt hln
  let K : Finset (Fin n) := prefix_set σ (l.1 + 1) hl
  let x : Fin n → ℝ := ascending_vector n ∘ σ
  let i : Fin n := σ.symm (boundary_left_index m)
  let j : Fin n := σ.symm (boundary_right_index m)
  have hx_face : x ∈ face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
    -- The ordered permutation vertex lies on every prefix face.
    simpa [K, prefix_face, x, hln, hl] using mem_prefix_subset_sum_face_of_permuted_vertex σ hln
  have hx_sum :
      ∑ t ∈ K, x t = (Nat.choose (K.card + 1) 2 : ℝ) :=
    (mem_permutahedron_subset_sum_face_iff.mp hx_face).2
  have hy_perm : x ∘ Equiv.swap i j ∈ permutahedron n := by
    -- Swapping adjacent coordinates still gives a permutation vertex of the permutahedron.
    rw [permutahedron_eq_convexHull]
    exact subset_convexHull ℝ (permutahedron_vertices n)
      (mem_permutahedron_vertices_iff.mpr
        ⟨σ * Equiv.swap (σ.symm (boundary_left_index m)) (σ.symm (boundary_right_index m)), rfl⟩)
  have hleft :
      σ.symm (boundary_left_index m) ∈ K ↔ m ≤ l := by
    simpa [K, hl] using castSucc_preimage_mem_prefix_set_iff (σ := σ) l m
  have hright :
      σ.symm (boundary_right_index m) ∈ K ↔ m < l := by
    simpa [K, hl] using succ_preimage_mem_prefix_set_iff (σ := σ) l m
  have hmlelt : m ≤ l ↔ m < l := by
    constructor
    · intro hml'
      exact lt_of_le_of_ne hml' hml
    · exact fun h ↦ le_of_lt h
  have hsame : i ∈ K ↔ j ∈ K := by
    exact hleft.trans (hmlelt.trans hright.symm)
  have hy_sum :
      ∑ t ∈ K, (x ∘ Equiv.swap i j) t = (Nat.choose (K.card + 1) 2 : ℝ) := by
    -- When both swapped indices lie on the same side of the cut, the prefix sum is unchanged.
    calc
      ∑ t ∈ K, (x ∘ Equiv.swap i j) t = subsetSumIndicator K ⬝ᵥ (x ∘ Equiv.swap i j) := by
        symm
        exact dot_subsetSumIndicator_eq_sum K (x ∘ Equiv.swap i j)
      _ = subsetSumIndicator K ⬝ᵥ x := by
        exact dot_subsetSumIndicator_comp_swap_eq_of_same_membership K x i j hsame
      _ = ∑ t ∈ K, x t := dot_subsetSumIndicator_eq_sum K x
      _ = (Nat.choose (K.card + 1) 2 : ℝ) := hx_sum
  -- The face equation for the swapped vertex now follows from the preserved prefix sum.
  have hy_face :
      x ∘ Equiv.swap i j ∈ face_set (permutahedron n) (-subsetSumIndicator K)
        (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
    exact (mem_permutahedron_subset_sum_face_iff).2 ⟨hy_perm, hy_sum⟩
  simpa [boundary_swap_vertex, prefix_face, K, x, i, j, hln, hl] using hy_face

/-- Helper for Exercise 3.23: swapping across the `m`th boundary leaves the corresponding prefix
facet. -/
lemma boundary_swap_vertex_not_mem_prefix_face
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : Fin (n - 1)) :
    boundary_swap_vertex σ m ∉ prefix_face σ m := by
  let hmn : m.1 + 1 < n := by omega
  let hm : m.1 + 1 ≤ n := Nat.le_of_lt hmn
  let K : Finset (Fin n) := prefix_set σ (m.1 + 1) hm
  let x : Fin n → ℝ := ascending_vector n ∘ σ
  let i : Fin n := σ.symm (boundary_left_index m)
  let j : Fin n := σ.symm (boundary_right_index m)
  intro hy_face
  have hx_face : x ∈ face_set (permutahedron n) (-subsetSumIndicator K)
      (-(Nat.choose (K.card + 1) 2 : ℝ)) := by
    -- The base permutation vertex is tight for its own prefix face.
    simpa [K, prefix_face, x, hmn, hm] using mem_prefix_subset_sum_face_of_permuted_vertex σ hmn
  have hx_sum :
      ∑ t ∈ K, x t = (Nat.choose (K.card + 1) 2 : ℝ) :=
    (mem_permutahedron_subset_sum_face_iff.mp hx_face).2
  have hy_sum :
      ∑ t ∈ K, (x ∘ Equiv.swap i j) t = (Nat.choose (K.card + 1) 2 : ℝ) :=
    (mem_permutahedron_subset_sum_face_iff.mp
      (by simpa [boundary_swap_vertex, prefix_face, K, x, i, j, hmn, hm] using hy_face)).2
  have hi : i ∈ K := by
    simpa [K, hm] using
      (castSucc_preimage_mem_prefix_set_iff (σ := σ) m m).2 le_rfl
  have hj : j ∉ K := by
    intro hjK
    have : m < m := by
      simpa [K, hm] using
        (succ_preimage_mem_prefix_set_iff (σ := σ) m m).1 hjK
    exact lt_irrefl _ this
  have hijx : x i < x j := by
    -- Across the crossed boundary the ordered vertex gains exactly one.
    simp [x, i, j, ascending_vector, boundary_left_index, boundary_right_index]
  have hlt_sum :
      ∑ t ∈ K, x t < ∑ t ∈ K, (x ∘ Equiv.swap i j) t := by
    -- A cross-boundary swap strictly increases the matching prefix sum.
    simpa [K, x, i, j, dot_subsetSumIndicator_eq_sum] using
      dot_subsetSumIndicator_lt_comp_swap_of_mem_not_mem K x i j hi hj hijx
  linarith

/-- Helper for Exercise 3.23: distinct prefix boundaries define distinct incident prefix facets. -/
lemma prefix_face_injective
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (prefix_face σ) := by
  intro m l hface
  by_contra hml
  have hmem : boundary_swap_vertex σ m ∈ prefix_face σ l :=
    boundary_swap_vertex_mem_prefix_face_of_ne σ hml
  have hmem' : boundary_swap_vertex σ m ∈ prefix_face σ m := by
    -- Rewrite the surviving witness through the assumed equality of prefix faces.
    simpa [hface] using hmem
  exact boundary_swap_vertex_not_mem_prefix_face σ m hmem'

/-- Helper for Exercise 3.23: once an incident facet is contained in one prefix facet, the common
incident vertex and the codimension-one affine-span comparison force equality. -/
lemma prefix_face_eq_of_incident_facet_subset
    {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n))
    {F : Set (Fin n → ℝ)} (hF : IsFacetOf (permutahedron n) F)
    (hxF : ascending_vector n ∘ σ ∈ F) (m : Fin (n - 1))
    (hsubset : F ⊆ prefix_face σ m) :
    F = prefix_face σ m := by
  rcases hF with ⟨hF_nonempty, hF_exposed, hF_dim⟩
  have hm_pos : 0 < m.1 + 1 := by omega
  have hm_lt : m.1 + 1 < n := by omega
  have hprefix_facet : IsFacetOf (permutahedron n) (prefix_face σ m) := by
    simpa [prefix_face] using (prefix_face_incident σ hm_pos hm_lt).1
  have hx_prefix : ascending_vector n ∘ σ ∈ prefix_face σ m := by
    simpa [prefix_face] using (prefix_face_incident σ hm_pos hm_lt).2
  rcases hprefix_facet with ⟨hprefix_nonempty, _, hprefix_dim⟩
  have hdir_le :
      (affineSpan ℝ F).direction ≤ (affineSpan ℝ (prefix_face σ m)).direction := by
    exact AffineSubspace.direction_le (affineSpan_mono ℝ hsubset)
  have hdir_rank_eq :
      Module.finrank ℝ (affineSpan ℝ F).direction =
      Module.finrank ℝ (affineSpan ℝ (prefix_face σ m)).direction := by
    omega
  have hdir_eq :
      (affineSpan ℝ F).direction = (affineSpan ℝ (prefix_face σ m)).direction :=
    Submodule.eq_of_le_of_finrank_eq hdir_le hdir_rank_eq
  have hspan_eq :
      affineSpan ℝ F = affineSpan ℝ (prefix_face σ m) := by
    refine (AffineSubspace.eq_iff_direction_eq_of_mem
      (subset_affineSpan ℝ _ hxF)
      (subset_affineSpan ℝ _ hx_prefix)).2 hdir_eq
  rcases hF_exposed.exists_eq_face_set_of_nonempty hF_nonempty with
    ⟨cFace, δFace, hvalidFace, hF_eq_face⟩
  have hxF_face : ascending_vector n ∘ σ ∈ face_set (permutahedron n) cFace δFace := by
    simpa [hF_eq_face] using hxF
  have hdir_ker :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductStrongDual cFace).toLinearMap := by
    -- The defining face equation is constant on the whole facet `F`.
    refine face_set_direction_le_dotProduct_ker (F := F)
      (c := cFace) (δ := δFace) (x₀ := ascending_vector n ∘ σ) hxF ?_
    intro x hx
    have hx_face : x ∈ face_set (permutahedron n) cFace δFace := by
      simpa [hF_eq_face] using hx
    exact (mem_face_set_iff.mp hx_face).2
  apply Set.Subset.antisymm hsubset
  intro y hy
  have hy_perm : y ∈ permutahedron n := by
    have hy_prefix : y ∈ prefix_face σ m := hy
    exact (mem_face_set_iff.mp (by simpa [prefix_face] using hy_prefix)).1
  have hy_aff_prefix : y ∈ affineSpan ℝ (prefix_face σ m) := subset_affineSpan ℝ _ hy
  have hy_aff_F : y ∈ affineSpan ℝ F := by
    rw [hspan_eq]
    exact hy_aff_prefix
  have hxF_aff : ascending_vector n ∘ σ ∈ affineSpan ℝ F := subset_affineSpan ℝ _ hxF
  have hy_vsub :
      y -ᵥ (ascending_vector n ∘ σ) ∈ (affineSpan ℝ F).direction := by
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxF_aff]
    exact ⟨y, hy_aff_F, rfl⟩
  have hy_vsub_ker :
      y -ᵥ (ascending_vector n ∘ σ) ∈ LinearMap.ker (dotProductStrongDual cFace).toLinearMap := by
    exact hdir_ker hy_vsub
  have hx_eq : cFace ⬝ᵥ (ascending_vector n ∘ σ) = δFace :=
    (mem_face_set_iff.mp hxF_face).2
  have hy_eq : cFace ⬝ᵥ y = δFace := by
    have hzero :
        cFace ⬝ᵥ (y - (ascending_vector n ∘ σ)) = 0 := by
      simpa [dotProductStrongDual_apply] using LinearMap.mem_ker.mp hy_vsub_ker
    have hy_sub :
        cFace ⬝ᵥ y - cFace ⬝ᵥ (ascending_vector n ∘ σ) = 0 := by
      calc
        cFace ⬝ᵥ y - cFace ⬝ᵥ (ascending_vector n ∘ σ)
            = ∑ i, cFace i * y i - ∑ i, cFace i * (ascending_vector n ∘ σ) i := by
                simp [dotProduct]
        _ = ∑ i, cFace i * (y i - (ascending_vector n ∘ σ) i) := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = cFace ⬝ᵥ (y - (ascending_vector n ∘ σ)) := by
              simp [dotProduct, Pi.sub_apply, mul_sub]
        _ = 0 := hzero
    linarith
  have hy_face : y ∈ face_set (permutahedron n) cFace δFace := (mem_face_set_iff).2
    ⟨hy_perm, hy_eq⟩
  simpa [hF_eq_face] using hy_face

/-- Helper for Exercise 3.23: every facet of the permutahedron incident to the permutation vertex
`ascending_vector n ∘ σ` is exactly one prefix facet. -/
lemma incident_facet_eq_unique_prefix_face
    {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n))
    {F : Set (Fin n → ℝ)} (hF : IsFacetOf (permutahedron n) F)
    (hxF : ascending_vector n ∘ σ ∈ F) :
    ∃! m : Fin (n - 1), F = prefix_face σ m := by
  -- Route correction: the remaining upper-bound step must follow the source's exposed-face route,
  -- not a new local recursion on facets.
  rcases hF with ⟨hF_nonempty, hF_exposed, hF_dim⟩
  have hF' : IsFacetOf (permutahedron n) F := ⟨hF_nonempty, hF_exposed, hF_dim⟩
  rcases hF_exposed.exists_eq_face_set_of_nonempty hF_nonempty with
    ⟨c, δ, hvalid, hF_eq_face⟩
  have hx_face : ascending_vector n ∘ σ ∈ face_set (permutahedron n) c δ := by
    simpa [hF_eq_face] using hxF
  have hF_dim_face :
      Module.finrank ℝ (affineSpan ℝ (face_set (permutahedron n) c δ)).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ (permutahedron n)).direction := by
    rw [hF_eq_face] at hF_dim
    exact hF_dim
  obtain ⟨m, hm_pos⟩ :=
    exists_positive_adjacent_gap_of_incident_face hn σ hvalid hx_face hF_dim_face
  have hsubset_face :
      face_set (permutahedron n) c δ ⊆ prefix_face σ m := by
    -- The ordered-gap Abel summation now turns the positive boundary gap into a tight prefix sum.
    exact incident_face_subset_prefix_face_of_positive_gap σ hvalid hx_face m hm_pos
  have hsubset : F ⊆ prefix_face σ m := by
    intro x hx
    have hx_face' : x ∈ face_set (permutahedron n) c δ := by
      simpa [hF_eq_face] using hx
    exact hsubset_face hx_face'
  have hEq : F = prefix_face σ m :=
    prefix_face_eq_of_incident_facet_subset hn σ hF' hxF m hsubset
  refine ⟨m, hEq, ?_⟩
  intro l hl
  apply prefix_face_injective σ
  exact hl.symm.trans hEq

/-- Helper for Exercise 3.23: once incident facets are classified, the incident-facet set is
contained in the range of the prefix-face family. -/
lemma incident_facet_set_subset_range_prefix_face
    {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n)) :
    {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧ ascending_vector n ∘ σ ∈ F} ⊆
      Set.range (prefix_face σ) := by
  intro F hF
  rcases hF with ⟨hFacet, hxFacet⟩
  -- The classification lemma turns the incident facet into the unique matching prefix facet.
  rcases incident_facet_eq_unique_prefix_face hn σ hFacet hxFacet with ⟨m, hm, -⟩
  exact ⟨m, hm.symm⟩

/-- Exercise 3.23. The permutahedron `Π_n` is simple: every extreme point belongs to exactly as
many facets as the affine dimension of `Π_n`. -/
theorem permutahedron_is_simple
    (n : ℕ) {x : Fin n → ℝ} (hx : x ∈ (permutahedron n).extremePoints ℝ) :
    {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧ x ∈ F}.ncard =
      Module.finrank ℝ (affineSpan ℝ (permutahedron n)).direction := by
  rcases extreme_point_eq_permuted_ascending_vector hx with ⟨σ, rfl⟩
  by_cases hn : n ≤ 1
  · -- In affine dimension `0`, no facet can satisfy the codimension-one equality.
    have hdim : Module.finrank ℝ (affineSpan ℝ (permutahedron n)).direction = 0 := by
      rw [permutahedron_finrank_direction_affineSpan n]
      omega
    have hIncidentEmpty :
        {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧ ascending_vector n ∘ σ ∈ F} = ∅ := by
      ext F
      constructor
      · rintro ⟨hF, -⟩
        rcases (isFacetOf_iff.mp hF) with ⟨-, -, hF_dim⟩
        rw [hdim] at hF_dim
        omega
      · simp
    rw [hIncidentEmpty, Set.ncard_empty, hdim]
  · have hlower :
        n - 1 ≤ {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧
          ascending_vector n ∘ σ ∈ F}.ncard := by
      have hn_two : 2 ≤ n := by
        omega
      have hincident_finite :
          {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧
            ascending_vector n ∘ σ ∈ F}.Finite := by
        refine (Set.finite_range (prefix_face σ)).subset ?_
        intro F hF
        exact incident_facet_set_subset_range_prefix_face hn_two σ hF
      have hsubset :
          Set.range (prefix_face σ) ⊆
            {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧ ascending_vector n ∘ σ ∈ F} := by
        intro F hF
        rcases hF with ⟨m, rfl⟩
        -- Every nontrivial prefix split of the ordered vertex yields an incident facet.
        have hm_pos : 0 < m.1 + 1 := by omega
        have hm_lt : m.1 + 1 < n := by omega
        simpa [prefix_face] using prefix_face_incident σ hm_pos hm_lt
      calc
        n - 1 = (Set.range (prefix_face σ)).ncard := by
          simpa using (Set.ncard_range_of_injective (prefix_face_injective σ)).symm
        _ ≤ {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧
              ascending_vector n ∘ σ ∈ F}.ncard := by
          exact Set.ncard_le_ncard hsubset hincident_finite
    have hn_two : 2 ≤ n := by
      omega
    have hupper :
        {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧
          ascending_vector n ∘ σ ∈ F}.ncard ≤ n - 1 := by
      -- The converse direction is now isolated in `incident_facet_eq_unique_prefix_face`.
      calc
        {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧
            ascending_vector n ∘ σ ∈ F}.ncard
            ≤ (Set.range (prefix_face σ)).ncard :=
              Set.ncard_le_ncard (incident_facet_set_subset_range_prefix_face hn_two σ)
        _ = n - 1 := by
          simpa using Set.ncard_range_of_injective (prefix_face_injective σ)
    have hcount :
        {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧
          ascending_vector n ∘ σ ∈ F}.ncard = n - 1 := by
      omega
    -- The incident-facet count now matches the affine dimension of the permutahedron.
    simpa [permutahedron_finrank_direction_affineSpan n] using hcount

/-- Every extreme point of the `n`th permutahedron belongs to exactly `n - 1` facets. -/
theorem permutahedron_facet_count_of_mem_extremePoints
    (n : ℕ) {x : Fin n → ℝ} (hx : x ∈ (permutahedron n).extremePoints ℝ) :
    {F : Set (Fin n → ℝ) | IsFacetOf (permutahedron n) F ∧ x ∈ F}.ncard = n - 1 := by
  simpa [permutahedron_finrank_direction_affineSpan n] using permutahedron_is_simple n hx
