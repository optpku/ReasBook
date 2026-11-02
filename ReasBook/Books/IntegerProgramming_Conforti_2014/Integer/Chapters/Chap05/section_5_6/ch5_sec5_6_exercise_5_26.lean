import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_25

open scoped BigOperators

-- Primary domain: Chapter 5 lift-and-project closures on finite-coordinate polyhedra in `ℝ^n`.
-- Sampled owner abstractions:
-- * Section 5.4: `coordinate_lift_project_hull`
-- * Theorem 5.22: sequential convexification along prefix coordinates
-- * Exercise 5.25: `kth_lift_project_closure`
-- This file is source-facing: it reuses the Exercise 5.19 polyhedron owner for the common
-- pairwise-inequality polyhedron, introduces the Exercise 5.26 subset-sum relaxation, and
-- uses the Exercise 5.25 closure iteration owner directly.

section Exercise526

variable {n : ℕ}

/-- The nonnegative polyhedron cut out by the subset-sum inequalities
`∑_{j ∈ J} x_j ≤ 1` for all `(k + 2)`-element subsets `J`. -/
def exercise_5_26_subset_sum_relaxation
    (n k : ℕ) : Set (Fin n → ℝ) :=
  {x |
    (∀ i : Fin n, 0 ≤ x i) ∧
      ∀ J : Finset (Fin n), J.card = k + 2 → J.sum x ≤ 1}

/-- Membership in `exercise_5_26_subset_sum_relaxation n k` is exactly nonnegativity together
with the subset-sum inequalities `∑_{j ∈ J} x_j ≤ 1` for all `(k + 2)`-element sets `J`. -/
theorem mem_exercise_5_26_subset_sum_relaxation_iff
    {k : ℕ}
    {x : Fin n → ℝ} :
    x ∈ exercise_5_26_subset_sum_relaxation n k ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ J : Finset (Fin n), J.card = k + 2 → J.sum x ≤ 1 :=
  Iff.rfl

/-- Helper for Exercise 5.26: the source polyhedron from Exercise 5.19 satisfies the pairwise
inequality `x i + x j ≤ 1` for any two distinct indices. -/
lemma exercise_5_26_pairwise_bound_of_ne
    {x : Fin n → ℝ}
    (hx : x ∈ exercise_5_19_polyhedron n)
    {i j : Fin n}
    (hij : i ≠ j) :
    x i + x j ≤ 1 := by
  -- Reorder the pair into the increasing order expected by the source-facing API.
  rw [mem_exercise_5_19_polyhedron_iff] at hx
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · exact hx.2 hij_lt
  · simpa [add_comm] using hx.2 hji_lt

/-- Helper for Exercise 5.26: the fixed-slice relaxation attached to a `k`-subset `J` records
nonnegativity together with the inequalities `∑_{j ∈ J} x_j + x_a + x_b ≤ 1` for distinct
indices outside `J`. -/
def exercise_5_26_pair_relaxation
    (n : ℕ)
    (J : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {x |
    (∀ i : Fin n, 0 ≤ x i) ∧
      ∀ a b : Fin n, a ∉ J → b ∉ J → a ≠ b → J.sum x + x a + x b ≤ 1}

/-- Membership in `exercise_5_26_pair_relaxation n J` is exactly nonnegativity together with the
outside-pair inequalities `∑_{j ∈ J} x_j + x_a + x_b ≤ 1`. -/
theorem mem_exercise_5_26_pair_relaxation_iff
    {J : Finset (Fin n)}
    {x : Fin n → ℝ} :
    x ∈ exercise_5_26_pair_relaxation n J ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ a b : Fin n, a ∉ J → b ∉ J → a ≠ b → J.sum x + x a + x b ≤ 1 :=
  Iff.rfl

/-- Helper for Exercise 5.26: there are two distinct indices outside `J` whenever
`J.card + 2 ≤ n`. -/
lemma exercise_5_26_exists_two_outside_indices
    {J : Finset (Fin n)}
    (hJroom : J.card + 2 ≤ n) :
    ∃ a b : Fin n, a ∉ J ∧ b ∉ J ∧ a ≠ b := by
  have hcompl : 1 < Jᶜ.card := by
    have hcard : Jᶜ.card = n - J.card := by
      simpa using (Finset.card_compl (s := J))
    rw [hcard]
    omega
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hcompl
  exact ⟨a, b, by simpa using ha, by simpa using hb, hab⟩

/-- Helper for Exercise 5.26: every outside index has a distinct partner outside `J` whenever
`J.card + 2 ≤ n`. -/
lemma exercise_5_26_exists_outside_partner
    {J : Finset (Fin n)}
    (hJroom : J.card + 2 ≤ n)
    {a : Fin n}
    (ha : a ∉ J) :
    ∃ b : Fin n, b ∉ J ∧ b ≠ a := by
  have hcompl : 1 < Jᶜ.card := by
    have hcard : Jᶜ.card = n - J.card := by
      simpa using (Finset.card_compl (s := J))
    rw [hcard]
    omega
  have ha_compl : a ∈ Jᶜ := by
    simpa using ha
  have herase_pos : 0 < (Jᶜ.erase a).card := by
    have hcard : (Jᶜ.erase a).card + 1 = Jᶜ.card := by
      simpa [ha_compl] using Finset.card_erase_add_one ha_compl
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp herase_pos
  exact ⟨b, by simpa using Finset.mem_of_mem_erase hb, Finset.ne_of_mem_erase hb⟩

/-- Helper for Exercise 5.26: the zero vector belongs to every binary slice. -/
lemma exercise_5_26_zero_mem_binarySlice
    (J : Finset (Fin n)) :
    (0 : Fin n → ℝ) ∈
      binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J := by
  -- The zero vector satisfies the source polyhedron and every required binary condition.
  rw [mem_binary_prefix_points_on_subset_iff, mem_exercise_5_19_polyhedron_iff]
  simp

/-- Helper for Exercise 5.26: every unit vector is a point of the corresponding binary slice. -/
lemma exercise_5_26_single_mem_binarySlice
    (J : Finset (Fin n))
    (j : Fin n) :
    Pi.single j (1 : ℝ) ∈
      binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J := by
  -- Unit vectors satisfy the source polyhedron, and their `J`-coordinates are automatically
  -- binary.
  rw [mem_binary_prefix_points_on_subset_iff, mem_exercise_5_19_polyhedron_iff]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Pi.single_eq_of_ne hij]
    · intro a b hab
      by_cases haj : a = j
      · subst haj
        simp [Pi.single_eq_of_ne (ne_of_gt hab)]
      · by_cases hbj : b = j
        · subst hbj
          simp [Pi.single_eq_of_ne (ne_of_lt hab)]
        · simp [Pi.single_eq_of_ne haj, Pi.single_eq_of_ne hbj]
  · intro i hiJ
    by_cases hij : i = j
    · right
      subst hij
      simp
    · left
      simp [Pi.single_eq_of_ne hij]

/-- Helper for Exercise 5.26: the fixed-slice relaxation is convex because its defining
nonnegativity and outside-pair inequalities are preserved by convex combinations. -/
lemma exercise_5_26_pairRelaxation_convex
    (J : Finset (Fin n)) :
    Convex ℝ (exercise_5_26_pair_relaxation n J) := by
  intro x hx y hy a c ha hc hac
  rw [mem_exercise_5_26_pair_relaxation_iff] at hx hy ⊢
  refine ⟨?_, ?_⟩
  · -- Coordinatewise nonnegativity is stable under convex combinations.
    intro i
    simp [Pi.add_apply, Pi.smul_apply, add_nonneg, mul_nonneg, ha, hc, hx.1 i, hy.1 i]
  · -- The outside-pair inequalities combine linearly as well.
    intro i j hiJ hjJ hij
    have hsum :
        J.sum (a • x + c • y) = a * J.sum x + c * J.sum y := by
      simp [Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, Finset.mul_sum]
    calc
      J.sum (a • x + c • y) + (a • x + c • y) i + (a • x + c • y) j
          = a * (J.sum x + x i + x j) + c * (J.sum y + y i + y j) := by
              rw [hsum]
              simp [Pi.add_apply, Pi.smul_apply]
              ring
      _ ≤ a * 1 + c * 1 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hx.2 i j hiJ hjJ hij) ha)
              (mul_le_mul_of_nonneg_left (hy.2 i j hiJ hjJ hij) hc)
      _ = 1 := by
            linarith

/-- Helper for Exercise 5.26: the outside-pair inequalities force `∑_{j ∈ J} x_j ≤ 1` whenever
there are at least two indices outside `J`. -/
lemma exercise_5_26_pairRelaxation_sum_le_one
    {J : Finset (Fin n)}
    {x : Fin n → ℝ}
    (hx : x ∈ exercise_5_26_pair_relaxation n J)
    (hJroom : J.card + 2 ≤ n) :
    J.sum x ≤ 1 := by
  rw [mem_exercise_5_26_pair_relaxation_iff] at hx
  obtain ⟨a, b, ha, hb, hab⟩ := exercise_5_26_exists_two_outside_indices hJroom
  -- Use one outside pair and discard its nonnegative coordinates.
  have hpair : J.sum x + x a + x b ≤ 1 := hx.2 a b ha hb hab
  linarith [hx.1 a, hx.1 b, hpair]

/-- Helper for Exercise 5.26: any nonnegative vector supported on `J` with total `J`-mass `1`
is a convex combination of the unit vectors indexed by `J`, hence belongs to the binary-slice
convex hull. -/
lemma exercise_5_26_supportedOnJ_mem_convexHull_binarySlice
    (J : Finset (Fin n))
    {x : Fin n → ℝ}
    (hx_nonneg : ∀ i : Fin n, 0 ≤ x i)
    (hx_outside : ∀ i : Fin n, i ∉ J → x i = 0)
    (hx_sum : J.sum x = 1) :
    x ∈ convexHull ℝ
      (binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J) := by
  classical
  -- Use the `J`-indexed unit vectors as the barycentric generators.
  refine mem_convexHull_of_exists_fintype
    (w := fun i : {i : Fin n // i ∈ J} ↦ x i.1)
    (z := fun i : {i : Fin n // i ∈ J} ↦ (Pi.single i.1 (1 : ℝ) : Fin n → ℝ))
    ?_ ?_ ?_ ?_
  · intro i
    exact hx_nonneg i.1
  · calc
      ∑ i : {i : Fin n // i ∈ J}, x i.1 = J.sum x := by
            simpa using (Finset.sum_attach J (fun i : Fin n ↦ x i))
      _ = 1 := hx_sum
  · intro i
    exact exercise_5_26_single_mem_binarySlice J i.1
  · -- The weighted unit-vector sum recovers the original vector on and off `J`.
    ext k
    by_cases hk : k ∈ J
    · let kk : {i : Fin n // i ∈ J} := ⟨k, hk⟩
      rw [Finset.sum_apply, Finset.sum_eq_single kk]
      · simp [kk]
      · intro i _ hik
        have hik' : i.1 ≠ k := by
          intro hEq
          apply hik
          exact Subtype.ext (by simpa [kk] using hEq)
        rw [Pi.smul_apply]
        simp [hik']
      · intro hkk
        exact (hkk (by simp [kk])).elim
    · have hsum_zero :
          (∑ i : {i : Fin n // i ∈ J}, x i.1 • Pi.single i.1 (1 : ℝ)) k = 0 := by
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero ?_
        intro i _
        have hik : i.1 ≠ k := by
          intro hEq
          exact hk (by simpa [hEq] using i.2)
        rw [Pi.smul_apply]
        simp [hik]
      simpa [hx_outside k hk] using hsum_zero

/-- Helper for Exercise 5.26: after normalizing by the remaining mass `1 - ∑_{j ∈ J} x_j`, the
coordinates outside `J` form a point of the zero-on-`J` binary slice. -/
lemma exercise_5_26_pairRelaxation_normalizedRemainder_mem_binarySlice
    {J : Finset (Fin n)}
    {x : Fin n → ℝ}
    (hx : x ∈ exercise_5_26_pair_relaxation n J)
    (hJroom : J.card + 2 ≤ n)
    (hs : J.sum x < 1) :
    (fun i : Fin n ↦ if i ∈ J then 0 else x i / (1 - J.sum x)) ∈
      binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J := by
  rw [mem_binary_prefix_points_on_subset_iff, mem_exercise_5_19_polyhedron_iff]
  have hden : 0 < 1 - J.sum x := by
    linarith
  have houtside_bound :
      ∀ a : Fin n, a ∉ J → x a ≤ 1 - J.sum x := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := exercise_5_26_exists_outside_partner hJroom ha
    have hpair : J.sum x + x a + x b ≤ 1 := hx.2 a b ha hb hba.symm
    linarith [hx.1 b, hpair]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- All normalized coordinates are nonnegative.
      intro i
      by_cases hiJ : i ∈ J
      · simp [hiJ]
      · simp [hiJ, div_nonneg (hx.1 i) hden.le]
    · -- Mixed pairs use the one-coordinate outside bound; outside pairs use the defining pair
      -- inequality directly.
      intro i j hij
      by_cases hiJ : i ∈ J
      · by_cases hjJ : j ∈ J
        · simp [hiJ, hjJ]
        · have hj_bound : x j ≤ 1 - J.sum x := houtside_bound j hjJ
          have hratio : x j / (1 - J.sum x) ≤ 1 := by
            rw [div_le_iff₀ hden]
            linarith
          simpa [hiJ, hjJ] using hratio
      · by_cases hjJ : j ∈ J
        · have hi_bound : x i ≤ 1 - J.sum x := houtside_bound i hiJ
          have hratio : x i / (1 - J.sum x) ≤ 1 := by
            rw [div_le_iff₀ hden]
            linarith
          simpa [hiJ, hjJ, add_comm] using hratio
        · have hpair : J.sum x + x i + x j ≤ 1 := hx.2 i j hiJ hjJ hij.ne
          have hratio : x i / (1 - J.sum x) + x j / (1 - J.sum x) ≤ 1 := by
            rw [← add_div]
            rw [div_le_iff₀ hden]
            linarith
          simpa [hiJ, hjJ] using hratio
  · -- The normalized remainder is zero on `J`.
    intro i hiJ
    left
    simp [hiJ]

/-- Helper for Exercise 5.26: every point of the fixed-slice pair relaxation lies in the convex
hull of the corresponding binary slice. -/
lemma exercise_5_26_pairRelaxation_mem_convexHull_binarySlice
    {J : Finset (Fin n)}
    {x : Fin n → ℝ}
    (hx : x ∈ exercise_5_26_pair_relaxation n J)
    (hJroom : J.card + 2 ≤ n) :
    x ∈ convexHull ℝ
      (binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J) := by
  let s : ℝ := J.sum x
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun i _ ↦ hx.1 i
  have hs_le : s ≤ 1 := by
    simpa [s] using exercise_5_26_pairRelaxation_sum_le_one hx hJroom
  by_cases hs_zero : s = 0
  · -- When the `J`-mass is zero, the normalized remainder is just `x` itself.
    have hy_mem :
        (fun i : Fin n ↦ if i ∈ J then 0 else x i / (1 - J.sum x)) ∈
          binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J := by
      apply exercise_5_26_pairRelaxation_normalizedRemainder_mem_binarySlice hx hJroom
      dsimp [s] at hs_zero ⊢
      linarith [hs_le]
    have hx_eq :
        x = fun i : Fin n ↦ if i ∈ J then 0 else x i / (1 - J.sum x) := by
      ext i
      by_cases hiJ : i ∈ J
      · have hxi_le : x i ≤ J.sum x := by
          exact Finset.single_le_sum (fun j _ ↦ hx.1 j) hiJ
        have hxi_zero : x i = 0 := by
          dsimp [s] at hs_zero
          have hxi_nonpos : x i ≤ 0 := by
            linarith
          exact le_antisymm hxi_nonpos (hx.1 i)
        simp [hiJ, hxi_zero]
      · dsimp [s] at hs_zero
        simp [hiJ, hs_zero]
    rw [hx_eq]
    exact subset_convexHull ℝ _ hy_mem
  · by_cases hs_one : s = 1
    · -- Full `J`-mass forces every outside coordinate to vanish, so `x` is already a convex
      -- combination of the `J`-unit vectors.
      have hx_outside : ∀ i : Fin n, i ∉ J → x i = 0 := by
        intro i hiJ
        obtain ⟨b, hb, hbi⟩ := exercise_5_26_exists_outside_partner hJroom hiJ
        have hpair : J.sum x + x i + x b ≤ 1 := hx.2 i b hiJ hb hbi.symm
        dsimp [s] at hs_one
        linarith [hx.1 i, hx.1 b, hpair]
      exact exercise_5_26_supportedOnJ_mem_convexHull_binarySlice J hx.1 hx_outside
        (by dsimp [s] at hs_one; simpa [s] using hs_one)
    · -- Split `x` into the normalized zero-on-`J` remainder plus a `J`-supported simplex point.
      have hs_lt : s < 1 := by
        exact lt_of_le_of_ne hs_le hs_one
      have hs_pos : 0 < s := by
        exact lt_of_le_of_ne hs_nonneg (Ne.symm hs_zero)
      let y : Fin n → ℝ := fun i ↦ if i ∈ J then 0 else x i / (1 - s)
      let u : Fin n → ℝ := fun i ↦ if i ∈ J then x i / s else 0
      have hy_mem :
          y ∈ binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J := by
        dsimp [y, s]
        exact exercise_5_26_pairRelaxation_normalizedRemainder_mem_binarySlice hx hJroom hs_lt
      have hu_mem :
          u ∈ convexHull ℝ
            (binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J) := by
        apply exercise_5_26_supportedOnJ_mem_convexHull_binarySlice J
        · intro i
          by_cases hiJ : i ∈ J
          · simp [u, hiJ, div_nonneg (hx.1 i) hs_pos.le]
          · simp [u, hiJ]
        · intro i hiJ
          simp [u, hiJ]
        · calc
            J.sum u = J.sum (fun j ↦ x j / s) := by
                        refine Finset.sum_congr rfl ?_
                        intro j hj
                        simp [u, hj]
            _ = J.sum x / s := by
                  rw [Finset.sum_div]
            _ = 1 := by
                  dsimp [s]
                  simpa [hs_pos.ne']
      have hy_hull :
          y ∈ convexHull ℝ
            (binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J) :=
        subset_convexHull ℝ _ hy_mem
      have hx_combo :
          (1 - s) • y + s • u = x := by
        ext i
        by_cases hiJ : i ∈ J
        · simp [y, u, hiJ]
          field_simp [hs_pos.ne']
        · have hden : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs_one)
          simp [y, u, hiJ]
          field_simp [hden]
      have hcombo_mem :
          (1 - s) • y + s • u ∈ convexHull ℝ
            (binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J) := by
        exact (convex_convexHull ℝ _) hy_hull hu_mem (by linarith) hs_pos.le (by linarith)
      simpa [hx_combo] using hcombo_mem

/-- Helper for Exercise 5.26: removing two distinct elements from a `(k + 2)`-subset leaves a
`k`-subset, and the original sum splits into the remaining sum plus the two removed terms. -/
lemma exercise_5_26_removeTwoElements_card_bridge
    {k : ℕ}
    {L : Finset (Fin n)}
    {a b : Fin n}
    (ha : a ∈ L)
    (hb : b ∈ L)
    (hab : a ≠ b)
    (hL : L.card = k + 2) :
    (((L.erase a).erase b).card = k) ∧
      (((L.erase a).erase b) ⊆ L) ∧
  ∀ x : Fin n → ℝ, L.sum x = ((L.erase a).erase b).sum x + x a + x b := by
  have hb_erase : b ∈ L.erase a := by
    exact Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hcard_a : (L.erase a).card + 1 = L.card := by
    simpa [ha] using Finset.card_erase_add_one ha
  have hcard_b : ((L.erase a).erase b).card + 1 = (L.erase a).card := by
    simpa [hb_erase] using Finset.card_erase_add_one hb_erase
  refine ⟨?_, ?_, ?_⟩
  · omega
  · intro i hi
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  · intro x
    calc
      L.sum x = (L.erase a).sum x + x a := by
            simpa using (Finset.sum_erase_add (s := L) (f := x) ha).symm
      _ = ((L.erase a).erase b).sum x + x b + x a := by
            simpa using (Finset.sum_erase_add (s := L.erase a) (f := x) hb_erase).symm
      _ = ((L.erase a).erase b).sum x + x a + x b := by
            ring

/-- Helper for Exercise 5.26: the convex hull of a fixed binary slice is exactly the fixed-slice
outside-pair relaxation. -/
lemma exercise_5_26_binarySliceConvexHull_eq_pairRelaxation
    (J : Finset (Fin n))
    (hJroom : J.card + 2 ≤ n) :
    convexHull ℝ
        (binary_prefix_points_on_subset (Nat.le_refl n) (exercise_5_19_polyhedron n) J) =
      exercise_5_26_pair_relaxation n J := by
  -- Route correction: separate the easy generator inclusion from the reverse barycentric
  -- decomposition instead of mixing both jobs in one procedural proof.
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (exercise_5_26_pairRelaxation_convex (n := n) J)
    intro x hx
    rw [mem_binary_prefix_points_on_subset_iff, mem_exercise_5_19_polyhedron_iff] at hx
    rw [mem_exercise_5_26_pair_relaxation_iff]
    refine ⟨hx.1.1, ?_⟩
    intro a b ha hb hab
    by_cases hOne : ∃ j : Fin n, j ∈ J ∧ x j = 1
    · rcases hOne with ⟨j, hjJ, hj_one⟩
      have hxa_zero : x a = 0 := by
        have hpair := exercise_5_26_pairwise_bound_of_ne hx.1 (show j ≠ a by
          intro hEq
          exact ha (hEq ▸ hjJ))
        linarith [hx.1.1 a, hpair, hj_one]
      have hxb_zero : x b = 0 := by
        have hpair := exercise_5_26_pairwise_bound_of_ne hx.1 (show j ≠ b by
          intro hEq
          exact hb (hEq ▸ hjJ))
        linarith [hx.1.1 b, hpair, hj_one]
      have hJ_sum : J.sum x = 1 := by
        rw [Finset.sum_eq_single j]
        · simp [hj_one]
        · intro i hiJ hij
          have hxi_zero : x i = 0 := by
            have hpair := exercise_5_26_pairwise_bound_of_ne hx.1 (show j ≠ i by
              exact hij.symm)
            linarith [hx.1.1 i, hpair, hj_one]
          simp [hxi_zero]
        · intro hj_not_mem
          exact (hj_not_mem hjJ).elim
      linarith [hJ_sum, hxa_zero, hxb_zero]
    · have hJ_sum : J.sum x = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hiJ
        rcases hx.2 i hiJ with hxi_zero | hxi_one
        · exact hxi_zero
        · exfalso
          exact hOne ⟨i, hiJ, hxi_one⟩
      have hpair := exercise_5_26_pairwise_bound_of_ne hx.1 hab
      linarith [hpair, hJ_sum]
  · intro x hx
    exact exercise_5_26_pairRelaxation_mem_convexHull_binarySlice hx hJroom

/-- Helper for Exercise 5.26: intersecting the fixed-slice pair relaxations over all `k`-subsets
recovers the global `(k + 2)`-subset-sum relaxation. -/
lemma exercise_5_26_iInter_pairRelaxation_eq_subset_sum_relaxation
    (n k : ℕ)
    (hk : k + 2 ≤ n) :
    (⋂ J : {J : Finset (Fin n) // J.card = k},
      exercise_5_26_pair_relaxation n J.1) =
      exercise_5_26_subset_sum_relaxation n k := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iInter] at hx
    rw [mem_exercise_5_26_subset_sum_relaxation_iff]
    have hk_le : k ≤ n := by
      omega
    have hk_univ : k ≤ (Finset.univ : Finset (Fin n)).card := by
      simpa using hk_le
    obtain ⟨J0, -, hJ0card⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) hk_univ
    refine ⟨(mem_exercise_5_26_pair_relaxation_iff.mp (hx ⟨J0, hJ0card⟩)).1, ?_⟩
    intro L hL
    have hL_two : 1 < L.card := by
      omega
    obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hL_two
    rcases exercise_5_26_removeTwoElements_card_bridge
      (L := L) (a := a) (b := b) (k := k) (ha := ha) (hb := hb) (hab := hab) (hL := hL) with
      ⟨hcard, -, hsum⟩
    let J : Finset (Fin n) := (L.erase a).erase b
    have hpair :
        J.sum x + x a + x b ≤ 1 := by
      have hxJ := mem_exercise_5_26_pair_relaxation_iff.mp (hx ⟨J, hcard⟩)
      exact hxJ.2 a b (by simp [J]) (by simp [J]) hab
    have hsumL : L.sum x = J.sum x + x a + x b := by
      simpa [J] using hsum x
    rw [hsumL]
    exact hpair
  · intro hx
    rw [mem_exercise_5_26_subset_sum_relaxation_iff] at hx
    simp only [Set.mem_iInter]
    intro J
    rcases J with ⟨J, hJcard⟩
    rw [mem_exercise_5_26_pair_relaxation_iff]
    refine ⟨hx.1, ?_⟩
    intro a b ha hb hab
    have hcard_insert : (insert a (insert b J)).card = k + 2 := by
      simp [ha, hb, hab, hJcard]
    have hineq : (insert a (insert b J)).sum x ≤ 1 := hx.2 (insert a (insert b J)) hcard_insert
    have hsum_insert : (insert a (insert b J)).sum x = J.sum x + x a + x b := by
      rw [Finset.sum_insert (by simp [ha, hab]), Finset.sum_insert hb]
      ring
    rw [hsum_insert] at hineq
    exact hineq

/-- Helper for Exercise 5.26: the pairwise-inequality polyhedron from Exercise 5.19 is a
polyhedron in the Chapter 3 sense. -/
lemma exercise_5_26_pairwisePolyhedron_isPolyhedron
    (n : ℕ) :
    is_polyhedron (exercise_5_19_polyhedron n) := by
  let nonnegMatrix : Matrix (Fin n) (Fin n) ℝ :=
    fun i ↦ -Pi.single i (1 : ℝ)
  let pairMatrix : Matrix (Fin (n * n)) (Fin n) ℝ :=
    fun p ↦
      if h : p.divNat < p.modNat then
        fun k ↦ (if k = p.divNat then (1 : ℝ) else 0) + if k = p.modNat then (1 : ℝ) else 0
      else
        0
  let pairRhs : Fin (n * n) → ℝ :=
    fun p ↦ if p.divNat < p.modNat then 1 else 0
  -- Present the pairwise system by stacking the nonnegativity rows with all ordered pair rows.
  refine (is_polyhedron_iff).2
    ⟨n + n * n, Fin.append nonnegMatrix pairMatrix, Fin.append 0 pairRhs, ?_⟩
  ext x
  have hsingle_row (i : Fin n) :
      ∑ k, ((Pi.single i (1 : ℝ) : Fin n → ℝ) k) * x k = x i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [Pi.single_eq_of_ne hki]
    · intro hi
      exact (hi (by simp)).elim
  have hpair_row (p : Fin (n * n)) :
      ∑ k, ((if k = p.divNat then (1 : ℝ) else 0) + if k = p.modNat then (1 : ℝ) else 0) * x k =
        x p.divNat + x p.modNat := by
    calc
      ∑ k, ((if k = p.divNat then (1 : ℝ) else 0) + if k = p.modNat then (1 : ℝ) else 0) * x k
          = ∑ k,
              ((if k = p.divNat then (1 : ℝ) else 0) * x k +
                (if k = p.modNat then (1 : ℝ) else 0) * x k) := by
                refine Finset.sum_congr rfl ?_
                intro k _
                ring
      _ = (∑ k, (if k = p.divNat then (1 : ℝ) else 0) * x k) +
            ∑ k, (if k = p.modNat then (1 : ℝ) else 0) * x k := by
              rw [Finset.sum_add_distrib]
      _ = x p.divNat + x p.modNat := by
            simp
  constructor
  · intro hx
    rw [mem_exercise_5_19_polyhedron_iff] at hx
    rw [mem_polyhedron_le_set_iff]
    intro r
    refine Fin.addCases ?_ ?_ r
    · intro i
      -- The first block is exactly the coordinatewise nonnegativity system `-x_i ≤ 0`.
      simpa [nonnegMatrix, Matrix.mulVec, dotProduct, hsingle_row i] using hx.1 i
    · intro p
      -- The second block keeps the rows corresponding to `i < j` and zeros out the rest.
      by_cases hij : p.divNat < p.modNat
      · simpa [pairMatrix, pairRhs, hij, Matrix.mulVec, dotProduct, hpair_row p] using hx.2 hij
      · simp [pairMatrix, pairRhs, hij, Matrix.mulVec, dotProduct]
  · intro hx
    rw [mem_polyhedron_le_set_iff] at hx
    rw [mem_exercise_5_19_polyhedron_iff]
    refine ⟨?_, ?_⟩
    · intro i
      simpa [nonnegMatrix, Matrix.mulVec, dotProduct, hsingle_row i] using
        hx (Fin.castAdd (n * n) i)
    · intro i j hij
      have hdiv :
          (finProdFinEquiv (i, j)).divNat = i := by
        simpa [finProdFinEquiv] using congrArg Prod.fst (finProdFinEquiv.left_inv (i, j))
      have hmod :
          (finProdFinEquiv (i, j)).modNat = j := by
        simpa [finProdFinEquiv] using congrArg Prod.snd (finProdFinEquiv.left_inv (i, j))
      have hij' : (finProdFinEquiv (i, j)).divNat < (finProdFinEquiv (i, j)).modNat := by
        simpa [hdiv, hmod] using hij
      have hij_row :
          x i + x j ≤ 1 := by
        have hxrow :
            ∑ k,
                ((if k = i then (1 : ℝ) else 0) + if k = j then (1 : ℝ) else 0) * x k ≤ 1 := by
          simpa [pairMatrix, pairRhs, hij, Matrix.mulVec, dotProduct, hdiv, hmod] using
            hx (Fin.natAdd n (finProdFinEquiv (i, j)))
        have hrow_eq :
            ∑ k,
                ((if k = i then (1 : ℝ) else 0) + if k = j then (1 : ℝ) else 0) * x k =
              x i + x j := by
          simpa [hdiv, hmod] using hpair_row (finProdFinEquiv (i, j))
        rw [hrow_eq] at hxrow
        exact hxrow
      exact hij_row

/-- Exercise 5.26. For `k + 2 ≤ n`, the `k`th lift-and-project closure of
`P = {x ∈ ℝ_+^n | x_i + x_j ≤ 1 for all 1 ≤ i < j ≤ n}` is exactly the set
`{x ∈ ℝ_+^n | ∑_{j ∈ J} x_j ≤ 1 for all J with |J| = k + 2}`. -/
theorem exercise_5_26_kth_lift_project_closure_eq_subset_sum_relaxation
    (n k : ℕ)
    (hk : k + 2 ≤ n) :
    kth_lift_project_closure (Nat.le_refl n) (exercise_5_19_polyhedron n) k =
      exercise_5_26_subset_sum_relaxation n k := by
  have hk_le : k ≤ n := by
    omega
  have hpoly : is_polyhedron (exercise_5_19_polyhedron n) :=
    exercise_5_26_pairwisePolyhedron_isPolyhedron n
  calc
    kth_lift_project_closure (Nat.le_refl n) (exercise_5_19_polyhedron n) k
        =
          ⋂ J : {J : Finset (Fin n) // J.card = k},
            convexHull ℝ
              (binary_prefix_points_on_subset
                (Nat.le_refl n) (exercise_5_19_polyhedron n) J.1) := by
              exact kth_lift_project_closure_eq_iInter_convexHull_binary_on_k_subsets
                (Nat.le_refl n) (exercise_5_19_polyhedron n) hpoly k hk_le
    _ =
          ⋂ J : {J : Finset (Fin n) // J.card = k},
            exercise_5_26_pair_relaxation n J.1 := by
              ext x
              simp only [Set.mem_iInter]
              constructor
              · intro hx J
                simpa [exercise_5_26_binarySliceConvexHull_eq_pairRelaxation
                  (n := n) J.1 (by simpa [J.2] using hk)]
                  using hx J
              · intro hx J
                simpa [exercise_5_26_binarySliceConvexHull_eq_pairRelaxation
                  (n := n) J.1 (by simpa [J.2] using hk)]
                  using hx J
    _ = exercise_5_26_subset_sum_relaxation n k :=
          exercise_5_26_iInter_pairRelaxation_eq_subset_sum_relaxation n k hk

/-- Membership in the `k`th lift-and-project closure from Exercise 5.26 is exactly
nonnegativity together with the subset-sum inequalities `∑_{j ∈ J} x_j ≤ 1` for all
`(k + 2)`-element sets `J`. -/
theorem mem_exercise_5_26_kth_lift_project_closure_iff
    {k : ℕ}
    (hk : k + 2 ≤ n)
    {x : Fin n → ℝ} :
    x ∈ kth_lift_project_closure (Nat.le_refl n) (exercise_5_19_polyhedron n) k ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ J : Finset (Fin n), J.card = k + 2 → J.sum x ≤ 1 := by
  rw [exercise_5_26_kth_lift_project_closure_eq_subset_sum_relaxation n k hk]
  exact mem_exercise_5_26_subset_sum_relaxation_iff

end Exercise526
