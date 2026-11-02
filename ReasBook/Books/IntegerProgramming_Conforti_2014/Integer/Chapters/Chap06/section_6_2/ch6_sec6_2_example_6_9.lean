import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_20
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free

open scoped BigOperators

-- This example specializes the Section 6.2 corner/intersection-cut owner API from
-- `ch6_sec6_2_theorem_6_5` to split sets, while reusing the chapter's canonical lattice-free
-- owners from Theorem 6.18.

noncomputable section

section Example69

variable {n p k : ℕ}

/-- The split linear form `πx` on `ℝ^p`. -/
def split_linear_form
    (π : Fin p → ℤ)
    (x : Fin p → ℝ) : ℝ :=
  ∑ i : Fin p, (π i : ℝ) * x i

/-- The split linear form `πx` on `ℝ^n`, using only the first `p` coordinates. -/
def split_prefix_linear_form
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin p, (π i : ℝ) * x (Fin.castLE hpn i)

/-- The strip `K = {x ∈ ℝ^p : π₀ ≤ πx ≤ π₀ + 1}` cut out by an integral split pair
`(π, π₀)`. -/
def split_slab
    (π : Fin p → ℤ)
    (π0 : ℤ) : Set (Fin p → ℝ) :=
  {x | (π0 : ℝ) ≤ split_linear_form π x ∧ split_linear_form π x ≤ (π0 : ℝ) + 1}

/-- Membership in `split_slab π π0` is exactly the displayed double inequality
`π₀ ≤ πx ≤ π₀ + 1`. -/
theorem mem_split_slab_iff
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (x : Fin p → ℝ) :
    x ∈ split_slab π π0 ↔
      (π0 : ℝ) ≤ split_linear_form π x ∧ split_linear_form π x ≤ (π0 : ℝ) + 1 :=
  Iff.rfl

/-- The split set `C = K × ℝ^(n - p)` written directly in `ℝ^n` by using the split inequality on
the first `p` coordinates. -/
def split_set
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ) : Set (Fin n → ℝ) :=
  {x | (π0 : ℝ) ≤ split_prefix_linear_form hpn π x ∧
      split_prefix_linear_form hpn π x ≤ (π0 : ℝ) + 1}

/-- Membership in `split_set hpn π π0` is exactly the displayed split inequality on the first
`p` coordinates. -/
theorem mem_split_set_iff
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (x : Fin n → ℝ) :
    x ∈ split_set hpn π π0 ↔
      (π0 : ℝ) ≤ split_prefix_linear_form hpn π x ∧
        split_prefix_linear_form hpn π x ≤ (π0 : ℝ) + 1 :=
  Iff.rfl

/-- The quantity `ε = π x̄ - π₀` attached to a point `x̄` lying strictly between the two split
hyperplanes. -/
def split_epsilon
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ) : ℝ :=
  split_prefix_linear_form hpn π xbar - (π0 : ℝ)

/-- `split_epsilon hpn π π0 xbar` unfolds to `π x̄ - π₀`. -/
theorem split_epsilon_def
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ) :
    split_epsilon hpn π π0 xbar =
      split_prefix_linear_form hpn π xbar - (π0 : ℝ) :=
  rfl

/-- Helper for Example 6.9: the split linear form distributes over affine combinations. -/
theorem splitLinearForm_smul_add
    (π : Fin p → ℤ)
    (a b : ℝ)
    (x y : Fin p → ℝ) :
    split_linear_form π (a • x + b • y) =
      a * split_linear_form π x + b * split_linear_form π y := by
  -- Expand the finite sum coordinatewise and collect the scalar terms.
  simp [split_linear_form, Finset.mul_sum, Finset.sum_add_distrib, add_mul, mul_comm, mul_assoc]

/-- Helper for Example 6.9: the prefix split linear form distributes over translated ray
directions. -/
theorem splitPrefixLinearForm_add_smul
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (x r : Fin n → ℝ)
    (t : ℝ) :
    split_prefix_linear_form hpn π (x + t • r) =
      split_prefix_linear_form hpn π x + t * split_prefix_linear_form hpn π r := by
  -- Expand the finite sum coordinatewise and collect the scalar terms.
  simp [split_prefix_linear_form, Finset.mul_sum, Finset.sum_add_distrib,
    add_mul, mul_comm, mul_assoc]

/-- Helper for Example 6.9: perturbing a slab point along one coordinate changes the split linear
form by that coordinate's coefficient times the step size. -/
theorem splitLinearForm_add_smul_single
    (π : Fin p → ℤ)
    (x : Fin p → ℝ)
    (i : Fin p)
    (t : ℝ) :
    split_linear_form π (x + t • Pi.single i (1 : ℝ)) =
      split_linear_form π x + t * (π i : ℝ) := by
  -- Only the `i`th summand survives the `Pi.single` perturbation.
  have hsingle : split_linear_form π (Pi.single i (1 : ℝ)) = (π i : ℝ) := by
    rw [split_linear_form, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  calc
    split_linear_form π (x + t • Pi.single i (1 : ℝ)) =
        split_linear_form π x + t * split_linear_form π (Pi.single i (1 : ℝ)) := by
          simpa using splitLinearForm_smul_add π 1 t x (Pi.single i (1 : ℝ))
    _ = split_linear_form π x + t * (π i : ℝ) := by rw [hsingle]

/-- Helper for Example 6.9: perturbing a split-set point along one prefix coordinate changes the
prefix split linear form by that coordinate's coefficient times the step size. -/
theorem splitPrefixLinearForm_add_smul_single
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (x : Fin n → ℝ)
    (i : Fin p)
    (t : ℝ) :
    split_prefix_linear_form hpn π (x + t • Pi.single (Fin.castLE hpn i) (1 : ℝ)) =
      split_prefix_linear_form hpn π x + t * (π i : ℝ) := by
  -- Only the `i`th prefix summand survives the `Pi.single` perturbation.
  have hsingle :
      split_prefix_linear_form hpn π (Pi.single (Fin.castLE hpn i) (1 : ℝ)) = (π i : ℝ) := by
    rw [split_prefix_linear_form, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have hcast : Fin.castLE hpn j ≠ Fin.castLE hpn i := by
        intro hEq
        exact hj ((Fin.castLE_injective hpn) hEq)
      simp [hcast]
    · simp
  calc
    split_prefix_linear_form hpn π (x + t • Pi.single (Fin.castLE hpn i) (1 : ℝ)) =
        split_prefix_linear_form hpn π x +
          t * split_prefix_linear_form hpn π (Pi.single (Fin.castLE hpn i) (1 : ℝ)) := by
            rw [splitPrefixLinearForm_add_smul]
    _ = split_prefix_linear_form hpn π x + t * (π i : ℝ) := by rw [hsingle]

/-- Helper for Example 6.9: a boundary point of a split slab with nonzero normal cannot lie in
its interior. -/
lemma splitSlabBoundaryValue_not_mem_interior
    (π : Fin p → ℤ)
    (hπ : π ≠ 0)
    (π0 : ℤ)
    (x : Fin p → ℝ)
    (hx :
      split_linear_form π x = (π0 : ℝ) ∨
        split_linear_form π x = (π0 : ℝ) + 1) :
    x ∉ interior (split_slab π π0) := by
  intro hxint
  classical
  have hnonzero_coord : ∃ i : Fin p, π i ≠ 0 := by
    by_contra h
    apply hπ
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hnonzero_coord
  have hiR : (π i : ℝ) ≠ 0 := by
    exact_mod_cast hi
  have hpreimage :
      {t : ℝ | x + t • Pi.single i (1 : ℝ) ∈ interior (split_slab π π0)} ∈ nhds (0 : ℝ) := by
    have hcont : Continuous fun t : ℝ ↦ x + t • Pi.single i (1 : ℝ) := by
      continuity
    simpa using
      hcont.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hxint)
  rcases Metric.mem_nhds_iff.mp hpreimage with ⟨ε, hεpos, hεsubset⟩
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact half_pos hεpos
  rcases hx with hx | hx
  · rcases lt_or_gt_of_ne hiR with hneg | hpos
    · have hy_mem : x + δ • Pi.single i (1 : ℝ) ∈ split_slab π π0 := by
        exact interior_subset <| hεsubset <| by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos]
          dsimp [δ]
          exact half_lt_self hεpos
      rw [mem_split_slab_iff] at hy_mem
      have hlt :
          split_linear_form π (x + δ • Pi.single i (1 : ℝ)) < (π0 : ℝ) := by
        calc
          split_linear_form π (x + δ • Pi.single i (1 : ℝ)) =
              split_linear_form π x + δ * (π i : ℝ) := by
                rw [splitLinearForm_add_smul_single]
          _ = (π0 : ℝ) + δ * (π i : ℝ) := by rw [hx]
          _ < (π0 : ℝ) := by nlinarith
      exact (not_le_of_gt hlt) hy_mem.1
    · have hy_mem : x + (-δ) • Pi.single i (1 : ℝ) ∈ split_slab π π0 := by
        exact interior_subset <| hεsubset <| by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg (neg_neg_iff_pos.mpr hδpos)]
          simpa [δ] using half_lt_self hεpos
      rw [mem_split_slab_iff] at hy_mem
      have hlt :
          split_linear_form π (x + (-δ) • Pi.single i (1 : ℝ)) < (π0 : ℝ) := by
        calc
          split_linear_form π (x + (-δ) • Pi.single i (1 : ℝ)) =
              split_linear_form π x + (-δ) * (π i : ℝ) := by
                rw [splitLinearForm_add_smul_single]
          _ = (π0 : ℝ) + (-δ) * (π i : ℝ) := by rw [hx]
          _ < (π0 : ℝ) := by nlinarith
      exact (not_le_of_gt hlt) hy_mem.1
  · rcases lt_or_gt_of_ne hiR with hneg | hpos
    · have hy_mem : x + (-δ) • Pi.single i (1 : ℝ) ∈ split_slab π π0 := by
        exact interior_subset <| hεsubset <| by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg (neg_neg_iff_pos.mpr hδpos)]
          simpa [δ] using half_lt_self hεpos
      rw [mem_split_slab_iff] at hy_mem
      have hgt :
          (π0 : ℝ) + 1 <
            split_linear_form π (x + (-δ) • Pi.single i (1 : ℝ)) := by
        calc
          split_linear_form π (x + (-δ) • Pi.single i (1 : ℝ)) =
              split_linear_form π x + (-δ) * (π i : ℝ) := by
                rw [splitLinearForm_add_smul_single]
          _ = ((π0 : ℝ) + 1) + (-δ) * (π i : ℝ) := by rw [hx]
          _ > (π0 : ℝ) + 1 := by nlinarith
      exact (not_le_of_gt hgt) hy_mem.2
    · have hy_mem : x + δ • Pi.single i (1 : ℝ) ∈ split_slab π π0 := by
        exact interior_subset <| hεsubset <| by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos]
          dsimp [δ]
          exact half_lt_self hεpos
      rw [mem_split_slab_iff] at hy_mem
      have hgt :
          (π0 : ℝ) + 1 <
            split_linear_form π (x + δ • Pi.single i (1 : ℝ)) := by
        calc
          split_linear_form π (x + δ • Pi.single i (1 : ℝ)) =
              split_linear_form π x + δ * (π i : ℝ) := by
                rw [splitLinearForm_add_smul_single]
          _ = ((π0 : ℝ) + 1) + δ * (π i : ℝ) := by rw [hx]
          _ > (π0 : ℝ) + 1 := by nlinarith
      exact (not_le_of_gt hgt) hy_mem.2

/-- Helper for Example 6.9: a boundary point of a split set with nonzero normal cannot lie in its
interior. -/
lemma splitSetBoundaryValue_not_mem_interior
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (hπ : π ≠ 0)
    (π0 : ℤ)
    (x : Fin n → ℝ)
    (hx :
      split_prefix_linear_form hpn π x = (π0 : ℝ) ∨
        split_prefix_linear_form hpn π x = (π0 : ℝ) + 1) :
    x ∉ interior (split_set hpn π π0) := by
  intro hxint
  classical
  have hnonzero_coord : ∃ i : Fin p, π i ≠ 0 := by
    by_contra h
    apply hπ
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hnonzero_coord
  have hiR : (π i : ℝ) ≠ 0 := by
    exact_mod_cast hi
  have hpreimage :
      {t : ℝ | x + t • Pi.single (Fin.castLE hpn i) (1 : ℝ) ∈ interior (split_set hpn π π0)} ∈
        nhds (0 : ℝ) := by
    have hcont :
        Continuous fun t : ℝ ↦ x + t • Pi.single (Fin.castLE hpn i) (1 : ℝ) := by
      continuity
    simpa using
      hcont.continuousAt.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hxint)
  rcases Metric.mem_nhds_iff.mp hpreimage with ⟨ε, hεpos, hεsubset⟩
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact half_pos hεpos
  rcases hx with hx | hx
  · rcases lt_or_gt_of_ne hiR with hneg | hpos
    · have hy_mem : x + δ • Pi.single (Fin.castLE hpn i) (1 : ℝ) ∈ split_set hpn π π0 := by
        exact interior_subset <| hεsubset <| by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos]
          dsimp [δ]
          exact half_lt_self hεpos
      rw [mem_split_set_iff] at hy_mem
      have hlt :
          split_prefix_linear_form hpn π (x + δ • Pi.single (Fin.castLE hpn i) (1 : ℝ)) <
            (π0 : ℝ) := by
        calc
          split_prefix_linear_form hpn π (x + δ • Pi.single (Fin.castLE hpn i) (1 : ℝ)) =
              split_prefix_linear_form hpn π x + δ * (π i : ℝ) := by
                rw [splitPrefixLinearForm_add_smul_single]
          _ = (π0 : ℝ) + δ * (π i : ℝ) := by rw [hx]
          _ < (π0 : ℝ) := by nlinarith
      exact (not_le_of_gt hlt) hy_mem.1
    · have hy_mem : x + (-δ) • Pi.single (Fin.castLE hpn i) (1 : ℝ) ∈ split_set hpn π π0 := by
        exact interior_subset <| hεsubset <| by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg (neg_neg_iff_pos.mpr hδpos)]
          simpa [δ] using half_lt_self hεpos
      rw [mem_split_set_iff] at hy_mem
      have hlt :
          split_prefix_linear_form hpn π (x + (-δ) • Pi.single (Fin.castLE hpn i) (1 : ℝ)) <
            (π0 : ℝ) := by
        calc
          split_prefix_linear_form hpn π (x + (-δ) • Pi.single (Fin.castLE hpn i) (1 : ℝ)) =
              split_prefix_linear_form hpn π x + (-δ) * (π i : ℝ) := by
                rw [splitPrefixLinearForm_add_smul_single]
          _ = (π0 : ℝ) + (-δ) * (π i : ℝ) := by rw [hx]
          _ < (π0 : ℝ) := by nlinarith
      exact (not_le_of_gt hlt) hy_mem.1
  · rcases lt_or_gt_of_ne hiR with hneg | hpos
    · have hy_mem : x + (-δ) • Pi.single (Fin.castLE hpn i) (1 : ℝ) ∈ split_set hpn π π0 := by
        exact interior_subset <| hεsubset <| by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg (neg_neg_iff_pos.mpr hδpos)]
          simpa [δ] using half_lt_self hεpos
      rw [mem_split_set_iff] at hy_mem
      have hgt :
          (π0 : ℝ) + 1 <
            split_prefix_linear_form hpn π
              (x + (-δ) • Pi.single (Fin.castLE hpn i) (1 : ℝ)) := by
        calc
          split_prefix_linear_form hpn π (x + (-δ) • Pi.single (Fin.castLE hpn i) (1 : ℝ)) =
              split_prefix_linear_form hpn π x + (-δ) * (π i : ℝ) := by
                rw [splitPrefixLinearForm_add_smul_single]
          _ = ((π0 : ℝ) + 1) + (-δ) * (π i : ℝ) := by rw [hx]
          _ > (π0 : ℝ) + 1 := by nlinarith
      exact (not_le_of_gt hgt) hy_mem.2
    · have hy_mem : x + δ • Pi.single (Fin.castLE hpn i) (1 : ℝ) ∈ split_set hpn π π0 := by
        exact interior_subset <| hεsubset <| by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos]
          dsimp [δ]
          exact half_lt_self hεpos
      rw [mem_split_set_iff] at hy_mem
      have hgt :
          (π0 : ℝ) + 1 <
            split_prefix_linear_form hpn π (x + δ • Pi.single (Fin.castLE hpn i) (1 : ℝ)) := by
        calc
          split_prefix_linear_form hpn π (x + δ • Pi.single (Fin.castLE hpn i) (1 : ℝ)) =
              split_prefix_linear_form hpn π x + δ * (π i : ℝ) := by
                rw [splitPrefixLinearForm_add_smul_single]
          _ = ((π0 : ℝ) + 1) + δ * (π i : ℝ) := by rw [hx]
          _ > (π0 : ℝ) + 1 := by nlinarith
      exact (not_le_of_gt hgt) hy_mem.2

/-- Example 6.9 (1). The strip
`K = {x ∈ ℝ^p : π₀ ≤ πx ≤ π₀ + 1}` is convex. -/
theorem example_6_9_split_slab_convex
    (π : Fin p → ℤ)
    (π0 : ℤ) :
    Convex ℝ (split_slab π π0) := by
  intro x hx y hy a b ha hb hab
  rw [mem_split_slab_iff] at hx hy ⊢
  -- Rewrite the split functional on the convex combination and combine the endpoint bounds.
  rw [splitLinearForm_smul_add]
  have hxLower := mul_le_mul_of_nonneg_left hx.1 ha
  have hyLower := mul_le_mul_of_nonneg_left hy.1 hb
  have hxUpper := mul_le_mul_of_nonneg_left hx.2 ha
  have hyUpper := mul_le_mul_of_nonneg_left hy.2 hb
  have hsumLower :
      a * (π0 : ℝ) + b * (π0 : ℝ) ≤
        a * split_linear_form π x + b * split_linear_form π y :=
    add_le_add hxLower hyLower
  have hsumUpper :
      a * split_linear_form π x + b * split_linear_form π y ≤
        a * ((π0 : ℝ) + 1) + b * ((π0 : ℝ) + 1) :=
    add_le_add hxUpper hyUpper
  constructor
  · calc
      (π0 : ℝ) = (a + b) * (π0 : ℝ) := by rw [hab, one_mul]
      _ = a * (π0 : ℝ) + b * (π0 : ℝ) := by ring
      _ ≤ a * split_linear_form π x + b * split_linear_form π y := hsumLower
  · calc
      a * split_linear_form π x + b * split_linear_form π y
          ≤ a * ((π0 : ℝ) + 1) + b * ((π0 : ℝ) + 1) := hsumUpper
      _ = (a + b) * ((π0 : ℝ) + 1) := by ring
      _ = (π0 : ℝ) + 1 := by rw [hab, one_mul]

/-- Example 6.9 (2). For a nonzero split normal `π`, the strip
`K = {x ∈ ℝ^p : π₀ ≤ πx ≤ π₀ + 1}` is `ℤ^p`-free. -/
theorem example_6_9_split_slab_is_lattice_free
    (π : Fin p → ℤ)
    (hπ : π ≠ 0)
    (π0 : ℤ) :
    is_lattice_free (split_slab π π0) := by
  rw [is_lattice_free_iff]
  intro z
  -- The split value at an integer point is itself an integer, so only the boundary values are
  -- possible inside the width-one slab.
  have hvalue :
      split_linear_form π (Int.cast ∘ z) = ((∑ i : Fin p, π i * z i : ℤ) : ℝ) := by
    change ∑ i : Fin p, (π i : ℝ) * ((z i : ℤ) : ℝ) = ((∑ i : Fin p, π i * z i : ℤ) : ℝ)
    exact_mod_cast (rfl : (∑ i : Fin p, π i * z i : ℤ) = ∑ i : Fin p, π i * z i)
  intro hzint
  have hzmem : (Int.cast ∘ z) ∈ split_slab π π0 := interior_subset hzint
  rw [mem_split_slab_iff] at hzmem
  let m : ℤ := ∑ i : Fin p, π i * z i
  have hm_lowerR : (π0 : ℝ) ≤ (m : ℝ) := by
    calc
      (π0 : ℝ) ≤ split_linear_form π (Int.cast ∘ z) := hzmem.1
      _ = (m : ℝ) := by simpa [m] using hvalue
  have hm_upperR : (m : ℝ) ≤ (π0 : ℝ) + 1 := by
    calc
      (m : ℝ) = split_linear_form π (Int.cast ∘ z) := by simpa [m] using hvalue.symm
      _ ≤ (π0 : ℝ) + 1 := hzmem.2
  have hm_lower : (π0 : ℤ) ≤ m := by
    exact_mod_cast hm_lowerR
  have hm_upper : m ≤ π0 + 1 := by
    exact_mod_cast hm_upperR
  have hm_cases : m = π0 ∨ m = π0 + 1 := by
    by_cases hm0 : m = π0
    · exact Or.inl hm0
    · right
      have hmgt : π0 < m := lt_of_le_of_ne hm_lower (Ne.symm hm0)
      have hmge : π0 + 1 ≤ m := Int.add_one_le_iff.mpr hmgt
      exact le_antisymm hm_upper hmge
  have hboundary :
      split_linear_form π (Int.cast ∘ z) = (π0 : ℝ) ∨
        split_linear_form π (Int.cast ∘ z) = (π0 : ℝ) + 1 := by
    rcases hm_cases with hm | hm
    · left
      simp [hvalue, m, hm]
    · right
      simp [hvalue, m, hm]
  exact splitSlabBoundaryValue_not_mem_interior π hπ π0 (Int.cast ∘ z) hboundary hzint

/-- Helper for Example 6.9: a point strictly between the two split-slab hyperplanes lies in the
interior of the slab. -/
lemma splitSlabPoint_between_hyperplanes_mem_interior
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (x : Fin p → ℝ)
    (hinside :
      (π0 : ℝ) < split_linear_form π x ∧
        split_linear_form π x < (π0 : ℝ) + 1) :
    x ∈ interior (split_slab π π0) := by
  let U : Set (Fin p → ℝ) :=
    {y | (π0 : ℝ) < split_linear_form π y ∧
        split_linear_form π y < (π0 : ℝ) + 1}
  have hU_open : IsOpen U := by
    -- The strict strip is the preimage of an open interval under a continuous linear form.
    have hcont : Continuous fun y : Fin p → ℝ ↦ split_linear_form π y := by
      unfold split_linear_form
      continuity
    dsimp [U]
    exact (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hxU : x ∈ U := hinside
  have hU_subset : U ⊆ split_slab π π0 := by
    intro y hy
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  exact mem_interior_iff_mem_nhds.2 <|
    Filter.mem_of_superset (hU_open.mem_nhds hxU) hU_subset

/-- Helper for Example 6.9: the push-off point `z + δ • (z - x)` rewrites `z` as a convex
combination of that pushed point and `x`. -/
lemma eq_convexCombo_pushOff
    (x z : Fin p → ℝ)
    {δ : ℝ}
    (hδ : 0 < δ) :
    z = (1 / (1 + δ)) • (z + δ • (z - x)) + (δ / (1 + δ)) • x := by
  -- Solve the affine identity once so the maximality proof can reuse it on both facets.
  have hone : 1 + δ ≠ 0 := by linarith
  ext i
  simp [Pi.add_apply, Pi.smul_apply, sub_eq_add_neg]
  field_simp [hone]
  ring

/-- Example 6.9 (3). If each boundary hyperplane of the strip contains an integral point, then
the strip is maximal lattice-free. In particular, the source's relative-primality hypothesis on
the entries of `π` implies these boundary-point assumptions by Exercise 1.20. -/
theorem example_6_9_split_slab_is_maximal_of_boundary_integer_points
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (hlower : ∃ z : Fin p → ℤ, split_linear_form π (Int.cast ∘ z) = (π0 : ℝ))
    (hupper :
      ∃ z : Fin p → ℤ, split_linear_form π (Int.cast ∘ z) = (π0 : ℝ) + 1) :
    is_maximal_lattice_free (split_slab π π0) := by
  classical
  obtain ⟨zlower, hzlower⟩ := hlower
  obtain ⟨zupper, hzupper⟩ := hupper
  have hπ : π ≠ 0 := by
    -- The two distinct boundary values force the split normal to be nonzero.
    intro hzero
    simp [split_linear_form, hzero] at hzlower hzupper
    linarith
  rw [is_maximal_lattice_free_iff]
  refine ⟨example_6_9_split_slab_convex π π0, example_6_9_split_slab_is_lattice_free π hπ π0, ?_⟩
  intro L hKL hLconvex hLfree
  apply Set.Subset.antisymm ?_ hKL
  intro x hxL
  rw [mem_split_slab_iff]
  by_contra hxslab
  have hxoutside :
      split_linear_form π x < (π0 : ℝ) ∨ (π0 : ℝ) + 1 < split_linear_form π x := by
    by_cases hlower : (π0 : ℝ) ≤ split_linear_form π x
    · right
      have hupper_not : ¬ split_linear_form π x ≤ (π0 : ℝ) + 1 := by
        intro hupper
        exact hxslab ⟨hlower, hupper⟩
      exact lt_of_not_ge hupper_not
    · left
      exact lt_of_not_ge hlower
  rcases hxoutside with hbelow | habove
  · -- Push off from the lower boundary lattice point into the slab interior.
    have hzlower_mem : (Int.cast ∘ zlower) ∈ split_slab π π0 := by
      rw [mem_split_slab_iff]
      constructor <;> linarith [hzlower]
    have hzlower_mem_L : (Int.cast ∘ zlower) ∈ L := hKL hzlower_mem
    let δ : ℝ := 1 / (2 * ((π0 : ℝ) - split_linear_form π x))
    have hgap : 0 < (π0 : ℝ) - split_linear_form π x := by
      linarith
    have hδpos : 0 < δ := by
      dsimp [δ]
      apply one_div_pos.mpr
      nlinarith
    let y : Fin p → ℝ := (Int.cast ∘ zlower) + δ • ((Int.cast ∘ zlower) - x)
    have hsub :
        split_linear_form π ((Int.cast ∘ zlower) - x) =
          split_linear_form π (Int.cast ∘ zlower) - split_linear_form π x := by
      -- Rewrite the difference as an affine combination so linearity applies directly.
      simpa [sub_eq_add_neg, one_smul] using
        splitLinearForm_smul_add π 1 (-1) (Int.cast ∘ zlower) x
    have hy_value : split_linear_form π y = (π0 : ℝ) + 1 / 2 := by
      -- The chosen `δ` lands exactly halfway between the two split hyperplanes.
      calc
        split_linear_form π y
            = split_linear_form π (Int.cast ∘ zlower) +
                δ * split_linear_form π ((Int.cast ∘ zlower) - x) := by
                  dsimp [y]
                  simpa [one_smul] using
                    splitLinearForm_smul_add π 1 δ (Int.cast ∘ zlower) ((Int.cast ∘ zlower) - x)
        _ = (π0 : ℝ) + δ * ((π0 : ℝ) - split_linear_form π x) := by
              rw [hsub, hzlower]
        _ = (π0 : ℝ) + 1 / 2 := by
              dsimp [δ]
              have hgap_ne : (π0 : ℝ) - split_linear_form π x ≠ 0 := by linarith
              field_simp [hgap_ne]
    have hy_between :
        (π0 : ℝ) < split_linear_form π y ∧ split_linear_form π y < (π0 : ℝ) + 1 := by
      constructor <;> rw [hy_value] <;> norm_num
    have hy_int_slab : y ∈ interior (split_slab π π0) := by
      -- Interior points are exactly those lying strictly between the two supporting hyperplanes.
      exact splitSlabPoint_between_hyperplanes_mem_interior π π0 y hy_between
    have hy_int_L : y ∈ interior L := interior_mono hKL hy_int_slab
    have hone : 0 < 1 + δ := by linarith
    have hone_ne : 1 + δ ≠ 0 := by linarith
    have hzlower_combo :
        (Int.cast ∘ zlower) =
          (1 / (1 + δ)) • y + (δ / (1 + δ)) • x := by
      -- Express the boundary point as a convex combination of the interior push-off and `x`.
      dsimp [y]
      simpa using eq_convexCombo_pushOff x (Int.cast ∘ zlower) hδpos
    have hzlower_int_L : (Int.cast ∘ zlower) ∈ interior L := by
      rw [hzlower_combo]
      exact hLconvex.combo_interior_self_mem_interior hy_int_L hxL
        (one_div_pos.mpr hone) (div_nonneg hδpos.le hone.le) (by field_simp [hone_ne])
    have hzlower_lattice : (Int.cast ∘ zlower) ∈ integerVectors p := by
      exact (mem_integerVectors_iff).2 ⟨zlower, rfl⟩
    exact (is_lattice_free.not_mem_interior hLfree hzlower_lattice) hzlower_int_L
  · -- Push off from the upper boundary lattice point back into the slab interior.
    have hzupper_mem : (Int.cast ∘ zupper) ∈ split_slab π π0 := by
      rw [mem_split_slab_iff]
      constructor <;> linarith [hzupper]
    have hzupper_mem_L : (Int.cast ∘ zupper) ∈ L := hKL hzupper_mem
    let δ : ℝ := 1 / (2 * (split_linear_form π x - ((π0 : ℝ) + 1)))
    have hgap : 0 < split_linear_form π x - ((π0 : ℝ) + 1) := by
      linarith
    have hδpos : 0 < δ := by
      dsimp [δ]
      apply one_div_pos.mpr
      nlinarith
    let y : Fin p → ℝ := (Int.cast ∘ zupper) + δ • ((Int.cast ∘ zupper) - x)
    have hsub :
        split_linear_form π ((Int.cast ∘ zupper) - x) =
          split_linear_form π (Int.cast ∘ zupper) - split_linear_form π x := by
      -- Rewrite the difference as an affine combination so linearity applies directly.
      simpa [sub_eq_add_neg, one_smul] using
        splitLinearForm_smul_add π 1 (-1) (Int.cast ∘ zupper) x
    have hy_value : split_linear_form π y = (π0 : ℝ) + 1 / 2 := by
      -- The chosen `δ` lands exactly halfway between the two split hyperplanes.
      calc
        split_linear_form π y
            = split_linear_form π (Int.cast ∘ zupper) +
                δ * split_linear_form π ((Int.cast ∘ zupper) - x) := by
                  dsimp [y]
                  simpa [one_smul] using
                    splitLinearForm_smul_add π 1 δ (Int.cast ∘ zupper) ((Int.cast ∘ zupper) - x)
        _ = ((π0 : ℝ) + 1) +
              δ * (((π0 : ℝ) + 1) - split_linear_form π x) := by
                rw [hsub, hzupper]
        _ = (π0 : ℝ) + 1 / 2 := by
              dsimp [δ]
              have hgap_ne : split_linear_form π x - ((π0 : ℝ) + 1) ≠ 0 := by linarith
              field_simp [hgap_ne]
              ring
    have hy_between :
        (π0 : ℝ) < split_linear_form π y ∧ split_linear_form π y < (π0 : ℝ) + 1 := by
      constructor <;> rw [hy_value] <;> norm_num
    have hy_int_slab : y ∈ interior (split_slab π π0) := by
      -- Interior points are exactly those lying strictly between the two supporting hyperplanes.
      exact splitSlabPoint_between_hyperplanes_mem_interior π π0 y hy_between
    have hy_int_L : y ∈ interior L := interior_mono hKL hy_int_slab
    have hone : 0 < 1 + δ := by linarith
    have hone_ne : 1 + δ ≠ 0 := by linarith
    have hzupper_combo :
        (Int.cast ∘ zupper) =
          (1 / (1 + δ)) • y + (δ / (1 + δ)) • x := by
      -- Express the boundary point as a convex combination of the interior push-off and `x`.
      dsimp [y]
      simpa using eq_convexCombo_pushOff x (Int.cast ∘ zupper) hδpos
    have hzupper_int_L : (Int.cast ∘ zupper) ∈ interior L := by
      rw [hzupper_combo]
      exact hLconvex.combo_interior_self_mem_interior hy_int_L hxL
        (one_div_pos.mpr hone) (div_nonneg hδpos.le hone.le) (by field_simp [hone_ne])
    have hzupper_lattice : (Int.cast ∘ zupper) ∈ integerVectors p := by
      exact (mem_integerVectors_iff).2 ⟨zupper, rfl⟩
    exact (is_lattice_free.not_mem_interior hLfree hzupper_lattice) hzupper_int_L

/-- Example 6.9 (3), source-facing form. If the coefficients of `π` are relatively prime, then
Exercise 1.20 supplies integral points on both boundary hyperplanes, so the split slab is maximal
lattice-free. -/
theorem example_6_9_split_slab_is_maximal_of_coprime_coefficients
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (hcoprime : (Ideal.span (Set.range π) : Ideal ℤ) = ⊤) :
    is_maximal_lattice_free (split_slab π π0) := by
  have hp : 0 < p := by
    cases p with
    | zero =>
        simp at hcoprime
    | succ p =>
        exact Nat.succ_pos p
  refine example_6_9_split_slab_is_maximal_of_boundary_integer_points π π0 ?_ ?_
  · obtain ⟨z, hz⟩ := integer_points_on_coprime_hyperplane hp π hcoprime π0
    refine ⟨z, ?_⟩
    have hz' : split_linear_form π (Int.cast ∘ z) = ((π0 : ℤ) : ℝ) := by
      change ∑ i : Fin p, (π i : ℝ) * (z i : ℝ) = (π0 : ℝ)
      exact_mod_cast hz
    simpa using hz'
  · obtain ⟨z, hz⟩ := integer_points_on_coprime_hyperplane hp π hcoprime (π0 + 1)
    refine ⟨z, ?_⟩
    have hz' : split_linear_form π (Int.cast ∘ z) = ((π0 + 1 : ℤ) : ℝ) := by
      change ∑ i : Fin p, (π i : ℝ) * (z i : ℝ) = ((π0 + 1 : ℤ) : ℝ)
      exact_mod_cast hz
    simpa using hz'

/-- Example 6.9 (4). The split set
`C = {x ∈ ℝ^n : π₀ ≤ ∑_{j=1}^p π_j x_j ≤ π₀ + 1}` is convex. -/
theorem example_6_9_split_set_convex
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ) :
    Convex ℝ (split_set hpn π π0) := by
  intro x hx y hy a b ha hb hab
  rw [mem_split_set_iff] at hx hy ⊢
  -- Rewrite the prefix split functional on the convex combination and combine the endpoint bounds.
  have hrewrite :
      split_prefix_linear_form hpn π (a • x + b • y) =
        a * split_prefix_linear_form hpn π x + b * split_prefix_linear_form hpn π y := by
    simp [split_prefix_linear_form, Finset.mul_sum, Finset.sum_add_distrib,
      add_mul, mul_comm, mul_assoc]
  rw [hrewrite]
  have hxLower := mul_le_mul_of_nonneg_left hx.1 ha
  have hyLower := mul_le_mul_of_nonneg_left hy.1 hb
  have hxUpper := mul_le_mul_of_nonneg_left hx.2 ha
  have hyUpper := mul_le_mul_of_nonneg_left hy.2 hb
  have hsumLower :
      a * (π0 : ℝ) + b * (π0 : ℝ) ≤
        a * split_prefix_linear_form hpn π x + b * split_prefix_linear_form hpn π y :=
    add_le_add hxLower hyLower
  have hsumUpper :
      a * split_prefix_linear_form hpn π x + b * split_prefix_linear_form hpn π y ≤
        a * ((π0 : ℝ) + 1) + b * ((π0 : ℝ) + 1) :=
    add_le_add hxUpper hyUpper
  constructor
  · calc
      (π0 : ℝ) = (a + b) * (π0 : ℝ) := by rw [hab, one_mul]
      _ = a * (π0 : ℝ) + b * (π0 : ℝ) := by ring
      _ ≤ a * split_prefix_linear_form hpn π x + b * split_prefix_linear_form hpn π y :=
        hsumLower
  · calc
      a * split_prefix_linear_form hpn π x + b * split_prefix_linear_form hpn π y
          ≤ a * ((π0 : ℝ) + 1) + b * ((π0 : ℝ) + 1) := hsumUpper
      _ = (a + b) * ((π0 : ℝ) + 1) := by ring
      _ = (π0 : ℝ) + 1 := by rw [hab, one_mul]

/-- Example 6.9 (5). For a nonzero split normal `π`, the interior of the split set contains no
point of `ℤ^p × ℝ^(n - p)`. -/
theorem example_6_9_split_set_interior_disjoint_mixed_integer_prefix_lattice
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (hπ : π ≠ 0)
    (π0 : ℤ) :
    Disjoint (interior (split_set hpn π π0)) (mixed_integer_prefix_lattice hpn) := by
  rw [Set.disjoint_left]
  intro x hxint hxmix
  classical
  rw [mem_mixed_integer_prefix_lattice_iff] at hxmix
  let z : Fin p → ℤ := fun i ↦ Classical.choose (hxmix i)
  have hz : ∀ i : Fin p, x (Fin.castLE hpn i) = (z i : ℝ) := by
    intro i
    exact Classical.choose_spec (hxmix i)
  -- The prefix split value at a mixed-integer point is an integer, so only the two boundary
  -- values are possible in the width-one split strip.
  have hvalue :
      split_prefix_linear_form hpn π x = ((∑ i : Fin p, π i * z i : ℤ) : ℝ) := by
    calc
      split_prefix_linear_form hpn π x =
          ∑ i : Fin p, (π i : ℝ) * ((z i : ℤ) : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hz i]
      _ = ((∑ i : Fin p, π i * z i : ℤ) : ℝ) := by
            exact_mod_cast (rfl : (∑ i : Fin p, π i * z i : ℤ) = ∑ i : Fin p, π i * z i)
  have hxmem : x ∈ split_set hpn π π0 := interior_subset hxint
  rw [mem_split_set_iff] at hxmem
  let m : ℤ := ∑ i : Fin p, π i * z i
  have hm_lowerR : (π0 : ℝ) ≤ (m : ℝ) := by
    calc
      (π0 : ℝ) ≤ split_prefix_linear_form hpn π x := hxmem.1
      _ = (m : ℝ) := by simpa [m] using hvalue
  have hm_upperR : (m : ℝ) ≤ (π0 : ℝ) + 1 := by
    calc
      (m : ℝ) = split_prefix_linear_form hpn π x := by simpa [m] using hvalue.symm
      _ ≤ (π0 : ℝ) + 1 := hxmem.2
  have hm_lower : (π0 : ℤ) ≤ m := by
    exact_mod_cast hm_lowerR
  have hm_upper : m ≤ π0 + 1 := by
    exact_mod_cast hm_upperR
  have hm_cases : m = π0 ∨ m = π0 + 1 := by
    by_cases hm0 : m = π0
    · exact Or.inl hm0
    · right
      have hmgt : π0 < m := lt_of_le_of_ne hm_lower (Ne.symm hm0)
      have hmge : π0 + 1 ≤ m := Int.add_one_le_iff.mpr hmgt
      exact le_antisymm hm_upper hmge
  have hboundary :
      split_prefix_linear_form hpn π x = (π0 : ℝ) ∨
        split_prefix_linear_form hpn π x = (π0 : ℝ) + 1 := by
    rcases hm_cases with hm | hm
    · left
      simp [hvalue, m, hm]
    · right
      simp [hvalue, m, hm]
  exact splitSetBoundaryValue_not_mem_interior hpn π hπ π0 x hboundary hxint

/-- ch6_sec6_2_example_6_9

Example 6.9. (Intersection Cut Defined by a Split)

Given `π ∈ ℤ^p` and `π₀ ∈ ℤ`, let
`C = {x ∈ ℝ^n : π₀ ≤ ∑_{j=1}^p π_j x_j ≤ π₀ + 1}`. For a nonzero split normal `π`, the split
set `C` is convex and its interior contains no point of `ℤ^p × ℝ^(n - p)`. -/
theorem ch6_sec6_2_example_6_9
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (hπ : π ≠ 0)
    (π0 : ℤ) :
    Convex ℝ (split_set hpn π π0) ∧
      Disjoint (interior (split_set hpn π π0)) (mixed_integer_prefix_lattice hpn) := by
  -- Package the two geometric claims already proved for the split set.
  exact ⟨example_6_9_split_set_convex hpn π π0,
    example_6_9_split_set_interior_disjoint_mixed_integer_prefix_lattice hpn π hπ π0⟩

/-- Canonical bridge form of Example 6.9 (5): a split set with nonzero normal is free of
`mixed_integer_prefix_lattice hpn`. -/
theorem split_set_is_free_of_mixed_integer_prefix_lattice
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (hπ : π ≠ 0)
    (π0 : ℤ) :
    is_free_of (mixed_integer_prefix_lattice hpn) (split_set hpn π π0) := by
  simpa [is_free_of] using
    example_6_9_split_set_interior_disjoint_mixed_integer_prefix_lattice hpn π hπ π0

/-- Example 6.9 (6). If one of the first `p` coordinates of `x̄` is nonintegral, then there is a
split pair `(π, π₀)` for which `x̄` lies strictly between the two split hyperplanes. -/
theorem example_6_9_exists_split_around_fractional_prefix_coordinate
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (hfrac :
      ∃ i : Fin p, xbar (Fin.castLE hpn i) ∉ Set.range (Int.cast : ℤ → ℝ)) :
    ∃ π : Fin p → ℤ, ∃ π0 : ℤ,
      (π0 : ℝ) < split_prefix_linear_form hpn π xbar ∧
        split_prefix_linear_form hpn π xbar < (π0 : ℝ) + 1 := by
  rcases hfrac with ⟨i, hi⟩
  let ξ : ℝ := xbar (Fin.castLE hpn i)
  refine ⟨Pi.single i 1, Int.floor ξ, ?_⟩
  have hform : split_prefix_linear_form hpn (Pi.single i 1) xbar = ξ := by
    -- Choosing `π = Pi.single i 1` isolates the fractional prefix coordinate.
    rw [split_prefix_linear_form, Finset.sum_eq_single i]
    · simp [ξ]
    · intro j _ hj
      have hcast : Fin.castLE hpn j ≠ Fin.castLE hpn i := by
        intro hEq
        exact hj ((Fin.castLE_injective hpn) hEq)
      by_cases hji : j = i
      · exact (hj hji).elim
      · simp [hji]
    · intro hiuniv
      simp at hiuniv
  have hfloor_le : ((Int.floor ξ : ℤ) : ℝ) ≤ ξ := Int.floor_le ξ
  have hfloor_ne : ((Int.floor ξ : ℤ) : ℝ) ≠ ξ := by
    intro hξ
    exact hi ⟨Int.floor ξ, hξ⟩
  have hlt_lower : ((Int.floor ξ : ℤ) : ℝ) < ξ := lt_of_le_of_ne hfloor_le hfloor_ne
  have hlt_upper : ξ < ((Int.floor ξ : ℤ) : ℝ) + 1 := by
    simpa using Int.lt_floor_add_one ξ
  simpa [hform, ξ] using And.intro hlt_lower hlt_upper

/-- Example 6.9 (7). If `x̄` lies strictly between the two split hyperplanes, then it belongs to
the interior of the split set. -/
theorem example_6_9_point_between_split_hyperplanes_mem_interior
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (hinside :
      (π0 : ℝ) < split_prefix_linear_form hpn π xbar ∧
        split_prefix_linear_form hpn π xbar < (π0 : ℝ) + 1) :
    xbar ∈ interior (split_set hpn π π0) := by
  let U : Set (Fin n → ℝ) :=
    {x | (π0 : ℝ) < split_prefix_linear_form hpn π x ∧
        split_prefix_linear_form hpn π x < (π0 : ℝ) + 1}
  have hU_open : IsOpen U := by
    -- The strict strip is the preimage of an open interval under a continuous linear form.
    have hcont : Continuous fun x : Fin n → ℝ ↦ split_prefix_linear_form hpn π x := by
      unfold split_prefix_linear_form
      continuity
    dsimp [U]
    exact (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hxU : xbar ∈ U := hinside
  have hU_subset : U ⊆ split_set hpn π π0 := by
    intro x hx
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  exact mem_interior_iff_mem_nhds.2 <|
    Filter.mem_of_superset (hU_open.mem_nhds hxU) hU_subset

/-- Example 6.9 (8). With `ε = π x̄ - π₀`, the strict split inequalities imply `0 < ε < 1`. -/
theorem example_6_9_split_epsilon_mem_Ioo
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (hinside :
      (π0 : ℝ) < split_prefix_linear_form hpn π xbar ∧
        split_prefix_linear_form hpn π xbar < (π0 : ℝ) + 1) :
    split_epsilon hpn π π0 xbar ∈ Set.Ioo (0 : ℝ) 1 := by
  -- Unfold `ε = π x̄ - π₀` and rewrite the strict strip inequalities into `0 < ε < 1`.
  rw [split_epsilon_def]
  constructor
  · linarith [hinside.1]
  · linarith [hinside.2]

/-- Helper for Example 6.9: the admissible parameters along a split ray form a closed interval in
the nonparallel cases and the ray `Set.Ici 0` in the parallel case. -/
lemma splitRayAdmissibleParameters_eq
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hε : split_epsilon hpn π π0 xbar ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin k) :
    IntersectionCut.ray_admissible_parameters (split_set hpn π π0) xbar rays j =
      if _hneg : split_prefix_linear_form hpn π (rays j) < 0 then
        Set.Icc 0 ((-split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j))
      else if _hpos : 0 < split_prefix_linear_form hpn π (rays j) then
        Set.Icc 0 ((1 - split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j))
      else
        Set.Ici 0 := by
  let d : ℝ := split_prefix_linear_form hpn π (rays j)
  let ε : ℝ := split_epsilon hpn π π0 xbar
  have hvalue :
      ∀ t : ℝ,
        split_prefix_linear_form hpn π (xbar + t • rays j) = (π0 : ℝ) + ε + t * d := by
    intro t
    -- Normalize the split functional along the chosen ray to the scalar form `π x̄ + t * π r`.
    dsimp [d, ε]
    rw [splitPrefixLinearForm_add_smul, split_epsilon_def]
    ring
  by_cases hneg : split_prefix_linear_form hpn π (rays j) < 0
  · -- Negative slope: the upper endpoint comes from the lower split boundary.
    have hd : d < 0 := by simpa [d] using hneg
    have hbranch :
        (if _hneg : split_prefix_linear_form hpn π (rays j) < 0 then
            Set.Icc 0 ((-split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j))
          else if _hpos : 0 < split_prefix_linear_form hpn π (rays j) then
            Set.Icc 0 ((1 - split_epsilon hpn π π0 xbar) /
              split_prefix_linear_form hpn π (rays j))
          else
            Set.Ici 0) =
          Set.Icc 0 ((-split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j)) := by
      simp [hneg]
    rw [hbranch]
    ext t
    rw [IntersectionCut.mem_ray_admissible_parameters_iff, Set.mem_Icc, mem_split_set_iff]
    constructor
    · intro ht
      rcases ht with ⟨ht0, htmem⟩
      have hlower : 0 ≤ ε + t * d := by
        rw [hvalue t] at htmem
        linarith
      have hdpos : 0 < -d := by
        linarith
      have hmul : t * (-d) ≤ ε := by
        have : -(t * d) ≤ ε := by
          linarith
        simpa [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using this
      have hbound_aux : t ≤ ε / (-d) := by
        exact (le_div_iff₀ hdpos).2 (by simpa [mul_comm] using hmul)
      have hbound :
          t ≤ (-ε) / split_prefix_linear_form hpn π (rays j) := by
        have hneg_ne : d ≠ 0 := ne_of_lt hneg
        have hrewrite : ε / (-d) = (-ε) / d := by
          field_simp [hneg_ne]
        simpa [d, ε] using hbound_aux.trans_eq hrewrite
      constructor
      · exact ht0
      · exact hbound
    · intro ht
      rcases ht with ⟨ht0, htbound⟩
      have hmul :
          ((-split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j)) * d ≤
            t * d := by
        simpa [d, ε] using mul_le_mul_of_nonpos_right htbound hd.le
      have hdne : d ≠ 0 := ne_of_lt hd
      have htd_lower : -ε ≤ t * d := by
        calc
          -ε = ((-ε) / d) * d := by
                field_simp [hdne]
          _ ≤ t * d := by simpa [d, ε] using hmul
      have htd_nonpos : t * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hd.le
      constructor
      · exact ht0
      · constructor
        · rw [hvalue t]
          linarith
        · rw [hvalue t]
          linarith [hε.2, htd_nonpos]
  · by_cases hpos : 0 < split_prefix_linear_form hpn π (rays j)
    · -- Positive slope: the upper endpoint comes from the upper split boundary.
      have hd : 0 < d := by simpa [d] using hpos
      have hbranch :
          (if _hneg : split_prefix_linear_form hpn π (rays j) < 0 then
              Set.Icc 0 ((-split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j))
            else if _hpos : 0 < split_prefix_linear_form hpn π (rays j) then
              Set.Icc 0 ((1 - split_epsilon hpn π π0 xbar) /
                split_prefix_linear_form hpn π (rays j))
            else
              Set.Ici 0) =
            Set.Icc 0 ((1 - split_epsilon hpn π π0 xbar) /
              split_prefix_linear_form hpn π (rays j)) := by
        simp [hneg, hpos]
      rw [hbranch]
      ext t
      rw [IntersectionCut.mem_ray_admissible_parameters_iff, Set.mem_Icc, mem_split_set_iff]
      constructor
      · intro ht
        rcases ht with ⟨ht0, htmem⟩
        have hupper : ε + t * d ≤ 1 := by
          rw [hvalue t] at htmem
          linarith
        have hmul : t * d ≤ 1 - ε := by
          linarith
        have hbound :
            t ≤ (1 - split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j) := by
          exact (le_div_iff₀ hd).2 (by simpa [d, ε, mul_comm] using hmul)
        constructor
        · exact ht0
        · exact hbound
      · intro ht
        rcases ht with ⟨ht0, htbound⟩
        have hmul :
            t * d ≤
              ((1 - split_epsilon hpn π π0 xbar) /
                split_prefix_linear_form hpn π (rays j)) * d := by
          simpa [d, ε] using mul_le_mul_of_nonneg_right htbound hd.le
        have hdne : d ≠ 0 := ne_of_gt hd
        have htd_upper : t * d ≤ 1 - ε := by
          calc
            t * d ≤ ((1 - ε) / d) * d := by simpa [d, ε] using hmul
            _ = 1 - ε := by
                  field_simp [hdne]
          -- `field_simp` closes the endpoint simplification.
        have htd_nonneg : 0 ≤ t * d := mul_nonneg ht0 hd.le
        constructor
        · exact ht0
        · constructor
          · rw [hvalue t]
            linarith [hε.1, htd_nonneg]
          · rw [hvalue t]
            linarith
    · -- Zero slope: every nonnegative parameter stays between the same two split hyperplanes.
      have hbranch :
          (if _hneg : split_prefix_linear_form hpn π (rays j) < 0 then
              Set.Icc 0 ((-split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j))
            else if _hpos : 0 < split_prefix_linear_form hpn π (rays j) then
              Set.Icc 0 ((1 - split_epsilon hpn π π0 xbar) /
                split_prefix_linear_form hpn π (rays j))
            else
              Set.Ici 0) =
            Set.Ici 0 := by
        simp [hneg, hpos]
      rw [hbranch]
      have hzero : d = 0 := by
        linarith
      ext t
      rw [IntersectionCut.mem_ray_admissible_parameters_iff, Set.mem_Ici, mem_split_set_iff]
      constructor
      · intro ht
        rcases ht with ⟨ht0, htmem⟩
        exact ht0
      · intro ht0
        constructor
        · exact ht0
        · rw [hvalue t, hzero]
          constructor <;> linarith [hε.1, hε.2]

/-- Helper for Example 6.9: the ENNReal image of `Set.Icc 0 a` has supremum `ENNReal.ofReal a`
when `a` is nonnegative. -/
lemma sSup_ofReal_image_Icc
    {a : ℝ}
    (ha : 0 ≤ a) :
    sSup (ENNReal.ofReal '' Set.Icc (0 : ℝ) a) = ENNReal.ofReal a := by
  -- The endpoint `a` is itself in the image and every other image point lies below it.
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ENNReal.ofReal_le_ofReal ht.2
  · exact le_sSup ⟨a, ⟨ha, le_rfl⟩, rfl⟩

/-- Helper for Example 6.9: the ENNReal image of `Set.Ici 0` is unbounded, so its supremum is
`⊤`. -/
lemma sSup_ofReal_image_Ici :
    sSup (ENNReal.ofReal '' Set.Ici (0 : ℝ)) = (⊤ : ENNReal) := by
  -- Every finite ENNReal value is strictly below the image point at `toReal + 1`.
  rw [sSup_eq_top]
  intro b hb
  have hbtop : b ≠ ⊤ := lt_top_iff_ne_top.mp hb
  have hbReal_nonneg : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have hbReal_pos : 0 < b.toReal + 1 := by linarith
  refine ⟨ENNReal.ofReal (b.toReal + 1), ?_, ?_⟩
  · refine ⟨b.toReal + 1, ?_, rfl⟩
    exact add_nonneg hbReal_nonneg zero_le_one
  · have hb_eq : b = ENNReal.ofReal b.toReal := by
      symm
      exact ENNReal.ofReal_toReal hbtop
    have hlt : ENNReal.ofReal b.toReal < ENNReal.ofReal (b.toReal + 1) := by
      exact (ENNReal.ofReal_lt_ofReal_iff hbReal_pos).2 (by linarith)
    calc
      b = ENNReal.ofReal b.toReal := hb_eq
      _ < ENNReal.ofReal (b.toReal + 1) := hlt

/-- Example 6.9 (9). For a point `x̄` in the interior of the split set, the ray-intersection
parameter `α_j` has the explicit split formula
`-ε / (π r̄^j)` when `π r̄^j < 0`, `(1 - ε) / (π r̄^j)` when `π r̄^j > 0`, and `∞`
otherwise. -/
theorem example_6_9_split_ray_parameter_eq_piecewise
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hε : split_epsilon hpn π π0 xbar ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin k) :
    IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j =
      if _hneg : split_prefix_linear_form hpn π (rays j) < 0 then
        ENNReal.ofReal
          ((-split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j))
      else if _hpos : 0 < split_prefix_linear_form hpn π (rays j) then
        ENNReal.ofReal
          ((1 - split_epsilon hpn π π0 xbar) / split_prefix_linear_form hpn π (rays j))
      else
        ⊤ := by
  let d : ℝ := split_prefix_linear_form hpn π (rays j)
  let ε : ℝ := split_epsilon hpn π π0 xbar
  rw [IntersectionCut.ray_intersection_parameter_def, splitRayAdmissibleParameters_eq hpn π π0 xbar
    rays hε j]
  by_cases hneg : split_prefix_linear_form hpn π (rays j) < 0
  · -- In the negative-slope case the admissible parameters are a bounded closed interval.
    have hd : d < 0 := by simpa [d] using hneg
    simp [hneg]
    have hendpoint_nonneg : 0 ≤ (-ε) / d := by
      have hdpos : 0 < -d := by
        linarith
      have : 0 ≤ ε / (-d) := div_nonneg hε.1.le hdpos.le
      have hdne : d ≠ 0 := ne_of_lt hd
      have hrewrite : ε / (-d) = (-ε) / d := by
        field_simp [hdne]
      exact hrewrite ▸ this
    simpa [d, ε] using sSup_ofReal_image_Icc hendpoint_nonneg
  · by_cases hpos : 0 < split_prefix_linear_form hpn π (rays j)
    · -- In the positive-slope case the bounded interval ends at `(1 - ε) / d`.
      have hd : 0 < d := by simpa [d] using hpos
      simp [hneg, hpos]
      have hendpoint_nonneg : 0 ≤ (1 - ε) / d := by
        have hnum : 0 ≤ 1 - ε := by
          linarith [hε.2]
        exact div_nonneg hnum hd.le
      simpa [d, ε] using sSup_ofReal_image_Icc hendpoint_nonneg
    · -- If the ray is parallel to the split hyperplanes, admissible parameters are unbounded.
      simp [hneg, hpos]
      simpa using sSup_ofReal_image_Ici

/-- Example 6.9 (10). If the `j`th ray is not parallel to the split hyperplanes, then `α_j` is
the largest nonnegative parameter `α` for which the half-line `x̄ + α r̄^j` stays in the split
set. -/
theorem example_6_9_split_ray_parameter_is_greatest_of_nonparallel
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hε : split_epsilon hpn π π0 xbar ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin k)
    (hj : split_prefix_linear_form hpn π (rays j) ≠ 0) :
    IsGreatest
      {α : ℝ | 0 ≤ α ∧ xbar + α • rays j ∈ split_set hpn π π0}
      (IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j).toReal := by
  classical
  let d : ℝ := split_prefix_linear_form hpn π (rays j)
  let ε : ℝ := split_epsilon hpn π π0 xbar
  have hset :
      {α : ℝ | 0 ≤ α ∧ xbar + α • rays j ∈ split_set hpn π π0} =
        IntersectionCut.ray_admissible_parameters (split_set hpn π π0) xbar rays j := by
    rfl
  have hparams := splitRayAdmissibleParameters_eq hpn π π0 xbar rays hε j
  rcases lt_or_gt_of_ne (by simpa [d] using hj) with hneg | hpos
  · -- Nonparallel with negative slope: the greatest admissible parameter is the right endpoint.
    have hendpoint_nonneg : 0 ≤ (-ε) / d := by
      have hdpos : 0 < -d := by
        linarith
      have : 0 ≤ ε / (-d) := div_nonneg hε.1.le hdpos.le
      have hdne : d ≠ 0 := ne_of_lt hneg
      have hrewrite : ε / (-d) = (-ε) / d := by
        field_simp [hdne]
      exact hrewrite ▸ this
    have hparams' :
        IntersectionCut.ray_admissible_parameters (split_set hpn π π0) xbar rays j =
          Set.Icc 0 ((-ε) / d) := by
      simpa [d, ε, hneg] using hparams
    have hvalue :
        (IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j).toReal =
          (-ε) / d := by
      have hpiece := example_6_9_split_ray_parameter_eq_piecewise hpn π π0 xbar rays hε j
      have hparam :
          IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j =
            ENNReal.ofReal ((-ε) / d) := by
        simpa [d, ε, hneg] using hpiece
      calc
        (IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j).toReal
            = (ENNReal.ofReal ((-ε) / d)).toReal := by rw [hparam]
        _ = (-ε) / d := ENNReal.toReal_ofReal hendpoint_nonneg
    rw [hset, hparams', hvalue]
    exact isGreatest_Icc hendpoint_nonneg
  · -- Nonparallel with positive slope: the greatest admissible parameter is the right endpoint.
    have hendpoint_nonneg : 0 ≤ (1 - ε) / d := by
      have hnum : 0 ≤ 1 - ε := by
        linarith [hε.2]
      exact div_nonneg hnum hpos.le
    have hparams' :
        IntersectionCut.ray_admissible_parameters (split_set hpn π π0) xbar rays j =
          Set.Icc 0 ((1 - ε) / d) := by
      have hneg_false : ¬d < 0 := not_lt_of_gt hpos
      simpa [d, ε, hneg_false, hpos] using hparams
    have hvalue :
        (IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j).toReal =
          (1 - ε) / d := by
      have hpiece := example_6_9_split_ray_parameter_eq_piecewise hpn π π0 xbar rays hε j
      have hparam :
          IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j =
            ENNReal.ofReal ((1 - ε) / d) := by
        have hneg_false : ¬d < 0 := not_lt_of_gt hpos
        simpa [d, ε, hneg_false, hpos] using hpiece
      calc
        (IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j).toReal
            = (ENNReal.ofReal ((1 - ε) / d)).toReal := by rw [hparam]
        _ = (1 - ε) / d := ENNReal.toReal_ofReal hendpoint_nonneg
    rw [hset, hparams', hvalue]
    exact isGreatest_Icc hendpoint_nonneg

/-- Example 6.9 (11). If the `j`th ray is parallel to the split hyperplanes, then `α_j = +∞`. -/
theorem example_6_9_split_ray_parameter_eq_top_of_parallel
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hε : split_epsilon hpn π π0 xbar ∈ Set.Ioo (0 : ℝ) 1)
    (j : Fin k)
    (hparallel : split_prefix_linear_form hpn π (rays j) = 0) :
    IntersectionCut.ray_intersection_parameter (split_set hpn π π0) xbar rays j = ⊤ := by
  -- The piecewise formula collapses to the parallel branch once `π r̄^j = 0`.
  simpa [hparallel] using example_6_9_split_ray_parameter_eq_piecewise hpn π π0 xbar rays hε j

/-- Example 6.9 (12). The Section 6.2 intersection cut specialized to the split set is the
inequality `∑_{j ∈ N} x_j / α_j ≥ 1`, where `α_j` is the split ray-intersection parameter of
`split_set hpn π π0`. -/
theorem example_6_9_mem_split_intersection_cut_iff
    (hpn : p ≤ n)
    (π : Fin p → ℤ)
    (π0 : ℤ)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (x : Fin k → ℝ) :
    1 ≤ IntersectionCut.intersection_cut_coeff (split_set hpn π π0) xbar rays ⬝ᵥ x ↔
      1 ≤ ∑ j : Fin k,
        x j /
          (IntersectionCut.ray_intersection_parameter
            (split_set hpn π π0) xbar rays j).toReal := by
  -- Unfold the cut coefficients and rewrite the dot product termwise as division by `αⱼ`.
  simp [IntersectionCut.intersection_cut_coeff, dotProduct, div_eq_mul_inv, mul_comm]

end Example69
