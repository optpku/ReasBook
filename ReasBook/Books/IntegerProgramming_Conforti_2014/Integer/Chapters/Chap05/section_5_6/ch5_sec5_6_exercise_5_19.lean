/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1

open scoped BigOperators Matrix

-- Primary domain: Chapter 5 Chvatal closures and Chvatal rank in `Fin n → ℝ`.
-- Core/canonical owners sampled upstream: `is_valid_inequality`,
-- `pure_integer_chvatal_closure`, `(pure_integer_chvatal_closure^[t]) P`, and
-- `is_iterate_rank_of_inequality`.
-- Primitive source-facing data kept here: the explicit Exercise 5.19 polyhedron.
-- Derived API kept here: the subset-sum relaxation, the iterate comparison theorem, and the
-- source-facing rank bounds.
-- The all-ones coefficient vector is expressed directly as `(1 : Fin n → ℝ)`, rather than by a
-- parallel local alias.
-- Semantic recall note: `lean_leansearch` returned no relevant Chvatal-rank API for this
-- exercise, so this file uses the local Chapter 5 owners directly.

section Exercise519

variable {n : ℕ}

/-- The polyhedron
`P = {x ∈ ℝ_+^n | x_i + x_j ≤ 1 for all 1 ≤ i < j ≤ n}`
from Exercise 5.19. -/
def exercise_5_19_polyhedron (n : ℕ) : Set (Fin n → ℝ) :=
  {x |
    (∀ i : Fin n, 0 ≤ x i) ∧
      ∀ ⦃i j : Fin n⦄, i < j → x i + x j ≤ 1}

/-- Membership in `exercise_5_19_polyhedron n` is exactly nonnegativity together with the
pairwise inequalities `x_i + x_j ≤ 1` for `i < j`. -/
theorem mem_exercise_5_19_polyhedron_iff
    {x : Fin n → ℝ} :
    x ∈ exercise_5_19_polyhedron n ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ ⦃i j : Fin n⦄, i < j → x i + x j ≤ 1 :=
  Iff.rfl

/-- The source-facing threshold subset-sum relaxation appearing in the positive Chvátal iterates
of Exercise 5.19. At stage `t`, the active subset size is `min(n, 2^t + 1)`. -/
def exercise_5_19_subset_sum_relaxation (n t : ℕ) : Set (Fin n → ℝ) :=
  {x |
    (∀ i : Fin n, 0 ≤ x i) ∧
      ∀ I : Finset (Fin n),
        I.card = Nat.min n (2 ^ t + 1) → I.sum x ≤ 1}

/-- Membership in `exercise_5_19_subset_sum_relaxation n t` is exactly nonnegativity together
with the threshold subset-sum bounds `∑_{i ∈ I} x_i ≤ 1` for all subsets of cardinality
`min(n, 2^t + 1)`. -/
theorem mem_exercise_5_19_subset_sum_relaxation_iff
    {t : ℕ}
    {x : Fin n → ℝ} :
    x ∈ exercise_5_19_subset_sum_relaxation n t ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ I : Finset (Fin n),
          I.card = Nat.min n (2 ^ t + 1) → I.sum x ≤ 1 :=
  Iff.rfl

/-- Helper for Exercise 5.19: a point in the `t`-th subset-sum relaxation satisfies every
subset-sum inequality whose support has cardinality at most the active threshold. -/
lemma exercise_5_19_subset_sum_relaxation_card_le
    {t : ℕ}
    {x : Fin n → ℝ}
    (hx : x ∈ exercise_5_19_subset_sum_relaxation n t)
    {J : Finset (Fin n)}
    (hJ : J.card ≤ Nat.min n (2 ^ t + 1)) :
    J.sum x ≤ 1 := by
  rw [mem_exercise_5_19_subset_sum_relaxation_iff] at hx
  let m := Nat.min n (2 ^ t + 1)
  obtain ⟨K, hJK, hKcard⟩ :=
    Finset.exists_superset_card_eq (s := J) (n := m) hJ (by
      simp [m])
  -- Enlarge `J` to an active set `K`, then use nonnegativity to compare the two sums.
  have hJ_le_K : J.sum x ≤ K.sum x := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hJK ?_
    intro i hiK hiJ'
    exact hx.1 i
  have hK_le : K.sum x ≤ 1 := hx.2 K hKcard
  exact hJ_le_K.trans hK_le

/-- Helper for Exercise 5.19: when `n ≥ 2`, the source polyhedron is the stage-`0`
subset-sum relaxation, because the active subsets are exactly the pairs. -/
lemma exercise_5_19_polyhedron_eq_subset_sum_relaxation_zero
    (hn : 2 ≤ n) :
    exercise_5_19_polyhedron n = exercise_5_19_subset_sum_relaxation n 0 := by
  ext x
  rw [mem_exercise_5_19_polyhedron_iff, mem_exercise_5_19_subset_sum_relaxation_iff]
  have hmin : Nat.min n (2 ^ 0 + 1) = 2 := by
    simpa using (Nat.min_eq_right hn : Nat.min n 2 = 2)
  constructor
  · rintro ⟨hx_nonneg, hx_pair⟩
    refine ⟨hx_nonneg, ?_⟩
    intro I hI
    rw [hmin] at hI
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hI
    -- Rewrite the two-element subset inequality as one of the source pairwise inequalities.
    have hsum :
        ({i, j} : Finset (Fin n)).sum x = x i + x j := by
      rw [Finset.sum_insert]
      · simp
      · simp [hij]
    rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
    · rw [hsum]
      exact hx_pair hij_lt
    · rw [hsum, add_comm]
      exact hx_pair hji_lt
  · rintro ⟨hx_nonneg, hx_subset⟩
    refine ⟨hx_nonneg, ?_⟩
    intro i j hij
    have hcard_pair : ({i, j} : Finset (Fin n)).card = 2 := by
      exact Finset.card_pair hij.ne
    have hpair :
        ({i, j} : Finset (Fin n)).sum x ≤ 1 := by
      apply hx_subset
      rw [hmin]
      exact hcard_pair
    have hsum :
        ({i, j} : Finset (Fin n)).sum x = x i + x j := by
      rw [Finset.sum_insert]
      · simp
      · simp [hij.ne]
    -- Specialize the stage-`0` subset inequality to the pair `{i, j}`.
    rw [hsum] at hpair
    exact hpair

/-- Helper for Exercise 5.19: the zero vector belongs to every threshold subset-sum relaxation. -/
lemma exercise_5_19_zero_mem_subset_sum_relaxation
    (n t : ℕ) :
    (0 : Fin n → ℝ) ∈ exercise_5_19_subset_sum_relaxation n t := by
  -- Every active subset sum of the zero vector is exactly `0`.
  rw [mem_exercise_5_19_subset_sum_relaxation_iff]
  simp

/-- Helper for Exercise 5.19: every unit vector belongs to every threshold subset-sum relaxation,
because every active subset sum is at most the full unit-vector sum `1`. -/
lemma exercise_5_19_single_mem_subset_sum_relaxation
    (n t : ℕ)
    (i : Fin n) :
    Pi.single i (1 : ℝ) ∈ exercise_5_19_subset_sum_relaxation n t := by
  rw [mem_exercise_5_19_subset_sum_relaxation_iff]
  refine ⟨?_, ?_⟩
  · -- Unit vectors are coordinatewise nonnegative.
    intro j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [Pi.single_eq_of_ne hji]
  · intro I hI
    -- Compare the subset sum with the full sum of the same unit vector.
    have hsubset :
        I.sum (Pi.single i (1 : ℝ)) ≤
          (Finset.univ : Finset (Fin n)).sum (Pi.single i (1 : ℝ)) := by
      exact Finset.sum_le_univ_sum_of_nonneg fun j ↦ by
        by_cases hji : j = i
        · subst hji
          simp
        · simp [Pi.single_eq_of_ne hji]
    simpa using hsubset

/-- Helper for Exercise 5.19: every point of the simplex
`{x ≥ 0 | ∑ i, x i ≤ 1}` already lies in every threshold subset-sum relaxation. -/
lemma exercise_5_19_mem_subset_sum_relaxation_of_mem_simplex
    {t : ℕ}
    {x : Fin n → ℝ}
    (hx_nonneg : ∀ i : Fin n, 0 ≤ x i)
    (hx_sum : ∑ i : Fin n, x i ≤ 1) :
    x ∈ exercise_5_19_subset_sum_relaxation n t := by
  rw [mem_exercise_5_19_subset_sum_relaxation_iff]
  refine ⟨hx_nonneg, ?_⟩
  intro I hI
  -- Every active subset sum is bounded by the full nonnegative sum.
  exact (Finset.sum_le_univ_sum_of_nonneg fun i ↦ hx_nonneg i).trans hx_sum

/-- Helper for Exercise 5.19: once the active threshold reaches `n`, the stage is exactly the
standard simplex `{x ≥ 0 | ∑ i, x i ≤ 1}`. -/
lemma exercise_5_19_subset_sum_relaxation_eq_simplex_of_stage_saturated
    {s : ℕ}
    (hsat : Nat.min n (2 ^ s + 1) = n) :
    exercise_5_19_subset_sum_relaxation n s =
      {x : Fin n → ℝ | (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1} := by
  ext x
  rw [mem_exercise_5_19_subset_sum_relaxation_iff]
  constructor
  · rintro ⟨hx_nonneg, hx_subset⟩
    refine ⟨hx_nonneg, ?_⟩
    -- The unique active subset of size `n` is `Finset.univ`.
    simpa [hsat] using hx_subset Finset.univ (by simp [hsat])
  · rintro ⟨hx_nonneg, hx_sum⟩
    exact exercise_5_19_mem_subset_sum_relaxation_of_mem_simplex
      (n := n) (t := s) hx_nonneg hx_sum

/-- Helper for Exercise 5.19: every simplex point survives one pure-integer Chvátal step from any
threshold subset-sum stage. -/
lemma exercise_5_19_mem_pure_integer_chvatal_closure_of_mem_simplex
    {s : ℕ}
    {x : Fin n → ℝ}
    (hx_nonneg : ∀ i : Fin n, 0 ≤ x i)
    (hx_sum : ∑ i : Fin n, x i ≤ 1) :
    x ∈ pure_integer_chvatal_closure (exercise_5_19_subset_sum_relaxation n s) := by
  rw [mem_pure_integer_chvatal_closure_iff]
  refine ⟨exercise_5_19_mem_subset_sum_relaxation_of_mem_simplex
    (n := n) (t := s) hx_nonneg hx_sum, ?_⟩
  intro c d hvalid
  have hd_nonneg : 0 ≤ d := by
    -- Testing the valid inequality at the zero vector forces a nonnegative right-hand side.
    simpa using hvalid (exercise_5_19_zero_mem_subset_sum_relaxation n s)
  have hfloor_nonneg_int : 0 ≤ Int.floor d :=
    Int.floor_nonneg.mpr hd_nonneg
  have hfloor_nonneg : 0 ≤ (((Int.floor d : ℤ) : ℝ)) := by
    exact_mod_cast hfloor_nonneg_int
  have hcoord_floor : ∀ i : Fin n, (c i : ℝ) ≤ (((Int.floor d : ℤ) : ℝ)) := by
    intro i
    have hsingle_valid :
        (fun j ↦ (c j : ℝ)) ⬝ᵥ Pi.single i (1 : ℝ) ≤ d := by
      exact hvalid (exercise_5_19_single_mem_subset_sum_relaxation n s i)
    have hci_le_d : (c i : ℝ) ≤ d := by
      -- Evaluating the cut on `e_i` reads off the `i`th coefficient directly.
      simpa [dotProduct, Pi.single_apply] using hsingle_valid
    have hci_floor_int : c i ≤ Int.floor d :=
      Int.le_floor.mpr hci_le_d
    exact_mod_cast hci_floor_int
  have hdot_le :
      (fun i ↦ (c i : ℝ)) ⬝ᵥ x ≤
        ∑ i : Fin n, (((Int.floor d : ℤ) : ℝ)) * x i := by
    -- Bound each coefficient by the common floor bound and sum the coordinatewise inequalities.
    exact Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_right (hcoord_floor i) (hx_nonneg i)
  calc
    (fun i ↦ (c i : ℝ)) ⬝ᵥ x
        ≤ ∑ i : Fin n, (((Int.floor d : ℤ) : ℝ)) * x i := hdot_le
    _ = (((Int.floor d : ℤ) : ℝ)) * ∑ i : Fin n, x i := by
          rw [← Finset.mul_sum]
    _ ≤ (((Int.floor d : ℤ) : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hx_sum hfloor_nonneg
    _ = ((Int.floor d : ℤ) : ℝ) := by
          simp

/-- Helper for Exercise 5.19: once a stage has saturated to the simplex, one more pure-integer
Chvátal step leaves it unchanged. -/
lemma exercise_5_19_subset_sum_relaxation_oneStep_of_stage_saturated
    {s : ℕ}
    (hsat : Nat.min n (2 ^ s + 1) = n) :
    pure_integer_chvatal_closure (exercise_5_19_subset_sum_relaxation n s) =
      exercise_5_19_subset_sum_relaxation n (s + 1) := by
  have hs_le : n ≤ 2 ^ s + 1 := by
    rw [← hsat]
    exact Nat.min_le_right n (2 ^ s + 1)
  have hpow_le : 2 ^ s + 1 ≤ 2 ^ (s + 1) + 1 := by
    have hpow : 2 ^ s ≤ 2 ^ (s + 1) := by
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ s)
    omega
  have hnext :
      Nat.min n (2 ^ (s + 1) + 1) = n := by
    exact Nat.min_eq_left (hs_le.trans hpow_le)
  ext x
  constructor
  · intro hx
    have hx_base : x ∈ exercise_5_19_subset_sum_relaxation n s :=
      (mem_pure_integer_chvatal_closure_iff.mp hx).1
    -- The ambient membership already puts the point in the simplex, which is the next stage too.
    rw [exercise_5_19_subset_sum_relaxation_eq_simplex_of_stage_saturated
      (n := n) (s := s) hsat] at hx_base
    rw [exercise_5_19_subset_sum_relaxation_eq_simplex_of_stage_saturated
      (n := n) (s := s + 1) hnext]
    exact hx_base
  · intro hx
    rw [exercise_5_19_subset_sum_relaxation_eq_simplex_of_stage_saturated
      (n := n) (s := s + 1) hnext] at hx
    -- Every simplex point already survives the preceding closure step.
    exact exercise_5_19_mem_pure_integer_chvatal_closure_of_mem_simplex
      (n := n) (s := s) hx.1 hx.2

/-- Helper for Exercise 5.19: every threshold subset-sum stage is down-closed under
coordinatewise decrease. -/
lemma exercise_5_19_subset_sum_relaxation_downClosed
    {t : ℕ}
    {x y : Fin n → ℝ}
    (hx : x ∈ exercise_5_19_subset_sum_relaxation n t)
    (hy_nonneg : ∀ i : Fin n, 0 ≤ y i)
    (hy_le : ∀ i : Fin n, y i ≤ x i) :
    y ∈ exercise_5_19_subset_sum_relaxation n t := by
  rw [mem_exercise_5_19_subset_sum_relaxation_iff] at hx ⊢
  refine ⟨hy_nonneg, ?_⟩
  intro I hI
  -- Compare the new subset sum coordinatewise against the old feasible point.
  exact (Finset.sum_le_sum fun i _ ↦ hy_le i).trans (hx.2 I hI)

/-- Helper for Exercise 5.19: truncating an integer coefficient vector to its positive part
preserves validity on the down-closed threshold subset-sum stages. -/
lemma exercise_5_19_positivePart_is_valid_on_subset_sum_relaxation
    {s : ℕ}
    {c : Fin n → ℤ}
    {d : ℝ}
    (hvalid :
      is_valid_inequality
        (exercise_5_19_subset_sum_relaxation n s)
        (fun i ↦ (c i : ℝ)) d) :
    is_valid_inequality
      (exercise_5_19_subset_sum_relaxation n s)
      (fun i ↦ ((max (c i) 0 : ℤ) : ℝ)) d := by
  intro x hx
  let y : Fin n → ℝ := fun i ↦ if 0 ≤ c i then x i else 0
  have hy_mem :
      y ∈ exercise_5_19_subset_sum_relaxation n s := by
    -- Zeroing the negative-coefficient coordinates only decreases the point.
    refine exercise_5_19_subset_sum_relaxation_downClosed (n := n) (t := s) hx ?_ ?_
    · intro i
      by_cases hci : 0 ≤ c i
      · simpa [y, hci] using (show 0 ≤ x i from
          (mem_exercise_5_19_subset_sum_relaxation_iff.mp hx).1 i)
      · simp [y, hci]
    · intro i
      by_cases hci : 0 ≤ c i
      · simp [y, hci]
      · have hx_nonneg : 0 ≤ x i :=
          (mem_exercise_5_19_subset_sum_relaxation_iff.mp hx).1 i
        simp [y, hci, hx_nonneg]
  have hy_valid :
      (fun i ↦ (c i : ℝ)) ⬝ᵥ y ≤ d :=
    hvalid hy_mem
  have hdot :
      (fun i ↦ ((max (c i) 0 : ℤ) : ℝ)) ⬝ᵥ x =
        (fun i ↦ (c i : ℝ)) ⬝ᵥ y := by
    -- The positive part agrees with `c` on the kept coordinates and vanishes elsewhere.
    unfold dotProduct y
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hci : 0 ≤ c i
    · simp [hci]
    · have hci_le : c i ≤ 0 := le_of_not_ge hci
      simp [hci, max_eq_right hci_le]
  rw [hdot]
  exact hy_valid

/-- Helper for Exercise 5.19: when the active threshold is `m`, the constant vector `1 / m`
lies in the same threshold subset-sum relaxation. -/
lemma exercise_5_19_constantWitness_mem_subset_sum_relaxation
    {s m : ℕ}
    (hm : Nat.min n (2 ^ s + 1) = m)
    (hm_pos : 0 < m) :
    (fun _ : Fin n ↦ (1 : ℝ) / (m : ℝ)) ∈
      exercise_5_19_subset_sum_relaxation n s := by
  rw [mem_exercise_5_19_subset_sum_relaxation_iff]
  refine ⟨?_, ?_⟩
  · -- The constant witness is coordinatewise nonnegative.
    intro i
    exact one_div_nonneg.mpr (show 0 ≤ (m : ℝ) by positivity)
  · intro I hI
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hm_pos)
    have hIm : I.card = m := by
      simpa [hm] using hI
    have hIm_real : (I.card : ℝ) = m := by
      exact_mod_cast hIm
    -- Every active subset sum of the constant witness is exactly `1`.
    calc
      I.sum (fun _ : Fin n ↦ (1 : ℝ) / (m : ℝ))
          = (I.card : ℝ) * ((m : ℝ)⁻¹) := by
              simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      _ = (m : ℝ) * ((m : ℝ)⁻¹) := by rw [hIm_real]
      _ = 1 := by rw [mul_inv_cancel₀ hm_ne]
      _ ≤ 1 := by simp

/-- Helper for Exercise 5.19: a bounded natural demand vector can be dominated by the indicator
vectors of `k` subsets of size at most `r`. -/
lemma exercise_5_19_packDemandIntoBoundedSubsets
    {r k : ℕ}
    {a : Fin n → ℕ}
    (ha_bound : ∀ i : Fin n, a i ≤ k)
    (ha_sum : ∑ i : Fin n, a i ≤ k * r) :
    ∃ B : Fin k → Finset (Fin n),
      (∀ q, (B q).card ≤ r) ∧
      ∀ i : Fin n, a i ≤ ∑ q : Fin k, if i ∈ B q then 1 else 0 := by
  by_cases hk_zero : k = 0
  · subst k
    refine ⟨fun q ↦ Fin.elim0 q, ?_, ?_⟩
    · intro q
      exact Fin.elim0 q
    · intro i
      -- With no rows available, the coordinate bound forces every demand to vanish.
      simpa using ha_bound i
  · classical
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_zero
    let offset : Fin n → ℕ := fun i ↦ ∑ j ∈ Finset.Iio i, a j
    let position : (Σ i : Fin n, Fin (a i)) → ℕ :=
      fun z ↦ offset z.1 + z.2
    let slots : Fin k → Finset (Σ i : Fin n, Fin (a i)) :=
      fun q ↦ (Finset.univ.sigma fun i ↦ Finset.univ).filter
        (fun z ↦ position z % k = q)
    let B : Fin k → Finset (Fin n) := fun q ↦ (slots q).image Sigma.fst
    have prefix_add (i : Fin n) :
        offset i + a i = ∑ j ∈ Finset.Iic i, a j := by
      rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons]
      simp only [offset]
      omega
    have prefix_mono {i j : Fin n} (hij : i < j) :
        offset i + a i ≤ offset j := by
      rw [prefix_add]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro u hu
        exact Finset.mem_Iio.mpr (lt_of_le_of_lt (Finset.mem_Iic.mp hu) hij)
      · intro u huIio huIic
        exact Nat.zero_le (a u)
    have prefix_le_total (i : Fin n) :
        offset i + a i ≤ ∑ j : Fin n, a j := by
      rw [prefix_add]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun u _ _ ↦
        Nat.zero_le (a u)
    have position_lt_total (z : Σ i : Fin n, Fin (a i)) :
        position z < ∑ j : Fin n, a j := by
      exact lt_of_lt_of_le (by simp [position]) (prefix_le_total z.1)
    have position_injective : Function.Injective position := by
      rintro ⟨i, z⟩ ⟨j, w⟩ hposition
      rcases lt_trichotomy i j with hij | hij | hji
      · have hlt : position ⟨i, z⟩ < position ⟨j, w⟩ := by
          exact lt_of_lt_of_le (by simp [position])
            ((prefix_mono hij).trans (Nat.le_add_right (offset j) w))
        exact (hlt.ne hposition).elim
      · subst j
        have hzw : z = w := by
          apply Fin.ext
          simpa [position] using Nat.add_left_cancel hposition
        subst w
        rfl
      · have hlt : position ⟨j, w⟩ < position ⟨i, z⟩ := by
          exact lt_of_lt_of_le (by simp [position])
            ((prefix_mono hji).trans (Nat.le_add_right (offset i) z))
        exact (hlt.ne hposition.symm).elim
    refine ⟨B, ?_, ?_⟩
    · intro q
      calc
        (B q).card ≤ (slots q).card := by
          exact Finset.card_image_le
        _ ≤ (Finset.range r).card := by
          refine Finset.card_le_card_of_injOn (fun z ↦ position z / k) ?_ ?_
          · intro z hz
            apply Finset.mem_range.mpr
            apply (Nat.div_lt_iff_lt_mul hk_pos).2
            have hposition := position_lt_total z
            exact lt_of_lt_of_le hposition (by simpa [Nat.mul_comm] using ha_sum)
          · intro x hx y hy hquotient
            apply position_injective
            have hxmod : position x % k = q := by
              exact (Finset.mem_filter.mp hx).2
            have hymod : position y % k = q := by
              exact (Finset.mem_filter.mp hy).2
            calc
              position x = position x % k + k * (position x / k) :=
                (Nat.mod_add_div (position x) k).symm
              _ = position y % k + k * (position y / k) := by
                rw [hxmod, hymod]
                exact congrArg (fun v ↦ (q : ℕ) + k * v) hquotient
              _ = position y := Nat.mod_add_div (position y) k
        _ = r := Finset.card_range r
    · intro i
      let residue : Fin (a i) → Fin k := fun z ↦
        ⟨(offset i + z) % k, Nat.mod_lt _ hk_pos⟩
      have residue_maps :
          Set.MapsTo residue (Finset.univ : Finset (Fin (a i)))
            ((Finset.univ : Finset (Fin k)).filter fun q ↦ i ∈ B q) := by
        intro z hz
        have hmem : i ∈ B (residue z) := by
          dsimp [B]
          rw [Finset.mem_image]
          refine ⟨⟨i, z⟩, ?_, rfl⟩
          simp [slots, position, residue]
        simpa using hmem
      have residue_injective : Set.InjOn residue (Finset.univ : Finset (Fin (a i))) := by
        intro z hz w hw hresidue
        have hmod : offset i + z ≡ offset i + w [MOD k] := by
          exact congrArg Fin.val hresidue
        have hzw_le : offset i + z ≤ offset i + w := by
          apply hmod.le_of_lt_add
          have hz_lt : (z : ℕ) < k := lt_of_lt_of_le z.isLt (ha_bound i)
          omega
        have hwz_le : offset i + w ≤ offset i + z := by
          apply hmod.symm.le_of_lt_add
          have hw_lt : (w : ℕ) < k := lt_of_lt_of_le w.isLt (ha_bound i)
          omega
        apply Fin.ext
        omega
      have hcard := Finset.card_le_card_of_injOn residue residue_maps residue_injective
      calc
        a i = (Finset.univ : Finset (Fin (a i))).card := by simp
        _ ≤ ((Finset.univ : Finset (Fin k)).filter fun q ↦ i ∈ B q).card := hcard
        _ = ∑ q : Fin k, if i ∈ B q then 1 else 0 := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
            (Finset.card_eq_sum_ite
              (Finset.filter_subset (fun q : Fin k ↦ i ∈ B q) Finset.univ))

/-- Helper for Exercise 5.19: on the unsaturated branch, averaging all active stage-`s`
subset inequalities over the `m`-subsets of a next-stage support bounds the total support sum. -/
lemma exercise_5_19_nextStageSubset_average_bound
    {s : ℕ}
    {J : Finset (Fin n)}
    {y : Fin n → ℝ}
    (hsat : Nat.min n (2 ^ s + 1) ≠ n)
    (hy : y ∈ exercise_5_19_subset_sum_relaxation n s)
    (hJ : J.card = Nat.min n (2 ^ (s + 1) + 1)) :
    J.sum y ≤ (J.card : ℝ) / (Nat.min n (2 ^ s + 1) : ℝ) := by
  classical
  let m := Nat.min n (2 ^ s + 1)
  have hpow_lt_n : 2 ^ s + 1 < n := by
    by_contra hnot
    exact hsat (Nat.min_eq_left (by omega))
  have hm_eq : m = 2 ^ s + 1 := Nat.min_eq_right (le_of_lt hpow_lt_n)
  have hm_pos : 0 < m := by
    rw [hm_eq]
    positivity
  have hm_le_J : m ≤ J.card := by
    rw [hJ, hm_eq]
    exact le_min (le_of_lt hpow_lt_n) (by omega)
  let c := Nat.choose (J.card - 1) (m - 1)
  have hdoubleCount :
      ∑ I ∈ J.powersetCard m, I.sum y = (c : ℝ) * J.sum y := by
    -- Exchange the subset and coordinate sums, then count the active subsets containing a point.
    calc
      ∑ I ∈ J.powersetCard m, I.sum y =
          ∑ I ∈ J.powersetCard m, ∑ i ∈ J, if i ∈ I then y i else 0 := by
            refine Finset.sum_congr rfl ?_
            intro I hI
            have hIJ : I ⊆ J := (Finset.mem_powersetCard.mp hI).1
            symm
            refine (Finset.sum_ite_mem (s := J) (t := I) (f := y)).trans ?_
            simp [Finset.inter_eq_right.mpr hIJ]
      _ = ∑ i ∈ J, ∑ I ∈ J.powersetCard m, if i ∈ I then y i else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ i ∈ J, (c : ℝ) * y i := by
            refine Finset.sum_congr rfl ?_
            intro i hiJ
            have hcount :
                ((J.powersetCard m).filter fun I ↦ i ∈ I).card = c := by
              simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using
                Finset.card_filter_powersetCard_subset ({i} : Finset (Fin n)) J m
                  (by simp [hiJ]) hm_pos
            calc
              (∑ I ∈ J.powersetCard m, if i ∈ I then y i else 0) =
                  (∑ I ∈ J.powersetCard m, (if i ∈ I then (1 : ℝ) else 0) * y i) := by
                    refine Finset.sum_congr rfl ?_
                    intro I hI
                    by_cases hiI : i ∈ I <;> simp [hiI]
              _ = (∑ I ∈ J.powersetCard m, if i ∈ I then (1 : ℝ) else 0) * y i := by
                    rw [Finset.sum_mul]
              _ = (c : ℝ) * y i := by
                    congr 1
                    rw [Finset.sum_boole]
                    exact_mod_cast hcount
      _ = (c : ℝ) * J.sum y := by
            rw [Finset.mul_sum]
  have hsumSubsets :
      ∑ I ∈ J.powersetCard m, I.sum y ≤
        ∑ I ∈ J.powersetCard m, (1 : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro I hI
    exact (mem_exercise_5_19_subset_sum_relaxation_iff.mp hy).2 I
      (by simpa [m] using (Finset.mem_powersetCard.mp hI).2)
  have hscaled :
      (c : ℝ) * J.sum y ≤ (Nat.choose J.card m : ℝ) := by
    calc
      (c : ℝ) * J.sum y = ∑ I ∈ J.powersetCard m, I.sum y := hdoubleCount.symm
      _ ≤ ∑ I ∈ J.powersetCard m, (1 : ℝ) := hsumSubsets
      _ = (Nat.choose J.card m : ℝ) := by simp
  have hJ_pos : 0 < J.card := lt_of_lt_of_le hm_pos hm_le_J
  have hchooseIdentity :
      J.card * c = Nat.choose J.card m * m := by
    simpa [c, Nat.sub_add_cancel hJ_pos, Nat.sub_add_cancel hm_pos] using
      Nat.add_one_mul_choose_eq (J.card - 1) (m - 1)
  have hc_pos_nat : 0 < c := by
    exact Nat.choose_pos (by omega)
  have hc_pos : 0 < (c : ℝ) := by
    exact_mod_cast hc_pos_nat
  have hm_pos_real : 0 < (m : ℝ) := by
    exact_mod_cast hm_pos
  -- Multiply by the positive incidence count, use the binomial identity, and cancel it.
  apply (le_div_iff₀ hm_pos_real).2
  apply (mul_le_mul_iff_left₀ hc_pos).mp
  calc
    (J.sum y * (m : ℝ)) * (c : ℝ) = ((c : ℝ) * J.sum y) * (m : ℝ) := by ring
    _ ≤ (Nat.choose J.card m : ℝ) * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hscaled hm_pos_real.le
    _ = (J.card : ℝ) * (c : ℝ) := by exact_mod_cast hchooseIdentity.symm

/-- Helper for Exercise 5.19: if `|J|` lies between `m` and `2m`, then dividing by `m` has
floor exactly `1`. -/
lemma exercise_5_19_floor_div_card_eq_one
    {J : Finset (Fin n)}
    {m : ℕ}
    (hm_pos : 0 < m)
    (hm_le : m ≤ J.card)
    (hJ_lt : J.card < 2 * m) :
    Int.floor ((J.card : ℝ) / (m : ℝ)) = 1 := by
  have hm_pos_real : 0 < (m : ℝ) := by
    exact_mod_cast hm_pos
  -- Put the quotient into the interval `[1, 2)`, which is the defining window for floor `1`.
  apply Int.floor_eq_iff.mpr
  constructor
  · have hJ_ge_real : (m : ℝ) ≤ J.card := by
      exact_mod_cast hm_le
    exact (le_div_iff₀ hm_pos_real).2 (by simpa using hJ_ge_real)
  · have hdiv_lt : (J.card : ℝ) / (m : ℝ) < (1 : ℝ) + 1 := by
      exact (div_lt_iff₀ hm_pos_real).2 (by exact_mod_cast hJ_lt)
    simpa using hdiv_lt

/-- Helper for Exercise 5.19: in the unsaturated branch, a valid nonnegative integer cut on the
stage-`s` relaxation has coefficients bounded by `⌊d⌋` and total demand bounded by the true
next-stage threshold. -/
lemma exercise_5_19_natValidInequality_bounds_of_unsaturated
    {s : ℕ}
    {a : Fin n → ℕ}
    {d : ℝ}
    (hsat : Nat.min n (2 ^ s + 1) ≠ n)
    (hvalid :
      is_valid_inequality
        (exercise_5_19_subset_sum_relaxation n s)
        (fun i ↦ (a i : ℝ)) d) :
    let k := Int.toNat (Int.floor d)
    (∀ i : Fin n, a i ≤ k) ∧
      ∑ i : Fin n, a i ≤ k * Nat.min n (2 ^ (s + 1) + 1) := by
  let m := Nat.min n (2 ^ s + 1)
  let k := Int.toNat (Int.floor d)
  change (∀ i : Fin n, a i ≤ k) ∧
    ∑ i : Fin n, a i ≤ k * Nat.min n (2 ^ (s + 1) + 1)
  have hpow_lt_n : 2 ^ s + 1 < n := by
    by_contra hnot
    exact hsat (Nat.min_eq_left (by omega))
  have hm_eq : m = 2 ^ s + 1 := Nat.min_eq_right (le_of_lt hpow_lt_n)
  have hm_pos : 0 < m := by
    rw [hm_eq]
    positivity
  have hd_nonneg : 0 ≤ d := by
    -- Validity at the zero vector fixes the sign needed to identify `k` with the floor.
    simpa using hvalid (exercise_5_19_zero_mem_subset_sum_relaxation n s)
  have hfloor_nonneg : 0 ≤ Int.floor d := Int.floor_nonneg.mpr hd_nonneg
  have hk_int : (k : ℤ) = Int.floor d := by
    exact Int.toNat_of_nonneg hfloor_nonneg
  have hk_real : (k : ℝ) = ((Int.floor d : ℤ) : ℝ) := by
    exact_mod_cast hk_int
  have ha_bound : ∀ i : Fin n, a i ≤ k := by
    intro i
    have hsingle :
        (fun j ↦ (a j : ℝ)) ⬝ᵥ Pi.single i (1 : ℝ) ≤ d :=
      hvalid (exercise_5_19_single_mem_subset_sum_relaxation n s i)
    have hai_le_d : (a i : ℝ) ≤ d := by
      simpa [dotProduct, Pi.single_apply] using hsingle
    have hai_floor : (a i : ℤ) ≤ Int.floor d := Int.le_floor.mpr hai_le_d
    exact_mod_cast hai_floor.trans_eq hk_int.symm
  have hwitness := hvalid
    (exercise_5_19_constantWitness_mem_subset_sum_relaxation
      (n := n) (s := s) (m := m) rfl hm_pos)
  have hratio :
      ((∑ i : Fin n, a i : ℕ) : ℝ) / (m : ℝ) ≤ d := by
    simpa [dotProduct, div_eq_mul_inv, ← Finset.sum_mul] using hwitness
  have hd_lt : d < (k : ℝ) + 1 := by
    calc
      d < ((Int.floor d : ℤ) : ℝ) + 1 := Int.lt_floor_add_one d
      _ = (k : ℝ) + 1 := by rw [hk_real]
  have hm_pos_real : 0 < (m : ℝ) := by
    exact_mod_cast hm_pos
  have hsum_lt_real :
      ((∑ i : Fin n, a i : ℕ) : ℝ) < (m : ℝ) * ((k : ℝ) + 1) := by
    simpa [mul_comm] using (div_lt_iff₀ hm_pos_real).mp (hratio.trans_lt hd_lt)
  have hsum_lt : ∑ i : Fin n, a i < m * (k + 1) := by
    exact_mod_cast hsum_lt_real
  refine ⟨ha_bound, ?_⟩
  by_cases hn_next : n ≤ 2 ^ (s + 1) + 1
  · -- If the next threshold is `n`, sum the coordinatewise floor bounds.
    calc
      ∑ i : Fin n, a i ≤ ∑ _i : Fin n, k :=
        Finset.sum_le_sum fun i _ ↦ ha_bound i
      _ = n * k := by simp
      _ = k * n := Nat.mul_comm n k
      _ = k * Nat.min n (2 ^ (s + 1) + 1) := by
        exact congrArg (fun u ↦ k * u) (Nat.min_eq_left hn_next).symm
  · have hnext_eq : 2 ^ (s + 1) + 1 = 2 * m - 1 := by
      rw [hm_eq, pow_succ]
      omega
    have hthreshold : Nat.min n (2 ^ (s + 1) + 1) = 2 * m - 1 :=
      (Nat.min_eq_right (le_of_not_ge hn_next)).trans hnext_eq
    apply le_of_le_of_eq ?_ (congrArg (fun u ↦ k * u) hthreshold.symm)
    by_cases hk_zero : k = 0
    · have ha_zero : ∀ i : Fin n, a i = 0 := by
        intro i
        specialize ha_bound i
        omega
      simp [hk_zero, ha_zero]
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_zero
      -- The strict constant-witness bound fits below `k(2m-1)` as soon as `k ≥ 1`.
      have hk_decomp : k = (k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
      have hm_decomp : m = (m - 1) + 1 := (Nat.sub_add_cancel hm_pos).symm
      have htwo_m_pos : 0 < 2 * m := Nat.mul_pos (by decide) hm_pos
      have htwo_m_decomp : 2 * m = (2 * m - 1) + 1 :=
        (Nat.sub_add_cancel htwo_m_pos).symm
      have hproduct_nonneg : 0 ≤ (k - 1) * (m - 1) := Nat.zero_le _
      nlinarith

/-- Helper for Exercise 5.19: once the nat demand bounds are packed into next-stage subsets,
every point of the next relaxation satisfies the resulting rounded inequality. -/
lemma exercise_5_19_natDotProduct_le_of_packedNextStage
    {s k : ℕ}
    {x : Fin n → ℝ}
    {a : Fin n → ℕ}
    (hx : x ∈ exercise_5_19_subset_sum_relaxation n (s + 1))
    (ha_bound : ∀ i : Fin n, a i ≤ k)
    (ha_sum : ∑ i : Fin n, a i ≤ k * Nat.min n (2 ^ (s + 1) + 1)) :
    (fun i ↦ (a i : ℝ)) ⬝ᵥ x ≤ (k : ℝ) := by
  obtain ⟨B, hB_card, hB_dom⟩ :=
    exercise_5_19_packDemandIntoBoundedSubsets (n := n) ha_bound ha_sum
  have hx_nonneg : ∀ i : Fin n, 0 ≤ x i :=
    (mem_exercise_5_19_subset_sum_relaxation_iff.mp hx).1
  have hsubset_bound : ∀ q : Fin k, (B q).sum x ≤ 1 := by
    intro q
    exact exercise_5_19_subset_sum_relaxation_card_le (n := n) (t := s + 1) hx (hB_card q)
  have hcoord_le :
      ∑ i : Fin n, (a i : ℝ) * x i ≤
        ∑ i : Fin n, (((∑ q : Fin k, if i ∈ B q then 1 else 0 : ℕ) : ℝ) * x i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hB_dom i) (hx_nonneg i)
  have hrewrite :
      ∑ i : Fin n, (((∑ q : Fin k, if i ∈ B q then 1 else 0 : ℕ) : ℝ) * x i) =
        ∑ q : Fin k, (B q).sum x := by
    -- Swap the packed subset count with the coordinate sum.
    calc
      ∑ i : Fin n, (((∑ q : Fin k, if i ∈ B q then 1 else 0 : ℕ) : ℝ) * x i)
          = ∑ i : Fin n, ∑ q : Fin k, (((if i ∈ B q then 1 else 0 : ℕ) : ℝ) * x i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [Nat.cast_sum, Finset.sum_mul]
      _ = ∑ q : Fin k, ∑ i : Fin n, (((if i ∈ B q then 1 else 0 : ℕ) : ℝ) * x i) := by
            rw [Finset.sum_comm]
      _ = ∑ q : Fin k, (B q).sum x := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            calc
              ∑ i : Fin n, (((if i ∈ B q then 1 else 0 : ℕ) : ℝ) * x i)
                  = ∑ i : Fin n, if i ∈ B q then x i else 0 := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      by_cases hiB : i ∈ B q <;> simp [hiB]
              _ = (B q).sum x := by
                    refine
                      (Finset.sum_ite_mem (s := Finset.univ) (t := B q) (f := x)).trans ?_
                    simp
  calc
    (fun i ↦ (a i : ℝ)) ⬝ᵥ x = ∑ i : Fin n, (a i : ℝ) * x i := by
      rfl
    _ ≤ ∑ i : Fin n, (((∑ q : Fin k, if i ∈ B q then 1 else 0 : ℕ) : ℝ) * x i) := hcoord_le
    _ = ∑ q : Fin k, (B q).sum x := hrewrite
    _ ≤ ∑ q : Fin k, (1 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro q hq
          exact hsubset_bound q
    _ = (k : ℝ) := by
          simp

/-- Helper for Exercise 5.19: the next pure-integer Chvátal closure step should enlarge the
active subset size from `min(n, 2^s + 1)` to `min(n, 2^(s + 1) + 1)`. The saturated simplex
branch is already formalized; the genuinely unsaturated branch still needs the averaged-cut
forward inclusion and the row-multiplier normalization for reverse inclusion. -/
lemma exercise_5_19_subset_sum_relaxation_oneStep
    (s : ℕ) :
    pure_integer_chvatal_closure (exercise_5_19_subset_sum_relaxation n s) =
      exercise_5_19_subset_sum_relaxation n (s + 1) := by
  by_cases hsat : Nat.min n (2 ^ s + 1) = n
  · -- Once the current stage is the simplex, the next stage is the same simplex.
    exact exercise_5_19_subset_sum_relaxation_oneStep_of_stage_saturated
      (n := n) (s := s) hsat
  · -- Route correction: the easy simplex branch is now separated.
    have hsat_ne : Nat.min n (2 ^ s + 1) ≠ n := hsat
    have hpow_lt_n : 2 ^ s + 1 < n := by
      by_contra hcontra
      have hn_le : n ≤ 2 ^ s + 1 := by omega
      exact hsat_ne (Nat.min_eq_left hn_le)
    let m := Nat.min n (2 ^ s + 1)
    let r := Nat.min n (2 ^ (s + 1) + 1)
    have hm_eq : m = 2 ^ s + 1 := by
      exact Nat.min_eq_right (le_of_lt hpow_lt_n)
    have hm_pos : 0 < m := by
      rw [hm_eq]
      positivity
    have hm_le_r : m ≤ r := by
      rw [hm_eq]
      dsimp [r]
      exact le_min (le_of_lt hpow_lt_n) (by omega)
    have hr_lt_two_m : r < 2 * m := by
      rw [hm_eq]
      dsimp [r]
      have hmin_lt : Nat.min n (2 ^ (s + 1) + 1) < 2 ^ (s + 1) + 2 := by
        exact lt_of_le_of_lt (Nat.min_le_right n (2 ^ (s + 1) + 1)) (by omega)
      omega
    ext x
    constructor
    · intro hx
      rw [mem_pure_integer_chvatal_closure_iff] at hx
      rw [mem_exercise_5_19_subset_sum_relaxation_iff]
      refine ⟨hx.1.1, ?_⟩
      intro J hJ
      have hvalidJ :
          is_valid_inequality
            (exercise_5_19_subset_sum_relaxation n s)
            (fun i ↦ ↑(if i ∈ J then (1 : ℤ) else 0 : ℤ))
            ((J.card : ℝ) / (m : ℝ)) := by
        intro y hy
        -- The averaged subset-counting bound packages the exact forward cut.
        have hsum_le :
            J.sum y ≤ (J.card : ℝ) / (m : ℝ) :=
          exercise_5_19_nextStageSubset_average_bound (n := n) (s := s)
            hsat_ne hy (by simpa [r] using hJ)
        calc
          (fun i ↦ ↑(if i ∈ J then (1 : ℤ) else 0 : ℤ)) ⬝ᵥ y
              = ∑ i : Fin n, if i ∈ J then (1 : ℝ) * y i else 0 := by
                  simp [dotProduct]
          _ = J.sum y := by
                refine
                  (Finset.sum_ite_mem (s := Finset.univ) (t := J)
                    (f := fun i : Fin n ↦ (1 : ℝ) * y i)).trans ?_
                simp
          _ ≤ (J.card : ℝ) / (m : ℝ) := hsum_le
      have hcut :
          (fun i ↦ ↑(if i ∈ J then (1 : ℤ) else 0 : ℤ)) ⬝ᵥ x ≤
            ((Int.floor ((J.card : ℝ) / (m : ℝ)) : ℤ) : ℝ) :=
        hx.2 (fun i ↦ if i ∈ J then (1 : ℤ) else 0) ((J.card : ℝ) / (m : ℝ)) hvalidJ
      have hm_pos_real : 0 < (m : ℝ) := by
        exact_mod_cast hm_pos
      have hfloor_one :
          Int.floor ((J.card : ℝ) / (m : ℝ)) = 1 := by
        have hJ_ge : m ≤ J.card := by
          rw [hJ]
          exact hm_le_r
        have hJ_lt : J.card < 2 * m := by
          rw [hJ]
          exact hr_lt_two_m
        -- Keep the floor arithmetic behind the dedicated division helper.
        exact exercise_5_19_floor_div_card_eq_one (n := n) hm_pos hJ_ge hJ_lt
      have hsum_cut :
          J.sum x ≤ 1 := by
        calc
          J.sum x = ∑ i : Fin n, if i ∈ J then (1 : ℝ) * x i else 0 := by
              symm
              refine
                (Finset.sum_ite_mem (s := Finset.univ) (t := J)
                  (f := fun i : Fin n ↦ (1 : ℝ) * x i)).trans ?_
              simp
          _ = (fun i ↦ ↑(if i ∈ J then (1 : ℤ) else 0 : ℤ)) ⬝ᵥ x := by
                simp [dotProduct]
          _ ≤ ((Int.floor ((J.card : ℝ) / (m : ℝ)) : ℤ) : ℝ) := hcut
          _ = 1 := by simp [hfloor_one]
      exact hsum_cut
    · intro hx
      rw [mem_exercise_5_19_subset_sum_relaxation_iff] at hx
      rw [mem_pure_integer_chvatal_closure_iff]
      refine ⟨⟨hx.1, ?_⟩, ?_⟩
      · intro I hI
        exact exercise_5_19_subset_sum_relaxation_card_le (n := n) (t := s + 1)
          ⟨hx.1, hx.2⟩ (by
            rw [hI]
            exact hm_le_r)
      · intro c d hvalid
        have hvalidPos :
            is_valid_inequality
              (exercise_5_19_subset_sum_relaxation n s)
              (fun i ↦ ((max (c i) 0 : ℤ) : ℝ)) d :=
          exercise_5_19_positivePart_is_valid_on_subset_sum_relaxation (n := n)
            (s := s) hvalid
        let a : Fin n → ℕ := fun i ↦ Int.toNat (max (c i) 0)
        have ha_cast :
            (fun i ↦ (a i : ℝ)) = (fun i ↦ ((max (c i) 0 : ℤ) : ℝ)) := by
          funext i
          have hmax_nonneg : 0 ≤ max (c i) 0 := le_max_right _ _
          dsimp [a]
          exact_mod_cast (Int.toNat_of_nonneg hmax_nonneg)
        obtain ⟨ha_bound, ha_sum⟩ :=
          exercise_5_19_natValidInequality_bounds_of_unsaturated (n := n) (s := s)
            (a := a) (d := d) hsat_ne (by simpa [ha_cast] using hvalidPos)
        have hnat_cut :
            (fun i ↦ (a i : ℝ)) ⬝ᵥ x ≤ (Int.toNat (Int.floor d) : ℝ) :=
          exercise_5_19_natDotProduct_le_of_packedNextStage (n := n) (s := s)
            (x := x) (a := a) (k := Int.toNat (Int.floor d)) ⟨hx.1, hx.2⟩ ha_bound ha_sum
        have hfloor_nonneg : 0 ≤ Int.floor d := by
          have hd_nonneg : 0 ≤ d := by
            simpa using hvalidPos (exercise_5_19_zero_mem_subset_sum_relaxation n s)
          exact Int.floor_nonneg.mpr hd_nonneg
        have hk_cast :
            (Int.toNat (Int.floor d) : ℝ) = ((Int.floor d : ℤ) : ℝ) := by
          exact_mod_cast (Int.toNat_of_nonneg hfloor_nonneg)
        have horig_le_pos :
            (fun i ↦ (c i : ℝ)) ⬝ᵥ x ≤
              (fun i ↦ ((max (c i) 0 : ℤ) : ℝ)) ⬝ᵥ x := by
          -- On the nonnegative next-stage point, dropping negative coefficients can only
          -- increase the dot product.
          refine Finset.sum_le_sum ?_
          intro i hi
          have hci_le : (c i : ℝ) ≤ ((max (c i) 0 : ℤ) : ℝ) := by
            exact_mod_cast (le_max_left (c i) 0)
          exact mul_le_mul_of_nonneg_right hci_le (hx.1 i)
        calc
          (fun i ↦ (c i : ℝ)) ⬝ᵥ x
              ≤ (fun i ↦ ((max (c i) 0 : ℤ) : ℝ)) ⬝ᵥ x := horig_le_pos
          _ = (fun i ↦ (a i : ℝ)) ⬝ᵥ x := by rw [ha_cast]
          _ ≤ (Int.toNat (Int.floor d) : ℝ) := hnat_cut
          _ = ((Int.floor d : ℤ) : ℝ) := hk_cast

/-- Validity of the all-ones coefficient vector with right-hand side `1` is exactly the textbook
inequality `∑_{j=1}^n x_j ≤ 1`. -/
theorem exercise_5_19_sum_le_one_valid_iff
    {Q : Set (Fin n → ℝ)} :
    is_valid_inequality Q (1 : Fin n → ℝ) 1 ↔
      ∀ ⦃x : Fin n → ℝ⦄, x ∈ Q → ∑ j : Fin n, x j ≤ 1 := by
  simp [is_valid_inequality, one_dotProduct]

/-- For Exercise 5.19, when `n ≥ 3`, the positive Chvátal iterates of `P` are exactly the
corresponding threshold subset-sum relaxations. -/
theorem exercise_5_19_chvatal_iterate_succ_eq_subset_sum_relaxation
    (hn : 3 ≤ n) (t : ℕ) :
    (pure_integer_chvatal_closure^[t + 1]) (exercise_5_19_polyhedron n) =
      exercise_5_19_subset_sum_relaxation n (t + 1) := by
  have hn_two : 2 ≤ n := by
    omega
  have hpoly :
      exercise_5_19_polyhedron n = exercise_5_19_subset_sum_relaxation n 0 :=
    exercise_5_19_polyhedron_eq_subset_sum_relaxation_zero hn_two
  -- Route correction: keep the main theorem as a positive-stage iterate statement, but expose the
  -- true stage-`0` model so the induction only has to consume one named closure step.
  have hstep := exercise_5_19_subset_sum_relaxation_oneStep (n := n)
  induction t with
  | zero =>
      -- The first iterate is the one-step closure of the stage-`0` presentation of `P`.
      calc
        (pure_integer_chvatal_closure^[0 + 1]) (exercise_5_19_polyhedron n)
            = pure_integer_chvatal_closure (exercise_5_19_polyhedron n) := by
                simp
        _ = pure_integer_chvatal_closure (exercise_5_19_subset_sum_relaxation n 0) := by
              rw [hpoly]
        _ = exercise_5_19_subset_sum_relaxation n (0 + 1) := hstep 0
  | succ t ih =>
      -- Push one closure step through the induction hypothesis and then apply the uniform step.
      calc
        (pure_integer_chvatal_closure^[Nat.succ t + 1]) (exercise_5_19_polyhedron n)
            = pure_integer_chvatal_closure
                ((pure_integer_chvatal_closure^[t + 1]) (exercise_5_19_polyhedron n)) := by
                  simp [Function.iterate_succ_apply']
        _ = pure_integer_chvatal_closure (exercise_5_19_subset_sum_relaxation n (t + 1)) := by
              rw [ih]
        _ = exercise_5_19_subset_sum_relaxation n ((t + 1) + 1) := hstep (t + 1)
        _ = exercise_5_19_subset_sum_relaxation n (Nat.succ t + 1) := by
              simp [Nat.add_assoc]

/-- When `n ≥ 3`, membership in the positive Chvátal iterates of `P` is described by
nonnegativity together with the threshold subset-sum bounds
`∑_{i ∈ I} x_i ≤ 1` for all subsets `I` of cardinality `min(n, 2^(t + 1) + 1)`. -/
theorem mem_exercise_5_19_chvatal_iterate_succ_iff
    (hn : 3 ≤ n)
    {t : ℕ}
    {x : Fin n → ℝ} :
    x ∈ (pure_integer_chvatal_closure^[t + 1]) (exercise_5_19_polyhedron n) ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ I : Finset (Fin n),
          I.card = Nat.min n (2 ^ (t + 1) + 1) → I.sum x ≤ 1 := by
  rw [exercise_5_19_chvatal_iterate_succ_eq_subset_sum_relaxation hn t]
  rfl

/-- Helper for Exercise 5.19: on every positive stage, the constant witness with denominator
`2^(t + 1) - 1` survives in the `t`-th subset-sum relaxation. -/
lemma exercise_5_19_uniformWitness_mem_subset_sum_relaxation
    {t : ℕ} (ht : 1 ≤ t) :
    (fun _ : Fin n ↦ (1 : ℝ) / ((2 ^ (t + 1) - 1 : ℕ) : ℝ)) ∈
      exercise_5_19_subset_sum_relaxation n t := by
  rw [mem_exercise_5_19_subset_sum_relaxation_iff]
  refine ⟨?_, ?_⟩
  · -- The constant witness is coordinatewise nonnegative because its denominator is positive.
    intro i
    have hpow_ge_four : 4 ≤ 2 ^ (t + 1) := by
      simpa using
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ t + 1) :
          2 ^ 2 ≤ 2 ^ (t + 1))
    have hden_pos_nat : 0 < 2 ^ (t + 1) - 1 := by
      omega
    have hden_pos : 0 < (((2 ^ (t + 1) - 1 : ℕ) : ℝ)) := by
      exact_mod_cast hden_pos_nat
    exact (one_div_pos.mpr hden_pos).le
  · intro I hI
    -- Rewrite the subset sum of the constant vector and compare the cardinality to the denominator.
    have hpow_ge_four : 4 ≤ 2 ^ (t + 1) := by
      simpa using
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ t + 1) :
          2 ^ 2 ≤ 2 ^ (t + 1))
    have hden_pos_nat : 0 < 2 ^ (t + 1) - 1 := by
      omega
    have hden_pos : 0 < (((2 ^ (t + 1) - 1 : ℕ) : ℝ)) := by
      exact_mod_cast hden_pos_nat
    have hbound_nat : I.card ≤ 2 ^ (t + 1) - 1 := by
      rw [hI]
      refine (Nat.min_le_right n (2 ^ t + 1)).trans ?_
      have hpow_ge_two : 2 ≤ 2 ^ t := by
        simpa using
          (Nat.pow_le_pow_right (by decide : 0 < 2) ht : 2 ^ 1 ≤ 2 ^ t)
      omega
    have hbound : (I.card : ℝ) ≤ (((2 ^ (t + 1) - 1 : ℕ) : ℝ)) := by
      exact_mod_cast hbound_nat
    have hinv_nonneg : 0 ≤ ((((2 ^ (t + 1) - 1 : ℕ) : ℝ))⁻¹) := by
      positivity
    have hsum :
        I.sum (fun _ : Fin n ↦ (1 : ℝ) / ((2 ^ (t + 1) - 1 : ℕ) : ℝ)) =
          (I.card : ℝ) * ((((2 ^ (t + 1) - 1 : ℕ) : ℝ))⁻¹) := by
      simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    calc
      I.sum (fun _ : Fin n ↦ (1 : ℝ) / ((2 ^ (t + 1) - 1 : ℕ) : ℝ))
          = (I.card : ℝ) * ((((2 ^ (t + 1) - 1 : ℕ) : ℝ))⁻¹) := hsum
      _ ≤ (((2 ^ (t + 1) - 1 : ℕ) : ℝ)) * ((((2 ^ (t + 1) - 1 : ℕ) : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_right hbound hinv_nonneg
      _ = 1 := by
            rw [mul_inv_cancel₀ hden_pos.ne']

/-- Helper for Exercise 5.19: on the source branch `n ≥ 3`, the all-ones inequality is already
valid on the `(Nat.log 2 n + 1)`-st Chvátal iterate. -/
theorem exercise_5_19_sum_le_one_valid_on_logIterate
    (hn : 3 ≤ n) :
    is_valid_inequality
      ((pure_integer_chvatal_closure^[Nat.log 2 n + 1]) (exercise_5_19_polyhedron n))
      (1 : Fin n → ℝ) 1 := by
  rw [exercise_5_19_sum_le_one_valid_iff]
  intro x hx
  -- Move to the explicit subset-sum description of the logarithmic iterate.
  rw [exercise_5_19_chvatal_iterate_succ_eq_subset_sum_relaxation hn (Nat.log 2 n)] at hx
  rw [mem_exercise_5_19_subset_sum_relaxation_iff] at hx
  have hmin : Nat.min n (2 ^ (Nat.log 2 n + 1) + 1) = n := by
    apply Nat.min_eq_left
    have hpow : n < 2 ^ (Nat.log 2 n + 1) := by
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two n
    omega
  have hfull :
      (Finset.univ : Finset (Fin n)).sum x ≤ 1 :=
    hx.2 Finset.univ (by simp [hmin])
  simpa using hfull

/--
remote integer-programming proof cleanup Integer/Chapters/Chap05/section_5_6/ch5_sec5_6_exercise_5_19.lean

Exercise 5.19 (1). For
`P := {x ∈ ℝ_+^n | x_i + x_j ≤ 1 for all 1 ≤ i < j ≤ n}` and
`S = P ∩ {0,1}^n`, if the inequality `∑_{j=1}^n x_j ≤ 1` has Chvatal rank `k`, then
`⌊log₂ n⌋ ≤ k` for `n ≥ 3`. -/
theorem exercise_5_19_sum_le_one_chvatal_rank_lower_bound
    (hn : 3 ≤ n)
    {k : ℕ}
    (hk : is_iterate_rank_of_inequality pure_integer_chvatal_closure
      (exercise_5_19_polyhedron n) (1 : Fin n → ℝ) 1 k) :
    Nat.log 2 n ≤ k := by
  by_contra hbound
  have hklt : k < Nat.log 2 n := by
    exact lt_of_not_ge hbound
  have hnotvalid :
      ¬ is_valid_inequality
        ((pure_integer_chvatal_closure^[k]) (exercise_5_19_polyhedron n))
        (1 : Fin n → ℝ) 1 := by
    cases k with
    | zero =>
        intro hvalid
        rw [exercise_5_19_sum_le_one_valid_iff] at hvalid
        let x : Fin n → ℝ := fun _ ↦ (1 / 2 : ℝ)
        have hx_mem : x ∈ exercise_5_19_polyhedron n := by
          rw [mem_exercise_5_19_polyhedron_iff]
          refine ⟨?_, ?_⟩
          · intro i
            norm_num [x]
          · intro i j hij
            norm_num [x]
        have hsum_le : ∑ j : Fin n, x j ≤ 1 := hvalid hx_mem
        have hsum_eq : ∑ j : Fin n, x j = (n : ℝ) * (1 / 2 : ℝ) := by
          simp [x, Finset.sum_const, nsmul_eq_mul]
        have hn_real : (3 : ℝ) ≤ n := by
          exact_mod_cast hn
        rw [hsum_eq] at hsum_le
        nlinarith
    | succ j =>
        intro hvalid
        rw [exercise_5_19_sum_le_one_valid_iff] at hvalid
        let x : Fin n → ℝ := fun _ ↦ (1 : ℝ) / ((2 ^ (j + 2) - 1 : ℕ) : ℝ)
        have hx_mem_subset :
            x ∈ exercise_5_19_subset_sum_relaxation n (j + 1) :=
          exercise_5_19_uniformWitness_mem_subset_sum_relaxation
            (t := j + 1) (Nat.succ_le_succ (Nat.zero_le j))
        have hx_mem_iterate :
            x ∈ (pure_integer_chvatal_closure^[j + 1]) (exercise_5_19_polyhedron n) := by
          rw [exercise_5_19_chvatal_iterate_succ_eq_subset_sum_relaxation hn j]
          exact hx_mem_subset
        have hsum_le : ∑ i : Fin n, x i ≤ 1 := hvalid hx_mem_iterate
        have hjlt : j + 1 < Nat.log 2 n := by
          simpa using hklt
        have hn0 : n ≠ 0 := by
          exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hn)
        have hpow_le : 2 ^ (j + 2) ≤ n := by
          refine (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_of_lt hjlt)).trans ?_
          exact Nat.pow_log_le_self 2 hn0
        have hden_lt_nat : 2 ^ (j + 2) - 1 < n := by
          omega
        have hpow_ge_four : 4 ≤ 2 ^ (j + 2) := by
          simpa using
            (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ j + 2) :
              2 ^ 2 ≤ 2 ^ (j + 2))
        have hden_pos_nat : 0 < 2 ^ (j + 2) - 1 := by
          omega
        have hden_pos : 0 < (((2 ^ (j + 2) - 1 : ℕ) : ℝ)) := by
          exact_mod_cast hden_pos_nat
        have hden_lt : (((2 ^ (j + 2) - 1 : ℕ) : ℝ)) < n := by
          exact_mod_cast hden_lt_nat
        have hsum_eq : ∑ i : Fin n, x i = (n : ℝ) * (1 / (((2 ^ (j + 2) - 1 : ℕ) : ℝ))) := by
          simp [x, Finset.sum_const, nsmul_eq_mul]
        have hsum_gt : 1 < ∑ i : Fin n, x i := by
          rw [hsum_eq]
          simpa [div_eq_mul_inv] using (one_lt_div hden_pos).2 hden_lt
        linarith
  exact hnotvalid hk.valid_on_iterate

/-- Exercise 5.19 (2). For
`P := {x ∈ ℝ_+^n | x_i + x_j ≤ 1 for all 1 ≤ i < j ≤ n}` and
`S = P ∩ {0,1}^n`, if the inequality `∑_{j=1}^n x_j ≤ 1` has Chvatal rank `k`, then
`k ≤ ⌊log₂ n⌋ + 1`. -/
theorem exercise_5_19_sum_le_one_chvatal_rank_upper_bound
    {k : ℕ}
    (hk : is_iterate_rank_of_inequality pure_integer_chvatal_closure
      (exercise_5_19_polyhedron n) (1 : Fin n → ℝ) 1 k) :
    k ≤ Nat.log 2 n + 1 := by
  by_cases hn : 3 ≤ n
  · -- On the source branch, the logarithmic iterate is already valid.
    by_contra hbound
    have hkgt : Nat.log 2 n + 1 < k := by
      exact lt_of_not_ge hbound
    have hnot :
        ¬ is_valid_inequality
          ((pure_integer_chvatal_closure^[Nat.log 2 n + 1]) (exercise_5_19_polyhedron n))
          (1 : Fin n → ℝ) 1 :=
      hk.not_valid_on_iterate hkgt
    exact hnot (exercise_5_19_sum_le_one_valid_on_logIterate hn)
  · have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by
      omega
    rcases hn_cases with rfl | rfl | rfl
    · -- In dimension `0`, the inequality is already valid on `P`, so the rank is `0`.
      have hvalidP : is_valid_inequality (exercise_5_19_polyhedron 0) (1 : Fin 0 → ℝ) 1 := by
        rw [exercise_5_19_sum_le_one_valid_iff]
        intro x hx
        simp
      have hk_zero : k = 0 := by
        cases k with
        | zero =>
            rfl
        | succ j =>
            exfalso
            exact (hk.not_valid_on_iterate (j := 0) (Nat.succ_pos _)) (by simpa using hvalidP)
      omega
    · -- In dimension `1`, the inequality is not valid on the pure-integer hull at all.
      exfalso
      let x : Fin 1 → ℝ := fun _ ↦ (2 : ℝ)
      have hx_mem_poly : x ∈ exercise_5_19_polyhedron 1 := by
        rw [mem_exercise_5_19_polyhedron_iff]
        refine ⟨?_, ?_⟩
        · intro i
          fin_cases i
          norm_num [x]
        · intro i j hij
          fin_cases i
          fin_cases j
          cases hij
      have hx_mem_int : x ∈ integerVectors 1 := by
        rw [mem_integerVectors_iff_forall]
        intro i
        fin_cases i
        exact ⟨2, by norm_num [x]⟩
      have hx_hull : x ∈ pure_integer_hull (exercise_5_19_polyhedron 1) := by
        rw [pure_integer_hull_eq_convexHull]
        exact subset_convexHull ℝ _ ⟨hx_mem_poly, hx_mem_int⟩
      have hvalidHull :
          ∀ ⦃y : Fin 1 → ℝ⦄,
            y ∈ pure_integer_hull (exercise_5_19_polyhedron 1) →
              ∑ i : Fin 1, y i ≤ 1 :=
        (exercise_5_19_sum_le_one_valid_iff
          (Q := pure_integer_hull (exercise_5_19_polyhedron 1))).1 hk.valid_on_integer_hull
      have hsum_gt : 1 < ∑ i : Fin 1, x i := by
        simp [x]
      have hsum_le : ∑ i : Fin 1, x i ≤ 1 := hvalidHull hx_hull
      linarith
    · -- In dimension `2`, the source pairwise inequality is already the target inequality.
      have hvalidP : is_valid_inequality (exercise_5_19_polyhedron 2) (1 : Fin 2 → ℝ) 1 := by
        rw [exercise_5_19_sum_le_one_valid_iff]
        intro x hx
        have hpair :=
          (mem_exercise_5_19_polyhedron_iff.mp hx).2 (show (0 : Fin 2) < 1 by decide)
        simpa [Fin.sum_univ_two] using hpair
      have hk_zero : k = 0 := by
        cases k with
        | zero =>
            rfl
        | succ j =>
            exfalso
            exact (hk.not_valid_on_iterate (j := 0) (Nat.succ_pos _)) (by simpa using hvalidP)
      omega

end Exercise519
