/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3

section Exercise71

variable {n : ℕ}

/-- The coefficient vector of the coordinate lower bound `x_j ≥ 0`, written as `-x_j ≤ 0`. -/
def zero_one_knapsack_coordinate_lower_bound_coeff
    (j : Fin n) : Fin n → ℝ :=
  -Pi.single j 1

/-- The lower-bound coefficient vector has value `-1` at the distinguished coordinate. -/
@[simp] theorem zero_one_knapsack_coordinate_lower_bound_coeff_apply_self
    (j : Fin n) :
    zero_one_knapsack_coordinate_lower_bound_coeff j j = -1 := by
  simp [zero_one_knapsack_coordinate_lower_bound_coeff]

/-- The lower-bound coefficient vector vanishes away from the distinguished coordinate. -/
@[simp] theorem zero_one_knapsack_coordinate_lower_bound_coeff_apply_of_ne
    {j k : Fin n} (hk : k ≠ j) :
    zero_one_knapsack_coordinate_lower_bound_coeff j k = 0 := by
  simp [zero_one_knapsack_coordinate_lower_bound_coeff, hk]

/-- The lower-bound coefficient vector evaluates on `x` as `-x j`. -/
@[simp] theorem zero_one_knapsack_coordinate_lower_bound_coeff_dotProduct
    (j : Fin n) (x : Fin n → ℝ) :
    zero_one_knapsack_coordinate_lower_bound_coeff j ⬝ᵥ x = -x j := by
  simp [zero_one_knapsack_coordinate_lower_bound_coeff]

/-- The equality face cut out by `x_j ≥ 0` is the coordinate face `x_j = 0`. -/
def zero_one_knapsack_coordinate_zero_face
    (a : Fin n → ℕ) (b : ℕ) (j : Fin n) : Set (Fin n → ℝ) :=
  face_set
    (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
    (zero_one_knapsack_coordinate_lower_bound_coeff j)
    0

/-- Membership in `zero_one_knapsack_coordinate_zero_face a b j` means belonging to the knapsack
polytope and having `j`th coordinate equal to `0`. -/
theorem mem_zero_one_knapsack_coordinate_zero_face_iff
    {a : Fin n → ℕ} {b : ℕ} {j : Fin n} {x : Fin n → ℝ} :
    x ∈ zero_one_knapsack_coordinate_zero_face a b j ↔
      x ∈ zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ) ∧ x j = 0 := by
  rw [zero_one_knapsack_coordinate_zero_face, mem_face_set_iff,
    zero_one_knapsack_coordinate_lower_bound_coeff_dotProduct]
  constructor
  · rintro ⟨hxP, hxeq⟩
    refine ⟨hxP, ?_⟩
    have hxj' := congrArg Neg.neg hxeq
    simpa using hxj'
  · rintro ⟨hxP, hxj⟩
    refine ⟨hxP, ?_⟩
    simp [hxj]

/-- The coefficient vector of the coordinate upper bound `x_j ≤ 1`. -/
def zero_one_knapsack_coordinate_upper_bound_coeff
    (j : Fin n) : Fin n → ℝ :=
  Pi.single j 1

/-- The upper-bound coefficient vector has value `1` at the distinguished coordinate. -/
@[simp] theorem zero_one_knapsack_coordinate_upper_bound_coeff_apply_self
    (j : Fin n) :
    zero_one_knapsack_coordinate_upper_bound_coeff j j = 1 := by
  simp [zero_one_knapsack_coordinate_upper_bound_coeff]

/-- The upper-bound coefficient vector vanishes away from the distinguished coordinate. -/
@[simp] theorem zero_one_knapsack_coordinate_upper_bound_coeff_apply_of_ne
    {j k : Fin n} (hk : k ≠ j) :
    zero_one_knapsack_coordinate_upper_bound_coeff j k = 0 := by
  simp [zero_one_knapsack_coordinate_upper_bound_coeff, hk]

/-- The upper-bound coefficient vector evaluates on `x` as `x j`. -/
@[simp] theorem zero_one_knapsack_coordinate_upper_bound_coeff_dotProduct
    (j : Fin n) (x : Fin n → ℝ) :
    zero_one_knapsack_coordinate_upper_bound_coeff j ⬝ᵥ x = x j := by
  simp [zero_one_knapsack_coordinate_upper_bound_coeff]

/-- The equality face cut out by `x_j ≤ 1` is the coordinate face `x_j = 1`. -/
def zero_one_knapsack_coordinate_one_face
    (a : Fin n → ℕ) (b : ℕ) (j : Fin n) : Set (Fin n → ℝ) :=
  face_set
    (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
    (zero_one_knapsack_coordinate_upper_bound_coeff j)
    1

/-- Membership in `zero_one_knapsack_coordinate_one_face a b j` means belonging to the knapsack
polytope and having `j`th coordinate equal to `1`. -/
theorem mem_zero_one_knapsack_coordinate_one_face_iff
    {a : Fin n → ℕ} {b : ℕ} {j : Fin n} {x : Fin n → ℝ} :
    x ∈ zero_one_knapsack_coordinate_one_face a b j ↔
      x ∈ zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ) ∧ x j = 1 := by
  rw [zero_one_knapsack_coordinate_one_face, mem_face_set_iff,
    zero_one_knapsack_coordinate_upper_bound_coeff_dotProduct]

/-- Helper for Exercise 7.1: every `0/1` knapsack vector lies in the ambient unit box. -/
lemma zero_one_knapsack_set_subset_unit_box
    (a : Fin n → ℕ) (b : ℕ) :
    zero_one_knapsack_set (fun i ↦ (a i : ℝ)) (b : ℝ) ⊆
      Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) := by
  intro x hx
  rw [mem_zero_one_knapsack_set_iff] at hx
  rw [Set.mem_univ_pi]
  intro i
  -- Each generator is binary, so each coordinate lies in `[0,1]`.
  rcases hx.1 i with hxi | hxi
  · rw [hxi]
    simp
  · rw [hxi]
    simp

/-- Helper for Exercise 7.1: the knapsack polytope stays inside the ambient unit box. -/
lemma zero_one_knapsack_polytope_subset_unit_box
    (a : Fin n → ℕ) (b : ℕ) :
    zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ) ⊆
      Set.univ.pi (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) := by
  rw [zero_one_knapsack_polytope_eq_convexHull]
  -- The convex hull remains inside any convex box containing all generators.
  refine convexHull_min (zero_one_knapsack_set_subset_unit_box a b) ?_
  exact convex_pi fun _ _ ↦ convex_Icc (0 : ℝ) 1

/-- Helper for Exercise 7.1: every point of the `0,1` knapsack polytope satisfies
`0 ≤ x i ≤ 1` coordinatewise. -/
lemma zero_one_knapsack_polytope_coord_bounds
    {a : Fin n → ℕ} {b : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
    (i : Fin n) :
    0 ≤ x i ∧ x i ≤ 1 := by
  have hxBox := zero_one_knapsack_polytope_subset_unit_box a b hx
  rw [Set.mem_univ_pi] at hxBox
  exact hxBox i

/-- Helper for Exercise 7.1: the singleton vector in coordinate `j` is feasible because
`a j ≤ b`. -/
lemma zero_one_knapsack_singleton_not_overweight
    (a : Fin n → ℕ) (b : ℕ) (ha_le_b : ∀ j, a j ≤ b)
    (j : Fin n) :
    j ∉ zero_one_knapsack_overweight_indices (fun i ↦ (a i : ℝ)) (b : ℝ) := by
  have hj_le : (a j : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast ha_le_b j
  -- The singleton is allowed exactly when its weight does not exceed the capacity.
  simpa [zero_one_knapsack_overweight_indices] using
    (show ¬ ((b : ℝ) < (a j : ℝ)) from not_lt.mpr hj_le)

/-- Helper for Exercise 7.1: if items `i` and `j` fit together, then the vector with ones in
exactly those two coordinates belongs to the knapsack polytope. -/
lemma zero_one_knapsack_two_singletons_mem_polytope
    (a : Fin n → ℕ) (b : ℕ) {i j : Fin n} (hij : i ≠ j)
    (hpair : a i + a j ≤ b) :
    Pi.single i (1 : ℝ) + Pi.single j 1 ∈
      zero_one_knapsack_polytope (fun k ↦ (a k : ℝ)) (b : ℝ) := by
  rw [zero_one_knapsack_polytope_eq_convexHull]
  -- The two-singleton vector is itself a feasible binary point.
  apply subset_convexHull ℝ (zero_one_knapsack_set (fun k ↦ (a k : ℝ)) (b : ℝ))
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · intro k
    by_cases hki : k = i
    · right
      subst hki
      simp [hij]
    · by_cases hkj : k = j
      · right
        subst hkj
        simp [hij]
      · left
        simp [hki, hkj]
  · have hpair_real : (a i : ℝ) + (a j : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast hpair
    -- The weight sum splits across the two singleton supports.
    have hweight :
        (fun k ↦ (a k : ℝ)) ⬝ᵥ (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) ≤ (b : ℝ) := by
      rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one]
      exact hpair_real
    simpa [dotProduct] using hweight

/-- Helper for Exercise 7.1: a coefficient vector supported only at `j` evaluates by the single
coordinate formula `d ⬝ᵥ x = d j * x j`. -/
lemma supportedSingleCoordinateDotProduct
    (j : Fin n) (d x : Fin n → ℝ)
    (hsupport : ∀ k : Fin n, k ≠ j → d k = 0) :
    d ⬝ᵥ x = d j * x j := by
  -- Replace `d` by the singleton vector with the same `j`th coefficient.
  have hd_eq : d = Pi.single j (d j) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk, hsupport k hk]
  rw [hd_eq]
  rw [single_dotProduct (v := x) (x := d j) (i := j)]
  simp

/-- Helper for Exercise 7.1: if the pair `{i,j}` is infeasible, then every point of the knapsack
polytope satisfies `x i + x j ≤ 1`. -/
lemma pairInfeasibleCoordinateSumValid
    (a : Fin n → ℕ) (b : ℕ) {i j : Fin n} (hij : i ≠ j)
    (hpair : ¬ a i + a j ≤ b)
    {x : Fin n → ℝ}
    (hx : x ∈ zero_one_knapsack_polytope (fun k ↦ (a k : ℝ)) (b : ℝ)) :
    x i + x j ≤ 1 := by
  rw [zero_one_knapsack_polytope_eq_convexHull] at hx
  have hgenerators :
      zero_one_knapsack_set (fun k ↦ (a k : ℝ)) (b : ℝ) ⊆
        {y : Fin n → ℝ | y i + y j ≤ 1} := by
    intro y hy
    change y i + y j ≤ 1
    rw [mem_zero_one_knapsack_set_iff] at hy
    rcases hy with ⟨hbin, hweight⟩
    -- A binary generator cannot place ones in both infeasible coordinates.
    rcases hbin i with hyi | hyi
    · rcases hbin j with hyj | hyj
      · simp [hyi, hyj]
      · simp [hyi, hyj]
    · rcases hbin j with hyj | hyj
      · simp [hyj, hyi]
      · have hterm_nonneg : ∀ k : Fin n, 0 ≤ (a k : ℝ) * y k := by
          intro k
          rcases hbin k with hyk | hyk
          · simp [hyk]
          · simp [hyk]
        let s : Finset (Fin n) := {i, j}
        have hpair_le_weight :
            (a i : ℝ) + (a j : ℝ) ≤
              Finset.sum Finset.univ (fun k ↦ (a k : ℝ) * y k) := by
          have hsubset_sum :
              Finset.sum s (fun k ↦ (a k : ℝ) * y k) ≤
                Finset.sum Finset.univ (fun k ↦ (a k : ℝ) * y k) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro k hk
              simp [s] at hk ⊢
            · intro k _hk_univ hk_not_pair
              exact hterm_nonneg k
          have hsubset_sum' :
              (a i : ℝ) * y i + (a j : ℝ) * y j ≤
                Finset.sum Finset.univ (fun k ↦ (a k : ℝ) * y k) := by
            simpa [s, Finset.sum_pair hij] using hsubset_sum
          simpa [hyi, hyj] using hsubset_sum'
        have hpair_real : (a i : ℝ) + (a j : ℝ) ≤ (b : ℝ) := by
          exact le_trans hpair_le_weight hweight
        have hpair_nat : a i + a j ≤ b := by
          exact_mod_cast hpair_real
        exact False.elim (hpair hpair_nat)
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun y ↦ y i + y j
      map_add' := by
        intro y z
        simp [Pi.add_apply, add_left_comm, add_comm]
      map_smul' := by
        intro c y
        simp [mul_add] }
  have hconvex :
      Convex ℝ {y : Fin n → ℝ | y i + y j ≤ 1} := by
    -- The target inequality defines the preimage of a convex ray under a linear map.
    simpa [f] using (convex_Iic (1 : ℝ)).linear_preimage f
  have hxHalfspace : x ∈ {y : Fin n → ℝ | y i + y j ≤ 1} :=
    convexHull_min hgenerators hconvex hx
  simpa using hxHalfspace

/-- Helper for Exercise 7.1: the coordinate-zero face is already inclusionwise maximal among
proper faces of the knapsack polytope. -/
lemma zero_one_knapsack_coordinate_zero_face_eq_of_subset_proper_face
    (a : Fin n → ℕ) (b : ℕ) (ha_le_b : ∀ j, a j ≤ b)
    (j : Fin n) {G : Set (Fin n → ℝ)}
    (hG : is_proper_face (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ)) G)
    (hsubset : zero_one_knapsack_coordinate_zero_face a b j ⊆ G) :
    G = zero_one_knapsack_coordinate_zero_face a b j := by
  let P := zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ)
  rcases (is_proper_face_iff.mp hG) with ⟨hG_exposed, hG_nonempty, hG_ssubset⟩
  rcases hG_exposed.exists_eq_face_set_of_nonempty hG_nonempty with
    ⟨d, β, _hvalidG, hG_eq⟩
  have hzeroP : (0 : Fin n → ℝ) ∈ P := by
    simpa [P] using zero_mem_zero_one_knapsack_polytope
      (fun i ↦ (a i : ℝ)) (show (0 : ℝ) ≤ b by exact_mod_cast Nat.zero_le b)
  have hzeroFace : (0 : Fin n → ℝ) ∈ zero_one_knapsack_coordinate_zero_face a b j := by
    exact (mem_zero_one_knapsack_coordinate_zero_face_iff).2 ⟨hzeroP, by simp⟩
  have hzeroG : (0 : Fin n → ℝ) ∈ face_set P d β := by
    simpa [hG_eq] using hsubset hzeroFace
  have hβ_zero : β = 0 := by
    -- The origin lies in the containing face, so the right-hand side is zero.
    have hzeroEq : d ⬝ᵥ (0 : Fin n → ℝ) = β := (mem_face_set_iff.mp hzeroG).2
    simpa using hzeroEq.symm
  have hsupport : ∀ i : Fin n, i ≠ j → d i = 0 := by
    intro i hij
    have hsingleP : Pi.single i (1 : ℝ) ∈ P := by
      exact single_one_mem_zero_one_knapsack_polytope
        (fun k ↦ (a k : ℝ)) i
        (zero_one_knapsack_singleton_not_overweight a b ha_le_b i)
    have hsingleFace : Pi.single i (1 : ℝ) ∈ zero_one_knapsack_coordinate_zero_face a b j := by
      exact (mem_zero_one_knapsack_coordinate_zero_face_iff).2 ⟨hsingleP, by simp [hij]⟩
    have hsingleG : Pi.single i (1 : ℝ) ∈ face_set P d β := by
      simpa [hG_eq] using hsubset hsingleFace
    have hdi_eq_beta : d i = β := by
      have hEq : d ⬝ᵥ Pi.single i (1 : ℝ) = β := (mem_face_set_iff.mp hsingleG).2
      simpa using hEq
    rw [hβ_zero] at hdi_eq_beta
    exact hdi_eq_beta
  have hdj_ne : d j ≠ 0 := by
    intro hdj_zero
    have hd_zero : d = 0 := by
      funext i
      by_cases hij : i = j
      · subst hij
        exact hdj_zero
      · exact hsupport i hij
    have hface_eq_P : face_set P d β = P := by
      ext x
      rw [mem_face_set_iff]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        refine ⟨hx, ?_⟩
        simp [hd_zero, hβ_zero]
    exact hG_ssubset.ne (hG_eq.trans hface_eq_P)
  apply Set.Subset.antisymm
  · intro x hxG
    have hxG' : x ∈ face_set P d β := by
      simpa [hG_eq] using hxG
    have hxj_zero : x j = 0 := by
      -- After normalizing the exposing functional, the face equation forces `x j = 0`.
      have hxEq : d j * x j = 0 := by
        calc
          d j * x j = d ⬝ᵥ x := by
            symm
            exact supportedSingleCoordinateDotProduct j d x hsupport
          _ = β := (mem_face_set_iff.mp hxG').2
          _ = 0 := hβ_zero
      have hxEq' : d j * x j = d j * 0 := by
        simpa using hxEq
      exact (mul_left_cancel₀ hdj_ne hxEq')
    exact (mem_zero_one_knapsack_coordinate_zero_face_iff).2
      ⟨(mem_face_set_iff.mp hxG').1, hxj_zero⟩
  · intro x hxFace
    rcases (mem_zero_one_knapsack_coordinate_zero_face_iff.mp hxFace) with ⟨hxP, hxj_zero⟩
    -- Conversely, `x j = 0` makes the exposed-face equation automatic.
    have hxG' : x ∈ face_set P d β := by
      refine (mem_face_set_iff).2 ⟨hxP, ?_⟩
      calc
        d ⬝ᵥ x = d j * x j := supportedSingleCoordinateDotProduct j d x hsupport
        _ = d j * 0 := by rw [hxj_zero]
        _ = 0 := by simp
        _ = β := hβ_zero.symm
    simpa [hG_eq] using hxG'

/-- Helper for Exercise 7.1: under pairwise feasibility with item `j`, the coordinate-one face is
already inclusionwise maximal among proper faces of the knapsack polytope. -/
lemma zero_one_knapsack_coordinate_one_face_eq_of_subset_proper_face
    (a : Fin n → ℕ) (b : ℕ) (ha_le_b : ∀ j, a j ≤ b)
    (j : Fin n) (hpairwise : ∀ i : Fin n, i ≠ j → a i + a j ≤ b)
    {G : Set (Fin n → ℝ)}
    (hG : is_proper_face (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ)) G)
    (hsubset : zero_one_knapsack_coordinate_one_face a b j ⊆ G) :
    G = zero_one_knapsack_coordinate_one_face a b j := by
  let P := zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ)
  rcases (is_proper_face_iff.mp hG) with ⟨hG_exposed, hG_nonempty, hG_ssubset⟩
  rcases hG_exposed.exists_eq_face_set_of_nonempty hG_nonempty with
    ⟨d, β, _hvalidG, hG_eq⟩
  have hsinglejP : Pi.single j (1 : ℝ) ∈ P := by
    exact single_one_mem_zero_one_knapsack_polytope
      (fun i ↦ (a i : ℝ)) j
      (zero_one_knapsack_singleton_not_overweight a b ha_le_b j)
  have hsinglejFace : Pi.single j (1 : ℝ) ∈ zero_one_knapsack_coordinate_one_face a b j := by
    exact (mem_zero_one_knapsack_coordinate_one_face_iff).2 ⟨hsinglejP, by simp⟩
  have hsinglejG : Pi.single j (1 : ℝ) ∈ face_set P d β := by
    simpa [hG_eq] using hsubset hsinglejFace
  have hβ_eq : β = d j := by
    -- The singleton on coordinate `j` fixes the exposed-face right-hand side.
    have hEq : d ⬝ᵥ Pi.single j (1 : ℝ) = β := (mem_face_set_iff.mp hsinglejG).2
    symm
    simpa using hEq
  have hsupport : ∀ i : Fin n, i ≠ j → d i = 0 := by
    intro i hij
    have hpairP :
        Pi.single i (1 : ℝ) + Pi.single j 1 ∈ P := by
      exact zero_one_knapsack_two_singletons_mem_polytope a b hij (hpairwise i hij)
    have hpairFace :
        Pi.single i (1 : ℝ) + Pi.single j 1 ∈ zero_one_knapsack_coordinate_one_face a b j := by
      exact (mem_zero_one_knapsack_coordinate_one_face_iff).2 ⟨hpairP, by simp [hij]⟩
    have hpairG :
        Pi.single i (1 : ℝ) + Pi.single j 1 ∈ face_set P d β := by
      simpa [hG_eq] using hsubset hpairFace
    have hpairEq : d i + d j = β := by
      have hEq :
          d ⬝ᵥ (Pi.single i (1 : ℝ) + Pi.single j 1) = β :=
        (mem_face_set_iff.mp hpairG).2
      simpa [dotProduct_add] using hEq
    linarith [hpairEq, hβ_eq]
  have hdj_ne : d j ≠ 0 := by
    intro hdj_zero
    have hd_zero : d = 0 := by
      funext i
      by_cases hij : i = j
      · subst hij
        exact hdj_zero
      · exact hsupport i hij
    have hface_eq_P : face_set P d β = P := by
      ext x
      rw [mem_face_set_iff]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        refine ⟨hx, ?_⟩
        simp [hd_zero, hβ_eq]
    exact hG_ssubset.ne (hG_eq.trans hface_eq_P)
  apply Set.Subset.antisymm
  · intro x hxG
    have hxG' : x ∈ face_set P d β := by
      simpa [hG_eq] using hxG
    have hxj_one : x j = 1 := by
      -- After support normalization, the exposed-face equation becomes `d j * x j = d j`.
      have hxEq : d j * x j = d j := by
        calc
          d j * x j = d ⬝ᵥ x := by
            symm
            exact supportedSingleCoordinateDotProduct j d x hsupport
          _ = β := (mem_face_set_iff.mp hxG').2
          _ = d j := hβ_eq
      have hxEq' : d j * x j = d j * 1 := by
        simpa using hxEq
      exact (mul_left_cancel₀ hdj_ne hxEq')
    exact (mem_zero_one_knapsack_coordinate_one_face_iff).2
      ⟨(mem_face_set_iff.mp hxG').1, hxj_one⟩
  · intro x hxFace
    rcases (mem_zero_one_knapsack_coordinate_one_face_iff.mp hxFace) with ⟨hxP, hxj_one⟩
    -- Conversely, points with `x j = 1` satisfy the exposed-face equation.
    have hxG' : x ∈ face_set P d β := by
      refine (mem_face_set_iff).2 ⟨hxP, ?_⟩
      calc
        d ⬝ᵥ x = d j * x j := supportedSingleCoordinateDotProduct j d x hsupport
        _ = d j * 1 := by rw [hxj_one]
        _ = d j := by simp
        _ = β := hβ_eq.symm
    simpa [hG_eq] using hxG'

/-- Helper for Exercise 7.1: if some pair `{i,j}` is infeasible, then every point on the
coordinate-one face for `j` also lies on the coordinate-zero face for `i`. -/
lemma zero_one_knapsack_coordinate_one_face_subset_coordinate_zero_face_of_pair_infeasible
    (a : Fin n → ℕ) (b : ℕ) {i j : Fin n} (hij : i ≠ j)
    (hpair : ¬ a i + a j ≤ b) :
    zero_one_knapsack_coordinate_one_face a b j ⊆
      zero_one_knapsack_coordinate_zero_face a b i := by
  intro x hxFace
  rcases (mem_zero_one_knapsack_coordinate_one_face_iff.mp hxFace) with ⟨hxP, hxj_one⟩
  have hsum_le : x i + x j ≤ 1 :=
    pairInfeasibleCoordinateSumValid a b hij hpair hxP
  have hxi_nonneg : 0 ≤ x i := (zero_one_knapsack_polytope_coord_bounds hxP i).1
  have hxi_zero : x i = 0 := by
    -- The valid inequality and the face equation force the remaining coordinate to vanish.
    linarith [hsum_le, hxj_one, hxi_nonneg]
  exact (mem_zero_one_knapsack_coordinate_zero_face_iff).2 ⟨hxP, hxi_zero⟩

/-- Exercise 7.1 (i). For the `0,1` knapsack set
`K = {x ∈ {0,1}^n | ∑ j, a j * x j ≤ b}` with `a j ≤ b` for every `j`, the coordinate
inequality `x_j ≥ 0` defines a facet of `conv(K)`. -/
theorem exercise_7_1_coordinate_lower_bound_is_facet
    (a : Fin n → ℕ) (b : ℕ)
    (ha_le_b : ∀ j, a j ≤ b)
    (j : Fin n) :
    facet_defining_inequality
      (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
      (zero_one_knapsack_coordinate_lower_bound_coeff j)
      0 := by
  let P := zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ)
  have hvalid :
      is_valid_inequality P (zero_one_knapsack_coordinate_lower_bound_coeff j) 0 := by
    intro x hxP
    -- Coordinate lower bounds come from the unit-box containment of the knapsack polytope.
    have hxj_nonneg := (zero_one_knapsack_polytope_coord_bounds hxP j).1
    simpa using neg_nonpos.mpr hxj_nonneg
  have hproper : is_proper_face P (zero_one_knapsack_coordinate_zero_face a b j) := by
    rw [is_proper_face_iff]
    refine ⟨?_, ?_, ?_⟩
    · -- The equality set of a valid inequality is an exposed face.
      simpa [P, zero_one_knapsack_coordinate_zero_face] using
        isExposed_face_set_of_valid_inequality hvalid
    · have hzeroP : (0 : Fin n → ℝ) ∈ P := by
        simpa [P] using zero_mem_zero_one_knapsack_polytope
          (fun i ↦ (a i : ℝ)) (show (0 : ℝ) ≤ b by exact_mod_cast Nat.zero_le b)
      -- The origin lies on the lower-bound face.
      exact ⟨0, (mem_zero_one_knapsack_coordinate_zero_face_iff).2 ⟨hzeroP, by simp⟩⟩
    · refine ⟨?_, ?_⟩
      · intro x hx
        exact (mem_zero_one_knapsack_coordinate_zero_face_iff.mp hx).1
      · intro hsubsetP
        have hsinglejP : Pi.single j (1 : ℝ) ∈ P := by
          exact single_one_mem_zero_one_knapsack_polytope
            (fun i ↦ (a i : ℝ)) j
            (zero_one_knapsack_singleton_not_overweight a b ha_le_b j)
        have hsinglejFace :
            Pi.single j (1 : ℝ) ∈ zero_one_knapsack_coordinate_zero_face a b j :=
          hsubsetP hsinglejP
        have hsinglejEq := (mem_zero_one_knapsack_coordinate_zero_face_iff.mp hsinglejFace).2
        simp at hsinglejEq
  rw [facet_defining_inequality_iff, is_facet_iff]
  refine ⟨hvalid, hproper, ?_⟩
  intro G hG hsubset
  -- Route correction: maximality is proved by recovering the exposing functional of any
  -- containing proper face and showing it must be a scalar multiple of `-e_j`.
  exact zero_one_knapsack_coordinate_zero_face_eq_of_subset_proper_face a b ha_le_b j hG hsubset

/-- Exercise 7.1 (ii). For the same `0,1` knapsack polytope, the coordinate
inequality `x_j ≤ 1` defines a facet of `conv(K)` exactly when every pair
consisting of item `j` and one other item is jointly feasible, i.e. when
`a i + a j ≤ b` for all `i ≠ j`. -/
theorem exercise_7_1_coordinate_upper_bound_is_facet_iff
    (a : Fin n → ℕ) (b : ℕ)
    (ha_le_b : ∀ j, a j ≤ b)
    (j : Fin n) :
    facet_defining_inequality
      (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
      (zero_one_knapsack_coordinate_upper_bound_coeff j)
      1 ↔
      ∀ i : Fin n, i ≠ j → a i + a j ≤ b := by
  let P := zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ)
  constructor
  · intro hfacet i hij
    by_contra hpair
    have hfacetFace : is_facet P (zero_one_knapsack_coordinate_one_face a b j) := by
      simpa [P, zero_one_knapsack_coordinate_one_face] using
        facet_defining_inequality_is_facet hfacet
    have hzeroProper : is_proper_face P (zero_one_knapsack_coordinate_zero_face a b i) := by
      -- Part (i) already shows every coordinate-zero face is a proper face.
      exact is_facet_to_is_proper_face <| by
        simpa [P, zero_one_knapsack_coordinate_zero_face] using
          facet_defining_inequality_is_facet
            (exercise_7_1_coordinate_lower_bound_is_facet a b ha_le_b i)
    have hsubset :
        zero_one_knapsack_coordinate_one_face a b j ⊆
          zero_one_knapsack_coordinate_zero_face a b i := by
      exact zero_one_knapsack_coordinate_one_face_subset_coordinate_zero_face_of_pair_infeasible
        a b hij hpair
    have hEq :
        zero_one_knapsack_coordinate_zero_face a b i =
          zero_one_knapsack_coordinate_one_face a b j :=
      is_facet_maximal hfacetFace hzeroProper hsubset
    have hzeroP : (0 : Fin n → ℝ) ∈ P := by
      simpa [P] using zero_mem_zero_one_knapsack_polytope
        (fun k ↦ (a k : ℝ)) (show (0 : ℝ) ≤ b by exact_mod_cast Nat.zero_le b)
    have hzeroInZeroFace :
        (0 : Fin n → ℝ) ∈ zero_one_knapsack_coordinate_zero_face a b i := by
      exact (mem_zero_one_knapsack_coordinate_zero_face_iff).2 ⟨hzeroP, by simp⟩
    have hzeroInOneFace :
        (0 : Fin n → ℝ) ∈ zero_one_knapsack_coordinate_one_face a b j := by
      exact hEq ▸ hzeroInZeroFace
    have hzeroNotOneFace :
        (0 : Fin n → ℝ) ∉ zero_one_knapsack_coordinate_one_face a b j := by
      intro hx
      have hEqOne := (mem_zero_one_knapsack_coordinate_one_face_iff.mp hx).2
      simp at hEqOne
    exact hzeroNotOneFace hzeroInOneFace
  · intro hpairwise
    have hvalid :
        is_valid_inequality P (zero_one_knapsack_coordinate_upper_bound_coeff j) 1 := by
      intro x hxP
      -- Coordinate upper bounds also come from the unit-box containment.
      simpa using (zero_one_knapsack_polytope_coord_bounds hxP j).2
    have hproper : is_proper_face P (zero_one_knapsack_coordinate_one_face a b j) := by
      rw [is_proper_face_iff]
      refine ⟨?_, ?_, ?_⟩
      · -- The equality set of the valid upper-bound inequality is exposed.
        simpa [P, zero_one_knapsack_coordinate_one_face] using
          isExposed_face_set_of_valid_inequality hvalid
      · have hsinglejP :
            Pi.single j (1 : ℝ) ∈ P := by
          exact single_one_mem_zero_one_knapsack_polytope
            (fun i ↦ (a i : ℝ)) j
            (zero_one_knapsack_singleton_not_overweight a b ha_le_b j)
        -- The `j`th singleton lies on the upper-bound face.
        exact ⟨Pi.single j 1,
          (mem_zero_one_knapsack_coordinate_one_face_iff).2 ⟨hsinglejP, by simp⟩⟩
      · refine ⟨?_, ?_⟩
        · intro x hx
          exact (mem_zero_one_knapsack_coordinate_one_face_iff.mp hx).1
        · intro hsubsetP
          have hzeroP : (0 : Fin n → ℝ) ∈ P := by
            simpa [P] using zero_mem_zero_one_knapsack_polytope
              (fun i ↦ (a i : ℝ)) (show (0 : ℝ) ≤ b by exact_mod_cast Nat.zero_le b)
          have hzeroFace : (0 : Fin n → ℝ) ∈ zero_one_knapsack_coordinate_one_face a b j :=
            hsubsetP hzeroP
          have hzeroEq := (mem_zero_one_knapsack_coordinate_one_face_iff.mp hzeroFace).2
          simp at hzeroEq
    rw [facet_defining_inequality_iff, is_facet_iff]
    refine ⟨hvalid, hproper, ?_⟩
    intro G hG hsubset
    -- Route correction: once pairwise-feasible two-singleton witnesses are in the face, any
    -- containing proper face must be exposed by a scalar multiple of `e_j`.
    exact zero_one_knapsack_coordinate_one_face_eq_of_subset_proper_face
      a b ha_le_b j hpairwise hG hsubset

/-- Summary for Exercise 7.1. For the `0,1` knapsack polytope, the coordinate lower bound
`x_j ≥ 0` is facet-defining, and the coordinate upper bound `x_j ≤ 1` is facet-defining exactly
when every pair `{i, j}` is jointly feasible. -/
theorem exercise_7_1
    (a : Fin n → ℕ) (b : ℕ)
    (ha_le_b : ∀ j, a j ≤ b)
    (j : Fin n) :
    facet_defining_inequality
        (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
        (zero_one_knapsack_coordinate_lower_bound_coeff j)
        0 ∧
      (facet_defining_inequality
          (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
          (zero_one_knapsack_coordinate_upper_bound_coeff j)
          1 ↔
        ∀ i : Fin n, i ≠ j → a i + a j ≤ b) := by
  constructor
  · exact exercise_7_1_coordinate_lower_bound_is_facet a b ha_le_b j
  · exact exercise_7_1_coordinate_upper_bound_is_facet_iff a b ha_le_b j

/-- The lower-bound facet fact from Exercise 7.1 is available as an instance. -/
instance instExercise71CoordinateLowerBoundFacetDefiningInequality
    (a : Fin n → ℕ) (b : ℕ)
    (ha_le_b : ∀ j, a j ≤ b)
    (j : Fin n) :
    facet_defining_inequality
      (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
      (zero_one_knapsack_coordinate_lower_bound_coeff j)
      0 :=
  exercise_7_1_coordinate_lower_bound_is_facet a b ha_le_b j

/-- Under the pairwise-feasibility hypothesis, the upper-bound facet fact from Exercise 7.1 is
available as an instance. -/
instance instExercise71CoordinateUpperBoundFacetDefiningInequality
    (a : Fin n → ℕ) (b : ℕ)
    (ha_le_b : ∀ j, a j ≤ b)
    (j : Fin n)
    (hpairwise : ∀ i : Fin n, i ≠ j → a i + a j ≤ b) :
    facet_defining_inequality
      (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
      (zero_one_knapsack_coordinate_upper_bound_coeff j)
      1 :=
  (exercise_7_1_coordinate_upper_bound_is_facet_iff a b ha_le_b j).2 hpairwise

end Exercise71
