import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_8

open scoped BigOperators Matrix

/- Domain sampling for this exercise:
- primary domain: binary knapsack covers, lifted/extended cover inequalities, and facet statements
- core/canonical owners already present upstream:
  `IsKnapsackCover`, `IsMinimalKnapsackCover`, `zero_one_knapsack_set`,
  `zero_one_knapsack_polytope`, `cover_indicator`, `cover_inequality_rhs`, and
  `IsKnapsackChvatalPresentation` from Exercises 7.1 and 7.8, together with `IsFacetOf` from
  Section 3.18
- source-facing layer kept here: the extended-cover construction `E(C)`, its equality face, and
  the extended-cover inequality statements built on that shared Chvatal owner

This file refines to those upstream owners instead of restating local duplicates. -/

section Exercise79

variable {n : ℕ}

/-- The extension `E(C)` of a minimal cover `C` is obtained by adjoining every index outside `C`
whose weight is at least every weight already occurring in `C`. -/
def extended_cover
    (a : Fin n → ℕ)
    (C : Finset (Fin n)) : Finset (Fin n) :=
  C ∪ Finset.univ.filter fun k ↦ k ∉ C ∧ ∀ j ∈ C, a j ≤ a k

/-- Membership in `extended_cover a C` means either lying in `C` or lying outside `C` with weight
at least every cover weight. -/
theorem mem_extended_cover_iff
    (a : Fin n → ℕ)
    (C : Finset (Fin n))
    (k : Fin n) :
    k ∈ extended_cover a C ↔
      k ∈ C ∨ (k ∉ C ∧ ∀ j ∈ C, a j ≤ a k) := by
  simp [extended_cover]

/-- Dotting the canonical cover indicator of `E(C)` with `x` recovers the left-hand side
`∑_{j ∈ E(C)} x_j` of the extended cover inequality. -/
theorem extended_cover_dotProduct
    (a : Fin n → ℕ)
    (C : Finset (Fin n))
    (x : Fin n → ℝ) :
    cover_indicator (extended_cover a C) ⬝ᵥ x =
      (extended_cover a C).sum fun j ↦ x j := by
  classical
  simp [dotProduct, cover_indicator]

/-- The equality face cut out from the knapsack polytope by the extended cover inequality
attached to `C`, viewed as the canonical Chapter 3 equality face `face_set`. -/
abbrev extended_cover_face
    (a : Fin n → ℕ)
    (b : ℕ)
    (C : Finset (Fin n)) : Set (Fin n → ℝ) :=
  face_set
    (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
    (cover_indicator (extended_cover a C))
    (cover_inequality_rhs C)

/-- Membership in `extended_cover_face a b C` means belonging to the knapsack polytope and
saturating the extended cover inequality. -/
theorem mem_extended_cover_face_iff
    (a : Fin n → ℕ)
    (b : ℕ)
    (C : Finset (Fin n))
    (x : Fin n → ℝ) :
    x ∈ extended_cover_face a b C ↔
      x ∈ zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ) ∧
        cover_indicator (extended_cover a C) ⬝ᵥ x = cover_inequality_rhs C := by
  simpa [extended_cover_face] using
    (mem_face_set_iff :
      x ∈ face_set
            (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
            (cover_indicator (extended_cover a C))
            (cover_inequality_rhs C) ↔
        x ∈ zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ) ∧
          cover_indicator (extended_cover a C) ⬝ᵥ x = cover_inequality_rhs C)

/-- Helper for Exercise 7.9: if a coefficient vector already has a knapsack Chvatal
presentation, then lowering it coordinatewise preserves the same right-hand side by increasing
only the lower-bound multipliers. -/
theorem knapsackChvatalPresentation_of_le
    (a : Fin n → ℕ)
    (b : ℕ)
    (coeff coeff' : Fin n → ℝ)
    (rhs : ℕ)
    (hcoeff : IsKnapsackChvatalPresentation a b coeff rhs)
    (hle : ∀ j, coeff' j ≤ coeff j) :
    IsKnapsackChvatalPresentation a b coeff' rhs := by
  rcases hcoeff with ⟨u₀, u, v, hu₀, hu, hv, hcoeff_eq, hrhs⟩
  let w : Fin n → ℝ := fun j ↦ coeff j - coeff' j
  have hw_nonneg : ∀ j, 0 ≤ w j := by
    intro j
    exact sub_nonneg.mpr (hle j)
  refine ⟨u₀, u, fun j ↦ v j + w j, hu₀, hu, ?_, ?_, hrhs⟩
  · -- The new lower-bound multipliers stay nonnegative because we only add slack.
    intro j
    exact add_nonneg (hv j) (hw_nonneg j)
  · -- Subtracting the added slack lowers the coefficient vector to `coeff'`.
    funext j
    have hcoeff_j := congrFun hcoeff_eq j
    dsimp [w]
    linarith

/-- Helper for Exercise 7.9: antitonicity lets us choose the smallest cover index as a pivot of
maximal cover weight. -/
theorem exercise79_exists_maxWeightPivot
    (a : Fin n → ℕ)
    (C : Finset (Fin n))
    (ha_desc : Antitone a)
    (hC_nonempty : C.Nonempty) :
    ∃ h ∈ C, ∀ j ∈ C, a j ≤ a h := by
  refine ⟨C.min' hC_nonempty, Finset.min'_mem C hC_nonempty, ?_⟩
  intro j hj
  -- The minimum index in the cover carries the maximal weight because `a` is antitone.
  exact ha_desc (Finset.min'_le C j hj)

/-- Helper for Exercise 7.9: the Exercise 7.8 coefficient vector dominates the indicator of the
extended cover when the pivot has maximal weight on `C`. -/
theorem exercise79_exercise78Coeff_ge_extendedCoverIndicator
    (a : Fin n → ℕ)
    (C : Finset (Fin n))
    (ha_pos : ∀ j, 0 < a j)
    {h : Fin n}
    (hhC : h ∈ C)
    (hhmax : ∀ j ∈ C, a j ≤ a h) :
    ∀ j, cover_indicator (extended_cover a C) j ≤ exercise_7_8_chvatal_coeffs a C h j := by
  classical
  intro j
  by_cases hjC : j ∈ C
  · -- On the cover both coefficient vectors equal `1`.
    simp [cover_indicator, exercise_7_8_chvatal_coeffs_apply, mem_extended_cover_iff, hjC]
  · by_cases hjE : j ∈ extended_cover a C
    · rcases (mem_extended_cover_iff a C j).mp hjE with (hjC' | ⟨_, hdom⟩)
      · exact (hjC hjC').elim
      have hh_le : a h ≤ a j := hdom h hhC
      have hpivot_pos : 0 < (a h : ℝ) := by
        exact_mod_cast ha_pos h
      have hratio_ge_one : 1 ≤ (a j : ℝ) / (a h : ℝ) := by
        rw [one_le_div hpivot_pos]
        simpa using (show (a h : ℝ) ≤ (a j : ℝ) by exact_mod_cast hh_le)
      have hfloor_pos : 0 < Int.floor ((a j : ℝ) / (a h : ℝ)) :=
        (Int.floor_pos).2 hratio_ge_one
      have hone_le :
          (1 : ℝ) ≤ (Int.floor ((a j : ℝ) / (a h : ℝ)) : ℝ) := by
        exact_mod_cast hfloor_pos
      -- Every index in `E(C) \ C` gets at least coefficient `1` in Exercise 7.8.
      simpa [cover_indicator, exercise_7_8_chvatal_coeffs_apply, hjC, hjE] using hone_le
    · have hnot_all : ¬ ∀ i ∈ C, a i ≤ a j := by
        intro hall
        exact hjE ((mem_extended_cover_iff a C j).mpr (Or.inr ⟨hjC, hall⟩))
      push Not at hnot_all
      rcases hnot_all with ⟨i, hiC, hij_lt⟩
      have hj_lt_h : a j < a h := lt_of_lt_of_le hij_lt (hhmax i hiC)
      have hpivot_pos : 0 < (a h : ℝ) := by
        exact_mod_cast ha_pos h
      have hratio_nonneg : 0 ≤ (a j : ℝ) / (a h : ℝ) := by
        exact div_nonneg (by exact_mod_cast Nat.zero_le (a j)) hpivot_pos.le
      have hratio_lt_one : (a j : ℝ) / (a h : ℝ) < 1 := by
        rw [div_lt_iff₀ hpivot_pos]
        simpa using (show (a j : ℝ) < (a h : ℝ) by exact_mod_cast hj_lt_h)
      have hfloor_zero : Int.floor ((a j : ℝ) / (a h : ℝ)) = 0 :=
        (Int.floor_eq_zero_iff).2 ⟨hratio_nonneg, hratio_lt_one⟩
      -- Outside `E(C)`, Exercise 7.8 also gives coefficient `0`.
      simp [cover_indicator, exercise_7_8_chvatal_coeffs_apply, hjC, hjE, hfloor_zero]

/-- Helper for Exercise 7.9: every omit-one cover point remains tight for the extended cover
inequality because the extension contains `C` and the omit-one point vanishes off `C`. -/
theorem exercise79_omitPoint_mem_extendedCoverFace
    (a : Fin n → ℕ)
    (b : ℕ)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    {j : Fin n}
    (hj : j ∈ C) :
    omitPoint C j ∈ extended_cover_face a b C := by
  have hrestricted :
      omitPoint C j ∈ cover_restricted_polytope a b C :=
    omitPoint_mem_coverRestrictedPolytope a b C hC hj
  rcases (mem_cover_restricted_polytope_iff a b C (omitPoint C j)).mp hrestricted with
    ⟨hxP, hxZero⟩
  rw [mem_extended_cover_face_iff]
  refine ⟨hxP, ?_⟩
  -- Split the extension sum into the cover part and the zero off-cover tail.
  rw [extended_cover_dotProduct]
  have hCsubset : C ⊆ extended_cover a C := by
    intro i hi
    exact (mem_extended_cover_iff a C i).mpr (Or.inl hi)
  calc
    (extended_cover a C).sum (omitPoint C j)
      = C.sum (omitPoint C j) + (extended_cover a C \ C).sum (omitPoint C j) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (Finset.sum_sdiff hCsubset (f := omitPoint C j)).symm
    _ = C.sum (omitPoint C j) := by
          have hzero :
              (extended_cover a C \ C).sum (omitPoint C j) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro i hi
            have hi_not_mem_C : i ∉ C := (Finset.mem_sdiff.mp hi).2
            exact hxZero i hi_not_mem_C
          rw [hzero, add_zero]
    _ = cover_inequality_rhs C := omitPoint_coverSum_eq_rhs C hj

/-- Helper for Exercise 7.9: since every singleton item is feasible, the ambient `0,1`
knapsack polytope is full-dimensional. -/
theorem exercise79_knapsackPolytope_finrank
    [NeZero n]
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_le_b : ∀ j, a j ≤ b) :
    Module.finrank ℝ
        (affineSpan ℝ (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))).direction = n := by
  have hnonneg : ∀ j, 0 ≤ (a j : ℝ) := by
    intro j
    exact_mod_cast Nat.zero_le (a j)
  have hb_nonneg : (0 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast Nat.zero_le b
  have hdim :=
    zero_one_knapsack_polytope_finrank_direction_affineSpan
      (fun i ↦ (a i : ℝ)) (b : ℝ) hnonneg hb_nonneg
  have hover :
      zero_one_knapsack_overweight_indices (fun i ↦ (a i : ℝ)) (b : ℝ) = ∅ := by
    ext j
    simp [zero_one_knapsack_overweight_indices, ha_le_b j]
  simpa [hover] using hdim

/-- Helper for Exercise 7.9: the Chvatal presentation from part (ii) certifies that the extended
cover inequality is valid on the ambient knapsack polytope. -/
theorem exercise79_extendedCover_validOnKnapsackPolytope
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_pos : ∀ j, 0 < a j)
    (ha_le_b : ∀ j, a j ≤ b)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C) :
    is_valid_inequality
      (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
      (cover_indicator (extended_cover a C))
      (cover_inequality_rhs C) := by
  let _ := ha_le_b
  rw [zero_one_knapsack_polytope_eq_convexHull]
  rw [is_valid_inequality_convexHull_iff]
  intro x hx
  have hC_cover : IsKnapsackCover a b C := inferInstance
  have hC_nonempty : C.Nonempty := by
    by_contra hC_empty
    rw [Finset.not_nonempty_iff_eq_empty] at hC_empty
    have hsum_gt : b < C.sum a := (isKnapsackCover_iff a b C).mp hC_cover
    simp [hC_empty] at hsum_gt
  rcases exercise79_exists_maxWeightPivot a C ha_desc hC_nonempty with ⟨h, hhC, hhmax⟩
  have hbase :
      IsKnapsackChvatalPresentation a b (exercise_7_8_chvatal_coeffs a C h) (C.card - 1) :=
    exercise_7_8_chvatal_inequality a b C hC h hhC hhmax
  have hchvatal :
      IsKnapsackChvatalPresentation
        a
        b
        (cover_indicator (extended_cover a C))
        (C.card - 1) :=
    knapsackChvatalPresentation_of_le
      a
      b
      (exercise_7_8_chvatal_coeffs a C h)
      (cover_indicator (extended_cover a C))
      (C.card - 1)
      hbase
      (exercise79_exercise78Coeff_ge_extendedCoverIndicator a C ha_pos hhC hhmax)
  rcases hchvatal with ⟨u₀, u, v, hu₀, hu, hv, hcoeff_eq, hrhs⟩
  rw [mem_zero_one_knapsack_set_iff] at hx
  rcases hx with ⟨hbin, hweight⟩
  have hx_nonneg : ∀ j, 0 ≤ x j := by
    intro j
    obtain hxj | hxj := hbin j
    · simp [hxj]
    · simp [hxj]
  have hx_le_one : ∀ j, x j ≤ 1 := by
    intro j
    obtain hxj | hxj := hbin j
    · simp [hxj]
    · simp [hxj]
  have hcoeff_point :
      ∀ j, cover_indicator (extended_cover a C) j = u₀ * (a j : ℝ) + u j - v j := by
    intro j
    exact (congrFun hcoeff_eq j).symm
  have hterm :
      ∀ j,
        (u₀ * (a j : ℝ) + u j - v j) * x j ≤
          u₀ * ((a j : ℝ) * x j) + u j := by
    intro j
    have haj_nonneg : 0 ≤ (a j : ℝ) := by
      exact_mod_cast Nat.zero_le (a j)
    have hax_nonneg : 0 ≤ (a j : ℝ) * x j := mul_nonneg haj_nonneg (hx_nonneg j)
    nlinarith [hu₀, hu j, hv j, hx_nonneg j, hx_le_one j, hax_nonneg]
  have hagg :
      cover_indicator (extended_cover a C) ⬝ᵥ x ≤
        u₀ * (b : ℝ) + Finset.univ.sum u := by
    calc
      cover_indicator (extended_cover a C) ⬝ᵥ x
          = ∑ j, (u₀ * (a j : ℝ) + u j - v j) * x j := by
              simp_rw [dotProduct, hcoeff_point]
      _ ≤ ∑ j, (u₀ * ((a j : ℝ) * x j) + u j) := by
            exact Finset.sum_le_sum fun j _ ↦ hterm j
      _ = ∑ j, u₀ * ((a j : ℝ) * x j) + ∑ j, u j := by
            rw [Finset.sum_add_distrib]
      _ = u₀ * (∑ j, (a j : ℝ) * x j) + Finset.univ.sum u := by
            rw [← Finset.mul_sum]
      _ ≤ u₀ * (b : ℝ) + Finset.univ.sum u := by
            gcongr
  let m : ℕ := (extended_cover a C).sum fun j ↦ if x j = 1 then 1 else 0
  have hm_eq : cover_indicator (extended_cover a C) ⬝ᵥ x = (m : ℝ) := by
    rw [coverIndicator_dot_eq_sum]
    -- The binary-point support sum is an integer because every coordinate is `0` or `1`.
    calc
      (extended_cover a C).sum x
          = Finset.sum (extended_cover a C)
              (fun j ↦ (((if x j = 1 then 1 else 0 : ℕ)) : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              obtain hxj | hxj := hbin j
              · simp [hxj]
              · simp [hxj]
      _ = (m : ℝ) := by
            simp [m]
  have hm_le_rhs : (m : ℤ) ≤ Int.ofNat (C.card - 1) := by
    have hm_le_real : (m : ℝ) ≤ u₀ * (b : ℝ) + Finset.univ.sum u := by
      simpa [hm_eq] using hagg
    have hm_floor :
        (m : ℤ) ≤ Int.floor (u₀ * (b : ℝ) + Finset.univ.sum u) :=
      Int.le_floor.mpr hm_le_real
    simpa [hrhs] using hm_floor
  have hC_nonempty : C.Nonempty := by
    have hC_cover : IsKnapsackCover a b C := inferInstance
    by_contra hC_empty
    rw [Finset.not_nonempty_iff_eq_empty] at hC_empty
    have hsum_gt : b < C.sum a := (isKnapsackCover_iff a b C).mp hC_cover
    simp [hC_empty] at hsum_gt
  have hcard_one_le : 1 ≤ C.card := Nat.succ_le_of_lt (Finset.card_pos.mpr hC_nonempty)
  have hm_le_cover_rhs : (m : ℝ) ≤ cover_inequality_rhs C := by
    have hm_le_natCast : (m : ℝ) ≤ ((C.card - 1 : ℕ) : ℝ) := by
      have hm_le_intCast : ((m : ℤ) : ℝ) ≤ (Int.ofNat (C.card - 1) : ℝ) := by
        exact_mod_cast hm_le_rhs
      simpa using hm_le_intCast
    simpa [cover_inequality_rhs_eq, Nat.cast_sub hcard_one_le] using hm_le_natCast
  simpa [hm_eq] using hm_le_cover_rhs

-- The next helpers start the codimension-one route for the extended-cover facet proof.
/-- Helper for Exercise 7.9: a feasible indicator vector is a point of the ambient `0,1`
knapsack polytope. -/
theorem coverIndicator_mem_zeroOneKnapsackPolytope_of_sum_le
    (a : Fin n → ℕ)
    (b : ℕ)
    (D : Finset (Fin n))
    (hDsum : D.sum a ≤ b) :
    cover_indicator D ∈ zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ) := by
  rw [zero_one_knapsack_polytope_eq_convexHull]
  refine subset_convexHull ℝ _ ?_
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · -- The indicator of a finite set is binary on every coordinate.
    intro i
    by_cases hi : i ∈ D
    · right
      simp [cover_indicator, hi]
    · left
      simp [cover_indicator, hi]
  · -- The weight of the indicator vector is exactly the support sum.
    calc
      ∑ i, (a i : ℝ) * cover_indicator D i
          = ∑ i, cover_indicator D i * (a i : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_comm]
      _ = cover_indicator D ⬝ᵥ (fun i ↦ (a i : ℝ)) := by
            rfl
      _ = D.sum (fun i ↦ (a i : ℝ)) := by
            simpa using coverIndicator_dot_eq_sum D (fun i ↦ (a i : ℝ))
      _ = ((D.sum a : ℕ) : ℝ) := by
            rw [Nat.cast_sum]
      _ ≤ (b : ℝ) := by
            exact_mod_cast hDsum

/-- Helper for Exercise 7.9: a nonzero linear functional on `ℝ^n` has a codimension-one kernel.
-/
private lemma exercise79_finrankKerEqCardSubOne {L : (Fin n → ℝ) →ₗ[ℝ] ℝ}
    (hL : L ≠ 0) :
    Module.finrank ℝ (LinearMap.ker L) = n - 1 := by
  let f : Module.Dual ℝ (Fin n → ℝ) := L
  have hf : f ≠ 0 := by
    simpa [f] using hL
  have hker_add_one :
      Module.finrank ℝ (LinearMap.ker L) + 1 = n := by
    simpa [f, Module.finrank_fintype_fun_eq_card] using f.finrank_ker_add_one_of_ne_zero hf
  exact Nat.eq_sub_of_add_eq hker_add_one

/-- Helper for Exercise 7.9: if every point of a face lies on the same exposed level set, then
the face direction is contained in the kernel of the exposing functional. -/
private lemma exercise79_faceDirection_le_dotProduct_ker
    {F : Set (Fin n → ℝ)} {c x₀ : Fin n → ℝ} {δ : ℝ}
    (hx₀ : x₀ ∈ F)
    (hlevel : ∀ ⦃x : Fin n → ℝ⦄, x ∈ F → c ⬝ᵥ x = δ) :
    (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductStrongDual c).toLinearMap := by
  have hspan_level :
      (affineSpan ℝ F : Set (Fin n → ℝ)) ⊆ {x | c ⬝ᵥ x = δ} := by
    intro x hx
    -- The exposing equation is affine, so it extends from `F` to its affine span.
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
  -- Two points on the same exposed level differ by a kernel vector.
  have hx_eq : c ⬝ᵥ x = δ := hspan_level hx_aff
  have hx₀_eq : c ⬝ᵥ x₀ = δ := hlevel hx₀
  simp [dotProductStrongDual_apply, vsub_eq_sub, hx_eq, hx₀_eq]

/-- Helper for Exercise 7.9: subtracting two omit-one cover points isolates the corresponding
basis difference on the cover. -/
theorem omitPoint_sub_omitPoint_eq_single_sub_single
    (C : Finset (Fin n))
    {i j : Fin n}
    (hi : i ∈ C)
    (hj : j ∈ C)
    (hij : i ≠ j) :
    omitPoint C i - omitPoint C j = Pi.single j (1 : ℝ) - Pi.single i 1 := by
  ext m
  by_cases hmj : m = j
  · subst hmj
    have hm_ne_i : m ≠ i := fun h ↦ hij h.symm
    simp [omitPoint, hj, hm_ne_i]
  · by_cases hmi : m = i
    · subst hmi
      simp [omitPoint, hi, hij]
    · by_cases hmC : m ∈ C
      · simp [omitPoint, hmC, hmi, hmj]
      · simp [omitPoint, hmC, hmi, hmj]

/-- Helper for Exercise 7.9: inserting one outside index and erasing the pivot changes the cover
indicator by the single free coordinate. -/
theorem coverIndicator_insert_erase_sub_omitPoint_eq_single
    (C : Finset (Fin n))
    {j k : Fin n}
    (hj : j ∈ C)
    (hkC : k ∉ C) :
    cover_indicator ((insert k C).erase j) - omitPoint C j = Pi.single k (1 : ℝ) := by
  ext m
  by_cases hmk : m = k
  · subst hmk
    have hm_ne_j : m ≠ j := fun h ↦ hkC (h.symm ▸ hj)
    simp [cover_indicator, omitPoint, hkC, hm_ne_j]
  · by_cases hmj : m = j
    · subst hmj
      have hm_ne_k : m ≠ k := fun h ↦ hkC (h ▸ hj)
      simp [cover_indicator, omitPoint, hj, hm_ne_k]
    · by_cases hmC : m ∈ C
      · simp [cover_indicator, omitPoint, hmC, hmk, hmj]
      · simp [cover_indicator, omitPoint, hmC, hmk, hmj]

/-- Helper for Exercise 7.9: erasing two cover indices and inserting one outside extension index
isolates the corresponding basis-difference direction. -/
theorem coverIndicator_doubleErase_sub_omitPoint_eq_single_sub_single
    (C : Finset (Fin n))
    {r s k : Fin n}
    (hr : r ∈ C)
    (hs : s ∈ C)
    (hrs : r ≠ s)
    (hkC : k ∉ C) :
    cover_indicator (((insert k C).erase r).erase s) - omitPoint C s =
      (Pi.single k (1 : ℝ) - Pi.single r 1 : Fin n → ℝ) := by
  -- Compare the two vectors coordinatewise on the inserted index, the two erased indices,
  -- and the untouched coordinates.
  ext m
  by_cases hmk : m = k
  · subst hmk
    have hm_ne_r : m ≠ r := fun h ↦ hkC (h.symm ▸ hr)
    have hm_ne_s : m ≠ s := fun h ↦ hkC (h.symm ▸ hs)
    simp [cover_indicator, omitPoint, hkC, hm_ne_r, hm_ne_s]
  · by_cases hmr : m = r
    · subst hmr
      have hm_ne_k : m ≠ k := by simpa using hmk
      have hm_ne_s : m ≠ s := hrs
      simp [cover_indicator, omitPoint, hr, hm_ne_k, hm_ne_s]
    · by_cases hms : m = s
      · subst hms
        have hm_ne_k : m ≠ k := by simpa using hmk
        have hm_ne_r : m ≠ r := by simpa [eq_comm] using hrs
        simp [cover_indicator, omitPoint, hs, hm_ne_k, hm_ne_r]
      · by_cases hmC : m ∈ C
        · simp [cover_indicator, omitPoint, hmC, hmk, hmr, hms]
        · simp [cover_indicator, omitPoint, hmC, hmk, hmr, hms]

/-- Helper for Exercise 7.9: inserting one outside index and erasing one cover index adds the
outside weight to the erased-cover sum. -/
theorem insert_erase_sum_eq_erase_sum_add
    (a : Fin n → ℕ)
    (C : Finset (Fin n))
    {j k : Fin n}
    (hj : j ∈ C)
    (hkC : k ∉ C) :
    ((insert k C).erase j).sum a = (C.erase j).sum a + a k := by
  have hkj : k ≠ j := fun h ↦ hkC (h ▸ hj)
  have hset : (insert k C).erase j = insert k (C.erase j) := by
    ext i
    by_cases hik : i = k
    · subst hik
      simp [Finset.mem_erase, hkC, hkj]
    · simp [Finset.mem_erase, hik]
  -- Normalize the support before evaluating the finite sum.
  rw [hset, Finset.sum_insert]
  · simp [add_comm]
  · simp [hkC]

/-- Helper for Exercise 7.9: inserting one outside index and erasing two distinct cover indices
adds the outside weight to the double-erased cover sum. -/
theorem doubleInsert_doubleErase_sum_eq_doubleErase_sum_add
    (a : Fin n → ℕ)
    (C : Finset (Fin n))
    {r s k : Fin n}
    (hr : r ∈ C)
    (hs : s ∈ C)
    (hrs : r ≠ s)
    (hkC : k ∉ C) :
    (((insert k C).erase r).erase s).sum a = ((C.erase r).erase s).sum a + a k := by
  let _ := hrs
  have hkr : k ≠ r := fun h ↦ hkC (h ▸ hr)
  have hks : k ≠ s := fun h ↦ hkC (h ▸ hs)
  have hset : ((insert k C).erase r).erase s = insert k ((C.erase r).erase s) := by
    ext i
    by_cases hik : i = k
    · subst hik
      simp [Finset.mem_erase, hkC, hkr, hks]
    · simp [Finset.mem_erase, hik]
  -- Normalize the support before evaluating the finite sum.
  rw [hset, Finset.sum_insert]
  · simp [add_comm]
  · simp [hkC]

/-- Helper for Exercise 7.9: the outside witness obtained by replacing `ℓ` with any later index
outside `E(C)` still lies on the exposed extended-cover face. -/
theorem extendedCoverOutsideWitness_mem_face
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    {j₁ ℓ k : Fin n}
    (hj₁ : j₁ ∈ C)
    (hkE : k ∉ extended_cover a C)
    (hℓ_out : ℓ ∉ extended_cover a C)
    (hℓ_min : ∀ i : Fin n, i < ℓ → i ∈ extended_cover a C)
    (hside₂ : ((insert ℓ C).erase j₁).sum a ≤ b) :
    cover_indicator ((insert k C).erase j₁) ∈ extended_cover_face a b C := by
  have hkC : k ∉ C := fun hkC ↦ hkE ((mem_extended_cover_iff a C k).mpr (Or.inl hkC))
  have hℓC : ℓ ∉ C := fun hℓC ↦ hℓ_out ((mem_extended_cover_iff a C ℓ).mpr (Or.inl hℓC))
  have hℓ_le_k : ℓ ≤ k := by
    exact le_of_not_gt fun hk_lt ↦ hkE (hℓ_min k hk_lt)
  have hweight : a k ≤ a ℓ := ha_desc hℓ_le_k
  have hsum_k :
      ((insert k C).erase j₁).sum a ≤ b := by
    have hside₂' : (C.erase j₁).sum a + a ℓ ≤ b := by
      simpa [insert_erase_sum_eq_erase_sum_add a C hj₁ hℓC] using hside₂
    -- Replace the witness index `ℓ` by the no-heavier index `k`.
    simpa [insert_erase_sum_eq_erase_sum_add a C hj₁ hkC] using
      (le_trans (Nat.add_le_add_left hweight _) hside₂')
  rw [mem_extended_cover_face_iff]
  refine ⟨coverIndicator_mem_zeroOneKnapsackPolytope_of_sum_le a b _ hsum_k, ?_⟩
  have homit :
      cover_indicator (extended_cover a C) ⬝ᵥ omitPoint C j₁ = cover_inequality_rhs C :=
    (mem_extended_cover_face_iff a b C (omitPoint C j₁)).mp
      (exercise79_omitPoint_mem_extendedCoverFace a b C hC hj₁) |>.2
  -- On the exposed support, replacing `ℓ` by another outside index does not change the sum.
  calc
    cover_indicator (extended_cover a C) ⬝ᵥ cover_indicator ((insert k C).erase j₁)
        = (extended_cover a C).sum (cover_indicator ((insert k C).erase j₁)) := by
            rw [extended_cover_dotProduct]
    _ = (extended_cover a C).sum (omitPoint C j₁) := by
          refine Finset.sum_congr rfl ?_
          intro i hiE
          have hik : i ≠ k := fun hik ↦ hkE (hik ▸ hiE)
          simp [cover_indicator, omitPoint, Finset.mem_erase, hik]
    _ = cover_indicator (extended_cover a C) ⬝ᵥ omitPoint C j₁ := by
          rw [extended_cover_dotProduct]
    _ = cover_inequality_rhs C := homit

/-- Helper for Exercise 7.9: when `0 ∉ C`, replacing the inserted index `0` by any extension
index `k ∈ E(C) \ C` preserves face membership of the double-erase witness. -/
theorem extendedCoverExtensionWitness_mem_face_of_zero_not_mem
    [NeZero n]
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    {j₁ j₂ k : Fin n}
    (h0C : (0 : Fin n) ∉ C)
    (hj₁ : j₁ ∈ C)
    (hj₂ : j₂ ∈ C)
    (hj₁₂ : j₁ ≠ j₂)
    (hkE : k ∈ extended_cover a C)
    (hkC : k ∉ C)
    (hside₁ : (((insert (0 : Fin n) C).erase j₁).erase j₂).sum a ≤ b) :
    cover_indicator (((insert k C).erase j₁).erase j₂) ∈ extended_cover_face a b C := by
  have hweight : a k ≤ a 0 := by
    exact ha_desc (show (0 : Fin n) ≤ k by exact Fin.zero_le _)
  have hsum_k :
      (((insert k C).erase j₁).erase j₂).sum a ≤ b := by
    have hside₁' : ((C.erase j₁).erase j₂).sum a + a 0 ≤ b := by
      simpa [doubleInsert_doubleErase_sum_eq_doubleErase_sum_add a C hj₁ hj₂ hj₁₂ h0C] using hside₁
    -- Replace the inserted zero index by the no-heavier extension index `k`.
    simpa [doubleInsert_doubleErase_sum_eq_doubleErase_sum_add a C hj₁ hj₂ hj₁₂ hkC] using
      (le_trans (Nat.add_le_add_left hweight _) hside₁')
  rw [mem_extended_cover_face_iff]
  refine ⟨coverIndicator_mem_zeroOneKnapsackPolytope_of_sum_le a b _ hsum_k, ?_⟩
  have hsubset :
      (((insert k C).erase j₁).erase j₂) ⊆ extended_cover a C := by
    intro i hi
    rcases Finset.mem_erase.mp hi with ⟨hi_ne_j₂, hi_mem⟩
    rcases Finset.mem_erase.mp hi_mem with ⟨hi_ne_j₁, hi_mem'⟩
    rcases Finset.mem_insert.mp hi_mem' with rfl | hiC
    · exact hkE
    · exact (mem_extended_cover_iff a C i).mpr (Or.inl hiC)
  have hcard :
      ((((insert k C).erase j₁).erase j₂).card : ℝ) = cover_inequality_rhs C := by
    have hj₁_insert : j₁ ∈ insert k C := by simp [hj₁]
    have hj₂_mem : j₂ ∈ (insert k C).erase j₁ := by
      simp [hj₂, show j₂ ≠ j₁ by exact fun h ↦ hj₁₂ h.symm]
    have hcard1 : ((insert k C).erase j₁).card = C.card := by
      rw [Finset.card_erase_of_mem hj₁_insert, Finset.card_insert_of_notMem hkC]
      simp
    have hcard_one_le : 1 ≤ C.card := Finset.one_le_card.mpr ⟨j₁, hj₁⟩
    calc
      ((((insert k C).erase j₁).erase j₂).card : ℝ)
          = ((((insert k C).erase j₁).card - 1 : ℕ) : ℝ) := by
              rw [Finset.card_erase_of_mem hj₂_mem]
      _ = ((C.card - 1 : ℕ) : ℝ) := by rw [hcard1]
      _ = cover_inequality_rhs C := by
              simp [cover_inequality_rhs_eq, Nat.cast_sub hcard_one_le]
  -- All coordinates of the witness lie inside `E(C)`, so the exposed sum is just its cardinality.
  calc
    cover_indicator (extended_cover a C) ⬝ᵥ cover_indicator (((insert k C).erase j₁).erase j₂)
        = (extended_cover a C).sum (cover_indicator (((insert k C).erase j₁).erase j₂)) := by
            rw [extended_cover_dotProduct]
    _ = (((insert k C).erase j₁).erase j₂).sum
          (cover_indicator (((insert k C).erase j₁).erase j₂)) := by
            symm
            exact Finset.sum_subset hsubset (by
              intro i hiE hiD
              simp [cover_indicator, hiD])
    _ = ((((insert k C).erase j₁).erase j₂).card : ℝ) := by
          calc
            (((insert k C).erase j₁).erase j₂).sum
                (cover_indicator (((insert k C).erase j₁).erase j₂)) =
              (((insert k C).erase j₁).erase j₂).sum (fun _ ↦ (1 : ℝ)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [cover_indicator, hi]
            _ = ((((insert k C).erase j₁).erase j₂).card : ℝ) := by
                simp
    _ = cover_inequality_rhs C := hcard

/-- Helper for Exercise 7.9: in the `0 ∈ C` branch, replacing the erased zero index by any
extension index preserves the cover weight because the extension index has the same weight as `0`.
-/
theorem extendedCoverZeroBranchWitness_sum_le
    [NeZero n]
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    {j₁ j₂ k : Fin n}
    (h0C : (0 : Fin n) ∈ C)
    (hj₁ : j₁ ∈ C)
    (hj₂ : j₂ ∈ C)
    (hj₁₂ : j₁ ≠ j₂)
    (hkE : k ∈ extended_cover a C)
    (hkC : k ∉ C) :
    (((insert k C).erase 0).erase (if j₁ = 0 then j₂ else j₁)).sum a ≤ b := by
  let σ : Fin n := if j₁ = 0 then j₂ else j₁
  have hσC : σ ∈ C := by
    by_cases hj₁_zero : j₁ = 0
    · simp [σ, hj₁_zero, hj₂]
    · simp [σ, hj₁_zero, hj₁]
  have hσ_ne_zero : σ ≠ 0 := by
    by_cases hj₁_zero : j₁ = 0
    · simpa [σ, hj₁_zero] using hj₁₂.symm
    · simp [σ, hj₁_zero]
  have hzero_ne_sigma : (0 : Fin n) ≠ σ := by
    intro h
    exact hσ_ne_zero h.symm
  have hk_eq_zero : a k = a 0 := by
    have hzero_le : a 0 ≤ a k := by
      rcases (mem_extended_cover_iff a C k).mp hkE with (hkC' | ⟨_, hdom⟩)
      · exact (hkC hkC').elim
      · exact hdom 0 h0C
    have hk_le_zero : a k ≤ a 0 := ha_desc (Fin.zero_le _)
    exact le_antisymm hk_le_zero hzero_le
  have hswap :
      ((C.erase 0).erase σ) = ((C.erase σ).erase 0) := by
    ext i
    simp [Finset.mem_erase, and_left_comm]
  have hsum :
      (((insert k C).erase 0).erase σ).sum a = (C.erase σ).sum a := by
    have hdouble :
        (((insert k C).erase 0).erase σ).sum a = ((C.erase 0).erase σ).sum a + a k := by
      simpa [σ] using
        doubleInsert_doubleErase_sum_eq_doubleErase_sum_add a C h0C hσC hzero_ne_sigma hkC
    have hzero_mem : (0 : Fin n) ∈ C.erase σ := by
      simp [Finset.mem_erase, h0C, hzero_ne_sigma]
    have herase :
        ((C.erase σ).erase 0).sum a + a 0 = (C.erase σ).sum a := by
      simpa [add_comm] using (Finset.sum_erase_add (s := C.erase σ) (f := a) hzero_mem)
    calc
      (((insert k C).erase 0).erase σ).sum a = ((C.erase 0).erase σ).sum a + a k := hdouble
      _ = ((C.erase σ).erase 0).sum a + a 0 := by rw [hswap, hk_eq_zero]
      _ = (C.erase σ).sum a := herase
  -- Reduce the inserted witness to the feasible erased cover.
  rw [hsum]
  exact hC.erase_sum_le σ hσC

/-- Helper for Exercise 7.9: when `0 ∈ C`, replacing the zero cover index by an equal-weight
extension index preserves face membership of the corresponding double-erase witness. -/
theorem extendedCoverExtensionWitness_mem_face_of_zero_mem
    [NeZero n]
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    {j₁ j₂ k : Fin n}
    (h0C : (0 : Fin n) ∈ C)
    (hj₁ : j₁ ∈ C)
    (hj₂ : j₂ ∈ C)
    (hj₁₂ : j₁ ≠ j₂)
    (hkE : k ∈ extended_cover a C)
    (hkC : k ∉ C) :
    cover_indicator (((insert k C).erase 0).erase (if j₁ = 0 then j₂ else j₁)) ∈
      extended_cover_face a b C := by
  let σ : Fin n := if j₁ = 0 then j₂ else j₁
  have hσC : σ ∈ C := by
    by_cases hj₁_zero : j₁ = 0
    · simp [σ, hj₁_zero, hj₂]
    · simp [σ, hj₁_zero, hj₁]
  have hσ_ne_zero : σ ≠ 0 := by
    by_cases hj₁_zero : j₁ = 0
    · simpa [σ, hj₁_zero] using hj₁₂.symm
    · simp [σ, hj₁_zero]
  have hzero_ne_sigma : (0 : Fin n) ≠ σ := by
    intro h
    exact hσ_ne_zero h.symm
  have hsum_k :
      (((insert k C).erase 0).erase σ).sum a ≤ b :=
    extendedCoverZeroBranchWitness_sum_le a b ha_desc C hC h0C hj₁ hj₂ hj₁₂ hkE hkC
  rw [mem_extended_cover_face_iff]
  refine ⟨coverIndicator_mem_zeroOneKnapsackPolytope_of_sum_le a b _ hsum_k, ?_⟩
  have hsubset :
      (((insert k C).erase 0).erase σ) ⊆ extended_cover a C := by
    intro i hi
    rcases Finset.mem_erase.mp hi with ⟨hi_ne_sigma, hi_mem⟩
    rcases Finset.mem_erase.mp hi_mem with ⟨hi_ne_zero, hi_mem'⟩
    rcases Finset.mem_insert.mp hi_mem' with rfl | hiC
    · exact hkE
    · exact (mem_extended_cover_iff a C i).mpr (Or.inl hiC)
  have hcard :
      ((((insert k C).erase 0).erase σ).card : ℝ) = cover_inequality_rhs C := by
    have hσ_mem : σ ∈ (insert k C).erase 0 := by
      simp [Finset.mem_erase, hσ_ne_zero, hσC]
    have hcard1 : ((insert k C).erase 0).card = C.card := by
      rw [Finset.card_erase_of_mem]
      · rw [Finset.card_insert_of_notMem hkC]
        simp
      · simp [h0C]
    have hcard_one_le : 1 ≤ C.card := Finset.one_le_card.mpr ⟨0, h0C⟩
    calc
      ((((insert k C).erase 0).erase σ).card : ℝ)
          = ((((insert k C).erase 0).card - 1 : ℕ) : ℝ) := by
              rw [Finset.card_erase_of_mem hσ_mem]
      _ = ((C.card - 1 : ℕ) : ℝ) := by rw [hcard1]
      _ = cover_inequality_rhs C := by
              simp [cover_inequality_rhs_eq, Nat.cast_sub hcard_one_le]
  -- Every support index of the witness lies in `E(C)`, so the exposed sum is its support size.
  calc
    cover_indicator (extended_cover a C) ⬝ᵥ cover_indicator (((insert k C).erase 0).erase σ)
        = (extended_cover a C).sum (cover_indicator (((insert k C).erase 0).erase σ)) := by
            rw [extended_cover_dotProduct]
    _ =
        (((insert k C).erase 0).erase σ).sum
          (cover_indicator (((insert k C).erase 0).erase σ)) := by
          symm
          exact Finset.sum_subset hsubset (by
            intro i hiE hiD
            simp [cover_indicator, hiD])
    _ = ((((insert k C).erase 0).erase σ).card : ℝ) := by
          calc
            (((insert k C).erase 0).erase σ).sum
                (cover_indicator (((insert k C).erase 0).erase σ)) =
              (((insert k C).erase 0).erase σ).sum (fun _ ↦ (1 : ℝ)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [cover_indicator, hi]
            _ = ((((insert k C).erase 0).erase σ).card : ℝ) := by
                simp
    _ = cover_inequality_rhs C := hcard

/-- Helper for Exercise 7.9: every non-pivot cover index contributes the basis difference
`e_j - e_j₁` to the face direction. -/
theorem exercise79_coverDirection_mem
    (a : Fin n → ℕ)
    (b : ℕ)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    {j₁ j : Fin n}
    (hj₁ : j₁ ∈ C)
    (hj : j ∈ C)
    (hj_ne : j ≠ j₁) :
    (Pi.single j (1 : ℝ) - Pi.single j₁ 1 : Fin n → ℝ) ∈
      (affineSpan ℝ (extended_cover_face a b C)).direction := by
  have hj₁_aff :
      omitPoint C j₁ ∈ affineSpan ℝ (extended_cover_face a b C) := by
    exact mem_affineSpan ℝ (exercise79_omitPoint_mem_extendedCoverFace a b C hC hj₁)
  have hj_aff :
      omitPoint C j ∈ affineSpan ℝ (extended_cover_face a b C) := by
    exact mem_affineSpan ℝ (exercise79_omitPoint_mem_extendedCoverFace a b C hC hj)
  -- Comparing the two omit-one points isolates the desired cover basis difference.
  simpa [omitPoint_sub_omitPoint_eq_single_sub_single C hj₁ hj hj_ne.symm] using
    (AffineSubspace.vsub_mem_direction hj₁_aff hj_aff)

/-- Helper for Exercise 7.9: a feasible outside witness yields the free coordinate direction
`e_k`. -/
theorem exercise79_outsideDirection_mem
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    {j₁ ℓ k : Fin n}
    (hj₁ : j₁ ∈ C)
    (hkE : k ∉ extended_cover a C)
    (hℓ_out : ℓ ∉ extended_cover a C)
    (hℓ_min : ∀ i : Fin n, i < ℓ → i ∈ extended_cover a C)
    (hside₂ : ((insert ℓ C).erase j₁).sum a ≤ b) :
    (Pi.single k (1 : ℝ) : Fin n → ℝ) ∈
      (affineSpan ℝ (extended_cover_face a b C)).direction := by
  have hkC : k ∉ C := fun hkC ↦ hkE ((mem_extended_cover_iff a C k).mpr (Or.inl hkC))
  have hwitness :
      cover_indicator ((insert k C).erase j₁) ∈ extended_cover_face a b C :=
    extendedCoverOutsideWitness_mem_face a b ha_desc C hC hj₁ hkE hℓ_out hℓ_min hside₂
  have hwitness_aff :
      cover_indicator ((insert k C).erase j₁) ∈ affineSpan ℝ (extended_cover_face a b C) := by
    exact mem_affineSpan ℝ hwitness
  have homit_aff :
      omitPoint C j₁ ∈ affineSpan ℝ (extended_cover_face a b C) := by
    exact mem_affineSpan ℝ (exercise79_omitPoint_mem_extendedCoverFace a b C hC hj₁)
  -- Subtract the outside witness from the omit-one cover point to isolate `e_k`.
  simpa [coverIndicator_insert_erase_sub_omitPoint_eq_single C hj₁ hkC] using
    (AffineSubspace.vsub_mem_direction hwitness_aff homit_aff)

/-- Helper for Exercise 7.9: every extension index outside the cover contributes a basis
difference direction anchored at `j₁`. -/
theorem exercise79_extensionDirection_mem
    [NeZero n]
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    {j₁ j₂ k : Fin n}
    (hj₁ : j₁ ∈ C)
    (hj₂ : j₂ ∈ C)
    (hj₁₂ : j₁ ≠ j₂)
    (hkE : k ∈ extended_cover a C)
    (hkC : k ∉ C)
    (hside₁ : (((insert (0 : Fin n) C).erase j₁).erase j₂).sum a ≤ b) :
    (Pi.single k (1 : ℝ) - Pi.single j₁ 1 : Fin n → ℝ) ∈
      (affineSpan ℝ (extended_cover_face a b C)).direction := by
  by_cases h0C : (0 : Fin n) ∉ C
  · have hwitness :
        cover_indicator (((insert k C).erase j₁).erase j₂) ∈ extended_cover_face a b C :=
      extendedCoverExtensionWitness_mem_face_of_zero_not_mem
        a b ha_desc C h0C hj₁ hj₂ hj₁₂ hkE hkC hside₁
    have hwitness_aff :
        cover_indicator (((insert k C).erase j₁).erase j₂) ∈
          affineSpan ℝ (extended_cover_face a b C) := by
      exact mem_affineSpan ℝ hwitness
    have homit_aff :
        omitPoint C j₂ ∈ affineSpan ℝ (extended_cover_face a b C) := by
      exact mem_affineSpan ℝ (exercise79_omitPoint_mem_extendedCoverFace a b C hC hj₂)
    -- Subtract the double-erase witness from the omit-one cover point to isolate `e_k - e_j₁`.
    simpa [coverIndicator_doubleErase_sub_omitPoint_eq_single_sub_single C hj₁ hj₂ hj₁₂ hkC] using
      (AffineSubspace.vsub_mem_direction hwitness_aff homit_aff)
  · have h0C : (0 : Fin n) ∈ C := by simpa using h0C
    let σ : Fin n := if j₁ = 0 then j₂ else j₁
    have hσC : σ ∈ C := by
      by_cases hj₁_zero : j₁ = 0
      · simp [σ, hj₁_zero, hj₂]
      · simp [σ, hj₁_zero, hj₁]
    have hσ_ne_zero : σ ≠ 0 := by
      by_cases hj₁_zero : j₁ = 0
      · simpa [σ, hj₁_zero] using hj₁₂.symm
      · simp [σ, hj₁_zero]
    have hzero_ne_sigma : (0 : Fin n) ≠ σ := by
      intro h
      exact hσ_ne_zero h.symm
    have hwitness :
        cover_indicator (((insert k C).erase 0).erase σ) ∈ extended_cover_face a b C :=
      extendedCoverExtensionWitness_mem_face_of_zero_mem
        a b ha_desc C hC h0C hj₁ hj₂ hj₁₂ hkE hkC
    have hwitness_aff :
        cover_indicator (((insert k C).erase 0).erase σ) ∈
          affineSpan ℝ (extended_cover_face a b C) := by
      exact mem_affineSpan ℝ hwitness
    have homit_aff :
        omitPoint C σ ∈ affineSpan ℝ (extended_cover_face a b C) := by
      exact mem_affineSpan ℝ (exercise79_omitPoint_mem_extendedCoverFace a b C hC hσC)
    have hbase :
        (Pi.single k (1 : ℝ) - Pi.single (0 : Fin n) 1 : Fin n → ℝ) ∈
          (affineSpan ℝ (extended_cover_face a b C)).direction := by
      -- Subtract the zero-branch extension witness from the matching omit-one cover point.
      simpa [σ, coverIndicator_doubleErase_sub_omitPoint_eq_single_sub_single C h0C hσC
        hzero_ne_sigma hkC] using
        (AffineSubspace.vsub_mem_direction hwitness_aff homit_aff)
    by_cases hj₁_zero : j₁ = 0
    · subst j₁
      simpa using hbase
    · have hcover :
          (Pi.single (0 : Fin n) (1 : ℝ) - Pi.single j₁ 1 : Fin n → ℝ) ∈
            (affineSpan ℝ (extended_cover_face a b C)).direction :=
        exercise79_coverDirection_mem a b C hC hj₁ h0C (by
          intro h
          exact hj₁_zero h.symm)
      have hadd :
          ((Pi.single k (1 : ℝ) - Pi.single (0 : Fin n) 1 : Fin n → ℝ) +
              (Pi.single (0 : Fin n) (1 : ℝ) - Pi.single j₁ 1 : Fin n → ℝ)) ∈
            (affineSpan ℝ (extended_cover_face a b C)).direction :=
        Submodule.add_mem _ hbase hcover
      have hrewrite :
          ((Pi.single k (1 : ℝ) - Pi.single (0 : Fin n) 1 : Fin n → ℝ) +
              (Pi.single (0 : Fin n) (1 : ℝ) - Pi.single j₁ 1 : Fin n → ℝ)) =
            (Pi.single k (1 : ℝ) - Pi.single j₁ 1 : Fin n → ℝ) := by
        ext i
        simp [Pi.single_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      simpa [hrewrite] using hadd

/-- Helper for Exercise 7.9: a vector whose coordinates sum to zero on `E` decomposes into
anchored basis differences on `E` together with the free outside coordinates. -/
theorem sumZeroOnFinsetDecompose
    (E : Finset (Fin n))
    {j₀ : Fin n}
    (hj₀ : j₀ ∈ E)
    (x : Fin n → ℝ)
    (hzero : E.sum x = 0) :
    x =
      Finset.sum (E.erase j₀) (fun i ↦ x i • (Pi.single i (1 : ℝ) - Pi.single j₀ 1)) +
        Finset.sum (Finset.univ \ E) (fun i ↦ x i • Pi.single i 1) := by
  let inside : Fin n → ℝ :=
    Finset.sum (E.erase j₀) (fun i ↦ x i • (Pi.single i (1 : ℝ) - Pi.single j₀ 1))
  let outside : Fin n → ℝ :=
    Finset.sum (Finset.univ \ E) (fun i ↦ x i • Pi.single i 1)
  change x = inside + outside
  ext m
  change x m = inside m + outside m
  by_cases hmE : m ∈ E
  · by_cases hmj₀ : m = j₀
    · subst m
      have hout : outside j₀ = 0 := by
        dsimp [outside]
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hiE : i ∉ E := (Finset.mem_sdiff.mp hi).2
        have hji : j₀ ≠ i := fun h ↦ hiE (h.symm ▸ hj₀)
        simp [Pi.smul_apply, hji]
      have hsum_erase : (E.erase j₀).sum x + x j₀ = 0 := by
        simpa [hzero] using (E.sum_erase_add x hj₀)
      have hxj₀ : x j₀ = -((E.erase j₀).sum x) := by
        linarith
      have hinside : inside j₀ = -((E.erase j₀).sum x) := by
        dsimp [inside]
        rw [Finset.sum_apply]
        calc
          Finset.sum (E.erase j₀) (fun i ↦ (((x i) •
            ((Pi.single i (1 : ℝ) - Pi.single j₀ 1 : Fin n → ℝ))) j₀))
              = Finset.sum (E.erase j₀) (fun i ↦ -x i) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hij₀ : i ≠ j₀ := (Finset.mem_erase.mp hi).1
                  simp [Pi.smul_apply, hij₀, sub_eq_add_neg]
          _ = -((E.erase j₀).sum x) := by
                simp
      rw [hout, add_zero, hinside]
      simp [hxj₀]
    · have hmErase : m ∈ E.erase j₀ := by
        simp [hmE, hmj₀]
      have hout : outside m = 0 := by
        dsimp [outside]
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hiE : i ∉ E := (Finset.mem_sdiff.mp hi).2
        have hmi : m ≠ i := fun h ↦ hiE (h ▸ hmE)
        simp [Pi.smul_apply, hmi]
      have hinside : inside m = x m := by
        dsimp [inside]
        rw [Finset.sum_apply]
        rw [Finset.sum_eq_single_of_mem m hmErase]
        · simp [Pi.smul_apply, Pi.sub_apply, hmj₀]
        · intro i hi him
          have hi_ne_j₀ : i ≠ j₀ := (Finset.mem_erase.mp hi).1
          simp [Pi.smul_apply, Pi.sub_apply, him, hmj₀]
      rw [hout, add_zero, hinside]
  · have hinside : inside m = 0 := by
      dsimp [inside]
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hiE : i ∈ E := (Finset.mem_erase.mp hi).2
      have hmi : m ≠ i := fun h ↦ hmE (h ▸ hiE)
      have hmj₀ : m ≠ j₀ := fun h ↦ hmE (h ▸ hj₀)
      simp [Pi.smul_apply, Pi.sub_apply, hmi, hmj₀]
    have hm_out : m ∈ Finset.univ \ E := by
      simp [hmE]
    have hout : outside m = x m := by
      dsimp [outside]
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single_of_mem m hm_out]
      · simp [Pi.smul_apply]
      · intro i hi him
        simp [Pi.smul_apply, him]
    rw [hinside, zero_add, hout]

/-- Helper for Exercise 7.9: the kernel of the exposed extended-cover functional is already
spanned by the explicit cover, extension, and outside directions. -/
theorem exercise79_extendedCoverFace_ker_le_direction
    [NeZero n]
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (j₁ j₂ ℓ : Fin n)
    (hj₁ : j₁ ∈ C)
    (hj₂ : j₂ ∈ C)
    (hj₁₂ : j₁ ≠ j₂)
    (hℓ_out : ℓ ∉ extended_cover a C)
    (hℓ_min : ∀ i : Fin n, i < ℓ → i ∈ extended_cover a C)
    (hside₁ : (((insert (0 : Fin n) C).erase j₁).erase j₂).sum a ≤ b)
    (hside₂ : ((insert ℓ C).erase j₁).sum a ≤ b) :
    LinearMap.ker (dotProductStrongDual (cover_indicator (extended_cover a C))).toLinearMap ≤
      (affineSpan ℝ (extended_cover_face a b C)).direction := by
  let E : Finset (Fin n) := extended_cover a C
  let D : Submodule ℝ (Fin n → ℝ) := (affineSpan ℝ (extended_cover_face a b C)).direction
  intro x hx
  have hj₁E : j₁ ∈ E := by
    simpa [E] using (mem_extended_cover_iff a C j₁).mpr (Or.inl hj₁)
  have hxsum : E.sum x = 0 := by
    have hxker : ((dotProductStrongDual (cover_indicator E)).toLinearMap) x = 0 :=
      LinearMap.mem_ker.mp hx
    -- Rewrite kernel membership as the exposed support sum vanishing.
    calc
      E.sum x = cover_indicator E ⬝ᵥ x := by
        symm
        simp [E, extended_cover_dotProduct]
      _ = ((dotProductStrongDual (cover_indicator E)).toLinearMap) x := by
        simp [dotProductStrongDual_apply]
      _ = 0 := hxker
  have hdecomp :
      x =
        Finset.sum (E.erase j₁) (fun i ↦ x i • (Pi.single i (1 : ℝ) - Pi.single j₁ 1)) +
          Finset.sum (Finset.univ \ E) (fun i ↦ x i • Pi.single i 1) := by
    simpa [E] using sumZeroOnFinsetDecompose E hj₁E x hxsum
  have hinside_mem :
      Finset.sum (E.erase j₁) (fun i ↦ x i • (Pi.single i (1 : ℝ) - Pi.single j₁ 1)) ∈ D := by
    -- Inside `E(C)`, each anchored basis difference is either a cover direction or an
    -- extension direction.
    refine Submodule.sum_mem D ?_
    intro i hi
    have hi_ne_j₁ : i ≠ j₁ := (Finset.mem_erase.mp hi).1
    have hiE : i ∈ E := (Finset.mem_erase.mp hi).2
    have hgenerator :
        (Pi.single i (1 : ℝ) - Pi.single j₁ 1 : Fin n → ℝ) ∈ D := by
      by_cases hiC : i ∈ C
      · exact exercise79_coverDirection_mem a b C hC hj₁ hiC hi_ne_j₁
      · exact exercise79_extensionDirection_mem
          a b ha_desc C hC hj₁ hj₂ hj₁₂ (by simpa [E] using hiE) hiC hside₁
    exact Submodule.smul_mem D (x i) hgenerator
  have houtside_mem :
      Finset.sum (Finset.univ \ E) (fun i ↦ x i • Pi.single i 1) ∈ D := by
    -- Outside `E(C)`, the free coordinates are exactly the outside directions already packaged.
    refine Submodule.sum_mem D ?_
    intro i hi
    have hiE : i ∉ extended_cover a C := by
      simpa [E] using (Finset.mem_sdiff.mp hi).2
    exact Submodule.smul_mem D (x i)
      (exercise79_outsideDirection_mem a b ha_desc C hC hj₁ hiE hℓ_out hℓ_min hside₂)
  have hxmem : x ∈ D := by
    -- Assemble the kernel vector from the inside and outside generators.
    rw [hdecomp]
    exact Submodule.add_mem D hinside_mem houtside_mem
  simpa [D] using hxmem

/-- Exercise 7.9. The codimension count underlying part (1): under the two witness side
conditions, the exposed extended-cover face has affine-span direction of finrank `n - 1`. -/
theorem exercise79_extendedCoverFace_finrank
    [NeZero n]
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_pos : ∀ j, 0 < a j)
    (ha_le_b : ∀ j, a j ≤ b)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (j₁ j₂ ℓ : Fin n)
    (hj₁ : j₁ ∈ C)
    (hj₂ : j₂ ∈ C)
    (hj₁₂ : j₁ ≠ j₂)
    (hℓ_out : ℓ ∉ extended_cover a C)
    (hℓ_min : ∀ i : Fin n, i < ℓ → i ∈ extended_cover a C)
    (hside₁ : (((insert (0 : Fin n) C).erase j₁).erase j₂).sum a ≤ b)
    (hside₂ : ((insert ℓ C).erase j₁).sum a ≤ b) :
    Module.finrank ℝ (affineSpan ℝ (extended_cover_face a b C)).direction = n - 1 :=
by
  let _ := ha_pos
  let _ := ha_le_b
  let E : Finset (Fin n) := extended_cover a C
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductStrongDual (cover_indicator E)).toLinearMap
  have hdir_le :
      (affineSpan ℝ (extended_cover_face a b C)).direction ≤ LinearMap.ker L := by
    -- Every point on the equality face lies on the same exposed level set.
    simpa [L, E] using
      exercise79_faceDirection_le_dotProduct_ker
        (F := extended_cover_face a b C)
        (c := cover_indicator E)
        (x₀ := omitPoint C j₁)
        (δ := cover_inequality_rhs C)
        (exercise79_omitPoint_mem_extendedCoverFace a b C hC hj₁)
        (by
          intro x hx
          exact (mem_extended_cover_face_iff a b C x).mp hx |>.2)
  have hker_le :
      LinearMap.ker L ≤ (affineSpan ℝ (extended_cover_face a b C)).direction := by
    -- Route correction: use the explicit generator-based kernel inclusion rather than trying to
    -- prove the codimension count directly inside affine-span manipulations.
    simpa [L, E] using
      exercise79_extendedCoverFace_ker_le_direction
        a b ha_desc C hC j₁ j₂ ℓ hj₁ hj₂ hj₁₂ hℓ_out hℓ_min hside₁ hside₂
  have hdir_eq :
      (affineSpan ℝ (extended_cover_face a b C)).direction = LinearMap.ker L :=
    le_antisymm hdir_le hker_le
  have hj₁E : j₁ ∈ E := by
    simpa [E] using (mem_extended_cover_iff a C j₁).mpr (Or.inl hj₁)
  have hEval : L (Pi.single j₁ (1 : ℝ)) = 1 := by
    -- Evaluating on the pivot unit vector shows that the exposing functional is nonzero.
    calc
      L (Pi.single j₁ (1 : ℝ)) = cover_indicator E ⬝ᵥ Pi.single j₁ (1 : ℝ) := by
        simp [L, dotProductStrongDual_apply]
      _ = E.sum (Pi.single j₁ (1 : ℝ)) := by
        simpa using (coverIndicator_dot_eq_sum E (Pi.single j₁ (1 : ℝ)))
      _ = 1 := by
        simp [E, hj₁E]
  have hL_ne : L ≠ 0 := by
    intro hzero
    have hEvalZero : L (Pi.single j₁ (1 : ℝ)) = 0 := by
      simp [hzero]
    have : (1 : ℝ) = 0 := by
      rw [← hEval, hEvalZero]
    norm_num at this
  rw [hdir_eq]
  simpa [L] using exercise79_finrankKerEqCardSubOne (L := L) hL_ne

/-- Part (1) of Exercise 7.9. In the project's zero-based `Fin n` indexing, the textbook assumption
`b ≥ a₁ ≥ ⋯ ≥ aₙ > 0` is recorded as positivity together with `Antitone a`. If `C` is a minimal
cover, `j₁,j₂ ∈ C` are distinct, `ℓ` is the smallest index outside the extension `E(C)`, and the
two displayed side conditions hold, then the extended cover inequality
`∑_{j ∈ E(C)} x_j ≤ |C| - 1` defines a facet of `conv(K)`. -/
theorem exercise_7_9_extended_cover_inequality_facet
    [NeZero n]
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_pos : ∀ j, 0 < a j)
    (ha_le_b : ∀ j, a j ≤ b)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (j₁ j₂ ℓ : Fin n)
    (hj₁ : j₁ ∈ C)
    (hj₂ : j₂ ∈ C)
    (hj₁₂ : j₁ ≠ j₂)
    (hℓ_out : ℓ ∉ extended_cover a C)
    (hℓ_min : ∀ i : Fin n, i < ℓ → i ∈ extended_cover a C)
    (hside₁ : (((insert (0 : Fin n) C).erase j₁).erase j₂).sum a ≤ b)
    (hside₂ : ((insert ℓ C).erase j₁).sum a ≤ b) :
    IsFacetOf
      (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
      (extended_cover_face a b C) := by
  have hnonempty : (extended_cover_face a b C).Nonempty := by
    -- The omit-one cover point is a tight witness for the extended cover face.
    exact ⟨omitPoint C j₁, exercise79_omitPoint_mem_extendedCoverFace a b C hC hj₁⟩
  have hvalid :
      is_valid_inequality
        (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
        (cover_indicator (extended_cover a C))
        (cover_inequality_rhs C) :=
    exercise79_extendedCover_validOnKnapsackPolytope a b ha_pos ha_le_b ha_desc C hC
  have hexposed :
      IsExposed ℝ
        (zero_one_knapsack_polytope (fun i ↦ (a i : ℝ)) (b : ℝ))
        (extended_cover_face a b C) := by
    -- The extended cover face is the equality face of the valid inequality above.
    simpa [extended_cover_face] using isExposed_face_set_of_valid_inequality hvalid
  rw [isFacetOf_iff]
  refine ⟨hnonempty, hexposed, ?_⟩
  -- The remaining codimension-one count is delegated to the explicit rank lemmas.
  rw [exercise79_extendedCoverFace_finrank a b ha_pos ha_le_b ha_desc C hC j₁ j₂ ℓ hj₁ hj₂ hj₁₂
    hℓ_out hℓ_min hside₁ hside₂, exercise79_knapsackPolytope_finrank a b ha_le_b]
  omega

/-- Part (2) of Exercise 7.9. For a `0,1` knapsack set with `b ≥ a₁ ≥ ⋯ ≥ aₙ > 0`,
every extended cover inequality attached to a minimal cover admits a Chvatal presentation
for the natural formulation `a ⬝ᵥ x ≤ b, x ≤ 1, x ≥ 0`. -/
theorem exercise_7_9_extended_cover_inequality_is_chvatal
    (a : Fin n → ℕ)
    (b : ℕ)
    (ha_pos : ∀ j, 0 < a j)
    (ha_le_b : ∀ j, a j ≤ b)
    (ha_desc : Antitone a)
    (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C) :
    IsKnapsackChvatalPresentation
      a
      b
      (cover_indicator (extended_cover a C))
      (C.card - 1) := by
  let _ := ha_le_b
  have hC_cover : IsKnapsackCover a b C := inferInstance
  have hC_nonempty : C.Nonempty := by
    by_contra hC_empty
    rw [Finset.not_nonempty_iff_eq_empty] at hC_empty
    have hsum_gt : b < C.sum a := (isKnapsackCover_iff a b C).mp hC_cover
    simp [hC_empty] at hsum_gt
  rcases exercise79_exists_maxWeightPivot a C ha_desc hC_nonempty with ⟨h, hhC, hhmax⟩
  have hbase :
      IsKnapsackChvatalPresentation a b (exercise_7_8_chvatal_coeffs a C h) (C.card - 1) :=
    exercise_7_8_chvatal_inequality a b C hC h hhC hhmax
  refine
    knapsackChvatalPresentation_of_le
      a
      b
      (exercise_7_8_chvatal_coeffs a C h)
      (cover_indicator (extended_cover a C))
      (C.card - 1)
      hbase
      ?_
  -- Exercise 7.8 gives a stronger coefficient vector, so we may lower it to the extension
  -- indicator by increasing only the lower-bound multipliers.
  intro j
  exact exercise79_exercise78Coeff_ge_extendedCoverIndicator a C ha_pos hhC hhmax j

end Exercise79
