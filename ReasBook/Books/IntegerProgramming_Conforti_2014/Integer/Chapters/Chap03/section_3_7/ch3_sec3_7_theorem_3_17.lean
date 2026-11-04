/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_definition_3_7_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_remark_3_16
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_1.ch3_sec3_4_1_definition_3_4_1_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Domain sampling for this refine pass: Section 3.7’s owner subsystem is the row-restricted pair
-- `implicit_equality_matrix` / `implicit_equality_rhs`, built canonically from `Matrix.submatrix`;
-- mathlib provides the ambient owners `affineSpan` and `Matrix.rank`.

section

variable {m n : ℕ}
variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

local notation:max A "^=" => implicit_equality_matrix A b
local notation:max "b^=" => implicit_equality_rhs A b

/-- Helper for Theorem 3.17: every point of the affine hull of the polyhedron satisfies the
implicit equalities of the system. -/
lemma affineSpan_polyhedron_subset_implicit_equality_solution_set :
    (affineSpan ℝ (polyhedron_le_set A b) : Set (Fin n → ℝ)) ⊆
      {x : Fin n → ℝ | A^= *ᵥ x = b^=} := by
  intro x hx
  -- Induct over the affine span and keep the implicit-equality predicate stable.
  refine affineSpan_induction (k := ℝ) (s := polyhedron_le_set A b)
    (p := fun y : Fin n → ℝ ↦ A^= *ᵥ y = b^=) hx ?_ ?_
  · intro y hy
    -- Feasible points satisfy the implicit subsystem with equality by definition.
    have hy' :
        y ∈ {x : Fin n → ℝ |
          A^= *ᵥ x = b^= ∧
            remaining_inequality_matrix A b *ᵥ x ≤ remaining_inequality_rhs A b} := by
      simpa [polyhedron_le_set_eq_implicit_eq_and_remaining_subsystems A b] using hy
    exact hy'.1
  · intro c u v w hu hv hw
    -- The equality system is preserved by affine combinations.
    ext i
    have hu_i : (A^= *ᵥ u) i = b^= i := congrArg (fun f ↦ f i) hu
    have hv_i : (A^= *ᵥ v) i = b^= i := congrArg (fun f ↦ f i) hv
    have hw_i : (A^= *ᵥ w) i = b^= i := congrArg (fun f ↦ f i) hw
    calc
      (A^= *ᵥ (c • (u - v) + w)) i
          = c * ((A^= *ᵥ u) i - (A^= *ᵥ v) i) + (A^= *ᵥ w) i := by
              simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
      _ = c * (b^= i - b^= i) + b^= i := by rw [hu_i, hv_i, hw_i]
      _ = b^= i := by ring

/-- Helper for Theorem 3.17: a nonzero step from `xbar` toward `xhat` places `xhat` on the affine
line through `xbar` and the stepped point. -/
lemma mem_affineSpan_pair_of_nonzero_step
    (xbar xtilde xhat : Fin n → ℝ)
    {ε : ℝ}
    (hxtilde : xtilde = xbar + ε • (xhat - xbar))
    (hε : ε ≠ 0) :
    xhat ∈ affineSpan ℝ ({xbar, xtilde} : Set (Fin n → ℝ)) := by
  -- Rewrite `xhat` as the inverse-scaled step from `xbar` to `xtilde`.
  have hline_repr : ε⁻¹ • (xtilde - xbar) + xbar = xhat := by
    calc
      ε⁻¹ • (xtilde - xbar) + xbar
          = ε⁻¹ • ((xbar + ε • (xhat - xbar)) - xbar) + xbar := by rw [hxtilde]
      _ = ε⁻¹ • (ε • (xhat - xbar)) + xbar := by simp
      _ = (ε⁻¹ * ε) • (xhat - xbar) + xbar := by rw [smul_smul]
      _ = xhat := by
            rw [inv_mul_cancel₀ hε, one_smul]
            simpa [sub_eq_add_neg, add_assoc]
  rw [← hline_repr]
  simpa using smul_vsub_vadd_mem_affineSpan_pair (ε⁻¹) xbar xtilde

/-- Helper for Theorem 3.17: from a point that is strict on all remaining inequalities, one can
move a short positive distance toward any point satisfying the implicit inequalities and stay in
the original polyhedron. -/
lemma exists_small_step_mem_polyhedron_of_implicit_equality_inequality
    (xbar xhat : Fin n → ℝ)
    (hxbar : xbar ∈ polyhedron_le_set A b)
    (hstrict :
      ∀ i ∈ remaining_inequality_indices A b, (A *ᵥ xbar) i < b i)
    (hxhat : A^= *ᵥ xhat ≤ b^=) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ xbar + ε • (xhat - xbar) ∈ polyhedron_le_set A b := by
  classical
  by_cases hremaining : Nonempty {i // i ∈ remaining_inequality_indices A b}
  · let slack : {i // i ∈ remaining_inequality_indices A b} → ℝ :=
        fun i ↦ b i.1 - (A *ᵥ xbar) i.1
    let drift : {i // i ∈ remaining_inequality_indices A b} → ℝ :=
        fun i ↦ (A *ᵥ xhat) i.1 - (A *ᵥ xbar) i.1
    let bound : {i // i ∈ remaining_inequality_indices A b} → ℝ :=
        fun i ↦ if hpos : 0 < drift i then min 1 (slack i / drift i) else 1
    letI : Nonempty {i // i ∈ remaining_inequality_indices A b} := hremaining
    let ε : ℝ := Finset.univ.inf' Finset.univ_nonempty bound
    have hε_pos : 0 < ε := by
      -- Every row-wise bound is positive, so their finite infimum is positive.
      have hbound_pos : ∀ i : {i // i ∈ remaining_inequality_indices A b}, 0 < bound i := by
        intro i
        by_cases hpos : 0 < drift i
        · have hslack_pos : 0 < slack i := by
            dsimp [slack]
            linarith [hstrict i.1 i.2]
          have hratio_pos : 0 < slack i / drift i := by
            exact div_pos hslack_pos hpos
          dsimp [bound]
          rw [if_pos hpos]
          exact lt_min zero_lt_one hratio_pos
        · dsimp [bound]
          rw [if_neg hpos]
          norm_num
      dsimp [ε]
      exact (Finset.lt_inf'_iff _).2 fun i _ ↦ hbound_pos i
    have hε_le_one : ε ≤ 1 := by
      -- The chosen step length is bounded above by each row-wise admissible bound, hence by `1`.
      have hbound_le_one : ∀ i : {i // i ∈ remaining_inequality_indices A b}, bound i ≤ 1 := by
        intro i
        by_cases hpos : 0 < drift i
        · dsimp [bound]
          rw [if_pos hpos]
          exact min_le_left _ _
        · dsimp [bound]
          simpa [bound, hpos]
      have hε_le_bound :
          ∀ i : {i // i ∈ remaining_inequality_indices A b}, ε ≤ bound i := by
        intro i
        dsimp [ε]
        exact Finset.inf'_le _ (Finset.mem_univ i)
      have hε_le_one_row : ε ≤ bound (Classical.choice hremaining) := hε_le_bound _
      have hone : bound (Classical.choice hremaining) ≤ 1 := hbound_le_one _
      exact hε_le_one_row.trans hone
    refine ⟨ε, hε_pos, hε_le_one, ?_⟩
    -- Check each row directly, splitting into implicit and remaining inequalities.
    · change A *ᵥ (xbar + ε • (xhat - xbar)) ≤ b
      intro j
      by_cases hj : j ∈ implicit_equality_indices A b
      · have hxbar_eq_j : (A *ᵥ xbar) j = b j := by
          exact (mem_implicit_equality_indices_iff A b j).1 hj hxbar
        have hxhat_le_j : (A *ᵥ xhat) j ≤ b j := by
          simpa [implicit_equality_mulVec_apply, implicit_equality_rhs_apply] using hxhat ⟨j, hj⟩
        have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
        have hε_sub_nonneg : 0 ≤ 1 - ε := sub_nonneg.mpr hε_le_one
        calc
          (A *ᵥ (xbar + ε • (xhat - xbar))) j
              = (1 - ε) * (A *ᵥ xbar) j + ε * (A *ᵥ xhat) j := by
                  simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
                  ring
          _ = (1 - ε) * b j + ε * (A *ᵥ xhat) j := by rw [hxbar_eq_j]
          _ ≤ (1 - ε) * b j + ε * b j := by
                gcongr
          _ = b j := by ring
      · have hj' : j ∈ remaining_inequality_indices A b := hj
        let j' : {i // i ∈ remaining_inequality_indices A b} := ⟨j, hj'⟩
        have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
        have hε_le_bound : ε ≤ bound j' := by
          dsimp [ε]
          exact Finset.inf'_le _ (Finset.mem_univ j')
        have hslack_pos : 0 < slack j' := by
          dsimp [slack]
          linarith [hstrict j hj']
        have hdrift_case :
            ε * drift j' ≤ slack j' := by
          by_cases hpos : 0 < drift j'
          · have hbound_le_ratio : bound j' ≤ slack j' / drift j' := by
              dsimp [bound]
              rw [if_pos hpos]
              exact min_le_right _ _
            have hε_le_ratio : ε ≤ slack j' / drift j' := hε_le_bound.trans hbound_le_ratio
            calc
              ε * drift j' ≤ (slack j' / drift j') * drift j' := by
                exact mul_le_mul_of_nonneg_right hε_le_ratio hpos.le
              _ = slack j' := by
                field_simp [ne_of_gt hpos]
          · have hle : drift j' ≤ 0 := le_of_not_gt hpos
            have hmul_nonpos : ε * drift j' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε_nonneg hle
            exact hmul_nonpos.trans hslack_pos.le
        have hrow_eval :
            (A *ᵥ (xbar + ε • (xhat - xbar))) j = (A *ᵥ xbar) j + ε * drift j' := by
          dsimp [j', drift]
          simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
        calc
          (A *ᵥ (xbar + ε • (xhat - xbar))) j
              = (A *ᵥ xbar) j + ε * drift j' := hrow_eval
          _ ≤ (A *ᵥ xbar) j + slack j' := by gcongr
          _ = b j := by
                dsimp [j', slack]
                ring
  · have hremaining_empty :
        remaining_inequality_indices A b = (∅ : Set (Fin m)) := by
      ext i
      constructor
      · intro hi
        exact False.elim (hremaining ⟨i, hi⟩)
      · intro hi
        simp at hi
    have h_one_pos : 0 < (1 : ℝ) := by
      norm_num
    refine ⟨1, h_one_pos, le_rfl, ?_⟩
    -- With no remaining inequalities, the implicit subsystem alone defines the polyhedron.
    rw [polyhedron_le_set_eq_implicit_and_remaining_subsystems A b]
    constructor
    · simpa using hxhat
    · intro i
      have : False := by
        simpa [hremaining_empty] using i.2
      exact False.elim this

/-- Helper for Theorem 3.17: when the polyhedron is nonempty, every point satisfying the implicit
inequalities already lies in the affine hull of the polyhedron. -/
lemma implicit_equality_inequality_set_subset_affineSpan_of_nonempty
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    {x : Fin n → ℝ | A^= *ᵥ x ≤ b^=} ⊆
      (affineSpan ℝ (polyhedron_le_set A b) : Set (Fin n → ℝ)) := by
  intro xhat hxhat
  rcases exists_mem_polyhedron_le_set_strict_on_remaining_inequality_indices A b h_nonempty with
    ⟨xbar, hxbar, hstrict⟩
  rcases
      exists_small_step_mem_polyhedron_of_implicit_equality_inequality A b xbar xhat hxbar
        hstrict hxhat with
    ⟨ε, hε_pos, hε_le_one, hxtilde_mem⟩
  have hline :
      xhat ∈ affineSpan ℝ ({xbar, xbar + ε • (xhat - xbar)} : Set (Fin n → ℝ)) := by
    -- The source proof uses the whole line through the base point and the stepped feasible point.
    refine mem_affineSpan_pair_of_nonzero_step xbar (xbar + ε • (xhat - xbar)) xhat rfl ?_
    exact ne_of_gt hε_pos
  have hpair_subset :
      ({xbar, xbar + ε • (xhat - xbar)} : Set (Fin n → ℝ)) ⊆ polyhedron_le_set A b := by
    intro y hy
    rcases hy with rfl | rfl
    · exact hxbar
    · exact hxtilde_mem
  exact affineSpan_mono ℝ hpair_subset hline

/-- Helper for Theorem 3.17: once a feasible base point is fixed, the implicit-equality solution
set is the translate of the kernel of the implicit subsystem through that point. -/
lemma implicit_equality_solution_set_eq_point_translate_ker
    (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ polyhedron_le_set A b) :
    {x : Fin n → ℝ | A^= *ᵥ x = b^=} =
      (AffineSubspace.mk' x0 (LinearMap.ker (A^=).mulVecLin) : Set (Fin n → ℝ)) := by
  have hx0_eq : A^= *ᵥ x0 = b^= := by
    have hx0' :
        x0 ∈ {x : Fin n → ℝ |
          A^= *ᵥ x = b^= ∧
            remaining_inequality_matrix A b *ᵥ x ≤ remaining_inequality_rhs A b} := by
      simpa [polyhedron_le_set_eq_implicit_eq_and_remaining_subsystems A b] using hx0
    exact hx0'.1
  ext x
  constructor
  · intro hx
    -- Equal right-hand sides imply that the difference lies in the kernel.
    change x - x0 ∈ LinearMap.ker (A^=).mulVecLin
    rw [LinearMap.mem_ker]
    have hsub : A^= *ᵥ x - A^= *ᵥ x0 = 0 := by
      rw [hx, hx0_eq, sub_self]
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_sub] using hsub
  · intro hx
    -- Conversely, a kernel displacement preserves the implicit-equality image.
    change x - x0 ∈ LinearMap.ker (A^=).mulVecLin at hx
    rw [LinearMap.mem_ker] at hx
    have hsub : A^= *ᵥ x - A^= *ᵥ x0 = 0 := by
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_sub] using hx
    have himage : A^= *ᵥ x = A^= *ᵥ x0 := sub_eq_zero.mp hsub
    change A^= *ᵥ x = b^=
    rw [himage, hx0_eq]

/-- Theorem 3.17 (1). The affine hull of the polyhedron `P = {x | A *ᵥ x ≤ b}` is exactly the
solution set of the implicit equalities `A^= x = b^=`. -/
theorem affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set
    :
    (affineSpan ℝ (polyhedron_le_set A b) : Set (Fin n → ℝ)) =
      {x : Fin n → ℝ | A^= *ᵥ x = b^=} := by
  by_cases h_nonempty : Set.Nonempty (polyhedron_le_set A b)
  · apply Set.Subset.antisymm
    · -- The affine hull cannot leave the implicit-equality hyperplanes.
      exact affineSpan_polyhedron_subset_implicit_equality_solution_set A b
    · intro x hx
      -- In the nonempty case, the source line argument upgrades equality solutions to affine-hull
      -- membership through the inequality formulation.
      apply implicit_equality_inequality_set_subset_affineSpan_of_nonempty A b h_nonempty
      intro i
      have hi : (A^= *ᵥ x) i = b^= i := by
        simpa using congrArg (fun f ↦ f i) hx
      exact le_of_eq hi
  · have hP : polyhedron_le_set A b = (∅ : Set (Fin n → ℝ)) :=
      Set.not_nonempty_iff_eq_empty.mp h_nonempty
    have hremaining_empty :
        remaining_inequality_indices A b = (∅ : Set (Fin m)) :=
      remaining_inequality_indices_eq_empty_of_polyhedron_le_set_eq_empty A b hP
    have hremaining_eq_vacuous :
        {x : Fin n → ℝ |
            A^= *ᵥ x = b^= ∧
              remaining_inequality_matrix A b *ᵥ x ≤ remaining_inequality_rhs A b} =
          ({x : Fin n → ℝ | A^= *ᵥ x = b^=} : Set (Fin n → ℝ)) := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        constructor
        · exact hx
        · intro i
          have : False := by
            simpa [hremaining_empty] using i.2
          exact this.elim
    have hpoly_eq_implicit :
        polyhedron_le_set A b = ({x : Fin n → ℝ | A^= *ᵥ x = b^=} : Set (Fin n → ℝ)) := by
      rw [polyhedron_le_set_eq_implicit_eq_and_remaining_subsystems A b, hremaining_eq_vacuous]
    have himplicit_empty :
        ({x : Fin n → ℝ | A^= *ᵥ x = b^=} : Set (Fin n → ℝ)) = ∅ := by
      -- When the polyhedron is empty, the implicit-equality subsystem is empty as well.
      calc
        ({x : Fin n → ℝ | A^= *ᵥ x = b^=} : Set (Fin n → ℝ)) = polyhedron_le_set A b := by
          symm
          exact hpoly_eq_implicit
        _ = ∅ := hP
    -- The affine span of the empty set is empty, so both sides coincide.
    simpa [hP, himplicit_empty]

/-- Theorem 3.17 (2). The implicit-equality subsystem cuts out the same set whether it is
written as equations `A^= x = b^=` or as inequalities `A^= x ≤ b^=`. -/
theorem implicit_equality_solution_set_eq_implicit_equality_inequality_set
    :
    {x : Fin n → ℝ | A^= *ᵥ x = b^=} =
      {x : Fin n → ℝ | A^= *ᵥ x ≤ b^=} := by
  by_cases h_nonempty : Set.Nonempty (polyhedron_le_set A b)
  · apply Set.Subset.antisymm
    · intro x hx
      intro i
      have hi : (A^= *ᵥ x) i = b^= i := by
        simpa using congrArg (fun f ↦ f i) hx
      exact le_of_eq hi
    · intro x hx
      have hx_aff :
          x ∈ (affineSpan ℝ (polyhedron_le_set A b) : Set (Fin n → ℝ)) :=
        implicit_equality_inequality_set_subset_affineSpan_of_nonempty A b h_nonempty hx
      exact affineSpan_polyhedron_subset_implicit_equality_solution_set A b hx_aff
  · have hP : polyhedron_le_set A b = (∅ : Set (Fin n → ℝ)) :=
      Set.not_nonempty_iff_eq_empty.mp h_nonempty
    have hremaining_empty :
        remaining_inequality_indices A b = (∅ : Set (Fin m)) :=
      remaining_inequality_indices_eq_empty_of_polyhedron_le_set_eq_empty A b hP
    have hremaining_eq_vacuous :
        {x : Fin n → ℝ |
            A^= *ᵥ x = b^= ∧
              remaining_inequality_matrix A b *ᵥ x ≤ remaining_inequality_rhs A b} =
          ({x : Fin n → ℝ | A^= *ᵥ x = b^=} : Set (Fin n → ℝ)) := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        constructor
        · exact hx
        · intro i
          have : False := by
            simpa [hremaining_empty] using i.2
          exact this.elim
    have hremaining_le_vacuous :
        {x : Fin n → ℝ |
            A^= *ᵥ x ≤ b^= ∧
              remaining_inequality_matrix A b *ᵥ x ≤ remaining_inequality_rhs A b} =
          ({x : Fin n → ℝ | A^= *ᵥ x ≤ b^=} : Set (Fin n → ℝ)) := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        constructor
        · exact hx
        · intro i
          have : False := by
            simpa [hremaining_empty] using i.2
          exact this.elim
    have hpoly_eq_implicit_eq :
        polyhedron_le_set A b = ({x : Fin n → ℝ | A^= *ᵥ x = b^=} : Set (Fin n → ℝ)) := by
      rw [polyhedron_le_set_eq_implicit_eq_and_remaining_subsystems A b, hremaining_eq_vacuous]
    have hpoly_eq_implicit_le :
        polyhedron_le_set A b = ({x : Fin n → ℝ | A^= *ᵥ x ≤ b^=} : Set (Fin n → ℝ)) := by
      rw [polyhedron_le_set_eq_implicit_and_remaining_subsystems A b, hremaining_le_vacuous]
    have himplicit_eq_empty :
        ({x : Fin n → ℝ | A^= *ᵥ x = b^=} : Set (Fin n → ℝ)) = ∅ := by
      calc
        ({x : Fin n → ℝ | A^= *ᵥ x = b^=} : Set (Fin n → ℝ)) = polyhedron_le_set A b := by
          symm
          exact hpoly_eq_implicit_eq
        _ = ∅ := hP
    have himplicit_le_empty :
        ({x : Fin n → ℝ | A^= *ᵥ x ≤ b^=} : Set (Fin n → ℝ)) = ∅ := by
      calc
        ({x : Fin n → ℝ | A^= *ᵥ x ≤ b^=} : Set (Fin n → ℝ)) = polyhedron_le_set A b := by
          symm
          exact hpoly_eq_implicit_le
        _ = ∅ := hP
    simpa [himplicit_eq_empty, himplicit_le_empty]

/-- Helper for Theorem 3.17: every direction vector of the affine hull annihilates the
implicit-equality subsystem. -/
lemma mem_direction_affineSpan_subset_kernel_implicit_equalities
    (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ polyhedron_le_set A b) :
    (affineSpan ℝ (polyhedron_le_set A b)).direction ≤ LinearMap.ker (A^=).mulVecLin := by
  have hx0_aff : x0 ∈ affineSpan ℝ (polyhedron_le_set A b) :=
    subset_affineSpan ℝ (polyhedron_le_set A b) hx0
  have hx0_eq : A^= *ᵥ x0 = b^= :=
    affineSpan_polyhedron_subset_implicit_equality_solution_set A b hx0_aff
  -- Route correction: convert a direction into a right-difference from `x0`.
  intro v hv
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff] at hv
  rw [LinearMap.mem_ker]
  rcases hv with ⟨x, hxAff, rfl⟩
  have hx_eq : A^= *ᵥ x = b^= :=
    affineSpan_polyhedron_subset_implicit_equality_solution_set A b hxAff
  have hsub : A^= *ᵥ x - A^= *ᵥ x0 = 0 := by
    rw [hx_eq, hx0_eq, sub_self]
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_sub] using hsub

/-- Helper for Theorem 3.17: every kernel vector of the implicit-equality subsystem gives a
direction of the affine hull when translated from a feasible base point `x0`. -/
lemma kernel_implicit_equalities_subset_direction_affineSpan
    (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ polyhedron_le_set A b) :
    LinearMap.ker (A^=).mulVecLin ≤ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
  have hx0_aff : x0 ∈ affineSpan ℝ (polyhedron_le_set A b) :=
    subset_affineSpan ℝ (polyhedron_le_set A b) hx0
  -- Route correction: translate the kernel vector to a point, then return via the equality-set
  -- characterization of the affine hull.
  intro v hv
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff]
  rw [LinearMap.mem_ker] at hv
  let x : Fin n → ℝ := v + x0
  have hx_mk :
      x ∈ (AffineSubspace.mk' x0 (LinearMap.ker (A^=).mulVecLin) : Set (Fin n → ℝ)) := by
    simpa [x] using
      (AffineSubspace.vadd_mem_mk' (direction := LinearMap.ker (A^=).mulVecLin) x0 hv)
  have hx_eq :
      x ∈ ({x : Fin n → ℝ | A^= *ᵥ x = b^=} : Set (Fin n → ℝ)) := by
    rw [implicit_equality_solution_set_eq_point_translate_ker A b x0 hx0]
    exact hx_mk
  have hx_aff :
      x ∈ (affineSpan ℝ (polyhedron_le_set A b) : Set (Fin n → ℝ)) := by
    rw [affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set A b]
    exact hx_eq
  refine ⟨x, hx_aff, ?_⟩
  change v = x - x0
  dsimp [x]
  abel

/-- Theorem 3.17 (3). If the polyhedron `P = {x | A *ᵥ x ≤ b}` is nonempty, then its affine
dimension is the ambient dimension minus the rank of the implicit-equality matrix `A^=`. -/
theorem finrank_direction_affineSpan_eq_ambient_sub_rank_implicit_equalities
    (h_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction =
      n - (A^=).rank := by
  rcases h_nonempty with ⟨x0, hx0⟩
  let Aeq : Matrix {i // i ∈ implicit_equality_indices A b} (Fin n) ℝ := A^=
  have hdir_le_ker :
      Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction ≤
        Module.finrank ℝ (LinearMap.ker (A^=).mulVecLin) :=
    Submodule.finrank_mono
      (mem_direction_affineSpan_subset_kernel_implicit_equalities A b x0 hx0)
  have hker_le_dir :
      Module.finrank ℝ (LinearMap.ker (A^=).mulVecLin) ≤
        Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction :=
    Submodule.finrank_mono
      (kernel_implicit_equalities_subset_direction_affineSpan A b x0 hx0)
  calc
    Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction
        = Module.finrank ℝ (LinearMap.ker Aeq.mulVecLin) := by
            exact le_antisymm hdir_le_ker hker_le_dir
    _ = n - Aeq.rank := by
          simpa using finrank_matrix_kernel_eq_card_sub_rank Aeq
    _ = n - (A^=).rank := by
          rfl

end
