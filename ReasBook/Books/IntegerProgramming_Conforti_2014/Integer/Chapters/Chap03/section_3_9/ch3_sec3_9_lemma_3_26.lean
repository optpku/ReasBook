/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_theorem_3_17
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_24
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25

open scoped Matrix

/- Lemma 3.26 works with the singleton specialization of the Chapter 3 owner
`active_constraint_face A b I`; no parallel singleton-face wrapper is needed here.
This file is also the source-facing owner of the Section 3.9 row-irredundancy predicate used
again in Theorem 3.27. -/

section Lemma_3_26

variable {m n : ℕ}
variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin m)

local notation:max A "^=" => implicit_equality_matrix A b
local notation:max "b^=" => implicit_equality_rhs A b

/-- A row `j` of the system `A *ᵥ x ≤ b` is irredundant if removing that row strictly enlarges
the feasible set. -/
def is_irredundant_row : Prop :=
  ∃ x : Fin n → ℝ,
    (∀ i : Fin m, i ≠ j → (A *ᵥ x) i ≤ b i) ∧
      b j < (A *ᵥ x) j

/-- Helper for Lemma 3.26: from a point of the singleton active face that is strict on every
other non-implicit row, one can move a short positive distance toward any point satisfying the
row-`j` equality and all implicit equalities while staying in the same face. -/
lemma exists_small_step_mem_active_constraint_face_singleton_of_row_eq_and_implicit_eq
    (xbar xhat : Fin n → ℝ)
    (hxbar : xbar ∈ active_constraint_face A b ({j} : Set (Fin m)))
    (hstrict :
      ∀ i : Fin m,
        i ≠ j →
          ¬ is_implicit_equality A b i →
            (A *ᵥ xbar) i < b i)
    (hxhat_row : (A *ᵥ xhat) j = b j)
    (hxhat_implicit :
      ∀ i : Fin m, is_implicit_equality A b i → (A *ᵥ xhat) i = b i) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε ≤ 1 ∧
          xbar + ε • (xhat - xbar) ∈ active_constraint_face A b ({j} : Set (Fin m)) := by
  classical
  by_cases hremaining : Nonempty {i // i ∈ remaining_inequality_indices A b ∧ i ≠ j}
  · let slack : {i // i ∈ remaining_inequality_indices A b ∧ i ≠ j} → ℝ :=
        fun i ↦ b i.1 - (A *ᵥ xbar) i.1
    let drift : {i // i ∈ remaining_inequality_indices A b ∧ i ≠ j} → ℝ :=
        fun i ↦ (A *ᵥ xhat) i.1 - (A *ᵥ xbar) i.1
    let bound : {i // i ∈ remaining_inequality_indices A b ∧ i ≠ j} → ℝ :=
        fun i ↦ if hpos : 0 < drift i then min 1 (slack i / drift i) else 1
    letI : Nonempty {i // i ∈ remaining_inequality_indices A b ∧ i ≠ j} := hremaining
    let ε : ℝ := Finset.univ.inf' Finset.univ_nonempty bound
    have hε_pos : 0 < ε := by
      -- Every rowwise admissible bound is positive, so the chosen infimum is positive too.
      have hbound_pos :
          ∀ i : {i // i ∈ remaining_inequality_indices A b ∧ i ≠ j}, 0 < bound i := by
        intro i
        by_cases hpos : 0 < drift i
        · have hslack_pos : 0 < slack i := by
            have hrow :
                (A *ᵥ xbar) i.1 < b i.1 :=
              hstrict i.1 i.2.2 ((mem_remaining_inequality_indices_iff A b i.1).1 i.2.1)
            dsimp [slack]
            linarith
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
      -- The chosen step is bounded above by every admissible rowwise bound, hence by `1`.
      have hbound_le_one :
          ∀ i : {i // i ∈ remaining_inequality_indices A b ∧ i ≠ j}, bound i ≤ 1 := by
        intro i
        by_cases hpos : 0 < drift i
        · dsimp [bound]
          rw [if_pos hpos]
          exact min_le_left _ _
        · dsimp [bound]
          simp [hpos]
      have hε_le_bound :
          ∀ i : {i // i ∈ remaining_inequality_indices A b ∧ i ≠ j}, ε ≤ bound i := by
        intro i
        dsimp [ε]
        exact Finset.inf'_le _ (Finset.mem_univ i)
      have hε_le_one_row : ε ≤ bound (Classical.choice hremaining) := hε_le_bound _
      exact hε_le_one_row.trans (hbound_le_one _)
    refine ⟨ε, hε_pos, hε_le_one, ?_⟩
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      have hij : i = j := by simpa using hi
      -- The row `j` equation is preserved because both endpoints already satisfy it.
      have hrow_combo :
          (A *ᵥ (xbar + ε • (xhat - xbar))) i =
            (1 - ε) * (A *ᵥ xbar) i + ε * (A *ᵥ xhat) i := by
        simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
        ring
      have hxbar_row : (A *ᵥ xbar) i = b i := by
        simpa [hij] using (mem_active_constraint_face_iff.mp hxbar).1 j (by simp)
      have hxhat_row_i : (A *ᵥ xhat) i = b i := by
        simpa [hij] using hxhat_row
      calc
        (A *ᵥ (xbar + ε • (xhat - xbar))) i
            = (1 - ε) * (A *ᵥ xbar) i + ε * (A *ᵥ xhat) i := hrow_combo
        _ = (1 - ε) * b i + ε * b i := by rw [hxbar_row, hxhat_row_i]
        _ = b i := by ring
    · intro i hi
      have hij : i ≠ j := by
        intro hij
        exact hi (by simp [hij])
      by_cases hi_implicit : is_implicit_equality A b i
      · -- Implicit rows stay on their defining hyperplane throughout the step.
        have hxbar_poly : xbar ∈ polyhedron_le_set A b :=
          mem_polyhedron_of_mem_active_constraint_face hxbar
        have hxbar_eq : (A *ᵥ xbar) i = b i := hi_implicit hxbar_poly
        have hrow_combo :
            (A *ᵥ (xbar + ε • (xhat - xbar))) i =
              (1 - ε) * (A *ᵥ xbar) i + ε * (A *ᵥ xhat) i := by
          simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
          ring
        calc
          (A *ᵥ (xbar + ε • (xhat - xbar))) i
              = (1 - ε) * (A *ᵥ xbar) i + ε * (A *ᵥ xhat) i := hrow_combo
          _ = (1 - ε) * b i + ε * b i := by rw [hxbar_eq, hxhat_implicit i hi_implicit]
          _ = b i := by ring
          _ ≤ b i := le_rfl
      · let i' : {i // i ∈ remaining_inequality_indices A b ∧ i ≠ j} :=
          ⟨i, (mem_remaining_inequality_indices_iff A b i).2 hi_implicit, hij⟩
        have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
        have hstrict_i : (A *ᵥ xbar) i < b i := hstrict i hij hi_implicit
        have hdrift_case :
            ε * drift i' ≤ slack i' := by
          have hε_le_bound : ε ≤ bound i' := by
            dsimp [ε]
            exact Finset.inf'_le _ (Finset.mem_univ i')
          by_cases hpos : 0 < drift i'
          · have hbound_le_ratio : bound i' ≤ slack i' / drift i' := by
              dsimp [bound]
              rw [if_pos hpos]
              exact min_le_right _ _
            have hε_le_ratio : ε ≤ slack i' / drift i' :=
              hε_le_bound.trans hbound_le_ratio
            calc
              ε * drift i' ≤ (slack i' / drift i') * drift i' := by
                exact mul_le_mul_of_nonneg_right hε_le_ratio hpos.le
              _ = slack i' := by
                field_simp [ne_of_gt hpos]
          · have hle : drift i' ≤ 0 := le_of_not_gt hpos
            have hslack_pos : 0 < slack i' := by
              dsimp [slack]
              linarith
            have hmul_nonpos : ε * drift i' ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hε_nonneg hle
            exact hmul_nonpos.trans hslack_pos.le
        have hrow_eval :
            (A *ᵥ (xbar + ε • (xhat - xbar))) i = (A *ᵥ xbar) i + ε * drift i' := by
          dsimp [i', drift]
          simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
        calc
          (A *ᵥ (xbar + ε • (xhat - xbar))) i
              = (A *ᵥ xbar) i + ε * drift i' := hrow_eval
          _ ≤ (A *ᵥ xbar) i + slack i' := by gcongr
          _ = b i := by
                dsimp [i', slack]
                ring
  · have h_one_pos : 0 < (1 : ℝ) := by norm_num
    refine ⟨1, h_one_pos, le_rfl, ?_⟩
    -- If there are no other remaining inequalities, the target point itself already lies in the
    -- singleton face.
    have hstep_eq : xbar + (1 : ℝ) • (xhat - xbar) = xhat := by
      simp [sub_eq_add_neg]
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      have hij : i = j := by simpa using hi
      rw [hstep_eq]
      simpa [hij] using hxhat_row
    · intro i hi
      have hij : i ≠ j := by
        intro hij
        exact hi (by simp [hij])
      have hi_implicit : is_implicit_equality A b i := by
        by_contra hi_not_implicit
        have hi_remaining : i ∈ remaining_inequality_indices A b :=
          (mem_remaining_inequality_indices_iff A b i).2 hi_not_implicit
        exact hremaining ⟨i, hi_remaining, hij⟩
      rw [hstep_eq]
      exact le_of_eq (hxhat_implicit i hi_implicit)

omit A b j in
/-- Helper for Lemma 3.26: if a linear functional evaluates to `1` on some vector of a
submodule `D`, then intersecting `D` with its kernel lowers the finrank by exactly one. -/
lemma finrank_inf_ker_add_one_of_eval_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (D : Submodule ℝ E) (L : E →ₗ[ℝ] ℝ) {w : E}
    (hwD : w ∈ D) (hw : L w = 1) :
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
  have hne : L.domRestrict D ≠ 0 := by
    -- Evaluating the restricted map at `w` rules out the zero map.
    intro hzero
    have hvalue := congrArg (fun f : D →ₗ[ℝ] ℝ ↦ f ⟨w, hwD⟩) hzero
    simp [LinearMap.domRestrict_apply, hw] at hvalue
  have hdim :
      Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 =
        Module.finrank ℝ ↥D := by
    simpa using Module.Dual.finrank_ker_add_one_of_ne_zero (f := L.domRestrict D) hne
  have hmap :
      (LinearMap.ker (L.domRestrict D)).map D.subtype = D ⊓ LinearMap.ker L := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  have hfin :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) =
        Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) := by
    -- The subtype embedding identifies the restricted kernel with the ambient intersection.
    rw [← hmap]
    exact
      Submodule.finrank_map_subtype_eq (R := ℝ) (p := D)
        (q := LinearMap.ker (L.domRestrict D))
  calc
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1
        = Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 := by
            rw [hfin]
    _ = Module.finrank ℝ ↥D := hdim

/-- Part (i) of Lemma 3.26. If `P = polyhedron_le_set A b` is nonempty and row `j` is
irredundant, then the singleton active-constraint face contains a point where every other
non-implicit row is
strict. -/
theorem exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
    (h_nonempty : (polyhedron_le_set A b).Nonempty)
    (hj_irredundant : is_irredundant_row A b j) :
    ∃ xhat ∈ active_constraint_face A b ({j} : Set (Fin m)),
      ∀ i : Fin m,
        i ≠ j →
          ¬ is_implicit_equality A b i →
            (A *ᵥ xhat) i < b i := by
  by_cases hj_implicit : is_implicit_equality A b j
  · rcases exists_mem_polyhedron_le_set_strict_on_remaining_inequality_indices A b h_nonempty with
      ⟨xbar, hxbar, hbar_strict⟩
    have hxbar_face : xbar ∈ active_constraint_face A b ({j} : Set (Fin m)) := by
      refine (mem_active_constraint_face_iff).2 ?_
      constructor
      · intro i hi
        have hij : i = j := by simpa using hi
        simpa [hij] using hj_implicit hxbar
      · intro i hi
        exact hxbar i
    refine ⟨xbar, hxbar_face, ?_⟩
    intro i hij hi_not_implicit
    -- The strict point from Remark 3.16 already works because `j` is implicit.
    exact hbar_strict i ((mem_remaining_inequality_indices_iff A b i).2 hi_not_implicit)
  · rcases exists_mem_polyhedron_le_set_strict_on_remaining_inequality_indices A b h_nonempty with
      ⟨xbar, hxbar, hbar_strict⟩
    rcases hj_irredundant with ⟨xtilde, hxtilde_le, hxtilde_j_gt⟩
    let denom : ℝ := (A *ᵥ xtilde) j - (A *ᵥ xbar) j
    let t : ℝ := (b j - (A *ᵥ xbar) j) / denom
    let xhat : Fin n → ℝ := xbar + t • (xtilde - xbar)
    have hj_remaining : j ∈ remaining_inequality_indices A b :=
      (mem_remaining_inequality_indices_iff A b j).2 hj_implicit
    have hxbar_j_lt : (A *ᵥ xbar) j < b j := hbar_strict j hj_remaining
    have hdenom_pos : 0 < denom := by
      dsimp [denom]
      linarith
    have ht_pos : 0 < t := by
      dsimp [t]
      exact div_pos (sub_pos.mpr hxbar_j_lt) hdenom_pos
    have ht_lt_one : t < 1 := by
      have hnum_lt_denom : b j - (A *ᵥ xbar) j < denom := by
        dsimp [denom]
        linarith
      have hdiv : t < denom / denom := by
        dsimp [t]
        exact div_lt_div_of_pos_right hnum_lt_denom hdenom_pos
      simpa [hdenom_pos.ne'] using hdiv
    have ht_le_one : t ≤ 1 := le_of_lt ht_lt_one
    have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
    have h_one_sub_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht_le_one
    have h_one_sub_pos : 0 < 1 - t := sub_pos.mpr ht_lt_one
    have hrow_combo (i : Fin m) :
        (A *ᵥ xhat) i = (1 - t) * (A *ᵥ xbar) i + t * (A *ᵥ xtilde) i := by
      dsimp [xhat]
      simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
      ring
    have hmul_t_denom : t * denom = b j - (A *ᵥ xbar) j := by
      dsimp [t]
      field_simp [ne_of_gt hdenom_pos]
    have hxhat_face : xhat ∈ active_constraint_face A b ({j} : Set (Fin m)) := by
      refine (mem_active_constraint_face_iff).2 ?_
      constructor
      · intro i hi
        have hij : i = j := by simpa using hi
        -- The interpolation parameter is chosen so that row `j` lands exactly on `b j`.
        calc
          (A *ᵥ xhat) i = (1 - t) * (A *ᵥ xbar) i + t * (A *ᵥ xtilde) i := hrow_combo i
          _ = (A *ᵥ xbar) i + t * ((A *ᵥ xtilde) i - (A *ᵥ xbar) i) := by ring
          _ = (A *ᵥ xbar) i + (b j - (A *ᵥ xbar) j) := by
                simpa [hij, denom] using
                  congrArg (fun z : ℝ ↦ (A *ᵥ xbar) i + z) hmul_t_denom
          _ = b i := by
                subst hij
                ring
      · intro i hi
        have hij : i ≠ j := by
          intro hij
          exact hi (by simp [hij])
        by_cases hi_implicit : is_implicit_equality A b i
        · have hxbar_eq : (A *ᵥ xbar) i = b i := hi_implicit hxbar
          have hxtilde_le_i : (A *ᵥ xtilde) i ≤ b i := hxtilde_le i hij
          calc
            (A *ᵥ xhat) i = (1 - t) * (A *ᵥ xbar) i + t * (A *ᵥ xtilde) i := hrow_combo i
            _ ≤ (1 - t) * b i + t * b i := by
                  rw [hxbar_eq]
                  gcongr
            _ = b i := by ring
        · have hxbar_lt : (A *ᵥ xbar) i < b i :=
            hbar_strict i ((mem_remaining_inequality_indices_iff A b i).2 hi_implicit)
          have hxtilde_le_i : (A *ᵥ xtilde) i ≤ b i := hxtilde_le i hij
          calc
            (A *ᵥ xhat) i = (1 - t) * (A *ᵥ xbar) i + t * (A *ᵥ xtilde) i := hrow_combo i
            _ ≤ (1 - t) * b i + t * b i := by
                  have hleft : (1 - t) * (A *ᵥ xbar) i ≤ (1 - t) * b i :=
                    (mul_le_mul_of_nonneg_left hxbar_lt.le h_one_sub_nonneg)
                  have hright : t * (A *ᵥ xtilde) i ≤ t * b i :=
                    mul_le_mul_of_nonneg_left hxtilde_le_i ht_nonneg
                  linarith
            _ = b i := by ring
    refine ⟨xhat, hxhat_face, ?_⟩
    intro i hij hi_not_implicit
    have hxtilde_le_i : (A *ᵥ xtilde) i ≤ b i := hxtilde_le i hij
    have hxbar_lt : (A *ᵥ xbar) i < b i :=
      hbar_strict i ((mem_remaining_inequality_indices_iff A b i).2 hi_not_implicit)
    -- Strictness persists because `xbar` is already strict and the step length satisfies `t < 1`.
    calc
      (A *ᵥ xhat) i = (1 - t) * (A *ᵥ xbar) i + t * (A *ᵥ xtilde) i := hrow_combo i
      _ < (1 - t) * b i + t * b i := by
            have hleft : (1 - t) * (A *ᵥ xbar) i < (1 - t) * b i :=
              mul_lt_mul_of_pos_left hxbar_lt h_one_sub_pos
            have hright : t * (A *ᵥ xtilde) i ≤ t * b i :=
              mul_le_mul_of_nonneg_left hxtilde_le_i ht_nonneg
            linarith
      _ = b i := by ring

/-- Part (ii) of Lemma 3.26. If `P = polyhedron_le_set A b` is nonempty and row `j` is
irredundant, then the affine hull of the face where row `j` is active is cut out exactly by the
implicit equalities together with the equation for row `j`. -/
theorem affineSpan_active_constraint_face_singleton_eq_implicit_equalities_and_row
    (h_nonempty : (polyhedron_le_set A b).Nonempty)
    (hj_irredundant : is_irredundant_row A b j) :
    affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m))) =
      {x : Fin n → ℝ |
        (A *ᵥ x) j = b j ∧
          ∀ i : Fin m, is_implicit_equality A b i → (A *ᵥ x) i = b i} := by
  by_cases hj_implicit : is_implicit_equality A b j
  · have hface_eq :
        active_constraint_face A b ({j} : Set (Fin m)) = polyhedron_le_set A b := by
      ext x
      constructor
      · intro hx
        exact mem_polyhedron_of_mem_active_constraint_face hx
      · intro hx
        refine (mem_active_constraint_face_iff).2 ?_
        constructor
        · intro i hi
          have hij : i = j := by simpa using hi
          simpa [hij] using hj_implicit hx
        · intro i hi
          exact hx i
    -- When row `j` is implicit, activating it does not change the polyhedron.
    calc
      (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m))) : Set (Fin n → ℝ))
          = affineSpan ℝ (polyhedron_le_set A b) := by rw [hface_eq]
      _ = {x : Fin n → ℝ | A^= *ᵥ x = b^=} := by
            rw [affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set A b]
      _ = {x : Fin n → ℝ |
            (A *ᵥ x) j = b j ∧
              ∀ i : Fin m, is_implicit_equality A b i → (A *ᵥ x) i = b i} := by
            ext x
            constructor
            · intro hx
              constructor
              · have hxj := congrArg (fun f ↦ f ⟨j, hj_implicit⟩) hx
                simpa [implicit_equality_mulVec_apply, implicit_equality_rhs_apply] using hxj
              · intro i hi_implicit
                have hxi := congrArg (fun f ↦ f ⟨i, hi_implicit⟩) hx
                simpa [implicit_equality_mulVec_apply, implicit_equality_rhs_apply] using hxi
            · rintro ⟨_, hx⟩
              ext i
              simpa [implicit_equality_mulVec_apply, implicit_equality_rhs_apply] using hx i.1 i.2
  · ext x
    constructor
    · intro hxAff
      -- Every point of the affine span remains on row `j` and on every implicit-equality
      -- hyperplane because the face itself already lies in each of them.
      have hface_row :
          active_constraint_face A b ({j} : Set (Fin m)) ⊆
            {y : Fin n → ℝ | A j ⬝ᵥ y = b j} := by
        intro y hy
        simpa [Matrix.mulVec] using (mem_active_constraint_face_iff.mp hy).1 j (by simp)
      have hface_row_aff :=
        affineSpan_subset_hyperplane_of_subset
          (S := active_constraint_face A b ({j} : Set (Fin m))) (c := A j) (δ := b j) hface_row
      constructor
      · simpa [Matrix.mulVec] using hface_row_aff hxAff
      · intro i hi_implicit
        have himplicit :
            active_constraint_face A b ({j} : Set (Fin m)) ⊆
              {y : Fin n → ℝ | A i ⬝ᵥ y = b i} := by
          intro y hy
          simpa [Matrix.mulVec] using
            hi_implicit (mem_polyhedron_of_mem_active_constraint_face hy)
        have himplicit_aff :=
          affineSpan_subset_hyperplane_of_subset
            (S := active_constraint_face A b ({j} : Set (Fin m))) (c := A i) (δ := b i) himplicit
        simpa [Matrix.mulVec] using himplicit_aff hxAff
    · intro hx
      obtain ⟨xbar, hxbar_face, hbar_strict⟩ :=
        exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
          A b j h_nonempty hj_irredundant
      rcases
          exists_small_step_mem_active_constraint_face_singleton_of_row_eq_and_implicit_eq
            A b j xbar x hxbar_face hbar_strict hx.1 hx.2 with
        ⟨ε, hε_pos, _hε_le_one, hstep_face⟩
      have hx_line :
          x ∈ affineSpan ℝ ({xbar, xbar + ε • (x - xbar)} : Set (Fin n → ℝ)) := by
        -- The source line argument places `x` on the affine line through `xbar` and the stepped
        -- feasible point.
        refine
          mem_affineSpan_pair_of_nonzero_step xbar (xbar + ε • (x - xbar)) x rfl
            (ne_of_gt hε_pos)
      have hpair_subset :
          ({xbar, xbar + ε • (x - xbar)} : Set (Fin n → ℝ)) ⊆
            active_constraint_face A b ({j} : Set (Fin m)) := by
        intro y hy
        rcases hy with rfl | rfl
        · exact hxbar_face
        · exact hstep_face
      exact affineSpan_mono ℝ hpair_subset hx_line

/-- Lemma 3.26. Under the hypotheses of Lemma 3.26, activating an irredundant non-implicit
row lowers the affine dimension by exactly one. -/
theorem finrank_direction_affineSpan_active_constraint_face_singleton_eq_sub_one
    (h_nonempty : (polyhedron_le_set A b).Nonempty)
    (hj_not_implicit : ¬ is_implicit_equality A b j)
    (hj_irredundant : is_irredundant_row A b j) :
    Module.finrank ℝ (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))).direction =
      Module.finrank ℝ
          (affineSpan ℝ (polyhedron_le_set A b)).direction -
        1 := by
  let F : Set (Fin n → ℝ) := active_constraint_face A b ({j} : Set (Fin m))
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  let D : Submodule ℝ (Fin n → ℝ) := (affineSpan ℝ P).direction
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductStrongDual (A j)).toLinearMap
  obtain ⟨xhat, hxhat_face, hhat_strict⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A b j h_nonempty hj_irredundant
  have hxhat_poly : xhat ∈ P := by
    simpa [F, P] using mem_polyhedron_of_mem_active_constraint_face hxhat_face
  have hxhat_face_aff : xhat ∈ affineSpan ℝ F := subset_affineSpan ℝ F hxhat_face
  have hxhat_poly_aff : xhat ∈ affineSpan ℝ P := subset_affineSpan ℝ P hxhat_poly
  have hxhat_row : (A *ᵥ xhat) j = b j := by
    simpa [F] using (mem_active_constraint_face_iff.mp hxhat_face).1 j (by simp)
  have hF_subset_P : F ⊆ P := by
    intro x hx
    simpa [F, P] using mem_polyhedron_of_mem_active_constraint_face hx
  have hdir_eq :
      (affineSpan ℝ F).direction = D ⊓ LinearMap.ker L := by
    apply le_antisymm
    · intro v hv
      refine ⟨?_, ?_⟩
      · -- Any face direction is automatically an ambient polyhedron direction.
        simpa [D] using (AffineSubspace.direction_le (affineSpan_mono ℝ hF_subset_P)) hv
      · change L v = 0
        rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhat_face_aff] at hv
        rcases hv with ⟨x, hxAff, rfl⟩
        have hx_rhs :
            (A *ᵥ x) j = b j ∧
              ∀ i : Fin m, is_implicit_equality A b i → (A *ᵥ x) i = b i := by
          have hxAff' : x ∈ (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m))) :
              Set (Fin n → ℝ)) := by
            simpa [F] using hxAff
          simpa using
            (show x ∈
              {y : Fin n → ℝ |
                (A *ᵥ y) j = b j ∧
                  ∀ i : Fin m, is_implicit_equality A b i → (A *ᵥ y) i = b i} by
                rwa [affineSpan_active_constraint_face_singleton_eq_implicit_equalities_and_row
                  A b j h_nonempty hj_irredundant] at hxAff')
        -- Subtracting two points of the same row-`j` hyperplane kills the row functional.
        calc
          L (x - xhat) = (A *ᵥ (x - xhat)) j := by
              simp [L, dotProductStrongDual_apply, Matrix.mulVec]
          _ = (A *ᵥ x) j - (A *ᵥ xhat) j := by
                simp [Matrix.mulVec_sub]
          _ = 0 := by rw [hx_rhs.1, hxhat_row, sub_self]
    · rintro v ⟨hvD, hvKer⟩
      have hvD' : v ∈ D := by simpa [D] using hvD
      have hvKer' : L v = 0 := by simpa [L] using hvKer
      rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhat_poly_aff] at hvD'
      rcases hvD' with ⟨x, hxAffP, rfl⟩
      have hxImpEq : A^= *ᵥ x = b^= := by
        have hxAffP' : x ∈ (affineSpan ℝ (polyhedron_le_set A b) : Set (Fin n → ℝ)) := by
          simpa [P] using hxAffP
        simpa using
          (show x ∈ ({y : Fin n → ℝ | A^= *ᵥ y = b^=} : Set (Fin n → ℝ)) by
            rwa [affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set A b]
              at hxAffP')
      have hx_implicit :
          ∀ i : Fin m, is_implicit_equality A b i → (A *ᵥ x) i = b i := by
        intro i hi_implicit
        have hxi := congrArg (fun f ↦ f ⟨i, hi_implicit⟩) hxImpEq
        simpa [implicit_equality_mulVec_apply, implicit_equality_rhs_apply] using hxi
      have hx_row : (A *ᵥ x) j = b j := by
        have hsub_zero : (A *ᵥ (x - xhat)) j = 0 := by
          simpa [L, dotProductStrongDual_apply, Matrix.mulVec_sub, Matrix.mulVec] using hvKer'
        calc
          (A *ᵥ x) j = (A *ᵥ (x - xhat)) j + (A *ᵥ xhat) j := by
              simp [Matrix.mulVec_sub]
          _ = 0 + (A *ᵥ xhat) j := by rw [hsub_zero]
          _ = b j := by simp [hxhat_row]
      have hx_face_aff :
          x ∈ (affineSpan ℝ F : Set (Fin n → ℝ)) := by
        have hx_rhs :
            x ∈ {y : Fin n → ℝ |
              (A *ᵥ y) j = b j ∧
                ∀ i : Fin m, is_implicit_equality A b i → (A *ᵥ y) i = b i} := by
          exact ⟨hx_row, hx_implicit⟩
        simpa [F] using
          (show x ∈ (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m))) :
              Set (Fin n → ℝ)) by
            rwa [affineSpan_active_constraint_face_singleton_eq_implicit_equalities_and_row
              A b j h_nonempty hj_irredundant])
      -- Re-enter the face direction by translating back from `xhat`.
      rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhat_face_aff]
      refine ⟨x, hx_face_aff, ?_⟩
      simp [vsub_eq_sub]
  have hj_remaining : j ∈ remaining_inequality_indices A b :=
    (mem_remaining_inequality_indices_iff A b j).2 hj_not_implicit
  rcases exists_mem_polyhedron_le_set_strict_on_remaining_inequality_indices A b h_nonempty with
    ⟨xP, hxP, hxP_strict⟩
  have hxP_row_lt : (A *ᵥ xP) j < b j := hxP_strict j hj_remaining
  let gap : ℝ := b j - (A *ᵥ xP) j
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  have hdiff_dir : xhat - xP ∈ D := by
    have hxP_aff : xP ∈ affineSpan ℝ P := subset_affineSpan ℝ P hxP
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxP_aff]
    refine ⟨xhat, hxhat_poly_aff, ?_⟩
    simp [vsub_eq_sub]
  let w : Fin n → ℝ := gap⁻¹ • (xhat - xP)
  have hwD : w ∈ D := by
    dsimp [w]
    exact Submodule.smul_mem D _ hdiff_dir
  have hw_eval : L w = 1 := by
    have hbase :
        L (xhat - xP) = gap := by
      calc
        L (xhat - xP) = (A *ᵥ (xhat - xP)) j := by
            simp [L, dotProductStrongDual_apply, Matrix.mulVec]
        _ = (A *ᵥ xhat) j - (A *ᵥ xP) j := by
              simp [Matrix.mulVec_sub]
        _ = gap := by
              dsimp [gap]
              rw [hxhat_row]
    -- Normalize the row gap so that the functional evaluates to `1`.
    calc
      L w = gap⁻¹ * gap := by
              dsimp [w]
              simp [hbase, smul_eq_mul]
      _ = 1 := by
            field_simp [ne_of_gt hgap_pos]
  have hcodim :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D :=
    finrank_inf_ker_add_one_of_eval_one D L hwD hw_eval
  have hfin :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) = Module.finrank ℝ ↥D - 1 := by
    have hcodim' := congrArg (fun t : ℕ ↦ t - 1) hcodim
    simpa using hcodim'
  -- The direction equality turns the codimension-one kernel computation into the face dimension.
  calc
    Module.finrank ℝ (affineSpan ℝ F).direction
        = Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) := by rw [hdir_eq]
    _ = Module.finrank ℝ ↥D - 1 := hfin
    _ = Module.finrank ℝ (affineSpan ℝ P).direction - 1 := by rfl

end Lemma_3_26
