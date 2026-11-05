/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_1.ch3_sec3_4_1_definition_3_4_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_corollary_3_23
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3

open scoped Matrix

-- Semantic search tool `lean_leansearch` was unavailable in this environment; this item uses the
-- local Chapter 3 `Fin n → ℝ` matrix API together with the Section 3.8 mixed-system owner
-- `mixed_constraint_polyhedron`, the canonical face/facet owners, and the row-vector notation
-- `u ᵥ* A`.

section Theorem_3_30

/-- A minimal representation of `P` is a mixed equality/inequality system whose equation rows cut
out `affineSpan ℝ P` with full row rank and whose inequality rows are in bijection with the facets
of `P`. -/
class is_minimal_representation
    {n meq mineq : ℕ}
    (P : Set (Fin n → ℝ))
    (Aeq : Matrix (Fin meq) (Fin n) ℝ)
    (beq : Fin meq → ℝ)
    (Aineq : Matrix (Fin mineq) (Fin n) ℝ)
    (bineq : Fin mineq → ℝ) : Prop where
  /-- The mixed system represents `P`. -/
  eq_polyhedron : P = mixed_constraint_polyhedron Aineq bineq Aeq beq
  /-- The equality subsystem cuts out the affine hull of `P`. -/
  eq_affine_hull :
    (affineSpan ℝ P : Set (Fin n → ℝ)) = {x : Fin n → ℝ | Aeq *ᵥ x = beq}
  /-- The equality matrix has full row rank, so no equation is redundant. -/
  full_row_rank : Aeq.rank = meq
  /-- Every inequality row defines a facet of `P`. -/
  row_is_facet (i : Fin mineq) : is_facet P (face_set P (Aineq i) (bineq i))
  /-- Every facet of `P` is defined by a unique inequality row. -/
  facets_exhausted (F : Set (Fin n → ℝ)) (hF : is_facet P F) :
    ∃! i : Fin mineq, F = face_set P (Aineq i) (bineq i)

namespace is_minimal_representation

variable {n meq mineq : ℕ}
variable {P : Set (Fin n → ℝ)}
variable {Aeq : Matrix (Fin meq) (Fin n) ℝ}
variable {beq : Fin meq → ℝ}
variable {Aineq : Matrix (Fin mineq) (Fin n) ℝ}
variable {bineq : Fin mineq → ℝ}

/-- Every facet of `P` occurs among the inequality rows of a minimal representation. -/
theorem facet_surjective
    (hmin : is_minimal_representation P Aeq beq Aineq bineq)
    (F : Set (Fin n → ℝ))
    (hF : is_facet P F) :
    ∃ i : Fin mineq, F = face_set P (Aineq i) (bineq i) := by
  exact (hmin.facets_exhausted F hF).exists

/-- Distinct inequality rows of a minimal representation cut out distinct facets. -/
theorem facet_injective
    (hmin : is_minimal_representation P Aeq beq Aineq bineq) :
    Function.Injective (fun i : Fin mineq ↦ face_set P (Aineq i) (bineq i)) := by
  intro i j hij
  obtain ⟨k, hk, hk_unique⟩ :=
    hmin.facets_exhausted (face_set P (Aineq i) (bineq i)) (hmin.row_is_facet i)
  have hki : i = k := hk_unique i rfl
  have hkj : j = k := hk_unique j hij
  exact hki.trans hkj.symm

end is_minimal_representation

/-- Helper for Theorem 3.30: once the affine hull of `P` is presented as the solution set of
`Aeq *ᵥ x = beq`, its direction is exactly the kernel of `Aeq.mulVecLin`. -/
lemma affine_hull_direction_eq_matrix_kernel_of_eq_system
    {n meq : ℕ}
    (P : Set (Fin n → ℝ))
    (Aeq : Matrix (Fin meq) (Fin n) ℝ)
    (beq : Fin meq → ℝ)
    (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ P)
    (hAff : (affineSpan ℝ P : Set (Fin n → ℝ)) = {x : Fin n → ℝ | Aeq *ᵥ x = beq}) :
    (affineSpan ℝ P).direction = LinearMap.ker Aeq.mulVecLin := by
  have hx0_aff : x0 ∈ affineSpan ℝ P := subset_affineSpan ℝ P hx0
  have hx0_eq : Aeq *ᵥ x0 = beq := by
    change x0 ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) at hx0_aff
    have hx0_eq_set :
        x0 ∈ ({x : Fin n → ℝ | Aeq *ᵥ x = beq} : Set (Fin n → ℝ)) := by
      rwa [hAff] at hx0_aff
    exact hx0_eq_set
  have hSet :
      {x : Fin n → ℝ | Aeq *ᵥ x = beq} =
        (AffineSubspace.mk' x0 Aeq.mulVecLin.ker : Set (Fin n → ℝ)) := by
    ext x
    -- Rewrite the affine solution set as a translate of the matrix kernel through one solution.
    simp [AffineSubspace.mem_mk', LinearMap.mem_ker, hx0_eq, Matrix.mulVec_sub, sub_eq_zero]
  have hAffSubspace :
      affineSpan ℝ P = AffineSubspace.mk' x0 Aeq.mulVecLin.ker := by
    ext x
    change
      (x ∈ (affineSpan ℝ P : Set (Fin n → ℝ))) ↔
        x ∈ (AffineSubspace.mk' x0 Aeq.mulVecLin.ker : Set (Fin n → ℝ))
    rw [hAff, hSet]
  -- The direction of a point-translate is the underlying kernel submodule.
  rw [hAffSubspace, AffineSubspace.direction_mk']

/-- Helper for Theorem 3.30: the weighted deficit against a pointwise upper bound vanishes at a
coordinate with positive weight only when that coordinate is already tight. -/
lemma eq_of_positive_dotProduct_sub_eq_zero
    {m : ℕ}
    (u a b : Fin m → ℝ)
    (hu_nonneg : 0 ≤ u)
    (hab : a ≤ b)
    (hsum : u ⬝ᵥ (fun r : Fin m ↦ b r - a r) = 0)
    {r : Fin m}
    (hr : 0 < u r) :
    a r = b r := by
  have hsum' : ∑ s : Fin m, u s * (b s - a s) = 0 := by
    simpa [dotProduct] using hsum
  have hterm_zero :
      ∀ s ∈ Finset.univ, u s * (b s - a s) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum'
    intro s _hs
    exact mul_nonneg (hu_nonneg s) (sub_nonneg.mpr (hab s))
  have hsub_zero : b r - a r = 0 := by
    exact (mul_eq_zero.mp (hterm_zero r (Finset.mem_univ r))).resolve_left (ne_of_gt hr)
  exact (sub_eq_zero.mp hsub_zero).symm

/-- Helper for Theorem 3.30: the facets of a minimal representation are exactly the range of its
rowwise face map. -/
lemma facets_eq_row_face_range
    {n meq mineq : ℕ}
    (P : Set (Fin n → ℝ))
    (Aeq : Matrix (Fin meq) (Fin n) ℝ)
    (beq : Fin meq → ℝ)
    (Aineq : Matrix (Fin mineq) (Fin n) ℝ)
    (bineq : Fin mineq → ℝ)
    (hmin : is_minimal_representation P Aeq beq Aineq bineq) :
    {F : Set (Fin n → ℝ) | is_facet P F} =
      Set.range (fun i : Fin mineq ↦ face_set P (Aineq i) (bineq i)) := by
  ext F
  constructor
  · intro hF
    rcases hmin.facet_surjective F hF with ⟨i, rfl⟩
    exact Set.mem_range_self i
  · rintro ⟨i, rfl⟩
    exact hmin.row_is_facet i

/-- Theorem 3.30 (1) and (2) (Uniqueness of the Minimal Representation). Any minimal
representation of the nonempty polyhedron `P ⊆ ℝ^n` has
`n - Module.finrank ℝ (affineSpan ℝ P).direction` equality rows. -/
theorem minimal_representation_eq_rows_count
    {n meqA mineqA : ℕ}
    (P : Set (Fin n → ℝ))
    (Aeq : Matrix (Fin meqA) (Fin n) ℝ)
    (beq : Fin meqA → ℝ)
    (Aineq : Matrix (Fin mineqA) (Fin n) ℝ)
    (bineq : Fin mineqA → ℝ)
    (hP_nonempty : P.Nonempty)
    (hAmin : is_minimal_representation P Aeq beq Aineq bineq) :
    meqA = n - Module.finrank ℝ (affineSpan ℝ P).direction := by
  rcases hP_nonempty with ⟨x0, hx0⟩
  have hdir :
      (affineSpan ℝ P).direction = LinearMap.ker Aeq.mulVecLin :=
    affine_hull_direction_eq_matrix_kernel_of_eq_system P Aeq beq x0 hx0 hAmin.eq_affine_hull
  have hker :
      Module.finrank ℝ (LinearMap.ker Aeq.mulVecLin) = n - Aeq.rank := by
    simpa using finrank_matrix_kernel_eq_card_sub_rank Aeq
  have hsum' : n = Module.finrank ℝ (LinearMap.ker Aeq.mulVecLin) + Aeq.rank := by
    exact (Nat.sub_eq_iff_eq_add (Matrix.rank_le_width Aeq)).mp hker.symm
  have hsum : Aeq.rank + Module.finrank ℝ (LinearMap.ker Aeq.mulVecLin) = n := by
    omega
  have hrank :
      Aeq.rank = n - Module.finrank ℝ (LinearMap.ker Aeq.mulVecLin) := by
    have hfin_le : Module.finrank ℝ (LinearMap.ker Aeq.mulVecLin) ≤ n := by
      rw [hker]
      exact Nat.sub_le _ _
    exact ((Nat.sub_eq_iff_eq_add hfin_le).mpr (by simpa [add_comm] using hsum.symm)).symm
  -- The affine-hull description and the full-row-rank hypothesis identify the equality count.
  calc
    meqA = Aeq.rank := hAmin.full_row_rank.symm
    _ = n - Module.finrank ℝ (LinearMap.ker Aeq.mulVecLin) := hrank
    _ = n - Module.finrank ℝ (affineSpan ℝ P).direction := by rw [hdir]

/-- Theorem 3.30 (3) (Uniqueness of the Minimal Representation). If
`Aeq *ᵥ x = beq, Aineq *ᵥ x ≤ bineq` and `Ceq *ᵥ x = deq, Cineq *ᵥ x ≤ dineq` are two minimal
representations of the same nonempty polyhedron `P ⊆ ℝ^n`, then every equation of
`Ceq *ᵥ x = deq` is a linear combination of the equations of `Aeq *ᵥ x = beq`. -/
theorem minimal_representation_eq_rows_linear_combination
    {n meqA mineqA meqC mineqC : ℕ}
    (P : Set (Fin n → ℝ))
    (Aeq : Matrix (Fin meqA) (Fin n) ℝ)
    (beq : Fin meqA → ℝ)
    (Aineq : Matrix (Fin mineqA) (Fin n) ℝ)
    (bineq : Fin mineqA → ℝ)
    (Ceq : Matrix (Fin meqC) (Fin n) ℝ)
    (deq : Fin meqC → ℝ)
    (Cineq : Matrix (Fin mineqC) (Fin n) ℝ)
    (dineq : Fin mineqC → ℝ)
    (hP_nonempty : P.Nonempty)
    (hAmin : is_minimal_representation P Aeq beq Aineq bineq)
    (hCmin : is_minimal_representation P Ceq deq Cineq dineq)
    (i : Fin meqC) :
    ∃ u : Fin meqA → ℝ, u ᵥ* Aeq = Ceq i ∧ u ⬝ᵥ beq = deq i := by
  rcases hP_nonempty with ⟨x0, hx0P⟩
  have hx0_mixedA : x0 ∈ mixed_constraint_polyhedron Aineq bineq Aeq beq := by
    simpa [hAmin.eq_polyhedron] using hx0P
  have hx0_aff : x0 ∈ affineSpan ℝ P := subset_affineSpan ℝ P hx0P
  have hx0_Aeq : Aeq *ᵥ x0 = beq := by
    change x0 ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) at hx0_aff
    have hx0_eq_set :
        x0 ∈ ({x : Fin n → ℝ | Aeq *ᵥ x = beq} : Set (Fin n → ℝ)) := by
      rwa [hAmin.eq_affine_hull] at hx0_aff
    exact hx0_eq_set
  have hx0_Ceq : Ceq *ᵥ x0 = deq := by
    change x0 ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) at hx0_aff
    have hx0_eq_set :
        x0 ∈ ({x : Fin n → ℝ | Ceq *ᵥ x = deq} : Set (Fin n → ℝ)) := by
      rwa [hCmin.eq_affine_hull] at hx0_aff
    exact hx0_eq_set
  have hvalid :
      is_valid_inequality (mixed_constraint_polyhedron Aineq bineq Aeq beq) (Ceq i) (deq i) := by
    intro x hx
    have hxP : x ∈ P := by
      simpa [hAmin.eq_polyhedron] using hx
    have hxAff : x ∈ affineSpan ℝ P := subset_affineSpan ℝ P hxP
    have hxEq : Ceq *ᵥ x = deq := by
      change x ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) at hxAff
      have hxEq_set :
          x ∈ ({x : Fin n → ℝ | Ceq *ᵥ x = deq} : Set (Fin n → ℝ)) := by
        rwa [hCmin.eq_affine_hull] at hxAff
      exact hxEq_set
    exact le_of_eq (congrFun hxEq i)
  obtain ⟨u, v, hu_nonneg, hrow, hδ⟩ :=
    (valid_inequality_iff_exists_mixed_row_multiplier
      Aineq bineq Aeq beq (Ceq i) (deq i) ⟨x0, hx0_mixedA⟩).mp hvalid
  have hu_zero : u = 0 := by
    funext r
    by_cases hr_pos : 0 < u r
    · exfalso
      have hr_eq_all : ∀ {x : Fin n → ℝ}, x ∈ P → (Aineq *ᵥ x) r = bineq r := by
        intro x hxP
        have hxMixed : x ∈ mixed_constraint_polyhedron Aineq bineq Aeq beq := by
          simpa [hAmin.eq_polyhedron] using hxP
        have hxAff : x ∈ affineSpan ℝ P := subset_affineSpan ℝ P hxP
        have hxAeq : Aeq *ᵥ x = beq := by
          change x ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) at hxAff
          have hxEq_set :
              x ∈ ({x : Fin n → ℝ | Aeq *ᵥ x = beq} : Set (Fin n → ℝ)) := by
            rwa [hAmin.eq_affine_hull] at hxAff
          exact hxEq_set
        have hxCeq : Ceq *ᵥ x = deq := by
          change x ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) at hxAff
          have hxEq_set :
              x ∈ ({x : Fin n → ℝ | Ceq *ᵥ x = deq} : Set (Fin n → ℝ)) := by
            rwa [hCmin.eq_affine_hull] at hxAff
          exact hxEq_set
        have hEval :
            u ⬝ᵥ (Aineq *ᵥ x) + v ⬝ᵥ beq = deq i := by
          have hu_eval :
              u ⬝ᵥ (Aineq *ᵥ x) = (u ᵥ* Aineq) ⬝ᵥ x := by
            exact Matrix.dotProduct_mulVec u Aineq x
          have hv_eval :
              v ⬝ᵥ (Aeq *ᵥ x) = (v ᵥ* Aeq) ⬝ᵥ x := by
            exact Matrix.dotProduct_mulVec v Aeq x
          calc
            u ⬝ᵥ (Aineq *ᵥ x) + v ⬝ᵥ beq
                = u ⬝ᵥ (Aineq *ᵥ x) + v ⬝ᵥ (Aeq *ᵥ x) := by rw [hxAeq]
            _ = ((u ᵥ* Aineq) ⬝ᵥ x) + ((v ᵥ* Aeq) ⬝ᵥ x) := by rw [hu_eval, hv_eval]
            _ = (u ᵥ* Aineq + v ᵥ* Aeq) ⬝ᵥ x := by
                  rw [add_dotProduct]
            _ = Ceq i ⬝ᵥ x := by rw [hrow]
            _ = deq i := congrFun hxCeq i
        have hEval_le :
            u ⬝ᵥ (Aineq *ᵥ x) + v ⬝ᵥ beq ≤ u ⬝ᵥ bineq + v ⬝ᵥ beq := by
          gcongr
          exact dotProduct_le_dotProduct_of_nonneg_left hxMixed.1 hu_nonneg
        have hdot_eq : u ⬝ᵥ (Aineq *ᵥ x) = u ⬝ᵥ bineq := by
          linarith
        have hdef_zero :
            u ⬝ᵥ (fun s : Fin mineqA ↦ bineq s - (Aineq *ᵥ x) s) = 0 := by
          calc
            u ⬝ᵥ (fun s : Fin mineqA ↦ bineq s - (Aineq *ᵥ x) s)
                = u ⬝ᵥ bineq - u ⬝ᵥ (Aineq *ᵥ x) := by
                    simp [dotProduct, Finset.sum_sub_distrib, mul_sub]
            _ = 0 := by rw [hdot_eq, sub_self]
        exact
          eq_of_positive_dotProduct_sub_eq_zero
            u (Aineq *ᵥ x) bineq hu_nonneg hxMixed.1 hdef_zero hr_pos
      have hface_eq : face_set P (Aineq r) (bineq r) = P := by
        ext x
        constructor
        · intro hxFace
          exact (mem_face_set_iff.mp hxFace).1
        · intro hxP
          exact (mem_face_set_iff).2 ⟨hxP, hr_eq_all hxP⟩
      exact
        (is_proper_face_iff.mp (is_facet_to_is_proper_face (hAmin.row_is_facet r))).2.2.ne
          hface_eq
    · exact le_antisymm (le_of_not_gt hr_pos) (hu_nonneg r)
  refine ⟨v, ?_, ?_⟩
  · -- Once every inequality multiplier vanishes, only the equality-row combination remains.
    simpa [hu_zero] using hrow
  · -- Evaluate the row identity at a feasible point to upgrade the scalar inequality to equality.
    have hv_eval :
        v ⬝ᵥ beq = deq i := by
      have hvAeq :
          v ⬝ᵥ (Aeq *ᵥ x0) = (v ᵥ* Aeq) ⬝ᵥ x0 := by
        exact Matrix.dotProduct_mulVec v Aeq x0
      calc
        v ⬝ᵥ beq = v ⬝ᵥ (Aeq *ᵥ x0) := by rw [hx0_Aeq]
        _ = (v ᵥ* Aeq) ⬝ᵥ x0 := hvAeq
        _ = Ceq i ⬝ᵥ x0 := by simpa [hu_zero] using congrArg (fun w ↦ w ⬝ᵥ x0) hrow
        _ = deq i := congrFun hx0_Ceq i
    exact hv_eval

/-- Theorem 3.30 (4) and (5) (Uniqueness of the Minimal Representation). Any minimal
representation of `P ⊆ ℝ^n` has as many inequality rows as `P` has facets. -/
theorem minimal_representation_facet_rows_count
    {n meqA mineqA : ℕ}
    (P : Set (Fin n → ℝ))
    (Aeq : Matrix (Fin meqA) (Fin n) ℝ)
    (beq : Fin meqA → ℝ)
    (Aineq : Matrix (Fin mineqA) (Fin n) ℝ)
    (bineq : Fin mineqA → ℝ)
    (hAmin : is_minimal_representation P Aeq beq Aineq bineq) :
    mineqA = {F : Set (Fin n → ℝ) | is_facet P F}.ncard := by
  have hfacets :
      {F : Set (Fin n → ℝ) | is_facet P F} =
        Set.range (fun i : Fin mineqA ↦ face_set P (Aineq i) (bineq i)) :=
    facets_eq_row_face_range P Aeq beq Aineq bineq hAmin
  -- Minimality identifies the facet set with the range of the injective row-face map.
  calc
    mineqA = Fintype.card (Fin mineqA) := by simp
    _ = (Set.range fun i : Fin mineqA ↦ face_set P (Aineq i) (bineq i)).ncard := by
          simpa [Nat.card_eq_fintype_card] using
            (Set.ncard_range_of_injective (is_minimal_representation.facet_injective hAmin)).symm
    _ = {F : Set (Fin n → ℝ) | is_facet P F}.ncard := by rw [← hfacets]

/-- Helper for Theorem 3.30: every point of `P` satisfies the equality subsystem of a minimal
representation. -/
lemma eq_rows_eq_of_mem_minimal_representation
    {n meq mineq : ℕ}
    {P : Set (Fin n → ℝ)}
    {Aeq : Matrix (Fin meq) (Fin n) ℝ}
    {beq : Fin meq → ℝ}
    {Aineq : Matrix (Fin mineq) (Fin n) ℝ}
    {bineq : Fin mineq → ℝ}
    (hmin : is_minimal_representation P Aeq beq Aineq bineq)
    {x : Fin n → ℝ}
    (hx : x ∈ P) :
    Aeq *ᵥ x = beq := by
  -- Any point of `P` lies in `affineSpan ℝ P`, so the affine-hull presentation gives the
  -- equality rows immediately.
  have hx_aff : x ∈ affineSpan ℝ P := subset_affineSpan ℝ P hx
  change x ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) at hx_aff
  have hx_eq :
      x ∈ ({y : Fin n → ℝ | Aeq *ᵥ y = beq} : Set (Fin n → ℝ)) := by
    rwa [hmin.eq_affine_hull] at hx_aff
  exact hx_eq

/-- Helper for Theorem 3.30: on a matched facet, every inequality row with positive mixed
certificate weight is tight at each point of that facet. -/
lemma same_facet_certificate_positive_support_tight
    {n meqA mineqA mineqC : ℕ}
    {P : Set (Fin n → ℝ)}
    {Aeq : Matrix (Fin meqA) (Fin n) ℝ}
    {beq : Fin meqA → ℝ}
    {Aineq : Matrix (Fin mineqA) (Fin n) ℝ}
    {bineq : Fin mineqA → ℝ}
    {Cineq : Matrix (Fin mineqC) (Fin n) ℝ}
    {dineq : Fin mineqC → ℝ}
    (hAmin : is_minimal_representation P Aeq beq Aineq bineq)
    {j : Fin mineqA}
    {k : Fin mineqC}
    {u : Fin mineqA → ℝ}
    {v : Fin meqA → ℝ}
    (hu_nonneg : 0 ≤ u)
    (hrow : u ᵥ* Aineq + v ᵥ* Aeq = Cineq k)
    (hδ : u ⬝ᵥ bineq + v ⬝ᵥ beq ≤ dineq k)
    (hface_eq : face_set P (Aineq j) (bineq j) = face_set P (Cineq k) (dineq k))
    {x : Fin n → ℝ}
    (hx_face : x ∈ face_set P (Aineq j) (bineq j))
    {r : Fin mineqA}
    (hr : 0 < u r) :
    (Aineq *ᵥ x) r = bineq r := by
  have hxP : x ∈ P := (mem_face_set_iff.mp hx_face).1
  have hxMixedA : x ∈ mixed_constraint_polyhedron Aineq bineq Aeq beq := by
    simpa [hAmin.eq_polyhedron] using hxP
  have hxAeq : Aeq *ᵥ x = beq := eq_rows_eq_of_mem_minimal_representation hAmin hxP
  have hxC_face : x ∈ face_set P (Cineq k) (dineq k) := by
    simpa [hface_eq] using hx_face
  have hxCeq : Cineq k ⬝ᵥ x = dineq k := (mem_face_set_iff.mp hxC_face).2
  have hEval :
      u ⬝ᵥ (Aineq *ᵥ x) + v ⬝ᵥ beq = dineq k := by
    -- Evaluating the certificate on a point of the matched facet removes the equality block and
    -- identifies the `C`-row value with `dineq k`.
    calc
      u ⬝ᵥ (Aineq *ᵥ x) + v ⬝ᵥ beq
          = u ⬝ᵥ (Aineq *ᵥ x) + v ⬝ᵥ (Aeq *ᵥ x) := by rw [hxAeq]
      _ = ((u ᵥ* Aineq) ⬝ᵥ x) + ((v ᵥ* Aeq) ⬝ᵥ x) := by
            rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
      _ = (u ᵥ* Aineq + v ᵥ* Aeq) ⬝ᵥ x := by rw [add_dotProduct]
      _ = Cineq k ⬝ᵥ x := by rw [hrow]
      _ = dineq k := hxCeq
  have hEval_le :
      u ⬝ᵥ (Aineq *ᵥ x) + v ⬝ᵥ beq ≤ u ⬝ᵥ bineq + v ⬝ᵥ beq := by
    gcongr
    exact dotProduct_le_dotProduct_of_nonneg_left hxMixedA.1 hu_nonneg
  have hdot_eq : u ⬝ᵥ (Aineq *ᵥ x) = u ⬝ᵥ bineq := by
    linarith
  have hslack_zero :
      u ⬝ᵥ (fun s : Fin mineqA ↦ bineq s - (Aineq *ᵥ x) s) = 0 := by
    -- The weighted slack vanishes because the matched-facet point attains the certificate bound.
    calc
      u ⬝ᵥ (fun s : Fin mineqA ↦ bineq s - (Aineq *ᵥ x) s)
          = u ⬝ᵥ bineq - u ⬝ᵥ (Aineq *ᵥ x) := by
              simp [dotProduct, Finset.sum_sub_distrib, mul_sub]
      _ = 0 := by rw [hdot_eq, sub_self]
  exact
    eq_of_positive_dotProduct_sub_eq_zero
      u (Aineq *ᵥ x) bineq hu_nonneg hxMixedA.1 hslack_zero hr

/-- Helper for Theorem 3.30: if a positive coefficient appears in a mixed certificate for a matched
facet pair, then that coefficient must belong to the anchor inequality row. -/
lemma positive_support_row_eq_anchor_of_same_facet_certificate
    {n meqA mineqA mineqC : ℕ}
    {P : Set (Fin n → ℝ)}
    {Aeq : Matrix (Fin meqA) (Fin n) ℝ}
    {beq : Fin meqA → ℝ}
    {Aineq : Matrix (Fin mineqA) (Fin n) ℝ}
    {bineq : Fin mineqA → ℝ}
    {Cineq : Matrix (Fin mineqC) (Fin n) ℝ}
    {dineq : Fin mineqC → ℝ}
    (hAmin : is_minimal_representation P Aeq beq Aineq bineq)
    {j : Fin mineqA}
    {k : Fin mineqC}
    {u : Fin mineqA → ℝ}
    {v : Fin meqA → ℝ}
    (hu_nonneg : 0 ≤ u)
    (hrow : u ᵥ* Aineq + v ᵥ* Aeq = Cineq k)
    (hδ : u ⬝ᵥ bineq + v ⬝ᵥ beq ≤ dineq k)
    (hface_eq : face_set P (Aineq j) (bineq j) = face_set P (Cineq k) (dineq k))
    {r : Fin mineqA}
    (hr : 0 < u r) :
    r = j := by
  have hsubset :
      face_set P (Aineq j) (bineq j) ⊆ face_set P (Aineq r) (bineq r) := by
    intro x hx
    refine (mem_face_set_iff).2 ?_
    refine ⟨(mem_face_set_iff.mp hx).1, ?_⟩
    exact same_facet_certificate_positive_support_tight hAmin hu_nonneg hrow hδ hface_eq hx hr
  -- Route correction: first prove rowwise tightness on the matched facet, then use facet
  -- maximality to collapse the entire positive support to the anchor row.
  have hface_r_eq :
      face_set P (Aineq r) (bineq r) = face_set P (Aineq j) (bineq j) :=
    is_facet_maximal
      (hAmin.row_is_facet j)
      (is_facet_to_is_proper_face (hAmin.row_is_facet r))
      hsubset
  exact (is_minimal_representation.facet_injective hAmin) hface_r_eq

/-- Helper for Theorem 3.30: a matched facet pair yields the textbook positive-scaling-plus-equality
normal form for the matched `C` row. -/
lemma same_facet_certificate_eq_pos_smul_add_equalities
    {n meqA mineqA meqC mineqC : ℕ}
    {P : Set (Fin n → ℝ)}
    {Aeq : Matrix (Fin meqA) (Fin n) ℝ}
    {beq : Fin meqA → ℝ}
    {Aineq : Matrix (Fin mineqA) (Fin n) ℝ}
    {bineq : Fin mineqA → ℝ}
    {Ceq : Matrix (Fin meqC) (Fin n) ℝ}
    {deq : Fin meqC → ℝ}
    {Cineq : Matrix (Fin mineqC) (Fin n) ℝ}
    {dineq : Fin mineqC → ℝ}
    (hAmin : is_minimal_representation P Aeq beq Aineq bineq)
    (hCmin : is_minimal_representation P Ceq deq Cineq dineq)
    {j : Fin mineqA}
    {k : Fin mineqC}
    (hface_eq : face_set P (Aineq j) (bineq j) = face_set P (Cineq k) (dineq k)) :
    ∃ lam : ℝ,
      0 < lam ∧
        ∃ uEq : Fin meqA → ℝ,
          (Cineq k, dineq k) =
            (lam • Aineq j + uEq ᵥ* Aeq, lam * bineq j + uEq ⬝ᵥ beq) := by
  rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face (hAmin.row_is_facet j))).2.1 with
    ⟨xF, hxF⟩
  have hxF_P : xF ∈ P := (mem_face_set_iff.mp hxF).1
  have hxF_mixedA : xF ∈ mixed_constraint_polyhedron Aineq bineq Aeq beq := by
    simpa [hAmin.eq_polyhedron] using hxF_P
  have hvalid_Crow :
      is_valid_inequality (mixed_constraint_polyhedron Aineq bineq Aeq beq) (Cineq k) (dineq k) :=
    by
      intro x hx
      have hxP : x ∈ P := by
        simpa [hAmin.eq_polyhedron] using hx
      have hxMixedC : x ∈ mixed_constraint_polyhedron Cineq dineq Ceq deq := by
        simpa [hCmin.eq_polyhedron] using hxP
      simpa [Matrix.mulVec] using hxMixedC.1 k
  obtain ⟨u, v, hu_nonneg, hrow, hδ⟩ :=
    (valid_inequality_iff_exists_mixed_row_multiplier
      Aineq bineq Aeq beq (Cineq k) (dineq k) ⟨xF, hxF_mixedA⟩).mp hvalid_Crow
  let lam : ℝ := u j
  have hu_zero_of_ne : ∀ r : Fin mineqA, r ≠ j → u r = 0 := by
    intro r hr_ne
    have hnot_pos : ¬ 0 < u r := by
      intro hr_pos
      exact hr_ne
        (positive_support_row_eq_anchor_of_same_facet_certificate
          hAmin hu_nonneg hrow hδ hface_eq hr_pos)
    exact le_antisymm (le_of_not_gt hnot_pos) (hu_nonneg r)
  have hcollapse_row : u ᵥ* Aineq = lam • Aineq j := by
    -- Once every off-anchor coefficient is zero, the mixed row combination collapses to the
    -- single anchor row `j`.
    calc
      u ᵥ* Aineq = ∑ r : Fin mineqA, u r • Aineq r := Matrix.vecMul_eq_sum u Aineq
      _ = u j • Aineq j := by
            classical
            refine Finset.sum_eq_single j ?_ ?_
            · intro r _hr hr_ne
              simp [hu_zero_of_ne r hr_ne]
            · simp
      _ = lam • Aineq j := by rfl
  have hCineq_eq : Cineq k = lam • Aineq j + v ᵥ* Aeq := by
    -- Replacing the inequality multiplier by its collapsed form yields the row identity.
    calc
      Cineq k = u ᵥ* Aineq + v ᵥ* Aeq := by symm; exact hrow
      _ = lam • Aineq j + v ᵥ* Aeq := by rw [hcollapse_row]
  have hxF_Aeq : Aeq *ᵥ xF = beq := eq_rows_eq_of_mem_minimal_representation hAmin hxF_P
  have hxF_Cface : xF ∈ face_set P (Cineq k) (dineq k) := by
    simpa [hface_eq] using hxF
  have hxF_anchor : Aineq j ⬝ᵥ xF = bineq j := (mem_face_set_iff.mp hxF).2
  have h_rhs_eq : dineq k = lam * bineq j + v ⬝ᵥ beq := by
    -- Evaluating the collapsed row identity on a point of the matched facet upgrades the
    -- certificate inequality to the desired equality on the right-hand side.
    calc
      dineq k = Cineq k ⬝ᵥ xF := (mem_face_set_iff.mp hxF_Cface).2.symm
      _ = (lam • Aineq j + v ᵥ* Aeq) ⬝ᵥ xF := by rw [hCineq_eq]
      _ = (lam • Aineq j) ⬝ᵥ xF + (v ᵥ* Aeq) ⬝ᵥ xF := by rw [add_dotProduct]
      _ = lam * (Aineq j ⬝ᵥ xF) + v ⬝ᵥ (Aeq *ᵥ xF) := by
            rw [← Matrix.dotProduct_mulVec]
            simp
      _ = lam * (Aineq j ⬝ᵥ xF) + v ⬝ᵥ beq := by rw [hxF_Aeq]
      _ = lam * bineq j + v ⬝ᵥ beq := by rw [hxF_anchor]
  have hface_ssubset : face_set P (Aineq j) (bineq j) ⊂ P :=
    (is_proper_face_iff.mp (is_facet_to_is_proper_face (hAmin.row_is_facet j))).2.2
  obtain ⟨xOut, hxOutP, hxOut_not_face⟩ := Set.exists_of_ssubset hface_ssubset
  have hxOut_mixedA : xOut ∈ mixed_constraint_polyhedron Aineq bineq Aeq beq := by
    simpa [hAmin.eq_polyhedron] using hxOutP
  have hxOut_mixedC : xOut ∈ mixed_constraint_polyhedron Cineq dineq Ceq deq := by
    simpa [hCmin.eq_polyhedron] using hxOutP
  have hxOut_Aeq : Aeq *ᵥ xOut = beq := eq_rows_eq_of_mem_minimal_representation hAmin hxOutP
  have hxOut_not_Cface : xOut ∉ face_set P (Cineq k) (dineq k) := by
    simpa [hface_eq] using hxOut_not_face
  have hxOut_Cle : Cineq k ⬝ᵥ xOut ≤ dineq k := by
    simpa [Matrix.mulVec] using hxOut_mixedC.1 k
  have hxOut_Clt : Cineq k ⬝ᵥ xOut < dineq k := by
    have hxOut_Cne : Cineq k ⬝ᵥ xOut ≠ dineq k := by
      intro hxEq
      exact hxOut_not_Cface ((mem_face_set_iff).2 ⟨hxOutP, hxEq⟩)
    exact lt_of_le_of_ne hxOut_Cle hxOut_Cne
  have hxOut_Ale : Aineq j ⬝ᵥ xOut ≤ bineq j := by
    simpa [Matrix.mulVec] using hxOut_mixedA.1 j
  have hxOut_Alt : Aineq j ⬝ᵥ xOut < bineq j := by
    have hxOut_Ane : Aineq j ⬝ᵥ xOut ≠ bineq j := by
      intro hxEq
      exact hxOut_not_face ((mem_face_set_iff).2 ⟨hxOutP, hxEq⟩)
    exact lt_of_le_of_ne hxOut_Ale hxOut_Ane
  have hgap_pos : 0 < bineq j - Aineq j ⬝ᵥ xOut := sub_pos.mpr hxOut_Alt
  have hC_out_eval :
      Cineq k ⬝ᵥ xOut = lam * (Aineq j ⬝ᵥ xOut) + v ⬝ᵥ beq := by
    calc
      Cineq k ⬝ᵥ xOut = (lam • Aineq j + v ᵥ* Aeq) ⬝ᵥ xOut := by rw [hCineq_eq]
      _ = (lam • Aineq j) ⬝ᵥ xOut + (v ᵥ* Aeq) ⬝ᵥ xOut := by rw [add_dotProduct]
      _ = lam * (Aineq j ⬝ᵥ xOut) + v ⬝ᵥ (Aeq *ᵥ xOut) := by
            rw [← Matrix.dotProduct_mulVec]
            simp
      _ = lam * (Aineq j ⬝ᵥ xOut) + v ⬝ᵥ beq := by rw [hxOut_Aeq]
  have hprod_eq :
      lam * (bineq j - Aineq j ⬝ᵥ xOut) = dineq k - Cineq k ⬝ᵥ xOut := by
    -- Comparing a point on the facet with a point strictly outside it isolates the anchor
    -- coefficient `lam`.
    calc
      lam * (bineq j - Aineq j ⬝ᵥ xOut)
          = (lam * bineq j + v ⬝ᵥ beq) - (lam * (Aineq j ⬝ᵥ xOut) + v ⬝ᵥ beq) := by
              ring
      _ = dineq k - Cineq k ⬝ᵥ xOut := by rw [h_rhs_eq, hC_out_eval]
  have hprod_pos : 0 < lam * (bineq j - Aineq j ⬝ᵥ xOut) := by
    rw [hprod_eq]
    linarith
  have hlam_pos : 0 < lam := by
    rw [mul_comm] at hprod_pos
    exact pos_of_mul_pos_right hprod_pos hgap_pos.le
  refine ⟨lam, hlam_pos, v, ?_⟩
  exact Prod.ext hCineq_eq h_rhs_eq

/-- Theorem 3.30 (6) (Uniqueness of the Minimal Representation). If
`Aeq *ᵥ x = beq, Aineq *ᵥ x ≤ bineq` and `Ceq *ᵥ x = deq, Cineq *ᵥ x ≤ dineq` are two minimal
representations of the same polyhedron `P ⊆ ℝ^n`, then after a permutation of the rows of
`Cineq`, each row is obtained from the corresponding row of `Aineq` by a positive scaling plus a
linear combination of the equality rows of `Aeq`. -/
theorem minimal_representation_facet_rows_permutation_scaling_and_equalities
    {n meqA mineqA meqC mineqC : ℕ}
    (P : Set (Fin n → ℝ))
    (Aeq : Matrix (Fin meqA) (Fin n) ℝ)
    (beq : Fin meqA → ℝ)
    (Aineq : Matrix (Fin mineqA) (Fin n) ℝ)
    (bineq : Fin mineqA → ℝ)
    (Ceq : Matrix (Fin meqC) (Fin n) ℝ)
    (deq : Fin meqC → ℝ)
    (Cineq : Matrix (Fin mineqC) (Fin n) ℝ)
    (dineq : Fin mineqC → ℝ)
    (hAmin : is_minimal_representation P Aeq beq Aineq bineq)
    (hCmin : is_minimal_representation P Ceq deq Cineq dineq) :
    ∃ σ : Fin mineqA ≃ Fin mineqC,
      ∀ j : Fin mineqA,
        ∃ lam : ℝ,
          0 < lam ∧
            ∃ u : Fin meqA → ℝ,
              (Cineq (σ j), dineq (σ j)) =
                (lam • Aineq j + u ᵥ* Aeq, lam * bineq j + u ⬝ᵥ beq) := by
  let σ : Fin mineqA → Fin mineqC :=
    fun j ↦
      Classical.choose
        (is_minimal_representation.facet_surjective
          hCmin
          (face_set P (Aineq j) (bineq j))
          (hAmin.row_is_facet j))
  have hσ_face :
      ∀ j : Fin mineqA,
        face_set P (Aineq j) (bineq j) = face_set P (Cineq (σ j)) (dineq (σ j)) := by
    intro j
    exact
      Classical.choose_spec
        (is_minimal_representation.facet_surjective
          hCmin
          (face_set P (Aineq j) (bineq j))
          (hAmin.row_is_facet j))
  have hσ_inj : Function.Injective σ := by
    intro j₁ j₂ hσ
    have hfaces :
        face_set P (Aineq j₁) (bineq j₁) = face_set P (Aineq j₂) (bineq j₂) := by
      calc
        face_set P (Aineq j₁) (bineq j₁) = face_set P (Cineq (σ j₁)) (dineq (σ j₁)) :=
          hσ_face j₁
        _ = face_set P (Cineq (σ j₂)) (dineq (σ j₂)) := by rw [hσ]
        _ = face_set P (Aineq j₂) (bineq j₂) := (hσ_face j₂).symm
    exact (is_minimal_representation.facet_injective hAmin) hfaces
  have hcard :
      Fintype.card (Fin mineqA) = Fintype.card (Fin mineqC) := by
    simp [minimal_representation_facet_rows_count P Aeq beq Aineq bineq hAmin,
      minimal_representation_facet_rows_count P Ceq deq Cineq dineq hCmin]
  have hσ_bij : Function.Bijective σ :=
    (Fintype.bijective_iff_injective_and_card σ).2 ⟨hσ_inj, hcard⟩
  refine ⟨Equiv.ofBijective σ hσ_bij, ?_⟩
  intro j
  -- Route correction: the certificate support is not collapsed directly. First turn a matched
  -- facet point into rowwise tightness, then use facet maximality to force all positive support
  -- onto the anchor row `j`.
  obtain ⟨lam, hlam_pos, u, hpair⟩ :=
    same_facet_certificate_eq_pos_smul_add_equalities
      hAmin hCmin (j := j) (k := σ j) (hface_eq := hσ_face j)
  refine ⟨lam, hlam_pos, u, ?_⟩
  exact hpair

end Theorem_3_30
