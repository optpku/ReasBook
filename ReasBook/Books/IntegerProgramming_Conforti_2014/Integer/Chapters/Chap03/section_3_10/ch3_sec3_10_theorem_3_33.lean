/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_1.ch3_sec3_4_1_definition_3_4_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_remark_3_16
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_theorem_3_27
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_1

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- This file reuses the Chapter 3 owners `polyhedron_le_set`, `linealitySpace`, and
-- `linealitySubmodule`, together with mathlib's canonical `Matrix.submatrix` row restriction API.

section Theorem333

variable {m n : ℕ}

/-- Helper for Theorem 3.33: a nonempty matrix equality solution set is the translate of the
kernel of the associated matrix map through any chosen solution point. -/
lemma matrix_solution_set_eq_translate_ker
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι (Fin n) ℝ)
    (rhs : ι → ℝ)
    (x0 : Fin n → ℝ)
    (hx0 : M *ᵥ x0 = rhs) :
    {x : Fin n → ℝ | M *ᵥ x = rhs} =
      (AffineSubspace.mk' x0 M.mulVecLin.ker : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · intro hx
    -- Equal right-hand sides force the displacement from the base solution into the kernel.
    change x ∈ AffineSubspace.mk' x0 M.mulVecLin.ker
    rw [AffineSubspace.mem_mk']
    rw [LinearMap.mem_ker]
    have hsub : M *ᵥ x - M *ᵥ x0 = 0 := by
      rw [hx, hx0, sub_self]
    have hkernel : M *ᵥ (x - x0) = 0 := by
      simpa [Matrix.mulVec_sub] using hsub
    simpa [sub_eq_add_neg] using hkernel
  · intro hx
    -- A kernel displacement preserves the matrix image, so the point stays in the equality slice.
    change x ∈ AffineSubspace.mk' x0 M.mulVecLin.ker at hx
    rw [AffineSubspace.mem_mk'] at hx
    rw [LinearMap.mem_ker] at hx
    have himage : M *ᵥ (x - x0) = 0 := by
      simpa [Matrix.mulVecLin_apply] using hx
    have hsplit : M *ᵥ x - M *ᵥ x0 = 0 := by
      simpa [Matrix.mulVec_sub] using himage
    calc
      M *ᵥ x = M *ᵥ x0 := sub_eq_zero.mp hsplit
      _ = rhs := hx0

/-- Helper for Theorem 3.33: the lineality submodule of an affine subspace written as
`AffineSubspace.mk' x0 L` is exactly the translation submodule `L`. -/
lemma linealitySubmodule_affineSubspace_mk'
    (x0 : Fin n → ℝ)
    (L : Submodule ℝ (Fin n → ℝ)) :
    linealitySubmodule ((AffineSubspace.mk' x0 L : Set (Fin n → ℝ))) = L := by
  ext r
  rw [mem_linealitySubmodule_iff, mem_linealitySpace_iff]
  constructor
  · intro hr
    -- Evaluating the lineality condition at the base point recovers the translation vector.
    have hx0_mem : x0 ∈ (AffineSubspace.mk' x0 L : Set (Fin n → ℝ)) := by
      simp [AffineSubspace.mem_mk']
    have hx0_add : x0 + (1 : ℝ) • r ∈ (AffineSubspace.mk' x0 L : Set (Fin n → ℝ)) := by
      exact hr hx0_mem 1
    have hx0_add' : x0 + (1 : ℝ) • r - x0 ∈ L := by
      simpa [AffineSubspace.mem_mk'] using hx0_add
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx0_add'
  · intro hr x hx a
    -- Translating by a vector from `L` keeps the affine translate `x0 + L` invariant.
    have hx' : x - x0 ∈ L := by
      simpa [AffineSubspace.mem_mk'] using hx
    change x + a • r - x0 ∈ L
    have har : a • r ∈ L := L.smul_mem a hr
    have hadd : x - x0 + a • r ∈ L := L.add_mem hx' har
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd

/-- Helper for Theorem 3.33: every lineality direction of a nonempty set lies in the direction of
its affine span. -/
lemma linealitySubmodule_le_direction_of_nonempty_set
    {S : Set (Fin n → ℝ)}
    (hS_nonempty : S.Nonempty) :
    linealitySubmodule S ≤ (affineSpan ℝ S).direction := by
  intro r hr
  obtain ⟨x0, hx0S⟩ := hS_nonempty
  have hx0_aff : x0 ∈ affineSpan ℝ S := subset_affineSpan ℝ S hx0S
  rw [mem_linealitySubmodule_iff, mem_linealitySpace_iff] at hr
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff]
  refine ⟨x0 + r, ?_, ?_⟩
  · -- Translate the base point once in the lineality direction to stay inside the affine span.
    have hx0_add : x0 + r ∈ S := by
      simpa using hr hx0S (1 : ℝ)
    exact subset_affineSpan ℝ S hx0_add
  · -- The translated point differs from the base point by the prescribed direction `r`.
    ext i
    simp

/-- Helper for Theorem 3.33: if a nonempty exposed face has the same affine-span direction
dimension as the ambient lineality space, then its affine direction is exactly the face
lineality submodule. -/
lemma affine_direction_eq_linealitySubmodule_of_nonempty_exposed_face_finrank_eq
    (P F : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hF_nonempty : F.Nonempty)
    (hF_exposed : IsExposed ℝ P F)
    (hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction =
        Module.finrank ℝ (linealitySubmodule P)) :
    (affineSpan ℝ F).direction = linealitySubmodule F := by
  have hLineality :
      linealitySpace F = linealitySpace P :=
    linealitySpace_eq_of_nonempty_face hP_polyhedron hF_exposed hF_nonempty
  have hLinealitySubmodule :
      linealitySubmodule F = linealitySubmodule P := by
    -- The face and the ambient polyhedron have the same lineality space, so their submodules
    -- coincide after repackaging the carrier set as a submodule.
    ext r
    rw [mem_linealitySubmodule_iff, mem_linealitySubmodule_iff, hLineality]
  have hle :
      linealitySubmodule F ≤ (affineSpan ℝ F).direction :=
    linealitySubmodule_le_direction_of_nonempty_set hF_nonempty
  have hfinrank :
      Module.finrank ℝ (linealitySubmodule F) =
        Module.finrank ℝ (affineSpan ℝ F).direction := by
    -- Rewrite the ambient lineality dimension through the face lineality submodule.
    calc
      Module.finrank ℝ (linealitySubmodule F)
          = Module.finrank ℝ (linealitySubmodule P) := by
              rw [hLinealitySubmodule]
      _ = Module.finrank ℝ (affineSpan ℝ F).direction := hF_dim.symm
  -- Equal finite dimensions upgrade the inclusion to equality.
  exact (Submodule.eq_of_le_of_finrank_eq hle hfinrank).symm

/-- Helper for Theorem 3.33: an exposed face whose affine-span dimension already equals the
ambient lineality dimension is minimal. -/
lemma minimal_face_of_exposed_face_finrank_eq_linealitySubmodule
    (P F : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (hF_nonempty : F.Nonempty)
    (hF_exposed : IsExposed ℝ P F)
    (hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction =
        Module.finrank ℝ (linealitySubmodule P)) :
    IsMinimalFaceOf ℝ P F := by
  have hdir :
      (affineSpan ℝ F).direction = linealitySubmodule F :=
    affine_direction_eq_linealitySubmodule_of_nonempty_exposed_face_finrank_eq
      P F hP_polyhedron hF_nonempty hF_exposed hF_dim
  rw [isMinimalFaceOf_iff]
  refine ⟨hF_nonempty, hF_exposed.isExtreme, ?_⟩
  intro G hG_nonempty hG_extreme hGF
  have hG_extreme_in_F : IsExtreme ℝ F G := by
    -- Restrict the ambient extremality to the exposed face `F`.
    exact hG_extreme.mono hF_exposed.isExtreme.subset hGF
  obtain ⟨x0, hx0G⟩ := hG_nonempty
  have hx0F : x0 ∈ F := hGF hx0G
  intro y hyF
  let r : Fin n → ℝ := y - x0
  have hy_dir : y -ᵥ x0 ∈ (affineSpan ℝ F).direction :=
    AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ F hyF)
      (subset_affineSpan ℝ F hx0F)
  have hr_lin : r ∈ linealitySubmodule F := by
    -- Route correction: after proving the direction equality once, the midpoint argument runs
    -- inside `F` without any further dimension calculations.
    simpa [r, hdir, vsub_eq_sub] using hy_dir
  rw [mem_linealitySubmodule_iff, mem_linealitySpace_iff] at hr_lin
  have hmirror' : x0 + (-1 : ℝ) • r ∈ F := hr_lin hx0F (-1)
  have hmirror : x0 - r ∈ F := by
    simpa [sub_eq_add_neg] using hmirror'
  have hseg : x0 ∈ openSegment ℝ (x0 - r) (x0 + r) := by
    simpa [r] using (mem_openSegment_sub_add (𝕜 := ℝ) x0 r)
  have hy_in_G : x0 + r ∈ G :=
    hG_extreme_in_F.right_mem_of_mem_openSegment
      hmirror (by simpa [r] using hyF) hx0G hseg
  simpa [r] using hy_in_G

/-- Helper for Theorem 3.33: translating a point of a minimal face by any ambient lineality
direction stays inside that minimal face. -/
lemma point_translate_linealitySubmodule_subset_of_minimal_face
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (hF_minimal : IsMinimalFaceOf ℝ (polyhedron_le_set A b) F)
    (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ F) :
    (AffineSubspace.mk' x0 (linealitySubmodule (polyhedron_le_set A b)) :
      Set (Fin n → ℝ)) ⊆ F := by
  intro x hx
  have hx_dir : x - x0 ∈ linealitySubmodule (polyhedron_le_set A b) := by
    -- Membership in the affine translate records that the displacement from `x0` is lineal.
    simpa [AffineSubspace.mem_mk'] using hx
  rw [mem_linealitySubmodule_iff, mem_linealitySpace_iff] at hx_dir
  have hx0P : x0 ∈ polyhedron_le_set A b := hF_minimal.isExtreme.subset hx0
  have hleft : x0 - (x - x0) ∈ polyhedron_le_set A b := by
    -- The ambient lineality direction keeps the polyhedron invariant in the negative direction.
    have hleft' : x0 + (-1 : ℝ) • (x - x0) ∈ polyhedron_le_set A b := hx_dir hx0P (-1)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hleft'
  have hright : x0 + (x - x0) ∈ polyhedron_le_set A b := by
    -- The same lineality direction also keeps the positive translate inside the polyhedron.
    simpa using hx_dir hx0P (1 : ℝ)
  have hsegment : x0 ∈ openSegment ℝ (x0 - (x - x0)) (x0 + (x - x0)) := by
    -- The base point sits in the open segment between its opposite lineality translates.
    simpa using (mem_openSegment_sub_add (𝕜 := ℝ) x0 (x - x0))
  have hxF : x0 + (x - x0) ∈ F :=
    hF_minimal.isExtreme.right_mem_of_mem_openSegment hleft hright hx0 hsegment
  -- Midpoint extremality upgrades the ambient lineality translate back into the minimal face.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxF

/-- Helper for Theorem 3.33: once an exposed face is normalized to a translate of the ambient
lineality submodule, midpoint extremality makes it a minimal face. -/
lemma translate_linealitySubmodule_isMinimalFaceOf
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (hF_face : IsExposed ℝ (polyhedron_le_set A b) F)
    (hF_nonempty : F.Nonempty)
    (x0 : Fin n → ℝ)
    (hF_eq :
      F = (AffineSubspace.mk' x0 (linealitySubmodule (polyhedron_le_set A b)) :
        Set (Fin n → ℝ))) :
    IsMinimalFaceOf ℝ (polyhedron_le_set A b) F := by
  have hPolyhedron : is_polyhedron (polyhedron_le_set A b) := ⟨m, A, b, rfl⟩
  have hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction =
        Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) := by
    -- Rewriting `F` as a translate makes its affine-span direction definitionally equal to the
    -- ambient lineality submodule.
    rw [hF_eq, AffineSubspace.affineSpan_coe, AffineSubspace.direction_mk']
  exact minimal_face_of_exposed_face_finrank_eq_linealitySubmodule
    (polyhedron_le_set A b) F hPolyhedron hF_nonempty hF_face hF_dim

/-- Helper for Theorem 3.33: if a point satisfies the rows indexed by `U` at equality but still
lies outside `polyhedron_le_set A b`, then some row outside `U` is strictly violated. -/
lemma exists_violated_row_of_not_mem_polyhedron_on_universally_active_slice
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (U : Set (Fin m))
    {x : Fin n → ℝ}
    (hUx :
      (A.submatrix (Subtype.val : {i // i ∈ U} → Fin m) id) *ᵥ x =
        b ∘ (Subtype.val : {i // i ∈ U} → Fin m))
    (hx_not_mem : x ∉ polyhedron_le_set A b) :
    ∃ j : Fin m, j ∉ U ∧ b j < (A *ᵥ x) j := by
  by_contra hno
  have hx_mem : x ∈ polyhedron_le_set A b := by
    intro j
    by_cases hjU : j ∈ U
    · -- Rows from `U` are forced to hold at equality by the restricted system.
      let jj : {i // i ∈ U} := ⟨j, hjU⟩
      have hj_eq := congrArg (fun v ↦ v jj) hUx
      have hrow_eq : (A *ᵥ x) j = b j := by
        simpa [jj, Matrix.mulVec] using hj_eq
      exact le_of_eq hrow_eq
    · -- Any row outside `U` would contradict the assumption that no strict violation exists.
      have hnot_lt : ¬ b j < (A *ᵥ x) j := by
        intro hj_lt
        exact hno ⟨j, hjU, hj_lt⟩
      exact le_of_not_gt hnot_lt
  exact hx_not_mem hx_mem

/-- Helper for Theorem 3.33: if a row-restricted submatrix has the same rank as `A`, then its
kernel is exactly the ambient polyhedron's lineality submodule. -/
lemma submatrix_kernel_eq_linealitySubmodule_of_rank_eq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin m))
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (hI_rank :
      (A.submatrix (Subtype.val : {i // i ∈ I} → Fin m) id).rank = A.rank) :
    (A.submatrix (Subtype.val : {i // i ∈ I} → Fin m) id).mulVecLin.ker =
      linealitySubmodule (polyhedron_le_set A b) := by
  let AI : Matrix {i // i ∈ I} (Fin n) ℝ :=
    A.submatrix (Subtype.val : {i // i ∈ I} → Fin m) id
  have hlineality_eq_ker :
      linealitySubmodule (polyhedron_le_set A b) = A.mulVecLin.ker := by
    ext r
    rw [mem_linealitySubmodule_iff, LinearMap.mem_ker,
      polyhedron_linealitySpace_eq_kernel_set A b hP_nonempty]
    simp
  have hlineality_le :
      linealitySubmodule (polyhedron_le_set A b) ≤ AI.mulVecLin.ker := by
    intro r hr
    rw [LinearMap.mem_ker]
    have hrA : A *ᵥ r = 0 := by
      rw [mem_linealitySubmodule_iff,
        polyhedron_linealitySpace_eq_kernel_set A b hP_nonempty] at hr
      exact hr
    -- Restricting a zero row-evaluation system to the selected rows preserves vanishing.
    ext i
    simpa [AI, Matrix.mulVec] using congrArg (fun v ↦ v i.1) hrA
  have hAI_finrank :
      Module.finrank ℝ AI.mulVecLin.ker = n - AI.rank := by
    simpa using finrank_matrix_kernel_eq_card_sub_rank AI
  have hlineality_finrank :
      Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) = n - A.rank := by
    calc
      Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b))
          = Module.finrank ℝ A.mulVecLin.ker := by
              rw [hlineality_eq_ker]
      _ = n - A.rank := by
            simpa using finrank_matrix_kernel_eq_card_sub_rank A
  have hfinrank_eq :
      Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) =
        Module.finrank ℝ AI.mulVecLin.ker := by
    rw [hlineality_finrank, hAI_finrank, hI_rank]
  -- Equal rank forces equal nullity, so the lineality submodule already exhausts the restricted
  -- kernel.
  exact (Submodule.eq_of_le_of_finrank_eq hlineality_le hfinrank_eq).symm

/-- Helper for Theorem 3.33: if a row is not universally active on an active-constraint
description of `F`, then some point of `F` is strict on that row. -/
lemma exists_strict_point_of_not_universally_active_row
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (I : Set (Fin m))
    (j : Fin m)
    (hF_eq : F = active_constraint_face A b I)
    (hj_not_universal : ¬ ∀ y ∈ F, (A *ᵥ y) j = b j) :
    ∃ y ∈ F, (A *ᵥ y) j < b j := by
  by_contra hno
  have hno' : ∀ y ∈ F, ¬ (A *ᵥ y) j < b j := by
    intro y hyF hy_lt
    exact hno ⟨y, hyF, hy_lt⟩
  have hj_universal : ∀ y ∈ F, (A *ᵥ y) j = b j := by
    intro y hyF
    have hy_face : y ∈ active_constraint_face A b I := by
      simpa [hF_eq] using hyF
    by_cases hjI : j ∈ I
    · -- Active rows are equalities by definition of `active_constraint_face`.
      exact (mem_active_constraint_face_iff.mp hy_face).1 j hjI
    · -- On inactive rows, feasibility plus the absence of strict witnesses forces equality.
      have hy_le : (A *ᵥ y) j ≤ b j :=
        (mem_active_constraint_face_iff.mp hy_face).2 j hjI
      exact le_antisymm hy_le (le_of_not_gt (hno' y hyF))
  exact hj_not_universal hj_universal

/-- Helper for Theorem 3.33: inserting a row that is not universally active on `F` cuts out a
proper exposed subface of the active-constraint description of `F`. -/
lemma active_constraint_face_insert_ssubset_of_not_universally_active
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (I : Set (Fin m))
    (j : Fin m)
    (hF_eq : F = active_constraint_face A b I)
    (hj_not_universal : ¬ ∀ y ∈ F, (A *ᵥ y) j = b j) :
    active_constraint_face A b (insert j I) ⊂ F := by
  refine Set.ssubset_iff_subset_ne.mpr ?_
  constructor
  · intro x hx
    have hx_face : x ∈ active_constraint_face A b I := by
      rcases mem_active_constraint_face_iff.mp hx with ⟨hEq, hLe⟩
      refine (mem_active_constraint_face_iff).2 ?_
      constructor
      · intro i hiI
        exact hEq i (by simp [hiI])
      · intro i hiI
        by_cases hij : i = j
        · exact le_of_eq (hEq i (by simp [hij]))
        · have hi_insert : i ∉ insert j I := by
            simp [hiI, hij]
          exact hLe i hi_insert
    simpa [hF_eq] using hx_face
  · rcases
      exists_strict_point_of_not_universally_active_row
        A b F I j hF_eq hj_not_universal with ⟨y, hyF, hy_lt⟩
    intro hEq
    have hy_insert : y ∈ active_constraint_face A b (insert j I) := by
      simpa [hEq] using hyF
    have hy_eq : (A *ᵥ y) j = b j :=
      (mem_active_constraint_face_iff.mp hy_insert).1 j (by simp)
    exact (ne_of_lt hy_lt) hy_eq

/-- Helper for Theorem 3.33: a finite family of rows that are not universally active on an
active-constraint face admits one common witness point that is strict on all of them
simultaneously. -/
lemma exists_strict_point_on_finset_of_active_constraint_face
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (I : Set (Fin m))
    (J : Finset (Fin m))
    (hF_nonempty : F.Nonempty)
    (hF_eq : F = active_constraint_face A b I)
    (hJ : ∀ j ∈ J, ¬ ∀ y ∈ F, (A *ᵥ y) j = b j) :
    ∃ y ∈ F, ∀ j ∈ J, (A *ᵥ y) j < b j := by
  classical
  let A' : Matrix (Fin (m + m)) (Fin n) ℝ := activeConstraintFaceMatrix A I
  let b' : Fin (m + m) → ℝ := activeConstraintFaceRhs b I
  let JAux : Finset (Fin (m + m)) := J.image (Fin.castAdd m)
  have hAux_nonempty : (polyhedron_le_set A' b').Nonempty := by
    obtain ⟨x, hxF⟩ := hF_nonempty
    refine ⟨x, ?_⟩
    simpa [A', b', hF_eq, active_constraint_face_eq_polyhedronAux] using hxF
  have hAux_strict :
      ∀ j' ∈ JAux, ∃ x ∈ polyhedron_le_set A' b', (A' *ᵥ x) j' < b' j' := by
    intro j' hj'
    rcases Finset.mem_image.mp hj' with ⟨j, hjJ, rfl⟩
    rcases
        exists_strict_point_of_not_universally_active_row
          A b F I j hF_eq (hJ j hjJ) with
      ⟨x, hxF, hx_strict⟩
    refine ⟨x, ?_, ?_⟩
    · -- The strict witness for the original face is also feasible for its auxiliary polyhedron.
      simpa [A', b', hF_eq, active_constraint_face_eq_polyhedronAux] using hxF
    · -- The copied upper-half auxiliary row is exactly the original row `j`.
      simpa [A', b', Matrix.mulVec, activeConstraintFaceMatrix_castAdd,
        activeConstraintFaceRhs_castAdd] using hx_strict
  rcases exists_mem_polyhedron_le_set_strict_on_finset A' b' JAux hAux_nonempty hAux_strict with
    ⟨y0, hy0Aux, hy0_strict⟩
  refine ⟨y0, ?_, ?_⟩
  · -- Transport the auxiliary witness back to the original active-constraint face.
    simpa [A', b', hF_eq, active_constraint_face_eq_polyhedronAux] using hy0Aux
  · intro j hjJ
    have hjAux : Fin.castAdd m j ∈ JAux := Finset.mem_image.mpr ⟨j, hjJ, rfl⟩
    -- Reading the strict auxiliary inequality on the copied row recovers the original row.
    simpa [A', b', Matrix.mulVec, activeConstraintFaceMatrix_castAdd,
      activeConstraintFaceRhs_castAdd] using hy0_strict (Fin.castAdd m j) hjAux

/-- Helper for Theorem 3.33: a nonempty active-constraint face contains one point that is strict
on every row that is not universally active on that face. -/
lemma exists_strict_point_on_all_nonuniversal_rows
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (I : Set (Fin m))
    (hF_nonempty : F.Nonempty)
    (hF_eq : F = active_constraint_face A b I) :
    ∃ y0 ∈ F, ∀ j : Fin m,
      j ∉ {i : Fin m | ∀ y ∈ F, (A *ᵥ y) i = b i} → (A *ᵥ y0) j < b j := by
  classical
  let J : Finset (Fin m) := Finset.univ.filter (fun j ↦ ¬ ∀ y ∈ F, (A *ᵥ y) j = b j)
  have hJ : ∀ j ∈ J, ¬ ∀ y ∈ F, (A *ᵥ y) j = b j := by
    intro j hjJ
    simpa [J] using hjJ
  rcases
      exists_strict_point_on_finset_of_active_constraint_face
        A b F I J hF_nonempty hF_eq hJ with
    ⟨y0, hy0F, hy0_strict⟩
  refine ⟨y0, hy0F, ?_⟩
  intro j hj_not_universal
  have hj_not_all : ¬ ∀ y ∈ F, (A *ᵥ y) j = b j := by
    simpa using hj_not_universal
  have hjJ : j ∈ J := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨by simp, hj_not_all⟩
  -- The finite strictness witness specializes to each non-universally-active row.
  exact hy0_strict j hjJ

/-- Helper for Theorem 3.33: if a segment parameter stays below the first hit time of row `i`,
then the row value along the segment is still at most `b i`. -/
lemma row_eval_segment_le_of_le_hit_time
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {y0 x z : Fin n → ℝ}
    {i : Fin m}
    {t : ℝ}
    (hz : z = (1 - t) • y0 + t • x)
    (hy0_lt : (A *ᵥ y0) i < b i)
    (hx_gt : b i < (A *ᵥ x) i)
    (ht_le : t ≤ (b i - (A *ᵥ y0) i) / ((A *ᵥ x) i - (A *ᵥ y0) i)) :
    (A *ᵥ z) i ≤ b i := by
  have hden_pos : 0 < (A *ᵥ x) i - (A *ᵥ y0) i := by
    linarith
  have ht_mul :
      t * ((A *ᵥ x) i - (A *ᵥ y0) i) ≤ b i - (A *ᵥ y0) i := by
    exact (le_div_iff₀ hden_pos).mp ht_le
  have hz_row :
      (A *ᵥ z) i =
        (1 - t) * (A *ᵥ y0) i + t * (A *ᵥ x) i := by
    -- Expand the segment row by row using linearity of matrix-vector multiplication.
    rw [hz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [Pi.add_apply, Pi.smul_apply, sub_eq_add_neg]
  -- Repackage the row value as the base value plus the displacement toward `x`.
  rw [hz_row]
  have hz_row' :
      (1 - t) * (A *ᵥ y0) i + t * (A *ᵥ x) i =
        (A *ᵥ y0) i + t * ((A *ᵥ x) i - (A *ᵥ y0) i) := by
    ring
  rw [hz_row']
  linarith

/-- Helper for Theorem 3.33: among the finitely many non-universal rows violated by `x`, one
attains the earliest segment hit time from the globally strict base point `y0`. -/
lemma exists_min_hit_row_on_segment_of_violated_finset
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (U : Set (Fin m))
    [DecidablePred fun r : Fin m ↦ r ∈ U]
    (y0 x : Fin n → ℝ)
    (hVx_nonempty :
      (Finset.univ.filter
        (fun r : Fin m ↦ r ∉ U ∧ b r < (A *ᵥ x) r)).Nonempty)
    (hy0_strict :
      ∀ r : Fin m, r ∉ U → (A *ᵥ y0) r < b r) :
    ∃ j : Fin m,
      j ∈ Finset.univ.filter
          (fun r : Fin m ↦ r ∉ U ∧ b r < (A *ᵥ x) r) ∧
        0 <
          (b j - (A *ᵥ y0) j) / ((A *ᵥ x) j - (A *ᵥ y0) j) ∧
        (b j - (A *ᵥ y0) j) / ((A *ᵥ x) j - (A *ᵥ y0) j) < 1 ∧
        ∀ r ∈ Finset.univ.filter
            (fun r : Fin m ↦ r ∉ U ∧ b r < (A *ᵥ x) r),
          (b j - (A *ᵥ y0) j) / ((A *ᵥ x) j - (A *ᵥ y0) j) ≤
            (b r - (A *ᵥ y0) r) / ((A *ᵥ x) r - (A *ᵥ y0) r) := by
  let Vx : Finset (Fin m) :=
    Finset.univ.filter (fun r : Fin m ↦ r ∉ U ∧ b r < (A *ᵥ x) r)
  let τ : Fin m → ℝ :=
    fun r ↦ (b r - (A *ᵥ y0) r) / ((A *ᵥ x) r - (A *ᵥ y0) r)
  obtain ⟨j, hjVx, hjmin⟩ := Vx.exists_min_image τ (by simpa [Vx] using hVx_nonempty)
  have hjVx' :
      j ∈ Finset.univ.filter (fun r : Fin m ↦ r ∉ U ∧ b r < (A *ᵥ x) r) := by
    simpa [Vx] using hjVx
  have hj_notU : j ∉ U := by
    exact (Finset.mem_filter.mp hjVx').2.1
  have hj_violate : b j < (A *ᵥ x) j := by
    exact (Finset.mem_filter.mp hjVx').2.2
  have hy0_lt : (A *ᵥ y0) j < b j := hy0_strict j hj_notU
  have hnum_pos : 0 < b j - (A *ᵥ y0) j := by
    linarith
  have hden_pos : 0 < (A *ᵥ x) j - (A *ᵥ y0) j := by
    linarith
  have hτ_pos : 0 < τ j := by
    -- The first-hit time is positive because the base point is strict on row `j`.
    exact div_pos hnum_pos hden_pos
  have hτ_lt_one : τ j < 1 := by
    -- The same row is already violated at `x`, so the hit happens before the segment endpoint.
    dsimp [τ]
    have hnum_lt_den : b j - (A *ᵥ y0) j < (A *ᵥ x) j - (A *ᵥ y0) j := by
      linarith
    exact (div_lt_one hden_pos).2 hnum_lt_den
  refine ⟨j, hjVx', ?_, ?_, ?_⟩
  · simpa [τ] using hτ_pos
  · simpa [τ] using hτ_lt_one
  · intro r hr
    simpa [Vx, τ] using hjmin r hr

/-- Helper for Theorem 3.33: the earliest violated row on the segment from a globally strict base
point to an infeasible equality-slice point produces a point on the inserted active face. -/
lemma mem_active_constraint_face_insert_of_first_hit_time
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (I0 U : Set (Fin m))
    [DecidablePred fun r : Fin m ↦ r ∈ U]
    (hF_eq : F = active_constraint_face A b I0)
    (hU_def : U = {i : Fin m | ∀ y ∈ F, (A *ᵥ y) i = b i})
    {y0 x z : Fin n → ℝ}
    (hy0F : y0 ∈ F)
    (hy0_strict : ∀ r : Fin m, r ∉ U → (A *ᵥ y0) r < b r)
    (hxU :
      (A.submatrix (Subtype.val : {i // i ∈ U} → Fin m) id) *ᵥ x =
        b ∘ (Subtype.val : {i // i ∈ U} → Fin m))
    {j : Fin m}
    (hjVx :
      j ∈ Finset.univ.filter (fun r : Fin m ↦ r ∉ U ∧ b r < (A *ᵥ x) r))
    (ht_pos :
      0 <
        (b j - (A *ᵥ y0) j) / ((A *ᵥ x) j - (A *ᵥ y0) j))
    (ht_lt_one :
      (b j - (A *ᵥ y0) j) / ((A *ᵥ x) j - (A *ᵥ y0) j) < 1)
    (ht_min :
      ∀ r ∈ Finset.univ.filter (fun r : Fin m ↦ r ∉ U ∧ b r < (A *ᵥ x) r),
        (b j - (A *ᵥ y0) j) / ((A *ᵥ x) j - (A *ᵥ y0) j) ≤
          (b r - (A *ᵥ y0) r) / ((A *ᵥ x) r - (A *ᵥ y0) r))
    (hz :
      z =
        (1 - (b j - (A *ᵥ y0) j) / ((A *ᵥ x) j - (A *ᵥ y0) j)) • y0 +
          ((b j - (A *ᵥ y0) j) / ((A *ᵥ x) j - (A *ᵥ y0) j)) • x) :
    z ∈ active_constraint_face A b (insert j I0) := by
  let τ : ℝ := (b j - (A *ᵥ y0) j) / ((A *ᵥ x) j - (A *ᵥ y0) j)
  have hz' : z = (1 - τ) • y0 + τ • x := by
    simpa [τ] using hz
  have ht_pos' : 0 < τ := by
    simpa [τ] using ht_pos
  have ht_lt_one' : τ < 1 := by
    simpa [τ] using ht_lt_one
  have ht_nonneg : 0 ≤ τ := le_of_lt ht_pos'
  have h_one_sub_nonneg : 0 ≤ 1 - τ := by
    linarith
  have hy0_face : y0 ∈ active_constraint_face A b I0 := by
    simpa [hF_eq] using hy0F
  have hI0_subset_U : I0 ⊆ U := by
    intro i hiI
    have hi_universal : ∀ y ∈ F, (A *ᵥ y) i = b i := by
      intro y hyF
      have hy_face : y ∈ active_constraint_face A b I0 := by
        simpa [hF_eq] using hyF
      exact (mem_active_constraint_face_iff.mp hy_face).1 i hiI
    simpa [hU_def] using hi_universal
  have hxU_eq (i : Fin m) (hiU : i ∈ U) : (A *ᵥ x) i = b i := by
    let ii : {r // r ∈ U} := ⟨i, hiU⟩
    have hii := congrArg (fun v ↦ v ii) hxU
    simpa [ii, Matrix.mulVec] using hii
  have hy0_eq_U (i : Fin m) (hiU : i ∈ U) : (A *ᵥ y0) i = b i := by
    have hi_universal : ∀ y ∈ F, (A *ᵥ y) i = b i := by
      simpa [hU_def] using hiU
    exact hi_universal y0 hy0F
  have hz_row (i : Fin m) :
      (A *ᵥ z) i = (1 - τ) * (A *ᵥ y0) i + τ * (A *ᵥ x) i := by
    -- Expand the segment point rowwise once so every branch can reuse the same formula.
    rw [hz', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [Pi.add_apply, Pi.smul_apply, sub_eq_add_neg]
  have hj_notU : j ∉ U := (Finset.mem_filter.mp hjVx).2.1
  have hj_violate : b j < (A *ᵥ x) j := (Finset.mem_filter.mp hjVx).2.2
  have hy0_lt_j : (A *ᵥ y0) j < b j := hy0_strict j hj_notU
  have hden_pos_j : 0 < (A *ᵥ x) j - (A *ᵥ y0) j := by
    linarith
  have hτ_mul :
      τ * ((A *ᵥ x) j - (A *ᵥ y0) j) = b j - (A *ᵥ y0) j := by
    -- The chosen hit time is exactly the parameter at which row `j` reaches equality.
    dsimp [τ]
    field_simp [ne_of_gt hden_pos_j]
  refine (mem_active_constraint_face_iff).2 ?_
  constructor
  · intro i hi_insert
    by_cases hij : i = j
    · subst i
      rw [hz_row j]
      calc
        (1 - τ) * (A *ᵥ y0) j + τ * (A *ᵥ x) j
            = (A *ᵥ y0) j + τ * ((A *ᵥ x) j - (A *ᵥ y0) j) := by ring
        _ = b j := by
              rw [hτ_mul]
              ring
    · have hiI0 : i ∈ I0 := by
        simpa [hij] using hi_insert
      have hiU : i ∈ U := hI0_subset_U hiI0
      have hy0_eq : (A *ᵥ y0) i = b i := (mem_active_constraint_face_iff.mp hy0_face).1 i hiI0
      have hx_eq : (A *ᵥ x) i = b i := hxU_eq i hiU
      rw [hz_row i, hy0_eq, hx_eq]
      ring
  · intro i hi_insert
    by_cases hiVx :
        i ∈ Finset.univ.filter (fun r : Fin m ↦ r ∉ U ∧ b r < (A *ᵥ x) r)
    · have hi_notU : i ∉ U := (Finset.mem_filter.mp hiVx).2.1
      have hi_violate : b i < (A *ᵥ x) i := (Finset.mem_filter.mp hiVx).2.2
      exact
        row_eval_segment_le_of_le_hit_time
          A b hz' (hy0_strict i hi_notU) hi_violate (ht_min i hiVx)
    · by_cases hiU : i ∈ U
      · have hy0_eq : (A *ᵥ y0) i = b i := hy0_eq_U i hiU
        have hx_eq : (A *ᵥ x) i = b i := hxU_eq i hiU
        rw [hz_row i, hy0_eq, hx_eq]
        ring_nf
        nlinarith
      · have hy0_le : (A *ᵥ y0) i ≤ b i := le_of_lt (hy0_strict i hiU)
        have hx_le : (A *ᵥ x) i ≤ b i := by
          have hnot_violate : ¬ b i < (A *ᵥ x) i := by
            intro hi_violate
            exact hiVx (Finset.mem_filter.mpr ⟨by simp, hiU, hi_violate⟩)
          exact le_of_not_gt hnot_violate
        rw [hz_row i]
        nlinarith [hy0_le, hx_le, ht_nonneg, h_one_sub_nonneg]

/-- Helper for Theorem 3.33: every point on the universally active equality slice of a minimal
face is feasible for the ambient polyhedron. -/
lemma universally_active_solution_mem_polyhedron_of_minimal_face
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (I0 U : Set (Fin m))
    [DecidablePred fun r : Fin m ↦ r ∈ U]
    (hF_minimal : IsMinimalFaceOf ℝ (polyhedron_le_set A b) F)
    (hF_eq : F = active_constraint_face A b I0)
    (hU_def : U = {i : Fin m | ∀ y ∈ F, (A *ᵥ y) i = b i})
    {x : Fin n → ℝ}
    (hxU :
      (A.submatrix (Subtype.val : {i // i ∈ U} → Fin m) id) *ᵥ x =
        b ∘ (Subtype.val : {i // i ∈ U} → Fin m)) :
    x ∈ polyhedron_le_set A b := by
  by_contra hx_not_mem
  rcases
      exists_strict_point_on_all_nonuniversal_rows
        A b F I0 hF_minimal.nonempty hF_eq with
    ⟨y0, hy0F, hy0_strict_raw⟩
  have hy0_strict : ∀ r : Fin m, r ∉ U → (A *ᵥ y0) r < b r := by
    intro r hr_notU
    have hr_not_universal :
        r ∉ {i : Fin m | ∀ y ∈ F, (A *ᵥ y) i = b i} := by
      simpa [hU_def] using hr_notU
    exact hy0_strict_raw r hr_not_universal
  rcases
      exists_violated_row_of_not_mem_polyhedron_on_universally_active_slice
        A b U hxU hx_not_mem with
    ⟨j, hj_notU, hj_violate⟩
  let Vx : Finset (Fin m) := Finset.univ.filter (fun r : Fin m ↦ r ∉ U ∧ b r < (A *ᵥ x) r)
  have hVx_nonempty : Vx.Nonempty := by
    refine ⟨j, ?_⟩
    exact Finset.mem_filter.mpr ⟨by simp, hj_notU, hj_violate⟩
  rcases
      exists_min_hit_row_on_segment_of_violated_finset
        A b U y0 x (by simpa [Vx] using hVx_nonempty) hy0_strict with
    ⟨j0, hj0Vx, hj0_pos, hj0_lt_one, hj0_min⟩
  let z : Fin n → ℝ :=
    (1 - (b j0 - (A *ᵥ y0) j0) / ((A *ᵥ x) j0 - (A *ᵥ y0) j0)) • y0 +
      ((b j0 - (A *ᵥ y0) j0) / ((A *ᵥ x) j0 - (A *ᵥ y0) j0)) • x
  have hz_insert :
      z ∈ active_constraint_face A b (insert j0 I0) := by
    -- The earliest-hit row turns the boundary point into a point of the inserted active face.
    refine
      mem_active_constraint_face_insert_of_first_hit_time
        A b F I0 U hF_eq hU_def hy0F hy0_strict hxU hj0Vx hj0_pos hj0_lt_one hj0_min ?_
    rfl
  have hj0_not_universal : ¬ ∀ y ∈ F, (A *ᵥ y) j0 = b j0 := by
    have hj0_notU : j0 ∉ U := (Finset.mem_filter.mp hj0Vx).2.1
    simpa [hU_def] using hj0_notU
  have hproper :
      active_constraint_face A b (insert j0 I0) ⊂ F :=
    active_constraint_face_insert_ssubset_of_not_universally_active
      A b F I0 j0 hF_eq hj0_not_universal
  have hF_subset_insert :
      F ⊆ active_constraint_face A b (insert j0 I0) :=
    IsMinimalFaceOf.minimal
      (𝕜 := ℝ)
      (P := polyhedron_le_set A b)
      (F := F)
      (G := active_constraint_face A b (insert j0 I0))
      hF_minimal
      ⟨z, hz_insert⟩
      (active_constraint_face_isExposed A b (insert j0 I0)).isExtreme
      hproper.subset
  have hEq :
      active_constraint_face A b (insert j0 I0) = F :=
    Set.Subset.antisymm hproper.subset hF_subset_insert
  exact hproper.ne hEq

/-- Helper for Theorem 3.33: a point of an active-constraint face that is strict on every
non-universal row admits a small backward step along the ray from any other face point while
remaining in the same face. -/
lemma exists_backward_step_mem_active_constraint_face_of_strict_point
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (I0 U : Set (Fin m))
    (hF_eq : F = active_constraint_face A b I0)
    (hU_def : U = {i : Fin m | ∀ y ∈ F, (A *ᵥ y) i = b i})
    {x y : Fin n → ℝ}
    (hxF : x ∈ F)
    (hyF : y ∈ F)
    (hx_strict : ∀ j : Fin m, j ∉ U → (A *ᵥ x) j < b j) :
    ∃ ε : ℝ, 0 < ε ∧ x - ε • (y - x) ∈ F := by
  classical
  let V : Finset (Fin m) :=
    Finset.univ.filter (fun r : Fin m ↦ r ∉ U ∧ (A *ᵥ y) r < (A *ᵥ x) r)
  have hx_face : x ∈ active_constraint_face A b I0 := by
    simpa [hF_eq] using hxF
  have hy_face : y ∈ active_constraint_face A b I0 := by
    simpa [hF_eq] using hyF
  have hI0_subset_U : I0 ⊆ U := by
    intro i hiI
    have hi_universal : ∀ z ∈ F, (A *ᵥ z) i = b i := by
      intro z hzF
      have hz_face : z ∈ active_constraint_face A b I0 := by
        simpa [hF_eq] using hzF
      exact (mem_active_constraint_face_iff.mp hz_face).1 i hiI
    simpa [hU_def] using hi_universal
  have hx_eq_U (i : Fin m) (hiU : i ∈ U) : (A *ᵥ x) i = b i := by
    have hi_universal : ∀ z ∈ F, (A *ᵥ z) i = b i := by
      simpa [hU_def] using hiU
    exact hi_universal x hxF
  have hy_eq_U (i : Fin m) (hiU : i ∈ U) : (A *ᵥ y) i = b i := by
    have hi_universal : ∀ z ∈ F, (A *ᵥ z) i = b i := by
      simpa [hU_def] using hiU
    exact hi_universal y hyF
  by_cases hV : V.Nonempty
  · let τ : Fin m → ℝ := fun r ↦ (b r - (A *ᵥ x) r) / ((A *ᵥ x) r - (A *ᵥ y) r)
    obtain ⟨j, hjV, hjmin⟩ := V.exists_min_image τ hV
    let ε : ℝ := τ j / 2
    have hj_notU : j ∉ U := (Finset.mem_filter.mp hjV).2.1
    have hj_lt : (A *ᵥ y) j < (A *ᵥ x) j := (Finset.mem_filter.mp hjV).2.2
    have hnum_pos : 0 < b j - (A *ᵥ x) j := by
      linarith [hx_strict j hj_notU]
    have hden_pos : 0 < (A *ᵥ x) j - (A *ᵥ y) j := by
      linarith
    have hε_pos : 0 < ε := by
      dsimp [ε, τ]
      positivity
    have hw_row (i : Fin m) :
        (A *ᵥ (x - ε • (y - x))) i =
          (A *ᵥ x) i + ε * ((A *ᵥ x) i - (A *ᵥ y) i) := by
      -- Expand the backward step rowwise so each row can be handled by one scalar inequality.
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_sub]
      simp [Pi.sub_apply]
      ring
    have hε_le (i : Fin m) (hiV : i ∈ V) : ε ≤ τ i := by
      have hmin : τ j ≤ τ i := hjmin i hiV
      have hτ_nonneg : 0 ≤ τ j := le_of_lt <| by
        have hi_notU : i ∉ U := (Finset.mem_filter.mp hiV).2.1
        have hi_lt : (A *ᵥ y) i < (A *ᵥ x) i := (Finset.mem_filter.mp hiV).2.2
        have hnum_pos_i : 0 < b i - (A *ᵥ x) i := by
          linarith [hx_strict i hi_notU]
        have hden_pos_i : 0 < (A *ᵥ x) i - (A *ᵥ y) i := by
          linarith
        dsimp [τ]
        positivity
      dsimp [ε]
      nlinarith
    refine ⟨ε, hε_pos, ?_⟩
    have hw_face : x - ε • (y - x) ∈ active_constraint_face A b I0 := by
      refine (mem_active_constraint_face_iff).2 ?_
      constructor
      · intro i hiI
        have hiU : i ∈ U := hI0_subset_U hiI
        have hx_eq : (A *ᵥ x) i = b i := (mem_active_constraint_face_iff.mp hx_face).1 i hiI
        have hy_eq : (A *ᵥ y) i = b i := (mem_active_constraint_face_iff.mp hy_face).1 i hiI
        rw [hw_row i, hx_eq, hy_eq]
        ring
      · intro i hiI
        by_cases hiU : i ∈ U
        · have hx_eq : (A *ᵥ x) i = b i := hx_eq_U i hiU
          have hy_eq : (A *ᵥ y) i = b i := hy_eq_U i hiU
          rw [hw_row i, hx_eq, hy_eq]
          ring_nf
          linarith
        · by_cases hiV : i ∈ V
          · have hi_lt : (A *ᵥ y) i < (A *ᵥ x) i := (Finset.mem_filter.mp hiV).2.2
            have hden_pos_i : 0 < (A *ᵥ x) i - (A *ᵥ y) i := by
              linarith
            have hmul :
                ε * ((A *ᵥ x) i - (A *ᵥ y) i) ≤ b i - (A *ᵥ x) i := by
              exact (le_div_iff₀ hden_pos_i).mp (hε_le i hiV)
            rw [hw_row i]
            linarith
          · have hnot_lt : ¬ (A *ᵥ y) i < (A *ᵥ x) i := by
              intro hi_lt
              exact hiV (Finset.mem_filter.mpr ⟨by simp, hiU, hi_lt⟩)
            have hxy_le : (A *ᵥ x) i ≤ (A *ᵥ y) i := le_of_not_gt hnot_lt
            rw [hw_row i]
            nlinarith [hxy_le, hx_strict i hiU, le_of_lt hε_pos]
    simpa [hF_eq] using hw_face
  · refine ⟨1, by norm_num, ?_⟩
    have hw_row (i : Fin m) :
        (A *ᵥ (x - (1 : ℝ) • (y - x))) i =
          2 * (A *ᵥ x) i - (A *ᵥ y) i := by
      -- The unit backward step is the simplest point to test once every problematic row is absent.
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_sub]
      simp [Pi.sub_apply]
      ring
    have hw_face : x - (1 : ℝ) • (y - x) ∈ active_constraint_face A b I0 := by
      refine (mem_active_constraint_face_iff).2 ?_
      constructor
      · intro i hiI
        have hx_eq : (A *ᵥ x) i = b i := (mem_active_constraint_face_iff.mp hx_face).1 i hiI
        have hy_eq : (A *ᵥ y) i = b i := (mem_active_constraint_face_iff.mp hy_face).1 i hiI
        rw [hw_row i, hx_eq, hy_eq]
        ring
      · intro i hiI
        by_cases hiU : i ∈ U
        · have hx_eq : (A *ᵥ x) i = b i := hx_eq_U i hiU
          have hy_eq : (A *ᵥ y) i = b i := hy_eq_U i hiU
          rw [hw_row i, hx_eq, hy_eq]
          linarith
        -- With no decreasing non-universal row, the unit backward step cannot increase any slack.
        · have hnot_lt : ¬ (A *ᵥ y) i < (A *ᵥ x) i := by
            intro hi_lt
            exact hV ⟨i, Finset.mem_filter.mpr ⟨by simp, hiU, hi_lt⟩⟩
          have hxy_le : (A *ᵥ x) i ≤ (A *ᵥ y) i := le_of_not_gt hnot_lt
          rw [hw_row i]
          linarith [hx_strict i hiU]
    simpa [hF_eq] using hw_face

/-- Helper for Theorem 3.33: if an extreme subset of an active-constraint face contains a point
that is strict on every non-universal row, then that extreme subset already equals the whole
active-constraint face. -/
lemma active_constraint_face_subset_of_extreme_mem_and_strict_on_nonuniversal_rows
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F H : Set (Fin n → ℝ))
    (I0 U : Set (Fin m))
    (hF_eq : F = active_constraint_face A b I0)
    (hU_def : U = {i : Fin m | ∀ y ∈ F, (A *ᵥ y) i = b i})
    (hH_extreme : IsExtreme ℝ F H)
    {x : Fin n → ℝ}
    (hxH : x ∈ H)
    (hx_strict : ∀ j : Fin m, j ∉ U → (A *ᵥ x) j < b j) :
    F ⊆ H := by
  intro y hyF
  have hxF : x ∈ F := hH_extreme.subset hxH
  rcases
      exists_backward_step_mem_active_constraint_face_of_strict_point
        A b F I0 U hF_eq hU_def hxF hyF hx_strict with
    ⟨ε, hε_pos, hwF⟩
  have hx_open :
      x ∈ openSegment ℝ (x - ε • (y - x)) y := by
    -- Writing `x` as a strict convex combination of the backward step and `y` lets extremality
    -- recover `y` from the known point `x ∈ H`.
    refine (mem_openSegment_iff_div).2 ?_
    refine ⟨1, ε, by norm_num, hε_pos, ?_⟩
    ext i
    have hε_ne : (1 + ε : ℝ) ≠ 0 := by linarith
    simp [sub_eq_add_neg]
    field_simp [hε_ne]
    ring
  exact hH_extreme.right_mem_of_mem_openSegment hwF hyF hxH hx_open

/-- Helper for Theorem 3.33: every minimal face of a polyhedron is exposed, so the exposed-face
API from part (1) applies to it. -/
lemma minimal_face_isExposed_of_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (hF_minimal : IsMinimalFaceOf ℝ (polyhedron_le_set A b) F) :
    IsExposed ℝ (polyhedron_le_set A b) F := by
  classical
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  let S : Set (Set (Fin n → ℝ)) := {E : Set (Fin n → ℝ) | IsExposed ℝ P E ∧ F ⊆ E}
  have hP_polyhedron : is_polyhedron P := by
    exact ⟨m, A, b, rfl⟩
  have hS_finite : S.Finite := by
    -- Only finitely many exposed faces of a polyhedron can contain the fixed minimal face `F`.
    exact (polyhedron_finite_faces hP_polyhedron).subset fun E hE ↦ hE.1
  have hP_mem : P ∈ S := by
    constructor
    · exact IsExposed.refl P
    · intro x hxF
      exact (IsMinimalFaceOf.subset (𝕜 := ℝ) hF_minimal) hxF
  obtain ⟨E, _, hEmin_raw⟩ := Set.Finite.exists_le_minimal hS_finite hP_mem
  have hEmin : Minimal (fun G : Set (Fin n → ℝ) ↦ IsExposed ℝ P G ∧ F ⊆ G) E := by
    simpa [S] using hEmin_raw
  have hE_exposed : IsExposed ℝ P E := hEmin.prop.1
  have hFE : F ⊆ E := hEmin.prop.2
  by_cases hEF : E = F
  · -- The minimal exposed superset collapses to `F`, so `F` itself is exposed.
    simpa [P, hEF] using hE_exposed
  · obtain ⟨x, hxF⟩ := hF_minimal.nonempty
    have hxE : x ∈ E := hFE hxF
    have hE_nonempty : E.Nonempty := ⟨x, hxE⟩
    obtain ⟨I0, hE_eq⟩ := exists_eq_active_constraint_face_of_isExposed A b E hE_exposed hE_nonempty
    let U : Set (Fin m) := {i : Fin m | ∀ y ∈ E, (A *ᵥ y) i = b i}
    have hF_extreme_in_E : IsExtreme ℝ E F := by
      -- Restrict the ambient minimal-face extremality to the current exposed superset `E`.
      exact hF_minimal.isExtreme.mono hE_exposed.subset hFE
    by_cases hx_strict : ∀ j : Fin m, j ∉ U → (A *ᵥ x) j < b j
    · have hE_subset_F :
          E ⊆ F :=
        active_constraint_face_subset_of_extreme_mem_and_strict_on_nonuniversal_rows
          A b E F I0 U hE_eq rfl hF_extreme_in_E hxF hx_strict
      exact False.elim (hEF (Set.Subset.antisymm hE_subset_F hFE))
    · have hx_face : x ∈ active_constraint_face A b I0 := by
        simpa [hE_eq] using hxE
      have hI0_subset_U : I0 ⊆ U := by
        intro i hiI
        have hi_universal : ∀ y ∈ E, (A *ᵥ y) i = b i := by
          intro y hyE
          have hy_face : y ∈ active_constraint_face A b I0 := by
            simpa [hE_eq] using hyE
          exact (mem_active_constraint_face_iff.mp hy_face).1 i hiI
        simpa [U] using hi_universal
      push Not at hx_strict
      rcases hx_strict with ⟨j, hj_notU, hj_not_lt⟩
      have hj_notI0 : j ∉ I0 := by
        intro hjI
        exact hj_notU (hI0_subset_U hjI)
      have hx_le_j : (A *ᵥ x) j ≤ b j :=
        (mem_active_constraint_face_iff.mp hx_face).2 j hj_notI0
      have hx_eq_j : (A *ᵥ x) j = b j := by
        exact le_antisymm hx_le_j hj_not_lt
      have hx_insert : x ∈ active_constraint_face A b (insert j I0) := by
        refine (mem_active_constraint_face_iff).2 ?_
        constructor
        · intro i hi_insert
          by_cases hij : i = j
          · simpa [hij] using hx_eq_j
          · have hiI0 : i ∈ I0 := by
              simpa [hij] using hi_insert
            exact (mem_active_constraint_face_iff.mp hx_face).1 i hiI0
        · intro i hi_insert
          have hiI0 : i ∉ I0 := by
            intro hiI
            exact hi_insert (by simp [hiI])
          exact (mem_active_constraint_face_iff.mp hx_face).2 i hiI0
      have hj_not_universal : ¬ ∀ y ∈ E, (A *ᵥ y) j = b j := by
        simpa [U] using hj_notU
      have hproper :
          active_constraint_face A b (insert j I0) ⊂ E :=
        active_constraint_face_insert_ssubset_of_not_universally_active
          A b E I0 j hE_eq hj_not_universal
      have hInter_nonempty : (F ∩ active_constraint_face A b (insert j I0)).Nonempty := by
        exact ⟨x, hxF, hx_insert⟩
      have hInter_extreme :
          IsExtreme ℝ P (F ∩ active_constraint_face A b (insert j I0)) := by
        -- Intersect the minimal face with the inserted active face to keep a nonempty extreme
        -- subset of the ambient polyhedron.
        exact hF_minimal.isExtreme.inter (active_constraint_face_isExposed A b (insert j I0)).isExtreme
      have hF_subset_insert : F ⊆ active_constraint_face A b (insert j I0) := by
        have hF_subset_inter :
            F ⊆ F ∩ active_constraint_face A b (insert j I0) :=
          IsMinimalFaceOf.minimal (𝕜 := ℝ) hF_minimal hInter_nonempty hInter_extreme
            Set.inter_subset_left
        intro z hzF
        exact (hF_subset_inter hzF).2
      have hInsert_mem :
          IsExposed ℝ P (active_constraint_face A b (insert j I0)) ∧
            F ⊆ active_constraint_face A b (insert j I0) := by
        exact ⟨active_constraint_face_isExposed A b (insert j I0), hF_subset_insert⟩
      have hEq :
          active_constraint_face A b (insert j I0) = E :=
        Minimal.eq_of_subset hEmin hInsert_mem hproper.subset
      exact False.elim (hproper.ne hEq)

/-- Theorem 3.33 (1). For a nonempty face `F` of the polyhedron `P = {x | A *ᵥ x ≤ b}`, `F` is
minimal if and only if it is the affine solution set of a subsystem of rows of `A *ᵥ x ≤ b`
whose restricted coefficient matrix has the same rank as `A`. -/
theorem isMinimalFaceOf_iff_exists_eq_submatrix_solution_set_and_rank
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (hF_face : IsExposed ℝ (polyhedron_le_set A b) F)
    (hF_nonempty : F.Nonempty) :
    IsMinimalFaceOf ℝ (polyhedron_le_set A b) F ↔
      ∃ I : Set (Fin m),
        F = {x : Fin n → ℝ |
          A.submatrix (Subtype.val : {i // i ∈ I} → Fin m) id *ᵥ x =
            b ∘ (Subtype.val : {i // i ∈ I} → Fin m)} ∧
          (A.submatrix (Subtype.val : {i // i ∈ I} → Fin m) id).rank = A.rank := by
  classical
  constructor
  · intro hF_minimal
    obtain ⟨I0, hI0_eq⟩ := exists_eq_active_constraint_face_of_isExposed A b F hF_face hF_nonempty
    let U : Set (Fin m) := {i : Fin m | ∀ y ∈ F, (A *ᵥ y) i = b i}
    let AU : Matrix {i // i ∈ U} (Fin n) ℝ :=
      A.submatrix (Subtype.val : {i // i ∈ U} → Fin m) id
    have hI0_subset_U : I0 ⊆ U := by
      intro i hiI
      show ∀ y ∈ F, (A *ᵥ y) i = b i
      intro y hyF
      have hy_face : y ∈ active_constraint_face A b I0 := by
        simpa [hI0_eq] using hyF
      exact (mem_active_constraint_face_iff.mp hy_face).1 i hiI
    have hslice_subset_polyhedron :
        {x : Fin n → ℝ | AU *ᵥ x = b ∘ (Subtype.val : {i // i ∈ U} → Fin m)} ⊆
          polyhedron_le_set A b := by
      intro x hx
      exact
        universally_active_solution_mem_polyhedron_of_minimal_face
          A b F I0 U hF_minimal hI0_eq rfl hx
    have hF_eq_slice :
        F = {x : Fin n → ℝ | AU *ᵥ x = b ∘ (Subtype.val : {i // i ∈ U} → Fin m)} := by
      ext x
      constructor
      · intro hxF
        ext i
        -- Every point of the face satisfies every universally active row at equality.
        exact i.2 x hxF
      · intro hxSlice
        have hxP : x ∈ polyhedron_le_set A b := hslice_subset_polyhedron hxSlice
        have hxFace : x ∈ active_constraint_face A b I0 := by
          refine (mem_active_constraint_face_iff).2 ?_
          constructor
          · intro i hiI
            let ii : {r // r ∈ U} := ⟨i, hI0_subset_U hiI⟩
            have hii := congrArg (fun v ↦ v ii) hxSlice
            simpa [AU, ii, Matrix.mulVec] using hii
          · intro i hiI
            exact hxP i
        simpa [hI0_eq] using hxFace
    obtain ⟨x0, hx0F⟩ := hF_nonempty
    have hx0_slice :
        AU *ᵥ x0 = b ∘ (Subtype.val : {i // i ∈ U} → Fin m) := by
      change x0 ∈ {x : Fin n → ℝ | AU *ᵥ x = b ∘ (Subtype.val : {i // i ∈ U} → Fin m)}
      simpa [hF_eq_slice] using hx0F
    have hF_translate :
        F = (AffineSubspace.mk' x0 AU.mulVecLin.ker : Set (Fin n → ℝ)) := by
      calc
        F = {x : Fin n → ℝ | AU *ᵥ x = b ∘ (Subtype.val : {i // i ∈ U} → Fin m)} := hF_eq_slice
        _ = (AffineSubspace.mk' x0 AU.mulVecLin.ker : Set (Fin n → ℝ)) := by
              exact
                matrix_solution_set_eq_translate_ker
                  AU
                  (b ∘ (Subtype.val : {i // i ∈ U} → Fin m))
                  x0
                  hx0_slice
    have hlineality_F_eq_AUker :
        linealitySubmodule F = AU.mulVecLin.ker := by
      rw [hF_translate, linealitySubmodule_affineSubspace_mk']
    have hlineality_F_eq_P :
        linealitySubmodule F = linealitySubmodule (polyhedron_le_set A b) := by
      ext r
      rw [mem_linealitySubmodule_iff, mem_linealitySubmodule_iff,
        linealitySpace_eq_of_nonempty_face ⟨m, A, b, rfl⟩ hF_face ⟨x0, hx0F⟩]
    have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨x0, hF_face.subset hx0F⟩
    have hlineality_P_eq_Aker :
        linealitySubmodule (polyhedron_le_set A b) = A.mulVecLin.ker := by
      ext r
      rw [mem_linealitySubmodule_iff, LinearMap.mem_ker,
        polyhedron_linealitySpace_eq_kernel_set A b hP_nonempty]
      simp
    have hAU_finrank :
        Module.finrank ℝ AU.mulVecLin.ker = n - AU.rank := by
      simpa using finrank_matrix_kernel_eq_card_sub_rank AU
    have hA_finrank :
        Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) = n - A.rank := by
      calc
        Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b))
            = Module.finrank ℝ A.mulVecLin.ker := by
                rw [hlineality_P_eq_Aker]
        _ = n - A.rank := by
              simpa using finrank_matrix_kernel_eq_card_sub_rank A
    have hsub_eq :
        n - AU.rank = n - A.rank := by
      calc
        n - AU.rank = Module.finrank ℝ AU.mulVecLin.ker := by
            symm
            exact hAU_finrank
        _ = Module.finrank ℝ (linealitySubmodule F) := by
              rw [hlineality_F_eq_AUker]
        _ = Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) := by
              rw [hlineality_F_eq_P]
        _ = n - A.rank := hA_finrank
    have hI_rank : AU.rank = A.rank := by
      have hAU_rank_le : AU.rank ≤ n := by
        simpa using Matrix.rank_le_card_width AU
      have hA_rank_le : A.rank ≤ n := Matrix.rank_le_width A
      omega
    exact ⟨U, hF_eq_slice, hI_rank⟩
  · rintro ⟨I, hI_eq, hI_rank⟩
    let AI : Matrix {i // i ∈ I} (Fin n) ℝ :=
      A.submatrix (Subtype.val : {i // i ∈ I} → Fin m) id
    obtain ⟨x0, hx0⟩ := hF_nonempty
    have hx0_AI :
        AI *ᵥ x0 = b ∘ (Subtype.val : {i // i ∈ I} → Fin m) := by
      change x0 ∈ {x : Fin n → ℝ | AI *ᵥ x = b ∘ (Subtype.val : {i // i ∈ I} → Fin m)}
      simpa [AI, hI_eq] using hx0
    have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨x0, hF_face.subset hx0⟩
    have hkernel :
        AI.mulVecLin.ker = linealitySubmodule (polyhedron_le_set A b) :=
      submatrix_kernel_eq_linealitySubmodule_of_rank_eq A b I hP_nonempty hI_rank
    have hF_translate :
        F = (AffineSubspace.mk' x0 (linealitySubmodule (polyhedron_le_set A b)) :
          Set (Fin n → ℝ)) := by
      calc
        F = {x : Fin n → ℝ | AI *ᵥ x = b ∘ (Subtype.val : {i // i ∈ I} → Fin m)} := by
              simpa [AI] using hI_eq
        _ = (AffineSubspace.mk' x0 AI.mulVecLin.ker : Set (Fin n → ℝ)) := by
              exact
                matrix_solution_set_eq_translate_ker
                  AI
                  (b ∘ (Subtype.val : {i // i ∈ I} → Fin m))
                  x0
                  hx0_AI
        _ = (AffineSubspace.mk' x0 (linealitySubmodule (polyhedron_le_set A b)) :
              Set (Fin n → ℝ)) := by
              rw [hkernel]
    exact
      translate_linealitySubmodule_isMinimalFaceOf
        A b F hF_face ⟨x0, hx0⟩ x0 hF_translate

/-- Theorem 3.33 (2). Every minimal face of a polyhedron is the affine translate of its
lineality submodule through any point of that face. -/
theorem minimalFace_eq_point_translate_linealitySubmodule
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (hF_minimal : IsMinimalFaceOf ℝ (polyhedron_le_set A b) F)
    (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ F) :
    F = (AffineSubspace.mk' x0 (linealitySubmodule (polyhedron_le_set A b)) :
      Set (Fin n → ℝ)) := by
  have hF_face : IsExposed ℝ (polyhedron_le_set A b) F :=
    minimal_face_isExposed_of_polyhedron A b F hF_minimal
  have hF_nonempty : F.Nonempty := hF_minimal.nonempty
  obtain ⟨I, hI_eq, hI_rank⟩ :=
    (isMinimalFaceOf_iff_exists_eq_submatrix_solution_set_and_rank
      A b F hF_face hF_nonempty).mp hF_minimal
  let AI : Matrix {i // i ∈ I} (Fin n) ℝ :=
    A.submatrix (Subtype.val : {i // i ∈ I} → Fin m) id
  have hx0_AI : AI *ᵥ x0 = b ∘ (Subtype.val : {i // i ∈ I} → Fin m) := by
    -- The chosen base point belongs to the equality slice produced by part (1).
    have hx0_slice :
        x0 ∈ {x : Fin n → ℝ |
          AI *ᵥ x = b ∘ (Subtype.val : {i // i ∈ I} → Fin m)} := by
      simpa [AI, hI_eq] using hx0
    simpa [AI] using hx0_slice
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨x0, hF_minimal.isExtreme.subset hx0⟩
  have hkernel :
      AI.mulVecLin.ker = linealitySubmodule (polyhedron_le_set A b) :=
    submatrix_kernel_eq_linealitySubmodule_of_rank_eq A b I hP_nonempty hI_rank
  -- Part (1) identifies `F` with the equality slice, and the slice is the translate of its kernel.
  calc
    F = {x : Fin n → ℝ | AI *ᵥ x = b ∘ (Subtype.val : {i // i ∈ I} → Fin m)} := by
          simpa [AI] using hI_eq
    _ = (AffineSubspace.mk' x0 AI.mulVecLin.ker : Set (Fin n → ℝ)) := by
          exact
            matrix_solution_set_eq_translate_ker
              AI
              (b ∘ (Subtype.val : {i // i ∈ I} → Fin m))
              x0
              hx0_AI
    _ = (AffineSubspace.mk' x0 (linealitySubmodule (polyhedron_le_set A b)) :
          Set (Fin n → ℝ)) := by
          rw [hkernel]

/-- Helper for Theorem 3.33: a nonminimal exposed face contains a proper nonempty exposed
subface obtained by activating one additional non-universal row. -/
lemma exists_proper_exposed_subface_of_nonminimal_exposed_face
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (G : Set (Fin n → ℝ))
    (hG_nonempty : G.Nonempty)
    (hG_exposed : IsExposed ℝ (polyhedron_le_set A b) G)
    (hG_not_minimal : ¬ IsMinimalFaceOf ℝ (polyhedron_le_set A b) G) :
    ∃ H : Set (Fin n → ℝ),
      H.Nonempty ∧
        IsExposed ℝ (polyhedron_le_set A b) H ∧
          H ⊂ G := by
  classical
  obtain ⟨I0, hG_eq⟩ := exists_eq_active_constraint_face_of_isExposed A b G hG_exposed hG_nonempty
  let U : Set (Fin m) := {i : Fin m | ∀ y ∈ G, (A *ᵥ y) i = b i}
  have hnot_minimal_witness :
      ¬ ∀ H : Set (Fin n → ℝ),
        H.Nonempty →
          IsExtreme ℝ (polyhedron_le_set A b) H →
            H ⊆ G → G ⊆ H := by
    intro hminimal
    exact hG_not_minimal <|
      (isMinimalFaceOf_iff (𝕜 := ℝ) (P := polyhedron_le_set A b) (F := G)).2
        ⟨hG_nonempty, hG_exposed.isExtreme, fun H hH_nonempty hH_extreme hHG ↦
          hminimal H hH_nonempty hH_extreme hHG⟩
  push Not at hnot_minimal_witness
  obtain ⟨H, hH_nonempty, hH_extreme, hHG, hG_not_subset_H⟩ := hnot_minimal_witness
  obtain ⟨x, hxH⟩ := hH_nonempty
  have hxG : x ∈ G := hHG hxH
  have hH_extreme_in_G : IsExtreme ℝ G H := by
    -- Restrict the ambient extremality to the currently exposed face `G`.
    exact hH_extreme.mono hG_exposed.isExtreme.subset hHG
  by_cases hx_strict : ∀ j : Fin m, j ∉ U → (A *ᵥ x) j < b j
  · have hG_subset_H :
        G ⊆ H :=
      active_constraint_face_subset_of_extreme_mem_and_strict_on_nonuniversal_rows
        A b G H I0 U hG_eq rfl hH_extreme_in_G hxH hx_strict
    exact False.elim (hG_not_subset_H hG_subset_H)
  · have hI0_subset_U : I0 ⊆ U := by
      intro i hiI
      have hi_universal : ∀ y ∈ G, (A *ᵥ y) i = b i := by
        intro y hyG
        have hy_face : y ∈ active_constraint_face A b I0 := by
          simpa [hG_eq] using hyG
        exact (mem_active_constraint_face_iff.mp hy_face).1 i hiI
      simpa [U] using hi_universal
    push Not at hx_strict
    obtain ⟨j, hj_notU, hj_not_lt⟩ := hx_strict
    have hx_face : x ∈ active_constraint_face A b I0 := by
      simpa [hG_eq] using hxG
    have hj_notI0 : j ∉ I0 := by
      intro hjI
      exact hj_notU (hI0_subset_U hjI)
    have hx_le_j : (A *ᵥ x) j ≤ b j :=
      (mem_active_constraint_face_iff.mp hx_face).2 j hj_notI0
    have hx_eq_j : (A *ᵥ x) j = b j := by
      exact le_antisymm hx_le_j hj_not_lt
    have hx_insert : x ∈ active_constraint_face A b (insert j I0) := by
      -- The first row that is tight at `x` but not universal on `G` cuts out the next face.
      refine (mem_active_constraint_face_iff).2 ?_
      constructor
      · intro i hi_insert
        by_cases hij : i = j
        · simpa [hij] using hx_eq_j
        · have hiI0 : i ∈ I0 := by
            simpa [hij] using hi_insert
          exact (mem_active_constraint_face_iff.mp hx_face).1 i hiI0
      · intro i hi_insert
        have hiI0 : i ∉ I0 := by
          intro hiI
          exact hi_insert (by simp [hiI])
        exact (mem_active_constraint_face_iff.mp hx_face).2 i hiI0
    have hj_not_universal : ¬ ∀ y ∈ G, (A *ᵥ y) j = b j := by
      simpa [U] using hj_notU
    have hproper :
        active_constraint_face A b (insert j I0) ⊂ G :=
      active_constraint_face_insert_ssubset_of_not_universally_active
        A b G I0 j hG_eq hj_not_universal
    exact
      ⟨active_constraint_face A b (insert j I0), ⟨x, hx_insert⟩,
        active_constraint_face_isExposed A b (insert j I0), hproper⟩

/-- Helper for Theorem 3.33: if an exposed face has affine-span direction strictly larger than the
ambient lineality space, then it contains a nonempty exposed codimension-one subface. -/
lemma exists_exposed_subface_of_pred_finrank_of_lineality_lt
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (G : Set (Fin n → ℝ))
    (hG_nonempty : G.Nonempty)
    (hG_exposed : IsExposed ℝ (polyhedron_le_set A b) G)
    (hLinealityLt :
      Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) <
        Module.finrank ℝ (affineSpan ℝ G).direction) :
    ∃ H : Set (Fin n → ℝ),
      H.Nonempty ∧
        IsExposed ℝ (polyhedron_le_set A b) H ∧
          H ⊆ G ∧
            Module.finrank ℝ (affineSpan ℝ H).direction + 1 =
              Module.finrank ℝ (affineSpan ℝ G).direction := by
  classical
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  have hP_polyhedron : is_polyhedron P := by
    exact ⟨m, A, b, rfl⟩
  have hG_not_minimal : ¬ IsMinimalFaceOf ℝ P G := by
    intro hG_minimal
    obtain ⟨x0, hx0G⟩ := hG_nonempty
    have hG_translate :
        G = (AffineSubspace.mk' x0 (linealitySubmodule P) : Set (Fin n → ℝ)) :=
      minimalFace_eq_point_translate_linealitySubmodule A b G hG_minimal x0 hx0G
    have hG_dim :
        Module.finrank ℝ (affineSpan ℝ G).direction =
          Module.finrank ℝ (linealitySubmodule P) := by
      rw [hG_translate, AffineSubspace.affineSpan_coe, AffineSubspace.direction_mk']
    have hG_dim' :
        Module.finrank ℝ (affineSpan ℝ G).direction =
          Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) := by
      simpa [P] using hG_dim
    omega
  obtain ⟨H0, hH0_nonempty, hH0_exposed, hH0_ssubset⟩ :=
    exists_proper_exposed_subface_of_nonminimal_exposed_face
      A b G hG_nonempty hG_exposed hG_not_minimal
  obtain ⟨I0, hG_eq⟩ := exists_eq_active_constraint_face_of_isExposed A b G hG_exposed hG_nonempty
  let A' : Matrix (Fin (m + m)) (Fin n) ℝ := activeConstraintFaceMatrix A I0
  let b' : Fin (m + m) → ℝ := activeConstraintFaceRhs b I0
  have hG_aux_eq : polyhedron_le_set A' b' = G := by
    simpa [A', b', hG_eq] using (active_constraint_face_eq_polyhedronAux A b I0).symm
  have hG_polyhedron : is_polyhedron G := by
    -- Repackage the exposed face `G` as the auxiliary polyhedron that cuts out its active rows.
    rw [← hG_aux_eq]
    exact ⟨m + m, A', b', rfl⟩
  have hH0_local : IsExposed ℝ G H0 := by
    -- A face of the ambient polyhedron contained in `G` is exactly a face of the polyhedron `G`.
    exact (isExposed_iff_isExposed_of_subset hP_polyhedron hG_exposed).2
      ⟨hH0_exposed, hH0_ssubset.subset⟩
  have hH0_proper_local : is_proper_face G H0 := by
    exact (is_proper_face_iff).2 ⟨hH0_local, hH0_nonempty, hH0_ssubset⟩
  obtain ⟨H, hH_facet_local, hH0H⟩ :=
    exists_is_facet_superset_of_is_proper_face hG_polyhedron hH0_proper_local
  have hH_proper_local : is_proper_face G H := is_facet_to_is_proper_face hH_facet_local
  rcases is_proper_face_iff.mp hH_proper_local with ⟨hH_local, hH_nonempty, hH_ssubset⟩
  have hH_ambient_pair :
      IsExposed ℝ P H ∧ H ⊆ G :=
    (isExposed_iff_isExposed_of_subset hP_polyhedron hG_exposed).1 hH_local
  have hG_nonempty_aux :
      (polyhedron_le_set A' b').Nonempty := by
    simpa [A', b', hG_eq, active_constraint_face_eq_polyhedronAux] using hG_nonempty
  have hH_local_aux :
      IsExposed ℝ (polyhedron_le_set A' b') H := by
    simpa [A', b', hG_eq, active_constraint_face_eq_polyhedronAux] using hH_local
  have hH_facet_aux :
      is_facet (polyhedron_le_set A' b') H := by
    simpa [A', b', hG_eq, active_constraint_face_eq_polyhedronAux] using hH_facet_local
  have hH_codim :
      Module.finrank ℝ (affineSpan ℝ H).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ G).direction := by
    -- The local facet theorem computes codimension one inside the exposed face `G`.
    have hAux_codim :
        Module.finrank ℝ (affineSpan ℝ H).direction + 1 =
          Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A' b')).direction := by
      exact
        ((is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
            A' b' hG_nonempty_aux H hH_local_aux).mp hH_facet_aux).2
    rw [← hG_aux_eq]
    exact hAux_codim
  exact ⟨H, hH_nonempty, hH_ambient_pair.1, hH_ambient_pair.2, hH_codim⟩

/-- Helper for Theorem 3.33: inside any nonempty exposed face of the ambient polyhedron, every
dimension between the ambient lineality dimension and the face dimension is realized by a nonempty
exposed subface. -/
lemma exists_nonempty_face_of_finrank_between_lineality_and_exposed_face
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (G : Set (Fin n → ℝ))
    (hG_nonempty : G.Nonempty)
    (hG_exposed : IsExposed ℝ (polyhedron_le_set A b) G)
    (k : ℕ)
    (hk_lineality : Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) ≤ k)
    (hkG : k ≤ Module.finrank ℝ (affineSpan ℝ G).direction) :
    ∃ F : Set (Fin n → ℝ),
      F.Nonempty ∧
        IsExposed ℝ (polyhedron_le_set A b) F ∧
          F ⊆ G ∧
            Module.finrank ℝ (affineSpan ℝ F).direction = k := by
  classical
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  let ldim : ℕ := Module.finrank ℝ (linealitySubmodule P)
  -- Recurse on the current face dimension, dropping one dimension at a time through a facet.
  refine
    Nat.strong_induction_on
      (p := fun d : ℕ ↦
        ∀ G' : Set (Fin n → ℝ),
          G'.Nonempty →
            IsExposed ℝ P G' →
              Module.finrank ℝ (affineSpan ℝ G').direction = d →
                ldim ≤ k →
                  k ≤ d →
                    ∃ F : Set (Fin n → ℝ),
                      F.Nonempty ∧
                        IsExposed ℝ P F ∧
                          F ⊆ G' ∧
                            Module.finrank ℝ (affineSpan ℝ F).direction = k)
      (Module.finrank ℝ (affineSpan ℝ G).direction) ?_
      G hG_nonempty (by simpa [P] using hG_exposed) rfl (by simpa [ldim, P] using hk_lineality) hkG
  intro d ih G' hG'_nonempty hG'_exposed hG'_dim hk_lineality' hkG'
  by_cases hkd : k = d
  · have hG'_target :
        Module.finrank ℝ (affineSpan ℝ G').direction = k := by
      omega
    exact ⟨G', hG'_nonempty, hG'_exposed, Set.Subset.rfl, hG'_target⟩
  · have hklt : k < d := by
      omega
    have hLinealityLt_d : ldim < d := lt_of_le_of_lt hk_lineality' hklt
    have hLinealityLt :
        Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) <
          Module.finrank ℝ (affineSpan ℝ G').direction := by
      simpa [ldim, P, hG'_dim] using hLinealityLt_d
    obtain ⟨H, hH_nonempty, hH_exposed, hHG, hH_dim⟩ :=
      exists_exposed_subface_of_pred_finrank_of_lineality_lt
        A b G' hG'_nonempty (by simpa [P] using hG'_exposed) hLinealityLt
    have hH_dim_eq :
        Module.finrank ℝ (affineSpan ℝ H).direction = d - 1 := by
      omega
    have hH_dim_lt : Module.finrank ℝ (affineSpan ℝ H).direction < d := by
      omega
    have hkH : k ≤ d - 1 := by
      omega
    obtain ⟨F, hF_nonempty, hF_exposed, hFH, hF_dim⟩ :=
      ih (d - 1) (by omega)
        H hH_nonempty hH_exposed hH_dim_eq hk_lineality' hkH
    exact ⟨F, hF_nonempty, hF_exposed, Set.Subset.trans hFH hHG, hF_dim⟩

/-- Theorem 3.33 (3). The nonempty faces of a nonempty polyhedron `P = {x | A *ᵥ x ≤ b}` realize
every dimension between the dimension of the lineality space of `P` and the dimension of `P`. -/
theorem exists_nonempty_face_of_finrank_between_linealitySpace_and_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (k : ℕ)
    (hk_lineality : Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) ≤ k)
    (hk_polyhedron : k ≤ Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction) :
    ∃ F : Set (Fin n → ℝ),
      F.Nonempty ∧
        IsExposed ℝ (polyhedron_le_set A b) F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = k := by
  -- The source proof descends through facets from the ambient polyhedron until the requested
  -- dimension is reached, stopping at the lineality dimension.
  obtain ⟨F, hF_nonempty, hF_exposed, -, hF_dim⟩ :=
    exists_nonempty_face_of_finrank_between_lineality_and_exposed_face
      A b (polyhedron_le_set A b) hP_nonempty (IsExposed.refl (polyhedron_le_set A b))
      k hk_lineality hk_polyhedron
  exact ⟨F, hF_nonempty, hF_exposed, hF_dim⟩

end Theorem333
