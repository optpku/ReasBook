/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Order.Preorder.Finite
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_24
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2

/-
Definition 3.8-extra-3 adds the facet layer on top of the source-facing face API from
Section 3.8-extra-2, where faces are already organized around mathlib's canonical owner
`IsExposed ℝ P`.
-/

/-- Definition 3.8-extra-3 (1): a facet of `P` is an inclusionwise maximal proper face of `P`. -/
class is_facet {n : ℕ} (P F : Set (Fin n → ℝ)) : Prop where
  /-- A facet is, in particular, a proper face. -/
  isProper : is_proper_face P F
  /-- A facet is maximal among proper faces. -/
  maximal (G : Set (Fin n → ℝ)) (hG : is_proper_face P G) (hFG : F ⊆ G) : G = F

/-- The defining expansion of `is_facet`. -/
theorem is_facet_iff {n : ℕ} {P F : Set (Fin n → ℝ)} :
    is_facet P F ↔
      is_proper_face P F ∧
        ∀ G : Set (Fin n → ℝ), is_proper_face P G → F ⊆ G → G = F := by
  constructor
  · intro hF
    exact ⟨hF.isProper, hF.maximal⟩
  · rintro ⟨hF, hmax⟩
    exact ⟨hF, hmax⟩

/-- A facet is, in particular, a proper face. -/
theorem is_facet_to_is_proper_face {n : ℕ} {P F : Set (Fin n → ℝ)}
    (hF : is_facet P F) : is_proper_face P F :=
  hF.isProper

/-- A facet is maximal among proper faces. -/
theorem is_facet_maximal {n : ℕ} {P F G : Set (Fin n → ℝ)}
    (hF : is_facet P F) (hG : is_proper_face P G) (hFG : F ⊆ G) : G = F :=
  hF.maximal G hG hFG

/-- Helper for Definition 3.8-extra-3: every proper face of a presented polyhedron is one of its
active-constraint faces. -/
lemma proper_face_superset_mem_active_constraint_face_range
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {G : Set (Fin n → ℝ)}
    (hG : is_proper_face (polyhedron_le_set A b) G) :
    ∃ I : Set (Fin m), G = active_constraint_face A b I := by
  -- Unpack the proper-face data so Theorem 3.24 can realize `G` as an active-constraint face.
  rcases (is_proper_face_iff.mp hG) with ⟨hG_exposed, hG_nonempty, _⟩
  exact exists_eq_active_constraint_face_of_isExposed A b G hG_exposed hG_nonempty

/-- Helper for Definition 3.8-extra-3: the proper faces of `polyhedron_le_set A b` that contain a
fixed proper face form a finite family. -/
lemma proper_face_supersets_finite
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {F : Set (Fin n → ℝ)} :
    {G : Set (Fin n → ℝ) | is_proper_face (polyhedron_le_set A b) G ∧ F ⊆ G}.Finite := by
  classical
  -- Every candidate is realized by some subset of the finitely many defining inequalities.
  refine (Set.finite_range (fun I : Set (Fin m) ↦ active_constraint_face A b I)).subset ?_
  intro G hG
  rcases proper_face_superset_mem_active_constraint_face_range hG.1 with ⟨I, hI⟩
  exact ⟨I, hI.symm ▸ rfl⟩

/-- Helper for Definition 3.8-extra-3: a maximal proper-face superset of `F` is a facet. -/
lemma maximal_proper_face_superset_is_facet
    {n : ℕ} {P F G : Set (Fin n → ℝ)}
    (hmax : Maximal (fun H : Set (Fin n → ℝ) ↦ is_proper_face P H ∧ F ⊆ H) G) :
    is_facet P G := by
  have hG : is_proper_face P G := hmax.prop.1
  have hFG : F ⊆ G := hmax.prop.2
  refine ⟨hG, ?_⟩
  intro H hH hGH
  -- Any larger proper face containing `G` still contains the seed face `F`, so maximality closes.
  have hH_mem : is_proper_face P H ∧ F ⊆ H := ⟨hH, Set.Subset.trans hFG hGH⟩
  exact (hmax.eq_of_subset hH_mem hGH).symm

/-- Definition 3.8-extra-3 (2): if `P` is a polyhedron, then every proper face of `P` is
contained in a facet of `P`. -/
theorem exists_is_facet_superset_of_is_proper_face
    {n : ℕ} {P F : Set (Fin n → ℝ)} (hP : is_polyhedron P) (hF : is_proper_face P F) :
    ∃ G : Set (Fin n → ℝ), is_facet P G ∧ F ⊆ G := by
  classical
  rcases (is_polyhedron_iff.mp hP) with ⟨m, A, b, rfl⟩
  let S : Set (Set (Fin n → ℝ)) :=
    {G : Set (Fin n → ℝ) | is_proper_face (polyhedron_le_set A b) G ∧ F ⊆ G}
  have hS_finite : S.Finite := by
    -- The source proof reduces the search for a facet to finitely many active-constraint faces.
    simpa [S] using (proper_face_supersets_finite (A := A) (b := b) (F := F))
  have hF_mem : F ∈ S := by
    -- The given proper face is the initial element in the finite poset
    -- of its proper-face supersets.
    exact ⟨hF, Set.Subset.refl F⟩
  obtain ⟨G, hFG, hGmax⟩ := hS_finite.exists_le_maximal hF_mem
  refine ⟨G, maximal_proper_face_superset_is_facet hGmax, hFG⟩

/-- Definition 3.8-extra-3 (3): a valid inequality for `P` is facet-defining when the face that it
cuts out on `P` is a facet. -/
class facet_defining_inequality {n : ℕ}
    (P : Set (Fin n → ℝ)) (c : Fin n → ℝ) (δ : ℝ) : Prop where
  /-- A facet-defining inequality is valid for the ambient polyhedron. -/
  valid : is_valid_inequality P c δ
  /-- The equality face cut out by a facet-defining inequality is a facet. -/
  facet : is_facet P (face_set P c δ)

/-- The defining expansion of `facet_defining_inequality`. -/
theorem facet_defining_inequality_iff {n : ℕ} {P : Set (Fin n → ℝ)} {c : Fin n → ℝ} {δ : ℝ} :
    facet_defining_inequality P c δ ↔
      is_valid_inequality P c δ ∧ is_facet P (face_set P c δ) := by
  constructor
  · intro h
    exact ⟨h.valid, h.facet⟩
  · rintro ⟨hvalid, hfacet⟩
    exact ⟨hvalid, hfacet⟩

/-- A facet-defining inequality is valid for the ambient polyhedron. -/
theorem facet_defining_inequality_valid {n : ℕ} {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ} {δ : ℝ} (h : facet_defining_inequality P c δ) :
    is_valid_inequality P c δ :=
  h.valid

/-- The equality set of a facet-defining inequality is a facet. -/
theorem facet_defining_inequality_is_facet {n : ℕ} {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ} {δ : ℝ} (h : facet_defining_inequality P c δ) :
    is_facet P (face_set P c δ) :=
  h.facet
