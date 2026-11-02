import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_lemma_3_26

open scoped BigOperators Matrix

section Theorem_3_27

variable {m n : ℕ}

/-
Theorem 3.27 specializes the Chapter 3 owner `active_constraint_face A b I` to singleton index
sets and reuses the Section 3.9 owner `is_irredundant_row`; the facet layer itself is already
owned upstream by `is_facet`.
-/

/-- Helper for Theorem 3.27: if every activated row is already an implicit equality, then the
corresponding active-constraint face is the whole polyhedron. -/
lemma activeConstraintFace_eq_polyhedron_of_forall_implicit
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin m))
    (hI :
      ∀ i : Fin m, i ∈ I → is_implicit_equality A b i) :
    active_constraint_face A b I = polyhedron_le_set A b := by
  ext x
  constructor
  · intro hx
    -- Every active-constraint point is feasible for the ambient polyhedron.
    exact mem_polyhedron_of_mem_active_constraint_face hx
  · intro hx
    -- Implicit rows contribute no extra restriction beyond feasibility.
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      exact hI i hi hx
    · intro i _hi
      exact hx i

/-- Theorem 3.27 (1) (Characterization of the Facets). If `polyhedron_le_set A b` is nonempty,
then every facet of it is cut out by some non-implicit row of the defining system. -/
theorem exists_eq_active_constraint_face_singleton_of_is_facet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : (polyhedron_le_set A b).Nonempty)
    (F : Set (Fin n → ℝ))
    (hF_facet : is_facet (polyhedron_le_set A b) F) :
    ∃ j : {j // j ∈ remaining_inequality_indices A b},
      F = active_constraint_face A b ({j.1} : Set (Fin m)) := by
  classical
  rcases is_proper_face_iff.mp (is_facet_to_is_proper_face hF_facet) with
    ⟨hF_face, hF_nonempty, hF_ssubset⟩
  obtain ⟨I, hI⟩ := exists_eq_active_constraint_face_of_isExposed A b F hF_face hF_nonempty
  have hI_has_remaining :
      ∃ j : Fin m, j ∈ I ∧ j ∈ remaining_inequality_indices A b := by
    by_contra hno
    have hI_implicit :
        ∀ i : Fin m, i ∈ I → is_implicit_equality A b i := by
      intro i hi
      by_cases hi_implicit : is_implicit_equality A b i
      · exact hi_implicit
      · have hi_remaining : i ∈ remaining_inequality_indices A b :=
          (mem_remaining_inequality_indices_iff A b i).2 hi_implicit
        exact False.elim (hno ⟨i, hi, hi_remaining⟩)
    have hF_eq_poly : F = polyhedron_le_set A b := by
      calc
        F = active_constraint_face A b I := hI
        _ = polyhedron_le_set A b :=
          activeConstraintFace_eq_polyhedron_of_forall_implicit A b I hI_implicit
    exact hF_ssubset.ne hF_eq_poly
  rcases hI_has_remaining with ⟨j, hjI, hj_remaining⟩
  have hF_subset_singleton :
      F ⊆ active_constraint_face A b ({j} : Set (Fin m)) := by
    intro x hxF
    have hxI : x ∈ active_constraint_face A b I := by
      simpa [hI] using hxF
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro r hr
      have hrj : r = j := by simpa using hr
      simpa [hrj] using (mem_active_constraint_face_iff.mp hxI).1 j hjI
    · intro r _hr
      exact mem_polyhedron_of_mem_active_constraint_face hxI r
  have hsingleton_nonempty :
      (active_constraint_face A b ({j} : Set (Fin m))).Nonempty := by
    obtain ⟨x, hxF⟩ := hF_nonempty
    exact ⟨x, hF_subset_singleton hxF⟩
  have hsingleton_ssubset :
      active_constraint_face A b ({j} : Set (Fin m)) ⊂ polyhedron_le_set A b := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact mem_polyhedron_of_mem_active_constraint_face hx
    · intro hEq
      rcases
          exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices
            A b j hj_remaining with
        ⟨x, hxP, hxlt⟩
      have hxFace : x ∈ active_constraint_face A b ({j} : Set (Fin m)) := by
        exact hEq hxP
      have hxj_eq : (A *ᵥ x) j = b j :=
        (mem_active_constraint_face_iff.mp hxFace).1 j (by simp)
      exact (ne_of_lt hxlt) hxj_eq
  have hsingleton_proper :
      is_proper_face (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))) := by
    exact
      (is_proper_face_iff).2
        ⟨active_constraint_face_isExposed A b ({j} : Set (Fin m)),
          hsingleton_nonempty, hsingleton_ssubset⟩
  have hsingleton_eq_F :
      active_constraint_face A b ({j} : Set (Fin m)) = F :=
    is_facet_maximal hF_facet hsingleton_proper hF_subset_singleton
  -- Theorem 3.24 reduces the facet to one active-constraint face, and maximality shrinks that
  -- face to a singleton remaining row.
  exact ⟨⟨j, hj_remaining⟩, hsingleton_eq_F.symm⟩

/-- Helper for Theorem 3.27: a nonempty exposed face of codimension one is a facet. -/
lemma isFacet_of_nonempty_finrank_direction_affineSpan_add_one_eq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (F : Set (Fin n → ℝ))
    (hF_face : IsExposed ℝ (polyhedron_le_set A b) F)
    (hF_nonempty : F.Nonempty)
    (hF_codim :
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
        Module.finrank ℝ
          (affineSpan ℝ (polyhedron_le_set A b)).direction) :
    is_facet (polyhedron_le_set A b) F := by
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  have hP_poly : is_polyhedron P := by
    exact ⟨m, A, b, rfl⟩
  have hF_ssubset : F ⊂ P := by
    refine ⟨hF_face.subset, ?_⟩
    intro hFP
    -- If `F = P`, the codimension-one equation collapses to `d + 1 = d`.
    have hFP_eq : F = P := Set.Subset.antisymm hF_face.subset hFP
    have hcollapse :
        Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
          Module.finrank ℝ (affineSpan ℝ F).direction := by
      calc
        Module.finrank ℝ (affineSpan ℝ F).direction + 1
            = Module.finrank ℝ (affineSpan ℝ P).direction := by
                dsimp [P]
                exact hF_codim
        _ = Module.finrank ℝ (affineSpan ℝ F).direction := by
              rw [← hFP_eq]
    exact Nat.succ_ne_self _ hcollapse
  have hF_proper : is_proper_face P F := by
    exact (is_proper_face_iff).2 ⟨hF_face, hF_nonempty, hF_ssubset⟩
  obtain ⟨G, hG_facet, hFG⟩ := exists_is_facet_superset_of_is_proper_face hP_poly hF_proper
  by_cases hGF : G = F
  · simpa [P, hGF] using hG_facet
  · have hG_proper : is_proper_face P G := is_facet_to_is_proper_face hG_facet
    rcases (is_proper_face_iff.mp hG_proper) with ⟨hG_face, hG_nonempty, hG_ssubset⟩
    have hFG_ssubset : F ⊂ G := by
      refine ⟨hFG, ?_⟩
      intro hGF_sub
      exact hGF (Set.Subset.antisymm hGF_sub hFG)
    have hAff_lt_FG : affineSpan ℝ F < affineSpan ℝ G := by
      have hAff_ne :
          affineSpan ℝ F ≠ affineSpan ℝ G :=
        (face_ne_iff_affineSpan_ne hP_poly hF_face hG_face).1 hFG_ssubset.ne
      exact lt_of_le_of_ne (affineSpan_mono ℝ hFG) hAff_ne
    have hF_aff_nonempty :
        ((affineSpan ℝ F : AffineSubspace ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)).Nonempty := by
      obtain ⟨x, hx⟩ := hF_nonempty
      exact ⟨x, subset_affineSpan ℝ F hx⟩
    have hDir_lt_FG :
        (affineSpan ℝ F).direction < (affineSpan ℝ G).direction :=
      AffineSubspace.direction_lt_of_nonempty hAff_lt_FG hF_aff_nonempty
    have hFinrank_lt_FG :
        Module.finrank ℝ (affineSpan ℝ F).direction <
          Module.finrank ℝ (affineSpan ℝ G).direction :=
      Submodule.finrank_lt_finrank_of_lt hDir_lt_FG
    have hAff_lt_GP : affineSpan ℝ G < affineSpan ℝ P := by
      have hAff_ne :
          affineSpan ℝ G ≠ affineSpan ℝ P :=
        (face_ne_iff_affineSpan_ne hP_poly hG_face (IsExposed.refl P)).1 hG_ssubset.ne
      exact lt_of_le_of_ne (affineSpan_mono ℝ hG_ssubset.subset) hAff_ne
    have hG_aff_nonempty :
        ((affineSpan ℝ G : AffineSubspace ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)).Nonempty := by
      obtain ⟨x, hx⟩ := hG_nonempty
      exact ⟨x, subset_affineSpan ℝ G hx⟩
    have hDir_lt_GP :
        (affineSpan ℝ G).direction < (affineSpan ℝ P).direction :=
      AffineSubspace.direction_lt_of_nonempty hAff_lt_GP hG_aff_nonempty
    have hFinrank_lt_GP :
        Module.finrank ℝ (affineSpan ℝ G).direction <
          Module.finrank ℝ (affineSpan ℝ P).direction :=
      Submodule.finrank_lt_finrank_of_lt hDir_lt_GP
    -- A facet cannot admit a strictly intermediate face between itself and the ambient polyhedron.
    exfalso
    let dF := Module.finrank ℝ (affineSpan ℝ F).direction
    let dG := Module.finrank ℝ (affineSpan ℝ G).direction
    let dP := Module.finrank ℝ (affineSpan ℝ P).direction
    have hdF : dF + 1 = dP := by
      simpa [dF, dP, P] using hF_codim
    have hdFG : dF < dG := by
      simpa [dF, dG, P] using hFinrank_lt_FG
    have hdGP : dG < dP := by
      simpa [dG, dP, P] using hFinrank_lt_GP
    omega

/-- Helper for Theorem 3.27: under a minimal representation, different remaining rows define
different singleton active-constraint faces. -/
lemma activeConstraintFaceSingleton_injective_of_minimalRepresentation
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hminimal :
      ∀ i : Fin m, ¬ is_implicit_equality A b i → is_irredundant_row A b i) :
    Function.Injective
      (fun i : {i // i ∈ remaining_inequality_indices A b} ↦
        active_constraint_face A b ({i.1} : Set (Fin m))) := by
  intro i j hij
  by_contra hij_ne
  have hi_not_implicit : ¬ is_implicit_equality A b i.1 :=
    (mem_remaining_inequality_indices_iff A b i.1).1 i.2
  have hi_irredundant : is_irredundant_row A b i.1 := hminimal i.1 hi_not_implicit
  rcases exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b i.1 i.2 with
    ⟨x, hxP, _⟩
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨x, hxP⟩
  obtain ⟨xhat, hxhat_face, hhat_strict⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A b i.1 hP_nonempty hi_irredundant
  have hxhat_face' : xhat ∈ active_constraint_face A b ({j.1} : Set (Fin m)) := by
    simpa [hij] using hxhat_face
  have hji : j.1 ≠ i.1 := by
    intro hji_eq
    apply hij_ne
    exact Subtype.ext hji_eq.symm
  have hj_not_implicit : ¬ is_implicit_equality A b j.1 :=
    (mem_remaining_inequality_indices_iff A b j.1).1 j.2
  have hxhat_lt :
      (A *ᵥ xhat) j.1 < b j.1 :=
    hhat_strict j.1 hji hj_not_implicit
  have hxhat_eq :
      (A *ᵥ xhat) j.1 = b j.1 :=
    (mem_active_constraint_face_iff.mp hxhat_face').1 j.1 (by simp)
  exact (ne_of_lt hxhat_lt) hxhat_eq

/-- Helper for Theorem 3.27: under minimality, a remaining singleton active face has codimension
one in the ambient affine span. -/
lemma finrank_direction_affineSpan_add_one_eq_of_irredundant_singleton
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m)
    (hj : j ∈ remaining_inequality_indices A b)
    (hj_irredundant : is_irredundant_row A b j) :
    Module.finrank ℝ
        (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))).direction + 1 =
      Module.finrank ℝ
        (affineSpan ℝ (polyhedron_le_set A b)).direction := by
  rcases exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b j hj with
    ⟨x, hxP, hxlt⟩
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨x, hxP⟩
  have hj_not_implicit : ¬ is_implicit_equality A b j :=
    (mem_remaining_inequality_indices_iff A b j).1 hj
  have hdim :
      Module.finrank ℝ
          (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))).direction =
        Module.finrank ℝ
            (affineSpan ℝ (polyhedron_le_set A b)).direction - 1 :=
    finrank_direction_affineSpan_active_constraint_face_singleton_eq_sub_one
      A b j hP_nonempty hj_not_implicit hj_irredundant
  obtain ⟨xhat, hxhat_face, _⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A b j hP_nonempty hj_irredundant
  have hxhatP : xhat ∈ polyhedron_le_set A b :=
    mem_polyhedron_of_mem_active_constraint_face hxhat_face
  have hxhat_row : (A *ᵥ xhat) j = b j :=
    (mem_active_constraint_face_iff.mp hxhat_face).1 j (by simp)
  have hxhat_ne_x : xhat ≠ x := by
    intro hEq
    have hx_row : (A *ᵥ x) j = b j := by
      simpa [hEq] using hxhat_row
    exact (ne_of_lt hxlt) hx_row
  let v : Fin n → ℝ := xhat - x
  have hv_mem :
      v ∈ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
    have hx_aff :
        x ∈ affineSpan ℝ (polyhedron_le_set A b) :=
      subset_affineSpan ℝ (polyhedron_le_set A b) hxP
    have hxhat_aff :
        xhat ∈ affineSpan ℝ (polyhedron_le_set A b) :=
      subset_affineSpan ℝ (polyhedron_le_set A b) hxhatP
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx_aff]
    refine ⟨xhat, hxhat_aff, ?_⟩
    simp [v, vsub_eq_sub]
  have hv_ne : v ≠ 0 := by
    dsimp [v]
    exact sub_ne_zero.mpr hxhat_ne_x
  have hP_dim_pos :
      0 < Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv_mem⟩, by simpa using hv_ne⟩
  have hP_dim_ge :
      1 ≤ Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction :=
    Nat.succ_le_of_lt hP_dim_pos
  have hdim_rev :
      Module.finrank ℝ
          (affineSpan ℝ (polyhedron_le_set A b)).direction - 1 =
        Module.finrank ℝ
          (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))).direction :=
    hdim.symm
  have hcodim :
      Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction =
        Module.finrank ℝ
          (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))).direction + 1 :=
    (Nat.sub_eq_iff_eq_add hP_dim_ge).mp hdim_rev
  -- Translate the subtraction form from Lemma 3.26 into the codimension-one equation used here.
  simpa [Nat.add_comm] using hcodim.symm

/-- Helper for Theorem 3.27: if a singleton active face is a facet, then any remaining row whose
singleton face contains it actually defines the same face. -/
lemma singletonActiveConstraintFace_eq_of_subset_of_isFacet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    (hsubset :
      active_constraint_face A b ({j} : Set (Fin m)) ⊆
        active_constraint_face A b ({i} : Set (Fin m))) :
    active_constraint_face A b ({i} : Set (Fin m)) =
      active_constraint_face A b ({j} : Set (Fin m)) := by
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  let Fi : Set (Fin n → ℝ) := active_constraint_face A b ({i} : Set (Fin m))
  have hFi_nonempty : Fi.Nonempty := by
    rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.1 with ⟨x, hx⟩
    exact ⟨x, hsubset hx⟩
  have hFi_ssubset : Fi ⊂ P := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact mem_polyhedron_of_mem_active_constraint_face hx
    · intro hEq
      rcases
          exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices
            A b i hi with
        ⟨x, hxP, hxlt⟩
      have hxFi : x ∈ Fi := by
        simpa [Fi, P] using hEq hxP
      have hxi : (A *ᵥ x) i = b i :=
        (mem_active_constraint_face_iff.mp hxFi).1 i (by simp)
      exact (ne_of_lt hxlt) hxi
  have hFi_proper : is_proper_face P Fi := by
    -- A remaining row cuts out a proper exposed face because that row is strict somewhere on `P`.
    exact
      (is_proper_face_iff).2
        ⟨active_constraint_face_isExposed A b ({i} : Set (Fin m)),
          hFi_nonempty, hFi_ssubset⟩
  -- Facet maximality upgrades containment into equality of the singleton faces.
  simpa [Fi] using (is_facet_maximal hfacet hFi_proper hsubset)

/-- Helper for Theorem 3.27: the midpoint of two points in the same singleton active face stays in
that face. -/
lemma midpoint_mem_activeConstraintFace_singleton
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m)
    {x y : Fin n → ℝ}
    (hx :
      x ∈ active_constraint_face A b ({j} : Set (Fin m)))
    (hy :
      y ∈ active_constraint_face A b ({j} : Set (Fin m))) :
    ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ∈
      active_constraint_face A b ({j} : Set (Fin m)) := by
  refine (mem_active_constraint_face_iff).2 ?_
  constructor
  · intro k hk
    have hkj : k = j := by simpa using hk
    have hxk : (A *ᵥ x) k = b k := by
      simpa [hkj] using (mem_active_constraint_face_iff.mp hx).1 j (by simp)
    have hyk : (A *ᵥ y) k = b k := by
      simpa [hkj] using (mem_active_constraint_face_iff.mp hy).1 j (by simp)
    -- The midpoint preserves the activated equality because both endpoints satisfy it.
    calc
      (A *ᵥ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) k
          = (1 / 2 : ℝ) * (A *ᵥ x) k + (1 / 2 : ℝ) * (A *ᵥ y) k := by
              simp [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = (1 / 2 : ℝ) * b k + (1 / 2 : ℝ) * b k := by rw [hxk, hyk]
      _ = b k := by ring
  · intro k hk
    have hxk : (A *ᵥ x) k ≤ b k :=
      (mem_active_constraint_face_iff.mp hx).2 k hk
    have hyk : (A *ᵥ y) k ≤ b k :=
      (mem_active_constraint_face_iff.mp hy).2 k hk
    -- Averaging two feasible points preserves every nonactivated inequality.
    calc
      (A *ᵥ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) k
          = (1 / 2 : ℝ) * (A *ᵥ x) k + (1 / 2 : ℝ) * (A *ᵥ y) k := by
              simp [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ ≤ (1 / 2 : ℝ) * b k + (1 / 2 : ℝ) * b k := by
            have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
            gcongr
      _ = b k := by ring

/-- Helper for Theorem 3.27: if a remaining row does not define the same singleton facet, then
that facet contains a point that is strict on the row. -/
lemma exists_mem_singletonFacet_strict_on_distinct_singletonFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) ≠
        active_constraint_face A b ({j} : Set (Fin m))) :
    ∃ x ∈ active_constraint_face A b ({j} : Set (Fin m)), (A *ᵥ x) i < b i := by
  by_contra hno
  have hsubset :
      active_constraint_face A b ({j} : Set (Fin m)) ⊆
        active_constraint_face A b ({i} : Set (Fin m)) := by
    intro x hxj
    by_contra hxi
    have hxP : x ∈ polyhedron_le_set A b :=
      mem_polyhedron_of_mem_active_constraint_face hxj
    have hxle : (A *ᵥ x) i ≤ b i := hxP i
    have hxne : (A *ᵥ x) i ≠ b i := by
      intro hEq
      apply hxi
      refine (mem_active_constraint_face_iff).2 ?_
      constructor
      · intro k hk
        have hki : k = i := by simpa using hk
        simpa [hki] using hEq
      · intro k hk
        exact hxP k
    have hxlt : (A *ᵥ x) i < b i := lt_of_le_of_ne hxle hxne
    exact hno ⟨x, hxj, hxlt⟩
  exact hij_face (singletonActiveConstraintFace_eq_of_subset_of_isFacet A b i j hi hfacet hsubset)

/-- Helper for Theorem 3.27: a singleton facet contains one point that is strict on every
remaining row whose singleton face is different from the facet. -/
lemma exists_mem_singletonFacet_strict_outside_rowClass
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m)))) :
    ∃ xbar ∈ active_constraint_face A b ({j} : Set (Fin m)),
      ∀ i : Fin m,
        i ∈ remaining_inequality_indices A b →
          active_constraint_face A b ({i} : Set (Fin m)) ≠
            active_constraint_face A b ({j} : Set (Fin m)) →
              (A *ᵥ xbar) i < b i := by
  classical
  let Fj : Set (Fin n → ℝ) := active_constraint_face A b ({j} : Set (Fin m))
  let badRows : Finset (Fin m) :=
    Finset.univ.filter fun i ↦
      i ∈ remaining_inequality_indices A b ∧
        active_constraint_face A b ({i} : Set (Fin m)) ≠ Fj
  have hbuild :
      ∀ s : Finset (Fin m),
        (∀ i : Fin m, i ∈ s →
          i ∈ remaining_inequality_indices A b ∧
            active_constraint_face A b ({i} : Set (Fin m)) ≠ Fj) →
          ∃ x ∈ Fj, ∀ i : Fin m, i ∈ s → (A *ᵥ x) i < b i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _hs
        rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.1 with ⟨x, hx⟩
        -- The empty set of strict rows only needs a point of the facet.
        exact ⟨x, hx, fun i hi ↦ by simp at hi⟩
    | @insert a s ha ih =>
      intro hs_all
      have hs_tail :
          ∀ i : Fin m, i ∈ s →
            i ∈ remaining_inequality_indices A b ∧
              active_constraint_face A b ({i} : Set (Fin m)) ≠ Fj := by
        intro i hi
        exact hs_all i (Finset.mem_insert_of_mem hi)
      rcases ih hs_tail with ⟨x, hxFj, hxstrict⟩
      have ha_data :
          a ∈ remaining_inequality_indices A b ∧
            active_constraint_face A b ({a} : Set (Fin m)) ≠ Fj :=
        hs_all a (Finset.mem_insert_self a s)
      rcases
          exists_mem_singletonFacet_strict_on_distinct_singletonFace
            A b a j ha_data.1 hfacet (by simpa [Fj] using ha_data.2) with
        ⟨y, hyFj, hylt⟩
      let z : Fin n → ℝ := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
      have hzFj : z ∈ Fj := by
        simpa [z, Fj] using midpoint_mem_activeConstraintFace_singleton A b j hxFj hyFj
      refine ⟨z, hzFj, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst hi
        -- The new witness row stays strict because one midpoint endpoint is already strict on it.
        have hx_le : (A *ᵥ x) i ≤ b i :=
          (mem_polyhedron_of_mem_active_constraint_face hxFj) i
        have hy_half_lt :
            (1 / 2 : ℝ) * (A *ᵥ y) i < (1 / 2 : ℝ) * b i := by
          have hhalf_pos : 0 < (1 / 2 : ℝ) := by norm_num
          exact mul_lt_mul_of_pos_left hylt hhalf_pos
        have hx_half_le :
            (1 / 2 : ℝ) * (A *ᵥ x) i ≤ (1 / 2 : ℝ) * b i := by
          have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
          gcongr
        calc
          (A *ᵥ z) i = (1 / 2 : ℝ) * (A *ᵥ x) i + (1 / 2 : ℝ) * (A *ᵥ y) i := by
              simp [z, Matrix.mulVec_add, Matrix.mulVec_smul]
          _ < (1 / 2 : ℝ) * b i + (1 / 2 : ℝ) * b i := by
                linarith
          _ = b i := by ring
      · have hxlt_i : (A *ᵥ x) i < b i := hxstrict i hi
        have hy_le : (A *ᵥ y) i ≤ b i :=
          (mem_polyhedron_of_mem_active_constraint_face hyFj) i
        have hx_half_lt :
            (1 / 2 : ℝ) * (A *ᵥ x) i < (1 / 2 : ℝ) * b i := by
          have hhalf_pos : 0 < (1 / 2 : ℝ) := by norm_num
          exact mul_lt_mul_of_pos_left hxlt_i hhalf_pos
        have hy_half_le :
            (1 / 2 : ℝ) * (A *ᵥ y) i ≤ (1 / 2 : ℝ) * b i := by
          have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
          gcongr
        -- Previously strict rows remain strict after averaging with another feasible facet point.
        calc
          (A *ᵥ z) i = (1 / 2 : ℝ) * (A *ᵥ x) i + (1 / 2 : ℝ) * (A *ᵥ y) i := by
              simp [z, Matrix.mulVec_add, Matrix.mulVec_smul]
          _ < (1 / 2 : ℝ) * b i + (1 / 2 : ℝ) * b i := by
                linarith
          _ = b i := by ring
  have hbadRows :
      ∀ i : Fin m, i ∈ badRows →
        i ∈ remaining_inequality_indices A b ∧
          active_constraint_face A b ({i} : Set (Fin m)) ≠ Fj := by
    intro i hi
    simpa [badRows, Fj] using (Finset.mem_filter.mp hi).2
  rcases hbuild badRows hbadRows with ⟨xbar, hxbar, hxbar_strict⟩
  · refine ⟨xbar, hxbar, ?_⟩
    intro i hi hij_face
    exact hxbar_strict i (by
      simp [badRows, Fj, hi, hij_face])

/-- Helper for Theorem 3.27: if row `i` cuts out the same singleton facet as row `j`, then the
multiplier certificate for the valid inequality `A i x ≤ b i` only uses implicit rows or rows that
define that same facet. -/
lemma exists_sameFacetRowMultiplier_of_eq_singletonFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hi_remaining : i ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m))) :
    ∃ u : Fin m → ℝ,
      (∀ k : Fin m, 0 ≤ u k) ∧
        u ᵥ* A = A i ∧
          u ⬝ᵥ b = b i ∧
            ∀ k : Fin m, 0 < u k →
              is_implicit_equality A b k ∨
                active_constraint_face A b ({k} : Set (Fin m)) =
                  active_constraint_face A b ({j} : Set (Fin m)) := by
  let _ := hi_remaining
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  have hvalid : is_valid_inequality P (A i) (b i) := by
    intro x hx
    exact hx i
  have hattained : (face_set P (A i) (b i)).Nonempty := by
    rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.1 with ⟨x, hxj⟩
    refine ⟨x, ?_⟩
    rw [← active_constraint_face_singleton_eq A b i]
    simpa [hij_face] using hxj
  obtain ⟨u, hu, hrow, hδ⟩ :=
    exists_nonneg_multiplier_of_attained_valid_inequality A b (A i) (b i) hvalid hattained
  refine ⟨u, hu, hrow, hδ, ?_⟩
  intro k hk
  by_cases hk_implicit : is_implicit_equality A b k
  · exact Or.inl hk_implicit
  · right
    have hk_remaining : k ∈ remaining_inequality_indices A b :=
      (mem_remaining_inequality_indices_iff A b k).2 hk_implicit
    have hsubset :
        active_constraint_face A b ({j} : Set (Fin m)) ⊆
          active_constraint_face A b ({k} : Set (Fin m)) := by
      intro x hxj
      have hxface : x ∈ face_set P (A i) (b i) := by
        rw [← active_constraint_face_singleton_eq A b i]
        simpa [hij_face] using hxj
      have hxsupport :
          x ∈ active_constraint_face A b {l : Fin m | 0 < u l} :=
        (mem_face_set_iff_mem_active_constraint_face_of_support hu hrow hδ).1 hxface
      rcases mem_active_constraint_face_iff.mp hxsupport with ⟨hxEq, hxLe⟩
      refine (mem_active_constraint_face_iff).2 ?_
      constructor
      · intro l hl
        have hlk : l = k := by simpa using hl
        simpa [hlk] using hxEq k hk
      · intro l hl
        by_cases hlu : 0 < u l
        · exact le_of_eq (hxEq l hlu)
        · exact hxLe l hlu
    -- Facet maximality forces every positive-support remaining row to define the same singleton
    -- face as `j`.
    exact singletonActiveConstraintFace_eq_of_subset_of_isFacet A b k j hk_remaining hfacet hsubset

/-- Helper for Theorem 3.27: any row multiplier certificate rewrites the target-row deficit as the
weighted sum of the row deficits. -/
lemma rowSub_eq_dotProduct_rowSub_of_multiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i : Fin m)
    (u : Fin m → ℝ)
    (hrow : u ᵥ* A = A i)
    (hrhs : u ⬝ᵥ b = b i)
    {x : Fin n → ℝ} :
    (A *ᵥ x) i - b i = u ⬝ᵥ (fun r : Fin m ↦ (A *ᵥ x) r - b r) := by
  -- Expand the multiplier certificate at `x`, then regroup the right-hand side as row deficits.
  calc
    (A *ᵥ x) i - b i = (A i ⬝ᵥ x) - u ⬝ᵥ b := by
      rw [hrhs]
      simp [Matrix.mulVec]
    _ = ((u ᵥ* A) ⬝ᵥ x) - u ⬝ᵥ b := by rw [hrow]
    _ = u ⬝ᵥ (A *ᵥ x) - u ⬝ᵥ b := by rw [Matrix.dotProduct_mulVec]
    _ = u ⬝ᵥ (fun r : Fin m ↦ (A *ᵥ x) r - b r) := by
      have hsub :
          (fun r : Fin m ↦ (A *ᵥ x) r - b r) = A *ᵥ x - b := by
        rfl
      rw [hsub, dotProduct_sub]

/-- Helper for Theorem 3.27: count the positive support of a multiplier on the non-implicit rows.
-/
noncomputable def nonimplicitPositiveSupportCard
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ) : ℕ :=
  Nat.card {k : Fin m // ¬ is_implicit_equality A b k ∧ 0 < u k}

/-- Helper for Theorem 3.27: among the multiplier certificates for a same-facet row, one minimizes
the positive support on the non-implicit rows. -/
lemma existsSameFacetRowMultiplier_cardMinimal
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m))) :
    ∃ u : Fin m → ℝ,
      (∀ k : Fin m, 0 ≤ u k) ∧
        u ᵥ* A = A i ∧
          u ⬝ᵥ b = b i ∧
            (∀ k : Fin m, 0 < u k →
              is_implicit_equality A b k ∨
                active_constraint_face A b ({k} : Set (Fin m)) =
                  active_constraint_face A b ({j} : Set (Fin m))) ∧
              ∀ u' : Fin m → ℝ,
                (∀ k : Fin m, 0 ≤ u' k) →
                  u' ᵥ* A = A i →
                    u' ⬝ᵥ b = b i →
                      (∀ k : Fin m, 0 < u' k →
                        is_implicit_equality A b k ∨
                          active_constraint_face A b ({k} : Set (Fin m)) =
                            active_constraint_face A b ({j} : Set (Fin m))) →
                        nonimplicitPositiveSupportCard A b u ≤
                          nonimplicitPositiveSupportCard A b u' := by
  classical
  let P : ℕ → Prop := fun t ↦
    ∃ u : Fin m → ℝ,
      (∀ k : Fin m, 0 ≤ u k) ∧
        u ᵥ* A = A i ∧
          u ⬝ᵥ b = b i ∧
            (∀ k : Fin m, 0 < u k →
              is_implicit_equality A b k ∨
                active_constraint_face A b ({k} : Set (Fin m)) =
                  active_constraint_face A b ({j} : Set (Fin m))) ∧
              nonimplicitPositiveSupportCard A b u = t
  have hP : ∃ t, P t := by
    rcases exists_sameFacetRowMultiplier_of_eq_singletonFace A b i j hi hfacet hij_face with
      ⟨u, hu_nonneg, hu_row, hu_rhs, hu_same⟩
    -- Package one existing certificate so `Nat.find` can minimize its non-implicit support size.
    exact
      ⟨nonimplicitPositiveSupportCard A b u,
        u, hu_nonneg, hu_row, hu_rhs, hu_same, rfl⟩
  rcases Nat.find_spec hP with ⟨u, hu_nonneg, hu_row, hu_rhs, hu_same, hu_card⟩
  refine ⟨u, hu_nonneg, hu_row, hu_rhs, hu_same, ?_⟩
  intro u' hu'_nonneg hu'_row hu'_rhs hu'_same
  have hmin :
      Nat.find hP ≤ nonimplicitPositiveSupportCard A b u' := by
    -- Any competing certificate contributes another admissible support count, so minimality
    -- bounds it from below.
    exact Nat.find_min' hP ⟨u', hu'_nonneg, hu'_row, hu'_rhs, hu'_same, rfl⟩
  -- Rewrite the chosen minimal count back to the concrete support cardinality of `u`.
  simpa [hu_card] using hmin

/-- Helper for Theorem 3.27: a feasible point that is strict on row `j` is automatically strict on
every row whose singleton active face agrees with the singleton face of `j`. -/
lemma sameFacetRow_strict_of_eq_singletonFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m)))
    {x : Fin n → ℝ}
    (hxP : x ∈ polyhedron_le_set A b)
    (hxj_lt : (A *ᵥ x) j < b j) :
    (A *ᵥ x) i < b i := by
  have hxi_le : (A *ᵥ x) i ≤ b i := hxP i
  have hxi_ne : (A *ᵥ x) i ≠ b i := by
    intro hxi_eq
    have hxi_face : x ∈ active_constraint_face A b ({i} : Set (Fin m)) := by
      -- Activating only row `i` is immediate once `x` is feasible and tight on that row.
      refine (mem_active_constraint_face_iff).2 ?_
      constructor
      · intro k hk
        have hki : k = i := by simpa using hk
        simpa [hki] using hxi_eq
      · intro k _hk
        exact hxP k
    have hxj_face : x ∈ active_constraint_face A b ({j} : Set (Fin m)) := by
      -- Equal singleton faces transport membership from row `i` to row `j`.
      simpa [hij_face] using hxi_face
    have hxj_eq : (A *ᵥ x) j = b j :=
      (mem_active_constraint_face_iff.mp hxj_face).1 j (by simp)
    exact (ne_of_lt hxj_lt) hxj_eq
  exact lt_of_le_of_ne hxi_le hxi_ne

/-- Helper for Theorem 3.27: the singleton multiplier on a remaining row has exactly one
non-implicit positive-support entry. -/
lemma nonimplicitPositiveSupportCard_single
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i : Fin m)
    (hi : i ∈ remaining_inequality_indices A b) :
    nonimplicitPositiveSupportCard A b (Pi.single i (1 : ℝ)) = 1 := by
  classical
  have hi_not_implicit : ¬ is_implicit_equality A b i :=
    (mem_remaining_inequality_indices_iff A b i).1 hi
  let uSingle : Fin m → ℝ := Pi.single i (1 : ℝ)
  let S := {k : Fin m // ¬ is_implicit_equality A b k ∧ 0 < uSingle k}
  have hS : S ≃ {k : Fin m // k = i} := by
    refine
      { toFun := fun x ↦ ⟨x.1, by
            by_contra hxi
            have hxzero : uSingle x.1 = 0 := by
              simp [uSingle, hxi]
            exact (not_lt_of_ge (by simp [hxzero] : uSingle x.1 ≤ 0)) x.2.2⟩
        invFun := fun x ↦ ⟨i, hi_not_implicit, by simp [uSingle]⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro x
      apply Subtype.ext
      by_contra hxi
      have hxzero : uSingle x.1 = 0 := by
        simp [uSingle, hxi]
      exact (not_lt_of_ge (by simp [hxzero] : uSingle x.1 ≤ 0)) x.2.2
    · intro u
      apply Subtype.ext
      simp [u.2.symm]
  -- The non-implicit positive support of the singleton coefficient vector is equivalent to `PUnit`.
  have hsingleton : Nat.card {k : Fin m // k = i} = 1 := by
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype_eq i : Fintype.card {k : Fin m // k = i} = 1)
  exact (Nat.card_congr hS).trans hsingleton

/-- Helper for Theorem 3.27: two distinct non-implicit positive-support rows force the support
cardinality to be strictly larger than one. -/
lemma nonimplicitPositiveSupportCard_gt_one_of_two
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (u : Fin m → ℝ)
    (k l : Fin m)
    (hk : ¬ is_implicit_equality A b k ∧ 0 < u k)
    (hl : ¬ is_implicit_equality A b l ∧ 0 < u l)
    (hkl : k ≠ l) :
    1 < nonimplicitPositiveSupportCard A b u := by
  let S := {r : Fin m // ¬ is_implicit_equality A b r ∧ 0 < u r}
  have hS_nontrivial : Nontrivial S := by
    -- The two distinct support witnesses produce distinct points of the support subtype.
    refine ⟨⟨k, hk⟩, ⟨l, hl⟩, ?_⟩
    intro hEq
    exact hkl (congrArg Subtype.val hEq)
  simpa [nonimplicitPositiveSupportCard, S] using
    (Finite.one_lt_card_iff_nontrivial.mpr hS_nontrivial)

/-- Helper for Theorem 3.27: a support-minimal same-facet multiplier already has at most one
non-implicit positive-support row. -/
lemma existsSameFacetRowMultiplier_cardMinimal_subsingleton
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m))) :
    ∃ u : Fin m → ℝ,
      (∀ k : Fin m, 0 ≤ u k) ∧
        u ᵥ* A = A i ∧
          u ⬝ᵥ b = b i ∧
            (∀ k : Fin m, 0 < u k →
              is_implicit_equality A b k ∨
                active_constraint_face A b ({k} : Set (Fin m)) =
                  active_constraint_face A b ({j} : Set (Fin m))) ∧
              ∀ k l : Fin m,
                ¬ is_implicit_equality A b k →
                  ¬ is_implicit_equality A b l →
                    0 < u k →
                      0 < u l →
                        k = l := by
  rcases existsSameFacetRowMultiplier_cardMinimal A b i j hi hfacet hij_face with
    ⟨u, hu_nonneg, hu_row, hu_rhs, hu_same, hu_min⟩
  refine ⟨u, hu_nonneg, hu_row, hu_rhs, hu_same, ?_⟩
  intro k l hk_nonimplicit hl_nonimplicit hk_pos hl_pos
  by_contra hkl_ne
  have hcard_le_one : nonimplicitPositiveSupportCard A b u ≤ 1 := by
    let uSingle : Fin m → ℝ := Pi.single i (1 : ℝ)
    have hsingle_nonneg : ∀ r : Fin m, 0 ≤ uSingle r := by
      intro r
      by_cases hr : r = i
      · simp [uSingle, hr]
      · simp [uSingle, hr]
    have hsingle_row : uSingle ᵥ* A = A i := by
      -- The singleton multiplier reproduces row `i` exactly.
      ext c
      change Pi.single i (1 : ℝ) ⬝ᵥ (fun x : Fin m ↦ A x c) = A i c
      simpa using (single_one_dotProduct i (fun x : Fin m ↦ A x c))
    have hsingle_rhs : uSingle ⬝ᵥ b = b i := by
      simpa [uSingle] using single_one_dotProduct i b
    have hsingle_same :
        ∀ r : Fin m, 0 < uSingle r →
          is_implicit_equality A b r ∨
            active_constraint_face A b ({r} : Set (Fin m)) =
              active_constraint_face A b ({j} : Set (Fin m)) := by
      intro r hr_pos
      by_cases hr : r = i
      · subst hr
        exact Or.inr hij_face
      · have hr_zero : uSingle r = 0 := by
          simp [uSingle, hr]
        linarith
    have hmin_single :=
      hu_min uSingle hsingle_nonneg hsingle_row hsingle_rhs hsingle_same
    -- Minimality compares the chosen certificate against the obvious singleton support.
    simpa [uSingle, nonimplicitPositiveSupportCard_single A b i hi] using hmin_single
  have hcard_gt_one : 1 < nonimplicitPositiveSupportCard A b u := by
    exact
      nonimplicitPositiveSupportCard_gt_one_of_two A b u k l
        ⟨hk_nonimplicit, hk_pos⟩
        ⟨hl_nonimplicit, hl_pos⟩
        hkl_ne
  exact (not_lt_of_ge hcard_le_one) hcard_gt_one

/-- Helper for Theorem 3.27: a support-minimal same-facet multiplier can be normalized to one
non-implicit anchor row plus an implicit-row remainder. -/
lemma sameFacetRow_eq_pos_smul_anchor_add_implicit
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m))) :
    ∃ k : Fin m, ∃ lam : ℝ, ∃ uImp : Fin m → ℝ,
      k ∈ remaining_inequality_indices A b ∧
        active_constraint_face A b ({k} : Set (Fin m)) =
          active_constraint_face A b ({j} : Set (Fin m)) ∧
        0 < lam ∧
        uImp k = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp r = 0) ∧
        uImp ᵥ* A + lam • A k = A i ∧
        uImp ⬝ᵥ b + lam * b k = b i := by
  rcases existsSameFacetRowMultiplier_cardMinimal_subsingleton A b i j hi hfacet hij_face with
    ⟨u, hu_nonneg, hu_row, hu_rhs, hu_same, hu_subsingleton⟩
  rcases exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b i hi with
    ⟨xP, hxP, hxP_lt⟩
  have h_nonimplicit_support :
      ∃ k : Fin m, ¬ is_implicit_equality A b k ∧ 0 < u k := by
    by_contra hno
    have hsupport_implicit :
        ∀ k : Fin m, 0 < u k → is_implicit_equality A b k := by
      intro k hk_pos
      by_contra hk_not_implicit
      exact hno ⟨k, hk_not_implicit, hk_pos⟩
    have hdot_eq :
        u ⬝ᵥ (A *ᵥ xP) = u ⬝ᵥ b := by
      unfold dotProduct
      refine Finset.sum_congr rfl ?_
      intro k hk
      by_cases hk_pos : 0 < u k
      · have hk_eq : (A *ᵥ xP) k = b k := hsupport_implicit k hk_pos hxP
        rw [hk_eq]
      · have hk_zero : u k = 0 := by linarith [hu_nonneg k]
        simp [hk_zero]
    have hxPi_eq :
        (A *ᵥ xP) i = b i := by
      calc
        (A *ᵥ xP) i = A i ⬝ᵥ xP := by simp [Matrix.mulVec]
        _ = (u ᵥ* A) ⬝ᵥ xP := by rw [← hu_row]
        _ = u ⬝ᵥ (A *ᵥ xP) := by rw [← Matrix.dotProduct_mulVec]
        _ = u ⬝ᵥ b := hdot_eq
        _ = b i := hu_rhs
    exact (ne_of_lt hxP_lt) hxPi_eq
  rcases h_nonimplicit_support with ⟨k, hk_not_implicit, hk_pos⟩
  have hk_remaining : k ∈ remaining_inequality_indices A b :=
    (mem_remaining_inequality_indices_iff A b k).2 hk_not_implicit
  have hk_face :
      active_constraint_face A b ({k} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m)) := by
    rcases hu_same k hk_pos with hk_implicit | hk_face
    · exact False.elim (hk_not_implicit hk_implicit)
    · exact hk_face
  let uImp : Fin m → ℝ := fun r ↦ if r = k then 0 else u r
  have huImp_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp r = 0 := by
    intro r hr_not_implicit hrk
    dsimp [uImp]
    rw [if_neg hrk]
    by_cases hr_pos : 0 < u r
    · have hr_eq :
        r = k :=
          hu_subsingleton r k hr_not_implicit hk_not_implicit hr_pos hk_pos
      exact False.elim (hrk hr_eq)
    · have hr_zero : u r = 0 := by linarith [hu_nonneg r]
      exact hr_zero
  have hu_split :
      u = uImp + u k • Pi.single k (1 : ℝ) := by
    funext r
    by_cases hrk : r = k
    · subst hrk
      simp [uImp]
    · simp [uImp, hrk]
  have hsingle_row :
      (u k • Pi.single k (1 : ℝ)) ᵥ* A = u k • A k := by
    ext c
    rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single k]
    · simp
    · intro r _ hrk
      simp [hrk]
    · simp
  have hadd_row :
      (uImp + u k • Pi.single k (1 : ℝ)) ᵥ* A =
        uImp ᵥ* A + (u k • Pi.single k (1 : ℝ)) ᵥ* A := by
    ext c
    simp [Matrix.vecMul, dotProduct, add_mul, Finset.sum_add_distrib]
  have huImp_row :
      uImp ᵥ* A + u k • A k = A i := by
    -- Split the row certificate into the unique non-implicit anchor row and the residual tail.
    calc
      uImp ᵥ* A + u k • A k
          = uImp ᵥ* A + (u k • Pi.single k (1 : ℝ)) ᵥ* A := by
              rw [hsingle_row]
      _ = (uImp + u k • Pi.single k (1 : ℝ)) ᵥ* A := by
            rw [hadd_row]
      _ = u ᵥ* A := by rw [← hu_split]
      _ = A i := hu_row
  have hsingle_rhs :
      (u k • Pi.single k (1 : ℝ)) ⬝ᵥ b = u k * b k := by
    rw [dotProduct, Finset.sum_eq_single k]
    · simp
    · intro r _ hrk
      simp [hrk]
    · simp
  have hadd_rhs :
      (uImp + u k • Pi.single k (1 : ℝ)) ⬝ᵥ b =
        uImp ⬝ᵥ b + (u k • Pi.single k (1 : ℝ)) ⬝ᵥ b := by
    simp [dotProduct, add_mul, Finset.sum_add_distrib]
  have huImp_rhs :
      uImp ⬝ᵥ b + u k * b k = b i := by
    -- The same coefficient split works for the right-hand side scalar identity.
    calc
      uImp ⬝ᵥ b + u k * b k
          = uImp ⬝ᵥ b + (u k • Pi.single k (1 : ℝ)) ⬝ᵥ b := by
              rw [hsingle_rhs]
      _ = (uImp + u k • Pi.single k (1 : ℝ)) ⬝ᵥ b := by
            rw [hadd_rhs]
      _ = u ⬝ᵥ b := by rw [← hu_split]
      _ = b i := hu_rhs
  have huImp_at_anchor : uImp k = 0 := by
    simp [uImp]
  exact
    ⟨k, u k, uImp, hk_remaining, hk_face, hk_pos, huImp_at_anchor,
      huImp_zero, huImp_row, huImp_rhs⟩

/-- Helper for Theorem 3.27: once a same-facet row is normalized to one anchor row plus implicit
rows, the target-row deficit on the ambient affine hull is a scalar multiple of the anchor-row
deficit. -/
lemma sameFacetRow_sub_eq_smul_anchorSub_of_implicitEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (uImp : Fin m → ℝ)
    (lam : ℝ)
    (hk_remaining : k ∈ remaining_inequality_indices A b)
    (huk_zero : uImp k = 0)
    (huImp_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp r = 0)
    (hrow : uImp ᵥ* A + lam • A k = A i)
    (hrhs : uImp ⬝ᵥ b + lam * b k = b i)
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b)) :
    (A *ᵥ x) i - b i = lam * ((A *ᵥ x) k - b k) := by
  let _ := hk_remaining
  have hxImpEqVec : implicit_equality_matrix A b *ᵥ x = implicit_equality_rhs A b := by
    -- Every point of the ambient affine hull already satisfies the implicit-equality subsystem.
    have hxImpEqSet :
        x ∈ ({y : Fin n → ℝ |
          implicit_equality_matrix A b *ᵥ y = implicit_equality_rhs A b} : Set (Fin n → ℝ)) := by
      rw [← affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set A b]
      exact hxAff
    simpa using hxImpEqSet
  have hxImpEq :
      ∀ r : Fin m, is_implicit_equality A b r → (A *ᵥ x) r = b r := by
    intro r hr_implicit
    have hxr := congrArg (fun f ↦ f ⟨r, hr_implicit⟩) hxImpEqVec
    simpa [implicit_equality_mulVec_apply, implicit_equality_rhs_apply] using hxr
  have huImp_eval :
      uImp ⬝ᵥ (A *ᵥ x) = uImp ⬝ᵥ b := by
    -- The residual multiplier only sees implicit rows, so it evaluates identically on `x` and `b`.
    unfold dotProduct
    refine Finset.sum_congr rfl ?_
    intro r hr
    by_cases hr_implicit : is_implicit_equality A b r
    · rw [hxImpEq r hr_implicit]
    · by_cases hrk : r = k
      · subst hrk
        simp [huk_zero]
      · have hur_zero : uImp r = 0 := huImp_zero r hr_implicit hrk
        simp [hur_zero]
  -- Route correction: keep the same-face normalization as a deficit identity on `affineSpan ℝ P`;
  -- downstream proofs can specialize this to anchor-row equality only when needed.
  calc
    (A *ᵥ x) i - b i
        = ((uImp ᵥ* A + lam • A k) ⬝ᵥ x) - (uImp ⬝ᵥ b + lam * b k) := by
            rw [hrow, hrhs]
            simp [Matrix.mulVec]
    _ = ((uImp ᵥ* A) ⬝ᵥ x + (lam • A k) ⬝ᵥ x) - (uImp ⬝ᵥ b + lam * b k) := by
          simp [dotProduct, add_mul, Finset.sum_add_distrib]
    _ = (uImp ⬝ᵥ (A *ᵥ x) + lam * (A *ᵥ x) k) - (uImp ⬝ᵥ b + lam * b k) := by
          rw [Matrix.dotProduct_mulVec]
          simp [Matrix.mulVec]
    _ = lam * ((A *ᵥ x) k - b k) := by
          rw [huImp_eval]
          ring

/-- Helper for Theorem 3.27: once a same-facet row is normalized to one anchor row plus implicit
rows, equality on the anchor row transports to the target row on the ambient affine hull. -/
lemma sameFacetRow_eq_of_anchorRowEq_and_implicitEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (uImp : Fin m → ℝ)
    (lam : ℝ)
    (hk : k ∈ remaining_inequality_indices A b)
    (huk_zero : uImp k = 0)
    (huImp_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp r = 0)
    (hrow : uImp ᵥ* A + lam • A k = A i)
    (hrhs : uImp ⬝ᵥ b + lam * b k = b i)
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxk : (A *ᵥ x) k = b k) :
    (A *ᵥ x) i = b i := by
  have hsub :
      (A *ᵥ x) i - b i = lam * ((A *ᵥ x) k - b k) :=
    sameFacetRow_sub_eq_smul_anchorSub_of_implicitEq
      A b i k uImp lam hk huk_zero huImp_zero hrow hrhs hxAff
  -- Specializing the deficit identity to a tight anchor row recovers the target equality.
  have hzero : (A *ᵥ x) i - b i = 0 := by
    rw [hsub, hxk]
    ring
  linarith

/-- Helper for Theorem 3.27: if a same-facet row is normalized to a positive multiple of an anchor
row plus implicit rows, then tightness of the target row on `affineSpan ℝ P` forces tightness of
that anchor row. -/
lemma anchorRow_eq_of_sameFacetRowEq_and_implicitEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (uImp : Fin m → ℝ)
    (lam : ℝ)
    (hk : k ∈ remaining_inequality_indices A b)
    (huk_zero : uImp k = 0)
    (huImp_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp r = 0)
    (hrow : uImp ᵥ* A + lam • A k = A i)
    (hrhs : uImp ⬝ᵥ b + lam * b k = b i)
    (hlam : 0 < lam)
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxi : (A *ᵥ x) i = b i) :
    (A *ᵥ x) k = b k := by
  have hsub :
      (A *ᵥ x) i - b i = lam * ((A *ᵥ x) k - b k) :=
    sameFacetRow_sub_eq_smul_anchorSub_of_implicitEq
      A b i k uImp lam hk huk_zero huImp_zero hrow hrhs hxAff
  -- The positive anchor coefficient lets us divide the deficit identity by `lam`.
  have hzero : lam * ((A *ᵥ x) k - b k) = 0 := by
    calc
      lam * ((A *ᵥ x) k - b k) = (A *ᵥ x) i - b i := by rw [hsub]
      _ = 0 := by simp [hxi]
  have hdiff_zero : (A *ᵥ x) k - b k = 0 := by
    nlinarith
  linarith

/-- Helper for Theorem 3.27: row-`j` tightness on `affineSpan ℝ P` propagates to the anchor row
returned by the same-facet multiplier certificate for row `j` itself. -/
lemma sameFacetSelf_exists_anchor_eq_on_affineHull
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m)
    (hj : j ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxj : (A *ᵥ x) j = b j) :
    ∃ k : Fin m, ∃ lam : ℝ, ∃ uImp : Fin m → ℝ,
      k ∈ remaining_inequality_indices A b ∧
        active_constraint_face A b ({k} : Set (Fin m)) =
          active_constraint_face A b ({j} : Set (Fin m)) ∧
        0 < lam ∧
        uImp k = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp r = 0) ∧
        uImp ᵥ* A + lam • A k = A j ∧
        uImp ⬝ᵥ b + lam * b k = b j ∧
        (A *ᵥ x) k = b k := by
  rcases sameFacetRow_eq_pos_smul_anchor_add_implicit A b j j hj hfacet rfl with
    ⟨k, lam, uImp, hk, hk_face, hlam, huk_zero, huImp_zero, hrow, hrhs⟩
  refine ⟨k, lam, uImp, hk, hk_face, hlam, huk_zero, huImp_zero, hrow, hrhs, ?_⟩
  -- Route correction: isolate the anchor returned by the existing normalization API before trying
  -- to compare arbitrary same-facet rows to the fixed row `j`.
  exact
    anchorRow_eq_of_sameFacetRowEq_and_implicitEq
      A b j k uImp lam hk huk_zero huImp_zero hrow hrhs hlam hxAff hxj

/-- Helper for Theorem 3.27: every point of one singleton active face already satisfies the
defining equality of any equal singleton active face. -/
lemma sameFacetRow_eq_at_singletonFacePoint
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m)))
    {y : Fin n → ℝ}
    (hy : y ∈ active_constraint_face A b ({j} : Set (Fin m))) :
    (A *ᵥ y) i = b i := by
  have hyi :
      y ∈ active_constraint_face A b ({i} : Set (Fin m)) := by
    -- Equality of the singleton faces transports the point from row `j` to row `i`.
    simpa [hij_face] using hy
  -- Reading off the active row equation at that transported point gives the target equality.
  exact (mem_active_constraint_face_iff.mp hyi).1 i (by simp)

/-- Helper for Theorem 3.27: if two singleton active faces agree, then activating both rows does
not cut out a smaller face. -/
lemma activeConstraintFace_pair_eq_of_eq_singletonFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m))) :
    active_constraint_face A b ({i, j} : Set (Fin m)) =
      active_constraint_face A b ({j} : Set (Fin m)) := by
  ext x
  constructor
  · intro hx
    -- Activating both rows certainly activates row `j`.
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro k hk
      have hkj : k = j := by simpa using hk
      simpa [hkj] using (mem_active_constraint_face_iff.mp hx).1 j (by simp)
    · intro k hk
      exact mem_polyhedron_of_mem_active_constraint_face hx k
  · intro hx
    have hxi : x ∈ active_constraint_face A b ({i} : Set (Fin m)) := by
      simpa [hij_face] using hx
    -- Equality of the singleton faces transports row-`i` activity back to the pair face.
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro k hk
      rcases Set.mem_insert_iff.mp hk with hk | hk
      · simpa [hk] using (mem_active_constraint_face_iff.mp hxi).1 i (by simp)
      · have hkj : k = j := by simpa using hk
        simpa [hkj] using (mem_active_constraint_face_iff.mp hx).1 j (by simp)
    · intro k hk
      exact mem_polyhedron_of_mem_active_constraint_face hx k

/-- Helper for Theorem 3.27: every point of the affine span of a singleton facet also lies on the
hyperplane of any row defining that same singleton face. -/
lemma sameFacetRow_eq_on_affineSpan_singletonFacet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m)))
    {x : Fin n → ℝ}
    (hxAff :
      x ∈ affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))) :
    (A *ᵥ x) i = b i := by
  have hpair_eq :
      active_constraint_face A b ({i, j} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m)) :=
    activeConstraintFace_pair_eq_of_eq_singletonFace A b i j hij_face
  have hpair_subset :
      active_constraint_face A b ({i, j} : Set (Fin m)) ⊆
        {y : Fin n → ℝ | A i ⬝ᵥ y = b i} := by
    intro y hy
    have hyi : (A *ᵥ y) i = b i :=
      (mem_active_constraint_face_iff.mp hy).1 i (by simp)
    simpa [Matrix.mulVec] using hyi
  have hpair_aff :
      x ∈ affineSpan ℝ (active_constraint_face A b ({i, j} : Set (Fin m))) := by
    simpa [hpair_eq] using hxAff
  have hAffHyper :=
    affineSpan_subset_hyperplane_of_subset hpair_subset
  -- Passing to the affine span preserves the row-`i` equality because the whole pair face lies in
  -- the corresponding hyperplane.
  simpa [Matrix.mulVec] using hAffHyper hpair_aff

/-- Helper for Theorem 3.27: every ambient affine-hull point already satisfies each implicit row
equation. -/
lemma row_eq_of_implicit_on_affineHull
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r : Fin m)
    (hr : is_implicit_equality A b r)
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b)) :
    (A *ᵥ x) r = b r := by
  have hxImpEqSet :
      x ∈ ({y : Fin n → ℝ |
        implicit_equality_matrix A b *ᵥ y = implicit_equality_rhs A b} : Set (Fin n → ℝ)) := by
    rw [← affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set A b]
    exact hxAff
  -- Read off the `r`-component of the implicit-equality system.
  have hxr := congrArg (fun f ↦ f ⟨r, hr⟩) hxImpEqSet
  simpa [implicit_equality_mulVec_apply, implicit_equality_rhs_apply] using hxr

/-- Helper for Theorem 3.27: evaluating a row-multiplier deficit identity at a fixed point turns it
into the corresponding gap identity. -/
lemma gap_dotProduct_eq_gap_of_rowMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i : Fin m)
    (u : Fin m → ℝ)
    (hrow : u ᵥ* A = A i)
    (hrhs : u ⬝ᵥ b = b i)
    {xP : Fin n → ℝ} :
    u ⬝ᵥ (fun r : Fin m ↦ b r - (A *ᵥ xP) r) = b i - (A *ᵥ xP) i := by
  have hsub :
      (A *ᵥ xP) i - b i = u ⬝ᵥ (fun r : Fin m ↦ (A *ᵥ xP) r - b r) :=
    rowSub_eq_dotProduct_rowSub_of_multiplier A b i u hrow hrhs
  -- Negating the deficit identity replaces row deficits by row gaps.
  calc
    u ⬝ᵥ (fun r : Fin m ↦ b r - (A *ᵥ xP) r)
        = ∑ r : Fin m, -(u r * ((A *ᵥ xP) r - b r)) := by
            unfold dotProduct
            refine Finset.sum_congr rfl ?_
            intro r hr
            ring
    _ = -(u ⬝ᵥ (fun r : Fin m ↦ (A *ᵥ xP) r - b r)) := by
          unfold dotProduct
          rw [Finset.sum_neg_distrib]
    _ = -((A *ᵥ xP) i - b i) := by rw [hsub]
    _ = b i - (A *ᵥ xP) i := by ring

/-- Helper for Theorem 3.27: every point of the singleton facet for `k` lies on the
cross-multiplied gap hyperplane associated to any row defining the same singleton face. -/
lemma sameFacetRow_gapHyperplane_contains_singletonFacet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r k : Fin m)
    (hrk_face :
      active_constraint_face A b ({r} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m)))
    (xP : Fin n → ℝ)
    {y : Fin n → ℝ}
    (hy : y ∈ active_constraint_face A b ({k} : Set (Fin m))) :
    let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
    ((gap k) • A r - (gap r) • A k) ⬝ᵥ y = (gap k) * b r - (gap r) * b k := by
  let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
  have hyr : (A *ᵥ y) r = b r :=
    sameFacetRow_eq_at_singletonFacePoint A b r k hrk_face hy
  have hyk : (A *ᵥ y) k = b k :=
    (mem_active_constraint_face_iff.mp hy).1 k (by simp)
  -- Once both singleton-face rows are tight, the hyperplane equation is just a row evaluation.
  calc
    (((gap k) • A r - (gap r) • A k) ⬝ᵥ y)
        = gap k * (A *ᵥ y) r - gap r * (A *ᵥ y) k := by
            simp [gap, Matrix.mulVec]
    _ = gap k * b r - gap r * b k := by rw [hyr, hyk]

/-- Helper for Theorem 3.27: if a row is tight on the singleton facet of `k` and also at one
strict feasible point for row `k`, then that row is already an implicit equality. -/
lemma rowEqAtStrictPoint_of_singletonFacet_forces_implicit
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    {xP : Fin n → ℝ}
    (hxP : xP ∈ polyhedron_le_set A b)
    (hxP_lt : (A *ᵥ xP) k < b k)
    (hrow_on_face :
      ∀ y : Fin n → ℝ,
        y ∈ active_constraint_face A b ({k} : Set (Fin m)) →
          (A *ᵥ y) i = b i)
    (hxP_eq : (A *ᵥ xP) i = b i) :
    is_implicit_equality A b i := by
  by_contra hi_not_implicit
  have hi_remaining : i ∈ remaining_inequality_indices A b :=
    (mem_remaining_inequality_indices_iff A b i).2 hi_not_implicit
  have hsubset :
      active_constraint_face A b ({k} : Set (Fin m)) ⊆
        active_constraint_face A b ({i} : Set (Fin m)) := by
    intro y hy
    have hyP : y ∈ polyhedron_le_set A b :=
      mem_polyhedron_of_mem_active_constraint_face hy
    -- Every point of the singleton facet already satisfies the row-`i` equality by hypothesis.
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro l hl
      have hli : l = i := by simpa using hl
      simpa [hli] using hrow_on_face y hy
    · intro l _hl
      exact hyP l
  have hik_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m)) :=
    singletonActiveConstraintFace_eq_of_subset_of_isFacet A b i k hi_remaining hfacet hsubset
  have hxi_lt : (A *ᵥ xP) i < b i :=
    sameFacetRow_strict_of_eq_singletonFace A b i k hik_face hxP hxP_lt
  exact (ne_of_lt hxi_lt) hxP_eq

/-- Helper for Theorem 3.27: if rows `i` and `k` are both normalized against the same remaining
anchor row modulo implicit rows, then row-`k` tightness on the ambient affine hull forces
row-`i` tightness there as well. -/
lemma sameFacetRow_eq_of_commonAnchor
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k a : Fin m)
    (uImp_i uImp_k : Fin m → ℝ)
    (lam_i lam_k : ℝ)
    (ha : a ∈ remaining_inequality_indices A b)
    (hui_zero : uImp_i a = 0)
    (huImp_i_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp_i r = 0)
    (hrow_i : uImp_i ᵥ* A + lam_i • A a = A i)
    (hrhs_i : uImp_i ⬝ᵥ b + lam_i * b a = b i)
    (huk_zero : uImp_k a = 0)
    (huImp_k_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp_k r = 0)
    (hrow_k : uImp_k ᵥ* A + lam_k • A a = A k)
    (hrhs_k : uImp_k ⬝ᵥ b + lam_k * b a = b k)
    (hlam_k : 0 < lam_k)
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxk : (A *ᵥ x) k = b k) :
    (A *ᵥ x) i = b i := by
  -- First transport row-`k` tightness to the shared anchor row.
  have hxa : (A *ᵥ x) a = b a := by
    exact
      anchorRow_eq_of_sameFacetRowEq_and_implicitEq
        A b k a uImp_k lam_k ha huk_zero huImp_k_zero hrow_k hrhs_k hlam_k hxAff hxk
  -- Then use the same anchor normalization to recover row-`i` tightness.
  exact
    sameFacetRow_eq_of_anchorRowEq_and_implicitEq
      A b i a uImp_i lam_i ha hui_zero huImp_i_zero hrow_i hrhs_i hxAff hxa

/-- Helper for Theorem 3.27: composing two positive-anchor-plus-implicit decompositions keeps the
same normal form, with the anchor pushed to the second decomposition's anchor row. -/
lemma compose_anchorAddImplicit_decomposition
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k a : Fin m)
    (uImp_i uImp_k : Fin m → ℝ)
    (lam_i lam_k : ℝ)
    (ha : a ∈ remaining_inequality_indices A b)
    (hui_zero : uImp_i k = 0)
    (huImp_i_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_i r = 0)
    (hrow_i : uImp_i ᵥ* A + lam_i • A k = A i)
    (hrhs_i : uImp_i ⬝ᵥ b + lam_i * b k = b i)
    (huk_zero : uImp_k a = 0)
    (huImp_k_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp_k r = 0)
    (hrow_k : uImp_k ᵥ* A + lam_k • A a = A k)
    (hrhs_k : uImp_k ⬝ᵥ b + lam_k * b a = b k) :
    ∃ uImp : Fin m → ℝ,
      uImp a = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp r = 0) ∧
        uImp ᵥ* A + (lam_i * lam_k) • A a = A i ∧
        uImp ⬝ᵥ b + (lam_i * lam_k) * b a = b i := by
  let uImp : Fin m → ℝ := fun r ↦ uImp_i r + lam_i * uImp_k r
  refine ⟨uImp, ?_, ?_, ?_, ?_⟩
  · -- The composed remainder still vanishes at the prescribed anchor row `a`.
    by_cases hka : k = a
    · subst hka
      simp [uImp, hui_zero, huk_zero]
    · have hua_zero : uImp_i a = 0 := by
        have ha_not_implicit : ¬ is_implicit_equality A b a :=
          (mem_remaining_inequality_indices_iff A b a).1 ha
        exact huImp_i_zero a ha_not_implicit (fun h ↦ hka h.symm)
      simp [uImp, hua_zero, huk_zero]
  · intro r hr_not_implicit hra
    -- Away from the final anchor `a`, both tails vanish on non-implicit rows.
    by_cases hrk : r = k
    · have hui_at_r : uImp_i r = 0 := by simpa [hrk] using hui_zero
      have huk_at_r : uImp_k r = 0 := huImp_k_zero r hr_not_implicit hra
      simp [uImp, hui_at_r, huk_at_r]
    · have hui_at_r : uImp_i r = 0 := huImp_i_zero r hr_not_implicit hrk
      have huk_at_r : uImp_k r = 0 := huImp_k_zero r hr_not_implicit hra
      simp [uImp, hui_at_r, huk_at_r]
  · -- Expand the first decomposition, then substitute the second anchor decomposition for `A k`.
    calc
      uImp ᵥ* A + (lam_i * lam_k) • A a
          = (uImp_i ᵥ* A + lam_i • (uImp_k ᵥ* A)) + (lam_i * lam_k) • A a := by
              ext c
              simp [uImp, Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul,
                Finset.mul_sum, mul_assoc]
      _ = uImp_i ᵥ* A + lam_i • (uImp_k ᵥ* A + lam_k • A a) := by
            ext c
            simp [smul_add, mul_smul]
            ring
      _ = uImp_i ᵥ* A + lam_i • A k := by rw [hrow_k]
      _ = A i := hrow_i
  · -- The right-hand side scalar identity composes by the same linearity calculation.
    calc
      uImp ⬝ᵥ b + (lam_i * lam_k) * b a
          = (uImp_i ⬝ᵥ b + lam_i * (uImp_k ⬝ᵥ b)) + (lam_i * lam_k) * b a := by
              simp [uImp, dotProduct, Finset.sum_add_distrib, add_mul, Finset.mul_sum,
                mul_assoc]
      _ = uImp_i ⬝ᵥ b + lam_i * (uImp_k ⬝ᵥ b + lam_k * b a) := by
            ring
      _ = uImp_i ⬝ᵥ b + lam_i * b k := by rw [hrhs_k]
      _ = b i := hrhs_i

/-- Helper for Theorem 3.27: if rows `i` and `a` are both normalized against one common anchor
row modulo implicit rows, then eliminating that common anchor yields the prescribed-anchor normal
form for row `i` against row `a`. -/
lemma sameFacetRow_eq_pos_smul_fixedAnchor_add_implicit_of_commonAnchor
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i a k : Fin m)
    (uImp_i uImp_a : Fin m → ℝ)
    (lam_i lam_a : ℝ)
    (ha : a ∈ remaining_inequality_indices A b)
    (hui_zero : uImp_i k = 0)
    (huImp_i_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_i r = 0)
    (hrow_i : uImp_i ᵥ* A + lam_i • A k = A i)
    (hrhs_i : uImp_i ⬝ᵥ b + lam_i * b k = b i)
    (hlam_i : 0 < lam_i)
    (hua_zero : uImp_a k = 0)
    (huImp_a_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_a r = 0)
    (hrow_a : uImp_a ᵥ* A + lam_a • A k = A a)
    (hrhs_a : uImp_a ⬝ᵥ b + lam_a * b k = b a)
    (hlam_a : 0 < lam_a) :
    ∃ lam : ℝ, ∃ uImp : Fin m → ℝ,
      0 < lam ∧
        uImp a = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp r = 0) ∧
        uImp ᵥ* A + lam • A a = A i ∧
        uImp ⬝ᵥ b + lam * b a = b i := by
  let lam : ℝ := lam_i / lam_a
  let uImp : Fin m → ℝ := fun r ↦ uImp_i r - lam * uImp_a r
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos hlam_i hlam_a
  have hrow_a_sub : A a - uImp_a ᵥ* A = lam_a • A k := by
    -- Rewrite the anchor row as the common-anchor contribution plus the implicit tail.
    ext c
    have hc := congrFun hrow_a c
    dsimp at hc ⊢
    linarith
  have hrhs_a_sub : b a - uImp_a ⬝ᵥ b = lam_a * b k := by
    linarith
  have huImp_a_eq_zero : uImp a = 0 := by
    have ha_not_implicit : ¬ is_implicit_equality A b a :=
      (mem_remaining_inequality_indices_iff A b a).1 ha
    by_cases hka : k = a
    · subst hka
      simp [uImp, hui_zero, hua_zero]
    · have hui_a : uImp_i a = 0 := huImp_i_zero a ha_not_implicit (fun hak ↦ hka hak.symm)
      have hua_a : uImp_a a = 0 := huImp_a_zero a ha_not_implicit (fun hak ↦ hka hak.symm)
      simp [uImp, hui_a, hua_a]
  have huImp_vecMul :
      uImp ᵥ* A = uImp_i ᵥ* A - (lam • uImp_a) ᵥ* A := by
    simpa [uImp, Pi.sub_apply] using Matrix.sub_vecMul A uImp_i (lam • uImp_a)
  have hsmul_uImp_vecMul :
      (lam • uImp_a) ᵥ* A = lam • (uImp_a ᵥ* A) := by
    ext c
    simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
  have hsmul_uImp_dot :
      (lam • uImp_a) ⬝ᵥ b = lam * (uImp_a ⬝ᵥ b) := by
    simp [dotProduct, Finset.mul_sum, mul_assoc]
  have huImp_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp r = 0 := by
    intro r hr_not_implicit hra
    by_cases hrk : r = k
    · subst hrk
      simp [uImp, hui_zero, hua_zero]
    · have hui_r : uImp_i r = 0 := huImp_i_zero r hr_not_implicit hrk
      have hua_r : uImp_a r = 0 := huImp_a_zero r hr_not_implicit hrk
      simp [uImp, hui_r, hua_r]
  have huImp_row :
      uImp ᵥ* A + lam • A a = A i := by
    -- Eliminate the common anchor `k` by solving the `a`-decomposition for `A a`.
    calc
      uImp ᵥ* A + lam • A a
          = (uImp_i ᵥ* A - (lam • uImp_a) ᵥ* A) + lam • A a := by
              rw [huImp_vecMul]
      _ = (uImp_i ᵥ* A - lam • (uImp_a ᵥ* A)) + lam • A a := by
            rw [hsmul_uImp_vecMul]
      _ = uImp_i ᵥ* A + lam • (A a - uImp_a ᵥ* A) := by
            ext c
            simp [sub_eq_add_neg]
            ring
      _ = uImp_i ᵥ* A + lam • (lam_a • A k) := by rw [hrow_a_sub]
      _ = uImp_i ᵥ* A + lam_i • A k := by
            have hlam_mul : lam * lam_a = lam_i := by
              dsimp [lam]
              field_simp [ne_of_gt hlam_a]
            rw [smul_smul, hlam_mul]
      _ = A i := hrow_i
  have huImp_rhs :
      uImp ⬝ᵥ b + lam * b a = b i := by
    -- The scalar right-hand side identity eliminates the same common anchor.
    have huImp_dot :
        uImp ⬝ᵥ b = uImp_i ⬝ᵥ b - (lam • uImp_a) ⬝ᵥ b := by
      unfold dotProduct
      simp [uImp, Pi.sub_apply, Finset.sum_sub_distrib, sub_mul, Finset.mul_sum]
    calc
      uImp ⬝ᵥ b + lam * b a
          = (uImp_i ⬝ᵥ b - (lam • uImp_a) ⬝ᵥ b) + lam * b a := by
              rw [huImp_dot]
      _ = (uImp_i ⬝ᵥ b - lam * (uImp_a ⬝ᵥ b)) + lam * b a := by
            rw [hsmul_uImp_dot]
      _ = uImp_i ⬝ᵥ b + lam * (b a - uImp_a ⬝ᵥ b) := by ring
      _ = uImp_i ⬝ᵥ b + lam * (lam_a * b k) := by rw [hrhs_a_sub]
      _ = uImp_i ⬝ᵥ b + lam_i * b k := by
            have hlam_mul : lam * lam_a = lam_i := by
              dsimp [lam]
              field_simp [ne_of_gt hlam_a]
            rw [← mul_assoc, hlam_mul]
      _ = b i := hrhs_i
  exact ⟨lam, uImp, hlam, huImp_a_eq_zero, huImp_zero, huImp_row, huImp_rhs⟩

/-- Helper for Theorem 3.27: an equality-valid row difference on the whole polyhedron comes from
implicit rows only. -/
lemma implicitMultiplier_of_eq_on_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (δ : ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (heq :
      ∀ {x : Fin n → ℝ}, x ∈ polyhedron_le_set A b → c ⬝ᵥ x = δ) :
    ∃ uImp : Fin m → ℝ,
      (∀ r : Fin m, 0 ≤ uImp r) ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → uImp r = 0) ∧
          uImp ᵥ* A = c ∧
          uImp ⬝ᵥ b = δ := by
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  have hvalid : is_valid_inequality P c δ := by
    intro x hx
    exact le_of_eq (heq hx)
  have hattained : (face_set P c δ).Nonempty := by
    rcases hP_nonempty with ⟨x, hxP⟩
    exact ⟨x, (mem_face_set_iff).2 ⟨hxP, heq hxP⟩⟩
  obtain ⟨uImp, hu_nonneg, hrow, hδ⟩ :=
    exists_nonneg_multiplier_of_attained_valid_inequality A b c δ hvalid hattained
  refine ⟨uImp, hu_nonneg, ?_, hrow, hδ⟩
  intro r hr_not_implicit
  by_cases hr_pos : 0 < uImp r
  · have hr_implicit : is_implicit_equality A b r := by
      intro x hxP
      have hxFace : x ∈ face_set P c δ := (mem_face_set_iff).2 ⟨hxP, heq hxP⟩
      have hxSupport :
          x ∈ active_constraint_face A b {s : Fin m | 0 < uImp s} :=
        (mem_face_set_iff_mem_active_constraint_face_of_support hu_nonneg hrow hδ).1 hxFace
      exact (mem_active_constraint_face_iff.mp hxSupport).1 r hr_pos
    exact False.elim (hr_not_implicit hr_implicit)
  · linarith [hu_nonneg r]

/-- Helper for Theorem 3.27: once an auxiliary singleton-face multiplier already avoids every
ambient nonimplicit row except the prescribed anchor `k`, its castAdd/natAdd coefficients translate
directly into the ambient fixed-anchor row and right-hand-side identities. -/
lemma ambientFixedAnchorData_of_auxMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (uAux : Fin (m + m) → ℝ)
    (huCastZero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uAux (Fin.castAdd m r) = 0)
    (hrowAux :
      uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i)
    (hrhsAux :
      uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i) :
    ∃ lam : ℝ, ∃ uImp : Fin m → ℝ,
      uImp k = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp r = 0) ∧
        uImp ᵥ* A + lam • A k = A i ∧
        uImp ⬝ᵥ b + lam * b k = b i := by
  let uCast : Fin m → ℝ := fun r ↦ uAux (Fin.castAdd m r)
  let uImp : Fin m → ℝ := fun r ↦ if r = k then 0 else uCast r
  let lam : ℝ := uCast k - uAux (Fin.natAdd m k)
  have huImp_at_anchor : uImp k = 0 := by
    simp [uImp]
  have huImp_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp r = 0 := by
    intro r hr_not_implicit hrk
    -- Away from the prescribed anchor, the clean castAdd support is exactly the given ambient
    -- nonimplicit support condition.
    simp [uImp, hrk, uCast, huCastZero r hr_not_implicit hrk]
  have hrowAux_split :
      uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) =
        uCast ᵥ* A - uAux (Fin.natAdd m k) • A k := by
    ext c
    -- Split the auxiliary row identity into the original castAdd block and the single effective
    -- natAdd row indexed by `k`.
    calc
      (uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m))) c
          = ∑ r : Fin m, uAux (Fin.castAdd m r) * A r c +
              ∑ r : Fin m, uAux (Fin.natAdd m r) *
                activeConstraintFaceMatrix A ({k} : Set (Fin m)) (Fin.natAdd m r) c := by
                  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_add,
                    activeConstraintFaceMatrix_castAdd]
      _ = ∑ r : Fin m, uAux (Fin.castAdd m r) * A r c +
            uAux (Fin.natAdd m k) * (-A k c) := by
            congr 1
            rw [Finset.sum_eq_single k]
            · rw [activeConstraintFaceMatrix_natAdd_of_mem A ({k} : Set (Fin m)) k (by simp)]
              simp
            · intro r _ hrk
              have hr_not_mem : r ∉ ({k} : Set (Fin m)) := by
                simpa [Set.mem_singleton_iff] using hrk
              rw [activeConstraintFaceMatrix_natAdd_of_not_mem A ({k} : Set (Fin m)) r hr_not_mem]
              simp
            · simp
      _ = (uCast ᵥ* A - uAux (Fin.natAdd m k) • A k) c := by
            simp [uCast, Matrix.vecMul, dotProduct, sub_eq_add_neg]
  have hrhsAux_split :
      uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) =
        uCast ⬝ᵥ b - uAux (Fin.natAdd m k) * b k := by
    -- The auxiliary right-hand side has the same castAdd/natAdd decomposition.
    calc
      uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m))
          = ∑ r : Fin m, uAux (Fin.castAdd m r) * b r +
              ∑ r : Fin m, uAux (Fin.natAdd m r) *
                activeConstraintFaceRhs b ({k} : Set (Fin m)) (Fin.natAdd m r) := by
                  simp [dotProduct, Fin.sum_univ_add, activeConstraintFaceRhs_castAdd]
      _ = ∑ r : Fin m, uAux (Fin.castAdd m r) * b r +
            uAux (Fin.natAdd m k) * (-b k) := by
            congr 1
            rw [Finset.sum_eq_single k]
            · rw [activeConstraintFaceRhs_natAdd_of_mem b ({k} : Set (Fin m)) k (by simp)]
            · intro r _ hrk
              have hr_not_mem : r ∉ ({k} : Set (Fin m)) := by
                simpa [Set.mem_singleton_iff] using hrk
              rw [activeConstraintFaceRhs_natAdd_of_not_mem b ({k} : Set (Fin m)) r hr_not_mem]
              simp
            · simp
      _ = uCast ⬝ᵥ b - uAux (Fin.natAdd m k) * b k := by
            simp [uCast, dotProduct, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have huCast_split :
      uCast = uImp + uCast k • Pi.single k (1 : ℝ) := by
    funext r
    by_cases hrk : r = k
    · subst hrk
      simp [uImp]
    · simp [uImp, hrk]
  have hsingle_row :
      (uCast k • Pi.single k (1 : ℝ)) ᵥ* A = uCast k • A k := by
    ext c
    rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single k]
    · simp
    · intro r _ hrk
      simp [hrk]
    · simp
  have hcast_row :
      uImp ᵥ* A + uCast k • A k = uCast ᵥ* A := by
    -- Split the original block into its residual tail and the coefficient on row `k`.
    calc
      uImp ᵥ* A + uCast k • A k
          = uImp ᵥ* A + (uCast k • Pi.single k (1 : ℝ)) ᵥ* A := by
              rw [hsingle_row]
      _ = (uImp + uCast k • Pi.single k (1 : ℝ)) ᵥ* A := by
            ext c
            simp [Matrix.vecMul, dotProduct, add_mul, Finset.sum_add_distrib]
      _ = uCast ᵥ* A := by rw [← huCast_split]
  have hsingle_rhs :
      (uCast k • Pi.single k (1 : ℝ)) ⬝ᵥ b = uCast k * b k := by
    rw [dotProduct, Finset.sum_eq_single k]
    · simp
    · intro r _ hrk
      simp [hrk]
    · simp
  have hcast_rhs :
      uImp ⬝ᵥ b + uCast k * b k = uCast ⬝ᵥ b := by
    -- The same coefficient split applies to the scalar right-hand side identity.
    calc
      uImp ⬝ᵥ b + uCast k * b k
          = uImp ⬝ᵥ b + (uCast k • Pi.single k (1 : ℝ)) ⬝ᵥ b := by
              rw [hsingle_rhs]
      _ = (uImp + uCast k • Pi.single k (1 : ℝ)) ⬝ᵥ b := by
            simp [dotProduct, add_mul, Finset.sum_add_distrib]
      _ = uCast ⬝ᵥ b := by rw [← huCast_split]
  have huImp_row :
      uImp ᵥ* A + lam • A k = A i := by
    -- Recombine the residual castAdd tail with the unique effective natAdd contribution at `k`.
    calc
      uImp ᵥ* A + lam • A k
          = uImp ᵥ* A + uCast k • A k - uAux (Fin.natAdd m k) • A k := by
              ext c
              simp [lam]
              ring
      _ = uCast ᵥ* A - uAux (Fin.natAdd m k) • A k := by
            rw [hcast_row]
      _ = uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) := by
            rw [hrowAux_split]
      _ = A i := hrowAux
  have huImp_rhs :
      uImp ⬝ᵥ b + lam * b k = b i := by
    -- The right-hand side identity is the scalar analogue of the row recombination.
    calc
      uImp ⬝ᵥ b + lam * b k
          = uImp ⬝ᵥ b + uCast k * b k - uAux (Fin.natAdd m k) * b k := by
              simp [lam]
              ring
      _ = uCast ⬝ᵥ b - uAux (Fin.natAdd m k) * b k := by
            rw [hcast_rhs]
      _ = uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) := by
            rw [hrhsAux_split]
      _ = b i := hrhsAux
  exact ⟨lam, uImp, huImp_at_anchor, huImp_zero, huImp_row, huImp_rhs⟩

/-- Helper for Theorem 3.27: after translating a prescribed-anchor decomposition back to the
ambient system, evaluating it at a strict feasible point for row `k` forces the anchor coefficient
to be positive. -/
lemma sameFacetRow_fixedAnchorPos_of_strictPoint
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (uImp_i : Fin m → ℝ)
    (lam_i : ℝ)
    (hk : k ∈ remaining_inequality_indices A b)
    (hik_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m)))
    (hui_zero : uImp_i k = 0)
    (huImp_i_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_i r = 0)
    (hrow_i : uImp_i ᵥ* A + lam_i • A k = A i)
    (hrhs_i : uImp_i ⬝ᵥ b + lam_i * b k = b i) :
    0 < lam_i := by
  rcases exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b k hk with
    ⟨xP, hxP, hxP_lt⟩
  have hxP_aff : xP ∈ affineSpan ℝ (polyhedron_le_set A b) :=
    subset_affineSpan ℝ (polyhedron_le_set A b) hxP
  have hsub :
      (A *ᵥ xP) i - b i = lam_i * ((A *ᵥ xP) k - b k) :=
    sameFacetRow_sub_eq_smul_anchorSub_of_implicitEq
      A b i k uImp_i lam_i hk hui_zero huImp_i_zero hrow_i hrhs_i hxP_aff
  have hxi_lt : (A *ᵥ xP) i < b i :=
    sameFacetRow_strict_of_eq_singletonFace A b i k hik_face hxP hxP_lt
  -- The target-row and anchor-row deficits are both negative at the strict feasible point.
  have hk_neg : (A *ᵥ xP) k - b k < 0 := by linarith
  have hi_neg : (A *ᵥ xP) i - b i < 0 := by linarith
  by_contra hlam_not_pos
  have hlam_nonpos : lam_i ≤ 0 := le_of_not_gt hlam_not_pos
  have hmul_nonneg : 0 ≤ lam_i * ((A *ᵥ xP) k - b k) :=
    mul_nonneg_of_nonpos_of_nonpos hlam_nonpos hk_neg.le
  have hi_nonneg : 0 ≤ (A *ᵥ xP) i - b i := by simpa [hsub] using hmul_nonneg
  exact not_lt_of_ge hi_nonneg hi_neg

/-- Helper for Theorem 3.27: count the positive `castAdd` support on ambient nonimplicit rows away
from the prescribed anchor `k` inside the singleton-face auxiliary system. -/
noncomputable def singletonFacetAuxBadSupportCard
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (k : Fin m)
    (uAux : Fin (m + m) → ℝ) : ℕ :=
  Nat.card {r : Fin m // ¬ is_implicit_equality A b r ∧ r ≠ k ∧ 0 < uAux (Fin.castAdd m r)}

/-- Helper for Theorem 3.27: among all auxiliary multiplier certificates for the implicit
singleton-face row `Fin.castAdd m i`, one minimizes the positive `castAdd` support on ambient
nonimplicit rows away from the prescribed anchor `k`. -/
lemma existsSingletonFacetAuxMultiplier_badSupportMinimal
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hiAux :
      is_implicit_equality
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))
        (Fin.castAdd m i))
    (hAux_nonempty :
      (polyhedron_le_set
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))).Nonempty) :
    ∃ uAux : Fin (m + m) → ℝ,
      (∀ r : Fin (m + m), 0 ≤ uAux r) ∧
        (∀ r : Fin (m + m),
          ¬ is_implicit_equality
              (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
              (activeConstraintFaceRhs b ({k} : Set (Fin m))) r →
            uAux r = 0) ∧
          uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i ∧
            uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i ∧
              ∀ uAux' : Fin (m + m) → ℝ,
                (∀ r : Fin (m + m), 0 ≤ uAux' r) →
                  (∀ r : Fin (m + m),
                    ¬ is_implicit_equality
                        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
                        (activeConstraintFaceRhs b ({k} : Set (Fin m))) r →
                      uAux' r = 0) →
                    uAux' ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i →
                      uAux' ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i →
                        singletonFacetAuxBadSupportCard A b k uAux ≤
                          singletonFacetAuxBadSupportCard A b k uAux' := by
  classical
  let A' : Matrix (Fin (m + m)) (Fin n) ℝ := activeConstraintFaceMatrix A ({k} : Set (Fin m))
  let b' : Fin (m + m) → ℝ := activeConstraintFaceRhs b ({k} : Set (Fin m))
  let Q : ℕ → Prop := fun t ↦
    ∃ uAux : Fin (m + m) → ℝ,
      (∀ r : Fin (m + m), 0 ≤ uAux r) ∧
        (∀ r : Fin (m + m), ¬ is_implicit_equality A' b' r → uAux r = 0) ∧
          uAux ᵥ* A' = A i ∧
            uAux ⬝ᵥ b' = b i ∧
              singletonFacetAuxBadSupportCard A b k uAux = t
  have hQ : ∃ t : ℕ, Q t := by
    obtain ⟨uAux, huAux_nonneg, huAux_zero, hrowAux, hrhsAux⟩ :=
      implicitMultiplier_of_eq_on_polyhedron A' b' (A i) (b i) hAux_nonempty (by
        intro x hx
        -- Read the implicit auxiliary row `Fin.castAdd m i` back as the original ambient row `i`.
        have hxi : (A' *ᵥ x) (Fin.castAdd m i) = b' (Fin.castAdd m i) := hiAux hx
        simpa [A', b', Matrix.mulVec, activeConstraintFaceMatrix_castAdd,
          activeConstraintFaceRhs_castAdd] using hxi)
    -- Package one auxiliary certificate so `Nat.find` can minimize the bad `castAdd` support.
    exact
      ⟨singletonFacetAuxBadSupportCard A b k uAux,
        uAux, huAux_nonneg, huAux_zero, hrowAux, hrhsAux, rfl⟩
  rcases Nat.find_spec hQ with ⟨uAux, huAux_nonneg, huAux_zero, hrowAux, hrhsAux, huAux_card⟩
  refine ⟨uAux, huAux_nonneg, huAux_zero, hrowAux, hrhsAux, ?_⟩
  intro uAux' huAux'_nonneg huAux'_zero hrowAux' hrhsAux'
  have hmin :
      Nat.find hQ ≤ singletonFacetAuxBadSupportCard A b k uAux' := by
    -- Any competing auxiliary certificate contributes another admissible bad-support cardinality.
    exact Nat.find_min' hQ ⟨uAux', huAux'_nonneg, huAux'_zero, hrowAux', hrhsAux', rfl⟩
  -- Rewrite the chosen minimal cardinality back to the concrete certificate `uAux`.
  simpa [huAux_card] using hmin

/-- Helper for Theorem 3.27: if an original auxiliary row is implicit in the singleton-face
auxiliary system and the original row is still remaining, then it defines the same singleton face.
-/
lemma eqSingletonFace_of_singletonFacetAuxOriginalRowImplicit
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hiAux :
      is_implicit_equality
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))
        (Fin.castAdd m i)) :
    active_constraint_face A b ({i} : Set (Fin m)) =
      active_constraint_face A b ({k} : Set (Fin m)) := by
  have hsubset :
      active_constraint_face A b ({k} : Set (Fin m)) ⊆
        active_constraint_face A b ({i} : Set (Fin m)) := by
    intro y hy
    have hyAux :
        y ∈ polyhedron_le_set
          (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
          (activeConstraintFaceRhs b ({k} : Set (Fin m))) := by
      -- Switch to the auxiliary presentation of the singleton face before reading off row `i`.
      simpa [active_constraint_face_eq_polyhedronAux] using hy
    have hyRow :
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)) *ᵥ y) (Fin.castAdd m i) =
          activeConstraintFaceRhs b ({k} : Set (Fin m)) (Fin.castAdd m i) :=
      hiAux hyAux
    have hyi : (A *ᵥ y) i = b i := by
      rw [Matrix.mulVec, activeConstraintFaceMatrix_castAdd, activeConstraintFaceRhs_castAdd] at hyRow
      simpa [Matrix.mulVec] using hyRow
    -- The auxiliary implicit equality upgrades every point of the singleton face to row-`i`
    -- tightness in the ambient system.
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro r hr
      have hri : r = i := by simpa using hr
      simpa [hri] using hyi
    · intro r hr
      exact mem_polyhedron_of_mem_active_constraint_face hy r
  -- Facet maximality turns containment into equality once row `i` is known to remain nonimplicit.
  exact singletonActiveConstraintFace_eq_of_subset_of_isFacet A b i k hi hfacet hsubset

/-- Helper for Theorem 3.27: a positive `castAdd` coefficient on an ambient nonimplicit row in
the singleton-face auxiliary system forces that row to define the same singleton facet as `k`. -/
lemma eqSingletonFace_of_positiveSingletonFacetAuxCoeff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (k : Fin m)
    (hfacet_k :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (uAux : Fin (m + m) → ℝ)
    (huAux_zero :
      ∀ r : Fin (m + m),
        ¬ is_implicit_equality
            (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
            (activeConstraintFaceRhs b ({k} : Set (Fin m))) r →
          uAux r = 0)
    (r : Fin m)
    (hr_not_implicit : ¬ is_implicit_equality A b r)
    (hur_pos : 0 < uAux (Fin.castAdd m r)) :
    active_constraint_face A b ({r} : Set (Fin m)) =
      active_constraint_face A b ({k} : Set (Fin m)) := by
  have hr_remaining : r ∈ remaining_inequality_indices A b :=
    (mem_remaining_inequality_indices_iff A b r).2 hr_not_implicit
  have hrAux_implicit :
      is_implicit_equality
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))
        (Fin.castAdd m r) := by
    -- A positive auxiliary coefficient cannot sit on a non-implicit auxiliary row.
    by_contra hrAux_not_implicit
    have hur_zero : uAux (Fin.castAdd m r) = 0 :=
      huAux_zero (Fin.castAdd m r) hrAux_not_implicit
    exact (ne_of_gt hur_pos) hur_zero
  -- Read the auxiliary implicit original row back as singleton-face equality in the ambient
  -- system.
  exact
    eqSingletonFace_of_singletonFacetAuxOriginalRowImplicit
      A b r k hr_remaining hfacet_k hrAux_implicit

/-- Helper for Theorem 3.27: an ambient implicit row stays implicit after passing to the
singleton-face auxiliary system of `{k}`. -/
lemma singletonFacetAuxOriginalRowImplicit_of_implicitEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hi : is_implicit_equality A b i) :
    is_implicit_equality
      (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
      (activeConstraintFaceRhs b ({k} : Set (Fin m)))
      (Fin.castAdd m i) := by
  intro y hy
  have hyFace :
      y ∈ active_constraint_face A b ({k} : Set (Fin m)) := by
    -- Reinterpret the auxiliary feasible point as a point of the singleton face.
    simpa [active_constraint_face_eq_polyhedronAux] using hy
  have hyP : y ∈ polyhedron_le_set A b :=
    mem_polyhedron_of_mem_active_constraint_face hyFace
  have hyRow : (A *ᵥ y) i = b i := hi hyP
  -- The original block of the auxiliary system is exactly the ambient row system.
  rw [Matrix.mulVec, activeConstraintFaceMatrix_castAdd, activeConstraintFaceRhs_castAdd]
  simpa [Matrix.mulVec] using hyRow

/-- Helper for Theorem 3.27: if two singleton active faces agree, then the original row from one
face becomes an implicit equality in the auxiliary singleton-face system of the other row. -/
lemma singletonFacetAuxOriginalRowImplicit_of_eqSingletonFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hik_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m))) :
    is_implicit_equality
      (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
      (activeConstraintFaceRhs b ({k} : Set (Fin m)))
      (Fin.castAdd m i) := by
  intro y hy
  have hyFace :
      y ∈ active_constraint_face A b ({k} : Set (Fin m)) := by
    -- Reinterpret the auxiliary feasible point as a point of the singleton face.
    simpa [active_constraint_face_eq_polyhedronAux] using hy
  have hyRow : (A *ᵥ y) i = b i :=
    sameFacetRow_eq_at_singletonFacePoint A b i k hik_face hyFace
  -- The original block of the auxiliary system is exactly the original row system.
  rw [Matrix.mulVec, activeConstraintFaceMatrix_castAdd, activeConstraintFaceRhs_castAdd]
  simpa [Matrix.mulVec] using hyRow

/-- Helper for Theorem 3.27: equality of singleton active faces transports the facet property to
the other row. -/
lemma isFacet_singleton_of_eq_singletonFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m)))
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m)))) :
    is_facet (polyhedron_le_set A b)
      (active_constraint_face A b ({i} : Set (Fin m))) := by
  -- Rewriting along the singleton-face equality identifies the two facet statements.
  simpa [hij_face] using hfacet

/-- Helper for Theorem 3.27: a row cutting out the same singleton face as a facet row cannot be an
implicit equality, so it remains among the non-implicit inequalities. -/
lemma remaining_row_of_eq_singletonFacet_of_isFacet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i a : Fin m)
    (hfacet_a :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({a} : Set (Fin m))))
    (hia_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({a} : Set (Fin m))) :
    i ∈ remaining_inequality_indices A b := by
  have hi_not_implicit : ¬ is_implicit_equality A b i := by
    intro hi_implicit
    have hface_i_eq :
        active_constraint_face A b ({i} : Set (Fin m)) = polyhedron_le_set A b :=
      activeConstraintFace_eq_polyhedron_of_forall_implicit
        A b ({i} : Set (Fin m)) (by
          intro r hr
          have hri : r = i := by simpa using hr
          simpa [hri] using hi_implicit)
    have hproper_a :
        is_proper_face (polyhedron_le_set A b)
          (active_constraint_face A b ({a} : Set (Fin m))) :=
      is_facet_to_is_proper_face hfacet_a
    exact (is_proper_face_iff.mp hproper_a).2.2.ne (by
      calc
        active_constraint_face A b ({a} : Set (Fin m))
            = active_constraint_face A b ({i} : Set (Fin m)) := hia_face.symm
        _ = polyhedron_le_set A b := hface_i_eq)
  -- Membership in `remaining_inequality_indices` is exactly non-implicitness.
  exact (mem_remaining_inequality_indices_iff A b i).2 hi_not_implicit

/-- Helper for Theorem 3.27: once a clean auxiliary certificate for row `r` is available, replacing
the bad coefficient at `Fin.castAdd m r` strictly lowers `singletonFacetAuxBadSupportCard`. -/
lemma singletonFacetAuxBadSupportCard_strictDecrease_of_cleanReplacement
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k r : Fin m)
    (uAux vAux : Fin (m + m) → ℝ)
    (huAux_nonneg : ∀ p : Fin (m + m), 0 ≤ uAux p)
    (huAux_zero :
      ∀ p : Fin (m + m),
        ¬ is_implicit_equality
            (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
            (activeConstraintFaceRhs b ({k} : Set (Fin m))) p →
          uAux p = 0)
    (hrowAux :
      uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i)
    (hrhsAux :
      uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i)
    (hr_not_implicit : ¬ is_implicit_equality A b r)
    (hrk : r ≠ k)
    (hur_pos : 0 < uAux (Fin.castAdd m r))
    (hvAux_nonneg : ∀ p : Fin (m + m), 0 ≤ vAux p)
    (hvAux_zero :
      ∀ p : Fin (m + m),
        ¬ is_implicit_equality
            (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
            (activeConstraintFaceRhs b ({k} : Set (Fin m))) p →
          vAux p = 0)
    (hvAux_castZero :
      ∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → vAux (Fin.castAdd m s) = 0)
    (hrowV :
      vAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A r)
    (hrhsV :
      vAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b r) :
    ∃ uAux' : Fin (m + m) → ℝ,
      (∀ p : Fin (m + m), 0 ≤ uAux' p) ∧
        (∀ p : Fin (m + m),
          ¬ is_implicit_equality
              (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
              (activeConstraintFaceRhs b ({k} : Set (Fin m))) p →
            uAux' p = 0) ∧
          uAux' ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i ∧
            uAux' ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i ∧
              singletonFacetAuxBadSupportCard A b k uAux' <
                singletonFacetAuxBadSupportCard A b k uAux := by
  let idx : Fin (m + m) := Fin.castAdd m r
  let coeff : ℝ := uAux idx
  let uDrop : Fin (m + m) → ℝ := fun p ↦ if p = idx then 0 else uAux p
  let uAux' : Fin (m + m) → ℝ := fun p ↦ uDrop p + coeff * vAux p
  have hcoeff_nonneg : 0 ≤ coeff := huAux_nonneg idx
  have hvAux_r_zero : vAux idx = 0 := by
    simpa [idx] using hvAux_castZero r hr_not_implicit hrk
  have huDrop_nonneg : ∀ p : Fin (m + m), 0 ≤ uDrop p := by
    intro p
    by_cases hp : p = idx
    · simp [uDrop, hp]
    · simp [uDrop, hp, huAux_nonneg p]
  have huAux'_nonneg : ∀ p : Fin (m + m), 0 ≤ uAux' p := by
    intro p
    by_cases hp : p = idx
    · subst hp
      -- The bad coefficient at `Fin.castAdd m r` is removed exactly because `vAux` vanishes there.
      simp [uAux', uDrop, coeff, hvAux_r_zero]
    · -- Away from `Fin.castAdd m r`, the replacement only adds a nonnegative multiple of `vAux`.
      exact add_nonneg (huDrop_nonneg p) (mul_nonneg hcoeff_nonneg (hvAux_nonneg p))
  have huAux'_zero :
      ∀ p : Fin (m + m),
        ¬ is_implicit_equality
            (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
            (activeConstraintFaceRhs b ({k} : Set (Fin m))) p →
          uAux' p = 0 := by
    intro p hp_not_implicit
    have huDrop_zero : uDrop p = 0 := by
      by_cases hp : p = idx
      · simp [uDrop, hp]
      · simp [uDrop, hp, huAux_zero p hp_not_implicit]
    have hv_zero : vAux p = 0 := hvAux_zero p hp_not_implicit
    simp [uAux', huDrop_zero, hv_zero]
  have hsingle_row :
      (coeff • Pi.single idx (1 : ℝ)) ᵥ*
          activeConstraintFaceMatrix A ({k} : Set (Fin m)) =
        coeff • A r := by
    ext c
    -- The singleton vector on `idx = Fin.castAdd m r` reproduces row `r`.
    rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single idx]
    · simp [idx, coeff, activeConstraintFaceMatrix_castAdd]
    · intro p _ hp
      simp [Pi.single_apply, hp]
    · simp
  have hsingle_rhs :
      (coeff • Pi.single idx (1 : ℝ)) ⬝ᵥ
          activeConstraintFaceRhs b ({k} : Set (Fin m)) =
        coeff * b r := by
    -- The same singleton vector reads off the right-hand side entry `b r`.
    rw [dotProduct, Finset.sum_eq_single idx]
    · simp [idx, coeff, activeConstraintFaceRhs_castAdd]
    · intro p _ hp
      simp [Pi.single_apply, hp]
    · simp
  have huDrop_split :
      uAux = uDrop + coeff • Pi.single idx (1 : ℝ) := by
    funext p
    by_cases hp : p = idx
    · subst hp
      simp [uDrop, coeff]
    · simp [uDrop, hp, coeff]
  have huDrop_row :
      uDrop ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) + coeff • A r =
        uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) := by
    -- Splitting off the `idx` coefficient isolates the row `A r` to be replaced.
    calc
      uDrop ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) + coeff • A r
          = uDrop ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) +
              (coeff • Pi.single idx (1 : ℝ)) ᵥ*
                activeConstraintFaceMatrix A ({k} : Set (Fin m)) := by
                  rw [hsingle_row]
      _ = (uDrop + coeff • Pi.single idx (1 : ℝ)) ᵥ*
            activeConstraintFaceMatrix A ({k} : Set (Fin m)) := by
              ext c
              simp [Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul]
      _ = uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) := by
            rw [huDrop_split]
  have huDrop_rhs :
      uDrop ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) + coeff * b r =
        uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) := by
    -- The right-hand side identity splits off the same `idx` coefficient.
    calc
      uDrop ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) + coeff * b r
          = uDrop ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) +
              (coeff • Pi.single idx (1 : ℝ)) ⬝ᵥ
                activeConstraintFaceRhs b ({k} : Set (Fin m)) := by
                  rw [hsingle_rhs]
      _ = (uDrop + coeff • Pi.single idx (1 : ℝ)) ⬝ᵥ
            activeConstraintFaceRhs b ({k} : Set (Fin m)) := by
              simp [dotProduct, Finset.sum_add_distrib, add_mul]
      _ = uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) := by
            rw [huDrop_split]
  have huAux'_row :
      uAux' ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i := by
    -- Replacing the extracted `A r` contribution by the clean certificate preserves the row data.
    calc
      uAux' ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m))
          = uDrop ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) +
              (coeff • vAux) ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) := by
                ext c
                simp [uAux', uDrop, Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul]
      _ = uDrop ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) +
            coeff • (vAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m))) := by
              ext c
              simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
      _ = uDrop ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) + coeff • A r := by
            rw [hrowV]
      _ = uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) := huDrop_row
      _ = A i := hrowAux
  have huAux'_rhs :
      uAux' ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i := by
    -- The right-hand side is preserved by the same replacement calculation.
    calc
      uAux' ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m))
          = uDrop ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) +
              (coeff • vAux) ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) := by
                simp [uAux', dotProduct, Finset.sum_add_distrib, add_mul]
      _ = uDrop ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) +
            coeff * (vAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m))) := by
              simp [dotProduct, Finset.mul_sum, mul_assoc]
      _ = uDrop ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) + coeff * b r := by
            rw [hrhsV]
      _ = uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) := huDrop_rhs
      _ = b i := hrhsAux
  have huAux'_r_zero : uAux' idx = 0 := by
    -- The replacement removes the original bad coefficient and `vAux` does not reintroduce it.
    simp [uAux', uDrop, coeff, hvAux_r_zero]
  let badSupport' : Set (Fin m) :=
    {s : Fin m | ¬ is_implicit_equality A b s ∧ s ≠ k ∧ 0 < uAux' (Fin.castAdd m s)}
  let badSupport : Set (Fin m) :=
    {s : Fin m | ¬ is_implicit_equality A b s ∧ s ≠ k ∧ 0 < uAux (Fin.castAdd m s)}
  have hsubset : badSupport' ⊆ badSupport := by
    intro s hs
    rcases hs with ⟨hs_not_implicit, hsk, hs_pos⟩
    have hsr : s ≠ r := by
      intro hsr
      subst hsr
      have hs_zero : uAux' (Fin.castAdd m s) = 0 := by
        simpa [idx] using huAux'_r_zero
      exact (ne_of_gt hs_pos) hs_zero
    have hcast_eq :
        uAux' (Fin.castAdd m s) = uAux (Fin.castAdd m s) := by
      have hidx_ne : Fin.castAdd m s ≠ idx := by
        intro hEq
        exact hsr (by simpa [idx] using hEq)
      have hv_zero : vAux (Fin.castAdd m s) = 0 :=
        hvAux_castZero s hs_not_implicit hsk
      simp [uAux', uDrop, coeff, hidx_ne, hv_zero]
    exact ⟨hs_not_implicit, hsk, by rwa [← hcast_eq]⟩
  have hr_mem : r ∈ badSupport := by
    exact ⟨hr_not_implicit, hrk, hur_pos⟩
  have hr_not_mem : r ∉ badSupport' := by
    intro hr_mem'
    have hr_pos' : 0 < uAux' (Fin.castAdd m r) := hr_mem'.2.2
    have hs_zero : uAux' (Fin.castAdd m r) = 0 := by
      simpa [idx] using huAux'_r_zero
    rw [hs_zero] at hr_pos'
    exact lt_irrefl 0 hr_pos'
  have hssub : badSupport' ⊂ badSupport := by
    refine Set.ssubset_iff_subset_ne.mpr ?_
    refine ⟨hsubset, ?_⟩
    intro hEq
    have hr_mem' : r ∈ badSupport' := by simpa [hEq] using hr_mem
    exact hr_not_mem hr_mem'
  have hcard_lt :
      singletonFacetAuxBadSupportCard A b k uAux' <
        singletonFacetAuxBadSupportCard A b k uAux := by
    -- Strict containment of the bad-support sets forces a strict drop in their finite cardinals.
    simpa [singletonFacetAuxBadSupportCard, badSupport', badSupport, Nat.card_eq_fintype_card] using
      Set.card_lt_card hssub
  exact ⟨uAux', huAux'_nonneg, huAux'_zero, huAux'_row, huAux'_rhs, hcard_lt⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap03/section_3_9/ch3_sec3_9_theorem_3_27.lean:
retain the rows in `S` and replace every other inequality by the tautology `0 ≤ 0`. -/
def maskedInequalityMatrix
    (A : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin m)) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j ↦ if i ∈ S then A i j else 0

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap03/section_3_9/ch3_sec3_9_theorem_3_27.lean:
the right-hand side accompanying `maskedInequalityMatrix`. -/
def maskedInequalityRhs
    (b : Fin m → ℝ)
    (S : Finset (Fin m)) : Fin m → ℝ :=
  fun i ↦ if i ∈ S then b i else 0

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap03/section_3_9/ch3_sec3_9_theorem_3_27.lean:
every finite inequality system has an equivalent masked presentation in which every non-implicit
row is irredundant. -/
lemma exists_equivalent_row_irredundant_representation
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    ∃ A' : Matrix (Fin m) (Fin n) ℝ, ∃ b' : Fin m → ℝ,
      polyhedron_le_set A' b' = polyhedron_le_set A b ∧
        ∀ i : Fin m, ¬ is_implicit_equality A' b' i → is_irredundant_row A' b' i := by
  classical
  let presentations : Set (Finset (Fin m)) :=
    {S | polyhedron_le_set (maskedInequalityMatrix A S) (maskedInequalityRhs b S) =
      polyhedron_le_set A b}
  have huniv : Finset.univ ∈ presentations := by
    dsimp [presentations]
    -- Keeping every row leaves the original system unchanged.
    have hmatrix : maskedInequalityMatrix A Finset.univ = A := by
      ext i j
      simp [maskedInequalityMatrix]
    have hrhs : maskedInequalityRhs b Finset.univ = b := by
      funext i
      simp [maskedInequalityRhs]
    rw [hmatrix, hrhs]
  obtain ⟨S, _hS_sub, hS_minimal⟩ :=
    Set.Finite.exists_le_minimal (Set.toFinite presentations) huniv
  have hS_system :
      polyhedron_le_set (maskedInequalityMatrix A S) (maskedInequalityRhs b S) =
        polyhedron_le_set A b := by
    exact hS_minimal.prop
  refine
    ⟨maskedInequalityMatrix A S, maskedInequalityRhs b S, hS_system, ?_⟩
  intro i hi_not_implicit
  have hiS : i ∈ S := by
    by_contra hiS
    apply hi_not_implicit
    intro x hx
    -- A masked row is the tautological equality `0 = 0`, hence is implicit.
    simp [maskedInequalityMatrix, maskedInequalityRhs, Matrix.mulVec, hiS]
  let T : Finset (Fin m) := S.erase i
  have hT_ssubset : T ⊂ S := by
    simpa [T] using Finset.erase_ssubset hiS
  have hT_not_presentation : T ∉ presentations :=
    hS_minimal.not_prop_of_lt hT_ssubset
  have hT_ne :
      polyhedron_le_set (maskedInequalityMatrix A T) (maskedInequalityRhs b T) ≠
        polyhedron_le_set (maskedInequalityMatrix A S) (maskedInequalityRhs b S) := by
    intro hEq
    apply hT_not_presentation
    dsimp [presentations]
    exact hEq.trans hS_system
  have hS_subset_T :
      polyhedron_le_set (maskedInequalityMatrix A S) (maskedInequalityRhs b S) ⊆
        polyhedron_le_set (maskedInequalityMatrix A T) (maskedInequalityRhs b T) := by
    intro x hx q
    by_cases hqT : q ∈ T
    · have hqS : q ∈ S := Finset.mem_of_mem_erase hqT
      simpa [maskedInequalityMatrix, maskedInequalityRhs, Matrix.mulVec, hqT, hqS] using hx q
    · simp [maskedInequalityMatrix, maskedInequalityRhs, Matrix.mulVec, hqT]
  have hT_not_subset_S :
      ¬ polyhedron_le_set (maskedInequalityMatrix A T) (maskedInequalityRhs b T) ⊆
        polyhedron_le_set (maskedInequalityMatrix A S) (maskedInequalityRhs b S) := by
    intro hT_subset_S
    exact hT_ne (Set.Subset.antisymm hT_subset_S hS_subset_T)
  rcases Set.not_subset.mp hT_not_subset_S with ⟨x, hxT, hx_not_S⟩
  have hx_other :
      ∀ q : Fin m, q ≠ i →
        (maskedInequalityMatrix A S *ᵥ x) q ≤ maskedInequalityRhs b S q := by
    intro q hqi
    by_cases hqS : q ∈ S
    · have hqT : q ∈ T := by
        simp [T, hqS, hqi]
      simpa [maskedInequalityMatrix, maskedInequalityRhs, Matrix.mulVec, hqT, hqS] using hxT q
    · simp [maskedInequalityMatrix, maskedInequalityRhs, Matrix.mulVec, hqS]
  have hi_not_le :
      ¬ (maskedInequalityMatrix A S *ᵥ x) i ≤ maskedInequalityRhs b S i := by
    intro hi_le
    apply hx_not_S
    intro q
    by_cases hqi : q = i
    · simpa [hqi] using hi_le
    · exact hx_other q hqi
  -- Removing the retained row produces a point satisfying every other row and violating this one.
  exact ⟨x, hx_other, lt_of_not_ge hi_not_le⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap03/section_3_9/ch3_sec3_9_theorem_3_27.lean:
every facet of a nonempty finite inequality polyhedron has codimension one in its ambient affine
span. -/
lemma finrank_direction_affineSpan_add_one_eq_of_isFacet_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (F : Set (Fin n → ℝ))
    (hF_facet : is_facet (polyhedron_le_set A b) F) :
    Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
      Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
  rcases exists_equivalent_row_irredundant_representation A b with
    ⟨A', b', hsystem, hminimal⟩
  have hP'_nonempty : (polyhedron_le_set A' b').Nonempty := by
    rw [hsystem]
    exact hP_nonempty
  have hF_facet' : is_facet (polyhedron_le_set A' b') F := by
    simpa [hsystem] using hF_facet
  obtain ⟨j, hjF⟩ :=
    exists_eq_active_constraint_face_singleton_of_is_facet
      A' b' hP'_nonempty F hF_facet'
  have hj_not_implicit : ¬ is_implicit_equality A' b' j.1 :=
    (mem_remaining_inequality_indices_iff A' b' j.1).1 j.2
  have hj_irredundant : is_irredundant_row A' b' j.1 :=
    hminimal j.1 hj_not_implicit
  have hcodim :=
    finrank_direction_affineSpan_add_one_eq_of_irredundant_singleton
      A' b' j.1 j.2 hj_irredundant
  -- The minimal presentation defines the same ambient polyhedron, and its selected row defines
  -- the original facet.
  rw [← hjF] at hcodim
  rw [← hsystem]
  exact hcodim

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap03/section_3_9/ch3_sec3_9_theorem_3_27.lean:
a codimension-one submodule contained in the kernel cut of a nonzero functional is that kernel
cut. -/
lemma eq_inf_ker_of_finrank_add_one_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F D : Submodule ℝ E)
    (L : E →ₗ[ℝ] ℝ)
    (hFD : F ≤ D)
    (hFker : F ≤ LinearMap.ker L)
    (hcodim : Module.finrank ℝ F + 1 = Module.finrank ℝ D)
    {w : E}
    (hwD : w ∈ D)
    (hw_ne : L w ≠ 0) :
    F = D ⊓ LinearMap.ker L := by
  let wOne : E := (L w)⁻¹ • w
  have hwOneD : wOne ∈ D := by
    exact D.smul_mem (L w)⁻¹ hwD
  have hwOne_eval : L wOne = 1 := by
    dsimp [wOne]
    simp [hw_ne]
  have hinter_codim :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D :=
    finrank_inf_ker_add_one_of_eval_one D L hwOneD hwOne_eval
  have hfinrank :
      Module.finrank ℝ F = Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) := by
    omega
  -- Both the ambient-direction and kernel conditions hold on every direction of `F`.
  exact Submodule.eq_of_le_of_finrank_eq (fun v hv ↦ ⟨hFD hv, hFker hv⟩) hfinrank

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap03/section_3_9/ch3_sec3_9_theorem_3_27.lean`: two real linear
functionals with the same kernel cut on a submodule and the same strict sign are positive scalar
multiples on that submodule. -/
lemma exists_pos_smul_on_submodule_of_inf_ker_eq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (D : Submodule ℝ E)
    (f g : E →ₗ[ℝ] ℝ)
    {w : E}
    (hwD : w ∈ D)
    (hfw : f w < 0)
    (hgw : g w < 0)
    (hker : D ⊓ LinearMap.ker f = D ⊓ LinearMap.ker g) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ {x : E}, x ∈ D → f x = lam * g x := by
  let lam : ℝ := f w / g w
  have hgw_ne : g w ≠ 0 := ne_of_lt hgw
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    exact div_pos_of_neg_of_neg hfw hgw
  refine ⟨lam, hlam_pos, ?_⟩
  intro x hxD
  let z : E := x - (g x / g w) • w
  have hzD : z ∈ D := by
    dsimp [z]
    exact D.sub_mem hxD (D.smul_mem _ hwD)
  have hzg : g z = 0 := by
    dsimp [z]
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  have hz_common : z ∈ D ⊓ LinearMap.ker g := ⟨hzD, hzg⟩
  have hzf : f z = 0 := by
    have hz_common' : z ∈ D ⊓ LinearMap.ker f := by
      rw [hker]
      exact hz_common
    exact hz_common'.2
  have hrelation : f x - (g x / g w) * f w = 0 := by
    simpa only [z, map_sub, map_smul, smul_eq_mul] using hzf
  -- Solving the one-dimensional quotient relation gives the common positive scale.
  calc
    f x = (g x / g w) * f w := by linarith
    _ = lam * g x := by
      dsimp [lam]
      field_simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap03/section_3_9/ch3_sec3_9_theorem_3_27.lean`: rows defining the same
singleton facet have positively proportional affine deficits on the ambient affine span. -/
lemma sameFacetRows_sub_eq_pos_smul_on_affineHull_of_isFacet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r k : Fin m)
    (hfacet_k :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hrk_face :
      active_constraint_face A b ({r} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m))) :
    ∃ lam : ℝ,
      0 < lam ∧
        ∀ {x : Fin n → ℝ},
          x ∈ affineSpan ℝ (polyhedron_le_set A b) →
            (A *ᵥ x) r - b r = lam * ((A *ᵥ x) k - b k) := by
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  let F : Set (Fin n → ℝ) :=
    active_constraint_face A b ({k} : Set (Fin m))
  let D : Submodule ℝ (Fin n → ℝ) := (affineSpan ℝ P).direction
  let Fr : Submodule ℝ (Fin n → ℝ) := (affineSpan ℝ F).direction
  let Lr : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductStrongDual (A r)).toLinearMap
  let Lk : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductStrongDual (A k)).toLinearMap
  rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet_k)).2.1 with
    ⟨xhat, hxhat_face⟩
  have hxhatP : xhat ∈ P := by
    simpa [F, P] using mem_polyhedron_of_mem_active_constraint_face hxhat_face
  have hxhatFAff : xhat ∈ affineSpan ℝ F := subset_affineSpan ℝ F hxhat_face
  have hxhatPAff : xhat ∈ affineSpan ℝ P := subset_affineSpan ℝ P hxhatP
  have hxhat_r : (A *ᵥ xhat) r = b r := by
    exact sameFacetRow_eq_on_affineSpan_singletonFacet A b r k hrk_face hxhatFAff
  have hxhat_k : (A *ᵥ xhat) k = b k := by
    exact sameFacetRow_eq_on_affineSpan_singletonFacet A b k k rfl hxhatFAff
  have hF_subset_P : F ⊆ P := by
    intro x hx
    simpa [F, P] using mem_polyhedron_of_mem_active_constraint_face hx
  have hFrD : Fr ≤ D := by
    simpa [Fr, D] using
      AffineSubspace.direction_le (affineSpan_mono ℝ hF_subset_P)
  have hFr_ker_r : Fr ≤ LinearMap.ker Lr := by
    intro v hv
    change Lr v = 0
    have hv' : v ∈ (affineSpan ℝ F).direction := by simpa [Fr] using hv
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhatFAff] at hv'
    rcases hv' with ⟨x, hxAff, rfl⟩
    have hx_r : (A *ᵥ x) r = b r :=
      sameFacetRow_eq_on_affineSpan_singletonFacet A b r k hrk_face hxAff
    calc
      Lr (x - xhat) = (A *ᵥ (x - xhat)) r := by
        simp [Lr, dotProductStrongDual_apply, Matrix.mulVec]
      _ = (A *ᵥ x) r - (A *ᵥ xhat) r := by simp [Matrix.mulVec_sub]
      _ = 0 := by rw [hx_r, hxhat_r, sub_self]
  have hFr_ker_k : Fr ≤ LinearMap.ker Lk := by
    intro v hv
    change Lk v = 0
    have hv' : v ∈ (affineSpan ℝ F).direction := by simpa [Fr] using hv
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhatFAff] at hv'
    rcases hv' with ⟨x, hxAff, rfl⟩
    have hx_k : (A *ᵥ x) k = b k :=
      sameFacetRow_eq_on_affineSpan_singletonFacet A b k k rfl hxAff
    calc
      Lk (x - xhat) = (A *ᵥ (x - xhat)) k := by
        simp [Lk, dotProductStrongDual_apply, Matrix.mulVec]
      _ = (A *ᵥ x) k - (A *ᵥ xhat) k := by simp [Matrix.mulVec_sub]
      _ = 0 := by rw [hx_k, hxhat_k, sub_self]
  have hk_not_implicit : ¬ is_implicit_equality A b k := by
    intro hk_implicit
    have hsingleton_implicit :
        ∀ i : Fin m, i ∈ ({k} : Set (Fin m)) → is_implicit_equality A b i := by
      intro i hi
      have hik : i = k := by simpa using hi
      simpa [hik] using hk_implicit
    have hface_eq :
        active_constraint_face A b ({k} : Set (Fin m)) = polyhedron_le_set A b :=
      activeConstraintFace_eq_polyhedron_of_forall_implicit A b ({k} : Set (Fin m))
        hsingleton_implicit
    exact (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet_k)).2.2.ne hface_eq
  have hk : k ∈ remaining_inequality_indices A b :=
    (mem_remaining_inequality_indices_iff A b k).2 hk_not_implicit
  rcases exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b k hk with
    ⟨xP, hxP, hxP_k_lt⟩
  have hxP_r_lt : (A *ᵥ xP) r < b r :=
    sameFacetRow_strict_of_eq_singletonFace A b r k hrk_face hxP hxP_k_lt
  have hxPAff : xP ∈ affineSpan ℝ P := by
    exact subset_affineSpan ℝ P hxP
  let w : Fin n → ℝ := xP - xhat
  have hwD : w ∈ D := by
    have hw : xP - xhat ∈ (affineSpan ℝ P).direction := by
      simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxPAff hxhatPAff
    simpa [w, D] using hw
  have hLr_w_neg : Lr w < 0 := by
    have heval : Lr w = (A *ᵥ xP) r - (A *ᵥ xhat) r := by
      dsimp [w]
      simp [Lr, dotProductStrongDual_apply, Matrix.mulVec]
    rw [heval, hxhat_r]
    linarith
  have hLk_w_neg : Lk w < 0 := by
    have heval : Lk w = (A *ᵥ xP) k - (A *ᵥ xhat) k := by
      dsimp [w]
      simp [Lk, dotProductStrongDual_apply, Matrix.mulVec]
    rw [heval, hxhat_k]
    linarith
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨xP, hxP⟩
  have hcodim : Module.finrank ℝ Fr + 1 = Module.finrank ℝ D := by
    simpa [F, P, Fr, D] using
      finrank_direction_affineSpan_add_one_eq_of_isFacet_polyhedron
        A b hP_nonempty F hfacet_k
  have hker_r : Fr = D ⊓ LinearMap.ker Lr :=
    eq_inf_ker_of_finrank_add_one_eq
      Fr D Lr hFrD hFr_ker_r hcodim hwD (ne_of_lt hLr_w_neg)
  have hker_k : Fr = D ⊓ LinearMap.ker Lk :=
    eq_inf_ker_of_finrank_add_one_eq
      Fr D Lk hFrD hFr_ker_k hcodim hwD (ne_of_lt hLk_w_neg)
  have hcommon_kernel : D ⊓ LinearMap.ker Lr = D ⊓ LinearMap.ker Lk :=
    hker_r.symm.trans hker_k
  obtain ⟨lam, hlam_pos, hproportional⟩ :=
    exists_pos_smul_on_submodule_of_inf_ker_eq
      D Lr Lk hwD hLr_w_neg hLk_w_neg hcommon_kernel
  refine ⟨lam, hlam_pos, ?_⟩
  intro x hxAff
  have hdiffD : x - xhat ∈ D := by
    have hdiff : x - xhat ∈ (affineSpan ℝ P).direction := by
      simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxAff hxhatPAff
    simpa [D] using hdiff
  have hlinear := hproportional hdiffD
  have hlinear' :
      (A *ᵥ x) r - (A *ᵥ xhat) r =
        lam * ((A *ᵥ x) k - (A *ᵥ xhat) k) := by
    simpa [Lr, Lk, dotProductStrongDual_apply, Matrix.mulVec_sub, Matrix.mulVec] using hlinear
  -- Translating the proportional direction evaluations through the facet point gives deficits.
  rwa [hxhat_r, hxhat_k] at hlinear'

/-- Helper for Theorem 3.27: the geometric blocker is to rewrite row `r` as one positive copy of
the prescribed facet row `k` plus a nonnegative implicit-row remainder. -/
lemma fixedAnchor_difference_eq_on_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r k : Fin m)
    (lam : ℝ)
    (uRaw : Fin m → ℝ)
    (huRaw_k_zero : uRaw k = 0)
    (huRaw_zero :
      ∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → uRaw s = 0)
    (hrow : uRaw ᵥ* A + lam • A k = A r)
    (hrhs : uRaw ⬝ᵥ b + lam * b k = b r) :
    ∀ {x : Fin n → ℝ},
      x ∈ polyhedron_le_set A b →
        (A r - lam • A k) ⬝ᵥ x = b r - lam * b k := by
  intro x hxP
  have huRaw_eval :
      uRaw ⬝ᵥ (A *ᵥ x) = uRaw ⬝ᵥ b := by
    -- Every nonzero coefficient of `uRaw` lands on an implicit row, so feasible points evaluate
    -- `A *ᵥ x` and `b` identically against `uRaw`.
    unfold dotProduct
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hs_implicit : is_implicit_equality A b s
    · rw [hs_implicit hxP]
    · by_cases hsk : s = k
      · subst hsk
        simp [huRaw_k_zero]
      · have hus_zero : uRaw s = 0 := huRaw_zero s hs_implicit hsk
        simp [hus_zero]
  have hrow_diff : uRaw ᵥ* A = A r - lam • A k := by
    -- Rearranging the prescribed-anchor row identity isolates the implicit remainder.
    ext c
    have hc := congrFun hrow c
    dsimp at hc ⊢
    linarith
  have hrhs_diff : uRaw ⬝ᵥ b = b r - lam * b k := by
    -- The same rearrangement works for the right-hand side scalar identity.
    linarith
  -- Evaluate the isolated row difference on a feasible point and collapse the implicit tail.
  calc
    (A r - lam • A k) ⬝ᵥ x = (uRaw ᵥ* A) ⬝ᵥ x := by rw [hrow_diff]
    _ = uRaw ⬝ᵥ (A *ᵥ x) := by rw [Matrix.dotProduct_mulVec]
    _ = uRaw ⬝ᵥ b := huRaw_eval
    _ = b r - lam * b k := hrhs_diff

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap03/section_3_9/ch3_sec3_9_theorem_3_27.lean

Theorem 3.27: the raw prescribed-anchor normalization rewrites row `r` as one positive copy of
the facet row `k` plus a remainder supported only on implicit rows. -/
lemma sameFacetRow_eq_pos_smul_fixedAnchor_add_implicit_pre
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r k : Fin m)
    (hfacet_k :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hr_not_implicit : ¬ is_implicit_equality A b r)
    (hrk : r ≠ k)
    (hrk_face :
      active_constraint_face A b ({r} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m))) :
    ∃ lam : ℝ, ∃ uRaw : Fin m → ℝ,
      0 < lam ∧
        uRaw k = 0 ∧
        (∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → uRaw s = 0) ∧
        uRaw ᵥ* A + lam • A k = A r ∧
        uRaw ⬝ᵥ b + lam * b k = b r := by
  have hk_not_implicit : ¬ is_implicit_equality A b k := by
    intro hk_implicit
    have hsingleton_implicit :
        ∀ i : Fin m, i ∈ ({k} : Set (Fin m)) → is_implicit_equality A b i := by
      intro i hi
      have hik : i = k := by simpa using hi
      simpa [hik] using hk_implicit
    have hface_eq :
        active_constraint_face A b ({k} : Set (Fin m)) = polyhedron_le_set A b :=
      activeConstraintFace_eq_polyhedron_of_forall_implicit A b ({k} : Set (Fin m))
        hsingleton_implicit
    exact (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet_k)).2.2.ne hface_eq
  rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet_k)).2.1 with
    ⟨xhat, hxhat_face⟩
  have hP_nonempty : (polyhedron_le_set A b).Nonempty :=
    ⟨xhat, mem_polyhedron_of_mem_active_constraint_face hxhat_face⟩
  obtain ⟨lam, hlam_pos, hdeficit⟩ :=
    sameFacetRows_sub_eq_pos_smul_on_affineHull_of_isFacet
      A b r k hfacet_k hrk_face
  have hrowEq_on_polyhedron :
      ∀ {x : Fin n → ℝ},
        x ∈ polyhedron_le_set A b →
          (A r - lam • A k) ⬝ᵥ x = b r - lam * b k := by
    intro x hxP
    have hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b) :=
      subset_affineSpan ℝ (polyhedron_le_set A b) hxP
    have hdeficit_x := hdeficit hxAff
    have hdot :
        (A r - lam • A k) ⬝ᵥ x =
          (A *ᵥ x) r - lam * (A *ᵥ x) k := by
      simp [Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, sub_mul, Finset.mul_sum,
        mul_assoc]
    rw [hdot]
    linarith
  obtain ⟨uRaw, _huRaw_nonneg, huRaw_zero_all, hrow_diff, hrhs_diff⟩ :=
    implicitMultiplier_of_eq_on_polyhedron
      A b (A r - lam • A k) (b r - lam * b k) hP_nonempty hrowEq_on_polyhedron
  have huRaw_k_zero : uRaw k = 0 := huRaw_zero_all k hk_not_implicit
  have huRaw_zero :
      ∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → uRaw s = 0 := by
    intro s hs_not_implicit _hsk
    exact huRaw_zero_all s hs_not_implicit
  have hrow : uRaw ᵥ* A + lam • A k = A r := by
    -- Reattaching the prescribed anchor to the equality-valid difference recovers row `r`.
    calc
      uRaw ᵥ* A + lam • A k = (A r - lam • A k) + lam • A k := by rw [hrow_diff]
      _ = A r := by
        ext c
        simp
  have hrhs : uRaw ⬝ᵥ b + lam * b k = b r := by
    -- The right-hand side is recovered by the same scalar rearrangement.
    calc
      uRaw ⬝ᵥ b + lam * b k = (b r - lam * b k) + lam * b k := by rw [hrhs_diff]
      _ = b r := by ring
  let _ := hr_not_implicit
  let _ := hrk
  exact ⟨lam, uRaw, hlam_pos, huRaw_k_zero, huRaw_zero, hrow, hrhs⟩

/-- Helper for Theorem 3.27: the geometric blocker is to rewrite row `r` as one positive copy of
the prescribed facet row `k` plus a nonnegative implicit-row remainder. -/
lemma sameFacetRow_nonneg_fixed_anchor_add_implicit_of_eq_singletonFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r k : Fin m)
    (hfacet_k :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hr_not_implicit : ¬ is_implicit_equality A b r)
    (hrk : r ≠ k)
    (hrk_face :
      active_constraint_face A b ({r} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m))) :
    ∃ lam : ℝ, ∃ uImp : Fin m → ℝ,
      0 < lam ∧
        (∀ s : Fin m, 0 ≤ uImp s) ∧
        uImp k = 0 ∧
        (∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → uImp s = 0) ∧
        uImp ᵥ* A + lam • A k = A r ∧
        uImp ⬝ᵥ b + lam * b k = b r := by
  have hk_not_implicit : ¬ is_implicit_equality A b k := by
    intro hk_implicit
    have hface_k_eq :
        active_constraint_face A b ({k} : Set (Fin m)) = polyhedron_le_set A b :=
      activeConstraintFace_eq_polyhedron_of_forall_implicit
        A b ({k} : Set (Fin m)) (by
          intro i hi
          have hik : i = k := by simpa using hi
          simpa [hik] using hk_implicit)
    exact (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet_k)).2.2.ne hface_k_eq
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := by
    rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet_k)).2.1 with ⟨x, hx⟩
    exact ⟨x, mem_polyhedron_of_mem_active_constraint_face hx⟩
  have hraw :
      ∃ lam : ℝ, ∃ uRaw : Fin m → ℝ,
        0 < lam ∧
          uRaw k = 0 ∧
          (∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → uRaw s = 0) ∧
          uRaw ᵥ* A + lam • A k = A r ∧
          uRaw ⬝ᵥ b + lam * b k = b r :=
    sameFacetRow_eq_pos_smul_fixedAnchor_add_implicit_pre
      A b r k hfacet_k hr_not_implicit hrk hrk_face
  rcases hraw with ⟨lam, uRaw, hlam, huRaw_k_zero, huRaw_zero, hrow_raw, hrhs_raw⟩
  have hrowEq_on_polyhedron :
      ∀ {x : Fin n → ℝ},
        x ∈ polyhedron_le_set A b →
          (A r - lam • A k) ⬝ᵥ x = b r - lam * b k :=
    fixedAnchor_difference_eq_on_polyhedron
      A b r k lam uRaw huRaw_k_zero huRaw_zero hrow_raw hrhs_raw
  obtain ⟨uImp, huImp_nonneg, huImp_zero_all, hrow_diff, hrhs_diff⟩ :=
    implicitMultiplier_of_eq_on_polyhedron
      A b (A r - lam • A k) (b r - lam * b k) hP_nonempty hrowEq_on_polyhedron
  have huImp_k_zero : uImp k = 0 := huImp_zero_all k hk_not_implicit
  have huImp_zero :
      ∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → uImp s = 0 := by
    intro s hs_not_implicit _hsk
    exact huImp_zero_all s hs_not_implicit
  have hrow :
      uImp ᵥ* A + lam • A k = A r := by
    -- Reattach the anchor term to the nonnegative implicit remainder.
    calc
      uImp ᵥ* A + lam • A k = (A r - lam • A k) + lam • A k := by rw [hrow_diff]
      _ = A r := by
            ext c
            simp
  have hrhs :
      uImp ⬝ᵥ b + lam * b k = b r := by
    -- The scalar identity is the same recombination on the right-hand side.
    calc
      uImp ⬝ᵥ b + lam * b k = (b r - lam * b k) + lam * b k := by rw [hrhs_diff]
      _ = b r := by ring
  exact ⟨lam, uImp, hlam, huImp_nonneg, huImp_k_zero, huImp_zero, hrow, hrhs⟩

/-- Helper for Theorem 3.27: once row `r` is normalized against the prescribed anchor row `k`,
that ambient certificate packages directly into the singleton-face auxiliary system of `{k}`. -/
lemma singletonFacetAuxCleanReplacement_of_fixed_anchor_data
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r k : Fin m)
    (lam : ℝ)
    (uImp : Fin m → ℝ)
    (hlam : 0 < lam)
    (huImp_nonneg : ∀ s : Fin m, 0 ≤ uImp s)
    (huImp_k_zero : uImp k = 0)
    (huImp_zero :
      ∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → uImp s = 0)
    (hrow : uImp ᵥ* A + lam • A k = A r)
    (hrhs : uImp ⬝ᵥ b + lam * b k = b r) :
    ∃ vAux : Fin (m + m) → ℝ,
      (∀ p : Fin (m + m), 0 ≤ vAux p) ∧
        (∀ p : Fin (m + m),
          ¬ is_implicit_equality
              (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
              (activeConstraintFaceRhs b ({k} : Set (Fin m))) p →
            vAux p = 0) ∧
          (∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → vAux (Fin.castAdd m s) = 0) ∧
            vAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A r ∧
              vAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b r := by
  let vCast : Fin m → ℝ := uImp + lam • Pi.single k (1 : ℝ)
  let vAux : Fin (m + m) → ℝ := Fin.addCases vCast (fun _ ↦ 0)
  have hvCast_eq : vCast = uImp + lam • Pi.single k (1 : ℝ) := by
    funext s
    simp [vCast]
  have hsingle_row :
      (lam • Pi.single k (1 : ℝ)) ᵥ* A = lam • A k := by
    ext c
    rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single k]
    · simp
    · intro s _ hsk
      simp [hsk]
    · simp
  have hsingle_rhs :
      (lam • Pi.single k (1 : ℝ)) ⬝ᵥ b = lam * b k := by
    rw [dotProduct, Finset.sum_eq_single k]
    · simp
    · intro s _ hsk
      simp [hsk]
    · simp
  have hvCast_row :
      vCast ᵥ* A = uImp ᵥ* A + lam • A k := by
    -- The castAdd block is exactly the ambient certificate plus one extra copy of row `k`.
    calc
      vCast ᵥ* A = (uImp + lam • Pi.single k (1 : ℝ)) ᵥ* A := by rw [hvCast_eq]
      _ = uImp ᵥ* A + (lam • Pi.single k (1 : ℝ)) ᵥ* A := by
            ext c
            simp [Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul]
      _ = uImp ᵥ* A + lam • A k := by rw [hsingle_row]
  have hvCast_rhs :
      vCast ⬝ᵥ b = uImp ⬝ᵥ b + lam * b k := by
    -- The scalar right-hand side splits in the same way as the row identity.
    calc
      vCast ⬝ᵥ b = (uImp + lam • Pi.single k (1 : ℝ)) ⬝ᵥ b := by rw [hvCast_eq]
      _ = uImp ⬝ᵥ b + (lam • Pi.single k (1 : ℝ)) ⬝ᵥ b := by
            simp [dotProduct, Finset.sum_add_distrib, add_mul]
      _ = uImp ⬝ᵥ b + lam * b k := by rw [hsingle_rhs]
  have hvAux_nonneg : ∀ p : Fin (m + m), 0 ≤ vAux p := by
    intro p
    revert p
    refine Fin.addCases ?_ ?_
    · intro s
      by_cases hsk : s = k
      · subst s
        -- At the prescribed anchor, the castAdd block carries `lam` on top of the zero remainder.
        simp [vAux, vCast, huImp_k_zero, hlam.le]
      · -- Away from `k`, the castAdd block is just the nonnegative ambient implicit remainder.
        simp [vAux, vCast, hsk, huImp_nonneg s]
    · intro s
      -- The natAdd block is identically zero in the clean replacement.
      simp [vAux, Fin.addCases]
  have hvAux_zero :
      ∀ p : Fin (m + m),
        ¬ is_implicit_equality
            (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
            (activeConstraintFaceRhs b ({k} : Set (Fin m))) p →
          vAux p = 0 := by
    intro p hp_not_implicit
    revert hp_not_implicit
    refine Fin.addCases ?_ ?_ p
    · intro s hsAux_not_implicit
      by_cases hsk : s = k
      · subst s
        have hsAux_implicit :
            is_implicit_equality
              (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
              (activeConstraintFaceRhs b ({k} : Set (Fin m)))
              (Fin.castAdd m k) :=
          singletonFacetAuxOriginalRowImplicit_of_eqSingletonFace A b k k rfl
        exact False.elim (hsAux_not_implicit hsAux_implicit)
      · by_cases hs_implicit : is_implicit_equality A b s
        · have hsAux_implicit :
              is_implicit_equality
                (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
                (activeConstraintFaceRhs b ({k} : Set (Fin m)))
                (Fin.castAdd m s) :=
            singletonFacetAuxOriginalRowImplicit_of_implicitEq A b s k hs_implicit
          exact False.elim (hsAux_not_implicit hsAux_implicit)
        · have hs_zero : uImp s = 0 := huImp_zero s hs_implicit hsk
          simp [vAux, vCast, hsk, hs_zero]
    · intro s hsAux_not_implicit
      have hsAux_implicit :
          is_implicit_equality
            (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
            (activeConstraintFaceRhs b ({k} : Set (Fin m)))
            (Fin.natAdd m s) := by
        intro y hy
        have hyFace :
            y ∈ active_constraint_face A b ({k} : Set (Fin m)) := by
          simpa [active_constraint_face_eq_polyhedronAux] using hy
        by_cases hsk : s ∈ ({k} : Set (Fin m))
        · -- The appended row at `k` is the negated defining equality of the singleton face.
          rw [activeConstraintFaceMatrix_mulVec_natAdd_of_mem A ({k} : Set (Fin m)) y s hsk]
          rw [activeConstraintFaceRhs_natAdd_of_mem b ({k} : Set (Fin m)) s hsk]
          have hsk_eq : s = k := by simpa using hsk
          have hyk : (A *ᵥ y) k = b k :=
            (mem_active_constraint_face_iff.mp hyFace).1 k (by simp)
          simpa [hsk_eq] using congrArg Neg.neg hyk
        · -- NatAdd rows away from `k` are zero rows in the auxiliary singleton-face system.
          rw [activeConstraintFaceMatrix_mulVec_natAdd_of_not_mem A ({k} : Set (Fin m)) y s hsk]
          rw [activeConstraintFaceRhs_natAdd_of_not_mem b ({k} : Set (Fin m)) s hsk]
      exact False.elim (hsAux_not_implicit hsAux_implicit)
  have hvAux_castZero :
      ∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → vAux (Fin.castAdd m s) = 0 := by
    intro s hs_not_implicit hsk
    -- Away from the prescribed anchor, the clean castAdd block is exactly the ambient remainder.
    have hs_zero : uImp s = 0 := huImp_zero s hs_not_implicit hsk
    simp [vAux, vCast, hsk, hs_zero]
  have hvAux_row :
      vAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A r := by
    -- The natAdd block vanishes, so the auxiliary row identity is exactly the ambient one.
    calc
      vAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m))
          = vCast ᵥ* A := by
              ext c
              calc
                (vAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m))) c
                    =
                      ∑ s : Fin m, vAux (Fin.castAdd m s) * A s c +
                        ∑ s : Fin m,
                          vAux (Fin.natAdd m s) *
                            activeConstraintFaceMatrix A ({k} : Set (Fin m))
                              (Fin.natAdd m s) c := by
                        simp [Matrix.vecMul, dotProduct, Fin.sum_univ_add,
                          activeConstraintFaceMatrix_castAdd]
                _ = ∑ s : Fin m, vCast s * A s c + 0 := by
                      congr 1
                      · simp [vAux, vCast]
                      · rw [Finset.sum_eq_zero]
                        intro s _
                        simp [vAux, Fin.addCases]
                _ = ∑ s : Fin m, vCast s * A s c := by simp
                _ = (vCast ᵥ* A) c := by
                      simp [Matrix.vecMul, dotProduct]
      _ = uImp ᵥ* A + lam • A k := hvCast_row
      _ = A r := hrow
  have hvAux_rhs :
      vAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b r := by
    -- The scalar auxiliary identity has the same castAdd-only form.
    calc
      vAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m))
          = vCast ⬝ᵥ b := by
              calc
                vAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m))
                    =
                      ∑ s : Fin m, vAux (Fin.castAdd m s) * b s +
                        ∑ s : Fin m,
                          vAux (Fin.natAdd m s) *
                            activeConstraintFaceRhs b ({k} : Set (Fin m))
                              (Fin.natAdd m s) := by
                        simp [dotProduct, Fin.sum_univ_add, activeConstraintFaceRhs_castAdd]
                _ = ∑ s : Fin m, vCast s * b s + 0 := by
                      congr 1
                      · simp [vAux, vCast]
                      · rw [Finset.sum_eq_zero]
                        intro s _
                        simp [vAux, Fin.addCases]
                _ = ∑ s : Fin m, vCast s * b s := by simp
                _ = vCast ⬝ᵥ b := by
                      simp [dotProduct]
      _ = uImp ⬝ᵥ b + lam * b k := hvCast_rhs
      _ = b r := hrhs
  exact ⟨vAux, hvAux_nonneg, hvAux_zero, hvAux_castZero, hvAux_row, hvAux_rhs⟩

/-- Helper for Theorem 3.27: the missing owner-level step is a clean auxiliary certificate for a
row `r` that defines the same singleton facet as the prescribed anchor row `k`. -/
lemma sameSingletonFacetAuxCleanReplacement_of_eqSingletonFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r k : Fin m)
    (hfacet_k :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hr_not_implicit : ¬ is_implicit_equality A b r)
    (hrk : r ≠ k)
    (hrk_face :
      active_constraint_face A b ({r} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m))) :
    ∃ vAux : Fin (m + m) → ℝ,
      (∀ p : Fin (m + m), 0 ≤ vAux p) ∧
        (∀ p : Fin (m + m),
          ¬ is_implicit_equality
              (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
              (activeConstraintFaceRhs b ({k} : Set (Fin m))) p →
            vAux p = 0) ∧
          (∀ s : Fin m, ¬ is_implicit_equality A b s → s ≠ k → vAux (Fin.castAdd m s) = 0) ∧
            vAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A r ∧
              vAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b r := by
  obtain ⟨lam, uImp, hlam, huImp_nonneg, huImp_k_zero, huImp_zero, hrow, hrhs⟩ :=
    sameFacetRow_nonneg_fixed_anchor_add_implicit_of_eq_singletonFace
      A b r k hfacet_k hr_not_implicit hrk hrk_face
  -- Package the prescribed-anchor ambient decomposition into the singleton-face auxiliary system.
  exact
    singletonFacetAuxCleanReplacement_of_fixed_anchor_data
      A b r k lam uImp hlam huImp_nonneg huImp_k_zero huImp_zero hrow hrhs

/-- Helper for Theorem 3.27: once a positive bad-support row is known to define the same singleton
facet as `k`, replacing that coefficient by a clean same-facet auxiliary certificate should
produce a strictly smaller bad-support witness for the same target row. -/
lemma exists_smallerSingletonFacetAuxBadSupportCertificate_of_eqSingletonFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hAux_nonempty :
      (polyhedron_le_set
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))).Nonempty)
    (uAux : Fin (m + m) → ℝ)
    (huAux_nonneg : ∀ r : Fin (m + m), 0 ≤ uAux r)
    (huAux_zero :
      ∀ r : Fin (m + m),
        ¬ is_implicit_equality
            (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
            (activeConstraintFaceRhs b ({k} : Set (Fin m))) r →
          uAux r = 0)
    (hrowAux :
      uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i)
    (hrhsAux :
      uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i)
    (r : Fin m)
    (hfacet_k :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hr_not_implicit : ¬ is_implicit_equality A b r)
    (hrk : r ≠ k)
    (hur_pos : 0 < uAux (Fin.castAdd m r))
    (hrk_face :
      active_constraint_face A b ({r} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m))) :
    ∃ uAux' : Fin (m + m) → ℝ,
      (∀ p : Fin (m + m), 0 ≤ uAux' p) ∧
        (∀ p : Fin (m + m),
          ¬ is_implicit_equality
              (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
              (activeConstraintFaceRhs b ({k} : Set (Fin m))) p →
            uAux' p = 0) ∧
          uAux' ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i ∧
            uAux' ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i ∧
              singletonFacetAuxBadSupportCard A b k uAux' <
                singletonFacetAuxBadSupportCard A b k uAux := by
  let _ := hAux_nonempty
  obtain ⟨vAux, hvAux_nonneg, hvAux_zero, hvAux_castZero, hrowV, hrhsV⟩ :=
    sameSingletonFacetAuxCleanReplacement_of_eqSingletonFace
      A b r k hfacet_k hr_not_implicit hrk hrk_face
  -- Replace the bad coefficient at `Fin.castAdd m r` by the clean certificate for row `r`.
  exact
    singletonFacetAuxBadSupportCard_strictDecrease_of_cleanReplacement
      A b i k r uAux vAux huAux_nonneg huAux_zero hrowAux hrhsAux hr_not_implicit hrk hur_pos
      hvAux_nonneg hvAux_zero hvAux_castZero hrowV hrhsV

/-- Helper for Theorem 3.27: a bad-support-minimal auxiliary multiplier cannot keep a positive
`castAdd` coefficient on an ambient nonimplicit row away from the prescribed anchor `k`. -/
lemma sameSingletonFacetAuxBadSupportMinimal_zero
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hfacet_k :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hiAux :
      is_implicit_equality
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))
        (Fin.castAdd m i))
    (hAux_nonempty :
      (polyhedron_le_set
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))).Nonempty)
    (uAux : Fin (m + m) → ℝ)
    (huAux_nonneg : ∀ r : Fin (m + m), 0 ≤ uAux r)
    (huAux_zero :
      ∀ r : Fin (m + m),
        ¬ is_implicit_equality
            (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
            (activeConstraintFaceRhs b ({k} : Set (Fin m))) r →
          uAux r = 0)
    (hrowAux :
      uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i)
    (hrhsAux :
      uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i)
    (huAux_min :
      ∀ uAux' : Fin (m + m) → ℝ,
        (∀ r : Fin (m + m), 0 ≤ uAux' r) →
          (∀ r : Fin (m + m),
            ¬ is_implicit_equality
                (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
                (activeConstraintFaceRhs b ({k} : Set (Fin m))) r →
              uAux' r = 0) →
            uAux' ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i →
              uAux' ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i →
                singletonFacetAuxBadSupportCard A b k uAux ≤
                  singletonFacetAuxBadSupportCard A b k uAux') :
    ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uAux (Fin.castAdd m r) = 0 := by
  intro r hr_not_implicit hrk
  by_contra hur_ne_zero
  -- A nonzero bad-support coefficient is automatically positive by auxiliary nonnegativity.
  have hur_pos : 0 < uAux (Fin.castAdd m r) := by
    have hur_ne : 0 ≠ uAux (Fin.castAdd m r) := by
      simpa [eq_comm] using hur_ne_zero
    exact lt_of_le_of_ne (huAux_nonneg (Fin.castAdd m r)) hur_ne
  have hrk_face :
      active_constraint_face A b ({r} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m)) :=
    eqSingletonFace_of_positiveSingletonFacetAuxCoeff
      A b k hfacet_k uAux huAux_zero r hr_not_implicit hur_pos
  obtain ⟨uAux', huAux'_nonneg, huAux'_zero, hrowAux', hrhsAux', hcard_lt⟩ :=
    exists_smallerSingletonFacetAuxBadSupportCertificate_of_eqSingletonFace
      A b i k hAux_nonempty uAux huAux_nonneg huAux_zero hrowAux hrhsAux
      r hfacet_k hr_not_implicit hrk hur_pos hrk_face
  -- Minimality of `uAux` rules out any strictly smaller bad-support competitor.
  exact (not_lt_of_ge (huAux_min uAux' huAux'_nonneg huAux'_zero hrowAux' hrhsAux')) hcard_lt

/-- Helper for Theorem 3.27: the singleton-face auxiliary multiplier for `Fin.castAdd m i`
should first be normalized so that every ambient nonimplicit castAdd row away from `k` vanishes
before translating back to the ambient fixed-anchor decomposition. -/
lemma sameSingletonFacetAuxNormalizedMultiplier_exists
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hfacet_k :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hiAux :
      is_implicit_equality
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))
        (Fin.castAdd m i))
    (hAux_nonempty :
      (polyhedron_le_set
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))).Nonempty) :
    ∃ uAux : Fin (m + m) → ℝ,
      (∀ r : Fin (m + m), 0 ≤ uAux r) ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uAux (Fin.castAdd m r) = 0) ∧
          uAux ᵥ* activeConstraintFaceMatrix A ({k} : Set (Fin m)) = A i ∧
          uAux ⬝ᵥ activeConstraintFaceRhs b ({k} : Set (Fin m)) = b i := by
  obtain ⟨uAux, huAux_nonneg, huAux_zero, hrowAux, hrhsAux, huAux_min⟩ :=
    existsSingletonFacetAuxMultiplier_badSupportMinimal A b i k hiAux hAux_nonempty
  have huCastZero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uAux (Fin.castAdd m r) = 0 :=
    sameSingletonFacetAuxBadSupportMinimal_zero
      A b i k hfacet_k hiAux hAux_nonempty uAux huAux_nonneg huAux_zero hrowAux hrhsAux huAux_min
  -- The minimal auxiliary certificate is the desired normalized multiplier.
  exact ⟨uAux, huAux_nonneg, huCastZero, hrowAux, hrhsAux⟩

/-- Helper for Theorem 3.27: fixing a prescribed anchor row `k` reduces the common-anchor problem
to one auxiliary-system translation problem for the singleton-face polyhedron of `{k}`. -/
lemma sameFacetRow_eq_pos_smul_fixedAnchor_add_implicit_aux
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hk : k ∈ remaining_inequality_indices A b)
    (hfacet_k :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hik_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m))) :
    ∃ lam_i : ℝ, ∃ uImp_i : Fin m → ℝ,
      0 < lam_i ∧
        uImp_i k = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_i r = 0) ∧
        uImp_i ᵥ* A + lam_i • A k = A i ∧
        uImp_i ⬝ᵥ b + lam_i * b k = b i := by
  -- Route correction: the missing owner is the auxiliary-to-ambient translation for a prescribed
  -- anchor row, not another existential common-anchor search in the ambient system.
  let A' : Matrix (Fin (m + m)) (Fin n) ℝ := activeConstraintFaceMatrix A ({k} : Set (Fin m))
  let b' : Fin (m + m) → ℝ := activeConstraintFaceRhs b ({k} : Set (Fin m))
  have hAux_nonempty : (polyhedron_le_set A' b').Nonempty := by
    rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet_k)).2.1 with ⟨x, hx⟩
    -- Reinterpret a point of the singleton face as a feasible point of the auxiliary polyhedron.
    exact ⟨x, by simpa [A', b', active_constraint_face_eq_polyhedronAux] using hx⟩
  have hiAux :
      is_implicit_equality A' b' (Fin.castAdd m i) := by
    -- Equality of singleton faces turns the original castAdd row into an auxiliary implicit row.
    simpa [A', b'] using
      singletonFacetAuxOriginalRowImplicit_of_eqSingletonFace A b i k hik_face
  obtain ⟨uAux, _huAux_nonneg, huCastZero, hrowAux, hrhsAux⟩ :=
    sameSingletonFacetAuxNormalizedMultiplier_exists A b i k hfacet_k hiAux hAux_nonempty
  obtain ⟨lam_i, uImp_i, hui_zero, huImp_i_zero, hrow_i, hrhs_i⟩ :=
    ambientFixedAnchorData_of_auxMultiplier A b i k uAux huCastZero hrowAux hrhsAux
  have hlam_i : 0 < lam_i :=
    sameFacetRow_fixedAnchorPos_of_strictPoint
      A b i k uImp_i lam_i hk hik_face hui_zero huImp_i_zero hrow_i hrhs_i
  -- Once the auxiliary support is normalized, the ambient prescribed-anchor certificate is ready.
  exact ⟨lam_i, uImp_i, hlam_i, hui_zero, huImp_i_zero, hrow_i, hrhs_i⟩

/-- Helper for Theorem 3.27: rows `i` and `a` should admit one shared remaining anchor before the
cross-gap hyperplane is converted into a Chapter 3.22 multiplier certificate. -/
lemma sameFacetRowAndFacetRow_commonAnchor_exists
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i a : Fin m)
    (ha : a ∈ remaining_inequality_indices A b)
    (hfacet_a :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({a} : Set (Fin m))))
    (hia_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({a} : Set (Fin m))) :
    ∃ k : Fin m, ∃ uImp_i uImp_a : Fin m → ℝ, ∃ lam_i lam_a : ℝ,
      k ∈ remaining_inequality_indices A b ∧
        active_constraint_face A b ({k} : Set (Fin m)) =
          active_constraint_face A b ({a} : Set (Fin m)) ∧
        0 < lam_i ∧
        uImp_i k = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_i r = 0) ∧
        uImp_i ᵥ* A + lam_i • A k = A i ∧
        uImp_i ⬝ᵥ b + lam_i * b k = b i ∧
        0 < lam_a ∧
        uImp_a k = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_a r = 0) ∧
        uImp_a ᵥ* A + lam_a • A k = A a ∧
        uImp_a ⬝ᵥ b + lam_a * b k = b a := by
  have hi :
      i ∈ remaining_inequality_indices A b :=
    remaining_row_of_eq_singletonFacet_of_isFacet A b i a hfacet_a hia_face
  -- First choose the shared anchor from the self-normalization of the facet row `a`.
  obtain ⟨k, lam_a, uImp_a, hk, hk_face, hlam_a, hua_zero, huImp_a_zero, hrow_a, hrhs_a⟩ :=
    sameFacetRow_eq_pos_smul_anchor_add_implicit A b a a ha hfacet_a rfl
  have hfacet_k :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))) := by
    -- The anchor row `k` cuts out the same singleton facet as `a`, so the facet property transports.
    exact isFacet_singleton_of_eq_singletonFace A b k a hk_face hfacet_a
  have hik_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m)) := by
    -- Compose the given equality `Fi = Fa` with the anchor-row equality `Fk = Fa`.
    exact hia_face.trans hk_face.symm
  obtain ⟨lam_i, uImp_i, hlam_i, hui_zero, huImp_i_zero, hrow_i, hrhs_i⟩ :=
    sameFacetRow_eq_pos_smul_fixedAnchor_add_implicit_aux A b i k hi hk hfacet_k hik_face
  -- Once the row-`i` certificate is normalized against the same anchor as row `a`, the common
  -- anchor package is just the pair of fixed-anchor decompositions.
  exact
    ⟨k, uImp_i, uImp_a, lam_i, lam_a, hk, hk_face, hlam_i, hui_zero, huImp_i_zero, hrow_i,
      hrhs_i, hlam_a, hua_zero, huImp_a_zero, hrow_a, hrhs_a⟩

/-- Helper for Theorem 3.27: a shared-anchor normalization turns the cross-gap hyperplane into an
equality-valid implicit-row combination, so Chapter 3.22 can recover the final nonnegative
multiplier certificate. -/
lemma sameFacetRow_gapHyperplane_nonneg_rowMultiplier_of_commonAnchor
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i a k : Fin m)
    (uImp_i uImp_a : Fin m → ℝ)
    (lam_i lam_a : ℝ)
    (hk : k ∈ remaining_inequality_indices A b)
    (hk_face :
      active_constraint_face A b ({k} : Set (Fin m)) =
        active_constraint_face A b ({a} : Set (Fin m)))
    (hui_zero : uImp_i k = 0)
    (huImp_i_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_i r = 0)
    (hrow_i : uImp_i ᵥ* A + lam_i • A k = A i)
    (hrhs_i : uImp_i ⬝ᵥ b + lam_i * b k = b i)
    (hua_zero : uImp_a k = 0)
    (huImp_a_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_a r = 0)
    (hrow_a : uImp_a ᵥ* A + lam_a • A k = A a)
    (hrhs_a : uImp_a ⬝ᵥ b + lam_a * b k = b a)
    {xP : Fin n → ℝ}
    (hxP : xP ∈ polyhedron_le_set A b)
    (hxP_lt : (A *ᵥ xP) a < b a) :
    let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
    ∃ uGap : Fin m → ℝ,
      0 ≤ uGap ∧
        uGap ᵥ* A = ((gap a) • A i - (gap i) • A a) ∧
        uGap ⬝ᵥ b ≤ gap a * b i - gap i * b a := by
  let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
  have hxPAff :
      xP ∈ affineSpan ℝ (polyhedron_le_set A b) :=
    subset_affineSpan ℝ (polyhedron_le_set A b) hxP
  have hgap_i :
      gap i = lam_i * gap k := by
    have hsub_i :
        (A *ᵥ xP) i - b i = lam_i * ((A *ᵥ xP) k - b k) :=
      sameFacetRow_sub_eq_smul_anchorSub_of_implicitEq
        A b i k uImp_i lam_i hk hui_zero huImp_i_zero hrow_i hrhs_i hxPAff
    dsimp [gap] at hsub_i ⊢
    linarith
  have hgap_a :
      gap a = lam_a * gap k := by
    have hsub_a :
        (A *ᵥ xP) a - b a = lam_a * ((A *ᵥ xP) k - b k) :=
      sameFacetRow_sub_eq_smul_anchorSub_of_implicitEq
        A b a k uImp_a lam_a hk hua_zero huImp_a_zero hrow_a hrhs_a hxPAff
    dsimp [gap] at hsub_a ⊢
    linarith
  have hcoeff_zero : gap a * lam_i - gap i * lam_a = 0 := by
    rw [hgap_i, hgap_a]
    ring
  let vImp : Fin m → ℝ := fun r ↦ gap a * uImp_i r - gap i * uImp_a r
  have hvImp_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → vImp r = 0 := by
    intro r hr_not_implicit
    by_cases hrk : r = k
    · subst hrk
      simp [vImp, hui_zero, hua_zero]
    · have hui_r : uImp_i r = 0 := huImp_i_zero r hr_not_implicit hrk
      have hua_r : uImp_a r = 0 := huImp_a_zero r hr_not_implicit hrk
      simp [vImp, hui_r, hua_r]
  have hvImp_eq :
      vImp = (gap a) • uImp_i - (gap i) • uImp_a := by
    funext r
    simp [vImp, Pi.sub_apply]
  have hvImp_vecMul_aux :
      vImp ᵥ* A + (gap a * lam_i - gap i * lam_a) • A k =
        (gap a) • A i - (gap i) • A a := by
    calc
      vImp ᵥ* A + (gap a * lam_i - gap i * lam_a) • A k
          = (((gap a) • uImp_i - (gap i) • uImp_a) ᵥ* A) +
              (gap a * lam_i - gap i * lam_a) • A k := by
                rw [hvImp_eq]
      _ = (((gap a) • uImp_i) ᵥ* A - ((gap i) • uImp_a) ᵥ* A) +
            (gap a * lam_i - gap i * lam_a) • A k := by
              rw [Matrix.sub_vecMul]
      _ = ((gap a) • (uImp_i ᵥ* A) - (gap i) • (uImp_a ᵥ* A)) +
            (gap a * lam_i - gap i * lam_a) • A k := by
              ext c
              simp [Matrix.vecMul, dotProduct, Finset.sum_sub_distrib, Finset.mul_sum, sub_mul,
                mul_assoc]
      _ = (gap a) • (uImp_i ᵥ* A + lam_i • A k) -
            (gap i) • (uImp_a ᵥ* A + lam_a • A k) := by
              ext c
              simp [sub_eq_add_neg]
              ring
      _ = (gap a) • A i - (gap i) • A a := by rw [hrow_i, hrow_a]
  have hvImp_vecMul :
      vImp ᵥ* A = (gap a) • A i - (gap i) • A a := by
    calc
      vImp ᵥ* A
          = vImp ᵥ* A + (gap a * lam_i - gap i * lam_a) • A k := by
              simp [hcoeff_zero]
      _ = (gap a) • A i - (gap i) • A a := hvImp_vecMul_aux
  have hvImp_rhs_aux :
      vImp ⬝ᵥ b + (gap a * lam_i - gap i * lam_a) * b k =
        gap a * b i - gap i * b a := by
    calc
      vImp ⬝ᵥ b + (gap a * lam_i - gap i * lam_a) * b k
          = (((gap a) • uImp_i - (gap i) • uImp_a) ⬝ᵥ b) +
              (gap a * lam_i - gap i * lam_a) * b k := by
                rw [hvImp_eq]
      _ = (((gap a) • uImp_i) ⬝ᵥ b - ((gap i) • uImp_a) ⬝ᵥ b) +
            (gap a * lam_i - gap i * lam_a) * b k := by
              simp [dotProduct_sub]
      _ = ((gap a) * (uImp_i ⬝ᵥ b) - (gap i) * (uImp_a ⬝ᵥ b)) +
            (gap a * lam_i - gap i * lam_a) * b k := by
              simp [dotProduct, Finset.mul_sum, mul_assoc]
      _ = gap a * (uImp_i ⬝ᵥ b + lam_i * b k) -
            gap i * (uImp_a ⬝ᵥ b + lam_a * b k) := by
              ring
      _ = gap a * b i - gap i * b a := by rw [hrhs_i, hrhs_a]
  have hvImp_rhs :
      vImp ⬝ᵥ b = gap a * b i - gap i * b a := by
    calc
      vImp ⬝ᵥ b
          = vImp ⬝ᵥ b + (gap a * lam_i - gap i * lam_a) * b k := by
              simp [hcoeff_zero]
      _ = gap a * b i - gap i * b a := hvImp_rhs_aux
  have hrowEq_on_polyhedron :
      ∀ {x : Fin n → ℝ},
        x ∈ polyhedron_le_set A b →
          ((gap a) • A i - (gap i) • A a) ⬝ᵥ x = gap a * b i - gap i * b a := by
    intro x hx
    calc
      ((gap a) • A i - (gap i) • A a) ⬝ᵥ x
          = (vImp ᵥ* A) ⬝ᵥ x := by rw [hvImp_vecMul]
      _ = vImp ⬝ᵥ (A *ᵥ x) := by rw [Matrix.dotProduct_mulVec]
      _ = vImp ⬝ᵥ b := by
            unfold dotProduct
            refine Finset.sum_congr rfl ?_
            intro r hr
            by_cases hr_implicit : is_implicit_equality A b r
            · rw [hr_implicit hx]
            · have hvImp_r : vImp r = 0 := hvImp_zero r hr_implicit
              simp [hvImp_r]
      _ = gap a * b i - gap i * b a := hvImp_rhs
  obtain ⟨uGap, huGap_nonneg, _huGap_zero, huGap_row, huGap_rhs⟩ :=
    implicitMultiplier_of_eq_on_polyhedron
      A b ((gap a) • A i - (gap i) • A a) (gap a * b i - gap i * b a)
      ⟨xP, hxP⟩ hrowEq_on_polyhedron
  -- Chapter 3.22 now packages the equality-valid cross-gap row as the required nonnegative
  -- row-multiplier witness.
  refine ⟨uGap, ?_, huGap_row, huGap_rhs.le⟩
  intro r
  exact huGap_nonneg r

/-- Helper for Theorem 3.27: in the singleton-face auxiliary system for row `k`, the original
row `i` should already evaluate to equality at any ambient affine-hull point where row `k` is
tight, provided rows `i` and `k` cut out the same singleton facet. -/
lemma sameSingletonFacetAuxCastAdd_eval_of_rowEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    {x : Fin n → ℝ}
    (hxi : (A *ᵥ x) i = b i) :
    (activeConstraintFaceMatrix A ({k} : Set (Fin m)) *ᵥ x) (Fin.castAdd m i) =
      activeConstraintFaceRhs b ({k} : Set (Fin m)) (Fin.castAdd m i) := by
  -- The original block of the singleton-face auxiliary system is literally the ambient row system.
  rw [Matrix.mulVec, activeConstraintFaceMatrix_castAdd, activeConstraintFaceRhs_castAdd]
  simpa [Matrix.mulVec] using hxi

/-- Helper for Theorem 3.27: a common-anchor normalization for rows `i` and `k` is already enough
to certify the auxiliary castAdd equality for row `i`. -/
lemma sameSingletonFacetAuxCastAdd_eval_of_commonAnchor
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k a : Fin m)
    (uImp_i uImp_k : Fin m → ℝ)
    (lam_i lam_k : ℝ)
    (ha : a ∈ remaining_inequality_indices A b)
    (hui_zero : uImp_i a = 0)
    (huImp_i_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp_i r = 0)
    (hrow_i : uImp_i ᵥ* A + lam_i • A a = A i)
    (hrhs_i : uImp_i ⬝ᵥ b + lam_i * b a = b i)
    (huk_zero : uImp_k a = 0)
    (huImp_k_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp_k r = 0)
    (hrow_k : uImp_k ᵥ* A + lam_k • A a = A k)
    (hrhs_k : uImp_k ⬝ᵥ b + lam_k * b a = b k)
    (hlam_k : 0 < lam_k)
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxk : (A *ᵥ x) k = b k) :
    (activeConstraintFaceMatrix A ({k} : Set (Fin m)) *ᵥ x) (Fin.castAdd m i) =
      activeConstraintFaceRhs b ({k} : Set (Fin m)) (Fin.castAdd m i) := by
  -- First recover the ambient row-`i` equality from the shared anchor, then rewrite to castAdd.
  have hxi : (A *ᵥ x) i = b i :=
    sameFacetRow_eq_of_commonAnchor
      A b i k a uImp_i uImp_k lam_i lam_k ha hui_zero huImp_i_zero hrow_i hrhs_i
      huk_zero huImp_k_zero hrow_k hrhs_k hlam_k hxAff hxk
  exact sameSingletonFacetAuxCastAdd_eval_of_rowEq A b i k hxi

/-- Helper for Theorem 3.27: once row `i` is normalized directly against row `k`, the common-anchor
package needed by the auxiliary singleton-face transport is immediate by taking `a = k`. -/
lemma sameFacetRows_commonAnchor_exists_of_fixedAnchor
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hk : k ∈ remaining_inequality_indices A b)
    (hfixed :
      ∃ lam_i : ℝ, ∃ uImp_i : Fin m → ℝ,
        0 < lam_i ∧
          uImp_i k = 0 ∧
          (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_i r = 0) ∧
          uImp_i ᵥ* A + lam_i • A k = A i ∧
          uImp_i ⬝ᵥ b + lam_i * b k = b i) :
    ∃ a : Fin m, ∃ uImp_i uImp_k : Fin m → ℝ, ∃ lam_i lam_k : ℝ,
      a ∈ remaining_inequality_indices A b ∧
        uImp_i a = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp_i r = 0) ∧
        uImp_i ᵥ* A + lam_i • A a = A i ∧
        uImp_i ⬝ᵥ b + lam_i * b a = b i ∧
        uImp_k a = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp_k r = 0) ∧
        uImp_k ᵥ* A + lam_k • A a = A k ∧
        uImp_k ⬝ᵥ b + lam_k * b a = b k ∧
        0 < lam_k := by
  rcases hfixed with ⟨lam_i, uImp_i, hlam_i, hui_zero, huImp_i_zero, hrow_i, hrhs_i⟩
  let uImp_k : Fin m → ℝ := 0
  refine
    ⟨k, uImp_i, uImp_k, lam_i, 1, hk, hui_zero, huImp_i_zero, hrow_i, hrhs_i, ?_, ?_, ?_, ?_,
      by norm_num⟩
  · -- The zero remainder vanishes at the chosen anchor row `k`.
    simp [uImp_k]
  · intro r _hr_not_implicit _hrk
    -- The anchor row decomposition for row `k` uses no implicit remainder at all.
    simp [uImp_k]
  · -- Choosing `lam_k = 1` and zero remainder reproduces row `k` tautologically.
    ext c
    simp [uImp_k]
  · -- The same tautological normalization works on the right-hand side.
    simp [uImp_k]

/-- Helper for Theorem 3.27: the Chapter 3.22 route for the cross-gap hyperplane reduces validity
to one explicit nonnegative row-multiplier witness. -/
lemma sameFacetRow_gapHyperplane_nonneg_rowMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i a : Fin m)
    (ha : a ∈ remaining_inequality_indices A b)
    (hfacet_a :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({a} : Set (Fin m))))
    (hia_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({a} : Set (Fin m)))
    {xP : Fin n → ℝ}
    (hxP : xP ∈ polyhedron_le_set A b)
    (hxP_lt : (A *ᵥ xP) a < b a) :
    let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
    ∃ uGap : Fin m → ℝ,
      0 ≤ uGap ∧
        uGap ᵥ* A = ((gap a) • A i - (gap i) • A a) ∧
        uGap ⬝ᵥ b ≤ gap a * b i - gap i * b a := by
  let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
  by_cases hia : i = a
  · subst hia
    refine ⟨0, by simp, ?_, ?_⟩
    · -- When the two rows coincide, the cross-gap row is the zero row.
      ext c
      simp [gap]
    · -- The right-hand side also collapses to zero in the diagonal case.
      simp [gap]
  · have hi :
      i ∈ remaining_inequality_indices A b :=
      remaining_row_of_eq_singletonFacet_of_isFacet A b i a hfacet_a hia_face
    obtain ⟨k, uImp_i, uImp_a, lam_i, lam_a, hk, hk_face, hlam_i, hui_zero, huImp_i_zero,
        hrow_i, hrhs_i, hlam_a, hua_zero, huImp_a_zero, hrow_a, hrhs_a⟩ :=
      sameFacetRowAndFacetRow_commonAnchor_exists A b i a ha hfacet_a hia_face
    -- Route correction: once the duplicate-row branch is normalized against a shared anchor, the
    -- cross-gap row is equality-valid on `P`, so the nonnegative multiplier comes from Chapter 3.22.
    let _ := hi
    let _ := hlam_i
    let _ := hlam_a
    simpa [gap] using
      sameFacetRow_gapHyperplane_nonneg_rowMultiplier_of_commonAnchor
        A b i a k uImp_i uImp_a lam_i lam_a hk hk_face hui_zero huImp_i_zero hrow_i hrhs_i
        hua_zero huImp_a_zero hrow_a hrhs_a hxP hxP_lt

/-- Helper for Theorem 3.27: the cross-gap hyperplane attached to two rows defining the same
singleton facet should cut out a valid inequality on the whole polyhedron. -/
lemma sameFacetRow_gapHyperplane_valid_on_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i a : Fin m)
    (ha : a ∈ remaining_inequality_indices A b)
    (hfacet_a :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({a} : Set (Fin m))))
    (hia_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({a} : Set (Fin m)))
    {xP : Fin n → ℝ}
    (hxP : xP ∈ polyhedron_le_set A b)
    (hxP_lt : (A *ᵥ xP) a < b a) :
    let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
    is_valid_inequality
      (polyhedron_le_set A b)
      ((gap a) • A i - (gap i) • A a)
      (gap a * b i - gap i * b a) := by
  let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
  rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet_a)).2.1 with ⟨x0, hx0⟩
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := by
    exact ⟨x0, mem_polyhedron_of_mem_active_constraint_face hx0⟩
  -- Route correction: package the cross-gap inequality through Theorem 3.22 and isolate the
  -- multiplier construction as the only remaining owner-level blocker.
  rw [valid_inequality_iff_exists_nonneg_row_multiplier
    A b ((gap a) • A i - (gap i) • A a) (gap a * b i - gap i * b a) hP_nonempty]
  simpa [gap] using
    sameFacetRow_gapHyperplane_nonneg_rowMultiplier
      A b i a ha hfacet_a hia_face hxP hxP_lt

/-- Helper for Theorem 3.27: once the cross-gap inequality is valid, facet maximality forces its
equality face to be the whole polyhedron. -/
lemma sameFacetRow_gapHyperplane_eq_on_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i a : Fin m)
    (ha : a ∈ remaining_inequality_indices A b)
    (hfacet_a :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({a} : Set (Fin m))))
    (hia_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({a} : Set (Fin m)))
    {xP : Fin n → ℝ}
    (hxP : xP ∈ polyhedron_le_set A b)
    (hxP_lt : (A *ᵥ xP) a < b a) :
    let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
    ∀ {x : Fin n → ℝ},
      x ∈ polyhedron_le_set A b →
        ((gap a) • A i - (gap i) • A a) ⬝ᵥ x = gap a * b i - gap i * b a := by
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
  let c : Fin n → ℝ := (gap a) • A i - (gap i) • A a
  let δ : ℝ := gap a * b i - gap i * b a
  let F : Set (Fin n → ℝ) := active_constraint_face A b ({a} : Set (Fin m))
  let G : Set (Fin n → ℝ) := face_set P c δ
  have hvalid : is_valid_inequality P c δ := by
    -- The Chapter 3.22 multiplier route already proves the cross-gap inequality is valid on `P`.
    simpa [P, c, δ, gap] using
      sameFacetRow_gapHyperplane_valid_on_polyhedron
        A b i a ha hfacet_a hia_face hxP hxP_lt
  have hF_subset_G : F ⊆ G := by
    intro y hy
    have hyP : y ∈ P := by
      simpa [P, F] using mem_polyhedron_of_mem_active_constraint_face hy
    have hyEq : c ⬝ᵥ y = δ := by
      simpa [c, δ, gap] using
        (sameFacetRow_gapHyperplane_contains_singletonFacet A b i a hia_face xP hy)
    -- Every point of the singleton facet lies on the cross-gap equality hyperplane.
    exact (mem_face_set_iff).2 ⟨hyP, hyEq⟩
  have hxP_mem_G : xP ∈ G := by
    have hxP_eq : c ⬝ᵥ xP = δ := by
      -- The witness point `xP` lies on the cross-gap hyperplane by the defining gap identities.
      calc
        c ⬝ᵥ xP = gap a * (A *ᵥ xP) i - gap i * (A *ᵥ xP) a := by
          simp [c, Matrix.mulVec]
        _ = δ := by
          dsimp [δ, gap]
          ring
    exact (mem_face_set_iff).2 ⟨by simpa [P] using hxP, hxP_eq⟩
  have hxP_not_mem_F : xP ∉ F := by
    intro hxPF
    have hxa_eq : (A *ᵥ xP) a = b a := by
      simpa [F] using (mem_active_constraint_face_iff.mp hxPF).1 a (by simp)
    exact (ne_of_lt hxP_lt) hxa_eq
  have hG_subset_P : G ⊆ P := by
    intro x hx
    exact (mem_face_set_iff.mp hx).1
  show ∀ {x : Fin n → ℝ},
      x ∈ polyhedron_le_set A b →
        ((gap a) • A i - (gap i) • A a) ⬝ᵥ x = gap a * b i - gap i * b a
  intro x hx
  by_cases hGP : G = P
  · have hxG : x ∈ G := by simpa [G, P, hGP] using hx
    exact (mem_face_set_iff.mp hxG).2
  · have hG_proper : is_proper_face P G := by
      refine (is_proper_face_iff).2 ?_
      refine
        ⟨isExposed_face_set_of_valid_inequality hvalid, ⟨xP, hxP_mem_G⟩, ⟨hG_subset_P, ?_⟩⟩
      intro hPG
      exact hGP (Set.Subset.antisymm hG_subset_P hPG)
    have hG_eq_F : G = F := is_facet_maximal hfacet_a hG_proper hF_subset_G
    have hxP_mem_F : xP ∈ F := by
      simpa [hG_eq_F] using hxP_mem_G
    exact False.elim (hxP_not_mem_F hxP_mem_F)

/-- Helper for Theorem 3.27: normalize a same-facet row directly against a prescribed anchor row
once the corresponding cross-gap hyperplane is known to be an equality on the whole polyhedron. -/
lemma sameFacetRow_eq_pos_smul_fixedAnchor_add_implicitCore
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i a : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (ha : a ∈ remaining_inequality_indices A b)
    (hfacet_a :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({a} : Set (Fin m))))
    (hia_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({a} : Set (Fin m))) :
    ∃ lam : ℝ, ∃ uImp : Fin m → ℝ,
      0 < lam ∧
        uImp a = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp r = 0) ∧
        uImp ᵥ* A + lam • A a = A i ∧
        uImp ⬝ᵥ b + lam * b a = b i := by
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  let _ := hi
  rcases exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b a ha with
    ⟨xP, hxP, hxP_lt⟩
  let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
  have hgap_a_pos : 0 < gap a := by
    dsimp [gap]
    linarith
  have hgap_i_pos : 0 < gap i := by
    have hxi_lt : (A *ᵥ xP) i < b i :=
      sameFacetRow_strict_of_eq_singletonFace A b i a hia_face hxP hxP_lt
    dsimp [gap]
    linarith
  let lam : ℝ := gap i / gap a
  have hrowEq_on_polyhedron :
      ∀ {x : Fin n → ℝ}, x ∈ P → (A i - lam • A a) ⬝ᵥ x = b i - lam * b a := by
    intro x hx
    have hcross :
        ((gap a) • A i - (gap i) • A a) ⬝ᵥ x = gap a * b i - gap i * b a := by
      simpa [P, gap] using
        (sameFacetRow_gapHyperplane_eq_on_polyhedron
          A b i a ha hfacet_a hia_face hxP hxP_lt hx)
    have hcross' :
        gap a * (A i ⬝ᵥ x - b i) = gap i * (A a ⬝ᵥ x - b a) := by
      have hcross'' :
          gap a * (A i ⬝ᵥ x) - gap i * (A a ⬝ᵥ x) = gap a * b i - gap i * b a := by
        simpa [Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, sub_mul, Finset.mul_sum,
          mul_assoc] using hcross
      linarith
    have hgap_a_ne : gap a ≠ 0 := ne_of_gt hgap_a_pos
    have hsubx' : A i ⬝ᵥ x - b i = lam * (A a ⬝ᵥ x - b a) := by
      apply mul_right_cancel₀ hgap_a_ne
      calc
        (A i ⬝ᵥ x - b i) * gap a = gap a * (A i ⬝ᵥ x - b i) := by ring
        _ = gap i * (A a ⬝ᵥ x - b a) := hcross'
        _ = ((gap i / gap a) * (A a ⬝ᵥ x - b a)) * gap a := by
              field_simp [hgap_a_ne]
        _ = lam * (A a ⬝ᵥ x - b a) * gap a := by rfl
    have hdot :
        (A i - lam • A a) ⬝ᵥ x = A i ⬝ᵥ x - lam * (A a ⬝ᵥ x) := by
      simp [dotProduct, Finset.sum_sub_distrib, sub_mul, Finset.mul_sum, mul_assoc]
    -- Rewriting the cross-gap identity by the positive anchor gap gives an equality-valid row
    -- difference against the prescribed row `a`.
    calc
      (A i - lam • A a) ⬝ᵥ x = A i ⬝ᵥ x - lam * (A a ⬝ᵥ x) := hdot
      _ = b i - lam * b a := by linarith
  rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet_a)).2.1 with ⟨x0, hx0⟩
  have hP_nonempty : P.Nonempty := ⟨x0, mem_polyhedron_of_mem_active_constraint_face hx0⟩
  obtain ⟨uImp, _huImp_nonneg, huImp_zero_all, hrow_diff, hrhs_diff⟩ :=
    implicitMultiplier_of_eq_on_polyhedron
      A b (A i - lam • A a) (b i - lam * b a) hP_nonempty hrowEq_on_polyhedron
  have ha_not_implicit : ¬ is_implicit_equality A b a :=
    (mem_remaining_inequality_indices_iff A b a).1 ha
  have huImp_anchor : uImp a = 0 := huImp_zero_all a ha_not_implicit
  have huImp_zero :
      ∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp r = 0 := by
    intro r hr_not_implicit _hra
    exact huImp_zero_all r hr_not_implicit
  have huImp_row :
      uImp ᵥ* A + lam • A a = A i := by
    calc
      uImp ᵥ* A + lam • A a = (A i - lam • A a) + lam • A a := by rw [hrow_diff]
      _ = A i := by
            ext c
            simp
  have huImp_rhs :
      uImp ⬝ᵥ b + lam * b a = b i := by
    calc
      uImp ⬝ᵥ b + lam * b a = (b i - lam * b a) + lam * b a := by rw [hrhs_diff]
      _ = b i := by ring
  -- The prescribed-anchor normalization now follows by packaging the equality-valid row
  -- difference with its implicit-support multiplier.
  exact ⟨lam, uImp, by dsimp [lam]; exact div_pos hgap_i_pos hgap_a_pos, huImp_anchor,
    huImp_zero, huImp_row, huImp_rhs⟩

/-- Helper for Theorem 3.27: in the singleton-face auxiliary system for row `k`, the original
row `i` should already evaluate to equality at any ambient affine-hull point where row `k` is
tight, provided rows `i` and `k` cut out the same singleton facet. -/
lemma sameFacetRows_commonAnchor_exists
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hk : k ∈ remaining_inequality_indices A b)
    (hik_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m)))
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m)))) :
    ∃ a : Fin m, ∃ uImp_i uImp_k : Fin m → ℝ, ∃ lam_i lam_k : ℝ,
      a ∈ remaining_inequality_indices A b ∧
        uImp_i a = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp_i r = 0) ∧
        uImp_i ᵥ* A + lam_i • A a = A i ∧
        uImp_i ⬝ᵥ b + lam_i * b a = b i ∧
        uImp_k a = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp_k r = 0) ∧
        uImp_k ᵥ* A + lam_k • A a = A k ∧
        uImp_k ⬝ᵥ b + lam_k * b a = b k ∧
        0 < lam_k := by
  have hfixed :
      ∃ lam_i : ℝ, ∃ uImp_i : Fin m → ℝ,
        0 < lam_i ∧
          uImp_i k = 0 ∧
          (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ k → uImp_i r = 0) ∧
          uImp_i ᵥ* A + lam_i • A k = A i ∧
          uImp_i ⬝ᵥ b + lam_i * b k = b i :=
    sameFacetRow_eq_pos_smul_fixedAnchor_add_implicitCore A b i k hi hk hfacet hik_face
  -- Once the row-`i` certificate is normalized directly against row `k`, the common-anchor data is
  -- exactly the trivial self-normalization of row `k`.
  exact sameFacetRows_commonAnchor_exists_of_fixedAnchor A b i k hk hfixed

/-- Helper for Theorem 3.27: in the singleton-face auxiliary system for row `k`, the original
row `i` should already evaluate to equality at any ambient affine-hull point where row `k` is
tight, provided rows `i` and `k` cut out the same singleton facet. -/
lemma sameSingletonFacetAuxCastAdd_eval_of_affineHull_rowEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hk : k ∈ remaining_inequality_indices A b)
    (hik_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m)))
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxk : (A *ᵥ x) k = b k) :
    (activeConstraintFaceMatrix A ({k} : Set (Fin m)) *ᵥ x) (Fin.castAdd m i) =
      activeConstraintFaceRhs b ({k} : Set (Fin m)) (Fin.castAdd m i) := by
  by_cases hk_irredundant : is_irredundant_row A b k
  · rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.1 with ⟨x0, hx0_face⟩
    have hP_nonempty : (polyhedron_le_set A b).Nonempty := by
      exact ⟨x0, mem_polyhedron_of_mem_active_constraint_face hx0_face⟩
    have hxFaceAff :
        x ∈ affineSpan ℝ (active_constraint_face A b ({k} : Set (Fin m))) := by
      have hxFaceEq :
          x ∈ {y : Fin n → ℝ |
            (A *ᵥ y) k = b k ∧
              ∀ r : Fin m, is_implicit_equality A b r → (A *ᵥ y) r = b r} := by
        constructor
        · exact hxk
        · intro r hr
          -- Ambient affine-hull points already satisfy every implicit equality of `P`.
          exact row_eq_of_implicit_on_affineHull A b r hr hxAff
      -- In the irredundant case, Lemma 3.26 already identifies the singleton-facet affine span.
      change x ∈
        ((affineSpan ℝ (active_constraint_face A b ({k} : Set (Fin m))) :
          AffineSubspace ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))
      rwa [affineSpan_active_constraint_face_singleton_eq_implicit_equalities_and_row
        A b k hP_nonempty hk_irredundant]
    have hxi : (A *ᵥ x) i = b i :=
      sameFacetRow_eq_on_affineSpan_singletonFacet A b i k hik_face hxFaceAff
    -- Translate the ambient row equality back to the original block of the auxiliary system.
    exact sameSingletonFacetAuxCastAdd_eval_of_rowEq A b i k hxi
  · obtain ⟨a, uImp_i, uImp_k, lam_i, lam_k, ha, hui_zero, huImp_i_zero, hrow_i, hrhs_i,
      huk_zero, huImp_k_zero, hrow_k, hrhs_k, hlam_k⟩ :=
        sameFacetRows_commonAnchor_exists A b i k hi hk hik_face hfacet
    -- The duplicate-row branch reduces to the same shared-anchor consumer as soon as the common
    -- anchor data is packaged at the certificate level.
    exact
      sameSingletonFacetAuxCastAdd_eval_of_commonAnchor
        A b i k a uImp_i uImp_k lam_i lam_k ha hui_zero huImp_i_zero hrow_i hrhs_i
        huk_zero huImp_k_zero hrow_k hrhs_k hlam_k hxAff hxk

/-- Helper for Theorem 3.27: on `affineSpan ℝ (polyhedron_le_set A b)`, tightness of a prescribed
facet row should transport to any remaining row cutting out the same singleton face. -/
lemma sameFacetRow_eq_on_affineHullCore
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hj : j ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m)))
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxj : (A *ᵥ x) j = b j) :
    (A *ᵥ x) i = b i := by
  have hAux :
      (activeConstraintFaceMatrix A ({j} : Set (Fin m)) *ᵥ x) (Fin.castAdd m i) =
        activeConstraintFaceRhs b ({j} : Set (Fin m)) (Fin.castAdd m i) :=
    sameSingletonFacetAuxCastAdd_eval_of_affineHull_rowEq
      A b i j hi hj hij_face hfacet hxAff hxj
  -- Route correction: treat the ambient statement as a castAdd wrapper over the singleton-face
  -- auxiliary transport owner.
  rw [Matrix.mulVec, activeConstraintFaceMatrix_castAdd, activeConstraintFaceRhs_castAdd] at hAux
  simpa [Matrix.mulVec] using hAux

/-- Helper for Theorem 3.27: an original row that becomes implicit in the singleton-face auxiliary
system is already tight at any ambient affine-hull point where row `k` is tight. -/
lemma singletonFacetAuxOriginalRow_eval_of_affineHull_rowEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hk : k ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hiAux :
      is_implicit_equality
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))
        (Fin.castAdd m i))
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxk : (A *ᵥ x) k = b k) :
    (A *ᵥ x) i = b i := by
  by_cases hi_implicit : is_implicit_equality A b i
  · -- Ambient implicit rows are already constant on the whole affine hull of `P`.
    exact row_eq_of_implicit_on_affineHull A b i hi_implicit hxAff
  · have hi : i ∈ remaining_inequality_indices A b :=
      (mem_remaining_inequality_indices_iff A b i).2 hi_implicit
    have hik_face :
        active_constraint_face A b ({i} : Set (Fin m)) =
          active_constraint_face A b ({k} : Set (Fin m)) :=
      eqSingletonFace_of_singletonFacetAuxOriginalRowImplicit A b i k hi hfacet hiAux
    have hAux :
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)) *ᵥ x) (Fin.castAdd m i) =
          activeConstraintFaceRhs b ({k} : Set (Fin m)) (Fin.castAdd m i) :=
      sameSingletonFacetAuxCastAdd_eval_of_affineHull_rowEq
        A b i k hi hk hik_face hfacet hxAff hxk
    -- Once the auxiliary castAdd row is known to be tight, translate it back to the ambient row.
    rw [Matrix.mulVec, activeConstraintFaceMatrix_castAdd, activeConstraintFaceRhs_castAdd] at hAux
    simpa [Matrix.mulVec] using hAux

/-- Helper for Theorem 3.27: every implicit row of the singleton-face auxiliary system already
evaluates to equality at an ambient affine-hull point where row `k` is tight. -/
lemma singletonFacetAuxImplicitRow_eval_of_affineHull_rowEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (k : Fin m)
    (hk : k ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (p : Fin (m + m))
    (hpAux :
      is_implicit_equality
        (activeConstraintFaceMatrix A ({k} : Set (Fin m)))
        (activeConstraintFaceRhs b ({k} : Set (Fin m)))
        p)
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxk : (A *ᵥ x) k = b k) :
    (activeConstraintFaceMatrix A ({k} : Set (Fin m)) *ᵥ x) p =
      activeConstraintFaceRhs b ({k} : Set (Fin m)) p := by
  revert hpAux
  refine Fin.addCases ?_ ?_ p
  · intro i hiAux
    -- The original block of the auxiliary system is the ambient row system itself.
    rw [Matrix.mulVec, activeConstraintFaceMatrix_castAdd, activeConstraintFaceRhs_castAdd]
    simpa [Matrix.mulVec] using
      singletonFacetAuxOriginalRow_eval_of_affineHull_rowEq
        A b i k hk hfacet hiAux hxAff hxk
  · intro i _hiAux
    by_cases hik : i ∈ ({k} : Set (Fin m))
    · -- The appended row for `k` is exactly the negated defining equality.
      rw [activeConstraintFaceMatrix_mulVec_natAdd_of_mem A ({k} : Set (Fin m)) x i hik]
      rw [activeConstraintFaceRhs_natAdd_of_mem b ({k} : Set (Fin m)) i hik]
      have hi_eq : i = k := by simpa using hik
      simpa [hi_eq] using congrArg Neg.neg hxk
    · -- Rows appended away from `{k}` are zero in the auxiliary presentation.
      rw [activeConstraintFaceMatrix_mulVec_natAdd_of_not_mem A ({k} : Set (Fin m)) x i hik]
      rw [activeConstraintFaceRhs_natAdd_of_not_mem b ({k} : Set (Fin m)) i hik]

/-- Helper for Theorem 3.27: row-`k` tightness on `affineSpan ℝ (polyhedron_le_set A b)`
propagates to every remaining row defining the same singleton facet. -/
lemma mem_affineSpan_singletonFacet_of_affineHull_rowEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (k : Fin m)
    (hk : k ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxk : (A *ᵥ x) k = b k) :
    x ∈ affineSpan ℝ (active_constraint_face A b ({k} : Set (Fin m))) := by
  let A' : Matrix (Fin (m + m)) (Fin n) ℝ :=
    activeConstraintFaceMatrix A ({k} : Set (Fin m))
  let b' : Fin (m + m) → ℝ :=
    activeConstraintFaceRhs b ({k} : Set (Fin m))
  have hxAuxImplicit :
      x ∈ ({y : Fin n → ℝ | implicit_equality_matrix A' b' *ᵥ y = implicit_equality_rhs A' b'}
        : Set (Fin n → ℝ)) := by
    -- Route correction: prove auxiliary affine-span membership by checking the implicit rows of
    -- the singleton-face auxiliary system one by one.
    change implicit_equality_matrix A' b' *ᵥ x = implicit_equality_rhs A' b'
    ext p
    have hp :
        (A' *ᵥ x) p.1 = b' p.1 := by
      simpa [A', b'] using
        singletonFacetAuxImplicitRow_eval_of_affineHull_rowEq
          A b k hk hfacet p.1 p.2 hxAff hxk
    simpa [A', b', implicit_equality_mulVec_apply, implicit_equality_rhs_apply] using hp
  have hxAuxAff :
      x ∈ affineSpan ℝ (polyhedron_le_set A' b') := by
    -- Theorem 3.17 for the auxiliary system converts auxiliary implicit equalities into affine
    -- span membership.
    change
      x ∈ ((affineSpan ℝ (polyhedron_le_set A' b') :
        AffineSubspace ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))
    rw [affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set A' b']
    exact hxAuxImplicit
  -- Reinterpret the auxiliary affine span as the affine span of the singleton active face.
  simpa [A', b', active_constraint_face_eq_polyhedronAux] using hxAuxAff

/-- Helper for Theorem 3.27: row-`k` tightness on `affineSpan ℝ (polyhedron_le_set A b)`
propagates to every remaining row defining the same singleton facet. -/
lemma sameFacetRowsTight_of_affineHull_rowEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hk : k ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hik_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m)))
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxk : (A *ᵥ x) k = b k) :
    (A *ᵥ x) i = b i := by
  -- Route correction: first place `x` on the affine span of the singleton facet cut out by `k`,
  -- then read off the row-`i` equality from the common singleton-face geometry.
  have hxFaceAff :
      x ∈ affineSpan ℝ (active_constraint_face A b ({k} : Set (Fin m))) :=
    mem_affineSpan_singletonFacet_of_affineHull_rowEq A b k hk hfacet hxAff hxk
  exact sameFacetRow_eq_on_affineSpan_singletonFacet A b i k hik_face hxFaceAff

/-- Helper for Theorem 3.27: the cross-multiplied gap identity already holds on the affine span of
the singleton facet cut out by row `k`. -/
lemma sameFacetRow_gapCrossMul_eq_on_affineSpan_singletonFacet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r k : Fin m)
    (hrk_face :
      active_constraint_face A b ({r} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m)))
    {xP x : Fin n → ℝ}
    (hxAff :
      x ∈ affineSpan ℝ (active_constraint_face A b ({k} : Set (Fin m)))) :
    let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
    gap k * ((A *ᵥ x) r - b r) = gap r * ((A *ᵥ x) k - b k) := by
  dsimp
  have hxr : (A *ᵥ x) r = b r :=
    sameFacetRow_eq_on_affineSpan_singletonFacet A b r k hrk_face hxAff
  have hxk : (A *ᵥ x) k = b k :=
    sameFacetRow_eq_on_affineSpan_singletonFacet A b k k rfl hxAff
  -- Both singleton-face deficits vanish on the affine span, so the cross-multiplied identity
  -- reduces to `0 = 0`.
  calc
    (b k - (A *ᵥ xP) k) * ((A *ᵥ x) r - b r)
        = (b k - (A *ᵥ xP) k) * 0 := by rw [hxr]; ring
    _ = 0 := by ring
    _ = (b r - (A *ᵥ xP) r) * 0 := by ring
    _ = (b r - (A *ᵥ xP) r) * ((A *ᵥ x) k - b k) := by rw [hxk]; ring


/-- Helper for Theorem 3.27: a singleton-facet point that is strict off the row class of `j`
admits a short step toward any ambient affine-hull point that is tight on row `j`, while staying
inside the singleton facet. -/
lemma exists_small_step_mem_singletonFacet_of_affineHull_rowEq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m)
    (hj : j ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    {xbar x : Fin n → ℝ}
    (hxbar :
      xbar ∈ active_constraint_face A b ({j} : Set (Fin m)))
    (hstrict :
      ∀ i : Fin m,
        i ∈ remaining_inequality_indices A b →
          active_constraint_face A b ({i} : Set (Fin m)) ≠
            active_constraint_face A b ({j} : Set (Fin m)) →
              (A *ᵥ xbar) i < b i)
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxj : (A *ᵥ x) j = b j) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε ≤ 1 ∧
          xbar + ε • (x - xbar) ∈ active_constraint_face A b ({j} : Set (Fin m)) := by
  classical
  let Fj : Set (Fin n → ℝ) := active_constraint_face A b ({j} : Set (Fin m))
  let badRows : Finset (Fin m) :=
    Finset.univ.filter fun i ↦
      i ∈ remaining_inequality_indices A b ∧
        active_constraint_face A b ({i} : Set (Fin m)) ≠ Fj
  by_cases hbad_nonempty : badRows.Nonempty
  · let slack : {i // i ∈ badRows} → ℝ :=
        fun i ↦ b i.1 - (A *ᵥ xbar) i.1
    let drift : {i // i ∈ badRows} → ℝ :=
        fun i ↦ (A *ᵥ x) i.1 - (A *ᵥ xbar) i.1
    let bound : {i // i ∈ badRows} → ℝ :=
        fun i ↦ if hpos : 0 < drift i then min 1 (slack i / drift i) else 1
    letI : Nonempty {i // i ∈ badRows} := by
      rcases hbad_nonempty with ⟨i, hi⟩
      exact ⟨⟨i, hi⟩⟩
    let ε : ℝ := Finset.univ.inf' Finset.univ_nonempty bound
    have hε_pos : 0 < ε := by
      -- Every rowwise admissible bound is positive, so their infimum stays positive.
      have hbound_pos :
          ∀ i : {i // i ∈ badRows}, 0 < bound i := by
        intro i
        have hi_data :
            i.1 ∈ remaining_inequality_indices A b ∧
              active_constraint_face A b ({i.1} : Set (Fin m)) ≠ Fj := by
          simpa [badRows, Fj] using (Finset.mem_filter.mp i.2).2
        by_cases hpos : 0 < drift i
        · have hslack_pos : 0 < slack i := by
            have hrow :
                (A *ᵥ xbar) i.1 < b i.1 :=
              hstrict i.1 hi_data.1 (by simpa [Fj] using hi_data.2)
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
      -- The chosen step is bounded above by every rowwise bound, hence by `1`.
      have hbound_le_one :
          ∀ i : {i // i ∈ badRows}, bound i ≤ 1 := by
        intro i
        by_cases hpos : 0 < drift i
        · dsimp [bound]
          rw [if_pos hpos]
          exact min_le_left _ _
        · dsimp [bound]
          simp [hpos]
      have hε_le_bound :
          ∀ i : {i // i ∈ badRows}, ε ≤ bound i := by
        intro i
        dsimp [ε]
        exact Finset.inf'_le _ (Finset.mem_univ i)
      have hε_le_bound0 :
          ε ≤ bound (Classical.choice inferInstance) :=
        hε_le_bound (Classical.choice inferInstance)
      exact hε_le_bound0.trans (hbound_le_one _)
    refine ⟨ε, hε_pos, hε_le_one, ?_⟩
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      have hij : i = j := by simpa using hi
      have hrow_combo :
          (A *ᵥ (xbar + ε • (x - xbar))) i =
            (1 - ε) * (A *ᵥ xbar) i + ε * (A *ᵥ x) i := by
        simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
        ring
      have hj_mem : j ∈ ({j} : Set (Fin m)) := by simp
      have hxbar_row : (A *ᵥ xbar) i = b i := by
        simpa [hij] using (mem_active_constraint_face_iff.mp hxbar).1 j hj_mem
      have hx_row_i : (A *ᵥ x) i = b i := by
        simpa [hij] using hxj
      calc
        (A *ᵥ (xbar + ε • (x - xbar))) i
            = (1 - ε) * (A *ᵥ xbar) i + ε * (A *ᵥ x) i := hrow_combo
        _ = (1 - ε) * b i + ε * b i := by rw [hxbar_row, hx_row_i]
        _ = b i := by ring
    · intro i hi
      have hij : i ≠ j := by
        intro hij_eq
        exact hi (by simp [hij_eq])
      by_cases hi_implicit : is_implicit_equality A b i
      · have hxbar_poly : xbar ∈ polyhedron_le_set A b :=
          mem_polyhedron_of_mem_active_constraint_face hxbar
        have hxbar_eq : (A *ᵥ xbar) i = b i := hi_implicit hxbar_poly
        have hx_eq : (A *ᵥ x) i = b i :=
          row_eq_of_implicit_on_affineHull A b i hi_implicit hxAff
        have hrow_combo :
            (A *ᵥ (xbar + ε • (x - xbar))) i =
              (1 - ε) * (A *ᵥ xbar) i + ε * (A *ᵥ x) i := by
          simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
          ring
        calc
          (A *ᵥ (xbar + ε • (x - xbar))) i
              = (1 - ε) * (A *ᵥ xbar) i + ε * (A *ᵥ x) i := hrow_combo
          _ = (1 - ε) * b i + ε * b i := by rw [hxbar_eq, hx_eq]
          _ = b i := by ring
          _ ≤ b i := le_rfl
      · have hi_remaining : i ∈ remaining_inequality_indices A b :=
          (mem_remaining_inequality_indices_iff A b i).2 hi_implicit
        by_cases hij_face :
            active_constraint_face A b ({i} : Set (Fin m)) =
              active_constraint_face A b ({j} : Set (Fin m))
        · have hx_eq : (A *ᵥ x) i = b i :=
            sameFacetRowsTight_of_affineHull_rowEq
              A b i j hi_remaining hj hfacet hij_face hxAff hxj
          have hxbar_aff :
              xbar ∈ affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m))) :=
            subset_affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m))) hxbar
          have hxbar_eq : (A *ᵥ xbar) i = b i :=
            sameFacetRow_eq_on_affineSpan_singletonFacet A b i j hij_face hxbar_aff
          have hrow_combo :
              (A *ᵥ (xbar + ε • (x - xbar))) i =
                (1 - ε) * (A *ᵥ xbar) i + ε * (A *ᵥ x) i := by
            simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
            ring
          calc
            (A *ᵥ (xbar + ε • (x - xbar))) i
                = (1 - ε) * (A *ᵥ xbar) i + ε * (A *ᵥ x) i := hrow_combo
            _ = (1 - ε) * b i + ε * b i := by rw [hxbar_eq, hx_eq]
            _ = b i := by ring
            _ ≤ b i := le_rfl
        · let i' : {i // i ∈ badRows} := by
            refine ⟨i, ?_⟩
            simp [badRows, Fj, hi_remaining, hij_face]
          have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
          have hstrict_i : (A *ᵥ xbar) i < b i := hstrict i hi_remaining hij_face
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
              (A *ᵥ (xbar + ε • (x - xbar))) i = (A *ᵥ xbar) i + ε * drift i' := by
            dsimp [i', drift]
            simp [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
          calc
            (A *ᵥ (xbar + ε • (x - xbar))) i
                = (A *ᵥ xbar) i + ε * drift i' := hrow_eval
            _ ≤ (A *ᵥ xbar) i + slack i' := by gcongr
            _ = b i := by
                  dsimp [i', slack]
                  ring
  · have h_one_pos : 0 < (1 : ℝ) := by norm_num
    refine ⟨1, h_one_pos, le_rfl, ?_⟩
    have hstep_eq : xbar + (1 : ℝ) • (x - xbar) = x := by
      simp [sub_eq_add_neg]
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      have hij : i = j := by simpa using hi
      rw [hstep_eq]
      simpa [hij] using hxj
    · intro i hi
      have hij : i ≠ j := by
        intro hij_eq
        exact hi (by simp [hij_eq])
      by_cases hi_implicit : is_implicit_equality A b i
      · rw [hstep_eq]
        exact le_of_eq (row_eq_of_implicit_on_affineHull A b i hi_implicit hxAff)
      · have hi_remaining : i ∈ remaining_inequality_indices A b :=
          (mem_remaining_inequality_indices_iff A b i).2 hi_implicit
        have hij_face :
            active_constraint_face A b ({i} : Set (Fin m)) =
              active_constraint_face A b ({j} : Set (Fin m)) := by
          by_contra hij_face
          have hi_bad : i ∈ badRows := by
            simp [badRows, Fj, hi_remaining, hij_face]
          exact hbad_nonempty ⟨i, hi_bad⟩
        rw [hstep_eq]
        exact le_of_eq
          (sameFacetRowsTight_of_affineHull_rowEq
            A b i j hi_remaining hj hfacet hij_face hxAff hxj)

/-- Helper for Theorem 3.27: the affine span of a singleton facet should be the ambient affine
hull cut by the defining row equation. -/
lemma affineSpan_active_constraint_face_singleton_eq_affineHull_and_row
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m)
    (hj : j ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m)))) :
    affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m))) =
      {x : Fin n → ℝ |
        x ∈ affineSpan ℝ (polyhedron_le_set A b) ∧
          (A *ᵥ x) j = b j} := by
  ext x
  constructor
  · intro hxAff
    constructor
    · -- The singleton facet sits inside the ambient polyhedron, so its affine span does too.
      exact
        affineSpan_mono ℝ
          (by
            intro y hy
            exact mem_polyhedron_of_mem_active_constraint_face hy)
          hxAff
    · -- Every point of the singleton-facet affine span remains on the defining row hyperplane.
      exact sameFacetRow_eq_on_affineSpan_singletonFacet A b j j rfl hxAff
  · rintro ⟨hxAff, hxj⟩
    -- Route correction: consume the earlier singleton-facet affine-span membership lemma instead
    -- of rebuilding the small-step argument here.
    exact mem_affineSpan_singletonFacet_of_affineHull_rowEq A b j hj hfacet hxAff hxj

/-- Helper for Theorem 3.27: the ambient affine hull should be generated by one strict feasible
point together with the singleton facet of `k`. -/
lemma ambientAffineHull_eq_affineSpan_strictPoint_union_singletonFacet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (k : Fin m)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    {xP : Fin n → ℝ}
    (hxP : xP ∈ polyhedron_le_set A b)
    (hxP_lt : (A *ᵥ xP) k < b k) :
    affineSpan ℝ (polyhedron_le_set A b) =
      affineSpan ℝ ({xP} ∪ active_constraint_face A b ({k} : Set (Fin m))) := by
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  let F : Set (Fin n → ℝ) := active_constraint_face A b ({k} : Set (Fin m))
  let S : AffineSubspace ℝ (Fin n → ℝ) := affineSpan ℝ ({xP} ∪ F)
  let D : Submodule ℝ (Fin n → ℝ) := (affineSpan ℝ P).direction
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductStrongDual (A k)).toLinearMap
  rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.1 with ⟨xhat, hxhat_face⟩
  have hxhat_poly : xhat ∈ P := by
    simpa [F, P] using mem_polyhedron_of_mem_active_constraint_face hxhat_face
  have hxhat_face_aff : xhat ∈ affineSpan ℝ F := subset_affineSpan ℝ F hxhat_face
  have hxhat_poly_aff : xhat ∈ affineSpan ℝ P := subset_affineSpan ℝ P hxhat_poly
  have hxP_aff : xP ∈ affineSpan ℝ P := subset_affineSpan ℝ P hxP
  have hxP_mem_S : xP ∈ S := by
    exact subset_affineSpan ℝ ({xP} ∪ F) (by simp)
  have hxhat_mem_S : xhat ∈ S := by
    exact subset_affineSpan ℝ ({xP} ∪ F) (by simp [F, hxhat_face])
  have hk_mem : k ∈ ({k} : Set (Fin m)) := by simp
  have hxhat_row : (A *ᵥ xhat) k = b k := by
    simpa [F] using (mem_active_constraint_face_iff.mp hxhat_face).1 k hk_mem
  have hF_subset_P : F ⊆ P := by
    intro x hx
    simpa [F, P] using mem_polyhedron_of_mem_active_constraint_face hx
  have hS_le_P : S ≤ affineSpan ℝ P :=
    affineSpan_mono ℝ (by
      intro x hx
      rcases hx with rfl | hxF
      · simpa [P] using hxP
      · exact hF_subset_P hxF)
  have hF_dir_eq :
      (affineSpan ℝ F).direction = D ⊓ LinearMap.ker L := by
    apply le_antisymm
    · intro v hv
      refine ⟨?_, ?_⟩
      · -- Every singleton-facet direction is an ambient direction.
        simpa [D] using (AffineSubspace.direction_le (affineSpan_mono ℝ hF_subset_P)) hv
      · change L v = 0
        rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhat_face_aff] at hv
        rcases hv with ⟨x, hxAff, rfl⟩
        have hxFace :
            x ∈ (affineSpan ℝ (active_constraint_face A b ({k} : Set (Fin m))) :
              Set (Fin n → ℝ)) := by
          simpa [F] using hxAff
        have hxRow :
            x ∈ {y : Fin n → ℝ |
              y ∈ affineSpan ℝ (polyhedron_le_set A b) ∧
                (A *ᵥ y) k = b k} := by
          rwa [affineSpan_active_constraint_face_singleton_eq_affineHull_and_row
            A b k
              (by
                have hk_not_implicit :
                    ¬ is_implicit_equality A b k := by
                  intro hk_implicit
                  have hface_eq :
                      active_constraint_face A b ({k} : Set (Fin m)) = polyhedron_le_set A b :=
                    activeConstraintFace_eq_polyhedron_of_forall_implicit
                      A b ({k} : Set (Fin m)) (by
                        intro i hi
                        have hik : i = k := by simpa using hi
                        simpa [hik] using hk_implicit)
                  exact (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.2.ne hface_eq
                exact (mem_remaining_inequality_indices_iff A b k).2 hk_not_implicit)
              hfacet] at hxFace
        calc
          L (x - xhat) = (A *ᵥ (x - xhat)) k := by
              simp [L, dotProductStrongDual_apply, Matrix.mulVec]
          _ = (A *ᵥ x) k - (A *ᵥ xhat) k := by
                simp [Matrix.mulVec_sub]
          _ = 0 := by rw [hxRow.2, hxhat_row, sub_self]
    · rintro v ⟨hvD, hvKer⟩
      have hvD' : v ∈ D := by simpa [D] using hvD
      have hvKer' : L v = 0 := by simpa [LinearMap.mem_ker] using hvKer
      rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhat_poly_aff] at hvD'
      rcases hvD' with ⟨x, hxAffP, rfl⟩
      have hxAffP' : x ∈ affineSpan ℝ P := by simpa [P] using hxAffP
      have hxRow : (A *ᵥ x) k = b k := by
        have hsub_zero : (A *ᵥ (x - xhat)) k = 0 := by
          simpa [L, dotProductStrongDual_apply, Matrix.mulVec, LinearMap.mem_ker] using hvKer'
        calc
          (A *ᵥ x) k = (A *ᵥ (x - xhat)) k + (A *ᵥ xhat) k := by
              simp [Matrix.mulVec_sub]
          _ = 0 + (A *ᵥ xhat) k := by rw [hsub_zero]
          _ = b k := by simp [hxhat_row]
      have hxFace :
          x ∈ (affineSpan ℝ F : Set (Fin n → ℝ)) := by
        have hxFace' :
            x ∈ (affineSpan ℝ (active_constraint_face A b ({k} : Set (Fin m))) :
              Set (Fin n → ℝ)) := by
          rw [affineSpan_active_constraint_face_singleton_eq_affineHull_and_row
            A b k
              (by
                have hk_not_implicit :
                    ¬ is_implicit_equality A b k := by
                  intro hk_implicit
                  have hface_eq :
                      active_constraint_face A b ({k} : Set (Fin m)) = polyhedron_le_set A b :=
                    activeConstraintFace_eq_polyhedron_of_forall_implicit
                      A b ({k} : Set (Fin m)) (by
                        intro i hi
                        have hik : i = k := by simpa using hi
                        simpa [hik] using hk_implicit)
                  exact (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.2.ne hface_eq
                exact (mem_remaining_inequality_indices_iff A b k).2 hk_not_implicit)
              hfacet]
          exact ⟨by simpa [P] using hxAffP', hxRow⟩
        simpa [F] using hxFace'
      -- Re-enter the singleton-facet direction after imposing the row-`k` equation.
      rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhat_face_aff]
      refine ⟨x, hxFace, ?_⟩
      simp [vsub_eq_sub]
  have hdiff_D : xhat - xP ∈ D := by
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxP_aff]
    refine ⟨xhat, hxhat_poly_aff, ?_⟩
    simp [vsub_eq_sub]
  let gap : ℝ := b k - (A *ᵥ xP) k
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    linarith
  let w : Fin n → ℝ := gap⁻¹ • (xhat - xP)
  have hw_D : w ∈ D := by
    dsimp [w]
    exact Submodule.smul_mem D _ hdiff_D
  have hw_eval : L w = 1 := by
    have hbase :
        L (xhat - xP) = gap := by
      calc
        L (xhat - xP) = (A *ᵥ (xhat - xP)) k := by
            simp [L, dotProductStrongDual_apply, Matrix.mulVec]
        _ = (A *ᵥ xhat) k - (A *ᵥ xP) k := by
              simp [Matrix.mulVec_sub]
        _ = gap := by
              dsimp [gap]
              rw [hxhat_row]
    -- Normalize the strict row gap so the row functional evaluates to `1`.
    calc
      L w = gap⁻¹ * gap := by
              dsimp [w]
              simp [hbase, smul_eq_mul]
      _ = 1 := by
            field_simp [ne_of_gt hgap_pos]
  have hF_dir_le_S : (affineSpan ℝ F).direction ≤ S.direction := by
    exact AffineSubspace.direction_le (affineSpan_mono ℝ (by
      intro x hx
      exact Or.inr hx))
  have hw_S : w ∈ S.direction := by
    have hdiff_S : xhat - xP ∈ S.direction := by
      simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxhat_mem_S hxP_mem_S
    dsimp [w]
    exact Submodule.smul_mem _ _ hdiff_S
  have hP_dir_le_S : D ≤ S.direction := by
    intro v hvD
    let z : Fin n → ℝ := v - (L v) • w
    have hz_D : z ∈ D := by
      dsimp [z]
      exact Submodule.sub_mem D hvD (Submodule.smul_mem D _ hw_D)
    have hz_ker : z ∈ LinearMap.ker L := by
      change L z = 0
      dsimp [z]
      calc
        L (v - (L v) • w) = L v - (L v) * L w := by
            simp [map_sub]
        _ = 0 := by rw [hw_eval]; ring
    have hz_F : z ∈ (affineSpan ℝ F).direction := by
      have hz_inf : z ∈ D ⊓ LinearMap.ker L := ⟨hz_D, hz_ker⟩
      simpa [hF_dir_eq] using hz_inf
    have hz_S : z ∈ S.direction := hF_dir_le_S hz_F
    have hsmul_S : (L v) • w ∈ S.direction := Submodule.smul_mem _ _ hw_S
    have hv_split : v = z + (L v) • w := by
      dsimp [z]
      abel
    rw [hv_split]
    exact Submodule.add_mem _ hz_S hsmul_S
  have hdir_eq : (affineSpan ℝ P).direction = S.direction := by
    refine le_antisymm hP_dir_le_S ?_
    simpa [D] using AffineSubspace.direction_le hS_le_P
  -- The strict point `xP` lies in both affine spans, so the direction equality upgrades to
  -- equality of affine subspaces.
  apply AffineSubspace.ext_of_direction_eq hdir_eq
  exact ⟨xP, hxP_aff, hxP_mem_S⟩

/-- Helper for Theorem 3.27: same-facet rows have proportional deficits on the ambient affine hull
relative to a prescribed facet row. -/
lemma sameFacetRow_sub_eq_pos_smul_on_affineHull_direct
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i a : Fin m)
    (ha : a ∈ remaining_inequality_indices A b)
    (hfacet_a :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({a} : Set (Fin m))))
    (hia_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({a} : Set (Fin m))) :
    ∃ lam : ℝ,
      0 < lam ∧
        ∀ {x : Fin n → ℝ},
          x ∈ affineSpan ℝ (polyhedron_le_set A b) →
            (A *ᵥ x) i - b i = lam * ((A *ᵥ x) a - b a) := by
  rcases exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b a ha with
    ⟨xP, hxP, hxP_lt⟩
  let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
  have hgap_a_pos : 0 < gap a := by
    dsimp [gap]
    linarith
  have hgap_i_pos : 0 < gap i := by
    have hxi_lt : (A *ᵥ xP) i < b i :=
      sameFacetRow_strict_of_eq_singletonFace A b i a hia_face hxP hxP_lt
    dsimp [gap]
    linarith
  let c : Fin n → ℝ := (gap a) • A i - (gap i) • A a
  let δ : ℝ := gap a * b i - gap i * b a
  have hface_hyper :
      active_constraint_face A b ({a} : Set (Fin m)) ⊆
        {y : Fin n → ℝ | c ⬝ᵥ y = δ} := by
    intro y hy
    -- The singleton facet already lies on the cross-multiplied gap hyperplane.
    simpa [c, δ, gap] using
      (sameFacetRow_gapHyperplane_contains_singletonFacet
        A b i a hia_face xP hy)
  have hxP_hyper : xP ∈ {y : Fin n → ℝ | c ⬝ᵥ y = δ} := by
    -- The chosen strict point satisfies the same hyperplane equation by direct algebra.
    change c ⬝ᵥ xP = δ
    dsimp [c, δ, gap]
    simp [Matrix.mulVec]
    ring
  have hunion_hyper :
      ({xP} ∪ active_constraint_face A b ({a} : Set (Fin m)) : Set (Fin n → ℝ)) ⊆
        {y : Fin n → ℝ | c ⬝ᵥ y = δ} := by
    intro y hy
    rcases hy with rfl | hy
    · exact hxP_hyper
    · exact hface_hyper hy
  have hAffHyper := affineSpan_subset_hyperplane_of_subset hunion_hyper
  let lam : ℝ := gap i / gap a
  refine ⟨lam, by dsimp [lam]; exact div_pos hgap_i_pos hgap_a_pos, ?_⟩
  intro x hxAff
  have hxUnion :
      x ∈ affineSpan ℝ ({xP} ∪ active_constraint_face A b ({a} : Set (Fin m))) := by
    rw [← ambientAffineHull_eq_affineSpan_strictPoint_union_singletonFacet A b a hfacet_a hxP hxP_lt]
    exact hxAff
  have hhyper : c ⬝ᵥ x = δ := hAffHyper hxUnion
  have hcross :
      gap a * ((A *ᵥ x) i - b i) = gap i * ((A *ᵥ x) a - b a) := by
    have hhyper' :
        gap a * (A *ᵥ x) i - gap i * (A *ᵥ x) a = gap a * b i - gap i * b a := by
      simpa [c, δ, Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, sub_mul, Finset.mul_sum,
        mul_assoc] using hhyper
    linarith
  have hgap_a_ne : gap a ≠ 0 := ne_of_gt hgap_a_pos
  -- Clearing the positive anchor gap turns the cross-multiplied identity into the desired
  -- proportional-deficit formula.
  apply mul_right_cancel₀ hgap_a_ne
  calc
    ((A *ᵥ x) i - b i) * gap a = gap a * ((A *ᵥ x) i - b i) := by ring
    _ = gap i * ((A *ᵥ x) a - b a) := hcross
    _ = ((gap i / gap a) * ((A *ᵥ x) a - b a)) * gap a := by
          field_simp [hgap_a_ne]
    _ = lam * ((A *ᵥ x) a - b a) * gap a := by rfl

/-- Helper for Theorem 3.27: normalize a same-facet row against one prescribed anchor row,
rather than against an existentially chosen same-facet row. -/
lemma sameFacetRow_eq_pos_smul_fixedAnchor_add_implicit
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i a : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (ha : a ∈ remaining_inequality_indices A b)
    (hfacet_a :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({a} : Set (Fin m))))
    (hia_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({a} : Set (Fin m))) :
    ∃ lam : ℝ, ∃ uImp : Fin m → ℝ,
      0 < lam ∧
        uImp a = 0 ∧
        (∀ r : Fin m, ¬ is_implicit_equality A b r → r ≠ a → uImp r = 0) ∧
        uImp ᵥ* A + lam • A a = A i ∧
        uImp ⬝ᵥ b + lam * b a = b i := by
  -- Route correction: the fixed-anchor normalization is now owned earlier by the cross-gap core,
  -- so the later ambient affine-hull transport block only consumes that certificate.
  exact sameFacetRow_eq_pos_smul_fixedAnchor_add_implicitCore A b i a hi ha hfacet_a hia_face

/-- Helper for Theorem 3.27: same-facet rows should satisfy the cross-multiplied gap identity on
the ambient affine hull with respect to a fixed strict point for row `k`. This needs the
singleton face of `k` to be a facet; without that premise the statement is false for empty or
redundant singleton faces. -/
lemma sameFacetRow_gapCrossMul_eq_on_affineHull
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r k : Fin m)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hrk_face :
      active_constraint_face A b ({r} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m)))
    {xP x : Fin n → ℝ}
    (hxP : xP ∈ polyhedron_le_set A b)
    (hxP_lt : (A *ᵥ xP) k < b k)
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b)) :
    let gap : Fin m → ℝ := fun s ↦ b s - (A *ᵥ xP) s
    gap k * ((A *ᵥ x) r - b r) = gap r * ((A *ᵥ x) k - b k) := by
  dsimp
  have hproper_k :
      is_proper_face (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))) :=
    is_facet_to_is_proper_face hfacet
  have hface_k_ssubset :
      active_constraint_face A b ({k} : Set (Fin m)) ⊂ polyhedron_le_set A b :=
    (is_proper_face_iff.mp hproper_k).2.2
  have hk_not_implicit : ¬ is_implicit_equality A b k := by
    intro hk_implicit
    have hface_k_eq :
        active_constraint_face A b ({k} : Set (Fin m)) = polyhedron_le_set A b :=
      activeConstraintFace_eq_polyhedron_of_forall_implicit
        A b ({k} : Set (Fin m)) (by
          intro i hi
          have hik : i = k := by simpa using hi
          simpa [hik] using hk_implicit)
    exact hface_k_ssubset.ne hface_k_eq
  have hk_remaining : k ∈ remaining_inequality_indices A b :=
    (mem_remaining_inequality_indices_iff A b k).2 hk_not_implicit
  have hr_not_implicit : ¬ is_implicit_equality A b r := by
    intro hr_implicit
    have hface_r_eq :
        active_constraint_face A b ({r} : Set (Fin m)) = polyhedron_le_set A b :=
      activeConstraintFace_eq_polyhedron_of_forall_implicit
        A b ({r} : Set (Fin m)) (by
          intro i hi
          have hir : i = r := by simpa using hi
          simpa [hir] using hr_implicit)
    have hface_k_eq :
        active_constraint_face A b ({k} : Set (Fin m)) = polyhedron_le_set A b := by
      calc
        active_constraint_face A b ({k} : Set (Fin m))
            = active_constraint_face A b ({r} : Set (Fin m)) := hrk_face.symm
        _ = polyhedron_le_set A b := hface_r_eq
    exact hface_k_ssubset.ne hface_k_eq
  have hr_remaining : r ∈ remaining_inequality_indices A b :=
    (mem_remaining_inequality_indices_iff A b r).2 hr_not_implicit
  rcases
      sameFacetRow_eq_pos_smul_fixedAnchor_add_implicit
        A b r k hr_remaining hk_remaining hfacet hrk_face with
    ⟨lam, uImp, _hlam, huImp_anchor, huImp_zero, hrow, hrhs⟩
  have hsub :
      ∀ {y : Fin n → ℝ},
        y ∈ affineSpan ℝ (polyhedron_le_set A b) →
          (A *ᵥ y) r - b r = lam * ((A *ᵥ y) k - b k) := by
    intro y hyAff
    exact
      sameFacetRow_sub_eq_smul_anchorSub_of_implicitEq
        A b r k uImp lam hk_remaining huImp_anchor huImp_zero hrow hrhs hyAff
  have hxPAff : xP ∈ affineSpan ℝ (polyhedron_le_set A b) :=
    subset_affineSpan ℝ (polyhedron_le_set A b) hxP
  have hgap :
      b r - (A *ᵥ xP) r = lam * (b k - (A *ᵥ xP) k) := by
    have hsubP :
        (A *ᵥ xP) r - b r = lam * ((A *ᵥ xP) k - b k) := hsub hxPAff
    linarith
  -- The ambient proportional-deficit identity determines both the row gaps at `xP` and the row
  -- deficits at `x`, so the cross-multiplied gap formula follows by one ring rearrangement.
  calc
    (b k - (A *ᵥ xP) k) * ((A *ᵥ x) r - b r)
        = (b k - (A *ᵥ xP) k) * (lam * ((A *ᵥ x) k - b k)) := by rw [hsub hxAff]
    _ = (lam * (b k - (A *ᵥ xP) k)) * ((A *ᵥ x) k - b k) := by ring
    _ = (b r - (A *ᵥ xP) r) * ((A *ᵥ x) k - b k) := by rw [hgap]

/-- Helper for Theorem 3.27: on the ambient affine hull, two remaining rows defining the same
singleton facet have proportional deficits with positive orientation. -/
lemma sameFacetRow_sub_eq_pos_smul_on_affineHull
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i k : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hk : k ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({k} : Set (Fin m))))
    (hik_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({k} : Set (Fin m))) :
    ∃ lam : ℝ,
      0 < lam ∧
        ∀ {x : Fin n → ℝ},
          x ∈ affineSpan ℝ (polyhedron_le_set A b) →
            (A *ᵥ x) i - b i = lam * ((A *ᵥ x) k - b k) := by
  rcases
      sameFacetRow_eq_pos_smul_fixedAnchor_add_implicit
        A b i k hi hk hfacet hik_face with
    ⟨lam, uImp, hlam, huImp_anchor, huImp_zero, hrow, hrhs⟩
  refine ⟨lam, hlam, ?_⟩
  intro x hxAff
  -- Route correction: after the fixed-anchor normalization is available, the proportional-deficit
  -- identity is exactly the existing anchor-row deficit lemma specialized to row `k`.
  exact
    sameFacetRow_sub_eq_smul_anchorSub_of_implicitEq
      A b i k uImp lam hk huImp_anchor huImp_zero hrow hrhs hxAff

/-- Helper for Theorem 3.27: on the ambient affine hull, row-`j` tightness should transport to
any remaining row that defines the same singleton facet. -/
lemma sameFacetRow_eq_on_affineHull
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (i j : Fin m)
    (hi : i ∈ remaining_inequality_indices A b)
    (hj : j ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m))))
    (hij_face :
      active_constraint_face A b ({i} : Set (Fin m)) =
        active_constraint_face A b ({j} : Set (Fin m)))
    {x : Fin n → ℝ}
    (hxAff : x ∈ affineSpan ℝ (polyhedron_le_set A b))
    (hxj : (A *ᵥ x) j = b j) :
    (A *ᵥ x) i = b i := by
  -- Route correction: the ambient same-face transport is owned by the earlier bridge theorem that
  -- the auxiliary-system proof also consumes.
  exact sameFacetRow_eq_on_affineHullCore A b i j hi hj hfacet hij_face hxAff hxj

/-- Helper for Theorem 3.27: if a remaining singleton active face is a facet, then it should have
codimension one in the ambient affine span. -/
lemma finrank_direction_affineSpan_add_one_eq_of_is_facet_singletonActiveConstraintFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m)
    (hj : j ∈ remaining_inequality_indices A b)
    (hfacet :
      is_facet (polyhedron_le_set A b)
        (active_constraint_face A b ({j} : Set (Fin m)))) :
    Module.finrank ℝ
        (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))).direction + 1 =
    Module.finrank ℝ
        (affineSpan ℝ (polyhedron_le_set A b)).direction := by
  let F : Set (Fin n → ℝ) := active_constraint_face A b ({j} : Set (Fin m))
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  let D : Submodule ℝ (Fin n → ℝ) := (affineSpan ℝ P).direction
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductStrongDual (A j)).toLinearMap
  rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.1 with ⟨xhat, hxhat_face⟩
  have hxhat_poly : xhat ∈ P := by
    simpa [F, P] using mem_polyhedron_of_mem_active_constraint_face hxhat_face
  have hxhat_face_aff : xhat ∈ affineSpan ℝ F := subset_affineSpan ℝ F hxhat_face
  have hxhat_poly_aff : xhat ∈ affineSpan ℝ P := subset_affineSpan ℝ P hxhat_poly
  have hj_mem : j ∈ ({j} : Set (Fin m)) := by simp
  have hxhat_row : (A *ᵥ xhat) j = b j := by
    simpa [F] using (mem_active_constraint_face_iff.mp hxhat_face).1 j hj_mem
  have hF_subset_P : F ⊆ P := by
    intro x hx
    simpa [F, P] using mem_polyhedron_of_mem_active_constraint_face hx
  have hdir_eq :
      (affineSpan ℝ F).direction = D ⊓ LinearMap.ker L := by
    apply le_antisymm
    · intro v hv
      refine ⟨?_, ?_⟩
      · -- Any face direction is automatically an ambient direction.
        simpa [D] using (AffineSubspace.direction_le (affineSpan_mono ℝ hF_subset_P)) hv
      · change L v = 0
        rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhat_face_aff] at hv
        rcases hv with ⟨x, hxAff, rfl⟩
        have hxAffF :
            x ∈ (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m))) :
              Set (Fin n → ℝ)) := by
          simpa [F] using hxAff
        have hxPair :
            x ∈ {y : Fin n → ℝ |
              y ∈ affineSpan ℝ (polyhedron_le_set A b) ∧
                (A *ᵥ y) j = b j} := by
          rwa [affineSpan_active_constraint_face_singleton_eq_affineHull_and_row
            A b j hj hfacet] at hxAffF
        calc
          L (x - xhat) = (A *ᵥ (x - xhat)) j := by
              simp [L, dotProductStrongDual_apply, Matrix.mulVec]
          _ = (A *ᵥ x) j - (A *ᵥ xhat) j := by
                simp [Matrix.mulVec_sub]
          _ = 0 := by rw [hxPair.2, hxhat_row, sub_self]
    · rintro v ⟨hvD, hvKer⟩
      have hvD' : v ∈ D := by simpa [D] using hvD
      have hvKer' : L v = 0 := by simpa [L] using hvKer
      rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhat_poly_aff] at hvD'
      rcases hvD' with ⟨x, hxAffP, rfl⟩
      have hxAffP' : x ∈ affineSpan ℝ P := by simpa [P] using hxAffP
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
        have hxFace :
            x ∈ (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m))) :
              Set (Fin n → ℝ)) := by
          rw [affineSpan_active_constraint_face_singleton_eq_affineHull_and_row A b j hj hfacet]
          exact ⟨by simpa [P] using hxAffP', hx_row⟩
        simpa [F] using hxFace
      -- Translating back from `xhat` re-enters the face direction.
      rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxhat_face_aff]
      refine ⟨x, hx_face_aff, ?_⟩
      simp [vsub_eq_sub]
  rcases exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b j hj with
    ⟨xP, hxP, hxP_lt⟩
  have hxP_row_lt : (A *ᵥ xP) j < b j := hxP_lt
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
    -- Normalizing the row gap produces the vector on which `L` evaluates to `1`.
    calc
      L w = gap⁻¹ * gap := by
              dsimp [w]
              simp [hbase, smul_eq_mul]
      _ = 1 := by
            field_simp [ne_of_gt hgap_pos]
  have hcodim :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D :=
    finrank_inf_ker_add_one_of_eval_one D L hwD hw_eval
  -- The direction equality converts the kernel-cut computation into the facet codimension formula.
  calc
    Module.finrank ℝ (affineSpan ℝ F).direction + 1
        = Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 := by rw [hdir_eq]
    _ = Module.finrank ℝ ↥D := hcodim
    _ = Module.finrank ℝ (affineSpan ℝ P).direction := by rfl

/-- Theorem 3.27 (2) (Characterization of the Facets). If `polyhedron_le_set A b` is nonempty and
the rows that are not implicit equalities form a minimal inequality representation of it, then its
facets are exactly the faces obtained by activating one non-implicit row. -/
theorem facets_eq_range_active_constraint_face_singleton_of_minimal_representation
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : (polyhedron_le_set A b).Nonempty)
    (hminimal :
      ∀ i : Fin m, ¬ is_implicit_equality A b i → is_irredundant_row A b i) :
    {F : Set (Fin n → ℝ) | is_facet (polyhedron_le_set A b) F} =
      Set.range
        (fun i : {i // i ∈ remaining_inequality_indices A b} ↦
          active_constraint_face A b ({i.1} : Set (Fin m))) := by
  ext F
  constructor
  · intro hF_facet
    rcases
        exists_eq_active_constraint_face_singleton_of_is_facet
          A b h_nonempty F hF_facet with
      ⟨j, hjF⟩
    exact Set.mem_range.mpr ⟨j, hjF.symm⟩
  · rintro ⟨j, rfl⟩
    have hj_not_implicit : ¬ is_implicit_equality A b j.1 :=
      (mem_remaining_inequality_indices_iff A b j.1).1 j.2
    have hj_irredundant : is_irredundant_row A b j.1 :=
      hminimal j.1 hj_not_implicit
    obtain ⟨xhat, hxhat_face, _⟩ :=
      exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
        A b j.1 h_nonempty hj_irredundant
    have hsingleton_nonempty :
        (active_constraint_face A b ({j.1} : Set (Fin m))).Nonempty := ⟨xhat, hxhat_face⟩
    have hsingleton_codim :
        Module.finrank ℝ
            (affineSpan ℝ (active_constraint_face A b ({j.1} : Set (Fin m)))).direction + 1 =
          Module.finrank ℝ
            (affineSpan ℝ (polyhedron_le_set A b)).direction :=
      finrank_direction_affineSpan_add_one_eq_of_irredundant_singleton
        A b j.1 j.2 hj_irredundant
    -- Under minimality, Lemma 3.26 gives codimension one for each remaining singleton face, and
    -- the exposed codimension-one criterion upgrades that face to a facet.
    exact
      isFacet_of_nonempty_finrank_direction_affineSpan_add_one_eq
        A b
        (active_constraint_face A b ({j.1} : Set (Fin m)))
        (active_constraint_face_isExposed A b ({j.1} : Set (Fin m)))
        hsingleton_nonempty
        hsingleton_codim

/-- Theorem 3.27 (3) (Characterization of the Facets). For a nonempty polyhedron
`polyhedron_le_set A b` given by a minimal representation, the number of non-implicit inequality
rows equals the number of its facets. -/
theorem ncard_facets_eq_card_nonimplicit_rows_of_minimal_representation
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : (polyhedron_le_set A b).Nonempty)
    (hminimal :
      ∀ i : Fin m, ¬ is_implicit_equality A b i → is_irredundant_row A b i) :
    {F : Set (Fin n → ℝ) | is_facet (polyhedron_le_set A b) F}.ncard =
      Fintype.card {i // i ∈ remaining_inequality_indices A b} := by
  have hfacets_eq :
      {F : Set (Fin n → ℝ) | is_facet (polyhedron_le_set A b) F} =
        Set.range
          (fun i : {i // i ∈ remaining_inequality_indices A b} ↦
            active_constraint_face A b ({i.1} : Set (Fin m))) :=
    facets_eq_range_active_constraint_face_singleton_of_minimal_representation
      A b h_nonempty hminimal
  -- Part (ii) identifies the facet set with the range of an injective map from the remaining rows.
  calc
    {F : Set (Fin n → ℝ) | is_facet (polyhedron_le_set A b) F}.ncard
        = (Set.range
            fun i : {i // i ∈ remaining_inequality_indices A b} ↦
              active_constraint_face A b ({i.1} : Set (Fin m))).ncard := by
              rw [hfacets_eq]
    _ = Fintype.card {i // i ∈ remaining_inequality_indices A b} := by
          simpa [Nat.card_eq_fintype_card] using
            Set.ncard_range_of_injective
              (activeConstraintFaceSingleton_injective_of_minimalRepresentation A b hminimal)

/-- Theorem 3.27 (4) (Characterization of the Facets). For a nonempty polyhedron
`polyhedron_le_set A b` and a face `F` of it, expressed here by the canonical predicate
`IsExposed`, being a facet is equivalent to being nonempty and having codimension one in the
affine span of the polyhedron. -/
theorem is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (h_nonempty : (polyhedron_le_set A b).Nonempty)
    (F : Set (Fin n → ℝ))
    (hF_face : IsExposed ℝ (polyhedron_le_set A b) F) :
    is_facet (polyhedron_le_set A b) F ↔
      F.Nonempty ∧
        Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
          Module.finrank ℝ
            (affineSpan ℝ (polyhedron_le_set A b)).direction := by
  constructor
  · intro hF_facet
    have hF_nonempty : F.Nonempty :=
      (is_proper_face_iff.mp (is_facet_to_is_proper_face hF_facet)).2.1
    rcases
        exists_eq_active_constraint_face_singleton_of_is_facet
          A b h_nonempty F hF_facet with
      ⟨j, hjF⟩
    have hj_facet :
        is_facet (polyhedron_le_set A b)
          (active_constraint_face A b ({j.1} : Set (Fin m))) := by
      simpa [hjF] using hF_facet
    have hj_codim :
        Module.finrank ℝ
            (affineSpan ℝ (active_constraint_face A b ({j.1} : Set (Fin m)))).direction + 1 =
          Module.finrank ℝ
            (affineSpan ℝ (polyhedron_le_set A b)).direction :=
      finrank_direction_affineSpan_add_one_eq_of_is_facet_singletonActiveConstraintFace
        A b j.1 j.2 hj_facet
    -- Part (i) identifies the facet with one singleton active face, so the singleton codimension
    -- statement is exactly the codimension statement for `F`.
    refine ⟨hF_nonempty, ?_⟩
    rw [hjF]
    exact hj_codim
  · rintro ⟨hF_nonempty, hF_codim⟩
    -- The reverse implication is already the codimension-one exposed-face criterion proved above.
    exact
      isFacet_of_nonempty_finrank_direction_affineSpan_add_one_eq
        A b F hF_face hF_nonempty hF_codim

end Theorem_3_27
