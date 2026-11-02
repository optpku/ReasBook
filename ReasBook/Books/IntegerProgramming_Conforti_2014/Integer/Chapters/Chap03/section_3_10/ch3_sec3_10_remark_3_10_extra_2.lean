import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_definition_3_7_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_1

open scoped Matrix

-- This remark is source-facing, but its owner abstractions already live earlier in Chapter 3:
-- `is_polyhedral_cone`, `linealitySpace`, and `IsMinimalFaceOf`. The lemmas below are only the
-- homogeneous-matrix bridge API needed for this remark.

/-- Helper for Remark 3.10-extra-2: the origin belongs to every homogeneous matrix cone. -/
lemma zero_mem_matrix_cone
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {C : Set (Fin n → ℝ)}
    (hA : C = polyhedron_le_set A (0 : Fin m → ℝ)) :
    (0 : Fin n → ℝ) ∈ C := by
  -- Rewriting the cone as the homogeneous solution set reduces the claim to `A *ᵥ 0 = 0`.
  rw [hA]
  change A *ᵥ (0 : Fin n → ℝ) ≤ 0
  simp

/-- Helper for Remark 3.10-extra-2: homogeneous matrix cones are closed under nonnegative
scaling. -/
lemma smul_mem_matrix_cone
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {C : Set (Fin n → ℝ)}
    (hA : C = polyhedron_le_set A (0 : Fin m → ℝ))
    {x : Fin n → ℝ} (hx : x ∈ C) {a : ℝ} (ha : 0 ≤ a) :
    a • x ∈ C := by
  -- Each defining inequality scales by the same nonnegative factor.
  rw [hA] at hx ⊢
  change A *ᵥ (a • x) ≤ 0
  have hscaled : a • (A *ᵥ x) ≤ a • (0 : Fin _ → ℝ) :=
    smul_le_smul_of_nonneg_left hx ha
  simpa [Matrix.mulVec_smul] using hscaled

/-- Helper for Remark 3.10-extra-2: in a homogeneous matrix cone, the lineality space is the
kernel of the defining matrix. -/
lemma mem_linealitySpace_iff_mulVec_eq_zero
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {C : Set (Fin n → ℝ)} {r : Fin n → ℝ}
    (hA : C = polyhedron_le_set A (0 : Fin m → ℝ)) :
    r ∈ linealitySpace C ↔ A *ᵥ r = 0 := by
  rw [mem_linealitySpace_iff]
  constructor
  · intro hr
    have h0C : (0 : Fin n → ℝ) ∈ C := zero_mem_matrix_cone hA
    have hrC : r ∈ C := by
      simpa using hr h0C 1
    have hnegC : -r ∈ C := by
      simpa using hr h0C (-1)
    rw [hA] at hrC hnegC
    ext i
    have hle : (A *ᵥ r) i ≤ 0 := hrC i
    have hnegle : -((A *ᵥ r) i) ≤ 0 := by
      simpa [Matrix.mulVec_neg] using hnegC i
    have hge : 0 ≤ (A *ᵥ r) i := by
      linarith
    exact le_antisymm hle hge
  · intro hr x hx a
    -- The equality `A *ᵥ r = 0` shows that every translate by `a • r` stays feasible.
    rw [hA] at hx ⊢
    change A *ᵥ (x + a • r) ≤ 0
    have htranslate : A *ᵥ (x + a • r) = A *ᵥ x := by
      calc
        A *ᵥ (x + a • r) = A *ᵥ x + A *ᵥ (a • r) := by
          rw [Matrix.mulVec_add]
        _ = A *ᵥ x + a • (A *ᵥ r) := by
          rw [Matrix.mulVec_smul]
        _ = A *ᵥ x := by
          rw [hr, smul_zero, add_zero]
    change A *ᵥ (x + a • r) ≤ 0
    rw [htranslate]
    exact hx

/-- Helper for Remark 3.10-extra-2: the lineality space of a homogeneous matrix cone is
nonempty. -/
lemma linealitySpace_nonempty_of_matrix_cone
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {C : Set (Fin n → ℝ)}
    (hA : C = polyhedron_le_set A (0 : Fin m → ℝ)) :
    (linealitySpace C).Nonempty := by
  -- The zero vector lies in the kernel of `A`, hence in the lineality space.
  refine ⟨0, ?_⟩
  rw [mem_linealitySpace_iff_mulVec_eq_zero hA]
  simp

/-- Helper for Remark 3.10-extra-2: the lineality space is an extreme face of a homogeneous
matrix cone. -/
lemma linealitySpace_isExtreme_of_matrix_cone
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {C : Set (Fin n → ℝ)}
    (hA : C = polyhedron_le_set A (0 : Fin m → ℝ)) :
    IsExtreme ℝ C (linealitySpace C) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    -- A lineality direction satisfies `A *ᵥ r = 0`, hence it already belongs to the cone.
    rw [mem_linealitySpace_iff_mulVec_eq_zero hA] at hr
    rw [hA]
    change A *ᵥ r ≤ 0
    simp [hr]
  · intro x hx y hy z hz hzxy
    -- Route correction: prove extremality rowwise by pushing the open-segment identity through
    -- `A *ᵥ` and forcing both endpoint images to vanish.
    rw [mem_openSegment_iff_div] at hzxy
    rcases hzxy with ⟨a, b, ha, hb, hzxy⟩
    rw [hA] at hx hy
    rw [mem_linealitySpace_iff_mulVec_eq_zero hA] at hz
    rw [mem_linealitySpace_iff_mulVec_eq_zero hA]
    ext i
    have hcoeff_a : 0 < a / (a + b) := by positivity
    have hcoeff_b : 0 < b / (a + b) := by positivity
    have hmul :
        A *ᵥ z = (a / (a + b)) • (A *ᵥ x) + (b / (a + b)) • (A *ᵥ y) := by
      calc
        A *ᵥ z = A *ᵥ ((a / (a + b)) • x + (b / (a + b)) • y) := by
          rw [← hzxy]
        _ = A *ᵥ ((a / (a + b)) • x) + A *ᵥ ((b / (a + b)) • y) := by
          rw [Matrix.mulVec_add]
        _ = (a / (a + b)) • (A *ᵥ x) + A *ᵥ ((b / (a + b)) • y) := by
          rw [Matrix.mulVec_smul]
        _ = (a / (a + b)) • (A *ᵥ x) + (b / (a + b)) • (A *ᵥ y) := by
          rw [Matrix.mulVec_smul]
    have hrow :
        0 = (a / (a + b)) * (A *ᵥ x) i + (b / (a + b)) * (A *ᵥ y) i := by
      have hrow' := congrArg (fun v : Fin m → ℝ ↦ v i) hmul
      simpa [hz, Pi.smul_apply] using hrow'
    have hx_i : (A *ᵥ x) i ≤ 0 := hx i
    have hy_i : (A *ᵥ y) i ≤ 0 := hy i
    have hy_term_nonpos : (b / (a + b)) * (A *ᵥ y) i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoeff_b.le hy_i
    have hleft_nonneg : 0 ≤ (a / (a + b)) * (A *ᵥ x) i := by
      linarith
    have hx_nonneg : 0 ≤ (A *ᵥ x) i := by
      exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hleft_nonneg) hcoeff_a
    exact le_antisymm hx_i hx_nonneg

/-- Helper for Remark 3.10-extra-2: every nonempty extreme face of a homogeneous matrix cone
contains the origin. -/
lemma zero_mem_of_nonempty_extreme_face_of_matrix_cone
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {C G : Set (Fin n → ℝ)}
    (hA : C = polyhedron_le_set A (0 : Fin m → ℝ))
    (hGne : G.Nonempty) (hG : IsExtreme ℝ C G) :
    (0 : Fin n → ℝ) ∈ G := by
  rcases hGne with ⟨g, hgG⟩
  -- Put `g` on the open segment from `0` to `2 • g` and use extremality to recover `0 ∈ G`.
  have h0C : (0 : Fin n → ℝ) ∈ C := zero_mem_matrix_cone hA
  have hgC : g ∈ C := hG.subset hgG
  have h2gC : (2 : ℝ) • g ∈ C := smul_mem_matrix_cone hA hgC (by norm_num)
  have hsegment : g ∈ openSegment ℝ (0 : Fin n → ℝ) ((2 : ℝ) • g) := by
    simpa [two_smul] using (mem_openSegment_sub_add g g)
  exact hG.left_mem_of_mem_openSegment h0C h2gC hgG hsegment

/-- Helper for Remark 3.10-extra-2: every nonempty extreme face of a homogeneous matrix cone
contains the lineality space. -/
lemma linealitySpace_subset_of_nonempty_extreme_face
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {C G : Set (Fin n → ℝ)}
    (hA : C = polyhedron_le_set A (0 : Fin m → ℝ))
    (hGne : G.Nonempty) (hG : IsExtreme ℝ C G) :
    linealitySpace C ⊆ G := by
  intro r hr
  -- Once `0 ∈ G`, the midpoint identity `0 ∈ openSegment (-r) r` forces `r ∈ G`.
  have hzeroG : (0 : Fin n → ℝ) ∈ G :=
    zero_mem_of_nonempty_extreme_face_of_matrix_cone hA hGne hG
  rw [mem_linealitySpace_iff_mulVec_eq_zero hA] at hr
  have hrC : r ∈ C := by
    rw [hA]
    change A *ᵥ r ≤ 0
    simp [hr]
  have hneg : A *ᵥ (-r) = 0 := by
    simp [Matrix.mulVec_neg, hr]
  have hnegC : -r ∈ C := by
    rw [hA]
    change A *ᵥ (-r) ≤ 0
    simp [hneg]
  have hsegment : (0 : Fin n → ℝ) ∈ openSegment ℝ (-r) r := by
    simpa using (mem_openSegment_sub_add (0 : Fin n → ℝ) r)
  exact hG.right_mem_of_mem_openSegment hnegC hrC hzeroG hsegment

/-- Remark 3.10-extra-2 (1). For any polyhedral cone `C ⊆ ℝ^n`, its lineality space is a minimal
face of `C`. -/
theorem polyhedral_cone_linealitySpace_isMinimalFace
    {n : ℕ} {C : Set (Fin n → ℝ)} (hC : is_polyhedral_cone C) :
    IsMinimalFaceOf ℝ C (linealitySpace C) := by
  rcases (is_polyhedral_cone_iff.mp hC) with ⟨m, A, hA⟩
  -- The matrix presentation supplies nonemptiness, extremality, and the minimality inclusion.
  rw [isMinimalFaceOf_iff]
  refine ⟨linealitySpace_nonempty_of_matrix_cone hA, linealitySpace_isExtreme_of_matrix_cone hA, ?_⟩
  intro G hGne hG _hsubset
  exact linealitySpace_subset_of_nonempty_extreme_face hA hGne hG

/-- Remark 3.10-extra-2 (2). If `F` is a minimal face of a polyhedral cone `C ⊆ ℝ^n`, then
`F` is exactly the lineality space of `C`. -/
theorem polyhedral_cone_minimalFace_eq_linealitySpace
    {n : ℕ} {C F : Set (Fin n → ℝ)} (hC : is_polyhedral_cone C) (hF : IsMinimalFaceOf ℝ C F) :
    F = linealitySpace C := by
  have hLinealityMinimal : IsMinimalFaceOf ℝ C (linealitySpace C) :=
    polyhedral_cone_linealitySpace_isMinimalFace hC
  rcases (is_polyhedral_cone_iff.mp hC) with ⟨m, A, hA⟩
  -- First, every nonempty extreme face contains the lineality space.
  have hlineality_subset : linealitySpace C ⊆ F :=
    linealitySpace_subset_of_nonempty_extreme_face hA hF.nonempty hF.isExtreme
  -- Then minimality of `F` forces the reverse inclusion against
  -- the minimal face `linealitySpace C`.
  have hF_subset : F ⊆ linealitySpace C := by
    exact IsMinimalFaceOf.minimal ℝ hF
      hLinealityMinimal.nonempty hLinealityMinimal.isExtreme hlineality_subset
  exact Set.Subset.antisymm hF_subset hlineality_subset
