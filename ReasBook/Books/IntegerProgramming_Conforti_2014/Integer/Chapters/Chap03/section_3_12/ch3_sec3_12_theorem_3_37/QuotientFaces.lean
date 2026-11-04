/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_33
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_theorem_3_35
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.PointedCore
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.Recession

open scoped BigOperators Matrix Pointwise

section QuotientFacesSupport

variable {n : ℕ}

/-- Helper for Theorem 3.37: the common kernel of `n - 1` independent rows that annihilate a
nonzero vector is the line spanned by that vector. -/
lemma selectedRowsZero_mem_spanSingleton
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    {d z : Fin n → ℝ}
    (hd_ne : d ≠ 0)
    (I : Fin (n - 1) ↪ Fin m)
    (hI_active : ∀ i : Fin (n - 1), (A *ᵥ d) (I i) = 0)
    (hI_independent : LinearIndependent ℝ (fun i : Fin (n - 1) ↦ A (I i)))
    (hz_active : ∀ i : Fin (n - 1), (A *ᵥ z) (I i) = 0) :
    z ∈ Submodule.span ℝ ({d} : Set (Fin n → ℝ)) := by
  have hn_pos : 0 < n := by
    by_contra hn
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    apply hd_ne
    ext i
    exact Fin.elim0 i
  let B : Matrix (Fin (n - 1)) (Fin n) ℝ := fun i j ↦ A (I i) j
  have hB_rows : LinearIndependent ℝ B.row := by
    simpa [B, Matrix.row] using hI_independent
  have hB_rank : B.rank = n - 1 := by
    simpa [B] using LinearIndependent.rank_matrix hB_rows
  have hker_finrank : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 1 := by
    calc
      Module.finrank ℝ (LinearMap.ker B.mulVecLin) = n - B.rank := by
        simpa using finrank_matrix_kernel_eq_ambient_sub_rank B
      _ = n - (n - 1) := by rw [hB_rank]
      _ = 1 := by omega
  have hd_ker : d ∈ LinearMap.ker B.mulVecLin := by
    change B *ᵥ d = 0
    ext i
    simpa [B, Matrix.mulVec] using hI_active i
  have hz_ker : z ∈ LinearMap.ker B.mulVecLin := by
    change B *ᵥ z = 0
    ext i
    simpa [B, Matrix.mulVec] using hz_active i
  have hd_sub_ne : (⟨d, hd_ker⟩ : LinearMap.ker B.mulVecLin) ≠ 0 := by
    intro hzero
    exact hd_ne (congrArg Subtype.val hzero)
  obtain ⟨μ, hμ⟩ :=
    exists_smul_eq_of_finrank_eq_one
      (V := LinearMap.ker B.mulVecLin) hker_finrank
      (x := ⟨d, hd_ker⟩) hd_sub_ne ⟨z, hz_ker⟩
  exact Submodule.mem_span_singleton.mpr ⟨μ, by simpa using congrArg Subtype.val hμ⟩

/-- Helper for Theorem 3.37: every extreme ray of a pointed polyhedral cone is an exposed
face. -/
lemma extremeRay_isExposed_of_polyhedral_pointed
    (C : Set (Fin n → ℝ))
    (hC_polyhedral : is_polyhedral_cone C)
    (hC_pointed : is_pointed C)
    {d : Fin n → ℝ}
    (hd_extreme : IsExtremeRayOfCone C d) :
    IsExposed ℝ C (ray d) := by
  rcases is_polyhedral_cone_iff.mp hC_polyhedral with ⟨m, A, hC_eq⟩
  rw [hC_eq] at hC_pointed hd_extreme ⊢
  have hd_ne : d ≠ 0 := extremeRay_ne_zero hd_extreme
  have hd_mem : d ∈ matrix_polyhedral_cone A := by
    exact (isExtremeRayOfCone_iff.mp hd_extreme).isExtreme.subset
      (PointedCone.subset_hull (by simp))
  obtain ⟨I, hI_active, hI_independent⟩ :=
    (matrix_polyhedral_cone_extreme_ray_iff_exists_active_linearlyIndependent_rows
      A hC_pointed hd_mem hd_ne).mp hd_extreme
  let F : Set (Fin n → ℝ) := active_constraint_face A 0 (Set.range I)
  have hF_eq : F = ray d := by
    apply Set.Subset.antisymm
    · intro z hzF
      have hz_mem : z ∈ matrix_polyhedral_cone A :=
        mem_polyhedron_of_mem_active_constraint_face hzF
      have hz_active : ∀ i : Fin (n - 1), (A *ᵥ z) (I i) = 0 := by
        intro i
        exact (mem_active_constraint_face_iff.mp hzF).1 (I i) ⟨i, rfl⟩
      have hz_span :=
        selectedRowsZero_mem_spanSingleton A hd_ne I hI_active hI_independent hz_active
      rcases Submodule.mem_span_singleton.mp hz_span with ⟨μ, rfl⟩
      have hμ_nonneg : 0 ≤ μ := by
        by_contra hμ
        have hμ_neg : μ < 0 := lt_of_not_ge hμ
        have hnegd_mem : -d ∈ matrix_polyhedral_cone A := by
          have hscaled :=
            matrix_polyhedral_cone_nonneg_smul_mem A hz_mem
              (inv_nonneg.mpr (neg_nonneg.mpr hμ_neg.le))
          have hscale : (-μ)⁻¹ • (μ • d) = -d := by
            rw [smul_smul]
            have hμ_ne : μ ≠ 0 := hμ_neg.ne
            rw [inv_neg, neg_mul, inv_mul_cancel₀ hμ_ne, neg_one_smul]
          rwa [hscale] at hscaled
        have hd_lineality : d ∈ linealitySpace (matrix_polyhedral_cone A) :=
          mem_linealitySpace_of_mem_cone_and_neg
            ⟨matrix_polyhedral_cone_pointedCone A, rfl⟩ hd_mem hnegd_mem
        exact hd_ne ((is_pointed_iff_eq_zero_of_mem_linealitySpace.mp hC_pointed) d hd_lineality)
      exact mem_ray_iff.mpr ⟨μ, hμ_nonneg, rfl⟩
    · intro z hz
      rcases mem_ray_iff.mp hz with ⟨μ, hμ, rfl⟩
      apply mem_active_constraint_face_iff.mpr
      constructor
      · intro j hj
        rcases hj with ⟨i, rfl⟩
        simp [Matrix.mulVec_smul, hI_active i]
      · intro j _
        exact (matrix_polyhedral_cone_nonneg_smul_mem A hd_mem hμ) j
  rw [← hF_eq]
  exact active_constraint_face_isExposed A 0 (Set.range I)

/-- Helper for Theorem 3.37: the fiber in `P` over an extreme point of the quotient by lineality
is a minimal face of `P`. -/
lemma linealityQuotientExtremePointFiber_isMinimalFace
    (P : Set (Fin n → ℝ))
    {q : Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ linealitySubmodule P)) → ℝ}
    (hq : q ∈ (linealityQuotientCoordinateMap P '' P).extremePoints ℝ) :
    IsMinimalFaceOf ℝ P
      (P ∩ linealityQuotientCoordinateMap P ⁻¹' ({q} : Set _)) := by
  let π := linealityQuotientCoordinateMap P
  have hq_image : q ∈ π '' P := extremePoints_subset hq
  rcases hq_image with ⟨p, hpP, hpq⟩
  rw [isMinimalFaceOf_iff]
  refine ⟨⟨p, hpP, by simpa [π, hpq]⟩, ?_, ?_⟩
  · refine
      { subset := Set.inter_subset_left
        left_mem_of_mem_openSegment := ?_ }
    intro x hxP y hyP z hzF hz_open
    have hzq : π z = q := by simpa [π] using hzF.2
    rcases hz_open with ⟨a, b, ha, hb, hab, hz⟩
    have hq_open : q ∈ openSegment ℝ (π x) (π y) := by
      refine ⟨a, b, ha, hb, hab, ?_⟩
      calc
        a • π x + b • π y = π (a • x + b • y) := by simp [π]
        _ = π z := by rw [hz]
        _ = q := hzq
    have hπx : π x = q :=
      (mem_extremePoints_iff_left.mp hq).2 (π x) ⟨x, hxP, rfl⟩
        (π y) ⟨y, hyP, rfl⟩ hq_open
    exact ⟨hxP, by simpa [π, hπx]⟩
  · intro G hG_nonempty hG_extreme hGF
    obtain ⟨g, hgG⟩ := hG_nonempty
    have hgF := hGF hgG
    intro r hrF
    have hmaps : π r = π g := by
      have hrq : π r = q := by simpa [π] using hrF.2
      have hgq : π g = q := by simpa [π] using hgF.2
      exact hrq.trans hgq.symm
    have hdiff_ker : r - g ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker]
      rw [LinearMap.map_sub, hmaps, sub_self]
    have hdiff_lineality : r - g ∈ linealitySpace P := by
      rw [linealityQuotientCoordinateMap_ker P] at hdiff_ker
      exact mem_linealitySubmodule_iff.mp hdiff_ker
    have hmirror : g - (r - g) ∈ P := by
      rw [mem_linealitySpace_iff] at hdiff_lineality
      have hmirror' := hdiff_lineality hgF.1 (-1)
      simpa only [neg_one_smul, sub_eq_add_neg] using hmirror'
    have hrightP : g + (r - g) ∈ P := by
      convert hrF.1 using 1 <;> abel
    have hsegment : g ∈ openSegment ℝ (g - (r - g)) (g + (r - g)) :=
      mem_openSegment_sub_add g (r - g)
    have hright : g + (r - g) ∈ G :=
      hG_extreme.right_mem_of_mem_openSegment hmirror hrightP hgG hsegment
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hright

/-- Helper for Theorem 3.37: the inverse image of a quotient extreme ray is an exposed
recession face whose direction has lineality-successor dimension. -/
lemma linealityQuotientExtremeRayFiber_isExposed_finrank
    (P : Set (Fin n → ℝ))
    (hImage_polyhedral :
      is_polyhedral_cone
        (linealityQuotientCoordinateMap P '' recessionCone P))
    (hImage_pointed :
      is_pointed (linealityQuotientCoordinateMap P '' recessionCone P))
    {d : Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ linealitySubmodule P)) → ℝ}
    (hd_extreme :
      IsExtremeRayOfCone
        (linealityQuotientCoordinateMap P '' recessionCone P) d) :
    IsExposed ℝ (recessionCone P)
        (recessionCone P ∩ linealityQuotientCoordinateMap P ⁻¹' ray d) ∧
      Module.finrank ℝ
          (affineSpan ℝ
            (recessionCone P ∩ linealityQuotientCoordinateMap P ⁻¹' ray d)).direction =
        Module.finrank ℝ (linealitySubmodule P) + 1 := by
  let π := linealityQuotientCoordinateMap P
  let K : Set (Fin n → ℝ) := recessionCone P
  let C : Set (Fin (Module.finrank ℝ ((Fin n → ℝ) ⧸ linealitySubmodule P)) → ℝ) := π '' K
  let R : Set (Fin n → ℝ) := K ∩ π ⁻¹' ray d
  have hRay_exposed : IsExposed ℝ C (ray d) :=
    extremeRay_isExposed_of_polyhedral_pointed C hImage_polyhedral hImage_pointed hd_extreme
  have hRay_nonempty : (ray d).Nonempty := ⟨0, ray_zero_mem⟩
  obtain ⟨l, hl⟩ := hRay_exposed hRay_nonempty
  have hR_exposed : IsExposed ℝ K R := by
    intro _
    let pulled : StrongDual ℝ (Fin n → ℝ) :=
      l.comp (LinearMap.toContinuousLinearMap π)
    refine ⟨pulled, ?_⟩
    ext x
    constructor
    · intro hx
      have hxRay : π x ∈ ray d := hx.2
      have hxMax : π x ∈ {q ∈ C | ∀ q' ∈ C, l q' ≤ l q} := by
        rw [← hl]
        exact hxRay
      refine ⟨hx.1, ?_⟩
      intro y hyK
      exact hxMax.2 (π y) ⟨y, hyK, rfl⟩
    · intro hx
      refine ⟨hx.1, ?_⟩
      rw [hl]
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      intro q hqC
      rcases hqC with ⟨y, hyK, rfl⟩
      exact hx.2 y hyK
  have hd_mem : d ∈ C :=
    (isExtremeRayOfCone_iff.mp hd_extreme).isExtreme.subset
      (PointedCone.subset_hull (by simp))
  rcases hd_mem with ⟨u, huK, hu_map⟩
  have hd_ne : d ≠ 0 := extremeRay_ne_zero hd_extreme
  have hu_not_lineality : u ∉ linealitySubmodule P := by
    intro huL
    have huKer : u ∈ LinearMap.ker π := by
      rw [linealityQuotientCoordinateMap_ker P]
      exact huL
    have huZero : π u = 0 := by simpa [LinearMap.mem_ker] using huKer
    exact hd_ne (hu_map ▸ huZero)
  have hzeroR : (0 : Fin n → ℝ) ∈ R := by
    refine ⟨zero_mem_recessionCone, ?_⟩
    change π 0 ∈ ray d
    simpa using (ray_zero_mem : (0 : _) ∈ ray d)
  have huR : u ∈ R := by
    refine ⟨huK, ?_⟩
    change π u ∈ ray d
    rw [hu_map]
    exact mem_ray_iff.mpr ⟨1, zero_le_one, by simp⟩
  have hlineality_subset_R : (linealitySubmodule P : Set (Fin n → ℝ)) ⊆ R := by
    intro z hzL
    have hzRec : z ∈ recessionCone P := by
      have hzLin : z ∈ linealitySpace P := mem_linealitySubmodule_iff.mp hzL
      rw [linealitySpace_eq_recessionCone_inter_neg] at hzLin
      exact hzLin.1
    have hzKer : z ∈ LinearMap.ker π := by
      rw [linealityQuotientCoordinateMap_ker P]
      exact hzL
    refine ⟨hzRec, ?_⟩
    change π z ∈ ray d
    have hzZero : π z = 0 := by simpa [LinearMap.mem_ker] using hzKer
    simpa [hzZero] using (ray_zero_mem : (0 : _) ∈ ray d)
  have hspanR : Submodule.span ℝ R = linealitySubmodule P ⊔ ℝ ∙ u := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro z hzR
      rcases mem_ray_iff.mp hzR.2 with ⟨μ, hμ, hmap⟩
      have hdiffKer : z - μ • u ∈ LinearMap.ker π := by
        rw [LinearMap.mem_ker, LinearMap.map_sub, LinearMap.map_smul, hu_map, hmap]
        simp
      have hdiffL : z - μ • u ∈ linealitySubmodule P := by
        rwa [linealityQuotientCoordinateMap_ker P] at hdiffKer
      have hdiffSup : z - μ • u ∈ linealitySubmodule P ⊔ ℝ ∙ u :=
        Submodule.mem_sup_left hdiffL
      have hsmulSup : μ • u ∈ linealitySubmodule P ⊔ ℝ ∙ u :=
        Submodule.mem_sup_right (Submodule.smul_mem (ℝ ∙ u) μ (Submodule.mem_span_singleton_self u))
      convert (linealitySubmodule P ⊔ ℝ ∙ u).add_mem hdiffSup hsmulSup using 1 <;> abel
    · refine sup_le ?_ ?_
      · intro z hzL
        exact Submodule.subset_span (hlineality_subset_R hzL)
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.subset_span huR
  have hdirection : (affineSpan ℝ R).direction = Submodule.span ℝ R := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hzeroR]
    congr 1
    ext z
    simp [vsub_eq_sub]
  refine ⟨hR_exposed, ?_⟩
  rw [hdirection, hspanR]
  exact Submodule.finrank_sup_span_singleton hu_not_lineality

end QuotientFacesSupport
