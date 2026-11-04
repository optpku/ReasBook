/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_28
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_theorem_3_27
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_corollary_3_31
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_38
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_18
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free

open scoped BigOperators Matrix

noncomputable section

section Theorem620

variable {p : ℕ}

/-- The normalized facet functional centered at `xbar` with normal `d`. -/
def centered_facet_functional
    (xbar d x : Fin p → ℝ) : ℝ :=
  d ⬝ᵥ (x - xbar)

/-- `centered_facet_functional xbar d x` is the displayed sum
`∑ h, d_h * (x_h - xbar_h)`. -/
theorem centered_facet_functional_def
    (xbar d x : Fin p → ℝ) :
    centered_facet_functional xbar d x =
      ∑ h : Fin p, d h * (x h - xbar h) := by
  simp [centered_facet_functional, dotProduct]

/-- The polyhedron cut out by the normalized centered inequalities with normals `normals`. -/
def centered_polyhedron_of_normals
    {t : ℕ}
    (xbar : Fin p → ℝ)
    (normals : Fin t → Fin p → ℝ) : Set (Fin p → ℝ) :=
  {x | ∀ i : Fin t, centered_facet_functional xbar (normals i) x ≤ 1}

/-- Membership in `centered_polyhedron_of_normals xbar normals` means satisfying each normalized
facet inequality. -/
theorem mem_centered_polyhedron_of_normals_iff
    {t : ℕ}
    (xbar : Fin p → ℝ)
    (normals : Fin t → Fin p → ℝ)
    (x : Fin p → ℝ) :
    x ∈ centered_polyhedron_of_normals xbar normals ↔
      ∀ i : Fin t, centered_facet_functional xbar (normals i) x ≤ 1 :=
  Iff.rfl

/-- The centered inequalities `centered_facet_functional xbar (normals i) x ≤ 1` are exactly the
ordinary matrix inequalities `normals *ᵥ x ≤ fun i ↦ 1 + normals i ⬝ᵥ xbar`. -/
theorem centered_polyhedron_of_normals_eq_polyhedron_le_set
    {t : ℕ}
    (xbar : Fin p → ℝ)
    (normals : Fin t → Fin p → ℝ) :
    centered_polyhedron_of_normals xbar normals =
      polyhedron_le_set normals (fun i : Fin t ↦ 1 + normals i ⬝ᵥ xbar) := by
  ext x
  constructor
  · intro hx i
    have hi := hx i
    rw [centered_facet_functional, dotProduct_sub] at hi
    simpa [Matrix.mulVec] using hi
  · intro hx i
    have hi :
        normals i ⬝ᵥ x ≤ 1 + normals i ⬝ᵥ xbar := by
      simpa [Matrix.mulVec] using hx i
    rw [centered_facet_functional, dotProduct_sub]
    linarith

/-- The facet of `K` cut out by the normalized centered inequality with normal `d`. -/
def centered_facet_face
    (xbar : Fin p → ℝ)
    (K : Set (Fin p → ℝ))
    (d : Fin p → ℝ) : Set (Fin p → ℝ) :=
  face_set K d (1 + d ⬝ᵥ xbar)

/-- `centered_facet_face xbar K d` is the canonical equality face `face_set K d (1 + d ⬝ᵥ xbar)`
coming from the centered inequality `d ⬝ᵥ (x - xbar) ≤ 1`. -/
theorem centered_facet_face_eq_face_set
    (xbar : Fin p → ℝ)
    (K : Set (Fin p → ℝ))
    (d : Fin p → ℝ) :
    centered_facet_face xbar K d = face_set K d (1 + d ⬝ᵥ xbar) :=
  rfl

/-- Membership in `centered_facet_face xbar K d` means belonging to `K` and saturating the
corresponding normalized facet inequality. -/
theorem mem_centered_facet_face_iff
    (xbar : Fin p → ℝ)
    (K : Set (Fin p → ℝ))
    (d x : Fin p → ℝ) :
    x ∈ centered_facet_face xbar K d ↔
      x ∈ K ∧ centered_facet_functional xbar d x = 1 := by
  rw [centered_facet_face_eq_face_set, mem_face_set_iff]
  constructor
  · rintro ⟨hxK, hxface⟩
    refine ⟨hxK, ?_⟩
    rw [centered_facet_functional, dotProduct_sub]
    linarith
  · rintro ⟨hxK, hxface⟩
    refine ⟨hxK, ?_⟩
    rw [centered_facet_functional, dotProduct_sub] at hxface
    linarith

/-- A centered facet presentation of `K` at `xbar` is a normalized finite family of facet
inequalities whose associated equality sets are exactly the facets of `K`. -/
def IsCenteredFacetPresentation
    {t : ℕ}
    (K : Set (Fin p → ℝ))
    (xbar : Fin p → ℝ)
    (normals : Fin t → Fin p → ℝ) : Prop :=
  K = centered_polyhedron_of_normals xbar normals ∧
    (∀ i : Fin t, IsFacetOf K (centered_facet_face xbar K (normals i))) ∧
    ∀ F : Set (Fin p → ℝ), IsFacetOf K F →
      ∃! i : Fin t, F = centered_facet_face xbar K (normals i)

/-- `IsCenteredFacetPresentation K xbar normals` unfolds to a normalized facet presentation whose
equality faces are exactly the facets of `K`. -/
theorem isCenteredFacetPresentation_iff
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ} :
    IsCenteredFacetPresentation K xbar normals ↔
      K = centered_polyhedron_of_normals xbar normals ∧
        (∀ i : Fin t, IsFacetOf K (centered_facet_face xbar K (normals i))) ∧
        ∀ F : Set (Fin p → ℝ), IsFacetOf K F →
          ∃! i : Fin t, F = centered_facet_face xbar K (normals i) :=
  Iff.rfl

namespace IsCenteredFacetPresentation

/-- A centered facet presentation identifies `K` with the normalized centered inequality system
cut out by its indexed facet normals. -/
theorem eq_centered_polyhedron_of_normals
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ}
    (h : IsCenteredFacetPresentation K xbar normals) :
    K = centered_polyhedron_of_normals xbar normals :=
  h.1

/-- Every indexed equality face in a centered facet presentation is a facet of `K`. -/
theorem isFacetOf
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ}
    (h : IsCenteredFacetPresentation K xbar normals)
    (i : Fin t) :
    IsFacetOf K (centered_facet_face xbar K (normals i)) :=
  h.2.1 i

/-- Every facet of `K` appears exactly once among the indexed centered equality faces. -/
theorem existsUnique_index
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ}
    (h : IsCenteredFacetPresentation K xbar normals)
    (F : Set (Fin p → ℝ))
    (hF : IsFacetOf K F) :
    ∃! i : Fin t, F = centered_facet_face xbar K (normals i) :=
  h.2.2 F hF

end IsCenteredFacetPresentation

/-- Helper for Theorem 6.20: a centered facet presentation of a full-dimensional set is already
the pure-inequality minimal representation needed by Corollary 3.31. -/
lemma minimalRepresentationOfCenteredFacetPresentation
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ}
    (hfull : affineSpan ℝ K = ⊤)
    (hpresentation : IsCenteredFacetPresentation K xbar normals) :
    is_minimal_representation
      K
      (0 : Matrix (Fin 0) (Fin p) ℝ)
      (0 : Fin 0 → ℝ)
      normals
      (fun i : Fin t ↦ 1 + normals i ⬝ᵥ xbar) := by
  let rhs : Fin t → ℝ := fun i : Fin t ↦ 1 + normals i ⬝ᵥ xbar
  have hK_eq_polyhedron : K = polyhedron_le_set normals rhs := by
    calc
      K = centered_polyhedron_of_normals xbar normals :=
        hpresentation.eq_centered_polyhedron_of_normals
      _ = polyhedron_le_set normals rhs :=
        centered_polyhedron_of_normals_eq_polyhedron_le_set xbar normals
  have hfull_polyhedron : affineSpan ℝ (polyhedron_le_set normals rhs) = ⊤ := by
    simpa [hK_eq_polyhedron] using hfull
  have hpolyhedron_nonempty : (polyhedron_le_set normals rhs).Nonempty := by
    rcases
        (Convex.interior_nonempty_iff_affineSpan_eq_top (polyhedron_le_set_convex normals rhs)).2
          hfull_polyhedron with
      ⟨z, hz⟩
    exact ⟨z, interior_subset hz⟩
  refine
    { eq_polyhedron := ?_
      eq_affine_hull := ?_
      full_row_rank := ?_
      row_is_facet := ?_
      facets_exhausted := ?_ }
  · -- Rewrite the mixed system with no equality rows back to the centered inequalities.
    calc
      K = polyhedron_le_set normals rhs := hK_eq_polyhedron
      _ =
          mixed_constraint_polyhedron
            normals
            rhs
            (0 : Matrix (Fin 0) (Fin p) ℝ)
            (0 : Fin 0 → ℝ) := by
            ext x
            rw [mem_mixed_constraint_polyhedron]
            constructor
            · intro hx
              refine ⟨hx, ?_⟩
              ext i
              exact Fin.elim0 i
            · rintro ⟨hx, _hxeq⟩
              exact hx
  · -- Full dimensionality identifies the affine hull with the empty equality system `Set.univ`.
    ext x
    simp [hfull]
  · -- The empty equality subsystem has rank zero definitionally.
    simp
  · -- Each centered equality face is declared to be a facet in the presentation data.
    intro i
    rcases isFacetOf_iff.mp (hpresentation.isFacetOf i) with
      ⟨hface_nonempty, hface_exposed, hface_codim⟩
    have hface_exposed_polyhedron :
        IsExposed
          ℝ
          (polyhedron_le_set normals rhs)
          (face_set (polyhedron_le_set normals rhs) (normals i) (rhs i)) := by
      simpa [hK_eq_polyhedron, rhs, centered_facet_face_eq_face_set] using hface_exposed
    have hface_nonempty_polyhedron :
        (face_set (polyhedron_le_set normals rhs) (normals i) (rhs i)).Nonempty := by
      simpa [hK_eq_polyhedron, rhs, centered_facet_face_eq_face_set] using hface_nonempty
    have hface_codim_polyhedron :
        Module.finrank ℝ
            (affineSpan ℝ
              (face_set (polyhedron_le_set normals rhs) (normals i) (rhs i))).direction +
          1 =
          Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set normals rhs)).direction := by
      cases hK_eq_polyhedron
      simpa [rhs, centered_facet_face_eq_face_set] using hface_codim
    simpa [hK_eq_polyhedron, rhs] using
      isFacet_of_nonempty_finrank_direction_affineSpan_add_one_eq
        normals
        rhs
        (face_set (polyhedron_le_set normals rhs) (normals i) (rhs i))
        hface_exposed_polyhedron
        hface_nonempty_polyhedron
        hface_codim_polyhedron
  · -- Every facet appears exactly once among the centered equality faces by hypothesis.
    intro F hF
    have hF_exposed : IsExposed ℝ K F :=
      (is_proper_face_iff.mp (is_facet_to_is_proper_face hF)).1
    have hF_polyhedron : is_facet (polyhedron_le_set normals rhs) F := by
      simpa [hK_eq_polyhedron] using hF
    have hF_exposed_polyhedron : IsExposed ℝ (polyhedron_le_set normals rhs) F := by
      simpa [hK_eq_polyhedron] using hF_exposed
    have hF_nonempty_polyhedron :
        F.Nonempty := by
      exact
        (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
          normals
          rhs
          hpolyhedron_nonempty
          F
          hF_exposed_polyhedron).mp hF_polyhedron |>.1
    have hF_codim_polyhedron :
        Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
          Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set normals rhs)).direction := by
      exact
        (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
          normals
          rhs
          hpolyhedron_nonempty
          F
          hF_exposed_polyhedron).mp hF_polyhedron |>.2
    have hF_isFacetOf : IsFacetOf K F := by
      refine isFacetOf_iff.mpr ?_
      refine ⟨?_, ?_, ?_⟩
      · exact hF_nonempty_polyhedron
      · simpa [hK_eq_polyhedron] using hF_exposed_polyhedron
      · cases hK_eq_polyhedron
        simpa using hF_codim_polyhedron
    simpa [centered_facet_face_eq_face_set] using hpresentation.existsUnique_index F hF_isFacetOf

/-- Helper for Theorem 6.20: once existence is known, Corollary 3.31 forces any two centered
facet presentations at the same interior point to agree exactly up to reindexing. -/
lemma centeredFacetPresentation_unique_up_to_reindexing
    {t t' : ℕ}
    [NeZero t]
    [NeZero t']
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ}
    {normals' : Fin t' → Fin p → ℝ}
    (hfull : affineSpan ℝ K = ⊤)
    (hpresentation : IsCenteredFacetPresentation K xbar normals)
    (hpresentation' : IsCenteredFacetPresentation K xbar normals') :
    ∃ e : Fin t ≃ Fin t', ∀ i : Fin t, normals' (e i) = normals i := by
  let hmin :=
    minimalRepresentationOfCenteredFacetPresentation hfull hpresentation
  let hmin' :=
    minimalRepresentationOfCenteredFacetPresentation hfull hpresentation'
  obtain ⟨e, he⟩ :=
    full_dimensional_minimal_representation_unique_up_to_permutation_and_positive_scaling
      K
      normals
      (fun i : Fin t ↦ 1 + normals i ⬝ᵥ xbar)
      normals'
      (fun i : Fin t' ↦ 1 + normals' i ⬝ᵥ xbar)
      hmin
      hmin'
  refine ⟨e, ?_⟩
  intro i
  obtain ⟨lam, hlam_pos, hlam_pair⟩ := he i
  -- Compare the scalar component against the dot-product normalization at `xbar`.
  have hlam_eq_one : lam = 1 := by
    have hfst : normals' (e i) = lam • normals i := congrArg Prod.fst hlam_pair
    have hsnd :
        1 + normals' (e i) ⬝ᵥ xbar = lam * (1 + normals i ⬝ᵥ xbar) :=
      congrArg Prod.snd hlam_pair
    have hdot : (lam • normals i) ⬝ᵥ xbar = lam * (normals i ⬝ᵥ xbar) := by
      simp [dotProduct, Finset.mul_sum]
      ring
    have hlam_left : 1 = lam := by
      calc
        1 = (1 + normals' (e i) ⬝ᵥ xbar) - normals' (e i) ⬝ᵥ xbar := by ring
        _ = lam * (1 + normals i ⬝ᵥ xbar) - (lam • normals i) ⬝ᵥ xbar := by
              rw [hsnd, hfst]
        _ = lam := by
              rw [hdot]
              ring
    linarith
  -- With the scaling fixed to `1`, the vector component is the desired equality.
  simpa [hlam_eq_one] using congrArg Prod.fst hlam_pair

/-- Helper for Theorem 6.20: moving from `xbar` along a ray turns the centered facet functional
into the scalar slope `t * (d ⬝ᵥ r)`. -/
lemma centered_facet_functional_add_smul
    (xbar d r : Fin p → ℝ)
    (t : ℝ) :
    centered_facet_functional xbar d (xbar + t • r) = t * (d ⬝ᵥ r) := by
  -- The centered difference cancels the base point, so only the ray contribution remains.
  rw [centered_facet_functional]
  have hsub : xbar + t • r - xbar = t • r := by
    ext i
    simp
  rw [hsub]
  simp [dotProduct, Finset.mul_sum, mul_left_comm]

/-- Helper for Theorem 6.20: the center of a centered facet presentation belongs to the presented
polyhedron. -/
lemma centeredPresentation_center_mem
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ}
    (hpresentation : IsCenteredFacetPresentation K xbar normals) :
    xbar ∈ K := by
  -- At the center every normalized facet functional is `0`, so all inequalities are satisfied.
  have hxbar_mem :
      xbar ∈ centered_polyhedron_of_normals xbar normals := by
    intro i
    simp [centered_facet_functional]
  simpa [hpresentation.eq_centered_polyhedron_of_normals] using hxbar_mem

/-- Helper for Theorem 6.20: strict satisfaction of every row in a finite linear-inequality
system puts the point in the ambient interior of the feasible set. -/
lemma strictRows_memInterior_polyhedronLeSet
    {ι : Type*}
    [Finite ι]
    {A : Matrix ι (Fin p) ℝ}
    {b : ι → ℝ}
    {x : Fin p → ℝ}
    (hstrict : ∀ i : ι, (A *ᵥ x) i < b i) :
    x ∈ interior {y : Fin p → ℝ | A *ᵥ y ≤ b} := by
  let U : Set (Fin p → ℝ) := {y : Fin p → ℝ | ∀ i : ι, (A *ᵥ y) i < b i}
  have hU_open : IsOpen U := by
    -- Rewrite the strict row system as a finite intersection of open halfspaces.
    classical
    rw [show U = ⋂ i : ι, {y : Fin p → ℝ | (A *ᵥ y) i < b i} by
      ext y
      simp [U]]
    refine isOpen_iInter_of_finite fun i ↦ ?_
    have hcont : Continuous fun y : Fin p → ℝ ↦ (A *ᵥ y) i := by
      continuity
    exact isOpen_lt hcont continuous_const
  have hxU : x ∈ U := hstrict
  have hUSubset : U ⊆ {y : Fin p → ℝ | A *ᵥ y ≤ b} := by
    intro y hy i
    exact (hy i).le
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hU_open.mem_nhds hxU) hUSubset

/-- Helper for Theorem 6.20: the center of a centered facet presentation is an interior point of
the presented polyhedron. -/
lemma centeredPresentation_center_mem_interior
    {t : ℕ}
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {normals : Fin t → Fin p → ℝ}
    (hpresentation : IsCenteredFacetPresentation K xbar normals) :
    xbar ∈ interior K := by
  let rhs : Fin t → ℝ := fun i : Fin t ↦ 1 + normals i ⬝ᵥ xbar
  have hstrict : ∀ i : Fin t, (normals *ᵥ xbar) i < rhs i := by
    intro i
    dsimp [rhs]
    simp [Matrix.mulVec]
  have hxbar_mem :
      xbar ∈ interior (polyhedron_le_set normals rhs) :=
    strictRows_memInterior_polyhedronLeSet hstrict
  -- Reinterpret the strict rowwise interior witness in the centered coordinates of `K`.
  have hxbar_centered :
      xbar ∈ interior (centered_polyhedron_of_normals xbar normals) := by
    simpa [rhs, centered_polyhedron_of_normals_eq_polyhedron_le_set xbar normals] using hxbar_mem
  simpa [hpresentation.eq_centered_polyhedron_of_normals] using hxbar_centered

/-- Helper for Theorem 6.20: if one row is tight at an interior point of a polyhedron, then that
row and right-hand side must both be zero. -/
lemma rowEq_zero_of_memInterior
    {m : ℕ}
    {A : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xbar : Fin p → ℝ}
    {i : Fin m}
    (hxbar : xbar ∈ interior (polyhedron_le_set A b))
    (hxbar_eq : A i ⬝ᵥ xbar = b i) :
    (A i, b i) = 0 := by
  have hAi_zero : A i = 0 := by
    ext k
    let e : Fin p → ℝ := fun l ↦ if l = k then 1 else 0
    let line : ℝ → Fin p → ℝ := fun t ↦ xbar + t • e
    have hline_cont : Continuous line := by
      -- The parameterized line is the sum of a constant map and a scalar multiple of a constant
      -- direction.
      simpa [line] using
        (continuous_const.add (continuous_id.smul continuous_const) :
          Continuous fun t : ℝ ↦ xbar + t • e)
    have hline_zero : line 0 ∈ interior (polyhedron_le_set A b) := by
      simpa [line, e] using hxbar
    have hline_preimage :
        {t : ℝ | line t ∈ interior (polyhedron_le_set A b)} ∈ nhds (0 : ℝ) := by
      simpa [line] using
        hline_cont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hline_zero)
    rcases Metric.mem_nhds_iff.mp hline_preimage with ⟨ε, hεpos, hεball⟩
    let δ : ℝ := ε / 2
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact half_pos hεpos
    let xplus : Fin p → ℝ := xbar + δ • e
    let xminus : Fin p → ℝ := xbar - δ • e
    have hxplus_mem : xplus ∈ polyhedron_le_set A b := by
      -- The open interior contains a symmetric interval of line parameters around `0`.
      have hδball : δ ∈ Metric.ball (0 : ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        simpa [sub_zero, abs_of_nonneg hδpos.le, δ] using half_lt_self hεpos
      exact interior_subset (by simpa [line, xplus] using hεball hδball)
    have hxminus_mem : xminus ∈ polyhedron_le_set A b := by
      -- The backward parameter `-δ` lies in the same one-dimensional neighborhood.
      have hnegδball : -δ ∈ Metric.ball (0 : ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        simpa [sub_zero, abs_of_neg, abs_of_nonneg hδpos.le, δ] using half_lt_self hεpos
      exact interior_subset (by simpa [line, xminus, sub_eq_add_neg] using hεball hnegδball)
    have hxplus_eq' : A i ⬝ᵥ xplus ≤ b i := hxplus_mem i
    have hxminus_eq' : A i ⬝ᵥ xminus ≤ b i := hxminus_mem i
    have hdot_e : A i ⬝ᵥ e = A i k := by
      simp [e, dotProduct]
    have hxplus_expand :
        A i ⬝ᵥ xplus = A i ⬝ᵥ xbar + A i k * δ := by
      -- The forward perturbation changes only the `k`th coordinate.
      calc
        A i ⬝ᵥ xplus = A i ⬝ᵥ (xbar + δ • e) := by
          rfl
        _ = A i ⬝ᵥ xbar + A i ⬝ᵥ (δ • e) := by
          rw [dotProduct_add]
        _ = A i ⬝ᵥ xbar + δ * (A i ⬝ᵥ e) := by
          rw [dotProduct_smul]
          simp [smul_eq_mul]
        _ = A i ⬝ᵥ xbar + A i k * δ := by
          rw [hdot_e]
          ring
    have hxminus_expand :
        A i ⬝ᵥ xminus = A i ⬝ᵥ xbar - A i k * δ := by
      -- The backward perturbation contributes the same coordinate with opposite sign.
      calc
        A i ⬝ᵥ xminus = A i ⬝ᵥ (xbar - δ • e) := by
          rfl
        _ = A i ⬝ᵥ xbar - A i ⬝ᵥ (δ • e) := by
          rw [dotProduct_sub]
        _ = A i ⬝ᵥ xbar - δ * (A i ⬝ᵥ e) := by
          rw [dotProduct_smul]
          simp [smul_eq_mul]
        _ = A i ⬝ᵥ xbar - A i k * δ := by
          rw [hdot_e]
          ring
    have hplus :
        A i ⬝ᵥ xbar + A i k * δ ≤ b i := by
      rw [← hxplus_expand]
      exact hxplus_eq'
    have hminus :
        A i ⬝ᵥ xbar - A i k * δ ≤ b i := by
      rw [← hxminus_expand]
      exact hxminus_eq'
    have hcoord_zero : A i k * δ = 0 := by
      linarith [hplus, hminus, hxbar_eq]
    exact (mul_eq_zero.mp hcoord_zero).resolve_right (ne_of_gt hδpos)
  have hbi_zero : b i = 0 := by
    symm
    simpa [hAi_zero, dotProduct] using hxbar_eq
  ext <;> simp [hAi_zero, hbi_zero]

/-- Helper for Theorem 6.20: an implicit row of a polyhedron with an interior point must be the
trivial zero row, since the equality holds on a whole neighborhood. -/
lemma implicitEqualityRow_eq_zero_of_memInterior
    {m : ℕ}
    {A : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xbar : Fin p → ℝ}
    {i : Fin m}
    (hxbar : xbar ∈ interior (polyhedron_le_set A b))
    (hi : is_implicit_equality A b i) :
    (A i, b i) = 0 := by
  -- Specialize the row-tightness lemma to the implicit equality evaluated at the interior point.
  exact rowEq_zero_of_memInterior hxbar (hi (interior_subset hxbar))

/-- Helper for Theorem 6.20: every remaining row of a polyhedral presentation is strict at an
interior point, so its centered normalization denominator is positive. -/
lemma remainingRowSlack_pos_of_memInterior
    {m : ℕ}
    {A : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xbar : Fin p → ℝ}
    {j : Fin m}
    (hxbar : xbar ∈ interior (polyhedron_le_set A b))
    (hj : j ∈ remaining_inequality_indices A b) :
    0 < b j - A j ⬝ᵥ xbar := by
  have hxbar_mem : xbar ∈ polyhedron_le_set A b := interior_subset hxbar
  have hxbar_le : A j ⬝ᵥ xbar ≤ b j := hxbar_mem j
  have hj_not_implicit : ¬ is_implicit_equality A b j :=
    (mem_remaining_inequality_indices_iff A b j).1 hj
  by_contra hgap_not_pos
  have hgap_nonpos : b j - A j ⬝ᵥ xbar ≤ 0 := le_of_not_gt hgap_not_pos
  have hxbar_eq : A j ⬝ᵥ xbar = b j := by
    linarith
  have hrow_zero : (A j, b j) = 0 := rowEq_zero_of_memInterior hxbar hxbar_eq
  have himplicit : is_implicit_equality A b j := by
    -- A zero row with zero right-hand side is tight on every feasible point.
    intro y hy
    have hAj_zero : A j = 0 := congrArg Prod.fst hrow_zero
    have hbj_zero : b j = 0 := congrArg Prod.snd hrow_zero
    simp [Matrix.mulVec, hAj_zero, hbj_zero, dotProduct]
  exact hj_not_implicit himplicit

/-- Helper for Theorem 6.20: normalizing a remaining irredundant row at an interior point turns
its active singleton face into the centered facet face cut out by the normalized normal. -/
lemma centeredFacetFace_eq_activeConstraintFace_of_normalizedRemainingRow
    {m : ℕ}
    {A : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xbar : Fin p → ℝ}
    (hxbar : xbar ∈ interior (polyhedron_le_set A b))
    (j : {i // i ∈ remaining_inequality_indices A b}) :
    centered_facet_face xbar (polyhedron_le_set A b)
      ((remaining_inequality_rhs A b j - remaining_inequality_matrix A b j ⬝ᵥ xbar)⁻¹ •
        remaining_inequality_matrix A b j) =
      active_constraint_face A b ({j.1} : Set (Fin m)) := by
  have hgap_pos :
      0 <
        remaining_inequality_rhs A b j -
          remaining_inequality_matrix A b j ⬝ᵥ xbar := by
    -- The normalization denominator is exactly the positive slack of the remaining row at `xbar`.
    simpa [remaining_inequality_rhs_apply, remaining_inequality_matrix_apply] using
      remainingRowSlack_pos_of_memInterior (A := A) (b := b) (xbar := xbar) (j := j.1) hxbar j.2
  have hgap_ne :
      remaining_inequality_rhs A b j -
          remaining_inequality_matrix A b j ⬝ᵥ xbar ≠ 0 :=
    ne_of_gt hgap_pos
  have hrowdef : remaining_inequality_matrix A b j = A j.1 := by
    ext k
    simp
  have hrhsdef : remaining_inequality_rhs A b j = b j.1 := by
    simp
  let c : ℝ := (b j.1 - A j.1 ⬝ᵥ xbar)⁻¹
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hc_gap : c * (b j.1 - A j.1 ⬝ᵥ xbar) = 1 := by
    simpa [c] using inv_mul_cancel₀ hgap_ne
  ext x
  rw [mem_centered_facet_face_iff, mem_active_constraint_face_iff]
  constructor
  · rintro ⟨hxK, hxeq⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      have hi_eq : i = j.1 := by simpa using hi
      subst hi_eq
      have hscaled_eq : c * (A j.1 ⬝ᵥ x) - c * (A j.1 ⬝ᵥ xbar) = 1 := by
        simpa [c, centered_facet_functional, dotProduct_sub, smul_eq_mul, hrowdef] using hxeq
      have hrow_eq :
          A j.1 ⬝ᵥ x = b j.1 := by
        have hmul : c * (A j.1 ⬝ᵥ x) = c * b j.1 := by
          linarith [hscaled_eq, hc_gap]
        field_simp [c, ne_of_gt hc_pos] at hmul
        exact hmul
      simpa [Matrix.mulVec] using hrow_eq
    · intro i _hi
      exact hxK i
  · rintro ⟨hxEq, hxLe⟩
    have hxK : x ∈ polyhedron_le_set A b := by
      intro i
      by_cases hi : i = j.1
      · subst hi
        exact le_of_eq (hxEq j.1 (by simp))
      · exact hxLe i (by simp [hi])
    refine ⟨hxK, ?_⟩
    have hrow_eq : A j.1 ⬝ᵥ x = b j.1 := hxEq j.1 (by simp)
    have hscaled_eq : c * (A j.1 ⬝ᵥ x) - c * (A j.1 ⬝ᵥ xbar) = 1 := by
      calc
        c * (A j.1 ⬝ᵥ x) - c * (A j.1 ⬝ᵥ xbar)
            = c * b j.1 - c * (A j.1 ⬝ᵥ xbar) := by rw [hrow_eq]
        _ = 1 := by linarith [hc_gap]
    simpa [c, centered_facet_functional, dotProduct_sub, smul_eq_mul, hrowdef] using hscaled_eq

/-- Helper for Theorem 6.20: an irredundant inequality presentation can be normalized at an
interior point into a centered facet presentation. -/
lemma centeredPresentationOfIrredundantRowsAtInteriorPoint
    {m : ℕ}
    {A : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xbar : Fin p → ℝ}
    (hxbar : xbar ∈ interior (polyhedron_le_set A b))
    (hminimal : ∀ i : Fin m, ¬ is_implicit_equality A b i → is_irredundant_row A b i) :
    ∃ t : ℕ, ∃ normals : Fin t → Fin p → ℝ,
      IsCenteredFacetPresentation (polyhedron_le_set A b) xbar normals := by
  let ι := {i // i ∈ remaining_inequality_indices A b}
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let normals : Fin (Fintype.card ι) → Fin p → ℝ := fun i ↦
    ((remaining_inequality_rhs A b (e.symm i) -
          remaining_inequality_matrix A b (e.symm i) ⬝ᵥ xbar)⁻¹ •
      remaining_inequality_matrix A b (e.symm i))
  have hnonempty : (polyhedron_le_set A b).Nonempty := ⟨xbar, interior_subset hxbar⟩
  have hfacets :
      {F : Set (Fin p → ℝ) | is_facet (polyhedron_le_set A b) F} =
        Set.range (fun i : ι ↦ active_constraint_face A b ({i.1} : Set (Fin m))) :=
    facets_eq_range_active_constraint_face_singleton_of_minimal_representation
      A
      b
      hnonempty
      hminimal
  refine ⟨Fintype.card ι, normals, ?_⟩
  constructor
  · -- Compare feasibility row-by-row after dividing each remaining row by its positive slack.
    ext x
    constructor
    · intro hx i
      let j : ι := e.symm i
      have hrow : A j.1 ⬝ᵥ x ≤ b j.1 := hx j.1
      have hgap_pos : 0 < b j.1 - A j.1 ⬝ᵥ xbar := by
        exact remainingRowSlack_pos_of_memInterior (A := A) (b := b) (xbar := xbar) (j := j.1)
          hxbar j.2
      have hrowdef : remaining_inequality_matrix A b j = A j.1 := by
        ext k
        simp
      let c : ℝ := (b j.1 - A j.1 ⬝ᵥ xbar)⁻¹
      have hc_pos : 0 < c := by
        dsimp [c]
        positivity
      have hc_gap : c * (b j.1 - A j.1 ⬝ᵥ xbar) = 1 := by
        simpa [c] using inv_mul_cancel₀ (ne_of_gt hgap_pos)
      have hscaled :
          c * (A j.1 ⬝ᵥ x) - c * (A j.1 ⬝ᵥ xbar) ≤ 1 := by
        calc
          c * (A j.1 ⬝ᵥ x) - c * (A j.1 ⬝ᵥ xbar)
              ≤ c * b j.1 - c * (A j.1 ⬝ᵥ xbar) := by
                  nlinarith [hrow, hc_pos]
          _ = 1 := by linarith [hc_gap]
      have hcentered : centered_facet_functional xbar (normals i) x ≤ 1 := by
        simpa [c, centered_facet_functional, normals, dotProduct_sub, smul_eq_mul, hrowdef] using
          hscaled
      exact hcentered
    · intro hx i
      by_cases hi : is_implicit_equality A b i
      · -- Implicit rows vanish at an interior point, so they impose no further inequality.
        have hzero : (A i, b i) = 0 :=
          implicitEqualityRow_eq_zero_of_memInterior (A := A) (b := b) (xbar := xbar) hxbar hi
        have hAi_zero : A i = 0 := congrArg Prod.fst hzero
        have hbi_zero : b i = 0 := congrArg Prod.snd hzero
        simp [Matrix.mulVec, hAi_zero, hbi_zero, dotProduct]
      · have hi_remaining : i ∈ remaining_inequality_indices A b :=
          (mem_remaining_inequality_indices_iff A b i).2 hi
        let j : ι := ⟨i, hi_remaining⟩
        have hj : centered_facet_functional xbar (normals (e j)) x ≤ 1 := hx (e j)
        have hrowdef : remaining_inequality_matrix A b j = A i := by
          ext k
          simp [j]
        let c : ℝ := (b i - A i ⬝ᵥ xbar)⁻¹
        have hj' : c * (A i ⬝ᵥ x) - c * (A i ⬝ᵥ xbar) ≤ 1 := by
          simpa [c, centered_facet_functional, normals, dotProduct_sub, smul_eq_mul, hrowdef] using
            hj
        have hrow : A i ⬝ᵥ x ≤ b i := by
          have hgap_pos : 0 < b i - A i ⬝ᵥ xbar := by
            exact remainingRowSlack_pos_of_memInterior (A := A) (b := b) (xbar := xbar) (j := i)
              hxbar hi_remaining
          have hc_gap : c * (b i - A i ⬝ᵥ xbar) = 1 := by
            simpa [c] using inv_mul_cancel₀ (ne_of_gt hgap_pos)
          have hmul : c * (A i ⬝ᵥ x) ≤ c * b i := by
            linarith [hj', hc_gap]
          field_simp [c, ne_of_gt hgap_pos] at hmul
          exact hmul
        simpa [Matrix.mulVec] using hrow
  · constructor
    · intro i
      let j : ι := e.symm i
      have hj_facet :
          is_facet (polyhedron_le_set A b) (active_constraint_face A b ({j.1} : Set (Fin m))) := by
        have hmem :
            active_constraint_face A b ({j.1} : Set (Fin m)) ∈
              {F : Set (Fin p → ℝ) | is_facet (polyhedron_le_set A b) F} := by
          rw [hfacets]
          exact Set.mem_range.mpr ⟨j, rfl⟩
        simpa using hmem
      have hface_eq :
          centered_facet_face xbar (polyhedron_le_set A b) (normals i) =
            active_constraint_face A b ({j.1} : Set (Fin m)) := by
        simpa [normals] using
          centeredFacetFace_eq_activeConstraintFace_of_normalizedRemainingRow
            (A := A) (b := b) (xbar := xbar) hxbar j
      have hj_facetOf :
          IsFacetOf (polyhedron_le_set A b) (active_constraint_face A b ({j.1} : Set (Fin m))) := by
        have hj_props :=
          (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
            A b hnonempty
            (active_constraint_face A b ({j.1} : Set (Fin m)))
            (active_constraint_face_isExposed A b ({j.1} : Set (Fin m)))).1 hj_facet
        exact
          isFacetOf_iff.mpr
            ⟨hj_props.1, active_constraint_face_isExposed A b ({j.1} : Set (Fin m)), hj_props.2⟩
      rw [hface_eq]
      exact hj_facetOf
    · intro F hF
      rcases isFacetOf_iff.mp hF with ⟨hF_nonempty, hF_exposed, hF_codim⟩
      have hF_facet : is_facet (polyhedron_le_set A b) F :=
        isFacet_of_nonempty_finrank_direction_affineSpan_add_one_eq
          A b F hF_exposed hF_nonempty hF_codim
      have hF_mem :
          F ∈ {F : Set (Fin p → ℝ) | is_facet (polyhedron_le_set A b) F} := by
        simpa using hF_facet
      rw [hfacets] at hF_mem
      rcases hF_mem with ⟨j, rfl⟩
      refine ⟨e j, ?_, ?_⟩
      · -- The chosen normalized row recovers the original singleton active face.
        simpa [normals] using
          (centeredFacetFace_eq_activeConstraintFace_of_normalizedRemainingRow
            (A := A) (b := b) (xbar := xbar) hxbar j).symm
      · intro i hi
        have hface_eq_i :
            centered_facet_face xbar (polyhedron_le_set A b) (normals i) =
              active_constraint_face A b ({(e.symm i).1} : Set (Fin m)) := by
          simpa [normals] using
            centeredFacetFace_eq_activeConstraintFace_of_normalizedRemainingRow
              (A := A) (b := b) (xbar := xbar) hxbar (e.symm i)
        have hSubtypeEq : e.symm i = j := by
          apply
            (activeConstraintFaceSingleton_injective_of_minimalRepresentation A b hminimal)
          calc
            active_constraint_face A b ({(e.symm i).1} : Set (Fin m))
                = centered_facet_face xbar (polyhedron_le_set A b) (normals i) := hface_eq_i.symm
            _ = active_constraint_face A b ({j.1} : Set (Fin m)) := hi.symm
        simpa using congrArg e hSubtypeEq

/-- Helper for Theorem 6.20: the ENNReal image of `Set.Icc 0 a` has supremum `ENNReal.ofReal a`
when `a` is nonnegative. -/
lemma sSup_ofReal_image_Icc
    {a : ℝ}
    (ha : 0 ≤ a) :
    sSup (ENNReal.ofReal '' Set.Icc (0 : ℝ) a) = ENNReal.ofReal a := by
  -- The endpoint `a` lies in the image, and every other image point is bounded above by it.
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ENNReal.ofReal_le_ofReal ht.2
  · exact le_sSup ⟨a, ⟨ha, le_rfl⟩, rfl⟩

/-- Helper for Theorem 6.20: the ENNReal image of `Set.Ici 0` is unbounded, so its supremum is
`⊤`. -/
lemma sSup_ofReal_image_Ici :
    sSup (ENNReal.ofReal '' Set.Ici (0 : ℝ)) = (⊤ : ENNReal) := by
  -- Every finite ENNReal value is dominated by the image point at `toReal + 1`.
  rw [sSup_eq_top]
  intro b hb
  have hbtop : b ≠ ⊤ := lt_top_iff_ne_top.mp hb
  have hbReal_nonneg : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have hbReal_pos : 0 < b.toReal + 1 := by
    linarith
  refine ⟨ENNReal.ofReal (b.toReal + 1), ?_, ?_⟩
  · refine ⟨b.toReal + 1, ?_, rfl⟩
    exact add_nonneg hbReal_nonneg zero_le_one
  · have hb_eq : b = ENNReal.ofReal b.toReal := by
      symm
      exact ENNReal.ofReal_toReal hbtop
    have hlt : ENNReal.ofReal b.toReal < ENNReal.ofReal (b.toReal + 1) := by
      exact (ENNReal.ofReal_lt_ofReal_iff hbReal_pos).2 (by linarith)
    calc
      b = ENNReal.ofReal b.toReal := hb_eq
      _ < ENNReal.ofReal (b.toReal + 1) := hlt

/-- Helper for Theorem 6.20: flattening a translated mixed point by `Fin.appendEquiv` commutes
with the affine ray expression. -/
lemma appendEquiv_add_smul
    {n : ℕ}
    (x d : MixedRealPoint p (n - p))
    (a : ℝ) :
    Fin.appendEquiv p (n - p) (x + a • d) =
      Fin.appendEquiv p (n - p) x + a • Fin.appendEquiv p (n - p) d := by
  -- Check the integer and free-coordinate blocks separately.
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [Fin.appendEquiv]
  · intro j
    simp [Fin.appendEquiv]

/-- Helper for Theorem 6.20: admissible ray parameters for the cylinder over a centered facet
presentation are exactly the nonnegative parameters satisfying all centered facet inequalities on
the first block. -/
lemma mem_centeredCylinderRayAdmissibleParameters_iff
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {t : ℕ}
    {normals : Fin t → Fin p → ℝ}
    (hpresentation : IsCenteredFacetPresentation K xbar normals)
    {n k : ℕ}
    (xfree : Fin (n - p) → ℝ)
    (rays : Fin k → MixedRealPoint p (n - p))
    (j : Fin k)
    (a : ℝ) :
    a ∈ IntersectionCut.ray_admissible_parameters
        (Fin.appendEquiv p (n - p) '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))))
        (Fin.appendEquiv p (n - p) (xbar, xfree))
        (fun j ↦ Fin.appendEquiv p (n - p) (rays j))
        j ↔
      0 ≤ a ∧ ∀ i : Fin t, a * (normals i ⬝ᵥ (rays j).1) ≤ 1 := by
  rw [IntersectionCut.mem_ray_admissible_parameters_iff]
  have hflat :
      Fin.appendEquiv p (n - p) (xbar, xfree) +
          a • Fin.appendEquiv p (n - p) (rays j) =
        Fin.appendEquiv p (n - p)
          ((xbar, xfree) + a • rays j) := by
    simpa using (appendEquiv_add_smul (x := (xbar, xfree)) (d := rays j) a).symm
  constructor
  · rintro ⟨ha_nonneg, ha_mem⟩
    refine ⟨ha_nonneg, ?_⟩
    have hfirst_mem :
        xbar + a • (rays j).1 ∈ K := by
      rcases ha_mem with ⟨xy, hxy, hxy_eq⟩
      have hxy_def :
          xy = (xbar + a • (rays j).1, xfree + a • (rays j).2) := by
        apply (Fin.appendEquiv p (n - p)).injective
        simpa [hflat] using hxy_eq
      simpa [hxy_def] using hxy.1
    have hxcentered :
        xbar + a • (rays j).1 ∈ centered_polyhedron_of_normals xbar normals := by
      simpa [hpresentation.eq_centered_polyhedron_of_normals] using hfirst_mem
    intro i
    have hi := hxcentered i
    simpa [centered_facet_functional_add_smul] using hi
  · rintro ⟨ha_nonneg, ha_mem⟩
    refine ⟨ha_nonneg, ?_⟩
    have hfirst_mem :
        xbar + a • (rays j).1 ∈ K := by
      have hxcentered :
          xbar + a • (rays j).1 ∈ centered_polyhedron_of_normals xbar normals := by
        intro i
        simpa [centered_facet_functional_add_smul] using ha_mem i
      simpa [hpresentation.eq_centered_polyhedron_of_normals] using hxcentered
    refine ⟨(xbar + a • (rays j).1, xfree + a • (rays j).2), ?_, ?_⟩
    · exact ⟨hfirst_mem, Set.mem_univ _⟩
    · calc
        Fin.appendEquiv p (n - p) (xbar + a • (rays j).1, xfree + a • (rays j).2)
            = Fin.appendEquiv p (n - p) ((xbar, xfree) + a • rays j) := by
                rfl
        _ = Fin.appendEquiv p (n - p) (xbar, xfree) +
              a • Fin.appendEquiv p (n - p) (rays j) := by
                exact hflat.symm

/-- Helper for Theorem 6.20: the admissible ray parameters for the cylinder over a centered facet
presentation are a closed interval when the maximal slope is positive and `Set.Ici 0` otherwise. -/
lemma centeredCylinderRayAdmissibleParameters_eq
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {t : ℕ}
    [NeZero t]
    {normals : Fin t → Fin p → ℝ}
    (hpresentation : IsCenteredFacetPresentation K xbar normals)
    {n k : ℕ}
    (xfree : Fin (n - p) → ℝ)
    (rays : Fin k → MixedRealPoint p (n - p))
    (j : Fin k) :
    let s : ℝ := Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin t ↦ normals i ⬝ᵥ (rays j).1)
    IntersectionCut.ray_admissible_parameters
      (Fin.appendEquiv p (n - p) '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))))
      (Fin.appendEquiv p (n - p) (xbar, xfree))
      (fun j ↦ Fin.appendEquiv p (n - p) (rays j))
      j =
      if 0 < s then Set.Icc 0 (1 / s) else Set.Ici 0 := by
  let s : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin t ↦ normals i ⬝ᵥ (rays j).1)
  ext a
  rw [mem_centeredCylinderRayAdmissibleParameters_iff hpresentation xfree rays j a]
  by_cases hs : 0 < s
  · -- In the positive-slope branch, the active facet attaining the supremum supplies the endpoint.
    rw [if_pos hs, Set.mem_Icc]
    constructor
    · rintro ⟨ha_nonneg, ha_memK⟩
      refine ⟨ha_nonneg, ?_⟩
      obtain ⟨imax, -, himax⟩ :=
        Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun i : Fin t ↦ normals i ⬝ᵥ (rays j).1)
      have himax_le_one : a * (normals imax ⬝ᵥ (rays j).1) ≤ 1 := ha_memK imax
      have has_le_one : a * s ≤ 1 := by
        simpa [s, himax] using himax_le_one
      exact (le_div_iff₀ hs).2 (by simpa [mul_comm] using has_le_one)
    · rintro ⟨ha_nonneg, ha_bound⟩
      refine ⟨ha_nonneg, ?_⟩
      intro i
      have hsi : normals i ⬝ᵥ (rays j).1 ≤ s := by
        dsimp [s]
        exact Finset.le_sup' (fun i : Fin t ↦ normals i ⬝ᵥ (rays j).1) (Finset.mem_univ i)
      have hmul_sup : a * (normals i ⬝ᵥ (rays j).1) ≤ a * s :=
        mul_le_mul_of_nonneg_left hsi ha_nonneg
      have has_le_one : a * s ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_right ha_bound hs.le
        calc
          a * s ≤ (1 / s) * s := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          _ = 1 := by
            field_simp [hs.ne']
      exact hmul_sup.trans has_le_one
  · -- If the maximal slope is nonpositive, every nonnegative parameter remains admissible.
    have hs_nonpos : s ≤ 0 := le_of_not_gt hs
    rw [if_neg hs, Set.mem_Ici]
    constructor
    · intro h
      exact h.1
    · intro ha_nonneg
      refine ⟨ha_nonneg, ?_⟩
      intro i
      have hsi : normals i ⬝ᵥ (rays j).1 ≤ s := by
        dsimp [s]
        exact Finset.le_sup' (fun i : Fin t ↦ normals i ⬝ᵥ (rays j).1) (Finset.mem_univ i)
      have hsi_nonpos : normals i ⬝ᵥ (rays j).1 ≤ 0 := hsi.trans hs_nonpos
      have hmul_nonpos : a * (normals i ⬝ᵥ (rays j).1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha_nonneg hsi_nonpos
      linarith

/-- Helper for Theorem 6.20: if every centered facet slope of `r` is strict negative, then `r`
lies in the interior of the recession cone. -/
lemma negativeFacetSlopes_mem_recessionConeInterior
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {t : ℕ}
    {normals : Fin t → Fin p → ℝ}
    (hpresentation : IsCenteredFacetPresentation K xbar normals)
    {r : Fin p → ℝ}
    (hneg : ∀ i : Fin t, normals i ⬝ᵥ r < 0) :
    r ∈ interior (recessionCone K) := by
  let rhs : Fin t → ℝ := fun i : Fin t ↦ 1 + normals i ⬝ᵥ xbar
  have hxbar_mem : xbar ∈ K := centeredPresentation_center_mem hpresentation
  have hpoly_nonempty : (polyhedron_le_set normals rhs).Nonempty := by
    refine ⟨xbar, ?_⟩
    simpa [rhs, hpresentation.eq_centered_polyhedron_of_normals,
      centered_polyhedron_of_normals_eq_polyhedron_le_set xbar normals] using hxbar_mem
  have hstrict :
      ∀ i : Fin t, (normals *ᵥ r) i < (0 : Fin t → ℝ) i := by
    intro i
    simpa [Matrix.mulVec] using hneg i
  have hr_matrix :
      r ∈ interior (matrix_polyhedral_cone normals) := by
    -- The homogeneous row system has `r` as a strict interior point because every slope is
    -- negative.
    have hr_set :
        r ∈ interior {y : Fin p → ℝ | normals *ᵥ y ≤ (0 : Fin t → ℝ)} :=
      strictRows_memInterior_polyhedronLeSet hstrict
    simpa [matrix_polyhedral_cone, mem_matrix_polyhedral_cone] using hr_set
  have hrec :
      recessionCone K = matrix_polyhedral_cone normals := by
    calc
      recessionCone K = recessionCone (centered_polyhedron_of_normals xbar normals) := by
        rw [hpresentation.eq_centered_polyhedron_of_normals]
      _ = recessionCone (polyhedron_le_set normals rhs) := by
        rw [centered_polyhedron_of_normals_eq_polyhedron_le_set xbar normals]
      _ = matrix_polyhedral_cone normals := by
        rw [recessionCone_polyhedron_eq_matrix_polyhedral_cone normals rhs hpoly_nonempty]
  simpa [hrec] using hr_matrix

/-- Helper for Theorem 6.20: translating an interior point along a recession direction stays in
the interior. This local copy avoids depending on unrecompiled owner API in Theorem 6.18. -/
lemma recessionDirectionPreservesInterior_local
    {K : Set (Fin p → ℝ)}
    {xbar r : Fin p → ℝ}
    (hxbar : xbar ∈ interior K)
    (hr : r ∈ recessionCone K)
    {a : ℝ}
    (ha : 0 ≤ a) :
    xbar + a • r ∈ interior K := by
  rw [mem_interior_iff_mem_nhds] at hxbar ⊢
  rcases mem_nhds_iff.mp hxbar with ⟨s, hsK, hsOpen, hxbar_mem⟩
  have hsImageOpen : IsOpen ((fun x : Fin p → ℝ ↦ x + a • r) '' s) := by
    exact (Homeomorph.addRight (a • r)).isOpenMap _ hsOpen
  have hsImageSubset : ((fun x : Fin p → ℝ ↦ x + a • r) '' s) ⊆ K := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (mem_recessionCone_iff.mp hr) (hsK hx) a ha
  have hxImage : xbar + a • r ∈ (fun x : Fin p → ℝ ↦ x + a • r) '' s := by
    exact ⟨xbar, hxbar_mem, rfl⟩
  exact Filter.mem_of_superset (hsImageOpen.mem_nhds hxImage) hsImageSubset

/-- Helper for Theorem 6.20: a lattice-free set with an interior point cannot admit an interior
recession direction, because a large floor-rounded translate would be an interior lattice point. -/
lemma not_latticeFree_of_memInterior_recessionConeInterior
    {K : Set (Fin p → ℝ)}
    {xbar r : Fin p → ℝ}
    (hxbar : xbar ∈ interior K)
    (hr : r ∈ interior (recessionCone K))
    (hK_lattice_free : is_lattice_free K) :
    False := by
  rw [mem_interior_iff_mem_nhds] at hr
  rcases Metric.mem_nhds_iff.mp hr with ⟨ε, hεpos, hεball⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hεpos
  let M : ℝ := N + 1
  let y : Fin p → ℝ := xbar + M • r
  let z : Fin p → ℤ := fun i ↦ Int.floor (y i)
  let zReal : Fin p → ℝ := Int.cast ∘ z
  let q : Fin p → ℝ := fun i ↦ (zReal i - y i) / M
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hball_mem : r + q ∈ Metric.ball r ε := by
    -- Each floor-rounding error is in `(-1, 0]`, so after dividing by the large scalar `M`
    -- every coordinate stays within the recession-cone ball radius `ε`.
    rw [Metric.mem_ball, dist_pi_lt_iff hεpos]
    intro i
    have hfloor_le : zReal i ≤ y i := by
      exact_mod_cast Int.floor_le (y i)
    have hfloor_lt : y i < zReal i + 1 := by
      change y i < (((Int.floor (y i) : ℤ) : ℝ) + 1)
      exact_mod_cast Int.lt_floor_add_one (y i)
    have habs_lt_one : |zReal i - y i| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have habs_lt_inv : |(zReal i - y i) / M| < 1 / M := by
      rw [abs_div, abs_of_pos hMpos]
      exact div_lt_div_of_pos_right habs_lt_one hMpos
    have hinv_lt_eps : 1 / M < ε := by
      simpa [M] using hN
    have habs_lt_eps : |(zReal i - y i) / M| < ε := habs_lt_inv.trans hinv_lt_eps
    simpa [q, abs_div, abs_of_pos hMpos] using habs_lt_eps
  have hrq : r + q ∈ recessionCone K := hεball hball_mem
  have hzReal_eq : zReal = xbar + M • (r + q) := by
    -- Expanding the definition of `q` cancels the translate `xbar + M • r`.
    ext i
    have hMq : M * q i = zReal i - y i := by
      dsimp [q]
      field_simp [hMpos.ne']
    calc
      zReal i = y i + M * q i := by
        linarith
      _ = xbar i + M * r i + M * q i := by
            simp [y]
      _ = (xbar + M • (r + q)) i := by
            simp [Pi.add_apply, smul_add, M, add_assoc]
  have hzInterior : zReal ∈ interior K := by
    have htranslate :
        xbar + M • (r + q) ∈ interior K :=
      recessionDirectionPreservesInterior_local hxbar hrq hMpos.le
    simpa [hzReal_eq] using htranslate
  have hzInt : zReal ∈ integerVectors p := by
    -- The coordinatewise floor vector is an embedded integer vector.
    exact (mem_integerVectors_iff).2 ⟨z, rfl⟩
  exact hK_lattice_free.not_mem_interior hzInt hzInterior

/-- Helper for Theorem 6.20: the maximal centered facet slope cannot be negative for a lattice-free
polyhedron with the displayed centered presentation. -/
lemma supFacetSlopeNonnegOfLatticeFree
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {t : ℕ}
    [NeZero t]
    {normals : Fin t → Fin p → ℝ}
    (hK_lattice_free : is_lattice_free K)
    (hpresentation : IsCenteredFacetPresentation K xbar normals)
    (r : Fin p → ℝ) :
    0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun i : Fin t ↦ normals i ⬝ᵥ r) := by
  -- Route correction: a negative supremum would make every slope negative, hence would place `r`
  -- in the interior of the recession cone and contradict lattice-freeness via floor rounding.
  by_contra hs_neg
  have hs_lt : Finset.univ.sup' Finset.univ_nonempty (fun i : Fin t ↦ normals i ⬝ᵥ r) < 0 :=
    lt_of_not_ge hs_neg
  have hneg : ∀ i : Fin t, normals i ⬝ᵥ r < 0 := by
    -- Every indexed slope is bounded above by the strictly negative supremum.
    intro i
    have hi_le :
        normals i ⬝ᵥ r ≤
          Finset.univ.sup' Finset.univ_nonempty (fun j : Fin t ↦ normals j ⬝ᵥ r) := by
      exact Finset.le_sup' (fun j : Fin t ↦ normals j ⬝ᵥ r) (Finset.mem_univ i)
    exact hi_le.trans_lt hs_lt
  have hrInterior :
      r ∈ interior (recessionCone K) :=
    negativeFacetSlopes_mem_recessionConeInterior hpresentation hneg
  exact
    not_latticeFree_of_memInterior_recessionConeInterior
      (centeredPresentation_center_mem_interior hpresentation)
      hrInterior
      hK_lattice_free

/-- Theorem 6.20 (1). Let `K ⊆ ℝ^p` be a `ℤ^p`-free polyhedron containing `xbar` in its
interior. Then `K` admits a normalized centered facet presentation
`K = {x | ∑ h, d_h^i * (x_h - xbar_h) ≤ 1 for all i}`, and this presentation is unique up to a
reindexing of the facet normals. -/
theorem exists_unique_centered_facet_presentation_up_to_reindexing
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    (hK_polyhedron : is_polyhedron K)
    (hK_lattice_free : is_lattice_free K)
    (hxbar_mem : xbar ∈ interior K) :
    ∃ t : ℕ, ∃ _ : NeZero t, ∃ normals : Fin t → Fin p → ℝ,
      IsCenteredFacetPresentation K xbar normals ∧
        ∀ t' : ℕ, ∀ _ : NeZero t', ∀ normals' : Fin t' → Fin p → ℝ,
          IsCenteredFacetPresentation K xbar normals' →
            ∃ e : Fin t ≃ Fin t', ∀ i : Fin t, normals' (e i) = normals i := by
  -- Route correction: normalize the remaining rows of an irredundant presentation first, then use
  -- the already-closed uniqueness theorem to eliminate the permutation/scaling ambiguity.
  have hfull : affineSpan ℝ K = ⊤ := by
    exact
      (Convex.interior_nonempty_iff_affineSpan_eq_top (convex_of_is_polyhedron hK_polyhedron)).1
        ⟨xbar, hxbar_mem⟩
  rcases hK_polyhedron with ⟨m, A, b, rfl⟩
  have hpoly_nonempty : (polyhedron_le_set A b).Nonempty := ⟨xbar, interior_subset hxbar_mem⟩
  rcases
      existsIrredundantPresentationOfNonemptyPolyhedron (A := A) (b := b) hpoly_nonempty with
    ⟨m', A', b', hrepr, hminimal⟩
  have hxbar_repr : xbar ∈ interior (polyhedron_le_set A' b') := by
    simpa [hrepr] using hxbar_mem
  rcases centeredPresentationOfIrredundantRowsAtInteriorPoint hxbar_repr hminimal with
    ⟨t, normals, hpresentation_repr⟩
  have hpresentation : IsCenteredFacetPresentation (polyhedron_le_set A b) xbar normals := by
    simpa [hrepr] using hpresentation_repr
  have ht_ne : t ≠ 0 := by
    intro ht
    have hzero_int : (0 : Fin p → ℝ) ∈ integerVectors p := by
      exact (mem_integerVectors_iff).2 ⟨0, by ext i; simp⟩
    have hzero_mem : (0 : Fin p → ℝ) ∈ interior (polyhedron_le_set A b) := by
      have hPolyEq :
          polyhedron_le_set A b = centered_polyhedron_of_normals xbar normals :=
        hpresentation.eq_centered_polyhedron_of_normals
      have hUniv : centered_polyhedron_of_normals xbar normals = Set.univ := by
        subst ht
        ext x
        simp [centered_polyhedron_of_normals]
      simp [hPolyEq, hUniv]
    exact hK_lattice_free.not_mem_interior hzero_int hzero_mem
  let ht : NeZero t := ⟨ht_ne⟩
  -- Local instance justification (finite-index witness): the centered-presentation uniqueness
  -- theorem is stated with `[NeZero t]`, and the lattice-free contradiction above supplies it.
  letI : NeZero t := ht
  refine ⟨t, ht, normals, hpresentation, ?_⟩
  intro t' ht' normals' hpresentation'
  -- Local instance justification (comparison index witness): the comparison presentation already
  -- arrives with its own explicit `NeZero` witness from the theorem statement.
  letI : NeZero t' := ht'
  exact centeredFacetPresentation_unique_up_to_reindexing hfull hpresentation hpresentation'

/-- Theorem 6.20 (2). If `K` is written by a normalized centered facet presentation, then for the
intersection cut of the cylinder `K × ℝ^(n - p)` with `p ≤ n`, the coefficient along `rays j` is
the maximum of the dot products of the facet normals with the first `p` coordinates of that ray. -/
theorem intersection_cut_coeff_eq_sup_facet_normal_dotProduct
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    {t : ℕ}
    [NeZero t]
    (normals : Fin t → Fin p → ℝ)
    (hK_lattice_free : is_lattice_free K)
    (hpresentation : IsCenteredFacetPresentation K xbar normals)
    {n k : ℕ}
    (_hpn : p ≤ n)
    (xfree : Fin (n - p) → ℝ)
    (rays : Fin k → MixedRealPoint p (n - p))
    (j : Fin k) :
    IntersectionCut.intersection_cut_coeff
      (Fin.appendEquiv p (n - p) '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))))
      (Fin.appendEquiv p (n - p) (xbar, xfree))
      (fun j ↦ Fin.appendEquiv p (n - p) (rays j))
      j =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin t ↦ normals i ⬝ᵥ (rays j).1) := by
  let s : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin t ↦ normals i ⬝ᵥ (rays j).1)
  have hparams :
      IntersectionCut.ray_admissible_parameters
        (Fin.appendEquiv p (n - p) '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))))
        (Fin.appendEquiv p (n - p) (xbar, xfree))
        (fun j ↦ Fin.appendEquiv p (n - p) (rays j))
        j =
        if 0 < s then Set.Icc 0 (1 / s) else Set.Ici 0 := by
    -- First normalize the admissible ray parameters to the one-dimensional interval formula.
      simpa [s] using centeredCylinderRayAdmissibleParameters_eq hpresentation xfree rays j
  rw [IntersectionCut.intersection_cut_coeff_eq_inv_ray_intersection_parameter]
  by_cases hs : 0 < s
  · -- Positive maximal slope: the ray parameter is the finite endpoint `1 / s`.
    have hendpoint_nonneg : 0 ≤ 1 / s := by
      positivity
    have hα :
        IntersectionCut.ray_intersection_parameter
          (Fin.appendEquiv p (n - p) '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))))
          (Fin.appendEquiv p (n - p) (xbar, xfree))
          (fun j ↦ Fin.appendEquiv p (n - p) (rays j))
          j =
        (ENNReal.ofReal s)⁻¹ := by
      rw [IntersectionCut.ray_intersection_parameter_def, hparams]
      rw [if_pos hs]
      simpa [one_div, ENNReal.ofReal_inv_of_pos hs] using sSup_ofReal_image_Icc hendpoint_nonneg
    calc
      ((IntersectionCut.ray_intersection_parameter
            (Fin.appendEquiv p (n - p) '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))))
            (Fin.appendEquiv p (n - p) (xbar, xfree))
            (fun j ↦ Fin.appendEquiv p (n - p) (rays j))
            j).toReal)⁻¹
          = (((ENNReal.ofReal s)⁻¹).toReal)⁻¹ := by
              rw [hα]
      _ = ((ENNReal.ofReal s).toReal⁻¹)⁻¹ := by
            simp
      _ = (s⁻¹)⁻¹ := by
            rw [ENNReal.toReal_ofReal hs.le]
      _ = s := by
            field_simp [hs.ne']
  · -- Nonpositive maximal slope: the admissible set is unbounded, so the coefficient is `0`.
    have hs_nonneg : 0 ≤ s := supFacetSlopeNonnegOfLatticeFree hK_lattice_free hpresentation
      (rays j).1
    have hs_zero : s = 0 := le_antisymm (le_of_not_gt hs) hs_nonneg
    have hα :
        IntersectionCut.ray_intersection_parameter
          (Fin.appendEquiv p (n - p) '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))))
          (Fin.appendEquiv p (n - p) (xbar, xfree))
          (fun j ↦ Fin.appendEquiv p (n - p) (rays j))
          j =
        ⊤ := by
      rw [IntersectionCut.ray_intersection_parameter_def, hparams]
      rw [if_neg hs]
      simpa using sSup_ofReal_image_Ici
    calc
      ((IntersectionCut.ray_intersection_parameter
            (Fin.appendEquiv p (n - p) '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))))
            (Fin.appendEquiv p (n - p) (xbar, xfree))
            (fun j ↦ Fin.appendEquiv p (n - p) (rays j))
            j).toReal)⁻¹
          = ((⊤ : ENNReal).toReal)⁻¹ := by
              rw [hα]
      _ = 0 := by
            simp
      _ = s := by
            simp [hs_zero]

/-- ch6_sec6_2_2_theorem_6_20

Theorem 6.20. Let `K ⊆ ℝ^p` be a `ℤ^p`-free polyhedron containing `xbar` in its interior.
Then `K` can be written uniquely in normalized centered facet form
`K = {x | ∑ h, d_h^i * (x_h - xbar_h) ≤ 1 for all i}`, and for the intersection cut of the
cylinder `K × ℝ^(n - p)` in any ambient dimension `n` with `p ≤ n`, the coefficient along each
indexed ray `rays j` satisfies formula
`(6.17)`:
`1 / αⱼ = max_i (normals i ⬝ᵥ (rays j).1)`. -/
theorem ch6_sec6_2_2_theorem_6_20
    {K : Set (Fin p → ℝ)}
    {xbar : Fin p → ℝ}
    (hK_polyhedron : is_polyhedron K)
    (hK_lattice_free : is_lattice_free K)
    (hxbar_mem : xbar ∈ interior K) :
    ∃ t : ℕ, ∃ _ : NeZero t, ∃ normals : Fin t → Fin p → ℝ,
      IsCenteredFacetPresentation K xbar normals ∧
        (∀ t' : ℕ, ∀ _ : NeZero t', ∀ normals' : Fin t' → Fin p → ℝ,
          IsCenteredFacetPresentation K xbar normals' →
            ∃ e : Fin t ≃ Fin t', ∀ i : Fin t, normals' (e i) = normals i) ∧
        ∀ {n k : ℕ}, ∀ hpn : p ≤ n, ∀ xfree : Fin (n - p) → ℝ,
          ∀ rays : Fin k → MixedRealPoint p (n - p), ∀ j : Fin k,
          IntersectionCut.intersection_cut_coeff
            (Fin.appendEquiv p (n - p) '' (K ×ˢ (Set.univ : Set (Fin (n - p) → ℝ))))
            (Fin.appendEquiv p (n - p) (xbar, xfree))
            (fun j ↦ Fin.appendEquiv p (n - p) (rays j))
            j =
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin t ↦ normals i ⬝ᵥ (rays j).1) := by
  -- Route correction: the bundled theorem should only assemble the centered-facet existence part
  -- with the separate coefficient computation, rather than duplicating either proof.
  rcases
      exists_unique_centered_facet_presentation_up_to_reindexing
        hK_polyhedron hK_lattice_free hxbar_mem with
    ⟨t, ht, normals, hpresentation, hunique⟩
  -- Local instance justification (finite-index witness): the coefficient companion theorem is
  -- parameterized by `[NeZero t]`, and the existence theorem returns exactly that witness.
  letI : NeZero t := ht
  refine ⟨t, ht, normals, hpresentation, hunique, ?_⟩
  intro n k hpn xfree rays j
  -- Once the centered presentation is fixed, the coefficient formula is exactly the local
  -- companion theorem specialized to that presentation.
  simpa using
    intersection_cut_coeff_eq_sup_facet_normal_dotProduct
      (K := K)
      (xbar := xbar)
      (normals := normals)
      hK_lattice_free
      hpresentation
      hpn
      xfree
      rays
      j

end Theorem620
