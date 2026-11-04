/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_theorem_6_16
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_20
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_lemma_6_28
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_lemma_6_29

-- Declarations for this item will be appended below by the statement pipeline.

section Theorem630

-- This theorem reuses the chapter's canonical owner `is_maximal_lattice_free` from
-- Section 6.2 and the direct set-builder presentation of the translate `B - f`.

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "ContAssignment" => Rq →₀ NNReal

open Set
open scoped IntegerVectorNotation Matrix Pointwise

/-- The canonical pointwise set translation `(-f) +ᵥ B` is exactly the source-facing translate
`B - f = {r | f + r ∈ B}`. -/
theorem neg_vadd_set_eq_setOf_add_mem
    (f : Rq) (B : Set Rq) :
    (-f) +ᵥ B = {r : Rq | f + r ∈ B} := by
  ext r
  simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]

/-- Helper for Theorem 6.30:
the maximum of a nonempty finite family of linear functionals is sublinear. -/
lemma facetSupSublinear
    {t : ℕ} [NeZero t]
    (normals : Fin t → Rq) :
    (fun r : Rq ↦
      Finset.univ.sup' Finset.univ_nonempty (fun i : Fin t ↦ normals i ⬝ᵥ r)).Sublinear := by
  constructor
  · -- Bound every branch at a sum by the sum of the two finite maxima.
    intro x y
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro i _hi
    calc
      normals i ⬝ᵥ (x + y) = normals i ⬝ᵥ x + normals i ⬝ᵥ y := by
        rw [dotProduct_add]
      _ ≤
          Finset.univ.sup' Finset.univ_nonempty (fun j : Fin t ↦ normals j ⬝ᵥ x) +
            Finset.univ.sup' Finset.univ_nonempty (fun j : Fin t ↦ normals j ⬝ᵥ y) :=
        add_le_add
          (Finset.le_sup' (fun j : Fin t ↦ normals j ⬝ᵥ x) (Finset.mem_univ i))
          (Finset.le_sup' (fun j : Fin t ↦ normals j ⬝ᵥ y) (Finset.mem_univ i))
  · -- A positive scalar preserves both the maximizing order and the maximizing branch.
    intro x c hc
    apply le_antisymm
    · refine Finset.sup'_le Finset.univ_nonempty _ ?_
      intro i _hi
      calc
        normals i ⬝ᵥ (c • x) = c * (normals i ⬝ᵥ x) := by
          rw [dotProduct_smul, smul_eq_mul]
        _ ≤ c * Finset.univ.sup' Finset.univ_nonempty
              (fun j : Fin t ↦ normals j ⬝ᵥ x) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun j : Fin t ↦ normals j ⬝ᵥ x) (Finset.mem_univ i)) hc.le
    · obtain ⟨i, _hi, hmax⟩ :=
        Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun j : Fin t ↦ normals j ⬝ᵥ x)
      calc
        c * Finset.univ.sup' Finset.univ_nonempty
              (fun j : Fin t ↦ normals j ⬝ᵥ x) = c * (normals i ⬝ᵥ x) := by
          rw [hmax]
        _ = normals i ⬝ᵥ (c • x) := by
          rw [dotProduct_smul, smul_eq_mul]
        _ ≤ Finset.univ.sup' Finset.univ_nonempty
              (fun j : Fin t ↦ normals j ⬝ᵥ (c • x)) :=
          Finset.le_sup' (fun j : Fin t ↦ normals j ⬝ᵥ (c • x)) (Finset.mem_univ i)

/-- Helper for Theorem 6.30:
the gauge of a translated centered polyhedron is the maximum of its normalized facet slopes. -/
lemma gaugeTranslatedCenteredPolyhedron_eq_supFacetNormals
    {B : Set Rq} {f : Rq} {t : ℕ} [NeZero t]
    {normals : Fin t → Rq}
    (hfree : is_lattice_free B)
    (hpresentation : IsCenteredFacetPresentation B f normals)
    (r : Rq) :
    gauge {x : Rq | f + x ∈ B} r =
      Finset.univ.sup' Finset.univ_nonempty (fun i : Fin t ↦ normals i ⬝ᵥ r) := by
  let g : Rq → ℝ := fun x ↦
    Finset.univ.sup' Finset.univ_nonempty (fun i : Fin t ↦ normals i ⬝ᵥ x)
  have hg : g.Sublinear := facetSupSublinear normals
  have hg_nonneg : ∀ x : Rq, 0 ≤ g x := by
    -- Lattice-freeness rules out a direction on which every normalized facet slope is negative.
    intro x
    exact supFacetSlopeNonnegOfLatticeFree hfree hpresentation x
  have htranslate : {x : Rq | f + x ∈ B} = sublinear_unit_sublevel_set g := by
    -- The centered inequalities become homogeneous after translating the center to the origin.
    ext x
    rw [hpresentation.eq_centered_polyhedron_of_normals]
    simp only [centered_polyhedron_of_normals, Set.mem_setOf_eq,
      mem_sublinear_unit_sublevel_set]
    constructor
    · intro hx
      refine Finset.sup'_le Finset.univ_nonempty _ ?_
      intro i _hi
      simpa [g, centered_facet_functional, dotProduct] using hx i
    · intro hx i
      have hi : normals i ⬝ᵥ x ≤ g x :=
        Finset.le_sup' (fun j : Fin t ↦ normals j ⬝ᵥ x) (Finset.mem_univ i)
      have hgx : g x ≤ 1 := hx
      simpa [g, centered_facet_functional, dotProduct] using hi.trans hgx
  -- Theorem 6.16 identifies the gauge of this sublinear unit sublevel set pointwise.
  rw [htranslate]
  exact gauge_sublinear_unit_sublevel_set_eq hg hg_nonneg r

/-- Helper for Theorem 6.30:
a valid gauge with an interior origin yields a lattice-free translate. -/
lemma continuousInfiniteGaugeTranslateLatticeFree
    {K : Set Rq} {f : Rq}
    (hK_convex : Convex ℝ K)
    (hK_zero : (0 : Rq) ∈ interior K)
    (hvalid : IsValidFunctionForContinuousInfiniteRelaxation f (gauge K)) :
    is_lattice_free {x : Rq | x - f ∈ K} := by
  classical
  rw [is_lattice_free_iff]
  intro z hz
  let zReal : Rq := Int.cast ∘ z
  have hzTranslated : zReal ∈ interior {x : Rq | (-f) + x ∈ K} := by
    simpa [zReal, sub_eq_add_neg, add_comm] using hz
  have hzK : zReal - f ∈ interior K := by
    have hzK' := (memInterior_setOf_add_mem_iff K (-f) zReal).1 hzTranslated
    simpa [sub_eq_add_neg, add_comm] using hzK'
  have hgauge_lt : gauge K (zReal - f) < 1 :=
    (gauge_lt_one_iff_mem_interior_of_convex_of_zero_mem_interior hK_convex hK_zero).2 hzK
  let y : ContAssignment := Finsupp.single (zReal - f) 1
  have hy : y ∈ continuous_infinite_relaxation_feasible_set f := by
    -- The singleton assignment has shifted balance equal to the chosen integer point.
    rw [mem_continuous_infinite_relaxation_feasible_set_iff, mem_integerVectors_iff]
    refine ⟨z, ?_⟩
    ext i
    simp [continuous_infinite_balance, y, zReal]
  have hone : 1 ≤ gauge K (zReal - f) := by
    have := continuous_infinite_valid_function_one_le hvalid hy
    simpa [y] using this
  exact (not_lt_of_ge hone) hgauge_lt

/-- Helper for Theorem 6.30:
the translated unit sublevel set of a minimal valid function is maximal lattice-free. -/
lemma minimalUnitSublevelTranslateIsMaximalLatticeFree
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    is_maximal_lattice_free
      {x : Rq | x - f ∈ sublinear_unit_sublevel_set ψ} := by
  let K : Set Rq := sublinear_unit_sublevel_set ψ
  let B : Set Rq := {x : Rq | x - f ∈ K}
  have hsublinear : ψ.Sublinear := hψ.sublinear
  have hnonneg : ∀ r : Rq, 0 ≤ ψ r := hψ.nonnegative
  have hK_closed : IsClosed K := isClosed_sublinear_unit_sublevel_set hsublinear
  have hK_convex : Convex ℝ K := convex_sublinear_unit_sublevel_set hsublinear
  have hK_zero : (0 : Rq) ∈ interior K :=
    zero_mem_interior_sublinear_unit_sublevel_set hsublinear
  have hB_convex : Convex ℝ B := by
    -- Translation preserves convex combinations because their coefficients sum to one.
    intro x hx y hy a b ha hb hab
    have hxy := hK_convex hx hy ha hb hab
    have htranslate :
        a • (x - f) + b • (y - f) = (a • x + b • y) - f := by
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      calc
        a * (x i - f i) + b * (y i - f i) =
            a * x i + b * y i - (a + b) * f i := by ring
        _ = a * x i + b * y i - f i := by rw [hab, one_mul]
    rwa [htranslate] at hxy
  have hB_free : is_lattice_free B := by
    apply continuousInfiniteGaugeTranslateLatticeFree hK_convex hK_zero
    have hgauge_eq : gauge K = ψ := by
      -- Identify the whole gauge function before transporting validity across the equality.
      funext r
      simpa [K] using gauge_sublinear_unit_sublevel_set_eq hsublinear hnonneg r
    rw [hgauge_eq]
    exact hψ.toIsValidFunctionForContinuousInfiniteRelaxation
  refine (is_maximal_lattice_free_iff).2 ⟨hB_convex, hB_free, ?_⟩
  intro L hBL hL_convex hL_free
  have hfB : f ∈ interior B := by
    have hfTranslated : f ∈ interior {x : Rq | (-f) + x ∈ K} := by
      apply (memInterior_setOf_add_mem_iff K (-f) f).2
      simpa using hK_zero
    simpa [B, sub_eq_add_neg, add_comm] using hfTranslated
  have hfL : f ∈ interior L := interior_mono hBL hfB
  have hLInterior : (interior L).Nonempty := ⟨f, hfL⟩
  have hclosure_free : is_lattice_free (closure L) := by
    -- A convex set with nonempty interior has the same interior as its closure.
    rw [is_lattice_free_iff]
    intro z
    rw [hL_convex.interior_closure_eq_interior_of_nonempty_interior hLInterior]
    exact (is_lattice_free_iff.mp hL_free) z
  have hfClosure : f ∈ interior (closure L) := by
    simpa [hL_convex.interior_closure_eq_interior_of_nonempty_interior hLInterior] using hfL
  have hclosure_valid :
      IsValidFunctionForContinuousInfiniteRelaxation f
        (gauge {r : Rq | f + r ∈ closure L}) :=
    lemma_6_28_gauge_is_valid_function (closure L) f isClosed_closure
      hL_convex.closure hclosure_free hfClosure
  have hK_absorbent : Absorbent ℝ K :=
    absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hK_zero)
  have hK_subset : K ⊆ {r : Rq | f + r ∈ closure L} := by
    intro r hr
    apply subset_closure
    apply hBL
    simpa [B] using hr
  have hgauge_le : ∀ r : Rq, gauge {s : Rq | f + s ∈ closure L} r ≤ ψ r := by
    intro r
    calc
      gauge {s : Rq | f + s ∈ closure L} r ≤ gauge K r :=
        gauge_mono hK_absorbent hK_subset r
      _ = ψ r := gauge_sublinear_unit_sublevel_set_eq hsublinear hnonneg r
  have hgauge_eq : gauge {r : Rq | f + r ∈ closure L} = ψ :=
    hψ.eq_of_le hclosure_valid hgauge_le
  have hLB : L ⊆ B := by
    intro x hx
    have hxClosure : x - f ∈ {r : Rq | f + r ∈ closure L} := by
      simpa using subset_closure hx
    have hgauge_one : gauge {r : Rq | f + r ∈ closure L} (x - f) ≤ 1 :=
      gauge_le_one_of_mem hxClosure
    have hψ_one : ψ (x - f) ≤ 1 := by
      rwa [hgauge_eq] at hgauge_one
    exact hψ_one
  exact Set.Subset.antisymm hLB hBL

/-- Helper for Theorem 6.30:
an intrinsic-interior point of one centered facet strictly satisfies every other centered
facet inequality. -/
lemma centeredFacetIntrinsicInterior_strict
    {B : Set Rq} {f : Rq} {t : ℕ} {normals : Fin t → Rq}
    (hfull : affineSpan ℝ B = ⊤)
    (hpresentation : IsCenteredFacetPresentation B f normals)
    (i j : Fin t) (hji : j ≠ i) {x : Rq}
    (hx : x ∈ intrinsicInterior ℝ (centered_facet_face f B (normals i))) :
    centered_facet_functional f (normals j) x < 1 := by
  let rhs : Fin t → ℝ := fun k ↦ 1 + normals k ⬝ᵥ f
  have hBpoly : B = polyhedron_le_set normals rhs := by
    calc
      B = centered_polyhedron_of_normals f normals :=
        hpresentation.eq_centered_polyhedron_of_normals
      _ = polyhedron_le_set normals rhs :=
        centered_polyhedron_of_normals_eq_polyhedron_le_set f normals
  have hminimal :=
    minimalRepresentationOfCenteredFacetPresentation hfull hpresentation
  have hactiveFace (k : Fin t) :
      active_constraint_face normals rhs ({k} : Set (Fin t)) =
        face_set B (normals k) (rhs k) := by
    -- The centered presentation and the active-row presentation describe the same facet.
    calc
      active_constraint_face normals rhs ({k} : Set (Fin t)) =
          face_set (polyhedron_le_set normals rhs) (normals k) (rhs k) :=
        active_constraint_face_singleton_eq normals rhs k
      _ = face_set B (normals k) (rhs k) := by rw [hBpoly]
  have hfacet (k : Fin t) :
      is_facet (polyhedron_le_set normals rhs)
        (active_constraint_face normals rhs ({k} : Set (Fin t))) := by
    rw [active_constraint_face_singleton_eq]
    have hk := hminimal.row_is_facet k
    rw [hBpoly] at hk
    simpa [rhs] using hk
  have hjRemaining : j ∈ remaining_inequality_indices normals rhs := by
    -- Every row of a minimal facet representation is non-implicit.
    exact remaining_row_of_eq_singletonFacet_of_isFacet normals rhs j j (hfacet j) rfl
  have hfacesNe :
      active_constraint_face normals rhs ({j} : Set (Fin t)) ≠
        active_constraint_face normals rhs ({i} : Set (Fin t)) := by
    intro hfaces
    apply hji
    apply is_minimal_representation.facet_injective hminimal
    calc
      face_set B (normals j) (rhs j) =
          active_constraint_face normals rhs ({j} : Set (Fin t)) := (hactiveFace j).symm
      _ = active_constraint_face normals rhs ({i} : Set (Fin t)) := hfaces
      _ = face_set B (normals i) (rhs i) := hactiveFace i
  have hxActive :
      x ∈ intrinsicInterior ℝ
        (active_constraint_face normals rhs ({i} : Set (Fin t))) := by
    have hcenteredFace :
        centered_facet_face f B (normals i) =
          active_constraint_face normals rhs ({i} : Set (Fin t)) := by
      calc
        centered_facet_face f B (normals i) =
            face_set B (normals i) (rhs i) := by rfl
        _ = active_constraint_face normals rhs ({i} : Set (Fin t)) := (hactiveFace i).symm
    rwa [hcenteredFace] at hx
  have hrow : Matrix.mulVec normals x j < rhs j :=
    intrinsicInteriorPoint_strictOnDistinctMinimalRow
      hjRemaining (hfacet i) hfacesNe hxActive
  -- Return from the uncentered row presentation to the normalized centered functional.
  simp only [rhs, Matrix.mulVec, centered_facet_functional, dotProduct_sub] at hrow ⊢
  linarith

/-- Helper for Theorem 6.30:
a unique maximizer of finitely many linear functionals remains a maximizer after a sufficiently
small positive step in any fixed direction. -/
lemma existsPositiveStepPreservingUniqueMaximum
    {t : ℕ} (normals : Fin t → Rq) (i : Fin t) (s r : Rq)
    (hstrict : ∀ j : Fin t, j ≠ i → normals j ⬝ᵥ s < normals i ⬝ᵥ s) :
    ∃ ε : NNReal, 0 < ε ∧
      ∀ j : Fin t,
        normals j ⬝ᵥ (s - (ε : ℝ) • r) ≤
          normals i ⬝ᵥ (s - (ε : ℝ) • r) := by
  classical
  have heventually :
      ∀ᶠ a : ℝ in nhds 0, ∀ j : Fin t,
        normals j ⬝ᵥ (s - a • r) ≤ normals i ⬝ᵥ (s - a • r) := by
    apply Filter.eventually_all.2
    intro j
    by_cases hji : j = i
    · subst j
      exact Filter.Eventually.of_forall fun _ ↦ le_rfl
    · have hjContinuous : Continuous fun a : ℝ ↦ normals j ⬝ᵥ (s - a • r) := by
        fun_prop
      have hiContinuous : Continuous fun a : ℝ ↦ normals i ⬝ᵥ (s - a • r) := by
        fun_prop
      have hzero :
          normals j ⬝ᵥ (s - (0 : ℝ) • r) < normals i ⬝ᵥ (s - (0 : ℝ) • r) := by
        simpa only [zero_smul, sub_zero] using hstrict j hji
      exact
        (hjContinuous.continuousAt.eventually_lt hiContinuous.continuousAt hzero).mono
          fun _ ha ↦ ha.le
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.1 heventually
  let ε : NNReal := ⟨δ / 2, le_of_lt (half_pos hδpos)⟩
  refine ⟨ε, ?_, ?_⟩
  · -- The midpoint of the positive radius is a positive `NNReal` step.
    change 0 < δ / 2
    exact half_pos hδpos
  · intro j
    apply hδ
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos]
    · change δ / 2 < δ
      linarith
    · change 0 < δ / 2
      exact half_pos hδpos

/-- Helper for Theorem 6.30:
the gauge translated from a maximal lattice-free set is a minimal valid function. -/
lemma gaugeTranslateIsMinimalOfMaximalLatticeFree
    {B : Set Rq} {f : Rq}
    (hB : is_maximal_lattice_free B)
    (hf : f ∈ interior B) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f
      (gauge {r : Rq | f + r ∈ B}) := by
  classical
  have hconv : Convex ℝ B := hB.convex
  have hfree : is_lattice_free B := hB.lattice_free
  have hfull : affineSpan ℝ B = ⊤ :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hconv).1 ⟨f, hf⟩
  have hclosed : IsClosed B := maximalLatticeFree_isClosed hfull hB
  have hvalid :
      IsValidFunctionForContinuousInfiniteRelaxation f
        (gauge {r : Rq | f + r ∈ B}) :=
    lemma_6_28_gauge_is_valid_function B f hclosed hconv hfree hf
  obtain ⟨hpoly, _hfreeAgain, hfacets⟩ :=
    (maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice hfull).1 hB
  obtain ⟨t, ht, normals, hpresentation, _hunique⟩ :=
    exists_unique_centered_facet_presentation_up_to_reindexing hpoly hfree hf
  -- Local instance justification (finite facet family): the presentation theorem returns the
  -- nonemptiness witness explicitly, while the finite-supremum gauge API consumes it as an
  -- instance.
  letI : NeZero t := ht
  refine
    { toIsValidFunctionForContinuousInfiniteRelaxation := hvalid
      eq_of_le := ?_ }
  intro φ hφvalid hφle
  have hgaugeLe : ∀ r : Rq, gauge {u : Rq | f + u ∈ B} r ≤ φ r := by
    intro r
    rw [gaugeTranslatedCenteredPolyhedron_eq_supFacetNormals hfree hpresentation r]
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro i _hi
    obtain ⟨z, hz⟩ := hfacets
      (centered_facet_face f B (normals i)) (hpresentation.isFacetOf i)
    let zReal : Rq := Int.cast ∘ z
    let s : Rq := zReal - f
    have hzFace : zReal ∈ centered_facet_face f B (normals i) :=
      intrinsicInterior_subset hz
    have hiActive : normals i ⬝ᵥ s = 1 := by
      have hiCentered :=
        (mem_centered_facet_face_iff f B (normals i) zReal).1 hzFace |>.2
      simpa [s, zReal, centered_facet_functional] using hiCentered
    have hstrict :
        ∀ j : Fin t, j ≠ i → normals j ⬝ᵥ s < normals i ⬝ᵥ s := by
      intro j hji
      have hjCentered : centered_facet_functional f (normals j) zReal < 1 :=
        centeredFacetIntrinsicInterior_strict hfull hpresentation i j hji hz
      have hjSlope : normals j ⬝ᵥ s < 1 := by
        simpa [s, zReal, centered_facet_functional] using hjCentered
      rwa [hiActive]
    obtain ⟨ε, hεpos, hmax⟩ :=
      existsPositiveStepPreservingUniqueMaximum normals i s r hstrict
    let w : Rq := s - (ε : ℝ) • r
    have hsupW :
        Finset.univ.sup' Finset.univ_nonempty (fun j : Fin t ↦ normals j ⬝ᵥ w) =
          normals i ⬝ᵥ w := by
      apply le_antisymm
      · exact Finset.sup'_le Finset.univ_nonempty _ fun j _hj ↦ hmax j
      · exact Finset.le_sup' (fun j : Fin t ↦ normals j ⬝ᵥ w) (Finset.mem_univ i)
    have hgaugeW : gauge {u : Rq | f + u ∈ B} w = normals i ⬝ᵥ w := by
      calc
        gauge {u : Rq | f + u ∈ B} w =
            Finset.univ.sup' Finset.univ_nonempty
              (fun j : Fin t ↦ normals j ⬝ᵥ w) :=
          gaugeTranslatedCenteredPolyhedron_eq_supFacetNormals hfree hpresentation w
        _ = normals i ⬝ᵥ w := hsupW
    let y : ContAssignment :=
      Finsupp.single r ε + Finsupp.single w 1
    have hy : y ∈ continuous_infinite_relaxation_feasible_set f := by
      -- The two coefficients balance at the chosen lattice point on facet `i`.
      rw [mem_continuous_infinite_relaxation_feasible_set_iff, mem_integerVectors_iff]
      refine ⟨z, ?_⟩
      ext k
      rw [continuous_infinite_balance_apply]
      dsimp [y]
      rw [Finsupp.sum_add_index]
      · simp [w, s, zReal, Pi.smul_apply, smul_eq_mul]
      · simp
      · intro u a b
        simp [NNReal.coe_add, add_mul]
    have hone : 1 ≤ y.sum (fun u a ↦ φ u * (a : ℝ)) :=
      continuous_infinite_valid_function_one_le hφvalid hy
    have hcutValue :
        y.sum (fun u a ↦ φ u * (a : ℝ)) =
          φ r * (ε : ℝ) + φ w := by
      -- Evaluate the cut only after feasibility has fixed the two-point assignment.
      dsimp [y]
      rw [Finsupp.sum_add_index]
      · simp
      · simp
      · intro u a b
        simp [NNReal.coe_add, left_distrib]
    rw [hcutValue] at hone
    have hφw : φ w ≤ normals i ⬝ᵥ w := by
      simpa [hgaugeW] using hφle w
    have hiAtW : normals i ⬝ᵥ w = 1 - (ε : ℝ) * (normals i ⬝ᵥ r) := by
      calc
        normals i ⬝ᵥ w = normals i ⬝ᵥ s - normals i ⬝ᵥ ((ε : ℝ) • r) := by
          dsimp only [w]
          rw [dotProduct_sub]
        _ = 1 - (ε : ℝ) * (normals i ⬝ᵥ r) := by
          rw [dotProduct_smul, smul_eq_mul, hiActive]
    have hφwBound : φ w ≤ 1 - (ε : ℝ) * (normals i ⬝ᵥ r) := by
      rwa [hiAtW] at hφw
    have hεReal : 0 < (ε : ℝ) := by exact_mod_cast hεpos
    nlinarith
  -- The assumed minorant and the facetwise reverse inequality give pointwise equality.
  funext r
  exact le_antisymm (hφle r) (hgaugeLe r)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_2/ch6_sec6_3_2_theorem_6_30.lean
Theorem 6.30. A function `ψ` is a minimal valid function for `R_f` if and only if there
exists a maximal `ℤ^q`-free convex set `B` with `f ∈ interior B` such that `ψ` is the gauge of
`B - f`. -/
theorem minimal_valid_function_iff_exists_maximal_integer_free_gauge
    (f : Rq) (ψ : Rq → ℝ) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ ↔
      ∃ B : Set Rq, is_maximal_lattice_free B ∧ f ∈ interior B ∧
        ψ = gauge {r | f + r ∈ B} := by
  constructor
  · intro hψ
    let K : Set Rq := sublinear_unit_sublevel_set ψ
    let B : Set Rq := {x : Rq | x - f ∈ K}
    have hsublinear : ψ.Sublinear := hψ.sublinear
    have hnonneg : ∀ r : Rq, 0 ≤ ψ r := hψ.nonnegative
    have hKzero : (0 : Rq) ∈ interior K :=
      zero_mem_interior_sublinear_unit_sublevel_set hsublinear
    have hBmax : is_maximal_lattice_free B := by
      -- Minimality makes the canonical translated unit sublevel set geometrically maximal.
      exact minimalUnitSublevelTranslateIsMaximalLatticeFree hψ
    have hfB : f ∈ interior B := by
      have hfTranslated : f ∈ interior {x : Rq | (-f) + x ∈ K} := by
        apply (memInterior_setOf_add_mem_iff K (-f) f).2
        simpa using hKzero
      simpa [B, sub_eq_add_neg, add_comm] using hfTranslated
    have htranslate : {r : Rq | f + r ∈ B} = K := by
      -- Translating `B = f + K` back by its center recovers the original unit sublevel set.
      ext r
      simp [B]
    have hgauge : gauge K = ψ := by
      funext r
      simpa [K] using gauge_sublinear_unit_sublevel_set_eq hsublinear hnonneg r
    refine ⟨B, hBmax, hfB, ?_⟩
    calc
      ψ = gauge K := hgauge.symm
      _ = gauge {r : Rq | f + r ∈ B} := by rw [htranslate]
  · rintro ⟨B, hB, hf, rfl⟩
    -- Facet lattice witnesses force every valid minorant to dominate the translated gauge.
    exact gaugeTranslateIsMinimalOfMaximalLatticeFree hB hf

namespace IsMinimalValidFunctionForContinuousInfiniteRelaxation

/-- A minimal valid function for `R_f` is the gauge of `B - f` for some maximal `ℤ^q`-free
convex set `B` containing `f` in its interior. -/
theorem exists_maximal_integer_free_gauge
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    ∃ B : Set Rq, is_maximal_lattice_free B ∧ f ∈ interior B ∧
      ψ = gauge {r | f + r ∈ B} :=
  (minimal_valid_function_iff_exists_maximal_integer_free_gauge f ψ).1 hψ

/-- A minimal valid function for `R_f` is the gauge of the canonical pointwise translate
`(-f) +ᵥ B` of some maximal `ℤ^q`-free convex set `B` containing `f` in its interior. -/
theorem exists_maximal_integer_free_gauge_vadd
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    ∃ B : Set Rq, is_maximal_lattice_free B ∧ f ∈ interior B ∧
      ψ = gauge ((-f) +ᵥ B) := by
  rcases hψ.exists_maximal_integer_free_gauge with ⟨B, hB, hf, hψB⟩
  refine ⟨B, hB, hf, ?_⟩
  rw [hψB, neg_vadd_set_eq_setOf_add_mem]

/-- If `ψ` is the gauge of `B - f` for some maximal `ℤ^q`-free convex set `B`, then `ψ` is a
minimal valid function for `R_f`, provided `f ∈ interior B`. -/
theorem of_exists_maximal_integer_free_gauge
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : ∃ B : Set Rq, is_maximal_lattice_free B ∧ f ∈ interior B ∧
      ψ = gauge {r | f + r ∈ B}) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ :=
  (minimal_valid_function_iff_exists_maximal_integer_free_gauge f ψ).2 hψ

/-- If `ψ` is the gauge of the canonical pointwise translate `(-f) +ᵥ B` of some maximal
`ℤ^q`-free convex set `B`, then `ψ` is a minimal valid function for `R_f`, provided
`f ∈ interior B`. -/
theorem of_exists_maximal_integer_free_gauge_vadd
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : ∃ B : Set Rq, is_maximal_lattice_free B ∧ f ∈ interior B ∧
      ψ = gauge ((-f) +ᵥ B)) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ := by
  rcases hψ with ⟨B, hB, hf, hψB⟩
  refine of_exists_maximal_integer_free_gauge ?_
  refine ⟨B, hB, hf, ?_⟩
  rw [hψB, neg_vadd_set_eq_setOf_add_mem]

end IsMinimalValidFunctionForContinuousInfiniteRelaxation

end Theorem630
