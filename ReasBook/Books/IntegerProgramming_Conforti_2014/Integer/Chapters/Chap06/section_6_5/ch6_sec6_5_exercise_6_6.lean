/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_12.ch3_sec3_12_theorem_3_37.Recession
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_example_6_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_12

open scoped BigOperators CornerPolyhedronNotation Matrix

namespace IntersectionCut

variable {n p k : ℕ}

/-- The unrestricted ambient image of the nonnegative ray-coordinate orthant under
`corner_point xbar rays`. -/
def basis_relaxation
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  corner_point xbar rays '' {coeffs : Fin k → ℝ | ∀ j : Fin k, 0 ≤ coeffs j}

/-- Membership in `basis_relaxation xbar rays` means that the ambient point is represented by a
nonnegative ray coefficient vector. -/
theorem mem_basis_relaxation_iff
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (x : Fin n → ℝ) :
    x ∈ basis_relaxation xbar rays ↔
      ∃ coeffs : Fin k → ℝ,
        (∀ j : Fin k, 0 ≤ coeffs j) ∧
          corner_point xbar rays coeffs = x := Iff.rfl

/-- Helper for Exercise 6.6: moving along a single ray coordinate produces the expected translated
ray point. -/
lemma cornerPoint_smul_single
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k)
    (t : ℝ) :
    corner_point xbar rays (t • Pi.single j (1 : ℝ)) = xbar + t • rays j := by
  classical
  -- Collapse the finite ray sum to the unique active coordinate.
  rw [corner_point_def]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _hi hij
    simp [hij]
  · simp

/-- Helper for Exercise 6.6: if a basis-relaxation point lies outside `interior C`, then every
nonnegative witness satisfies the intersection-cut inequality. -/
lemma basisRelaxationPoint_mem_cutRegion_of_not_mem_interior
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C)
    {coeffs : Fin k → ℝ}
    (hcoeffs_nonneg : ∀ j : Fin k, 0 ≤ coeffs j)
    (hnot_mem : corner_point xbar rays coeffs ∉ interior C) :
    1 ≤ intersection_cut_coeff C xbar rays ⬝ᵥ coeffs := by
  by_contra hcut
  have hcut_lt : intersection_cut_coeff C xbar rays ⬝ᵥ coeffs < 1 :=
    lt_of_not_ge hcut
  rcases existsAdmissibleParametersWithStrictWeightSum
      C xbar rays coeffs hxbar_mem hcoeffs_nonneg hcut_lt with
    ⟨t, ht, hweight_sum_lt_one⟩
  have ht_pos : ∀ j : Fin k, 0 < t j := fun j ↦ (ht j).1
  have ht_mem : ∀ j : Fin k, xbar + t j • rays j ∈ C := fun j ↦ (ht j).2
  have hcorner_mem : corner_point xbar rays coeffs ∈ interior C := by
    -- Reuse the Section 6.2 affine normal form and strict-weight interior lemma directly.
    rw [cornerPoint_eq_weightedAdmissibleCombination xbar rays coeffs t
      (fun j ↦ ne_of_gt (ht_pos j))]
    refine weightedCombination_memInterior_of_sum_lt_one
      C xbar hC_convex hxbar_mem
      (fun j : Fin k ↦ coeffs j / t j)
      (fun j : Fin k ↦ xbar + t j • rays j) ?_ hweight_sum_lt_one ht_mem
    intro j
    exact div_nonneg (hcoeffs_nonneg j) (ht_pos j).le
  exact hnot_mem hcorner_mem

/-- Helper for Exercise 6.6: a strict cut slack forces the represented basis-relaxation point
into `interior C`. -/
lemma basisRelaxationPoint_mem_interior_of_cut_lt_one
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C)
    {coeffs : Fin k → ℝ}
    (hcoeffs_nonneg : ∀ j : Fin k, 0 ≤ coeffs j)
    (hcut_lt : intersection_cut_coeff C xbar rays ⬝ᵥ coeffs < 1) :
    corner_point xbar rays coeffs ∈ interior C := by
  -- Contrapose the outside-`interior C` cut-validity lemma proved just above.
  by_contra hnot_mem
  exact not_lt_of_ge
    (basisRelaxationPoint_mem_cutRegion_of_not_mem_interior
      C xbar rays hC_convex hxbar_mem hcoeffs_nonneg hnot_mem)
    hcut_lt

/-- Helper for Exercise 6.6: splitting a witness into its positive-cut and zero-cut parts preserves
the coefficient vector, carries all cut weight on the positive part, and separates the ambient ray
sum accordingly. -/
lemma splitCoeffIntoPositiveCutAndZeroCutParts
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (coeffs : Fin k → ℝ) :
    let positivePart : Fin k → ℝ :=
      fun j ↦ if intersection_cut_coeff C xbar rays j = 0 then 0 else coeffs j
    let zeroPart : Fin k → ℝ :=
      fun j ↦ if intersection_cut_coeff C xbar rays j = 0 then coeffs j else 0
    positivePart + zeroPart = coeffs ∧
      intersection_cut_coeff C xbar rays ⬝ᵥ positivePart =
        intersection_cut_coeff C xbar rays ⬝ᵥ coeffs ∧
      intersection_cut_coeff C xbar rays ⬝ᵥ zeroPart = 0 ∧
      corner_point xbar rays coeffs =
        corner_point xbar rays positivePart + ∑ j : Fin k, zeroPart j • rays j := by
  classical
  -- Split every coordinate according to whether its cut coefficient vanishes.
  dsimp
  constructor
  · funext j
    by_cases hj : intersection_cut_coeff C xbar rays j = 0
    · simp [hj]
    · simp [hj]
  constructor
  · -- The positive part retains every nonzero-cut contribution to the dot product.
    simp [dotProduct]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hj0 : intersection_cut_coeff C xbar rays j = 0
    · simp [hj0]
    · simp [hj0]
  constructor
  · -- Every coordinate of the zero part is annihilated by its zero cut coefficient.
    simp [dotProduct]
    refine Finset.sum_eq_zero ?_
    intro j _hj
    by_cases hj0 : intersection_cut_coeff C xbar rays j = 0
    · simp [hj0]
    · simp [hj0]
  · -- Expanding `corner_point` reduces the claim to the pointwise split of the ray sum.
    rw [corner_point_def, corner_point_def]
    have hsplit :
        ∑ j : Fin k, coeffs j • rays j =
          (∑ j : Fin k,
            (if intersection_cut_coeff C xbar rays j = 0 then 0 else coeffs j) • rays j) +
          ∑ j : Fin k,
            (if intersection_cut_coeff C xbar rays j = 0 then coeffs j else 0) • rays j := by
      calc
        ∑ j : Fin k, coeffs j • rays j =
            ∑ j : Fin k, (((if intersection_cut_coeff C xbar rays j = 0 then 0 else coeffs j) +
              (if intersection_cut_coeff C xbar rays j = 0 then coeffs j else 0)) • rays j) := by
                refine Finset.sum_congr rfl ?_
                intro j _hj
                by_cases hj0 : intersection_cut_coeff C xbar rays j = 0
                · simp [hj0]
                · simp [hj0]
        _ = ∑ j : Fin k,
              ((if intersection_cut_coeff C xbar rays j = 0 then 0 else coeffs j) • rays j +
                (if intersection_cut_coeff C xbar rays j = 0 then coeffs j else 0) • rays j) := by
                  refine Finset.sum_congr rfl ?_
                  intro j _hj
                  rw [add_smul]
        _ =
            (∑ j : Fin k,
              (if intersection_cut_coeff C xbar rays j = 0 then 0 else coeffs j) • rays j) +
            ∑ j : Fin k,
              (if intersection_cut_coeff C xbar rays j = 0 then coeffs j else 0) • rays j := by
                rw [Finset.sum_add_distrib]
    calc
      xbar + ∑ j : Fin k, coeffs j • rays j =
          xbar +
            ((∑ j : Fin k,
                (if intersection_cut_coeff C xbar rays j = 0 then 0 else coeffs j) • rays j) +
              ∑ j : Fin k,
                (if intersection_cut_coeff C xbar rays j = 0 then coeffs j else 0) • rays j) := by
                rw [hsplit]
      _ =
          (xbar +
              ∑ j : Fin k,
                (if intersection_cut_coeff C xbar rays j = 0 then 0 else coeffs j) • rays j) +
            ∑ j : Fin k,
              (if intersection_cut_coeff C xbar rays j = 0 then coeffs j else 0) • rays j := by
                rw [add_assoc]

/-- Helper for Exercise 6.6: every basis-relaxation point outside `interior C` already satisfies
the exercise's cut-side existential description. -/
lemma basisRelaxationDiffInterior_subset_cutDescription
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C) :
    basis_relaxation xbar rays \ interior C ⊆
      {x | ∃ coeffs : Fin k → ℝ,
        (∀ j : Fin k, 0 ≤ coeffs j) ∧
          1 ≤ intersection_cut_coeff C xbar rays ⬝ᵥ coeffs ∧
            corner_point xbar rays coeffs = x} := by
  intro x hx
  rcases hx with ⟨hx_basis, hx_not_interior⟩
  rcases (mem_basis_relaxation_iff xbar rays x).mp hx_basis with
    ⟨coeffs, hcoeffs_nonneg, rfl⟩
  -- Unpack the basis-relaxation witness and apply the outside-`interior C` cut inequality.
  refine ⟨coeffs, hcoeffs_nonneg, ?_, rfl⟩
  exact basisRelaxationPoint_mem_cutRegion_of_not_mem_interior
    C xbar rays hC_convex hxbar_mem hcoeffs_nonneg hx_not_interior

/-- Helper for Exercise 6.6: the ray matrix realizes the linear part of `corner_point`. -/
lemma rayMatrix_mulVec_eq_raySum
    (rays : Fin k → Fin n → ℝ)
    (coeffs : Fin k → ℝ) :
    (fun i j ↦ rays j i) *ᵥ coeffs = ∑ j : Fin k, coeffs j • rays j := by
  -- Compare both sides coordinatewise and expand the matrix-vector product.
  ext i
  simpa [Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]

/-- Helper for Exercise 6.6: every finitely presented polyhedron in `ℝ^n` is closed. -/
lemma isClosed_of_isPolyhedron
    {P : Set (Fin n → ℝ)}
    (hP : is_polyhedron P) :
    IsClosed P := by
  rcases hP with ⟨m, A, b, rfl⟩
  -- Intersect the closed row halfspaces of the defining matrix system.
  rw [show polyhedron_le_set A b = ⋂ i : Fin m, {x : Fin n → ℝ | (A *ᵥ x) i ≤ b i} by
    ext x
    constructor
    · intro hx
      simpa [polyhedron_le_set] using hx
    · intro hx
      simpa [polyhedron_le_set] using hx]
  refine isClosed_iInter ?_
  intro i
  have hcont : Continuous fun x : Fin n → ℝ ↦ (A *ᵥ x) i := by
    exact (continuous_apply i).comp A.mulVecLin.continuous_of_finiteDimensional
  exact isClosed_le hcont continuous_const

/-- Helper for Exercise 6.6: translating a polyhedron by a fixed ambient vector preserves
polyhedrality. -/
lemma translate_isPolyhedron
    (xbar : Fin n → ℝ)
    {P : Set (Fin n → ℝ)}
    (hP : is_polyhedron P) :
    is_polyhedron ((fun z : Fin n → ℝ ↦ xbar + z) '' P) := by
  rcases hP with ⟨m, A, b, rfl⟩
  -- Rewrite the translated set by shifting the right-hand side of the same matrix system.
  refine ⟨m, A, fun i ↦ b i + (A *ᵥ xbar) i, ?_⟩
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    intro i
    have hz' :
        ((A *ᵥ xbar) i + (A *ᵥ z) i) ≤ (A *ᵥ xbar) i + b i :=
      add_le_add_left (hz i) ((A *ᵥ xbar) i)
    simpa [Matrix.mulVec_add, add_comm, add_left_comm, add_assoc] using hz'
  · intro hx
    refine ⟨x - xbar, ?_, by ext i <;> simp⟩
    intro i
    have hx' :
        ((A *ᵥ (x - xbar)) i + (A *ᵥ xbar) i) ≤ b i + (A *ᵥ xbar) i := by
      simpa [sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_neg, add_comm, add_left_comm,
        add_assoc] using hx i
    linarith

/-- Helper for Exercise 6.6: the ambient cut-description set is polyhedral. -/
lemma cutDescription_isPolyhedron
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ) :
    is_polyhedron
      {x | ∃ coeffs : Fin k → ℝ,
        (∀ j : Fin k, 0 ≤ coeffs j) ∧
          1 ≤ intersection_cut_coeff C xbar rays ⬝ᵥ coeffs ∧
            corner_point xbar rays coeffs = x} := by
  let a : Fin k → ℝ := intersection_cut_coeff C xbar rays
  let H : Set (Fin k → ℝ) := {coeffs | (∀ j : Fin k, 0 ≤ coeffs j) ∧ 1 ≤ a ⬝ᵥ coeffs}
  let R : Matrix (Fin n) (Fin k) ℝ := fun i j ↦ rays j i
  have hH_poly : is_polyhedron H := by
    -- Encode the nonnegativity constraints and the single cut inequality as one matrix system.
    refine ⟨k + 1,
      fun i j ↦ Fin.cases (-a j) (fun i' ↦ -(1 : Matrix (Fin k) (Fin k) ℝ) i' j) i,
      fun i ↦ Fin.cases (-1 : ℝ) (fun _ ↦ (0 : ℝ)) i, ?_⟩
    ext coeffs
    constructor
    · rintro ⟨hcoeffs_nonneg, hcut⟩
      intro i
      cases i using Fin.cases with
      | zero =>
          simpa [a, Matrix.mulVec, dotProduct] using (neg_le_neg hcut)
      | succ i =>
          simpa [Matrix.mulVec, dotProduct] using hcoeffs_nonneg i
    · intro hcoeffs
      constructor
      · intro j
        simpa [Matrix.mulVec, dotProduct] using hcoeffs j.succ
      · have hzero := hcoeffs 0
        have hzero' : -(a ⬝ᵥ coeffs) ≤ -1 := by
          simpa [a, Matrix.mulVec, dotProduct] using hzero
        linarith
  have hLinear_poly : is_polyhedron (R.mulVecLin '' H) :=
    linearImage_isPolyhedron_of_polyhedron R.mulVecLin H hH_poly
  have hTranslate_poly :
      is_polyhedron ((fun z : Fin n → ℝ ↦ xbar + z) '' (R.mulVecLin '' H)) :=
    translate_isPolyhedron xbar hLinear_poly
  have hrewrite :
      {x | ∃ coeffs : Fin k → ℝ,
        (∀ j : Fin k, 0 ≤ coeffs j) ∧
          1 ≤ intersection_cut_coeff C xbar rays ⬝ᵥ coeffs ∧
            corner_point xbar rays coeffs = x} =
        ((fun z : Fin n → ℝ ↦ xbar + z) '' (R.mulVecLin '' H)) := by
    ext x
    constructor
    · rintro ⟨coeffs, hcoeffs_nonneg, hcut, hcorner⟩
      refine ⟨R *ᵥ coeffs, ?_, ?_⟩
      · exact ⟨coeffs, ⟨hcoeffs_nonneg, by simpa [a] using hcut⟩, rfl⟩
      · calc
          xbar + R *ᵥ coeffs = corner_point xbar rays coeffs := by
            rw [corner_point_def, rayMatrix_mulVec_eq_raySum]
          _ = x := hcorner
    · rintro ⟨z, ⟨coeffs, hcoeffs, hz⟩, rfl⟩
      rcases hcoeffs with ⟨hcoeffs_nonneg, hcut⟩
      refine ⟨coeffs, hcoeffs_nonneg, by simpa [a] using hcut, ?_⟩
      calc
        corner_point xbar rays coeffs = xbar + R *ᵥ coeffs := by
          rw [corner_point_def, rayMatrix_mulVec_eq_raySum]
        _ = xbar + z := by simpa using congrArg (fun w ↦ xbar + w) hz
  rw [hrewrite]
  exact hTranslate_poly

/-- Helper for Exercise 6.6: every mixed-integer ambient corner point outside `interior C`
already satisfies the cut description. -/
lemma ambientCornerDiffInterior_subset_cutDescription
    (hpn : p ≤ n)
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C)
    (hC_lattice_free : Disjoint (interior C) (mixed_integer_prefix_lattice hpn)) :
    P(hpn, xbar, rays) \ interior C ⊆
      {x | ∃ coeffs : Fin k → ℝ,
        (∀ j : Fin k, 0 ≤ coeffs j) ∧
          1 ≤ intersection_cut_coeff C xbar rays ⬝ᵥ coeffs ∧
            corner_point xbar rays coeffs = x} := by
  intro x hx
  rcases hx with ⟨hxP, _hx_not_mem_interior⟩
  rcases (mem_ambient_corner_polyhedron_iff hpn xbar rays x).mp hxP with
    ⟨coeffs, hcoeffs_mem, hcorner⟩
  have hcoeffs_nonneg :
      ∀ j : Fin k, 0 ≤ coeffs j :=
    (mem_corner_polyhedron_iff hpn xbar rays coeffs).mp hcoeffs_mem |>.1
  refine ⟨coeffs, hcoeffs_nonneg, ?_, hcorner⟩
  exact intersection_cut_valid_for_corner_polyhedron
    hpn C xbar rays hC_closed hC_convex hxbar_mem hC_lattice_free hcoeffs_mem

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_6.lean
Exercise 6.6 uses the Section 6.2 ambient corner-polyhedron owner `P(B)`. -/
-- Source alignment: Exercise 6.6 uses the Section 6.2 ambient corner-polyhedron owner `P(B)` on
-- the left-hand side, not the larger continuous basis relaxation. A split-set counterexample
-- refutes the converse inclusion, so the source-facing repair keeps the valid
-- direction only while retaining the original hypotheses.
theorem ch6_sec6_5_exercise_6_6
    (hpn : p ≤ n)
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hperiods : HasPositiveLatticePeriods hpn rays)
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C)
    (hC_lattice_free : Disjoint (interior C) (mixed_integer_prefix_lattice hpn)) :
    closedConvexHull ℝ (P(hpn, xbar, rays) \ interior C) ⊆
      {x | ∃ coeffs : Fin k → ℝ,
        (∀ j : Fin k, 0 ≤ coeffs j) ∧
          1 ≤ intersection_cut_coeff C xbar rays ⬝ᵥ coeffs ∧
            corner_point xbar rays coeffs = x} := by
  -- The split-set counterexample above blocks the reverse inclusion, while this validity direction
  -- follows from the ambient-corner cut inequality and closed/convexity of the cut-description
  -- region.
  refine closedConvexHull_min
    (ambientCornerDiffInterior_subset_cutDescription
      hpn C xbar rays hC_closed hC_convex hxbar_mem hC_lattice_free)
    (convex_of_is_polyhedron (cutDescription_isPolyhedron C xbar rays))
    (isClosed_of_isPolyhedron (cutDescription_isPolyhedron C xbar rays))

end IntersectionCut
