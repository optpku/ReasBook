/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4.ch5_sec5_4_definition_5_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_2.ch10_sec10_2_2_theorem_10_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_3_theorem_10_10
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_7

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling note:
-- * source-facing owner already in Chapter 7.7: `fractional_stable_set_polytope`
-- * source-facing owner already in Chapter 10.2: `theta_body`, with primitive witness data
--   `Matrix.IsThetaBodyWitness`
-- * core/canonical Section 10.3 owners: `IsLovaszSchrijverMatrix` and
--   `lovasz_schrijver_N_plus`
-- The only local public data kept below is the `±1 ↦ {0,1}` change of variables and the
-- graph-specific bridge from `N₊(FRAC(G))` to `theta_body`; the relaxation owner itself is reused
-- from the project graph-relaxation API.

open scoped BigOperators Matrix LovaszSchrijverNotation

universe u

section Ambient

variable {V : Type u}

/-- The affine change of variables `χ_i = (1 + x_i) / 2` taking `±1` coordinates to binary
coordinates. -/
noncomputable def sign_to_binary_transform (x : V → ℝ) : V → ℝ :=
  fun i ↦ (1 + x i) / 2

end Ambient

section Example_10_6

variable {n : ℕ} (G : SimpleGraph (Fin n))

/-- Helper for Example 10.6: the fractional stable-set relaxation `FRAC(G)` is convex because
its box and edge inequalities are preserved by convex combinations. -/
lemma convex_fractionalStableSetPolytope :
    Convex ℝ (FRAC(G)) := by
  intro x hx y hy a b ha hb hab
  rw [mem_fractional_stable_set_polytope_iff] at hx hy ⊢
  rcases hx with ⟨hx_box, hx_edge⟩
  rcases hy with ⟨hy_box, hy_edge⟩
  refine ⟨?_, ?_⟩
  · intro v
    constructor
    · -- The lower box bound is preserved coordinatewise.
      change 0 ≤ a * x v + b * y v
      nlinarith [(hx_box v).1, (hy_box v).1]
    · -- The upper box bound is preserved because `a + b = 1`.
      change a * x v + b * y v ≤ 1
      nlinarith [(hx_box v).2, (hy_box v).2, hab]
  · intro u v huv
    -- The edge inequality is linear in the vector coordinates.
    change a * x u + b * y u + (a * x v + b * y v) ≤ 1
    nlinarith [hx_edge huv, hy_edge huv, hab]

/-- Helper for Example 10.6: a point of `homogenized_cone (FRAC(G))` satisfies the scaled box
and edge inequalities of `FRAC(G)`. -/
lemma homogenizedConeFractionalStableSetData
    {y : Fin (n + 1) → ℝ}
    (hy : y ∈ homogenized_cone (FRAC(G))) :
    0 ≤ y 0 ∧
      (∀ v : Fin n, 0 ≤ y v.succ ∧ y v.succ ≤ y 0) ∧
      ∀ ⦃u v : Fin n⦄, G.Adj u v → y u.succ + y v.succ ≤ y 0 := by
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hxHull, rfl⟩
  -- Collapse the convex-hull witness because `FRAC(G)` is already convex.
  have hxFrac : x ∈ FRAC(G) := by
    rwa [convexHull_eq_self.2 (convex_fractionalStableSetPolytope (G := G))] at hxHull
  rw [mem_fractional_stable_set_polytope_iff] at hxFrac
  rcases hxFrac with ⟨hx_box, hx_edge⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The top coordinate of a homogenized point is the nonnegative scaling factor.
    simpa [homogenized_point] using ht
  · intro v
    constructor
    · -- Tail coordinates inherit nonnegativity from the box constraints.
      simpa [homogenized_point] using mul_nonneg ht (hx_box v).1
    · -- Tail coordinates are bounded above by the top coordinate.
      simpa [homogenized_point] using mul_le_mul_of_nonneg_left (hx_box v).2 ht
  · intro u v huv
    -- Scaling the edge inequality gives the homogenized edge inequality.
    simpa [homogenized_point, mul_add, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hx_edge huv) ht

namespace IsLovaszSchrijverMatrix

/-- For `P = FRAC(G)`, the canonical Section 10.3 Lovasz-Schrijver matrix conditions force every
entry indexed by an edge of `G` to vanish. This is the graph-specific bridge from the canonical
owner `IsLovaszSchrijverMatrix` to the `theta_body` edge constraints. -/
theorem edge_entry_eq_zero_of_mem_fractional_stable_set_polytope
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hY : IsLovaszSchrijverMatrix (FRAC(G)) Y)
    {i j : Fin n} (hij : G.Adj i j) :
    Y i.succ j.succ = 0 := by
  rw [isLovaszSchrijverMatrix_iff] at hY
  rcases hY with ⟨hSymm, -, hcols, hdiag⟩
  -- Read the `j`th lifted column as a homogenized `FRAC(G)` point.
  have hcolData :
      0 ≤ Y 0 j.succ ∧
        (∀ v : Fin n, 0 ≤ Y v.succ j.succ ∧ Y v.succ j.succ ≤ Y 0 j.succ) ∧
        ∀ ⦃u v : Fin n⦄, G.Adj u v → Y u.succ j.succ + Y v.succ j.succ ≤ Y 0 j.succ := by
    simpa [mulVec_lifted_basis] using
      homogenizedConeFractionalStableSetData (G := G) (hcols j).1
  have hij_nonneg : 0 ≤ Y i.succ j.succ := (hcolData.2.1 i).1
  have hsymm_entry : Y j.succ 0 = Y 0 j.succ := by
    simpa [Matrix.transpose_apply] using congr_fun (congr_fun hSymm 0) j.succ
  have hjdiag : Y j.succ j.succ = Y 0 j.succ := by
    calc
      Y j.succ j.succ = Y j.succ 0 := hdiag j
      _ = Y 0 j.succ := hsymm_entry
  have hij_nonpos : Y i.succ j.succ ≤ 0 := by
    -- The edge inequality on the `j`th column collapses against the diagonal identity.
    have hedge : Y i.succ j.succ + Y j.succ j.succ ≤ Y 0 j.succ := hcolData.2.2 hij
    rw [hjdiag] at hedge
    linarith
  linarith

end IsLovaszSchrijverMatrix

/-- Helper for Example 10.6: an `N₊(FRAC(G))` witness matrix reindexed along
`Option.elim' 0 Fin.succ` is a theta-body witness. -/
lemma thetaBodyWitnessOfFracLovaszSchrijverMatrix
    {x : Fin n → ℝ}
    {Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hY : IsLovaszSchrijverMatrix (FRAC(G)) Y)
    (hYpsd : Y.PosSemidef)
    (hfirst : Y *ᵥ lifted_basis 0 = homogenized_point x) :
    (Y.submatrix (Option.elim' 0 Fin.succ) (Option.elim' 0 Fin.succ)).IsThetaBodyWitness G x := by
  have hYmatrix := hY
  rw [isLovaszSchrijverMatrix_iff] at hYmatrix
  rcases hYmatrix with ⟨hSymm, -, -, hdiag⟩
  let e : Option (Fin n) → Fin (n + 1) := Option.elim' 0 Fin.succ
  have hsymm_entry {a b : Fin (n + 1)} : Y a b = Y b a := by
    simpa [Matrix.transpose_apply] using (congr_fun (congr_fun hSymm a) b).symm
  have hfirst_zero : Y 0 0 = 1 := by
    -- The first lifted column is exactly the homogenized point `(1, x)`.
    simpa [mulVec_lifted_basis, homogenized_point] using congrArg (fun z ↦ z 0) hfirst
  have hfirst_tail (v : Fin n) : Y v.succ 0 = x v := by
    -- Reading a tail coordinate recovers the corresponding entry of `x`.
    simpa [mulVec_lifted_basis, homogenized_point] using congrArg (fun z ↦ z v.succ) hfirst
  refine Matrix.IsThetaBodyWitness.mk (G := G) ?_ ?_ ?_ ?_ ?_
  · -- Positive semidefiniteness survives the reindexing to `Option (Fin n)`.
    simpa [e] using hYpsd.submatrix e
  · -- The `none, none` entry is the top-left entry of the lifted witness.
    simpa [Matrix.submatrix_apply, e] using hfirst_zero
  · intro v
    -- The `none` row becomes the vector `x`.
    calc
      Y.submatrix e e none (some v) = Y 0 v.succ := by simp [Matrix.submatrix_apply, e]
      _ = Y v.succ 0 := hsymm_entry
      _ = x v := hfirst_tail v
  · intro v
    -- The diagonal identity of the Lovasz-Schrijver witness matches the theta-body diagonal.
    calc
      Y.submatrix e e (some v) (some v) = Y v.succ v.succ := by
        simp [Matrix.submatrix_apply, e]
      _ = Y v.succ 0 := hdiag v
      _ = x v := hfirst_tail v
  · intro u v huv
    -- Edge entries vanish by the graph-specific matrix lemma proved above.
    simpa [Matrix.submatrix_apply, e] using
      IsLovaszSchrijverMatrix.edge_entry_eq_zero_of_mem_fractional_stable_set_polytope
        (G := G) (Y := Y) hY huv

/-- First claim of Example 10.6. Applying the canonical Lovasz-Schrijver `N₊` operator to
`FRAC(G)` yields
a relaxation contained in the theta body `TH(G)`. -/
theorem lovasz_schrijver_N_plus_frac_subset_theta_body :
    N₊(FRAC(G)) ⊆ TH(G) := by
  intro x hx
  rw [mem_lovasz_schrijver_N_plus_iff] at hx
  rcases hx with ⟨Y, hY, hYpsd, hfirst⟩
  -- Reindex the lifted semidefinite witness into the `Option`-indexed theta-body witness.
  exact
    (thetaBodyWitnessOfFracLovaszSchrijverMatrix
      (G := G) (x := x) (Y := Y) hY hYpsd hfirst).mem_theta_body

end Example_10_6

section Example_10_6_Strictness

local notation "C₅" => (SimpleGraph.cycleGraph 5 : SimpleGraph (Fin 5))

/-- Helper for Example 10.6: the five-cycle counterexample value `1 / Real.sqrt 5`. -/
noncomputable def fiveCycleThetaValue : ℝ :=
  1 / Real.sqrt 5

/-- Helper for Example 10.6: the constant five-cycle counterexample point with value
`1 / Real.sqrt 5` in every coordinate. -/
noncomputable def fiveCycleThetaCounterexample : Fin 5 → ℝ :=
  fun _ ↦ fiveCycleThetaValue

/-- Helper for Example 10.6: the regular pentagon vectors used to build the five-cycle theta-body
witness. -/
noncomputable def fiveCyclePentagonVectors : Fin 5 → EuclideanSpace ℝ (Fin 2) :=
  fun i ↦
    WithLp.toLp 2
      (![Real.cos (4 * Real.pi * (i : ℝ) / 5), Real.sin (4 * Real.pi * (i : ℝ) / 5)] :
        Fin 2 → ℝ)

/-- Helper for Example 10.6: the `Option`-indexed Gram family whose matrix witnesses
`fiveCycleThetaCounterexample ∈ TH(C₅)`. -/
noncomputable def fiveCycleThetaWitnessVectors : Option (Fin 5) → EuclideanSpace ℝ (Fin 3)
  | none => WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ)
  | some i =>
      WithLp.toLp 2
        (![fiveCycleThetaValue,
          Real.sqrt (fiveCycleThetaValue * (1 - fiveCycleThetaValue)) *
            fiveCyclePentagonVectors i 0,
          Real.sqrt (fiveCycleThetaValue * (1 - fiveCycleThetaValue)) *
            fiveCyclePentagonVectors i 1] :
          Fin 3 → ℝ)

/-- Helper for Example 10.6: the pentagon vectors have inner product given by the cosine of their
angle difference. -/
lemma fiveCyclePentagonInner (i j : Fin 5) :
    Matrix.gram ℝ fiveCyclePentagonVectors i j =
      Real.cos ((4 * Real.pi / 5) * ((j : ℝ) - i)) := by
  -- Reuse the Exercise 10.7 pentagon Gram-matrix computation.
  simpa [fiveCyclePentagonVectors] using exercise_10_7_gram_entry i j

/-- Helper for Example 10.6: `cos (4π / 5)` is the adjacent pentagon value. -/
lemma fiveCycleCosFourPiDivFive :
    Real.cos (4 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  simpa using exercise_10_7_cosFourPiDivFive

/-- Helper for Example 10.6: `cos (16π / 5)` repeats the adjacent pentagon value. -/
lemma fiveCycleCosSixteenPiDivFive :
    Real.cos (16 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  simpa using exercise_10_7_cosSixteenPiDivFive

/-- Helper for Example 10.6: the normalized adjacent cosine value at multiplier `1`. -/
lemma fiveCycleCosMulOne :
    Real.cos (4 * Real.pi / 5) = (-Real.sqrt 5 + -1) / 4 := by
  simpa [neg_add_rev] using fiveCycleCosFourPiDivFive

/-- Helper for Example 10.6: the normalized adjacent cosine value at multiplier `4`. -/
lemma fiveCycleCosMulFour :
    Real.cos (4 * Real.pi / 5 * 4) = (-Real.sqrt 5 + -1) / 4 := by
  simpa using exercise_10_7_cosMulFour

/-- Helper for Example 10.6: adjacent pentagon vectors have inner product
`-(1 + Real.sqrt 5) / 4`. -/
lemma fiveCyclePentagonAdjInner {i j : Fin 5} (h : (C₅).Adj i j) :
    Matrix.gram ℝ fiveCyclePentagonVectors i j =
      -(1 + Real.sqrt 5) / 4 := by
  -- Reuse the explicit Exercise 10.7 witness entry formula on cycle edges.
  rw [show Matrix.gram ℝ fiveCyclePentagonVectors = exercise_10_7_witness by
    simpa [fiveCyclePentagonVectors] using exercise_10_7_witness_eq_gram.symm]
  exact exercise_10_7_witness_entry_of_adj h

/-- Helper for Example 10.6: the theta-body counterexample value is positive. -/
lemma fiveCycleThetaValue_pos :
    0 < fiveCycleThetaValue := by
  -- Positivity of `sqrt 5` makes the reciprocal positive.
  have hsqrt_pos : 0 < Real.sqrt 5 := by
    exact Real.sqrt_pos.2 (by positivity)
  simp [fiveCycleThetaValue, hsqrt_pos]

/-- Helper for Example 10.6: the theta-body counterexample value lies in `[0, 1]`. -/
lemma fiveCycleThetaValue_le_one :
    fiveCycleThetaValue ≤ 1 := by
  -- Compare `1 / sqrt 5` with `1` using `sqrt 5 > 1`.
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  have hsqrt_gt_one : 1 < Real.sqrt 5 := by
    nlinarith [hsqrt_sq, Real.sqrt_nonneg 5]
  have hsqrt_pos : 0 < Real.sqrt 5 := by
    exact Real.sqrt_pos.2 (by positivity)
  unfold fiveCycleThetaValue
  field_simp [hsqrt_pos.ne']
  nlinarith

/-- Helper for Example 10.6: the diagonal value of the five-cycle theta witness is
`fiveCycleThetaValue`. -/
lemma fiveCycleThetaValue_diag :
    fiveCycleThetaValue ^ 2 +
      fiveCycleThetaValue * (1 - fiveCycleThetaValue) =
      fiveCycleThetaValue := by
  -- The radial term was chosen so that the diagonal adds back to `α`.
  ring

/-- Helper for Example 10.6: the adjacent witness inner product cancels to zero. -/
lemma fiveCycleThetaValue_edge :
    fiveCycleThetaValue ^ 2 +
      (fiveCycleThetaValue * (1 - fiveCycleThetaValue)) *
        (-(1 + Real.sqrt 5) / 4) = 0 := by
  -- This is the standard `C₅` cancellation `α + (1 - α) cos (4π/5) = 0`
  -- with `α = 1 / √5`.
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  have hsqrt_pos : 0 < Real.sqrt 5 := by
    exact Real.sqrt_pos.2 (by positivity)
  simp [fiveCycleThetaValue]
  field_simp [hsqrt_pos.ne']
  nlinarith

/-- Helper for Example 10.6: the `some`-indexed witness vectors have an inner product controlled
by the pentagon-vector inner product. -/
lemma fiveCycleThetaWitnessVectors_some_inner (i j : Fin 5) :
    Matrix.gram ℝ fiveCycleThetaWitnessVectors (some i) (some j) =
      fiveCycleThetaValue ^ 2 +
        (fiveCycleThetaValue * (1 - fiveCycleThetaValue)) *
          Matrix.gram ℝ fiveCyclePentagonVectors i j := by
  -- Expand the `ℝ³` Gram entry and collapse the squared radial factor.
  have hnonneg :
      0 ≤ fiveCycleThetaValue * (1 - fiveCycleThetaValue) := by
    exact mul_nonneg (le_of_lt fiveCycleThetaValue_pos) (sub_nonneg.mpr fiveCycleThetaValue_le_one)
  have hs :
      Real.sqrt (fiveCycleThetaValue - fiveCycleThetaValue ^ 2) ^ 2 =
        fiveCycleThetaValue * (1 - fiveCycleThetaValue) := by
    have hrewrite :
        fiveCycleThetaValue - fiveCycleThetaValue ^ 2 =
          fiveCycleThetaValue * (1 - fiveCycleThetaValue) := by
      ring
    rw [hrewrite]
    exact Real.sq_sqrt hnonneg
  simp [Matrix.gram_apply, fiveCycleThetaWitnessVectors, fiveCyclePentagonVectors, PiLp.inner_apply,
    Fin.sum_univ_three]
  ring_nf
  rw [hs]
  ring

/-- Helper for Example 10.6: the constant point `1 / √5` lies in `TH(C₅)`. -/
theorem fiveCycleThetaCounterexample_mem_thetaBody :
    fiveCycleThetaCounterexample ∈ TH(C₅) := by
  -- Route correction: finish the theta-side witness directly from the local Gram family.
  let Y : Matrix (Option (Fin 5)) (Option (Fin 5)) ℝ :=
    Matrix.gram ℝ fiveCycleThetaWitnessVectors
  have hdiagPentagon (v : Fin 5) :
      Matrix.gram ℝ fiveCyclePentagonVectors v v = 1 := by
    -- The diagonal pentagon entry is the cosine at angle `0`.
    rw [fiveCyclePentagonInner]
    simp
  refine ⟨Y, Matrix.IsThetaBodyWitness.mk (G := C₅) ?_ ?_ ?_ ?_ ?_⟩
  · -- The Gram matrix is automatically positive semidefinite.
    simpa [Y] using Matrix.posSemidef_gram ℝ fiveCycleThetaWitnessVectors
  · -- The `none, none` entry is the squared norm of `[1, 0, 0]`.
    change Matrix.gram ℝ fiveCycleThetaWitnessVectors none none = 1
    rw [Matrix.gram_apply]
    rw [inner_self_eq_norm_sq_to_K]
    change ‖WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ)‖ ^ 2 = 1
    have hvec : (![1, 0, 0] : Fin 3 → ℝ) = Pi.single (0 : Fin 3) (1 : ℝ) := by
      ext i
      fin_cases i <;> simp
    rw [hvec]
    change ‖PiLp.single 2 (β := fun _ : Fin 3 => ℝ) (0 : Fin 3) (1 : ℝ)‖ ^ 2 = 1
    rw [PiLp.norm_single]
    norm_num
  · intro v
    -- The `none` row recovers the constant vector `1 / √5`.
    change Matrix.gram ℝ fiveCycleThetaWitnessVectors none (some v) =
      fiveCycleThetaCounterexample v
    simp [fiveCycleThetaWitnessVectors, fiveCycleThetaCounterexample, Matrix.gram_apply,
      PiLp.inner_apply, Fin.sum_univ_three]
  · intro v
    -- The diagonal entry reduces to the scalar identity built into the witness.
    change Matrix.gram ℝ fiveCycleThetaWitnessVectors (some v) (some v) =
      fiveCycleThetaCounterexample v
    calc
      Matrix.gram ℝ fiveCycleThetaWitnessVectors (some v) (some v)
          = fiveCycleThetaValue ^ 2 +
              (fiveCycleThetaValue * (1 - fiveCycleThetaValue)) *
                Matrix.gram ℝ fiveCyclePentagonVectors v v := by
              exact fiveCycleThetaWitnessVectors_some_inner v v
      _ = fiveCycleThetaValue ^ 2 +
            (fiveCycleThetaValue * (1 - fiveCycleThetaValue)) * 1 := by
              rw [hdiagPentagon v]
      _ = fiveCycleThetaCounterexample v := by
              simpa [fiveCycleThetaCounterexample] using fiveCycleThetaValue_diag
  · intro u v huv
    -- Adjacent entries cancel to `0` once the pentagon Gram entry is normalized.
    change Matrix.gram ℝ fiveCycleThetaWitnessVectors (some u) (some v) = 0
    calc
      Matrix.gram ℝ fiveCycleThetaWitnessVectors (some u) (some v)
          = fiveCycleThetaValue ^ 2 +
              (fiveCycleThetaValue * (1 - fiveCycleThetaValue)) *
                Matrix.gram ℝ fiveCyclePentagonVectors u v := by
              exact fiveCycleThetaWitnessVectors_some_inner u v
      _ = fiveCycleThetaValue ^ 2 +
            (fiveCycleThetaValue * (1 - fiveCycleThetaValue)) *
              (-(1 + Real.sqrt 5) / 4) := by
              rw [fiveCyclePentagonAdjInner huv]
      _ = 0 := fiveCycleThetaValue_edge

/-- Helper for Example 10.6: every `N(FRAC(C₅))` point lies in the coordinate lift-project hull
for coordinate `0`. -/
theorem fiveCycleNSubsetCoordinateLiftProjectHullZero :
    N(FRAC(C₅)) ⊆ coordinate_lift_project_hull (FRAC(C₅)) 0 := by
  -- Specialize the canonical coordinate-hull containment theorem to `FRAC(C₅)` and `j = 0`.
  refine lovasz_schrijver_N_subset_coordinate_lift_project_hull (P := FRAC(C₅)) ?_ 0
  intro x hx
  rw [mem_prefix_unit_box_iff]
  rw [mem_fractional_stable_set_polytope_iff] at hx
  exact hx.1

/-- Helper for Example 10.6: every point of `FRAC(C₅)` with `x 0 = 0` satisfies
`∑ i, x i ≤ 2`. -/
lemma fiveCycleFracZeroSection_sum_le_two
    {x : Fin 5 → ℝ}
    (hx : x ∈ FRAC(C₅))
    (hx0 : x 0 = 0) :
    ∑ i : Fin 5, x i ≤ 2 := by
  -- With the `0`th coordinate fixed to `0`, the two disjoint path-edge inequalities already
  -- bound the remaining four coordinates by `2`.
  rw [mem_fractional_stable_set_polytope_iff] at hx
  rcases hx with ⟨-, hxEdge⟩
  have h12 : x 1 + x 2 ≤ 1 := hxEdge (by decide : (C₅).Adj 1 2)
  have h34 : x 3 + x 4 ≤ 1 := hxEdge (by decide : (C₅).Adj 3 4)
  simp [Fin.sum_univ_five, hx0]
  nlinarith

/-- Helper for Example 10.6: every point of `FRAC(C₅)` with `x 0 = 1` satisfies
`∑ i, x i ≤ 2`. -/
lemma fiveCycleFracOneSection_sum_le_two
    {x : Fin 5 → ℝ}
    (hx : x ∈ FRAC(C₅))
    (hx0 : x 0 = 1) :
    ∑ i : Fin 5, x i ≤ 2 := by
  -- The neighbors of vertex `0` must vanish, and the remaining edge inequality bounds the
  -- opposite pair.
  rw [mem_fractional_stable_set_polytope_iff] at hx
  rcases hx with ⟨-, hxEdge⟩
  have h01 : x 0 + x 1 ≤ 1 := hxEdge (by decide : (C₅).Adj 0 1)
  have h04 : x 0 + x 4 ≤ 1 := hxEdge (by decide : (C₅).Adj 0 4)
  have h23 : x 2 + x 3 ≤ 1 := hxEdge (by decide : (C₅).Adj 2 3)
  simp [Fin.sum_univ_five, hx0]
  nlinarith

/-- Helper for Example 10.6: every point of the coordinate lift-project hull
`coordinate_lift_project_hull (FRAC(C₅)) 0` satisfies the odd-cycle inequality
`∑ i, x i ≤ 2`. -/
lemma fiveCycleCoordinateLiftProjectHullZero_sum_le_two
    {x : Fin 5 → ℝ}
    (hx : x ∈ coordinate_lift_project_hull (FRAC(C₅)) 0) :
    ∑ i : Fin 5, x i ≤ 2 := by
  rw [coordinate_lift_project_hull_def] at hx
  let S : Set (Fin 5 → ℝ) :=
    {y : Fin 5 → ℝ | ∑ i : Fin 5, y i ≤ 2}
  have hsubset :
      ((FRAC(C₅) ∩ {y : Fin 5 → ℝ | y 0 = 0}) ∪
        (FRAC(C₅) ∩ {y : Fin 5 → ℝ | y 0 = 1})) ⊆ S := by
    intro y hy
    rcases hy with ⟨hyFrac, hy0⟩ | ⟨hyFrac, hy1⟩
    · exact fiveCycleFracZeroSection_sum_le_two hyFrac hy0
    · exact fiveCycleFracOneSection_sum_le_two hyFrac hy1
  have hconvex : Convex ℝ S := by
    intro y hy z hz a b ha hb hab
    -- The odd-cycle halfspace is convex because the coordinate sum is affine.
    dsimp [S] at hy hz ⊢
    simp [Fin.sum_univ_five] at hy hz ⊢
    nlinarith
  exact convexHull_min hsubset hconvex hx

/-- Helper for Example 10.6: the five-cycle point `fiveCycleThetaCounterexample` is not in
`N₊(FRAC(C₅))`. -/
lemma fiveCycleThetaCounterexample_not_mem_lovaszSchrijverNPlus :
    fiveCycleThetaCounterexample ∉ N₊(FRAC(C₅)) := by
  intro hxNplus
  have hxN : fiveCycleThetaCounterexample ∈ N(FRAC(C₅)) := by
    exact lovasz_schrijver_N_plus_subset_N (FRAC(C₅)) hxNplus
  have hxCoord :
      fiveCycleThetaCounterexample ∈ coordinate_lift_project_hull (FRAC(C₅)) 0 := by
    exact fiveCycleNSubsetCoordinateLiftProjectHullZero hxN
  have hsum_le_two :
      ∑ i : Fin 5, fiveCycleThetaCounterexample i ≤ 2 := by
    exact fiveCycleCoordinateLiftProjectHullZero_sum_le_two hxCoord
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  have hsqrt_pos : 0 < Real.sqrt 5 := by
    exact Real.sqrt_pos.2 (by positivity)
  have hsum_eq :
      ∑ i : Fin 5, fiveCycleThetaCounterexample i = Real.sqrt 5 := by
    simp [fiveCycleThetaCounterexample, fiveCycleThetaValue]
    field_simp [hsqrt_pos.ne']
    nlinarith
  have hsqrt_gt_two : 2 < Real.sqrt 5 := by
    nlinarith [hsqrt_sq, Real.sqrt_nonneg 5]
  rw [hsum_eq] at hsum_le_two
  linarith

/-- Helper for Example 10.6: the five-cycle gives a strict inclusion
`N₊(FRAC(C₅)) ⊂ TH(C₅)`. -/
theorem fiveCycleLovaszSchrijverNPlusSSubsetThetaBody :
    N₊(FRAC(C₅)) ⊂ TH(C₅) := by
  rw [Set.ssubset_def]
  -- Combine the inclusion already proved above with the explicit counterexample point.
  refine ⟨lovasz_schrijver_N_plus_frac_subset_theta_body (G := C₅), ?_⟩
  intro hsubset
  exact
    fiveCycleThetaCounterexample_not_mem_lovaszSchrijverNPlus
      (hsubset fiveCycleThetaCounterexample_mem_thetaBody)

/-- Example 10.6 (2). The inclusion `N₊(FRAC(G)) ⊆ TH(G)` is strict for some finite graph. The
canonical Section 10.3 owner is stated on `Fin n`, so the existence statement is presented in
that finite coordinate model. -/
theorem exists_finite_graph_with_strict_lovasz_schrijver_N_plus_frac_subset_theta_body :
    ∃ n : ℕ, ∃ H : SimpleGraph (Fin n),
      N₊(FRAC(H)) ⊂ TH(H) := by
  -- Route correction: instead of importing later Exercise 10.8, build the strictness witness
  -- locally from the five-cycle and the explicit point `1 / √5`.
  exact ⟨5, C₅, fiveCycleLovaszSchrijverNPlusSSubsetThetaBody⟩

end Example_10_6_Strictness

section Example_10_6_Transform

variable {V : Type u}

/-- Third claim of Example 10.6. The change of variables `χ_i = (1 + x_i) / 2` sends every
`±1`-valued vector to a binary vector, matching the `[0,1]^V` ambient polytope used for the
Goemans-Williamson
semidefinite bound. -/
theorem sign_to_binary_transform_eq_zero_or_one_of_pm_one
    (x : V → ℝ) (hx : ∀ i, x i = -1 ∨ x i = 1) (i : V) :
    sign_to_binary_transform x i = 0 ∨ sign_to_binary_transform x i = 1 := by
  rcases hx i with hxi | hxi
  · left
    simp [sign_to_binary_transform, hxi]
  · right
    simp [sign_to_binary_transform, hxi]

end Example_10_6_Transform
