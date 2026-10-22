/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_extra_3

noncomputable section

open Matrix
open EuclideanSpace

-- Domain sampling:
-- * primary domain: linear inequality alternatives and cone duality in finite-dimensional real
--   inner-product spaces
-- * sampled owners: Chapter 1 `halfSpaceIntersection`, mathlib `ConvexCone.positive`,
--   mathlib `ConvexCone.mem_map`, the matrix-model bridge `Matrix.toEuclideanLin`,
--   and the coordinate equivalence `EuclideanSpace.equiv`
-- * source-facing layer: `farkasSystem1` / `farkasSystem2` are the textbook systems
--   `Ax ≤ 0, ⟪c, x⟫ > 0` and `Aᵀ y = c, y ≥ 0`
-- * core/canonical layer: `halfSpaceIntersection (matrixRowFamily A)` and the image of
--   `ConvexCone.positive ℝ DualCoords` under the canonical transpose-coordinate action
-- * bridge/view layer: `matrixRowFamily`, `matrixTransposeCoordMap`, and the equivalence lemmas
--   relating the textbook systems to those canonical owners
-- * primitive data: the matrix `A` and the right-hand-side vector `c`
-- * derived API: the two Farkas alternatives and the exclusion/existence theorems

section Theorem1322

variable {m n : ℕ}

local notation "PrimalPoint" => EuclideanSpace ℝ (Fin n)
local notation "DualCoords" => Fin m → ℝ

/-- The rows of `A`, viewed as the half-space normals that cut out the system `Ax ≤ 0`. -/
abbrev matrixRowFamily (A : Matrix (Fin m) (Fin n) ℝ) : Fin m → PrimalPoint :=
  fun i ↦ A.toEuclideanLin.adjoint (EuclideanSpace.basisFun (Fin m) ℝ i)

/-- Evaluating the `i`-th matrix-row normal against `x` recovers the `i`-th coordinate of `Ax`. -/
theorem inner_matrixRowFamily_eq_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (x : PrimalPoint) (i : Fin m) :
    inner ℝ x (matrixRowFamily A i) = A.toEuclideanLin x i := by
  have hbasis :
      inner ℝ (A.toEuclideanLin x) (EuclideanSpace.basisFun (Fin m) ℝ i) =
        A.toEuclideanLin x i := by
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
    simp
  simpa [matrixRowFamily] using
    (LinearMap.adjoint_inner_right A.toEuclideanLin x
      (EuclideanSpace.basisFun (Fin m) ℝ i)).trans hbasis

/-- The coordinate inequalities `Ax ≤ 0` are exactly membership in the canonical half-space
intersection cut out by the rows of `A`. -/
theorem mem_halfSpaceIntersection_matrixRowFamily_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (x : PrimalPoint) :
    x ∈ halfSpaceIntersection (matrixRowFamily A) ↔
      ∀ i : Fin m, A.toEuclideanLin x i ≤ 0 := by
  constructor
  · intro hx i
    simpa [inner_matrixRowFamily_eq_apply A x i] using hx i
  · intro hx i
    simpa [inner_matrixRowFamily_eq_apply A x i] using hx i

/-- System 1 in Farkas' lemma: there exists `x` with coordinatewise `Ax ≤ 0` and
`inner ℝ c x > 0`. -/
def farkasSystem1 (A : Matrix (Fin m) (Fin n) ℝ) (c : PrimalPoint) : Prop :=
  ∃ x : PrimalPoint, (∀ i : Fin m, A.toEuclideanLin x i ≤ 0) ∧ 0 < inner ℝ c x

/-- The transpose action of `A` on coordinate vectors in `ℝ^m`, transported into the Euclidean
model used for the primal space. -/
abbrev matrixTransposeCoordMap (A : Matrix (Fin m) (Fin n) ℝ) : DualCoords →ₗ[ℝ] PrimalPoint :=
  Aᵀ.toEuclideanLin.comp (equiv (Fin m) ℝ).symm.toLinearMap

@[simp] theorem matrixTransposeCoordMap_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (y : DualCoords) :
    matrixTransposeCoordMap A y =
      Aᵀ.toEuclideanLin ((equiv (Fin m) ℝ).symm y) :=
  rfl

/-- Helper for Chapter01 Theorem 1.3.22: the transpose-coordinate map sends the `i`-th standard
coordinate vector to the `i`-th row normal. -/
theorem matrixTransposeCoordMap_basisFun_eq_matrixRowFamily
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    matrixTransposeCoordMap A (EuclideanSpace.basisFun (Fin m) ℝ i) = matrixRowFamily A i := by
  -- Expand the coordinate equivalence on the standard basis vector before comparing the two
  -- adjoint descriptions of the same row normal.
  have hAdj : Aᵀ.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A)
  have hBasis :
      (equiv (Fin m) ℝ).symm (EuclideanSpace.basisFun (Fin m) ℝ i) =
        EuclideanSpace.basisFun (Fin m) ℝ i := by
    ext j
    simp [EuclideanSpace.basisFun_apply]
  calc
    matrixTransposeCoordMap A (EuclideanSpace.basisFun (Fin m) ℝ i)
        = Aᵀ.toEuclideanLin ((equiv (Fin m) ℝ).symm (EuclideanSpace.basisFun (Fin m) ℝ i)) := by
            rfl
    _ = Aᵀ.toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i) := by
          exact congrArg Aᵀ.toEuclideanLin hBasis
    _ = matrixRowFamily A i := by
          simpa [matrixRowFamily] using
            congrArg
              (fun f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] PrimalPoint ↦
                f (EuclideanSpace.basisFun (Fin m) ℝ i))
              hAdj

/-- Helper for Chapter01 Theorem 1.3.22: the transpose-coordinate map is the finite conical
combination of the row normals with coefficients given by the input coordinates. -/
theorem matrixTransposeCoordMap_eq_sum_rows
    (A : Matrix (Fin m) (Fin n) ℝ) (y : DualCoords) :
    matrixTransposeCoordMap A y = ∑ i : Fin m, y i • matrixRowFamily A i := by
  -- Expand `y` in the standard basis of `ℝ^m`, then transport each basis vector through the
  -- transpose-coordinate map.
  have hy_repr0 : y = ∑ i : Fin m, Pi.single i (y i) := by
    simpa using (LinearMap.sum_single_apply (ι := Fin m) (v := y)).symm
  rw [hy_repr0, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hsingle :
      (Pi.single i (y i) : DualCoords) = y i • EuclideanSpace.basisFun (Fin m) ℝ i := by
    ext j
    by_cases h : j = i
    · subst h
      simp [EuclideanSpace.basisFun_apply]
    · simp [EuclideanSpace.basisFun_apply, h]
  have hyi : (∑ j : Fin m, Pi.single j (y j)) i = y i := by
    exact congrArg (fun v : DualCoords => v i) hy_repr0.symm
  rw [hsingle, map_smul, matrixTransposeCoordMap_basisFun_eq_matrixRowFamily, hyi]

/-- Bridge from the source-facing System 1 to the chapter owner `halfSpaceIntersection`. -/
theorem farkasSystem1_iff_halfSpace
    (A : Matrix (Fin m) (Fin n) ℝ) (c : PrimalPoint) :
    farkasSystem1 A c ↔
      ∃ x : PrimalPoint, x ∈ halfSpaceIntersection (matrixRowFamily A) ∧ 0 < inner ℝ c x := by
  constructor
  · rintro ⟨x, hx, hcx⟩
    exact ⟨x, (mem_halfSpaceIntersection_matrixRowFamily_iff A x).2 hx, hcx⟩
  · rintro ⟨x, hx, hcx⟩
    exact ⟨x, (mem_halfSpaceIntersection_matrixRowFamily_iff A x).1 hx, hcx⟩

/-- System 2 in Farkas' lemma: there exists a coordinate vector `y : ℝ^m` with `Aᵀ y = c` and
coordinatewise `0 ≤ y`. -/
def farkasSystem2 (A : Matrix (Fin m) (Fin n) ℝ) (c : PrimalPoint) : Prop :=
  ∃ y : DualCoords, matrixTransposeCoordMap A y = c ∧ 0 ≤ y

/-- Helper for Chapter01 Theorem 1.3.22: the conic hull of the row normals is the canonical cone
owner for the System-2 feasible set. -/
abbrev rowCone (A : Matrix (Fin m) (Fin n) ℝ) : PointedCone ℝ PrimalPoint :=
  PointedCone.hull ℝ (Set.range (matrixRowFamily A))

/-- Bridge from the source-facing System 2 to the canonical positive-cone image formulation. -/
theorem farkasSystem2_iff_positiveConeMap
    (A : Matrix (Fin m) (Fin n) ℝ) (c : PrimalPoint) :
    farkasSystem2 A c ↔
      c ∈ (ConvexCone.positive ℝ DualCoords).map (matrixTransposeCoordMap A) := by
  constructor
  · rintro ⟨y, hyc, hy⟩
    exact (ConvexCone.mem_map).2 ⟨y, by simpa using hy, hyc⟩
  · intro hc
    rcases (ConvexCone.mem_map).1 hc with ⟨y, hy, hyc⟩
    exact ⟨y, hyc, by simpa using hy⟩

/-- Helper for Chapter01 Theorem 1.3.22: mapping the nonnegative coordinate cone by
`matrixTransposeCoordMap A` produces exactly the cone generated by the row normals of `A`. -/
lemma positiveConeMap_eq_rowCone
    (A : Matrix (Fin m) (Fin n) ℝ) :
    PointedCone.map (matrixTransposeCoordMap A)
      (PointedCone.positive ℝ DualCoords) = rowCone A := by
  apply le_antisymm
  · intro x hx
    rcases (PointedCone.mem_map).1 hx with ⟨y, hy, rfl⟩
    -- Rewrite the image as the explicit conical combination of the row normals.
    have hdecomp :
        matrixTransposeCoordMap A y = ∑ i : Fin m, y i • matrixRowFamily A i :=
      matrixTransposeCoordMap_eq_sum_rows A y
    rw [hdecomp]
    -- Each basis image already lies in the hull, so the whole conical sum stays in `rowCone A`.
    have hsum_mem : (∑ i : Fin m, y i • matrixRowFamily A i) ∈ rowCone A := by
      induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
      | empty =>
          simp
      | insert i s hi hs =>
          have hgen : matrixRowFamily A i ∈ rowCone A :=
            PointedCone.subset_hull ⟨i, rfl⟩
          have hsmul : y i • matrixRowFamily A i ∈ rowCone A :=
            (rowCone A).smul_mem (hy i) hgen
          simpa [Finset.sum_insert hi] using (rowCone A).add_mem hsmul hs
    exact hsum_mem
  · -- The image cone contains every row generator, so by hull minimality it contains `rowCone A`.
    show rowCone A ≤ PointedCone.map (matrixTransposeCoordMap A) (PointedCone.positive ℝ DualCoords)
    refine Submodule.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨i, rfl⟩
    refine (PointedCone.mem_map).2 ?_
    refine ⟨(Pi.single i (1 : ℝ) : DualCoords), ?_, ?_⟩
    · change 0 ≤ (Pi.single i (1 : ℝ) : DualCoords)
      intro j
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    · have hbasis :
          (Pi.single i (1 : ℝ) : DualCoords) = EuclideanSpace.basisFun (Fin m) ℝ i := by
        ext j
        simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
      rw [hbasis]
      exact matrixTransposeCoordMap_basisFun_eq_matrixRowFamily A i

/-- Helper for Chapter01 Theorem 1.3.22: System 2 is exactly membership in the row cone of `A`. -/
theorem farkasSystem2_iff_rowCone
    (A : Matrix (Fin m) (Fin n) ℝ) (c : PrimalPoint) :
    farkasSystem2 A c ↔ c ∈ (rowCone A : Set PrimalPoint) := by
  -- Replace the coordinate-positive image owner by the row-cone owner once and for all.
  rw [farkasSystem2_iff_positiveConeMap]
  calc
    c ∈ ((ConvexCone.positive ℝ DualCoords).map (matrixTransposeCoordMap A) : Set PrimalPoint)
        ↔ c ∈ (PointedCone.map (matrixTransposeCoordMap A) (PointedCone.positive ℝ DualCoords) :
          Set PrimalPoint) := by
            simp
    _ ↔ c ∈ (rowCone A : Set PrimalPoint) := by
          rw [positiveConeMap_eq_rowCone A]

/-- Helper for Chapter01 Theorem 1.3.22: the matrix half-space owner is exactly the polar cone of
the row generators. -/
lemma halfSpaceIntersection_eq_polarCone_rows
    (A : Matrix (Fin m) (Fin n) ℝ) :
    halfSpaceIntersection (matrixRowFamily A) =
      (polarCone (Set.range (matrixRowFamily A)) : Set PrimalPoint) := by
  ext x
  constructor
  · intro hx
    -- Unfold the polar-cone inequalities on each row generator.
    refine mem_polarCone_iff.mpr ?_
    intro z hz
    rcases hz with ⟨i, rfl⟩
    simpa [inner_matrixRowFamily_eq_apply A x i] using
      (mem_halfSpaceIntersection_matrixRowFamily_iff A x).1 hx i
  · intro hx
    -- Specialize the polar inequalities back to the indexed row family.
    refine (mem_halfSpaceIntersection_matrixRowFamily_iff A x).2 ?_
    intro i
    simpa [inner_matrixRowFamily_eq_apply A x i] using
      (mem_polarCone_iff.mp hx) _ ⟨i, rfl⟩

/-- Helper for Chapter01 Theorem 1.3.22: every conical combination of rows satisfies the polar
inequalities cut out by the associated half-space intersection. -/
lemma rowCone_le_polarCone_halfSpace
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (rowCone A : Set PrimalPoint) ⊆
      (polarCone (halfSpaceIntersection (matrixRowFamily A)) : Set PrimalPoint) := by
  intro z hz
  refine mem_polarCone_iff.mpr ?_
  intro x hx
  -- Prove the defining inequality by spanning induction over the row generators.
  induction hz using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨i, rfl⟩
      have hrow : inner ℝ x (matrixRowFamily A i) ≤ 0 := by
        simpa [inner_matrixRowFamily_eq_apply A x i] using
          (mem_halfSpaceIntersection_matrixRowFamily_iff A x).1 hx i
      simpa [real_inner_comm] using hrow
  | zero =>
      simp
  | add y z _hy _hz hy hz =>
      simpa [inner_add_left] using add_nonpos hy hz
  | smul a y _hy hy =>
      change inner ℝ ((a : ℝ) • y) x ≤ 0
      rw [real_inner_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos a.2 hy

/-- Helper for Chapter01 Theorem 1.3.22: the row cone has exactly the expected polar half-space
description. -/
lemma polarCone_rowCone_eq_halfSpaceIntersection
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (polarCone (rowCone A : Set PrimalPoint) : Set PrimalPoint) =
      halfSpaceIntersection (matrixRowFamily A) := by
  refine Set.Subset.antisymm ?_ ?_
  · -- Larger primal cones induce smaller polar cones, so it suffices to restrict to the generators.
    rw [halfSpaceIntersection_eq_polarCone_rows A]
    exact polarCone_anti PointedCone.subset_hull
  · -- The reverse inclusion comes from polarizing the already-proved row-cone containment.
    have hrow :
        (rowCone A : Set PrimalPoint) ⊆
          (polarCone (halfSpaceIntersection (matrixRowFamily A)) : Set PrimalPoint) :=
      rowCone_le_polarCone_halfSpace A
    have hdouble :
        (polarCone (polarCone (halfSpaceIntersection (matrixRowFamily A)) : Set PrimalPoint) :
          Set PrimalPoint) =
          halfSpaceIntersection (matrixRowFamily A) := by
      rw [halfSpaceIntersection_eq_polarCone_rows A]
      -- Rewrite the local polar convention to the canonical inner dual before applying the bundled
      -- proper-cone bipolar theorem.
      rw [polarCone, neg_polarCone_eq_innerDual]
      exact congrArg (fun C : ProperCone ℝ PrimalPoint => (C : Set PrimalPoint))
        (ProperCone.innerDual_innerDual (polarCone (Set.range (matrixRowFamily A))))
    have hanti :
        (polarCone (polarCone (halfSpaceIntersection (matrixRowFamily A)) : Set PrimalPoint) :
          Set PrimalPoint) ⊆
          (polarCone (rowCone A : Set PrimalPoint) : Set PrimalPoint) :=
      polarCone_anti hrow
    simpa [hdouble] using hanti

/-- Helper for Chapter01 Theorem 1.3.22: taking the polar cone commutes with topological closure,
because the defining inequalities are preserved under limits. -/
lemma sunYuanPolarCone_closure_eq (S : Set PrimalPoint) :
    (polarCone (closure S) : Set PrimalPoint) = polarCone S := by
  ext p
  constructor
  · intro hp
    -- Restrict the defining inequalities from `closure S` back to `S`.
    exact mem_polarCone_iff.mpr fun x hx ↦
      (mem_polarCone_iff.mp hp) x (subset_closure hx)
  · intro hp
    -- Extend the defining inequalities from `S` to `closure S` using closedness of the half-space.
    refine mem_polarCone_iff.mpr ?_
    have hclosed :
        IsClosed (((fun x : PrimalPoint ↦ inner ℝ p x) ⁻¹' Set.Iic (0 : ℝ)) : Set PrimalPoint) :=
      isClosed_Iic.preimage (continuous_const.inner continuous_id)
    have hs : S ⊆ ((fun x : PrimalPoint ↦ inner ℝ p x) ⁻¹' Set.Iic (0 : ℝ)) := by
      intro x hx
      exact (mem_polarCone_iff.mp hp) x hx
    have hclosure : closure S ⊆ ((fun x : PrimalPoint ↦ inner ℝ p x) ⁻¹' Set.Iic (0 : ℝ)) :=
      closure_minimal hs hclosed
    intro x hx
    exact hclosure hx

/-- Helper for Chapter01 Theorem 1.3.22: the closure of the row cone is the double polar of the
row half-space owner. This isolates the remaining gap to showing that the finitely generated row
cone already equals its closure. -/
lemma closure_rowCone_eq_doublePolar
    (A : Matrix (Fin m) (Fin n) ℝ) :
    closure (rowCone A : Set PrimalPoint) =
      (polarCone (halfSpaceIntersection (matrixRowFamily A)) : Set PrimalPoint) := by
  let C0 : ConvexCone ℝ PrimalPoint := ((rowCone A).closure : ConvexCone ℝ PrimalPoint)
  have hC0 : Set.Nonempty (C0 : Set PrimalPoint) ∧ IsClosed (C0 : Set PrimalPoint) := by
    constructor
    · refine ⟨0, ?_⟩
      change 0 ∈ closure (rowCone A : Set PrimalPoint)
      exact subset_closure (show (0 : PrimalPoint) ∈ rowCone A from (rowCone A).zero_mem)
    · change IsClosed (closure (rowCone A : Set PrimalPoint))
      exact isClosed_closure
  obtain ⟨C, hCeq⟩ := CanLift.prf (β := ProperCone ℝ PrimalPoint) C0 hC0
  have hCset : (C : Set PrimalPoint) = closure (rowCone A : Set PrimalPoint) := by
    ext z
    change z ∈ (C : ConvexCone ℝ PrimalPoint) ↔ z ∈ closure (rowCone A : Set PrimalPoint)
    rw [hCeq]
    simp [C0]
  have hpolar :
      (polarCone (C : Set PrimalPoint) : Set PrimalPoint) =
        halfSpaceIntersection (matrixRowFamily A) := by
    calc
      (polarCone (C : Set PrimalPoint) : Set PrimalPoint)
          = (polarCone (closure (rowCone A : Set PrimalPoint)) : Set PrimalPoint) := by
              rw [hCset]
      _ = (polarCone (rowCone A : Set PrimalPoint) : Set PrimalPoint) := by
            rw [sunYuanPolarCone_closure_eq]
      _ = halfSpaceIntersection (matrixRowFamily A) := by
            rw [polarCone_rowCone_eq_halfSpaceIntersection A]
  calc
    closure (rowCone A : Set PrimalPoint)
        = (C : Set PrimalPoint) := by
            rw [hCset]
    _ = (polarCone ((polarCone (C : Set PrimalPoint) : Set PrimalPoint)) : Set PrimalPoint) := by
          symm
          simpa using (polarCone_polarCone_eq_of_properCone C)
    _ = (polarCone (halfSpaceIntersection (matrixRowFamily A)) : Set PrimalPoint) := by
          rw [hpolar]

/-- Helper for Chapter01 Theorem 1.3.22: the row cone is finitely generated by the finite family of
matrix rows. -/
lemma rowCone_fg
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (rowCone A).FG := by
  -- The row cone is the conic hull of a `Fin m`-indexed family, so the generators are finite.
  simpa [rowCone] using Submodule.fg_span (Set.finite_range (matrixRowFamily A))

/-- Helper for Chapter01 Theorem 1.3.22: the cone generated by a fixed row subset is the image of
the coordinate cone on that subset. -/
abbrev rowSubsetMap
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) : (s → ℝ) →ₗ[ℝ] PrimalPoint :=
  Fintype.linearCombination ℝ (fun i : s ↦ matrixRowFamily A i)

/-- Helper for Chapter01 Theorem 1.3.22: linear independence of the chosen rows makes the
coordinate map on that subset injective. -/
lemma rowSubsetMap_injective
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m))
    (hs : LinearIndependent ℝ (fun i : s ↦ matrixRowFamily A i)) :
    Function.Injective (rowSubsetMap A s) := by
  intro g h hEq
  apply funext
  intro i
  -- Subtract the two coefficient vectors and use row independence on the resulting zero
  -- combination.
  have hsum : ∑ j : s, (g j - h j) • matrixRowFamily A j = 0 := by
    calc
      ∑ j : s, (g j - h j) • matrixRowFamily A j
          = (∑ j : s, g j • matrixRowFamily A j) + (∑ j : s, (-h j) • matrixRowFamily A j) := by
              simp [sub_eq_add_neg, add_smul, Finset.sum_add_distrib]
      _ = (∑ j : s, g j • matrixRowFamily A j) - ∑ j : s, h j • matrixRowFamily A j := by
            simp [sub_eq_add_neg]
      _ = 0 := by
            simpa [rowSubsetMap, Fintype.linearCombination_apply] using sub_eq_zero.mpr hEq
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hs (fun j ↦ g j - h j) hsum i)

/-- Helper for Chapter01 Theorem 1.3.22: the nonnegative coordinate cone on a linearly independent
row subset has closed image. -/
lemma rowSubsetCone_isClosed
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m))
    (hs : LinearIndependent ℝ (fun i : s ↦ matrixRowFamily A i)) :
    IsClosed (Set.image (rowSubsetMap A s) {g : s → ℝ | 0 ≤ g}) := by
  -- The source orthant is coordinatewise closed.
  have hclosedDom : IsClosed ({g : s → ℝ | 0 ≤ g} : Set (s → ℝ)) := by
    rw [show ({g : s → ℝ | 0 ≤ g} : Set (s → ℝ)) = ⋂ i : s, {g : s → ℝ | 0 ≤ g i} by
      ext g
      simp [Pi.le_def]]
    refine isClosed_iInter ?_
    intro i
    exact isClosed_Ici.preimage (continuous_apply i)
  -- On an independent row family, the coordinate map is a closed embedding.
  have hclosedEmb : Topology.IsClosedEmbedding (rowSubsetMap A s) := by
    exact LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr (rowSubsetMap_injective A s hs))
  simpa [Set.image_eq_range] using hclosedEmb.isClosedMap _ hclosedDom

/-- Helper for Chapter01 Theorem 1.3.22: extend a coefficient vector on a row subset by zero
outside the chosen subset. -/
abbrev sunYuanExtendByZero (s : Finset (Fin m)) (g : s → ℝ) : DualCoords :=
  fun i ↦ if h : i ∈ s then g ⟨i, h⟩ else 0

/-- Helper for Chapter01 Theorem 1.3.22: the subset coordinate map agrees with the full
transpose-coordinate map after zero extension. -/
lemma rowSubsetMap_eq_matrixTransposeCoordMap_sunYuanExtendByZero
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) (g : s → ℝ) :
    rowSubsetMap A s g = matrixTransposeCoordMap A (sunYuanExtendByZero s g) := by
  -- Rewrite the full map as a sum over all rows, then discard the zero coefficients off `s`.
  rw [matrixTransposeCoordMap_eq_sum_rows, rowSubsetMap, Fintype.linearCombination_apply]
  have hsum_univ :
      (∑ x : Fin m, sunYuanExtendByZero s g x • matrixRowFamily A x) =
        ∑ x ∈ s, sunYuanExtendByZero s g x • matrixRowFamily A x := by
    classical
    show Finset.univ.sum (fun x ↦ sunYuanExtendByZero s g x • matrixRowFamily A x) = _
    symm
    refine Finset.sum_subset ?_ ?_
    · simp
    · intro x _ hx
      simp [sunYuanExtendByZero, hx]
  rw [hsum_univ]
  simp +contextual [sunYuanExtendByZero, ← s.sum_attach]

/-- Helper for Chapter01 Theorem 1.3.22: if a coefficient vector vanishes off `s`, then
restricting it to `s` and re-extending by zero does not change the transpose-coordinate image. -/
lemma rowSubsetMap_eq_matrixTransposeCoordMap_of_zero_off_subset
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) (y : DualCoords)
    (hy : ∀ i, i ∉ s → y i = 0) :
    rowSubsetMap A s (fun i : s ↦ y i) = matrixTransposeCoordMap A y := by
  -- Rewrite the restricted coefficients through zero extension and then compare coordinatewise.
  rw [rowSubsetMap_eq_matrixTransposeCoordMap_sunYuanExtendByZero]
  congr
  ext i
  by_cases hi : i ∈ s
  · simp [sunYuanExtendByZero, hi]
  · simp [sunYuanExtendByZero, hi, hy i hi]

/-- Helper for Chapter01 Theorem 1.3.22: a dependent row subset carries a nontrivial supported
relation that can be oriented to have a positive coefficient. -/
lemma dependentRowSubset_hasPositiveRelation
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m))
    (hs : ¬ LinearIndependent ℝ (fun i : s ↦ matrixRowFamily A i)) :
    ∃ a : DualCoords, (∀ i, i ∉ s → a i = 0) ∧
      matrixTransposeCoordMap A a = 0 ∧ ∃ j ∈ s, 0 < a j := by
  -- Extract a nontrivial supported dependence relation from the dependent row family.
  have hs' : ¬ LinearIndepOn ℝ (matrixRowFamily A) (↑s : Set (Fin m)) := by
    simpa [LinearIndepOn] using hs
  rcases (linearDepOn_iff').mp hs' with ⟨f, hf_supported, hf_zero, hf_ne⟩
  let a0 : DualCoords := fun i ↦ f i
  have ha0_supported : ∀ i, i ∉ s → a0 i = 0 := by
    intro i hi
    exact (Finsupp.mem_supported' ℝ f).mp hf_supported i hi
  have ha0_zero : matrixTransposeCoordMap A a0 = 0 := by
    -- Transport the finitely supported relation to the `Fin m → ℝ` model used by System 2.
    have ha0_finsupp :
        (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin m)).symm a0 = f := by
      ext i
      rfl
    have ha0_fintype :
        Fintype.linearCombination ℝ (matrixRowFamily A) a0 = 0 := by
      rw [← Finsupp.linearCombination_eq_fintype_linearCombination_apply
        (R := ℝ) (v := matrixRowFamily A) (x := a0)]
      rw [ha0_finsupp]
      exact hf_zero
    rw [matrixTransposeCoordMap_eq_sum_rows]
    simpa [Fintype.linearCombination_apply] using ha0_fintype
  have hne : ∃ i : Fin m, f i ≠ 0 := by
    by_contra h
    apply hf_ne
    ext i
    exact by
      by_contra hi
      exact h ⟨i, hi⟩
  rcases hne with ⟨i, hi_ne⟩
  have his : i ∈ s := by
    exact (Finsupp.mem_supported ℝ f).mp hf_supported <|
      by simpa [Finsupp.mem_support_iff] using hi_ne
  by_cases hi_pos : 0 < f i
  · exact ⟨a0, ha0_supported, ha0_zero, ⟨i, his, hi_pos⟩⟩
  · have hi_neg : f i < 0 := lt_of_le_of_ne (not_lt.mp hi_pos) hi_ne
    refine ⟨-a0, ?_, ?_, ?_⟩
    · intro j hj
      simp [a0, ha0_supported j hj]
    · simpa [map_neg] using congrArg (fun z ↦ -z) ha0_zero
    · refine ⟨i, his, ?_⟩
      simpa [a0] using neg_pos.mpr hi_neg

/-- Helper for Chapter01 Theorem 1.3.22: every nonnegative row combination supported inside `s`
can be compressed to a linearly independent row subset of `s`. -/
lemma exists_independentRowRepresentation_aux
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∀ s : Finset (Fin m), ∀ y : DualCoords, 0 ≤ y →
      (∀ i, y i ≠ 0 → i ∈ s) →
      ∃ t ⊆ s, LinearIndependent ℝ (fun i : t ↦ matrixRowFamily A i) ∧
        ∃ g : t → ℝ, 0 ≤ g ∧ rowSubsetMap A t g = matrixTransposeCoordMap A y := by
  classical
  intro s
  refine s.strongInductionOn ?_
  intro s ih y hy hsupport
  by_cases hs : LinearIndependent ℝ (fun i : s ↦ matrixRowFamily A i)
  · -- If the current ambient subset is already independent, just restrict `y` to it.
    refine ⟨s, by intro i hi; exact hi, hs, ?_⟩
    refine ⟨fun i : s ↦ y i, ?_, ?_⟩
    · intro i
      exact hy i
    · -- The coefficients already vanish off `s`, so the subset map matches the original image.
      apply rowSubsetMap_eq_matrixTransposeCoordMap_of_zero_off_subset
      intro i hi
      by_cases hyi : y i = 0
      · exact hyi
      · exact (hi (hsupport i hyi)).elim
  · -- Otherwise extract a supported relation and eliminate one positive coefficient by
    -- minimal ratio.
    rcases dependentRowSubset_hasPositiveRelation A s hs with ⟨a, ha_out, ha_zero, hpos⟩
    let p : Finset (Fin m) := s.filter (fun i ↦ 0 < a i)
    rcases hpos with ⟨j, hjs, hja⟩
    have hp_nonempty : p.Nonempty := ⟨j, by simp [p, hjs, hja]⟩
    obtain ⟨j0, hj0p, hj0_min⟩ := p.exists_min_image (fun i ↦ y i / a i) hp_nonempty
    have hj0s : j0 ∈ s := (Finset.mem_filter.mp hj0p).1
    have hj0a : 0 < a j0 := (Finset.mem_filter.mp hj0p).2
    let t : ℝ := y j0 / a j0
    let y' : DualCoords := fun i ↦ y i - t * a i
    have ht_nonneg : 0 ≤ t := div_nonneg (hy j0) (le_of_lt hj0a)
    have hy'_nonneg : 0 ≤ y' := by
      intro i
      by_cases hi_pos : 0 < a i
      · have his : i ∈ s := by
          by_contra his
          have : a i = 0 := ha_out i his
          linarith
        have hip : i ∈ p := by
          simp [p, his, hi_pos]
        have hratio : t ≤ y i / a i := hj0_min i hip
        have hmul : t * a i ≤ y i := (le_div_iff₀ hi_pos).mp hratio
        exact sub_nonneg.mpr hmul
      · have hai : a i ≤ 0 := le_of_not_gt hi_pos
        have hmul : t * a i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht_nonneg hai
        simpa [y', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          add_nonneg (hy i) (neg_nonneg.mpr hmul)
    have hy'j0 : y' j0 = 0 := by
      -- The minimizing index is forced to vanish after subtracting the chosen multiple.
      have hmul : t * a j0 = y j0 := by
        dsimp [t]
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hj0a.ne', mul_one]
      simp [y', hmul]
    have hsupport' : ∀ i, y' i ≠ 0 → i ∈ s.erase j0 := by
      intro i hi
      by_cases his : i ∈ s
      · by_cases hij : i = j0
        · subst hij
          exact (hi hy'j0).elim
        · exact Finset.mem_erase.mpr ⟨hij, his⟩
      · have hyi : y i = 0 := by
          by_cases hyi : y i = 0
          · exact hyi
          · exact (his (hsupport i hyi)).elim
        have hai : a i = 0 := ha_out i his
        have : y' i = 0 := by simp [y', hyi, hai]
        exact (hi this).elim
    have hy'_map : matrixTransposeCoordMap A y' = matrixTransposeCoordMap A y := by
      -- The supported relation maps to zero, so subtracting it preserves the represented point.
      calc
        matrixTransposeCoordMap A y'
            = matrixTransposeCoordMap A y - t • matrixTransposeCoordMap A a := by
                change matrixTransposeCoordMap A (y - t • a) =
                  matrixTransposeCoordMap A y - t • matrixTransposeCoordMap A a
                rw [map_sub, map_smul]
        _ = matrixTransposeCoordMap A y := by simp [ha_zero]
    rcases ih (s.erase j0) (Finset.erase_ssubset hj0s) y' hy'_nonneg hsupport' with
      ⟨u, hu_sub, hu_indep, g, hg_nonneg, hg_eq⟩
    refine ⟨u, hu_sub.trans (Finset.erase_subset _ _), hu_indep, g, hg_nonneg, ?_⟩
    calc
      rowSubsetMap A u g = matrixTransposeCoordMap A y' := hg_eq
      _ = matrixTransposeCoordMap A y := hy'_map

/-- Helper for Chapter01 Theorem 1.3.22: every nonnegative row combination can be rewritten using
only a linearly independent row subset. -/
lemma exists_independentRowRepresentation
    (A : Matrix (Fin m) (Fin n) ℝ) (y : DualCoords) (hy : 0 ≤ y) :
    ∃ s : Finset (Fin m), LinearIndependent ℝ (fun i : s ↦ matrixRowFamily A i) ∧
      ∃ g : s → ℝ, 0 ≤ g ∧ rowSubsetMap A s g = matrixTransposeCoordMap A y := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter (fun i ↦ y i ≠ 0)
  have hsupp : ∀ i, y i ≠ 0 → i ∈ s := by
    intro i hi
    simp [s, hi]
  rcases exists_independentRowRepresentation_aux A s y hy hsupp with
    ⟨t, -, ht_indep, g, hg_nonneg, hg_eq⟩
  exact ⟨t, ht_indep, g, hg_nonneg, hg_eq⟩

/-- Helper for Chapter01 Theorem 1.3.22: the source-facing positive-orthant image of the transpose
coordinate map is closed. -/
lemma matrixTransposePositiveImage_isClosed
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsClosed
      ((PointedCone.map (matrixTransposeCoordMap A) (PointedCone.positive ℝ DualCoords) :
        Set PrimalPoint)) := by
  classical
  -- Route correction: instead of searching for a global `FG -> closed` cone theorem, decompose the
  -- image into finitely many closed pieces indexed by linearly independent row subsets.
  have hdecomp :
      ((PointedCone.map (matrixTransposeCoordMap A) (PointedCone.positive ℝ DualCoords) :
        Set PrimalPoint)) =
        ⋃ s : Finset (Fin m),
          if hs : LinearIndependent ℝ (fun i : s ↦ matrixRowFamily A i) then
            Set.image (rowSubsetMap A s) {g : s → ℝ | 0 ≤ g}
          else
            (∅ : Set PrimalPoint) := by
    ext x
    constructor
    · intro hx
      rcases (PointedCone.mem_map).1 hx with ⟨y, hy, rfl⟩
      -- Replace the raw coefficient vector by one with linearly independent row support.
      rcases exists_independentRowRepresentation A y (by simpa using hy) with ⟨s, hs, g, hg, hEq⟩
      refine Set.mem_iUnion.2 ⟨s, ?_⟩
      rw [dif_pos hs]
      exact ⟨g, hg, hEq⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨s, hsx⟩
      by_cases hs : LinearIndependent ℝ (fun i : s ↦ matrixRowFamily A i)
      · rw [dif_pos hs] at hsx
        rcases hsx with ⟨g, hg, rfl⟩
        -- Zero-extend the subset coefficients back to `ℝ^m` to recover a point of the original
        -- image cone.
        refine (PointedCone.mem_map).2 ?_
        refine ⟨sunYuanExtendByZero s g, ?_, ?_⟩
        · intro i
          by_cases hi : i ∈ s
          · simpa [sunYuanExtendByZero, hi] using hg ⟨i, hi⟩
          · simp [sunYuanExtendByZero, hi]
        · symm
          exact rowSubsetMap_eq_matrixTransposeCoordMap_sunYuanExtendByZero A s g
      · rw [dif_neg hs] at hsx
        exact hsx.elim
  rw [hdecomp]
  -- The index family is finite because `Fin m` has only finitely many subsets.
  refine isClosed_iUnion_of_finite ?_
  intro s
  by_cases hs : LinearIndependent ℝ (fun i : s ↦ matrixRowFamily A i)
  · simpa [hs] using rowSubsetCone_isClosed A s hs
  · simp [hs]

/-- Helper for Chapter01 Theorem 1.3.22: the finitely generated cone of row normals is closed. -/
lemma rowCone_isClosed
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsClosed (rowCone A : Set PrimalPoint) := by
  -- Route correction: prove closedness at the source-facing owner `Aᵀ(ℝ^m_{\ge 0})`, then rewrite
  -- back to `rowCone A`.
  rw [← positiveConeMap_eq_rowCone A]
  exact matrixTransposePositiveImage_isClosed A

/-- Helper for Chapter01 Theorem 1.3.22: a separating functional for the row cone yields a System-1
witness after a sign flip. -/
lemma rowConeSeparator_gives_farkasSystem1
    (A : Matrix (Fin m) (Fin n) ℝ) (c y : PrimalPoint)
    (hycone : ∀ z ∈ (rowCone A : Set PrimalPoint), 0 ≤ inner ℝ z y)
    (hyc : inner ℝ c y < 0) :
    farkasSystem1 A c := by
  refine ⟨-y, ?_, ?_⟩
  · -- Test the separator on each row generator and rewrite the resulting inner products as
    -- matrix coordinates of `A (-y)`.
    intro i
    have hrow :
        0 ≤ inner ℝ (matrixRowFamily A i) y :=
      hycone (matrixRowFamily A i) (PointedCone.subset_hull ⟨i, rfl⟩)
    have hrow' : 0 ≤ inner ℝ y (matrixRowFamily A i) := by
      simpa [real_inner_comm] using hrow
    have hcoord : inner ℝ (-y) (matrixRowFamily A i) ≤ 0 := by
      have : -inner ℝ y (matrixRowFamily A i) ≤ 0 := neg_nonpos.mpr hrow'
      simpa [inner_neg_left] using this
    simpa [inner_matrixRowFamily_eq_apply] using hcoord
  · -- The strict separator inequality becomes the required positive objective value.
    simpa [inner_neg_right] using neg_pos.mpr hyc

/-- Helper for Chapter01 Theorem 1.3.22: for `A : Matrix (Fin m) (Fin n) ℝ` and
`c : EuclideanSpace ℝ (Fin n)`, System 1 and System 2 from Farkas' lemma cannot both have
solutions. -/
theorem farkasLemmaNotBoth
    (A : Matrix (Fin m) (Fin n) ℝ) (c : PrimalPoint) :
    ¬ (farkasSystem1 A c ∧ farkasSystem2 A c) := by
  rintro ⟨⟨x, hxAx, hcx⟩, ⟨y, hyc, hy⟩⟩
  -- Rewrite `⟪c, x⟫` through the transpose action and move `A` to the other side by adjointness.
  let yEuclid : EuclideanSpace ℝ (Fin m) := (equiv (Fin m) ℝ).symm y
  have hAdj : Aᵀ.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A)
  have htranspose :
      inner ℝ c x = inner ℝ yEuclid (A.toEuclideanLin x) := by
    calc
      inner ℝ c x
          = inner ℝ (matrixTransposeCoordMap A y) x := by rw [hyc]
      _ = inner ℝ (A.toEuclideanLin.adjoint yEuclid) x := by
        rw [matrixTransposeCoordMap, hAdj, LinearMap.comp_apply]
        simp [yEuclid]
      _ = inner ℝ yEuclid (A.toEuclideanLin x) := by
        rw [LinearMap.adjoint_inner_left]
  -- The coordinatewise sign conditions make every summand in the Euclidean inner product
  -- nonpositive.
  have hnonpos :
      inner ℝ yEuclid (A.toEuclideanLin x) ≤ 0 := by
    rw [PiLp.inner_apply]
    refine Finset.sum_nonpos ?_
    intro i hi
    exact mul_nonpos_of_nonpos_of_nonneg (hxAx i) (hy i)
  have hcx_nonpos : inner ℝ c x ≤ 0 := by
    rw [htranspose]
    exact hnonpos
  exact (not_le_of_gt hcx) hcx_nonpos

/-- Helper for Chapter01 Theorem 1.3.22: if `c` does not even lie in the range of `Aᵀ`, then a
kernel vector of `A` already witnesses System 1. -/
lemma farkasSystem1_of_not_mem_transposeRange
    (A : Matrix (Fin m) (Fin n) ℝ) (c : PrimalPoint)
    (hc : c ∉ LinearMap.range Aᵀ.toEuclideanLin) :
    farkasSystem1 A c := by
  let T : PrimalPoint →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := A.toEuclideanLin
  have hAdj : Aᵀ.toEuclideanLin = T.adjoint := by
    simpa [T] using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A)
  have hc_not_orth : c ∉ T.kerᗮ := by
    rw [LinearMap.orthogonal_ker T]
    simpa [hAdj] using hc
  have hkernel_pairing :
      ∃ x ∈ T.ker, inner ℝ c x ≠ 0 := by
    by_contra hkernel_pairing
    apply hc_not_orth
    rw [Submodule.mem_orthogonal']
    intro x hx
    by_cases hcx : inner ℝ c x = 0
    · exact hcx
    · exact False.elim (hkernel_pairing ⟨x, hx, hcx⟩)
  rcases hkernel_pairing with ⟨x, hxker, hcx_nonzero⟩
  have hx_zero : T x = 0 := LinearMap.mem_ker.mp hxker
  have hx_system :
      ∀ i : Fin m, A.toEuclideanLin x i ≤ 0 := by
    intro i
    simp [T, hx_zero]
  by_cases hpos : 0 < inner ℝ c x
  · -- A positive kernel pairing is already the desired witness.
    exact ⟨x, hx_system, hpos⟩
  · -- Otherwise the kernel vector has negative pairing, so flipping its sign fixes the witness.
    have hneg : inner ℝ c x < 0 := by
      exact lt_of_le_of_ne (not_lt.mp hpos) hcx_nonzero
    refine ⟨-x, ?_, ?_⟩
    · intro i
      simp [T, hx_zero]
    · simpa using neg_pos.mpr hneg

/-- Chapter01 Theorem 1.3.22: for `A : Matrix (Fin m) (Fin n) ℝ` and
`c : EuclideanSpace ℝ (Fin n)`, at least one of the two systems in Farkas' lemma has a
solution. -/
theorem farkasLemmaOneHasSolution
    (A : Matrix (Fin m) (Fin n) ℝ) (c : PrimalPoint) :
    farkasSystem1 A c ∨ farkasSystem2 A c := by
  by_cases h2 : farkasSystem2 A c
  · -- The easy branch is the direct System-2 certificate.
    exact Or.inr h2
  · -- Route correction: use the closed row cone as the canonical owner of System 2, then apply
    -- proper-cone separation to `c ∉ rowCone A`.
    have hnotmem : c ∉ (rowCone A : Set PrimalPoint) := by
      simpa [farkasSystem2_iff_rowCone A] using h2
    let C0 : ConvexCone ℝ PrimalPoint := (rowCone A : ConvexCone ℝ PrimalPoint)
    have hC0_nonempty : Set.Nonempty (C0 : Set PrimalPoint) := ⟨0, (rowCone A).zero_mem⟩
    have hC0_closed : IsClosed (C0 : Set PrimalPoint) := by
      change IsClosed (rowCone A : Set PrimalPoint)
      exact rowCone_isClosed A
    obtain ⟨C, hCeq⟩ := CanLift.prf (β := ProperCone ℝ PrimalPoint) C0 ⟨hC0_nonempty, hC0_closed⟩
    have hCset : (C : Set PrimalPoint) = (rowCone A : Set PrimalPoint) := by
      ext z
      change z ∈ (C : ConvexCone ℝ PrimalPoint) ↔ z ∈ rowCone A
      rw [hCeq]
      rfl
    have hnotmem' : c ∉ (C : Set PrimalPoint) := by
      rwa [hCset]
    rcases ProperCone.hyperplane_separation' C hnotmem' with ⟨y, hycone, hyc⟩
    have hycone' : ∀ z ∈ (rowCone A : Set PrimalPoint), 0 ≤ inner ℝ z y := by
      intro z hz
      have hz' : z ∈ (C : Set PrimalPoint) := by
        rwa [hCset]
      exact hycone z hz'
    exact Or.inl (rowConeSeparator_gives_farkasSystem1 A c y hycone' hyc)

end Theorem1322
