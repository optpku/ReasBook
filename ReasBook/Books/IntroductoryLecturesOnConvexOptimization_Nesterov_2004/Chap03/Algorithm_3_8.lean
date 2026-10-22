/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_52
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open scoped EllipsoidNotation

/- Primary domain: ellipsoid-method iterations for the chapter's constrained convex minimization
problems with separation oracle.

Relevant owner-style declarations sampled before refinement:
- `ConvexMinimizationWithSeparationOracle` in `Definition_3_51` for the ambient constrained
  problem and its oracle semantics;
- `GeneralCuttingPlaneScheme` and `cuttingHalfspace` in `Algorithm_3_6` for the chapter's
  cutting-plane owner abstraction and retained affine half-space cuts;
- `localizationSets` in `Definition_3_52` for the canonical recursive localization-set
  construction attached to query/cut sequences;
- `affineEllipsoid`, `center_mem_affineEllipsoid`, `affineEllipsoid_bounded`,
  `centerCutEllipsoid`, `updatedEllipsoidCenter`, and `updatedEllipsoidMatrix` in
  `Lemma_3_2_7` for the ellipsoid geometry, the canonical owner facts about ellipsoid centers and
  boundedness, and the textbook update formulas.

Source/core/bridge triage:
- source-facing: the recursively defined ellipsoid centers `yₖ`, shape matrices `Hₖ`, and
  associated ellipsoids attached to an initial center `y₀` and radius `R`;
- core/canonical: `ConvexMinimizationWithSeparationOracle (EuclideanSpace ℝ (Fin n))`,
  `GeneralCuttingPlaneScheme`, `localizationSets`, and the ellipsoid-update API of
  `Lemma_3_2_7`;
- bridge/view: `toGeneralCuttingPlaneScheme` and
  `localizationSets_subset_associatedEllipsoid`.

Primitive data:
- the owner constrained minimization problem with separation oracle;
- the initial center `y₀` and radius `R`.

Derived API:
- the recursive center sequence `y₀, y₁, ...`;
- the recursive shape sequence `H₀, H₁, ...`;
- the cutting vectors returned by the owner oracle map `problem.oracle` at those centers;
- the associated ellipsoid sequence;
- the canonical localization sets determined by the query/cut recursion;
- the bridge from the ellipsoid sequence to the chapter's cutting-plane owner abstraction. -/

namespace EllipsoidMethod

variable (problem : ConvexMinimizationWithSeparationOracle (EuclideanSpace ℝ (Fin n)))

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

mutual

/-- Algorithm 3.8: the ellipsoid-method center sequence `y₀, y₁, ...` attached to an initial
center `y₀` and radius `R`, where the update uses the recursively defined shape matrices and the
cutting vectors returned by the separation oracle at the current center. -/
def center
    (problem : ConvexMinimizationWithSeparationOracle (EuclideanSpace ℝ (Fin n)))
    (initialCenter : E) (radius : ℝ) : ℕ → E
  | 0 => initialCenter
  | k + 1 =>
      x̄₊(
        shape problem initialCenter radius k,
        center problem initialCenter radius k,
        problem.oracle (center problem initialCenter radius k))

/-- The shape-matrix sequence `H₀, H₁, ...` of the ellipsoid method. -/
def shape
    (problem : ConvexMinimizationWithSeparationOracle (EuclideanSpace ℝ (Fin n)))
    (initialCenter : E) (radius : ℝ) : ℕ → Mat
  | 0 => radius ^ (2 : ℕ) • (1 : Mat)
  | k + 1 =>
      H₊(
        shape problem initialCenter radius k,
        problem.oracle (center problem initialCenter radius k))

end

/-- The cut vector `gₖ` is the owner oracle value at the current center `yₖ`. -/
def cuttingVector
    (problem : ConvexMinimizationWithSeparationOracle (EuclideanSpace ℝ (Fin n)))
    (initialCenter : E) (radius : ℝ) (k : ℕ) : E :=
  problem.oracle (center problem initialCenter radius k)

/-- The ellipsoid `Eₖ = E(Hₖ, yₖ)` attached to the `k`-th ellipsoid-method state. -/
def associatedEllipsoid
    (problem : ConvexMinimizationWithSeparationOracle (EuclideanSpace ℝ (Fin n)))
    (initialCenter : E) (radius : ℝ) (k : ℕ) : Set E :=
  E(shape problem initialCenter radius k, center problem initialCenter radius k)

/-- The center sequence starts at the prescribed initial point `y₀`. -/
-- Proof sketch: unfold the zero case of the recursive definition of `center`.
theorem center_zero (initialCenter : E) (radius : ℝ) :
    center problem initialCenter radius 0 = initialCenter :=
  rfl

/-- The shape sequence starts from the textbook initial matrix `R² Iₙ`. -/
-- Proof sketch: unfold the zero case of the recursive definition of `shape`.
theorem shape_zero (initialCenter : E) (radius : ℝ) :
    shape problem initialCenter radius 0 =
      radius ^ (2 : ℕ) • (1 : Mat) :=
  rfl

/-- The center update is the textbook normalized `Hₖ gₖ` step. -/
-- Proof sketch: unfold the successor case of `center` and rewrite `cuttingVector`.
theorem center_succ
    (initialCenter : E) (radius : ℝ) (k : ℕ) :
    center problem initialCenter radius (k + 1) =
      x̄₊(
        shape problem initialCenter radius k,
        center problem initialCenter radius k,
        cuttingVector problem initialCenter radius k) :=
  rfl

/-- The shape-matrix update is the textbook ellipsoid rank-one correction formula. -/
-- Proof sketch: unfold the successor case of `shape` and rewrite `cuttingVector`.
theorem shape_succ
    (initialCenter : E) (radius : ℝ) (k : ℕ) :
    shape problem initialCenter radius (k + 1) =
      H₊(
        shape problem initialCenter radius k,
        cuttingVector problem initialCenter radius k) :=
  rfl

/-- Membership in the associated ellipsoid is exactly its defining quadratic inequality. -/
-- Proof sketch: unfold `associatedEllipsoid` and then the notation `E(H, x̄)`.
theorem mem_associatedEllipsoid_iff
    (initialCenter : E) (radius : ℝ) (k : ℕ) {x : E} :
    x ∈ associatedEllipsoid problem initialCenter radius k ↔
      inner ℝ
          (((shape problem initialCenter radius k)⁻¹).toEuclideanLin
            (x - center problem initialCenter radius k))
          (x - center problem initialCenter radius k) ≤
        1 :=
  by
    simp [associatedEllipsoid, affineEllipsoid]

/-- On feasible centers, the owner oracle returns a subgradient of the objective. -/
-- Proof sketch: specialize the feasible-point specification of the separation oracle at the
-- current center and identify the returned vector with `cuttingVector`.
theorem cuttingVector_isSubgradientAt_of_mem
    (initialCenter : E) (radius : ℝ) {k : ℕ}
    (hmem : center problem initialCenter radius k ∈ problem.feasibleSet) :
    IsSubgradientAt (fun x ↦ (problem x : WithTop ℝ))
      (center problem initialCenter radius k)
      (cuttingVector problem initialCenter radius k) :=
  by
    simpa [cuttingVector] using problem.oracle.subgradient_spec hmem

/-- On infeasible centers, the owner oracle returns a strict separating vector for the feasible
set. -/
-- Proof sketch: specialize the infeasible-point branch of the separation oracle at the current
-- center and rewrite the oracle output as `cuttingVector`.
theorem separatesByCuttingVector_of_not_mem
    (initialCenter : E) (radius : ℝ) {k : ℕ}
    (hmem : center problem initialCenter radius k ∉ problem.feasibleSet) :
    SeparatesByCuttingVector
      problem.feasibleSet
      (center problem initialCenter radius k)
      (cuttingVector problem initialCenter radius k) :=
  by
    simpa [cuttingVector] using problem.oracle.separating_spec hmem

/-- For infeasible centers, the feasible set lies in the retained half-space cut. -/
-- Proof sketch: derive the separating-vector statement from the oracle and apply its canonical
-- half-space containment lemma.
theorem feasibleSet_subset_cuttingHalfspace_of_not_mem
    (initialCenter : E) (radius : ℝ) {k : ℕ}
    (hmem : center problem initialCenter radius k ∉ problem.feasibleSet) :
    problem.feasibleSet ⊆
      cuttingHalfspace
        (center problem initialCenter radius k)
        (cuttingVector problem initialCenter radius k) :=
  (separatesByCuttingVector_of_not_mem problem initialCenter radius hmem).subset_cuttingHalfspace

/-- The current center always belongs to its associated ellipsoid. -/
-- Proof sketch: unfold `associatedEllipsoid` and invoke the center-membership theorem for affine
-- ellipsoids.
theorem center_mem_associatedEllipsoid
    (initialCenter : E) (radius : ℝ) (k : ℕ) :
    center problem initialCenter radius k ∈
      associatedEllipsoid problem initialCenter radius k :=
  by
    simpa [associatedEllipsoid] using
      center_mem_affineEllipsoid
        (shape problem initialCenter radius k)
        (center problem initialCenter radius k)

/-- Each ellipsoid in the recursion is bounded as soon as its shape matrix is positive
definite. -/
-- Proof sketch: unfold `associatedEllipsoid` and apply boundedness of a positive-definite affine
-- ellipsoid.
theorem associatedEllipsoid_bounded
    (initialCenter : E) (radius : ℝ) (k : ℕ)
    (hshape_pos : (shape problem initialCenter radius k).PosDef) :
    Bornology.IsBounded (associatedEllipsoid problem initialCenter radius k) :=
  by
    simpa [associatedEllipsoid] using
      affineEllipsoid_bounded
        (shape problem initialCenter radius k)
        (center problem initialCenter radius k)
        hshape_pos

/-- Under the standard ellipsoid-update hypotheses, the next ellipsoid contains the retained
half-space cut of the current ellipsoid. -/
-- Proof sketch: turn a point of the current ellipsoid and its retained cutting half-space into a
-- point of the center-cut ellipsoid, apply the standard ellipsoid-update containment theorem from
-- `Lemma_3_2_7`, and rewrite the successor formulas for `center` and `shape`.
theorem next_associatedEllipsoid_contains_cuttingHalfspace
    (initialCenter : E) (radius : ℝ) (k : ℕ)
    (hshape_pos : (shape problem initialCenter radius k).PosDef)
    (hn : 1 < n)
    (hcut_nonzero : cuttingVector problem initialCenter radius k ≠ 0) :
    associatedEllipsoid problem initialCenter radius k ∩
        cuttingHalfspace
          (center problem initialCenter radius k)
          (cuttingVector problem initialCenter radius k) ⊆
      associatedEllipsoid problem initialCenter radius (k + 1) :=
  by
    intro x hx
    have hxcut :
        inner ℝ
            (cuttingVector problem initialCenter radius k)
            (x - center problem initialCenter radius k) ≤
          0 := by
      have hxhalf :
          inner ℝ (cuttingVector problem initialCenter radius k) x ≤
            inner ℝ (cuttingVector problem initialCenter radius k)
              (center problem initialCenter radius k) := by
        simpa [cuttingHalfspace] using hx.2
      simpa [inner_sub_right] using sub_nonpos.mpr hxhalf
    have hxcenterCut :
        x ∈
          E₊(
            shape problem initialCenter radius k,
            center problem initialCenter radius k,
            cuttingVector problem initialCenter radius k) := by
      exact
        (mem_centerCutEllipsoid_iff.2
          ⟨by simpa [associatedEllipsoid] using hx.1, hxcut⟩)
    have hxnext :
        x ∈
          E(
            H₊(shape problem initialCenter radius k, cuttingVector problem initialCenter radius k),
            x̄₊(
              shape problem initialCenter radius k,
              center problem initialCenter radius k,
              cuttingVector problem initialCenter radius k)) :=
      (centerCutEllipsoid_subset_updatedEllipsoid_and_volume_le
        (shape problem initialCenter radius k)
        hshape_pos
        (center problem initialCenter radius k)
        (cuttingVector problem initialCenter radius k)
        hcut_nonzero
        hn).1 hxcenterCut
    simpa [associatedEllipsoid, center_succ, shape_succ] using hxnext

/-- When the initial ellipsoid covers the feasible set, `n > 1`, and every ellipsoid update uses
a nonzero cutting vector, the ellipsoid recursion defines a `GeneralCuttingPlaneScheme` whose
localizers are the associated ellipsoids. -/
def toGeneralCuttingPlaneScheme
    (initialCenter : E) (radius : ℝ)
    (hn : 1 < n)
    (hcut_nonzero : ∀ k : ℕ, cuttingVector problem initialCenter radius k ≠ 0)
    (hE0_cover :
      problem.feasibleSet ⊆ associatedEllipsoid problem initialCenter radius 0)
    (hshape_pos : ∀ k : ℕ, (shape problem initialCenter radius k).PosDef) :
    GeneralCuttingPlaneScheme problem where
  localizer := associatedEllipsoid problem initialCenter radius
  queryPoint := center problem initialCenter radius
  initial_bounded :=
    associatedEllipsoid_bounded problem initialCenter radius 0 (hshape_pos 0)
  feasibleSet_subset_initial := hE0_cover
  query_mem := center_mem_associatedEllipsoid problem initialCenter radius
  next_localizer_contains := fun k ↦
    next_associatedEllipsoid_contains_cuttingHalfspace
      problem initialCenter radius k (hshape_pos k) hn (hcut_nonzero k)

/-- The cutting vectors of the induced cutting-plane scheme are the ellipsoid-method cutting
vectors. -/
-- Proof sketch: unfold the scheme cutting-vector definition and then `toGeneralCuttingPlaneScheme`.
@[simp] theorem toGeneralCuttingPlaneScheme_cuttingVector
    (initialCenter : E) (radius : ℝ)
    (hn : 1 < n)
    (hcut_nonzero : ∀ k : ℕ, cuttingVector problem initialCenter radius k ≠ 0)
    (hE0_cover :
      problem.feasibleSet ⊆ associatedEllipsoid problem initialCenter radius 0)
    (hshape_pos : ∀ k : ℕ, (shape problem initialCenter radius k).PosDef)
    (k : ℕ) :
    (toGeneralCuttingPlaneScheme
      problem initialCenter radius hn hcut_nonzero hE0_cover hshape_pos).cuttingVector k =
      cuttingVector problem initialCenter radius k :=
  by
    simp [GeneralCuttingPlaneScheme.cuttingVector, toGeneralCuttingPlaneScheme, cuttingVector]

/-- The canonical localization sets determined by the ellipsoid query/cut sequences stay inside
the associated ellipsoids, provided the initial ellipsoid covers the feasible set and every
ellipsoid update direction is nonzero in dimension `n > 1`. -/
-- Proof sketch: apply the general localization-set containment theorem to the induced
-- cutting-plane scheme from `toGeneralCuttingPlaneScheme`.
theorem localizationSets_subset_associatedEllipsoid
    (initialCenter : E) (radius : ℝ)
    (hn : 1 < n)
    (hcut_nonzero : ∀ k : ℕ, cuttingVector problem initialCenter radius k ≠ 0)
    (hE0_cover :
      problem.feasibleSet ⊆ associatedEllipsoid problem initialCenter radius 0)
    (hshape_pos : ∀ k : ℕ, (shape problem initialCenter radius k).PosDef) :
    ∀ k : ℕ,
      localizationSets
          problem.feasibleSet
          (center problem initialCenter radius)
          (cuttingVector problem initialCenter radius)
          k ⊆
        associatedEllipsoid problem initialCenter radius k :=
  by
    intro k
    let scheme :=
      toGeneralCuttingPlaneScheme
        problem initialCenter radius hn hcut_nonzero hE0_cover hshape_pos
    simpa [scheme, GeneralCuttingPlaneScheme.cuttingVector, cuttingVector] using
      scheme.localizationSets_subset_localizer k

end EllipsoidMethod

end
