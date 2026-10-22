/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : ℕ}

local notation "E" => Fin n → ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMat" => {A : Mat // Matrix.PosDef A}
local notation "Euclid" => EuclideanSpace ℝ (Fin n)
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ

/- Definition 1.8.3 is a source-facing recall in the positive-definite matrix geometry of `ℝ^n`,
modeled as `Fin n → ℝ`.

Primary domain:
- inner products and norms induced by positive-(semi)definite matrices.

Sampled owner-style declarations:
- `Matrix.toNormedAddCommGroup`, the canonical norm owner attached to a positive-definite matrix;
- `Matrix.toInnerProductSpace`, the canonical inner-product owner attached to a positive
  semidefinite matrix;
- `Matrix.PosDef.posSemidef`, the bridge from the positive-definite hypothesis needed for the norm
  owner to the positive-semidefinite hypothesis needed for the inner-product owner;
- `Matrix.dotProduct_mulVec`, the coordinate formula used in the textbook expansion.

Best owner abstraction:
- the canonical induced structures `Matrix.toNormedAddCommGroup A hA` and
  `Matrix.toInnerProductSpace A hA.posSemidef`.

Primitive data:
- `A : Mat`
- `hA : A.PosDef`

Derived API:
- the source-facing notation `‖x‖[A]` and `⟪x, y⟫_[A]` for
  `A : {A : Mat // A.PosDef}`;
- the textbook coordinate formulas recorded below as thin bridge lemmas.

Source/core/bridge triage:
- source-facing: the induced norm and inner product attached to a positive-definite matrix;
- core/canonical: `Matrix.toNormedAddCommGroup` and `Matrix.toInnerProductSpace`;
- bridge/view: the notation layer `‖x‖[A]`, `⟪x, y⟫_[A]`, and the formula companions
  `inner_eq_dotProduct_mulVec`, `norm_eq_sqrt_dotProduct_mulVec`, implemented through
  abbreviation-level notation bridges.

This file therefore keeps Definition 1.8.3 as direct canonical recall/use of the induced owner
structures, rather than introducing a second public wrapper API for the same norm and inner
product.
-/

recall Matrix.toNormedAddCommGroup
    {n : Type*} {𝕜 : Type*} [Fintype n] [RCLike 𝕜] (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜)

recall Matrix.toInnerProductSpace
    {n : Type*} {𝕜 : Type*} [Fintype n] [RCLike 𝕜] (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (M.toSeminormedAddCommGroup hM)

namespace Matrix
namespace PosDef

/-- The coordinate model `Fin n → ℝ`, equipped with the norm and inner product induced by the
positive-definite matrix owner `A`. This is the bridge carrier used by the weighted Chapter 1
owners. -/
abbrev WeightedSpace (_A : PosMat) := E

instance (A : PosMat) : NormedAddCommGroup (WeightedSpace (n := n) A) :=
  Matrix.toNormedAddCommGroup A.1 A.2

instance (A : PosMat) :
    @InnerProductSpace ℝ (WeightedSpace A) _
      (Matrix.toNormedAddCommGroup A.1 A.2).toSeminormedAddCommGroup :=
  Matrix.toInnerProductSpace A.1 A.2.posSemidef

instance (A : PosMat) : CompleteSpace (WeightedSpace (n := n) A) :=
  FiniteDimensional.complete ℝ (WeightedSpace A)

abbrev weightedInner (A : PosMat) (x y : E) : ℝ :=
  @inner ℝ E (Matrix.toInnerProductSpace A.1 A.2.posSemidef).toInner x y

abbrev weightedNorm (A : PosMat) (x : E) : ℝ :=
  @norm E (Matrix.toNormedAddCommGroup A.1 A.2).toNorm x

end PosDef
end Matrix

namespace MatrixPosDef

scoped notation:70 "⟪" x ", " y "⟫_[" A:arg "]" => Matrix.PosDef.weightedInner A x y
scoped notation:max "‖" x "‖[" A:arg "]" => Matrix.PosDef.weightedNorm A x

end MatrixPosDef

open scoped MatrixPosDef

namespace Matrix
namespace PosDef

/-- For a positive-definite real matrix owner, the weighted inner product is the textbook pairing
`⟪Ax, y⟫`. -/
theorem inner_eq_dotProduct_mulVec (A : PosMat) (x y : E) :
    ⟪x, y⟫_[A] = dotProduct (A.1 *ᵥ x) y := by
  change dotProduct (A.1 *ᵥ y) x = dotProduct (A.1 *ᵥ x) y
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  have hA' : A.1ᴴ = A.1 := by
    simpa using A.2.1.eq
  rw [← conjTranspose_eq_transpose_of_trivial A.1, hA']

/-- For a positive-definite real matrix owner, the weighted norm is the square root of the weighted
quadratic form `⟪Ax, x⟫`. -/
theorem norm_eq_sqrt_dotProduct_mulVec (A : PosMat) (x : E) :
    ‖x‖[A] = Real.sqrt (dotProduct (A.1 *ᵥ x) x) := by
  rw [show ‖x‖[A] = Real.sqrt (⟪x, x⟫_[A]) by
    exact @norm_eq_sqrt_real_inner E
      (Matrix.toNormedAddCommGroup A.1 A.2).toSeminormedAddCommGroup
      (Matrix.toInnerProductSpace A.1 A.2.posSemidef) x]
  rw [inner_eq_dotProduct_mulVec]

/-- Transporting the weighted norm on coordinates through `EuclideanSpace.equiv` rewrites it as
the textbook Euclidean quadratic form `⟪Ax, x⟫`. -/
theorem norm_coordEquiv_eq_sqrt_inner_toEuclideanLin (A : PosMat) (x : Euclid) :
    ‖coordEquiv x‖[A] = Real.sqrt (inner ℝ (A.1.toEuclideanLin x) x) := by
  have hinner :
      inner ℝ (A.1.toEuclideanLin x) x = dotProduct (coordEquiv x) (A.1 *ᵥ coordEquiv x) := by
    simpa only [Matrix.ofLp_toLpLin] using
      (EuclideanSpace.inner_eq_star_dotProduct (A.1.toEuclideanLin x) x)
  calc
    ‖coordEquiv x‖[A] = Real.sqrt (dotProduct (A.1 *ᵥ coordEquiv x) (coordEquiv x)) := by
      simpa using norm_eq_sqrt_dotProduct_mulVec A (coordEquiv x)
    _ = Real.sqrt (inner ℝ (A.1.toEuclideanLin x) x) := by
      rw [hinner, dotProduct_comm]

/-- The identity-matrix weighted norm on coordinates agrees with the Euclidean norm after
transporting by `EuclideanSpace.equiv`. -/
theorem one_norm_coordEquiv_eq (x : Euclid) :
    ‖coordEquiv x‖[⟨(1 : Mat), PosDef.one⟩] = ‖x‖ := by
  calc
    ‖coordEquiv x‖[⟨(1 : Mat), PosDef.one⟩] =
        Real.sqrt (dotProduct ((1 : Mat) *ᵥ coordEquiv x) (coordEquiv x)) := by
      simpa using norm_eq_sqrt_dotProduct_mulVec ⟨(1 : Mat), PosDef.one⟩ (coordEquiv x)
    _ = ‖x‖ := by
      rw [EuclideanSpace.norm_eq x]
      simp [dotProduct, pow_two]

end PosDef
end Matrix

end
