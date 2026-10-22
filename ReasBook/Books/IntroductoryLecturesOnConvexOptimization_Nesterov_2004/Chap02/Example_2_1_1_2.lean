/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_9_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

open scoped RealInnerProductSpace

/- Example 2.1.1.2 lies in finite-dimensional Euclidean convexity for quadratic objectives.

Sampled owner-style declarations in this domain:
* `quadraticObjective` from `Definition_1_9_1`
* `Matrix.PosSemidef` from `Definition_1_4_18`
* `Matrix.isPositive_toEuclideanLin_iff` from mathlib's positive-operator API

Best owner abstraction:
* positivity of the Euclidean linear operator `A.toEuclideanLin`, with `A.PosSemidef` as its
  canonical matrix-level realization

Primitive data:
* `alpha`, `a`, `A`, and `A.PosSemidef`

Derived API:
* the owner-derived theorem `Matrix.PosSemidef.convexOn_quadraticObjective`
  for `quadraticObjective alpha a A`

Source/core/bridge triage:
* source-facing: the textbook convexity example for a quadratic with positive-semidefinite Hessian
* core/canonical: `quadraticObjective`, `Matrix.PosSemidef`, `LinearMap.IsPositive`
* bridge/view: the owner-derived theorem `Matrix.PosSemidef.convexOn_quadraticObjective`
-/

/-- Helper for Example 2.1.1.2: every affine functional `x ↦ α + ⟪a, x⟫` on `ℝⁿ` is convex on
the whole space. -/
theorem convexOn_const_add_inner_univ (alpha : ℝ) (a : E) :
    ConvexOn ℝ Set.univ (fun x : E ↦ alpha + inner ℝ a x) := by
  let ℓ : E →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ E alpha + ((innerSL ℝ a).toLinearMap).toAffineMap
  -- Package the affine expression as a single affine map and pull back convexity of `id`.
  have hℓ : ConvexOn ℝ Set.univ (ℓ : E → ℝ) := by
    simpa [Function.comp, ℓ] using
      (convexOn_id convex_univ).comp_affineMap ℓ
  -- Expand the packaged affine map back to the textbook formula.
  simpa [ℓ, innerSL_apply_apply, add_assoc, add_left_comm, add_comm] using hℓ

namespace LinearMap.IsPositive

universe u

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A positive operator on a real inner-product space has convex quadratic form
`x ↦ (1 / 2) * ⟪T x, x⟫`. -/
theorem convexOn_half_inner_map_self {T : F →ₗ[ℝ] F} (hT : T.IsPositive) :
    ConvexOn ℝ Set.univ (fun x : F ↦ (1 / 2 : ℝ) * inner ℝ (T x) x) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ t s ht hs hts
  -- The Jensen gap is controlled by the quadratic form on `x - y`.
  have hquad : 0 ≤ inner ℝ (T (x - y)) (x - y) := hT.inner_nonneg_left (x - y)
  -- Self-adjointness turns the cross terms into a symmetric expression.
  have hsymm : ∀ u v : F, inner ℝ (T u) v = inner ℝ (T v) u := by
    intro u v
    simpa [real_inner_comm] using hT.isSymmetric u v
  have hs' : s = 1 - t := by
    linarith
  -- After normalizing `s = 1 - t`, the Jensen gap is exactly the negative PSD correction term.
  have hrewrite :
      (1 / 2 : ℝ) * inner ℝ (T (t • x + s • y)) (t • x + s • y) -
        (t * ((1 / 2 : ℝ) * inner ℝ (T x) x) +
          s * ((1 / 2 : ℝ) * inner ℝ (T y) y)) =
      -((t * s) / 2) * inner ℝ (T (x - y)) (x - y) := by
    subst hs'
    simp [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, map_add, map_sub, map_smul, hsymm x y]
    ring_nf
  -- Positivity of `T` and nonnegativity of the barycentric weights make the correction term
  -- nonpositive, which is exactly the Jensen inequality.
  have hrhs : -((t * s) / 2) * inner ℝ (T (x - y)) (x - y) ≤ 0 := by
    nlinarith [mul_nonneg ht hs, hquad]
  exact sub_nonpos.mp <| hrewrite ▸ hrhs

end LinearMap.IsPositive

namespace Matrix.PosSemidef

/-- Example 2.1.1.2: the canonical quadratic objective on `ℝ^n` with positive-semidefinite
Hessian data is convex. -/
-- Proof sketch: split the quadratic objective into its affine and quadratic pieces. The affine
-- term is convex on all of `ℝⁿ`, and the quadratic term is convex because `A.toEuclideanLin` is a
-- positive operator when `A` is positive semidefinite. Then add the two convex functions and
-- rewrite back to `quadraticObjective`.
theorem convexOn_quadraticObjective
    {A : Mat} (hA : A.PosSemidef) (alpha : ℝ) (a : E) :
    ConvexOn ℝ Set.univ (quadraticObjective alpha a A) := by
  -- The linear-plus-constant part is affine, hence convex on the whole space.
  have hAffine : ConvexOn ℝ Set.univ (fun x : E ↦ alpha + inner ℝ a x) :=
    convexOn_const_add_inner_univ alpha a
  -- The Hessian contribution is convex because `A` induces a positive operator.
  have hQuad :
      ConvexOn ℝ Set.univ (fun x : E ↦ (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x) :=
    LinearMap.IsPositive.convexOn_half_inner_map_self
      (Matrix.isPositive_toEuclideanLin_iff.mpr hA)
  -- Reassemble the affine and quadratic owners into the original quadratic objective.
  change ConvexOn ℝ Set.univ
    ((fun x : E ↦ alpha + inner ℝ a x) +
      fun x : E ↦ (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin x) x)
  simpa [quadraticObjective, Pi.add_apply, add_assoc] using hAffine.add hQuad

end Matrix.PosSemidef
