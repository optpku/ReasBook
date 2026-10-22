/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Matrix
open InnerProductSpace (toDualMap)

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable (A : Matrix (Fin n) (Fin n) ℝ) (b y : E) (c : ℝ)

/- Proposition 4.12 is `source-facing`: its primitive data are the quadratic coefficients `A`, `b`,
and `c`, and its main content is the explicit maximizer/value of the quadratic Fenchel objective on
`ℝ^n`. The `core/canonical` owners are already Chapter 4's `quadratic_affine_function` for the
primal quadratic and `conjugate_function_primal` / `f∗` for its Euclidean Fenchel conjugate, so
this file should reuse those owners rather than restating the same quadratic formula under
anonymous functions. -/

recall quadratic_affine_function
recall conjugate_function_primal

-- Semantic recall: Definition 4.4 already exposes the quadratic/conjugate bridge on the
-- source-facing Euclidean carrier `EuclideanSpace ℝ (Fin n)`, so the public statements here
-- should stay on that surface and use only the explicit solve map `Matrix.toEuclideanLin`.

-- Semantic recall: a `lean_leansearch` query for the quadratic/maximizer pattern only returned
-- matrix positive-definiteness infrastructure, so the Chapter 4 bridge theorems in
-- `Definition_4_4` remain the right local owner/API precedent here.
-- Route correction: the current source-facing `dotProduct` surface on `EuclideanSpace ℝ (Fin n)`
-- silently inserts unresolved coordinate coercions in Lean, so the next pass must first replace
-- that surface by an explicit coordinate map or an equivalent intrinsic `inner` formulation.
-- Proof sketch: complete the square in the rewritten objective from equation `(4.4.7)` to obtain
-- a negative definite quadratic centered at `A⁻¹ (y - b)` plus a constant. Since `hA` implies `A`
-- is positive definite, the centered quadratic term is nonpositive and vanishes exactly at
-- `x = A⁻¹ (y - b)`, yielding the greatest value there.
/-- Helper for Proposition 4.12: a real-valued range achieves the `EReal` supremum at `x`
exactly when `x` is a global maximizer on `Set.univ`. -/
lemma ereal_sSup_coe_range_eq_iff_isMaxOn_univ
    {α : Type*} (φ : α → ℝ) (x : α) :
    sSup (Set.range fun z : α ↦ ((φ z : ℝ) : EReal)) = (φ x : EReal) ↔
      IsMaxOn φ Set.univ x := by
  -- Translate the `EReal` supremum condition into the pointwise maximality predicate.
  rw [isMaxOn_univ_iff]
  constructor
  · intro hs z
    have hz : ((φ z : ℝ) : EReal) ≤ sSup (Set.range fun w : α ↦ ((φ w : ℝ) : EReal)) :=
      le_sSup (Set.mem_range_self z)
    rw [hs] at hz
    exact EReal.coe_le_coe_iff.mp hz
  · intro hx
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨z, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hx z)
    · exact le_sSup (Set.mem_range_self x)

/-- Helper for Proposition 4.12: on Euclidean space, the inner product agrees with the coordinate
dot product. -/
lemma inner_eq_dotProduct {n : ℕ} (y x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ y x = dotProduct y.ofLp x.ofLp := by
  -- The Euclidean-space inner product is already the coordinate dot product.
  simpa [dotProduct_comm] using
    (EuclideanSpace.inner_eq_star_dotProduct (x := y) (y := x))

/-- Helper for Proposition 4.12: the Euclidean linear-map spelling of the inverse solve point
still satisfies the stationarity equation `A *ᵥ x = y - b`. -/
lemma inverseSolve_mulVec_eq_sub {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b y : EuclideanSpace ℝ (Fin n))
    (hA : A.PosDef) :
    A *ᵥ (Matrix.toEuclideanLin (A⁻¹) (y - b)).ofLp = (y - b).ofLp := by
  let _ : Invertible A := hA.isUnit.invertible
  -- Normalize the solve point to matrix-vector notation and cancel the inverse.
  ext i
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- Helper for Proposition 4.12: at a stationary point `A *ᵥ x = y - b`, the rewritten quadratic
objective collapses to the claimed dual value. -/
lemma rewrittenQuadraticObjective_eq_dualValue_of_stationary {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hAx : A *ᵥ x.ofLp = (y - b).ofLp) :
    (-(1 / 2 : ℝ)) * dotProduct x.ofLp (A *ᵥ x.ofLp) - dotProduct (b - y).ofLp x.ofLp - c =
      (1 / 2 : ℝ) * dotProduct (y - b).ofLp x.ofLp - c := by
  have hsub : (b - y).ofLp = -((y - b).ofLp) := by
    ext i
    simp
  -- Rewrite the linear term using `b - y = -(y - b)`, then substitute stationarity.
  rw [hAx, hsub, neg_dotProduct, dotProduct_comm x.ofLp (y - b).ofLp]
  ring_nf

/-- The argmax statement used in Proposition 4.12: for
`f(x) = (1 / 2) xᵀ A x + bᵀ x + c` with `A ∈ 𝕊_{++}^n`, the maximum in equation `(4.4.7)`,
`x ↦ -(1 / 2) xᵀ A x - (b - y)ᵀ x - c`, is attained at `x = A⁻¹ (y - b)`. -/
theorem strictly_convex_quadratic_conjugate_isMaxOn {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hA : A.PosDef) :
    IsMaxOn
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        (-(1 / 2 : ℝ)) * dotProduct x.ofLp (A *ᵥ x.ofLp) - dotProduct (b - y).ofLp x.ofLp - c)
      Set.univ
      (Matrix.toEuclideanLin (A⁻¹) (y - b)) := by
  have hgreatest := rewrittenQuadraticObjective_isGreatest_of_posDef A hA b.ofLp y.ofLp c
  -- Transport the coordinate-space greatest-element certificate to `IsMaxOn` on `Set.univ`.
  rw [isMaxOn_univ_iff]
  intro z
  simpa [Matrix.toLpLin_apply] using hgreatest.2 (Set.mem_range_self z.ofLp)

-- Proof sketch: use `strictly_convex_quadratic_conjugate_isMaxOn` to identify the supremum in
-- `f∗ y` with the value of the quadratic objective at `x = A⁻¹ (y - b)`. Then expand that value
-- and simplify the completed-square expression to
-- obtain `(1 / 2) * dotProduct (y - b) (A⁻¹ (y - b)) - c`.
-- Route correction: the proof route through `conjugate_function_primal_apply` is still viable
-- once the statement surface is repaired to a typed Euclidean/coefficient bridge.
/-- Proposition 4.12: the conjugate of the positive-definite quadratic
`quadratic_affine_function A b c`, evaluated on `ℝ^n` through the primal Chapter 4 conjugate
surface `f∗`, is `y ↦ (1 / 2) (y - b)ᵀ A⁻¹ (y - b) - c`. -/
theorem strictly_convex_quadratic_conjugate_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hA : A.PosDef) :
    ((fun x : EuclideanSpace ℝ (Fin n) ↦
        (quadratic_affine_function A b.ofLp c x.ofLp : EReal))∗) y =
      (((1 / 2 : ℝ) * dotProduct (y - b).ofLp
          (Matrix.toEuclideanLin (A⁻¹) (y - b)).ofLp - c : ℝ) :
        EReal) := by
  let xStar : EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin (A⁻¹) (y - b)
  let ψ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x ↦
      (-(1 / 2 : ℝ)) * dotProduct x.ofLp (A *ᵥ x.ofLp) - dotProduct (b - y).ofLp x.ofLp - c
  let φ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x ↦ inner ℝ y x - quadratic_affine_function A b.ofLp c x.ofLp
  have hmaxPsi : IsMaxOn ψ Set.univ xStar := by
    -- Reuse the positive-definite argmax theorem on the rewritten quadratic objective.
    simpa [ψ, xStar] using
      (strictly_convex_quadratic_conjugate_isMaxOn A b y c hA)
  have hφ : ∀ z : EuclideanSpace ℝ (Fin n), φ z = ψ z := by
    intro z
    -- Route correction: rewrite `toDualMap` through `inner`, then convert `inner` to coordinates.
    dsimp [φ, ψ]
    rw [inner_eq_dotProduct y z]
    simpa using (quadraticAffineObjective_rewrite A b.ofLp y.ofLp z.ofLp c)
  have hmax : IsMaxOn φ Set.univ xStar := by
    -- Once the two objectives agree pointwise, the argmax property transfers directly.
    rw [isMaxOn_univ_iff] at hmaxPsi ⊢
    intro z
    rw [hφ z, hφ xStar]
    exact hmaxPsi z
  have hsup :
      sSup (Set.range fun z : EuclideanSpace ℝ (Fin n) ↦
        (((inner ℝ y z : ℝ) : EReal) -
          (quadratic_affine_function A b.ofLp c z.ofLp : EReal))) =
        (φ xStar : EReal) := by
    -- Identify the primal `sSup` with the value at the Euclidean maximizer.
    simpa [φ, EReal.coe_sub] using
      (ereal_sSup_coe_range_eq_iff_isMaxOn_univ (φ := φ) (x := xStar)).2 hmax
  have hxStar : A *ᵥ xStar.ofLp = (y - b).ofLp := by
    -- The inverse solve point satisfies the stationary equation.
    simpa [xStar] using
      (inverseSolve_mulVec_eq_sub A b y hA)
  have hvalue : φ xStar = (1 / 2 : ℝ) * dotProduct (y - b).ofLp xStar.ofLp - c := by
    -- Evaluate the rewritten objective at the stationary point.
    calc
      φ xStar = ψ xStar := hφ xStar
      _ = (1 / 2 : ℝ) * dotProduct (y - b).ofLp xStar.ofLp - c := by
        exact rewrittenQuadraticObjective_eq_dualValue_of_stationary A b y c hxStar
  have hsupDual :
      sSup (Set.range fun z : EuclideanSpace ℝ (Fin n) ↦
        ((((toDualMap ℝ (EuclideanSpace ℝ (Fin n)) y) z : ℝ) : EReal) -
          (quadratic_affine_function A b.ofLp c z.ofLp : EReal))) =
        (φ xStar : EReal) := by
    -- Normalize the Riesz pairing to `inner` at the supremum boundary.
    simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hsup
  -- Rewrite the primal conjugate to a supremum of real values and then evaluate that supremum.
  rw [conjugate_function_primal_apply, conjugate_function_apply]
  calc
    sSup (Set.range fun z : EuclideanSpace ℝ (Fin n) ↦
        ((((toDualMap ℝ (EuclideanSpace ℝ (Fin n)) y) z : ℝ) : EReal) -
          (quadratic_affine_function A b.ofLp c z.ofLp : EReal))) =
        (φ xStar : EReal) :=
      hsupDual
    _ =
        (((1 / 2 : ℝ) * dotProduct (y - b).ofLp xStar.ofLp - c : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hvalue
    _ =
        (((1 / 2 : ℝ) * dotProduct (y - b).ofLp
          (Matrix.toEuclideanLin A⁻¹ (y - b)).ofLp - c : ℝ) : EReal) := by
      simp [xStar]

end
