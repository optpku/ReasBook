/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators InnerProduct

universe u v

variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "E₂" => EuclideanSpace ℝ ι

/- Proposition 6.32 [Chapter6_1.json:101] lies in the finite Euclidean affine-minorant /
quadratic-dualization domain.

Sampled owner-style declarations:
- `EuclideanSpace.proj`, the canonical coordinate functionals on `EuclideanSpace ℝ ι`;
- `ContinuousLinearMap.smulRight`, the canonical way to assemble the row family
  `u ↦ ∑ⱼ uⱼ gⱼ` into one linear map;
- `ContinuousLinearMap.adjoint`, written `A†`, the canonical Hilbert adjoint owner;
- mathlib `HasGradientAt`, the canonical global-gradient owner for scalar functions on real
  inner-product spaces.

Best owner abstraction:
- source-facing: the offset vector `b`, the map `Aᵀ`, its adjoint `A`, and the minimization
  objective `φ`;
- core/canonical: `EuclideanSpace ℝ ι`, `ContinuousLinearMap.adjoint`, and `HasGradientAt`;
- bridge/view: the coordinate formulas for `b` and for the adjoint action `Ax`.

Primitive data:
- the row family `g : ι → E`;
- the base points `points : ι → E`;
- the affine offsets `f : ι → ℝ`.

Derived API:
- the Euclidean offset vector `b`;
- the linear map `Aᵀ : E₂ →L[ℝ] E` with `Aᵀ u = ∑ⱼ uⱼ gⱼ`;
- its adjoint `A : E →L[ℝ] E₂`;
- the dual objective `φ(u)` as the infimum of the quadratic affine minorants.

The source is intrinsically finite-dimensional on both sides. This file keeps that source-facing
surface, with `E₂ = EuclideanSpace ℝ ι` and `E` a finite-dimensional real inner-product space,
instead of rebuilding a matrix-only wrapper.
-/

/-- The offset vector `b` with coordinates `bⱼ = ⟪gⱼ, xⱼ⟫ - fⱼ`. -/
def affine_minorant_offset (g points : ι → E) (f : ι → ℝ) : E₂ :=
  (EuclideanSpace.equiv ι ℝ).symm fun j ↦ inner ℝ (g j) (points j) - f j

/-- The row operator `Aᵀ : EuclideanSpace ℝ ι →L[ℝ] E` with
`Aᵀ u = ∑ⱼ uⱼ gⱼ`. -/
def affine_minorant_adjointMap (g : ι → E) : E₂ →L[ℝ] E :=
  ∑ j : ι, (EuclideanSpace.proj j).smulRight (g j)

/-- The Hilbert adjoint `A : E →L[ℝ] EuclideanSpace ℝ ι` of `affine_minorant_adjointMap g`. -/
def affine_minorant_rowMap (g : ι → E) : E →L[ℝ] E₂ :=
  (affine_minorant_adjointMap g)†

/-- The quadratic affine minimand
`x ↦ ∑ⱼ uⱼ (fⱼ + ⟪gⱼ, x - xⱼ⟫) + (1 / 2) ‖x‖²`. -/
def affine_minorant_dualObjectiveMinimand
    (g points : ι → E) (f : ι → ℝ) (u : E₂) : E → ℝ :=
  fun x ↦
    (∑ j : ι, u j * (f j + inner ℝ (g j) (x - points j))) +
      (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)

/-- The dual objective `φ(u)`, defined as the infimum of the quadratic affine minorants over
all `x : E`. -/
def affine_minorant_dualObjective (g points : ι → E) (f : ι → ℝ) : E₂ → ℝ :=
  fun u ↦ sInf (Set.range (affine_minorant_dualObjectiveMinimand g points f u))

/-- Helper for Proposition 6.32 [Chapter6_1.json:101]: rewriting the affine-minorant minimand in
terms of the canonical operators `b` and `Aᵀ`. -/
private lemma affine_minorant_minimand_eq_inner_row_term_sub_inner_offset
    (g points : ι → E) (f : ι → ℝ) (u : E₂) (x : E) :
    affine_minorant_dualObjectiveMinimand g points f u x =
      inner ℝ (affine_minorant_adjointMap g u) x -
        inner ℝ (affine_minorant_offset g points f) u +
          (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
  have hsum_row :
      (∑ j : ι, u j * inner ℝ (g j) x) = inner ℝ (affine_minorant_adjointMap g u) x := by
    -- The `x`-dependent sum is exactly the inner product with `Aᵀ u`.
    calc
      (∑ j : ι, u j * inner ℝ (g j) x) = ∑ j : ι, inner ℝ (u j • g j) x := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simp [real_inner_smul_left]
      _ = inner ℝ (∑ j : ι, u j • g j) x := by
        simpa using
          (sum_inner (s := Finset.univ) (f := fun j : ι ↦ u j • g j) (x := x)).symm
      _ = inner ℝ (affine_minorant_adjointMap g u) x := by
        simp [affine_minorant_adjointMap]
  have hoffset :
      (∑ j : ι, u j * (inner ℝ (g j) (points j) - f j)) =
        inner ℝ (affine_minorant_offset g points f) u := by
    -- The constant part is the Euclidean inner product `⟪b, u⟫`.
    rw [affine_minorant_offset, PiLp.inner_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    have hcoord :
        (((EuclideanSpace.equiv ι ℝ).symm fun k ↦ inner ℝ (g k) (points k) - f k) : E₂) j =
          inner ℝ (g j) (points j) - f j := by
      simpa using
        congrArg (fun h : ι → ℝ ↦ h j)
          ((EuclideanSpace.equiv ι ℝ).symm_apply_apply
            (fun k : ι ↦ inner ℝ (g k) (points k) - f k))
    rw [hcoord]
    calc
      u j * (inner ℝ (g j) (points j) - f j) =
          (inner ℝ (g j) (points j) - f j) * u j := by ring
      _ = inner ℝ (inner ℝ (g j) (points j) - f j) (u j) := by
          change (inner ℝ (g j) (points j) - f j) * u j =
            u j * star (inner ℝ (g j) (points j) - f j)
          simp [mul_comm]
  have hterm :
      ∀ j : ι,
        u j * (f j + inner ℝ (g j) (x - points j)) =
          u j * inner ℝ (g j) x - u j * (inner ℝ (g j) (points j) - f j) := by
    intro j
    -- Each coordinate is an elementary linear expansion of `⟪gⱼ, x - xⱼ⟫`.
    rw [inner_sub_right]
    ring
  -- Expand the finite sum, then substitute the operator identities for the linear and constant
  -- parts.
  calc
    affine_minorant_dualObjectiveMinimand g points f u x
        = (∑ j : ι,
            (u j * inner ℝ (g j) x - u j * (inner ℝ (g j) (points j) - f j))) +
            (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
          simp [affine_minorant_dualObjectiveMinimand, hterm]
    _ = ((∑ j : ι, u j * inner ℝ (g j) x) -
          (∑ j : ι, u j * (inner ℝ (g j) (points j) - f j))) +
          (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
          rw [Finset.sum_sub_distrib]
    _ = inner ℝ (affine_minorant_adjointMap g u) x -
          inner ℝ (affine_minorant_offset g points f) u +
            (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
          rw [hsum_row, hoffset]

/-- Helper for Proposition 6.32 [Chapter6_1.json:101]: completing the square in the primal
variable reduces the minimand to a translated quadratic norm. -/
private lemma affine_minorant_minimand_eq_completed_square
    (g points : ι → E) (f : ι → ℝ) (u : E₂) (x : E) :
    affine_minorant_dualObjectiveMinimand g points f u x =
      (-inner ℝ (affine_minorant_offset g points f) u -
        (1 / 2 : ℝ) * ‖affine_minorant_adjointMap g u‖ ^ (2 : ℕ)) +
          (1 / 2 : ℝ) * ‖x + affine_minorant_adjointMap g u‖ ^ (2 : ℕ) := by
  have hsquare :
      inner ℝ (affine_minorant_adjointMap g u) x -
          inner ℝ (affine_minorant_offset g points f) u +
            (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) =
        (-inner ℝ (affine_minorant_offset g points f) u -
          (1 / 2 : ℝ) * ‖affine_minorant_adjointMap g u‖ ^ (2 : ℕ)) +
            (1 / 2 : ℝ) * ‖x + affine_minorant_adjointMap g u‖ ^ (2 : ℕ) := by
    -- The cross term in `‖x + Aᵀ u‖²` is exactly `2 ⟪Aᵀ u, x⟫`.
    rw [norm_add_sq_real, real_inner_comm x (affine_minorant_adjointMap g u)]
    ring
  -- After the operator rewrite, the square completion is a scalar identity.
  rw [affine_minorant_minimand_eq_inner_row_term_sub_inner_offset]
  exact hsquare

/-- Helper for Proposition 6.32 [Chapter6_1.json:101]: translating a nonnegative quadratic does
not change the value of its infimum after adding a constant. -/
private lemma iInf_const_add_half_norm_sq_eq
    (c : ℝ) (a : E) :
    (⨅ x : E, c + (1 / 2 : ℝ) * ‖x + a‖ ^ (2 : ℕ)) = c := by
  rw [← sInf_range]
  apply le_antisymm
  · -- The witness `x = -a` makes the translated norm vanish.
    refine csInf_le ?_ ?_
    · refine ⟨c, ?_⟩
      intro y hy
      rcases hy with ⟨x, rfl⟩
      have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖x + a‖ ^ (2 : ℕ) := by
        positivity
      linarith
    · refine ⟨(-a : E), ?_⟩
      simp
  · -- Every translated quadratic term is nonnegative, so the whole family stays above `c`.
    refine le_csInf ?_ ?_
    · exact ⟨c, ⟨(-a : E), by simp⟩⟩
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖x + a‖ ^ (2 : ℕ) := by
        positivity
      linarith

/-- Helper for Proposition 6.32 [Chapter6_1.json:101]: the linear functional
`u ↦ -⟪b, u⟫` has gradient `-b`. -/
private lemma hasGradientAt_neg_inner_offset
    (g points : ι → E) (f : ι → ℝ) (u : E₂) :
    HasGradientAt
      (fun v : E₂ ↦ -inner ℝ (affine_minorant_offset g points f) v)
      (-affine_minorant_offset g points f)
      u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  -- The linear functional is already represented by the Riesz map.
  simpa [InnerProductSpace.toDual_apply_apply] using
    ((InnerProductSpace.toDual ℝ E₂ (-affine_minorant_offset g points f)).hasFDerivAt :
      HasFDerivAt
        (fun v : E₂ ↦
          (InnerProductSpace.toDual ℝ E₂ (-affine_minorant_offset g points f)) v)
        (InnerProductSpace.toDual ℝ E₂ (-affine_minorant_offset g points f))
        u)

/-- Helper for Proposition 6.32 [Chapter6_1.json:101]: the negative half squared norm of `Aᵀ u`
has gradient `-A(Aᵀ u)`. -/
private lemma hasGradientAt_neg_half_norm_sq_comp_affine_minorant_adjointMap
    (g : ι → E) (u : E₂) :
    HasGradientAt
      (fun v : E₂ ↦ -(1 / 2 : ℝ) * ‖affine_minorant_adjointMap g v‖ ^ (2 : ℕ))
      (-affine_minorant_rowMap g (affine_minorant_adjointMap g u))
      u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hA :
      HasFDerivAt
        (fun v : E₂ ↦ affine_minorant_adjointMap g v)
        (affine_minorant_adjointMap g)
        u := by
    -- The derivative of a continuous linear map is the map itself.
    simpa using (affine_minorant_adjointMap g).hasFDerivAt
  have hscaled :
      HasFDerivAt
        (fun v : E₂ ↦ -(1 / 2 : ℝ) * ‖affine_minorant_adjointMap g v‖ ^ (2 : ℕ))
        (-(1 / 2 : ℝ) •
          (2 • (innerSL ℝ (affine_minorant_adjointMap g u)).comp
            (affine_minorant_adjointMap g)))
        u := by
    -- Differentiate the squared norm, then scale by `-(1 / 2)`.
    simpa [smul_eq_mul] using (hA.norm_sq.const_smul (-(1 / 2 : ℝ)))
  have hderiv :
      (-(1 / 2 : ℝ) •
        (2 • (innerSL ℝ (affine_minorant_adjointMap g u)).comp
          (affine_minorant_adjointMap g))) =
        InnerProductSpace.toDual ℝ E₂
          (-affine_minorant_rowMap g (affine_minorant_adjointMap g u)) := by
    -- `innerSL_apply_comp` turns the chain-rule output into the adjoint action `A(Aᵀ u)`.
    ext v
    simp [ContinuousLinearMap.innerSL_apply_comp, affine_minorant_rowMap,
      InnerProductSpace.toDual_apply_apply]
  rw [hderiv] at hscaled
  simpa [InnerProductSpace.toDual_apply_apply] using hscaled

-- Proof sketch: expand the affine term, rewrite the linear part as
-- `⟪Aᵀ u, x⟫ - ⟪b, u⟫`, and complete the square in `x`; the minimizer is `x = -Aᵀ u`.
/-- Closed-form evaluation used in Proposition 6.32 [Chapter6_1.json:101]: the infimum defining
`φ(u)` is the explicit quadratic expression `-⟪b, u⟫ - (1 / 2) ‖Aᵀ u‖²`. -/
theorem affine_minorant_dualObjective_eq_neg_inner_offset_sub_half_norm_sq
    (g points : ι → E) (f : ι → ℝ) (u : E₂) :
    affine_minorant_dualObjective g points f u =
      -inner ℝ (affine_minorant_offset g points f) u -
        (1 / 2 : ℝ) * ‖affine_minorant_adjointMap g u‖ ^ (2 : ℕ) := by
  -- Rewrite the infimum as an `iInf`, then apply the completed-square normal form.
  rw [affine_minorant_dualObjective, sInf_range]
  have hfun :
      affine_minorant_dualObjectiveMinimand g points f u =
        fun x : E ↦
          (-inner ℝ (affine_minorant_offset g points f) u -
            (1 / 2 : ℝ) * ‖affine_minorant_adjointMap g u‖ ^ (2 : ℕ)) +
              (1 / 2 : ℝ) * ‖x + affine_minorant_adjointMap g u‖ ^ (2 : ℕ) := by
    -- The completed-square identity is pointwise, so it upgrades to a function equality.
    funext x
    exact affine_minorant_minimand_eq_completed_square g points f u x
  rw [hfun]
  exact
    iInf_const_add_half_norm_sq_eq
      (-inner ℝ (affine_minorant_offset g points f) u -
        (1 / 2 : ℝ) * ‖affine_minorant_adjointMap g u‖ ^ (2 : ℕ))
      (affine_minorant_adjointMap g u)

-- Proof sketch: first rewrite `φ` by the closed formula above, then differentiate the linear term
-- and the negative quadratic norm term; the latter contributes `-A(Aᵀ u)`.
/-- Proposition 6.32 [Chapter6_1.json:101] (2): the dual objective is differentiable on
`EuclideanSpace ℝ ι`, and at every `u` its gradient is `-b - A(Aᵀ u)`, encoded by the canonical
pointwise owner `HasGradientAt`. -/
theorem affine_minorant_dualObjective_hasGradientAt
    (g points : ι → E) (f : ι → ℝ) (u : E₂) :
    HasGradientAt
      (affine_minorant_dualObjective g points f)
      (-affine_minorant_offset g points f -
        affine_minorant_rowMap g (affine_minorant_adjointMap g u))
      u := by
  have hclosedForm :
      affine_minorant_dualObjective g points f =
        fun v : E₂ ↦
          -inner ℝ (affine_minorant_offset g points f) v -
            (1 / 2 : ℝ) * ‖affine_minorant_adjointMap g v‖ ^ (2 : ℕ) := by
    -- The first part identifies the dual objective with its closed-form expression everywhere.
    funext v
    exact affine_minorant_dualObjective_eq_neg_inner_offset_sub_half_norm_sq g points f v
  rw [hclosedForm, sub_eq_add_neg]
  -- Differentiate the linear and quadratic pieces separately, then add their gradients.
  have hsumGradient :=
    (((hasGradientAt_neg_inner_offset g points f u).hasFDerivAt).add
      ((hasGradientAt_neg_half_norm_sq_comp_affine_minorant_adjointMap g u).hasFDerivAt)).hasGradientAt
  simpa [sub_eq_add_neg] using hsumGradient
