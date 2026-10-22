/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_1_5.Index
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_1_3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Basic

open Matrix
open Filter

noncomputable section

section

variable {n : ℕ}

local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "Point" => EuclideanSpace ℝ (Fin n)
variable {x : ℕ → Point} {α : ℕ → ℝ}

-- Domain sampling for this item:
-- * source-facing: steepest descent with exact line search on the centered quadratic objective
--   `x ↦ (1 / 2) * xᵀ G x`;
-- * core/canonical: the project quadratic owner `quadraticObjective G b c`,
--   `gradient_quadraticObjective`, `steepestDescentDirection`,
--   `IsExactLineSearchStepOnNonnegativeRay`, `posDefEigenvalues`, `ellipsoidNorm`, and the
--   Euclidean norm owner `‖·‖₂`, together with the Chapter 3 run owner
--   `IsSteepestDescentSequence`;
-- * bridge/view: the centered specialization `quadraticObjective G 0 0`, together with the
--   quadratic-gradient identity and the nonstationary closed-form exact line-search step size.
--
-- Triage:
-- * source-facing: the centered quadratic objective and the exact-line-search steepest-descent
--   iterates attached to it;
-- * core/canonical: the project quadratic owner `quadraticObjective G b c`;
-- * bridge/view: `quadraticObjective G 0 0`.
--
-- Primitive data for this theorem family are the iterate sequence `x`, the step sizes `α`, and
-- the Chapter 3 owner `IsSteepestDescentSequence f x α`. The one-step contraction clauses record
-- their ratio domain directly by the nonstationary-step hypothesis `x k ≠ 0`, rather than
-- carrying the heavier algorithm wrapper with tolerance, initial point, and auxiliary streams.

section CenteredQuadraticObjective

variable (G : MatrixN)

local notation "f" => quadraticObjective G 0 0

/-- Helper for Chapter03 Theorem 3.1.5: the centered quadratic objective is strictly positive
away from the minimizer `0`. -/
theorem centeredQuadraticObjective_pos_of_ne_zero
    (hG : G.PosDef) {x : Point} (hx : x ≠ 0) :
    0 < quadraticObjective G 0 0 x := by
  have hQuad :
      0 < dotProduct x (G.mulVec x) := by
    -- Positive definiteness makes the centered quadratic form strictly positive.
    simpa [Matrix.toEuclideanLin_apply] using
      hG.dotProduct_mulVec_pos (x := x.ofLp) (by simpa using hx)
  -- The centered objective is one half of that positive quadratic form.
  have hHalf :
      0 < (1 / 2 : ℝ) * dotProduct x (G.mulVec x) := by
    nlinarith
  simpa [quadraticObjective_apply, Matrix.toEuclideanLin_apply] using hHalf

/-- Helper for Chapter03 Theorem 3.1.5: along the centered steepest-descent ray, the quadratic
objective becomes a completed square centered at the textbook closed-form step size. -/
theorem centeredQuadraticObjective_lineSearchProfile_eq_completedSquare
    (hG : G.PosDef) {x : Point} (hx : x ≠ 0) (β : ℝ) :
    let g : Point := Matrix.toEuclideanLin G x
    let a : ℝ := dotProduct g g
    let c : ℝ := dotProduct g (G.mulVec g)
    lineSearchObjective f x (steepestDescentDirection f x) β =
      quadraticObjective G 0 0 x - a ^ (2 : ℕ) / (2 * c) +
        (c / 2) * (β - a / c) ^ (2 : ℕ) := by
  let _ := hG.isUnit.invertible
  have hGsymm : G.IsSymm := posDef_isSymm hG
  let g : Point := Matrix.toEuclideanLin G x
  let a : ℝ := dotProduct g g
  let c : ℝ := dotProduct g (G.mulVec g)
  have hGrad : gradient f x = g := by
    simpa [f, g] using gradient_quadraticObjective G 0 0 hGsymm x
  have hg_ne : g ≠ 0 := by
    -- The Hessian action is injective because a positive-definite matrix is invertible.
    intro hg0
    apply hx
    have h0 := congrArg (Matrix.toEuclideanLin G⁻¹) hg0
    simpa [g, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] using h0
  have hc_pos : 0 < c := by
    -- The quadratic coefficient of the ray profile is positive away from the stationary point.
    simpa [c, g] using hG.dotProduct_mulVec_pos (x := g.ofLp) (by simpa using hg_ne)
  have hProfile :
      lineSearchObjective f x (steepestDescentDirection f x) β =
        quadraticObjective G 0 0 x - β * a + (β ^ (2 : ℕ) / 2 : ℝ) * c := by
    have hExpand :=
      quadraticObjective_eq_at_reference_add_gradient_displacement G 0 0 hGsymm x
        (-(β : ℝ) • g)
    have hLinear :
        dotProduct ((gradient f x : Point)) (-(β : ℝ) • g) = -β * a := by
      -- The linear term is exactly the textbook `-β * gᵀ g`.
      rw [hGrad]
      rw [dotProduct_smul]
      simp [a]
      ring
    have hQuadratic :
        (1 / 2 : ℝ) * dotProduct (-(β : ℝ) • g) (G.mulVec (-(β : ℝ) • g)) =
          (β ^ (2 : ℕ) / 2 : ℝ) * c := by
      have hMul : G.mulVec (-(β : ℝ) • g) = -(β : ℝ) • G.mulVec g := by
        simpa using (Matrix.mulVec_smul G (-β) g.ofLp)
      -- The quadratic remainder is the positive coefficient `c / 2` times `β^2`.
      rw [hMul]
      simp [smul_dotProduct, dotProduct_smul, c]
    calc
      lineSearchObjective f x (steepestDescentDirection f x) β
          = quadraticObjective G 0 0 (x + (-(β : ℝ) • g)) := by
              rw [lineSearchObjective, steepestDescentDirection, hGrad]
              simp [g]
      _ = quadraticObjective G 0 0 x +
            dotProduct ((gradient f x : Point)) (-(β : ℝ) • g) +
            (1 / 2 : ℝ) * dotProduct (-(β : ℝ) • g) (G.mulVec (-(β : ℝ) • g)) := hExpand
      _ = quadraticObjective G 0 0 x - β * a + (β ^ (2 : ℕ) / 2 : ℝ) * c := by
            rw [hLinear, hQuadratic]
            ring
  calc
    lineSearchObjective f x (steepestDescentDirection f x) β
        = quadraticObjective G 0 0 x - β * a + (β ^ (2 : ℕ) / 2 : ℝ) * c := hProfile
    _ = quadraticObjective G 0 0 x - a ^ (2 : ℕ) / (2 * c) + (c / 2) * (β - a / c) ^ (2 : ℕ) := by
          -- Completing the square exposes the unique minimizer of the one-dimensional profile.
          have hc_ne : c ≠ 0 := hc_pos.ne'
          field_simp [hc_ne]
          ring

/-- Helper for Chapter03 Theorem 3.1.5: substituting the closed-form step size into the
completed-square profile gives the textbook one-step decrease formula. -/
theorem centeredQuadraticObjective_closedForm_step_suboptimality
    (hG : G.PosDef) {x : Point} (hx : x ≠ 0) :
    let g : Point := Matrix.toEuclideanLin G x
    let a : ℝ := dotProduct g g
    let c : ℝ := dotProduct g (G.mulVec g)
    let αcf := a / c
    quadraticObjective G 0 0 (steepestDescentStep f x αcf) =
      quadraticObjective G 0 0 x - a ^ (2 : ℕ) / (2 * c) := by
  let _ := hG.isUnit.invertible
  let g : Point := Matrix.toEuclideanLin G x
  let a : ℝ := dotProduct g g
  let c : ℝ := dotProduct g (G.mulVec g)
  let αcf : ℝ := a / c
  have hg_ne : g ≠ 0 := by
    -- Positive definiteness makes `G` invertible, so `G x = 0` would force `x = 0`.
    intro hg0
    apply hx
    have h0 := congrArg (Matrix.toEuclideanLin G⁻¹) hg0
    simpa [g, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] using h0
  have hc_pos : 0 < c := by
    -- The completed-square coefficient is positive away from the stationary point.
    simpa [c, g] using hG.dotProduct_mulVec_pos (x := g.ofLp) (by simpa using hg_ne)
  have hProfile :=
    centeredQuadraticObjective_lineSearchProfile_eq_completedSquare
      (G := G) hG hx αcf
  calc
    quadraticObjective G 0 0 (steepestDescentStep f x αcf)
        = lineSearchObjective f x (steepestDescentDirection f x) αcf := by
            -- The textbook step is exactly the point on the steepest-descent ray at `αcf`.
            rw [lineSearchObjective, steepestDescentStep]
    _ = quadraticObjective G 0 0 x - a ^ (2 : ℕ) / (2 * c) +
          (c / 2) * (αcf - a / c) ^ (2 : ℕ) := by
            simpa [g, a, c, αcf] using hProfile
    _ = quadraticObjective G 0 0 x - a ^ (2 : ℕ) / (2 * c) := by
          -- At the center of the completed square, the quadratic remainder vanishes.
          have hc_ne : c ≠ 0 := hc_pos.ne'
          simp [αcf, hc_ne]

/-- Helper for Chapter03 Theorem 3.1.5: at the stationary point `0`, the centered quadratic is
constant along the steepest-descent ray, so the exact line-search step is `0`. -/
theorem centeredQuadraticObjective_zero_exactLineSearch
    (hG : G.PosDef) :
    IsExactLineSearchStepOnNonnegativeRay
      (quadraticObjective G (0 : Point) (0 : ℝ))
      0
      (steepestDescentDirection (quadraticObjective G (0 : Point) (0 : ℝ)) 0)
      0 := by
  change IsExactLineSearchStepOnNonnegativeRay f 0 (steepestDescentDirection f 0) 0
  have hGsymm : G.IsSymm := posDef_isSymm hG
  have hGradZero :
      gradient f 0 = 0 := by
    simpa using gradient_quadraticObjective G 0 0 hGsymm (0 : Point)
  have hDirZero :
      steepestDescentDirection f 0 = 0 := by
    simp [steepestDescentDirection, hGradZero]
  refine ⟨by simp, ?_⟩
  refine isMinOn_iff.mpr ?_
  intro β hβ
  -- The centered quadratic has zero gradient at `0`, so the whole search ray collapses to `0`.
  simpa [lineSearchObjective, hDirZero]

/-- On a nonstationary iterate of a symmetric positive-definite quadratic objective, the exact
line-search step on the steepest descent ray is given by the classical quadratic closed form. -/
theorem centeredQuadraticObjective_closedForm_exactLineSearch
    (hG : G.PosDef) {x : Point} (hx : x ≠ 0) :
    IsExactLineSearchStepOnNonnegativeRay
      f
      x
      (steepestDescentDirection f x)
      (dotProduct (G.mulVec x) (G.mulVec x) /
        dotProduct (G.mulVec x) (G.mulVec (G.mulVec x))) := by
  let _ := hG.isUnit.invertible
  let g : Point := Matrix.toEuclideanLin G x
  let a : ℝ := dotProduct g g
  let c : ℝ := dotProduct g (G.mulVec g)
  let αcf : ℝ := a / c
  have hg_ne : g ≠ 0 := by
    -- Route correction: keep the proof on the source ray `g = G x`, rather than switching to
    -- a recursion argument. Invertibility of `G` identifies nonstationarity with `g ≠ 0`.
    intro hg0
    apply hx
    have h0 := congrArg (Matrix.toEuclideanLin G⁻¹) hg0
    simpa [g, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] using h0
  have hc_pos : 0 < c := by
    -- Positive definiteness makes the quadratic coefficient of the ray strictly positive.
    simpa [c, g] using hG.dotProduct_mulVec_pos (x := g.ofLp) (by simpa using hg_ne)
  have hnorm_sq : ‖g‖ ^ (2 : ℕ) = a := by
    simpa [g, a, dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq g)
  have ha_nonneg : 0 ≤ a := by
    nlinarith [sq_nonneg ‖g‖, hnorm_sq]
  have hαcf_nonneg : 0 ≤ αcf := by
    -- The closed-form step size is feasible because its numerator is a norm square.
    exact div_nonneg ha_nonneg hc_pos.le
  have hAtClosedForm :
      lineSearchObjective f x (steepestDescentDirection f x) αcf =
        quadraticObjective G 0 0 x - a ^ (2 : ℕ) / (2 * c) := by
    -- First rewrite the line-search value at `αcf` through the closed-form step formula.
    calc
      lineSearchObjective f x (steepestDescentDirection f x) αcf
          = quadraticObjective G 0 0 (steepestDescentStep f x αcf) := by
              rw [lineSearchObjective, steepestDescentStep]
      _ = quadraticObjective G 0 0 x - a ^ (2 : ℕ) / (2 * c) := by
            simpa [g, a, c, αcf] using
              centeredQuadraticObjective_closedForm_step_suboptimality
                (G := G) hG hx
  refine (isExactLineSearchStepOnNonnegativeRay_iff _ _ _ _).2 ?_
  refine ⟨?_, ?_⟩
  · simpa [g, a, c, αcf, Matrix.toEuclideanLin_apply] using hαcf_nonneg
  · intro β hβ
    have hProfileβ :=
      centeredQuadraticObjective_lineSearchProfile_eq_completedSquare
        (G := G) hG hx β
    have hSquare_nonneg : 0 ≤ (β - a / c) ^ (2 : ℕ) := by
      positivity
    have hCorrection_nonneg : 0 ≤ (c / 2) * (β - a / c) ^ (2 : ℕ) := by
      nlinarith [hc_pos, hSquare_nonneg]
    -- The completed-square expansion shows every feasible `β` has value at least the center.
    calc
      lineSearchObjective f x (steepestDescentDirection f x) αcf
          = quadraticObjective G 0 0 x - a ^ (2 : ℕ) / (2 * c) := hAtClosedForm
      _ ≤ quadraticObjective G 0 0 x - a ^ (2 : ℕ) / (2 * c) +
            (c / 2) * (β - a / c) ^ (2 : ℕ) := by
              linarith
      _ = lineSearchObjective f x (steepestDescentDirection f x) β := by
            simpa [g, a, c] using hProfileβ.symm

/-- Helper for Chapter03 Theorem 3.1.5: on the centered quadratic, replacing `x` by
`G⁻¹ (G x)` rewrites the objective denominator into the textbook inverse-gradient quadratic
form. -/
theorem centeredQuadraticObjective_eq_half_inverse_gradient_quadratic
    (hG : G.PosDef) (x : Point) :
    let g : Point := G.mulVec x
    quadraticObjective G 0 0 x = (1 / 2 : ℝ) * dotProduct g (G⁻¹.mulVec g) := by
  let _ := hG.isUnit.invertible
  let g : Point := Matrix.toEuclideanLin G x
  have hx_inv : x = Matrix.toEuclideanLin G⁻¹ g := by
    -- Applying the inverse matrix to `g = G x` recovers the original point.
    show x = Matrix.toEuclideanLin G⁻¹ (Matrix.toEuclideanLin G x)
    simpa [g, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] using (rfl : x = x)
  calc
    quadraticObjective G 0 0 x
        = (1 / 2 : ℝ) * dotProduct x g := by
            simp [quadraticObjective_apply, g]
    _ = (1 / 2 : ℝ) * dotProduct (Matrix.toEuclideanLin G⁻¹ g) g := by
          rw [← hx_inv]
    _ = (1 / 2 : ℝ) * dotProduct g (Matrix.toEuclideanLin G⁻¹ g) := by
          rw [dotProduct_comm]
    _ = (1 / 2 : ℝ) * dotProduct (G.mulVec x) (G⁻¹.mulVec (G.mulVec x)) := by
          simp [g, Matrix.toEuclideanLin_apply]

/-- Helper for Chapter03 Theorem 3.1.5: the theorem-local finite-coordinate Kantorovich bound
transfers back to the public `Point` surface by the tautological `ofLp` identification. -/
theorem centeredQuadraticObjective_kantorovich_ratio_bound
    {lambdaMax lambdaMin : ℝ}
    (hG : G.PosDef)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
    {g : Point} (hg : g ≠ 0) :
    ((dotProduct g g) ^ (2 : ℕ)) /
        (dotProduct g (G.mulVec g) * dotProduct g (G⁻¹.mulVec g)) ≥
      ((4 : ℝ) * lambdaMax * lambdaMin) / (lambdaMax + lambdaMin) ^ (2 : ℕ) := by
  -- Route correction: keep the spectral proof on `Fin n → ℝ`, then transport back only once.
  simpa [Matrix.toEuclideanLin_apply] using
    KantorovichLocal.centeredQuadraticObjective_kantorovich_ratio_bound_fin
      (G := G) (hG := hG) lambdaMax lambdaMin hLambdaMax hLambdaMin
      (x := g.ofLp) (by simpa using hg)

/-- Helper for Chapter03 Theorem 3.1.5: the actual exact line-search step is no worse than the
source closed-form trial step on the same steepest-descent ray. -/
theorem steepestDescentQuadratic_exactStep_le_closedFormTrial
    (hG : G.PosDef) {x : ℕ → Point} {α : ℕ → ℝ}
    (hSeq : IsSteepestDescentSequence f x α) (k : ℕ) (hk : x k ≠ 0) :
    let g : Point := G.mulVec (x k)
    let αcf : ℝ := dotProduct g g / dotProduct g (G.mulVec g)
    quadraticObjective G 0 0 (x (k + 1)) ≤
      quadraticObjective G 0 0 (steepestDescentStep f (x k) αcf) := by
  let g : Point := G.mulVec (x k)
  let αcf : ℝ := dotProduct g g / dotProduct g (G.mulVec g)
  have hClosedForm :
      IsExactLineSearchStepOnNonnegativeRay
        f
        (x k)
        (steepestDescentDirection f (x k))
        αcf := by
    -- The closed-form step is itself exact on a nonstationary centered quadratic iterate.
    simpa [g, αcf] using centeredQuadraticObjective_closedForm_exactLineSearch (G := G) hG hk
  have hClosedForm_nonneg : 0 ≤ αcf := hClosedForm.nonneg
  have hOptimal :
      lineSearchObjective f (x k) (steepestDescentDirection f (x k)) (α k) ≤
        lineSearchObjective f (x k) (steepestDescentDirection f (x k)) αcf :=
    (hSeq.exactLineSearch k).optimal hClosedForm_nonneg
  calc
    quadraticObjective G 0 0 (x (k + 1))
        = quadraticObjective G 0 0 (steepestDescentStep f (x k) (α k)) := by
            -- The iterate update identifies the accepted next point with the algorithm step.
            simpa using congrArg (quadraticObjective G 0 0) (hSeq.update k)
    _ ≤ quadraticObjective G 0 0 (steepestDescentStep f (x k) αcf) := by
          -- Compare the accepted exact step against the closed-form exact step on the same ray.
          simpa [lineSearchObjective, steepestDescentStep] using hOptimal

/-- Helper for Chapter03 Theorem 3.1.5: on a positive-definite centered quadratic, the objective
is one half of the squared `G`-energy. -/
theorem centeredQuadraticObjective_eq_half_ellipsoidNorm_sq
    (hG : G.PosDef) (z : Point) :
    quadraticObjective G 0 0 z = (1 / 2 : ℝ) * (ellipsoidNorm G z) ^ (2 : ℕ) := by
  have hquad_nonneg : 0 ≤ z.ofLp ⬝ᵥ (G *ᵥ z.ofLp) := by
    by_cases hz : z = 0
    · subst hz
      simp
    · exact (hG.dotProduct_mulVec_pos (x := z.ofLp) (by simpa using hz)).le
  -- Rewrite the objective and the ellipsoid norm to the same quadratic form, then square the
  -- square root back to the textbook identity `2 f = ‖z‖_G^2`.
  calc
    quadraticObjective G 0 0 z = (1 / 2 : ℝ) * (z.ofLp ⬝ᵥ (G *ᵥ z.ofLp)) := by
      simp [quadraticObjective_apply, Matrix.toEuclideanLin_apply]
    _ = (1 / 2 : ℝ) * (Real.sqrt (z.ofLp ⬝ᵥ (G *ᵥ z.ofLp))) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt hquad_nonneg]
    _ = (1 / 2 : ℝ) * (ellipsoidNorm G z) ^ (2 : ℕ) := by
      rfl

/-- Helper for Chapter03 Theorem 3.1.5: once a centered steepest-descent iterate reaches the
minimizer `0`, the next iterate stays at `0`. -/
theorem steepestDescentQuadratic_zero_tail
    (hG : G.PosDef)
    {x : ℕ → Point} {α : ℕ → ℝ}
    (hSeq : IsSteepestDescentSequence f x α)
    (k : ℕ) (hk : x k = 0) :
    x (k + 1) = 0 := by
  have hGsymm : G.IsSymm := posDef_isSymm hG
  -- At the minimizer, the steepest-descent direction is `0`, so the update stays fixed.
  simpa [hk, steepestDescentStep, steepestDescentDirection,
    gradient_quadraticObjective G 0 0 hGsymm (0 : Point)] using hSeq.update k

section SpectralContraction

variable {lambdaMax lambdaMin : ℝ}
variable (hG : G.PosDef)
variable (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
variable (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
variable {x : ℕ → Point} {α : ℕ → ℝ}
variable (hSeq : IsSteepestDescentSequence f x α)

/-- Helper for Chapter03 Theorem 3.1.5: the closed-form exact step plus the local Kantorovich
bound gives the sharp one-step objective contraction from the source proof. -/
theorem steepestDescentQuadratic_objective_step_mul_bound
    (hG : G.PosDef)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
    {x : ℕ → Point} {α : ℕ → ℝ}
    (hSeq : IsSteepestDescentSequence f x α)
    (k : ℕ) (hk : x k ≠ 0) :
    quadraticObjective G 0 0 (x (k + 1)) ≤
      (((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) ^ (2 : ℕ)) *
        quadraticObjective G 0 0 (x k) := by
  let _ : Invertible G := (show IsUnit G from hG.isUnit).invertible
  let g : Point := G.mulVec (x k)
  let a : ℝ := dotProduct g g
  let c : ℝ := dotProduct g (G.mulVec g)
  let d : ℝ := dotProduct g (G⁻¹.mulVec g)
  let q : ℝ := (lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)
  have hStep :
      quadraticObjective G 0 0 (x (k + 1)) ≤
        quadraticObjective G 0 0 (x k) - a ^ (2 : ℕ) / (2 * c) := by
    calc
      quadraticObjective G 0 0 (x (k + 1))
          ≤ quadraticObjective G 0 0 (steepestDescentStep f (x k) (a / c)) := by
              -- Compare the accepted exact step against the source closed-form exact step.
              simpa [g, a, c] using
                steepestDescentQuadratic_exactStep_le_closedFormTrial
                  (G := G) hG hSeq k hk
      _ = quadraticObjective G 0 0 (x k) - a ^ (2 : ℕ) / (2 * c) := by
            -- The completed-square profile gives the textbook exact decrease.
            simpa [g, a, c] using
              centeredQuadraticObjective_closedForm_step_suboptimality
                (G := G) hG hk
  have hg_ne : g ≠ 0 := by
    -- Invertibility of `G` identifies nonstationarity with a nonzero gradient ray.
    intro hg0
    apply hk
    have h0 := congrArg (Matrix.toEuclideanLin G⁻¹) hg0
    simpa [g, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] using h0
  have hc_pos : 0 < c := by
    -- The ray curvature is positive on every nonstationary centered quadratic iterate.
    simpa [c, g] using hG.dotProduct_mulVec_pos (x := g.ofLp) (by simpa using hg_ne)
  have hd_pos : 0 < d := by
    -- The inverse quadratic form is positive for the same nonzero gradient ray.
    simpa [d, g, Matrix.toEuclideanLin_apply] using
      hG.inv.dotProduct_mulVec_pos (x := g.ofLp) (by simpa using hg_ne)
  have hObj :
      quadraticObjective G 0 0 (x k) = (1 / 2 : ℝ) * d := by
    -- Rewrite the current objective exactly as the inverse-gradient quadratic form.
    simpa [g, d, Matrix.toEuclideanLin_apply] using
      centeredQuadraticObjective_eq_half_inverse_gradient_quadratic
        (G := G) hG (x k)
  have hK :
      ((4 : ℝ) * lambdaMax * lambdaMin) / (lambdaMax + lambdaMin) ^ (2 : ℕ) ≤
        a ^ (2 : ℕ) / (c * d) := by
    -- The source quotient `(gᵀ g)^2 / ((gᵀ G g) (gᵀ G⁻¹ g))` has the sharp spectral lower bound.
    simpa [a, c, d, g, Matrix.toEuclideanLin_apply, mul_assoc, mul_left_comm, mul_comm] using
      centeredQuadraticObjective_kantorovich_ratio_bound
        (G := G) (hG := hG) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
        hLambdaMax hLambdaMin (g := g) hg_ne
  rcases (isGreatest_posDefEigenvalues_iff G hG lambdaMax).1 hLambdaMax with
    ⟨⟨iMax, hiMax⟩, _hUpperEig⟩
  rcases (isLeast_posDefEigenvalues_iff G hG lambdaMin).1 hLambdaMin with
    ⟨⟨iMin, hiMin⟩, _hLowerEig⟩
  have hLambdaMinPos : 0 < lambdaMin := by
    -- The least positive-definite eigenvalue is still positive.
    rw [← hiMin]
    simpa [posDefEigenvalues_def] using hG.eigenvalues_pos iMin
  have hLambdaMaxPos : 0 < lambdaMax := by
    -- The greatest positive-definite eigenvalue is still positive.
    rw [← hiMax]
    simpa [posDefEigenvalues_def] using hG.eigenvalues_pos iMax
  have hq_sq :
      q ^ (2 : ℕ) =
        1 - ((4 : ℝ) * lambdaMax * lambdaMin) / (lambdaMax + lambdaMin) ^ (2 : ℕ) := by
    have hq_def : q = (lambdaMax - lambdaMin) / (lambdaMax + lambdaMin) := rfl
    have hSum_ne : lambdaMax + lambdaMin ≠ 0 := by positivity
    rw [hq_def]
    field_simp [hSum_ne]
    ring
  have hOneMinus :
      1 - a ^ (2 : ℕ) / (c * d) ≤ q ^ (2 : ℕ) := by
    -- Subtract the sharp spectral lower bound from `1`.
    rw [hq_sq]
    nlinarith
  have hRewrite :
      quadraticObjective G 0 0 (x k) - a ^ (2 : ℕ) / (2 * c) =
        (1 - a ^ (2 : ℕ) / (c * d)) * quadraticObjective G 0 0 (x k) := by
    have hc_ne : c ≠ 0 := hc_pos.ne'
    have hd_ne : d ≠ 0 := hd_pos.ne'
    -- Factor the objective drop through the source ratio `1 - (gᵀ g)^2 / ((gᵀ G g)(gᵀ G⁻¹ g))`.
    rw [hObj]
    field_simp [hc_ne, hd_ne]
  calc
    quadraticObjective G 0 0 (x (k + 1))
        ≤ quadraticObjective G 0 0 (x k) - a ^ (2 : ℕ) / (2 * c) := hStep
    _ = (1 - a ^ (2 : ℕ) / (c * d)) * quadraticObjective G 0 0 (x k) := hRewrite
    _ ≤ q ^ (2 : ℕ) * quadraticObjective G 0 0 (x k) := by
          -- Multiply the scalar bound `1 - ratio ≤ q^2` by the positive current objective.
          exact mul_le_mul_of_nonneg_right hOneMinus
            (by rw [hObj]; nlinarith [hd_pos])
    _ = (((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) ^ (2 : ℕ)) *
          quadraticObjective G 0 0 (x k) := by
          simp [q]

/-- Helper for Chapter03 Theorem 3.1.5: the least and greatest positive-definite eigenvalue
endpoints are positive and ordered. -/
theorem posDef_eigenvalue_endpoints_pos_le
    (hG : G.PosDef)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin) :
    0 < lambdaMin ∧ 0 < lambdaMax ∧ lambdaMin ≤ lambdaMax := by
  rcases (isGreatest_posDefEigenvalues_iff G hG lambdaMax).1 hLambdaMax with
    ⟨⟨iMax, hiMax⟩, _hUpperEig⟩
  rcases (isLeast_posDefEigenvalues_iff G hG lambdaMin).1 hLambdaMin with
    ⟨⟨iMin, hiMin⟩, _hLowerEig⟩
  have hLambdaMinPos : 0 < lambdaMin := by
    -- The least positive-definite eigenvalue is still strictly positive.
    rw [← hiMin]
    simpa [posDefEigenvalues_def] using hG.eigenvalues_pos iMin
  have hLambdaMaxPos : 0 < lambdaMax := by
    -- The greatest positive-definite eigenvalue is still strictly positive.
    rw [← hiMax]
    simpa [posDefEigenvalues_def] using hG.eigenvalues_pos iMax
  exact ⟨hLambdaMinPos, hLambdaMaxPos, hLambdaMin.2 hLambdaMax.1⟩

-- The next theorem is the explicit-binder core behind the public theorem (2).
/-- Helper for Chapter03 Theorem 3.1.5: the one-step sharp objective contraction packaged with
the explicit spectral and sequence hypotheses needed by the source proof. -/
theorem steepestDescentQuadraticObjectiveContraction_core
    (hG : G.PosDef)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
    {x : ℕ → Point} {α : ℕ → ℝ}
    (hSeq : IsSteepestDescentSequence f x α)
    (k : ℕ) (hNonstationary : x k ≠ 0) :
    (f (x (k + 1)) - f 0) / (f (x k) - f 0) ≤
      (((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) ^ 2) := by
  have hk_pos : 0 < f (x k) :=
    centeredQuadraticObjective_pos_of_ne_zero (G := G) hG hNonstationary
  have hStep :=
    steepestDescentQuadratic_objective_step_mul_bound
      (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
      hG hLambdaMax hLambdaMin hSeq k hNonstationary
  have hRatio :
      f (x (k + 1)) / f (x k) ≤
        (((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) ^ (2 : ℕ)) := by
    -- Divide the one-step objective estimate by the positive current objective value.
    exact (div_le_iff₀ hk_pos).2 hStep
  have hZero : f 0 = 0 := by
    simp [f, quadraticObjective_apply]
  -- The centered minimizer satisfies `f 0 = 0`, so the error ratio is just the objective ratio.
  simpa [hZero, pow_two] using hRatio

/-- Objective-ratio clause for Chapter03 Theorem 3.1.5 (2): on a nonstationary steepest
descent iterate, the ratio of
successive quadratic objective errors is bounded by
`((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin))^2`. -/
theorem steepestDescentQuadraticObjectiveContraction
    (hG : G.PosDef)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
    (hSeq : IsSteepestDescentSequence f x α)
    (k : ℕ) (hNonstationary : x k ≠ 0) :
    (f (x (k + 1)) - f 0) / (f (x k) - f 0) ≤
      (((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) ^ 2) := by
  -- This public clause is exactly the explicit-binder core specialized to the section data.
  simpa using
    steepestDescentQuadraticObjectiveContraction_core
      (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
      (x := x) (α := α) hG hLambdaMax hLambdaMin hSeq k hNonstationary

-- The next theorem is the explicit-binder core behind the public theorem (3).
/-- Helper for Chapter03 Theorem 3.1.5: the source step `(3.1.16)`-(3.1.18)` packaged with the
explicit spectral and sequence hypotheses needed to extract the `G`-energy contraction. -/
theorem steepestDescentQuadraticEnergyNormContraction_core
    (hG : G.PosDef)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
    {x : ℕ → Point} {α : ℕ → ℝ}
    (hSeq : IsSteepestDescentSequence f x α)
    (k : ℕ) (hNonstationary : x k ≠ 0) :
    ellipsoidNorm G (x (k + 1)) / ellipsoidNorm G (x k) ≤
      ((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) := by
  let q : ℝ := (lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)
  let hNorm : IsVectorNorm (ellipsoidNorm G) := ellipsoidNorm_isVectorNorm G hG
  have ⟨hLambdaMinPos, hLambdaMaxPos, hLambdaOrder⟩ :=
    posDef_eigenvalue_endpoints_pos_le
      (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
      hG hLambdaMax hLambdaMin
  have hq_nonneg : 0 ≤ q := by
    have hSum_pos : 0 < lambdaMax + lambdaMin := by
      nlinarith
    exact div_nonneg (sub_nonneg.mpr hLambdaOrder) hSum_pos.le
  have hk_norm_ne : ellipsoidNorm G (x k) ≠ 0 := by
    intro hk_zero
    apply hNonstationary
    exact (hNorm.eq_zero_iff (x k)).1 hk_zero
  have hk_norm_pos : 0 < ellipsoidNorm G (x k) := by
    exact lt_of_le_of_ne (hNorm.nonneg _) (Ne.symm hk_norm_ne)
  have hStep :=
    steepestDescentQuadratic_objective_step_mul_bound
      (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
      hG hLambdaMax hLambdaMin hSeq k hNonstationary
  have hEnergySq :
      (ellipsoidNorm G (x (k + 1))) ^ (2 : ℕ) ≤
        q ^ (2 : ℕ) * (ellipsoidNorm G (x k)) ^ (2 : ℕ) := by
    -- Rewrite the centered objective as one half of the squared `G`-energy on both iterates.
    rw [centeredQuadraticObjective_eq_half_ellipsoidNorm_sq (G := G) hG (x (k + 1)),
      centeredQuadraticObjective_eq_half_ellipsoidNorm_sq (G := G) hG (x k)] at hStep
    nlinarith
  have hEnergyLe :
      ellipsoidNorm G (x (k + 1)) ≤ q * ellipsoidNorm G (x k) := by
    -- Extract the square-root contraction from the squared-energy inequality.
    refine (sq_le_sq₀ (hNorm.nonneg _) (mul_nonneg hq_nonneg (hNorm.nonneg _))).1 ?_
    simpa [q, pow_two, mul_assoc, mul_left_comm, mul_comm] using hEnergySq
  -- Divide by the positive denominator `‖x k‖_G`.
  have hRatio : ellipsoidNorm G (x (k + 1)) / ellipsoidNorm G (x k) ≤ q := by
    exact (div_le_iff₀ hk_norm_pos).2 hEnergyLe
  simpa [q] using hRatio

/-- Energy-norm clause for Chapter03 Theorem 3.1.5 (3): on a nonstationary steepest
descent iterate, the ratio of
successive `G`-energy errors is bounded by
`(lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)`. -/
theorem steepestDescentQuadraticEnergyNormContraction
    (hG : G.PosDef)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
    (hSeq : IsSteepestDescentSequence f x α)
    (k : ℕ) (hNonstationary : x k ≠ 0) :
    ellipsoidNorm G (x (k + 1)) / ellipsoidNorm G (x k) ≤
      ((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) := by
  -- This public clause is exactly the explicit-binder core specialized to the section data.
  simpa using
    steepestDescentQuadraticEnergyNormContraction_core
      (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
      (x := x) (α := α) hG hLambdaMax hLambdaMin hSeq k hNonstationary

-- The public theorem (4) still needs a source-faithful wrapper around this explicit-binder core.
/-- Helper for Chapter03 Theorem 3.1.5: combining the `G`-energy contraction with the Chapter 1
spectral comparisons gives the explicit Euclidean contraction factor. -/
theorem steepestDescentQuadraticEuclideanNormContraction_core
    (hG : G.PosDef)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
    {x : ℕ → Point} {α : ℕ → ℝ}
    (hSeq : IsSteepestDescentSequence f x α)
    (k : ℕ) (hNonstationary : x k ≠ 0) :
    ‖x (k + 1)‖₂ / ‖x k‖₂ ≤
      Real.sqrt (lambdaMax / lambdaMin) *
        ((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) := by
  let q : ℝ := (lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)
  let hEnergyNorm : IsVectorNorm (ellipsoidNorm G) := ellipsoidNorm_isVectorNorm G hG
  have ⟨hLambdaMinPos, hLambdaMaxPos, hLambdaOrder⟩ :=
    posDef_eigenvalue_endpoints_pos_le
      (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
      hG hLambdaMax hLambdaMin
  have hq_nonneg : 0 ≤ q := by
    have hSum_pos : 0 < lambdaMax + lambdaMin := by
      nlinarith
    exact div_nonneg (sub_nonneg.mpr hLambdaOrder) hSum_pos.le
  have hsqrtMin_pos : 0 < Real.sqrt lambdaMin := by
    exact Real.sqrt_pos.mpr hLambdaMinPos
  have hk_norm_ne : ‖x k‖₂ ≠ 0 := by
    intro hk_zero
    apply hNonstationary
    simpa using (l2Norm_isVectorNorm.eq_zero_iff (x k).ofLp).1 hk_zero
  have hk_norm_pos : 0 < ‖x k‖₂ := by
    exact lt_of_le_of_ne (l2Norm_isVectorNorm.nonneg _) (Ne.symm hk_norm_ne)
  have hk_energy_ne : ellipsoidNorm G (x k) ≠ 0 := by
    intro hk_zero
    apply hNonstationary
    exact (hEnergyNorm.eq_zero_iff (x k)).1 hk_zero
  have hk_energy_pos : 0 < ellipsoidNorm G (x k) := by
    exact lt_of_le_of_ne (hEnergyNorm.nonneg _) (Ne.symm hk_energy_ne)
  have hLowerNext :
      Real.sqrt lambdaMin * ‖x (k + 1)‖₂ ≤ ellipsoidNorm G (x (k + 1)) := by
    -- The least spectral endpoint gives the lower Euclidean-to-`G` comparison.
    simpa using
      sqrt_lambdaMin_mul_vectorTwoNorm_le_matrixInducedVectorNorm
        G hG lambdaMin hLambdaMin (x (k + 1))
  have hUpperCurrent :
      ellipsoidNorm G (x k) ≤ Real.sqrt lambdaMax * ‖x k‖₂ := by
    -- The greatest spectral endpoint gives the matching upper comparison.
    simpa using
      matrixInducedVectorNorm_le_sqrt_lambdaMax_mul_vectorTwoNorm
        G hG lambdaMax hLambdaMax (x k)
  have hEnergyStepRatio :=
    steepestDescentQuadraticEnergyNormContraction_core
      (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
      hG hLambdaMax hLambdaMin hSeq k hNonstationary
  have hEnergyStep :
      ellipsoidNorm G (x (k + 1)) ≤ q * ellipsoidNorm G (x k) := by
    -- Convert the ratio estimate back into the one-step `G`-energy inequality.
    exact (div_le_iff₀ hk_energy_pos).1 (by simpa [q] using hEnergyStepRatio)
  have hStep :
      ‖x (k + 1)‖₂ ≤
        (q * (Real.sqrt lambdaMax / Real.sqrt lambdaMin)) * ‖x k‖₂ := by
    have hChain :
        Real.sqrt lambdaMin * ‖x (k + 1)‖₂ ≤
          q * (Real.sqrt lambdaMax * ‖x k‖₂) := by
      -- Sandwich the `G`-energy contraction between the two Chapter 1 norm comparisons.
      calc
        Real.sqrt lambdaMin * ‖x (k + 1)‖₂ ≤ ellipsoidNorm G (x (k + 1)) := hLowerNext
        _ ≤ q * ellipsoidNorm G (x k) := hEnergyStep
        _ ≤ q * (Real.sqrt lambdaMax * ‖x k‖₂) := by
              exact mul_le_mul_of_nonneg_left hUpperCurrent hq_nonneg
    have hsqrtMin_ne : Real.sqrt lambdaMin ≠ 0 := hsqrtMin_pos.ne'
    have hRewrite :
        (q * (Real.sqrt lambdaMax / Real.sqrt lambdaMin)) * ‖x k‖₂ =
          (q * (Real.sqrt lambdaMax * ‖x k‖₂)) / Real.sqrt lambdaMin := by
      field_simp [hsqrtMin_ne]
    rw [hRewrite]
    -- Divide by the positive factor `sqrt lambdaMin`.
    exact (le_div_iff₀ hsqrtMin_pos).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hChain)
  have hRatio :
      ‖x (k + 1)‖₂ / ‖x k‖₂ ≤
        q * (Real.sqrt lambdaMax / Real.sqrt lambdaMin) := by
    -- Divide by the positive Euclidean norm of the current nonstationary iterate.
    exact (div_le_iff₀ hk_norm_pos).2 hStep
  have hSqrtDiv :
      Real.sqrt (lambdaMax / lambdaMin) = Real.sqrt lambdaMax / Real.sqrt lambdaMin := by
    rw [Real.sqrt_div hLambdaMaxPos.le lambdaMin]
  simpa [q, hSqrtDiv, mul_assoc, mul_left_comm, mul_comm] using hRatio

/-- Euclidean-norm clause for Chapter03 Theorem 3.1.5 (4): on a nonstationary steepest
descent iterate, the ratio of
successive Euclidean errors is bounded by
`sqrt (lambdaMax / lambdaMin) * ((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin))`. -/
theorem steepestDescentQuadraticEuclideanNormContraction
    (hG : G.PosDef)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
    (hSeq : IsSteepestDescentSequence f x α)
    (k : ℕ) (hNonstationary : x k ≠ 0) :
    ‖x (k + 1)‖₂ / ‖x k‖₂ ≤
      Real.sqrt (lambdaMax / lambdaMin) *
        ((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) := by
  -- This public clause is exactly the explicit-binder core specialized to the section data.
  simpa using
    steepestDescentQuadraticEuclideanNormContraction_core
      (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
      (x := x) (α := α) hG hLambdaMax hLambdaMin hSeq k hNonstationary

/-- Helper for Chapter03 Theorem 3.1.5: the `G`-energy decays geometrically along the
exact-line-search steepest-descent sequence. -/
theorem steepestDescentQuadratic_energy_geometric_bound_core
    (hG : G.PosDef)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin)
    {x : ℕ → Point} {α : ℕ → ℝ}
    (hSeq : IsSteepestDescentSequence f x α)
    : ∀ k : ℕ,
        ellipsoidNorm G (x k) ≤
          (((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) ^ k) *
            ellipsoidNorm G (x 0) := by
  let q : ℝ := (lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)
  have ⟨hLambdaMinPos, hLambdaMaxPos, hLambdaOrder⟩ :=
    posDef_eigenvalue_endpoints_pos_le
      (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
      hG hLambdaMax hLambdaMin
  have hq_nonneg : 0 ≤ q := by
    have hSum_pos : 0 < lambdaMax + lambdaMin := by
      nlinarith
    exact div_nonneg (sub_nonneg.mpr hLambdaOrder) hSum_pos.le
  intro k
  induction k with
  | zero =>
      simp [q]
  | succ k hk =>
      by_cases hZero : x k = 0
      · have hk_succ_zero :=
          steepestDescentQuadratic_zero_tail
            (G := G) hG hSeq k hZero
        -- Once the sequence reaches `0`, every later `G`-energy is also `0`.
        rw [hk_succ_zero]
        positivity
      · let hEnergyNorm : IsVectorNorm (ellipsoidNorm G) := ellipsoidNorm_isVectorNorm G hG
        have hk_norm_ne : ellipsoidNorm G (x k) ≠ 0 := by
          intro hk_zero
          apply hZero
          simpa using (hEnergyNorm.eq_zero_iff (x k)).1 hk_zero
        have hk_norm_pos : 0 < ellipsoidNorm G (x k) := by
          exact lt_of_le_of_ne (hEnergyNorm.nonneg _) (Ne.symm hk_norm_ne)
        have hStep :
            ellipsoidNorm G (x (k + 1)) ≤ q * ellipsoidNorm G (x k) := by
          have hRatio :=
            steepestDescentQuadraticEnergyNormContraction_core
              (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
              hG hLambdaMax hLambdaMin hSeq k hZero
          exact (div_le_iff₀ hk_norm_pos).1 (by simpa [q] using hRatio)
        -- Combine the one-step contraction with the induction hypothesis.
        calc
          ellipsoidNorm G (x (k + 1)) ≤ q * ellipsoidNorm G (x k) := hStep
          _ ≤ q * (q ^ k * ellipsoidNorm G (x 0)) := by
                exact mul_le_mul_of_nonneg_left hk hq_nonneg
          _ = q ^ (k + 1) * ellipsoidNorm G (x 0) := by
                rw [pow_succ']
                ring
          _ = (((lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)) ^ (k + 1)) *
                ellipsoidNorm G (x 0) := by
                  simp [q]

end SpectralContraction

/-- Helper for Chapter03 Theorem 3.1.5: when `Fin n` is nonempty, the positive-definite spectral
range attains both its least and greatest values. -/
theorem posDefEigenvalueEndpointsExist
    (hG : G.PosDef) (hNonempty : Nonempty (Fin n)) :
    ∃ lambdaMax lambdaMin,
      IsGreatest (Set.range (posDefEigenvalues G hG)) lambdaMax ∧
      IsLeast (Set.range (posDefEigenvalues G hG)) lambdaMin := by
  classical
  let s : Set ℝ := Set.range (posDefEigenvalues G hG)
  have hFinite : s.Finite := by
    simpa [s] using (Set.finite_range (posDefEigenvalues G hG))
  have hCompact : IsCompact s := hFinite.isCompact
  have hRangeNonempty : s.Nonempty := by
    let i0 : Fin n := Classical.choice hNonempty
    exact ⟨posDefEigenvalues G hG i0, ⟨i0, rfl⟩⟩
  -- Compactness upgrades the finite spectral range to actual least and greatest endpoints.
  obtain ⟨lambdaMax, hLambdaMax⟩ := hCompact.exists_isGreatest hRangeNonempty
  obtain ⟨lambdaMin, hLambdaMin⟩ := hCompact.exists_isLeast hRangeNonempty
  exact ⟨lambdaMax, lambdaMin, hLambdaMax, hLambdaMin⟩

/-- Chapter03 Theorem 3.1.5 (1): for a symmetric positive definite quadratic objective,
the exact-line-search steepest-descent iterates converge to the minimizer `0`. -/
theorem steepestDescentQuadraticConverges
    (hG : G.PosDef)
    (x : ℕ → Point)
    (α : ℕ → ℝ)
    (hSeq : IsSteepestDescentSequence f x α) :
    Tendsto x atTop (nhds 0) := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hEmpty | hNonempty
  · have hxZero : x = fun _ ↦ (0 : Point) := by
      funext k
      ext i
      exact (hEmpty.false i).elim
    -- In the zero-dimensional case, every iterate is forced to be the minimizer `0`.
    simpa [hxZero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : Point)) atTop (nhds 0))
  · obtain ⟨lambdaMax, lambdaMin, hLambdaMax, hLambdaMin⟩ :=
      posDefEigenvalueEndpointsExist (G := G) hG hNonempty
    let q : ℝ := (lambdaMax - lambdaMin) / (lambdaMax + lambdaMin)
    have ⟨hLambdaMinPos, hLambdaMaxPos, hLambdaOrder⟩ :=
      posDef_eigenvalue_endpoints_pos_le
        (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
        hG hLambdaMax hLambdaMin
    have hq_nonneg : 0 ≤ q := by
      have hSum_pos : 0 < lambdaMax + lambdaMin := by
        nlinarith
      exact div_nonneg (sub_nonneg.mpr hLambdaOrder) hSum_pos.le
    have hq_lt_one : q < 1 := by
      have hSum_pos : 0 < lambdaMax + lambdaMin := by
        nlinarith
      exact (div_lt_iff₀ hSum_pos).2 (by nlinarith)
    have hsqrtMin_pos : 0 < Real.sqrt lambdaMin := by
      exact Real.sqrt_pos.mpr hLambdaMinPos
    have hEnergyGeom :=
      steepestDescentQuadratic_energy_geometric_bound_core
        (G := G) (lambdaMax := lambdaMax) (lambdaMin := lambdaMin)
        (x := x) (α := α) hG hLambdaMax hLambdaMin hSeq
    have hNormBound :
        ∀ k : ℕ,
          ‖x k‖₂ ≤ q ^ k * ((Real.sqrt lambdaMin)⁻¹ * ellipsoidNorm G (x 0)) := by
      intro k
      have hLower :
          Real.sqrt lambdaMin * ‖x k‖₂ ≤ ellipsoidNorm G (x k) := by
        -- The least spectral endpoint converts `G`-energy into a Euclidean lower bound.
        simpa using
          sqrt_lambdaMin_mul_vectorTwoNorm_le_matrixInducedVectorNorm
            G hG lambdaMin hLambdaMin (x k)
      have hScaled :
          ‖x k‖₂ ≤ ellipsoidNorm G (x k) / Real.sqrt lambdaMin := by
        -- Divide the lower bound by the positive factor `sqrt lambdaMin`.
        exact (le_div_iff₀ hsqrtMin_pos).2 (by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hLower)
      calc
        ‖x k‖₂ ≤ ellipsoidNorm G (x k) / Real.sqrt lambdaMin := hScaled
        _ ≤ (q ^ k * ellipsoidNorm G (x 0)) / Real.sqrt lambdaMin := by
              exact div_le_div_of_nonneg_right (hEnergyGeom k) hsqrtMin_pos.le
        _ = q ^ k * ((Real.sqrt lambdaMin)⁻¹ * ellipsoidNorm G (x 0)) := by
              rw [div_eq_mul_inv]
              ring
    have hMajorantTendsto :
        Tendsto
          (fun k : ℕ ↦ q ^ k * ((Real.sqrt lambdaMin)⁻¹ * ellipsoidNorm G (x 0)))
          atTop (nhds 0) := by
      -- The geometric majorant tends to zero because `0 ≤ q < 1`.
      simpa [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one).mul_const
          ((Real.sqrt lambdaMin)⁻¹ * ellipsoidNorm G (x 0))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    -- Squeeze the ambient norm by the geometric majorant obtained from the `G`-energy decay.
    refine squeeze_zero_norm ?_ hMajorantTendsto
    intro k
    simpa [EuclideanSpace.norm_eq, l2Norm_eq_sqrt_sum_sq] using hNormBound k
end CenteredQuadraticObjective

end
