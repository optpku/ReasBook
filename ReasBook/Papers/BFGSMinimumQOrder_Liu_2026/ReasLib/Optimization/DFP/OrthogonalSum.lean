module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.Block
public import ReasLib.Optimization.DFP.Orbit
public import ReasLib.Optimization.LineSearch
public import ReasLib.Optimization.DFP.OrthogonalSum.Lift

public section

universe u v

open scoped Matrix

namespace DFP.OrthogonalSum

/-- The continuous linear embedding into the left summand of an orthogonal coordinate sum. -/
noncomputable def embed {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι ⊕ κ) :=
  EuclideanSpace.OrthogonalSum.inl

/-- The left coordinates of an embedded vector agree with the original vector. -/
theorem embed_apply_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) (i : ι) :
    WithLp.ofLp (embed z) (Sum.inl i : ι ⊕ κ) = WithLp.ofLp z i := by
  exact EuclideanSpace.OrthogonalSum.inl_apply_inl (κ := κ) z i

/-- The right coordinates of an embedded vector vanish. -/
theorem embed_apply_inr {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) (j : κ) :
    WithLp.ofLp (embed z) (Sum.inr j : ι ⊕ κ) = 0 := by
  exact EuclideanSpace.OrthogonalSum.inl_apply_inr (ι := ι) z j

/-- The left orthogonal-sum embedding preserves the real inner product. -/
theorem inner_embed {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z z' : EuclideanSpace ℝ ι) :
    inner ℝ (embed z : EuclideanSpace ℝ (ι ⊕ κ)) (embed z') = inner ℝ z z' := by
  exact EuclideanSpace.OrthogonalSum.inner_inl (κ := κ) z z'

/-- The left orthogonal-sum embedding preserves norms. -/
@[simp]
theorem norm_embed {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) :
    ‖(embed z : EuclideanSpace ℝ (ι ⊕ κ))‖ = ‖z‖ := by
  exact EuclideanSpace.OrthogonalSum.norm_inl (κ := κ) z

/-- Scaled DFP steps commute with the left orthogonal-sum embedding. -/
theorem steps_embed {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (α : ℕ → ℝ) (d : ℕ → EuclideanSpace ℝ ι) (k : ℕ) :
    DFP.steps α (fun n ↦ embed (d n) : ℕ → EuclideanSpace ℝ (ι ⊕ κ)) k =
      embed (DFP.steps α d k) := by
  exact DFP.OrthogonalSum.Transport.steps_inl (κ := κ) α d k

/-- Successive gradient differences commute with the left orthogonal-sum embedding. -/
theorem gradientChanges_embed {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (g : ℕ → EuclideanSpace ℝ ι) (k : ℕ) :
    DFP.gradientChanges (fun n ↦ embed (g n) : ℕ → EuclideanSpace ℝ (ι ⊕ κ)) k =
      embed (DFP.gradientChanges g k) := by
  exact DFP.OrthogonalSum.Transport.gradientChanges_inl (κ := κ) g k

/-- Extend a real objective by the quadratic `‖w‖ ^ 2 / 2` on an orthogonal summand. -/
noncomputable def objective {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (f : EuclideanSpace ℝ ι → ℝ) (p : EuclideanSpace ℝ (ι ⊕ κ)) : ℝ :=
  EuclideanSpace.OrthogonalSum.Gradient.objective f p

/-- The DFP-facing orthogonal-sum objective is the generic gradient-level
orthogonal-sum objective. -/
theorem objective_eq {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (f : EuclideanSpace ℝ ι → ℝ) :
    objective (κ := κ) f = EuclideanSpace.OrthogonalSum.Gradient.objective f := by
  rfl

/-- The orthogonal-sum objective restricts to the original objective on the left summand. -/
theorem objective_embed {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (f : EuclideanSpace ℝ ι → ℝ) (z : EuclideanSpace ℝ ι) :
    objective f (embed z : EuclideanSpace ℝ (ι ⊕ κ)) = f z := by
  exact EuclideanSpace.OrthogonalSum.Gradient.objective_inl (κ := κ) f z

/-- A certified gradient embeds as a certified gradient of the orthogonal-sum objective. -/
theorem hasGradientAt_objective_embed {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {f : EuclideanSpace ℝ ι → ℝ}
    {z g : EuclideanSpace ℝ ι} (hf : HasGradientAt f g z) :
    HasGradientAt (objective f) (embed g : EuclideanSpace ℝ (ι ⊕ κ))
      (embed z : EuclideanSpace ℝ (ι ⊕ κ)) := by
  exact EuclideanSpace.OrthogonalSum.Gradient.hasGradientAt_objective_inl (κ := κ) hf

/-- The gradient of the orthogonal-sum objective at an embedded point is the embedded
gradient of the original objective. -/
theorem gradient_objective_embed {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {f : EuclideanSpace ℝ ι → ℝ}
    {z : EuclideanSpace ℝ ι} (hf : DifferentiableAt ℝ f z) :
    gradient (objective f : EuclideanSpace ℝ (ι ⊕ κ) → ℝ) (embed z) =
      embed (gradient f z) := by
  exact EuclideanSpace.OrthogonalSum.Gradient.gradient_objective_inl (κ := κ) hf

/-- Extend a square matrix by the identity matrix on an orthogonal summand. -/
def matrix {ι : Type u} {κ : Type v} [DecidableEq κ]
    (H : Matrix ι ι ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  EuclideanSpace.OrthogonalSum.extendMatrix H

/-- The identity-block extension acts on an embedded vector by the embedded original
matrix action. -/
theorem matrix_mulVec_embed {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (H : Matrix ι ι ℝ) (z : EuclideanSpace ℝ ι) :
    matrix H *ᵥ WithLp.ofLp (embed z : EuclideanSpace ℝ (ι ⊕ κ)) =
      WithLp.ofLp (embed (WithLp.toLp 2 (H *ᵥ WithLp.ofLp z)) :
        EuclideanSpace ℝ (ι ⊕ κ)) := by
  exact EuclideanSpace.OrthogonalSum.extendMatrix_mulVec_inl (κ := κ) H z

/-- Search directions for identity-block matrices are embedded original search directions. -/
theorem directions_embed {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (H : ℕ → Matrix ι ι ℝ) (g : ℕ → EuclideanSpace ℝ ι) (k : ℕ) :
    DFP.directions
        (fun n ↦ matrix (H n) : ℕ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
        (fun n ↦ embed (g n) : ℕ → EuclideanSpace ℝ (ι ⊕ κ)) k =
      embed (DFP.directions H g k) := by
  exact DFP.OrthogonalSum.Transport.directions_inl (κ := κ) H g k

/-- The secant pairing is unchanged by the left orthogonal-sum embedding and
identity-block extension. -/
theorem secantPairing_embed {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (α : ℕ → ℝ) (H : ℕ → Matrix ι ι ℝ)
    (g : ℕ → EuclideanSpace ℝ ι) (k : ℕ) :
    WithLp.ofLp
          (DFP.steps α
            (DFP.directions
              (fun n ↦ matrix (κ := κ) (H n))
              (fun n ↦ embed (κ := κ) (g n))) k) ⬝ᵥ
        WithLp.ofLp
          (DFP.gradientChanges (fun n ↦ embed (κ := κ) (g n)) k) =
      WithLp.ofLp (DFP.steps α (DFP.directions H g) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges g k) := by
  have hDirection :
      DFP.directions
          (fun n ↦ matrix (κ := κ) (H n) : ℕ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
          (fun n ↦ embed (κ := κ) (g n) : ℕ → EuclideanSpace ℝ (ι ⊕ κ)) k =
        embed (κ := κ) (DFP.directions H g k) :=
    directions_embed (κ := κ) H g k
  have hStep :
      DFP.steps α
          (DFP.directions
            (fun n ↦ matrix (κ := κ) (H n))
            (fun n ↦ embed (κ := κ) (g n))) k =
        embed (κ := κ) (DFP.steps α (DFP.directions H g) k) := by
    rw [DFP.steps_apply, hDirection, DFP.steps_apply]
    exact ((embed (ι := ι) (κ := κ)).map_smul (α k) (DFP.directions H g k)).symm
  have hChange :
      DFP.gradientChanges (fun n ↦ embed (κ := κ) (g n)) k =
        embed (κ := κ) (DFP.gradientChanges g k) :=
    gradientChanges_embed (κ := κ) g k
  rw [hStep, hChange]
  exact DFP.OrthogonalSum.Transport.dotProduct_inl _ _

/-- Identity-block extension preserves and reflects positive definiteness. -/
theorem matrix_posDef_iff {ι : Type u} {κ : Type v} [DecidableEq κ]
    (H : Matrix ι ι ℝ) :
    (matrix H : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ).PosDef ↔ H.PosDef := by
  exact EuclideanSpace.OrthogonalSum.extendMatrix_posDef_iff (κ := κ) H

/-- An inverse-form DFP update by embedded secant vectors preserves the identity block. -/
theorem inverseDFPUpdate_matrix {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (H : Matrix ι ι ℝ) (s y : EuclideanSpace ℝ ι) :
    Matrix.inverseDFPUpdate (matrix H : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
        (WithLp.ofLp (embed s)) (WithLp.ofLp (embed y)) =
      matrix (Matrix.inverseDFPUpdate H (WithLp.ofLp s) (WithLp.ofLp y)) := by
  exact DFP.OrthogonalSum.Transport.inverseDFPUpdate_extendMatrix_inl (κ := κ) H s y

end DFP.OrthogonalSum

namespace DFP.IsOrbit

/-- The quadratic objective and identity-block matrices transport a certified DFP orbit
through the left orthogonal-sum embedding. -/
theorem orthogonalSum {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {f : EuclideanSpace ℝ ι → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ ι} {H : ℕ → Matrix ι ι ℝ}
    (h : DFP.IsOrbit f α x g H) :
    DFP.IsOrbit (DFP.OrthogonalSum.objective f) α
      (fun k ↦ DFP.OrthogonalSum.embed (x k) :
        ℕ → EuclideanSpace ℝ (ι ⊕ κ))
      (fun k ↦ DFP.OrthogonalSum.embed (g k) :
        ℕ → EuclideanSpace ℝ (ι ⊕ κ))
      (fun k ↦ DFP.OrthogonalSum.matrix (H k) :
        ℕ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) := by
  exact DFP.OrthogonalSum.Lift.isOrbit (κ := κ) h

end DFP.IsOrbit

namespace DFP.InverseIteration

/-- Adjoining an identity quadratic block transports an inverse-form DFP iteration
through the canonical left orthogonal-sum embedding. -/
noncomputable def orthogonalSum {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k) :
    DFP.InverseIteration (ι ⊕ κ) := by
  let hOrbit := (it.isOrbit hStep).orthogonalSum (κ := κ)
  apply hOrbit.toInverseIteration
  · intro k
    exact (DFP.OrthogonalSum.matrix_posDef_iff
      (κ := κ) (it.inverseHessian k)).mpr (it.inverseHessianPosDef k)
  · intro k
    rw [DFP.OrthogonalSum.secantPairing_embed]
    exact it.secantDenominatorNe k

/-- The objective of the orthogonal-sum iteration is the original objective plus the
identity quadratic block. -/
@[simp]
theorem orthogonalSum_objective {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k) :
    (it.orthogonalSum (κ := κ) hStep).objective =
      DFP.OrthogonalSum.objective it.objective := by
  rw [orthogonalSum, DFP.IsOrbit.toInverseIteration_objective]

/-- Orthogonal-sum transport leaves the step-length sequence unchanged. -/
@[simp]
theorem orthogonalSum_stepLength {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k) :
    (it.orthogonalSum (κ := κ) hStep).stepLength = it.stepLength := by
  rw [orthogonalSum, DFP.IsOrbit.toInverseIteration_stepLength]

/-- The points of the orthogonal-sum iteration are the embedded original points. -/
@[simp]
theorem orthogonalSum_point {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k) (k : ℕ) :
    (it.orthogonalSum (κ := κ) hStep).point k =
      DFP.OrthogonalSum.embed (it.point k) := by
  rw [orthogonalSum, DFP.IsOrbit.toInverseIteration_point]

/-- The inverse Hessians of the orthogonal-sum iteration are the identity-block
extensions of the original inverse Hessians. -/
@[simp]
theorem orthogonalSum_inverseHessian {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k) (k : ℕ) :
    (it.orthogonalSum (κ := κ) hStep).inverseHessian k =
      DFP.OrthogonalSum.matrix (it.inverseHessian k) := by
  rw [orthogonalSum, DFP.IsOrbit.toInverseIteration_inverseHessian]

/-- The canonical gradient sequence of the orthogonal-sum iteration is the embedded
canonical gradient sequence of the original iteration. -/
@[simp]
theorem orthogonalSum_gradients {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k) :
    DFP.gradients (it.orthogonalSum (κ := κ) hStep).objective
        (it.orthogonalSum (κ := κ) hStep).point =
      fun k ↦ DFP.OrthogonalSum.embed
        (DFP.gradients it.objective it.point k) := by
  funext k
  rw [DFP.gradients_apply, DFP.gradients_apply,
    orthogonalSum_objective, orthogonalSum_point]
  exact DFP.OrthogonalSum.gradient_objective_embed (κ := κ) (it.differentiableAt k)

end DFP.InverseIteration

namespace LineSearch.IsWeakWolfe

/-- Weak Wolfe satisfaction for an embedded step is equivalent to weak Wolfe satisfaction
in the original coordinate summand. -/
theorem orthogonalSum_iff {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] {c₁ c₂ : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    {x s : EuclideanSpace ℝ ι} :
    LineSearch.IsWeakWolfe c₁ c₂ (DFP.OrthogonalSum.objective f)
        (DFP.OrthogonalSum.embed x : EuclideanSpace ℝ (ι ⊕ κ))
        (DFP.OrthogonalSum.embed s : EuclideanSpace ℝ (ι ⊕ κ)) ↔
      LineSearch.IsWeakWolfe c₁ c₂ f x s := by
  exact DFP.OrthogonalSum.Lift.weakWolfe_iff (κ := κ)

end LineSearch.IsWeakWolfe
