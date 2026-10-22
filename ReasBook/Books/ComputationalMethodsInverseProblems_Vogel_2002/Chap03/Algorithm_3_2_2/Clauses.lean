/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.PosDef

public section

namespace PreconditionedConjugateGradient

universe u

/-- The displayed initialization clause `f 0 = f0` for the PCG iterate
sequence. -/
abbrev IsInitialized {n : Type u} (f0 : EuclideanSpace ℝ n) (f : ℕ → EuclideanSpace ℝ n) :
    Prop :=
  f 0 = f0

/-- Extracts the initialization equality from
`PreconditionedConjugateGradient.IsInitialized`. -/
theorem IsInitialized.init_eq {n : Type u} {f0 : EuclideanSpace ℝ n}
    {f : ℕ → EuclideanSpace ℝ n}
    (h : IsInitialized f0 f) :
    f 0 = f0 := by
  -- Unfold the clause abbreviation and read off the stored equality.
  simpa [IsInitialized] using h

/-- The displayed initial gradient clause `g 0 = A.toEuclideanLin (f 0) + b`. -/
abbrev HasInitialGradient {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n)
    (f g : ℕ → EuclideanSpace ℝ n) : Prop :=
  g 0 = A.toEuclideanLin (f 0) + b

/-- Extracts the initial gradient equality from
`PreconditionedConjugateGradient.HasInitialGradient`. -/
theorem HasInitialGradient.eq {n : Type u} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} {b : EuclideanSpace ℝ n}
    {f g : ℕ → EuclideanSpace ℝ n}
    (h : HasInitialGradient A b f g) :
    g 0 = A.toEuclideanLin (f 0) + b := by
  -- Unfold the clause abbreviation and recover the displayed initialization formula.
  simpa [HasInitialGradient] using h

/-- The displayed initial preconditioner-application clause
`z 0 = (M⁻¹).toEuclideanLin (g 0)`. -/
abbrev HasInitialPreconditionedGradient {n : Type u} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ)
    (g z : ℕ → EuclideanSpace ℝ n) : Prop :=
  z 0 = (M⁻¹).toEuclideanLin (g 0)

/-- Extracts the initial preconditioner-application equality from
`PreconditionedConjugateGradient.HasInitialPreconditionedGradient`. -/
theorem HasInitialPreconditionedGradient.eq {n : Type u} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} {g z : ℕ → EuclideanSpace ℝ n}
    (h : HasInitialPreconditionedGradient M g z) :
    z 0 = (M⁻¹).toEuclideanLin (g 0) := by
  -- Unfold the clause abbreviation and recover the displayed inverse-action formula.
  simpa [HasInitialPreconditionedGradient] using h

/-- The displayed initial direction clause `p 0 = -z 0`. -/
abbrev HasInitialDirection {n : Type u} (z p : ℕ → EuclideanSpace ℝ n) : Prop :=
  p 0 = -z 0

/-- Extracts the initial direction equality from
`PreconditionedConjugateGradient.HasInitialDirection`. -/
theorem HasInitialDirection.eq {n : Type u}
    {z p : ℕ → EuclideanSpace ℝ n}
    (h : HasInitialDirection z p) :
    p 0 = -z 0 := by
  -- Unfold the clause abbreviation and read off the initial direction update.
  simpa [HasInitialDirection] using h

/-- The displayed initial scalar clause `δ 0 = inner ℝ (g 0) (z 0)`. -/
abbrev HasInitialDelta {n : Type u} [Fintype n]
    (g z : ℕ → EuclideanSpace ℝ n) (δ : ℕ → ℝ) : Prop :=
  δ 0 = inner ℝ (g 0) (z 0)

/-- Extracts the initial `δ` equality from
`PreconditionedConjugateGradient.HasInitialDelta`. -/
theorem HasInitialDelta.eq {n : Type u} [Fintype n]
    {g z : ℕ → EuclideanSpace ℝ n} {δ : ℕ → ℝ}
    (h : HasInitialDelta g z δ) :
    δ 0 = inner ℝ (g 0) (z 0) := by
  -- Unfold the clause abbreviation and recover the displayed scalar identity.
  simpa [HasInitialDelta] using h

/-- The displayed matrix-action clause `h v = A.toEuclideanLin (p v)`. -/
abbrev HasAppliedDirection {n : Type u} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (p h : ℕ → EuclideanSpace ℝ n) : Prop :=
  ∀ v : ℕ, h v = A.toEuclideanLin (p v)

/-- Extracts the matrix-action equality from
`PreconditionedConjugateGradient.HasAppliedDirection`. -/
theorem HasAppliedDirection.eq {n : Type u} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} {p h : ℕ → EuclideanSpace ℝ n}
    (hh : HasAppliedDirection A p h) (v : ℕ) :
    h v = A.toEuclideanLin (p v) := by
  -- Specialize the pointwise clause at `v`.
  simpa [HasAppliedDirection] using hh v

/-- The displayed step-size clause
`τ v = δ v / inner ℝ (p v) (h v)`. -/
abbrev HasStepSize {n : Type u} [Fintype n] (p h : ℕ → EuclideanSpace ℝ n)
    (δ τ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, τ v = δ v / inner ℝ (p v) (h v)

/-- Extracts the step-size equality from
`PreconditionedConjugateGradient.HasStepSize`. -/
theorem HasStepSize.eq {n : Type u} [Fintype n]
    {p h : ℕ → EuclideanSpace ℝ n} {δ τ : ℕ → ℝ}
    (hτ : HasStepSize p h δ τ) (v : ℕ) :
    τ v = δ v / inner ℝ (p v) (h v) := by
  -- Specialize the pointwise clause at `v`.
  simpa [HasStepSize] using hτ v

/-- The displayed solution update `f (v + 1) = f v + τ v • p v`. -/
abbrev HasSolutionUpdate {n : Type u} (f p : ℕ → EuclideanSpace ℝ n)
    (τ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, f (v + 1) = f v + τ v • p v

/-- Extracts the solution update equality from
`PreconditionedConjugateGradient.HasSolutionUpdate`. -/
theorem HasSolutionUpdate.eq {n : Type u}
    {f p : ℕ → EuclideanSpace ℝ n} {τ : ℕ → ℝ}
    (hf : HasSolutionUpdate f p τ) (v : ℕ) :
    f (v + 1) = f v + τ v • p v := by
  -- Specialize the pointwise clause at `v`.
  simpa [HasSolutionUpdate] using hf v

/-- The displayed gradient update `g (v + 1) = g v + τ v • h v`. -/
abbrev HasGradientUpdate {n : Type u} (g h : ℕ → EuclideanSpace ℝ n)
    (τ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, g (v + 1) = g v + τ v • h v

/-- Extracts the gradient update equality from
`PreconditionedConjugateGradient.HasGradientUpdate`. -/
theorem HasGradientUpdate.eq {n : Type u}
    {g h : ℕ → EuclideanSpace ℝ n} {τ : ℕ → ℝ}
    (hg : HasGradientUpdate g h τ) (v : ℕ) :
    g (v + 1) = g v + τ v • h v := by
  -- Specialize the pointwise clause at `v`.
  simpa [HasGradientUpdate] using hg v

/-- The displayed preconditioner-application update
`z (v + 1) = (M⁻¹).toEuclideanLin (g (v + 1))`. -/
abbrev HasPreconditionerUpdate {n : Type u} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ)
    (g z : ℕ → EuclideanSpace ℝ n) : Prop :=
  ∀ v : ℕ, z (v + 1) = (M⁻¹).toEuclideanLin (g (v + 1))

/-- Extracts the preconditioner-application equality from
`PreconditionedConjugateGradient.HasPreconditionerUpdate`. -/
theorem HasPreconditionerUpdate.eq {n : Type u} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} {g z : ℕ → EuclideanSpace ℝ n}
    (hz : HasPreconditionerUpdate M g z) (v : ℕ) :
    z (v + 1) = (M⁻¹).toEuclideanLin (g (v + 1)) := by
  -- Specialize the pointwise clause at `v`.
  simpa [HasPreconditionerUpdate] using hz v

/-- Under positive definiteness of `M`, the displayed inverse-action update
implies the solve-form equality `M.toEuclideanLin (z (v + 1)) = g (v + 1)`. -/
theorem HasPreconditionerUpdate.solve_eq {n : Type u} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} {g z : ℕ → EuclideanSpace ℝ n}
    (hz : HasPreconditionerUpdate M g z) (hM : M.PosDef) (v : ℕ) :
    M.toEuclideanLin (z (v + 1)) = g (v + 1) := by
  have hM_det : IsUnit M.det := by
    exact M.isUnit_iff_isUnit_det.mp hM.isUnit
  -- Rewrite the update using the stored inverse-action clause.
  rw [HasPreconditionerUpdate.eq hz v]
  -- Compose the matrix actions, cancel `M * M⁻¹`, and simplify the identity action.
  calc
    M.toEuclideanLin ((M⁻¹).toEuclideanLin (g (v + 1)))
        = (M * M⁻¹).toEuclideanLin (g (v + 1)) := by
            simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    _ = (1 : Matrix n n ℝ).toEuclideanLin (g (v + 1)) := by
      rw [Matrix.mul_nonsing_inv M hM_det]
    _ = g (v + 1) := by
      simp

/-- The displayed scalar recurrence `δ (v + 1) = inner ℝ (g (v + 1)) (z (v + 1))`. -/
abbrev HasDeltaUpdate {n : Type u} [Fintype n] (g z : ℕ → EuclideanSpace ℝ n)
    (δ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, δ (v + 1) = inner ℝ (g (v + 1)) (z (v + 1))

/-- Extracts the `δ` recurrence from
`PreconditionedConjugateGradient.HasDeltaUpdate`. -/
theorem HasDeltaUpdate.eq {n : Type u} [Fintype n]
    {g z : ℕ → EuclideanSpace ℝ n} {δ : ℕ → ℝ}
    (hδ : HasDeltaUpdate g z δ) (v : ℕ) :
    δ (v + 1) = inner ℝ (g (v + 1)) (z (v + 1)) := by
  -- Specialize the pointwise clause at `v`.
  simpa [HasDeltaUpdate] using hδ v

/-- The displayed direction recurrence
`p (v + 1) = -z (v + 1) + β v • p v`. -/
abbrev HasDirectionUpdate {n : Type u} (z p : ℕ → EuclideanSpace ℝ n)
    (β : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, p (v + 1) = -z (v + 1) + β v • p v

/-- Extracts the direction recurrence from
`PreconditionedConjugateGradient.HasDirectionUpdate`. -/
theorem HasDirectionUpdate.eq {n : Type u}
    {z p : ℕ → EuclideanSpace ℝ n} {β : ℕ → ℝ}
    (hp : HasDirectionUpdate z p β) (v : ℕ) :
    p (v + 1) = -z (v + 1) + β v • p v := by
  -- Specialize the pointwise clause at `v`.
  simpa [HasDirectionUpdate] using hp v

end PreconditionedConjugateGradient
