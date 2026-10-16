module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Coefficient
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.GramMatrix
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycle
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM.Period48.Realization

noncomputable section

/-- The realized first-block family `ηᵢ = S eᵢ`: the image of the first-block standard
basis coefficient vector under the Gram factor `S`. -/
def eta (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    EuclideanSpace ℝ (Fin 2 × Fin 48) :=
  WithLp.toLp 2 (S.mulVec (Coefficient.eta i))

/-- The realized first-block family is the image of the first-block standard basis
coefficient vector. -/
theorem eta_apply (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    eta S i = WithLp.toLp 2 (S.mulVec (Coefficient.eta i)) :=
  -- Definitional: the right-hand side is the defining body of `eta`.
  rfl

/-- The realized multiplier direction `wᵢ = γ₀⁻¹ S e₄₈₊ᵢ`: the image of the second-block
standard basis coefficient vector under `S`, scaled by the inverse of the multiplier
`γ₀` of the period-48 configuration. -/
def w (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    EuclideanSpace ℝ (Fin 2 × Fin 48) :=
  gammaZero⁻¹ • WithLp.toLp 2 (S.mulVec (Coefficient.nu i))

/-- The realized multiplier direction is the image of the scaled second-block coefficient
vector `γ₀⁻¹ e₄₈₊ᵢ`. -/
theorem w_apply (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    w S i = gammaZero⁻¹ • WithLp.toLp 2 (S.mulVec (Coefficient.nu i)) :=
  -- Definitional: the right-hand side is the defining body of `w`.
  rfl

/-- The realized residual `ρᵢ = wᵢ - wᵢ₋₁`. -/
def rho (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    EuclideanSpace ℝ (Fin 2 × Fin 48) :=
  w S i - w S (i - 1)

/-- The realized residual is the difference of consecutive realized multiplier
directions. -/
theorem rho_apply (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    rho S i = w S i - w S (i - 1) :=
  -- Definitional: the right-hand side is the defining body of `rho`.
  rfl

/-- The realized first-block vertex `ξᵢ = ηᵢ + ρᵢ`. -/
def xi (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    EuclideanSpace ℝ (Fin 2 × Fin 48) :=
  eta S i + rho S i

/-- The realized first-block vertex is the sum of the realized first-block family and the
realized residual. -/
theorem xi_apply (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    xi S i = eta S i + rho S i :=
  -- Definitional: the right-hand side is the defining body of `xi`.
  rfl

/-- The realized multiplier vertex `νᵢ(γ) = γ wᵢ`. -/
def nu (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ) (i : ZMod 48) :
    EuclideanSpace ℝ (Fin 2 × Fin 48) :=
  γ • w S i

/-- The realized multiplier vertex is the realized multiplier direction scaled by the
multiplier factor. -/
theorem nu_apply (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ)
    (i : ZMod 48) : nu S γ i = γ • w S i :=
  -- Definitional: the right-hand side is the defining body of `nu`.
  rfl

/-- The first realized hull: the convex hull of the origin and the realized first-block
vertices `ξᵢ`. -/
def xSet (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) :
    Set (EuclideanSpace ℝ (Fin 2 × Fin 48)) :=
  convexHull ℝ (Set.insert 0 (Set.range (xi S)))

/-- The first realized hull is the convex hull of the origin and the realized first-block
vertices. -/
theorem xSet_def (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) :
    xSet S = convexHull ℝ (Set.insert 0 (Set.range (xi S))) :=
  -- Definitional: the right-hand side is the defining body of `xSet`.
  rfl

/-- The second realized hull: the convex hull of the origin and the realized first-block
family `ηᵢ`. -/
def ySet (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) :
    Set (EuclideanSpace ℝ (Fin 2 × Fin 48)) :=
  convexHull ℝ (Set.insert 0 (Set.range (eta S)))

/-- The second realized hull is the convex hull of the origin and the realized first-block
family. -/
theorem ySet_def (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) :
    ySet S = convexHull ℝ (Set.insert 0 (Set.range (eta S))) :=
  -- Definitional: the right-hand side is the defining body of `ySet`.
  rfl

/-- The realized multiplier direction is the image of the scaled second-block coefficient
vector `wᵢ = γ₀⁻¹ e₄₈₊ᵢ`. -/
theorem w_mulVec (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    w S i = WithLp.toLp 2 (S.mulVec (Coefficient.w i)) := by
  -- Unfold the two scaled directions, then push the scalar `γ₀⁻¹` out of the matrix
  -- action and out of the `WithLp.toLp` embedding.
  rw [w, Coefficient.w, Matrix.mulVec_smul, WithLp.toLp_smul]

/-- The realized residual is the image of the coefficient residual `ρᵢ = wᵢ - wᵢ₋₁`. -/
theorem rho_mulVec (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    rho S i = WithLp.toLp 2 (S.mulVec (Coefficient.rho i)) := by
  -- Distribute the difference through the matrix action and through the `WithLp` embedding.
  rw [rho, Coefficient.rho, w_mulVec, w_mulVec, Matrix.mulVec_sub, WithLp.toLp_sub]

/-- The realized first-block vertex is the image of the coefficient vertex
`ξᵢ = ηᵢ + ρᵢ`. -/
theorem xi_mulVec (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (i : ZMod 48) :
    xi S i = WithLp.toLp 2 (S.mulVec (Coefficient.xi i)) := by
  -- Distribute the sum through the matrix action and through the `WithLp` embedding.
  rw [xi, Coefficient.xi, eta_apply, rho_mulVec, Matrix.mulVec_add, WithLp.toLp_add]

/-- For a Gram factor `S` with `Sᵀ S = H`, the inner product of two realized vectors is
the Gram pairing of their coefficient vectors. -/
theorem inner_mulVec (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
    (factor : S.transpose * S = gramMatrix) (z y : (Fin 2 × Fin 48) → ℝ) :
    inner ℝ (WithLp.toLp 2 (S.mulVec z)) (WithLp.toLp 2 (S.mulVec y)) =
      dotProduct z (gramMatrix.mulVec y) := by
  -- Rewrite the Euclidean inner product of embedded vectors as a `dotProduct`, then
  -- move the first factor `S` across the pairing and reassociate it with the second.
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial]
  rw [Matrix.dotProduct_mulVec (v := S.mulVec y) (A := S) (w := z)]
  rw [← Matrix.mulVec_transpose (A := S) (x := S.mulVec y)]
  rw [Matrix.mulVec_mulVec, factor]
  -- Both sides now pair the same `gramMatrix`-image with `z`, up to the symmetric order.
  exact dotProduct_comm _ _

/-- The generic multiplier residual of the realized data is the fixed realized residual
`ρᵢ = γ⁻¹ (νᵢ - νᵢ₋₁)` for `ν = γ w`. -/
theorem residual_eq (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ)
    (gamma_ne_zero : γ ≠ 0) (i : ZMod 48) :
    ProjectionCycle.residual γ (nu S γ) i = rho S i := by
  -- Replace the generic multipliers `ν = γ w` by their affine values, factor the common
  -- `γ` out of the difference, and cancel it against `γ⁻¹` using `γ ≠ 0`.
  rw [ProjectionCycle.residual_apply, nu_apply, nu_apply, ← smul_sub, smul_smul,
    inv_mul_cancel₀ gamma_ne_zero, one_smul, rho]

/-- The generic first projection-cycle vertex of the realized data is the fixed realized
vertex `ξᵢ = ηᵢ + ρᵢ`. -/
theorem xVertex_eq (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ)
    (gamma_ne_zero : γ ≠ 0) (i : ZMod 48) :
    ProjectionCycle.xVertex γ (eta S) (nu S γ) i = xi S i := by
  -- The generic vertex is `ηᵢ` plus the generic residual, which is the realized `ρᵢ`.
  rw [ProjectionCycle.xVertex_apply, residual_eq S γ gamma_ne_zero i, xi]

/-- The generic first supporting normal of the realized data is the affine normal
`aᵢ(γ) = ηᵢ₋₁ - γ wᵢ₋₁ - ξᵢ`. -/
theorem firstNormal_eq (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ)
    (gamma_ne_zero : γ ≠ 0) (i : ZMod 48) :
    ProjectionCycle.firstNormal γ (eta S) (nu S γ) i =
      eta S (i - 1) - γ • w S (i - 1) - xi S i := by
  -- Expand the normal, evaluate `ν = γ w` at the predecessor phase, and identify the
  -- generic vertex with the realized vertex.
  rw [ProjectionCycle.firstNormal_apply, nu_apply, xVertex_eq S γ gamma_ne_zero i]

/-- The generic second supporting normal of the realized data is the affine normal
`cᵢ(γ) = γ wᵢ₋₁ + ρᵢ`. -/
theorem secondNormal_eq (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ) (γ : ℝ)
    (gamma_ne_zero : γ ≠ 0) (i : ZMod 48) :
    ProjectionCycle.secondNormal γ (nu S γ) i = γ • w S (i - 1) + rho S i := by
  -- Expand the normal, evaluate `ν = γ w` at the predecessor phase, and identify the
  -- generic residual with the realized residual.
  rw [ProjectionCycle.secondNormal_apply, nu_apply, residual_eq S γ gamma_ne_zero i]

end

end ConsensusADMM.Period48.Realization
