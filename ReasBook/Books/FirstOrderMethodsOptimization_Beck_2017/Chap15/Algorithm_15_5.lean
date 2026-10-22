/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 12 and Chapter 15 optimization files together with mathlib's proximal and adjoint API.

This item is `source-facing`: Algorithm 15.5 specifies explicit proximal updates for `x` and `z`
and reuses the standard ADMM affine update for `y`, while the proximal points remain set-valued at
statement stage. The clean public API is therefore:
- the generic map-indexed owner `adlpmm_linearization_bound` together with the canonical subtype
  `ADLPMMLinearizationParameter`, from which the source-facing `α`- and `β`-constraints are
  recovered by specializing the map to `A` and `B`;
- source-facing set-valued one-step updates for `x` and `z`;
- `admm_multiplier_update` from Algorithm 15.2 as the canonical affine multiplier owner;
- a Prop-valued trajectory structure for the iterate sequences. -/

section LinearizationBound

variable {X : Type u} {Y : Type w}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The canonical operator-norm rendering of the AD-LPMM linearization lower bound
`ρ λ_max(Lᵀ L)` is `ρ ‖L‖²`. -/
def adlpmm_linearization_bound
    (ρ : PosReal) (L : X →ₗ[ℝ] Y) : ℝ :=
  (ρ : ℝ) * ‖L.toContinuousLinearMap‖ ^ (2 : ℕ)

end LinearizationBound

section LinearizationBoundNegId

variable {Y : Type w}
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- For the linear-composite specialization `L = -I`, the canonical AD-LPMM linearization bound
always satisfies the textbook lower estimate `ρ ‖-I‖² ≤ ρ`. -/
theorem adlpmm_linearization_bound_neg_id_le
    (ρ : PosReal) :
    adlpmm_linearization_bound ρ (-LinearMap.id : Y →ₗ[ℝ] Y) ≤ (ρ : ℝ) := by
  change (ρ : ℝ) * ‖(-LinearMap.id : Y →ₗ[ℝ] Y).toContinuousLinearMap‖ ^ (2 : ℕ) ≤ (ρ : ℝ)
  have hnorm : ‖(-LinearMap.id : Y →ₗ[ℝ] Y).toContinuousLinearMap‖ ≤ 1 := by
    change ‖-(ContinuousLinearMap.id ℝ Y)‖ ≤ 1
    simpa using (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℝ Y‖ ≤ 1)
  have hsq : ‖(-LinearMap.id : Y →ₗ[ℝ] Y).toContinuousLinearMap‖ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [hnorm, norm_nonneg ((-LinearMap.id : Y →ₗ[ℝ] Y).toContinuousLinearMap)]
  have hρ : 0 ≤ (ρ : ℝ) := ρ.2.le
  calc
    (ρ : ℝ) * ‖(-LinearMap.id : Y →ₗ[ℝ] Y).toContinuousLinearMap‖ ^ (2 : ℕ)
        ≤ (ρ : ℝ) * 1 := mul_le_mul_of_nonneg_left hsq hρ
    _ = (ρ : ℝ) := by simp

/-- For the linear-composite specialization `L = -I`, the canonical AD-LPMM linearization bound
reduces to `ρ` as soon as the ambient space is nontrivial. -/
@[simp] theorem adlpmm_linearization_bound_neg_id
    [NontrivialTopology Y]
    (ρ : PosReal) :
    adlpmm_linearization_bound ρ (-LinearMap.id : Y →ₗ[ℝ] Y) = ρ := by
  have hnorm : ‖(-LinearMap.id : Y →ₗ[ℝ] Y).toContinuousLinearMap‖ = 1 := by
    change ‖-(ContinuousLinearMap.id ℝ Y)‖ = 1
    simpa using (ContinuousLinearMap.norm_id : ‖(ContinuousLinearMap.id ℝ Y)‖ = 1)
  calc
    adlpmm_linearization_bound ρ (-LinearMap.id : Y →ₗ[ℝ] Y) =
        (ρ : ℝ) * ‖(-LinearMap.id : Y →ₗ[ℝ] Y).toContinuousLinearMap‖ ^ (2 : ℕ) := rfl
    _ = (ρ : ℝ) * 1 ^ (2 : ℕ) := by rw [hnorm]
    _ = ρ := by simp

end LinearizationBoundNegId

section LinearizationParameter

variable {X : Type u} {Y : Type w}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- An admissible AD-LPMM linearization parameter for a map `L` is a positive real `τ`
satisfying the operator-norm lower bound `ρ ‖L‖² ≤ τ`, equivalently
`ρ λ_max(Lᵀ L) ≤ τ`. -/
abbrev ADLPMMLinearizationParameter
    (ρ : PosReal) (L : X →ₗ[ℝ] Y) :=
  { τ : PosReal // adlpmm_linearization_bound ρ L ≤ (τ : ℝ) }

namespace ADLPMMLinearizationParameter

section

-- Proof sketch: the subtype condition in `ADLPMMLinearizationParameter ρ L` is exactly the
-- stored lower bound `ρ ‖L‖² ≤ τ`.
/-- Every admissible AD-LPMM linearization parameter satisfies the stored lower bound
`ρ ‖L‖² ≤ τ`. -/
theorem lower_bound
    {ρ : PosReal} {L : X →ₗ[ℝ] Y}
    (τ : ADLPMMLinearizationParameter ρ L) :
    adlpmm_linearization_bound ρ L ≤ (τ : ℝ) :=
  τ.2

end

end ADLPMMLinearizationParameter

end LinearizationParameter

section XStep

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommMonoid Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The admissible next `x`-iterates in AD-LPMM are the proximal points of `(1 / α) h₁` at the
linearized augmented-Lagrangian point
`x^k - (ρ / α) Aᵀ (A x^k + B z^k - c + (1 / ρ) y^k)`. -/
def adlpmm_x_step
    (h₁ : X → EReal)
    (ρ α : PosReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (xk : X) (zk : Z) (yk : Y) : Set X :=
  prox[((((1 / α : PosReal) : EReal) • h₁))]
    (xk - ((ρ / α : PosReal) : ℝ) •
      A.adjoint (A xk + B zk - c + (1 / (ρ : ℝ)) • yk))

-- Proof sketch: unfold `adlpmm_x_step`; membership is by definition proximal-set membership for
-- the scaled function `(1 / α) h₁` at the displayed linearized point.

/-- A point belongs to `adlpmm_x_step` exactly when it satisfies the textbook proximal update from
Algorithm 15.5(a). -/
@[simp] theorem mem_adlpmm_x_step_iff
    {h₁ : X → EReal}
    {ρ α : PosReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y}
    {c : Y} {xk xNext : X} {zk : Z} {yk : Y} :
    xNext ∈ adlpmm_x_step h₁ ρ α A B c xk zk yk ↔
      xNext ∈ prox[((((1 / α : PosReal) : EReal) • h₁))]
        (xk - ((ρ / α : PosReal) : ℝ) •
          A.adjoint (A xk + B zk - c + (1 / (ρ : ℝ)) • yk)) :=
  Iff.rfl

end XStep

section ZStep

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommMonoid X] [Module ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The admissible next `z`-iterates in AD-LPMM are the proximal points of `(1 / β) h₂` at the
linearized augmented-Lagrangian point
`z^k - (ρ / β) Bᵀ (A x^(k+1) + B z^k - c + (1 / ρ) y^k)`. -/
def adlpmm_z_step
    (h₂ : Z → EReal)
    (ρ β : PosReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (c : Y) (xNext : X) (zk : Z) (yk : Y) : Set Z :=
  prox[((((1 / β : PosReal) : EReal) • h₂))]
    (zk - ((ρ / β : PosReal) : ℝ) •
      B.adjoint (A xNext + B zk - c + (1 / (ρ : ℝ)) • yk))

-- Proof sketch: unfold `adlpmm_z_step`; membership is by definition proximal-set membership for
-- the scaled function `(1 / β) h₂` at the displayed linearized point.

/-- A point belongs to `adlpmm_z_step` exactly when it satisfies the textbook proximal update from
Algorithm 15.5(b). -/
@[simp] theorem mem_adlpmm_z_step_iff
    {h₂ : Z → EReal}
    {ρ β : PosReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y}
    {c : Y} {xNext : X} {zk zNext : Z} {yk : Y} :
    zNext ∈ adlpmm_z_step h₂ ρ β A B c xNext zk yk ↔
      zNext ∈ prox[((((1 / β : PosReal) : EReal) • h₂))]
        (zk - ((ρ / β : PosReal) : ℝ) •
          B.adjoint (A xNext + B zk - c + (1 / (ρ : ℝ)) • yk)) :=
  Iff.rfl

end ZStep

section Trajectory

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Algorithm 15.5: given initial points `x^0 = x0`, `z^0 = z0`, `y^0 = y0`, a positive penalty
parameter `ρ`, and admissible linearization parameters `α` and `β` satisfying the operator-norm
forms of `ρ λ_max(Aᵀ A) ≤ α` and `ρ λ_max(Bᵀ B) ≤ β`, the sequences `x`, `z`, and `y` form an
AD-LPMM trajectory when, for every iteration `k`, `x^(k+1)` satisfies the proximal update in
(a), `z^(k+1)` satisfies the proximal update in (b), and `y^(k+1)` satisfies the affine update in
(c). -/
class IsADLPMMTrajectory
    (ρ : PosReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (α : ADLPMMLinearizationParameter ρ A)
    (β : ADLPMMLinearizationParameter ρ B)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (x : ℕ → X) (z : ℕ → Z) (y : ℕ → Y)
    (x0 : X) (z0 : Z) (y0 : Y) : Prop where
  x_zero : x 0 = x0
  z_zero : z 0 = z0
  y_zero : y 0 = y0
  x_step (k : ℕ) :
    x (k + 1) ∈ adlpmm_x_step h₁ ρ α A B c (x k) (z k) (y k)
  z_step (k : ℕ) :
    z (k + 1) ∈ adlpmm_z_step h₂ ρ β A B c (x (k + 1)) (z k) (y k)
  y_step (k : ℕ) :
    y (k + 1) = admm_multiplier_update ρ A B c (y k) (x (k + 1)) (z (k + 1))

/-- An Algorithm 15.5 AD-LPMM trajectory predicate is a proposition, hence subsingleton. -/
instance instSubsingletonIsADLPMMTrajectory
    {ρ : PosReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {α : ADLPMMLinearizationParameter ρ A}
    {β : ADLPMMLinearizationParameter ρ B}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y}
    {x0 : X} {z0 : Z} {y0 : Y} :
    Subsingleton (IsADLPMMTrajectory ρ A B c α β h₁ h₂ x z y x0 z0 y0) :=
  inferInstance

end Trajectory

end
