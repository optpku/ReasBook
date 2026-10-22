/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v w

section

variable {ι : Type v} {X : Type u} {Y : ι → Type w}
variable [Fintype ι]
variable [AddCommMonoid X] [Module ℝ X]
variable [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled directly from the
nearby Chapter 15 ADMM files, the finite-sum linear-composite owner from Definition 15.9, and
the shared proximal API from Chapter 6.

This item is `source-facing`: Algorithm 15.15 gives the version-1 ADMM recursion for the
finite-sum linear-composite problem in the case where the stacked operator `A` has full column
rank, so the `x`-step can be written explicitly. Domain sampling shows that the right ambient
owner is the canonical Hilbert product `PiLp (2 : ENNReal) Y`, not the raw dependent function
type:
- `core/canonical`: the stacked block space `PiLp (2 : ENNReal) Y`;
- `bridge/view`: the stacked map `x ↦ (A_i x)_i`, implemented as a linear map
  `X →ₗ[ℝ] PiLp (2 : ENNReal) Y`;
- `core/canonical`: Chapter 6's `PiLp.separableSum` and `prox[...]` for the aggregate `z`-step;
- `source-facing`: the explicit full-column-rank `x`-formula and the coordinatewise `z_i` and
  `y_i` bridge theorems.

Primitive data are therefore the family `A`, the block penalties `g_i`, the iterate sequences,
and the prescribed initial data `x⁰`, `z⁰`, `y⁰`. The `PiLp 2` product owner supplies the
correct `L²` quadratic term for the inherited ADMM `z`-subproblem, while the coordinate formulas
remain derived bridge API. -/

local notation "Z" => PiLp (2 : ENNReal) Y

/-- The canonical stacked block operator `x ↦ (A_i x)_i`, viewed on the `PiLp 2` product owner. -/
def admm_finite_sum_linear_composite_stacked_map
    (A : ∀ i, X →ₗ[ℝ] Y i) : X →ₗ[ℝ] Z :=
  ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Y).symm.toLinearMap).comp (LinearMap.pi A)

/-- Evaluating the canonical stacked block operator at coordinate `i` recovers `A_i x`. -/
@[simp] theorem admm_finite_sum_linear_composite_stacked_map_apply
    (A : ∀ i, X →ₗ[ℝ] Y i) (x : X) (i : ι) :
    admm_finite_sum_linear_composite_stacked_map A x i = A i x := by
  simp [admm_finite_sum_linear_composite_stacked_map]

end

section

variable {ι : Type v} {X : Type u} {Y : ι → Type w}
variable [Fintype ι]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [∀ i, NormedAddCommGroup (Y i)]
variable [∀ i, InnerProductSpace ℝ (Y i)]
variable [∀ i, FiniteDimensional ℝ (Y i)]

local notation "Z" => PiLp (2 : ENNReal) Y

/-- The finite-sum normal operator attached to the canonical stacked map on `PiLp 2 Y`. -/
def admm_finite_sum_linear_composite_normal_map
    (A : ∀ i, X →ₗ[ℝ] Y i) : X →ₗ[ℝ] X :=
  (admm_finite_sum_linear_composite_stacked_map A).adjoint.comp
    (admm_finite_sum_linear_composite_stacked_map A)

/-- Evaluating the finite-sum normal operator at `x` gives `∑ i, A_iᵀ (A_i x)`. -/
@[simp] theorem admm_finite_sum_linear_composite_normal_map_apply
    (A : ∀ i, X →ₗ[ℝ] Y i) (x : X) :
    admm_finite_sum_linear_composite_normal_map A x =
      ∑ i, (A i).adjoint (A i x) := by
  apply ext_inner_right ℝ
  intro u
  calc
    inner ℝ (admm_finite_sum_linear_composite_normal_map A x) u =
        inner ℝ
          (admm_finite_sum_linear_composite_stacked_map A x)
          (admm_finite_sum_linear_composite_stacked_map A u) := by
      simpa [admm_finite_sum_linear_composite_normal_map] using
        LinearMap.adjoint_inner_left
          (admm_finite_sum_linear_composite_stacked_map A)
          u
          (admm_finite_sum_linear_composite_stacked_map A x)
    _ = ∑ i, inner ℝ (A i x) (A i u) := by
      simp [PiLp.inner_apply]
    _ = ∑ i, inner ℝ ((A i).adjoint (A i x)) u := by
      simp only [LinearMap.adjoint_inner_left]
    _ = inner ℝ (∑ i, (A i).adjoint (A i x)) u := by
      rw [sum_inner]

/-- The adjoint of the canonical stacked block map acts coordinatewise by summing the block
adjoints. -/
@[simp] theorem admm_finite_sum_linear_composite_stacked_map_adjoint_apply
    (A : ∀ i, X →ₗ[ℝ] Y i) (z : Z) :
    (admm_finite_sum_linear_composite_stacked_map A).adjoint z =
      ∑ i, (A i).adjoint (z i) := by
  apply ext_inner_right ℝ
  intro u
  calc
    inner ℝ ((admm_finite_sum_linear_composite_stacked_map A).adjoint z) u =
        inner ℝ z (admm_finite_sum_linear_composite_stacked_map A u) := by
      simpa using
        LinearMap.adjoint_inner_left
          (admm_finite_sum_linear_composite_stacked_map A)
          u
          z
    _ = ∑ i, inner ℝ (z i) (A i u) := by
      simp [PiLp.inner_apply]
    _ = ∑ i, inner ℝ ((A i).adjoint (z i)) u := by
      simp only [LinearMap.adjoint_inner_left]
    _ = inner ℝ (∑ i, (A i).adjoint (z i)) u := by
      rw [sum_inner]

/-- If the canonical stacked block operator has full column rank, then the normal operator is
injective. -/
theorem admm_finite_sum_linear_composite_normal_map_injective
    (A : ∀ i, X →ₗ[ℝ] Y i)
    (hA : Function.Injective (admm_finite_sum_linear_composite_stacked_map A)) :
    Function.Injective (admm_finite_sum_linear_composite_normal_map A) := by
  intro x y hxy
  have h0 : admm_finite_sum_linear_composite_normal_map A (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hnormsq :
      ‖admm_finite_sum_linear_composite_stacked_map A (x - y)‖ ^ (2 : ℕ) = 0 := by
    calc
      ‖admm_finite_sum_linear_composite_stacked_map A (x - y)‖ ^ (2 : ℕ) =
          inner ℝ
            (admm_finite_sum_linear_composite_stacked_map A (x - y))
            (admm_finite_sum_linear_composite_stacked_map A (x - y)) := by
        symm
        exact real_inner_self_eq_norm_sq _
      _ = inner ℝ (admm_finite_sum_linear_composite_normal_map A (x - y)) (x - y) := by
        symm
        simpa [admm_finite_sum_linear_composite_normal_map] using
          LinearMap.adjoint_inner_left
            (admm_finite_sum_linear_composite_stacked_map A)
            (x - y)
            (admm_finite_sum_linear_composite_stacked_map A (x - y))
      _ = 0 := by simp [h0]
  have hstacked : admm_finite_sum_linear_composite_stacked_map A (x - y) = 0 := by
    exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnormsq)
  have hsub : x - y = 0 := by
    apply hA
    simpa using hstacked
  exact sub_eq_zero.mp hsub

/-- The explicit version-1 ADMM `x`-update in the full-column-rank case:
`x^(k+1) = (∑ i, A_iᵀ A_i)⁻¹ ∑ i, A_iᵀ (z_i^k - (1 / ρ) y_i^k)`. -/
def admm_finite_sum_linear_composite_v1_x_update
    (A : ∀ i, X →ₗ[ℝ] Y i)
    (hA : Function.Injective (admm_finite_sum_linear_composite_stacked_map A))
    (ρ : PosReal)
    (zk yk : Z) : X :=
  (LinearEquiv.ofInjectiveEndo
      (admm_finite_sum_linear_composite_normal_map A)
      (admm_finite_sum_linear_composite_normal_map_injective A hA)).symm
    (∑ i, (A i).adjoint (zk i - (1 / (ρ : ℝ)) • yk i))

end

section

variable {ι : Type v} {X : Type u} {Y : ι → Type w}
variable [Fintype ι]
variable [AddCommMonoid X] [Module ℝ X]
variable [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]

local notation "Z" => PiLp (2 : ENNReal) Y

/-- The stacked proximal center `A x^(k+1) + (1 / ρ) y^k` on the canonical `PiLp 2` block
product. -/
def admm_finite_sum_linear_composite_v1_z_update_center
    (ρ : PosReal)
    (A : ∀ i, X →ₗ[ℝ] Y i)
    (xNext : X)
    (yk : Z) : Z :=
  admm_finite_sum_linear_composite_stacked_map A xNext + (1 / (ρ : ℝ)) • yk

/-- Evaluating the stacked proximal center at block `i` gives `A_i x^(k+1) + (1 / ρ) y_i^k`. -/
@[simp] theorem admm_finite_sum_linear_composite_v1_z_update_center_apply
    (ρ : PosReal)
    (A : ∀ i, X →ₗ[ℝ] Y i)
    (xNext : X)
    (yk : Z)
    (i : ι) :
    admm_finite_sum_linear_composite_v1_z_update_center ρ A xNext yk i =
      A i xNext + (1 / (ρ : ℝ)) • yk i := by
  simp [admm_finite_sum_linear_composite_v1_z_update_center]

end

section

variable {ι : Type v} {X : Type u} {Y : ι → Type w}
variable [Fintype ι]
variable [AddCommMonoid X] [Module ℝ X]
variable [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]

local notation "Z" => PiLp (2 : ENNReal) Y

/-- Under coordinatewise properness of the block penalties, the canonical aggregate proximal
`z`-update is equivalent to the displayed coordinatewise proximal clauses from Algorithm 15.15. -/
@[simp] theorem admm_finite_sum_linear_composite_v1_z_step_iff
    {ρ : PosReal}
    {g : ∀ i, Y i → EReal}
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {A : ∀ i, X →ₗ[ℝ] Y i}
    {xNext : X}
    {yk zNext : Z} :
    zNext ∈ prox[(((1 / ρ : PosReal) : EReal) • PiLp.separableSum g)]
      (admm_finite_sum_linear_composite_v1_z_update_center ρ A xNext yk) ↔
      ∀ i,
        zNext i ∈ prox[(((1 / ρ : PosReal) : EReal) • g i)]
          (admm_finite_sum_linear_composite_v1_z_update_center ρ A xNext yk i) := by
  have hρinv_nonneg : (0 : EReal) ≤ ((1 / ρ : PosReal) : ℝ) := by
    exact_mod_cast (show 0 ≤ ((1 / ρ : PosReal) : ℝ) by exact (1 / ρ : PosReal).2.le)
  have hg_scaled_proper :
      ∀ i, IsProperExtendedRealFunction ((((1 / ρ : PosReal) : EReal) • g i)) := by
    intro i
    refine ⟨?_, ?_⟩
    · intro y
      rw [Pi.smul_apply, smul_eq_mul]
      exact
        (EReal.mul_ne_bot _ _).2
          ⟨Or.inl (EReal.coe_ne_bot _), Or.inr ((hg_proper i).ne_bot y),
            Or.inl (EReal.coe_ne_top _), Or.inl hρinv_nonneg⟩
    · rcases (hg_proper i).effective_domain_nonempty with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [mem_effective_domain, Pi.smul_apply, smul_eq_mul]
      exact
        lt_top_iff_ne_top.mpr <|
          (EReal.mul_ne_top _ _).2
            ⟨Or.inl (EReal.coe_ne_bot _), Or.inl hρinv_nonneg,
              Or.inl (EReal.coe_ne_top _), Or.inr (mem_effective_domain.mp hy).ne⟩
  have hscaled_separableSum :
      (((1 / ρ : PosReal) : EReal) • PiLp.separableSum g) =
        PiLp.separableSum (fun i ↦ (((1 / ρ : PosReal) : EReal) • g i)) := by
    funext z
    classical
    let a : EReal := (((1 / ρ : PosReal) : ℝ) : EReal)
    have ha_nonneg : 0 ≤ a := hρinv_nonneg
    have ha_ne_top : a ≠ ⊤ := EReal.coe_ne_top _
    have hmul_sum :
        a * (∑ i : ι, g i (z.ofLp i)) = ∑ i : ι, a * g i (z.ofLp i) := by
      refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
      · simp
      · intro i s hi hs
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top, hs]
    rw [Pi.smul_apply, PiLp.separableSum_apply, PiLp.separableSum_apply, smul_eq_mul]
    simpa [a] using hmul_sum
  have hscaled_apply (z : Z) :
      ((((1 / ρ : PosReal) : EReal) • PiLp.separableSum g) z) =
        PiLp.separableSum (fun i ↦ (((1 / ρ : PosReal) : EReal) • g i)) z :=
    congrFun hscaled_separableSum z
  constructor
  · intro hz
    have hz' :
        zNext ∈ prox[PiLp.separableSum (fun i ↦ (((1 / ρ : PosReal) : EReal) • g i))]
          (admm_finite_sum_linear_composite_v1_z_update_center ρ A xNext yk) := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hz ⊢
      intro v
      rw [proximal_objective_apply, proximal_objective_apply,
        ← hscaled_apply zNext, ← hscaled_apply v]
      exact hz v
    simpa using
      (mem_prox_separableSum_iff hg_scaled_proper).mp hz'
  · intro hz
    have hz' :
        zNext ∈ prox[PiLp.separableSum (fun i ↦ (((1 / ρ : PosReal) : EReal) • g i))]
          (admm_finite_sum_linear_composite_v1_z_update_center ρ A xNext yk) := by
      exact
        (mem_prox_separableSum_iff hg_scaled_proper).mpr <| by
            intro i
            simpa using hz i
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hz' ⊢
    intro v
    rw [proximal_objective_apply, proximal_objective_apply,
      hscaled_apply zNext, hscaled_apply v]
    exact hz' v

end

section

variable {ι : Type v} {X : Type u} {Y : ι → Type w}
variable [Fintype ι]
variable [AddCommMonoid X] [Module ℝ X]
variable [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]

local notation "Z" => PiLp (2 : ENNReal) Y

/-- The coordinatewise multiplier update
`y_i^(k+1) = y_i^k + ρ (A_i x^(k+1) - z_i^(k+1))`. -/
@[simp] theorem admm_multiplier_update_finite_sum_linear_composite_apply
    (ρ : PosReal)
    (A : ∀ i, X →ₗ[ℝ] Y i)
    (yk : Z)
    (xNext : X)
    (zNext : Z)
    (i : ι) :
    admm_multiplier_update
        ρ
        (admm_finite_sum_linear_composite_stacked_map A)
        (-LinearMap.id)
        0
        yk
        xNext
        zNext
        i =
      yk i + (ρ : ℝ) • (A i xNext - zNext i) := by
  simp [admm_multiplier_update, sub_eq_add_neg]

end

section

variable {ι : Type v} {X : Type u} {Y : ι → Type w}
variable [Fintype ι]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [∀ i, NormedAddCommGroup (Y i)]
variable [∀ i, InnerProductSpace ℝ (Y i)]
variable [∀ i, FiniteDimensional ℝ (Y i)]

local notation "Z" => PiLp (2 : ENNReal) Y

/-- Algorithm 15.15: for the finite-sum linear-composite problem `min_x ∑ i, g_i(A_i x)`,
assume the canonical stacked operator `x ↦ (A_i x)_i` on `PiLp 2 Y` has full column rank. The
underlying ADMM trajectory is the canonical alternating trajectory for the split objective
`0 + PiLp.separableSum g` and constraint `A x - z = 0`; the source-facing content retained here is
the explicit full-column-rank formula for the `x`-update. -/
class IsADMMFiniteSumLinearCompositeTrajectoryV1FullColumnRank
    (A : ∀ i, X →ₗ[ℝ] Y i)
    (ρ : PosReal)
    (g : ∀ i, Y i → EReal)
    (x : ℕ → X)
    (z y : ℕ → Z)
    (x0 : X)
    (z0 y0 : Z) : Prop extends
    IsADMMAlternatingTrajectory
      ρ
      (fun _ : X ↦ (0 : EReal))
      (PiLp.separableSum g)
      (admm_finite_sum_linear_composite_stacked_map A)
      (-LinearMap.id)
      0
      x
      z
      y
      x0
      z0
      y0 where
  fullColumnRank : Function.Injective (admm_finite_sum_linear_composite_stacked_map A)
  x_step_eq (k : ℕ) :
    x (k + 1) = admm_finite_sum_linear_composite_v1_x_update A fullColumnRank ρ (z k) (y k)

/-- An Algorithm 15.15 full-column-rank trajectory predicate is a proposition, hence
subsingleton. -/
instance
    {A : ∀ i, X →ₗ[ℝ] Y i}
    {ρ : PosReal}
    {g : ∀ i, Y i → EReal}
    {x : ℕ → X}
    {z y : ℕ → Z}
    {x0 : X}
    {z0 y0 : Z}
    :
    Subsingleton
      (IsADMMFiniteSumLinearCompositeTrajectoryV1FullColumnRank A ρ g x z y x0 z0 y0) :=
  inferInstance

namespace IsADMMFiniteSumLinearCompositeTrajectoryV1FullColumnRank

/-- Along an Algorithm 15.15 trajectory, the `x`-iterate is the displayed explicit
full-column-rank update formula. -/
theorem x_step_formula
    {A : ∀ i, X →ₗ[ℝ] Y i}
    {ρ : PosReal}
    {g : ∀ i, Y i → EReal}
    {x : ℕ → X}
    {z y : ℕ → Z}
    {x0 : X}
    {z0 y0 : Z}
    (h : IsADMMFiniteSumLinearCompositeTrajectoryV1FullColumnRank A ρ g x z y x0 z0 y0)
    (k : ℕ) :
    x (k + 1) = admm_finite_sum_linear_composite_v1_x_update A h.fullColumnRank ρ (z k) (y k) :=
  h.x_step_eq k

/-- Along an Algorithm 15.15 trajectory, the inherited canonical stacked ADMM `z`-step is exactly
the aggregate separable proximal update from the textbook. -/
theorem z_step_mem
    {A : ∀ i, X →ₗ[ℝ] Y i}
    {ρ : PosReal}
    {g : ∀ i, Y i → EReal}
    {x : ℕ → X}
    {z y : ℕ → Z}
    {x0 : X}
    {z0 y0 : Z}
    (h : IsADMMFiniteSumLinearCompositeTrajectoryV1FullColumnRank A ρ g x z y x0 z0 y0)
    (k : ℕ) :
    z (k + 1) ∈ prox[(((1 / ρ : PosReal) : EReal) • PiLp.separableSum g)]
      (admm_finite_sum_linear_composite_v1_z_update_center ρ A (x (k + 1)) (y k)) := by
  simpa [admm_finite_sum_linear_composite_v1_z_update_center] using
    h.toIsADMMAlternatingTrajectory.z_step_linear_composite k

/-- Under coordinatewise properness of the block penalties, the canonical aggregate `z`-step in
Algorithm 15.15 reduces to the displayed coordinatewise proximal formula. -/
theorem z_step_prox
    {A : ∀ i, X →ₗ[ℝ] Y i}
    {ρ : PosReal}
    {g : ∀ i, Y i → EReal}
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x : ℕ → X}
    {z y : ℕ → Z}
    {x0 : X}
    {z0 y0 : Z}
    (h : IsADMMFiniteSumLinearCompositeTrajectoryV1FullColumnRank A ρ g x z y x0 z0 y0)
    (k : ℕ) :
    ∀ i,
      z (k + 1) i ∈ prox[(((1 / ρ : PosReal) : EReal) • g i)]
        (admm_finite_sum_linear_composite_v1_z_update_center ρ A (x (k + 1)) (y k) i) := by
  simpa using (admm_finite_sum_linear_composite_v1_z_step_iff hg_proper).mp (h.z_step_mem k)

/-- Along an Algorithm 15.15 trajectory, the inherited canonical stacked multiplier update reduces
coordinatewise to `y_i^(k+1) = y_i^k + ρ (A_i x^(k+1) - z_i^(k+1))`. -/
theorem y_step_apply
    {A : ∀ i, X →ₗ[ℝ] Y i}
    {ρ : PosReal}
    {g : ∀ i, Y i → EReal}
    {x : ℕ → X}
    {z y : ℕ → Z}
    {x0 : X}
    {z0 y0 : Z}
    (h : IsADMMFiniteSumLinearCompositeTrajectoryV1FullColumnRank A ρ g x z y x0 z0 y0)
    (k : ℕ)
    (i : ι) :
    y (k + 1) i = y k i + (ρ : ℝ) • (A i (x (k + 1)) - z (k + 1) i) := by
  simpa using
    congrArg (fun u : Z ↦ u i) (h.toIsADMMAlternatingTrajectory.y_step_linear_composite k)

end IsADMMFiniteSumLinearCompositeTrajectoryV1FullColumnRank

end
