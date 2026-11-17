module

public import ReasLib.Optimization.DFP.Polar.InterpolationSum
public import ReasLib.Optimization.DFP.Polar.ActualObjective
public import ReasLib.Optimization.DFP.Polar.HolderSharpness
public import ReasLib.Analysis.Calculus.Gradient.HessianHolder
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Interpolation with an arbitrary Hölder exponent

The explicit cutoff from `ExplicitCutoff` has a uniform Hessian bound and a
Lipschitz Hessian bound. Interpolating their minimum gives every exponent in
`[0, 1]`, with one constant fixed before the exponent and the interpolation
data. The disjoint-support estimate then applies to the actual correction sum.
-/

public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DFP.Polar.General.InterpolationBounds

/-- Helper for lem:polar-interpolation: the minimum of two nonnegative
numbers is bounded by their weighted geometric mean for any weight in `[0,1]`.
This inequality is upstream-worthy as a real-power interpolation estimate. -/
theorem min_le_rpow_mul_rpow {A B β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hβ : 0 ≤ β) (hβone : β ≤ 1) :
    min A B ≤ A ^ (1 - β) * B ^ β := by
  have hmin : 0 ≤ min A B := le_min hA hB
  have hcomplement : 0 ≤ 1 - β := sub_nonneg.mpr hβone
  calc
    min A B = (min A B) ^ (1 - β) * (min A B) ^ β := by
      rw [← Real.rpow_add_of_nonneg hmin hcomplement hβ, sub_add_cancel,
        Real.rpow_one]
    _ ≤ A ^ (1 - β) * B ^ β :=
      mul_le_mul (Real.rpow_le_rpow hmin (min_le_left A B) hcomplement)
        (Real.rpow_le_rpow hmin (min_le_right A B) hβ)
        (Real.rpow_nonneg hmin _) (Real.rpow_nonneg hA _)

/-- Helper for lem:polar-interpolation: the geometric interpolation of the
inverse-radius and inverse-square-radius moduli has radius power `-(1+β)`.
This scalar identity is file-local support for the explicit cutoff bounds. -/
theorem inverse_scales_rpow_mul (ρ d β : ℝ) (hρ : 0 < ρ) (hd : 0 ≤ d) :
    (ρ⁻¹) ^ (1 - β) * ((ρ⁻¹) ^ 2 * d) ^ β =
      ρ ^ (-(1 + β)) * d ^ β := by
  have hexponent : (1 - β) + 2 * β = 1 + β := by
    ring
  rw [Real.mul_rpow (sq_nonneg _) hd, ← Real.rpow_two (ρ⁻¹),
    ← Real.rpow_mul (inv_nonneg.mpr hρ.le), ← mul_assoc,
    ← Real.rpow_add (inv_pos.mpr hρ), hexponent,
    ← Real.rpow_neg_eq_inv_rpow]

/-- Helper for lem:polar-interpolation: the minimum of the uniform and
Lipschitz inverse-radius scales satisfies the arbitrary Hölder modulus.
This scalar inequality is file-local support for the explicit cutoff bounds. -/
theorem min_inverse_scales_le_holderPower {ρ d β : ℝ} (hρ : 0 < ρ) (hd : 0 ≤ d)
    (hβ : 0 ≤ β) (hβone : β ≤ 1) :
    min (ρ⁻¹) ((ρ⁻¹) ^ 2 * d) ≤ ρ ^ (-(1 + β)) * d ^ β := by
  calc
    min (ρ⁻¹) ((ρ⁻¹) ^ 2 * d) ≤
        (ρ⁻¹) ^ (1 - β) * ((ρ⁻¹) ^ 2 * d) ^ β :=
      min_le_rpow_mul_rpow (inv_pos.mpr hρ).le
        (mul_nonneg (sq_nonneg _) hd) hβ hβone
    _ = ρ ^ (-(1 + β)) * d ^ β := inverse_scales_rpow_mul ρ d β hρ hd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Helper for lem:polar-interpolation: (arbitrary-exponent single correction estimate).
The Hessian of the manuscript's explicit cutoff-times-affine correction is
globally `β`-Hölder with coefficient `Cχ ‖a‖ ρ^(-(1+β))`. One cutoff constant
works for every `β ∈ [0,1]` and all centers, radii, and affine coefficients. -/
theorem exists_norm_hessian_correction_sub_le :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      ∀ (c : E) (ρ : ℝ) (a x y : E), 0 < ρ →
        ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) x -
          fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) y‖ ≤
          Cχ * ‖a‖ * ρ ^ (-(1 + β)) * ‖x - y‖ ^ β := by
  obtain ⟨Cχ, hCχ, hmin⟩ :=
    DFP.Polar.InterpolationBounds.exists_norm_hessian_correction_sub_le_min (E := E)
  refine ⟨Cχ, hCχ, ?_⟩
  intro β hβ hβone c ρ a x y hρ
  calc
    ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) x -
        fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) y‖ ≤
        Cχ * ‖a‖ * min (ρ⁻¹) ((ρ⁻¹) ^ 2 * ‖x - y‖) := hmin c ρ a x y hρ
    _ ≤ Cχ * ‖a‖ * (ρ ^ (-(1 + β)) * ‖x - y‖ ^ β) :=
      mul_le_mul_of_nonneg_left
        (min_inverse_scales_le_holderPower hρ (norm_nonneg _) hβ hβone)
        (mul_nonneg hCχ (norm_nonneg _))
    _ = Cχ * ‖a‖ * ρ ^ (-(1 + β)) * ‖x - y‖ ^ β := by
      ring

/-- Helper for lem:polar-interpolation: pairwise disjoint explicit correction
supports and a bounded scaled coefficient envelope give a global `β`-Hölder
estimate for the pointwise sum of correction Hessians. The cutoff constant is
fixed before the exponent, index type, centers, radii, and coefficients.
This is a reusable extension of the disjoint correction API. -/
theorem exists_norm_finsum_hessian_correction_sub_le {ι : Type*} :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      ∀ (c : ι → E) (ρ : ι → ℝ) (a : ι → E) (M : ℝ),
        0 ≤ M → (∀ i, 0 < ρ i) →
        Set.univ.PairwiseDisjoint (fun i ↦ Metric.ball (c i) (ρ i)) →
        (∀ i, ‖a i‖ * (ρ i) ^ (-(1 + β)) ≤ M) → ∀ x y : E,
        ‖(∑ᶠ i, fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) x) -
          ∑ᶠ i, fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) y‖ ≤
          2 * Cχ * M * ‖x - y‖ ^ β := by
  obtain ⟨Cχ, hCχ, hlocal⟩ := exists_norm_hessian_correction_sub_le (E := E)
  refine ⟨Cχ, hCχ, ?_⟩
  intro β hβ hβone c ρ a M hM hρ hballs hscaled x y
  have hdisjoint : Set.univ.PairwiseDisjoint
      (fun i ↦ Function.support
        (fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))))) :=
    hballs.mono (fun i ↦ DFP.Polar.InterpolationBounds.support_hessian_correction_subset_ball
      (c i) (ρ i) (a i) (hρ i))
  have hmodulus (u v : E) : 0 ≤ Cχ * M * ‖u - v‖ ^ β :=
    mul_nonneg (mul_nonneg hCχ hM) (Real.rpow_nonneg (norm_nonneg _) _)
  have hlocalUniform (i : ι) (u v : E) :
      ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) u -
        fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) v‖ ≤
        Cχ * M * ‖u - v‖ ^ β := by
    calc
      ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) u -
          fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) v‖ ≤
          Cχ * ‖a i‖ * (ρ i) ^ (-(1 + β)) * ‖u - v‖ ^ β :=
        hlocal β hβ hβone (c i) (ρ i) (a i) u v (hρ i)
      _ = Cχ * (‖a i‖ * (ρ i) ^ (-(1 + β))) * ‖u - v‖ ^ β := by
        ring
      _ ≤ Cχ * M * ‖u - v‖ ^ β :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hscaled i) hCχ)
          (Real.rpow_nonneg (norm_nonneg _) _)
  have hsum := DFP.Polar.InterpolationBounds.norm_finsum_sub_le_two_mul_modulus
    (fun i ↦ fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))))
    hdisjoint (fun u v ↦ Cχ * M * ‖u - v‖ ^ β) hmodulus hlocalUniform x y
  calc
    ‖(∑ᶠ i, fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) x) -
        ∑ᶠ i, fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) y‖ ≤
        2 * (Cχ * M * ‖x - y‖ ^ β) := hsum
    _ = 2 * Cχ * M * ‖x - y‖ ^ β := by
      ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for lem:polar-interpolation and eq:polar-support-radii: a correction
of size at most `A τ^(1+β)` supported at radius `κ τ` has scaled Hölder
coefficient at most `A κ^(-(1+β))`. This reusable estimate does not require
any restriction on the exponent. -/
theorem coefficient_mul_radius_rpow_le {a : E} {ρ τ κ A β : ℝ}
    (hκ : 0 < κ) (hτ : 0 < τ) (hρ : ρ = κ * τ)
    (ha : ‖a‖ ≤ A * τ ^ (1 + β)) :
    ‖a‖ * ρ ^ (-(1 + β)) ≤ A * κ ^ (-(1 + β)) := by
  have hcancel : τ ^ (1 + β) * τ ^ (-(1 + β)) = 1 := by
    rw [← Real.rpow_add hτ, add_neg_cancel, Real.rpow_zero]
  rw [hρ]
  calc
    ‖a‖ * (κ * τ) ^ (-(1 + β)) ≤
        (A * τ ^ (1 + β)) * (κ * τ) ^ (-(1 + β)) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (mul_pos hκ hτ).le _)
    _ = (A * κ ^ (-(1 + β))) * (τ ^ (1 + β) * τ ^ (-(1 + β))) := by
      rw [Real.mul_rpow hκ.le hτ.le]
      ring
    _ = A * κ ^ (-(1 + β)) := by
      rw [hcancel, mul_one]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for lem:polar-interpolation and eq:polar-interpolation-bound: a
correction of size at most `A τ^(1+β)` at radius `κ τ` has Hessian scale at
most `(A/κ) τ^β`. This reusable estimate does not restrict the exponent. -/
theorem coefficient_div_radius_le {a : E} {ρ τ κ A β : ℝ}
    (hκ : 0 < κ) (hτ : 0 < τ) (hρ : ρ = κ * τ)
    (ha : ‖a‖ ≤ A * τ ^ (1 + β)) :
    ‖a‖ / ρ ≤ (A / κ) * τ ^ β := by
  rw [hρ]
  calc
    ‖a‖ / (κ * τ) ≤ (A * τ ^ (1 + β)) / (κ * τ) :=
      div_le_div_of_nonneg_right ha (mul_pos hκ hτ).le
    _ = (A / κ) * τ ^ β := by
      rw [Real.rpow_add hτ, Real.rpow_one]
      field_simp [hκ.ne', hτ.ne']

variable [Nontrivial E]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Helper for lem:polar-interpolation and eq:polar-objective: each bump in
the actual infinite sum is the explicit cutoff-times-affine correction with
the same data. This file-local adapter exposes the function equality across
module boundaries so derivative estimates transfer without unfolding. -/
theorem bump_eq_correction (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (k : ℕ) :
    InterpolationSum.bump c ρ a k = ExplicitCutoff.correction (c k) (ρ k) (a k) := by
  ext x
  rw [InterpolationSum.bump_apply, ExplicitCutoff.correction_apply]

/-- Helper for lem:polar-interpolation: the actual infinite perturbation built
from the explicit cutoff has a global `β`-Hölder Hessian under the geometric
gluing hypotheses and the scaled coefficient envelope. Its derivative-sum
identity is supplied by the existing regularity theorem, rather than assumed.
This is a reusable arbitrary-exponent extension of the correction-sum API. -/
theorem exists_hessian_holder_perturbation :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      ∀ (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E),
        InterpolationSum.Geometry c ρ a → ∀ M : ℝ, 0 ≤ M →
        (∀ k, ‖a k‖ * (ρ k) ^ (-(1 + β)) ≤ M) → ∀ x y,
        ‖fderiv ℝ (fderiv ℝ (InterpolationSum.perturbation c ρ a)) x -
          fderiv ℝ (fderiv ℝ (InterpolationSum.perturbation c ρ a)) y‖ ≤
          2 * Cχ * M * ‖x - y‖ ^ β := by
  obtain ⟨Cχ, hCχ, hholder⟩ :=
    exists_norm_finsum_hessian_correction_sub_le (E := E) (ι := ℕ)
  refine ⟨Cχ, hCχ, ?_⟩
  intro β hβ hβone c ρ a h M hM hbound x y
  rw [InterpolationSum.secondFDeriv_perturbation h,
    InterpolationSum.secondFDeriv_perturbation h]
  simpa only [bump_eq_correction] using
    hholder β hβ hβone c ρ a M hM h.radius_pos h.disjoint_open hbound x y

/-- Helper for lem:polar-interpolation: one fixed cutoff constant controls
both the actual perturbation's uniform Hessian norm and its `β`-Hölder modulus.
The constant is independent of the exponent and all interpolation data.
This is a reusable arbitrary-exponent extension of the correction-sum API. -/
theorem exists_global_hessian_bounds :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      ∀ (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E),
        InterpolationSum.Geometry c ρ a → ∀ B M : ℝ, 0 ≤ B → 0 ≤ M →
        (∀ k, ‖a k‖ / ρ k ≤ B) → (∀ k, ‖a k‖ * (ρ k) ^ (-(1 + β)) ≤ M) →
        (∀ x, ‖fderiv ℝ (fderiv ℝ (InterpolationSum.perturbation c ρ a)) x‖ ≤ Cχ * B) ∧
        (∀ x y, ‖fderiv ℝ (fderiv ℝ (InterpolationSum.perturbation c ρ a)) x -
          fderiv ℝ (fderiv ℝ (InterpolationSum.perturbation c ρ a)) y‖ ≤
            2 * Cχ * M * ‖x - y‖ ^ β) := by
  obtain ⟨Cholder, hCholder, hholder⟩ := exists_hessian_holder_perturbation (E := E)
  have hC : 0 ≤ max (InterpolationSum.derivativeConstant (E := E) 2) Cholder :=
    (InterpolationSum.derivativeConstant_nonneg 2).trans (le_max_left _ _)
  refine ⟨max (InterpolationSum.derivativeConstant (E := E) 2) Cholder, hC, ?_⟩
  intro β hβ hβone c ρ a h B M hB hM hsize hscaled
  constructor
  · intro x
    exact (InterpolationSum.norm_secondFDeriv_perturbation_le h hB hsize x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)
  · intro x y
    apply (hholder β hβ hβone c ρ a h M hM hscaled x y).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
    apply mul_le_mul_of_nonneg_right _ hM
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) zero_le_two

/-- Helper for lem:polar-interpolation and eq:polar-objective: adding the
identity quadratic preserves the actual perturbation's Hölder Hessian modulus.
This bridge uses the norm-preserving Riesz identification of the Hessian and
the ordinary second Fréchet derivative and is reusable for arbitrary exponents. -/
theorem objective_hessian_holder
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : InterpolationSum.Geometry c ρ a) {H β : ℝ}
    (hholder : ∀ x y,
      ‖fderiv ℝ (fderiv ℝ (InterpolationSum.perturbation c ρ a)) x -
        fderiv ℝ (fderiv ℝ (InterpolationSum.perturbation c ρ a)) y‖ ≤ H * ‖x - y‖ ^ β)
    (x y : E) :
    ‖hessian (InterpolationSum.objective c ρ a) x -
      hessian (InterpolationSum.objective c ρ a) y‖ ≤ H * ‖x - y‖ ^ β := by
  rw [hessian_def, hessian_def, InterpolationSum.hessian_objective h,
    InterpolationSum.hessian_objective h, add_sub_add_left_eq_sub,
    ActualObjective.norm_hessian_sub_eq_secondFDeriv_sub]
  exact hholder x y

/-- Helper for lem:polar-interpolation and eq:polar-objective: the actual
quadratic-plus-explicit-correction objective is globally `β`-Hölder in its
operator-valued Hessian, with a cutoff constant independent of the exponent.
The geometric hypotheses also prove that this objective is globally `C²`.
This is a reusable general interpolation theorem. -/
theorem exists_contDiff_objective_hessian_holder :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      ∀ (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E),
        InterpolationSum.Geometry c ρ a → ∀ M : ℝ, 0 ≤ M →
        (∀ k, ‖a k‖ * (ρ k) ^ (-(1 + β)) ≤ M) →
        ContDiff ℝ 2 (InterpolationSum.objective c ρ a) ∧
          ∀ x y, ‖hessian (InterpolationSum.objective c ρ a) x -
            hessian (InterpolationSum.objective c ρ a) y‖ ≤
            2 * Cχ * M * ‖x - y‖ ^ β := by
  obtain ⟨Cχ, hCχ, hholder⟩ := exists_hessian_holder_perturbation (E := E)
  refine ⟨Cχ, hCχ, ?_⟩
  intro β hβ hβone c ρ a h M hM hbound
  refine ⟨InterpolationSum.contDiff_objective h, ?_⟩
  intro x y
  exact objective_hessian_holder h (hholder β hβ hβone c ρ a h M hM hbound) x y

/-- Helper for lem:polar-interpolation and eq:polar-interpolation-bound: the
source scales `ρ_k = κ τ_k` and `‖a_k‖ ≤ A τ_k^(1+β)` give a globally `C²`
explicit objective, Hessian perturbation of order `τ₀^β`, and a global
`β`-Hölder Hessian constant independent of the maximum scale `τ₀`.
This is a reusable interpolation interface for the generalized polar orbit. -/
theorem exists_objective_bounds_of_powerScale :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      ∀ (c : ℕ → E) (ρ : ℕ → ℝ) (a : ℕ → E) (τ : ℕ → ℝ) (κ A τ₀ : ℝ),
        InterpolationSum.Geometry c ρ a → 0 < κ → 0 ≤ A → 0 < τ₀ →
        (∀ k, 0 < τ k) → (∀ k, τ k ≤ τ₀) →
        (∀ k, ρ k = κ * τ k) → (∀ k, ‖a k‖ ≤ A * τ k ^ (1 + β)) →
        ContDiff ℝ 2 (InterpolationSum.objective c ρ a) ∧
        (∀ x, ‖hessian (InterpolationSum.objective c ρ a) x - 1‖ ≤
          Cχ * (A / κ) * τ₀ ^ β) ∧
        (∀ x y, ‖hessian (InterpolationSum.objective c ρ a) x -
          hessian (InterpolationSum.objective c ρ a) y‖ ≤
          2 * Cχ * (A * κ ^ (-(1 + β))) * ‖x - y‖ ^ β) := by
  obtain ⟨Cχ, hCχ, hbounds⟩ := exists_global_hessian_bounds (E := E)
  refine ⟨Cχ, hCχ, ?_⟩
  intro β hβ hβone c ρ a τ κ A τ₀ h hκ hA hτ₀ hτ hupper hradius hcoefficient
  have hB : 0 ≤ (A / κ) * τ₀ ^ β :=
    mul_nonneg (div_nonneg hA hκ.le) (Real.rpow_nonneg hτ₀.le _)
  have hM : 0 ≤ A * κ ^ (-(1 + β)) :=
    mul_nonneg hA (Real.rpow_nonneg hκ.le _)
  have hsize (k : ℕ) : ‖a k‖ / ρ k ≤ (A / κ) * τ₀ ^ β := by
    exact (coefficient_div_radius_le hκ (hτ k) (hradius k) (hcoefficient k)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hτ k).le (hupper k) hβ) (div_nonneg hA hκ.le))
  have hscaled (k : ℕ) : ‖a k‖ * (ρ k) ^ (-(1 + β)) ≤ A * κ ^ (-(1 + β)) :=
    coefficient_mul_radius_rpow_le hκ (hτ k) (hradius k) (hcoefficient k)
  obtain ⟨hsizeSum, hholder⟩ := hbounds β hβ hβone c ρ a h
    ((A / κ) * τ₀ ^ β) (A * κ ^ (-(1 + β))) hB hM hsize hscaled
  refine ⟨InterpolationSum.contDiff_objective h, ?_, ?_⟩
  · intro x
    rw [hessian_def, InterpolationSum.hessian_objective h, add_sub_cancel_left,
      norm_fderiv_gradient_eq_norm_fderiv_fderiv, mul_assoc]
    exact hsizeSum x
  · intro x y
    exact objective_hessian_holder h hholder x y

end DFP.Polar.General.InterpolationBounds

namespace DFP.Polar.General.HolderSharpness

/-- Helper for eq:counterexample-nonlipschitz: the quotient of the prescribed
residual scale `τ^(1+β)` by a step scale `U τ` to power `1+β'` has the exact
power `τ^(β-β')`. This identity is reusable for arbitrary real exponents. -/
theorem power_div_scaled_power (c U τ β β' : ℝ) (hU : 0 < U) (hτ : 0 < τ) :
    c * τ ^ (1 + β) / (U * τ) ^ (1 + β') =
      (c / U ^ (1 + β')) * τ ^ (β - β') := by
  have hexponent : (1 + β) - (1 + β') = β - β' := by
    ring
  rw [Real.mul_rpow hU.le hτ.le]
  calc
    c * τ ^ (1 + β) / (U ^ (1 + β') * τ ^ (1 + β')) =
        (c / U ^ (1 + β')) * (τ ^ (1 + β) / τ ^ (1 + β')) :=
      (div_mul_div_comm _ _ _ _).symm
    _ = (c / U ^ (1 + β')) * τ ^ (β - β') := by
      rw [← Real.rpow_sub hτ, hexponent]

/-- Helper for eq:counterexample-nonlipschitz: a lower residual bound at
scale `τ^(1+β)` and an upper positive step bound at scale `τ` give a lower
normalized residual bound with the exact power `τ^(β-β')`.
This is reusable support for arbitrary-exponent secant sharpness. -/
theorem powerScaleRatio_lower {a d τ c U β β' : ℝ}
    (hτ : 0 < τ) (hc : 0 ≤ c) (hU : 0 < U) (hexponent : 0 ≤ 1 + β')
    (hd : 0 < d) (ha : c * τ ^ (1 + β) ≤ a) (hstep : d ≤ U * τ) :
    (c / U ^ (1 + β')) * τ ^ (β - β') ≤ a / d ^ (1 + β') := by
  have haNonneg : 0 ≤ a := (mul_nonneg hc (Real.rpow_nonneg hτ.le _)).trans ha
  have hdenominator := Real.rpow_le_rpow hd.le hstep hexponent
  have hlargePositive := Real.rpow_pos_of_pos (mul_pos hU hτ) (1 + β')
  rw [← power_div_scaled_power c U τ β β' hU hτ]
  calc
    c * τ ^ (1 + β) / (U * τ) ^ (1 + β') ≤ a / (U * τ) ^ (1 + β') :=
      div_le_div_of_nonneg_right ha hlargePositive.le
    _ ≤ a / d ^ (1 + β') :=
      div_le_div_of_nonneg_left haNonneg (Real.rpow_pos_of_pos hd _) hdenominator

/-- Helper for eq:counterexample-nonlipschitz: an upper residual bound at
scale `τ^(1+β)` and a lower positive step bound at scale `τ` give the matching
upper normalized residual bound with power `τ^(β-β')`.
This is reusable support for arbitrary-exponent secant sharpness. -/
theorem powerScaleRatio_upper {a d τ C lower β β' : ℝ}
    (hτ : 0 < τ) (hC : 0 ≤ C) (hlower : 0 < lower) (hexponent : 0 ≤ 1 + β')
    (ha : a ≤ C * τ ^ (1 + β)) (hstep : lower * τ ≤ d) :
    a / d ^ (1 + β') ≤ (C / lower ^ (1 + β')) * τ ^ (β - β') := by
  have hd := (mul_pos hlower hτ).trans_le hstep
  have hdenominator := Real.rpow_le_rpow (mul_pos hlower hτ).le hstep hexponent
  rw [← power_div_scaled_power C lower τ β β' hlower hτ]
  calc
    a / d ^ (1 + β') ≤ (C * τ ^ (1 + β)) / d ^ (1 + β') :=
      div_le_div_of_nonneg_right ha (Real.rpow_pos_of_pos hd _).le
    _ ≤ (C * τ ^ (1 + β)) / (lower * τ) ^ (1 + β') :=
      div_le_div_of_nonneg_left (mul_nonneg hC (Real.rpow_nonneg hτ.le _))
        (Real.rpow_pos_of_pos (mul_pos hlower hτ) _) hdenominator

/-- Helper for eq:counterexample-nonlipschitz: positive scales tending to zero
make `τ^(β-β')` diverge for every strictly larger exponent `β'`.
This is a reusable real-power sharpness limit. -/
theorem sourcePower_tendsto_atTop {τ : ℕ → ℝ} (hτ : ∀ n, 0 < τ n)
    (hzero : Tendsto τ atTop (𝓝 0)) {β β' : ℝ} (hβ : β < β') :
    Tendsto (fun n ↦ τ n ^ (β - β')) atTop atTop := by
  have hwithin : Tendsto τ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Filter.Eventually.of_forall hτ⟩
  exact (tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hβ)).comp hwithin

/-- Helper for eq:counterexample-nonlipschitz: residuals bounded below by
`c τ^(1+β)` and positive steps bounded above by `U τ` force the normalized
residual ratio at every exponent `β' > β` to diverge.
This is reusable support for the secant-residual contradiction. -/
theorem powerScaleRatio_tendsto_atTop {a d τ : ℕ → ℝ} {c U β β' : ℝ}
    (hτ : ∀ n, 0 < τ n) (hzero : Tendsto τ atTop (𝓝 0))
    (hc : 0 < c) (hU : 0 < U) (hβ : β < β') (hexponent : 0 ≤ 1 + β')
    (hd : ∀ n, 0 < d n) (ha : ∀ n, c * τ n ^ (1 + β) ≤ a n)
    (hstep : ∀ n, d n ≤ U * τ n) :
    Tendsto (fun n ↦ a n / d n ^ (1 + β')) atTop atTop := by
  have hcoefficient : 0 < c / U ^ (1 + β') :=
    div_pos hc (Real.rpow_pos_of_pos hU _)
  have hpower := (sourcePower_tendsto_atTop hτ hzero hβ).const_mul_atTop hcoefficient
  apply tendsto_atTop_mono _ hpower
  intro n
  exact powerScaleRatio_lower (hτ n) hc.le hU hexponent (hd n) (ha n) (hstep n)

/-- Helper for eq:counterexample-nonlipschitz: on a convex set containing the
secant endpoints, a `C²` objective whose residual has size at least
`c τ^(1+β)` along steps of size at most `U τ` cannot have a `β'`-Hölder Hessian
for `β' > β`. The contradiction uses the existing Hölder-gradient remainder
estimate. This theorem is reusable for arbitrary generalized polar data. -/
theorem not_holderHessianOn_of_powerScaleResidual
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {S : Set E} (hf : ContDiff ℝ 2 f) (hS : Convex ℝ S)
    {x y : ℕ → E} (hx : ∀ n, x n ∈ S) (hy : ∀ n, y n ∈ S)
    {τ : ℕ → ℝ} (hτ : ∀ n, 0 < τ n) (hzero : Tendsto τ atTop (𝓝 0))
    {c U β β' : ℝ} (hc : 0 < c) (hU : 0 < U) (hβ : β < β') (hβ' : 0 ≤ β')
    (hstep : ∀ n, 0 < ‖y n - x n‖)
    (hupper : ∀ n, ‖y n - x n‖ ≤ U * τ n)
    (hresidual : ∀ n, c * τ n ^ (1 + β) ≤
      ‖gradient f (y n) - gradient f (x n) - hessian f (x n) (y n - x n)‖) :
    ¬ ∃ C ≥ 0, ∀ x ∈ S, ∀ y ∈ S,
      ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β' := by
  apply DFP.Polar.HolderSharpness.not_holderHessianOn_of_remainderRatio_tendsto
    hf hS hx hy hstep hβ'
  exact powerScaleRatio_tendsto_atTop hτ hzero hc hU hβ (add_nonneg zero_le_one hβ')
    hstep hresidual hupper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- Helper for eq:counterexample-nonlipschitz: at interpolation centers with
zero initial correction coefficient, the exact objective's secant-gradient
remainder equals the terminal coefficient. This is the same coefficient that
controls the objective's Hölder upper bound and is reusable for any pair of
interpolation centers. -/
theorem gradientRemainder_objective_centers
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : InterpolationSum.Geometry c ρ a) (i j : ℕ) (hzero : a i = 0) :
    gradient (InterpolationSum.objective c ρ a) (c j) -
        gradient (InterpolationSum.objective c ρ a) (c i) -
        hessian (InterpolationSum.objective c ρ a) (c i) (c j - c i) = a j := by
  rw [InterpolationSum.gradient_objective_center h j,
    InterpolationSum.gradient_objective_center h i, hessian_def,
    InterpolationSum.hessian_objective_center h i, one_apply_eq_self, hzero,
    add_zero]
  abel

/-- Helper for eq:counterexample-nonlipschitz: the actual explicit interpolated
objective fails every `β'`-Hölder Hessian bound with `β' > β` on a convex set
containing the selected center pairs, when their steps have scale `τ`, the
initial coefficients vanish, and the terminal coefficients are at least
`c₀ τ^(1+β)`. Thus the contradiction concerns the same objective and the same
coefficients as the interpolation upper bound. This is a reusable sharpness
interface for the generalized polar orbit. -/
theorem not_holderHessianOn_objective_of_powerScaleCoefficients
    {c : ℕ → E} {ρ : ℕ → ℝ} {a : ℕ → E}
    (h : InterpolationSum.Geometry c ρ a) {S : Set E} (hS : Convex ℝ S)
    {i j : ℕ → ℕ} (hi : ∀ n, c (i n) ∈ S) (hj : ∀ n, c (j n) ∈ S)
    {τ : ℕ → ℝ} (hτ : ∀ n, 0 < τ n) (hlimit : Tendsto τ atTop (𝓝 0))
    {c₀ U β β' : ℝ} (hc₀ : 0 < c₀) (hU : 0 < U) (hβ : β < β') (hβ' : 0 ≤ β')
    (hstep : ∀ n, 0 < ‖c (j n) - c (i n)‖)
    (hupper : ∀ n, ‖c (j n) - c (i n)‖ ≤ U * τ n)
    (hzero : ∀ n, a (i n) = 0)
    (hcoefficient : ∀ n, c₀ * τ n ^ (1 + β) ≤ ‖a (j n)‖) :
    ¬ ∃ C ≥ 0, ∀ x ∈ S, ∀ y ∈ S,
      ‖hessian (InterpolationSum.objective c ρ a) x -
        hessian (InterpolationSum.objective c ρ a) y‖ ≤ C * ‖x - y‖ ^ β' := by
  have hresidual (n : ℕ) : c₀ * τ n ^ (1 + β) ≤
      ‖gradient (InterpolationSum.objective c ρ a) (c (j n)) -
        gradient (InterpolationSum.objective c ρ a) (c (i n)) -
        hessian (InterpolationSum.objective c ρ a) (c (i n)) (c (j n) - c (i n))‖ := by
    rw [gradientRemainder_objective_centers h (i n) (j n) (hzero n)]
    exact hcoefficient n
  exact not_holderHessianOn_of_powerScaleResidual (InterpolationSum.contDiff_objective h)
    hS hi hj hτ hlimit hc₀ hU hβ hβ' hstep hupper hresidual

end DFP.Polar.General.HolderSharpness
