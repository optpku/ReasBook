/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.ExplicitCutoff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Pairwise.Basic

public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DFP.Polar.InterpolationBounds

/-- Helper for lem:polar-interpolation: a global third-derivative bound gives
a global Lipschitz bound for the ordinary second Fréchet derivative. -/
theorem norm_secondFDeriv_sub_le_of_thirdFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {B : ℝ} (hf : ContDiff ℝ 3 f)
    (hbound : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ B) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ B * ‖x - y‖ := by
  have horderFirst : (2 : WithTop ℕ∞) + 1 ≤ 3 := by
    norm_num
  have horderSecond : (1 : WithTop ℕ∞) + 1 ≤ 2 := by
    norm_num
  have hfirst : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right horderFirst
  have hsecond : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) :=
    hfirst.fderiv_right horderSecond
  have hboundOrdinary : ∀ z, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ B := by
    intro z
    calc
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ =
          ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fderiv ℝ f)) z‖ :=
        (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ (fderiv ℝ f))).symm
      _ = ‖iteratedFDeriv ℝ 2 (fderiv ℝ f) z‖ := norm_iteratedFDeriv_fderiv
      _ = ‖iteratedFDeriv ℝ 3 f z‖ := norm_iteratedFDeriv_fderiv
      _ ≤ B := hbound z
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (f := fderiv ℝ (fderiv ℝ f))
    (fun z _ ↦ hsecond.differentiable_one z) (fun z _ ↦ hboundOrdinary z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)

/-- Helper for lem:polar-interpolation: the smaller of two nonnegative
bounds does not exceed their geometric mean. -/
theorem min_le_sqrt_mul_sqrt {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    min A B ≤ Real.sqrt A * Real.sqrt B := by
  have hmin : 0 ≤ min A B := le_min hA hB
  have hproduct := mul_le_mul (min_le_left A B) (min_le_right A B) hmin hA
  have hsquare : min A B ^ 2 ≤ A * B := by
    simpa only [pow_two] using hproduct
  exact (Real.le_sqrt_of_sq_le hsquare).trans_eq (Real.sqrt_mul hA B)

/-- Helper for lem:polar-interpolation: the inverse three-halves radius
power is exactly the inverse radius times the square root of its inverse. -/
theorem rpow_neg_three_halves_eq_inv_mul_sqrt_inv {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (-3 / 2 : ℝ) = ρ⁻¹ * Real.sqrt (ρ⁻¹) := by
  have hexponent : (-3 / 2 : ℝ) = -1 + -(1 / 2) := by
    norm_num
  rw [hexponent, Real.rpow_add hρ, Real.rpow_neg_one,
    Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow]

/-- Helper for lem:polar-interpolation: the minimum of the scaled uniform
and Lipschitz moduli has the source's radius-three-halves square-root bound. -/
theorem min_inverse_scales_le_halfPower {ρ d : ℝ} (hρ : 0 < ρ) (hd : 0 ≤ d) :
    min (ρ⁻¹) ((ρ⁻¹) ^ 2 * d) ≤ ρ ^ (-3 / 2 : ℝ) * d ^ (1 / 2 : ℝ) := by
  have hinverse : 0 ≤ ρ⁻¹ := (inv_pos.mpr hρ).le
  have hscaled : 0 ≤ (ρ⁻¹) ^ 2 * d := mul_nonneg (sq_nonneg _) hd
  calc
    min (ρ⁻¹) ((ρ⁻¹) ^ 2 * d) ≤
        Real.sqrt (ρ⁻¹) * Real.sqrt ((ρ⁻¹) ^ 2 * d) :=
      min_le_sqrt_mul_sqrt hinverse hscaled
    _ = Real.sqrt (ρ⁻¹) * (ρ⁻¹ * Real.sqrt d) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hinverse]
    _ = (ρ⁻¹ * Real.sqrt (ρ⁻¹)) * Real.sqrt d := by
      ring
    _ = ρ ^ (-3 / 2 : ℝ) * d ^ (1 / 2 : ℝ) := by
      rw [rpow_neg_three_halves_eq_inv_mul_sqrt_inv hρ, Real.sqrt_eq_rpow d]

/-- Helper for lem:polar-interpolation: for a family with pairwise disjoint
function supports, at most two indices contribute to a difference of pointwise
finsums. A common modulus for each summand therefore gives twice that modulus
for the finsum. -/
theorem norm_finsum_sub_le_two_mul_modulus
    {ι X G : Type*} [NormedAddCommGroup G] (f : ι → X → G)
    (hdisjoint : Set.univ.PairwiseDisjoint (fun i ↦ Function.support (f i)))
    (modulus : X → X → ℝ) (hmodulus : ∀ x y, 0 ≤ modulus x y)
    (hlocal : ∀ i x y, ‖f i x - f i y‖ ≤ modulus x y) (x y : X) :
    ‖(∑ᶠ i, f i x) - ∑ᶠ i, f i y‖ ≤ 2 * modulus x y := by
  classical
  have hsubsingleton (z : X) : (Function.support (fun i ↦ f i z)).Subsingleton := by
    intro i hi j hj
    exact hdisjoint.elim_set (Set.mem_univ i) (Set.mem_univ j) z hi hj
  have hcard (z : X) : (hsubsingleton z).finite.toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hsubsingleton z ((hsubsingleton z).finite.mem_toFinset.mp hi)
      ((hsubsingleton z).finite.mem_toFinset.mp hj)
  let I := (hsubsingleton x).finite.toFinset ∪ (hsubsingleton y).finite.toFinset
  have hcardI : I.card ≤ 2 := by
    calc
      I.card ≤ (hsubsingleton x).finite.toFinset.card +
          (hsubsingleton y).finite.toFinset.card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add (hcard x) (hcard y)
      _ = 2 := rfl
  have hx : Function.support (fun i ↦ f i x) ⊆ I := by
    intro i hi
    exact Finset.mem_union_left _ ((hsubsingleton x).finite.mem_toFinset.mpr hi)
  have hy : Function.support (fun i ↦ f i y) ⊆ I := by
    intro i hi
    exact Finset.mem_union_right _ ((hsubsingleton y).finite.mem_toFinset.mpr hi)
  rw [finsum_eq_sum_of_support_subset _ hx, finsum_eq_sum_of_support_subset _ hy,
    ← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ I, (f i x - f i y)‖ ≤ ∑ i ∈ I, ‖f i x - f i y‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ I, modulus x y := Finset.sum_le_sum (fun i _ ↦ hlocal i x y)
    _ = (I.card : ℝ) * modulus x y := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * modulus x y :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcardI) (hmodulus x y)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for lem:polar-interpolation: every derivative of the exact affine
correction vanishes on and outside its support sphere, including the closed
boundary. -/
theorem iteratedFDeriv_correction_eq_zero_of_radius_le_norm_sub
    (n : ℕ) (c : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ) (hz : ρ ≤ ‖z - c‖) :
    iteratedFDeriv ℝ n (ExplicitCutoff.correction c ρ a) z = 0 := by
  have hzero : EqOn (iteratedFDeriv ℝ n (ExplicitCutoff.correction c ρ a))
      (fun _ ↦ 0) (Metric.closedBall c ρ)ᶜ := by
    intro y hy
    have hnot : y ∉ tsupport (ExplicitCutoff.correction c ρ a) := by
      intro hsupport
      exact hy (ExplicitCutoff.tsupport_correction_subset_closedBall c ρ a hρ hsupport)
    exact iteratedFDeriv_eq_zero_of_notMem_tsupport (ExplicitCutoff.correction c ρ a) n hnot
  have hcontinuous : Continuous (iteratedFDeriv ℝ n (ExplicitCutoff.correction c ρ a)) :=
    (ExplicitCutoff.contDiff_correction c ρ a).continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hclosure : z ∈ closure (Metric.closedBall c ρ)ᶜ := by
    rw [closure_compl, interior_closedBall c hρ.ne']
    simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_eq_norm, not_lt] using hz
  exact hzero.closure hcontinuous continuous_const hclosure

/-- Helper for lem:polar-interpolation: the Hessian of the exact affine
correction is zero on and outside its support sphere. -/
theorem hessian_correction_eq_zero_of_radius_le_norm_sub
    (c : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ) (hz : ρ ≤ ‖z - c‖) :
    fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) z = 0 := by
  apply norm_eq_zero.mp
  calc
    ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) z‖ =
        ‖iteratedFDeriv ℝ 1 (fderiv ℝ (ExplicitCutoff.correction c ρ a)) z‖ :=
      (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ (ExplicitCutoff.correction c ρ a))).symm
    _ = ‖iteratedFDeriv ℝ 2 (ExplicitCutoff.correction c ρ a) z‖ :=
      norm_iteratedFDeriv_fderiv
    _ = 0 := by
      rw [iteratedFDeriv_correction_eq_zero_of_radius_le_norm_sub 2 c ρ a z hρ hz,
        norm_zero]

/-- Helper for lem:polar-interpolation: the function support of each exact
correction's Hessian lies in the OPEN support ball. This includes zero Hessian
on the boundary while retaining the cutoff's CLOSED topological support. -/
theorem support_hessian_correction_subset_ball (c : E) (ρ : ℝ) (a : E) (hρ : 0 < ρ) :
    Function.support (fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a))) ⊆
      Metric.ball c ρ := by
  intro z hz
  by_contra houtside
  have hnorm : ρ ≤ ‖z - c‖ := by
    simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using houtside
  exact hz (hessian_correction_eq_zero_of_radius_le_norm_sub c ρ a z hρ hnorm)

variable [FiniteDimensional ℝ E]

/-- Helper for lem:polar-interpolation: the exact manuscript correction has
third derivative bounded by `C ‖a‖ / ρ²`, with `C` chosen before all correction
data. -/
theorem exists_norm_thirdFDeriv_correction_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : E) (ρ : ℝ) (a z : E), 0 < ρ →
      ‖iteratedFDeriv ℝ 3 (ExplicitCutoff.correction c ρ a) z‖ ≤ C * ‖a‖ / ρ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    ExplicitCutoff.exists_norm_iteratedFDeriv_correction_le (E := E) 3
  refine ⟨C, hC, ?_⟩
  intro c ρ a z hρ
  calc
    ‖iteratedFDeriv ℝ 3 (ExplicitCutoff.correction c ρ a) z‖ ≤
        C * ‖a‖ * ρ * (ρ⁻¹) ^ 3 := hbound c ρ a z hρ
    _ = C * ‖a‖ / ρ ^ 2 := by
      field_simp [hρ.ne']

/-- Helper for lem:polar-interpolation: the Hessian of every exact correction
is globally Lipschitz with constant `C ‖a‖ / ρ²`, uniformly in all correction
data. The Hessian is the ordinary second Fréchet derivative. -/
theorem exists_norm_hessian_correction_sub_le_lipschitz :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : E) (ρ : ℝ) (a x y : E), 0 < ρ →
      ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) x -
        fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) y‖ ≤
        (C * ‖a‖ / ρ ^ 2) * ‖x - y‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_thirdFDeriv_correction_le (E := E)
  refine ⟨C, hC, ?_⟩
  intro c ρ a x y hρ
  have hsmooth : ContDiff ℝ 3 (ExplicitCutoff.correction c ρ a) :=
    (ExplicitCutoff.contDiff_correction c ρ a).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  exact norm_secondFDeriv_sub_le_of_thirdFDeriv hsmooth (hbound c ρ a · hρ) x y

/-- Helper for lem:polar-interpolation: the Hessian difference satisfies the
source minimum of the uniform size bound and the Lipschitz bound, with one
constant chosen before all correction data. -/
theorem exists_norm_hessian_correction_sub_le_min :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : E) (ρ : ℝ) (a x y : E), 0 < ρ →
      ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) x -
        fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) y‖ ≤
        C * ‖a‖ * min (ρ⁻¹) ((ρ⁻¹) ^ 2 * ‖x - y‖) := by
  obtain ⟨Csize, hCsize, hsize⟩ :=
    ExplicitCutoff.exists_norm_secondFDeriv_correction_le (E := E)
  obtain ⟨Clip, hClip, hlip⟩ := exists_norm_hessian_correction_sub_le_lipschitz (E := E)
  have hC : 0 ≤ max (2 * Csize) Clip := hClip.trans (le_max_right _ _)
  refine ⟨max (2 * Csize) Clip, hC, ?_⟩
  intro c ρ a x y hρ
  rw [mul_min_of_nonneg _ _ (mul_nonneg hC (norm_nonneg a))]
  apply le_min
  · calc
      ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) x -
          fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) y‖ ≤
          ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) x‖ +
            ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) y‖ := norm_sub_le _ _
      _ ≤ Csize * ‖a‖ / ρ + Csize * ‖a‖ / ρ :=
        add_le_add (hsize c ρ a x hρ) (hsize c ρ a y hρ)
      _ = (2 * Csize) * ‖a‖ * ρ⁻¹ := by
        ring
      _ ≤ max (2 * Csize) Clip * ‖a‖ * ρ⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
          (inv_pos.mpr hρ).le
  · calc
      ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) x -
          fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) y‖ ≤
          (Clip * ‖a‖ / ρ ^ 2) * ‖x - y‖ := hlip c ρ a x y hρ
      _ = Clip * ‖a‖ * ((ρ⁻¹) ^ 2 * ‖x - y‖) := by
        rw [div_eq_mul_inv, inv_pow]
        ring
      _ ≤ max (2 * Csize) Clip * ‖a‖ * ((ρ⁻¹) ^ 2 * ‖x - y‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
          (mul_nonneg (sq_nonneg _) (norm_nonneg _))

/-- lem:polar-interpolation (single correction Hölder bound). For the exact
manuscript cutoff and affine correction, the Hessian, represented by the
ordinary second Fréchet derivative, is globally `1 / 2`-Hölder with coefficient
`Cχ ‖a‖ ρ^(-3/2)`. The fixed constant precedes all correction data. -/
theorem exists_norm_hessian_correction_sub_le :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (c : E) (ρ : ℝ) (a x y : E), 0 < ρ →
      ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) x -
        fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) y‖ ≤
        Cχ * ‖a‖ * ρ ^ (-3 / 2 : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨Cχ, hCχ, hmin⟩ := exists_norm_hessian_correction_sub_le_min (E := E)
  refine ⟨Cχ, hCχ, ?_⟩
  intro c ρ a x y hρ
  calc
    ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) x -
        fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction c ρ a)) y‖ ≤
        Cχ * ‖a‖ * min (ρ⁻¹) ((ρ⁻¹) ^ 2 * ‖x - y‖) := hmin c ρ a x y hρ
    _ ≤ Cχ * ‖a‖ * (ρ ^ (-3 / 2 : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (min_inverse_scales_le_halfPower hρ (norm_nonneg _))
        (mul_nonneg hCχ (norm_nonneg _))
    _ = Cχ * ‖a‖ * ρ ^ (-3 / 2 : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
      ring

/-- Helper for lem:polar-interpolation: conditional on pairwise disjoint
open support balls and a uniform scaled coefficient bound, the pointwise
finsum of exact correction Hessians has a uniform half-Hölder bound. This is
an estimate for the Hessian field; it does not assert a derivative identity
for an infinite objective sum. -/
theorem exists_norm_finsum_hessian_correction_sub_le {ι : Type*} :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (c : ι → E) (ρ : ι → ℝ) (a : ι → E) (M : ℝ),
      0 ≤ M → (∀ i, 0 < ρ i) →
      Set.univ.PairwiseDisjoint (fun i ↦ Metric.ball (c i) (ρ i)) →
      (∀ i, ‖a i‖ * (ρ i) ^ (-3 / 2 : ℝ) ≤ M) → ∀ x y : E,
      ‖(∑ᶠ i, fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) x) -
        ∑ᶠ i, fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) y‖ ≤
        2 * Cχ * M * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨Cχ, hCχ, hlocal⟩ := exists_norm_hessian_correction_sub_le (E := E)
  refine ⟨Cχ, hCχ, ?_⟩
  intro c ρ a M hM hρ hballs hscaled x y
  have hdisjoint : Set.univ.PairwiseDisjoint
      (fun i ↦ Function.support
        (fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))))) :=
    hballs.mono (fun i ↦ support_hessian_correction_subset_ball (c i) (ρ i) (a i) (hρ i))
  have hmodulus (u v : E) : 0 ≤ Cχ * M * ‖u - v‖ ^ (1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg hCχ hM) (Real.rpow_nonneg (norm_nonneg _) _)
  have hlocalUniform (i : ι) (u v : E) :
      ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) u -
        fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) v‖ ≤
        Cχ * M * ‖u - v‖ ^ (1 / 2 : ℝ) := by
    calc
      ‖fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) u -
          fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) v‖ ≤
          Cχ * ‖a i‖ * (ρ i) ^ (-3 / 2 : ℝ) * ‖u - v‖ ^ (1 / 2 : ℝ) :=
        hlocal (c i) (ρ i) (a i) u v (hρ i)
      _ = Cχ * (‖a i‖ * (ρ i) ^ (-3 / 2 : ℝ)) * ‖u - v‖ ^ (1 / 2 : ℝ) := by
        ring
      _ ≤ Cχ * M * ‖u - v‖ ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hscaled i) hCχ)
          (Real.rpow_nonneg (norm_nonneg _) _)
  have hsum := norm_finsum_sub_le_two_mul_modulus
    (fun i ↦ fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))))
    hdisjoint (fun u v ↦ Cχ * M * ‖u - v‖ ^ (1 / 2 : ℝ)) hmodulus hlocalUniform x y
  calc
    ‖(∑ᶠ i, fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) x) -
        ∑ᶠ i, fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) y‖ ≤
        2 * (Cχ * M * ‖x - y‖ ^ (1 / 2 : ℝ)) := hsum
    _ = 2 * Cχ * M * ‖x - y‖ ^ (1 / 2 : ℝ) := by
      ring

/-- Helper for lem:polar-interpolation: once an independent regularity proof
identifies an objective's Hessian with the pointwise finsum of the exact bump
Hessians, the disjoint-support estimate transfers to that objective. All
geometric and derivative-identification assumptions remain explicit. -/
theorem exists_norm_hessian_gluing_sub_le {ι : Type*} :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (c : ι → E) (ρ : ι → ℝ) (a : ι → E) (M : ℝ) (F : E → ℝ),
      0 ≤ M → (∀ i, 0 < ρ i) →
      Set.univ.PairwiseDisjoint (fun i ↦ Metric.ball (c i) (ρ i)) →
      (∀ i, ‖a i‖ * (ρ i) ^ (-3 / 2 : ℝ) ≤ M) →
      (∀ z, fderiv ℝ (fderiv ℝ F) z =
        ∑ᶠ i, fderiv ℝ (fderiv ℝ (ExplicitCutoff.correction (c i) (ρ i) (a i))) z) →
      ∀ x y, ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤
        2 * Cχ * M * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨Cχ, hCχ, hsum⟩ := exists_norm_finsum_hessian_correction_sub_le (E := E) (ι := ι)
  refine ⟨Cχ, hCχ, ?_⟩
  intro c ρ a M F hM hρ hballs hscaled hHessian x y
  rw [hHessian x, hHessian y]
  exact hsum c ρ a M hM hρ hballs hscaled x y

end DFP.Polar.InterpolationBounds
