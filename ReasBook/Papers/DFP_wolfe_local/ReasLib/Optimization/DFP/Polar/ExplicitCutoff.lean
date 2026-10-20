module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import ReasLib.Analysis.Calculus.ContDiff.SupportBounds
public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump

public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DFP.Polar.ExplicitCutoff

/-- Helper for v21 Section 4.1: explicit cutoff: the function η used in the
manuscript is mathlib's exponentially flat gluing function. -/
def eta : ℝ → ℝ := expNegInvGlue

/-- Helper for v21 Section 4.1: explicit cutoff: η is exactly `exp (-1 / t)`
for `t > 0`, and zero for `t ≤ 0`. -/
theorem eta_apply (t : ℝ) :
    eta t = if 0 < t then Real.exp (-1 / t) else 0 := by
  by_cases ht : 0 < t
  · simp [eta, expNegInvGlue, ht, not_le.mpr ht, div_eq_mul_inv]
  · simp [eta, expNegInvGlue, ht, not_lt.mp ht]

/-- Helper for v21 Section 4.1: explicit cutoff: η is nonnegative everywhere. -/
theorem eta_nonneg (t : ℝ) : 0 ≤ eta t := by
  exact expNegInvGlue.nonneg t

/-- Helper for v21 Section 4.1: explicit cutoff: η vanishes precisely on
`(-∞, 0]`. -/
theorem eta_eq_zero_iff (t : ℝ) : eta t = 0 ↔ t ≤ 0 := by
  exact expNegInvGlue.zero_iff_nonpos

/-- Helper for v21 Section 4.1: explicit cutoff: η is positive precisely on
`(0, ∞)`. -/
theorem eta_pos_iff (t : ℝ) : 0 < eta t ↔ 0 < t := by
  constructor
  · intro ht
    by_contra hnonpos
    have hz := (eta_eq_zero_iff t).mpr (not_lt.mp hnonpos)
    linarith
  · exact expNegInvGlue.pos_of_pos

/-- Helper for v21 Section 4.1: explicit cutoff: η is infinitely differentiable,
including at its junction at zero. -/
theorem contDiff_eta : ContDiff ℝ ∞ eta := by
  exact expNegInvGlue.contDiff

/-- Helper for v21 Section 4.1: explicit cutoff: all iterated derivatives of η
vanish on `(-∞, 0]`, including the flat junction at zero. -/
theorem iteratedFDeriv_eta_eq_zero (n : ℕ) {t : ℝ} (ht : t ≤ 0) :
    iteratedFDeriv ℝ n eta t = 0 := by
  have hnegative : EqOn (iteratedFDeriv ℝ n eta) (fun _ ↦ 0) (Iio 0) := by
    intro s hs
    have hevent : eta =ᶠ[𝓝 s] (fun _ ↦ 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with u hu
      exact (eta_eq_zero_iff u).mpr hu.le
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (hevent.iteratedFDeriv ℝ n).self_of_nhds
  have hcontinuous : Continuous (iteratedFDeriv ℝ n eta) :=
    contDiff_eta.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hclosure : t ∈ closure (Iio (0 : ℝ)) := by
    rwa [closure_Iio]
  exact hnegative.closure hcontinuous continuous_const hclosure

variable {E : Type*} [NormedAddCommGroup E]

/-- Helper for v21 Section 4.1: explicit cutoff: the denominator in the
manuscript's exact cutoff quotient. -/
def denominator (z : E) : ℝ :=
  eta (1 - ‖z‖ ^ 2) + eta (‖z‖ ^ 2 - 1 / 9)

/-- Helper for v21 Section 4.1: explicit cutoff: the two summands of the
cutoff denominator use the manuscript's exact arguments. -/
theorem denominator_apply (z : E) :
    denominator z = eta (1 - ‖z‖ ^ 2) + eta (‖z‖ ^ 2 - 1 / 9) := by
  rfl

/-- Helper for v21 Section 4.1: explicit cutoff: the denominator is strictly
positive everywhere, since the two positive intervals overlap. -/
theorem denominator_pos (z : E) : 0 < denominator z := by
  rw [denominator_apply]
  by_cases hz : ‖z‖ ^ 2 < 1
  · have hleft := (eta_pos_iff (1 - ‖z‖ ^ 2)).mpr (sub_pos.mpr hz)
    exact add_pos_of_pos_of_nonneg hleft (eta_nonneg _)
  · have hright : 0 < ‖z‖ ^ 2 - (1 / 9 : ℝ) := by
      linarith [not_lt.mp hz]
    exact add_pos_of_nonneg_of_pos (eta_nonneg _) ((eta_pos_iff _).mpr hright)

/-- Helper for v21 Section 4.1: explicit cutoff: the exact η quotient χ of
the manuscript, defined on any real inner product space. -/
def chi (z : E) : ℝ :=
  eta (1 - ‖z‖ ^ 2) / denominator z

/-- Helper for v21 Section 4.1: explicit cutoff: χ has exactly the displayed
quotient formula in the manuscript. -/
theorem chi_apply (z : E) :
    chi z = eta (1 - ‖z‖ ^ 2) /
      (eta (1 - ‖z‖ ^ 2) + eta (‖z‖ ^ 2 - 1 / 9)) := by
  rfl

/-- Helper for v21 Section 4.1: explicit cutoff: χ is nonnegative everywhere. -/
theorem chi_nonneg (z : E) : 0 ≤ chi z := by
  exact div_nonneg (eta_nonneg _) (denominator_pos z).le

/-- Helper for v21 Section 4.1: explicit cutoff: χ is at most one everywhere. -/
theorem chi_le_one (z : E) : chi z ≤ 1 := by
  apply (div_le_one (denominator_pos z)).mpr
  rw [denominator_apply]
  exact le_add_of_nonneg_right (eta_nonneg _)

/-- Helper for v21 Section 4.1: explicit cutoff: χ equals one on the closed
ball of radius `1 / 3`. -/
theorem chi_eq_one {z : E} (hz : ‖z‖ ≤ 1 / 3) : chi z = 1 := by
  have hsquare : ‖z‖ ^ 2 ≤ (1 / 9 : ℝ) := by
    nlinarith [norm_nonneg z]
  have hzero := (eta_eq_zero_iff (‖z‖ ^ 2 - 1 / 9)).mpr (sub_nonpos.mpr hsquare)
  have hpositive : 0 < 1 - ‖z‖ ^ 2 := by
    linarith
  rw [chi_apply, hzero, add_zero]
  exact div_self ((eta_pos_iff _).mpr hpositive).ne'

/-- Helper for v21 Section 4.1: explicit cutoff: χ equals one at the origin. -/
theorem chi_zero : chi (0 : E) = 1 := by
  apply chi_eq_one
  simp only [norm_zero]
  norm_num

/-- Helper for v21 Section 4.1: explicit cutoff: χ vanishes on and outside
the unit sphere, including the closed support boundary. -/
theorem chi_eq_zero {z : E} (hz : 1 ≤ ‖z‖) : chi z = 0 := by
  have hsquare : 1 ≤ ‖z‖ ^ 2 := by
    nlinarith
  have hzero := (eta_eq_zero_iff (1 - ‖z‖ ^ 2)).mpr (sub_nonpos.mpr hsquare)
  rw [chi_apply, hzero, zero_div]

/-- Helper for v21 Section 4.1: explicit cutoff: χ is strictly positive at
exactly the points of the open unit ball. -/
theorem chi_pos_iff (z : E) : 0 < chi z ↔ ‖z‖ < 1 := by
  constructor
  · intro hz
    by_contra hout
    have hzero := chi_eq_zero (not_lt.mp hout)
    linarith
  · intro hz
    have hsquare : 0 < 1 - ‖z‖ ^ 2 := by
      nlinarith [norm_nonneg z]
    exact div_pos ((eta_pos_iff _).mpr hsquare) (denominator_pos z)

/-- Helper for v21 Section 4.1: explicit cutoff: the function support of χ is
exactly the open unit ball. -/
theorem support_chi : Function.support (chi (E := E)) = Metric.ball 0 1 := by
  ext z
  rw [Function.mem_support, Metric.mem_ball, dist_zero_right]
  constructor
  · intro hz
    exact (chi_pos_iff z).mp ((chi_nonneg z).lt_of_ne' hz)
  · intro hz
    exact ((chi_pos_iff z).mpr hz).ne'

/-- Helper for v21 Section 4.1: explicit cutoff: χ is locally equal to one
throughout the open ball of radius `1 / 3`. -/
theorem chi_eventuallyEq_one {z : E} (hz : ‖z‖ < 1 / 3) :
    chi =ᶠ[𝓝 z] (fun _ : E ↦ (1 : ℝ)) := by
  have hnear : ∀ᶠ y in 𝓝 z, ‖y‖ < (1 / 3 : ℝ) :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hz
  filter_upwards [hnear] with y hy
  exact chi_eq_one hy.le

/-- Helper for v21 Section 4.1: explicit cutoff: χ is locally equal to zero
outside the closed unit ball. -/
theorem chi_eventuallyEq_zero {z : E} (hz : 1 < ‖z‖) :
    chi =ᶠ[𝓝 z] (fun _ : E ↦ (0 : ℝ)) := by
  have hnear : ∀ᶠ y in 𝓝 z, (1 : ℝ) < ‖y‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  filter_upwards [hnear] with y hy
  exact chi_eq_zero hy.le

variable [InnerProductSpace ℝ E]

/-- Helper for v21 Section 4.1: explicit cutoff: every positive-order
derivative of χ vanishes wherever χ is locally equal to one. -/
theorem iteratedFDeriv_chi_eq_zero_of_norm_lt (n : ℕ) (hn : n ≠ 0)
    {z : E} (hz : ‖z‖ < 1 / 3) : iteratedFDeriv ℝ n chi z = 0 := by
  simpa only [iteratedFDeriv_const_of_ne hn, Pi.zero_apply] using
    ((chi_eventuallyEq_one hz).iteratedFDeriv ℝ n).self_of_nhds

/-- Helper for v21 Section 4.1: explicit cutoff: every iterated derivative of
χ vanishes outside the closed unit ball. -/
theorem iteratedFDeriv_chi_eq_zero_of_one_lt_norm (n : ℕ)
    {z : E} (hz : 1 < ‖z‖) : iteratedFDeriv ℝ n chi z = 0 := by
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
    ((chi_eventuallyEq_zero hz).iteratedFDeriv ℝ n).self_of_nhds

/-- Helper for v21 Section 4.1: explicit cutoff: the cutoff denominator is
infinitely differentiable. -/
theorem contDiff_denominator : ContDiff ℝ ∞ (denominator (E := E)) := by
  exact (contDiff_eta.comp (contDiff_const.sub (contDiff_norm_sq ℝ))).add
    (contDiff_eta.comp ((contDiff_norm_sq ℝ).sub contDiff_const))

/-- v21 Section 4.1: explicit cutoff. The manuscript's exact quotient χ is
infinitely differentiable because its smooth denominator is positive everywhere. -/
theorem contDiff_chi : ContDiff ℝ ∞ (chi (E := E)) := by
  exact (contDiff_eta.comp (contDiff_const.sub (contDiff_norm_sq ℝ))).div
    contDiff_denominator (fun z ↦ (denominator_pos z).ne')

/-- Helper for v21 Section 4.1: explicit cutoff: every positive-order
derivative of χ vanishes on the closed inner ball, including its boundary. -/
theorem iteratedFDeriv_chi_eq_zero_of_norm_le (n : ℕ) (hn : n ≠ 0)
    {z : E} (hz : ‖z‖ ≤ 1 / 3) : iteratedFDeriv ℝ n chi z = 0 := by
  have hzero : EqOn (iteratedFDeriv ℝ n (chi (E := E))) (fun _ ↦ 0)
      (Metric.ball 0 (1 / 3)) := by
    intro y hy
    have hynorm : ‖y‖ < 1 / 3 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hy
    exact iteratedFDeriv_chi_eq_zero_of_norm_lt n hn hynorm
  have hcontinuous : Continuous (iteratedFDeriv ℝ n (chi (E := E))) :=
    contDiff_chi.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hradius : (1 / 3 : ℝ) ≠ 0 := by
    norm_num
  have hclosure : z ∈ closure (Metric.ball (0 : E) (1 / 3)) := by
    rw [closure_ball 0 hradius]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  exact hzero.closure hcontinuous continuous_const hclosure

/-- Helper for v21 Section 4.1: explicit cutoff: every iterated derivative of
χ vanishes on and outside the unit sphere, including its boundary. -/
theorem iteratedFDeriv_chi_eq_zero_of_one_le_norm (n : ℕ)
    {z : E} (hz : 1 ≤ ‖z‖) : iteratedFDeriv ℝ n chi z = 0 := by
  have hzero : EqOn (iteratedFDeriv ℝ n (chi (E := E))) (fun _ ↦ 0)
      (Metric.closedBall 0 1)ᶜ := by
    intro y hy
    have hynorm : 1 < ‖y‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
        using hy
    exact iteratedFDeriv_chi_eq_zero_of_one_lt_norm n hynorm
  have hcontinuous : Continuous (iteratedFDeriv ℝ n (chi (E := E))) :=
    contDiff_chi.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hclosure : z ∈ closure (Metric.closedBall (0 : E) 1)ᶜ := by
    rw [closure_compl, interior_closedBall 0 one_ne_zero]
    simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz
  exact hzero.closure hcontinuous continuous_const hclosure

/-- Helper for v21 Section 4.1: explicit cutoff: the first Fréchet derivative
of χ vanishes throughout the open inner ball. -/
theorem fderiv_chi_eq_zero {z : E} (hz : ‖z‖ < 1 / 3) :
    fderiv ℝ chi z = 0 := by
  simpa only [fderiv_const_apply] using (chi_eventuallyEq_one hz).fderiv_eq

/-- Helper for v21 Section 4.1: explicit cutoff: the Hessian of χ vanishes
throughout the open inner ball. -/
theorem secondFDeriv_chi_eq_zero {z : E} (hz : ‖z‖ < 1 / 3) :
    fderiv ℝ (fderiv ℝ chi) z = 0 := by
  have hevent : fderiv ℝ (chi (E := E)) =ᶠ[𝓝 z]
      (fun _ : E ↦ (0 : E →L[ℝ] ℝ)) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with y hy
    exact fderiv_chi_eq_zero hy
  simpa only [fderiv_const_apply] using hevent.fderiv_eq (𝕜 := ℝ)

/-- Helper for v21 Section 4.1: explicit cutoff: the topological support of χ
is exactly the closed unit ball. -/
theorem tsupport_chi : tsupport (chi (E := E)) = Metric.closedBall 0 1 := by
  rw [tsupport, support_chi, closure_ball (0 : E) one_ne_zero]

/-- Helper for v21 Section 4.1: explicit cutoff: in a finite-dimensional real
inner product space χ has compact support. -/
theorem hasCompactSupport_chi [FiniteDimensional ℝ E] :
    HasCompactSupport (chi (E := E)) := by
  rw [HasCompactSupport, tsupport_chi]
  exact isCompact_closedBall 0 1

/-- Helper for v21 Section 4.1: explicit cutoff: every order of derivative of
the fixed cutoff admits a global nonnegative norm bound in finite dimension. -/
theorem exists_norm_iteratedFDeriv_chi_le [FiniteDimensional ℝ E] (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E, ‖iteratedFDeriv ℝ n chi z‖ ≤ C := by
  exact hasCompactSupport_chi.exists_norm_iteratedFDeriv_le
    (contDiff_chi.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))

/-- Helper for v21 Section 4.1: explicit cutoff: the first Fréchet derivative
of the fixed cutoff has a global nonnegative norm bound in finite dimension. -/
theorem exists_norm_fderiv_chi_le [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E, ‖fderiv ℝ chi z‖ ≤ C := by
  exact hasCompactSupport_chi.exists_norm_fderiv_le
    (contDiff_chi.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))

/-- Helper for v21 Section 4.1: explicit cutoff: the Hessian of the fixed
cutoff has a global nonnegative operator-norm bound in finite dimension. -/
theorem exists_norm_secondFDeriv_chi_le [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E, ‖fderiv ℝ (fderiv ℝ chi) z‖ ≤ C := by
  exact hasCompactSupport_chi.exists_norm_secondFDeriv_le
    (contDiff_chi.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))

/-- Helper for v21 Section 4.1: explicit cutoff: the identity vector field
localized by the manuscript's fixed cutoff. -/
def cutoffIdentity (z : E) : E := chi z • z

/-- Helper for v21 Section 4.1: explicit cutoff: evaluation of the localized
identity vector field. -/
theorem cutoffIdentity_apply (z : E) : cutoffIdentity z = chi z • z := by
  rfl

/-- Helper for v21 Section 4.1: explicit cutoff: the localized identity
vector field is infinitely differentiable. -/
theorem contDiff_cutoffIdentity : ContDiff ℝ ∞ (cutoffIdentity (E := E)) := by
  exact contDiff_chi.smul contDiff_id

/-- Helper for v21 Section 4.1: explicit cutoff: the localized identity
vector field has compact support in finite dimension. -/
theorem hasCompactSupport_cutoffIdentity [FiniteDimensional ℝ E] :
    HasCompactSupport (cutoffIdentity (E := E)) := by
  exact hasCompactSupport_chi.smul_right

/-- Helper for v21 Section 4.1: explicit cutoff: each derivative of the fixed
localized identity vector field has a global nonnegative norm bound. -/
theorem exists_norm_iteratedFDeriv_cutoffIdentity_le [FiniteDimensional ℝ E] (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E, ‖iteratedFDeriv ℝ n cutoffIdentity z‖ ≤ C := by
  exact hasCompactSupport_cutoffIdentity.exists_norm_iteratedFDeriv_le
    (contDiff_cutoffIdentity.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))

/-- Helper for v21 Section 4.1: explicit cutoff: the unit-scale affine
correction with linear coefficient `a`. -/
def unitCorrection (a z : E) : ℝ := chi z * inner ℝ a z

/-- Helper for v21 Section 4.1: explicit cutoff: evaluation of the unit-scale
linear correction. -/
theorem unitCorrection_apply (a z : E) : unitCorrection a z = chi z * inner ℝ a z := by
  rfl

/-- Helper for v21 Section 4.1: explicit cutoff: the unit correction is the
linear functional `innerSL ℝ a` applied to the fixed localized identity. -/
theorem unitCorrection_eq_comp (a : E) :
    unitCorrection a = (innerSL ℝ a) ∘ cutoffIdentity := by
  funext z
  rw [Function.comp_apply, unitCorrection_apply, cutoffIdentity_apply,
    innerSL_apply_apply, inner_smul_right]

/-- Helper for v21 Section 4.1: explicit cutoff: each unit-scale affine
correction is infinitely differentiable. -/
theorem contDiff_unitCorrection (a : E) : ContDiff ℝ ∞ (unitCorrection a) := by
  rw [unitCorrection_eq_comp]
  exact (innerSL ℝ a).contDiff.comp contDiff_cutoffIdentity

/-- Helper for v21 Section 4.1: explicit cutoff: the derivative norm of the
unit correction is bounded by `‖a‖` times that of the fixed localized identity. -/
theorem norm_iteratedFDeriv_unitCorrection_le (n : ℕ) (a z : E) :
    ‖iteratedFDeriv ℝ n (unitCorrection a) z‖ ≤
      ‖a‖ * ‖iteratedFDeriv ℝ n cutoffIdentity z‖ := by
  rw [unitCorrection_eq_comp, ← innerSL_apply_norm (𝕜 := ℝ) a]
  exact (innerSL ℝ a).norm_iteratedFDeriv_comp_left
    contDiff_cutoffIdentity.contDiffAt
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

/-- Helper for v21 Section 4.1: explicit cutoff: the manuscript's affine
correction centered at `c`, with radius `ρ` and coefficient `a`. -/
def correction (c : E) (ρ : ℝ) (a : E) : E → ℝ :=
  AffineBump.scaledLinearBump chi c ρ a

/-- Helper for v21 Section 4.1: explicit cutoff: the scaled affine correction
has exactly the formula in `eq:polar-objective`. -/
theorem correction_apply (c : E) (ρ : ℝ) (a z : E) :
    correction c ρ a z = chi (ρ⁻¹ • (z - c)) * inner ℝ a (z - c) := by
  exact AffineBump.scaledLinearBump_apply chi c ρ a z

/-- Helper for v21 Section 4.1: explicit cutoff: every scaled affine
correction is infinitely differentiable. -/
theorem contDiff_correction (c : E) (ρ : ℝ) (a : E) :
    ContDiff ℝ ∞ (correction c ρ a) := by
  exact AffineBump.contDiff_scaledLinearBump chi contDiff_chi c ρ a

/-- Helper for v21 Section 4.1: explicit cutoff: translation and positive
rescaling divide the argument's norm by the radius. -/
theorem norm_rescale (c z : E) (ρ : ℝ) (hρ : 0 < ρ) :
    ‖ρ⁻¹ • (z - c)‖ = ‖z - c‖ / ρ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), div_eq_inv_mul]

/-- Helper for v21 Section 4.1: explicit cutoff: the topological support of a
scaled affine correction lies in its CLOSED radius-`ρ` ball. -/
theorem tsupport_correction_subset_closedBall (c : E) (ρ : ℝ) (a : E) (hρ : 0 < ρ) :
    tsupport (correction c ρ a) ⊆ Metric.closedBall c ρ := by
  have hscaled : Continuous (fun z : E ↦ ρ⁻¹ • (z - c)) :=
    continuous_const.smul (continuous_id.sub continuous_const)
  have hpreimage := tsupport_comp_subset_preimage (chi (E := E)) hscaled
  have hproduct : tsupport (correction c ρ a) ⊆
      tsupport (fun z : E ↦ chi (ρ⁻¹ • (z - c))) := by
    rw [funext (correction_apply c ρ a)]
    exact tsupport_mul_subset_left
  intro z hz
  have hcutoff : ρ⁻¹ • (z - c) ∈ tsupport (chi (E := E)) :=
    hpreimage (hproduct hz)
  rw [tsupport_chi, Metric.mem_closedBall, dist_zero_right, norm_rescale c z ρ hρ]
    at hcutoff
  have hnorm := (div_le_one hρ).mp hcutoff
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hnorm

/-- Helper for v21 Section 4.1: explicit cutoff: the affine correction is a
translated and rescaled unit correction, with amplitude factor `ρ`. -/
theorem correction_eq_rescale (c : E) (ρ : ℝ) (a : E) (hρ : ρ ≠ 0) :
    correction c ρ a = fun z ↦ ρ * unitCorrection a (ρ⁻¹ • (z - c)) := by
  funext z
  rw [correction_apply, unitCorrection_apply, inner_smul_right]
  calc
    chi (ρ⁻¹ • (z - c)) * inner ℝ a (z - c) =
        (ρ * ρ⁻¹) * (chi (ρ⁻¹ • (z - c)) * inner ℝ a (z - c)) := by
      rw [mul_inv_cancel₀ hρ, one_mul]
    _ = ρ * (chi (ρ⁻¹ • (z - c)) * (ρ⁻¹ * inner ℝ a (z - c))) := by
      ring

/-- Helper for v21 Section 4.1: explicit cutoff: differentiation of the
scaled affine correction contributes one factor `ρ⁻¹` per derivative. -/
theorem iteratedFDeriv_correction (n : ℕ) (c : E) (ρ : ℝ) (a z : E) (hρ : ρ ≠ 0) :
    iteratedFDeriv ℝ n (correction c ρ a) z =
      (ρ * (ρ⁻¹) ^ n) • iteratedFDeriv ℝ n (unitCorrection a) (ρ⁻¹ • (z - c)) := by
  have hunit : ContDiff ℝ n (unitCorrection a) :=
    (contDiff_unitCorrection a).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hscaled : ContDiff ℝ n (fun y : E ↦ unitCorrection a (ρ⁻¹ • (y - c))) :=
    hunit.comp ((contDiff_id.sub contDiff_const).const_smul ρ⁻¹)
  have hrescale : correction c ρ a =
      fun y ↦ ρ • unitCorrection a (ρ⁻¹ • (y - c)) := by
    simpa only [smul_eq_mul] using correction_eq_rescale c ρ a hρ
  rw [hrescale, iteratedFDeriv_const_smul_apply' hscaled.contDiffAt,
    iteratedFDeriv_comp_sub (𝕜 := ℝ)
      (f := fun y : E ↦ unitCorrection a (ρ⁻¹ • y)) n c z,
    iteratedFDeriv_comp_const_smul ρ⁻¹ hunit, smul_smul]

/-- Helper for v21 Section 4.1: explicit cutoff: fixed derivative constants
control all affine corrections, independently of their center, radius, and
coefficient. This gives the source scaling `‖D^n ψ‖ ≤ Cₙ ‖a‖ ρ^(1-n)`. -/
theorem exists_norm_iteratedFDeriv_correction_le [FiniteDimensional ℝ E] (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : E) (ρ : ℝ) (a z : E), 0 < ρ →
      ‖iteratedFDeriv ℝ n (correction c ρ a) z‖ ≤ C * ‖a‖ * ρ * (ρ⁻¹) ^ n := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_cutoffIdentity_le (E := E) n
  refine ⟨C, hC, ?_⟩
  intro c ρ a z hρ
  have hunit : ‖iteratedFDeriv ℝ n (unitCorrection a) (ρ⁻¹ • (z - c))‖ ≤ ‖a‖ * C :=
    (norm_iteratedFDeriv_unitCorrection_le n a _).trans
      (mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _))
  have hfactor : 0 < ρ * (ρ⁻¹) ^ n :=
    mul_pos hρ (pow_pos (inv_pos.mpr hρ) n)
  rw [iteratedFDeriv_correction n c ρ a z hρ.ne', norm_smul,
    Real.norm_eq_abs, abs_of_pos hfactor]
  calc
    (ρ * (ρ⁻¹) ^ n) * ‖iteratedFDeriv ℝ n (unitCorrection a) (ρ⁻¹ • (z - c))‖ ≤
        (ρ * (ρ⁻¹) ^ n) * (‖a‖ * C) :=
      mul_le_mul_of_nonneg_left hunit hfactor.le
    _ = C * ‖a‖ * ρ * (ρ⁻¹) ^ n := by
      ring

/-- Helper for v21 Section 4.1: explicit cutoff: the all-order scaled
correction bound in the manuscript's integer-power notation. -/
theorem exists_norm_iteratedFDeriv_correction_le_zpow [FiniteDimensional ℝ E] (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : E) (ρ : ℝ) (a z : E), 0 < ρ →
      ‖iteratedFDeriv ℝ n (correction c ρ a) z‖ ≤ C * ‖a‖ * ρ ^ ((1 : ℤ) - n) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_correction_le (E := E) n
  refine ⟨C, hC, ?_⟩
  intro c ρ a z hρ
  have hscale : ρ * (ρ⁻¹) ^ n = ρ ^ ((1 : ℤ) - n) := by
    rw [zpow_sub₀ hρ.ne', zpow_one, zpow_natCast, div_eq_mul_inv, inv_pow]
  calc
    ‖iteratedFDeriv ℝ n (correction c ρ a) z‖ ≤ C * ‖a‖ * ρ * (ρ⁻¹) ^ n :=
      hbound c ρ a z hρ
    _ = C * ‖a‖ * ρ ^ ((1 : ℤ) - n) := by
      rw [mul_assoc (C * ‖a‖), hscale]

/-- Helper for v21 Section 4.1: explicit cutoff: the first derivative of the
affine correction has the two terms displayed in the source proof. -/
theorem fderiv_correction (c : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ) :
    fderiv ℝ (correction c ρ a) z =
      chi (ρ⁻¹ • (z - c)) • innerSL ℝ a +
        (ρ⁻¹ * inner ℝ a (z - c)) • fderiv ℝ chi (ρ⁻¹ • (z - c)) := by
  exact AffineBump.fderiv_scaledLinearBump chi
    (contDiff_chi.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) c ρ a z hρ

/-- Helper for v21 Section 4.1: explicit cutoff: the Hessian of the affine
correction has the two cross terms and the second-cutoff-derivative term of
the source proof. -/
theorem secondFDeriv_correction_apply (c : E) (ρ : ℝ) (a z v u : E) (hρ : 0 < ρ) :
    fderiv ℝ (fderiv ℝ (correction c ρ a)) z v u =
      ρ⁻¹ * (fderiv ℝ chi (ρ⁻¹ • (z - c)) v * inner ℝ a u +
        inner ℝ a v * fderiv ℝ chi (ρ⁻¹ • (z - c)) u) +
        ρ⁻¹ ^ 2 * inner ℝ a (z - c) *
          fderiv ℝ (fderiv ℝ chi) (ρ⁻¹ • (z - c)) v u := by
  exact AffineBump.secondFDeriv_scaledLinearBump_apply chi
    (contDiff_chi.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    c ρ a z v u hρ

/-- Helper for v21 Section 4.1: explicit cutoff: the first derivative of χ
vanishes at the origin. -/
theorem fderiv_chi_zero : fderiv ℝ (chi (E := E)) 0 = 0 := by
  apply fderiv_chi_eq_zero
  simp only [norm_zero]
  norm_num

/-- Helper for v21 Section 4.1: explicit cutoff: the affine correction has
zero value at its designated center. -/
theorem correction_apply_center (c : E) (ρ : ℝ) (a : E) : correction c ρ a c = 0 := by
  rw [correction_apply, sub_self, inner_zero_right, mul_zero]

/-- Helper for v21 Section 4.1: explicit cutoff: the affine correction has
exactly its prescribed first derivative at the center. -/
theorem fderiv_correction_center (c : E) (ρ : ℝ) (a : E) (hρ : 0 < ρ) :
    fderiv ℝ (correction c ρ a) c = innerSL ℝ a := by
  rw [fderiv_correction c ρ a c hρ]
  simp only [sub_self, smul_zero, chi_zero, one_smul, inner_zero_right,
    mul_zero, zero_smul, add_zero]

/-- Helper for v21 Section 4.1: explicit cutoff: the affine correction has
zero Hessian at its designated center. -/
theorem secondFDeriv_correction_center (c : E) (ρ : ℝ) (a : E) (hρ : 0 < ρ) :
    fderiv ℝ (fderiv ℝ (correction c ρ a)) c = 0 := by
  ext v u
  rw [secondFDeriv_correction_apply c ρ a c v u hρ]
  simp only [sub_self, smul_zero, fderiv_chi_zero, zero_apply, inner_zero_right,
    zero_mul, mul_zero, add_zero]

/-- Helper for v21 Section 4.1: explicit cutoff: the global Hessian bound of
each affine correction is `C ‖a‖ / ρ`, with `C` chosen before all correction
parameters. -/
theorem exists_norm_secondFDeriv_correction_le [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : E) (ρ : ℝ) (a z : E), 0 < ρ →
      ‖fderiv ℝ (fderiv ℝ (correction c ρ a)) z‖ ≤ C * ‖a‖ / ρ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_correction_le (E := E) 2
  refine ⟨C, hC, ?_⟩
  intro c ρ a z hρ
  calc
    ‖fderiv ℝ (fderiv ℝ (correction c ρ a)) z‖ =
        ‖iteratedFDeriv ℝ 1 (fderiv ℝ (correction c ρ a)) z‖ :=
      (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ (correction c ρ a))).symm
    _ = ‖iteratedFDeriv ℝ 2 (correction c ρ a) z‖ := norm_iteratedFDeriv_fderiv
    _ ≤ C * ‖a‖ * ρ * (ρ⁻¹) ^ 2 := hbound c ρ a z hρ
    _ = C * ‖a‖ / ρ := by
      field_simp

end DFP.Polar.ExplicitCutoff
