module

public import ReasLib.Analysis.InnerProductSpace.Congruence

public section

noncomputable section

universe u

open scoped InnerProduct NNReal

namespace ContinuousLinearMap

/-- A nonnegative Loewner lower bound makes a continuous self-endomorphism positive. -/
theorem isPositive_of_loewner_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} {m : ℝ} (hm : 0 ≤ m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) : H.IsPositive := by
  have hpos : (H - m • (1 : E →L[ℝ] E)).IsPositive :=
    (le_def _ _).mp lower
  have hscalar : (m • (1 : E →L[ℝ] E)).IsPositive :=
    isPositive_one.smul_of_nonneg hm
  have hadd := hscalar.add hpos
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd

/-- A strict Loewner lower bound gives a quantitative inverse-distance estimate for the operator. -/
theorem antilipschitzWith_of_loewner_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) :
    AntilipschitzWith ((⟨m, hm.le⟩ : ℝ≥0)⁻¹) H := by
  have hpos : (H - m • (1 : E →L[ℝ] E)).IsPositive :=
    (le_def _ _).mp lower
  apply antilipschitz_of_forall_le_inner_map H (c := ⟨m, hm.le⟩) hm
  intro x
  have hnonneg := hpos.inner_nonneg_left x
  have hscalar : m * ‖x‖ ^ 2 ≤ @inner ℝ E _ (H x) x := by
    simpa [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, real_inner_self_eq_norm_sq] using hnonneg
  have hnorm : @inner ℝ E _ (H x) x ≤ ‖@inner ℝ E _ (H x) x‖ := le_abs_self _
  change ‖x‖ ^ 2 * m ≤ ‖@inner ℝ E _ (H x) x‖
  simpa [mul_comm] using hscalar.trans hnorm

/-- A strict Loewner lower bound makes a continuous self-endomorphism invertible. -/
theorem isUnit_of_loewner_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) : IsUnit H := by
  have hpos : (H - m • (1 : E →L[ℝ] E)).IsPositive :=
    (le_def _ _).mp lower
  apply isUnit_of_forall_le_norm_inner_map H (c := ⟨m, hm.le⟩) hm
  intro x
  have hnonneg := hpos.inner_nonneg_left x
  have hscalar : m * ‖x‖ ^ 2 ≤ @inner ℝ E _ (H x) x := by
    simpa [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, real_inner_self_eq_norm_sq] using hnonneg
  have hnorm : @inner ℝ E _ (H x) x ≤ ‖@inner ℝ E _ (H x) x‖ := le_abs_self _
  change ‖x‖ ^ 2 * m ≤ ‖@inner ℝ E _ (H x) x‖
  simpa [mul_comm] using hscalar.trans hnorm

/-- A strict Loewner lower bound forces the operator kernel to be trivial. -/
theorem ker_eq_bot_of_loewner_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) : LinearMap.ker (H : E →ₗ[ℝ] E) = ⊥ := by
  have hunit : IsUnit H := isUnit_of_loewner_lowerBound hm lower
  have hbij : Function.Bijective H := H.isUnit_iff_bijective.mp hunit
  exact LinearMap.ker_eq_bot.mpr hbij.1

/-- A strict Loewner lower bound forces the operator range to be all of the space. -/
theorem range_eq_top_of_loewner_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) : LinearMap.range (H : E →ₗ[ℝ] E) = ⊤ := by
  have hunit : IsUnit H := isUnit_of_loewner_lowerBound hm lower
  have hbij : Function.Bijective H := H.isUnit_iff_bijective.mp hunit
  exact LinearMap.range_eq_top.mpr hbij.2

/-- A strict Loewner lower bound packages the operator as a continuous linear equivalence. -/
noncomputable def continuousLinearEquiv_of_loewner_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective H
    (ker_eq_bot_of_loewner_lowerBound hm lower)
    (range_eq_top_of_loewner_lowerBound hm lower)

end ContinuousLinearMap
