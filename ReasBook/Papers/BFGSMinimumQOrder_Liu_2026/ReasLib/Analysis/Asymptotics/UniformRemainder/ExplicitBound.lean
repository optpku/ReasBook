module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.ModulusScale
public import ReasLib.Analysis.Asymptotics.UniformRemainder.ModulusOrderDrop
public import ReasLib.Analysis.Asymptotics.UniformRemainder
import all ReasLib.Analysis.Asymptotics.UniformRemainder

public section

open Filter
open scoped Topology

namespace Asymptotics.IsUniformRemainderModulusOn

universe u v

/-- A common explicit natural-power bound is an `IsUniformRemainderOn` estimate
with the corresponding real exponent. -/
theorem isUniformRemainderOn_of_explicit_bound
    {Theta : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Theta -> ℝ -> E} {s : Set Theta} {n : ℕ} {C delta : ℝ}
    (hdelta : 0 < delta)
    (hbound : ∀ theta ∈ s, ∀ epsilon : ℝ, |epsilon| < delta ->
      ‖R theta epsilon‖ ≤ C * |epsilon| ^ (n + 1)) :
    Asymptotics.IsUniformRemainderOn R s C ((n + 1 : ℕ) : ℝ) := by
  have hboundReal : ∀ theta ∈ s, ∀ epsilon : ℝ, |epsilon| < delta ->
      ‖R theta epsilon‖ ≤ C * |epsilon| ^ ((n + 1 : ℕ) : ℝ) := by
    intro theta htheta epsilon hepsilon
    have hNat := hbound theta htheta epsilon hepsilon
    have hexponent : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
    have hn_nonneg : (0 : ℝ) ≤ n := by positivity
    have hone_nonneg : (0 : ℝ) ≤ 1 := by positivity
    rw [hexponent, Real.rpow_add_of_nonneg (abs_nonneg epsilon) hn_nonneg
      hone_nonneg, Real.rpow_natCast, Real.rpow_one]
    rw [pow_succ] at hNat
    exact hNat
  exact ⟨delta, hdelta, hboundReal⟩

/-- A positive-increment natural-power bound extends to a uniform remainder when
the remainder vanishes at the base point. -/
theorem isUniformRemainderOn_of_pos_explicit_bound
    {Theta : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Theta -> ℝ -> E} {s : Set Theta} {n : ℕ} {C delta : ℝ}
    (hdelta : 0 < delta)
    (hzero : ∀ theta ∈ s, R theta 0 = 0)
    (hbound : ∀ theta ∈ s, ∀ epsilon : ℝ, 0 < |epsilon| ->
      |epsilon| < delta ->
      ‖R theta epsilon‖ ≤ C * |epsilon| ^ (n + 1)) :
    Asymptotics.IsUniformRemainderOn R s C ((n + 1 : ℕ) : ℝ) := by
  have hboundReal : ∀ theta ∈ s, ∀ epsilon : ℝ, |epsilon| < delta ->
      ‖R theta epsilon‖ ≤ C * |epsilon| ^ ((n + 1 : ℕ) : ℝ) := by
    intro theta htheta epsilon hepsilon
    by_cases hepsilon_zero : epsilon = 0
    · subst epsilon
      have hexponent_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [hzero theta htheta, norm_zero, abs_zero,
        Real.zero_rpow hexponent_ne, mul_zero]
    · have hNat := hbound theta htheta epsilon
        (abs_pos.mpr hepsilon_zero) hepsilon
      have hexponent : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      have hn_nonneg : (0 : ℝ) ≤ n := by positivity
      have hone_nonneg : (0 : ℝ) ≤ 1 := by positivity
      rw [hexponent, Real.rpow_add_of_nonneg (abs_nonneg epsilon) hn_nonneg
        hone_nonneg, Real.rpow_natCast, Real.rpow_one]
      rw [pow_succ] at hNat
      exact hNat
  exact ⟨delta, hdelta, hboundReal⟩

/-- A common explicit natural-power bound produces the canonical lower-order
uniform remainder estimate and the canonical lower-order modulus's linear scale
estimate. -/
theorem exists_natPow_modulus_of_explicit_bound
    {Theta : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Theta -> ℝ -> E} {s : Set Theta} {n : ℕ} {C delta : ℝ}
    (hdelta : 0 < delta) (hC : 0 ≤ C)
    (hbound : ∀ theta ∈ s, ∀ epsilon : ℝ, |epsilon| < delta ->
      ‖R theta epsilon‖ ≤ C * |epsilon| ^ (n + 1)) :
    ∃ eta0 > 0,
      Asymptotics.IsUniformRemainderOn R s C ((n + 1 : ℕ) : ℝ) ∧
        ∀ eta ∈ Set.Ioc 0 eta0,
          uniformRemainderModulus R s (n : ℝ) eta ≤ C * eta := by
  have hUniform : Asymptotics.IsUniformRemainderOn R s C ((n + 1 : ℕ) : ℝ) := by
    exact isUniformRemainderOn_of_explicit_bound hdelta hbound
  obtain ⟨eta0, heta0, hmodulus⟩ :=
    exists_uniformRemainderModulus_natCast_le_mul hC hUniform
  exact ⟨eta0, heta0, hUniform, hmodulus⟩

/-- A common nonnegative order-`n + 1` bound is little-o at order `n` for the
same parameter set. -/
theorem isLittleO_of_explicit_natPow_bound
    {Theta : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Theta -> ℝ -> E} {s : Set Theta} {n : ℕ} {C delta : ℝ}
    (hdelta : 0 < delta) (hC : 0 ≤ C)
    (hbound : ∀ theta ∈ s, ∀ epsilon : ℝ, |epsilon| < delta ->
      ‖R theta epsilon‖ ≤ C * |epsilon| ^ (n + 1)) :
    (fun z : Theta × ℝ ↦ R z.1 z.2) =o[
      Filter.principal s ×ˢ 𝓝 0]
      (fun z : Theta × ℝ ↦ |z.2| ^ (n : ℝ)) := by
  rw [Asymptotics.IsUniformRemainderOn.isLittleO_iff]
  intro K hK
  have hden : 0 < C + 1 := by linarith
  have hscale : 0 < K / (C + 1) := div_pos hK hden
  refine ⟨min delta (K / (C + 1)), lt_min hdelta hscale, ?_⟩
  intro theta htheta epsilon hepsilon
  by_cases hepsilon_zero : epsilon = 0
  · subst epsilon
    have hzero_increment : |(0 : ℝ)| < delta := by simpa using hdelta
    have h0 := hbound theta htheta 0 hzero_increment
    have hnorm : ‖R theta 0‖ ≤ 0 := by simpa using h0
    have hpow_zero_nonneg : 0 ≤ (0 : ℝ) ^ (n : ℝ) := by positivity
    rw [abs_zero]
    exact hnorm.trans (mul_nonneg hK.le hpow_zero_nonneg)
  · have hepsilon_pos : 0 < |epsilon| := abs_pos.mpr hepsilon_zero
    have hepsilon_delta : |epsilon| < delta :=
      lt_of_lt_of_le hepsilon (min_le_left delta (K / (C + 1)))
    have hepsilon_scale : |epsilon| < K / (C + 1) :=
      lt_of_lt_of_le hepsilon (min_le_right delta (K / (C + 1)))
    have hmul : |epsilon| * (C + 1) < K :=
      (lt_div_iff₀ hden).mp hepsilon_scale
    have hC_le : C ≤ C + 1 := by linarith
    have hCscale : C * |epsilon| ≤ (C + 1) * |epsilon| :=
      mul_le_mul_of_nonneg_right hC_le (abs_nonneg epsilon)
    have hscale_comm : (C + 1) * |epsilon| < K := by
      simpa [mul_comm] using hmul
    have hCepsilon : C * |epsilon| ≤ K := by
      exact hCscale.trans (le_of_lt hscale_comm)
    have hNat := hbound theta htheta epsilon hepsilon_delta
    have hpow_nonneg : 0 ≤ |epsilon| ^ n :=
      pow_nonneg (abs_nonneg epsilon) n
    have hprod : C * (|epsilon| ^ n * |epsilon|) ≤ K * |epsilon| ^ n := by
      calc
        C * (|epsilon| ^ n * |epsilon|) = (C * |epsilon|) * |epsilon| ^ n := by ring
        _ ≤ K * |epsilon| ^ n := mul_le_mul_of_nonneg_right hCepsilon hpow_nonneg
    have hbound_factor : ‖R theta epsilon‖ ≤ C * (|epsilon| ^ n * |epsilon|) := by
      simpa only [pow_succ] using hNat
    have hfactor_rpow : K * |epsilon| ^ n = K * |epsilon| ^ (n : ℝ) := by
      rw [Real.rpow_natCast]
    calc
      ‖R theta epsilon‖ ≤ C * (|epsilon| ^ n * |epsilon|) := hbound_factor
      _ ≤ K * |epsilon| ^ n := hprod
      _ = K * |epsilon| ^ (n : ℝ) := hfactor_rpow

/-- A common explicit order-`n + 1` estimate yields both the canonical order-`n`
modulus and its linear-in-radius bound on one common positive interval. -/
theorem exists_natPow_modulus_spec_of_explicit_bound
    {Theta : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Theta -> ℝ -> E} {s : Set Theta} {n : ℕ} {C delta : ℝ}
    (hdelta : 0 < delta) (hC : 0 ≤ C)
    (hbound : ∀ theta ∈ s, ∀ epsilon : ℝ, |epsilon| < delta ->
      ‖R theta epsilon‖ ≤ C * |epsilon| ^ (n + 1)) :
    ∃ eta0 > 0,
      Asymptotics.IsUniformRemainderOn R s C ((n + 1 : ℕ) : ℝ) ∧
        Asymptotics.IsUniformRemainderModulusOn R s (n : ℝ) eta0
          (Asymptotics.uniformRemainderModulus R s (n : ℝ)) ∧
        ∀ eta ∈ Set.Ioc 0 eta0,
          Asymptotics.uniformRemainderModulus R s (n : ℝ) eta ≤ C * eta := by
  have hUniform := isUniformRemainderOn_of_explicit_bound hdelta hbound
  have hLittle := isLittleO_of_explicit_natPow_bound hdelta hC hbound
  obtain ⟨etaMod, hetaMod, hMod⟩ :=
    Asymptotics.IsUniformRemainderModulusOn.of_isLittleO R s (n : ℝ) hLittle
  obtain ⟨etaBound, hetaBound, hBound⟩ :=
    exists_uniformRemainderModulus_natCast_le_mul hC hUniform
  refine ⟨min etaMod etaBound, lt_min hetaMod hetaBound, hUniform, ?_, ?_⟩
  · exact mono_radius hMod (min_le_left etaMod etaBound)
  · intro eta heta
    exact hBound eta ⟨heta.1, heta.2.trans (min_le_right etaMod etaBound)⟩

end Asymptotics.IsUniformRemainderModulusOn
