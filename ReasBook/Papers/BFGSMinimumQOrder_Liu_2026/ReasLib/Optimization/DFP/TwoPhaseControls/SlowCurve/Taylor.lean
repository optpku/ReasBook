module

public import ReasLib.Analysis.Calculus.ContDiff.Taylor

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- A `C⁵` real graph through `(2, 1)` whose coordinate functions are flat to
second order has cubic and quartic Taylor coefficients with fifth-order
remainders. -/
theorem exists_flatGraphTaylorCoefficients (p h : ℝ → ℝ)
    (h_contDiff : ContDiffAt ℝ 5 (fun ε ↦ (p ε, h ε)) 0)
    (h_base : (p 0, h 0) = (2, 1))
    (h_p_first : iteratedDeriv 1 p 0 = 0)
    (h_h_first : iteratedDeriv 1 h 0 = 0)
    (h_p_second : iteratedDeriv 2 p 0 = 0)
    (h_h_second : iteratedDeriv 2 h 0 = 0) :
    ∃ P₃ H₃ P₄ H₄ : ℝ,
      (fun ε ↦ p ε - (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)) =O[𝓝 0]
          (fun ε ↦ ε ^ 5) ∧
        (fun ε ↦ h ε - (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) =O[𝓝 0]
          (fun ε ↦ ε ^ 5) := by
  have hp0 : p 0 = 2 := congrArg Prod.fst h_base
  have hh0 : h 0 = 1 := congrArg Prod.snd h_base
  have hp_cont : ContDiffAt ℝ 5 p 0 := by simpa using h_contDiff.fst
  have hh_cont : ContDiffAt ℝ 5 h 0 := by simpa using h_contDiff.snd
  let ps : ℝ → ℝ := fun ε ↦ p ε - 2
  let hs : ℝ → ℝ := fun ε ↦ h ε - 1
  have hps_cont : ContDiffAt ℝ 5 ps 0 := by
    dsimp [ps]
    exact hp_cont.sub contDiffAt_const
  have hhs_cont : ContDiffAt ℝ 5 hs 0 := by
    dsimp [hs]
    exact hh_cont.sub contDiffAt_const
  have hps_zero : ∀ n < 3, iteratedDeriv n ps 0 = 0 := by
    intro n hn
    interval_cases n
    · simp [ps, iteratedDeriv_zero, hp0]
    · simpa [ps, iteratedDeriv_one] using h_p_first
    · simpa [ps, iteratedDeriv_succ, iteratedDeriv_one] using h_p_second
  have hhs_zero : ∀ n < 3, iteratedDeriv n hs 0 = 0 := by
    intro n hn
    interval_cases n
    · simp [hs, iteratedDeriv_zero, hh0]
    · simpa [hs, iteratedDeriv_one] using h_h_first
    · simpa [hs, iteratedDeriv_succ, iteratedDeriv_one] using h_h_second
  have hpsTaylor :=
    ContDiffAt.taylor_isLittleO_of_iteratedDeriv_eq_zero hps_cont
      (by norm_num : 3 ≤ 5) hps_zero
  have hhsTaylor :=
    ContDiffAt.taylor_isLittleO_of_iteratedDeriv_eq_zero hhs_cont
      (by norm_num : 3 ≤ 5) hhs_zero
  let P₃ : ℝ := ((3 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 3 ps 0
  let H₃ : ℝ := ((3 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 3 hs 0
  let P₄ : ℝ := ((4 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 4 ps 0
  let H₄ : ℝ := ((4 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 4 hs 0
  refine ⟨P₃, H₃, P₄, H₄, ?_, ?_⟩
  · have hmain := hpsTaylor.isBigO
    have h5 :
        (fun ε : ℝ ↦
          (((5 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 5 ps 0) * ε ^ 5) =O[𝓝 0]
          (fun ε ↦ ε ^ 5) := by
      simpa only [smul_eq_mul] using
        (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).const_mul_left
          (((5 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 5 ps 0)
    have hsum := hmain.add h5
    apply hsum.congr'
    · filter_upwards [] with ε
      dsimp [ps, P₃, P₄]
      norm_num [Finset.sum_Icc_succ_top]
      ring
    · rfl
  · have hmain := hhsTaylor.isBigO
    have h5 :
        (fun ε : ℝ ↦
          (((5 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 5 hs 0) * ε ^ 5) =O[𝓝 0]
          (fun ε ↦ ε ^ 5) := by
      simpa only [smul_eq_mul] using
        (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).const_mul_left
          (((5 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 5 hs 0)
    have hsum := hmain.add h5
    apply hsum.congr'
    · filter_upwards [] with ε
      dsimp [hs, H₃, H₄]
      norm_num [Finset.sum_Icc_succ_top]
      ring
    · rfl

end DFP.TwoLeg
