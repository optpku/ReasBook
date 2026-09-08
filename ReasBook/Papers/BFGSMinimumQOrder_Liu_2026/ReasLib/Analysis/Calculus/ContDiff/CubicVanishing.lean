module

public import ReasLib.Analysis.Calculus.ContDiff.Taylor
public import Mathlib.Analysis.Asymptotics.Lemmas

public section

open Filter
open scoped Topology

universe u

namespace ContDiffAt

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Helper for Infrastructure I.16 (finite-order graph-jet contraction): vanishing zeroth,
first, and second scalar derivatives force a cubic asymptotic bound for a `C^3` map. -/
theorem isBigO_of_threefold_vanishing
    {f : ℝ → F} {x : ℝ}
    (hf : ContDiffAt ℝ 3 f x)
    (hzero : ∀ n < 3, iteratedDeriv n f x = 0) :
    (fun h : ℝ ↦ f (x + h)) =O[𝓝 0] (fun h ↦ h ^ (3 : ℕ)) := by
  have hthreeLe : 3 ≤ 3 := by
    norm_num
  have hTaylor := taylor_isLittleO_of_iteratedDeriv_eq_zero hf hthreeLe hzero
  let c : F := (((3 : ℕ).factorial : ℝ)⁻¹) • iteratedDeriv 3 f x
  have hTaylor' :
      (fun h : ℝ ↦ f (x + h) - h ^ (3 : ℕ) • c) =o[𝓝 0]
        (fun h ↦ h ^ (3 : ℕ)) := by
    refine hTaylor.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [] with h
    dsimp [c]
    norm_num [Finset.sum_Icc_succ_top]
    rw [smul_smul]
    congr 1
    ring
  have hpolyScalar :
      (fun h : ℝ ↦ h ^ (3 : ℕ)) =O[𝓝 0] (fun h ↦ h ^ (3 : ℕ)) :=
    Asymptotics.isBigO_refl _ _
  have hpolyConst :
      (fun _ : ℝ ↦ c) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    Asymptotics.isBigO_const_one ℝ c _
  have hpoly :
      (fun h : ℝ ↦ h ^ (3 : ℕ) • c) =O[𝓝 0] (fun h ↦ h ^ (3 : ℕ)) := by
    simpa only [smul_eq_mul, mul_one] using hpolyScalar.smul hpolyConst
  have hsum := hTaylor'.isBigO.add hpoly
  apply hsum.congr'
  · filter_upwards [] with h
    abel
  · exact Filter.EventuallyEq.rfl

end ContDiffAt
