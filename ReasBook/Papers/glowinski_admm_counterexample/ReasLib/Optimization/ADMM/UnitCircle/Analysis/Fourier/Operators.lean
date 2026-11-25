/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.Transform
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Symbol

@[expose] public section

namespace ADMM.UnitCircle.Fourier

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

/-- The orientation makes a positive time delay correspond to a negative power. -/
def circlePoint (t : AddCircle (1 : ℝ)) : ℂ := fourier (-1) t

@[simp] theorem circlePoint_norm (t : AddCircle (1 : ℝ)) : ‖circlePoint t‖ = 1 :=
  Circle.norm_coe _

theorem circlePoint_inv (t : AddCircle (1 : ℝ)) : (circlePoint t)⁻¹ = fourier 1 t := by
  apply inv_eq_of_mul_eq_one_right
  change fourier (-1) t * fourier 1 t = 1
  rw [← fourier_add]
  norm_num [fourier_zero]

theorem character_nat (j : ℕ) (t : AddCircle (1 : ℝ)) :
    fourier (j : ℤ) t = fourier 1 t ^ j := by
  induction j with
  | zero => simp [fourier_zero]
  | succ j ih => simp only [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

theorem backward_character (j : ℕ) (t : AddCircle (1 : ℝ)) :
    fourier (j : ℤ) t = ((circlePoint t)⁻¹) ^ j := by
  rw [circlePoint_inv, character_nat]

theorem forward_character (j : ℕ) (t : AddCircle (1 : ℝ)) :
    fourier (-(j : ℤ)) t = circlePoint t ^ j := by
  rw [fourier_neg, character_nat]
  simp only [circlePoint, fourier_neg, map_pow]

theorem transform_add_ae (x y : TimeSequence) :
    transform (x + y) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ transform x t + transform y t) := by
  rw [map_add]
  filter_upwards [Lp.coeFn_add (transform x) (transform y)] with t ht
  exact ht

theorem transform_sub_ae (x y : TimeSequence) :
    transform (x - y) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ transform x t - transform y t) := by
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub (transform x) (transform y)] with t ht
  exact ht

theorem transform_neg_ae (x : TimeSequence) :
    transform (-x) =ᵐ[AddCircle.haarAddCircle] (fun t ↦ -transform x t) := by
  rw [map_neg]
  filter_upwards [Lp.coeFn_neg (transform x)] with t ht
  exact ht

theorem transform_smul_ae (c : ℂ) (x : TimeSequence) :
    transform (c • x) =ᵐ[AddCircle.haarAddCircle] (fun t ↦ c * transform x t) := by
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul c (transform x)] with t ht
  exact ht

theorem transform_delay_ae (j : ℤ) (x : TimeSequence) :
    transform (delay j x) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ fourier j t * transform x t) := by
  rw [transform_delay]
  exact characterMultiply_ae j (transform x)

/-- The true discounted difference operator on bilateral square-summable sequences. -/
def difference (α : ℝ) (x : TimeSequence) : TimeSequence :=
  x - (α : ℂ) • delay 1 x

/-- The multiplier-normal operator `I + (γ−1)αS`. -/
def multiplierNormal (α γ : ℝ) (x : TimeSequence) : TimeSequence :=
  x + (((γ - 1) * α : ℝ) : ℂ) • delay 1 x

theorem transform_difference_ae (α : ℝ) (x : TimeSequence) :
    transform (difference α x) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ delaySymbol α (circlePoint t) * transform x t) := by
  filter_upwards [transform_sub_ae x ((α : ℂ) • delay 1 x),
    transform_smul_ae (α : ℂ) (delay 1 x), transform_delay_ae 1 x] with t hsub hsmul hd
  change transform (x - (α : ℂ) • delay 1 x) t = _
  rw [hsub, hsmul, hd, delaySymbol, circlePoint_inv]
  ring

theorem transform_multiplierNormal_ae (α γ : ℝ) (x : TimeSequence) :
    transform (multiplierNormal α γ x) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ multiplierSymbol α γ (circlePoint t) * transform x t) := by
  filter_upwards [transform_add_ae x ((((γ - 1) * α : ℝ) : ℂ) • delay 1 x),
    transform_smul_ae (((γ - 1) * α : ℝ) : ℂ) (delay 1 x),
    transform_delay_ae 1 x] with t hadd hsmul hd
  change transform (x + (((γ - 1) * α : ℝ) : ℂ) • delay 1 x) t = _
  rw [hadd, hsmul, hd, multiplierSymbol, circlePoint_inv]
  push_cast
  ring

/-- The two actual graph outputs in discounted state coordinates `(eta,w)`. -/
def pointSignal (α : ℝ) (s : Fin 2 → TimeSequence) (b : Fin 2) : TimeSequence :=
  if b = 0 then s 0 + difference α (s 1) else s 0

/-- The corresponding two actual graph normals. -/
def normalSignal (α γ : ℝ) (s : Fin 2 → TimeSequence) (b : Fin 2) : TimeSequence :=
  if b = 0 then -difference α (s 0) - multiplierNormal α γ (s 1)
  else multiplierNormal α γ (s 1)

def frequencyState (s : Fin 2 → TimeSequence) (t : AddCircle (1 : ℝ)) : Fin 2 → ℂ :=
  fun i ↦ transform (s i) t

theorem transform_pointSignal_ae (α : ℝ) (s : Fin 2 → TimeSequence) (b : Fin 2) :
    transform (pointSignal α s b) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ dotProduct (pointRow α (circlePoint t) b) (frequencyState s t)) := by
  fin_cases b
  · filter_upwards [transform_add_ae (s 0) (difference α (s 1)),
      transform_difference_ae α (s 1)] with t hadd hd
    change transform (s 0 + difference α (s 1)) t = _
    rw [hadd, hd]
    simp [pointRow, frequencyState, Fin.sum_univ_two, dotProduct]
  · exact Filter.Eventually.of_forall fun t ↦ by
      simp [pointSignal, pointRow, frequencyState, Fin.sum_univ_two, dotProduct]

theorem transform_normalSignal_ae (α γ : ℝ) (s : Fin 2 → TimeSequence) (b : Fin 2) :
    transform (normalSignal α γ s b) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ dotProduct (normalRow α γ (circlePoint t) b) (frequencyState s t)) := by
  fin_cases b
  · filter_upwards [transform_sub_ae (-difference α (s 0)) (multiplierNormal α γ (s 1)),
      transform_neg_ae (difference α (s 0)), transform_difference_ae α (s 0),
      transform_multiplierNormal_ae α γ (s 1)] with t hsub hneg hd hm
    change transform (-difference α (s 0) - multiplierNormal α γ (s 1)) t = _
    rw [hsub, hneg, hd, hm]
    simp [normalRow, frequencyState, Fin.sum_univ_two, dotProduct, sub_eq_add_neg]
  · filter_upwards [transform_multiplierNormal_ae α γ (s 1)] with t hm
    simpa [normalSignal, normalRow, frequencyState, Fin.sum_univ_two, dotProduct] using hm

end

end ADMM.UnitCircle.Fourier
