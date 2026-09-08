module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Ext
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp

public section

namespace FiniteTaylorJet

universe u v w

variable {E : Type u} {F : Type v} {G : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Helper for Infrastructure I.16 (Finite-order graph-jet contraction):
derivative-constructed jets commute with function composition at order zero. -/
theorem comp_ofFunction_zero {f : E → F} {g : F → G} {x : E} :
    comp (ofFunction ℝ 0 g (f x)) (ofFunction ℝ 0 f x) =
      ofFunction ℝ 0 (g ∘ f) x := by
  apply ext_coeff
  intro n
  have hn : n = 0 := Fin.eq_zero n
  subst n
  ext v
  change Fin 0 → E at v
  rw [coeff_comp]
  change ((ofFunction ℝ 0 g (f x)).toFormalMultilinearSeries.comp
      (ofFunction ℝ 0 f x).toFormalMultilinearSeries 0) v = _
  have hzero := FormalMultilinearSeries.comp_coeff_zero
    (ofFunction ℝ 0 g (f x)).toFormalMultilinearSeries
    (ofFunction ℝ 0 f x).toFormalMultilinearSeries
    (fun _ : Fin 0 ↦ (0 : E)) (fun _ : Fin 0 ↦ (0 : F))
  rw [toFormalMultilinearSeries_coeff_of_le _ (Nat.zero_le 0)] at hzero
  rw [coeff_ofFunction_apply] at hzero
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul] at hzero
  rw [iteratedFDeriv_zero_apply] at hzero
  rw [coeff_ofFunction_apply]
  simp only [Fin.val_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  have hv : v = (fun _ : Fin 0 ↦ (0 : E)) := by
    funext i
    exact Fin.elim0 i
  rw [hv]
  exact hzero

/-- Infrastructure I.16 (Finite-order graph-jet contraction):
derivative-constructed jets commute with function composition at order one. -/
theorem comp_ofFunction_one {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g (f x)) :
    comp (ofFunction ℝ 1 g (f x)) (ofFunction ℝ 1 f x) =
      ofFunction ℝ 1 (g ∘ f) x := by
  apply ext_coeff
  intro n
  fin_cases n
  · ext v
    change Fin 0 → E at v
    rw [coeff_comp]
    change ((ofFunction ℝ 1 g (f x)).toFormalMultilinearSeries.comp
        (ofFunction ℝ 1 f x).toFormalMultilinearSeries 0) v = _
    have hzero := FormalMultilinearSeries.comp_coeff_zero
      (ofFunction ℝ 1 g (f x)).toFormalMultilinearSeries
      (ofFunction ℝ 1 f x).toFormalMultilinearSeries
      (fun _ : Fin 0 ↦ (0 : E)) (fun _ : Fin 0 ↦ (0 : F))
    rw [toFormalMultilinearSeries_coeff_of_le _ (Nat.zero_le 1)] at hzero
    rw [coeff_ofFunction_apply] at hzero
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul] at hzero
    rw [iteratedFDeriv_zero_apply] at hzero
    rw [coeff_ofFunction_apply]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    have hv' : v = (fun _ : Fin 0 ↦ (0 : E)) := by
      funext i
      exact Fin.elim0 i
    rw [hv']
    exact hzero
  · ext v
    change Fin 1 → E at v
    rw [coeff_comp]
    change ((ofFunction ℝ 1 g (f x)).toFormalMultilinearSeries.comp
        (ofFunction ℝ 1 f x).toFormalMultilinearSeries 1) v = _
    rw [FormalMultilinearSeries.comp_coeff_one]
    rw [toFormalMultilinearSeries_coeff_of_le _ (Nat.le_refl 1)]
    rw [toFormalMultilinearSeries_coeff_of_le _ (Nat.le_refl 1)]
    rw [coeff_ofFunction_apply, coeff_ofFunction_apply, coeff_ofFunction_apply]
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
    rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply,
      iteratedFDeriv_one_apply]
    have hchain := fderiv_comp x hg.differentiableAt_one hf.differentiableAt_one
    rw [hchain]
    rfl

end FiniteTaylorJet
