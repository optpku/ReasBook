module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Taylor
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
public import ReasLib.Optimization.DFP.TwoPhaseControls.FrameAngleJet.SlowGraphSlope
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
import all ReasLib.Geometry.Euclidean.Plane.SignedAngle
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- The normalization of two canonical low eigenvectors cancels from the signed
coordinate of their frame product. -/
private theorem coordinate_frame_lowVector_mul (a₁ b₁ d₁ a₂ b₂ d₂ : ℝ)
    (h₁ : RealSymmetric2.lowDenom a₁ b₁ d₁ ≠ 0)
    (h₂ : RealSymmetric2.lowDenom a₂ b₂ d₂ ≠ 0) :
    EuclideanPlane.SignedAngle.coordinate
        (EuclideanPlane.frame (RealSymmetric2.lowVector a₁ b₁ d₁) *
          EuclideanPlane.frame (RealSymmetric2.lowVector a₂ b₂ d₂)) =
      Real.arctan
        (-(b₁ * (d₂ - RealSymmetric2.low a₂ b₂ d₂) +
            (d₁ - RealSymmetric2.low a₁ b₁ d₁) * b₂) /
          ((d₁ - RealSymmetric2.low a₁ b₁ d₁) *
              (d₂ - RealSymmetric2.low a₂ b₂ d₂) - b₁ * b₂)) := by
  unfold EuclideanPlane.SignedAngle.coordinate EuclideanPlane.frame
  simp only [Matrix.mul_apply, Fin.sum_univ_two, EuclideanPlane.perp_apply,
    RealSymmetric2.lowVector, RealSymmetric2.lowRaw, PiLp.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  congr 1
  field_simp [h₁, h₂]
  ring

/-- A germ known to order `m` is also known to every lower order `n`. -/
private theorem eqModPow_mono {n m : ℕ} {f g : ℝ → ℝ}
    (h : EqModPow m f g) (hnm : n ≤ m) : EqModPow n f g := by
  obtain rfl | hlt := hnm.eq_or_lt
  · exact h
  · unfold EqModPow at h ⊢
    exact h.trans (Asymptotics.isLittleO_pow_pow hlt).isBigO

/-- Multiplying order-`n` congruent germs by the parameter raises the order by one. -/
private theorem eqModPow_mul_id {n : ℕ} {f g : ℝ → ℝ}
    (h : EqModPow n f g) :
    EqModPow (n + 1) (fun ε ↦ ε * f ε) (fun ε ↦ ε * g ε) := by
  unfold EqModPow at h ⊢
  have hprod := (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε) (nhds 0)).mul h
  refine hprod.congr' ?_ ?_
  · exact Filter.Eventually.of_forall (fun ε ↦ by ring)
  · exact Filter.Eventually.of_forall (fun ε ↦ by
      change ε * ε ^ n = ε ^ (n + 1)
      rw [pow_succ]
      ring)

/-- The cubic Taylor polynomial of `Real.arctan` has a fourth-order remainder at
zero. -/
private theorem arctan_sub_cubic_isBigO :
    (fun x : ℝ ↦ Real.arctan x - (x - x ^ 3 / 3)) =O[nhds 0]
      (fun x : ℝ ↦ x ^ 4) := by
  let den : ℝ → ℝ := fun x ↦ 1 + x ^ 2
  let d : ℝ → ℝ := fun x ↦ (den x)⁻¹
  have hden : ContDiff ℝ 4 den := by
    fun_prop
  have hd : ContDiff ℝ 4 d := by
    apply hden.inv
    intro x
    dsimp [den]
    positivity
  have hproduct : den * d = fun _ ↦ 1 := by
    funext x
    dsimp [den, d]
    field_simp
  have hdZero : iteratedDeriv 0 d 0 = 1 := by
    norm_num [d, den]
  have hdOne : iteratedDeriv 1 d 0 = 0 := by
    simp [d, den, iteratedDeriv_succ]
  have hdenZero : iteratedDeriv 0 den 0 = 1 := by
    norm_num [den]
  have hdenOne : iteratedDeriv 1 den 0 = 0 := by
    rw [show den = fun x : ℝ ↦ 1 + x ^ 2 by rfl,
      iteratedDeriv_const_add (by norm_num) 1]
    simp
  have hdenTwo : iteratedDeriv 2 den 0 = 2 := by
    rw [show den = fun x : ℝ ↦ 1 + x ^ 2 by rfl,
      iteratedDeriv_const_add (by norm_num) 1]
    simp
  have hdenThree : iteratedDeriv 3 den 0 = 0 := by
    rw [show den = fun x : ℝ ↦ 1 + x ^ 2 by rfl,
      iteratedDeriv_const_add (by norm_num) 1]
    simp
  have hdTwo : iteratedDeriv 2 d 0 = -2 := by
    have h := congrArg (fun f : ℝ → ℝ ↦ iteratedDeriv 2 f 0) hproduct
    rw [iteratedDeriv_mul (hden.contDiffAt.of_le (by norm_num))
      (hd.contDiffAt.of_le (by norm_num))] at h
    norm_num [Finset.sum_range_succ, hdenZero, hdenOne, hdenTwo,
      hdZero, hdOne, iteratedDeriv_const] at h
    linarith
  have hdThree : iteratedDeriv 3 d 0 = 0 := by
    have h := congrArg (fun f : ℝ → ℝ ↦ iteratedDeriv 3 f 0) hproduct
    rw [iteratedDeriv_mul (hden.contDiffAt.of_le (by norm_num))
      (hd.contDiffAt.of_le (by norm_num))] at h
    norm_num [Finset.sum_range_succ, hdenZero, hdenOne, hdenTwo, hdenThree,
      hdZero, hdOne, hdTwo, iteratedDeriv_const] at h
    linarith
  have hderivArctan : deriv Real.arctan = d := by
    simpa only [d, den, one_div] using Real.deriv_arctan
  have h₀ : iteratedDeriv 0 Real.arctan 0 = 0 := by
    simp
  have h₁ : iteratedDeriv 1 Real.arctan 0 = 1 := by
    simp [iteratedDeriv_succ, Real.deriv_arctan]
  have h₂ : iteratedDeriv 2 Real.arctan 0 = 0 := by
    simp [iteratedDeriv_succ, Real.deriv_arctan]
  have h₃ : iteratedDeriv 3 Real.arctan 0 = -2 := by
    rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ', hderivArctan]
    exact hdTwo
  have h₄ : iteratedDeriv 4 Real.arctan 0 = 0 := by
    rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ', hderivArctan]
    exact hdThree
  have hTaylor := taylor_isLittleO_univ (x₀ := 0) (n := 4) Real.contDiff_arctan
  have hPolynomial (x : ℝ) :
      taylorWithinEval Real.arctan 4 Set.univ 0 x = x - x ^ 3 / 3 := by
    rw [taylor_within_apply]
    norm_num [iteratedDerivWithin_univ, Finset.sum_range_succ,
      h₀, h₁, h₂, h₃, h₄]
    ring
  exact hTaylor.isBigO.congr'
    (Filter.Eventually.of_forall fun x ↦ by simp only [hPolynomial])
    (Filter.Eventually.of_forall fun x ↦ by simp)

/-- Along the polynomial slow-graph path, the local real cycle-frame increment is
`-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6 + O(ε ^ 7)`. -/
theorem slowGraphFrameAngleRemainder :
    (fun ε : ℝ ↦
      (observableMap (slowGraphJetPath ε)).frameAngleIncrement -
        (-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  exact slowGraphFrameAngleRemainder_viaSlope

end DFP.TwoLeg
