module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-- Infrastructure I.16a: a quadratic germ with `C²` regularity has first
derivative equal to its linear Taylor coefficient at the base point. -/
theorem HasQuadraticGerm.deriv_eq_linear_of_contDiffAt
    {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂)
    (hregular : ContDiffAt ℝ 2 f 0) :
    deriv f 0 = a₁ := by
  have hmodelRegular : ContDiffAt ℝ 1
      (quadraticModel a₀ a₁ a₂) 0 := by
    unfold quadraticModel
    fun_prop
  have hregularOrder : (1 : WithTop ENat) ≤ (2 : WithTop ENat) := by
    norm_num
  have htwoLeThree : (2 : ℕ) ≤ 3 := by
    norm_num
  have hmodTwo : EqModPow 2 f (quadraticModel a₀ a₁ a₂) :=
    hf.eqMod.mono (n := 2) (m := 3) htwoLeThree
  have hjet :
      FiniteTaylorJet.ofFunction ℝ 1 f 0 =
        FiniteTaylorJet.ofFunction ℝ 1 (quadraticModel a₀ a₁ a₂) 0 := by
    apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
      (hregular.of_le hregularOrder) hmodelRegular
    simpa only [zero_add, Nat.reduceAdd] using hmodTwo.to_isBigO
  have hderivs :=
    (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 1 f
      (quadraticModel a₀ a₁ a₂) 0 0).mp hjet
  have hfirst := hderivs (Fin.last 1)
  have hmodelDeriv : deriv (quadraticModel a₀ a₁ a₂) 0 = a₁ := by
    have hlinear :=
      (hasDerivAt_const (0 : ℝ) a₁).mul (hasDerivAt_id (0 : ℝ))
    have hquadratic :=
      (hasDerivAt_const (0 : ℝ) a₂).mul ((hasDerivAt_id (0 : ℝ)).pow 2)
    have hsum := (hasDerivAt_const (0 : ℝ) a₀).add
      (hlinear.add hquadratic)
    have hcoeff :
        0 + (0 * id 0 + a₁ * 1 +
          (0 * (id ^ 2) 0 + a₂ * ((2 : ℝ) * id 0 ^ (2 - 1) * 1))) = a₁ := by
      simp [id]
    have hsum' := hsum.congr_deriv hcoeff
    have hfunction :
        (fun x : ℝ ↦ a₀) + ((fun x ↦ a₁) * id + (fun x ↦ a₂) * id ^ 2) =
          quadraticModel a₀ a₁ a₂ := by
      funext r
      simp [quadraticModel]
      ring
    rw [hfunction] at hsum'
    exact hsum'.deriv
  have hlastValue : ((Fin.last 1 : Fin (1 + 1)) : ℕ) = 1 := by
    norm_num
  simpa only [hlastValue, iteratedDeriv_succ, iteratedDeriv_zero, hmodelDeriv]
    using hfirst

end DFP.TwoLeg.Mixed
