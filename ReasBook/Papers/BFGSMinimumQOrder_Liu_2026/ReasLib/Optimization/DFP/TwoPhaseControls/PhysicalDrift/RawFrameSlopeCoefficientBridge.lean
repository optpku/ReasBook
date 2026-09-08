module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This file contains the lower, source-facing algebraic boundary for the mixed raw
frame slope.  It deliberately mentions only the four scalar frame-entry paths;
the evaluator and its orientation/sign choices remain owned by the physical-drift
source file.
-/

/-- Infrastructure I.16a: quadratic germs of the four frame entries determine the
quadratic germ of the lower-left/upper-left relative-frame quotient. -/
theorem mixedRawFrameSlope_quadraticGerm_of_entryGerms
    {E₁ X₁ E₂ X₂ : ℝ → ℝ}
    {e₁ e₁₂ x₁ x₁₂ e₂ e₂₂ x₂ x₂₂ : ℝ}
    (hE₁ : HasQuadraticGerm E₁ 0 e₁ e₁₂)
    (hX₁ : HasQuadraticGerm X₁ 1 x₁ x₁₂)
    (hE₂ : HasQuadraticGerm E₂ 0 e₂ e₂₂)
    (hX₂ : HasQuadraticGerm X₂ 1 x₂ x₂₂)
    (hlinear : e₁ + e₂ = 3) :
    HasQuadraticGerm
      (fun r ↦ -(E₁ r * X₂ r + X₁ r * E₂ r) /
        (X₁ r * X₂ r - E₁ r * E₂ r))
      0 (-3)
      (-(e₁ * x₂ + e₁₂ + e₂₂ + x₁ * e₂) +
        (e₁ + e₂) * (x₁ + x₂)) := by
  let numerator : ℝ → ℝ := fun r ↦
    -(E₁ r * X₂ r + X₁ r * E₂ r)
  let denominator : ℝ → ℝ := fun r ↦
    X₁ r * X₂ r - E₁ r * E₂ r
  have hfirstProduct := hE₁.mul hX₂
  have hsecondProduct := hX₁.mul hE₂
  have hsum := hfirstProduct.add hsecondProduct
  have hnumeratorRaw := hsum.neg
  have hnumeratorCoeff : HasQuadraticGerm
      (fun r ↦ -(E₁ r * X₂ r + X₁ r * E₂ r)) 0 (-(e₁ + e₂))
      (-(e₁ * x₂ + e₁₂ + e₂₂ + x₁ * e₂)) := by
    apply hnumeratorRaw.congrCoefficients
    · ring
    · ring
    · ring
  have hnumerator : HasQuadraticGerm numerator 0 (-(e₁ + e₂))
      (-(e₁ * x₂ + e₁₂ + e₂₂ + x₁ * e₂)) := by
    apply hnumeratorCoeff.congrFunction
    intro r
    rfl
  have hdenominatorRaw := (hX₁.mul hX₂).sub (hE₁.mul hE₂)
  have hdenominatorCoeff : HasQuadraticGerm
      (fun r ↦ X₁ r * X₂ r - E₁ r * E₂ r) 1 (x₁ + x₂)
      (x₁ * x₂ + x₁₂ + x₂₂ - e₁ * e₂) := by
    apply hdenominatorRaw.congrCoefficients
    · ring
    · ring
    · ring
  have hdenominator : HasQuadraticGerm denominator 1 (x₁ + x₂)
      (x₁ * x₂ + x₁₂ + x₂₂ - e₁ * e₂) := by
    apply hdenominatorCoeff.congrFunction
    intro r
    rfl
  have hdenominatorBase : (1 : ℝ) ≠ 0 := by
    norm_num
  have hquotientRaw := hnumerator.div hdenominator
    hdenominatorBase
  have hquotientCoeff : HasQuadraticGerm
      (fun r ↦ numerator r / denominator r) 0 (-3)
      (-(e₁ * x₂ + e₁₂ + e₂₂ + x₁ * e₂) +
        (e₁ + e₂) * (x₁ + x₂)) := by
    apply hquotientRaw.congrCoefficients
    · ring
    · rw [hlinear]
      ring
    · ring
  apply hquotientCoeff.congrFunction
  intro r
  rfl

/-- Helper for Infrastructure I.16a: `C²` entry paths and a nonzero denominator
at the base produce the `C²` regularity needed by the raw-frame slope quotient. -/
theorem mixedRawFrameSlope_contDiffAt_of_entryRegularity
    {E₁ X₁ E₂ X₂ : ℝ → ℝ}
    (hE₁ : ContDiffAt ℝ 2 E₁ 0)
    (hX₁ : ContDiffAt ℝ 2 X₁ 0)
    (hE₂ : ContDiffAt ℝ 2 E₂ 0)
    (hX₂ : ContDiffAt ℝ 2 X₂ 0)
    (hden : X₁ 0 * X₂ 0 - E₁ 0 * E₂ 0 ≠ 0) :
    ContDiffAt ℝ 2
      (fun r ↦ -(E₁ r * X₂ r + X₁ r * E₂ r) /
        (X₁ r * X₂ r - E₁ r * E₂ r)) 0 := by
  have hnumerator : ContDiffAt ℝ 2
      (fun r ↦ -(E₁ r * X₂ r + X₁ r * E₂ r)) 0 := by
    exact (hE₁.mul hX₂).add (hX₁.mul hE₂) |>.neg
  have hdenominator : ContDiffAt ℝ 2
      (fun r ↦ X₁ r * X₂ r - E₁ r * E₂ r) 0 := by
    exact (hX₁.mul hX₂).sub (hE₁.mul hE₂)
  exact hnumerator.div hdenominator hden

/-- Helper for Infrastructure I.16a: a quadratic germ and `C²` regularity expose
the germ's first derivative as its linear coefficient. -/
private theorem quadraticGerm_deriv_eq_linear_of_contDiffAt
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
  have hindex : (1 : ℕ) < 1 + 1 := by
    norm_num
  have hfirst := hderivs ⟨1, hindex⟩
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
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, hmodelDeriv] using hfirst

/-- Infrastructure I.16a: four regular quadratic entry certificates and the
nonvanishing base denominator close the raw-frame slope `C²` and derivative
interface, with the mixed linear coefficient fixed to `-3`. -/
theorem mixedRawFrameSlope_contDiffAt_and_deriv_of_entryCertificates
    {E₁ X₁ E₂ X₂ : ℝ → ℝ}
    {e₁ e₁₂ x₁ x₁₂ e₂ e₂₂ x₂ x₂₂ : ℝ}
    (hE₁Regular : ContDiffAt ℝ 2 E₁ 0)
    (hX₁Regular : ContDiffAt ℝ 2 X₁ 0)
    (hE₂Regular : ContDiffAt ℝ 2 E₂ 0)
    (hX₂Regular : ContDiffAt ℝ 2 X₂ 0)
    (hE₁ : HasQuadraticGerm E₁ 0 e₁ e₁₂)
    (hX₁ : HasQuadraticGerm X₁ 1 x₁ x₁₂)
    (hE₂ : HasQuadraticGerm E₂ 0 e₂ e₂₂)
    (hX₂ : HasQuadraticGerm X₂ 1 x₂ x₂₂)
    (hden : X₁ 0 * X₂ 0 - E₁ 0 * E₂ 0 ≠ 0)
    (hlinear : e₁ + e₂ = 3) :
    ContDiffAt ℝ 2
        (fun r ↦ -(E₁ r * X₂ r + X₁ r * E₂ r) /
          (X₁ r * X₂ r - E₁ r * E₂ r)) 0 ∧
      deriv (fun r ↦ -(E₁ r * X₂ r + X₁ r * E₂ r) /
        (X₁ r * X₂ r - E₁ r * E₂ r)) 0 = -3 := by
  have hregular := mixedRawFrameSlope_contDiffAt_of_entryRegularity
    hE₁Regular hX₁Regular hE₂Regular hX₂Regular hden
  have hgerm := mixedRawFrameSlope_quadraticGerm_of_entryGerms
    hE₁ hX₁ hE₂ hX₂ hlinear
  have hderiv := quadraticGerm_deriv_eq_linear_of_contDiffAt hgerm hregular
  exact ⟨hregular, hderiv⟩

end DFP.TwoLeg.Mixed
