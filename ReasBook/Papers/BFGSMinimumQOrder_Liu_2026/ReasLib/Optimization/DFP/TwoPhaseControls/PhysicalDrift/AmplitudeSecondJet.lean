module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondJetConcrete
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondJetConcrete
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Helper for Appendix Lemma A.6: the quadratic polynomial with constant, linear,
and quadratic coefficients `a₀`, `a₁`, and `a₂`. -/
def quadraticModel (a₀ a₁ a₂ : ℝ) : ℝ → ℝ :=
  fun r ↦ a₀ + a₁ * r + a₂ * r ^ 2

/-- Helper for Appendix Lemma A.6: a scalar path has a continuous quadratic germ
when it agrees with `quadraticModel a₀ a₁ a₂` modulo the third power. -/
structure HasQuadraticGerm (f : ℝ → ℝ) (a₀ a₁ a₂ : ℝ) : Prop where
  continuousAt : ContinuousAt f 0
  eqMod : EqModPow 3 f (quadraticModel a₀ a₁ a₂)

namespace HasQuadraticGerm

/-- Helper for Appendix Lemma A.6: every quadratic model is continuous at the origin. -/
theorem quadraticModel_continuousAt (a₀ a₁ a₂ : ℝ) :
    ContinuousAt (quadraticModel a₀ a₁ a₂) 0 := by
  unfold quadraticModel
  fun_prop

/-- Helper for Appendix Lemma A.6: a quadratic model carries its own quadratic germ. -/
theorem model (a₀ a₁ a₂ : ℝ) :
    HasQuadraticGerm (quadraticModel a₀ a₁ a₂) a₀ a₁ a₂ := by
  constructor
  · exact quadraticModel_continuousAt a₀ a₁ a₂
  · exact EqModPow.refl 3 (quadraticModel a₀ a₁ a₂)

/-- Helper for Appendix Lemma A.6: a `C³` path with a quadratic germ has the
    corresponding second iterated derivative at the origin. -/
theorem iteratedDeriv_two_eq_of_contDiffAt
    {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂)
    (hregular : ContDiffAt ℝ 3 f 0) :
    iteratedDeriv 2 f 0 = 2 * a₂ := by
  have hmodelRegular : ContDiffAt ℝ 2 (quadraticModel a₀ a₁ a₂) 0 := by
    unfold quadraticModel
    fun_prop
  have hjet :
      FiniteTaylorJet.ofFunction ℝ 2 f 0 =
        FiniteTaylorJet.ofFunction ℝ 2 (quadraticModel a₀ a₁ a₂) 0 := by
    have hregularOrder : (2 : WithTop ENat) ≤ 3 := by
      norm_num
    apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
      (hregular.of_le hregularOrder) hmodelRegular
    simpa only [zero_add, Nat.reduceAdd] using hf.eqMod.to_isBigO
  have hderivs :=
    (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 2 f
      (quadraticModel a₀ a₁ a₂) 0 0).mp hjet
  have hindex : (2 : ℕ) < 2 + 1 := by norm_num
  have hsecond := hderivs ⟨2, hindex⟩
  have hmodelDeriv :
      deriv (quadraticModel a₀ a₁ a₂) = fun r ↦ a₁ + 2 * a₂ * r := by
    funext r
    have hlinear := (hasDerivAt_const r a₁).mul (hasDerivAt_id r)
    have hquadratic := (hasDerivAt_const r a₂).mul ((hasDerivAt_id r).pow 2)
    have hsum := (hasDerivAt_const r a₀).add (hlinear.add hquadratic)
    have hcoeff :
        0 + (0 * id r + a₁ * 1 +
          (0 * (id ^ 2) r + a₂ * ((2 : ℝ) * id r ^ (2 - 1) * 1))) =
          a₁ + 2 * a₂ * r := by
      simp [id]
      ring
    have hsum' := hsum.congr_deriv hcoeff
    have hfunction :
        (fun x : ℝ ↦ a₀) + ((fun x ↦ a₁) * id + (fun x ↦ a₂) * id ^ 2) =
          quadraticModel a₀ a₁ a₂ := by
      funext s
      simp [quadraticModel]
      ring
    rw [hfunction] at hsum'
    exact hsum'.deriv
  have hsecond' : deriv (deriv f) 0 =
      deriv (deriv (quadraticModel a₀ a₁ a₂)) 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hsecond
  have hlinear' : HasDerivAt (fun r : ℝ ↦ a₁ + 2 * a₂ * r) (2 * a₂) 0 := by
    have hlinear := (hasDerivAt_const 0 a₁).add
      ((hasDerivAt_const 0 (2 * a₂)).mul (hasDerivAt_id 0))
    apply hlinear.congr_deriv
    simp
  calc
    iteratedDeriv 2 f 0 = deriv (deriv f) 0 := by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    _ = deriv (deriv (quadraticModel a₀ a₁ a₂)) 0 := hsecond'
    _ = deriv (fun r ↦ a₁ + 2 * a₂ * r) 0 := by rw [hmodelDeriv]
    _ = 2 * a₂ := hlinear'.deriv

/-- Helper for Appendix Lemma A.6: a pointwise equal representative carries the same
quadratic germ. -/
theorem congrFunction {f g : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂) (hfg : ∀ r, g r = f r) :
    HasQuadraticGerm g a₀ a₁ a₂ := by
  have hfun : g = f := by
    funext r
    exact hfg r
  rw [hfun]
  exact hf

/-- Helper for Appendix Lemma A.6: equal coefficient triples describe the same
quadratic germ. -/
theorem congrCoefficients {f : ℝ → ℝ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂)
    (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
    HasQuadraticGerm f b₀ b₁ b₂ := by
  subst b₀
  subst b₁
  subst b₂
  exact hf

/-- Helper for Appendix Lemma A.6: quadratic germs are closed under negation. -/
theorem neg {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂) :
    HasQuadraticGerm (fun r ↦ -f r) (-a₀) (-a₁) (-a₂) := by
  constructor
  · exact hf.continuousAt.neg
  · have hneg := hf.eqMod.neg
    apply hneg.congr
    · intro r
      rfl
    · intro r
      simp only [quadraticModel]
      ring

/-- Helper for Appendix Lemma A.6: quadratic germs are closed under addition. -/
theorem add {f g : ℝ → ℝ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂)
    (hg : HasQuadraticGerm g b₀ b₁ b₂) :
    HasQuadraticGerm (fun r ↦ f r + g r)
      (a₀ + b₀) (a₁ + b₁) (a₂ + b₂) := by
  constructor
  · exact hf.continuousAt.add hg.continuousAt
  · have hadd := hf.eqMod.add hg.eqMod
    apply hadd.congr
    · intro r
      rfl
    · intro r
      simp only [quadraticModel]
      ring

/-- Helper for Appendix Lemma A.6: quadratic germs are closed under subtraction. -/
theorem sub {f g : ℝ → ℝ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂)
    (hg : HasQuadraticGerm g b₀ b₁ b₂) :
    HasQuadraticGerm (fun r ↦ f r - g r)
      (a₀ - b₀) (a₁ - b₁) (a₂ - b₂) := by
  constructor
  · exact hf.continuousAt.sub hg.continuousAt
  · have hsub := hf.eqMod.sub hg.eqMod
    apply hsub.congr
    · intro r
      rfl
    · intro r
      simp only [quadraticModel]
      ring

/-- Helper for Appendix Lemma A.6: multiplication convolves quadratic germ
coefficients and discards terms of order at least three. -/
theorem mul {f g : ℝ → ℝ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂)
    (hg : HasQuadraticGerm g b₀ b₁ b₂) :
    HasQuadraticGerm (fun r ↦ f r * g r)
      (a₀ * b₀) (a₀ * b₁ + a₁ * b₀)
      (a₀ * b₂ + a₁ * b₁ + a₂ * b₀) := by
  constructor
  · exact hf.continuousAt.mul hg.continuousAt
  · have hmodelContinuous := quadraticModel_continuousAt a₀ a₁ a₂
    have hraw := hf.eqMod.mul hg.eqMod hmodelContinuous hg.continuousAt
    have htruncate : EqModPow 3
        (fun r ↦ quadraticModel a₀ a₁ a₂ r * quadraticModel b₀ b₁ b₂ r)
        (quadraticModel (a₀ * b₀) (a₀ * b₁ + a₁ * b₀)
          (a₀ * b₂ + a₁ * b₁ + a₂ * b₀)) := by
      apply EqModPow.of_factor
        (q := fun r ↦ a₁ * b₂ + a₂ * b₁ + a₂ * b₂ * r)
      · fun_prop
      · intro r
        simp only [quadraticModel]
        ring
    exact hraw.trans htruncate

/-- Helper for Appendix Lemma A.6: multiplication by a constant scales every
quadratic germ coefficient. -/
theorem constMul (c : ℝ) {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂) :
    HasQuadraticGerm (fun r ↦ c * f r) (c * a₀) (c * a₁) (c * a₂) := by
  have hc := model c 0 0
  have hmul := hc.mul hf
  have hlinearCoefficient : c * a₁ + 0 * a₀ = c * a₁ := by
    ring
  have hquadraticCoefficient : c * a₂ + 0 * a₁ + 0 * a₀ = c * a₂ := by
    ring
  have hcoeff := hmul.congrCoefficients
    (show c * a₀ = c * a₀ from rfl)
    hlinearCoefficient hquadraticCoefficient
  apply hcoeff.congrFunction
  intro r
  simp only [quadraticModel]
  ring

/-- Helper for Appendix Lemma A.6: the reciprocal of a nonvanishing quadratic germ
has the standard reciprocal coefficients. -/
theorem inv {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂) (ha₀ : a₀ ≠ 0) :
    HasQuadraticGerm (fun r ↦ (f r)⁻¹)
      a₀⁻¹ (-a₁ / a₀ ^ 2) (a₁ ^ 2 / a₀ ^ 3 - a₂ / a₀ ^ 2) := by
  let q := quadraticModel a₀⁻¹ (-a₁ / a₀ ^ 2)
    (a₁ ^ 2 / a₀ ^ 3 - a₂ / a₀ ^ 2)
  have hq : HasQuadraticGerm q a₀⁻¹ (-a₁ / a₀ ^ 2)
      (a₁ ^ 2 / a₀ ^ 3 - a₂ / a₀ ^ 2) := model _ _ _
  have hproduct := hf.mul hq
  have hmodelEq : ∀ r : ℝ,
      quadraticModel
          (a₀ * a₀⁻¹)
          (a₀ * (-a₁ / a₀ ^ 2) + a₁ * a₀⁻¹)
          (a₀ * (a₁ ^ 2 / a₀ ^ 3 - a₂ / a₀ ^ 2) +
            a₁ * (-a₁ / a₀ ^ 2) + a₂ * a₀⁻¹) r = 1 := by
    intro r
    simp only [quadraticModel]
    field_simp [ha₀]
    ring
  have hproductOne : EqModPow 3 (fun r ↦ f r * q r) (fun _ ↦ 1) := by
    apply hproduct.eqMod.congr
    · intro r
      rfl
    · intro r
      exact (hmodelEq r).symm
  have hvalue := EqModPow.eq_at_zero_of_pos (n := 3) (Nat.zero_lt_succ 2) hf.eqMod
  have hf0 : f 0 ≠ 0 := by
    rw [hvalue]
    simpa [quadraticModel, pow_two] using ha₀
  constructor
  · exact hf.continuousAt.inv₀ hf0
  · exact EqModPow.inv_of_mul_eq_one hproductOne hf.continuousAt hf0

/-- Helper for Appendix Lemma A.6: division by a nonvanishing quadratic germ is
multiplication by its reciprocal germ. -/
theorem div {f g : ℝ → ℝ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂)
    (hg : HasQuadraticGerm g b₀ b₁ b₂) (hb₀ : b₀ ≠ 0) :
    HasQuadraticGerm (fun r ↦ f r / g r)
      (a₀ * b₀⁻¹)
      (a₀ * (-b₁ / b₀ ^ 2) + a₁ * b₀⁻¹)
      (a₀ * (b₁ ^ 2 / b₀ ^ 3 - b₂ / b₀ ^ 2) +
        a₁ * (-b₁ / b₀ ^ 2) + a₂ * b₀⁻¹) := by
  have hinv := hg.inv hb₀
  have hmul := hf.mul hinv
  apply hmul.congrFunction
  intro r
  rw [div_eq_mul_inv]

/-- Helper for Appendix Lemma A.6: the positive square root of a germ based at one
has coefficients obtained by solving the square equation through order two. -/
theorem sqrtOne {f : ℝ → ℝ} {a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f 1 a₁ a₂) :
    HasQuadraticGerm (fun r ↦ Real.sqrt (f r))
      1 (a₁ / 2) (a₂ / 2 - a₁ ^ 2 / 8) := by
  let q := quadraticModel 1 (a₁ / 2) (a₂ / 2 - a₁ ^ 2 / 8)
  have hq : HasQuadraticGerm q 1 (a₁ / 2) (a₂ / 2 - a₁ ^ 2 / 8) := model _ _ _
  have hsquare := hq.mul hq
  have hconstantCoefficient : (1 : ℝ) * 1 = 1 := by
    norm_num
  have hlinearCoefficient :
      (1 : ℝ) * (a₁ / 2) + (a₁ / 2) * 1 = a₁ := by
    ring
  have hquadraticCoefficient :
      (1 : ℝ) * (a₂ / 2 - a₁ ^ 2 / 8) +
          (a₁ / 2) * (a₁ / 2) + (a₂ / 2 - a₁ ^ 2 / 8) * 1 = a₂ := by
    ring
  have hsquare' : HasQuadraticGerm (fun r ↦ q r ^ 2) 1 a₁ a₂ := by
    have hcoeff := hsquare.congrCoefficients
      hconstantCoefficient hlinearCoefficient hquadraticCoefficient
    apply hcoeff.congrFunction
    intro r
    ring
  have horder : 0 < (3 : ℕ) := by
    norm_num
  have hvalue := EqModPow.eq_at_zero_of_pos (n := 3) horder hf.eqMod
  have hf0 : 0 < f 0 := by
    rw [hvalue]
    norm_num [quadraticModel]
  have hq0 : 0 < q 0 := by
    norm_num [q, quadraticModel]
  constructor
  · exact hf.continuousAt.sqrt
  · exact EqModPow.sqrt_of_sq (hf.eqMod.trans hsquare'.eqMod.symm)
      hf.continuousAt hq.continuousAt hf0 hq0

end HasQuadraticGerm

/- The canonical base values in the mixed normal form are
   `(sLow,sHigh,gLow,gHigh) = (2,1,1,2)`. -/

/-- Helper for Appendix Lemma A.6: canonical spectral and gradient component germs
    determine the recovered radius factor through quadratic order. -/
theorem recoveryRadiusQuadraticGerm_of_componentGerms
    {sLow sHigh gLow gHigh : ℝ → ℝ}
    {s₁ s₂ t₁ t₂ g₁ g₂ u₁ u₂ : ℝ}
    (hsLow : HasQuadraticGerm sLow 2 s₁ s₂)
    (hsHigh : HasQuadraticGerm sHigh 1 t₁ t₂)
    (hgLow : HasQuadraticGerm gLow 1 g₁ g₂)
    (hgHigh : HasQuadraticGerm gHigh 2 u₁ u₂) :
    HasQuadraticGerm
      (fun r ↦ sLow r * gLow r / (sHigh r * gHigh r))
      1
      ((2 * g₁ + s₁ - (u₁ + 2 * t₁)) / 2)
      ((2 * (2 * g₂ + s₁ * g₁ + s₂) - (2 * g₁ + s₁) * (u₁ + 2 * t₁) +
          (u₁ + 2 * t₁) ^ 2 - 2 * (u₂ + t₁ * u₁ + 2 * t₂)) / 4) := by
  have hnumerator := hsLow.mul hgLow
  have hdenominator := hsHigh.mul hgHigh
  have hdenominatorBase : (1 * 2 : ℝ) ≠ 0 := by
    norm_num
  have hquotient := hnumerator.div hdenominator hdenominatorBase
  have hconstant : (2 * 1) * (1 * 2)⁻¹ = (1 : ℝ) := by
    norm_num
  have hlinear :
      (2 * 1) * (-(1 * u₁ + t₁ * 2) / (1 * 2) ^ 2) +
          (2 * g₁ + s₁ * 1) * (1 * 2)⁻¹ =
        (2 * g₁ + s₁ - (u₁ + 2 * t₁)) / 2 := by
    ring
  have hquadratic :
      (2 * 1) * ((1 * u₁ + t₁ * 2) ^ 2 / (1 * 2) ^ 3 -
          (1 * u₂ + t₁ * u₁ + t₂ * 2) / (1 * 2) ^ 2) +
          (2 * g₁ + s₁ * 1) * (-(1 * u₁ + t₁ * 2) / (1 * 2) ^ 2) +
        (2 * g₂ + s₁ * g₁ + s₂ * 1) * (1 * 2)⁻¹ =
      (2 * (2 * g₂ + s₁ * g₁ + s₂) - (2 * g₁ + s₁) * (u₁ + 2 * t₁) +
          (u₁ + 2 * t₁) ^ 2 - 2 * (u₂ + t₁ * u₁ + 2 * t₂)) / 4 := by
    ring_nf
  exact hquotient.congrCoefficients hconstant hlinear hquadratic

/-- Helper for Appendix Lemma A.6: multiplying the recovered radius factor by the
    independent radius shifts the same quadratic germ by one order. -/
theorem recoveryRadiusPathQuadraticGerm_of_componentGerms
    {sLow sHigh gLow gHigh : ℝ → ℝ}
    {s₁ s₂ t₁ t₂ g₁ g₂ u₁ u₂ : ℝ}
    (hsLow : HasQuadraticGerm sLow 2 s₁ s₂)
    (hsHigh : HasQuadraticGerm sHigh 1 t₁ t₂)
    (hgLow : HasQuadraticGerm gLow 1 g₁ g₂)
    (hgHigh : HasQuadraticGerm gHigh 2 u₁ u₂) :
    HasQuadraticGerm
      (fun r ↦ r * (sLow r * gLow r / (sHigh r * gHigh r)))
      0 1 ((2 * g₁ + s₁ - (u₁ + 2 * t₁)) / 2) := by
  have hradius : HasQuadraticGerm (fun r ↦ r) 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [quadraticModel]
  have hfactor := recoveryRadiusQuadraticGerm_of_componentGerms
    hsLow hsHigh hgLow hgHigh
  have hproduct := hradius.mul hfactor
  have hconstant : 0 * 1 = (0 : ℝ) := by
    norm_num
  have hlinear : 0 * ((2 * g₁ + s₁ - (u₁ + 2 * t₁)) / 2) + 1 * 1 = (1 : ℝ) := by
    ring
  have hquadratic :
      0 * ((2 * (2 * g₂ + s₁ * g₁ + s₂) - (2 * g₁ + s₁) * (u₁ + 2 * t₁) +
          (u₁ + 2 * t₁) ^ 2 - 2 * (u₂ + t₁ * u₁ + 2 * t₂)) / 4) +
          1 * ((2 * g₁ + s₁ - (u₁ + 2 * t₁)) / 2) + 0 * 1 =
        ((2 * g₁ + s₁ - (u₁ + 2 * t₁)) / 2) := by
    ring
  exact hproduct.congrCoefficients hconstant hlinear hquadratic

/-- Appendix Lemma A.6 companion: the five first-leg residual coordinates along the
independent-radius path have their explicit quadratic germs. -/
theorem independentFirstResidualQuadraticGerms (b P J : ℝ) :
    HasQuadraticGerm
        (fun r ↦ (independentFirstResiduals b r (2 + P * b * r) (1 + J * b * r)).1)
        3 (b * (2 * J + P - 2)) (J * P * b ^ 2 - 1) ∧
      HasQuadraticGerm
        (fun r ↦ (independentFirstResiduals b r (2 + P * b * r) (1 + J * b * r)).2.1)
        1 (-4 * b) (-2 * J * b ^ 2 - P * b ^ 2 + 6 * b ^ 2 - 3) ∧
      HasQuadraticGerm
        (fun r ↦ (independentFirstResiduals b r (2 + P * b * r) (1 + J * b * r)).2.2)
        1 (-2 * b) (6 * b ^ 2 - 1) ∧
      HasQuadraticGerm
        (fun r ↦ (independentFirstGradientResiduals b r (2 + P * b * r)).1)
        1 (-2 * b) (-2 * P * b ^ 2 / 3 + 4 * b ^ 2 - 2) ∧
      HasQuadraticGerm
        (fun r ↦ (independentFirstGradientResiduals b r (2 + P * b * r)).2)
        0 (b * (P + 6) / 3) (2 * P * b ^ 2 / 3 - 4 * b ^ 2 + 2) := by
  let X : ℝ → ℝ := fun r ↦ r
  let p : ℝ → ℝ := fun r ↦ 2 + P * b * r
  let h : ℝ → ℝ := fun r ↦ 1 + J * b * r
  let B : ℝ → ℝ := fun r ↦ 1 + 2 * b * r + r ^ 2
  let C : ℝ → ℝ := fun r ↦ (1 + b * r) ^ 2 + p r * r ^ 2 * (b + r) ^ 2
  let bPlusX : ℝ → ℝ := fun r ↦ b + r
  let onePlusBX : ℝ → ℝ := fun r ↦ 1 + b * r
  have hX : HasQuadraticGerm X 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [X, quadraticModel]
  have hp : HasQuadraticGerm p 2 (P * b) 0 := by
    apply (HasQuadraticGerm.model 2 (P * b) 0).congrFunction
    intro r
    simp [p, quadraticModel]
  have hh : HasQuadraticGerm h 1 (J * b) 0 := by
    apply (HasQuadraticGerm.model 1 (J * b) 0).congrFunction
    intro r
    simp [h, quadraticModel]
  have hB : HasQuadraticGerm B 1 (2 * b) 1 := by
    apply (HasQuadraticGerm.model 1 (2 * b) 1).congrFunction
    intro r
    simp [B, quadraticModel]
  have hC : HasQuadraticGerm C 1 (2 * b) (3 * b ^ 2) := by
    constructor
    · dsimp [C, p]
      fun_prop
    · apply EqModPow.of_factor
        (q := fun r ↦ P * b ^ 3 + 2 * P * b ^ 2 * r + P * b * r ^ 2 + 4 * b + 2 * r)
      · fun_prop
      · intro r
        simp only [C, p, quadraticModel]
        ring
  have hbPlusX : HasQuadraticGerm bPlusX b 1 0 := by
    apply (HasQuadraticGerm.model b 1 0).congrFunction
    intro r
    simp [bPlusX, quadraticModel]
  have honePlusBX : HasQuadraticGerm onePlusBX 1 b 0 := by
    apply (HasQuadraticGerm.model 1 b 0).congrFunction
    intro r
    simp [onePlusBX, quadraticModel]
  have hOneNe : (1 : ℝ) ≠ 0 := by
    norm_num
  have hBinv := hB.inv hOneNe
  have hCinv := hC.inv hOneNe
  have hpSq := hp.mul hp
  have hXSq := hX.mul hX
  have hbPlusXSq := hbPlusX.mul hbPlusX
  have honePlusBXSq := honePlusBX.mul honePlusBX
  have hhp := hh.mul hp
  have hfirstCorrection := (((hh.mul hpSq).mul hXSq).mul hbPlusXSq).mul hCinv
  have hAraw := (hhp.sub hfirstCorrection).add hBinv
  have hA : HasQuadraticGerm
      (fun r ↦ h r * p r -
        h r * (p r * p r) * (X r * X r) * (bPlusX r * bPlusX r) * (C r)⁻¹ +
          (B r)⁻¹)
      3 (b * (2 * J + P - 2)) (J * P * b ^ 2 - 1) := by
    apply hAraw.congrCoefficients
    · ring
    · ring
    · ring
  have hsecondCorrection :=
    (((((hh.mul hp).mul hX).mul hbPlusX).mul honePlusBX).mul hCinv)
  have hCraw := hBinv.sub hsecondCorrection
  have hCres : HasQuadraticGerm
      (fun r ↦ (B r)⁻¹ - h r * p r * X r * bPlusX r * onePlusBX r * (C r)⁻¹)
      1 (-4 * b)
      (-2 * J * b ^ 2 - P * b ^ 2 + 6 * b ^ 2 - 3) := by
    apply hCraw.congrCoefficients
    · ring
    · ring
    · ring
  have hDraw := (hh.sub ((hh.mul honePlusBXSq).mul hCinv)).add hBinv
  have hDres : HasQuadraticGerm
      (fun r ↦ h r - h r * (onePlusBX r * onePlusBX r) * (C r)⁻¹ + (B r)⁻¹)
      1 (-2 * b) (6 * b ^ 2 - 1) := by
    apply hDraw.congrCoefficients
    · ring
    · ring
    · ring
  have hTwoThirds := HasQuadraticGerm.model (2 / 3 : ℝ) 0 0
  have hpPlusOne := hp.add (HasQuadraticGerm.model 1 0 0)
  have hqCorrection := ((((hTwoThirds.mul hpPlusOne).mul hX).mul hbPlusX).mul hBinv)
  have hqRaw := (HasQuadraticGerm.model 1 0 0).sub hqCorrection
  have hq : HasQuadraticGerm
      (fun r ↦ quadraticModel 1 0 0 r -
        quadraticModel (2 / 3) 0 0 r * (p r + quadraticModel 1 0 0 r) *
          X r * bPlusX r * (B r)⁻¹)
      1 (-2 * b)
      (-2 * P * b ^ 2 / 3 + 4 * b ^ 2 - 2) := by
    apply hqRaw.congrCoefficients
    · ring
    · ring
    · ring
  have huCorrection := (((hTwoThirds.mul hpPlusOne).mul honePlusBX).mul hBinv)
  have huRaw := hp.sub huCorrection
  have hu : HasQuadraticGerm
      (fun r ↦ p r - quadraticModel (2 / 3) 0 0 r *
        (p r + quadraticModel 1 0 0 r) * onePlusBX r * (B r)⁻¹)
      0 (b * (P + 6) / 3)
      (2 * P * b ^ 2 / 3 - 4 * b ^ 2 + 2) := by
    apply huRaw.congrCoefficients
    · ring
    · ring
    · ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply hA.congrFunction
    intro r
    simp only [independentFirstResiduals, X, p, h, B, C, bPlusX,
      div_eq_mul_inv]
    ring
  · apply hCres.congrFunction
    intro r
    simp only [independentFirstResiduals, X, p, h, B, C, bPlusX, onePlusBX,
      div_eq_mul_inv]
    ring
  · apply hDres.congrFunction
    intro r
    simp only [independentFirstResiduals, p, h, B, C, onePlusBX,
      div_eq_mul_inv]
    ring
  · apply hq.congrFunction
    intro r
    simp only [independentFirstGradientResiduals, quadraticModel, X, p, B,
      bPlusX, div_eq_mul_inv, mul_inv_rev]
    ring
  · apply hu.congrFunction
    intro r
    simp only [independentFirstGradientResiduals, quadraticModel, p, B,
      onePlusBX, div_eq_mul_inv, mul_inv_rev]
    ring

end DFP.TwoLeg.Mixed
