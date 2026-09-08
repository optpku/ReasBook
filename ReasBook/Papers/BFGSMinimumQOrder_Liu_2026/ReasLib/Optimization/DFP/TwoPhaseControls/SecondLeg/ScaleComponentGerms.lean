module
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondOrderJet
public section
noncomputable section
namespace DFP.SecondLeg
open DFP.TwoLeg.Mixed
open DFP.TwoLeg

private theorem germId : HasQuadraticGerm (fun ε : ℝ => ε) 0 1 0 := by
  apply (HasQuadraticGerm.model 0 1 0).congrFunction
  intro r; simp [quadraticModel]

private theorem germConst (c : ℝ) : HasQuadraticGerm (fun _ : ℝ => c) c 0 0 := by
  refine ⟨by fun_prop, ?_⟩
  apply EqModPow.of_factor (q := fun _ => 0) (by fun_prop)
  intro ε; simp [quadraticModel]

private theorem germ_flat (c : ℝ) {f : ℝ → ℝ} (q : ℝ → ℝ) (hq : ContinuousAt q 0)
    (hfac : ∀ ε, f ε - c = q ε * ε ^ 3) (hcont : ContinuousAt f 0) :
    HasQuadraticGerm f c 0 0 := by
  refine ⟨hcont, ?_⟩
  apply EqModPow.of_factor (q := q) hq
  intro ε; have := hfac ε; simp only [quadraticModel]; linarith [this]

private theorem sqrtGerm {f : ℝ → ℝ} {c₀ c₁ c₂ s : ℝ}
    (hf : HasQuadraticGerm f c₀ c₁ c₂) (hs : 0 < s) (hc₀ : c₀ = s ^ 2) :
    HasQuadraticGerm (fun r => Real.sqrt (f r)) s (c₁/(2*s)) (c₂/(2*s) - c₁^2/(8*s^3)) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hfeq : ∀ r, f r / s^2 = (1:ℝ)/s^2 * f r := fun r => by ring
  have hg : HasQuadraticGerm (fun r => f r / s^2) 1 (c₁/s^2) (c₂/s^2) := by
    have h := (hf.constMul (1/s^2)).congrFunction hfeq
    apply h.congrCoefficients
    · rw [hc₀]; field_simp
    · field_simp
    · field_simp
  have hsqrtg := hg.sqrtOne
  have hval := hsqrtg.constMul s
  have hfun : ∀ r, Real.sqrt (f r) = s * Real.sqrt (f r / s^2) := by
    intro r
    rw [show f r / s^2 = (1/s^2) * f r by ring, Real.sqrt_mul (by positivity),
      show (1:ℝ)/s^2 = (1/s)^2 by ring, Real.sqrt_sq (by positivity)]
    field_simp
  apply (hval.congrFunction hfun).congrCoefficients
  · ring
  · field_simp
  · field_simp

-- generalized gap germ:  D germ (d0) 0 0, A,B arbitrary flat-ish, d0>0
-- gap = √((D - ε⁴A)² + 4(ε²B)²),  at ε=0 arg = d0², so gap germ (d0) 0 0
private theorem germGap {A B D : ℝ → ℝ} {Ac Bc d0 : ℝ}
    (hA : HasQuadraticGerm A Ac 0 0) (hB : HasQuadraticGerm B Bc 0 0)
    (hD : HasQuadraticGerm D d0 0 0) (hd0 : 0 < d0) :
    HasQuadraticGerm (fun ε => Real.sqrt ((D ε - ε^4 * A ε)^2 + 4*(ε^2 * B ε)^2)) d0 0 0 := by
  have hId2 : HasQuadraticGerm (fun ε : ℝ => ε^2) 0 0 1 := by
    have := germId.mul germId
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have hId4 : HasQuadraticGerm (fun ε : ℝ => ε^4) 0 0 0 := by
    have := hId2.mul hId2
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have he4A : HasQuadraticGerm (fun ε => ε^4 * A ε) 0 0 0 := by
    have := hId4.mul hA; apply this.congrCoefficients <;> ring
  have he2B : HasQuadraticGerm (fun ε => ε^2 * B ε) 0 0 Bc := by
    have := hId2.mul hB; apply this.congrCoefficients <;> ring
  have hDsub : HasQuadraticGerm (fun ε => D ε - ε^4 * A ε) d0 0 0 := by
    have := hD.sub he4A; apply this.congrCoefficients <;> ring
  have hDsubSq : HasQuadraticGerm (fun ε => (D ε - ε^4 * A ε)^2) (d0^2) 0 0 := by
    have := hDsub.mul hDsub
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have he2Bsq : HasQuadraticGerm (fun ε => (ε^2 * B ε)^2) 0 0 0 := by
    have := he2B.mul he2B
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have h4e2Bsq : HasQuadraticGerm (fun ε => 4*(ε^2 * B ε)^2) 0 0 0 := by
    have := he2Bsq.constMul 4; apply this.congrCoefficients <;> ring
  have hArg : HasQuadraticGerm (fun ε => (D ε - ε^4*A ε)^2 + 4*(ε^2*B ε)^2) (d0^2) 0 0 := by
    have := hDsubSq.add h4e2Bsq; apply this.congrCoefficients <;> ring
  have := sqrtGerm hArg hd0 rfl
  apply this.congrCoefficients <;> norm_num

private theorem germHigh {A B D : ℝ → ℝ} {Ac Bc d0 : ℝ}
    (hA : HasQuadraticGerm A Ac 0 0) (hB : HasQuadraticGerm B Bc 0 0)
    (hD : HasQuadraticGerm D d0 0 0) (hd0 : 0 < d0) :
    HasQuadraticGerm (fun ε => RealSymmetric2.high (ε^4 * A ε) (ε^2 * B ε) (D ε)) d0 0 0 := by
  have hId2 : HasQuadraticGerm (fun ε : ℝ => ε^2) 0 0 1 := by
    have := germId.mul germId
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have hId4 : HasQuadraticGerm (fun ε : ℝ => ε^4) 0 0 0 := by
    have := hId2.mul hId2
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have he4A : HasQuadraticGerm (fun ε => ε^4 * A ε) 0 0 0 := by
    have := hId4.mul hA; apply this.congrCoefficients <;> ring
  have hgap := germGap hA hB hD hd0
  have hsum : HasQuadraticGerm
      (fun ε => ε^4*A ε + D ε + Real.sqrt ((D ε - ε^4*A ε)^2 + 4*(ε^2*B ε)^2)) (2*d0) 0 0 := by
    have := (he4A.add hD).add hgap; apply this.congrCoefficients <;> ring
  have hhigh := hsum.constMul (1/2 : ℝ)
  apply (hhigh.congrCoefficients (by ring) (by ring) (by ring)).congrFunction
  intro ε; simp only [RealSymmetric2.high, RealSymmetric2.gap]; ring_nf

private theorem germLow {A B D : ℝ → ℝ} {Ac Bc d0 : ℝ}
    (hA : HasQuadraticGerm A Ac 0 0) (hB : HasQuadraticGerm B Bc 0 0)
    (hD : HasQuadraticGerm D d0 0 0) (hd0 : 0 < d0) :
    HasQuadraticGerm (fun ε => RealSymmetric2.low (ε^4 * A ε) (ε^2 * B ε) (D ε)) 0 0 0 := by
  have hId2 : HasQuadraticGerm (fun ε : ℝ => ε^2) 0 0 1 := by
    have := germId.mul germId
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have hId4 : HasQuadraticGerm (fun ε : ℝ => ε^4) 0 0 0 := by
    have := hId2.mul hId2
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have he4A : HasQuadraticGerm (fun ε => ε^4 * A ε) 0 0 0 := by
    have := hId4.mul hA; apply this.congrCoefficients <;> ring
  have hgap := germGap hA hB hD hd0
  have hsum : HasQuadraticGerm
      (fun ε => ε^4*A ε + D ε - Real.sqrt ((D ε - ε^4*A ε)^2 + 4*(ε^2*B ε)^2)) 0 0 0 := by
    have := (he4A.add hD).sub hgap; apply this.congrCoefficients <;> ring
  have hlow := hsum.constMul (1/2 : ℝ)
  apply (hlow.congrCoefficients (by ring) (by ring) (by ring)).congrFunction
  intro ε; simp only [RealSymmetric2.low, RealSymmetric2.gap]; ring_nf

private theorem germLowDenom {A B D : ℝ → ℝ} {Ac Bc d0 : ℝ}
    (hA : HasQuadraticGerm A Ac 0 0) (hB : HasQuadraticGerm B Bc 0 0)
    (hD : HasQuadraticGerm D d0 0 0) (hd0 : 0 < d0) :
    HasQuadraticGerm (fun ε => RealSymmetric2.lowDenom (ε^4 * A ε) (ε^2 * B ε) (D ε)) d0 0 0 := by
  have hId2 : HasQuadraticGerm (fun ε : ℝ => ε^2) 0 0 1 := by
    have := germId.mul germId
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have he2B : HasQuadraticGerm (fun ε => ε^2 * B ε) 0 0 Bc := by
    have := hId2.mul hB; apply this.congrCoefficients <;> ring
  have he2Bsq : HasQuadraticGerm (fun ε => (ε^2 * B ε)^2) 0 0 0 := by
    have := he2B.mul he2B
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have hlow0 := germLow hA hB hD hd0
  have hDmLow : HasQuadraticGerm (fun ε => D ε - RealSymmetric2.low (ε^4*A ε) (ε^2*B ε) (D ε)) d0 0 0 := by
    have := hD.sub hlow0; apply this.congrCoefficients <;> ring
  have hDmLowSq : HasQuadraticGerm (fun ε => (D ε - RealSymmetric2.low (ε^4*A ε) (ε^2*B ε) (D ε))^2) (d0^2) 0 0 := by
    have := hDmLow.mul hDmLow
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have hArg2 : HasQuadraticGerm
      (fun ε => (D ε - RealSymmetric2.low (ε^4*A ε) (ε^2*B ε) (D ε))^2 + (ε^2*B ε)^2) (d0^2) 0 0 := by
    have := hDmLowSq.add he2Bsq; apply this.congrCoefficients <;> ring
  have := sqrtGerm hArg2 hd0 rfl
  apply (this.congrCoefficients (by norm_num) (by norm_num) (by norm_num)).congrFunction
  intro ε; simp only [RealSymmetric2.lowDenom]

/-! ## FirstLeg factor germs (as functions of ε at symbolic p h) -/

section FirstLeg
variable (p h : ℝ)

-- FirstLeg subquantities a_F, b_F, d_F, q_F, v_F
private theorem germFLaF : HasQuadraticGerm
    (fun ε : ℝ => h*p - h*p^2*ε^6*(1+ε)^2/((1+ε^3)^2 + p*ε^6*(1+ε)^2) + 1/((1:ℝ)+2*ε^3+ε^4))
    (h*p+1) 0 0 := by
  have hC : HasQuadraticGerm (fun ε : ℝ => (1+ε^3)^2 + p*ε^6*(1+ε)^2) 1 0 0 :=
    germ_flat 1 (fun ε => 2 + ε^3 + p*ε^3*(1+ε)^2) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hB : HasQuadraticGerm (fun ε : ℝ => (1:ℝ)+2*ε^3+ε^4) 1 0 0 :=
    germ_flat 1 (fun ε => 2 + ε) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hInvB : HasQuadraticGerm (fun ε : ℝ => 1/((1:ℝ)+2*ε^3+ε^4)) 1 0 0 := by
    have := (germConst (1:ℝ)).div hB (by norm_num); apply this.congrCoefficients <;> norm_num
  have hNum : HasQuadraticGerm (fun ε : ℝ => h*p^2*ε^6*(1+ε)^2) 0 0 0 :=
    germ_flat 0 (fun ε => h*p^2*ε^3*(1+ε)^2) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hDiv : HasQuadraticGerm (fun ε : ℝ => h*p^2*ε^6*(1+ε)^2/((1+ε^3)^2 + p*ε^6*(1+ε)^2)) 0 0 0 := by
    have := hNum.div hC (by norm_num); apply this.congrCoefficients <;> norm_num
  have := ((germConst (h*p)).sub hDiv).add hInvB
  apply this.congrCoefficients <;> ring

private theorem germFLbF : HasQuadraticGerm
    (fun ε : ℝ => 1/((1:ℝ)+2*ε^3+ε^4) - h*p*ε^3*(1+ε)*(1+ε^3)/((1+ε^3)^2 + p*ε^6*(1+ε)^2)) 1 0 0 := by
  have hC : HasQuadraticGerm (fun ε : ℝ => (1+ε^3)^2 + p*ε^6*(1+ε)^2) 1 0 0 :=
    germ_flat 1 (fun ε => 2 + ε^3 + p*ε^3*(1+ε)^2) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hB : HasQuadraticGerm (fun ε : ℝ => (1:ℝ)+2*ε^3+ε^4) 1 0 0 :=
    germ_flat 1 (fun ε => 2 + ε) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hInvB : HasQuadraticGerm (fun ε : ℝ => 1/((1:ℝ)+2*ε^3+ε^4)) 1 0 0 := by
    have := (germConst (1:ℝ)).div hB (by norm_num); apply this.congrCoefficients <;> norm_num
  have hNum : HasQuadraticGerm (fun ε : ℝ => h*p*ε^3*(1+ε)*(1+ε^3)) 0 0 0 :=
    germ_flat 0 (fun ε => h*p*(1+ε)*(1+ε^3)) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hDiv : HasQuadraticGerm (fun ε : ℝ => h*p*ε^3*(1+ε)*(1+ε^3)/((1+ε^3)^2 + p*ε^6*(1+ε)^2)) 0 0 0 := by
    have := hNum.div hC (by norm_num); apply this.congrCoefficients <;> norm_num
  have := hInvB.sub hDiv
  apply this.congrCoefficients <;> ring

private theorem germFLdF : HasQuadraticGerm
    (fun ε : ℝ => h - h*(1+ε^3)^2/((1+ε^3)^2 + p*ε^6*(1+ε)^2) + 1/((1:ℝ)+2*ε^3+ε^4)) 1 0 0 := by
  have hC : HasQuadraticGerm (fun ε : ℝ => (1+ε^3)^2 + p*ε^6*(1+ε)^2) 1 0 0 :=
    germ_flat 1 (fun ε => 2 + ε^3 + p*ε^3*(1+ε)^2) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hB : HasQuadraticGerm (fun ε : ℝ => (1:ℝ)+2*ε^3+ε^4) 1 0 0 :=
    germ_flat 1 (fun ε => 2 + ε) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hInvB : HasQuadraticGerm (fun ε : ℝ => 1/((1:ℝ)+2*ε^3+ε^4)) 1 0 0 := by
    have := (germConst (1:ℝ)).div hB (by norm_num); apply this.congrCoefficients <;> norm_num
  have hNum : HasQuadraticGerm (fun ε : ℝ => h*(1+ε^3)^2) h 0 0 :=
    germ_flat h (fun ε => h*(2+ε^3)) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hDiv : HasQuadraticGerm (fun ε : ℝ => h*(1+ε^3)^2/((1+ε^3)^2 + p*ε^6*(1+ε)^2)) h 0 0 := by
    have := hNum.div hC (by norm_num); apply this.congrCoefficients <;> norm_num
  have := ((germConst h).sub hDiv).add hInvB
  apply this.congrCoefficients <;> norm_num

private theorem germFLqF : HasQuadraticGerm
    (fun ε : ℝ => 1 - 2*(p+1)*ε^3*(1+ε)/(3*((1:ℝ)+2*ε^3+ε^4))) 1 0 0 := by
  have hB : HasQuadraticGerm (fun ε : ℝ => 3*((1:ℝ)+2*ε^3+ε^4)) 3 0 0 :=
    germ_flat 3 (fun ε => 3*(2 + ε)) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hNum : HasQuadraticGerm (fun ε : ℝ => 2*(p+1)*ε^3*(1+ε)) 0 0 0 :=
    germ_flat 0 (fun ε => 2*(p+1)*(1+ε)) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hDiv : HasQuadraticGerm (fun ε : ℝ => 2*(p+1)*ε^3*(1+ε)/(3*((1:ℝ)+2*ε^3+ε^4))) 0 0 0 := by
    have := hNum.div hB (by norm_num); apply this.congrCoefficients <;> norm_num
  have := (germConst (1:ℝ)).sub hDiv
  apply this.congrCoefficients <;> ring

private theorem germFLvF : HasQuadraticGerm
    (fun ε : ℝ => p - 2*(p+1)*(1+ε^3)/(3*((1:ℝ)+2*ε^3+ε^4))) ((p-2)/3) 0 0 := by
  have hB : HasQuadraticGerm (fun ε : ℝ => 3*((1:ℝ)+2*ε^3+ε^4)) 3 0 0 :=
    germ_flat 3 (fun ε => 3*(2 + ε)) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hNum : HasQuadraticGerm (fun ε : ℝ => 2*(p+1)*(1+ε^3)) (2*(p+1)) 0 0 :=
    germ_flat (2*(p+1)) (fun ε => 2*(p+1)) (by fun_prop) (fun ε => by ring) (by fun_prop)
  have hDiv : HasQuadraticGerm (fun ε : ℝ => 2*(p+1)*(1+ε^3)/(3*((1:ℝ)+2*ε^3+ε^4))) (2*(p+1)/3) 0 0 := by
    have := hNum.div hB (by norm_num)
    apply this.congrCoefficients
    · field_simp
    · field_simp; ring
    · field_simp; ring
  have := (germConst p).sub hDiv
  apply this.congrCoefficients
  · field_simp; ring
  · ring
  · ring

/-- FirstLeg spectral high factor `H₁` germ. -/
private theorem germFLH (hh : 0 < h) : HasQuadraticGerm
    (fun ε : ℝ => (DFP.FirstLeg.spectralFactors ε p h).2) 1 0 0 := by
  have := germHigh (germFLaF p h) (germFLbF p h) (germFLdF p h) (by norm_num)
  exact this.congrFunction (fun ε => by rfl)

/-- FirstLeg spectral low denom `denom₁` germ. -/
private theorem germFLdenom : HasQuadraticGerm
    (fun ε : ℝ => RealSymmetric2.lowDenom
      (ε^4 * (h*p - h*p^2*ε^6*(1+ε)^2/((1+ε^3)^2 + p*ε^6*(1+ε)^2) + 1/((1:ℝ)+2*ε^3+ε^4)))
      (ε^2 * (1/((1:ℝ)+2*ε^3+ε^4) - h*p*ε^3*(1+ε)*(1+ε^3)/((1+ε^3)^2 + p*ε^6*(1+ε)^2)))
      (h - h*(1+ε^3)^2/((1+ε^3)^2 + p*ε^6*(1+ε)^2) + 1/((1:ℝ)+2*ε^3+ε^4))) 1 0 0 :=
  germLowDenom (germFLaF p h) (germFLbF p h) (germFLdF p h) (by norm_num)

/-- FirstLeg spectral low `low₁` germ. -/
private theorem germFLlow : HasQuadraticGerm
    (fun ε : ℝ => RealSymmetric2.low
      (ε^4 * (h*p - h*p^2*ε^6*(1+ε)^2/((1+ε^3)^2 + p*ε^6*(1+ε)^2) + 1/((1:ℝ)+2*ε^3+ε^4)))
      (ε^2 * (1/((1:ℝ)+2*ε^3+ε^4) - h*p*ε^3*(1+ε)*(1+ε^3)/((1+ε^3)^2 + p*ε^6*(1+ε)^2)))
      (h - h*(1+ε^3)^2/((1+ε^3)^2 + p*ε^6*(1+ε)^2) + 1/((1:ℝ)+2*ε^3+ε^4))) 0 0 0 :=
  germLow (germFLaF p h) (germFLbF p h) (germFLdF p h) (by norm_num)

/-- FirstLeg spectral low factor `L₁` germ (const `h*p`). -/
private theorem germFLL : HasQuadraticGerm
    (fun ε : ℝ => (DFP.FirstLeg.spectralFactors ε p h).1) (h*p) 0 0 := by
  -- L = (a_F * d_F - b_F^2) / H
  have hbsq : HasQuadraticGerm (fun ε : ℝ =>
      (1/((1:ℝ)+2*ε^3+ε^4) - h*p*ε^3*(1+ε)*(1+ε^3)/((1+ε^3)^2 + p*ε^6*(1+ε)^2))^2) 1 0 0 := by
    have := (germFLbF p h).mul (germFLbF p h)
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have hnum := ((germFLaF p h).mul (germFLdF p h)).sub hbsq
  have hH := germHigh (germFLaF p h) (germFLbF p h) (germFLdF p h) (by norm_num)
  have hL := hnum.div hH (by norm_num)
  apply hL.congrFunction (fun ε => by rfl) |>.congrCoefficients
  · ring
  · ring
  · ring

/-- FirstLeg gradient factor `Q₁` germ (const `1`). -/
private theorem germFLQ : HasQuadraticGerm
    (fun ε : ℝ => (DFP.FirstLeg.gradientFactors ε p h).1) 1 0 0 := by
  -- Q = ((d_F - low_F)*q_F - ε^4 * b_F * v_F) / denom_F
  have hId2 : HasQuadraticGerm (fun ε : ℝ => ε^2) 0 0 1 := by
    have := germId.mul germId
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have hId4 : HasQuadraticGerm (fun ε : ℝ => ε^4) 0 0 0 := by
    have := hId2.mul hId2
    apply (this.congrFunction (fun r => by ring)).congrCoefficients <;> ring
  have hDmLow := (germFLdF p h).sub (germFLlow p h)
  have hNum := (hDmLow.mul (germFLqF p)).sub
    ((hId4.mul (germFLbF p h)).mul (germFLvF p))
  have hQ := hNum.div (germFLdenom p h) (by norm_num)
  apply hQ.congrFunction (fun ε => by rfl) |>.congrCoefficients
  · ring
  · ring
  · ring

/-- FirstLeg gradient factor `U₁` germ (const `(p+1)/3`). -/
private theorem germFLU : HasQuadraticGerm
    (fun ε : ℝ => (DFP.FirstLeg.gradientFactors ε p h).2) ((p+1)/3) 0 0 := by
  -- U = (b_F*q_F + (d_F - low_F)*v_F) / denom_F
  have hDmLow := (germFLdF p h).sub (germFLlow p h)
  have hNum := ((germFLbF p h).mul (germFLqF p)).add (hDmLow.mul (germFLvF p))
  have hU := hNum.div (germFLdenom p h) (by norm_num)
  apply hU.congrFunction (fun ε => by rfl) |>.congrCoefficients
  · field_simp; ring
  · ring
  · ring

/-! ## SecondLeg subquantity germs -/

-- abbreviations for FirstLeg factors as ε-functions
private def Lf : ℝ → ℝ := fun ε => (DFP.FirstLeg.spectralFactors ε p h).1
private def Hf : ℝ → ℝ := fun ε => (DFP.FirstLeg.spectralFactors ε p h).2
private def Qf : ℝ → ℝ := fun ε => (DFP.FirstLeg.gradientFactors ε p h).1
private def Uf : ℝ → ℝ := fun ε => (DFP.FirstLeg.gradientFactors ε p h).2

private theorem gLf : HasQuadraticGerm (Lf p h) (h*p) 0 0 := germFLL p h
private theorem gHf (hh : 0 < h) : HasQuadraticGerm (Hf p h) 1 0 0 := germFLH p h hh
private theorem gQf : HasQuadraticGerm (Qf p h) 1 0 0 := germFLQ p h
private theorem gUf : HasQuadraticGerm (Uf p h) ((p+1)/3) 0 0 := germFLU p h

-- continuity of FirstLeg factors at 0
private theorem cLf : ContinuousAt (Lf p h) 0 := (gLf p h).continuousAt
private theorem cHf (hh : 0 < h) : ContinuousAt (Hf p h) 0 := (gHf p h hh).continuousAt
private theorem cQf : ContinuousAt (Qf p h) 0 := (gQf p h).continuousAt
private theorem cUf : ContinuousAt (Uf p h) 0 := (gUf p h).continuousAt

-- ε³-flat helper: an explicit ε³ factor times a continuous g has germ (0,0,0)
private theorem gFlatMul3 {g : ℝ → ℝ} (hg : ContinuousAt g 0) :
    HasQuadraticGerm (fun ε => ε^3 * g ε) 0 0 0 := by
  have hcont : ContinuousAt (fun ε : ℝ => ε^3 * g ε) 0 := by
    have : ContinuousAt (fun ε : ℝ => ε^3) 0 := by fun_prop
    exact this.mul hg
  exact germ_flat 0 g hg (fun ε => by ring) hcont

/-! ### SecondLeg subquantity germs (all of the form (const, 0, 0)) -/

-- w₁ = ε*L*Q - 2*H*U ; germ (-2*(p+1)/3, h*p, 0)
private theorem gW1 (hh : 0 < h) : HasQuadraticGerm
    (fun ε => ε * Lf p h ε * Qf p h ε - 2*(Hf p h ε * Uf p h ε)) (-2*((p+1)/3)) (h*p) 0 := by
  have hεLQ : HasQuadraticGerm (fun ε => ε * Lf p h ε * Qf p h ε) 0 (h*p) 0 := by
    have := (germId.mul (gLf p h)).mul (gQf p h)
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have h2HU := ((gHf p h hh).mul (gUf p h)).constMul 2
  have := hεLQ.sub h2HU
  apply this.congrCoefficients <;> ring

-- w₂ = H*U - 2ε³*L*Q ; germ ((p+1)/3, 0, 0)
private theorem gW2 (hh : 0 < h) : HasQuadraticGerm
    (fun ε => Hf p h ε * Uf p h ε - 2*ε^3*(Lf p h ε * Qf p h ε)) ((p+1)/3) 0 0 := by
  have hHU := (gHf p h hh).mul (gUf p h)
  have hcorr : HasQuadraticGerm (fun ε => 2*ε^3*(Lf p h ε * Qf p h ε)) 0 0 0 := by
    have := (gFlatMul3 (g := fun ε => 2*(Lf p h ε * Qf p h ε))
      (continuousAt_const.mul ((cLf p h).mul (cQf p h))))
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have := hHU.sub hcorr
  apply this.congrCoefficients <;> ring

-- abbreviations
private def w1 : ℝ → ℝ := fun ε => ε * Lf p h ε * Qf p h ε - 2*(Hf p h ε * Uf p h ε)
private def w2 : ℝ → ℝ := fun ε => Hf p h ε * Uf p h ε - 2*ε^3*(Lf p h ε * Qf p h ε)

private theorem gw1 (hh : 0 < h) : HasQuadraticGerm (w1 p h) (-2*((p+1)/3)) (h*p) 0 := gW1 p h hh
private theorem gw2 (hh : 0 < h) : HasQuadraticGerm (w2 p h) ((p+1)/3) 0 0 := gW2 p h hh
private theorem cw1 (hh : 0 < h) : ContinuousAt (w1 p h) 0 := (gw1 p h hh).continuousAt
private theorem cw2 (hh : 0 < h) : ContinuousAt (w2 p h) 0 := (gw2 p h hh).continuousAt

-- beta = ε³*L*Q*w₁ + H*U*w₂ ; germ (((p+1)/3)², 0, 0)
private theorem gBeta (hh : 0 < h) : HasQuadraticGerm
    (fun ε => ε^3 * (Lf p h ε * Qf p h ε * w1 p h ε) + Hf p h ε * Uf p h ε * w2 p h ε)
    (((p+1)/3)^2) 0 0 := by
  have hfirst := gFlatMul3 (g := fun ε => Lf p h ε * Qf p h ε * w1 p h ε)
    (((cLf p h).mul (cQf p h)).mul (cw1 p h hh))
  have hsecond := ((gHf p h hh).mul (gUf p h)).mul (gw2 p h hh)
  have := hfirst.add hsecond
  apply this.congrCoefficients <;> ring

-- gamma = ε⁶*L*w₁² + H*w₂² ; germ (((p+1)/3)², 0, 0)
private theorem gGamma (hh : 0 < h) : HasQuadraticGerm
    (fun ε => ε^6 * (Lf p h ε * w1 p h ε ^ 2) + Hf p h ε * w2 p h ε ^ 2)
    (((p+1)/3)^2) 0 0 := by
  have hfirst : HasQuadraticGerm (fun ε => ε^6 * (Lf p h ε * w1 p h ε ^ 2)) 0 0 0 := by
    apply germ_flat 0 (fun ε => ε^3 * (Lf p h ε * w1 p h ε ^ 2))
      (((continuousAt_id.pow 3).mul ((cLf p h).mul ((cw1 p h hh).pow 2))))
      (fun ε => by ring)
    have : ContinuousAt (fun ε : ℝ => ε^6) 0 := by fun_prop
    exact this.mul ((cLf p h).mul ((cw1 p h hh).pow 2))
  have hw2sq : HasQuadraticGerm (fun ε => w2 p h ε ^ 2) (((p+1)/3)^2) 0 0 := by
    have := (gw2 p h hh).mul (gw2 p h hh)
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have hsecond := (gHf p h hh).mul hw2sq
  have := hfirst.add hsecond
  apply this.congrCoefficients <;> ring

-- delta = L*Q² + H*U² ; germ (h*p + ((p+1)/3)², 0, 0)
private theorem gDelta (hh : 0 < h) : HasQuadraticGerm
    (fun ε => Lf p h ε * Qf p h ε ^ 2 + Hf p h ε * Uf p h ε ^ 2)
    (h*p + ((p+1)/3)^2) 0 0 := by
  have hQsq : HasQuadraticGerm (fun ε => Qf p h ε ^ 2) 1 0 0 := by
    have := (gQf p h).mul (gQf p h)
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have hUsq : HasQuadraticGerm (fun ε => Uf p h ε ^ 2) (((p+1)/3)^2) 0 0 := by
    have := (gUf p h).mul (gUf p h)
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have hfirst := (gLf p h).mul hQsq
  have hsecond := (gHf p h hh).mul hUsq
  have := hfirst.add hsecond
  apply this.congrCoefficients <;> ring

private def betaf : ℝ → ℝ := fun ε =>
  ε^3 * (Lf p h ε * Qf p h ε * w1 p h ε) + Hf p h ε * Uf p h ε * w2 p h ε
private def gammaf : ℝ → ℝ := fun ε =>
  ε^6 * (Lf p h ε * w1 p h ε ^ 2) + Hf p h ε * w2 p h ε ^ 2
private def deltaf : ℝ → ℝ := fun ε =>
  Lf p h ε * Qf p h ε ^ 2 + Hf p h ε * Uf p h ε ^ 2

private theorem gbeta (hh : 0 < h) : HasQuadraticGerm (betaf p h) (((p+1)/3)^2) 0 0 := gBeta p h hh
private theorem ggamma (hh : 0 < h) : HasQuadraticGerm (gammaf p h) (((p+1)/3)^2) 0 0 := gGamma p h hh
private theorem gdelta (hh : 0 < h) : HasQuadraticGerm (deltaf p h) (h*p + ((p+1)/3)^2) 0 0 := gDelta p h hh

-- The metric/gradient subquantities a, b, d, q, v as functions of ε.
private def af : ℝ → ℝ := fun ε =>
  Lf p h ε - ε^6 * Lf p h ε ^ 2 * w1 p h ε ^ 2 / gammaf p h ε
    + Lf p h ε ^ 2 * Qf p h ε ^ 2 / betaf p h ε
private def bf : ℝ → ℝ := fun ε =>
  -(ε^3 * Lf p h ε * Hf p h ε * w1 p h ε * w2 p h ε / gammaf p h ε)
    + Lf p h ε * Qf p h ε * Hf p h ε * Uf p h ε / betaf p h ε
private def df : ℝ → ℝ := fun ε =>
  Hf p h ε - Hf p h ε ^ 2 * w2 p h ε ^ 2 / gammaf p h ε
    + Hf p h ε ^ 2 * Uf p h ε ^ 2 / betaf p h ε
private def qf : ℝ → ℝ := fun ε =>
  Qf p h ε - ε^3 * deltaf p h ε * w1 p h ε / (3 * betaf p h ε)
private def vf : ℝ → ℝ := fun ε =>
  Uf p h ε - deltaf p h ε * w2 p h ε / (3 * betaf p h ε)

private theorem beta0 (hp1 : (p + 1) / 3 ≠ 0) : ((p+1)/3)^2 ≠ 0 := pow_ne_zero 2 hp1
private theorem gamma0 (hp1 : (p + 1) / 3 ≠ 0) : ((p+1)/3)^2 ≠ 0 := pow_ne_zero 2 hp1
private theorem beta3 (hp1 : (p + 1) / 3 ≠ 0) : (3 : ℝ) * ((p+1)/3)^2 ≠ 0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero 2 hp1)

-- value of a germ at 0 equals its constant coefficient.
private theorem germVal0 {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂) : f 0 = a₀ := by
  have hval := EqModPow.eq_at_zero_of_pos (n := 3) (Nat.zero_lt_succ 2) hf.eqMod
  simpa [quadraticModel] using hval

private theorem gammaf0 (hh : 0 < h) : gammaf p h 0 = ((p+1)/3)^2 :=
  germVal0 (ggamma p h hh)

private theorem betaf0 (hh : 0 < h) : betaf p h 0 = ((p+1)/3)^2 :=
  germVal0 (gbeta p h hh)

-- germ of b (const value 3*h*p/(p+1); linear/quad 0).
private theorem gbf (hh : 0 < h) (hp1 : (p + 1) / 3 ≠ 0) : HasQuadraticGerm (bf p h)
    ((h*p) * ((p+1)/3) * (((p+1)/3)^2)⁻¹) 0 0 := by
  have hnum1 : HasQuadraticGerm
      (fun ε => ε^3 * (Lf p h ε * Hf p h ε * w1 p h ε * w2 p h ε)) 0 0 0 :=
    gFlatMul3 (g := fun ε => Lf p h ε * Hf p h ε * w1 p h ε * w2 p h ε)
      ((((cLf p h).mul (cHf p h hh)).mul (cw1 p h hh)).mul (cw2 p h hh))
  have hterm1 : HasQuadraticGerm
      (fun ε => ε^3 * Lf p h ε * Hf p h ε * w1 p h ε * w2 p h ε / gammaf p h ε) 0 0 0 := by
    have := hnum1.div (ggamma p h hh) (gamma0 p hp1)
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have hnum2 := (((gLf p h).mul (gQf p h)).mul (gHf p h hh)).mul (gUf p h)
  have hterm2 := hnum2.div (gbeta p h hh) (beta0 p hp1)
  have hsum := (hterm1.neg).add hterm2
  apply (hsum.congrFunction (fun ε => by rw [bf])).congrCoefficients
  · ring
  · ring
  · ring

-- germ of d (const 1).
private theorem gdf (hh : 0 < h) (hp1 : (p + 1) / 3 ≠ 0) : HasQuadraticGerm (df p h) 1 0 0 := by
  have hHsq : HasQuadraticGerm (fun ε => Hf p h ε ^ 2) 1 0 0 := by
    have := (gHf p h hh).mul (gHf p h hh)
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have hw2sq : HasQuadraticGerm (fun ε => w2 p h ε ^ 2) (((p+1)/3)^2) 0 0 := by
    have := (gw2 p h hh).mul (gw2 p h hh)
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have hUsq : HasQuadraticGerm (fun ε => Uf p h ε ^ 2) (((p+1)/3)^2) 0 0 := by
    have := (gUf p h).mul (gUf p h)
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have hterm1 := (hHsq.mul hw2sq).div (ggamma p h hh) (gamma0 p hp1)
  have hterm2 := (hHsq.mul hUsq).div (gbeta p h hh) (beta0 p hp1)
  have hsum := ((gHf p h hh).sub hterm1).add hterm2
  have hp1' : (p : ℝ) + 1 ≠ 0 := by
    intro hz; apply hp1; rw [hz]; norm_num
  apply (hsum.congrFunction (fun ε => by simp only [df])).congrCoefficients
  · ring
  · ring
  · ring

-- germ of q (const 1, quad 0): correction has explicit ε³ ⇒ flat.
private theorem gqf (hh : 0 < h) (hp1 : (p + 1) / 3 ≠ 0) : HasQuadraticGerm (qf p h) 1 0 0 := by
  have hcorr : HasQuadraticGerm
      (fun ε => ε^3 * (deltaf p h ε * w1 p h ε / (3 * betaf p h ε))) 0 0 0 := by
    apply gFlatMul3 (g := fun ε => deltaf p h ε * w1 p h ε / (3 * betaf p h ε))
    have hden0 : (3 : ℝ) * betaf p h 0 ≠ 0 := by
      rw [betaf0 p h hh]; exact beta3 p hp1
    exact (((gdelta p h hh).continuousAt.mul (cw1 p h hh)).div
      (continuousAt_const.mul (gbeta p h hh).continuousAt) hden0)
  have := (gQf p h).sub hcorr
  apply (this.congrFunction (fun ε => by simp only [qf]; ring)).congrCoefficients <;> ring

-- germ of v (constants irrelevant for the chart).
private theorem gvf (hh : 0 < h) (hp1 : (p + 1) / 3 ≠ 0) : HasQuadraticGerm (vf p h)
    (((p+1)/3) - (h*p + ((p+1)/3)^2) * ((p+1)/3) * (3 * ((p+1)/3)^2)⁻¹) 0 0 := by
  have hden : HasQuadraticGerm (fun ε => 3 * betaf p h ε) (3 * ((p+1)/3)^2) 0 0 := by
    have := (germConst (3:ℝ)).mul (gbeta p h hh)
    apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring
  have hden0 : (3 : ℝ) * ((p+1)/3)^2 ≠ 0 := beta3 p hp1
  have hcorr' : HasQuadraticGerm
      (fun ε => deltaf p h ε * w2 p h ε / (3 * betaf p h ε))
      ((h*p + ((p+1)/3)^2) * ((p+1)/3) * (3 * ((p+1)/3)^2)⁻¹) 0 0 := by
    have hraw := ((gdelta p h hh).mul (gw2 p h hh)).div hden hden0
    apply hraw.congrCoefficients
    · ring
    · ring
    · ring
  have := (gUf p h).sub hcorr'
  apply (this.congrFunction (fun ε => by simp only [vf])).congrCoefficients <;> ring

-- continuity of a (only continuity is needed for metricA = ε⁴·a).
private theorem caf (hh : 0 < h) (hp1 : (p + 1) / 3 ≠ 0) : ContinuousAt (af p h) 0 := by
  have hgamma := (ggamma p h hh).continuousAt
  have hbeta := (gbeta p h hh).continuousAt
  have hcont : ContinuousAt (fun ε : ℝ =>
      Lf p h ε - ε^6 * Lf p h ε ^ 2 * w1 p h ε ^ 2 / gammaf p h ε
        + Lf p h ε ^ 2 * Qf p h ε ^ 2 / betaf p h ε) 0 := by
    have hc6 : ContinuousAt (fun ε : ℝ => ε^6) 0 := by fun_prop
    have hgamma0 : gammaf p h 0 ≠ 0 := by rw [gammaf0 p h hh]; exact gamma0 p hp1
    have hbeta0 : betaf p h 0 ≠ 0 := by rw [betaf0 p h hh]; exact beta0 p hp1
    have ht1 := (((hc6.mul ((cLf p h).pow 2)).mul ((cw1 p h hh).pow 2)).div
      hgamma hgamma0)
    have ht2 := (((cLf p h).pow 2).mul ((cQf p h).pow 2)).div hbeta hbeta0
    exact ((cLf p h).sub ht1).add ht2
  apply hcont.congr
  filter_upwards with ε
  rw [af]

-- germ of r² (0 0 1) and r⁴ (0 0 0)
private theorem gsq : HasQuadraticGerm (fun r : ℝ => r^2) 0 0 1 := by
  have := germId.mul germId
  apply (this.congrFunction (fun ε => by ring)).congrCoefficients <;> ring

-- metricA = r⁴·af has germ (0,0,0)
private theorem gmetricA (hh : 0 < h) (hp1 : (p + 1) / 3 ≠ 0) :
    HasQuadraticGerm (fun r => r^4 * af p h r) 0 0 0 := by
  apply germ_flat 0 (fun r => r * af p h r)
  · exact continuousAt_id.mul (caf p h hh hp1)
  · intro ε; ring
  · exact (by fun_prop : ContinuousAt (fun r : ℝ => r^4) 0).mul (caf p h hh hp1)

-- metricC = r²·bf has germ (0,0,c₂) with c₁ = 0
private theorem gmetricC (hh : 0 < h) (hp1 : (p + 1) / 3 ≠ 0) :
    HasQuadraticGerm (fun r => r^2 * bf p h r) 0 0
      ((h*p) * ((p+1)/3) * (((p+1)/3)^2)⁻¹) := by
  have := gsq.mul (gbf p h hh hp1)
  apply this.congrCoefficients <;> ring

-- gradientU = r·vf has germ (0, u₁, u₂)
private theorem gGradU (hh : 0 < h) (hp1 : (p + 1) / 3 ≠ 0) :
    HasQuadraticGerm (fun r => r * vf p h r)
      0 (((p+1)/3) - (h*p + ((p+1)/3)^2) * ((p+1)/3) * (3 * ((p+1)/3)^2)⁻¹) 0 := by
  have := germId.mul (gvf p h hh hp1)
  apply this.congrCoefficients <;> ring

-- pointwise chart matches lowGradientFactor definitionally
private theorem hpath_eq (r : ℝ) :
    lowGradientChartPath (fun r => r) (fun r => r^4 * af p h r)
      (fun r => r^2 * bf p h r) (fun r => df p h r) (fun r => qf p h r)
      (fun r => r * vf p h r) r = lowGradientFactor (r, p, h) := by
  simp only [lowGradientChartPath, lowGradientFactor, gradientFactors,
    af, bf, df, qf, vf, Lf, Hf, Qf, Uf, w1, w2, betaf, gammaf, deltaf,
    RealSymmetric2.low_apply, RealSymmetric2.gap_apply,
    RealSymmetric2.lowDenom_apply]
  have hsqrt : ∀ A D E : ℝ,
      Real.sqrt ((A - D)^2 + 4*E^2) = Real.sqrt ((D - A)^2 + 4*E^2) := by
    intro A D E; congr 1; ring
  rw [hsqrt]
  ring_nf

/-- Helper for Lemma 4.15 (Claim 2, `𝒢₂ = 1 + O(ε³)`): via the FirstLeg component germ tower
and the pure-algebra chart factorization, the pure second signed-scale derivative of the low
second-leg gradient factor vanishes at any transverse parameter with `0 < h` and `(p+1)/3 ≠ 0`. -/
theorem lowGradientFactor_scale_iteratedDeriv_two_eq_zero
    (hh : 0 < h) (hp1 : (p + 1) / 3 ≠ 0)
    (hregular : ContDiffAt ℝ 3 (fun r : ℝ => lowGradientFactor (r, p, h)) 0) :
    iteratedDeriv 2 (fun r : ℝ => lowGradientFactor (r, p, h)) 0 = 0 := by
  have hderiv := lowGradientFactor_scale_iteratedDeriv_two_eq_of_chartFactorization
    p h germId (gmetricA p h hh hp1) (gmetricC p h hh hp1) (gdf p h hh hp1)
    (gqf p h hh hp1) (gGradU p h hh hp1) (hpath_eq p h) hregular
  simpa using hderiv

end FirstLeg

end DFP.SecondLeg
