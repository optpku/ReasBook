module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AngleQuadraticTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AngleQuadraticTransport

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.FirstLeg

open DFP.TwoLeg.Mixed

/-- Helper for Infrastructure I.16a: transport a quadratic germ across equal
coefficient triples. -/
private theorem normG
    {f : ℝ → ℝ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (h : HasQuadraticGerm f a₀ a₁ a₂)
    (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
    HasQuadraticGerm f b₀ b₁ b₂ := h.congrCoefficients h₀ h₁ h₂

/-- Helper for Infrastructure I.16a: the identity path has its standard quadratic germ. -/
private lemma gid : HasQuadraticGerm (fun x : ℝ => x) 0 1 0 := by
  apply (HasQuadraticGerm.model 0 1 0).congrFunction
  intro x; simp [quadraticModel]

/-- Helper for Infrastructure I.16a: the square path has its standard quadratic germ. -/
private lemma gp2 : HasQuadraticGerm (fun x : ℝ => x ^ 2) 0 0 1 := by
  have hraw := gid.mul gid
  have h : HasQuadraticGerm (fun x : ℝ => x * x) 0 0 1 := by
    apply normG hraw
    · ring
    · ring
    · ring
  apply h.congrFunction
  intro x
  ring

/-- Helper for Infrastructure I.16a: the cube path has vanishing quadratic jet. -/
private lemma gp3 : HasQuadraticGerm (fun x : ℝ => x ^ 3) 0 0 0 := by
  have hraw := gp2.mul gid
  have h : HasQuadraticGerm (fun x => x ^ 2 * x) 0 0 0 := by
    apply normG hraw
    · ring
    · ring
    · ring
  apply h.congrFunction
  intro x
  ring

/-- Helper for Infrastructure I.16a: the fourth power has vanishing quadratic jet. -/
private lemma gp4 : HasQuadraticGerm (fun x : ℝ => x ^ 4) 0 0 0 := by
  have hraw := gp2.mul gp2
  have h : HasQuadraticGerm (fun x => x ^ 2 * x ^ 2) 0 0 0 := by
    apply normG hraw
    · ring
    · ring
    · ring
  apply h.congrFunction
  intro x
  ring

/-- Helper for Infrastructure I.16a: the sixth power has vanishing quadratic jet. -/
private lemma gp6 : HasQuadraticGerm (fun x : ℝ => x ^ 6) 0 0 0 := by
  have hraw := gp3.mul gp3
  have h : HasQuadraticGerm (fun x => x ^ 3 * x ^ 3) 0 0 0 := by
    apply normG hraw
    · ring
    · ring
    · ring
  apply h.congrFunction
  intro x
  ring

/-- Helper for Infrastructure I.16a: a constant path has its constant quadratic germ. -/
private lemma gc (c : ℝ) : HasQuadraticGerm (fun _ : ℝ => c) c 0 0 := by
  apply (HasQuadraticGerm.model c 0 0).congrFunction
  intro x; simp [quadraticModel]

/-- Helper for Infrastructure I.16a: the low chart quotient is flat when its component
germs have the displayed orders. -/
private theorem flatChartGerm
    (p h : ℝ)
    {a b d q v : ℝ → ℝ}
    (ha : HasQuadraticGerm a (h * p + 1) 0 0)
    (hb : HasQuadraticGerm b 1 0 0)
    (hd : HasQuadraticGerm d 1 0 0)
    (hq : HasQuadraticGerm q 1 0 0)
    (hv : HasQuadraticGerm v ((p - 2) / 3) 0 0) :
    HasQuadraticGerm
      (fun ε =>
        let A := ε ^ 4 * a ε
        let E := ε ^ 2 * b ε
        let D := d ε
        let low := RealSymmetric2.low A E D
        let den := RealSymmetric2.lowDenom A E D
        ((D - low) * q ε - ε ^ 4 * b ε * v ε) / den) 1 0 0 := by
  let A : ℝ → ℝ := fun ε => ε ^ 4 * a ε
  let E : ℝ → ℝ := fun ε => ε ^ 2 * b ε
  let D : ℝ → ℝ := d
  let R : ℝ → ℝ := fun ε => ε ^ 4 * b ε * v ε
  have hA : HasQuadraticGerm A 0 0 0 := by
    dsimp [A]
    apply normG (gp4.mul ha)
    · ring
    · ring
    · ring
  have hE : HasQuadraticGerm E 0 0 1 := by
    dsimp [E]
    apply normG (gp2.mul hb)
    · ring
    · ring
    · ring
  have hR : HasQuadraticGerm R 0 0 0 := by
    dsimp [R]
    apply normG ((gp4.mul hb).mul hv)
    · ring
    · ring
    · ring
  have hDA := hd.sub hA
  have hDAsqRaw := hDA.mul hDA
  have hDAsq0 : HasQuadraticGerm (fun ε => (D ε - A ε) * (D ε - A ε)) 1 0 0 := by
    have h : HasQuadraticGerm
        (fun ε => (D ε - A ε) * (D ε - A ε)) 1 0 0 := by
      apply normG hDAsqRaw
      · ring
      · ring
      · ring
    exact h
  let rad : ℝ → ℝ := fun ε => (D ε - A ε) ^ 2 + 4 * (E ε) ^ 2
  have hRad : HasQuadraticGerm rad 1 0 0 := by
    have h := hDAsq0.add (hE.mul hE |>.constMul 4)
    have hrad_eq : ∀ ε : ℝ,
        rad ε = (D ε - A ε) * (D ε - A ε) + 4 * (E ε * E ε) := by
      intro ε
      simp [rad, pow_two]
    have hcongr := h.congrFunction hrad_eq
    apply normG hcongr
    · ring
    · ring
    · ring
  let gap : ℝ → ℝ := fun ε => Real.sqrt (rad ε)
  have hGap : HasQuadraticGerm gap 1 0 0 := by
    have h := hRad.sqrtOne
    have hgap_eq : ∀ ε : ℝ, gap ε = Real.sqrt (rad ε) := by
      intro ε
      rfl
    have hcongr := h.congrFunction hgap_eq
    apply normG hcongr
    · ring
    · ring
    · ring
  let low : ℝ → ℝ := fun ε => (A ε + D ε - gap ε) / 2
  have hLow : HasQuadraticGerm low 0 0 0 := by
    have h := (hA.add hd).sub hGap
    have h' := h.constMul (1 / 2 : ℝ)
    have hlow_eq : ∀ ε : ℝ,
        low ε = (1 / 2 : ℝ) * (A ε + D ε - gap ε) := by
      intro ε
      simp [low]
      ring
    have hcongr := h'.congrFunction hlow_eq
    apply normG hcongr
    · ring
    · ring
    · ring
  have hDlow : HasQuadraticGerm (fun ε => D ε - low ε) 1 0 0 := by
    have h := hd.sub hLow
    apply normG h
    · ring
    · ring
    · ring
  let denRad : ℝ → ℝ := fun ε => (D ε - low ε) ^ 2 + (E ε) ^ 2
  have hDenRad : HasQuadraticGerm denRad 1 0 0 := by
    have hsqRaw := hDlow.mul hDlow
    have hsq : HasQuadraticGerm (fun ε => (D ε - low ε) ^ 2) 1 0 0 := by
      have hsq0 : HasQuadraticGerm
          (fun ε => (D ε - low ε) * (D ε - low ε)) 1 0 0 := by
          apply normG hsqRaw
          · ring
          · ring
          · ring
      apply hsq0.congrFunction
      intro ε
      ring
    have h := hsq.add (hE.mul hE)
    have hdenRad_eq : ∀ ε : ℝ,
        denRad ε = (D ε - low ε) ^ 2 + E ε * E ε := by
      intro ε
      simp [denRad, pow_two]
    have hcongr := h.congrFunction hdenRad_eq
    apply normG hcongr
    · ring
    · ring
    · ring
  let den : ℝ → ℝ := fun ε => Real.sqrt (denRad ε)
  have hDen : HasQuadraticGerm den 1 0 0 := by
    have h := hDenRad.sqrtOne
    have hden_eq : ∀ ε : ℝ, den ε = Real.sqrt (denRad ε) := by
      intro ε
      rfl
    have hcongr := h.congrFunction hden_eq
    apply normG hcongr
    · ring
    · ring
    · ring
  have hDlowQ : HasQuadraticGerm (fun ε => (D ε - low ε) * q ε) 1 0 0 := by
    have h := hDlow.mul hq
    apply normG h
    · ring
    · ring
    · ring
  have hNum : HasQuadraticGerm
      (fun ε => (D ε - low ε) * q ε - R ε) 1 0 0 := by
    have h := hDlowQ.sub hR
    apply normG h
    · ring
    · ring
    · ring
  have hden0 : (1 : ℝ) ≠ 0 := by norm_num
  have hQuot := hNum.div hDen hden0
  have hQuot' : HasQuadraticGerm
      (fun r => ((D r - low r) * q r - R r) / den r) 1 0 0 := by
      apply normG hQuot
      · ring
      · ring
      · ring
  apply hQuot'.congrFunction
  intro ε
  simp only [A, E, D, R, low, gap, rad, den, denRad,
    RealSymmetric2.low, RealSymmetric2.gap, RealSymmetric2.lowDenom]

/-- Infrastructure I.16a: the signed pure-scale slice of the first-leg low gradient
factor has a flat quadratic germ.  This source-facing theorem supplies the concrete
component certificate needed by the generic independent-radius chart transport. -/
theorem gradientFactors_low_flat (p h : ℝ) :
    HasQuadraticGerm
      (fun ε : ℝ => (gradientFactors ε p h).1) 1 0 0 := by
  let B : ℝ → ℝ := fun ε => 1 + 2 * ε ^ 3 + ε ^ 4
  let C : ℝ → ℝ := fun ε => (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
  let a : ℝ → ℝ := fun ε =>
    h * p - h * p ^ 2 * ε ^ 6 * (1 + ε) ^ 2 / C ε + 1 / B ε
  let b : ℝ → ℝ := fun ε =>
    1 / B ε - h * p * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / C ε
  let d : ℝ → ℝ := fun ε =>
    h - h * (1 + ε ^ 3) ^ 2 / C ε + 1 / B ε
  let q : ℝ → ℝ := fun ε =>
    1 - 2 * (p + 1) * ε ^ 3 * (1 + ε) / (3 * B ε)
  let v : ℝ → ℝ := fun ε =>
    p - 2 * (p + 1) * (1 + ε ^ 3) / (3 * B ε)
  have hB : HasQuadraticGerm B 1 0 0 := by
    have h := (gc 1).add ((gc 2).mul gp3) |>.add gp4
    have hB_eq : ∀ ε : ℝ, B ε = 1 + 2 * ε ^ 3 + ε ^ 4 := by
      intro ε
      simp [B]
    have hcongr := h.congrFunction hB_eq
    apply normG hcongr
    · ring
    · ring
    · ring
  have hBInv : HasQuadraticGerm (fun ε => (B ε)⁻¹) 1 0 0 := by
    have hB0 : (1 : ℝ) ≠ 0 := by norm_num
    have hraw := hB.inv hB0
    apply normG hraw
    · ring
    · ring
    · ring
  have hOneCube : HasQuadraticGerm (fun ε => 1 + ε ^ 3) 1 0 0 := by
    apply normG ((gc 1).add gp3)
    · ring
    · ring
    · ring
  have hOneCubeSq : HasQuadraticGerm (fun ε => (1 + ε ^ 3) ^ 2) 1 0 0 := by
    have hraw := hOneCube.mul hOneCube
    have hsq_eq : ∀ ε : ℝ,
        (1 + ε ^ 3) ^ 2 = (1 + ε ^ 3) * (1 + ε ^ 3) := by
      intro ε
      ring
    have hcongr := hraw.congrFunction hsq_eq
    apply normG hcongr
    · ring
    · ring
    · ring
  have hOneX : HasQuadraticGerm (fun ε => 1 + ε) 1 1 0 := by
    apply normG ((gc 1).add gid)
    · ring
    · ring
    · ring
  have hOneXSq : HasQuadraticGerm (fun ε => (1 + ε) ^ 2) 1 2 1 := by
    have hraw := hOneX.mul hOneX
    have hsq_eq : ∀ ε : ℝ, (1 + ε) ^ 2 = (1 + ε) * (1 + ε) := by
      intro ε
      ring
    have hcongr := hraw.congrFunction hsq_eq
    apply normG hcongr
    · ring
    · ring
    · ring
  have hC : HasQuadraticGerm C 1 0 0 := by
    have hterm := (((gc p).mul gp6).mul hOneXSq)
    have hraw := hOneCubeSq.add hterm
    have hC_eq : ∀ ε : ℝ,
        C ε = (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2 := by
      intro ε
      simp [C]
    have hcongr := hraw.congrFunction hC_eq
    apply normG hcongr
    · ring
    · ring
    · ring
  have hCInv : HasQuadraticGerm (fun ε => (C ε)⁻¹) 1 0 0 := by
    have hC0 : (1 : ℝ) ≠ 0 := by norm_num
    have hraw := hC.inv hC0
    apply normG hraw
    · ring
    · ring
    · ring
  have ha : HasQuadraticGerm a (h * p + 1) 0 0 := by
    have hcorr := (((((gc h).mul (gc (p ^ 2))).mul gp6).mul hOneXSq).mul hCInv)
    have hraw := ((gc (h * p)).sub hcorr).add hBInv
    have hnorm : HasQuadraticGerm
        (fun r => h * p - h * p ^ 2 * r ^ 6 * (1 + r) ^ 2 * (C r)⁻¹ + (B r)⁻¹)
        (h * p + 1) 0 0 := by
        apply normG hraw
        · ring
        · ring
        · ring
    apply hnorm.congrFunction
    intro ε
    simp only [a, B, C, div_eq_mul_inv]
    ring
  have hb : HasQuadraticGerm b 1 0 0 := by
    have hcorr := (((((gc (h * p)).mul gp3).mul hOneX).mul hOneCube).mul hCInv)
    have hraw := hBInv.sub hcorr
    have hnorm : HasQuadraticGerm
        (fun r => (B r)⁻¹ - h * p * r ^ 3 * (1 + r) * (1 + r ^ 3) * (C r)⁻¹)
        1 0 0 := by
        apply normG hraw
        · ring
        · ring
        · ring
    apply hnorm.congrFunction
    intro ε
    simp only [b, B, C, div_eq_mul_inv]
    ring
  have hd : HasQuadraticGerm d 1 0 0 := by
    have hcorr := ((((gc h).mul hOneCubeSq).mul hCInv))
    have hraw := ((gc h).sub hcorr).add hBInv
    have hnorm : HasQuadraticGerm
        (fun r => h - h * (1 + r ^ 3) ^ 2 * (C r)⁻¹ + (B r)⁻¹)
        1 0 0 := by
        apply normG hraw
        · ring
        · ring
        · ring
    apply hnorm.congrFunction
    intro ε
    simp only [d, B, C, div_eq_mul_inv]
    ring
  have hq : HasQuadraticGerm q 1 0 0 := by
    have hcorr := (((((gc (2 / 3 : ℝ)).mul (gc (p + 1))).mul gp3).mul hOneX).mul hBInv)
    have hraw := (gc 1).sub hcorr
    have hnorm : HasQuadraticGerm
        (fun r => 1 - (2 / 3 : ℝ) * (p + 1) * r ^ 3 * (1 + r) * (B r)⁻¹)
        1 0 0 := by
        apply normG hraw
        · ring
        · ring
        · ring
    apply hnorm.congrFunction
    intro ε
    change 1 - 2 * (p + 1) * ε ^ 3 * (1 + ε) / (3 * B ε) =
      1 - (2 / 3 : ℝ) * (p + 1) * ε ^ 3 * (1 + ε) * (B ε)⁻¹
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  have hv : HasQuadraticGerm v ((p - 2) / 3) 0 0 := by
    have hcorr := (((((gc (2 / 3 : ℝ)).mul (gc (p + 1))).mul hOneCube).mul hBInv))
    have hraw := (gc p).sub hcorr
    have hnorm : HasQuadraticGerm
        (fun r => p - (2 / 3 : ℝ) * (p + 1) * (1 + r ^ 3) * (B r)⁻¹)
        ((p - 2) / 3) 0 0 := by
        apply normG hraw
        · ring
        · ring
        · ring
    apply hnorm.congrFunction
    intro ε
    change p - 2 * (p + 1) * (1 + ε ^ 3) / (3 * B ε) =
      p - (2 / 3 : ℝ) * (p + 1) * (1 + ε ^ 3) * (B ε)⁻¹
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  have hflat := flatChartGerm p h ha hb hd hq hv
  apply hflat.congrFunction
  intro ε
  simp only [gradientFactors, a, b, d, q, v, B, C]

end DFP.FirstLeg
