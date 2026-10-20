module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap.Linearization
public import ReasLib.Optimization.DFP.TwoPhaseOrbit
public import ReasLib.Optimization.DFP.AbstractSecantStep.Wolfe
public import ReasLib.Analysis.Calculus.LocalCutoff.CenterStable
public import ReasLib.Analysis.Calculus.LocalInvariantGraph
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.GraphIterateBounds
public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterDisplacement
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterTailUniform
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterConvergence
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeTail
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngleDivergence
public import ReasLib.Topology.Real.VanishingStepModulo
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport
public import ReasLib.Topology.Sequences.Interleave
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepLength
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientLimit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PhaseRadiusApproximation
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointCorrection
import all ReasLib.Geometry.Euclidean.Plane.Rotation
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import all ReasLib.Optimization.DFP.SpectralRecovery
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve
import all ReasLib.Analysis.Calculus.LocalInvariantGraph

/-!
# The separate spectral recurrence of Section 6

The regular one-step formulas below are the exact inverse DFP update in the
current eigenbasis. The two controls keep the same cycle scale while the
intermediate eigenbasis changes. The signed two-step map and its linearization
are those of `cm-two-step-map`, independently of the polar construction.

The source C⁷ graph is constructed from uniform C⁸ zero-start graph-transform
iterates and Arzelà–Ascoli. `centerProposition` includes the literal initialization,
infinite actual recurrence and inverse-cubic scale law for every sufficiently
small positive initial scale. The Section 6.3 interfaces retain the same physical
orbit, source frame first crossings, cancellation constants and limiting circle.
No polar or earlier counterexample existence theorem is used here.
-/

public section

noncomputable section

open Filter
open scoped Asymptotics EuclideanSpace Matrix Topology

namespace DFPWolfe.V21.CenterManifold

/-- Helper for cm-center-proposition: the regular secant energy denominator
`D = 1 + 2μr + r²` in cm-regular-step. -/
def regularDenominator (r μ : ℝ) : ℝ :=
  1 + 2 * μ * r + r ^ 2

/-- Helper for cm-center-proposition: the regular inverse-metric energy
`E = pr²(r + μ)² + (1 + μr)²` in cm-regular-step. -/
def regularEnergy (p r μ : ℝ) : ℝ :=
  p * r ^ 2 * (r + μ) ^ 2 + (1 + μ * r) ^ 2

/-- Helper for cm-center-proposition: the three source entries `(a₀,b₀,d₀)`
encode the next matrix as `!![a₀, r*b₀; r*b₀, d₀]`. -/
def regularEntries (p h r μ : ℝ) : ℝ × ℝ × ℝ :=
  let D := regularDenominator r μ
  let E := regularEnergy p r μ
  (h * p * r ^ 2 * (1 + μ * r) ^ 2 / E + r ^ 2 / D,
    1 / D - h * p * r * (r + μ) * (1 + μ * r) / E,
    h * p * r ^ 2 * (r + μ) ^ 2 / E + 1 / D)

/-- Helper for cm-center-proposition: the exact regular updated inverse Hessian
in the incoming eigenbasis, before rotating to its new eigenbasis. -/
def regularMetric (p h r μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let a := regularEntries p h r μ
  !![a.1, r * a.2.1; r * a.2.1, a.2.2]

/-- Helper for cm-center-proposition: the low diagonal entry of the regular matrix. -/
theorem regularMetric_low (p h r μ : ℝ) :
    regularMetric p h r μ 0 0 = (regularEntries p h r μ).1 := by
  rfl

/-- Helper for cm-center-proposition: the upper off-diagonal entry of the regular matrix. -/
theorem regularMetric_upper (p h r μ : ℝ) :
    regularMetric p h r μ 0 1 = r * (regularEntries p h r μ).2.1 := by
  rfl

/-- Helper for cm-center-proposition: the lower off-diagonal entry of the regular matrix. -/
theorem regularMetric_lower (p h r μ : ℝ) :
    regularMetric p h r μ 1 0 = r * (regularEntries p h r μ).2.1 := by
  rfl

/-- Helper for cm-center-proposition: the high diagonal entry of the regular matrix. -/
theorem regularMetric_high (p h r μ : ℝ) :
    regularMetric p h r μ 1 1 = (regularEntries p h r μ).2.2 := by
  rfl

/-- Helper for cm-center-proposition: the normalized gradient coordinates
`(q₁,q₂)` with actual incoming-frame vector `(q₁,r*q₂)`. -/
def regularGradientResiduals (p r μ τ : ℝ) : ℝ × ℝ :=
  let D := regularDenominator r μ
  (1 - τ * (p + 1) * r * (r + μ) / D,
    p - τ * (p + 1) * (1 + μ * r) / D)

/-- Helper for cm-center-proposition: the actual normalized updated gradient
in the incoming eigenbasis. -/
def regularGradient (p r μ τ : ℝ) : Fin 2 → ℝ :=
  let q := regularGradientResiduals p r μ τ
  ![q.1, r * q.2]

/-- Helper for cm-center-proposition: the source scalar denominator is strictly
positive whenever `|μ| < 1`. -/
theorem regularDenominator_pos (r μ : ℝ) (hμ : |μ| < 1) :
    0 < regularDenominator r μ := by
  have hμsq : μ ^ 2 < 1 := by
    nlinarith [abs_lt.mp hμ, sq_abs μ]
  unfold regularDenominator
  nlinarith [sq_nonneg (r + μ)]

/-- Helper for cm-center-proposition: the source inverse-metric energy is
strictly positive for positive shape and `|μ| < 1`. -/
theorem regularEnergy_pos (p r μ : ℝ) (hp : 0 < p) (hμ : |μ| < 1) :
    0 < regularEnergy p r μ := by
  have hnonneg : 0 ≤ p * r ^ 2 * (r + μ) ^ 2 := by positivity
  by_cases hlinear : 1 + μ * r = 0
  · have hr : r ≠ 0 := by
      intro hr
      simp [hr] at hlinear
    have hrμ : r + μ ≠ 0 := by
      intro hrμ
      have hμsq : μ ^ 2 < 1 := by
        nlinarith [abs_lt.mp hμ, sq_abs μ]
      nlinarith
    unfold regularEnergy
    exact add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos hp (sq_pos_of_ne_zero hr)) (sq_pos_of_ne_zero hrμ))
      (sq_nonneg _)
  · unfold regularEnergy
    exact add_pos_of_nonneg_of_pos hnonneg (sq_pos_of_ne_zero hlinear)

/-- Helper for cm-center-proposition: the three raw energies in cm-single-update
have the source's canceled factors in spectral coordinates. -/
theorem spectralEnergyIdentities (z : DFP.AbstractSecantStep (Fin 2))
    (p h r μ G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * r])
    (hA : z.secantMatrix = !![1, μ; μ, 1]) :
    z.gradient ⬝ᵥ z.preconditionedGradient = h * p * G ^ 2 * r ^ 2 * (p + 1) ∧
      z.preconditionedGradient ⬝ᵥ (z.secantMatrix *ᵥ z.preconditionedGradient) =
        h ^ 2 * p ^ 2 * G ^ 2 * r ^ 2 * regularDenominator r μ ∧
      (z.secantMatrix *ᵥ z.preconditionedGradient) ⬝ᵥ
          (z.inverseHessian *ᵥ (z.secantMatrix *ᵥ z.preconditionedGradient)) =
        h ^ 3 * p ^ 2 * G ^ 2 * r ^ 2 * regularEnergy p r μ := by
  rw [DFP.AbstractSecantStep.preconditionedGradient_def, hH, hg, hA]
  simp only [regularDenominator, regularEnergy]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · ring
  · constructor
    · ring
    · ring

/-- Helper for cm-center-proposition: positivity of the actual step energies
makes every canceled spectral factor nonzero. -/
theorem spectralParameters_ne_zero (z : DFP.AbstractSecantStep (Fin 2))
    (p h r μ G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * r])
    (hA : z.secantMatrix = !![1, μ; μ, 1]) :
    h ≠ 0 ∧ p ≠ 0 ∧ G ≠ 0 ∧ r ≠ 0 ∧
      regularDenominator r μ ≠ 0 ∧ regularEnergy p r μ ≠ 0 := by
  obtain ⟨_, hβ, hγ⟩ := spectralEnergyIdentities z p h r μ G hH hg hA
  have hβne := z.stepLengthDenominator_ne_zero
  have hγne := ne_of_gt z.secantImageEnergy_pos
  rw [hβ] at hβne
  rw [hγ] at hγne
  have hh : h ≠ 0 := by
    intro hh
    simp [hh] at hβne
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hβne
  have hG : G ≠ 0 := by
    intro hG
    simp [hG] at hβne
  have hr : r ≠ 0 := by
    intro hr
    simp [hr] at hβne
  exact ⟨hh, hp, hG, hr, right_ne_zero_of_mul hβne, right_ne_zero_of_mul hγne⟩

/-- Helper for cm-center-proposition: cm-single-step has the exact regular
spectral displacement `−G*τ*(p+1)*r/D * (r,1)`. -/
theorem spectralDisplacement (z : DFP.AbstractSecantStep (Fin 2))
    (p h r μ G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * r])
    (hA : z.secantMatrix = !![1, μ; μ, 1]) :
    z.displacement = (-(G * z.tau * (p + 1) * r / regularDenominator r μ)) •
      ![r, (1 : ℝ)] := by
  obtain ⟨hδ, hβ, _⟩ := spectralEnergyIdentities z p h r μ G hH hg hA
  obtain ⟨hh, hp, hG, hr, hD, _⟩ :=
    spectralParameters_ne_zero z p h r μ G hH hg hA
  rw [DFP.AbstractSecantStep.preconditionedGradient_def] at hδ hβ
  rw [z.displacement_def, z.stepLength_def, hδ, hβ,
    z.preconditionedGradient_def, hH, hg]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hh, hp, hG, hr, hD]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hh, hp, hG, hr, hD]

/-- Helper for cm-center-proposition: the exact next gradient is the source
regular `(q₁,r*q₂)` vector, multiplied by its incoming amplitude. -/
theorem spectralGradientUpdate (z : DFP.AbstractSecantStep (Fin 2))
    (p h r μ G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * r])
    (hA : z.secantMatrix = !![1, μ; μ, 1]) :
    z.nextGradient = G • regularGradient p r μ z.tau := by
  rw [z.nextGradient_def, z.gradientChange_def,
    spectralDisplacement z p h r μ G hH hg hA, hA, hg]
  unfold regularGradient regularGradientResiduals
  ext i
  fin_cases i
  · simp
    ring
  · simp
    ring

/-- Helper for cm-center-proposition: the source entries of cm-regular-step are
the actual inverse DFP matrix, without a remaining singular power of `r`. -/
theorem spectralMetricUpdate (z : DFP.AbstractSecantStep (Fin 2))
    (p h r μ G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * r])
    (hA : z.secantMatrix = !![1, μ; μ, 1]) :
    z.nextInverseHessian = regularMetric p h r μ := by
  obtain ⟨hh, hp, hG, hr, hD, hE⟩ :=
    spectralParameters_ne_zero z p h r μ G hH hg hA
  have hgCoord : z.gradient = ![G, G * (p * r)] := by
    rw [hg]
    ext i
    fin_cases i
    · simp
    · simp
  have hβ :
      (h * p * r ^ 2 * G) * (1 * (h * p * r ^ 2 * G) + μ * (h * (G * (p * r)))) +
        (h * (G * (p * r))) * (μ * (h * p * r ^ 2 * G) + 1 * (h * (G * (p * r)))) =
      h ^ 2 * p ^ 2 * G ^ 2 * r ^ 2 * regularDenominator r μ := by
    simp only [regularDenominator]
    ring
  have hγ :
      (h * p * r ^ 2) * (1 * (h * p * r ^ 2 * G) + μ * (h * (G * (p * r)))) ^ 2 +
        h * (μ * (h * p * r ^ 2 * G) + 1 * (h * (G * (p * r)))) ^ 2 =
      h ^ 3 * p ^ 2 * G ^ 2 * r ^ 2 * regularEnergy p r μ := by
    simp only [regularEnergy]
    ring
  rw [z.nextInverseHessian_eigenframe (h * p * r ^ 2) h G (G * (p * r))
    1 μ 1 hH hgCoord hA, hβ, hγ]
  apply Matrix.ext
  intro i j
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl
  · rcases hj with rfl | rfl
    · simp only [regularMetric_low, regularEntries, Matrix.of_apply, Matrix.cons_val_zero]
      field_simp [hh, hp, hG, hr, hD, hE]
      simp only [regularDenominator, regularEnergy]
      ring
    · simp only [regularMetric_upper, regularEntries, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp [hh, hp, hG, hr, hD, hE]
      ring
  · rcases hj with rfl | rfl
    · simp only [regularMetric_lower, regularEntries, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp [hh, hp, hG, hr, hD, hE]
      ring
    · simp only [regularMetric_high, regularEntries, Matrix.of_apply,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp [hh, hp, hG, hr, hD, hE]
      simp only [regularDenominator, regularEnergy]
      ring

/-- Helper for cm-center-proposition: the determinant of the regular updated
matrix is exactly `h*p*r²*D/E`, as in cm-regular-step. -/
theorem regularMetric_det (p h r μ : ℝ)
    (hD : regularDenominator r μ ≠ 0) (hE : regularEnergy p r μ ≠ 0) :
    (regularMetric p h r μ).det =
      h * p * r ^ 2 * regularDenominator r μ / regularEnergy p r μ := by
  rw [Matrix.det_fin_two, regularMetric_low, regularMetric_high,
    regularMetric_upper, regularMetric_lower]
  dsimp only [regularEntries]
  field_simp [hD, hE]
  simp only [regularDenominator, regularEnergy]
  ring

/-- Helper for cm-center-proposition: the nonsingular source step extends at
`r = 0` to the matrix `diag(0,1)`. -/
theorem regularMetric_zero (p h μ : ℝ) :
    regularMetric p h 0 μ = Matrix.diagonal ![(0 : ℝ), 1] := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [regularMetric, regularEntries, regularDenominator, regularEnergy]
    · simp [regularMetric, regularEntries, regularDenominator, regularEnergy]
  · fin_cases j
    · simp [regularMetric, regularEntries, regularDenominator, regularEnergy]
    · simp [regularMetric, regularEntries, regularDenominator, regularEnergy]

/-- Helper for cm-center-proposition: the source high eigenvalue and removable
low factor `(ℓ,λ)` in cm-regular-step. -/
def regularSpectrum (p h r μ : ℝ) : ℝ × ℝ :=
  let a := regularEntries p h r μ
  let highValue := RealSymmetric2.high a.1 (r * a.2.1) a.2.2
  (h * p * regularDenominator r μ / (regularEnergy p r μ * highValue), highValue)

/-- Helper for cm-center-proposition: the source rotated numerators `(X,Y)`
and normalization `N`, with `c₀ = d₀ − r²ℓ`. -/
def regularRotatedData (p h r μ τ : ℝ) : (ℝ × ℝ) × ℝ :=
  let a := regularEntries p h r μ
  let spectrum := regularSpectrum p h r μ
  let q := regularGradientResiduals p r μ τ
  let c := a.2.2 - r ^ 2 * spectrum.1
  ((c * q.1 - r ^ 2 * a.2.1 * q.2, a.2.1 * q.1 + c * q.2),
    Real.sqrt (c ^ 2 + r ^ 2 * a.2.1 ^ 2))

/-- Helper for cm-center-proposition: the exact regular map stores
`(rnew/r,pnew,hnew,Gnew/G)` from cm-regular-step. -/
def regularStep (p h r μ τ : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  let spectrum := regularSpectrum p h r μ
  let rotated := regularRotatedData p h r μ τ
  (spectrum.1 * rotated.1.1 / (spectrum.2 * rotated.1.2),
    spectrum.2 * rotated.1.2 ^ 2 / (spectrum.1 * rotated.1.1 ^ 2),
    spectrum.2, rotated.1.1 / rotated.2)

/-- Helper for cm-center-proposition: the source entries at zero radius are
`(a₀,b₀,d₀) = (0,1,1)`. -/
theorem regularEntries_zero (p h μ : ℝ) : regularEntries p h 0 μ = (0, 1, 1) := by
  simp [regularEntries, regularDenominator, regularEnergy]

/-- Helper for cm-center-proposition: the removable spectrum at zero radius
is `(ℓ,λ) = (hp,1)`. -/
theorem regularSpectrum_zero (p h μ : ℝ) : regularSpectrum p h 0 μ = (h * p, 1) := by
  simp [regularSpectrum, regularEntries_zero, regularDenominator, regularEnergy,
    RealSymmetric2.high_apply, RealSymmetric2.gap_apply]

/-- Helper for cm-center-proposition: at zero radius `X=N=1` and
`Y=(1−τ)(p+1)`. -/
theorem regularRotatedData_zero (p h μ τ : ℝ) :
    regularRotatedData p h 0 μ τ = ((1, (1 - τ) * (p + 1)), 1) := by
  simp [regularRotatedData, regularEntries_zero, regularSpectrum_zero,
    regularGradientResiduals, regularDenominator]
  ring

/-- Helper for cm-center-proposition: the regular zero-radius step retains
its nontrivial radius multiplier and shape coordinate. -/
theorem regularStep_zero (p h μ τ : ℝ) :
    regularStep p h 0 μ τ =
      (h * p / ((1 - τ) * (p + 1)), ((1 - τ) * (p + 1)) ^ 2 / (h * p), 1, 1) := by
  simp [regularStep, regularSpectrum_zero, regularRotatedData_zero]

/-- Helper for cm-center-proposition: the two exact limiting stages have the
source alternating shape cycle `2 ↦ 1/2 ↦ 2` and radius factors `2`, `1/2`. -/
theorem limitingAlternatingCycle :
    regularStep 2 1 0 0 (2 / 3) = (2, 1 / 2, 1, 1) ∧
      regularStep (1 / 2) 1 0 0 (1 / 3) = (1 / 2, 2, 1, 1) := by
  rw [regularStep_zero, regularStep_zero]
  norm_num

/-- Helper for cm-center-proposition: the removable low factor reconstructs
the actual lower eigenvalue of the regular updated matrix. -/
theorem regularSpectrum_low (p h r μ : ℝ)
    (hD : regularDenominator r μ ≠ 0) (hE : regularEnergy p r μ ≠ 0)
    (hhigh : RealSymmetric2.high (regularEntries p h r μ).1
      (r * (regularEntries p h r μ).2.1) (regularEntries p h r μ).2.2 ≠ 0) :
    r ^ 2 * (regularSpectrum p h r μ).1 =
      RealSymmetric2.low (regularEntries p h r μ).1
        (r * (regularEntries p h r μ).2.1) (regularEntries p h r μ).2.2 := by
  have hdet := regularMetric_det p h r μ hD hE
  rw [Matrix.det_fin_two, regularMetric_low, regularMetric_high,
    regularMetric_upper, regularMetric_lower] at hdet
  rw [RealSymmetric2.low_eq_det_div_high_of_ne _ _ _ hhigh]
  unfold regularSpectrum
  dsimp only
  rw [← pow_two] at hdet
  rw [hdet]
  field_simp

/-- Helper for cm-center-proposition: the oriented frame in cm-regular-step
has columns `(c₀,−rb₀)/N` and `(rb₀,c₀)/N`. -/
def regularFrame (p h r μ τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let a := regularEntries p h r μ
  let c := a.2.2 - r ^ 2 * (regularSpectrum p h r μ).1
  (regularRotatedData p h r μ τ).2⁻¹ • !![c, r * a.2.1; -(r * a.2.1), c]

/-- Helper for cm-center-proposition: rotation into the new source frame
sends the actual normalized gradient to `(X,rY)/N`. -/
theorem regularFrame_gradient (p h r μ τ : ℝ) :
    (regularFrame p h r μ τ).transpose *ᵥ regularGradient p r μ τ =
      ![(regularRotatedData p h r μ τ).1.1 / (regularRotatedData p h r μ τ).2,
        r * (regularRotatedData p h r μ τ).1.2 / (regularRotatedData p h r μ τ).2] := by
  unfold regularFrame regularGradient regularRotatedData
  ext i
  fin_cases i
  · simp [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, div_eq_mul_inv]
    ring
  · simp [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, div_eq_mul_inv]
    ring

/-- Helper for cm-center-proposition: the source normalization `N` is the
normalization of the actual lower-eigenvector branch. -/
theorem regularNormalizer_eq_lowDenom (p h r μ τ : ℝ)
    (hD : regularDenominator r μ ≠ 0) (hE : regularEnergy p r μ ≠ 0)
    (hhigh : RealSymmetric2.high (regularEntries p h r μ).1
      (r * (regularEntries p h r μ).2.1) (regularEntries p h r μ).2.2 ≠ 0) :
    (regularRotatedData p h r μ τ).2 =
      RealSymmetric2.lowDenom (regularEntries p h r μ).1
        (r * (regularEntries p h r μ).2.1) (regularEntries p h r μ).2.2 := by
  rw [RealSymmetric2.lowDenom_apply, ← regularSpectrum_low p h r μ hD hE hhigh]
  unfold regularRotatedData
  dsimp only
  congr 1
  ring

/-- Helper for cm-center-proposition: the source frame is precisely the
canonical oriented eigenframe of the actual regular updated matrix. -/
theorem regularFrame_eq_lowEigenframe (p h r μ τ : ℝ)
    (hD : regularDenominator r μ ≠ 0) (hE : regularEnergy p r μ ≠ 0)
    (hhigh : RealSymmetric2.high (regularEntries p h r μ).1
      (r * (regularEntries p h r μ).2.1) (regularEntries p h r μ).2.2 ≠ 0) :
    regularFrame p h r μ τ = EuclideanPlane.frame
      (RealSymmetric2.lowVector (regularEntries p h r μ).1
        (r * (regularEntries p h r μ).2.1) (regularEntries p h r μ).2.2) := by
  have hlow := regularSpectrum_low p h r μ hD hE hhigh
  have hnormal := regularNormalizer_eq_lowDenom p h r μ τ hD hE hhigh
  rw [RealSymmetric2.lowVector_apply]
  unfold RealSymmetric2.lowRaw
  unfold regularFrame
  dsimp only
  rw [hnormal]
  apply Matrix.ext
  intro i j
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl
  · rcases hj with rfl | rfl
    · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply, ← hlow]
    · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply, ← hlow]
  · rcases hj with rfl | rfl
    · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply, ← hlow]
    · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply, ← hlow]

/-- Helper for cm-center-proposition: wherever `N` is nonzero, the source
regular frame is positively oriented orthogonal. -/
theorem regularFrame_oriented (p h r μ τ : ℝ)
    (hD : regularDenominator r μ ≠ 0) (hE : regularEnergy p r μ ≠ 0)
    (hhigh : RealSymmetric2.high (regularEntries p h r μ).1
      (r * (regularEntries p h r μ).2.1) (regularEntries p h r μ).2.2 ≠ 0)
    (hN : (regularRotatedData p h r μ τ).2 ≠ 0) :
    regularFrame p h r μ τ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [regularFrame_eq_lowEigenframe p h r μ τ hD hE hhigh]
  rw [regularNormalizer_eq_lowDenom p h r μ τ hD hE hhigh] at hN
  exact RealSymmetric2.frame_mem_specialOrthogonalGroup_of_lowDenom_ne_zero _ _ _ hN

/-- Helper for cm-center-proposition: the source radius, shape, and amplitude
formulas are exactly spectral recovery from `(r²ℓ,λ)` and `(GX,GrY)/N`. -/
theorem regularStep_spectralRecovery (p h r μ τ G : ℝ)
    (hr : r ≠ 0) (hG : G ≠ 0)
    (hN : (regularRotatedData p h r μ τ).2 ≠ 0)
    (hX : (regularRotatedData p h r μ τ).1.1 ≠ 0)
    (hY : (regularRotatedData p h r μ τ).1.2 ≠ 0)
    (hL : (regularSpectrum p h r μ).1 ≠ 0)
    (hH : (regularSpectrum p h r μ).2 ≠ 0) :
    CycleBoundaryState.recoveryRadius
        (r ^ 2 * (regularSpectrum p h r μ).1) (regularSpectrum p h r μ).2
        (G * (regularRotatedData p h r μ τ).1.1 / (regularRotatedData p h r μ τ).2)
        (G * r * (regularRotatedData p h r μ τ).1.2 /
          (regularRotatedData p h r μ τ).2) = r * (regularStep p h r μ τ).1 ∧
      CycleBoundaryState.recoveryShape
        (r ^ 2 * (regularSpectrum p h r μ).1) (regularSpectrum p h r μ).2
        (G * (regularRotatedData p h r μ τ).1.1 / (regularRotatedData p h r μ τ).2)
        (G * r * (regularRotatedData p h r μ τ).1.2 /
          (regularRotatedData p h r μ τ).2) = (regularStep p h r μ τ).2.1 := by
  unfold CycleBoundaryState.recoveryRadius CycleBoundaryState.recoveryShape
  dsimp only [regularStep]
  constructor
  · field_simp [hr, hG, hN, hX, hY, hL, hH]
  · field_simp [hr, hG, hN, hX, hY, hL, hH]

/-- Helper for cm-center-proposition: the exact one-step center change
`Cnew − C = s − y` is the source vector in cm-center-step. -/
theorem spectralCenterDisplacement (z : DFP.AbstractSecantStep (Fin 2))
    (p h r μ G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * r])
    (hA : z.secantMatrix = !![1, μ; μ, 1]) :
    z.displacement - z.gradientChange =
      (G * z.tau * (p + 1) * μ * r / regularDenominator r μ) • ![(1 : ℝ), r] := by
  rw [z.gradientChange_def, spectralDisplacement z p h r μ G hH hg hA, hA]
  ext i
  fin_cases i
  · simp
    ring
  · simp
    ring

/-- Helper for cm-center-proposition: the source two-step map is analytic at
`(0,2,1)` and fixes that point. -/
theorem twoStepAnalytic :
    AnalyticAt ℝ DFP.TwoLeg.stateMap ((0, 2, 1) : ℝ × ℝ × ℝ) ∧
      DFP.TwoLeg.stateMap (0, 2, 1) = (0, 2, 1) := by
  exact ⟨DFP.TwoLeg.stateMapAnalytic, DFP.TwoLeg.stateMap_base⟩

/-- Helper for cm-center-proposition: the zero-scale source cycle has exactly
the displayed rational radius, shape, and high eigenvalue factors. -/
theorem twoStepZeroSlice (p h : ℝ) (hp : 0 < p) (hh : 0 < h) :
    DFP.TwoLeg.radiusFactor 0 p h =
        9 * h * p * (p + 1) / (2 * (9 * h * p + (p + 1) ^ 2)) ∧
      (DFP.TwoLeg.stateMap (0, p, h)).2 =
        (4 * (9 * h * p + (p + 1) ^ 2) ^ 2 / (81 * h * p * (p + 1) ^ 2), 1) := by
  exact ⟨DFP.TwoLeg.radiusFactor_zero p h hp hh,
    DFP.TwoLeg.stateMap_zero_transverse p h hp hh⟩

/-- Helper for cm-center-proposition: the linearization part. The derivative of the exact
source two-step map is `(δε,δp,δh) ↦ (δε,−δp/9+2δh/3,0)` and has the three
source eigenvalues `1`, `−1/9`, and `0`. Graph existence is a separate part. -/
theorem centerMapLinearization :
    (∀ v : ℝ × ℝ × ℝ,
      fderiv ℝ DFP.TwoLeg.stateMap (0, 2, 1) v =
        (v.1, (-(1 : ℝ) / 9) * v.2.1 + (2 / 3) * v.2.2, 0)) ∧
      Module.End.HasEigenvalue
        (fderiv ℝ DFP.TwoLeg.stateMap (0, 2, 1)).toLinearMap (1 : ℝ) ∧
      Module.End.HasEigenvalue
        (fderiv ℝ DFP.TwoLeg.stateMap (0, 2, 1)).toLinearMap (-(1 : ℝ) / 9) ∧
      Module.End.HasEigenvalue
        (fderiv ℝ DFP.TwoLeg.stateMap (0, 2, 1)).toLinearMap (0 : ℝ) := by
  exact ⟨DFP.TwoLeg.stateMap_fderiv_apply, DFP.TwoLeg.stateMap_centerEigenvalue,
    DFP.TwoLeg.stateMap_transverseEigenvalue_negNinth,
    DFP.TwoLeg.stateMap_transverseEigenvalue_zero⟩

/-- Helper for cm-center-proposition: the literal initial point and gradient
are `(1,p(ε₀)*ε₀²)` and the literal initial matrix is `diag(h*p*ε₀⁴,h)`. -/
theorem prescribedInitialization (p h : ℝ → ℝ) (ε₀ : ℝ) :
    (DFP.TwoPhaseOrbit.State.initial p h ε₀).point =
        WithLp.toLp 2 ![(1 : ℝ), p ε₀ * ε₀ ^ 2] ∧
      (DFP.TwoPhaseOrbit.State.initial p h ε₀).gradient =
        WithLp.toLp 2 ![(1 : ℝ), p ε₀ * ε₀ ^ 2] ∧
      (DFP.TwoPhaseOrbit.State.initial p h ε₀).metric =
        Matrix.diagonal ![h ε₀ * p ε₀ * ε₀ ^ 4, h ε₀] := by
  have hgradient : (DFP.TwoPhaseOrbit.State.initial p h ε₀).gradient =
      WithLp.toLp 2 ![(1 : ℝ), p ε₀ * ε₀ ^ 2] := by
    rw [DFP.TwoPhaseOrbit.State.gradient_def,
      DFP.TwoPhaseOrbit.State.initial_amplitude, DFP.TwoPhaseOrbit.State.initial_frame,
      DFP.TwoPhaseOrbit.State.initial_p, DFP.TwoPhaseOrbit.State.initial_epsilon]
    simp
  refine ⟨?_, hgradient, ?_⟩
  · rw [DFP.TwoPhaseOrbit.State.initial_point, hgradient]
  · rw [DFP.TwoPhaseOrbit.State.metric_def, DFP.TwoPhaseOrbit.State.initial_frame,
      DFP.TwoPhaseOrbit.State.initial_h, DFP.TwoPhaseOrbit.State.initial_p,
      DFP.TwoPhaseOrbit.State.initial_epsilon]
    simp

/-- Helper for cm-center-proposition: the second-stage factor package exposes
its spectral, gradient, and canonical pairs. -/
theorem secondFactors_apply (ε p h : ℝ) :
    DFP.SecondLeg.factors ε p h =
      (DFP.SecondLeg.spectralFactors ε p h, DFP.SecondLeg.gradientFactors ε p h,
        DFP.SecondLeg.canonicalFactors ε p h) := by
  exact DFP.SecondLeg.factors_apply ε p h

/-- Helper for cm-center-proposition: the ten positive removable factors for
both actual stages, in spectral, gradient, and radius order. -/
def twoStageFactors (x : ℝ × ℝ × ℝ) : Fin 10 → ℝ :=
  let first := DFP.FirstLeg.factors x.1 x.2.1 x.2.2
  let second := DFP.SecondLeg.factors x.1 x.2.1 x.2.2
  ![first.1.1, first.1.2, first.2.1.1, first.2.1.2, first.2.2.1,
    second.1.1, second.1.2, second.2.1.1, second.2.1.2, second.2.2.1]

/-- Helper for cm-center-proposition: the ten-factor interface refers to the
original stage spectral, gradient, and radius factors. -/
theorem twoStageFactors_apply (ε p h : ℝ) :
    twoStageFactors (ε, p, h) =
      ![(DFP.FirstLeg.spectralFactors ε p h).1, (DFP.FirstLeg.spectralFactors ε p h).2,
        (DFP.FirstLeg.gradientFactors ε p h).1, (DFP.FirstLeg.gradientFactors ε p h).2,
        (DFP.FirstLeg.canonicalFactors ε p h).1,
        (DFP.SecondLeg.spectralFactors ε p h).1, (DFP.SecondLeg.spectralFactors ε p h).2,
        (DFP.SecondLeg.gradientFactors ε p h).1, (DFP.SecondLeg.gradientFactors ε p h).2,
        (DFP.SecondLeg.canonicalFactors ε p h).1] := by
  simp only [twoStageFactors, DFP.FirstLeg.factors_apply, secondFactors_apply]

/-- Helper for cm-center-proposition: both actual stages have continuous
removable factor data at the common base state. -/
theorem twoStageFactors_continuousAt :
    ContinuousAt twoStageFactors ((0, 2, 1) : ℝ × ℝ × ℝ) := by
  have hfirst := DFP.FirstLeg.factorsAnalytic.continuousAt
  have hsecond := DFP.SecondLeg.factorsAnalytic.continuousAt
  unfold twoStageFactors
  fun_prop

/-- Helper for cm-center-proposition: the ten actual stage factors at the
base state are `(2,1,1,1,2,2,1,1,2,1)`. -/
theorem twoStageFactors_base :
    twoStageFactors ((0, 2, 1) : ℝ × ℝ × ℝ) =
      ![(2 : ℝ), 1, 1, 1, 2, 2, 1, 1, 2, 1] := by
  simp only [twoStageFactors, DFP.FirstLeg.factorsBase, DFP.SecondLeg.factorsBase]

/-- Helper for cm-center-proposition: one fixed neighborhood bounds all ten
actual stage factors strictly above `1/2`. -/
theorem twoStageFactors_eventually_half_lt :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ∀ i, (1 / 2 : ℝ) < twoStageFactors x i := by
  apply Filter.eventually_all.mpr
  intro i
  have hbase : (1 / 2 : ℝ) < twoStageFactors ((0, 2, 1) : ℝ × ℝ × ℝ) i := by
    rw [twoStageFactors_base]
    fin_cases i
    all_goals norm_num
  have hcontinuous := (continuous_apply i).continuousAt.comp twoStageFactors_continuousAt
  exact hcontinuous.eventually (Ioi_mem_nhds hbase)

/-- Helper for cm-center-proposition: positive scale, amplitude, and oriented
frame give valid actual two-stage data on a fixed neighborhood of `(0,2,1)`. -/
theorem phaseValidity_near_base :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ∀ s : DFP.TwoPhaseOrbit.State, s.coordinates = x →
        s.frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ →
        0 < s.amplitude → 0 < s.ε → s.PhaseValidity := by
  have hshape : ∀ᶠ x : ℝ × ℝ × ℝ in 𝓝 (0, 2, 1), 0 < x.2.1 := by
    have hbase : (0 : ℝ) < 2 := by norm_num
    exact (continuousAt_fst.comp continuousAt_snd).eventually (Ioi_mem_nhds hbase)
  have hhigh : ∀ᶠ x : ℝ × ℝ × ℝ in 𝓝 (0, 2, 1), 0 < x.2.2 := by
    have hbase : (0 : ℝ) < 1 := by norm_num
    exact (continuousAt_snd.comp continuousAt_snd).eventually (Ioi_mem_nhds hbase)
  have hscale : ∀ᶠ x : ℝ × ℝ × ℝ in 𝓝 (0, 2, 1), x.1 < 1 / 4 := by
    have hbase : (0 : ℝ) < 1 / 4 := by norm_num
    exact continuousAt_fst.eventually (Iio_mem_nhds hbase)
  filter_upwards [twoStageFactors_eventually_half_lt, hshape, hhigh, hscale]
    with x hfactor hp hh hεlt
  intro s hcoordinates hframe hG hε
  have htuple : (s.ε, s.p, s.h) = x := by
    rw [← DFP.TwoPhaseOrbit.State.coordinates_def]
    exact hcoordinates
  rw [← htuple] at hfactor hp hh hεlt
  have hpositive : ∀ i, 0 < twoStageFactors (s.ε, s.p, s.h) i := by
    intro i
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    exact hhalf.trans (hfactor i)
  apply DFP.TwoPhaseOrbit.State.PhaseValidity.ofComponents s hframe hε hεlt hp hh hG
  · simpa [twoStageFactors_apply] using hpositive 0
  · simpa [twoStageFactors_apply] using hpositive 1
  · simpa [twoStageFactors_apply] using hpositive 2
  · simpa [twoStageFactors_apply] using hpositive 3
  · simpa [twoStageFactors_apply] using hpositive 4
  · simpa [twoStageFactors_apply] using hpositive 5
  · simpa [twoStageFactors_apply] using hpositive 6
  · simpa [twoStageFactors_apply] using hpositive 7
  · simpa [twoStageFactors_apply] using hpositive 8
  · simpa [twoStageFactors_apply] using hpositive 9

/-- Helper for cm-center-proposition: a fixed regular neighborhood gives exact
agreement with both actual inverse DFP stages, without any invariant-graph premise. -/
theorem exactCycle_near_base :
    ∃ δ > 0, ∀ s : DFP.TwoPhaseOrbit.State,
      dist s.coordinates (0, 2, 1) < δ →
        s.frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ →
        0 < s.amplitude → 0 < s.ε → s.ExactCycle := by
  obtain ⟨δ, hδ, hvalid⟩ := Metric.eventually_nhds_iff.mp phaseValidity_near_base
  refine ⟨δ, hδ, ?_⟩
  intro s hdist hframe hG hε
  exact DFP.TwoPhaseOrbit.State.exactCycle_of_phaseValidity s
    (hvalid hdist s rfl hframe hG hε)

/-- Helper for cm-center-proposition: both exact stages use the incoming
cycle scale `ε`, with ratios `2/3`, `1/3`; the second uses the updated frame. -/
theorem alternatingControls (s : DFP.TwoPhaseOrbit.State) (h : s.PhaseValidity) :
    (DFP.TwoPhaseOrbit.State.firstStep s h).secantMatrix = !![1, s.ε; s.ε, 1] ∧
      (DFP.TwoPhaseOrbit.State.firstStep s h).tau = 2 / 3 ∧
      (DFP.TwoPhaseOrbit.State.secondStep s h).secantMatrix =
        !![1, -2 * s.ε; -2 * s.ε, 1] ∧
      (DFP.TwoPhaseOrbit.State.secondStep s h).tau = 1 / 3 ∧
      s.middleFrame = s.frame * DFP.FirstLeg.frame s.ε s.p s.h := by
  simp only [DFP.TwoPhaseOrbit.State.firstStep_secantMatrix,
    DFP.TwoPhaseOrbit.State.firstStep_tau, DFP.TwoPhaseOrbit.State.secondStep_secantMatrix,
    DFP.TwoPhaseOrbit.State.secondStep_tau, TwoPhaseControls.first_matrix,
    TwoPhaseControls.second_matrix, TwoPhaseControls.first_tau, TwoPhaseControls.second_tau,
    DFP.TwoPhaseOrbit.State.middleFrame_def, and_self]

/-- Helper for cm-center-proposition: actual physical successor coordinates
and frame are the source signed two-step map and its two ordered eigenframe updates. -/
theorem physicalTwoStep (s : DFP.TwoPhaseOrbit.State) :
    s.next.coordinates = DFP.TwoLeg.stateMap s.coordinates ∧
      s.next.frame = s.middleFrame * DFP.SecondLeg.frame s.ε s.p s.h ∧
      s.next.point = s.point + s.firstDisplacement + s.secondDisplacement := by
  exact ⟨DFP.TwoPhaseOrbit.State.next_coordinates s,
    DFP.TwoPhaseOrbit.State.next_frame s,
    (DFP.TwoPhaseOrbit.State.next_point s).trans
      (congrArg (fun x ↦ x + s.secondDisplacement)
        (DFP.TwoPhaseOrbit.State.middlePoint_def s))⟩

/-- Helper for cm-center-proposition: orthogonal congruence preserves positive
definiteness of the actual local inverse Hessian. -/
theorem frameConjugate_posDef (H R : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : H.PosDef) (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    (R * H * R.transpose).PosDef := by
  have hdet : R.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp hR).2
  have hunit : IsUnit R := by
    apply (Matrix.isUnit_iff_isUnit_det R).mpr
    rw [hdet]
    exact isUnit_one
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial R, ← Matrix.star_eq_conjTranspose]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hunit).mpr hH

/-- Helper for cm-center-proposition: the first source eigenframe update
preserves the orientation of the physical middle frame. -/
theorem middleFrame_oriented (s : DFP.TwoPhaseOrbit.State) (h : s.PhaseValidity) :
    s.middleFrame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [DFP.TwoPhaseOrbit.State.middleFrame_def]
  exact mul_mem h.frame_specialOrthogonal
    (DFP.FirstLeg.frame_mem_specialOrthogonalGroup s.ε s.p s.h
      (ne_of_gt h.firstGradientLow_pos))

/-- Helper for cm-center-proposition: all three physical inverse Hessians
in an admissible source cycle are positive definite. -/
theorem physicalMatrices_posDef (s : DFP.TwoPhaseOrbit.State) (h : s.PhaseValidity) :
    s.metric.PosDef ∧ s.middleMetric.PosDef ∧ s.next.metric.PosDef := by
  have hfirst := DFP.TwoPhaseOrbit.State.firstPhaseExact_of_phaseValidity s h
  have hsecond := DFP.TwoPhaseOrbit.State.secondPhaseExact_of_phaseValidity s h
  constructor
  · rw [DFP.TwoPhaseOrbit.State.metric_def]
    exact frameConjugate_posDef _ _
      (DFP.TwoPhaseOrbit.State.firstStep_inverseHessian_posDef s h)
      h.frame_specialOrthogonal
  · constructor
    · rw [hfirst.metric]
      exact frameConjugate_posDef _ _
        (DFP.TwoPhaseOrbit.State.firstStep s h).nextInverseHessian_posDef
        h.frame_specialOrthogonal
    · rw [hsecond.metric]
      exact frameConjugate_posDef _ _
        (DFP.TwoPhaseOrbit.State.secondStep s h).nextInverseHessian_posDef
        (middleFrame_oriented s h)

/-- Helper for cm-center-proposition: a single fixed neighborhood gives two
exact source stages and positive physical matrices, before any initial scale is selected. -/
theorem localSpectralRecurrence :
    ∃ δ > 0, ∀ s : DFP.TwoPhaseOrbit.State,
      dist s.coordinates (0, 2, 1) < δ →
        s.frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ →
        0 < s.amplitude → 0 < s.ε →
        s.ExactCycle ∧ s.metric.PosDef ∧ s.middleMetric.PosDef ∧ s.next.metric.PosDef := by
  obtain ⟨δ, hδ, hexact⟩ := exactCycle_near_base
  refine ⟨δ, hδ, ?_⟩
  intro s hdist hframe hG hε
  have hcycle := hexact s hdist hframe hG hε
  exact ⟨hcycle, physicalMatrices_posDef s hcycle.valid⟩

/-- Helper for cm-center-proposition: the first-stage source formulas agree
with the actual first leg in a valid physical cycle. -/
theorem firstStageRegularStep (s : DFP.TwoPhaseOrbit.State) (h : s.PhaseValidity) :
    DFP.FirstLeg.outputMetric s.ε s.p s.h = regularMetric s.p s.h (s.ε ^ 2) s.ε ∧
      s.amplitude • DFP.FirstLeg.outputGradient s.ε s.p s.h =
        s.amplitude • regularGradient s.p (s.ε ^ 2) s.ε (2 / 3) := by
  have hmetric : (DFP.TwoPhaseOrbit.State.firstStep s h).inverseHessian =
      Matrix.diagonal ![s.h * s.p * (s.ε ^ 2) ^ 2, s.h] := by
    rw [DFP.TwoPhaseOrbit.State.firstStep_inverseHessian, ← pow_mul]
  have hgradient : (DFP.TwoPhaseOrbit.State.firstStep s h).gradient =
      s.amplitude • ![(1 : ℝ), s.p * s.ε ^ 2] :=
    DFP.TwoPhaseOrbit.State.firstStep_gradient s h
  have hcontrol : (DFP.TwoPhaseOrbit.State.firstStep s h).secantMatrix =
      !![1, s.ε; s.ε, 1] := by
    rw [DFP.TwoPhaseOrbit.State.firstStep_secantMatrix, TwoPhaseControls.first_matrix]
  have houtput := DFP.TwoPhaseOrbit.State.firstStep_output s h
  constructor
  · exact (congrArg Prod.fst houtput).symm.trans
      (spectralMetricUpdate _ s.p s.h (s.ε ^ 2) s.ε s.amplitude
        hmetric hgradient hcontrol)
  · have hregular := spectralGradientUpdate (DFP.TwoPhaseOrbit.State.firstStep s h)
      s.p s.h (s.ε ^ 2) s.ε s.amplitude hmetric hgradient hcontrol
    rw [DFP.TwoPhaseOrbit.State.firstStep_tau, TwoPhaseControls.first_tau] at hregular
    exact (congrArg Prod.snd houtput).symm.trans hregular

/-- Helper for cm-center-proposition: the first canonical factors expose the
source recovery quotients for the updated radius and shape. -/
theorem firstCanonicalFactors_apply (ε p h : ℝ) :
    DFP.FirstLeg.canonicalFactors ε p h =
      ((DFP.FirstLeg.spectralFactors ε p h).1 *
          (DFP.FirstLeg.gradientFactors ε p h).1 /
          ((DFP.FirstLeg.spectralFactors ε p h).2 *
            (DFP.FirstLeg.gradientFactors ε p h).2),
        (DFP.FirstLeg.spectralFactors ε p h).2 *
          (DFP.FirstLeg.gradientFactors ε p h).2 ^ 2 /
          ((DFP.FirstLeg.spectralFactors ε p h).1 *
            (DFP.FirstLeg.gradientFactors ε p h).1 ^ 2)) := by
  rfl

/-- Helper for cm-center-proposition: after the first rotation the second
step's actual inputs have precisely the recovered `pnew,hnew,rnew,Gnew` form. -/
theorem middleCanonicalInput (s : DFP.TwoPhaseOrbit.State) (h : s.PhaseValidity) :
    (DFP.TwoPhaseOrbit.State.secondStep s h).inverseHessian =
      Matrix.diagonal
        ![(DFP.FirstLeg.spectralFactors s.ε s.p s.h).2 *
            (DFP.FirstLeg.canonicalFactors s.ε s.p s.h).2 *
            (s.ε ^ 2 * (DFP.FirstLeg.canonicalFactors s.ε s.p s.h).1) ^ 2,
          (DFP.FirstLeg.spectralFactors s.ε s.p s.h).2] ∧
      (DFP.TwoPhaseOrbit.State.secondStep s h).gradient =
        (s.amplitude * (DFP.FirstLeg.gradientFactors s.ε s.p s.h).1) •
          ![(1 : ℝ), (DFP.FirstLeg.canonicalFactors s.ε s.p s.h).2 *
            (s.ε ^ 2 * (DFP.FirstLeg.canonicalFactors s.ε s.p s.h).1)] := by
  have hL := ne_of_gt h.firstSpectralLow_pos
  have hH := ne_of_gt h.firstSpectralHigh_pos
  have hQ := ne_of_gt h.firstGradientLow_pos
  have hU := ne_of_gt h.firstGradientHigh_pos
  constructor
  · rw [DFP.TwoPhaseOrbit.State.secondStep_inverseHessian, firstCanonicalFactors_apply]
    congr 1
    ext i
    fin_cases i
    · norm_num
      field_simp [hL, hH, hQ, hU]
    · norm_num
  · rw [DFP.TwoPhaseOrbit.State.secondStep_gradient, firstCanonicalFactors_apply]
    ext i
    fin_cases i
    · norm_num
    · norm_num
      field_simp [hL, hH, hQ, hU]

/-- Helper for cm-center-proposition: the actual second leg is the same regular
step applied to the UPDATED spectral coordinates and the ORIGINAL cycle scale. -/
theorem secondStageRegularStep (s : DFP.TwoPhaseOrbit.State) (h : s.PhaseValidity) :
    DFP.SecondLeg.outputMetric s.ε s.p s.h =
      regularMetric (DFP.FirstLeg.canonicalFactors s.ε s.p s.h).2
        (DFP.FirstLeg.spectralFactors s.ε s.p s.h).2
        (s.ε ^ 2 * (DFP.FirstLeg.canonicalFactors s.ε s.p s.h).1) (-2 * s.ε) ∧
      s.amplitude • DFP.SecondLeg.outputGradient s.ε s.p s.h =
        (s.amplitude * (DFP.FirstLeg.gradientFactors s.ε s.p s.h).1) •
          regularGradient (DFP.FirstLeg.canonicalFactors s.ε s.p s.h).2
            (s.ε ^ 2 * (DFP.FirstLeg.canonicalFactors s.ε s.p s.h).1)
            (-2 * s.ε) (1 / 3) := by
  obtain ⟨hmetric, hgradient⟩ := middleCanonicalInput s h
  have hcontrol : (DFP.TwoPhaseOrbit.State.secondStep s h).secantMatrix =
      !![1, -2 * s.ε; -2 * s.ε, 1] := by
    rw [DFP.TwoPhaseOrbit.State.secondStep_secantMatrix, TwoPhaseControls.second_matrix]
  have houtput := DFP.TwoPhaseOrbit.State.secondStep_output s h
  constructor
  · exact (congrArg Prod.fst houtput).symm.trans
      (spectralMetricUpdate _ _ _ _ _ _ hmetric hgradient hcontrol)
  · have hregular := spectralGradientUpdate (DFP.TwoPhaseOrbit.State.secondStep s h)
      _ _ _ _ _ hmetric hgradient hcontrol
    rw [DFP.TwoPhaseOrbit.State.secondStep_tau, TwoPhaseControls.second_tau] at hregular
    exact (congrArg Prod.snd houtput).symm.trans hregular

/-- Helper for cm-center-proposition: the parameter choices in the source graph
transform make its slope, uniform contraction, and all order-2 through order-8
highest-derivative coefficients strictly contractive simultaneously. -/
theorem graphTransformParameters (stableRate slope : ℝ)
    (hstable : stableRate < 1) (hslope : 0 < slope) :
    ∃ δ > 0,
      let m := 1 - δ * (1 + slope)
      let η := δ + (stableRate + δ) * slope
      0 < m ∧ η / m < slope ∧ stableRate + δ + η * δ / m < 1 ∧
        ∀ r : Fin 7, (stableRate + δ * (1 + slope)) / m ^ (r.val + 2) < 1 := by
  let m : ℝ → ℝ := fun δ ↦ 1 - δ * (1 + slope)
  let η : ℝ → ℝ := fun δ ↦ δ + (stableRate + δ) * slope
  have hm : ContinuousAt m 0 := by
    dsimp only [m]
    fun_prop
  have hη : ContinuousAt η 0 := by
    dsimp only [η]
    fun_prop
  have hmzero : m 0 ≠ 0 := by simp [m]
  have hmpos : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < m δ := by
    have hbase : 0 < m 0 := by simp [m]
    exact hm.eventually (Ioi_mem_nhds hbase)
  have hslopeBase : η 0 / m 0 < slope := by
    simp only [η, m, zero_mul, sub_zero, add_zero, zero_add, div_one]
    nlinarith
  have hslopeEvent : ∀ᶠ δ in 𝓝 (0 : ℝ), η δ / m δ < slope :=
    (hη.div hm hmzero).eventually (Iio_mem_nhds hslopeBase)
  have hcontractionContinuous :
      ContinuousAt (fun δ ↦ stableRate + δ + η δ * δ / m δ) 0 := by
    exact (continuousAt_const.add continuousAt_id).add
      ((hη.mul continuousAt_id).div hm hmzero)
  have hcontractionBase : stableRate + 0 + η 0 * 0 / m 0 < 1 := by
    simpa using hstable
  have hcontraction : ∀ᶠ δ in 𝓝 (0 : ℝ),
      stableRate + δ + η δ * δ / m δ < 1 :=
    hcontractionContinuous.eventually (Iio_mem_nhds hcontractionBase)
  have hhighest : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ r : Fin 7,
      (stableRate + δ * (1 + slope)) / m δ ^ (r.val + 2) < 1 := by
    apply Filter.eventually_all.mpr
    intro r
    have hcontinuous : ContinuousAt
        (fun δ ↦ (stableRate + δ * (1 + slope)) / m δ ^ (r.val + 2)) 0 := by
      have hnum : ContinuousAt (fun δ : ℝ ↦ stableRate + δ * (1 + slope)) 0 := by
        fun_prop
      exact hnum.div (hm.pow _) (pow_ne_zero _ hmzero)
    have hbase : (stableRate + 0 * (1 + slope)) / m 0 ^ (r.val + 2) < 1 := by
      simpa [m] using hstable
    exact hcontinuous.eventually (Iio_mem_nhds hbase)
  have hall := hmpos.and (hslopeEvent.and (hcontraction.and hhighest))
  obtain ⟨radius, hradius, hbound⟩ := Metric.eventually_nhds_iff.mp hall
  have hδ : 0 < radius / 2 := half_pos hradius
  have hdist : dist (radius / 2) 0 < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    exact half_lt_self hradius
  exact ⟨radius / 2, hδ, hbound hdist⟩

/-- Helper for cm-center-proposition: the stable linear block of the source
map, in the two transverse coordinates `(p−2,h−1)`. -/
def stableDerivative : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (((-(1 : ℝ) / 9) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    ((2 : ℝ) / 3) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (0 : (ℝ × ℝ) →L[ℝ] ℝ)

/-- Helper for cm-center-proposition: the stable block has the exact source
triangular action. -/
theorem stableDerivative_apply (z : ℝ × ℝ) :
    stableDerivative z = ((-(1 : ℝ) / 9) * z.1 + (2 / 3) * z.2, 0) := by
  simp [stableDerivative]

/-- Helper for cm-center-proposition: the same source stable block strictly
contracts the product norm; the bound `7/9` is a coordinate-norm adapter. -/
theorem stableDerivative_norm_le : ‖stableDerivative‖ ≤ (7 / 9 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound
  · norm_num
  · intro z
    rw [stableDerivative_apply]
    apply norm_prod_le_iff.mpr
    constructor
    · calc
        ‖(-(1 : ℝ) / 9) * z.1 + (2 / 3) * z.2‖ ≤
            ‖(-(1 : ℝ) / 9) * z.1‖ + ‖(2 / 3) * z.2‖ := norm_add_le _ _
        _ = (1 / 9 : ℝ) * ‖z.1‖ + (2 / 3) * ‖z.2‖ := by
          rw [norm_mul, norm_mul]
          norm_num
        _ ≤ (7 / 9 : ℝ) * ‖z‖ := by
          nlinarith [norm_fst_le z, norm_snd_le z]
    · simp only [norm_zero]
      positivity

/-- Helper for cm-center-proposition: the source transverse derivative has
operator norm strictly below one. -/
theorem stableDerivative_norm_lt_one : ‖stableDerivative‖ < 1 := by
  have hrate : (7 / 9 : ℝ) < 1 := by norm_num
  exact stableDerivative_norm_le.trans_lt hrate

/-- Helper for cm-center-proposition: translate the actual source map to the
center-stable origin, without changing its scale coordinate or parameter map. -/
def centeredStateMap (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  DFP.TwoLeg.stateMap (x + (0, 2, 1)) - (0, 2, 1)

/-- Helper for cm-center-proposition: the centered map is the actual source
map expressed in `(ε,p−2,h−1)` coordinates. -/
theorem centeredStateMap_apply (ε u v : ℝ) :
    centeredStateMap (ε, u, v) =
      let y := DFP.TwoLeg.stateMap (ε, u + 2, v + 1)
      (y.1, y.2.1 - 2, y.2.2 - 1) := by
  simp only [centeredStateMap, Prod.mk_add_mk, add_zero]
  apply Prod.ext
  · simp
  · rfl

/-- Helper for cm-center-proposition: the centered source map fixes zero. -/
theorem centeredStateMap_zero : centeredStateMap 0 = 0 := by
  simp [centeredStateMap, DFP.TwoLeg.stateMap_base]

/-- Helper for cm-center-proposition: the centered source map is analytic
at zero, so all finite smoothness orders required by the graph transform are available. -/
theorem centeredStateMap_analyticAt : AnalyticAt ℝ centeredStateMap 0 := by
  have hinput : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x + (0, 2, 1)) 0 :=
    analyticAt_id.add analyticAt_const
  have houter : AnalyticAt ℝ DFP.TwoLeg.stateMap
      ((0 : ℝ × ℝ × ℝ) + (0, 2, 1)) := by
    simpa only [zero_add] using DFP.TwoLeg.stateMapAnalytic
  have hcomposition := houter.comp
    (f := fun x : ℝ × ℝ × ℝ ↦ x + (0, 2, 1)) (x := 0) hinput
  have hsub : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.TwoLeg.stateMap (x + (0, 2, 1)) - (0, 2, 1)) 0 :=
    hcomposition.sub analyticAt_const
  exact hsub

/-- Helper for cm-center-proposition: the derivative of the translated source
map is exactly its center identity plus the stable block. -/
theorem centeredStateMap_hasFDerivAt :
    HasFDerivAt centeredStateMap (LocalCutoff.centerStable stableDerivative) 0 := by
  have hinput : HasFDerivAt (fun x : ℝ × ℝ × ℝ ↦ x + (0, 2, 1))
      (ContinuousLinearMap.id ℝ (ℝ × ℝ × ℝ)) 0 :=
    (hasFDerivAt_id 0).add_const (0, 2, 1)
  have houter : HasFDerivAt DFP.TwoLeg.stateMap
      (fderiv ℝ DFP.TwoLeg.stateMap (0, 2, 1))
      ((0 : ℝ × ℝ × ℝ) + (0, 2, 1)) := by
    simpa only [zero_add] using DFP.TwoLeg.stateMapAnalytic.differentiableAt.hasFDerivAt
  have hraw := ((houter.comp 0 hinput).sub_const ((0, 2, 1) : ℝ × ℝ × ℝ))
  have hcentered : HasFDerivAt centeredStateMap
      ((fderiv ℝ DFP.TwoLeg.stateMap (0, 2, 1)).comp
        (ContinuousLinearMap.id ℝ (ℝ × ℝ × ℝ))) 0 := by
    apply hraw.congr_of_eventuallyEq
    filter_upwards [] with x
    rfl
  apply hcentered.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨ε, u, v⟩
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    DFP.TwoLeg.stateMap_fderiv_apply, LocalCutoff.centerStable_apply, stableDerivative_apply]

/-- Helper for cm-center-proposition: an invariant C⁷ graph through the base,
tangent to the scale axis, has the actual source map's determined Taylor jets.
This is coefficient extraction from a supplied graph, not graph existence. -/
theorem invariantGraphTaylorJets (p h : ℝ → ℝ)
    (hsmooth : ContDiffAt ℝ 7 (fun ε ↦ (p ε, h ε)) 0)
    (hbase : (p 0, h 0) = (2, 1))
    (htangent : HasFDerivAt (fun ε ↦ (p ε, h ε)) (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0)
    (hinvariant : (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let nextScale := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (nextScale, p nextScale, h nextScale))) :
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) ∧
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) ∧
      (fun ε : ℝ ↦ (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1 -
        (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 6) := by
  have htwo : (2 : WithTop ℕ∞) ≤ 7 := by norm_num
  have hfive : (5 : WithTop ℕ∞) ≤ 7 := by norm_num
  obtain ⟨hpFirst, hhFirst, hpSecond, hhSecond⟩ :=
    DFP.TwoLeg.slowCurveInvariantGraph_secondOrderFlat p h (hsmooth.of_le htwo)
      hbase htangent hinvariant
  obtain ⟨P₃, H₃, P₄, H₄, hpJet, hhJet⟩ :=
    DFP.TwoLeg.exists_slowCurveTaylorCoefficients p h (hsmooth.of_le hfive)
      hbase hpFirst hhFirst hpSecond hhSecond
  obtain ⟨hshapeCubic, hhighCubic, hshapeQuartic, hhighQuartic⟩ :=
    DFP.TwoLeg.slowCurveInvariantGraph_coefficientEquations p h P₃ H₃ P₄ H₄
      hinvariant hpJet hhJet
  have hH₃ : H₃ = 8 := by linarith
  have hP₃ : P₃ = 198 / 5 := by linarith
  have hH₄ : H₄ = 0 := by linarith
  have hP₄ : P₄ = -9 / 5 := by linarith
  have hpTarget :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    apply hpJet.congr'
    · filter_upwards [] with ε
      rw [hP₃, hP₄]
      ring
    · rfl
  have hhTarget :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [hH₃, hH₄, zero_mul, add_zero] using hhJet
  have hrecurrence := DFP.TwoLeg.slowGraphSignedRecurrence p h hpTarget hhTarget
  refine ⟨hpTarget, hhTarget, ?_⟩
  simpa only [DFP.TwoLeg.stateMap_fst] using hrecurrence

/-- Helper for cm-center-proposition: coefficient extraction gives precisely
the three uniform cubic/quartic expansions displayed in cm-center-expansions.
The invariant graph itself must still be constructed by the source graph transform. -/
theorem invariantGraphSourceExpansions (p h : ℝ → ℝ)
    (hsmooth : ContDiffAt ℝ 7 (fun ε ↦ (p ε, h ε)) 0)
    (hbase : (p 0, h 0) = (2, 1))
    (htangent : HasFDerivAt (fun ε ↦ (p ε, h ε)) (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0)
    (hinvariant : (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let nextScale := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (nextScale, p nextScale, h nextScale))) :
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) ∧
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) ∧
      (fun ε : ℝ ↦ (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1 -
        (ε - (3 / 2) * ε ^ 4)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
  obtain ⟨hpJet, hhJet, hscaleJet⟩ :=
    invariantGraphTaylorJets p h hsmooth hbase htangent hinvariant
  have hfourFive : 4 < 5 := by norm_num
  have hfiveSix : 5 < 6 := by norm_num
  have hpowerFiveFour : (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hfourFive).isBigO
  have hpowerSixFive : (fun ε : ℝ ↦ ε ^ 6) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) :=
    (Asymptotics.isLittleO_pow_pow hfiveSix).isBigO
  have hshapeCorrection : (fun ε : ℝ ↦ (9 / 5) * ε ^ 4) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 4) (𝓝 0)).const_mul_left (9 / 5)
  have hscaleCorrection : (fun ε : ℝ ↦ (5 / 4) * ε ^ 5) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) :=
    (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).const_mul_left (5 / 4)
  constructor
  · apply ((hpJet.trans hpowerFiveFour).sub hshapeCorrection).congr'
    · filter_upwards [] with ε
      ring
    · rfl
  · constructor
    · exact hhJet.trans hpowerFiveFour
    · apply ((hscaleJet.trans hpowerSixFive).add hscaleCorrection).congr'
      · filter_upwards [] with ε
        ring
      · rfl

/-- Helper for cm-center-proposition: the actual two-stage spectral recovery
is the source signed square-root scale update and its two transverse coordinates. -/
theorem twoStepActualRecovery :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < x.1 →
      DFP.TwoLeg.stateMap x =
        (Real.sqrt (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).1,
          (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).2,
          (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).2) := by
  exact DFP.TwoLeg.stateMap_eventuallyEq_recovered

/-- Helper for cm-center-proposition: the exact scalar curvature ratio of a
source secant step is `1−τ` for `τ ≤ 1`, before specifying an objective function. -/
theorem oneStepCurvatureRatio {ι : Type*} [Fintype ι]
    (z : DFP.AbstractSecantStep ι) (hτ : z.tau ≤ 1) :
    |z.nextGradient ⬝ᵥ z.displacement| / |z.gradient ⬝ᵥ z.displacement| = 1 - z.tau := by
  have hpair := z.nextSlope_eq
  rw [DFP.AbstractSecantStep.nextSlope_def, DFP.AbstractSecantStep.slope_def] at hpair
  have hdecrease := z.predictedDecrease_pos
  rw [DFP.AbstractSecantStep.predictedDecrease_def] at hdecrease
  have hnonzero : z.gradient ⬝ᵥ z.displacement ≠ 0 := ne_of_lt (neg_pos.mp hdecrease)
  rw [hpair, abs_mul, abs_of_nonneg (sub_nonneg.mpr hτ), mul_div_assoc,
    div_self (abs_ne_zero.mpr hnonzero), mul_one]

/-- Helper for cm-center-proposition: the source fixed-scale alternating
controls have exact directional curvature ratios `1/3` and `2/3`. -/
theorem alternatingCurvatureRatios (s : DFP.TwoPhaseOrbit.State) (h : s.PhaseValidity) :
    |(DFP.TwoPhaseOrbit.State.firstStep s h).nextGradient ⬝ᵥ
          (DFP.TwoPhaseOrbit.State.firstStep s h).displacement| /
        |(DFP.TwoPhaseOrbit.State.firstStep s h).gradient ⬝ᵥ
          (DFP.TwoPhaseOrbit.State.firstStep s h).displacement| = 1 / 3 ∧
      |(DFP.TwoPhaseOrbit.State.secondStep s h).nextGradient ⬝ᵥ
          (DFP.TwoPhaseOrbit.State.secondStep s h).displacement| /
        |(DFP.TwoPhaseOrbit.State.secondStep s h).gradient ⬝ᵥ
          (DFP.TwoPhaseOrbit.State.secondStep s h).displacement| = 2 / 3 := by
  have hfirstTau : (DFP.TwoPhaseOrbit.State.firstStep s h).tau ≤ 1 := by
    rw [DFP.TwoPhaseOrbit.State.firstStep_tau, TwoPhaseControls.first_tau]
    norm_num
  have hsecondTau : (DFP.TwoPhaseOrbit.State.secondStep s h).tau ≤ 1 := by
    rw [DFP.TwoPhaseOrbit.State.secondStep_tau, TwoPhaseControls.second_tau]
    norm_num
  constructor
  · rw [oneStepCurvatureRatio _ hfirstTau, DFP.TwoPhaseOrbit.State.firstStep_tau,
      TwoPhaseControls.first_tau]
    norm_num
  · rw [oneStepCurvatureRatio _ hsecondTau, DFP.TwoPhaseOrbit.State.secondStep_tau,
      TwoPhaseControls.second_tau]
    norm_num

/-- Helper for cm-center-proposition: a supplied invariant C⁷ source graph
bundles as the existing SlowCurve with its Taylor coefficients DERIVED from invariance. -/
theorem invariantGraphSlowCurve (p h : ℝ → ℝ)
    (hsmooth : ContDiffAt ℝ 7 (fun ε ↦ (p ε, h ε)) 0)
    (hbase : (p 0, h 0) = (2, 1))
    (htangent : HasFDerivAt (fun ε ↦ (p ε, h ε)) (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0)
    (hinvariant : (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let nextScale := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (nextScale, p nextScale, h nextScale))) :
    ∃ curve : DFP.TwoLeg.SlowCurve, curve.shape = p ∧ curve.high = h := by
  obtain ⟨hp, hh, _⟩ := invariantGraphTaylorJets p h hsmooth hbase htangent hinvariant
  refine ⟨DFP.TwoLeg.SlowCurve.ofAsymptotics p h hp hh hinvariant, ?_, ?_⟩
  · exact DFP.TwoLeg.SlowCurve.ofAsymptotics_shape p h hp hh hinvariant
  · exact DFP.TwoLeg.SlowCurve.ofAsymptotics_high p h hp hh hinvariant

/-- Helper for cm-center-proposition: the actual amplitude multiplier on a
supplied source slow curve has coefficient `−13/2` and a uniform sixth-order remainder.
This is conditional support for cm-scale-and-angle. -/
theorem slowCurveAmplitudeExpansion (curve : DFP.TwoLeg.SlowCurve) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, curve.shape ε, curve.high ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 6) := by
  exact DFP.TwoLeg.slowCurveAmplitudeDrift curve.shape curve.high curve.isInvariant
    curve.shapeRemainder curve.highRemainder

/-- Helper for cm-center-proposition: the actual two-stage center cancellation
has the source coefficient `−116/5`, uniformly BEFORE the initial scale is chosen.
This is conditional support for cm-center-cancellation. -/
theorem slowCurveCenterCancellation (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ C > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar, ∀ j : ℕ,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        let state := orbit.state j
        ‖(orbit.state (j + 1)).center - state.center +
            ((116 / 5) * state.amplitude * state.ε ^ 6) • state.lowVector‖ ≤
          C * state.amplitude * state.ε ^ 7 := by
  exact DFP.TwoPhaseOrbit.slowCurveFullCenterDrift curve.shape curve.high
    curve.isInvariant curve.shapeRemainder curve.highRemainder

/-- Helper for cm-center-proposition: the actual first-stage center change
on a supplied source slow curve is uniformly cubic in the cycle scale. -/
theorem slowCurveHalfCenterBound (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ C > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar, ∀ j : ℕ,
        let state := (DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).state j
        ‖state.halfCenterDisplacement‖ ≤ C * state.amplitude * state.ε ^ 3 := by
  exact DFP.TwoPhaseOrbit.slowCurveHalfCenterDisplacementBound curve.shape curve.high
    curve.isInvariant curve.shapeRemainder curve.highRemainder

/-- Helper for cm-center-proposition: the actual unwrapped source frame has
increment `−3ε² + O(ε⁴)` with one constant for all small initial scales. -/
theorem slowCurveFrameRotation (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ C > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar, ∀ j : ℕ,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        |orbit.frameAngle (j + 1) - orbit.frameAngle j +
            3 * (orbit.state j).ε ^ 2| ≤ C * (orbit.state j).ε ^ 4 := by
  exact DFP.TwoPhaseOrbit.slowCurveFrameRotation curve.shape curve.high
    curve.isInvariant curve.shapeRemainder curve.highRemainder

/-- Helper for cm-center-proposition: the scale coordinate of the physical
source orbit is exactly the scale of the iterated normalized map. -/
theorem orbitScale_eq_iterate (p h : ℝ → ℝ) (ε₀ : ℝ) (j : ℕ) :
    ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).ε =
      (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
  have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
  simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using congrArg Prod.fst hcoordinates

/-- Helper for cm-center-proposition: the source inverse-cubic comparison scale
converges to zero. -/
theorem inverseCubicScale_tendsto_zero :
    Tendsto (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
  have hcoefficient : (0 : ℝ) < 9 / 2 := by norm_num
  have hexponent : (0 : ℝ) < 1 / 3 := by norm_num
  have hbase : Tendsto (fun j : ℕ ↦ (9 / 2 : ℝ) * (j : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hcoefficient
  convert (tendsto_rpow_neg_atTop hexponent).comp hbase using 1
  funext j
  simp only [Function.comp_apply]
  congr 1
  ring

/-- Helper for cm-center-proposition: every sufficiently small actual orbit
of a supplied source slow curve has the source inverse-cubic scale asymptotic. -/
theorem slowCurveScaleAsymptotic (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      (fun j : ℕ ↦ ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).state j).ε)
        ~[atTop] (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) := by
  obtain ⟨εbar, hεbar, hscale⟩ := DFP.TwoLeg.slowCurveScaleAsymptotic curve.shape curve.high
    curve.isInvariant curve.shapeRemainder curve.highRemainder
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  simpa only [orbitScale_eq_iterate] using hscale ε₀ hε₀

/-- Helper for cm-center-proposition: a supplied source slow curve gives
positive limiting amplitude, coefficient `13/3`, convergent centers, and a
uniform cubic center tail. The amplitude statement here is asymptotic equivalence;
it does not assert the stronger quadratic amplitude remainder in cm-limiting-scales. -/
theorem slowCurveLimitingScales (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∃ Glim > 0, ∃ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
          (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) ~[atTop]
            (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) ∧
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) ∧
          ∀ j : ℕ, ‖(orbit.state j).center - Clim‖ + ‖(orbit.state j).middleCenter - Clim‖ ≤
            K * (orbit.state j).ε ^ 3 := by
  obtain ⟨ηAmplitude, hηAmplitude, hamplitude⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeAsymptotics curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηCenter, hηCenter, hcenter⟩ :=
    DFP.TwoPhaseOrbit.slowCurveCenterTendsto curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηTail, hηTail, K, hK, htail⟩ :=
    DFP.TwoPhaseOrbit.slowCurveCenterTailUniformBound curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  let εbar := min ηAmplitude (min ηCenter ηTail)
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · exact lt_min hηAmplitude (lt_min hηCenter.1 hηTail.1)
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans_lt hηCenter.2
  refine ⟨εbar, hεbar, K, hK, ?_⟩
  intro ε₀ hε₀
  have hεAmplitude : ε₀ ∈ Set.Ioc 0 ηAmplitude :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεCenter : ε₀ ∈ Set.Ioc 0 ηCenter :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεTail : ε₀ ∈ Set.Ioc 0 ηTail :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨Glim, hGlim, hGlimLimit, hfirstOrder⟩ := hamplitude ε₀ hεAmplitude
  obtain ⟨Clim, hClimLimit⟩ := hcenter ε₀ hεCenter
  exact ⟨Glim, hGlim, Clim, hGlimLimit, hfirstOrder, hClimLimit,
    htail ε₀ hεTail Clim hClimLimit⟩

/-- Helper for cm-center-proposition: the source frame angle is strictly
decreasing, diverges, and has vanishing steps; Nat.find first crossings on successive
turns approach every target angle. This is conditional support from a supplied SlowCurve. -/
theorem slowCurveFrameFirstCrossings (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      StrictAnti orbit.frameAngle ∧ Tendsto orbit.frameAngle atTop atBot ∧
      Tendsto (fun j : ℕ ↦ orbit.frameAngle j - orbit.frameAngle (j + 1)) atTop (𝓝 0) ∧
      ∀ θ : ℝ, ∃ j : ℕ → ℕ, ∃ m : ℕ → ℤ, StrictMono j ∧
        Tendsto (fun i ↦ orbit.frameAngle (j i) + m i * (2 * Real.pi)) atTop (𝓝 θ) := by
  obtain ⟨ηRotation, hηRotation, C, hC, hrotation⟩ := slowCurveFrameRotation curve
  obtain ⟨ηDivergence, hηDivergence, hdivergence⟩ :=
    DFP.TwoPhaseOrbit.slowCurveFrameAngleTendstoAtBot curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηGraph, hηGraph, hgraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηScale, hηScale, hscale⟩ := slowCurveScaleAsymptotic curve
  let εbar := min ηRotation (min ηDivergence (min ηGraph
    (min ηScale (min 1 (1 / (C + 1))))))
  have hden : 0 < C + 1 := by linarith
  have hεbarPos : 0 < εbar := by
    exact lt_min hηRotation.1 (lt_min hηDivergence.1 (lt_min hηGraph.1
      (lt_min hηScale (lt_min zero_lt_one (one_div_pos.mpr hden)))))
  have hεbarLt : εbar < 1 / 4 := (min_le_left _ _).trans_lt hηRotation.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hsmall : ε₀ ≤ ηRotation ∧ ε₀ ≤ ηDivergence ∧ ε₀ ≤ ηGraph ∧
      ε₀ ≤ ηScale ∧ ε₀ ≤ 1 ∧ ε₀ ≤ 1 / (C + 1) := by
    simpa only [εbar, le_min_iff] using hε₀.2
  have hεRotation : ε₀ ∈ Set.Ioc 0 ηRotation := ⟨hε₀.1, hsmall.1⟩
  have hεDivergence : ε₀ ∈ Set.Ioc 0 ηDivergence := ⟨hε₀.1, hsmall.2.1⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph := ⟨hε₀.1, hsmall.2.2.1⟩
  have hεScale : ε₀ ∈ Set.Ioc 0 ηScale := ⟨hε₀.1, hsmall.2.2.2.1⟩
  have hscaleRange (j : ℕ) : 0 < (orbit.state j).ε ∧ (orbit.state j).ε ≤ ε₀ := by
    simpa only [orbit, orbitScale_eq_iterate, Set.mem_Ioc] using (hgraph ε₀ hεGraph j).2
  have hscaleZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) :=
    (hscale ε₀ hεScale).symm.tendsto_nhds inverseCubicScale_tendsto_zero
  have hstrict : StrictAnti orbit.frameAngle := by
    apply strictAnti_nat_of_succ_lt
    intro j
    have hεPos := (hscaleRange j).1
    have hεOne : (orbit.state j).ε ≤ 1 := (hscaleRange j).2.trans hsmall.2.2.2.2.1
    have hεDen : (orbit.state j).ε ≤ 1 / (C + 1) :=
      (hscaleRange j).2.trans hsmall.2.2.2.2.2
    have hmul : (orbit.state j).ε * (C + 1) ≤ 1 := (le_div_iff₀ hden).mp hεDen
    have hεSquare : (orbit.state j).ε ^ 2 ≤ (orbit.state j).ε := by
      nlinarith
    have hquadratic : C * (orbit.state j).ε ^ 2 ≤ 1 := by
      nlinarith
    have hquartic : C * (orbit.state j).ε ^ 4 ≤ (orbit.state j).ε ^ 2 := by
      calc
        C * (orbit.state j).ε ^ 4 =
            (C * (orbit.state j).ε ^ 2) * (orbit.state j).ε ^ 2 := by ring
        _ ≤ 1 * (orbit.state j).ε ^ 2 :=
          mul_le_mul_of_nonneg_right hquadratic (sq_nonneg _)
        _ = (orbit.state j).ε ^ 2 := one_mul _
    have hbound := (abs_le.mp (hrotation ε₀ hεRotation j)).2
    have hsquarePos : 0 < (orbit.state j).ε ^ 2 := pow_pos hεPos 2
    nlinarith
  have hbot : Tendsto orbit.frameAngle atTop atBot := hdivergence ε₀ hεDivergence
  have hupperZero : Tendsto
      (fun j : ℕ ↦ 3 * (orbit.state j).ε ^ 2 + C * (orbit.state j).ε ^ 4)
      atTop (𝓝 0) := by
    have hraw := ((hscaleZero.pow 2).const_mul 3).add ((hscaleZero.pow 4).const_mul C)
    simpa using hraw
  have hdropNonneg : ∀ j : ℕ, 0 ≤ orbit.frameAngle j - orbit.frameAngle (j + 1) := by
    intro j
    exact sub_nonneg.mpr (hstrict (Nat.lt_succ_self j)).le
  have hdropUpper : ∀ j : ℕ, orbit.frameAngle j - orbit.frameAngle (j + 1) ≤
      3 * (orbit.state j).ε ^ 2 + C * (orbit.state j).ε ^ 4 := by
    intro j
    have hbound : -(C * (orbit.state j).ε ^ 4) ≤
        orbit.frameAngle (j + 1) - orbit.frameAngle j + 3 * (orbit.state j).ε ^ 2 := by
      simpa only [orbit] using (abs_le.mp (hrotation ε₀ hεRotation j)).1
    linarith
  have hstep : Tendsto
      (fun j : ℕ ↦ orbit.frameAngle j - orbit.frameAngle (j + 1)) atTop (𝓝 0) :=
    squeeze_zero hdropNonneg hdropUpper hupperZero
  refine ⟨hstrict, hbot, hstep, ?_⟩
  intro θ
  have hperiod : 0 < 2 * Real.pi := mul_pos zero_lt_two Real.pi_pos
  exact Real.existsSubseqAddIntMulTendsto (2 * Real.pi) hperiod hstrict hbot hstep θ

/-- Helper for cm-center-proposition: the actual centered source map admits
canonical C⁸ cutoff data for its zero-start graph transform. The fixed rational
rates are chosen before the cutoff and before any initial orbit scale; no
fixed-graph regularity theorem is used. -/
theorem sourceCutoffData :
    ∃ d : LocalInvariantGraph.MetricGraphTransformData (ℝ × ℝ),
      d.nu = 8 ∧ d.L = stableDerivative ∧ d.slope = 1 / 2 ∧
      d.epsilon = 1 / 1000 ∧ d.lower = 999 / 1000 ∧ d.linearRate = 8 / 9 ∧
      HasFDerivAt d.R (0 : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × (ℝ × ℝ))) (0, 0) ∧
      centeredStateMap =ᶠ[𝓝 (0, 0)] LocalInvariantGraph.metricCenterStableMap d ∧
      ∀ r : ℕ, 1 ≤ r → r ≤ 8 →
        ((d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ))) *
          (d.lower : ℝ)⁻¹ ^ r < 1 := by
  let epsilon : NNReal := 1 / 1000
  let lower : NNReal := 999 / 1000
  let linearRate : NNReal := 8 / 9
  let slope : NNReal := 1 / 2
  have hν : 2 ≤ 8 := by norm_num
  have hνone : 1 ≤ 8 := by norm_num
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hlower : 0 < lower := by norm_num [lower]
  have hadd : lower + epsilon = 1 := by norm_num [lower, epsilon]
  have hslopeOne : slope ≤ 1 := by norm_num [slope]
  have hepsilonOne : epsilon < 1 := by norm_num [epsilon]
  have hlinearRate : linearRate < 1 := by norm_num [linearRate]
  have hslope : (linearRate * slope + epsilon) * lower⁻¹ ≤ slope := by
    have hreal : (((linearRate * slope + epsilon) * lower⁻¹ : NNReal) : ℝ) ≤
        (slope : ℝ) := by
      norm_num [linearRate, slope, epsilon, lower]
    exact_mod_cast hreal
  have hrate : LocalInvariantGraph.metricGraphTransformRate lower linearRate epsilon slope < 1 := by
    have hreal : (LocalInvariantGraph.metricGraphTransformRate lower linearRate epsilon slope : ℝ)
        < 1 := by
      rw [LocalInvariantGraph.metricGraphTransformRate_coe]
      norm_num [linearRate, slope, epsilon, lower]
    exact_mod_cast hreal
  have hL : ‖stableDerivative‖ ≤ (linearRate : ℝ) := by
    have hcompare : (7 / 9 : ℝ) ≤ (linearRate : ℝ) := by norm_num [linearRate]
    exact stableDerivative_norm_le.trans hcompare
  have hNzero := LocalInvariantGraph.centerStable_remainder_zero centeredStateMap
    stableDerivative centeredStateMap_zero
  have hNderiv := LocalInvariantGraph.centerStable_remainder_hasFDerivAt_zero
    centeredStateMap stableDerivative centeredStateMap_hasFDerivAt
  have hNsmooth := LocalInvariantGraph.centerStable_remainder_contDiffAt 8
    centeredStateMap stableDerivative centeredStateMap_analyticAt.contDiffAt
  obtain ⟨R, hRsmooth, hRsupport, hRzero, hRLip, hRderiv, hRgerm⟩ :=
    LocalInvariantGraph.cutoffRemainderWithZeroDerivative 8
      (fun x ↦ centeredStateMap x - LocalCutoff.centerStable stableDerivative x)
      hνone hNsmooth hNzero hNderiv hepsilon
  obtain ⟨stableBound, hstableBound⟩ :=
    LocalInvariantGraph.exists_stableCoordinateBound R hRsmooth.continuous hRsupport
  have hlinearRateReal : (linearRate : ℝ) < 1 := by exact_mod_cast hlinearRate
  obtain ⟨radius, hradius⟩ := LocalInvariantGraph.metricRadius_bound hlinearRateReal
  have hcenter : ∀ ξ : SmallLipschitzGraph (ℝ × ℝ) radius slope,
      Function.Bijective (fun u ↦ u + (R (u, ξ u)).1) := by
    intro ξ
    obtain ⟨homeomorph, hhomeomorph⟩ :=
      LocalInvariantGraph.exists_centerProjectionHomeomorph R hRLip ξ hslopeOne hepsilonOne
    rw [← hhomeomorph]
    exact homeomorph.bijective
  have hinverse : ∀ ξ : SmallLipschitzGraph (ℝ × ℝ) radius slope,
      LipschitzWith lower⁻¹ (Function.invFun (fun u ↦ u + (R (u, ξ u)).1)) := by
    intro ξ
    exact LocalInvariantGraph.lipschitzWith_invFun_centerProjection R hRLip ξ
      hslopeOne lower hlower hadd
  have hinverseDistance : ∀ (ξ ζ : SmallLipschitzGraph (ℝ × ℝ) radius slope) (v : ℝ),
      dist (Function.invFun (fun u ↦ u + (R (u, ξ u)).1) v)
          (Function.invFun (fun u ↦ u + (R (u, ζ u)).1) v) ≤
        (lower⁻¹ : ℝ) * (epsilon : ℝ) * dist ξ ζ := by
    intro ξ ζ v
    exact LocalInvariantGraph.dist_invFun_centerProjection_le R hRLip ξ ζ
      hslopeOne lower hlower hadd v
  let d := LocalInvariantGraph.metricGraphTransformData_of_cutoff 8 R stableDerivative
    radius slope epsilon lower linearRate stableBound hν hRsmooth hRsupport hRzero hRLip
    hslopeOne hlower hadd hcenter hinverse hinverseDistance hL hlinearRate hstableBound
    hradius hslope hrate
  have hmodel := LocalInvariantGraph.centerStable_remainder_germ centeredStateMap
    stableDerivative R hRgerm
  have hdR : d.R = R := by rfl
  have hdL : d.L = stableDerivative := by rfl
  have hmodelGerm : centeredStateMap =ᶠ[𝓝 (0, 0)]
      LocalInvariantGraph.metricCenterStableMap d := by
    filter_upwards [hmodel.symm] with x hx
    rw [LocalInvariantGraph.metricCenterStableMap_eq, hdR, hdL]
    exact hx
  refine ⟨d, rfl, hdL, rfl, rfl, rfl, rfl, ?_, hmodelGerm, ?_⟩
  · rw [hdR]
    exact hRderiv
  · intro r hrOne hrEight
    have hdSlope : d.slope = 1 / 2 := by rfl
    have hdEpsilon : d.epsilon = 1 / 1000 := by rfl
    have hdLower : d.lower = 999 / 1000 := by rfl
    have hdRate : d.linearRate = 8 / 9 := by rfl
    rw [hdSlope, hdEpsilon, hdLower, hdRate]
    interval_cases r
    all_goals norm_num

/-- Helper for cm-center-proposition: a C⁷ fixed graph of the exact source
cutoff transform transfers back to a tangent invariant graph of the original
stateMap. This support lemma differentiates invariance only AFTER regularity
has been supplied by the source uniform-iterate/Arzelà–Ascoli argument. -/
theorem invariantGraphOfSmoothFixedGraph
    (d : LocalInvariantGraph.MetricGraphTransformData (ℝ × ℝ))
    (hRderiv : HasFDerivAt d.R
      (0 : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × (ℝ × ℝ))) (0, 0))
    (hgerm : centeredStateMap =ᶠ[𝓝 (0, 0)] LocalInvariantGraph.metricCenterStableMap d)
    (ζ : SmallLipschitzGraph (ℝ × ℝ) d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    (hsmooth : ContDiffAt ℝ 7 (ζ : ℝ → ℝ × ℝ) 0) :
    ∃ p h : ℝ → ℝ,
      ContDiffAt ℝ 7 (fun ε ↦ (p ε, h ε)) 0 ∧ (p 0, h 0) = (2, 1) ∧
      HasFDerivAt (fun ε ↦ (p ε, h ε)) (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 ∧
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let nextScale := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (nextScale, p nextScale, h nextScale)) := by
  have hzero : (ζ : ℝ → ℝ × ℝ) 0 = 0 := SmallLipschitzGraph.zero_apply ζ
  have hseven : (7 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hderivative : HasFDerivAt (ζ : ℝ → ℝ × ℝ)
      (fderiv ℝ (ζ : ℝ → ℝ × ℝ) 0) 0 :=
    (hsmooth.differentiableAt hseven).hasFDerivAt
  have hmodelZero := LocalInvariantGraph.metricCenterStableMap_zero d
  have hmodelDerivative :=
    LocalInvariantGraph.metricCenterStableMap_hasFDerivAt_of_zeroDerivative d hRderiv
  have hmodelInvariant := LocalInvariantGraph.metricFixedGraph_invariant d ζ hfixed
  have hrate : (d.linearRate : ℝ) < 1 := by exact_mod_cast d.hlinearRate
  have htangent := LocalInvariantGraph.tangent_zero_of_centerStable_invariant
    (ζ : ℝ → ℝ × ℝ) (fderiv ℝ (ζ : ℝ → ℝ × ℝ) 0)
    (LocalInvariantGraph.metricCenterStableMap d) d.L hzero hderivative
    hmodelZero hmodelDerivative hmodelInvariant (d.hL.trans_lt hrate)
  have htendsto : Tendsto (ζ : ℝ → ℝ × ℝ) (𝓝 0) (𝓝 0) := by
    simpa only [hzero] using hsmooth.continuousAt.tendsto
  have hpathTendsto : Tendsto (fun u : ℝ ↦ (u, ζ u)) (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [nhds_prod_eq, id_eq] using tendsto_id.prodMk htendsto
  have hsourceModel := hgerm.comp_tendsto hpathTendsto
  have hsourceInvariant :
      (fun u ↦ (centeredStateMap (u, ζ u)).2) =ᶠ[𝓝 0]
        (fun u ↦ ζ (centeredStateMap (u, ζ u)).1) := by
    filter_upwards [hmodelInvariant, hsourceModel] with u hu hmap
    dsimp only [Function.comp_apply] at hmap
    rw [hmap]
    exact hu
  let p : ℝ → ℝ := fun u ↦ (ζ u).1 + 2
  let h : ℝ → ℝ := fun u ↦ (ζ u).2 + 1
  have hgraphEq : (fun u ↦ (p u, h u)) = fun u ↦ ζ u + ((2, 1) : ℝ × ℝ) := by
    rfl
  refine ⟨p, h, ?_, ?_, ?_, ?_⟩
  · rw [hgraphEq]
    exact hsmooth.add contDiffAt_const
  · simp only [p, h, hzero, Prod.fst_zero, Prod.snd_zero, zero_add]
  · rw [hgraphEq]
    exact htangent.add_const (2, 1)
  · filter_upwards [hsourceInvariant] with u hu
    rw [centeredStateMap_apply] at hu
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · have hshape := congrArg Prod.fst hu
        dsimp only [p]
        dsimp only at hshape
        linarith
      · have hhigh := congrArg Prod.snd hu
        dsimp only [h]
        dsimp only at hhigh
        linarith

/-- Helper for cm-center-proposition: Nat.find first-crossing subsequences
of a real angle lift approach every unit direction under actual planar rotation. -/
theorem rotationSubsequenceOfFirstCrossings (φ : ℕ → ℝ)
    (hcrossings : ∀ θ : ℝ, ∃ j : ℕ → ℕ, ∃ m : ℕ → ℤ, StrictMono j ∧
      Tendsto (fun i ↦ φ (j i) + m i * (2 * Real.pi)) atTop (𝓝 θ))
    (v : EuclideanSpace ℝ (Fin 2)) (hv : ‖v‖ = 1) :
    ∃ j : ℕ → ℕ, StrictMono j ∧
      Tendsto (fun i ↦ EuclideanPlane.rotation (φ (j i))
        (WithLp.toLp 2 ![(1 : ℝ), 0])) atTop (𝓝 v) := by
  let e : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(1 : ℝ), 0]
  let θ : ℝ := (EuclideanPlane.orientation.oangle e v).toReal
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hangle : (θ : Real.Angle) = EuclideanPlane.orientation.oangle e v :=
    Real.Angle.coe_toReal _
  have hnorm : ‖e‖ = ‖v‖ := he.trans hv.symm
  have hrotation : EuclideanPlane.rotation (θ : Real.Angle) e = v := by
    rw [hangle]
    exact (EuclideanPlane.orientation.rotation_oangle_eq_iff_norm_eq e v).mpr hnorm
  obtain ⟨j, m, hj, hlimit⟩ := hcrossings θ
  have hcontinuous : Continuous (fun t : Real.Angle ↦ EuclideanPlane.rotation t e) := by
    simp only [EuclideanPlane.rotation_apply]
    exact (Real.Angle.continuous_cos.smul continuous_const).add
      (Real.Angle.continuous_sin.smul continuous_const)
  have hrotationLimit := ((hcontinuous.comp Real.Angle.continuous_coe).tendsto θ).comp hlimit
  have hperiod (i : ℕ) :
      ((φ (j i) + m i * (2 * Real.pi) : ℝ) : Real.Angle) = (φ (j i) : Real.Angle) := by
    rw [Real.Angle.coe_add, Real.Angle.intCast_mul_eq_zsmul]
    simp only [Real.Angle.coe_two_pi, smul_zero, add_zero]
  refine ⟨j, hj, ?_⟩
  dsimp only [Function.comp_apply] at hrotationLimit
  rw [hrotation] at hrotationLimit
  apply hrotationLimit.congr'
  filter_upwards [] with i
  exact congrArg (fun angle : Real.Angle ↦ EuclideanPlane.rotation angle e) (hperiod i)

/-- Helper for cm-center-proposition: a sequence approaching the source rotating
circle has EXACTLY that circle as its cluster set when its angle lift has the
source first-crossing subsequences. No compactness existence argument is used. -/
theorem clusterSetOfRotatingCircle (x : ℕ → EuclideanSpace ℝ (Fin 2)) (φ : ℕ → ℝ)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (hG : 0 < G)
    (hcrossings : ∀ θ : ℝ, ∃ j : ℕ → ℕ, ∃ m : ℕ → ℤ, StrictMono j ∧
      Tendsto (fun i ↦ φ (j i) + m i * (2 * Real.pi)) atTop (𝓝 θ))
    (herror : Tendsto (fun n ↦ ‖x n - (C + G • EuclideanPlane.rotation (φ n)
      (WithLp.toLp 2 ![(1 : ℝ), 0]))‖) atTop (𝓝 0)) :
    {z : EuclideanSpace ℝ (Fin 2) | MapClusterPt z atTop x} =
      DFP.TwoPhaseOrbit.limitCircle C G := by
  let model : ℕ → EuclideanSpace ℝ (Fin 2) := fun n ↦
    C + G • EuclideanPlane.rotation (φ n) (WithLp.toLp 2 ![(1 : ℝ), 0])
  have hnormModel (n : ℕ) : ‖model n - C‖ = G := by
    simp [model, norm_smul, Real.norm_eq_abs, abs_of_pos hG,
      EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hradialError (n : ℕ) : |‖x n - C‖ - G| ≤ ‖x n - model n‖ := by
    rw [← hnormModel n]
    have hnormalized : (x n - C) - (model n - C) = x n - model n := by abel
    simpa only [hnormalized] using abs_norm_sub_norm_le (x n - C) (model n - C)
  have hradialZero : Tendsto (fun n ↦ ‖x n - C‖ - G) atTop (𝓝 0) := by
    apply squeeze_zero_norm
    · intro n
      simpa only [Real.norm_eq_abs] using hradialError n
    · exact herror
  have hradial : Tendsto (fun n ↦ ‖x n - C‖) atTop (𝓝 G) := by
    simpa only [sub_add_cancel, zero_add] using hradialZero.add_const G
  have herrorVector : Tendsto (fun n ↦ x n - model n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr herror
  ext z
  constructor
  · intro hcluster
    obtain ⟨j, hj, hjlimit⟩ := hcluster.tendsto_subseq
    have hnormLimit := (hjlimit.sub_const C).norm
    have hnorm : ‖z - C‖ = G := tendsto_nhds_unique hnormLimit
      (hradial.comp hj.tendsto_atTop)
    rw [DFP.TwoPhaseOrbit.limitCircle_eq_sphere C G hG, Metric.mem_sphere, dist_eq_norm]
    exact hnorm
  · intro hcircle
    obtain ⟨v, hv, rfl⟩ := DFP.TwoPhaseOrbit.mem_limitCircle.mp hcircle
    obtain ⟨j, hj, hrotation⟩ := rotationSubsequenceOfFirstCrossings φ hcrossings v hv
    have hmodel : Tendsto (fun i ↦ model (j i)) atTop (𝓝 (C + G • v)) := by
      exact tendsto_const_nhds.add (tendsto_const_nhds.smul hrotation)
    have hpoint : Tendsto (fun i ↦ x (j i)) atTop (𝓝 (C + G • v)) := by
      have hsum := (herrorVector.comp hj.tendsto_atTop).add hmodel
      simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hsum
    exact hpoint.mapClusterPt.of_comp hj.tendsto_atTop

/-- Helper for cm-center-proposition: the physical low direction is the first
column of the actual eigenframe, equivalently its action on `(1,0)`. -/
theorem lowVector_eq_frameBasis (s : DFP.TwoPhaseOrbit.State) :
    s.lowVector = WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), 0]) := by
  ext i
  rw [DFP.TwoPhaseOrbit.State.lowVector_apply]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Helper for cm-center-proposition: an oriented physical eigenframe has a
unit low direction. -/
theorem lowVector_norm (s : DFP.TwoPhaseOrbit.State)
    (hframe : s.frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) : ‖s.lowVector‖ = 1 := by
  rw [lowVector_eq_frameBasis,
    Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup _ hframe]
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- Helper for cm-center-proposition: the actual gradient differs from its
low-direction component by exactly the high coordinate `G*p*ε²` in norm. -/
theorem gradientLowVector_error (s : DFP.TwoPhaseOrbit.State)
    (hframe : s.frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    ‖s.gradient - s.amplitude • s.lowVector‖ =
      |s.amplitude| * |s.p * s.ε ^ 2| := by
  have hcoordinates : (![(1 : ℝ), s.p * s.ε ^ 2] : Fin 2 → ℝ) - ![(1 : ℝ), 0] =
      ![(0 : ℝ), s.p * s.ε ^ 2] := by
    ext i
    fin_cases i
    · simp
    · simp
  rw [DFP.TwoPhaseOrbit.State.gradient_def, lowVector_eq_frameBasis,
    ← smul_sub, ← WithLp.toLp_sub, ← Matrix.mulVec_sub, hcoordinates,
    norm_smul, Real.norm_eq_abs,
    Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup _ hframe]
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

/-- Helper for cm-center-proposition: physical source states lie on the
supplied slow curve and retain positive decreasing cycle scales. -/
theorem slowCurveStateOnGraph (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar, ∀ j : ℕ,
      let state := (DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).state j
      (state.p, state.h) = (curve.shape state.ε, curve.high state.ε) ∧
        0 < state.ε ∧ state.ε ≤ ε₀ := by
  obtain ⟨εbar, hεbar, hgraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀ j
  have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates curve.shape curve.high ε₀ j
  rw [DFP.TwoPhaseOrbit.State.coordinates_def] at hcoordinates
  have hstateGraph := (hgraph ε₀ hε₀ j).1
  rw [← hcoordinates] at hstateGraph
  have hstateRange := (hgraph ε₀ hε₀ j).2
  rw [← hcoordinates] at hstateRange
  exact ⟨congrArg Prod.snd hstateGraph, hstateRange⟩

/-- Helper for cm-center-proposition: the exact spectral representation
approaches its rotating low-direction circle whenever the source scale,
amplitude, shape and center have their derived limits. -/
theorem pointLowVectorApproximation (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (hframe : ∀ j, (orbit.state j).frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (hscale : Tendsto (fun j ↦ (orbit.state j).ε) atTop (𝓝 0))
    (hshape : Tendsto (fun j ↦ (orbit.state j).p) atTop (𝓝 2))
    (hamplitude : Tendsto (fun j ↦ (orbit.state j).amplitude) atTop (𝓝 G))
    (hcenter : Tendsto (fun j ↦ (orbit.state j).center) atTop (𝓝 C)) :
    Tendsto (fun j ↦ ‖(orbit.state j).point -
      (C + G • (orbit.state j).lowVector)‖) atTop (𝓝 0) := by
  have hcenterNorm : Tendsto (fun j ↦ ‖(orbit.state j).center - C‖) atTop (𝓝 0) := by
    simpa using (hcenter.sub_const C).norm
  have hhighNorm : Tendsto
      (fun j ↦ |(orbit.state j).amplitude| * |(orbit.state j).p * (orbit.state j).ε ^ 2|)
      atTop (𝓝 0) := by
    have hraw := (hamplitude.mul (hshape.mul (hscale.pow 2))).abs
    simpa only [zero_pow (Nat.succ_ne_zero 1), mul_zero, abs_zero, abs_mul] using hraw
  have hamplitudeNorm : Tendsto (fun j ↦ |(orbit.state j).amplitude - G|) atTop (𝓝 0) := by
    simpa using (hamplitude.sub_const G).abs
  have hupper : Tendsto
      (fun j ↦ ‖(orbit.state j).center - C‖ +
        |(orbit.state j).amplitude| * |(orbit.state j).p * (orbit.state j).ε ^ 2| +
        |(orbit.state j).amplitude - G|) atTop (𝓝 0) := by
    simpa using (hcenterNorm.add hhighNorm).add hamplitudeNorm
  have hbound (j : ℕ) :
      ‖(orbit.state j).point - (C + G • (orbit.state j).lowVector)‖ ≤
        ‖(orbit.state j).center - C‖ +
          |(orbit.state j).amplitude| * |(orbit.state j).p * (orbit.state j).ε ^ 2| +
          |(orbit.state j).amplitude - G| := by
    let state := orbit.state j
    have hdecomposition : state.point - (C + G • state.lowVector) =
        (state.center - C) + (state.gradient - state.amplitude • state.lowVector) +
          (state.amplitude - G) • state.lowVector := by
      rw [DFP.TwoPhaseOrbit.State.center_def]
      module
    rw [hdecomposition]
    calc
      ‖(state.center - C) + (state.gradient - state.amplitude • state.lowVector) +
          (state.amplitude - G) • state.lowVector‖ ≤
        ‖state.center - C‖ + ‖state.gradient - state.amplitude • state.lowVector‖ +
          ‖(state.amplitude - G) • state.lowVector‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖state.center - C‖ + |state.amplitude| * |state.p * state.ε ^ 2| +
          |state.amplitude - G| := by
        rw [gradientLowVector_error state (hframe j), norm_smul, Real.norm_eq_abs,
          lowVector_norm state (hframe j), mul_one]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) hbound hupper

/-- Helper for cm-center-proposition: the actual even and odd endpoints have
the full source circle as cluster set when the derived spectral errors vanish
and the SOURCE eigenframe has first-crossing subsequences. -/
theorem endpointCircleFromSourceFrame (orbit : DFP.TwoPhaseOrbit) (φ : ℕ → ℝ)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (hG : 0 < G)
    (hframe : ∀ j, (orbit.state j).frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (hscale : Tendsto (fun j ↦ (orbit.state j).ε) atTop (𝓝 0))
    (hshape : Tendsto (fun j ↦ (orbit.state j).p) atTop (𝓝 2))
    (hamplitude : Tendsto (fun j ↦ (orbit.state j).amplitude) atTop (𝓝 G))
    (hcenter : Tendsto (fun j ↦ (orbit.state j).center) atTop (𝓝 C))
    (hsteps : Tendsto (fun j ↦ ‖(orbit.state j).firstDisplacement‖) atTop (𝓝 0))
    (hrepresentation : ∀ j, (orbit.state j).lowVector =
      EuclideanPlane.rotation (φ j) (WithLp.toLp 2 ![(1 : ℝ), 0]))
    (hcrossings : ∀ θ : ℝ, ∃ j : ℕ → ℕ, ∃ m : ℕ → ℤ, StrictMono j ∧
      Tendsto (fun i ↦ φ (j i) + m i * (2 * Real.pi)) atTop (𝓝 θ)) :
    {z : EuclideanSpace ℝ (Fin 2) | MapClusterPt z atTop orbit.endpoint} =
      DFP.TwoPhaseOrbit.limitCircle C G := by
  let model : ℕ → EuclideanSpace ℝ (Fin 2) := fun j ↦
    C + G • EuclideanPlane.rotation (φ j) (WithLp.toLp 2 ![(1 : ℝ), 0])
  have hevenError : Tendsto (fun j ↦ ‖(orbit.state j).point - model j‖) atTop (𝓝 0) := by
    have hraw := pointLowVectorApproximation orbit C G hframe hscale hshape hamplitude hcenter
    apply hraw.congr'
    filter_upwards [] with j
    rw [hrepresentation j]
  have hoddBound (j : ℕ) :
      ‖orbit.endpoint (2 * j + 1) - model j‖ ≤
        ‖(orbit.state j).firstDisplacement‖ + ‖(orbit.state j).point - model j‖ := by
    rw [DFP.TwoPhaseOrbit.endpoint_odd, DFP.TwoPhaseOrbit.State.middlePoint_def]
    have hnormalize : (orbit.state j).point + (orbit.state j).firstDisplacement - model j =
        (orbit.state j).firstDisplacement + ((orbit.state j).point - model j) := by abel
    rw [hnormalize]
    exact norm_add_le _ _
  have hoddError : Tendsto (fun j ↦ ‖orbit.endpoint (2 * j + 1) - model j‖)
      atTop (𝓝 0) := by
    have hupper : Tendsto
        (fun j ↦ ‖(orbit.state j).firstDisplacement‖ + ‖(orbit.state j).point - model j‖)
        atTop (𝓝 0) := by
      simpa using hsteps.add hevenError
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hoddBound hupper
  let liftedAngle : ℕ → ℝ := fun k ↦ φ (k / 2)
  have hfullError : Tendsto (fun k ↦ ‖orbit.endpoint k -
      (C + G • EuclideanPlane.rotation (liftedAngle k) (WithLp.toLp 2 ![(1 : ℝ), 0]))‖)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_even_odd
    · simpa [liftedAngle, model, DFP.TwoPhaseOrbit.endpoint_even] using hevenError
    · have hdiv (j : ℕ) : (2 * j + 1) / 2 = j := by omega
      simpa [liftedAngle, model, hdiv] using hoddError
  have hfullCrossings : ∀ θ : ℝ, ∃ j : ℕ → ℕ, ∃ m : ℕ → ℤ, StrictMono j ∧
      Tendsto (fun i ↦ liftedAngle (j i) + m i * (2 * Real.pi)) atTop (𝓝 θ) := by
    intro θ
    obtain ⟨j, m, hj, hlimit⟩ := hcrossings θ
    refine ⟨fun i ↦ 2 * j i, m, ?_, ?_⟩
    · intro i k hik
      exact Nat.mul_lt_mul_of_pos_left (hj hik) Nat.two_pos
    · simpa [liftedAngle] using hlimit
  exact clusterSetOfRotatingCircle orbit.endpoint liftedAngle C G hG hfullCrossings hfullError

/-- Helper for cm-center-proposition: every sufficiently small trajectory of
a supplied SOURCE slow curve has exactly its limiting circle as the cluster set
of ALL actual even and odd endpoints. The decisive subsequences are the source
frame's Nat.find first crossings, and the odd steps vanish. -/
theorem slowCurveCircleGeometry (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∃ Glim > 0, ∃ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) ∧
        Tendsto orbit.frameAngle atTop atBot ∧
        {z : EuclideanSpace ℝ (Fin 2) | MapClusterPt z atTop orbit.endpoint} =
          DFP.TwoPhaseOrbit.limitCircle Clim Glim := by
  obtain ⟨ηCrossing, hηCrossing, hcrossing⟩ := slowCurveFrameFirstCrossings curve
  obtain ⟨ηGraph, hηGraph, hgraph⟩ := slowCurveStateOnGraph curve
  obtain ⟨ηScale, hηScale, hscale⟩ := slowCurveScaleAsymptotic curve
  have heighth : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by norm_num
  obtain ⟨ηValid, hηValid, hvalid⟩ := DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity
    curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
    (1 / 8) heighth
  obtain ⟨ηFrame, hηFrame, hframe⟩ :=
    DFP.TwoPhaseOrbit.slowCurveFrameAngleRepresentsLowVector curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder (1 / 8) heighth
  obtain ⟨ηStep, hηStep, hstep⟩ := DFP.TwoPhaseOrbit.slowCurveFirstStepNormRemainder
    curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηLimits, hηLimits, K, hK, hlimits⟩ := slowCurveLimitingScales curve
  let εbar := min ηCrossing (min ηGraph (min ηScale (min ηValid
    (min ηFrame (min ηStep ηLimits)))))
  have hεbarPos : 0 < εbar := by
    exact lt_min hηCrossing.1 (lt_min hηGraph.1 (lt_min hηScale
      (lt_min hηValid.1 (lt_min hηFrame.1 (lt_min hηStep hηLimits.1)))))
  have hεbarLt : εbar < 1 / 4 := (min_le_left _ _).trans_lt hηCrossing.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hsmall : ε₀ ≤ ηCrossing ∧ ε₀ ≤ ηGraph ∧ ε₀ ≤ ηScale ∧ ε₀ ≤ ηValid ∧
      ε₀ ≤ ηFrame ∧ ε₀ ≤ ηStep ∧ ε₀ ≤ ηLimits := by
    simpa only [εbar, le_min_iff] using hε₀.2
  have hεCrossing : ε₀ ∈ Set.Ioc 0 ηCrossing := ⟨hε₀.1, hsmall.1⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph := ⟨hε₀.1, hsmall.2.1⟩
  have hεScale : ε₀ ∈ Set.Ioc 0 ηScale := ⟨hε₀.1, hsmall.2.2.1⟩
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid := ⟨hε₀.1, hsmall.2.2.2.1⟩
  have hεFrame : ε₀ ∈ Set.Ioc 0 ηFrame := ⟨hε₀.1, hsmall.2.2.2.2.1⟩
  have hεStep : ε₀ ∈ Set.Ioc 0 ηStep := ⟨hε₀.1, hsmall.2.2.2.2.2.1⟩
  have hεLimits : ε₀ ∈ Set.Ioc 0 ηLimits := ⟨hε₀.1, hsmall.2.2.2.2.2.2⟩
  obtain ⟨Glim, hGlim, Clim, hamplitude, _, hcenter, _⟩ := hlimits ε₀ hεLimits
  have hscaleZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) :=
    (hscale ε₀ hεScale).symm.tendsto_nhds inverseCubicScale_tendsto_zero
  have hshapeZero : Tendsto curve.shape (𝓝 0) (𝓝 2) := by
    have hproject : Continuous (fun x : ℝ × ℝ × ℝ ↦ x.2.1) := by fun_prop
    have hlimit := (hproject.tendsto ((0, 2, 1) : ℝ × ℝ × ℝ)).comp
      curve.toSlowGraph.path_tendsto
    simpa only [Function.comp_def, DFP.TwoLeg.SlowGraph.path_apply] using hlimit
  have hshape : Tendsto (fun j : ℕ ↦ (orbit.state j).p) atTop (𝓝 2) := by
    apply (hshapeZero.comp hscaleZero).congr'
    filter_upwards [] with j
    exact (congrArg Prod.fst (hgraph ε₀ hεGraph j).1).symm
  have hsquareZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε ^ 2) atTop (𝓝 0) := by
    simpa using hscaleZero.pow 2
  have hstepRemainderZero : Tendsto
      (fun j : ℕ ↦ ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude -
        2 * (orbit.state j).ε ^ 2) atTop (𝓝 0) :=
    (hstep ε₀ hεStep).isBigO.trans_tendsto hsquareZero
  have hquotientZero : Tendsto
      (fun j : ℕ ↦ ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude)
      atTop (𝓝 0) := by
    have hsum := hstepRemainderZero.add (hsquareZero.const_mul 2)
    simpa only [sub_add_cancel, mul_zero, zero_add] using hsum
  have hstepZero : Tendsto (fun j : ℕ ↦ ‖(orbit.state j).firstDisplacement‖)
      atTop (𝓝 0) := by
    have hnormalize (j : ℕ) :
        ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude *
          (orbit.state j).amplitude = ‖(orbit.state j).firstDisplacement‖ :=
      div_mul_cancel₀ _ (ne_of_gt (hvalid ε₀ hεValid j).amplitude_pos)
    have hproduct : Tendsto
        (fun j : ℕ ↦ ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude *
          (orbit.state j).amplitude) atTop (𝓝 (0 * Glim)) :=
      hquotientZero.mul hamplitude
    simpa only [hnormalize, zero_mul] using hproduct
  have hinitial : (orbit.state 0).lowVector = WithLp.toLp 2 ![(1 : ℝ), 0] := by
    rw [DFP.TwoPhaseOrbit.ofSlowCurve_zero, lowVector_eq_frameBasis,
      DFP.TwoPhaseOrbit.State.initial_frame]
    simp
  have hrepresentation (j : ℕ) : (orbit.state j).lowVector =
      EuclideanPlane.rotation (orbit.frameAngle j) (WithLp.toLp 2 ![(1 : ℝ), 0]) := by
    have hraw : (orbit.state j).lowVector =
        EuclideanPlane.rotation (orbit.frameAngle j) (orbit.state 0).lowVector :=
      hframe ε₀ hεFrame j
    rw [hinitial] at hraw
    exact hraw
  have hcircle := endpointCircleFromSourceFrame orbit orbit.frameAngle Clim Glim hGlim
    (fun j ↦ (hvalid ε₀ hεValid j).frame_specialOrthogonal) hscaleZero hshape
    hamplitude hcenter hstepZero hrepresentation (hcrossing ε₀ hεCrossing).2.2.2
  exact ⟨Glim, hGlim, Clim, hamplitude, hcenter, (hcrossing ε₀ hεCrossing).2.1, hcircle⟩

/-- Helper for cm-center-proposition: compensating the actual amplitude by
`1−(13/3)ε` cancels the leading quartic terms in the source scale and ratio recurrences. -/
theorem compensatedAmplitudeIdentity (a b x y : ℝ) (ha : a ≠ 0) :
    b * (1 - (13 / 3) * y) - a * (1 - (13 / 3) * x) =
      a * ((b / a - 1 + (13 / 2) * x ^ 4) * (1 - (13 / 3) * y) -
        (13 / 3) * (y - x + (3 / 2) * x ^ 4) + (169 / 6) * x ^ 4 * y) := by
  field_simp [ha]
  ring

/-- Helper for cm-center-proposition: uniform fifth-order source ratio and
scale residuals give a fifth-order increment bound for the compensated amplitude. -/
theorem compensatedAmplitudeIncrement (a b x y M KG Kε : ℝ)
    (ha : 0 < a) (haM : a ≤ M) (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hsmall : (13 / 3) * x ≤ 1 / 2) (hKG : 0 ≤ KG) (hKε : 0 ≤ Kε)
    (hratio : |b / a - 1 + (13 / 2) * x ^ 4| ≤ KG * x ^ 5)
    (hscale : |y - x + (3 / 2) * x ^ 4| ≤ Kε * x ^ 5) :
    |b * (1 - (13 / 3) * y) - a * (1 - (13 / 3) * x)| ≤
      (M * (KG + (13 / 3) * Kε + 169 / 6)) * x ^ 5 := by
  have hthirteen : (0 : ℝ) ≤ 13 / 3 := by norm_num
  have hleading : (0 : ℝ) ≤ 169 / 6 := by norm_num
  have hfactor : 0 ≤ 1 - (13 / 3) * y := by nlinarith
  have hfactorOne : 1 - (13 / 3) * y ≤ 1 := by nlinarith
  have hfourth : 0 ≤ x ^ 4 := pow_nonneg hx.le 4
  have hfifth : 0 ≤ x ^ 5 := pow_nonneg hx.le 5
  have hratioTerm :
      |(b / a - 1 + (13 / 2) * x ^ 4) * (1 - (13 / 3) * y)| ≤ KG * x ^ 5 := by
    rw [abs_mul, abs_of_nonneg hfactor]
    exact (mul_le_mul_of_nonneg_right hratio hfactor).trans
      (mul_le_of_le_one_right (mul_nonneg hKG hfifth) hfactorOne)
  have hscaleTerm : |(13 / 3 : ℝ) * (y - x + (3 / 2) * x ^ 4)| ≤
      (13 / 3) * Kε * x ^ 5 := by
    rw [abs_mul]
    norm_num
    calc
      (13 / 3 : ℝ) * |y - x + (3 / 2) * x ^ 4| ≤ (13 / 3) * (Kε * x ^ 5) :=
        mul_le_mul_of_nonneg_left hscale hthirteen
      _ = _ := by ring
  have hproductTerm : |(169 / 6 : ℝ) * x ^ 4 * y| ≤ (169 / 6) * x ^ 5 := by
    rw [abs_of_nonneg]
    · calc
        (169 / 6 : ℝ) * x ^ 4 * y ≤ (169 / 6) * x ^ 4 * x :=
          mul_le_mul_of_nonneg_left hyx (mul_nonneg hleading hfourth)
        _ = (169 / 6) * x ^ 5 := by ring
    · positivity
  rw [compensatedAmplitudeIdentity a b x y (ne_of_gt ha), abs_mul, abs_of_pos ha]
  have hinside :
      |(b / a - 1 + (13 / 2) * x ^ 4) * (1 - (13 / 3) * y) -
          (13 / 3) * (y - x + (3 / 2) * x ^ 4) + (169 / 6) * x ^ 4 * y| ≤
        (KG + (13 / 3) * Kε + 169 / 6) * x ^ 5 := by
    calc
      _ ≤ |(b / a - 1 + (13 / 2) * x ^ 4) * (1 - (13 / 3) * y) -
          (13 / 3) * (y - x + (3 / 2) * x ^ 4)| + |(169 / 6 : ℝ) * x ^ 4 * y| :=
        abs_add_le _ _
      _ ≤ (|(b / a - 1 + (13 / 2) * x ^ 4) * (1 - (13 / 3) * y)| +
          |(13 / 3 : ℝ) * (y - x + (3 / 2) * x ^ 4)|) +
          |(169 / 6 : ℝ) * x ^ 4 * y| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ (KG * x ^ 5 + (13 / 3) * Kε * x ^ 5) + (169 / 6) * x ^ 5 :=
        add_le_add (add_le_add hratioTerm hscaleTerm) hproductTerm
      _ = _ := by ring
  have hboundNonneg : 0 ≤ (KG + (13 / 3) * Kε + 169 / 6) * x ^ 5 := by positivity
  calc
    a * |(b / a - 1 + (13 / 2) * x ^ 4) * (1 - (13 / 3) * y) -
        (13 / 3) * (y - x + (3 / 2) * x ^ 4) + (169 / 6) * x ^ 4 * y| ≤
        a * ((KG + (13 / 3) * Kε + 169 / 6) * x ^ 5) :=
      mul_le_mul_of_nonneg_left hinside ha.le
    _ ≤ M * ((KG + (13 / 3) * Kε + 169 / 6) * x ^ 5) :=
      mul_le_mul_of_nonneg_right haM hboundNonneg
    _ = _ := by ring

/-- Helper for cm-center-proposition: summing the source compensated
increments gives the full quadratic amplitude remainder with coefficient `13/3`.
The hypotheses are scalar recurrence residuals and uniform bounds, not the desired tail estimate. -/
theorem amplitudeQuadraticTail (a ε : ℕ → ℝ) (A M KG Kε : ℝ)
    (ha : ∀ n, 0 < a n) (haM : ∀ n, a n ≤ M)
    (hε : ∀ n, 0 < ε n) (hsmall : ∀ n, (13 / 3) * ε n ≤ 1 / 2)
    (hdecrement : ∀ n, ε n ^ 4 ≤ ε n - ε (n + 1))
    (hKG : 0 ≤ KG) (hKε : 0 ≤ Kε)
    (hratio : ∀ n, |a (n + 1) / a n - 1 + (13 / 2) * ε n ^ 4| ≤ KG * ε n ^ 5)
    (hscale : ∀ n, |ε (n + 1) - ε n + (3 / 2) * ε n ^ 4| ≤ Kε * ε n ^ 5)
    (hlimit : Tendsto a atTop (𝓝 A)) (hεzero : Tendsto ε atTop (𝓝 0))
    (hAnonneg : 0 ≤ A) (hAM : A ≤ M) (j : ℕ) :
    |a j - A - (13 / 3) * A * ε j| ≤
      2 * (M * (KG + (13 / 3) * Kε + 169 / 6) + (169 / 9) * M) * ε j ^ 2 := by
  let b : ℕ → ℝ := fun n ↦ a n * (1 - (13 / 3) * ε n)
  let L : ℝ := M * (KG + (13 / 3) * Kε + 169 / 6)
  have hM : 0 ≤ M := (ha 0).le.trans (haM 0)
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hfourFive : 3 + 1 ≤ 5 := by norm_num
  have htail : ∀ n : ℕ, Summable (fun k : ℕ ↦ ε (n + k) ^ 5) ∧
      (∑' k : ℕ, ε (n + k) ^ 5) ≤ 1 * ε n ^ 2 := by
    intro n
    have hpositive : ∀ (_ : Unit) k, 0 < ε k := fun _ k ↦ hε k
    have hdecrease : ∀ (_ : Unit) k, (1 : ℝ) * ε k ^ (3 + 1) ≤ ε k - ε (k + 1) := by
      intro _ k
      simpa using hdecrement k
    have hraw := ParabolicRecurrence.summable_tail_pow_and_tsum_le_of_decrement
      (ε := fun _ : Unit ↦ ε) (p := 3) (q := 5) zero_lt_one hfourFive
      hpositive hdecrease () n
    simpa using hraw
  have hbound : ∀ n, ‖b (n + 1) - b n‖ ≤ L * ε n ^ 5 := by
    intro n
    have hyx : ε (n + 1) ≤ ε n := by
      have hnonneg : 0 ≤ ε n ^ 4 := pow_nonneg (hε n).le 4
      linarith [hdecrement n]
    simpa only [Real.norm_eq_abs, b, L] using
      compensatedAmplitudeIncrement (a n) (a (n + 1)) (ε n) (ε (n + 1)) M KG Kε
        (ha n) (haM n) (hε n) (hε (n + 1)).le hyx (hsmall n) hKG hKε
        (hratio n) (hscale n)
  have hsumPower : Summable (fun n ↦ ε n ^ 5) := by
    simpa using (htail 0).1
  have hsumNorm : Summable (fun n ↦ ‖b (n + 1) - b n‖) :=
    (hsumPower.mul_left L).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  have hbLimit : Tendsto b atTop (𝓝 A) := by
    have hconstant : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hfactor : Tendsto (fun n ↦ 1 - (13 / 3) * ε n) atTop (𝓝 1) := by
      simpa using hconstant.sub (hεzero.const_mul (13 / 3 : ℝ))
    simpa only [b, mul_one] using hlimit.mul hfactor
  have hbError : |b j - A| ≤ L * ε j ^ 2 := by
    simpa only [Real.norm_eq_abs, mul_one] using
      SequenceTail.norm_sub_limit_le hL hsumNorm hbLimit hbound htail j
  have hidentity : (1 - (13 / 3) * ε j) * (a j - A - (13 / 3) * A * ε j) =
      b j - A + (169 / 9) * A * ε j ^ 2 := by
    dsimp only [b]
    ring
  have hfactorHalf : 1 / 2 ≤ 1 - (13 / 3) * ε j := by linarith [hsmall j]
  have hfactorNonneg : 0 ≤ 1 - (13 / 3) * ε j := by linarith
  have hcorrection : |(169 / 9 : ℝ) * A * ε j ^ 2| ≤ (169 / 9) * M * ε j ^ 2 := by
    rw [abs_of_nonneg]
    · have hcoefficient : (0 : ℝ) ≤ 169 / 9 := by norm_num
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAM hcoefficient) (sq_nonneg _)
    · positivity
  have hproductBound : (1 - (13 / 3) * ε j) * |a j - A - (13 / 3) * A * ε j| ≤
      (L + (169 / 9) * M) * ε j ^ 2 := by
    calc
      _ = |(1 - (13 / 3) * ε j) * (a j - A - (13 / 3) * A * ε j)| := by
        rw [abs_mul, abs_of_nonneg hfactorNonneg]
      _ = |b j - A + (169 / 9) * A * ε j ^ 2| := congrArg abs hidentity
      _ ≤ |b j - A| + |(169 / 9 : ℝ) * A * ε j ^ 2| := abs_add_le _ _
      _ ≤ L * ε j ^ 2 + (169 / 9) * M * ε j ^ 2 := add_le_add hbError hcorrection
      _ = _ := by ring
  have hhalf : (1 / 2) * |a j - A - (13 / 3) * A * ε j| ≤
      (1 - (13 / 3) * ε j) * |a j - A - (13 / 3) * A * ε j| :=
    mul_le_mul_of_nonneg_right hfactorHalf (abs_nonneg _)
  dsimp only [L] at hproductBound
  linarith

/-- Helper for cm-center-proposition: the ORIGINAL two-step map has a C⁷
invariant tangent graph, constructed by uniform C⁸ ZERO-START graph-transform
iterates and Arzelà–Ascoli. No earlier fixed-section regularity theorem is used. -/
theorem existsInvariantCenterGraph :
    ∃ p h : ℝ → ℝ,
      ContDiffAt ℝ 7 (fun ε ↦ (p ε, h ε)) 0 ∧ (p 0, h 0) = (2, 1) ∧
      HasFDerivAt (fun ε ↦ (p ε, h ε)) (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 ∧
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let nextScale := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (nextScale, p nextScale, h nextScale)) := by
  obtain ⟨d, hν, _, _, _, _, _, hR, hgerm, hbunching⟩ := sourceCutoffData
  have hνEight : 8 ≤ d.nu := by rw [hν]
  have honeTwo : 1 ≤ 2 := by norm_num
  have htop : ∀ r : ℕ, 2 ≤ r → r ≤ 8 →
      ((d.linearRate : ℝ) + (d.epsilon : ℝ) * (1 + (d.slope : ℝ))) *
        (d.lower : ℝ)⁻¹ ^ r < 1 := by
    intro r hrTwo hrEight
    exact hbunching r (honeTwo.trans hrTwo) hrEight
  let ζ := LocalInvariantGraph.GraphIterateBounds.graphLimit d
  have hfixed : d.transform ζ = ζ :=
    LocalInvariantGraph.GraphIterateBounds.graphLimit_fixed d
  have hsmooth : ContDiffAt ℝ 7 (ζ : ℝ → ℝ × ℝ) 0 :=
    (LocalInvariantGraph.GraphIterateBounds.graphLimit_contDiff_seven d hνEight htop).contDiffAt
  exact invariantGraphOfSmoothFixedGraph d hR hgerm ζ hfixed hsmooth

/-- cm-center-proposition. The source two-step map has eigenvalues `1,−1/9,0`
and a locally invariant C⁷ graph with coefficients `198/5`, `8`, and `−3/2`.
For EVERY sufficiently small positive initial scale, the LITERAL source data
`x₀=g₀=(1,p(ε₀)ε₀²)` and `H₀=diag(h(ε₀)p(ε₀)ε₀⁴,h(ε₀))` generate the infinite
exact alternating secant recurrence. Both physical matrices in every cycle are
positive definite, the spectral coordinates remain on the graph, and
`εⱼ ∼ ((9/2)j)^(−1/3)`.

`State.ExactCycle` records the actual displacement, gradient and inverse DFP
updates in the current eigenbasis; `State.metric_def` and `gradient_def` encode
`rⱼ=εⱼ²`. The graph is obtained from the SOURCE highest-derivative estimates
and Arzelà–Ascoli, independently of the polar counterexample construction. -/
theorem centerProposition :
    Module.End.HasEigenvalue
        (fderiv ℝ DFP.TwoLeg.stateMap (0, 2, 1)).toLinearMap (1 : ℝ) ∧
      Module.End.HasEigenvalue
        (fderiv ℝ DFP.TwoLeg.stateMap (0, 2, 1)).toLinearMap (-(1 : ℝ) / 9) ∧
      Module.End.HasEigenvalue
        (fderiv ℝ DFP.TwoLeg.stateMap (0, 2, 1)).toLinearMap (0 : ℝ) ∧
      ∃ p h : ℝ → ℝ,
        ContDiffAt ℝ 7 (fun ε ↦ (p ε, h ε)) 0 ∧ (p 0, h 0) = (2, 1) ∧
        HasFDerivAt (fun ε ↦ (p ε, h ε)) (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 ∧
        (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
          (fun ε ↦
            let nextScale := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
            (nextScale, p nextScale, h nextScale)) ∧
        (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 4) ∧
        (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 4) ∧
        (fun ε : ℝ ↦ (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1 -
          (ε - (3 / 2) * ε ^ 4)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) ∧
        ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          ((orbit.state 0).point = WithLp.toLp 2 ![(1 : ℝ), p ε₀ * ε₀ ^ 2] ∧
            (orbit.state 0).gradient = WithLp.toLp 2 ![(1 : ℝ), p ε₀ * ε₀ ^ 2] ∧
            (orbit.state 0).metric = Matrix.diagonal ![h ε₀ * p ε₀ * ε₀ ^ 4, h ε₀]) ∧
          (∀ j : ℕ, (orbit.state j).ExactCycle) ∧
          (∀ j : ℕ, (orbit.state j).metric.PosDef ∧
            (orbit.state j).middleMetric.PosDef ∧ (orbit.state j).next.metric.PosDef) ∧
          (∀ j : ℕ, ((orbit.state j).p, (orbit.state j).h) =
            (p (orbit.state j).ε, h (orbit.state j).ε) ∧ 0 < (orbit.state j).ε) ∧
          (fun j : ℕ ↦ (orbit.state j).ε) ~[atTop]
            (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) := by
  refine ⟨DFP.TwoLeg.stateMap_centerEigenvalue,
    DFP.TwoLeg.stateMap_transverseEigenvalue_negNinth,
    DFP.TwoLeg.stateMap_transverseEigenvalue_zero, ?_⟩
  obtain ⟨p, h, hsmooth, hbase, htangent, hinvariant⟩ := existsInvariantCenterGraph
  obtain ⟨hpJet, hhJet, _⟩ := invariantGraphTaylorJets p h hsmooth hbase htangent hinvariant
  obtain ⟨hpSource, hhSource, hscaleSource⟩ :=
    invariantGraphSourceExpansions p h hsmooth hbase htangent hinvariant
  have heighth : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by norm_num
  obtain ⟨ηValid, hηValid, hexact⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurveExact p h hinvariant hpJet hhJet (1 / 8) heighth
  obtain ⟨ηGraph, hηGraph, hgraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h hinvariant hpJet hhJet
  obtain ⟨ηScale, hηScale, hscale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h hinvariant hpJet hhJet
  let εbar := min ηValid (min ηGraph ηScale)
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · exact lt_min hηValid.1 (lt_min hηGraph.1 hηScale)
    · exact ((min_le_left _ _).trans hηValid.2).trans_lt heighth.2
  refine ⟨p, h, hsmooth, hbase, htangent, hinvariant,
    hpSource, hhSource, hscaleSource, εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεScale : ε₀ ∈ Set.Ioc 0 ηScale :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hinitial :
      (orbit.state 0).point = WithLp.toLp 2 ![(1 : ℝ), p ε₀ * ε₀ ^ 2] ∧
      (orbit.state 0).gradient = WithLp.toLp 2 ![(1 : ℝ), p ε₀ * ε₀ ^ 2] ∧
      (orbit.state 0).metric = Matrix.diagonal ![h ε₀ * p ε₀ * ε₀ ^ 4, h ε₀] := by
    simpa only [orbit, DFP.TwoPhaseOrbit.ofSlowCurve_zero] using prescribedInitialization p h ε₀
  have hcycles (j : ℕ) : (orbit.state j).ExactCycle := hexact ε₀ hεValid j
  have hmatrices (j : ℕ) : (orbit.state j).metric.PosDef ∧
      (orbit.state j).middleMetric.PosDef ∧ (orbit.state j).next.metric.PosDef :=
    physicalMatrices_posDef (orbit.state j) (hcycles j).valid
  have hcoordinates (j : ℕ) : ((orbit.state j).p, (orbit.state j).h) =
      (p (orbit.state j).ε, h (orbit.state j).ε) ∧ 0 < (orbit.state j).ε := by
    have hraw := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    rw [DFP.TwoPhaseOrbit.State.coordinates_def] at hraw
    have hshape := (hgraph ε₀ hεGraph j).1
    rw [← hraw] at hshape
    exact ⟨congrArg Prod.snd hshape, (hcycles j).valid.ε_pos⟩
  have hscaleActual : (fun j : ℕ ↦ (orbit.state j).ε) ~[atTop]
      (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) := by
    simpa only [orbit, orbitScale_eq_iterate] using hscale ε₀ hεScale
  exact ⟨hinitial, hcycles, hmatrices, hcoordinates, hscaleActual⟩

/-- Helper for cm-center-proposition: the actual physical scale successor
is the first coordinate of the original stateMap at the current spectral state. -/
theorem orbitScale_succ_eq_stateMap (p h : ℝ → ℝ) (ε₀ : ℝ) (j : ℕ) :
    ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state (j + 1)).ε =
      (DFP.TwoLeg.stateMap
        (((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).ε,
          ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).p,
          ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).h)).1 := by
  rw [DFP.TwoPhaseOrbit.ofSlowCurve_succ]
  have hraw := congrArg Prod.fst (DFP.TwoPhaseOrbit.State.next_coordinates
    ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j))
  simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using hraw

/-- Helper for cm-center-proposition: the actual source amplitudes have the
FULL uniform quadratic remainder `Gⱼ−G∞−(13/3)G∞εⱼ = O(εⱼ²)` in
cm-limiting-scales. Constants are selected before every small initial scale. -/
theorem slowCurveAmplitudeQuadraticTail (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∃ Glim > 0,
          Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
          ∀ j : ℕ, |(orbit.state j).amplitude - Glim -
            (13 / 3) * Glim * (orbit.state j).ε| ≤ K * (orbit.state j).ε ^ 2 := by
  have hfiveSix : 5 < 6 := by norm_num
  have hsixFive : (fun ε : ℝ ↦ ε ^ 6) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) :=
    (Asymptotics.isLittleO_pow_pow hfiveSix).isBigO
  have hscaleSix :
      (fun ε : ℝ ↦ (DFP.TwoLeg.stateMap (ε, curve.shape ε, curve.high ε)).1 -
        (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 6) := by
    simpa only [DFP.TwoLeg.stateMap_fst] using
      DFP.TwoLeg.slowGraphSignedRecurrence curve.shape curve.high
        curve.shapeRemainder curve.highRemainder
  have hcorrection : (fun ε : ℝ ↦ (5 / 4) * ε ^ 5) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) :=
    (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).const_mul_left (5 / 4)
  have hscaleFive :
      (fun ε : ℝ ↦ (DFP.TwoLeg.stateMap (ε, curve.shape ε, curve.high ε)).1 - ε +
        (3 / 2) * ε ^ 4) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    apply ((hscaleSix.trans hsixFive).add hcorrection).congr'
    · filter_upwards [] with ε
      ring
    · rfl
  have hratioFive :
      (fun ε : ℝ ↦ (DFP.TwoLeg.observableMap (ε, curve.shape ε, curve.high ε)).amplitudeRatio -
        1 + (13 / 2) * ε ^ 4) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    apply ((slowCurveAmplitudeExpansion curve).trans hsixFive).congr'
    · filter_upwards [] with ε
      ring
    · rfl
  obtain ⟨Cε, hCε, δε, hδε, hscaleLocal⟩ :=
    Asymptotics.IsUniformRemainderOn.exists_pos_natPow_bound_of_isBigO hscaleFive
  obtain ⟨CG, hCG, δG, hδG, hratioLocal⟩ :=
    Asymptotics.IsUniformRemainderOn.exists_pos_natPow_bound_of_isBigO hratioFive
  obtain ⟨ηGraph, hηGraph, hgraph⟩ := slowCurveStateOnGraph curve
  obtain ⟨ηScale, hηScale, hscale⟩ := slowCurveScaleAsymptotic curve
  obtain ⟨ηAmplitude, hηAmplitude, Gmin, hGmin, M, hGminM, hamplitude⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeUniformBounds curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  let εbar := min ηAmplitude (min ηGraph (min ηScale
    (min (δε / 2) (min (δG / 2) (min (3 / 26) (1 / (2 * (Cε + 1))))))))
  have hden : 0 < 2 * (Cε + 1) := by positivity
  have hcap : (0 : ℝ) < 3 / 26 := by norm_num
  have hεbarPos : 0 < εbar := by
    exact lt_min hηAmplitude.1 (lt_min hηGraph.1 (lt_min hηScale
      (lt_min (half_pos hδε) (lt_min (half_pos hδG) (lt_min hcap (one_div_pos.mpr hden))))))
  have hεbarLt : εbar < 1 / 4 := (min_le_left _ _).trans_lt hηAmplitude.2
  let K : ℝ := 2 * (M * (CG + (13 / 3) * Cε + 169 / 6) + (169 / 9) * M)
  have hM : 0 < M := hGmin.trans_le hGminM
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, K, hK, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  let a : ℕ → ℝ := fun j ↦ (orbit.state j).amplitude
  let ε : ℕ → ℝ := fun j ↦ (orbit.state j).ε
  have hsmall : ε₀ ≤ ηAmplitude ∧ ε₀ ≤ ηGraph ∧ ε₀ ≤ ηScale ∧ ε₀ ≤ δε / 2 ∧
      ε₀ ≤ δG / 2 ∧ ε₀ ≤ 3 / 26 ∧ ε₀ ≤ 1 / (2 * (Cε + 1)) := by
    simpa only [εbar, le_min_iff] using hε₀.2
  have hεAmplitude : ε₀ ∈ Set.Ioc 0 ηAmplitude := ⟨hε₀.1, hsmall.1⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph := ⟨hε₀.1, hsmall.2.1⟩
  have hεScale : ε₀ ∈ Set.Ioc 0 ηScale := ⟨hε₀.1, hsmall.2.2.1⟩
  obtain ⟨Glim, hGlimRange, hlimit, hbounds⟩ := hamplitude ε₀ hεAmplitude
  have hGlim : 0 < Glim := hGmin.trans_le hGlimRange.1
  have ha (j : ℕ) : 0 < a j := hGmin.trans_le (hbounds j).1
  have haM (j : ℕ) : a j ≤ M := (hbounds j).2
  have hεPositive (j : ℕ) : 0 < ε j := (hgraph ε₀ hεGraph j).2.1
  have hεBound (j : ℕ) : ε j ≤ ε₀ := (hgraph ε₀ hεGraph j).2.2
  have hεZero : Tendsto ε atTop (𝓝 0) :=
    (hscale ε₀ hεScale).symm.tendsto_nhds inverseCubicScale_tendsto_zero
  have hcoordinates (j : ℕ) : (orbit.state j).coordinates =
      (ε j, curve.shape (ε j), curve.high (ε j)) := by
    rw [DFP.TwoPhaseOrbit.State.coordinates_def]
    exact congrArg (fun z : ℝ × ℝ ↦ (ε j, z)) (hgraph ε₀ hεGraph j).1
  have hnextScale (j : ℕ) : ε (j + 1) =
      (DFP.TwoLeg.stateMap (ε j, curve.shape (ε j), curve.high (ε j))).1 := by
    have hraw : ε (j + 1) =
        (DFP.TwoLeg.stateMap ((orbit.state j).ε, (orbit.state j).p, (orbit.state j).h)).1 :=
      orbitScale_succ_eq_stateMap curve.shape curve.high ε₀ j
    rw [← DFP.TwoPhaseOrbit.State.coordinates_def, hcoordinates] at hraw
    exact hraw
  have hnextAmplitude (j : ℕ) : a (j + 1) / a j =
      (DFP.TwoLeg.observableMap (ε j, curve.shape (ε j), curve.high (ε j))).amplitudeRatio := by
    have hsuccessor : orbit.state (j + 1) = (orbit.state j).next :=
      DFP.TwoPhaseOrbit.ofSlowCurve_succ curve.shape curve.high ε₀ j
    dsimp only [a]
    rw [hsuccessor, DFP.TwoPhaseOrbit.State.nextAmplitudeRatio _ (ne_of_gt (ha j)), hcoordinates]
  have hscaleBound (j : ℕ) :
      |ε (j + 1) - ε j + (3 / 2) * ε j ^ 4| ≤ Cε * ε j ^ 5 := by
    have hdist : |ε j| < δε := by
      rw [abs_of_pos (hεPositive j)]
      exact ((hεBound j).trans hsmall.2.2.2.1).trans_lt (half_lt_self hδε)
    have hraw := hscaleLocal (ε j) hdist
    rw [← hnextScale j] at hraw
    simpa only [Real.norm_eq_abs, abs_of_pos (hεPositive j)] using hraw
  have hratioBound (j : ℕ) :
      |a (j + 1) / a j - 1 + (13 / 2) * ε j ^ 4| ≤ CG * ε j ^ 5 := by
    have hdist : |ε j| < δG := by
      rw [abs_of_pos (hεPositive j)]
      exact ((hεBound j).trans hsmall.2.2.2.2.1).trans_lt (half_lt_self hδG)
    have hraw := hratioLocal (ε j) hdist
    rw [← hnextAmplitude j] at hraw
    simpa only [Real.norm_eq_abs, abs_of_pos (hεPositive j)] using hraw
  have hsmallAmplitude (j : ℕ) : (13 / 3) * ε j ≤ 1 / 2 := by
    have hbound := (hεBound j).trans hsmall.2.2.2.2.2.1
    linarith
  have hdecrement (j : ℕ) : ε j ^ 4 ≤ ε j - ε (j + 1) := by
    have hcapj := (hεBound j).trans hsmall.2.2.2.2.2.2
    have hmul : ε j * (2 * (Cε + 1)) ≤ 1 := (le_div_iff₀ hden).mp hcapj
    have hlocalSmall : Cε * ε j ≤ 1 / 2 := by nlinarith [hεPositive j]
    have hresidual : Cε * ε j ^ 5 ≤ (1 / 2) * ε j ^ 4 := by
      calc
        Cε * ε j ^ 5 = (Cε * ε j) * ε j ^ 4 := by ring
        _ ≤ (1 / 2) * ε j ^ 4 :=
          mul_le_mul_of_nonneg_right hlocalSmall (pow_nonneg (hεPositive j).le 4)
    have hbound := (abs_le.mp (hscaleBound j)).2
    linarith
  refine ⟨Glim, hGlim, hlimit, ?_⟩
  intro j
  exact amplitudeQuadraticTail a ε Glim M CG Cε ha haM hεPositive hsmallAmplitude hdecrement
    hCG.le hCε.le hratioBound hscaleBound hlimit hεZero hGlim.le hGlimRange.2 j

/-- Helper for cm-center-proposition: the exact source spectral representation
forces the boundary gradient norm to have the SAME positive limit as its amplitude. -/
theorem boundaryGradientNormLimit (orbit : DFP.TwoPhaseOrbit) (G : ℝ) (hG : 0 < G)
    (hframe : ∀ j, (orbit.state j).frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (hscale : Tendsto (fun j ↦ (orbit.state j).ε) atTop (𝓝 0))
    (hshape : Tendsto (fun j ↦ (orbit.state j).p) atTop (𝓝 2))
    (hamplitude : Tendsto (fun j ↦ (orbit.state j).amplitude) atTop (𝓝 G)) :
    Tendsto (fun j ↦ ‖(orbit.state j).gradient‖) atTop (𝓝 G) := by
  have hhighZero : Tendsto
      (fun j ↦ |(orbit.state j).amplitude| * |(orbit.state j).p * (orbit.state j).ε ^ 2|)
      atTop (𝓝 0) := by
    have hraw := (hamplitude.mul (hshape.mul (hscale.pow 2))).abs
    simpa only [zero_pow (Nat.succ_ne_zero 1), mul_zero, abs_zero, abs_mul] using hraw
  have hbound (j : ℕ) :
      |‖(orbit.state j).gradient‖ - (|(orbit.state j).amplitude|)| ≤
        |(orbit.state j).amplitude| * |(orbit.state j).p * (orbit.state j).ε ^ 2| := by
    have hnorm : ‖(orbit.state j).amplitude • (orbit.state j).lowVector‖ =
        |(orbit.state j).amplitude| := by
      rw [norm_smul, Real.norm_eq_abs, lowVector_norm _ (hframe j), mul_one]
    calc
      |‖(orbit.state j).gradient‖ - (|(orbit.state j).amplitude|)| =
          |‖(orbit.state j).gradient‖ - ‖(orbit.state j).amplitude • (orbit.state j).lowVector‖| :=
        congrArg (fun z : ℝ ↦ |‖(orbit.state j).gradient‖ - z|) hnorm.symm
      _ ≤ ‖(orbit.state j).gradient - (orbit.state j).amplitude • (orbit.state j).lowVector‖ :=
        abs_norm_sub_norm_le _ _
      _ = _ := gradientLowVector_error _ (hframe j)
  have herrorZero : Tendsto
      (fun j ↦ ‖(orbit.state j).gradient‖ - |(orbit.state j).amplitude|) atTop (𝓝 0) := by
    apply squeeze_zero_norm
    · intro j
      simpa only [Real.norm_eq_abs] using hbound j
    · exact hhighZero
  have hsum := herrorZero.add hamplitude.abs
  simpa only [sub_add_cancel, zero_add, abs_of_pos hG] using hsum

/-- Helper for cm-center-proposition: actual prescribed gradient norms along
BOTH phases converge to the same positive source amplitude limit. -/
theorem slowCurveFullGradientLimit (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ G > 0, Tendsto (fun j ↦ (orbit.state j).amplitude) atTop (𝓝 G) →
        Tendsto (fun k ↦ ‖orbit.endpointGradient k‖) atTop (𝓝 G) := by
  obtain ⟨ηGradient, hηGradient, hgradient⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointGradientNormTendsto curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηGraph, hηGraph, hgraph⟩ := slowCurveStateOnGraph curve
  obtain ⟨ηScale, hηScale, hscale⟩ := slowCurveScaleAsymptotic curve
  have heighth : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by norm_num
  obtain ⟨ηValid, hηValid, hvalid⟩ := DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity
    curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
    (1 / 8) heighth
  let εbar := min ηGradient (min ηGraph (min ηScale ηValid))
  have hεbarPos : 0 < εbar :=
    lt_min hηGradient (lt_min hηGraph.1 (lt_min hηScale hηValid.1))
  have hεbarLt : εbar < 1 / 4 :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt hηGraph.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hsmall : ε₀ ≤ ηGradient ∧ ε₀ ≤ ηGraph ∧ ε₀ ≤ ηScale ∧ ε₀ ≤ ηValid := by
    simpa only [εbar, le_min_iff] using hε₀.2
  have hεGradient : ε₀ ∈ Set.Ioc 0 ηGradient := ⟨hε₀.1, hsmall.1⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph := ⟨hε₀.1, hsmall.2.1⟩
  have hεScale : ε₀ ∈ Set.Ioc 0 ηScale := ⟨hε₀.1, hsmall.2.2.1⟩
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid := ⟨hε₀.1, hsmall.2.2.2⟩
  intro G hG hamplitude
  have hscaleZero : Tendsto (fun j ↦ (orbit.state j).ε) atTop (𝓝 0) :=
    (hscale ε₀ hεScale).symm.tendsto_nhds inverseCubicScale_tendsto_zero
  have hshapeZero : Tendsto curve.shape (𝓝 0) (𝓝 2) := by
    have hproject : Continuous (fun x : ℝ × ℝ × ℝ ↦ x.2.1) := by fun_prop
    have hlimit := (hproject.tendsto ((0, 2, 1) : ℝ × ℝ × ℝ)).comp
      curve.toSlowGraph.path_tendsto
    simpa only [Function.comp_def, DFP.TwoLeg.SlowGraph.path_apply] using hlimit
  have hshape : Tendsto (fun j ↦ (orbit.state j).p) atTop (𝓝 2) := by
    apply (hshapeZero.comp hscaleZero).congr'
    filter_upwards [] with j
    exact (congrArg Prod.fst (hgraph ε₀ hεGraph j).1).symm
  have hboundary := boundaryGradientNormLimit orbit G hG
    (fun j ↦ (hvalid ε₀ hεValid j).frame_specialOrthogonal) hscaleZero hshape hamplitude
  obtain ⟨G', _, hfull⟩ := hgradient ε₀ hεGradient
  have hevenMono : StrictMono (fun j : ℕ ↦ 2 * j) := by
    intro i j hij
    exact Nat.mul_lt_mul_of_pos_left hij Nat.two_pos
  have hfullEven : Tendsto (fun j ↦ ‖(orbit.state j).gradient‖) atTop (𝓝 G') := by
    simpa only [Function.comp_def, DFP.TwoPhaseOrbit.endpointGradient_even, orbit] using
      hfull.comp hevenMono.tendsto_atTop
  have hlimitEq : G' = G := tendsto_nhds_unique hfullEven hboundary
  rwa [hlimitEq] at hfull

/-- Helper for cm-center-proposition: a source SlowCurve with C⁷ regularity,
the prescribed base, and zero tangent exists by the ACTUAL source graph transform. -/
theorem existsSourceSlowCurve :
    ∃ curve : DFP.TwoLeg.SlowCurve,
      ContDiffAt ℝ 7 (fun ε ↦ (curve.shape ε, curve.high ε)) 0 ∧
      (curve.shape 0, curve.high 0) = (2, 1) ∧
      HasFDerivAt (fun ε ↦ (curve.shape ε, curve.high ε))
        (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 := by
  obtain ⟨p, h, hsmooth, hbase, htangent, hinvariant⟩ := existsInvariantCenterGraph
  obtain ⟨curve, hshape, hhigh⟩ :=
    invariantGraphSlowCurve p h hsmooth hbase htangent hinvariant
  refine ⟨curve, ?_, ?_, ?_⟩
  · simpa only [hshape, hhigh] using hsmooth
  · simpa only [hshape, hhigh] using hbase
  · simpa only [hshape, hhigh] using htangent

/-- Helper for cm-center-proposition: the ACTUAL Section 6 recurrence has
positive limiting gradient norm, the FULL `13/3` quadratic amplitude expansion,
uniform cubic center tails, unbounded source frame rotation, and the EXACT
limiting circle for both endpoint phases. The same C⁷ source graph is fixed
before the common threshold and every later initial scale. -/
theorem centerManifoldAsymptotics :
    ∃ curve : DFP.TwoLeg.SlowCurve,
      ContDiffAt ℝ 7 (fun ε ↦ (curve.shape ε, curve.high ε)) 0 ∧
      (curve.shape 0, curve.high 0) = (2, 1) ∧
      ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ CG > 0, ∃ CC > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εbar,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
          ∃ Glim > 0, ∃ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
            Tendsto (fun k : ℕ ↦ ‖orbit.endpointGradient k‖) atTop (𝓝 Glim) ∧
            Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) ∧
            (∀ j : ℕ, |(orbit.state j).amplitude - Glim -
                (13 / 3) * Glim * (orbit.state j).ε| ≤ CG * (orbit.state j).ε ^ 2) ∧
            (∀ j : ℕ, ‖(orbit.state j).center - Clim‖ +
                ‖(orbit.state j).middleCenter - Clim‖ ≤ CC * (orbit.state j).ε ^ 3) ∧
            Tendsto orbit.frameAngle atTop atBot ∧
            {z : EuclideanSpace ℝ (Fin 2) | MapClusterPt z atTop orbit.endpoint} =
              DFP.TwoPhaseOrbit.limitCircle Clim Glim := by
  obtain ⟨curve, hsmooth, hbase, _⟩ := existsSourceSlowCurve
  obtain ⟨ηCircle, hηCircle, hcircle⟩ := slowCurveCircleGeometry curve
  obtain ⟨ηQuadratic, hηQuadratic, CG, hCG, hquadratic⟩ := slowCurveAmplitudeQuadraticTail curve
  obtain ⟨ηCenter, hηCenter, CC, hCC, hcenterTail⟩ :=
    DFP.TwoPhaseOrbit.slowCurveCenterTailUniformBound curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηGradient, hηGradient, hgradient⟩ := slowCurveFullGradientLimit curve
  let εbar := min ηCircle (min ηQuadratic (min ηCenter ηGradient))
  have hεbarPos : 0 < εbar :=
    lt_min hηCircle.1 (lt_min hηQuadratic.1 (lt_min hηCenter.1 hηGradient.1))
  have hεbarLt : εbar < 1 / 4 := (min_le_left _ _).trans_lt hηCircle.2
  refine ⟨curve, hsmooth, hbase, εbar, ⟨hεbarPos, hεbarLt⟩, CG, hCG, CC, hCC, ?_⟩
  intro ε₀ hε₀
  dsimp only
  have hsmall : ε₀ ≤ ηCircle ∧ ε₀ ≤ ηQuadratic ∧ ε₀ ≤ ηCenter ∧ ε₀ ≤ ηGradient := by
    simpa only [εbar, le_min_iff] using hε₀.2
  have hεCircle : ε₀ ∈ Set.Ioc 0 ηCircle := ⟨hε₀.1, hsmall.1⟩
  have hεQuadratic : ε₀ ∈ Set.Ioc 0 ηQuadratic := ⟨hε₀.1, hsmall.2.1⟩
  have hεCenter : ε₀ ∈ Set.Ioc 0 ηCenter := ⟨hε₀.1, hsmall.2.2.1⟩
  have hεGradient : ε₀ ∈ Set.Ioc 0 ηGradient := ⟨hε₀.1, hsmall.2.2.2⟩
  obtain ⟨Glim, hGlim, Clim, hamplitude, hcenter, hrotation, hcluster⟩ := hcircle ε₀ hεCircle
  obtain ⟨G', _, hlimit', htail⟩ := hquadratic ε₀ hεQuadratic
  have hlimitEq : G' = Glim := tendsto_nhds_unique hlimit' hamplitude
  rw [hlimitEq] at htail
  exact ⟨Glim, hGlim, Clim, hamplitude, hgradient ε₀ hεGradient Glim hGlim hamplitude,
    hcenter, htail, hcenterTail ε₀ hεCenter Clim hcenter, hrotation, hcluster⟩

/-- Helper for cm-center-proposition: actual hatted points have radial excess
comparable to the source cycle scale, and their prescribed gradient corrections
are uniformly cubic. All constants precede the initial scale. No support-radius
cap or separation is assumed here; the manuscript's eventual radius and disjointness
assumptions can therefore be supplied separately to the interpolation bridge. -/
theorem slowCurveRadialCoefficientBounds (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cR > 0, ∃ CR > 0, ∃ Ca > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∃ Glim > 0, ∃ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
          Tendsto (fun j ↦ (orbit.state j).center) atTop (𝓝 Clim) ∧
          Tendsto (fun k ↦ (orbit.state (k / 2)).ε) atTop (𝓝 0) ∧
          {z : EuclideanSpace ℝ (Fin 2) | MapClusterPt z atTop orbit.endpoint} =
            DFP.TwoPhaseOrbit.limitCircle Clim Glim ∧
          ∀ k : ℕ, 0 < (orbit.state (k / 2)).ε ∧
            cR * (orbit.state (k / 2)).ε ≤ ‖orbit.endpoint k - Clim‖ - Glim ∧
            ‖orbit.endpoint k - Clim‖ - Glim ≤ CR * (orbit.state (k / 2)).ε ∧
            ‖orbit.endpointCorrection Clim k‖ ≤ Ca * (orbit.state (k / 2)).ε ^ 3 := by
  obtain ⟨ηCircle, hηCircle, hcircle⟩ := slowCurveCircleGeometry curve
  obtain ⟨ηQuadratic, hηQuadratic, K, hK, hquadratic⟩ := slowCurveAmplitudeQuadraticTail curve
  obtain ⟨ηGraph, hηGraph, hgraph⟩ := slowCurveStateOnGraph curve
  obtain ⟨ηScale, hηScale, hscale⟩ := slowCurveScaleAsymptotic curve
  obtain ⟨ηAmplitude, hηAmplitude, Gmin, hGmin, M, hGminM, hamplitude⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeUniformBounds curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηRadius, hηRadius, ω, hω, hradius⟩ :=
    DFP.TwoPhaseOrbit.slowCurvePhaseRadiusErrorUniform curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηCorrection, hηCorrection, Ca, hCa, hcorrection⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointCorrectionUniformBound curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  let ηBase := ηRadius / 2
  have hηBase : ηBase ∈ Set.Ioc 0 ηRadius :=
    ⟨half_pos hηRadius.1, half_le_self hηRadius.1.le⟩
  have hωBase : 0 ≤ ω ηBase := hω.1 ηBase hηBase
  let E := K + ω ηBase
  let cR := (13 / 6) * Gmin
  let CR := (13 / 3) * M + E
  have hE : 0 < E := add_pos_of_pos_of_nonneg hK hωBase
  have hcR : 0 < cR := by
    dsimp only [cR]
    positivity
  have hM : 0 < M := hGmin.trans_le hGminM
  have hCR : 0 < CR := by
    dsimp only [CR]
    positivity
  let εbar := min ηCircle (min ηQuadratic (min ηGraph (min ηScale
    (min ηAmplitude (min ηBase (min ηCorrection (min 1 (cR / (E + 1)))))))))
  have hden : 0 < E + 1 := by positivity
  have hεbarPos : 0 < εbar :=
    lt_min hηCircle.1 (lt_min hηQuadratic.1 (lt_min hηGraph.1 (lt_min hηScale
      (lt_min hηAmplitude.1 (lt_min hηBase.1 (lt_min hηCorrection.1
        (lt_min zero_lt_one (div_pos hcR hden))))))))
  have hεbarLt : εbar < 1 / 4 := (min_le_left _ _).trans_lt hηCircle.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, cR, hcR, CR, hCR, Ca, hCa, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hsmall : ε₀ ≤ ηCircle ∧ ε₀ ≤ ηQuadratic ∧ ε₀ ≤ ηGraph ∧ ε₀ ≤ ηScale ∧
      ε₀ ≤ ηAmplitude ∧ ε₀ ≤ ηBase ∧ ε₀ ≤ ηCorrection ∧ ε₀ ≤ 1 ∧ ε₀ ≤ cR / (E + 1) := by
    simpa only [εbar, le_min_iff] using hε₀.2
  have hεCircle : ε₀ ∈ Set.Ioc 0 ηCircle := ⟨hε₀.1, hsmall.1⟩
  have hεQuadratic : ε₀ ∈ Set.Ioc 0 ηQuadratic := ⟨hε₀.1, hsmall.2.1⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph := ⟨hε₀.1, hsmall.2.2.1⟩
  have hεScale : ε₀ ∈ Set.Ioc 0 ηScale := ⟨hε₀.1, hsmall.2.2.2.1⟩
  have hεAmplitude : ε₀ ∈ Set.Ioc 0 ηAmplitude := ⟨hε₀.1, hsmall.2.2.2.2.1⟩
  have hεBase : ε₀ ∈ Set.Ioc 0 ηBase := ⟨hε₀.1, hsmall.2.2.2.2.2.1⟩
  have hεCorrection : ε₀ ∈ Set.Ioc 0 ηCorrection := ⟨hε₀.1, hsmall.2.2.2.2.2.2.1⟩
  obtain ⟨Glim, hGlim, Clim, hAmp, hCenter, _, hCluster⟩ := hcircle ε₀ hεCircle
  obtain ⟨G', hGRange, hGLimit, _⟩ := hamplitude ε₀ hεAmplitude
  have hGident : G' = Glim := tendsto_nhds_unique hGLimit hAmp
  rw [hGident] at hGRange
  obtain ⟨G'', _, hG''Limit, hQuadratic⟩ := hquadratic ε₀ hεQuadratic
  have hG''ident : G'' = Glim := tendsto_nhds_unique hG''Limit hAmp
  rw [hG''ident] at hQuadratic
  have hscaleZero : Tendsto (fun j ↦ (orbit.state j).ε) atTop (𝓝 0) :=
    (hscale ε₀ hεScale).symm.tendsto_nhds inverseCubicScale_tendsto_zero
  have hflatScale : Tendsto (fun k ↦ (orbit.state (k / 2)).ε) atTop (𝓝 0) :=
    hscaleZero.comp (Nat.tendsto_div_const_atTop (ne_of_gt Nat.two_pos))
  have hscalePositive (j : ℕ) : 0 < (orbit.state j).ε := (hgraph ε₀ hεGraph j).2.1
  have hscaleBound (j : ℕ) : (orbit.state j).ε ≤ ε₀ := (hgraph ε₀ hεGraph j).2.2
  have hradial (j : ℕ) (σ : Fin 2) :
      cR * (orbit.state j).ε ≤ ‖orbit.endpoint (2 * j + σ.val) - Clim‖ - Glim ∧
      ‖orbit.endpoint (2 * j + σ.val) - Clim‖ - Glim ≤ CR * (orbit.state j).ε := by
    have hRadius : |‖orbit.endpoint (2 * j + σ.val) - Clim‖ - (orbit.state j).amplitude| ≤
        ω ηBase * (orbit.state j).ε ^ 2 :=
      hradius ηBase hηBase ε₀ hεBase Clim hCenter j σ
    have hAmpError : |(orbit.state j).amplitude - Glim -
        (13 / 3) * Glim * (orbit.state j).ε| ≤ K * (orbit.state j).ε ^ 2 := hQuadratic j
    have hError : |‖orbit.endpoint (2 * j + σ.val) - Clim‖ - Glim -
        (13 / 3) * Glim * (orbit.state j).ε| ≤ E * (orbit.state j).ε ^ 2 := by
      calc
        _ = |(‖orbit.endpoint (2 * j + σ.val) - Clim‖ - (orbit.state j).amplitude) +
            ((orbit.state j).amplitude - Glim - (13 / 3) * Glim * (orbit.state j).ε)| := by
          congr 1
          ring
        _ ≤ |‖orbit.endpoint (2 * j + σ.val) - Clim‖ - (orbit.state j).amplitude| +
            |(orbit.state j).amplitude - Glim - (13 / 3) * Glim * (orbit.state j).ε| :=
          abs_add_le _ _
        _ ≤ ω ηBase * (orbit.state j).ε ^ 2 + K * (orbit.state j).ε ^ 2 :=
          add_le_add hRadius hAmpError
        _ = _ := by
          dsimp only [E]
          ring
    have hOne : (orbit.state j).ε ≤ 1 := (hscaleBound j).trans hsmall.2.2.2.2.2.2.2.1
    have hCap : (orbit.state j).ε ≤ cR / (E + 1) :=
      (hscaleBound j).trans hsmall.2.2.2.2.2.2.2.2
    have hCapMul : (orbit.state j).ε * (E + 1) ≤ cR := (le_div_iff₀ hden).mp hCap
    have hSmall : E * (orbit.state j).ε ≤ cR := by nlinarith [hscalePositive j]
    have hErrorLower : E * (orbit.state j).ε ^ 2 ≤ cR * (orbit.state j).ε := by
      calc
        _ = (E * (orbit.state j).ε) * (orbit.state j).ε := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hSmall (hscalePositive j).le
    have hErrorUpper : E * (orbit.state j).ε ^ 2 ≤ E * (orbit.state j).ε := by
      have hsquare : (orbit.state j).ε ^ 2 ≤ (orbit.state j).ε := by nlinarith [hscalePositive j]
      exact mul_le_mul_of_nonneg_left hsquare hE.le
    have hcoefficient : (0 : ℝ) ≤ 13 / 3 := by norm_num
    have hLeadingLower : (13 / 3) * Gmin * (orbit.state j).ε ≤
        (13 / 3) * Glim * (orbit.state j).ε :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hGRange.1 hcoefficient) (hscalePositive j).le
    have hLeadingUpper : (13 / 3) * Glim * (orbit.state j).ε ≤
        (13 / 3) * M * (orbit.state j).ε :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hGRange.2 hcoefficient) (hscalePositive j).le
    have hAbs := abs_le.mp hError
    constructor
    · dsimp only [cR] at hErrorLower ⊢
      linarith
    · dsimp only [CR]
      linarith
  refine ⟨Glim, hGlim, Clim, hAmp, hCenter, hflatScale, hCluster, ?_⟩
  intro k
  have hRadial : cR * (orbit.state (k / 2)).ε ≤ ‖orbit.endpoint k - Clim‖ - Glim ∧
      ‖orbit.endpoint k - Clim‖ - Glim ≤ CR * (orbit.state (k / 2)).ε := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · simpa using hradial j 0
    · have hdiv : (2 * j + 1) / 2 = j := by omega
      simpa [hdiv] using hradial j 1
  exact ⟨hscalePositive (k / 2), hRadial.1, hRadial.2,
    hcorrection ε₀ hεCorrection Clim hCenter k⟩

/-- Helper for cm-center-proposition: removing a nonzero amplitude from a
normalized step remainder recovers the source physical step equivalence. -/
theorem stepEquivalentOfNormalizedRemainder (s a ε : ℕ → ℝ) (c : ℝ)
    (hc : c ≠ 0) (ha : ∀ j, a j ≠ 0)
    (hremainder : (fun j ↦ s j / a j - c * ε j ^ 2) =o[atTop]
      (fun j ↦ ε j ^ 2)) :
    s ~[atTop] (fun j ↦ c * a j * ε j ^ 2) := by
  have hproduct := (Asymptotics.isBigO_refl a atTop).mul_isLittleO hremainder
  have hscaled := Asymptotics.IsLittleO.const_mul_right hc hproduct
  have hdifference : (fun j ↦ s j - c * a j * ε j ^ 2) =o[atTop]
      (fun j ↦ c * a j * ε j ^ 2) := by
    apply hscaled.congr'
    · filter_upwards [] with j
      field_simp [ha j]
    · filter_upwards [] with j
      ring
  exact hdifference

/-- Helper for cm-center-proposition: both physical source phase steps have
exact leading norms `2Gⱼεⱼ²` and `Gⱼεⱼ²`, uniformly on one initialization neighborhood. -/
theorem slowCurveStepAsymptotics (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      (fun j ↦ ‖(orbit.state j).firstDisplacement‖) ~[atTop]
        (fun j ↦ 2 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2) ∧
      (fun j ↦ ‖(orbit.state j).secondDisplacement‖) ~[atTop]
        (fun j ↦ (orbit.state j).amplitude * (orbit.state j).ε ^ 2) := by
  obtain ⟨ηFirst, hηFirst, hfirst⟩ := DFP.TwoPhaseOrbit.slowCurveFirstStepNormRemainder
    curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηSecond, hηSecond, hsecond⟩ := DFP.TwoPhaseOrbit.slowCurveSecondStepNormRemainder
    curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
  have heighth : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by norm_num
  obtain ⟨ηValid, hηValid, hvalid⟩ := DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity
    curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
    (1 / 8) heighth
  let εbar := min ηValid (min ηFirst ηSecond)
  have hεbarPos : 0 < εbar := lt_min hηValid.1 (lt_min hηFirst hηSecond)
  have hεbarLt : εbar < 1 / 4 := ((min_le_left _ _).trans hηValid.2).trans_lt heighth.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid := ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεFirst : ε₀ ∈ Set.Ioc 0 ηFirst :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεSecond : ε₀ ∈ Set.Ioc 0 ηSecond :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have ha (j : ℕ) : (orbit.state j).amplitude ≠ 0 :=
    ne_of_gt (hvalid ε₀ hεValid j).amplitude_pos
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  constructor
  · exact stepEquivalentOfNormalizedRemainder _ _ _ 2 htwo ha (hfirst ε₀ hεFirst)
  · have hremainder :
        (fun j ↦ ‖(orbit.state j).secondDisplacement‖ / (orbit.state j).amplitude -
          1 * (orbit.state j).ε ^ 2) =o[atTop] (fun j ↦ (orbit.state j).ε ^ 2) := by
      simpa only [one_mul] using hsecond ε₀ hεSecond
    simpa only [one_mul] using
      stepEquivalentOfNormalizedRemainder _ _ _ 1 one_ne_zero ha hremainder

/-- Helper for cm-center-proposition: actual flattened endpoint differences
are precisely the two physical displacements of the original recurrence. -/
theorem endpointDisplacements (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j) = (orbit.state j).firstDisplacement ∧
      orbit.endpoint (2 * j + 2) - orbit.endpoint (2 * j + 1) =
        (orbit.state j).secondDisplacement := by
  constructor
  · rw [DFP.TwoPhaseOrbit.endpoint_odd, DFP.TwoPhaseOrbit.endpoint_even,
      DFP.TwoPhaseOrbit.State.middlePoint_def]
    abel
  · have hindex : 2 * j + 2 = 2 * (j + 1) := by omega
    rw [hindex, DFP.TwoPhaseOrbit.endpoint_even, DFP.TwoPhaseOrbit.endpoint_odd,
      orbit.state_succ, DFP.TwoPhaseOrbit.State.next_point]
    abel

/-- Helper for cm-center-proposition: a cluster point of centers cannot lie
inside ANY one of their pairwise disjoint positive-radius open balls. Early
balls are included; tangency at their boundary is allowed. -/
theorem clusterPoint_outside_disjointBalls {X : Type*} [PseudoMetricSpace X]
    (c : ℕ → X) (ρ : ℕ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (Metric.ball (c i) (ρ i))
      (Metric.ball (c j) (ρ j)))) (z : X) (hz : MapClusterPt z atTop c) (i : ℕ) :
    ρ i ≤ dist z (c i) := by
  by_contra hnot
  have hzball : z ∈ Metric.ball (c i) (ρ i) := lt_of_not_ge hnot
  obtain ⟨j, hj, hlimit⟩ := hz.tendsto_subseq
  have hmem : ∀ᶠ n in atTop, c (j n) ∈ Metric.ball (c i) (ρ i) :=
    hlimit.eventually (Metric.isOpen_ball.mem_nhds hzball)
  have hafter : ∀ᶠ n in atTop, i < j n := hj.tendsto_atTop.eventually (eventually_gt_atTop i)
  obtain ⟨n, hmemn, haftern⟩ := (hmem.and hafter).exists
  have hne : i ≠ j n := ne_of_lt haftern
  have hself : c (j n) ∈ Metric.ball (c (j n)) (ρ (j n)) := Metric.mem_ball_self (hρ _)
  exact Set.disjoint_left.mp (hdisjoint hne) hmemn hself

/-- Helper for cm-center-proposition: the actual FULL-circle cluster property
and source disjointness exclude every early open interpolation ball from the
entire limiting circle, without any extra global support margin. -/
theorem limitingCircle_outside_disjointBalls (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (ρ : ℕ → ℝ)
    (hρ : ∀ i, 0 < ρ i)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (Metric.ball (orbit.endpoint i) (ρ i))
      (Metric.ball (orbit.endpoint j) (ρ j))))
    (hcluster : {z : EuclideanSpace ℝ (Fin 2) | MapClusterPt z atTop orbit.endpoint} =
      DFP.TwoPhaseOrbit.limitCircle C G) :
    ∀ i : ℕ, Disjoint (Metric.ball (orbit.endpoint i) (ρ i))
      (DFP.TwoPhaseOrbit.limitCircle C G) := by
  intro i
  apply Set.disjoint_left.mpr
  intro z hzball hzcircle
  have hz : MapClusterPt z atTop orbit.endpoint := by
    rw [← hcluster] at hzcircle
    exact hzcircle
  have hbound := clusterPoint_outside_disjointBalls orbit.endpoint ρ hρ hdisjoint z hz i
  exact not_lt_of_ge hbound hzball

/-- Helper for cm-center-proposition: the source graph construction supplies
ACTUAL radial, correction, scale-limit and full-circle data for conditional
interpolation. Only the manuscript's eventual support-radius orders and explicit
disjointness remain for the separate analytic interpolation theorem. -/
theorem centerManifoldInterpolationGeometry :
    ∃ curve : DFP.TwoLeg.SlowCurve,
      ContDiffAt ℝ 7 (fun ε ↦ (curve.shape ε, curve.high ε)) 0 ∧
      (curve.shape 0, curve.high 0) = (2, 1) ∧
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cR > 0, ∃ CR > 0, ∃ Ca > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∃ Glim > 0, ∃ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
          Tendsto (fun j ↦ (orbit.state j).center) atTop (𝓝 Clim) ∧
          Tendsto (fun k ↦ (orbit.state (k / 2)).ε) atTop (𝓝 0) ∧
          {z : EuclideanSpace ℝ (Fin 2) | MapClusterPt z atTop orbit.endpoint} =
            DFP.TwoPhaseOrbit.limitCircle Clim Glim ∧
          ∀ k : ℕ, 0 < (orbit.state (k / 2)).ε ∧
            cR * (orbit.state (k / 2)).ε ≤ ‖orbit.endpoint k - Clim‖ - Glim ∧
            ‖orbit.endpoint k - Clim‖ - Glim ≤ CR * (orbit.state (k / 2)).ε ∧
            ‖orbit.endpointCorrection Clim k‖ ≤ Ca * (orbit.state (k / 2)).ε ^ 3 := by
  obtain ⟨curve, hsmooth, hbase, _⟩ := existsSourceSlowCurve
  exact ⟨curve, hsmooth, hbase, slowCurveRadialCoefficientBounds curve⟩

end DFPWolfe.V21.CenterManifold
