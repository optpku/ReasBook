module

public import ReasLib.LinearAlgebra.Matrix.OrientedEigenframe
public import ReasLib.Optimization.DFP.InverseUpdate
public import ReasLib.Optimization.DFP.SpectralRecovery
public import ReasLib.Optimization.DFP.TwoPhaseControls
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.LinearAlgebra.Matrix.OrientedEigenframe
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import all ReasLib.Optimization.DFP.AbstractSecantStep
import all ReasLib.Optimization.DFP.InverseUpdate
import all ReasLib.Optimization.DFP.SpectralRecovery
import all ReasLib.Optimization.DFP.TwoPhaseControls
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.TwoLeg.Mixed

/-- One inverse-form DFP step, computed directly from a metric, gradient, and planar
control. -/
private def rawStep (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) : Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) :=
  let v := H *ᵥ g
  let α := control.tau * (g ⬝ᵥ v) / (v ⬝ᵥ (control.matrix *ᵥ v))
  let s := -(α • v)
  let y := control.matrix *ᵥ s
  (Matrix.inverseDFPUpdate H s y, g + y)

/-- The bounded mixed-parameter region with control coordinate `b` in `[-β, β]`
and coefficient pair `(P, J)` in the closed ball of radius `B`. -/
def parameterSet (β B : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Icc (-β) β ×ˢ Metric.closedBall (0 : ℝ × ℝ) B

/-- The canonical input `(r, 2 + P * b * r, 1 + J * b * r)` associated to mixed
parameters `(b, P, J)`. -/
def input (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ × ℝ × ℝ :=
  (r, 2 + θ.2.1 * θ.1 * r, 1 + θ.2.2 * θ.1 * r)

/-- The exact two-leg canonical-state map with independent control scale `b` and
radius `r`, extended at the removable base radius by `(0, 2, 1)`. -/
def map (b : ℝ) (state : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let r := state.1
  let p := state.2.1
  let h := state.2.2
  if r = 0 then
    (0, 2, 1)
  else
    let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
    let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * r]
    let firstStep := rawStep H₀ g₀ (TwoPhaseControls.first b)
    let firstFrame := OrientedEigenframe.frame
      (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
      (WithLp.toLp 2 firstStep.2)
    let H₁ := firstFrame.transpose * firstStep.1 * firstFrame
    let g₁ := firstFrame.transpose *ᵥ firstStep.2
    let secondStep := rawStep H₁ g₁ (TwoPhaseControls.second b)
    let secondFrame := OrientedEigenframe.frame
      (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
      (WithLp.toLp 2 secondStep.2)
    let g₂ := secondFrame.transpose *ᵥ secondStep.2
    let lambdaMinus := RealSymmetric2.low
      (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
    let lambdaPlus := RealSymmetric2.high
      (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
    (CycleBoundaryState.recoveryRadius lambdaMinus lambdaPlus (g₂ 0) (g₂ 1),
      CycleBoundaryState.recoveryShape lambdaMinus lambdaPlus (g₂ 0) (g₂ 1),
      lambdaPlus)

/-- Membership in the mixed parameter set separates into the control interval and
the coefficient ball. -/
theorem mem_parameterSet (θ : ℝ × ℝ × ℝ) (β B : ℝ) :
    θ ∈ parameterSet β B ↔
      θ.1 ∈ Set.Icc (-β) β ∧ θ.2 ∈ Metric.closedBall (0 : ℝ × ℝ) B := by
  rfl

/-- Evaluation of the mixed canonical input. -/
theorem input_apply (b P J r : ℝ) :
    input (b, P, J) r = (r, 2 + P * b * r, 1 + J * b * r) := by
  rfl

/-- The removable mixed map fixes the canonical base state for every control scale. -/
theorem map_zero (b : ℝ) : map b (0, 2, 1) = (0, 2, 1) := by
  simp [map]

/-- Helper for Appendix Lemma A.5: the oriented frame reconstructed from the
first leg output agrees with the canonical first-leg frame when its low
coordinate is positive. -/
private lemma orientedFirstFrame_eq (x : ℝ × ℝ × ℝ)
    (hcoord : 0 < (DFP.FirstLeg.coordinates x.1 x.2.1 x.2.2).1) :
    OrientedEigenframe.frame
        (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
        (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
        (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1)
        (WithLp.toLp 2 (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2)) =
      DFP.FirstLeg.frame x.1 x.2.1 x.2.2 := by
  rw [OrientedEigenframe.frame]
  unfold OrientedEigenframe.lowVector
  split_ifs with hif
  · rfl
  · exfalso
    have hinner : inner ℝ
        (RealSymmetric2.lowVector
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1))
        (WithLp.toLp 2 (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2)) =
        (DFP.FirstLeg.coordinates x.1 x.2.1 x.2.2).1 := by
      simp [DFP.FirstLeg.coordinates, DFP.FirstLeg.frame,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
        EuclideanPlane.frame, PiLp.inner_apply]
      ring
    apply (not_lt_of_ge (le_of_not_gt hif))
    rw [hinner]
    exact hcoord

/-- Helper for Appendix Lemma A.5: the oriented frame reconstructed from the
second leg output agrees with the canonical second-leg frame when its low
coordinate is positive. -/
private lemma orientedSecondFrame_eq (x : ℝ × ℝ × ℝ)
    (hcoord : 0 < (DFP.SecondLeg.coordinates x.1 x.2.1 x.2.2).1) :
    OrientedEigenframe.frame
        (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
        (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
        (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1)
        (WithLp.toLp 2 (DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2)) =
      DFP.SecondLeg.frame x.1 x.2.1 x.2.2 := by
  rw [OrientedEigenframe.frame]
  unfold OrientedEigenframe.lowVector
  split_ifs with hif
  · rfl
  · exfalso
    have hinner : inner ℝ
        (RealSymmetric2.lowVector
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1))
        (WithLp.toLp 2 (DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2)) =
        (DFP.SecondLeg.coordinates x.1 x.2.1 x.2.2).1 := by
      simp [DFP.SecondLeg.coordinates, DFP.SecondLeg.frame,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
        EuclideanPlane.frame, PiLp.inner_apply]
      ring
    apply (not_lt_of_ge (le_of_not_gt hif))
    rw [hinner]
    exact hcoord

/-- Helper for Appendix Lemma A.5: the first mixed control matrix is positive
definite throughout the small signed-scale neighborhood. -/
private lemma firstControl_pos (ε : ℝ) (hε : |ε| < (1 / 4 : ℝ)) :
    (TwoPhaseControls.first ε).matrix.PosDef := by
  rw [TwoPhaseControls.first_matrix]
  have hHermitian : (!![1, ε; ε, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hquadratic : ∀ x : Fin 2 → ℝ, x ≠ 0 →
      0 < x ⬝ᵥ (!![1, ε; ε, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x := by
    intro x hx
    have hleft : -(1 / 4 : ℝ) < ε := (abs_lt.mp hε).1
    have hright : ε < (1 / 4 : ℝ) := (abs_lt.mp hε).2
    have hs : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      have hc : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra hn
        apply hx
        funext i
        fin_cases i
        · exact not_ne_iff.mp (not_or.mp hn).1
        · exact not_ne_iff.mp (not_or.mp hn).2
      rcases hc with h0 | h1
      · nlinarith [sq_pos_of_ne_zero h0]
      · nlinarith [sq_pos_of_ne_zero h1]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]
  exact Matrix.PosDef.of_dotProduct_mulVec_pos hHermitian hquadratic

/-- Helper for Appendix Lemma A.5: the second mixed control matrix is positive
definite throughout the small signed-scale neighborhood. -/
private lemma secondControl_pos (ε : ℝ) (hε : |ε| < (1 / 4 : ℝ)) :
    (TwoPhaseControls.second ε).matrix.PosDef := by
  rw [TwoPhaseControls.second_matrix]
  have hHermitian :
      (!![1, -2 * ε; -2 * ε, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hquadratic : ∀ x : Fin 2 → ℝ, x ≠ 0 →
      0 < x ⬝ᵥ (!![1, -2 * ε; -2 * ε, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x := by
    intro x hx
    have hleft : -(1 / 4 : ℝ) < ε := (abs_lt.mp hε).1
    have hright : ε < (1 / 4 : ℝ) := (abs_lt.mp hε).2
    have hs : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      have hc : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra hn
        apply hx
        funext i
        fin_cases i
        · exact not_ne_iff.mp (not_or.mp hn).1
        · exact not_ne_iff.mp (not_or.mp hn).2
      rcases hc with h0 | h1
      · nlinarith [sq_pos_of_ne_zero h0]
      · nlinarith [sq_pos_of_ne_zero h1]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]
  exact Matrix.PosDef.of_dotProduct_mulVec_pos hHermitian hquadratic


/-- Away from zero signed scale and near the canonical base state, specializing the
independent radius to `ε ^ 2` agrees with the square of the signed-scale coordinate
of `DFP.TwoLeg.stateMap`. -/
theorem map_fixedScale :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      x.1 ≠ 0 →
        map x.1 (x.1 ^ 2, x.2.1, x.2.2) =
          ((DFP.TwoLeg.stateMap x).1 ^ 2,
          (DFP.TwoLeg.stateMap x).2.1, (DFP.TwoLeg.stateMap x).2.2) := by
  have hsmall : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), |x.1| < (1 / 4 : ℝ) := by
    have hc : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ |x.1|) (0, 2, 1) :=
      continuousAt_fst.abs
    have hbase : (fun x : ℝ × ℝ × ℝ ↦ |x.1|) (0, 2, 1) < 1 / 4 := by
      norm_num
    exact hc.eventually (Iio_mem_nhds hbase)
  have hp : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < x.2.1 := by
    have hc : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
      continuousAt_fst.comp continuousAt_snd
    have hbase : (0 : ℝ) < 2 := by
      norm_num
    exact hc.eventually (Ioi_mem_nhds hbase)
  have hh : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < x.2.2 := by
    have hc : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.2) (0, 2, 1) :=
      continuousAt_snd.comp continuousAt_snd
    have hbase : (0 : ℝ) < 1 := by
      norm_num
    exact hc.eventually (Ioi_mem_nhds hbase)
  have hfirstcoord := DFP.FirstLeg.frameOriented
  have hsecondcoord := DFP.SecondLeg.frameOriented
  have hfac := DFP.FirstLeg.factorsAnalytic.continuousAt
  have hspectral := continuousAt_fst.comp hfac
  have hgradient := continuousAt_fst.comp (continuousAt_snd.comp hfac)
  have hL : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1 := by
    have hc : ContinuousAt
        (fun x : ℝ × ℝ × ℝ ↦
          (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1) (0, 2, 1) :=
      (continuousAt_fst.comp hspectral)
    have hbase : (DFP.FirstLeg.spectralFactors 0 2 1).1 = 2 := by
      simpa only [DFP.FirstLeg.factors] using
        congrArg (fun y ↦ y.1.1) DFP.FirstLeg.factorsBase
    apply hc.eventually
    have hbasePos : 0 < (fun x : ℝ × ℝ × ℝ ↦
        (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1) (0, 2, 1) := by
      change 0 < (DFP.FirstLeg.spectralFactors 0 2 1).1
      rw [hbase]
      norm_num
    exact Ioi_mem_nhds hbasePos
  have hH : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2 := by
    have hc : ContinuousAt
        (fun x : ℝ × ℝ × ℝ ↦
          (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2) (0, 2, 1) :=
      (continuousAt_snd.comp hspectral)
    have hbase : (DFP.FirstLeg.spectralFactors 0 2 1).2 = 1 := by
      simpa only [DFP.FirstLeg.factors] using
        congrArg (fun y ↦ y.1.2) DFP.FirstLeg.factorsBase
    apply hc.eventually
    have hbasePos : 0 < (fun x : ℝ × ℝ × ℝ ↦
        (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2) (0, 2, 1) := by
      change 0 < (DFP.FirstLeg.spectralFactors 0 2 1).2
      rw [hbase]
      norm_num
    exact Ioi_mem_nhds hbasePos
  have hQ : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1 := by
    have hc : ContinuousAt
        (fun x : ℝ × ℝ × ℝ ↦
          (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1) (0, 2, 1) :=
      (continuousAt_fst.comp hgradient)
    have hbase : (DFP.FirstLeg.gradientFactors 0 2 1).1 = 1 := by
      simpa only [DFP.FirstLeg.factors] using
        congrArg (fun y ↦ y.2.1.1) DFP.FirstLeg.factorsBase
    apply hc.eventually
    have hbasePos : 0 < (fun x : ℝ × ℝ × ℝ ↦
        (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1) (0, 2, 1) := by
      change 0 < (DFP.FirstLeg.gradientFactors 0 2 1).1
      rw [hbase]
      norm_num
    exact Ioi_mem_nhds hbasePos
  have hR : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1 := by
    have hfac2 := DFP.SecondLeg.factorsAnalytic.continuousAt
    have hcanPair := continuousAt_snd.comp (continuousAt_snd.comp hfac2)
    have hc : ContinuousAt
        (fun x : ℝ × ℝ × ℝ ↦
          (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1) (0, 2, 1) :=
      continuousAt_fst.comp hcanPair
    have hbase : (DFP.SecondLeg.canonicalFactors 0 2 1).1 = 1 := by
      simpa only [DFP.SecondLeg.factors] using
        congrArg (fun y ↦ y.2.2.1) DFP.SecondLeg.factorsBase
    apply hc.eventually
    have hbasePos : 0 < (fun x : ℝ × ℝ × ℝ ↦
        (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1) (0, 2, 1) := by
      change 0 < (DFP.SecondLeg.canonicalFactors 0 2 1).1
      rw [hbase]
      norm_num
    exact Ioi_mem_nhds hbasePos
  filter_upwards [hsmall, hp, hh, hfirstcoord, hsecondcoord, hL, hH, hQ,
    hR, DFP.FirstLeg.frameDiagonalization, DFP.FirstLeg.gradientFactorization,
    DFP.SecondLeg.frameDiagonalization, DFP.SecondLeg.gradientFactorization,
    DFP.SecondLeg.canonicalFactorization, DFP.SecondLeg.spectrumFactorization]
    with x hsmall hp hh hcoord1 hcoord2 hL hH hQ hR hdiag1 hgrad1 hdiag2 hgrad2 hcan hspectrum
  intro hx
  have hε4 : 0 < x.1 ^ 4 := by
    have hpow : x.1 ^ 4 = (x.1 ^ 2) ^ 2 := by
      ring
    rw [hpow]
    exact sq_pos_of_ne_zero (pow_ne_zero 2 hx)
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal ![x.2.2 * x.2.1 * (x.1 ^ 2) ^ 2, x.2.2]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), x.2.1 * x.1 ^ 2]
  have hH₀ : H₀.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · dsimp [H₀]
      have hε4' : 0 < (x.1 ^ 2) ^ 2 := by
        have hpow : (x.1 ^ 2) ^ 2 = x.1 ^ 4 := by
          ring
        rw [hpow]
        exact hε4
      exact mul_pos (mul_pos hh hp) hε4'
    · dsimp [H₀]
      exact hh
  have hA₀ : (TwoPhaseControls.first x.1).matrix.PosDef :=
    firstControl_pos x.1 hsmall
  have hτ₀ : 0 < (TwoPhaseControls.first x.1).tau :=
    TwoPhaseControls.tau_pos x.1 0
  have hg₀ : g₀ ≠ 0 := by
    intro hz
    have hz0 := congrArg (fun q : Fin 2 → ℝ => q 0) hz
    simp [g₀] at hz0
  let z₀ := DFP.AbstractSecantStep.ofMatrices H₀ g₀
    (TwoPhaseControls.first x.1).matrix (TwoPhaseControls.first x.1).tau
    hH₀ hA₀ hτ₀ hg₀
  have hraw₀ : rawStep H₀ g₀ (TwoPhaseControls.first x.1) =
      (z₀.nextInverseHessian, z₀.nextGradient) := by
    rfl
  have hz₀ : (z₀.nextInverseHessian, z₀.nextGradient) =
      (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2,
        DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2) := by
    have hHspec : z₀.inverseHessian = Matrix.diagonal
        ![x.2.2 * x.2.1 * x.1 ^ 4, x.2.2] := by
      change H₀ = _
      dsimp [H₀]
      congr 2
      ring
    have hgspec : z₀.gradient = (1 : ℝ) • ![(1 : ℝ), x.2.1 * x.1 ^ 2] := by
      change g₀ = _
      simp [g₀]
    have hAspec : z₀.secantMatrix = (TwoPhaseControls.first x.1).matrix := by
      rfl
    have hτspec : z₀.tau = (TwoPhaseControls.first x.1).tau := by
      rfl
    have hout := DFP.FirstLeg.outputEqStep z₀ x.1 x.2.1 x.2.2 1
      hHspec hgspec hAspec hτspec
    simpa using hout
  have hfirstRaw : rawStep H₀ g₀ (TwoPhaseControls.first x.1) =
      (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2,
        DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2) := by
    rw [hraw₀, hz₀]
  have hframe₁ : OrientedEigenframe.frame
      (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
      (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
      (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1)
      (WithLp.toLp 2 (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2)) =
      DFP.FirstLeg.frame x.1 x.2.1 x.2.2 :=
    orientedFirstFrame_eq x hcoord1
  have hdiag₁ := hdiag1
  have hgrad₁ : (DFP.FirstLeg.frame x.1 x.2.1 x.2.2).transpose *ᵥ
      (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2) =
      ![(DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1,
        x.1 ^ 2 * (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2] := by
    simpa using hgrad1 1
  let H₁ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal
      ![x.1 ^ 4 * (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1,
        (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2]
  let g₁ : Fin 2 → ℝ := ![(DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1,
      x.1 ^ 2 * (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2]
  have hH₁ : H₁.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · dsimp [H₁]
      exact mul_pos hε4 hL
    · dsimp [H₁]
      exact hH
  have hA₁ : (TwoPhaseControls.second x.1).matrix.PosDef :=
    secondControl_pos x.1 hsmall
  have hτ₁ : 0 < (TwoPhaseControls.second x.1).tau :=
    TwoPhaseControls.tau_pos x.1 1
  have hg₁ : g₁ ≠ 0 := by
    intro hz
    have hz0 := congrArg (fun q : Fin 2 → ℝ => q 0) hz
    have hz0' : (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1 = 0 := by
      simpa [g₁] using hz0
    exact (ne_of_gt hQ) hz0'
  let z₁ := DFP.AbstractSecantStep.ofMatrices H₁ g₁
    (TwoPhaseControls.second x.1).matrix (TwoPhaseControls.second x.1).tau
    hH₁ hA₁ hτ₁ hg₁
  have hraw₁ :
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2).transpose *
          DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 *
          DFP.FirstLeg.frame x.1 x.2.1 x.2.2 = H₁ := by
    simpa [H₁] using hdiag₁
  have hrawg₁ :
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2).transpose *ᵥ
          DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 = g₁ := by
    simpa [g₁] using hgrad₁
  have hrawSecond :
      rawStep
          ((DFP.FirstLeg.frame x.1 x.2.1 x.2.2).transpose *
            DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 *
            DFP.FirstLeg.frame x.1 x.2.1 x.2.2)
          ((DFP.FirstLeg.frame x.1 x.2.1 x.2.2).transpose *ᵥ
            DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2)
          (TwoPhaseControls.second x.1) =
        (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2,
          DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) := by
    have hz₁ : (z₁.nextInverseHessian, z₁.nextGradient) =
        (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2,
          DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) := by
      have hHspec : z₁.inverseHessian = H₁ := by rfl
      have hgspec : z₁.gradient = g₁ := by rfl
      have hAspec : z₁.secantMatrix = (TwoPhaseControls.second x.1).matrix := by rfl
      have hτspec : z₁.tau = (TwoPhaseControls.second x.1).tau := by rfl
      have hgspec' : z₁.gradient = (1 : ℝ) • ![
          (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1,
          x.1 ^ 2 * (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2] := by
        simpa [g₁] using hgspec
      simpa using (DFP.SecondLeg.outputEqStep z₁ x.1 x.2.1 x.2.2 1
        hHspec hgspec' hAspec hτspec)
    have hrawz : rawStep H₁ g₁ (TwoPhaseControls.second x.1) =
        (z₁.nextInverseHessian, z₁.nextGradient) := by rfl
    rw [hraw₁, hrawg₁, hrawz, hz₁]
  have hframe₂ : OrientedEigenframe.frame
      (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
      (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
      (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1)
      (WithLp.toLp 2 (DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2)) =
      DFP.SecondLeg.frame x.1 x.2.1 x.2.2 :=
    orientedSecondFrame_eq x hcoord2
  have hcan := hcan hx
  have hsqrt :
      ((x.1 * Real.sqrt
          (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1) ^ 2) =
        x.1 ^ 2 * (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1 := by
    have hs := Real.sq_sqrt (le_of_lt hR)
    calc
      (x.1 * Real.sqrt
          (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1) ^ 2 =
          x.1 ^ 2 * (Real.sqrt
            (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1) ^ 2 := by ring
      _ = _ := by rw [hs]
  unfold map
  dsimp
  have hsqne : x.1 ^ 2 ≠ 0 := pow_ne_zero 2 hx
  rw [if_neg hsqne]
  rw [hfirstRaw, hframe₁]
  rw [hrawSecond, hframe₂]
  have hrec : DFP.SecondLeg.recovered x.1 x.2.1 x.2.2 =
      (x.1 ^ 2 * (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1,
        (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).2) := hcan
  change ((DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).1,
      (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).2,
      (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).2) = _
  change ((DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).1,
      (DFP.SecondLeg.recovered x.1 x.2.1 x.2.2).2,
      (DFP.SecondLeg.eigenvalues x.1 x.2.1 x.2.2).2) =
    ((x.1 * Real.sqrt
        (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).1) ^ 2,
      (DFP.SecondLeg.canonicalFactors x.1 x.2.1 x.2.2).2,
      (DFP.SecondLeg.spectralFactors x.1 x.2.1 x.2.2).2)
  rw [hrec, hsqrt]
  have hhigh := congrArg Prod.snd hspectrum
  rw [hhigh]

end DFP.TwoLeg.Mixed
