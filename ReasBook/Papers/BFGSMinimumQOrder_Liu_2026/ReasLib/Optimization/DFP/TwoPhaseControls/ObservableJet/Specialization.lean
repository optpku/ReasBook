module

public import ReasLib.Optimization.DFP.TwoPhaseControls.ObservableJet
import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.SlowGraphRemainder
import ReasLib.Optimization.DFP.TwoPhaseControls.CenterJet.HalfRemainder
import ReasLib.Optimization.DFP.TwoPhaseControls.CenterJet.SlowGraphRemainder
import all ReasLib.Optimization.DFP.TwoPhaseControls.ObservableJet

public section

noncomputable section

namespace DFP.TwoLeg.ObservableJet

/-- The strongest certified truncation order for each coordinate of the
complete two-leg observable along the polynomial slow-graph path. -/
def slowOrder : Fin 13 → ℕ :=
  ![7, 6, 3, 5, 7, 8, 6, 6, 6, 6, 5, 6, 6]

/-- Evaluation of the coordinatewise truncation orders for the slow-graph
observable jets. -/
theorem slowOrder_apply (i : Fin 13) :
    slowOrder i = ![7, 6, 3, 5, 7, 8, 6, 6, 6, 6, 5, 6, 6] i := by
  rfl

/-- The ordered vector of explicit polynomial models for the thirteen
complete two-leg observables along the polynomial slow-graph path. -/
def slowPolynomial (ε : ℝ) : Fin 13 → ℝ :=
  ![1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7,
    -3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6,
    2 * ε ^ 3,
    2 * ε ^ 5,
    -(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7,
    -(508 / 5) * ε ^ 8,
    -2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6,
    -ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6,
    2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6,
    ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6,
    1 + 2 * ε ^ 4,
    1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6,
    1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6]

/-- Evaluation of the ordered polynomial models for the slow-graph
observable jets. -/
theorem slowPolynomial_apply (ε : ℝ) (i : Fin 13) :
    slowPolynomial ε i =
      ![1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7,
        -3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6,
        2 * ε ^ 3,
        2 * ε ^ 5,
        -(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7,
        -(508 / 5) * ε ^ 8,
        -2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6,
        -ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6,
        2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6,
        ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6,
        1 + 2 * ε ^ 4,
        1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6,
      1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6] i := by
  rfl

/-- Every scalar coordinate of the complete observable is smooth along the
polynomial slow-graph path to each prescribed finite order. -/
private theorem slowObservableCoordinate_contDiffAt (n : ℕ) (i : Fin 13) :
    ContDiffAt ℝ n
      (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.slowGraphJetPath ε)) i) 0 := by
  have hpathPolynomial : ContDiffAt ℝ n
      (fun ε : ℝ ↦
        (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
          1 + 8 * ε ^ 3)) 0 := by
    fun_prop
  have hpathEq : DFP.TwoLeg.slowGraphJetPath =
      (fun ε : ℝ ↦
        (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
          1 + 8 * ε ^ 3)) := by
    funext ε
    exact DFP.TwoLeg.slowGraphJetPath_apply ε
  have hpath : ContDiffAt ℝ n DFP.TwoLeg.slowGraphJetPath 0 := by
    simpa only [hpathEq] using hpathPolynomial
  have hpathBase : DFP.TwoLeg.slowGraphJetPath 0 =
      ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    rw [DFP.TwoLeg.slowGraphJetPath_apply]
    norm_num
  have houter : ContDiffAt ℝ n
      (fun x : ℝ × ℝ × ℝ ↦ coordinates (DFP.TwoLeg.observableMap x))
      ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    simpa only [coordinates] using DFP.TwoLeg.observableCoordinateVector_contDiffAt n
  rw [← hpathBase] at houter
  have hvector := houter.comp 0 hpath
  have hvector' : ContDiffAt ℝ n
      (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.slowGraphJetPath ε))) 0 := by
    simpa only [Function.comp_def] using hvector
  rw [contDiffAt_pi] at hvector'
  exact hvector' i

/-- An order-`n + 1` remainder identifies the order-`n` finite jet of one
smooth slow-graph observable coordinate with its polynomial model. -/
private theorem slowObservableCoordinateJet_eq_of_remainder
    (i : Fin 13) (n : ℕ) (P : ℝ → ℝ)
    (hP : ContDiffAt ℝ n P 0)
    (hR : (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
      (DFP.TwoLeg.slowGraphJetPath ε)) i - P ε) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ (n + 1))) :
    FiniteTaylorJet.ofFunction ℝ n
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) i) 0 =
      FiniteTaylorJet.ofFunction ℝ n P 0 := by
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
    (slowObservableCoordinate_contDiffAt n i) hP
  simpa only [zero_add] using hR

/-- A little-oh remainder of order `n` identifies the order-`n` finite jet of
one smooth slow-graph observable coordinate with its polynomial model. -/
private theorem slowObservableCoordinateJet_eq_of_isLittleO
    (i : Fin 13) (n : ℕ) (P : ℝ → ℝ)
    (hP : ContDiffAt ℝ n P 0)
    (hR : (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
      (DFP.TwoLeg.slowGraphJetPath ε)) i - P ε) =o[nhds 0]
        (fun ε : ℝ ↦ ε ^ n)) :
    FiniteTaylorJet.ofFunction ℝ n
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) i) 0 =
      FiniteTaylorJet.ofFunction ℝ n P 0 := by
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isLittleO
    (slowObservableCoordinate_contDiffAt n i) hP
  simpa only [zero_add] using hR

/-- Every coordinate of the complete two-leg observable along the polynomial
slow-graph path has its displayed polynomial jet at the strongest certified order. -/
theorem slowGraphJets (i : Fin 13) :
    FiniteTaylorJet.ofFunction ℝ (slowOrder i)
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) i) 0 =
      FiniteTaylorJet.ofFunction ℝ (slowOrder i)
        (fun ε : ℝ ↦ slowPolynomial ε i) 0 := by
  fin_cases i
  · have hmodel : ContDiffAt ℝ 7
        (fun ε : ℝ ↦
          1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7) 0 := by
      fun_prop
    have hremainder :
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) 0 -
            (1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7)) =O[nhds 0]
          (fun ε : ℝ ↦ ε ^ (7 + 1)) := by
      simpa [coordinates, DFP.TwoLeg.observableCoordinates] using
        DFP.TwoLeg.slowGraphAmplitudeRemainderDirect
    have hjet := slowObservableCoordinateJet_eq_of_remainder 0 7
      (fun ε : ℝ ↦
        1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7)
      hmodel hremainder
    simpa [slowOrder, slowPolynomial] using hjet
  · have hmodel : ContDiffAt ℝ 6
        (fun ε : ℝ ↦ -3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6) 0 := by
      fun_prop
    have hremainder :
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) 1 -
            (-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)) =O[nhds 0]
          (fun ε : ℝ ↦ ε ^ (6 + 1)) := by
      simpa [coordinates, DFP.TwoLeg.observableCoordinates] using
        DFP.TwoLeg.slowGraphFrameAngleRemainder
    have hjet := slowObservableCoordinateJet_eq_of_remainder 1 6
      (fun ε : ℝ ↦ -3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)
      hmodel hremainder
    simpa [slowOrder, slowPolynomial] using hjet
  · let p₀ : ℝ → ℝ := fun ε ↦
      2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
    let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
    have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[nhds 0] (fun ε : ℝ ↦ ε ^ 5) :=
      Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (nhds 0)
    have hp : (fun ε ↦ p₀ ε -
        (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5) := by simpa [p₀] using hzero
    have hh : (fun ε ↦ h₀ ε - (1 + 8 * ε ^ 3)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5) := by simpa [h₀] using hzero
    have hraw := DFP.TwoLeg.CenterJet.slowHalfLowRemainderViaCancellation
      p₀ h₀ hp hh
    have hremainder :
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) 2 - 2 * ε ^ 3) =o[nhds 0]
          (fun ε : ℝ ↦ ε ^ 3) := by
      simpa [p₀, h₀, DFP.TwoLeg.slowGraphJetPath_apply, coordinates,
        DFP.TwoLeg.observableCoordinates] using hraw
    have hjet := slowObservableCoordinateJet_eq_of_isLittleO 2 3
      (fun ε : ℝ ↦ 2 * ε ^ 3) (by fun_prop) hremainder
    simpa [slowOrder, slowPolynomial] using hjet
  · let p₀ : ℝ → ℝ := fun ε ↦
      2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
    let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
    have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[nhds 0] (fun ε : ℝ ↦ ε ^ 5) :=
      Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (nhds 0)
    have hp : (fun ε ↦ p₀ ε -
        (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5) := by simpa [p₀] using hzero
    have hh : (fun ε ↦ h₀ ε - (1 + 8 * ε ^ 3)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5) := by simpa [h₀] using hzero
    have hraw := DFP.TwoLeg.CenterJet.slowHalfHighRemainderViaCancellation
      p₀ h₀ hp hh
    have hremainder :
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) 3 - 2 * ε ^ 5) =o[nhds 0]
          (fun ε : ℝ ↦ ε ^ 5) := by
      simpa [p₀, h₀, DFP.TwoLeg.slowGraphJetPath_apply, coordinates,
        DFP.TwoLeg.observableCoordinates] using hraw
    have hjet := slowObservableCoordinateJet_eq_of_isLittleO 3 5
      (fun ε : ℝ ↦ 2 * ε ^ 5) (by fun_prop) hremainder
    simpa [slowOrder, slowPolynomial] using hjet
  · have hmodel : ContDiffAt ℝ 7
        (fun ε : ℝ ↦ -(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7) 0 := by
      fun_prop
    have hremainder :
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) 4 -
            (-(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7)) =O[nhds 0]
          (fun ε : ℝ ↦ ε ^ (7 + 1)) := by
      simpa [coordinates, DFP.TwoLeg.observableCoordinates] using
        DFP.TwoLeg.CenterJet.slowGraphFullCenterLowRemainder
    have hjet := slowObservableCoordinateJet_eq_of_remainder 4 7
      (fun ε : ℝ ↦ -(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7)
      hmodel hremainder
    simpa [slowOrder, slowPolynomial] using hjet
  · have hmodel : ContDiffAt ℝ 8 (fun ε : ℝ ↦ -(508 / 5) * ε ^ 8) 0 := by
      fun_prop
    have hremainder :
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) 5 - (-(508 / 5) * ε ^ 8)) =O[nhds 0]
          (fun ε : ℝ ↦ ε ^ (8 + 1)) := by
      simpa [coordinates, DFP.TwoLeg.observableCoordinates] using
        DFP.TwoLeg.CenterJet.slowGraphFullCenterHighRemainder
    have hjet := slowObservableCoordinateJet_eq_of_remainder 5 8
      (fun ε : ℝ ↦ -(508 / 5) * ε ^ 8) hmodel hremainder
    simpa [slowOrder, slowPolynomial] using hjet
  · have hmodel : ContDiffAt ℝ 6
        (fun ε : ℝ ↦ -2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6) 0 := by
      fun_prop
    have hremainder :
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) 6 -
            (-2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6)) =O[nhds 0]
          (fun ε : ℝ ↦ ε ^ (6 + 1)) := by
      simpa [coordinates, DFP.TwoLeg.observableCoordinates] using
        DFP.TwoLeg.EndpointAngleJet.slowFirst
    have hjet := slowObservableCoordinateJet_eq_of_remainder 6 6
      (fun ε : ℝ ↦ -2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6)
      hmodel hremainder
    simpa [slowOrder, slowPolynomial] using hjet
  · have hmodel : ContDiffAt ℝ 6
        (fun ε : ℝ ↦ -ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6) 0 := by
      fun_prop
    have hremainder :
        (fun ε : ℝ ↦ coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)) 7 -
            (-ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6)) =O[nhds 0]
          (fun ε : ℝ ↦ ε ^ (6 + 1)) := by
      simpa [coordinates, DFP.TwoLeg.observableCoordinates] using
        DFP.TwoLeg.EndpointAngleJet.slowSecond
    have hjet := slowObservableCoordinateJet_eq_of_remainder 7 6
      (fun ε : ℝ ↦ -ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6)
      hmodel hremainder
    simpa [slowOrder, slowPolynomial] using hjet
  · simpa [slowOrder, slowPolynomial, coordinates] using
      DFP.TwoLeg.NormJet.slowFirstStep
  · simpa [slowOrder, slowPolynomial, coordinates] using
      DFP.TwoLeg.NormJet.slowSecondStep
  · simpa [slowOrder, slowPolynomial, coordinates] using
      DFP.TwoLeg.NormJet.slowInitialGradient
  · simpa [slowOrder, slowPolynomial, coordinates] using
      DFP.TwoLeg.NormJet.slowIntermediateGradient
  · simpa [slowOrder, slowPolynomial, coordinates] using
      DFP.TwoLeg.NormJet.slowFinalGradient

end DFP.TwoLeg.ObservableJet
