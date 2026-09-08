module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CoordinateSmoothness
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Uniform
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CoordinateSmoothness
import all ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet

/-!
# Joint graph-path smoothness and uniform Taylor jets of all observables
-/

public section

noncomputable section

open scoped EuclideanSpace Matrix Nat ContDiff

namespace DFP.TwoLeg

/-- The canonical ordered vector of all thirteen real observables as a function of the
three-dimensional canceled state. -/
def observableCoordinates (x : ℝ × ℝ × ℝ) : Fin 13 → ℝ :=
  let observable := observableMap x
  ![observable.amplitudeRatio, observable.frameAngleIncrement,
    observable.halfCenterDisplacement 0, observable.halfCenterDisplacement 1,
    observable.fullCenterDisplacement 0, observable.fullCenterDisplacement 1,
    observable.firstEndpointAngleIncrement.toReal,
    observable.secondEndpointAngleIncrement.toReal,
    observable.firstStepNorm, observable.secondStepNorm,
    observable.initialGradientNorm, observable.intermediateGradientNorm,
    observable.finalGradientNorm]

/-- The named canonical observable vector is smooth to every order at the canceled base. -/
@[fun_prop]
theorem observableCoordinates_contDiffAt (k : ℕ∞ω) :
    ContDiffAt ℝ k observableCoordinates (0, 2, 1) := by
  unfold observableCoordinates
  exact observableCoordinateVector_contDiffAt k

/-- All thirteen observables evaluated along the polynomial graph-jet family. -/
def graphObservableFamily (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) : Fin 13 → ℝ :=
  observableCoordinates (graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε)

/-- The complete graph-observable family is jointly smooth to every order at each point of the
zero-scale coefficient fiber. -/
theorem graphObservableFamily_contDiffAt (k : ℕ∞ω)
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ k (Function.uncurry graphObservableFamily) (θ, 0) := by
  let path : (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) → ℝ × ℝ × ℝ :=
    Function.uncurry (fun η : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
      graphJetPath η.1.1 η.1.2 η.2.1 η.2.2 ε)
  have hpath : ContDiffAt ℝ k path (θ, 0) := by
    dsimp only [path, Function.uncurry_apply_pair]
    unfold graphJetPath
    fun_prop
  have hbase : path (θ, 0) = (0, 2, 1) := by
    simp [path, graphJetPath]
  have houter := observableCoordinates_contDiffAt k
  rw [← hbase] at houter
  have hcomp := houter.comp (θ, 0) hpath
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [] with z
  rcases z with ⟨η, ε⟩
  rfl

/-- On every closed coefficient ball, the derivative-constructed order-nine jets of the complete
graph-observable family are uniform. -/
theorem graphObservableFamily_uniformOn (B : ℝ) :
    FiniteTaylorJet.IsUniformOn graphObservableFamily
      (fun θ ↦ FiniteTaylorJet.ofFunction ℝ 9 (graphObservableFamily θ) 0) 0
      (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) := by
  apply FiniteTaylorJet.isUniformOn_of_contDiffAt 9 graphObservableFamily 0
    (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) (isCompact_closedBall _ _)
  intro θ hθ
  exact graphObservableFamily_contDiffAt 9 θ

end DFP.TwoLeg
