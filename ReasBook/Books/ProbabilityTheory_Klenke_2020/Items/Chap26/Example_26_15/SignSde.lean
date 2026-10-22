/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_21.Integral
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_12

open Filter
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

private abbrev TimeFiltration (Ω : Type u) [MeasurableSpace Ω] :=
  Filtration NNReal (inferInstance : MeasurableSpace Ω)

private abbrev RealProcess (Ω : Type u) :=
  NNReal → Ω → ℝ

/-- Helper for Example 26.15: the initial state `X₀ = 0` as a one-dimensional vector. -/
def signSdeInitialState : Fin 1 → ℝ :=
  fun _ ↦ 0

/-- Helper for Example 26.15: the sign SDE is considered with initial law `δ₀`. -/
def signSdeInitialLaw : Measure (Fin 1 → ℝ) :=
  Measure.dirac signSdeInitialState

instance signSdeInitialLaw_isProbabilityMeasure :
    IsProbabilityMeasure signSdeInitialLaw := by
  change IsProbabilityMeasure (Measure.dirac signSdeInitialState)
  refine ⟨by simp⟩

/-- Helper for Example 26.15: the scalar coordinate process carried by a one-dimensional state
path. -/
def signSdeStateProcess {Ω : Type u}
    (X : Ω → EuclideanPathSpace 1) : NNReal → Ω → ℝ :=
  fun t ω ↦ X ω t 0

/-- Helper for Example 26.15: the scalar coordinate of the one-dimensional Brownian driver. -/
def signSdeDriverProcess {Ω : Type u}
    (W : NNReal → Ω → Fin 1 → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ W t ω 0

/-- Helper for Example 26.15: the coefficient process `sign (X_t)` appearing in equations
`(26.18)` and `(26.19)`. -/
def signSdeIntegrand {Ω : Type u}
    (X : Ω → EuclideanPathSpace 1) : NNReal → Ω → ℝ :=
  fun t ω ↦ Real.sign (X ω t 0)

/-- Helper for Example 26.15: the source equation `(26.18)`,
`X_t = X₀ + ∫₀ᵗ sign (X_s) dW_s`. -/
def signSdeSolvesSDE
    {Ω : Type u} [MeasurableSpace Ω]
    (ℱ : TimeFiltration Ω)
    (μ : Measure Ω)
    (X : Ω → EuclideanPathSpace 1)
    (W : NNReal → Ω → Fin 1 → ℝ) : Prop :=
  ∃ hW : IsContinuousLocalMartingale ℱ μ (signSdeDriverProcess W),
    ∀ t ω,
      signSdeStateProcess X t ω =
        signSdeStateProcess X 0 ω +
          continuousLocalMartingaleItoIntegralProcess hW (signSdeIntegrand X) t ω

/-- Helper for Example 26.15: the source equation `(26.19)`,
`W_t = ∫₀ᵗ sign (X_s) dX_s`, on a Brownian sign-SDE setup. -/
def signSdeReverseEquation
    {Ω : Type u} [MeasurableSpace Ω]
    (ℱ : TimeFiltration Ω)
    (μ : Measure Ω)
    (X : Ω → EuclideanPathSpace 1)
    (W : NNReal → Ω → Fin 1 → ℝ) : Prop :=
  ∃ hX : IsContinuousLocalMartingale ℱ μ (signSdeStateProcess X),
    ∀ t ω,
      signSdeDriverProcess W t ω =
        continuousLocalMartingaleItoIntegralProcess hX (signSdeIntegrand X) t ω

/-- Helper for Example 26.15: a Brownian sign-SDE setup carries the state path together with the
driving Brownian motion from the weak-solution data. This is the thin owner on which `(26.18)`
and `(26.19)` become independent surfaces. -/
structure SignSdeBrownianPair where
  Ω : Type u
  instMeasurableSpace : MeasurableSpace Ω
  μ : Measure Ω
  instIsProbabilityMeasure : IsProbabilityMeasure μ
  ℱ : TimeFiltration Ω
  instUsualConditions : Filtration.UsualConditions ℱ μ
  X : Ω → EuclideanPathSpace 1
  W : NNReal → Ω → Fin 1 → ℝ
  driver_brownian :
    IsStandardBrownianMotionVector μ (CoordinateProcess.toEuclidean W) ∧ Adapted ℱ W

attribute [instance] SignSdeBrownianPair.instMeasurableSpace
attribute [instance] SignSdeBrownianPair.instIsProbabilityMeasure
attribute [instance] SignSdeBrownianPair.instUsualConditions

/-- Helper for Example 26.15: equation `(26.18)` on the Brownian sign-SDE surface. -/
def signSdeForwardIdentity (S : SignSdeBrownianPair) : Prop :=
  signSdeSolvesSDE S.ℱ S.μ S.X S.W

/-- Helper for Example 26.15: equation `(26.19)` on the Brownian sign-SDE surface. -/
def signSdeReverseIdentity (S : SignSdeBrownianPair) : Prop :=
  signSdeReverseEquation S.ℱ S.μ S.X S.W

/-- Helper for Example 26.15: the state process is Brownian, the property used internally in the
source argument for `(26.18) ↔ (26.19)` and for the later non-adaptedness conclusion. -/
def signSdeStateIsBrownian (S : SignSdeBrownianPair) : Prop :=
  IsBrownianMotion S.μ (signSdeStateProcess S.X)

/-- Helper for Example 26.15: a weak solution of the one-dimensional sign SDE with initial law
`δ₀`. This is the ordinary Chapter 26 weak-solution surface, specialized to the sign coefficient.
-/
abbrev SignSdeWeakSolution :=
  WeakSDESolution 1 1 signSdeInitialLaw signSdeSolvesSDE

/-- Helper for Example 26.15: forget a sign-SDE weak solution down to the thinner Brownian
sign-SDE setup used for the `(26.18)`/`(26.19)` equivalence. -/
abbrev SignSdeWeakSolution.toBrownianPair (L : SignSdeWeakSolution) : SignSdeBrownianPair where
  Ω := L.Ω
  instMeasurableSpace := L.instMeasurableSpace
  μ := L.μ
  instIsProbabilityMeasure := L.instIsProbabilityMeasure
  ℱ := L.ℱ
  instUsualConditions := L.instUsualConditions
  X := L.X
  W := L.W
  driver_brownian := L.brownian

/-- Helper for Example 26.15: the forward identity `(26.18)` on the repaired weak-solution
surface. -/
def signSdeWeakForwardIdentity (L : SignSdeWeakSolution) : Prop :=
  signSdeForwardIdentity L.toBrownianPair

/-- Helper for Example 26.15: the reverse identity `(26.19)` on the repaired weak-solution
surface. -/
def signSdeWeakReverseIdentity (L : SignSdeWeakSolution) : Prop :=
  signSdeReverseIdentity L.toBrownianPair

/-- Helper for Example 26.15: the Brownianity of the state process appearing later in the source
discussion is a property of a weak solution, not part of its defining data. -/
def signSdeWeakStateIsBrownian (L : SignSdeWeakSolution) : Prop :=
  signSdeStateIsBrownian L.toBrownianPair

end ProbabilityTheory
