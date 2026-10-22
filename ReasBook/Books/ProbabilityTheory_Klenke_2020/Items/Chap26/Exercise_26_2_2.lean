/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Example_26_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped Topology

noncomputable section

namespace ProbabilityTheory

local notation "State1" => Fin 1 → ℝ
local notation "State2" => Fin 2 → ℝ
local notation "StatePathSpace1" => EuclideanPathSpace 1
local notation "StatePathSpace2" => EuclideanPathSpace 2
local notation "DiffusionCoeff2" => NNReal → State2 → Fin 2 → Fin 2 → ℝ
local notation "DriftCoeff2" => NNReal → State2 → Fin 2 → ℝ

/-- Helper for Exercise 26.2.2: a weak-solution realization of an `n`-dimensional SDE consists of
progressively measurable continuous coordinates together with the ambient noise condition and the
chosen SDE-solving relation. -/
def HasWeakSolutionRealization
    {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (NoiseCondition : (NNReal → Ω → Fin m → ℝ) → Prop)
    (SolvesSDE :
      (Ω → Fin n → ℝ) → (NNReal → Ω → Fin m → ℝ) → (NNReal → Ω → Fin n → ℝ) → Prop)
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Ω → Fin n → ℝ) (W : NNReal → Ω → Fin m → ℝ) (X : NNReal → Ω → Fin n → ℝ) : Prop :=
  (∀ i : Fin n, ProgMeasurable ℱ (fun t ω ↦ X t ω i)) ∧
    (∀ i : Fin n, ∀ ω : Ω, Continuous fun t ↦ X t ω i) ∧
      NoiseCondition W ∧
      SolvesSDE ξ W X

/-- Helper for Exercise 26.2.2: a scalar process `I` is a Brownian local Itô integral of `H`
against `W` when it carries the standard local square-integrability, continuity, and martingale
structure. -/
class IsBrownianLocalItoIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (W H I : NNReal → Ω → ℝ) : Prop where
  locally_square_integrable : IsLocallySquareIntegrableProcess ℱ μ H
  brownian_motion : IsBrownianMotion μ W
  zero : I 0 = 0
  continuous_paths : HasAlmostSurelyContinuousPaths μ I
  martingale : Martingale I ℱ μ

/-- Helper for Exercise 26.2.2: the vector-valued Brownian Itô term is represented coordinatewise
by scalar Brownian local Itô integrals. -/
def IsMatrixBrownianLocalItoIntegral
    {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (W : NNReal → Ω → Fin m → ℝ)
    (H : NNReal → Ω → Fin n → Fin m → ℝ)
    (N : NNReal → Ω → Fin n → ℝ) : Prop :=
  ∃ Nij : Fin n → Fin m → NNReal → Ω → ℝ,
    (∀ i : Fin n, ∀ j : Fin m,
      IsBrownianLocalItoIntegral ℱ μ (fun t ω ↦ W t ω j) (fun t ω ↦ H t ω i j) (Nij i j)) ∧
      ∀ t : NNReal, ∀ ω : Ω, ∀ i : Fin n, N t ω i = ∑ j : Fin m, Nij i j t ω

/-- Helper for Exercise 26.2.2: an `m`-dimensional Brownian process with filtration `ℱ` is a
standard vector Brownian motion adapted to `ℱ`. -/
def IsBrownianMotionWithFiltration
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (W : NNReal → Ω → Fin m → ℝ) : Prop :=
  IsStandardBrownianMotionVector μ W.toEuclidean ∧
    Adapted ℱ W

/-- Helper for Exercise 26.2.2: evaluate a path-valued random variable at time `t`. -/
abbrev pathProcess {Ω : Type*} {d : ℕ} (Y : Ω → EuclideanPathSpace d) :
    NNReal → Ω → Fin d → ℝ :=
  fun t ω ↦ Y ω t

/-- Helper for Exercise 26.2.2: the path-valued Brownian-driver condition used in the stored
strong-solution data. -/
abbrev GeneralizedSDEBrownianMotion
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω)
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (W : Ω → EuclideanPathSpace m) : Prop :=
  ∃ _ : IsProbabilityMeasure P,
    IsBrownianMotionWithFiltration ℱ P (pathProcess W)

/-- Helper for Exercise 26.2.2: a generalized `n`-dimensional diffusion with initial datum `ξ`
is driven by an adapted `m`-dimensional Brownian motion and admits the standard Itô
decomposition. -/
def IsGeneralizedNDimensionalDiffusion
    {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (ξ : Ω → Fin n → ℝ) (W : NNReal → Ω → Fin m → ℝ)
    (σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ)
    (b : NNReal → (Fin n → ℝ) → Fin n → ℝ)
    (X : NNReal → Ω → Fin n → ℝ) : Prop :=
  IsBrownianMotionWithFiltration ℱ μ W ∧
    ∃ N : NNReal → Ω → Fin n → ℝ,
      IsMatrixBrownianLocalItoIntegral
        ℱ
        μ
        W
        (fun t ω i j ↦ σ t (X t ω) i j)
        N ∧
      (∀ i, ProgMeasurable ℱ (fun t ω ↦ b t (X t ω) i)) ∧
      (∀ i T, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦ |b s.toNNReal (X s.toNNReal ω) i|)
          (Set.Icc (0 : ℝ) (T : ℝ))) ∧
      X =
        fun t ω i ↦
          ξ ω i +
            N t ω i +
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (X s.toNNReal ω) i

/-- Helper for Exercise 26.2.2: the path-valued strong-solution relation attached to the
coefficients `(σ, b)`. -/
def SolvesStrongGeneralizedSDE
    {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ)
    (b : NNReal → (Fin n → ℝ) → Fin n → ℝ)
    (P : Measure Ω)
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Ω → Fin n → ℝ) (W : Ω → EuclideanPathSpace m) (X : Ω → EuclideanPathSpace n) : Prop :=
  ∃ _ : IsProbabilityMeasure P,
    IsGeneralizedNDimensionalDiffusion ℱ P ξ (pathProcess W) σ b (pathProcess X)

/-- Helper for Exercise 26.2.2: a two-dimensional generalized weak solution stores the filtered
probability space, the path-valued state process, the Brownian driver, and the corresponding
strong-solution data on the same space. -/
structure GeneralizedWeakSDESolution {n m : ℕ}
    (μ₀ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ₀]
    (σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ)
    (b : NNReal → (Fin n → ℝ) → Fin n → ℝ) where
  Ω : Type _
  instMeasurableSpace : MeasurableSpace Ω
  μ : Measure Ω
  instIsProbabilityMeasure : IsProbabilityMeasure μ
  ℱ : Filtration NNReal instMeasurableSpace
  instUsualConditions : Filtration.UsualConditions ℱ μ
  X : Ω → EuclideanPathSpace n
  W : NNReal → Ω → Fin m → ℝ
  brownian : IsStandardBrownianMotionVector μ W.toEuclidean ∧ Adapted ℱ W
  adapted : Adapted ℱ (fun t ω ↦ X ω t)
  initialLaw : HasLaw (fun ω ↦ X ω 0) μ₀ μ
  ξ : Ω → Fin n → ℝ
  Wpath : Ω → EuclideanPathSpace m
  w_eq : W = pathProcess Wpath
  initial_state_eq : (fun ω ↦ X ω 0) =ᵐ[μ] ξ
  initial_data_measurable : Measurable[ℱ 0] ξ
  independent_initial_brownian : IndepFun ξ Wpath μ
  brownian_path : GeneralizedSDEBrownianMotion μ ℱ Wpath
  solves_strong_sde : SolvesStrongGeneralizedSDE σ b μ ℱ ξ Wpath X

attribute [instance] GeneralizedWeakSDESolution.instMeasurableSpace
attribute [instance] GeneralizedWeakSDESolution.instIsProbabilityMeasure
attribute [instance] GeneralizedWeakSDESolution.instUsualConditions

/-- Helper for Exercise 26.2.2: a generalized weak solution is callable as its state-path random
variable. -/
instance generalizedWeakSDESolutionCoeFun
    {n m : ℕ} {μ₀ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ₀]
    {σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ}
    {b : NNReal → (Fin n → ℝ) → Fin n → ℝ} :
    CoeFun (GeneralizedWeakSDESolution μ₀ σ b) (fun L ↦ L.Ω → EuclideanPathSpace n) where
  coe := GeneralizedWeakSDESolution.X

/-- Helper for Exercise 26.2.2: unpacking the stored strong-solution data recovers the
generalized diffusion relation for the time-indexed state process driven by `L.W`. -/
theorem GeneralizedWeakSDESolution.solvesGeneralizedDiffusion
    {n m : ℕ} {μ₀ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ₀]
    {σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ}
    {b : NNReal → (Fin n → ℝ) → Fin n → ℝ}
    (L : GeneralizedWeakSDESolution μ₀ σ b) :
    IsGeneralizedNDimensionalDiffusion L.ℱ L.μ L.ξ L.W σ b (fun t ω ↦ L ω t) := by
  rcases L.solves_strong_sde with ⟨_, hDiffusion⟩
  simpa [pathProcess, L.w_eq] using hDiffusion

/-- Helper for Exercise 26.2.2: every stored strong solution path starts from the prescribed
initial datum at time `0`. -/
theorem GeneralizedWeakSDESolution.initialState_eq
    {n m : ℕ} {μ₀ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ₀]
    {σ : NNReal → (Fin n → ℝ) → Fin n → Fin m → ℝ}
    {b : NNReal → (Fin n → ℝ) → Fin n → ℝ}
    (L : GeneralizedWeakSDESolution μ₀ σ b) :
    ∀ ω : L.Ω, L ω 0 = L.ξ ω := by
  rcases L.solves_strong_sde with ⟨_, hDiffusion⟩
  rcases hDiffusion with ⟨_, N, hIto, _, _, hStateEq⟩
  intro ω
  ext i
  rcases hIto with ⟨Nij, hNij, hNsum⟩
  have hNzero : N 0 ω i = 0 := by
    rw [hNsum 0 ω i]
    have hZero : ∀ j : Fin m, Nij i j 0 ω = 0 := by
      intro j
      simpa using congrFun ((hNij i j).zero) ω
    simp [hZero]
  have hEq0 := congrFun (congrFun (congrFun hStateEq 0) ω) i
  -- Proof comment: at time `0`, both the Itô term and the drift integral vanish, so the
  -- strong integral equation collapses to `X₀ = ξ`.
  simpa [pathProcess, hNzero] using hEq0

/- Domain-style sampling for Exercise 26.2.2:
- primary domain: weak solutions and same-space weak realizations of Chapter 26 SDEs;
- sampled chapter owners: `cirDiffusionCoeff`, `cirDriftCoeff`, `oneDimensionalState`,
  `oneDimensionalDiffusion`, `oneDimensionalDrift`, `HasWeakSolutionRealization`, and
  `GeneralizedWeakSDESolution`;
- core/canonical owner choice: the summed one-dimensional equation is the chapter's CIR / Feller
  branching diffusion with coefficient `cirDiffusionCoeff γ` and drift `cirDriftCoeff 0 0`,
  expressed through the existing one-dimensional coefficient lifts and realization predicates;
- source-facing data kept here: the genuinely two-dimensional diagonal coefficient, deterministic
  pair initial state, and the state-sum map;
- deleted duplicate local owner layer: the previous one-dimensional square-root coefficient and
  drift wrappers, the independence alias, and the packaged
  `SummedSquareRootWeakSolution` wrapper.
-/

/-- The diagonal two-dimensional square-root diffusion coefficient with independent coordinates,
written as a coordinatewise bridge to the chapter's one-dimensional CIR / Feller branching
coefficient. -/
abbrev squareRootPairDiffusionCoeff (γ : NNReal) : DiffusionCoeff2 :=
  fun t x i j ↦ if i = j then cirDiffusionCoeff γ t (x i) else 0

-- Proof sketch: unfold `squareRootPairDiffusionCoeff`; the coefficient is diagonal, with
-- diagonal entry the chapter's CIR coefficient `cirDiffusionCoeff γ t (xᵢ)` and off-diagonal
-- entry `0`.
/-- Evaluating the two-dimensional square-root diffusion coefficient gives the diagonal formula
with coordinatewise CIR entries and vanishing off-diagonal terms. -/
theorem squareRootPairDiffusionCoeff_apply
    (γ : NNReal) (t : NNReal) (x : State2) (i j : Fin 2) :
    squareRootPairDiffusionCoeff γ t x i j =
      if i = j then cirDiffusionCoeff γ t (x i) else 0 := rfl

/-- The zero drift coefficient for the two-dimensional square-root diffusion, written
coordinatewise through the chapter's zero-CIR drift owner. -/
abbrev squareRootDrift2 : DriftCoeff2 :=
  fun t x i ↦ cirDriftCoeff 0 0 t (x i)

-- Proof sketch: unfold `squareRootDrift2`; each coordinate is the zero CIR drift
-- `cirDriftCoeff 0 0`.
/-- Evaluating the two-dimensional drift coefficient recovers the coordinatewise zero CIR drift. -/
theorem squareRootDrift2_apply
    (t : NNReal) (x : State2) (i : Fin 2) :
    squareRootDrift2 t x i = cirDriftCoeff 0 0 t (x i) := rfl

/-- The deterministic initial state `(x₀¹, x₀²)` in `ℝ²`. -/
abbrev squareRootPairInitialState (x01 x02 : ℝ) : State2 :=
  ![x01, x02]

-- Proof sketch: unfold `squareRootPairInitialState`; the first coordinate is the first component
-- of the vector notation `![x₀¹, x₀²]`.
/-- The first coordinate of the initial state is `x₀¹`. -/
theorem squareRootPairInitialState_apply_zero
    (x01 x02 : ℝ) :
    squareRootPairInitialState x01 x02 0 = x01 := by
  simp [squareRootPairInitialState]

-- Proof sketch: unfold `squareRootPairInitialState`; the second coordinate is the second
-- component of the vector notation `![x₀¹, x₀²]`.
/-- The second coordinate of the initial state is `x₀²`. -/
theorem squareRootPairInitialState_apply_one
    (x01 x02 : ℝ) :
    squareRootPairInitialState x01 x02 1 = x02 := by
  simp [squareRootPairInitialState]

-- Proof sketch: the map `x ↦ x 0 + x 1` is continuous as a sum of the two continuous coordinate
-- projections, and viewing this scalar as a `Fin 1 → ℝ`-valued function preserves continuity.
/-- The state map `x ↦ x₁ + x₂` from `ℝ²` to `ℝ` is continuous in the `Fin`-indexed model. -/
theorem sumTwoCoordinateState_continuous :
    Continuous (fun x : State2 ↦ fun _ : Fin 1 ↦ x 0 + x 1) := by
  continuity

/-- The continuous state map sending `(x₁, x₂)` to the one-dimensional state `x₁ + x₂`. -/
def sumTwoCoordinateStateMap : ContinuousMap State2 State1 :=
  ⟨fun x _ ↦ x 0 + x 1, sumTwoCoordinateState_continuous⟩

-- Proof sketch: unfold `sumTwoCoordinateStateMap`; it is the continuous map built from the
-- function `x ↦ x₁ + x₂`.
/-- Evaluating the state-sum map returns the one-dimensional state with value `x₁ + x₂`. -/
theorem sumTwoCoordinateStateMap_apply
    (x : State2) (i : Fin 1) :
    sumTwoCoordinateStateMap x i = x 0 + x 1 := rfl

/-- Summing the two coordinates of a two-dimensional continuous path gives a one-dimensional
continuous path. -/
def sumTwoCoordinatePath (x : StatePathSpace2) : StatePathSpace1 :=
  sumTwoCoordinateStateMap.comp x

-- Proof sketch: `sumTwoCoordinatePath` is defined by composing the path `x` with
-- `sumTwoCoordinateStateMap`, so evaluation at time `t` gives the sum of the two coordinates of
-- `x t`.
/-- Evaluating the summed path at time `t` gives `x_t¹ + x_t²`. -/
theorem sumTwoCoordinatePath_apply
    (x : StatePathSpace2) (t : NNReal) (i : Fin 1) :
    sumTwoCoordinatePath x t i = x t 0 + x t 1 := rfl

/-- Bridge/view: the scalar state `x` as the chapter's one-dimensional `Fin 1 → ℝ` state. -/
abbrev oneDimensionalState (x : ℝ) : State1 :=
  fun _ ↦ x

/-- Evaluating `oneDimensionalState x` at its unique coordinate recovers `x`. -/
theorem oneDimensionalState_apply (x : ℝ) (i : Fin 1) :
    oneDimensionalState x i = x := rfl

/-- Bridge/view: a scalar process as the chapter's one-dimensional state process. -/
abbrev oneDimensionalProcess {Ω : Type*} (X : NNReal → Ω → ℝ) :
    NNReal → Ω → State1 :=
  fun t ω ↦ oneDimensionalState (X t ω)

/-- The drift coefficient `b(t, x)` of a one-dimensional SDE, viewed as a `Fin 1`-valued drift
field on `ℝ¹`. -/
abbrev oneDimensionalDrift (b : NNReal → ℝ → ℝ) :
    NNReal → State1 → Fin 1 → ℝ :=
  fun t x _ ↦ b t (x 0)

/-- Evaluating the lifted one-dimensional drift field recovers the scalar drift coefficient. -/
theorem oneDimensionalDrift_apply
    (b : NNReal → ℝ → ℝ) (t : NNReal) (x : State1) (i : Fin 1) :
    oneDimensionalDrift b t x i = b t (x 0) := rfl

/-- The diffusion coefficient `σ(t, x)` of a one-dimensional SDE, viewed as a `1 × 1` diffusion
matrix field on `ℝ¹`. -/
abbrev oneDimensionalDiffusion (σ : NNReal → ℝ → ℝ) :
    NNReal → State1 → Fin 1 → Fin 1 → ℝ :=
  fun t x _ _ ↦ σ t (x 0)

/-- Evaluating the lifted one-dimensional diffusion matrix recovers the scalar diffusion
coefficient. -/
theorem oneDimensionalDiffusion_apply
    (σ : NNReal → ℝ → ℝ) (t : NNReal) (x : State1) (i j : Fin 1) :
    oneDimensionalDiffusion σ t x i j = σ t (x 0) := rfl

/-- Helper for Exercise 26.2.2: pushing the time-zero law of the two-dimensional solution
through `sumTwoCoordinateStateMap` gives the Dirac law at `x₀¹ + x₀²`. -/
lemma sumTwoCoordinateInitialLaw
    {x01 x02 : ℝ} {γ : NNReal}
    (L : GeneralizedWeakSDESolution
      (Measure.dirac (squareRootPairInitialState x01 x02))
      (squareRootPairDiffusionCoeff γ) squareRootDrift2) :
    HasLaw (fun ω ↦ sumTwoCoordinatePath (L ω) 0)
      (Measure.dirac (oneDimensionalState (x01 + x02))) L.μ := by
  have hSumStateLaw :
      HasLaw sumTwoCoordinateStateMap
        (Measure.dirac (oneDimensionalState (x01 + x02)))
        (Measure.dirac (squareRootPairInitialState x01 x02)) := by
    have hPoint :
        sumTwoCoordinateStateMap (squareRootPairInitialState x01 x02) =
          oneDimensionalState (x01 + x02) := by
      ext i
      fin_cases i
      simp [sumTwoCoordinateStateMap_apply, oneDimensionalState]
    -- Proof comment: the sum map is continuous, and at the deterministic initial state it returns
    -- the one-dimensional state `x₀¹ + x₀²`.
    refine ⟨sumTwoCoordinateStateMap.continuous.measurable.aemeasurable, ?_⟩
    rw [Measure.map_dirac]
    simp [hPoint]
  -- Proof comment: composing the time-zero state law with the sum state map gives the law of the
  -- summed path at time `0`.
  simpa [sumTwoCoordinatePath] using HasLaw.fun_comp hSumStateLaw L.initialLaw

/-- Helper for Exercise 26.2.2: the first coordinate of the two-dimensional Brownian driver is a
one-dimensional Brownian motion with the ambient filtration. -/
lemma firstDriverCoordinate_isBrownianWithFiltration
    {x01 x02 : ℝ} {γ : NNReal}
    (L : GeneralizedWeakSDESolution
      (Measure.dirac (squareRootPairInitialState x01 x02))
      (squareRootPairDiffusionCoeff γ) squareRootDrift2) :
    IsBrownianMotionWithFiltration L.ℱ L.μ
      (oneDimensionalProcess (fun t ω ↦ L.W t ω 0)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      -- Proof comment: the only coordinate of the lifted one-dimensional driver is the chosen
      -- scalar Brownian coordinate.
      letI : IsStandardBrownianMotionVector L.μ L.W.toEuclidean :=
        L.brownian.1
      simpa [oneDimensionalProcess, oneDimensionalState, Function.toEuclidean] using
        (inferInstance : IsBrownianMotion L.μ (fun t ω ↦ (L.W.toEuclidean t ω) 0))
    · -- Proof comment: independence for a singleton coordinate family is automatic.
      exact iIndepFun.of_subsingleton
  · intro t
    -- Proof comment: the lifted one-dimensional driver is adapted because its unique coordinate is
    -- the adapted first coordinate of the original vector driver.
    have hone : Measurable (fun x : Fin 2 → ℝ ↦ oneDimensionalState (x 0)) := by
      refine measurable_pi_lambda _ fun i : Fin 1 ↦ ?_
      fin_cases i
      exact measurable_pi_apply 0
    change Measurable[L.ℱ t]
      (((fun x : Fin 2 → ℝ ↦ oneDimensionalState (x 0)) ∘ fun ω : L.Ω ↦ L.W t ω))
    exact hone.comp (L.brownian.2 t)

-- Proof sketch: regard `(X¹, X²)` as a two-dimensional weak solution with diagonal diffusion
-- coefficient. The summed path `Z = X¹ + X²` is adapted and
-- starts from `x₀¹ + x₀²`. Its quadratic variation is `γ ∫ Z_s ds`, so by Lévy's characterization
-- or the martingale representation used in Theorem 26.26, there exists a one-dimensional
-- Brownian motion `W` on the same filtered probability space such that
-- `dZ_t = √(γ Z_t) dW_t`.
/-- Exercise 26.2.2: if `(X¹, X²)` is a two-dimensional weak solution of the diagonal square-root
diffusion with initial state `(x₀¹, x₀²)`, then the summed process `Z := X¹ + X²` is a weak
solution of the one-dimensional square-root SDE with initial value `x₀¹ + x₀²`. -/
theorem squareRoot_diffusion_sum_isWeakSolution
    {x01 x02 : ℝ} {γ : NNReal}
    (L : GeneralizedWeakSDESolution
      (Measure.dirac (squareRootPairInitialState x01 x02))
      (squareRootPairDiffusionCoeff γ) squareRootDrift2) :
    ∃ W : NNReal → L.Ω → Fin 1 → ℝ,
      HasLaw (fun ω ↦ sumTwoCoordinatePath (L ω) 0)
        (Measure.dirac (oneDimensionalState (x01 + x02))) L.μ ∧
      HasWeakSolutionRealization
        (IsBrownianMotionWithFiltration L.ℱ L.μ)
        (fun ξ W X ↦
          IsGeneralizedNDimensionalDiffusion L.ℱ L.μ ξ W
            (oneDimensionalDiffusion (cirDiffusionCoeff γ))
            (oneDimensionalDrift (cirDriftCoeff 0 0))
            X)
        L.ℱ
        (fun ω ↦ sumTwoCoordinatePath (L ω) 0)
        W
        (fun t ω ↦ sumTwoCoordinatePath (L ω) t) := by
  let Wsum : NNReal → L.Ω → Fin 1 → ℝ :=
    oneDimensionalProcess (fun t ω ↦ L.W t ω 0)
  -- Proof comment: the first conjunct is just the time-zero law pushed through the sum map.
  refine ⟨Wsum, sumTwoCoordinateInitialLaw L, ?_⟩
  refine ⟨?_, ?_, firstDriverCoordinate_isBrownianWithFiltration L, ?_⟩
  · intro i
    fin_cases i
    have hSumAdapted : Adapted L.ℱ (fun t ω ↦ sumTwoCoordinatePath (L ω) t 0) := by
      intro t
      have hCoord0 :
          Measurable[L.ℱ t] (fun ω ↦ L ω t 0) := by
        change Measurable[L.ℱ t] ((fun x : Fin 2 → ℝ ↦ x 0) ∘ fun ω ↦ L ω t)
        exact (measurable_pi_apply 0).comp (L.adapted t)
      have hCoord1 :
          Measurable[L.ℱ t] (fun ω ↦ L ω t 1) := by
        change Measurable[L.ℱ t] ((fun x : Fin 2 → ℝ ↦ x 1) ∘ fun ω ↦ L ω t)
        exact (measurable_pi_apply 1).comp (L.adapted t)
      -- Proof comment: the summed state coordinate is the sum of the two adapted coordinates.
      simpa [sumTwoCoordinatePath_apply] using hCoord0.add hCoord1
    have hSumCont : ∀ ω : L.Ω, Continuous (fun t ↦ sumTwoCoordinatePath (L ω) t 0) := by
      intro ω
      -- Proof comment: the summed path is a continuous path in `ℝ¹`, so its unique coordinate is
      -- continuous in time.
      simpa using (continuous_apply 0).comp (sumTwoCoordinatePath (L ω)).continuous
    exact hSumAdapted.stronglyAdapted.progMeasurable_of_continuous hSumCont
  · intro i ω
    fin_cases i
    -- Proof comment: evaluating the continuous one-dimensional summed path at its unique
    -- coordinate gives a continuous scalar trajectory.
    simpa using (continuous_apply 0).comp (sumTwoCoordinatePath (L ω)).continuous
  · rcases L.solvesGeneralizedDiffusion with ⟨_, N, hIto, _, _, hStateEq⟩
    rcases hIto with ⟨Nij, hNij, hNsum⟩
    let scalarIto : NNReal → L.Ω → ℝ :=
      fun t ω ↦ Nij 0 0 t ω + Nij 0 1 t ω + Nij 1 0 t ω + Nij 1 1 t ω
    let summedMartingalePart : NNReal → L.Ω → Fin 1 → ℝ :=
      oneDimensionalProcess scalarIto
    have hSumStateAdapted : Adapted L.ℱ (fun t ω ↦ sumTwoCoordinatePath (L ω) t 0) := by
      intro t
      have hCoord0 :
          Measurable[L.ℱ t] (fun ω ↦ L ω t 0) := by
        change Measurable[L.ℱ t] ((fun x : Fin 2 → ℝ ↦ x 0) ∘ fun ω ↦ L ω t)
        exact (measurable_pi_apply 0).comp (L.adapted t)
      have hCoord1 :
          Measurable[L.ℱ t] (fun ω ↦ L ω t 1) := by
        change Measurable[L.ℱ t] ((fun x : Fin 2 → ℝ ↦ x 1) ∘ fun ω ↦ L ω t)
        exact (measurable_pi_apply 1).comp (L.adapted t)
      simpa [sumTwoCoordinatePath_apply] using hCoord0.add hCoord1
    have hSumStateCont : ∀ ω : L.Ω, Continuous (fun t ↦ sumTwoCoordinatePath (L ω) t 0) := by
      intro ω
      simpa using (continuous_apply 0).comp (sumTwoCoordinatePath (L ω)).continuous
    have hCirContinuous : Continuous (fun x : ℝ ↦ Real.sqrt ((γ : ℝ) * realPosPart x)) := by
      -- Proof comment: the CIR coefficient is continuous because it is `sqrt` composed with the
      -- nonnegative continuous function `x ↦ γ * x⁺`.
      simpa only [realPosPart_eq_max] using
        (Real.continuous_sqrt.comp
          ((continuous_const.mul (continuous_id.max continuous_const))))
    have hDiffusionLocal :
        IsLocallySquareIntegrableProcess L.ℱ L.μ
          (fun t ω ↦ cirDiffusionCoeff γ t (sumTwoCoordinatePath (L ω) t 0)) := by
      constructor
      · have hCoeffAdapted :
            Adapted L.ℱ
              (fun t ω ↦ cirDiffusionCoeff γ t (sumTwoCoordinatePath (L ω) t 0)) := by
          intro t
          -- Proof comment: at each time, the scalar CIR coefficient is a measurable function of
          -- the adapted summed state coordinate.
          simpa [cirDiffusionCoeff_apply] using
            hCirContinuous.measurable.comp (hSumStateAdapted t)
        have hCoeffCont :
            ∀ ω : L.Ω,
              Continuous (fun t ↦ cirDiffusionCoeff γ t (sumTwoCoordinatePath (L ω) t 0)) := by
          intro ω
          -- Proof comment: the coefficient process is the continuous scalar CIR map applied to the
          -- continuous summed state path.
          simpa [cirDiffusionCoeff_apply] using hCirContinuous.comp (hSumStateCont ω)
        exact hCoeffAdapted.stronglyAdapted.progMeasurable_of_continuous hCoeffCont
      · intro T
        filter_upwards with ω
        have hCoeffContReal :
            Continuous
              (fun s : ℝ ↦
                cirDiffusionCoeff γ s.toNNReal
                  (sumTwoCoordinatePath (L ω) s.toNNReal 0)) := by
          -- Proof comment: on each sample path the scalar coefficient stays continuous after
          -- pulling the `NNReal`-time path back to the real interval `[0, T]`.
          simpa [cirDiffusionCoeff_apply] using
            hCirContinuous.comp ((hSumStateCont ω).comp continuous_real_toNNReal)
        exact (hCoeffContReal.pow 2).integrableOn_Icc
    have hScalarItoCont :
        HasAlmostSurelyContinuousPaths L.μ scalarIto := by
      filter_upwards [(hNij 0 0).continuous_paths, (hNij 0 1).continuous_paths,
        (hNij 1 0).continuous_paths, (hNij 1 1).continuous_paths] with ω h00 h01 h10 h11
      -- Proof comment: the summed martingale part is a finite sum of continuous scalar paths.
      simpa [HasAlmostSurelyContinuousPaths, processPath, scalarIto] using
        ((h00.add h01).add h10).add h11
    have hScalarItoIsBrownianLocal :
        IsBrownianLocalItoIntegral
          L.ℱ
          L.μ
          (fun t ω ↦ L.W t ω 0)
          (fun t ω ↦ cirDiffusionCoeff γ t (sumTwoCoordinatePath (L ω) t 0))
          scalarIto := by
      refine
        { locally_square_integrable := hDiffusionLocal
          brownian_motion := by
            letI : IsStandardBrownianMotionVector L.μ L.W.toEuclidean :=
              L.brownian.1
            simpa [Function.toEuclidean] using
              (inferInstance : IsBrownianMotion L.μ (fun t ω ↦ (L.W.toEuclidean t ω) 0))
          zero := ?_
          continuous_paths := hScalarItoCont
          martingale := ?_ }
      · ext ω
        -- Proof comment: each scalar Itô component starts from `0`, so their finite sum does too.
        simp [scalarIto, (hNij 0 0).zero, (hNij 0 1).zero, (hNij 1 0).zero, (hNij 1 1).zero]
      · -- Proof comment: finite sums of martingales remain martingales.
        exact
          (((hNij 0 0).martingale.add (hNij 0 1).martingale).add
            (hNij 1 0).martingale).add
            (hNij 1 1).martingale
    have hInitialState :
        ∀ ω : L.Ω, L ω 0 = L.ξ ω := L.initialState_eq
    refine ⟨firstDriverCoordinate_isBrownianWithFiltration L, ?_⟩
    refine ⟨summedMartingalePart, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨fun _ _ ↦ scalarIto, ?_, ?_⟩
      · intro i j
        fin_cases i
        fin_cases j
        -- Proof comment: the one-dimensional matrix-Itô owner has just one scalar component,
        -- namely the summed martingale witness constructed above.
        simpa using hScalarItoIsBrownianLocal
      · intro t ω i
        fin_cases i
        simp [summedMartingalePart, scalarIto]
    · intro i
      fin_cases i
      -- Proof comment: the target drift is identically zero.
      simpa [cirDriftCoeff_apply] using
        progMeasurable_const L.ℱ (0 : ℝ)
    · intro i T
      fin_cases i
      -- Proof comment: the zero drift has trivial absolute-value integral on every finite
      -- interval.
      filter_upwards with ω
      simp [cirDriftCoeff_apply]
    · ext t ω i
      fin_cases i
      have hState0 :
          L ω t 0 = L.ξ ω 0 + N t ω 0 := by
        -- Proof comment: each original coordinate solves the zero-drift generalized diffusion.
        simpa [squareRootDrift2_apply, cirDriftCoeff_apply] using
          congrFun (congrFun (congrFun hStateEq t) ω) 0
      have hState1 :
          L ω t 1 = L.ξ ω 1 + N t ω 1 := by
        simpa [squareRootDrift2_apply, cirDriftCoeff_apply] using
          congrFun (congrFun (congrFun hStateEq t) ω) 1
      have hInit0 : L ω 0 0 = L.ξ ω 0 := by
        simpa using congrFun (hInitialState ω) 0
      have hInit1 : L ω 0 1 = L.ξ ω 1 := by
        simpa using congrFun (hInitialState ω) 1
      have hN0 :
          N t ω 0 = Nij 0 0 t ω + Nij 0 1 t ω := by
        simpa using hNsum t ω 0
      have hN1 :
          N t ω 1 = Nij 1 0 t ω + Nij 1 1 t ω := by
        simpa using hNsum t ω 1
      -- Proof comment: summing the two coordinate equations gives the one-dimensional state
      -- equation, and the drift integral vanishes because the target drift is zero.
      calc
        sumTwoCoordinatePath (L ω) t 0 = L ω t 0 + L ω t 1 := by
          rfl
        _ = (L.ξ ω 0 + N t ω 0) + (L.ξ ω 1 + N t ω 1) := by
          rw [hState0, hState1]
        _ = (L.ξ ω 0 + L.ξ ω 1) + (N t ω 0 + N t ω 1) := by
          ring
        _ = sumTwoCoordinatePath (L ω) 0 0 + summedMartingalePart t ω 0 := by
          rw [hN0, hN1]
          simp [sumTwoCoordinatePath_apply, summedMartingalePart, scalarIto, hInit0, hInit1]
          ring
        _ = sumTwoCoordinatePath (L ω) 0 0 + summedMartingalePart t ω 0 +
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
                oneDimensionalDrift
                  (cirDriftCoeff 0 0)
                  s.toNNReal
                  ((fun t ω ↦ sumTwoCoordinatePath (L ω) t) s.toNNReal ω)
                  0 := by
            simp [cirDriftCoeff_apply]

end ProbabilityTheory
