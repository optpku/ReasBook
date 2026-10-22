/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_3_1

open Filter Topology

-- Chapter 4 already owns the canonical conjugate-gradient iterative-scheme record and the
-- Fletcher-Reeves coefficient used by its update rule. This exercise keeps its explicit objective
-- functions and bridges the quartic run to that owner, while retaining the source exercise's
-- concrete iterate and convergence statements.

section

local notation "Point" => EuclideanSpace ℝ (Fin 2)

/-- The common initial point `x^(0) = (0, 0)ᵀ` for Exercise 4.2. -/
def exercise42InitialPoint : Point := !₂[(0 : ℝ), 0]

/-- The quadratic objective from Exercise 4.2 (1). -/
def exercise42QuadraticObjective (x : Point) : ℝ :=
  x 0 ^ (2 : ℕ) + 2 * x 1 ^ (2 : ℕ) - 2 * x 0 * x 1 + 2 * x 1 + 2

/-- The quartic objective from Exercise 4.2 (2). -/
def exercise42QuarticObjective (x : Point) : ℝ :=
  (x 0 - 1) ^ (4 : ℕ) + (x 0 - x 1) ^ (2 : ℕ)

/-- The first Fletcher-Reeves iterate for `exercise42QuadraticObjective` from `(0, 0)ᵀ`. -/
def exercise42QuadraticFirstIterate : Point := !₂[(0 : ℝ), -((1 / 2 : ℚ) : ℝ)]

/-- The initial gradient of `exercise42QuadraticObjective` at `(0, 0)ᵀ`. -/
def exercise42QuadraticInitialGradient : Point := !₂[(0 : ℝ), 2]

/-- The initial Fletcher-Reeves direction for `exercise42QuadraticObjective` at `(0, 0)ᵀ`. -/
def exercise42QuadraticInitialDirection : Point := !₂[(0 : ℝ), -2]

/-- The first exact line-search step for the quadratic run in Exercise 4.2 (1). -/
def exercise42QuadraticFirstStep : ℝ := ((1 / 4 : ℚ) : ℝ)

/-- The gradient of `exercise42QuadraticObjective` at `exercise42QuadraticFirstIterate`. -/
def exercise42QuadraticSecondGradient : Point := !₂[(1 : ℝ), 0]

/-- The Fletcher-Reeves coefficient used to form the second search direction. -/
def exercise42QuadraticFirstBeta : ℝ := ((1 / 4 : ℚ) : ℝ)

/-- The second Fletcher-Reeves direction for the quadratic run in Exercise 4.2 (1). -/
def exercise42QuadraticSecondDirection : Point := !₂[-(1 : ℝ), -((1 / 2 : ℚ) : ℝ)]

/-- The second exact line-search step for the quadratic run in Exercise 4.2 (1). -/
def exercise42QuadraticSecondStep : ℝ := 1

/-- The global minimizer of `exercise42QuadraticObjective`. -/
def exercise42QuadraticMinimizer : Point := !₂[-(1 : ℝ), -1]

/-- The second iterate of the quadratic Fletcher-Reeves run in Exercise 4.2 (1). -/
def exercise42QuadraticSecondIterate : Point :=
  exercise42QuadraticFirstIterate +
    exercise42QuadraticSecondStep • exercise42QuadraticSecondDirection

/-- The global minimizer of `exercise42QuarticObjective`. -/
def exercise42QuarticMinimizer : Point := !₂[(1 : ℝ), 1]

/-- The quadratic objective has gradient `exercise42QuadraticInitialGradient` at `(0, 0)ᵀ`. -/
theorem exercise42QuadraticInitialGradient_hasGradientAt :
    HasGradientAt exercise42QuadraticObjective
      exercise42QuadraticInitialGradient exercise42InitialPoint := sorry

/-- The initial Fletcher-Reeves direction for the quadratic run is the negative gradient. -/
theorem exercise42QuadraticInitialDirection_eq :
    exercise42QuadraticInitialDirection = -exercise42QuadraticInitialGradient := sorry

/-- The first quadratic Fletcher-Reeves step is an exact line-search minimizer. -/
theorem exercise42QuadraticFirstStep_exactLineSearch :
    IsExactLineSearchStepOnNonnegativeRay
      exercise42QuadraticObjective exercise42InitialPoint
      exercise42QuadraticInitialDirection exercise42QuadraticFirstStep := sorry

/-- The first quadratic Fletcher-Reeves iterate is obtained from the line-search update. -/
theorem exercise42QuadraticFirstIterate_eq :
    exercise42QuadraticFirstIterate =
      exercise42InitialPoint +
        exercise42QuadraticFirstStep • exercise42QuadraticInitialDirection := sorry

/-- The quadratic objective has gradient `exercise42QuadraticSecondGradient`
at `exercise42QuadraticFirstIterate`. -/
theorem exercise42QuadraticSecondGradient_hasGradientAt :
    HasGradientAt exercise42QuadraticObjective
      exercise42QuadraticSecondGradient exercise42QuadraticFirstIterate := sorry

/-- The quadratic Fletcher-Reeves coefficient is the canonical Fletcher-Reeves ratio of the
two successive gradients. -/
theorem exercise42QuadraticFirstBeta_eq :
    exercise42QuadraticFirstBeta =
      fletcherReevesCoefficient
        exercise42QuadraticInitialGradient exercise42QuadraticSecondGradient := sorry

/-- The second quadratic Fletcher-Reeves direction satisfies the Fletcher-Reeves update rule. -/
theorem exercise42QuadraticSecondDirection_eq :
    exercise42QuadraticSecondDirection =
      -exercise42QuadraticSecondGradient +
        exercise42QuadraticFirstBeta • exercise42QuadraticInitialDirection := sorry

/-- The second quadratic Fletcher-Reeves step is an exact line-search minimizer. -/
theorem exercise42QuadraticSecondStep_exactLineSearch :
    IsExactLineSearchStepOnNonnegativeRay
      exercise42QuadraticObjective exercise42QuadraticFirstIterate
      exercise42QuadraticSecondDirection exercise42QuadraticSecondStep := sorry

/-- Chapter04 Exercise 4.2 (1): for
`f x = x 0 ^ 2 + 2 * x 1 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 + 2`, the Fletcher-Reeves
conjugate-gradient run from `(0, 0)ᵀ` reaches `!₂[-1, -1]` after the two explicit
exact line-search steps recorded above, and that point is a global minimizer. -/
theorem quadraticFletcherReevesReachesMinimizerFromOrigin :
    exercise42QuadraticSecondIterate = exercise42QuadraticMinimizer ∧
      IsMinOn exercise42QuadraticObjective Set.univ exercise42QuadraticMinimizer := sorry

/-- Internal state used to iterate the quartic Fletcher-Reeves run. -/
private structure QuarticFletcherReevesState where
  x : Point
  d : Point

/-- The initial quartic Fletcher-Reeves state starts at `(0, 0)ᵀ` with direction `!₂[4, 0]`. -/
private def exercise42QuarticInitialState : QuarticFletcherReevesState where
  x := exercise42InitialPoint
  d := !₂[(4 : ℝ), 0]

/-- The canonical exact line-search steplength attached to one quartic Fletcher-Reeves state. -/
private noncomputable def exercise42QuarticStepOfState
    (s : QuarticFletcherReevesState) : ℝ :=
  sInf {a : ℝ | IsExactLineSearchStepOnNonnegativeRay exercise42QuarticObjective s.x s.d a}

/-- The successor state obtained by one Fletcher-Reeves step for `exercise42QuarticObjective`. -/
private noncomputable def exercise42QuarticNextState
    (s : QuarticFletcherReevesState) : QuarticFletcherReevesState :=
  let α := exercise42QuarticStepOfState s
  let xNext := s.x + α • s.d
  let g := gradient exercise42QuarticObjective s.x
  let gNext := gradient exercise42QuarticObjective xNext
  let β := fletcherReevesCoefficient g gNext
  { x := xNext
    d := -gNext + β • s.d }

/-- Internal recursive state sequence for the quartic Fletcher-Reeves run. -/
private noncomputable def exercise42QuarticState (k : ℕ) : QuarticFletcherReevesState :=
  (exercise42QuarticNextState^[k]) exercise42QuarticInitialState

/-- The concrete quartic Fletcher-Reeves run from Exercise 4.2 (2), recorded as a value of
the Chapter 4 conjugate-gradient iterative-scheme owner. -/
noncomputable def exercise42QuarticFletcherReevesMethod :
    ConjugateGradientIterativeScheme 2 exercise42QuarticObjective where
  x0 := exercise42InitialPoint
  x := fun k ↦ (exercise42QuarticState k).x
  g := fun k ↦
    let s := exercise42QuarticState k
    gradient exercise42QuarticObjective s.x
  d := fun k ↦ (exercise42QuarticState k).d
  α := fun k ↦ exercise42QuarticStepOfState (exercise42QuarticState k)
  β := fun k ↦
    let s := exercise42QuarticState k
    let sNext := exercise42QuarticState (k + 1)
    fletcherReevesCoefficient
      (gradient exercise42QuarticObjective s.x)
      (gradient exercise42QuarticObjective sNext.x)
  x_zero := rfl
  hasGradientAt := by
    intro k
    sorry
  direction_zero := by
    sorry
  exactLineSearch := by
    intro k hk
    sorry
  iterate_eq := by
    intro k hk
    sorry
  beta_eq := by
    intro k hk hkNext
    rfl
  direction_eq := by
    intro k hk hkNext
    sorry

/-- The quartic Fletcher-Reeves run starts at the prescribed initial point. -/
theorem exercise42QuarticFletcherReevesIterate_zero :
    exercise42QuarticFletcherReevesMethod 0 = exercise42InitialPoint :=
  exercise42QuarticFletcherReevesMethod.x_zero

/-- The initial quartic Fletcher-Reeves gradient is `!₂[-4, 0]`. -/
theorem exercise42QuarticFletcherReevesGradient_zero :
    exercise42QuarticFletcherReevesMethod.g 0 = !₂[-(4 : ℝ), 0] := sorry

/-- The initial quartic Fletcher-Reeves direction is the negative initial gradient. -/
theorem exercise42QuarticFletcherReevesDirection_zero :
    exercise42QuarticFletcherReevesMethod.d 0 =
      -exercise42QuarticFletcherReevesMethod.g 0 :=
  exercise42QuarticFletcherReevesMethod.direction_zero

/-- The quartic objective has gradient `exercise42QuarticFletcherReevesMethod.g k`
at the `k`-th iterate of the quartic Fletcher-Reeves run. -/
theorem exercise42QuarticFletcherReeves_hasGradientAt (k : ℕ) :
    HasGradientAt exercise42QuarticObjective
      (exercise42QuarticFletcherReevesMethod.g k)
      (exercise42QuarticFletcherReevesMethod k) :=
  exercise42QuarticFletcherReevesMethod.hasGradientAt k

/-- The stage-`k` quartic Fletcher-Reeves step is an exact line-search minimizer whenever the
run has not terminated at stage `k`. -/
theorem exercise42QuarticFletcherReevesStep_exactLineSearch (k : ℕ)
    (hk : exercise42QuarticFletcherReevesMethod.g k ≠ 0) :
    IsExactLineSearchStepOnNonnegativeRay exercise42QuarticObjective
      (exercise42QuarticFletcherReevesMethod k)
      (exercise42QuarticFletcherReevesMethod.d k)
      (exercise42QuarticFletcherReevesMethod.α k) :=
  exercise42QuarticFletcherReevesMethod.exactLineSearch k hk

/-- The quartic Fletcher-Reeves iterates satisfy the exact line-search update recurrence
whenever the stage-`k` gradient is nonzero. -/
theorem exercise42QuarticFletcherReevesIterate_succ (k : ℕ)
    (hk : exercise42QuarticFletcherReevesMethod.g k ≠ 0) :
    exercise42QuarticFletcherReevesMethod (k + 1) =
      exercise42QuarticFletcherReevesMethod k +
        exercise42QuarticFletcherReevesMethod.α k •
          exercise42QuarticFletcherReevesMethod.d k :=
  exercise42QuarticFletcherReevesMethod.iterate_eq k hk

/-- The quartic Fletcher-Reeves coefficients are the canonical Fletcher-Reeves ratios of
successive gradients whenever the method continues across both stages. -/
theorem exercise42QuarticFletcherReevesBeta_eq (k : ℕ)
    (hk : exercise42QuarticFletcherReevesMethod.g k ≠ 0)
    (hkNext : exercise42QuarticFletcherReevesMethod.g (k + 1) ≠ 0) :
    exercise42QuarticFletcherReevesMethod.β k =
      fletcherReevesCoefficient
        (exercise42QuarticFletcherReevesMethod.g k)
        (exercise42QuarticFletcherReevesMethod.g (k + 1)) :=
  exercise42QuarticFletcherReevesMethod.beta_eq k hk hkNext

/-- The quartic Fletcher-Reeves directions satisfy the Fletcher-Reeves update recurrence
whenever the method continues across both stages. -/
theorem exercise42QuarticFletcherReevesDirection_succ (k : ℕ)
    (hk : exercise42QuarticFletcherReevesMethod.g k ≠ 0)
    (hkNext : exercise42QuarticFletcherReevesMethod.g (k + 1) ≠ 0) :
    exercise42QuarticFletcherReevesMethod.d (k + 1) =
      -exercise42QuarticFletcherReevesMethod.g (k + 1) +
        exercise42QuarticFletcherReevesMethod.β k •
          exercise42QuarticFletcherReevesMethod.d k :=
  exercise42QuarticFletcherReevesMethod.direction_eq k hk hkNext

/-- Chapter04 Exercise 4.2 (2): for
`f x = (x 0 - 1) ^ 4 + (x 0 - x 1) ^ 2`, the concrete Fletcher-Reeves run from
`(0, 0)ᵀ` recorded by `exercise42QuarticFletcherReevesMethod`
converges to `!₂[1, 1]`, and that point is a global minimizer. -/
theorem quarticFletcherReevesConvergesFromOrigin :
    Tendsto exercise42QuarticFletcherReevesMethod atTop (𝓝 exercise42QuarticMinimizer) ∧
      IsMinOn exercise42QuarticObjective Set.univ exercise42QuarticMinimizer := sorry

end
