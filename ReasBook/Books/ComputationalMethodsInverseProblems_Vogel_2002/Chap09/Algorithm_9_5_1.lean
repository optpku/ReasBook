/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Bounds.Basic

public section

noncomputable section

open scoped Matrix

namespace Mrnsd

universe u v

variable {n : Type v}

/-- A single MRNSD stage stores the current solution, gradient, and scalar `γ`. -/
structure State (n : Type v) where
  /-- The current iterate `f_v`. -/
  solution : EuclideanSpace ℝ n
  /-- The current gradient `g_v`. -/
  gradient : EuclideanSpace ℝ n
  /-- The current scalar `γ_v`. -/
  gamma : ℝ

/-- The MRNSD descent direction at a state is `-(f_v * g_v)`. -/
def direction (state : State n) : EuclideanSpace ℝ n :=
  -WithLp.toLp 2 (fun i ↦ state.solution i * state.gradient i)

/-- The boundary-step candidates are the ratios `-f_i / p_i` over indices where
the current direction has negative component. -/
def boundaryCandidates (state : State n) : Set ℝ :=
  { t | ∃ i : n, direction state i < 0 ∧ t = -state.solution i / direction state i }

/-- The defining formula for the MRNSD direction. -/
theorem direction_def (state : State n) :
    direction state = -WithLp.toLp 2 (fun i ↦ state.solution i * state.gradient i) := by
  -- This is exactly the defining equation of `direction`.
  rfl

/-- A real number belongs to the boundary-candidate set exactly when it is one
of the ratios `-f_i / p_i` for a negative direction component. -/
theorem mem_boundaryCandidates_iff (state : State n) (t : ℝ) :
    t ∈ boundaryCandidates state ↔
      ∃ i : n, direction state i < 0 ∧ t = -state.solution i / direction state i := by
  -- Membership unfolds directly to the defining existential predicate.
  rfl

section MatrixIndexed

variable {m : Type u} {n : Type v} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The initial MRNSD state has solution `f₀`, gradient `Kᵀ (K f₀ - d)`, and
scalar `⟪g₀, f₀ * g₀⟫`. -/
def initialState (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (f0 : EuclideanSpace ℝ n) :
    State n :=
  let gradient := Matrix.toEuclideanLin Kᵀ (Matrix.toEuclideanLin K f0 - d)
  { solution := f0
    gradient := gradient
    gamma := inner ℝ gradient (WithLp.toLp 2 fun i ↦ f0 i * gradient i) }

/-- The auxiliary vector `u_v` is `K p_v` for the current direction `p_v`. -/
def appliedDirection (K : Matrix m n ℝ) (state : State n) : EuclideanSpace ℝ m :=
  Matrix.toEuclideanLin K (direction state)

/-- The explicit MRNSD successor state obtained from `state` with step length
`τ`. -/
def nextState (K : Matrix m n ℝ) (state : State n) (τ : ℝ) : State n :=
  let solution := state.solution + τ • direction state
  let gradient := state.gradient + τ • Matrix.toEuclideanLin Kᵀ (appliedDirection K state)
  { solution := solution
    gradient := gradient
    gamma :=
      inner ℝ gradient (WithLp.toLp 2 fun i ↦ solution i * gradient i) }

/-- The recursive MRNSD state family generated from the explicit initial state
and the step-size sequence `τ`. -/
@[expose] def iterates (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (f0 : EuclideanSpace ℝ n) (τ : ℕ → ℝ) : ℕ → State n
  | 0 => initialState K d f0
  | v + 1 => nextState K (iterates K d f0 τ v) (τ v)

/-- A single MRNSD update records the boundary minimum and step-size clauses for
the canonical successor state determined by that step length. -/
structure IsStep (K : Matrix m n ℝ) (state : State n) (τBoundary τ : ℝ)
    (next : State n) : Prop where
  /-- `τBoundary` is the least admissible boundary step. -/
  boundary_isLeast : IsLeast (boundaryCandidates state) τBoundary
  /-- The auxiliary vector `u_v = K p_v` is nonzero, so `γ_v / ‖u_v‖²` is well posed. -/
  appliedDirection_ne_zero : appliedDirection K state ≠ 0
  /-- `τ` is the minimum of `γ_v / ‖u_v‖²` and `τBoundary`. -/
  stepSize_eq : τ = min (state.gamma / ‖appliedDirection K state‖ ^ 2) τBoundary
  /-- The successor state is the explicit MRNSD update determined by `τ`. -/
  next_eq : next = nextState K state τ

/-- Algorithm 9.5.1. An MRNSD iterate sequence with componentwise nonnegative
initial guess and recursively defined successor states satisfying the MRNSD step
relations. -/
structure IsIterateSequence (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (f0 : EuclideanSpace ℝ n) (τBoundary τ : ℕ → ℝ) : Prop where
  /-- The initial guess is componentwise nonnegative. -/
  nonneg : ∀ i : n, 0 ≤ f0 i
  /-- Every recursively defined successor is related by one MRNSD step. -/
  step :
    ∀ v : ℕ,
      IsStep K (iterates K d f0 τ v) (τBoundary v) (τ v) (iterates K d f0 τ (v + 1))

/-- The solution component of `initialState K d f0` is `f₀`. -/
theorem initialState_solution (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (f0 : EuclideanSpace ℝ n) :
    (initialState K d f0).solution = f0 := by
  -- The `solution` projection reads off the constructor field of `initialState`.
  rfl

/-- The gradient component of `initialState K d f0` is `Kᵀ (K f₀ - d)`. -/
theorem initialState_gradient (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (f0 : EuclideanSpace ℝ n) :
    (initialState K d f0).gradient =
      Matrix.toEuclideanLin Kᵀ (Matrix.toEuclideanLin K f0 - d) := by
  -- The `gradient` projection is the auxiliary value introduced in `initialState`.
  rfl

/-- The scalar component of `initialState K d f0` is `⟪g₀, f₀ * g₀⟫`. -/
theorem initialState_gamma (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (f0 : EuclideanSpace ℝ n) :
    (initialState K d f0).gamma =
      inner ℝ (Matrix.toEuclideanLin Kᵀ (Matrix.toEuclideanLin K f0 - d))
        (WithLp.toLp 2 fun i ↦
          f0 i * Matrix.toEuclideanLin Kᵀ (Matrix.toEuclideanLin K f0 - d) i) := by
  -- The `gamma` projection is also stored directly in the `initialState` record.
  rfl

/-- The solution component of `nextState K state τ` is `f_v + τ p_v`. -/
theorem nextState_solution (K : Matrix m n ℝ) (state : State n) (τ : ℝ) :
    (nextState K state τ).solution = state.solution + τ • direction state := by
  -- The successor state's `solution` field is defined by the explicit MRNSD update.
  rfl

/-- The gradient component of `nextState K state τ` is `g_v + τ Kᵀ u_v`. -/
theorem nextState_gradient (K : Matrix m n ℝ) (state : State n) (τ : ℝ) :
    (nextState K state τ).gradient =
      state.gradient + τ • Matrix.toEuclideanLin Kᵀ (appliedDirection K state) := by
  -- The successor state's `gradient` field is the corresponding explicit update.
  rfl

/-- The scalar component of `nextState K state τ` is
`⟪g_(v+1), f_(v+1) * g_(v+1)⟫`. -/
theorem nextState_gamma (K : Matrix m n ℝ) (state : State n) (τ : ℝ) :
    (nextState K state τ).gamma =
      inner ℝ (nextState K state τ).gradient
        (WithLp.toLp 2 fun i ↦
          (nextState K state τ).solution i * (nextState K state τ).gradient i) := by
  -- Expanding the constructor shows that `gamma` is computed from the new fields.
  rfl

/-- The zeroth MRNSD iterate is the explicit initial state. -/
@[simp] theorem iterates_zero (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (f0 : EuclideanSpace ℝ n) (τ : ℕ → ℝ) :
    iterates K d f0 τ 0 = initialState K d f0 := rfl

/-- The successor MRNSD iterate is obtained by applying the explicit MRNSD
update with step size `τ v` to the current state. -/
@[simp] theorem iterates_succ (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (f0 : EuclideanSpace ℝ n) (τ : ℕ → ℝ) (v : ℕ) :
    iterates K d f0 τ (v + 1) = nextState K (iterates K d f0 τ v) (τ v) := rfl

namespace IsStep

variable (K : Matrix m n ℝ) (state : State n) (τBoundary τ : ℝ) (next : State n)

/-- The solution update extracted from `Mrnsd.IsStep`. -/
theorem solution_eq (h : IsStep K state τBoundary τ next) :
    next.solution = state.solution + τ • direction state := by
  -- Project the stored state equality to the `solution` component.
  simpa [nextState_solution] using congrArg State.solution h.next_eq

/-- The gradient update extracted from `Mrnsd.IsStep`. -/
theorem gradient_eq (h : IsStep K state τBoundary τ next) :
    next.gradient = state.gradient + τ • Matrix.toEuclideanLin Kᵀ (appliedDirection K state) :=
  by
  -- Project the stored state equality to the `gradient` component.
  simpa [nextState_gradient] using congrArg State.gradient h.next_eq

/-- The scalar update extracted from `Mrnsd.IsStep`. -/
theorem gamma_eq (h : IsStep K state τBoundary τ next) :
    next.gamma =
      inner ℝ next.gradient (WithLp.toLp 2 fun i ↦ next.solution i * next.gradient i) := by
  -- Rewrite `next` to the explicit successor state, then use its stored `gamma` formula.
  cases h.next_eq
  exact nextState_gamma K state τ

end IsStep

/-- Specification theorem for `Mrnsd.IsStep`. -/
theorem isStep_iff (K : Matrix m n ℝ) (state : State n) (τBoundary τ : ℝ) (next : State n) :
    IsStep K state τBoundary τ next ↔
      IsLeast (boundaryCandidates state) τBoundary ∧
        appliedDirection K state ≠ 0 ∧
        τ = min (state.gamma / ‖appliedDirection K state‖ ^ 2) τBoundary ∧
        next.solution = state.solution + τ • direction state ∧
        next.gradient =
          state.gradient + τ • Matrix.toEuclideanLin Kᵀ (appliedDirection K state) ∧
        next.gamma =
          inner ℝ next.gradient
            (WithLp.toLp 2 fun i ↦ next.solution i * next.gradient i) := by
  constructor
  · intro h
    -- Unpack the structure fields and expose the three projection formulas.
    refine ⟨h.boundary_isLeast, h.appliedDirection_ne_zero, h.stepSize_eq, ?_, ?_, ?_⟩
    · exact IsStep.solution_eq K state τBoundary τ next h
    · exact IsStep.gradient_eq K state τBoundary τ next h
    · exact IsStep.gamma_eq K state τBoundary τ next h
  · rintro ⟨hBoundary, hApplied, hTau, hSolution, hGradient, hGamma⟩
    -- Rebuild the record by reconstructing the stored successor-state equality.
    have hSolutionNext : next.solution = (nextState K state τ).solution := by
      exact hSolution.trans (nextState_solution K state τ).symm
    have hGradientNext : next.gradient = (nextState K state τ).gradient := by
      exact hGradient.trans (nextState_gradient K state τ).symm
    have hGammaNext : next.gamma = (nextState K state τ).gamma := by
      calc
        next.gamma
            =
              inner ℝ next.gradient
                (WithLp.toLp 2 fun i ↦ next.solution i * next.gradient i) := hGamma
        _ = inner ℝ (nextState K state τ).gradient
              (WithLp.toLp 2 fun i ↦
                (nextState K state τ).solution i * (nextState K state τ).gradient i) := by
              rw [hGradientNext, hSolutionNext]
        _ = (nextState K state τ).gamma := (nextState_gamma K state τ).symm
    refine ⟨hBoundary, hApplied, hTau, ?_⟩
    -- Equality of `State` records reduces to equality of the three fields.
    cases next
    cases hSolutionNext
    cases hGradientNext
    cases hGammaNext
    rfl

/-- Specification theorem for `Mrnsd.IsIterateSequence`. -/
theorem isIterateSequence_iff (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (f0 : EuclideanSpace ℝ n) (τBoundary τ : ℕ → ℝ) :
    IsIterateSequence K d f0 τBoundary τ ↔
      (∀ i : n, 0 ≤ f0 i) ∧
        ∀ v : ℕ,
          IsStep K (iterates K d f0 τ v) (τBoundary v) (τ v) (iterates K d f0 τ (v + 1)) :=
  by
  constructor
  · intro h
    -- The specification is exactly the pair of fields stored in the structure.
    exact ⟨h.nonneg, h.step⟩
  · rintro ⟨hNonneg, hStep⟩
    -- Conversely, package the two clauses back into `IsIterateSequence`.
    exact ⟨hNonneg, hStep⟩

end MatrixIndexed

end Mrnsd

/-!
Algorithm 9.5.1. MRNSD.

The reusable owner for the source algorithm is the recursive MRNSD iterate
validity predicate `Mrnsd.IsIterateSequence`, which packages the nonnegative
initial guess together with the per-step boundary-minimum and line-search
requirements for the canonical iterate family `Mrnsd.iterates`.
-/

/- Algorithm 9.5.1. Source-facing MRNSD iterate-sequence owner. -/
#check Mrnsd.IsIterateSequence

/- Backend recursive iterate family used by Algorithm 9.5.1. -/
#check Mrnsd.iterates
