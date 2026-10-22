/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1

noncomputable section

section NegativeCurvatureDirectionMethodExtra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The source trial arc `x_k(α) = x_k + α • s_k + α^2 • d_k` used in
Algorithm 3.5-extra-1. -/
def negativeCurvatureArcTrialPoint (x s d : E) (α : ℝ) : E :=
  x + α • s + (α ^ (2 : ℕ)) • d

/-- The sufficient-decrease test `(3.5.45)` on the source trial arc `x_k(α)`. -/
def negativeCurvatureArcAccepts (f : E → ℝ) (x s d : E) (γ ρ : ℝ) (i : ℕ) : Prop :=
  f (negativeCurvatureArcTrialPoint x s d (γ ^ i)) - f x ≤
    ρ * ((γ ^ i) * inner ℝ s (gradient f x) +
      (1 / 2 : ℝ) * (γ ^ (4 * i)) * hessianQuadraticAt f x d)

/-- `m` is the smallest nonnegative integer satisfying the sufficient-decrease test. -/
def IsSmallestNegativeCurvatureArcIndex (f : E → ℝ)
    (x s d : E) (γ ρ : ℝ) (m : ℕ) : Prop :=
  negativeCurvatureArcAccepts f x s d γ ρ m ∧
    ∀ j : ℕ, j < m → ¬ negativeCurvatureArcAccepts f x s d γ ρ j

/-- Algorithm 3.5-extra-1 stops at index `k` exactly when no descent pair exists at `x k`. -/
def negativeCurvatureDirectionMethodExtraStopsAt (f : E → ℝ) (x : ℕ → E) (k : ℕ) : Prop :=
  ¬ ∃ s d : E, IsDescentPairAt f (x k) s d

/-- The stopping rule is the Chapter 3 criterion that `x k` is stationary and its Hessian is
positive semidefinite. -/
theorem negativeCurvatureDirectionMethodExtraStopsAt_iff
    (f : E → ℝ) (x : ℕ → E) (k : ℕ)
    (hHessian : DifferentiableAt ℝ (gradient f) (x k)) :
    negativeCurvatureDirectionMethodExtraStopsAt f x k ↔
      gradient f (x k) = 0 ∧ HasPositiveSemidefiniteHessianAt f (x k) := by
  simpa [negativeCurvatureDirectionMethodExtraStopsAt] using
    (not_exists_descentPairAt_iff f (x k) hHessian)

/-- Algorithm 3.5-extra-1 continues from iterate `x k` when a descent pair is chosen,
`acceptedIndex k` is the smallest accepted exponent from `(3.5.45)`, and
`x (k + 1)` is updated by `(3.5.46)`. -/
def negativeCurvatureDirectionMethodExtraContinuesAt (f : E → ℝ)
    (x s d : ℕ → E) (acceptedIndex : ℕ → ℕ) (γ ρ : ℝ) (k : ℕ) : Prop :=
  IsDescentPairAt f (x k) (s k) (d k) ∧
    IsSmallestNegativeCurvatureArcIndex f (x k) (s k) (d k) γ ρ (acceptedIndex k) ∧
    x (k + 1) =
      negativeCurvatureArcTrialPoint (x k) (s k) (d k) (γ ^ acceptedIndex k)

/-- Chapter03 Algorithm 3.5-extra-1: for parameters `γ, ρ ∈ (0, 1)` and initial point
`x₀`, the data `x`, `s`, `d`, and `acceptedIndex` follow the negative-curvature
direction method on `D` when `x 0 = x₀`, every iterate lies in `D`, and for each `k`,
if a descent pair exists at `x k`, then `(s k, d k)` is chosen, `acceptedIndex k` is
the smallest nonnegative integer satisfying `(3.5.45)`, and `(3.5.46)` sets
`x (k + 1) = negativeCurvatureArcTrialPoint (x k) (s k) (d k) (γ ^ acceptedIndex k)`;
otherwise the algorithm stops at `k`. -/
class IsNegativeCurvatureDirectionMethodExtraSequenceOn
    (D : Set E) (f : E → ℝ) (γ ρ : ℝ) (x0 : E) (x s d : ℕ → E)
    (acceptedIndex : ℕ → ℕ) : Prop where
  gamma_mem : γ ∈ Set.Ioo (0 : ℝ) 1
  rho_mem : ρ ∈ Set.Ioo (0 : ℝ) 1
  x_zero : x 0 = x0
  iterates_mem : ∀ k : ℕ, x k ∈ D
  continue_of_exists :
    ∀ k : ℕ,
      (∃ s' d' : E, IsDescentPairAt f (x k) s' d') →
      negativeCurvatureDirectionMethodExtraContinuesAt f x s d acceptedIndex γ ρ k

/-- A finite terminating run of Algorithm 3.5-extra-1 packages a source-faithful
sequence together with an index where the algorithm stops. -/
structure NegativeCurvatureDirectionMethodExtraRunOn
    (D : Set E) (f : E → ℝ) where
  γ : ℝ
  ρ : ℝ
  x0 : E
  x : ℕ → E
  s : ℕ → E
  d : ℕ → E
  acceptedIndex : ℕ → ℕ
  terminalIndex : ℕ
  toSequence :
    IsNegativeCurvatureDirectionMethodExtraSequenceOn D f γ ρ x0 x s d acceptedIndex
  terminal : negativeCurvatureDirectionMethodExtraStopsAt f x terminalIndex

/-- A run of Algorithm 3.5-extra-1 can be used as its sequence of iterates. -/
instance {D : Set E} {f : E → ℝ} :
    CoeFun (NegativeCurvatureDirectionMethodExtraRunOn D f) (fun _ ↦ ℕ → E) where
  coe A := A.x

/-- A terminating run inherits the source-faithful sequence property. -/
instance {D : Set E} {f : E → ℝ}
    (A : NegativeCurvatureDirectionMethodExtraRunOn D f) :
    IsNegativeCurvatureDirectionMethodExtraSequenceOn D f A.γ A.ρ A.x0 A.x A.s A.d
      A.acceptedIndex :=
  A.toSequence

/-- If a descent pair exists at step `k`, the algorithm continues at `k` with the recorded
search directions and accepted index. -/
theorem IsNegativeCurvatureDirectionMethodExtraSequenceOn.continuesAt
    {D : Set E} {f : E → ℝ} {γ ρ : ℝ} {x0 : E} {x s d : ℕ → E}
    {acceptedIndex : ℕ → ℕ}
    (A : IsNegativeCurvatureDirectionMethodExtraSequenceOn D f γ ρ x0 x s d acceptedIndex)
    (k : ℕ)
    (hk : ∃ s' d' : E, IsDescentPairAt f (x k) s' d') :
    negativeCurvatureDirectionMethodExtraContinuesAt f x s d acceptedIndex γ ρ k :=
  A.continue_of_exists k hk

/-- If a descent pair exists at step `k`, the recorded exponent `acceptedIndex k` is the
smallest accepted index for `(3.5.45)`. -/
theorem IsNegativeCurvatureDirectionMethodExtraSequenceOn.acceptedIndex_isSmallest
    {D : Set E} {f : E → ℝ} {γ ρ : ℝ} {x0 : E} {x s d : ℕ → E}
    {acceptedIndex : ℕ → ℕ}
    (A : IsNegativeCurvatureDirectionMethodExtraSequenceOn D f γ ρ x0 x s d acceptedIndex)
    (k : ℕ)
    (hk : ∃ s' d' : E, IsDescentPairAt f (x k) s' d') :
    IsSmallestNegativeCurvatureArcIndex f (x k) (s k) (d k) γ ρ (acceptedIndex k) :=
  (A.continuesAt k hk).2.1

/-- If a descent pair exists at step `k`, the recorded exponent `acceptedIndex k`
satisfies the sufficient-decrease test `(3.5.45)`. -/
theorem IsNegativeCurvatureDirectionMethodExtraSequenceOn.accepts_acceptedIndex
    {D : Set E} {f : E → ℝ} {γ ρ : ℝ} {x0 : E} {x s d : ℕ → E}
    {acceptedIndex : ℕ → ℕ}
    (A : IsNegativeCurvatureDirectionMethodExtraSequenceOn D f γ ρ x0 x s d acceptedIndex)
    (k : ℕ)
    (hk : ∃ s' d' : E, IsDescentPairAt f (x k) s' d') :
    negativeCurvatureArcAccepts f (x k) (s k) (d k) γ ρ (acceptedIndex k) :=
  (A.acceptedIndex_isSmallest k hk).1

/-- If a descent pair exists at step `k`, the next iterate is the accepted trial point from
`(3.5.46)`. -/
theorem IsNegativeCurvatureDirectionMethodExtraSequenceOn.next_eq
    {D : Set E} {f : E → ℝ} {γ ρ : ℝ} {x0 : E} {x s d : ℕ → E}
    {acceptedIndex : ℕ → ℕ}
    (A : IsNegativeCurvatureDirectionMethodExtraSequenceOn D f γ ρ x0 x s d acceptedIndex)
    (k : ℕ)
    (hk : ∃ s' d' : E, IsDescentPairAt f (x k) s' d') :
    x (k + 1) =
      negativeCurvatureArcTrialPoint (x k) (s k) (d k) (γ ^ acceptedIndex k) :=
  (A.continuesAt k hk).2.2

end NegativeCurvatureDirectionMethodExtra
