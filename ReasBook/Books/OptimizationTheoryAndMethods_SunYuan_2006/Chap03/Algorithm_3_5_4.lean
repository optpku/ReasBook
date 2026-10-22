/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_3_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_5_2

noncomputable section

/-- The ambient Euclidean space `ℝ^n` for the negative-curvature direction method. -/
abbrev NegativeCurvaturePoint (n : ℕ) := EuclideanSpace ℝ (Fin n)

section

variable {n : ℕ}

local notation "Point" => NegativeCurvaturePoint n
local notation "Hessian" => Matrix (Fin n) (Fin n) ℝ

-- Semantic recall: `lean_leansearch` points to `Mathlib.Analysis.Matrix.LDL` for `LDLᵀ`
-- factorizations, `modifiedCholeskySystemMatrix` now lives with the Gill-Murray factorization
-- owner in Algorithm 3.3.2, and Chapter 3 already owns the pivot-search data in
-- `NegativeCurvaturePivotStep`. This item keeps the source-facing modified Cholesky and
-- Algorithm 3.5.2 data explicit, since the source algorithm records one concrete run rather than
-- an existence API.

/-- The Step 5 sign correction reverses a candidate negative-curvature direction when
`⟪g, d⟫_ℝ > 0`, so the corrected direction is not positively aligned with the gradient. -/
def negativeCurvatureSignCorrection (g d : Point) : Point :=
  if 0 < dotProduct g d then -d else d

/-- If `⟪g, d⟫_ℝ ≤ 0`, then the Step 5 sign correction leaves the candidate direction unchanged. -/
theorem negativeCurvatureSignCorrection_eq_self_of_inner_nonpos
    {g d : Point} (hgd : dotProduct g d ≤ 0) :
    negativeCurvatureSignCorrection g d = d := by
  simp [negativeCurvatureSignCorrection, not_lt.mpr hgd]

/-- If `⟪g, d⟫_ℝ > 0`, then the Step 5 sign correction flips the candidate direction. -/
theorem negativeCurvatureSignCorrection_eq_neg_of_inner_pos
    {g d : Point} (hgd : 0 < dotProduct g d) :
    negativeCurvatureSignCorrection g d = -d := by
  simp [negativeCurvatureSignCorrection, hgd]

/-- The Step 5 sign correction always produces a direction whose pairing with `g` is
nonpositive. -/
theorem negativeCurvatureSignCorrection_dotProduct_nonpos (g d : Point) :
    dotProduct g (negativeCurvatureSignCorrection g d) ≤ 0 := by
  by_cases hgd : 0 < dotProduct g d
  · simp [negativeCurvatureSignCorrection, hgd, le_of_lt hgd]
  · have hgd' : dotProduct g d ≤ 0 := le_of_not_gt hgd
    simp [negativeCurvatureSignCorrection, hgd, hgd']

/-- The Step 4 / Step 5 rule for producing the search direction at one iteration:
either `‖g‖ > ε` and the modified Cholesky linear system is solved, or `‖g‖ ≤ ε`,
Algorithm 3.5.2 returns the direction branch at the selected pivot, and the search
direction is the Step 5 sign correction of that returned negative-curvature direction. -/
def NegativeCurvatureDirectionStep (ε : ℝ) (g : Point) (L : Hessian)
    (dDiag eDiag : Fin n → ℝ) (step : NegativeCurvaturePivotStep L dDiag eDiag)
    (d : Point) : Prop :=
  (ε < ‖g‖ ∧ (modifiedCholeskySystemMatrix L dDiag).mulVec d = -g) ∨
    (‖g‖ ≤ ε ∧
      ∃ (negative : negativeCurvaturePivotScores dDiag eDiag step.t < 0)
        (dk : Point)
        (solve_eq : (Matrix.transpose L).mulVec dk = negativeCurvatureUnitVector step.t),
        step.outcome = NegativeCurvaturePivotOutcome.direction negative dk solve_eq ∧
          d = negativeCurvatureSignCorrection g dk)

/-- The terminal small-gradient branch records that Algorithm 3.5.2 does not return a
negative-curvature direction when `‖g‖ ≤ ε` and the selected pivot score is nonnegative. -/
def negativeCurvatureTerminalSmallGradient (ε : ℝ) (g : Point) (L : Hessian)
    (dDiag eDiag : Fin n → ℝ) (step : NegativeCurvaturePivotStep L dDiag eDiag) : Prop :=
  ‖g‖ ≤ ε ∧
    ∃ nonnegative : 0 ≤ negativeCurvaturePivotScores dDiag eDiag step.t,
      step.outcome = NegativeCurvaturePivotOutcome.stop nonnegative

/-- The terminal line-search branch records that a computed search direction and update
fail to decrease the objective at the terminal iteration index. -/
def negativeCurvatureTerminalLineSearchFailure
    (f : Point → ℝ) (ε : ℝ) (x g : ℕ → Point)
    (L : ℕ → Hessian) (dDiag eDiag : ℕ → Fin n → ℝ)
    (pivotStep : ∀ k : ℕ, NegativeCurvaturePivotStep (L k) (dDiag k) (eDiag k))
    (d : ℕ → Point) (α : ℕ → ℝ) (k : ℕ) : Prop :=
  NegativeCurvatureDirectionStep ε (g k) (L k) (dDiag k) (eDiag k) (pivotStep k) (d k) ∧
    x (k + 1) = x k + α k • d k ∧
    f (x (k + 1)) ≥ f (x k)

/-- Chapter03 Algorithm 3.5.4: a run of the negative-curvature direction method with
modified Cholesky factorization, Algorithm 3.5.2 pivot steps, and line search on `ℝ^n`.

The data `x`, `g`, `G`, `L`, `dDiag`, `eDiag`, `pivotStep`, `d`, and `α` record one
execution of the algorithm. Lean uses the 0-based reindexing `x 0 = x₀` for the book's
initialization `k := 1`. For every active index `k ≤ terminalIndex`, Step 2 ties
`g k = gradient f (x k)` and `G k` to the Hessian of `f` at `x k`; Step 3 records the
diagonal correction `Matrix.diagonal (eDiag k)` with nonnegative entries and the
factorization `G k + Matrix.diagonal (eDiag k) = L k D k L kᵀ`; and `pivotStep k`
records the Algorithm 3.5.2 pivot choice and its stop/direction outcome for the same
`L k`, `dDiag k`, and `eDiag k`. For every nonterminal index `k`, the search direction
satisfies the Step 4 / Step 5 branching rule, Step 6 updates
`x (k + 1) = x k + α k • d k`, and Step 7 strictly decreases the objective. At the terminal
index `terminalIndex`, either Algorithm 3.5.2 returns the stop branch in the small-gradient
case or the computed line-search step fails to decrease `f` after the terminal Step 6
update. -/
structure NegativeCurvatureDirectionMethodRun (n : ℕ)
    (f : NegativeCurvaturePoint n → ℝ) where
  ε : ℝ
  x0 : NegativeCurvaturePoint n
  x : ℕ → NegativeCurvaturePoint n
  g : ℕ → NegativeCurvaturePoint n
  G : ℕ → Matrix (Fin n) (Fin n) ℝ
  L : ℕ → Matrix (Fin n) (Fin n) ℝ
  dDiag : ℕ → Fin n → ℝ
  eDiag : ℕ → Fin n → ℝ
  pivotStep : ∀ k : ℕ, NegativeCurvaturePivotStep (L k) (dDiag k) (eDiag k)
  d : ℕ → NegativeCurvaturePoint n
  α : ℕ → ℝ
  terminalIndex : ℕ
  x_zero : x 0 = x0
  gradient_eq : ∀ k : ℕ, k ≤ terminalIndex → g k = gradient f (x k)
  hessian :
    ∀ k : ℕ, k ≤ terminalIndex →
      HasFDerivAt (gradient f)
        (((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
              NegativeCurvaturePoint n →L[ℝ] NegativeCurvaturePoint n) (G k)))
        (x k)
  correction_nonneg :
    ∀ k : ℕ, k ≤ terminalIndex → ∀ i : Fin n, 0 ≤ eDiag k i
  factorization :
    ∀ k : ℕ, k ≤ terminalIndex →
      G k + Matrix.diagonal (eDiag k) = modifiedCholeskySystemMatrix (L k) (dDiag k)
  iterateDirection :
    ∀ k : ℕ, k < terminalIndex →
      NegativeCurvatureDirectionStep ε (g k) (L k) (dDiag k) (eDiag k) (pivotStep k) (d k)
  update :
    ∀ k : ℕ, k < terminalIndex → x (k + 1) = x k + α k • d k
  strictDecrease :
    ∀ k : ℕ, k < terminalIndex → f (x (k + 1)) < f (x k)
  terminal :
    negativeCurvatureTerminalSmallGradient
        ε (g terminalIndex) (L terminalIndex) (dDiag terminalIndex) (eDiag terminalIndex)
        (pivotStep terminalIndex) ∨
      negativeCurvatureTerminalLineSearchFailure
        f ε x g L dDiag eDiag pivotStep d α terminalIndex

/-- A run of the negative-curvature direction method can be used as its sequence of iterates. -/
instance {n : ℕ} {f : NegativeCurvaturePoint n → ℝ} :
    CoeFun (NegativeCurvatureDirectionMethodRun n f) (fun _ ↦ ℕ → NegativeCurvaturePoint n) where
  coe A := A.x

namespace NegativeCurvatureDirectionMethodRun

/-- The algorithm stops at `k` when either Algorithm 3.5.2 cannot produce a negative-curvature
direction in the small-gradient branch or the computed line-search step does not decrease `f`. -/
def terminatedAt {n : ℕ} {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f) (k : ℕ) : Prop :=
  negativeCurvatureTerminalSmallGradient
      A.ε (A.g k) (A.L k) (A.dDiag k) (A.eDiag k) (A.pivotStep k) ∨
    negativeCurvatureTerminalLineSearchFailure
      f A.ε A.x A.g A.L A.dDiag A.eDiag A.pivotStep A.d A.α k

/-- Unfolding formula for the termination predicate. -/
@[simp] theorem terminatedAt_iff {n : ℕ} {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f) (k : ℕ) :
    A.terminatedAt k ↔
      negativeCurvatureTerminalSmallGradient
          A.ε (A.g k) (A.L k) (A.dDiag k) (A.eDiag k) (A.pivotStep k) ∨
        negativeCurvatureTerminalLineSearchFailure
          f A.ε A.x A.g A.L A.dDiag A.eDiag A.pivotStep A.d A.α k :=
  Iff.rfl

/-- At every nonterminal index, the recorded run carries the direction branch, iterate update,
and strict decrease clauses from Steps 4-7. -/
theorem step {n : ℕ} {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f) {k : ℕ}
    (hk : k < A.terminalIndex) :
    NegativeCurvatureDirectionStep
        A.ε (A.g k) (A.L k) (A.dDiag k) (A.eDiag k) (A.pivotStep k) (A.d k) ∧
      A.x (k + 1) = A.x k + A.α k • A.d k ∧
      f (A.x (k + 1)) < f (A.x k) := by
  exact ⟨A.iterateDirection k hk, A.update k hk, A.strictDecrease k hk⟩

/-- A recorded run satisfies the terminal stopping condition at its terminal index. -/
theorem terminatedAt_terminalIndex {n : ℕ} {f : NegativeCurvaturePoint n → ℝ}
    (A : NegativeCurvatureDirectionMethodRun n f) :
    A.terminatedAt A.terminalIndex := by
  simpa [terminatedAt] using A.terminal

end NegativeCurvatureDirectionMethodRun

end
