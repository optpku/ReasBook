/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped InnerProductSpace

/-
Domain sampling for this file:
- primary domain: L-BFGS two-loop recursion on real inner-product spaces;
- sampled canonical/project declarations in this domain:
  `satisfiesQuasiNewtonEquation` from `Definition_5_1_extra_1.lean`,
  `GeneralQuasiNewtonMethod` from `Algorithm_5_1_1.lean`,
  `Matrix.toEuclideanLin`,
  `Matrix.toEuclideanLin.symm`;
- best owner abstraction: stored correction pairs together with an initial endomorphism on a
  real inner-product space, with the Euclidean matrix model used only as a downstream bridge;
- primitive data here: stored correction pairs and their ordered history;
- derived API here: the reciprocal curvature scalar, the backward loop, the forward loop, and
  the intrinsic two-loop recursion.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The reciprocal curvature scalar `ρ = ⟪s, y⟫_ℝ⁻¹` attached to one L-BFGS correction pair. -/
def lbfgsRho (s y : E) : ℝ :=
  (⟪s, y⟫_ℝ)⁻¹

/-- A stored L-BFGS correction pair consisting of the displacement `s` and the gradient
difference `y`. The reciprocal curvature scalar used in Algorithm 5.7.1 is derived canonically
as `ρ = ⟪s, y⟫_ℝ⁻¹`. -/
structure LBFGSHistoryEntry (E : Type*) where
  s : E
  y : E

/-- The reciprocal curvature scalar attached to a stored L-BFGS correction pair. -/
abbrev LBFGSHistoryEntry.rho (entry : LBFGSHistoryEntry E) : ℝ :=
  lbfgsRho entry.s entry.y

/-- The reverse loop in the L-BFGS two-loop recursion. For a history ordered from the oldest
stored pair to the newest one, this loop visits the entries in reverse order and returns the
final vector `q` together with the coefficients `αᵢ` listed again from oldest to newest. -/
def lbfgsBackwardLoop (q : E) (history : List (LBFGSHistoryEntry E)) : E × List ℝ :=
  history.reverse.foldl
    (fun (state : E × List ℝ) entry ↦
      let α := entry.rho * ⟪entry.s, state.1⟫_ℝ
      (state.1 - α • entry.y, α :: state.2))
    (q, [])

/-- The forward loop in the L-BFGS two-loop recursion. The history is ordered from the oldest
stored pair to the newest one, and the coefficient list is aligned with that same order. -/
def lbfgsForwardLoop
    (r : E) (history : List (LBFGSHistoryEntry E)) (alphas : List ℝ) : E :=
  (List.zip history alphas).foldl
    (fun r pair ↦
      let entry := pair.1
      let α := pair.2
      let β := entry.rho * ⟪entry.y, r⟫_ℝ
      r + (α - β) • entry.s)
    r

/-- Chapter05 Algorithm 5.7.1: the L-BFGS two-loop recursion for `Hₖ gₖ`. The input `history`
is the memory of stored correction pairs `(sᵢ, yᵢ)` ordered from `(s_{k-m}, y_{k-m})` to
`(s_{k-1}, y_{k-1})`, so its length is the memory parameter `m`. For each stored pair,
Algorithm 5.7.1 uses the derived reciprocal curvature scalar `ρᵢ := ⟪sᵢ, yᵢ⟫_ℝ⁻¹`.
Step 1 sets `q := gₖ`. Step 2 runs the reverse loop
`αᵢ := ρᵢ * ⟪sᵢ, q⟫_ℝ`, `q := q - αᵢ • yᵢ`. Step 3 sets `r := Hₖ⁽⁰⁾ q`.
Step 4 runs the forward loop `β := ρᵢ * ⟪yᵢ, r⟫_ℝ`, `r := r + (αᵢ - β) • sᵢ`.
On the Euclidean matrix model, the textbook matrix `Hₖ⁽⁰⁾` is recovered by passing through
`Matrix.toEuclideanLin`. -/
def lbfgsTwoLoopRecursion
    (Hk0 : E →ₗ[ℝ] E) (gk : E) (history : List (LBFGSHistoryEntry E)) : E :=
  let backward := lbfgsBackwardLoop gk history
  lbfgsForwardLoop (Hk0 backward.1) history backward.2

/-- For a single stored pair, the two-loop recursion expands to one backward update, one
application of `Hₖ^(0)`, and one forward correction. -/
theorem lbfgsTwoLoopRecursion_singleton
    (Hk0 : E →ₗ[ℝ] E) (gk : E) (entry : LBFGSHistoryEntry E) :
    lbfgsTwoLoopRecursion Hk0 gk [entry] =
      let α := entry.rho * ⟪entry.s, gk⟫_ℝ
      let q := gk - α • entry.y
      let r := Hk0 q
      let β := entry.rho * ⟪entry.y, r⟫_ℝ
      r + (α - β) • entry.s := rfl

end

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- On the Chapter 5 Euclidean model, the reciprocal curvature scalar is the reciprocal of the
usual dot product. -/
@[simp] theorem lbfgsRho_eq_dotProduct (s y : Point) :
    lbfgsRho s y = (dotProduct s y)⁻¹ := by
  simp [lbfgsRho, PiLp.inner_apply, dotProduct, mul_comm]

end
