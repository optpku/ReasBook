/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Order.Filter.AtTopBot.Basic

public section

namespace ParameterChoice

/-- Definition 7.33 (1). A regularization parameter selection method with
parameter sequence `α` is exactly optimal relative to a benchmark sequence
`αopt` when `α n = αopt n` for all sufficiently large `n`. Choosing
`αopt = αₑ` gives the source notion of e-optimality, while `αopt = αₚ` gives
the analogous p-optimality notion. -/
def IsExactOptimal (α αopt : ℕ → ℝ) : Prop :=
  α =ᶠ[Filter.atTop] αopt

/-- The source-style eventual-threshold characterization of
`IsExactOptimal`. -/
theorem IsExactOptimal_iff (α αopt : ℕ → ℝ) :
    IsExactOptimal α αopt ↔ ∃ n₀, ∀ n ≥ n₀, α n = αopt n := by
  change (∀ᶠ n in Filter.atTop, α n = αopt n) ↔
    ∃ n₀, ∀ n ≥ n₀, α n = αopt n
  exact Filter.eventually_atTop

/-- Definition 7.33 (2). A regularization parameter selection method with
parameter sequence `α` is asymptotically optimal relative to a benchmark
sequence `αopt` when `α` and `αopt` are asymptotically equivalent as
`n → ∞`. Choosing `αopt = αₑ` gives asymptotic e-optimality, and
`αopt = αₚ` gives the analogous p-optimality notion. -/
def IsAsymptoticallyOptimal (α αopt : ℕ → ℝ) : Prop :=
  Asymptotics.IsEquivalent Filter.atTop α αopt

/-- An asymptotically optimal parameter sequence is asymptotically equivalent
to its benchmark sequence. -/
theorem IsAsymptoticallyOptimal.isEquivalent {α αopt : ℕ → ℝ}
    (h : IsAsymptoticallyOptimal α αopt) :
    Asymptotics.IsEquivalent Filter.atTop α αopt :=
  h

/-- If two parameter sequences are asymptotically optimal relative to each
other, then either sequence converges to a limit exactly when the other does. -/
theorem IsAsymptoticallyOptimal.tendsto_nhds_iff
    {α αopt : ℕ → ℝ} {c : ℝ} (h : IsAsymptoticallyOptimal α αopt) :
    Filter.Tendsto α Filter.atTop (nhds c) ↔
      Filter.Tendsto αopt Filter.atTop (nhds c) :=
  Asymptotics.IsEquivalent.tendsto_nhds_iff h

/-- A regularization parameter sequence `α` is order-optimal with order
constant `r` relative to a benchmark sequence `αopt` when `r` is positive and
`α` is asymptotically equivalent to `fun n ↦ r * αopt n`. -/
def IsOrderOptimalWith (r : ℝ) (α αopt : ℕ → ℝ) : Prop :=
  0 < r ∧ Asymptotics.IsEquivalent Filter.atTop α (fun n ↦ r * αopt n)

/-- An order-optimality witness carries a positive order constant. -/
theorem IsOrderOptimalWith.pos {r : ℝ} {α αopt : ℕ → ℝ}
    (h : IsOrderOptimalWith r α αopt) : 0 < r :=
  h.1

/-- An order-optimality witness carries the corresponding asymptotic
equivalence. -/
theorem IsOrderOptimalWith.isEquivalent {r : ℝ} {α αopt : ℕ → ℝ}
    (h : IsOrderOptimalWith r α αopt) :
    Asymptotics.IsEquivalent Filter.atTop α (fun n ↦ r * αopt n) :=
  h.2

/-- The explicit positive-constant characterization of `IsOrderOptimalWith`. -/
theorem IsOrderOptimalWith_iff (r : ℝ) (α αopt : ℕ → ℝ) :
    IsOrderOptimalWith r α αopt ↔
      0 < r ∧ Asymptotics.IsEquivalent Filter.atTop α (fun n ↦ r * αopt n) := by
  -- The owner definition is exactly the displayed conjunction.
  rfl

/-- Definition 7.33 (3). A regularization parameter selection method with
parameter sequence `α` is order-optimal relative to a benchmark sequence
`αopt` when there exists a positive order constant `r` such that `α` is
asymptotically equivalent to `fun n ↦ r * αopt n` as `n → ∞`. Choosing
`αopt = αₑ` gives order e-optimality, and `αopt = αₚ` gives the analogous
p-optimality notion. -/
def IsOrderOptimal (α αopt : ℕ → ℝ) : Prop :=
  ∃ r : ℝ, IsOrderOptimalWith r α αopt

/-- The explicit positive-constant characterization of `IsOrderOptimal`. -/
theorem IsOrderOptimal_iff (α αopt : ℕ → ℝ) :
    IsOrderOptimal α αopt ↔
      ∃ r : ℝ, 0 < r ∧ Asymptotics.IsEquivalent Filter.atTop α (fun n ↦ r * αopt n) := by
  constructor
  · rintro ⟨r, hr, hEqv⟩
    exact ⟨r, hr, hEqv⟩
  · rintro ⟨r, hr, hEqv⟩
    exact ⟨r, hr, hEqv⟩

/-- Definition 7.33 (4). A regularization parameter selection method is
mean-square convergent when its expected squared estimation-error sequence tends
to `0` as `n → ∞`. -/
def IsMeanSquareConvergent (expectedSqError : ℕ → ℝ) : Prop :=
  Filter.Tendsto expectedSqError Filter.atTop (nhds (0 : ℝ))

/-- A mean-square convergent parameter choice has expected squared error
tending to `0`. -/
theorem IsMeanSquareConvergent.tendsto_zero {expectedSqError : ℕ → ℝ}
    (h : IsMeanSquareConvergent expectedSqError) :
    Filter.Tendsto expectedSqError Filter.atTop (nhds (0 : ℝ)) :=
  h

/-- Definition 7.33 (5). A regularization parameter selection method is
mean-square nonconvergent when its expected squared estimation-error sequence
does not tend to `0` as `n → ∞`. -/
def IsMeanSquareNonconvergent (expectedSqError : ℕ → ℝ) : Prop :=
  ¬ IsMeanSquareConvergent expectedSqError

/-- A mean-square nonconvergent parameter choice has expected squared error
that does not tend to `0`. -/
theorem IsMeanSquareNonconvergent.not_tendsto_zero {expectedSqError : ℕ → ℝ}
    (h : IsMeanSquareNonconvergent expectedSqError) :
    ¬ Filter.Tendsto expectedSqError Filter.atTop (nhds (0 : ℝ)) := by
  simpa [IsMeanSquareNonconvergent, IsMeanSquareConvergent] using h

/-- A parameter choice is mean-square nonconvergent as soon as its expected
squared error fails to be mean-square convergent. -/
theorem isMeanSquareNonconvergent_of_not_meanSquareConvergent
    {expectedSqError : ℕ → ℝ}
    (h : ¬ IsMeanSquareConvergent expectedSqError) :
    IsMeanSquareNonconvergent expectedSqError := by
  -- The owner definition of mean-square nonconvergence is the negated
  -- convergence statement.
  exact h

end ParameterChoice
