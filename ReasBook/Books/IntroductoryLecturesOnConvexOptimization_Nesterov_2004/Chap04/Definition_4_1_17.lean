/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {X : Type u}

/- Definition 4.1.17 lies in the cubic-regularization backtracking domain.

Relevant declarations sampled before refining:
* `RegularizedNewton.acceptingParameters` and
  `RegularizedNewton.mem_acceptingParameters_iff` in `Definition_4_1_16`, the canonical owner
  of the acceptance condition for a trial regularization parameter;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, which keeps the
  source-facing least stage directly as an `IsLeast` owner;
* `stopIndexAt` / `stopIndexAt_isLeast` in `Chap02/Algorithm_2_11`, the project's local
  `Nat.find` pattern for first accepted indices;
* `Nat.isLeast_find` in mathlib, the standard least-natural-number API.

Best owner abstraction:
* source-facing: the set of accepted backtracking exponents `i` for which `2^i M_k` is an
  accepting parameter, together with its least element `i_k`;
* core/canonical: `RegularizedNewton.acceptingParameters f stepMap modelValue xk` and
  `IsLeast (acceptingExponents ...) iₖ`;
* bridge/view: `mem_acceptingExponents_iff`.

Primitive data:
* the current regularization estimate `M_k`;
* existence of an accepted backtracking exponent.

Derived API:
* minimality and acceptance of the chosen exponent;
* failure of all smaller exponents;
* the accepted regularization, next iterate, and next regularization;
* the witness-free bridge `IsNextRegularization` for downstream trajectory statements.

The interval condition `M_k ∈ [L₀, 2L]` remains theorem-level auxiliary data downstream, rather
than primitive owner data for the intrinsic update objects themselves. -/

namespace CubicRegularizationBacktracking

open RegularizedNewton

variable (f : X → ℝ) (stepMap : ℝ → X → X) (modelValue : ℝ → X → ℝ) (xk : X) (Mk : ℝ)

/-- The accepted backtracking exponents are exactly the natural numbers `i` such that the trial
parameter `2^i M_k` belongs to the canonical acceptance set at `x_k`. -/
def acceptingExponents : Set ℕ :=
  { i | (2 : ℝ) ^ i * Mk ∈ acceptingParameters f stepMap modelValue xk }

/-- Membership in `acceptingExponents` is exactly the regularized-Newton acceptance inequality for
the trial parameter `2^i M_k`. -/
@[simp] theorem mem_acceptingExponents_iff
    (i : ℕ) :
    i ∈ acceptingExponents f stepMap modelValue xk Mk ↔
      f (stepMap ((2 : ℝ) ^ i * Mk) xk) ≤ modelValue ((2 : ℝ) ^ i * Mk) xk := by
  simp [acceptingExponents]

/-- Definition 4.1.17: `i_k` is the least backtracking exponent whose trial parameter
`2^i M_k` satisfies the acceptance inequality. -/
noncomputable def index
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    ℕ :=
  let _ : DecidablePred (· ∈ acceptingExponents f stepMap modelValue xk Mk) := Classical.decPred _
  Nat.find hAccepts

/-- The chosen exponent `i_k` is least among all accepted backtracking exponents. -/
theorem index_isLeast
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    IsLeast
      (acceptingExponents f stepMap modelValue xk Mk)
      (index f stepMap modelValue xk Mk hAccepts) := by
  classical
  let _ : DecidablePred (· ∈ acceptingExponents f stepMap modelValue xk Mk) := Classical.decPred _
  simpa [index] using Nat.isLeast_find hAccepts

/-- The least backtracking exponent `i_k` belongs to the accepted-exponent set. -/
theorem index_mem_acceptingExponents
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    index f stepMap modelValue xk Mk hAccepts ∈
      acceptingExponents f stepMap modelValue xk Mk := by
  simpa using (index_isLeast f stepMap modelValue xk Mk hAccepts).1

/-- The accepted regularization parameter `hat M_k = 2^i_k M_k`. -/
def acceptedRegularization
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    ℝ :=
  (2 : ℝ) ^ index f stepMap modelValue xk Mk hAccepts * Mk

/-- The next iterate `x_(k+1) = T_(hat M_k)(x_k)` selected by the least accepted exponent. -/
def nextIterate
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    X :=
  stepMap (acceptedRegularization f stepMap modelValue xk Mk hAccepts) xk

/-- The next regularization estimate `M_(k+1) = max{L0, hat M_k / 2}`. -/
def nextRegularization
    (L0 : ℝ)
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    ℝ :=
  max L0 (acceptedRegularization f stepMap modelValue xk Mk hAccepts / 2)

/-- The conservative update `nextRegularization` is independent of which proof of acceptance
existence is supplied. -/
theorem nextRegularization_eq
    (L0 : ℝ)
    (hAccepts hAccepts' : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    nextRegularization f stepMap modelValue xk Mk L0 hAccepts =
      nextRegularization f stepMap modelValue xk Mk L0 hAccepts' := by
  have h : hAccepts = hAccepts' := Subsingleton.elim _ _
  subst h
  rfl

/-- A value `Mk'` is the conservative next regularization estimate if it agrees with the canonical
update for some accepted backtracking witness. The witness stays internal because
`nextRegularization` is proof-irrelevant in that argument. -/
def IsNextRegularization
    (L0 Mk' : ℝ) : Prop :=
  ∃ hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty,
    Mk' = nextRegularization f stepMap modelValue xk Mk L0 hAccepts

/-- Any witness-free conservative update can be evaluated against any proof that an accepted
backtracking exponent exists. -/
theorem IsNextRegularization.eq
    {L0 Mk' : ℝ}
    (hMk' : IsNextRegularization f stepMap modelValue xk Mk L0 Mk')
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    Mk' = nextRegularization f stepMap modelValue xk Mk L0 hAccepts := by
  rcases hMk' with ⟨hAccepts', rfl⟩
  exact nextRegularization_eq f stepMap modelValue xk Mk L0 hAccepts' hAccepts

-- Proof sketch: unfold `nextIterate` and `acceptedRegularization`, then use
-- `index_mem_acceptingExponents` through `mem_acceptingExponents_iff`.
/-- The next iterate selected by the least accepted exponent satisfies the accepted model
comparison. -/
theorem objective_nextIterate_le_modelValue
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    f (nextIterate f stepMap modelValue xk Mk hAccepts) ≤
      modelValue (acceptedRegularization f stepMap modelValue xk Mk hAccepts) xk := by
  simpa [nextIterate, acceptedRegularization] using
    (mem_acceptingExponents_iff
      f stepMap modelValue xk Mk
      (index f stepMap modelValue xk Mk hAccepts)).1
      (index_mem_acceptingExponents f stepMap modelValue xk Mk hAccepts)

-- Proof sketch: this is exactly the minimality clause in `index_isLeast`.
/-- Any smaller backtracking exponent lies outside the accepted-exponent set. -/
theorem not_mem_acceptingExponents_of_lt_index
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty)
    {j : ℕ} (hj : j < index f stepMap modelValue xk Mk hAccepts) :
    j ∉ acceptingExponents f stepMap modelValue xk Mk := by
  intro hjAccepts
  exact (not_le_of_gt hj) ((index_isLeast f stepMap modelValue xk Mk hAccepts).2 hjAccepts)

-- Proof sketch: unfold `nextRegularization`; it is the maximum of `L0` and another real number.
/-- The update rule always keeps the next regularization estimate at least `L0`. -/
theorem le_nextRegularization
    (L0 : ℝ)
    (hAccepts : (acceptingExponents f stepMap modelValue xk Mk).Nonempty) :
    L0 ≤ nextRegularization f stepMap modelValue xk Mk L0 hAccepts := by
  exact le_max_left _ _

end CubicRegularizationBacktracking
