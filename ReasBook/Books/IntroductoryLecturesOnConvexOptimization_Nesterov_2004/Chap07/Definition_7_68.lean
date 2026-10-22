/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_56

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {V : Type u} {A : Type v} [Fintype A]

/- Definition 7.68 lies in Chapter 7's multicommodity-flow / constrained-maximization domain.

Sampled owner-style declarations:
- `Matrix.mulVec` in mathlib, the canonical owner for balance equations on an incidence matrix
  `B : Matrix V A ℝ` with an arbitrary vertex type and a finite arc type;
- `maximalValueOn` and `maximalValueOn_eq_sSup_image` in `Chap07/Definition_7_56`, the chapter
  owner and expansion theorem for maximization values on explicit feasible sets;
- `ConvexMinimaxProblem E ι` in `Chap07/Definition_7_69`, the nearby chapter pattern for keeping
  source-facing data while parameterizing the finite family by an arbitrary finite type rather
  than a concrete `Fin` model.

Best owner abstraction:
- source-facing: the concurrent-flow feasibility conditions and maximal concurrency value on a
  network with vertex type `V`, finite arc type `A`, finite OD family `OD`, and incidence matrix
  `B : Matrix V A ℝ`;
- core/canonical: `Matrix.mulVec` for the balance equations and `maximalValueOn` on the feasible
  set of concurrency-flow states;
- bridge/view: `concurrentFlowFeasibleSet` and the `sSup` expansion theorem below.

Primitive data:
- the incidence matrix `B : Matrix V A ℝ`;
- the finite origin-destination family `OD`;
- the `OD`-indexed demand data and the arc-capacity data on `A`.

Derived API:
- the origin-destination demand vector;
- the feasibility predicate on a nonnegative concurrency level and an `OD`-indexed flow family;
- the feasible-state set and its canonical maximal-value owner.

The key refinement is to remove the raw supremum wheel and reuse `maximalValueOn`. The flow family
is indexed only by the actual origin-destination subtype `{p // p ∈ OD}`, the demand owner uses
that same commodity index, and the concurrency parameter is carried by `NNReal`. The previous
version hard-coded vertices and arcs as `Fin n` and `Fin m`; this refinement keeps only the
intrinsic network data and treats the `Fin` model as a specialization rather than as the
public owner.
-/

/-- The net supply-demand vector for an origin-destination pair `p = (i, j)` with demand
`demand p` is `demand p • (e_i - e_j)`. Defining it as the difference of the two singleton basis
vectors keeps the diagonal case `i = j` faithful as the zero vector. -/
def odDemandVector
    {OD : Finset (V × V)} (demand : {p // p ∈ OD} → NNReal) (p : {p // p ∈ OD}) : V → ℝ :=
  let _ : DecidableEq V := Classical.decEq V
  let src := p.1.1
  let dst := p.1.2
  Pi.single src (demand p : ℝ) - Pi.single dst (demand p : ℝ)

@[simp] theorem odDemandVector_diag
    {OD : Finset (V × V)} (demand : {p // p ∈ OD} → NNReal)
    (i : V) (hi : (i, i) ∈ OD) :
    odDemandVector demand ⟨(i, i), hi⟩ = 0 := by
  classical
  ext k
  simp [odDemandVector]

/-- A family of commodity flows indexed by the actual origin-destination pairs in `OD` is feasible
for concurrency level `λ` when each commodity satisfies its flow-balance equation, the aggregated
arc flow stays within capacity, and every commodity flow is coordinatewise nonnegative. -/
def IsConcurrentFlowFeasible
    (B : Matrix V A ℝ) (OD : Finset (V × V))
    (demand : {p // p ∈ OD} → NNReal) (capacity : A → NNReal)
    (concurrency : NNReal) (flows : {p // p ∈ OD} → A → ℝ) : Prop :=
  (∀ p : {p // p ∈ OD},
      Matrix.mulVec B (flows p) = concurrency • odDemandVector demand p) ∧
    (∀ a : A, OD.attach.sum (fun p ↦ flows p a) ≤ capacity a) ∧
      ∀ p : {p // p ∈ OD}, ∀ a : A, 0 ≤ flows p a

/-- Expanding concurrent-flow feasibility gives the flow-balance, capacity, and nonnegativity
constraints. -/
@[simp] theorem isConcurrentFlowFeasible_iff
    (B : Matrix V A ℝ) (OD : Finset (V × V))
    (demand : {p // p ∈ OD} → NNReal) (capacity : A → NNReal)
    (concurrency : NNReal) (flows : {p // p ∈ OD} → A → ℝ) :
    IsConcurrentFlowFeasible B OD demand capacity concurrency flows ↔
      (∀ p : {p // p ∈ OD},
        Matrix.mulVec B (flows p) = concurrency • odDemandVector demand p) ∧
        (∀ a : A, OD.attach.sum (fun p ↦ flows p a) ≤ capacity a) ∧
          ∀ p : {p // p ∈ OD}, ∀ a : A, 0 ≤ flows p a :=
  Iff.rfl

namespace IsConcurrentFlowFeasible

/-- For each `(i, j)` in `OD`, a feasible concurrent flow satisfies
`B fᵢⱼ = λ dᵢⱼ (eᵢ - eⱼ)`. -/
theorem flow_conservation
    {B : Matrix V A ℝ} {OD : Finset (V × V)}
    {demand : {p // p ∈ OD} → NNReal} {capacity : A → NNReal}
    {concurrency : NNReal} {flows : {p // p ∈ OD} → A → ℝ}
    (hfeasible : IsConcurrentFlowFeasible B OD demand capacity concurrency flows)
    (p : {p // p ∈ OD}) :
    Matrix.mulVec B (flows p) = concurrency • odDemandVector demand p :=
  hfeasible.1 p

/-- On each arc, the total routed flow of a feasible concurrent flow is bounded by capacity. -/
theorem capacity_bound
    {B : Matrix V A ℝ} {OD : Finset (V × V)}
    {demand : {p // p ∈ OD} → NNReal} {capacity : A → NNReal}
    {concurrency : NNReal} {flows : {p // p ∈ OD} → A → ℝ}
    (hfeasible : IsConcurrentFlowFeasible B OD demand capacity concurrency flows)
    (a : A) :
    OD.attach.sum (fun p ↦ flows p a) ≤ capacity a :=
  hfeasible.2.1 a

/-- Every commodity flow in a feasible concurrent flow is coordinatewise nonnegative. -/
theorem flow_nonneg
    {B : Matrix V A ℝ} {OD : Finset (V × V)}
    {demand : {p // p ∈ OD} → NNReal} {capacity : A → NNReal}
    {concurrency : NNReal} {flows : {p // p ∈ OD} → A → ℝ}
    (hfeasible : IsConcurrentFlowFeasible B OD demand capacity concurrency flows)
    (p : {p // p ∈ OD}) (a : A) :
    0 ≤ flows p a :=
  hfeasible.2.2 p a

end IsConcurrentFlowFeasible

/-- The feasible-state set of the concurrent-flow problem, with states `(λ, f)` given by a
nonnegative concurrency level and an `OD`-indexed commodity-flow family. -/
def concurrentFlowFeasibleSet
    (B : Matrix V A ℝ) (OD : Finset (V × V))
    (demand : {p // p ∈ OD} → NNReal) (capacity : A → NNReal) :
    Set (NNReal × ({p // p ∈ OD} → A → ℝ)) :=
  {state | IsConcurrentFlowFeasible B OD demand capacity state.1 state.2}

/-- Membership in `concurrentFlowFeasibleSet` means the flow-balance, capacity, and nonnegativity
constraints hold for the state `(λ, f)`. -/
@[simp] theorem mem_concurrentFlowFeasibleSet_iff
    (B : Matrix V A ℝ) (OD : Finset (V × V))
    (demand : {p // p ∈ OD} → NNReal) (capacity : A → NNReal)
    (state : NNReal × ({p // p ∈ OD} → A → ℝ)) :
    state ∈ concurrentFlowFeasibleSet B OD demand capacity ↔
      (∀ p : {p // p ∈ OD},
        Matrix.mulVec B (state.2 p) = state.1 • odDemandVector demand p) ∧
        (∀ a : A, OD.attach.sum (fun p ↦ state.2 p a) ≤ capacity a) ∧
          ∀ p : {p // p ∈ OD}, ∀ a : A, 0 ≤ state.2 p a :=
  Iff.rfl

/-- Definition 7.68: the maximal concurrent flow value is the maximal value of the nonnegative
concurrency coordinate on the feasible-state set, viewed through the chapter's faithful `EReal`
maximization owner. -/
def maximalConcurrentFlowValue
    (B : Matrix V A ℝ) (OD : Finset (V × V))
    (demand : {p // p ∈ OD} → NNReal) (capacity : A → NNReal) : EReal :=
  maximalValueOn (concurrentFlowFeasibleSet B OD demand capacity) fun state ↦ state.1

-- Proof sketch: unfold `maximalConcurrentFlowValue` and apply the chapter owner expansion theorem
-- `maximalValueOn_eq_sSup_image` to the real-valued concurrency coordinate `state ↦ (state.1 : ℝ)`.
/-- Expanding `maximalConcurrentFlowValue` gives the supremum of the feasible concurrency levels,
viewed as an `EReal` image of the feasible-state set. -/
theorem maximalConcurrentFlowValue_eq_sSup
    (B : Matrix V A ℝ) (OD : Finset (V × V))
    (demand : {p // p ∈ OD} → NNReal) (capacity : A → NNReal) :
    maximalConcurrentFlowValue B OD demand capacity =
      sSup
        ((fun state : NNReal × ({p // p ∈ OD} → A → ℝ) ↦ (state.1 : EReal)) ''
          concurrentFlowFeasibleSet B OD demand capacity) := by
  simpa [maximalConcurrentFlowValue] using
    maximalValueOn_eq_sSup_image
      (concurrentFlowFeasibleSet B OD demand capacity) (fun state ↦ (state.1 : ℝ))
