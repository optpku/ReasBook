/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_56

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

/- Definition 7.57 lies in Chapter 7's barrier-subgradient gap-function domain.

Sampled owner-style declarations:
- `AffineVariationalInequalityProblem.gapFunction` in `Chap06/Definition_6_18`, the chapter
  pattern of keeping gap objects as the primary owner and deriving only thin expansion API;
- `maximalValueOn` in `Definition_7_56`, the nearby Chapter 7 faithful `EReal` maximization owner
  whose raw `sSup` formula lives only in a companion theorem;
- `DualBarrierSubgradientMethod` in `Algorithm_7_12`, the source-facing owner of the Chapter 7
  iterates, stepsizes, and chosen subgradients.

Best owner abstraction:
- source-facing: Definition 7.57's gap function `ℓ_k` and its maximal gap `ℓ_k⋆`;
- core/canonical: `barrierSubgradientGapFunction`, `barrierSubgradientMaximalGap`, and
  `barrierSubgradientWeightSum`;
- bridge/view: the method-specific views `DualBarrierSubgradientMethod.gapFunction` and
  `DualBarrierSubgradientMethod.maximalGap`, together with the explicit unfolding lemmas below.

Primitive data:
- a feasible set `P : Set E`;
- iterates `x : ℕ → P`;
- chosen subgradients `g_i`;
- weights `lam : ℕ → ℝ`;
- an index `k : ℕ`.

Derived API:
- evaluation of `barrierSubgradientGapFunction` at a feasible point;
- expansion of `barrierSubgradientMaximalGap` as a faithful `EReal` supremum;
- the method-level bridge from `DualBarrierSubgradientMethod` to the generic owners.

The previous arrangement made the generic gap owners live in `Theorem_7_15`, even though they are
the owner declarations for Definition 7.57 and are already needed by the upstream maximal-gap
machinery of Theorem 7.14. This refinement restores the owner layer here and leaves Theorem 7.15
to state only the explicit-rate theorem built on top of it.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

/-- Definition 7.57 (1): given iterates `x_i ∈ P`, chosen subgradients `g_i`, and weights
`λ_i`, the gap function `ℓ_k` is the weighted affine sum
`ℓ_k(y) = ∑_{i=0}^k λ_i ⟪g_i, y - x_i⟫`. -/
def barrierSubgradientGapFunction
    {P : Set E} (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ) : P → ℝ :=
  fun y ↦
    ∑ i ∈ Finset.range (k + 1), lam i * inner ℝ (subgradient i) ((y : E) - (x i : E))

/-- Definition 7.57 (2): the associated maximal gap `ℓ_k⋆` is the maximal value of `ℓ_k` over
`P`, formalized through the Chapter 7 `EReal`-valued maximization owner. -/
def barrierSubgradientMaximalGap
    {P : Set E} (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ) : EReal :=
  maximalValueOn (Set.univ : Set P) (barrierSubgradientGapFunction x subgradient lam k)

/-- The partial weight sum `S_k = ∑_{i=0}^k λ_i` attached to the barrier-subgradient gap
normalization. -/
def barrierSubgradientWeightSum (lam : ℕ → ℝ) (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun i ↦ lam i

/-- Expanding `barrierSubgradientWeightSum λ k` gives the finite sum `∑_{i=0}^k λ_i`. -/
theorem barrierSubgradientWeightSum_def (lam : ℕ → ℝ) (k : ℕ) :
    barrierSubgradientWeightSum lam k =
      Finset.sum (Finset.range (k + 1)) fun i ↦ lam i :=
  rfl

/-- Evaluating `barrierSubgradientGapFunction x g λ k` at `y ∈ P` gives the sum
`∑_{i=0}^k λ_i ⟪g_i, y - x_i⟫`. -/
theorem barrierSubgradientGapFunction_apply
    {P : Set E} (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ) (y : P) :
    barrierSubgradientGapFunction x subgradient lam k y =
      ∑ i ∈ Finset.range (k + 1), lam i * inner ℝ (subgradient i) ((y : E) - (x i : E)) :=
  rfl

/-- Expanding `barrierSubgradientMaximalGap x g λ k` gives the faithful `EReal` supremum of the
gap function `ℓ_k`. -/
theorem barrierSubgradientMaximalGap_def
    {P : Set E} (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ) :
    barrierSubgradientMaximalGap x subgradient lam k =
      sSup
        (Set.range
          fun y : P ↦ ((barrierSubgradientGapFunction x subgradient lam k y : ℝ) : EReal)) :=
  by
    rw [barrierSubgradientMaximalGap, maximalValueOn_eq_sSup_image]
    simp

end

namespace DualBarrierSubgradientMethod

/-- The chosen primal subgradient vector along the iterate sequence `x_k`. -/
def iterateSubgradient
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) : ℕ → E :=
  fun k ↦ method.subgradient (method k)

/-- The gap function `ℓ_k` attached to the actual dual barrier subgradient method. -/
def gapFunction
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) : P → ℝ :=
  barrierSubgradientGapFunction method method.iterateSubgradient
    (fun i ↦ (method.stepSize i : ℝ)) k

/-- The maximal gap `ℓ_k⋆` attached to the actual dual barrier subgradient method. -/
def maximalGap
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) : EReal :=
  barrierSubgradientMaximalGap method method.iterateSubgradient
    (fun i ↦ (method.stepSize i : ℝ)) k

/-- Evaluating the iterate-subgradient sequence recovers the chosen subgradient at the current
iterate. -/
theorem iterateSubgradient_eq
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    method.iterateSubgradient k = method.subgradient (method k) :=
  rfl

/-- Evaluating `method.gapFunction k` at `y ∈ P` gives the weighted subgradient sum from the
textbook definition of `ℓ_k`. -/
theorem gapFunction_apply
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) (y : P) :
    method.gapFunction k y =
      ∑ i ∈ Finset.range (k + 1),
        (method.stepSize i : ℝ) *
          inner ℝ (method.iterateSubgradient i) ((y : E) - (method i : E)) :=
  rfl

/-- Expanding `method.maximalGap k` recovers the generic maximal-gap owner applied to the method's
chosen subgradient data. -/
theorem maximalGap_eq
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    method.maximalGap k =
      barrierSubgradientMaximalGap method method.iterateSubgradient
        (fun i ↦ (method.stepSize i : ℝ)) k :=
  rfl

end DualBarrierSubgradientMethod

end
