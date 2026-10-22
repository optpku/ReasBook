/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_50
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_53

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Algorithm 7.12 lies in the chapter's barrier-subgradient / concave-support domain.

Mandatory domain-style sampling:
- `IsConcaveSubgradientAt` and `isConcaveSubgradientAt_iff` in `Definition_7_50`, the Chapter 7
  owner for concave subgradients;
- `Argmaxβ` and `mem_Argmaxβ_iff` in `Definition_7_53`, the Chapter 7 owner of the auxiliary
  barrier-smoothed maximization problem solved by `u^*_β(s)`;
- `supportFunctionApproximation_hasFDerivAt_of_unique_argmax` in `Proposition_7_28`, the nearby
  unique-argmax bridge showing why the auxiliary maximizer must stay tied to `Argmaxβ`;
- `PrimalUpdateScheme` in `Algorithm_7_13`, the neighboring source-facing recursive algorithm
  owner.

Best owner abstraction:
- source-facing: `DualBarrierSubgradientMethod`, with the textbook dual recursion and primal
  iterates `x_k = u^*_{β_k}(s_k)`;
- core/canonical: `Argmaxβ` for the auxiliary maximizer and `IsConcaveSubgradientAt` for the
  concave subgradient predicate;
- bridge/view: `dualSubgradient`, obtained from the primal subgradient vector by the canonical
  strong-dual embedding `InnerProductSpace.toDualMap`.

Primitive data:
- the feasible set `P`, concave objective `f`, barrier term `F`, auxiliary maximizer map `uStar`
  together with its canonical `Argmaxβ` membership and uniqueness data, a primal subgradient field,
  and positive parameter sequences.

Derived API:
- the StrongDual-valued bridge `dualSubgradient`;
- the recursively defined dual orbit `s₀, s₁, s₂, ...`;
- the primal iterate view `iterate`;
- the canonical maximality theorem `uStar_isMaxOn`;
- the textbook dual recursion theorem `dualIterate_succ_eq`.

The previous version weakened the textbook object `u^*_β(s)` to an arbitrary feasible-point
selector and also reused the colliding top-level owner name `BarrierSubgradientMethod`, already
taken later in `Algorithm_7_14`. This refinement keeps Algorithm 7.12 source-facing while making
the auxiliary solver canonical through `Argmaxβ` and moving the StrongDual presentation to a
derived bridge layer.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The dual update `s ↦ s + λ ∇f(u^*_β(s))` used in Algorithm 7.12. -/
def dualBarrierSubgradientUpdate
    {P : Set E}
    (uStar : {β : ℝ // 0 < β} → StrongDual ℝ E → P)
    (dualSubgradient : P → StrongDual ℝ E)
    (β : {β : ℝ // 0 < β}) (stepSize : ℝ)
    (s : StrongDual ℝ E) : StrongDual ℝ E :=
  s + stepSize • dualSubgradient (uStar β s)

-- Proof sketch: unfold `dualBarrierSubgradientUpdate`.
/-- Evaluating `dualBarrierSubgradientUpdate uStar dualSubgradient β stepSize s` recovers the
textbook dual update `s + λ ∇f(u^*_β(s))`. -/
theorem dualBarrierSubgradientUpdate_eq
    {P : Set E}
    (uStar : {β : ℝ // 0 < β} → StrongDual ℝ E → P)
    (dualSubgradient : P → StrongDual ℝ E)
    (β : {β : ℝ // 0 < β}) (stepSize : ℝ)
    (s : StrongDual ℝ E) :
    dualBarrierSubgradientUpdate uStar dualSubgradient β stepSize s =
      s + stepSize • dualSubgradient (uStar β s) :=
  rfl

/-- Algorithm 7.12: for a feasible set `P ⊆ E`, a concave function `f` on `P`, a barrier term
`F`, a canonical auxiliary maximizer `u^*_β(s)` for the owner `Argmaxβ P F β s`, and an available
subgradient map `∇f`, a dual barrier subgradient method is determined by positive parameter
sequences `β₀, β₁, β₂, ...` and `λ₀, λ₁, λ₂, ...`; the dual iterates
`s₀, s₁, s₂, ... ∈ E*` are then defined recursively by `s₀ = 0`,
`x_k = u^*_{β_k}(s_k)`, and
`s_{k+1} = s_k + λ_k ∇f(x_k)` for every `k`. -/
structure DualBarrierSubgradientMethod (P : Set E) (f : E → ℝ) where
  /-- The barrier/prox term used in the auxiliary maximization problem `Argmaxβ`. -/
  F : E → ℝ
  /-- The canonical auxiliary maximizer `u^*_β(s)` for the barrier-smoothed support problem. -/
  uStar : {β : ℝ // 0 < β} → StrongDual ℝ E → P
  /-- Each chosen point is the canonical maximizer of the auxiliary problem owned by `Argmaxβ`. -/
  uStar_argmax :
    ∀ (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E),
      (uStar β s : E) ∈ Argmaxβ P F β s
  /-- The auxiliary problem has the chosen point as its unique maximizer. -/
  uStar_unique :
    ∀ (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) {u : E},
      u ∈ Argmaxβ P F β s → u = (uStar β s : E)
  /-- The objective `f` is concave on the feasible set `P`. -/
  concaveOn_objective : ConcaveOn ℝ P f
  /-- The available primal subgradient vector `x ↦ ∇f(x)` on `P`. -/
  subgradient : P → E
  /-- Each chosen vector is a genuine concave subgradient of `f` at the corresponding feasible
  point. -/
  subgradient_spec :
    ∀ x : P, IsConcaveSubgradientAt f (x : E) (subgradient x)
  /-- The positive barrier parameters `β₀, β₁, β₂, ...`. -/
  beta : ℕ → {β : ℝ // 0 < β}
  /-- The positive stepsizes `λ₀, λ₁, λ₂, ...`. -/
  stepSize : ℕ → {t : ℝ // 0 < t}

namespace DualBarrierSubgradientMethod

/-- The StrongDual-valued bridge of the primal subgradient field obtained from the Riesz map. -/
def dualSubgradient
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) : P → StrongDual ℝ E :=
  fun x ↦ InnerProductSpace.toDualMap ℝ E (method.subgradient x)

/-- The dual orbit `s₀, s₁, s₂, ...` of Algorithm 7.12 is defined recursively from `s₀ = 0`
and the textbook update `s ↦ s + λ ∇f(u^*_β(s))`. -/
def dualIterate
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) : ℕ → StrongDual ℝ E
  | 0 => 0
  | k + 1 =>
      dualBarrierSubgradientUpdate method.uStar method.dualSubgradient
        (method.beta k) (method.stepSize k : ℝ) (dualIterate method k)

/-- The primal iterate `x_k = u^*_{β_k}(s_k)` attached to the current dual iterate `s_k`. -/
def iterate
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) : P :=
  method.uStar (method.beta k) (method.dualIterate k)

/-- A dual barrier subgradient method can be used as its primal iterate sequence
`x₀, x₁, x₂, ...`. -/
instance
    {P : Set E} {f : E → ℝ} :
    CoeFun (DualBarrierSubgradientMethod P f) (fun _ ↦ ℕ → P) where
  coe method := method.iterate

-- Proof sketch: unfold `DualBarrierSubgradientMethod.dualSubgradient`.
/-- Evaluating `method.dualSubgradient x` applies the Riesz map to the primal subgradient vector
`method.subgradient x`. -/
theorem dualSubgradient_eq
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (x : P) :
    method.dualSubgradient x = InnerProductSpace.toDualMap ℝ E (method.subgradient x) :=
  rfl

/-- The recursive dual orbit starts from `s₀ = 0`. -/
@[simp] theorem dualIterate_zero
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) :
    method.dualIterate 0 = 0 :=
  rfl

/-- The recursive dual orbit satisfies the textbook one-step update. -/
@[simp] theorem dualIterate_succ
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    method.dualIterate (k + 1) =
      dualBarrierSubgradientUpdate method.uStar method.dualSubgradient
        (method.beta k) (method.stepSize k : ℝ) (method.dualIterate k) :=
  rfl

-- Proof sketch: unfold `DualBarrierSubgradientMethod.iterate`.
/-- Evaluating `method.iterate k` recovers the textbook formula `x_k = u^*_{β_k}(s_k)`. -/
theorem iterate_eq
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    method.iterate k = method.uStar (method.beta k) (method.dualIterate k) :=
  rfl

-- Proof sketch: use the field `method.uStar_argmax` and the canonical owner bridge
-- `mem_Argmaxβ_iff` to recover the textbook maximizer sentence for the chosen point.
/-- The auxiliary point `u^*_β(s)` attains the maximum in the canonical barrier-smoothed owner
problem for every choice of base point `x₀`. -/
theorem uStar_isMaxOn
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f)
    (x0 : E) (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) :
    IsMaxOn
      (fun v : E ↦ s (v - x0) - β * (method.F v - method.F x0))
      P
      (method.uStar β s) := by
  have hscore :
      IsMaxOn (fun v : E ↦ s v - β * method.F v) P (method.uStar β s : E) := by
    -- Route correction: `mem_Argmaxβ_iff` needs an analytic-center base point, while the
    -- textbook maximizer statement here must hold for an arbitrary shift `x₀`. Unpack
    -- `Argmaxβ` directly to the raw score maximizer before reintroducing the constant shift.
    have hu : (method.uStar β s : E) ∈ Argmaxβ P method.F β s :=
      method.uStar_argmax β s
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hu
    rcases hu with ⟨_, hmax⟩
    simpa [smoothedPrimalObjectiveMaximand] using hmax
  -- Reinsert the constant base-point shift to recover the textbook payoff.
  exact
    (isMaxOn_shifted_score_iff_textbook_payoff
      (hatP := P) (F := method.F) (x0 := x0) (β := β) (s := s)
      (u := (method.uStar β s : E))).mp hscore

-- Proof sketch: apply the uniqueness field of `method`.
/-- Any point in the canonical auxiliary argmax owner agrees with the chosen point
`u^*_β(s)`. -/
theorem eq_uStar_of_mem_argmax
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f)
    (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) {u : E}
    (hu : u ∈ Argmaxβ P method.F β s) :
    u = (method.uStar β s : E) :=
  method.uStar_unique β s hu

-- Proof sketch: rewrite `method.dualIterate_succ k` and unfold
-- `dualBarrierSubgradientUpdate`, `DualBarrierSubgradientMethod.dualSubgradient`,
-- and `DualBarrierSubgradientMethod.iterate`.
/-- The dual recursion can be written in the textbook form
`s_{k+1} = s_k + λ_k ∇f(x_k)` with `x_k = method.iterate k`. -/
theorem dualIterate_succ_eq
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    method.dualIterate (k + 1) =
      method.dualIterate k + (method.stepSize k : ℝ) • method.dualSubgradient (method.iterate k) :=
  by
    simp [DualBarrierSubgradientMethod.iterate, dualBarrierSubgradientUpdate]

end DualBarrierSubgradientMethod
