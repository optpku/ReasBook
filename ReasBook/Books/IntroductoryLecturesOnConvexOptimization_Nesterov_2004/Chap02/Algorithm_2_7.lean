/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: constrained type-II accelerated projected-gradient dynamics on a closed convex
set in a real Hilbert space.

Owner declarations sampled for this refinement:
* `constantStepSchemeIIAlphaNext` and `ConstantStepSchemeIIMomentumRecurrence` in
  `Algorithm_2_4`, which own the scalar update and the ambient type-II momentum recurrence
  interface;
* `gradientMapping` and `gradientMapping_isProjectionPointOn` in `Definition_2_35_1`, which own
  the projected-gradient step and its feasibility bridge, with step parameter
  `γ : NNRealˣ`;
* `simpleSetGradientMethod` in `Algorithm_2_6`, which shows the chapter pattern for keeping
  simple-set feasibility intrinsic via a recursive feasible-carrier trajectory.

Best owner abstraction:
* `ConstantStepSchemeIIMomentumRecurrence` for the ambient type-II momentum data, together with
  the owner projected step `gradientMapping`.

Source/core/bridge triage:
* source-facing: `constantStepSchemeIISimpleSet`;
* core/canonical: `gradientMapping`, `constantStepSchemeIIAlphaNext`, and
  `ConstantStepSchemeIIMomentumRecurrence`;
* bridge/view: the coordinate projections, the projected-step / momentum recursion lemmas, and
  the canonical momentum-recurrence conversion below.

Primitive data:
* the simple set `Q` with its closed / convex hypotheses;
* the objective `f`, the positive inverse-stepsize parameter `L`, and the reciprocal condition
  number `q_f`;
* the initial feasible point `x0 ∈ Q` and admissible initial scalar
  `α₀ ∈ (√q_f, constantStepSchemeIIAlphaUpper q_f]`, which determine the initial state.
  The one-step projected-gradient owner uses only the ambient nonemptiness of `Q`, which the
  trajectory section recovers canonically from the initial feasible point `x0 ∈ Q`.

Derived API:
* the one-step state update;
* the projected coordinate sequences `x_k`, `y_k`, and `α_k`;
* the recurrence equations and feasibility lemmas;
* the bridge to the owner momentum-recurrence interface.
-/

section

variable (QSet : Set E)
variable (hQ_closed : IsClosed QSet) (hQ_convex : Convex ℝ QSet)
variable (f : E → ℝ) (L : NNRealˣ) (qf : ℝ)

/-- The one-step state update of Algorithm 2.7 on triples `(x_k, y_k, α_k)` with `x_k ∈ Q`. -/
noncomputable def constantStepSchemeIISimpleSetStep
    :
    QSet × E × ℝ → QSet × E × ℝ :=
  fun state ↦
    let xk := state.1
    let yk := state.2.1
    let alphak := state.2.2
    let _ : Fact (Set.Nonempty QSet) := ⟨⟨(xk : E), xk.property⟩⟩
    let alphaNext := constantStepSchemeIIAlphaNext qf alphak
    let xNext : QSet :=
      ⟨x_Q[QSet; hQ_closed; hQ_convex | f; L](yk),
        (gradientMapping_isProjectionPointOn
          QSet Fact.out hQ_closed hQ_convex f L yk).1⟩
    let yNext :=
      (xNext : E) +
        ((alphak * (1 - alphak)) / (alphak ^ (2 : ℕ) + alphaNext)) •
          ((xNext : E) - (xk : E))
    (xNext, yNext, alphaNext)

section Trajectory

variable (x0 : QSet)
variable (alpha0 : Set.Ioc (Real.sqrt qf) (constantStepSchemeIIAlphaUpper qf))

/-- Algorithm 2.7: for a simple closed convex set `Q`, objective `f`, step parameter `L`,
reciprocal condition number `q_f`, initial feasible point `x₀ ∈ Q`, and admissible initial
scalar `α₀ ∈ (√q_f, 2 (3 + q_f) / (3 + √(21 + 4 q_f))]`, the recursive state
`(x_k, y_k, α_k)` starts from `(x₀, x₀, α₀)` and applies the projected step
`x_{k+1} = x_Q(y_k; L)`, the scalar update
`α_{k+1} = constantStepSchemeIIAlphaNext q_f α_k`, and the textbook type-II momentum formula
for `y_{k+1}`. The step parameter is stored at the owner level as the positive inverse-stepsize
datum `L : NNRealˣ`, matching the projected-gradient owner API. The textbook
`ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
noncomputable def constantStepSchemeIISimpleSet
    : ℕ → QSet × E × ℝ :=
  Nat.rec
    (x0, (x0 : E), (alpha0 : ℝ))
    (fun _ state ↦ constantStepSchemeIISimpleSetStep QSet hQ_closed hQ_convex f L qf state)

/-- The main iterate sequence `x_k` of the recursive simple-set type-II trajectory. -/
noncomputable def constantStepSchemeIISimpleSetX
    :
    ℕ → QSet :=
  fun k ↦
    (constantStepSchemeIISimpleSet QSet hQ_closed hQ_convex f L qf x0 alpha0 k).1

/-- The extrapolated sequence `y_k` of the recursive simple-set type-II trajectory. -/
noncomputable def constantStepSchemeIISimpleSetY
    :
    ℕ → E :=
  fun k ↦
    (constantStepSchemeIISimpleSet QSet hQ_closed hQ_convex f L qf x0 alpha0 k).2.1

/-- The scalar sequence `α_k` of the recursive simple-set type-II trajectory. -/
noncomputable def constantStepSchemeIISimpleSetAlpha
    :
    ℕ → ℝ :=
  fun k ↦
    (constantStepSchemeIISimpleSet QSet hQ_closed hQ_convex f L qf x0 alpha0 k).2.2

local notation "step" =>
  constantStepSchemeIISimpleSetStep QSet hQ_closed hQ_convex f L qf

local notation "state" =>
  constantStepSchemeIISimpleSet QSet hQ_closed hQ_convex f L qf x0 alpha0

local notation "xSeq" =>
  constantStepSchemeIISimpleSetX QSet hQ_closed hQ_convex f L qf x0 alpha0

local notation "ySeq" =>
  constantStepSchemeIISimpleSetY QSet hQ_closed hQ_convex f L qf x0 alpha0

local notation "alphaSeq" =>
  constantStepSchemeIISimpleSetAlpha QSet hQ_closed hQ_convex f L qf x0 alpha0

@[simp] theorem constantStepSchemeIISimpleSet_zero :
    state 0 = (x0, (x0 : E), (alpha0 : ℝ)) :=
  rfl

/-- The recursive simple-set type-II state satisfies the one-step state update law. -/
@[simp] theorem constantStepSchemeIISimpleSet_succ
    (k : ℕ) :
    state (k + 1) = step (state k) :=
  rfl

@[simp] theorem constantStepSchemeIISimpleSetX_zero :
    xSeq 0 = x0 :=
  rfl

@[simp] theorem constantStepSchemeIISimpleSetY_zero :
    ySeq 0 = (x0 : E) :=
  rfl

@[simp] theorem constantStepSchemeIISimpleSetAlpha_zero :
    alphaSeq 0 = (alpha0 : ℝ) :=
  rfl

section ShortProjectedStep

/-- The recursive simple-set type-II iterates satisfy the textbook projected step
`x_{k+1} = x_Q(y_k; L)`. -/
@[simp] theorem constantStepSchemeIISimpleSetX_succ
    (k : ℕ) :
    (xSeq (k + 1) : E) =
      x_Q[QSet; ⟨(x0 : E), x0.property⟩; hQ_closed; hQ_convex | f; L](ySeq k) :=
by
  change
    gradientMapping QSet ⟨(xSeq k : E), (xSeq k).property⟩ hQ_closed hQ_convex f (ySeq k) L =
      gradientMapping QSet ⟨(x0 : E), x0.property⟩ hQ_closed hQ_convex f (ySeq k) L
  exact
    congrArg
      (fun hQ_nonempty : Set.Nonempty QSet ↦
        gradientMapping QSet hQ_nonempty hQ_closed hQ_convex f (ySeq k) L)
      (Subsingleton.elim
        (⟨(xSeq k : E), (xSeq k).property⟩ : Set.Nonempty QSet)
        (⟨(x0 : E), x0.property⟩ : Set.Nonempty QSet))

end ShortProjectedStep

/-- The recursive simple-set type-II scalar sequence uses the canonical scheme-II update
`constantStepSchemeIIAlphaNext`. -/
@[simp] theorem constantStepSchemeIISimpleSetAlpha_succ
    (k : ℕ) :
    alphaSeq (k + 1) = constantStepSchemeIIAlphaNext qf (alphaSeq k) :=
  rfl

/-- The recursive simple-set type-II extrapolated points satisfy the textbook momentum update. -/
@[simp] theorem constantStepSchemeIISimpleSetY_succ
    (k : ℕ) :
    ySeq (k + 1) =
      (xSeq (k + 1) : E) +
        ((alphaSeq k * (1 - alphaSeq k)) / (alphaSeq k ^ (2 : ℕ) + alphaSeq (k + 1))) •
          ((xSeq (k + 1) : E) - (xSeq k : E)) :=
  rfl

/-- If `q_f ∈ [0, 1)`, then every scalar in the recursive simple-set type-II trajectory lies in
`(0, 1)`. -/
theorem constantStepSchemeIISimpleSetAlpha_mem_Ioo
    (hqf : qf ∈ Set.Ico (0 : ℝ) 1) :
    ∀ k : ℕ, alphaSeq k ∈ Set.Ioo (0 : ℝ) 1 := by
  intro k
  induction k with
  | zero =>
      simpa [constantStepSchemeIISimpleSetAlpha_zero] using
        (constantStepSchemeII_alpha_mem_Ioo_of_mem_Ioc alpha0.2 :
          (alpha0 : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
  | succ k hk =>
      simpa [constantStepSchemeIISimpleSetAlpha_succ] using
        constantStepSchemeIIAlphaNext_mem_Ioo hqf hk

/-- The recursive Algorithm 2.7 trajectory, viewed through the owner type-II momentum
recurrence API. -/
def constantStepSchemeIISimpleSetToMomentumRecurrence
    :
    ConstantStepSchemeIIMomentumRecurrence E QSet qf x0 (alpha0 : ℝ) := {
  x := xSeq
  y := ySeq
  alpha := alphaSeq
  x_zero := constantStepSchemeIISimpleSetX_zero QSet hQ_closed hQ_convex f L qf x0 alpha0
  y_zero := constantStepSchemeIISimpleSetY_zero QSet hQ_closed hQ_convex f L qf x0 alpha0
  alpha_zero := constantStepSchemeIISimpleSetAlpha_zero QSet hQ_closed hQ_convex f L qf x0 alpha0
  alpha_succ_equation := fun k ↦ by
    simpa [constantStepSchemeIISimpleSetAlpha_succ] using
      constantStepSchemeIIAlphaNext_satisfies_equation qf (alphaSeq k)
  y_succ := constantStepSchemeIISimpleSetY_succ QSet hQ_closed hQ_convex f L qf x0 alpha0
  }

end Trajectory

end
