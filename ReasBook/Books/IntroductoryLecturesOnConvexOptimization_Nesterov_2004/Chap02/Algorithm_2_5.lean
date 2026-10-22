/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Algorithm 2.5 lives in the chapter's fixed-momentum accelerated-gradient domain on real Hilbert
spaces.

Sampled declarations in this domain:
* `gradientMethod` in `Algorithm_2_1`, the chapter pattern for a source-facing recursive
  trajectory;
* `simpleSetGradientMethod` in `Algorithm_2_6`, which likewise exposes a recursive algorithm and
  keeps the owner predicate as derived bridge API;
* `ConstantStepSchemeIIStep` and `ConstantStepSchemeIICore` in `Algorithm_2_4`, which show the
  chapter's canonical real-Hilbert-space owner style for accelerated recursive trajectories;
* `ConstantStepSchemeIIMomentumRecurrence` in `Algorithm_2_4`, the canonical upstream momentum
  owner;
* `ConstantStepSchemeIIIMomentumRecurrence.toConstantStepSchemeIIMomentumRecurrence` in
  `Proposition_2_12`, the bridge from the source-facing fixed-`β` data to that owner;
* `ConstantStepSchemeIII` in `Proposition_2_12`, the owner exact-step specialization used later
  for analysis.

Best owner abstractions:
* `ConstantStepSchemeIIIMomentumRecurrence E E qf x0` for the intrinsic fixed-momentum view;
* `ConstantStepSchemeIIMomentumRecurrence E E qf x0 (Real.sqrt qf)` for the canonical type-II
  momentum view obtained by adjoining the constant scalar sequence `α_k = √q_f`;
* `ConstantStepSchemeIII f L qf x0` for the source-facing exact-step view.

Source/core/bridge triage:
* `source-facing`: the recursive state trajectory `constantStepSchemeIII`;
* `core/canonical`: `ConstantStepSchemeIIIMomentumRecurrence`,
  `ConstantStepSchemeIIMomentumRecurrence`, and `ConstantStepSchemeIII`;
* `bridge/view`: the `toXxx` conversions below.

Primitive data:
* the objective `f`, the step parameter `L`, the reciprocal condition-number parameter `q_f`,
  and the initial point `x0`.

Derived API:
* the one-step state update map `constantStepSchemeIIIStep`;
* the projected coordinate sequences `x_k` and `y_k`;
* the zero/successor recurrences;
* the direct conversion of the recursive trajectory to the fixed-momentum owner, and then to the
  type-II momentum and exact-step owner structures once the side conditions `0 < L` and
  `q_f ∈ (0, 1]` are supplied.
-/

section

/-- The one-step state update of Algorithm 2.5 on pairs `(x_k, y_k)`. -/
noncomputable def constantStepSchemeIIIStep
    (f : E → ℝ) (L qf : ℝ) :
    E × E → E × E :=
  fun state ↦
    let xk := state.1
    let yk := state.2
    let xNext := yk - (1 / L) • ∇ f (yk)
    let yNext :=
      xNext + β[qf] • (xNext - xk)
    (xNext, yNext)

/-- Algorithm 2.5: the recursive scheme-III state trajectory `(x_k, y_k)` started from
`(x₀, y₀) = (x0, x0)` and updated by the exact gradient step
`x_{k+1} = y_k - (1 / L) ∇ f(y_k)` together with the fixed-momentum extrapolation
`y_{k+1} = x_{k+1} + β (x_{k+1} - x_k)`, where
`β = β[q_f]`. -/
noncomputable def constantStepSchemeIII
    (f : E → ℝ) (L qf : ℝ) (x0 : E) :
    ℕ → E × E
  | 0 => (x0, x0)
  | k + 1 => constantStepSchemeIIIStep f L qf (constantStepSchemeIII f L qf x0 k)

/-- The recursive scheme-III trajectory starts from the diagonal state `(x0, x0)`. -/
@[simp] theorem constantStepSchemeIII_zero
    (f : E → ℝ) (L qf : ℝ) (x0 : E) :
    constantStepSchemeIII f L qf x0 0 = (x0, x0) :=
  rfl

/-- One step of the recursive scheme-III trajectory is obtained by applying the update map to the
previous state. -/
@[simp] theorem constantStepSchemeIII_succ
    (f : E → ℝ) (L qf : ℝ) (x0 : E) (k : ℕ) :
    constantStepSchemeIII f L qf x0 (k + 1) =
      constantStepSchemeIIIStep f L qf (constantStepSchemeIII f L qf x0 k) :=
  rfl

/-- The main iterate sequence `x_k` of the recursive scheme-III trajectory. -/
noncomputable def constantStepSchemeIIIX
    (f : E → ℝ) (L qf : ℝ) (x0 : E) :
    ℕ → E :=
  fun k ↦ (constantStepSchemeIII f L qf x0 k).1

/-- The extrapolated sequence `y_k` of the recursive scheme-III trajectory. -/
noncomputable def constantStepSchemeIIIY
    (f : E → ℝ) (L qf : ℝ) (x0 : E) :
    ℕ → E :=
  fun k ↦ (constantStepSchemeIII f L qf x0 k).2

section Trajectory

variable (f : E → ℝ) (L qf : ℝ) (x0 : E)

local notation "state" => constantStepSchemeIII f L qf x0
local notation "xSeq" => constantStepSchemeIIIX f L qf x0
local notation "ySeq" => constantStepSchemeIIIY f L qf x0

/-- The recursive scheme-III trajectory starts from `x₀ = x0`. -/
@[simp] theorem constantStepSchemeIIIX_zero
    :
    xSeq 0 = x0 :=
  rfl

/-- The recursive scheme-III trajectory starts from `y₀ = x0`. -/
@[simp] theorem constantStepSchemeIIIY_zero
    :
    ySeq 0 = x0 :=
  rfl

/-- The recursive scheme-III iterates satisfy the textbook exact gradient-step update. -/
@[simp] theorem constantStepSchemeIIIX_succ
    (k : ℕ) :
    xSeq (k + 1) = ySeq k - (1 / L) • ∇ f (ySeq k) :=
  rfl

/-- The recursive scheme-III extrapolated points satisfy the fixed-momentum update. -/
@[simp] theorem constantStepSchemeIIIY_succ
    (k : ℕ) :
    ySeq (k + 1) = xSeq (k + 1) + β[qf] • (xSeq (k + 1) - xSeq k) :=
  rfl

/-- The recursive Algorithm 2.5 trajectory, viewed through the owner fixed-momentum recurrence
API. -/
def constantStepSchemeIIIToIIIMomentumRecurrence
    :
    ConstantStepSchemeIIIMomentumRecurrence E E qf x0 where
  x := constantStepSchemeIIIX f L qf x0
  y := constantStepSchemeIIIY f L qf x0
  x_zero := constantStepSchemeIIIX_zero f L qf x0
  y_zero := constantStepSchemeIIIY_zero f L qf x0
  y_succ := constantStepSchemeIIIY_succ f L qf x0

/-- The recursive Algorithm 2.5 trajectory, viewed through the canonical type-II momentum
owner by adjoining the constant scalar sequence `α_k = √q_f`. -/
def constantStepSchemeIIIToMomentumRecurrence
    (hqf : qf ∈ Set.Ioc (0 : ℝ) 1) :
    ConstantStepSchemeIIMomentumRecurrence E E qf x0 (Real.sqrt qf) :=
  ConstantStepSchemeIIIMomentumRecurrence.toConstantStepSchemeIIMomentumRecurrence
    (constantStepSchemeIIIToIIIMomentumRecurrence f L qf x0) hqf

/-- The recursive Algorithm 2.5 trajectory, viewed through the owner exact-step scheme-III API. -/
def constantStepSchemeIIIToScheme
    (hL : 0 < L) (hqf : qf ∈ Set.Ioc (0 : ℝ) 1) :
    ConstantStepSchemeIII f L qf x0 where
  toConstantStepSchemeIIIMomentumRecurrence :=
    constantStepSchemeIIIToIIIMomentumRecurrence f L qf x0
  L_pos := hL
  qf_mem_Ioc := hqf
  x_succ := constantStepSchemeIIIX_succ f L qf x0

/-- The owner exact-step scheme attached to `constantStepSchemeIII` has iterate sequence equal
to the first coordinate of the recursive state trajectory. -/
-- Proof sketch: unfold `constantStepSchemeIIIToScheme`; its `x` field is
-- `constantStepSchemeIIIX`, which is definitionally the first projection of
-- `constantStepSchemeIII`.
@[simp] theorem constantStepSchemeIIIToScheme_apply
    (hL : 0 < L) (hqf : qf ∈ Set.Ioc (0 : ℝ) 1) (k : ℕ) :
    constantStepSchemeIIIToScheme f L qf x0 hL hqf k =
      (constantStepSchemeIII f L qf x0 k).1 :=
  rfl

end Trajectory

end

end
