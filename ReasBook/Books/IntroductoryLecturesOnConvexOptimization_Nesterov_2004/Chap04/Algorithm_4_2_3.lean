/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Algorithm 4.2.3 lies in the accelerated cubic-Newton / restart-orbit domain.

Sampled owner-style declarations:
* `Function.iterate`, the canonical owner of autonomous discrete trajectories;
* `AcceleratedCubicNewtonMethod` in `Algorithm_4_2_2`, the chapter owner of the inner
  accelerated cubic-Newton dynamics started from a prescribed point;
* the `CoeFun`/iterate surface of `AcceleratedCubicNewtonMethod`, which turns each owner into its
  canonical sequence of iterates;
* `restartedAcceleratedCubicNewton_normCube_succ_le_exp_neg_one_mul` in `Lemma_4_2_7`, which
  records the restart lower bound on the same source-facing `σ₃`/`L₃` scalar data used by the
  restart contraction argument.

Best owner abstraction:
* source-facing: the restarted accelerated cubic-Newton outer sequence;
* core/canonical: the autonomous restart self-map
  `acceleratedCubicNewtonRestartMap innerMethod σ₃`, built from the inner owner family
  `(x : E) → AcceleratedCubicNewtonMethod f L3 x` together with the least natural block length
  above the source restart threshold;
* bridge/view: the textbook identities `y₀ = x₀`, `y_{k+1} = 𝓐_m(y_k)`, and
  `𝓐_m(x) = innerMethod x m`, recovered from `Function.iterate` and the owner coercion.

Primitive data:
* the objective `f`;
* the source-facing cubic-growth parameter `σ₃`;
* the Hessian-Lipschitz constant `L₃` used by the inner accelerated cubic-Newton owner family
  `(x : E) → AcceleratedCubicNewtonMethod f L3 x`;
* the starting point `x₀`.

Derived API:
* the real restart threshold `((24 e) / (σ₃ / L₃))^{1/3}`;
* the least natural block length above that threshold;
* the autonomous restart self-map `x ↦ 𝓐_m(x)`, written on the owner surface as
  `x ↦ innerMethod x m`;
* the restarted outer sequence as the canonical orbit of that restart map;
* the zeroth-iterate and successor identities.

The previous file mixed two incompatible layers: the restart period came from the canonical
condition number `γ₃(f)`, while the restart map itself was built from an arbitrary inner owner
`AcceleratedCubicNewtonMethod f L3 x`. This refinement keeps Algorithm 4.2.3 on the same
source-facing `σ₃`/`L₃` data as the restart analysis in Lemma 4.2.7, so the block length is tied
to the same `L₃` used by the inner method. The restart map is then derived from the canonical
inner method owner family, and the restarted method is the canonical `Function.iterate` orbit of
that restart map. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

variable {f : E → ℝ} {sigma3 : ℝ} {L3 : NNReal}

/-- The source restart threshold `((24 e) / (σ₃ / L₃))^{1/3} = (24 e * L₃ / σ₃)^{1/3}` used in
Lemma 4.2.7 and Algorithm 4.2.3. Writing it in the latter form ties the threshold directly to the
same `L₃` parameter carried by the inner accelerated cubic-Newton owner. -/
def acceleratedCubicNewtonRestartThreshold (sigma3 : ℝ) (L3 : NNReal) : ℝ :=
  Real.rpow ((((24 : ℝ) * Real.exp 1) * (L3 : ℝ)) / sigma3) (1 / 3 : ℝ)

/-- The restart length `m = ⌈((24 e) / (σ₃ / L₃))^{1/3}⌉₊`, i.e. the least natural block length
satisfying the source restart lower bound. -/
def acceleratedCubicNewtonRestartPeriod (sigma3 : ℝ) (L3 : NNReal) : ℕ :=
  Nat.ceil (acceleratedCubicNewtonRestartThreshold sigma3 L3)

/-- The canonical restart block length is at least the source threshold
`((24 e) / (σ₃ / L₃))^{1/3}` required by the restart-contraction estimates. -/
theorem acceleratedCubicNewtonRestartPeriod_lower_bound
    (sigma3 : ℝ) (L3 : NNReal) :
    acceleratedCubicNewtonRestartThreshold sigma3 L3 ≤
      (acceleratedCubicNewtonRestartPeriod sigma3 L3 : ℝ) := by
  simpa [acceleratedCubicNewtonRestartPeriod] using
    (Nat.le_ceil (acceleratedCubicNewtonRestartThreshold sigma3 L3))

variable [CompleteSpace E]

/-- The restart map sending `x` to the point obtained after one full block of
`acceleratedCubicNewtonRestartPeriod σ₃ L₃` inner accelerated cubic-Newton steps of the chapter
owner started from `x`. -/
def acceleratedCubicNewtonRestartMap
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x) (sigma3 : ℝ) :
    E → E :=
  fun x ↦ innerMethod x (acceleratedCubicNewtonRestartPeriod sigma3 L3)

/-- Evaluating the restart map at `x` applies the `m`-step accelerated iterate with
`m = acceleratedCubicNewtonRestartPeriod σ₃ L₃`. -/
@[simp] theorem acceleratedCubicNewtonRestartMap_apply
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x) (sigma3 : ℝ) (x : E) :
    acceleratedCubicNewtonRestartMap innerMethod sigma3 x =
      innerMethod x (acceleratedCubicNewtonRestartPeriod sigma3 L3) :=
  rfl

/-- Algorithm 4.2.3: if `innerMethod x` denotes the chapter accelerated cubic-Newton method
started from `x`, then the restarted accelerated cubic-Newton method with starting point `x₀` is
the canonical outer orbit of the restart map `x ↦ 𝓐_m(x)`, where
`m = ⌈((24 e) / (σ₃ / L₃))^{1/3}⌉₊` and `𝓐_m(x)` is written canonically as
`innerMethod x (acceleratedCubicNewtonRestartPeriod σ₃ L₃)`. -/
def restartedAcceleratedCubicNewtonMethod
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x) (sigma3 : ℝ) (x0 : E) :
    ℕ → E :=
  fun k ↦ (acceleratedCubicNewtonRestartMap innerMethod sigma3)^[k] x0

/-- The restarted accelerated cubic-Newton method starts from the prescribed initial point `x₀`.
-/
@[simp] theorem restartedAcceleratedCubicNewtonMethod_zero
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x) (sigma3 : ℝ) (x0 : E) :
    restartedAcceleratedCubicNewtonMethod innerMethod sigma3 x0 0 = x0 := by
  simp [restartedAcceleratedCubicNewtonMethod]

/-- The restarted accelerated cubic-Newton outer orbit satisfies the textbook recursion
`y_{k+1} = 𝓐_m(y_k)`, with `m = acceleratedCubicNewtonRestartPeriod σ₃ L₃`. -/
theorem restartedAcceleratedCubicNewtonMethod_succ
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x) (sigma3 : ℝ) (x0 : E)
    (k : ℕ) :
    restartedAcceleratedCubicNewtonMethod innerMethod sigma3 x0 (k + 1) =
      acceleratedCubicNewtonRestartMap innerMethod sigma3
        (restartedAcceleratedCubicNewtonMethod innerMethod sigma3 x0 k) := by
  simpa [restartedAcceleratedCubicNewtonMethod] using
    (Function.iterate_succ_apply' (acceleratedCubicNewtonRestartMap innerMethod sigma3) k x0)

end

end
