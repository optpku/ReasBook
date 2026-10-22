/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Algorithm 4.2.4 lies in the strongly-convex accelerated cubic-Newton / multistage-restart
domain.

Layer targeted by this refinement:
- source-facing owner for the multistage schedule of Algorithm 4.2.4

Primary mathematical domain:
- stage-dependent restarted accelerated cubic-Newton dynamics for strongly convex objectives

Sampled owner-style declarations:
- `AcceleratedCubicNewtonMethod` in `Algorithm_4_2_2`, the chapter owner for the inner
  accelerated cubic-Newton dynamics started from a prescribed point
- `acceleratedCubicNewtonRestartPeriod` in `Algorithm_4_2_3`, the fixed-length restart owner for
  the autonomous restart scheme
- `restartedAcceleratedCubicNewtonMethod` in `Algorithm_4_2_3`, the autonomous outer orbit built
  from a single restart map
- `strongConvexAcceleratedCubicNewtonQuadraticRegion` in `Text_4_2_13`, which shows that the
  later strong-convexity analysis is organized around stage-dependent radii, lengths, and the
  first entry of the outer orbit into a quadratic region rather than a fixed restart period

Best owner abstraction:
- source-facing: the multistage strong-convex accelerated cubic-Newton method of Algorithm 4.2.4
- core/canonical: the radius schedule `R_k`, the source stage lengths `m_k`, the derived natural
  stage counts `⌈m_k⌉₊`, the stage maps `x ↦ 𝓐_{⌈m_k⌉₊}(x)`, and the recursively generated outer
  orbit
- bridge/view: the zeroth-step and successor identities for that orbit

Primitive data:
- the objective `f`
- the strong-convexity modulus `σ₂`
- the Hessian-Lipschitz constant `L₃`
- the initial radius `R`
- the inner accelerated cubic-Newton owner family
  `(x : E) → AcceleratedCubicNewtonMethod f L3 x`
- the initial point `y₀`

Derived API:
- the radius schedule `R_k = R / 2^k`
- the source stage lengths `m_k = 5 ((L₃ R_k) / σ₂)^(1/3)`
- the natural stage counts `⌈m_k⌉₊` used by the discrete outer orbit
- the stage maps applying the inner owner for `⌈m_k⌉₊` steps
- the multistage outer orbit together with its `0`th-step and successor formulas

Source/core/bridge triage:
- source-facing: Algorithm 4.2.4 itself
- core/canonical: `StrongConvexAcceleratedCubicNewton.stageRadius`,
  `StrongConvexAcceleratedCubicNewton.stageLength`,
  `StrongConvexAcceleratedCubicNewton.stageSteps`,
  `StrongConvexAcceleratedCubicNewton.stageMap`, and
  `StrongConvexAcceleratedCubicNewton.method`
- bridge/view: `StrongConvexAcceleratedCubicNewton.method_zero` and
  `StrongConvexAcceleratedCubicNewton.method_succ`

The previous file collapsed Algorithm 4.2.4 to the fixed-period autonomous restart orbit from
Algorithm 4.2.3. That erased the genuine source-defined stage schedule `R_k, m_k` and
misidentified the owner abstraction. This refinement restores Algorithm 4.2.4 as its own
source-facing multistage owner, keeps the real-valued source schedule `m_k` visible, and treats
the natural step count `⌈m_k⌉₊` only as the discrete bridge needed to run the inner method. The
fixed-period restart API of Algorithm 4.2.3 remains a nearby chapter analogue, not the owner of
this item. -/

namespace StrongConvexAcceleratedCubicNewton

section

/-- The stage radius `R_k = R / 2^k` used in Algorithm 4.2.4. -/
def stageRadius (R : ℝ) (k : ℕ) : ℝ :=
  R / (2 : ℝ) ^ k

/-- The source stage length `m_k = 5 ((L₃ R_k) / σ₂)^(1/3)` attached to the radius `R_k`. -/
def stageLength (σ2 : ℝ) (L3 : NNReal) (R : ℝ) (k : ℕ) : ℝ :=
  5 * Real.rpow (((L3 : ℝ) * stageRadius R k) / σ2) (1 / 3 : ℝ)

/-- The discrete stage count `⌈m_k⌉₊` obtained from the source stage length `m_k`. -/
def stageSteps (σ2 : ℝ) (L3 : NNReal) (R : ℝ) (k : ℕ) : ℕ :=
  Nat.ceil (stageLength σ2 L3 R k)

/-- By construction the discrete stage count is at least the source stage length `m_k`. -/
theorem stageSteps_lower (σ2 : ℝ) (L3 : NNReal) (R : ℝ) (k : ℕ) :
    stageLength σ2 L3 R k ≤ (stageSteps σ2 L3 R k : ℝ) :=
  Nat.le_ceil _

/-- For `σ₂ > 0` and `R ≥ 0`, the source stage lengths satisfy the geometric recursion
`m_(k+1) = 2^(-1/3) m_k`. -/
theorem stageLength_succ
    {σ2 : ℝ} {L3 : NNReal} {R : ℝ} (k : ℕ)
    (hσ2 : 0 < σ2) (hR : 0 ≤ R) :
    stageLength σ2 L3 R (k + 1) =
      (1 / Real.rpow (2 : ℝ) (1 / 3 : ℝ)) * stageLength σ2 L3 R k := by
  have hbase_nonneg : 0 ≤ ((L3 : ℝ) * stageRadius R k) / σ2 := by
    dsimp [stageRadius]
    positivity
  calc
    stageLength σ2 L3 R (k + 1)
        = 5 * Real.rpow ((((L3 : ℝ) * stageRadius R k) / σ2) / 2) (1 / 3 : ℝ) := by
            simp [stageLength, stageRadius, pow_succ, div_eq_mul_inv]
            ring_nf
    _ = 5 * (Real.rpow (((L3 : ℝ) * stageRadius R k) / σ2) (1 / 3 : ℝ) /
          Real.rpow (2 : ℝ) (1 / 3 : ℝ)) := by
            exact congrArg (fun t ↦ 5 * t)
              (by
                simpa using
                  (Real.div_rpow hbase_nonneg (show 0 ≤ (2 : ℝ) by positivity)
                    (1 / 3 : ℝ)))
    _ = (1 / Real.rpow (2 : ℝ) (1 / 3 : ℝ)) * stageLength σ2 L3 R k := by
            rw [stageLength]
            ring

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {L3 : NNReal}

/-- The `k`th stage map of Algorithm 4.2.4 applies the inner accelerated cubic-Newton owner for
`⌈m_k⌉₊ = stageSteps σ₂ L₃ R k` steps, where `m_k = stageLength σ₂ L₃ R k` is the source schedule.
-/
def stageMap
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (k : ℕ) :
    E → E :=
  fun x ↦ innerMethod x (stageSteps σ2 L3 R k)

/-- Algorithm 4.2.4: the strong-convex accelerated cubic-Newton method is the outer sequence
obtained by applying at stage `k` the restart map with the stage-dependent length
`⌈m_k⌉₊ = stageSteps σ₂ L₃ R k`, where the source stage schedule is
`m_k = stageLength σ₂ L₃ R k`. -/
def method
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (y0 : E) :
    ℕ → E :=
  Nat.rec y0 (fun k yk ↦ stageMap innerMethod σ2 R k yk)

/-- The multistage method starts from the prescribed initial point `y₀`. -/
@[simp] theorem method_zero
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (y0 : E) :
    method innerMethod σ2 R y0 0 = y0 :=
  rfl

/-- The multistage method satisfies the textbook stage recursion
`y_{k+1} = 𝓐_{⌈m_k⌉₊}(y_k)`. -/
@[simp] theorem method_succ
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (y0 : E) (k : ℕ) :
    method innerMethod σ2 R y0 (k + 1) =
      stageMap innerMethod σ2 R k (method innerMethod σ2 R y0 k) :=
  rfl

/-- Evaluating the multistage method at stage `k + 1` applies the inner accelerated cubic-Newton
owner for the canonical stage length `⌈m_k⌉₊` to the previous outer iterate. -/
@[simp] theorem method_spec
    (innerMethod : (x : E) → AcceleratedCubicNewtonMethod f L3 x)
    (σ2 R : ℝ) (y0 : E) (k : ℕ) :
    method innerMethod σ2 R y0 (k + 1) =
      innerMethod (method innerMethod σ2 R y0 k) (stageSteps σ2 L3 R k) :=
  rfl

end

end StrongConvexAcceleratedCubicNewton
