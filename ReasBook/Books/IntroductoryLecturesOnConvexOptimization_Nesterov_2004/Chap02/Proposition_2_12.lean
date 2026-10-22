/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_9

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: accelerated first-order dynamics for strongly convex smooth unconstrained
minimization on real Hilbert spaces.

Relevant owner-style declarations sampled before refining this file:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`, which owns the objective-side
  `C¹`/strong-convexity/gradient-Lipschitz package;
* `IsMinOn` on `Set.univ`, which gives the canonical global minimizer predicate for the ambient
  unconstrained problem;
* `ConstantStepSchemeIIMomentumRecurrence` in `Algorithm_2_4`, the nearby owner abstraction for
  accelerated `(x_k, y_k)` trajectories with a momentum law;
* `ConstantStepSchemeIIRecurrence` in `Algorithm_2_4`, which adds the analytic side conditions to
  that owner trajectory.

Best owner abstractions here:
* `ConstantStepSchemeIIIMomentumRecurrence` for the intrinsic fixed-momentum trajectory data;
* `ConstantStepSchemeIII` for the exact gradient-step specialization of that trajectory;
* `IsStrongConvexSmoothObjective μ L f` for the objective-side regularity assumptions.

Primitive data:
* the shared fixed-β trajectory data `x`, `y` and its defining recurrences;
* the exact gradient-step equation of `ConstantStepSchemeIII`;
* one minimizing point `xStar`, expressed canonically by `IsMinOn`.

Derived API:
* positivity/regularity facts extracted from `IsStrongConvexSmoothObjective`;
* the textbook coefficient `β = (1 - √q_f) / (1 + √q_f)`;
* the canonical bridge to `ConstantStepSchemeIIMomentumRecurrence` with the constant scalar
  sequence `α_k = √q_f`.

Although scheme III can be embedded into the type-II owner abstraction by taking a constant
auxiliary scalar sequence `α_k = √q_f`, that scalar sequence is auxiliary implementation data,
not the intrinsic source-level object. The public owner here therefore remains the fixed-momentum
trajectory data, with `ConstantStepSchemeIII` as the source-facing exact-step specialization.
That shared fixed-momentum owner is purely algebraic: only the exact-step specialization and the
objective-gap estimates need the ambient Hilbert-space structure. -/

/-- The constant momentum coefficient `β = (1 - √q_f) / (1 + √q_f)` attached to the reciprocal
condition-number parameter `q_f` in constant step scheme III. -/
def constantStepSchemeIIIMomentumCoefficient (qf : ℝ) : ℝ :=
  (1 - Real.sqrt qf) / (1 + Real.sqrt qf)

/- Textbook surface notation for the constant scheme-III momentum coefficient. -/
scoped[StrongConvexSmooth] notation "β[" qf "]" => constantStepSchemeIIIMomentumCoefficient qf

/-- The fixed-momentum scheme-III trajectory data shared by the chapter's exact-step variants. -/
structure ConstantStepSchemeIIIMomentumRecurrence
    (E : Type u) [AddCommGroup E] [Module ℝ E]
    (X : Type*) [CoeTC X E] (qf : ℝ) (x0 : X) where
  /-- The main iterate sequence `x_k`. -/
  x : ℕ → X
  /-- The extrapolated sequence `y_k`. -/
  y : ℕ → E
  /-- The zeroth iterate is the prescribed initial point. -/
  x_zero : x 0 = x0
  /-- The extrapolated sequence starts from the same initial point. -/
  y_zero : y 0 = (x0 : E)
  /-- The extrapolated points use the fixed momentum coefficient `β[q_f]`. -/
  y_succ (k : ℕ) :
    y (k + 1) =
      (x (k + 1) : E) +
        β[qf] •
          ((x (k + 1) : E) - (x k : E))

namespace ConstantStepSchemeIIIMomentumRecurrence

variable {qf : ℝ}

private theorem constant_alpha_momentumCoefficient_eq
    (hqf : qf ∈ Set.Ioc (0 : ℝ) 1) :
    (Real.sqrt qf * (1 - Real.sqrt qf)) /
        (Real.sqrt qf ^ (2 : ℕ) + Real.sqrt qf) =
      β[qf] := by
  unfold constantStepSchemeIIIMomentumCoefficient
  have hqf_nonneg : 0 ≤ qf := hqf.1.le
  have hsqrt_ne : Real.sqrt qf ≠ 0 := Real.sqrt_ne_zero'.2 hqf.1
  field_simp [hsqrt_ne]
  nlinarith [Real.sq_sqrt hqf_nonneg]

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {X : Type*} [CoeTC X E] {qf : ℝ} {x0 : X}

/-- A fixed-momentum scheme-III recurrence can be used as its iterate sequence `x_k`. -/
instance :
    CoeFun
      (ConstantStepSchemeIIIMomentumRecurrence E X qf x0)
      (fun _ ↦ ℕ → X) where
  coe scheme := scheme.x

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {X : Type*} [CoeTC X E] {qf : ℝ} {x0 : X}

/-- Under the admissible parameter condition `q_f ∈ (0, 1]`, a fixed-momentum scheme-III
recurrence canonically induces the chapter's type-II momentum owner by adjoining the constant
scalar sequence `α_k = √q_f`. -/
def toConstantStepSchemeIIMomentumRecurrence
    (scheme : ConstantStepSchemeIIIMomentumRecurrence E X qf x0)
    (hqf : qf ∈ Set.Ioc (0 : ℝ) 1) :
    ConstantStepSchemeIIMomentumRecurrence E X qf x0 (Real.sqrt qf) where
  x := scheme.x
  y := scheme.y
  alpha := fun _ ↦ Real.sqrt qf
  x_zero := scheme.x_zero
  y_zero := scheme.y_zero
  alpha_zero := rfl
  alpha_succ_equation := by
    intro k
    have hqf_nonneg : 0 ≤ qf := hqf.1.le
    rw [Real.sq_sqrt hqf_nonneg]
    ring
  y_succ := by
    intro k
    rw [scheme.y_succ k, constant_alpha_momentumCoefficient_eq hqf]

end

end ConstantStepSchemeIIIMomentumRecurrence

/-- A constant step scheme of type III for `f : E → ℝ` with parameter `q_f` consists of
sequences `x_k` and `y_k` with constant step size `1 / L` and fixed momentum coefficient
`β[q_f] = (1 - √q_f) / (1 + √q_f)`. -/
structure ConstantStepSchemeIII (f : E → ℝ) (L qf : ℝ) (x0 : E)
    extends ConstantStepSchemeIIIMomentumRecurrence E E qf x0 where
  /-- The smoothness constant used in the step size is positive. -/
  L_pos : 0 < L
  /-- The reciprocal condition-number parameter lies in `(0, 1]`. -/
  qf_mem_Ioc : qf ∈ Set.Ioc (0 : ℝ) 1
  /-- The iterates are produced by a gradient step of size `1 / L` from `y_k`. -/
  x_succ (k : ℕ) :
    x (k + 1) = y k - (1 / L) • ∇ f (y k)

namespace ConstantStepSchemeIII

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {L qf : ℝ} {x0 : E}

/-- A scheme-III exact-step recurrence canonically induces the upstream type-II momentum owner by
forgetting only the fixed-`β` presentation and adjoining the constant scalar sequence
`α_k = √q_f`. -/
def toConstantStepSchemeIIMomentumRecurrence
    (scheme : ConstantStepSchemeIII f L qf x0) :
    ConstantStepSchemeIIMomentumRecurrence E E qf x0 (Real.sqrt qf) :=
  scheme.toConstantStepSchemeIIIMomentumRecurrence.toConstantStepSchemeIIMomentumRecurrence
    scheme.qf_mem_Ioc

/-- A constant-step scheme III can be used as its iterate sequence `x_k`. -/
instance : CoeFun (ConstantStepSchemeIII f L qf x0) (fun _ ↦ ℕ → E) where
  coe scheme := scheme.toConstantStepSchemeIIIMomentumRecurrence

end ConstantStepSchemeIII

/-
Proposition 2.12 is stated against the chapter's owner objective predicate
`IsStrongConvexSmoothObjective μ L f`, together with the canonical minimizer predicate
`IsMinOn f Set.univ xStar`. By Definition 2.22, the reciprocal condition number appearing in the
scheme-III rate is the canonical scalar `q[μ, L]`, so the scheme's exact-step data remain owned
by `ConstantStepSchemeIII f L q[μ, L] x0`, while its shared fixed-momentum trajectory lives in
`ConstantStepSchemeIIIMomentumRecurrence E E q[μ, L] x0`.
-/
section ObjectiveGapRates

variable {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f)
variable {xStar x0 : E} (hxStar : IsMinOn f Set.univ xStar)
variable (scheme : ConstantStepSchemeIII f L (q[μ, L]) x0)

local notation "qf" => q[μ, L]
local notation "a" => Real.sqrt qf
local notation "alpha" => fun _ : ℕ ↦ a
local notation "phi" =>
  strongConvexEstimatingFunction μ f
    (quadraticallyRegularizedObjective (fun _ : E ↦ f x0) μ x0)
    scheme.y
    alpha
local notation "phiStar" =>
  estimatingSequenceValue f alpha scheme.y μ (f x0) μ x0
local notation "center" =>
  estimatingSequenceCenter f alpha scheme.y μ μ x0

/-- Helper for Proposition 2.12: the constant coefficient sequence
`α_k = √q[μ, L]` gives the geometric estimating weight `(1 - √q[μ, L])^k`. -/
lemma schemeIII_estimating_weight_eq_geometric
    (k : ℕ) :
    estimatingWeight alpha k = (1 - a) ^ k := by
  -- The constant-coefficient weight recurrence is a geometric progression.
  induction k with
  | zero =>
      simp [estimatingWeight]
  | succ k ih =>
      rw [estimatingWeight, ih]
      ring

/-- Helper for Proposition 2.12: with initial curvature `γ₀ = μ` and constant
`α_k = √q[μ, L]`, the estimating-sequence curvature stays equal to `μ`. -/
lemma schemeIII_estimating_curvature_eq_mu
    (k : ℕ) :
    estimatingSequenceCurvature μ μ alpha k = μ := by
  -- The curvature recursion fixes `μ` when both the current and target curvatures equal `μ`.
  induction k with
  | zero =>
      simp [estimatingSequenceCurvature]
  | succ k ih =>
      rw [estimatingSequenceCurvature_succ]
      simp [ih]
      ring

/-- Helper for Proposition 2.12: a centered quadratic with positive curvature attains its minimum
value at its center. -/
lemma canonical_quadratic_isLeast_value
    {γ c : ℝ} {v : E}
    (hγ : 0 < γ) :
    IsLeast (Set.range (quadraticallyRegularizedObjective (fun _ : E ↦ c) γ v)) c := by
  refine ⟨?_, ?_⟩
  · -- Evaluating the quadratic at its center gives the claimed minimum value.
    refine ⟨v, ?_⟩
    simp [quadraticallyRegularizedObjective_apply]
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    -- Every other value differs from `c` by a nonnegative quadratic term.
    have hquad_nonneg : 0 ≤ (γ / 2) * ‖x - v‖ ^ (2 : ℕ) := by
      positivity
    simp [quadraticallyRegularizedObjective_apply]
    linarith

include hf
/-- Helper for Proposition 2.12: one normalized successor step converts the center recursion into
the scheme-III iterate gap update. -/
lemma schemeIII_center_succ_normalized
    {k : ℕ}
    (hcenter : center k - scheme.y k = (1 / a) • (scheme.y k - scheme k)) :
    center (k + 1) - scheme.y (k + 1) =
      ((((1 - a) / a) - β[qf]) : ℝ) • (scheme (k + 1) - scheme k) := by
  have hqf_nonneg : 0 ≤ qf := scheme.qf_mem_Ioc.1.le
  have ha_pos : 0 < a := Real.sqrt_pos.mpr scheme.qf_mem_Ioc.1
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have hmu_ne : μ ≠ 0 := hf.mu_pos.ne'
  have hstep :
      scheme.y k - scheme (k + 1) = (1 / L) • ∇ f (scheme.y k) := by
    -- Rewrite the exact gradient step into the gap form used by the source algebra.
    rw [scheme.x_succ k]
    abel
  have hcenter_sub :
      center (k + 1) - scheme.y k =
        ((1 - a) / a) • (scheme.y k - scheme k) -
          (1 / a) • (scheme.y k - scheme (k + 1)) := by
    have hyk :
        (1 / μ : ℝ) • (μ • scheme.y k) = scheme.y k := by
      rw [smul_smul, one_div, inv_mul_cancel₀ hmu_ne, one_smul]
    -- Route correction: first normalize the center recursion at the common basepoint `y_k`.
    calc
      center (k + 1) - scheme.y k
          =
            (1 / μ : ℝ) •
                (((1 - a) * μ) • center k + (a * μ) • scheme.y k - a • ∇ f (scheme.y k)) -
              (1 / μ : ℝ) • (μ • scheme.y k) := by
              rw [hyk]
              simp [estimatingSequenceCenter_succ, schemeIII_estimating_curvature_eq_mu (k := k),
                schemeIII_estimating_curvature_eq_mu (k := k + 1)]
      _ =
          (1 / μ : ℝ) •
            ((((1 - a) * μ) • center k + (a * μ) • scheme.y k - a • ∇ f (scheme.y k)) -
              μ • scheme.y k) := by
            rw [← smul_sub]
      _ =
          (1 / μ : ℝ) • (((1 - a) * μ) • (center k - scheme.y k) - a • ∇ f (scheme.y k)) := by
            congr 1
            module
      _ = (1 - a) • (center k - scheme.y k) - (a / μ) • ∇ f (scheme.y k) := by
            rw [smul_sub, smul_smul, smul_smul]
            have hcoef1 : (1 / μ : ℝ) * ((1 - a) * μ) = 1 - a := by
              field_simp [hmu_ne]
            have hcoef2 : (1 / μ : ℝ) * a = a / μ := by ring
            rw [hcoef1, hcoef2]
      _ = ((1 - a) / a) • (scheme.y k - scheme k) - (a / μ) • ∇ f (scheme.y k) := by
            rw [hcenter, smul_smul]
            congr 1
            field_simp [ha_ne]
      _ =
          ((1 - a) / a) • (scheme.y k - scheme k) -
            (1 / a) • (scheme.y k - scheme (k + 1)) := by
            have hscalar : a / μ = (1 / a : ℝ) * (1 / L) := by
              have hsq : a * a = μ / L := by
                calc
                  a * a = a ^ (2 : ℕ) := by ring
                  _ = μ / L := by simpa using Real.sq_sqrt hqf_nonneg
              calc
                a / μ = (a * a) / (a * μ) := by
                  field_simp [ha_ne, hmu_ne]
                _ = (μ / L) / (a * μ) := by rw [hsq]
                _ = (1 / a : ℝ) * (1 / L) := by
                  field_simp [ha_ne, hmu_ne, scheme.L_pos.ne']
            rw [hstep, smul_smul, hscalar]
  -- Now subtract the explicit momentum update `y_{k+1} - y_k`.
  calc
    center (k + 1) - scheme.y (k + 1)
        = (center (k + 1) - scheme.y k) - (scheme.y (k + 1) - scheme.y k) := by
            abel
    _ =
        (((1 - a) / a) • (scheme.y k - scheme k) -
            (1 / a) • (scheme.y k - scheme (k + 1))) -
          (scheme.y (k + 1) - scheme.y k) := by
            rw [hcenter_sub]
    _ =
        (((1 - a) / a) •
              ((scheme.y k - scheme (k + 1)) + (scheme (k + 1) - scheme k)) -
            (1 / a) • (scheme.y k - scheme (k + 1))) -
          (-(scheme.y k - scheme (k + 1)) +
            β[qf] • (scheme (k + 1) - scheme k)) := by
            have hydecomp :
                scheme.y k - scheme k =
                  (scheme.y k - scheme (k + 1)) + (scheme (k + 1) - scheme k) := by
              abel_nf
            have hysucc :
                scheme.y (k + 1) - scheme.y k =
                  -(scheme.y k - scheme (k + 1)) +
                    β[qf] • (scheme (k + 1) - scheme k) := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                congrArg (fun z : E ↦ z - scheme.y k) (scheme.y_succ k)
            rw [hydecomp, hysucc]
    _ = ((((1 - a) / a) - β[qf]) : ℝ) • (scheme (k + 1) - scheme k) := by
          let u : E := scheme.y k - scheme (k + 1)
          let v : E := scheme (k + 1) - scheme k
          have hcancel : (((1 - a) / a : ℝ) - 1 / a + 1) = 0 := by
            field_simp [ha_ne]
            ring
          change (((1 - a) / a) • (u + v) - (1 / a) • u) - (-u + β[qf] • v) =
            ((((1 - a) / a) - β[qf]) : ℝ) • v
          calc
            (((1 - a) / a) • (u + v) - (1 / a) • u) - (-u + β[qf] • v)
                = ((((1 - a) / a) - 1 / a + 1) : ℝ) • u +
                    ((((1 - a) / a) - β[qf]) : ℝ) • v := by
                      module
            _ = ((((1 - a) / a) - β[qf]) : ℝ) • v := by
                  rw [hcancel, zero_smul, zero_add]

/-- Helper for Proposition 2.12: the estimating-sequence center differs from `y_k` by the
scaled iterate gap `(1 / √q[μ, L]) (y_k - x_k)`. -/
lemma schemeIII_estimating_center_sub_eq_iterate_gap
    (k : ℕ) :
    center k - scheme.y k = (1 / a) • (scheme.y k - scheme k) := by
  induction k with
  | zero =>
      -- At time zero, both the center and the extrapolated point equal the initial iterate.
      rw [show center 0 = x0 by rfl, scheme.y_zero, scheme.x_zero]
      change (x0 : E) - (x0 : E) = (1 / a) • ((x0 : E) - (x0 : E))
      simp
  | succ k ih =>
      have hbeta_gap :
          scheme.y (k + 1) - scheme (k + 1) =
            β[qf] • (scheme (k + 1) - scheme k) := by
        -- Rewrite the momentum update as the displayed iterate gap.
        rw [scheme.y_succ k]
        module
      -- Route correction: use the normalized successor identity before converting back to the
      -- public `(1 / a) • (y_k - x_k)` bridge.
      calc
        center (k + 1) - scheme.y (k + 1)
            = ((((1 - a) / a) - β[qf]) : ℝ) • (scheme (k + 1) - scheme k) := by
                exact schemeIII_center_succ_normalized (hf := hf) (scheme := scheme) ih
        _ = (β[qf] / a) • (scheme (k + 1) - scheme k) := by
              have hbeta :
                  β[qf] = (1 - a) / (1 + a) := by
                rfl
              have ha_pos : 0 < a := Real.sqrt_pos.mpr scheme.qf_mem_Ioc.1
              have ha_ne : a ≠ 0 := ha_pos.ne'
              have hdenom_ne : 1 + a ≠ 0 := by
                linarith
              rw [hbeta]
              field_simp [ha_ne, hdenom_ne]
              ring_nf
        _ = (1 / a) • (β[qf] • (scheme (k + 1) - scheme k)) := by
              rw [smul_smul]
              congr 1
              ring
        _ = (1 / a) • (scheme.y (k + 1) - scheme (k + 1)) := by
              rw [hbeta_gap]

/-- Helper for Proposition 2.12: every estimating function `φ_k` attains the minimum value
`φ_k^*`. -/
lemma schemeIII_estimating_value_isLeast
    (k : ℕ) :
    IsLeast (Set.range (phi k)) (phiStar k) := by
  have hγ :
      ∀ j, estimatingSequenceCurvature μ μ alpha (j + 1) ≠ 0 := by
    intro j
    rw [schemeIII_estimating_curvature_eq_mu (k := j + 1)]
    exact IsStrongConvexSmoothObjective.mu_pos hf |>.ne'
  -- Re-express `φ_k` as its centered quadratic normal form, then apply the generic minimum-value
  -- lemma for positive-curvature quadratics.
  rw [estimatingSequence_eq_canonicalQuadratic f (fun _ : ℕ ↦ a) scheme.y μ (f x0) μ x0 hγ k]
  rw [schemeIII_estimating_curvature_eq_mu (k := k)]
  simpa using
    canonical_quadratic_isLeast_value
      (E := E)
      (γ := μ)
      (c := estimatingSequenceValue f (fun _ : ℕ ↦ a) scheme.y μ (f x0) μ x0 k)
      (v := estimatingSequenceCenter f (fun _ : ℕ ↦ a) scheme.y μ μ x0 k)
      (IsStrongConvexSmoothObjective.mu_pos hf)

/-- Helper for Proposition 2.12: the scalar recurrence for `φ_k^*` reduces to the exact
scheme-III Lyapunov update after rewriting the center gap by the iterate gap. -/
lemma schemeIII_estimating_value_succ_normalized
    (k : ℕ) :
    phiStar (k + 1) =
      (1 - a) * phiStar k +
        a * f (scheme.y k) -
        (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
        (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
        ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
  have hqf_nonneg : 0 ≤ qf := scheme.qf_mem_Ioc.1.le
  have ha_pos : 0 < a := Real.sqrt_pos.mpr scheme.qf_mem_Ioc.1
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have hmu_ne : μ ≠ 0 := hf.mu_pos.ne'
  have hcenter := schemeIII_estimating_center_sub_eq_iterate_gap
    (hf := hf) (scheme := scheme) k
  have hycenter :
      scheme.y k - center k = (1 / a) • (scheme k - scheme.y k) := by
    -- Reverse the center-gap identity to match the quadratic norm term.
    calc
      scheme.y k - center k = -(center k - scheme.y k) := by
        abel
      _ = -((1 / a) • (scheme.y k - scheme k)) := by
        rw [hcenter]
      _ = (1 / a) • (scheme k - scheme.y k) := by
        simp [sub_eq_add_neg, add_comm]
  have hgradient :
      a ^ (2 : ℕ) / (2 * μ) = 1 / (2 * L) := by
    have hsq : a * a = μ / L := by
      calc
        a * a = a ^ (2 : ℕ) := by ring
        _ = μ / L := by simpa using Real.sq_sqrt hqf_nonneg
    calc
      a ^ (2 : ℕ) / (2 * μ) = (a * a) / (2 * μ) := by ring
      _ = (μ / L) / (2 * μ) := by rw [hsq]
      _ = 1 / (2 * L) := by
            field_simp [hmu_ne, scheme.L_pos.ne']
  have hlinear :
      a * (1 - a) * inner ℝ (∇ f (scheme.y k)) (center k - scheme.y k) =
        (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) := by
    rw [hcenter, real_inner_smul_right]
    field_simp [ha_ne]
  have hquadratic :
      a * (1 - a) * ((μ / 2) * ‖scheme.y k - center k‖ ^ (2 : ℕ)) =
        ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
    rw [hycenter, norm_smul, Real.norm_eq_abs]
    have habs : |(1 / a : ℝ)| = 1 / a := by
      rw [abs_of_pos (one_div_pos.mpr ha_pos)]
    rw [habs]
    field_simp [ha_ne]
  -- Rewrite the generic estimating-sequence scalar recursion at constant curvature `μ`.
  calc
    phiStar (k + 1)
        = (1 - a) * phiStar k +
            a * f (scheme.y k) -
            (a ^ (2 : ℕ) / (2 * μ)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
            a * (1 - a) *
              ((μ / 2) * ‖scheme.y k - center k‖ ^ (2 : ℕ) +
                inner ℝ (∇ f (scheme.y k)) (center k - scheme.y k)) := by
            simpa [schemeIII_estimating_curvature_eq_mu (k := k),
              schemeIII_estimating_curvature_eq_mu (k := k + 1), hmu_ne] using
              estimatingSequenceValue_succ f (fun _ : ℕ ↦ a) scheme.y μ (f x0) μ x0 k
    _ = (1 - a) * phiStar k +
          a * f (scheme.y k) -
          (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
          (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
          ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
            rw [hgradient]
            rw [mul_add, hquadratic, hlinear]
            ring

include hf
/-- Helper for Proposition 2.12: the estimating-sequence values dominate the actual objective
values along the scheme-III trajectory. -/
lemma schemeIII_estimating_value_ge_objective
    (k : ℕ) :
    f (scheme k) ≤ phiStar k := by
  have ha_pos : 0 < a := Real.sqrt_pos.mpr scheme.qf_mem_Ioc.1
  have hqf_nonneg : 0 ≤ qf := scheme.qf_mem_Ioc.1.le
  have ha_le_one : a ≤ 1 := by
    nlinarith [scheme.qf_mem_Ioc.2, Real.sq_sqrt hqf_nonneg, Real.sqrt_nonneg qf]
  induction k with
  | zero =>
      -- The initial estimating value is exactly `f x₀`.
      simp [estimatingSequenceValue, scheme.x_zero]
  | succ k ih =>
      have hfactor_nonneg : 0 ≤ 1 - a := by
        linarith
      have hdescent_core :
          inner ℝ (∇ f (scheme.y k)) (scheme (k + 1) - scheme.y k) +
              (L / 2) * ‖scheme (k + 1) - scheme.y k‖ ^ (2 : ℕ) =
            -(1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) := by
        have hstep :
            scheme (k + 1) - scheme.y k = (- (1 / L : ℝ)) • ∇ f (scheme.y k) := by
          have hstep_eq :=
            congrArg (fun z : E ↦ z - scheme.y k) (scheme.x_succ k)
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, neg_smul] using hstep_eq
        -- The exact gradient step turns the smooth tangent model into the standard decrease term.
        rw [hstep, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs]
        have habs : |(-(1 / L : ℝ))| = 1 / L := by
          have hnonpos : -(1 / L : ℝ) ≤ 0 := by
            have hLinv_pos : 0 < (1 / L : ℝ) := one_div_pos.mpr scheme.L_pos
            linarith
          rw [abs_of_nonpos hnonpos]
          ring
        rw [habs]
        field_simp [scheme.L_pos.ne']
        ring
      have hdescent :
          f (scheme (k + 1)) ≤
            f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) := by
        have hupper := hf.upper_tangent_quadratic (scheme.y k) (scheme (k + 1))
        calc
          f (scheme (k + 1))
              ≤ f (scheme.y k) +
                  inner ℝ (∇ f (scheme.y k)) (scheme (k + 1) - scheme.y k) +
                    (L / 2) * ‖scheme (k + 1) - scheme.y k‖ ^ (2 : ℕ) := by
                      simpa using hupper
          _ = f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) := by
                linarith [hdescent_core]
      have hnorm_nonneg : 0 ≤ ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
        positivity
      have hinside_nonneg :
          0 ≤
            phiStar k - f (scheme.y k) +
              inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
              (μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
        have hlower := hf.lower_tangent_quadratic (scheme.y k) (scheme k)
        have hbase :
            0 ≤
              phiStar k - f (scheme.y k) +
                inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) -
                (μ / 2) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
          have hinner :
              -inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) =
                inner ℝ (∇ f (scheme.y k)) (scheme k - scheme.y k) := by
            have hvec : scheme.y k - scheme k = -(scheme k - scheme.y k) := by
              abel
            rw [hvec, inner_neg_right, neg_neg]
          have hlower' :
              f (scheme.y k) -
                  inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
                  (μ / 2) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) ≤
                f (scheme k) := by
            calc
              f (scheme.y k) -
                    inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
                    (μ / 2) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ)
                  =
                    f (scheme.y k) +
                      inner ℝ (∇ f (scheme.y k)) (scheme k - scheme.y k) +
                      (μ / 2) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
                        rw [sub_eq_add_neg, hinner]
              _ ≤ f (scheme k) := hlower
          nlinarith [ih, hlower']
        have hextra_nonneg :
            0 ≤
              ((μ / (2 * a)) + μ / 2) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
          have hcoef_nonneg : 0 ≤ (μ / (2 * a)) + μ / 2 := by
            have hleft : 0 ≤ μ / (2 * a) := by
              have hden : 0 ≤ 2 * a := by
                nlinarith [ha_pos]
              exact div_nonneg hf.mu_pos.le hden
            have hright : 0 ≤ μ / 2 := by
              exact div_nonneg hf.mu_pos.le (by norm_num)
            linarith
          exact mul_nonneg hcoef_nonneg hnorm_nonneg
        -- Combine the inductive domination with strong convexity at the common basepoint `y_k`.
        nlinarith [hbase, hextra_nonneg]
      have hstep_model :
          f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) ≤
            (1 - a) * phiStar k +
              a * f (scheme.y k) -
              (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
              (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
              ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
        have hscaled :
            0 ≤
              (1 - a) *
                (phiStar k - f (scheme.y k) +
                  inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
                  (μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ)) := by
          exact mul_nonneg hfactor_nonneg hinside_nonneg
        calc
          f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ)
              ≤ f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
                  (1 - a) *
                    (phiStar k - f (scheme.y k) +
                      inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
                      (μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ)) := by
                    nlinarith
          _ = (1 - a) * phiStar k +
                a * f (scheme.y k) -
                (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
                (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
                ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := by
                  ring
      calc
        f (scheme (k + 1))
            ≤ f (scheme.y k) - (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) := hdescent
        _ ≤ (1 - a) * phiStar k +
              a * f (scheme.y k) -
              (1 / (2 * L)) * ‖∇ f (scheme.y k)‖ ^ (2 : ℕ) +
              (1 - a) * inner ℝ (∇ f (scheme.y k)) (scheme.y k - scheme k) +
              ((1 - a) * μ / (2 * a)) * ‖scheme k - scheme.y k‖ ^ (2 : ℕ) := hstep_model
        _ = phiStar (k + 1) := by
              rw [schemeIII_estimating_value_succ_normalized (hf := hf) (scheme := scheme) k]

include hf hxStar
/-- The owner geometric objective-gap estimate for constant step scheme III is controlled by the
canonical initial Lyapunov energy
`f x₀ - f x* + (μ / 2) ‖x₀ - x*‖²`, with decay factor `(1 - √q[μ, L])^k`. -/
-- Proof sketch: identify scheme III with the `γ₀ = μ` specialization of the chapter's
-- estimating-sequence owner, whose weight is exactly `(1 - √q[μ, L])^k`. Then apply the owner
-- estimating-sequence suboptimality theorem with that geometric weight and the initial quadratic
-- model at `x₀`.
theorem constantStepSchemeIII_objective_gap_le_geometric_initial_energy
    (k : ℕ) :
    f (scheme k) - f xStar ≤
      (1 - Real.sqrt (q[μ, L])) ^ k *
        (f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  have hqf_nonneg : 0 ≤ qf := scheme.qf_mem_Ioc.1.le
  have ha_le_one : a ≤ 1 := by
    nlinarith [scheme.qf_mem_Ioc.2, Real.sq_sqrt hqf_nonneg, Real.sqrt_nonneg qf]
  have hgrad :
      ∀ j, HasGradientAt f (∇ f (scheme.y j)) (scheme.y j) := by
    intro j
    exact hf.contDiff.differentiable_one (scheme.y j) |>.hasGradientAt
  have halpha_mem_Icc : ∀ j, alpha j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    exact ⟨Real.sqrt_nonneg qf, ha_le_one⟩
  have hphiUpper :
      ∀ j, phi j ≤ lineMap f (phi 0) (estimatingWeight alpha j) := by
    intro j
    simpa using
      strongConvexEstimatingFunction_upper_bound
        (φ₀ := quadraticallyRegularizedObjective (fun _ : E ↦ f x0) μ x0)
        (y := scheme.y) (α := fun _ : ℕ ↦ a)
        hf.strongConvexOn hgrad halpha_mem_Icc j
  have hgap :
      f (scheme k) - f xStar ∈
        Set.Icc 0 (estimatingWeight alpha k * (phi 0 xStar - f xStar)) := by
    exact estimatingSequence_gap_mem_Icc xStar phiStar scheme hxStar hphiUpper
      (schemeIII_estimating_value_isLeast (hf := hf) (scheme := scheme))
      (schemeIII_estimating_value_ge_objective (hf := hf) (scheme := scheme))
      k
  have hInitial :
      phi 0 xStar - f xStar =
        f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    -- Evaluate the initial quadratic model at the minimizer.
    calc
      phi 0 xStar - f xStar
          = quadraticallyRegularizedObjective (fun _ : E ↦ f x0) μ x0 xStar - f xStar := by
              rfl
      _ = (f x0 + (μ / 2) * ‖xStar - x0‖ ^ (2 : ℕ)) - f xStar := by
            rw [quadraticallyRegularizedObjective_apply]
      _ = f x0 - f xStar + (μ / 2) * ‖xStar - x0‖ ^ (2 : ℕ) := by
            ring
      _ = f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
            rw [norm_sub_rev]
  -- Extract the interval upper endpoint and rewrite the owner weight as the geometric factor.
  calc
    f (scheme k) - f xStar
        ≤ estimatingWeight alpha k * (phi 0 xStar - f xStar) := hgap.2
    _ = (1 - a) ^ k * (f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
          rw [schemeIII_estimating_weight_eq_geometric (k := k), hInitial]
omit hf hxStar

include hf hxStar
/-- Proposition 2.12: if `f : E → ℝ` belongs to the strongly convex smooth class with
parameters `μ` and `L`, `xStar` is a minimizer of `f`, and `x_k` is generated by constant step
scheme III with reciprocal condition number `q_f = q[μ, L]` and momentum coefficient
`β[q[μ, L]] = (1 - √q[μ, L]) / (1 + √q[μ, L])`, then
`f(x_k) - f(xStar) ≤ ((L + μ) / 2) ‖x₀ - xStar‖² exp(-k √q[μ, L])` for every `k ≥ 0`. -/
-- Proof sketch: use the standard Lyapunov function for constant step scheme III, whose one-step
-- decay factor is `1 - √q[μ, L]`. Iterating the decay gives
-- `E_k ≤ (1 - √q[μ, L])^k E_0`, while the energy controls the objective gap and
-- satisfies the initial bound `E_0 ≤ ((L + μ) / 2) ‖x₀ - xStar‖²`. Finally apply
-- `(1 - √q[μ, L])^k ≤ exp (-k √q[μ, L])`.
theorem constantStepSchemeIII_objective_gap_le_exponential_rate
    (k : ℕ) :
    f (scheme k) - f xStar ≤
      ((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) *
        Real.exp (-(k : ℝ) * Real.sqrt (q[μ, L])) := by
  have hqf_nonneg : 0 ≤ qf := scheme.qf_mem_Ioc.1.le
  have ha_le_one : a ≤ 1 := by
    nlinarith [scheme.qf_mem_Ioc.2, Real.sq_sqrt hqf_nonneg, Real.sqrt_nonneg qf]
  have hweight_nonneg : 0 ≤ (1 - a) ^ k := by
    exact pow_nonneg (sub_nonneg.mpr ha_le_one) k
  have hinitial_gap :
      f x0 - f xStar ≤ (L / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hgrad_zero : ∇ f xStar = 0 := hf.gradient_eq_zero_of_isMinOn hxStar
    have hupper :
        f x0 ≤ f xStar + (L / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      simpa [hgrad_zero] using hf.upper_tangent_quadratic xStar x0
    linarith
  have hinitial_energy :
      f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤
        ((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    linarith
  have hgeom_exp :
      (1 - a) ^ k ≤ Real.exp (-(k : ℝ) * a) := by
    -- Compare the geometric weight with its exponential majorant.
    cases k with
    | zero =>
        simp
    | succ k =>
        have haux : a * ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          nlinarith
        have hbase :=
          Real.one_sub_div_pow_le_exp_neg (n := k + 1)
            (t := a * ((k + 1 : ℕ) : ℝ)) haux
        have hdiv :
            a * ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ)) = a := by
          field_simp
        calc
          (1 - a) ^ (k + 1)
              = (1 - a * ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ))) ^ (k + 1) := by
                  rw [hdiv]
          _ ≤ Real.exp (-(a * ((k + 1 : ℕ) : ℝ))) := hbase
          _ = Real.exp (-((k + 1 : ℕ) : ℝ) * a) := by
                ring_nf
  have henergy_nonneg :
      0 ≤ ((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hnorm_nonneg : 0 ≤ ‖x0 - xStar‖ ^ (2 : ℕ) := by
      positivity
    nlinarith [scheme.L_pos, hf.mu_pos, hnorm_nonneg]
  calc
    f (scheme k) - f xStar
        ≤ (1 - a) ^ k *
            (f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) :=
      constantStepSchemeIII_objective_gap_le_geometric_initial_energy
        (hf := hf) (hxStar := hxStar) (scheme := scheme) k
    _ ≤ (1 - a) ^ k * (((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
          gcongr
    _ ≤ Real.exp (-(k : ℝ) * a) * (((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
          gcongr
    _ = ((L + μ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) * Real.exp (-(k : ℝ) * a) := by
          ring

omit hf hxStar

end ObjectiveGapRates
