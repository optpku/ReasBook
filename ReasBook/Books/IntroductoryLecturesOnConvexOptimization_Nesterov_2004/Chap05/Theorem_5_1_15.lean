/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DikinEllipsoidNotation Gradient HessianLocalNorm NewtonDecrement
open scoped SelfConcordantAuxiliaryFunction
open SelfConcordantNewtonVariant

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.1.15 lies in the Chapter 5 self-concordant damped-Newton domain.

Sampled owner declarations:
* `newtonDecrement`, the notation `λ[f; x | hPos; hInv]`, and the bridge
  `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the Chapter 5 owner for the Newton
  decrement;
* `selfConcordantNewtonShift` in `Definition_5_2_1`, whose `.damped` branch is the textbook
  shift formula `ξ = M_f λ`;
* `selfConcordantNewtonNextPoint` in `Definition_5_2_1`, the chapter owner for one-step
  self-concordant Newton updates and their `.damped` specialization;
* `localNorm_taylor_upper_bound_with_selfConcordantOmegaStar` in `Theorem_5_1_9`, the chapter
  owner for the upper Taylor bound with the canonical `ω_*` remainder on an admissible step.

Best owner abstraction:
* source-facing: the one-step value decrease for the damped specialization of
  `selfConcordantNewtonNextPoint`;
* core/canonical: `selfConcordantNewtonNextPoint` together with `newtonDecrement`;
* bridge/view: the admissible damped-step norm
  `λ_f(x) / (1 + M_f λ_f(x))`, the corresponding `ω_*` upper remainder, and the Fenchel bridge
  back to the source-facing `ω(M_f λ_f(x))` term.

Primitive data:
* a self-concordant function `f` on `dom` with parameter `Mf`;
* a point `x ∈ dom`;
* Hessian nondegeneracy at `x`.

Derived API:
* the damped self-concordant Newton next point at `x` as the specialization
  `selfConcordantNewtonNextPoint f Mf .damped x hx hH`;
* the Newton decrement `λ_f(x)` supplied by `NewtonDecrement.ofDetNeZero`;
* the canonical auxiliary-function argument
  `NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH`, whose coercion is `(Mf : ℝ) * λ_f(x)`.

The previous version still depended on a parallel damped-step wrapper. This refinement states the
value decrease directly for the canonical `.damped` specialization of
`selfConcordantNewtonNextPoint`, keeps the decrement side on the Chapter 5 owner surface, and is
organized around the chapter's upper-bound `ω_*` Taylor layer rather than the lower-bound
Hessian-comparison theorem.
-/

-- Proof sketch: write the step `d = x₊ - x` as the damped inverse-Hessian gradient direction, so
-- `‖d‖_x = λ_f(x) / (1 + M_f λ_f(x))`. Theorem 5.1.9 applies directly to this admissible step,
-- giving the upper Taylor remainder `ω_*` at the damped step norm, while the gradient pairing
-- along the Newton direction is
-- `-λ_f(x)^2 / (1 + M_f λ_f(x))`. Rewriting with the Fenchel relation
-- `ω(t) = t ω'(t) - ω_*(ω'(t))` gives the canonical remainder `M_f⁻² ω(M_f λ_f(x))`
-- when `M_f > 0`.
/-- Helper for Theorem 5.1.15: nonnegative scalar dilations scale the Hessian local norm at a
point with positive Hessian. -/
private theorem hessianLocalNorm_smul_of_nonneg
    {f : E → ℝ} {x u : E} (hPos : (hessian f x).IsPositive)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖τ • u‖[f; x] = τ * ‖u‖[f; x] := by
  have hquad : 0 ≤ inner ℝ u (hessian f x u) := hPos.inner_nonneg_right u
  -- Expand the local norm and pull the nonnegative scalar through the square root.
  calc
    ‖τ • u‖[f; x] = Real.sqrt ((τ * τ) * inner ℝ u (hessian f x u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f x u)) * Real.sqrt (τ * τ) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = τ * ‖u‖[f; x] := by
      rw [show τ * τ = τ ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hτ,
        hessianLocalNorm_def]
      ring

/-- Helper for Theorem 5.1.15: the inverse-Hessian gradient pairing is nonnegative. -/
private theorem inverse_hessian_gradient_pairing_nonneg
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    0 ≤ inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x)) := by
  let v := (hessian f x).inverse (∇ f x)
  let hPos : (hessian f x).IsPositive :=
    IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx
  let hInv : (hessian f x).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero hH
  have hquad : 0 ≤ inner ℝ v (hessian f x v) := hPos.inner_nonneg_right v
  have hHv : hessian f x v = ∇ f x := hInv.self_apply_inverse (∇ f x)
  -- Rewrite the positive quadratic form of the Newton direction back to the gradient pairing.
  calc
    0 ≤ inner ℝ v (hessian f x v) := hquad
    _ = inner ℝ (∇ f x) v := by rw [hHv, real_inner_comm]
    _ = inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x)) := by
      rfl

/-- Helper for Theorem 5.1.15: expanding the damped next point exposes the inverse-Hessian
Newton direction. -/
private theorem damped_step_sub_eq_neg_smul
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let α := 1 / (1 + (Mf : ℝ) * δ)
    selfConcordantNewtonNextPoint f Mf .damped x hx hH - x =
      -(α • (hessian f x).inverse (∇ f x)) := by
  dsimp
  -- Subtract the base point from the explicit damped-step formula.
  rw [selfConcordantNewtonNextPoint_def]
  simp [selfConcordantNewtonShift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 5.1.15: the damped Newton displacement has the textbook local norm
`λ_f(x) / (1 + M_f λ_f(x))`. -/
private theorem damped_step_localNorm_eq
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    ‖selfConcordantNewtonNextPoint f Mf .damped x hx hH - x‖[f; x] =
      δ / (1 + (Mf : ℝ) * δ) := by
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let α : ℝ := 1 / (1 + (Mf : ℝ) * δ)
  let v : E := (hessian f x).inverse (∇ f x)
  let hPos : (hessian f x).IsPositive :=
    IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx
  let hInv : (hessian f x).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero hH
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg Mf f hx hH
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    have hden_nonneg : 0 ≤ 1 + (Mf : ℝ) * δ := by
      have hMf_nonneg : 0 ≤ (Mf : ℝ) := by exact_mod_cast Mf.2
      nlinarith
    exact one_div_nonneg.mpr hden_nonneg
  have hv_eq : hessian f x v = ∇ f x := hInv.self_apply_inverse (∇ f x)
  have hv_norm : ‖v‖[f; x] = δ := by
    -- The local norm of the Newton direction is exactly the Newton decrement.
    rw [hessianLocalNorm_def]
    calc
      Real.sqrt (inner ℝ v (hessian f x v))
          = Real.sqrt (inner ℝ (∇ f x) v) := by rw [hv_eq, real_inner_comm]
      _ = δ := by
        simpa [δ, v] using (NewtonDecrement.ofDetNeZero_def Mf f hx hH).symm
  -- Rewrite the displacement and then scale the local norm through the positive scalar `α`.
  calc
    ‖selfConcordantNewtonNextPoint f Mf .damped x hx hH - x‖[f; x]
        = ‖α • v‖[f; x] := by
            rw [@damped_step_sub_eq_neg_smul E _ _ _ dom Mf f _ x hx hH]
            rw [hessianLocalNorm_neg]
    _ = α * ‖v‖[f; x] := hessianLocalNorm_smul_of_nonneg hPos hα_nonneg
    _ = α * δ := by rw [hv_norm]
    _ = δ / (1 + (Mf : ℝ) * δ) := by
      simpa [α, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 5.1.15: the affine Taylor term along the damped Newton direction collapses
to `-λ_f(x)^2 / (1 + M_f λ_f(x))`. -/
private theorem damped_step_gradient_pairing_eq
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    inner ℝ (∇ f x) (selfConcordantNewtonNextPoint f Mf .damped x hx hH - x) =
      -(δ ^ (2 : ℕ) / (1 + (Mf : ℝ) * δ)) := by
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let α : ℝ := 1 / (1 + (Mf : ℝ) * δ)
  let v : E := (hessian f x).inverse (∇ f x)
  have hq_nonneg : 0 ≤ inner ℝ (∇ f x) v := by
    simpa [v] using (@inverse_hessian_gradient_pairing_nonneg E _ _ _ dom Mf f _ x hx hH)
  have hq_eq : inner ℝ (∇ f x) v = δ ^ (2 : ℕ) := by
    -- Square the defining Newton-decrement identity.
    calc
      inner ℝ (∇ f x) v = (Real.sqrt (inner ℝ (∇ f x) v)) ^ (2 : ℕ) := by
        symm
        simpa using Real.sq_sqrt hq_nonneg
      _ = δ ^ (2 : ℕ) := by
        rw [show Real.sqrt (inner ℝ (∇ f x) v) = δ by
          simpa [δ, v] using (NewtonDecrement.ofDetNeZero_def Mf f hx hH).symm]
  -- Rewrite the displacement and evaluate the gradient pairing on the scaled Newton direction.
  calc
    inner ℝ (∇ f x) (selfConcordantNewtonNextPoint f Mf .damped x hx hH - x)
        = inner ℝ (∇ f x) (-(α • v)) := by
            rw [@damped_step_sub_eq_neg_smul E _ _ _ dom Mf f _ x hx hH]
    _ = -(α * inner ℝ (∇ f x) v) := by
      simp [inner_smul_right, mul_comm, mul_left_comm, mul_assoc]
    _ = -(α * δ ^ (2 : ℕ)) := by rw [hq_eq]
    _ = -(δ ^ (2 : ℕ) / (1 + (Mf : ℝ) * δ)) := by
      simpa [α, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 5.1.15: when `M_f > 0`, the damped step lies in the admissible Dikin
ellipsoid centered at the current iterate. -/
private theorem damped_step_mem_openDikinEllipsoid
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) (hMf : Mf ≠ 0) :
    selfConcordantNewtonNextPoint f Mf .damped x hx hH ∈ W⁰[f; x](1 / (Mf : ℝ)) := by
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg Mf f hx hH
  have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
  have hMf_pos : 0 < (Mf : ℝ) := by exact_mod_cast hMf_pos_nn
  have hstep_lt :
      δ / (1 + (Mf : ℝ) * δ) < 1 / (Mf : ℝ) := by
    refine (lt_div_iff₀ hMf_pos).2 ?_
    have hfrac_lt :
        ((Mf : ℝ) * δ) / (1 + (Mf : ℝ) * δ) < 1 := by
      have hden_pos : 0 < 1 + (Mf : ℝ) * δ := by positivity
      refine (div_lt_iff₀ hden_pos).2 ?_
      nlinarith
    simpa [δ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfrac_lt
  -- The local norm computation is exactly the Dikin-radius condition.
  refine (mem_openDikinEllipsoid_iff f x
      (selfConcordantNewtonNextPoint f Mf .damped x hx hH) (1 / (Mf : ℝ))).2 ?_
  rw [show
      ‖selfConcordantNewtonNextPoint f Mf .damped x hx hH - x‖[f; x] =
        δ / (1 + (Mf : ℝ) * δ) by
      simpa [δ] using (@damped_step_localNorm_eq E _ _ _ dom Mf f _ x hx hH)]
  exact hstep_lt

/-- Helper for Theorem 5.1.15: the `ω_*` remainder argument at the damped step coincides with the
canonical `ω'(M_f λ_f(x))` point. -/
private theorem damped_step_omegaStarArg_eq
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) (hMf : Mf ≠ 0) :
    selfConcordantOmegaStarArg Mf
        ‖selfConcordantNewtonNextPoint f Mf .damped x hx hH - x‖[f; x]
        (mf_mul_lt_one_of_lt_inv <|
          by
            simpa using
              (mem_openDikinEllipsoid_iff f x
                (selfConcordantNewtonNextPoint f Mf .damped x hx hH) (1 / (Mf : ℝ))).1
                (@damped_step_mem_openDikinEllipsoid E _ _ _ dom Mf f _ x hx hH hMf)) =
      selfConcordantOmegaStarArg 1
        (ω' (NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH))
        (by
          simpa using
            selfConcordantOmegaDeriv_lt_one (NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH)) := by
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let tω : Set.Ioi (-1 : ℝ) := NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH
  have hcoetω : (tω : ℝ) = (Mf : ℝ) * δ := by
    simpa [δ, tω] using (NewtonDecrement.coe_omegaArgOfDetNeZero Mf f hx hH)
  apply Subtype.ext
  -- Both subtype arguments have the same scalar value `M_f λ_f(x) / (1 + M_f λ_f(x))`.
  calc
    ↑(selfConcordantOmegaStarArg Mf ‖selfConcordantNewtonNextPoint f Mf .damped x hx hH - x‖[f; x]
        (mf_mul_lt_one_of_lt_inv <|
          by
            simpa using
              (mem_openDikinEllipsoid_iff f x
                (selfConcordantNewtonNextPoint f Mf .damped x hx hH) (1 / (Mf : ℝ))).1
                (@damped_step_mem_openDikinEllipsoid E _ _ _ dom Mf f _ x hx hH hMf)))
        = (Mf : ℝ) * ‖selfConcordantNewtonNextPoint f Mf .damped x hx hH - x‖[f; x] := by
            simp
    _ = (Mf : ℝ) * (δ / (1 + (Mf : ℝ) * δ)) := by
      rw [show
          ‖selfConcordantNewtonNextPoint f Mf .damped x hx hH - x‖[f; x] =
            δ / (1 + (Mf : ℝ) * δ) by
          simpa [δ] using (@damped_step_localNorm_eq E _ _ _ dom Mf f _ x hx hH)]
    _ = ω' (NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH) := by
      rw [selfConcordantOmegaDeriv_apply]
      rw [hcoetω]
      ring
    _ = ↑(selfConcordantOmegaStarArg 1
          (ω' (NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH))
          (by
            simpa using
              selfConcordantOmegaDeriv_lt_one
                (NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH))) := by
            simp

/-- Theorem 5.1.15: the damped Newton step
`x ↦ x - (1 + M_f λ_f(x))⁻¹ (∇² f(x))⁻¹ ∇ f(x)` decreases the objective by at least
`M_f⁻² ω(M_f λ_f(x))` for a positive self-concordance parameter `M_f`. -/
theorem selfConcordant_dampedNewtonStep_value_decrease
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) (hMf : Mf ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    f (selfConcordantNewtonNextPoint f Mf .damped x hx hH) ≤
      f x -
        (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω (NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH) :=
  by
    dsimp
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let tω : Set.Ioi (-1 : ℝ) := NewtonDecrement.omegaArgOfDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .damped x hx hH
    have hδ_nonneg : 0 ≤ δ := by
      simpa [δ] using NewtonDecrement.ofDetNeZero_nonneg Mf f hx hH
    have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
    have hMf_pos : 0 < (Mf : ℝ) := by
      exact_mod_cast hMf_pos_nn
    have hMf_ne : (Mf : ℝ) ≠ 0 := ne_of_gt hMf_pos
    have hxPlus_mem :
        xPlus ∈ W⁰[f; x](1 / (Mf : ℝ)) := by
      -- The damped Newton update stays inside the admissible Dikin ellipsoid.
      simpa [xPlus] using
        (damped_step_mem_openDikinEllipsoid (dom := dom) (Mf := Mf) (f := f) hx hH hMf)
    have hrawTau_lt :
        (Mf : ℝ) * ‖xPlus - x‖[f; x] < 1 := by
      exact
        mf_mul_lt_one_of_lt_inv <|
          by
            simpa [xPlus] using
              (mem_openDikinEllipsoid_iff f x xPlus (1 / (Mf : ℝ))).1 hxPlus_mem
    let rawTau : Set.Iio (1 : ℝ) := selfConcordantOmegaStarArg Mf ‖xPlus - x‖[f; x] hrawTau_lt
    have hupper_raw :
        f xPlus ≤
          f x + inner ℝ (∇ f x) (xPlus - x) +
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* rawTau := by
      -- Keep the owner-level Taylor bound on its canonical remainder subtype.
      simpa [xPlus, rawTau] using
        (IsSelfConcordantOnWith.localNorm_taylor_upper_bound_with_selfConcordantOmegaStar
          (dom := dom) (Mf := Mf) (f := f) inferInstance hx hxPlus_mem)
    have hτ_lt :
        ((1 : NNReal) : ℝ) * ((tω : ℝ) / (1 + (tω : ℝ))) < 1 := by
      simpa [selfConcordantOmegaDeriv_apply] using selfConcordantOmegaDeriv_lt_one tω
    let τω : Set.Iio (1 : ℝ) :=
      selfConcordantOmegaStarArg 1 ((tω : ℝ) / (1 + (tω : ℝ))) hτ_lt
    have hcoetω : (tω : ℝ) = (Mf : ℝ) * δ := by
      simpa [δ, tω] using (NewtonDecrement.coe_omegaArgOfDetNeZero Mf f hx hH)
    have hτeq :
        rawTau =
          τω := by
      -- Normalize the Taylor remainder argument to the canonical `ω'(M_f λ_f(x))` point.
      apply Subtype.ext
      calc
        (rawTau : ℝ) = (Mf : ℝ) * ‖xPlus - x‖[f; x] := by
          simp [rawTau]
        _ = (Mf : ℝ) * (δ / (1 + (Mf : ℝ) * δ)) := by
          rw [show ‖xPlus - x‖[f; x] = δ / (1 + (Mf : ℝ) * δ) by
            simpa [δ, xPlus] using
              (damped_step_localNorm_eq (dom := dom) (Mf := Mf) (f := f) hx hH)]
        _ = (tω : ℝ) / (1 + (tω : ℝ)) := by
          rw [hcoetω]
          ring
        _ = (τω : ℝ) := by
          simp [τω]
    have hupper :
        f xPlus ≤
          f x + inner ℝ (∇ f x) (xPlus - x) +
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
      -- Rewrite the owner-level Taylor bound using the normalized `ω_*` argument.
      rw [← hτeq]
      exact hupper_raw
    have hpair :
        inner ℝ (∇ f x) (xPlus - x) =
          -(δ ^ (2 : ℕ) / (1 + (Mf : ℝ) * δ)) := by
      -- Evaluate the affine Taylor term on the damped Newton displacement.
      simpa [δ, xPlus] using
        (damped_step_gradient_pairing_eq (dom := dom) (Mf := Mf) (f := f) hx hH)
    have hpair_scalar :
        δ ^ (2 : ℕ) / (1 + (Mf : ℝ) * δ) =
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ((tω : ℝ) * ω' tω) := by
      -- Put the Newton decrement contribution into the canonical `t ω'(t)` normal form.
      rw [selfConcordantOmegaDeriv_apply, hcoetω]
      field_simp [hMf_ne]
    have htω_dom : -1 < ((1 : NNReal) : ℝ) * (tω : ℝ) := by
      rw [show (((1 : NNReal) : ℝ)) = (1 : ℝ) by norm_num, hcoetω]
      nlinarith
    have htω_eq :
        selfConcordantOmegaArg 1 (tω : ℝ) htω_dom =
          tω := by
      apply Subtype.ext
      simp [tω]
    have hfenchel :
        ω tω = (tω : ℝ) * ω' tω - ω_* τω := by
      -- The conjugate identity collapses the affine term and the `ω_*` remainder to `ω`.
      simpa [tω, τω, htω_eq, selfConcordantOmegaDeriv_apply] using
        (selfConcordantOmega_eq_mul_selfConcordantOmegaDeriv_sub_selfConcordantOmegaStar
          (t := (tω : ℝ)) tω.2)
    have hscalar :
        -(δ ^ (2 : ℕ) / (1 + (Mf : ℝ) * δ)) +
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω =
          -((1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω) := by
      -- Collect the two scalar contributions under the common `M_f⁻²` factor.
      rw [hpair_scalar, hfenchel]
      ring
    have hmain :
        f xPlus ≤ f x - ((1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω) := by
      -- Assemble the Taylor upper bound, the Newton pairing formula, and the Fenchel collapse.
      linarith [hupper, hpair, hscalar]
    simpa [xPlus, tω] using hmain

end
