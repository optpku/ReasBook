/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "State" => E × E × ℝ

/- Primary domain: optimal-method recurrences and exact gradient-step descent on real Hilbert
spaces. The source text is written on `ℝⁿ`, but the owner layer already lives on a general
real inner-product space.

Owner-style declarations sampled in this domain:
* `OptimalMethodRecurrence` in `Algorithm_2_2`, which owns the canonical
  `(x_k, y_k, v_k, α_k, γ_k)` recurrence data;
* `GeneralOptimalMethodScheme` in `Algorithm_2_2`, which adds the owner step-`(c)` descent
  inequality;
* `gradient_step_value_descent_of_lipschitzGradient` in `Lemma_2_16`, the source-facing
  `1 / L` descent estimate under the exact differentiability and Lipschitz-gradient hypotheses
  used by the algorithm;
* `constantStepSchemeIII` in `Algorithm_2_5`, which shows the chapter style for a source-facing
  recursive algorithm with projection API and a bridge to an owner recurrence structure.

Best owner abstraction:
* `source-facing`: the recursive Algorithm 2.3 trajectory and its named sequences;
* `core/canonical`: `OptimalMethodRecurrence` and `GeneralOptimalMethodScheme`;
* `bridge/view`: `constantStepSchemeIToOptimalMethodRecurrence` and
  `constantStepSchemeIToGeneralOptimalMethodScheme`.

Primitive data:
* the recursive state `(x_k, v_k, γ_k)`.

Derived API:
* `α_k` as the canonical positive root of the quadratic step-`(a)` equation;
* `y_k` from the textbook interpolation formula;
* the owner optimal-method structures recovered from those recursive sequences. -/

section

/-- The canonical positive root of the optimal-method quadratic equation
`L * α^2 = (1 - α) * γ + α * μ`. -/
def constantStepSchemeIAlphaNext
    (L mu gamma : ℝ) : ℝ :=
  ((mu - gamma) + Real.sqrt ((gamma - mu) ^ (2 : ℕ) + 4 * L * gamma)) / (2 * L)

/-- Under `L > 0` and `γ > 0`, the canonical root satisfies the defining optimal-method equation.
-/
theorem constantStepSchemeIAlphaNext_satisfies_equation
    {L mu gamma : ℝ}
    (hL : 0 < L) (hgamma : 0 < gamma) :
    L * constantStepSchemeIAlphaNext L mu gamma ^ (2 : ℕ) =
      (1 - constantStepSchemeIAlphaNext L mu gamma) * gamma +
        constantStepSchemeIAlphaNext L mu gamma * mu := by
  unfold constantStepSchemeIAlphaNext
  set d : ℝ := (gamma - mu) ^ (2 : ℕ) + 4 * L * gamma
  have hd : 0 ≤ d := by
    dsimp [d]
    nlinarith [sq_nonneg (gamma - mu)]
  have hs : Real.sqrt d ^ (2 : ℕ) = d := by
    nlinarith [Real.sq_sqrt hd]
  field_simp [hL.ne']
  nlinarith [hs]

/-- The canonical root is positive whenever `L > 0` and `γ > 0`. -/
theorem constantStepSchemeIAlphaNext_pos
    {L mu gamma : ℝ}
    (hL : 0 < L) (hgamma : 0 < gamma) :
    0 < constantStepSchemeIAlphaNext L mu gamma := by
  unfold constantStepSchemeIAlphaNext
  set d : ℝ := (gamma - mu) ^ (2 : ℕ) + 4 * L * gamma
  have hsq : (gamma - mu) ^ (2 : ℕ) < d := by
    dsimp [d]
    nlinarith
  have hsqrt : |gamma - mu| < Real.sqrt d := by
    have hsqrt := Real.sqrt_lt_sqrt (show 0 ≤ (gamma - mu) ^ (2 : ℕ) by positivity) hsq
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  have hnum : 0 < (mu - gamma) + Real.sqrt d := by
    have hbound : gamma - mu < Real.sqrt d :=
      lt_of_le_of_lt (le_abs_self (gamma - mu)) hsqrt
    linarith
  have hden : 0 < 2 * L := by
    positivity
  exact div_pos hnum hden

/-- If `μ < L`, then the canonical root lies strictly below `1`. -/
theorem constantStepSchemeIAlphaNext_lt_one
    {L mu gamma : ℝ}
    (hL : 0 < L) (hmu : mu < L) (hgamma : 0 < gamma) :
    constantStepSchemeIAlphaNext L mu gamma < 1 := by
  unfold constantStepSchemeIAlphaNext
  set d : ℝ := (gamma - mu) ^ (2 : ℕ) + 4 * L * gamma
  have hd : 0 ≤ d := by
    dsimp [d]
    nlinarith [sq_nonneg (gamma - mu)]
  have hright : 0 < 2 * L + gamma - mu := by
    nlinarith
  have hsq : d < (2 * L + gamma - mu) ^ (2 : ℕ) := by
    dsimp [d]
    nlinarith
  have hsqrt : Real.sqrt d < 2 * L + gamma - mu := by
    by_contra hs
    have hs' : 2 * L + gamma - mu ≤ Real.sqrt d := not_lt.mp hs
    have : (2 * L + gamma - mu) ^ (2 : ℕ) ≤ d := by
      nlinarith [Real.sq_sqrt hd, hs', hright.le]
    linarith
  have hden : 0 < 2 * L := by
    positivity
  rw [div_lt_iff₀ hden]
  linarith

/-- Under `L > 0`, `μ < L`, and `γ > 0`, the canonical root belongs to `(0, 1)`. -/
theorem constantStepSchemeIAlphaNext_mem_Ioo
    {L mu gamma : ℝ}
    (hL : 0 < L) (hmu : mu < L) (hgamma : 0 < gamma) :
    constantStepSchemeIAlphaNext L mu gamma ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨constantStepSchemeIAlphaNext_pos hL hgamma,
    constantStepSchemeIAlphaNext_lt_one hL hmu hgamma⟩

private def constantStepSchemeIAlphaState
    (L mu : ℝ) (state : State) : ℝ :=
  constantStepSchemeIAlphaNext L mu state.2.2

private def constantStepSchemeIGammaNextState
    (L mu : ℝ) (state : State) : ℝ :=
  L * constantStepSchemeIAlphaState L mu state ^ (2 : ℕ)

private def constantStepSchemeIYState
    (L mu : ℝ) (state : State) : E :=
  let xk := state.1
  let vk := state.2.1
  let gammak := state.2.2
  let alphak := constantStepSchemeIAlphaState L mu state
  let gammaNext := constantStepSchemeIGammaNextState L mu state
  (1 / (gammak + alphak * mu)) •
    ((alphak * gammak) • vk + gammaNext • xk)

private def constantStepSchemeIStep
    (f : E → ℝ) (L mu : ℝ) (state : State) : State :=
  let vk := state.2.1
  let gammak := state.2.2
  let alphak := constantStepSchemeIAlphaState L mu state
  let gammaNext := constantStepSchemeIGammaNextState L mu state
  let yk := constantStepSchemeIYState L mu state
  let xNext := yk - (1 / L) • ∇ f yk
  let vNext :=
    (1 / gammaNext) •
      (((1 - alphak) * gammak) • vk +
        (alphak * mu) • yk -
        alphak • ∇ f yk)
  (xNext, vNext, gammaNext)

/-- Algorithm 2.3: the recursive type-I optimal-method trajectory. The primitive recursive state
is `(x_k, v_k, γ_k)`; the source-named quantities `α_k` and `y_k` are the canonical derived
projections determined by step `(a)` and step `(b)`. -/
noncomputable def constantStepSchemeI
    (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ) :
    ℕ → State
  | 0 => (x0, x0, gamma0)
  | k + 1 => constantStepSchemeIStep f L mu (constantStepSchemeI f L mu x0 gamma0 k)

/-- The iterate sequence `x_k` of Algorithm 2.3. -/
noncomputable def constantStepSchemeIX
    (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ) :
    ℕ → E :=
  fun k ↦ (constantStepSchemeI f L mu x0 gamma0 k).1

/-- The estimating-sequence centers `v_k` of Algorithm 2.3. -/
noncomputable def constantStepSchemeIV
    (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ) :
    ℕ → E :=
  fun k ↦ (constantStepSchemeI f L mu x0 gamma0 k).2.1

/-- The curvature sequence `γ_k` of Algorithm 2.3. -/
noncomputable def constantStepSchemeIGamma
    (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ) :
    ℕ → ℝ :=
  fun k ↦ (constantStepSchemeI f L mu x0 gamma0 k).2.2

/-- The coefficient sequence `α_k` of Algorithm 2.3, obtained from the canonical positive root of
the quadratic step-`(a)` equation. -/
noncomputable def constantStepSchemeIAlpha
    (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ) :
    ℕ → ℝ :=
  fun k ↦ constantStepSchemeIAlphaState L mu (constantStepSchemeI f L mu x0 gamma0 k)

/-- The interpolation sequence `y_k` of Algorithm 2.3. -/
noncomputable def constantStepSchemeIY
    (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ) :
    ℕ → E :=
  fun k ↦ constantStepSchemeIYState L mu (constantStepSchemeI f L mu x0 gamma0 k)

section Trajectory

variable (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ)

local notation "xSeq" => constantStepSchemeIX f L mu x0 gamma0
local notation "vSeq" => constantStepSchemeIV f L mu x0 gamma0
local notation "gammaSeq" => constantStepSchemeIGamma f L mu x0 gamma0
local notation "alphaSeq" => constantStepSchemeIAlpha f L mu x0 gamma0
local notation "ySeq" => constantStepSchemeIY f L mu x0 gamma0

@[simp] theorem constantStepSchemeIX_zero
    :
    xSeq 0 = x0 :=
  rfl

@[simp] theorem constantStepSchemeIV_zero
    :
    vSeq 0 = x0 :=
  rfl

@[simp] theorem constantStepSchemeIGamma_zero
    :
    gammaSeq 0 = gamma0 :=
  rfl

@[simp] theorem constantStepSchemeIAlpha_eq
    (k : ℕ) :
    alphaSeq k = constantStepSchemeIAlphaNext L mu (gammaSeq k) :=
  rfl

/-- The interpolation sequence is given by the textbook weighted-average formula. -/
theorem constantStepSchemeIY_eq
    (k : ℕ) :
    ySeq k =
      (1 / (gammaSeq k + alphaSeq k * mu)) •
        ((alphaSeq k * gammaSeq k) • vSeq k +
          gammaSeq (k + 1) • xSeq k) := by
  rfl

/-- The exact step-`(c)` update of Algorithm 2.3. -/
@[simp] theorem constantStepSchemeIX_succ
    (k : ℕ) :
    xSeq (k + 1) = ySeq k - (1 / L) • ∇ f (ySeq k) :=
  rfl

/-- The center update of Algorithm 2.3. -/
theorem constantStepSchemeIV_succ
    (k : ℕ) :
    vSeq (k + 1) =
      (1 / gammaSeq (k + 1)) •
        (((1 - alphaSeq k) * gammaSeq k) • vSeq k +
          (alphaSeq k * mu) • ySeq k -
          alphaSeq k • ∇ f (ySeq k)) := by
  rfl

end Trajectory

/-- The curvature sequence stays positive once `γ₀ > 0` and `L > 0`. -/
theorem constantStepSchemeIGamma_pos
    (f : E → ℝ) (L mu : ℝ) (x0 : E) {gamma0 : ℝ}
    (hL : 0 < L) (hgamma0 : 0 < gamma0) :
    ∀ k : ℕ, 0 < constantStepSchemeIGamma f L mu x0 gamma0 k
  | 0 => by
      simpa using hgamma0
  | k + 1 => by
      have hk : 0 < constantStepSchemeIGamma f L mu x0 gamma0 k :=
        constantStepSchemeIGamma_pos f L mu x0 hL hgamma0 k
      have hα :
          0 <
            constantStepSchemeIAlphaNext L mu
              (constantStepSchemeIGamma f L mu x0 gamma0 k) :=
        constantStepSchemeIAlphaNext_pos hL hk
      have hsucc :
          0 <
            L *
              constantStepSchemeIAlphaNext L mu
                (constantStepSchemeIGamma f L mu x0 gamma0 k) ^ (2 : ℕ) := by
        positivity
      simpa [constantStepSchemeIAlpha_eq] using hsucc

/-- Every coefficient `α_k` is positive once `γ₀ > 0` and `L > 0`. -/
theorem constantStepSchemeIAlpha_pos
    (f : E → ℝ) (L mu : ℝ) (x0 : E) {gamma0 : ℝ}
    (hL : 0 < L) (hgamma0 : 0 < gamma0) (k : ℕ) :
    0 < constantStepSchemeIAlpha f L mu x0 gamma0 k := by
  simpa [constantStepSchemeIAlpha_eq] using
    constantStepSchemeIAlphaNext_pos hL
      (constantStepSchemeIGamma_pos f L mu x0 hL hgamma0 k)

/-- Every coefficient `α_k` lies below `1` once `μ < L`. -/
theorem constantStepSchemeIAlpha_lt_one
    (f : E → ℝ) (L mu : ℝ) (x0 : E) {gamma0 : ℝ}
    (hL : 0 < L) (hmu : mu < L) (hgamma0 : 0 < gamma0) (k : ℕ) :
    constantStepSchemeIAlpha f L mu x0 gamma0 k < 1 := by
  simpa [constantStepSchemeIAlpha_eq] using
    constantStepSchemeIAlphaNext_lt_one hL hmu
      (constantStepSchemeIGamma_pos f L mu x0 hL hgamma0 k)

/-- Every coefficient `α_k` belongs to `(0, 1)` under the canonical positivity hypotheses. -/
theorem constantStepSchemeIAlpha_mem_Ioo
    (f : E → ℝ) (L mu : ℝ) (x0 : E) {gamma0 : ℝ}
    (hL : 0 < L) (hmu : mu < L) (hgamma0 : 0 < gamma0) (k : ℕ) :
    constantStepSchemeIAlpha f L mu x0 gamma0 k ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨constantStepSchemeIAlpha_pos f L mu x0 hL hgamma0 k,
    constantStepSchemeIAlpha_lt_one f L mu x0 hL hmu hgamma0 k⟩

/-- The recursive coefficients satisfy the optimal-method quadratic relation. -/
theorem constantStepSchemeIAlpha_equation
    (f : E → ℝ) (L mu : ℝ) (x0 : E) {gamma0 : ℝ}
    (hL : 0 < L) (hgamma0 : 0 < gamma0) (k : ℕ) :
    L * constantStepSchemeIAlpha f L mu x0 gamma0 k ^ (2 : ℕ) =
      (1 - constantStepSchemeIAlpha f L mu x0 gamma0 k) *
          constantStepSchemeIGamma f L mu x0 gamma0 k +
        constantStepSchemeIAlpha f L mu x0 gamma0 k * mu := by
  simpa [constantStepSchemeIAlpha_eq] using
    constantStepSchemeIAlphaNext_satisfies_equation hL
      (constantStepSchemeIGamma_pos f L mu x0 hL hgamma0 k)

/-- The recursive curvature sequence satisfies the owner optimal-method update law. -/
theorem constantStepSchemeIGamma_succ
    (f : E → ℝ) (L mu : ℝ) (x0 : E) {gamma0 : ℝ}
    (hL : 0 < L) (hgamma0 : 0 < gamma0) (k : ℕ) :
    constantStepSchemeIGamma f L mu x0 gamma0 (k + 1) =
      (1 - constantStepSchemeIAlpha f L mu x0 gamma0 k) *
          constantStepSchemeIGamma f L mu x0 gamma0 k +
        constantStepSchemeIAlpha f L mu x0 gamma0 k * mu := by
  calc
    constantStepSchemeIGamma f L mu x0 gamma0 (k + 1)
        = L * constantStepSchemeIAlpha f L mu x0 gamma0 k ^ (2 : ℕ) := rfl
    _ =
        (1 - constantStepSchemeIAlpha f L mu x0 gamma0 k) *
            constantStepSchemeIGamma f L mu x0 gamma0 k +
          constantStepSchemeIAlpha f L mu x0 gamma0 k * mu :=
      constantStepSchemeIAlpha_equation f L mu x0 hL hgamma0 k

/-- Under differentiability and `L`-Lipschitz gradient smoothness, the exact step of
Algorithm 2.3 satisfies the owner descent inequality on the ambient real Hilbert space. -/
theorem constantStepSchemeIX_succ_le
    {f : E → ℝ} {L mu : ℝ} {x0 : E} {gamma0 : ℝ}
    (hL : 0 < L)
    (hDiff : Differentiable ℝ f)
    (hGrad : LipschitzWith ⟨L, le_of_lt hL⟩ (∇ f))
    (k : ℕ) :
    f (constantStepSchemeIX f L mu x0 gamma0 (k + 1)) ≤
      f (constantStepSchemeIY f L mu x0 gamma0 k) -
        (1 / (2 * L)) * ‖∇ f (constantStepSchemeIY f L mu x0 gamma0 k)‖ ^ (2 : ℕ) := by
  simpa [constantStepSchemeIX_succ] using
    gradient_step_value_descent_of_lipschitzGradient
      f hL hDiff hGrad (constantStepSchemeIY f L mu x0 gamma0 k)

/-- The recursive Algorithm 2.3 trajectory, viewed through the owner optimal-method recurrence
API. -/
def constantStepSchemeIToOptimalMethodRecurrence
    (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ)
    (hL : 0 < L) (hmu_nonneg : 0 ≤ mu) (hmu : mu < L) (hgamma0 : 0 < gamma0) :
    OptimalMethodRecurrence f L mu x0 gamma0 where
  L_pos := hL
  mu_nonneg := hmu_nonneg
  gamma0_pos := hgamma0
  x := constantStepSchemeIX f L mu x0 gamma0
  y := constantStepSchemeIY f L mu x0 gamma0
  v := constantStepSchemeIV f L mu x0 gamma0
  alpha := constantStepSchemeIAlpha f L mu x0 gamma0
  gamma := constantStepSchemeIGamma f L mu x0 gamma0
  x_zero := constantStepSchemeIX_zero f L mu x0 gamma0
  v_zero := constantStepSchemeIV_zero f L mu x0 gamma0
  gamma_zero := constantStepSchemeIGamma_zero f L mu x0 gamma0
  alpha_mem_Ioo := constantStepSchemeIAlpha_mem_Ioo f L mu x0 hL hmu hgamma0
  alpha_equation := constantStepSchemeIAlpha_equation f L mu x0 hL hgamma0
  gamma_succ := constantStepSchemeIGamma_succ f L mu x0 hL hgamma0
  y_eq := constantStepSchemeIY_eq f L mu x0 gamma0
  v_succ := constantStepSchemeIV_succ f L mu x0 gamma0

/-- Forgetting the exact step update and retaining the induced owner descent estimate yields the
canonical `GeneralOptimalMethodScheme`. -/
def constantStepSchemeIToGeneralOptimalMethodScheme
    (f : E → ℝ) (L mu : ℝ) (x0 : E) (gamma0 : ℝ)
    (hL : 0 < L) (hmu_nonneg : 0 ≤ mu) (hmu : mu < L) (hgamma0 : 0 < gamma0)
    (hDiff : Differentiable ℝ f)
    (hGrad : LipschitzWith ⟨L, le_of_lt hL⟩ (∇ f)) :
    GeneralOptimalMethodScheme f L mu x0 gamma0 where
  toOptimalMethodRecurrence :=
    constantStepSchemeIToOptimalMethodRecurrence f L mu x0 gamma0 hL hmu_nonneg hmu hgamma0
  x_succ_le := constantStepSchemeIX_succ_le hL hDiff hGrad

end

end
