/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part18

section Chap06
section Section30

/-- The feasible set of the enlarged-perturbation program at perturbation parameter `w`: the
points `x` satisfying `fᵢ(x - xᵢ) ≤ uᵢ` for every constraint index `i`. -/
def enlargedPerturbationProgramFeasibleSet {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) (w : EnlargedPerturbationParameter m n) :
    Set (Fin n → ℝ) :=
  {x | ∀ i : Fin m, f i (x - w.xShift i) ≤ ((w.u i : ℝ) : EReal)}

/-- The convex bifunction of the enlarged-perturbation program:
`G_w(x) = f₀(x - x₀) + δ(x | fᵢ(x - xᵢ) ≤ uᵢ, i = 1, …, m)`. -/
noncomputable def enlargedPerturbationProgramBifunction {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal) :
    EnlargedPerturbationParameter m n → (Fin n → ℝ) → EReal :=
  fun w x => f0 (x - w.x0) + indicatorFunction (enlargedPerturbationProgramFeasibleSet f w) x

/-- The canonical pairing `⟪w, w*⟫` between an enlarged perturbation parameter and its dual. -/
def enlargedPerturbationDualPairing {m n : ℕ}
    (w : EnlargedPerturbationParameter m n) (wStar : EnlargedPerturbationDualParameter m n) : ℝ :=
  (w.u ⬝ᵥ wStar.uStar : ℝ) + (w.x0 ⬝ᵥ wStar.x0Star : ℝ) +
    ∑ i : Fin m, (w.xShift i ⬝ᵥ wStar.xShiftStar i : ℝ)

/-- The adjoint value of the enlarged-perturbation bifunction, defined by the infimum formula
for `G*(x*, w*)`. -/
noncomputable def adjointOfEnlargedPerturbationProgram {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EnlargedPerturbationDualParameter m n → EReal :=
  fun xStar wStar =>
    sInf (Set.range fun p : EnlargedPerturbationParameter m n × (Fin n → ℝ) =>
      enlargedPerturbationProgramBifunction f0 f p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
        (((enlargedPerturbationDualPairing p.1 wStar : ℝ) : EReal)))

/-- The sum `x₀* + ⋯ + x_m*` of the dual translation variables in the enlarged-perturbation
program. -/
def enlargedPerturbationDualTranslationSum {m n : ℕ}
    (wStar : EnlargedPerturbationDualParameter m n) : Fin n → ℝ :=
  wStar.x0Star + ∑ i : Fin m, wStar.xShiftStar i

/-- The feasibility conditions in the adjoint formula for the enlarged-perturbation program:
`u* ≥ 0` and `x₀* + ⋯ + x_m* = x*`. -/
def enlargedPerturbationDualFeasible {m n : ℕ}
    (xStar : Fin n → ℝ) (wStar : EnlargedPerturbationDualParameter m n) : Prop :=
  (∀ i : Fin m, 0 ≤ wStar.uStar i) ∧ enlargedPerturbationDualTranslationSum wStar = xStar

/-- The dual objective appearing in the adjoint formula for the enlarged-perturbation program. -/
noncomputable def enlargedPerturbationDualObjective {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (wStar : EnlargedPerturbationDualParameter m n) : EReal :=
  -fenchelConjugate n f0 wStar.x0Star -
    ∑ i : Fin m,
      fenchelConjugate n (fun x => (((wStar.uStar i : ℝ) : EReal) * f i x)) (wStar.xShiftStar i)

/-- The value of the dual maximization problem attached to the enlarged-perturbation program. -/
noncomputable def dualProgramValueOfEnlargedPerturbationProgram {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal) : EReal :=
  sSup (Set.range fun wStar : EnlargedPerturbationDualParameter m n =>
    adjointOfEnlargedPerturbationProgram f0 f 0 wStar)

/-- Helper for Theorem 6.30.22: if `f₀` is constantly `⊤`, then the enlarged-perturbation
bifunction is constantly `⊤`. -/
lemma helperForTheorem_6_30_22_bifunction_constTop {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (w : EnlargedPerturbationParameter m n) (x : Fin n → ℝ) :
    enlargedPerturbationProgramBifunction (fun _ : Fin n → ℝ => (⊤ : EReal)) f w x = (⊤ : EReal) := by
  -- Unfold the bifunction and use `⊤ + a = ⊤` in `EReal`.
  by_cases hx : x ∈ enlargedPerturbationProgramFeasibleSet f w
  · simp [enlargedPerturbationProgramBifunction, indicatorFunction, hx]
  · simp [enlargedPerturbationProgramBifunction, indicatorFunction, hx]

/-- Helper for Theorem 6.30.22: with `f₀ ≡ ⊤`, every integrand in the adjoint infimum is `⊤`,
so the adjoint value is `⊤` at every dual parameter. -/
lemma helperForTheorem_6_30_22_adjoint_constTop {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) (wStar : EnlargedPerturbationDualParameter m n) :
    adjointOfEnlargedPerturbationProgram (fun _ : Fin n → ℝ => (⊤ : EReal)) f xStar wStar = (⊤ : EReal) := by
  -- After unfolding the adjoint definition, every ranged value simplifies to `⊤`.
  simp [adjointOfEnlargedPerturbationProgram, helperForTheorem_6_30_22_bifunction_constTop]

/-- Helper for Theorem 6.30.22: the explicit one-dimensional dual witness used to refute the
infeasible branch. It has zero multiplier, zero `x₀*`, and unit translated component `x₁*`. -/
def helperForTheorem_6_30_22_counterexampleDualParameter :
    EnlargedPerturbationDualParameter 1 1 :=
  { uStar := fun _ => 0
    x0Star := fun _ => 0
    xShiftStar := fun _ _ => 1 }

/-- Helper for Theorem 6.30.22: every multiplier coordinate of the explicit dual witness is
nonnegative. -/
lemma helperForTheorem_6_30_22_counterexampleDualParameter_nonnegative :
    ∀ i : Fin 1, 0 ≤ helperForTheorem_6_30_22_counterexampleDualParameter.uStar i := by
  -- The unique multiplier coordinate of the witness is `0`.
  intro i
  simp [helperForTheorem_6_30_22_counterexampleDualParameter]

/-- Helper for Theorem 6.30.22: the translation sum of the explicit dual witness is the constant
vector with value `1`. -/
lemma helperForTheorem_6_30_22_counterexampleDualParameter_translationSum :
    enlargedPerturbationDualTranslationSum
        helperForTheorem_6_30_22_counterexampleDualParameter =
      (fun _ : Fin 1 => (1 : ℝ)) := by
  -- The witness has `x₀* = 0` and `x₁* = 1`, so the sum is constantly `1`.
  ext i
  simp [enlargedPerturbationDualTranslationSum,
    helperForTheorem_6_30_22_counterexampleDualParameter]

/-- Helper for Theorem 6.30.22: the explicit bad witness fails the balance equation
`x₀* + x₁* = 0`; its translation sum is nonzero even though its multiplier is nonnegative. -/
lemma helperForTheorem_6_30_22_counterexampleDualParameter_translationSum_ne_zero :
    enlargedPerturbationDualTranslationSum
        helperForTheorem_6_30_22_counterexampleDualParameter ≠
      (0 : Fin 1 → ℝ) := by
  -- Substitute the explicit translation sum `1` and evaluate at the unique coordinate.
  intro hZero
  have hOneVecEqZero : (fun _ : Fin 1 => (1 : ℝ)) = (0 : Fin 1 → ℝ) := by
    exact helperForTheorem_6_30_22_counterexampleDualParameter_translationSum.symm.trans hZero
  have hOneEqZero : (1 : ℝ) = 0 := by
    -- The vector contradiction reduces pointwise to `1 = 0`.
    simpa using congrArg (fun z : Fin 1 → ℝ => z 0) hOneVecEqZero
  linarith

/-- Helper for Theorem 6.30.22: the explicit dual witness is infeasible at `x* = 0`, because its
translation sum is `1` rather than `0`. -/
lemma helperForTheorem_6_30_22_counterexampleDualParameter_not_feasible :
    ¬ enlargedPerturbationDualFeasible
        (0 : Fin 1 → ℝ)
        helperForTheorem_6_30_22_counterexampleDualParameter := by
  -- Feasibility would force the witness translation sum to vanish at `x* = 0`.
  intro hFeasible
  have hOneVecEqZero : (fun _ : Fin 1 => (1 : ℝ)) = (0 : Fin 1 → ℝ) := by
    -- Compare the explicit translation-sum formula with the feasibility equality.
    exact helperForTheorem_6_30_22_counterexampleDualParameter_translationSum.symm.trans
      hFeasible.2
  have hOneEqZero : (1 : ℝ) = 0 := by
    -- Evaluating at the unique coordinate exposes the contradiction `1 = 0`.
    simpa using congrArg (fun z : Fin 1 → ℝ => z 0) hOneVecEqZero
  linarith

/-- Helper for Theorem 6.30.22: for the explicit dual witness, the adjoint value with
`f₀ ≡ ⊤` and `f₁ ≡ 0` is exactly `⊤`. -/
lemma helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_eq_top :
    adjointOfEnlargedPerturbationProgram
        (fun _ : Fin 1 → ℝ => (⊤ : EReal))
        (fun _ _ => (0 : EReal))
        (0 : Fin 1 → ℝ)
        helperForTheorem_6_30_22_counterexampleDualParameter = (⊤ : EReal) := by
  -- The constant-`⊤` objective forces every adjoint value to be `⊤`.
  simpa using
    helperForTheorem_6_30_22_adjoint_constTop
      (m := 1) (n := 1)
      (f := fun _ _ => (0 : EReal))
      (xStar := (0 : Fin 1 → ℝ))
      (wStar := helperForTheorem_6_30_22_counterexampleDualParameter)

/-- Helper for Theorem 6.30.22: for the explicit dual witness, the dual objective associated to
the counterexample data `f₀ ≡ ⊤` and `f₁ ≡ 0` evaluates to `⊥`. -/
lemma helperForTheorem_6_30_22_counterexampleDualParameter_dualObjective_eq_bot :
    enlargedPerturbationDualObjective
        (m := 1) (n := 1)
        (fun _ : Fin 1 → ℝ => (⊤ : EReal))
        (fun _ : Fin 1 => fun _ : Fin 1 → ℝ => (0 : EReal))
        helperForTheorem_6_30_22_counterexampleDualParameter = (⊥ : EReal) := by
  -- Unfold the dual objective. The conjugate of the constant-`⊤` function is `⊥`, and the
  -- conjugate of the constant-`0` function at a nonzero dual vector is `⊤`. The resulting
  -- arithmetic simplifies to `⊥`.
  have hTop :
      fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (⊤ : EReal)) (fun _ => (0 : ℝ)) = (⊥ : EReal) := by
    -- Every affine minorant of the constant-`⊤` function is trivial, so the conjugate is `⊥`.
    unfold fenchelConjugate
    simp
  have hZero :
      fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)) (fun _ => (1 : ℝ)) = (⊤ : EReal) := by
    -- At the nonzero dual vector `1`, the conjugate of the constant-`0` function is `⊤` because
    -- the linear form `x ↦ ⟪x, 1⟫` is unbounded above on `ℝ`.
    unfold fenchelConjugate
    rw [sSup_eq_top]
    intro b hb
    by_cases hbot : b = (⊥ : EReal)
    · -- If the lower bound is `⊥`, any ranged point provides `b < a`.
      subst hbot
      refine ⟨(0 : EReal), ?_, ?_⟩
      refine ⟨(fun _ : Fin 1 => (0 : ℝ)), ?_⟩
      simp [dotProduct]
      simp
    · -- Otherwise, pick `x = b.toReal + 1` so `⟪x, 1⟫` lies strictly above `b`.
      refine ⟨(((b.toReal + 1 : ℝ)) : EReal), ?_, ?_⟩
      · refine ⟨(fun _ : Fin 1 => (b.toReal + 1 : ℝ)), ?_⟩
        simp [dotProduct]
      · have hcoe : (((b.toReal : ℝ)) : EReal) = b := by
            have hTop : b ≠ (⊤ : EReal) := by
              exact ne_of_lt hb
            simpa using (EReal.coe_toReal (x := b) hTop hbot)
        rw [← hcoe]
        have hreal : b.toReal < b.toReal + 1 := by linarith
        exact_mod_cast hreal
  simp [enlargedPerturbationDualObjective, helperForTheorem_6_30_22_counterexampleDualParameter,
    hTop, hZero]

/-- Helper for Theorem 6.30.22: for the explicit witness, the adjoint value and the explicit dual
objective are separated by the extremes `⊤` and `⊥`. -/
lemma helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_ne_dualObjective :
    adjointOfEnlargedPerturbationProgram
        (fun _ : Fin 1 → ℝ => (⊤ : EReal))
        (fun _ _ => (0 : EReal))
        (0 : Fin 1 → ℝ)
        helperForTheorem_6_30_22_counterexampleDualParameter ≠
      enlargedPerturbationDualObjective
        (m := 1) (n := 1)
        (fun _ : Fin 1 → ℝ => (⊤ : EReal))
        (fun _ : Fin 1 => fun _ : Fin 1 → ℝ => (0 : EReal))
        helperForTheorem_6_30_22_counterexampleDualParameter := by
  -- Evaluate both sides explicitly: the adjoint is `⊤`, while the dual objective is `⊥`.
  rw [helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_eq_top,
    helperForTheorem_6_30_22_counterexampleDualParameter_dualObjective_eq_bot]
  exact top_ne_bot

/-- Helper for Theorem 6.30.22: therefore the explicit dual witness gives an adjoint value that is
not `⊥`. -/
lemma helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_ne_bot :
    adjointOfEnlargedPerturbationProgram
        (fun _ : Fin 1 → ℝ => (⊤ : EReal))
        (fun _ _ => (0 : EReal))
        (0 : Fin 1 → ℝ)
        helperForTheorem_6_30_22_counterexampleDualParameter ≠ (⊥ : EReal) := by
  -- Replace the adjoint by the explicit value `⊤`.
  intro hAdjointBot
  have hTopEqBot : (⊤ : EReal) = (⊥ : EReal) := by
    exact helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_eq_top.symm.trans
      hAdjointBot
  exact top_ne_bot hTopEqBot

/-- Helper for Theorem 6.30.22: the explicit counterexample already lies in the stronger
subclass where `u* ≥ 0` and only the translation-balance equation fails, yet the adjoint still
equals `⊤`. Thus the obstruction is not caused by negative multipliers. -/
lemma helperForTheorem_6_30_22_exists_nonnegativeTranslationMismatchWitness_with_adjoint_eq_top :
    ∃ wStar : EnlargedPerturbationDualParameter 1 1,
      (∀ i : Fin 1, 0 ≤ wStar.uStar i) ∧
      enlargedPerturbationDualTranslationSum wStar ≠ (0 : Fin 1 → ℝ) ∧
      adjointOfEnlargedPerturbationProgram
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ _ => (0 : EReal))
          (0 : Fin 1 → ℝ)
          wStar = (⊤ : EReal) := by
  -- Reuse the explicit bad witness: its multiplier is `0`, its translation sum is `1`, and its
  -- adjoint has already been computed to be `⊤`.
  refine ⟨helperForTheorem_6_30_22_counterexampleDualParameter, ?_⟩
  refine ⟨helperForTheorem_6_30_22_counterexampleDualParameter_nonnegative, ?_, ?_⟩
  · -- The witness fails only the translation-balance equation at `x* = 0`.
    exact helperForTheorem_6_30_22_counterexampleDualParameter_translationSum_ne_zero
  · -- Nevertheless its adjoint remains `⊤`.
    exact helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_eq_top

/-- Helper for Theorem 6.30.22: even the stronger branch
`u* ≥ 0` and `x₀* + x₁* ≠ 0` imply `adjoint = ⊥` is false for the counterexample data. This
shows that any upstream repair must do more than merely separate the nonnegativity and
translation-balance failures. -/
lemma helperForTheorem_6_30_22_translationMismatchBranch_isFalse :
    ¬ (∀ wStar : EnlargedPerturbationDualParameter 1 1,
        (∀ i : Fin 1, 0 ≤ wStar.uStar i) →
        enlargedPerturbationDualTranslationSum wStar ≠ (0 : Fin 1 → ℝ) →
          adjointOfEnlargedPerturbationProgram
            (fun _ : Fin 1 → ℝ => (⊤ : EReal))
            (fun _ _ => (0 : EReal))
            (0 : Fin 1 → ℝ)
            wStar = (⊥ : EReal)) := by
  intro hBranch
  have hAdjointEqBot :
      adjointOfEnlargedPerturbationProgram
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ _ => (0 : EReal))
          (0 : Fin 1 → ℝ)
          helperForTheorem_6_30_22_counterexampleDualParameter = (⊥ : EReal) :=
    hBranch
      helperForTheorem_6_30_22_counterexampleDualParameter
      helperForTheorem_6_30_22_counterexampleDualParameter_nonnegative
      helperForTheorem_6_30_22_counterexampleDualParameter_translationSum_ne_zero
  -- The stronger branch still contradicts the explicit computation `adjoint = ⊤`.
  exact helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_ne_bot hAdjointEqBot

/-- Helper for Theorem 6.30.22: in the one-dimensional case, there is a dual parameter with
`u* ≥ 0` whose translation sum is not zero, hence it is dual-infeasible at `x* = 0`. -/
lemma helperForTheorem_6_30_22_exists_dualInfeasibleParameter :
    ∃ wStar : EnlargedPerturbationDualParameter 1 1,
      (∀ i : Fin 1, 0 ≤ wStar.uStar i) ∧
      ¬ enlargedPerturbationDualFeasible (0 : Fin 1 → ℝ) wStar := by
  -- Use the explicit witness introduced above so later counterexample lemmas can reuse it.
  refine ⟨helperForTheorem_6_30_22_counterexampleDualParameter, ?_⟩
  exact ⟨helperForTheorem_6_30_22_counterexampleDualParameter_nonnegative,
    helperForTheorem_6_30_22_counterexampleDualParameter_not_feasible⟩

/-- Helper for Theorem 6.30.22: in dimension `1`, the theorem's infeasible branch fails for the
data `f₀ ≡ ⊤` and `f₁ ≡ 0`, because one can find a dual-infeasible parameter with adjoint value
`⊤` instead of `⊥`. -/
lemma helperForTheorem_6_30_22_infeasibleBranch_counterexample :
    ∃ xStar : Fin 1 → ℝ, ∃ wStar : EnlargedPerturbationDualParameter 1 1,
      ¬ enlargedPerturbationDualFeasible xStar wStar ∧
      adjointOfEnlargedPerturbationProgram
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ _ => (0 : EReal))
          xStar wStar = (⊤ : EReal) := by
  -- Choose `x* = 0` and the explicit dual witness whose adjoint value is already computed.
  refine ⟨0, helperForTheorem_6_30_22_counterexampleDualParameter, ?_⟩
  exact ⟨helperForTheorem_6_30_22_counterexampleDualParameter_not_feasible,
    helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_eq_top⟩

/-- Helper for Theorem 6.30.22: the concrete counterexample already gives a dual-infeasible
parameter at which the adjoint is not `⊥`. This is the exact obstruction to the theorem's
universal infeasible branch. -/
lemma helperForTheorem_6_30_22_exists_infeasibleParameter_with_adjoint_ne_bot :
    ∃ xStar : Fin 1 → ℝ, ∃ wStar : EnlargedPerturbationDualParameter 1 1,
      ¬ enlargedPerturbationDualFeasible xStar wStar ∧
      adjointOfEnlargedPerturbationProgram
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ _ => (0 : EReal))
          xStar wStar ≠ (⊥ : EReal) := by
  -- Reuse the explicit pointwise witness showing the adjoint is `⊤`, hence not `⊥`.
  refine ⟨0, helperForTheorem_6_30_22_counterexampleDualParameter, ?_⟩
  exact ⟨helperForTheorem_6_30_22_counterexampleDualParameter_not_feasible,
    helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_ne_bot⟩

/-- Helper for Theorem 6.30.22: at the explicit counterexample witness, the theorem's
`otherwise = ⊥` implication already fails. -/
lemma helperForTheorem_6_30_22_counterexampleInfeasibleBranchAtWitness_isFalse :
    ¬ (¬ enlargedPerturbationDualFeasible
            (0 : Fin 1 → ℝ)
            helperForTheorem_6_30_22_counterexampleDualParameter →
          adjointOfEnlargedPerturbationProgram
            (fun _ : Fin 1 → ℝ => (⊤ : EReal))
            (fun _ _ => (0 : EReal))
            (0 : Fin 1 → ℝ)
            helperForTheorem_6_30_22_counterexampleDualParameter = (⊥ : EReal)) := by
  -- The explicit witness is dual-infeasible, but its adjoint value was computed to be `⊤`.
  intro hBranch
  have hAdjointEqBot :
      adjointOfEnlargedPerturbationProgram
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ _ => (0 : EReal))
          (0 : Fin 1 → ℝ)
          helperForTheorem_6_30_22_counterexampleDualParameter = (⊥ : EReal) :=
    hBranch helperForTheorem_6_30_22_counterexampleDualParameter_not_feasible
  -- This contradicts the earlier explicit computation `adjoint = ⊤`.
  exact helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_ne_bot hAdjointEqBot

/-- Helper for Theorem 6.30.22: at the explicit witness
`(x*, w*) = (0, helperForTheorem_6_30_22_counterexampleDualParameter)`, the full
two-branch conjunction from the theorem fails because its infeasible branch is already false. -/
lemma helperForTheorem_6_30_22_counterexampleConjunctionAtWitness_isFalse :
    ¬ ((enlargedPerturbationDualFeasible
            (0 : Fin 1 → ℝ)
            helperForTheorem_6_30_22_counterexampleDualParameter →
          adjointOfEnlargedPerturbationProgram
            (fun _ : Fin 1 → ℝ => (⊤ : EReal))
            (fun _ _ => (0 : EReal))
            (0 : Fin 1 → ℝ)
            helperForTheorem_6_30_22_counterexampleDualParameter =
            enlargedPerturbationDualObjective
              (fun _ : Fin 1 → ℝ => (⊤ : EReal))
              (fun _ _ => (0 : EReal))
              helperForTheorem_6_30_22_counterexampleDualParameter) ∧
        (¬ enlargedPerturbationDualFeasible
              (0 : Fin 1 → ℝ)
              helperForTheorem_6_30_22_counterexampleDualParameter →
            adjointOfEnlargedPerturbationProgram
              (fun _ : Fin 1 → ℝ => (⊤ : EReal))
              (fun _ _ => (0 : EReal))
              (0 : Fin 1 → ℝ)
              helperForTheorem_6_30_22_counterexampleDualParameter = (⊥ : EReal))) := by
  intro hConj
  -- The second conjunct is exactly the implication already disproved above.
  exact helperForTheorem_6_30_22_counterexampleInfeasibleBranchAtWitness_isFalse hConj.2

-- The remaining helper development for Theorem 6.30.22 now follows the textbook proper/full-
-- domain hypotheses recorded in the theorem statement below. The earlier counterexample block for
-- the fully general `EReal` version has been intentionally removed, because it no longer matches
-- the original theorem being formalized.

/-- Helper for Theorem 6.30.22: if `f₀` is constantly `⊤`, then every adjoint value in the
defining supremum for the dual-program value is `⊤`, so the dual-program value itself is `⊤`. -/
lemma helperForTheorem_6_30_22_dualValue_constTop {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) :
    dualProgramValueOfEnlargedPerturbationProgram
        (fun _ : Fin n → ℝ => (⊤ : EReal)) f = (⊤ : EReal) := by
  -- Unfold the dual value and identify the ranged set with the singleton `{⊤}`.
  rw [dualProgramValueOfEnlargedPerturbationProgram]
  have hRange :
      Set.range
          (fun wStar : EnlargedPerturbationDualParameter m n =>
            adjointOfEnlargedPerturbationProgram
              (fun _ : Fin n → ℝ => (⊤ : EReal)) f 0 wStar) = {(⊤ : EReal)} := by
    ext y
    constructor
    · rintro ⟨wStar, rfl⟩
      -- Every adjoint value in the range is `⊤` by the constant-`⊤` computation above.
      simp [helperForTheorem_6_30_22_adjoint_constTop]
    · intro hy
      simp at hy
      rcases hy with rfl
      -- Conversely, the zero dual parameter already realizes the value `⊤`.
      refine ⟨{ uStar := 0, x0Star := 0, xShiftStar := fun _ => 0 }, ?_⟩
      simp [helperForTheorem_6_30_22_adjoint_constTop]
  rw [hRange]
  simp

/-- Helper for Theorem 6.30.22: the zero one-dimensional dual parameter used to show that the
dual-value identity can still hold for the counterexample data. -/
def helperForTheorem_6_30_22_zeroDualParameter :
    EnlargedPerturbationDualParameter 1 1 :=
  { uStar := 0
    x0Star := 0
    xShiftStar := fun _ => 0 }

/-- Helper for Theorem 6.30.22: the zero dual parameter is feasible at `x* = 0`. -/
lemma helperForTheorem_6_30_22_zeroDualParameter_feasible :
    enlargedPerturbationDualFeasible
        (0 : Fin 1 → ℝ)
        helperForTheorem_6_30_22_zeroDualParameter := by
  -- Both feasibility conditions are immediate for the zero dual parameter.
  constructor
  · intro i
    simp [helperForTheorem_6_30_22_zeroDualParameter]
  · ext i
    simp [enlargedPerturbationDualTranslationSum,
      helperForTheorem_6_30_22_zeroDualParameter]

/-- Helper for Theorem 6.30.22: the translation sum of the zero dual witness vanishes. -/
lemma helperForTheorem_6_30_22_zeroDualParameter_translationSum :
    enlargedPerturbationDualTranslationSum
        helperForTheorem_6_30_22_zeroDualParameter =
      (0 : Fin 1 → ℝ) := by
  -- The zero witness has both translated dual components equal to `0`.
  ext i
  simp [enlargedPerturbationDualTranslationSum,
    helperForTheorem_6_30_22_zeroDualParameter]

/-- Helper for Theorem 6.30.22: at the zero feasible dual parameter, the explicit dual objective
for the counterexample data equals `⊤`. -/
lemma helperForTheorem_6_30_22_zeroDualParameter_dualObjective_eq_top :
    enlargedPerturbationDualObjective
        (m := 1) (n := 1)
        (fun _ : Fin 1 → ℝ => (⊤ : EReal))
        (fun _ : Fin 1 => fun _ : Fin 1 → ℝ => (0 : EReal))
        helperForTheorem_6_30_22_zeroDualParameter = (⊤ : EReal) := by
  -- Compute the conjugates at the zero covector and substitute the zero dual parameter.
  have hTop :
      fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (⊤ : EReal)) (0 : Fin 1 → ℝ) = (⊥ : EReal) := by
    -- The constant-`⊤` function has conjugate `⊥`.
    unfold fenchelConjugate
    simp
  have hZero :
      fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal)) (0 : Fin 1 → ℝ) = (0 : EReal) := by
    -- The zero function has conjugate `0` at the zero covector.
    unfold fenchelConjugate
    simp
  simp [enlargedPerturbationDualObjective, helperForTheorem_6_30_22_zeroDualParameter, hTop, hZero]

/-- Helper for Theorem 6.30.22: for the counterexample data `f₀ ≡ ⊤` and `f₁ ≡ 0`, the
dual-value identity still holds. Hence the obstruction is confined to the theorem's universal
infeasible branch, not to the terminal `sSup` formula. -/
lemma helperForTheorem_6_30_22_counterexampleDualValueEquality_holds :
    dualProgramValueOfEnlargedPerturbationProgram
        (fun _ : Fin 1 → ℝ => (⊤ : EReal))
        (fun _ : Fin 1 => fun _ : Fin 1 → ℝ => (0 : EReal)) =
      sSup {v : EReal | ∃ wStar : EnlargedPerturbationDualParameter 1 1,
        enlargedPerturbationDualFeasible (0 : Fin 1 → ℝ) wStar ∧
          v = enlargedPerturbationDualObjective
                (fun _ : Fin 1 → ℝ => (⊤ : EReal))
                (fun _ : Fin 1 => fun _ : Fin 1 → ℝ => (0 : EReal))
                wStar} := by
  -- The left-hand side is already `⊤`, so it suffices to realize `⊤` on the feasible side too.
  rw [helperForTheorem_6_30_22_dualValue_constTop]
  symm
  rw [sSup_eq_top]
  intro b hb
  -- The feasible zero dual parameter attains the value `⊤`, which dominates every `b < ⊤`.
  refine ⟨(⊤ : EReal), ?_, ?_⟩
  refine ⟨helperForTheorem_6_30_22_zeroDualParameter,
    helperForTheorem_6_30_22_zeroDualParameter_feasible, ?_⟩
  exact helperForTheorem_6_30_22_zeroDualParameter_dualObjective_eq_top.symm
  simpa using hb

/-- Helper for Theorem 6.30.22: the explicit counterexample data simultaneously admit a feasible
dual parameter that realizes the terminal value `⊤` and a dual-infeasible parameter whose adjoint
value is also `⊤`. This packages the exact split between the surviving dual-value identity and the
failing pointwise infeasible branch. -/
lemma helperForTheorem_6_30_22_counterexampleHasFeasibleValueWitness_and_InfeasibleAdjointWitness :
    (∃ wGood : EnlargedPerturbationDualParameter 1 1,
        enlargedPerturbationDualFeasible (0 : Fin 1 → ℝ) wGood ∧
          enlargedPerturbationDualObjective
              (m := 1) (n := 1)
              (fun _ : Fin 1 → ℝ => (⊤ : EReal))
              (fun _ : Fin 1 => fun _ : Fin 1 → ℝ => (0 : EReal))
              wGood = (⊤ : EReal)) ∧
    ∃ wBad : EnlargedPerturbationDualParameter 1 1,
      ¬ enlargedPerturbationDualFeasible (0 : Fin 1 → ℝ) wBad ∧
        adjointOfEnlargedPerturbationProgram
            (fun _ : Fin 1 → ℝ => (⊤ : EReal))
            (fun _ _ => (0 : EReal))
            (0 : Fin 1 → ℝ)
            wBad = (⊤ : EReal) := by
  constructor
  · -- The zero dual parameter is feasible and realizes the terminal value `⊤`.
    refine ⟨helperForTheorem_6_30_22_zeroDualParameter, ?_⟩
    exact ⟨helperForTheorem_6_30_22_zeroDualParameter_feasible,
      helperForTheorem_6_30_22_zeroDualParameter_dualObjective_eq_top⟩
  · -- The explicit counterexample parameter is infeasible while its adjoint still equals `⊤`.
    refine ⟨helperForTheorem_6_30_22_counterexampleDualParameter, ?_⟩
    exact ⟨helperForTheorem_6_30_22_counterexampleDualParameter_not_feasible,
      helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_eq_top⟩

/-- Helper for Theorem 6.30.22: the same counterexample data admit one feasible dual witness
realizing the terminal dual value and one infeasible dual witness with adjoint value `⊤`. This
packages both witnesses in a single existential statement for later contradiction steps. -/
lemma helperForTheorem_6_30_22_counterexampleProvidesSimultaneousGoodAndBadDualWitnesses :
    ∃ wGood wBad : EnlargedPerturbationDualParameter 1 1,
      enlargedPerturbationDualFeasible (0 : Fin 1 → ℝ) wGood ∧
      enlargedPerturbationDualObjective
          (m := 1) (n := 1)
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ : Fin 1 => fun _ : Fin 1 → ℝ => (0 : EReal))
          wGood = (⊤ : EReal) ∧
      ¬ enlargedPerturbationDualFeasible (0 : Fin 1 → ℝ) wBad ∧
      adjointOfEnlargedPerturbationProgram
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ _ => (0 : EReal))
          (0 : Fin 1 → ℝ)
          wBad = (⊤ : EReal) := by
  -- Reuse the feasible zero witness for the terminal value and the infeasible counterexample
  -- witness for the failing pointwise adjoint branch.
  refine ⟨helperForTheorem_6_30_22_zeroDualParameter,
    helperForTheorem_6_30_22_counterexampleDualParameter, ?_⟩
  constructor
  · -- The zero dual parameter satisfies the feasibility conditions at `x* = 0`.
    exact helperForTheorem_6_30_22_zeroDualParameter_feasible
  constructor
  · -- The same feasible witness realizes the terminal dual value `⊤`.
    exact helperForTheorem_6_30_22_zeroDualParameter_dualObjective_eq_top
  constructor
  · -- The counterexample witness is not feasible at `x* = 0`.
    exact helperForTheorem_6_30_22_counterexampleDualParameter_not_feasible
  · -- Nevertheless, its adjoint value is still `⊤`.
    exact helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_eq_top

/-- Helper for Theorem 6.30.22: any dual-feasible witness at `x* = 0` is automatically different
from the bad counterexample witness, because that witness is not dual-feasible. -/
lemma helperForTheorem_6_30_22_feasibleWitness_ne_counterexampleDualParameter
    {wStar : EnlargedPerturbationDualParameter 1 1}
    (hFeasible : enlargedPerturbationDualFeasible (0 : Fin 1 → ℝ) wStar) :
    wStar ≠ helperForTheorem_6_30_22_counterexampleDualParameter := by
  -- If a feasible witness coincided with the bad counterexample parameter, the counterexample
  -- witness would become feasible, contradicting its explicit infeasibility proof.
  intro hEq
  have hCounterexampleFeasible :
      enlargedPerturbationDualFeasible
          (0 : Fin 1 → ℝ)
          helperForTheorem_6_30_22_counterexampleDualParameter := by
    -- Rewrite the feasible witness along the assumed equality to transfer feasibility.
    simpa [hEq] using hFeasible
  exact helperForTheorem_6_30_22_counterexampleDualParameter_not_feasible hCounterexampleFeasible

/-- Helper for Theorem 6.30.22: any one-dimensional witness whose explicit dual objective already
equals `⊤` cannot be the bad counterexample witness, because that witness has dual objective
`⊥`. -/
lemma helperForTheorem_6_30_22_topDualObjectiveWitness_ne_counterexampleDualParameter
    {wStar : EnlargedPerturbationDualParameter 1 1}
    (hObjectiveTop :
      enlargedPerturbationDualObjective
          (m := 1) (n := 1)
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ : Fin 1 => fun _ : Fin 1 → ℝ => (0 : EReal))
          wStar = (⊤ : EReal)) :
    wStar ≠ helperForTheorem_6_30_22_counterexampleDualParameter := by
  -- If a `⊤`-valued witness coincided with the bad counterexample witness, then the same explicit
  -- dual objective would have to equal both `⊤` and `⊥`.
  intro hEq
  have hBadObjectiveTop :
      enlargedPerturbationDualObjective
          (m := 1) (n := 1)
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ : Fin 1 => fun _ : Fin 1 → ℝ => (0 : EReal))
          helperForTheorem_6_30_22_counterexampleDualParameter = (⊤ : EReal) := by
    -- Rewrite the putative `⊤`-valued witness along the assumed equality to move the value to the
    -- explicit bad witness.
    simpa [hEq] using hObjectiveTop
  exact top_ne_bot
    (hBadObjectiveTop.symm.trans
      helperForTheorem_6_30_22_counterexampleDualParameter_dualObjective_eq_bot)

/-- Helper for Theorem 6.30.22: the feasible zero witness and the infeasible counterexample
witness are genuinely different dual parameters. -/
lemma helperForTheorem_6_30_22_goodAndBadWitnesses_haveDifferentTranslationSums :
    enlargedPerturbationDualTranslationSum
        helperForTheorem_6_30_22_zeroDualParameter ≠
      enlargedPerturbationDualTranslationSum
        helperForTheorem_6_30_22_counterexampleDualParameter := by
  -- The feasible zero witness has translation sum `0`, whereas the bad witness has translation
  -- sum `1`, so they are already separated by the balance equation.
  intro hEq
  have hZeroVecEqOneVec : (0 : Fin 1 → ℝ) = (fun _ : Fin 1 => (1 : ℝ)) := by
    -- Substitute the two explicit translation-sum formulas into the assumed equality.
    calc
      (0 : Fin 1 → ℝ) =
          enlargedPerturbationDualTranslationSum
            helperForTheorem_6_30_22_zeroDualParameter :=
        helperForTheorem_6_30_22_zeroDualParameter_translationSum.symm
      _ =
          enlargedPerturbationDualTranslationSum
            helperForTheorem_6_30_22_counterexampleDualParameter :=
        hEq
      _ = (fun _ : Fin 1 => (1 : ℝ)) :=
        helperForTheorem_6_30_22_counterexampleDualParameter_translationSum
  have hZeroEqOne : (0 : ℝ) = 1 := by
    -- Evaluating at the unique coordinate reduces the vector contradiction to `0 = 1`.
    simpa using congrArg (fun z : Fin 1 → ℝ => z 0) hZeroVecEqOneVec
  linarith

/-- Helper for Theorem 6.30.22: the feasible zero witness and the infeasible counterexample
witness are genuinely different dual parameters. -/
lemma helperForTheorem_6_30_22_goodAndBadWitnesses_areDistinct :
    helperForTheorem_6_30_22_zeroDualParameter ≠
      helperForTheorem_6_30_22_counterexampleDualParameter := by
  -- Route correction: rather than separating the witnesses via objective values, compare their
  -- translation sums directly. The zero witness has sum `0`, while the bad witness has sum `1`.
  intro hEq
  have hTranslationEq :
      enlargedPerturbationDualTranslationSum
          helperForTheorem_6_30_22_zeroDualParameter =
        enlargedPerturbationDualTranslationSum
          helperForTheorem_6_30_22_counterexampleDualParameter := by
    -- Applying the translation-sum map to the assumed witness equality preserves equality.
    exact congrArg enlargedPerturbationDualTranslationSum hEq
  exact helperForTheorem_6_30_22_goodAndBadWitnesses_haveDifferentTranslationSums hTranslationEq

/-- Helper for Theorem 6.30.22: the surviving terminal-value witness and the pointwise
counterexample witness are distinct. This shows the valid `sSup` formula and the broken
infeasible branch live on different dual parameters. -/
lemma helperForTheorem_6_30_22_counterexampleHasDistinctGoodAndBadWitnesses :
    ∃ wGood wBad : EnlargedPerturbationDualParameter 1 1,
      enlargedPerturbationDualFeasible (0 : Fin 1 → ℝ) wGood ∧
      enlargedPerturbationDualObjective
          (m := 1) (n := 1)
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ : Fin 1 => fun _ : Fin 1 → ℝ => (0 : EReal))
          wGood = (⊤ : EReal) ∧
      ¬ enlargedPerturbationDualFeasible (0 : Fin 1 → ℝ) wBad ∧
      adjointOfEnlargedPerturbationProgram
          (fun _ : Fin 1 → ℝ => (⊤ : EReal))
          (fun _ _ => (0 : EReal))
          (0 : Fin 1 → ℝ)
          wBad = (⊤ : EReal) ∧
      wGood ≠ wBad := by
  -- Use the feasible zero witness for the terminal value and the bad witness for the broken
  -- infeasible branch, then record that these witnesses do not coincide.
  refine ⟨helperForTheorem_6_30_22_zeroDualParameter,
    helperForTheorem_6_30_22_counterexampleDualParameter, ?_⟩
  constructor
  · -- The zero witness is feasible at `x* = 0`.
    exact helperForTheorem_6_30_22_zeroDualParameter_feasible
  constructor
  · -- The same feasible witness realizes the terminal dual value `⊤`.
    exact helperForTheorem_6_30_22_zeroDualParameter_dualObjective_eq_top
  constructor
  · -- The counterexample witness violates the translation-balance condition.
    exact helperForTheorem_6_30_22_counterexampleDualParameter_not_feasible
  constructor
  · -- Its adjoint nevertheless remains `⊤`.
    exact helperForTheorem_6_30_22_counterexampleDualParameter_adjoint_eq_top
  · -- The two witnesses differ on their translated dual coordinate.
    exact helperForTheorem_6_30_22_goodAndBadWitnesses_areDistinct

-- Proof sketch: unfold the adjoint infimum defining `G*(x*, w*)`, translate variables by
-- `x₀` and the `xᵢ`, and separate the infimum into one term for `f₀` and one term for each
-- scaled constraint function `uᵢ* fᵢ`. Minimizing over the perturbation variables forces the
-- conditions `u* ≥ 0` and `x₀* + ⋯ + x_m* = x*`; under those conditions the remaining infimum is
-- the negative sum of the corresponding Fenchel conjugates. Evaluating at `x* = 0` yields the
-- stated dual maximization program.
/-- Helper for Theorem 6.30.22: if one increases a single perturbation coordinate while keeping
the translations fixed, the adjoint integrand changes only by the corresponding linear multiplier
term `t * uᵢ*`. -/
lemma helperForTheorem_6_30_22_negativeMultiplierRayWitnessValue
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) (wStar : EnlargedPerturbationDualParameter m n)
    (w0 : EnlargedPerturbationParameter m n) (x : Fin n → ℝ)
    (hxFeas : x ∈ enlargedPerturbationProgramFeasibleSet f w0)
    (i0 : Fin m) (t : ℝ) (ht : 0 ≤ t) :
    let w : EnlargedPerturbationParameter m n :=
      { u := w0.u + (Pi.single i0 t : Fin m → ℝ)
        x0 := w0.x0
        xShift := w0.xShift }
    enlargedPerturbationProgramBifunction f0 f w x - (((x ⬝ᵥ xStar : ℝ) : EReal)) +
        (((enlargedPerturbationDualPairing w wStar : ℝ) : EReal)) =
      (enlargedPerturbationProgramBifunction f0 f w0 x - (((x ⬝ᵥ xStar : ℝ) : EReal)) +
        (((enlargedPerturbationDualPairing w0 wStar : ℝ) : EReal))) +
        (((t * wStar.uStar i0 : ℝ) : EReal)) := by
  -- Keep the translations fixed and only enlarge one scalar perturbation coordinate.
  dsimp
  have hfeas :
      x ∈ enlargedPerturbationProgramFeasibleSet f
        { u := w0.u + (Pi.single i0 t : Fin m → ℝ)
          x0 := w0.x0
          xShift := w0.xShift } := by
    -- Increasing one perturbation coordinate preserves feasibility of the same primal point.
    intro j
    by_cases hj : j = i0
    · have hbase :
          f j (x - w0.xShift j) ≤ (((w0.u j : ℝ) : EReal)) := hxFeas j
      have hincReal : w0.u j ≤ w0.u j + t := by
        linarith
      have hincE :
          (((w0.u j : ℝ) : EReal)) ≤ (((w0.u j + t : ℝ) : EReal)) := by
        exact_mod_cast hincReal
      have hgoal :
          f j (x - w0.xShift j) ≤ (((w0.u j + t : ℝ) : EReal)) :=
        le_trans hbase hincE
      simpa [hj] using hgoal
    · simpa [Pi.single_eq_of_ne hj] using (hxFeas j)
  have hpair :
      enlargedPerturbationDualPairing
          { u := w0.u + (Pi.single i0 t : Fin m → ℝ)
            x0 := w0.x0
            xShift := w0.xShift } wStar =
        enlargedPerturbationDualPairing w0 wStar + t * wStar.uStar i0 := by
    -- Only the `u`-pairing changes, and it changes by the one-dimensional increment.
    unfold enlargedPerturbationDualPairing
    rw [add_dotProduct, single_dotProduct]
    ring
  -- Evaluate the bifunction at the preserved feasible point and simplify the affine increment.
  rw [enlargedPerturbationProgramBifunction, enlargedPerturbationProgramBifunction]
  have hIndicatorZero :
      indicatorFunction
          (enlargedPerturbationProgramFeasibleSet f
            { u := w0.u + (Pi.single i0 t : Fin m → ℝ)
              x0 := w0.x0
              xShift := w0.xShift }) x = (0 : EReal) := by
    simp [indicatorFunction, hfeas]
  have hIndicatorZero0 :
      indicatorFunction (enlargedPerturbationProgramFeasibleSet f w0) x = (0 : EReal) := by
    simp [indicatorFunction, hxFeas]
  rw [hIndicatorZero, hIndicatorZero0, hpair]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 6.30.22: if one multiplier coordinate is negative, then the enlarged
adjoint value is `-∞`, obtained by sending the corresponding perturbation coordinate to `+∞`
along a feasible ray while keeping all translations fixed. -/
lemma helperForTheorem_6_30_22_adjoint_eq_bot_of_exists_negativeMultiplier
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom : ∀ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) = Set.univ)
    (xStar : Fin n → ℝ) (wStar : EnlargedPerturbationDualParameter m n)
    (hneg : ∃ i0 : Fin m, wStar.uStar i0 < 0) :
    adjointOfEnlargedPerturbationProgram f0 f xStar wStar = (⊥ : EReal) := by
  -- Show the ranged infimum lies below every real number by following a feasible ray.
  rw [adjointOfEnlargedPerturbationProgram, EReal.eq_bot_iff_forall_lt]
  intro y
  rcases hneg with ⟨i0, hi0neg⟩
  have hx0_dom_nonempty :
      Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0) := by
    -- Properness gives a nonempty epigraph, hence a nonempty effective domain.
    exact (nonempty_epigraph_iff_nonempty_effectiveDomain
      (S := (Set.univ : Set (Fin n → ℝ))) (f := f0)).mp hf0.2.1
  rcases hx0_dom_nonempty with ⟨x0, hx0_dom⟩
  have hx0_lt_top : f0 x0 < (⊤ : EReal) := by
    simpa [effectiveDomain_eq] using hx0_dom
  have hx0_ne_top : f0 x0 ≠ (⊤ : EReal) := (lt_top_iff_ne_top).1 hx0_lt_top
  let w0 : EnlargedPerturbationParameter m n :=
    { u := fun i => (f i 0).toReal
      x0 := 0
      xShift := fun _ => x0 }
  have hx0Feas : x0 ∈ enlargedPerturbationProgramFeasibleSet f w0 := by
    -- Choosing every translated constraint point to be `0` makes the feasibility test explicit.
    intro i
    have hzeroDom :
        (0 : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
      rw [hdom i]
      simp
    have hzero_lt_top : f i (0 : Fin n → ℝ) < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hzeroDom
    have hzero_ne_bot : f i (0 : Fin n → ℝ) ≠ (⊥ : EReal) := (hf i).2.2 0 (by simp)
    have hzero_eq :
        ((((f i (0 : Fin n → ℝ)).toReal : ℝ) : EReal)) = f i (0 : Fin n → ℝ) := by
      exact EReal.coe_toReal (x := f i (0 : Fin n → ℝ))
        ((lt_top_iff_ne_top).1 hzero_lt_top) hzero_ne_bot
    calc
      f i (x0 - w0.xShift i) = f i (0 : Fin n → ℝ) := by
        simp [w0]
      _ ≤ (((w0.u i : ℝ) : EReal)) := by
        simpa [w0] using le_of_eq hzero_eq.symm
  let base : ℝ :=
    (f0 x0).toReal - (x0 ⬝ᵥ xStar : ℝ) + enlargedPerturbationDualPairing w0 wStar
  let t : ℝ := |((base - y) / (-wStar.uStar i0))| + 1
  have hden : 0 < -wStar.uStar i0 := by
    linarith
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hratio :
      ((base - y) / (-wStar.uStar i0)) < t := by
    -- The chosen scalar `t` strictly dominates the relevant quotient.
    dsimp [t]
    refine lt_of_le_of_lt (le_abs_self ((base - y) / (-wStar.uStar i0))) ?_
    linarith [abs_nonneg ((base - y) / (-wStar.uStar i0))]
  have hmul : (base - y) < t * (-wStar.uStar i0) := by
    exact (div_lt_iff₀ hden).mp hratio
  have hreal : base + t * wStar.uStar i0 < y := by
    linarith
  have hcoex0 : ((((f0 x0).toReal : ℝ) : EReal)) = f0 x0 := by
    exact EReal.coe_toReal (x := f0 x0) hx0_ne_top (hf0.2.2 x0 (by simp))
  let wRay : EnlargedPerturbationParameter m n :=
    { u := w0.u + (Pi.single i0 t : Fin m → ℝ)
      x0 := w0.x0
      xShift := w0.xShift }
  have hwitnessEval :
      enlargedPerturbationProgramBifunction f0 f wRay x0 -
          (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing wRay wStar : ℝ) : EReal)) =
        (enlargedPerturbationProgramBifunction f0 f w0 x0 -
          (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing w0 wStar : ℝ) : EReal))) +
          (((t * wStar.uStar i0 : ℝ) : EReal)) := by
    -- The previously established ray computation applies to the explicit feasible base point.
    simpa [w0, wRay] using
      helperForTheorem_6_30_22_negativeMultiplierRayWitnessValue
        (f0 := f0) (f := f) (xStar := xStar) (wStar := wStar)
        (w0 := w0) (x := x0) (hxFeas := hx0Feas) (i0 := i0) (t := t) ht
  have hwitnessLe :
      sInf
          (Set.range fun p : EnlargedPerturbationParameter m n × (Fin n → ℝ) =>
            enlargedPerturbationProgramBifunction f0 f p.1 p.2 -
              (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
              (((enlargedPerturbationDualPairing p.1 wStar : ℝ) : EReal))) ≤
        (enlargedPerturbationProgramBifunction f0 f w0 x0 -
          (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing w0 wStar : ℝ) : EReal))) +
          (((t * wStar.uStar i0 : ℝ) : EReal)) := by
    -- The infimum is bounded above by the value at the chosen ray witness.
    have hLePair :
        sInf
            (Set.range fun p : EnlargedPerturbationParameter m n × (Fin n → ℝ) =>
              enlargedPerturbationProgramBifunction f0 f p.1 p.2 -
                (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
                (((enlargedPerturbationDualPairing p.1 wStar : ℝ) : EReal))) ≤
          enlargedPerturbationProgramBifunction f0 f wRay x0 -
            (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((enlargedPerturbationDualPairing wRay wStar : ℝ) : EReal)) := by
      exact sInf_le ⟨(wRay, x0), rfl⟩
    exact hLePair.trans (le_of_eq hwitnessEval)
  have hbaseEval :
      enlargedPerturbationProgramBifunction f0 f w0 x0 -
          (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing w0 wStar : ℝ) : EReal)) =
        (((base : ℝ) : EReal)) := by
    -- At the explicit feasible base point, the bifunction reduces to the finite objective value.
    have hIndicatorZero0 :
        indicatorFunction (enlargedPerturbationProgramFeasibleSet f w0) x0 = (0 : EReal) := by
      simp [indicatorFunction, hx0Feas]
    rw [enlargedPerturbationProgramBifunction, hIndicatorZero0]
    simp [base, w0, hcoex0, sub_eq_add_neg, add_assoc]
  have htargetEq :
      (enlargedPerturbationProgramBifunction f0 f w0 x0 -
          (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing w0 wStar : ℝ) : EReal))) +
          (((t * wStar.uStar i0 : ℝ) : EReal)) =
        (((base + t * wStar.uStar i0 : ℝ) : EReal)) := by
    -- Rewrite the finite base value as a real coercion and combine the real terms.
    rw [hbaseEval]
    simp [EReal.coe_add]
  have hltTarget :
      (((base + t * wStar.uStar i0 : ℝ) : EReal)) < ((y : ℝ) : EReal) := by
    exact_mod_cast hreal
  have hltWitness :
      (enlargedPerturbationProgramBifunction f0 f w0 x0 -
          (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing w0 wStar : ℝ) : EReal))) +
          (((t * wStar.uStar i0 : ℝ) : EReal)) <
        ((y : ℝ) : EReal) := by
    rw [htargetEq]
    exact hltTarget
  exact lt_of_le_of_lt hwitnessLe hltWitness


end Section30
end Chap06
