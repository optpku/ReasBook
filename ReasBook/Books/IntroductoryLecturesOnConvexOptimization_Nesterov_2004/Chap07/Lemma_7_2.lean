/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise SupportFunction

universe u v

/-
Lemma 7.2 lies in the chapter's support-function / dual-norm comparison domain.

Sampled owner-style declarations:
- Chapter 3 `ξ[Q]` and `supportFunction_apply`
- Chapter 3 `Seminorm.dualNorm` and `Seminorm.dualNorm_apply`
- mathlib `Seminorm.closedBall`
- mathlib `Seminorm.closedBall_zero_eq`

Best owner abstraction:
- source-facing: the support-function bound for `x ↦ (ξ[Q₂] (A x)).toReal`
- core/canonical: `ξ[Q₂]`, `Seminorm.dualNorm`, and `Seminorm.closedBall`
- bridge/view: the real-valued `toReal` surface of `ξ[Q₂]`

Primitive data:
- a real-linear map `A : X →ₗ[ℝ] F`
- a set `Q₂ : Set F`
- a seminorm `p : Seminorm ℝ F` with `[Seminorm.IsNorm p]`
- radii `γ₀`, `γ₁`

Derived API:
- the dual norm `p.dualNorm`
- the primal balls `p.closedBall 0 γ`
- the pointwise real-valued support function `x ↦ (ξ[Q₂] (A x)).toReal`

Source/core/bridge triage:
- source-facing: the sandwich estimate for the support function of `Aᵀ Q₂`
- core/canonical: the Chapter 3 support-function and dual-norm owners
- bridge/view: precomposition with `A` and the `toReal` passage for the support function

This refinement deletes the duplicate local owners `VectorNorm`, `supportFunction`,
`supportFunctionAlongLinearMap`, and `pulledDualNorm`. The public statement now uses the chapter
owners directly and only keeps the real-valued `toReal` bridge because the textbook inequality is
real-valued.
-/

section

variable {X : Type v} [AddCommGroup X] [Module ℝ X]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [FiniteDimensional ℝ F]

/-- Helper for Lemma 7.2: support functions are monotone with respect to set inclusion. -/
-- Proof sketch: unfold both support functions to their defining `EReal` suprema and enlarge the
-- image set along the given inclusion.
lemma supportFunction_mono_of_subset {Q1 Q2 : Set F} (hQ : Q1 ⊆ Q2) (u : F) :
    ξ[Q1] u ≤ ξ[Q2] u := by
  rw [supportFunction_apply, supportFunction_apply]
  exact sSup_le_sSup (Set.image_mono hQ)

/-- Helper for Lemma 7.2: a support function over a nonempty set never takes the value `⊥`. -/
-- Proof sketch: any witness `y ∈ Q` contributes one concrete real value to the defining supremum,
-- so the supremum cannot drop below all real numbers.
lemma supportFunction_ne_bot_of_nonempty {Q : Set F} (hQ : Q.Nonempty) (u : F) :
    ξ[Q] u ≠ ⊥ := by
  rw [supportFunction_apply]
  rcases hQ with ⟨y, hy⟩
  intro hbot
  have hy_le :
      ((inner ℝ y u : ℝ) : EReal) ≤
        sSup ((fun x : F ↦ ((inner ℝ x u : ℝ) : EReal)) '' Q) := by
    exact le_sSup ⟨y, hy, rfl⟩
  have : ((inner ℝ y u : ℝ) : EReal) ≤ (⊥ : EReal) := by
    simpa [hbot] using hy_le
  exact (not_le_of_gt (EReal.bot_lt_coe _)) this

/-- Helper for Lemma 7.2: scaling a set scales the support-function argument in the dual slot. -/
-- Proof sketch: rewrite membership in the pointwise-scaled set, then use bilinearity of the real
-- inner product to identify the two image sets defining the support functions.
lemma supportFunction_smul_set_eq (γ : ℝ) (Q : Set F) (u : F) :
    ξ[γ • Q] u = ξ[Q] (γ • u) := by
  rw [supportFunction_apply, supportFunction_apply]
  have himage :
      (fun x : F ↦ ((inner ℝ x u : ℝ) : EReal)) '' (γ • Q) =
        (fun x : F ↦ ((inner ℝ x (γ • u) : ℝ) : EReal)) '' Q := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp [inner_smul_left, inner_smul_right, mul_comm]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨γ • y, Set.smul_mem_smul_set hy, ?_⟩
      simp [inner_smul_left, inner_smul_right, mul_comm]
  rw [himage]

/-- Helper for Lemma 7.2: the inner-product image of the closed primal unit ball is bounded
above, so `le_csSup` and `csSup_le` can be used on the Chapter 2 dual-norm surface. -/
-- Proof sketch: a finite-dimensional comparison between the ambient norm and `p` bounds the
-- closed `p`-unit ball inside an ambient Euclidean ball, and Cauchy--Schwarz then bounds every
-- pairing `⟪u, y⟫`.
private theorem dualNormBddAboveInnerImageClosedBall
    (p : Seminorm ℝ F) [Seminorm.IsNorm p] (u : F) :
    BddAbove ((fun y : F ↦ inner ℝ u y) '' p.closedBall 0 1) := by
  obtain ⟨C, _, hnorm_le⟩ := p.exists_norm_le_mul
  refine ⟨‖u‖ * C, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hy_norm : ‖y‖ ≤ C := by
    have hpy : p y ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hy
    calc
      ‖y‖ ≤ C * p y := hnorm_le y
      _ ≤ C * 1 := by
        gcongr
      _ = C := by
        ring
  calc
    inner ℝ u y ≤ ‖u‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖u‖ * C := by
      gcongr

/-- Helper for Lemma 7.2: the radius-`γ` closed `p`-ball is the pointwise `γ`-dilation of the
unit closed `p`-ball when `γ` is nonnegative. -/
-- Proof sketch: the zero-radius case is immediate. For `γ > 0`, reuse mathlib's canonical
-- closed-ball scaling theorem and then simplify `‖γ‖` to `γ`.
lemma closedBall_zero_eq_smul_closedBall_zero_one_of_nonneg
    (p : Seminorm ℝ F) [Seminorm.IsNorm p] {γ : ℝ} (hγ : 0 ≤ γ) :
    p.closedBall 0 γ = γ • p.closedBall 0 1 := by
  by_cases hγ_zero : γ = 0
  · subst hγ_zero
    ext u
    constructor
    · intro hu
      have hu_zero : u = 0 := by
        exact Seminorm.IsNorm.eq_zero_of_map_eq_zero <|
          le_antisymm (by simpa [Seminorm.mem_closedBall_zero] using hu) (apply_nonneg p u)
      exact Set.mem_smul_set.2
        ⟨0, by simpa [Seminorm.mem_closedBall_zero], by simpa [hu_zero]⟩
    · intro hu
      rcases Set.mem_smul_set.mp hu with ⟨v, hv, rfl⟩
      simpa [Seminorm.mem_closedBall_zero]
  · have hγ_pos : 0 < ‖γ‖ := by
      exact norm_pos_iff.mpr hγ_zero
    calc
      p.closedBall 0 γ = p.closedBall 0 (‖γ‖ * 1) := by
        simp [Real.norm_of_nonneg hγ]
      _ = γ • p.closedBall 0 1 := by
        symm
        simpa [Real.norm_of_nonneg hγ] using
          (Seminorm.smul_closedBall_zero (p := p) (k := γ) (r := 1) hγ_pos)

/-- Helper for Lemma 7.2: the Chapter 2 dual norm is nonnegative because the closed primal unit
ball contains the zero witness. -/
-- Proof sketch: rewrite the dual norm as a supremum over the closed primal unit ball and test it
-- on `0`.
private theorem dualNorm_nonneg
    (p : Seminorm ℝ F) [Seminorm.IsNorm p] (u : F) :
    0 ≤ p.dualNorm u := by
  rw [Seminorm.dualNorm_apply, ← p.closedBall_zero_eq]
  exact le_csSup (dualNormBddAboveInnerImageClosedBall p u)
    ⟨0, by simp [Seminorm.mem_closedBall_zero]⟩

/-- Helper for Lemma 7.2: each point of the closed primal unit ball gives a pairing bounded above
by the Chapter 2 dual norm. -/
-- Proof sketch: commute the real inner product and apply `Seminorm.inner_le_dualNorm_mul`, then
-- use the unit-ball bound `p y ≤ 1`.
private theorem inner_le_dualNorm_of_mem_closedBall_zero_one
    (p : Seminorm ℝ F) [Seminorm.IsNorm p] (u y : F) (hy : y ∈ p.closedBall 0 1) :
    inner ℝ y u ≤ p.dualNorm u := by
  calc
    inner ℝ y u = inner ℝ u y := by rw [real_inner_comm]
    _ ≤ p.dualNorm u * p y := Seminorm.inner_le_dualNorm_mul p y u
    _ ≤ p.dualNorm u * 1 := by
      refine mul_le_mul_of_nonneg_left ?_ (dualNorm_nonneg p u)
      simpa [Seminorm.mem_closedBall_zero] using hy
    _ = p.dualNorm u := by ring

/-- Helper for Lemma 7.2: the support function of the closed primal unit ball is bounded above by
the `EReal` coercion of the Chapter 2 dual norm. -/
-- Proof sketch: each unit-ball witness is bounded by the dual norm through
-- `Seminorm.inner_le_dualNorm_mul`, so the support-function supremum is bounded by the same real.
private theorem supportFunction_closedBall_zero_one_le_coe_dualNorm
    (p : Seminorm ℝ F) [Seminorm.IsNorm p] (u : F) :
    ξ[p.closedBall 0 1] u ≤ ((p.dualNorm u : ℝ) : EReal) := by
  rw [supportFunction_apply]
  refine sSup_le ?_
  rintro _ ⟨y, hy, rfl⟩
  simpa using (EReal.coe_le_coe_iff.mpr
    (inner_le_dualNorm_of_mem_closedBall_zero_one p u y hy))

/-- Helper for Lemma 7.2: the Chapter 2 dual norm is bounded above by the real-valued support
function of the closed primal unit ball. -/
-- Proof sketch: rewrite the dual norm as a supremum over the same unit-ball witnesses and use
-- each witness's contribution to the support-function supremum before taking `toReal`.
private theorem dualNorm_le_supportFunction_closedBall_zero_one_toReal
    (p : Seminorm ℝ F) [Seminorm.IsNorm p] (u : F) :
    p.dualNorm u ≤ (ξ[p.closedBall 0 1] u).toReal := by
  rw [Seminorm.dualNorm_apply, ← p.closedBall_zero_eq]
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    exact ⟨0, by simpa [Seminorm.mem_closedBall_zero], by simp⟩
  · rintro z ⟨y, hy, rfl⟩
    have hy_support : (((inner ℝ u y : ℝ) : EReal)) ≤ ξ[p.closedBall 0 1] u := by
      rw [supportFunction_apply]
      exact le_sSup ⟨y, hy, by simpa [real_inner_comm]⟩
    have hsupport_ne_top : ξ[p.closedBall 0 1] u ≠ ⊤ := by
      exact ne_top_of_le_ne_top (EReal.coe_ne_top _)
        (supportFunction_closedBall_zero_one_le_coe_dualNorm p u)
    have hy_toReal :
        ((((inner ℝ u y : ℝ) : EReal)).toReal) ≤ (ξ[p.closedBall 0 1] u).toReal := by
      exact EReal.toReal_le_toReal hy_support (EReal.coe_ne_bot _) hsupport_ne_top
    simpa using hy_toReal

/-- Helper for Lemma 7.2: the support function of the closed `p`-unit ball agrees with the dual
norm after passing to the real-valued `toReal` surface. -/
-- Proof sketch: combine the upper support-function estimate and the reverse dual-norm estimate,
-- both already reduced to small canonical helper lemmas.
lemma supportFunction_closedBall_zero_one_toReal_eq_dualNorm
    (p : Seminorm ℝ F) [Seminorm.IsNorm p] (u : F) :
    (ξ[p.closedBall 0 1] u).toReal = p.dualNorm u := by
  have hunit_nonempty : (p.closedBall 0 1 : Set F).Nonempty := by
    exact ⟨0, by simpa [Seminorm.mem_closedBall_zero]⟩
  have hsupport_ne_bot : ξ[p.closedBall 0 1] u ≠ ⊥ :=
    supportFunction_ne_bot_of_nonempty hunit_nonempty u
  have hsupport_toReal_le : (ξ[p.closedBall 0 1] u).toReal ≤ p.dualNorm u := by
    simpa using EReal.toReal_le_toReal
      (supportFunction_closedBall_zero_one_le_coe_dualNorm p u) hsupport_ne_bot (EReal.coe_ne_top _)
  exact le_antisymm hsupport_toReal_le
    (dualNorm_le_supportFunction_closedBall_zero_one_toReal p u)

/-- Helper for Lemma 7.2: the support function of the closed `p`-unit ball is the `EReal`
coercion of the Chapter 2 dual norm. -/
-- Proof sketch: first identify the real-valued `toReal` image with the dual norm, then recover
-- the original `EReal` value by `EReal.coe_toReal` after proving the support value is finite.
lemma supportFunction_closedBall_zero_one_eq_coe_dualNorm
    (p : Seminorm ℝ F) [Seminorm.IsNorm p] (u : F) :
    ξ[p.closedBall 0 1] u = ((p.dualNorm u : ℝ) : EReal) := by
  have hunit_nonempty : (p.closedBall 0 1 : Set F).Nonempty := by
    exact ⟨0, by simpa [Seminorm.mem_closedBall_zero]⟩
  have hsupport_ne_bot : ξ[p.closedBall 0 1] u ≠ ⊥ :=
    supportFunction_ne_bot_of_nonempty hunit_nonempty u
  calc
    ξ[p.closedBall 0 1] u = (((ξ[p.closedBall 0 1] u).toReal : ℝ) : EReal) := by
      symm
      have hsupport_ne_top : ξ[p.closedBall 0 1] u ≠ ⊤ := by
        exact ne_top_of_le_ne_top (EReal.coe_ne_top _)
          (supportFunction_closedBall_zero_one_le_coe_dualNorm p u)
      exact EReal.coe_toReal hsupport_ne_top hsupport_ne_bot
    _ = ((p.dualNorm u : ℝ) : EReal) := by
      rw [supportFunction_closedBall_zero_one_toReal_eq_dualNorm]

/-- Helper for Lemma 7.2: the support function of a closed `p`-ball of radius `γ` is the `EReal`
coercion of `γ` times the dual norm. -/
-- Proof sketch: rewrite the radius-`γ` ball as a dilation of the unit ball, move that dilation to
-- the support-function argument, and then invoke positive homogeneity and the unit-ball formula.
lemma supportFunction_closedBall_eq_coe_mul_dualNorm
    (p : Seminorm ℝ F) [Seminorm.IsNorm p] {γ : ℝ} (hγ : 0 ≤ γ) (u : F) :
    ξ[p.closedBall 0 γ] u = ((γ * p.dualNorm u : ℝ) : EReal) := by
  have hunit_nonempty : (p.closedBall 0 1 : Set F).Nonempty := by
    exact ⟨0, by simpa [Seminorm.mem_closedBall_zero]⟩
  calc
    ξ[p.closedBall 0 γ] u = ξ[γ • p.closedBall 0 1] u := by
      rw [closedBall_zero_eq_smul_closedBall_zero_one_of_nonneg p hγ]
    _ = ξ[p.closedBall 0 1] (γ • u) := supportFunction_smul_set_eq γ (p.closedBall 0 1) u
    _ = (γ : EReal) * ξ[p.closedBall 0 1] u := by
      rw [supportFunction_nonneg_smul (p.closedBall 0 1) hunit_nonempty u γ hγ]
    _ = (γ : EReal) * ((p.dualNorm u : ℝ) : EReal) := by
      rw [supportFunction_closedBall_zero_one_eq_coe_dualNorm p u]
    _ = ((γ * p.dualNorm u : ℝ) : EReal) := by
      rw [← EReal.coe_mul]

/-
Proof sketch: compare `ξ[Q₂]` with the support functions of the inner and outer `p`-balls using
`p.closedBall 0 γ₀ ⊆ Q₂ ⊆ p.closedBall 0 γ₁`; then identify the support functions of those balls
with `γ₀` and `γ₁` times `p.dualNorm`. The only explicit radius sign assumption needed in the public
API is `0 ≤ γ₀`: since `0 ∈ p.closedBall 0 γ₀`, the inclusions force `0 ∈ p.closedBall 0 γ₁`, so
`0 ≤ γ₁` is derived internally from the canonical closed-ball owner. -/
/-- Lemma 7.2: if `Q₂` contains the `p`-ball of radius `γ₀` and is contained in the `p`-ball of
radius `γ₁`, then the real-valued support function of `Aᵀ Q₂ = ∂f(0)` is sandwiched between `γ₀`
and `γ₁` times the pulled-back dual norm `x ↦ ‖A x‖_*`. The pointwise sandwich only needs the
inner radius to be explicitly nonnegative; the outer-radius nonnegativity follows from the two ball
inclusions. The stronger positivity hypotheses needed for the ratio `γ₀ / γ₁` are kept separate in
`gammaRatio_pos_and_le_one`. -/
theorem supportFunction_toReal_comp_linearMap_dualNorm_bounds
    (A : X →ₗ[ℝ] F) (Q2 : Set F) (p : Seminorm ℝ F) [Seminorm.IsNorm p]
    (γ₀ γ₁ : ℝ) (hγ₀_nonneg : 0 ≤ γ₀)
    (hQ2_lower : p.closedBall 0 γ₀ ⊆ Q2)
    (hQ2_upper : Q2 ⊆ p.closedBall 0 γ₁)
    (x : X) :
    γ₀ * p.dualNorm (A x) ≤ (ξ[Q2] (A x)).toReal ∧
      (ξ[Q2] (A x)).toReal ≤ γ₁ * p.dualNorm (A x) := by
  -- Route correction: first prove the support-function sandwich in `EReal`, then convert both
  -- sides to real inequalities only after finiteness is established.
  have hzero_mem_lower : (0 : F) ∈ p.closedBall 0 γ₀ := by
    simpa [Seminorm.mem_closedBall_zero] using hγ₀_nonneg
  have hzero_mem_Q2 : (0 : F) ∈ Q2 := hQ2_lower hzero_mem_lower
  have hQ2_nonempty : Q2.Nonempty := ⟨0, hzero_mem_Q2⟩
  have hzero_mem_upper : (0 : F) ∈ p.closedBall 0 γ₁ := hQ2_upper hzero_mem_Q2
  have hγ₁_nonneg : 0 ≤ γ₁ := by
    simpa [Seminorm.mem_closedBall_zero] using hzero_mem_upper
  have hlower_ereal :
      (((γ₀ * p.dualNorm (A x) : ℝ) : EReal)) ≤ ξ[Q2] (A x) := by
    have hsubset : ξ[p.closedBall 0 γ₀] (A x) ≤ ξ[Q2] (A x) :=
      supportFunction_mono_of_subset hQ2_lower (A x)
    rw [supportFunction_closedBall_eq_coe_mul_dualNorm p hγ₀_nonneg (A x)] at hsubset
    exact hsubset
  have hupper_ereal :
      ξ[Q2] (A x) ≤ (((γ₁ * p.dualNorm (A x) : ℝ) : EReal)) := by
    calc
      ξ[Q2] (A x) ≤ ξ[p.closedBall 0 γ₁] (A x) :=
        supportFunction_mono_of_subset hQ2_upper (A x)
      _ = (((γ₁ * p.dualNorm (A x) : ℝ) : EReal)) := by
        rw [supportFunction_closedBall_eq_coe_mul_dualNorm p hγ₁_nonneg (A x)]
  have hsupport_ne_bot : ξ[Q2] (A x) ≠ ⊥ :=
    supportFunction_ne_bot_of_nonempty hQ2_nonempty (A x)
  have hsupport_ne_top : ξ[Q2] (A x) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hupper_ereal
  constructor
  · -- The lower `EReal` comparison becomes the lower real inequality once the support value is
    -- known to be finite from above.
    have hlower_real :
        (γ₀ * p.dualNorm (A x) : EReal).toReal ≤ (ξ[Q2] (A x)).toReal := by
      exact EReal.toReal_le_toReal hlower_ereal (EReal.coe_ne_bot _) hsupport_ne_top
    simpa using hlower_real
  · -- The upper `EReal` comparison uses nonemptiness to rule out `⊥` for the support value.
    have hupper_real :
        (ξ[Q2] (A x)).toReal ≤ (γ₁ * p.dualNorm (A x) : EReal).toReal := by
      exact EReal.toReal_le_toReal hupper_ereal hsupport_ne_bot (EReal.coe_ne_top _)
    simpa using hupper_real

-- Proof sketch: `0 < γ₀ ≤ γ₁` implies `0 < γ₁`, hence division by `γ₁` preserves order and gives
-- `0 < γ₀ / γ₁ ≤ 1`.
/-- The ratio `γ₀ / γ₁` is positive and at most `1`, which is the numerical content used for the
choice `α = γ₀ / γ₁` in the relative-scale condition. -/
theorem gammaRatio_pos_and_le_one {γ₀ γ₁ : ℝ}
    (hγ₀ : 0 < γ₀) (hγ₀γ₁ : γ₀ ≤ γ₁) :
    0 < γ₀ / γ₁ ∧ γ₀ / γ₁ ≤ 1 := by
  have hγ₁ : 0 < γ₁ := lt_of_lt_of_le hγ₀ hγ₀γ₁
  have hγ₁_ne : γ₁ ≠ 0 := hγ₁.ne'
  constructor
  · -- Positivity of the quotient is immediate from positivity of numerator and denominator.
    exact div_pos hγ₀ hγ₁
  · -- Rewrite division as multiplication by the nonnegative inverse of `γ₁`.
    calc
      γ₀ / γ₁ = γ₀ * γ₁⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ γ₁ * γ₁⁻¹ := by
        exact mul_le_mul_of_nonneg_right hγ₀γ₁ (inv_nonneg.mpr hγ₁.le)
      _ = 1 := by
        rw [mul_inv_cancel₀ hγ₁_ne]

end
