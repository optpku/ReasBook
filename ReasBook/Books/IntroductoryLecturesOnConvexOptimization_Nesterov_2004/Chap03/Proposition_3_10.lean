/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped SupportFunction

/- Proposition 3.10 lies in the chapter's support-function / positive-homogeneity domain.

Sampled owner-style declarations:
- `supportFunction` / `supportFunction_apply` in `Definition_3_9`
- `pointwiseSupremumOn` in `PointwiseSupremumOn`
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`

Best owner abstraction:
- source-facing: positive homogeneity of `ξ[Q]`
- core/canonical: `supportFunction`, built from `pointwiseSupremumOn`
- bridge/view: a real-scalar restatement obtained from the bundled nonnegative-scalar theorem below

Primitive data:
- a set `Q : Set E`
- a nonemptiness witness `hQ : Q.Nonempty`

Derived API:
- the `NNReal`-parameterized scaling theorem `supportFunction_smul`
- the real-scalar companion `supportFunction_nonneg_smul`

Because `supportFunction` is `EReal`-valued, the chapter owner `IsPositivelyHomogeneousOn`
cannot be applied to it directly. The minimal canonical surface is therefore the bundled
nonnegative-scalar theorem with parameter `τ : NNReal`, and the raw `τ : ℝ` plus `0 ≤ τ`
statement is kept only as a bridge.
-/

/-- Proposition 3.10: the support function of a nonempty set in a real inner-product space is
positively homogeneous with respect to every bundled nonnegative scalar. The textbook `ℝⁿ`
statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: rewrite `supportFunction Q (τ • x)` as the supremum of the image of `Q` under
-- `q ↦ ⟪τ • x, q⟫ = τ * ⟪x, q⟫`. If `τ = 0`, the support value at `0` is the supremum of the
-- constant-zero family over the nonempty set `Q`. If `τ > 0`, pull the positive scalar through
-- `sSup` using the standard order-theoretic rule for multiplication by a positive scalar.
theorem supportFunction_smul (Q : Set E) (hQ : Q.Nonempty) (x : E) (τ : NNReal) :
    ξ[Q] (τ • x) = (τ : EReal) * ξ[Q] x := by
  by_cases hτ : τ = 0
  · subst hτ
    rw [supportFunction_apply]
    simp [hQ]
  · have hτpos : 0 < (τ : ℝ) := by
      exact_mod_cast (show 0 < τ from pos_iff_ne_zero.mpr hτ)
    have hτE : (0 : EReal) < (τ : EReal) := by
      exact_mod_cast hτpos
    have hτE_top : (τ : EReal) ≠ ⊤ := EReal.coe_ne_top _
    rw [supportFunction_apply, supportFunction_apply]
    have himage :
        (fun g ↦ ↑(inner ℝ g (τ • x)) : E → EReal) '' Q =
          (fun z ↦ (τ : EReal) * z) '' ((fun g ↦ ↑(inner ℝ g x) : E → EReal) '' Q) := by
      ext y
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine ⟨((inner ℝ g x : ℝ) : EReal), ?_, ?_⟩
        · exact ⟨g, hg, rfl⟩
        · change (τ : EReal) * ((inner ℝ g x : ℝ) : EReal) = ((inner ℝ g (τ • x) : ℝ) : EReal)
          rw [NNReal.smul_def, inner_smul_right]
          rfl
      · rintro ⟨z, ⟨g, hg, rfl⟩, rfl⟩
        refine ⟨g, hg, ?_⟩
        change ((inner ℝ g (τ • x) : ℝ) : EReal) = (τ : EReal) * ((inner ℝ g x : ℝ) : EReal)
        rw [NNReal.smul_def, inner_smul_right]
        rfl
    rw [himage]
    refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact mul_le_mul_of_nonneg_left (le_sSup hz) hτE.le
    · intro w hw
      have hw' : w / (τ : EReal) < sSup ((fun g ↦ ↑(inner ℝ g x) : E → EReal) '' Q) := by
        rw [EReal.div_lt_iff hτE hτE_top, mul_comm]
        exact hw
      rcases lt_sSup_iff.mp hw' with ⟨z, hz, hzw⟩
      refine ⟨(τ : EReal) * z, ⟨z, hz, rfl⟩, ?_⟩
      rw [EReal.div_lt_iff hτE hτE_top] at hzw
      simpa [mul_comm] using hzw

/-- Real-scalar bridge for Proposition 3.10, derived from the bundled `NNReal` theorem
`supportFunction_smul`. -/
theorem supportFunction_nonneg_smul
    (Q : Set E) (hQ : Q.Nonempty) (x : E) (τ : ℝ) (hτ : 0 ≤ τ) :
    ξ[Q] (τ • x) = (τ : EReal) * ξ[Q] x := by
  simpa [NNReal.smul_def, Real.toNNReal_of_nonneg hτ] using
    supportFunction_smul Q hQ x (Real.toNNReal τ)

end
