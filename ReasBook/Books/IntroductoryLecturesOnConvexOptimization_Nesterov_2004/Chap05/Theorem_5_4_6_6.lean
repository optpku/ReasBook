/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u v w

open Set Topology

/- Theorem 5.4.6.6 lies in the subsection's self-concordant-barrier / recession-direction /
composition domain.

Sampled owner declarations:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for a
  `μ`-self-concordant barrier on an open convex domain;
* `IsSelfConcordantOn` from `Definition_5_1_1`, the chapter pattern for passing from a
  quantitative owner with an auxiliary constant to the source-facing existential owner when that
  constant is not part of the public statement;
* `compositionPotentialSigmaTwo` from `Theorem_5_4_6_5`, the source-facing owner for `σ₂`;
* `compositionSecondLiftedDirectionDerivative` from `Definition_5_4_6_7`, the source-facing owner
  for the lifted derivative direction `l' = (D²ξ(x)[d, d], 0)`;
* `IsSelfConcordantBarrierOnWith.inner_gradient_nonpos_of_recession_direction` from
  `Corollary_5_3_2`, the canonical barrier-owner recession-direction inequality;
* mathlib `Convex.add_smul_mem_interior`, the convex-interior bridge that transfers a recession
  direction of `Q₂` to one of `interior Q₂`.

Best owner abstraction:
* `∃ μ : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ`.

Source/core/bridge triage:
* source-facing: the nonnegativity conclusion for `σ₂` under the recession-direction hypothesis on
  `-l'`;
* core/canonical: the quantitative barrier owner `IsSelfConcordantBarrierOnWith` on `Φ` over
  `interior Q₂`;
* bridge/view: the lifted product direction `compositionSecondLiftedDirectionDerivative ξ x d`
  together with the internal `WithLp 2 (E₂ × E₃)` pullback used to apply the ambient pairing
  theorem.

Primitive data:
* `Φ`, `ξ`, `x`, `d`, `z`, the set `Q₂`, and the recession-direction hypothesis on `-l'`;
* the convexity of `Q₂`;
* the source-facing existence of some barrier parameter for `Φ` on `interior Q₂`.

Derived API:
* the lifted second derivative `l' = (D²ξ(x)[d, d], 0)` from `Definition_5_4_6_7`;
* the internal pullback barrier `w ↦ Φ w.ofLp` on the canonical `L²` product owner;
* the recession transfer from `Q₂` to `interior Q₂`;
* the nonpositivity of the ambient gradient pairing with the recession direction `-l'`.

The local public API should therefore stay on the source-facing existence of a barrier owner for
`Φ` on `interior Q₂`; the numerical barrier parameter is auxiliary proof data, the canonical `L²`
pullback is only an internal bridge, and the public statement must make the convexity of `Q₂`
explicit because that hypothesis is exactly what moves the recession-direction assumption from
`Q₂` to the barrier domain `interior Q₂`. -/

section SigmaTwoNonneg

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

noncomputable local instance instLocalChap05_Theorem_5_4_6_61 : SeminormedAddCommGroup (E₂ × E₃) :=
  WithLp.seminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_62 : NormedAddCommGroup (E₂ × E₃) :=
  WithLp.normedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_63 : NormedSpace ℝ (E₂ × E₃) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_6_61 : InnerProductSpace ℝ (E₂ × E₃) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E₂ E₃ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instLocalChap05_Theorem_5_4_6_64 : CompleteSpace (E₂ × E₃) := inferInstance

local notation "Z" => WithLp 2 (E₂ × E₃)
local notation "ofZ" => (WithLp.ofLp : Z → E₂ × E₃)

-- Proof sketch: pull the barrier back along `WithLp.ofLp` to the canonical `L²` product owner,
-- rewrite `σ₂` as the ambient gradient pairing of that pullback barrier with the lifted direction
-- `WithLp.toLp 2 l'`, transfer the recession-direction hypothesis on `-l'` from the convex set
-- `Q₂` to the barrier domain `interior Q₂`, and then apply
-- `IsSelfConcordantBarrierOnWith.inner_gradient_nonpos_of_recession_direction`.
/-- Theorem 5.4.6.6: if the negative lifted derivative direction `-l'` is a recession direction
of `Q₂`, and if `Φ` is some self-concordant barrier on `interior Q₂`, then the term `σ₂` is
nonnegative. -/
theorem compositionPotentialSigmaTwo_nonneg_of_neg_liftedDirectionDerivative_recession
    {Q₂ : Set (E₂ × E₃)} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hQ₂_convex : Convex ℝ Q₂)
    (hΦ : ∃ μ : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hyz : (ξ x, z) ∈ interior Q₂)
    (hrecession :
      ∀ ⦃p : E₂ × E₃⦄, p ∈ Q₂ → ∀ τ : ℝ, 0 ≤ τ →
        p + τ • (-compositionSecondLiftedDirectionDerivative ξ x d) ∈ Q₂) :
    0 ≤ compositionPotentialSigmaTwo Φ ξ x z d := by
  rcases hΦ with ⟨μ, hΦμ⟩
  let l' : E₂ × E₃ := compositionSecondLiftedDirectionDerivative ξ x d
  let g : Z →ᴬ[ℝ] E₂ × E₃ :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap).toContinuousAffineMap
  let hΦZ : IsSelfConcordantBarrierOnWith (ofZ ⁻¹' interior Q₂) μ (Φ ∘ ofZ) := by
    simpa [g, Function.comp] using
      IsSelfConcordantBarrierOnWith.comp_continuousAffineMap hΦμ g
  have hyzZ : WithLp.toLp 2 (ξ x, z) ∈ ofZ ⁻¹' interior Q₂ := by
    simpa using hyz
  have hrecessionZ :
      ∀ ⦃w : Z⦄, w ∈ ofZ ⁻¹' interior Q₂ →
        ∀ τ : ℝ, 0 ≤ τ → w + τ • WithLp.toLp 2 (-l') ∈ ofZ ⁻¹' interior Q₂ := by
    intro w hw τ hτ
    let p : E₂ × E₃ := w.ofLp
    let d' : E₂ × E₃ := -l'
    let q : E₂ × E₃ := p + (2 * τ) • d'
    have hp : p ∈ interior Q₂ := by
      simpa [p] using hw
    have hq : q ∈ Q₂ := by
      simpa [p, d', q, l'] using hrecession (interior_subset hp) (2 * τ) (by positivity)
    have hp' : q + (-(2 * τ)) • d' ∈ interior Q₂ := by
      convert hp using 1
      simp [p, d', q, add_assoc]
    have hmid :=
      hQ₂_convex.add_smul_mem_interior hq hp' (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioc 0 1)
    have hsum : (2 * τ) • d' + -τ • d' = τ • d' := by
      rw [← add_smul]
      have hcoeff : (2 * τ : ℝ) + -τ = τ := by ring
      rw [hcoeff]
    have hinterior : p + τ • d' ∈ interior Q₂ := by
      convert hmid using 1
      rw [show q = p + (2 * τ) • d' by rfl, smul_smul]
      have hcoeff : (1 / 2 : ℝ) * (-(2 * τ)) = -τ := by ring
      rw [hcoeff]
      simpa [p, d', q, add_assoc] using congrArg (fun v : E₂ × E₃ ↦ p + v) hsum.symm
    simpa [p, d'] using hinterior
  let hstdZ : IsStandardSelfConcordantOn (ofZ ⁻¹' interior Q₂) (Φ ∘ ofZ) :=
    hΦZ.toIsStandardSelfConcordantOn
  have hdiffZ : DifferentiableAt ℝ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z)) := by
    simpa using
      (hstdZ.contDiffOn.contDiffAt (hstdZ.isOpen_domain.mem_nhds hyzZ)).differentiableAt
        (by norm_num)
  have hsigma :
      compositionPotentialSigmaTwo Φ ξ x z d =
        inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z))) (WithLp.toLp 2 l') := by
    have hpair :
        inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) (ξ x))
            (vectorSecondDirectionalDerivative ξ x d) +
          inner ℝ (∇ (fun z' : E₃ ↦ Φ (ξ x, z')) z) (0 : E₃) =
            inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z))) (WithLp.toLp 2 l') :=
      by
        simpa [l', compositionSecondLiftedDirectionDerivative] using
          (@sum_partialGradient_pairings_eq_inner_gradient_pair
            E₂ E₃ _ _ _ _ _ _
            Φ (ξ x) (vectorSecondDirectionalDerivative ξ x d) z (0 : E₃) hdiffZ)
    simpa [compositionPotentialSigmaTwo_def] using hpair
  have hnonpos :
      inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z))) (WithLp.toLp 2 (-l')) ≤ 0 :=
    hΦZ.inner_gradient_nonpos_of_recession_direction hrecessionZ hyzZ
  have hnonneg :
      0 ≤ inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z))) (WithLp.toLp 2 l') := by
    have hneg :
        -(inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (ξ x, z))) (WithLp.toLp 2 l')) ≤ 0 := by
      simpa using hnonpos
    linarith
  simpa [hsigma] using hnonneg

end SigmaTwoNonneg

end
