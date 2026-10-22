/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_81

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SupportFunction
open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 7.17 lies in the chapter's support-function / subdifferential positivity domain.

Mandatory domain-style sampling before refinement:
- `supportFunction` with notation `ξ[Q]` in `Chap03/Definition_3_9`, the chapter owner for support
  functions of sets;
- `supportFunction_dom_eq_univ_of_nonempty_bounded` in `Chap03/Proposition_3_11`, the bounded-set
  finiteness theorem for that owner;
- `ConvexBody.supportFunctionReal` in `Chap07/Definition_7_24`, the convex-body `toReal` bridge
  showing that Chapter 7 treats real-valued support functions through the Chapter 3 owner;
- `StrictlyPositiveOn` in `Chap07/Definition_7_81`, the source-facing positivity predicate for
  real-valued functions.

Best owner abstraction:
- source-facing: Lemma 7.17 as a `StrictlyPositiveOn` statement for a centrally symmetric support
  function;
- core/canonical: the chapter support-function owner `ξ[S]`;
- bridge/view: the real-valued support-function surface `fun x ↦ (ξ[S] x).toReal`.

Primitive data:
- a set `S : Set E`;
- nonemptiness, boundedness, and central symmetry of `S`.

Derived API:
- the real-valued support function `fun x ↦ (ξ[S] x).toReal`, justified by
  `supportFunction_dom_eq_univ_of_nonempty_bounded`;
- the `StrictlyPositiveOn` conclusion on `Set.univ`.

The previous version stated the support function through a raw `sSup ((fun s ↦ ⟪s, x⟫) '' S)`
formula even though the chapter already owns this notion as `ξ[S]` and Chapter 7 already uses the
`toReal` bridge for real-valued support functions. This refinement keeps the source-facing
positivity theorem but moves it to the canonical owner surface, drops the redundant closedness
hypothesis from the public API, and replaces the over-concrete `EuclideanSpace ℝ (Fin n)` ambient
model by the standard real inner-product-space layer. The `.toReal` bridge is kept only under the
finite-value hypothesis supplied by nonemptiness together with boundedness.
-/

-- Proof sketch: let `f x = (ξ[S] x).toReal`. For `g ∈ ∂ f(x)`, use the subgradient inequality at
-- `y` together with the support-function subgradient characterization to identify `g` with a
-- support point of `S` at `x`. Central symmetry gives `-g ∈ S`, hence
-- `f y = (ξ[S] y).toReal ≥ ⟪-g, y⟫`. Rearranging yields
-- `0 ≤ f y + f x + ⟪g, y - x⟫`.
/-- Helper for Lemma 7.17: the real-valued support-function surface of a nonempty bounded set is
positively homogeneous of degree `1` on the whole space. -/
lemma supportFunction_toReal_isPositivelyHomogeneousOn_univ_of_nonempty_bounded
    (S : Set E) (hS_nonempty : S.Nonempty) (_hS_bounded : Bornology.IsBounded S) :
    IsPositivelyHomogeneousOn 1 Set.univ (fun x ↦ (ξ[S] x).toReal) where
  smul_mem := by
    -- The whole-space domain is closed under every nonnegative scaling.
    intro x hx τ
    simp
  map_smul := by
    -- Read the Chapter 3 `EReal` scaling law through `EReal.toReal`.
    intro x hx τ
    simpa [Real.rpow_one, smul_eq_mul, EReal.toReal_mul] using
      congrArg EReal.toReal (supportFunction_smul S hS_nonempty x τ)

/-- Helper for Lemma 7.17: lifting a real-valued function to `WithTop ℝ` turns the unconstrained
subdifferential into the whole-space constrained subdifferential. -/
private lemma mem_lifted_subdifferential_iff_mem_subdifferential_univ
    {h : E → ℝ} {x g : E} :
    g ∈ ∂ (fun z ↦ (h z : WithTop ℝ))(x) ↔ g ∈ ∂[Set.univ] h(x) := by
  -- Rewrite both owners to the same global affine lower-support inequality.
  rw [mem_subdifferential_coe_real_iff, mem_subdifferentialWithin_iff]
  simp

/-- Helper for Lemma 7.17: a centrally symmetric support function is even after passing to
`EReal.toReal`. -/
lemma supportFunction_toReal_neg_eq_of_centrallySymmetric
    (S : Set E) (hS_centrallySymmetric : ∀ ⦃s : E⦄, s ∈ S → -s ∈ S) (z : E) :
    (ξ[S] (-z)).toReal = (ξ[S] z).toReal := by
  -- Route correction: prove evenness on the canonical `EReal` owner first, then apply `toReal`.
  have hξ : ξ[S] (-z) = ξ[S] z := by
    rw [supportFunction_apply, supportFunction_apply]
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      rintro _ ⟨s, hs, rfl⟩
      have hneg : -s ∈ S := hS_centrallySymmetric hs
      calc
        ((inner ℝ s (-z) : ℝ) : EReal) = ((inner ℝ (-s) z : ℝ) : EReal) := by
          simp [inner_neg_left, inner_neg_right]
        _ ≤ sSup ((fun g ↦ ↑(inner ℝ g z)) '' S) := le_sSup ⟨-s, hneg, rfl⟩
    · refine sSup_le ?_
      rintro _ ⟨s, hs, rfl⟩
      have hneg : -s ∈ S := hS_centrallySymmetric hs
      calc
        ((inner ℝ s z : ℝ) : EReal) = ((inner ℝ (-s) (-z) : ℝ) : EReal) := by
          simp [inner_neg_left, inner_neg_right]
        _ ≤ sSup ((fun g ↦ ↑(inner ℝ g (-z))) '' S) := le_sSup ⟨-s, hneg, rfl⟩
  -- The real-valued bridge preserves equal support values.
  exact congrArg EReal.toReal hξ

/-- Helper for Lemma 7.17: a whole-space subgradient of the real-valued support function at `x`
is simultaneously a subgradient at `0`, and it touches the support function at `x`. -/
lemma supportFunction_toReal_subgradient_zero_and_touch_of_mem_subdifferentialWithin
    (S : Set E) (hS_nonempty : S.Nonempty) (hS_bounded : Bornology.IsBounded S)
    {x g : E}
    (hg : g ∈ subdifferentialWithin Set.univ (fun z ↦ (ξ[S] z).toReal) x) :
    g ∈ ∂ (fun z ↦ ((ξ[S] z).toReal : WithTop ℝ))(0) ∧
      inner ℝ g x = (ξ[S] x).toReal := by
  have hf_hom :
      IsPositivelyHomogeneousOn 1 Set.univ (fun z ↦ (ξ[S] z).toReal) :=
    supportFunction_toReal_isPositivelyHomogeneousOn_univ_of_nonempty_bounded
      S hS_nonempty hS_bounded
  have hg_top : g ∈ ∂ (fun z ↦ ((ξ[S] z).toReal : WithTop ℝ))(x) := by
    -- Rewrite the whole-space real-valued owner to the unconstrained `WithTop` owner.
    exact (mem_lifted_subdifferential_iff_mem_subdifferential_univ).2 hg
  -- Lemma 3.15 packages the origin subgradient reduction and the touching identity.
  rw [subdifferential_eq_subdifferential_zero_of_posHomogeneous hf_hom x] at hg_top
  exact hg_top

/-- Lemma 7.17: the real-valued support-function surface `x ↦ (ξ[S] x).toReal` of a nonempty
bounded centrally symmetric set is strictly positive on the whole space in the sense of
Definition 7.81. At this owner level, closedness is redundant because the support function depends
only on the closed convex hull of `S`, while nonemptiness is essential to keep the `.toReal`
bridge faithful. -/
theorem supportFunction_strictlyPositiveOn_univ_of_nonempty_bounded_centrallySymmetric
    (S : Set E) (hS_nonempty : S.Nonempty) (hS_bounded : Bornology.IsBounded S)
    (hS_centrallySymmetric : ∀ ⦃s : E⦄, s ∈ S → -s ∈ S) :
    StrictlyPositiveOn Set.univ (fun x ↦ (ξ[S] x).toReal) := by
  have hf_hom :
      IsPositivelyHomogeneousOn 1 Set.univ (fun z ↦ (ξ[S] z).toReal) :=
    supportFunction_toReal_isPositivelyHomogeneousOn_univ_of_nonempty_bounded
      S hS_nonempty hS_bounded
  have hzero : (ξ[S] (0 : E)).toReal = 0 := by
    -- Positive homogeneity at the zero scalar forces the support value at the origin to vanish.
    simpa [Real.rpow_one] using hf_hom.map_smul (by simp : (0 : E) ∈ Set.univ) (0 : NNReal)
  intro x y g _hx _hy hg
  rcases
      supportFunction_toReal_subgradient_zero_and_touch_of_mem_subdifferentialWithin
        S hS_nonempty hS_bounded hg with
    ⟨hg_zero, htouch⟩
  have hminus :
      (ξ[S] (-y)).toReal ≥ (ξ[S] (0 : E)).toReal + inner ℝ g (-y - 0) := by
    -- Evaluate the origin subgradient inequality at `-y`.
    exact mem_subdifferential_coe_real_iff.mp hg_zero (-y)
  have hnonneg : 0 ≤ (ξ[S] y).toReal + inner ℝ g y := by
    -- Central symmetry turns the inequality at `-y` into the needed lower bound at `y`.
    have hyineq : (ξ[S] y).toReal ≥ -inner ℝ g y := by
      rw [supportFunction_toReal_neg_eq_of_centrallySymmetric S hS_centrallySymmetric y, hzero] at hminus
      simpa [sub_eq_add_neg, inner_neg_right] using hminus
    linarith
  -- The touching identity cancels the `x`-terms in the strict-positivity expression.
  have hrewrite :
      (ξ[S] y).toReal + (ξ[S] x).toReal + inner ℝ g (y - x) =
        (ξ[S] y).toReal + inner ℝ g y := by
    rw [inner_sub_right, htouch]
    ring
  rw [hrewrite]
  exact hnonneg

end
