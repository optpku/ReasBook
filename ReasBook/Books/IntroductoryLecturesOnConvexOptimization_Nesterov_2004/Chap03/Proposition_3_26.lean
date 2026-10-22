/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe uE uU uι uR

open scoped BigOperators
open scoped WithTopConvexAnalysis

/- Proposition 3.26 (1) lies in the chapter's sampled affine-minorant aggregation domain.

Relevant owner-style declarations sampled before refinement:
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner for
  extended-valued subgradients;
- `mem_subdifferential_iff` in `Definition_3_1_5`, the atomic bridge from the owner notation to
  the supporting-inequality predicate;
- the mathlib affine-map owner `E →ᵃ[ℝ] ℝ`, whose additive and `ℝ`-module structure canonically
  organizes weighted sums of sampled affine minorants;
- `Convex.centerMass_mem`, the owner theorem used for Proposition 3.26 (2).

Best owner abstractions:
- source-facing: the weighted sampled affine lower model from Proposition 3.26 (1);
- core/canonical: the affine-map sum
  `∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i)) : E →ᵃ[ℝ] ℝ`;
- bridge/view: the pointwise evaluation formula for that affine-map sum, together with
  `mem_subdifferential_iff` for the subgradient hypotheses.

Primitive data:
- weights `α : ι → ℝ`;
- sampled points `y : ι → E`;
- sampled subgradients `g : ι → E`;
- sampled values `f (y i)`.

Derived API:
- the sampled affine minorants and their affine-map sum
  `∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i))`;
- the pointwise expansion `sum_smul_sampledAffineMinorant_apply`;
- the lower-bound theorem `sum_smul_sampledAffineMinorant_le`.

The earlier version exposed the sampled model through a proposition-local wrapper around the
canonical affine-map sum and stated the subgradient data through the lower-level predicate
`IsSubgradientAt`. This refinement keeps the same mathematical semantics, but removes that
duplicate owner in favor of the affine-map sum itself and states the hypotheses through the
existing subdifferential notation `∂ f(x)`.
-/

section

variable {ι : Type uι}
variable {E : Type uE} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine minorant determined by one sampled value `f y`, one sample point `y`, and one
chosen subgradient `g`. -/
def sampledAffineMinorant (y g : E) (fy : ℝ) : E →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ E (fy - inner ℝ g y) +
    LinearMap.toAffineMap (((innerSL ℝ) g).toLinearMap)

/-- Evaluating the sampled affine minorant recovers the textbook pointwise affine lower model
`f(y) + ⟪g, x - y⟫`. -/
@[simp] theorem sampledAffineMinorant_apply (y g x : E) (fy : ℝ) :
    sampledAffineMinorant y g fy x = fy + inner ℝ g (x - y) := by
  simp [sampledAffineMinorant, sub_eq_add_neg, inner_add_right, inner_neg_right]
  ring

/-- Evaluating the canonical affine-map sum of the sampled affine minorants gives the weighted
pointwise sum of the textbook lower models. -/
@[simp] theorem sum_smul_sampledAffineMinorant_apply [Fintype ι]
    (α : ι → ℝ) (y g : ι → E) (f : E → ℝ) (x : E) :
    (∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i)) : E →ᵃ[ℝ] ℝ) x =
      ∑ i, α i * (f (y i) + inner ℝ (g i) (x - y i)) := by
  classical
  let s : Finset ι := Finset.univ
  change (s.sum fun i ↦ α i • sampledAffineMinorant (y i) (g i) (f (y i))) x =
    s.sum fun i ↦ α i * (f (y i) + inner ℝ (g i) (x - y i))
  clear_value s
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s his ih =>
      simp [his, ih, sampledAffineMinorant_apply]

/-- Proposition 3.26 (1): the aggregated affine lower model is dominated by the original convex
function. -/
-- Proof sketch: rewrite `g i ∈ ∂ (fun z ↦ (f z : WithTop ℝ))((y i))` via
-- `mem_subdifferential_iff`, apply the resulting affine lower-support inequality at the
-- comparison point `x`, multiply by the nonnegative weight `α i`, sum over the finite index type,
-- and use `∑ i, α i = 1`.
theorem sum_smul_sampledAffineMinorant_le
    [Fintype ι] {f : E → ℝ} (y g : ι → E)
    (hsubgrad : ∀ i, g i ∈ ∂ (fun z ↦ (f z : WithTop ℝ))((y i)))
    (α : ι → ℝ) (hα_nonneg : ∀ i, 0 ≤ α i)
    (hα_sum : ∑ i, α i = 1) (x : E) :
    (∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i)) : E →ᵃ[ℝ] ℝ) x ≤ f x := by
  have hsupport : ∀ i, f (y i) + inner ℝ (g i) (x - y i) ≤ f x := by
    intro i
    have hx_dom : x ∈ dom (fun z ↦ (f z : WithTop ℝ)) := by
      simp [withTopEffectiveDomain]
    have hineq :
        ((f x : WithTop ℝ) ≥
          (f (y i) : WithTop ℝ) + inner ℝ (g i) (x - y i)) :=
      (mem_subdifferential_iff.mp (hsubgrad i)).2 hx_dom
    exact_mod_cast hineq
  calc
    (∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i)) : E →ᵃ[ℝ] ℝ) x
        = ∑ i, α i * (f (y i) + inner ℝ (g i) (x - y i)) := by
          rw [sum_smul_sampledAffineMinorant_apply]
    _ ≤ ∑ i, α i * f x := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      exact mul_le_mul_of_nonneg_left (hsupport i) (hα_nonneg i)
    _ = (∑ i, α i) * f x := by
      rw [Finset.sum_mul]
    _ = f x := by
      rw [hα_sum, one_mul]

end

section

variable {ι : Type uι}
variable {R : Type uR} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/- Proposition 3.26 (2) lies in the finite convex-combination / center-of-mass domain.

Sampled owner-style declarations:
- `Finset.centerMass`
- `Convex.centerMass_mem`
- `ConvexOn.exists_ge_of_centerMass` in `Chap03/Theorem_3_1`

Best owner abstraction:
- `Convex.centerMass_mem`

Primitive data:
- a convex feasible set `S`
- a finite family `u : ι → U` with `u i ∈ S`
- normalized nonnegative weights `α`

Derived API:
- the weighted average `(Finset.univ).centerMass α u`

Source/core/bridge triage:
- source-facing: the normalized weighted-average feasibility statement in Proposition 3.26 (2)
- core/canonical: `Convex.centerMass_mem`
- bridge/view: the source normalization `∑ i, α i = 1`, used only to discharge the owner's
  positivity hypothesis

The previous file exposed an extra proposition-local argmax wrapper and then projected away all of
its maximizer data in the proof. This refinement keeps only the primitive feasibility data that
affect the conclusion and reuses the canonical owner directly.
-/

/-- Proposition 3.26 (2): a convex feasible set contains the normalized weighted average of
finitely many feasible points. The textbook real statement is the specialization `R = ℝ`. -/
-- Proof sketch: apply the canonical owner theorem `Convex.centerMass_mem`; the source
-- normalization `∑ i, α i = 1` supplies the required positivity hypothesis.
theorem centerMass_mem_of_sum_eq_one
    {U : Type uU} [Fintype ι] [AddCommGroup U] [Module R U]
    {S : Set U} (hS : Convex R S) (u : ι → U) (hu : ∀ i, u i ∈ S)
    (α : ι → R) (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1) :
    (Finset.univ).centerMass α u ∈ S := by
  classical
  exact hS.centerMass_mem
    (fun i _ ↦ hα_nonneg i)
    (by simp [hα_sum])
    (fun i _ ↦ hu i)

end

end
