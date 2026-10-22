/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 3.15 is the chapter's real-valued bridge over the upstream `WithTop`-valued
subdifferential owner.

Primary domain:
- real-valued subdifferentials of positively homogeneous functions.

Sampled owner-style declarations:
- `IsSubgradientAt` and `subdifferential` in `Definition_3_1_5`, the chapter owner for
  subgradients, already stated on `E → WithTop ℝ`;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity;
- `subdifferential_eq_subdifferential_zero_touching_of_convex_oneHomogeneous` in
  `Lemma_3_1_15`, an earlier Euclidean real-valued restatement of the same source fact with a
  redundant convexity hypothesis;
- `mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing` in `Theorem_3_1_24`, an existing
  downstream use of the canonical owner on the real-to-`WithTop` coercion.

Best owner abstraction:
- primitive predicate `IsSubgradientAt` from `Definition_3_1_5`, specialized to
  `fun y ↦ (f y : WithTop ℝ)`;
- derived set-valued owner `subdifferential` from `Definition_3_1_5`;
- `IsPositivelyHomogeneousOn 1 Set.univ f` for the positive-homogeneity input to Lemma 3.15.

Primitive data:
- the affine lower-support predicate `IsSubgradientAt (fun y ↦ (f y : WithTop ℝ))`;
- the positive-homogeneity owner hypothesis.

Internal bridge:
- the coercion lemma identifying the owner predicate with the usual real-valued inequality.

Source/core/bridge triage:
- source-facing: Lemma 3.15's description of `∂f(x)` for one-homogeneous real-valued `f`;
- core/canonical: `IsSubgradientAt`, `subdifferential`, `IsPositivelyHomogeneousOn`;
- bridge/view: `mem_subdifferential_coe_real_iff`, the owner-level real-valued coercion bridge
  from `Definition_3_1_5`.

This file therefore stops duplicating the real-valued subgradient owner. Its public API keeps only
the source-facing Lemma 3.15 statement and reuses the owner-level real-valued bridge from
`Definition_3_1_5` instead of carrying a private copy.
-/

/-- Lemma 3.15: for a positively `1`-homogeneous function on a real inner-product space,
the subdifferential at `x` is exactly the intersection of the origin subdifferential with the
touching condition `⟪g, x⟫ = f x`. -/
-- Proof sketch: if `g ∈ ∂f(x)`, apply the subgradient inequality at `0` and at `2 • x`; positive
-- homogeneity gives the two opposite inequalities needed for `⟪g, x⟫ = f x`, and then the same
-- supporting inequality shows `g ∈ ∂f(0)`. Conversely, if `g ∈ ∂f(0)` and `⟪g, x⟫ = f x`,
-- rewrite the support inequality at `0` to obtain the support inequality at `x`. No convexity
-- hypothesis is needed once the owner subgradient inequality is used directly.
theorem subdifferential_eq_subdifferential_zero_of_posHomogeneous
    {f : E → ℝ} (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f) (x : E) :
    ∂ (fun y ↦ (f y : WithTop ℝ))(x) =
      ∂ (fun y ↦ (f y : WithTop ℝ))(0) ∩ {g | inner ℝ g x = f x} := by
  have h0 : f 0 = 0 := by
    simpa using hf_hom.map_smul (show x ∈ Set.univ by simp) (0 : NNReal)
  ext g
  constructor
  · intro hg
    have hsub : ∀ y : E, f y ≥ f x + inner ℝ g (y - x) :=
      mem_subdifferential_coe_real_iff.mp hg
    have hfx_le : f x ≤ inner ℝ g x := by
      have hzero : 0 ≥ f x - inner ℝ g x := by
        simpa [h0, sub_eq_add_neg] using hsub 0
      linarith
    have htwo : f (x + x) = 2 * f x := by
      simpa [NNReal.smul_def, two_smul, smul_eq_mul] using
        hf_hom.map_smul (show x ∈ Set.univ by simp) (2 : NNReal)
    have hinner_le : inner ℝ g x ≤ f x := by
      have htwo_sub : f (x + x) ≥ f x + inner ℝ g x := by
        simpa [two_smul] using hsub ((2 : ℝ) • x)
      linarith
    have htouch : inner ℝ g x = f x := le_antisymm hinner_le hfx_le
    refine ⟨?_, htouch⟩
    exact mem_subdifferential_coe_real_iff.mpr <| fun y ↦ by
      calc
        f y ≥ f x + inner ℝ g (y - x) := hsub y
        _ = inner ℝ g y := by
          rw [sub_eq_add_neg, inner_add_right, inner_neg_right]
          linarith
        _ = f 0 + inner ℝ g (y - 0) := by
          simp [h0]
  · rintro ⟨hg0, htouch⟩
    have hsub0 : ∀ y : E, f y ≥ f 0 + inner ℝ g (y - 0) :=
      mem_subdifferential_coe_real_iff.mp hg0
    exact mem_subdifferential_coe_real_iff.mpr <| fun y ↦ by
      calc
        f y ≥ f 0 + inner ℝ g (y - 0) := hsub0 y
        _ = inner ℝ g y := by simp [h0]
        _ = f x + inner ℝ g (y - x) := by
          rw [← htouch, sub_eq_add_neg, inner_add_right, inner_neg_right]
          linarith

end
