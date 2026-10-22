/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {X : Type u}

/- Lemma 3.2.2 lies in the finite best-value / monotone-modulus domain.

Sampled owner declarations:
- `bestFunctionValueUpTo` and `bestRadiusUpTo` in `Definition_3_55`, the source-facing objective
  and radius owners for finite sampled prefix minima;
- mathlib `Finite.map_iInf_of_monotone`, the finite-infimum transport rule for monotone maps;
- mathlib `iInf_le`, the pointwise lower-bound rule for a finite indexed infimum;
- `bestFunctionValueUpTo_sub_le_pointwiseGrowthFunction_at_bestRadius` in `Lemma_3_26`, the
  direct downstream specialization of the present lemma.

Best owner abstraction:
- core/canonical: the finite infima underlying `bestFunctionValueUpTo` and `bestRadiusUpTo`,
  together with finite-infimum monotonicity;
- bridge/view: the later specialization to pointwise growth functions in `Lemma_3_26`.

Primitive data:
- a sample sequence `xSeq : ℕ → X`;
- a real radius sequence `radii : ℕ → ℝ`;
- a reference point `xStar`;
- a monotone modulus `ω`;
- the pointwise estimates `f (xSeq i) - f xStar ≤ ω (radii i)` on `Fin (k + 1)`.

Derived API:
- the best-value gap bound at the best sampled radius.

Source/core/bridge triage:
- source-facing: Lemma 3.2.2's best sampled gap inequality;
- core/canonical: `bestFunctionValueUpTo`, `bestRadiusUpTo`, and finite-infimum monotonicity;
- bridge/view: `bestFunctionValueUpTo` on the objective side and `bestRadiusUpTo` on the radius
  side;
- bridge/view: downstream specializations where the radius sequence is built from distances or
  localization measures.

The chapter's public owners for finite sampled minima are `bestFunctionValueUpTo` and
`bestRadiusUpTo`, with the raw finite infimum kept as the underlying canonical expression rather
than a separate neutral wrapper. This file keeps the source-facing objective notation on the
left-hand side and the source-facing radius notation on the right-hand side, rather than reusing
the objective-value owner for both roles.
-/

/-- Lemma 3.2.2: if `f_k^* = min_{0 ≤ i ≤ k} f(x_i)` and `v_k^* = min_{0 ≤ i ≤ k} v_i`, then the
best function-value gap up to step `k` is bounded by the modulus value at the best radius. This
specializes to `ω_f(x^*; v_k^*)` when `ω = ω_f(x^*; ·)`, with `ω` allowed to take the value `⊤`
when the growth profile is unbounded. -/
-- Proof sketch: for each `i ≤ k`, apply the pointwise bound
-- `f (xSeq i) - f xStar ≤ ω (radii i)`. Since
-- `Fin (k + 1)` is finite, the minima defining `f_k^*` and `v_k^*` are attained; monotonicity of
-- `ω` then identifies `ω (min_i radii i)` with `min_i ω (radii i)`, and taking minima on both
-- sides gives the claim.
theorem bestFunctionValueGapUpTo_le_modulusAtBestRadius
    (f : X → ℝ) (ω : ℝ → WithTop ℝ) (hω_mono : Monotone ω)
    (xSeq : ℕ → X) (xStar : X) (radii : ℕ → ℝ) (k : ℕ)
    (hbound : ∀ i : Fin (k + 1), f (xSeq i) - f xStar ≤ ω (radii i)) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar ≤
      ω (bestRadiusUpTo radii k) := by
  let gap : ℕ → ℝ := fun i ↦ f (xSeq i) - f xStar
  have hsub_mono : Monotone (fun y : ℝ ↦ ((y - f xStar : ℝ) : WithTop ℝ)) := by
    intro a b hab
    simpa using sub_le_sub_right hab (f xStar)
  have hgap_eq :
      ((bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar : ℝ) : WithTop ℝ) =
        ⨅ i : Fin (k + 1), (gap i : WithTop ℝ) := by
    simpa [gap, bestFunctionValueUpTo] using
      Finite.map_iInf_of_monotone (fun i : Fin (k + 1) ↦ f (xSeq i)) hsub_mono
  have hgap_le :
      (⨅ i : Fin (k + 1), (gap i : WithTop ℝ)) ≤
        ⨅ i : Fin (k + 1), ω (radii i) :=
    Finite.ciInf_mono hbound
  have hω_eq :
      ω (bestRadiusUpTo radii k) =
        ⨅ i : Fin (k + 1), ω (radii i) := by
    simpa [bestRadiusUpTo] using
      Finite.map_iInf_of_monotone (fun i : Fin (k + 1) ↦ radii i) hω_mono
  calc
    ((bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar : ℝ) : WithTop ℝ) =
        ⨅ i : Fin (k + 1), (gap i : WithTop ℝ) := hgap_eq
    _ ≤ ⨅ i : Fin (k + 1), ω (radii i) := hgap_le
    _ = ω (bestRadiusUpTo radii k) := hω_eq.symm

end
