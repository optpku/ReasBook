/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_39
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- Primary domain: finite max-type objectives built from real-Hilbert first-order models of
strongly convex and smooth components.

Sampled owner-style declarations:
* `StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt` in `Definition_2_14`;
* `taylor_upper_bound_of_contDiffOne_withLipschitzGradient` in `Mathlib`;
* `IsStrongConvexSmoothObjective` and `𝓢[μ, L]¹¹` in `Definition_2_17`;
* `maxTypeAffineApproximation` in `Definition_2_39`.

Best owner abstractions:
* `StrongConvexOn Set.univ μ` together with `ContDiff ℝ 1` for the lower tangent bound;
* `ContDiff ℝ 1` together with `LipschitzWith L (∇ ·)` for the upper tangent bound;
* `maxTypeObjective fi` and `maxTypeAffineApproximation fi xBar` from `Definition_2_39` for the
  max-type objective and its local affine model.

Primitive data:
* the nonempty finite component family `fi : ι → E → ℝ`;
* the component strong-convexity / `C¹` owner data for the lower estimate;
* the component `C¹` / Lipschitz-gradient owner data for the upper estimate.

Derived API:
* the owner max objective `maxTypeObjective fi`;
* component lower and upper tangent bounds recovered from the owner data;
* the textbook companion theorem with componentwise membership `fi i ∈ 𝓢[μ, L]¹¹`.

Source/core/bridge triage:
* source-facing: the paired quadratic bounds under the textbook componentwise hypothesis
  `fi i ∈ 𝓢[μ, L]¹¹`;
* core/canonical: `StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt`,
  `taylor_upper_bound_of_contDiffOne_withLipschitzGradient`, and
  `maxTypeAffineApproximation fi xBar`;
* bridge/view: passage from `fi i ∈ 𝓢[μ, L]¹¹` to the lower and upper owner data.

The public API below is kept at the owner-theorem level: the lower and upper inequalities are
exposed as separate canonical theorems with minimal hypotheses, while the textbook paired
statement remains as a thin source-facing companion. -/

section StrongConvexSmooth

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A finite max-type objective inherits the quadratic lower tangent bound from the corresponding
component-wise lower tangent bounds. -/
-- Proof sketch: apply the lower tangent bound for each component `fᵢ`, then take the finite
-- maximum over `i`; the common quadratic term is independent of `i` and factors out of the
-- resulting supremum.
private theorem maxTypeObjective_lower_tangent_quadratic_of_component_bounds
    (fi : ι → E → ℝ) (μ : ℝ)
    (hlower :
      ∀ i : ι, ∀ x xBar : E,
        fi i x ≥
          fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar) +
            (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ))
    (x xBar : E) :
    maxTypeObjective fi x ≥
      maxTypeAffineApproximation fi xBar x + (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  rw [maxTypeObjective_apply, maxTypeAffineApproximation_apply]
  have hsup :
      Finset.univ.sup' Finset.univ_nonempty
          (fun i : ι ↦ fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar)) ≤
        Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ fi i x) -
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
    rw [Finset.sup'_le_iff]
    intro i hi
    have hmax :
        fi i x ≤ Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ fi j x) := by
      exact Finset.le_sup' (fun j : ι ↦ fi j x) hi
    linarith [hlower i x xBar, hmax]
  linarith

/-- A finite max-type objective inherits the quadratic upper tangent bound from the corresponding
component-wise upper tangent bounds. -/
-- Proof sketch: apply the upper tangent bound for each component `fᵢ`, then take the finite
-- maximum over `i`; the common quadratic term is independent of `i` and factors out of the
-- resulting supremum.
private theorem maxTypeObjective_upper_tangent_quadratic_of_component_bounds
    (fi : ι → E → ℝ) (L : ℝ)
    (hupper :
      ∀ i : ι, ∀ x xBar : E,
        fi i x ≤
          fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar) +
            (L / 2) * ‖x - xBar‖ ^ (2 : ℕ))
    (x xBar : E) :
    maxTypeObjective fi x ≤
      maxTypeAffineApproximation fi xBar x + (L / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  rw [maxTypeObjective_apply, maxTypeAffineApproximation_apply, Finset.sup'_le_iff]
  intro i hi
  have hmodel :
      fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : ι ↦ fi j xBar + inner ℝ (∇ (fi j) xBar) (x - xBar)) := by
    exact
      Finset.le_sup'
        (fun j : ι ↦ fi j xBar + inner ℝ (∇ (fi j) xBar) (x - xBar)) hi
  linarith [hupper i x xBar, hmodel]

/-- If each component is `μ`-strongly convex on the whole space and `C¹`, then the finite
max-type objective satisfies the corresponding quadratic lower tangent bound relative to
`maxTypeAffineApproximation fi xBar`. -/
theorem maxTypeObjective_lower_tangent_quadratic_of_components
    (fi : ι → E → ℝ) (μ : ℝ)
    (hstrong : ∀ i : ι, StrongConvexOn Set.univ μ (fi i))
    (hcontDiff : ∀ i : ι, ContDiff ℝ 1 (fi i))
    (x xBar : E) :
    maxTypeObjective fi x ≥
      maxTypeAffineApproximation fi xBar x + (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
  maxTypeObjective_lower_tangent_quadratic_of_component_bounds fi μ
    (fun i x xBar ↦ by
      have hgrad : HasGradientAt (fi i) (∇ (fi i) xBar) xBar :=
        (hcontDiff i).differentiable_one xBar |>.hasGradientAt
      simpa using
        StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
          (hstrong i) (by simp) (by simp) hgrad)
    x xBar

/-- If each component is `C¹` and has `L`-Lipschitz gradient, then the finite max-type objective
satisfies the corresponding quadratic upper tangent bound relative to
`maxTypeAffineApproximation fi xBar`. -/
theorem maxTypeObjective_upper_tangent_quadratic_of_components
    (fi : ι → E → ℝ) (L : NNReal)
    (hcontDiff : ∀ i : ι, ContDiff ℝ 1 (fi i))
    (hgrad_lipschitz : ∀ i : ι, LipschitzWith L (∇ (fi i)))
    (x xBar : E) :
    maxTypeObjective fi x ≤
      maxTypeAffineApproximation fi xBar x + ((L : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
  maxTypeObjective_upper_tangent_quadratic_of_component_bounds fi (L : ℝ)
    (fun i x xBar ↦ by
      have hupper :=
        taylor_upper_bound_of_contDiffOne_withLipschitzGradient
          (hcontDiff i) (hgrad_lipschitz i) xBar x
      simpa [firstOrderTaylorModelAt_apply] using hupper)
    x xBar

/-- Lemma 2.18 in the chapter notation surface: if each component of a finite max-type objective
lies in `𝓢[μ, L]¹¹`, then the max-type function satisfies the corresponding lower and upper
quadratic bounds relative to its canonical affine approximation
`maxTypeAffineApproximation fi xBar`. -/
-- Proof sketch: pass from `fi i ∈ 𝓢[μ, L]¹¹` to the lower owner data
-- `StrongConvexOn Set.univ μ (fi i)` and `ContDiff ℝ 1 (fi i)`, and to the upper owner data
-- `ContDiff ℝ 1 (fi i)` and `LipschitzWith (Real.toNNReal L) (∇ (fi i))`; then apply the two
-- atomic owner theorems above and simplify the smoothness constant in the nontrivial ambient
-- case. The subsingleton case is tautological.
theorem maxTypeObjective_quadratic_bounds_of_components_mem
    (fi : ι → E → ℝ) (μ L : ℝ)
    (hfi : ∀ i : ι, fi i ∈ 𝓢[μ, L]¹¹)
    (x xBar : E) :
    maxTypeObjective fi x ≥
        maxTypeAffineApproximation fi xBar x + (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) ∧
      maxTypeObjective fi x ≤
        maxTypeAffineApproximation fi xBar x + (L / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  have hfi' : ∀ i : ι, IsStrongConvexSmoothObjective μ L (fi i) :=
    fun i ↦ mem_S11_iff.mp (hfi i)
  have hstrong : ∀ i : ι, StrongConvexOn Set.univ μ (fi i) :=
    fun i ↦ (hfi' i).strongConvexOn
  have hcontDiff : ∀ i : ι, ContDiff ℝ 1 (fi i) :=
    fun i ↦ (hfi' i).contDiff
  refine ⟨maxTypeObjective_lower_tangent_quadratic_of_components fi μ hstrong hcontDiff x xBar, ?_⟩
  by_cases hE : Subsingleton E
  · have hx : x = xBar := hE.elim x xBar
    subst hx
    simp [maxTypeObjective_apply, maxTypeAffineApproximation_apply]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    let i0 : ι := Classical.choice ‹Nonempty ι›
    have hL : 0 ≤ L := le_trans (hfi' i0).mu_pos.le (hfi' i0).mu_le_L
    have hgrad_lipschitz : ∀ i : ι, LipschitzWith (Real.toNNReal L) (∇ (fi i)) := by
      intro i
      refine LipschitzWith.of_dist_le_mul ?_
      intro y z
      have hdist := (hfi' i).gradient_lipschitz y z
      have hL' : L ≤ (Real.toNNReal L : ℝ) := by
        simp [Real.toNNReal_of_nonneg hL]
      simpa [dist_eq_norm] using
        le_trans hdist (mul_le_mul_of_nonneg_right hL' (norm_nonneg _))
    simpa [Real.toNNReal_of_nonneg hL] using
      maxTypeObjective_upper_tangent_quadratic_of_components
        fi (Real.toNNReal L) hcontDiff hgrad_lipschitz x xBar

end StrongConvexSmooth
