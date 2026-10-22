/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: linear convergence of gradient descent on strongly convex smooth objectives over
real Hilbert spaces.

Owner-style declarations sampled for this refinement:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`
* `gradientMethod` in `Algorithm_2_1`
* `gradientMethod_sqdist_le_geometric_rate` in `Theorem_2_17`

Best owner abstraction:
* the source-facing primitive objective data are `hf : f ∈ 𝓢[μ, L]¹¹`;
* the minimizer witness `hxStar : IsMinOn f Set.univ xStar` is separate primitive data;
* the canonical squared-distance contraction owner is
  `gradientMethod_sqdist_le_geometric_rate`;
* Theorem 2.18 is the optimal-step bridge/view obtained by specializing that owner theorem to
  `h = 2 / (μ + L)` and simplifying the scalar factor.

Accordingly, this file states Theorem 2.18 as the squared-distance reformulation of the canonical
optimal-step contraction theorem from `Theorem_2_17` on the intrinsic real-Hilbert-space owner
layer, rather than keeping a separate Euclidean-model statement or routing the proof through the
distance theorem and then squaring it again.
-/

section

variable {μ L : ℝ} {f : E → ℝ}

/-- Helper for Theorem 2.18: the optimal constant-step contraction factor from
`gradientMethod_sqdist_le_geometric_rate` is the square of the standard ratio
`(L - μ) / (L + μ)`. -/
private lemma optimal_step_factor_eq_ratio_sq (μ L : ℝ) (hden : 0 < μ + L) :
    1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L) =
      ((L - μ) / (L + μ)) ^ (2 : ℕ) := by
  -- Clear the positive denominator and reduce to a polynomial identity.
  have hden_ne : μ + L ≠ 0 := ne_of_gt hden
  ring_nf
  field_simp [hden_ne]
  ring

/-- Theorem 2.18 on the intrinsic real-Hilbert-space owner layer: if `f : E → ℝ` lies in the
strongly convex smooth class `𝓢^{1,1}_{μ,L}` and `xStar` is a minimizer of `f`, then gradient
descent with step
size `2 / (μ + L)` contracts the squared distance to `xStar` by the factor
`((L - μ) / (L + μ))^(2k)` after `k` iterations. The textbook `ℝⁿ` statement is recovered by
specializing `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: specialize the owner squared-distance estimate
-- `gradientMethod_sqdist_le_geometric_rate` from `Theorem_2_17` to the optimal constant step size
-- `2 / (μ + L)`, then simplify the resulting contraction factor to
-- `((L - μ) / (L + μ))^(2k)`. In the nontrivial ambient case, `μ ≤ L` is derived from the owner
-- hypothesis; the subsingleton case is tautological.
theorem gradientMethod_sqdist_le_optimal_linear_rate
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) (k : ℕ) :
    ‖gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k - xStar‖ ^ (2 : ℕ) ≤
      (((L - μ) / (L + μ)) ^ (2 * k)) * ‖(x0 - xStar)‖ ^ (2 : ℕ) := by
  -- Split off the degenerate ambient case, where all iterates and minimizers coincide.
  by_cases hE : Subsingleton E
  · have hx0 : x0 = xStar := hE.elim _ _
    subst hx0
    have hxk : gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k = x0 := hE.elim _ _
    simp [hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
    have hμL : μ ≤ L := hf'.mu_le_L
    -- The owner hypothesis gives the positivity needed to specialize the optimal step.
    have hden : 0 < μ + L := by
      nlinarith [hf'.mu_pos, hμL]
    have hh0 : 0 < 2 / (μ + L) := by
      positivity
    -- Specialize the geometric owner estimate at the optimal constant step size.
    have hsq :=
      gradientMethod_sqdist_le_geometric_rate hf hxStar (2 / (μ + L)) hh0 le_rfl x0 k
    -- Rewrite the scalar rate into the textbook ratio and then combine exponents.
    calc
      ‖gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k - xStar‖ ^ (2 : ℕ) ≤
          (1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) :=
        hsq
      _ = (((L - μ) / (L + μ)) ^ (2 : ℕ)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
        rw [optimal_step_factor_eq_ratio_sq μ L hden]
      _ = (((L - μ) / (L + μ)) ^ (2 * k)) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
        rw [pow_mul]

end
