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

/-
Primary domain: linear convergence of gradient descent on strongly convex smooth objectives over
real Hilbert spaces.

Owner-style declarations sampled before refining this file:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`
* `gradientMethod` in `Algorithm_2_1`
* `IsStrongConvexSmoothObjective.pairing_lower_bound` in `Theorem_2_13`
* `gradientMethod_sqdist_le_geometric_rate` in `Theorem_2_17`

Source/core/bridge triage:
* source-facing: Proposition 2.23, the `h = 1 / L` contraction estimate;
* core/canonical: `gradientMethod_sqdist_le_geometric_rate`;
* bridge/view: the scalar comparison `((L - μ) / (L + μ)) ≤ 1 - μ / L`, with the textbook
  Euclidean `ℝⁿ` statement recovered by specializing `E`.

Primitive data:
* `hf : f ∈ 𝓢[μ, L]¹¹`;
* `hxStar : IsMinOn f Set.univ xStar`;
* `x0 : E`;
* `k : ℕ`.

Derived API:
* `μ ≤ L`, derived from the owner hypothesis in the nontrivial ambient case via
  `IsStrongConvexSmoothObjective.mu_le_L`;
* positivity of `L`, since `0 < μ ≤ L` then follows in the nontrivial case;
* admissibility of the step size `1 / L`;
* the sharper contraction factor from `Theorem_2_17`, relaxed to the source-facing factor
  `1 - q[μ, L] = 1 - μ / L`.

Accordingly, this file keeps no parallel local owner theorem for the same contraction estimate: it
states Proposition 2.23 as a direct corollary of `gradientMethod_sqdist_le_geometric_rate` on the
intrinsic real-Hilbert-space owner layer, with the textbook `ℝⁿ` case treated only as a
specialization.
-/

section

variable {μ L : ℝ} {f : E → ℝ}

/- Proposition 2.23 is stated in the text for `ℝⁿ`; the theorem below records the same
`h = 1 / L` contraction on the ambient real Hilbert-space owner abstraction and hence
specializes back to the Euclidean case. -/
/-- Proposition 2.23: if `f : E → ℝ` lies in the strongly convex smooth class `𝓢^{1,1}_{μ,L}`,
`xStar` is a
minimizer of `f`, and gradient descent uses the constant step size `1 / L`, then the iterates
satisfy the linear squared-distance contraction
`‖x_k - xStar‖² ≤ (1 - q[μ, L])^k ‖x₀ - xStar‖²`, equivalently
`‖x_k - xStar‖² ≤ (1 - μ / L)^k ‖x₀ - xStar‖²`. The textbook `ℝⁿ` statement is the
specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: specialize the owner estimate
-- `gradientMethod_sqdist_le_geometric_rate` from `Theorem_2_17` to the constant step size
-- `h = 1 / L`, obtaining the sharper factor `((L - μ) / (L + μ))^k`. Then compare
-- `((L - μ) / (L + μ))` with `1 - q[μ, L] = 1 - μ / L` using the owner-derived inequality
-- `μ ≤ L` in the nontrivial ambient case; the subsingleton case is tautological.
theorem gradientMethod_sqdist_le_geometric_rate_step_inv_L
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) (k : ℕ) :
    ‖gradientMethod (fun _ ↦ 1 / L) f x0 k - xStar‖ ^ (2 : ℕ) ≤
      (1 - q[μ, L]) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hx0 : x0 = xStar := hE.elim _ _
    subst hx0
    have hxk : gradientMethod (fun _ ↦ 1 / L) f x0 k = x0 := hE.elim _ _
    calc
      ‖gradientMethod (fun _ ↦ 1 / L) f x0 k - x0‖ ^ (2 : ℕ) = 0 := by
        rw [hxk]
        simp
      _ ≤ (1 - q[μ, L]) ^ k * ‖x0 - x0‖ ^ (2 : ℕ) := by
        simp
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
    have hμL : μ ≤ L := hf'.mu_le_L
    have hL : 0 < L := lt_of_lt_of_le hf'.mu_pos hμL
    have hden : 0 < μ + L := by
      nlinarith [hf'.mu_pos, hμL]
    have hh0 : 0 < 1 / L := by
      positivity
    have hh : 1 / L ≤ 2 / (μ + L) := by
      have hL_ne : L ≠ 0 := ne_of_gt hL
      have hden_ne : μ + L ≠ 0 := ne_of_gt hden
      field_simp [hL_ne, hden_ne]
      nlinarith
    have hnum : 2 * (1 / L) * μ * L = 2 * μ := by
      have hL_ne : L ≠ 0 := ne_of_gt hL
      field_simp [hL_ne]
    have hleft : 1 - (2 * μ) / (μ + L) = (L - μ) / (μ + L) := by
      have hden_ne : μ + L ≠ 0 := ne_of_gt hden
      field_simp [hden_ne]
      nlinarith
    have hsq :=
      gradientMethod_sqdist_le_geometric_rate hf hxStar (1 / L) hh0 hh x0 k
    have hfactor_nonneg : 0 ≤ 1 - (2 * (1 / L) * μ * L) / (μ + L) := by
      rw [hnum, hleft]
      exact div_nonneg (sub_nonneg.mpr hμL) hden.le
    have hcomp :
        1 - (2 * (1 / L) * μ * L) / (μ + L) ≤ 1 - q[μ, L] := by
      rw [hnum]
      have hrewrite : 1 - q[μ, L] = (L - μ) / L := by
        have hL_ne : L ≠ 0 := ne_of_gt hL
        field_simp [hL_ne]
      rw [hrewrite, hleft]
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hμL) hL (by nlinarith [hf'.mu_pos])
    have hpow :
        (1 - (2 * (1 / L) * μ * L) / (μ + L)) ^ k ≤ (1 - q[μ, L]) ^ k := by
      exact pow_le_pow_left₀ hfactor_nonneg hcomp k
    calc
      ‖gradientMethod (fun _ ↦ 1 / L) f x0 k - xStar‖ ^ (2 : ℕ) ≤
          (1 - (2 * (1 / L) * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) :=
        hsq
      _ ≤ (1 - q[μ, L]) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
        gcongr

end
