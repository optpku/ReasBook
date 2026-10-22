/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth
open HasGeometricRateOfConvergence

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: linear convergence of gradient descent on strongly convex smooth objectives over
real Hilbert spaces.

Owner-style declarations sampled before refining this file:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`
* `gradientMethod` in `Algorithm_2_1`
* `IsStrongConvexSmoothObjective.pairing_lower_bound` in `Theorem_2_13`
* `HasGeometricRateOfConvergence.of_step_bound` in `Chap01/Definition_1_2_6`

Source/core/bridge triage:
* source-facing: Theorem 2.17 and its optimal-step corollaries, whose public hypothesis surface
  uses the textbook class notation `f ∈ 𝓢[μ, L]¹¹`;
* core/canonical: `IsStrongConvexSmoothObjective μ L f`, `IsMinOn f Set.univ xStar`,
  `gradientMethod (fun _ ↦ h) f x0`, and the scalar rate owner
  `HasGeometricRateOfConvergence` for the squared-distance sequence;
* bridge/view: the Euclidean specialization of these owner theorems, together with the optimal-step
  rate simplifications.

Primitive data:
* `hf : IsStrongConvexSmoothObjective μ L f`, equivalently `f ∈ 𝓢[μ, L]¹¹`;
* `hxStar : IsMinOn f Set.univ xStar`;
* the step size `h` for the general-rate theorem and the initial point `x0`.

Derived API:
* `hf.mu_pos`;
* `hf.pairing_lower_bound`;
* `hf.gradient_eq_zero_of_isMinOn hxStar`;
* `hf.upper_tangent_quadratic`;
* the subsingleton/nontrivial split used only to turn the optimal squared-distance estimate into a
  distance estimate without adding `μ ≤ L` as primitive data.

Accordingly, this file keeps the source-facing theorem hypotheses in the textbook notation
`f ∈ 𝓢[μ, L]¹¹` while deriving the statements from the core owner predicate
`IsStrongConvexSmoothObjective μ L f`, the canonical gradient-method trajectory, and the minimizer
hypothesis. Internally, the main contraction proof is routed through the scalar owner
`HasGeometricRateOfConvergence` rather than a handwritten induction, while the textbook `ℝⁿ`
formulation is refined to the intrinsic real-Hilbert-space owner layer, with the Euclidean case
recovered by specialization rather than kept as the primary ambient model.
-/

section

variable {μ L : ℝ} {f : E → ℝ}

/-- Helper for Theorem 2.17: one gradient step with a constant stepsize in
`(0, 2 / (μ + L)]` contracts the squared distance to the minimizer by the
textbook factor `1 - 2 h μ L / (μ + L)`. -/
private theorem gradientMethod_sqdist_step_le
    [Nontrivial E]
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (h : ℝ) (hh0 : 0 < h) (hh : h ≤ 2 / (μ + L))
    (x : E) :
    ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) ≤
      (1 - (2 * h * μ * L) / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) := by
  have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  have hμL : μ ≤ L := hf'.mu_le_L
  have hden : 0 < μ + L := by
    nlinarith [hf'.mu_pos, hμL]
  have hgrad0 : ∇ f xStar = 0 := hf'.gradient_eq_zero_of_isMinOn hxStar
  have hpair := hf'.pairing_lower_bound x xStar
  have hpair' :
      (μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) +
          (1 / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) ≤
        inner ℝ (∇ f x) (x - xStar) := by
    simpa [hgrad0, sub_zero] using hpair
  -- The stepsize restriction makes the residual gradient-norm coefficient nonpositive.
  have hcoeff : 0 ≤ 2 * h / (μ + L) - h ^ (2 : ℕ) := by
    have hh' : h * h ≤ h * (2 / (μ + L)) :=
      mul_le_mul_of_nonneg_left hh hh0.le
    have hsq : h ^ (2 : ℕ) ≤ 2 * h / (μ + L) := by
      calc
        h ^ (2 : ℕ) = h * h := by ring
        _ ≤ h * (2 / (μ + L)) := hh'
        _ = 2 * h / (μ + L) := by ring
    exact sub_nonneg.mpr hsq
  -- Expand the next squared distance exactly as in the source proof.
  have h_expand :
      ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) =
        ‖x - xStar‖ ^ (2 : ℕ) - 2 * h * inner ℝ (∇ f x) (x - xStar) +
          h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
    calc
      ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ)
          = ‖(x - xStar) - h • ∇ f x‖ ^ (2 : ℕ) := by
              abel_nf
      _ = ‖x - xStar‖ ^ (2 : ℕ) - 2 * inner ℝ (x - xStar) (h • ∇ f x) +
            ‖h • ∇ f x‖ ^ (2 : ℕ) := by
            simpa using norm_sub_sq_real (x - xStar) (h • ∇ f x)
      _ = ‖x - xStar‖ ^ (2 : ℕ) - 2 * h * inner ℝ (∇ f x) (x - xStar) +
            h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
            rw [real_inner_smul_right, real_inner_comm]
            simp [norm_smul, Real.norm_of_nonneg hh0.le, sq]
            ring
  have h2h_nonneg : 0 ≤ 2 * h := by
    positivity
  have hpair'' :
      2 * h *
          ((μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) +
            (1 / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ)) ≤
        2 * h * inner ℝ (∇ f x) (x - xStar) := by
    exact mul_le_mul_of_nonneg_left hpair' h2h_nonneg
  have hgrad_sq_nonneg : 0 ≤ ‖∇ f x‖ ^ (2 : ℕ) := by
    positivity
  have hcoeff' :
      h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) ≤
        (2 * h / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_right (sub_nonneg.mp hcoeff) hgrad_sq_nonneg
  have hpair''' :
      (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) +
          (2 * h / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) ≤
        2 * h * inner ℝ (∇ f x) (x - xStar) := by
    ring_nf at hpair'' ⊢
    exact hpair''
  have hstep₁ :
      ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) ≤
        ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) +
          h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
    rw [h_expand]
    nlinarith [hpair''']
  have hstep₂ :
      ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) +
          h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) ≤
        ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) := by
    nlinarith [hcoeff']
  -- Substitute the lower pairing bound into the expansion and drop the nonpositive remainder.
  calc
    ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) ≤
        ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) +
          h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := hstep₁
    _ ≤ ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) := hstep₂
    _ = (1 - (2 * h * μ * L) / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) := by
      ring

/-- Helper for Theorem 2.17: the one-step squared-distance contraction packages
into the owner geometric-rate bound for the whole gradient trajectory. -/
private theorem gradientMethod_sqdist_le_geometric_rate_nontrivial
    [Nontrivial E]
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (h : ℝ)
    (hh0 : 0 < h) (hh : h ≤ 2 / (μ + L))
    (x0 : E) (k : ℕ) :
    ‖gradientMethod (fun _ ↦ h) f x0 k - xStar‖ ^ (2 : ℕ) ≤
      (1 - (2 * h * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  let r : ℕ → ℝ := fun j ↦ ‖gradientMethod (fun _ ↦ h) f x0 j - xStar‖ ^ (2 : ℕ)
  -- Bound the owner contraction parameter by `1` so that the scalar iteration API applies.
  have hq₁ : (2 * h * μ * L) / (μ + L) ≤ 1 := by
    have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
    have hμL : μ ≤ L := hf'.mu_le_L
    have hden : 0 < μ + L := by
      nlinarith [hf'.mu_pos, hμL]
    have hstep : h * (μ + L) ≤ 2 := by
      exact (le_div_iff₀ hden).mp hh
    have hAMGM : 4 * μ * L ≤ (μ + L) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (L - μ)]
    have hbound_num : 4 * h * μ * L ≤ h * (μ + L) ^ (2 : ℕ) := by
      have hmulg := mul_le_mul_of_nonneg_left hAMGM hh0.le
      nlinarith [hmulg]
    have hbound :
        (2 * h * μ * L) / (μ + L) ≤ h * (μ + L) / 2 := by
      have h_eq₁ :
          (2 * h * μ * L) / (μ + L) = (4 * h * μ * L) / (2 * (μ + L)) := by
        have hden_ne : μ + L ≠ 0 := ne_of_gt hden
        field_simp [hden_ne]
        ring
      have h_eq₂ :
          h * (μ + L) / 2 = (h * (μ + L) ^ (2 : ℕ)) / (2 * (μ + L)) := by
        have hden_ne : μ + L ≠ 0 := ne_of_gt hden
        field_simp [hden_ne]
      have h2den_nonneg : 0 ≤ 2 * (μ + L) := by
        positivity
      calc
        (2 * h * μ * L) / (μ + L) = (4 * h * μ * L) / (2 * (μ + L)) := h_eq₁
        _ ≤ (h * (μ + L) ^ (2 : ℕ)) / (2 * (μ + L)) := by
          exact div_le_div_of_nonneg_right hbound_num h2den_nonneg
        _ = h * (μ + L) / 2 := h_eq₂.symm
    have hhalf : h * (μ + L) / 2 ≤ 1 := by
      nlinarith [hstep]
    exact le_trans hbound hhalf
  -- Rewrite the gradient recursion into the one-step contraction already proved above.
  have hstep :
      ∀ j : ℕ, r (j + 1) ≤ (1 - (2 * h * μ * L) / (μ + L)) * r j := by
    intro j
    dsimp [r]
    simpa [gradientMethod_succ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      gradientMethod_sqdist_step_le hf hxStar h hh0 hh
        (gradientMethod (fun _ ↦ h) f x0 j)
  -- The owner geometric-rate constructor now iterates the one-step bound automatically.
  have hgeom :
      HasGeometricRateOfConvergence r ((2 * h * μ * L) / (μ + L)) (r 0) := by
    refine of_step_bound hq₁ le_rfl hstep
  simpa [r, mul_comm, mul_left_comm, mul_assoc] using hgeom k

/-- Helper for Theorem 2.17: at the optimal step `2 / (μ + L)`, the generic
contraction factor simplifies to `((L - μ) / (L + μ))²`. -/
private theorem optimal_step_contraction_factor_sq
    [Nontrivial E]
    (hf : f ∈ 𝓢[μ, L]¹¹) :
    1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L) =
      (((L - μ) / (L + μ)) ^ (2 : ℕ)) := by
  have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  have hμL : μ ≤ L := hf'.mu_le_L
  have hden : 0 < μ + L := by
    nlinarith [hf'.mu_pos, hμL]
  have hden₁ : μ + L ≠ 0 := ne_of_gt hden
  have hden₂ : L + μ ≠ 0 := by
    simpa [add_comm] using hden₁
  -- This is the scalar simplification used by both optimal-step corollaries.
  field_simp [hden₁, hden₂]
  ring

/-- Helper for Theorem 2.17: smoothness bounds the objective gap by `(L / 2)` times
the squared distance to a minimizer. -/
private theorem objective_gap_le_half_L_mul_sqdist_to_minimizer
    [Nontrivial E]
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x : E) :
    f x - f xStar ≤ (L / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
  have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  have hupper' := hf'.upper_tangent_quadratic xStar x
  have hgrad0 : ∇ f xStar = 0 := hf'.gradient_eq_zero_of_isMinOn hxStar
  -- Apply the upper tangent inequality at the minimizer and remove the zero-gradient term.
  have hupper'' :
      f x - f xStar ≤
        inner ℝ (∇ f xStar) (x - xStar) + (L / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    nlinarith [hupper']
  simpa [hgrad0] using hupper''

/- Theorem 2.17 is split into one labeled main contraction statement and two unlabeled optimal-step
companions so that the public API stays atomic rather than packaging three conclusions into one
large conjunction. -/
/-- Theorem 2.17: if `f : E → ℝ` lies in the strongly convex smooth class `𝓢^{1,1}_{μ,L}`,
`xStar` is a minimizer of `f`, and `0 < h ≤ 2 / (μ + L)`, then the gradient-method iterates
satisfy the geometric squared-distance contraction
`‖x_k - xStar‖² ≤ (1 - 2 h μ L / (μ + L))^k ‖x₀ - xStar‖²`. -/
-- Proof sketch: combine `gradientMethod_succ` for the constant schedule `fun _ ↦ h` with the
-- owner secant inequality `IsStrongConvexSmoothObjective.pairing_lower_bound` applied to
-- `(x_k, xStar)`. Since `xStar` minimizes `f`, the owner stationarity theorem
-- `hf.gradient_eq_zero_of_isMinOn hxStar` gives `∇ f xStar = 0`; substituting this into the
-- one-step expansion of `‖x_{k+1} - xStar‖²` yields
-- a contraction factor, and the stepsize bound makes the remaining gradient term nonpositive.
-- Iterate the resulting one-step estimate over `k`.
theorem gradientMethod_sqdist_le_geometric_rate
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (h : ℝ)
    (hh0 : 0 < h) (hh : h ≤ 2 / (μ + L))
    (x0 : E) (k : ℕ) :
    ‖gradientMethod (fun _ ↦ h) f x0 k - xStar‖ ^ (2 : ℕ) ≤
      (1 - (2 * h * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hxStar0 : xStar = x0 := hE.elim _ _
    have hxk : gradientMethod (fun _ ↦ h) f x0 k = x0 := hE.elim _ _
    simp [hxStar0, hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    exact gradientMethod_sqdist_le_geometric_rate_nontrivial hf hxStar h hh0 hh x0 k

/-- With the optimal constant step size `2 / (μ + L)`, the gradient method contracts the distance
to the minimizer at the sharp linear rate `((L - μ) / (L + μ))^k`, equivalently
`((Q - 1) / (Q + 1))^k` for `Q = L / μ`. In nontrivial ambient spaces the owner hypothesis already
forces `μ ≤ L`, while the subsingleton case is tautological. -/
-- Proof sketch: specialize `gradientMethod_sqdist_le_geometric_rate` to `h = 2 / (μ + L)`,
-- simplify the contraction factor to `((L - μ) / (L + μ))²`, use the owner-derived inequality
-- `hf.mu_le_L` in the nontrivial case to identify the nonnegative square root, and note that the
-- subsingleton case is immediate.
theorem gradientMethod_dist_le_optimal_geometric_rate
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) (k : ℕ) :
    ‖gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k - xStar‖ ≤
      ((L - μ) / (L + μ)) ^ k * ‖x0 - xStar‖ := by
  by_cases hE : Subsingleton E
  · have hxStar0 : xStar = x0 := hE.elim _ _
    have hxk : gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k = x0 := hE.elim _ _
    simp [hxStar0, hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    let ρ : ℝ := (L - μ) / (L + μ)
    have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
    have hμL : μ ≤ L := hf'.mu_le_L
    have hden : 0 < μ + L := by
      nlinarith [hf'.mu_pos, hμL]
    have hh0 : 0 < 2 / (μ + L) := by
      positivity
    have hρsq :
        1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L) = ρ ^ (2 : ℕ) := by
      simpa [ρ] using optimal_step_contraction_factor_sq (E := E) (f := f) (μ := μ) (L := L) hf
    have hsq :=
      gradientMethod_sqdist_le_geometric_rate_nontrivial
        hf hxStar (2 / (μ + L)) hh0 le_rfl x0 k
    have hρ_nonneg : 0 ≤ ρ := by
      dsimp [ρ]
      simpa [add_comm] using div_nonneg (sub_nonneg.mpr hμL) hden.le
    -- Rewrite the squared-distance estimate with the optimal textbook factor `ρ²`.
    have hsq' :
        ‖gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k - xStar‖ ^ (2 : ℕ) ≤
          (ρ ^ k * ‖x0 - xStar‖) ^ (2 : ℕ) := by
      calc
        ‖gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k - xStar‖ ^ (2 : ℕ) ≤
            (1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) :=
          hsq
        _ = (ρ ^ (2 : ℕ)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by rw [hρsq]
        _ = (ρ ^ k * ‖x0 - xStar‖) ^ (2 : ℕ) := by ring_nf
    exact
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg hρ_nonneg _) (norm_nonneg _))).1 hsq'

/-- With the optimal constant step size `2 / (μ + L)`, the gradient method satisfies the linear
objective-gap estimate
`f(x_k) - f(xStar) ≤ (L / 2) * ((L - μ) / (L + μ))^(2k) * ‖x₀ - xStar‖²`, equivalently
`(L / 2) * ((Q - 1) / (Q + 1))^(2k) * ‖x₀ - xStar‖²` for `Q = L / μ`. As above, no separate
`μ ≤ L` hypothesis is needed: it is derived from `hf` off the subsingleton case. -/
-- Proof sketch: apply the owner smooth upper tangent estimate at `(xStar, x_k)`, use
-- `hf.gradient_eq_zero_of_isMinOn hxStar` to remove the linear term at `xStar`, and then
-- substitute the optimal-step squared-distance estimate obtained from
-- `gradientMethod_sqdist_le_geometric_rate`.
theorem gradientMethod_objective_gap_le_optimal_geometric_rate
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) (k : ℕ) :
    f (gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k) - f xStar ≤
      (L / 2) * (((L - μ) / (L + μ)) ^ (2 * k)) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hxStar0 : xStar = x0 := hE.elim _ _
    have hxk : gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k = x0 := hE.elim _ _
    simp [hxStar0, hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    let xk : E := gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k
    let ρ : ℝ := (L - μ) / (L + μ)
    have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
    have hμL : μ ≤ L := hf'.mu_le_L
    have hden : 0 < μ + L := by
      nlinarith [hf'.mu_pos, hμL]
    have hh0 : 0 < 2 / (μ + L) := by
      positivity
    have hL_nonneg : 0 ≤ L / 2 := by
      nlinarith [hf'.mu_pos, hμL]
    have hρsq :
        1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L) = ρ ^ (2 : ℕ) := by
      simpa [ρ] using optimal_step_contraction_factor_sq (E := E) (f := f) (μ := μ) (L := L) hf
    have hsq :=
      gradientMethod_sqdist_le_geometric_rate_nontrivial
        hf hxStar (2 / (μ + L)) hh0 le_rfl x0 k
    -- Rewrite the optimal-step squared-distance estimate into the textbook factor `ρ^(2k)`.
    have hsq' :
        ‖xk - xStar‖ ^ (2 : ℕ) ≤ ρ ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      calc
        ‖xk - xStar‖ ^ (2 : ℕ) ≤
            (1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
          simpa [xk] using hsq
        _ = (ρ ^ (2 : ℕ)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by rw [hρsq]
        _ = ρ ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ) := by rw [pow_mul]
    have hupper : f xk - f xStar ≤ (L / 2) * ‖xk - xStar‖ ^ (2 : ℕ) :=
      objective_gap_le_half_L_mul_sqdist_to_minimizer
        (E := E) (f := f) (μ := μ) (L := L) hf hxStar xk
    calc
      f xk - f xStar ≤ (L / 2) * ‖xk - xStar‖ ^ (2 : ℕ) := hupper
      _ ≤ (L / 2) * (ρ ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
        gcongr
      _ = (L / 2) * (ρ ^ (2 * k)) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
        ring

end
