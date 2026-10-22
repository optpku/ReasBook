/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {E₁ : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup E₁] [Module ℝ E₁]

/- Proposition 7.30 lies in the finite weighted-average / logarithmic primal-dual gap domain.

Sampled owner-style declarations:
- `Finset.centerMass` in mathlib's convex-combination API, the canonical owner of weighted finite
  averages;
- `Finset.centroid` in mathlib's affine-space API, the equal-weight specialization of
  `Finset.centerMass`;
- `Finset.centroid_eq_centerMass`, the bridge identifying the arithmetic mean with the canonical
  center-of-mass owner;
- `Real.log_le_iff_le_exp`, the canonical logarithm-to-exponential comparison used in the final
  estimate.

Best owner abstraction:
- source-facing: Proposition 7.30's primal-dual efficiency estimate;
- core/canonical: `Finset.centroid` for the primal arithmetic mean and `Finset.centerMass` for the
  inverse-`ψ` weighted dual average;
- bridge/view: the logarithmic hypothesis rewritten as an exponential bound.

Primitive data:
- the iterate family `x : Fin (k + 1) → P`;
- the positive objective `ψ` and positive dual objective `ψStar`;
- the dual-point assignment `u`.

Derived API:
- the canonical primal aggregate `barx`;
- the canonical dual aggregate `barU`;
- the exponential lower bound obtained from the logarithmic gap inequality.

The previous file stored all three aggregates as separate public definitions even though they are
exact instances of the mathlib owners `Finset.centroid` and `Finset.centerMass`. This refinement
deletes those duplicate wrappers and states the proposition directly on the owner abstractions.
The auxiliary witness `barx : P` is also removed from the theorem surface: the primal aggregate is
intrinsic, so the only required source-facing input is its membership in `P`.
-/

section WeightedAverages

variable {P : Set E} {Ω : Set E₁}
variable (ψ : P → { r : ℝ // 0 < r }) (u : P → E₁) (ψStar : Ω → { r : ℝ // 0 < r })
variable {k : ℕ} (x : Fin (k + 1) → P)

local notation "barx" => Finset.univ.centroid ℝ (fun i ↦ (x i : E))
local notation "barU" =>
  Finset.univ.centerMass (fun i ↦ ((ψ (x i) : ℝ)⁻¹)) (fun i ↦ u (x i))

-- Proof sketch: the logarithmic hypothesis is `log (ψ⋆(barU) / ψ(barx)) ≤ ellStar / Sk`.
-- Apply `Real.log_le_iff_le_exp` to bound the ratio by `exp (ellStar / Sk)`, then divide by the
-- positive factor `exp (ellStar / Sk)` and rewrite with `Real.exp_neg`.
/-- Proposition 7.30: if the logarithmic primal-dual gap at the canonical weighted aggregates
`barx` and `barU` is bounded by `\ell_k^\star / S_k`, then
`ψ(barx) ≥ ψ^\star(barU) \exp(-\ell_k^\star / S_k)`. Here `barx` is the arithmetic mean of the
iterates and `barU` is their inverse-`ψ` weighted dual center of mass. -/
theorem primalDualEfficiencyEstimate_of_weightedLogarithmicGap
    (hbarx_mem : barx ∈ P)
    (hbarU_mem : barU ∈ Ω)
    {Sk ellStar : ℝ}
    (hloggap :
      ellStar / Sk ≥
        Real.log ((ψStar ⟨barU, hbarU_mem⟩ : ℝ) / (ψ ⟨barx, hbarx_mem⟩ : ℝ))) :
    (ψ ⟨barx, hbarx_mem⟩ : ℝ) ≥
      (ψStar ⟨barU, hbarU_mem⟩ : ℝ) * Real.exp (-ellStar / Sk) := by
  let a : ℝ := ψStar ⟨barU, hbarU_mem⟩
  let b : ℝ := ψ ⟨barx, hbarx_mem⟩
  have ha : 0 < a := (ψStar ⟨barU, hbarU_mem⟩).2
  have hb : 0 < b := (ψ ⟨barx, hbarx_mem⟩).2
  have hratio : a / b ≤ Real.exp (ellStar / Sk) := by
    refine (Real.log_le_iff_le_exp (show 0 < a / b by exact div_pos ha hb)).1 ?_
    simpa [a, b] using hloggap
  have hmul : a ≤ Real.exp (ellStar / Sk) * b :=
    (div_le_iff₀ hb).1 hratio
  have hexp : 0 < Real.exp (ellStar / Sk) := Real.exp_pos _
  have hdiv : a / Real.exp (ellStar / Sk) ≤ b :=
    (div_le_iff₀ hexp).2 (by simpa [mul_comm] using hmul)
  simpa [a, b, Real.exp_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

end WeightedAverages

end
