/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Corollary_3_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open MeasureTheory

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "μ" => (Measure.addHaar : Measure E)
local notation "finDim" => Module.finrank ℝ E
local notation "δ" => 1 - 1 / (((finDim : ℝ) + 1) ^ (2 : ℕ))

attribute [local instance] Classical.decPred

/- Proposition 3.45 lies in the intrinsic finite-dimensional real normed-space
selected-feasible-index / interior-ball volume-decay domain.

Sampled owner-style declarations in the same domain:
- `Nat.count` and `feasibleSubsequence` from `Definition_3_53`, the chapter owners for the
  textbook selected feasible index `i(k)`;
- `selected_index_pos_of_volume_drop` from `Theorem_3_52`, the canonical bridge from strict
  comparison-set volume drop to positivity of that selected feasible index;
- `volume_ratio_rpow_decay_under_interior_ball_condition` from `Proposition_3_44`, the chapter's
  intrinsic bridge from interior-ball geometry and ellipsoid-style volume decay to the explicit
  exponential ratio bound;
- `Module.finrank`, the canonical owner of ambient dimension data replacing the coordinate
  parameter `n`;
- `Real.exp_lt_one_iff` and `Real.rpow_lt_one_iff'`, the canonical scalar owners that turn the
  logarithmic threshold into strict volume drop.

Best owner abstraction:
- source-facing: positivity of the canonical selected feasible index
  `Nat.count (fun j ↦ querySeq j ∈ Q) k`;
- core/canonical: `selected_index_pos_of_volume_drop` together with
  `volume_ratio_rpow_decay_under_interior_ball_condition`;
- bridge/view: the scalar threshold implication
  `(R / ρ) * exp (-k / (2 (finDim + 1)^2)) < 1`.

Primitive data:
- the finite-dimensional real normed ambient space `E` with `0 < Module.finrank ℝ E`;
- the feasible set `Q`, its radius-`ρ` interior-ball condition, and its containment in the outer
  ball `B₂(x0, R)`;
- the raw query sequence `querySeq`, the localization map `g`, the comparison set `E_k`, and the
  selected-stage Haar/Lebesgue-volume comparison with `E_k`;
- the standard ellipsoid-style ENNReal Haar/Lebesgue-volume decay bound for `E_k`;
- the logarithmic budget inequality
  `2 (Module.finrank ℝ E + 1)^2 log (R / ρ) < k`.

Derived API:
- the scalar inequality `(R / ρ) * exp (-k / (2 (finDim + 1)^2)) < 1`;
- strict Haar/Lebesgue-volume drop `μ (E_k) < μ Q`;
- positivity of the textbook selected feasible index via the canonical owner theorem
  `selected_index_pos_of_volume_drop`.

Source/core/bridge triage:
- source-facing: the positivity conclusion for `Nat.count (fun j ↦ querySeq j ∈ Q) k`;
- core/canonical: `Nat.count`, `selected_index_pos_of_volume_drop`, and
  `volume_ratio_rpow_decay_under_interior_ball_condition`;
- bridge/view: the scalar exponential-threshold lemma below.

The previous version kept this bridge pinned to the coordinate model
`E = EuclideanSpace ℝ (Fin n)` and exposed a separate finiteness binder for `volume (E_k)`. The
ambient owner from `Proposition_3_44` is already intrinsic, and the stagewise decay hypothesis is
more naturally primitive as a direct ENNReal Haar/Lebesgue-volume bound than as a real-volume
inequality plus a bookkeeping finiteness witness. This refinement separates the intrinsic
volume-drop core from the source-facing selected-index bridge: the strict-volume comparison lives
at the finite-dimensional real normed-space owner level, while the final positivity theorem
reintroduces the chapter localization family only where its inner-product-space API is genuinely
needed.
-/

/-- If `k` exceeds the logarithmic threshold `2 (d + 1)^2 log (R / ρ)`, then the scalar
exponential factor `(R / ρ) * exp (-k / (2 (d + 1)^2))` is strictly smaller than `1`. -/
theorem radiusRatio_exp_neg_lt_one_of_log_threshold
    {d k : ℕ} {ρ R : ℝ}
    (hk :
      (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log (R / ρ) < (k : ℝ)) :
    (R / ρ) * Real.exp (-((k : ℝ) / (2 * (((d : ℝ) + 1) ^ (2 : ℕ))))) < 1 := by
  by_cases hratio_pos : 0 < R / ρ
  · have hbound : Real.log (R / ρ) < (k : ℝ) / (2 * (((d : ℝ) + 1) ^ (2 : ℕ))) := by
      have hdenom_pos : 0 < 2 * (((d : ℝ) + 1) ^ (2 : ℕ)) := by
        positivity
      refine (lt_div_iff₀ hdenom_pos).2 ?_
      simpa [mul_assoc, mul_comm, mul_left_comm] using hk
    rw [← Real.exp_log hratio_pos, ← Real.exp_add]
    have hsum :
        Real.log (R / ρ) + -((k : ℝ) / (2 * (((d : ℝ) + 1) ^ (2 : ℕ)))) < 0 := by
      linarith
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using
      (Real.exp_lt_one_iff.mpr hsum)
  · have hratio_nonpos : R / ρ ≤ 0 := le_of_not_gt hratio_pos
    have hexp_pos : 0 < Real.exp (-((k : ℝ) / (2 * (((d : ℝ) + 1) ^ (2 : ℕ))))) :=
      Real.exp_pos _
    have hmul_nonpos :
        (R / ρ) * Real.exp (-((k : ℝ) / (2 * (((d : ℝ) + 1) ^ (2 : ℕ))))) ≤ 0 := by
      nlinarith
    exact lt_of_le_of_lt hmul_nonpos zero_lt_one

/-- The intrinsic volume-drop core of Proposition 3.45: in a finite-dimensional real normed space,
if `Q` satisfies the radius-`ρ` interior-ball condition, if `Q` lies in the outer ball
`B₂(x0, R)`, if `E_k` satisfies the standard ellipsoid-style stagewise volume decay, and if
`k > 2 (Module.finrank ℝ E + 1)^2 log (R / ρ)`, then `μ E_k < μ Q`. -/
theorem volume_drop_of_log_threshold_under_interior_ball_condition
    (hdim : 0 < finDim)
    {Q : Set E} {ρ : ℝ} (hQ : Q.SatisfiesInteriorBallCondition ρ)
    {Ek : Set E} {x0 : E} {R : ℝ} (k : ℕ)
    (hQ_subset : Q ⊆ Metric.closedBall x0 R)
    (hvol_decay :
      μ Ek ≤ ENNReal.ofReal (Real.rpow δ (((k * finDim : ℕ) : ℝ) / 2)) *
        μ (Metric.closedBall x0 R))
    (hk :
      (2 : ℝ) * (((finDim + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log (R / ρ) < (k : ℝ)) :
    μ Ek < μ Q := by
  rcases hQ with ⟨hρ, xBar, hball⟩
  have hQ : Q.SatisfiesInteriorBallCondition ρ := ⟨hρ, xBar, hball⟩
  have hxBar : xBar ∈ Q := hball (Metric.mem_ball_self hρ)
  have hR : 0 ≤ R := by
    have hxBar_ball : xBar ∈ Metric.closedBall x0 R := hQ_subset hxBar
    exact le_trans dist_nonneg (by simpa [Metric.mem_closedBall] using hxBar_ball)
  have hclosedBall_lt_top : μ (Metric.closedBall x0 R) < ⊤ := by
    simpa using (measure_closedBall_lt_top : μ (Metric.closedBall x0 R) < ⊤)
  have hQ_finite : μ Q ≠ ⊤ := by
    exact
      measure_ne_top_of_subset hQ_subset hclosedBall_lt_top.ne
  have hdecay_finite :
      ENNReal.ofReal (Real.rpow δ (((k * finDim : ℕ) : ℝ) / 2)) *
          μ (Metric.closedBall x0 R) ≠
        ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hclosedBall_lt_top.ne
  have hEk_finite : μ Ek ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hvol_decay hdecay_finite.lt_top)
  have hratio_decay_and_exp :=
    volume_ratio_rpow_decay_under_interior_ball_condition
      hdim hQ hR k hvol_decay
  have hratio_exp :
      Real.rpow (Measure.real μ Ek / Measure.real μ Q) (1 / (finDim : ℝ)) <
        1 := by
    refine lt_of_le_of_lt hratio_decay_and_exp.1 ?_
    exact lt_of_le_of_lt hratio_decay_and_exp.2
      (radiusRatio_exp_neg_lt_one_of_log_threshold hk)
  have hball_real_pos : 0 < Measure.real μ (Metric.ball xBar ρ) := by
    have hball_pos : 0 < μ (Metric.ball xBar ρ) :=
      Metric.measure_ball_pos μ xBar hρ
    have hball_lt_top : μ (Metric.ball xBar ρ) < ⊤ := by
      simpa using (measure_ball_lt_top : μ (Metric.ball xBar ρ) < ⊤)
    simpa [Measure.real] using
      ENNReal.toReal_pos hball_pos.ne' hball_lt_top.ne
  have hQ_pos : 0 < Measure.real μ Q := by
    exact
      lt_of_lt_of_le hball_real_pos
        (measureReal_mono hball hQ_finite)
  have hratio_lt_one : Measure.real μ Ek / Measure.real μ Q < 1 := by
    exact (Real.rpow_lt_one_iff' (by positivity) (by positivity)).1 hratio_exp
  have hEk_real_lt : Measure.real μ Ek < Measure.real μ Q := by
    exact (div_lt_one hQ_pos).1 hratio_lt_one
  exact
    (ENNReal.toReal_lt_toReal hEk_finite hQ_finite).1
      (by simpa [Measure.real] using hEk_real_lt)

section SourceFacing

variable [InnerProductSpace ℝ E]

/-- Proposition 3.45 as the source-facing selected-index bridge: let
`i(k) = Nat.count (fun j ↦ querySeq j ∈ Q) k` be the canonical selected feasible index attached to
the query sequence `querySeq`. If `Q` satisfies the radius-`ρ` interior-ball condition in a
finite-dimensional real inner-product space `E`, if `0 < Module.finrank ℝ E`, if `Q` lies in the
outer ball `B₂(x0, R)`, if the selected localization stage has volume at most `vol(E_k)`, if
`E_k` satisfies the standard ellipsoid-style stagewise volume decay, and if
`k > 2 (Module.finrank ℝ E + 1)^2 log (R / ρ)`, then `i(k) > 0`. The intrinsic normed-space core
is `volume_drop_of_log_threshold_under_interior_ball_condition`; the extra inner-product-space
assumption here comes only from the chapter owner `localizationSets`. -/
theorem selected_index_pos_of_log_threshold_under_interior_ball_condition
    (hdim : 0 < finDim)
    {Q : Set E} {ρ : ℝ} (hQ : Q.SatisfiesInteriorBallCondition ρ)
    {querySeq : ℕ → E} {g : E → E} {Ek : Set E} {x0 : E} {R : ℝ} (k : ℕ)
    (hQ_subset : Q ⊆ Metric.closedBall x0 R)
    (hstage :
      μ
          (localizationSets
            Q
            (feasibleSubsequence Q querySeq)
            (g ∘ feasibleSubsequence Q querySeq)
            (Nat.count (fun j ↦ querySeq j ∈ Q) k)) ≤
        μ Ek)
    (hvol_decay :
      μ Ek ≤ ENNReal.ofReal (Real.rpow δ (((k * finDim : ℕ) : ℝ) / 2)) *
        μ (Metric.closedBall x0 R))
    (hk :
      (2 : ℝ) * (((finDim + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log (R / ρ) < (k : ℝ)) :
    0 < Nat.count (fun j ↦ querySeq j ∈ Q) k := by
  let Ell : ℕ → Set E := fun _ ↦ Ek
  have hstage' :
      μ
          (localizationSets
            Q
            (feasibleSubsequence Q querySeq)
            (g ∘ feasibleSubsequence Q querySeq)
            (Nat.count (fun j ↦ querySeq j ∈ Q) k)) ≤
        μ (Ell k) := hstage
  have hEll_lt_Q : μ (Ell k) < μ Q := by
    simpa [Ell] using
      volume_drop_of_log_threshold_under_interior_ball_condition
        hdim hQ k hQ_subset hvol_decay hk
  exact selected_index_pos_of_volume_drop hstage' hEll_lt_Q

end SourceFacing

end
