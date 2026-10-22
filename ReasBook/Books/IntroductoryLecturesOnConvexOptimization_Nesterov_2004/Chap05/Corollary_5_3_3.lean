/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Corollary 5.3.3 lies in the Chapter 5 self-concordant-barrier / segment-growth domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the barrier owner;
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` from `Lemma_5_3_1`, the owner-level
  concavity theorem for the exponential transform;
* `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` from the same file, the canonical
  positive-parameter bridge to the textbook transform `x ↦ exp (-(F x / ν))`;
* mathlib `ConcaveOn` on convex combinations, the canonical segment-evaluation API.

Best owner abstraction:
* `IsSelfConcordantBarrierOnWith.segment_upper_bound_log_one_sub`.

Primitive data:
* the barrier owner `hF : IsSelfConcordantBarrierOnWith dom ν F`;
* points `x, y ∈ dom`;
* a segment parameter `α ∈ [0, 1)`.

Derived API:
* concavity of the barrier exponential transform on `dom`;
* the displayed logarithmic upper bound along the segment.

Source/core/bridge triage:
* source-facing: the textbook upper bound along the segment from `x` to `y`;
* core/canonical: the owner `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: the exponential-transform concavity bridge from `Lemma_5_3_1`.

This corollary carries genuine source-facing content, so it should not be collapsed into a
recall-only item. Its proof route should nevertheless stay owner-based: the segment bound is a
thin corollary of the existing concavity owner theorem, not a second standalone derivation. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: use the owner theorem
-- `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` to make
-- `x ↦ exp (-(F x / p))` concave on `dom`, with `p = ν` when `ν > 0` and `p = 1` when `ν = 0`.
-- Evaluate concavity on the convex combination `(1 - α) • x + α • y = x + α • (y - x)`, drop the
-- nonnegative `α`-endpoint term, take logarithms, and rearrange. In the degenerate case `ν = 0`,
-- the same concavity argument with `p = 1` still yields the stronger monotonicity bound
-- `F (x + α • (y - x)) ≤ F x`, because `log (1 - α) ≤ 0`.
/-- Corollary 5.3.3: along the segment from `x` to `y` inside the domain of a
`ν`-self-concordant barrier, the barrier value at `x + α • (y - x)` is bounded above by
`F x - ν log (1 - α)` for every `α ∈ [0, 1)`. -/
theorem segment_upper_bound_log_one_sub
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    F (x + α • (y - x)) ≤ F x - (ν : ℝ) * Real.log (1 - α) := by
  rcases hα with ⟨hα0, hα1⟩
  by_cases hαzero : α = 0
  · subst hαzero
    simp
  set z : E := x + α • (y - x)
  have hz_eq : z = (1 - α) • x + α • y := by
    dsimp [z]
    rw [smul_sub]
    rw [show (1 - α : ℝ) • x = x - α • x by rw [sub_smul, one_smul]]
    abel
  have hαpos : 0 < α := by
    have h0α : 0 ≠ α := by
      simpa [eq_comm] using hαzero
    exact lt_of_le_of_ne hα0 h0α
  have h1α_nonneg : 0 ≤ 1 - α := by linarith
  have h1α_pos : 0 < 1 - α := by linarith
  have hab : (1 - α) + α = 1 := by ring
  have segment_upper_bound_of_posParameter
      {p : ℝ} (hp : 0 < p)
      (hconc : ConcaveOn ℝ dom (fun w ↦ Real.exp (-(F w / p)))) :
      F z ≤ F x - p * Real.log (1 - α) := by
    have hsegment := hconc.2 hx hy h1α_nonneg hα0 hab
    have hleft :
        (1 - α) * Real.exp (-(F x / p)) ≤ Real.exp (-(F z / p)) := by
      calc
        (1 - α) * Real.exp (-(F x / p)) ≤
            (1 - α) * Real.exp (-(F x / p)) + α * Real.exp (-(F y / p)) := by
          nlinarith [hα0, Real.exp_pos (-(F y / p))]
        _ ≤ Real.exp (-(F z / p)) := by
          simpa [hz_eq] using hsegment
    have hlog :
        Real.log ((1 - α) * Real.exp (-(F x / p))) ≤ -(F z / p) := by
      simpa using Real.log_le_log (mul_pos h1α_pos (Real.exp_pos _)) hleft
    rw [Real.log_mul h1α_pos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hfrac : F z / p + Real.log (1 - α) ≤ F x / p := by
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hfrac hp.le
    have hp_ne : p ≠ 0 := by linarith
    field_simp [hp_ne] at hscaled
    linarith
  have segment_upper_bound_of_unitParameter
      {p : NNRealˣ}
      (hconc : ConcaveOn ℝ dom (barrierExponentialTransform p F)) :
      F z ≤ F x - (p : ℝ) * Real.log (1 - α) := by
    have hsegment := hconc.2 hx hy h1α_nonneg hα0 hab
    have hleft :
        (1 - α) * Real.exp (-F x / (p : ℝ)) ≤ Real.exp (-F z / (p : ℝ)) := by
      calc
        (1 - α) * Real.exp (-F x / (p : ℝ)) ≤
            (1 - α) * Real.exp (-F x / (p : ℝ)) +
              α * Real.exp (-F y / (p : ℝ)) := by
          nlinarith [hα0, Real.exp_pos (-F y / (p : ℝ))]
        _ ≤ Real.exp (-F z / (p : ℝ)) := by
          simpa [barrierExponentialTransform, hz_eq] using hsegment
    have hlog :
        Real.log ((1 - α) * Real.exp (-F x / (p : ℝ))) ≤ -F z / (p : ℝ) := by
      simpa using Real.log_le_log (mul_pos h1α_pos (Real.exp_pos _)) hleft
    rw [Real.log_mul h1α_pos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
    have hp_ne : (p : ℝ) ≠ 0 := by
      exact_mod_cast Units.ne_zero p
    have hp_pos : 0 < (p : ℝ) := lt_of_le_of_ne hp_nonneg (by simp [eq_comm, hp_ne])
    have hscaled := mul_le_mul_of_nonneg_left hlog hp_pos.le
    field_simp [hp_ne] at hscaled
    linarith
  by_cases hν : ν = 0
  · have hlog_neg : Real.log (1 - α) < 0 := by
      exact Real.log_neg h1α_pos (by linarith)
    by_contra hz_gt
    have hz_gt' : F x < F z := by
      simpa [hν] using hz_gt
    let p0 : ℝ := (F z - F x) / (-(2 * Real.log (1 - α)))
    have hp0_pos : 0 < p0 := by
      have hden_pos : 0 < -(2 * Real.log (1 - α)) := by
        nlinarith
      exact div_pos (by linarith) hden_pos
    have hpNN_ne : (⟨p0, le_of_lt hp0_pos⟩ : NNReal) ≠ 0 := by
      simpa using hp0_pos.ne'
    let p : NNRealˣ := Units.mk0 (⟨p0, le_of_lt hp0_pos⟩ : NNReal) hpNN_ne
    have hconc :
        ConcaveOn ℝ dom (barrierExponentialTransform p F) :=
      hF.concaveOn_exp_neg_div (by simp [hν])
    have hp_eq : (((p : NNReal) : ℝ)) = p0 := by
      change (((⟨p0, le_of_lt hp0_pos⟩ : NNReal) : ℝ)) = p0
      rfl
    have hz_le'' : F z ≤ F x - (p : ℝ) * Real.log (1 - α) := by
      exact segment_upper_bound_of_unitParameter hconc
    have hden_ne : -(2 * Real.log (1 - α)) ≠ 0 := by
      nlinarith [hlog_neg.ne]
    have hlog_ne : Real.log (1 - α) ≠ 0 := by
      linarith [hlog_neg.ne]
    have hfx : F x - p0 * Real.log (1 - α) = F x + (F z - F x) / 2 := by
      dsimp [p0]
      field_simp [hlog_ne]
      ring
    have hz_half : F z ≤ F x + (F z - F x) / 2 := by
      simpa [hp_eq, hfx] using hz_le''
    linarith
  · have hνpos : 0 < (ν : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hν)
    have hconc :
        ConcaveOn ℝ dom (fun w ↦ Real.exp (-(F w / (ν : ℝ)))) :=
      (isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div
        hF.toIsStandardSelfConcordantOn hνpos).1 hF
    have hz_le : F z ≤ F x - (ν : ℝ) * Real.log (1 - α) :=
      segment_upper_bound_of_posParameter hνpos hconc
    simpa [z] using hz_le

end IsSelfConcordantBarrierOnWith

end
