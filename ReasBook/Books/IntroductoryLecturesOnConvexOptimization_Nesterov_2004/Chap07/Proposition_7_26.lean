/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {Q : Type u}

/- Proposition 7.26 lies in Chapter 7's relative-accuracy / stagewise gap-conversion domain.

Sampled owner-style declarations:
- `IsRelativeAccuracy` in `Definition_7_1`, the chapter owner for two-sided relative accuracy;
- `subgradient_approximation_scheme_value_le_one_add_delta_mul_optimal_value` in `Theorem_7_2`,
  the sibling one-shot conversion from a stagewise gap bound to a `(1 + δ) fStar` upper bound;
- `direct_structure_iterate_value_le_one_add_delta_mul_optimal_value` in `Theorem_7_4`, the same
  owner-level conversion pattern for a different coefficient profile;
- `iterativeSmoothing_outputPoint_value_le` in `Theorem_7_11`, showing the local chapter style:
  the one-sided upper bound is source-facing, while `IsRelativeAccuracy` is a companion bridge
  once the lower bound is available.

Best owner abstraction:
- source-facing: Proposition 7.26's one-sided value estimate
  `f_p (x_k) ≤ (1 + δ) f_p^*` at an iteration index satisfying the explicit lower bound;
- core/canonical: `IsRelativeAccuracy fStar δ (f_p (x k))`;
- bridge/view: the passage from the explicit coefficient
  `16 (1 + δ) r log r / (δ k (k + 1))` to `δ`.

Primitive data:
- the objective `f_p`, iterate sequence `x`, and scalars `δ`, `r`, `fStar`;
- the stagewise gap estimate;
- the explicit lower bound on the chosen index `k`;
- the nonnegativity of `fStar`, which is exactly what the one-sided upper bound uses.

Derived API:
- the source-facing upper bound below;
- the companion `IsRelativeAccuracy` statement obtained by supplying the missing lower bound
  `fStar ≤ f_p (x k)` and the stronger positivity input needed by the chapter owner.

Source/core/bridge triage:
- source-facing: `fp_relative_accuracy_of_iteration_gap_bound`;
- core/canonical: `IsRelativeAccuracy`;
- bridge/view: `fp_iterate_isRelativeAccuracy_of_iteration_gap_bound`.

The main theorem remains the source-facing upper bound because the current proposition does not
assume the lower inequality `fStar ≤ f_p (x k)`. Replacing it by `IsRelativeAccuracy` would change
the source semantics. The canonical owner is therefore added only as the minimal companion bridge.
-/

-- Proof sketch: for the chosen iterate `k`, rewrite the assumed gap estimate as
-- `f_p (x k) ≤ (1 + C_k) fStar` with
-- `C_k = 16 (1 + δ) r log r / (δ k (k + 1))`. The lower bound on `k` implies
-- `k (k + 1) ≥ k^2 ≥ 16 (1 + δ) r log r / δ^2`, so `C_k ≤ δ`. Substituting this into the
-- previous inequality and using `0 ≤ fStar` gives `f_p (x k) ≤ (1 + δ) fStar`.
/-- Proposition 7.26: if the iterates `x_k` satisfy the displayed gap estimate
`f_p(x_k) - f_p^* ≤ 16 (1 + δ) r log r / (δ k (k + 1)) * f_p^*`, `f_p^*` is nonnegative, and
every iterate with
`k ≥ (4 / δ) * sqrt ((1 + δ) r log r)` satisfies the relative-accuracy bound
`f_p(x_k) ≤ (1 + δ) f_p^*`. -/
theorem fp_relative_accuracy_of_iteration_gap_bound
    (f_p : Q → ℝ) (δ r fStar : ℝ) (x : ℕ → Q) {k : ℕ}
    (hδ : 0 < δ) (hr : 1 < r) (hfStar_nonneg : 0 ≤ fStar)
    (hgap :
      ∀ n : ℕ,
        1 ≤ n →
          f_p (x n) - fStar ≤
            ((16 : ℝ) * (1 + δ) * r * Real.log r) / (δ * (n : ℝ) * (n + 1)) * fStar)
    (hk : (4 / δ) * Real.sqrt ((1 + δ) * r * Real.log r) ≤ (k : ℝ)) :
    f_p (x k) ≤ (1 + δ) * fStar := by
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
  have hOne_add_δ_pos : 0 < 1 + δ := by linarith
  have hr_pos : 0 < r := lt_trans zero_lt_one hr
  have hlogr_pos : 0 < Real.log r := Real.log_pos hr
  set A : ℝ := (1 + δ) * r * Real.log r
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hsqrt_pos : 0 < Real.sqrt A := by
    apply Real.sqrt_pos.2
    have hA_pos : 0 < A := by
      dsimp [A]
      positivity
    exact hA_pos
  have hleft_pos : 0 < (4 / δ) * Real.sqrt A := by
    positivity
  have hk_pos : 0 < (k : ℝ) := lt_of_lt_of_le hleft_pos hk
  have hk_nat_pos : 1 ≤ k := Nat.succ_le_of_lt (Nat.cast_pos.mp hk_pos)
  have hgapk := hgap k hk_nat_pos
  have hscaled :
      4 * Real.sqrt A ≤ δ * (k : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hk hδ_nonneg
    have hδ_ne : δ ≠ 0 := ne_of_gt hδ
    simpa [A, div_eq_mul_inv, hδ_ne, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hmain :
      (16 : ℝ) * A ≤ δ ^ (2 : ℕ) * (k : ℝ) ^ (2 : ℕ) := by
    have hsq :
        (4 * Real.sqrt A) ^ (2 : ℕ) ≤ (δ * (k : ℝ)) ^ (2 : ℕ) := by
      nlinarith [hscaled]
    nlinarith [hsq, Real.sq_sqrt hA_nonneg]
  have hk_sq_le :
      (k : ℝ) ^ (2 : ℕ) ≤ (k : ℝ) * (k + 1) := by
    nlinarith [show 0 ≤ (k : ℝ) by positivity]
  have hmain' :
      (16 : ℝ) * A ≤ δ ^ (2 : ℕ) * ((k : ℝ) * (k + 1)) := by
    exact hmain.trans <| by
      gcongr
  have hden_pos : 0 < δ * (k : ℝ) * (k + 1) := by
    positivity
  have hcoeff_le :
      ((16 : ℝ) * (1 + δ) * r * Real.log r) / (δ * (k : ℝ) * (k + 1)) ≤ δ := by
    apply (div_le_iff₀ hden_pos).2
    simpa [A, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmain'
  have hcoeff_mul_le :
      (((16 : ℝ) * (1 + δ) * r * Real.log r) / (δ * (k : ℝ) * (k + 1))) * fStar ≤
        δ * fStar := by
    exact mul_le_mul_of_nonneg_right hcoeff_le hfStar_nonneg
  calc
    f_p (x k) = (f_p (x k) - fStar) + fStar := by ring
    _ ≤
        (((16 : ℝ) * (1 + δ) * r * Real.log r) / (δ * (k : ℝ) * (k + 1))) * fStar + fStar := by
      linarith
    _ ≤ δ * fStar + fStar := by
      gcongr
    _ = (1 + δ) * fStar := by ring

/-- Proposition 7.26 upgrades to the chapter owner `IsRelativeAccuracy` once the missing lower
bound `f_p^* ≤ f_p(x_k)` is supplied explicitly. -/
theorem fp_iterate_isRelativeAccuracy_of_iteration_gap_bound
    (f_p : Q → ℝ) (δ r fStar : ℝ) (x : ℕ → Q) {k : ℕ}
    (hδ : 0 < δ) (hr : 1 < r) (hfStar_pos : 0 < fStar)
    (hgap :
      ∀ n : ℕ,
        1 ≤ n →
          f_p (x n) - fStar ≤
            ((16 : ℝ) * (1 + δ) * r * Real.log r) / (δ * (n : ℝ) * (n + 1)) * fStar)
    (hk : (4 / δ) * Real.sqrt ((1 + δ) * r * Real.log r) ≤ (k : ℝ))
    (hfStar_le : fStar ≤ f_p (x k)) :
    IsRelativeAccuracy fStar δ (f_p (x k)) := by
  refine ⟨hfStar_pos, hfStar_le, ?_⟩
  exact
    fp_relative_accuracy_of_iteration_gap_bound f_p δ r fStar x hδ hr
      (le_of_lt hfStar_pos) hgap hk

end
