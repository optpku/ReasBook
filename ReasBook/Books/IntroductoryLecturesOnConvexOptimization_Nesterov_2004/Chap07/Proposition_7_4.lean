/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Asymptotics
open Filter

local notation "DimPair" => ℕ × ℕ

/- Proposition 7.4 lies in the chapter's support-function smoothing / one-step work asymptotics
domain.

Sampled owner-style declarations:
- `SupportFunctionSmoothingMethod` in `Algorithm_7_3`, the chapter owner of Method `S_N(R)`;
- mathlib `Asymptotics.IsBigO`, the canonical asymptotic owner behind `f =O[l] g`;
- `restrictedDimensionFilter` in `Proposition_7_6.lean`, the chapter owner of the admissible
  dimension regime `0 < p < n (n + 1) / 2` with `n → ∞`;
- `frobeniusGramPreliminaryArithmeticWorkBound` in `Proposition_7_5.lean`, the nearby
  source-facing work owner for the Frobenius-Gram subroutine that contributes to one step of the
  method.

Best owner abstraction:
- source-facing: the direct one-step work profile
  `(n, p) ↦ gradientWork (n, p) + projectionWork (n, p) + auxiliaryWork (n, p)`;
- core/canonical: `Asymptotics.IsBigO` on `restrictedDimensionFilter`;
- bridge/view: none beyond reading the source prose as the sum of its three component costs.

Primitive data:
- the three component cost profiles for one step of the method.

Derived API:
- the final `=O` bound by `n^2 (n + p)` on the chapter's restricted-dimension filter.

There is no genuine upstream owner in this chapter for the arithmetic work of one Algorithm 7.3
iteration. The previous version introduced a namespace-packaged alias for the sum of three
arbitrary profiles, but that alias carried no additional method data and violated the no-wrapper
rule. This refinement therefore keeps the proposition directly on the source-facing sum profile
while still reusing the canonical filter owner `restrictedDimensionFilter` from Proposition 7.6.
-/

-- Proof sketch: add the three assumed `O`-bounds for the gradient, projection, and auxiliary
-- vector computations. On the restricted regime `p < n (n + 1) / 2`, the quadratic term `p^2`
-- is absorbed by `n^3 + n^2 p`, and `n^3 + n^2 p = n^2 (n + p)`.
/-- Helper for Proposition 7.4: the mixed gradient/projection source profile `p n^2 + n^3` is
dominated by the target scale `n^2 (n + p)`. -/
lemma mixed_gradient_projection_profile_isBigO_target :
    (fun dims : DimPair ↦
      (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) + (dims.1 : ℝ) ^ (3 : ℕ)) =O[
        restrictedDimensionFilter]
      (fun dims ↦ (dims.1 : ℝ) ^ (2 : ℕ) * ((dims.1 : ℝ) + dims.2)) := by
  -- Bound both nonnegative summands by the target profile and absorb the factor `2` into `O`.
  refine IsBigO.of_bound 2 <| Filter.Eventually.of_forall fun dims ↦ ?_
  have hn : 0 ≤ (dims.1 : ℝ) := by
    positivity
  have hp : 0 ≤ (dims.2 : ℝ) := by
    positivity
  have hmixed_nonneg :
      0 ≤ (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) + (dims.1 : ℝ) ^ (3 : ℕ) := by
    positivity
  have hsum_nonneg : 0 ≤ (dims.1 : ℝ) + dims.2 := by
    positivity
  have hbound :
      (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) + (dims.1 : ℝ) ^ (3 : ℕ) ≤
        2 * ((dims.1 : ℝ) ^ (2 : ℕ) * ((dims.1 : ℝ) + dims.2)) := by
    nlinarith
  simpa [Real.norm_eq_abs, abs_of_nonneg, hn, hp, hmixed_nonneg, hsum_nonneg] using hbound

/-- Helper for Proposition 7.4: on the restricted-dimension regime, the auxiliary quadratic
profile `p^2` is also dominated by `n^2 (n + p)`. -/
lemma auxiliary_profile_isBigO_target :
    (fun dims : DimPair ↦ (dims.2 : ℝ) ^ (2 : ℕ)) =O[restrictedDimensionFilter]
      (fun dims ↦ (dims.1 : ℝ) ^ (2 : ℕ) * ((dims.1 : ℝ) + dims.2)) := by
  -- Extract the regime `0 < p < n (n + 1) / 2` from the principal part of the filter.
  refine IsBigO.of_bound 1 ?_
  have hp_nat : ∀ᶠ dims in restrictedDimensionFilter, 0 < dims.2 := by
    rw [restrictedDimensionFilter, Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall fun _dims hmem ↦ hmem.1
  have hlt_nat : ∀ᶠ dims in restrictedDimensionFilter, dims.2 < dims.1 * (dims.1 + 1) / 2 := by
    rw [restrictedDimensionFilter, Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall fun _dims hmem ↦ hmem.2
  filter_upwards [hp_nat, hlt_nat] with dims hp_nat hlt_nat
  have hn : 0 ≤ (dims.1 : ℝ) := by
    positivity
  have hp : 0 < (dims.2 : ℝ) := by
    exact_mod_cast hp_nat
  have hlt_cast :
      (dims.2 : ℝ) < (((dims.1 * (dims.1 + 1) / 2 : ℕ) : ℝ)) := by
    exact_mod_cast hlt_nat
  have hlt :
      (dims.2 : ℝ) < (dims.1 : ℝ) * ((dims.1 : ℝ) + 1) / 2 := by
    refine lt_of_lt_of_le hlt_cast ?_
    calc
      (((dims.1 * (dims.1 + 1) / 2 : ℕ) : ℝ)) ≤ (((dims.1 * (dims.1 + 1) : ℕ) : ℝ) / 2) := by
        exact Nat.cast_div_le (α := ℝ) (m := dims.1 * (dims.1 + 1)) (n := 2)
      _ = (dims.1 : ℝ) * ((dims.1 : ℝ) + 1) / 2 := by
        norm_num [Nat.cast_add, Nat.cast_mul]
  -- First show `n ≥ 1`, then deduce `p ≤ n^2`, and finally absorb `p^2` into `n^2 (n + p)`.
  have hn_pos_nat : 0 < dims.1 := by
    have hn_pos : 0 < (dims.1 : ℝ) := by
      nlinarith
    exact_mod_cast hn_pos
  have hn_one : 1 ≤ (dims.1 : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hp_le_nsq : (dims.2 : ℝ) ≤ (dims.1 : ℝ) ^ (2 : ℕ) := by
    nlinarith
  have hsum_nonneg : 0 ≤ (dims.1 : ℝ) + dims.2 := by
    positivity
  have hbound :
      (dims.2 : ℝ) ^ (2 : ℕ) ≤ (dims.1 : ℝ) ^ (2 : ℕ) * ((dims.1 : ℝ) + dims.2) := by
    nlinarith
  simpa [Real.norm_eq_abs, abs_of_nonneg, hn, le_of_lt hp, hsum_nonneg] using hbound

/-- Helper for Proposition 7.4: the full explicit one-step source profile is dominated by the
target scale `n^2 (n + p)`. -/
lemma explicit_iteration_profile_isBigO_target :
    (fun dims : DimPair ↦
      (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) +
        (dims.1 : ℝ) ^ (3 : ℕ) + (dims.2 : ℝ) ^ (2 : ℕ)) =O[
          restrictedDimensionFilter]
      (fun dims ↦ (dims.1 : ℝ) ^ (2 : ℕ) * ((dims.1 : ℝ) + dims.2)) := by
  -- Add the mixed `p n^2 + n^3` bound to the restricted-dimension control of `p^2`.
  simpa [Pi.add_apply, add_assoc] using
    mixed_gradient_projection_profile_isBigO_target.add auxiliary_profile_isBigO_target

/-- Proposition 7.4: along the restricted-dimension regime where `n → ∞` and
`0 < p < n (n + 1) / 2`, if one iteration of Method `S_N(R)` has gradient work
`O(p n^2)`, Frobenius-projection work `O(n^3)`, and auxiliary `ℝ^p` arithmetic work `O(p^2)`,
then the total one-step arithmetic work, obtained by summing those three component profiles, is
`O(n^2 (n + p))`. -/
theorem supportFunctionSmoothingIterationWork_isBigO_n_sq_mul_n_add_p
    (gradientWork projectionWork auxiliaryWork : DimPair → ℝ)
    (hgradient : gradientWork =O[restrictedDimensionFilter]
      (fun dims ↦ (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ)))
    (hprojection : projectionWork =O[restrictedDimensionFilter]
      (fun dims ↦ (dims.1 : ℝ) ^ (3 : ℕ)))
    (hauxiliary : auxiliaryWork =O[restrictedDimensionFilter]
      (fun dims ↦ (dims.2 : ℝ) ^ (2 : ℕ))) :
    (fun dims ↦ gradientWork dims + projectionWork dims + auxiliaryWork dims) =O[
      restrictedDimensionFilter]
      (fun dims ↦ (dims.1 : ℝ) ^ (2 : ℕ) * ((dims.1 : ℝ) + dims.2)) := by
  -- First rewrite each assumed component bound against the explicit source work profile.
  have hgradient_explicit :
      gradientWork =O[restrictedDimensionFilter]
        (fun dims : DimPair ↦
          (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) +
            (dims.1 : ℝ) ^ (3 : ℕ) + (dims.2 : ℝ) ^ (2 : ℕ)) := by
    refine hgradient.trans ?_
    refine IsBigO.of_bound 1 <| Filter.Eventually.of_forall fun dims ↦ ?_
    have hn : 0 ≤ (dims.1 : ℝ) := by
      positivity
    have hp : 0 ≤ (dims.2 : ℝ) := by
      positivity
    have hexplicit_nonneg :
        0 ≤ (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) +
          ((dims.1 : ℝ) ^ (3 : ℕ) + (dims.2 : ℝ) ^ (2 : ℕ)) := by
      positivity
    have hbound :
        (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) ≤
          (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) +
            ((dims.1 : ℝ) ^ (3 : ℕ) + (dims.2 : ℝ) ^ (2 : ℕ)) := by
      nlinarith
    simpa [Real.norm_eq_abs, abs_of_nonneg, hn, hp, hexplicit_nonneg, add_assoc] using hbound
  have hprojection_explicit :
      projectionWork =O[restrictedDimensionFilter]
        (fun dims : DimPair ↦
          (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) +
            (dims.1 : ℝ) ^ (3 : ℕ) + (dims.2 : ℝ) ^ (2 : ℕ)) := by
    refine hprojection.trans ?_
    refine IsBigO.of_bound 1 <| Filter.Eventually.of_forall fun dims ↦ ?_
    have hn : 0 ≤ (dims.1 : ℝ) := by
      positivity
    have hp : 0 ≤ (dims.2 : ℝ) := by
      positivity
    have hexplicit_nonneg :
        0 ≤ (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) +
          ((dims.1 : ℝ) ^ (3 : ℕ) + (dims.2 : ℝ) ^ (2 : ℕ)) := by
      positivity
    have hbound :
        (dims.1 : ℝ) ^ (3 : ℕ) ≤
          (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) +
            ((dims.1 : ℝ) ^ (3 : ℕ) + (dims.2 : ℝ) ^ (2 : ℕ)) := by
      nlinarith
    simpa [Real.norm_eq_abs, abs_of_nonneg, hn, hp, hexplicit_nonneg, add_assoc] using hbound
  have hauxiliary_explicit :
      auxiliaryWork =O[restrictedDimensionFilter]
        (fun dims : DimPair ↦
          (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) +
            (dims.1 : ℝ) ^ (3 : ℕ) + (dims.2 : ℝ) ^ (2 : ℕ)) := by
    refine hauxiliary.trans ?_
    refine IsBigO.of_bound 1 <| Filter.Eventually.of_forall fun dims ↦ ?_
    have hn : 0 ≤ (dims.1 : ℝ) := by
      positivity
    have hp : 0 ≤ (dims.2 : ℝ) := by
      positivity
    have hexplicit_nonneg :
        0 ≤ (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) +
          ((dims.1 : ℝ) ^ (3 : ℕ) + (dims.2 : ℝ) ^ (2 : ℕ)) := by
      positivity
    have hbound :
        (dims.2 : ℝ) ^ (2 : ℕ) ≤
          (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ) +
            ((dims.1 : ℝ) ^ (3 : ℕ) + (dims.2 : ℝ) ^ (2 : ℕ)) := by
      nlinarith
    simpa [Real.norm_eq_abs, abs_of_nonneg, hn, hp, hexplicit_nonneg, add_assoc] using hbound
  -- Now add the three source components and absorb the resulting explicit profile.
  exact ((hgradient_explicit.add hprojection_explicit).add hauxiliary_explicit).trans
    explicit_iteration_profile_isBigO_target

end
