/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped ConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 6.1 lies in the chapter's Fenchel-conjugacy / dual-norm domain.

Primary domain:
- growth bounds for the continuous-dual effective domain of a Fenchel conjugate.

Sampled owner-style declarations:
- `fenchelConjugate` in `Definition_6_1`, the chapter owner for conjugates on `Module.Dual ℝ E`;
- `fenchelConjugate_apply` in `Definition_6_1`, the owner evaluation theorem;
- `strongFenchelConjugate` in `Definition_6_1`, the continuous-dual bridge owner used in Chapter 6
  normed-space statements;
- `extendedRealEffectiveDomain` / the notation `dom` in `Definition_3_1_1_2`, the chapter owner
  for finite-value domains of `EReal`-valued functions;
- `fenchelDual` in `Chap03/Definition_3_1_2_1`, the nearby bridge/view pattern that specializes
  the same owner surface instead of rebuilding it.

Best owner abstraction:
- `strongFenchelConjugate` together with `dom`.

Primitive data:
- `f : E → ℝ`.

Derived API:
- the closed-ball containment and boundedness consequences for the continuous-dual effective
  domain of `strongFenchelConjugate`.

Source/core/bridge triage:
- source-facing: Proposition 6.1's boundedness statement for the continuous-dual finite-value
  domain of the conjugate of a real-valued function;
- core/canonical: `fenchelConjugate` and `dom`;
- bridge/view: `strongFenchelConjugate`.

This file therefore uses the reusable Chapter 6 bridge owner `strongFenchelConjugate` instead of
repeating a theorem-local `StrongDual` lambda for the continuous-dual restriction of
`fenchelConjugate`. The previous local `convexConjugate` definition duplicated the owner
`fenchelConjugate`, the previous local domain alias duplicated the chapter owner `dom`, and the
previous specialized membership wrapper duplicated `mem_extendedRealEffectiveDomain_iff`; all
three are removed here. The linear-growth conclusion itself does not use convexity,
finite-dimensionality, or a separate `0 ≤ L` witness, so the theorem surface is reduced to the
actual primitive data: a nonnegative radius `L : NNReal` and the growth bound.
-/

/-- Helper for Proposition 6.1: if a continuous dual vector has norm strictly larger than `L`,
then some unit vector evaluates strictly larger than `L` under that functional. -/
lemma exists_unit_apply_gt_of_lt_norm {s : StrongDual ℝ E} {L : NNReal}
    (hLt : (L : ℝ) < ‖s‖) :
    ∃ u : E, ‖u‖ = 1 ∧ (L : ℝ) < s u := by
  have hLt' : L < ‖s‖₊ := by
    exact_mod_cast hLt
  obtain ⟨u, hu, hsu⟩ :=
      ContinuousLinearMap.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm s hLt'
  have hu_real : ‖u‖ = 1 := by
    simpa using congrArg NNReal.toReal hu
  have hsu_real : (L : ℝ) < ‖s u‖ := by
    exact_mod_cast hsu
  -- Normalize the sign so the witness has positive evaluation rather than merely large absolute
  -- value.
  by_cases hnonneg : 0 ≤ s u
  · refine ⟨u, hu_real, ?_⟩
    simpa [Real.norm_of_nonneg hnonneg] using hsu_real
  · have hneg : s u < 0 := lt_of_not_ge hnonneg
    refine ⟨-u, by simpa [norm_neg] using hu_real, ?_⟩
    have hneg_eval : (L : ℝ) < -s u := by
      simpa [Real.norm_of_nonpos hneg.le] using hsu_real
    simpa using hneg_eval

/-- Helper for Proposition 6.1: along a unit ray, the Fenchel maximand is bounded below by the
linear function with slope `s u - L`. -/
lemma fenchel_maximand_nat_smul_lower_bound
    (f : E → ℝ) (L : NNReal) (hgrowth : ∀ x : E, f x ≤ f 0 + (L : ℝ) * ‖x‖)
    {s : StrongDual ℝ E} {u : E} (hu : ‖u‖ = 1) (n : ℕ) :
    ((n : ℝ) * (s u - L) - f 0) ≤ s ((n : ℝ) • u) - f ((n : ℝ) • u) := by
  -- The growth bound turns `f ((n : ℝ) • u)` into an affine upper bound in `n`.
  have hnorm : ‖((n : ℝ) • u : E)‖ = (n : ℝ) := by
    rw [norm_smul, hu, Real.norm_of_nonneg (by positivity), mul_one]
  have hgrowth' : f ((n : ℝ) • u) ≤ f 0 + (n : ℝ) * (L : ℝ) := by
    simpa [hnorm, mul_comm, mul_left_comm, mul_assoc] using hgrowth ((n : ℝ) • u)
  -- Linearity identifies the dual pairing along the ray with scalar multiplication by `n`.
  have hsmap : s ((n : ℝ) • u) = (n : ℝ) * s u := by
    simp
  rw [hsmap]
  linarith

/-- Helper for Proposition 6.1: if some unit vector evaluates above the radius `L`, then the
continuous-dual Fenchel conjugate is infinite at that functional. -/
lemma strongFenchelConjugate_eq_top_of_unit_apply_gt_radius
    (f : E → ℝ) (L : NNReal) (hgrowth : ∀ x : E, f x ≤ f 0 + (L : ℝ) * ‖x‖)
    {s : StrongDual ℝ E} {u : E} (hu : ‖u‖ = 1) (hsu : (L : ℝ) < s u) :
    strongFenchelConjugate f s = ⊤ := by
  apply le_antisymm le_top
  -- It suffices to show that every real number lies below the defining supremum.
  refine (EReal.ge_of_forall_gt_iff_ge).1 ?_
  intro z hz
  have hslope : 0 < s u - L := by
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((z + f 0) / (s u - L))
  have hn' : ((z + f 0) / (s u - L)) < (n : ℝ) := by
    exact_mod_cast hn
  have hlarge : z < (n : ℝ) * (s u - L) - f 0 := by
    have hmul : z + f 0 < (n : ℝ) * (s u - L) := by
      exact (div_lt_iff₀ hslope).mp hn'
    linarith
  have hbound : ((n : ℝ) * (s u - L) - f 0) ≤ s ((n : ℝ) • u) - f ((n : ℝ) • u) :=
    fenchel_maximand_nat_smul_lower_bound f L hgrowth (s := s) (u := u) hu n
  change (z : EReal) ≤ ⨆ x : E, (s x : EReal) - (f x : EReal)
  refine le_iSup_of_le ((n : ℝ) • u) ?_
  have hreal : z ≤ s ((n : ℝ) • u) - f ((n : ℝ) • u) :=
    (lt_of_lt_of_le hlarge hbound).le
  have hereal :
      (z : EReal) ≤ (((s ((n : ℝ) • u) - f ((n : ℝ) • u)) : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa using hereal

-- Proof sketch: if `‖s‖ > L`, choose `u` in the unit ball with `s u > L`; then along the ray
-- `t • u` the maximand `s (t • u) - f (t • u)` is bounded below by
-- `t * (s u - L) - f 0`, which diverges to `+∞`, so `s` cannot lie in the finite-value domain.
/-- Proposition 6.1: if a real-valued function is bounded above by `f 0 + L ‖x‖`, then the
finite-value domain of its Fenchel conjugate on the continuous dual is contained in the closed
dual ball of radius `L`. -/
theorem dom_fenchelConjugate_subset_closedBall_of_upper_linear_growth
    (f : E → ℝ) (L : NNReal) (hgrowth : ∀ x : E, f x ≤ f 0 + (L : ℝ) * ‖x‖) :
    dom (strongFenchelConjugate f) ⊆ closedBall 0 L := by
  intro s hs
  rw [mem_closedBall_zero_iff]
  by_contra hs_out
  have hs_fin : strongFenchelConjugate f s ≠ ⊤ ∧ strongFenchelConjugate f s ≠ ⊥ :=
    mem_extendedRealEffectiveDomain_iff.mp hs
  -- A norm gap above `L` produces a unit ray on which the maximand has positive slope.
  have hLt : (L : ℝ) < ‖s‖ := lt_of_not_ge hs_out
  obtain ⟨u, hu, hsu⟩ := exists_unit_apply_gt_of_lt_norm (s := s) (L := L) hLt
  have htop : strongFenchelConjugate f s = ⊤ :=
    strongFenchelConjugate_eq_top_of_unit_apply_gt_radius f L hgrowth hu hsu
  exact hs_fin.1 htop

/-- The finite-value domain of the conjugate is bounded under the same upper linear-growth
hypothesis. -/
-- Proof sketch: apply the closed-ball containment theorem and `Metric.isBounded_closedBall`.
theorem dom_fenchelConjugate_bounded_of_upper_linear_growth
    (f : E → ℝ) (L : NNReal) (hgrowth : ∀ x : E, f x ≤ f 0 + (L : ℝ) * ‖x‖) :
    Bornology.IsBounded (dom (strongFenchelConjugate f)) := by
  -- The previous theorem places the domain inside a closed ball, and closed balls are bounded.
  exact Metric.isBounded_closedBall.subset
    (dom_fenchelConjugate_subset_closedBall_of_upper_linear_growth f L hgrowth)

end
