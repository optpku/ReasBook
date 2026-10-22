/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_41
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_14
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_21
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_22
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_23

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-- The nonnegative multiplier function `λ : Fin m → ℝ≥0` viewed as the corresponding Euclidean
multiplier vector in `ℝ^m`. -/
def dual_projected_subgradient_multiplier_vector (lam : Fin m → NNReal) : Λ :=
  WithLp.toLp 2 (fun i ↦ (lam i : ℝ))

-- Proof sketch: unfold `dual_projected_subgradient_multiplier_vector`; the `i`-th coordinate is
-- definitionally the real coercion of the `i`-th nonnegative multiplier coordinate.
/-- Evaluating `dual_projected_subgradient_multiplier_vector lam` at `i` returns the real value of
the `i`-th multiplier coordinate. -/
@[simp] theorem dual_projected_subgradient_multiplier_vector_apply
    (lam : Fin m → NNReal) (i : Fin m) :
    dual_projected_subgradient_multiplier_vector lam i = (lam i : ℝ) := by
  rfl

section

variable {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {fOpt L ρ : ℝ}
variable (xSel : (Fin m → NNReal) → {x // x ∈ X}) (γ : ℕ → ℝ) (lam0 : Fin m → NNReal)

local notation "lamSeq" =>
  dual_projected_subgradient_method X g xSel γ lam0

local notation "xSeq" =>
  dual_projected_subgradient_primal_iterate X g xSel γ lam0

local notation "constraintSeq" =>
  fun n ↦ dual_projected_subgradient_constraint_vector g (xSeq n : E)

local notation "lamVecSeq" =>
  fun n ↦ dual_projected_subgradient_multiplier_vector (lamSeq n)

local notation "gVec" => fun x i ↦ g i x

/-- The full-history averaged primal iterate from Lemma 8.45. When every constraint vector in the
window `0, …, k` is nonzero, it uses the textbook normalized weights `γ_n / ‖g(x^n)‖₂`. If the
window contains a zero-constraint iterate, the repaired owner falls back to the current iterate
`x^k` rather than silently deleting those indices via Lean's totalized division. -/
def dual_projected_subgradient_full_average_iterate (k : ℕ) : E :=
  if ∃ n : Fin (k + 1), constraintSeq n = 0 then
    (xSeq k : E)
  else
    let denom := ∑ j : Fin (k + 1), γ j / ‖constraintSeq j‖
    ∑ n : Fin (k + 1), ((γ n / ‖constraintSeq n‖) / denom) • (xSeq n : E)

/-- If the full-history window contains a zero-constraint iterate, the repaired average uses the
current iterate `x^k`. -/
theorem dual_projected_subgradient_full_average_iterate_eq_current_of_exists_constraint_eq_zero
    {k : ℕ}
    (hzero : ∃ n : Fin (k + 1), constraintSeq n = 0) :
    dual_projected_subgradient_full_average_iterate (xSel := xSel) (γ := γ) (lam0 := lam0)
        (X := X) (g := g) k =
      (xSeq k : E) := by
  -- The repaired owner is defined by this branch split, so the zero-constraint case simplifies.
  rw [dual_projected_subgradient_full_average_iterate, if_pos hzero]

/-- When every constraint vector in the full-history window is nonzero, the repaired average is
exactly the displayed weighted sum from Lemma 8.45. -/
theorem dual_projected_subgradient_full_average_iterate_eq_weighted_sum
    {k : ℕ}
    (hactive : ∀ n : Fin (k + 1), constraintSeq n ≠ 0) :
    dual_projected_subgradient_full_average_iterate (xSel := xSel) (γ := γ) (lam0 := lam0)
        (X := X) (g := g) k =
      ∑ n : Fin (k + 1),
        ((γ n / ‖constraintSeq n‖) /
          ∑ j : Fin (k + 1), γ j / ‖constraintSeq j‖) • (xSeq n : E) := by
  -- The nonzero-constraint hypothesis removes the fallback branch of the repaired definition.
  have hzero : ¬ ∃ n : Fin (k + 1), constraintSeq n = 0 := by
    intro h
    rcases h with ⟨n, hn⟩
    exact hactive n hn
  rw [dual_projected_subgradient_full_average_iterate, if_neg hzero]

/-- The suffix-window averaged primal iterate from Lemma 8.45. When every constraint vector in the
window `[k / 2, k]` is nonzero, it uses the textbook normalized weights `γ_n / ‖g(x^n)‖₂` on
that window. If the window contains a zero-constraint iterate, the repaired owner falls back to
the current iterate `x^k` rather than silently deleting those indices via Lean's totalized
division. -/
def dual_projected_subgradient_partial_average_iterate (k : ℕ) : E :=
  if ∃ n ∈ Finset.Icc (k / 2) k, constraintSeq n = 0 then
    (xSeq k : E)
  else
    let denom := Finset.sum (Finset.Icc (k / 2) k) fun j ↦ γ j / ‖constraintSeq j‖
    Finset.sum (Finset.Icc (k / 2) k) fun n ↦
      ((γ n / ‖constraintSeq n‖) / denom) • (xSeq n : E)

/-- If the suffix window contains a zero-constraint iterate, the repaired average uses the
current iterate `x^k`. -/
theorem dual_projected_subgradient_partial_average_iterate_eq_current_of_exists_constraint_eq_zero
    {k : ℕ}
    (hzero : ∃ n ∈ Finset.Icc (k / 2) k, constraintSeq n = 0) :
    dual_projected_subgradient_partial_average_iterate (xSel := xSel) (γ := γ) (lam0 := lam0)
        (X := X) (g := g) k =
      (xSeq k : E) := by
  -- The repaired suffix average is also defined by this branch split on zero constraints.
  rw [dual_projected_subgradient_partial_average_iterate, if_pos hzero]

/-- When every constraint vector in the suffix window is nonzero, the repaired partial average is
exactly the displayed weighted sum from Lemma 8.45. -/
theorem dual_projected_subgradient_partial_average_iterate_eq_weighted_sum
    {k : ℕ}
    (hactive : ∀ n ∈ Finset.Icc (k / 2) k, constraintSeq n ≠ 0) :
    dual_projected_subgradient_partial_average_iterate (xSel := xSel) (γ := γ) (lam0 := lam0)
        (X := X) (g := g) k =
      Finset.sum (Finset.Icc (k / 2) k) fun n ↦
        ((γ n / ‖constraintSeq n‖) /
          Finset.sum (Finset.Icc (k / 2) k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E) := by
  -- The nonzero-constraint hypothesis removes the fallback branch on the suffix window.
  have hzero : ¬ ∃ n ∈ Finset.Icc (k / 2) k, constraintSeq n = 0 := by
    intro h
    rcases h with ⟨n, hn, hconstraint⟩
    exact hactive n hn hconstraint
  rw [dual_projected_subgradient_partial_average_iterate, if_neg hzero]

local notation "fullAvg" =>
  dual_projected_subgradient_full_average_iterate (X := X) (g := g) xSel γ lam0

local notation "partialAvg" =>
  dual_projected_subgradient_partial_average_iterate (X := X) (g := g) xSel γ lam0

/-- Helper for Lemma 8.45: projecting a real number to `ℝ≥0` cannot increase its squared
distance to a nonnegative target. -/
lemma toNNReal_sub_sq_le_sub_sq {a b : ℝ} (hb : 0 ≤ b) :
    ((Real.toNNReal a : ℝ) - b) ^ (2 : ℕ) ≤ (a - b) ^ (2 : ℕ) := by
  -- Split according to the sign of `a`, since `Real.toNNReal a` is either `a` or `0`.
  by_cases ha : 0 ≤ a
  · rw [Real.coe_toNNReal a ha]
  · have htoa : (Real.toNNReal a : ℝ) = 0 := by
      rw [Real.toNNReal_of_nonpos (le_of_not_ge ha)]
      simp
    rw [htoa]
    have hlt : a < 0 := lt_of_not_ge ha
    nlinarith

/-- Helper for Lemma 8.45: each primal iterate furnishes a lower bound on the feasible objective
values through its current Lagrangian minimization property. -/
lemma dualProjectedSubgradientPrimalGapLeNegMultiplierPairing
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (n : ℕ) :
    f (xSeq n : E) - fOpt ≤ -∑ i, (lamSeq n i : ℝ) * g i (xSeq n : E) := by
  have hmin := dual_projected_subgradient_primal_iterate_isMinOn
    (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0) h_admissible n
  have hlag_le_fOpt :
      dual_projected_subgradient_lagrangian f g (lamSeq n) (xSeq n : E) ≤ fOpt := by
    -- The current Lagrangian value is a lower bound on every feasible objective value.
    refine h_problem.optimal_value_isGLB.2 ?_
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    rcases (mem_dual_projected_subgradient_feasible_set.mp hy) with ⟨hyX, hyg⟩
    have hxy := (isMinOn_iff.mp hmin) y hyX
    have hpenalty_nonpos : ∑ i, (lamSeq n i : ℝ) * g i y ≤ 0 := by
      refine Finset.sum_nonpos ?_
      intro i hi
      exact mul_nonpos_of_nonneg_of_nonpos (NNReal.coe_nonneg _) (hyg i)
    rw [dual_projected_subgradient_lagrangian_apply]
    linarith
  -- Expanding the Lagrangian isolates the desired primal gap estimate.
  rw [dual_projected_subgradient_lagrangian_apply] at hlag_le_fOpt
  linarith

omit [NormedSpace ℝ E] in
/-- Helper for Lemma 8.45: if the normalization denominator over a window `[p, k]` vanishes,
then every constraint vector in that window is zero. -/
lemma constraintZeroOfWindowDenomEqZero
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    {p k n : ℕ}
    (hzero :
      Finset.sum (Finset.Icc p k) (fun j ↦ γ j / ‖constraintSeq j‖) = 0)
    (hn : n ∈ Finset.Icc p k) :
    constraintSeq n = 0 := by
  have hterm_zero :
      γ n / ‖constraintSeq n‖ = 0 := by
    have hnonneg :
        ∀ j ∈ Finset.Icc p k, 0 ≤ γ j / ‖constraintSeq j‖ := by
      intro j hj
      exact div_nonneg (le_of_lt (dual_projected_subgradient_method_stepsize_pos
        (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible j)) (norm_nonneg _)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero n hn
  by_contra hconstraint
  have hnorm_pos : 0 < ‖constraintSeq n‖ := norm_pos_iff.mpr hconstraint
  have hfrac_pos : 0 < γ n / ‖constraintSeq n‖ := by
    exact div_pos
      (dual_projected_subgradient_method_stepsize_pos
        (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible n)
      hnorm_pos
  linarith

omit [NormedSpace ℝ E] in
/-- Helper for Lemma 8.45: if the current constraint vector vanishes, then the positive-part
constraint violation also vanishes. -/
lemma positiveConstraintViolationEqZeroOfConstraintEqZero
    {x : E}
    (hconstraint : dual_projected_subgradient_constraint_vector g x = 0) :
    positive_constraint_violation gVec x = 0 := by
  -- Rewrite the positive-part vector coordinatewise using the zero constraint vector.
  have hpos : (gVec x)⁺ = 0 := by
    funext i
    have hcoord : g i x = 0 := by
      simpa using congrArg (fun v : Λ ↦ v i) hconstraint
    simp [hcoord]
  rw [positive_constraint_violation_def, hpos]
  simp

omit [NormedSpace ℝ E] in
/-- Helper for Lemma 8.45: once a zero constraint vector appears, the deterministic update keeps
all later primal iterates fixed, so every later constraint vector also vanishes. -/
lemma constraintSeqEqZeroOfLeOfConstraintEqZero
    {n k : ℕ} (hnk : n ≤ k) (hconstraint : constraintSeq n = 0) :
    constraintSeq k = 0 := by
  -- Induct forward along the time interval and freeze each successor step with the zero update.
  induction hnk with
  | refl =>
      simpa using hconstraint
  | @step k hnk ih =>
      have hlam :
          lamSeq (k + 1) = lamSeq k :=
        dual_projected_subgradient_method_succ_of_constraint_vector_eq_zero
          (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0) k ih
      have hx :
          (xSeq (k + 1) : E) = (xSeq k : E) := by
        -- The frozen multiplier makes the next primal minimizer equal to the current one.
        rw [dual_projected_subgradient_primal_iterate_eq,
          dual_projected_subgradient_primal_iterate_eq, hlam]
      have hnext :
          constraintSeq (k + 1) = constraintSeq k := by
        -- The constraint vector only depends on the primal iterate, which has not changed.
        exact congrArg (dual_projected_subgradient_constraint_vector g) hx
      exact hnext.trans ih

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Helper for Lemma 8.45: a test multiplier proportional to the positive part of `g x` has
Euclidean norm at most `ρ` and realizes the penalized constraint term exactly. -/
lemma positivePartTestMultiplierSpec
    {x : E} (hρ : 0 < ρ) :
    ∃ lamBar : Fin m → NNReal,
      ‖dual_projected_subgradient_multiplier_vector lamBar‖ ≤ ρ ∧
        ∑ i, (lamBar i : ℝ) * g i x =
          ρ * positive_constraint_violation gVec x := by
  let posVec : Λ := WithLp.toLp 2 (fun i ↦ max (g i x) 0)
  by_cases hzero : positive_constraint_violation gVec x = 0
  · refine ⟨fun _ ↦ 0, ?_, ?_⟩
    -- When the positive-part norm vanishes, the zero multiplier already realizes the claim.
    · change ‖(0 : Λ)‖ ≤ ρ
      simpa using hρ.le
    · rw [hzero]
      simp
  · let lamBar : Fin m → NNReal :=
      fun i ↦ Real.toNNReal
        ((ρ / positive_constraint_violation gVec x) * max (g i x) 0)
    have hposVec_eq : posVec = WithLp.toLp 2 ((gVec x)⁺) := by
      ext i
      rfl
    have hposVec_norm : ‖posVec‖ = positive_constraint_violation gVec x := by
      rw [positive_constraint_violation_def, hposVec_eq]
    have hviolation_nonneg : 0 ≤ positive_constraint_violation gVec x := by
      simp [positive_constraint_violation_def]
    have hviolation_pos : 0 < positive_constraint_violation gVec x := by
      exact lt_of_le_of_ne hviolation_nonneg (by
        intro h
        exact hzero h.symm)
    have hscale_nonneg : 0 ≤ ρ / positive_constraint_violation gVec x := by
      exact div_nonneg hρ.le hviolation_nonneg
    have hlamBar_apply :
        ∀ i,
          (lamBar i : ℝ) =
            (ρ / positive_constraint_violation gVec x) * max (g i x) 0 := by
      intro i
      have hcoord_nonneg :
          0 ≤
            (ρ / positive_constraint_violation gVec x) * max (g i x) 0 := by
        exact mul_nonneg hscale_nonneg (le_max_right _ _)
      simpa [lamBar] using
        (Real.coe_toNNReal
          ((ρ / positive_constraint_violation gVec x) * max (g i x) 0) hcoord_nonneg)
    have hvec :
        dual_projected_subgradient_multiplier_vector lamBar =
          (ρ / positive_constraint_violation gVec x) • posVec := by
      -- Identify the constructed multiplier vector with a scalar multiple of the positive part.
      ext i
      rw [dual_projected_subgradient_multiplier_vector_apply, hlamBar_apply i]
      change
        (ρ / positive_constraint_violation gVec x) * max (g i x) 0 =
          ((ρ / positive_constraint_violation gVec x) • posVec) i
      simp [posVec]
    refine ⟨lamBar, ?_, ?_⟩
    · -- The constructed multiplier has exactly norm `ρ`.
      calc
        ‖dual_projected_subgradient_multiplier_vector lamBar‖
            = ‖(ρ / positive_constraint_violation gVec x) • posVec‖ := by
                rw [hvec]
        _ = ‖ρ / positive_constraint_violation gVec x‖ * ‖posVec‖ := by
              rw [norm_smul]
        _ = |ρ / positive_constraint_violation gVec x| *
              positive_constraint_violation gVec x := by
              rw [Real.norm_eq_abs, hposVec_norm]
        _ = (ρ / positive_constraint_violation gVec x) *
              positive_constraint_violation gVec x := by
              rw [abs_of_nonneg hscale_nonneg]
        _ = ρ := by
              field_simp [hzero]
        _ ≤ ρ := by
              exact le_rfl
    · -- Pair the test multiplier with `g x` and rewrite it as the squared norm
      -- of the positive part.
      have hcoord_sq :
          ∀ a : ℝ, max a 0 * a = (max a 0) ^ (2 : ℕ) := by
        intro a
        by_cases ha : 0 ≤ a
        · simp [max_eq_left ha, sq]
        · have ha' : a ≤ 0 := le_of_not_ge ha
          simp [max_eq_right ha', sq]
      have hnorm_sq :
          ∑ i, (max (g i x) 0) ^ (2 : ℕ) =
            (positive_constraint_violation gVec x) ^ (2 : ℕ) := by
        -- The squared Euclidean norm is the sum of the squared coordinates of the positive part.
        have hnorm_sq_pos :
            ∑ i, (max (g i x) 0) ^ (2 : ℕ) = ‖posVec‖ ^ (2 : ℕ) := by
          symm
          simpa [posVec] using EuclideanSpace.real_norm_sq_eq posVec
        rw [hnorm_sq_pos, hposVec_norm]
      calc
        ∑ i, (lamBar i : ℝ) * g i x
            = ∑ i, ((ρ / positive_constraint_violation gVec x) * max (g i x) 0) * g i x := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [hlamBar_apply i]
        _ = (ρ / positive_constraint_violation gVec x) *
              ∑ i, max (g i x) 0 * g i x := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = (ρ / positive_constraint_violation gVec x) *
              ∑ i, (max (g i x) 0) ^ (2 : ℕ) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hcoord_sq (g i x)
        _ = (ρ / positive_constraint_violation gVec x) *
              (positive_constraint_violation gVec x) ^ (2 : ℕ) := by
              rw [hnorm_sq]
        _ = ρ * positive_constraint_violation gVec x := by
              field_simp [hzero]

/-- Helper for Lemma 8.45: if the current iterate already has zero constraint vector, then it
automatically satisfies every window bound ending at that iterate. -/
lemma windowPenalizedGapLeOfCurrentConstraintEqZero
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    {p k : ℕ} (hpk : p ≤ k)
    (hconstraint_zero : constraintSeq k = 0)
    (ρ : ℝ) :
    f (xSeq k : E) - fOpt +
        ρ * positive_constraint_violation gVec (xSeq k : E) ≤
      (L / 2) *
        ((‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) +
            Finset.sum (Finset.Icc p k) fun n ↦ (γ n) ^ (2 : ℕ)) /
          Finset.sum (Finset.Icc p k) γ := by
  have hgap :=
    dualProjectedSubgradientPrimalGapLeNegMultiplierPairing
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
      (xSel := xSel) (γ := γ) (lam0 := lam0) h_problem h_admissible k
  have hpair_zero :
      ∑ i, (lamSeq k i : ℝ) * g i (xSeq k : E) = 0 := by
    -- Every constraint coordinate vanishes at the current iterate.
    refine Finset.sum_eq_zero ?_
    intro i hi
    change (lamSeq k i : ℝ) * constraintSeq k i = 0
    rw [hconstraint_zero]
    simp
  have hviolation_zero :
      positive_constraint_violation gVec (xSeq k : E) = 0 :=
    positiveConstraintViolationEqZeroOfConstraintEqZero
      (g := g) (x := (xSeq k : E)) hconstraint_zero
  have hleft_nonpos :
      f (xSeq k : E) - fOpt +
          ρ * positive_constraint_violation gVec (xSeq k : E) ≤ 0 := by
    -- The primal gap is nonpositive, and the residual term vanishes on a zero-constraint iterate.
    rw [hviolation_zero]
    have hgap_nonpos : f (xSeq k : E) - fOpt ≤ 0 := by
      rw [hpair_zero] at hgap
      simpa using hgap
    linarith
  have hL_nonneg : 0 ≤ L := by
    -- Evaluating the uniform constraint bound at `x^p` shows that `L` itself is nonnegative.
    have hbound_p := h_constraint_bound (xSeq p : E) (xSeq p).property
    exact le_trans (norm_nonneg _) hbound_p
  have hsum_pos : 0 < Finset.sum (Finset.Icc p k) γ := by
    -- The interval contains `p`, and every stepsize is strictly positive.
    have hp_mem : p ∈ Finset.Icc p k := Finset.mem_Icc.mpr ⟨le_rfl, hpk⟩
    have hle :
        γ p ≤ Finset.sum (Finset.Icc p k) γ :=
      Finset.single_le_sum
        (fun n _ ↦ le_of_lt
          (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible n))
        hp_mem
    exact lt_of_lt_of_le
      (dual_projected_subgradient_method_stepsize_pos
        (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible p)
      hle
  have hsqsum_nonneg :
      0 ≤ Finset.sum (Finset.Icc p k) fun n ↦ (γ n) ^ (2 : ℕ) := by
    exact Finset.sum_nonneg fun n _ ↦ sq_nonneg (γ n)
  have hnum_nonneg :
      0 ≤
        (‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) +
          Finset.sum (Finset.Icc p k) fun n ↦ (γ n) ^ (2 : ℕ) := by
    exact add_nonneg (sq_nonneg _) hsqsum_nonneg
  have hright_nonneg :
      0 ≤
        (L / 2) *
            ((‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) +
                Finset.sum (Finset.Icc p k) fun n ↦ (γ n) ^ (2 : ℕ)) /
          Finset.sum (Finset.Icc p k) γ := by
    have hmul_nonneg :
        0 ≤
          (L / 2) *
            ((‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) +
                Finset.sum (Finset.Icc p k) fun n ↦ (γ n) ^ (2 : ℕ)) := by
      refine mul_nonneg ?_ hnum_nonneg
      exact div_nonneg hL_nonneg (by norm_num)
    exact div_nonneg hmul_nonneg (le_of_lt hsum_pos)
  -- Compare the already nonpositive left-hand side against the nonnegative window bound.
  linarith

/-- Helper for Lemma 8.45: if the normalization denominator over a window `[p, k]` vanishes, then
the fallback iterate `x^k` already satisfies the claimed penalized-gap bound on that window. -/
lemma windowPenalizedGapLeOfDenomEqZero
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    {p k : ℕ} (hpk : p ≤ k)
    (hzero : Finset.sum (Finset.Icc p k) (fun j ↦ γ j / ‖constraintSeq j‖) = 0)
    (ρ : ℝ) :
    f (xSeq k : E) - fOpt +
        ρ * positive_constraint_violation gVec (xSeq k : E) ≤
      (L / 2) *
        ((‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) +
            Finset.sum (Finset.Icc p k) fun n ↦ (γ n) ^ (2 : ℕ)) /
          Finset.sum (Finset.Icc p k) γ := by
  -- The zero denominator forces the current window constraints to vanish, so the current iterate
  -- satisfies the generic zero-constraint window estimate.
  have hk_mem : k ∈ Finset.Icc p k := Finset.mem_Icc.mpr ⟨hpk, le_rfl⟩
  have hconstraint_zero : constraintSeq k = 0 :=
    constraintZeroOfWindowDenomEqZero
      (X := X) (f := f) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0)
      h_admissible hzero hk_mem
  exact windowPenalizedGapLeOfCurrentConstraintEqZero
    (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
    (L := L) (xSel := xSel) (γ := γ) (lam0 := lam0)
    h_problem h_admissible h_constraint_bound hpk hconstraint_zero ρ

omit [NormedSpace ℝ E] in
/-- Helper for Lemma 8.45: the one-step squared-distance recursion holds on every active
multiplier update against an arbitrary nonnegative test multiplier. -/
lemma multiplierStepSqDistLe
    (n : ℕ) (lamBar : Fin m → NNReal)
    (hconstraint : constraintSeq n ≠ 0) :
    2 * (γ n / ‖constraintSeq n‖) *
        (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ))) ≤
      ‖lamVecSeq n - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
        (γ n) ^ (2 : ℕ) -
          ‖lamVecSeq (n + 1) - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) := by
  let lamBarVec := dual_projected_subgradient_multiplier_vector lamBar
  have hsucc :
      lamSeq (n + 1) =
        dual_projected_subgradient_multiplier_update g (γ n) (lamSeq n) (xSeq n : E) :=
    dual_projected_subgradient_method_succ_of_constraint_vector_ne_zero
      (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0) n hconstraint
  have hnorm_pos : 0 < ‖constraintSeq n‖ := norm_pos_iff.mpr hconstraint
  have hnext_le :
      ‖lamVecSeq (n + 1) - lamBarVec‖ ^ (2 : ℕ) ≤
        ∑ i,
          (((lamSeq n i : ℝ) +
                γ n * g i (xSeq n : E) / ‖constraintSeq n‖) -
              (lamBar i : ℝ)) ^ (2 : ℕ) := by
    -- Control the projected update coordinatewise with the scalar projection inequality.
    have hcoord :
        ∀ i : Fin m,
          (((lamSeq (n + 1) i : ℝ) - (lamBar i : ℝ)) ^ (2 : ℕ)) ≤
            ((((lamSeq n i : ℝ) +
                    γ n * g i (xSeq n : E) / ‖constraintSeq n‖) -
                  (lamBar i : ℝ)) ^ (2 : ℕ)) := by
      intro i
      have hscalar :=
        toNNReal_sub_sq_le_sub_sq
          (a := (lamSeq n i : ℝ) + γ n * g i (xSeq n : E) / ‖constraintSeq n‖)
          (b := (lamBar i : ℝ)) (NNReal.coe_nonneg _)
      simpa [lamBarVec, hsucc, dual_projected_subgradient_multiplier_update_apply,
        dual_projected_subgradient_multiplier_vector_apply] using hscalar
    calc
      ‖lamVecSeq (n + 1) - lamBarVec‖ ^ (2 : ℕ)
          = ∑ i, (((lamSeq (n + 1) i : ℝ) - (lamBar i : ℝ)) ^ (2 : ℕ)) := by
              simpa [lamBarVec, dual_projected_subgradient_multiplier_vector_apply] using
                EuclideanSpace.real_norm_sq_eq (lamVecSeq (n + 1) - lamBarVec)
      _ ≤ ∑ i,
            (((lamSeq n i : ℝ) + γ n * g i (xSeq n : E) / ‖constraintSeq n‖) -
              (lamBar i : ℝ)) ^ (2 : ℕ) := Finset.sum_le_sum fun i _ ↦ hcoord i
  have hcurr_eq :
      ‖lamVecSeq n - lamBarVec‖ ^ (2 : ℕ) =
        ∑ i, (((lamSeq n i : ℝ) - (lamBar i : ℝ)) ^ (2 : ℕ)) := by
    simpa [lamBarVec, dual_projected_subgradient_multiplier_vector_apply] using
      EuclideanSpace.real_norm_sq_eq (lamVecSeq n - lamBarVec)
  have hconstraint_sq :
      ‖constraintSeq n‖ ^ (2 : ℕ) =
        ∑ i, (g i (xSeq n : E)) ^ (2 : ℕ) := by
    simpa [dual_projected_subgradient_constraint_vector_apply] using
      EuclideanSpace.real_norm_sq_eq (constraintSeq n)
  have hstep_sq :
      ∑ i, (((γ n / ‖constraintSeq n‖) * g i (xSeq n : E)) ^ (2 : ℕ)) = (γ n) ^ (2 : ℕ) := by
    calc
      ∑ i, (((γ n / ‖constraintSeq n‖) * g i (xSeq n : E)) ^ (2 : ℕ))
          = ∑ i,
              ((γ n / ‖constraintSeq n‖) ^ (2 : ℕ)) *
                (g i (xSeq n : E)) ^ (2 : ℕ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = ((γ n / ‖constraintSeq n‖) ^ (2 : ℕ)) *
            ∑ i, (g i (xSeq n : E)) ^ (2 : ℕ) := by
            rw [Finset.mul_sum]
      _ = ((γ n / ‖constraintSeq n‖) ^ (2 : ℕ)) * ‖constraintSeq n‖ ^ (2 : ℕ) := by
            rw [← hconstraint_sq]
      _ = (γ n) ^ (2 : ℕ) := by
            field_simp [hnorm_pos.ne']
  have hcross :
      ∑ i,
          2 * (((γ n / ‖constraintSeq n‖) * g i (xSeq n : E)) *
            ((lamSeq n i : ℝ) - (lamBar i : ℝ))) =
        2 * (γ n / ‖constraintSeq n‖) *
          ∑ i, g i (xSeq n : E) * ((lamSeq n i : ℝ) - (lamBar i : ℝ)) := by
    calc
      ∑ i,
          2 * (((γ n / ‖constraintSeq n‖) * g i (xSeq n : E)) *
            ((lamSeq n i : ℝ) - (lamBar i : ℝ))) =
        ∑ i,
          (2 * (γ n / ‖constraintSeq n‖)) *
            (g i (xSeq n : E) * ((lamSeq n i : ℝ) - (lamBar i : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = 2 * (γ n / ‖constraintSeq n‖) *
            ∑ i, g i (xSeq n : E) * ((lamSeq n i : ℝ) - (lamBar i : ℝ)) := by
            rw [Finset.mul_sum]
  have hexpand :
      ∑ i,
          (((lamSeq n i : ℝ) +
                γ n * g i (xSeq n : E) / ‖constraintSeq n‖) -
              (lamBar i : ℝ)) ^ (2 : ℕ) =
        ‖lamVecSeq n - lamBarVec‖ ^ (2 : ℕ) +
          (γ n) ^ (2 : ℕ) +
            2 * (γ n / ‖constraintSeq n‖) *
              ∑ i, g i (xSeq n : E) * ((lamSeq n i : ℝ) - (lamBar i : ℝ)) := by
    calc
      ∑ i,
          (((lamSeq n i : ℝ) +
                γ n * g i (xSeq n : E) / ‖constraintSeq n‖) -
              (lamBar i : ℝ)) ^ (2 : ℕ)
          =
        ∑ i,
          ((((lamSeq n i : ℝ) - (lamBar i : ℝ)) ^ (2 : ℕ)) +
            (((γ n / ‖constraintSeq n‖) * g i (xSeq n : E)) ^ (2 : ℕ)) +
              2 * (((γ n / ‖constraintSeq n‖) * g i (xSeq n : E)) *
                ((lamSeq n i : ℝ) - (lamBar i : ℝ)))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = (∑ i, (((lamSeq n i : ℝ) - (lamBar i : ℝ)) ^ (2 : ℕ))) +
            (∑ i, (((γ n / ‖constraintSeq n‖) * g i (xSeq n : E)) ^ (2 : ℕ))) +
            ∑ i,
              2 * (((γ n / ‖constraintSeq n‖) * g i (xSeq n : E)) *
                ((lamSeq n i : ℝ) - (lamBar i : ℝ))) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ‖lamVecSeq n - lamBarVec‖ ^ (2 : ℕ) +
            (γ n) ^ (2 : ℕ) +
              2 * (γ n / ‖constraintSeq n‖) *
                ∑ i, g i (xSeq n : E) * ((lamSeq n i : ℝ) - (lamBar i : ℝ)) := by
              rw [← hcurr_eq, hstep_sq, hcross]
  have hpair_flip :
      ∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)) =
        -∑ i, g i (xSeq n : E) * ((lamSeq n i : ℝ) - (lamBar i : ℝ)) := by
    calc
      ∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ))
          = ∑ i, -(g i (xSeq n : E) * ((lamSeq n i : ℝ) - (lamBar i : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = -∑ i, g i (xSeq n : E) * ((lamSeq n i : ℝ) - (lamBar i : ℝ)) := by
            rw [Finset.sum_neg_distrib]
  -- Rearrange the expanded update inequality into the source one-step recursion.
  rw [hexpand] at hnext_le
  rw [hpair_flip]
  nlinarith

omit [NormedSpace ℝ E] in
/-- Helper for Lemma 8.45: the active-window squared-distance estimates telescope to a single
initial multiplier distance plus the accumulated squared stepsizes. -/
lemma windowMultiplierPairingLe
    {p k : ℕ} (hpk : p ≤ k) (lamBar : Fin m → NNReal)
    (hactive : ∀ n ∈ Finset.Icc p k, constraintSeq n ≠ 0) :
    2 * (Finset.sum (Finset.Icc p k) fun n ↦
        (γ n / ‖constraintSeq n‖) *
          (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)))) ≤
      ‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
        Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ)) := by
  let d : ℕ → ℝ := fun n ↦
    ‖lamVecSeq n - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ)
  have hsum_le :
      Finset.sum (Finset.Icc p k) (fun n ↦
          2 * ((γ n / ‖constraintSeq n‖) *
            (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ))))) ≤
        Finset.sum (Finset.Icc p k) (fun n ↦ d n + (γ n) ^ (2 : ℕ) - d (n + 1)) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    simpa [d, mul_assoc] using multiplierStepSqDistLe
      (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0)
      n lamBar (hactive n hn)
  have htel :
      Finset.sum (Finset.Icc p k) (fun n ↦ d n - d (n + 1)) = d p - d (k + 1) := by
    have htel_aux : ∀ q : ℕ,
        Finset.sum (Finset.Icc p (p + q)) (fun n ↦ d n - d (n + 1)) = d p - d (p + q + 1) := by
      intro q
      induction q with
      | zero =>
          simp [d]
      | succ q ih =>
          calc
            Finset.sum (Finset.Icc p (p + (q + 1))) (fun n ↦ d n - d (n + 1))
                = Finset.sum (Finset.Icc p (p + q + 1)) (fun n ↦ d n - d (n + 1)) := by
                    simp [Nat.add_assoc]
            _ = Finset.sum (Finset.Icc p (p + q)) (fun n ↦ d n - d (n + 1)) +
                  (d (p + q + 1) - d (p + q + 2)) := by
                    rw [Finset.sum_Icc_succ_top (show p ≤ p + q + 1 by omega)]
            _ = (d p - d (p + q + 1)) + (d (p + q + 1) - d (p + q + 2)) := by
                  rw [ih]
            _ = d p - d (p + (q + 1) + 1) := by
                  ring
    rcases Nat.exists_eq_add_of_le hpk with ⟨q, rfl⟩
    simpa [Nat.add_assoc] using htel_aux q
  have hsum_eq :
      Finset.sum (Finset.Icc p k) (fun n ↦ d n + (γ n) ^ (2 : ℕ) - d (n + 1)) =
        d p + Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ)) - d (k + 1) := by
    calc
      Finset.sum (Finset.Icc p k) (fun n ↦ d n + (γ n) ^ (2 : ℕ) - d (n + 1))
          = Finset.sum (Finset.Icc p k) (fun n ↦ (d n - d (n + 1)) + (γ n) ^ (2 : ℕ)) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              ring
      _ = Finset.sum (Finset.Icc p k) (fun n ↦ d n - d (n + 1)) +
            Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ)) := by
              rw [Finset.sum_add_distrib]
      _ = d p + Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ)) - d (k + 1) := by
            rw [htel]
            ring
  have htail_nonneg : 0 ≤ d (k + 1) := by
    exact sq_nonneg _
  -- Drop the terminal squared-distance term after telescoping.
  rw [← Finset.mul_sum] at hsum_le
  rw [hsum_eq] at hsum_le
  linarith

/-- Helper for Lemma 8.45: the active-window weighted average is exactly the `centerMass`
normal form attached to the weights `γ_n / ‖g(x^n)‖₂`. -/
lemma activeWindowAverage_eq_centerMass
    {p k : ℕ} :
    let w : ℕ → ℝ := fun n ↦ γ n / ‖constraintSeq n‖
    let xAvg :=
      Finset.sum (Finset.Icc p k) fun n ↦
        (w n / Finset.sum (Finset.Icc p k) w) • (xSeq n : E)
    xAvg = (Finset.Icc p k).centerMass w (fun n ↦ (xSeq n : E)) := by
  -- This is just the `Finset.centerMass` definition with the same displayed weights.
  dsimp
  rw [Finset.centerMass]
  simp only [div_eq_mul_inv, smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  ring

/-- Helper for Lemma 8.45: on an active window, the source telescope plus Jensen yields the
generic averaged primal-gap estimate against an arbitrary nonnegative test multiplier. -/
lemma windowGapWithTestMultiplierLeOfActiveWindow
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    {p k : ℕ} (hpk : p ≤ k)
    (hactive : ∀ n ∈ Finset.Icc p k, constraintSeq n ≠ 0)
    (lamBar : Fin m → NNReal) :
    let xAvg :=
      Finset.sum (Finset.Icc p k) fun n ↦
        ((γ n / ‖constraintSeq n‖) /
          Finset.sum (Finset.Icc p k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E)
    f xAvg - fOpt +
        ∑ i, (lamBar i : ℝ) * g i xAvg ≤
      (L / 2) *
        (‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
            Finset.sum (Finset.Icc p k) fun n ↦ (γ n) ^ (2 : ℕ)) /
          Finset.sum (Finset.Icc p k) γ := by
  let I : Finset ℕ := Finset.Icc p k
  let w : ℕ → ℝ := fun n ↦ γ n / ‖constraintSeq n‖
  let denom : ℝ := Finset.sum I w
  let α : ℕ → ℝ := fun n ↦ w n / denom
  let xAvg : E := Finset.sum I fun n ↦ α n • (xSeq n : E)
  have hp_mem : p ∈ I := by
    simp [I, hpk]
  have hsumγ_pos : 0 < Finset.sum I γ := by
    have hp_le :
        γ p ≤ Finset.sum I γ :=
      Finset.single_le_sum
        (fun n _ ↦ le_of_lt
          (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible n))
        hp_mem
    exact lt_of_lt_of_le
      (dual_projected_subgradient_method_stepsize_pos
        (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible p)
      hp_le
  have hdenom_pos : 0 < denom := by
    have hp_term_pos : 0 < w p := by
      dsimp [w]
      exact div_pos
        (dual_projected_subgradient_method_stepsize_pos
          (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible p)
        (norm_pos_iff.mpr (hactive p hp_mem))
    have hterm_nonneg : ∀ n ∈ I, 0 ≤ w n := by
      intro n hn
      dsimp [w]
      exact div_nonneg
        (le_of_lt (dual_projected_subgradient_method_stepsize_pos
          (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible n))
        (norm_nonneg _)
    exact lt_of_lt_of_le hp_term_pos (Finset.single_le_sum hterm_nonneg hp_mem)
  have hα_nonneg : ∀ n ∈ I, 0 ≤ α n := by
    intro n hn
    dsimp [α]
    exact div_nonneg
      (show 0 ≤ w n by
        dsimp [w]
        exact div_nonneg
          (le_of_lt (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible n))
          (norm_nonneg _))
      (le_of_lt hdenom_pos)
  have hα_sum_one : Finset.sum I α = 1 := by
    calc
      Finset.sum I α = (Finset.sum I w) / denom := by
        simp [α, div_eq_mul_inv, Finset.sum_mul]
      _ = 1 := by
        simp [denom, hdenom_pos.ne']
  have hxAvg_def :
      xAvg =
        Finset.sum (Finset.Icc p k) fun n ↦
          ((γ n / ‖constraintSeq n‖) /
            Finset.sum (Finset.Icc p k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E) := by
    simp [xAvg, I, α, w, denom]
  have hobj :
      f xAvg ≤ Finset.sum I fun n ↦ α n * f (xSeq n : E) := by
    -- Jensen on the objective uses the normalized active-window weights `α`.
    simpa [xAvg, smul_eq_mul] using
      h_problem.objective_convex.map_sum_le hα_nonneg hα_sum_one
        (fun n _ ↦ by simp)
  have hconstraint_jensen :
      ∀ i : Fin m,
        g i xAvg ≤ Finset.sum I fun n ↦ α n * g i (xSeq n : E) := by
    intro i
    -- Jensen applies coordinatewise to each convex constraint function.
    simpa [xAvg, smul_eq_mul] using
      (h_problem.constraint_convex i).map_sum_le hα_nonneg hα_sum_one
        (fun n _ ↦ by simp)
  have hpenalty :
      ∑ i, (lamBar i : ℝ) * g i xAvg ≤
        Finset.sum I fun n ↦ α n * (∑ i, (lamBar i : ℝ) * g i (xSeq n : E)) := by
    calc
      ∑ i, (lamBar i : ℝ) * g i xAvg
          ≤ ∑ i, (lamBar i : ℝ) *
              Finset.sum I (fun n ↦ α n * g i (xSeq n : E)) := by
                refine Finset.sum_le_sum ?_
                intro i hi
                exact mul_le_mul_of_nonneg_left
                  (hconstraint_jensen i) (NNReal.coe_nonneg _)
      _ = Finset.sum Finset.univ
            (fun i : Fin m ↦ Finset.sum I fun n ↦ (lamBar i : ℝ) * (α n * g i (xSeq n : E))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.mul_sum]
      _ = Finset.sum I
            (fun n ↦ Finset.sum Finset.univ fun i : Fin m ↦
              (lamBar i : ℝ) * (α n * g i (xSeq n : E))) := by
            rw [Finset.sum_comm]
      _ = Finset.sum I fun n ↦ α n * (∑ i, (lamBar i : ℝ) * g i (xSeq n : E)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            calc
              ∑ i, (lamBar i : ℝ) * (α n * g i (xSeq n : E))
                  = ∑ i, α n * ((lamBar i : ℝ) * g i (xSeq n : E)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      ring
              _ = α n * (∑ i, (lamBar i : ℝ) * g i (xSeq n : E)) := by
                    rw [Finset.mul_sum]
  have hpointwise :
      ∀ n ∈ I,
        α n * (f (xSeq n : E) - fOpt + ∑ i, (lamBar i : ℝ) * g i (xSeq n : E)) ≤
          α n * ∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)) := by
    intro n hn
    have hgap :=
      dualProjectedSubgradientPrimalGapLeNegMultiplierPairing
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
        (xSel := xSel) (γ := γ) (lam0 := lam0) h_problem h_admissible n
    have hpair_eq :
        ∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)) =
          ∑ i, (lamBar i : ℝ) * g i (xSeq n : E) -
            ∑ i, (lamSeq n i : ℝ) * g i (xSeq n : E) := by
      calc
        ∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ))
            = ∑ i,
                ((lamBar i : ℝ) * g i (xSeq n : E) -
                  (lamSeq n i : ℝ) * g i (xSeq n : E)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = ∑ i, (lamBar i : ℝ) * g i (xSeq n : E) -
              ∑ i, (lamSeq n i : ℝ) * g i (xSeq n : E) := by
              rw [Finset.sum_sub_distrib]
    have hmain :
        f (xSeq n : E) - fOpt + ∑ i, (lamBar i : ℝ) * g i (xSeq n : E) ≤
          ∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)) := by
      rw [hpair_eq]
      linarith
    exact mul_le_mul_of_nonneg_left hmain (hα_nonneg n hn)
  have hweighted_pair :
      Finset.sum I
          (fun n ↦ α n * (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)))) ≤
        ((‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
              Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ))) / 2) / denom := by
    have hwindow :=
      windowMultiplierPairingLe
        (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0)
        hpk lamBar hactive
    have hhalf :
        Finset.sum I (fun n ↦
            w n * (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)))) ≤
          (‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
              Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ))) / 2 := by
      linarith
    have hdiv :
        Finset.sum I (fun n ↦
            w n * (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)))) / denom ≤
          ((‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
                Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ))) / 2) / denom := by
      exact div_le_div_of_nonneg_right hhalf (le_of_lt hdenom_pos)
    have hα_pair_eq :
        Finset.sum I
            (fun n ↦ α n * (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)))) =
          Finset.sum I
              (fun n ↦
                (w n * (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)))) /
                  denom) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      dsimp [α]
      ring
    calc
      Finset.sum I
          (fun n ↦ α n * (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ))))
          = Finset.sum I
              (fun n ↦
                (w n * (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)))) /
                  denom) := hα_pair_eq
      _ = (Finset.sum I (fun n ↦
              w n * (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ))))) /
            denom := by
            rw [Finset.sum_div]
      _ ≤
          ((‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
                Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ))) / 2) / denom := hdiv
  have hweighted_left_eq :
      Finset.sum I
          (fun n ↦ α n *
            (f (xSeq n : E) - fOpt + ∑ i, (lamBar i : ℝ) * g i (xSeq n : E))) =
        Finset.sum I (fun n ↦ α n * f (xSeq n : E)) - fOpt +
          Finset.sum I (fun n ↦ α n * (∑ i, (lamBar i : ℝ) * g i (xSeq n : E))) := by
    calc
      Finset.sum I
          (fun n ↦ α n *
            (f (xSeq n : E) - fOpt + ∑ i, (lamBar i : ℝ) * g i (xSeq n : E)))
          =
        Finset.sum I
          (fun n ↦
            α n * f (xSeq n : E) -
              α n * fOpt +
              α n * ∑ i, (lamBar i : ℝ) * g i (xSeq n : E)) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              ring
      _ = Finset.sum I (fun n ↦ α n * f (xSeq n : E)) -
            Finset.sum I (fun n ↦ α n * fOpt) +
            Finset.sum I (fun n ↦ α n * ∑ i, (lamBar i : ℝ) * g i (xSeq n : E)) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = Finset.sum I (fun n ↦ α n * f (xSeq n : E)) - fOpt +
            Finset.sum I (fun n ↦ α n * ∑ i, (lamBar i : ℝ) * g i (xSeq n : E)) := by
              have hsum_fOpt : Finset.sum I (fun n ↦ α n * fOpt) = fOpt := by
                calc
                  Finset.sum I (fun n ↦ α n * fOpt) = (Finset.sum I α) * fOpt := by
                    rw [← Finset.sum_mul]
                  _ = fOpt := by rw [hα_sum_one, one_mul]
              rw [hsum_fOpt]
  have hleft_to_pair :
      f xAvg - fOpt + ∑ i, (lamBar i : ℝ) * g i xAvg ≤
        Finset.sum I
          (fun n ↦ α n * (∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ)))) := by
    have hsum_pointwise :
        Finset.sum I
            (fun n ↦ α n *
              (f (xSeq n : E) - fOpt + ∑ i, (lamBar i : ℝ) * g i (xSeq n : E))) ≤
          Finset.sum I
            (fun n ↦ α n *
              ∑ i, g i (xSeq n : E) * ((lamBar i : ℝ) - (lamSeq n i : ℝ))) :=
      Finset.sum_le_sum hpointwise
    rw [hweighted_left_eq] at hsum_pointwise
    linarith [hobj, hpenalty, hsum_pointwise]
  have hL_pos : 0 < L := by
    have hnorm_pos : 0 < ‖constraintSeq p‖ := norm_pos_iff.mpr (hactive p hp_mem)
    exact lt_of_lt_of_le hnorm_pos (h_constraint_bound (xSeq p : E) (xSeq p).property)
  have hratio_compare :
      Finset.sum I γ ≤ denom * L := by
    have hsum_compare :
        Finset.sum I γ ≤ Finset.sum I (fun n ↦ w n * L) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hterm_nonneg : 0 ≤ w n := by
        dsimp [w]
        exact div_nonneg
          (le_of_lt (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible n))
          (norm_nonneg _)
      have hnorm_le : ‖constraintSeq n‖ ≤ L :=
        h_constraint_bound (xSeq n : E) (xSeq n).property
      have hnorm_pos : 0 < ‖constraintSeq n‖ := norm_pos_iff.mpr (hactive n hn)
      calc
        γ n = w n * ‖constraintSeq n‖ := by
                dsimp [w]
                field_simp [hnorm_pos.ne']
        _ ≤ w n * L := by
              exact mul_le_mul_of_nonneg_left hnorm_le hterm_nonneg
    calc
      Finset.sum I γ ≤ Finset.sum I (fun n ↦ w n * L) := hsum_compare
      _ = denom * L := by
            simp [denom, Finset.sum_mul]
  have hinv_compare : 1 / denom ≤ L / Finset.sum I γ := by
    field_simp [hdenom_pos.ne', hsumγ_pos.ne']
    nlinarith [hratio_compare]
  have hnum_nonneg :
      0 ≤
        ‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
          Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ)) := by
    refine add_nonneg (sq_nonneg _) ?_
    exact Finset.sum_nonneg fun n _ ↦ sq_nonneg (γ n)
  have hratio :
      ((‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
            Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ))) / 2) / denom ≤
        (L / 2) *
          (‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
              Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum I γ := by
    calc
      ((‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
            Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ))) / 2) / denom
          = ((‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
                Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ))) / 2) * (1 / denom) := by
                ring
      _ ≤ ((‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
                Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ))) / 2) *
              (L / Finset.sum I γ) := by
                exact mul_le_mul_of_nonneg_left hinv_compare
                  (div_nonneg hnum_nonneg (by norm_num))
      _ = (L / 2) *
            (‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
                Finset.sum I (fun n ↦ (γ n) ^ (2 : ℕ))) /
              Finset.sum I γ := by
              ring
  -- Route correction: telescope first in the arbitrary `lamBar` world, then specialize `lamBar`
  -- only after Jensen has produced the active-window averaged gap bound.
  have hmain := hleft_to_pair.trans hweighted_pair
  simpa [xAvg, I, α, w, denom] using hmain.trans hratio

/-- Helper for Lemma 8.45: specializing the arbitrary active-window estimate with the positive
part test multiplier yields the penalized residual bound used by the two public wrappers. -/
lemma windowPenalizedGapLeOfActiveWindow
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    {p k : ℕ} (hpk : p ≤ k) (hρ : 0 < ρ)
    (hactive : ∀ n ∈ Finset.Icc p k, constraintSeq n ≠ 0) :
    let xAvg :=
      Finset.sum (Finset.Icc p k) fun n ↦
        ((γ n / ‖constraintSeq n‖) /
          Finset.sum (Finset.Icc p k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E)
    f xAvg - fOpt +
        ρ * positive_constraint_violation gVec xAvg ≤
      (L / 2) *
        ((‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) +
            Finset.sum (Finset.Icc p k) fun n ↦ (γ n) ^ (2 : ℕ)) /
          Finset.sum (Finset.Icc p k) γ := by
  let xAvg :=
    Finset.sum (Finset.Icc p k) fun n ↦
      ((γ n / ‖constraintSeq n‖) /
        Finset.sum (Finset.Icc p k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E)
  rcases positivePartTestMultiplierSpec
      (g := g) (ρ := ρ) (x := xAvg) hρ with
    ⟨lamBar, hlamBar_norm, hlamBar_eval⟩
  have hbase :
      f xAvg - fOpt + ∑ i, (lamBar i : ℝ) * g i xAvg ≤
        (L / 2) *
          (‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
              Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc p k) γ := by
    simpa [xAvg] using
      (windowGapWithTestMultiplierLeOfActiveWindow
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) (L := L)
        (xSel := xSel) (γ := γ) (lam0 := lam0)
        h_problem h_admissible h_constraint_bound hpk hactive lamBar)
  have htriangle :
      ‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ≤
        ‖lamVecSeq p‖ + ρ := by
    calc
      ‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖
          ≤ ‖lamVecSeq p‖ +
              ‖dual_projected_subgradient_multiplier_vector lamBar‖ := norm_sub_le _ _
      _ ≤ ‖lamVecSeq p‖ + ρ := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hlamBar_norm ‖lamVecSeq p‖
  have hsq :
      ‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) ≤
        (‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  have hL_nonneg : 0 ≤ L := by
    exact le_of_lt <|
      lt_of_lt_of_le
        (norm_pos_iff.mpr (hactive p (by simp [hpk])))
        (h_constraint_bound (xSeq p : E) (xSeq p).property)
  have hsumγ_pos : 0 < Finset.sum (Finset.Icc p k) γ := by
    have hp_mem : p ∈ Finset.Icc p k := by simp [hpk]
    have hp_le :
        γ p ≤ Finset.sum (Finset.Icc p k) γ :=
      Finset.single_le_sum
        (fun n _ ↦ le_of_lt
          (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible n))
        hp_mem
    exact lt_of_lt_of_le
      (dual_projected_subgradient_method_stepsize_pos
        (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible p)
      hp_le
  have hmono :
      (L / 2) *
          (‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
              Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc p k) γ ≤
        (L / 2) *
          ((‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) +
              Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc p k) γ := by
    have hnum_le :
        ‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
            Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ)) ≤
          (‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) +
            Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ)) := by
      exact add_le_add hsq le_rfl
    calc
      (L / 2) *
          (‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
              Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc p k) γ
          = ((L / 2) / Finset.sum (Finset.Icc p k) γ) *
              (‖lamVecSeq p - dual_projected_subgradient_multiplier_vector lamBar‖ ^ (2 : ℕ) +
                Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ))) := by
                ring
      _ ≤ ((L / 2) / Finset.sum (Finset.Icc p k) γ) *
            ((‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) +
              Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ))) := by
            exact mul_le_mul_of_nonneg_left hnum_le
              (div_nonneg (div_nonneg hL_nonneg (by norm_num)) (le_of_lt hsumγ_pos))
      _ = (L / 2) *
            ((‖lamVecSeq p‖ + ρ) ^ (2 : ℕ) +
              Finset.sum (Finset.Icc p k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
              Finset.sum (Finset.Icc p k) γ := by
            ring
  -- Specialize the generic `lamBar` estimate with the positive-part witness and then enlarge the
  -- multiplier-distance term using the triangle inequality.
  rw [hlamBar_eval] at hbase
  simpa [xAvg] using hbase.trans hmono

/-- Helper for Lemma 8.45: on the active full-history branch, the repaired owner is exactly the
generic window average over `Finset.Icc 0 k`. -/
lemma fullWindowIndexBridge {k : ℕ}
    (hactive : ∀ n : Fin (k + 1), constraintSeq n ≠ 0) :
    fullAvg k =
      Finset.sum (Finset.Icc 0 k) fun n ↦
        ((γ n / ‖constraintSeq n‖) /
          Finset.sum (Finset.Icc 0 k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E) := by
  have htail0 : Finset.Icc 0 k = Finset.range (k + 1) := by
    ext n
    simp [Finset.mem_Icc]
  have hden :
      (∑ j : Fin (k + 1), γ j / ‖constraintSeq j‖) =
        Finset.sum (Finset.Icc 0 k) fun j ↦ γ j / ‖constraintSeq j‖ := by
    calc
      (∑ j : Fin (k + 1), γ j / ‖constraintSeq j‖)
          = Finset.sum (Finset.range (k + 1)) fun j ↦ γ j / ‖constraintSeq j‖ := by
              simpa using
                (Fin.sum_univ_eq_sum_range
                  (fun j ↦ γ j / ‖constraintSeq j‖) (k + 1))
      _ = Finset.sum (Finset.Icc 0 k) fun j ↦ γ j / ‖constraintSeq j‖ := by
            rw [← htail0]
  -- Remove the fallback branch first, then rewrite both the numerator and denominator sums.
  calc
    fullAvg k
        = ∑ n : Fin (k + 1),
            ((γ n / ‖constraintSeq n‖) /
              ∑ j : Fin (k + 1), γ j / ‖constraintSeq j‖) • (xSeq n : E) := by
            exact dual_projected_subgradient_full_average_iterate_eq_weighted_sum
              (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0) hactive
    _ = ∑ n : Fin (k + 1),
          ((γ n / ‖constraintSeq n‖) /
            Finset.sum (Finset.Icc 0 k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E) := by
          rw [hden]
    _ = Finset.sum (Finset.range (k + 1)) fun n ↦
          ((γ n / ‖constraintSeq n‖) /
            Finset.sum (Finset.Icc 0 k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E) := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun n ↦
                ((γ n / ‖constraintSeq n‖) /
                  Finset.sum (Finset.Icc 0 k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E))
              (k + 1))
    _ = Finset.sum (Finset.Icc 0 k) fun n ↦
          ((γ n / ‖constraintSeq n‖) /
            Finset.sum (Finset.Icc 0 k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E) := by
          rw [← htail0]

/- Lemma 8.45 is `source-facing`: it gives the primal-dual gap estimates for the two averaged
primal sequences attached to the dual projected subgradient method. Domain sampling against the
nearby Chapter 8 owners shows that the canonical public surface is the generated multiplier and
primal iterate sequences from `dual_projected_subgradient_method` together with source-faithful
same-file owners for the two averaged iterates. Since `source/` is unavailable in this repo, the
repair follows the item text and proof diagnostic: if a window already contains a zero-constraint
iterate, the repaired owner uses the current stationary iterate `x^k` instead of silently
removing those indices through Lean's totalized division by zero. The source proof chooses its
test multiplier from the positive part of the averaged constraint vector, so the controlled
residual is the existing Chapter 8 owner `positive_constraint_violation`, not the full Euclidean
norm of `g(x)`. The only new local bridge is the Euclidean multiplier-vector coercion needed to
state the norm term `‖λ^k‖₂`. -/

-- Proof sketch: apply the one-step multiplier recursion with `p = 0` and choose the test
-- multiplier from the positive part of the averaged constraint vector to obtain (8.70).
/-- Lemma 8.45 (8.70): under Assumption 8.41, if the constraint vectors satisfy `‖g(x)‖₂ ≤ L`
on `X`, then for every `k ≥ 2` the full-history averaged iterate generated by the dual projected
subgradient method satisfies the source-faithful objective-plus-positive-constraint-violation
bound (8.70). -/
theorem dual_projected_subgradient_full_average_gap_le
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hρ : 0 < ρ) {k : ℕ} (hk : 2 ≤ k) :
    f (fullAvg k) - fOpt +
        ρ * positive_constraint_violation gVec (fullAvg k) ≤
      (L / 2) *
        ((‖dual_projected_subgradient_multiplier_vector lam0‖ + ρ) ^ (2 : ℕ) +
            Finset.sum (Finset.range (k + 1)) fun n ↦ (γ n) ^ (2 : ℕ)) /
          Finset.sum (Finset.range (k + 1)) γ := by
  -- Route correction: the source proof's feasible optimizer witness is replaced by the proved
  -- GLB-based helper `dualProjectedSubgradientPrimalGapLeNegMultiplierPairing`, because
  -- `IsMinOn` does not encode set membership in the current Chapter 8 API.
  have hk_nonneg : 0 ≤ k := by
    omega
  have htail0 : Finset.Icc 0 k = Finset.range (k + 1) := by
    ext n
    simp [Finset.mem_Icc]
  by_cases hzero : ∃ n : Fin (k + 1), constraintSeq n = 0
  · rcases hzero with ⟨n, hn⟩
    have hcurrent :
        constraintSeq k = 0 := by
      exact constraintSeqEqZeroOfLeOfConstraintEqZero
        (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0)
        (n := n) (k := k) (Nat.le_of_lt_succ n.is_lt) hn
    have havg :
        fullAvg k = (xSeq k : E) :=
      dual_projected_subgradient_full_average_iterate_eq_current_of_exists_constraint_eq_zero
        (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0) ⟨n, hn⟩
    have hwindow :=
      windowPenalizedGapLeOfCurrentConstraintEqZero
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
        (L := L) (xSel := xSel) (γ := γ) (lam0 := lam0)
        h_problem h_admissible h_constraint_bound (p := 0) (k := k)
        hk_nonneg hcurrent ρ
    -- In the zero branch the repaired average is exactly the current iterate.
    simpa [havg, htail0, dual_projected_subgradient_method_zero] using hwindow
  · have hactive : ∀ n : Fin (k + 1), constraintSeq n ≠ 0 := by
      intro n
      exact fun hn ↦ hzero ⟨n, hn⟩
    have hden_pos :
        0 < Finset.sum (Finset.Icc 0 k) (fun j ↦ γ j / ‖constraintSeq j‖) := by
      have h0_mem : 0 ∈ Finset.Icc 0 k := by simp
      have h0_nonzero : constraintSeq 0 ≠ 0 := hactive 0
      have hterm_nonneg :
          ∀ j ∈ Finset.Icc 0 k, 0 ≤ γ j / ‖constraintSeq j‖ := by
        intro j hj
        exact div_nonneg
          (le_of_lt (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible j))
          (norm_nonneg _)
      have h0_term_pos : 0 < γ 0 / ‖constraintSeq 0‖ := by
        exact div_pos
          (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible 0)
          (norm_pos_iff.mpr h0_nonzero)
      have hle :
          γ 0 / ‖constraintSeq 0‖ ≤
            Finset.sum (Finset.Icc 0 k) (fun j ↦ γ j / ‖constraintSeq j‖) :=
        Finset.single_le_sum hterm_nonneg h0_mem
      exact lt_of_lt_of_le h0_term_pos hle
    have hwindow :=
      windowPenalizedGapLeOfActiveWindow
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
        (L := L) (xSel := xSel) (γ := γ) (lam0 := lam0)
        h_problem h_admissible h_constraint_bound (p := 0) (k := k)
        hk_nonneg hρ (fun n hn ↦ hactive ⟨n, by simpa [Finset.mem_Icc] using hn⟩)
    have hbridge :=
      fullWindowIndexBridge
        (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0) hactive
    -- In the active branch the repaired average matches the canonical weighted window sum.
    simpa [hbridge, htail0, dual_projected_subgradient_method_zero] using hwindow

-- Proof sketch: apply the same averaged inequality with the suffix-window choice `p = k / 2`
-- and the positive-part test multiplier to obtain (8.71).
/-- Lemma 8.45 (8.71): under Assumption 8.41, if the constraint vectors satisfy `‖g(x)‖₂ ≤ L`
on `X`, then for every `k ≥ 2` the suffix-window averaged iterate generated by the dual projected
subgradient method satisfies the source-faithful objective-plus-positive-constraint-violation
bound (8.71). -/
theorem dual_projected_subgradient_partial_average_gap_le
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hρ : 0 < ρ) {k : ℕ} (hk : 2 ≤ k) :
    f (partialAvg k) - fOpt +
        ρ * positive_constraint_violation gVec (partialAvg k) ≤
      (L / 2) *
        ((‖lamVecSeq (k / 2)‖ + ρ) ^ (2 : ℕ) +
            Finset.sum (Finset.Icc (k / 2) k) fun n ↦ (γ n) ^ (2 : ℕ)) /
          Finset.sum (Finset.Icc (k / 2) k) γ := by
  by_cases hzero : ∃ n ∈ Finset.Icc (k / 2) k, constraintSeq n = 0
  · rcases hzero with ⟨n, hn, hconstraint⟩
    have hk_div_le : k / 2 ≤ k := by
      omega
    have hnk : n ≤ k := (Finset.mem_Icc.mp hn).2
    have hcurrent :
        constraintSeq k = 0 := by
      exact constraintSeqEqZeroOfLeOfConstraintEqZero
        (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0)
        hnk hconstraint
    have havg :
        partialAvg k = (xSeq k : E) :=
      dual_projected_subgradient_partial_average_iterate_eq_current_of_exists_constraint_eq_zero
        (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0) ⟨n, hn, hconstraint⟩
    have hwindow :=
      windowPenalizedGapLeOfCurrentConstraintEqZero
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
        (L := L) (xSel := xSel) (γ := γ) (lam0 := lam0)
        h_problem h_admissible h_constraint_bound
        (p := k / 2) (k := k) hk_div_le hcurrent ρ
    -- A zero constraint inside the suffix window freezes the sequence at the current iterate.
    simpa [havg] using hwindow
  · have hactive : ∀ n ∈ Finset.Icc (k / 2) k, constraintSeq n ≠ 0 := by
      intro n hn
      exact fun hconstraint ↦ hzero ⟨n, hn, hconstraint⟩
    have hk_div_le : k / 2 ≤ k := by
      omega
    have hp_mem : k / 2 ∈ Finset.Icc (k / 2) k := by
      exact Finset.mem_Icc.mpr ⟨le_rfl, hk_div_le⟩
    have hden_pos :
        0 < Finset.sum (Finset.Icc (k / 2) k) (fun j ↦ γ j / ‖constraintSeq j‖) := by
      have hterm_nonneg :
          ∀ j ∈ Finset.Icc (k / 2) k, 0 ≤ γ j / ‖constraintSeq j‖ := by
        intro j hj
        exact div_nonneg
          (le_of_lt (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible j))
          (norm_nonneg _)
      have hp_term_pos : 0 < γ (k / 2) / ‖constraintSeq (k / 2)‖ := by
        exact div_pos
          (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) (xSel := xSel) (γ := γ) h_admissible (k / 2))
          (norm_pos_iff.mpr (hactive (k / 2) hp_mem))
      have hle :
          γ (k / 2) / ‖constraintSeq (k / 2)‖ ≤
            Finset.sum (Finset.Icc (k / 2) k) (fun j ↦ γ j / ‖constraintSeq j‖) :=
        Finset.single_le_sum hterm_nonneg hp_mem
      exact lt_of_lt_of_le hp_term_pos hle
    have hwindow :=
      windowPenalizedGapLeOfActiveWindow
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
        (L := L) (xSel := xSel) (γ := γ) (lam0 := lam0)
        h_problem h_admissible h_constraint_bound
        (p := k / 2) (k := k) hk_div_le hρ hactive
    have havg :=
      dual_projected_subgradient_partial_average_iterate_eq_weighted_sum
        (X := X) (g := g) (xSel := xSel) (γ := γ) (lam0 := lam0) hactive
    -- On the active suffix window the repaired average is the canonical weighted sum itself.
    simpa [havg] using hwindow

end

end
