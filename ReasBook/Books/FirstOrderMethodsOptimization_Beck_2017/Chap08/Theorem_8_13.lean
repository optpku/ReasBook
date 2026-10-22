/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_10
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_11
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
open scoped BigOperators

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → EReal) (C XStar : Set E) (fOpt : ℝ)
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/-- Helper for Theorem 8.13: the objective gap at the `k`-th projected-subgradient iterate. -/
abbrev objective_gap (k : ℕ) : ℝ := (f (x[k] : E)).toReal - fOpt

local notation "gap" =>
  objective_gap (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
    (g := g) (t := t) (x0 := x0)

/-- Helper for Theorem 8.13: every projected-subgradient iterate has objective value at least the
recorded optimum `fOpt`. -/
lemma objective_gap_nonneg_at_iterate (k : ℕ) :
    0 ≤ gap k := by
  -- Feasibility places the current objective value in the image set controlled by the GLB data.
  have hxk_image : f (x[k] : E) ∈ f '' C := by
    exact ⟨(x[k] : E), (x[k]).property, rfl⟩
  have hlower : (fOpt : EReal) ≤ f (x[k] : E) :=
    h_problem.optimal_value_isGLB.left hxk_image
  have hxk_dom : (x[k] : E) ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain (x[k]).property)
  have hxk_top : f (x[k] : E) ≠ ⊤ := ne_of_lt hxk_dom
  have hxk_bot : f (x[k] : E) ≠ ⊥ := h_problem.ne_bot _
  have hreal : (fOpt : EReal) ≤ (((f (x[k] : E)).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hxk_top hxk_bot] using hlower
  have hreal' : fOpt ≤ (f (x[k] : E)).toReal := EReal.coe_le_coe_iff.mp hreal
  linarith

/-- Helper for Theorem 8.13: if the selected subgradient vanishes, then the current objective gap
also vanishes. -/
lemma objective_gap_eq_zero_of_zero_selected_subgradient
    (h_subgrad :
      ∀ k,
        (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ subdifferential f (x[k] : E))
    (k : ℕ) (hg0 : g k (x[k]) = 0) :
    gap k = 0 := by
  -- The Chapter 8 subgradient-gap lemma turns the zero subgradient branch into a zero gap branch.
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  have hgap_le :
      gap k ≤ inner ℝ (g k (x[k])) ((x[k] : E) - xStar) :=
    subgradient_gap_le_inner_at_iterate
      h_problem
      (fun n ↦ by
        simpa [projected_subgradient_method_iterate, mem_strongDualSubdifferential] using
          h_subgrad n)
      hxStar k
  have hgap_nonneg : 0 ≤ gap k :=
    objective_gap_nonneg_at_iterate
      (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
      (g := g) (t := t) (x0 := x0) k
  have hgap_le_zero : gap k ≤ 0 := by
    simpa [hg0] using hgap_le
  linarith

/-- Helper for Theorem 8.13: one Polyak step decreases the squared distance to any optimal point
by at least the squared objective gap divided by `L_f^2`. -/
lemma polyak_sqdist_drop_le_squared_gap_div_Lf_sq
    (h_norm : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ k,
        (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ subdifferential f (x[k] : E))
    (h_polyak :
      ∀ k,
        t k = polyak_stepsize f fOpt (x[k] : E) (g k (x[k])))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖(x[k + 1] : E) - xStar‖ ^ (2 : ℕ) ≤
      ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) - gap k ^ (2 : ℕ) / h_norm.L_f ^ (2 : ℕ) := by
  by_cases hg0 : g k (x[k]) = 0
  · -- In the zero-subgradient branch, the Polyak rule gives zero objective gap, so only
    -- nonexpansiveness of projection is needed.
    have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
      simpa [h_problem.optimal_set_eq] using hxStar
    have hxkp1 :
        (x[k + 1] : E) =
          metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
            h_problem.feasible_convex ((x[k] : E) - t k • g k (x[k])) := by
      exact congrArg (fun z : C ↦ (z : E))
        (projected_subgradient_method_succ C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex g t x0 k)
    have hxStar_proj :
        (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
          h_problem.feasible_convex xStar : E) = xStar := by
      simpa [projectionPoint] using
        projectionPoint_eq_self_of_mem C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex hxStar_data.1
    have hdist :
        ‖(x[k + 1] : E) - xStar‖ ≤ ‖((x[k] : E) - t k • g k (x[k])) - xStar‖ := by
      -- Compare the next iterate with the projection of the optimal point.
      simpa [hxkp1, hxStar_proj, dist_eq_norm] using
        LipschitzWith.dist_le_mul
          (metricProjection_nonexpansive C h_problem.feasible_nonempty
            h_problem.feasible_closed h_problem.feasible_convex)
          ((x[k] : E) - t k • g k (x[k])) xStar
    have hsq :
        ‖(x[k + 1] : E) - xStar‖ ^ (2 : ℕ) ≤
          ‖((x[k] : E) - t k • g k (x[k])) - xStar‖ ^ (2 : ℕ) := by
      rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
      exact hdist
    have hgap_zero :
        gap k = 0 :=
      objective_gap_eq_zero_of_zero_selected_subgradient
        (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
        (g := g) (t := t) (x0 := x0) h_subgrad k hg0
    have ht_one : t k = 1 := by
      rw [h_polyak k, hg0, polyak_stepsize_zero]
    have hupdate :
        ((x[k] : E) - t k • g k (x[k])) = (x[k] : E) := by
      rw [hg0, ht_one]
      simp
    simpa [hupdate, hgap_zero]
      using hsq
  · -- Route correction: avoid the false all-stepsizes route in `Lemma_8_11`; here the Polyak
    -- formula gives the needed sign information directly.
    have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
      simpa [h_problem.optimal_set_eq] using hxStar
    have hxkp1 :
        (x[k + 1] : E) =
          metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
            h_problem.feasible_convex ((x[k] : E) - t k • g k (x[k])) := by
      exact congrArg (fun z : C ↦ (z : E))
        (projected_subgradient_method_succ C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex g t x0 k)
    have hxStar_proj :
        (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
          h_problem.feasible_convex xStar : E) = xStar := by
      simpa [projectionPoint] using
        projectionPoint_eq_self_of_mem C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex hxStar_data.1
    have hdist :
        ‖(x[k + 1] : E) - xStar‖ ≤ ‖((x[k] : E) - t k • g k (x[k])) - xStar‖ := by
      -- Nonexpansiveness reduces the problem to the unprojected update.
      simpa [hxkp1, hxStar_proj, dist_eq_norm] using
        LipschitzWith.dist_le_mul
          (metricProjection_nonexpansive C h_problem.feasible_nonempty
            h_problem.feasible_closed h_problem.feasible_convex)
          ((x[k] : E) - t k • g k (x[k])) xStar
    have hsq :
        ‖(x[k + 1] : E) - xStar‖ ^ (2 : ℕ) ≤
          ‖((x[k] : E) - t k • g k (x[k])) - xStar‖ ^ (2 : ℕ) := by
      rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
      exact hdist
    have hgap_nonneg : 0 ≤ gap k :=
      objective_gap_nonneg_at_iterate
        (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
        (g := g) (t := t) (x0 := x0) k
    have ht_nonneg : 0 ≤ t k := by
      rw [h_polyak k, polyak_stepsize_of_ne_zero _ _ _ _ hg0]
      exact div_nonneg hgap_nonneg (sq_nonneg ‖g k (x[k])‖)
    have hgap_le_inner :
        gap k ≤ inner ℝ ((x[k] : E) - xStar) (g k (x[k])) := by
      -- The subgradient inequality supplies the source cross-term estimate.
      simpa [real_inner_comm] using
        subgradient_gap_le_inner_at_iterate
          h_problem
          (fun n ↦ by
            simpa [projected_subgradient_method_iterate, mem_strongDualSubdifferential] using
              h_subgrad n)
          hxStar k
    have hexpand :
        ‖((x[k] : E) - t k • g k (x[k])) - xStar‖ ^ (2 : ℕ) =
          ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) -
            2 * t k * inner ℝ ((x[k] : E) - xStar) (g k (x[k])) +
              (t k) ^ (2 : ℕ) * ‖g k (x[k])‖ ^ (2 : ℕ) := by
      -- Expand the square of the explicit gradient step.
      have hrewrite :
          ((x[k] : E) - t k • g k (x[k])) - xStar =
            ((x[k] : E) - xStar) - t k • g k (x[k]) := by
        abel
      rw [hrewrite, norm_sub_sq_real]
      rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
      ring
    have hstep_gap :
        ‖((x[k] : E) - t k • g k (x[k])) - xStar‖ ^ (2 : ℕ) ≤
          ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) -
            2 * t k * gap k +
              (t k) ^ (2 : ℕ) * ‖g k (x[k])‖ ^ (2 : ℕ) := by
      rw [hexpand]
      nlinarith
    have ht_formula :
        t k = gap k / ‖g k (x[k])‖ ^ (2 : ℕ) := by
      rw [h_polyak k, polyak_stepsize_of_ne_zero _ _ _ _ hg0]
    have hnorm_sq_ne_zero : ‖g k (x[k])‖ ^ (2 : ℕ) ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hg0)
    have hpolyak_exact :
        ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) -
            2 * t k * gap k +
              (t k) ^ (2 : ℕ) * ‖g k (x[k])‖ ^ (2 : ℕ) =
          ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) - gap k ^ (2 : ℕ) / ‖g k (x[k])‖ ^ (2 : ℕ) := by
      rw [ht_formula]
      field_simp [hnorm_sq_ne_zero]
      ring
    have hsubgrad_strong :
        toDualMap ℝ E (g k (x[k])) ∈ strongDualSubdifferential f (x[k] : E) := by
      simpa [mem_strongDualSubdifferential] using h_subgrad k
    have hnorm_le :
        ‖g k (x[k])‖ ≤ h_norm.L_f := by
      simpa using
        h_norm.norm_le (x := (x[k] : E)) (g := toDualMap ℝ E (g k (x[k])))
          (x[k]).property hsubgrad_strong
    have hnorm_sq_le :
        ‖g k (x[k])‖ ^ (2 : ℕ) ≤ h_norm.L_f ^ (2 : ℕ) := by
      rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (le_of_lt h_norm.L_f_pos)]
      exact hnorm_le
    have hfrac_le :
        gap k ^ (2 : ℕ) / h_norm.L_f ^ (2 : ℕ) ≤
          gap k ^ (2 : ℕ) / ‖g k (x[k])‖ ^ (2 : ℕ) := by
      have hLf_sq_pos : 0 < h_norm.L_f ^ (2 : ℕ) := by
        nlinarith [h_norm.L_f_pos]
      have hnorm_sq_pos : 0 < ‖g k (x[k])‖ ^ (2 : ℕ) := by
        have hnorm_pos : 0 < ‖g k (x[k])‖ := norm_pos_iff.mpr hg0
        nlinarith
      exact div_le_div_of_nonneg_left (sq_nonneg (gap k)) hnorm_sq_pos hnorm_sq_le
    have hdrop_to_Lf :
        ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) - gap k ^ (2 : ℕ) / ‖g k (x[k])‖ ^ (2 : ℕ) ≤
          ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) - gap k ^ (2 : ℕ) / h_norm.L_f ^ (2 : ℕ) := by
      linarith
    calc
      ‖(x[k + 1] : E) - xStar‖ ^ (2 : ℕ) ≤
          ‖((x[k] : E) - t k • g k (x[k])) - xStar‖ ^ (2 : ℕ) := hsq
      _ ≤ ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) -
            2 * t k * gap k +
              (t k) ^ (2 : ℕ) * ‖g k (x[k])‖ ^ (2 : ℕ) := hstep_gap
      _ = ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) -
            gap k ^ (2 : ℕ) / ‖g k (x[k])‖ ^ (2 : ℕ) := hpolyak_exact
      _ ≤ ‖(x[k] : E) - xStar‖ ^ (2 : ℕ) -
            gap k ^ (2 : ℕ) / h_norm.L_f ^ (2 : ℕ) := hdrop_to_Lf

/-- Helper for Theorem 8.13: the squared objective gaps have a telescoping prefix bound in terms
of the initial squared distance to an optimal point. -/
lemma polyak_squared_gap_prefix_sum_le_initial_sqdist
    (h_norm : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ k,
        (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ subdifferential f (x[k] : E))
    (h_polyak :
      ∀ k,
        t k = polyak_stepsize f fOpt (x[k] : E) (g k (x[k])))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ gap n ^ (2 : ℕ)) ≤
      h_norm.L_f ^ (2 : ℕ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) := by
  -- First telescope the one-step estimate over the whole prefix.
  have hprefix :
      ∀ n : ℕ,
        Finset.sum (Finset.range n) (fun i ↦ gap i ^ (2 : ℕ)) ≤
          h_norm.L_f ^ (2 : ℕ) *
            (‖(x0 : E) - xStar‖ ^ (2 : ℕ) - ‖(x[n] : E) - xStar‖ ^ (2 : ℕ)) := by
    intro n
    induction n with
    | zero =>
        rw [projected_subgradient_method_zero]
        simp
    | succ n hn =>
        have hstep :
            gap n ^ (2 : ℕ) ≤
              h_norm.L_f ^ (2 : ℕ) *
                (‖(x[n] : E) - xStar‖ ^ (2 : ℕ) - ‖(x[n + 1] : E) - xStar‖ ^ (2 : ℕ)) := by
          have hdrop :=
            polyak_sqdist_drop_le_squared_gap_div_Lf_sq
              (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
              (g := g) (t := t) (x0 := x0) h_norm h_subgrad h_polyak hxStar n
          have hLf_sq_pos : 0 < h_norm.L_f ^ (2 : ℕ) := by
            nlinarith [h_norm.L_f_pos]
          have hscaled :
              gap n ^ (2 : ℕ) ≤
                h_norm.L_f ^ (2 : ℕ) *
                  (‖(x[n] : E) - xStar‖ ^ (2 : ℕ) - ‖(x[n + 1] : E) - xStar‖ ^ (2 : ℕ)) := by
            have htmp :
                gap n ^ (2 : ℕ) / h_norm.L_f ^ (2 : ℕ) ≤
                  ‖(x[n] : E) - xStar‖ ^ (2 : ℕ) - ‖(x[n + 1] : E) - xStar‖ ^ (2 : ℕ) := by
              linarith
            have hmul :=
              mul_le_mul_of_nonneg_left htmp (le_of_lt hLf_sq_pos)
            have hLf_ne : h_norm.L_f ≠ 0 := ne_of_gt h_norm.L_f_pos
            have hLf_sq_ne : h_norm.L_f ^ (2 : ℕ) ≠ 0 := ne_of_gt hLf_sq_pos
            have hcancel :
                h_norm.L_f ^ (2 : ℕ) * (gap n ^ (2 : ℕ) / h_norm.L_f ^ (2 : ℕ)) =
                  gap n ^ (2 : ℕ) := by
              field_simp [hLf_ne]
            calc
              gap n ^ (2 : ℕ) =
                  h_norm.L_f ^ (2 : ℕ) * (gap n ^ (2 : ℕ) / h_norm.L_f ^ (2 : ℕ)) := by
                    simpa using hcancel.symm
              _ ≤ h_norm.L_f ^ (2 : ℕ) *
                    (‖(x[n] : E) - xStar‖ ^ (2 : ℕ) - ‖(x[n + 1] : E) - xStar‖ ^ (2 : ℕ)) := hmul
          exact hscaled
        rw [Finset.sum_range_succ]
        have hcombine :
            Finset.sum (Finset.range n) (fun i ↦ gap i ^ (2 : ℕ)) + gap n ^ (2 : ℕ) ≤
              h_norm.L_f ^ (2 : ℕ) *
                (‖(x0 : E) - xStar‖ ^ (2 : ℕ) - ‖(x[n] : E) - xStar‖ ^ (2 : ℕ)) +
                  h_norm.L_f ^ (2 : ℕ) *
                    (‖(x[n] : E) - xStar‖ ^ (2 : ℕ) - ‖(x[n + 1] : E) - xStar‖ ^ (2 : ℕ)) := by
          linarith
        have hring :
            h_norm.L_f ^ (2 : ℕ) *
                (‖(x0 : E) - xStar‖ ^ (2 : ℕ) - ‖(x[n] : E) - xStar‖ ^ (2 : ℕ)) +
                  h_norm.L_f ^ (2 : ℕ) *
                    (‖(x[n] : E) - xStar‖ ^ (2 : ℕ) - ‖(x[n + 1] : E) - xStar‖ ^ (2 : ℕ)) =
              h_norm.L_f ^ (2 : ℕ) *
                (‖(x0 : E) - xStar‖ ^ (2 : ℕ) - ‖(x[n + 1] : E) - xStar‖ ^ (2 : ℕ)) := by
          ring
        exact hcombine.trans_eq hring
  have hdrop_nonneg : 0 ≤ ‖(x[k + 1] : E) - xStar‖ ^ (2 : ℕ) := sq_nonneg _
  have hmain := hprefix (k + 1)
  nlinarith

/-- Helper for Theorem 8.13: the running-best objective gap controls every squared gap in the
prefix from below. -/
lemma best_value_gap_sq_mul_le_squared_gap_prefix_sum
    (k : ℕ) :
    (k + 1 : ℝ) *
        (best_achieved_function_value (fun y ↦ (f y).toReal) (fun n ↦ (x[n] : E)) k - fOpt) ^
          (2 : ℕ) ≤
      Finset.sum (Finset.range (k + 1)) (fun n ↦ gap n ^ (2 : ℕ)) := by
  let bestGap :=
    best_achieved_function_value (fun y ↦ (f y).toReal) (fun n ↦ (x[n] : E)) k - fOpt
  have hbest_lower :
      fOpt ≤ best_achieved_function_value (fun y ↦ (f y).toReal) (fun n ↦ (x[n] : E)) k := by
    -- Every attained prefix value lies above `fOpt`, so the finite minimum does as well.
    unfold best_achieved_function_value
    apply Finset.le_min'
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
    exact sub_nonneg.mp <|
      objective_gap_nonneg_at_iterate
        (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
        (g := g) (t := t) (x0 := x0) n
  have hbest_nonneg : 0 ≤ bestGap := by
    dsimp [bestGap]
    linarith
  have hpointwise :
      ∀ n ∈ Finset.range (k + 1), bestGap ^ (2 : ℕ) ≤ gap n ^ (2 : ℕ) := by
    intro n hn
    have hbest_le :
        best_achieved_function_value (fun y ↦ (f y).toReal) (fun m ↦ (x[m] : E)) k ≤
          (f (x[n] : E)).toReal :=
      best_achieved_function_value_le_objective_value
        (fun y ↦ (f y).toReal) (fun m ↦ (x[m] : E)) k n hn
    have hgap_nonneg :
        0 ≤ gap n :=
      objective_gap_nonneg_at_iterate
        (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
        (g := g) (t := t) (x0 := x0) n
    have hgap_le : bestGap ≤ gap n := by
      dsimp [bestGap]
      linarith
    nlinarith
  have hsum_le :
      Finset.sum (Finset.range (k + 1)) (fun _ ↦ bestGap ^ (2 : ℕ)) ≤
        Finset.sum (Finset.range (k + 1)) (fun n ↦ gap n ^ (2 : ℕ)) := by
    exact Finset.sum_le_sum hpointwise
  simpa [bestGap, Finset.card_range] using hsum_le

-- Proof sketch: start from Lemma 8.11 and rewrite the stepsize by `h_polyak`. If the chosen
-- subgradient vanishes, then `polyak_stepsize_zero` and optimality give equality. If it is
-- nonzero, use `polyak_stepsize_of_ne_zero` together with the norm bound from Assumption 8.12 to
-- obtain the sharper descent estimate `‖x[k + 1] - xStar‖² ≤ ‖x[k] - xStar‖²`.
/-- Theorem 8.13 (1): clause (a). Under Assumptions 8.7 and 8.12, the projected subgradient method
with Polyak's stepsize rule has nonincreasing squared distance to every optimal point
`xStar ∈ XStar`. -/
theorem projected_subgradient_method_sqdist_mono_of_polyak_stepsize
    (h_norm : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ k,
        (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ subdifferential f (x[k] : E))
    (h_polyak :
      ∀ k,
        t k = polyak_stepsize f fOpt (x[k] : E) (g k (x[k])))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖(x[k + 1] : E) - xStar‖ ^ 2 ≤ ‖(x[k] : E) - xStar‖ ^ 2 := by
  -- The stronger one-step descent estimate already contains clause (a); drop the nonnegative term.
  have hdrop :=
    polyak_sqdist_drop_le_squared_gap_div_Lf_sq
      (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
      (g := g) (t := t) (x0 := x0) h_norm h_subgrad h_polyak hxStar k
  have hfrac_nonneg : 0 ≤ gap k ^ (2 : ℕ) / h_norm.L_f ^ (2 : ℕ) := by
    have hLf_sq_nonneg : 0 ≤ h_norm.L_f ^ (2 : ℕ) := by
      nlinarith [h_norm.L_f_pos]
    exact div_nonneg (sq_nonneg (gap k)) hLf_sq_nonneg
  nlinarith

-- Proof sketch: use the descent inequality from clause (a) and the uniform norm bound from
-- Assumption 8.12 to deduce
-- `‖x[k + 1] - xStar‖² ≤ ‖x[k] - xStar‖² - ((f(x[k]) - fOpt)^2 / h_norm.L_f^2)`. Summing this
-- estimate shows the squared objective gaps are summable, hence `(f (x[k])).toReal - fOpt → 0`.
/-- Theorem 8.13 (2): clause (b). Under Assumptions 8.7 and 8.12, the objective values along the
projected subgradient method with Polyak's stepsize rule converge to the optimal value `fOpt`. -/
theorem projected_subgradient_method_objective_tendsto_of_polyak_stepsize
    (h_norm : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ k,
        (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ subdifferential f (x[k] : E))
    (h_polyak :
      ∀ k,
        t k = polyak_stepsize f fOpt (x[k] : E) (g k (x[k])))
    :
    Filter.Tendsto (fun k ↦ (f (x[k] : E)).toReal) Filter.atTop (nhds fOpt) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  -- The telescoping squared-gap bound gives a uniform bound on every prefix sum.
  have hsum_bound :
      ∀ n : ℕ,
        Finset.sum (Finset.range n) (fun i ↦ gap i ^ (2 : ℕ)) ≤
          h_norm.L_f ^ (2 : ℕ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) := by
    intro n
    cases n with
    | zero =>
        have hLf_sq_nonneg : 0 ≤ h_norm.L_f ^ (2 : ℕ) := by
          nlinarith [h_norm.L_f_pos]
        exact mul_nonneg hLf_sq_nonneg (sq_nonneg ‖(x0 : E) - xStar‖)
    | succ n =>
        simpa using
          polyak_squared_gap_prefix_sum_le_initial_sqdist
            (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
            (g := g) (t := t) (x0 := x0) h_norm h_subgrad h_polyak hxStar n
  have hsummable :
      Summable (fun n ↦ gap n ^ (2 : ℕ)) :=
    summable_of_sum_range_le (fun n ↦ sq_nonneg (gap n)) hsum_bound
  have hsq_tendsto_zero :
      Filter.Tendsto (fun n ↦ gap n ^ (2 : ℕ)) Filter.atTop (nhds 0) :=
    hsummable.tendsto_atTop_zero
  have hgap_eq_sqrt :
      ∀ n : ℕ, gap n = Real.sqrt (gap n ^ (2 : ℕ)) := by
    intro n
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    exact objective_gap_nonneg_at_iterate
      (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
      (g := g) (t := t) (x0 := x0) n
  have hgap_tendsto_zero :
      Filter.Tendsto (fun n ↦ gap n) Filter.atTop (nhds 0) := by
    -- Nonnegativity lets us recover `gap n` from the square-root of `gap n^2`.
    have hsqrt_tendsto :
        Filter.Tendsto (fun n ↦ Real.sqrt (gap n ^ (2 : ℕ))) Filter.atTop (nhds 0) := by
      simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hsq_tendsto_zero
    have hEq : (fun n ↦ gap n) = fun n ↦ Real.sqrt (gap n ^ (2 : ℕ)) := by
      funext n
      exact hgap_eq_sqrt n
    rw [hEq]
    exact hsqrt_tendsto
  -- Add back the constant `fOpt` to recover objective convergence.
  simpa [objective_gap, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    hgap_tendsto_zero.const_add fOpt

-- Proof sketch: combine the square-summability estimate from clause (b) with the defining minimum
-- property of `best_achieved_function_value` on the prefix `0, …, k`. This bounds the finite sum
-- of squared gaps below by `(k + 1)` times the squared best gap, and rearranging yields the
-- `O((k + 1)⁻¹ᐟ²)` rate in terms of the distance from `x0` to `XStar`.
/-- Theorem 8.13 (3): clause (c). Under Assumptions 8.7 and 8.12, the best objective value found
by the first `k + 1` projected-subgradient iterates with Polyak's stepsize rule satisfies the
rate bound `f_best^k - fOpt ≤ L_f d_{X^*}(x^0) / √(k + 1)`. -/
theorem projected_subgradient_method_best_value_gap_le_of_polyak_stepsize
    (h_norm : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ k,
        (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ subdifferential f (x[k] : E))
    (h_polyak :
      ∀ k,
        t k = polyak_stepsize f fOpt (x[k] : E) (g k (x[k])))
    (k : ℕ) :
    best_achieved_function_value (fun y ↦ (f y).toReal) (fun n ↦ (x[n] : E)) k - fOpt ≤
      h_norm.L_f * Metric.infDist (x0 : E) XStar / Real.sqrt (k + 1) := by
  let bestGap :=
    best_achieved_function_value (fun y ↦ (f y).toReal) (fun n ↦ (x[n] : E)) k - fOpt
  have hbest_nonneg : 0 ≤ bestGap := by
    -- The running best is still bounded below by the optimal value.
    have hbest_lower :
        fOpt ≤ best_achieved_function_value (fun y ↦ (f y).toReal) (fun n ↦ (x[n] : E)) k := by
      unfold best_achieved_function_value
      apply Finset.le_min'
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
      exact sub_nonneg.mp <|
        objective_gap_nonneg_at_iterate
          (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
          (g := g) (t := t) (x0 := x0) n
    dsimp [bestGap]
    linarith
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
    have hk_pos : 0 < (k : ℝ) + 1 := by
      positivity
    exact Real.sqrt_pos.mpr hk_pos
  have hscaled_le_dist :
      ∀ {xStar : E}, xStar ∈ XStar →
        bestGap * Real.sqrt ((k : ℝ) + 1) / h_norm.L_f ≤ dist (x0 : E) xStar := by
    intro xStar hxStar
    have hprefix :=
      polyak_squared_gap_prefix_sum_le_initial_sqdist
        (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
        (g := g) (t := t) (x0 := x0) h_norm h_subgrad h_polyak hxStar k
    have hbest_sq :=
      best_value_gap_sq_mul_le_squared_gap_prefix_sum
        (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
        (g := g) (t := t) (x0 := x0) k
    have hmain_sq :
        ((k + 1 : ℝ) * bestGap ^ (2 : ℕ)) ≤
          h_norm.L_f ^ (2 : ℕ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) := by
      dsimp [bestGap] at hbest_sq ⊢
      exact hbest_sq.trans hprefix
    have hmul_sq :
        (bestGap * Real.sqrt ((k : ℝ) + 1)) ^ (2 : ℕ) ≤
          (h_norm.L_f * ‖(x0 : E) - xStar‖) ^ (2 : ℕ) := by
      have hsqrt_sq : Real.sqrt ((k : ℝ) + 1) ^ (2 : ℕ) = (k : ℝ) + 1 := by
        exact Real.sq_sqrt (by positivity)
      nlinarith [hmain_sq, hsqrt_sq]
    have hmul :
        bestGap * Real.sqrt ((k : ℝ) + 1) ≤ h_norm.L_f * ‖(x0 : E) - xStar‖ := by
      have hright_nonneg : 0 ≤ h_norm.L_f * ‖(x0 : E) - xStar‖ := by
        exact mul_nonneg (le_of_lt h_norm.L_f_pos) (norm_nonneg _)
      nlinarith
    have hmul_div :
        bestGap * Real.sqrt ((k : ℝ) + 1) / h_norm.L_f ≤ ‖(x0 : E) - xStar‖ := by
      have hscaled :=
        mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr (le_of_lt h_norm.L_f_pos))
      have hLf_ne : h_norm.L_f ≠ 0 := ne_of_gt h_norm.L_f_pos
      simpa [div_eq_mul_inv, hLf_ne, mul_assoc, mul_left_comm, mul_comm] using hscaled
    simpa [dist_eq_norm] using hmul_div
  have hscaled_le_infDist :
      bestGap * Real.sqrt ((k : ℝ) + 1) / h_norm.L_f ≤ Metric.infDist (x0 : E) XStar := by
    -- Use the arbitrary-optimal-point estimate to pass from a chosen minimizer to `infDist`.
    exact (Metric.le_infDist h_problem.optimal_set_nonempty).2 <|
      by
        intro xStar hxStar
        exact hscaled_le_dist hxStar
  have hmul :
      bestGap * Real.sqrt ((k : ℝ) + 1) ≤ h_norm.L_f * Metric.infDist (x0 : E) XStar := by
    have hscaled :=
      mul_le_mul_of_nonneg_right hscaled_le_infDist (le_of_lt h_norm.L_f_pos)
    have hLf_ne : h_norm.L_f ≠ 0 := ne_of_gt h_norm.L_f_pos
    simpa [div_eq_mul_inv, hLf_ne, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hfinal_mul :
      bestGap * Real.sqrt ((k : ℝ) + 1) ≤
        (h_norm.L_f * Metric.infDist (x0 : E) XStar / Real.sqrt ((k : ℝ) + 1)) *
          Real.sqrt ((k : ℝ) + 1) := by
    have hsqrt_ne : Real.sqrt ((k : ℝ) + 1) ≠ 0 := ne_of_gt hsqrt_pos
    simpa [div_eq_mul_inv, hsqrt_ne, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hfinal :
      bestGap ≤ h_norm.L_f * Metric.infDist (x0 : E) XStar / Real.sqrt ((k : ℝ) + 1) :=
    le_of_mul_le_mul_right hfinal_mul hsqrt_pos
  simpa [bestGap] using hfinal

end
