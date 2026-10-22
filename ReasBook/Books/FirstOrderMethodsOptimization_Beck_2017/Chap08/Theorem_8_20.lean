/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_41
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_19
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_20
import FirstOrderMethodsOptimization_Beck_2017.Chap08.DualConstraintVector
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {m : ℕ}
variable {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {fOpt : ℝ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)
local notation "Eq0" => EuclideanSpace ℝ (Fin 0)
local notation "q" => lagrangian_dual_objective X f (dual_constraint_vector g)

/-- Helper for Theorem 8.20: the `i`-th standard coordinate vector in the Euclidean multiplier
space `Λ = ℝ^m`. -/
abbrev dualProjectedSubgradientBasisVector (i : Fin m) : Λ :=
  WithLp.toLp 2 (Pi.single i (1 : ℝ))

/-- Helper for Theorem 8.20: the multiplier vector read off from a linear functional on `Λ` by
negating its values on the standard coordinate vectors. -/
abbrev dualProjectedSubgradientMultiplierOfFunctional
    (phi : Module.Dual ℝ Λ) : Λ :=
  WithLp.toLp 2 (fun i : Fin m ↦ -(phi (dualProjectedSubgradientBasisVector i)))

/-- Helper for Theorem 8.20: the inequality-only perturbation value function obtained by
specializing Chapter 3's `value_function` to the Chapter 8 inequality family and a trivial
equality space. -/
abbrev dualProjectedSubgradientPerturbationValue
    (X : Set E) (f : E → ℝ) (g : Fin m → E → ℝ) : Λ → EReal :=
  fun u ↦
    value_function
      X
      (fun x ↦ (f x : EReal))
      (fun i x ↦ (g i x : EReal))
      (0 : E →ₗ[ℝ] Eq0)
      0
      (u, 0)

/-- Helper for Theorem 8.20: every point satisfying the perturbed inequality slice gives an upper
bound on the specialized perturbation value function. -/
lemma dualProjectedSubgradientPerturbationValue_le_of_mem
    {u : Λ} {x : E}
    (hxX : x ∈ X)
    (hxg : ∀ i : Fin m, g i x ≤ u i) :
    dualProjectedSubgradientPerturbationValue X f g u ≤ (f x : EReal) := by
  -- Use `x` itself as a feasible witness in the perturbation slice at `u`.
  rw [dualProjectedSubgradientPerturbationValue, value_function_apply]
  refine sInf_le ?_
  refine ⟨x, ?_, rfl⟩
  rw [mem_value_function_feasible_set]
  refine ⟨hxX, ?_, by simp⟩
  intro i
  exact_mod_cast hxg i

/-- Helper for Theorem 8.20: every coordinate of a multiplier-space vector is bounded by its
Euclidean norm. -/
lemma abs_coord_le_norm (u : Λ) (i : Fin m) :
    |u i| ≤ ‖u‖ := by
  have hsq :
      ‖u i‖ ^ (2 : ℕ) ≤ ‖u‖ ^ (2 : ℕ) := by
    have hnorm_sq :
        ‖u‖ ^ (2 : ℕ) = ∑ j : Fin m, ‖u j‖ ^ (2 : ℕ) := by
      simpa using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin m ↦ ℝ) u)
    have hterm :
        ‖u i‖ ^ (2 : ℕ) ≤ ∑ j : Fin m, ‖u j‖ ^ (2 : ℕ) := by
      exact Finset.single_le_sum
        (fun j _ ↦ sq_nonneg ‖u j‖)
        (Finset.mem_univ i)
    calc
      ‖u i‖ ^ (2 : ℕ) ≤ ∑ j : Fin m, ‖u j‖ ^ (2 : ℕ) := hterm
      _ = ‖u‖ ^ (2 : ℕ) := by rw [← hnorm_sq]
  -- Compare nonnegative norms through their squares.
  rw [sq_le_sq, abs_of_nonneg (norm_nonneg (u i)), abs_of_nonneg (norm_nonneg u)] at hsq
  simpa [Real.norm_eq_abs] using hsq

/-- Helper for Theorem 8.20: a linear functional on the multiplier space is determined by its
values on the standard coordinate vectors, so the induced coefficient vector represents the
functional as the negative Euclidean dot product. -/
lemma dualProjectedSubgradientLinearFunctional_eq_negDotProduct
    (phi : Module.Dual ℝ Λ) :
    let lam : Λ := dualProjectedSubgradientMultiplierOfFunctional phi
    ∀ u : Λ, phi u = -dotProduct lam u := by
  intro lam u
  have hphi_sum :
      phi u = ∑ i : Fin m, u.ofLp i * phi (dualProjectedSubgradientBasisVector i) := by
    calc
      phi u = phi (∑ i : Fin m, u.ofLp i • dualProjectedSubgradientBasisVector i) := by
          congr 1
          ext j
          simp [dualProjectedSubgradientBasisVector, Pi.single_apply]
      _ = ∑ i : Fin m, u.ofLp i * phi (dualProjectedSubgradientBasisVector i) := by
            rw [map_sum]
            simp [dualProjectedSubgradientBasisVector]
  calc
    phi u = ∑ i : Fin m, u.ofLp i * phi (dualProjectedSubgradientBasisVector i) := hphi_sum
    _ = -dotProduct lam u := by
          simp [lam, dotProduct, dualProjectedSubgradientBasisVector, mul_comm]

/-- Helper for Theorem 8.20: the specialized perturbation value is antitone in the inequality
perturbation parameter. -/
lemma dualProjectedSubgradientPerturbationValue_antitone
    {u w : Λ} (huw : ∀ i : Fin m, u i ≤ w i) :
    dualProjectedSubgradientPerturbationValue X f g u ≥
      dualProjectedSubgradientPerturbationValue X f g w := by
  -- This is the inequality-only specialization of Chapter 3's general antitonicity owner.
  simpa [dualProjectedSubgradientPerturbationValue] using
    value_function_antitone_u
      X
      (fun x ↦ (f x : EReal))
      (fun i x ↦ (g i x : EReal))
      (0 : E →ₗ[ℝ] Eq0)
      0
      (t := (0 : Eq0))
      huw

/-- Helper for Theorem 8.20: the specialized perturbation value function is convex. -/
lemma dualProjectedSubgradientPerturbationValue_isConvex
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt) :
    is_convex_function (dualProjectedSubgradientPerturbationValue X f g) := by
  have hf_convex : is_convex_function (fun x : E ↦ (f x : EReal)) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro x hx
      simp
    · simpa [effective_domain] using h_problem.objective_convex
  have hg_convex : ∀ i : Fin m, is_convex_function (fun x : E ↦ (g i x : EReal)) := by
    intro i
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro x hx
      simp
    · simpa [effective_domain] using h_problem.constraint_convex i
  have hvalue_convex :
      is_convex_function
        (value_function
          X
          (fun x ↦ (f x : EReal))
          (fun i x ↦ (g i x : EReal))
          (0 : E →ₗ[ℝ] Eq0)
          0) :=
    value_function_is_convex
      X
      (fun x ↦ (f x : EReal))
      (fun i x ↦ (g i x : EReal))
      (0 : E →ₗ[ℝ] Eq0)
      0
      hf_convex
      hg_convex
      h_problem.feasible_convex
  -- Precompose the Chapter 3 convex perturbation owner with the inclusion `u ↦ (u, 0)`.
  simpa [dualProjectedSubgradientPerturbationValue] using
    is_convex_function_precompose_linearMap_add
      hvalue_convex
      (LinearMap.inl ℝ Λ Eq0)
      (0 : Λ × Eq0)

/-- Helper for Theorem 8.20: the zero perturbation slice of the specialized value function
recovers the primal optimal value `fOpt`. -/
lemma dualProjectedSubgradientPerturbationValue_zero_eq_fOpt
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt) :
    dualProjectedSubgradientPerturbationValue X f g 0 = (fOpt : EReal) := by
  rcases h_problem.slater_condition_on_X with ⟨xBar, hxBar, hgBar⟩
  let ownerValues : Set EReal :=
    (fun x : E ↦ (f x : EReal)) '' dual_projected_subgradient_feasible_set X g
  have howner_eq :
      (fun x : E ↦ (f x : EReal)) ''
          value_function_feasible_set
            X
            (fun i x ↦ (g i x : EReal))
            (0 : E →ₗ[ℝ] Eq0)
            0
            0
            0 =
        ownerValues := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      rcases (mem_value_function_feasible_set
          X
          (fun i x ↦ (g i x : EReal))
          (0 : E →ₗ[ℝ] Eq0)
          0
          0
          0
          x).1 hx with ⟨hxX, hxg, _⟩
      refine (mem_dual_projected_subgradient_feasible_set).2 ⟨hxX, ?_⟩
      intro i
      exact EReal.coe_le_coe_iff.mp (by simpa using hxg i)
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      rcases (mem_dual_projected_subgradient_feasible_set).1 hx with ⟨hxX, hxg⟩
      rw [mem_value_function_feasible_set]
      refine ⟨hxX, ?_, by simp⟩
      intro i
      exact_mod_cast hxg i
  have howner_nonempty : ownerValues.Nonempty := by
    refine ⟨(f xBar : EReal), ?_⟩
    refine ⟨xBar, ?_, rfl⟩
    exact (mem_dual_projected_subgradient_feasible_set).2 ⟨hxBar, fun i ↦ le_of_lt (hgBar i)⟩
  have hfOpt_lower : ∀ y ∈ ownerValues, (fOpt : EReal) ≤ y := by
    rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe (h_problem.optimal_value_isGLB.1 (Set.mem_image_of_mem f hx))
  have hsInf_lower : (fOpt : EReal) ≤ sInf ownerValues :=
    le_csInf howner_nonempty hfOpt_lower
  have hsInf_ne_top : sInf ownerValues ≠ ⊤ := by
    rcases howner_nonempty with ⟨y, hy⟩
    have hsInf_le : sInf ownerValues ≤ y := sInf_le hy
    exact ne_of_lt <| lt_of_le_of_lt hsInf_le (by rcases hy with ⟨x, -, rfl⟩; simp)
  have hsInf_ne_bot : sInf ownerValues ≠ ⊥ := by
    have hbot_lt : (⊥ : EReal) < sInf ownerValues := by
      exact lt_of_lt_of_le (by simp) hsInf_lower
    exact ne_of_gt hbot_lt
  have hsInf_coe :
      (((sInf ownerValues).toReal : ℝ) : EReal) = sInf ownerValues := by
    rw [EReal.coe_toReal hsInf_ne_top hsInf_ne_bot]
  have hsInf_real_lower :
      ∀ r ∈ f '' dual_projected_subgradient_feasible_set X g, (sInf ownerValues).toReal ≤ r := by
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hsInf_le : sInf ownerValues ≤ (f x : EReal) := by
      exact sInf_le ⟨x, hx, rfl⟩
    rw [← hsInf_coe] at hsInf_le
    exact EReal.coe_le_coe_iff.mp hsInf_le
  have hsInf_real_le_fOpt : (sInf ownerValues).toReal ≤ fOpt :=
    h_problem.optimal_value_isGLB.2 hsInf_real_lower
  have hsInf_le_fOpt : sInf ownerValues ≤ (fOpt : EReal) := by
    rw [← hsInf_coe]
    exact_mod_cast hsInf_real_le_fOpt
  -- The zero perturbation infimum equals the attained primal optimal value.
  rw [dualProjectedSubgradientPerturbationValue, value_function_apply]
  rw [howner_eq]
  exact le_antisymm hsInf_le_fOpt hsInf_lower

/-- Helper for Theorem 8.20: the origin lies in the intrinsic interior of the effective domain of
the specialized perturbation value function. -/
lemma zero_mem_intrinsicInterior_dualProjectedSubgradientPerturbationValue_effectiveDomain
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt) :
    (0 : Λ) ∈
      intrinsicInterior ℝ
        (effective_domain (dualProjectedSubgradientPerturbationValue X f g)) := by
  rcases h_problem.slater_condition_on_X with ⟨xBar, hxBar, hgBar⟩
  have hzero_interior :
      (0 : Λ) ∈ interior (effective_domain (dualProjectedSubgradientPerturbationValue X f g)) := by
    by_cases hm : m = 0
    · subst hm
      -- In the zero-constraint case the perturbation space is trivial, so every ball collapses
      -- to the origin and the origin is an interior effective-domain point as soon as it is
      -- feasible.
      refine mem_interior_iff_mem_nhds.2 <|
        Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one) ?_
      intro u hu
      have hu0 : u = 0 := Subsingleton.elim _ _
      rw [hu0, mem_effective_domain]
      have hfinite :
          dualProjectedSubgradientPerturbationValue X f g 0 ≤ (f xBar : EReal) := by
        exact dualProjectedSubgradientPerturbationValue_le_of_mem (X := X) (f := f) (g := g)
          hxBar (fun i ↦ Fin.elim0 i)
      exact lt_of_le_of_lt hfinite (by simp)
    · letI : NeZero m := ⟨hm⟩
      let slackSet : Finset ℝ := (Finset.univ).image fun i : Fin m ↦ -g i xBar
      let ε : ℝ := slackSet.min' (Finset.univ_nonempty.image fun i : Fin m ↦ -g i xBar) / 2
      have hε_pos : 0 < ε := by
        have hmin_pos : 0 < slackSet.min' (Finset.univ_nonempty.image fun i : Fin m ↦ -g i xBar) := by
          rcases Finset.mem_image.mp
              (Finset.min'_mem
                slackSet
                (Finset.univ_nonempty.image fun i : Fin m ↦ -g i xBar)) with
            ⟨i, -, hi⟩
          rw [← hi]
          exact neg_pos.mpr (hgBar i)
        dsimp [ε]
        linarith
      refine mem_interior_iff_mem_nhds.2 <|
        Filter.mem_of_superset (Metric.ball_mem_nhds 0 hε_pos) ?_
      intro u hu
      rw [mem_effective_domain]
      have hu_norm : ‖u‖ < ε := by
        simpa [Metric.mem_ball, dist_eq_norm] using hu
      have hu_coord : ∀ i : Fin m, -ε < u i := by
        intro i
        have hcoord_le : |u i| ≤ ‖u‖ := abs_coord_le_norm u i
        have hcoord_lt : |u i| < ε := lt_of_le_of_lt hcoord_le hu_norm
        have hneg_abs_lt : -ε < -|u i| := by
          linarith
        exact lt_of_lt_of_le hneg_abs_lt (neg_abs_le (u i))
      have hslack_lt : ∀ i : Fin m, g i xBar < -ε := by
        intro i
        have hmin_le :
            slackSet.min' (Finset.univ_nonempty.image fun j : Fin m ↦ -g j xBar) ≤
              -g i xBar := by
          exact Finset.min'_le
            slackSet
            (-g i xBar)
            (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        have hhalf_lt :
            ε < slackSet.min' (Finset.univ_nonempty.image fun j : Fin m ↦ -g j xBar) := by
          have hε_eq :
              ε =
                slackSet.min' (Finset.univ_nonempty.image fun j : Fin m ↦ -g j xBar) / 2 := rfl
          show
            slackSet.min' (Finset.univ_nonempty.image fun j : Fin m ↦ -g j xBar) / 2 <
              slackSet.min' (Finset.univ_nonempty.image fun j : Fin m ↦ -g j xBar)
          nlinarith [hε_pos, hε_eq]
        have hε_lt : ε < -g i xBar := lt_of_lt_of_le hhalf_lt hmin_le
        linarith
      have hxg : ∀ i : Fin m, g i xBar ≤ u i := by
        intro i
        linarith [hslack_lt i, hu_coord i]
      have hfinite :
          dualProjectedSubgradientPerturbationValue X f g u ≤ (f xBar : EReal) :=
        dualProjectedSubgradientPerturbationValue_le_of_mem (X := X) (f := f) (g := g) hxBar hxg
      exact lt_of_le_of_lt hfinite (by simp)
  -- Interior points are automatically intrinsic-interior points.
  exact interior_subset_intrinsicInterior hzero_interior

/-- Helper for Theorem 8.20: a subgradient of the specialized perturbation value function at the
origin produces a coordinatewise nonnegative multiplier vector. -/
lemma dualProjectedSubgradientMultiplier_mem_feasible_of_mem_subdifferential_zero
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    {phi : Module.Dual ℝ Λ}
    (hphi :
      phi ∈ subdifferential (dualProjectedSubgradientPerturbationValue X f g) (0 : Λ)) :
    dualProjectedSubgradientMultiplierOfFunctional phi ∈ dual_problem_feasible_set m := by
  rw [mem_subdifferential] at hphi
  rw [mem_dual_problem_feasible_set]
  intro i
  have hp_zero :
      dualProjectedSubgradientPerturbationValue X f g 0 = (fOpt : EReal) :=
    dualProjectedSubgradientPerturbationValue_zero_eq_fOpt
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem
  have hmono :
      dualProjectedSubgradientPerturbationValue X f g 0 ≥
        dualProjectedSubgradientPerturbationValue X f g (dualProjectedSubgradientBasisVector i) :=
    dualProjectedSubgradientPerturbationValue_antitone
      (X := X) (f := f) (g := g) <| by
        intro j
        by_cases hji : j = i
        · subst hji
          simp [dualProjectedSubgradientBasisVector]
        · simp [dualProjectedSubgradientBasisVector, hji]
  have hsub :
      dualProjectedSubgradientPerturbationValue X f g (dualProjectedSubgradientBasisVector i) ≥
        dualProjectedSubgradientPerturbationValue X f g 0 +
          ((phi (dualProjectedSubgradientBasisVector i) : ℝ) : EReal) :=
    by simpa using hphi.2 (dualProjectedSubgradientBasisVector i)
  have hcoeffE :
      (((fOpt + phi (dualProjectedSubgradientBasisVector i) : ℝ)) : EReal) ≤ (fOpt : EReal) := by
    calc
      (((fOpt + phi (dualProjectedSubgradientBasisVector i) : ℝ)) : EReal)
          = dualProjectedSubgradientPerturbationValue X f g 0 +
              ((phi (dualProjectedSubgradientBasisVector i) : ℝ) : EReal) := by
                rw [hp_zero, EReal.coe_add]
      _ ≤ dualProjectedSubgradientPerturbationValue X f g (dualProjectedSubgradientBasisVector i) := by
            simpa [ge_iff_le] using hsub
      _ ≤ dualProjectedSubgradientPerturbationValue X f g 0 := by
            simpa [ge_iff_le] using hmono
      _ = (fOpt : EReal) := hp_zero
  have hcoeff :
      fOpt + phi (dualProjectedSubgradientBasisVector i) ≤ fOpt := EReal.coe_le_coe_iff.mp hcoeffE
  have hphi_nonpos : phi (dualProjectedSubgradientBasisVector i) ≤ 0 := by
    linarith
  simpa [dualProjectedSubgradientMultiplierOfFunctional, dualProjectedSubgradientBasisVector] using
    neg_nonneg.mpr hphi_nonpos

/-- Helper for Theorem 8.20: every feasible dual multiplier satisfies weak duality against the
primal optimal value `fOpt`. -/
lemma lagrangianDualObjective_le_primalOptimalValue_of_dualProblemFeasible
    {lam : Λ}
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (hlam : lam ∈ dual_problem_feasible_set m) :
    q lam ≤ (fOpt : EReal) := by
  rcases h_problem.slater_condition_on_X with ⟨xBar, hxBar, hgBar⟩
  have hq_ne_top : q lam ≠ ⊤ := by
    have hq_le :
        q lam ≤ ((lagrangian f (dual_constraint_vector g) lam xBar : ℝ) : EReal) := by
      rw [lagrangian_dual_objective_eq_sInf]
      exact sInf_le ⟨xBar, hxBar, rfl⟩
    exact ne_of_lt <| lt_of_le_of_lt hq_le (EReal.coe_lt_top _)
  by_cases hq_bot : q lam = ⊥
  · simp [hq_bot]
  · have hq_coe :
        (((q lam).toReal : ℝ) : EReal) = q lam := by
          rw [EReal.coe_toReal hq_ne_top hq_bot]
    have hq_real_lower :
        ∀ r ∈ f '' dual_projected_subgradient_feasible_set X g, (q lam).toReal ≤ r := by
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      have hxX : x ∈ X := (mem_dual_projected_subgradient_feasible_set.mp hx).1
      have hxg : ∀ i : Fin m, g i x ≤ 0 := (mem_dual_projected_subgradient_feasible_set.mp hx).2
      have hlag_le_fx : lagrangian f (dual_constraint_vector g) lam x ≤ f x := by
        have hsum_nonpos : ∑ i, lam i * g i x ≤ 0 := by
          refine Finset.sum_nonpos ?_
          intro i hi
          exact mul_nonpos_of_nonneg_of_nonpos
            ((mem_dual_problem_feasible_set.mp hlam) i)
            (hxg i)
        simp [lagrangian_apply, dotProduct]
        linarith
      have hq_le_fxE : q lam ≤ (f x : EReal) := by
        have hq_le_lag :
            q lam ≤ ((lagrangian f (dual_constraint_vector g) lam x : ℝ) : EReal) := by
          rw [lagrangian_dual_objective_eq_sInf]
          exact sInf_le ⟨x, hxX, rfl⟩
        exact le_trans hq_le_lag (by exact_mod_cast hlag_le_fx)
      rw [← hq_coe] at hq_le_fxE
      exact EReal.coe_le_coe_iff.mp hq_le_fxE
    have hq_real_le_fOpt : (q lam).toReal ≤ fOpt :=
      h_problem.optimal_value_isGLB.2 hq_real_lower
    rw [← hq_coe]
    exact_mod_cast hq_real_le_fOpt

/-- Helper for Theorem 8.20: the multiplier extracted from a subgradient of the perturbation
value function at the origin supports the primal objective below the corresponding Lagrangian
family. -/
lemma primalOptimalValue_le_lagrangian_of_mem_subdifferential_zero
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    {phi : Module.Dual ℝ Λ}
    (hphi :
      phi ∈ subdifferential (dualProjectedSubgradientPerturbationValue X f g) (0 : Λ)) :
    ∀ x : E,
      x ∈ X →
        (fOpt : EReal) ≤
          lagrangian f (dual_constraint_vector g)
            (dualProjectedSubgradientMultiplierOfFunctional phi) x := by
  rw [mem_subdifferential] at hphi
  have hp_zero :
      dualProjectedSubgradientPerturbationValue X f g 0 = (fOpt : EReal) :=
    dualProjectedSubgradientPerturbationValue_zero_eq_fOpt
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem
  have hphi_apply :
      ∀ u : Λ,
        phi u = -dotProduct (dualProjectedSubgradientMultiplierOfFunctional phi) u :=
    dualProjectedSubgradientLinearFunctional_eq_negDotProduct phi
  intro x hxX
  let u : Λ := dual_constraint_vector g x
  have hp_le_fx :
      dualProjectedSubgradientPerturbationValue X f g u ≤ (f x : EReal) :=
    dualProjectedSubgradientPerturbationValue_le_of_mem
      (X := X) (f := f) (g := g) hxX (fun i ↦ by simp [u, dual_constraint_vector_apply])
  have hsub :
      dualProjectedSubgradientPerturbationValue X f g u ≥
        dualProjectedSubgradientPerturbationValue X f g 0 + ((phi u : ℝ) : EReal) :=
    by simpa using hphi.2 u
  have hsupportE :
      (((fOpt - dotProduct (dualProjectedSubgradientMultiplierOfFunctional phi) u : ℝ)) : EReal) ≤
        (f x : EReal) := by
    have hphiE :
        (((phi u : ℝ)) : EReal) =
          (((-dotProduct (dualProjectedSubgradientMultiplierOfFunctional phi) u : ℝ)) : EReal) :=
      congrArg (fun t : ℝ ↦ (t : EReal)) (hphi_apply u)
    calc
      (((fOpt - dotProduct (dualProjectedSubgradientMultiplierOfFunctional phi) u : ℝ)) : EReal)
          = (fOpt : EReal) +
              (((-dotProduct (dualProjectedSubgradientMultiplierOfFunctional phi) u : ℝ)) : EReal) := by
                norm_num [sub_eq_add_neg, EReal.coe_add]
      _ = dualProjectedSubgradientPerturbationValue X f g 0 + ((phi u : ℝ) : EReal) := by
            rw [hp_zero, hphiE]
      _ ≤ dualProjectedSubgradientPerturbationValue X f g u := by
            simpa [ge_iff_le] using hsub
      _ ≤ (f x : EReal) := hp_le_fx
  have hsupport :
      fOpt -
          dotProduct (dualProjectedSubgradientMultiplierOfFunctional phi) u ≤
        f x := EReal.coe_le_coe_iff.mp hsupportE
  have hlag_real :
      fOpt ≤
        lagrangian f (dual_constraint_vector g)
          (dualProjectedSubgradientMultiplierOfFunctional phi) x := by
    simp [lagrangian_apply, u, dotProduct] at hsupport ⊢
    linarith
  exact_mod_cast hlag_real

/-- Helper for Theorem 8.20: the dual problem admits a feasible maximizer whose dual value equals
the primal optimal value `fOpt`. -/
lemma existsDualOptimalMultiplier_eq_fOpt
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt) :
    ∃ lamStar : Λ,
      lamStar ∈ dual_problem_feasible_set m ∧
        IsMaxOn q (dual_problem_feasible_set m) lamStar ∧
        q lamStar = (fOpt : EReal) := by
  let p := dualProjectedSubgradientPerturbationValue X f g
  have hp_convex : is_convex_function p :=
    dualProjectedSubgradientPerturbationValue_isConvex (X := X) (XStar := XStar) (f := f)
      (g := g) (fOpt := fOpt) h_problem
  have hzero_intrinsic :
      (0 : Λ) ∈ intrinsicInterior ℝ (effective_domain p) :=
    zero_mem_intrinsicInterior_dualProjectedSubgradientPerturbationValue_effectiveDomain
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem
  rcases subdifferential_nonempty_at_relativeInterior_point p 0 hp_convex hzero_intrinsic with
    ⟨phi, hphi⟩
  let lamStar : Λ := dualProjectedSubgradientMultiplierOfFunctional phi
  have hlamStar_feasible : lamStar ∈ dual_problem_feasible_set m :=
    dualProjectedSubgradientMultiplier_mem_feasible_of_mem_subdifferential_zero
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem hphi
  have hq_ge : (fOpt : EReal) ≤ q lamStar := by
    rcases h_problem.slater_condition_on_X with ⟨xBar, hxBar, _⟩
    rw [lagrangian_dual_objective_eq_sInf]
    refine le_csInf ?_ ?_
    · exact ⟨_, Set.mem_image_of_mem
        (fun x : E ↦ ((lagrangian f (dual_constraint_vector g) lamStar x : ℝ) : EReal)) hxBar⟩
    · rintro _ ⟨x, hxX, rfl⟩
      simpa [lamStar] using
        primalOptimalValue_le_lagrangian_of_mem_subdifferential_zero
          (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem hphi x hxX
  have hq_le :
      q lamStar ≤ (fOpt : EReal) :=
    lagrangianDualObjective_le_primalOptimalValue_of_dualProblemFeasible
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem hlamStar_feasible
  have hq_eq : q lamStar = (fOpt : EReal) := le_antisymm hq_le hq_ge
  have hmax : IsMaxOn q (dual_problem_feasible_set m) lamStar := by
    -- Weak duality bounds every feasible dual value by the attained value at `lamStar`.
    rw [isMaxOn_iff]
    intro μ hμ
    have hμ_le :
        q μ ≤ (fOpt : EReal) :=
      lagrangianDualObjective_le_primalOptimalValue_of_dualProblemFeasible
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem hμ
    simpa [hq_eq] using hμ_le
  exact ⟨lamStar, hlamStar_feasible, hmax, hq_eq⟩

/- Theorem 8.20 is `source-facing`: it asserts strong duality and dual attainment for the
Chapter 8 inequality-constrained problem under Assumption 8.41. The canonical owners already
exist in the repository:

- `IsDualProjectedSubgradientProblem` for the standing assumptions,
- `lagrangian_dual_objective X f (dual_constraint_vector g)` for the dual objective `q`,
- `dual_problem_feasible_set m` for the nonnegative orthant `ℝ_+^m`.

The theorem therefore stays a thin bridge over those owners instead of redefining the problem
package, the feasible multiplier region, or the dual objective locally. Clause (2) keeps the
multiplier feasibility hypothesis explicit because `IsMaxOn` alone does not record that the
maximizer itself lies in the feasible set. -/

-- Proof sketch: apply the strong-duality theorem for convex inequality-constrained problems under
-- the Slater-type assumptions packaged by `h_problem`. This identifies the least upper bound of
-- the dual objective values over `dual_problem_feasible_set m` with the primal optimal value.
/-- Theorem 8.20 (1): under Assumption 8.41, if `qOpt` is the optimal value of the dual problem
`max {q(λ) : λ ∈ ℝ_+^m}`, then `qOpt = fOpt`. -/
theorem dual_projected_subgradient_problem_strong_duality
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    {qOpt : EReal}
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) qOpt) :
    qOpt = (fOpt : EReal) := by
  obtain ⟨lamStar, hlamStar, -, hqStar⟩ :=
    existsDualOptimalMultiplier_eq_fOpt
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem
  have hfOpt_le : (fOpt : EReal) ≤ qOpt := by
    -- The attained dual value belongs to the image set governed by the supplied `IsLUB`.
    have hmem : q lamStar ∈ q '' dual_problem_feasible_set m :=
      Set.mem_image_of_mem q hlamStar
    simpa [hqStar] using hdual_value.1 hmem
  have hqOpt_le : qOpt ≤ (fOpt : EReal) := by
    -- Weak duality shows that `fOpt` is an upper bound on the whole dual image set.
    refine hdual_value.2 ?_
    intro y hy
    rcases hy with ⟨lam, hlam, rfl⟩
    exact lagrangianDualObjective_le_primalOptimalValue_of_dualProblemFeasible
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem hlam
  exact le_antisymm hqOpt_le hfOpt_le

-- Proof sketch: apply the dual-attainment part of the strong-duality theorem for convex
-- inequality-constrained problems under `h_problem` to obtain a nonnegative multiplier whose dual
-- objective value is `qOpt`, then record both its feasibility and maximality on
-- `dual_problem_feasible_set m`.
/-- Theorem 8.20 (2): under Assumption 8.41, the dual problem attains the optimal value `qOpt`
at some nonnegative multiplier `λ* ∈ ℝ_+^m`. -/
theorem dual_projected_subgradient_problem_dual_attainment
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    {qOpt : EReal}
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) qOpt) :
    ∃ lamStar : Λ,
      lamStar ∈ dual_problem_feasible_set m ∧
        IsMaxOn q (dual_problem_feasible_set m) lamStar ∧
        q lamStar = qOpt := by
  obtain ⟨lamStar, hlamStar, hmax, hqStar⟩ :=
    existsDualOptimalMultiplier_eq_fOpt
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem
  have hstrong :
      qOpt = (fOpt : EReal) :=
    dual_projected_subgradient_problem_strong_duality
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem hdual_value
  -- Reuse the attained `fOpt`-valued dual maximizer and rewrite the value through strong duality.
  refine ⟨lamStar, hlamStar, hmax, ?_⟩
  rw [hqStar, ← hstrong]

end
