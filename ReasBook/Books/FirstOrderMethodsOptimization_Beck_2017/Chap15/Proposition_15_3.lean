/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Proposition_15_2

noncomputable section

universe u v w

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 15.3 is a `bridge/view` item. The source-facing content is the Euclidean
subdifferential reformulation of Proposition 15.2's ADMM argmin conditions. The Chapter 15
owners `admm_x_subproblem`, `admm_z_subproblem`, and `admm_dual_optimality_condition` already
live in Proposition 15.2, while the Euclidean/owner subdifferential bridge lives in
Proposition 15.1. This file therefore keeps only the affine-perturbation bridge API unique to
Proposition 15.3. -/

/-- Adding the everywhere-finite linear perturbation `u ↦ ⟪a, u⟫` does not change the effective
domain. -/
@[simp] theorem mem_effective_domain_inner_perturbation_iff
    (h : E → EReal) (a u : E) :
    u ∈ effective_domain (fun v ↦ ((inner ℝ a v : ℝ) : EReal) + h v) ↔
      u ∈ effective_domain h := by
  constructor
  · intro hu
    have hu_ne_top : h u ≠ ⊤ := by
      intro hhu_top
      have hsum_top :
          ((inner ℝ a u : ℝ) : EReal) + h u = ⊤ := by
        simp [hhu_top, EReal.add_top_of_ne_bot, EReal.coe_ne_bot]
      exact hu.ne hsum_top
    exact lt_top_iff_ne_top.mpr hu_ne_top
  · intro hu
    simpa using EReal.add_lt_top (EReal.coe_ne_top (inner ℝ a u)) hu.ne

/-- Zero is a subgradient of the affine perturbation `u ↦ ⟪a, u⟫ + h(u)` at `x` exactly when
`-a` belongs to the Euclidean subdifferential of `h` at `x`. -/
theorem zero_mem_subdifferential_inner_perturbation_iff_neg_mem_euclideanSubdifferential
    (h : E → EReal) (a x : E) :
    (0 : Module.Dual ℝ E) ∈
        subdifferential (fun u ↦ ((inner ℝ a u : ℝ) : EReal) + h u) x ↔
      -a ∈ euclideanSubdifferential h x := by
  let perturbation : E → EReal := fun u ↦ ((inner ℝ a u : ℝ) : EReal) + h u
  rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  constructor
  · rintro ⟨hx, hzero⟩
    refine ⟨(mem_effective_domain_inner_perturbation_iff h a x).1 hx, ?_⟩
    intro y hy
    have hy_perturbation :
        y ∈ effective_domain perturbation :=
      (mem_effective_domain_inner_perturbation_iff h a y).2 hy
    have haux :
        h x + ((inner ℝ a x : ℝ) : EReal) ≤
          h y + ((inner ℝ a y : ℝ) : EReal) := by
      simpa [perturbation, add_assoc, add_left_comm, add_comm, ge_iff_le] using
        hzero y hy_perturbation
    have hstep :
        h x ≤ h y + ((inner ℝ a (y - x) : ℝ) : EReal) := by
      have hsub :
          h x ≤ (h y + ((inner ℝ a y : ℝ) : EReal)) - ((inner ℝ a x : ℝ) : EReal) := by
        exact (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _))
          (.inl (EReal.coe_ne_top _))).2 (by
            simpa [add_assoc, add_left_comm, add_comm] using haux)
      have hinner :
          -(((inner ℝ a x : ℝ) : EReal)) + ((inner ℝ a y : ℝ) : EReal) =
            ((inner ℝ a (y - x) : ℝ) : EReal) := by
        calc
          -(((inner ℝ a x : ℝ) : EReal)) + ((inner ℝ a y : ℝ) : EReal) =
              (((-inner ℝ a x : ℝ) + inner ℝ a y : ℝ) : EReal) := by
                rw [← EReal.coe_neg, EReal.coe_add]
          _ = ((inner ℝ a (y - x) : ℝ) : EReal) := by
                congr
                rw [inner_sub_right]
                ring
      simpa [sub_eq_add_neg, hinner, add_assoc, add_left_comm, add_comm] using hsub
    have hsub :
        h x - ((inner ℝ a (y - x) : ℝ) : EReal) ≤ h y :=
      EReal.sub_le_of_le_add' (by
        simpa [add_comm, add_left_comm, add_assoc] using hstep)
    simpa [ge_iff_le, InnerProductSpace.toDualMap_apply_apply, sub_eq_add_neg, inner_neg_left]
      using hsub
  · rintro ⟨hx, hsubgrad⟩
    refine ⟨(mem_effective_domain_inner_perturbation_iff h a x).2 hx, ?_⟩
    intro y hy
    have hy_h : y ∈ effective_domain h :=
      (mem_effective_domain_inner_perturbation_iff h a y).1 hy
    have hsub :
        h x - ((inner ℝ a (y - x) : ℝ) : EReal) ≤ h y := by
      simpa [ge_iff_le, InnerProductSpace.toDualMap_apply_apply, sub_eq_add_neg, inner_neg_left]
        using hsubgrad y hy_h
    have hstep :
        h x ≤ h y + ((inner ℝ a (y - x) : ℝ) : EReal) := by
      exact (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
        (.inl (EReal.coe_ne_top _))).1 hsub
    have haux :
        h x + ((inner ℝ a x : ℝ) : EReal) ≤
          h y + ((inner ℝ a y : ℝ) : EReal) := by
      have hbase :
          h x + ((inner ℝ a x : ℝ) : EReal) ≤
            (h y + ((inner ℝ a (y - x) : ℝ) : EReal)) +
              ((inner ℝ a x : ℝ) : EReal) := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_right hstep (((inner ℝ a x : ℝ) : EReal))
      have hinner :
          ((inner ℝ a (y - x) : ℝ) : EReal) + ((inner ℝ a x : ℝ) : EReal) =
            ((inner ℝ a y : ℝ) : EReal) := by
        calc
          ((inner ℝ a (y - x) : ℝ) : EReal) + ((inner ℝ a x : ℝ) : EReal) =
              (((inner ℝ a (y - x) : ℝ) + inner ℝ a x : ℝ) : EReal) := by
                rw [EReal.coe_add]
          _ = ((inner ℝ a y : ℝ) : EReal) := by
                congr
                rw [inner_sub_right]
                ring
      calc
        h x + ((inner ℝ a x : ℝ) : EReal) ≤
            (h y + ((inner ℝ a (y - x) : ℝ) : EReal)) +
              ((inner ℝ a x : ℝ) : EReal) := hbase
        _ = h y + ((inner ℝ a y : ℝ) : EReal) := by
          rw [add_assoc, hinner]
    simpa [perturbation, add_assoc, add_left_comm, add_comm, ge_iff_le] using haux

end

section

variable {X : Type u} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- A point minimizes the `x`-subproblem from Proposition 15.2 exactly when `-Aᵀ y` belongs to
the Euclidean subdifferential of `h₁` at that point. -/
theorem mem_admm_x_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y)
    (hh₁_dom : (effective_domain h₁).Nonempty)
    (y : Y) (x : X) :
    x ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A y) ↔
      -A.adjoint y ∈ euclideanSubdifferential h₁ x := by
  have hdom :
      (effective_domain (admm_x_subproblem h₁ A y)).Nonempty := by
    rcases hh₁_dom with ⟨x₀, hx₀⟩
    exact ⟨x₀, by
      simpa [admm_x_subproblem] using
        (mem_effective_domain_inner_perturbation_iff h₁ (A.adjoint y) x₀).2 hx₀⟩
  rw [mem_unconstrained_problem_solutions_iff]
  exact (isMinOn_univ_iff_zero_mem_subdifferential hdom).trans <| by
    simpa [admm_x_subproblem] using
      zero_mem_subdifferential_inner_perturbation_iff_neg_mem_euclideanSubdifferential
        h₁ (A.adjoint y) x

end

section

variable {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- A point minimizes the `z`-subproblem from Proposition 15.2 exactly when `-Bᵀ y` belongs to
the Euclidean subdifferential of `h₂` at that point. -/
theorem mem_admm_z_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y)
    (hh₂_dom : (effective_domain h₂).Nonempty)
    (y : Y) (z : Z) :
    z ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B y) ↔
      -B.adjoint y ∈ euclideanSubdifferential h₂ z := by
  have hdom :
      (effective_domain (admm_z_subproblem h₂ B y)).Nonempty := by
    rcases hh₂_dom with ⟨z₀, hz₀⟩
    exact ⟨z₀, by
      simpa [admm_z_subproblem] using
        (mem_effective_domain_inner_perturbation_iff h₂ (B.adjoint y) z₀).2 hz₀⟩
  rw [mem_unconstrained_problem_solutions_iff]
  exact (isMinOn_univ_iff_zero_mem_subdifferential hdom).trans <| by
    simpa [admm_z_subproblem] using
      zero_mem_subdifferential_inner_perturbation_iff_neg_mem_euclideanSubdifferential
        h₂ (B.adjoint y) z

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Proposition 15.3: equation (15.5) is equivalent to the existence of primal witnesses
`x^(k+1)` and `z^(k+1)` satisfying the affine update (15.6) together with the Euclidean
subdifferential conditions corresponding to (15.7) and (15.8). -/
theorem admm_dual_optimality_condition_iff_exists_primal_subgradient_and_affine_update
    (ρ : ℝ)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk yNext : Y)
    (hPair : IsADMMConvexObjectivePair h₁ h₂) :
    admm_dual_optimality_condition ρ h₁ h₂ A B c yk yNext ↔
      ∃ xNext,
        -A.adjoint yNext ∈ euclideanSubdifferential h₁ xNext ∧
          ∃ zNext,
            -B.adjoint yNext ∈ euclideanSubdifferential h₂ zNext ∧
              yNext = yk + ρ • (A xNext + B zNext - c) := by
  constructor
  · intro hdual
    rcases
        (admm_dual_optimality_condition_iff_exists_primal_argmin_and_affine_update
          ρ h₁ h₂ A B c yk yNext hPair).1 hdual with
      ⟨xNext, hxMin, zNext, hzMin, hyNext⟩
    refine ⟨xNext, ?_, zNext, ?_, hyNext⟩
    · exact
        (mem_admm_x_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
          h₁ A hPair.toIsProperExtendedRealFunction.effective_domain_nonempty yNext xNext).1 hxMin
    · exact
        (mem_admm_z_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
          h₂ B hPair.h₂_proper.effective_domain_nonempty yNext zNext).1 hzMin
  · rintro ⟨xNext, hxNext, zNext, hzNext, hyNext⟩
    refine
      (admm_dual_optimality_condition_iff_exists_primal_argmin_and_affine_update
        ρ h₁ h₂ A B c yk yNext hPair).2 ?_
    refine ⟨xNext, ?_, zNext, ?_, hyNext⟩
    · exact
        (mem_admm_x_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
          h₁ A hPair.toIsProperExtendedRealFunction.effective_domain_nonempty yNext xNext).2 hxNext
    · exact
        (mem_admm_z_subproblem_solutions_iff_neg_adjoint_mem_euclideanSubdifferential
          h₂ B hPair.h₂_proper.effective_domain_nonempty yNext zNext).2 hzNext

end
