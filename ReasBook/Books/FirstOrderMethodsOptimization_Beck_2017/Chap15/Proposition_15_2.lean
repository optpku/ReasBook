/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_10
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_11
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open InnerProductSpace (toDualMap)

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/- Domain sampling for this file:
- the Chapter 4 conjugacy owner `conjugate_function`, together with Chapter 3's
  `subdifferential`, governs the dual-side optimality clauses;
- the Chapter 8 owner `unconstrained_problem_solutions` is the canonical whole-space `arg min`
  set, with Mathlib's `IsMinOn` as its membership view;
- the ADMM affine `x`- and `z`-subproblems, together with equation (15.5), are the
  `source-facing` objects specific to this proposition.

Accordingly, this file keeps those source-facing ADMM objects, but phrases the bridge theorems
using the chapter's canonical dual-space conjugacy owner and whole-space solution-set owner rather
than parallel local copies. -/

/-- The `x`-subproblem in Proposition 15.2 is the affine perturbation
`x ↦ ⟪Aᵀ y, x⟫ + h₁(x)`, with the transpose represented by `A.adjoint`. -/
def admm_x_subproblem
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y) (y : Y) : X → EReal :=
  fun x ↦ ((inner ℝ (A.adjoint y) x : ℝ) : EReal) + h₁ x

-- Proof sketch: unfold `admm_x_subproblem`; evaluation at `x` is exactly the displayed affine
-- term plus `h₁(x)`.
/-- Evaluating the `x`-subproblem gives the objective `⟪Aᵀ y, x⟫ + h₁(x)`. -/
@[simp] theorem admm_x_subproblem_apply
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y) (y : Y) (x : X) :
    admm_x_subproblem h₁ A y x =
      ((inner ℝ (A.adjoint y) x : ℝ) : EReal) + h₁ x :=
  rfl

/-- The `z`-subproblem in Proposition 15.2 is the affine perturbation
`z ↦ ⟪Bᵀ y, z⟫ + h₂(z)`, with the transpose represented by `B.adjoint`. -/
def admm_z_subproblem
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y) (y : Y) : Z → EReal :=
  fun z ↦ ((inner ℝ (B.adjoint y) z : ℝ) : EReal) + h₂ z

-- Proof sketch: unfold `admm_z_subproblem`; evaluation at `z` is exactly the displayed affine
-- term plus `h₂(z)`.
/-- Evaluating the `z`-subproblem gives the objective `⟪Bᵀ y, z⟫ + h₂(z)`. -/
@[simp] theorem admm_z_subproblem_apply
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y) (y : Y) (z : Z) :
    admm_z_subproblem h₂ B y z =
      ((inner ℝ (B.adjoint y) z : ℝ) : EReal) + h₂ z :=
  rfl

/-- Equation (15.5) in source-facing form: there exist primal witnesses whose canonical
double-dual images lie in the subdifferentials of `h₁^*` and `h₂^*` at `-Aᵀ y^{k+1}` and
`-Bᵀ y^{k+1}`, and these witnesses realize the affine dual update. -/
def admm_dual_optimality_condition
    (ρ : ℝ)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk yNext : Y) : Prop :=
  ∃ xNext,
    Module.Dual.eval ℝ X xNext ∈
        ∂ (conjugate_function h₁)(toDualMap ℝ X (-A.adjoint yNext)) ∧
      ∃ zNext,
        Module.Dual.eval ℝ Z zNext ∈
            ∂ (conjugate_function h₂)(toDualMap ℝ Z (-B.adjoint yNext)) ∧
          yNext = yk + ρ • (A xNext + B zNext - c)

/-- Helper for Proposition 15.2: on the whole space, maximizing `φ` is equivalent to minimizing
its pointwise negation. -/
lemma isMaxOn_univ_iff_isMinOn_univ_neg
    (φ : X → EReal) (x : X) :
    IsMaxOn φ Set.univ x ↔ IsMinOn (fun x' ↦ -φ x') Set.univ x := by
  -- Unfold both extremality predicates on `Set.univ` and compare them pointwise by negation.
  rw [isMaxOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro hx u
    exact EReal.neg_le_neg_iff.2 (hx u)
  · intro hx u
    exact EReal.neg_le_neg_iff.1 (hx u)

/-- Helper for Proposition 15.2: negating the `x`-block affine-minus-`h₁` objective produces the
Chapter 15 `x`-subproblem. -/
lemma neg_pairing_sub_eq_admm_x_subproblem
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (y : Y) :
    (fun x' : X ↦ -(((toDualMap ℝ X (-A.adjoint y)) x' : EReal) - h₁ x')) =
      admm_x_subproblem h₁ A y := by
  funext x'
  -- Negate the affine-minus-`h₁` expression using properness to exclude the `-∞` case.
  have hneg :
      -(((toDualMap ℝ X (-A.adjoint y)) x' : EReal) - h₁ x') =
        -((toDualMap ℝ X (-A.adjoint y)) x' : EReal) + h₁ x' := by
    rw [EReal.neg_sub] <;> simp [hh₁_proper.ne_bot x']
  -- Then identify the resulting affine term with `⟪Aᵀ y, x'⟫ + h₁(x')`.
  rw [hneg, admm_x_subproblem_apply]
  simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]

/-- Helper for Proposition 15.2: negating the `z`-block affine-minus-`h₂` objective produces the
Chapter 15 `z`-subproblem. -/
lemma neg_pairing_sub_eq_admm_z_subproblem
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y)
    (hh₂_proper : IsProperExtendedRealFunction h₂)
    (y : Y) :
    (fun z' : Z ↦ -(((toDualMap ℝ Z (-B.adjoint y)) z' : EReal) - h₂ z')) =
      admm_z_subproblem h₂ B y := by
  funext z'
  -- Negate the affine-minus-`h₂` expression using properness to exclude the `-∞` case.
  have hneg :
      -(((toDualMap ℝ Z (-B.adjoint y)) z' : EReal) - h₂ z') =
        -((toDualMap ℝ Z (-B.adjoint y)) z' : EReal) + h₂ z' := by
    rw [EReal.neg_sub] <;> simp [hh₂_proper.ne_bot z']
  -- Then identify the resulting affine term with `⟪Bᵀ y, z'⟫ + h₂(z')`.
  rw [hneg, admm_z_subproblem_apply]
  simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]

-- Proof sketch: combine `pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate` with
-- `conjugate_function_eq_iff_isMaxOn_pairing_sub_function`; after substituting
-- `toDualMap ℝ X (-A.adjoint y)` and `toDualMap ℝ Z (-B.adjoint y)`, rewrite the resulting
-- argmax statements as the displayed `arg min` conditions by negating the affine term.
/-- The canonical double-dual image of `x` lies in `∂ h₁^*(-Aᵀ y)` exactly when `x` solves the
`x`-subproblem from Proposition 15.2. -/
theorem eval_mem_conjugate_subdifferential_iff_mem_admm_x_subproblem_solutions
    (h₁ : X → EReal) (A : X →ₗ[ℝ] Y)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_closed : LowerSemicontinuous h₁) (hh₁_convex : is_convex_function h₁)
    (y : Y) (x : X) :
    Module.Dual.eval ℝ X x ∈
        ∂ (conjugate_function h₁)(toDualMap ℝ X (-A.adjoint y)) ↔
      x ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A y) := by
  let ℓ : Module.Dual ℝ X := toDualMap ℝ X (-A.adjoint y)
  let φ : X → EReal := fun x' ↦ (ℓ x' : EReal) - h₁ x'
  have hmax :
      Module.Dual.eval ℝ X x ∈ ∂ (conjugate_function h₁)(ℓ) ↔ IsMaxOn φ Set.univ x := by
    -- Route correction: use Theorem 4.12's `eval`-image argmax description to avoid brittle
    -- `EReal` subtraction algebra in the main bridge.
    constructor
    · intro hx
      rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
        h₁ hh₁_proper hh₁_closed hh₁_convex ℓ] at hx
      rcases hx with ⟨x', hx', hEval⟩
      have hxEq : x' = x :=
        Module.eval_apply_injective ℝ hEval
      simpa [φ] using hxEq ▸ hx'
    · intro hx
      rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
        h₁ hh₁_proper hh₁_closed hh₁_convex ℓ]
      exact ⟨x, by simpa [φ] using hx, rfl⟩
  have hmin :
      IsMaxOn φ Set.univ x ↔ IsMinOn (admm_x_subproblem h₁ A y) Set.univ x := by
    -- Replace the argmax viewpoint by the equivalent argmin viewpoint for the negated objective.
    have hobj : (fun x' : X ↦ -φ x') = admm_x_subproblem h₁ A y := by
      simpa [φ, ℓ] using neg_pairing_sub_eq_admm_x_subproblem h₁ A hh₁_proper y
    calc
      IsMaxOn φ Set.univ x ↔ IsMinOn (fun x' : X ↦ -φ x') Set.univ x := by
        simpa [φ] using isMaxOn_univ_iff_isMinOn_univ_neg φ x
      _ ↔ IsMinOn (admm_x_subproblem h₁ A y) Set.univ x := by
        constructor
        · intro hxMin
          simpa [hobj] using hxMin
        · intro hxMin
          simpa [hobj] using hxMin
  have hsol :
      IsMinOn (admm_x_subproblem h₁ A y) Set.univ x ↔
        x ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A y) := by
    -- Translate the `IsMinOn` statement into membership in the canonical Chapter 8 solution set.
    simpa using
      (mem_unconstrained_problem_solutions_iff :
        x ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A y) ↔
          IsMinOn (admm_x_subproblem h₁ A y) Set.univ x).symm
  -- Chain the conjugate-subgradient, argmax, and argmin characterizations.
  have hchain :
      Module.Dual.eval ℝ X x ∈ ∂ (conjugate_function h₁)(ℓ) ↔
        x ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A y) :=
    hmax.trans (hmin.trans hsol)
  simpa [ℓ] using hchain

-- Proof sketch: apply the same conjugate-subgradient/argmax bridge as in the `x`-case, now to
-- `h₂` and the adjoint image `-B.adjoint y`.
/-- The canonical double-dual image of `z` lies in `∂ h₂^*(-Bᵀ y)` exactly when `z` solves the
`z`-subproblem from Proposition 15.2. -/
theorem eval_mem_conjugate_subdifferential_iff_mem_admm_z_subproblem_solutions
    (h₂ : Z → EReal) (B : Z →ₗ[ℝ] Y)
    (hh₂_proper : IsProperExtendedRealFunction h₂)
    (hh₂_closed : LowerSemicontinuous h₂) (hh₂_convex : is_convex_function h₂)
    (y : Y) (z : Z) :
    Module.Dual.eval ℝ Z z ∈
        ∂ (conjugate_function h₂)(toDualMap ℝ Z (-B.adjoint y)) ↔
      z ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B y) := by
  let ℓ : Module.Dual ℝ Z := toDualMap ℝ Z (-B.adjoint y)
  let φ : Z → EReal := fun z' ↦ (ℓ z' : EReal) - h₂ z'
  have hmax :
      Module.Dual.eval ℝ Z z ∈ ∂ (conjugate_function h₂)(ℓ) ↔ IsMaxOn φ Set.univ z := by
    -- Route correction: use Theorem 4.12's `eval`-image argmax description to avoid brittle
    -- `EReal` subtraction algebra in the main bridge.
    constructor
    · intro hz
      rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
        h₂ hh₂_proper hh₂_closed hh₂_convex ℓ] at hz
      rcases hz with ⟨z', hz', hEval⟩
      have hzEq : z' = z :=
        Module.eval_apply_injective ℝ hEval
      simpa [φ] using hzEq ▸ hz'
    · intro hz
      rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
        h₂ hh₂_proper hh₂_closed hh₂_convex ℓ]
      exact ⟨z, by simpa [φ] using hz, rfl⟩
  have hmin :
      IsMaxOn φ Set.univ z ↔ IsMinOn (admm_z_subproblem h₂ B y) Set.univ z := by
    -- Replace the argmax viewpoint by the equivalent argmin viewpoint for the negated objective.
    have hobj : (fun z' : Z ↦ -φ z') = admm_z_subproblem h₂ B y := by
      simpa [φ, ℓ] using neg_pairing_sub_eq_admm_z_subproblem h₂ B hh₂_proper y
    calc
      IsMaxOn φ Set.univ z ↔ IsMinOn (fun z' : Z ↦ -φ z') Set.univ z := by
        simpa [φ] using isMaxOn_univ_iff_isMinOn_univ_neg φ z
      _ ↔ IsMinOn (admm_z_subproblem h₂ B y) Set.univ z := by
        constructor
        · intro hzMin
          simpa [hobj] using hzMin
        · intro hzMin
          simpa [hobj] using hzMin
  have hsol :
      IsMinOn (admm_z_subproblem h₂ B y) Set.univ z ↔
        z ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B y) := by
    -- Translate the `IsMinOn` statement into membership in the canonical Chapter 8 solution set.
    simpa using
      (mem_unconstrained_problem_solutions_iff :
        z ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B y) ↔
          IsMinOn (admm_z_subproblem h₂ B y) Set.univ z).symm
  -- Chain the conjugate-subgradient, argmax, and argmin characterizations.
  have hchain :
      Module.Dual.eval ℝ Z z ∈ ∂ (conjugate_function h₂)(ℓ) ↔
        z ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B y) :=
    hmax.trans (hmin.trans hsol)
  simpa [ℓ] using hchain

-- Proof sketch: unfold `admm_dual_optimality_condition`, apply the two bridge theorems turning
-- conjugate-subdifferential memberships into `arg min` conditions, and keep the affine update
-- equation unchanged.
/-- Proposition 15.2: by the conjugate subgradient theorem, equation (15.5) holds exactly when
there are points `x^{k+1}` and `z^{k+1}` minimizing the two affine subproblems
`x ↦ ⟪Aᵀ y^{k+1}, x⟫ + h₁(x)` and `z ↦ ⟪Bᵀ y^{k+1}, z⟫ + h₂(z)` such that
`y^{k+1} = y^k + ρ (A x^{k+1} + B z^{k+1} - c)`. -/
theorem admm_dual_optimality_condition_iff_exists_primal_argmin_and_affine_update
    (ρ : ℝ)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk yNext : Y)
    (hPair : IsADMMConvexObjectivePair h₁ h₂) :
    admm_dual_optimality_condition ρ h₁ h₂ A B c yk yNext ↔
      ∃ xNext ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A yNext),
        ∃ zNext ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B yNext),
          yNext = yk + ρ • (A xNext + B zNext - c) := by
  constructor
  · intro h
    -- Unpack equation (15.5) and convert each conjugate-subgradient clause into an argmin clause.
    rcases h with ⟨xNext, hxNext, zNext, hzNext, hyNext⟩
    have hxMin :
        xNext ∈ unconstrained_problem_solutions (admm_x_subproblem h₁ A yNext) :=
      (eval_mem_conjugate_subdifferential_iff_mem_admm_x_subproblem_solutions
        h₁ A hPair.toIsProperExtendedRealFunction hPair.h₁_closed hPair.h₁_convex
        yNext xNext).1 hxNext
    have hzMin :
        zNext ∈ unconstrained_problem_solutions (admm_z_subproblem h₂ B yNext) :=
      (eval_mem_conjugate_subdifferential_iff_mem_admm_z_subproblem_solutions
        h₂ B hPair.h₂_proper hPair.h₂_closed hPair.h₂_convex
        yNext zNext).1 hzNext
    exact ⟨xNext, hxMin, zNext, hzMin, hyNext⟩
  · intro h
    -- Repackage the primal argmin witnesses as the conjugate-subgradient witnesses of (15.5).
    rcases h with ⟨xNext, hxMin, zNext, hzMin, hyNext⟩
    have hxNext :
        Module.Dual.eval ℝ X xNext ∈
          ∂ (conjugate_function h₁)(toDualMap ℝ X (-A.adjoint yNext)) :=
      (eval_mem_conjugate_subdifferential_iff_mem_admm_x_subproblem_solutions
        h₁ A hPair.toIsProperExtendedRealFunction hPair.h₁_closed hPair.h₁_convex
        yNext xNext).2 hxMin
    have hzNext :
        Module.Dual.eval ℝ Z zNext ∈
          ∂ (conjugate_function h₂)(toDualMap ℝ Z (-B.adjoint yNext)) :=
      (eval_mem_conjugate_subdifferential_iff_mem_admm_z_subproblem_solutions
        h₂ B hPair.h₂_proper hPair.h₂_closed hPair.h₂_convex
        yNext zNext).2 hzMin
    exact ⟨xNext, hxNext, zNext, hzNext, hyNext⟩

end
