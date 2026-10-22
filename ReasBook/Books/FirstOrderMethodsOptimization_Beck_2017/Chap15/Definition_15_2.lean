/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_4
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open InnerProductSpace (toDualMap)

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Z] [Module ℝ Z]
variable [AddCommGroup Y] [Module ℝ Y]

/- `prompt_add/` is absent in this workspace, so the API choice is sampled from the nearby duality
files. This item is `source-facing`: the primitive data are the ADMM Lagrangian, the resulting
dual objective, the dual-value function, and the equivalent minimization-form objective. The
`core/canonical` owners already upstream in the chapter/project are `H[h₁, h₂] = admm_objective
h₁ h₂` from Definition 15.1 for the two-block primal objective, `conjugate_function` from Chapter
4 for Fenchel conjugates, and `LinearMap.dualMap` for the pulled-back dual variables encoding the
transpose terms `-Aᵀ y` and `-Bᵀ y`. -/

-- Semantic recall: `ereal_sInf_range_sub_pairing_eq_neg_conjugate` in Theorem 15.1 and
-- `fenchel_dual_objective_eq_sInf_split_lagrangian` in Definition 4.8 show that the `EReal`
-- infimum bridge needs explicit properness hypotheses to avoid mixed `⊤/⊥` pathologies.

/-- Definition 15.2 (1): the ADMM Lagrangian associated with the affine constraint
`A x + B z = c`. -/
def admm_lagrangian
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (x : X) (z : Z) (y : Module.Dual ℝ Y) : EReal :=
  H[h₁, h₂] (x, z) + (y (A x + B z - c) : EReal)

/-- Evaluating the ADMM Lagrangian gives `h₁ x + h₂ z + ⟨y, A x + B z - c⟩`. -/
@[simp] theorem admm_lagrangian_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (x : X) (z : Z) (y : Module.Dual ℝ Y) :
    admm_lagrangian h₁ h₂ A B c x z y =
      h₁ x + h₂ z + (y (A x + B z - c) : EReal) := by
  simp [admm_lagrangian]

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Z] [Module ℝ Z]
variable [AddCommGroup Y] [Module ℝ Y]

/-- Definition 15.2 (2): the ADMM dual objective function
`q(y) = -h₁^*(-Aᵀ y) - h₂^*(-Bᵀ y) - ⟨c, y⟩`, where the transpose terms are represented canonically
by the pulled-back dual vectors `A.dualMap (-y)` and `B.dualMap (-y)`. -/
def admm_dual_objective
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) : Module.Dual ℝ Y → EReal :=
  fun y ↦
    -conjugate_function h₁ (A.dualMap (-y)) -
      conjugate_function h₂ (B.dualMap (-y)) -
        (y c : EReal)

/-- Evaluating the ADMM dual objective at `y` gives the conjugate formula from Definition 15.2. -/
@[simp] theorem admm_dual_objective_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Module.Dual ℝ Y) :
    admm_dual_objective h₁ h₂ A B c y =
      -conjugate_function h₁ (A.dualMap (-y)) -
        conjugate_function h₂ (B.dualMap (-y)) -
          (y c : EReal) := rfl

/-- Source-facing optimization-value companion to Definition 15.2 (2): for each dual variable `y`,
this is the infimum value of the ADMM Lagrangian over the primal variables `(x, z)`. -/
def admm_dual_lagrangian_value
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) : Module.Dual ℝ Y → EReal :=
  fun y ↦ sInf (Set.range fun xz : X × Z ↦ admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y)

/-- The source-facing Lagrangian-value formulation of `q(y)` is the infimum over the primal
variables `(x, z)` of `admm_lagrangian h₁ h₂ A B c x z y`. -/
theorem admm_dual_lagrangian_value_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Module.Dual ℝ Y) :
    admm_dual_lagrangian_value h₁ h₂ A B c y =
      sInf (Set.range fun xz : X × Z ↦ admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y) :=
  rfl

/-- Helper for Definition 15.2: the ADMM Lagrangian separates into the two affine perturbations
that define the pulled-back conjugates, together with the constant term `-⟪y, c⟫`. -/
private theorem admm_lagrangian_eq_affine_split
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (x : X) (z : Z) (y : Module.Dual ℝ Y) :
    admm_lagrangian h₁ h₂ A B c x z y =
      (h₁ x - ((A.dualMap (-y)) x : EReal)) +
        (h₂ z - ((B.dualMap (-y)) z : EReal)) +
          (-(y c : EReal)) := by
  -- Expand the affine constraint pairing and rewrite the pullbacks `A.dualMap (-y)` and
  -- `B.dualMap (-y)` as the expected transpose terms.
  rw [admm_lagrangian_apply]
  simp [LinearMap.dualMap_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

-- Proof sketch: unfold `admm_lagrangian`, separate the infimum over the product variables into the
-- `x`- and `z`-parts, and identify those two infima with the negatives of the pulled-back
-- conjugates `h₁^*(A.dualMap (-y))` and `h₂^*(B.dualMap (-y))`, leaving the affine remainder
-- `-(y c)`.
/-- Under properness hypotheses on both block objectives, the ADMM dual objective is the infimum
form `q(y) = inf_{x,z} L(x, z; y)` of the Lagrangian. -/
theorem admm_dual_objective_eq_sInf_lagrangian
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (y : Module.Dual ℝ Y) :
    admm_dual_objective h₁ h₂ A B c y =
      sInf (Set.range fun xz : X × Z ↦ admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y) :=
  by
  let ψ : X × Z → EReal :=
    fun xz ↦
      (((A.dualMap (-y)) xz.1 : EReal) - h₁ xz.1) +
        (((B.dualMap (-y)) xz.2 : EReal) - h₂ xz.2) +
          (y c : EReal)
  have hrange :
      Set.range (fun xz : X × Z ↦ admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y) = -Set.range ψ := by
    -- Normalize the ADMM Lagrangian range once so the main proof can stay at the conjugate API.
    ext w
    constructor
    · rintro ⟨⟨x, z⟩, rfl⟩
      rw [Set.mem_neg]
      refine ⟨(x, z), ?_⟩
      have hx_ne_top : (((A.dualMap (-y)) x : EReal) - h₁ x) ≠ ⊤ :=
        affinePairingMinusValue_ne_top_of_proper h₁ h₁_proper (A.dualMap (-y)) x
      have hz_ne_top : (((B.dualMap (-y)) z : EReal) - h₂ z) ≠ ⊤ :=
        affinePairingMinusValue_ne_top_of_proper h₂ h₂_proper (B.dualMap (-y)) z
      have hsplit :
          admm_lagrangian h₁ h₂ A B c x z y = -ψ (x, z) := by
        -- Rewrite the ADMM Lagrangian as one negated separable affine-conjugate integrand.
        let u : EReal := ((A.dualMap (-y)) x : EReal) - h₁ x
        let v : EReal := ((B.dualMap (-y)) z : EReal) - h₂ z
        have hx_split :
            -(((A.dualMap (-y)) x : EReal) - h₁ x) = h₁ x - ((A.dualMap (-y)) x : EReal) := by
          rw [EReal.neg_sub] <;> simp [sub_eq_add_neg, add_comm]
        have hz_split :
            -(((B.dualMap (-y)) z : EReal) - h₂ z) = h₂ z - ((B.dualMap (-y)) z : EReal) := by
          rw [EReal.neg_sub] <;> simp [sub_eq_add_neg, add_comm]
        have hneg_uv : -(u + v) = -u + -v := by
          simpa [u, v, sub_eq_add_neg] using
            (EReal.neg_add (.inr hz_ne_top) (.inl hx_ne_top) : -(u + v) = -u + -v)
        have hneg_const : -((u + v) + (y c : EReal)) = -(u + v) + (-(y c : EReal)) := by
          simpa [sub_eq_add_neg] using
            (EReal.neg_add (Or.inr (by simp : (y c : EReal) ≠ ⊤))
              (Or.inr (by simp : (y c : EReal) ≠ ⊥)) :
              -((u + v) + (y c : EReal)) = -(u + v) + -(y c : EReal))
        calc
          admm_lagrangian h₁ h₂ A B c x z y
              = (h₁ x - ((A.dualMap (-y)) x : EReal)) +
                  (h₂ z - ((B.dualMap (-y)) z : EReal)) +
                    (-(y c : EReal)) := by
                  rw [admm_lagrangian_eq_affine_split]
          _ = -u + -v + (-(y c : EReal)) := by
                  rw [← hx_split, ← hz_split]
          _ = -(u + v) + (-(y c : EReal)) := by
                  rw [hneg_uv]
          _ = -((u + v) + (y c : EReal)) := by
                  rw [hneg_const.symm]
          _ = -ψ (x, z) := by
                  simp [ψ, u, v]
      calc
        ψ (x, z) = -(-ψ (x, z)) := by simp [ψ]
        _ = -admm_lagrangian h₁ h₂ A B c x z y := by
              rw [hsplit]
    · rw [Set.mem_neg]
      rintro ⟨⟨x, z⟩, hw⟩
      refine ⟨(x, z), ?_⟩
      have hx_ne_top : (((A.dualMap (-y)) x : EReal) - h₁ x) ≠ ⊤ :=
        affinePairingMinusValue_ne_top_of_proper h₁ h₁_proper (A.dualMap (-y)) x
      have hz_ne_top : (((B.dualMap (-y)) z : EReal) - h₂ z) ≠ ⊤ :=
        affinePairingMinusValue_ne_top_of_proper h₂ h₂_proper (B.dualMap (-y)) z
      have hsplit :
          admm_lagrangian h₁ h₂ A B c x z y = -ψ (x, z) := by
        -- Reuse the same normalization when recovering a Lagrangian-range witness.
        let u : EReal := ((A.dualMap (-y)) x : EReal) - h₁ x
        let v : EReal := ((B.dualMap (-y)) z : EReal) - h₂ z
        have hx_split :
            -(((A.dualMap (-y)) x : EReal) - h₁ x) = h₁ x - ((A.dualMap (-y)) x : EReal) := by
          rw [EReal.neg_sub] <;> simp [sub_eq_add_neg, add_comm]
        have hz_split :
            -(((B.dualMap (-y)) z : EReal) - h₂ z) = h₂ z - ((B.dualMap (-y)) z : EReal) := by
          rw [EReal.neg_sub] <;> simp [sub_eq_add_neg, add_comm]
        have hneg_uv : -(u + v) = -u + -v := by
          simpa [u, v, sub_eq_add_neg] using
            (EReal.neg_add (.inr hz_ne_top) (.inl hx_ne_top) : -(u + v) = -u + -v)
        have hneg_const : -((u + v) + (y c : EReal)) = -(u + v) + (-(y c : EReal)) := by
          simpa [sub_eq_add_neg] using
            (EReal.neg_add (Or.inr (by simp : (y c : EReal) ≠ ⊤))
              (Or.inr (by simp : (y c : EReal) ≠ ⊥)) :
              -((u + v) + (y c : EReal)) = -(u + v) + -(y c : EReal))
        calc
          admm_lagrangian h₁ h₂ A B c x z y
              = (h₁ x - ((A.dualMap (-y)) x : EReal)) +
                  (h₂ z - ((B.dualMap (-y)) z : EReal)) +
                    (-(y c : EReal)) := by
                  rw [admm_lagrangian_eq_affine_split]
          _ = -u + -v + (-(y c : EReal)) := by
                  rw [← hx_split, ← hz_split]
          _ = -(u + v) + (-(y c : EReal)) := by
                  rw [hneg_uv]
          _ = -((u + v) + (y c : EReal)) := by
                  rw [hneg_const.symm]
          _ = -ψ (x, z) := by
                  simp [ψ, u, v]
      have hw' : w = admm_lagrangian h₁ h₂ A B c x z y := by
        calc
          w = -(-w) := by simp
          _ = -ψ (x, z) := by rw [← hw]
          _ = admm_lagrangian h₁ h₂ A B c x z y := by
                rw [hsplit]
      exact hw'.symm
  have h₁_conj_ne_bot : conjugate_function h₁ (A.dualMap (-y)) ≠ ⊥ :=
    conjugate_function_ne_bot h₁ h₁_proper (A.dualMap (-y))
  have h₂_conj_ne_bot : conjugate_function h₂ (B.dualMap (-y)) ≠ ⊥ :=
    conjugate_function_ne_bot h₂ h₂_proper (B.dualMap (-y))
  let a : EReal := conjugate_function h₁ (A.dualMap (-y))
  let b : EReal := conjugate_function h₂ (B.dualMap (-y))
  have hneg_ab : -(a + b) = -a + -b := by
    simpa [a, b, sub_eq_add_neg] using
      (EReal.neg_add (.inl h₁_conj_ne_bot) (.inr h₂_conj_ne_bot) : -(a + b) = -a + -b)
  have hneg_const : -((a + b) + (y c : EReal)) = -(a + b) + (-(y c : EReal)) := by
    simpa [sub_eq_add_neg] using
      (EReal.neg_add (Or.inr (by simp : (y c : EReal) ≠ ⊤))
        (Or.inr (by simp : (y c : EReal) ≠ ⊥)) :
        -((a + b) + (y c : EReal)) = -(a + b) + -(y c : EReal))
  -- Rewrite the dual objective as the negative of the separable supremum over `(x, z)`.
  calc
    admm_dual_objective h₁ h₂ A B c y
        = -((a + b) + (y c : EReal)) := by
            calc
              admm_dual_objective h₁ h₂ A B c y = -a + -b + (-(y c : EReal)) := by
                simp [admm_dual_objective, a, b, sub_eq_add_neg, add_assoc]
              _ = -(a + b) + (-(y c : EReal)) := by
                rw [hneg_ab]
              _ = -((a + b) + (y c : EReal)) := by
                rw [hneg_const.symm]
    _ = -(sSup (Set.range fun x : X ↦ ((A.dualMap (-y)) x : EReal) - h₁ x) +
          sSup (Set.range fun z : Z ↦ ((B.dualMap (-y)) z : EReal) - h₂ z) +
            (y c : EReal)) := by
            simp [a, b, conjugate_function_apply]
    _ = -((⨆ x : X, ((A.dualMap (-y)) x : EReal) - h₁ x) +
          (⨆ z : Z, ((B.dualMap (-y)) z : EReal) - h₂ z) +
            (y c : EReal)) := by
            rw [sSup_range, sSup_range]
    _ = -((⨆ xz : X × Z,
            (((A.dualMap (-y)) xz.1 : EReal) - h₁ xz.1) +
              (((B.dualMap (-y)) xz.2 : EReal) - h₂ xz.2)) +
            (y c : EReal)) := by
            rw [ereal_iSup_add_eq_iSup_prod]
    _ = -(⨆ xz : X × Z,
            ((((A.dualMap (-y)) xz.1 : EReal) - h₁ xz.1) +
              (((B.dualMap (-y)) xz.2 : EReal) - h₂ xz.2)) + (y c : EReal)) := by
            rw [(iSup_addRightEReal (y c)
              (fun xz : X × Z ↦
                (((A.dualMap (-y)) xz.1 : EReal) - h₁ xz.1) +
                  (((B.dualMap (-y)) xz.2 : EReal) - h₂ xz.2))).symm]
    _ = -(⨆ xz : X × Z, ψ xz) := by
            simp [ψ, add_assoc]
    _ = -sSup (Set.range ψ) := by
            rw [← sSup_range]
    _ = sInf (-Set.range ψ) := by
            simpa using (ereal_sInf_neg (Set.range ψ)).symm
    _ = sInf (Set.range fun xz : X × Z ↦ admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y) := by
            rw [← hrange]

/-- Under properness hypotheses on both block objectives, the canonical pointwise dual objective
agrees with the source-facing Lagrangian-value formulation `min_{x,z} L(x, z; y)`. -/
theorem admm_dual_objective_eq_admm_dual_lagrangian_value
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (y : Module.Dual ℝ Y) :
    admm_dual_objective h₁ h₂ A B c y =
      admm_dual_lagrangian_value h₁ h₂ A B c y :=
  admm_dual_objective_eq_sInf_lagrangian h₁ h₂ A B c h₁_proper h₂_proper y

/-- Definition 15.2 (3): the value of the ADMM dual maximization problem. -/
def admm_dual_problem_value
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) : EReal :=
  sSup (Set.range (admm_dual_objective h₁ h₂ A B c))

/-- The ADMM dual optimal value is the supremum of the range of `admm_dual_objective`. -/
theorem admm_dual_problem_value_eq_sSup
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) :
    admm_dual_problem_value h₁ h₂ A B c =
      sSup (Set.range (admm_dual_objective h₁ h₂ A B c)) := rfl

/-- Definition 15.2 (4): the equivalent minimization-form ADMM dual objective
`h₁^*(-Aᵀ y) + h₂^*(-Bᵀ y) + ⟨c, y⟩`. -/
def admm_dual_minimization_objective
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) : Module.Dual ℝ Y → EReal :=
  fun y ↦
    conjugate_function h₁ (A.dualMap (-y)) +
      conjugate_function h₂ (B.dualMap (-y)) +
        (y c : EReal)

/-- Evaluating the minimization-form ADMM dual objective gives the positive conjugate sum from
Definition 15.2. -/
@[simp] theorem admm_dual_minimization_objective_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Module.Dual ℝ Y) :
    admm_dual_minimization_objective h₁ h₂ A B c y =
      conjugate_function h₁ (A.dualMap (-y)) +
        conjugate_function h₂ (B.dualMap (-y)) +
          (y c : EReal) :=
  rfl

/-- Helper for Definition 15.2: if both conjugate terms avoid `⊥`, then the minimization-form
objective is pointwise the negation of the maximization-form dual objective. -/
private theorem admm_dual_minimization_view_apply_of_nonbot
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Module.Dual ℝ Y)
    (h₁_ne_bot : conjugate_function h₁ (A.dualMap (-y)) ≠ ⊥)
    (h₂_ne_bot : conjugate_function h₂ (B.dualMap (-y)) ≠ ⊥) :
    admm_dual_minimization_objective h₁ h₂ A B c y =
      -admm_dual_objective h₁ h₂ A B c y := by
  let a := conjugate_function h₁ (A.dualMap (-y))
  let b := conjugate_function h₂ (B.dualMap (-y))
  have ha_top : -a ≠ ⊤ := by
    intro ha
    have : a = ⊥ := by
      simpa [a] using congrArg Neg.neg ha
    exact h₁_ne_bot this
  have hab :
      -(-a - b) = a + b := by
    -- First collapse the negated two-term maximization objective to the positive sum `a + b`.
    have hraw : -(-a - b) = -(-a) + b := by
      exact EReal.neg_sub (Or.inr h₂_ne_bot) (Or.inl ha_top)
    simpa [a, b] using hraw
  -- Then use the finiteness of the scalar pairing term to absorb the final negation.
  calc
    admm_dual_minimization_objective h₁ h₂ A B c y = a + b + (y c : EReal) := by
      rfl
    _ = -(-a - b) + (y c : EReal) := by
      rw [hab]
    _ = -((-a - b) - (y c : EReal)) := by
      symm
      exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
    _ = -admm_dual_objective h₁ h₂ A B c y := by
      rfl

/-- Evaluating the minimization view gives the positive conjugate sum from Definition 15.2. -/
@[simp] theorem admm_dual_minimization_view_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Module.Dual ℝ Y)
    (h₁_ne_bot : conjugate_function h₁ (A.dualMap (-y)) ≠ ⊥)
    (h₂_ne_bot : conjugate_function h₂ (B.dualMap (-y)) ≠ ⊥) :
    admm_dual_minimization_objective h₁ h₂ A B c y =
      -admm_dual_objective h₁ h₂ A B c y :=
  admm_dual_minimization_view_apply_of_nonbot h₁ h₂ A B c y h₁_ne_bot h₂_ne_bot

/-- Under properness hypotheses on both block objectives, the minimization-form ADMM dual
objective is pointwise the negation of the maximization-form dual objective. -/
theorem admm_dual_minimization_objective_eq_neg_admm_dual_objective
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (y : Module.Dual ℝ Y) :
    admm_dual_minimization_objective h₁ h₂ A B c y =
      -admm_dual_objective h₁ h₂ A B c y :=
  admm_dual_minimization_view_apply h₁ h₂ A B c y
    (conjugate_function_ne_bot h₁ h₁_proper (A.dualMap (-y)))
    (conjugate_function_ne_bot h₂ h₂_proper (B.dualMap (-y)))

/-- Helper for Definition 15.2: under global non-`⊥` hypotheses on the two conjugate terms, the
minimization-form objective range is the pointwise negation of the ADMM dual-objective range. -/
private theorem admm_dual_minimization_range_eq_neg_dual_range_of_nonbot
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (h₁_ne_bot : ∀ y, conjugate_function h₁ (A.dualMap (-y)) ≠ ⊥)
    (h₂_ne_bot : ∀ y, conjugate_function h₂ (B.dualMap (-y)) ≠ ⊥) :
    Set.range (admm_dual_minimization_objective h₁ h₂ A B c) =
      -Set.range (admm_dual_objective h₁ h₂ A B c) := by
  -- Translate the pointwise negation identity into the exact range equality needed by `sInf`.
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rw [admm_dual_minimization_view_apply_of_nonbot h₁ h₂ A B c y (h₁_ne_bot y) (h₂_ne_bot y)]
    simp [Set.mem_neg]
  · intro hz
    have hz' : -z ∈ Set.range (admm_dual_objective h₁ h₂ A B c) := by
      simpa [Set.mem_neg] using hz
    rcases hz' with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [admm_dual_minimization_view_apply_of_nonbot h₁ h₂ A B c y (h₁_ne_bot y) (h₂_ne_bot y)]
    simpa using congrArg Neg.neg hy

/-- Source-facing optimization-value companion to Definition 15.2 (4): the minimization-form ADMM
dual problem value `min_y { h₁^*(-Aᵀ y) + h₂^*(-Bᵀ y) + ⟨c, y⟩ }`, represented canonically by an
`EReal` infimum. -/
def admm_dual_minimization_problem_value
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) : EReal :=
  sInf (Set.range (admm_dual_minimization_objective h₁ h₂ A B c))

/-- The minimization-form ADMM dual problem value is the infimum of the range of
`admm_dual_minimization_objective`. -/
theorem admm_dual_minimization_problem_value_eq_sInf
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) :
    admm_dual_minimization_problem_value h₁ h₂ A B c =
      sInf (Set.range (admm_dual_minimization_objective h₁ h₂ A B c)) :=
  rfl

/-- Under properness hypotheses on both block objectives, the minimization-form ADMM dual problem
value is the negation of the maximization-form dual problem value. -/
theorem admm_dual_minimization_problem_value_eq_neg_admm_dual_problem_value
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂) :
    admm_dual_minimization_problem_value h₁ h₂ A B c =
      -admm_dual_problem_value h₁ h₂ A B c :=
  by
  -- Rewrite both optimization values to range-level `sInf`/`sSup` owners and negate the range.
  rw [admm_dual_minimization_problem_value_eq_sInf, admm_dual_problem_value_eq_sSup]
  rw [admm_dual_minimization_range_eq_neg_dual_range_of_nonbot
    h₁ h₂ A B c
    (fun y ↦ conjugate_function_ne_bot h₁ h₁_proper (A.dualMap (-y)))
    (fun y ↦ conjugate_function_ne_bot h₂ h₂_proper (B.dualMap (-y)))]
  exact ereal_sInf_neg (Set.range (admm_dual_objective h₁ h₂ A B c))

-- Proof sketch: combine `admm_dual_problem_value_eq_sSup` with
-- `admm_dual_minimization_view_apply`, then use the order-reversing relation between
-- `sSup` and `sInf` under negation on `EReal`.
/-- Under properness hypotheses on both block objectives, the dual maximization problem is
equivalent to minimizing the source formula
`h₁^*(-Aᵀ y) + h₂^*(-Bᵀ y) + ⟨c, y⟩`. -/
theorem admm_dual_minimization_infimum_eq_neg_dual_problem_value
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂) :
    sInf (Set.range (admm_dual_minimization_objective h₁ h₂ A B c)) =
      -admm_dual_problem_value h₁ h₂ A B c :=
  admm_dual_minimization_problem_value_eq_neg_admm_dual_problem_value
    h₁ h₂ A B c h₁_proper h₂_proper

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup Z] [Module ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The primal-space view of the ADMM dual objective, obtained by evaluating the canonical
dual-space owner along the Riesz map `toDualMap ℝ Y : Y → Y*`. -/
noncomputable abbrev admm_dual_objective_primal
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) : Y → EReal :=
  fun y ↦ admm_dual_objective h₁ h₂ A B c (toDualMap ℝ Y y)

end

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Evaluating the ADMM dual objective on the primal-space variable `y` gives the source formula
`q(y) = -h₁*(-Aᵀ y) - h₂*(-Bᵀ y) - ⟪c, y⟫`. -/
@[simp] theorem admm_dual_objective_primal_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Y) :
    admm_dual_objective_primal h₁ h₂ A B c y =
      -(h₁∗) (-A.adjoint y) - (h₂∗) (-B.adjoint y) -
        ((inner ℝ c y : ℝ) : EReal) := by
  have hA : A.dualMap (-toDualMap ℝ Y y) = toDualMap ℝ X (-A.adjoint y) := by
    ext x
    simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, A.adjoint_inner_left]
  have hB : B.dualMap (-toDualMap ℝ Y y) = toDualMap ℝ Z (-B.adjoint y) := by
    ext z
    simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, B.adjoint_inner_left]
  simp [admm_dual_objective_primal, admm_dual_objective, hA, hB,
    conjugate_function_primal_apply, InnerProductSpace.toDualMap_apply_apply, real_inner_comm]

/-- Evaluating the primal-space minimization view gives the source formula
`h₁*(-Aᵀ y) + h₂*(-Bᵀ y) + ⟪c, y⟫ = -q(y)` at any point where both conjugate terms avoid `⊥`. -/
theorem admm_dual_minimization_view_primal_apply_of_nonbot
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Y)
    (h₁_ne_bot : (h₁∗) (-A.adjoint y) ≠ ⊥)
    (h₂_ne_bot : (h₂∗) (-B.adjoint y) ≠ ⊥) :
    (h₁∗) (-A.adjoint y) +
      (h₂∗) (-B.adjoint y) +
        ((inner ℝ c y : ℝ) : EReal) =
      -admm_dual_objective_primal h₁ h₂ A B c y := by
  have hA : A.dualMap (-toDualMap ℝ Y y) = toDualMap ℝ X (-A.adjoint y) := by
    ext x
    simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, A.adjoint_inner_left]
  have hB : B.dualMap (-toDualMap ℝ Y y) = toDualMap ℝ Z (-B.adjoint y) := by
    ext z
    simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, B.adjoint_inner_left]
  simpa [admm_dual_objective_primal, hA, hB, conjugate_function_primal_apply,
    InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using
    (admm_dual_minimization_view_apply h₁ h₂ A B c (toDualMap ℝ Y y)
      (by simpa [hA, conjugate_function_primal_apply] using h₁_ne_bot)
      (by simpa [hB, conjugate_function_primal_apply] using h₂_ne_bot))

/-- Evaluating the primal-space minimization view gives the source formula
`h₁*(-Aᵀ y) + h₂*(-Bᵀ y) + ⟪c, y⟫ = -q(y)` under the properness hypotheses needed
to rule out `⊥` in the conjugate terms. -/
@[simp] theorem admm_dual_minimization_view_primal_apply
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y) (y : Y)
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂) :
    (h₁∗) (-A.adjoint y) + (h₂∗) (-B.adjoint y) + ((inner ℝ c y : ℝ) : EReal) =
      -admm_dual_objective_primal h₁ h₂ A B c y := by
  have hA : A.dualMap (-toDualMap ℝ Y y) = toDualMap ℝ X (-A.adjoint y) := by
    ext x
    simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, A.adjoint_inner_left]
  have hB : B.dualMap (-toDualMap ℝ Y y) = toDualMap ℝ Z (-B.adjoint y) := by
    ext z
    simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, B.adjoint_inner_left]
  simpa [admm_dual_objective_primal, admm_dual_minimization_objective, hA, hB,
    conjugate_function_primal_apply, InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using
    (admm_dual_minimization_objective_eq_neg_admm_dual_objective
      h₁ h₂ A B c h₁_proper h₂_proper (toDualMap ℝ Y y))

end
