/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_3
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

-- The minimization-view bridge below follows the Chapter 4 owner shape
-- `fenchel_dual_objective_eq_sInf_split_lagrangian`: the relevant data is the dual objective,
-- the split Lagrangian, and properness of the two extended-real functions.

section

variable {E : Type u} {Y : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup Y] [Module ℝ Y]

/- Definition 12.4 is `source-facing`: it introduces the Lagrange dual maximization model attached
to the split Lagrangian formula from equation (12.3). The `core/canonical` owners already present
in the project are Chapter 4's `conjugate_function` for Fenchel conjugates and `LinearMap.dualMap`
for the transpose pullback `Aᵀ y`, so the dual-space formulation below is the owner-level Chapter
12 realization, while the primal-space version on `Y` is a `bridge/view` through the Riesz map. -/

/-- Helper for Definition 12.4: the canonical dual-space realization of the Lagrange dual
objective, written with the Chapter 4 conjugate owner and the pullback `A.dualMap`. -/
def dual_based_proximal_gradient_lagrange_dual_objective
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) : Module.Dual ℝ Y → EReal :=
  fun y ↦ -conjugate_function f (A.dualMap y) - conjugate_function g (-y)

-- Proof sketch: unfold `dual_based_proximal_gradient_lagrange_dual_objective`; this is exactly
-- the textbook formula `q(y) = -f*(Aᵀ y) - g*(-y)` with `Aᵀ y` realized by `A.dualMap y`.
/-- Evaluating the Lagrange dual objective at `y` gives `-f*(Aᵀ y) - g*(-y)`. -/
@[simp] theorem dual_based_proximal_gradient_lagrange_dual_objective_apply
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) (y : Module.Dual ℝ Y) :
    dual_based_proximal_gradient_lagrange_dual_objective f g A y =
      -conjugate_function f (A.dualMap y) - conjugate_function g (-y) := rfl

end

section

variable {E : Type u} {Y : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The source-space Lagrange dual objective for Definition 12.4 is
`q(y) = -f*(Aᵀ y) - g*(-y)`, with `Aᵀ y` realized by `A.adjoint y` under the chapter's
inner-product identifications. -/
abbrev dual_based_proximal_gradient_lagrange_dual_objective_primal
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) : Y → EReal :=
  fun y ↦ -(f∗) (A.adjoint y) - (g∗) (-y)

end

section

variable {E : Type u} {Y : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Evaluating the Chapter 12 dual objective on the primal-space variable `y` gives the source
formula `q(y) = -f*(Aᵀ y) - g*(-y)`. -/
@[simp] theorem dual_based_proximal_gradient_lagrange_dual_objective_primal_apply
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) (y : Y) :
    dual_based_proximal_gradient_lagrange_dual_objective_primal f g A y =
      -(f∗) (A.adjoint y) - (g∗) (-y) := rfl

end

section

variable {E : Type u} {Y : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup Y] [Module ℝ Y]

end

section

variable {E : Type u} {Y : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup Y] [Module ℝ Y]

/-- Definition 12.4: for proper extended-real-valued `f` and `g`, minimizing the Definition 12.3
Lagrangian over `(x, z)` yields the dual objective `q(y)`. This is the Chapter 12 analogue of the
Chapter 4 split Fenchel identity `q(y) = inf_{x,z} L(x, z; y)`. -/
theorem dual_based_proximal_gradient_lagrange_dual_objective_eq_sInf_lagrangian_formula
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) (y : Module.Dual ℝ Y)
    (hf_proper : IsProperExtendedRealFunction f) (hg_proper : IsProperExtendedRealFunction g) :
    dual_based_proximal_gradient_lagrange_dual_objective f g A y =
      sInf (Set.range fun xz : E × Y ↦
        dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y) := by
  let ψ : E × Y → EReal :=
    fun xz ↦ (((A.dualMap y) xz.1 : EReal) - f xz.1) + (((-y) xz.2 : EReal) - g xz.2)
  have hrange :
      Set.range (fun xz : E × Y ↦ dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y) =
        -Set.range ψ := by
    -- Normalize the Lagrangian range once so the main proof can stay at the conjugate API level.
    ext w
    constructor
    · rintro ⟨⟨x, z⟩, rfl⟩
      rw [Set.mem_neg]
      refine ⟨(x, z), ?_⟩
      have hx_ne_top : (((A.dualMap y) x : EReal) - f x) ≠ ⊤ :=
        affinePairingMinusValue_ne_top_of_proper f hf_proper (A.dualMap y) x
      have hz_ne_top : (((-y) z : EReal) - g z) ≠ ⊤ :=
        affinePairingMinusValue_ne_top_of_proper g hg_proper (-y) z
      have hsplit :
          dual_based_proximal_gradient_lagrangian f g A x z y =
            -((((A.dualMap y) x : EReal) - f x) + (((-y) z : EReal) - g z)) := by
        -- Rewrite the Chapter 12 Lagrangian as a single negated affine-conjugate integrand.
        have hx_split :
            -(((A.dualMap y) x : EReal) - f x) = f x - ((A.dualMap y) x : EReal) := by
          rw [EReal.neg_sub] <;> simp [sub_eq_add_neg, add_comm]
        have hz_split : -((((-y) z : EReal) - g z)) = g z + (y z : EReal) := by
          rw [EReal.neg_sub] <;> simp [add_comm]
        calc
          dual_based_proximal_gradient_lagrangian f g A x z y
              = (f x - ((A.dualMap y) x : EReal)) + (g z + (y z : EReal)) := by
                  rw [dual_based_proximal_gradient_lagrangian_eq_affine_split]
          _ = -(((A.dualMap y) x : EReal) - f x) - ((((-y) z : EReal) - g z)) := by
                  rw [← hx_split, ← hz_split]
                  simp [sub_eq_add_neg]
          _ = -((((A.dualMap y) x : EReal) - f x) + (((-y) z : EReal) - g z)) := by
                  rw [(EReal.neg_add (.inr hz_ne_top) (.inl hx_ne_top)).symm]
      calc
        ψ (x, z) = -(-ψ (x, z)) := by simp [ψ]
        _ = -dual_based_proximal_gradient_lagrangian f g A x z y := by
          rw [hsplit]
    · rw [Set.mem_neg]
      rintro ⟨⟨x, z⟩, hw⟩
      refine ⟨(x, z), ?_⟩
      have hx_ne_top : (((A.dualMap y) x : EReal) - f x) ≠ ⊤ :=
        affinePairingMinusValue_ne_top_of_proper f hf_proper (A.dualMap y) x
      have hz_ne_top : (((-y) z : EReal) - g z) ≠ ⊤ :=
        affinePairingMinusValue_ne_top_of_proper g hg_proper (-y) z
      have hsplit :
          dual_based_proximal_gradient_lagrangian f g A x z y =
            -((((A.dualMap y) x : EReal) - f x) + (((-y) z : EReal) - g z)) := by
        -- Reuse the same normalization when recovering a Lagrangian-range witness.
        have hx_split :
            -(((A.dualMap y) x : EReal) - f x) = f x - ((A.dualMap y) x : EReal) := by
          rw [EReal.neg_sub] <;> simp [sub_eq_add_neg, add_comm]
        have hz_split : -((((-y) z : EReal) - g z)) = g z + (y z : EReal) := by
          rw [EReal.neg_sub] <;> simp [add_comm]
        calc
          dual_based_proximal_gradient_lagrangian f g A x z y
              = (f x - ((A.dualMap y) x : EReal)) + (g z + (y z : EReal)) := by
                  rw [dual_based_proximal_gradient_lagrangian_eq_affine_split]
          _ = -(((A.dualMap y) x : EReal) - f x) - ((((-y) z : EReal) - g z)) := by
                  rw [← hx_split, ← hz_split]
                  simp [sub_eq_add_neg]
          _ = -((((A.dualMap y) x : EReal) - f x) + (((-y) z : EReal) - g z)) := by
                  rw [(EReal.neg_add (.inr hz_ne_top) (.inl hx_ne_top)).symm]
      have hw' : w = dual_based_proximal_gradient_lagrangian f g A x z y := by
        calc
          w = -(-w) := by simp
          _ = -ψ (x, z) := by rw [← hw]
          _ = dual_based_proximal_gradient_lagrangian f g A x z y := by
            rw [hsplit]
      exact hw'.symm
  have hf_conj_ne_bot : conjugate_function f (A.dualMap y) ≠ ⊥ :=
    conjugate_function_ne_bot_of_proper f hf_proper (A.dualMap y)
  have hg_conj_ne_bot : conjugate_function g (-y) ≠ ⊥ :=
    conjugate_function_ne_bot_of_proper g hg_proper (-y)
  -- Rewrite the dual objective as the negative of a separable supremum over `(x, z)`.
  calc
    dual_based_proximal_gradient_lagrange_dual_objective f g A y
        = -(conjugate_function f (A.dualMap y) + conjugate_function g (-y)) := by
            rw [dual_based_proximal_gradient_lagrange_dual_objective_apply]
            rw [(EReal.neg_add (.inl hf_conj_ne_bot) (.inr hg_conj_ne_bot)).symm]
    _ = -(sSup (Set.range fun x : E ↦ ((A.dualMap y) x : EReal) - f x) +
          sSup (Set.range fun z : Y ↦ (((-y) z : EReal) - g z))) := by
            rw [conjugate_function_apply, conjugate_function_apply]
    _ = -((⨆ x : E, ((A.dualMap y) x : EReal) - f x) +
          ⨆ z : Y, (((-y) z : EReal) - g z)) := by
            rw [sSup_range, sSup_range]
    _ = -(⨆ xz : E × Y, ψ xz) := by
            rw [ereal_iSup_add_eq_iSup_prod]
    _ = -sSup (Set.range ψ) := by
            rw [← sSup_range]
    _ = sInf (-Set.range ψ) := by
            simpa using (ereal_sInf_neg (Set.range ψ)).symm
    _ = sInf (Set.range fun xz : E × Y ↦
          dual_based_proximal_gradient_lagrangian f g A xz.1 xz.2 y) := by
            rw [← hrange]

end

section

variable {E : Type u} {Y : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup Y] [Module ℝ Y]

/-- The optimal value `q_opt` of the Lagrange dual problem is the supremum of the range of the
dual objective `q`. -/
def dual_based_proximal_gradient_lagrange_dual_problem_value
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) : EReal :=
  sSup (Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A))

/-- Expanding `q_opt` gives the supremum of the attained values of the dual objective `q`. -/
@[simp] theorem dual_based_proximal_gradient_lagrange_dual_problem_value_eq_sSup
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) :
    dual_based_proximal_gradient_lagrange_dual_problem_value f g A =
      sSup (Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A)) :=
  rfl

end
