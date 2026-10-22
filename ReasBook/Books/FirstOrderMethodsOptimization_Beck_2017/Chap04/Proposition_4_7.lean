/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Helper for Proposition 4.7: multiplying by a positive real scalar preserves suprema of
`EReal` ranges. -/
lemma erealPosMul_sSup_range {ι : Sort*} (α : ℝ) (hα : 0 < α) (φ : ι → EReal) :
    sSup (Set.range fun i ↦ (α : EReal) * φ i) = (α : EReal) * sSup (Set.range φ) := by
  have hαE : (0 : EReal) < (α : EReal) := by
    exact_mod_cast hα
  have hRange :
      Set.range (fun i ↦ (α : EReal) * φ i) =
        (fun x : EReal ↦ (α : EReal) * x) '' Set.range φ := by
    -- Identify the scaled range with the image under multiplication by the positive scalar.
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨φ i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hMon : Monotone (fun x : EReal ↦ (α : EReal) * x) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left hab hαE.le
  have hBot : (fun x : EReal ↦ (α : EReal) * x) ⊥ = ⊥ := by
    simpa using EReal.coe_mul_bot_of_pos hα
  have hCont :
      ContinuousAt (fun x : EReal ↦ (α : EReal) * x) (sSup (Set.range φ)) := by
    simpa using
      (EReal.Tendsto.const_mul (a := (α : EReal)) (b := sSup (Set.range φ))
        continuousAt_id.tendsto
        (Or.inl (EReal.coe_ne_bot α)) (Or.inl (EReal.coe_ne_top α)))
  -- Transport the supremum across the order isomorphism once and reuse the resulting formula.
  calc
    sSup (Set.range fun i ↦ (α : EReal) * φ i)
        = sSup ((fun x : EReal ↦ (α : EReal) * x) '' Set.range φ) := by
            rw [hRange]
    _ = (α : EReal) * sSup (Set.range φ) := by
          symm
          exact hMon.map_sSup_of_continuousAt (s := Set.range φ) hCont hBot

/-- Helper for Proposition 4.7: a positive finite `EReal` scalar distributes across subtraction.
-/
lemma erealPosMul_sub (α : ℝ) (hα : 0 < α) (a b : EReal) :
    (α : EReal) * (a - b) = (α : EReal) * a - (α : EReal) * b := by
  have hαE : (0 : EReal) ≤ (α : EReal) := by
    exact_mod_cast hα.le
  -- Rewrite subtraction as addition of a negation so the existing positive-distributivity API
  -- applies to the finite scalar `(α : EReal)`.
  rw [sub_eq_add_neg, EReal.left_distrib_of_nonneg_of_ne_top hαE (EReal.coe_ne_top α), mul_neg,
    sub_eq_add_neg]

/-- Helper for Proposition 4.7: dual evaluation can be rewritten by rescaling the dual vector by
`(1 / α)`. -/
lemma erealDualPairing_eq_posMul_invSmulPairing
    (α : ℝ) (hα : 0 < α) (y : Module.Dual ℝ E) (x : E) :
    (y x : EReal) = (α : EReal) * ((((1 / α) • y) x : ℝ) : EReal) := by
  -- Move the scalar action from the dual vector to the real pairing, then cancel `α * α⁻¹`.
  symm
  calc
    (α : EReal) * ((((1 / α) • y) x : ℝ) : EReal)
        = ((α * (((1 / α) • y) x : ℝ) : ℝ) : EReal) := by
            rw [← EReal.coe_mul]
    _ = (y x : EReal) := by
          congr 1
          simp [LinearMap.smul_apply, smul_eq_mul, one_div, hα.ne']

/-- Helper for Proposition 4.7: dual evaluation of a scaled primal vector factors out the scalar.
-/
lemma erealDualPairing_smul_eq_posMulPairing
    (α : ℝ) (y : Module.Dual ℝ E) (x : E) :
    (y (α • x) : EReal) = (α : EReal) * (y x : EReal) := by
  -- Use linearity of the dual map, then cast the resulting real multiplication into `EReal`.
  calc
    (y (α • x) : EReal) = ((α * y x : ℝ) : EReal) := by
        congr 1
        rw [y.map_smul, smul_eq_mul]
    _ = (α : EReal) * (y x : EReal) := by
          rw [EReal.coe_mul]

/-- Helper for Proposition 4.7: precomposing with `x ↦ (1 / α) • x` does not change the range of
an `EReal`-valued function when `α ≠ 0`. -/
lemma range_comp_invSmul (α : ℝ) (hα0 : α ≠ 0) (ψ : E → EReal) :
    Set.range (fun x : E ↦ ψ ((1 / α) • x)) = Set.range ψ := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(1 / α) • x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨α • x, ?_⟩
    -- The inverse scaling returns the original primal point.
    have hInv : (1 / α) • (α • x) = x := by
      simpa [one_div, smul_smul] using (inv_smul_smul₀ hα0 x)
    simpa [one_div] using congrArg ψ hInv

/- Proposition 4.7 is `source-facing` in the chapter Fenchel-conjugacy API. The `core/canonical`
owner is Definition 4.1's `conjugate_function`, so this file keeps only the two positive-scaling
calculus identities from equations (4.14a) and (4.14b). -/

-- Proof sketch: expand the defining supremum of `conjugate_function`. For `α > 0`, rewrite
-- `y x - α f x` as `α * (((1 / α) • y) x - f x)`, then pull the positive scalar `(α : EReal)`
-- through the supremum.
/-- Equation (4.14a) from Proposition 4.7: scaling an extended-real-valued function by a positive
real scalar scales its conjugate by the same scalar and rescales the dual argument by `(1 / α)`,
the Lean form of `y / α`. -/
theorem conjugate_function_pos_real_mul
    (f : E → EReal) (α : ℝ) (hα : 0 < α) :
    conjugate_function (fun x ↦ (α : EReal) * f x) =
      fun y ↦ (α : EReal) * conjugate_function f ((1 / α) • y) := by
  funext y
  rw [conjugate_function_apply, conjugate_function_apply]
  -- Rewrite each Fenchel integrand into a positive scalar times the original conjugate integrand.
  have hIntegrand :
      (fun x : E ↦ (y x : EReal) - (α : EReal) * f x) =
        fun x : E ↦ (α : EReal) * (((((1 / α) • y) x : ℝ) : EReal) - f x) := by
    funext x
    calc
      (y x : EReal) - (α : EReal) * f x
          = (α : EReal) * ((((1 / α) • y) x : ℝ) : EReal) - (α : EReal) * f x := by
              rw [erealDualPairing_eq_posMul_invSmulPairing α hα y x]
      _ = (α : EReal) * (((((1 / α) • y) x : ℝ) : EReal) - f x) := by
            rw [← erealPosMul_sub α hα ((((1 / α) • y) x : ℝ) : EReal) (f x)]
  -- Pull the positive scalar through the supremum using the reusable order-isomorphism lemma.
  rw [hIntegrand, erealPosMul_sSup_range α hα]

-- Proof sketch: expand the defining supremum of `conjugate_function` and substitute
-- `u = (1 / α) • x`, equivalently `x = α • u`. Because `α > 0`, this change of variables is a
-- bijection of `E`, and the supremum becomes `(α : EReal)` times the defining supremum of
-- `conjugate_function f`.
/-- Equation (4.14b) from Proposition 4.7: for a positive real scalar `α`, the conjugate of
`x ↦ α f ((1 / α) • x)` is `y ↦ α f*(y)`. -/
theorem conjugate_function_pos_real_precomp_inv_smul
    (f : E → EReal) (α : ℝ) (hα : 0 < α) :
    conjugate_function (fun x ↦ (α : EReal) * f ((1 / α) • x)) =
      fun y ↦ (α : EReal) * conjugate_function f y := by
  funext y
  rw [conjugate_function_apply, conjugate_function_apply]
  -- Route correction: change variables on the indexing set first, then normalize the pairing.
  have hRange :
      Set.range (fun x : E ↦ (y x : EReal) - (α : EReal) * f ((1 / α) • x)) =
        Set.range (fun u : E ↦ (y (α • u) : EReal) - (α : EReal) * f u) := by
    calc
      Set.range (fun x : E ↦ (y x : EReal) - (α : EReal) * f ((1 / α) • x))
          = Set.range
              (fun x : E ↦ ((fun u : E ↦ (y (α • u) : EReal) - (α : EReal) * f u)
                ((1 / α) • x))) := by
                  congr 1
                  funext x
                  simp [one_div, smul_inv_smul₀ hα.ne']
      _ = Set.range (fun u : E ↦ (y (α • u) : EReal) - (α : EReal) * f u) := by
            simpa using
              (range_comp_invSmul α hα.ne'
                (fun u : E ↦ (y (α • u) : EReal) - (α : EReal) * f u))
  have hIntegrand :
      (fun u : E ↦ (y (α • u) : EReal) - (α : EReal) * f u) =
        fun u : E ↦ (α : EReal) * ((y u : EReal) - f u) := by
    funext u
    calc
      (y (α • u) : EReal) - (α : EReal) * f u
          = (α : EReal) * (y u : EReal) - (α : EReal) * f u := by
              rw [erealDualPairing_smul_eq_posMulPairing α y u]
      _ = (α : EReal) * ((y u : EReal) - f u) := by
            rw [← erealPosMul_sub α hα (y u : EReal) (f u)]
  -- After the substitution, the same positive-scalar supremum factorization finishes the proof.
  rw [hRange, hIntegrand, erealPosMul_sSup_range α hα]

/-- Proposition 4.7: the Fenchel conjugate intertwines positive scalar multiplication both for
`x ↦ α f x` and for `x ↦ α f ((1 / α) • x)`, yielding equations (4.14a) and (4.14b). -/
theorem conjugate_function_pos_real_scaling
    (f : E → EReal) (α : ℝ) (hα : 0 < α) :
    (conjugate_function (fun x ↦ (α : EReal) * f x) =
        fun y ↦ (α : EReal) * conjugate_function f ((1 / α) • y)) ∧
      (conjugate_function (fun x ↦ (α : EReal) * f ((1 / α) • x)) =
        fun y ↦ (α : EReal) * conjugate_function f y) := by
  constructor
  · exact conjugate_function_pos_real_mul f α hα
  · exact conjugate_function_pos_real_precomp_inv_smul f α hα

end

section

open InnerProductSpace (toDualMap)
open scoped Pointwise

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 4.7 remains `source-facing` on the algebraic-dual owner `conjugate_function`.
The two theorems below are `bridge/view` API for the primal-space notation `f∗`, so later
inner-product-space chapters can reuse the same scaling identities without rebuilding them from
`toDualMap`. -/
recall conjugate_function_primal

/-- Primal-space companion to Proposition 4.7 (1): on a real inner product space, the scaled
primal Fenchel conjugate `((α : EReal) • f)∗` is `y ↦ α * f∗((1 / α) • y)`. -/
theorem conjugate_function_primal_pos_real_mul
    (f : E → EReal) (α : ℝ) (hα : 0 < α) :
    (((α : EReal) • f)∗) = fun y ↦ (α : EReal) * (f∗) ((1 / α) • y) := by
  funext y
  simpa [conjugate_function_primal_apply, Pi.smul_apply, smul_eq_mul] using
    congrFun (conjugate_function_pos_real_mul f α hα) (toDualMap ℝ E y)

/-- Primal-space companion to Proposition 4.7 (2): on a real inner product space, the conjugate
of `x ↦ α f ((1 / α) • x)` is `y ↦ α f∗(y)`. -/
theorem conjugate_function_primal_pos_real_precomp_inv_smul
    (f : E → EReal) (α : ℝ) (hα : 0 < α) :
    ((fun x ↦ (α : EReal) * f ((1 / α) • x))∗) = fun y ↦ (α : EReal) * (f∗) y := by
  funext y
  simpa [conjugate_function_primal_apply] using
    congrFun (conjugate_function_pos_real_precomp_inv_smul f α hα) (toDualMap ℝ E y)

end
