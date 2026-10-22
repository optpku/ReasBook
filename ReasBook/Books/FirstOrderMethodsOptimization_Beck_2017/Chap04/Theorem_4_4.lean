/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {V : Type u} {E : Type v}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup E] [Module ℝ E]

/- Theorem 4.4 is `source-facing` in the chapter conjugacy API. Its primitive owner is
`conjugate_function` from Definition 4.1, while the inverse transpose in the textbook formula is
the canonical mathlib dual equivalence `A.dualMap.symm`. -/

/-- Helper for Theorem 4.4: adding a fixed `EReal` constant commutes with taking an indexed
supremum. -/
lemma iSup_addRightEReal {ι : Sort*} (K : ℝ) (h : ι → EReal) :
    (⨆ i, h i + (K : EReal)) = (⨆ i, h i) + K := by
  let e : EReal ≃o EReal :=
    { toEquiv :=
        { toFun := fun x ↦ x + (K : EReal)
          invFun := fun x ↦ x - K
          left_inv := fun x ↦ EReal.add_sub_cancel_right
          right_inv := fun x ↦ EReal.sub_add_cancel }
      map_rel_iff' := by
        intro x y
        simpa using (EReal.addLECancellable_coe K).add_le_add_iff_right }
  -- Transport the supremum through the additive order isomorphism once.
  calc
    (⨆ i, h i + (K : EReal)) = ⨆ i, e (h i) := by
      rfl
    _ = e (⨆ i, h i) := by
      rw [← e.map_iSup]
    _ = (⨆ i, h i) + K := by
      rfl

/-- Helper for Theorem 4.4: the change of variables `x ↦ A (x - a)` transports the indexing
supremum from `V` to `E`. -/
lemma affineChangeOfVariables_iSup
    (a : V) (A : V ≃ₗ[ℝ] E) (core : E → EReal) :
    (⨆ x : V, core (A (x - a))) = ⨆ z : E, core z := by
  let e : V ≃ E := (Equiv.subRight a).trans A.toEquiv
  -- Rewrite the index change as composition with an equivalence.
  simpa [e] using (Equiv.iSup_comp (g := core) e)

/-- Helper for Theorem 4.4: the affine-precomposed Fenchel integrand splits into the pulled-back
core term and the constant `y a - c - b a`. -/
lemma affineChangeIntegrand_eq_core_addConstant
    (f : E → EReal) (A : V ≃ₗ[ℝ] E) (a : V) (b y : Module.Dual ℝ V) (c : ℝ) (x : V) :
    (y x : EReal) - (f (A (x - a)) + (b x : EReal) + (c : EReal)) =
      (((A.dualMap.symm (y - b)) (A (x - a)) : ℝ) : EReal) - f (A (x - a)) +
        ((y a - c - b a : ℝ) : EReal) := by
  let z : E := A (x - a)
  have hPairing :
      (A.dualMap.symm (y - b)) z + (y a - c - b a) = y x - b x - c := by
    -- Evaluate the inverse-transpose term on `z = A (x - a)` and simplify the real arithmetic.
    calc
      (A.dualMap.symm (y - b)) z + (y a - c - b a)
          = ((y - b) (x - a)) + (y a - c - b a) := by
              rw [LinearEquiv.dualMap_symm, LinearEquiv.dualMap_apply]
              simp [z]
      _ = (y (x - a) - b (x - a)) + (y a - c - b a) := by
            rfl
      _ = ((y x - y a) - (b x - b a)) + (y a - c - b a) := by
            rw [show y (x - a) = y x - y a by simp]
            rw [show b (x - a) = b x - b a by simp]
      _ = y x - b x - c := by
            ring
  have hCast :
      (((A.dualMap.symm (y - b)) z : ℝ) : EReal) + ((y a - c - b a : ℝ) : EReal) =
        ((y x - b x - c : ℝ) : EReal) := by
    -- Package the real identity into a single `EReal` cast.
    rw [← EReal.coe_add]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hPairing
  -- Isolate the only non-finite term `f z`, then use the casted real identity above.
  calc
    (y x : EReal) - (f z + (b x : EReal) + (c : EReal))
        = (((y x - b x - c : ℝ) : EReal)) - f z := by
            calc
              (y x : EReal) - (f z + (b x : EReal) + (c : EReal))
                  = (y x : EReal) - (f z + ((b x + c : ℝ) : EReal)) := by
                      rw [add_assoc, ← EReal.coe_add]
              _ = ((y x : EReal) - ((b x + c : ℝ) : EReal)) - f z := by
                    have hneg :
                        -(f z + ((b x + c : ℝ) : EReal)) =
                          -f z - ((b x + c : ℝ) : EReal) := by
                      rw [EReal.neg_add (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))]
                    rw [sub_eq_add_neg, hneg]
                    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
                    simp [add_assoc, add_comm]
              _ = (((y x - b x - c : ℝ) : EReal)) - f z := by
                    rw [← EReal.coe_sub]
                    congr 1
                    ring
    _ = (((A.dualMap.symm (y - b)) z : ℝ) : EReal) - f z + ((y a - c - b a : ℝ) : EReal) := by
          calc
            (((y x - b x - c : ℝ) : EReal)) - f z
                = ((((A.dualMap.symm (y - b)) z : ℝ) : EReal) +
                    ((y a - c - b a : ℝ) : EReal)) - f z := by
                      rw [hCast]
            _ = (((A.dualMap.symm (y - b)) z : ℝ) : EReal) - f z +
                  ((y a - c - b a : ℝ) : EReal) := by
                    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

-- Proof sketch: expand the conjugate by its defining supremum, make the change of variables
-- `z = A (x - a)` so that `x = A.symm z + a`, and rewrite the pairing term by the dual pullback
-- identity `A.dualMap φ x = φ (A x)`. The remaining affine constants factor out of the supremum,
-- leaving the conjugate of `f` evaluated at `A.dualMap.symm (y - b)`.
/-- Theorem 4.4: for `g(x) = f (A (x - a)) + ⟨b, x⟩ + c`, the conjugate `g*` is the conjugate of
`f` evaluated at the inverse transpose pullback `A.dualMap.symm (y - b)`, shifted by the affine
term `y a - c - b a`. This is the item's formula (4.13) in the chapter owner notation. -/
theorem conjugate_function_affine_change_of_variables
    (f : E → EReal) (A : V ≃ₗ[ℝ] E) (a : V) (b : Module.Dual ℝ V) (c : ℝ) :
    conjugate_function (fun x : V ↦ f (A (x - a)) + (b x : EReal) + (c : EReal)) =
      fun y ↦
        conjugate_function f (A.dualMap.symm (y - b)) +
          ((y a - c - b a : ℝ) : EReal) := by
  funext y
  let K : ℝ := y a - c - b a
  let core : E → EReal := fun z ↦ ((A.dualMap.symm (y - b) z : ℝ) : EReal) - f z
  -- Expand both conjugates into indexed suprema so the substitution acts on the index.
  rw [conjugate_function_apply, conjugate_function_apply, sSup_range, sSup_range]
  have hIntegrand :
      (fun x : V ↦ (y x : EReal) - (f (A (x - a)) + (b x : EReal) + (c : EReal))) =
        fun x : V ↦ core (A (x - a)) + (K : EReal) := by
    -- Normalize each integrand to the change-of-variables core plus the affine constant.
    funext x
    simpa [core, K] using affineChangeIntegrand_eq_core_addConstant f A a b y c x
  -- Transport the supremum along `x ↦ A (x - a)` and then extract the constant `K`.
  rw [hIntegrand]
  rw [affineChangeOfVariables_iSup a A (fun z ↦ core z + (K : EReal))]
  rw [iSup_addRightEReal K core]

/-- Pointwise form of Theorem 4.4. Evaluating the conjugate of
`x ↦ f (A (x - a)) + ⟨b, x⟩ + c` at `y` gives formula (4.13). -/
@[simp] theorem conjugate_function_affine_change_of_variables_apply
    (f : E → EReal) (A : V ≃ₗ[ℝ] E) (a : V) (b y : Module.Dual ℝ V) (c : ℝ) :
    conjugate_function (fun x : V ↦ f (A (x - a)) + (b x : EReal) + (c : EReal)) y =
      conjugate_function f (A.dualMap.symm (y - b)) +
        ((y a - c - b a : ℝ) : EReal) := by
  simpa using congrArg (fun g : Module.Dual ℝ V → EReal ↦ g y)
    (conjugate_function_affine_change_of_variables f A a b c)

end
