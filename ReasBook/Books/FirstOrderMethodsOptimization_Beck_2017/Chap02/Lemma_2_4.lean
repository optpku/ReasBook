/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Monotone
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Helper for Lemma 2.4: rewrite the support function as an indexed supremum over the subtype
`C`. -/
lemma support_function_eq_iSup_subtype (C : Set E) (y : Module.Dual ℝ E) :
    support_function C y = ⨆ x : C, ((y (x : E) : ℝ) : EReal) := by
  -- This is the canonical normal form for all four parts of the lemma.
  rw [support_function_apply, sSup_image']

/-- Helper for Lemma 2.4: a positive real scalar commutes with an indexed supremum in `EReal`. -/
lemma coe_pos_mul_iSup {ι : Sort*} (f : ι → EReal) {α : ℝ} (hα : 0 < α) :
    (α : EReal) * (⨆ i, f i) = ⨆ i, (α : EReal) * f i := by
  let g : EReal → EReal := fun z ↦ (α : EReal) * z
  have hα0 : (α : EReal) ≠ 0 := by
    simp [EReal.coe_eq_zero, hα.ne']
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα.le
  have hg_cont : ContinuousAt g (⨆ i, f i) := by
    -- Positive finite scalars avoid all `EReal` multiplication indeterminacies.
    have hmul_cont :
        ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) ((α : EReal), ⨆ i, f i) := by
      exact EReal.continuousAt_mul (.inl hα0) (.inl hα0) (.inl (EReal.coe_ne_bot α))
        (.inl (EReal.coe_ne_top α))
    have hpair :
        ContinuousAt (fun z : EReal ↦ ((α : EReal), z)) (⨆ i, f i) := by
      fun_prop
    simpa [g] using hmul_cont.comp hpair
  have hg_mono : Monotone g := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left hab hα_nonneg
  have hgbot : g ⊥ = ⊥ := by
    simpa [g] using EReal.coe_mul_bot_of_pos (x := α) hα
  simpa [g] using Monotone.map_iSup_of_continuousAt (g := f) hg_cont hg_mono hgbot

/-- Helper for Lemma 2.4: adding a finite left constant commutes with an indexed supremum in
`EReal`. -/
lemma ereal_const_add_iSup {ι : Sort*} {c : EReal} (hc_top : c ≠ ⊤) (hc_bot : c ≠ ⊥)
    (f : ι → EReal) :
    c + (⨆ i, f i) = ⨆ i, c + f i := by
  let g : EReal → EReal := fun z ↦ c + z
  have hg_cont : ContinuousAt g (⨆ i, f i) := by
    -- A finite constant makes addition continuous at every relevant supremum.
    have hadd_cont :
        ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (c, ⨆ i, f i) := by
      exact EReal.continuousAt_add (.inl hc_top) (.inl hc_bot)
    have hpair : ContinuousAt (fun z : EReal ↦ (c, z)) (⨆ i, f i) := by
      fun_prop
    simpa [g] using hadd_cont.comp hpair
  have hg_mono : Monotone g := by
    intro a b hab
    simpa [g] using add_le_add_right hab c
  have hgbot : g ⊥ = ⊥ := by
    simp [g]
  simpa [g] using Monotone.map_iSup_of_continuousAt (g := f) hg_cont hg_mono hgbot

/-- Helper for Lemma 2.4: adding a non-`⊥` right constant commutes with an indexed supremum whose
source supremum is not `⊥`. -/
lemma ereal_iSup_add_const {ι : Sort*} (f : ι → EReal) {c : EReal}
    (hSup_bot : (⨆ i, f i) ≠ ⊥) (hc_bot : c ≠ ⊥) :
    (⨆ i, f i) + c = ⨆ i, f i + c := by
  let g : EReal → EReal := fun z ↦ z + c
  have hg_cont : ContinuousAt g (⨆ i, f i) := by
    -- The right constant avoids the bad addition points because both summands stay above `⊥`.
    have hadd_cont :
        ContinuousAt (fun p : EReal × EReal ↦ p.2 + p.1) (c, ⨆ i, f i) := by
      simpa [add_comm] using
        (EReal.continuousAt_add (.inr hSup_bot) (.inl hc_bot) :
          ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (c, ⨆ i, f i))
    have hpair : ContinuousAt (fun z : EReal ↦ (c, z)) (⨆ i, f i) := by
      fun_prop
    simpa [g] using hadd_cont.comp hpair
  have hg_mono : Monotone g := by
    intro a b hab
    simpa [g] using add_le_add_left hab c
  have hgbot : g ⊥ = ⊥ := by
    simp [g]
  simpa [g] using Monotone.map_iSup_of_continuousAt (g := f) hg_cont hg_mono hgbot

/-- Helper for Lemma 2.4: scaling the set or scaling the dual vector gives the same support
function value. -/
lemma support_function_smul_set_eq_support_function_smul_dual
    (C : Set E) (y : Module.Dual ℝ E) (α : ℝ) :
    support_function (α • C) y = support_function C (α • y) := by
  -- Both sides are the supremum of the same image set under `x ↦ α • x`.
  rw [support_function_apply, support_function_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨w, hw, rfl⟩
    exact ⟨w, hw, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨α • w, ⟨w, hw, rfl⟩, by simp⟩

-- Proof sketch: expand `support_function`; for `α ≥ 0`, move the scalar through the dual pairing
-- and then through the supremum over the nonempty image set.
/-- Lemma 2.4 (1): (a) the support function is positively homogeneous in the dual variable:
for a nonempty set `C` and `α ≥ 0`, one has `σ_C (α y) = α σ_C (y)`. -/
theorem support_function_nonneg_smul_dual
    (C : Set E) (hC : C.Nonempty) (y : Module.Dual ℝ E) {α : ℝ} (hα : 0 ≤ α) :
    (σ_ C) (α • y) = (α : EReal) * (σ_ C) y := by
  -- Rewrite both sides into the canonical indexed-supremum normal form.
  rw [support_function_eq_iSup_subtype, support_function_eq_iSup_subtype]
  by_cases hα0 : α = 0
  · -- The zero scalar collapses both sides to `0`.
    subst hα0
    letI : Nonempty C := hC.to_subtype
    simp
  · have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    -- A positive finite scalar commutes with the indexed supremum in `EReal`.
    calc
      ⨆ x : C, ((((α • y) (x : E) : ℝ)) : EReal)
          = ⨆ x : C, (((α * y (x : E) : ℝ)) : EReal) := by
              simp
      _ = ⨆ x : C, ((α : EReal) * ((y (x : E) : ℝ) : EReal)) := by
            simp [EReal.coe_mul]
      _ = (α : EReal) * ⨆ x : C, ((y (x : E) : ℝ) : EReal) := by
            symm
            exact coe_pos_mul_iSup (f := fun x : C ↦ ((y (x : E) : ℝ) : EReal)) hα_pos

-- Proof sketch: expand `support_function`; for each `x ∈ C`, linearity gives
-- `(y₁ + y₂) x = y₁ x + y₂ x`, and taking suprema over the same set yields the usual
-- subadditivity inequality.
/-- Lemma 2.4 (2): (b) the support function is subadditive on the dual space:
for any set `C`, `σ_C (y₁ + y₂) ≤ σ_C (y₁) + σ_C (y₂)`. -/
theorem support_function_add_le
    (C : Set E) (y₁ y₂ : Module.Dual ℝ E) :
    (σ_ C) (y₁ + y₂) ≤ (σ_ C) y₁ + (σ_ C) y₂ := by
  -- Compare the common indexed supremum pointwise after linearizing evaluation.
  rw [support_function_eq_iSup_subtype, support_function_eq_iSup_subtype,
    support_function_eq_iSup_subtype]
  simpa [Pi.add_apply] using
    (EReal.iSup_add_le_add_iSup
      (u := fun x : C ↦ ((y₁ (x : E) : ℝ) : EReal))
      (v := fun x : C ↦ ((y₂ (x : E) : ℝ) : EReal)))

-- Proof sketch: rewrite `α • C` as the image of `C` under `x ↦ α • x`, expand
-- `support_function`, and use `y (α • x) = α * y x` with `α ≥ 0` to pull the scalar outside the
-- supremum.
/-- Lemma 2.4 (3): (c) scaling the set by a nonnegative scalar scales its support function by the
same scalar. -/
theorem support_function_smul_set
    (C : Set E) (hC : C.Nonempty) (y : Module.Dual ℝ E) {α : ℝ} (hα : 0 ≤ α) :
    (σ_ (α • C)) y = (α : EReal) * (σ_ C) y := by
  -- Transport set scaling to dual scaling, then reuse part (a).
  rw [support_function_smul_set_eq_support_function_smul_dual]
  exact support_function_nonneg_smul_dual C hC y hα

/-- Function-level companion to `support_function_smul_set` in textbook notation and canonical
pointwise scalar-action form for rewriting support functions of nonnegative scalar multiples of
sets. -/
theorem support_function_smul_set_eq_smul
    (C : Set E) (hC : C.Nonempty) {α : ℝ} (hα : 0 ≤ α) :
    σ_ (α • C) = (α : EReal) • σ_ C := by
  ext y
  simpa [Pi.smul_apply, smul_eq_mul] using support_function_smul_set C hC y hα

-- Proof sketch: rewrite `A + B` as the Minkowski sum of pointwise additions, expand the defining
-- supremum, use `y (a + b) = y a + y b`, and separate the supremum over pairs into the sum of the
-- two one-variable suprema over `A` and `B`.
/-- Lemma 2.4 (4): (d) the support function of a Minkowski sum equals the sum of the support
functions. -/
theorem support_function_minkowski_sum
    (A B : Set E) (y : Module.Dual ℝ E) :
    (σ_ (A + B)) y = (σ_ A) y + (σ_ B) y := by
  refine le_antisymm ?_ ?_
  · -- Every point in the Minkowski sum splits as `a + b`, giving the upper bound pointwise.
    rw [support_function_apply]
    refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, rfl⟩
    calc
      ((y (a + b) : ℝ) : EReal)
          = ((y a : ℝ) : EReal) + ((y b : ℝ) : EReal) := by simp
      _ ≤ (σ_ A) y + (σ_ B) y := by
        exact add_le_add (le_support_function_of_mem ha y) (le_support_function_of_mem hb y)
  · by_cases hA : A.Nonempty
    · by_cases hB : B.Nonempty
      · have hσA_bot : (σ_ A) y ≠ ⊥ := support_function_ne_bot A hA y
        have hσB_bot : (σ_ B) y ≠ ⊥ := support_function_ne_bot B hB y
        have hBstep :
            ∀ a : A, ((y (a : E) : ℝ) : EReal) + (σ_ B) y ≤ (σ_ (A + B)) y := by
          intro a
          -- Fix `a`, then maximize over `b ∈ B`.
          rw [support_function_eq_iSup_subtype]
          calc
            ((y (a : E) : ℝ) : EReal) + (⨆ b : B, ((y (b : E) : ℝ) : EReal))
                = ⨆ b : B, ((y (a : E) : ℝ) : EReal) + ((y (b : E) : ℝ) : EReal) := by
                    exact ereal_const_add_iSup (hc_top := EReal.coe_ne_top _)
                      (hc_bot := EReal.coe_ne_bot _)
                      (fun b : B ↦ ((y (b : E) : ℝ) : EReal))
            _ = ⨆ b : B, ((y ((a : E) + (b : E)) : ℝ) : EReal) := by
                  congr with b
                  simp
            _ ≤ (σ_ (A + B)) y := by
                  refine iSup_le ?_
                  intro b
                  exact le_support_function_of_mem
                    (Set.mem_add.mpr ⟨(a : E), a.2, (b : E), b.2, rfl⟩) y
        -- Now maximize the previous inequality over `a ∈ A`.
        rw [support_function_eq_iSup_subtype]
        calc
          (⨆ a : A, ((y (a : E) : ℝ) : EReal)) + (σ_ B) y
              = ⨆ a : A, ((y (a : E) : ℝ) : EReal) + (σ_ B) y := by
                  exact ereal_iSup_add_const
                    (f := fun a : A ↦ ((y (a : E) : ℝ) : EReal))
                    (hSup_bot := by
                      simpa [support_function_eq_iSup_subtype] using hσA_bot)
                    (hc_bot := hσB_bot)
          _ ≤ (σ_ (A + B)) y := by
                refine iSup_le ?_
                intro a
                exact hBstep a
      · -- If `B` is empty, both sides collapse to `⊥`.
        have hB_empty : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
        simp [hB_empty]
    · -- If `A` is empty, both sides collapse to `⊥`.
      have hA_empty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
      simp [hA_empty]

/-- Function-level companion to `support_function_minkowski_sum` in textbook notation for rewriting
support functions of Minkowski sums. -/
theorem support_function_minkowski_sum_eq_add (A B : Set E) :
    σ_ (A + B) = σ_ A + σ_ B := by
  ext y
  simpa using support_function_minkowski_sum A B y

end
