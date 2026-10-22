/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped BigOperators

section

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, NormedSpace ℝ (Ei i)]

variable {f : ((i : Fin p) → Ei i) → ℝ}
variable {g : (i : Fin p) → Ei i → EReal}

local notation "F" => composite_model_objective f.toEReal (separableSum g)

/-- Helper for Chapter 14 composite-domain API: coercing a finite real sum into `EReal` agrees
with summing the coerced terms. -/
private lemma ereal_coe_finset_sum_aux {α : Type*} (s : Finset α) (a : α → ℝ) :
    (((Finset.sum s a : ℝ)) : EReal) = Finset.sum s (fun i ↦ ((a i : ℝ) : EReal)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, ih, EReal.coe_add]

omit [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)] in
-- Proof sketch: the real-valued smooth term `f.toEReal` is finite everywhere, so adding it does
-- not change where the composite objective avoids `⊤`.
/-- Helper for Chapter 14 composite-domain API: the effective domain of
`f.toEReal + separableSum g` is exactly the effective domain of `separableSum g`. -/
lemma composite_objective_effective_domain_iff_separableSum
    {z : (i : Fin p) → Ei i} :
    z ∈ effective_domain F ↔ z ∈ effective_domain (separableSum g) := by
  have hf_ne_bot : f.toEReal z ≠ ⊥ := by
    simp [Function.toEReal]
  have hf_ne_top : f.toEReal z ≠ ⊤ := by
    simp [Function.toEReal]
  -- Finite addition on the left preserves exactly the non-`⊤` points of the separable term.
  simpa [effective_domain, composite_model_objective, lt_top_iff_ne_top] using
    (EReal.add_ne_top_iff_ne_top_right (x := f.toEReal z) (y := separableSum g z)
      hf_ne_bot hf_ne_top)

-- Proof sketch: every block penalty avoids `⊥` by properness, and `f.toEReal` also avoids `⊥`,
-- so their sum never attains `⊥`.
/-- Helper for Chapter 14 composite-domain API: the composite objective
`f.toEReal + separableSum g` never takes the value `-∞`. -/
lemma composite_objective_ne_bot
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (z : (i : Fin p) → Ei i) :
    F z ≠ ⊥ := by
  have hseparable_ne_bot : separableSum g z ≠ ⊥ := by
    simpa [separableSum_apply] using
      ereal_sum_ne_bot Finset.univ (fun i ↦ g i (z i))
        (fun i _ ↦ (hmodel.g_proper i).ne_bot (z i))
  -- The composite value avoids `⊥` once both summands do.
  rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
  exact ⟨by simp [Function.toEReal], hseparable_ne_bot⟩

-- Proof sketch: if one block value were `⊤`, then the whole separable sum would be `⊤`,
-- contradicting finiteness of the composite objective.
/-- Helper for Chapter 14 composite-domain API: finiteness of the composite objective at `x`
forces each block value `g_i(x_i)` to be finite. -/
lemma composite_block_mem_effective_domain_of_mem
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {x : (i : Fin p) → Ei i}
    (hx : x ∈ effective_domain F) (i : Fin p) :
    x i ∈ effective_domain (g i) := by
  have hx_separable :
      x ∈ effective_domain (separableSum g) :=
    composite_objective_effective_domain_iff_separableSum.mp hx
  -- A single `⊤` block would force the separable sum to be `⊤`.
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  intro hgi_top
  have hrest_ne_bot :
      (∑ j ∈ Finset.univ.erase i, g j (x j)) ≠ ⊥ := by
    exact ereal_sum_ne_bot (Finset.univ.erase i) (fun j ↦ g j (x j))
      (fun j _ ↦ (hmodel.g_proper j).ne_bot (x j))
  have hseparable_top : separableSum g x = ⊤ := by
    rw [separableSum_apply]
    calc
      ∑ j, g j (x j) = g i (x i) + ∑ j ∈ Finset.univ.erase i, g j (x j) := by
        symm
        exact Finset.add_sum_erase Finset.univ (fun j ↦ g j (x j)) (Finset.mem_univ i)
      _ = ⊤ := by
        rw [hgi_top, EReal.top_add_of_ne_bot hrest_ne_bot]
  exact (lt_top_iff_ne_top.mp (mem_effective_domain.mp hx_separable)) hseparable_top

-- Proof sketch: after changing one block to another finite `g_i`-value, all block penalties are
-- still finite, so the separable sum is a real coercion and the composite point stays feasible.
/-- Helper for Chapter 14 composite-domain API: replacing one block by another point of
`effective_domain (g i)` preserves membership in the effective domain of
`f.toEReal + separableSum g`. -/
lemma composite_update_mem_effective_domain_of_block_mem
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {x : (i : Fin p) → Ei i} (i : Fin p) {yi : Ei i}
    (hx : x ∈ effective_domain F) (hyi : yi ∈ effective_domain (g i)) :
    Function.update x i yi ∈ effective_domain F := by
  let y : (i : Fin p) → Ei i := Function.update x i yi
  have hy_block :
      ∀ j : Fin p, y j ∈ effective_domain (g j) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [y]
    · simpa [y, Function.update, hji] using
        composite_block_mem_effective_domain_of_mem hmodel hx j
  have hy_separable :
      y ∈ effective_domain (separableSum g) := by
    have hfinite :
        ∀ j : Fin p, g j (y j) = ((((g j (y j)).toReal : ℝ)) : EReal) := by
      intro j
      exact
        (EReal.coe_toReal (mem_effective_domain.mp (hy_block j)).ne
          ((hmodel.g_proper j).ne_bot (y j))).symm
    have hy_sum :
        separableSum g y = (((∑ j : Fin p, (g j (y j)).toReal) : ℝ) : EReal) := by
      rw [separableSum_apply]
      calc
        ∑ j : Fin p, g j (y j) = ∑ j : Fin p, ((((g j (y j)).toReal : ℝ)) : EReal) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hfinite j
        _ = (((∑ j : Fin p, (g j (y j)).toReal) : ℝ) : EReal) := by
          simpa using
            (ereal_coe_finset_sum_aux (s := Finset.univ)
              (a := fun j : Fin p ↦ (g j (y j)).toReal)).symm
    refine mem_effective_domain.mpr ?_
    rw [hy_sum]
    simp
  exact composite_objective_effective_domain_iff_separableSum.2 hy_separable

end
