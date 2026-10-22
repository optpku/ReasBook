/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Data.NNReal.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

section

variable {E : Type u}

/-- Helper for Theorem 2.6: the real epigraph of a pointwise supremum is an intersection. -/
lemma realEpigraph_iSup_eq_iInter {ι : Type v} {f : ι → E → EReal} :
    {p : E × ℝ | (⨆ i : ι, f i p.1) ≤ (p.2 : EReal)} =
      ⋂ i : ι, {p : E × ℝ | f i p.1 ≤ (p.2 : EReal)} := by
  -- Normalize the supremum inequality pointwise.
  ext p
  simp [iSup_le_iff]

end

section

variable {E : Type u} {V : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup V] [Module ℝ V]

/-- Helper for Theorem 2.6: the real epigraph of `f ∘ g` is the affine preimage of the real
epigraph of `f` under the product affine map on `E × ℝ`. -/
lemma realEpigraph_precompose_affineMap_eq_preimage {f : V → EReal} (g : E →ᵃ[ℝ] V) :
    {p : E × ℝ | (f ∘ g) p.1 ≤ (p.2 : EReal)} =
      (g.prodMap (AffineMap.id ℝ ℝ)) ⁻¹' {p : V × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  -- Unfold the product affine map on coordinates.
  ext p
  simp [AffineMap.prodMap_apply]

-- Proof sketch: the real epigraph of the pullback function is the affine preimage of the real
-- epigraph of `f`, and affine preimages preserve convexity.
/-- Precomposition clause of Theorem 2.6: affine pullback preserves convexity of an
extended-real-valued function. -/
theorem is_convex_function_precompose_affineMap {f : V → EReal}
    (hf : is_convex_function f) (g : E →ᵃ[ℝ] V) :
    is_convex_function (f ∘ g) := by
  rw [is_convex_function_iff_convex_real_epigraph]
  -- Rewrite the target epigraph as an affine preimage of the original epigraph.
  rw [realEpigraph_precompose_affineMap_eq_preimage]
  exact ((is_convex_function_iff_convex_real_epigraph f).1 hf).affine_preimage
    (g.prodMap (AffineMap.id ℝ ℝ))

/-- Source-facing specialization of Theorem 2.6 (1) to affine maps written as `x ↦ A x + b`. -/
theorem is_convex_function_precompose_linearMap_add {f : V → EReal}
    (hf : is_convex_function f) (A : E →ₗ[ℝ] V) (b : V) :
    is_convex_function (fun x ↦ f (A x + b)) := by
  simpa using
    is_convex_function_precompose_affineMap hf (A.toAffineMap + AffineMap.const ℝ E b)

end

section

variable {E : Type u}
variable [AddCommMonoid E] [Module ℝ E]

-- Proof sketch: combine the epigraph inequalities for each `f i` using the nonnegativity of the
-- coefficients; equivalently, build the result by iterating the two basic closure operations of
-- nonnegative scalar multiplication and addition.
/-
LeanSearch/local API note: `ConvexOn.add` and `ConvexOn.map_sum_le` confirm that the intended
owner remains the finite weighted-sum closure statement; the needed repair is the chapter-level
codomain restriction to `(-∞, ∞]`, expressed here by explicit no-`⊥` hypotheses.
-/
/-- Theorem 2.6 (2): a finite nonnegative weighted sum of convex extended-real-valued functions is
convex, provided each summand never takes the value `⊥`. -/
theorem is_convex_function_finset_nonneg_weighted_sum {ι : Type v} (s : Finset ι)
    {f : ι → E → EReal} (hf : ∀ i ∈ s, is_convex_function (f i))
    (h_ne_bot : ∀ i ∈ s, ∀ x, f i x ≠ ⊥) (α : ι → NNReal) :
    is_convex_function (fun x ↦ ∑ i ∈ s, (((α i : ℝ) : EReal) * f i x)) := by
  -- Route correction: prove the owner by local zero/scalar/add closure lemmas, rather than
  -- routing back through the later binary wrapper that already depends on this theorem.
  have isConvexFunctionZero : is_convex_function (0 : E → EReal) := by
    -- The real epigraph of the zero function is `Set.univ ×ˢ Set.Ici 0`.
    rw [is_convex_function_iff_convex_real_epigraph]
    have hzeroEpigraph :
        {p : E × ℝ | (0 : E → EReal) p.1 ≤ (p.2 : EReal)} = Set.univ ×ˢ Set.Ici (0 : ℝ) := by
      ext p
      simp [EReal.coe_nonneg]
    rw [hzeroEpigraph]
    exact convex_univ.prod (convex_Ici (0 : ℝ))
  have isConvexFunctionNonnegSmulOfNeBot :
      ∀ {g : E → EReal}, is_convex_function g → (∀ x, g x ≠ ⊥) → ∀ a : NNReal,
        is_convex_function (fun x ↦ (((a : ℝ) : EReal) * g x)) := by
    intro g hg hg_ne_bot a
    by_cases ha : a = 0
    · -- The zero scalar branch reduces to the zero function.
      simpa [ha] using isConvexFunctionZero
    · have ha_pos_nnreal : 0 < a := pos_iff_ne_zero.mpr ha
      have ha_pos : 0 < (a : ℝ) := NNReal.coe_pos.mpr ha_pos_nnreal
      have ha_ne : (a : ℝ) ≠ 0 := by exact_mod_cast ha
      have ha_nonneg_ereal : (0 : EReal) ≤ (((a : ℝ) : EReal)) := by
        exact_mod_cast (show 0 ≤ (a : ℝ) from a.2)
      rw [is_convex_function_iff_convex_real_epigraph] at hg ⊢
      rw [convex_iff_add_mem] at hg ⊢
      intro p hp q hq t u ht hu htu
      rcases p with ⟨x, r⟩
      rcases q with ⟨y, s⟩
      simp only [Prod.smul_mk, Prod.mk_add_mk, Set.mem_setOf_eq] at hp hq ⊢
      have ha_pos_ereal : (0 : EReal) < (((a : ℝ) : EReal)) := by
        exact_mod_cast ha_pos
      have hx_top : g x ≠ ⊤ := by
        intro hx_top
        have hpTop : (⊤ : EReal) ≤ (r : EReal) := by
          have hp' := hp
          simp [hx_top, EReal.mul_top_of_pos ha_pos_ereal] at hp'
        exact (not_le_of_gt (EReal.coe_lt_top r)) hpTop
      have hy_top : g y ≠ ⊤ := by
        intro hy_top
        have hqTop : (⊤ : EReal) ≤ (s : EReal) := by
          have hq' := hq
          simp [hy_top, EReal.mul_top_of_pos ha_pos_ereal] at hq'
        exact (not_le_of_gt (EReal.coe_lt_top s)) hqTop
      have hx_mul_ne_bot : (((a : ℝ) : EReal) * g x) ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        constructor
        · exact Or.inl (by simp)
        constructor
        · exact Or.inr (hg_ne_bot x)
        constructor
        · exact Or.inl (by simp)
        · exact Or.inl ha_nonneg_ereal
      have hy_mul_ne_bot : (((a : ℝ) : EReal) * g y) ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        constructor
        · exact Or.inl (by simp)
        constructor
        · exact Or.inr (hg_ne_bot y)
        constructor
        · exact Or.inl (by simp)
        · exact Or.inl ha_nonneg_ereal
      have hx_real : (a : ℝ) * (g x).toReal ≤ r := by
        have hx_toReal := EReal.toReal_le_toReal hp hx_mul_ne_bot (by simp)
        simpa [EReal.toReal_mul, EReal.toReal_coe] using hx_toReal
      have hy_real : (a : ℝ) * (g y).toReal ≤ s := by
        have hy_toReal := EReal.toReal_le_toReal hq hy_mul_ne_bot (by simp)
        simpa [EReal.toReal_mul, EReal.toReal_coe] using hy_toReal
      have hx_mem : (x, (g x).toReal) ∈ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} := by
        simpa using EReal.le_coe_toReal hx_top
      have hy_mem : (y, (g y).toReal) ∈ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} := by
        simpa using EReal.le_coe_toReal hy_top
      have hcombo := hg hx_mem hy_mem ht hu htu
      let z : E := t • x + u • y
      have hz_top : g z ≠ ⊤ := by
        exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (by simpa [z] using hcombo)
      have hcombo_real :
          (g z).toReal ≤ t * (g x).toReal + u * (g y).toReal := by
        exact EReal.toReal_le_toReal
          (by simpa [z] using hcombo) (hg_ne_bot z) (EReal.coe_ne_top _)
      have hdiv_real :
          t * (g x).toReal + u * (g y).toReal ≤ t * (r / (a : ℝ)) + u * (s / (a : ℝ)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (by
              have : (g x).toReal * (a : ℝ) ≤ r := by simpa [mul_comm] using hx_real
              simpa [mul_comm] using (le_div_iff₀ ha_pos).mpr this)
            ht)
          (mul_le_mul_of_nonneg_left
            (by
              have : (g y).toReal * (a : ℝ) ≤ s := by simpa [mul_comm] using hy_real
              simpa [mul_comm] using (le_div_iff₀ ha_pos).mpr this)
            hu)
      have hscaled_real :
          (a : ℝ) * (g z).toReal ≤
            (a : ℝ) * (t * (r / (a : ℝ)) + u * (s / (a : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (le_trans hcombo_real hdiv_real) (show 0 ≤ (a : ℝ) by exact a.2)
      have hz_coe : g z = (((g z).toReal : ℝ) : EReal) := by
        exact (EReal.coe_toReal hz_top (hg_ne_bot z)).symm
      calc
        (((a : ℝ) : EReal) * g z)
            = (((a : ℝ) : EReal) * ((((g z).toReal : ℝ)) : EReal)) := by
              exact congrArg (fun w : EReal => (((a : ℝ) : EReal) * w)) hz_coe
        _ = ((((a : ℝ) * (g z).toReal : ℝ)) : EReal) := by
          rw [← EReal.coe_mul]
        _ ≤ (((((a : ℝ) * (t * (r / (a : ℝ)) + u * (s / (a : ℝ)))) : ℝ)) : EReal) := by
          exact_mod_cast hscaled_real
        _ = ((t * r + u * s : ℝ) : EReal) := by
          congr 1
          field_simp [ha_ne]
  have isConvexFunctionAddOfNeBot :
      ∀ {g h : E → EReal}, is_convex_function g → is_convex_function h →
        (∀ x, g x ≠ ⊥) → (∀ x, h x ≠ ⊥) → is_convex_function (fun x ↦ g x + h x) := by
    intro g h hg hh hg_ne_bot hh_ne_bot
    rw [is_convex_function_iff_convex_real_epigraph] at hg hh ⊢
    rw [convex_iff_add_mem] at hg hh ⊢
    intro p hp q hq a b ha hb hab
    rcases p with ⟨x, r⟩
    rcases q with ⟨y, s⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, Set.mem_setOf_eq] at hp hq ⊢
    have hxg_top : g x ≠ ⊤ := by
      intro hxg_top
      have hpTop : (⊤ : EReal) ≤ (r : EReal) := by
        have hp' := hp
        simp [hxg_top, EReal.top_add_of_ne_bot (hh_ne_bot x)] at hp'
      exact (not_le_of_gt (EReal.coe_lt_top r)) hpTop
    have hxh_top : h x ≠ ⊤ := by
      intro hxh_top
      have hpTop : (⊤ : EReal) ≤ (r : EReal) := by
        have hp' := hp
        simp [hxh_top, EReal.add_top_of_ne_bot (hg_ne_bot x)] at hp'
      exact (not_le_of_gt (EReal.coe_lt_top r)) hpTop
    have hyg_top : g y ≠ ⊤ := by
      intro hyg_top
      have hqTop : (⊤ : EReal) ≤ (s : EReal) := by
        have hq' := hq
        simp [hyg_top, EReal.top_add_of_ne_bot (hh_ne_bot y)] at hq'
      exact (not_le_of_gt (EReal.coe_lt_top s)) hqTop
    have hyh_top : h y ≠ ⊤ := by
      intro hyh_top
      have hqTop : (⊤ : EReal) ≤ (s : EReal) := by
        have hq' := hq
        simp [hyh_top, EReal.add_top_of_ne_bot (hg_ne_bot y)] at hq'
      exact (not_le_of_gt (EReal.coe_lt_top s)) hqTop
    have hx_real : (g x).toReal + (h x).toReal ≤ r := by
      have hx_toReal := EReal.toReal_le_toReal hp
        (EReal.add_ne_bot_iff.mpr ⟨hg_ne_bot x, hh_ne_bot x⟩) (by simp)
      simpa [EReal.toReal_add hxg_top (hg_ne_bot x) hxh_top (hh_ne_bot x)] using hx_toReal
    have hy_real : (g y).toReal + (h y).toReal ≤ s := by
      have hy_toReal := EReal.toReal_le_toReal hq
        (EReal.add_ne_bot_iff.mpr ⟨hg_ne_bot y, hh_ne_bot y⟩) (by simp)
      simpa [EReal.toReal_add hyg_top (hg_ne_bot y) hyh_top (hh_ne_bot y)] using hy_toReal
    have hxg_mem : (x, (g x).toReal) ∈ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} := by
      simpa using EReal.le_coe_toReal hxg_top
    have hxh_mem : (x, (h x).toReal) ∈ {p : E × ℝ | h p.1 ≤ (p.2 : EReal)} := by
      simpa using EReal.le_coe_toReal hxh_top
    have hyg_mem : (y, (g y).toReal) ∈ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} := by
      simpa using EReal.le_coe_toReal hyg_top
    have hyh_mem : (y, (h y).toReal) ∈ {p : E × ℝ | h p.1 ≤ (p.2 : EReal)} := by
      simpa using EReal.le_coe_toReal hyh_top
    have hcombo_g := hg hxg_mem hyg_mem ha hb hab
    have hcombo_h := hh hxh_mem hyh_mem ha hb hab
    calc
      g (a • x + b • y) + h (a • x + b • y)
          ≤ ((((a * (g x).toReal + b * (g y).toReal) : ℝ)) : EReal)
            + ((((a * (h x).toReal + b * (h y).toReal) : ℝ)) : EReal) := by
            exact add_le_add hcombo_g hcombo_h
      _ = (((a * (g x).toReal + b * (g y).toReal)
            + (a * (h x).toReal + b * (h y).toReal) : ℝ) : EReal) := by
        rw [← EReal.coe_add]
      _ = (((a * ((g x).toReal + (h x).toReal)
            + b * ((g y).toReal + (h y).toReal) : ℝ)) : EReal) := by
        congr 1
        ring
      _ ≤ ((a * r + b * s : ℝ) : EReal) := by
        exact_mod_cast add_le_add
          (mul_le_mul_of_nonneg_left hx_real ha)
          (mul_le_mul_of_nonneg_left hy_real hb)
  have weightedSumConvexAndNeBot :
      ∀ t : Finset ι,
        (∀ i ∈ t, is_convex_function (f i)) →
        (∀ i ∈ t, ∀ x, f i x ≠ ⊥) →
        is_convex_function (fun x ↦ ∑ i ∈ t, (((α i : ℝ) : EReal) * f i x))
          ∧ ∀ x, (∑ i ∈ t, (((α i : ℝ) : EReal) * f i x)) ≠ ⊥ := by
    classical
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _ _
      -- The empty weighted sum is the zero function and never equals `⊥`.
      constructor
      · simpa using isConvexFunctionZero
      · intro x
        simp
    · intro i t hi ih ht_convex ht_ne_bot
      have htail := ih
        (fun j hj ↦ ht_convex j (Finset.mem_insert_of_mem hj))
        (fun j hj x ↦ ht_ne_bot j (Finset.mem_insert_of_mem hj) x)
      have hhead_convex :
          is_convex_function (fun x ↦ (((α i : ℝ) : EReal) * f i x)) := by
        -- The head summand is a nonnegative scalar multiple of a convex function.
        exact isConvexFunctionNonnegSmulOfNeBot (ht_convex i (Finset.mem_insert_self i t))
          (ht_ne_bot i (Finset.mem_insert_self i t)) (α i)
      have hhead_ne_bot :
          ∀ x, (((α i : ℝ) : EReal) * f i x) ≠ ⊥ := by
        intro x
        by_cases hα : α i = 0
        · simp [hα]
        · have hα_pos : 0 < (α i : ℝ) := NNReal.coe_pos.mpr <| pos_iff_ne_zero.mpr hα
          intro hbot
          have : f i x = ⊥ := by
            by_contra hfi
            have hmul_ne_bot : (((α i : ℝ) : EReal) * f i x) ≠ ⊥ := by
              rw [EReal.mul_ne_bot]
              constructor
              · exact Or.inl (by simp)
              constructor
              · exact Or.inr hfi
              constructor
              · exact Or.inl (by simp)
              · exact Or.inl (by exact_mod_cast (show 0 ≤ (α i : ℝ) from (α i).2))
            exact hmul_ne_bot hbot
          exact (ht_ne_bot i (Finset.mem_insert_self i t) x) this
      refine ⟨?_, ?_⟩
      · -- Combine the head summand and the tail sum using the local binary-add closure.
        simpa [Finset.sum_insert hi, Pi.add_apply] using
          isConvexFunctionAddOfNeBot hhead_convex htail.1 hhead_ne_bot htail.2
      · intro x
        have hsum_ne_bot :
            (((α i : ℝ) : EReal) * f i x) + ∑ j ∈ t, (((α j : ℝ) : EReal) * f j x) ≠ ⊥ :=
          (EReal.add_ne_bot_iff.mpr ⟨hhead_ne_bot x, htail.2 x⟩)
        simpa [Finset.sum_insert hi] using hsum_ne_bot
  exact (weightedSumConvexAndNeBot s hf h_ne_bot).1

/-- Bridge/view specialization of Theorem 2.6 (2) from a `Finset`-indexed weighted sum to the
`Fintype` sum over `Finset.univ`. -/
theorem is_convex_function_fintype_nonneg_weighted_sum {ι : Type v} [Fintype ι]
    {f : ι → E → EReal} (hf : ∀ i : ι, is_convex_function (f i))
    (h_ne_bot : ∀ i : ι, ∀ x, f i x ≠ ⊥) (α : ι → NNReal) :
    is_convex_function (fun x ↦ ∑ i : ι, (((α i : ℝ) : EReal) * f i x)) := by
  simpa using
    is_convex_function_finset_nonneg_weighted_sum Finset.univ
      (fun i _ ↦ hf i) (fun i _ x ↦ h_ne_bot i x) α

/-- Companion specialization of Theorem 2.6 (2): the pointwise sum of two convex
extended-real-valued functions is convex when neither summand ever takes the value `⊥`. -/
theorem is_convex_function_pointwise_add {f g : E → EReal}
    (hf : is_convex_function f) (hg : is_convex_function g)
    (hf_ne_bot : ∀ x, f x ≠ ⊥) (hg_ne_bot : ∀ x, g x ≠ ⊥) :
    is_convex_function (f + g) := by
  let F : Fin 2 → E → EReal := fun i ↦ if i = 0 then f else g
  have hF : ∀ i : Fin 2, is_convex_function (F i) := by
    intro i
    fin_cases i
    · simpa [F] using hf
    · simpa [F] using hg
  have hF_ne_bot : ∀ i : Fin 2, ∀ x, F i x ≠ ⊥ := by
    intro i x
    fin_cases i
    · simpa [F] using hf_ne_bot x
    · simpa [F] using hg_ne_bot x
  simpa [F, Fin.sum_univ_two, Pi.add_apply] using
    is_convex_function_finset_nonneg_weighted_sum Finset.univ
      (fun i _ ↦ hF i) (fun i _ x ↦ hF_ne_bot i x) (fun _ ↦ 1)

-- Proof sketch: the epigraph of the pointwise supremum is the intersection of the epigraphs of the
-- family members, and intersections of convex sets remain convex.
/-- Pointwise-supremum clause of Theorem 2.6: the pointwise maximum over the
index set, of convex extended-real-valued functions is convex. -/
theorem is_convex_function_iSup {ι : Type v} {f : ι → E → EReal}
    (hf : ∀ i : ι, is_convex_function (f i)) :
    is_convex_function (fun x ↦ ⨆ i : ι, f i x) := by
  rw [is_convex_function_iff_convex_real_epigraph]
  -- Normalize the target epigraph to an intersection of known convex epigraphs.
  rw [realEpigraph_iSup_eq_iInter]
  exact convex_iInter fun i ↦ (is_convex_function_iff_convex_real_epigraph (f i)).1 (hf i)

end
