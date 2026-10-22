/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open InnerProductSpace (toDualMap)
open scoped Pointwise RealInnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 6.46 is `source-facing`: the textbook statement computes the proximal operator of the
support function of a nonempty closed convex set. Domain sampling here points to the existing
`core/canonical` owners `support_function`, `σ[C]`, `prox[...]`, and Proposition 3.12's
complete-subset bridge `metricProjectionOfComplete`. The relevant supporting declarations are
Chapter 2's primal-space bridge `support_function_primal`, Proposition 3.12's projection
variational inequality `inner_sub_metricProjectionOfComplete_le_zero`,
Theorem 6.25's singleton bridge
`projection_mapping_eq_singleton_of_nonempty_closed_convex`, and Proposition 6.2.2's linear
proximal formula `prox_inner_eq_singleton_sub`. The primitive data are only the set `C` and its
nonempty/complete/convex hypotheses; the right-hand point `P_C (x / λ)` is derived from the owner
`metricProjectionOfComplete`, and the support-function term is the source-facing primal owner
`σ[C]`. The closed-subset-in-a-complete-space formulation is a downstream `bridge/view`
specialization obtained from `metricProjection`. -/

variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_complete : IsComplete C)
    (hC_convex : Convex ℝ C)

-- Proof sketch: let `p = metricProjection C (x / λ)` and `u = x - λ • p`.
-- Proposition 3.12 gives the projection
-- variational inequality `⟪u, w - p⟫ ≤ 0` for every `w ∈ C`, so `p` realizes the support
-- function at `u`. This identifies the proximal objective of `λ σ_C` at `u` with the proximal
-- objective of the linear functional `y ↦ ⟪y, λ • p⟫`, whose proximal map is the singleton `{u}`
-- by Proposition 6.2.2. The same linear lower bound then forces every minimizer of `λ σ_C` to
-- equal `u`.
/-- Theorem 6.46: prox of support functions. If `C` is a nonempty complete convex subset of a
real inner product space and `lam : PosReal` encodes a positive scalar `λ`, then the
proximal set of the scaled support function `λ σ_C` at `x` is the singleton containing
`x - λ P_C(x / λ)`, written in Lean using the canonical owners `σ[C]` and
`metricProjectionOfComplete`. The familiar
closed-subset-in-a-complete-space statement is the direct specialization obtained from
`metricProjection`. This is the chapter's set-valued rendering of the textbook identity
`prox_{λ σ_C}(x) = x - λ P_C(x / λ)`. -/
theorem prox_support_function_eq_singleton_sub_smul_metricProjection
    (lam : PosReal) (x : E) :
    prox[(((lam : ℝ) : EReal) • σ[C])] x =
      {x - (lam : ℝ) •
        (metricProjectionOfComplete C hC_nonempty hC_complete hC_convex
          ((lam : ℝ)⁻¹ • x) : E)} := by
  let σC : E → EReal := σ[C]
  let P : E → C := metricProjectionOfComplete C hC_nonempty hC_complete hC_convex
  let z : E := (lam : ℝ)⁻¹ • x
  let pC : C := P z
  let p : E := pC
  let u : E := x - (lam : ℝ) • p
  let g : E → EReal := fun y ↦ ((⟪y, (lam : ℝ) • p⟫ : ℝ) : EReal)
  change prox[(((lam : ℝ) : EReal) • σC)] x =
    {u}
  have hp_mem : p ∈ C := by
    simp [p, pC]
  have hu_eq : u = (lam : ℝ) • (z - p) := by
    dsimp [u, z]
    rw [smul_sub]
    congr 1
    have hlam_ne : (lam : ℝ) ≠ 0 := (show 0 < (lam : ℝ) from lam.2).ne'
    symm
    rw [smul_smul, mul_inv_cancel₀ hlam_ne, one_smul]
  have hu_inner_nonpos : ∀ w ∈ C, inner ℝ u (w - p) ≤ 0 := by
    intro w hw
    have hproj : inner ℝ (z - p) (w - p) ≤ 0 := by
      simpa [p, pC, z] using
        inner_sub_metricProjectionOfComplete_le_zero
          C hC_nonempty hC_complete hC_convex z w hw
    rw [hu_eq, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos lam.2.le hproj
  have hσ_lower (y : E) : ((⟪y, p⟫ : ℝ) : EReal) ≤ σC y := by
    rw [show σC y = σ[C] y by rfl, support_function_primal_apply, support_function_apply]
    exact le_sSup ⟨p, hp_mem, by simp⟩
  have hg_le (y : E) : g y ≤ (((lam : ℝ) : EReal) • σC) y := by
    have hscaled :=
      mul_le_mul_of_nonneg_left
        (hσ_lower y)
        (show 0 ≤ ((lam : ℝ) : EReal) by exact_mod_cast lam.2.le)
    simpa [g, Pi.smul_apply, real_inner_smul_right, EReal.coe_mul, mul_comm, mul_left_comm,
      mul_assoc] using hscaled
  have hσ_eq : σC u = ((⟪u, p⟫ : ℝ) : EReal) := by
    change σ[C] u = ((⟪u, p⟫ : ℝ) : EReal)
    rw [support_function_primal_apply]
    apply support_function_eq_of_isGreatest_image
    refine ⟨?_, ?_⟩
    · exact ⟨p, hp_mem, by simp⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hwp : inner ℝ u w ≤ inner ℝ u p := by
        have h := hu_inner_nonpos w hw
        rw [inner_sub_right] at h
        linarith
      have hwp' : ((toDualMap ℝ E u) w : ℝ) ≤ ⟪u, p⟫ := by
        simpa using hwp
      have hwp'' : (((toDualMap ℝ E u) w : ℝ) : EReal) ≤ (((⟪u, p⟫ : ℝ) : EReal)) := by
        exact_mod_cast hwp'
      simpa using hwp''
  have hprox_g : prox[g] x = {u} := by
    simpa [g, u, real_inner_comm] using prox_inner_eq_singleton_sub ((lam : ℝ) • p) x
  have hu_mem_g : u ∈ prox[g] x := by
    rw [hprox_g]
    simp
  have hu_min_g : ∀ y, proximal_objective g x u ≤ proximal_objective g x y := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu_mem_g
    exact hu_mem_g
  have hobj_eq_u :
      proximal_objective (((lam : ℝ) : EReal) • σC) x u = proximal_objective g x u := by
    simp [proximal_objective_apply, Pi.smul_apply, g, hσ_eq, real_inner_smul_right, EReal.coe_mul]
  have hobj_g_le (y : E) :
      proximal_objective g x y ≤ proximal_objective (((lam : ℝ) : EReal) • σC) x y := by
    rw [proximal_objective_apply, proximal_objective_apply]
    exact add_le_add (hg_le y) le_rfl
  have hu_mem :
      u ∈ prox[(((lam : ℝ) : EReal) • σC)] x := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro y
    calc
      proximal_objective (((lam : ℝ) : EReal) • σC) x u = proximal_objective g x u := hobj_eq_u
      _ ≤ proximal_objective g x y := hu_min_g y
      _ ≤ proximal_objective (((lam : ℝ) : EReal) • σC) x y := hobj_g_le y
  have hu_min : ∀ y,
      proximal_objective (((lam : ℝ) : EReal) • σC) x u ≤
        proximal_objective (((lam : ℝ) : EReal) • σC) x y := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu_mem
    exact hu_mem
  ext y
  constructor
  · intro hy
    have hy_min : ∀ v,
        proximal_objective (((lam : ℝ) : EReal) • σC) x y ≤
          proximal_objective (((lam : ℝ) : EReal) • σC) x v := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
      exact hy
    have hy_eq_u :
        proximal_objective (((lam : ℝ) : EReal) • σC) x y =
          proximal_objective (((lam : ℝ) : EReal) • σC) x u :=
      le_antisymm (hy_min u) (hu_min y)
    have hy_eq_g :
        proximal_objective g x y =
          proximal_objective (((lam : ℝ) : EReal) • σC) x y := by
      apply le_antisymm
      · exact hobj_g_le y
      · calc
          proximal_objective (((lam : ℝ) : EReal) • σC) x y =
              proximal_objective (((lam : ℝ) : EReal) • σC) x u := hy_eq_u
          _ = proximal_objective g x u := hobj_eq_u
          _ ≤ proximal_objective g x y := hu_min_g y
    have hy_mem_g : y ∈ prox[g] x := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
      intro v
      calc
        proximal_objective g x y =
            proximal_objective (((lam : ℝ) : EReal) • σC) x y := hy_eq_g
        _ = proximal_objective (((lam : ℝ) : EReal) • σC) x u := hy_eq_u
        _ = proximal_objective g x u := hobj_eq_u
        _ ≤ proximal_objective g x v := hu_min_g v
    rw [hprox_g] at hy_mem_g
    simpa using hy_mem_g
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hu_mem

end
