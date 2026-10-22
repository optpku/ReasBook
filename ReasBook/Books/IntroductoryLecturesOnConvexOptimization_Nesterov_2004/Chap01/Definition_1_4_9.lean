/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 1.4.9 is source-facing: it names the unit tangent directions to a level set.

Primary domain:
- tangent-cone geometry for level sets in real normed spaces.

Relevant owner-style declarations sampled before refinement:
- `posTangentConeAt`
- `mem_tangentConeAt_of_seq`
- `mem_tangentConeAt_iff_exists_seq`
- `mem_sphere_zero_iff_norm`

Owner abstraction:
- `posTangentConeAt`

Primitive data:
- the function `f`
- the base point `xbar`

Derived API:
- the tangent directions as the unit-sphere part of the owner cone to the level set
- the normalized-secant characterization of membership

This file therefore keeps the source-facing name, but expresses it directly through the owner cone
and the canonical unit sphere instead of a bespoke set-builder wrapper.

Source/core/bridge triage:
- source-facing: the unit tangent directions to the level set of `f` through `xbar`
- core/canonical: `posTangentConeAt (f ⁻¹' {f xbar}) xbar`
- bridge/view: the normalized-secant sequence characterization of membership
-/

/-- Definition 1.4.9: the directions tangent to the level set of `f` through `xbar` are the unit
vectors in the positive tangent cone of the level set `f ⁻¹' {f xbar}` at `xbar`. The direct
membership lemma `mem_tangentDirectionsToLevelSet_iff` records this owner-level decomposition, and
the companion theorem `mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit` records
the textbook normalized-secant characterization. -/
def tangentDirectionsToLevelSet (f : E → ℝ) (xbar : E) : Set E :=
  posTangentConeAt (f ⁻¹' {f xbar}) xbar ∩ Metric.sphere (0 : E) 1

/-- Membership in `tangentDirectionsToLevelSet f xbar` means lying in the positive tangent cone to
the level set through `xbar` and having unit norm. -/
@[simp] theorem mem_tangentDirectionsToLevelSet_iff {f : E → ℝ} {xbar s : E} :
    s ∈ tangentDirectionsToLevelSet f xbar ↔
      s ∈ posTangentConeAt (f ⁻¹' {f xbar}) xbar ∧ ‖s‖ = 1 := by
  simp [tangentDirectionsToLevelSet]

/-- Membership in `tangentDirectionsToLevelSet f xbar` is equivalent to admitting a sequence on
the level set through `xbar` whose normalized secants converge to the given direction. -/
-- Proof sketch: a unit vector belongs to the positive tangent cone of the level set iff it is the
-- limit of normalized secants along a sequence in that level set converging to `xbar`.
theorem mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit
    {f : E → ℝ} {xbar s : E} :
    s ∈ tangentDirectionsToLevelSet f xbar ↔
      ∃ y : ℕ → E,
        Tendsto y atTop (𝓝 xbar) ∧
        (∀ k : ℕ, y k ≠ xbar) ∧
        (∀ k : ℕ, y k ∈ f ⁻¹' {f xbar}) ∧
        Tendsto (fun k ↦ ‖y k - xbar‖⁻¹ • (y k - xbar)) atTop (𝓝 s) := by
  rw [mem_tangentDirectionsToLevelSet_iff]
  constructor
  · rintro ⟨hs, hnorm⟩
    have hs_ne : s ≠ 0 := norm_ne_zero_iff.mp (hnorm.symm ▸ one_ne_zero)
    rcases mem_tangentConeAt_iff_exists_seq.mp hs with ⟨c, d, hd₀, hlevel, hcd⟩
    have hcd_ne : ∀ᶠ n in atTop, c n • d n ≠ 0 := hcd.eventually_ne hs_ne
    obtain ⟨N, hN⟩ :
        ∃ N, ∀ n : ℕ,
          xbar + d (n + N) ∈ f ⁻¹' {f xbar} ∧ c (n + N) • d (n + N) ≠ 0 := by
      obtain ⟨N, hN⟩ := (hlevel.and hcd_ne).exists_forall_of_atTop
      exact ⟨N, fun n ↦ hN (n + N) (Nat.le_add_left N n)⟩
    refine ⟨fun n ↦ xbar + d (n + N), ?_, ?_, ?_, ?_⟩
    · have hd₀' : Tendsto (fun n ↦ d (n + N)) atTop (𝓝 (0 : E)) := by
        simpa [Function.comp] using hd₀.comp (tendsto_add_atTop_nat N)
      simpa [Function.comp] using tendsto_const_nhds.add hd₀'
    · intro n hEq
      have hd_ne : d (n + N) ≠ 0 := right_ne_zero_of_smul (hN n).2
      exact hd_ne (by simpa using congrArg (fun z ↦ z - xbar) hEq)
    · intro n
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (hN n).1
    · have hcd' : Tendsto (fun n ↦ c (n + N) • d (n + N)) atTop (𝓝 s) := by
        simpa [Function.comp] using hcd.comp (tendsto_add_atTop_nat N)
      have hnormalize :
          ContinuousAt (fun z : E ↦ ‖z‖⁻¹ • z) s :=
        (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hs_ne)).smul continuousAt_id
      have hnormalized :
          Tendsto (fun n ↦ ‖c (n + N) • d (n + N)‖⁻¹ • (c (n + N) • d (n + N))) atTop (𝓝 s) := by
        simpa [hnorm] using hnormalize.tendsto.comp hcd'
      have hnormalized_eq :
          (fun n ↦ ‖c (n + N) • d (n + N)‖⁻¹ • (c (n + N) • d (n + N))) =ᶠ[atTop]
            fun n ↦ ‖d (n + N)‖⁻¹ • d (n + N) := by
        exact Eventually.of_forall fun n ↦ by
          set cn : NNReal := c (n + N)
          set dn : E := d (n + N)
          have hprod_ne : cn • dn ≠ 0 := by
            simpa [cn, dn] using (hN n).2
          have hc_ne : (cn : ℝ) ≠ 0 := by
            intro hc
            have hc0 : cn = 0 := NNReal.coe_eq_zero.mp hc
            exact hprod_ne (by simp [hc0])
          have hd_ne : dn ≠ 0 := right_ne_zero_of_smul hprod_ne
          have hnorm_d_ne : ‖dn‖ ≠ 0 := norm_ne_zero_iff.mpr hd_ne
          have hnorm_cn : ‖(cn : ℝ)‖ = (cn : ℝ) := by
            rw [Real.norm_eq_abs]
            exact abs_of_nonneg cn.2
          simpa [cn, dn] using
            (show ‖cn • dn‖⁻¹ • (cn • dn) = ‖dn‖⁻¹ • dn from by
              change ‖((cn : ℝ) • dn)‖⁻¹ • (((cn : ℝ) • dn)) = ‖dn‖⁻¹ • dn
              rw [norm_smul, smul_smul, hnorm_cn]
              congr 1
              field_simp [hc_ne, hnorm_d_ne, mul_comm, mul_left_comm, mul_assoc])
      have hsecant :
          Tendsto (fun n ↦ ‖d (n + N)‖⁻¹ • d (n + N)) atTop (𝓝 s) :=
        Tendsto.congr' hnormalized_eq hnormalized
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsecant
  · rintro ⟨y, hy, hy_ne, hy_level, hy_secant⟩
    refine ⟨?_, ?_⟩
    · change s ∈ tangentConeAt NNReal (f ⁻¹' {f xbar}) xbar
      have hy_sub : Tendsto (fun k ↦ y k - xbar) atTop (𝓝 (0 : E)) := by
        have hy_const : Tendsto (fun _ : ℕ ↦ xbar) atTop (𝓝 xbar) := tendsto_const_nhds
        simpa using hy.sub hy_const
      have hy_level' : ∀ᶠ k in atTop, xbar + (y k - xbar) ∈ f ⁻¹' {f xbar} :=
        .of_forall fun k ↦ by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy_level k
      have hy_secant' :
          Tendsto
            (fun k ↦ (Real.toNNReal ‖y k - xbar‖⁻¹ : NNReal) • (y k - xbar))
            atTop (𝓝 s) := by
        refine Tendsto.congr' ?_ hy_secant
        exact .of_forall fun k ↦ by
          change ‖y k - xbar‖⁻¹ • (y k - xbar) =
            ((Real.toNNReal ‖y k - xbar‖⁻¹ : ℝ) • (y k - xbar))
          have hnonneg : 0 ≤ ‖y k - xbar‖⁻¹ := by positivity
          simp [Real.toNNReal_of_nonneg hnonneg]
      exact mem_tangentConeAt_of_seq atTop
        (fun k ↦ (Real.toNNReal ‖y k - xbar‖⁻¹ : NNReal))
        (fun k ↦ y k - xbar) hy_sub hy_level' hy_secant'
    · have hnorm_t :
          Tendsto (fun k ↦ ‖‖y k - xbar‖⁻¹ • (y k - xbar)‖) atTop (𝓝 ‖s‖) :=
        Tendsto.comp continuous_norm.continuousAt hy_secant
      have hnorm_eq :
          (fun k ↦ ‖‖y k - xbar‖⁻¹ • (y k - xbar)‖) =ᶠ[atTop] fun _ : ℕ ↦ (1 : ℝ) :=
        .of_forall fun k ↦ by
          have hnorm_ne : ‖y k - xbar‖ ≠ 0 := by
            exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hy_ne k))
          simp [norm_smul, hnorm_ne]
      exact tendsto_nhds_unique (Tendsto.congr' hnorm_eq hnorm_t) tendsto_const_nhds
