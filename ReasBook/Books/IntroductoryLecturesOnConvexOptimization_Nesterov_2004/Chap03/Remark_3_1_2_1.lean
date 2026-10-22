/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise Topology ENNReal NNReal WithTopConvexAnalysis

universe u

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [ContinuousSMul ℝ E]

/- Remark 3.1.2.1 lies in the Minkowski-functional / gauge domain.

Sampled owner-style declarations:
- mathlib `egauge`
- mathlib `egauge_eq_top`
- mathlib `gauge`
- project `IsPositivelyHomogeneousOn`

Best owner abstraction:
- the mathlib extended gauge owner `egauge ℝ≥0 Q`, with `gauge Q` as its finite real-valued view

Primitive data:
- a set `Q : Set E`
- the convexity hypothesis `Convex ℝ Q`
- the neighborhood-of-zero hypothesis `(0 : E) ∈ interior Q`

Derived API:
- the source-facing `WithTop ℝ` bridge `minkowskiFunctional Q`
- the finite-value bridge `minkowskiFunctional_eq_gauge` on `dom (ψ[Q])`
- the whole-space finiteness bridge `dom_minkowskiFunctional_eq_univ_of_zero_mem_interior`
- the whole-space equality bridge `minkowskiFunctional_eq_gauge_of_zero_mem_interior`
- degree-one positive homogeneity on `Set.univ`, recorded through the chapter owner
  `IsPositivelyHomogeneousOn 1 Set.univ`
- whole-space convexity `ConvexOn ℝ Set.univ`

Source/core/bridge triage:
- source-facing: the textbook remark that the Minkowski functional is positively homogeneous and
  convex, together with the `WithTop ℝ` notation `ψ[Q]` used downstream in subdifferential
  statements;
- core/canonical: mathlib `egauge` and `gauge`;
- bridge/view: `minkowskiFunctional`, which repackages `egauge ℝ≥0 Q` in the chapter's
  `WithTop ℝ` codomain, `minkowskiFunctional_eq_gauge` on the canonical effective domain
  `dom (ψ[Q])`, and the whole-space bridges obtained from `(0 : E) ∈ interior Q`.

The bounded and closed hypotheses from the textbook remark are redundant for these two
consequences, so the refined statement keeps only the convexity and interior-point assumptions
actually used by the canonical gauge API.
-/

section MinkowskiFunctional

private def ennrealToWithTopReal (x : ℝ≥0∞) : WithTop ℝ :=
  if x = ⊤ then ⊤ else ((x.toReal : ℝ) : WithTop ℝ)

/-- The textbook Minkowski functional `ψ_Q`, viewed as a `WithTop ℝ`-valued function so that the
value is `⊤` when no nonnegative scaling of `Q` contains the point. This is the chapter's
`WithTop ℝ` bridge of the canonical extended gauge `egauge ℝ≥0 Q`. -/
abbrev minkowskiFunctional {F : Type u} [SMul ℝ F] (Q : Set F) : F → WithTop ℝ :=
  fun x ↦ ennrealToWithTopReal (egauge ℝ≥0 Q x)

namespace MinkowskiFunctional

scoped notation:max "ψ[" Q "]" => minkowskiFunctional Q

end MinkowskiFunctional

open scoped MinkowskiFunctional

section GaugeBridge

variable {F : Type u}
variable [AddCommGroup F] [Module ℝ F]

/-- On the effective domain `dom (ψ[Q])`, the source-facing Minkowski functional agrees with
mathlib's canonical real-valued gauge. -/
theorem minkowskiFunctional_eq_gauge
    {Q : Set F} {x : F} (hx : x ∈ dom (ψ[Q])) :
    ψ[Q] x = (gauge Q x : WithTop ℝ) := by
  -- Read the finite `WithTop` value as a real number before comparing with the canonical gauge.
  let e : ℝ≥0∞ := egauge ℝ≥0 Q x
  have he_ne_top : e ≠ ⊤ := by
    intro he_top
    have : ψ[Q] x = ⊤ := by
      simp [minkowskiFunctional, ennrealToWithTopReal, e, he_top]
    simp [this] at hx
  have hrealpart : withTopRealPart (ψ[Q]) x = e.toReal := by
    apply WithTop.coe_injective
    rw [coe_withTopRealPart hx]
    simp [minkowskiFunctional, ennrealToWithTopReal, e, he_ne_top]
  have hreal_eq_gauge : e.toReal = gauge Q x := by
    by_cases hs : {r : ℝ | 0 < r ∧ x ∈ r • Q}.Nonempty
    · have hlower : e.toReal ≤ gauge Q x := by
        -- Every positive scale witnessing membership bounds the extended gauge from above.
        have hs' : {r ∈ Set.Ioi (0 : ℝ) | x ∈ r • Q}.Nonempty := by
          rcases hs with ⟨r, hr, hxr⟩
          exact ⟨r, hr, hxr⟩
        rw [gauge_def]
        refine le_csInf hs' ?_
        intro r hr
        let c : ℝ≥0 := ⟨r, le_of_lt hr.1⟩
        have he_le : e ≤ (c : ℝ≥0∞) := by
          have hc_mem : x ∈ c • Q := by
            simpa [c, NNReal.smul_def] using hr.2
          simpa [c, e] using egauge_le_of_mem_smul (𝕜 := ℝ≥0) (c := c) hc_mem
        have htoReal : e.toReal ≤ r := by
          simpa [c] using ENNReal.toReal_mono (by simp) he_le
        exact htoReal
      have hupper : gauge Q x ≤ e.toReal := by
        -- Approximate the infimum defining `egauge` by an actual scaling witness.
        refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
        let r : ℝ≥0 := ⟨e.toReal + ε, add_nonneg ENNReal.toReal_nonneg hε.le⟩
        have he_lt : e < (r : ℝ≥0∞) := by
          have htoReal_lt : e.toReal < (r : ℝ) := by
            change e.toReal < e.toReal + ε
            exact lt_add_of_pos_right e.toReal hε
          exact (ENNReal.toReal_lt_toReal he_ne_top (by simp)).1 (by simpa [r] using htoReal_lt)
        rcases egauge_lt_iff.1 he_lt with ⟨c, hxc, hc_lt⟩
        have hc_real : (c : ℝ) < e.toReal + ε := by
          simpa [r] using hc_lt
        have hc_mem : x ∈ (c : ℝ) • Q := by
          simpa [NNReal.smul_def] using hxc
        exact (gauge_le_of_mem c.2 hc_mem).trans_lt hc_real
      exact le_antisymm hlower hupper
    · have hgauge_zero : gauge Q x = 0 := by
        -- If no positive scaling contains `x`, then the gauge infimum is taken over the empty set.
        have hempty : {r ∈ Set.Ioi (0 : ℝ) | x ∈ r • Q} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro r hr
          exact hs ⟨r, hr.1, hr.2⟩
        rw [gauge_def, hempty, Real.sInf_empty]
      have hx_zero : x ∈ (0 : ℝ≥0) • Q := by
        by_contra hx_zero
        have he_top : e = ⊤ := by
          simpa [e] using
            (egauge_eq_top (𝕜 := ℝ≥0) (s := Q) (x := x)).2 fun c ↦ by
              rcases eq_or_lt_of_le c.2 with hc0 | hc
              · have hc0' : c = 0 := NNReal.eq (by simpa using hc0.symm)
                subst hc0'
                simpa using hx_zero
              · intro hxc
                exact hs ⟨(c : ℝ), hc, by simpa [NNReal.smul_def] using hxc⟩
        exact he_ne_top he_top
      have he_zero : e = 0 := by
        have he_le_zero : e ≤ 0 := by
          have h0 : egauge ℝ≥0 Q x ≤ ‖(0 : ℝ≥0)‖ₑ :=
            egauge_le_of_mem_smul (𝕜 := ℝ≥0) (c := (0 : ℝ≥0)) hx_zero
          have hnorm_zero : ‖(0 : ℝ≥0)‖ₑ = (0 : ℝ≥0∞) := by
            rfl
          rw [hnorm_zero] at h0
          simpa [e] using h0
        exact le_antisymm he_le_zero bot_le
      simp [he_zero, hgauge_zero]
  -- Coercing the finite real part back to `WithTop ℝ` gives the desired source-to-canonical bridge.
  calc
    ψ[Q] x = ((withTopRealPart (ψ[Q]) x : ℝ) : WithTop ℝ) := (coe_withTopRealPart hx).symm
    _ = (e.toReal : WithTop ℝ) := by rw [hrealpart]
    _ = (gauge Q x : WithTop ℝ) := by rw [hreal_eq_gauge]

end GaugeBridge

end MinkowskiFunctional

open scoped MinkowskiFunctional

/-- If `0` lies in the interior of `Q`, then the source-facing Minkowski functional is finite
everywhere. -/
theorem dom_minkowskiFunctional_eq_univ_of_zero_mem_interior
    {Q : Set E} (hQ_zero : (0 : E) ∈ interior Q) :
    dom (ψ[Q]) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  -- Interior at the origin gives absorbency, so some positive scaling of `Q` contains `x`.
  have hQ_absorbent : Absorbent ℝ Q :=
    absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hQ_zero)
  obtain ⟨r, hr_pos, hxr⟩ := hQ_absorbent.gauge_set_nonempty (x := x)
  have he_ne_top : egauge ℝ≥0 Q x ≠ ⊤ := by
    intro he_top
    rw [egauge_eq_top] at he_top
    exact he_top ⟨r, hr_pos.le⟩ (by simpa using hxr)
  -- Finite extended gauge means the `WithTop ℝ`-valued Minkowski functional is finite as well.
  simp [minkowskiFunctional, ennrealToWithTopReal, he_ne_top]

/-- If `0` lies in the interior of `Q`, then the source-facing Minkowski functional agrees
everywhere with mathlib's canonical real-valued gauge. -/
theorem minkowskiFunctional_eq_gauge_of_zero_mem_interior
    {Q : Set E} (hQ_zero : (0 : E) ∈ interior Q) (x : E) :
    ψ[Q] x = (gauge Q x : WithTop ℝ) := by
  have hx : x ∈ dom (ψ[Q]) := by
    simp [dom_minkowskiFunctional_eq_univ_of_zero_mem_interior hQ_zero]
  simpa using minkowskiFunctional_eq_gauge hx

/-- Canonical gauge companion to Remark 3.1.2.1. -/
-- Proof sketch: obtain absorbency from the interior-neighborhood hypothesis, then combine
-- `gauge_smul_of_nonneg` for degree-one positive homogeneity with `gauge_add_le` to build the
-- whole-space `ConvexOn` witness.
theorem gauge_posHom_and_convexOn_univ_of_convex_zero_mem_interior
    {Q : Set E} (hQ_convex : Convex ℝ Q) (hQ_zero : (0 : E) ∈ interior Q) :
    IsPositivelyHomogeneousOn 1 Set.univ (gauge Q) ∧
      ConvexOn ℝ Set.univ (gauge Q) := by
  have hQ_absorbent : Absorbent ℝ Q :=
    absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hQ_zero)
  constructor
  · refine {
      smul_mem := by
        intro x hx τ
        simp
      map_smul := by
        intro x hx τ
        rw [NNReal.smul_def, gauge_smul_of_nonneg (s := Q) (a := (τ : ℝ)) τ.2]
        have hτ : (τ : ℝ).rpow (1 : ℝ) = (τ : ℝ) := by
          exact Real.rpow_one (τ : ℝ)
        rw [hτ] }
    -- Positive homogeneity is exactly the canonical scaling law for the gauge.
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    -- The source proof's convex combination estimate becomes gauge subadditivity after scaling.
    have hineq :
        gauge Q (a • x + b • y) ≤ a * gauge Q x + b * gauge Q y := by
      calc
      gauge Q (a • x + b • y)
          ≤ gauge Q (a • x) + gauge Q (b • y) := gauge_add_le hQ_convex hQ_absorbent _ _
      _ = a * gauge Q x + b * gauge Q y := by
        rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb, smul_eq_mul, smul_eq_mul]
    simpa [smul_eq_mul] using hineq

/-- Remark 3.1.2.1: if `Q` is convex and contains `0` in its interior, then the everywhere-finite
real representative `withTopRealPart (ψ[Q])` of its Minkowski functional is positively homogeneous
of degree `1` and convex on all of the ambient real topological vector space. In the textbook
Euclidean bounded closed case, this is exactly the same Minkowski-functional conclusion. -/
-- Proof sketch: first use `(0 : E) ∈ interior Q` to identify `ψ[Q]` with the everywhere-finite
-- canonical gauge `gauge Q`, then transport degree-one positive homogeneity and whole-space
-- convexity from the canonical gauge owner API.
theorem minkowskiFunctional_posHom_and_convexOn_univ_of_convex_zero_mem_interior
    {Q : Set E} (hQ_convex : Convex ℝ Q) (hQ_zero : (0 : E) ∈ interior Q) :
    IsPositivelyHomogeneousOn 1 Set.univ (withTopRealPart (ψ[Q])) ∧
      ConvexOn ℝ Set.univ (withTopRealPart (ψ[Q])) := by
  -- Transport the canonical gauge properties through the everywhere-finite pointwise equality.
  have hEq : withTopRealPart (ψ[Q]) = gauge Q := by
    funext x
    have hx : x ∈ dom (ψ[Q]) := by
      simp [dom_minkowskiFunctional_eq_univ_of_zero_mem_interior hQ_zero]
    apply WithTop.coe_injective
    rw [coe_withTopRealPart hx, minkowskiFunctional_eq_gauge_of_zero_mem_interior hQ_zero]
  simpa [hEq] using
    gauge_posHom_and_convexOn_univ_of_convex_zero_mem_interior hQ_convex hQ_zero
