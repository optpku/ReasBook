/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_4_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_1_2

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped BigOperators
open scoped SecondOrderCone

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Nontrivial E]

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

/- Lemma 5.4.3.4 lies in the Chapter 5 second-order-cone / self-concordant-barrier domain.

Sampled owner declarations in this domain:
* `secondOrderCone` and `mem_interior_secondOrderCone_iff` from `Lemma_5_4_3_3`, the chapter owner
  for the second-order cone as a `ConvexCone ℝ (E × ℝ)`;
* mathlib `WithLp 2 (E × ℝ)` together with `WithLp.ofLp`, the canonical `L²` ambient owner for
  barriers on the second-order cone;
* mathlib `ConvexCone.convex`, which derives convexity from that cone owner instead of storing a
  parallel set-level wrapper;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for self-concordant
  barriers;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  from `Theorem_5_4_1_2`, the canonical lower-bound owner theorem specialized here.

Source/core/bridge triage:
* source-facing: the lower bound `ν ≥ 2` for barriers on the second-order cone;
* core/canonical: the raw-pair cone owner `secondOrderCone : ConvexCone ℝ (E × ℝ)` together
  with the barrier owner
  `IsSelfConcordantBarrierOnWith ((fun z : Z ↦ z.ofLp) ⁻¹' interior K₂[E]) ν F`;
* bridge/view: the textbook inequalities `‖x‖ ≤ t` and `‖x‖ < t`, already exposed by
  `mem_secondOrderCone_iff` and `mem_interior_secondOrderCone_iff`, together with the source
  notation `K₂[E]` and the ambient bridge `z ↦ z.ofLp`.

Primitive data:
* a nontrivial real Hilbert-space ambient `E`, used only to choose a norm-one vector;
* the self-concordant barrier owner on the pulled-back interior
  `IsSelfConcordantBarrierOnWith ((fun z : Z ↦ z.ofLp) ⁻¹' interior K₂[E]) ν F`.

Derived API:
* the source-facing lower bound `(2 : ℝ) ≤ (ν : ℝ)`.

This file therefore reuses the existing second-order-cone owner from `Lemma_5_4_3_3` instead of
keeping a parallel coordinate model. The source-facing cone notation remains on raw pairs, while
the barrier owner lives on the canonical `L²` product owner and is accessed through `z ↦ z.ofLp`.
The earlier `ℝⁿ` proof ingredient is refined to the intrinsic owner-level fact that a nontrivial
real normed space contains a norm-one vector. -/

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` to
-- `secondOrderCone : ConvexCone ℝ (E × ℝ)` with base point `(0, 1)`, recession directions
-- `(h, 1)` and `(-h, 1)` for a unit vector `h : E`, and coefficients
-- `α₁ = α₂ = β₁ = β₂ = 1 / 2`. Transport the cone to the canonical `L²` product owner
-- `Z = WithLp 2 (E × ℝ)` through `z ↦ z.ofLp`; the backward steps land on the boundary, the
-- combined step reaches `(0, 0) ∈ K₂[E]`, and the general lower-bound theorem yields `1 + 1 ≤ ν`.
/-- Lemma 5.4.3.4: every `ν`-self-concordant barrier for the interior of the second-order cone
`K₂ = {(x, t) ∈ E × ℝ | ‖x‖ ≤ t}` in a nontrivial real Hilbert space `E`, viewed on the canonical
`L²` product ambient space through `z ↦ z.ofLp`, has barrier parameter at least `2`. Specializing
to `E = EuclideanSpace ℝ (Fin n)` with `0 < n` recovers the textbook `ℝⁿ` statement. -/
theorem secondOrderCone_barrierParameter_ge_two
    {ν : NNReal} {F : Z → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (ofZ ⁻¹' interior K₂[E]) ν F) :
    (2 : ℝ) ≤ (ν : ℝ) := by
  let Q : Set Z := ofZ ⁻¹' K₂[E]
  have hQ_interior :
      interior Q = ofZ ⁻¹' interior K₂[E] := by
    simpa [Q] using
      ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toHomeomorph.preimage_interior K₂[E]).symm
  have hFQ : IsSelfConcordantBarrierOnWith (interior Q) ν F := by
    simpa [hQ_interior] using hF
  obtain ⟨h, hh_norm⟩ : ∃ h : E, ‖h‖ = 1 := by
    simpa using (exists_norm_eq E (show 0 ≤ (1 : ℝ) by positivity))
  let xBar : Z := WithLp.toLp 2 ((0 : E), (1 : ℝ))
  let p : Fin 2 → Z
    | 0 => WithLp.toLp 2 (h, 1)
    | 1 => WithLp.toLp 2 (-h, 1)
  let β : Fin 2 → ℝ := fun _ ↦ 1 / 2
  let α : Fin 2 → ℝ := fun _ ↦ 1 / 2
  have hQ_convex : Convex ℝ Q := by
    simpa [Q] using
      (secondOrderCone E).convex.linear_preimage
        (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toLinearMap
  have hxBar : xBar ∈ interior Q := by
    rw [hQ_interior]
    change xBar.ofLp ∈ interior K₂[E]
    rw [mem_interior_secondOrderCone_iff]
    simp [xBar]
  have hp :
      ∀ j : Fin 2,
        ∀ ⦃x : Z⦄, x ∈ Q → ∀ t : ℝ, 0 ≤ t → x + t • p j ∈ Q := by
    intro j x hx t ht
    have hxK : x.ofLp ∈ K₂[E] := by
      simpa [Q] using hx
    change (x + t • p j).ofLp ∈ K₂[E]
    rw [mem_secondOrderCone_iff] at hxK ⊢
    fin_cases j
    · calc
        ‖(x + t • p 0).ofLp.1‖ = ‖x.ofLp.1 + t • h‖ := by simp [p]
        _ ≤ ‖x.ofLp.1‖ + ‖t • h‖ := norm_add_le _ _
        _ = ‖x.ofLp.1‖ + t := by
          rw [norm_smul, hh_norm, Real.norm_of_nonneg ht, mul_one]
        _ ≤ x.ofLp.2 + t := by linarith [hxK]
        _ = (x + t • p 0).ofLp.2 := by simp [p]
    · calc
        ‖(x + t • p 1).ofLp.1‖ = ‖x.ofLp.1 + t • -h‖ := by simp [p]
        _ ≤ ‖x.ofLp.1‖ + ‖t • -h‖ := norm_add_le _ _
        _ = ‖x.ofLp.1‖ + t := by
          rw [norm_smul, norm_neg, hh_norm, Real.norm_of_nonneg ht, mul_one]
        _ ≤ x.ofLp.2 + t := by linarith [hxK]
        _ = (x + t • p 1).ofLp.2 := by simp [p]
  have hβ_pos : ∀ j : Fin 2, 0 < β j := by
    intro j
    norm_num [β]
  have hβ_exit : ∀ j : Fin 2, xBar - β j • p j ∉ interior Q := by
    intro j
    rw [hQ_interior]
    change (xBar - β j • p j).ofLp ∉ interior K₂[E]
    rw [mem_interior_secondOrderCone_iff]
    fin_cases j <;>
      simp [xBar, β, p, hh_norm, norm_smul, not_lt] <;>
      norm_num
  have hα_nonneg : ∀ j : Fin 2, 0 ≤ α j := by
    intro j
    norm_num [α]
  have hy : xBar - ∑ j, α j • p j ∈ Q := by
    have hyK : (xBar - ∑ j, α j • p j).ofLp ∈ K₂[E] := by
      rw [mem_secondOrderCone_iff]
      simp [xBar, α, p, Fin.sum_univ_two]
      norm_num
    simpa [Q] using hyK
  have hbound :=
    hFQ.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions
      hQ_convex hxBar p hp β α hβ_pos hβ_exit hα_nonneg hy
  simpa [α, β, Fin.sum_univ_two] using hbound

end
