/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_52

open Set

local notation "PathSpace" => C(NNReal, ℝ)

private theorem boundedVariationOn_univ_zero : BoundedVariationOn (0 : PathSpace) univ := by
  rw [BoundedVariationOn]
  rw [eVariationOn.constant_on]
  · simp
  · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    rfl

private theorem boundedVariationOn_univ_prod {F G : PathSpace}
    (hF : BoundedVariationOn F univ) (hG : BoundedVariationOn G univ) :
    BoundedVariationOn (fun t ↦ (F t, G t)) univ := by
  rw [BoundedVariationOn] at hF hG ⊢
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hF, hG⟩) ?_
  dsimp [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, us⟩
  calc
    ∑ i ∈ Finset.range n,
        edist ((F (u (i + 1))), (G (u (i + 1)))) ((F (u i)), (G (u i)))
        ≤ ∑ i ∈ Finset.range n,
            (edist (F (u (i + 1))) (F (u i)) + edist (G (u (i + 1))) (G (u i))) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [Prod.edist_eq]
          exact max_le_iff.mpr ⟨le_add_of_nonneg_right bot_le, by simp⟩
    _ =
        (∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))) +
        ∑ i ∈ Finset.range n, edist (G (u (i + 1))) (G (u i)) := by
          rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn F univ + eVariationOn G univ :=
      add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)

private theorem boundedVariationOn_univ_add {F G : PathSpace}
    (hF : BoundedVariationOn F univ) (hG : BoundedVariationOn G univ) :
    BoundedVariationOn (F + G) univ := by
  simpa [Function.comp] using
    (lipschitzWith_lipschitz_const_add_edist.comp_boundedVariationOn
      (boundedVariationOn_univ_prod hF hG))

private theorem boundedVariationOn_univ_smul (c : ℝ) {F : PathSpace}
    (hF : BoundedVariationOn F univ) : BoundedVariationOn (c • F) univ := by
  simpa [Function.comp] using (lipschitzWith_smul c).comp_boundedVariationOn hF

/-- Remark 21.53: the continuous real-valued paths on `[0, ∞)` with finite first variation form a
real vector space. The textbook finiteness condition is the canonical owner predicate
`BoundedVariationOn F univ`; this submodule is the corresponding bridge/view packaging. -/
def boundedVariationSubmodule : Submodule ℝ PathSpace where
  carrier := {F | BoundedVariationOn F univ}
  zero_mem' := boundedVariationOn_univ_zero
  add_mem' := boundedVariationOn_univ_add
  smul_mem' := boundedVariationOn_univ_smul

/-- Global bounded variation on `[0, ∞)` implies the earlier chapter owner property of local
bounded variation, so the bounded-variation submodule sits inside `continuousVariationSubmodule`.
-/
theorem boundedVariationSubmodule_le_continuousVariationSubmodule :
    boundedVariationSubmodule ≤ continuousVariationSubmodule := by
  intro F hF
  change LocallyBoundedVariationOn F univ
  exact hF.locallyBoundedVariationOn
