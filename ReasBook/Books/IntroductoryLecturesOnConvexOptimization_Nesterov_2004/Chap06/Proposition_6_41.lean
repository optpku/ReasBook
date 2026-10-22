/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 6.41 lies in the chapter's constrained-subdifferential / affine-optimality domain.

Sampled owner-style declarations:
- `constrainedSubdifferential` together with the notation `∂[Q] f(x)` in
  `Chap03/Definition_3_1_5`;
- `mem_constrainedSubdifferential_iff` in `Chap03/Definition_3_1_5`, the atomic bridge from the
  owner to the raw affine lower-support inequality;
- `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential` in
  `Chap03/Theorem_3_1_23`, a downstream owner-level consumer of the same constrained
  subdifferential;
- `subdifferentialWithin` in `Chap03/Theorem_3_44`, the real-valued bridge/view built on the same
  owner.

Best owner abstraction:
- source-facing: Proposition 6.41's affine optimality criterion for an extended-valued constrained
  subgradient;
- core/canonical: `constrainedSubdifferential`;
- bridge/view: `mem_constrainedSubdifferential_iff`.

Primitive data:
- a feasible set `Q`, extended-valued objective `Ψ`, and feasible base point `v ∈ Q`;
- finiteness of the base value `Ψ v < ⊤`;
- the affine optimality inequality on `Q`.

Derived API:
- the owner-level conclusion `-s ∈ ∂[Q] Ψ(v)`.

Source/core/bridge triage:
- source-facing: the proposition below, written directly on the chapter owner notation `∂[Q] Ψ(v)`;
- core/canonical: `constrainedSubdifferential`;
- bridge/view: the raw affine inequality hypothesis and the membership lemma
  `mem_constrainedSubdifferential_iff`.

The previous file duplicated the Chapter 3 owner locally and omitted the owner feasibility
condition `v ∈ Q`. This refinement removes the duplicate wheel, states the proposition directly
with the canonical owner surface, and keeps only the textbook affine inequality as the bridge
assumption.
-/

/-- Proposition 6.41: if a feasible point `v ∈ Q` satisfies the affine optimality inequality
`⟪s, x - v⟫ + Ψ(x) ≥ Ψ(v)` for every `x ∈ Q`, then `-s` belongs to the constrained
subdifferential of `Ψ` at `v` relative to `Q`. -/
-- Proof sketch: unfold the owner membership criterion
-- `mem_constrainedSubdifferential_iff`. The finiteness hypothesis gives `v ∈ dom Ψ`, and the
-- assumed inequality rearranges to the defining affine lower-support inequality for `-s`.
theorem neg_mem_constrainedSubdifferential_of_affine_optimality
    {Q : Set E} {Ψ : E → WithTop ℝ} {s v : E}
    (hvQ : v ∈ Q)
    (hv_finite : Ψ v < ⊤)
    (hoptimal :
      ∀ ⦃x : E⦄, x ∈ Q →
        (((inner ℝ s (x - v) : ℝ) : WithTop ℝ) + Ψ x) ≥ Ψ v) :
    -s ∈ ∂[Q] Ψ(v) := by
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨hvQ, by simpa, ?_⟩
  intro x hx
  by_cases hx_finite : Ψ x < ⊤
  · rcases WithTop.ne_top_iff_exists.mp (ne_of_lt hv_finite) with ⟨rv, hrv⟩
    rcases WithTop.ne_top_iff_exists.mp (ne_of_lt hx_finite) with ⟨rx, hrx⟩
    have hopt := hoptimal hx
    rw [← hrv, ← hrx] at hopt ⊢
    norm_num at hopt ⊢
    have hreal : rv ≤ inner ℝ s (x - v) + rx := by
      exact_mod_cast hopt
    have hminorant : rv + -inner ℝ s (x - v) ≤ rx := by
      linarith
    exact_mod_cast hminorant
  · have hx_top : Ψ x = ⊤ := by
      simpa [lt_top_iff_ne_top] using hx_finite
    simp [hx_top]

end
