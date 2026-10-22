/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 6.2 lies in the chapter's extended-valued Fenchel / subdifferential domain.

Primary domain:
- Fenchel duality and extended-valued subgradients on real inner-product spaces.

Relevant sampled owner-style declarations:
- `dom` and `withTopToEReal` in `Definition_3_3`, the canonical effective-domain / codomain bridge;
- `IsSubgradientAt`, `subdifferential`, and the notation `∂ f(x)` in `Definition_3_1_5`, the
  chapter owner surface for extended-valued subgradients;
- `fenchelDual` and the notation `f⋆` in `Definition_3_1_2_1`, the source-facing Fenchel-dual
  owner induced from the dual-space owner `fenchelConjugate`;
- `subdifferential_subset_dom_fenchelDual_of_nonempty` in `Theorem_3_1_5_2`, the nearby owner
  theorem showing that nonempty `∂ f(x)` forces finiteness of `f⋆` at every subgradient.

Best owner abstraction:
- the existing source-facing owner surface `∂ f(x)` and `f⋆`.

Primitive data:
- a membership hypothesis `g ∈ ∂ f(x)`.

Derived API:
- the Fenchel--Young equality at a subgradient;
- the corresponding affine lower-support inequality for the dual function at the dual point.

Source/core/bridge triage:
- source-facing: Proposition 6.2's equality `f(x) + f*(g) = ⟪g, x⟫`;
- core/canonical: `dom`, `subdifferential`, `fenchelDual`;
- bridge/view: the second theorem below, which states the source-facing content of
  `x ∈ ∂ f*(g)` directly on the canonical `EReal`-valued owner `f⋆`, instead of rebuilding a
  parallel `WithTop ℝ`-valued conjugate wrapper just to reuse `subdifferential`.

The previous version duplicated the effective-domain, finite-real-part, subgradient,
subdifferential, and Fenchel-conjugate owners locally. This refinement removes those duplicate
wheels and keeps Proposition 6.2 on the existing chapter owner surface. The textbook hypotheses
that `f` is proper, convex, and finite-dimensional are not needed for the statement itself once
`g ∈ ∂ f(x)` is taken as primitive data, so they are removed from the public API.
-/

-- Proof sketch: the defining subgradient inequality with `y = x` gives one side, and evaluating
-- the supremum defining `f⋆(g)` at `x` gives the reverse side.
/-- Proposition 6.2: if `g ∈ ∂ f(x)`, then `f(x) + f*(g) = ⟪g, x⟫`. -/
theorem fenchelYoung_equality_of_mem_subdifferential
    {f : E → WithTop ℝ} {x g : E} (hg : g ∈ ∂ f(x)) :
    withTopToEReal (f x) + (f⋆) g = (inner ℝ g x : EReal) := by
  have hxdom : x ∈ dom f := (mem_subdifferential_iff.mp hg).1
  have hfx_ne_bot : withTopToEReal (f x) ≠ ⊥ := by
    change (((f x : WithTop ℝ) : WithBot (WithTop ℝ))) ≠ ⊥
    exact WithBot.coe_ne_bot
  have hfx_ne_top : withTopToEReal (f x) ≠ ⊤ := by
    have hx' : f x < ⊤ := mem_withTopEffectiveDomain_iff.mp hxdom
    change (((f x : WithTop ℝ) : WithBot (WithTop ℝ))) ≠ ⊤
    exact_mod_cast ne_of_lt hx'
  have hfx : ((withTopRealPart f x : ℝ) : EReal) = withTopToEReal (f x) := by
    simpa [withTopToEReal] using congrArg withTopToEReal (coe_withTopRealPart hxdom)
  have hsup_le : (f⋆) g ≤ (inner ℝ g x : EReal) - withTopToEReal (f x) := by
    rw [fenchelDual_apply]
    refine iSup_le ?_
    intro y
    by_cases hy : y ∈ dom f
    · have hsub := (mem_subdifferential_iff.mp hg).2 hy
      have hy' : ((withTopRealPart f y : ℝ) : EReal) = withTopToEReal (f y) := by
        simpa [withTopToEReal] using congrArg withTopToEReal (coe_withTopRealPart hy)
      have hreal : inner ℝ g y - withTopRealPart f y ≤ inner ℝ g x - withTopRealPart f x := by
        have hsub' : withTopRealPart f x + inner ℝ g (y - x) ≤ withTopRealPart f y := by
          have hsub'' := hsub
          rw [← coe_withTopRealPart hxdom] at hsub''
          rw [← coe_withTopRealPart hy] at hsub''
          exact_mod_cast hsub''
        rw [inner_sub_right] at hsub'
        linarith
      rw [← hy', ← hfx, ← EReal.coe_sub, ← EReal.coe_sub]
      exact_mod_cast hreal
    · have hy_top : f y = ⊤ := top_unique (not_lt.mp hy)
      rw [hy_top, withTopToEReal]
      change (⊥ : EReal) ≤ (inner ℝ g x : EReal) - withTopToEReal (f x)
      exact bot_le
  have hle : withTopToEReal (f x) + (f⋆) g ≤ (inner ℝ g x : EReal) := by
    have := EReal.add_le_of_le_sub hsup_le
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hge : (inner ℝ g x : EReal) ≤ withTopToEReal (f x) + (f⋆) g := by
    rw [fenchelDual_apply]
    have htest : (inner ℝ g x : EReal) - withTopToEReal (f x) ≤ (f⋆) g := by
      exact le_iSup (fun y : E ↦ (inner ℝ g y : EReal) - withTopToEReal (f y)) x
    have hconv :
        (inner ℝ g x : EReal) - withTopToEReal (f x) ≤ (f⋆) g ↔
          (inner ℝ g x : EReal) ≤ (f⋆) g + withTopToEReal (f x) :=
      EReal.sub_le_iff_le_add (Or.inl hfx_ne_bot) (Or.inl hfx_ne_top)
    have : (inner ℝ g x : EReal) ≤ (f⋆) g + withTopToEReal (f x) := hconv.mp htest
    simpa [add_comm] using this
  exact antisymm hle hge

-- Proof sketch: combine the Fenchel--Young equality at `(x, g)` with the defining supremum lower
-- bound `(f⋆) h ≥ ⟪h, x⟫ - f(x)` obtained by testing the supremum at `x`.
/-- If `g ∈ ∂ f(x)`, then `x` satisfies the dual affine lower-support inequality at `g`, i.e. the
source-facing content of `x ∈ ∂ f*(g)` on the canonical owner `f⋆`. -/
theorem subgradient_inequality_fenchelDual_of_mem_subdifferential
    {f : E → WithTop ℝ} {x g : E} (hg : g ∈ ∂ f(x)) :
    g ∈ dom (f⋆) ∧
      ∀ ⦃h : E⦄, h ∈ dom (f⋆) →
        (f⋆) h ≥ (f⋆) g + (inner ℝ x (h - g) : EReal) := by
  refine ⟨subdifferential_subset_dom_fenchelDual hg, ?_⟩
  intro h hhdom
  have hxdom : x ∈ dom f := (mem_subdifferential_iff.mp hg).1
  have hfx_ne_bot : withTopToEReal (f x) ≠ ⊥ := by
    change (((f x : WithTop ℝ) : WithBot (WithTop ℝ))) ≠ ⊥
    exact WithBot.coe_ne_bot
  have hfx_ne_top : withTopToEReal (f x) ≠ ⊤ := by
    have hx' : f x < ⊤ := mem_withTopEffectiveDomain_iff.mp hxdom
    change (((f x : WithTop ℝ) : WithBot (WithTop ℝ))) ≠ ⊤
    exact_mod_cast ne_of_lt hx'
  have htest : (inner ℝ h x : EReal) - withTopToEReal (f x) ≤ (f⋆) h := by
    rw [fenchelDual_apply]
    exact le_iSup (fun y : E ↦ (inner ℝ h y : EReal) - withTopToEReal (f y)) x
  have hsupport : (f⋆) g + (inner ℝ x (h - g) : EReal) ≤
      (inner ℝ h x : EReal) - withTopToEReal (f x) := by
    have hsupport_add :
        (f⋆) g + (inner ℝ x (h - g) : EReal) + withTopToEReal (f x) ≤
          (inner ℝ h x : EReal) := by
      calc
        (f⋆) g + (inner ℝ x (h - g) : EReal) + withTopToEReal (f x)
            = withTopToEReal (f x) + (f⋆) g + (inner ℝ x (h - g) : EReal) := by
                ac_rfl
        _ = (inner ℝ g x : EReal) + (inner ℝ x (h - g) : EReal) := by
              rw [fenchelYoung_equality_of_mem_subdifferential hg]
        _ ≤ (inner ℝ h x : EReal) := by
              have hreal : inner ℝ g x + inner ℝ x (h - g) = inner ℝ h x := by
                rw [inner_sub_right, real_inner_comm x g, real_inner_comm x h]
                ring
              exact le_of_eq (by exact_mod_cast hreal)
    have hsub :
        (f⋆) g + (inner ℝ x (h - g) : EReal) ≤
            (inner ℝ h x : EReal) - withTopToEReal (f x) ↔
          (f⋆) g + (inner ℝ x (h - g) : EReal) + withTopToEReal (f x) ≤
            (inner ℝ h x : EReal) :=
      EReal.le_sub_iff_add_le (Or.inl hfx_ne_bot) (Or.inl hfx_ne_top)
    exact hsub.2 hsupport_add
  exact hsupport.trans htest

end
