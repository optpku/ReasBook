/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3.1.5.2 lies in the chapter's Fenchel-biconjugacy domain.

Primary domain:
- Fenchel conjugates, biduals, and subdifferentials of `ℝ ∪ {+∞}`-valued functions on real
  inner-product spaces.

Sampled owner-style declarations:
- `fenchelConjugate` and `fenchelConjugate_apply` in `Chap06/Definition_6_1`, the core
  extended-real Fenchel-conjugate owner and its evaluation theorem;
- `fenchelDual` and `fenchelDual_apply` in `Definition_3_1_2_1`, the source-facing Fenchel-dual
  bridge owner and its supremum formula;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner for
  extended-valued subgradients;
- `dom` in `Definition_3_1_1_2`, the effective-domain owner for `EReal`-valued functions.

Best owner abstraction:
- source-facing: `fenchelBidual`, written `f⋆⋆`;
- core/canonical: `fenchelConjugate`;
- bridge/view: evaluate `fenchelConjugate (f⋆)` along the Riesz map `innerₗ E`.

Primitive data:
- `f : E → WithTop ℝ`;
- the source-facing dual owner `f⋆`;
- the subdifferential owner `∂ f(x)`.

Derived API:
- the source-facing notation `f⋆⋆`;
- the unrestricted conjugate expansion of `(f⋆⋆) x`;
- the bridge theorem restricting that supremum to `dom (f⋆)` when `(dom f).Nonempty`;
- the three textbook theorem declarations on that notation surface.

Source/core/bridge triage:
- source-facing: Theorem 3.1.5.2's Fenchel-biconjugacy statements;
- core/canonical: `fenchelConjugate`;
- bridge/view: the bidual owner `fenchelBidual`, which packages the second Fenchel conjugate on
  the same source-facing inner-product-space surface.
-/

/-- The Fenchel bidual of an `ℝ ∪ {+∞}`-valued function on a real inner-product space. -/
abbrev fenchelBidual (f : E → WithTop ℝ) : E → EReal :=
  fenchelConjugate (f⋆) ∘ innerₗ E

/- Lean spelling `f⋆⋆` for the source-facing Fenchel bidual `fenchelBidual f`. -/
scoped[ConvexAnalysis] postfix:max "⋆⋆" => fenchelBidual

/-- Evaluating `fenchelBidual f` gives the unrestricted Fenchel-conjugate supremum formula. -/
theorem fenchelBidual_apply (f : E → WithTop ℝ) (x : E) :
    (f⋆⋆) x = ⨆ s : E, (inner ℝ s x : EReal) - (f⋆) s := by
  simpa [fenchelBidual, innerₗ_apply_apply, real_inner_comm] using
    fenchelConjugate_apply (f⋆) (innerₗ E x)

section

variable {f : E → WithTop ℝ}

/-- Helper for Theorem 3.1.5.2: on the effective domain of `f`, the `EReal` image of `f` is the
corresponding finite real value. -/
lemma withTopToEReal_eq_coe_withTopRealPart_of_mem_dom {y : E} (hy : y ∈ dom f) :
    withTopToEReal (f y) = (withTopRealPart f y : EReal) := by
  -- On `dom f`, coercing the finite real part back to `EReal` recovers the original value.
  simpa [withTopToEReal] using (congrArg withTopToEReal (coe_withTopRealPart hy)).symm

/-- Helper for Theorem 3.1.5.2: at a finite primal point, the `EReal` image of `f` is not
`⊤`. -/
lemma withTopToEReal_ne_top_of_mem_dom {y : E} (hy : y ∈ dom f) :
    withTopToEReal (f y) ≠ ⊤ := by
  rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy]
  exact EReal.coe_ne_top _

/-- Helper for Theorem 3.1.5.2: at a finite primal point, the `EReal` image of `f` is not
`⊥`. -/
lemma withTopToEReal_ne_bot_of_mem_dom {y : E} (hy : y ∈ dom f) :
    withTopToEReal (f y) ≠ ⊥ := by
  rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy]
  exact EReal.coe_ne_bot _

/-- Helper for Theorem 3.1.5.2: testing the Fenchel-dual supremum at a finite primal point gives
the canonical affine lower bound. -/
lemma fenchelDual_lower_bound_of_mem_dom {s y : E} (hy : y ∈ dom f) :
    (inner ℝ s y : EReal) - withTopToEReal (f y) ≤ (f⋆) s := by
  -- The point `y` is one admissible index in the domain-restricted supremum formula for `f⋆`.
  rw [fenchelDual_apply_eq_sSup_image_dom]
  exact le_sSup ⟨y, hy, rfl⟩

/-- Helper for Theorem 3.1.5.2: a finite primal point prevents the Fenchel dual from taking the
value `⊥`. -/
lemma fenchelDual_ne_bot_of_mem_dom {s y : E} (hy : y ∈ dom f) :
    (f⋆) s ≠ ⊥ := by
  -- Compare `f⋆ s` with the finite affine term contributed by `y`.
  have hlower := fenchelDual_lower_bound_of_mem_dom (f := f) (s := s) hy
  have hfinite : (⊥ : EReal) < (inner ℝ s y : EReal) - withTopToEReal (f y) := by
    rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy, ← EReal.coe_sub]
    exact EReal.bot_lt_coe _
  intro hbot
  rw [hbot] at hlower
  exact (not_lt_of_ge hlower) hfinite

/-- Helper for Theorem 3.1.5.2: once `dom f` is nonempty, any point outside `dom (f⋆)` contributes
`⊥` to the bidual maximand. -/
lemma fenchelBidual_maximand_eq_bot_of_not_mem_dom
    (hdom : (dom f).Nonempty) {s x : E} (hs : s ∉ dom (f⋆)) :
    ((inner ℝ s x : EReal) - (f⋆) s) = ⊥ := by
  -- A finite primal witness rules out `(f⋆) s = ⊥`, so outside `dom (f⋆)` the only remaining
  -- possibility is `(f⋆) s = ⊤`.
  rcases hdom with ⟨y, hy⟩
  have hdual_ne_bot : (f⋆) s ≠ ⊥ := fenchelDual_ne_bot_of_mem_dom (f := f) (s := s) hy
  have hs_top : (f⋆) s = ⊤ := by
    by_contra hs_ne_top
    exact hs ((mem_extendedRealEffectiveDomain_iff).2 ⟨hs_ne_top, hdual_ne_bot⟩)
  rw [hs_top, EReal.sub_top]

/-- Helper for Theorem 3.1.5.2: after discarding the `⊥` terms, the bidual supremum is indexed by
`dom (f⋆)`. -/
lemma iSup_fenchelBidual_maximand_eq_iSup_dom
    (hdom : (dom f).Nonempty) (x : E) :
    (⨆ s : E, (inner ℝ s x : EReal) - (f⋆) s) =
      ⨆ s : dom (f⋆), (inner ℝ s.1 x : EReal) - (f⋆) s.1 := by
  refine le_antisymm ?_ ?_
  · -- Every unrestricted term either comes from `dom (f⋆)` or is `⊥` outside that domain.
    refine iSup_le ?_
    intro s
    by_cases hs : s ∈ dom (f⋆)
    · exact le_iSup (fun t : dom (f⋆) ↦ (inner ℝ t.1 x : EReal) - (f⋆) t.1) ⟨s, hs⟩
    · rw [fenchelBidual_maximand_eq_bot_of_not_mem_dom (f := f) hdom hs]
      exact bot_le
  · -- Any point of `dom (f⋆)` is also an index in the unrestricted supremum.
    refine iSup_le ?_
    intro s
    exact le_iSup (fun t : E ↦ (inner ℝ t x : EReal) - (f⋆) t) s.1

-- Proof sketch: expand `fenchelBidual_apply`. If `dom f` is nonempty, then for every `s` the
-- term `(f⋆) s` is bounded below by one finite affine value, so `(f⋆) s ≠ ⊥`; points outside
-- `dom (f⋆)` therefore contribute only `⊥`, and the supremum may be restricted to `dom (f⋆)`.
/-- If `f` has a finite value somewhere, then the Fenchel-bidual supremum may be restricted to the
effective domain of the Fenchel dual. -/
theorem fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty
    (hdom : (dom f).Nonempty) (x : E) :
    (f⋆⋆) x =
      sSup ((fun s : E ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆)) := by
  calc
    (f⋆⋆) x = ⨆ s : E, (inner ℝ s x : EReal) - (f⋆) s := by
      -- Start from the unrestricted Fenchel-conjugate formula for the bidual.
      rw [fenchelBidual_apply]
    _ = ⨆ s : dom (f⋆), (inner ℝ s.1 x : EReal) - (f⋆) s.1 := by
      -- Restrict to `dom (f⋆)` because the complementary terms are `⊥`.
      rw [iSup_fenchelBidual_maximand_eq_iSup_dom (f := f) hdom x]
    _ = sSup (Set.range fun s : dom (f⋆) ↦ (inner ℝ s.1 x : EReal) - (f⋆) s.1) := by
      -- Convert the subtype-indexed supremum into the supremum over its range.
      rw [sSup_range]
    _ = sSup ((fun s : E ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆)) := by
      -- Identify the subtype range with the image of the maximand on `dom (f⋆)`.
      congr 1
      ext z
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨s.1, s.2, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hs⟩, rfl⟩

section

variable {x : E}

-- Proof sketch: use `fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty ⟨x, hx⟩` to rewrite
-- `(f⋆⋆) x` as the supremum over `dom (f⋆)` of the affine terms `⟪s, x⟫ - f⋆(s)`, then expand
-- `f⋆(s)` as a supremum over `dom f` and test the defining supremum at `y = x`.
/-- Theorem 3.1.5.2 (1): for every `x ∈ dom f`, the Fenchel bidual is bounded above by the
original value `f x`. -/
theorem fenchelBidual_le_of_mem_dom
    (hx : x ∈ dom f) :
    (f⋆⋆) x ≤ withTopToEReal (f x) := by
  -- Rewrite the bidual as the supremum of the dual support terms over `dom (f⋆)`.
  rw [fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty (f := f) ⟨x, hx⟩ x]
  refine sSup_le ?_
  rintro z ⟨s, hs, rfl⟩
  have hs_mem := mem_extendedRealEffectiveDomain_iff.mp hs
  have hsum : (inner ℝ s x : EReal) ≤ (f⋆) s + withTopToEReal (f x) := by
    -- Test the defining supremum of `f⋆ s` at the concrete primal point `x`.
    have hlower := fenchelDual_lower_bound_of_mem_dom (f := f) (s := s) hx
    exact (EReal.sub_le_iff_le_add (.inl (withTopToEReal_ne_bot_of_mem_dom (f := f) hx))
      (.inl (withTopToEReal_ne_top_of_mem_dom (f := f) hx))).1 hlower
  -- Rearranging that bound yields the desired estimate for this support term.
  exact EReal.sub_le_of_le_add' hsum

/-- Helper for Theorem 3.1.5.2: the subgradient inequality gives the standard upper bound on the
Fenchel dual at the subgradient. -/
lemma fenchelDual_le_subgradient_support_value {x g : E}
    (hg : g ∈ ∂ f(x)) :
    (f⋆) g ≤ (inner ℝ g x : EReal) - withTopToEReal (f x) := by
  have hsub : IsSubgradientAt f x g := mem_subdifferential_iff.mp hg
  have hx : x ∈ dom f := hsub.mem_dom
  rw [fenchelDual_apply_eq_sSup_image_dom]
  refine sSup_le ?_
  rintro z ⟨y, hy, rfl⟩
  have hineq : f y ≥ f x + (inner ℝ g (y - x) : WithTop ℝ) := hsub.2 hy
  have hineq_real : withTopRealPart f y ≥ withTopRealPart f x + inner ℝ g (y - x) := by
    -- On `dom f`, the `WithTop` inequality is an ordinary real inequality.
    have hineq' :
        (((withTopRealPart f y : ℝ) : WithTop ℝ) ≥
          ((withTopRealPart f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ)) := by
      rw [WithTop.coe_add, coe_withTopRealPart hy, coe_withTopRealPart hx]
      simpa [ge_iff_le] using hineq
    exact_mod_cast hineq'
  have hinner : inner ℝ g y = inner ℝ g x + inner ℝ g (y - x) := by
    -- Expand `⟪g, y⟫` along the decomposition `y = x + (y - x)`.
    calc
      inner ℝ g y = inner ℝ g (x + (y - x)) := by simp
      _ = inner ℝ g x + inner ℝ g (y - x) := by rw [inner_add_right]
  have hreal : inner ℝ g y - withTopRealPart f y ≤ inner ℝ g x - withTopRealPart f x := by
    -- After moving to real coordinates, the subgradient inequality is exactly the desired bound.
    linarith
  -- Re-express both finite function values as real coefficients in `EReal`.
  simpa only [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hx,
    withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy,
    ← EReal.coe_sub] using (show
      ((inner ℝ g y - withTopRealPart f y : ℝ) : EReal) ≤
        ((inner ℝ g x - withTopRealPart f x : ℝ) : EReal) from by
      exact_mod_cast hreal)

-- Proof sketch: for any `g ∈ ∂ f(x)`, the subgradient inequality bounds every term
-- `⟪g, y⟫ - f y` by `⟪g, x⟫ - f x`, so the supremum defining `(f⋆) g` is finite and therefore
-- `g ∈ dom (f⋆)`.
/-- Theorem 3.1.5.2 (2): every subgradient at `x` belongs to the effective domain of the
Fenchel dual. -/
theorem subdifferential_subset_dom_fenchelDual :
    ∂ f(x) ⊆ dom (f⋆) := by
  intro g hg
  have hsub : IsSubgradientAt f x g := mem_subdifferential_iff.mp hg
  have hx : x ∈ dom f := hsub.mem_dom
  have hdual_ne_bot : (f⋆) g ≠ ⊥ := fenchelDual_ne_bot_of_mem_dom (f := f) (s := g) hx
  have hdual_le := fenchelDual_le_subgradient_support_value (f := f) (x := x) hg
  have hsupport_ne_top : ((inner ℝ g x : EReal) - withTopToEReal (f x)) ≠ ⊤ := by
    -- The support value is finite because `x ∈ dom f`.
    rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hx, ← EReal.coe_sub]
    exact EReal.coe_ne_top _
  have hdual_ne_top : (f⋆) g ≠ ⊤ := by
    -- A value bounded above by a finite support term cannot be `⊤`.
    exact ne_of_lt (lt_of_le_of_lt hdual_le (lt_top_iff_ne_top.mpr hsupport_ne_top))
  exact (mem_extendedRealEffectiveDomain_iff).2 ⟨hdual_ne_top, hdual_ne_bot⟩

/-- Helper for Theorem 3.1.5.2: a subgradient witness gives the reverse support inequality needed
for the bidual equality. -/
lemma subgradient_support_term_ge_value {x g : E}
    (hg : g ∈ ∂ f(x)) :
    withTopToEReal (f x) ≤ (inner ℝ g x : EReal) - (f⋆) g := by
  have hsub : IsSubgradientAt f x g := mem_subdifferential_iff.mp hg
  have hx : x ∈ dom f := hsub.mem_dom
  have hg_dom : g ∈ dom (f⋆) := subdifferential_subset_dom_fenchelDual (f := f) (x := x) hg
  have hg_mem := mem_extendedRealEffectiveDomain_iff.mp hg_dom
  have hsupport := fenchelDual_le_subgradient_support_value (f := f) (x := x) hg
  -- Convert the upper bound on `f⋆ g` into the corresponding lower bound on the support term.
  rw [EReal.le_sub_iff_add_le (.inl hg_mem.2) (.inr (EReal.coe_ne_top _))]
  rw [EReal.le_sub_iff_add_le (.inl (withTopToEReal_ne_bot_of_mem_dom (f := f) hx))
    (.inl (withTopToEReal_ne_top_of_mem_dom (f := f) hx))] at hsupport
  simpa [add_comm] using hsupport

-- Proof sketch: part (1) gives `(f⋆⋆) x ≤ f x`. For any `g ∈ ∂ f(x)`, part (2) shows
-- `g ∈ dom (f⋆)`, and the subgradient inequality yields the reverse bound
-- `withTopToEReal (f x) ≤ (inner ℝ g x : EReal) - (f⋆) g ≤ (f⋆⋆) x`.
/-- Theorem 3.1.5.2 (3): if the subdifferential at `x` is nonempty, then the Fenchel bidual
agrees with the original value at `x`. -/
theorem fenchelBidual_eq_of_subdifferential_nonempty
    (hsub : (∂ f(x)).Nonempty) :
    (f⋆⋆) x = withTopToEReal (f x) := by
  rcases hsub with ⟨g, hg⟩
  have hx : x ∈ dom f := (mem_subdifferential_iff.mp hg).mem_dom
  have hupper : (f⋆⋆) x ≤ withTopToEReal (f x) := fenchelBidual_le_of_mem_dom (f := f) hx
  have hg_dom : g ∈ dom (f⋆) := subdifferential_subset_dom_fenchelDual (f := f) (x := x) hg
  have hsupport : withTopToEReal (f x) ≤ (inner ℝ g x : EReal) - (f⋆) g :=
    subgradient_support_term_ge_value (f := f) (x := x) hg
  have hterm : (inner ℝ g x : EReal) - (f⋆) g ≤ (f⋆⋆) x := by
    -- The subgradient witness contributes one admissible term to the bidual supremum.
    rw [fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty (f := f) ⟨x, hx⟩ x]
    exact le_sSup ⟨g, hg_dom, rfl⟩
  exact le_antisymm hupper (hsupport.trans hterm)

end

end

end
