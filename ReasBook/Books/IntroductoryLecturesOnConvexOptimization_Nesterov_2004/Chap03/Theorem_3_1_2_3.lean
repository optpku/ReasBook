/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped ConvexAnalysis

variable {X : Type u} {Y : Type v}

/- Theorem 3.1.2.3 lies in the chapter's convex-analysis / infimal-projection domain.

Sampled owner-style declarations:
- chapter `extendedRealEffectiveDomain` / notation `dom` in `Definition_3_1_1_2`
- chapter `extendedRealRealPart` and `coe_extendedRealRealPart` in `Definition_3_1_1_3`
- mathlib `ConvexOn`
- mathlib `sInf`

Best owner abstraction:
- source-facing owner: the constrained `EReal`-valued fiberwise infimum `partialInfProjection`
- core/canonical convexity owner:
  `ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ)` for `ψ = partialInfProjection Q φ`

Primitive data:
- a feasible set `Q : Set (X × Y)`
- an extended-real objective `φ : X × Y → EReal`

Derived API:
- the source-facing constrained infimum `partialInfProjection Q φ`
- the displayed fiber-value specification theorem `partialInfProjection_eq_sInf`
- the finite-value bridge
  `extendedRealRealPart_partialInfProjection_eq_sInf`

Source/core/bridge triage:
- source-facing: the constrained fiberwise infimum over `Q`
- core/canonical: the chapter `EReal` convexity owner
  `ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ)`
- bridge/view: the finite-value real surface
  `extendedRealRealPart (partialInfProjection Q φ)`

A `WithTop ℝ`-valued owner would not faithfully represent unbounded-below fibers, so this file
keeps the constrained source-facing owner directly in `EReal` and then uses the chapter's
canonical `EReal` convexity bridge on its finite-value domain.
-/

/-- The constrained partial infimum of `φ` over the fiber of `Q` above `x`, recorded in `EReal`
so that unbounded-below fibers are represented faithfully by `⊥`. -/
def partialInfProjection (Q : Set (X × Y)) (φ : X × Y → EReal) : X → EReal :=
  fun x ↦ sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x})

/-- Evaluating the constrained partial infimum gives the infimum of the `φ`-values attained on
the feasible fiber above `x`. -/
@[simp] theorem partialInfProjection_eq_sInf
    {Q : Set (X × Y)} {φ : X × Y → EReal} {x : X} :
    partialInfProjection Q φ x =
      sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}) :=
  rfl

/-- Helper for Theorem 3.1.2.3: a finite constrained partial infimum comes from a nonempty fiber
whose real values are bounded below. -/
lemma fiber_value_set_nonempty_bddBelow_of_mem_dom
    {Q : Set (X × Y)} {φ : X × Y → ℝ} {x : X}
    (hx : x ∈ dom (partialInfProjection Q (Real.toEReal ∘ φ))) :
    (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}).Nonempty ∧
      BddBelow (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}) := by
  let S : Set ℝ := φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}
  have hx_finite := mem_extendedRealEffectiveDomain_iff.mp hx
  constructor
  · -- An empty fiber would force the infimum to be `⊤`, contradicting finiteness.
    by_contra hS_nonempty
    have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS_nonempty
    have htop : partialInfProjection Q (Real.toEReal ∘ φ) x = ⊤ := by
      rw [partialInfProjection_eq_sInf]
      simp [S, hS_empty, ← Set.image_image]
    exact hx_finite.1 htop
  · -- If the real fiber values were not bounded below, the extended-real infimum would be `⊥`.
    by_contra hS_bddBelow
    have hbot : partialInfProjection Q (Real.toEReal ∘ φ) x = ⊥ := by
      apply (EReal.eq_bot_iff_forall_lt _).2
      intro y
      rw [partialInfProjection_eq_sInf]
      have hy : ∃ z ∈ S, z < y := by
        by_contra hy_not
        apply hS_bddBelow
        refine ⟨y, ?_⟩
        intro z hz
        by_contra hyz
        exact hy_not ⟨z, hz, lt_of_not_ge hyz⟩
      rcases hy with ⟨z, hzS, hzy⟩
      have hzmem : (z : EReal) ∈ Real.toEReal '' S := ⟨z, hzS, rfl⟩
      have hsInf_lt : sInf (Real.toEReal '' S) < (y : EReal) := by
        exact lt_of_le_of_lt (sInf_le hzmem) (by exact_mod_cast hzy)
      simpa [S, ← Set.image_image] using hsInf_lt
    exact hx_finite.2 hbot

/-- At a point where the constrained partial infimum is finite, its canonical real part agrees
with the textbook infimum of the real fiber values. -/
theorem extendedRealRealPart_partialInfProjection_eq_sInf
    {Q : Set (X × Y)} {φ : X × Y → ℝ} {x : X}
    (hx : x ∈ dom (partialInfProjection Q (Real.toEReal ∘ φ))) :
    extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ)) x =
      sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}) := by
  let S : Set ℝ := φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}
  obtain ⟨hS_nonempty, hS_bddBelow⟩ :=
    fiber_value_set_nonempty_bddBelow_of_mem_dom hx
  -- Transport the real infimum across the order embedding `ℝ ↪ EReal`.
  have hS_glb : IsGLB S (sInf S) := Real.isGLB_sInf hS_nonempty hS_bddBelow
  have hS_glb' : IsGLB (Real.toEReal '' S) ((sInf S : ℝ) : EReal) := by
    refine ⟨?_, ?_⟩
    · rintro z ⟨y, hy, rfl⟩
      exact_mod_cast hS_glb.1 hy
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          rcases hS_nonempty with ⟨y, hy⟩
          have hz_le : z ≤ (y : EReal) := hz ⟨y, hy, rfl⟩
          intro hz_eq_top
          rw [hz_eq_top] at hz_le
          simp at hz_le
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with z_real
        have hz_real : ∀ y ∈ S, z_real ≤ y := by
          intro y hy
          exact_mod_cast (hz ⟨y, hy, rfl⟩)
        exact_mod_cast hS_glb.2 hz_real
  have hψ :
      partialInfProjection Q (Real.toEReal ∘ φ) x = ((sInf S : ℝ) : EReal) := by
    rw [partialInfProjection_eq_sInf]
    calc
      sInf ((Real.toEReal ∘ φ) '' {z : X × Y | z ∈ Q ∧ z.1 = x}) =
          sInf (Real.toEReal '' S) := by
            simp [S, ← Set.image_image]
      _ = ((sInf S : ℝ) : EReal) := by
            exact hS_glb'.csInf_eq (hS_nonempty.image Real.toEReal)
  -- Read the `EReal` identity back through the chapter real-part bridge.
  apply EReal.coe_injective
  calc
    (((extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ)) x : ℝ) : EReal)) =
        partialInfProjection Q (Real.toEReal ∘ φ) x :=
      coe_extendedRealRealPart hx
    _ = ((sInf S : ℝ) : EReal) := hψ
    _ = (((sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}) : ℝ) : ℝ) : EReal) := by
      simp [S]

/-- Helper for Theorem 3.1.2.3: every finite fiber infimum admits a feasible point whose value is
within `ε` of the fiberwise infimum. -/
lemma exists_fiber_value_lt_sInf_add
    {Q : Set (X × Y)} {φ : X × Y → ℝ} {x : X} {ε : ℝ}
    (hx : x ∈ dom (partialInfProjection Q (Real.toEReal ∘ φ))) (hε : 0 < ε) :
    ∃ z : X × Y, z ∈ Q ∧ z.1 = x ∧
      φ z < sInf (φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}) + ε := by
  let S : Set ℝ := φ '' {z : X × Y | z ∈ Q ∧ z.1 = x}
  obtain ⟨hS_nonempty, -⟩ :=
    fiber_value_set_nonempty_bddBelow_of_mem_dom hx
  -- Choose a fiber value strictly below the infimum plus `ε`.
  obtain ⟨r, hrS, hrlt⟩ := exists_lt_of_csInf_lt hS_nonempty (lt_add_of_pos_right (sInf S) hε)
  rcases hrS with ⟨z, hz, rfl⟩
  exact ⟨z, hz.1, hz.2, by simpa [S] using hrlt⟩

section RealConvex

variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]

/-- Helper for Theorem 3.1.2.3: once the convex-combination point already lies in the finite-value
domain, the textbook near-minimizer argument gives the Jensen inequality for the partial infimum. -/
lemma partialInfProjection_jensen_of_mem_dom
    {Q : Set (X × Y)} {φ : X × Y → ℝ}
    (hQ : Convex ℝ Q) (hφ : ConvexOn ℝ Q φ)
    {x y : X} {a b : ℝ}
    (hx : x ∈ dom (partialInfProjection Q (Real.toEReal ∘ φ)))
    (hy : y ∈ dom (partialInfProjection Q (Real.toEReal ∘ φ)))
    (hz : a • x + b • y ∈ dom (partialInfProjection Q (Real.toEReal ∘ φ)))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ)) (a • x + b • y) ≤
      a * extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ)) x +
        b * extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ φ)) y := by
  let ψ : X → EReal := partialInfProjection Q (Real.toEReal ∘ φ)
  let z : X := a • x + b • y
  -- Work with an arbitrary `ε > 0`, build approximate minimizers at the endpoints, and then
  -- remove `ε` at the end.
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨zx, hzxQ, hzx1, hzxlt⟩ :=
    exists_fiber_value_lt_sInf_add hx hε
  obtain ⟨zy, hzyQ, hzy1, hzylt⟩ :=
    exists_fiber_value_lt_sInf_add hy hε
  let mz : X × Y := a • zx + b • zy
  have hmQ : mz ∈ Q := by
    dsimp [mz]
    exact hQ hzxQ hzyQ ha hb hab
  have hm1 : mz.1 = z := by
    dsimp [mz, z]
    simp [hzx1, hzy1]
  have hψ_le : ψ z ≤ (φ mz : EReal) := by
    -- The convex combination of the two near minimizers is a feasible candidate above `z`.
    dsimp [ψ, z, mz]
    exact sInf_le ⟨a • zx + b • zy, ⟨hmQ, hm1⟩, rfl⟩
  have hφ_le : φ mz ≤ a * φ zx + b * φ zy := by
    -- Convexity of `φ` gives the key Jensen step on the product space.
    dsimp [mz]
    simpa [smul_eq_mul] using hφ.2 hzxQ hzyQ ha hb hab
  have hx_mul :
      a * φ zx ≤ a * (sInf (φ '' {w : X × Y | w ∈ Q ∧ w.1 = x}) + ε) := by
    exact mul_le_mul_of_nonneg_left hzxlt.le ha
  have hy_mul :
      b * φ zy ≤ b * (sInf (φ '' {w : X × Y | w ∈ Q ∧ w.1 = y}) + ε) := by
    exact mul_le_mul_of_nonneg_left hzylt.le hb
  have hmid_le :
      ψ z ≤
        ((a * extendedRealRealPart ψ x + b * extendedRealRealPart ψ y + ε : ℝ) : EReal) := by
    calc
      ψ z ≤ (φ mz : EReal) := hψ_le
      _ ≤ ((a * φ zx + b * φ zy : ℝ) : EReal) := by
            exact_mod_cast hφ_le
      _ ≤ ((a * (sInf (φ '' {w : X × Y | w ∈ Q ∧ w.1 = x}) + ε) +
            b * (sInf (φ '' {w : X × Y | w ∈ Q ∧ w.1 = y}) + ε) : ℝ) : EReal) := by
            exact_mod_cast (add_le_add hx_mul hy_mul)
      _ = ((a * extendedRealRealPart ψ x + b * extendedRealRealPart ψ y + ε : ℝ) : EReal) := by
            rw [extendedRealRealPart_partialInfProjection_eq_sInf hx,
              extendedRealRealPart_partialInfProjection_eq_sInf hy]
            congr 1
            ring_nf
            nlinarith [hab]
  -- Translate the `EReal` estimate back to the finite real part at the midpoint.
  simpa [ψ, z] using (extendedRealRealPart_le_iff hz).2 hmid_le

omit [AddCommMonoid X] [Module ℝ X] [AddCommMonoid Y] [Module ℝ Y] in
/-- Helper for Theorem 3.1.2.3: a finite constrained partial infimum must come from a nonempty
feasible fiber. -/
lemma exists_feasible_of_mem_dom_partialInfProjection
    {Q : Set (X × Y)} {φ : X × Y → EReal} {x : X}
    (hx : x ∈ dom (partialInfProjection Q φ)) :
    ∃ y : Y, (x, y) ∈ Q := by
  -- An empty feasible fiber would make the constrained infimum equal to `⊤`.
  by_contra hfeasible
  have hfiber_empty : {z : X × Y | z ∈ Q ∧ z.1 = x} = ∅ := by
    ext z
    rcases z with ⟨zx, zy⟩
    constructor
    · intro hz
      have hzQ : (x, zy) ∈ Q := by
        rw [← hz.2]
        exact hz.1
      exact False.elim <| hfeasible ⟨zy, hzQ⟩
    · intro hz
      simp at hz
  have htop : partialInfProjection Q φ x = ⊤ := by
    rw [partialInfProjection_eq_sInf]
    simp [hfiber_empty]
  exact (mem_extendedRealEffectiveDomain_iff.mp hx).1 htop

omit [AddCommMonoid X] [Module ℝ X] [AddCommMonoid Y] [Module ℝ Y] in
/-- Helper for Theorem 3.1.2.3: on `Q`, the `EReal` objective agrees with the canonical
real-part model `Real.toEReal ∘ extendedRealRealPart φ`. -/
lemma partialInfProjection_eq_toEReal_extendedRealRealPart
    {Q : Set (X × Y)} {φ : X × Y → EReal}
    (hQdom : Q ⊆ dom φ) :
    partialInfProjection Q φ =
      partialInfProjection Q (Real.toEReal ∘ extendedRealRealPart φ) := by
  -- Compare the two fiber image sets pointwise; `Q ⊆ dom φ` makes every feasible value finite.
  funext x
  rw [partialInfProjection_eq_sInf, partialInfProjection_eq_sInf]
  congr 1
  ext a
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    simpa using (coe_extendedRealRealPart (f := φ) (x := z) (hQdom hz.1))
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    simpa using (coe_extendedRealRealPart (f := φ) (x := z) (hQdom hz.1)).symm

/-- Helper for Theorem 3.1.2.3: if every feasible fiber has finite constrained infimum, then the
effective domain of the constrained partial infimum is convex. -/
lemma convex_dom_partialInfProjection
    {Q : Set (X × Y)} {φ : X × Y → EReal}
    (hQ : Convex ℝ Q)
    (hfinite :
      ∀ ⦃x : X⦄, (∃ y : Y, (x, y) ∈ Q) →
        x ∈ dom (partialInfProjection Q φ)) :
    Convex ℝ (dom (partialInfProjection Q φ)) := by
  -- Domain membership gives feasible endpoint fibers, and convexity of `Q` propagates them.
  intro x hx y hy a b ha hb hab
  rcases exists_feasible_of_mem_dom_partialInfProjection (Q := Q) (φ := φ) hx with ⟨yx, hyx⟩
  rcases exists_feasible_of_mem_dom_partialInfProjection (Q := Q) (φ := φ) hy with ⟨yy, hyy⟩
  apply hfinite
  refine ⟨a • yx + b • yy, ?_⟩
  simpa using hQ hyx hyy ha hb hab

/-- Theorem 3.1.2.3: if `Q ⊆ X × Y` is convex and `φ : X × Y → EReal` is convex on its effective
domain with `Q ⊆ dom φ`, and every feasible fiber of the constrained partial infimum has a finite
infimum, then the constrained partial infimum is convex in the chapter's `EReal` sense: its
finite real part is convex on its finite-value domain. The hypothesis `Q ⊆ dom φ` restores the
source-side input surface `φ : ℝⁿ × ℝᵐ → ℝ ∪ {+∞}`, while the extra finite-fiber hypothesis is
the Lean rendering of the source conclusion `f : \hat Q → ℝ ∪ {+∞}`, which rules out `-∞` values
on feasible fibers. -/
theorem partialInfProjection_convexOn
    {Q : Set (X × Y)} {φ : X × Y → EReal}
    (hQ : Convex ℝ Q)
    (hφ : ConvexOn ℝ (dom φ) (extendedRealRealPart φ))
    (hQdom : Q ⊆ dom φ)
    (hfinite :
      ∀ ⦃x : X⦄, (∃ y : Y, (x, y) ∈ Q) →
        x ∈ dom (partialInfProjection Q φ)) :
    ConvexOn ℝ (dom (partialInfProjection Q φ))
      (extendedRealRealPart (partialInfProjection Q φ)) := by
  have hproj_eq :
      partialInfProjection Q φ =
        partialInfProjection Q (Real.toEReal ∘ extendedRealRealPart φ) :=
    partialInfProjection_eq_toEReal_extendedRealRealPart (Q := Q) (φ := φ) hQdom
  have hdom_conv : Convex ℝ (dom (partialInfProjection Q φ)) :=
    convex_dom_partialInfProjection (Q := Q) (φ := φ) hQ hfinite
  have hφQ : ConvexOn ℝ Q (extendedRealRealPart φ) := hφ.subset hQdom hQ
  refine ⟨hdom_conv, ?_⟩
  intro x hx y hy a b ha hb hab
  -- The convexity of the effective domain supplies the midpoint finiteness needed for Jensen.
  have hz : a • x + b • y ∈ dom (partialInfProjection Q φ) := hdom_conv hx hy ha hb hab
  have hx' : x ∈ dom (partialInfProjection Q (Real.toEReal ∘ extendedRealRealPart φ)) := by
    simpa [hproj_eq] using hx
  have hy' : y ∈ dom (partialInfProjection Q (Real.toEReal ∘ extendedRealRealPart φ)) := by
    simpa [hproj_eq] using hy
  have hz' :
      a • x + b • y ∈ dom (partialInfProjection Q (Real.toEReal ∘ extendedRealRealPart φ)) := by
    simpa [hproj_eq] using hz
  -- Normalize to the finite real-part model on `Q` and reuse the existing real-valued Jensen step.
  simpa [hproj_eq] using
    (partialInfProjection_jensen_of_mem_dom
      (Q := Q) (φ := extendedRealRealPart φ) hQ hφQ hx' hy' hz' ha hb hab)

end RealConvex

end
