/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped ConvexAnalysis

variable {X : Type u} {Y : Type v}

/- Theorem 3.30 lies in the chapter's infimal-projection / extended-real approximation domain.

Sampled owner-style declarations:
- chapter `partialInfProjection` in `Theorem_3_1_2_3`
- chapter `partialInfProjection_eq_sInf` in `Theorem_3_1_2_3`
- chapter `extendedRealRealPart_le_iff` in `Definition_3_1_1_3`
- mathlib `sInf`

Best owner abstraction:
- core/canonical owner: `partialInfProjection (Q := Set.univ)` for an unconstrained fiberwise
  infimum, valued in `EReal`
- source-facing theorem surface: the order comparison
  `partialInfProjection Set.univ F x ≤ (level : EReal)`
- finite-value bridge surface:
  `{x ∈ dom (partialInfProjection Set.univ F) | partialInfProjection Set.univ F x ≤ level}`

Primitive data:
- an extended-real objective `F : X × Y → EReal`

Derived API:
- the faithful set-level `EReal` sublevel characterization for the unconstrained infimal
  projection
- its pointwise reformulation
- the secondary finite-value bridge theorem on `dom (partialInfProjection Set.univ F)`

Source/core/bridge triage:
- source-facing: the approximation formula for the unconstrained infimal projection at the
  `EReal` order level
- core/canonical: `partialInfProjection` together with the order relation
  `partialInfProjection Set.univ F x ≤ (level : EReal)`
- bridge/view: intersecting with `dom` to recover the finite-value real sublevel surface

The earlier `dom`-cut theorem excluded fibers where `partialInfProjection Set.univ F = ⊥`, so it
was only a finite-value bridge and not the faithful main statement. This file restores the
canonical `EReal` order theorem as the main public entry and keeps the finite-value
`dom`-intersected reformulation only as a secondary bridge.
-/

/-- Helper for Theorem 3.30: the unconstrained partial infimal projection is bounded above by
every slice value. -/
lemma partialInfProjection_univ_le_slice
    (F : X × Y → EReal) (x : X) (y : Y) :
    partialInfProjection Set.univ F x ≤ F (x, y) := by
  -- Rewrite the unconstrained partial infimal projection as the infimum over the fiber above `x`.
  rw [partialInfProjection_eq_sInf]
  refine sInf_le ?_
  exact Set.mem_image_of_mem F ⟨by simp, rfl⟩

/-- Helper for Theorem 3.30: a real upper bound on a slice value upgrades a witness from the
effective domain of the infimal projection to the effective domain of that slice. -/
lemma slice_mem_dom_of_partialInfProjection_mem_dom_of_le_real
    {F : X × Y → EReal} {x : X} {y : Y} {r : ℝ}
    (hx : x ∈ dom (partialInfProjection Set.univ F))
    (hxy : F (x, y) ≤ (r : EReal)) :
    x ∈ dom (fun x : X ↦ F (x, y)) := by
  -- Show directly that the slice value is neither `⊤` nor `⊥`.
  rw [mem_extendedRealEffectiveDomain_iff]
  rcases mem_extendedRealEffectiveDomain_iff.mp hx with ⟨_, hproj_ne_bot⟩
  refine ⟨?_, ?_⟩
  · intro htop
    simp [htop] at hxy
  · intro hbot
    have hproj_le_bot : partialInfProjection Set.univ F x ≤ (⊥ : EReal) := by
      simpa [hbot] using partialInfProjection_univ_le_slice F x y
    exact hproj_ne_bot (le_antisymm hproj_le_bot bot_le)

/-- Theorem 3.30: the unconstrained infimal projection lies below the real level `λ` exactly on
the intersection, over all `ε > 0`, of the unions of the `(λ + ε)`-sublevel sets of the slices
`x ↦ F (x, y)`. This faithful `EReal` statement also covers fibers where the infimal projection
equals `⊥`. -/
theorem partialInfProjection_univ_sublevelSet_eq_iInter_iUnion
    (F : X × Y → EReal) (level : ℝ) :
    {x | partialInfProjection Set.univ F x ≤ (level : EReal)} =
      ⋂ ε > 0, ⋃ y : Y, {x | F (x, y) ≤ (level + ε : EReal)} := by
  ext x
  -- Evaluate the set identity at `x` so the goal becomes the textbook pointwise approximation
  -- formula.
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · intro hx ε hε
    -- Move from `partialInfProjection ≤ level` to a strict bound by `level + ε`, then extract a
    -- witness from the fiber infimum.
    by_cases hε_top : ε = ⊤
    · have hxpp : partialInfProjection Set.univ F x ≤ (level : EReal) := by
        simpa [partialInfProjection_eq_sInf] using hx
      have hproj_ne_top : partialInfProjection Set.univ F x ≠ ⊤ := by
        intro htop
        have hxpp' := hxpp
        rw [htop] at hxpp'
        simp at hxpp'
      have hlt : partialInfProjection Set.univ F x < (⊤ : EReal) :=
        lt_top_iff_ne_top.mpr hproj_ne_top
      rw [partialInfProjection_eq_sInf] at hlt
      rcases sInf_lt_iff.mp hlt with ⟨a, ha, ha_lt⟩
      rcases ha with ⟨⟨x', y⟩, ha_mem, rfl⟩
      rcases ha_mem with ⟨_, hx'⟩
      cases hx'
      rw [hε_top]
      exact ⟨y, ha_lt.le⟩
    · have hε_bot : ε ≠ ⊥ := by
        intro hε_bot
        simp [hε_bot] at hε
      lift ε to ℝ using ⟨hε_top, hε_bot⟩
      have hε_real : 0 < ε := EReal.coe_lt_coe_iff.mp hε
      have hlevel_lt : (level : EReal) < ((level + ε : ℝ) : EReal) := by
        exact_mod_cast (lt_add_of_pos_right level hε_real)
      have hlt : partialInfProjection Set.univ F x < ((level + ε : ℝ) : EReal) :=
        lt_of_le_of_lt hx hlevel_lt
      rw [partialInfProjection_eq_sInf] at hlt
      rcases sInf_lt_iff.mp hlt with ⟨a, ha, ha_lt⟩
      rcases ha with ⟨⟨x', y⟩, ha_mem, rfl⟩
      rcases ha_mem with ⟨_, hx'⟩
      cases hx'
      exact ⟨y, ha_lt.le⟩
  · intro hx
    -- If every positive `ε` admits a witness below `level + ε`, a real point strictly between
    -- `level` and the infimum contradicts the universal lower-bound property of the infimum.
    by_contra hle
    have hlt : (level : EReal) < partialInfProjection Set.univ F x := lt_of_not_ge hle
    rcases EReal.exists_between_coe_real hlt with ⟨μ, hlevel_μ, hμ_inf⟩
    have hε : (0 : EReal) < (μ : EReal) - level := by
      exact EReal.sub_pos.mpr hlevel_μ
    rcases hx ((μ : EReal) - level) hε with ⟨y, hy⟩
    have hsum : (level : EReal) + ((μ : EReal) - level) = (μ : EReal) := by
      calc
        (level : EReal) + ((μ : EReal) - level)
            = (level : EReal) + (((μ - level : ℝ)) : EReal) := by
                rw [← EReal.coe_sub]
        _ = (((level + (μ - level) : ℝ)) : EReal) := by
                rw [← EReal.coe_add]
        _ = (μ : EReal) := by simp
    have hy' : F (x, y) ≤ (μ : EReal) := by
      simpa [hsum] using hy
    have hcontra : (μ : EReal) < (μ : EReal) :=
      lt_of_lt_of_le hμ_inf (le_trans (partialInfProjection_univ_le_slice F x y) hy')
    exact (lt_irrefl (_ : EReal)) hcontra

/-- Pointwise form of Theorem 3.30. -/
theorem partialInfProjection_univ_le_iff_forall_pos_exists_le_add
    (F : X × Y → EReal) (x : X) (level : ℝ) :
    partialInfProjection Set.univ F x ≤ (level : EReal) ↔
      ∀ ε > 0, ∃ y : Y, F (x, y) ≤ (level + ε : EReal) := by
  simpa [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion] using
    congrArg (fun s : Set X ↦ x ∈ s)
      (partialInfProjection_univ_sublevelSet_eq_iInter_iUnion F level)

/-- Secondary finite-value bridge for Theorem 3.30: intersecting the faithful `EReal` theorem
with `dom (partialInfProjection Set.univ F)` recovers the textbook real-sublevel surface, which
forgets fibers where the infimal projection equals `⊥`. -/
theorem partialInfProjection_univ_sublevelSet_eq_dom_inter_iInter_iUnion
    (F : X × Y → EReal) (level : ℝ) :
    {x | x ∈ dom (partialInfProjection Set.univ F) ∧ partialInfProjection Set.univ F x ≤ level} =
      dom (partialInfProjection Set.univ F) ∩
        ⋂ ε > 0, ⋃ y : Y, {x | x ∈ dom (fun x : X ↦ F (x, y)) ∧ F (x, y) ≤ level + ε} := by
  ext x
  -- Evaluate the set equality at `x` and separate the domain condition from the approximation
  -- condition.
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · rintro ⟨hxdom, hlevel⟩
    refine ⟨hxdom, ?_⟩
    -- For finite positive `ε`, use the approximation theorem directly; for `ε = ⊤`, reuse one
    -- fixed finite witness.
    intro ε hε
    by_cases hε_top : ε = ⊤
    · have hone : (0 : EReal) < (1 : EReal) := by norm_num
      rcases (partialInfProjection_univ_le_iff_forall_pos_exists_le_add F x level).1 hlevel 1 hone
        with ⟨y, hy⟩
      refine ⟨y, ?_, ?_⟩
      · exact slice_mem_dom_of_partialInfProjection_mem_dom_of_le_real hxdom (by
          simpa [EReal.coe_add] using hy)
      · rw [hε_top]
        exact le_top
    · have hε_bot : ε ≠ ⊥ := by
        intro hε_bot
        simp [hε_bot] at hε
      lift ε to ℝ using ⟨hε_top, hε_bot⟩
      have hε_real : 0 < ε := EReal.coe_lt_coe_iff.mp hε
      rcases (partialInfProjection_univ_le_iff_forall_pos_exists_le_add F x level).1 hlevel ε
          (by exact_mod_cast hε_real) with ⟨y, hy⟩
      refine ⟨y, ?_, ?_⟩
      · exact slice_mem_dom_of_partialInfProjection_mem_dom_of_le_real hxdom (by
          simpa [EReal.coe_add] using hy)
      · simpa [EReal.coe_add] using hy
  · rintro ⟨hxdom, happrox⟩
    refine ⟨hxdom, ?_⟩
    -- Forget the slice-domain side condition and apply the faithful pointwise theorem backwards.
    refine (partialInfProjection_univ_le_iff_forall_pos_exists_le_add F x level).2 ?_
    intro ε hε
    rcases happrox ε hε with ⟨y, hy_dom, hy⟩
    exact ⟨y, hy⟩

end
