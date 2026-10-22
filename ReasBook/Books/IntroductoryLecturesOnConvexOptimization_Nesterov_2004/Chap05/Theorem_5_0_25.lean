/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped LevelSetNotation

/- Theorem 5.0.25 lies in the chapter's convex recession-direction domain.

Sampled owner declarations:
* `BddBelow (Set.range f)` from mathlib, the canonical function-level owner for "bounded below";
* `𝓛[f](a)` and `mem_levelSet_iff` from `Chap01/Definition_1_4_8`, the chapter owner for lower
  sublevel sets, retained here only for the horizontal-ray geometric companions.
* `Set.MapsTo` from mathlib, the canonical owner for the horizontal-ray bridge into a level set.

Best owner abstraction:
* source-facing: a function with a negative-slope recession ray is not bounded below;
* core/canonical: `¬ BddBelow (Set.range f)`;
* bridge/view: the horizontal-slope sublevel-set consequences for `𝓛[f](f x)`.

Primitive data:
* the objective `f : E → ℝ`;
* a base point `x` and a recession direction `d`;
* a scalar recession slope `σ < 0` together with the ray estimate
  `f (x + t • d) ≤ f x + t * σ`.

Derived API:
* the owner-level conclusion `¬ BddBelow (Set.range f)`;
* the horizontal-slope bridge `Set.MapsTo (fun t ↦ x + t • d) (Set.Ici 0) (𝓛[f](f x))`;
* the geometric corollaries `¬ Bornology.IsBounded (𝓛[f](f x))` and
  `Set.Infinite (𝓛[f](f x))`.

Source/core/bridge triage:
* source-facing: the function-level unbounded-below conclusion for the objective;
* core/canonical: `¬ BddBelow (Set.range f)`;
* bridge/view: the level-set containment and unboundedness lemmas for the special horizontal case
  `σ = 0`.

The previous revision promoted only the horizontal-ray geometric bridge
`¬ Bornology.IsBounded (𝓛[f](f x))`. This file restores the source-facing owner conclusion on
`Set.range f` and demotes the level-set statements to companions. -/

section RangeBoundedness

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {f : E → ℝ}

/-- Theorem 5.0.25: if an objective admits a recession ray from `x` whose values are bounded
above by an affine function with negative slope `σ`, then the objective is not bounded below on
the whole space. The owner-level conclusion is the canonical range statement
`¬ BddBelow (Set.range f)`. -/
theorem not_bddBelow_range_of_negative_recession_ray
    {x d : E} {σ : ℝ} (hσ : σ < 0)
    (hray : ∀ t : ℝ, 0 ≤ t → f (x + t • d) ≤ f x + t * σ) :
    ¬ BddBelow (Set.range f) := by
  intro hbelow
  rcases hbelow with ⟨m, hm⟩
  let t : ℝ := (|f x - m| + 1) / (-σ)
  have ht_nonneg : 0 ≤ t := by
    have : 0 < -σ := by linarith
    dsimp [t]
    positivity
  have hm_t : m ≤ f (x + t • d) :=
    hm ⟨x + t • d, rfl⟩
  have hltm : f x + t * σ < m := by
    have habs : f x - m ≤ |f x - m| := le_abs_self _
    have hσ_ne : σ ≠ 0 := ne_of_lt hσ
    have ht_eval : t * σ = -(|f x - m| + 1) := by
      dsimp [t]
      field_simp [hσ_ne]
    linarith
  exact (not_lt_of_ge hm_t) (lt_of_le_of_lt (hray t ht_nonneg) hltm)

end RangeBoundedness

section HorizontalLevelSetBridge

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {f : E → ℝ} {x d : E}

/-- In the horizontal recession case `σ = 0`, the forward ray from `x` in direction `d` stays
inside the lower sublevel set `𝓛[f](f x)`. This is a bridge/view statement for the later geometric
companions, not the main owner conclusion of Theorem 5.0.25. -/
theorem ray_mapsTo_levelSet_of_nonincreasing_ray
    (hray : ∀ t : ℝ, 0 ≤ t → f (x + t • d) ≤ f x) :
    Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Ici (0 : ℝ)) (𝓛[f]((f x))) := by
  intro t ht
  exact hray t ht

end HorizontalLevelSetBridge

section HorizontalLevelSetGeometry

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {x d : E}

/-- A nonzero horizontal recession ray forces the sublevel set through `x` to be unbounded. This
is the geometric bridge companion to Theorem 5.0.25, corresponding to the special slope `σ = 0`
case. -/
theorem levelSet_not_bounded_of_nonzero_horizontal_recession_ray
    (hd : d ≠ 0)
    (hray : ∀ t : ℝ, 0 ≤ t → f (x + t • d) ≤ f x) :
    ¬ Bornology.IsBounded (𝓛[f]((f x)) : Set E) := by
  intro hbounded
  let ray : ℝ → E := fun t ↦ x + t • d
  have hray_mapsTo : Set.MapsTo ray (Set.Ici (0 : ℝ)) (𝓛[f]((f x))) :=
    ray_mapsTo_levelSet_of_nonincreasing_ray hray
  have himage_bounded : Bornology.IsBounded (ray '' Set.Ici (0 : ℝ)) :=
    hbounded.subset hray_mapsTo.image_subset
  obtain ⟨R, hR⟩ := himage_bounded.exists_norm_le
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hR_nonneg : 0 ≤ R := by
    have hzero_mem : ray 0 ∈ ray '' Set.Ici (0 : ℝ) := ⟨0, by simp, rfl⟩
    exact le_trans (norm_nonneg _) (hR _ hzero_mem)
  let t : ℝ := (R + ‖x‖ + 1) / ‖d‖
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_mem : ray t ∈ ray '' Set.Ici (0 : ℝ) := ⟨t, ht_nonneg, rfl⟩
  have hRt : ‖ray t‖ ≤ R := hR _ ht_mem
  have htd : t * ‖d‖ ≤ R + ‖x‖ := by
    have hsub : ‖t • d‖ ≤ ‖ray t‖ + ‖x‖ := by
      simpa [ray, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        norm_sub_le (x + t • d) x
    calc
      t * ‖d‖ = ‖t • d‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht_nonneg]
      _ ≤ ‖ray t‖ + ‖x‖ := hsub
      _ ≤ R + ‖x‖ := add_le_add hRt le_rfl
  have ht_eval : t * ‖d‖ = R + ‖x‖ + 1 := by
    dsimp [t]
    field_simp [hdnorm.ne']
  linarith

/-- A nonzero horizontal recession ray produces infinitely many points in the sublevel set through
`x`. This remains a corollary of the geometric bridge theorem, not the main owner content of
Theorem 5.0.25. -/
theorem levelSet_infinite_of_nonzero_horizontal_recession_ray
    (hd : d ≠ 0)
    (hray : ∀ t : ℝ, 0 ≤ t → f (x + t • d) ≤ f x) :
    Set.Infinite (𝓛[f]((f x)) : Set E) := by
  intro hfinite
  exact levelSet_not_bounded_of_nonzero_horizontal_recession_ray hd hray hfinite.isBounded

end HorizontalLevelSetGeometry
