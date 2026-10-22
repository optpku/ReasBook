/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology WithTopConvexAnalysis

section Ambient

local notation "E" => EuclideanSpace ℝ (Fin 2)

local notation "S" => Metric.sphere (0 : E) 1
local notation "B" => Metric.closedBall (0 : E) 1

/- Proposition 3.8 lies in the chapter's source-facing unit-disk boundary-extension domain on the
Euclidean plane `ℝ²`, represented canonically as `EuclideanSpace ℝ (Fin 2)`.

Sampled owner-style declarations:
- mathlib `Metric.sphere` and `Metric.closedBall`, the canonical owners of the unit boundary and
  unit closed ball;
- chapter `dom` and `withTopRealPart` from `Definition_3_3`;
- chapter `WithTopConvexAnalysis.effectiveEpigraph` from `Definition_3_3`;
- mathlib `ConvexOn`, the canonical convexity owner on the effective domain;
- mathlib `LowerSemicontinuous`.

Best owner abstraction:
- source-facing: `unitDiskBoundaryExtension`, the textbook unit-disk construction on the Euclidean
  unit disk;
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`, `dom f`, and
  `LowerSemicontinuous f`, together with the canonical unit sphere and closed unit ball;
- bridge/view: the effective-epigraph formulation of convexity on
  `E = EuclideanSpace ℝ (Fin 2)`, the canonical mathlib model of the textbook plane.

Primitive data:
- the Euclidean plane `E = EuclideanSpace ℝ (Fin 2)`;
- the boundary datum `φ : S → ℝ`;
- the source-facing extension `unitDiskBoundaryExtension φ`.

Derived API:
- the open-disk value theorem below;
- the canonical convexity-plus-domain theorem below;
- the lower-semicontinuity criterion below.

The previous theorem surface stated convexity via `constrainedEpigraph Set.univ`, which duplicates
the chapter owner view. This file now uses the canonical `ConvexOn` surface on `dom` directly and
keeps the domain identification as the companion part of the same source-facing proposition. -/

/-- The textbook unit-disk boundary extension on the Euclidean plane `EuclideanSpace ℝ (Fin 2)`:
it is `0` on the open unit disk, equal to `φ` on the unit circle, and `⊤` outside the closed unit
disk. -/
def unitDiskBoundaryExtension (φ : S → ℝ) : E → WithTop ℝ :=
  let _ : DecidablePred fun x : E ↦ x ∈ S := Classical.decPred _
  fun x ↦
    if _hx : ‖x‖ < 1 then
      (0 : WithTop ℝ)
    else if hs : x ∈ S then
      (φ ⟨x, hs⟩ : WithTop ℝ)
    else
      ⊤

/-- On the open unit ball, `unitDiskBoundaryExtension φ` takes the value `0`. -/
-- Proof sketch: unfold `unitDiskBoundaryExtension` and simplify the first `if` with the strict
-- inequality hypothesis.
theorem unitDiskBoundaryExtension_eq_zero_of_norm_lt_one
    {φ : S → ℝ} {x : E} (hx : ‖x‖ < 1) :
    unitDiskBoundaryExtension φ x = 0 := by
  -- The open-ball branch of the definition applies immediately.
  simp [unitDiskBoundaryExtension, hx]

/-- Helper for Proposition 3.8: outside the closed unit ball, the unit-disk boundary extension
takes the value `⊤`. -/
theorem unitDiskBoundaryExtension_eq_top_of_not_mem_closedBall
    {φ : S → ℝ} {x : E} (hx : x ∉ B) :
    unitDiskBoundaryExtension φ x = ⊤ := by
  -- Outside the closed ball, the point is neither in the open ball nor on the sphere.
  have hlt : ¬ ‖x‖ < 1 := by
    intro hlt
    apply hx
    exact mem_closedBall_zero_iff.2 hlt.le
  have hne : ‖x‖ ≠ 1 := by
    intro hnorm
    apply hx
    exact mem_closedBall_zero_iff.2 hnorm.le
  simp [unitDiskBoundaryExtension, hlt, hne]

/-- Helper for Proposition 3.8: the effective domain of the unit-disk boundary extension is
exactly the closed unit ball. -/
theorem mem_dom_unitDiskBoundaryExtension_iff
    {φ : S → ℝ} {x : E} :
    x ∈ dom (unitDiskBoundaryExtension φ) ↔ x ∈ B := by
  constructor
  · intro hxdom
    -- Finite values occur only on the open disk or on the sphere.
    by_cases hlt : ‖x‖ < 1
    · exact mem_closedBall_zero_iff.2 hlt.le
    · by_cases hs : x ∈ S
      · exact mem_closedBall_zero_iff.2 (mem_sphere_zero_iff_norm.1 hs).le
      · exfalso
        have hnotB : x ∉ B := by
          intro hxB
          have hle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hxB
          rcases lt_or_eq_of_le hle with hlt' | hnorm
          · exact hlt hlt'
          · exact hs (mem_sphere_zero_iff_norm.2 hnorm)
        have htop : unitDiskBoundaryExtension φ x = ⊤ :=
          unitDiskBoundaryExtension_eq_top_of_not_mem_closedBall (φ := φ) hnotB
        have hnodom : x ∉ dom (unitDiskBoundaryExtension φ) := by
          intro hx'
          simpa [withTopEffectiveDomain, htop] using hx'
        exact hnodom hxdom
  · intro hxB
    -- On the closed ball, the value is either `0` or a finite boundary value.
    have hle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hxB
    by_cases hlt : ‖x‖ < 1
    · simp [withTopEffectiveDomain, unitDiskBoundaryExtension, hlt]
    · have hnorm : ‖x‖ = 1 := le_antisymm hle (le_of_not_gt hlt)
      have hs : x ∈ S := mem_sphere_zero_iff_norm.2 hnorm
      have hvalue : unitDiskBoundaryExtension φ x = (φ ⟨x, hs⟩ : WithTop ℝ) := by
        simp [unitDiskBoundaryExtension, hnorm]
      simpa [withTopEffectiveDomain, hvalue]

/-- Helper for Proposition 3.8: the real-valued representative of the unit-disk boundary
extension is nonnegative on the closed unit ball whenever the boundary datum is nonnegative. -/
theorem zero_le_withTopRealPart_unitDiskBoundaryExtension
    {φ : S → ℝ} (hφ_nonneg : ∀ z : S, 0 ≤ φ z) {x : E} (hx : x ∈ B) :
    0 ≤ withTopRealPart (unitDiskBoundaryExtension φ) x := by
  -- On the closed ball, the value is either the interior value `0` or the boundary datum `φ x`.
  have hxdom : x ∈ dom (unitDiskBoundaryExtension φ) :=
    (mem_dom_unitDiskBoundaryExtension_iff (φ := φ)).2 hx
  by_cases hlt : ‖x‖ < 1
  · have hwithtop : (0 : WithTop ℝ) ≤ unitDiskBoundaryExtension φ x := by
      simp [unitDiskBoundaryExtension_eq_zero_of_norm_lt_one (φ := φ) hlt]
    exact (le_withTopRealPart_iff hxdom).2 hwithtop
  · have hle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    have hnorm : ‖x‖ = 1 := le_antisymm hle (le_of_not_gt hlt)
    have hs : x ∈ S := mem_sphere_zero_iff_norm.2 hnorm
    have hwithtop : (0 : WithTop ℝ) ≤ unitDiskBoundaryExtension φ x := by
      have hvalue : unitDiskBoundaryExtension φ x = (φ ⟨x, hs⟩ : WithTop ℝ) := by
        simp [unitDiskBoundaryExtension, hlt, hnorm]
      rw [hvalue]
      exact_mod_cast hφ_nonneg ⟨x, hs⟩
    exact (le_withTopRealPart_iff hxdom).2 hwithtop

/-- Helper for Proposition 3.8: if the boundary datum vanishes on the unit circle, then the
unit-disk boundary extension vanishes on the whole closed unit ball. -/
theorem unitDiskBoundaryExtension_eq_zero_of_mem_closedBall
    {φ : S → ℝ} (hzero : ∀ z : S, φ z = 0) {x : E} (hx : x ∈ B) :
    unitDiskBoundaryExtension φ x = 0 := by
  -- Boundary points use the vanishing boundary datum, while interior points already have value `0`.
  by_cases hlt : ‖x‖ < 1
  · exact unitDiskBoundaryExtension_eq_zero_of_norm_lt_one (φ := φ) hlt
  · have hle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    have hnorm : ‖x‖ = 1 := le_antisymm hle (le_of_not_gt hlt)
    have hs : x ∈ S := mem_sphere_zero_iff_norm.2 hnorm
    have hvalue : unitDiskBoundaryExtension φ x = (φ ⟨x, hs⟩ : WithTop ℝ) := by
      simp [unitDiskBoundaryExtension, hlt, hnorm]
    simpa [hvalue, hzero ⟨x, hs⟩]

/-- Proposition 3.8 on the Euclidean unit circle: for a nonnegative function on the unit sphere in
`EuclideanSpace ℝ (Fin 2)`, the associated extended-real-valued unit-disk boundary extension is
convex in the chapter owner sense, and its effective domain is exactly the closed unit disk. -/
-- Proof sketch: compute `dom (unitDiskBoundaryExtension φ)` as the closed unit ball. Then verify
-- Jensen's inequality for `withTopRealPart (unitDiskBoundaryExtension φ)` on that domain, using
-- that the interior value is `0` while the boundary datum is nonnegative.
theorem unitDiskBoundaryExtension_convex_and_effectiveDomain
    (φ : S → ℝ) (hφ_nonneg : ∀ z : S, 0 ≤ φ z) :
    ConvexOn ℝ (dom (unitDiskBoundaryExtension φ))
      (withTopRealPart (unitDiskBoundaryExtension φ)) ∧
      dom (unitDiskBoundaryExtension φ) = B := by
  have hdom : dom (unitDiskBoundaryExtension φ) = B := by
    ext x
    exact mem_dom_unitDiskBoundaryExtension_iff (φ := φ)
  refine ⟨?_, hdom⟩
  rw [hdom]
  constructor
  · exact convex_closedBall (0 : E) 1
  · intro x hx y hy a b ha hb hab
    -- The endpoint and diagonal cases reduce to tautological equalities.
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simp [ha0, hb1]
    · by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simp [hb0, ha1]
      · by_cases hxy : x = y
        · subst hxy
          have hcombo : a • x + b • x = x := by
            calc
              a • x + b • x = (a + b) • x := by rw [← add_smul]
              _ = x := by simp [hab]
          rw [hcombo, ← add_smul]
          simpa [hab]
        · -- A strict convex combination of distinct boundary/domain points lands in the open ball.
          have hxa : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
          have hya : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.1 hy
          have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          have hcombo_norm : ‖a • x + b • y‖ < 1 :=
            norm_combo_lt_of_ne hxa hya hxy ha_pos hb_pos hab
          have hcombo_zero :
              withTopRealPart (unitDiskBoundaryExtension φ) (a • x + b • y) = 0 := by
            simp [withTopRealPart,
              unitDiskBoundaryExtension_eq_zero_of_norm_lt_one (φ := φ) hcombo_norm]
          rw [hcombo_zero]
          exact add_nonneg
            (smul_nonneg ha
              (zero_le_withTopRealPart_unitDiskBoundaryExtension
                (φ := φ) hφ_nonneg hx))
            (smul_nonneg hb
              (zero_le_withTopRealPart_unitDiskBoundaryExtension
                (φ := φ) hφ_nonneg hy))

/-- On `EuclideanSpace ℝ (Fin 2)`, the unit-disk boundary extension is lower semicontinuous
exactly when the boundary datum vanishes identically on the unit circle. -/
-- Proof sketch: if `φ = 0`, the function is the indicator of the closed unit ball. Conversely,
-- approach a boundary point by points from the open unit ball where the function is `0`, and use
-- semicontinuity plus the nonnegativity of `φ`.
theorem unitDiskBoundaryExtension_lowerSemicontinuous_iff_eq_zero
    (φ : S → ℝ) (hφ_nonneg : ∀ z : S, 0 ≤ φ z) :
    LowerSemicontinuous (unitDiskBoundaryExtension φ) ↔ ∀ z : S, φ z = 0 := by
  constructor
  · intro hlsc z
    -- The closed zero-sublevel contains the open ball, hence also its closure, which reaches
    -- every boundary point.
    let Z : Set E := (unitDiskBoundaryExtension φ) ⁻¹' Set.Iic (0 : WithTop ℝ)
    have hZ_closed : IsClosed Z :=
      (lowerSemicontinuous_iff_isClosed_preimage.1 hlsc) 0
    have hball_subset : Metric.ball (0 : E) 1 ⊆ Z := by
      intro x hx
      have hnorm : ‖x‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      have hval := unitDiskBoundaryExtension_eq_zero_of_norm_lt_one (φ := φ) hnorm
      simp [Z, Set.mem_preimage, hval]
    have hclosure_subset : closure (Metric.ball (0 : E) 1) ⊆ Z :=
      closure_minimal hball_subset hZ_closed
    have hz_closure : ((z : S) : E) ∈ closure (Metric.ball (0 : E) 1) := by
      rw [closure_ball (0 : E) one_ne_zero]
      exact mem_closedBall_zero_iff.2 (mem_sphere_zero_iff_norm.1 z.2).le
    have hz_mem : ((z : S) : E) ∈ Z := hclosure_subset hz_closure
    have hz_eq : ‖((z : S) : E)‖ = 1 := mem_sphere_zero_iff_norm.1 z.2
    have hz_not_lt : ¬ ‖((z : S) : E)‖ < 1 := by
      linarith
    have hboundary :
        unitDiskBoundaryExtension φ ((z : S) : E) = (φ z : WithTop ℝ) := by
      simp [unitDiskBoundaryExtension, hz_eq]
    have hφ_le : φ z ≤ 0 := by
      simpa [Z, Set.mem_preimage, hboundary] using hz_mem
    exact le_antisymm hφ_le (hφ_nonneg z)
  · intro hzero
    -- When the boundary datum vanishes, each finite sublevel set is either `∅` or the closed
    -- unit ball, and the `⊤`-sublevel is all of space.
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    rcases eq_or_ne y ⊤ with rfl | hy
    · simpa using isClosed_univ
    · rcases WithTop.ne_top_iff_exists.1 hy with ⟨r, rfl⟩
      rcases lt_or_ge r 0 with hr | hr
      · have hpreimage :
            (unitDiskBoundaryExtension φ) ⁻¹' Set.Iic (r : WithTop ℝ) = ∅ := by
            ext x
            by_cases hx : x ∈ B
            · have hval :=
                unitDiskBoundaryExtension_eq_zero_of_mem_closedBall (φ := φ) hzero hx
              simp [Set.mem_preimage, hval, not_le_of_gt hr]
            · have htop :=
                unitDiskBoundaryExtension_eq_top_of_not_mem_closedBall (φ := φ) hx
              simp [Set.mem_preimage, htop]
        exact hpreimage ▸ (isClosed_empty : IsClosed (∅ : Set E))
      · have hpreimage :
              (unitDiskBoundaryExtension φ) ⁻¹' Set.Iic (r : WithTop ℝ) = B := by
            ext x
            by_cases hx : x ∈ B
            · have hval :=
                unitDiskBoundaryExtension_eq_zero_of_mem_closedBall (φ := φ) hzero hx
              simp [Set.mem_preimage, hx, hval, hr]
            · have htop :=
                unitDiskBoundaryExtension_eq_top_of_not_mem_closedBall (φ := φ) hx
              simp [Set.mem_preimage, hx, htop]
        have hclosedB : IsClosed B := by
          change IsClosed (Metric.closedBall (0 : E) 1)
          exact Metric.isClosed_closedBall
        exact hpreimage ▸ hclosedB

end Ambient

end
