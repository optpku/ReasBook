/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- The perspective transform of an extended-real-valued function on a real vector space. -/
noncomputable def perspective (φ : H → EReal) : ℝ × H → EReal :=
  fun p ↦ if 0 < p.1 then (p.1 : EReal) * φ (p.1⁻¹ • p.2) else ⊤

-- Proof sketch: unfold `perspective` and simplify the `if` expression using the positivity
-- hypothesis on the first coordinate.
/-- At a positive first coordinate, the perspective equals `ξ * φ (x / ξ)`. -/
theorem perspective_apply_of_pos (φ : H → EReal) {ξ : ℝ} {x : H} (hξ : 0 < ξ) :
    perspective φ (ξ, x) = (ξ : EReal) * φ (ξ⁻¹ • x) := by
  -- Unfold the definition and select the positive branch of the conditional.
  simp [perspective, hξ]

-- Proof sketch: unfold `perspective` and simplify the `if` expression using the nonpositivity
-- hypothesis on the first coordinate.
/-- At a nonpositive first coordinate, the perspective is `+∞`. -/
theorem perspective_apply_of_nonpos (φ : H → EReal) {ξ : ℝ} {x : H} (hξ : ξ ≤ 0) :
    perspective φ (ξ, x) = ⊤ := by
  -- Unfold the definition and select the nonpositive branch of the conditional.
  simp [perspective, not_lt_of_ge hξ]

/-- The unit slice `C = {((1, x), η) | (x, η) ∈ epi φ}` used to describe the epigraph of the
perspective as a cone. -/
def perspectiveEpigraphSlice (φ : H → EReal) : Set ((ℝ × H) × ℝ) :=
  {p | p.1.1 = 1 ∧ (p.1.2, p.2) ∈ epigraph φ}

-- Proof sketch: unfold `perspectiveEpigraphSlice` and simplify membership for the explicit triple
-- `((ξ, x), η)`.
omit [AddCommGroup H] [Module ℝ H] in
/-- Membership in the perspective epigraph slice means that the first coordinate is `1` and the
remaining coordinates form a point of `epigraph φ`. -/
theorem mem_perspectiveEpigraphSlice_iff (φ : H → EReal) (ξ : ℝ) (x : H) (η : ℝ) :
    ((ξ, x), η) ∈ perspectiveEpigraphSlice φ ↔ ξ = 1 ∧ (x, η) ∈ epigraph φ := by
  -- Unfold the slice definition and read off the two defining coordinates.
  simp [perspectiveEpigraphSlice]

/-- Helper for Proposition 8.25: the unit slice over a convex epigraph is itself convex. -/
private lemma convex_perspectiveEpigraphSlice (φ : H → EReal)
    (hφ_convex : Convex ℝ (epigraph φ)) :
    Convex ℝ (perspectiveEpigraphSlice φ) := by
  -- The slice keeps the first coordinate fixed at `1`, while the remaining coordinates stay in the
  -- convex epigraph of `φ`.
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨⟨ξ₁, x₁⟩, η₁⟩
  rcases q with ⟨⟨ξ₂, x₂⟩, η₂⟩
  rw [mem_perspectiveEpigraphSlice_iff] at hp hq ⊢
  rcases hp with ⟨hξ₁, hp⟩
  rcases hq with ⟨hξ₂, hq⟩
  constructor
  · -- The first coordinate remains `1` because both endpoints lie in the unit slice.
    simp [Prod.smul_mk, smul_eq_mul, hξ₁, hξ₂, hab]
  · -- Convexity of the original epigraph transfers to the remaining two coordinates.
    have hcombo :
        a • (x₁, η₁) + b • (x₂, η₂) ∈ epigraph φ :=
      (convex_iff_forall_pos.mp hφ_convex) hp hq ha hb hab
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo

/-- Helper for Proposition 8.25: epigraph membership for the perspective is equivalent to a
positive-height normalization into the original epigraph. -/
private lemma mem_epigraph_perspective_iff (φ : H → EReal) {ξ : ℝ} {x : H} {η : ℝ} :
    ((ξ, x), η) ∈ epigraph (perspective φ) ↔
      0 < ξ ∧ (ξ⁻¹ • x, η / ξ) ∈ epigraph φ := by
  by_cases hξ : 0 < ξ
  · -- On the positive branch, divide by `ξ` to recover the normalized epigraph point.
    rw [mem_epigraph_iff, perspective_apply_of_pos φ hξ]
    constructor
    · intro hmem
      refine ⟨hξ, ?_⟩
      rw [mem_epigraph_iff, EReal.coe_div]
      exact (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr hξ) (EReal.coe_ne_top ξ)).2 <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmem
    · rintro ⟨_, hmem⟩
      rw [mem_epigraph_iff, EReal.coe_div] at hmem
      have hscaled :=
        (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr hξ) (EReal.coe_ne_top ξ)).1 hmem
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  · have hξ_nonpos : ξ ≤ 0 := le_of_not_gt hξ
    -- At nonpositive height, the perspective value is `⊤`, so no real epigraph point exists.
    rw [mem_epigraph_iff, perspective_apply_of_nonpos φ hξ_nonpos]
    constructor
    · intro hmem
      simp at hmem
    · rintro ⟨hpos, _⟩
      exact (hξ hpos).elim

/-- Helper for Proposition 8.25: cone membership in the unit slice is equivalent to the same
positive-height normalization as on the epigraph side. -/
private lemma mem_cone_perspectiveEpigraphSlice_iff (φ : H → EReal)
    (hφ_convex : Convex ℝ (epigraph φ)) {ξ : ℝ} {x : H} {η : ℝ} :
    ((ξ, x), η) ∈ cone (perspectiveEpigraphSlice φ) ↔
      0 < ξ ∧ (ξ⁻¹ • x, η / ξ) ∈ epigraph φ := by
  constructor
  · intro hcone
    rcases (ConvexCone.mem_hull_of_convex (x := ((ξ, x), η))
        (convex_perspectiveEpigraphSlice φ hφ_convex)).1 hcone with ⟨a, ha, hmem⟩
    rcases Set.mem_smul_set.mp hmem with ⟨p, hp, hp_eq⟩
    rcases p with ⟨⟨ζ, y⟩, θ⟩
    rw [mem_perspectiveEpigraphSlice_iff] at hp
    rcases hp with ⟨hζ, hp⟩
    have hξ_eq : ξ = a := by
      have hfirst : a * ζ = ξ := by
        simpa [Prod.smul_mk, smul_eq_mul] using congrArg (fun q : ((ℝ × H) × ℝ) ↦ q.1.1) hp_eq
      simpa [hζ] using hfirst.symm
    refine ⟨?_, ?_⟩
    · -- The cone scalar is the first coordinate because every generator has first coordinate `1`.
      simpa [hξ_eq] using ha
    · -- After cancelling the positive scalar, the normalized point lands back in `epigraph φ`.
      have hx_eq : x = a • y := by
        simpa [Prod.smul_mk, smul_eq_mul, hζ] using
          (congrArg (fun q : ((ℝ × H) × ℝ) ↦ q.1.2) hp_eq).symm
      have hη_eq : η = a * θ := by
        simpa [Prod.smul_mk, smul_eq_mul, hζ] using
          (congrArg (fun q : ((ℝ × H) × ℝ) ↦ q.2) hp_eq).symm
      have hx_norm : ξ⁻¹ • x = y := by
        calc
          ξ⁻¹ • x = a⁻¹ • x := by simp [hξ_eq]
          _ = a⁻¹ • (a • y) := by rw [hx_eq]
          _ = y := by simpa [smul_smul] using inv_smul_smul₀ ha.ne' y
      have hη_norm : η / ξ = θ := by
        calc
          η / ξ = (a * θ) / a := by rw [hη_eq, hξ_eq]
          _ = θ := by
            rw [div_eq_mul_inv, mul_assoc, mul_comm θ a⁻¹, ← mul_assoc, mul_inv_cancel₀ ha.ne',
              one_mul]
      simpa [hx_norm, hη_norm] using hp
  · rintro ⟨hξ, hmem⟩
    apply (ConvexCone.mem_hull_of_convex (x := ((ξ, x), η))
      (convex_perspectiveEpigraphSlice φ hφ_convex)).2
    refine ⟨ξ, hξ, ?_⟩
    -- Use the normalized point in the unit slice and scale it back by `ξ`.
    refine Set.mem_smul_set.mpr ?_
    refine ⟨((1, ξ⁻¹ • x), η / ξ), ?_, ?_⟩
    · rw [mem_perspectiveEpigraphSlice_iff]
      exact ⟨rfl, hmem⟩
    · -- Expanding the scalar action recovers the original triple from its normalized version.
      apply Prod.ext
      · apply Prod.ext
        · simp [Prod.smul_mk, smul_eq_mul]
        · simp [Prod.smul_mk, smul_eq_mul, smul_smul, hξ.ne']
      · rw [Prod.smul_mk, smul_eq_mul, div_eq_mul_inv, ← mul_assoc, mul_comm ξ η, mul_assoc,
          mul_inv_cancel₀ hξ.ne', mul_one]

-- Proof sketch: use the positivity branch of the perspective to normalize any epigraph point
-- `((ξ, x), η)` with `ξ > 0` to the unit slice `((1, ξ⁻¹ • x), η / ξ)`, and conversely scale a
-- unit-slice point back up. Convexity of `epigraph φ` makes the slice convex, so its conical hull
-- is exactly the positive-scalar image appearing in the normalization argument.
/-- The epigraph of the perspective of a function with convex epigraph is the cone generated by
its unit epigraph slice. -/
theorem epigraph_perspective_eq_cone (φ : H → EReal) (hφ_convex : Convex ℝ (epigraph φ)) :
    epigraph (perspective φ) = cone (perspectiveEpigraphSlice φ) := by
  -- Both sides are exactly the positive-height normalized triples from the textbook proof.
  ext p
  rcases p with ⟨⟨ξ, x⟩, η⟩
  rw [mem_epigraph_perspective_iff, mem_cone_perspectiveEpigraphSlice_iff φ hφ_convex]

-- Proof sketch: combine the previous epigraph formula with convexity of the cone over the convex
-- slice `perspectiveEpigraphSlice φ`.
/-- If `φ` has convex epigraph, then so does its perspective. -/
theorem convex_epigraph_perspective (φ : H → EReal) (hφ_convex : Convex ℝ (epigraph φ)) :
    Convex ℝ (epigraph (perspective φ)) := by
  -- Rewrite the epigraph as the convex cone hull of the unit slice.
  rw [epigraph_perspective_eq_cone φ hφ_convex, Set.cone_def]
  simpa using (ConvexCone.hull ℝ (perspectiveEpigraphSlice φ)).convex

-- Proof sketch: the first claim is the cone description of the previous theorem, and the second
-- is the resulting convexity of the perspective epigraph.
/-- Proposition 8.25: if `φ` has convex epigraph, then the epigraph of its perspective is the cone
generated by the unit slice `C = {((1, x), η) | (x, η) ∈ epi φ}`, and this epigraph is convex. -/
theorem perspective_epigraph_eq_cone_and_convex (φ : H → EReal)
    (hφ_convex : Convex ℝ (epigraph φ)) :
    epigraph (perspective φ) = cone (perspectiveEpigraphSlice φ) ∧
      Convex ℝ (epigraph (perspective φ)) := by
  -- The two claims are exactly the cone description and the induced convexity proved above.
  exact ⟨epigraph_perspective_eq_cone φ hφ_convex, convex_epigraph_perspective φ hφ_convex⟩

end ERealFunction
