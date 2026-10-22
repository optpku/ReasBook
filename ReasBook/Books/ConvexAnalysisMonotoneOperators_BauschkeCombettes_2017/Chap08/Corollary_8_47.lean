/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_39

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Corollary 8.47: under ambient pointwise upper semicontinuity on the strict
negative level set, Proposition 8.46 identifies that set with the interior of the nonpositive
level set. -/
lemma strictLowerLevelSet_zero_eq_interior_lowerLevelSet_zero_of_pointwise_upperSemicontinuousAt
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    (hneg : (strictLowerLevelSet (fun x : H ↦ (f x : EReal)) 0).Nonempty)
    (husc :
      ∀ x ∈ strictLowerLevelSet (fun x : H ↦ (f x : EReal)) 0,
        UpperSemicontinuousAt (fun x : H ↦ (f x : EReal)) x) :
    strictLowerLevelSet (fun x : H ↦ (f x : EReal)) 0 =
      interior (lowerLevelSet (fun x : H ↦ (f x : EReal)) 0) := by
  rcases hneg with ⟨x₀, hx₀⟩
  have hx₀_lt : (f x₀ : EReal) < 0 := by
    simpa [mem_strictLowerLevelSet_iff] using hx₀
  ext x
  constructor
  · intro hx
    have hx_lt : (f x : EReal) < 0 := by
      simpa [mem_strictLowerLevelSet_iff] using hx
    -- Proposition 8.46 sends each strict negative point with ambient upper semicontinuity into
    -- the interior of the nonpositive level set.
    exact mem_interior_lowerLevelSet_zero_of_upperSemicontinuousAt (husc x hx) hx_lt
  · -- The converse inclusion is the convexity part of Proposition 8.46, using any strict
    -- negative anchor point from the nonempty level set.
    intro hx
    exact
      interior_lowerLevelSet_zero_subset_strictLowerLevelSet_zero_of_convexOn hconv hx₀_lt hx

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 8.47: on an open effective domain, continuity of the finite real
representative upgrades to continuity of the original `EReal`-valued function. -/
lemma continuousAt_coe_of_continuousAt_toReal_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal))
    (hopen : IsOpen (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f)
    (hcont : ContinuousAt (fun y : H ↦ (f y : EReal).toReal) x) :
    ContinuousAt (fun y : H ↦ (f y : EReal)) x := by
  let G : H → EReal := fun y ↦ (((f y : EReal).toReal : ℝ) : EReal)
  have hGcont : ContinuousAt G x := by
    -- Compose the real-valued continuity with the continuous coercion `ℝ → EReal`.
    simpa [G] using (continuous_coe_real_ereal.continuousAt.comp hcont)
  have hEq : G =ᶠ[𝓝 x] (fun y : H ↦ (f y : EReal)) := by
    -- Inside the open effective domain, coercing `toReal` back to `EReal` is exact.
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    simpa [G] using (EReal.coe_toReal hy_top hy_bot)
  -- Eventual equality transfers the continuity statement back to the original function.
  exact hGcont.congr hEq

/-- Helper for Corollary 8.47: an open effective domain plus lower semicontinuity or finite
dimensionality makes the function ambiently upper semicontinuous at every strict negative point. -/
lemma
    upperSemicontinuousAt_on_strictLowerLevelSet_zero_of_openDomain_regularity
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    (hopen : IsOpen (effectiveDomain f))
    (hreg : LowerSemicontinuous (fun x : H ↦ (f x : EReal)) ∨ FiniteDimensional ℝ H) :
    ∀ x ∈ strictLowerLevelSet (fun x : H ↦ (f x : EReal)) 0,
      UpperSemicontinuousAt (fun x : H ↦ (f x : EReal)) x := by
  intro x hx
  have hx_dom : x ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    exact lt_trans (by simpa [mem_strictLowerLevelSet_iff] using hx) EReal.zero_lt_top
  have hx_cont_pt :
      x ∈ {x : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f ∧
        ContinuousAt (fun y : H ↦ (f y : EReal).toReal) x} := by
    -- Corollary 8.39 turns the open-domain regularity assumptions into local continuity of the
    -- real representative at every effective-domain point.
    rw
      [continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
        f hconv (Or.inr hreg)]
    simpa [hopen.interior_eq] using hx_dom
  rcases hx_cont_pt with ⟨_ρ, _hρ, _hball, hcont⟩
  -- Route correction: after Corollary 8.39 provides continuity of `toReal`, only the coercion
  -- adapter remains before Proposition 8.46 can be applied.
  exact
    (continuousAt_coe_of_continuousAt_toReal_of_mem_effectiveDomain
      f hopen hx_dom hcont).upperSemicontinuousAt

-- Proof sketch: in case (i), apply ambient pointwise upper semicontinuity at every point of the
-- strict lower level set to obtain a neighborhood on which the function stays negative, hence
-- openness. In cases (ii) and (iii), use continuity on the open effective domain to upgrade to
-- upper semicontinuity on the strict lower level set and reduce to case (i).
/-- Corollary 8.47: if a convex `]-∞,+∞]`-valued function has nonempty strict negative level set
and either is ambiently upper semicontinuous at every point of that set, or is lower
semicontinuous with open effective domain, or is defined on a finite-dimensional space with open
effective domain, then the strict negative level set is open; equivalently, it equals its
interior. -/
theorem
    isOpen_strictLowerLevelSet_zero_of_convexOn_of_upperSemicontinuousOn_or_lowerSemicontinuous_openDomain_or_finiteDimensional_openDomain
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    (hneg : (strictLowerLevelSet (fun x : H ↦ (f x : EReal)) 0).Nonempty)
    (h :
      (∀ x ∈ strictLowerLevelSet (fun x : H ↦ (f x : EReal)) 0,
        UpperSemicontinuousAt (fun x : H ↦ (f x : EReal)) x) ∨
      (IsOpen (effectiveDomain f) ∧
        (LowerSemicontinuous (fun x : H ↦ (f x : EReal)) ∨ FiniteDimensional ℝ H))) :
    IsOpen (strictLowerLevelSet (fun x : H ↦ (f x : EReal)) 0) := by
  rcases h with husc | ⟨hopen, hreg⟩
  · -- Case (i): Proposition 8.46 identifies the strict negative level set with an interior.
    rw [strictLowerLevelSet_zero_eq_interior_lowerLevelSet_zero_of_pointwise_upperSemicontinuousAt
      f hconv hneg husc]
    exact isOpen_interior
  · -- Cases (ii) and (iii): Corollary 8.39 supplies pointwise continuity on the open effective
    -- domain, which upgrades to the ambient upper semicontinuity needed in case (i).
    rw [strictLowerLevelSet_zero_eq_interior_lowerLevelSet_zero_of_pointwise_upperSemicontinuousAt
      f hconv hneg
      (upperSemicontinuousAt_on_strictLowerLevelSet_zero_of_openDomain_regularity
      f hconv hopen hreg)]
    exact isOpen_interior

end ERealFunction
