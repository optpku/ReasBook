/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_6
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.LocallyLipschitzAt
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.OneSidedDirectionalDeriv

noncomputable section

section Chapter14Theorem1418

universe u

-- Domain sampling:
-- * primary domain: finite-dimensional convex real-valued line derivatives and local growth;
-- * sampled canonical directional-derivative owners:
--   `HasLineDerivAt`, `lineDeriv`;
-- * sampled chapter owner-level precedent:
--   `Definition_1_2_27` uses `HasLineDerivAt` / `HasLineDerivWithinAt` as the canonical
--   directional-derivative API;
-- * sampled Chapter 14 local-Lipschitz surface:
--   `clarkeDirectionalDerivative_abs_le` and
--   `norm_le_of_mem_clarkeDifferential_of_closedBallLipschitz`, both stated with an explicit
--   closed-ball `LipschitzOnWith` hypothesis;
-- * sampled mathlib convex regularity owner:
--   `ConvexOn.locallyLipschitz`;
-- * source/core/bridge triage:
--   - source-facing: `convex_hasLinearLowerBound_near_of_pos_lineDeriv`
--   - core/canonical: `HasLineDerivAt`, `lineDeriv`, `ConvexOn`, and `LocallyLipschitzAt`
--   - bridge/view: the companion theorem
--     `convex_hasLinearLowerBound_near_of_pos_lineDeriv_of_locallyLipschitzAt`, which reuses
--     the source-facing closed-ball theorem through the canonical Chapter 14 local owner
-- * primitive data vs derived API:
--   - primitive data: finite-dimensional ambient space, convexity on `Set.univ`, and explicit
--     closed-ball Lipschitz control near `xStar`, together with positivity of the directional
--     line derivative in nonzero directions
--   - derived API: the theorem conclusion itself, plus the local-Lipschitz companion theorem

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- Helper for Chapter14 Theorem 14.1.8: a line derivative at `x` in direction `d` also computes
the one-sided directional derivative along the ray `x + t • d`. -/
lemma oneSidedDirectionalDeriv_eq_of_hasLineDerivAt
    {f : X → ℝ} {x d : X} {m : ℝ}
    (hline : HasLineDerivAt ℝ f m x d) :
    oneSidedDirectionalDeriv f x d = m := by
  -- Reinterpret the line derivative as the right derivative of the same scalar slice.
  have hright : HasOneSidedDirectionalDerivAt f m x d := by
    simpa [HasOneSidedDirectionalDerivAt, HasLineDerivAt] using
      (show HasDerivWithinAt (fun t : ℝ ↦ f (x + t • d)) m (Set.Ici 0) 0 from
        hline.hasDerivWithinAt)
  exact hright.oneSidedDirectionalDeriv_eq

/-- Helper for Chapter14 Theorem 14.1.8: under convexity and local Lipschitz control, the real
Clarke directional derivative agrees with the line derivative whenever the latter exists. -/
lemma clarkeDirectionalDerivReal_eq_lineDeriv_of_hasLineDerivAt
    {f : X → ℝ} {x d : X}
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_local : LocallyLipschitzAt f x)
    (hline : HasLineDerivAt ℝ f (lineDeriv ℝ f x d) x d) :
    clarkeDirectionalDerivReal f x d = lineDeriv ℝ f x d := by
  -- Rewrite the Clarke owner through the chapter's convex bridge and then use the ray derivative.
  simpa [oneSidedDirectionalDeriv_eq_of_hasLineDerivAt hline] using
    clarkeDirectionalDeriv_toReal_eq_oneSidedDirectionalDeriv_of_convexOn_of_locallyLipschitzAt
      f x d h_convex h_local

/-- Helper for Chapter14 Theorem 14.1.8: normalizing a nonzero vector puts it on the unit sphere
`Metric.sphere (0 : X) 1`. -/
lemma invNorm_smul_mem_sphere_zero_one {v : X} (hv : v ≠ 0) :
    ‖v‖⁻¹ • v ∈ Metric.sphere (0 : X) 1 := by
  -- Compute the norm of the normalized vector directly.
  rw [mem_sphere_zero_iff_norm]
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

/-- Helper for Chapter14 Theorem 14.1.8: every point on the unit sphere is nonzero. -/
lemma ne_zero_of_mem_sphere_zero_one {d : X} (hd : d ∈ Metric.sphere (0 : X) 1) :
    d ≠ 0 := by
  -- A unit vector cannot have zero norm.
  rw [mem_sphere_zero_iff_norm] at hd
  exact norm_ne_zero_iff.mp (by simpa [hd] using (one_ne_zero : (1 : ℝ) ≠ 0))

/-- Helper for Chapter14 Theorem 14.1.8: the real Clarke directional derivative is Lipschitz in
the direction variable when the Clarke differential is uniformly bounded on a closed ball. -/
lemma clarkeDirectionalDerivReal_lipschitzWith_of_closedBallLipschitz
    {f : X → ℝ} {x : X} {K : NNReal}
    (h_local : LocallyLipschitzAt f x)
    (hK : ∃ ε : ℝ, 0 < ε ∧ LipschitzOnWith K f (Metric.closedBall x ε)) :
    LipschitzWith K (fun d ↦ clarkeDirectionalDerivReal f x d) := by
  -- Compare two support-function values using maximizers in the bounded Clarke differential.
  refine LipschitzWith.of_dist_le_mul ?_
  intro d₁ d₂
  let g : X → ℝ := fun d ↦ clarkeDirectionalDerivReal f x d
  have hgreat₁ :=
    clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
      f x d₁ h_local
  have hgreat₂ :=
    clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
      f x d₂ h_local
  rcases hgreat₁.1 with ⟨ξ₁, hξ₁, hξ₁eq⟩
  rcases hgreat₂.1 with ⟨ξ₂, hξ₂, hξ₂eq⟩
  have hg₁ : g d₁ = ξ₁ d₁ := by
    simpa [g] using hξ₁eq.symm
  have hg₂ : g d₂ = ξ₂ d₂ := by
    simpa [g] using hξ₂eq.symm
  have hξ₁_on_d₂ : ξ₁ d₂ ≤ g d₂ := hgreat₂.2 ⟨ξ₁, hξ₁, rfl⟩
  have hξ₂_on_d₁ : ξ₂ d₁ ≤ g d₁ := hgreat₁.2 ⟨ξ₂, hξ₂, rfl⟩
  have hξ₁norm : ‖ξ₁‖ ≤ (K : ℝ) :=
    norm_le_of_mem_clarkeDifferential_of_closedBallLipschitz f x K hK hξ₁
  have hξ₂norm : ‖ξ₂‖ ≤ (K : ℝ) :=
    norm_le_of_mem_clarkeDifferential_of_closedBallLipschitz f x K hK hξ₂
  have hsub₁ : g d₁ - g d₂ ≤ (K : ℝ) * ‖d₁ - d₂‖ := by
    calc
      g d₁ - g d₂ = ξ₁ d₁ - g d₂ := by rw [hg₁]
      _ ≤ ξ₁ d₁ - ξ₁ d₂ := by linarith
      _ = ξ₁ (d₁ - d₂) := by rw [map_sub]
      _ ≤ ‖ξ₁ (d₁ - d₂)‖ := by exact le_abs_self _
      _ ≤ ‖ξ₁‖ * ‖d₁ - d₂‖ := by simpa using ξ₁.le_opNorm (d₁ - d₂)
      _ ≤ (K : ℝ) * ‖d₁ - d₂‖ := by
        exact mul_le_mul_of_nonneg_right hξ₁norm (norm_nonneg _)
  have hsub₂ : g d₂ - g d₁ ≤ (K : ℝ) * ‖d₁ - d₂‖ := by
    calc
      g d₂ - g d₁ = ξ₂ d₂ - g d₁ := by rw [hg₂]
      _ ≤ ξ₂ d₂ - ξ₂ d₁ := by linarith
      _ = ξ₂ (d₂ - d₁) := by rw [map_sub]
      _ ≤ ‖ξ₂ (d₂ - d₁)‖ := by exact le_abs_self _
      _ ≤ ‖ξ₂‖ * ‖d₂ - d₁‖ := by simpa using ξ₂.le_opNorm (d₂ - d₁)
      _ ≤ (K : ℝ) * ‖d₁ - d₂‖ := by
        simpa [norm_sub_rev] using
          (mul_le_mul_of_nonneg_right hξ₂norm (norm_nonneg (d₂ - d₁)))
  have habs : |g d₁ - g d₂| ≤ (K : ℝ) * ‖d₁ - d₂‖ := by
    rw [abs_le]
    constructor
    · linarith
    · exact hsub₁
  simpa [g, dist_eq_norm, Real.norm_eq_abs] using habs

/-- Helper for Chapter14 Theorem 14.1.8: convexity on the ambient space gives the standard
one-dimensional secant lower bound for the line derivative along a ray. -/
lemma lineDeriv_le_secant_slope_along_ray
    {f : X → ℝ} {x d : X} {t : ℝ}
    (h_convex : ConvexOn ℝ Set.univ f)
    (hline : HasLineDerivAt ℝ f (lineDeriv ℝ f x d) x d)
    (ht : 0 < t) :
    lineDeriv ℝ f x d ≤ (f (x + t • d) - f x) / t := by
  let ray : ℝ → X := fun s ↦ x + s • d
  have hray_lineMap : ray = AffineMap.lineMap (k := ℝ) x (x + d) := by
    -- The secant ray is the affine line from `x` to `x + d`.
    funext s
    symm
    simpa [ray, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module' x (x + d) s)
  have hray_convex : ConvexOn ℝ Set.univ (f ∘ ray) := by
    -- Restrict the ambient convex function to the affine line through `x` in direction `d`.
    rw [hray_lineMap]
    simpa using (h_convex.comp_affineMap (AffineMap.lineMap (k := ℝ) x (x + d)))
  have hray_deriv : HasDerivAt (f ∘ ray) (lineDeriv ℝ f x d) 0 := by
    -- The line derivative is exactly the derivative of the scalar slice at `0`.
    change HasDerivAt (fun s : ℝ ↦ f (x + s • d)) (lineDeriv ℝ f x d) 0
    simpa [HasLineDerivAt] using hline
  have hsec :=
    hray_convex.le_slope_of_hasDerivAt (by simp) (by simp) ht hray_deriv
  -- Expand the slope formula and simplify the endpoints of the ray.
  simpa [ray, slope_def_field, ht.ne', Function.comp] using hsec

/-- Chapter14 Theorem 14.1.8: on a finite-dimensional real normed space, if `f : X → ℝ` is
convex, Lipschitz on some closed ball centered at `xStar`, and every nonzero direction there has
a positive line derivative, then `f` has a local linear growth bound above `f xStar`.
The public derivative surface is the canonical `HasLineDerivAt ℝ` / `lineDeriv ℝ` owner, and the
local Lipschitz hypothesis remains explicit instead of being absorbed into proof support. -/
theorem convex_hasLinearLowerBound_near_of_pos_lineDeriv
    (f : X → ℝ)
    (xStar : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_lipschitz :
      ∃ ε : ℝ, 0 < ε ∧ ∃ K : NNReal, LipschitzOnWith K f (Metric.closedBall xStar ε))
    (h_line : ∀ d : X, d ≠ 0 → HasLineDerivAt ℝ f (lineDeriv ℝ f xStar d) xStar d)
    (h_pos : ∀ d : X, d ≠ 0 → 0 < lineDeriv ℝ f xStar d) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
      ∀ x : X, ‖x - xStar‖ < ε → δ * ‖x - xStar‖ ≤ f x - f xStar := by
  rcases h_lipschitz with ⟨ε, hε, K, hK⟩
  have h_local : LocallyLipschitzAt f xStar :=
    locallyLipschitzAt_of_closedBall ⟨ε, hε, hK⟩
  rcases subsingleton_or_nontrivial X with hsub | hnontriv
  · letI : Subsingleton X := hsub
    -- In the degenerate space every nearby point equals `xStar`, so the estimate is immediate.
    refine ⟨1, ε, zero_lt_one, hε, ?_⟩
    intro x hx
    have hxeq : x = xStar := Subsingleton.elim x xStar
    subst hxeq
    simp
  · letI : Nontrivial X := hnontriv
    let g : X → ℝ := fun d ↦ clarkeDirectionalDerivReal f xStar d
    have hgLip : LipschitzWith K g :=
      clarkeDirectionalDerivReal_lipschitzWith_of_closedBallLipschitz h_local ⟨ε, hε, hK⟩
    have hgCont : Continuous g := hgLip.continuous
    have hsphereCompact : IsCompact (Metric.sphere (0 : X) 1) := isCompact_sphere (0 : X) 1
    have hsphereNonempty : (Metric.sphere (0 : X) 1).Nonempty := by
      obtain ⟨v, hv⟩ := exists_ne (0 : X)
      exact ⟨‖v‖⁻¹ • v, invNorm_smul_mem_sphere_zero_one hv⟩
    obtain ⟨dMin, hdMinSphere, hdMin⟩ :=
      hsphereCompact.exists_isMinOn hsphereNonempty hgCont.continuousOn
    let δ : ℝ := g dMin
    have hdMinNe : dMin ≠ 0 := ne_zero_of_mem_sphere_zero_one hdMinSphere
    have hδpos : 0 < δ := by
      -- The minimum on the unit sphere is positive because every sphere direction is nonzero.
      have hbridge :
          g dMin = lineDeriv ℝ f xStar dMin :=
        clarkeDirectionalDerivReal_eq_lineDeriv_of_hasLineDerivAt
          h_convex h_local (h_line dMin hdMinNe)
      have hlinePos : 0 < lineDeriv ℝ f xStar dMin := h_pos dMin hdMinNe
      simpa [δ, hbridge] using hlinePos
    refine ⟨δ, ε, hδpos, hε, ?_⟩
    intro x hx
    by_cases hxeq : x = xStar
    · -- At the center point the linear growth inequality is trivial.
      subst hxeq
      simp
    · have hxsub_ne : x - xStar ≠ 0 := sub_ne_zero.mpr hxeq
      have hxnorm_pos : 0 < ‖x - xStar‖ := norm_pos_iff.mpr hxsub_ne
      let d : X := ‖x - xStar‖⁻¹ • (x - xStar)
      have hdSphere : d ∈ Metric.sphere (0 : X) 1 := by
        -- Normalize the displacement to move onto the unit sphere.
        exact invNorm_smul_mem_sphere_zero_one hxsub_ne
      have hdNe : d ≠ 0 := ne_zero_of_mem_sphere_zero_one hdSphere
      have hδleClarke : δ ≤ g d := by
        simpa [δ] using (hdMin hdSphere)
      have hbridge :
          g d = lineDeriv ℝ f xStar d :=
        clarkeDirectionalDerivReal_eq_lineDeriv_of_hasLineDerivAt
          h_convex h_local (h_line d hdNe)
      have hsecant :
          lineDeriv ℝ f xStar d ≤
            (f (xStar + ‖x - xStar‖ • d) - f xStar) / ‖x - xStar‖ :=
        lineDeriv_le_secant_slope_along_ray h_convex (h_line d hdNe) hxnorm_pos
      have hmul :
          δ * ‖x - xStar‖ ≤ f (xStar + ‖x - xStar‖ • d) - f xStar := by
        -- Multiply the secant bound by the positive radius `‖x - xStar‖`.
        exact (le_div_iff₀ hxnorm_pos).mp (by
          calc
            δ ≤ g d := hδleClarke
            _ = lineDeriv ℝ f xStar d := hbridge
            _ ≤ (f (xStar + ‖x - xStar‖ • d) - f xStar) / ‖x - xStar‖ := hsecant)
      have hxray : xStar + ‖x - xStar‖ • d = x := by
        -- The normalized direction reconstructs the original point from its radius.
        dsimp [d]
        rw [smul_smul, mul_inv_cancel₀ (show ‖x - xStar‖ ≠ 0 from ne_of_gt hxnorm_pos), one_smul]
        abel
      simpa [δ, g, hxray] using hmul

/-- Canonical Chapter 14 bridge for Theorem 14.1.8: the source-facing closed-ball Lipschitz
hypothesis can be supplied through the reusable local owner `LocallyLipschitzAt f xStar`. -/
theorem convex_hasLinearLowerBound_near_of_pos_lineDeriv_of_locallyLipschitzAt
    (f : X → ℝ)
    (xStar : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_local : LocallyLipschitzAt f xStar)
    (h_line : ∀ d : X, d ≠ 0 → HasLineDerivAt ℝ f (lineDeriv ℝ f xStar d) xStar d)
    (h_pos : ∀ d : X, d ≠ 0 → 0 < lineDeriv ℝ f xStar d) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
      ∀ x : X, ‖x - xStar‖ < ε → δ * ‖x - xStar‖ ≤ f x - f xStar := by
  rcases h_local.exists_lipschitzOnWith_closedBall with ⟨ε, hε, K, hK⟩
  exact convex_hasLinearLowerBound_near_of_pos_lineDeriv
    f xStar h_convex ⟨ε, hε, K, hK⟩ h_line h_pos

end Chapter14Theorem1418
