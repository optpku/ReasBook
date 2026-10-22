/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.23 is `source-facing`: it states the textbook formula
`h₁ + h₂ = (h₁^* □ h₂^*)^*` for a proper closed convex extended-real-valued function plus an
everywhere-finite convex perturbation. The `core/canonical` owners are already upstream:
Chapter 2's `IsProperExtendedRealFunction`, `is_convex_function`, and `infimal_convolution`,
Mathlib's `LowerSemicontinuous`, and Chapter 4's `conjugate_function` and
`biconjugate_function`. The explicit infimal-convolution/conjugate formula is therefore the main
source-facing declaration here, while the pure owner-form biconjugation equality is only a thin
companion view.

Primitive data: the functions `h₁`, `h₂` and the source hypotheses `hh₁_proper`, `hh₁_closed`,
`hh₁_convex`, `hh₂_convex`. Derived API: the explicit conjugate/infimal-convolution identity and
its owner-form biconjugation companion. The first theorem reuses the chapter owner
`conjugate_function_add_eq_infimal_convolution`, while the companion theorem below is the thin
proper/closed/convex owner view on the summed function and therefore uses the repository theorem
`biconjugate_function_eq_self_of_proper_closed_convex`. -/
recall IsProperExtendedRealFunction
recall is_convex_function
recall infimal_convolution
recall conjugate_function
recall biconjugate_function

/-- Helper for Proposition 4.23: a convex real-valued perturbation on the whole space becomes
lower semicontinuous after coercion to `EReal`. -/
lemma toERealLowerSemicontinuousOfConvexOnUniv
    {h₂ : E → ℝ} (hh₂_convex : ConvexOn ℝ Set.univ h₂) :
    LowerSemicontinuous h₂.toEReal := by
  -- Finite-dimensional convex functions are continuous on the whole space.
  have hh₂_continuous : Continuous h₂ := by
    simpa [continuousOn_univ] using hh₂_convex.continuousOn
  -- The canonical `EReal` lift preserves lower semicontinuity.
  simpa [Function.toEReal] using
    Function.toEReal_lowerSemicontinuous_of_continuous hh₂_continuous

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 4.23: adding an everywhere-finite convex real perturbation preserves
convexity of an extended-real-valued function. -/
lemma isConvexFunctionAddRealLift
    {h₁ : E → EReal} {h₂ : E → ℝ}
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂) :
    is_convex_function (fun x ↦ h₁ x + h₂.toEReal x) := by
  rw [is_convex_function_iff_convex_real_epigraph]
  -- Shift the real epigraph height by the finite perturbation and use convexity of each summand.
  have hh₁_epigraph :
      Convex ℝ {p : E × ℝ | h₁ p.1 ≤ (p.2 : EReal)} :=
    (is_convex_function_iff_convex_real_epigraph h₁).1 hh₁_convex
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, r⟩
  rcases q with ⟨y, s⟩
  simp only [Prod.smul_mk, Prod.mk_add_mk, Set.mem_setOf_eq] at hp hq ⊢
  have hx_shifted : h₁ x ≤ ((r - h₂ x : ℝ) : EReal) := by
    have hp_cancel := add_le_add_right hp (((-h₂ x : ℝ) : EReal))
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, ← EReal.coe_neg,
      ← EReal.coe_add] using hp_cancel
  have hy_shifted : h₁ y ≤ ((s - h₂ y : ℝ) : EReal) := by
    have hq_cancel := add_le_add_right hq (((-h₂ y : ℝ) : EReal))
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, ← EReal.coe_neg,
      ← EReal.coe_add] using hq_cancel
  have hx_mem : (x, r - h₂ x) ∈ {p : E × ℝ | h₁ p.1 ≤ (p.2 : EReal)} := by
    simpa using hx_shifted
  have hy_mem : (y, s - h₂ y) ∈ {p : E × ℝ | h₁ p.1 ≤ (p.2 : EReal)} := by
    simpa using hy_shifted
  have hz_shifted_mem := hh₁_epigraph hx_mem hy_mem ha hb hab
  have hz_shifted :
      h₁ (a • x + b • y) ≤ ((a * (r - h₂ x) + b * (s - h₂ y) : ℝ) : EReal) := by
    simpa [smul_eq_mul] using hz_shifted_mem
  have hx_univ : x ∈ Set.univ := by simp
  have hy_univ : y ∈ Set.univ := by simp
  have hh₂_combo :
      h₂ (a • x + b • y) ≤ a * h₂ x + b * h₂ y := by
    simpa [smul_eq_mul] using hh₂_convex.2 hx_univ hy_univ ha hb hab
  calc
    h₁ (a • x + b • y) + (h₂ (a • x + b • y) : EReal)
        ≤ ((a * (r - h₂ x) + b * (s - h₂ y) : ℝ) : EReal)
          + ((a * h₂ x + b * h₂ y : ℝ) : EReal) := by
            exact add_le_add hz_shifted (by exact_mod_cast hh₂_combo)
    _ = ((a * (r - h₂ x) + b * (s - h₂ y) + (a * h₂ x + b * h₂ y) : ℝ) : EReal) := by
      rw [← EReal.coe_add]
    _ = ((a * r + b * s : ℝ) : EReal) := by
      congr 1
      ring

/-- Helper for Proposition 4.23: the sum of a closed convex extended-real-valued function and an
everywhere-finite convex real perturbation is again closed and convex. -/
lemma addRealLiftClosedConvex
    {h₁ : E → EReal} {h₂ : E → ℝ}
    (hh₁_closed : LowerSemicontinuous h₁)
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂) :
    LowerSemicontinuous (fun x ↦ h₁ x + h₂.toEReal x) ∧
      is_convex_function (fun x ↦ h₁ x + h₂.toEReal x) := by
  constructor
  · -- Lower semicontinuity is stable under addition once the finite-valued summand supplies
    -- continuity of `EReal` addition at every point.
    have hh₂_closed : LowerSemicontinuous h₂.toEReal :=
      toERealLowerSemicontinuousOfConvexOnUniv hh₂_convex
    refine hh₁_closed.add' hh₂_closed ?_
    intro x
    exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  · -- Convexity is the specialized epigraph argument from `isConvexFunctionAddRealLift`.
    exact isConvexFunctionAddRealLift hh₁_convex hh₂_convex

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma isProperExtendedRealFunction_addRealLift
    {h₁ : E → EReal} {h₂ : E → ℝ}
    (hh₁_proper : IsProperExtendedRealFunction h₁) :
    IsProperExtendedRealFunction (fun x ↦ h₁ x + h₂.toEReal x) := by
  refine ⟨?_, ?_⟩
  · intro x
    cases hx : h₁ x with
    | bot =>
        exact False.elim (hh₁_proper.ne_bot x hx)
    | coe r =>
        rw [Function.toEReal, EReal.add_ne_bot_iff]
        exact ⟨EReal.coe_ne_bot r, EReal.coe_ne_bot (h₂ x)⟩
    | top =>
        simp [Function.toEReal]
  · rcases hh₁_proper.effective_domain_nonempty with ⟨x, hx⟩
    have hx_top : h₁ x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hx)
    lift h₁ x to ℝ using ⟨hx_top, hh₁_proper.ne_bot x⟩ with r hr
    refine ⟨x, ?_⟩
    rw [mem_effective_domain, ← hr]
    simpa [Function.toEReal, EReal.coe_add] using EReal.coe_lt_top (r + h₂ x)

-- Proof sketch: let `f := fun x ↦ h₁ x + h₂.toEReal x`. Because `h₂` is real-valued convex on
-- the whole space, it is continuous and hence lower semicontinuous in the finite-dimensional
-- setting, so `f` is again closed and convex. Apply the chapter-owner biconjugation theorem to
-- `f`, then rewrite `f*` using the preceding source-facing conjugate-of-sum theorem
-- `conjugate_function_add_eq_infimal_convolution`.
/-- Proposition 4.23: if `h₁` is a proper closed convex extended-real-valued
function and `h₂` is a real-valued convex function on the whole space, then the
pointwise sum `h₁ + h₂` equals the primal-side conjugate of the infimal
convolution `h₁^* □ h₂^*`. This is the source-facing chapter rendering of the
textbook identity `h₁ + h₂ = (h₁^* □ h₂^*)^*`. -/
theorem proper_closed_convex_add_real_convex_eq_conjugate_infimal_convolution
    (h₁ : E → EReal) (h₂ : E → ℝ)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_closed : LowerSemicontinuous h₁)
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂) :
    (fun x ↦ h₁ x + h₂.toEReal x) =
      fun x ↦
        conjugate_function
          (conjugate_function h₁ □ conjugate_function h₂.toEReal)
          (Module.Dual.eval ℝ E x) := by
  -- First identify the summed function with its biconjugate via the closed/convex owner theorem.
  rcases addRealLiftClosedConvex hh₁_closed hh₁_convex hh₂_convex with
    ⟨hsum_closed, hsum_convex⟩
  have hsum_proper :
      IsProperExtendedRealFunction (fun x ↦ h₁ x + h₂.toEReal x) :=
    isProperExtendedRealFunction_addRealLift hh₁_proper
  have hsum_biconjugate :
      (fun x ↦ h₁ x + h₂.toEReal x) =
        biconjugate_function (fun x ↦ h₁ x + h₂.toEReal x) := by
    simpa using
      (biconjugate_function_eq_self_of_proper_closed_convex
        (fun x ↦ h₁ x + h₂.toEReal x) hsum_proper hsum_closed hsum_convex).symm
  -- Then rewrite the inner conjugate by the Chapter 4 sum formula.
  calc
    (fun x ↦ h₁ x + h₂.toEReal x)
        = biconjugate_function (fun x ↦ h₁ x + h₂.toEReal x) := hsum_biconjugate
    _ = fun x ↦
          conjugate_function
            (conjugate_function h₁ □ conjugate_function h₂.toEReal)
            (Module.Dual.eval ℝ E x) := by
              ext x
              rw [biconjugate_function]
              rw [conjugate_function_add_eq_infimal_convolution
                h₁ h₂ hh₁_proper hh₁_convex hh₂_convex]

-- Proof sketch: apply the chapter biconjugation theorem directly to the sum
-- `fun x ↦ h₁ x + h₂.toEReal x`. This is the owner-form companion to the explicit
-- source-facing formula in `proper_closed_convex_add_real_convex_eq_conjugate_infimal_convolution`,
-- and the Chapter 4 owner `biconjugate_function_eq_self_of_proper_closed_convex` keeps the
-- textbook properness hypothesis explicit at this companion layer as well.
/-- Owner-form companion: the sum `h₁ + h₂`, viewed as an `EReal`-valued
function, equals its biconjugate. -/
theorem proper_closed_convex_add_real_convex_eq_biconjugate
    (h₁ : E → EReal) (h₂ : E → ℝ)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_closed : LowerSemicontinuous h₁)
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂) :
    (fun x ↦ h₁ x + h₂.toEReal x) = biconjugate_function (fun x ↦ h₁ x + h₂.toEReal x) := by
  -- Route correction: the companion theorem uses the proper/closed/convex owner directly, without
  -- re-running the source-facing conjugate-of-sum theorem.
  rcases addRealLiftClosedConvex hh₁_closed hh₁_convex hh₂_convex with
    ⟨hsum_closed, hsum_convex⟩
  have hsum_proper :
      IsProperExtendedRealFunction (fun x ↦ h₁ x + h₂.toEReal x) :=
    isProperExtendedRealFunction_addRealLift hh₁_proper
  simpa using
    (biconjugate_function_eq_self_of_proper_closed_convex
      (fun x ↦ h₁ x + h₂.toEReal x) hsum_proper hsum_closed hsum_convex).symm

end
