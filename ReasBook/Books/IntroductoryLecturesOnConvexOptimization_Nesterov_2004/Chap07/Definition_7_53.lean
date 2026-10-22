/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_52

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConstrainedArgmin

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 7.53 lies in the chapter's barrier-smoothed support-function domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjective` in `Chap06/Definition_6_30`, the chapter owner of regularized
  supremum constructions of the form `hatf x + sup_u (A x u - hatφ u - μ d₂ u)`;
- `smoothedPrimalObjectiveArgmax` and `mem_smoothedPrimalObjectiveArgmax_iff` in
  `Chap06/Definition_6_30`, the canonical argmax owner and its feasibility/maximality bridge;
- mathlib `IsMaxOn`, the primitive maximality predicate used by the owner bridge.

Best owner abstraction:
- source-facing: Definition 7.53's smooth support-function approximation `Uβ` together with its
  maximizer owner `Argmaxβ`, representing
  `U_β(s) = max_{u ∈ hatP} {⟨s, u - x₀⟩ - β (F(u) - F(x₀))}`;
- core/canonical: `smoothedPrimalObjective` and `smoothedPrimalObjectiveArgmax`, specialized to
  the identity dual map on `StrongDual ℝ E`, zero dual penalty, and prox term `F`;
- bridge/view: the expansion theorems below, which rewrite `Uβ` and `Argmaxβ` back to the
  textbook support-function formula and maximizer condition.

Primitive data:
- the feasible set `hatP`, barrier term `F`, base point `x₀`, smoothing parameter `β`, and the
  dual variable `s`.

Derived API:
- the value function owner `Uβ`, via the Chapter 6 owner `smoothedPrimalObjective`;
- the maximizer owner `Argmaxβ`, via `smoothedPrimalObjectiveArgmax`;
- the textbook support-function formula and feasible-maximizer characterization, via thin
  companion theorems.

The previous version introduced a second public owner
`SmoothSupportFunctionApproximationSetup` together with exact duplicate-wheel wrappers for the
maximand, value function, and argmax set. Those notions are already owned by
`smoothedPrimalObjective` and `smoothedPrimalObjectiveArgmax`. This file therefore refines
Definition 7.53 to a thin source-facing owner layer `Uβ` / `Argmaxβ` on top of the Chapter 6
owners, keeping only the textbook formula and argmax bridges as derived API.
-/

section

variable (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β})
variable (s : StrongDual ℝ E) (u : E)

/- Definition 7.53's smoothed support-function approximation `Uβ` is the Chapter 6 regularized-max
owner specialized to the identity dual map, the feasible set `hatP`, zero dual penalty, prox term
`F`, and affine base term `s ↦ -s x₀ + β F(x₀)`. Its maximizer layer `Argmaxβ` is the
corresponding canonical argmax owner. -/
recall smoothedPrimalObjective
recall smoothedPrimalObjectiveMaximand
recall smoothedPrimalObjective_apply
recall smoothedPrimalObjectiveArgmax
recall mem_smoothedPrimalObjectiveArgmax_iff

/-- Definition 7.53 (Smooth approximation of the support function): let `Q ⊆ E` be the ambient
barrier set, let `hatP ⊆ E` be the outer feasible set, put `P = hatP ∩ Q`, and let `x₀` be the
constrained analytic center of `P`. For `β > 0`, the smooth support-function approximation `U_β`
is the Chapter 6 regularized-max owner specialized to the textbook payoff
`u ↦ s (u - x₀) - β * (F u - F x₀)`, with the base-point shift kept in the owner data. -/
abbrev Uβ (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β}) :
    StrongDual ℝ E → ℝ :=
  smoothedPrimalObjective
    (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
    hatP
    (fun t : StrongDual ℝ E ↦ -t x0 + (β : ℝ) * F x0)
    0
    F
    (β : ℝ)

-- Proof sketch: unfold `Uβ`; the result is the defining Chapter 6 specialization of the whole
-- owner.
/-- Expanding `Uβ` recovers its Chapter 6 owner specialization. -/
@[simp] theorem Uβ_def
    (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β}) :
    Uβ hatP F x0 β =
      smoothedPrimalObjective
        (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
        hatP
        (fun t : StrongDual ℝ E ↦ -t x0 + (β : ℝ) * F x0)
        0
        F
        (β : ℝ) := by
  -- `Uβ` is definitionally the indicated Chapter 6 specialization.
  rfl

-- Proof sketch: unfold `Uβ`, then expand `smoothedPrimalObjective_apply` and simplify the
-- specialized Chapter 6 maximand.
/-- Evaluating `Uβ` gives the textbook affine-term plus supremum formula. -/
@[simp] theorem Uβ_apply
    (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) :
    Uβ hatP F x0 β s =
      -s x0 + β * F x0 +
        sSup ((fun u : E ↦ s u - β * F u) '' hatP) := by
  -- Expand the owner specialization to expose the penalized supremum.
  rw [Uβ_def, smoothedPrimalObjective_apply]
  -- Identify the specialized Chapter 6 maximand with the source score `u ↦ s u - β F u`.
  refine congrArg (fun t : Set ℝ ↦ -s x0 + β * F x0 + sSup t) ?_
  ext y
  constructor <;> intro hy
  · rcases hy with ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp [smoothedPrimalObjectiveMaximand]
  · rcases hy with ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp [smoothedPrimalObjectiveMaximand]

/-- Helper for Definition 7.53: the textbook payoff is the canonical Chapter 6 score plus the
constant shift `-s x₀ + β F(x₀)`. -/
theorem support_payoff_eq_shifted_score
    (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) (u : E) :
    s (u - x0) - β * (F u - F x0) =
      (-s x0 + β * F x0) + (s u - β * F u) := by
  -- Expand the linear and scalar subtraction terms, then collect the additive constant.
  rw [map_sub, mul_sub]
  ring

-- lean_leansearch recall: `OrderIso.addRight` gives the conditional-supremum constant-shift
-- identity, and `isMaxOn_const` is the matching maximizer-side translation lemma.
/- Route correction: the owner-first proof route is correct, but transporting `sSup` across the
support-function constant shift needs the score image to be nonempty and bounded above. The helper
theorems below record that valid conditional-complete-lattice translation step explicitly. -/
/-- Helper for Definition 7.53: translating a nonempty bounded-above subset of `ℝ` by a constant
shifts its conditional supremum by the same constant. -/
theorem nesterovSSup_image_add_const
    (c : ℝ) {S : Set ℝ} (hS_nonempty : S.Nonempty) (hS_bddAbove : BddAbove S) :
    sSup ((fun z : ℝ ↦ z + c) '' S) = sSup S + c := by
  -- Move the conditional supremum through the additive order isomorphism `z ↦ z + c`.
  simpa using ((OrderIso.addRight c).map_csSup' hS_nonempty hS_bddAbove).symm

/-- Helper for Definition 7.53: the textbook value formula holds once the canonical score image is
nonempty and bounded above, which are exactly the hypotheses needed to move `sSup` through the
constant shift. -/
theorem Uβ_textbook_formula_of_nonempty_bddAbove
    (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E)
    (hhatP_nonempty : hatP.Nonempty)
    (hscore_bddAbove : BddAbove ((fun u : E ↦ s u - β * F u) '' hatP)) :
    Uβ hatP F x0 β s =
      sSup ((fun u : E ↦ s (u - x0) - β * (F u - F x0)) '' hatP) := by
  let c : ℝ := -s x0 + β * F x0
  let score : E → ℝ := fun u ↦ s u - β * F u
  let payoff : E → ℝ := fun u ↦ s (u - x0) - β * (F u - F x0)
  have hscore_nonempty : (score '' hatP).Nonempty := hhatP_nonempty.image score
  have hpayoff_image :
      payoff '' hatP = (fun z : ℝ ↦ z + c) '' (score '' hatP) := by
    -- Rewrite the textbook image pointwise as the shifted canonical score image.
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨score u, ⟨u, hu, rfl⟩, ?_⟩
      dsimp [payoff, score, c]
      simpa [add_comm, add_left_comm, add_assoc] using
        (support_payoff_eq_shifted_score F x0 β s u).symm
    · rintro ⟨z, ⟨u, hu, rfl⟩, hy⟩
      refine ⟨u, hu, ?_⟩
      dsimp [score, payoff, c] at hy ⊢
      have hshift :
          s (u - x0) - β * (F u - F x0) = (-s x0 + β * F x0) + (s u - β * F u) :=
        support_payoff_eq_shifted_score F x0 β s u
      calc
        s (u - x0) - β * (F u - F x0) = (-s x0 + β * F x0) + (s u - β * F u) := hshift
        _ = y := by simpa [add_comm, add_left_comm, add_assoc] using hy
  -- Start from the owner formula, then move the conditional supremum through the constant shift.
  calc
    Uβ hatP F x0 β s = c + sSup (score '' hatP) := by
      rw [Uβ_apply]
    _ = sSup ((fun z : ℝ ↦ z + c) '' (score '' hatP)) := by
      symm
      simpa [add_comm] using
        nesterovSSup_image_add_const c hscore_nonempty hscore_bddAbove
    _ = sSup (payoff '' hatP) := by rw [hpayoff_image]

-- Proof sketch: combine `Uβ_apply` with linearity of `s` to absorb the additive constant
-- `-s x₀ + β * F x₀` into the textbook payoff `u ↦ s (u - x₀) - β (F u - F x₀)`.
/-- Helper for Definition 7.53: if `x₀` is the constrained analytic center from Definition 7.52 of
`P = hatP ∩ Q`, then evaluating the Chapter 6 owner `U_β` recovers the textbook support-function
payoff `u ↦ s (u - x₀) - β (F u - F x₀)` over `hatP`, provided the canonical score image is
nonempty and bounded above. -/
theorem Uβ_textbook_formula
    (hatP Q : Set E) (F : E → ℝ) (x0 : E)
    (hx0 : x0 ∈ argmin[hatP ∩ interior Q] F)
    (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E)
    (hhatP_nonempty : hatP.Nonempty)
    (hscore_bddAbove : BddAbove ((fun u : E ↦ s u - β * F u) '' hatP)) :
    Uβ hatP F x0 β s =
      sSup ((fun u : E ↦ s (u - x0) - β * (F u - F x0)) '' hatP) := by
  let _ : x0 ∈ argmin[hatP ∩ interior Q] F := hx0
  exact Uβ_textbook_formula_of_nonempty_bddAbove
    hatP F x0 β s hhatP_nonempty hscore_bddAbove

/-- Helper for Definition 7.53: the canonical score `v ↦ s v - β F(v)` and the textbook payoff
`v ↦ s (v - x₀) - β (F(v) - F(x₀))` define the same `IsMaxOn` predicate on `hatP`. -/
theorem isMaxOn_shifted_score_iff_textbook_payoff
    (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) (u : E) :
    IsMaxOn (fun v : E ↦ s v - β * F v) hatP u ↔
      IsMaxOn (fun v : E ↦ s (v - x0) - β * (F v - F x0)) hatP u := by
  let c : ℝ := -s x0 + β * F x0
  have hrewrite :
      (fun v : E ↦ s (v - x0) - β * (F v - F x0)) =
        fun v : E ↦ (s v - β * F v) + c := by
    -- Rewrite the textbook payoff as the owner score plus a constant.
    funext v
    simpa [c, add_comm, add_left_comm, add_assoc] using
      support_payoff_eq_shifted_score F x0 β s v
  rw [hrewrite]
  constructor
  · intro h
    -- Adding a constant does not change maximizers.
    simpa [c] using
      h.add (isMaxOn_const : IsMaxOn (fun _ : E ↦ c) hatP u)
  · intro h
    -- Subtract the same constant to return to the canonical owner score.
    simpa [c] using
      h.sub (isMinOn_const : IsMinOn (fun _ : E ↦ c) hatP u)

/-- The canonical feasible-maximizer owner for the support-function approximation `U_β`. The
base-point shift does not appear because it contributes only an additive constant in `u`. -/
abbrev Argmaxβ (hatP : Set E) (F : E → ℝ) (β : {β : ℝ // 0 < β}) :
    StrongDual ℝ E → Set E :=
  smoothedPrimalObjectiveArgmax
    (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
    hatP
    0
    F
    (β : ℝ)

set_option linter.hashCommand false in
#check
  Uβ hatP F x0 β s

set_option linter.hashCommand false in
#check
  Argmaxβ hatP F β s

set_option linter.hashCommand false in
#check
  u ∈ Argmaxβ hatP F β s

end

-- Proof sketch: expand `Argmaxβ` with `mem_smoothedPrimalObjectiveArgmax_iff`, then rewrite the
-- maximand by separating the additive constant `-s x₀ + β * F x₀`, which does not affect `IsMaxOn`.
/-- If `x₀` is the constrained analytic center from Definition 7.52 of `P = hatP ∩ Q`, then
membership in the source-facing argmax owner `Argmaxβ` is exactly feasibility in `hatP`
together with maximality for the textbook payoff `u ↦ s (u - x₀) - β (F u - F x₀)`. -/
@[simp] theorem mem_Argmaxβ_iff
    {hatP Q : Set E} {F : E → ℝ} {x0 : E}
    (hx0 : x0 ∈ argmin[hatP ∩ interior Q] F)
    {β : {β : ℝ // 0 < β}}
    {s : StrongDual ℝ E} {u : E} :
    u ∈ Argmaxβ hatP F β s ↔
      u ∈ hatP ∧
        IsMaxOn
          (fun v : E ↦ s (v - x0) - β * (F v - F x0))
          hatP
          u := by
  let _ : x0 ∈ argmin[hatP ∩ interior Q] F := hx0
  -- Unpack the canonical Chapter 6 argmax owner into feasibility and owner-score maximality.
  rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff]
  have hmaximand :
      smoothedPrimalObjectiveMaximand
          (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
          0
          F
          (β : ℝ)
          s =
        (fun v : E ↦ s v - β * F v) := by
    -- The specialized Chapter 6 maximand is exactly the canonical score.
    funext v
    simp [smoothedPrimalObjectiveMaximand]
  constructor
  · rintro ⟨hu, hmax⟩
    have hscore : IsMaxOn (fun v : E ↦ s v - β * F v) hatP u := by
      simpa [hmaximand] using hmax
    -- Translate maximality from the owner score to the textbook shifted payoff.
    exact ⟨hu, (isMaxOn_shifted_score_iff_textbook_payoff hatP F x0 β s u).mp hscore⟩
  · rintro ⟨hu, hmax⟩
    have hscore : IsMaxOn (fun v : E ↦ s v - β * F v) hatP u := by
      exact (isMaxOn_shifted_score_iff_textbook_payoff hatP F x0 β s u).mpr hmax
    -- Repackage the translated maximality back into the Chapter 6 owner maximand.
    exact ⟨hu, by simpa [hmaximand] using hscore⟩

end
