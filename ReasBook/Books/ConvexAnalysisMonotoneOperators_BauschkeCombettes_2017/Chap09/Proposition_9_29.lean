/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_48
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Helper for Proposition 9.29: bounding the recession-function value by a real number is
equivalent to bounding every translated increment over the effective domain by that same real
number. -/
private lemma recessionFunction_le_iff_forall_increment_le
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty)
    {y : H} {η : ℝ} :
    (recessionFunction f hdom y : EReal) ≤ η ↔
      ∀ x ∈ effectiveDomain f, (f (x + y) : EReal) - (f x : EReal) ≤ η := by
  -- Unfold the defining supremum and identify its image points with translated increments.
  rw [recessionFunction_apply, sSup_le_iff]
  constructor
  · intro hs x hx
    exact hs _ ⟨x, hx, rfl⟩
  · intro hinc z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact hinc x hx

/-- Helper for Proposition 9.29: every effective-domain point gives a canonical real-height point
of the epigraph. -/
private lemma mem_epigraph_toReal_of_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) :
    (x, (f x : EReal).toReal) ∈ epigraph (fun z : H ↦ (f z : EReal)) := by
  -- Finiteness of `f x` makes `(f x).toReal` a valid real ordinate above `f x`.
  rw [mem_epigraph_iff]
  exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hx))

/-- Helper for Proposition 9.29: a real-height epigraph point has base point in the effective
domain, and its ordinate dominates the function value there. -/
private lemma effectiveDomain_and_value_le_of_mem_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hξ : (x, ξ) ∈ epigraph (fun z : H ↦ (f z : EReal))) :
    x ∈ effectiveDomain f ∧ (f x : EReal) ≤ ξ := by
  -- A real epigraph ordinate bounds `f x` by something strictly below `⊤`.
  have hfx_le : (f x : EReal) ≤ ξ := (mem_epigraph_iff _ _ _).mp hξ
  have hx : x ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hfx_le (EReal.coe_lt_top ξ)
  exact ⟨hx, hfx_le⟩

/-- Helper for Proposition 9.29: belonging to the recession cone of the real-height epigraph is
equivalent to the textbook translated-increment inequality. -/
private lemma mem_recessionCone_epigraph_iff_forall_increment_le
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} {η : ℝ} :
    (y, η) ∈ Set.recessionCone (epigraph (fun z : H ↦ (f z : EReal))) ↔
      ∀ x ∈ effectiveDomain f, (f (x + y) : EReal) - (f x : EReal) ≤ η := by
  rw [Set.mem_recessionCone_iff]
  constructor
  · intro hrec x hx
    -- Test the recession-cone condition on the canonical finite-height epigraph point at `x`.
    have hx_epi :
        (x, (f x : EReal).toReal) ∈ epigraph (fun z : H ↦ (f z : EReal)) :=
      mem_epigraph_toReal_of_mem_effectiveDomain (f := f) hx
    have htranslate_mem :
        (x + y, (f x : EReal).toReal + η) ∈
          ({(y, η)} : Set (H × ℝ)) + epigraph (fun z : H ↦ (f z : EReal)) := by
      exact Set.mem_add.2 ⟨(y, η), by simp, (x, (f x : EReal).toReal), hx_epi, by simp [add_comm]⟩
    have hxy_epi :
        (x + y, (f x : EReal).toReal + η) ∈ epigraph (fun z : H ↦ (f z : EReal)) :=
      hrec htranslate_mem
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hxy_le_add :
        (f (x + y) : EReal) ≤ (η : EReal) + (f x : EReal) := by
      -- Reinterpret translated epigraph membership as an `EReal` inequality with the finite value `f x`.
      have hraw :
          (f (x + y) : EReal) ≤ (((f x : EReal).toReal + η : ℝ) : EReal) :=
        (mem_epigraph_iff _ _ _).mp hxy_epi
      simpa [EReal.coe_toReal hx_top hx_bot, add_comm, add_left_comm, add_assoc] using hraw
    -- Move the finite term `f x` back to the left-hand side to recover the increment bound.
    exact
      (EReal.sub_le_iff_le_add (.inl hx_bot) (.inl hx_top)).2
        (by simpa [add_comm] using hxy_le_add)
  · intro hinc s hs
    -- Unpack one translated epigraph point and apply the increment bound at its base point.
    rcases Set.mem_add.1 hs with ⟨p, hp, q, hq, rfl⟩
    have hp' : p = (y, η) := by
      simpa using hp
    subst p
    rcases q with ⟨x, ξ⟩
    rcases effectiveDomain_and_value_le_of_mem_epigraph (f := f) (by simpa using hq) with
      ⟨hx, hfx_le_ξ⟩
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hxy_le_add :
        (f (x + y) : EReal) ≤ (η : EReal) + (f x : EReal) :=
      (EReal.sub_le_iff_le_add (.inl hx_bot) (.inl hx_top)).1 (hinc x hx)
    have hxy_le_height :
        (f (x + y) : EReal) ≤ (η : EReal) + ξ := by
      exact le_trans hxy_le_add (by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hfx_le_ξ (η : EReal))
    -- The translated height stays in the epigraph, so the translate belongs to the epigraph.
    simpa [mem_epigraph_iff, add_comm, add_left_comm, add_assoc] using hxy_le_height

-- Proof sketch: unfold membership in both sides. A point `(y, η)` belongs to the epigraph of the
-- recession function exactly when every translated increment `f (x + y) - f x` is bounded by `η`
-- for `x` in the effective domain. Rewrite this as stability of `epigraph (fun x ↦ (f x : EReal))`
-- under translation by `(y, η)`, which is precisely membership in its recession cone.
/-- Proposition 9.29: for a proper convex `]-∞,+∞]`-valued function, the epigraph of its
recession function is the recession cone of the epigraph. -/
theorem epigraph_recessionFunction_eq_recessionCone_epigraph
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) :
    epigraph (fun y : H ↦ (recessionFunction f hconv.nonempty y : EReal)) =
      Set.recessionCone (epigraph (fun y : H ↦ (f y : EReal))) := by
  ext p
  rcases p with ⟨y, η⟩
  constructor
  · intro hp
    -- Rewrite left-side epigraph membership into the common translated-increment inequality.
    have hinc :
        ∀ x ∈ effectiveDomain f, (f (x + y) : EReal) - (f x : EReal) ≤ η := by
      have hleft : (recessionFunction f hconv.nonempty y : EReal) ≤ η :=
        (mem_epigraph_iff _ _ _).mp hp
      exact
        (recessionFunction_le_iff_forall_increment_le
          (f := f) (hdom := hconv.nonempty) (y := y) (η := η)).1 hleft
    -- The same inequality is exactly the recession-cone condition for the real-height epigraph.
    exact
      (mem_recessionCone_epigraph_iff_forall_increment_le
        (f := f) (y := y) (η := η)).2 hinc
  · intro hp
    -- Rewrite right-side recession-cone membership into the same translated-increment inequality.
    have hinc :
        ∀ x ∈ effectiveDomain f, (f (x + y) : EReal) - (f x : EReal) ≤ η :=
      (mem_recessionCone_epigraph_iff_forall_increment_le
        (f := f) (y := y) (η := η)).1 hp
    have hleft : (recessionFunction f hconv.nonempty y : EReal) ≤ η :=
      (recessionFunction_le_iff_forall_increment_le
        (f := f) (hdom := hconv.nonempty) (y := y) (η := η)).2 hinc
    -- Convert the common inequality back to left-side epigraph membership.
    exact (mem_epigraph_iff _ _ _).2 hleft

end ERealFunction
