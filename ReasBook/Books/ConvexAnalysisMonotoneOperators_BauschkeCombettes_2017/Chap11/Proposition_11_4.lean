/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
  [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]

omit [AddCommGroup H] [Module ℝ H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
private theorem isLocalMinOn_toReal_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x : H}
    (hlocal : IsLocalMin f.asEReal x) :
    IsLocalMinOn (fun y : H ↦ (f y : EReal).toReal) (effectiveDomain f) x := by
  rw [IsLocalMinOn, IsMinFilter]
  have hlocalDom : IsLocalMinOn f.asEReal (effectiveDomain f) x := hlocal.on (effectiveDomain f)
  rw [IsLocalMinOn, IsMinFilter] at hlocalDom
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  filter_upwards [self_mem_nhdsWithin, hlocalDom] with y hy_dom hy_min
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  exact EReal.toReal_le_toReal hy_min hx_bot (ne_of_lt (mem_effectiveDomain_iff.mp hy_dom))

/-- Bridge lemma: a finite-valued local minimizer of a convex `]-∞,+∞]`-valued function is a
global minimizer in `IsMinOn` form. -/
theorem isMinOn_univ_of_isLocalMin_of_convexOn_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f)
    (hlocal : IsLocalMin f.asEReal x) :
    IsMinOn f.asEReal Set.univ x := by
  have hminToReal :
      IsMinOn (fun y : H ↦ (f y : EReal).toReal) (effectiveDomain f) x :=
    IsMinOn.of_isLocalMinOn_of_convexOn hx
      (isLocalMinOn_toReal_effectiveDomain f hlocal)
      hconv.toReal_convexOn_effectiveDomain
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  rw [isMinOn_univ_iff]
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · have hxy : (f x : EReal).toReal ≤ (f y : EReal).toReal := hminToReal hy
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    calc
      (f x : EReal) = (((f x : EReal).toReal : ℝ) : EReal) := by
        symm
        exact EReal.coe_toReal hx_top hx_bot
      _ ≤ (((f y : EReal).toReal : ℝ) : EReal) := by
        exact_mod_cast hxy
      _ = (f y : EReal) := by
        exact EReal.coe_toReal hy_top hy_bot
  · have hy_top : (f y : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
    change (f x : EReal) ≤ (f y : EReal)
    rw [hy_top]
    exact le_top

/-- Proposition 11.4: a finite-valued local minimizer of a convex `]-∞,+∞]`-valued function is a
global minimizer. -/
-- Proof sketch: convert the local minimum to a global `IsMinOn` statement on `Set.univ`, then
-- rewrite that conclusion as membership in `Argmin`.
theorem mem_argmin_of_isLocalMin_of_convexOn_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f)
    (hlocal : IsLocalMin f.asEReal x) :
    x ∈ Argmin f.asEReal := by
  exact mem_argmin_iff.mpr <|
    isMinOn_univ_of_isLocalMin_of_convexOn_effectiveDomain f hconv hx hlocal

/-- Companion bridge: a neighborhood argmin witness yields the local-minimum hypothesis from
Proposition 11.4. -/
theorem mem_argmin_of_mem_argminOn_nhds_of_convexOn
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H}
    (hlocal : ∃ s ∈ nhds x, x ∈ effectiveDomain f ∧
      x ∈ Argmin[s] f.asEReal) :
    x ∈ Argmin f.asEReal := by
  rcases hlocal with ⟨s, hs, hx, hargmin⟩
  have hmin : IsMinOn f.asEReal s x := (mem_argminOn_iff.mp hargmin).2
  exact mem_argmin_of_isLocalMin_of_convexOn_effectiveDomain f hconv hx (hmin.isLocalMin hs)

/-- Companion bridge: the neighborhood-argmin formulation of Proposition 11.4 in `IsMinOn` form.
-/
theorem isMinOn_univ_of_mem_argminOn_nhds_of_convexOn
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H}
    (hlocal : ∃ s ∈ nhds x, x ∈ effectiveDomain f ∧
      x ∈ Argmin[s] f.asEReal) :
    IsMinOn f.asEReal Set.univ x :=
  mem_argmin_iff.mp <| mem_argmin_of_mem_argminOn_nhds_of_convexOn f hconv hlocal

end ERealFunction
