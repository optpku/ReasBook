/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_27
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` did not surface a relevant intrinsic breakpoint owner
-- for this exercise, so this file reuses the Chapter 6 symmetry owner
-- `satisfies_symmetry_condition`, the chapter's one-dimensional piecewise-linear owner, and the
-- Chapter 6 subadditivity owner `Function.Subadditive`.

section Exercise617

/-- In dimension `q = 1`, the Chapter 6 symmetry owner is exactly the scalar relation
`π(r) + π(-f-r) = 1`. -/
theorem satisfies_symmetry_condition_real_iff {f : ℝ} {π : ℝ → ℝ} :
    satisfies_symmetry_condition (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π (r 0)) ↔
      ∀ r : ℝ, π r + π (-f - r) = 1 := by
  constructor
  · intro h r
    simpa using h (fun _ ↦ r)
  · intro h r
    simpa using h (r 0)

/-- `LocallyConvexAt π x` means that `π` is convex on some convex neighborhood of `x`. -/
def LocallyConvexAt (π : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ s : Set ℝ, s ∈ nhds x ∧ Convex ℝ s ∧ ConvexOn ℝ s π

/-- Unfolding lemma for `LocallyConvexAt`. -/
theorem locallyConvexAt_iff {π : ℝ → ℝ} {x : ℝ} :
    LocallyConvexAt π x ↔
      ∃ s : Set ℝ, s ∈ nhds x ∧ Convex ℝ s ∧ ConvexOn ℝ s π :=
  Iff.rfl

variable {f : ℝ} {π : ℝ → ℝ}

/-- Helper for Exercise 6.17: `symmetryMate f r` is the representative of `-f-r` in the unit
interval. -/
noncomputable def symmetryMate (f r : ℝ) : ℝ :=
  Int.fract (-f - r)

/-- Helper for Exercise 6.17: every symmetry mate lies in `[0, 1]`. -/
theorem symmetryMate_mem_unitInterval (f r : ℝ) :
    symmetryMate f r ∈ Set.Icc (0 : ℝ) 1 := by
  -- The mate is defined as a fractional part, so it stays in the fundamental domain.
  constructor
  · simp [symmetryMate]
  · simpa [symmetryMate] using le_of_lt (Int.fract_lt_one (-f - r))

/-- Helper for Exercise 6.17: periodicity identifies `π (-f-r)` with the value at its symmetry
mate. -/
theorem periodic_eval_symmetryMate
    (hperiodic : Function.Periodic π 1) (f r : ℝ) :
    π (symmetryMate f r) = π (-f - r) := by
  -- Reduce `-f-r` to its fractional part inside the unit interval.
  have hshift : π (-f - r) = π (Int.fract (-f - r)) := by
    calc
      π (-f - r) = π (Int.fract (-f - r) + (Int.floor (-f - r) : ℝ)) := by
        rw [Int.fract_add_floor]
      _ = π (Int.fract (-f - r)) := by
        simpa using (hperiodic.int_mul (Int.floor (-f - r)) (Int.fract (-f - r)))
  simpa [symmetryMate] using hshift.symm

/-- Helper for Exercise 6.17: after taking the symmetry mate, the second symmetry evaluation comes
back to `π r`. -/
theorem periodic_eval_neg_add_symmetryMate
    (hperiodic : Function.Periodic π 1) (f r : ℝ) :
    π (-f - symmetryMate f r) = π r := by
  -- Rewrite the companion point as `r` translated by an integer period.
  have hdecomp : -f - symmetryMate f r = r + (Int.floor (-f - r) : ℝ) := by
    dsimp [symmetryMate]
    linarith [Int.fract_add_floor (-f - r)]
  calc
    π (-f - symmetryMate f r) = π (r + (Int.floor (-f - r) : ℝ)) := by rw [hdecomp]
    _ = π r := by
      simpa [add_assoc, add_left_comm, add_comm] using
        (hperiodic.int_mul (Int.floor (-f - r)) r)

/-- Helper for Exercise 6.17: applying the symmetry mate twice recovers any point of `[0, 1)`. -/
theorem symmetryMate_symmetryMate_eq_self
    (f x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    symmetryMate f (symmetryMate f x) = x := by
  -- The second application only adds back the integer translation used in the first fractional
  -- part reduction, so the remaining fractional part is just `x`.
  have hdecomp : -f - symmetryMate f x = x + (Int.floor (-f - x) : ℝ) := by
    dsimp [symmetryMate]
    linarith [Int.fract_add_floor (-f - x)]
  rw [symmetryMate, hdecomp, Int.fract_add_intCast]
  simp [Int.fract_eq_self.2 hx]

/-- Helper for Exercise 6.17: translating one summand by the symmetry mate preserves the total
argument modulo `1`. -/
theorem periodic_eval_add_symmetryMate
    (hperiodic : Function.Periodic π 1) (f a b : ℝ) :
    π (a + symmetryMate (f + a) b) = π (-f - b) := by
  -- The sum `a + symmetryMate (f+a) b` differs from `-f-b` by an integer translate.
  have hdecomp :
      a + symmetryMate (f + a) b = -f - b - (Int.floor (-f - a - b) : ℝ) := by
    have hfract :
        Int.fract (-f - a - b) = -f - a - b - (Int.floor (-f - a - b) : ℝ) := by
      linarith [Int.fract_add_floor (-f - a - b)]
    have harg : -((f + a)) - b = -f - a - b := by ring
    calc
      a + symmetryMate (f + a) b = a + Int.fract (-f - a - b) := by
        rw [symmetryMate, harg]
      _ = a + (-f - a - b - (Int.floor (-f - a - b) : ℝ)) := by rw [hfract]
      _ = -f - b - (Int.floor (-f - a - b) : ℝ) := by ring
  have hshift :
      π (-f - b) = π (-f - b - (Int.floor (-f - a - b) : ℝ)) := by
    calc
      π (-f - b) =
          π ((-f - b - (Int.floor (-f - a - b) : ℝ)) + (Int.floor (-f - a - b) : ℝ)) := by
            ring
      _ = π (-f - b - (Int.floor (-f - a - b) : ℝ)) := by
        simpa using
          (hperiodic.int_mul (Int.floor (-f - a - b))
            (-f - b - (Int.floor (-f - a - b) : ℝ)))
  rw [hdecomp]
  exact hshift.symm

/-- For Exercise 6.17, the breakpoint checkpoints attached to a chosen piecewise-linear witness on
`[0, 1]` are the raw witness breakpoints together with the interval endpoints `0` and `1`. -/
noncomputable def breakpointCheckpoints {π : ℝ → ℝ}
    (hpiece : PiecewiseLinearOnInterval 0 1 π) : Finset ℝ :=
  insert 0 (insert 1 hpiece.breakpoints)

/-- For Exercise 6.17, `Exercise617Breakpoint π x` is the source-facing, witness-independent
notion of a relevant breakpoint of `π` on `[0, 1]`: either a boundary point of the interval or an
interior breakpoint that must appear in every piecewise-linear witness on `[0, 1]`. -/
def Exercise617Breakpoint (π : ℝ → ℝ) (x : ℝ) : Prop :=
  x = 0 ∨ x = 1 ∨
    (x ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ hpiece : PiecewiseLinearOnInterval 0 1 π, x ∈ hpiece.breakpoints)

/-- Helper for Exercise 6.17: every real affine function is convex on every convex real domain. -/
theorem convexOn_affineReal
    {s : Set ℝ} (hs : Convex ℝ s) (m b : ℝ) :
    ConvexOn ℝ s (fun x : ℝ ↦ m * x + b) := by
  -- Affine real maps are linear maps plus constants, so the standard convexity owners apply.
  have hlinear :
      ConvexOn ℝ s (fun x : ℝ ↦ m * x) := by
    simpa [LinearMap.smulRight_apply, mul_comm] using
      ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight m).convexOn hs
  exact hlinear.add_const b

/-- Helper for Exercise 6.17: affine behavior on a convex neighborhood gives local convexity. -/
theorem locallyConvexAt_of_affineNeighborhood
    {π : ℝ → ℝ} {x : ℝ} {s : Set ℝ}
    (hs_nhds : s ∈ nhds x) (hs_convex : Convex ℝ s)
    {m b : ℝ} (hEq : Set.EqOn π (fun y ↦ m * y + b) s) :
    LocallyConvexAt π x := by
  -- Rewrite the local function values to the affine model and use exact convexity of that model.
  refine ⟨s, hs_nhds, hs_convex, ?_⟩
  exact (convexOn_affineReal hs_convex m b).congr fun y hy ↦ (hEq hy).symm

/-- Helper for Exercise 6.17: an interior point that is not source-facing must lie on an affine
neighborhood for some piecewise-linear witness. -/
lemma notExercise617Breakpoint_hasAffineOpenInterval
    (_hpiece : PiecewiseLinearOnInterval 0 1 π) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hnot : ¬ Exercise617Breakpoint π x) :
    ∃ a b m c : ℝ, a < x ∧ x < b ∧ Set.EqOn π (fun y ↦ m * y + c) (Set.Ioo a b) := by
  classical
  -- Since `x` is not source-facing, some witness omits it from the raw breakpoint set.
  have hx_unit : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hnot_all :
      ¬ ∀ hpiece' : PiecewiseLinearOnInterval 0 1 π, x ∈ hpiece'.breakpoints := by
    intro hall
    exact hnot (Or.inr <| Or.inr ⟨hx_unit, hall⟩)
  have hnot_all' :
      ∃ hpiece' : PiecewiseLinearOnInterval 0 1 π, x ∉ hpiece'.breakpoints := by
    simpa [not_forall] using hnot_all
  rcases hnot_all' with ⟨hpiece', hx_not_break⟩
  have hcover := hpiece'.cover hx_unit
  rw [Set.mem_iUnion] at hcover
  rcases hcover with ⟨j, hx_piece⟩
  have hlower_lt : hpiece'.lower j < x := by
    -- If `x` were the left endpoint of the owning piece, that endpoint would be a raw breakpoint.
    by_contra hlower
    have hxeq : x = hpiece'.lower j := le_antisymm (not_lt.mp hlower) hx_piece.1
    have hx_mem_break : x ∈ hpiece'.breakpoints := by
      subst hxeq
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, hx_unit⟩
      exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_image.mpr ⟨j, by simp, rfl⟩
    exact hx_not_break hx_mem_break
  have hx_lt_upper : x < hpiece'.upper j := by
    -- The same endpoint argument rules out `x` as the right endpoint of the owning piece.
    by_contra hupper
    have hxeq : x = hpiece'.upper j := le_antisymm hx_piece.2 (not_lt.mp hupper)
    have hx_mem_break : x ∈ hpiece'.breakpoints := by
      subst hxeq
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, hx_unit⟩
      exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_image.mpr ⟨j, by simp, rfl⟩
    exact hx_not_break hx_mem_break
  refine ⟨hpiece'.lower j, hpiece'.upper j, hpiece'.slope j, hpiece'.intercept j,
    hlower_lt, hx_lt_upper, ?_⟩
  -- On the open cell, the witness affine formula is available by restricting the owning piece.
  intro y hy
  exact hpiece'.eq_affine j y ⟨le_of_lt hy.1, le_of_lt hy.2⟩

/-- Helper for Exercise 6.17: an interior point that is not source-facing must lie on an affine
neighborhood for some piecewise-linear witness. -/
lemma notExercise617Breakpoint_hasAffineNeighborhood
    (_hpiece : PiecewiseLinearOnInterval 0 1 π) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hnot : ¬ Exercise617Breakpoint π x) :
    ∃ s : Set ℝ, s ∈ nhds x ∧ Convex ℝ s ∧ ∃ m b : ℝ, Set.EqOn π (fun y ↦ m * y + b) s := by
  -- Repackage the explicit affine interval into the neighborhood-based local form used later.
  rcases notExercise617Breakpoint_hasAffineOpenInterval (π := π) _hpiece hx hnot with
    ⟨a, b, m, c, ha, hb, hEq⟩
  refine ⟨Set.Ioo a b, ?_, convex_Ioo _ _, m, c, hEq⟩
  · -- The strict inequalities place the open cell inside the neighborhood filter of `x`.
    exact isOpen_Ioo.mem_nhds ⟨ha, hb⟩

/-- Helper for Exercise 6.17: when the symmetry mate of `x` stays away from the boundary values
`0` and `1`, the map `r ↦ symmetryMate f r` is affine near `x`. -/
lemma symmetryMate_hasAffineOpenInterval {f x : ℝ}
    (hmate : symmetryMate f x ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ a b c : ℝ, a < x ∧ x < b ∧
      Set.EqOn (symmetryMate f) (fun y ↦ -y + c) (Set.Ioo a b) := by
  let n : ℤ := Int.floor (-f - x)
  have hx_left : -f - ((n + 1 : ℤ) : ℝ) < x := by
    have hupper : -f - x < ((n + 1 : ℤ) : ℝ) := by
      simp [n]
    linarith
  have hx_right : x < -f - (n : ℝ) := by
    have hfloor_lt : (n : ℝ) < -f - x := by
      have hnot_int : -f - x ∉ Set.range (fun z : ℤ ↦ (z : ℝ)) := by
        intro hmem
        have hfract_zero : symmetryMate f x = 0 := by
          rcases hmem with ⟨z, hz⟩
          simpa [symmetryMate, hz] using (Int.fract_intCast z : Int.fract (z : ℝ) = 0)
        exact (lt_irrefl (0 : ℝ)) (by simpa [hfract_zero] using hmate.1)
      simpa [n] using (Int.floor_lt_self_iff (a := -f - x)).2 hnot_int
    linarith
  refine ⟨-f - ((n + 1 : ℤ) : ℝ), -f - (n : ℝ), -f - (n : ℝ), hx_left, hx_right, ?_⟩
  intro y hy
  have hy_floor : Int.floor (-f - y) = n := by
    have hlower : (n : ℝ) ≤ -f - y := by
      linarith [hy.2]
    have hupper : -f - y < ((n + 1 : ℤ) : ℝ) := by
      linarith [hy.1]
    exact (Int.floor_eq_iff (a := -f - y) (z := n)).2
      ⟨hlower, by simpa [Int.cast_add, Int.cast_one] using hupper⟩
  -- On this interval the floor is fixed, so the fractional part becomes one affine formula.
  rw [symmetryMate, Int.fract, hy_floor]
  ring

/-- Helper for Exercise 6.17: if both `x` and its symmetry mate are source-free interior points,
the symmetry defect is affine on an open interval around `x`. -/
lemma symmetryDefect_hasAffineOpenInterval
    (hperiodic : Function.Periodic π 1) (hpiece : PiecewiseLinearOnInterval 0 1 π)
    {f x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hnotx : ¬ Exercise617Breakpoint π x)
    (hnotmate : ¬ Exercise617Breakpoint π (symmetryMate f x)) :
    ∃ a b m c : ℝ, a < x ∧ x < b ∧
      Set.EqOn (fun y ↦ π y + π (-f - y)) (fun y ↦ m * y + c) (Set.Ioo a b) := by
  rcases notExercise617Breakpoint_hasAffineOpenInterval (π := π) hpiece hx hnotx with
    ⟨u₁, v₁, m₁, c₁, hu₁, hv₁, hπx⟩
  have hmate_unit : symmetryMate f x ∈ Set.Icc (0 : ℝ) 1 := symmetryMate_mem_unitInterval f x
  have hmate_inner : symmetryMate f x ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · refine lt_of_le_of_ne hmate_unit.1 ?_
      intro hzero
      exact hnotmate (Or.inl hzero.symm)
    · refine lt_of_le_of_ne hmate_unit.2 ?_
      intro hone
      exact hnotmate (Or.inr <| Or.inl hone)
  rcases notExercise617Breakpoint_hasAffineOpenInterval (π := π) hpiece hmate_inner hnotmate with
    ⟨u₂, v₂, m₂, c₂, hu₂, hv₂, hπmate⟩
  rcases symmetryMate_hasAffineOpenInterval (f := f) hmate_inner with
    ⟨u₃, v₃, c₃, hu₃, hv₃, hsym⟩
  have hmate_eq : symmetryMate f x = -x + c₃ := hsym ⟨hu₃, hv₃⟩
  let L : ℝ := max u₁ (max u₃ (c₃ - v₂))
  let U : ℝ := min v₁ (min v₃ (c₃ - u₂))
  have hLx : L < x := by
    dsimp [L]
    refine max_lt hu₁ ?_
    refine max_lt hu₃ ?_
    linarith [hv₂, hmate_eq]
  have hxU : x < U := by
    dsimp [U]
    refine lt_min hv₁ ?_
    refine lt_min hv₃ ?_
    linarith [hu₂, hmate_eq]
  refine ⟨L, U, m₁ - m₂, c₁ + m₂ * c₃ + c₂, hLx, hxU, ?_⟩
  -- Rewrite the second summand through the affine symmetry mate and then combine both affine
  -- descriptions into one affine formula for the defect.
  intro y hy
  have hy₁ : y ∈ Set.Ioo u₁ v₁ := by
    constructor
    · exact lt_of_le_of_lt (le_max_left _ _) hy.1
    · exact lt_of_lt_of_le hy.2 (min_le_left _ _)
  have hy₃ : y ∈ Set.Ioo u₃ v₃ := by
    constructor
    · exact lt_of_le_of_lt
        (le_trans (le_max_left _ _) (le_max_right _ _)) hy.1
    · exact lt_of_lt_of_le hy.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hy₂ : -y + c₃ ∈ Set.Ioo u₂ v₂ := by
    constructor
    · have hy_upper : y < c₃ - u₂ := by
        exact lt_of_lt_of_le hy.2 (le_trans (min_le_right _ _) (min_le_right _ _))
      linarith
    · have hy_lower : c₃ - v₂ < y := by
        have hL_le : c₃ - v₂ ≤ L := by
          dsimp [L]
          exact le_trans (le_max_right _ _) (le_max_right _ _)
        exact lt_of_le_of_lt hL_le hy.1
      linarith
  have hperiod : π (-f - y) = π (symmetryMate f y) := by
    simpa using (periodic_eval_symmetryMate hperiodic f y).symm
  change π y + π (-f - y) = (m₁ - m₂) * y + (c₁ + m₂ * c₃ + c₂)
  rw [hperiod]
  rw [hπx hy₁, hsym hy₃, hπmate hy₂]
  ring

/-- Helper for Exercise 6.17: if both `x` and its symmetry mate are source-free interior points,
the symmetry defect is affine on a neighborhood of `x`. -/
lemma symmetryDefect_hasAffineNeighborhood
    (hperiodic : Function.Periodic π 1) (hpiece : PiecewiseLinearOnInterval 0 1 π)
    {f x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hnotx : ¬ Exercise617Breakpoint π x)
    (hnotmate : ¬ Exercise617Breakpoint π (symmetryMate f x)) :
    ∃ s : Set ℝ, s ∈ nhds x ∧ Convex ℝ s ∧
      ∃ m c : ℝ, Set.EqOn (fun y ↦ π y + π (-f - y)) (fun y ↦ m * y + c) s := by
  -- Repackage the explicit affine interval into the neighborhood-based form used later.
  rcases symmetryDefect_hasAffineOpenInterval (π := π) hperiodic hpiece hx hnotx hnotmate with
    ⟨a, b, m, c, hax, hxb, hEq⟩
  refine ⟨Set.Ioo a b, isOpen_Ioo.mem_nhds ⟨hax, hxb⟩, convex_Ioo _ _, m, c, hEq⟩

/-- Helper for Exercise 6.17: any interior point that is not source-facing is locally convex. -/
lemma locallyConvexAt_of_notExercise617Breakpoint
    (hpiece : PiecewiseLinearOnInterval 0 1 π) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hnot : ¬ Exercise617Breakpoint π x) :
    LocallyConvexAt π x := by
  -- Package the affine-neighborhood witness into the exercise's local convexity owner.
  rcases notExercise617Breakpoint_hasAffineNeighborhood (π := π) hpiece hx hnot with
    ⟨s, hs_nhds, hs_convex, m, b, hEq⟩
  exact locallyConvexAt_of_affineNeighborhood hs_nhds hs_convex hEq

/-- Helper for Exercise 6.17: every source-facing breakpoint belongs to the raw checkpoint finset
of any chosen piecewise-linear witness. -/
theorem exercise617Breakpoint_mem_breakpointCheckpoints
    {hpiece : PiecewiseLinearOnInterval 0 1 π} {x : ℝ}
    (hx : Exercise617Breakpoint π x) :
    x ∈ breakpointCheckpoints hpiece := by
  -- Unpack the source-facing breakpoint cases and reinsert the point into the chosen witness.
  rcases hx with rfl | rfl | ⟨_hx_unit, hx_breaks⟩
  · simp [breakpointCheckpoints]
  · simp [breakpointCheckpoints]
  · simp [breakpointCheckpoints, hx_breaks hpiece]

/-- Helper for Exercise 6.17: the breakpoint hypothesis also forces the symmetry equation at the
shifted breakpoint mates. -/
theorem symmetryAtShiftedBreakpointOfBreakpointCheck
    (hperiodic : Function.Periodic π 1) (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm_checkpoints :
      ∀ ⦃r : ℝ⦄, r ∈ breakpointCheckpoints hpiece → π r + π (-f - r) = 1)
    {r : ℝ} (hr : r ∈ breakpointCheckpoints hpiece) :
    π (symmetryMate f r) + π (-f - symmetryMate f r) = 1 := by
  -- Move the shifted checkpoint back to the original checkpoint by periodicity.
  calc
    π (symmetryMate f r) + π (-f - symmetryMate f r)
        = π (-f - r) + π r := by
            rw [periodic_eval_symmetryMate hperiodic f r]
            rw [periodic_eval_neg_add_symmetryMate hperiodic f r]
    _ = 1 := by simpa [add_comm] using h_symm_checkpoints hr

/-- Helper for Exercise 6.17: the source-facing symmetry hypothesis also propagates to symmetry
mates of source-facing breakpoints. -/
theorem symmetryAtShiftedSourceBreakpoint
    (hperiodic : Function.Periodic π 1)
    (h_symm_checkpoints :
      ∀ ⦃r : ℝ⦄, Exercise617Breakpoint π r → π r + π (-f - r) = 1)
    {r : ℝ} (hr : Exercise617Breakpoint π r) :
    π (symmetryMate f r) + π (-f - symmetryMate f r) = 1 := by
  -- Rewrite the shifted evaluation back to the original source-facing breakpoint.
  calc
    π (symmetryMate f r) + π (-f - symmetryMate f r)
        = π (-f - r) + π r := by
            rw [periodic_eval_symmetryMate hperiodic f r]
            rw [periodic_eval_neg_add_symmetryMate hperiodic f r]
    _ = 1 := by simpa [add_comm] using h_symm_checkpoints hr

/-- Helper for Exercise 6.17: the scalar subadditivity defect `π a + π b - π (a + b)`. -/
def subadditivityDefect (π : ℝ → ℝ) (a b : ℝ) : ℝ :=
  π a + π b - π (a + b)

/-- Helper for Exercise 6.17: the subadditivity defect is unchanged by the standard symmetry
transport on either variable. -/
theorem subadditivityDefectTransport
    (hperiodic : Function.Periodic π 1) (h_symm : ∀ r : ℝ, π r + π (-f - r) = 1)
    (a b : ℝ) :
    let t := symmetryMate (f + a) b
    subadditivityDefect π a b = subadditivityDefect π a t ∧
      subadditivityDefect π a b = subadditivityDefect π t b := by
  let t : ℝ := symmetryMate (f + a) b
  have ht : π t = π (-f - a - b) := by
    simpa [t, add_assoc, add_left_comm, add_comm] using
      periodic_eval_symmetryMate hperiodic (f + a) b
  have hat : π (a + t) = π (-f - b) := by
    simpa [t, add_assoc, add_left_comm, add_comm] using
      periodic_eval_add_symmetryMate hperiodic f a b
  have hswap : symmetryMate (f + a) b = symmetryMate (f + b) a := by
    rw [symmetryMate, symmetryMate]
    congr 1
    ring
  have htb : π (t + b) = π (-f - a) := by
    simpa [t, hswap, add_assoc, add_left_comm, add_comm] using
      periodic_eval_add_symmetryMate hperiodic f b a
  constructor
  · -- Replace `π b` and `π (a + b)` using symmetry, then normalize the transported defect.
    calc
      subadditivityDefect π a b
          = π a + (1 - π (-f - b)) - (1 - π (-f - a - b)) := by
              have hb' : π b = 1 - π (-f - b) := by linarith [h_symm b]
              have hab' : π (a + b) = 1 - π (-f - a - b) := by
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                  (show π (a + b) = 1 - π (-f - (a + b)) by linarith [h_symm (a + b)])
              rw [subadditivityDefect, hb', hab']
      _ = π a + π (-f - a - b) - π (-f - b) := by ring
      _ = π a + π t - π (a + t) := by rw [ht, hat]
      _ = subadditivityDefect π a t := by rw [subadditivityDefect]
  · -- The same normalization works after transporting the first variable instead.
    calc
      subadditivityDefect π a b
          = (1 - π (-f - a)) + π b - (1 - π (-f - a - b)) := by
              have ha' : π a = 1 - π (-f - a) := by linarith [h_symm a]
              have hab' : π (a + b) = 1 - π (-f - a - b) := by
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                  (show π (a + b) = 1 - π (-f - (a + b)) by linarith [h_symm (a + b)])
              rw [subadditivityDefect, ha', hab']
      _ = π (-f - a - b) + π b - π (-f - a) := by ring
      _ = π t + π b - π (t + b) := by rw [ht, htb]
      _ = subadditivityDefect π t b := by rw [subadditivityDefect]

/-- Helper for Exercise 6.17: every fixed-first-coordinate subadditivity-defect slice is
continuous. -/
lemma continuous_subadditivityDefect_secondSlice
    (hcontinuous : Continuous π) (a : ℝ) :
    Continuous (fun y : ℝ ↦ subadditivityDefect π a y) := by
  -- The slice is built from `π` by addition with a constant and translation.
  have hconst : Continuous fun _ : ℝ ↦ π a := continuous_const
  have hsum : Continuous fun y : ℝ ↦ π (a + y) :=
    hcontinuous.comp (continuous_const.add continuous_id)
  simpa [subadditivityDefect] using (hconst.add hcontinuous).sub hsum

/-- Helper for Exercise 6.17: the scalar subadditivity defect is symmetric in its two arguments. -/
lemma subadditivityDefect_comm (a b : ℝ) :
    subadditivityDefect π a b = subadditivityDefect π b a := by
  -- The formula only depends on `a + b`, so swapping the arguments changes nothing.
  simp [subadditivityDefect, add_comm]

/-- Helper for Exercise 6.17: if both `x` and its transported mate stay away from the
source-facing breakpoints, then the slice `y ↦ subadditivityDefect π a y` is affine near `x`. -/
lemma subadditivityDefectOnSecondSlice_hasAffineOpenInterval
    (hperiodic : Function.Periodic π 1) (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm : ∀ r : ℝ, π r + π (-f - r) = 1)
    {a x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hnotx : ¬ Exercise617Breakpoint π x)
    (hnotmate : ¬ Exercise617Breakpoint π (symmetryMate (f + a) x)) :
    ∃ u v m c : ℝ, u < x ∧ x < v ∧
      Set.EqOn (fun y ↦ subadditivityDefect π a y) (fun y ↦ m * y + c) (Set.Ioo u v) := by
  rcases symmetryDefect_hasAffineOpenInterval (π := π) hperiodic hpiece
      (f := f + a) hx hnotx hnotmate with
    ⟨u, v, m, c, hux, hxv, hEq⟩
  refine ⟨u, v, m, c + (π a - 1), hux, hxv, ?_⟩
  -- Rewrite the `π (a + y)` term through the symmetry identity, then absorb the constant `π a`.
  intro y hy
  have hsymm_eval : π (a + y) = 1 - π (-f - a - y) := by
    have hbase := h_symm (a + y)
    have hbase' : π (a + y) + π (-f - a - y) = 1 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hbase
    linarith
  have haff : π y + π (-f - a - y) = m * y + c := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hEq hy
  calc
    subadditivityDefect π a y = π a + π y - π (a + y) := by rw [subadditivityDefect]
    _ = π y + π (-f - a - y) + (π a - 1) := by rw [hsymm_eval]; ring
    _ = m * y + c + (π a - 1) := by rw [haff]
    _ = m * y + (c + (π a - 1)) := by ring

/-- Helper for Exercise 6.17: an affine function with a local extremum at an interior point is
locally constant there. -/
lemma affinePlateauOfLocalExtremum
    {g : ℝ → ℝ} {u x v m c : ℝ}
    (hu : u < x) (hv : x < v)
    (hEq : Set.EqOn g (fun y ↦ m * y + c) (Set.Ioo u v))
    (hExt : IsLocalMax g x ∨ IsLocalMin g x) :
    ∃ u' v', u' < x ∧ x < v' ∧
      Set.EqOn g (fun _ ↦ g x) (Set.Ioo u' v') := by
  have hx_mem : x ∈ Set.Ioo u v := ⟨hu, hv⟩
  have hEq_nhds : g =ᶠ[nhds x] fun y ↦ m * y + c := by
    -- The affine formula holds on an open interval, hence in a full neighborhood of `x`.
    filter_upwards [isOpen_Ioo.mem_nhds hx_mem] with y hy
    exact hEq hy
  have hderiv_affine : HasDerivAt (fun y : ℝ ↦ m * y + c) m x := by
    -- The local affine model has constant derivative `m`.
    simpa using ((hasDerivAt_id x).const_mul m).add_const c
  have hderiv_g : HasDerivAt g m x := hderiv_affine.congr_of_eventuallyEq hEq_nhds
  have hm_zero : m = 0 := by
    -- Fermat's theorem forces the affine slope to vanish at a local extremum.
    rcases hExt with hmax | hmin
    · simpa using hmax.hasDerivAt_eq_zero hderiv_g
    · simpa using hmin.hasDerivAt_eq_zero hderiv_g
  refine ⟨u, v, hu, hv, ?_⟩
  intro y hy
  -- Once the slope is zero, the affine model is constant on the whole interval.
  rw [hEq hy, hEq hx_mem, hm_zero]
  simp

/-- Helper for Exercise 6.17: a nonzero global extremum of the centered symmetry defect on
`[0, 1]` is impossible. -/
lemma nonzeroSymmetryExtremumAbsurd
    (hperiodic : Function.Periodic π 1) (hcontinuous : Continuous π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm_checkpoints :
      ∀ ⦃r : ℝ⦄, Exercise617Breakpoint π r → π r + π (-f - r) = 1)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hExt :
      IsMaxOn (fun r ↦ π r + π (-f - r) - 1) (Set.Icc (0 : ℝ) 1) x ∨
        IsMinOn (fun r ↦ π r + π (-f - r) - 1) (Set.Icc (0 : ℝ) 1) x)
    (hneq : (π x + π (-f - x) - 1) ≠ 0) :
    False := by
  let defect : ℝ → ℝ := fun r ↦ π r + π (-f - r) - 1
  let levelSet : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ {r : ℝ | defect r = defect x}
  have hExt' : IsMaxOn defect (Set.Icc (0 : ℝ) 1) x ∨ IsMinOn defect (Set.Icc (0 : ℝ) 1) x := by
    simpa [defect] using hExt
  have hx_nonzero : defect x ≠ 0 := by
    simpa [defect] using hneq
  have hcont_shift : Continuous fun r : ℝ ↦ -f - r := continuous_const.sub continuous_id
  have hcont_defect : Continuous defect := by
    -- The centered defect is continuous because it is built from `π` by translation and addition.
    dsimp [defect]
    exact (hcontinuous.add (hcontinuous.comp hcont_shift)).sub continuous_const
  have hlevel_nonempty : levelSet.Nonempty := by
    refine ⟨x, ?_⟩
    exact ⟨hx, rfl⟩
  have hcompact_level : IsCompact levelSet := by
    have hclosed_level : IsClosed {r : ℝ | defect r = defect x} := by
      exact isClosed_eq hcont_defect continuous_const
    simpa [levelSet] using (isCompact_Icc.inter_right hclosed_level)
  rcases hcompact_level.exists_isMinOn hlevel_nonempty continuous_id.continuousOn with
    ⟨x0, hx0_level, hx0_leftmost⟩
  have hx0_unit : x0 ∈ Set.Icc (0 : ℝ) 1 := hx0_level.1
  have hx0_value : defect x0 = defect x := hx0_level.2
  have hx0_nonzero : defect x0 ≠ 0 := by
    simpa [hx0_value] using hx_nonzero
  have hExt0 : IsMaxOn defect (Set.Icc (0 : ℝ) 1) x0 ∨ IsMinOn defect (Set.Icc (0 : ℝ) 1) x0 := by
    rcases hExt' with hmax | hmin
    · left
      rw [isMaxOn_iff] at hmax ⊢
      intro y hy
      calc
        defect y ≤ defect x := hmax y hy
        _ = defect x0 := hx0_value.symm
    · right
      rw [isMinOn_iff] at hmin ⊢
      intro y hy
      calc
        defect x0 = defect x := hx0_value
        _ ≤ defect y := hmin y hy
  have hx0_not_break : ¬ Exercise617Breakpoint π x0 := by
    intro hx0_break
    have hzero : defect x0 = 0 := by
      -- Source-facing breakpoints satisfy the symmetry identity, so the defect vanishes there.
      have hsymm := h_symm_checkpoints hx0_break
      dsimp [defect] at *
      linarith
    exact hx0_nonzero hzero
  have hmate_not_break : ¬ Exercise617Breakpoint π (symmetryMate f x0) := by
    intro hmate_break
    have hzero_mate : defect (symmetryMate f x0) = 0 := by
      -- The same checkpoint hypothesis also kills the defect at a source-facing symmetry mate.
      have hsymm := h_symm_checkpoints hmate_break
      dsimp [defect] at *
      linarith
    have hmate_value : defect x0 = defect (symmetryMate f x0) := by
      -- Periodicity identifies the defect at `x0` with the defect at its mate.
      dsimp [defect]
      rw [periodic_eval_symmetryMate hperiodic f x0,
        periodic_eval_neg_add_symmetryMate hperiodic f x0]
      ring
    exact hx0_nonzero (hmate_value.trans hzero_mate)
  have hx0_inner : x0 ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · refine lt_of_le_of_ne hx0_unit.1 ?_
      intro hx0_zero
      exact hx0_not_break (Or.inl hx0_zero.symm)
    · refine lt_of_le_of_ne hx0_unit.2 ?_
      intro hx0_one
      exact hx0_not_break (Or.inr <| Or.inl hx0_one)
  rcases symmetryDefect_hasAffineOpenInterval (π := π) hperiodic hpiece
      (f := f) hx0_inner hx0_not_break hmate_not_break with
    ⟨u, v, m, c, hu, hv, hEq_symm⟩
  have hEq_defect :
      Set.EqOn defect (fun y ↦ m * y + (c - 1)) (Set.Ioo u v) := by
    intro y hy
    -- Subtracting the constant `1` preserves the affine description of the defect.
    have hy_eq := hEq_symm hy
    dsimp [defect] at *
    linarith
  have hIcc_nhds : Set.Icc (0 : ℝ) 1 ∈ nhds x0 := by
    -- An interior point of `[0, 1]` sees the whole closed interval as a neighborhood set.
    refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx0_inner) ?_
    intro y hy
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hLocal : IsLocalMax defect x0 ∨ IsLocalMin defect x0 := by
    rcases hExt0 with hmax | hmin
    · exact Or.inl (hmax.isLocalMax hIcc_nhds)
    · exact Or.inr (hmin.isLocalMin hIcc_nhds)
  rcases affinePlateauOfLocalExtremum hu hv hEq_defect hLocal with
    ⟨u', v', hu', hv', hPlateau⟩
  let y : ℝ := (max u' 0 + x0) / 2
  have hmax_lt_x0 : max u' 0 < x0 := by
    exact max_lt hu' hx0_inner.1
  have hy_lt_x0 : y < x0 := by
    -- Choose a plateau point strictly to the left of `x0` but still inside `[0, 1]`.
    dsimp [y]
    linarith
  have hy_Ioo : y ∈ Set.Ioo u' v' := by
    refine ⟨?_, ?_⟩
    · have hu'_le : u' ≤ max u' 0 := le_max_left _ _
      dsimp [y]
      linarith
    · exact lt_of_lt_of_le hy_lt_x0 (le_of_lt hv')
  have hy_unit : y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · have hzero_le : (0 : ℝ) ≤ max u' 0 := le_max_right _ _
      dsimp [y]
      linarith
    · exact le_of_lt (lt_of_lt_of_le hy_lt_x0 hx0_unit.2)
  have hy_level : y ∈ levelSet := by
    refine ⟨hy_unit, ?_⟩
    simpa [hx0_value] using hPlateau hy_Ioo
  have hx0_le_y : x0 ≤ y := by
    rw [isMinOn_iff] at hx0_leftmost
    exact hx0_leftmost y hy_level
  exact (not_le_of_gt hy_lt_x0) hx0_le_y

/-- Helper for Exercise 6.17: once the augmented breakpoint partition is built, the symmetry
defect is forced to be `1` on the whole unit interval. -/
lemma symmetryEqOneOnUnitIntervalOfBreakpointCheck
    (hperiodic : Function.Periodic π 1) (hcontinuous : Continuous π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm_checkpoints :
      ∀ ⦃r : ℝ⦄, Exercise617Breakpoint π r → π r + π (-f - r) = 1) :
    Set.EqOn (fun r ↦ π r + π (-f - r)) (fun _ ↦ (1 : ℝ)) (Set.Icc (0 : ℝ) 1) := by
  let defect : ℝ → ℝ := fun r ↦ π r + π (-f - r) - 1
  have hcont_shift : Continuous fun r : ℝ ↦ -f - r := continuous_const.sub continuous_id
  have hcont_defect : Continuous defect := by
    -- The centered defect is continuous on `[0, 1]`, so it attains both extrema there.
    dsimp [defect]
    exact (hcontinuous.add (hcontinuous.comp hcont_shift)).sub continuous_const
  rcases isCompact_Icc.exists_isMaxOn
      (s := Set.Icc (0 : ℝ) 1) (f := defect) ⟨0, by simp⟩ hcont_defect.continuousOn with
    ⟨xMax, hxMax_mem, hxMax⟩
  rcases isCompact_Icc.exists_isMinOn
      (s := Set.Icc (0 : ℝ) 1) (f := defect) ⟨0, by simp⟩ hcont_defect.continuousOn with
    ⟨xMin, hxMin_mem, hxMin⟩
  have hxMax_zero : defect xMax = 0 := by
    by_contra hxMax_nonzero
    exact nonzeroSymmetryExtremumAbsurd
      (π := π) hperiodic hcontinuous hpiece h_symm_checkpoints
      hxMax_mem (Or.inl hxMax) hxMax_nonzero
  have hxMin_zero : defect xMin = 0 := by
    by_contra hxMin_nonzero
    exact nonzeroSymmetryExtremumAbsurd
      (π := π) hperiodic hcontinuous hpiece h_symm_checkpoints
      hxMin_mem (Or.inr hxMin) hxMin_nonzero
  intro r hr
  have hmax_bound : defect r ≤ defect xMax := by
    rw [isMaxOn_iff] at hxMax
    exact hxMax r hr
  have hmin_bound : defect xMin ≤ defect r := by
    rw [isMinOn_iff] at hxMin
    exact hxMin r hr
  -- The maximum and minimum of the defect are both zero, so the defect itself vanishes.
  have hdefect_zero : defect r = 0 := by
    linarith [hmax_bound, hmin_bound, hxMax_zero, hxMin_zero]
  dsimp [defect] at hdefect_zero
  linarith

/-- Helper for Exercise 6.17: any failure of subadditivity can be normalized to the unit square by
passing to fractional parts. -/
lemma existsBadPointOnUnitSquareOfNotSubadditive
    (hperiodic : Function.Periodic π 1) (hnot : ¬ π.Subadditive) :
    ∃ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 ∧ b ∈ Set.Icc (0 : ℝ) 1 ∧ π (a + b) > π a + π b := by
  -- Normalize a violating pair to `[0,1]^2` using periodicity in each coordinate.
  have hnot' : ∃ a b : ℝ, π (a + b) > π a + π b := by
    simpa [Function.Subadditive, not_forall, not_le] using hnot
  rcases hnot' with ⟨a, b, hbad⟩
  refine ⟨Int.fract a, Int.fract b, ?_, ?_, ?_⟩
  · constructor
    · exact Int.fract_nonneg a
    · exact le_of_lt (Int.fract_lt_one a)
  · constructor
    · exact Int.fract_nonneg b
    · exact le_of_lt (Int.fract_lt_one b)
  have ha : π a = π (Int.fract a) := by
    calc
      π a = π (Int.fract a + (Int.floor a : ℝ)) := by rw [Int.fract_add_floor]
      _ = π (Int.fract a) := by
        simpa using (hperiodic.int_mul (Int.floor a) (Int.fract a))
  have hb : π b = π (Int.fract b) := by
    calc
      π b = π (Int.fract b + (Int.floor b : ℝ)) := by rw [Int.fract_add_floor]
      _ = π (Int.fract b) := by
        simpa using (hperiodic.int_mul (Int.floor b) (Int.fract b))
  have hab : π (a + b) = π (Int.fract a + Int.fract b) := by
    have hsum :
        a + b = Int.fract a + Int.fract b + ((Int.floor a + Int.floor b : ℤ) : ℝ) := by
      calc
        a + b =
            (Int.fract a + (Int.floor a : ℝ)) + (Int.fract b + (Int.floor b : ℝ)) := by
              rw [Int.fract_add_floor, Int.fract_add_floor]
        _ = Int.fract a + Int.fract b + ((Int.floor a + Int.floor b : ℤ) : ℝ) := by
              rw [Int.cast_add]
              ring_nf
    calc
      π (a + b) =
          π (Int.fract a + Int.fract b + ((Int.floor a + Int.floor b : ℤ) : ℝ)) := by
            rw [hsum]
      _ = π (Int.fract a + Int.fract b) := by
        simpa [add_assoc, add_left_comm, add_comm] using
          (hperiodic.int_mul (Int.floor a + Int.floor b) (Int.fract a + Int.fract b))
  linarith

/-- Helper for Exercise 6.17: every source-facing breakpoint lies in the unit interval. -/
theorem exercise617Breakpoint_mem_unitInterval {x : ℝ}
    (hx : Exercise617Breakpoint π x) :
    x ∈ Set.Icc (0 : ℝ) 1 := by
  -- The source-facing definition only adds the endpoints `0` and `1` to the unit interval.
  rcases hx with rfl | rfl | hx_unit
  · simp
  · simp
  · exact hx_unit.1

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: a function has specified
anchored affine formulas immediately to the left and right of a point. -/
private def HasAffineSidesAt (g : ℝ → ℝ) (x mLeft mRight : ℝ) : Prop :=
  ∃ u v : ℝ, u < x ∧ x < v ∧
    Set.EqOn g (fun y ↦ g x + mLeft * (y - x)) (Set.Icc u x) ∧
      Set.EqOn g (fun y ↦ g x + mRight * (y - x)) (Set.Icc x v)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: around any fixed point,
the finite raw breakpoint set contains no other point in a sufficiently small ball. -/
private lemma existsBreakpointFreeRadius
    (hpiece : PiecewiseLinearOnInterval 0 1 π) (x : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z ∈ hpiece.breakpoints, |z - x| < ε → z = x := by
  classical
  let s : Finset ℝ := hpiece.breakpoints.erase x
  have hx_compl : x ∈ (↑s : Set ℝ)ᶜ := by
    simp [s]
  have hcompl_nhds : (↑s : Set ℝ)ᶜ ∈ nhds x :=
    s.isClosed.isOpen_compl.mem_nhds hx_compl
  rcases Metric.mem_nhds_iff.mp hcompl_nhds with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro z hz hz_near
  by_contra hzx
  have hz_s : z ∈ s := by
    simp [s, hz, hzx]
  have hz_ball : z ∈ Metric.ball x ε := by
    simpa [Real.dist_eq, abs_sub_comm] using hz_near
  exact (hball hz_ball) hz_s

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: a piecewise-linear witness
provides one anchored affine formula immediately to the right of every point of `[0,1)`. -/
private lemma piecewiseLinearHasAffineRightAt
    (hpiece : PiecewiseLinearOnInterval 0 1 π) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ∃ v m : ℝ, x < v ∧
      Set.EqOn π (fun y ↦ π x + m * (y - x)) (Set.Icc x v) := by
  classical
  rcases existsBreakpointFreeRadius hpiece x with ⟨ε, hε, hfree⟩
  let d : ℝ := min (ε / 2) ((1 - x) / 2)
  let v : ℝ := x + d
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hx.2))
  have hdε : d < ε := by
    dsimp [d]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hv_unit : v ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [v]
      linarith [hx.1]
    · dsimp [v, d]
      have hd_bound : d ≤ (1 - x) / 2 := min_le_right _ _
      linarith
  have hv_cover := hpiece.cover hv_unit
  rw [Set.mem_iUnion] at hv_cover
  rcases hv_cover with ⟨j, hv_piece⟩
  have hlower_le_x : hpiece.lower j ≤ x := by
    by_contra hnot
    have hx_lower : x < hpiece.lower j := lt_of_not_ge hnot
    have hlower_unit : hpiece.lower j ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact hx.1.trans hx_lower.le
      · exact (hv_piece.1.trans hv_unit.2)
    have hlower_break : hpiece.lower j ∈ hpiece.breakpoints := by
      refine Finset.mem_filter.mpr ⟨?_, hlower_unit⟩
      have hj_univ : j ∈ Finset.univ := Finset.mem_univ j
      exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_image.mpr ⟨j, hj_univ, rfl⟩
    have hlower_near : |hpiece.lower j - x| < ε := by
      rw [abs_of_pos (sub_pos.mpr hx_lower)]
      dsimp [v] at hv_piece
      linarith [hv_piece.1, hdε]
    have hlower_eq := hfree (hpiece.lower j) hlower_break hlower_near
    exact (ne_of_gt hx_lower) hlower_eq
  have hx_lt_v : x < v := by simpa [v] using hd
  have hx_piece : x ∈ Set.Icc (hpiece.lower j) (hpiece.upper j) :=
    ⟨hlower_le_x, le_trans hx_lt_v.le hv_piece.2⟩
  refine ⟨v, hpiece.slope j, hx_lt_v, ?_⟩
  intro y hy
  have hy_piece : y ∈ Set.Icc (hpiece.lower j) (hpiece.upper j) :=
    ⟨hlower_le_x.trans hy.1, hy.2.trans hv_piece.2⟩
  -- Subtract the affine formula at the anchor from the formula at the nearby point.
  rw [hpiece.eq_affine j y hy_piece, hpiece.eq_affine j x hx_piece]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: a piecewise-linear witness
provides one anchored affine formula immediately to the left of every point of `(0,1]`. -/
private lemma piecewiseLinearHasAffineLeftAt
    (hpiece : PiecewiseLinearOnInterval 0 1 π) {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ u m : ℝ, u < x ∧
      Set.EqOn π (fun y ↦ π x + m * (y - x)) (Set.Icc u x) := by
  classical
  rcases existsBreakpointFreeRadius hpiece x with ⟨ε, hε, hfree⟩
  let d : ℝ := min (ε / 2) (x / 2)
  let u : ℝ := x - d
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (half_pos hε) (half_pos hx.1)
  have hdε : d < ε := by
    dsimp [d]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hu_unit : u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [u, d]
      have hd_bound : d ≤ x / 2 := min_le_right _ _
      linarith
    · dsimp [u]
      linarith [hx.2]
  have hu_cover := hpiece.cover hu_unit
  rw [Set.mem_iUnion] at hu_cover
  rcases hu_cover with ⟨j, hu_piece⟩
  have hx_le_upper : x ≤ hpiece.upper j := by
    by_contra hnot
    have hupper_x : hpiece.upper j < x := lt_of_not_ge hnot
    have hupper_unit : hpiece.upper j ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact hu_unit.1.trans hu_piece.2
      · exact hupper_x.le.trans hx.2
    have hupper_break : hpiece.upper j ∈ hpiece.breakpoints := by
      refine Finset.mem_filter.mpr ⟨?_, hupper_unit⟩
      have hj_univ : j ∈ Finset.univ := Finset.mem_univ j
      exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_image.mpr ⟨j, hj_univ, rfl⟩
    have hupper_near : |hpiece.upper j - x| < ε := by
      rw [abs_of_neg (sub_neg.mpr hupper_x)]
      dsimp [u] at hu_piece
      linarith [hu_piece.2, hdε]
    have hupper_eq := hfree (hpiece.upper j) hupper_break hupper_near
    exact (ne_of_lt hupper_x) hupper_eq
  have hu_lt_x : u < x := by simpa [u] using hd
  have hx_piece : x ∈ Set.Icc (hpiece.lower j) (hpiece.upper j) :=
    ⟨le_trans hu_piece.1 hu_lt_x.le, hx_le_upper⟩
  refine ⟨u, hpiece.slope j, hu_lt_x, ?_⟩
  intro y hy
  have hy_piece : y ∈ Set.Icc (hpiece.lower j) (hpiece.upper j) :=
    ⟨hu_piece.1.trans hy.1, hy.2.trans hx_le_upper⟩
  -- Subtract the affine formula at the anchor from the formula at the nearby point.
  rw [hpiece.eq_affine j y hy_piece, hpiece.eq_affine j x hx_piece]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: a periodic piecewise-linear
function has the same pair of affine side slopes at a point and at its fractional part. -/
private lemma periodicPiecewiseLinearHasAffineSidesAtAndFract
    (hperiodic : Function.Periodic π 1)
    (hpiece : PiecewiseLinearOnInterval 0 1 π) (x : ℝ) :
    ∃ mLeft mRight : ℝ,
      HasAffineSidesAt π x mLeft mRight ∧
        HasAffineSidesAt π (Int.fract x) mLeft mRight := by
  let p : ℝ := Int.fract x
  have hp_nonneg : 0 ≤ p := by
    simp [p]
  have hp_lt_one : p < 1 := by
    simpa [p] using Int.fract_lt_one x
  have hp_sides : ∃ mLeft mRight : ℝ, HasAffineSidesAt π p mLeft mRight := by
    by_cases hp_zero : p = 0
    · have hone_mem : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
        constructor <;> norm_num
      rcases piecewiseLinearHasAffineLeftAt (π := π) hpiece
          (x := (1 : ℝ)) hone_mem with
        ⟨u, mLeft, hu, hleft⟩
      rcases piecewiseLinearHasAffineRightAt (π := π) hpiece
          (x := p) ⟨hp_nonneg, hp_lt_one⟩ with
        ⟨v, mRight, hv, hright⟩
      refine ⟨mLeft, mRight, u - 1, v, ?_, hv, ?_, hright⟩
      · rw [hp_zero]
        linarith
      · intro y hy
        have hy_shift : y + 1 ∈ Set.Icc u 1 := by
          constructor
          · linarith [hy.1]
          · linarith [hy.2, hp_zero]
        have hperiod_y : π (y + 1) = π y := hperiodic y
        have hperiod_zero : π 1 = π 0 := by simpa using hperiodic 0
        have hleft_y := hleft hy_shift
        rw [hp_zero]
        rw [← hperiod_y, hleft_y, hperiod_zero]
        ring
    · have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp_zero)
      rcases piecewiseLinearHasAffineLeftAt (π := π) hpiece
          (x := p) ⟨hp_pos, hp_lt_one.le⟩ with
        ⟨u, mLeft, hu, hleft⟩
      rcases piecewiseLinearHasAffineRightAt (π := π) hpiece
          (x := p) ⟨hp_nonneg, hp_lt_one⟩ with
        ⟨v, mRight, hv, hright⟩
      exact ⟨mLeft, mRight, u, v, hu, hv, hleft, hright⟩
  rcases hp_sides with ⟨mLeft, mRight, u, v, hu, hv, hleft, hright⟩
  let k : ℝ := (Int.floor x : ℝ)
  have hx_decomp : x = p + k := by
    simp [p, k]
  have hperiod_shift (y : ℝ) : π (y + k) = π y := by
    simpa [k] using (hperiodic.int_mul (Int.floor x) y)
  have hx_value : π x = π p := by
    rw [hx_decomp]
    exact hperiod_shift p
  have hx_sides : HasAffineSidesAt π x mLeft mRight := by
    refine ⟨u + k, v + k, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · intro y hy
      have hy_base : y - k ∈ Set.Icc u p := by
        constructor <;> linarith [hy.1, hy.2, hx_decomp]
      have hy_value : π y = π (y - k) := by
        have hshift := hperiod_shift (y - k)
        have hy_arg : y - k + k = y := by ring
        rw [hy_arg] at hshift
        exact hshift
      rw [hy_value, hleft hy_base, hx_value]
      rw [hx_decomp]
      ring
    · intro y hy
      have hy_base : y - k ∈ Set.Icc p v := by
        constructor <;> linarith [hy.1, hy.2, hx_decomp]
      have hy_value : π y = π (y - k) := by
        have hshift := hperiod_shift (y - k)
        have hy_arg : y - k + k = y := by ring
        rw [hy_arg] at hshift
        exact hshift
      rw [hy_value, hright hy_base, hx_value]
      rw [hx_decomp]
      ring
  exact ⟨mLeft, mRight, hx_sides, u, v, hu, hv, hleft, hright⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: ordered affine side slopes
make a function convex on a neighborhood of their common anchor. -/
private lemma locallyConvexAtOfHasAffineSidesAt
    {g : ℝ → ℝ} {x mLeft mRight : ℝ}
    (hsides : HasAffineSidesAt g x mLeft mRight)
    (hslopes : mLeft ≤ mRight) :
    LocallyConvexAt g x := by
  rcases hsides with ⟨u, v, hu, hv, hleft, hright⟩
  have hdomain : Convex ℝ (Set.Icc u v) := convex_Icc _ _
  have hleft_convex :
      ConvexOn ℝ (Set.Icc u v) (fun y ↦ g x + mLeft * (y - x)) := by
    have hfun :
        (fun y : ℝ ↦ g x + mLeft * (y - x)) =
          fun y ↦ mLeft * y + (g x - mLeft * x) := by
      funext y
      ring
    rw [hfun]
    exact convexOn_affineReal hdomain mLeft (g x - mLeft * x)
  have hright_convex :
      ConvexOn ℝ (Set.Icc u v) (fun y ↦ g x + mRight * (y - x)) := by
    have hfun :
        (fun y : ℝ ↦ g x + mRight * (y - x)) =
          fun y ↦ mRight * y + (g x - mRight * x) := by
      funext y
      ring
    rw [hfun]
    exact convexOn_affineReal hdomain mRight (g x - mRight * x)
  have hsup := hleft_convex.sup hright_convex
  refine ⟨Set.Icc u v, ?_, hdomain, ?_⟩
  · -- The strict side endpoints put the closed interval in the neighborhood filter of `x`.
    refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hu, hv⟩) ?_
    intro y hy
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  · refine hsup.congr fun y hy ↦ ?_
    change max (g x + mLeft * (y - x)) (g x + mRight * (y - x)) = g y
    by_cases hyx : y ≤ x
    · calc
        max (g x + mLeft * (y - x)) (g x + mRight * (y - x)) =
            g x + mLeft * (y - x) := by
              rw [max_eq_left]
              nlinarith
        _ = g y := (hleft ⟨hy.1, hyx⟩).symm
    · have hxy : x ≤ y := le_of_not_ge hyx
      calc
        max (g x + mLeft * (y - x)) (g x + mRight * (y - x)) =
            g x + mRight * (y - x) := by
              rw [max_eq_right]
              nlinarith
        _ = g y := (hright ⟨hxy, hy.2⟩).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: if an affine neighborhood
overlaps both affine sides, then the two recorded side slopes coincide. -/
private lemma affineSideSlopesEqOfAffineOpenInterval
    {g : ℝ → ℝ} {x mLeft mRight a b m c : ℝ}
    (hsides : HasAffineSidesAt g x mLeft mRight)
    (ha : a < x) (hb : x < b)
    (hEq : Set.EqOn g (fun y ↦ m * y + c) (Set.Ioo a b)) :
    mLeft = mRight := by
  rcases hsides with ⟨u, v, hu, hv, hleft, hright⟩
  let yLeft : ℝ := (max u a + x) / 2
  have hmax_left : max u a < x := max_lt hu ha
  have hyLeft_lt : yLeft < x := by
    dsimp [yLeft]
    linarith
  have hyLeft_side : yLeft ∈ Set.Icc u x := by
    constructor
    · dsimp [yLeft]
      linarith [le_max_left u a]
    · exact hyLeft_lt.le
  have hyLeft_affine : yLeft ∈ Set.Ioo a b := by
    constructor
    · dsimp [yLeft]
      linarith [le_max_right u a]
    · exact hyLeft_lt.trans hb
  have hx_affine : x ∈ Set.Ioo a b := ⟨ha, hb⟩
  have hleft_product : (mLeft - m) * (yLeft - x) = 0 := by
    have hside := hleft hyLeft_side
    have hmodel_y := hEq hyLeft_affine
    have hmodel_x := hEq hx_affine
    nlinarith
  have hleft_slope : mLeft = m := by
    have hdiff : yLeft - x ≠ 0 := sub_ne_zero.mpr (ne_of_lt hyLeft_lt)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hleft_product).resolve_right hdiff)
  let yRight : ℝ := (x + min v b) / 2
  have hright_min : x < min v b := lt_min hv hb
  have hx_lt_yRight : x < yRight := by
    dsimp [yRight]
    linarith
  have hyRight_side : yRight ∈ Set.Icc x v := by
    constructor
    · exact hx_lt_yRight.le
    · dsimp [yRight]
      linarith [min_le_left v b]
  have hyRight_affine : yRight ∈ Set.Ioo a b := by
    constructor
    · exact ha.trans hx_lt_yRight
    · dsimp [yRight]
      linarith [min_le_right v b]
  have hright_product : (mRight - m) * (yRight - x) = 0 := by
    have hside := hright hyRight_side
    have hmodel_y := hEq hyRight_affine
    have hmodel_x := hEq hx_affine
    nlinarith
  have hright_slope : mRight = m := by
    have hdiff : yRight - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx_lt_yRight)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hright_product).resolve_right hdiff)
  exact hleft_slope.trans hright_slope.symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: unequal affine side slopes at
a point of `[0,1)` force that point to be source-facing. -/
private lemma exercise617BreakpointOfAffineSideSlopeChange
    (hpiece : PiecewiseLinearOnInterval 0 1 π) {x mLeft mRight : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hsides : HasAffineSidesAt π x mLeft mRight)
    (hne : mLeft ≠ mRight) :
    Exercise617Breakpoint π x := by
  by_contra hnot
  have hx_pos : 0 < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro hx_zero
    exact hnot (Or.inl hx_zero.symm)
  rcases notExercise617Breakpoint_hasAffineOpenInterval (π := π) hpiece
      ⟨hx_pos, hx.2⟩ hnot with
    ⟨a, b, m, c, ha, hb, hEq⟩
  -- A genuine affine neighborhood has only one slope, contradicting the recorded slope change.
  exact hne (affineSideSlopesEqOfAffineOpenInterval hsides ha hb hEq)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: at a minimum of a reflected
sum, each left affine slope is bounded by the opposite right affine slope. -/
private lemma affineSideSlopeBoundsAtReflectedMinimum
    {g : ℝ → ℝ} {x z constant pLeft pRight qLeft qRight : ℝ}
    (hx : HasAffineSidesAt g x pLeft pRight)
    (hz : HasAffineSidesAt g z qLeft qRight)
    (hmin : ∀ y : ℝ,
      constant + g x + g z ≤ constant + g y + g (z + x - y)) :
    pLeft ≤ qRight ∧ qLeft ≤ pRight := by
  rcases hx with ⟨uX, vX, huX, hvX, hxLeft, hxRight⟩
  rcases hz with ⟨uZ, vZ, huZ, hvZ, hzLeft, hzRight⟩
  have hleft_bound : pLeft ≤ qRight := by
    let d : ℝ := min ((x - uX) / 2) ((vZ - z) / 2)
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (half_pos (sub_pos.mpr huX)) (half_pos (sub_pos.mpr hvZ))
    have hx_arg : x - d ∈ Set.Icc uX x := by
      constructor
      · dsimp [d]
        have hd_bound : d ≤ (x - uX) / 2 := min_le_left _ _
        linarith
      · linarith
    have hz_arg : z + d ∈ Set.Icc z vZ := by
      constructor
      · linarith
      · dsimp [d]
        have hd_bound : d ≤ (vZ - z) / 2 := min_le_right _ _
        linarith
    have hminimum := hmin (x - d)
    have hx_formula := hxLeft hx_arg
    have hz_formula := hzRight hz_arg
    have hreflect : z + x - (x - d) = z + d := by ring
    rw [hreflect, hx_formula, hz_formula] at hminimum
    nlinarith
  have hright_bound : qLeft ≤ pRight := by
    let d : ℝ := min ((vX - x) / 2) ((z - uZ) / 2)
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min (half_pos (sub_pos.mpr hvX)) (half_pos (sub_pos.mpr huZ))
    have hx_arg : x + d ∈ Set.Icc x vX := by
      constructor
      · linarith
      · dsimp [d]
        have hd_bound : d ≤ (vX - x) / 2 := min_le_left _ _
        linarith
    have hz_arg : z - d ∈ Set.Icc uZ z := by
      constructor
      · dsimp [d]
        have hd_bound : d ≤ (z - uZ) / 2 := min_le_right _ _
        linarith
      · linarith
    have hminimum := hmin (x + d)
    have hx_formula := hxRight hx_arg
    have hz_formula := hzLeft hz_arg
    have hreflect : z + x - (x + d) = z - d := by ring
    rw [hreflect, hx_formula, hz_formula] at hminimum
    nlinarith
  exact ⟨hleft_bound, hright_bound⟩

/-- Helper for Exercise 6.17: a bad slice on `[0, 1]` has a leftmost global minimizer that is
still bad. -/
lemma leftmostBadSecondSliceMinimizer
    (hcontinuous : Continuous π) {a b : ℝ}
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hbad : subadditivityDefect π a b < 0) :
    ∃ y0 : ℝ,
      y0 ∈ Set.Icc (0 : ℝ) 1 ∧
        subadditivityDefect π a y0 < 0 ∧
        IsMinOn (fun y ↦ subadditivityDefect π a y) (Set.Icc (0 : ℝ) 1) y0 ∧
        (∀ y ∈ Set.Icc (0 : ℝ) 1,
          subadditivityDefect π a y = subadditivityDefect π a y0 → y0 ≤ y) := by
  let slice : ℝ → ℝ := fun y ↦ subadditivityDefect π a y
  have hcont_slice : Continuous slice := by
    -- The fixed-`a` slice inherits continuity from `π`.
    simpa [slice] using continuous_subadditivityDefect_secondSlice (π := π) hcontinuous a
  rcases isCompact_Icc.exists_isMinOn
      (s := Set.Icc (0 : ℝ) 1) (f := slice) ⟨b, hb⟩ hcont_slice.continuousOn with
    ⟨yMin, hyMin_mem, hyMin⟩
  let levelSet : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ {y : ℝ | slice y = slice yMin}
  have hlevel_nonempty : levelSet.Nonempty := by
    refine ⟨yMin, ?_⟩
    exact ⟨hyMin_mem, rfl⟩
  have hcompact_level : IsCompact levelSet := by
    have hclosed_level : IsClosed {y : ℝ | slice y = slice yMin} := by
      exact isClosed_eq hcont_slice continuous_const
    simpa [levelSet] using (isCompact_Icc.inter_right hclosed_level)
  rcases hcompact_level.exists_isMinOn hlevel_nonempty continuous_id.continuousOn with
    ⟨y0, hy0_level, hy0_leftmost⟩
  have hbad0 : slice y0 < 0 := by
    rw [isMinOn_iff] at hyMin
    have hyMin_le_bad : slice yMin ≤ slice b := hyMin b hb
    have hy0_eq : slice y0 = slice yMin := hy0_level.2
    linarith
  have hmin0 : IsMinOn slice (Set.Icc (0 : ℝ) 1) y0 := by
    -- The leftmost point of the minimizing level set is still a global minimizer of the slice.
    rw [isMinOn_iff] at hyMin ⊢
    intro y hy
    calc
      slice y0 = slice yMin := hy0_level.2
      _ ≤ slice y := hyMin y hy
  have hleftmost0 :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, slice y = slice y0 → y0 ≤ y := by
    -- Minimizing the identity on the level set records the leftmost minimizing point.
    intro y hy hy_eq
    have hy_level : y ∈ levelSet := by
      refine ⟨hy, ?_⟩
      exact hy_eq.trans hy0_level.2
    rw [isMinOn_iff] at hy0_leftmost
    exact hy0_leftmost y hy_level
  exact ⟨y0, hy0_level.1, hbad0, hmin0, hleftmost0⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: a minimum on one period of a
one-periodic function is a global minimum. -/
private lemma globalMinimumOfOnePeriodicUnitMinimum
    {g : ℝ → ℝ} (hperiodic : Function.Periodic g 1) {x : ℝ}
    (hmin : IsMinOn g (Set.Icc (0 : ℝ) 1) x) :
    ∀ y : ℝ, g x ≤ g y := by
  rw [isMinOn_iff] at hmin
  intro y
  have hfract_mem : Int.fract y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg y, le_of_lt (Int.fract_lt_one y)⟩
  have hy_period : g y = g (Int.fract y) := by
    calc
      g y = g (Int.fract y + (Int.floor y : ℝ)) := by rw [Int.fract_add_floor]
      _ = g (Int.fract y) := by
        simpa using hperiodic.int_mul (Int.floor y) (Int.fract y)
  calc
    g x ≤ g (Int.fract y) := hmin (Int.fract y) hfract_mem
    _ = g y := hy_period.symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: the fixed-first-coordinate
subadditivity defect inherits one-periodicity from `π`. -/
private lemma subadditivityDefectSecondSlice_periodic
    (hperiodic : Function.Periodic π 1) (a : ℝ) :
    Function.Periodic (fun y ↦ subadditivityDefect π a y) 1 := by
  intro y
  have hsum : π (a + (y + 1)) = π (a + y) := by
    calc
      π (a + (y + 1)) = π ((a + y) + 1) := by ring
      _ = π (a + y) := hperiodic (a + y)
  change π a + π (y + 1) - π (a + (y + 1)) = π a + π y - π (a + y)
  rw [hperiodic y, hsum]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: symmetry rewrites a defect
slice as a constant plus a reflected sum of two values of `π`. -/
private lemma subadditivityDefect_eq_reflectedSum
    (h_symm : ∀ r : ℝ, π r + π (-f - r) = 1) (a y : ℝ) :
    subadditivityDefect π a y = π a - 1 + π y + π (-f - a - y) := by
  have hsymm_eval : π (a + y) + π (-f - a - y) = 1 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h_symm (a + y)
  rw [subadditivityDefect]
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`: a leftmost minimum of a bad
slice is source-facing either at the minimum itself or at its symmetry mate. -/
private lemma breakpointOrMateAtLeftmostSecondSliceMinimum
    (hperiodic : Function.Periodic π 1)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm : ∀ r : ℝ, π r + π (-f - r) = 1)
    {a y0 : ℝ} (hy0 : y0 ∈ Set.Icc (0 : ℝ) 1)
    (hmin : IsMinOn (fun y ↦ subadditivityDefect π a y) (Set.Icc (0 : ℝ) 1) y0)
    (hleftmost : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      subadditivityDefect π a y = subadditivityDefect π a y0 → y0 ≤ y) :
    Exercise617Breakpoint π y0 ∨
      Exercise617Breakpoint π (symmetryMate (f + a) y0) := by
  by_contra hneither
  have hy0_not_break : ¬ Exercise617Breakpoint π y0 :=
    fun hy0_break ↦ hneither (Or.inl hy0_break)
  have hmate_not_break : ¬ Exercise617Breakpoint π (symmetryMate (f + a) y0) :=
    fun hmate_break ↦ hneither (Or.inr hmate_break)
  have hy0_inner : y0 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · refine lt_of_le_of_ne hy0.1 ?_
      intro hy0_zero
      exact hy0_not_break (Or.inl hy0_zero.symm)
    · refine lt_of_le_of_ne hy0.2 ?_
      intro hy0_one
      exact hy0_not_break (Or.inr <| Or.inl hy0_one)
  rcases subadditivityDefectOnSecondSlice_hasAffineOpenInterval
      (π := π) (f := f) hperiodic hpiece h_symm hy0_inner
      hy0_not_break hmate_not_break with
    ⟨u, v, m, c, hu, hv, hEq⟩
  have hIcc_nhds : Set.Icc (0 : ℝ) 1 ∈ nhds y0 := by
    refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hy0_inner) ?_
    intro y hy
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hlocal : IsLocalMin (fun y ↦ subadditivityDefect π a y) y0 :=
    hmin.isLocalMin hIcc_nhds
  rcases affinePlateauOfLocalExtremum hu hv hEq (Or.inr hlocal) with
    ⟨u', v', hu', hv', hplateau⟩
  let y : ℝ := (max u' 0 + y0) / 2
  have hmax_lt : max u' 0 < y0 := max_lt hu' hy0_inner.1
  have hy_lt : y < y0 := by
    dsimp [y]
    linarith
  have hy_interval : y ∈ Set.Ioo u' v' := by
    constructor
    · dsimp [y]
      linarith [le_max_left u' 0]
    · exact hy_lt.trans hv'
  have hy_unit : y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [y]
      linarith [le_max_right u' 0]
    · exact le_trans hy_lt.le hy0.2
  have hy_same : subadditivityDefect π a y = subadditivityDefect π a y0 :=
    hplateau hy_interval
  have hy0_le := hleftmost y hy_unit hy_same
  exact (not_le_of_gt hy_lt) hy0_le

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean

A bad slice already contains a source-facing breakpoint that is locally convex and still violates
subadditivity. -/
lemma existsLocallyConvexSourceBreakpointOnBadSecondSlice
    (hperiodic : Function.Periodic π 1) (hcontinuous : Continuous π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm : ∀ r : ℝ, π r + π (-f - r) = 1)
    {a b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hbad : subadditivityDefect π a b < 0) :
    ∃ b' : ℝ,
      Exercise617Breakpoint π b' ∧
        LocallyConvexAt π b' ∧
        subadditivityDefect π a b' < 0 := by
  rcases leftmostBadSecondSliceMinimizer (π := π) hcontinuous hb hbad with
    ⟨y0, hy0, hbad0, hmin0, hleftmost0⟩
  -- Route correction: work with the raw reflected point for slope comparisons, and only reduce
  -- it modulo one when selecting the source-facing orbit point.
  have horbit :
      Exercise617Breakpoint π y0 ∨
        Exercise617Breakpoint π (symmetryMate (f + a) y0) :=
    breakpointOrMateAtLeftmostSecondSliceMinimum
      hperiodic hpiece h_symm hy0 hmin0 hleftmost0
  rcases periodicPiecewiseLinearHasAffineSidesAtAndFract hperiodic hpiece y0 with
    ⟨pLeft, pRight, hy0_sides, _hy0_fract_sides⟩
  let z : ℝ := -f - a - y0
  rcases periodicPiecewiseLinearHasAffineSidesAtAndFract hperiodic hpiece z with
    ⟨qLeft, qRight, hz_sides, hz_fract_sides⟩
  have hmate_fract : symmetryMate (f + a) y0 = Int.fract z := by
    dsimp [symmetryMate, z]
    congr 1
    ring
  have hmate_sides :
      HasAffineSidesAt π (symmetryMate (f + a) y0) qLeft qRight := by
    rw [hmate_fract]
    exact hz_fract_sides
  have hmate_unit : symmetryMate (f + a) y0 ∈ Set.Ico (0 : ℝ) 1 := by
    rw [hmate_fract]
    exact ⟨Int.fract_nonneg z, Int.fract_lt_one z⟩
  have hslice_periodic :
      Function.Periodic (fun y ↦ subadditivityDefect π a y) 1 :=
    subadditivityDefectSecondSlice_periodic hperiodic a
  have hglobal_min : ∀ y : ℝ,
      subadditivityDefect π a y0 ≤ subadditivityDefect π a y :=
    globalMinimumOfOnePeriodicUnitMinimum hslice_periodic hmin0
  have hreflected_min : ∀ y : ℝ,
      π a - 1 + π y0 + π z ≤ π a - 1 + π y + π (z + y0 - y) := by
    intro y
    have hleft :
        π a - 1 + π y0 + π z = subadditivityDefect π a y0 := by
      symm
      simpa [z] using subadditivityDefect_eq_reflectedSum (π := π) h_symm a y0
    have hright :
        subadditivityDefect π a y = π a - 1 + π y + π (z + y0 - y) := by
      calc
        subadditivityDefect π a y = π a - 1 + π y + π (-f - a - y) :=
          subadditivityDefect_eq_reflectedSum h_symm a y
        _ = π a - 1 + π y + π (z + y0 - y) := by
          congr 2
          dsimp [z]
          ring
    calc
      π a - 1 + π y0 + π z = subadditivityDefect π a y0 := hleft
      _ ≤ subadditivityDefect π a y := hglobal_min y
      _ = π a - 1 + π y + π (z + y0 - y) := hright
  have hslope_bounds : pLeft ≤ qRight ∧ qLeft ≤ pRight :=
    affineSideSlopeBoundsAtReflectedMinimum hy0_sides hz_sides hreflected_min
  have hbad_mate : subadditivityDefect π a (symmetryMate (f + a) y0) < 0 := by
    have htransport := (subadditivityDefectTransport hperiodic h_symm a y0).1
    exact htransport ▸ hbad0
  by_cases hp_order : pLeft ≤ pRight
  · by_cases hy0_break : Exercise617Breakpoint π y0
    · -- If the minimizing orbit point is source-facing, its ordered slopes finish the proof.
      exact ⟨y0, hy0_break,
        locallyConvexAtOfHasAffineSidesAt hy0_sides hp_order, hbad0⟩
    · have hmate_break : Exercise617Breakpoint π (symmetryMate (f + a) y0) :=
        horbit.resolve_left hy0_break
      have hy0_inner : y0 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor
        · refine lt_of_le_of_ne hy0.1 ?_
          intro hy0_zero
          exact hy0_break (Or.inl hy0_zero.symm)
        · refine lt_of_le_of_ne hy0.2 ?_
          intro hy0_one
          exact hy0_break (Or.inr <| Or.inl hy0_one)
      rcases notExercise617Breakpoint_hasAffineOpenInterval (π := π) hpiece
          hy0_inner hy0_break with
        ⟨u, v, m, c, hu, hv, hEq⟩
      have hp_equal : pLeft = pRight :=
        affineSideSlopesEqOfAffineOpenInterval hy0_sides hu hv hEq
      have hq_order : qLeft ≤ qRight := by
        linarith [hslope_bounds.1, hslope_bounds.2]
      exact ⟨symmetryMate (f + a) y0, hmate_break,
        locallyConvexAtOfHasAffineSidesAt hmate_sides hq_order, hbad_mate⟩
  · have hp_reverse : pRight < pLeft := lt_of_not_ge hp_order
    have hq_strict : qLeft < qRight := by
      exact lt_of_le_of_lt hslope_bounds.2 (lt_of_lt_of_le hp_reverse hslope_bounds.1)
    have hmate_break : Exercise617Breakpoint π (symmetryMate (f + a) y0) :=
      exercise617BreakpointOfAffineSideSlopeChange
        hpiece hmate_unit hmate_sides (ne_of_lt hq_strict)
    -- A concave corner at the minimizer forces a strict convex corner at the reflected mate.
    exact ⟨symmetryMate (f + a) y0, hmate_break,
      locallyConvexAtOfHasAffineSidesAt hmate_sides hq_strict.le, hbad_mate⟩

/-- Helper for Exercise 6.17: a failure of global subadditivity yields a violating breakpoint pair
where both breakpoints are locally convex. -/
lemma existsBadLocallyConvexBreakpointPairOfNotSubadditive
    (hperiodic : Function.Periodic π 1) (hcontinuous : Continuous π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm : ∀ r : ℝ, π r + π (-f - r) = 1)
    (hnot : ¬ π.Subadditive) :
    ∃ a b : ℝ,
      Exercise617Breakpoint π a ∧
        Exercise617Breakpoint π b ∧
        LocallyConvexAt π a ∧ LocallyConvexAt π b ∧
        π (a + b) > π a + π b := by
  rcases existsBadPointOnUnitSquareOfNotSubadditive (π := π) hperiodic hnot with
    ⟨a0, b0, ha0, hb0, hbad0_raw⟩
  have hbad0 : subadditivityDefect π a0 b0 < 0 := by
    -- Rewrite the violating inequality into the defect sign convention used in this file.
    dsimp [subadditivityDefect] at *
    linarith
  rcases existsLocallyConvexSourceBreakpointOnBadSecondSlice
      (π := π) (f := f) hperiodic hcontinuous hpiece h_symm hb0 hbad0 with
    ⟨b1, hb1_break, hb1_convex, hbad1⟩
  have hbad1_swapped : subadditivityDefect π b1 a0 < 0 := by
    -- Swap the two coordinates and reuse symmetry of the scalar defect.
    simpa [subadditivityDefect_comm (π := π) a0 b1] using hbad1
  rcases existsLocallyConvexSourceBreakpointOnBadSecondSlice
      (π := π) (f := f) hperiodic hcontinuous hpiece h_symm ha0 hbad1_swapped with
    ⟨a1, ha1_break, ha1_convex, hbad2⟩
  refine ⟨a1, b1, ha1_break, hb1_break, ha1_convex, hb1_convex, ?_⟩
  -- Swap back to the user-facing order and unfold the defect inequality.
  have hbad2' : π (b1 + a1) > π b1 + π a1 := by
    dsimp [subadditivityDefect] at hbad2
    linarith
  simpa [add_comm, add_left_comm, add_assoc] using hbad2'

/-- Exercise 6.17 (1). For a continuous nonnegative periodic function `π : ℝ → ℝ` with `π 0 = 0`
that is piecewise-linear on `[0, 1]`, it suffices to verify the symmetry condition at the
source-facing breakpoints of `π` in the interval, independent of the chosen piecewise-linear
witness. This theorem is part of the remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_17.lean`. -/
theorem exercise_6_17_symmetry_check_on_breakpoints_suffices
    (hperiodic : Function.Periodic π 1) (hcontinuous : Continuous π)
    (hnonneg : ∀ r : ℝ, 0 ≤ π r) (hzero : π 0 = 0)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm_breakpoints :
      ∀ ⦃r : ℝ⦄, Exercise617Breakpoint π r → π r + π (-f - r) = 1) :
    ∀ r : ℝ, π r + π (-f - r) = 1 := by
  -- Route correction: once the defect is `1` on `[0,1]`, periodicity globalizes the statement.
  let defect : ℝ → ℝ := fun r ↦ π r + π (-f - r)
  have hdefect_periodic : Function.Periodic defect 1 := by
    intro r
    dsimp [defect]
    rw [hperiodic r]
    have hshift : π (-f - (r + 1)) = π (-f - r) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (hperiodic (-f - r - 1)).symm
    rw [hshift]
  have hunit :
      Set.EqOn defect (fun _ ↦ (1 : ℝ)) (Set.Icc (0 : ℝ) 1) :=
    symmetryEqOneOnUnitIntervalOfBreakpointCheck
      hperiodic hcontinuous hpiece h_symm_breakpoints
  have hglobal :
      defect = fun _ ↦ (1 : ℝ) :=
    eq_of_eqOn_unitInterval_of_onePeriodic hdefect_periodic
      (by intro r; rfl) hunit
  intro r
  have heq : π r + π (-f - r) = 1 := by
    simpa [defect] using congrFun hglobal r
  have hrelaxed : π r + π (-f - r) ≤ 1 + π 0 := by
    calc
      π r + π (-f - r) = 1 := heq
      _ ≤ 1 + π 0 := le_add_of_nonneg_right (hnonneg 0)
  have hupper : π r + π (-f - r) ≤ 1 := by
    calc
      π r + π (-f - r) ≤ 1 + π 0 := hrelaxed
      _ = 1 := by rw [hzero, add_zero]
  exact le_antisymm hupper heq.ge

/-- Exercise 6.17 (2). Assume in addition that `π` satisfies the Chapter 6 symmetry condition,
equivalently `π(r) + π(-f-r) = 1` for every real `r`. For a continuous nonnegative periodic
piecewise-linear function with `π 0 = 0`, it is enough to verify `π(a + b) ≤ π(a) + π(b)` at
source-facing breakpoint pairs `a, b` in `[0, 1]` where `π` is locally convex. -/
theorem exercise_6_17_subadditivity_check_on_locally_convex_breakpoints_suffices
    (hperiodic : Function.Periodic π 1) (hcontinuous : Continuous π)
    (hnonneg : ∀ r : ℝ, 0 ≤ π r) (hzero : π 0 = 0)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (h_symm : ∀ r : ℝ, π r + π (-f - r) = 1)
    (h_subadd_breakpoints :
      ∀ ⦃a b : ℝ⦄, Exercise617Breakpoint π a →
        Exercise617Breakpoint π b →
        LocallyConvexAt π a → LocallyConvexAt π b → π (a + b) ≤ π a + π b) :
    π.Subadditive := by
  classical
  -- A positive defect at a source-facing locally convex pair contradicts the checked inequalities.
  by_contra hnot
  rcases existsBadLocallyConvexBreakpointPairOfNotSubadditive
      hperiodic hcontinuous hpiece h_symm hnot with
    ⟨a, b, ha_break, hb_break, ha_convex, hb_convex, hbad⟩
  have hchecked : π (a + b) ≤ π a + π b :=
    h_subadd_breakpoints ha_break hb_break ha_convex hb_convex
  have hrelaxed : π (a + b) ≤ π a + π b + π 0 := by
    exact hchecked.trans (le_add_of_nonneg_right (hnonneg 0))
  have hchecked' : π (a + b) ≤ π a + π b := by
    calc
      π (a + b) ≤ π a + π b + π 0 := hrelaxed
      _ = π a + π b := by rw [hzero, add_zero]
  linarith

end Exercise617

#print axioms existsLocallyConvexSourceBreakpointOnBadSecondSlice
#print axioms exercise_6_17_symmetry_check_on_breakpoints_suffices
#print axioms exercise_6_17_subadditivity_check_on_locally_convex_breakpoints_suffices
