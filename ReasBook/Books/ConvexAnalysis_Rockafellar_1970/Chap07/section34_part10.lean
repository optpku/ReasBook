/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part9

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePredPart10 {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

section SaddleAmbient

/-- Membership in the open unit interval for a vector in `Fin 1 → ℝ`. -/
def InOpenUnitInterval (x : Fin 1 → ℝ) : Prop :=
  0 < x 0 ∧ x 0 < 1

/-- Membership in the closed unit interval for a vector in `Fin 1 → ℝ`. -/
def InClosedUnitInterval (x : Fin 1 → ℝ) : Prop :=
  0 ≤ x 0 ∧ x 0 ≤ 1

/-- The one-dimensional power kernel `(u, v) ↦ u^v`, written on `Fin 1 → ℝ` coordinates. -/
noncomputable def oneDimensionalPowerKernel (u v : Fin 1 → ℝ) : EReal :=
  ((Real.rpow (u 0) (v 0) : ℝ) : EReal)

/-- The saddle-function `K(u, v) = u^v` on the open unit square, represented on all of `ℝ × ℝ`
by the upper simple-extension convention for concave-convex saddle-functions. -/
noncomputable def openUnitSquarePowerSaddle : SaddleFunction 1 1 :=
  fun u v =>
    if InOpenUnitInterval v then
      if InOpenUnitInterval u then oneDimensionalPowerKernel u v else ⊥
    else
      ⊤

/-- The explicit upper-closure formula for the open-square power saddle-function. -/
noncomputable def openUnitSquarePowerUpperClosureFormula : SaddleFunction 1 1 :=
  fun u v =>
    if u 0 = 0 ∧ v 0 = 0 then
      ((1 : ℝ) : EReal)
    else if InClosedUnitInterval v then
      if InClosedUnitInterval u then oneDimensionalPowerKernel u v else ⊥
    else
      ⊤

/-- The explicit lower-closure formula for the open-square power saddle-function. -/
noncomputable def openUnitSquarePowerLowerClosureFormula : SaddleFunction 1 1 :=
  fun u v =>
    if u 0 = 0 ∧ v 0 = 0 then
      ((0 : ℝ) : EReal)
    else if InClosedUnitInterval v then
      if InClosedUnitInterval u then oneDimensionalPowerKernel u v else ⊥
    else
      ⊤

/-- Helper for Text 34.1.1: on `Fin 1`, the norm of a difference is the absolute value of
the unique coordinate difference. -/
lemma helperForText_34_1_1_norm_fin1_eq_abs (u w : Fin 1 → ℝ) :
    ‖w - u‖ = |w 0 - u 0| := by
  -- Rewrite a `Fin 1` vector difference as a constant one-coordinate function.
  have hRewrite : w - u = fun _ : Fin 1 => w 0 - u 0 := by
    ext i
    fin_cases i
    simp
  -- Then the sup norm on a singleton index set collapses to the absolute value.
  rw [hRewrite, Pi.norm_def]
  simp [Real.norm_eq_abs]

/-- Helper for Text 34.1.1: if a point lies outside `[0, 1]`, some ball around it misses the
open unit interval `(0, 1)`. -/
lemma helperForText_34_1_1_exists_radius_outside_closedUnitInterval
    (u : Fin 1 → ℝ) (hu : ¬ InClosedUnitInterval u) :
    ∃ ε : {r : ℝ // 0 < r},
      ∀ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}, ¬ InOpenUnitInterval w.1 := by
  by_cases hLeft : u 0 < 0
  · -- A point strictly left of `0` has a small neighborhood staying left of `0`.
    refine ⟨⟨-u 0 / 2, by linarith⟩, ?_⟩
    intro w hwOpen
    have hw := w.2
    rw [helperForText_34_1_1_norm_fin1_eq_abs] at hw
    rcases hwOpen with ⟨hw0, hw1⟩
    have habs := abs_lt.mp hw
    linarith
  · -- Otherwise `u 0 > 1`, so a small neighborhood stays strictly right of `1`.
    have hRight : 1 < u 0 := by
      rcases not_and_or.mp hu with hNeg | hGt
      · exfalso
        exact hLeft (lt_of_not_ge hNeg)
      · linarith
    refine ⟨⟨(u 0 - 1) / 2, by linarith⟩, ?_⟩
    intro w hwOpen
    have hw := w.2
    rw [helperForText_34_1_1_norm_fin1_eq_abs] at hw
    rcases hwOpen with ⟨hw0, hw1⟩
    have habs := abs_lt.mp hw
    linarith

/-- Helper for Text 34.1.1: if the second variable is already outside `(0, 1)`, the first
partial closure sees a constant `⊤` section. -/
lemma helperForText_34_1_1_partialClosure1_eq_top_of_not_inOpenUnitInterval
    {u v : Fin 1 → ℝ} (hv : ¬ InOpenUnitInterval v) :
    partialClosure₁ openUnitSquarePowerSaddle u v = ⊤ := by
  -- Unfold the first partial closure into an infimum of local suprema.
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm le_top
  refine le_iInf ?_
  intro ε
  -- The center point itself already contributes the value `⊤` to each local supremum.
  let wu : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1} := ⟨u, by simpa using ε.2⟩
  have hValue : openUnitSquarePowerSaddle wu.1 v = ⊤ := by
    simp [openUnitSquarePowerSaddle, hv]
  calc
    (⊤ : EReal) = openUnitSquarePowerSaddle wu.1 v := by simp [hValue]
    _ ≤ ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}, openUnitSquarePowerSaddle w.1 v :=
      le_iSup (fun w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1} => openUnitSquarePowerSaddle w.1 v) wu

/-- Helper for Text 34.1.1: if the first variable lies outside `[0, 1]` while the second
variable stays in `(0, 1)`, the first partial closure is already `⊥`. -/
lemma helperForText_34_1_1_partialClosure1_eq_bot_of_not_inClosedUnitInterval
    {u v : Fin 1 → ℝ} (hu : ¬ InClosedUnitInterval u) (hv : InOpenUnitInterval v) :
    partialClosure₁ openUnitSquarePowerSaddle u v = ⊥ := by
  rcases helperForText_34_1_1_exists_radius_outside_closedUnitInterval u hu with ⟨ε, hε⟩
  -- Use the radius from the exclusion lemma to force one local supremum to be `⊥`.
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm
  · have hLocal :
        (⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}, openUnitSquarePowerSaddle w.1 v) = ⊥ := by
      apply le_antisymm
      · refine iSup_le ?_
        intro w
        have hwNoOpen : ¬ InOpenUnitInterval w.1 := hε w
        have hValue : openUnitSquarePowerSaddle w.1 v = ⊥ := by
          simp [openUnitSquarePowerSaddle, hv, hwNoOpen]
        rw [hValue]
      · exact bot_le
    calc
      (⨅ ε' : {ε' : ℝ // 0 < ε'},
          ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε'.1}, openUnitSquarePowerSaddle w.1 v)
          ≤ ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}, openUnitSquarePowerSaddle w.1 v :=
            iInf_le _ ε
      _ = ⊥ := hLocal
  · exact bot_le

/-- Helper for Text 34.1.1: if the second variable lies outside `[0, 1]`, the second partial
closure already attains the constant value `⊤`. -/
lemma helperForText_34_1_1_partialClosure2_eq_top_of_not_inClosedUnitInterval
    {u v : Fin 1 → ℝ} (hv : ¬ InClosedUnitInterval v) :
    partialClosure₂ openUnitSquarePowerSaddle u v = ⊤ := by
  rcases helperForText_34_1_1_exists_radius_outside_closedUnitInterval v hv with ⟨ε, hε⟩
  -- A small second-variable ball missing `(0, 1)` makes the inner infimum equal `⊤`.
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm le_top
  have hLocal :
      (⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1}, openUnitSquarePowerSaddle u w.1) = ⊤ := by
    apply le_antisymm le_top
    refine le_iInf ?_
    intro w
    have hwNoOpen : ¬ InOpenUnitInterval w.1 := hε w
    simp [openUnitSquarePowerSaddle, hwNoOpen]
  calc
    (⊤ : EReal)
        ≤ ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1}, openUnitSquarePowerSaddle u w.1 := by
          rw [hLocal]
    _ ≤
      ⨆ ε' : {ε' : ℝ // 0 < ε'},
        ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε'.1}, openUnitSquarePowerSaddle u w.1 :=
          le_iSup (fun ε' : {ε' : ℝ // 0 < ε'} =>
            ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε'.1}, openUnitSquarePowerSaddle u w.1) ε

/-- Helper for Text 34.1.1: every neighborhood of a point in `[0, 1]` meets the open interval
`(0, 1)`. -/
lemma helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval
    (v : Fin 1 → ℝ) (hv : InClosedUnitInterval v) (ε : {r : ℝ // 0 < r}) :
    ∃ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1}, InOpenUnitInterval w.1 := by
  rcases hv with ⟨hv0, hv1⟩
  by_cases hZero : v 0 = 0
  · let t : ℝ := min (ε.1 / 2) (1 / 2)
    have ht_pos : 0 < t := by
      -- The chosen interior point is positive because both entries in the minimum are positive.
      dsimp [t]
      apply lt_min
      · linarith [ε.2]
      · norm_num
    have ht_lt_one : t < 1 := by
      -- The same choice also stays strictly below `1` because it is at most `1 / 2`.
      dsimp [t]
      have hHalfBound : min (ε.1 / 2) (1 / 2) ≤ (1 / 2 : ℝ) := min_le_right _ _
      linarith
    have ht_lt_eps : t < ε.1 := by
      -- Its distance from `0` is strictly less than the prescribed radius.
      dsimp [t]
      have hLeft : min (ε.1 / 2) (1 / 2) ≤ ε.1 / 2 := min_le_left _ _
      linarith [ε.2]
    have hMem : ‖(fun _ : Fin 1 => t) - v‖ < ε.1 := by
      -- On `Fin 1`, the norm reduces to the absolute value of the unique coordinate difference.
      rw [helperForText_34_1_1_norm_fin1_eq_abs]
      have hAbs : |t - v 0| < ε.1 := by
        rw [hZero, sub_zero, abs_of_pos ht_pos]
        exact ht_lt_eps
      simpa using hAbs
    refine ⟨⟨fun _ : Fin 1 => t, hMem⟩, ?_⟩
    -- The chosen point lies in `(0, 1)` by construction.
    exact ⟨ht_pos, ht_lt_one⟩
  · by_cases hOne : v 0 = 1
    · let δ : ℝ := min (ε.1 / 2) (1 / 2)
      let t : ℝ := 1 - δ
      have hδ_pos : 0 < δ := by
        -- The inward shift from `1` is positive for the same reason as in the `0`-boundary case.
        dsimp [δ]
        apply lt_min
        · linarith [ε.2]
        · norm_num
      have hδ_lt_one : δ < 1 := by
        -- The inward shift is also strictly smaller than `1`, so `1 - δ` stays positive.
        dsimp [δ]
        have hHalfBound : min (ε.1 / 2) (1 / 2) ≤ (1 / 2 : ℝ) := min_le_right _ _
        linarith
      have hδ_lt_eps : δ < ε.1 := by
        -- Its size is bounded by `ε / 2`, hence still strictly below `ε`.
        dsimp [δ]
        have hLeft : min (ε.1 / 2) (1 / 2) ≤ ε.1 / 2 := min_le_left _ _
        linarith [ε.2]
      have ht_pos : 0 < t := by
        linarith
      have ht_lt_one : t < 1 := by
        linarith
      have hMem : ‖(fun _ : Fin 1 => t) - v‖ < ε.1 := by
        -- Here the distance to `v 0 = 1` is exactly the inward shift `δ`.
        rw [helperForText_34_1_1_norm_fin1_eq_abs]
        have hAbs : |t - v 0| < ε.1 := by
          rw [hOne, show t - (1 : ℝ) = -δ by dsimp [t]; ring, abs_neg, abs_of_pos hδ_pos]
          exact hδ_lt_eps
        simpa using hAbs
      refine ⟨⟨fun _ : Fin 1 => t, hMem⟩, ?_⟩
      -- The shifted point now lies strictly between `0` and `1`.
      exact ⟨ht_pos, ht_lt_one⟩
    · have hvOpen : InOpenUnitInterval v := by
        -- Away from the two endpoints, a closed-unit-interval point is already interior.
        have hZero' : (0 : ℝ) ≠ v 0 := by
          intro hEq
          apply hZero
          exact hEq.symm
        have hvPos : 0 < v 0 := lt_of_le_of_ne hv0 hZero'
        have hvLtOne : v 0 < 1 := lt_of_le_of_ne hv1 hOne
        constructor
        · exact hvPos
        · exact hvLtOne
      have hMem : ‖v - v‖ < ε.1 := by
        -- The center of the ball is always an admissible witness.
        simpa using ε.2
      refine ⟨⟨v, hMem⟩, hvOpen⟩

/-- Helper for Text 34.1.1: once `u` is outside `(0, 1)`, every neighborhood of a point
`v ∈ [0, 1]` already sees the value `⊥` in the second partial closure. -/
lemma helperForText_34_1_1_partialClosure2_eq_bot_of_not_inOpenUnitInterval
    {u v : Fin 1 → ℝ} (hu : ¬ InOpenUnitInterval u) (hv : InClosedUnitInterval v) :
    partialClosure₂ openUnitSquarePowerSaddle u v = ⊥ := by
  -- Every `v`-ball inside `[0,1]` contains an open-interval point where the original saddle
  -- function already takes the value `⊥`.
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm
  · refine iSup_le ?_
    intro ε
    rcases helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval v hv ε with
      ⟨w, hwOpen⟩
    have hValue : openUnitSquarePowerSaddle u w.1 = ⊥ := by
      simp [openUnitSquarePowerSaddle, hwOpen, hu]
    calc
      (⨅ z : {z : Fin 1 → ℝ // ‖z - v‖ < ε.1}, openUnitSquarePowerSaddle u z.1)
          ≤ openUnitSquarePowerSaddle u w.1 := iInf_le _ w
      _ = ⊥ := hValue
  · exact bot_le

/-- Helper for Text 34.1.1: convex combinations of points in `(0, 1)` stay in `(0, 1)` on
`Fin 1`. -/
lemma helperForText_34_1_1_openUnitInterval_combo_mem
    {x y : Fin 1 → ℝ} {a b : ℝ}
    (hx : InOpenUnitInterval x) (hy : InOpenUnitInterval y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    InOpenUnitInterval (a • x + b • y) := by
  -- Pass to the unique coordinate, where convexity of `(0,1)` gives the claim immediately.
  have hxy : a * x 0 + b * y 0 ∈ Set.Ioo (0 : ℝ) 1 :=
    (convex_Ioo (0 : ℝ) 1) hx hy ha hb hab
  simpa [InOpenUnitInterval, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hxy

/-- Helper for Text 34.1.1: the off-domain second-variable section at `u = 2` is not convex on
all of `ℝ`, so the upper simple extension cannot be concave-convex on `Set.univ × Set.univ`. -/
lemma helperForText_34_1_1_secondSection_not_convex_at_two :
    ¬ IsERealConvexOn (Set.univ : Set (Fin 1 → ℝ))
      (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (2 : ℝ)) v) := by
  intro hConv
  let x : Fin 1 → ℝ := fun _ => (1 / 2 : ℝ)
  let y : Fin 1 → ℝ := fun _ => (2 : ℝ)
  let a : ℝ := 1 / 2
  let b : ℝ := 1 / 2
  have hx : x ∈ (Set.univ : Set (Fin 1 → ℝ)) := by
    simp
  have hy : y ∈ (Set.univ : Set (Fin 1 → ℝ)) := by
    simp
  have ha : 0 ≤ a := by
    norm_num [a]
  have hb : 0 ≤ b := by
    norm_num [b]
  have hab : a + b = 1 := by
    norm_num [a, b]
  have hxy : a • x + b • y ∈ (Set.univ : Set (Fin 1 → ℝ)) := by
    simp
  -- Evaluate Jensen's inequality on one open point and one off-domain point.
  have hIneq := hConv (x := x) (y := y) hx hy ha hb hab hxy
  have hUNotOpen : ¬ InOpenUnitInterval (fun _ : Fin 1 => (2 : ℝ)) := by
    simp [InOpenUnitInterval]
  have hxOpen : InOpenUnitInterval x := by
    dsimp [x, InOpenUnitInterval]
    constructor <;> norm_num
  have hyNotOpen : ¬ InOpenUnitInterval y := by
    dsimp [y, InOpenUnitInterval]
    norm_num
  have hxyNotOpen : ¬ InOpenUnitInterval (a • x + b • y) := by
    dsimp [a, b, x, y, InOpenUnitInterval]
    norm_num
  have hLeft :
      (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (2 : ℝ)) v) (a • x + b • y) = ⊤ := by
    -- The midpoint already leaves `(0,1)`, so the section takes the off-domain value `⊤`.
    simp [openUnitSquarePowerSaddle, hxyNotOpen]
  have hRight :
      ((a : EReal) * (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (2 : ℝ)) v) x +
        (b : EReal) * (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (2 : ℝ)) v) y) = ⊥ := by
    have haPos : 0 < a := by
      norm_num [a]
    have hxVal :
        (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (2 : ℝ)) v) x = ⊥ := by
      -- At the open point `x = 1/2`, the off-domain first variable forces the value `⊥`.
      simp [openUnitSquarePowerSaddle, hxOpen, hUNotOpen]
    have hyVal :
        (fun v => openUnitSquarePowerSaddle (fun _ : Fin 1 => (2 : ℝ)) v) y = ⊤ := by
      -- At the off-domain point `y = 2`, the second variable branch is already `⊤`.
      simp [openUnitSquarePowerSaddle, hyNotOpen]
    -- The weighted sum collapses to `⊥`, contradicting the required upper bound for `⊤`.
    rw [hxVal, hyVal, EReal.coe_mul_bot_of_pos haPos, EReal.bot_add]
  rw [hLeft, hRight] at hIneq
  simp at hIneq

/-- Helper for Text 34.1.1: the chosen upper simple extension is not concave-convex on all of
`ℝ × ℝ`, because one off-domain second-variable section already fails convexity. -/
lemma helperForText_34_1_1_openUnitSquarePowerSaddle_not_concaveConvex :
    ¬ IsConcaveConvex openUnitSquarePowerSaddle := by
  intro hK
  -- Unpack the second-variable convexity clause and specialize it to the off-domain section
  -- `u = 2`.
  exact
    helperForText_34_1_1_secondSection_not_convex_at_two
      ((show IsConcaveConvexOn (Set.univ : Set (Fin 1 → ℝ)) (Set.univ : Set (Fin 1 → ℝ))
          openUnitSquarePowerSaddle from hK).2
        (fun _ : Fin 1 => (2 : ℝ)) (by simp))

/-- Helper for Text 34.1.1: there is no global concave-convex witness for the chosen upper
simple extension, so the theorem header cannot be repaired locally by supplying an auxiliary
proof of `IsConcaveConvex openUnitSquarePowerSaddle`. -/
lemma helperForText_34_1_1_no_globalConcaveConvexWitness :
    ¬ ∃ hK : IsConcaveConvex openUnitSquarePowerSaddle,
      upperClosureConcaveConvex openUnitSquarePowerSaddle hK =
        openUnitSquarePowerUpperClosureFormula := by
  rintro ⟨hK, -⟩
  -- The off-domain second-variable section at `u = 2` already violates convexity, so no
  -- global concave-convex witness can exist.
  exact helperForText_34_1_1_openUnitSquarePowerSaddle_not_concaveConvex hK

/-- Helper for Text 34.1.1: the type of global concave-convex witnesses for the chosen upper
simple extension is empty, because the off-domain section at `u = 2` already violates convexity
on `Set.univ`. -/
lemma helperForText_34_1_1_globalConcaveConvexWitness_isEmpty :
    IsEmpty (IsConcaveConvex openUnitSquarePowerSaddle) := by
  refine ⟨?_⟩
  intro hK
  -- Any putative global witness is eliminated by the explicit off-domain Jensen counterexample.
  exact helperForText_34_1_1_openUnitSquarePowerSaddle_not_concaveConvex hK

/-- Helper for Text 34.1.1: on `[0, 1] × (0, 1)`, every first-variable neighborhood already
contains an open-interval point where the upper simple extension takes a nonnegative real
value, so the first partial closure is nonnegative. -/
lemma helperForText_34_1_1_partialClosure1_nonneg_of_closedFirst_openSecond
    {u v : Fin 1 → ℝ} (hu : InClosedUnitInterval u) (hv : InOpenUnitInterval v) :
    ((0 : ℝ) : EReal) ≤ partialClosure₁ openUnitSquarePowerSaddle u v := by
  -- Every positive-radius first-variable ball meets `(0,1)`, and at that witness the original
  -- power kernel is a nonnegative real number.
  unfold partialClosure₁ concaveClosureInFirst
  refine le_iInf ?_
  intro ε
  rcases helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval u hu ε with
    ⟨w, hwOpen⟩
  have hValue : ((0 : ℝ) : EReal) ≤ openUnitSquarePowerSaddle w.1 v := by
    have hrpow : 0 ≤ (w.1 0) ^ (v 0) := Real.rpow_nonneg hwOpen.1.le _
    simpa [openUnitSquarePowerSaddle, hv, hwOpen, oneDimensionalPowerKernel] using hrpow
  exact le_trans hValue
    (le_iSup (fun w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1} => openUnitSquarePowerSaddle w.1 v) w)

/-- Helper for Text 34.1.1: on `[0, 1] × (0, 1)`, the first partial closure already recovers
the original power kernel. -/
lemma helperForText_34_1_1_partialClosure1_eq_powerKernel_of_closedFirst_openSecond
    {u v : Fin 1 → ℝ} (hu : InClosedUnitInterval u) (hv : InOpenUnitInterval v) :
    partialClosure₁ openUnitSquarePowerSaddle u v = oneDimensionalPowerKernel u v := by
  have hCont : ContinuousAt (fun x : ℝ => x ^ (v 0)) (u 0) :=
    Real.continuousAt_rpow_const (u 0) (v 0) (Or.inr hv.1.le)
  have hNonnegClosure :
      ((0 : ℝ) : EReal) ≤ partialClosure₁ openUnitSquarePowerSaddle u v :=
    helperForText_34_1_1_partialClosure1_nonneg_of_closedFirst_openSecond hu hv
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm
  · -- Small first-variable balls keep the open-interval power values uniformly below any
    -- prescribed upper barrier, while off-open points only contribute `⊥`.
    refine (EReal.le_of_forall_lt_iff_le (x := oneDimensionalPowerKernel u v)
      (y := ⨅ ε : {ε : ℝ // 0 < ε},
        ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}, openUnitSquarePowerSaddle w.1 v)).1 ?_
    intro z hz
    have hzReal : (u 0) ^ (v 0) < z := by
      simpa [oneDimensionalPowerKernel] using hz
    have hGap : 0 < z - (u 0) ^ (v 0) := by
      linarith
    rcases (Metric.continuousAt_iff.mp hCont) (z - (u 0) ^ (v 0)) hGap with ⟨δ, hδPos, hδ⟩
    let ε : {ε : ℝ // 0 < ε} := ⟨δ, hδPos⟩
    calc
      (⨅ ε' : {ε' : ℝ // 0 < ε'},
          ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε'.1}, openUnitSquarePowerSaddle w.1 v)
          ≤ ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}, openUnitSquarePowerSaddle w.1 v :=
            iInf_le _ ε
      _ ≤ ((z : ℝ) : EReal) := by
        refine iSup_le ?_
        intro w
        by_cases hwOpen : InOpenUnitInterval w.1
        · have hwNorm : ‖w.1 - u‖ < δ := w.2
          rw [helperForText_34_1_1_norm_fin1_eq_abs] at hwNorm
          have hwCoord : dist (w.1 0) (u 0) < δ := by
            simpa [Real.dist_eq] using hwNorm
          have hPowDist : dist ((w.1 0) ^ (v 0)) ((u 0) ^ (v 0)) < z - (u 0) ^ (v 0) :=
            hδ hwCoord
          have hAbs : |(w.1 0) ^ (v 0) - (u 0) ^ (v 0)| < z - (u 0) ^ (v 0) := by
            simpa [Real.dist_eq] using hPowDist
          have hPowLt : (w.1 0) ^ (v 0) < z := by
            have hUpper : (w.1 0) ^ (v 0) - (u 0) ^ (v 0) < z - (u 0) ^ (v 0) :=
              (abs_lt.mp hAbs).2
            linarith
          have hValue : openUnitSquarePowerSaddle w.1 v = oneDimensionalPowerKernel w.1 v := by
            simp [openUnitSquarePowerSaddle, hv, hwOpen]
          rw [hValue]
          simpa [oneDimensionalPowerKernel] using hPowLt.le
        · have hValue : openUnitSquarePowerSaddle w.1 v = ⊥ := by
            simp [openUnitSquarePowerSaddle, hv, hwOpen]
          rw [hValue]
          exact bot_le
  · -- Any lower barrier below `u^v` is preserved on a smaller neighborhood, and each such
    -- neighborhood still contains an open-interval witness contributing a value above it.
    refine (forall_lt_iff_le).1 ?_
    intro z hz
    cases z using EReal.rec with
    | bot =>
        have hNonnegClosure' :
            ((0 : ℝ) : EReal) ≤
              ⨅ ε : {ε : ℝ // 0 < ε},
                ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}, openUnitSquarePowerSaddle w.1 v := by
          simpa [partialClosure₁, concaveClosureInFirst] using hNonnegClosure
        exact lt_of_lt_of_le (by norm_num) hNonnegClosure'
    | coe zr =>
        have hzReal : zr < (u 0) ^ (v 0) := by
          simpa [oneDimensionalPowerKernel] using hz
        by_cases hzNonneg : 0 ≤ zr
        · let β : ℝ := (zr + (u 0) ^ (v 0)) / 2
          have hzBeta : zr < β := by
            dsimp [β]
            linarith
          have hGap : 0 < (u 0) ^ (v 0) - β := by
            dsimp [β]
            linarith
          rcases (Metric.continuousAt_iff.mp hCont) ((u 0) ^ (v 0) - β) hGap with
            ⟨δ, hδPos, hδ⟩
          have hClosureLower :
              (β : EReal) ≤
                ⨅ ε : {ε : ℝ // 0 < ε},
                  ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}, openUnitSquarePowerSaddle w.1 v := by
            refine le_iInf ?_
            intro ε
            let η : {r : ℝ // 0 < r} := by
              refine ⟨min δ (ε.1 / 2), ?_⟩
              apply lt_min
              · exact hδPos
              · linarith [ε.2]
            rcases helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval u hu η with
              ⟨w, hwOpen⟩
            have hwInEps : ‖w.1 - u‖ < ε.1 := by
              have hwHalf : ‖w.1 - u‖ < ε.1 / 2 := lt_of_lt_of_le w.2 (min_le_right _ _)
              linarith [ε.2]
            have hwNorm : ‖w.1 - u‖ < δ := lt_of_lt_of_le w.2 (min_le_left _ _)
            rw [helperForText_34_1_1_norm_fin1_eq_abs] at hwNorm
            have hwCoord : dist (w.1 0) (u 0) < δ := by
              simpa [Real.dist_eq] using hwNorm
            have hPowDist : dist ((w.1 0) ^ (v 0)) ((u 0) ^ (v 0)) < (u 0) ^ (v 0) - β :=
              hδ hwCoord
            have hAbs : |(w.1 0) ^ (v 0) - (u 0) ^ (v 0)| < (u 0) ^ (v 0) - β := by
              simpa [Real.dist_eq] using hPowDist
            have hPowGt : β < (w.1 0) ^ (v 0) := by
              have hLower :
                  -((u 0) ^ (v 0) - β) < (w.1 0) ^ (v 0) - (u 0) ^ (v 0) :=
                (abs_lt.mp hAbs).1
              linarith
            have hValue : openUnitSquarePowerSaddle w.1 v = oneDimensionalPowerKernel w.1 v := by
              simp [openUnitSquarePowerSaddle, hv, hwOpen]
            calc
              (β : EReal) ≤ openUnitSquarePowerSaddle w.1 v := by
                rw [hValue]
                exact le_of_lt <| by
                  simpa [oneDimensionalPowerKernel] using hPowGt
              _ ≤
                ⨆ w' : {w' : Fin 1 → ℝ // ‖w' - u‖ < ε.1}, openUnitSquarePowerSaddle w'.1 v :=
                  le_iSup
                    (fun w' : {w' : Fin 1 → ℝ // ‖w' - u‖ < ε.1} =>
                      openUnitSquarePowerSaddle w'.1 v)
                    ⟨w.1, hwInEps⟩
          exact lt_of_lt_of_le (by exact_mod_cast hzBeta) hClosureLower
        · have hNeg : (zr : EReal) < ((0 : ℝ) : EReal) := by
            exact_mod_cast lt_of_not_ge hzNonneg
          have hNonnegClosure' :
              ((0 : ℝ) : EReal) ≤
                ⨅ ε : {ε : ℝ // 0 < ε},
                  ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}, openUnitSquarePowerSaddle w.1 v := by
            simpa [partialClosure₁, concaveClosureInFirst] using hNonnegClosure
          exact lt_of_lt_of_le hNeg hNonnegClosure'
    | top =>
        exfalso
        exact not_lt_of_ge le_top hz

/-- Helper for Text 34.1.1: the first partial closure extends the `u`-variable from `(0, 1)`
to `[0, 1]` while keeping the second variable open. -/
lemma helperForText_34_1_1_partialClosure1_formula :
    partialClosure₁ openUnitSquarePowerSaddle =
      fun u v =>
        if InOpenUnitInterval v then
          if InClosedUnitInterval u then oneDimensionalPowerKernel u v else (⊥ : EReal)
        else
          (⊤ : EReal) := by
  funext u
  funext v
  by_cases hv : InOpenUnitInterval v
  · by_cases hu : InClosedUnitInterval u
    · -- The closed strip `[0,1] × (0,1)` is now covered by the direct continuity computation.
      have hValue : partialClosure₁ openUnitSquarePowerSaddle u v = oneDimensionalPowerKernel u v :=
        helperForText_34_1_1_partialClosure1_eq_powerKernel_of_closedFirst_openSecond hu hv
      simp [hv, hu, hValue]
    · -- Outside `[0,1]` in the first variable, the first partial closure is already `⊥`.
      have hValue : partialClosure₁ openUnitSquarePowerSaddle u v = ⊥ :=
        helperForText_34_1_1_partialClosure1_eq_bot_of_not_inClosedUnitInterval hu hv
      simp [hv, hu, hValue]
  · -- Outside `(0,1)` in the second variable, the first partial closure is constantly `⊤`.
    have hValue : partialClosure₁ openUnitSquarePowerSaddle u v = ⊤ :=
      helperForText_34_1_1_partialClosure1_eq_top_of_not_inOpenUnitInterval hv
    simp [hv, hValue]

-- TODO: the off-domain `⊤` branch and the non-open-`u` `⊥` branch are now isolated below.
-- The only missing work is the closed-square `u^v` computation, including the boundary values
-- at `v = 0` and `v = 1`.
/-- Helper for Text 34.1.1: when the first variable stays in `(0, 1)`, every value entering the
second partial closure is nonnegative, so the closure itself is also nonnegative. -/
lemma helperForText_34_1_1_partialClosure2_nonneg_of_openFirst
    {u v : Fin 1 → ℝ} (hu : InOpenUnitInterval u) :
    ((0 : ℝ) : EReal) ≤ partialClosure₂ openUnitSquarePowerSaddle u v := by
  -- A single positive-radius neighborhood already has all section values in `[0, +∞]`.
  unfold partialClosure₂ convexClosureInSecond
  let ε : {ε : ℝ // 0 < ε} := ⟨1 / 2, by positivity⟩
  refine le_trans ?_
    (le_iSup
      (fun ε' : {ε' : ℝ // 0 < ε'} =>
        ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε'.1}, openUnitSquarePowerSaddle u w.1)
      ε)
  refine le_iInf ?_
  intro w
  by_cases hwOpen : InOpenUnitInterval w.1
  · -- On the open strip, the section is a real power and therefore nonnegative.
    have hNonneg : 0 ≤ (u 0) ^ (w.1 0) := Real.rpow_nonneg hu.1.le _
    simpa [openUnitSquarePowerSaddle, hu, hwOpen, oneDimensionalPowerKernel] using hNonneg
  · -- Outside the open strip, the upper simple extension takes the value `⊤`.
    have hValue : openUnitSquarePowerSaddle u w.1 = ⊤ := by
      simp [openUnitSquarePowerSaddle, hwOpen]
    rw [hValue]
    exact le_top

/-- Helper for Text 34.1.1: on the closed-square branch with `u ∈ (0,1)`, the second partial
closure already recovers the original power kernel `u^v`. -/
lemma helperForText_34_1_1_partialClosure2_eq_powerKernel_of_openFirst_closedSecond
    {u v : Fin 1 → ℝ} (hu : InOpenUnitInterval u) (hv : InClosedUnitInterval v) :
    partialClosure₂ openUnitSquarePowerSaddle u v = oneDimensionalPowerKernel u v := by
  have hBaseNe : u 0 ≠ 0 := ne_of_gt hu.1
  have hCont : ContinuousAt (fun x : ℝ => (u 0) ^ x) (v 0) :=
    Real.continuousAt_const_rpow hBaseNe
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm
  · -- To bound the closure from above, approximate `v` by open-interval points inside every
    -- neighborhood and use continuity of `x ↦ u^x`.
    refine (EReal.le_of_forall_lt_iff_le (x := oneDimensionalPowerKernel u v)
      (y := ⨆ ε : {ε : ℝ // 0 < ε},
        ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1}, openUnitSquarePowerSaddle u w.1)).1 ?_
    intro zr hz
    have hzReal : (u 0) ^ (v 0) < zr := by
      simpa [oneDimensionalPowerKernel] using hz
    refine iSup_le ?_
    intro ε
    have hGap : 0 < zr - (u 0) ^ (v 0) := by
      linarith
    rcases (Metric.continuousAt_iff.mp hCont) (zr - (u 0) ^ (v 0)) hGap with ⟨δ, hδPos, hδ⟩
    let η : {r : ℝ // 0 < r} := by
      refine ⟨min δ (ε.1 / 2), ?_⟩
      apply lt_min
      · exact hδPos
      · linarith [ε.2]
    rcases helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval v hv η with
      ⟨w, hwOpen⟩
    have hwInEps : ‖w.1 - v‖ < ε.1 := by
      have hwHalf : ‖w.1 - v‖ < ε.1 / 2 := lt_of_lt_of_le w.2 (min_le_right _ _)
      linarith [ε.2]
    have hwNorm : ‖w.1 - v‖ < δ := lt_of_lt_of_le w.2 (min_le_left _ _)
    rw [helperForText_34_1_1_norm_fin1_eq_abs] at hwNorm
    have hwCoord : dist (w.1 0) (v 0) < δ := by
      simpa [Real.dist_eq] using hwNorm
    have hPowDist : dist ((u 0) ^ (w.1 0)) ((u 0) ^ (v 0)) < zr - (u 0) ^ (v 0) := hδ hwCoord
    have hAbs : |(u 0) ^ (w.1 0) - (u 0) ^ (v 0)| < zr - (u 0) ^ (v 0) := by
      simpa [Real.dist_eq] using hPowDist
    have hPowLt : (u 0) ^ (w.1 0) < zr := by
      have hUpper : (u 0) ^ (w.1 0) - (u 0) ^ (v 0) < zr - (u 0) ^ (v 0) :=
        (abs_lt.mp hAbs).2
      linarith
    have hValue : openUnitSquarePowerSaddle u w.1 = oneDimensionalPowerKernel u w.1 := by
      simp [openUnitSquarePowerSaddle, hu, hwOpen]
    exact le_trans (iInf_le _ ⟨w.1, hwInEps⟩) <| by
      rw [hValue]
      simpa [oneDimensionalPowerKernel] using hPowLt.le
  · -- For the reverse inequality, continuity gives a radius on which all nearby open points stay
    -- above any prescribed lower bound, while the off-open points contribute only `⊤`.
    refine (forall_lt_iff_le).1 ?_
    intro z hz
    cases z using EReal.rec with
    | bot =>
        have hNonneg :
            ((0 : ℝ) : EReal) ≤
              ⨆ ε : {ε : ℝ // 0 < ε},
                ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1}, openUnitSquarePowerSaddle u w.1 :=
          helperForText_34_1_1_partialClosure2_nonneg_of_openFirst hu
        exact lt_of_lt_of_le (by norm_num) hNonneg
    | coe zr =>
        have hzReal : zr < (u 0) ^ (v 0) := by
          simpa [oneDimensionalPowerKernel] using hz
        by_cases hzNonneg : 0 ≤ zr
        · let β : ℝ := (zr + (u 0) ^ (v 0)) / 2
          have hzBeta : zr < β := by
            dsimp [β]
            linarith
          have hGap : 0 < (u 0) ^ (v 0) - β := by
            dsimp [β]
            linarith
          rcases (Metric.continuousAt_iff.mp hCont) ((u 0) ^ (v 0) - β) hGap with
            ⟨δ, hδPos, hδ⟩
          let ε : {ε : ℝ // 0 < ε} := ⟨δ, hδPos⟩
          have hLocal : (β : EReal) ≤
              ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1}, openUnitSquarePowerSaddle u w.1 := by
            refine le_iInf ?_
            intro w
            by_cases hwOpen : InOpenUnitInterval w.1
            · -- Open points stay close enough to `v` that their power values remain above `β`.
              have hwNorm : ‖w.1 - v‖ < δ := w.2
              rw [helperForText_34_1_1_norm_fin1_eq_abs] at hwNorm
              have hwCoord : dist (w.1 0) (v 0) < δ := by
                simpa [Real.dist_eq] using hwNorm
              have hPowDist :
                  dist ((u 0) ^ (w.1 0)) ((u 0) ^ (v 0)) < (u 0) ^ (v 0) - β :=
                hδ hwCoord
              have hAbs : |(u 0) ^ (w.1 0) - (u 0) ^ (v 0)| < (u 0) ^ (v 0) - β := by
                simpa [Real.dist_eq] using hPowDist
              have hPowGt : β < (u 0) ^ (w.1 0) := by
                have hLower :
                    -((u 0) ^ (v 0) - β) < (u 0) ^ (w.1 0) - (u 0) ^ (v 0) :=
                  (abs_lt.mp hAbs).1
                linarith
              have hValue : openUnitSquarePowerSaddle u w.1 = oneDimensionalPowerKernel u w.1 := by
                simp [openUnitSquarePowerSaddle, hu, hwOpen]
              exact le_of_lt <| by
                rw [hValue]
                simpa [oneDimensionalPowerKernel] using hPowGt
            · -- The off-open branch is `⊤`, which trivially dominates the lower barrier `β`.
              have hValue : openUnitSquarePowerSaddle u w.1 = ⊤ := by
                simp [openUnitSquarePowerSaddle, hwOpen]
              rw [hValue]
              exact le_top
          have hClosureLower : (β : EReal) ≤
              ⨆ ε : {ε : ℝ // 0 < ε},
                ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1}, openUnitSquarePowerSaddle u w.1 :=
            le_trans hLocal
              (le_iSup
                (fun ε' : {ε' : ℝ // 0 < ε'} =>
                  ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε'.1}, openUnitSquarePowerSaddle u w.1)
                ε)
          exact lt_of_lt_of_le (by exact_mod_cast hzBeta) hClosureLower
        · have hNeg : (zr : EReal) < ((0 : ℝ) : EReal) := by
            exact_mod_cast lt_of_not_ge hzNonneg
          exact lt_of_lt_of_le hNeg
            (helperForText_34_1_1_partialClosure2_nonneg_of_openFirst hu)
    | top =>
        exfalso
        exact not_lt_of_ge le_top hz

/-- Helper for Text 34.1.1: the second partial closure extends the `v`-variable from `(0, 1)`
to `[0, 1]` while keeping the first variable open. -/
lemma helperForText_34_1_1_partialClosure2_formula :
    partialClosure₂ openUnitSquarePowerSaddle =
      fun u v =>
        if InClosedUnitInterval v then
          if InOpenUnitInterval u then oneDimensionalPowerKernel u v else (⊥ : EReal)
        else
          (⊤ : EReal) := by
  funext u
  funext v
  by_cases hv : InClosedUnitInterval v
  · by_cases hu : InOpenUnitInterval u
    · -- On the closed-square branch with `u ∈ (0,1)`, the second partial closure is exactly
      -- the original power kernel.
      have hValue : partialClosure₂ openUnitSquarePowerSaddle u v = oneDimensionalPowerKernel u v :=
        helperForText_34_1_1_partialClosure2_eq_powerKernel_of_openFirst_closedSecond hu hv
      simp [hv, hu, hValue]
    · -- If `u` is not open, every `v`-ball in `[0,1]` already forces the infimum to `⊥`.
      have hValue : partialClosure₂ openUnitSquarePowerSaddle u v = ⊥ :=
        helperForText_34_1_1_partialClosure2_eq_bot_of_not_inOpenUnitInterval hu hv
      simp [hv, hu, hValue]
  · -- Outside `[0,1]` in the second variable, the second closure stays constantly `⊤`.
    have hValue : partialClosure₂ openUnitSquarePowerSaddle u v = ⊤ :=
      helperForText_34_1_1_partialClosure2_eq_top_of_not_inClosedUnitInterval hv
    simp [hv, hValue]

/-- Helper for Text 34.1.1: when the second variable stays in `(0,1)`, the first partial
closure at `u = 0` is the boundary value `0`. -/
lemma helperForText_34_1_1_partialClosure1_zero_eq_zero_of_openSecond
    {v : Fin 1 → ℝ} (hv : InOpenUnitInterval v) :
    partialClosure₁ openUnitSquarePowerSaddle 0 v = ((0 : ℝ) : EReal) := by
  have hPosExponent : 0 < v 0 := hv.1
  have hNonnegExponent : 0 ≤ v 0 := hPosExponent.le
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm
  · -- For every positive real upper bound, continuity of `u ↦ u^v` at `0` gives a radius on
    -- which the local supremum already stays below that bound.
    refine (EReal.le_of_forall_lt_iff_le (x := ((0 : ℝ) : EReal))
      (y := ⨅ ε : {ε : ℝ // 0 < ε},
        ⨆ w : {w : Fin 1 → ℝ // ‖w - 0‖ < ε.1}, openUnitSquarePowerSaddle w.1 v)).1 ?_
    intro z hz
    have hzReal : 0 < z := by
      exact_mod_cast hz
    have hCont : ContinuousAt (fun x : ℝ => x ^ (v 0)) 0 :=
      Real.continuousAt_rpow_const 0 (v 0) (Or.inr hNonnegExponent)
    rcases (Metric.continuousAt_iff.mp hCont) z hzReal with ⟨δ, hδPos, hδ⟩
    let ε : {ε : ℝ // 0 < ε} := ⟨min δ (1 / 2), by positivity⟩
    calc
      (⨅ ε' : {ε' : ℝ // 0 < ε'},
          ⨆ w : {w : Fin 1 → ℝ // ‖w - 0‖ < ε'.1}, openUnitSquarePowerSaddle w.1 v)
          ≤ ⨆ w : {w : Fin 1 → ℝ // ‖w - 0‖ < ε.1}, openUnitSquarePowerSaddle w.1 v :=
            iInf_le _ ε
      _ ≤ ((z : ℝ) : EReal) := by
        refine iSup_le ?_
        intro w
        by_cases hwOpen : InOpenUnitInterval w.1
        · have hwNorm : ‖w.1 - 0‖ < δ := lt_of_lt_of_le w.2 (min_le_left _ _)
          rw [helperForText_34_1_1_norm_fin1_eq_abs] at hwNorm
          have hwCoord : dist (w.1 0) 0 < δ := by
            simpa [Real.dist_eq, sub_zero] using hwNorm
          have hwPowDist : dist ((w.1 0) ^ (v 0)) (0 ^ (v 0)) < z := hδ hwCoord
          have hwPowLt :
              (w.1 0) ^ (v 0) < z := by
            simpa [Real.dist_eq, Real.zero_rpow (ne_of_gt hPosExponent),
              abs_of_nonneg (Real.rpow_nonneg hwOpen.1.le _)] using hwPowDist
          simpa [openUnitSquarePowerSaddle, hv, hwOpen, oneDimensionalPowerKernel]
            using hwPowLt.le
        · have hValue : openUnitSquarePowerSaddle w.1 v = ⊥ := by
            simp [openUnitSquarePowerSaddle, hv, hwOpen]
          rw [hValue]
          exact bot_le
  · -- Every positive-radius ball around `0` still meets `(0,1)`, and those witnesses contribute
    -- nonnegative real values to the local supremum.
    refine le_iInf ?_
    intro ε
    let t : ℝ := min (ε.1 / 2) (1 / 2)
    have htPos : 0 < t := by
      dsimp [t]
      apply lt_min
      · linarith [ε.2]
      · norm_num
    have htLtOne : t < 1 := by
      dsimp [t]
      have hHalfBound : min (ε.1 / 2) (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) := min_le_right _ _
      linarith
    have htLtEps : t < ε.1 := by
      dsimp [t]
      have hHalfBound : min (ε.1 / 2) (1 / 2 : ℝ) ≤ ε.1 / 2 := min_le_left _ _
      linarith [ε.2]
    let w : {w : Fin 1 → ℝ // ‖w - 0‖ < ε.1} := by
      refine ⟨fun _ : Fin 1 => t, ?_⟩
      rw [helperForText_34_1_1_norm_fin1_eq_abs]
      simpa [sub_zero, abs_of_pos htPos] using htLtEps
    have hwOpen : InOpenUnitInterval w.1 := ⟨htPos, htLtOne⟩
    have hValue : ((0 : ℝ) : EReal) ≤ openUnitSquarePowerSaddle w.1 v := by
      have hrpow : 0 ≤ (w.1 0) ^ (v 0) := Real.rpow_nonneg hwOpen.1.le _
      simpa [openUnitSquarePowerSaddle, hv, hwOpen, oneDimensionalPowerKernel] using hrpow
    exact le_trans hValue
      (le_iSup (fun w : {w : Fin 1 → ℝ // ‖w - 0‖ < ε.1} => openUnitSquarePowerSaddle w.1 v) w)


end SaddleAmbient

end Section34
end Chap07
