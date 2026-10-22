/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open FeasibilityResistingOracleState
open Lean Elab Tactic Meta

variable {n : ℕ}

/-
Lemma 3.2.4 lies in the midpoint-bisection box / Euclidean inradius domain.

Primary mathematical domain:
- recursively generated axis-aligned boxes in `ℝⁿ` and the Euclidean closed balls centered at
  their midpoints.

Sampled owner-style declarations:
- `FeasibilityResistingOracleState.currentBox` and
  `FeasibilityResistingOracleState.currentCenter` in `Algorithm_3_5`, the chapter owner
  declarations for the realized box and its midpoint at a given stage;
- `IsMidpointCoordinateBisectionStep` and
  `generated_box_side_lengths_eq_half_after_n_steps` in `Proposition_3_43`, the canonical
  midpoint-bisection geometry controlling the side lengths of those boxes;
- mathlib `Metric.closedBall`, the ambient Euclidean closed-ball owner;
- mathlib `Nat.cast_div_le` and `Real.rpow_le_rpow_of_exponent_ge'`, the canonical comparison
  between the cyclewise integer-division exponent and the textbook real exponent.

Best owner abstraction:
- source-facing: the current realized box `state.currentBox R hn` and its midpoint
  `state.currentCenter R hn`;
- core/canonical: the box recursion owned by `FeasibilityResistingOracleState` together with the
  side-length control supplied by `Proposition_3_43`;
- bridge/view: the passage from the stronger cyclewise exponent `state.depth / n : ℕ` to the
  textbook real exponent `((state.depth : ℝ) / n)`.

Primitive data:
- the outer scale `R`
- the positive dimension witness `hn : 0 < n`
- the resisting-oracle transcript `state : FeasibilityResistingOracleState n`

Derived API:
- the source-facing inclusion of the textbook Euclidean ball in the current realized box.

Source/core/bridge triage:
- source-facing: the textbook inclusion
  `B₂(state.currentCenter R hn, (R / 2) * (1 / 2)^(state.depth / n)) ⊆ state.currentBox R hn`;
- core/canonical: the midpoint-bisection owner API in `Algorithm_3_5`;
- bridge/view: the radius comparison from the stronger cyclewise radius
  `(R / 2) * (1 / 2)^(state.depth / n : ℕ)` to the textbook radius with real exponent.

The previous version erased the actual box owner and proved only a generic consequence from an
assumed stronger inclusion. This refinement restores the source-facing statement directly on the
chapter's box owner instead of keeping an arbitrary-family wrapper as the main public theorem.
-/

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the cyclic split index is the remainder of the
current depth modulo `n`. -/
lemma nextCoord_eq_depth_mod
    (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.nextCoord hn = ⟨state.depth % n, Nat.mod_lt _ hn⟩ := by
  induction state with
  | initial =>
      -- The initial transcript starts with the first coordinate.
      apply Fin.ext
      simp [FeasibilityResistingOracleState.nextCoord, FeasibilityResistingOracleState.depth]
  | keepLowerHalf state ih =>
      -- One more split advances the cyclic coordinate by one.
      apply Fin.ext
      simp [FeasibilityResistingOracleState.nextCoord, FeasibilityResistingOracleState.depth,
        FeasibilityResistingOracleState.nextCoordinateIndex, ih, Fin.val_add, Nat.add_mod]
  | keepUpperHalf state ih =>
      -- The upper-half branch advances the cyclic coordinate in the same way.
      apply Fin.ext
      simp [FeasibilityResistingOracleState.nextCoord, FeasibilityResistingOracleState.depth,
        FeasibilityResistingOracleState.nextCoordinateIndex, ih, Fin.val_add, Nat.add_mod]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: if the current remainder does not wrap around,
adding one step does not change the quotient `depth / n`. -/
lemma succ_div_eq_div_of_remainder_succ_lt
    {d n : ℕ} (hn : 0 < n) (hrem : d % n + 1 < n) :
    (d + 1) / n = d / n := by
  -- The non-wrap case means the new remainder is still nonzero.
  have hmod_ne : (d + 1) % n ≠ 0 := by
    have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [Nat.add_mod, hone, Nat.mod_eq_of_lt hrem]
    omega
  simpa using Nat.succ_div_of_mod_ne_zero hmod_ne

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: if the current remainder wraps around, adding one
step increases the quotient `depth / n` by one. -/
lemma succ_div_eq_div_add_one_of_remainder_succ_ge
    {d n : ℕ} (hn : 0 < n) (hrem : ¬ d % n + 1 < n) :
    (d + 1) / n = d / n + 1 := by
  -- Wrapping means the new remainder is exactly `0`.
  have hmod_zero : (d + 1) % n = 0 := by
    have hlt : d % n < n := Nat.mod_lt _ hn
    have hEq : d % n + 1 = n := by
      omega
    rw [Nat.add_mod]
    by_cases h1 : n = 1
    · subst h1
      omega
    · have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hone, hEq]
      simp
  simpa using Nat.succ_div_of_mod_eq_zero hmod_zero

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: if the current remainder does not wrap around,
the next remainder is exactly one larger. -/
lemma succ_mod_eq_remainder_succ_of_remainder_succ_lt
    {d n : ℕ} (hn : 0 < n) (hrem : d % n + 1 < n) :
    (d + 1) % n = d % n + 1 := by
  -- This is the remainder update in the non-wrap case.
  have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.add_mod, hone, Nat.mod_eq_of_lt hrem]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: if the current remainder wraps around, the next
remainder is `0`. -/
lemma succ_mod_eq_zero_of_remainder_succ_ge
    {d n : ℕ} (hn : 0 < n) (hrem : ¬ d % n + 1 < n) :
    (d + 1) % n = 0 := by
  -- Wrapping closes one full cycle of `n` coordinate splits.
  have hlt : d % n < n := Nat.mod_lt _ hn
  have hEq : d % n + 1 = n := by
    omega
  rw [Nat.add_mod]
  by_cases h1 : n = 1
  · subst h1
    omega
  · have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hone, hEq]
    simp

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: in one lower-half step, only the selected
coordinate width is halved. -/
lemma keepLowerHalf_width_eq_update
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (FeasibilityResistingOracleState.keepLowerHalf state).currentUpper R hn -
      (FeasibilityResistingOracleState.keepLowerHalf state).currentLower R hn =
        Function.update
          (state.currentUpper R hn - state.currentLower R hn)
          (state.nextCoord hn)
          ((state.currentUpper R hn (state.nextCoord hn) -
            state.currentLower R hn (state.nextCoord hn)) / 2) := by
  -- This is exactly the midpoint-bisection side-length update theorem.
  simpa using midpointCoordinateBisectionStep_sideLengths_eq_update
    (state.keepLowerHalf_isMidpointCoordinateBisectionStep (R := R) (hn := hn))

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: coordinatewise form of the lower-half width
update. -/
lemma keepLowerHalf_width_eq_if
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (i : Fin n) :
    (FeasibilityResistingOracleState.keepLowerHalf state).currentUpper R hn i -
      (FeasibilityResistingOracleState.keepLowerHalf state).currentLower R hn i =
        if i = state.nextCoord hn then
          (state.currentUpper R hn i - state.currentLower R hn i) / 2
        else
          state.currentUpper R hn i - state.currentLower R hn i := by
  -- Evaluate the update at coordinate `i`.
  have hfun := congrFun (keepLowerHalf_width_eq_update R hn state) i
  by_cases hi : i = state.nextCoord hn
  · subst hi
    simpa using hfun
  · simpa [hi] using hfun

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: in one upper-half step, only the selected
coordinate width is halved. -/
lemma keepUpperHalf_width_eq_update
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (FeasibilityResistingOracleState.keepUpperHalf state).currentUpper R hn -
      (FeasibilityResistingOracleState.keepUpperHalf state).currentLower R hn =
        Function.update
          (state.currentUpper R hn - state.currentLower R hn)
          (state.nextCoord hn)
          ((state.currentUpper R hn (state.nextCoord hn) -
            state.currentLower R hn (state.nextCoord hn)) / 2) := by
  -- The upper-half branch has the same side-length update.
  simpa using midpointCoordinateBisectionStep_sideLengths_eq_update
    (state.keepUpperHalf_isMidpointCoordinateBisectionStep (R := R) (hn := hn))

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: coordinatewise form of the upper-half width
update. -/
lemma keepUpperHalf_width_eq_if
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (i : Fin n) :
    (FeasibilityResistingOracleState.keepUpperHalf state).currentUpper R hn i -
      (FeasibilityResistingOracleState.keepUpperHalf state).currentLower R hn i =
        if i = state.nextCoord hn then
          (state.currentUpper R hn i - state.currentLower R hn i) / 2
        else
          state.currentUpper R hn i - state.currentLower R hn i := by
  -- Evaluate the update at coordinate `i`.
  have hfun := congrFun (keepUpperHalf_width_eq_update R hn state) i
  by_cases hi : i = state.nextCoord hn
  · subst hi
    simpa using hfun
  · simpa [hi] using hfun

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: after `depth / n` full coordinate cycles, each
side length is either the cycle radius `R * 2^{-⌊depth / n⌋}` or twice that value, depending on
whether this coordinate has already been visited in the current partial cycle. -/
lemma current_side_length_profile
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (i : Fin n) :
    state.currentUpper R hn i - state.currentLower R hn i =
      if i.1 < state.depth % n then
        R * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ))
      else
        2 * R * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ)) := by
  induction state generalizing i with
  | initial =>
      -- Initially every side length is exactly `2R`.
      have hbase :
          (FeasibilityResistingOracleState.initial : FeasibilityResistingOracleState n).currentUpper
              R hn i -
            (FeasibilityResistingOracleState.initial : FeasibilityResistingOracleState n).currentLower
              R hn i =
            2 * R := by
        change R - (-R) = 2 * R
        ring
      simpa [FeasibilityResistingOracleState.depth] using hbase
  | keepLowerHalf state ih =>
      -- A lower-half step either preserves a width or halves the currently selected width.
      rw [keepLowerHalf_width_eq_if]
      have hnext : (state.nextCoord hn).1 = state.depth % n := by
        simpa using congrArg Fin.val (nextCoord_eq_depth_mod hn state)
      by_cases hrem : state.depth % n + 1 < n
      · have hdiv : (state.depth + 1) / n = state.depth / n :=
            succ_div_eq_div_of_remainder_succ_lt hn hrem
        have hmod : (state.depth + 1) % n = state.depth % n + 1 :=
            succ_mod_eq_remainder_succ_of_remainder_succ_lt hn hrem
        by_cases hi : i = state.nextCoord hn
        · subst hi
          rw [if_pos rfl, ih]
          simp [FeasibilityResistingOracleState.depth, hnext, hdiv, hmod]
          ring_nf
        · rw [if_neg hi, ih]
          have hine : i.1 ≠ state.depth % n := by
            intro hieq
            apply hi
            apply Fin.ext
            simpa [hnext] using hieq
          by_cases hir : i.1 < state.depth % n
          · have hir' : i.1 < (state.depth + 1) % n := by
              rw [hmod]
              omega
            simp [FeasibilityResistingOracleState.depth, hir, hir', hdiv]
          · have hir' : ¬ i.1 < (state.depth + 1) % n := by
              rw [hmod]
              omega
            simp [FeasibilityResistingOracleState.depth, hir, hir', hdiv]
      · have hdiv : (state.depth + 1) / n = state.depth / n + 1 :=
            succ_div_eq_div_add_one_of_remainder_succ_ge hn hrem
        have hmod : (state.depth + 1) % n = 0 :=
            succ_mod_eq_zero_of_remainder_succ_ge hn hrem
        by_cases hi : i = state.nextCoord hn
        · subst hi
          rw [if_pos rfl, ih]
          simp [FeasibilityResistingOracleState.depth, hnext, hdiv, hmod]
          ring_nf
        · rw [if_neg hi, ih]
          have hir : i.1 < state.depth % n := by
            have hlt : i.1 < n := i.2
            have hstate : state.depth % n + 1 = n := by
              have hlt' : state.depth % n < n := Nat.mod_lt _ hn
              omega
            have hine : i.1 ≠ state.depth % n := by
              intro hieq
              apply hi
              apply Fin.ext
              simpa [hnext] using hieq
            omega
          simp [FeasibilityResistingOracleState.depth, hir, hdiv, hmod]
          ring_nf
  | keepUpperHalf state ih =>
      -- The upper-half branch obeys the same cyclic side-length profile.
      rw [keepUpperHalf_width_eq_if]
      have hnext : (state.nextCoord hn).1 = state.depth % n := by
        simpa using congrArg Fin.val (nextCoord_eq_depth_mod hn state)
      by_cases hrem : state.depth % n + 1 < n
      · have hdiv : (state.depth + 1) / n = state.depth / n :=
            succ_div_eq_div_of_remainder_succ_lt hn hrem
        have hmod : (state.depth + 1) % n = state.depth % n + 1 :=
            succ_mod_eq_remainder_succ_of_remainder_succ_lt hn hrem
        by_cases hi : i = state.nextCoord hn
        · subst hi
          rw [if_pos rfl, ih]
          simp [FeasibilityResistingOracleState.depth, hnext, hdiv, hmod]
          ring_nf
        · rw [if_neg hi, ih]
          have hine : i.1 ≠ state.depth % n := by
            intro hieq
            apply hi
            apply Fin.ext
            simpa [hnext] using hieq
          by_cases hir : i.1 < state.depth % n
          · have hir' : i.1 < (state.depth + 1) % n := by
              rw [hmod]
              omega
            simp [FeasibilityResistingOracleState.depth, hir, hir', hdiv]
          · have hir' : ¬ i.1 < (state.depth + 1) % n := by
              rw [hmod]
              omega
            simp [FeasibilityResistingOracleState.depth, hir, hir', hdiv]
      · have hdiv : (state.depth + 1) / n = state.depth / n + 1 :=
            succ_div_eq_div_add_one_of_remainder_succ_ge hn hrem
        have hmod : (state.depth + 1) % n = 0 :=
            succ_mod_eq_zero_of_remainder_succ_ge hn hrem
        by_cases hi : i = state.nextCoord hn
        · subst hi
          rw [if_pos rfl, ih]
          simp [FeasibilityResistingOracleState.depth, hnext, hdiv, hmod]
          ring_nf
        · rw [if_neg hi, ih]
          have hir : i.1 < state.depth % n := by
            have hlt : i.1 < n := i.2
            have hstate : state.depth % n + 1 = n := by
              have hlt' : state.depth % n < n := Nat.mod_lt _ hn
              omega
            have hine : i.1 ≠ state.depth % n := by
              intro hieq
              apply hi
              apply Fin.ext
              simpa [hnext] using hieq
            omega
          simp [FeasibilityResistingOracleState.depth, hir, hdiv, hmod]
          ring_nf

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: every current side length is at least the
cyclewise scale `R * 2^{-⌊depth / n⌋}` when `R` is nonnegative. -/
lemma current_side_length_ge_cycle_scale
    (R : ℝ) (hR : 0 ≤ R) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (i : Fin n) :
    R * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ)) ≤
      state.currentUpper R hn i - state.currentLower R hn i := by
  -- The profile theorem shows the width is either one or two copies of the cyclewise scale.
  have hprofile := current_side_length_profile (R := R) (hn := hn) (state := state) (i := i)
  rw [hprofile]
  by_cases hir : i.1 < state.depth % n
  · simp [hir]
  · simp [hir]
    nlinarith

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: every coordinate of a Euclidean vector is bounded
in absolute value by the ambient Euclidean norm. -/
lemma abs_coordinate_le_norm (v : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    |v j| ≤ ‖v‖ := by
  -- Re-express the chosen coordinate as an inner product against the standard basis vector.
  have hinner : inner ℝ v (EuclideanSpace.single j (1 : ℝ)) = v j := by
    simpa using EuclideanSpace.inner_single_right j (1 : ℝ) v
  calc
    |v j| = |inner ℝ v (EuclideanSpace.single j (1 : ℝ))| := by
      rw [hinner]
    _ ≤ ‖v‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := abs_real_inner_le_norm _ _
    _ = ‖v‖ := by
      simp [EuclideanSpace.single]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: a coordinate box whose every side length is at
least `2ρ` contains the Euclidean closed ball of radius `ρ` centered at its midpoint. -/
lemma closedBall_subset_box_of_halfwidth_le
    {a b : Fin n → ℝ} {ρ : ℝ}
    (hwidth : ∀ i, 2 * ρ ≤ b i - a i) :
    Metric.closedBall ((EuclideanSpace.equiv (Fin n) ℝ).symm (midpoint ℝ a b)) ρ ⊆
      {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a i ≤ x i ∧ x i ≤ b i} := by
  intro x hx i
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  -- Control the `i`-th coordinate displacement by the ambient Euclidean norm.
  have hcoord :
      |x i - ((EuclideanSpace.equiv (Fin n) ℝ).symm (midpoint ℝ a b)) i| ≤ ρ := by
    have hcoord_norm :=
      abs_coordinate_le_norm
        (v := x - (EuclideanSpace.equiv (Fin n) ℝ).symm (midpoint ℝ a b)) i
    simpa using le_trans hcoord_norm hx
  have hmid :
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (midpoint ℝ a b)) i = (a i + b i) / 2 := by
    simp [midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul]
    ring
  have hhalf : ρ ≤ (b i - a i) / 2 := by
    linarith [hwidth i]
  have habs : |x i - (a i + b i) / 2| ≤ (b i - a i) / 2 := by
    rw [hmid] at hcoord
    exact le_trans hcoord hhalf
  have habs' := abs_le.mp habs
  constructor <;> nlinarith

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the textbook real-exponent radius is no larger
than the stronger cyclewise radius with exponent `depth / n : ℕ`. -/
lemma textbook_radius_le_cycle_radius
    (R : ℝ) (hR : 0 ≤ R) (state : FeasibilityResistingOracleState n) :
    (R / 2) * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) ≤
      (R / 2) * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ)) := by
  -- The base `1 / 2` lies in `(0, 1)`, so larger exponents give smaller radii.
  have hdiv : (state.depth / n : ℕ) ≤ (state.depth : ℝ) / n := by
    simpa using (Nat.cast_div_le (m := state.depth) (n := n) :
      ((state.depth / n : ℕ) : ℝ) ≤ (state.depth : ℝ) / n)
  have hrpow :
      Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) ≤
        Real.rpow (1 / 2 : ℝ) (state.depth / n : ℕ) := by
    refine Real.rpow_le_rpow_of_exponent_ge' ?_ ?_ ?_ hdiv
    · norm_num
    · norm_num
    · positivity
  have hR2 : 0 ≤ R / 2 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hrpow hR2
  simpa [Real.rpow_natCast] using hmul

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: unfold the private lower-bound owners from
Algorithm 3.5 so the last stored lower corner reduces definitionally. -/
elab "unfold_oracle_lower_bound_owners" : tactic => do
  let privateRoot := Name.str Name.anonymous "_private"
  let privateRoot := Name.str privateRoot "Nesterov"
  let privateRoot := Name.str privateRoot "Chap03"
  let privateRoot := Name.str privateRoot "Algorithm_3_5"
  let privateRoot := Name.num privateRoot 0
  let stateNs := Name.str privateRoot "FeasibilityResistingOracleState"
  let names : Array Name := #[
    ``FeasibilityResistingOracleState.lower,
    ``FeasibilityResistingOracleState.currentLower,
    Name.str stateNs "realizedBounds",
    Name.str stateNs "currentBounds",
    Name.str (Name.str stateNs "BoxBounds") "lower"
  ]
  let stxNames : Array (TSyntax `ident) := names.map mkIdent
  evalTactic (← `(tactic| unfold $[$stxNames]*))

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: unfold the private upper-bound owners from
Algorithm 3.5 so the last stored upper corner reduces definitionally. -/
elab "unfold_oracle_upper_bound_owners" : tactic => do
  let privateRoot := Name.str Name.anonymous "_private"
  let privateRoot := Name.str privateRoot "Nesterov"
  let privateRoot := Name.str privateRoot "Chap03"
  let privateRoot := Name.str privateRoot "Algorithm_3_5"
  let privateRoot := Name.num privateRoot 0
  let stateNs := Name.str privateRoot "FeasibilityResistingOracleState"
  let names : Array Name := #[
    ``FeasibilityResistingOracleState.upper,
    ``FeasibilityResistingOracleState.currentUpper,
    Name.str stateNs "realizedBounds",
    Name.str stateNs "currentBounds",
    Name.str (Name.str stateNs "BoxBounds") "upper"
  ]
  let stxNames : Array (TSyntax `ident) := names.map mkIdent
  evalTactic (← `(tactic| unfold $[$stxNames]*))

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the last stored realized lower corner is exactly
the owner-level current lower corner. -/
lemma lower_last_eq_currentLower
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.lower R hn (Fin.last state.depth) = state.currentLower R hn := by
  -- Unfold the private recursive owners so the last stored lower corner becomes explicit.
  ext i
  unfold_oracle_lower_bound_owners
  -- Each constructor records the current lower corner in the newest transcript slot.
  cases state <;> simp [Fin.lastCases_last, FeasibilityResistingOracleState.depth]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the last stored realized upper corner is exactly
the owner-level current upper corner. -/
lemma upper_last_eq_currentUpper
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.upper R hn (Fin.last state.depth) = state.currentUpper R hn := by
  -- Unfold the private recursive owners so the last stored upper corner becomes explicit.
  ext i
  unfold_oracle_upper_bound_owners
  -- Each constructor records the current upper corner in the newest transcript slot.
  cases state <;> simp [Fin.lastCases_last, FeasibilityResistingOracleState.depth]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the owner `currentCenter` agrees with the
midpoint of the current lower and upper coordinate bounds. -/
lemma currentCenter_eq_midpoint_currentBounds
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.currentCenter R hn =
      (EuclideanSpace.equiv (Fin n) ℝ).symm
        (midpoint ℝ (state.currentLower R hn) (state.currentUpper R hn)) := by
  -- Rewrite the last stored realized box into the owner-level current coordinate bounds.
  rw [FeasibilityResistingOracleState.currentCenter.eq_1, FeasibilityResistingOracleState.center]
  rw [lower_last_eq_currentLower, upper_last_eq_currentUpper]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the owner `currentBox` agrees with the coordinate
box cut out by `currentLower` and `currentUpper`. -/
lemma currentBox_eq_currentBounds_set
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.currentBox R hn =
      {x : EuclideanSpace ℝ (Fin n) |
        ∀ i : Fin n, state.currentLower R hn i ≤ x i ∧ x i ≤ state.currentUpper R hn i} := by
  -- Rewrite the last stored realized box inequalities into the owner-level current bounds.
  ext x
  simp [FeasibilityResistingOracleState.currentBox.eq_1, FeasibilityResistingOracleState.box,
    lower_last_eq_currentLower, upper_last_eq_currentUpper]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the stronger cyclewise-radius closed ball is
already contained in the current box. -/
lemma cycle_radius_ball_subset_currentBox
    (R : ℝ) (hR : 0 ≤ R) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    Metric.closedBall (state.currentCenter R hn)
        ((R / 2) * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ))) ⊆
      state.currentBox R hn := by
  let ρ := (R / 2) * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ))
  have hwidth :
      ∀ i : Fin n, 2 * ρ ≤ state.currentUpper R hn i - state.currentLower R hn i := by
    intro i
    have hside := current_side_length_ge_cycle_scale (R := R) (hR := hR) (hn := hn)
      (state := state) (i := i)
    calc
      2 * ρ = R * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ)) := by
        dsimp [ρ]
        ring
      _ ≤ state.currentUpper R hn i - state.currentLower R hn i := hside
  -- Convert the generic midpoint-ball inclusion to the chapter's owner API.
  rw [currentCenter_eq_midpoint_currentBounds, currentBox_eq_currentBounds_set]
  exact closedBall_subset_box_of_halfwidth_le hwidth

/-- Lemma 3.2.4 [Chapter3_4.json:81]: every realized midpoint-bisection box in the chapter's
resisting-oracle construction contains the Euclidean closed ball centered at its midpoint with
textbook radius `r_k = (R / 2) * (1 / 2)^(k / n)`, where `k = state.depth`; this is the geometric
containment lemma that immediately yields the subsequent complexity result. -/
-- Proof sketch: write `state.depth = n * l + p` with `p < n`. The midpoint-bisection owner in
-- `Algorithm_3_5`, together with `generated_box_side_lengths_eq_half_after_n_steps`, shows that
-- each side length of `state.currentBox R hn` is at least `R * (1 / 2)^l`, so the stronger
-- cyclewise-radius ball of radius `(R / 2) * (1 / 2)^l` around `state.currentCenter R hn` lies in
-- the box. Since `l = state.depth / n : ℕ` and `l ≤ state.depth / n` in `ℝ`, the base
-- `1 / 2 ∈ (0, 1)` makes the textbook radius no larger than that cyclewise radius, yielding the
-- displayed inclusion by closed-ball monotonicity.
theorem FeasibilityResistingOracleState.closedBall_subset_currentBox
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    Metric.closedBall (state.currentCenter R hn)
        ((R / 2) * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n)) ⊆
      state.currentBox R hn := by
  -- Route correction: the proof follows the source's cyclewise side-length invariant first, and
  -- only then converts that stronger radius to the textbook `Real.rpow` radius.
  by_cases hR : 0 ≤ R
  · have hrad :
        (R / 2) * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) ≤
          (R / 2) * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ)) :=
        textbook_radius_le_cycle_radius (R := R) hR state
    exact Set.Subset.trans
      (Metric.closedBall_subset_closedBall hrad)
      (cycle_radius_ball_subset_currentBox (R := R) hR hn state)
  · have hR2neg : R / 2 < 0 := by
      nlinarith
    have hrpow_pos : 0 < Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hrad_neg :
        (R / 2) * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) < 0 :=
      mul_neg_of_neg_of_pos hR2neg hrpow_pos
    rw [Metric.closedBall_eq_empty.2 hrad_neg]
    simp

end
