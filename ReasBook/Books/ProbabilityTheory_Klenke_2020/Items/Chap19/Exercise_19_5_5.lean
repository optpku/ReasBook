/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Corollary_17_48
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_51
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Corollary_19_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Example_19_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_15
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_29Support
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/-- Helper for Exercise 19.5.5: the 4-cube state space is the Boolean cube `Fin N → Bool`. -/
abbrev HypercubeState (N : ℕ) : Type :=
  Fin N → Bool

/-- Helper for Exercise 19.5.5: flipping coordinate `i` toggles the Boolean value at `i`. -/
def hypercubeFlipAt {N : ℕ} (x : HypercubeState N) (i : Fin N) : HypercubeState N :=
  Function.update x i (!(x i))

/-- Helper for Exercise 19.5.5: flipping the same coordinate twice returns to the original
vertex. -/
private theorem hypercubeFlipAt_involutive {N : ℕ} (x : HypercubeState N) (i : Fin N) :
    hypercubeFlipAt (hypercubeFlipAt x i) i = x := by
  -- Proof comment: compare the two states coordinatewise; the flipped coordinate is toggled twice
  -- and every other coordinate is unchanged.
  ext j
  by_cases hji : j = i
  · subst hji
    simp [hypercubeFlipAt]
  · simp [hypercubeFlipAt, hji]

/-- Helper for Exercise 19.5.5: a single coordinate flip never fixes a vertex. -/
private theorem hypercubeFlipAt_ne_self {N : ℕ} (x : HypercubeState N) (i : Fin N) :
    hypercubeFlipAt x i ≠ x := by
  -- Proof comment: the two states differ at the flipped coordinate `i`.
  intro h
  have hcoord : !(x i) = x i := by
    simpa [hypercubeFlipAt] using congrArg (fun z : HypercubeState N ↦ z i) h
  cases hxi : x i <;> simp [hxi] at hcoord

/-- Helper for Exercise 19.5.5: two vertices of Fig. 19.17 are adjacent when they differ in
exactly one coordinate. -/
private def fig19_17Adj (x y : HypercubeState 4) : Prop :=
  ∃ i : Fin 4, y = hypercubeFlipAt x i

/-- The graph of Fig. 19.17, modeled as the 4-dimensional hypercube. -/
def fig19_17HypercubeGraph : SimpleGraph (HypercubeState 4) where
  Adj := fig19_17Adj
  symm := by
    intro x y hxy
    rcases hxy with ⟨i, rfl⟩
    -- Proof comment: reuse the same coordinate and cancel the double flip.
    exact ⟨i, (hypercubeFlipAt_involutive x i).symm⟩
  loopless := ⟨fun x hxx ↦ by
    rcases hxx with ⟨i, hi⟩
    -- Proof comment: the flipped vertex cannot coincide with the original one.
    exact hypercubeFlipAt_ne_self x i hi.symm⟩

/-- The distinguished starting vertex `a` in Fig. 19.17. -/
def fig19_17A : HypercubeState 4 := fun _ ↦ false

/-- The distinguished target vertex `z` in Fig. 19.17, opposite to `a` in the hypercube. -/
def fig19_17Z : HypercubeState 4 := fun _ ↦ true

/-- Helper for Exercise 19.5.5: the Hamming weight of a 4-cube vertex. -/
private def hypercubeWeight (x : HypercubeState 4) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 ↦ x i).card

/-- Helper for Exercise 19.5.5: flipping a Boolean coordinate exactly when it disagrees with the
target value produces that target value. -/
private theorem flipIfNeeded_eq_target (a b : Bool) :
    (if a = b then a else !a) = b := by
  cases a <;> cases b <;> rfl

/-- Helper for Exercise 19.5.5: the explicit opposite-corner voltage on the 4-cube, indexed by
Hamming layer. -/
private def fig19_17Voltage (x : HypercubeState 4) : ℝ :=
  match hypercubeWeight x with
  | 0 => 0
  | 1 => 3 / 8
  | 2 => 1 / 2
  | 3 => 5 / 8
  | _ => 1

/-- Helper for Exercise 19.5.5: a vertex of the 4-cube is determined by its four Boolean
coordinates. -/
private def hypercubeStateFourEquiv : HypercubeState 4 ≃ Bool × Bool × Bool × Bool where
  toFun x := (x 0, x 1, x 2, x 3)
  invFun t :=
    fun i ↦
      match (i : ℕ) with
      | 0 => t.1
      | 1 => t.2.1
      | 2 => t.2.2.1
      | _ => t.2.2.2
  left_inv x := by
    -- Proof comment: recover the original function by checking the four coordinates one by one.
    ext i
    fin_cases i <;> rfl
  right_inv t := by
    -- Proof comment: the tuple reconstructed from the inverse map is definitionally the same.
    rcases t with ⟨b0, b1, b2, b3⟩
    rfl

/-- Helper for Exercise 19.5.5: summing over all hypercube vertices is the same as summing over
the four Boolean coordinates explicitly. -/
private theorem hypercubeState_sum_eq_fourBoolSum
    {α : Type*} [AddCommMonoid α] (f : HypercubeState 4 → α) :
    (∑ y : HypercubeState 4, f y) =
      ∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool,
        f (fun i ↦
          match (i : ℕ) with
          | 0 => b0
          | 1 => b1
          | 2 => b2
          | _ => b3) := by
  let g : Bool × Bool × Bool × Bool → α :=
    fun t ↦
      f (fun i ↦
        match (i : ℕ) with
        | 0 => t.1
        | 1 => t.2.1
        | 2 => t.2.2.1
        | _ => t.2.2.2)
  have hsumEq :=
      Fintype.sum_equiv hypercubeStateFourEquiv f g <| by
        intro y
        dsimp [g, hypercubeStateFourEquiv]
        congr
        ext i
        fin_cases i <;> rfl
  -- Proof comment: after transporting the index set through the coordinate equivalence, the
  -- product-type sum unfolds into four nested Boolean sums.
  simpa [g, Fintype.sum_prod_type] using hsumEq

/-- Helper for Exercise 19.5.5: a hypercube state can be rewritten by its four coordinates. -/
private theorem hypercubeState_eq_fromCoords (x : HypercubeState 4) :
    x =
      (fun i : Fin 4 ↦
        match (i : ℕ) with
        | 0 => x 0
        | 1 => x 1
        | 2 => x 2
        | _ => x 3) := by
  -- Proof comment: on `Fin 4`, the four coordinate values determine the whole function.
  ext i
  fin_cases i <;> rfl

/-- Helper for Exercise 19.5.5: the Hamming weight of an explicit four-coordinate state is the
sum of its Boolean coordinates. -/
private theorem hypercubeWeight_fromCoords
    (b0 b1 b2 b3 : Bool) :
    hypercubeWeight (fun i : Fin 4 ↦
      match (i : ℕ) with
      | 0 => b0
      | 1 => b1
      | 2 => b2
      | _ => b3) =
        Bool.toNat b0 + Bool.toNat b1 + Bool.toNat b2 + Bool.toNat b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

/-- Helper for Exercise 19.5.5: flipping coordinate `0` of an explicit four-bit state only
changes the first coordinate. -/
private theorem hypercubeFlipAt_zero_fromCoords (b0 b1 b2 b3 : Bool) :
    hypercubeFlipAt
        (fun i : Fin 4 ↦
          match (i : ℕ) with
          | 0 => b0
          | 1 => b1
          | 2 => b2
          | _ => b3) 0 =
      (fun i : Fin 4 ↦
        match (i : ℕ) with
        | 0 => !b0
        | 1 => b1
        | 2 => b2
        | _ => b3) := by
  ext i
  fin_cases i <;> simp [hypercubeFlipAt]

/-- Helper for Exercise 19.5.5: flipping coordinate `1` of an explicit four-bit state only
changes the second coordinate. -/
private theorem hypercubeFlipAt_one_fromCoords (b0 b1 b2 b3 : Bool) :
    hypercubeFlipAt
        (fun i : Fin 4 ↦
          match (i : ℕ) with
          | 0 => b0
          | 1 => b1
          | 2 => b2
          | _ => b3) 1 =
      (fun i : Fin 4 ↦
        match (i : ℕ) with
        | 0 => b0
        | 1 => !b1
        | 2 => b2
        | _ => b3) := by
  ext i
  fin_cases i <;> simp [hypercubeFlipAt]

/-- Helper for Exercise 19.5.5: flipping coordinate `2` of an explicit four-bit state only
changes the third coordinate. -/
private theorem hypercubeFlipAt_two_fromCoords (b0 b1 b2 b3 : Bool) :
    hypercubeFlipAt
        (fun i : Fin 4 ↦
          match (i : ℕ) with
          | 0 => b0
          | 1 => b1
          | 2 => b2
          | _ => b3) 2 =
      (fun i : Fin 4 ↦
        match (i : ℕ) with
        | 0 => b0
        | 1 => b1
        | 2 => !b2
        | _ => b3) := by
  ext i
  fin_cases i <;> simp [hypercubeFlipAt]

/-- Helper for Exercise 19.5.5: flipping coordinate `3` of an explicit four-bit state only
changes the fourth coordinate. -/
private theorem hypercubeFlipAt_three_fromCoords (b0 b1 b2 b3 : Bool) :
    hypercubeFlipAt
        (fun i : Fin 4 ↦
          match (i : ℕ) with
          | 0 => b0
          | 1 => b1
          | 2 => b2
          | _ => b3) 3 =
      (fun i : Fin 4 ↦
        match (i : ℕ) with
        | 0 => b0
        | 1 => b1
        | 2 => b2
        | _ => !b3) := by
  ext i
  fin_cases i <;> simp [hypercubeFlipAt]

/-- Helper for Exercise 19.5.5: the first-hit event that the trajectory enters `insert y A`
exactly at the state `y`, allowing the hit to occur already at time `0`. -/
private def firstHitAtStateEvent {E Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → E) (A : Set E) (y : E) : Set Ω :=
  {ω | hittingAfter X (insert y A) 0 ω < ⊤ ∧
      stoppedValue X (hittingAfter X (insert y A) 0) ω = y}

/-- Helper for Exercise 19.5.5: `F_A P X A x y` is the probability that the first entrance into
`insert y A` occurs at `y`. -/
private def F_A {E Ω : Type*} [MeasurableSpace Ω]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) : ℝ :=
  (P x : Measure Ω).real (firstHitAtStateEvent X A y)

/-- Helper for Exercise 19.5.5: the starting vertex `a` lies in Hamming layer `0`. -/
private theorem hypercubeWeight_fig19_17A :
    hypercubeWeight fig19_17A = 0 := by
  -- Proof comment: every coordinate of `a` is `false`, so the filtered set is empty.
  simp [hypercubeWeight, fig19_17A]

/-- Helper for Exercise 19.5.5: the target vertex `z` lies in Hamming layer `4`. -/
private theorem hypercubeWeight_fig19_17Z :
    hypercubeWeight fig19_17Z = 4 := by
  -- Proof comment: every coordinate of `z` is `true`, so all four coordinates are counted.
  simp [hypercubeWeight, fig19_17Z]

/-- Helper for Exercise 19.5.5: the two distinguished boundary vertices of Fig. 19.17 are
distinct. -/
private theorem fig19_17A_ne_fig19_17Z :
    fig19_17A ≠ fig19_17Z := by
  -- Proof comment: `a` and `z` live in different Hamming layers.
  intro h
  have hweight := congrArg hypercubeWeight h
  simp [hypercubeWeight_fig19_17A, hypercubeWeight_fig19_17Z] at hweight

/-- Helper for Exercise 19.5.5: every one-step neighbor of `a` lies in Hamming layer `1`. -/
private theorem hypercubeWeight_flipAt_fig19_17A (i : Fin 4) :
    hypercubeWeight (hypercubeFlipAt fig19_17A i) = 1 := by
  -- Proof comment: flipping exactly one `false` coordinate of `a` produces exactly one `true`
  -- coordinate.
  fin_cases i <;> decide

/-- Helper for Exercise 19.5.5: the explicit voltage vanishes at `a`. -/
private theorem fig19_17Voltage_at_a :
    fig19_17Voltage fig19_17A = 0 := by
  -- Proof comment: this is the layer-`0` boundary condition of the explicit potential.
  simp [fig19_17Voltage, hypercubeWeight_fig19_17A]

/-- Helper for Exercise 19.5.5: the explicit voltage equals `1` at `z`. -/
private theorem fig19_17Voltage_at_z :
    fig19_17Voltage fig19_17Z = 1 := by
  -- Proof comment: this is the layer-`4` boundary condition of the explicit potential.
  simp [fig19_17Voltage, hypercubeWeight_fig19_17Z]

/-- Helper for Exercise 19.5.5: every one-step neighbor of `a` has explicit voltage `3 / 8`. -/
private theorem fig19_17Voltage_at_neighbor_of_a (i : Fin 4) :
    fig19_17Voltage (hypercubeFlipAt fig19_17A i) = 3 / 8 := by
  -- Proof comment: all four neighbors of `a` lie in the first Hamming layer.
  simp [fig19_17Voltage, hypercubeWeight_flipAt_fig19_17A i]

/-- Helper for Exercise 19.5.5: the explicit voltages on the four neighbors of `a` sum to
`3 / 2`. -/
private theorem fig19_17NeighborVoltageSum_at_a :
    ∑ i : Fin 4, fig19_17Voltage (hypercubeFlipAt fig19_17A i) = 3 / 2 := by
  -- Proof comment: each of the four neighbors contributes the same layer-`1` value `3 / 8`.
  norm_num [fig19_17Voltage_at_neighbor_of_a]

/-- Helper for Exercise 19.5.5: the one-step average of the explicit voltage from `a` is `3 / 8`.
-/
private theorem fig19_17Voltage_average_at_a :
    (1 / 4 : ℝ) * ∑ i : Fin 4, fig19_17Voltage (hypercubeFlipAt fig19_17A i) = 3 / 8 := by
  -- Proof comment: divide the already computed neighbor-voltage sum `3 / 2` by the degree `4`.
  rw [fig19_17NeighborVoltageSum_at_a]
  norm_num

/-- Helper for Exercise 19.5.5: dividing the neighbor-voltage sum at `a` by `4` still gives
`3 / 8`. -/
private theorem fig19_17NeighborVoltageQuotient_at_a :
    (∑ i : Fin 4, fig19_17Voltage (hypercubeFlipAt fig19_17A i)) / 4 = 3 / 8 := by
  -- Proof comment: rewrite division by `4` as multiplication by `1 / 4` and reuse the existing
  -- average computation.
  calc
    (∑ i : Fin 4, fig19_17Voltage (hypercubeFlipAt fig19_17A i)) / 4
        = (1 / 4 : ℝ) * ∑ i : Fin 4, fig19_17Voltage (hypercubeFlipAt fig19_17A i) := by ring
    _ = 3 / 8 := fig19_17Voltage_average_at_a

/-- Helper for Exercise 19.5.5: distinct coordinates give distinct one-step neighbors. -/
private theorem hypercubeFlipAt_injective (x : HypercubeState 4) :
    Function.Injective (fun i : Fin 4 ↦ hypercubeFlipAt x i) := by
  intro i j hij
  by_contra hij_ne
  have hcoord := congrArg (fun z : HypercubeState 4 ↦ z i) hij
  have hij' : i ≠ j := by
    intro h
    exact hij_ne h
  have htoggle : !(x i) = x i := by
    simpa [hypercubeFlipAt, hij'] using hcoord
  cases hxi : x i <;> simp [hxi] at htoggle

/-- Helper for Exercise 19.5.5: an ambient sum supported on the four coordinate flips of `x`
collapses to the explicit four-term flip sum. -/
private theorem fig19_17FlipImage_rowSum_eq_fourFlipSum
    {α : Type*} [AddCommMonoid α] (x : HypercubeState 4) (F : HypercubeState 4 → α) :
    (∑ y : HypercubeState 4, if ∃ i : Fin 4, y = hypercubeFlipAt x i then F y else 0) =
      ∑ i : Fin 4, F (hypercubeFlipAt x i) := by
  classical
  let s : Finset (HypercubeState 4) :=
    Finset.univ.image (fun i : Fin 4 ↦ hypercubeFlipAt x i)
  have hsum :
      (∑ y : HypercubeState 4, if ∃ i : Fin 4, y = hypercubeFlipAt x i then F y else 0) =
        Finset.sum s (fun y ↦ if ∃ i : Fin 4, y = hypercubeFlipAt x i then F y else 0) := by
    -- Proof comment: the summand is supported exactly on the image of the four coordinate flips.
    simpa only [s] using
      (Finset.sum_subset
        (s₁ := s) (s₂ := (Finset.univ : Finset (HypercubeState 4)))
        (by intro y hy; simp)
        (by
          intro y _ hy
          simp [s] at hy
          have hnot : ¬ ∃ i : Fin 4, y = hypercubeFlipAt x i := by
            intro h
            rcases h with ⟨i, hi⟩
            exact (hy i) hi.symm
          simp [hnot])).symm
  have hrestrict :
      Finset.sum s (fun y ↦ if ∃ i : Fin 4, y = hypercubeFlipAt x i then F y else 0) =
        Finset.sum s F := by
    -- Proof comment: every element of the image finset is one of the four flips by definition.
    refine Finset.sum_congr rfl ?_
    intro y hy
    have hy' : ∃ i : Fin 4, y = hypercubeFlipAt x i := by
      rcases (by simpa [s] using hy : ∃ i : Fin 4, hypercubeFlipAt x i = y) with ⟨i, hi⟩
      exact ⟨i, hi.symm⟩
    simp [hy']
  calc
    (∑ y : HypercubeState 4, if ∃ i : Fin 4, y = hypercubeFlipAt x i then F y else 0)
        = Finset.sum s (fun y ↦ if ∃ i : Fin 4, y = hypercubeFlipAt x i then F y else 0) := hsum
    _ = Finset.sum s F := hrestrict
    _ = ∑ i : Fin 4, F (hypercubeFlipAt x i) := by
          dsimp [s]
          rw [Finset.sum_image ((hypercubeFlipAt_injective x).injOn)]

/-- Helper for Exercise 19.5.5: every pair of vertices in the 4-cube lies in the same connected
component. -/
private theorem hypercubeReachable (x y : HypercubeState 4) :
    fig19_17HypercubeGraph.Reachable x y := by
  let x1 : HypercubeState 4 :=
    if x 0 = y 0 then x else hypercubeFlipAt x 0
  let x2 : HypercubeState 4 :=
    if x1 1 = y 1 then x1 else hypercubeFlipAt x1 1
  let x3 : HypercubeState 4 :=
    if x2 2 = y 2 then x2 else hypercubeFlipAt x2 2
  let x4 : HypercubeState 4 :=
    if x3 3 = y 3 then x3 else hypercubeFlipAt x3 3
  have hx1_reach : fig19_17HypercubeGraph.Reachable x x1 := by
    by_cases h0 : x 0 = y 0
    · simpa [x1, h0] using fig19_17HypercubeGraph.Reachable.refl x
    · exact (show fig19_17HypercubeGraph.Adj x x1 by
        exact ⟨0, by simp [x1, h0]⟩).reachable
  have hx2_reach : fig19_17HypercubeGraph.Reachable x1 x2 := by
    by_cases h1 : x1 1 = y 1
    · simpa [x2, h1] using fig19_17HypercubeGraph.Reachable.refl x1
    · exact (show fig19_17HypercubeGraph.Adj x1 x2 by
        exact ⟨1, by simp [x2, h1]⟩).reachable
  have hx3_reach : fig19_17HypercubeGraph.Reachable x2 x3 := by
    by_cases h2 : x2 2 = y 2
    · simpa [x3, h2] using fig19_17HypercubeGraph.Reachable.refl x2
    · exact (show fig19_17HypercubeGraph.Adj x2 x3 by
        exact ⟨2, by simp [x3, h2]⟩).reachable
  have hx4_reach : fig19_17HypercubeGraph.Reachable x3 x4 := by
    by_cases h3 : x3 3 = y 3
    · simpa [x4, h3] using fig19_17HypercubeGraph.Reachable.refl x3
    · exact (show fig19_17HypercubeGraph.Adj x3 x4 by
        exact ⟨3, by simp [x4, h3]⟩).reachable
  have hx1_0 : x1 0 = y 0 := by
    by_cases h0 : x 0 = y 0
    · simp [x1, h0]
    · cases hx0 : x 0 <;> cases hy0 : y 0 <;> simp [x1, h0, hypercubeFlipAt, hx0, hy0] at *
  have hx2_0 : x2 0 = y 0 := by
    by_cases h1 : x1 1 = y 1 <;> simp [x2, h1, hypercubeFlipAt, hx1_0]
  have hx2_1 : x2 1 = y 1 := by
    by_cases h1 : x1 1 = y 1
    · simp [x2, h1]
    · cases hx1' : x1 1 <;> cases hy1 : y 1 <;> simp [x2, h1, hypercubeFlipAt, hx1', hy1] at *
  have hx3_0 : x3 0 = y 0 := by
    by_cases h2 : x2 2 = y 2 <;> simp [x3, h2, hypercubeFlipAt, hx2_0]
  have hx3_1 : x3 1 = y 1 := by
    by_cases h2 : x2 2 = y 2 <;> simp [x3, h2, hypercubeFlipAt, hx2_1]
  have hx3_2 : x3 2 = y 2 := by
    by_cases h2 : x2 2 = y 2
    · simp [x3, h2]
    · cases hx2' : x2 2 <;> cases hy2 : y 2 <;> simp [x3, h2, hypercubeFlipAt, hx2', hy2] at *
  have hx4_eq : x4 = y := by
    ext j
    fin_cases j
    · by_cases h3 : x3 3 = y 3 <;> simp [x4, h3, hypercubeFlipAt, hx3_0]
    · by_cases h3 : x3 3 = y 3 <;> simp [x4, h3, hypercubeFlipAt, hx3_1]
    · by_cases h3 : x3 3 = y 3 <;> simp [x4, h3, hypercubeFlipAt, hx3_2]
    · by_cases h3 : x3 3 = y 3
      · simp [x4, h3]
      · cases hx3' : x3 3 <;> cases hy3 : y 3 <;> simp [x4, h3, hypercubeFlipAt, hx3', hy3] at *
  exact (hx1_reach.trans hx2_reach).trans (hx3_reach.trans <| hx4_eq ▸ hx4_reach)

/-- Helper for Exercise 19.5.5: every edge of the hypercube walk carries positive one-step
singleton mass. -/
private theorem hypercubeKernel_singleton_pos_of_adj
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph] {x y : HypercubeState 4}
    (hxy : fig19_17HypercubeGraph.Adj x y) :
    0 < (discreteMatrixKernel p) x ({y} : Set (HypercubeState 4)) := by
  rcases hxy with ⟨i, rfl⟩
  -- Proof comment: along a graph edge, the simple-random-walk transition formula is the
  -- positive unit conductance divided by the finite total conductance at the source vertex.
  rw [discreteMatrixKernel_apply_singleton]
  rw [(inferInstance :
    IsRandomWalkWithWeights p (simpleGraphWeights fig19_17HypercubeGraph)).transition_eq]
  refine (ENNReal.div_pos_iff).2 ?_
  refine ⟨by simp [simpleGraphWeights, fig19_17HypercubeGraph, fig19_17Adj], ?_⟩
  exact ne_of_lt
    ((inferInstance :
      IsRandomWalkWithWeights p (simpleGraphWeights fig19_17HypercubeGraph)).conductance_lt_top x)

/-- Helper for Exercise 19.5.5: composing a positive one-step singleton mass with a positive
`n`-step singleton mass yields a positive `(n + 1)`-step singleton mass. -/
private theorem hypercubeKernel_singleton_pos_succ
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    {x y z : HypercubeState 4} {n : ℕ}
    (hxy : 0 < (discreteMatrixKernel p) x ({y} : Set (HypercubeState 4)))
    (hyz : 0 < ((discreteMatrixKernel p) ^ n) y ({z} : Set (HypercubeState 4))) :
    0 < ((discreteMatrixKernel p) ^ (n + 1)) x ({z} : Set (HypercubeState 4)) := by
  let κ := discreteMatrixKernel p
  have hmeas : Measurable fun w : HypercubeState 4 ↦
      (κ ^ n) w ({z} : Set (HypercubeState 4)) :=
    Kernel.measurable_coe (κ ^ n) (MeasurableSet.singleton z)
  have hySupport : y ∈ Function.support fun w : HypercubeState 4 ↦
      (κ ^ n) w ({z} : Set (HypercubeState 4)) := by
    simpa [Function.support] using hyz.ne'
  have hsupportPos :
      0 < (κ x)
        (Function.support fun w : HypercubeState 4 ↦ (κ ^ n) w ({z} : Set (HypercubeState 4))) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the support of the tail kernel already contains the intermediate state `y`,
  -- so the composed kernel keeps positive mass on `z`.
  have hcomp :
      0 < (((κ ^ n) ∘ₖ κ) x) ({z} : Set (HypercubeState 4)) := by
    rw [Kernel.comp_apply' _ _ _ (MeasurableSet.singleton z)]
    rw [MeasureTheory.lintegral_pos_iff_support hmeas]
    exact hsupportPos
  simpa [pow_succ] using hcomp

/-- Helper for Exercise 19.5.5: every walk in the 4-cube gives positive singleton transition
mass after its length many steps. -/
private theorem hypercubePositiveSingletonReachabilityOfWalk
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph] {x y : HypercubeState 4}
    (w : fig19_17HypercubeGraph.Walk x y) :
    ∃ n : ℕ, 0 < ((discreteMatrixKernel p) ^ n) x ({y} : Set (HypercubeState 4)) := by
  induction w with
  | @nil x =>
      -- Proof comment: the zero-step kernel is the identity kernel, so it places unit mass on
      -- the starting state.
      refine ⟨0, ?_⟩
      have hself (v : HypercubeState 4) :
          0 < ((1 : Kernel (HypercubeState 4) (HypercubeState 4)) v)
            ({v} : Set (HypercubeState 4)) := by
        change 0 < (Measure.dirac v) ({v} : Set (HypercubeState 4))
        simp
      simpa [pow_zero] using hself x
  | @cons x y z hxy w ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, hypercubeKernel_singleton_pos_succ ?_ hn⟩
      exact hypercubeKernel_singleton_pos_of_adj hxy

/-- Helper for Exercise 19.5.5: every pair of hypercube vertices communicates with positive
singleton mass after finitely many steps. -/
private theorem hypercubePositiveSingletonReachability
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph] (x y : HypercubeState 4) :
    ∃ n : ℕ, 0 < ((discreteMatrixKernel p) ^ n) x ({y} : Set (HypercubeState 4)) := by
  -- Proof comment: choose a graph walk from the connected hypercube and compose the positive
  -- singleton masses along its edges.
  exact (hypercubeReachable x y).elim
    (fun w ↦ hypercubePositiveSingletonReachabilityOfWalk w)

/-- Helper for Exercise 19.5.5: the simple random walk on the connected 4-cube is irreducible
with respect to counting measure. -/
private instance hypercubeKernel_isIrreducible
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph] :
    Kernel.IsIrreducible (Measure.count : Measure (HypercubeState 4)) (discreteMatrixKernel p)
    where
  irreducible := by
    intro A hA hcountA_pos x
    obtain ⟨y, hyA⟩ := MeasureTheory.nonempty_of_measure_ne_zero
      (μ := (Measure.count : Measure (HypercubeState 4))) (ne_of_gt hcountA_pos)
    rcases hypercubePositiveSingletonReachability (p := p) x y with ⟨n, hn⟩
    -- Proof comment: a positive singleton mass at some `y ∈ A` yields positive mass on `A`
    -- itself by monotonicity.
    refine ⟨n, ?_⟩
    exact measure_pos_of_superset (Set.singleton_subset_iff.mpr hyA) hn.ne'

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
variable {P : HypercubeState 4 → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → HypercubeState 4}
variable [hSimple : IsSimpleRandomWalk p fig19_17HypercubeGraph]
variable [hMarkov :
  IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/-- Helper for Exercise 19.5.5: integrating a real observable of `X n` under `P x` matches the
`n`-step kernel row of the realized hypercube walk. -/
private theorem localMarkovRealization_integral_comp_transition_eq
    {g : HypercubeState 4 → ℝ} (x : HypercubeState 4) (n : ℕ) :
    (P x : Measure Ω)[fun ω ↦ g (X n ω)] =
      ∫ z, g z ∂((discreteMatrixKernel p ^ n) x) := by
  let hReal :
      IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X := inferInstance
  have hXn : Measurable (X n) := hReal.measurable_process n
  -- Proof comment: rewrite the time-`n` marginal through the realization field `transition_eq`.
  rw [← hReal.transition_eq x n, integral_map]
  · exact hXn.aemeasurable
  · exact (Measurable.of_discrete : Measurable g).aestronglyMeasurable

/-- Helper for Exercise 19.5.5: the positive-time first return event of a realized chain is a
countable union of measurable singleton fibers. -/
private theorem fig19_17MeasurableSet_firstReturnTimeFinite
    {κ : ℕ → Kernel (HypercubeState 4) (HypercubeState 4)}
    {P : HypercubeState 4 → ProbabilityMeasure Ω} {X : ℕ → Ω → HypercubeState 4}
    [IsMarkovProcessRealization κ P X] (x : HypercubeState 4) :
    MeasurableSet {ω | (τ_[X, x]^1) ω < ⊤} := by
  -- Proof comment: finiteness of the first return time means the path hits `x` at some time
  -- `n + 1`, so the event is a countable union of measurable coordinate fibers.
  have hEq :
      {ω | (τ_[X, x]^1) ω < ⊤} = ⋃ n : ℕ, X n.succ ⁻¹' ({x} : Set (HypercubeState 4)) := by
    ext ω
    constructor
    · intro hω
      rcases (hittingAfter_singleton_lt_top_iff X x ω).1 (by
        simpa [iteratedEntranceTime_one] using hω) with ⟨n, hn, hnx⟩
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m, rfl⟩
      exact Set.mem_iUnion.2 ⟨m, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hnx⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      exact (hittingAfter_singleton_lt_top_iff X x ω).2
        ⟨n.succ, Nat.succ_pos _, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hn⟩
  rw [hEq]
  refine MeasurableSet.iUnion ?_
  intro n
  have hReal : IsMarkovProcessRealization κ P X := inferInstance
  exact (hReal.measurable_process n.succ) (measurableSet_singleton x)

/-- Helper for Exercise 19.5.5: positive recurrence of a state implies recurrence. -/
private theorem recurrent_of_positiveRecurrentState
    {κ : ℕ → Kernel (HypercubeState 4) (HypercubeState 4)}
    {P : HypercubeState 4 → ProbabilityMeasure Ω} {X : ℕ → Ω → HypercubeState 4}
    [IsMarkovProcessRealization κ P X] (x : HypercubeState 4)
    (hx : IsPositiveRecurrentState P X x) :
    IsRecurrentState P X x := by
  -- Proof comment: if the complement of the finite-return event had positive mass, the first
  -- return time would integrate to `∞`, contradicting positive recurrence.
  let A : Set Ω := {ω | (τ_[X, x]^1) ω < ⊤}
  have hFirstReturnFinite :
      ∀ y : HypercubeState 4, MeasurableSet {ω | (τ_[X, y]^1) ω < ⊤} :=
    fun y ↦ fig19_17MeasurableSet_firstReturnTimeFinite (κ := κ) (P := P) (X := X) y
  have hA_meas : MeasurableSet A := by
    simpa [A] using hFirstReturnFinite x
  have hAc_zero : (P x : Measure Ω) Aᶜ = 0 := by
    by_contra hAc_zero
    have hindicator_top :
        ∫⁻ ω,
          Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω ∂(P x : Measure Ω) = ∞ := by
      have hmeas :
          AEMeasurable (Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞))) (P x : Measure Ω) :=
        (measurable_const.indicator hA_meas.compl).aemeasurable
      have hset :
          (P x : Measure Ω)
            {ω | Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω = ∞} ≠ 0 := by
        have hEq :
            {ω | Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω = ∞} = Aᶜ := by
          ext ω
          by_cases hω : ω ∈ Aᶜ
          · have hnotA : ω ∉ A := hω
            simp [Set.indicator, hω, hnotA]
          · have hA : ω ∈ A := by simpa using hω
            simp [Set.indicator, hω, hA]
        simpa [hEq] using hAc_zero
      exact lintegral_eq_top_of_measure_eq_top_ne_zero hmeas hset
    have hdom :
        ∫⁻ ω, Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω ∂(P x : Measure Ω) ≤
          expectedFirstReturnTime P X x := by
      rw [expectedFirstReturnTime]
      refine lintegral_mono fun ω ↦ ?_
      by_cases hω : ω ∈ Aᶜ
      · have hτ : (τ_[X, x]^1) ω = ⊤ := by
          have hτne : ¬ (τ_[X, x]^1) ω ≠ ⊤ := by
            simpa [A, Set.mem_setOf_eq, lt_top_iff_ne_top] using hω
          exact not_not.mp hτne
        simp [Set.indicator, hω, hτ]
      · simp [Set.indicator, hω]
    have htop : expectedFirstReturnTime P X x = ∞ := by
      simpa [hindicator_top] using hdom
    exact (ne_of_lt hx) htop
  have hA_prob : (P x : Measure Ω) A = 1 := by
    have hA_le : (P x : Measure Ω) A ≤ 1 := by
      have hA_le_univ : (P x : Measure Ω) A ≤ (P x : Measure Ω) Set.univ :=
        measure_mono (show A ⊆ Set.univ by intro ω _; simp)
      simpa using hA_le_univ
    have hA_ge : 1 ≤ (P x : Measure Ω) A := by
      have hunion : A ∪ Aᶜ = Set.univ := by
        ext ω
        simp [A]
      have hUnion_le :
          (P x : Measure Ω) (A ∪ Aᶜ) ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ :=
        measure_union_le A Aᶜ
      calc
        1 = (P x : Measure Ω) Set.univ := by simp
        _ ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ := by
              simpa [hunion] using hUnion_le
        _ = (P x : Measure Ω) A := by rw [hAc_zero, add_zero]
    exact le_antisymm hA_le hA_ge
  have hhit :
      (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = 1 := by
    have hEq : {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = A := by
      ext ω
      simpa [A, iteratedEntranceTime_one] using (hittingAfter_singleton_lt_top_iff X x ω).symm
    rw [hEq]
    exact hA_prob
  rw [IsRecurrentState, everHitsProbability_def]
  exact (ENNReal.toReal_eq_one_iff _).2 hhit

/-- Helper for Exercise 19.5.5: every vertex of a weighted random walk has positive total
conductance. -/
private theorem conductance_ne_zero_at
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    {C : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsRandomWalkWithWeights p C] (x : HypercubeState 4) :
    conductance C x ≠ 0 := by
  -- Proof comment: otherwise the whole `x`-row of the transition matrix vanishes, contradicting
  -- stochasticity.
  intro hx0
  have hC_zero : ∀ y : HypercubeState 4, C x y = 0 := by
    intro y
    have hle : C x y ≤ conductance C x := by
      simpa [conductance] using (ENNReal.le_tsum y : C x y ≤ ∑' z : HypercubeState 4, C x z)
    rw [hx0] at hle
    exact le_antisymm hle bot_le
  have hp_zero : ∀ y : HypercubeState 4, p x y = 0 := by
    intro y
    rw [(inferInstance : IsRandomWalkWithWeights p C).transition_eq x y, hC_zero y, hx0]
    simp
  have hsum_zero : ∑ y : HypercubeState 4, p x y = 0 := by
    simp [hp_zero]
  have hstochastic : ∑' y : HypercubeState 4, p x y = 1 := by
    exact (inferInstance : IsRandomWalkWithWeights p C).isStochasticMatrix x
  have hstochastic' : ∑ y : HypercubeState 4, p x y = 1 := by
    simpa using hstochastic
  rw [hsum_zero] at hstochastic'
  simp at hstochastic'

/-- Helper for Exercise 19.5.5: kernel irreducibility of the hypercube walk yields the Chapter 17
irreducibility predicate for its realization. -/
private theorem irreducibleMarkovChain_of_discreteMatrixKernelIsIrreducible
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    {C : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    {P : HypercubeState 4 → ProbabilityMeasure Ω} {X : ℕ → Ω → HypercubeState 4}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure (HypercubeState 4)) (discreteMatrixKernel p)] :
    IsIrreducibleMarkovChain P X := by
  have hgreen :
      ∀ ⦃x y : HypercubeState 4⦄, x ≠ y → 0 < (G[P, X; 1]) x y := by
    intro x y hxy
    have hy_pos : 0 < (Measure.count : Measure (HypercubeState 4)) ({y} : Set (HypercubeState 4)) := by
      simp
    rcases (inferInstance :
        Kernel.IsIrreducible (Measure.count : Measure (HypercubeState 4))
          (discreteMatrixKernel p)).irreducible
        (A := ({y} : Set (HypercubeState 4))) (MeasurableSet.singleton y) hy_pos x with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hnpos
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
      subst hnzero
      have hzero : ((discreteMatrixKernel p ^ 0) x) ({y} : Set (HypercubeState 4)) = 0 := by
        change (Kernel.id x) ({y} : Set (HypercubeState 4)) = 0
        simp [Kernel.id_apply, hxy]
      rw [hzero] at hn
      exact lt_irrefl _ hn
    exact greenFunctionFrom_one_pos_of_posStepMass
      (κ := fun m ↦ discreteMatrixKernel p ^ m) P X hnpos hn
  exact
    (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
      (κ := fun n ↦ discreteMatrixKernel p ^ n) P X).2 hgreen

/-- Helper for Exercise 19.5.5: the finite irreducible hypercube walk is recurrent because its
normalized conductance measure is invariant and Theorem 17.51 upgrades that to positive
recurrence. -/
private theorem recurrentMarkovChain_of_finite_irreducible_randomWalk
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    {C : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    {P : HypercubeState 4 → ProbabilityMeasure Ω} {X : ℕ → Ω → HypercubeState 4}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x0 : HypercubeState 4)
    [Kernel.IsIrreducible (Measure.count : Measure (HypercubeState 4)) (discreteMatrixKernel p)] :
    IsRecurrentMarkovChain P X := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  let hirr : IsIrreducibleMarkovChain P X :=
    irreducibleMarkovChain_of_discreteMatrixKernelIsIrreducible
      (p := p) (C := C) (P := P) (X := X)
  have hmass_ne_zero : conductanceMeasure C Set.univ ≠ 0 := by
    intro hmass_zero
    have hvertex_zero : conductanceMeasure C ({x0} : Set (HypercubeState 4)) = 0 := by
      simpa [hmass_zero] using
        (measure_mono_null (show ({x0} : Set (HypercubeState 4)) ⊆ Set.univ by simp) hmass_zero)
    have hcond_zero : conductance C x0 = 0 := by
      simpa [conductanceMeasure_apply_singleton] using hvertex_zero
    exact conductance_ne_zero_at (p := p) (C := C) x0 hcond_zero
  have hmass_lt_top : conductanceMeasure C Set.univ < ∞ := by
    rw [conductanceMeasure]
    rw [Measure.sum_apply _ MeasurableSet.univ]
    rw [tsum_fintype]
    have hterm :
        ∀ x : HypercubeState 4,
          (conductance C x • Measure.dirac x) Set.univ = conductance C x := by
      intro x
      simp [Measure.smul_apply]
    simp_rw [hterm]
    simp only [ENNReal.sum_lt_top, Finset.mem_univ, forall_true_left]
    intro x
    exact hWalk.conductance_lt_top x
  let πMeasure : Measure (HypercubeState 4) :=
    (conductanceMeasure C Set.univ)⁻¹ • conductanceMeasure C
  have hπ_prob : IsProbabilityMeasure πMeasure := by
    refine isProbabilityMeasure_iff.2 ?_
    rw [Measure.smul_apply]
    exact ENNReal.inv_mul_cancel hmass_ne_zero (ne_of_lt hmass_lt_top)
  let π : ProbabilityMeasure (HypercubeState 4) := ⟨πMeasure, hπ_prob⟩
  have hμ_inv_conductance :
      Kernel.Invariant
        (discreteMatrixKernel (conductanceTransitionMatrix C))
        (conductanceMeasure C) := by
    letI : IsMarkovKernel (discreteMatrixKernel (conductanceTransitionMatrix C)) :=
      discreteMatrixKernel_isMarkovKernel _
        (conductanceTransitionMatrix_isStochastic
          (C := C)
          (fun x ↦ hWalk.conductance_lt_top x)
          (fun x ↦ bot_lt_iff_ne_bot.mpr <| conductance_ne_zero_at (p := p) (C := C) x))
    exact
      (conductanceKernel_isReversible
        (C := C)
        hWalk.symmetric
        (fun x ↦ hWalk.conductance_lt_top x)
        (fun x ↦ bot_lt_iff_ne_bot.mpr <| conductance_ne_zero_at (p := p) (C := C) x)).invariant
  have hp_eq : p = conductanceTransitionMatrix C := by
    funext x y
    exact hWalk.transition_eq x y
  have hμ_inv : Kernel.Invariant (discreteMatrixKernel p) (conductanceMeasure C) := by
    simpa [hp_eq] using hμ_inv_conductance
  have hπ_inv : Kernel.Invariant (discreteMatrixKernel p) (π : Measure (HypercubeState 4)) := by
    have hscaled :
        Kernel.Invariant
          (discreteMatrixKernel p)
          ((conductanceMeasure C Set.univ)⁻¹ • conductanceMeasure C) :=
      kernelInvariant_smul
        (κ := fun _ : ℕ ↦ discreteMatrixKernel p)
        (a := (conductanceMeasure C Set.univ)⁻¹) hμ_inv
    simpa [π, πMeasure] using hscaled
  have hπ_mem : π ∈ invariantDistributions (discreteMatrixKernel p) := by
    exact (mem_invariantDistributions_iff (discreteMatrixKernel p) π).2 hπ_inv
  have hpositive : IsPositiveRecurrentMarkovChain P X := by
    refine
      (isPositiveRecurrentMarkovChain_iff_invariantDistributions_ne_empty
        (p := p) (P := P) (X := X) hirr).2 ?_
    intro hEmpty
    have : π ∈ (∅ : Set (ProbabilityMeasure (HypercubeState 4))) := by
      simpa [hEmpty] using hπ_mem
    simpa using this
  intro x
  exact recurrent_of_positiveRecurrentState
    (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) x (hpositive x)

/-- Helper for Exercise 19.5.5: under `P x`, the realized hypercube walk starts from the
deterministic state `x` with probability `1`. -/
private theorem initialState_prob_eq_one_local
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : HypercubeState 4) :
    (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hTransition :
      ((P x : Measure Ω).map (X 0)) ({x} : Set (HypercubeState 4)) =
        (Measure.dirac x) ({x} : Set (HypercubeState 4)) := by
    exact congrArg (fun μ : Measure (HypercubeState 4) ↦ μ ({x} : Set _)) (hReal.initial_eq x)
  -- Proof comment: evaluate the time-`0` marginal on the singleton `{x}` and rewrite the
  -- resulting preimage event as `{ω | X 0 ω = x}`.
  rw [show {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set (HypercubeState 4)) by
    ext ω
    simp]
  rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
  calc
    ((P x : Measure Ω).map (X 0)) ({x} : Set (HypercubeState 4))
        = (Measure.dirac x) ({x} : Set (HypercubeState 4)) := hTransition
    _ = 1 := by simp

/-- Helper for Exercise 19.5.5: under `P x`, the realized hypercube walk starts from `x` almost
surely. -/
private theorem initialState_ae_eq_start_local
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : HypercubeState 4) :
    ∀ᵐ ω ∂(P x : Measure Ω), X 0 ω = x := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hmeas : MeasurableSet {ω | X 0 ω = x} := by
    convert (hReal.measurable_process 0) (MeasurableSet.singleton x) using 1
  -- Proof comment: the probability-one start event upgrades immediately to an almost-sure
  -- statement.
  exact (mem_ae_iff_prob_eq_one hmeas).2
    (initialState_prob_eq_one_local (p := p) (P := P) (X := X) x)

/-- Helper for Exercise 19.5.5: if the realized trajectory starts outside `A`, then the first hit
searched from time `0` agrees with the first hit searched from time `1`. -/
private theorem hittingAfter_zero_eq_one_of_not_mem_initial_local
    {A : Set (HypercubeState 4)} {ω : Ω} (h0 : X 0 ω ∉ A) :
    hittingAfter X A 0 ω = hittingAfter X A 1 ω := by
  refine le_antisymm (hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)) ?_
  -- Proof comment: the time-`0` search cannot stop immediately because `X 0 ω ∉ A`.
  by_cases htop : hittingAfter X A 0 ω = ⊤
  · have hle :
        hittingAfter X A 0 ω ≤ hittingAfter X A 1 ω :=
      hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)
    simpa [htop] using hle
  · lift hittingAfter X A 0 ω to ℕ using htop with n hn
    have hn_ne_top : hittingAfter X A 0 ω ≠ ⊤ := by
      rw [← hn]
      simp
    have hidx : (hittingAfter X A 0 ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hmem : X n ω ∈ A := by
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 0) (ω := ω) hn_ne_top
    have hn_pos : 1 ≤ n := by
      by_contra hn_pos
      have hn_zero : n = 0 := by omega
      exact h0 (hn_zero ▸ hmem)
    simpa [hn] using
      hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω) hn_pos hmem

/-- Helper for Exercise 19.5.5: off the boundary `{a, z}`, the positive-time hit distribution of
that boundary landing at `z` agrees with the local first-hit owner `F_A`. -/
private theorem fig19_17BoundaryHitDistribution_eq_F_A_of_not_mem_boundary
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {x : HypercubeState 4}
    (hx : x ∉ ({fig19_17A, fig19_17Z} : Set (HypercubeState 4))) :
    ((P x : Measure Ω)
      {ω | hittingAfter X ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) 1 ω < ⊤ ∧
          stoppedValue X
              (hittingAfter X ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) 1) ω =
            fig19_17Z}).toReal =
      F_A P X ({fig19_17A} : Set (HypercubeState 4)) x fig19_17Z := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hEventAE :
      {ω | hittingAfter X ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) 1 ω < ⊤ ∧
          stoppedValue X
              (hittingAfter X ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) 1) ω =
            fig19_17Z} =ᵐ[μ]
        firstHitAtStateEvent X ({fig19_17A} : Set (HypercubeState 4)) fig19_17Z := by
    have hstart : ∀ᵐ ω ∂μ, X 0 ω = x :=
      initialState_ae_eq_start_local (p := p) (P := P) (X := X) x
    filter_upwards [hstart] with ω hω
    have hx0 : X 0 ω ∉ ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) := by
      simpa [hω] using hx
    have hτeq :
        hittingAfter X ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) 0 ω =
          hittingAfter X ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) 1 ω :=
      hittingAfter_zero_eq_one_of_not_mem_initial_local (X := X) (A := ({fig19_17A, fig19_17Z} : Set _))
        hx0
    have hboundary :
        ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) =
          insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4)) := by
      ext ξ
      simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_left_comm, or_comm]
    have hτeq' :
        hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 0 ω =
          hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 1 ω := by
      simpa [hboundary] using hτeq
    have hleft :
        {ω | hittingAfter X ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) 1 ω < ⊤ ∧
            stoppedValue X
                (hittingAfter X ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) 1) ω =
              fig19_17Z} ω ↔
          {ω | hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 1 ω < ⊤ ∧
              stoppedValue X
                  (hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 1) ω =
                fig19_17Z} ω := by
      simpa [hboundary]
    have hright :
        {ω | hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 1 ω < ⊤ ∧
            stoppedValue X
                (hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 1) ω =
              fig19_17Z} ω ↔
          {ω | hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 0 ω < ⊤ ∧
              stoppedValue X
                (hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 0) ω =
                fig19_17Z} ω := by
      have hstopEq :
          stoppedValue X
              (hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 0) ω =
            stoppedValue X
              (hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 1) ω := by
        rw [stoppedValue, hτeq']
        rfl
      constructor
      · intro h
        rcases h with ⟨hfin, hstop⟩
        refine ⟨?_, ?_⟩
        · simpa [hτeq'] using hfin
        · exact hstopEq.trans hstop
      · intro h
        rcases h with ⟨hfin, hstop⟩
        refine ⟨?_, ?_⟩
        · simpa [hτeq'] using hfin
        · exact hstopEq.symm.trans hstop
    -- Proof comment: away from the boundary, the time-`0` and time-`1` formulations of the
    -- boundary-hit event coincide.
    exact propext (hleft.trans hright)
  rw [measure_congr hEventAE]
  simp [F_A, Measure.real_def, μ]

/-- Helper for Exercise 19.5.5: a coordinatewise measurable process is adapted to its natural
filtration. -/
private theorem fig19_17Adapted_processFiltration_of_measurable
    {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → HypercubeState 4}
    (hY_meas : ∀ n, Measurable (Y n)) :
    Adapted (processFiltration Y) Y := by
  intro n
  refine measurable_iff_comap_le.2 ?_
  exact le_inf (measurable_iff_comap_le.1 (hY_meas n)) <| by
    refine le_iSup_of_le n ?_
    refine le_iSup_of_le le_rfl ?_
    exact le_rfl

/-- Helper for Exercise 19.5.5: the event that `hittingAfter Y A 1` is finite is measurable. -/
private theorem fig19_17HittingAfter_one_lt_top_measurableSet
    {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → HypercubeState 4}
    (hY_meas : ∀ n, Measurable (Y n)) (A : Set (HypercubeState 4)) :
    MeasurableSet {ω | hittingAfter Y A 1 ω < ⊤} := by
  have hEq : {ω | hittingAfter Y A 1 ω < ⊤} = ⋃ n : ℕ, Y n.succ ⁻¹' A := by
    ext ω
    constructor
    · intro hω
      have hne_top : hittingAfter Y A 1 ω ≠ ⊤ := lt_top_iff_ne_top.mp hω
      lift hittingAfter Y A 1 ω to ℕ using hne_top with m hm
      have hm_ne_top : hittingAfter Y A 1 ω ≠ ⊤ := by
        rw [← hm]
        simp
      have hm_idx : (hittingAfter Y A 1 ω).untopA = m := by
        rw [← hm, WithTop.untopA_eq_untop (by simp)]
        exact (WithTop.untop_eq_iff (by simp)).2 rfl
      have hm_mem : Y m ω ∈ A := by
        -- Proof comment: a finite first entrance time must land inside the target set.
        simpa [hm_idx] using
          hittingAfter_mem_set_of_ne_top (u := Y) (s := A) (n := 1) (ω := ω) hm_ne_top
      have hm_ne_zero : m ≠ 0 := by
        intro hm_zero
        have hm_pos_top : (1 : ℕ∞) ≤ hittingAfter Y A 1 ω :=
          le_hittingAfter (u := Y) (s := A) (n := 1) ω
        have hm_zero_top : hittingAfter Y A 1 ω = 0 := by
          symm
          simpa [hm_zero] using hm
        have hm_absurd : (1 : ℕ∞) ≤ (0 : ℕ∞) := by
          exact hm_zero_top ▸ hm_pos_top
        have hnot : ¬ ((1 : ℕ∞) ≤ (0 : ℕ∞)) := by simp
        exact hnot hm_absurd
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne_zero
      exact Set.mem_iUnion.2 ⟨n, by simpa [Set.mem_preimage] using hm_mem⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      have hn_mem : Y n.succ ω ∈ A := by
        simpa [Set.mem_preimage] using hn
      have hle :
          hittingAfter Y A 1 ω ≤ n.succ :=
        hittingAfter_le_of_mem (u := Y) (s := A) (n := 1) (ω := ω)
          (Nat.succ_le_succ (Nat.zero_le n)) hn_mem
      exact lt_of_le_of_lt hle (by simp)
  rw [hEq]
  refine MeasurableSet.iUnion fun n ↦ ?_
  exact (hY_meas n.succ) MeasurableSet.of_discrete

/-- Helper for Exercise 19.5.5: on the boundary `{a, z}`, the local first-hit probability `F_A`
already has the prescribed boundary values. -/
private theorem fig19_17F_A_eq_boundaryDatum_on_boundary
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : HypercubeState 4) (hx : x ∈ ({fig19_17A, fig19_17Z} : Set (HypercubeState 4))) :
    F_A P X ({fig19_17A} : Set (HypercubeState 4)) x fig19_17Z =
      if x = fig19_17Z then (1 : ℝ) else 0 := by
  by_cases hZ : x = fig19_17Z
  · subst hZ
    let μ : Measure Ω := (P fig19_17Z : Measure Ω)
    let S : Set Ω := {ω | X 0 ω = fig19_17Z}
    have hStart : μ S = 1 := by
      simpa [μ, S] using initialState_prob_eq_one_local (p := p) (P := P) (X := X) fig19_17Z
    have hSubset : S ⊆ firstHitAtStateEvent X ({fig19_17A} : Set (HypercubeState 4)) fig19_17Z := by
      intro ω hω
      have hτ0 :
          hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 0 ω = 0 := by
        refine le_antisymm ?_ (le_hittingAfter (u := X)
          (s := insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4)))
          (n := 0) ω)
        have hmem : X 0 ω ∈ insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4)) := by
          left
          simpa [S] using hω
        exact hittingAfter_le_of_mem
          (u := X) (s := insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4)))
          (n := 0) (ω := ω) (by simp) hmem
      have hstop :
          stoppedValue X
              (hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 0) ω =
            X 0 ω := by
        simp [stoppedValue, hτ0]
      constructor
      · simpa [firstHitAtStateEvent, Set.mem_insert_iff, Set.mem_singleton_iff, hτ0]
      · simpa [firstHitAtStateEvent, Set.mem_insert_iff, Set.mem_singleton_iff, hτ0] using
          hstop.trans hω
    have hEvent :
        μ (firstHitAtStateEvent X ({fig19_17A} : Set (HypercubeState 4)) fig19_17Z) = 1 := by
      refine le_antisymm ?_ ?_
      · calc
          μ (firstHitAtStateEvent X ({fig19_17A} : Set (HypercubeState 4)) fig19_17Z) ≤ μ Set.univ := by
            exact measure_mono (by intro ω hω; simp)
          _ = 1 := by simp [μ]
      · calc
          1 = μ S := hStart.symm
          _ ≤ μ (firstHitAtStateEvent X ({fig19_17A} : Set (HypercubeState 4)) fig19_17Z) :=
            measure_mono hSubset
    -- Proof comment: starting at `z` forces the first boundary hit to occur at `z` immediately.
    simpa [F_A, μ, Measure.real_def] using congrArg ENNReal.toReal hEvent
  · have hA : x = fig19_17A := by
      rcases (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with hA | hZ'
      · exact hA
      · exact False.elim (hZ hZ')
    subst hA
    have hAZ : fig19_17A ≠ fig19_17Z := fig19_17A_ne_fig19_17Z
    let μ : Measure Ω := (P fig19_17A : Measure Ω)
    let S : Set Ω := {ω | X 0 ω = fig19_17A}
    have hStart : μ S = 1 := by
      simpa [μ, S] using initialState_prob_eq_one_local (p := p) (P := P) (X := X) fig19_17A
    have hSubset :
        firstHitAtStateEvent X ({fig19_17A} : Set (HypercubeState 4)) fig19_17Z ⊆ Sᶜ := by
      intro ω hω hzero
      have hzeroState : X 0 ω = fig19_17A := by
        simpa [S] using hzero
      have hτ0 :
          hittingAfter X (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 0 ω = 0 := by
        refine le_antisymm ?_ (le_hittingAfter (u := X)
          (s := insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4)))
          (n := 0) ω)
        have hmem : X 0 ω ∈ insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4)) := by
          simp [hzeroState]
        exact hittingAfter_le_of_mem
          (u := X) (s := insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4)))
          (n := 0) (ω := ω) (by simp) hmem
      have hZ0 : X 0 ω = fig19_17Z := by
        simpa [firstHitAtStateEvent, Set.mem_insert_iff, Set.mem_singleton_iff, stoppedValue, hτ0]
          using hω.2
      exact hAZ (hzeroState.symm.trans hZ0)
    have hComp : μ (Sᶜ) = 0 := by
      let hReal :
          IsMarkovProcessRealization
            (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
      have hS_meas : MeasurableSet S := by
        rw [show S = X 0 ⁻¹' ({fig19_17A} : Set (HypercubeState 4)) by
          ext ω
          simp [S]]
        exact hReal.measurable_process 0 (MeasurableSet.singleton fig19_17A)
      have hFinite : μ S ≠ ∞ := by
        rw [hStart]
        simp
      rw [measure_compl hS_meas hFinite, hStart]
      simp [μ]
    have hEvent :
        μ (firstHitAtStateEvent X ({fig19_17A} : Set (HypercubeState 4)) fig19_17Z) = 0 := by
      exact measure_mono_null hSubset hComp
    -- Proof comment: starting at `a ≠ z` makes the first boundary hit occur at `a`, not at `z`.
    simpa [F_A, μ, Measure.real_def, hZ] using congrArg ENNReal.toReal hEvent

/-- Helper for Exercise 19.5.5: starting outside `{a, z}`, the hypercube walk hits that boundary
almost surely. -/
private theorem fig19_17BoundaryHit_prob_eq_one_of_not_mem
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {x : HypercubeState 4} (hx : x ∉ ({fig19_17A, fig19_17Z} : Set (HypercubeState 4))) :
    (P x : Measure Ω) {ω | hittingAfter X ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) 1 ω < ⊤} = 1 := by
  let hirr : IsIrreducibleMarkovChain P X :=
    irreducibleMarkovChain_of_discreteMatrixKernelIsIrreducible
      (p := p) (C := simpleGraphWeights fig19_17HypercubeGraph) (P := P) (X := X)
  let hrec : IsRecurrentMarkovChain P X :=
    recurrentMarkovChain_of_finite_irreducible_randomWalk
      (p := p) (C := simpleGraphWeights fig19_17HypercubeGraph) (P := P) (X := X) x
  let Ezero : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ X n ω = fig19_17A}
  let H : Set Ω := {ω | hittingAfter X ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) 1 ω < ⊤}
  have hzeroHit : (F[P, X]) x fig19_17A = 1 := by
    exact
      everHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
        (P := P) (X := X) (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (x := x) (y := fig19_17A) (hrec x) (hirr x fig19_17A)
  have hEzero_le_one : (P x : Measure Ω) Ezero ≤ 1 := by
    calc
      (P x : Measure Ω) Ezero ≤ (P x : Measure Ω) Set.univ := by
        exact measure_mono (by intro ω hω; simp)
      _ = 1 := by simp
  have hEzero : (P x : Measure Ω) Ezero = 1 := by
    exact
      (ENNReal.toReal_eq_one_iff ((P x : Measure Ω) Ezero)).mp <|
        by simpa [Ezero, everHitsProbability_def, Measure.real_def] using hzeroHit
  have hsubset : Ezero ⊆ H := by
    intro ω hω
    rcases hω with ⟨n, hn, hXn⟩
    have hmem : X n ω ∈ ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hXn]
    exact lt_of_le_of_lt
      (hittingAfter_le_of_mem (u := X) (s := ({fig19_17A, fig19_17Z} : Set _)) (n := 1)
        (ω := ω) hn hmem)
      (by simp)
  have hH_le_one : (P x : Measure Ω) H ≤ 1 := by
    calc
      (P x : Measure Ω) H ≤ (P x : Measure Ω) Set.univ := by
        exact measure_mono (by intro ω hω; simp)
      _ = 1 := by simp
  have hH_ge_one : 1 ≤ (P x : Measure Ω) H := by
    calc
      1 = (P x : Measure Ω) Ezero := hEzero.symm
      _ ≤ (P x : Measure Ω) H := measure_mono hsubset
  exact le_antisymm hH_le_one hH_ge_one

/-- Helper for Exercise 19.5.5: the explicit layer voltage on the 4-cube satisfies Kirchhoff's
law off the boundary `{a, z}`. -/
private theorem fig19_17NetFlow_row_eq_flipSum (x : HypercubeState 4) :
    netFlowAt (electricalCurrent (simpleGraphWeights fig19_17HypercubeGraph) fig19_17Voltage) x =
      ∑ i : Fin 4, (fig19_17Voltage x - fig19_17Voltage (hypercubeFlipAt x i)) := by
  have hrow :
      ∀ y : HypercubeState 4,
        electricalCurrent (simpleGraphWeights fig19_17HypercubeGraph) fig19_17Voltage x y =
          if ∃ i : Fin 4, y = hypercubeFlipAt x i then
            fig19_17Voltage x - fig19_17Voltage y
          else 0 := by
    intro y
    by_cases hy : ∃ i : Fin 4, y = hypercubeFlipAt x i
    · rcases hy with ⟨i, rfl⟩
      -- Proof comment: each flipped neighbor carries unit conductance, so the current is exactly
      -- the voltage drop across that edge.
      simp [electricalCurrent_apply, simpleGraphWeights, fig19_17HypercubeGraph, fig19_17Adj]
    · have hnotAdj : ¬ fig19_17HypercubeGraph.Adj x y := by
        simpa [fig19_17HypercubeGraph, fig19_17Adj] using hy
      -- Proof comment: away from the four flipped neighbors, the hypercube conductance row
      -- vanishes, so the corresponding current term is zero.
      simp [electricalCurrent_apply, simpleGraphWeights, fig19_17HypercubeGraph, fig19_17Adj,
        hy, hnotAdj]
  -- Proof comment: rewrite the full row as an indicator-supported sum and then collapse that
  -- support to the four coordinate flips.
  calc
    netFlowAt (electricalCurrent (simpleGraphWeights fig19_17HypercubeGraph) fig19_17Voltage) x
        = ∑ y : HypercubeState 4,
            if ∃ i : Fin 4, y = hypercubeFlipAt x i then
              fig19_17Voltage x - fig19_17Voltage y
            else 0 := by
              rw [netFlowAt]
              refine Finset.sum_congr rfl ?_
              intro y hy
              exact hrow y
    _ = ∑ i : Fin 4, (fig19_17Voltage x - fig19_17Voltage (hypercubeFlipAt x i)) := by
          exact fig19_17FlipImage_rowSum_eq_fourFlipSum
            (x := x) (F := fun y ↦ fig19_17Voltage x - fig19_17Voltage y)

/-- Helper for Exercise 19.5.5: off the boundary `{a, z}`, the four flipped-neighbor voltages
average back to the voltage at the current Hamming layer. -/
private theorem fig19_17NeighborVoltageSum_eq_fourMulVoltage
    (x : HypercubeState 4) (hx : x ∉ ({fig19_17A, fig19_17Z} : Set (HypercubeState 4))) :
    ∑ i : Fin 4, fig19_17Voltage (hypercubeFlipAt x i) = 4 * fig19_17Voltage x := by
  -- Route correction: normalize the arbitrary hypercube state to its four Boolean coordinates and
  -- then close the three interior Hamming-layer cases by the resulting finite case split.
  rw [hypercubeState_eq_fromCoords x] at hx ⊢
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals
    first
      | simp [fig19_17A, fig19_17Z, h0, h1, h2, h3] at hx
        contradiction
      | rw [Fin.sum_univ_four, hypercubeFlipAt_zero_fromCoords, hypercubeFlipAt_one_fromCoords,
          hypercubeFlipAt_two_fromCoords, hypercubeFlipAt_three_fromCoords]
        simp [fig19_17Voltage, hypercubeWeight_fromCoords, h0, h1, h2, h3]
        norm_num

private theorem fig19_17Voltage_isElectricalPotential :
    IsElectricalPotential (simpleGraphWeights fig19_17HypercubeGraph)
      ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) fig19_17Voltage := by
  refine
    { antisymm := ?_
      netFlowAt_eq_zero := ?_ }
  · -- Proof comment: Ohm-law currents are antisymmetric because the hypercube conductance family
    -- is symmetric and reversing the edge flips the voltage drop sign.
    intro x y
    rw [electricalCurrent_apply, electricalCurrent_apply,
      simpleGraphWeights_symmetric fig19_17HypercubeGraph x y]
    ring
  · intro x hx
    have hneighbor :
        ∑ i : Fin 4, fig19_17Voltage (hypercubeFlipAt x i) = 4 * fig19_17Voltage x :=
      fig19_17NeighborVoltageSum_eq_fourMulVoltage x hx
    -- Route correction: use the four-neighbor row formula first, then close harmonicity by the
    -- layer-average identity instead of expanding the full 16-state row.
    rw [fig19_17NetFlow_row_eq_flipSum x]
    calc
      ∑ i : Fin 4, (fig19_17Voltage x - fig19_17Voltage (hypercubeFlipAt x i))
          = ∑ i : Fin 4, fig19_17Voltage x - ∑ i : Fin 4, fig19_17Voltage (hypercubeFlipAt x i) := by
              simp [Finset.sum_sub_distrib]
      _ = 4 * fig19_17Voltage x - ∑ i : Fin 4, fig19_17Voltage (hypercubeFlipAt x i) := by
            simp
      _ = 0 := by
            rw [hneighbor]
            ring

/-- Helper for Exercise 19.5.5: the explicit layer voltage matches the unit boundary datum on
`{a, z}`. -/
private theorem fig19_17Voltage_eqOn_boundary :
    Set.EqOn fig19_17Voltage
      (fun z : HypercubeState 4 ↦ if z = fig19_17Z then (1 : ℝ) else 0)
      ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) := by
  intro z hz
  -- Proof comment: the boundary has exactly the two marked vertices, whose voltage values are
  -- already normalized.
  rcases by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz with rfl | rfl
  · simp [fig19_17Voltage_at_a, fig19_17A_ne_fig19_17Z]
  · simp [fig19_17Voltage_at_z]

/-- Helper for Exercise 19.5.5: the explicit layer voltage agrees with the first-hit probability
of reaching `z` before `a`. -/
private theorem fig19_17BoundaryHitProbability_eq_voltage
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : HypercubeState 4) :
    fig19_17Voltage x = F_A P X ({fig19_17A} : Set (HypercubeState 4)) x fig19_17Z := by
  by_cases hx : x ∈ ({fig19_17A, fig19_17Z} : Set (HypercubeState 4))
  · -- Proof comment: on the boundary, both sides are already the normalized `0/1` datum.
    rw [fig19_17Voltage_eqOn_boundary hx]
    exact
      (fig19_17F_A_eq_boundaryDatum_on_boundary (p := p) (P := P) (X := X) x hx).symm
  · let A : Set (HypercubeState 4) := ({fig19_17A, fig19_17Z} : Set (HypercubeState 4))
    let B : Set Ω :=
      {ω | hittingAfter X A 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X A 1) ω = fig19_17Z}
    let μ : Measure Ω := (P x : Measure Ω)
    have hτ : μ {ω | hittingAfter X A 1 ω < ⊤} = 1 := by
      simpa [A, μ] using
        fig19_17BoundaryHit_prob_eq_one_of_not_mem
          (p := p) (P := P) (X := X) hx
    let hReal :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
    let hX_adapted : Adapted (processFiltration X) X :=
      fig19_17Adapted_processFiltration_of_measurable (Y := X) hReal.measurable_process
    have hτ_stop : IsStoppingTime (processFiltration X) (hittingAfter X A 1) := by
      simpa [A] using
        Adapted.isStoppingTime_hittingAfter
          (u := X) (s := A) (n := 1) hX_adapted MeasurableSet.of_discrete
    have hHitMeas : MeasurableSet {ω | hittingAfter X A 1 ω < ⊤} :=
      fig19_17HittingAfter_one_lt_top_measurableSet hReal.measurable_process A
    have hB_eq :
        B = ⋃ n : ℕ, {ω | hittingAfter X A 1 ω = n.succ} ∩ {ω | X n.succ ω = fig19_17Z} := by
      ext ω
      constructor
      · intro hω
        have hne_top : hittingAfter X A 1 ω ≠ ⊤ := lt_top_iff_ne_top.mp hω.1
        lift hittingAfter X A 1 ω to ℕ using hne_top with m hm
        have hm_ne_zero : m ≠ 0 := by
          intro hm_zero
          have hm_pos_top : (1 : ℕ∞) ≤ hittingAfter X A 1 ω :=
            le_hittingAfter (u := X) (s := A) (n := 1) ω
          have hm_ge_one : 1 ≤ m := by
            have hge_m : (1 : ℕ∞) ≤ (m : ℕ∞) := by
              exact le_of_le_of_eq hm_pos_top hm.symm
            exact_mod_cast hge_m
          exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm_ge_one)) hm_zero
        rcases Nat.exists_eq_succ_of_ne_zero hm_ne_zero with ⟨n, rfl⟩
        have hτ_idx : (hittingAfter X A 1 ω).untopA = n.succ := by
          rw [← hm, WithTop.untopA_eq_untop (by simp)]
          exact (WithTop.untop_eq_iff (by simp)).2 rfl
        have hstop :
            stoppedValue X (hittingAfter X A 1) ω = X n.succ ω := by
          rw [stoppedValue, hτ_idx]
        refine Set.mem_iUnion.2 ⟨n, ?_⟩
        constructor
        · exact hm.symm
        · simpa [hstop] using hω.2
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨n, hωn⟩
        rcases hωn with ⟨hτn, hXn⟩
        have hτ' : hittingAfter X A 1 ω = n.succ := by
          simpa using hτn
        have hlt : hittingAfter X A 1 ω < ⊤ := by
          simpa [hτ'] using (show (n.succ : ℕ∞) < ⊤ by simp)
        have hτ_idx : (hittingAfter X A 1 ω).untopA = n.succ := by
          rw [hτ', WithTop.untopA_eq_untop (by simp)]
          exact (WithTop.untop_eq_iff (by simp)).2 rfl
        have hstop :
            stoppedValue X (hittingAfter X A 1) ω = X n.succ ω := by
          rw [stoppedValue, hτ_idx]
        constructor
        · exact hlt
        · simpa [hstop] using hXn
    have hBMeas : MeasurableSet B := by
      rw [hB_eq]
      refine MeasurableSet.iUnion fun n ↦ ?_
      have hτn_meas :
          MeasurableSet[processFiltration X n.succ] {ω | hittingAfter X A 1 ω = n.succ} :=
        hτ_stop.measurableSet_eq n.succ
      have hXn_meas :
          MeasurableSet[processFiltration X n.succ] {ω | X n.succ ω = fig19_17Z} := by
        simpa [Set.preimage] using hX_adapted n.succ (MeasurableSet.singleton fig19_17Z)
      exact
        (show processFiltration X n.succ ≤ ‹MeasurableSpace Ω› from inf_le_left) _
          (hτn_meas.inter hXn_meas)
    have hHitAE : ∀ᵐ ω ∂μ, hittingAfter X A 1 ω < ⊤ := (mem_ae_iff_prob_eq_one hHitMeas).2 hτ
    have hValueAE :
        (fun ω ↦ fig19_17Voltage (stoppedValue X (hittingAfter X A 1) ω)) =ᵐ[μ]
          Set.indicator B (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [hHitAE] with ω hω
      have hmem :
          stoppedValue X (hittingAfter X A 1) ω ∈ A := by
        simpa [A, Set.mem_insert_iff, Set.mem_singleton_iff] using
          hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 1) (ω := ω) hω.ne
      have hvalue :
          fig19_17Voltage (stoppedValue X (hittingAfter X A 1) ω) =
            if stoppedValue X (hittingAfter X A 1) ω = fig19_17Z then (1 : ℝ) else 0 :=
        fig19_17Voltage_eqOn_boundary hmem
      by_cases hone : stoppedValue X (hittingAfter X A 1) ω = fig19_17Z
      · have honeValue : fig19_17Voltage (stoppedValue X (hittingAfter X A 1) ω) = 1 := by
          simpa [hone] using hvalue
        simpa [B, hω, hone] using honeValue
      · have hnotOneValue : fig19_17Voltage (stoppedValue X (hittingAfter X A 1) ω) = 0 := by
          simpa [hone] using hvalue
        simpa [B, hω, hone] using hnotOneValue
    -- Proof comment: Corollary 19.16 converts the electrical potential to a stopped boundary
    -- value, and the stopped value is the indicator of landing at `z`.
    calc
      fig19_17Voltage x =
          ∫ ω, fig19_17Voltage (stoppedValue X (hittingAfter X A 1) ω) ∂μ := by
            simpa [A, μ] using
              electricalPotential_eq_expectation_at_firstEntrance
                (P := P) (X := X) (p := p) (C := simpleGraphWeights fig19_17HypercubeGraph)
                (A := A) (u := fig19_17Voltage) (x := x)
                fig19_17Voltage_isElectricalPotential hx hτ
      _ = ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            exact integral_congr_ae hValueAE
      _ = (μ B).toReal := by
            simpa [B, μ, Measure.real_def] using
              integral_indicator_one (μ := μ) (s := B) hBMeas
      _ = F_A P X ({fig19_17A} : Set (HypercubeState 4)) x fig19_17Z := by
            simpa [A, B, μ] using
              fig19_17BoundaryHitDistribution_eq_F_A_of_not_mem_boundary
                (p := p) (P := P) (X := X) hx

/-- Helper for Exercise 19.5.5: shifting the escape witness by one step isolates the first step
away from `a`. -/
private theorem fig19_17EscapeBeforeReturnAtA_iff_shiftedWitness (ω : Ω) :
    (∃ n : ℕ, 0 < n ∧ X n ω = fig19_17Z ∧
      ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ fig19_17A) ↔
        ∃ n : ℕ, X (n + 1) ω = fig19_17Z ∧
          ∀ m : ℕ, m ≤ n → X (m + 1) ω ≠ fig19_17A := by
  constructor
  · rintro ⟨n, hn_pos, hnZ, hAvoid⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
    refine ⟨m, by simpa using hnZ, ?_⟩
    intro j hj
    exact hAvoid (j + 1) (Nat.succ_pos _) (Nat.succ_le_succ hj)
  · rintro ⟨n, hnZ, hAvoid⟩
    refine ⟨n + 1, Nat.succ_pos _, by simpa using hnZ, ?_⟩
    intro m hm_pos hm_le
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos)
    exact hAvoid j (Nat.succ_le_succ_iff.mp hm_le)

/-- Helper for Exercise 19.5.5: the first hit of `insert z {a}` from time `k` lands at `z`
exactly when the path reaches `z` at some time `n ≥ k` and avoids `a` on the whole interval
`[k,n]`. -/
private theorem fig19_17BoundaryHitAtZ_fromTime_iff_exists
    {Ω' : Type*} [MeasurableSpace Ω'] (u : ℕ → Ω' → HypercubeState 4)
    (k : ℕ) (ω : Ω') :
    (hittingAfter u
        (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) k ω < ⊤ ∧
        stoppedValue u
            (hittingAfter u
              (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) k) ω =
          fig19_17Z) ↔
      ∃ n : ℕ, k ≤ n ∧ u n ω = fig19_17Z ∧
        ∀ m : ℕ, k ≤ m → m ≤ n → u m ω ≠ fig19_17A := by
  let s : Set (HypercubeState 4) :=
    insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))
  have hAZ : fig19_17A ≠ fig19_17Z := fig19_17A_ne_fig19_17Z
  constructor
  · rintro ⟨hfin, hstop⟩
    have hne_top : hittingAfter u s k ω ≠ ⊤ := ne_of_lt hfin
    lift hittingAfter u s k ω to ℕ using hne_top with n hn
    have hidx : (hittingAfter u s k ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hk : k ≤ n := by
      have hk' := le_hittingAfter (u := u) (s := s) (n := k) ω
      rw [← hn] at hk'
      exact_mod_cast hk'
    have hz : u n ω = fig19_17Z := by
      -- Proof comment: identifying the finite hitting time with `n` turns the stopped-value
      -- condition into the concrete endpoint equality `u n ω = z`.
      change stoppedValue u (hittingAfter u s k) ω = fig19_17Z at hstop
      rw [stoppedValue, hidx] at hstop
      exact hstop
    refine ⟨n, hk, hz, ?_⟩
    intro m hkm hmn hmA
    have hτ_le_m :
        hittingAfter u s k ω ≤ m :=
      hittingAfter_le_of_mem (u := u) (s := s) (n := k) (i := m) (ω := ω) hkm <| by
        simp [s, hmA]
    have hn_le_m : n ≤ m := by
      rw [← hn] at hτ_le_m
      simpa using hτ_le_m
    have hm_eq : m = n := le_antisymm hmn hn_le_m
    have : fig19_17A = fig19_17Z := ((hm_eq ▸ hmA).symm.trans hz)
    exact hAZ this
  · rintro ⟨n, hkn, hnz, havoid⟩
    have hτ_le_n :
        hittingAfter u s k ω ≤ n :=
      hittingAfter_le_of_mem (u := u) (s := s) (n := k) (i := n) (ω := ω) hkn <| by
        simp [s, hnz]
    have hne_top0 : hittingAfter u s k ω ≠ ⊤ := by
      intro htop
      simpa [htop] using hτ_le_n
    lift hittingAfter u s k ω to ℕ using hne_top0 with t ht
    have hidx : (hittingAfter u s k ω).untopA = t := by
      rw [← ht, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hkt : k ≤ t := by
      have hkt' := le_hittingAfter (u := u) (s := s) (n := k) ω
      rw [← ht] at hkt'
      exact_mod_cast hkt'
    have htn : t ≤ n := by
      simpa using hτ_le_n
    have hne_top : hittingAfter u s k ω ≠ ⊤ := by
      intro htop
      simpa [htop] using ht
    have ht_mem : u t ω ∈ s := by
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := u) (s := s) (n := k) (ω := ω) hne_top
    have ht_not_a : u t ω ≠ fig19_17A := havoid t hkt htn
    have htz : u t ω = fig19_17Z := by
      rcases (by simpa [s, Set.mem_insert_iff, Set.mem_singleton_iff] using ht_mem) with htz | hta
      · exact htz
      · exact False.elim (ht_not_a hta)
    have hltop : hittingAfter u s k ω < ⊤ := lt_of_le_of_ne le_top hne_top
    refine ⟨hltop, ?_⟩
    -- Proof comment: the finite first hit belongs to `insert z {a}` and cannot be `a`, so the
    -- stopped value is forced to be `z`.
    change stoppedValue u (hittingAfter u s k) ω = fig19_17Z
    rw [stoppedValue, hidx]
    exact htz

/-- Helper for Exercise 19.5.5: the shifted future path after `k` steps records the trajectory
`n ↦ X (n + k)`. -/
private def fig19_17FuturePath (Y : ℕ → Ω → HypercubeState 4) (k : ℕ) :
    Ω → ℕ → HypercubeState 4 :=
  fun ω n ↦ Y (n + k) ω

/-- Helper for Exercise 19.5.5: the path-space restart event is that the shifted trajectory hits
`z` before ever visiting `a`. -/
private def fig19_17HitZBeforeAPathEvent : Set (ℕ → HypercubeState 4) :=
  {ξ | ∃ n : ℕ, ξ n = fig19_17Z ∧
      ∀ m : ℕ, m ≤ n → ξ m ≠ fig19_17A}

/-- Helper for Exercise 19.5.5: avoiding `a` through the first `n + 1` coordinates is a measurable
path event. -/
private theorem fig19_17AvoidAThroughPathEvent_measurable (n : ℕ) :
    MeasurableSet {ξ : ℕ → HypercubeState 4 | ∀ m : ℕ, m ≤ n → ξ m ≠ fig19_17A} := by
  induction n with
  | zero =>
      -- Proof comment: at time `0`, the event is the singleton-complement condition `ξ 0 ≠ a`.
      have hEq :
          {ξ : ℕ → HypercubeState 4 | ∀ m : ℕ, m ≤ 0 → ξ m ≠ fig19_17A} =
            {ξ : ℕ → HypercubeState 4 | ξ 0 ≠ fig19_17A} := by
        ext ξ
        constructor
        · intro hξ
          exact hξ 0 le_rfl
        · intro hξ m hm
          have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
          simpa [hm0] using hξ
      rw [hEq]
      change MeasurableSet (((fun ξ : ℕ → HypercubeState 4 ↦ ξ 0) ⁻¹' ({fig19_17A} : Set _))ᶜ)
      simpa using ((measurable_pi_apply 0) (measurableSet_singleton fig19_17A)).compl
  | succ n ih =>
      have hEq :
          {ξ : ℕ → HypercubeState 4 | ∀ m : ℕ, m ≤ n.succ → ξ m ≠ fig19_17A} =
            {ξ : ℕ → HypercubeState 4 | ∀ m : ℕ, m ≤ n → ξ m ≠ fig19_17A} ∩
              {ξ : ℕ → HypercubeState 4 | ξ n.succ ≠ fig19_17A} := by
        ext ξ
        constructor
        · intro hξ
          refine ⟨?_, ?_⟩
          · intro m hm
            exact hξ m (Nat.le_trans hm (Nat.le_succ n))
          · exact hξ n.succ le_rfl
        · rintro ⟨hprefix, hlast⟩ m hm
          rcases Nat.le_or_eq_of_le_succ hm with hm' | rfl
          · exact hprefix m hm'
          · exact hlast
      -- Proof comment: split the finite avoidance condition into the previous prefix event and
      -- the last-coordinate inequality.
      rw [hEq]
      change MeasurableSet
        ({ξ : ℕ → HypercubeState 4 | ∀ m : ℕ, m ≤ n → ξ m ≠ fig19_17A} ∩
          (((fun ξ : ℕ → HypercubeState 4 ↦ ξ n.succ) ⁻¹' ({fig19_17A} : Set _))ᶜ))
      exact ih.inter (((measurable_pi_apply n.succ) (measurableSet_singleton fig19_17A)).compl)

/-- Helper for Exercise 19.5.5: the restart path event is measurable because it is a countable
union of finite-coordinate cylinder conditions. -/
private theorem fig19_17HitZBeforeAPathEvent_measurable :
    MeasurableSet fig19_17HitZBeforeAPathEvent := by
  let E : ℕ → Set (ℕ → HypercubeState 4) :=
    fun n ↦ {ξ | ξ n = fig19_17Z ∧ ∀ m : ℕ, m ≤ n → ξ m ≠ fig19_17A}
  have hEq : fig19_17HitZBeforeAPathEvent = ⋃ n : ℕ, E n := by
    ext ξ
    simp [fig19_17HitZBeforeAPathEvent, E]
  rw [hEq]
  refine MeasurableSet.iUnion fun n ↦ ?_
  change MeasurableSet
    (((fun ξ : ℕ → HypercubeState 4 ↦ ξ n) ⁻¹' ({fig19_17Z} : Set _)) ∩
      {ξ : ℕ → HypercubeState 4 | ∀ m : ℕ, m ≤ n → ξ m ≠ fig19_17A})
  refine ((measurable_pi_apply n) (measurableSet_singleton fig19_17Z)).inter ?_
  simpa [E] using fig19_17AvoidAThroughPathEvent_measurable n

/-- Helper for Exercise 19.5.5: under the shifted future path, hitting `z` before `a` is exactly
the positive-time boundary-hit event landing at `z`. -/
private theorem fig19_17FuturePath_mem_hitZBeforeAPathEvent_iff {ω : Ω} :
    fig19_17FuturePath X 1 ω ∈ fig19_17HitZBeforeAPathEvent ↔
      hittingAfter X ({fig19_17A, fig19_17Z} : Set _) 1 ω < ⊤ ∧
        stoppedValue X
            (hittingAfter X ({fig19_17A, fig19_17Z} : Set _) 1) ω =
          fig19_17Z := by
  let s : Set (HypercubeState 4) :=
    insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))
  have hs :
      ({fig19_17A, fig19_17Z} : Set (HypercubeState 4)) = s := by
    ext x
    simp [s, Set.mem_insert_iff, Set.mem_singleton_iff, or_left_comm, or_comm]
  have hshift :
      fig19_17FuturePath X 1 ω ∈ fig19_17HitZBeforeAPathEvent ↔
        ∃ n : ℕ, 1 ≤ n ∧ X n ω = fig19_17Z ∧
          ∀ m : ℕ, 1 ≤ m → m ≤ n → X m ω ≠ fig19_17A := by
    constructor
    · rintro ⟨j, hjz, hjavoid⟩
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · simpa [fig19_17FuturePath] using hjz
      · intro m hm1 hmn
        have hm_pos : 0 < m := lt_of_lt_of_le (by omega) hm1
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos)
        have hrj : r ≤ j := by omega
        simpa [fig19_17FuturePath] using hjavoid r hrj
    · rintro ⟨n, hn1, hnz, havoid⟩
      have hn_pos : 0 < n := lt_of_lt_of_le (by omega) hn1
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
      refine ⟨j, ?_, ?_⟩
      · simpa [fig19_17FuturePath] using hnz
      · intro m hmj
        have hm1 : 1 ≤ m + 1 := by omega
        have hmn : m + 1 ≤ j + 1 := by omega
        simpa [fig19_17FuturePath] using havoid (m + 1) hm1 hmn
  -- Proof comment: rewrite the shifted path event into the explicit positive-time boundary-hit
  -- witness and then invoke the generic first-hit bridge from time `1`.
  calc
    fig19_17FuturePath X 1 ω ∈ fig19_17HitZBeforeAPathEvent
        ↔ ∃ n : ℕ, 1 ≤ n ∧ X n ω = fig19_17Z ∧
            ∀ m : ℕ, 1 ≤ m → m ≤ n → X m ω ≠ fig19_17A := hshift
    _ ↔
        hittingAfter X s 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X s 1) ω = fig19_17Z := by
            simpa [s] using
              (fig19_17BoundaryHitAtZ_fromTime_iff_exists (u := X) (k := 1) (ω := ω)).symm
    _ ↔
        hittingAfter X ({fig19_17A, fig19_17Z} : Set _) 1 ω < ⊤ ∧
          stoppedValue X
              (hittingAfter X ({fig19_17A, fig19_17Z} : Set _) 1) ω =
            fig19_17Z := by
            simpa [hs]

/-- Helper for Exercise 19.5.5: the explicit escape event from `a` is the shifted restart path
event integrated as an indicator. -/
private theorem fig19_17Escape_eq_shiftedPathIndicatorIntegral
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    escapeToSetProbability P X fig19_17A ({fig19_17Z} : Set (HypercubeState 4)) =
      ENNReal.ofReal
        (∫ ω, Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
          (fig19_17FuturePath X 1 ω) ∂(P fig19_17A : Measure Ω)) := by
  have hEvent :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω ∈ ({fig19_17Z} : Set (HypercubeState 4)) ∧
          ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ fig19_17A} =
        (fig19_17FuturePath X 1) ⁻¹' fig19_17HitZBeforeAPathEvent := by
    ext ω
    simpa [fig19_17HitZBeforeAPathEvent, fig19_17FuturePath, Set.mem_singleton_iff] using
      fig19_17EscapeBeforeReturnAtA_iff_shiftedWitness (X := X) ω
  have hfuture_meas : Measurable (fig19_17FuturePath X 1) := by
    let hReal :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
    -- Proof comment: the shifted future path is measurable because the realized coordinates
    -- `X (n + 1)` are measurable for every `n`.
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa [fig19_17FuturePath, add_comm] using hReal.measurable_process (n + 1)
  have hEventMeas :
      MeasurableSet ((fig19_17FuturePath X 1) ⁻¹' fig19_17HitZBeforeAPathEvent) := by
    exact fig19_17HitZBeforeAPathEvent_measurable.preimage hfuture_meas
  have hIndicatorEq :
      (fun ω ↦
        Set.indicator ((fig19_17FuturePath X 1) ⁻¹' fig19_17HitZBeforeAPathEvent)
          (fun _ ↦ (1 : ℝ)) ω) =
        fun ω ↦
          Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
            (fig19_17FuturePath X 1 ω) := by
    funext ω
    by_cases hω : fig19_17FuturePath X 1 ω ∈ fig19_17HitZBeforeAPathEvent <;>
      simp [Set.indicator, hω]
  calc
    escapeToSetProbability P X fig19_17A ({fig19_17Z} : Set (HypercubeState 4))
        = (P fig19_17A : Measure Ω)
            ((fig19_17FuturePath X 1) ⁻¹' fig19_17HitZBeforeAPathEvent) := by
              rw [escapeToSetProbability_def, hEvent]
    _ = ENNReal.ofReal
          (((P fig19_17A : Measure Ω).real
            ((fig19_17FuturePath X 1) ⁻¹' fig19_17HitZBeforeAPathEvent))) := by
          simp [Measure.real_def]
    _ = ENNReal.ofReal
          (∫ ω,
            Set.indicator ((fig19_17FuturePath X 1) ⁻¹' fig19_17HitZBeforeAPathEvent)
              (fun _ ↦ (1 : ℝ)) ω ∂(P fig19_17A : Measure Ω)) := by
              congr 1
              symm
              exact
                MeasureTheory.integral_indicator_one
                  (μ := (P fig19_17A : Measure Ω))
                  (s := (fig19_17FuturePath X 1) ⁻¹' fig19_17HitZBeforeAPathEvent)
                  hEventMeas
    _ = ENNReal.ofReal
          (∫ ω, Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
            (fig19_17FuturePath X 1 ω) ∂(P fig19_17A : Measure Ω)) := by
              rw [hIndicatorEq]

/-- Helper for Exercise 19.5.5: the path-law kernel attached to the realization `(P, X)`. -/
private def fig19_17RealizationPathKernel :
    Kernel (HypercubeState 4) (ℕ → HypercubeState 4) :=
  Kernel.ofFunOfCountable fun y ↦
    (P y : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω)

/-- Helper for Exercise 19.5.5: each row of the hypercube path-law kernel is the corresponding
pushforward of `P y`. -/
@[simp] private theorem fig19_17RealizationPathKernel_apply
    (y : HypercubeState 4) :
    fig19_17RealizationPathKernel (P := P) (X := X) y =
      (P y : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) := rfl

/-- Helper for Exercise 19.5.5: the time-`n` marginal of the path-law kernel is the `n`-step
transition row. -/
private theorem fig19_17RealizationPathKernel_transition
    (x : HypercubeState 4) (n : ℕ) :
    transitionKernel (fig19_17RealizationPathKernel (P := P) (X := X)) n x =
      (discreteMatrixKernel p ^ n) x := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  -- Proof comment: unfold the explicit path-law kernel and read the time-`n` marginal from the
  -- realization field `transition_eq`.
  rw [transitionKernel_apply]
  change
    Measure.map (fun ξ : ℕ → HypercubeState 4 ↦ ξ n)
      ((P x : Measure Ω).map (fun ω : Ω ↦ fun m : ℕ ↦ X m ω)) =
        (discreteMatrixKernel p ^ n) x
  rw [Measure.map_map]
  · simpa using hReal.transition_eq x n
  · exact measurable_pi_apply n
  · exact measurable_pi_lambda _ fun m ↦ hReal.measurable_process m

/-- Helper for Exercise 19.5.5: the hypercube path-law kernel makes the realization into a
time-homogeneous Markov process on path space. -/
private theorem fig19_17RealizationPathKernel_isTimeHomogeneousMarkovProcess
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    IsTimeHomogeneousMarkovProcess X P
      (fig19_17RealizationPathKernel (P := P) (X := X)) := by
  let hReal :
      IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X := inferInstance
  refine
    { measurable_process := hReal.measurable_process
      initial_state := initialState_prob_eq_one_local (p := p) (P := P) (X := X)
      path_law := ?_
      markov_property := ?_ }
  · intro x
    rfl
  · intro x A hA s t
    -- Proof comment: the path-kernel transition is exactly the stored transition row of the
    -- original realization, so the Markov property transfers unchanged.
    refine (hReal.markov_property x hA s t).trans ?_
    filter_upwards with ω
    rw [fig19_17RealizationPathKernel_transition
      (p := p) (P := P) (X := X) (x := X s ω) (n := t)]

/-- Helper for Exercise 19.5.5: the restart path-event indicator is measurable. -/
private theorem fig19_17HitZBeforeAPathIndicator_measurable :
    Measurable
      (Set.indicator fig19_17HitZBeforeAPathEvent
        (fun _ : ℕ → HypercubeState 4 ↦ (1 : ℝ))) := by
  -- Proof comment: the indicator is measurable because the underlying path event is measurable.
  exact
    Measurable.indicator measurable_const fig19_17HitZBeforeAPathEvent_measurable

/-- Helper for Exercise 19.5.5: under the path-law kernel started from `y`, the restart path
event has mass `F_A({a}, y, z)`. -/
private theorem fig19_17HitZBeforeAPathIntegral_eq_F_A
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (y : HypercubeState 4) :
    ∫ ξ, Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
      ∂fig19_17RealizationPathKernel (P := P) (X := X) y =
        F_A P X ({fig19_17A} : Set (HypercubeState 4)) y fig19_17Z := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let path : Ω → ℕ → HypercubeState 4 := fun ω n ↦ X n ω
  have hpath_meas : Measurable path := by
    -- Proof comment: the realized full-path map is measurable because every coordinate of `X`
    -- is measurable.
    refine measurable_pi_lambda _ fun n ↦ ?_
    exact hReal.measurable_process n
  have hpreimage :
      path ⁻¹' fig19_17HitZBeforeAPathEvent =
        firstHitAtStateEvent X ({fig19_17A} : Set (HypercubeState 4)) fig19_17Z := by
    ext ω
    have hiff0 :
        fig19_17HitZBeforeAPathEvent (path ω) ↔
          ∃ n : ℕ, 0 ≤ n ∧ X n ω = fig19_17Z ∧
            ∀ m : ℕ, 0 ≤ m → m ≤ n → X m ω ≠ fig19_17A := by
      constructor
      · rintro ⟨n, hnz, havoid⟩
        exact ⟨n, Nat.zero_le n, hnz, fun m _ hm ↦ havoid m hm⟩
      · rintro ⟨n, _, hnz, havoid⟩
        exact ⟨n, hnz, fun m hm ↦ havoid m (Nat.zero_le m) hm⟩
    -- Proof comment: the full-path event is exactly the time-`0` first-hit event that defines
    -- `F_A`, after rewriting the boundary as `insert z {a}`.
    calc
      fig19_17HitZBeforeAPathEvent (path ω)
          ↔ ∃ n : ℕ, 0 ≤ n ∧ X n ω = fig19_17Z ∧
              ∀ m : ℕ, 0 ≤ m → m ≤ n → X m ω ≠ fig19_17A := hiff0
      _ ↔
          hittingAfter X
              (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 0 ω < ⊤ ∧
            stoppedValue X
                (hittingAfter X
                  (insert fig19_17Z ({fig19_17A} : Set (HypercubeState 4))) 0) ω =
              fig19_17Z := by
                simpa using
                  (fig19_17BoundaryHitAtZ_fromTime_iff_exists (u := X) (k := 0) (ω := ω)).symm
      _ ↔ firstHitAtStateEvent X ({fig19_17A} : Set (HypercubeState 4)) fig19_17Z ω := by
            rw [firstHitAtStateEvent]
            exact Iff.rfl
  calc
    ∫ ξ, Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
        ∂fig19_17RealizationPathKernel (P := P) (X := X) y
        = (fig19_17RealizationPathKernel (P := P) (X := X) y).real
            fig19_17HitZBeforeAPathEvent := by
              exact
                MeasureTheory.integral_indicator_one
                  (μ := fig19_17RealizationPathKernel (P := P) (X := X) y)
                  (s := fig19_17HitZBeforeAPathEvent)
                  fig19_17HitZBeforeAPathEvent_measurable
    _ = (((P y : Measure Ω).map path).real fig19_17HitZBeforeAPathEvent) := by
          rfl
    _ = (P y : Measure Ω).real (path ⁻¹' fig19_17HitZBeforeAPathEvent) := by
          simpa using
            (MeasureTheory.map_measureReal_apply
              (μ := (P y : Measure Ω)) (f := path) hpath_meas
              fig19_17HitZBeforeAPathEvent_measurable)
    _ = F_A P X ({fig19_17A} : Set (HypercubeState 4)) y fig19_17Z := by
          simpa [F_A, hpreimage]

/-- Helper for Exercise 19.5.5: the time-`1` conditional expectation of the shifted path-event
indicator is the realized path-kernel mass started from the present state. -/
private theorem fig19_17FuturePathIndicator_condExp_timeOne
    {p : HypercubeState 4 → HypercubeState 4 → ℝ≥0∞}
    [IsSimpleRandomWalk p fig19_17HypercubeGraph]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    ((P fig19_17A : Measure Ω)[fun ω ↦
        Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
          (fig19_17FuturePath X 1 ω)
      | generatedFiltrationSpace X 1]) =ᵐ[(P fig19_17A : Measure Ω)]
        fun ω ↦
          ∫ ξ, Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
            ∂fig19_17RealizationPathKernel (P := P) (X := X) (X 1 ω) := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let g : (ℕ → HypercubeState 4) → ℝ :=
    Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
  have hg_meas : Measurable g := by
    -- Proof comment: the shifted path test function is the measurable indicator of the restart
    -- path event.
    exact fig19_17HitZBeforeAPathIndicator_measurable
  have hg_bdd : Bornology.IsBounded (Set.range g) := by
    -- Proof comment: the indicator takes only the values `0` and `1`, so its range is bounded.
    simpa [g] using isBounded_range_indicator_one fig19_17HitZBeforeAPathEvent
  letI : IsTimeHomogeneousMarkovProcess X P
      (fig19_17RealizationPathKernel (P := P) (X := X)) :=
    fig19_17RealizationPathKernel_isTimeHomogeneousMarkovProcess
      (p := p) (P := P) (X := X)
  have hAE :=
    futurePathCondExp_of_markovProcessNat
      (X := X) (P := P) (κ := fig19_17RealizationPathKernel (P := P) (X := X))
      (hX_meas := hReal.measurable_process)
      (hX0 := fun x ↦ by
        simpa using initialState_prob_eq_one_local (p := p) (P := P) (X := X) x)
      (hpath := fig19_17RealizationPathKernel_apply (P := P) (X := X))
      fig19_17A 1 g hg_meas hg_bdd
  -- Proof comment: specialize the Chapter 17 future-path conditional-expectation formula to the
  -- restart-event indicator and collapse the kernel integral to the corresponding row mass.
  filter_upwards [hAE] with ω hω
  simpa [g, fig19_17FuturePath, shiftedPath, add_comm, MeasureTheory.integral_indicator_one,
    fig19_17HitZBeforeAPathEvent_measurable] using hω

/-- Helper for Exercise 19.5.5: escaping from `a` to `z` before the first positive return to `a`
is the one-step kernel average of the first-hit surface `F_A`. -/
private theorem fig19_17Escape_eq_transitionIntegral_ofFAAtA :
    escapeToSetProbability P X fig19_17A ({fig19_17Z} : Set (HypercubeState 4)) =
      ENNReal.ofReal
        (∫ y, F_A P X ({fig19_17A} : Set (HypercubeState 4)) y fig19_17Z
          ∂discreteMatrixKernel p fig19_17A) := by
  let μ : Measure Ω := (P fig19_17A : Measure Ω)
  let futureIndicator : Ω → ℝ := fun ω ↦
    Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
      (fig19_17FuturePath X 1 ω)
  let rowMass : HypercubeState 4 → ℝ := fun y ↦
    (fig19_17RealizationPathKernel (P := P) (X := X) y).real
      fig19_17HitZBeforeAPathEvent
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hfuturePath_meas : Measurable (fig19_17FuturePath X 1) := by
    -- Proof comment: the shifted path is measurable because every coordinate `X (n + 1)` is.
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa [fig19_17FuturePath, add_comm] using hReal.measurable_process (n + 1)
  have hfuture_meas : Measurable futureIndicator := by
    -- Proof comment: compose the measurable path-event indicator with the measurable shifted path.
    exact fig19_17HitZBeforeAPathIndicator_measurable.comp hfuturePath_meas
  have hfuture_int : Integrable futureIndicator μ := by
    -- Proof comment: the indicator is bounded by `1`, so it is integrable under the start law.
    refine Integrable.of_bound hfuture_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : fig19_17FuturePath X 1 ω ∈ fig19_17HitZBeforeAPathEvent
      · simp [futureIndicator, hω]
      · simp [futureIndicator, hω]
  have hgenerated_le : generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun j hj ↦ ?_
    exact (hReal.measurable_process j).comap_le
  let condFuture : Ω → ℝ :=
    MeasureTheory.condExp (m := generatedFiltrationSpace X 1) μ futureIndicator
  have hfutureIntegral :
      ∫ ω, futureIndicator ω ∂μ = ∫ ω, rowMass (X 1 ω) ∂μ := by
    calc
      ∫ ω, futureIndicator ω ∂μ
          = ∫ ω, condFuture ω ∂μ := by
              symm
              exact integral_condExp hgenerated_le
      _ = ∫ ω,
            (∫ ξ, Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
              ∂fig19_17RealizationPathKernel (P := P) (X := X) (X 1 ω)) ∂μ := by
            -- Proof comment: invoke the time-`1` conditional-expectation bridge on the shifted
            -- path indicator.
            exact integral_congr_ae <| by
              simpa [condFuture, μ, futureIndicator] using
                fig19_17FuturePathIndicator_condExp_timeOne (p := p) (P := P) (X := X)
      _ = ∫ ω, rowMass (X 1 ω) ∂μ := by
            -- Proof comment: each kernel integral is exactly the real row mass of the restart
            -- path event.
            refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
            simp [rowMass, MeasureTheory.integral_indicator_one,
              fig19_17HitZBeforeAPathEvent_measurable]
  have htransitionIntegral :
      ∫ ω, rowMass (X 1 ω) ∂μ =
        ∫ y, rowMass y ∂discreteMatrixKernel p fig19_17A := by
    -- Proof comment: push the present-state observable through the one-step marginal law at `a`.
    have hmap :
        ∫ y, rowMass y ∂((P fig19_17A : Measure Ω).map (X 1)) =
          ∫ ω, rowMass (X 1 ω) ∂μ := by
            simpa [μ] using
              (MeasureTheory.integral_map
                (hReal.measurable_process 1).aemeasurable
                Measurable.of_discrete.aestronglyMeasurable)
    calc
      ∫ ω, rowMass (X 1 ω) ∂μ
          = ∫ y, rowMass y ∂((P fig19_17A : Measure Ω).map (X 1)) := by
              exact hmap.symm
      _ = ∫ y, rowMass y ∂((discreteMatrixKernel p ^ 1) fig19_17A) := by
            rw [hReal.transition_eq fig19_17A 1]
      _ = ∫ y, rowMass y ∂discreteMatrixKernel p fig19_17A := by
            simp
  calc
    escapeToSetProbability P X fig19_17A ({fig19_17Z} : Set (HypercubeState 4))
        = ENNReal.ofReal (∫ ω, futureIndicator ω ∂μ) := by
            simpa [μ, futureIndicator] using
              fig19_17Escape_eq_shiftedPathIndicatorIntegral
                (p := p) (P := P) (X := X)
    _ = ENNReal.ofReal (∫ y, rowMass y ∂discreteMatrixKernel p fig19_17A) := by
          rw [hfutureIntegral, htransitionIntegral]
    _ =
        ENNReal.ofReal
          (∫ y, F_A P X ({fig19_17A} : Set (HypercubeState 4)) y fig19_17Z
            ∂discreteMatrixKernel p fig19_17A) := by
              -- Proof comment: identify each realized path-kernel row mass with the first-hit
              -- continuation value `F_A`.
              congr 1
              refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
              calc
                rowMass y
                    =
                      ∫ ξ,
                        Set.indicator fig19_17HitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
                          ∂fig19_17RealizationPathKernel (P := P) (X := X) y := by
                            symm
                            exact
                              MeasureTheory.integral_indicator_one
                                (μ := fig19_17RealizationPathKernel (P := P) (X := X) y)
                                (s := fig19_17HitZBeforeAPathEvent)
                                fig19_17HitZBeforeAPathEvent_measurable
                _ = F_A P X ({fig19_17A} : Set (HypercubeState 4)) y fig19_17Z :=
                  fig19_17HitZBeforeAPathIntegral_eq_F_A (p := p) (P := P) (X := X) y

/-- Helper for Exercise 19.5.5: the marked vertex `a` has total unit conductance `4` in the
4-cube. -/
private theorem fig19_17Conductance_at_a_eq_four :
    conductance (simpleGraphWeights fig19_17HypercubeGraph) fig19_17A = 4 := by
  have hrow :
      ∀ y : HypercubeState 4,
        simpleGraphWeights fig19_17HypercubeGraph fig19_17A y =
          if ∃ i : Fin 4, y = hypercubeFlipAt fig19_17A i then (1 : ℝ≥0∞) else 0 := by
    intro y
    by_cases hy : ∃ i : Fin 4, y = hypercubeFlipAt fig19_17A i
    · rcases hy with ⟨i, rfl⟩
      -- Proof comment: each flipped neighbor of `a` is adjacent to `a` with unit conductance.
      simp [simpleGraphWeights, fig19_17HypercubeGraph, fig19_17Adj]
    · have hnotAdj : ¬ fig19_17HypercubeGraph.Adj fig19_17A y := by
        simpa [fig19_17HypercubeGraph, fig19_17Adj] using hy
      -- Proof comment: the hypercube row at `a` is supported only on the four coordinate flips.
      simp [simpleGraphWeights, fig19_17HypercubeGraph, fig19_17Adj, hy, hnotAdj]
  calc
    conductance (simpleGraphWeights fig19_17HypercubeGraph) fig19_17A
        = ∑ y : HypercubeState 4,
            simpleGraphWeights fig19_17HypercubeGraph fig19_17A y := by
              rw [conductance, tsum_fintype]
    _ = ∑ y : HypercubeState 4,
          if ∃ i : Fin 4, y = hypercubeFlipAt fig19_17A i then (1 : ℝ≥0∞) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [hrow y]
    _ = ∑ i : Fin 4, (1 : ℝ≥0∞) := by
          exact fig19_17FlipImage_rowSum_eq_fourFlipSum
            (x := fig19_17A) (F := fun _ ↦ (1 : ℝ≥0∞))
    _ = 4 := by simp

/-- Helper for Exercise 19.5.5: the one-step kernel row at `a` is the uniform average over the
four flipped neighbors. -/
private theorem fig19_17KernelIntegral_eq_neighborAverage_at_a
    (g : HypercubeState 4 → ℝ) :
    ∫ y, g y ∂discreteMatrixKernel p fig19_17A =
      (∑ i : Fin 4, g (hypercubeFlipAt fig19_17A i)) / 4 := by
  have hp : IsStochasticMatrix p :=
    (inferInstance :
      IsRandomWalkWithWeights p (simpleGraphWeights fig19_17HypercubeGraph)).isStochasticMatrix
  have hrow :
      ∫ y, g y ∂discreteMatrixKernel p fig19_17A =
        ∑ y : HypercubeState 4, (p fig19_17A y).toReal * g y := by
    have hsum : Summable (fun y : HypercubeState 4 ↦ (p fig19_17A y).toReal * ‖g y‖) :=
      Summable.of_finite
    simpa using integral_discreteMatrixKernel_eq_tsum p hp g fig19_17A hsum
  have hweight :
      ∀ y : HypercubeState 4,
        (p fig19_17A y).toReal =
          if ∃ i : Fin 4, y = hypercubeFlipAt fig19_17A i then (1 / 4 : ℝ) else 0 := by
    intro y
    rw [(inferInstance :
      IsRandomWalkWithWeights p (simpleGraphWeights fig19_17HypercubeGraph)).transition_eq
      fig19_17A y, ENNReal.toReal_div]
    rw [fig19_17Conductance_at_a_eq_four]
    by_cases hy : ∃ i : Fin 4, y = hypercubeFlipAt fig19_17A i
    · rcases hy with ⟨i, rfl⟩
      -- Proof comment: on the four neighbors of `a`, the simple random walk has probability
      -- `1 / 4`.
      norm_num [simpleGraphWeights, fig19_17HypercubeGraph, fig19_17Adj]
    · have hnotAdj : ¬ fig19_17HypercubeGraph.Adj fig19_17A y := by
        simpa [fig19_17HypercubeGraph, fig19_17Adj] using hy
      -- Proof comment: outside those neighbors, the `a`-row of the transition matrix is zero.
      simp [simpleGraphWeights, fig19_17HypercubeGraph, fig19_17Adj, hy, hnotAdj]
  calc
    ∫ y, g y ∂discreteMatrixKernel p fig19_17A
        = ∑ y : HypercubeState 4, (p fig19_17A y).toReal * g y := hrow
    _ = ∑ y : HypercubeState 4,
          (if ∃ i : Fin 4, y = hypercubeFlipAt fig19_17A i then (1 / 4 : ℝ) else 0) * g y := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [hweight y]
    _ = ∑ y : HypercubeState 4,
          if ∃ i : Fin 4, y = hypercubeFlipAt fig19_17A i then (1 / 4 : ℝ) * g y else 0 := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            by_cases hy' : ∃ i : Fin 4, y = hypercubeFlipAt fig19_17A i <;> simp [hy']
    _ = ∑ i : Fin 4, (1 / 4 : ℝ) * g (hypercubeFlipAt fig19_17A i) := by
          exact fig19_17FlipImage_rowSum_eq_fourFlipSum
            (x := fig19_17A) (F := fun y ↦ (1 / 4 : ℝ) * g y)
    _ = (∑ i : Fin 4, g (hypercubeFlipAt fig19_17A i)) / 4 := by
          rw [← Finset.mul_sum]
          ring

-- Proof sketch: rewrite the target as a first-step decomposition from `fig19_17A`, then identify
-- the interior harmonic function with the explicit layer potential on Hamming layers `0,1,2,3,4`.
include p hSimple hMarkov in
/-- Exercise 19.5.5: for the simple random walk on the hypercube of Fig. 19.17, started at `a`,
the probability of hitting the opposite vertex `z` before the first strictly positive return to
`a` is `3 / 8`. -/
theorem fig19_17_hit_z_before_return_to_a_eq_three_eighths :
    escapeToSetProbability P X fig19_17A {fig19_17Z} =
      (3 / 8 : ℝ≥0∞) := by
  -- Proof comment: first rewrite the escape probability as the one-step average of the
  -- continuation surface `F_A`, then replace `F_A` by the explicit harmonic voltage and evaluate
  -- the resulting neighbor average at `a`.
  calc
    escapeToSetProbability P X fig19_17A {fig19_17Z}
        =
          ENNReal.ofReal
            (∫ y, F_A P X ({fig19_17A} : Set (HypercubeState 4)) y fig19_17Z
              ∂discreteMatrixKernel p fig19_17A) :=
      fig19_17Escape_eq_transitionIntegral_ofFAAtA (p := p) (P := P) (X := X)
    _ =
        ENNReal.ofReal
          (∫ y, fig19_17Voltage y ∂discreteMatrixKernel p fig19_17A) := by
            congr 1
            refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
            exact (fig19_17BoundaryHitProbability_eq_voltage
              (p := p) (P := P) (X := X) y).symm
    _ =
        ENNReal.ofReal
          ((∑ i : Fin 4, fig19_17Voltage (hypercubeFlipAt fig19_17A i)) / 4) := by
            rw [fig19_17KernelIntegral_eq_neighborAverage_at_a (p := p) (g := fig19_17Voltage)]
    _ = ENNReal.ofReal (3 / 8 : ℝ) := by
          rw [fig19_17NeighborVoltageQuotient_at_a]
    _ = (3 / 8 : ℝ≥0∞) := by
          rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 8 by norm_num)]
          norm_num

end

end ProbabilityTheory
