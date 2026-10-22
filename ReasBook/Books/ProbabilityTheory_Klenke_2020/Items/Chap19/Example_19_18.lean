/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_15
import Mathlib

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace ProbabilityTheory

/- `source-facing`: This item studies concrete series and parallel electrical networks.
Its primitive data are the edge conductances/resistances of those networks.
`core/canonical`: Chapter 19 already organizes electrical networks around
`electricalCurrent`, `IsElectricalPotential`, and `netFlowOnSet`, with Definition 19.17
identifying effective conductance/resistance as the boundary current and its reciprocal.
`bridge/view`: the declarations below package the concrete path/parallel networks into
conductance families and state the textbook series/parallel formulas directly through that owner
API. -/

section SeriesConnection

variable {k n : ℕ}

/-- The conductance network on the path `0 - 1 - ... - n` whose edge `(i, i + 1)` has
conductance `c i`. -/
def pathConductance {n : ℕ} (c : Fin n → ℝ≥0∞) : Fin (n + 1) → Fin (n + 1) → ℝ≥0∞
  | i, j =>
      if hij : i.1 + 1 = j.1 then
        c ⟨i.1, Nat.lt_of_succ_lt_succ <| by simpa [hij] using j.2⟩
      else if hji : j.1 + 1 = i.1 then
        c ⟨j.1, Nat.lt_of_succ_lt_succ <| by simpa [hji] using i.2⟩
      else
        0

-- Proof sketch: Kirchhoff's rule at the middle vertex of the three-point path gives
-- `c 0 * (u 1 - u 0) = c 1 * (u 2 - u 1)`. For finite positive conductances, substituting the
-- boundary values `u 0 = 0` and `u 2 = 1` yields the conductance-ratio formula without any
-- `toReal` degeneration at `∞`.
/-- A three-point case of this item (1): in the series network with finite positive
edge conductances `c 0` and `c 1`, the middle voltage is the conductance ratio
`c 1 / (c 0 + c 1)`. -/
theorem threePointSeriesVoltage_eq_conductanceRatio
    {u : Fin 3 → ℝ} {c : Fin 2 → ℝ≥0∞}
    (hu : IsElectricalPotential (pathConductance c) ({0, 2} : Set (Fin 3)) u)
    (hfinite : ∀ i : Fin 2, c i < ∞)
    (hpos : ∀ i : Fin 2, 0 < c i)
    (h0 : u 0 = 0) (h2 : u 2 = 1) :
    u 1 = (c 1).toReal / ((c 0).toReal + (c 1).toReal) := by
  -- Proof comment: Kirchhoff's rule at the middle vertex leaves exactly the two adjacent edge
  -- currents, and the boundary values turn that linear relation into the desired ratio formula.
  have hmid :
      netFlowAt (electricalCurrent (pathConductance c) u) 1 = 0 :=
    hu.netFlowAt_eq_zero (by simp)
  have hkirch :
      (c 0).toReal * (u 1 - u 0) + (c 1).toReal * (u 1 - u 2) = 0 := by
    simpa [netFlowAt_def, Fin.sum_univ_three, electricalCurrent_apply, pathConductance] using hmid
  have hc0_pos : 0 < (c 0).toReal :=
    ENNReal.toReal_pos (by exact (hpos 0).ne') (by exact ne_of_lt (hfinite 0))
  have hc1_pos : 0 < (c 1).toReal :=
    ENNReal.toReal_pos (by exact (hpos 1).ne') (by exact ne_of_lt (hfinite 1))
  have hsum_pos : 0 < (c 0).toReal + (c 1).toReal :=
    add_pos hc0_pos hc1_pos
  rw [h0, h2] at hkirch
  apply (eq_div_iff hsum_pos.ne').2
  linarith

-- Proof sketch: apply `threePointSeriesVoltage_eq_conductanceRatio` to the path conductance
-- `i ↦ (R i)⁻¹`; positivity of the resistances gives the required finite positive conductances,
-- and the resulting fraction of reciprocals simplifies to the resistance ratio.
/-- A three-point case of this item (2): in the same series network with edge
resistances `R 0` and `R 1`, the middle voltage is the resistance ratio
`R 0 / (R 0 + R 1)`. -/
theorem threePointSeriesVoltage_eq_resistanceRatio
    {u : Fin 3 → ℝ} {R : Fin 2 → ℝ}
    (hu : IsElectricalPotential
      (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) ({0, 2} : Set (Fin 3)) u)
    (h0 : u 0 = 0) (h2 : u 2 = 1)
    (hR0_pos : 0 < R 0) (hR1_pos : 0 < R 1) :
    u 1 = R 0 / (R 0 + R 1) := by
  -- Proof comment: specialize the conductance-ratio formula to reciprocal resistances and then
  -- simplify the resulting fraction of inverses.
  have hR_pos : ∀ i : Fin 2, 0 < R i := by
    intro i
    fin_cases i
    · simpa using hR0_pos
    · simpa using hR1_pos
  have htoReal_inv : ∀ i : Fin 2, (ENNReal.ofReal ((R i)⁻¹)).toReal = (R i)⁻¹ := by
    intro i
    rw [ENNReal.toReal_ofReal]
    exact inv_nonneg.2 (le_of_lt (hR_pos i))
  have hratio :
      u 1 = (R 1)⁻¹ / ((R 0)⁻¹ + (R 1)⁻¹) := by
    simpa [htoReal_inv] using
      threePointSeriesVoltage_eq_conductanceRatio hu
        (fun i ↦ by simp)
        (fun i ↦ by simpa using ENNReal.ofReal_pos.mpr (inv_pos.2 (hR_pos i)))
        h0 h2
  calc
    u 1 = (R 1)⁻¹ / ((R 0)⁻¹ + (R 1)⁻¹) := hratio
    _ = R 0 / (R 0 + R 1) := by
      field_simp [hR0_pos.ne', hR1_pos.ne']
      ring

/-- Helper for this item: evaluating the current on the oriented path edge `(l + 1, l)`
gives the reciprocal resistance times the corresponding voltage drop. -/
lemma pathEdgeCurrent_toPredecessor_eq_inv_mul_drop
    {n : ℕ} {u : Fin (n + 1) → ℝ} {R : Fin n → ℝ} (l : Fin n)
    (hR_pos : 0 < R l) :
    electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
      l.succ (Fin.castSucc l) =
      (R l)⁻¹ * (u l.succ - u (Fin.castSucc l)) := by
  -- Proof comment: the only conductance contributing on the adjacent edge `(l + 1, l)` is the
  -- reciprocal resistance attached to `l`, so Ohm's law is already in the desired normal form.
  have hcond :
      pathConductance (fun i ↦ ENNReal.ofReal ((R i)⁻¹)) l.succ (Fin.castSucc l) =
        ENNReal.ofReal ((R l)⁻¹) := by
    have hforward : ¬ (l.1 + 1 + 1 = l.1) := by
      omega
    have hbackward : (Fin.castSucc l).1 + 1 = l.succ.1 := by
      simp
    simp [pathConductance, hforward]
  -- Proof comment: positivity of `R l` keeps `ENNReal.ofReal` from truncating the reciprocal.
  rw [electricalCurrent_apply, hcond, ENNReal.toReal_ofReal]
  exact inv_nonneg.2 (le_of_lt hR_pos)

/-- Helper for this item: on a path edge, Ohm's law rewrites the voltage drop as the edge
current multiplied by the edge resistance. -/
lemma pathEdgeVoltageDrop_eq_current_mul_resistance
    {n : ℕ} {u : Fin (n + 1) → ℝ} {R : Fin n → ℝ} (l : Fin n)
    (hR_pos : 0 < R l) :
    u l.succ - u (Fin.castSucc l) =
      electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
        l.succ (Fin.castSucc l) * R l := by
  -- Proof comment: rewrite the edge current by the adjacent conductance and cancel the reciprocal
  -- resistance against `R l`.
  have hmul :
      electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
          l.succ (Fin.castSucc l) * R l =
        u l.succ - u (Fin.castSucc l) := by
    calc
      electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
          l.succ (Fin.castSucc l) * R l
          = (((R l)⁻¹) * (u l.succ - u (Fin.castSucc l))) * R l := by
              rw [pathEdgeCurrent_toPredecessor_eq_inv_mul_drop l hR_pos]
      _ = u l.succ - u (Fin.castSucc l) := by
            field_simp [hR_pos.ne']
  exact hmul.symm

/-- Helper for this item: summing the edgewise voltage drops over the first `k` edges of the
path telescopes to the total voltage drop from `0` to `k`. -/
lemma pathPrefixEdgeDrops_telescope
    {n k : ℕ} (hk : k ≤ n) (u : Fin (n + 1) → ℝ) :
    ∑ l : Fin k, (u (Fin.castLE hk l).succ - u (Fin.castSucc (Fin.castLE hk l))) =
      u ⟨k, Nat.lt_succ_of_le hk⟩ - u 0 := by
  -- Route correction: isolate the pure `Fin` telescope before any electrical-current algebra.
  induction k with
  | zero =>
      -- Proof comment: the empty prefix has no edge drops, so both sides are zero.
      simp
  | succ k ih =>
      -- Proof comment: split off the last edge, rewrite the remaining prefix by the induction
      -- hypothesis, and then telescope the last two vertex values.
      rw [Fin.sum_univ_castSucc]
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hhead :
          ∑ x : Fin k,
              (u (Fin.castLE hk x.castSucc).succ - u (Fin.castSucc (Fin.castLE hk x.castSucc))) =
            ∑ x : Fin k, (u (Fin.castLE hk' x).succ - u (Fin.castSucc (Fin.castLE hk' x))) := by
        simp [Fin.castLE_castSucc]
      rw [hhead, ih hk']
      have hlast : Fin.castLE hk (Fin.last k) = ⟨k, hk⟩ := by
        ext
        simp
      rw [hlast]
      have hsucc : (⟨k, hk⟩ : Fin n).succ = ⟨k + 1, Nat.lt_succ_of_le hk⟩ := by
        ext
        simp
      have hcast : Fin.castSucc (⟨k, hk⟩ : Fin n) = ⟨k, Nat.lt_succ_of_le hk'⟩ := by
        ext
        simp
      rw [hsucc, hcast]
      ring

/-- Helper for this item: summing the edgewise Ohm-law identities along the first `k` edges of
the path gives the prefix voltage drop. -/
lemma pathPrefixVoltageDrop_eq_current_mul_sum
    (hk : k ≤ n) {u : Fin (n + 1) → ℝ} {I₀ : ℝ} {R : Fin n → ℝ}
    (hcurrent :
      ∀ l : Fin n,
        electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
          l.succ (Fin.castSucc l) = I₀)
    (hR_pos : ∀ l : Fin n, 0 < R l) :
    u ⟨k, Nat.lt_succ_of_le hk⟩ - u 0 = I₀ * ∑ l : Fin k, R (Fin.castLE hk l) := by
  -- Route correction: rewrite the pure prefix telescope edge-by-edge by Ohm's law, instead of
  -- mixing the electrical proof with `Fin`/`Nat` summation transport.
  calc
    u ⟨k, Nat.lt_succ_of_le hk⟩ - u 0
        = ∑ l : Fin k, (u (Fin.castLE hk l).succ - u (Fin.castSucc (Fin.castLE hk l))) := by
            rw [pathPrefixEdgeDrops_telescope hk u]
    _ = ∑ l : Fin k,
          electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
            (Fin.castLE hk l).succ (Fin.castSucc (Fin.castLE hk l)) * R (Fin.castLE hk l) := by
          -- Proof comment: each summand is the voltage drop across one edge of the prefix path.
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          rw [pathEdgeVoltageDrop_eq_current_mul_resistance (Fin.castLE hk l) (hR_pos _)]
    _ = ∑ l : Fin k, I₀ * R (Fin.castLE hk l) := by
          -- Proof comment: the current hypothesis makes every path-edge current equal to `I₀`.
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          rw [hcurrent (Fin.castLE hk l)]
    _ = I₀ * ∑ l : Fin k, R (Fin.castLE hk l) := by
          rw [Finset.mul_sum]

-- Proof sketch: on each edge, the current on the ordered pair `(l + 1, l)` agrees with the
-- terminal boundary current `I₀` from Definition 19.17. Multiplying by `R l` gives the edgewise
-- voltage drop `u (l + 1) - u l`, and the sum telescopes from `0` to `k`.
/-- A series-connection identity from this item (3): if the current on each
ordered edge `(l + 1, l)` agrees with the common terminal current `I₀`, then the
voltage drop from `0` to `k` is `I₀` times the sum of the edge resistances. -/
theorem pathSeriesVoltageDrop_eq_current_mul_sum
    {u : Fin (k + 1) → ℝ} {I₀ : ℝ} {R : Fin k → ℝ}
    (hcurrent :
      ∀ l : Fin k,
        electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
          l.succ (Fin.castSucc l) = I₀)
    (hR_pos : ∀ l : Fin k, 0 < R l) :
    u (Fin.last k) - u 0 = I₀ * ∑ l : Fin k, R l := by
  -- Proof comment: the full path is the prefix case with `hk = le_rfl`.
  simpa using
    pathPrefixVoltageDrop_eq_current_mul_sum (n := k) (k := k) (hk := le_rfl) hcurrent hR_pos

/-- Helper for this item: at an interior vertex of the path, only the predecessor and
successor can carry nonzero current. -/
lemma pathInteriorCurrent_eq_zero_of_not_memNeighbors
    {n : ℕ} {u : Fin (n + 2) → ℝ} {R : Fin (n + 1) → ℝ}
    (i : Fin n) {y : Fin (n + 2)}
    (hy :
      y ∉ ({Fin.castSucc (Fin.castSucc i), i.succ.succ} : Finset (Fin (n + 2)))) :
    electricalCurrent (pathConductance fun j ↦ ENNReal.ofReal ((R j)⁻¹)) u
      ((Fin.castSucc i).succ) y = 0 := by
  -- Proof comment: on the path, an interior vertex is adjacent only to its predecessor and
  -- successor, so every other conductance term vanishes.
  have hy_pred : y ≠ Fin.castSucc (Fin.castSucc i) := by
    intro h
    exact hy (by simp [h])
  have hy_succ : y ≠ i.succ.succ := by
    intro h
    exact hy (by simp [h])
  have hforward : ¬ i.1 + 1 + 1 = y.1 := by
    intro h
    apply hy_succ
    apply Fin.ext
    simpa using h.symm
  have hbackward : ¬ y.1 = i.1 := by
    intro h
    apply hy_pred
    apply Fin.ext
    simpa using h
  simp [electricalCurrent_apply, pathConductance, hforward, hbackward]

/-- Helper for this item: the net flow at an interior path vertex is the sum of the currents
to its predecessor and successor. -/
lemma pathNetFlowAtInterior_eq_adjacentCurrents
    {n : ℕ} {u : Fin (n + 2) → ℝ} {R : Fin (n + 1) → ℝ}
    (i : Fin n) :
    let I := electricalCurrent (pathConductance fun j ↦ ENNReal.ofReal ((R j)⁻¹)) u
    netFlowAt I ((Fin.castSucc i).succ) =
      I ((Fin.castSucc i).succ) (Fin.castSucc (Fin.castSucc i)) +
        I ((Fin.castSucc i).succ) i.succ.succ := by
  -- Proof comment: split the row sum by the explicit two-point support and then show every
  -- complementary term vanishes by the path-support lemma.
  let I := electricalCurrent (pathConductance fun j ↦ ENNReal.ofReal ((R j)⁻¹)) u
  let pred : Fin (n + 2) := Fin.castSucc (Fin.castSucc i)
  let succ : Fin (n + 2) := i.succ.succ
  have hpred_ne_succ : pred ≠ succ := by
    intro h
    have hval : pred.1 = succ.1 := congrArg Fin.val h
    simp [pred, succ] at hval
    omega
  have hsupport :
      ∑ y ∈ ({pred, succ} : Finset (Fin (n + 2))), I ((Fin.castSucc i).succ) y =
        I ((Fin.castSucc i).succ) pred + I ((Fin.castSucc i).succ) succ := by
    simp [pred, succ, hpred_ne_succ]
  have hcompl :
      ∑ y ∈ ({pred, succ} : Finset (Fin (n + 2)))ᶜ, I ((Fin.castSucc i).succ) y = 0 := by
    refine Finset.sum_eq_zero fun y hy ↦ ?_
    exact pathInteriorCurrent_eq_zero_of_not_memNeighbors (u := u) (R := R) i (by
      simpa [pred, succ] using hy)
  calc
    netFlowAt I ((Fin.castSucc i).succ) = ∑ y : Fin (n + 2), I ((Fin.castSucc i).succ) y := by
      rw [netFlowAt_def]
    _ =
        ∑ y ∈ ({pred, succ} : Finset (Fin (n + 2))), I ((Fin.castSucc i).succ) y +
          ∑ y ∈ ({pred, succ} : Finset (Fin (n + 2)))ᶜ, I ((Fin.castSucc i).succ) y := by
            symm
            exact Finset.sum_add_sum_compl ({pred, succ} : Finset (Fin (n + 2)))
              (fun y ↦ I ((Fin.castSucc i).succ) y)
    _ =
        I ((Fin.castSucc i).succ) pred + I ((Fin.castSucc i).succ) succ := by
          rw [hsupport, hcompl, add_zero]

/-- Helper for this item: at the terminal vertex of the path, only the predecessor can carry
nonzero current. -/
lemma pathTerminalCurrent_eq_zero_of_nePredecessor
    {n : ℕ} {u : Fin (n + 2) → ℝ} {R : Fin (n + 1) → ℝ} {y : Fin (n + 2)}
    (hy : y ≠ Fin.castSucc (Fin.last n)) :
    electricalCurrent (pathConductance fun j ↦ ENNReal.ofReal ((R j)⁻¹)) u
      (Fin.last (n + 1)) y = 0 := by
  -- Proof comment: the terminal vertex has no successor on the path, so the predecessor is its
  -- only possible neighbor with nonzero conductance.
  have hforward : ¬ n + 1 + 1 = y.1 := by
    intro h
    have : n + 2 < n + 2 := by
      simpa [h] using y.2
    exact (lt_irrefl _ this)
  have hbackward : ¬ y.1 = n := by
    intro h
    apply hy
    apply Fin.ext
    simpa using h
  simp [electricalCurrent_apply, pathConductance, hforward, hbackward]

/-- Helper for this item: Kirchhoff's rule at an interior vertex of the path identifies the
left-pointing currents on the two adjacent edges. -/
lemma pathAdjacentCurrent_eq_next
    {n : ℕ} {u : Fin (n + 2) → ℝ} {R : Fin (n + 1) → ℝ}
    (hu : IsElectricalPotential
      (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹))
      ({0, Fin.last (n + 1)} : Set (Fin (n + 2))) u)
    (i : Fin n) :
    electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
      (Fin.castSucc i).succ (Fin.castSucc (Fin.castSucc i)) =
      electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
        i.succ.succ (Fin.castSucc i.succ) := by
  -- Proof comment: first collapse the interior row of the current matrix to the two adjacent
  -- edges, then apply Kirchhoff's rule and antisymmetry on the forward edge.
  let I := electricalCurrent (pathConductance fun j ↦ ENNReal.ofReal ((R j)⁻¹)) u
  let v : Fin (n + 2) := (Fin.castSucc i).succ
  let pred : Fin (n + 2) := Fin.castSucc (Fin.castSucc i)
  let succ : Fin (n + 2) := i.succ.succ
  have hv_not_mem : v ∉ ({0, Fin.last (n + 1)} : Set (Fin (n + 2))) := by
    simp [v]
  have hkirch : netFlowAt I v = 0 :=
    hu.netFlowAt_eq_zero hv_not_mem
  have hrow : netFlowAt I v = I v pred + I v succ := by
    simpa [I, v, pred, succ] using
      (pathNetFlowAtInterior_eq_adjacentCurrents (u := u) (R := R) i)
  have hantisymm : I v succ = -I succ v := by
    simpa [I, v, succ] using hu.antisymm v succ
  have hpred_eq_neg : I v pred = -I v succ := by
    rw [hrow] at hkirch
    linarith
  have hneg : -I v succ = I succ v := by
    linarith
  exact hpred_eq_neg.trans hneg

/-- Helper for this item: the singleton boundary current at the terminal vertex is exactly the
current on the final edge directed toward its predecessor. -/
lemma pathTerminalNetFlow_eq_lastEdgeCurrent
    {n : ℕ} {u : Fin (n + 2) → ℝ} {R : Fin (n + 1) → ℝ} :
    netFlowOnSet
        (electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
        ({Fin.last (n + 1)} : Set (Fin (n + 2))) =
      electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
        (Fin.last (n + 1)) (Fin.castSucc (Fin.last n)) := by
  -- Proof comment: the singleton boundary sum reduces to the terminal row, and the terminal
  -- support lemma leaves only the predecessor term in that row.
  let I := electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
  let terminal : Fin (n + 2) := Fin.last (n + 1)
  let pred : Fin (n + 2) := Fin.castSucc (Fin.last n)
  have hrow : netFlowAt I terminal = I terminal pred := by
    have hsupport :
        ∑ y ∈ ({pred} : Finset (Fin (n + 2))), I terminal y = I terminal pred := by
      simp [pred]
    have hcompl :
        ∑ y ∈ ({pred} : Finset (Fin (n + 2)))ᶜ, I terminal y = 0 := by
      refine Finset.sum_eq_zero fun y hy ↦ ?_
      exact pathTerminalCurrent_eq_zero_of_nePredecessor (u := u) (R := R) (by
        simpa [pred] using hy)
    calc
      netFlowAt I terminal = ∑ y : Fin (n + 2), I terminal y := by
        rw [netFlowAt_def]
      _ =
          ∑ y ∈ ({pred} : Finset (Fin (n + 2))), I terminal y +
            ∑ y ∈ ({pred} : Finset (Fin (n + 2)))ᶜ, I terminal y := by
              symm
              exact Finset.sum_add_sum_compl ({pred} : Finset (Fin (n + 2)))
                (fun y ↦ I terminal y)
      _ = I terminal pred := by
            rw [hsupport, hcompl, add_zero]
  calc
    netFlowOnSet I ({terminal} : Set (Fin (n + 2))) = netFlowAt I terminal := by
      rw [netFlowOnSet_def]
      simp [terminal]
    _ = I terminal pred := hrow
    _ = electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
          (Fin.last (n + 1)) (Fin.castSucc (Fin.last n)) := by
            rfl

/-- Helper for this item: every left-pointing edge current on the path equals the terminal
boundary current. -/
lemma pathCurrentToPredecessor_eq_terminalNetFlow
    {n : ℕ} {u : Fin (n + 1) → ℝ} {R : Fin n → ℝ}
    (hu : IsElectricalPotential
      (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) ({0, Fin.last n} : Set (Fin (n + 1))) u) :
    ∀ l : Fin n,
      electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
        l.succ (Fin.castSucc l) =
        netFlowOnSet
          (electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
          ({Fin.last n} : Set (Fin (n + 1))) := by
  -- Proof comment: start from the terminal edge, where the boundary current is explicit, and
  -- propagate the equality backward one edge at a time via the interior Kirchhoff identity.
  cases n with
  | zero =>
      intro l
      exact Fin.elim0 l
  | succ n =>
      intro l
      induction l using Fin.reverseInduction with
      | last =>
          simpa using
            (pathTerminalNetFlow_eq_lastEdgeCurrent (n := n) (u := u) (R := R)).symm
      | cast i ih =>
          calc
            electricalCurrent (pathConductance fun j ↦ ENNReal.ofReal ((R j)⁻¹)) u
                (Fin.castSucc i).succ (Fin.castSucc (Fin.castSucc i)) =
              electricalCurrent (pathConductance fun j ↦ ENNReal.ofReal ((R j)⁻¹)) u
                i.succ.succ (Fin.castSucc i.succ) := by
                  simpa using pathAdjacentCurrent_eq_next (u := u) (R := R) hu i
            _ =
              netFlowOnSet
                (electricalCurrent (pathConductance fun j ↦ ENNReal.ofReal ((R j)⁻¹)) u)
                ({Fin.last (n + 1)} : Set (Fin (n + 2))) := ih
-- Proof sketch: for the unit-voltage electrical potential on the path, Definition 19.17
-- identifies the effective resistance with the reciprocal of the boundary current through the
-- terminal vertex. The voltage-drop identity from the preceding theorem then gives the series
-- sum of resistances.
/-- A resistance formula from this item (4): for the unit-voltage electrical
potential on the path `0 - 1 - ... - n`, the effective resistance from `0` to `n`
is the sum of the edge resistances. -/
theorem pathSeriesEffectiveResistance_eq_sum
    {u : Fin (n + 1) → ℝ} {R : Fin n → ℝ}
    (hu : IsElectricalPotential
      (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) ({0, Fin.last n} : Set (Fin (n + 1))) u)
    (h0 : u 0 = 0) (hn : u (Fin.last n) = 1)
    (hR_pos : ∀ l : Fin n, 0 < R l) :
    (1 /
      netFlowOnSet
        (electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
        ({Fin.last n} : Set (Fin (n + 1))) : ℝ) =
      ∑ l : Fin n, R l := by
  -- Proof comment: use the terminal boundary flow as the common path current, rewrite the full
  -- voltage drop by the series lemma, and then divide by the nonzero current.
  let flow :=
    netFlowOnSet
      (electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
      ({Fin.last n} : Set (Fin (n + 1)))
  have hcurrent :
      ∀ l : Fin n,
        electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
          l.succ (Fin.castSucc l) = flow := by
    simpa [flow] using pathCurrentToPredecessor_eq_terminalNetFlow (u := u) (R := R) hu
  have hdrop : u (Fin.last n) - u 0 = flow * ∑ l : Fin n, R l := by
    simpa [flow] using
      pathSeriesVoltageDrop_eq_current_mul_sum (u := u) (I₀ := flow) (R := R) hcurrent hR_pos
  have hflow_mul : flow * ∑ l : Fin n, R l = 1 := by
    rw [h0, hn] at hdrop
    linarith
  have hrewrite :
      (1 /
        netFlowOnSet
          (electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
          ({Fin.last n} : Set (Fin (n + 1))) : ℝ) = flow⁻¹ := by
    change (1 / flow : ℝ) = flow⁻¹
    rw [← inv_eq_one_div]
  rw [hrewrite]
  exact inv_eq_of_mul_eq_one_right hflow_mul

-- Proof sketch: combine `pathSeriesEffectiveResistance_eq_sum` with the elementary splitting of
-- the finite sum of edge resistances at the breakpoint `k`.
/-- A decomposition formula from this item (5) and (6): the effective
resistance of a path is the sum of the resistances on the initial segment and on
the tail segment, so series resistances add under a decomposition at `k`. -/
theorem pathSeriesEffectiveResistance_eq_prefix_add_tail
    (hk : k ≤ n) {u : Fin (n + 1) → ℝ} {R : Fin n → ℝ}
    (hu : IsElectricalPotential
      (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) ({0, Fin.last n} : Set (Fin (n + 1))) u)
    (h0 : u 0 = 0) (hn : u (Fin.last n) = 1)
    (hR_pos : ∀ l : Fin n, 0 < R l) :
    (1 /
      netFlowOnSet
        (electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
        ({Fin.last n} : Set (Fin (n + 1))) : ℝ) =
      (∑ l : Fin k, R (Fin.castLE hk l)) +
        ∑ l : Fin (n - k), R (Fin.natAdd_castLEEmb (Nat.sub_le n k) l) := by
  -- Proof comment: first rewrite the effective resistance as the total path sum, then split that
  -- sum into the initial `k` edges and the remaining tail.
  rw [pathSeriesEffectiveResistance_eq_sum (u := u) (R := R) hu h0 hn hR_pos]
  convert (Fin.sum_univ_add (a := k) (b := n - k)
    (f := fun l : Fin (k + (n - k)) ↦ R (Fin.cast (Nat.add_sub_of_le hk) l))) using 1
  · simpa [Fin.cast] using (Equiv.sum_comp (finCongr (Nat.add_sub_of_le hk)) R).symm
  · congr 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    apply congrArg R
    apply Fin.ext
    simp [Fin.natAdd_castLEEmb, Fin.cast]
    omega

-- Proof sketch: apply the effective-resistance formula to the initial segment `0 - ... - k` and
-- to the full path `0 - ... - n`, then use the boundary values `u 0 = 0` and `u n = 1` to solve
-- for `u k`.
/-- Example 19.18 (7): for a series chain with boundary values `u 0 = 0` and `u n = 1`, the
voltage at `k` is the ratio of the prefix resistance sum to the total resistance sum. -/
theorem pathSeriesVoltage_eq_resistanceRatio
    (hk : k ≤ n) {u : Fin (n + 1) → ℝ} {R : Fin n → ℝ}
    (hu : IsElectricalPotential
      (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) ({0, Fin.last n} : Set (Fin (n + 1))) u)
    (h0 : u 0 = 0) (hn : u (Fin.last n) = 1)
    (hR_pos : ∀ l : Fin n, 0 < R l) :
    u ⟨k, Nat.lt_succ_of_le hk⟩ =
      (∑ l : Fin k, R (Fin.castLE hk l)) / ∑ l : Fin n, R l := by
  -- Proof comment: compare the prefix voltage-drop identity with the full-drop identity for the
  -- same common path current, and then eliminate that current by division.
  set flow : ℝ :=
    netFlowOnSet
      (electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
      ({Fin.last n} : Set (Fin (n + 1)))
  set prefixSum : ℝ := ∑ l : Fin k, R (Fin.castLE hk l)
  set totalSum : ℝ := ∑ l : Fin n, R l
  have hcurrent :
      ∀ l : Fin n,
        electricalCurrent (pathConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u
          l.succ (Fin.castSucc l) = flow := by
    simpa [flow] using pathCurrentToPredecessor_eq_terminalNetFlow (u := u) (R := R) hu
  have hprefix_drop : u ⟨k, Nat.lt_succ_of_le hk⟩ - u 0 = flow * prefixSum := by
    simpa [flow, prefixSum] using
      pathPrefixVoltageDrop_eq_current_mul_sum
        (n := n) (k := k) (hk := hk) (u := u) (I₀ := flow) (R := R) hcurrent hR_pos
  have hprefix : u ⟨k, Nat.lt_succ_of_le hk⟩ = flow * prefixSum := by
    rw [h0] at hprefix_drop
    simpa using hprefix_drop
  have hfull_drop : u (Fin.last n) - u 0 = flow * totalSum := by
    simpa [flow, totalSum] using
      pathSeriesVoltageDrop_eq_current_mul_sum (u := u) (I₀ := flow) (R := R) hcurrent hR_pos
  have hfull : flow * totalSum = 1 := by
    rw [h0, hn] at hfull_drop
    linarith
  have htotal_ne : totalSum ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfull
    norm_num at hfull
  apply (eq_div_iff htotal_ne).2
  calc
    u ⟨k, Nat.lt_succ_of_le hk⟩ * totalSum = (flow * prefixSum) * totalSum := by
      rw [hprefix]
    _ = prefixSum * (flow * totalSum) := by
          ring
    _ = prefixSum * 1 := by
          rw [hfull]
    _ = prefixSum := by
          ring

end SeriesConnection

section ParallelConnection

variable {n : ℕ}

/-- The two-vertex conductance network obtained by putting the wire conductances `C i` in
parallel between the boundary vertices `0` and `1`. -/
def parallelConductance (C : Fin n → ℝ≥0∞) : Fin 2 → Fin 2 → ℝ≥0∞ :=
  fun i j ↦
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
      ∑ t, C t
    else
      0

-- Proof sketch: on the two-vertex network, the boundary values `u 0 = 0` and `u 1 = 1` directly
-- determine the induced current. For finite positive wire conductances, the total flow through
-- `1` is exactly the sum of those conductances, with no loss from `toReal` at `∞`.
/-- A parallel-network case of this item (8): for parallel wires with finite
positive conductances and unit voltage drop, the effective conductance is the sum
of the individual wire conductances. -/
theorem parallelConnectionEffectiveConductance_eq_sum
    {u : Fin 2 → ℝ} {C : Fin n → ℝ≥0∞}
    (h0 : u 0 = 0) (h1 : u 1 = 1)
    (hfinite : ∀ i : Fin n, C i < ∞)
    (_hpos : ∀ i : Fin n, 0 < C i) :
    netFlowOnSet (electricalCurrent (parallelConductance C) u) ({1} : Set (Fin 2)) =
      (∑ i, C i).toReal := by
  -- Proof comment: on the two-vertex parallel network, the only nonzero boundary current is the
  -- current from `1` to `0`, and its conductance is the total parallel conductance.
  have hsum_toReal : (∑ i, C i).toReal = ∑ i, (C i).toReal := by
    rw [ENNReal.toReal_sum]
    intro i hi
    exact ne_of_lt (hfinite i)
  simp [netFlowOnSet_def, netFlowAt_def, Fin.sum_univ_two, electricalCurrent_apply,
    parallelConductance, hsum_toReal, h0, h1]

-- Proof sketch: apply the conductance formula to the conductance family `i ↦ (R i)⁻¹`; positive
-- resistances give finite positive conductances, and Definition 19.17 identifies effective
-- resistance with the reciprocal of the induced boundary current.
/-- A parallel-network case of this item (9): for parallel wires with unit
voltage drop, the effective resistance is the reciprocal of the sum of the
reciprocal wire resistances. -/
theorem parallelConnectionEffectiveResistance_eq_reciprocalSum
    {u : Fin 2 → ℝ} {R : Fin n → ℝ}
    (h0 : u 0 = 0) (h1 : u 1 = 1)
    (hR_pos : ∀ i : Fin n, 0 < R i) :
    (1 /
      netFlowOnSet
        (electricalCurrent (parallelConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
        ({1} : Set (Fin 2)) : ℝ) =
      (∑ i, (R i)⁻¹)⁻¹ := by
  -- Proof comment: specialize the parallel conductance formula to reciprocal resistances and then
  -- take reciprocals on both sides.
  have htoReal_inv : ∀ i : Fin n, (ENNReal.ofReal ((R i)⁻¹)).toReal = (R i)⁻¹ := by
    intro i
    rw [ENNReal.toReal_ofReal]
    exact inv_nonneg.2 (le_of_lt (hR_pos i))
  have hflow :
      netFlowOnSet
          (electricalCurrent (parallelConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
          ({1} : Set (Fin 2)) =
        ∑ i, (R i)⁻¹ := by
    have hflowRaw :
        netFlowOnSet
            (electricalCurrent (parallelConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
            ({1} : Set (Fin 2)) =
          (∑ i, ENNReal.ofReal ((R i)⁻¹)).toReal := by
      exact parallelConnectionEffectiveConductance_eq_sum (u := u)
        (C := fun i ↦ ENNReal.ofReal ((R i)⁻¹)) h0 h1
        (fun i ↦ by simp)
        (fun i ↦ by simpa using ENNReal.ofReal_pos.mpr (inv_pos.2 (hR_pos i)))
    calc
      netFlowOnSet
          (electricalCurrent (parallelConductance fun i ↦ ENNReal.ofReal ((R i)⁻¹)) u)
          ({1} : Set (Fin 2))
          = (∑ i, ENNReal.ofReal ((R i)⁻¹)).toReal := hflowRaw
      _ = ∑ i, (R i)⁻¹ := by
            rw [ENNReal.toReal_sum]
            · refine Finset.sum_congr rfl ?_
              intro i hi
              exact htoReal_inv i
            · intro i hi
              simp
  rw [hflow]
  simp [one_div]

end ParallelConnection

end ProbabilityTheory
