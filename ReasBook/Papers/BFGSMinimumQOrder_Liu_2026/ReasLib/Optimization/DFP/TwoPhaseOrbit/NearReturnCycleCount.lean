module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointAngleGap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- An antitone two-phase angle lift with quadratic phase-gap bounds controls the
angular displacement across a positive number of cycles.  The factor `10` accounts
for the two phase gaps in a cycle and the two possible endpoint phases. -/
theorem cycleCountBound_of_twoPhaseGap
    (angle scale : ℕ → ℝ)
    (hangle : Antitone angle)
    (hscaleNonneg : ∀ q : ℕ, 0 ≤ scale q)
    (hscaleSucc : ∀ q : ℕ, scale (q + 1) ≤ scale q)
    (hgap : ∀ q : ℕ, ∀ i : Fin 2,
      let k := 2 * q + i.val
      angle k - angle (k + 1) ≤ (5 / 2 : ℝ) * scale q ^ 2)
    (j N : ℕ) (σ τ : Fin 2) (hN : 0 < N)
    (m : ℤ) (ζ : ℝ)
    (hdecomposition :
      angle (2 * j + σ.val) - angle (2 * (j + N) + τ.val) =
        2 * Real.pi * (m : ℝ) + ζ)
    (hremainder : |ζ| < scale j ^ 2 / 4) :
    2 * Real.pi * (m : ℝ) - scale j ^ 2 / 4 ≤
      (N : ℝ) * 10 * scale j ^ 2 := by
  have hscaleAnti : Antitone scale := antitone_nat_of_succ_le hscaleSucc
  have hgapEven (q : ℕ) :
      angle (2 * q) - angle (2 * q + 1) ≤
        (5 / 2 : ℝ) * scale q ^ 2 := by
    have hbound := hgap q (0 : Fin 2)
    simpa only [Fin.val_zero, add_zero] using hbound
  have hgapOdd (q : ℕ) :
      angle (2 * q + 1) - angle ((2 * q + 1) + 1) ≤
        (5 / 2 : ℝ) * scale q ^ 2 := by
    have hbound := hgap q (1 : Fin 2)
    simpa only [Fin.val_one] using hbound
  have hcycleGap (q : ℕ) :
      angle (2 * q) - angle (2 * (q + 1)) ≤ 5 * scale q ^ 2 := by
    have hindex : 2 * (q + 1) = (2 * q + 1) + 1 := by
      omega
    rw [hindex]
    calc
      angle (2 * q) - angle ((2 * q + 1) + 1) =
          (angle (2 * q) - angle (2 * q + 1)) +
            (angle (2 * q + 1) - angle ((2 * q + 1) + 1)) := by
        ring
      _ ≤ (5 / 2 : ℝ) * scale q ^ 2 + (5 / 2 : ℝ) * scale q ^ 2 :=
        add_le_add (hgapEven q) (hgapOdd q)
      _ = 5 * scale q ^ 2 := by
        ring
  have hfullBound (q : ℕ) : ∀ n : ℕ,
      angle (2 * q) - angle (2 * (q + n)) ≤
        (n : ℝ) * 5 * scale q ^ 2 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hindex : 2 * (q + (n + 1)) = 2 * ((q + n) + 1) := by
          omega
        have hqLe : q ≤ q + n := by
          omega
        have hscaleLe : scale (q + n) ≤ scale q := hscaleAnti hqLe
        have hsquareLe : scale (q + n) ^ 2 ≤ scale q ^ 2 :=
          pow_le_pow_left₀ (hscaleNonneg (q + n)) hscaleLe 2
        have hfiveNonneg : (0 : ℝ) ≤ 5 := by
          norm_num
        have hgapMonotone : 5 * scale (q + n) ^ 2 ≤ 5 * scale q ^ 2 :=
          mul_le_mul_of_nonneg_left hsquareLe hfiveNonneg
        calc
          angle (2 * q) - angle (2 * (q + (n + 1))) =
              (angle (2 * q) - angle (2 * (q + n))) +
                (angle (2 * (q + n)) - angle (2 * ((q + n) + 1))) := by
            rw [hindex]
            ring
          _ ≤ (n : ℝ) * 5 * scale q ^ 2 + 5 * scale (q + n) ^ 2 :=
            add_le_add ih (hcycleGap (q + n))
          _ ≤ (n : ℝ) * 5 * scale q ^ 2 + 5 * scale q ^ 2 :=
            add_le_add_right hgapMonotone _
          _ = ((n + 1 : ℕ) : ℝ) * 5 * scale q ^ 2 := by
            rw [Nat.cast_add, Nat.cast_one]
            ring
  have hstartIndex : 2 * j ≤ 2 * j + σ.val := by
    omega
  have hendIndex : 2 * (j + N) + τ.val ≤ 2 * (j + (N + 1)) := by
    omega
  have hstart : angle (2 * j + σ.val) ≤ angle (2 * j) :=
    hangle hstartIndex
  have hend : angle (2 * (j + (N + 1))) ≤ angle (2 * (j + N) + τ.val) :=
    hangle hendIndex
  have henclose :
      angle (2 * j + σ.val) - angle (2 * (j + N) + τ.val) ≤
        angle (2 * j) - angle (2 * (j + (N + 1))) := by
    linarith
  have hcycles := hfullBound j (N + 1)
  have hcountNat : N + 1 ≤ 2 * N := by
    omega
  have hcountReal : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    calc
      ((N + 1 : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := Nat.cast_le.mpr hcountNat
      _ = 2 * (N : ℝ) := by
        norm_num
  have hfiveNonneg : (0 : ℝ) ≤ 5 := by
    norm_num
  have hfactorNonneg : 0 ≤ 5 * scale j ^ 2 :=
    mul_nonneg hfiveNonneg (sq_nonneg _)
  have hcountMul := mul_le_mul_of_nonneg_right hcountReal hfactorNonneg
  have hcountBound :
      ((N + 1 : ℕ) : ℝ) * 5 * scale j ^ 2 ≤
        (N : ℝ) * 10 * scale j ^ 2 := by
    calc
      ((N + 1 : ℕ) : ℝ) * 5 * scale j ^ 2 =
          ((N + 1 : ℕ) : ℝ) * (5 * scale j ^ 2) := by
        ring
      _ ≤ (2 * (N : ℝ)) * (5 * scale j ^ 2) := hcountMul
      _ = (N : ℝ) * 10 * scale j ^ 2 := by
        ring
  have hangleUpper :
      angle (2 * j + σ.val) - angle (2 * (j + N) + τ.val) ≤
        (N : ℝ) * 10 * scale j ^ 2 :=
    henclose.trans (hcycles.trans hcountBound)
  have hremainderLower : -(scale j ^ 2 / 4) < ζ := (abs_lt.mp hremainder).1
  have hleft :
      2 * Real.pi * (m : ℝ) - scale j ^ 2 / 4 ≤
        angle (2 * j + σ.val) - angle (2 * (j + N) + τ.val) := by
    rw [hdecomposition]
    linarith
  exact hleft.trans hangleUpper

/-- Along every sufficiently small invariant slow curve, a positive near-return winding
across `N` cycles satisfies the uniform cycle-count inequality. -/
theorem slowCurveNearReturnCycleCountBound (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5))
    (κ : ℝ) (hκ : κ ∈ Set.Ioo (1 / Real.sqrt 2) 1) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Cθ > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun i : ℕ ↦ (orbit.state i).center) atTop (𝓝 Clim) →
            ∀ j N : ℕ, ∀ σ τ : Fin 2,
              0 < N →
                κ * (orbit.state j).ε < (orbit.state (j + N)).ε →
                  ∀ (m : ℤ) (ζ : ℝ),
                    orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                        orbit.endpointPolarAngleLift Clim (2 * (j + N) + τ.val) =
                      2 * Real.pi * (m : ℝ) + ζ →
                        |ζ| < (orbit.state j).ε ^ 2 / 4 →
                          2 * Real.pi * (m : ℝ) - (orbit.state j).ε ^ 2 / 4 ≤
                            (N : ℝ) * Cθ * (orbit.state j).ε ^ 2 := by
  obtain ⟨ηAngle, hηAngle, hAngle⟩ :=
    slowCurveEndpointPolarAngleGapExplicitBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηNext, hηNext, hNext⟩ :=
    DFP.TwoLeg.slowCurveNextPosLt p h h_pJet h_hJet
  let εbar := min ηAngle (min ηGraph ηNext)
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · dsimp only [εbar]
      exact lt_min hηAngle.1 (lt_min hηGraph.1 hηNext)
    · exact (min_le_left _ _).trans_lt hηAngle.2
  have htenPos : (0 : ℝ) < 10 := by
    norm_num
  refine ⟨εbar, hεbar, (10 : ℝ), htenPos, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεAngle : ε₀ ∈ Set.Ioc 0 ηAngle :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεNext : ε₀ ≤ ηNext :=
    hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hscale (q : ℕ) : (orbit.state q).ε ∈ Set.Ioc 0 ε₀ := by
    let xq := DFP.TwoLeg.stateMap^[q] (ε₀, p ε₀, h ε₀)
    have hx := hGraph ε₀ hεGraph q
    have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ q
    have hcoordinates' : (orbit.state q).coordinates = xq := by
      simpa only [orbit, xq] using hcoordinates
    have hscaleEq : (orbit.state q).ε = xq.1 := by
      simpa only [State.coordinates_def] using congrArg Prod.fst hcoordinates'
    rw [hscaleEq]
    exact hx.2
  have hstateGraph (q : ℕ) : (orbit.state q).coordinates =
      ((orbit.state q).ε, p (orbit.state q).ε, h (orbit.state q).ε) := by
    let xq := DFP.TwoLeg.stateMap^[q] (ε₀, p ε₀, h ε₀)
    have hx := hGraph ε₀ hεGraph q
    have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ q
    have hcoordinates' : (orbit.state q).coordinates = xq := by
      simpa only [orbit, xq] using hcoordinates
    have hscaleEq : (orbit.state q).ε = xq.1 := by
      simpa only [State.coordinates_def] using congrArg Prod.fst hcoordinates'
    calc
      (orbit.state q).coordinates = xq := hcoordinates'
      _ = (xq.1, p xq.1, h xq.1) := hx.1
      _ = ((orbit.state q).ε, p (orbit.state q).ε, h (orbit.state q).ε) := by
        rw [hscaleEq]
  have hscaleSucc (q : ℕ) : (orbit.state (q + 1)).ε ≤ (orbit.state q).ε := by
    have hqNext : (orbit.state q).ε ∈ Set.Ioc 0 ηNext :=
      ⟨(hscale q).1, (hscale q).2.trans hεNext⟩
    have hraw := (hNext (orbit.state q).ε hqNext).2.le
    have hcoordinate : (orbit.state (q + 1)).ε =
        (DFP.TwoLeg.stateMap (orbit.state q).coordinates).1 := by
      calc
        (orbit.state (q + 1)).ε = ((orbit.state (q + 1)).coordinates).1 := by
          rw [State.coordinates_def]
        _ = (((orbit.state q).next).coordinates).1 := by
          rw [orbit.state_succ]
        _ = (DFP.TwoLeg.stateMap (orbit.state q).coordinates).1 := by
          rw [State.next_coordinates]
    rw [hcoordinate, hstateGraph q]
    simpa only [DFP.TwoLeg.stateMap_fst] using hraw
  intro Clim hClim
  obtain ⟨hangleAnti, hgap⟩ := hAngle ε₀ hεAngle Clim hClim
  have hscaleNonneg (q : ℕ) : 0 ≤ (orbit.state q).ε := (hscale q).1.le
  have hgapUpper (q : ℕ) (i : Fin 2) :
      let k := 2 * q + i.val
      orbit.endpointPolarAngleLift Clim k - orbit.endpointPolarAngleLift Clim (k + 1) ≤
        (5 / 2 : ℝ) * (orbit.state q).ε ^ 2 :=
    (hgap q i).2
  intro j N σ τ hN hscaleCompare m ζ hdecomposition hremainder
  exact cycleCountBound_of_twoPhaseGap
    (fun k ↦ orbit.endpointPolarAngleLift Clim k)
    (fun q ↦ (orbit.state q).ε)
    hangleAnti.antitone hscaleNonneg hscaleSucc hgapUpper
    j N σ τ hN m ζ hdecomposition hremainder

end DFP.TwoPhaseOrbit
