module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.GraphJetSmoothness
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.Continuity
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.StateJetDomainFactors
public import ReasLib.Topology.MetricSpace.CompactUniformPositivity
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.GraphJetSmoothness
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.Continuity
import all ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables

/-!
# A common regularity domain for all two-leg observables
-/

public section

noncomputable section

open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoLeg

/-- The five branch margins needed by the canonical spectral and angular charts. -/
def observableBranchFactors (x : ℝ × ℝ × ℝ) : Fin 5 → ℝ :=
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let F₁ := DFP.FirstLeg.frame ε p h
  let F₂ := DFP.SecondLeg.frame ε p h
  let observable := observableMap x
  ![(DFP.FirstLeg.coordinates ε p h).1,
    (DFP.SecondLeg.coordinates ε p h).1,
    (F₁ * F₂) 0 0,
    Real.pi / 2 - |observable.firstEndpointAngleIncrement.toReal|,
    Real.pi / 2 - |observable.secondEndpointAngleIncrement.toReal|]

/-- Every observable branch margin is continuous at the common canceled base. -/
theorem observableBranchFactors_continuousAt (i : Fin 5) :
    ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ observableBranchFactors x i) (0, 2, 1) := by
  have hcoord1 := DFP.FirstLeg.coordinates_continuousAt
  have hcoord2 := DFP.SecondLeg.coordinates_continuousAt
  have hprod : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
        DFP.SecondLeg.frame x.1 x.2.1 x.2.2) 0 0) (0, 2, 1) := by
    have h := ((DFP.FirstLeg.frameEntry_continuousAt 0 0).mul
      (DFP.SecondLeg.frameEntry_continuousAt 0 0)).add
      ((DFP.FirstLeg.frameEntry_continuousAt 0 1).mul
        (DFP.SecondLeg.frameEntry_continuousAt 1 0))
    apply h.congr
    filter_upwards [] with x
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hangle1 := DFP.TwoLeg.firstEndpointAngleMargin_continuousAt
  have hangle2 := DFP.TwoLeg.secondEndpointAngleMargin_continuousAt
  fin_cases i
  · have h := continuousAt_fst.comp hcoord1
    apply h.congr
    exact Filter.Eventually.of_forall (fun x => rfl)
  · have h := continuousAt_fst.comp hcoord2
    apply h.congr
    exact Filter.Eventually.of_forall (fun x => rfl)
  · exact hprod
  · exact hangle1
  · exact hangle2

/-- Every observable branch margin is positive at the common canceled base. -/
theorem observableBranchFactors_base (i : Fin 5) :
    0 < observableBranchFactors (0, 2, 1) i := by
  fin_cases i <;>
    norm_num [observableBranchFactors, observableMap,
      DFP.FirstLeg.coordinates, DFP.FirstLeg.frame, DFP.FirstLeg.outputMetric,
      DFP.FirstLeg.outputGradient, DFP.FirstLeg.spectralFactors,
      DFP.FirstLeg.gradientFactors, DFP.SecondLeg.coordinates,
      DFP.SecondLeg.frame, DFP.SecondLeg.outputMetric, DFP.SecondLeg.outputGradient,
      DFP.SecondLeg.spectralFactors, DFP.SecondLeg.gradientFactors,
      EuclideanPlane.frame, EuclideanPlane.perp_apply, RealSymmetric2.lowVector,
      RealSymmetric2.lowRaw, RealSymmetric2.low, RealSymmetric2.high,
      RealSymmetric2.gap, RealSymmetric2.lowDenom, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_two, EuclideanPlane.frame_mulVec]
  · exact Real.pi_pos
  · have hvector :
        WithLp.toLp 2 ((EuclideanSpace.equiv (Fin 2) ℝ)
          (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2))) =
            (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) := by
      rfl
    rw [hvector, EuclideanPlane.orientation.oangle_self]
    simp only [Real.Angle.toReal_zero, abs_zero, Nat.ofNat_pos,
      div_pos_iff_of_pos_right, gt_iff_lt]
    exact Real.pi_pos

/-- On a bounded closed coefficient ball, all five branch margins share one positive lower bound
throughout one common zero-scale neighborhood. -/
theorem observableBranchFactorsCommonDomain (B : ℝ) (hB : 0 ≤ B) :
    ∃ m > 0, ∃ δ > 0,
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ i : Fin 5, ∀ ε : ℝ, |ε| < δ →
          m ≤ observableBranchFactors
            (graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε) i := by
  let K : Set ((ℝ × ℝ) × (ℝ × ℝ)) := Metric.closedBall 0 B
  letI : CompactSpace K := by
    apply isCompact_iff_compactSpace.mp
    dsimp only [K]
    exact isCompact_closedBall _ _
  have hneK : Nonempty K := by
    have hzero : (0 : (ℝ × ℝ) × (ℝ × ℝ)) ∈ Metric.closedBall 0 B := by
      rw [Metric.mem_closedBall]
      simpa only [dist_self] using hB
    exact ⟨⟨0, by simpa only [K] using hzero⟩⟩
  have hcontinuous : ∀ θ : K, ∀ i : Fin 5,
      ContinuousAt
        (fun p : ℝ × K ↦ observableBranchFactors (graphJetPath
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 p.1) i)
        (0, θ) := by
    intro θ i
    have hpath : ContinuousAt
        (fun p : ℝ × K ↦ graphJetPath
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 p.1)
        (0, θ) := by
      unfold graphJetPath
      fun_prop
    have hbase : graphJetPath
        (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
        (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
        (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
        (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 0 = (0, 2, 1) := by
      simp [graphJetPath]
    have houter := observableBranchFactors_continuousAt i
    rw [← hbase] at houter
    have hcomp := ContinuousAt.comp
      (f := fun p : ℝ × K ↦ graphJetPath
        (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
        (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
        (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
        (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 p.1)
      (g := fun x : ℝ × ℝ × ℝ ↦ observableBranchFactors x i)
      (x := (0, θ)) houter hpath
    simpa only [Function.comp_def] using hcomp
  have hpositive : ∀ θ : K, ∀ i : Fin 5,
      0 < observableBranchFactors
        (graphJetPath
          (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
          (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
          (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
          (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 0) i := by
    intro θ i
    simpa [graphJetPath] using observableBranchFactors_base i
  obtain ⟨m, hm, δ, hδ, hbound⟩ :=
    CompactUniformPositivity.exists_uniform_lower_bound_finite_of_continuousAt
      (fun ε (θ : K) (i : Fin 5) ↦
        observableBranchFactors
          (graphJetPath
            (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
            (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
            (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
            (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 ε) i)
      hcontinuous hneK (inferInstance : Nonempty (Fin 5)) hpositive
  refine ⟨m, hm, δ, hδ, ?_⟩
  intro θ hθ i ε hε
  let θK : K := ⟨θ, by simpa only [K] using hθ⟩
  exact hbound θK i ε hε

/-- The complete common-domain factors: thirteen factored-state margins followed by five
observable branch margins. -/
def observableDomainFactors (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) : Fin 18 → ℝ :=
  Fin.append (DFP.TwoLeg.StateJet.domainFactors θ ε)
    (observableBranchFactors (graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε))

/-- On every bounded graph-coefficient set, one radius preserves all state and observable branch
margins and controls the common order-nine Taylor remainder. -/
theorem observableJetsCommonDomain_via_companions (B : ℝ) (hB : 0 ≤ B) :
    let f := graphObservableFamily
    let J := fun θ ↦ FiniteTaylorJet.ofFunction ℝ 9 (f θ) 0
    ∃ m > 0, ∀ C > 0, ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ ε : ℝ, |ε| < δ →
          (∀ i : Fin 18, m ≤ observableDomainFactors θ ε i) ∧
            ‖(J θ).remainder (f θ) 0 ε‖ ≤ C * |ε| ^ 9 := by
  dsimp only
  obtain ⟨ms, hms, δs, hδs, hs⟩ :=
    DFP.TwoLeg.StateJet.domainFactors_uniform_lower_bound B hB
  obtain ⟨mb, hmb, δb, hδb, hb⟩ := observableBranchFactorsCommonDomain B hB
  let m := min ms mb
  have hm : 0 < m := by
    exact lt_min hms hmb
  refine ⟨m, hm, ?_⟩
  intro C hC
  have huniform := graphObservableFamily_uniformOn B
  obtain ⟨δr, hδr, hr⟩ :=
    FiniteTaylorJet.IsUniformRemainderOn.bound (huniform.remainder C hC)
  let δ := min δs (min δb (min δr (1 / 8)))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hδs (lt_min hδb (lt_min hδr (by norm_num)))
  have hδquarter : δ < 1 / 4 := by
    have hδeighth : δ ≤ 1 / 8 := by
      dsimp only [δ]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  refine ⟨δ, ⟨hδ, hδquarter⟩, ?_⟩
  intro θ hθ ε hε
  have hεs : |ε| < δs := hε.trans_le (by
    dsimp only [δ]
    exact min_le_left _ _)
  have hεb : |ε| < δb := hε.trans_le (by
    dsimp only [δ]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hεr : |ε| < δr := hε.trans_le (by
    dsimp only [δ]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  constructor
  · intro i
    refine Fin.addCases (m := 13) (n := 5) (fun j ↦ ?_) (fun j ↦ ?_) i
    · rw [observableDomainFactors, Fin.append_left]
      exact (min_le_left ms mb).trans (hs θ hθ j ε hεs)
    · rw [observableDomainFactors, Fin.append_right]
      exact (min_le_right ms mb).trans (hb θ hθ j ε hεb)
  · have hrem := hr θ hθ ε (by simpa only [Real.norm_eq_abs] using hεr)
    calc
      ‖(FiniteTaylorJet.ofFunction ℝ 9 (graphObservableFamily θ) 0).remainder
          (graphObservableFamily θ) 0 ε‖
          ≤ C * ‖ε‖ ^ (9 : ℝ) := hrem
      _ = C * |ε| ^ (9 : ℕ) := by
        rw [Real.norm_eq_abs]
        exact congrArg (fun z : ℝ ↦ C * z) (Real.rpow_natCast |ε| 9)

end DFP.TwoLeg
