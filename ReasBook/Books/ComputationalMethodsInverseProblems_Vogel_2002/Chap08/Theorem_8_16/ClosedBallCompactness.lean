/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.LocallyConvex.Bounded
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.Embedding
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.HilbertBidual
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.L1Compactness
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.LpDual

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

namespace BVCompactness

/-- Helper for Theorem 8.16: pulling back the weak image of one critical `Lᵖ` closed ball recovers
the same norm-bounded subset of the ambient `Lᵖ` space. -/
lemma criticalLpClosedBall_preimage_bounded
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (C : ℝ) :
    Bornology.IsBounded
      (((toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d))) ⁻¹'
        (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
          Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C)) : Set
          (criticalLpSpace Ω (Nat.le_of_lt h1d))) := by
  -- Pulling back the weak image of the norm closed ball cannot enlarge the original norm-bounded
  -- set because `toWeakSpace` is injective.
  refine
    (Metric.isBounded_closedBall :
      Bornology.IsBounded
        (Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C)).subset ?_
  intro x hx
  rcases hx with ⟨y, hy, hxy⟩
  exact (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d))).injective hxy ▸ hy

/-- Helper for Theorem 8.16: the weak image of one critical `Lᵖ` norm closed ball is already
weakly closed because closed convex sets have the same closure in the norm and weak topologies. -/
lemma criticalLpClosedBall_image_isClosed
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (C : ℝ) :
    IsClosed
      (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
        Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C) := by
  -- The critical `Lᵖ` norm closed ball is convex, so its weak closure agrees with its norm
  -- closure after applying `toWeakSpace`.
  have hconvex :
      Convex ℝ (Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C) := by
    exact convex_closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C
  have hclosure :
      closure
          (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
            Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C) =
        toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
          Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C := by
    rw [← hconvex.toWeakSpace_closure (𝕜 := ℝ),
      (Metric.isClosed_closedBall : IsClosed
        (Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C)).closure_eq]
  rw [← hclosure]
  exact isClosed_closure

/-- Helper for Theorem 8.16: the finite critical exponent is the real Hölder conjugate of the
ambient dimension when `d > 1`. -/
lemma criticalExponent_toReal_holderConjugate
    (h1d : 1 < d) :
    ((d : ENNReal).toReal).HolderConjugate ((criticalExponent d).toReal) := by
  have hd_ne_one : d ≠ 1 := Nat.ne_of_gt h1d
  have hd_pos : (1 : ℝ) < d := by
    exact_mod_cast h1d
  -- Route correction: normalize the critical exponent to the concrete `d / (d - 1)` formula
  -- first, then compare it to the standard real conjugate-exponent expression.
  refine (Real.holderConjugate_iff_eq_conjExponent hd_pos).2 ?_
  rw [criticalExponent_eq_div_of_ne_one hd_ne_one]
  have hd_sub_toReal : (((d : ENNReal) - 1).toReal) = (d : ℝ) - 1 := by
    -- The finite-dimensional denominator stays finite, so `ENNReal.toReal` preserves subtraction.
    rw [ENNReal.toReal_sub_of_le]
    · simp
    · exact_mod_cast (Nat.le_of_lt h1d)
    · simp
  simp [ENNReal.toReal_div, hd_sub_toReal, sub_eq_add_neg]

/-- Helper for Theorem 8.16: the critical exponent and the ambient dimension form a Hölder
conjugate pair in the `ENNReal` API. -/
lemma criticalExponent_holderConjugate
    (h1d : 1 < d) :
    (criticalExponent d).HolderConjugate (d : ENNReal) := by
  -- Promote the already-normalized real conjugate-exponent identity back to the `ENNReal`
  -- exponents consumed by `ContinuousLinearMap.lpPairing`.
  apply ENNReal.HolderConjugate.of_toReal
  simpa [Real.HolderConjugate, add_comm] using
    (criticalExponent_toReal_holderConjugate (d := d) h1d).symm

/-- Helper for Theorem 8.16: the canonical critical `Lᵖ` pairing defines a strong-dual element
whose operator norm is bounded by the `L^(criticalExponent d)` norm of the representative. -/
lemma criticalLpPairing_norm_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    [Fact (1 ≤ (d : ENNReal))]
    [Fact (1 ≤ criticalExponent d)]
    [(criticalExponent d).HolderConjugate (d : ENNReal)]
    (f : criticalLpSpace Ω hd) :
    ‖((ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (domainMeasure Ω) (criticalExponent d) (d : ENNReal) f)‖ ≤ ‖f‖ := by
  -- Reduce the operator-norm estimate to the `L¹` norm of the Hölder product and then invoke
  -- the standard `Lp` pairing bound.
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro g
  calc
    ‖((ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (domainMeasure Ω) (criticalExponent d) (d : ENNReal) f) g‖
      = ‖MeasureTheory.L1.integralCLM
          (α := EuclideanSpace ℝ (Fin d)) (E := ℝ) (μ := domainMeasure Ω)
          ((ContinuousLinearMap.mul ℝ ℝ).holder
            (μ := domainMeasure Ω) (p := criticalExponent d) (q := (d : ENNReal))
            (r := (1 : ENNReal)) f g)‖ := by
          rfl
    _ ≤ ‖(ContinuousLinearMap.mul ℝ ℝ).holder
          (μ := domainMeasure Ω) (p := criticalExponent d) (q := (d : ENNReal))
          (r := (1 : ENNReal)) f g‖ := by
          exact
            (ContinuousLinearMap.le_opNorm
              (MeasureTheory.L1.integralCLM
                (α := EuclideanSpace ℝ (Fin d)) (E := ℝ) (μ := domainMeasure Ω))
              _).trans <| by
                simpa using
                  (mul_le_mul_of_nonneg_right MeasureTheory.L1.norm_Integral_le_one
                    (norm_nonneg _))
    _ ≤ ‖(ContinuousLinearMap.mul ℝ ℝ)‖ * ‖f‖ * ‖g‖ := by
          simpa using
            (ContinuousLinearMap.norm_holder_apply_apply_le
              (B := ContinuousLinearMap.mul ℝ ℝ) (r := (1 : ENNReal)) f g)
    _ ≤ 1 * ‖f‖ * ‖g‖ := by
          gcongr
          exact ContinuousLinearMap.opNorm_mul_le (𝕜 := ℝ) (R := ℝ)
    _ = ‖f‖ * ‖g‖ := by ring

/-- Helper for Theorem 8.16: the critical `Lᵖ` closed ball maps into one weak-* closed ball in the
dual of `L^d(Ω)` through the canonical Hölder pairing. -/
lemma criticalLpPairingImage_subset_closedBall
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    [Fact (1 ≤ (d : ENNReal))]
    [Fact (1 ≤ criticalExponent d)]
    [(criticalExponent d).HolderConjugate (d : ENNReal)]
    (C : ℝ) :
    (fun f : criticalLpSpace Ω hd ↦
      StrongDual.toWeakDual
        (((ContinuousLinearMap.mul ℝ ℝ).lpPairing
          (domainMeasure Ω) (criticalExponent d) (d : ENNReal) f))) ''
      Metric.closedBall (0 : criticalLpSpace Ω hd) C
      ⊆ WeakDual.toStrongDual ⁻¹'
        Metric.closedBall
          (0 : StrongDual ℝ (MeasureTheory.Lp ℝ (d : ENNReal) (domainMeasure Ω))) C := by
  intro z hz
  rcases hz with ⟨f, hf, rfl⟩
  have hf_norm : ‖f‖ ≤ C := by
    -- Rewrite the norm closed-ball membership once so the pairing estimate can consume it.
    simpa [Metric.mem_closedBall, dist_zero_right] using hf
  -- The pairing operator norm is controlled by the source `Lᵖ` norm, so the whole image stays
  -- inside the same radius-`C` weak-* closed ball.
  simpa [Metric.mem_closedBall, dist_zero_right] using
    (criticalLpPairing_norm_le (d := d) (Ω := Ω) hd f).trans hf_norm

/-- Helper for Theorem 8.16: the Hölder pairing image of one critical `Lᵖ` closed ball is
weak-* compact in the dual of `L^d(Ω)`. -/
lemma criticalLpPairingClosedBall_compact
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    [Fact (1 ≤ (d : ENNReal))]
    [Fact (1 ≤ criticalExponent d)]
    [(criticalExponent d).HolderConjugate (d : ENNReal)]
    (C : ℝ) :
    IsCompact
      (closure
        ((fun f : criticalLpSpace Ω (Nat.le_of_lt h1d) ↦
          StrongDual.toWeakDual
            (((ContinuousLinearMap.mul ℝ ℝ).lpPairing
              (domainMeasure Ω) (criticalExponent d) (d : ENNReal) f))) ''
          Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C)) := by
  have hsubset :
      ((fun f : criticalLpSpace Ω (Nat.le_of_lt h1d) ↦
        StrongDual.toWeakDual
          (((ContinuousLinearMap.mul ℝ ℝ).lpPairing
            (domainMeasure Ω) (criticalExponent d) (d : ENNReal) f))) ''
        Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C) ⊆
        WeakDual.toStrongDual ⁻¹'
          Metric.closedBall
            (0 : StrongDual ℝ (MeasureTheory.Lp ℝ (d : ENNReal) (domainMeasure Ω))) C := by
    -- Reuse the quantitative pairing estimate to place the whole image in one weak-* closed ball.
    exact
      criticalLpPairingImage_subset_closedBall
        (d := d) (Ω := Ω) (hd := Nat.le_of_lt h1d) C
  -- Banach-Alaoglu makes the ambient weak-* closed ball compact, so the closure of the pairing
  -- image is compact as a closed subset.
  exact
    (WeakDual.isCompact_closedBall
        (𝕜 := ℝ)
        (E := MeasureTheory.Lp ℝ (d : ENNReal) (domainMeasure Ω))
        (0 : StrongDual ℝ (MeasureTheory.Lp ℝ (d : ENNReal) (domainMeasure Ω))) C).of_isClosed_subset
      isClosed_closure
      (closure_minimal hsubset
        (WeakDual.isClosed_closedBall
          (𝕜 := ℝ)
          (E := MeasureTheory.Lp ℝ (d : ENNReal) (domainMeasure Ω))
          (0 : StrongDual ℝ (MeasureTheory.Lp ℝ (d : ENNReal) (domainMeasure Ω))) C))

/-- Helper for Theorem 8.16: the canonical Hölder pairing sends the weak critical `Lᵖ` surface
into the weak-* dual of `L^d(Ω)`. -/
def criticalLpPairingWeakMap
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hd : 1 ≤ d)
    [Fact (1 ≤ (d : ENNReal))]
    [Fact (1 ≤ criticalExponent d)]
    [(criticalExponent d).HolderConjugate (d : ENNReal)] :
    WeakSpace ℝ (criticalLpSpace Ω hd) →
      WeakDual ℝ (MeasureTheory.Lp ℝ (d : ENNReal) (domainMeasure Ω)) :=
  fun x ↦
    StrongDual.toWeakDual
      (((ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (domainMeasure Ω) (criticalExponent d) (d : ENNReal)
        ((toWeakSpace ℝ (criticalLpSpace Ω hd)).symm x)))

/-- Helper for Theorem 8.16: on the critical closed ball, the weak-space pairing map has exactly
the same image as the strong-space Hölder pairing used in the Banach-Alaoglu owner above. -/
lemma criticalLpPairingWeakMap_image_closedBall
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    [Fact (1 ≤ (d : ENNReal))]
    [Fact (1 ≤ criticalExponent d)]
    [(criticalExponent d).HolderConjugate (d : ENNReal)]
    (C : ℝ) :
    criticalLpPairingWeakMap (d := d) (Ω := Ω) (hd := Nat.le_of_lt h1d) ''
        (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
          Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C) =
      (fun f : criticalLpSpace Ω (Nat.le_of_lt h1d) ↦
        StrongDual.toWeakDual
          (((ContinuousLinearMap.mul ℝ ℝ).lpPairing
            (domainMeasure Ω) (criticalExponent d) (d : ENNReal) f))) ''
        Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨f, hf, rfl⟩
    -- Re-express the weak-space point by its underlying critical `Lp` representative.
    exact ⟨f, hf, rfl⟩
  · intro hy
    rcases hy with ⟨f, hf, rfl⟩
    -- The same critical `Lp` witness viewed in the weak topology gives the reverse inclusion.
    exact ⟨toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) f, ⟨f, hf, rfl⟩, rfl⟩

/-- Helper for Theorem 8.16: the canonical critical `Lᵖ` image in the weak-star bidual is the
minimal closed-range input needed by the local compactness transfer. -/
lemma criticalLpRange_isClosed
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d) :
    IsClosed
      (Set.range
        (NormedSpace.inclusionInDoubleDualWeak ℝ
          (criticalLpSpace Ω (Nat.le_of_lt h1d)))) := by
  letI : Fact (1 ≤ criticalExponent d) := factOneLeCriticalExponent (Nat.le_of_lt h1d)
  letI : Fact (1 ≤ (d : ENNReal)) := ⟨by exact_mod_cast (Nat.le_of_lt h1d)⟩
  letI : (criticalExponent d).HolderConjugate (d : ENNReal) :=
    criticalExponent_holderConjugate h1d
  have hreal : (criticalExponent d).toReal.HolderConjugate (d : ENNReal).toReal :=
    (criticalExponent_toReal_holderConjugate h1d).symm
  have hp : criticalExponent d ≠ ⊤ := by
    intro h
    have hpos := hreal.pos
    simp only [h, ENNReal.toReal_top, lt_self_iff_false] at hpos
  exact LpDual.inclusionInDoubleDualWeak_range_isClosed (domainMeasure Ω)
    (criticalExponent d) (d : ENNReal) hp (by finiteness) hreal

/-- Helper for Theorem 8.16: the critical weak closed ball will be compact once the closure of its
double-dual image is known to stay inside the canonical range. -/
lemma criticalLpClosedBall_doubleDualRange
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (C : ℝ) :
    closure
        (NormedSpace.inclusionInDoubleDualWeak ℝ
            (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
          (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
            Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C)) ⊆
      Set.range
        (NormedSpace.inclusionInDoubleDualWeak ℝ
          (criticalLpSpace Ω (Nat.le_of_lt h1d))) := by
  -- Route correction: the downstream compactness theorem only needs the closed-ball-specific
  -- bidual range inclusion consumed by `NormedSpace.isCompact_closure_of_isBounded`, not a global
  -- closed-embedding theorem for the pairing map.
  have hsubset :
      NormedSpace.inclusionInDoubleDualWeak ℝ
          (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
        (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
          Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C) ⊆
        Set.range
          (NormedSpace.inclusionInDoubleDualWeak ℝ
            (criticalLpSpace Ω (Nat.le_of_lt h1d))) := by
    intro z hz
    rcases hz with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  -- Once the closed range is isolated as its own owner, the closed-ball statement is just
  -- `closure_minimal`.
  exact closure_minimal hsubset (criticalLpRange_isClosed (d := d) (Ω := Ω) h1d)

/-- Helper for Theorem 8.16: one still needs a canonical weak compactness owner for the critical
`L^(criticalExponent d)(Ω)` closed ball, stated directly on the `criticalLpSpace` surface. -/
lemma criticalLpClosedBall_weakCompact
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (C : ℝ) :
    IsCompact
      (closure
        (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
          Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C)) := by
  let S : Set (WeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d))) :=
    toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
      Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C
  -- The exposed consumer surface now matches mathlib's weak-to-bidual compactness transfer
  -- exactly: boundedness comes from the norm closed ball, and the remaining owner is the
  -- closed-ball-specific bidual range inclusion above.
  simpa [S] using
    (NormedSpace.isCompact_closure_of_isBounded
      (𝕜 := ℝ)
      (X := criticalLpSpace Ω (Nat.le_of_lt h1d))
      (S := S)
      (criticalLpClosedBall_preimage_bounded (d := d) (Ω := Ω) h1d C)
      (criticalLpClosedBall_doubleDualRange (d := d) (Ω := Ω) h1d C))


end BVCompactness

end VariationalRegularization
