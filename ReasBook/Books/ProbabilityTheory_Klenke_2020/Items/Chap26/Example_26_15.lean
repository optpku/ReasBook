/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Example_26_15.SignSde
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Theorem_22_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_22
import Mathlib.MeasureTheory.Constructions.Projective

open Filter
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

/-- Helper for Example 26.15: every repaired sign-SDE weak solution already carries the forward
identity `(26.18)` as its stored `solves_sde` field. -/
lemma signSdeWeakForwardIdentity_of_solution
    (L : SignSdeWeakSolution) :
    signSdeWeakForwardIdentity L := by
  -- Proof comment: unfold the weak-solution surface and read off the stored sign-SDE relation.
  simpa [signSdeWeakForwardIdentity, signSdeForwardIdentity, SignSdeWeakSolution.toBrownianPair]
    using L.solves_sde

/-- Helper for Example 26.15: the scalar coordinate of the weak-solution driver is a Brownian
motion. -/
lemma signSdeDriverProcess_isBrownian
    (L : SignSdeWeakSolution) :
    IsBrownianMotion L.μ (signSdeDriverProcess L.W) := by
  -- Proof comment: the weak-solution package stores a one-dimensional standard Brownian driver,
  -- and its unique coordinate is exactly the scalar driver process.
  letI : IsStandardBrownianMotionVector L.μ (CoordinateProcess.toEuclidean L.W) := L.brownian.1
  simpa [signSdeDriverProcess, CoordinateProcess.toEuclidean] using
    (inferInstance : IsBrownianMotion L.μ
      (fun t ω ↦ (CoordinateProcess.toEuclidean L.W t ω) 0))

/-- Helper for Example 26.15: the scalar state coordinate is adapted to the ambient weak-solution
filtration. -/
lemma signSdeStateProcess_adapted
    (L : SignSdeWeakSolution) :
    Adapted L.ℱ (signSdeStateProcess L.X) := by
  intro t
  -- Proof comment: project the path-valued adapted state process to its unique scalar
  -- coordinate.
  change Measurable[L.ℱ t] ((fun x : Fin 1 → ℝ ↦ x 0) ∘ fun ω ↦ L.X ω t)
  exact (measurable_pi_apply 0).comp (L.adapted t)

/-- Helper for Example 26.15: the scalar state coordinate is progressively measurable because the
weak-solution state path is adapted and continuous in time for every sample. -/
lemma signSdeStateProcess_progMeasurable
    (L : SignSdeWeakSolution) :
    ProgMeasurable L.ℱ (signSdeStateProcess L.X) := by
  have hCont : ∀ ω, Continuous (fun t : NNReal ↦ signSdeStateProcess L.X t ω) := by
    intro ω
    -- Proof comment: each weak-solution state sample is a continuous path valued in `Fin 1 → ℝ`,
    -- and the scalar coordinate is obtained by the continuous evaluation map.
    simpa [signSdeStateProcess] using (continuous_apply 0).comp (L.X ω).continuous
  -- Proof comment: continuous sample paths upgrade adaptedness to progressive measurability on the
  -- ambient weak-solution filtration.
  exact (signSdeStateProcess_adapted L).stronglyAdapted.progMeasurable_of_continuous hCont

/-- Helper for Example 26.15: the real sign map is measurable. -/
private theorem measurableRealSignMap_example2615 :
    Measurable (Real.sign : ℝ → ℝ) := by
  classical
  change Measurable
      ((({r : ℝ | r < 0}).piecewise (fun _ ↦ (-1 : ℝ))
          ((({r : ℝ | 0 < r}).piecewise (fun _ ↦ (1 : ℝ)) fun _ ↦ (0 : ℝ)))))
  refine Measurable.piecewise ?_ measurable_const ?_
  · exact measurableSet_lt measurable_id measurable_const
  · refine Measurable.piecewise ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_const measurable_id

/-- Helper for Example 26.15: the sign coefficient `sign(X_t)` is jointly measurable on
`ℝ≥0 × Ω`. -/
lemma signSdeIntegrand_measurable_uncurry
    (L : SignSdeWeakSolution) :
    Measurable (Function.uncurry (signSdeIntegrand L.X)) := by
  have hStateMeas :
      Measurable (Function.uncurry (signSdeStateProcess L.X)) :=
    (signSdeStateProcess_progMeasurable L).measurable_uncurry
  -- Proof comment: the sign coefficient is the measurable real sign map composed with the jointly
  -- measurable scalar state coordinate.
  simpa [Function.comp, Function.uncurry, signSdeIntegrand, signSdeStateProcess] using
    measurableRealSignMap_example2615.comp hStateMeas

/-- Helper for Example 26.15: the sign coefficient is progressively measurable on the ambient
weak-solution filtration. -/
lemma signSdeIntegrand_progMeasurable
    (L : SignSdeWeakSolution) :
    ProgMeasurable L.ℱ (signSdeIntegrand L.X) := by
  -- Proof comment: product measurability of the sign coefficient restricts to every strip
  -- `[0, T] × Ω`, which is exactly the real-valued progressive measurability criterion.
  refine Adapted.progMeasurable_of_measurableOnStrips (ℱ := L.ℱ) ?_
  intro T
  exact
    Adapted.measurableOnStrip_of_productMeasurable
      (ℱ := L.ℱ) (H := signSdeIntegrand L.X)
      (signSdeIntegrand_measurable_uncurry L) T

/-- Helper for Example 26.15: squaring the sign coefficient never exceeds `1`. -/
lemma signSdeIntegrand_sq_le_one
    (L : SignSdeWeakSolution) (t : NNReal) (ω : L.Ω) :
    (signSdeIntegrand L.X t ω) ^ 2 ≤ 1 := by
  -- Proof comment: `Real.sign` only takes the values `-1`, `0`, and `1`, so its square is
  -- always at most `1`.
  obtain hsign | hsign | hsign := Real.sign_apply_eq (signSdeStateProcess L.X t ω)
  · simpa [signSdeIntegrand, signSdeStateProcess, hsign]
  · simpa [signSdeIntegrand, signSdeStateProcess, hsign]
  · simpa [signSdeIntegrand, signSdeStateProcess, hsign]

/-- Helper for Example 26.15: a jointly measurable scalar field whose square is pointwise bounded
by `1` has finite deterministic-horizon square energy on every interval `[0, T]`. -/
lemma squareIntegrableUpTo_of_uncurryMeasurable_sq_le_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {H : NNReal → Ω → ℝ}
    (hH_prod : Measurable (Function.uncurry H))
    (hH_sq_le : ∀ t : NNReal, ∀ ω : Ω, (H t ω) ^ 2 ≤ 1)
    (T : NNReal) :
    ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2) (Set.Icc (0 : ℝ) (T : ℝ)) := by
  refine Filter.Eventually.of_forall ?_
  intro ω
  have hMeas :
      AEStronglyMeasurable
        (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) := by
    have hSliceMeas : Measurable (fun s : ℝ ↦ H s.toNNReal ω) := by
      -- Proof comment: fixing `ω` turns the jointly measurable uncurry into a measurable time
      -- slice on `ℝ`.
      simpa [Function.uncurry] using
        hH_prod.comp (measurable_real_toNNReal.prod_mk measurable_const)
    exact (hSliceMeas.pow_const 2).aestronglyMeasurable
  have hConst :
      Integrable (fun _ : ℝ ↦ (1 : ℝ))
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) := by
    simpa using
      (integrableOn_const (μ := volume) (s := Set.Icc (0 : ℝ) (T : ℝ))
        measure_Icc_lt_top.ne)
  -- Proof comment: dominate the squared slice by the integrable constant `1` on the deterministic
  -- strip.
  exact hConst.mono' hMeas <| Filter.Eventually.of_forall fun s ↦ by
    have hsq_nonneg : 0 ≤ (H s.toNNReal ω) ^ 2 := sq_nonneg _
    have hsq_le : (H s.toNNReal ω) ^ 2 ≤ 1 := hH_sq_le s.toNNReal ω
    simpa [abs_of_nonneg hsq_nonneg] using hsq_le

/-- Helper for Example 26.15: the sign coefficient has finite deterministic-horizon square energy
on every interval `[0, T]`. -/
lemma signSdeIntegrand_squareIntegrableUpTo
    (L : SignSdeWeakSolution) (T : NNReal) :
    ∀ᵐ ω ∂L.μ,
      IntegrableOn
        (fun s : ℝ ↦ (signSdeIntegrand L.X s.toNNReal ω) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
  -- Proof comment: combine the joint measurability of `sign(X)` with the pointwise bound
  -- `sign(X)^2 ≤ 1`.
  exact
    squareIntegrableUpTo_of_uncurryMeasurable_sq_le_one
      (μ := L.μ)
      (H := signSdeIntegrand L.X)
      (signSdeIntegrand_measurable_uncurry L)
      (signSdeIntegrand_sq_le_one L)
      T

/-- Helper for Example 26.15: once the Brownian state starts at `0`, the stored forward identity
normalizes the scalar state process to the canonical Itô process without an additive constant. -/
lemma signSdeWeak_state_eq_forwardIto_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L) :
    ∃ hW : IsContinuousLocalMartingale L.ℱ L.μ (signSdeDriverProcess L.W),
      signSdeStateProcess L.X =
        continuousLocalMartingaleItoIntegralProcess hW (signSdeIntegrand L.X) := by
  change signSdeSolvesSDE L.ℱ L.μ L.X L.W at hForward
  rcases hForward with ⟨hW, hEq⟩
  refine ⟨hW, ?_⟩
  funext t ω
  have hZero : signSdeStateProcess L.X 0 ω = 0 := by
    -- Proof comment: Brownianity of the state process supplies the source initial condition
    -- `X₀ = 0` pointwise.
    simpa using congrFun hX.zero ω
  -- Proof comment: with the initial value removed, the stored weak-solution equation is already
  -- the exact canonical Itô realization needed later.
  simpa [hZero] using hEq t ω

/-- Helper for Example 26.15: summing the clipped increments of a continuous path along one dyadic
row telescopes to the endpoint increment on `[0,T]`. -/
private theorem partitionIncrementSum_eq_endpointIncrement_example2615
    (G : C(NNReal, ℝ)) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
        G (partitionNextPointUpTo P n k T) - G (P n k)) =
      G T - G 0 := by
  let m := partitionBoundIndex P n T
  -- Proof comment: split off the final clipped increment; before that index the row telescopes,
  -- and the last clipped successor is exactly `T`.
  by_cases hm : m = 0
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [m, hm] using le_partitionBoundIndex_time P n T
      simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
    have hm0 : partitionBoundIndex P n T = 0 := by
      simpa [m] using hm
    rw [hm0, Finset.sum_range_zero, hT0]
    ring
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have hkm : partitionBoundIndex P n T = k.succ := by
      simpa [m] using hk
    have hsum :
        ∀ r : ℕ,
          Finset.sum (Finset.range r) (fun j ↦ G (P n (j + 1)) - G (P n j)) =
            G (P n r) - G (P n 0) := by
      intro r
      induction r with
      | zero =>
          simp
      | succ r ihr =>
          rw [Finset.sum_range_succ, ihr]
          abel
    rw [hkm, Finset.sum_range_succ]
    have hprefix :
        Finset.sum (Finset.range k) (fun j ↦ G (partitionNextPointUpTo P n j T) - G (P n j)) =
          G (P n k) - G (P n 0) := by
      -- Proof comment: before the final contributing index, truncation is inactive.
      have hraw :
          Finset.sum (Finset.range k) (fun j ↦ G (partitionNextPointUpTo P n j T) - G (P n j)) =
            Finset.sum (Finset.range k) (fun j ↦ G (P n (j + 1)) - G (P n j)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hj_lt : j + 1 < partitionBoundIndex P n T := by
          simpa [m, hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hnext : partitionNextPointUpTo P n j T = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact le_of_lt (partitionPoint_lt_time_of_lt_truncationBoundIndex P n (j + 1) T hj_lt)
        rw [hnext]
      exact hraw.trans (hsum k)
    have hlast : G (partitionNextPointUpTo P n k T) - G (P n k) = G T - G (P n k) := by
      -- Proof comment: at the last active cell, clipping only changes the successor to the final
      -- endpoint `T`.
      have hnext : partitionNextPointUpTo P n k T = T := by
        rw [partitionNextPointUpTo, min_eq_right]
        simpa [m, hk] using le_partitionBoundIndex_time P n T
      rw [hnext]
    rw [hprefix, hlast]
    simp [IsAdmissiblePartitionSequence.zero_eq (P := P) n]

/-- Helper for Example 26.15: the canonical dyadic Itô realization with unit integrand is
exactly the underlying zero-start continuous local martingale. -/
lemma continuousLocalMartingaleItoIntegralProcess_one_eq_self_of_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hM0 : M 0 = 0) :
    continuousLocalMartingaleItoIntegralProcess hM (fun _ _ ↦ (1 : ℝ)) = M := by
  -- Proof comment: each dyadic row with coefficient `1` telescopes to the endpoint increment
  -- `M T - M 0`, so the canonical `limUnder` process reduces pointwise to `M`.
  refine
    continuousLocalMartingaleItoIntegralProcess_eq_of_tendsto
      (μ := μ) (ℱ := ℱ) (M := M) (H := fun _ _ ↦ (1 : ℝ)) ?_
  intro T ω
  have hPartitionEq :
      ∀ n : ℕ,
        Theorem25_22.partitionPathwiseItoApproximationUpTo
            (fun _ ↦ (1 : ℝ))
            (⟨fun t ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            T
            n =
          M T ω - M 0 ω := by
    intro n
    -- Proof comment: the unit-weighted partition sum is the plain sum of clipped path
    -- increments, and that row telescopes to the endpoint increment.
    simpa [Theorem25_22.partitionPathwiseItoApproximationUpTo] using
      (partitionIncrementSum_eq_endpointIncrement_example2615
        (G := (⟨fun t ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ)))
        (P := Definition2158.dyadicPartitionSequence)
        T
        n)
  -- Proof comment: the dyadic approximants are already constant in `n`, so their limit is the
  -- same endpoint increment, which equals `M T ω` because the process starts from `0`.
  simpa [hPartitionEq, congrFun hM0 ω] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ M T ω - M 0 ω) atTop (𝓝 (M T ω - M 0 ω)))

/-- Helper for Example 26.15: the scalar driver is the canonical unit-integrand Itô process of
itself because Brownian motion starts from `0`. -/
lemma signSdeDriverProcess_eq_canonicalSelf
    (L : SignSdeWeakSolution) :
    ∃ hW : IsContinuousLocalMartingale L.ℱ L.μ (signSdeDriverProcess L.W),
      continuousLocalMartingaleItoIntegralProcess hW (fun _ _ ↦ (1 : ℝ)) =
        signSdeDriverProcess L.W := by
  have hBrownian :
      IsBrownianMotionWithFiltration L.ℱ L.μ L.W := by
    -- Proof comment: repackage the stored weak-solution Brownian driver into the chapter-level
    -- Brownian-with-filtration owner.
    simpa [IsBrownianMotionWithFiltration] using L.brownian
  have hCoordIto :
      IsBrownianLocalItoIntegral L.ℱ L.μ
        (signSdeDriverProcess L.W)
        (fun _ _ ↦ (1 : ℝ))
        (signSdeDriverProcess L.W) := by
    -- Proof comment: the unique scalar driver coordinate is the constant-one Itô integral of the
    -- ambient one-dimensional Brownian motion.
    simpa [signSdeDriverProcess, CoordinateProcess.toEuclidean] using
      (brownianCoordinate_constOne_isBrownianLocalItoIntegral
        (ℱ := L.ℱ)
        (μ := L.μ)
        (W := L.W.toEuclidean)
        hBrownian.1
        0)
  have hCoordData :
      IsContinuousLocalMartingale L.ℱ L.μ (signSdeDriverProcess L.W) ∧
        IsContinuousSquareVariationProcess L.ℱ L.μ
          (signSdeDriverProcess L.W)
          (MeasureTheory.secondMomentCompensator (fun _ _ ↦ (1 : ℝ))) :=
    brownianLocalItoIntegral_isContinuousLocalMartingale_and_has_squareVariation hCoordIto
  have hZero :
      signSdeDriverProcess L.W 0 = 0 := by
    -- Proof comment: the Brownian driver starts from the origin at time `0`.
    funext ω
    simpa using congrFun (signSdeDriverProcess_isBrownian L).zero ω
  refine ⟨hCoordData.1, ?_⟩
  -- Proof comment: specialize the generic unit-integrand canonical-self lemma to the scalar
  -- driver coordinate.
  exact
    continuousLocalMartingaleItoIntegralProcess_one_eq_self_of_zero
      (μ := L.μ)
      (ℱ := L.ℱ)
      hCoordData.1
      hZero

/-- Helper for Example 26.15: every ambient scalar driver martingale of a weak sign-SDE carries
the unit bracket-density witness `d⟨W⟩ / dt = 1`. -/
lemma signSdeDriver_hasAbsolutelyContinuousSquareVariation
    (L : SignSdeWeakSolution)
    {hW : IsContinuousLocalMartingale L.ℱ L.μ (signSdeDriverProcess L.W)} :
    Theorem25_22.HasAbsolutelyContinuousSquareVariation
      (signSdeDriverProcess L.W)
      hW := by
  -- Proof comment: the driver is Brownian, so its square variation is the deterministic identity
  -- clock and therefore has constant density `1`.
  refine ⟨fun _ _ ↦ (1 : NNReal), fun t _ ↦ (t : ℝ), ?_⟩
  refine ⟨signSdeDriverIdentitySquareVariation L, ?_, ?_⟩
  · simpa using
      (stronglyMeasurable_const.progMeasurable :
        ProgMeasurable L.ℱ (fun _ _ : L.Ω ↦ (1 : ℝ)))
  · intro t ω
    simp

/-- Helper for Example 26.15: the normalized forward equation already packages the scalar state as
the Chapter 25 Itô-integral owner driven by the weak-solution driver. -/
lemma signSdeWeak_stateItoOwner_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L) :
    ∃ hW : IsContinuousLocalMartingale L.ℱ L.μ (signSdeDriverProcess L.W),
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral
        (signSdeDriver_hasAbsolutelyContinuousSquareVariation (L := L) (hW := hW))
        (signSdeIntegrand L.X)
        (signSdeStateProcess L.X) := by
  obtain ⟨hW, hStateEq⟩ := signSdeWeak_state_eq_forwardIto_of_forward L hX hForward
  -- Proof comment: after normalizing away the initial value, the state process is literally the
  -- canonical Itô realization, so the owner predicate is just reflexive transport.
  refine ⟨hW, ?_⟩
  simpa [hStateEq] using
    (Theorem25_22.canonicalSelf
      (μ := L.μ)
      (ℱ := L.ℱ)
      (M := signSdeDriverProcess L.W)
      (H := signSdeIntegrand L.X)
      (hM := hW)
      (hbr := signSdeDriver_hasAbsolutelyContinuousSquareVariation (L := L) (hW := hW)))

/-- Helper for Example 26.15: the scalar driver is itself the Chapter 25 Itô-integral owner for
the unit integrand. -/
lemma signSdeDriver_selfItoOwner
    (L : SignSdeWeakSolution) :
    ∃ hW : IsContinuousLocalMartingale L.ℱ L.μ (signSdeDriverProcess L.W),
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral
        (signSdeDriver_hasAbsolutelyContinuousSquareVariation (L := L) (hW := hW))
        (fun _ _ ↦ (1 : ℝ))
        (signSdeDriverProcess L.W) := by
  obtain ⟨hW, hSelfEq⟩ := signSdeDriverProcess_eq_canonicalSelf L
  -- Proof comment: the driver-side owner is the same reflexive canonical-self package, now for
  -- the constant-one integrand.
  refine ⟨hW, ?_⟩
  simpa [hSelfEq] using
    (Theorem25_22.canonicalSelf
      (μ := L.μ)
      (ℱ := L.ℱ)
      (M := signSdeDriverProcess L.W)
      (H := fun _ _ ↦ (1 : ℝ))
      (hM := hW)
      (hbr := signSdeDriver_hasAbsolutelyContinuousSquareVariation (L := L) (hW := hW)))

/-- Helper for Example 26.15: once the state process is Brownian, its natural process filtration
is contained in the ambient weak-solution filtration. -/
lemma signSdeStateProcessFiltration_le_ambient
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L) :
    processFiltration (signSdeStateProcess L.X) ≤ L.ℱ := by
  have hStateMeas :
      ∀ t, Measurable (signSdeStateProcess L.X t) := by
    intro t
    exact (hX.stronglyMeasurable t).measurable
  have hGeneratedLe :
      generatedFiltration (signSdeStateProcess L.X) hStateMeas ≤ L.ℱ :=
    (adapted_iff_generatedFiltration_le hStateMeas).mp
      (signSdeStateProcess_adapted L)
  -- Proof comment: `processFiltration` sits below the generated filtration by construction.
  intro t
  exact (inf_le_right.trans (hGeneratedLe t))

/-- Helper for Example 26.15: if the state process were adapted to the driver filtration, then the
absolute-value state history would also be generated by the driver filtration. -/
lemma absStateProcessFiltration_le_driver_of_stateAdapted
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hAdapted :
      Adapted
        (processFiltration (signSdeDriverProcess L.W))
        (signSdeStateProcess L.X)) :
    processFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|) ≤
      processFiltration (signSdeDriverProcess L.W) := by
  have hAbsMeas :
      ∀ t, Measurable (fun ω ↦ |signSdeStateProcess L.X t ω|) := by
    intro t
    exact measurable_abs.comp ((hX.stronglyMeasurable t).measurable)
  have hAbsAdapted :
      Adapted
        (processFiltration (signSdeDriverProcess L.W))
        (fun t ω ↦ |signSdeStateProcess L.X t ω|) := by
    intro t
    -- Proof comment: compose the assumed driver-adapted state coordinate with the measurable
    -- absolute-value map.
    exact measurable_abs.comp (hAdapted t)
  have hGeneratedLe :
      generatedFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|) hAbsMeas ≤
        processFiltration (signSdeDriverProcess L.W) :=
    (adapted_iff_generatedFiltration_le hAbsMeas).mp hAbsAdapted
  -- Proof comment: the process filtration is the generated history intersected with the ambient
  -- measurable space, so it also lies below the driver filtration.
  intro t
  exact (inf_le_right.trans (hGeneratedLe t))

/-- Helper for Example 26.15: a Brownian motion has a nondegenerate Gaussian marginal at time
`1`, so `B 1` cannot vanish almost surely. -/
lemma brownianFixedTime_not_ae_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    ¬ (∀ᵐ ω ∂μ, B 1 ω = 0) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hMeas : Measurable (B 1) := (hB.stronglyMeasurable 1).measurable
  have hZeroMeasure : μ {ω | B 1 ω = 0} = 0 := by
    have hLaw : HasLaw (B 1) (gaussianReal 0 1) μ := hB.gaussian_marginal (by positivity)
    -- Proof comment: push the time-`1` marginal forward to the centered Gaussian law and use
    -- that the Gaussian measure has no atoms.
    calc
      μ {ω | B 1 ω = 0}
          = μ.map (B 1) ({0} : Set ℝ) := by
              symm
              rw [Measure.map_apply hMeas (MeasurableSet.singleton 0)]
              rfl
      _ = gaussianReal 0 1 ({0} : Set ℝ) := by
            rw [hLaw.map_eq]
      _ = 0 := by
            exact (noAtoms_gaussianReal (by positivity)).measure_singleton 0
  intro hZeroAe
  have hZeroAeCompl : μ ({ω | B 1 ω = 0}ᶜ) = 0 := by
    -- Proof comment: the almost-sure zero hypothesis says the complementary nonzero event is
    -- null.
    simpa [ae_iff, Set.compl_setOf] using hZeroAe
  have hMeasZero : MeasurableSet {ω | B 1 ω = 0} := by
    change MeasurableSet ((B 1) ⁻¹' ({0} : Set ℝ))
    exact hMeas (MeasurableSet.singleton 0)
  have hFullMeasure : μ {ω | B 1 ω = 0} = 1 := by
    have hAdd := measure_add_measure_compl (μ := μ) hMeasZero
    rw [hZeroAeCompl, add_zero] at hAdd
    simpa using hAdd
  have hContr : (0 : ℝ≥0∞) = 1 := by
    calc
      (0 : ℝ≥0∞) = μ {ω | B 1 ω = 0} := hZeroMeasure.symm
      _ = 1 := hFullMeasure
  exact zero_ne_one hContr

/-- Helper for Example 26.15: on every deterministic interval `(0,T]`, a Brownian path spends
zero Lebesgue time at `0`. -/
lemma brownianZeroSet_measureOnIoc_eq_zero_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) {T : NNReal} (hT : 0 < T) :
    ∀ᵐ ω ∂μ,
      (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) {t : ℝ | B (Real.toNNReal t) ω = 0} = 0 := by
  -- Proof comment: Exercise 21.2.1 already proves the zero-occupation statement for the patched
  -- continuous Brownian version, and the patched zero set agrees almost surely with the original
  -- Brownian zero set.
  filter_upwards
      [brownianContinuousVersion_zeroSet_measureOnIoc_eq_zero_ae
        (μ := μ) (B := B) hB (show (0 : ℝ) < (T : ℝ) by exact_mod_cast hT),
        brownianContinuousVersion_zeroSet_ae_eq (μ := μ) (B := B) hB] with ω hPatch hZeroEq
  simpa [hZeroEq] using hPatch

/-- Helper for Example 26.15: on every deterministic interval `(0,T]`, the Brownian sign
coefficient can fail the identity `(sign (X_s))^2 = 1` only on the Brownian zero set. -/
lemma signSdeIntegrand_sq_ne_one_measureOnIoc_eq_zero
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    {T : NNReal} (hT : 0 < T) :
    ∀ᵐ ω ∂L.μ,
      (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))
        {s : ℝ | (signSdeIntegrand L.X s.toNNReal ω) ^ 2 ≠ 1} = 0 := by
  filter_upwards
      [brownianZeroSet_measureOnIoc_eq_zero_ae
        (μ := L.μ) (B := signSdeStateProcess L.X) hX hT] with ω hZero
  have hSubset :
      {s : ℝ | (signSdeIntegrand L.X s.toNNReal ω) ^ 2 ≠ 1} ⊆
        {s : ℝ | signSdeStateProcess L.X s.toNNReal ω = 0} := by
    intro s hs
    by_contra hs0
    have hsq :
        (signSdeIntegrand L.X s.toNNReal ω) ^ 2 = 1 := by
      have hsign_ne_zero :
          Real.sign (signSdeStateProcess L.X s.toNNReal ω) ≠ 0 := by
        rwa [_root_.sign_eq_zero_iff]
      obtain hsign | hsign | hsign := Real.sign_apply_eq (signSdeStateProcess L.X s.toNNReal ω)
      · -- Proof comment: away from the zero set, the sign is either `1` or `-1`, so its square
        -- is exactly `1`.
        simpa [signSdeIntegrand, signSdeStateProcess, hsign]
      · exact (hsign_ne_zero hsign).elim
      · simpa [signSdeIntegrand, signSdeStateProcess, hsign]
    exact hs hsq
  -- Proof comment: the exceptional set where `(sign (X_s))^2 ≠ 1` is contained in the Brownian
  -- zero set, whose restricted Lebesgue measure already vanishes almost surely.
  exact measure_mono_null hSubset hZero

/-- Helper for Example 26.15: stopping-time measurability is monotone under filtration
inclusion. -/
lemma isStoppingTime_of_filtration_le
    {Ω : Type*} [MeasurableSpace Ω]
    {ℱ 𝒢 : Filtration NNReal ‹MeasurableSpace Ω›}
    (hℱ𝒢 : ℱ ≤ 𝒢) {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ) :
    IsStoppingTime 𝒢 τ := by
  intro t
  exact hℱ𝒢 t _ (hτ t)

/-- Helper for Example 26.15: Brownian motion is a martingale in its natural filtration. -/
lemma brownianMartingale_natural_local
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    Martingale B (Filtration.natural B hB.stronglyMeasurable) μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let ℱB := Filtration.natural B hB.stronglyMeasurable
  have hB_adapted : StronglyAdapted ℱB B :=
    Filtration.stronglyAdapted_natural (u := B) hB.stronglyMeasurable
  refine ⟨hB_adapted, ?_⟩
  intro s t hst
  have hInc_meas : Measurable (fun ω ↦ B t ω - B s ω) := by
    exact (hB.stronglyMeasurable t).measurable.sub (hB.stronglyMeasurable s).measurable
  have hInc_stronglyMeas :
      StronglyMeasurable[
        MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) (borel ℝ)]
        (fun ω ↦ B t ω - B s ω) :=
    (comap_measurable (fun ω ↦ B t ω - B s ω)).stronglyMeasurable
  have hInc_indep :
      Indep
        (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) (borel ℝ))
        (ℱB s)
        μ :=
    brownianIncrement_indep_naturalFiltration hB hst
  have hInc_mean_zero : ∫ ω, (B t ω - B s ω) ∂μ = 0 := by
    simpa using (brownianIncrement_hasLaw hB hst).integral_eq
  have hBs_int : Integrable (B s) μ :=
    (brownianEval_memLp_two hB s).integrable (by norm_num)
  have hInc_int : Integrable (fun ω ↦ B t ω - B s ω) μ :=
    (brownianIncrement_memLp_two hB hst).integrable (by norm_num)
  have hSplit : (fun ω ↦ B t ω) = fun ω ↦ B s ω + (B t ω - B s ω) := by
    funext ω
    ring
  have hInc_condExp_zero :
      μ[(fun ω ↦ B t ω - B s ω) | ℱB s] =ᵐ[μ] 0 := by
    refine
      (MeasureTheory.condExp_indep_eq
        hInc_meas.comap_le (ℱB.le s) hInc_stronglyMeas hInc_indep).trans ?_
    exact Filter.Eventually.of_forall fun _ ↦ hInc_mean_zero
  calc
    μ[B t | ℱB s]
        =ᵐ[μ] μ[(fun ω ↦ B s ω + (B t ω - B s ω)) | ℱB s] := by
            exact condExp_congr_ae (Filter.EventuallyEq.of_eq hSplit)
    _ =ᵐ[μ] μ[B s | ℱB s] + μ[(fun ω ↦ B t ω - B s ω) | ℱB s] := by
          exact condExp_add hBs_int hInc_int _
    _ =ᵐ[μ] B s + 0 := by
          filter_upwards
            [Filter.EventuallyEq.of_eq
              (condExp_of_stronglyMeasurable (ℱB.le s) (hB_adapted s) hBs_int),
              hInc_condExp_zero]
            with ω hωs hωinc
          simp [hωs, hωinc]
    _ =ᵐ[μ] B s := by
          simp

/-- Helper for Example 26.15: projecting an adapted one-dimensional vector process to its unique
scalar coordinate preserves adaptedness. -/
private lemma oneDimVectorProcessCoordinate_adapted_example2615
    {Ω : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {B : NNReal → Ω → Fin 1 → ℝ}
    (hB : Adapted ℱ B) :
    Adapted ℱ (fun t ω ↦ B t ω 0) := by
  intro t
  -- Proof comment: evaluation at the unique coordinate is measurable, so adaptedness descends
  -- from the one-dimensional vector process to the scalar coordinate.
  change Measurable[ℱ t] ((fun x : Fin 1 → ℝ ↦ x 0) ∘ fun ω ↦ B t ω)
  exact (measurable_pi_apply 0).comp (hB t)

/-- Helper for Example 26.15: any scalar Brownian motion that is adapted to `ℱ` is a martingale on
that same filtration. -/
private lemma scalarBrownian_martingale_of_adapted_example2615
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    (hAdapted : Adapted ℱ B) :
    Martingale B ℱ μ := by
  let hBmNat := brownianMartingale_natural_local (μ := μ) (B := B) hB
  have hNatLe : Filtration.natural B hB.stronglyMeasurable ≤ ℱ := by
    let hBmeas : ∀ t, Measurable (B t) := fun t ↦ (hB.stronglyMeasurable t).measurable
    have hGenLe : generatedFiltration B hBmeas ≤ ℱ :=
      (adapted_iff_generatedFiltration_le hBmeas).mp hAdapted
    -- Proof comment: the generated filtration of the scalar coordinates is exactly the natural
    -- filtration once the deterministic-time measurability witnesses are fixed.
    simpa [generatedFiltration_eq_natural B hB.stronglyMeasurable] using hGenLe
  -- Proof comment: transport the natural-filtration martingale structure across the filtration
  -- inclusion supplied by adaptedness.
  exact martingale_of_le_filtration hNatLe hBmNat hAdapted

/-- Helper for Example 26.15: a deterministic-time observable that is measurable with respect to
the absolute-value history up to `T` factors through the bundled absolute past path on
`Set.Iic T`. -/
lemma absPastPathFactorizationAtTime
    {Ω : Type*} [MeasurableSpace Ω]
    {B : NNReal → Ω → ℝ} {T : NNReal} {Z : Ω → ℝ}
    (hMeas :
      Measurable[processFiltration (fun t ω ↦ |B t ω|) T] Z) :
    ∃ Φ : (Set.Iic T → ℝ) → ℝ, Measurable Φ ∧
      Z = Φ ∘ (fun ω u ↦ |B u ω|) := by
  let pastPath : Ω → Set.Iic T → ℝ := fun ω u ↦ |B u ω|
  have hPastLe :
      processFiltration (fun t ω ↦ |B t ω|) T ≤
        MeasurableSpace.comap pastPath
          (MeasurableSpace.pi : MeasurableSpace (Set.Iic T → ℝ)) := by
    -- Proof comment: every generator `ω ↦ |B r ω|` with `r ≤ T` is a coordinate of the bundled
    -- absolute past path, so the whole deterministic-time history lies in the pullback sigma
    -- algebra of `pastPath`.
    refine (inf_le_right.trans ?_)
    refine iSup₂_le fun r hr ↦ ?_
    simpa [pastPath] using
      (((measurable_pi_apply ⟨r, hr⟩).comp
        (measurable_iff_comap_le.mpr le_rfl :
          Measurable[MeasurableSpace.comap pastPath
            (MeasurableSpace.pi : MeasurableSpace (Set.Iic T → ℝ))] pastPath))).comap_le
  have hMeasPast :
      Measurable[MeasurableSpace.comap pastPath
        (MeasurableSpace.pi : MeasurableSpace (Set.Iic T → ℝ))] Z :=
    Measurable.mono hMeas hPastLe le_rfl
  -- Proof comment: once the deterministic-time filtration is rewritten as a pullback along the
  -- past-path map, the Doob-Dynkin lemma gives an explicit measurable factorization.
  obtain ⟨Φ, hΦ, hFactor⟩ := hMeasPast.exists_eq_measurable_comp
  exact ⟨Φ, hΦ, hFactor⟩

/-- Helper for Example 26.15: the Brownian path law on `NNReal → ℝ` should be invariant under
global negation. -/
lemma brownianPathLaw_eq_neg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    (μ.map (processPath B)).map (fun y : NNReal → ℝ ↦ -y) =
      μ.map (processPath B) := by
  -- Route correction: isolate the remaining sign-symmetry work as one path-law lemma on
  -- `μ.map (processPath B)`, instead of letting that infinite-dimensional symmetry argument stay
  -- mixed into the fixed-time contradiction proof below.
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Bneg : NNReal → Ω → ℝ := fun t ω ↦ -B t ω
  have hBneg : IsBrownianMotion μ Bneg :=
    neg_isBrownianMotion hB
  have hPathMeas : Measurable (processPath B) := by
    -- Proof comment: deterministic-time measurability of Brownian coordinates gives
    -- measurability of the full raw sample-path map.
    refine measurable_pi_lambda _ fun t ↦ ?_
    exact (hB.stronglyMeasurable t).measurable
  have hPathNegMeas : Measurable (fun y : NNReal → ℝ ↦ -y) := by
    -- Proof comment: raw path negation is measurable because each time coordinate is measurable.
    refine measurable_pi_lambda _ fun t ↦ ?_
    exact measurable_neg.comp (measurable_pi_apply t)
  have hPathNegProcMeas : Measurable (processPath Bneg) := by
    -- Proof comment: the negated Brownian process has the same coordinatewise measurability.
    refine measurable_pi_lambda _ fun t ↦ ?_
    exact (hBneg.stronglyMeasurable t).measurable
  have hRestrictMeas :
      ∀ I : Finset NNReal, Measurable (fun y : NNReal → ℝ ↦ I.restrict y) := by
    intro I
    -- Proof comment: finite restriction is measurable coordinatewise on the product space.
    exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : NNReal)
  have hrestrict :
      ∀ I : Finset NNReal,
        μ.map (fun ω ↦ I.restrict (processPath B ω)) =
          μ.map (fun ω ↦ I.restrict (processPath Bneg ω)) := by
    intro I
    let fB : Ω → I → ℝ := fun ω i ↦ B i ω
    let fBneg : Ω → I → ℝ := fun ω i ↦ Bneg i ω
    have hfB : Measurable fB := by
      exact measurable_pi_lambda _ fun i ↦ (hB.stronglyMeasurable i).measurable
    have hfBneg : Measurable fBneg := by
      exact measurable_pi_lambda _ fun i ↦ (hBneg.stronglyMeasurable i).measurable
    by_cases hI : I.Nonempty
    · let e : Fin ((I.card - 1) + 1) ≃ I :=
        (Fintype.equivFinOfCardEq
          (show Fintype.card I = ((I.card - 1) + 1) by
            simpa using (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 hI)).symm)).symm
      let times : Fin ((I.card - 1) + 1) → NNReal := fun i ↦ (e i : NNReal)
      let gB : Ω → Fin ((I.card - 1) + 1) → ℝ := fun ω i ↦ B (times i) ω
      let gBneg : Ω → Fin ((I.card - 1) + 1) → ℝ := fun ω i ↦ Bneg (times i) ω
      let eπ : (Fin ((I.card - 1) + 1) → ℝ) ≃ᵐ (I → ℝ) :=
        MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e
      have hgB : Measurable gB := by
        exact measurable_pi_lambda _ fun i ↦ (hB.stronglyMeasurable (times i)).measurable
      have hgBneg : Measurable gBneg := by
        exact measurable_pi_lambda _ fun i ↦ (hBneg.stronglyMeasurable (times i)).measurable
      let fullIndex : Finset (Fin ((I.card - 1) + 1)) := Finset.univ
      let eu : fullIndex ≃ Fin ((I.card - 1) + 1) :=
        { toFun := fun i ↦ i.1
          invFun := fun i ↦ ⟨i, by simp [fullIndex]⟩
          left_inv := fun i ↦ by cases i; rfl
          right_inv := fun i ↦ rfl }
      let eAll : (fullIndex → ℝ) ≃ᵐ
          (Fin ((I.card - 1) + 1) → ℝ) :=
        MeasurableEquiv.piCongrLeft (fun _ : Fin ((I.card - 1) + 1) ↦ ℝ) eu
      have hFullBMeas :
          Measurable (fun ω ↦ fullIndex.restrict (fun i ↦ B (times i) ω)) := by
        exact measurable_pi_lambda _ fun i ↦ (hB.stronglyMeasurable (times i.1)).measurable
      have hFullBnegMeas :
          Measurable (fun ω ↦ fullIndex.restrict (fun i ↦ Bneg (times i) ω)) := by
        exact measurable_pi_lambda _ fun i ↦ (hBneg.stronglyMeasurable (times i.1)).measurable
      have hGaussianB :
          IsGaussianProcess (fun i : Fin ((I.card - 1) + 1) ↦ B (times i)) μ :=
        (brownianMotion_isGaussianProcess hB).comp_right times
      have hGaussianBneg :
          IsGaussianProcess (fun i : Fin ((I.card - 1) + 1) ↦ Bneg (times i)) μ :=
        (brownianMotion_isGaussianProcess hBneg).comp_right times
      have hFiniteRestrict :
          μ.map
              (fun ω ↦
                fullIndex.restrict
                  (fun i ↦ B (times i) ω)) =
            μ.map
              (fun ω ↦
                fullIndex.restrict
                  (fun i ↦ Bneg (times i) ω)) := by
        -- Proof comment: the full finite tuple of Brownian coordinates and its negation are
        -- centered Gaussian vectors with the same covariance matrix.
        simpa [times, Bneg] using
          finiteDimensionalDistributions_eq_of_centered_gaussian_covariance
            (X := fun i : Fin ((I.card - 1) + 1) ↦ B (times i))
            (Y := fun i : Fin ((I.card - 1) + 1) ↦ fun ω ↦ Bneg (times i) ω)
            (P := μ)
            (Q := μ)
            hGaussianB
            hGaussianBneg
            (fun i ↦ hB.mean_zero (times i))
            (fun i ↦ hBneg.mean_zero (times i))
            (fun i j ↦ by
              rw [brownianMotion_covariance_eq hB (times i) (times j)]
              rw [brownianMotion_covariance_eq hBneg (times i) (times j)])
            Finset.univ
      have hFinite :
          μ.map gB = μ.map gBneg := by
        -- Proof comment: forget the redundant `Finset.univ` subtype by a measurable equivalence.
        have hCompAllB :
            eAll ∘
                (fun ω ↦
                  fullIndex.restrict
                    (fun i ↦ B (times i) ω)) =
              gB := by
          funext ω
          ext i
          simpa [eAll, gB, times] using
            (MeasurableEquiv.piCongrLeft_apply_apply
              (β := fun _ : Fin ((I.card - 1) + 1) ↦ ℝ)
              eu _ (eu.symm i))
        have hCompAllBneg :
            eAll ∘
                (fun ω ↦
                  fullIndex.restrict
                    (fun i ↦ Bneg (times i) ω)) =
              gBneg := by
          funext ω
          ext i
          simpa [eAll, gBneg, times, Bneg] using
            (MeasurableEquiv.piCongrLeft_apply_apply
              (β := fun _ : Fin ((I.card - 1) + 1) ↦ ℝ)
              eu _ (eu.symm i))
        calc
          μ.map gB
              = (μ.map
                  (fun ω ↦
                    fullIndex.restrict
                      (fun i ↦ B (times i) ω))).map eAll := by
                  rw [Measure.map_map eAll.measurable hFullBMeas]
                  simp [hCompAllB]
          _ = (μ.map
                (fun ω ↦
                  fullIndex.restrict
                    (fun i ↦ Bneg (times i) ω))).map eAll := by
                  exact congrArg (fun ν : Measure _ ↦ ν.map eAll) hFiniteRestrict
          _ = μ.map gBneg := by
                  rw [Measure.map_map eAll.measurable hFullBnegMeas]
                  simp [hCompAllBneg]
      have hCompB : eπ ∘ gB = fB := by
        funext ω
        ext i
        simpa [gB, fB, times] using
          (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : I ↦ ℝ) e (gB ω) (e.symm i))
      have hCompBneg : eπ ∘ gBneg = fBneg := by
        funext ω
        ext i
        simpa [gBneg, fBneg, times, Bneg] using
          (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : I ↦ ℝ) e (gBneg ω) (e.symm i))
      have hRestrictEqB :
          (fun ω ↦ I.restrict (processPath B ω)) = fB := by
        funext ω
        ext i
        rfl
      have hRestrictEqBneg :
          (fun ω ↦ I.restrict (processPath Bneg ω)) = fBneg := by
        funext ω
        ext i
        rfl
      calc
        μ.map (fun ω ↦ I.restrict (processPath B ω))
            = (μ.map gB).map eπ := by
                rw [Measure.map_map eπ.measurable hgB]
                simp [hCompB, hRestrictEqB]
        _ = (μ.map gBneg).map eπ := by
              exact congrArg (fun ν : Measure (Fin ((I.card - 1) + 1) → ℝ) ↦ ν.map eπ) hFinite
        _ = μ.map (fun ω ↦ I.restrict (processPath Bneg ω)) := by
              rw [Measure.map_map eπ.measurable hgBneg]
              simp [hCompBneg, hRestrictEqBneg]
    · have hI0 : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      subst hI0
      have hEmpty :
          (fun ω ↦ (∅ : Finset NNReal).restrict (processPath B ω)) =
            (fun ω ↦ (∅ : Finset NNReal).restrict (processPath Bneg ω)) := by
        funext ω
        exact Subsingleton.elim _ _
      rw [hEmpty]
  have hprojB :
      IsProjectiveLimit
        (μ.map (processPath B))
        (fun I : Finset NNReal ↦
          μ.map (fun ω ↦ I.restrict (processPath B ω))) := by
    -- Proof comment: the full Brownian path law is the projective limit of all its finite
    -- coordinate restrictions.
    exact ProbabilityTheory.isProjectiveLimit_map hPathMeas.aemeasurable
  have hprojBneg :
      IsProjectiveLimit
        (μ.map (processPath Bneg))
        (fun I : Finset NNReal ↦
          μ.map (fun ω ↦ I.restrict (processPath Bneg ω))) := by
    -- Proof comment: the negated Brownian path law has the same projective-limit description.
    exact ProbabilityTheory.isProjectiveLimit_map hPathNegProcMeas.aemeasurable
  have hPathLawEq :
      μ.map (processPath B) = μ.map (processPath Bneg) := by
    -- Proof comment: equality of every finite restriction identifies the whole raw path law by
    -- projective-limit uniqueness on the product sigma algebra.
    have hprojBnegOnB :
        IsProjectiveLimit
          (μ.map (processPath Bneg))
          (fun I : Finset NNReal ↦ μ.map (fun ω ↦ I.restrict (processPath B ω))) := by
      simpa [hrestrict] using hprojBneg
    exact hprojB.unique hprojBnegOnB
  have hNegMap :
      μ.map (processPath Bneg) =
        (μ.map (processPath B)).map (fun y : NNReal → ℝ ↦ -y) := by
    -- Proof comment: negating the Brownian path first or negating the pushed-forward raw path law
    -- afterwards produces the same measure.
    rw [Measure.map_map hPathNegMeas hPathMeas]
    rfl
  calc
    (μ.map (processPath B)).map (fun y : NNReal → ℝ ↦ -y)
        = μ.map (processPath Bneg) := hNegMap.symm
    _ = μ.map (processPath B) := hPathLawEq.symm

/-- Helper for Example 26.15: once the forward identity has already been normalized to the
canonical Itô process, any ambient bracket-density witness for the driver upgrades that canonical
process to an ambient continuous local martingale. -/
lemma signSdeStateLocalMartingale_of_forwardItoEq
    (L : SignSdeWeakSolution)
    {hW : IsContinuousLocalMartingale L.ℱ L.μ (signSdeDriverProcess L.W)}
    (hStateEq :
      signSdeStateProcess L.X =
        continuousLocalMartingaleItoIntegralProcess hW (signSdeIntegrand L.X))
    (hbrW :
      HasAbsolutelyContinuousSquareVariation
        (signSdeDriverProcess L.W)
        hW)
    (hSign_sq :
      ∀ T : NNReal, ∀ᵐ ω ∂L.μ,
        IntegrableOn
          (fun s : ℝ ↦
            (signSdeIntegrand L.X s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbrW s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousLocalMartingale L.ℱ L.μ (signSdeStateProcess L.X) := by
  let Y : NNReal → L.Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hW (signSdeIntegrand L.X)
  have hSign_prog : ProgMeasurable L.ℱ (signSdeIntegrand L.X) :=
    signSdeIntegrand_progMeasurable L
  have hY_upTo :
      ∀ n : ℕ,
        IsContinuousLocalMartingaleUpTo L.ℱ L.μ (fun _ ↦ ((n : NNReal) : ENNReal)) Y := by
    intro n
    -- Proof comment: Chapter 25 already upgrades the canonical dyadic Itô process to a
    -- finite-horizon local martingale once the weighted square-energy clause is available.
    simpa [Y] using
      (Theorem25_22.canonicalItoIntegral_singleClausesUpTo
        (μ := L.μ)
        (ℱ := L.ℱ)
        (M := signSdeDriverProcess L.W)
        (H := signSdeIntegrand L.X)
        (hM := hW)
        (hbr := hbrW)
        (T := (n : NNReal))
        hSign_prog
        (hSign_sq (n : NNReal))).1
  have hY_local :
      IsLocalMartingale L.ℱ L.μ Y := by
    refine (isLocalMartingale_iff L.ℱ L.μ Y).2 ?_
    refine ⟨(hY_upTo 0).adapted, ?_⟩
    refine ⟨fun n _ ↦ ((n : NNReal) : ENNReal), ?_⟩
    refine (isLocalizingSequence_iff L.ℱ L.μ Y (fun n _ ↦ ((n : NNReal) : ENNReal))).2 ?_
    refine ⟨?_, ?_, ?_⟩
    · intro n
      exact isStoppingTime_const L.ℱ (n : NNReal)
    · refine Filter.Eventually.of_forall ?_
      intro ω
      constructor
      · intro m n hmn
        exact_mod_cast hmn
      · simpa using ENNReal.tendsto_nat_nhds_top
    · intro n
      have hMart :
          Martingale
            (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
            L.ℱ
            L.μ := by
        -- Proof comment: specialize the finite-horizon owner at the same deterministic horizon
        -- used by the localizing clock.
        simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
          IsContinuousLocalMartingaleUpTo.martingale_stoppedProcess_minConst_of_upTo
            (ℱ := L.ℱ)
            (μ := L.μ)
            (τ := fun _ ↦ ((n : NNReal) : ENNReal))
            (M := Y)
            (hY_upTo n)
            (n : NNReal)
      refine ⟨hMart, ?_⟩
      -- Proof comment: stopping the already stopped martingale once more at the same horizon
      -- leaves it unchanged, so the standard deterministic-stop UI theorem applies verbatim.
      simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
        (martingaleUniformIntegrable_stoppedProcessConstTime
          (μ := L.μ)
          (ℱ := L.ℱ)
          hMart
          (n : NNReal)).2
  have hY :
      IsContinuousLocalMartingale L.ℱ L.μ Y := by
    refine ⟨hY_local, ?_⟩
    exact (hY_upTo 0).continuous
  -- Proof comment: the normalized forward identity identifies the public state process with the
  -- canonical ambient Itô process just shown to be a continuous local martingale.
  simpa [hStateEq] using hY

/-- Helper for Example 26.15: the scalar weak-solution driver has deterministic square variation
`t ↦ t` on the ambient filtration. -/
lemma signSdeDriverIdentitySquareVariation
    (L : SignSdeWeakSolution) :
    IsContinuousSquareVariationProcess L.ℱ L.μ
      (signSdeDriverProcess L.W)
      (fun t _ ↦ (t : ℝ)) := by
  have hBrownian :
      IsBrownianMotionWithFiltration L.ℱ L.μ L.W := by
    -- Proof comment: repackage the stored Brownian/adapted weak-solution driver into the standard
    -- owner used by the coordinate identity-bracket API.
    simpa [IsBrownianMotionWithFiltration] using L.brownian
  have hCoordIto :
      IsBrownianLocalItoIntegral L.ℱ L.μ
        (signSdeDriverProcess L.W)
        (fun _ _ ↦ (1 : ℝ))
        (signSdeDriverProcess L.W) := by
    -- Proof comment: the only scalar driver coordinate is the constant-one Itô integral of the
    -- ambient one-dimensional Brownian motion.
    simpa [signSdeDriverProcess, CoordinateProcess.toEuclidean] using
      (brownianCoordinate_constOne_isBrownianLocalItoIntegral
        (ℱ := L.ℱ)
        (μ := L.μ)
        (W := L.W.toEuclidean)
        hBrownian.1
        0)
  have hCoordData :
      IsContinuousLocalMartingale L.ℱ L.μ (signSdeDriverProcess L.W) ∧
        IsContinuousSquareVariationProcess L.ℱ L.μ
          (signSdeDriverProcess L.W)
          (MeasureTheory.secondMomentCompensator (fun _ _ ↦ (1 : ℝ))) :=
    brownianLocalItoIntegral_isContinuousLocalMartingale_and_has_squareVariation
      (ℱ := L.ℱ)
      (μ := L.μ)
      hCoordIto
  -- Proof comment: the compensator of the constant-one Brownian coefficient is exactly the
  -- identity clock.
  simpa [MeasureTheory.secondMomentCompensator] using hCoordData.2

/-- Helper for Example 26.15: the ambient state-owner must come from the stored forward identity
`(26.18)`, not from the invalid natural-filtration enlargement route. -/
lemma signSdeWeak_stateLocalMartingale_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L) :
    signSdeWeakForwardIdentity L →
    IsContinuousLocalMartingale L.ℱ L.μ (signSdeStateProcess L.X) := by
  -- Route correction: the reverse Itô identity needs an ambient-filtration martingale owner for
  -- the Brownian state process, so pivot the owner to the actual weak-solution equation rather
  -- than trying to transport a natural-filtration martingale through arbitrary enlargement.
  intro hForward
  obtain ⟨hW, hStateEq⟩ := signSdeWeak_state_eq_forwardIto_of_forward L hX hForward
  have hSign_sq :
      ∀ U : NNReal, ∀ᵐ ω ∂L.μ,
        IntegrableOn
          (fun s : ℝ ↦ (signSdeIntegrand L.X s.toNNReal ω) ^ 2)
          (Set.Icc (0 : ℝ) (U : ℝ)) := by
    intro U
    exact signSdeIntegrand_squareIntegrableUpTo L U
  have hDriverSqVar :
      IsContinuousSquareVariationProcess L.ℱ L.μ
        (signSdeDriverProcess L.W)
        (fun t _ ↦ (t : ℝ)) :=
    signSdeDriverIdentitySquareVariation L
  have hbrW :
      HasAbsolutelyContinuousSquareVariation (signSdeDriverProcess L.W) hW := by
    -- Proof comment: the Brownian driver has unit bracket density, and the square variation is
    -- the deterministic clock `t ↦ t`.
    refine ⟨fun _ _ ↦ (1 : NNReal), fun t _ ↦ (t : ℝ), ?_⟩
    refine ⟨hDriverSqVar, ?_, ?_⟩
    · simpa using
        (stronglyMeasurable_const.progMeasurable :
          ProgMeasurable L.ℱ (fun _ _ : L.Ω ↦ (1 : ℝ)))
    · intro t ω
      simp
  have hDensity_one :
      Theorem25_22.squareVariationDensity hbrW = fun _ _ ↦ (1 : NNReal) := by
    rfl
  have hSign_sq_weighted :
      ∀ U : NNReal, ∀ᵐ ω ∂L.μ,
        IntegrableOn
          (fun s : ℝ ↦
            (signSdeIntegrand L.X s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbrW s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (U : ℝ)) := by
    intro U
    filter_upwards [hSign_sq U] with ω hω
    simpa [hDensity_one] using hω
  -- Proof comment: with the exact ambient driver bracket witness rebuilt on the forward owner,
  -- the existing canonical-Itô local-martingale helper closes the state martingale property.
  exact
    signSdeStateLocalMartingale_of_forwardItoEq
      L
      hStateEq
      hbrW
      hSign_sq_weighted

/-- Helper for Example 26.15: a scalar Brownian motion adapted to `ℱ` can be repackaged as a
one-dimensional Brownian vector process on the same filtration. -/
private lemma scalarBrownian_asOneDimVectorWithFiltration_example2615
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    (hAdapted : Adapted ℱ B) :
    IsBrownianMotionWithFiltration ℱ μ (fun t ω _ : Fin 1 ↦ B t ω) := by
  refine ⟨?_, ?_⟩
  · refine
      { isBrownianMotion := ?_
        iIndepFun := ?_ }
    · intro i
      fin_cases i
      -- Proof comment: the unique coordinate of the one-dimensional vector process is exactly
      -- the original scalar Brownian motion.
      simpa [CoordinateProcess.toEuclidean]
        using hB
    · -- Proof comment: a one-point family of coordinates is independent for cardinality reasons.
      exact iIndepFun.of_subsingleton
  · intro t
    -- Proof comment: adaptedness is checked coordinatewise, and the unique coordinate is the
    -- original scalar process.
    refine measurable_pi_lambda _ ?_
    intro i
    fin_cases i
    simpa using hAdapted t

/-- Helper for Example 26.15: any scalar Brownian motion that is adapted to `ℱ` carries the
deterministic identity bracket on that filtration. -/
private lemma scalarBrownianIdentityBracketData_example2615
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    (hAdapted : Adapted ℱ B) :
    ∃ hM : IsContinuousLocalMartingale ℱ μ B,
      HasAbsolutelyContinuousSquareVariation B hM ∧
        IsContinuousSquareVariationProcess ℱ μ B (fun t _ ↦ (t : ℝ)) := by
  let Bvec : NNReal → Ω → Fin 1 → ℝ := fun t ω _ ↦ B t ω
  have hBvec :
      IsBrownianMotionWithFiltration ℱ μ Bvec :=
    scalarBrownian_asOneDimVectorWithFiltration_example2615 hB hAdapted
  have hCoordIto :
      IsBrownianLocalItoIntegral ℱ μ
        B
        (fun _ _ ↦ (1 : ℝ))
        B := by
    -- Proof comment: the scalar Brownian motion is the constant-one Itô integral of its own
    -- one-dimensional Brownian vector realization.
    simpa [Bvec, CoordinateProcess.toEuclidean] using
      (brownianCoordinate_constOne_isBrownianLocalItoIntegral
        (ℱ := ℱ)
        (μ := μ)
        (W := Bvec.toEuclidean)
        hBvec.1
        0)
  have hCoordData :
      IsContinuousLocalMartingale ℱ μ B ∧
        IsContinuousSquareVariationProcess ℱ μ B
          (MeasureTheory.secondMomentCompensator (fun _ _ ↦ (1 : ℝ))) :=
    brownianLocalItoIntegral_isContinuousLocalMartingale_and_has_squareVariation
      (ℱ := ℱ)
      (μ := μ)
      hCoordIto
  have hBracket :
      HasAbsolutelyContinuousSquareVariation B hCoordData.1 := by
    refine ⟨fun _ _ ↦ (1 : NNReal), fun t _ ↦ (t : ℝ), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · -- Proof comment: the canonical square variation of the constant-one Brownian Itô integral
      -- is exactly the deterministic clock.
      simpa [MeasureTheory.secondMomentCompensator] using hCoordData.2
    · -- Proof comment: the bracket density is the constant function `1`.
      simpa using
        (stronglyMeasurable_const.progMeasurable :
          ProgMeasurable ℱ (fun _ _ : Ω ↦ (1 : ℝ)))
    · intro t ω
      simp
  have hSquareVariation :
      IsContinuousSquareVariationProcess ℱ μ B (fun t _ ↦ (t : ℝ)) := by
    -- Proof comment: the public square-variation witness is the same compensator after
    -- rewriting `∫_0^t 1 ds` as `t`.
    simpa [MeasureTheory.secondMomentCompensator] using hCoordData.2
  exact ⟨hCoordData.1, hBracket, hSquareVariation⟩

/-- Helper for Example 26.15: once the forward identity supplies the ambient local-martingale
owner for the Brownian state process, the state bracket is still the deterministic clock. -/
lemma signSdeWeak_stateIdentitySquareVariation_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L) :
    IsContinuousSquareVariationProcess L.ℱ L.μ
      (signSdeStateProcess L.X)
      (fun t _ ↦ (t : ℝ)) := by
  rcases
      scalarBrownianIdentityBracketData_example2615
        (μ := L.μ)
        (ℱ := L.ℱ)
        (B := signSdeStateProcess L.X)
        hX
        (signSdeStateProcess_adapted L) with
    ⟨_, _, hSquareVariation⟩
  -- Proof comment: Brownianity determines the state bracket, independent of which ambient local
  -- martingale witness is later used for the same process.
  exact hSquareVariation

/-- Helper for Example 26.15: the ambient Brownian-state local-martingale witness from the
forward identity carries an absolutely continuous bracket with density `1`. -/
lemma signSdeWeak_stateAbsolutelyContinuousSquareVariation_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L) :
    HasAbsolutelyContinuousSquareVariation
      (signSdeStateProcess L.X)
      (signSdeWeak_stateLocalMartingale_of_forward L hX hForward) := by
  rcases
      scalarBrownianIdentityBracketData_example2615
        (μ := L.μ)
        (ℱ := L.ℱ)
        (B := signSdeStateProcess L.X)
        hX
        (signSdeStateProcess_adapted L) with
    ⟨_, hBracket, _⟩
  -- Proof comment: the bracket witness depends only on the Brownian state path itself; the
  -- forward equation is used only to pick the ambient local-martingale proof term.
  simpa using hBracket

/-- Helper for Example 26.15: the bundled absolute state past up to time `T` is measurable for
the deterministic-time absolute-state filtration. -/
lemma measurable_absStatePastPathAt
    (L : SignSdeWeakSolution) (T : NNReal) :
    Measurable[processFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|) T]
      (fun ω u : Set.Iic T ↦ |signSdeStateProcess L.X u ω|) := by
  let pastPath : L.Ω → Set.Iic T → ℝ := fun ω u ↦ |signSdeStateProcess L.X u ω|
  have hPastAmbient : Measurable pastPath := by
    -- Proof comment: every coordinate of the bundled absolute past path is an ambient measurable
    -- deterministic-time state slice.
    refine measurable_pi_lambda _ fun u ↦ ?_
    exact
      measurable_abs.comp <|
        Measurable.mono (signSdeStateProcess_adapted L u) (L.ℱ.le u) le_rfl
  have hPastGenerated :
      Measurable[generatedFiltrationSpace (fun t ω ↦ |signSdeStateProcess L.X t ω|) T] pastPath := by
    -- Proof comment: each history coordinate `u ≤ T` is one of the generators of the absolute
    -- state filtration up to time `T`.
    rw [@measurable_pi_iff]
    intro u
    refine Measurable.of_comap_le ?_
    exact
      le_iSup_of_le (u : NNReal) <|
        le_iSup_of_le u.2 le_rfl
  -- Proof comment: `processFiltration` is the ambient measurable space intersected with the
  -- generated time-`T` history sigma-algebra, so the past-path map is measurable for it.
  refine Measurable.of_comap_le ?_
  exact le_inf hPastAmbient.comap_le hPastGenerated.comap_le

/-- Helper for Example 26.15: once the fixed-time driver slice is measurable from the absolute
state history up to time `t`, Doob-Dynkin factors it through the bundled absolute past path. -/
lemma signSdeDriverSlice_factorThroughAbsPast
    (L : SignSdeWeakSolution)
    (t : NNReal)
    (hMeas :
      Measurable[processFiltration (fun s ω ↦ |signSdeStateProcess L.X s ω|) t]
        (signSdeDriverProcess L.W t)) :
    ∃ Φ : (Set.Iic t → ℝ) → ℝ, Measurable Φ ∧
      signSdeDriverProcess L.W t =
        Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|) := by
  -- Proof comment: the general absolute-past factorization lemma already packages any
  -- deterministic-time observable measurable for the absolute-state filtration.
  simpa using
    absPastPathFactorizationAtTime
      (B := signSdeStateProcess L.X)
      (T := t)
      hMeas

/-- Helper for Example 26.15: if two continuous local martingales share the same square-variation
witness and the same quadratic-covariation witness, then their difference has zero square
variation. -/
private lemma sub_zeroSquareVariation_of_sharedWitness_example2615
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N A : NNReal → Ω → ℝ}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A) :
    IsContinuousSquareVariationProcess ℱ μ
      (fun t ω ↦ M t ω - N t ω)
      (fun _ _ ↦ (0 : ℝ)) := by
  refine
    { zero := ?_
      adapted := ?_
      continuous := ?_
      monotone := ?_
      local_martingale_sq_sub := ?_ }
  · -- Proof comment: the zero bracket witness starts from `0` by definition.
    funext ω
    simp
  · -- Proof comment: the zero bracket witness is adapted at every deterministic time.
    intro t
    simpa using (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
  · -- Proof comment: the zero bracket witness is pathwise continuous.
    intro ω
    simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  · -- Proof comment: the zero bracket witness is monotone because it is constant.
    intro ω s t hst
    simp
  · refine
      { local_martingale := ?_
        continuous := ?_ }
    · -- Proof comment: expand `(M - N)^2` into the shared-witness combination
      -- `(M^2 - A) + (N^2 - A) - 2 * (MN - A)`.
      convert
        (hAleft.local_martingale_sq_sub.add
          (hAright.local_martingale_sq_sub.sub
            ((hQuad.local_martingale_mul_sub.const_mul (2 : ℝ)).local_martingale))) using 1
      funext t ω
      ring
    · -- Proof comment: the same algebraic decomposition preserves pathwise continuity.
      intro ω
      exact
        (hAleft.local_martingale_sq_sub.continuous ω).add
          ((hAright.local_martingale_sq_sub.continuous ω).sub
            ((hQuad.local_martingale_mul_sub.const_mul (2 : ℝ)).continuous ω))

/-- Helper for Example 26.15: a continuous local martingale with identically zero square
variation is almost surely `0` at every deterministic time once it starts from `0`. -/
private lemma ae_eq_zero_at_time_of_zeroSquareVariation_example2615
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hXsq : IsContinuousSquareVariationProcess ℱ μ X (fun _ _ ↦ (0 : ℝ)))
    (hX0 : X 0 =ᵐ[μ] fun _ : Ω ↦ 0)
    (T : NNReal) :
    X T =ᵐ[μ] fun _ : Ω ↦ 0 := by
  rcases existsUnique_continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hX with
    ⟨B, hB, huniq⟩
  have hCanonEqB :
      AreIndistinguishable μ (⟨X⟩[hX]) B := by
    exact huniq _ (continuousSquareVariationProcess_spec hX)
  have hBEqZero :
      AreIndistinguishable μ B (fun _ _ ↦ (0 : ℝ)) := by
    exact huniq _ hXsq
  have hCanonEqZero :
      AreIndistinguishable μ (⟨X⟩[hX]) (fun _ _ ↦ (0 : ℝ)) := by
    exact areIndistinguishable_trans hCanonEqB hBEqZero
  have hZeroAllTimes :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, (⟨X⟩[hX]) t ω = 0 := by
    rcases hCanonEqZero with ⟨bad, hbad_meas, hbad_null, hbad_sub⟩
    have hbad_ae : ∀ᵐ ω ∂μ, ω ∉ bad :=
      compl_mem_ae_iff.mpr hbad_null
    filter_upwards [hbad_ae] with ω hωbad t
    by_contra hneq
    exact hωbad (hbad_sub t hneq)
  have hConstAtTime :
      X T =ᵐ[μ] X 0 :=
    ae_eq_initial_at_time_of_ae_squareVariation_eq_zero ℱ hX hZeroAllTimes T
  -- Proof comment: once the process is almost surely constant in time, the zero initial value
  -- forces the fixed-time value to vanish.
  exact hConstAtTime.trans hX0

/-- Helper for Example 26.15: deterministic stopped martingale owners for all horizons recover a
genuine continuous local martingale. -/
private theorem isContinuousLocalMartingale_of_constStoppedMartingale_example2615
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {Y : NNReal → Ω → ℝ}
    (hY_adapted : Adapted ℱ Y)
    (hY_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω)
    (hStopped :
      ∀ T : NNReal, Martingale (stoppedProcess Y (fun _ ↦ (T : ENNReal))) ℱ μ) :
    IsContinuousLocalMartingale ℱ μ Y := by
  refine
    { local_martingale := ?_
      continuous := hY_cont }
  refine (isLocalMartingale_iff ℱ μ Y).2 ⟨hY_adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ Y (fun n _ ↦ (n : ENNReal))).2 ⟨?_, ?_, ?_⟩
  · intro n
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    -- Proof comment: the deterministic horizons `n` increase pointwise to `∞`.
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    have hMart :
        Martingale (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ :=
      hStopped n
    have hUI :
        UniformIntegrable
          (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          1
          μ := by
      have hDet :
          Martingale
              (stoppedProcess
                (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
                (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ ∧
            UniformIntegrable
              (stoppedProcess
                (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
                (fun _ ↦ ((n : NNReal) : ENNReal))) 1 μ :=
        martingaleUniformIntegrable_stoppedProcessConstTime
          (ℱ := ℱ)
          (μ := μ)
          (X := stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          hMart
          (n : NNReal)
      -- Proof comment: stopping again at the same deterministic horizon does not change the
      -- process, so the uniform-integrability clause descends directly.
      simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using hDet.2
    exact ⟨hMart, hUI⟩

/-- Helper for Example 26.15: equality up to a deterministic horizon survives stopping both
processes at that same horizon, because the stopped time is always a point `≤ T`. -/
private theorem eqUpTo_stoppedProcess_const_example2615
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {α : Type*} {T U : NNReal} {X Y : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) :
    EqUpTo μ U
      (stoppedProcess X (fun _ ↦ (T : ENNReal)))
      (stoppedProcess Y (fun _ ↦ (T : ENNReal))) := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro t ht ω hω
  have hmin : min t T ≤ T := min_le_right _ _
  -- Proof comment: after deterministic stopping at `T`, every visible sample is evaluated at
  -- time `min t T`, so the original `EqUpTo` witness still applies.
  exact hN_sub hmin (by simpa [stoppedProcessConstTime_eq_min] using hω)

/-- Helper for Example 26.15: a square-variation witness up to `T` can be stopped at `T` and then
reused as a square-variation witness up to any comparison horizon. -/
private theorem stoppedSquareVariationProcessUpTo_const_example2615
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {T U : NNReal} {N A : NNReal → Ω → ℝ}
    (hNA : IsContinuousSquareVariationProcessUpTo ℱ μ T N A) :
    IsContinuousSquareVariationProcessUpTo ℱ μ U
      (stoppedProcess N (fun _ ↦ (T : ENNReal)))
      (stoppedProcess A (fun _ ↦ (T : ENNReal))) := by
  rcases hNA with ⟨N', A', hNA', hEqN, hEqA⟩
  have hStopped :
      IsContinuousSquareVariationProcess ℱ μ
        (stoppedProcess N' (fun _ ↦ (T : ENNReal)))
        (stoppedProcess A' (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: once the owner pair is genuine, Theorem 21.75 preserves the square
    -- variation package under deterministic stopping.
    exact
      stoppedSquareVariationProcess
        (ℱ := ℱ)
        (μ := μ)
        hNA'
        (isStoppingTime_const ℱ T)
  -- Proof comment: transport the stopped genuine witness back to the visible stopped processes
  -- using the stopped `EqUpTo` comparisons on both coordinates.
  exact
    isContinuousSquareVariationProcessUpTo_of_eqUpTo
      (μ := μ)
      (ℱ := ℱ)
      (eqUpTo_stoppedProcess_const_example2615
        (μ := μ) (T := T) (U := U) hEqN)
      (eqUpTo_stoppedProcess_const_example2615
        (μ := μ) (T := T) (U := U) hEqA)
      (isContinuousSquareVariationProcessUpTo_of_isContinuousSquareVariationProcess
        (μ := μ)
        (ℱ := ℱ)
        (T := U)
        hStopped)

/-- Helper for Example 26.15: a zero quadratic-covariation witness up to `T` upgrades to a
genuine zero witness after deterministically stopping both coordinates at `T`. -/
private theorem stoppedZeroQuadraticCovariation_of_upTo_example2615
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {T : NNReal} {M N : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hUpTo : IsContinuousQuadraticCovariationProcessUpTo ℱ μ T M N 0) :
    IsContinuousQuadraticCovariationProcess ℱ μ
      (stoppedProcess M (fun _ ↦ (T : ENNReal)))
      (stoppedProcess N (fun _ ↦ (T : ENNReal)))
      0 := by
  let σ : Ω → ENNReal := fun _ ↦ (T : ENNReal)
  have hσ : IsStoppingTime ℱ σ := by
    simpa [σ] using isStoppingTime_const ℱ T
  rcases hUpTo with ⟨Mw, Nw, Aw, hMwNwAw, hEqMw, hEqNw, hEqAw⟩
  have hStoppedDriver :
      IsLocalMartingale ℱ μ
        (stoppedProcess (fun t ω ↦ Mw t ω * Nw t ω - Aw t ω) σ) := by
    -- Proof comment: deterministically stopping the genuine compensated-product witness preserves
    -- its local-martingale property.
    exact
      _root_.ProbabilityTheory.isLocalMartingale_stoppedProcess
        hMwNwAw.local_martingale_mul_sub.local_martingale
        hMwNwAw.local_martingale_mul_sub.continuous
        hσ
  have hStoppedMAdapted : Adapted ℱ (stoppedProcess M σ) :=
    (hM.adapted.stronglyAdapted.stoppedProcess hM.continuous hσ).adapted
  have hStoppedNAdapted : Adapted ℱ (stoppedProcess N σ) :=
    (hN.adapted.stronglyAdapted.stoppedProcess hN.continuous hσ).adapted
  have hStoppedTargetAdapted :
      Adapted ℱ
        (fun t ω ↦
          stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ)) := by
    exact
      (hStoppedMAdapted.mul hStoppedNAdapted).sub
        (adapted_const' ℱ (fun _ : NNReal ↦ (0 : ℝ)))
  have hStoppedTargetCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦
        stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ) := by
    intro ω
    -- Proof comment: deterministic stopping preserves continuity of both coordinates, so their
    -- stopped product remains continuous.
    exact
      ((continuous_stoppedProcess_of_continuous hM.continuous ω).mul
        (continuous_stoppedProcess_of_continuous hN.continuous ω)).sub
        (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEqMw with
    ⟨SMw, hSMwMeas, hSMwNull, hSMwEq⟩
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEqNw with
    ⟨SNw, hSNwMeas, hSNwNull, hSNwEq⟩
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEqAw with
    ⟨SAw, hSAwMeas, hSAwNull, hSAwEq⟩
  have hStoppedEq :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        stoppedProcess (fun t ω ↦ Mw t ω * Nw t ω - Aw t ω) σ t ω =
          (stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ)) := by
    let S : Set Ω := (SMw ∪ SNw) ∪ SAw
    have hSnull : μ S = 0 := by
      have hLeftNull : μ (SMw ∪ SNw) = 0 := by
        have hUnionLe : μ (SMw ∪ SNw) ≤ μ SMw + μ SNw := measure_union_le SMw SNw
        refine le_antisymm ?_ bot_le
        simpa [hSMwNull, hSNwNull] using hUnionLe
      have hUnionLe : μ ((SMw ∪ SNw) ∪ SAw) ≤ μ (SMw ∪ SNw) + μ SAw :=
        measure_union_le (SMw ∪ SNw) SAw
      refine le_antisymm ?_ bot_le
      simpa [S, hLeftNull, hSAwNull] using hUnionLe
    refine ae_iff.2 ?_
    refine measure_mono_null ?_ hSnull
    intro ω hω
    have hωMw : ω ∉ SMw := by
      exact fun hSMwω ↦ hω (Set.mem_union_left SAw (Set.mem_union_left SNw hSMwω))
    have hωNw : ω ∉ SNw := by
      exact fun hSNwω ↦ hω (Set.mem_union_left SAw (Set.mem_union_right SMw hSNwω))
    have hωAw : ω ∉ SAw := by
      exact fun hSAwω ↦ hω (Set.mem_union_right (SMw ∪ SNw) hSAwω)
    intro t
    have hMwStopped :
        stoppedProcess Mw σ t ω = stoppedProcess M σ t ω := by
      have hEq : Mw (min t T) ω = M (min t T) ω :=
        hSMwEq (min_le_right _ _) hωMw
      simpa [σ, stoppedProcessConstTime_eq_min] using hEq
    have hNwStopped :
        stoppedProcess Nw σ t ω = stoppedProcess N σ t ω := by
      have hEq : Nw (min t T) ω = N (min t T) ω :=
        hSNwEq (min_le_right _ _) hωNw
      simpa [σ, stoppedProcessConstTime_eq_min] using hEq
    have hAwStopped :
        stoppedProcess Aw σ t ω = 0 := by
      have hEq : Aw (min t T) ω = 0 := hSAwEq (min_le_right _ _) hωAw
      simpa [σ, stoppedProcessConstTime_eq_min] using hEq
    calc
      stoppedProcess (fun t ω ↦ Mw t ω * Nw t ω - Aw t ω) σ t ω =
          stoppedProcess Mw σ t ω * stoppedProcess Nw σ t ω - stoppedProcess Aw σ t ω := by
        simp [σ, stoppedProcess]
      _ = stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ) := by
        rw [hMwStopped, hNwStopped, hAwStopped]
  refine
    { zero := by
        funext ω
        simp [σ, stoppedProcess]
      adapted := by
        intro t
        exact (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
      continuous := by
        intro ω
        exact (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
      locally_finite_variation := zeroProcess_locallyFiniteVariation (μ := μ)
      local_martingale_mul_sub := by
        -- Proof comment: after stopping, the compensated-product witness agrees almost surely at
        -- all times with the target stopped product because the compensator coordinate is
        -- `EqUpTo` to `0`.
        exact
          isLocalMartingale_congr_ae_allTimes
            hStoppedDriver
            hStoppedTargetAdapted
            hStoppedTargetCont
            hStoppedEq }

/-- Helper for Example 26.15: two continuous local martingales with the same square-variation and
quadratic-covariation witnesses agree almost surely at every fixed deterministic time once they
agree at time `0`. -/
private lemma fixedTimeAeEq_ofSharedWitness_example2615
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
    {M N A : NNReal → Ω → ℝ}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A)
    (hZero : M 0 =ᵐ[μ] N 0)
    (T : NNReal) :
    M T =ᵐ[μ] N T := by
  have hSubSq :
      IsContinuousSquareVariationProcess ℱ μ
        (fun t ω ↦ M t ω - N t ω)
        (fun _ _ ↦ (0 : ℝ)) :=
    sub_zeroSquareVariation_of_sharedWitness_example2615
      hMmart hNmart hAleft hAright hQuad
  have hSubZero :
      (fun ω ↦ M 0 ω - N 0 ω) =ᵐ[μ] fun _ : Ω ↦ 0 := by
    -- Proof comment: the shared initial-value hypothesis turns the difference process into a
    -- zero-start continuous local martingale.
    filter_upwards [hZero] with ω hω
    simp [hω]
  have hSubAtTime :
      (fun ω ↦ M T ω - N T ω) =ᵐ[μ] fun _ : Ω ↦ 0 :=
    ae_eq_zero_at_time_of_zeroSquareVariation_example2615
      (ℱ := ℱ)
      (μ := μ)
      (X := fun t ω ↦ M t ω - N t ω)
      (hMmart.sub hNmart)
      hSubSq
      hSubZero
      T
  -- Proof comment: vanishing of the difference at time `T` is exactly the desired endpoint
  -- equality.
  filter_upwards [hSubAtTime] with ω hω
  exact sub_eq_zero.mp hω

/-- Helper for Example 26.15: once a fixed-time driver slice factors through the absolute past
and agrees with the reverse Itô slice, both slices share that same absolute-past factor map. -/
lemma signSdeCommonAbsHistorySliceFormulaAt_of_factorization
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal)
    (hFactor :
      ∃ Φ : (Set.Iic t → ℝ) → ℝ, Measurable Φ ∧
        signSdeDriverProcess L.W t =
          Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|))
    (hEq :
      signSdeDriverProcess L.W t =
        fun ω ↦
          continuousLocalMartingaleItoIntegralProcess
            (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
            (signSdeIntegrand L.X) t ω) :
    ∃ Φ : (Set.Iic t → ℝ) → ℝ, Measurable Φ ∧
      signSdeDriverProcess L.W t =
        Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|) ∧
      (fun ω ↦
        continuousLocalMartingaleItoIntegralProcess
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
          (signSdeIntegrand L.X) t ω) =
        Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|) := by
  rcases hFactor with ⟨Φ, hΦ, hDriver⟩
  refine ⟨Φ, hΦ, hDriver, ?_⟩
  -- Proof comment: rewrite the reverse Itô slice through the already factored driver slice.
  exact hEq.symm.trans hDriver

/-- Helper for Example 26.15: the source smooth-even route naturally factors the reverse Itô
slice through the absolute-value state past first, and the driver slice then inherits the same
factorization by the separate fixed-time reverse equality. -/
lemma signSdeCommonAbsHistorySliceFormulaAt_of_reverseFactorization
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal)
    (hFactor :
      ∃ Φ : (Set.Iic t → ℝ) → ℝ, Measurable Φ ∧
        (fun ω ↦
          continuousLocalMartingaleItoIntegralProcess
            (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
            (signSdeIntegrand L.X) t ω) =
          Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|))
    (hEq :
      signSdeDriverProcess L.W t =
        fun ω ↦
          continuousLocalMartingaleItoIntegralProcess
            (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
            (signSdeIntegrand L.X) t ω) :
    ∃ Φ : (Set.Iic t → ℝ) → ℝ, Measurable Φ ∧
      signSdeDriverProcess L.W t =
        Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|) ∧
      (fun ω ↦
        continuousLocalMartingaleItoIntegralProcess
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
          (signSdeIntegrand L.X) t ω) =
        Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|) := by
  rcases hFactor with ⟨Φ, hΦ, hReverse⟩
  refine ⟨Φ, hΦ, ?_, hReverse⟩
  -- Proof comment: transport the reverse-slice factorization across the fixed-time driver/reverse
  -- equality instead of reproving driver measurability from scratch.
  exact hEq.trans hReverse

/-- Helper for Example 26.15: the normalized forward identity rewrites each fixed-time state slice
as the dyadic pathwise Itô integral of `sign(X)` against the driver path. -/
lemma signSdeStateSlice_eq_pathwiseDriverIntegral_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal) (ω : L.Ω) :
    let hW := (signSdeWeak_state_eq_forwardIto_of_forward L hX hForward).choose
    signSdeStateProcess L.X t ω =
      pathwiseItoIntegralAlong
        (fun s ↦ signSdeIntegrand L.X s ω)
        (⟨fun s ↦ signSdeDriverProcess L.W s ω,
          hW.continuous ω⟩ :
          C(NNReal, ℝ))
        Definition2158.dyadicPartitionSequence
        t := by
  let hW := (signSdeWeak_state_eq_forwardIto_of_forward L hX hForward).choose
  have hStateEq :
      signSdeStateProcess L.X =
        continuousLocalMartingaleItoIntegralProcess hW (signSdeIntegrand L.X) :=
    (signSdeWeak_state_eq_forwardIto_of_forward L hX hForward).choose_spec
  -- Proof comment: `continuousLocalMartingaleItoIntegralProcess` is already the canonical
  -- pathwise Itô integral of the driver path, so the normalized forward identity is exactly this
  -- pointwise pathwise formula.
  simpa [continuousLocalMartingaleItoIntegralProcess] using hStateEq t ω

/-- Helper for Example 26.15: the reverse fixed-time slice is definitionally the dyadic pathwise
Itô integral of `sign(X)` against the state path. -/
lemma signSdeReverseItoSlice_eq_pathwiseStateIntegral_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal) (ω : L.Ω) :
    continuousLocalMartingaleItoIntegralProcess
        (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
        (signSdeIntegrand L.X) t ω =
      pathwiseItoIntegralAlong
        (fun s ↦ signSdeIntegrand L.X s ω)
        (⟨fun s ↦ signSdeStateProcess L.X s ω,
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward).continuous ω⟩ :
          C(NNReal, ℝ))
        Definition2158.dyadicPartitionSequence
        t := by
  -- Proof comment: unfold the canonical continuous-local-martingale Itô process at the fixed
  -- sample `ω`; no stochastic transport remains at this stage.
  rfl

/-- Helper for Example 26.15: the remaining reverse-slice frontier is deterministic-time
measurability with respect to the absolute-value state history. -/
private theorem signSdeReverseItoSlice_measurableAbsPastAt_example2615
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal) :
    Measurable[processFiltration (fun s ω ↦ |signSdeStateProcess L.X s ω|) t]
      (fun ω ↦
        continuousLocalMartingaleItoIntegralProcess
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
          (signSdeIntegrand L.X) t ω) := by
  by_cases ht : t = 0
  · -- Proof comment: at time `0` the reverse Itô slice is identically `0`.
    simpa [ht] using
      (measurable_const :
        Measurable[processFiltration (fun s ω ↦ |signSdeStateProcess L.X s ω|) t]
          (fun _ : L.Ω ↦ (0 : ℝ)))
  -- Route correction: keep the remaining gap as a single deterministic Tanaka/approximation
  -- theorem in the fixed-time pathwise normal form.
  -- TODO: rewrite the reverse slice with
  -- `signSdeReverseItoSlice_eq_pathwiseStateIntegral_of_forward`, then prove that the resulting
  -- dyadic pathwise integral depends measurably only on the absolute past `u ↦ |X_u|` on `[0, t]`.
  sorry

/-- Helper for Example 26.15: the fixed-time reverse Itô slice is the first shared normal form
that still needs the smooth-even approximation route. -/
lemma signSdeReverseItoSlice_factorThroughAbsPastAt_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal) :
    ∃ Φ : (Set.Iic t → ℝ) → ℝ, Measurable Φ ∧
      (fun ω ↦
        continuousLocalMartingaleItoIntegralProcess
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
          (signSdeIntegrand L.X) t ω) =
        Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|) := by
  -- Proof comment: the abstract factorization is already available once the reverse slice is
  -- known to be measurable for the absolute-state history at time `t`.
  exact
    absPastPathFactorizationAtTime
      (B := signSdeStateProcess L.X)
      (T := t)
      (signSdeReverseItoSlice_measurableAbsPastAt_example2615 L hX hForward t)

/-- Helper for Example 26.15: after normalizing both sides to canonical fixed-time Itô
realizations, the remaining equality is the deterministic pathwise involution frontier. -/
private theorem signSdeReverseItoSliceEq_driverAt_pathwise_example2615
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal) :
    signSdeDriverProcess L.W t =
      fun ω ↦
        continuousLocalMartingaleItoIntegralProcess
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
          (signSdeIntegrand L.X) t ω := by
  by_cases ht : t = 0
  · funext ω
    have hDriverZero : signSdeDriverProcess L.W 0 ω = 0 := by
      simpa using congrFun (signSdeDriverProcess_isBrownian L).zero ω
    simp [ht, hDriverZero]
  have hStateMart :
      IsContinuousLocalMartingale L.ℱ L.μ (signSdeStateProcess L.X) :=
    signSdeWeak_stateLocalMartingale_of_forward L hX hForward
  have hStateBr :
      HasAbsolutelyContinuousSquareVariation
        (signSdeStateProcess L.X)
        hStateMart :=
    signSdeWeak_stateAbsolutelyContinuousSquareVariation_of_forward L hX hForward
  obtain ⟨hDriverMart, hDriverOwner⟩ := signSdeDriver_selfItoOwner L
  have hUnitProg :
      ProgMeasurable L.ℱ (fun _ _ : L.Ω ↦ (1 : ℝ)) := by
    simpa using
      (stronglyMeasurable_const.progMeasurable :
        ProgMeasurable L.ℱ (fun _ _ : L.Ω ↦ (1 : ℝ)))
  have hUnitSq :
      ∀ᵐ ω ∂L.μ,
        IntegrableOn
          (fun s : ℝ ↦
            ((1 : ℝ) ^ 2) *
              (Theorem25_22.squareVariationDensity
                (signSdeDriver_hasAbsolutelyContinuousSquareVariation
                  (L := L) (hW := hDriverMart)) s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (t : ℝ)) := by
    filter_upwards with ω
    simpa using
      (integrableOn_const.2 measure_Icc_lt_top.ne :
        IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Icc (0 : ℝ) (t : ℝ)))
  have hSignProg :
      ProgMeasurable L.ℱ (signSdeIntegrand L.X) :=
    signSdeIntegrand_progMeasurable L
  have hSignSq :
      ∀ᵐ ω ∂L.μ,
        IntegrableOn
          (fun s : ℝ ↦
            (signSdeIntegrand L.X s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hStateBr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (t : ℝ)) := by
    simpa using signSdeIntegrand_squareIntegrableUpTo L t
  let R : NNReal → L.Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess
      hStateMart
      (signSdeIntegrand L.X)
  have hPair :=
    Theorem25_22.pair_spec
      (μ := L.μ)
      (ℱ := L.ℱ)
      (M₁ := signSdeDriverProcess L.W)
      (M₂ := signSdeStateProcess L.X)
      (H₁ := fun _ _ ↦ (1 : ℝ))
      (H₂ := signSdeIntegrand L.X)
      (N₁ := signSdeDriverProcess L.W)
      (N₂ := R)
      (hM₁ := hDriverMart)
      (hM₂ := hStateMart)
      (hbr₁ := signSdeDriver_hasAbsolutelyContinuousSquareVariation
        (L := L) (hW := hDriverMart))
      (hbr₂ := hStateBr)
      t
      hUnitProg
      hSignProg
      hUnitSq
      hSignSq
      hDriverOwner
      (Theorem25_22.canonicalSelf
        (μ := L.μ)
        (ℱ := L.ℱ)
        (M := signSdeStateProcess L.X)
        (H := signSdeIntegrand L.X)
        (hM := hStateMart)
        (hbr := hStateBr))
  have hSqOneNull :
      ∀ᵐ ω ∂L.μ,
        (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ)))
          {s : ℝ | (signSdeIntegrand L.X s.toNNReal ω) ^ 2 ≠ 1} = 0 :=
    signSdeIntegrand_sq_ne_one_measureOnIoc_eq_zero L hX (lt_of_le_of_ne bot_le (Ne.symm ht))
  let _ := hPair
  let _ := hSqOneNull
  -- Route correction: `pair_spec` only gives horizonwise `EqUpTo` information, while the present
  -- theorem asks for an exact fixed-time equality of the canonical pathwise realizations.
  -- TODO: use `signSdeStateSlice_eq_pathwiseDriverIntegral_of_forward` and
  -- `signSdeReverseItoSlice_eq_pathwiseStateIntegral_of_forward` to reduce to a deterministic
  -- dyadic pathwise involution theorem under the square-one coefficient `sign(X)`.
  sorry

/-- Helper for Example 26.15: the exact driver/reverse equality should be closed separately from
the Tanaka factorization by replacing `(sign X)^2` with `1` on deterministic horizons. -/
lemma signSdeReverseItoSliceEq_driverAt_of_forward_sqOne
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal) :
    signSdeDriverProcess L.W t =
      fun ω ↦
        continuousLocalMartingaleItoIntegralProcess
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
          (signSdeIntegrand L.X) t ω := by
  exact signSdeReverseItoSliceEq_driverAt_pathwise_example2615 L hX hForward t

/-- Helper for Example 26.15: the shared fixed-time Tanaka/Itô normal form is now just the short
assembly of the reverse-factorization frontier with the separate exact equality frontier. -/
lemma signSdeCommonTanakaSliceFormulaAt_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal) :
    ∃ Φ : (Set.Iic t → ℝ) → ℝ, Measurable Φ ∧
      signSdeDriverProcess L.W t =
        Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|) ∧
      (fun ω ↦
        continuousLocalMartingaleItoIntegralProcess
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
          (signSdeIntegrand L.X) t ω) =
        Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|) := by
  have hFactor :=
    signSdeReverseItoSlice_factorThroughAbsPastAt_of_forward L hX hForward t
  have hEq :=
    signSdeReverseItoSliceEq_driverAt_of_forward_sqOne L hX hForward t
  -- Proof comment: once the reverse slice factors through the absolute past and the driver slice
  -- is identified with that reverse slice, the public common-factor package is immediate.
  exact
    signSdeCommonAbsHistorySliceFormulaAt_of_reverseFactorization
      L hX hForward t hFactor hEq

/-- Helper for Example 26.15: the fixed-time driver slice should equal the reverse Itô slice once
the forward identity has already normalized the state process. -/
lemma signSdeDriverSliceEq_reverseItoAt_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal) :
    signSdeDriverProcess L.W t =
      fun ω ↦
        continuousLocalMartingaleItoIntegralProcess
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
          (signSdeIntegrand L.X) t ω := by
  -- Proof comment: keep the old local API name, but delegate the actual stochastic work to the
  -- dedicated square-one frontier.
  exact signSdeReverseItoSliceEq_driverAt_of_forward_sqOne L hX hForward t

/-- Helper for Example 26.15: under the forward identity, both the fixed-time driver slice and
the reverse Itô slice should factor through the same measurable absolute-state past up to time
`t`. -/
lemma signSdeCommonAbsHistorySliceFormulaAt_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (t : NNReal) :
    ∃ Φ : (Set.Iic t → ℝ) → ℝ, Measurable Φ ∧
      signSdeDriverProcess L.W t =
        Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|) ∧
      (fun ω ↦
        continuousLocalMartingaleItoIntegralProcess
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
          (signSdeIntegrand L.X) t ω) =
        Φ ∘ (fun ω u ↦ |signSdeStateProcess L.X u ω|) := by
  -- Proof comment: the public common-factor statement is now exactly the new shared fixed-time
  -- Tanaka normal form, kept under the old name for downstream callers.
  exact signSdeCommonTanakaSliceFormulaAt_of_forward L hX hForward t

/-- Helper for Example 26.15: under the forward identity, each deterministic driver slice should
agree with the reverse Itô slice against the Brownian state process. -/
lemma signSdeWeakDriverSliceEq_reverseIto_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L) :
    ∀ t ω,
      signSdeDriverProcess L.W t ω =
        continuousLocalMartingaleItoIntegralProcess
          (signSdeWeak_stateLocalMartingale_of_forward L hX hForward)
          (signSdeIntegrand L.X) t ω := by
  intro t ω
  -- Proof comment: the reverse identity only needs the exact fixed-time stochastic bridge, so
  -- use that bridge directly instead of routing through the separate abs-history factorization.
  exact congrFun (signSdeDriverSliceEq_reverseItoAt_of_forward L hX hForward t) ω

/-- Helper for Example 26.15: under the forward identity, each driver slice up to time `1` should
be measurable from the absolute-value state history up to time `1`. -/
lemma signSdeDriverSlice_measurable_absStateHistory_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L)
    (s : NNReal)
    (hs : s ≤ 1) :
    Measurable[processFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|) 1]
      (signSdeDriverProcess L.W s) := by
  obtain ⟨Φ, hΦ, hDriver, _⟩ :=
    signSdeCommonAbsHistorySliceFormulaAt_of_forward L hX hForward s
  have hAtTimeS :
      Measurable[processFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|) s]
        (signSdeDriverProcess L.W s) := by
    -- Proof comment: once the driver slice is rewritten through the common factor map `Φ`, its
    -- measurability reduces to measurability of the bundled absolute past path at time `s`.
    simpa using hΦ.comp_measurable (measurable_absStatePastPathAt L s)
  -- Proof comment: the time-`s` absolute-state filtration sits below the time-`1` filtration
  -- because `s ≤ 1`.
  exact
    Measurable.mono
      hAtTimeS
      ((processFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|)).mono hs)
      le_rfl

/-- Helper for Example 26.15: the Brownian-state forward identity should imply both the reverse
identity and the time-`1` absolute-history measurability of the driver in one shared stochastic
normal form. -/
lemma signSdeWeak_reverseIdentityAndDriverAbsHistoryAtOne_of_forward_core
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L) :
    signSdeWeakReverseIdentity L ∧
      processFiltration (signSdeDriverProcess L.W) 1 ≤
        processFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|) 1 := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: package the ambient Brownian-state martingale owner together with the
    -- fixed-time reverse-slice identity.
    refine ⟨signSdeWeak_stateLocalMartingale_of_forward L hX hForward, ?_⟩
    exact signSdeWeakDriverSliceEq_reverseIto_of_forward L hX hForward
  · -- Proof comment: the process filtration at time `1` is generated by deterministic slices
    -- `W_s` for `s ≤ 1`, so the generator-wise measurability lemma gives the inclusion.
    refine inf_le_right.trans ?_
    refine iSup₂_le fun s hs ↦ ?_
    exact
      measurable_iff_comap_le.mp
        (signSdeDriverSlice_measurable_absStateHistory_of_forward L hX hForward s hs)

/-- Helper for Example 26.15: on the weak-solution surface, the forward identity `(26.18)` should
already imply the reverse identity `(26.19)` once the state process is known to be Brownian. -/
lemma signSdeWeak_reverseIdentity_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L) :
    signSdeWeakReverseIdentity L := by
  -- Proof comment: the reverse identity itself depends only on the fixed-time equality bridge;
  -- keep the abs-history filtration package separate for the later non-adaptedness theorem.
  refine ⟨signSdeWeak_stateLocalMartingale_of_forward L hX hForward, ?_⟩
  exact signSdeWeakDriverSliceEq_reverseIto_of_forward L hX hForward

/-- Helper for Example 26.15: the forward identity `(26.18)` should force the driver history at
time `1` to be measurable from the absolute-value state history up to time `1`. -/
lemma signSdeWeak_driverFiltrationAtOne_le_absStateFiltration_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L) :
    processFiltration (signSdeDriverProcess L.W) 1 ≤
      processFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|) 1 := by
  -- Proof comment: the time-`1` driver-history inclusion is the second projection of the shared
  -- Brownian-state stochastic normalization packaged in the core helper.
  exact
    (signSdeWeak_reverseIdentityAndDriverAbsHistoryAtOne_of_forward_core
      L hX hForward).2

/-- Helper for Example 26.15: transport the Brownian-pair bridge back to the public weak-solution
surface without repeating any filtration or coordinate bookkeeping. -/
lemma signSdeWeak_reverseIdentityAndDriverAbsHistoryAtOne_of_forward
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L)
    (hForward : signSdeWeakForwardIdentity L) :
    signSdeWeakReverseIdentity L ∧
      processFiltration (signSdeDriverProcess L.W) 1 ≤
        processFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|) 1 := by
  -- Proof comment: the public bundle is now assembled directly from the two weak-surface bridges,
  -- so the remaining stochastic work stays on the owner that still remembers ambient adaptedness.
  exact signSdeWeak_reverseIdentityAndDriverAbsHistoryAtOne_of_forward_core L hX hForward

/-- Helper for Example 26.15: if `B 1` factors through the absolute Brownian past up to time
`1`, Brownian sign symmetry forces `B 1 = -B 1` almost surely. -/
lemma brownianFixedTime_absPastFactor_eq_neg_terminal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    {Φ : (Set.Iic (1 : NNReal) → ℝ) → ℝ}
    (hΦ : Measurable Φ)
    (hFactor : B (1 : NNReal) = Φ ∘ (fun ω u ↦ |B u ω|)) :
    B (1 : NNReal) =ᵐ[μ] fun ω ↦ -B (1 : NNReal) ω := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let pathNeg : (NNReal → ℝ) → NNReal → ℝ := fun y t ↦ -y t
  let absPastPath : (NNReal → ℝ) → Set.Iic (1 : NNReal) → ℝ := fun y u ↦ |y u|
  let pairMap : (NNReal → ℝ) → (Set.Iic (1 : NNReal) → ℝ) × ℝ :=
    fun y ↦ (absPastPath y, y (1 : NNReal))
  let flipTerminal : (Set.Iic (1 : NNReal) → ℝ) × ℝ → (Set.Iic (1 : NNReal) → ℝ) × ℝ :=
    fun z ↦ (z.1, -z.2)
  let pairProcess : Ω → (Set.Iic (1 : NNReal) → ℝ) × ℝ :=
    fun ω ↦ ((fun u ↦ |B u ω|), B (1 : NNReal) ω)
  let graph : Set ((Set.Iic (1 : NNReal) → ℝ) × ℝ) := {z | z.2 - Φ z.1 = 0}
  have hPathNegMeas : Measurable pathNeg := by
    -- Proof comment: pointwise path negation is measurable because each coordinate map is.
    refine measurable_pi_lambda _ fun t ↦ ?_
    exact measurable_neg.comp (measurable_pi_apply t)
  have hAbsPastPathMeas : Measurable absPastPath := by
    -- Proof comment: the absolute past path is measurable coordinatewise on `Set.Iic 1`.
    refine measurable_pi_lambda _ fun u ↦ ?_
    exact measurable_abs.comp (measurable_pi_apply (↑u : NNReal))
  have hPairMapMeas : Measurable pairMap := by
    -- Proof comment: the pair map keeps the absolute past path and the terminal coordinate.
    simpa [pairMap] using hAbsPastPathMeas.prodMk (measurable_pi_apply (1 : NNReal))
  have hFlipTerminalMeas : Measurable flipTerminal := by
    -- Proof comment: flipping only the terminal sign is measurable on the product space.
    simpa [flipTerminal] using measurable_fst.prodMk (measurable_neg.comp measurable_snd)
  have hProcessPathMeas : Measurable (processPath B) := by
    -- Proof comment: each Brownian deterministic-time coordinate is measurable, so the full path
    -- map is measurable.
    exact measurable_pi_lambda _ fun t ↦ (hB.stronglyMeasurable t).measurable
  have hPairProcessMeas : Measurable pairProcess := by
    -- Proof comment: the pair process is just the pair map applied to the Brownian sample path.
    exact hPairMapMeas.comp hProcessPathMeas
  have hPairIntertwine : pairMap ∘ pathNeg = flipTerminal ∘ pairMap := by
    -- Proof comment: negating a path leaves the absolute past unchanged and flips only the
    -- terminal coordinate.
    funext y
    ext <;> simp [pairMap, absPastPath, pathNeg, flipTerminal]
  have hPairLawNeg :
      (((μ.map (processPath B)).map pairMap).map flipTerminal) =
        ((μ.map (processPath B)).map pairMap) := by
    -- Proof comment: push the Brownian path-law symmetry through the pair map that records the
    -- absolute past together with the terminal value.
    calc
      (((μ.map (processPath B)).map pairMap).map flipTerminal)
          = (((μ.map (processPath B)).map pathNeg).map pairMap) := by
              rw [Measure.map_map (μ := μ.map (processPath B)) (f := pairMap) (g := flipTerminal)
                hFlipTerminalMeas hPairMapMeas]
              rw [Measure.map_map (μ := μ.map (processPath B)) (f := pathNeg) (g := pairMap)
                hPairMapMeas hPathNegMeas]
              simpa [Function.comp] using
                congrArg
                  (fun f :
                    (NNReal → ℝ) → ((Set.Iic (1 : NNReal) → ℝ) × ℝ) ↦
                      Measure.map f (μ.map (processPath B)))
                  hPairIntertwine.symm
      _ = ((μ.map (processPath B)).map pairMap) := by
            simpa using congrArg (fun ν : Measure (NNReal → ℝ) ↦ ν.map pairMap)
              (brownianPathLaw_eq_neg hB)
  have hPairLaw :
      ((μ.map (processPath B)).map pairMap) = μ.map pairProcess := by
    -- Proof comment: evaluating the pair map on the process path reproduces the concrete pair
    -- process `(absolute past, B 1)`.
    simpa [pairProcess, Function.comp] using
      (Measure.map_map (μ := μ) (f := processPath B) (g := pairMap) hPairMapMeas hProcessPathMeas :
        ((μ.map (processPath B)).map pairMap) = μ.map (pairMap ∘ processPath B))
  have hGraphMeas : MeasurableSet graph := by
    -- Proof comment: the graph condition is the zero-set of a measurable terminal-minus-factor map.
    change
      MeasurableSet
        ((fun z : (Set.Iic (1 : NNReal) → ℝ) × ℝ ↦ z.2 - Φ z.1) ⁻¹' ({0} : Set ℝ))
    exact (measurable_snd.sub (hΦ.comp measurable_fst)) (MeasurableSet.singleton 0)
  have hGraphFull : μ (pairProcess ⁻¹' graph) = 1 := by
    -- Proof comment: `hFactor` puts the concrete pair process on the graph of `Φ` pointwise, so
    -- the graph event has probability `1`.
    have hGraphAe : ∀ᵐ ω ∂μ, pairProcess ω ∈ graph := by
      exact Filter.Eventually.of_forall fun ω ↦ by
        have hFactorω : B 1 ω = Φ (fun u ↦ |B u ω|) := congrFun hFactor ω
        simp [pairProcess, graph, hFactorω]
    exact (mem_ae_iff_prob_eq_one (hPairProcessMeas hGraphMeas)).1 hGraphAe
  have hFlipGraphFull : μ (pairProcess ⁻¹' (flipTerminal ⁻¹' graph)) = 1 := by
    -- Proof comment: the pair-law symmetry transports the full graph mass to the
    -- sign-flipped graph.
    have hFlipGraphMass :
        ((μ.map (processPath B)).map pairMap) (flipTerminal ⁻¹' graph) =
          ((μ.map (processPath B)).map pairMap) graph := by
      have hMapGraph :
          (((μ.map (processPath B)).map pairMap).map flipTerminal) graph =
            ((μ.map (processPath B)).map pairMap) graph := by
        exact
          congrArg
            (fun ν : Measure ((Set.Iic (1 : NNReal) → ℝ) × ℝ) ↦ ν graph)
            hPairLawNeg
      rw [Measure.map_apply hFlipTerminalMeas hGraphMeas] at hMapGraph
      exact hMapGraph
    have hMappedFlipFull : (μ.map pairProcess) (flipTerminal ⁻¹' graph) = 1 := by
      calc
        (μ.map pairProcess) (flipTerminal ⁻¹' graph)
            = ((μ.map (processPath B)).map pairMap) (flipTerminal ⁻¹' graph) := by
                rw [hPairLaw]
        _ = ((μ.map (processPath B)).map pairMap) graph := hFlipGraphMass
        _ = (μ.map pairProcess) graph := by
              rw [hPairLaw]
        _ = 1 := by
              rw [Measure.map_apply hPairProcessMeas hGraphMeas]
              exact hGraphFull
    rw [← Measure.map_apply hPairProcessMeas (hFlipTerminalMeas hGraphMeas)]
    exact hMappedFlipFull
  have hGraphAe : ∀ᵐ ω ∂μ, pairProcess ω ∈ graph := by
    -- Proof comment: repackage the full graph measure as an almost-sure membership statement.
    exact (mem_ae_iff_prob_eq_one (hPairProcessMeas hGraphMeas)).2 hGraphFull
  have hFlipGraphAe : ∀ᵐ ω ∂μ, pairProcess ω ∈ flipTerminal ⁻¹' graph := by
    -- Proof comment: the flipped graph also has full measure by the path-law symmetry.
    exact
      (mem_ae_iff_prob_eq_one (hPairProcessMeas (hFlipTerminalMeas hGraphMeas))).2
        hFlipGraphFull
  -- Proof comment: on the intersection of the two full-measure graph events, the terminal value
  -- equals both `Φ(absPast)` and `-Φ(absPast)`, hence equals its own negative.
  filter_upwards [hGraphAe, hFlipGraphAe] with ω hω hω'
  have hGraphEq : B 1 ω = Φ (fun u ↦ |B u ω|) := by
    have hGraphZero : B 1 ω - Φ (fun u ↦ |B u ω|) = 0 := by
      simpa [pairProcess, graph] using hω
    linarith
  have hFlipEq : -B 1 ω = Φ (fun u ↦ |B u ω|) := by
    have hFlipZero : -B 1 ω - Φ (fun u ↦ |B u ω|) = 0 := by
      simpa [pairProcess, graph, flipTerminal] using hω'
    linarith
  linarith

/-- Helper for Example 26.15: a Brownian terminal value that is measurable with respect to the
absolute-value history up to time `1` must vanish almost surely by Brownian sign symmetry. -/
lemma brownianFixedTime_measurableAbsPast_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B)
    (hMeas :
      Measurable[processFiltration (fun t ω ↦ |B t ω|) 1] (B 1)) :
    ∀ᵐ ω ∂μ, B 1 ω = 0 := by
  obtain ⟨Φ, hΦ, hFactor⟩ :=
    absPastPathFactorizationAtTime (B := B) (T := 1) hMeas
  have hNegAe :
      B 1 =ᵐ[μ] fun ω ↦ -B 1 ω :=
    brownianFixedTime_absPastFactor_eq_neg_terminal hB hΦ hFactor
  -- Proof comment: once the terminal value equals its own negative almost surely, it must vanish
  -- almost surely.
  filter_upwards [hNegAe] with ω hω
  linarith

/-- Helper for Example 26.15: the time-`1` value of a Brownian motion cannot be measurable with
respect to its absolute-value history up to time `1`. -/
lemma brownianFixedTime_not_measurable_absPast
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    ¬ Measurable[processFiltration (fun t ω ↦ |B t ω|) 1] (B 1) := by
  intro hMeas
  have hZeroAe :
      ∀ᵐ ω ∂μ, B 1 ω = 0 :=
    brownianFixedTime_measurableAbsPast_eq_zero hB hMeas
  -- Proof comment: Brownian sign symmetry would force the nondegenerate terminal Gaussian
  -- marginal to collapse to `0` almost surely, which contradicts the fixed-time Gaussian law.
  exact brownianFixedTime_not_ae_eq_zero hB hZeroAe

/-- Helper for Example 26.15: covariance is unchanged after almost-everywhere replacement of
both real-valued coordinates. -/
private lemma covariance_congr_ae_example2615
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIntX : ∫ ω, X ω ∂μ = ∫ ω, X' ω ∂μ := integral_congr_ae hX
  have hIntY : ∫ ω, Y ω ∂μ = ∫ ω, Y' ω ∂μ := integral_congr_ae hY
  -- Proof comment: rewrite the expectations first, then compare the covariance integrands
  -- pointwise on the common almost-sure equality event.
  rw [covariance, covariance]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

/-- Helper for Example 26.15: the everywhere-continuous Brownian modification is again a
Brownian motion. -/
private lemma brownianContinuousVersion_isBrownianMotionLocal_example2615
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (brownianContinuousVersion (μ := μ) (B := B) hB) := by
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    -- Proof comment: the repaired process still starts from `0` pointwise.
    simpa using brownianContinuousVersion_zero (μ := μ) (B := B) hB ω
  · -- Proof comment: fixed-time almost-sure equality preserves the centered Gaussian process
    -- structure.
    exact
      hB.isGaussianProcess.congr
        (fun t ↦ brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)
  · intro t
    -- Proof comment: the centered mean is unchanged under almost-sure modification.
    exact
      (integral_congr_ae
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (hB.mean_zero t)
  · intro s t
    -- Proof comment: covariance is likewise invariant under fixed-time almost-sure equality.
    exact
      (covariance_congr_ae_example2615
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB s)
        (brownianContinuousVersion_areModifications (μ := μ) (B := B) hB t)).symm.trans
        (hB.covariance_eq s t)
  · -- Proof comment: the repaired process has continuous paths by construction.
    filter_upwards with ω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      brownianContinuousVersion_continuous (μ := μ) (B := B) hB ω

/-- Helper for Example 26.15: Chapter 22 and the continuous-version API provide one scalar
Brownian witness with everywhere continuous sample paths. -/
private theorem scalarContinuousBrownianWitness_example2615 :
    ∃ (Ω0 : Type) (_ : MeasurableSpace Ω0) (μ0 : ProbabilityMeasure Ω0)
      (B : NNReal → Ω0 → ℝ),
        IsBrownianMotion (μ0 : Measure Ω0) B ∧
          ∀ ω, Continuous (fun t : NNReal ↦ B t ω) := by
  let μstd : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hμstd_mean_zero : ∫ x, x ∂(μstd : Measure ℝ) = 0 := by
    -- Proof comment: the Skorohod embedding is applied to the centered standard Gaussian.
    simpa [μstd] using ProbabilityTheory.integral_id_gaussianReal
  have hμstd_memLp : MemLp id 2 (μstd : Measure ℝ) := by
    -- Proof comment: the standard Gaussian has finite second moment.
    simpa [μstd] using
      (ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp))
  rcases exists_skorohod_embedding μstd hμstd_mean_zero hμstd_memLp with
    ⟨Ω0, mΩ0, μ0, _Ξ, B, _τ, _hIndep, hB, _hτ, _hLaw, _hVar⟩
  let Bc : NNReal → Ω0 → ℝ := brownianContinuousVersion (μ := (μ0 : Measure Ω0)) (B := B) hB
  refine ⟨Ω0, mΩ0, μ0, Bc, ?_, ?_⟩
  · -- Proof comment: replace the Brownian witness by its everywhere-continuous modification.
    simpa [Bc] using
      brownianContinuousVersion_isBrownianMotionLocal_example2615
        (μ := (μ0 : Measure Ω0)) (B := B) hB
  · intro ω
    -- Proof comment: the repaired witness is continuous pathwise by definition.
    simpa [Bc] using
      brownianContinuousVersion_continuous (μ := (μ0 : Measure Ω0)) (B := B) hB ω

/-- Helper for Example 26.15: an everywhere-continuous one-dimensional standard Brownian vector
can be repackaged as a path-valued Brownian witness on `EuclideanPathSpace 1`. -/
private theorem pathValuedBrownian_of_continuousStandardBrownianVector_example2615
    {Ω0 : Type*} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    {W0 : NNReal → Ω0 → EuclideanSpace ℝ (Fin 1)}
    (hW0 : IsStandardBrownianMotionVector (μ0 : Measure Ω0) W0)
    (hW0cont : ∀ ω, Continuous (fun t : NNReal ↦ W0 t ω)) :
    ∃ Wpath : Ω0 → EuclideanPathSpace 1,
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Wpath))
        (μ0 : Measure Ω0)
        (pathProcess Wpath) := by
  let Wpath : Ω0 → EuclideanPathSpace 1 := fun ω ↦
    ⟨fun t ↦ (EuclideanSpace.equiv (Fin 1) ℝ) (W0 t ω), by
      -- Proof comment: the Euclidean equivalence transports continuity of the vector path to the
      -- coordinate-path representation.
      simpa using (EuclideanSpace.equiv (Fin 1) ℝ).continuous.comp (hW0cont ω)⟩
  refine ⟨Wpath, ?_⟩
  refine ⟨?_, ?_⟩
  · -- Proof comment: converting the path process back through `toEuclidean` recovers the
    -- original one-dimensional Brownian vector.
    simpa [CoordinateProcess.toEuclidean, pathProcess, Wpath] using hW0
  · intro t
    -- Proof comment: every process is adapted to its own natural filtration by construction.
    refine measurable_iff_comap_le.2 ?_
    have hWt_meas : Measurable (pathProcess Wpath t) := by
      exact
        ((EuclideanSpace.equiv (Fin 1) ℝ).continuous.measurable).comp
          (IsStandardBrownianMotionVector.stronglyMeasurable hW0 t).measurable
    exact le_inf (Measurable.comap_le hWt_meas) <| by
      refine le_iSup_of_le t ?_
      exact le_iSup_of_le le_rfl le_rfl

/-- Helper for Example 26.15: there exists a one-dimensional path-valued Brownian witness whose
ambient filtration is its own natural filtration. -/
private theorem existsOneDimensionalBrownianPathWitness_example2615 :
    ∃ (Ω0 : Type) (_ : MeasurableSpace Ω0) (μ0 : ProbabilityMeasure Ω0)
      (Wpath : Ω0 → EuclideanPathSpace 1),
        IsBrownianMotionWithFiltration
          (processFiltration (pathProcess Wpath))
          (μ0 : Measure Ω0)
          (pathProcess Wpath) := by
  rcases scalarContinuousBrownianWitness_example2615 with
    ⟨Ω0, mΩ0, μ0, B, hB, hBcont⟩
  let W0 : NNReal → Ω0 → EuclideanSpace ℝ (Fin 1) := fun t ω ↦
    (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ : Fin 1 ↦ B t ω)
  have hW0 : IsStandardBrownianMotionVector (μ0 : Measure Ω0) W0 := by
    refine
      { isBrownianMotion := ?_
        iIndepFun := ?_ }
    · intro i
      fin_cases i
      -- Proof comment: the unique coordinate is exactly the scalar Brownian witness.
      simpa [W0]
    · -- Proof comment: the one-point coordinate family is independent for cardinality reasons.
      exact iIndepFun.of_subsingleton
  have hW0cont : ∀ ω, Continuous (fun t : NNReal ↦ W0 t ω) := by
    intro ω
    -- Proof comment: the Euclidean-space spelling is just the continuous scalar path embedded in
    -- one dimension.
    have hCoords : Continuous (fun t : NNReal ↦ fun _ : Fin 1 ↦ B t ω) :=
      continuous_pi fun _ ↦ hBcont ω
    simpa [W0] using (EuclideanSpace.equiv (Fin 1) ℝ).symm.continuous.comp hCoords
  exact
    pathValuedBrownian_of_continuousStandardBrownianVector_example2615
      μ0 hW0 hW0cont

/-- Helper for Example 26.15: a one-dimensional Brownian path witness starts from the deterministic
zero state and therefore has the required Dirac initial law. -/
private theorem brownianPathWitness_initialLaw_example2615
    {Ω0 : Type*} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    (Xpath : Ω0 → EuclideanPathSpace 1)
    (hXpathNat :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        (pathProcess Xpath)) :
    HasLaw (fun ω ↦ Xpath ω 0) signSdeInitialLaw (μ0 : Measure Ω0) := by
  have hZero :
      (fun ω ↦ Xpath ω 0) = fun _ : Ω0 ↦ signSdeInitialState := by
    funext ω
    ext i
    fin_cases i
    -- Proof comment: the unique Brownian coordinate starts at `0`, so the time-zero path value is
    -- the deterministic zero state.
    simpa [signSdeInitialState, CoordinateProcess.toEuclidean, pathProcess] using
      congrFun ((hXpathNat.1.isBrownianMotion 0).zero) ω
  have hConstLaw :
      HasLaw (fun _ : Ω0 ↦ signSdeInitialState) signSdeInitialLaw (μ0 : Measure Ω0) := by
    refine ⟨measurable_const.aemeasurable, ?_⟩
    simpa [signSdeInitialLaw] using
      (Measure.map_const (μ0 : Measure Ω0) signSdeInitialState)
  -- Proof comment: replace the constant zero state by the actual time-zero path value using the
  -- pointwise Brownian start identity.
  exact HasLaw.congr hConstLaw (Filter.EventuallyEq.of_eq hZero)

/-- Helper for Example 26.15: the scalar coordinate of a Brownian path witness is adapted to its
own natural process filtration. -/
private lemma brownianPathStateProcess_adapted_example2615
    {Ω0 : Type*} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    (Xpath : Ω0 → EuclideanPathSpace 1)
    (hXpathNat :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        (pathProcess Xpath)) :
    Adapted (processFiltration (pathProcess Xpath)) (signSdeStateProcess Xpath) := by
  intro t
  -- Proof comment: project the path-valued coordinate process to its unique scalar component.
  change
    Measurable[processFiltration (pathProcess Xpath) t]
      ((fun x : Fin 1 → ℝ ↦ x 0) ∘ fun ω ↦ Xpath ω t)
  exact (measurable_pi_apply 0).comp (hXpathNat.2 t)

/-- Helper for Example 26.15: the scalar state coordinate of a Brownian path witness is
progressively measurable on its natural filtration. -/
private lemma brownianPathStateProcess_progMeasurable_example2615
    {Ω0 : Type*} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    (Xpath : Ω0 → EuclideanPathSpace 1)
    (hXpathNat :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        (pathProcess Xpath)) :
    ProgMeasurable (processFiltration (pathProcess Xpath)) (signSdeStateProcess Xpath) := by
  have hCont : ∀ ω, Continuous (fun t : NNReal ↦ signSdeStateProcess Xpath t ω) := by
    intro ω
    -- Proof comment: each sample path is continuous, and scalar evaluation preserves continuity.
    simpa [signSdeStateProcess] using (continuous_apply 0).comp (Xpath ω).continuous
  -- Proof comment: continuous adapted scalar paths are progressively measurable on the same
  -- filtration.
  exact
    (brownianPathStateProcess_adapted_example2615 μ0 Xpath hXpathNat).stronglyAdapted
      .progMeasurable_of_continuous hCont

/-- Helper for Example 26.15: the sign coefficient built from a Brownian path witness is jointly
measurable on `ℝ≥0 × Ω`. -/
private lemma brownianPathSignIntegrand_measurable_uncurry_example2615
    {Ω0 : Type*} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    (Xpath : Ω0 → EuclideanPathSpace 1)
    (hXpathNat :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        (pathProcess Xpath)) :
    Measurable (Function.uncurry (signSdeIntegrand Xpath)) := by
  have hStateMeas :
      Measurable (Function.uncurry (signSdeStateProcess Xpath)) :=
    (brownianPathStateProcess_progMeasurable_example2615 μ0 Xpath hXpathNat).measurable_uncurry
  -- Proof comment: compose the jointly measurable scalar state coordinate with the measurable
  -- real sign map.
  simpa [Function.comp, Function.uncurry, signSdeIntegrand, signSdeStateProcess] using
    measurableRealSignMap_example2615.comp hStateMeas

/-- Helper for Example 26.15: the sign coefficient built from a Brownian path witness is
progressively measurable on its natural filtration. -/
private lemma brownianPathSignIntegrand_progMeasurable_example2615
    {Ω0 : Type*} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    (Xpath : Ω0 → EuclideanPathSpace 1)
    (hXpathNat :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        (pathProcess Xpath)) :
    ProgMeasurable (processFiltration (pathProcess Xpath)) (signSdeIntegrand Xpath) := by
  -- Proof comment: product measurability of the sign coefficient restricts to each deterministic
  -- strip `[0, T] × Ω`, which is the scalar progressive measurability criterion.
  refine
    Adapted.progMeasurable_of_measurableOnStrips
      (ℱ := processFiltration (pathProcess Xpath)) ?_
  intro T
  exact
    Adapted.measurableOnStrip_of_productMeasurable
      (ℱ := processFiltration (pathProcess Xpath))
      (H := signSdeIntegrand Xpath)
      (brownianPathSignIntegrand_measurable_uncurry_example2615 μ0 Xpath hXpathNat)
      T

/-- Helper for Example 26.15: the sign coefficient of a Brownian path witness still has square at
most `1` pointwise. -/
private lemma brownianPathSignIntegrand_sq_le_one_example2615
    {Ω0 : Type*} [MeasurableSpace Ω0]
    (Xpath : Ω0 → EuclideanPathSpace 1)
    (t : NNReal) (ω : Ω0) :
    (signSdeIntegrand Xpath t ω) ^ 2 ≤ 1 := by
  -- Proof comment: `Real.sign` only takes the values `-1`, `0`, and `1`.
  obtain hsign | hsign | hsign := Real.sign_apply_eq (signSdeStateProcess Xpath t ω)
  · simpa [signSdeIntegrand, signSdeStateProcess, hsign]
  · simpa [signSdeIntegrand, signSdeStateProcess, hsign]
  · simpa [signSdeIntegrand, signSdeStateProcess, hsign]

/-- Helper for Example 26.15: the sign coefficient of a Brownian path witness has finite
deterministic-horizon square energy on every compact interval. -/
private lemma brownianPathSignIntegrand_squareIntegrableUpTo_example2615
    {Ω0 : Type*} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    (Xpath : Ω0 → EuclideanPathSpace 1)
    (hXpathNat :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        (pathProcess Xpath))
    (T : NNReal) :
    ∀ᵐ ω ∂(μ0 : Measure Ω0),
      IntegrableOn
        (fun s : ℝ ↦ (signSdeIntegrand Xpath s.toNNReal ω) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
  -- Proof comment: combine joint measurability with the pointwise bound `sign(X)^2 ≤ 1`.
  exact
    squareIntegrableUpTo_of_uncurryMeasurable_sq_le_one
      (μ := (μ0 : Measure Ω0))
      (H := signSdeIntegrand Xpath)
      (brownianPathSignIntegrand_measurable_uncurry_example2615 μ0 Xpath hXpathNat)
      (brownianPathSignIntegrand_sq_le_one_example2615 Xpath)
      T

/-- Helper for Example 26.15: once a Brownian state path has been paired with a Brownian driver
that already satisfies the exact forward identity, the remaining weak-solution packaging is
formal. -/
private theorem signSdeWeakSolution_of_brownianStatePath_example2615
    {Ω0 : Type*} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    (Xpath : Ω0 → EuclideanPathSpace 1)
    (hXpathNat :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        (pathProcess Xpath))
    (Wscalar : NNReal → Ω0 → ℝ)
    (hWBrownian :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        (fun t ω _ : Fin 1 ↦ Wscalar t ω))
    (hForward :
      signSdeSolvesSDE
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        Xpath
        (fun t ω _ : Fin 1 ↦ Wscalar t ω)) :
    ∃ L : SignSdeWeakSolution, signSdeWeakStateIsBrownian L := by
  have hStateBrownian :
      IsBrownianMotion (μ0 : Measure Ω0) (signSdeStateProcess Xpath) := by
    -- Proof comment: the scalar state coordinate is the unique coordinate of the Brownian path
    -- witness `Xpath`.
    simpa [signSdeStateProcess, CoordinateProcess.toEuclidean, pathProcess] using
      (hXpathNat.1.isBrownianMotion 0)
  have hWscalarBrownian :
      IsBrownianMotion (μ0 : Measure Ω0) Wscalar := by
    -- Proof comment: the scalar driver is the only coordinate of the one-dimensional Brownian
    -- vector process `fun t ω _ ↦ Wscalar t ω`.
    simpa [CoordinateProcess.toEuclidean] using
      (hWBrownian.1.isBrownianMotion 0)
  let L : SignSdeWeakSolution :=
    { Ω := Ω0
      instMeasurableSpace := inferInstance
      μ := (μ0 : Measure Ω0)
      instIsProbabilityMeasure := inferInstance
      ℱ := processFiltration (pathProcess Xpath)
      instUsualConditions := inferInstance
      X := Xpath
      W := fun t ω _ : Fin 1 ↦ Wscalar t ω
      brownian := hWBrownian
      coordinate_martingale := by
        intro i
        fin_cases i
        -- Proof comment: the one-dimensional Brownian driver is a martingale once it is viewed on
        -- the ambient filtration to which it is already adapted.
        exact
          scalarBrownian_martingale_of_adapted_example2615
            hWscalarBrownian
            (oneDimVectorProcessCoordinate_adapted_example2615 hWBrownian.2)
      adapted := by
        -- Proof comment: the state path witness is adapted to its own process filtration by
        -- construction.
        simpa [pathProcess] using hXpathNat.2
      initialLaw := brownianPathWitness_initialLaw_example2615 μ0 Xpath hXpathNat
      solves_sde := hForward }
  refine ⟨L, ?_⟩
  -- Proof comment: the packaged weak solution keeps the original Brownian state path unchanged.
  simpa [L, signSdeWeakStateIsBrownian, signSdeStateIsBrownian] using hStateBrownian

/-- Helper for Example 26.15: the remaining existence frontier is the explicit reverse sign-Itô
driver built from a Brownian state path. -/
private theorem reverseSignDriverBrownianWeakWitness_example2615
    {Ω0 : Type*} [MeasurableSpace Ω0]
    (μ0 : ProbabilityMeasure Ω0)
    (Xpath : Ω0 → EuclideanPathSpace 1)
    (hXpathNat :
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        (pathProcess Xpath)) :
    ∃ Wscalar : NNReal → Ω0 → ℝ,
      IsBrownianMotionWithFiltration
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        (fun t ω _ : Fin 1 ↦ Wscalar t ω) ∧
      signSdeSolvesSDE
        (processFiltration (pathProcess Xpath))
        (μ0 : Measure Ω0)
        Xpath
        (fun t ω _ : Fin 1 ↦ Wscalar t ω) := by
  -- Route correction: separate the genuine reverse-driver construction from the formal
  -- weak-solution packaging theorem above.
  -- TODO: define `Wscalar` as the canonical Itô integral of `sign(X)` against the Brownian state
  -- path `Xpath`, prove Brownianity of `Wscalar` from the unit square-variation bridge, and prove
  -- the exact forward identity by the deterministic fixed-time involution theorem.
  let _ := hXpathNat
  sorry

/-- Helper for Example 26.15: the existence theorem is a projection from one concrete sign-SDE
weak witness whose state process is Brownian. -/
lemma existsBrownianStateWeakSolution :
    ∃ L : SignSdeWeakSolution, signSdeWeakStateIsBrownian L := by
  -- Route correction: the public existence theorem should only extract the Brownian-state witness;
  -- the reverse identity can then be obtained from the generic forward-to-reverse bridge.
  rcases existsOneDimensionalBrownianPathWitness_example2615 with
    ⟨Ω0, mΩ0, μ0, Xpath, hXpathNat⟩
  rcases
      reverseSignDriverBrownianWeakWitness_example2615
        (Ω0 := Ω0)
        (μ0 := μ0)
        Xpath
        hXpathNat with
    ⟨Wscalar, hWBrownian, hForward⟩
  -- Proof comment: once the reverse driver and forward identity have been isolated, the
  -- weak-solution package is purely formal.
  exact
    signSdeWeakSolution_of_brownianStatePath_example2615
      μ0 Xpath hXpathNat Wscalar hWBrownian hForward

/-- Example 26.15 (1): on the source weak-solution surface, once the state process is Brownian,
the forward identity `(26.18)` is equivalent to the reverse identity `(26.19)`. -/
theorem sign_sde_forward_identity_iff_reverse_identity
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L) :
    signSdeWeakForwardIdentity L ↔ signSdeWeakReverseIdentity L := by
  constructor
  · intro hForward
    -- Proof comment: the public equivalence only needs the reverse identity, so use the direct
    -- fixed-time bridge and leave the abs-history filtration argument to theorem `(3)`.
    exact signSdeWeak_reverseIdentity_of_forward L hX hForward
  · intro hReverse
    -- Proof comment: the reverse identity is stronger than needed here because every weak
    -- solution already satisfies the forward identity by definition.
    exact signSdeWeakForwardIdentity_of_solution L

/-- Example 26.15 (2): the one-dimensional sign SDE with initial value `0` admits a weak
solution obtained from a Brownian state process; in particular, the witness also satisfies the
reverse identity `(26.19)`. -/
theorem sign_sde_hasWeakSolution :
    ∃ L : SignSdeWeakSolution,
      signSdeWeakStateIsBrownian L ∧ signSdeWeakReverseIdentity L := by
  rcases existsBrownianStateWeakSolution with ⟨L, hX⟩
  refine ⟨L, hX, ?_⟩
  -- Proof comment: once one Brownian-state weak witness exists, its reverse identity follows from
  -- the public equivalence together with the stored forward identity.
  exact
    (sign_sde_forward_identity_iff_reverse_identity L hX).mp
      (signSdeWeakForwardIdentity_of_solution L)

/-- Example 26.15 (3): for any weak solution of the sign SDE whose state process is Brownian, the
state process is not adapted to the filtration generated by its driving Brownian motion. -/
theorem sign_sde_state_not_adapted_to_driver
    (L : SignSdeWeakSolution)
    (hX : signSdeWeakStateIsBrownian L) :
    ¬ MeasureTheory.Adapted
        (processFiltration (signSdeDriverProcess L.W))
        (signSdeStateProcess L.X) := by
  intro hAdapted
  have hBundle :
      signSdeWeakReverseIdentity L ∧
        processFiltration (signSdeDriverProcess L.W) 1 ≤
          processFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|) 1 :=
    signSdeWeak_reverseIdentityAndDriverAbsHistoryAtOne_of_forward
      L hX (signSdeWeakForwardIdentity_of_solution L)
  have hStateOneMeasAbs :
      Measurable[processFiltration (fun t ω ↦ |signSdeStateProcess L.X t ω|) 1]
        (signSdeStateProcess L.X 1) := by
    -- Proof comment: the assumed driver-adaptedness makes `X₁` measurable with respect to the
    -- driver history, and the bundled reverse-identity bridge upgrades that to absolute-history
    -- measurability at time `1`.
    exact Measurable.mono (hAdapted 1) hBundle.2 le_rfl
  -- Proof comment: the new fixed-time obstruction helper packages the Brownian sign-symmetry
  -- contradiction directly as a non-measurability statement for the terminal value.
  exact brownianFixedTime_not_measurable_absPast hX hStateOneMeasAbs

end ProbabilityTheory
