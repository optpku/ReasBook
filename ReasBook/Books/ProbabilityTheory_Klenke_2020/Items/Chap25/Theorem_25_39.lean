/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Lemma_22_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.BrownianMotionVectorStartedAt
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Exercise_25_4_1.LocalOneSidedBrownianHitting
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_40

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Topology
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

section BrownianRecurrenceTransience

section
omit [IsProbabilityMeasure μ]

/-- Helper for Theorem 25.39: recentering a real Brownian motion at a deterministic time again
gives a Brownian motion. -/
lemma shiftedIncrement_isBrownianMotion
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (T : NNReal) :
    IsBrownianMotion μ (fun t ω ↦ B (T + t) ω - B T ω) := by
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: the recentered shifted process still starts from `0`.
    funext ω
    simp
  · -- Proof comment: increments on the translated time mesh are exactly increments of the
    -- original Brownian motion.
    rw [hasIndepIncrements_iff_nat]
    intro t ht
    simpa [add_assoc] using
      hB.indepIncrements.nat (t := fun i ↦ T + t i)
        (fun i j hij ↦ by
          simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left (ht hij) T)
  · -- Proof comment: deterministic time translation preserves stationary increments verbatim.
    intro r s t
    simpa [add_assoc, add_left_comm, add_comm] using
      hB.stationaryIncrements (T + r) s t
  · intro t ht
    -- Proof comment: the shifted marginal is an increment of `B`, hence has the same centered
    -- Gaussian law as the original Brownian motion at time `t`.
    have hId :
        IdentDistrib
          (fun ω ↦ B (T + t) ω - B T ω)
          (fun ω ↦ B t ω - B 0 ω)
          μ μ := by
      simpa [add_assoc, add_comm, add_left_comm] using
        hB.stationaryIncrements.identDistrib_increment (r := 0) (s := t) (t := T)
    have hLaw0 : HasLaw (fun ω ↦ B t ω - B 0 ω) (gaussianReal 0 t) μ := by
      simpa [hB.zero] using hB.gaussian_marginal ht
    exact hId.symm.hasLaw hLaw0
  · -- Proof comment: shifting the time parameter and subtracting the deterministic anchor keeps
    -- almost-sure continuity of the sample paths.
    filter_upwards [hB.continuous_paths] with ω hω
    have hshift : Continuous (fun t : NNReal ↦ B (T + t) ω) :=
      hω.comp (continuous_const.add continuous_id)
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hshift.sub continuous_const

/-- Helper for Theorem 25.39: translating a standard real Brownian motion by a constant produces
Brownian motion started from that constant. -/
lemma translatedBrownianMotionStartedAt
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (x : ℝ) :
    IsBrownianMotionStartedAt μ (fun t ω ↦ x + B t ω) x := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  refine
    { stronglyMeasurable := fun t ↦ (hB.stronglyMeasurable t).const_add x
      start := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: adding the deterministic start point preserves the time-zero identity.
    have hpreimage : (fun ω ↦ x + B 0 ω) ⁻¹' ({x} : Set ℝ) = Set.univ := by
      ext ω
      simp [hB.zero]
    rw [hpreimage]
    simp
  · -- Proof comment: the deterministic translation cancels in every increment.
    rw [hasIndepIncrements_iff_nat]
    intro t ht
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hB.indepIncrements.nat (t := t) ht
  · -- Proof comment: stationary increments are unchanged by adding the same constant everywhere.
    intro r s t
    have hleft :
        (fun ω ↦ (x + B ((s + t) + r) ω) - (x + B (t + r) ω)) =
          (fun ω ↦ B ((s + t) + r) ω - B (t + r) ω) := by
      funext ω
      ring
    have hright :
        (fun ω ↦ (x + B (s + r) ω) - (x + B r ω)) =
          (fun ω ↦ B (s + r) ω - B r ω) := by
      funext ω
      ring
    simpa [hleft, hright] using hB.stationaryIncrements r s t
  · intro t ht
    -- Proof comment: the time-`t` marginal is the centered Gaussian translated by `x`.
    simpa [add_comm] using ProbabilityTheory.gaussianReal_add_const (hB.gaussian_marginal ht) x
  · -- Proof comment: deterministic translation preserves almost-sure continuity of sample paths.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using continuous_const.add hω

end

section
omit [IsProbabilityMeasure μ]

/-- Helper for Theorem 25.39: deterministic-time recentering preserves the standard
`d`-dimensional Brownian-vector structure. -/
lemma shiftedIncrement_isStandardBrownianVector
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (T : NNReal) :
    IsStandardBrownianMotionVector μ (fun t ω ↦ W (T + t) ω - W T ω) := by
  let F : (NNReal → ℝ) → (NNReal → ℝ) := fun f t ↦ f (T + t) - f T
  have hF_meas : Measurable F := by
    -- Proof comment: measurability of the shifted-path transform is checked coordinatewise in
    -- the product measurable space on `NNReal → ℝ`.
    refine measurable_pi_lambda _ ?_
    intro t
    exact (measurable_pi_apply (T + t)).sub (measurable_pi_apply T)
  refine
    { isBrownianMotion := fun i ↦ by
        -- Proof comment: each coordinate is exactly the deterministic-time shift of a scalar
        -- Brownian motion.
        simpa using
          shiftedIncrement_isBrownianMotion
            (μ := μ) (B := fun t ω ↦ W t ω i) (hB := hW.isBrownianMotion i) T
      iIndepFun := by
        -- Proof comment: coordinate independence is preserved under the same measurable path
        -- transform applied coordinatewise.
        simpa [F] using hW.iIndepFun.comp (fun _ ↦ F) (fun _ ↦ hF_meas) }

end

section
omit [IsProbabilityMeasure μ]

/-- Helper for Theorem 25.39: restarting after a deterministic time and then translating by a
deterministic state produces a Brownian vector started from that state. -/
lemma translatedRestart_isBrownianVectorStartedAt
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (x : State) (T : NNReal) :
    IsBrownianMotionVectorStartedAt
      μ (fun t ω ↦ x + (W (T + t) ω - W T ω)) x := by
  let U : VectorProcess := fun t ω ↦ W (T + t) ω - W T ω
  let V : VectorProcess := fun t ω ↦ x + U t ω
  let G : Fin d → (NNReal → ℝ) → (NNReal → ℝ) := fun i f t ↦ x i + f t
  have hG_meas : ∀ i : Fin d, Measurable (G i) := by
    intro i
    refine measurable_pi_lambda _ ?_
    intro t
    exact measurable_const.add (measurable_pi_apply t)
  have hU : IsStandardBrownianMotionVector μ U :=
    shiftedIncrement_isStandardBrownianVector (μ := μ) (W := W) hW T
  refine
    { isBrownianMotionStartedAt := fun i ↦ by
        -- Proof comment: each coordinate is the deterministic translation of the restarted
        -- centered Brownian coordinate.
        have hshift :
            IsBrownianMotion μ (fun t ω ↦ U t ω i) :=
          hU.isBrownianMotion i
        simpa [U, V, G] using translatedBrownianMotionStartedAt (μ := μ) hshift (x i)
      iIndepFun := by
        -- Proof comment: coordinate independence survives the same deterministic translation
        -- applied coordinatewise to the restarted centered Brownian vector.
        simpa [U, V, G] using hU.iIndepFun.comp (fun i ↦ G i) hG_meas }

end

section
omit [IsProbabilityMeasure μ]

/-- Helper for Theorem 25.39: every deterministic coordinate of the Brownian vector belongs to
`L²`. -/
lemma brownianCoordinateEval_memLpTwo
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) (t : NNReal) :
    MemLp (fun ω ↦ W t ω i) 2 μ := by
  let B : NNReal → Ω → ℝ := fun s ω ↦ W s ω i
  have hB : IsBrownianMotion μ B := hW.isBrownianMotion i
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  by_cases ht : t = 0
  · -- Proof comment: at time `0`, each Brownian coordinate is the constant zero function.
    subst ht
    simp [B, hB.zero]
  · -- Proof comment: positive-time Brownian marginals are Gaussian, hence square-integrable.
    have ht_pos : 0 < t := pos_iff_ne_zero.mpr ht
    have hLaw : HasLaw (B t) (gaussianReal 0 t) μ := hB.gaussian_marginal ht_pos
    have hVar : Var[B t; μ] = t := by
      simpa using hLaw.variance_eq
    have hVar_ne : Var[B t; μ] ≠ 0 := by
      rw [hVar]
      exact_mod_cast ht
    simpa [B] using
      memLp_two_of_variance_ne_zero hLaw.aemeasurable.aestronglyMeasurable hVar_ne

/-- Helper for Theorem 25.39: a standard Brownian vector is a Gaussian process in the Euclidean
state space. -/
lemma standardBrownianVector_isGaussianProcess
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) :
    IsGaussianProcess W μ := by
  classical
  letI : IsStandardBrownianMotionVector μ W := hW
  let ψ : State ≃L[ℝ] (Fin d → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)
  refine
    { hasGaussianLaw := fun I ↦ ?_ }
  let Xi : Fin d → Ω → I → ℝ := fun i ω t ↦ W t ω i
  have hXi_gauss : ∀ i : Fin d, HasGaussianLaw (Xi i) μ := by
    intro i
    let hBi : IsBrownianMotion μ (fun t ω ↦ W t ω i) := inferInstance
    let hGi : IsGaussianProcess (fun t ω ↦ W t ω i) μ :=
      IsBrownianMotion.isGaussianProcess hBi
    simpa [Xi] using hGi.hasGaussianLaw I
  have hXi_indep : iIndepFun Xi μ := by
    -- Proof comment: coordinate-path independence survives restriction to the finite time set `I`.
    refine hW.iIndepFun.comp (fun _ f ↦ I.restrict f) ?_
    intro i
    exact measurable_pi_lambda _ fun t ↦ measurable_pi_apply (t : NNReal)
  let L : (Fin d → I → ℝ) →L[ℝ] I → State :=
    { toFun := fun x t ↦ ψ.symm (fun i ↦ x i t)
      map_add' := by
        intro x y
        ext t i
        rfl
      map_smul' := by
        intro c x
        ext t i
        rfl
      cont := by
        refine continuous_pi fun t ↦ ?_
        exact ψ.symm.continuous.comp <| continuous_pi fun i ↦
          (continuous_apply t).comp (continuous_apply i) }
  have hgauss :
      HasGaussianLaw (fun ω ↦ fun i ↦ Xi i ω) μ :=
    ProbabilityTheory.iIndepFun.hasGaussianLaw hXi_gauss hXi_indep
  -- Proof comment: repackage the coordinatewise Gaussian law back into the Euclidean state space.
  simpa [Xi] using hgauss.map L

end

/-- Helper for Theorem 25.39: at a rational deterministic time, the current Brownian state is
independent of the rational future increment path. -/
lemma futureIncrementRatPath_indep_currentState
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (q : ℚ≥0) :
    IndepFun
      (fun ω (s : ℚ≥0) ↦ W ((q : NNReal) + s) ω - W q ω)
      (fun ω ↦ W q ω)
      μ := by
  let X : ℚ≥0 → Ω → State := fun s ω ↦ W ((q : NNReal) + s) ω - W q ω
  let Y : Unit → Ω → State := fun _ ω ↦ W q ω
  have hWG :
      IsGaussianProcess W μ :=
    standardBrownianVector_isGaussianProcess (μ := μ) (W := W) hW
  have hJoint : IsGaussianProcess (Sum.elim X Y) μ := by
    refine hWG.of_isGaussianProcess ?_
    intro z
    cases z with
    | inl s =>
        let tq : NNReal := (q : NNReal) + s
        let I : Finset NNReal := {tq, (q : NNReal)}
        have htq : tq ∈ I := by simp [I, tq]
        have hqI : (q : NNReal) ∈ I := by simp [I]
        refine
          ⟨I,
            { toFun := fun x ↦ x (⟨tq, htq⟩ : I) - x (⟨(q : NNReal), hqI⟩ : I)
              map_add' := by
                intro x y
                ext i
                change
                  (x (⟨tq, htq⟩ : I)).ofLp i + (y (⟨tq, htq⟩ : I)).ofLp i -
                      ((x (⟨(q : NNReal), hqI⟩ : I)).ofLp i +
                        (y (⟨(q : NNReal), hqI⟩ : I)).ofLp i) =
                    ((x (⟨tq, htq⟩ : I)).ofLp i - (x (⟨(q : NNReal), hqI⟩ : I)).ofLp i) +
                      ((y (⟨tq, htq⟩ : I)).ofLp i - (y (⟨(q : NNReal), hqI⟩ : I)).ofLp i)
                ring
              map_smul' := by
                intro c x
                ext i
                change
                  c * (x (⟨tq, htq⟩ : I)).ofLp i - c * (x (⟨(q : NNReal), hqI⟩ : I)).ofLp i =
                    c * ((x (⟨tq, htq⟩ : I)).ofLp i - (x (⟨(q : NNReal), hqI⟩ : I)).ofLp i)
                ring
              cont := by
                fun_prop },
            ?_⟩
        · -- Proof comment: a future state difference is a linear projection of the two-time law.
          intro ω
          simp [X, tq]
    | inr u =>
        let I : Finset NNReal := {(q : NNReal)}
        have hqI : (q : NNReal) ∈ I := by simp [I]
        refine
          ⟨I,
            { toFun := fun x ↦ x (⟨(q : NNReal), hqI⟩ : I)
              map_add' := by
                intro x y
                rfl
              map_smul' := by
                intro c x
                rfl
              cont := by
                fun_prop },
            ?_⟩
        · -- Proof comment: the anchor state is just the evaluation at time `q`.
          intro ω
          cases u
          simp [Y, I]
  have hIndepFamily :
      IndepFun (fun ω s ↦ X s ω) (fun ω u ↦ Y u ω) μ := by
    -- Proof comment: the joint Euclidean Gaussian family is independent once every cross
    -- covariance of inner products vanishes.
    refine ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_inner hJoint ?_ ?_ ?_
    · intro s
      exact
        ((ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hW
              ((q : NNReal) + s)).measurable.sub
          (ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hW
            (q : NNReal)).measurable).aemeasurable
    · intro u
      cases u
      exact
        (ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hW
          (q : NNReal)).aemeasurable
    · intro s u x y
      cases u
      have hXinner :
          (fun ω ↦ inner ℝ x (X s ω)) = fun ω ↦ ∑ i, x i * X s ω i := by
        -- Proof comment: `PiLp.inner_apply` is the canonical coordinate formula for the Euclidean
        -- inner product on `State`.
        ext ω
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using (RCLike.inner_apply' (x.ofLp i) ((X s ω).ofLp i))
      have hYinner :
          (fun ω ↦ inner ℝ y (Y () ω)) = fun ω ↦ ∑ j, y j * Y () ω j := by
        -- Proof comment: the anchor-state inner product is normalized by the same coordinate API.
        ext ω
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using (RCLike.inner_apply' (y.ofLp i) ((Y () ω).ofLp i))
      have hXcoord_mem :
          ∀ i : Fin d, MemLp (fun ω ↦ X s ω i) 2 μ := by
        intro i
        exact
          (brownianCoordinateEval_memLpTwo (μ := μ) (W := W) hW i ((q : NNReal) + s)).sub
            (brownianCoordinateEval_memLpTwo (μ := μ) (W := W) hW i (q : NNReal))
      have hYcoord_mem :
          ∀ i : Fin d, MemLp (fun ω ↦ Y () ω i) 2 μ := by
        intro i
        simpa [Y] using
          brownianCoordinateEval_memLpTwo (μ := μ) (W := W) hW i (q : NNReal)
      have hXsum_mem :
          ∀ i : Fin d, MemLp (fun ω ↦ x i * X s ω i) 2 μ := by
        intro i
        exact (hXcoord_mem i).const_mul (x i)
      have hYsum_mem :
          ∀ i : Fin d, MemLp (fun ω ↦ y i * Y () ω i) 2 μ := by
        intro i
        exact (hYcoord_mem i).const_mul (y i)
      rw [hXinner, hYinner, covariance_fun_sum_fun_sum hXsum_mem hYsum_mem]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      by_cases hij : i = j
      · subst hij
        have htq_mem :
            MemLp (fun ω ↦ W ((q : NNReal) + s) ω i) 2 μ :=
          brownianCoordinateEval_memLpTwo (μ := μ) (W := W) hW i ((q : NNReal) + s)
        have hq_mem :
            MemLp (fun ω ↦ W (q : NNReal) ω i) 2 μ :=
          brownianCoordinateEval_memLpTwo (μ := μ) (W := W) hW i (q : NNReal)
        have htq_cov :
            cov[(fun ω ↦ W ((q : NNReal) + s) ω i), (fun ω ↦ W (q : NNReal) ω i); μ] =
              ((q : NNReal) : ℝ) := by
          simpa [inf_eq_right.mpr (show (q : NNReal) ≤ (q : NNReal) + s by simp)] using
            IsBrownianMotion.covariance_eq
              (show IsBrownianMotion μ (fun t ω ↦ W t ω i) from inferInstance)
              ((q : NNReal) + s) (q : NNReal)
        have hq_cov :
            cov[(fun ω ↦ W (q : NNReal) ω i), (fun ω ↦ W (q : NNReal) ω i); μ] =
              ((q : NNReal) : ℝ) := by
          simpa using
            IsBrownianMotion.covariance_eq
              (show IsBrownianMotion μ (fun t ω ↦ W t ω i) from inferInstance)
              (q : NNReal) (q : NNReal)
        calc
          cov[fun ω ↦ x i * X s ω i, fun ω ↦ y i * Y () ω i; μ]
              = x i * (y i *
                  cov[(fun ω ↦ W ((q : NNReal) + s) ω i - W (q : NNReal) ω i),
                    (fun ω ↦ W (q : NNReal) ω i); μ]) := by
                      simp [X, Y, covariance_const_mul_left, covariance_const_mul_right,
                        mul_left_comm]
          _ = x i * (y i * 0) := by
                rw [covariance_fun_sub_left htq_mem hq_mem hq_mem, htq_cov, hq_cov]
                ring
          _ = 0 := by ring
      · have hcoord_indep :
            IndepFun
              (fun ω ↦ W ((q : NNReal) + s) ω i - W (q : NNReal) ω i)
              (fun ω ↦ W (q : NNReal) ω j)
              μ := by
          -- Proof comment: distinct coordinates are independent as path processes, hence so are
          -- these deterministic-time functionals of the past and future coordinates.
          exact
            (hW.iIndepFun.indepFun (i := i) (j := j) hij).comp
              ((measurable_pi_apply ((q : NNReal) + s)).sub
                (measurable_pi_apply (q : NNReal)))
              (measurable_pi_apply (q : NNReal))
        calc
          cov[fun ω ↦ x i * X s ω i, fun ω ↦ y j * Y () ω j; μ]
              = x i * (y j *
                  cov[(fun ω ↦ W ((q : NNReal) + s) ω i - W (q : NNReal) ω i),
                    (fun ω ↦ W (q : NNReal) ω j); μ]) := by
                      simp [X, Y, covariance_const_mul_left, covariance_const_mul_right,
                        mul_left_comm]
          _ = x i * (y j * 0) := by
                rw [hcoord_indep.covariance_eq_zero (hXcoord_mem i) (hYcoord_mem j)]
          _ = 0 := by ring
  -- Proof comment: evaluating the independent `Unit`-indexed family at `()` recovers the anchor.
  simpa [X, Y] using
    hIndepFamily.comp measurable_id (by simpa using measurable_pi_apply ())

/-- Helper for Theorem 25.39: the sufficient tail-hit event on current states and rational future
increment paths is measurable. -/
lemma restartTailHitEvent_measurable
    (y : State) (r : ℝ) :
    MeasurableSet
      {p : State × (ℚ≥0 → State) |
        dist p.1 y < r ∨
          ∃ s : ℚ≥0, 0 < (s : NNReal) ∧ dist (p.1 + p.2 s) y < r / 2} := by
  have hinside :
      MeasurableSet {p : State × (ℚ≥0 → State) | dist p.1 y < r} := by
    exact (measurable_fst.dist measurable_const) measurableSet_Iio
  have htail :
      MeasurableSet
        {p : State × (ℚ≥0 → State) |
          ∃ s : ℚ≥0, 0 < (s : NNReal) ∧ dist (p.1 + p.2 s) y < r / 2} := by
    have hUnion :
        {p : State × (ℚ≥0 → State) |
          ∃ s : ℚ≥0, 0 < (s : NNReal) ∧ dist (p.1 + p.2 s) y < r / 2} =
          ⋃ s : ℚ≥0, {p : State × (ℚ≥0 → State) |
            0 < (s : NNReal) ∧ dist (p.1 + p.2 s) y < r / 2} := by
      ext p
      simp
    rw [hUnion]
    refine MeasurableSet.iUnion fun s : ℚ≥0 ↦ ?_
    by_cases hs : 0 < (s : NNReal)
    · have hsum :
          Measurable (fun p : State × (ℚ≥0 → State) ↦ p.1 + p.2 s) := by
        exact measurable_fst.add ((measurable_pi_apply s).comp measurable_snd)
      have hdist :
          Measurable fun p : State × (ℚ≥0 → State) ↦ dist (p.1 + p.2 s) y < r / 2 :=
        (hsum.dist measurable_const).lt measurable_const
      simpa [hs] using hdist
    · simp [hs]
  change
    MeasurableSet
      ({p : State × (ℚ≥0 → State) | dist p.1 y < r} ∪
        {p : State × (ℚ≥0 → State) |
          ∃ s : ℚ≥0, 0 < (s : NNReal) ∧ dist (p.1 + p.2 s) y < r / 2})
  exact hinside.union htail

/-- Helper for Theorem 25.39: the unit interval `[m, m + 1]` contains a visit to the natural ball
of radius `n` exactly on this event. -/
def visitNatBallOnUnitIntervalEvent
    {W : VectorProcess}
    (n m : ℕ) : Set Ω :=
  {ω | ∃ t ∈ Set.Icc (m : NNReal) (m + 1), ‖W t ω‖ < n}

/-- Helper for Theorem 25.39: bounding every coordinate of a Euclidean vector by `a` bounds the
whole norm by `√d * a`. -/
lemma norm_le_sqrt_card_mul_of_forall_abs_le
    {x : State} {a : ℝ} (ha : 0 ≤ a) (hx : ∀ i : Fin d, |x i| ≤ a) :
    ‖x‖ ≤ Real.sqrt d * a := by
  have hsq :
      ‖x‖ ^ 2 ≤ (Real.sqrt d * a) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i : Fin d, x i ^ 2 ≤ ∑ i : Fin d, a ^ 2 := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have hsq_i : x i ^ 2 ≤ a ^ 2 := by
          have hxi := abs_le.mp (hx i)
          nlinarith [hxi.1, hxi.2]
        exact hsq_i
      _ = d * a ^ 2 := by
        simp
      _ = (Real.sqrt d * a) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  have hnonneg : 0 ≤ Real.sqrt d * a := by
    positivity
  nlinarith

/-- Helper for Theorem 25.39: if the Euclidean norm exceeds the positive threshold `R`, then some
coordinate already exceeds `R / √d` in absolute value. -/
lemma exists_abs_coord_gt_of_norm_gt
    (hd0 : 0 < d) {x : State} {R : ℝ} (hR_nonneg : 0 ≤ R) (hR : R < ‖x‖) :
    ∃ i : Fin d, R / Real.sqrt d < |x i| := by
  by_contra hcontra
  have hsqrt_pos : 0 < Real.sqrt d := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hd0)
  have hcoord : ∀ i : Fin d, |x i| ≤ R / Real.sqrt d := by
    intro i
    exact le_of_not_gt fun hi ↦ hcontra ⟨i, hi⟩
  have hnorm :
      ‖x‖ ≤ Real.sqrt d * (R / Real.sqrt d) :=
    norm_le_sqrt_card_mul_of_forall_abs_le
      (d := d) (x := x) (a := R / Real.sqrt d) (by positivity) hcoord
  have hsqrt_ne : Real.sqrt d ≠ 0 := hsqrt_pos.ne'
  have hcancel : Real.sqrt d * (R / Real.sqrt d) = R := by
    field_simp [hsqrt_ne]
  exact (not_le_of_gt hR) (hcancel ▸ hnorm)

/-- Helper for Theorem 25.39: every deterministic tail time is bounded above by a nonnegative
rational time. -/
lemma exists_nnrat_ge (T : NNReal) : ∃ q : ℚ≥0, T ≤ q := by
  -- Proof comment: an integer bound is enough because natural numbers embed into `ℚ≥0`.
  obtain ⟨n, hn⟩ := exists_nat_ge T
  exact ⟨n, by exact_mod_cast hn⟩

/-- Helper for Theorem 25.39: the nonnegative rationals are dense in `NNReal`. -/
lemma denseRange_nnratCast_local : DenseRange (fun q : ℚ≥0 ↦ (q : NNReal)) := by
  -- Proof comment: every open interval in `NNReal` contains a nonnegative rational point.
  refine dense_of_exists_between fun a b hab ↦ ?_
  rcases (NNReal.lt_iff_exists_rat_btwn a b).mp hab with ⟨q, hq, haq, hqb⟩
  let q₀ : ℚ≥0 := ⟨q, hq⟩
  refine ⟨(q₀ : NNReal), ?_, ?_, ?_⟩
  · exact ⟨q₀, rfl⟩
  · have hq' : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq
    simpa [q₀, Real.toNNReal_of_nonneg hq'] using haq
  · have hq' : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq
    simpa [q₀, Real.toNNReal_of_nonneg hq'] using hqb

/-- Helper for Theorem 25.39: if every basis ball around `y` is hit after every tail time, then
`y` is a cluster point of the path along `t → ∞`. -/
lemma mapClusterPt_ofTailHitsBasisBalls
    {f : NNReal → State} {y : State}
    (h :
      ∀ n : ℕ, ∀ T : NNReal, ∃ t : NNReal, T ≤ t ∧ dist (f t) y < 1 / (n + 1 : ℝ)) :
    MapClusterPt y atTop f := by
  -- Proof comment: translate the cluster-point target into closure of every tail image.
  rw [mapClusterPt_atTop_iff_forall_mem_closure]
  intro T
  -- Proof comment: in a metric space, closure is detected by arbitrarily small balls.
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hnε⟩ := exists_nat_one_div_lt hε
  rcases h n T with ⟨t, hTt, hdist⟩
  refine ⟨f t, ?_, lt_of_lt_of_le (by simpa [dist_comm] using hdist) hnε.le⟩
  exact ⟨t, hTt, rfl⟩

/-- Helper for Theorem 25.39: a path whose cluster set contains a fixed dense sequence has dense
range. -/
lemma denseRange_ofDenseSeqClusterPts
    {f : NNReal → State}
    (h : ∀ n : ℕ, MapClusterPt (TopologicalSpace.denseSeq State n) atTop f) :
    DenseRange f := by
  -- Proof comment: every nonempty open set contains some dense-sequence point, and a cluster point
  -- in that open set forces the path to meet the open set.
  have hdense : Dense (Set.range f) := by
    refine dense_iff_inter_open.2 ?_
    intro U hU hUne
    obtain ⟨n, hnU⟩ :=
      DenseRange.exists_mem_open (TopologicalSpace.denseRange_denseSeq State) hU hUne
    have hclosure :
        ∀ n : ℕ, ∀ T : NNReal,
          TopologicalSpace.denseSeq State n ∈ closure (f '' Set.Ici T) :=
      fun n ↦ (mapClusterPt_atTop_iff_forall_mem_closure).1 (h n)
    have hclosure0 :
        TopologicalSpace.denseSeq State n ∈ closure (f '' Set.Ici (0 : NNReal)) := hclosure n 0
    rw [mem_closure_iff_nhds] at hclosure0
    obtain ⟨z, hzU, hzTail⟩ := hclosure0 U (hU.mem_nhds hnU)
    rcases hzTail with ⟨t, -, rfl⟩
    exact ⟨f t, hzU, ⟨t, rfl⟩⟩
  simpa [DenseRange] using hdense

/-- Helper for Theorem 25.39: in dimensions `d ≤ 2`, almost every Brownian path re-enters each
countable basis ball around `y` after every deterministic tail time. -/
lemma deterministicStart_rationalHit_ball_ofDimensionLeTwo
    {V : VectorProcess} {x y : State} {ρ : ℝ}
    (hV : IsBrownianMotionVectorStartedAt μ V x)
    (hd : d ≤ 2) (hρ : 0 < ρ) (hρ_lt : ρ < dist x y) :
    ∀ᵐ ω ∂μ, ∃ q : ℚ≥0, 0 < (q : NNReal) ∧ dist (V (q : NNReal) ω) y < ρ := by
  let R : Set Ω := ⋃ q : ℚ≥0, {ω | 0 < (q : NNReal) ∧ dist (V (q : NNReal) ω) y < ρ}
  let H : Set Ω := {ω | (τ_[V, Metric.ball y ρ]) ω < ⊤}
  let C : Set Ω := {ω | Continuous (fun t : NNReal ↦ V t ω)}
  have hR_meas : MeasurableSet R := by
    refine MeasurableSet.iUnion fun q : ℚ≥0 ↦ ?_
    by_cases hq : 0 < (q : NNReal)
    · have hdist_meas : MeasurableSet {ω | dist (V (q : NNReal) ω) y < ρ} := by
        -- Proof comment: deterministic-time Brownian marginals are measurable in the Euclidean
        -- state space, so the distance-to-`y` event is measurable.
        exact
          ((brownianVectorStartedAt_stronglyMeasurable
              (μ := μ) (V := V) (x := x) hV (q : NNReal)).measurable.dist
            measurable_const) measurableSet_Iio
      simpa [R, hq] using hdist_meas
    · have hset :
          {ω | 0 < (q : NNReal) ∧ dist (V (q : NNReal) ω) y < ρ} = ∅ := by
        ext ω
        simp [hq]
      simp [hq]
  have hcont_coord :
      ∀ i : Fin d, ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ V t ω i) := by
    intro i
    -- Proof comment: every coordinate path is almost surely continuous under the Brownian owner.
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      (hV.isBrownianMotionStartedAt i).continuous_paths
  have hcont : ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ V t ω) := by
    -- Proof comment: continuity of the vector path is coordinatewise continuity on the finite
    -- Euclidean product.
    have hall :
        ∀ᵐ ω ∂μ, ∀ i : Fin d, Continuous (fun t : NNReal ↦ V t ω i) := by
      rw [ae_all_iff]
      intro i
      exact hcont_coord i
    filter_upwards [hall] with ω hω
    have hcoords : Continuous (fun t : NNReal ↦ fun i : Fin d ↦ V t ω i) :=
      continuous_pi fun i ↦ hω i
    simpa using (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp hcoords
  have hH_one : μ H = 1 := by
    -- Proof comment: Theorem 25.40 gives probability `1` for every deterministic start in
    -- dimensions `d ≤ 2`.
    simpa [H, if_pos hd] using
      brownian_hits_ball_probability
        (μ := ⟨μ, inferInstance⟩) (W := V) (x := x) (hW := hV)
        (r := ρ) (hr := hρ) (y := y) (hxy := hρ_lt)
  have hsubset : H ⊆ R ∪ Cᶜ := by
    intro ω hω
    by_cases hωcont : Continuous (fun t : NNReal ↦ V t ω)
    · left
      have hHit :
          ∃ t : NNReal, 0 < t ∧ V t ω ∈ Metric.ball y ρ := by
        -- Proof comment: finite strict hitting time means the path enters the open ball at some
        -- strictly positive time.
        have hnot_top : (τ_[V, Metric.ball y ρ]) ω ≠ ⊤ := ne_of_lt hω
        have hnot_avoid :
            ¬ ∀ t : NNReal, 0 < t → V t ω ∉ Metric.ball y ρ := by
          intro havoid
          exact hnot_top ((strictPositiveHittingTime_eq_top_iff V (Metric.ball y ρ) ω).2 havoid)
        push Not at hnot_avoid
        exact hnot_avoid
      rcases hHit with ⟨t, ht_pos, ht_ball⟩
      let U : Set NNReal := {s | V s ω ∈ Metric.ball y ρ} ∩ Set.Ioi 0
      have hU_open : IsOpen U := by
        -- Proof comment: continuity turns the ball hit set into an open time set, and intersecting
        -- with positive times forces the rational witness to stay strictly positive.
        refine (hωcont.isOpen_preimage _ (Metric.isOpen_ball)).inter isOpen_Ioi
      have hU_nonempty : U.Nonempty := ⟨t, ht_ball, ht_pos⟩
      obtain ⟨q, hqU⟩ := DenseRange.exists_mem_open denseRange_nnratCast_local hU_open hU_nonempty
      refine Set.mem_iUnion.2 ⟨q, ?_⟩
      simpa [U, Metric.mem_ball, and_left_comm, and_right_comm, and_assoc, and_comm, dist_comm]
        using hqU
    · right
      exact hωcont
  have hC_zero : μ Cᶜ = 0 := by
    simpa [C] using (ae_iff.1 hcont)
  have hR_one : μ R = 1 := by
    have hR_ge : 1 ≤ μ R := by
      calc
        1 = μ H := hH_one.symm
        _ ≤ μ (R ∪ Cᶜ) := measure_mono hsubset
        _ ≤ μ R + μ Cᶜ := measure_union_le _ _
        _ = μ R := by simp [hC_zero]
    have hR_le : μ R ≤ 1 := by
      calc
        μ R ≤ μ Set.univ := measure_mono (Set.subset_univ R)
        _ = 1 := measure_univ
    exact le_antisymm hR_le hR_ge
  have hR_zero : μ Rᶜ = 0 := by
    have hR_ne_top : μ R ≠ ⊤ := by
      rw [hR_one]
      simp
    simpa [hR_one, IsProbabilityMeasure.measure_univ] using measure_compl hR_meas hR_ne_top
  refine (ae_iff.2 hR_zero).mono ?_
  intro ω hω
  simpa [R] using hω

/-- Helper for Theorem 25.39: in dimensions `d ≤ 2`, almost every Brownian path re-enters each
countable basis ball around `y` after every deterministic tail time. -/
lemma aeTailHitsBasisBalls_ofDimensionLeTwo
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (hd : d ≤ 2) (y : State) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ T : NNReal, ∃ t : NNReal, T ≤ t ∧ dist (W t ω) y < 1 / (n + 1 : ℝ) := by
  have hq :
      ∀ n : ℕ, ∀ q : ℚ≥0,
        ∀ᵐ ω ∂μ, ∃ t : NNReal, (q : NNReal) ≤ t ∧ dist (W t ω) y < 1 / (n + 1 : ℝ) := by
    intro n q
    let r : ℝ := 1 / (n + 1 : ℝ)
    let X : Ω → State := fun ω ↦ W (q : NNReal) ω
    let Z : Ω → ℚ≥0 → State :=
      fun ω s ↦ W ((q : NNReal) + s) ω - W (q : NNReal) ω
    let A : Set (State × (ℚ≥0 → State)) :=
      {p |
        dist p.1 y < r ∨
          ∃ s : ℚ≥0, 0 < (s : NNReal) ∧ dist (p.1 + p.2 s) y < r / 2}
    have hr_pos : 0 < r := by
      dsimp [r]
      positivity
    have hhalf_pos : 0 < r / 2 := by
      positivity
    have hhalf_lt : r / 2 < r := by
      linarith
    have hX_meas : Measurable X := by
      simpa [X] using
        (ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable
          hW (q : NNReal)).measurable
    have hZ_meas : Measurable Z := by
      refine measurable_pi_lambda _ fun s ↦ ?_
      exact
        (ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hW
            ((q : NNReal) + s)).measurable.sub
          ((ProbabilityTheory.IsStandardBrownianMotionVector.stronglyMeasurable hW
            (q : NNReal)).measurable)
    have hA_meas : MeasurableSet A :=
      restartTailHitEvent_measurable (y := y) (r := r)
    have hsection :
        ∀ x : State, ∀ᵐ z ∂μ.map Z, (x, z) ∈ A := by
      intro x
      by_cases hinside : dist x y < r
      · -- Proof comment: if the anchor point already lies inside the target ball, no future
        -- increment is needed.
        exact Filter.Eventually.of_forall fun z ↦ Or.inl hinside
      · have hlt : r / 2 < dist x y := by
          have hle : r ≤ dist x y := le_of_not_gt hinside
          linarith
        have hdet :
            ∀ᵐ ω ∂μ, ∃ s : ℚ≥0, 0 < (s : NNReal) ∧
              dist (x + (W ((q : NNReal) + s) ω - W (q : NNReal) ω)) y < r / 2 := by
          -- Proof comment: for a deterministic start `x`, the restarted Brownian vector hits the
          -- smaller radius `r / 2` ball almost surely.
          simpa [r] using
            deterministicStart_rationalHit_ball_ofDimensionLeTwo
              (μ := μ)
              (d := d)
              (V := fun t ω ↦ x + (W ((q : NNReal) + t) ω - W (q : NNReal) ω))
              (x := x)
              (y := y)
              (ρ := r / 2)
              (translatedRestart_isBrownianVectorStartedAt
                (μ := μ) (d := d) (W := W) hW x (q : NNReal))
              hd
              hhalf_pos
              hlt
        rw [ae_map_iff hZ_meas.aemeasurable (measurable_prodMk_left hA_meas)]
        filter_upwards [hdet] with ω hω
        exact Or.inr <| by
          simpa [A, Z, add_assoc, add_left_comm, add_comm]
            using hω
    have hprod_ae_base :
        ∀ᵐ p : State × (ℚ≥0 → State) ∂((μ.map X).prod (μ.map Z)),
          dist p.1 y < r ∨ ∃ s : ℚ≥0, 0 < (s : NNReal) ∧ dist (p.1 + p.2 s) y < r / 2 := by
      -- Proof comment: every deterministic section has full future-increment measure, so the
      -- sufficient event has full product measure.
      rw [Measure.ae_prod_iff_ae_ae hA_meas]
      filter_upwards with x
      exact hsection x
    have hprod_ae :
        ∀ᵐ p : State × (ℚ≥0 → State) ∂((μ.map X).prod (μ.map Z)), p ∈ A := by
      simpa [A] using hprod_ae_base
    have hpair_map :
        μ.map (fun ω ↦ (X ω, Z ω)) = (μ.map X).prod (μ.map Z) := by
      exact
        (indepFun_iff_map_prod_eq_prod_map_map hX_meas.aemeasurable hZ_meas.aemeasurable).1
          (futureIncrementRatPath_indep_currentState (μ := μ) (W := W) hW q).symm
    have hpair_ae_base :
        ∀ᵐ ω ∂μ,
          dist (X ω) y < r ∨ ∃ s : ℚ≥0, 0 < (s : NNReal) ∧ dist (X ω + Z ω s) y < r / 2 := by
      -- Proof comment: pull the full-measure product event back along the independent pair map.
      rw [← ae_map_iff (hX_meas.aemeasurable.prodMk hZ_meas.aemeasurable) hA_meas, hpair_map]
      exact hprod_ae
    have hpair_ae : ∀ᵐ ω ∂μ, (X ω, Z ω) ∈ A := by
      simpa [A, X, Z, add_assoc, add_left_comm, add_comm] using hpair_ae_base
    refine hpair_ae.mono ?_
    intro ω hω
    rcases hω with hinside | ⟨s, hs_pos, hs_hit⟩
    · -- Proof comment: on the inside branch, the anchor time `q` already closes the target.
      exact ⟨q, le_rfl, by simpa [X, r] using hinside⟩
    · -- Proof comment: otherwise, a positive rational tail increment gives the required later hit.
      have hs_hit' : dist (W ((q : NNReal) + s) ω) y < r / 2 := by
        simpa [X, Z, add_assoc, add_left_comm, add_comm] using hs_hit
      refine ⟨(q : NNReal) + s, by simp [hs_pos.le], ?_⟩
      exact lt_of_lt_of_le hs_hit' hhalf_lt.le
  have hq_all :
      ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ q : ℚ≥0,
        ∃ t : NNReal, (q : NNReal) ≤ t ∧ dist (W t ω) y < 1 / (n + 1 : ℝ) := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro q
    simpa using hq n q
  filter_upwards [hq_all] with ω hω n T
  rcases exists_nnrat_ge T with ⟨q, hTq⟩
  rcases hω n q with ⟨t, hqt, ht⟩
  exact ⟨t, le_trans hTq hqt, ht⟩

section
omit mΩ

/-- Helper for Theorem 25.39: a visit to the radius-`n` ball during `[m, m + 1]` forces either a
small position at time `m` or a large increment somewhere on that unit interval. -/
lemma visitNatBallOnUnitInterval_subset_smallStart_or_largeIncrement
    {W : VectorProcess}
    (n m : ℕ) {a : ℝ} :
    visitNatBallOnUnitIntervalEvent (W := W) n m ⊆
      {ω | ‖W m ω‖ < n + Real.sqrt d * a} ∪
        {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1, Real.sqrt d * a < ‖W (m + u) ω - W m ω‖} := by
  intro ω hω
  rcases hω with ⟨t, ht, hball⟩
  by_cases hinc : Real.sqrt d * a < ‖W t ω - W m ω‖
  · -- Proof comment: a large fluctuation already witnesses the second alternative.
    right
    refine ⟨t - m, ?_, ?_⟩
    constructor
    · exact zero_le _
    · exact tsub_le_iff_right.mpr (by simpa [add_comm, add_left_comm, add_assoc] using ht.2)
    · have htm : (m : NNReal) + (t - m) = t := add_tsub_cancel_of_le ht.1
      simpa [htm] using hinc
  · -- Proof comment: otherwise the visit point and the increment bound force the starting point
    -- at time `m` to be small by the triangle inequality.
    left
    have hnorm :
        ‖W m ω‖ ≤ ‖W t ω‖ + ‖W t ω - W m ω‖ := by
      calc
        ‖W m ω‖ ≤ ‖W m ω - W t ω‖ + ‖W t ω‖ := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            (norm_add_le (W m ω - W t ω) (W t ω))
        _ = ‖W t ω - W m ω‖ + ‖W t ω‖ := by rw [norm_sub_rev]
        _ = ‖W t ω‖ + ‖W t ω - W m ω‖ := by ring
    have hinc_le : ‖W t ω - W m ω‖ ≤ Real.sqrt d * a := le_of_not_gt hinc
    have hsmall : ‖W t ω‖ + ‖W t ω - W m ω‖ < n + Real.sqrt d * a := by
      exact add_lt_add_of_lt_of_le hball hinc_le
    exact lt_of_le_of_lt hnorm hsmall

end

section
omit [IsProbabilityMeasure μ]

/-- Helper for Theorem 25.39: in dimensions `d > 2`, the probability that the Brownian path is
already inside the enlarged radius at the left endpoint of the `m`th unit interval is summable. -/
lemma fixedTime_coordinateIndep
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (t : NNReal) :
    iIndepFun (fun i : Fin d ↦ fun ω ↦ W t ω i) μ := by
  -- Proof comment: coordinate-path independence survives evaluation at the deterministic time `t`.
  simpa using
    hW.iIndepFun.comp
      (fun _ ↦ fun f : NNReal → ℝ ↦ f t)
      (fun _ ↦ measurable_pi_apply t)

end

section
omit mΩ

/-- Helper for Theorem 25.39: a Euclidean small-ball event is contained in the corresponding
coordinate box. -/
lemma smallStartEvent_subset_coordinateBox
    {W : VectorProcess}
    {R : ℝ} (t : NNReal) :
    {ω | ‖W t ω‖ < R} ⊆
      ⋂ i ∈ Finset.univ, (fun ω ↦ W t ω i) ⁻¹' {x : ℝ | |x| ≤ R} := by
  intro ω hω
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  intro i _
  exact le_of_lt <| lt_of_le_of_lt (by simpa using PiLp.norm_apply_le (W t ω) i) hω

end

section
omit [IsProbabilityMeasure μ]

/-- Helper for Theorem 25.39: at a fixed deterministic time, the coordinate box measure factors
as a product over the independent Brownian coordinates. -/
lemma fixedTime_coordinateBox_measure_eq_prod
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (t : NNReal) {A : Set ℝ} (hA : MeasurableSet A) :
    μ (⋂ i ∈ Finset.univ, (fun ω ↦ W t ω i) ⁻¹' A) =
      ∏ i ∈ Finset.univ, μ ((fun ω ↦ W t ω i) ⁻¹' A) := by
  -- Proof comment: the factorization is the standard finite-product formula for `iIndepFun`.
  simpa using
    (fixedTime_coordinateIndep (μ := μ) (W := W) hW t).measure_inter_preimage_eq_mul
      (Finset.univ : Finset (Fin d))
      (fun _ _ ↦ hA)

/-- Helper for Theorem 25.39: a deterministic coordinate-box estimate converts the finite
independent product bound into a real-valued `d`th-power bound. -/
lemma fixedTime_coordinateBox_toReal_le_pow
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (t : NNReal) {A : Set ℝ} (hA : MeasurableSet A) {M : ℝ} (hM_nonneg : 0 ≤ M)
    (hM :
      ∀ i : Fin d, μ ((fun ω ↦ W t ω i) ⁻¹' A) ≤ ENNReal.ofReal M) :
    (μ (⋂ i ∈ Finset.univ, (fun ω ↦ W t ω i) ⁻¹' A)).toReal ≤ M ^ d := by
  have hprod_le :
      μ (⋂ i ∈ Finset.univ, (fun ω ↦ W t ω i) ⁻¹' A) ≤
        (Finset.univ : Finset (Fin d)).prod (fun _ ↦ ENNReal.ofReal M) := by
    rw [fixedTime_coordinateBox_measure_eq_prod (μ := μ) (W := W) hW t hA]
    exact Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun i _ ↦ hM i)
  have hreal :=
    ENNReal.toReal_mono (by simp) hprod_le
  simpa [hM_nonneg] using hreal

end

/-- Helper for Theorem 25.39: the small-start event on the `m`th unit interval is bounded by the
`d`th power of the corresponding one-coordinate Gaussian box estimate. -/
lemma smallStart_probability_term_le_majorant
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (n m : ℕ) :
    let β : ℝ := ((d - 2 : ℝ) / (4 * d))
    let R : ℝ := n + Real.sqrt d * (m + 2 : ℝ) ^ β
    let M : ℝ := 2 * R / Real.sqrt (2 * Real.pi * (m + 1))
    (μ {ω | ‖W (((m + 1 : ℕ) : NNReal)) ω‖ < R}).toReal ≤ M ^ d := by
  dsimp
  let A : Set ℝ := {x : ℝ | |x| ≤ n + Real.sqrt d * (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d))}
  have hA_meas : MeasurableSet A := by
    exact measurableSet_le measurable_abs measurable_const
  have hR_nonneg :
      0 ≤ n + Real.sqrt d * (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d)) := by
    positivity
  have hM_nonneg :
      0 ≤ 2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d))) /
        Real.sqrt (2 * Real.pi * (m + 1)) := by
    positivity
  have hvar_ne : (((m + 1 : ℕ) : NNReal)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero m
  have hcoord_bound :
      ∀ i : Fin d,
        μ ((fun ω ↦ W (((m + 1 : ℕ) : NNReal)) ω i) ⁻¹' A) ≤
          ENNReal.ofReal
            (2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d))) /
              Real.sqrt (2 * Real.pi * (m + 1))) := by
    intro i
    have hLaw :
        HasLaw
          (fun ω ↦ W (((m + 1 : ℕ) : NNReal)) ω i)
          (gaussianReal 0 (((m + 1 : ℕ) : NNReal))) μ := by
      exact (hW.isBrownianMotion i).gaussian_marginal (by positivity)
    calc
      μ ((fun ω ↦ W (((m + 1 : ℕ) : NNReal)) ω i) ⁻¹' A)
        = gaussianReal 0 (((m + 1 : ℕ) : NNReal)) A := by
            rw [← Measure.map_apply_of_aemeasurable hLaw.aemeasurable hA_meas, hLaw.map_eq]
      _ ≤ ENNReal.ofReal
            (2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d))) /
              Real.sqrt (2 * Real.pi * (m + 1))) := by
            simpa [A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              IsBrownianMotion.gaussianReal_abs_le_densityHeight
                (v := (((m + 1 : ℕ) : NNReal))) hR_nonneg hvar_ne
  have hsubset :
      {ω | ‖W (((m + 1 : ℕ) : NNReal)) ω‖ <
          n + Real.sqrt d * (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d))} ⊆
        ⋂ i ∈ Finset.univ,
          (fun ω ↦ W (((m + 1 : ℕ) : NNReal)) ω i) ⁻¹' A := by
    -- Proof comment: if the Euclidean norm is inside the ball, then every coordinate lies in
    -- the corresponding interval.
    simpa [A] using
      smallStartEvent_subset_coordinateBox
        (W := W)
        (t := (((m + 1 : ℕ) : NNReal)))
        (R := n + Real.sqrt d * (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d)))
  calc
    (μ {ω | ‖W (((m + 1 : ℕ) : NNReal)) ω‖ <
        n + Real.sqrt d * (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d))}).toReal
      ≤
        (μ
          (⋂ i ∈ Finset.univ,
            (fun ω ↦ W (((m + 1 : ℕ) : NNReal)) ω i) ⁻¹' A)).toReal := by
            exact ENNReal.toReal_mono (by simp [measure_ne_top]) (measure_mono hsubset)
    _ ≤
        (2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d))) /
          Real.sqrt (2 * Real.pi * (m + 1))) ^ d := by
            exact
              fixedTime_coordinateBox_toReal_le_pow
                (μ := μ)
                (W := W)
                (hW := hW)
                (t := (((m + 1 : ℕ) : NNReal)))
                (A := A)
                hA_meas
                hM_nonneg
                hcoord_bound

/-- Helper for Theorem 25.39: the explicit fixed-time small-start majorant is bounded by a
shifted `p`-series kernel when `d > 2`. -/
lemma smallStartMajorant_le_pSeriesKernel_ofDimensionGtTwo
    (n m : ℕ) (hd : 2 < d) :
    let β : ℝ := ((d - 2 : ℝ) / (4 * d))
    let M : ℝ := 2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β) / Real.sqrt (2 * Real.pi * (m + 1))
    let C : ℝ := (2 * (n + Real.sqrt d) * (2 : ℝ) ^ β) ^ d
    M ^ d ≤ C * (((m + 1 : ℝ) ^ ((d + 2 : ℝ) / 4))⁻¹) := by
  let β : ℝ := ((d - 2 : ℝ) / (4 * d))
  dsimp
  have hdReal : (2 : ℝ) < d := by
    exact_mod_cast hd
  have hβ : 0 < β := by
    have hnum : 0 < (d : ℝ) - 2 := by
      nlinarith
    have hden : 0 < (4 : ℝ) * d := by
      nlinarith
    exact div_pos hnum hden
  have ha_one : 1 ≤ (m + 2 : ℝ) ^ β := by
    have hbase : 1 ≤ (m + 2 : ℝ) := by
      nlinarith
    exact Real.one_le_rpow hbase hβ.le
  have hsqrt_mono : Real.sqrt (m + 1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (m + 1)) := by
    apply Real.sqrt_le_sqrt
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    nlinarith
  have hM₁ :
      2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β) / Real.sqrt (2 * Real.pi * (m + 1))
        ≤
      2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β) / Real.sqrt (m + 1) := by
    have hsqrt_pos : 0 < Real.sqrt (m + 1 : ℝ) := by
      positivity
    have hsqrt_bigpos : 0 < Real.sqrt (2 * Real.pi * (m + 1)) := by
      positivity
    have hsqrt_inv :
        (Real.sqrt (2 * Real.pi * (m + 1)))⁻¹ ≤ (Real.sqrt (m + 1))⁻¹ := by
      exact (inv_le_inv₀ hsqrt_bigpos hsqrt_pos).2 hsqrt_mono
    -- Proof comment: dropping the harmless `2π` factor in the denominator yields a coarser but
    -- simpler bound.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hsqrt_inv
        (by positivity : 0 ≤ 2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β))
  have hnum_le :
      n + Real.sqrt d * (m + 2 : ℝ) ^ β ≤ (n + Real.sqrt d) * (m + 2 : ℝ) ^ β := by
    have hn_le : (n : ℝ) ≤ n * (m + 2 : ℝ) ^ β := by
      calc
        (n : ℝ) = n * 1 := by ring
        _ ≤ n * (m + 2 : ℝ) ^ β := by
              gcongr
    -- Proof comment: `a_m ≥ 1`, so the additive constant `n` is absorbed into the same power.
    calc
      n + Real.sqrt d * (m + 2 : ℝ) ^ β
        ≤ n * (m + 2 : ℝ) ^ β + Real.sqrt d * (m + 2 : ℝ) ^ β := by
            linarith
      _ = (n + Real.sqrt d) * (m + 2 : ℝ) ^ β := by
            ring
  have hM₂ :
      2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β) / Real.sqrt (m + 1)
        ≤
      2 * ((n + Real.sqrt d) * (m + 2 : ℝ) ^ β) / Real.sqrt (m + 1) := by
    have hnum₂ :
        2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β) ≤
          2 * ((n + Real.sqrt d) * (m + 2 : ℝ) ^ β) := by
      nlinarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hnum₂
        (by positivity : 0 ≤ (Real.sqrt (m + 1))⁻¹)
  have ha_two :
      (m + 2 : ℝ) ^ β ≤ (2 : ℝ) ^ β * (m + 1 : ℝ) ^ β := by
    have hbase : (m + 2 : ℝ) ≤ 2 * (m + 1 : ℝ) := by
      nlinarith
    have hpow :
        (m + 2 : ℝ) ^ β ≤ (2 * (m + 1 : ℝ)) ^ β := by
      exact Real.rpow_le_rpow (by positivity : 0 ≤ (m + 2 : ℝ)) hbase hβ.le
    calc
      (m + 2 : ℝ) ^ β ≤ (2 * (m + 1 : ℝ)) ^ β := hpow
      _ = (2 : ℝ) ^ β * (m + 1 : ℝ) ^ β := by
            rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ)) (by positivity : 0 ≤ (m + 1 : ℝ))]
  have hM₃ :
      2 * ((n + Real.sqrt d) * (m + 2 : ℝ) ^ β) / Real.sqrt (m + 1)
        ≤
      2 * ((n + Real.sqrt d) * ((2 : ℝ) ^ β * (m + 1 : ℝ) ^ β)) / Real.sqrt (m + 1) := by
    have hnum₃ :
        2 * ((n + Real.sqrt d) * (m + 2 : ℝ) ^ β) ≤
          2 * ((n + Real.sqrt d) * ((2 : ℝ) ^ β * (m + 1 : ℝ) ^ β)) := by
      gcongr
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hnum₃
        (by positivity : 0 ≤ (Real.sqrt (m + 1))⁻¹)
  have hsqrt_eq : Real.sqrt (m + 1 : ℝ) = (m + 1 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have hM₄ :
      2 * ((n + Real.sqrt d) * ((2 : ℝ) ^ β * (m + 1 : ℝ) ^ β)) / Real.sqrt (m + 1)
        =
      2 * (n + Real.sqrt d) * (2 : ℝ) ^ β * (m + 1 : ℝ) ^ (β - 1 / 2) := by
    -- Proof comment: rewrite the denominator as a negative half-power and merge exponents once.
    rw [hsqrt_eq, div_eq_mul_inv]
    rw [show ((m + 1 : ℝ) ^ (1 / 2 : ℝ))⁻¹ = (m + 1 : ℝ) ^ (-(1 / 2 : ℝ)) by
      rw [Real.rpow_neg (by positivity : 0 ≤ (m + 1 : ℝ))]]
    calc
      2 * ((n + Real.sqrt d) * ((2 : ℝ) ^ β * (m + 1 : ℝ) ^ β)) *
          (m + 1 : ℝ) ^ (-(1 / 2 : ℝ))
        = 2 * (n + Real.sqrt d) * (2 : ℝ) ^ β *
            ((m + 1 : ℝ) ^ β * (m + 1 : ℝ) ^ (-(1 / 2 : ℝ))) := by
              ring
      _ = 2 * (n + Real.sqrt d) * (2 : ℝ) ^ β * (m + 1 : ℝ) ^ (β - 1 / 2) := by
            congr 1
            rw [← Real.rpow_add (by positivity : 0 < (m + 1 : ℝ))]
            ring
  have hmajorant :
      2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β) / Real.sqrt (2 * Real.pi * (m + 1))
        ≤
      2 * (n + Real.sqrt d) * (2 : ℝ) ^ β * (m + 1 : ℝ) ^ (β - 1 / 2) := by
    have hM₄_le :
        2 * ((n + Real.sqrt d) * ((2 : ℝ) ^ β * (m + 1 : ℝ) ^ β)) / Real.sqrt (m + 1)
          ≤
        2 * (n + Real.sqrt d) * (2 : ℝ) ^ β * (m + 1 : ℝ) ^ (β - 1 / 2) :=
      le_of_eq hM₄
    exact hM₁.trans (hM₂.trans (hM₃.trans hM₄_le))
  have hpow_bound :
      (2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β) / Real.sqrt (2 * Real.pi * (m + 1))) ^ d
        ≤
      (2 * (n + Real.sqrt d) * (2 : ℝ) ^ β * (m + 1 : ℝ) ^ (β - 1 / 2)) ^ d := by
    exact
      pow_le_pow_left₀
        (by positivity :
          0 ≤ 2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β) / Real.sqrt (2 * Real.pi * (m + 1)))
        hmajorant
        d
  calc
    (2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β) / Real.sqrt (2 * Real.pi * (m + 1))) ^ d
      ≤ (2 * (n + Real.sqrt d) * (2 : ℝ) ^ β * (m + 1 : ℝ) ^ (β - 1 / 2)) ^ d := hpow_bound
    _ =
        (2 * (n + Real.sqrt d) * (2 : ℝ) ^ β) ^ d * (m + 1 : ℝ) ^ (((β - 1 / 2) : ℝ) * d) := by
          rw [mul_pow]
          have hbase : 0 ≤ (m + 1 : ℝ) := by
            positivity
          have hpow :
              ((m + 1 : ℝ) ^ (β - 1 / 2)) ^ d = (m + 1 : ℝ) ^ (((β - 1 / 2) : ℝ) * d) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
          rw [hpow]
    _ =
        (2 * (n + Real.sqrt d) * (2 : ℝ) ^ β) ^ d *
          (((m + 1 : ℝ) ^ ((d + 2 : ℝ) / 4))⁻¹) := by
            have hbase : 0 ≤ (m + 1 : ℝ) := by
              positivity
            have hexp : (((β - 1 / 2) : ℝ) * d) = -((d + 2 : ℝ) / 4) := by
              dsimp [β]
              field_simp [show (d : ℝ) ≠ 0 by positivity]
              ring
            rw [hexp, Real.rpow_neg hbase]

/-- Helper for Theorem 25.39: in dimensions `d > 2`, the probability that the Brownian path is
already inside the enlarged radius at the left endpoint of the `m`th unit interval is summable. -/
lemma smallStart_probability_summable_ofDimensionGtTwo
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (n : ℕ) (hd : 2 < d) :
    let a : ℕ → ℝ := fun m ↦ (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d))
    Summable
      (fun m : ℕ ↦
        (μ {ω | ‖W (((m + 1 : ℕ) : NNReal)) ω‖ < n + Real.sqrt d * a m}).toReal) := by
  let β : ℝ := ((d - 2 : ℝ) / (4 * d))
  let a : ℕ → ℝ := fun m ↦ (m + 2 : ℝ) ^ β
  let C : ℝ := (2 * (n + Real.sqrt d) * (2 : ℝ) ^ β) ^ d
  have hp : 1 < ((d + 2 : ℝ) / 4) := by
    have hd' : (2 : ℝ) < d := by
      exact_mod_cast hd
    nlinarith
  have hkernel :
      Summable (fun m : ℕ ↦ (((m + 1 : ℝ) ^ ((d + 2 : ℝ) / 4))⁻¹)) := by
    -- Proof comment: the deterministic target is a shifted `p`-series with exponent
    -- `((d + 2) / 4) > 1`.
    simpa using
      ((_root_.summable_nat_add_iff 1).2 ((Real.summable_nat_rpow_inv).2 hp))
  have hdom :
      ∀ m : ℕ,
        (μ {ω | ‖W (((m + 1 : ℕ) : NNReal)) ω‖ < n + Real.sqrt d * a m}).toReal
          ≤ C * (((m + 1 : ℝ) ^ ((d + 2 : ℝ) / 4))⁻¹) := by
    intro m
    -- Proof comment: first pass to the coordinate-box Gaussian estimate, then apply the coarse
    -- deterministic normalization from the previous lemma.
    calc
      (μ {ω | ‖W (((m + 1 : ℕ) : NNReal)) ω‖ < n + Real.sqrt d * a m}).toReal
        ≤
          (2 * (n + Real.sqrt d * (m + 2 : ℝ) ^ β) /
            Real.sqrt (2 * Real.pi * (m + 1))) ^ d := by
              simpa [a, β] using
                smallStart_probability_term_le_majorant
                  (μ := μ) (W := W) hW n m
      _ ≤ C * (((m + 1 : ℝ) ^ ((d + 2 : ℝ) / 4))⁻¹) := by
            simpa [C, β] using
              smallStartMajorant_le_pSeriesKernel_ofDimensionGtTwo
                (d := d) n m hd
  have hseries :
      Summable
        (fun m : ℕ ↦ C * (((m + 1 : ℝ) ^ ((d + 2 : ℝ) / 4))⁻¹)) := by
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using hkernel.mul_left C
  exact Summable.of_nonneg_of_le (fun _ ↦ ENNReal.toReal_nonneg) hdom hseries

/-- Helper for Theorem 25.39: the exponential tail attached to the threshold
`(m + 2)^β` is eventually dominated by the inverse-square tail `(m + 2)⁻²`. -/
lemma expQuadraticTail_eventually_le_inverseSquare
    {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp (-((((m + 2 : ℝ) ^ β) ^ (2 : ℕ))) / 2) ≤ (m + 2 : ℝ) ^ (-2 : ℝ) := by
  have hDecayInput :
      Tendsto (fun m : ℕ ↦ (m + 2 : ℝ) ^ (2 * β)) atTop atTop := by
    -- Proof comment: the polynomial threshold itself tends to `∞` because `β > 0`.
    exact
      (tendsto_rpow_atTop (by positivity : 0 < 2 * β)).comp
        (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hDecayAux :
      Tendsto
        (fun x : ℝ ↦ x ^ (1 / β) * Real.exp (-(1 / 2 : ℝ) * x))
        atTop
        (𝓝 0) := by
    -- Proof comment: exponential decay dominates every positive power at `∞`.
    exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / β) (1 / 2 : ℝ) (by positivity)
  have hPowEq :
      ∀ m : ℕ, ((m + 2 : ℝ) ^ (2 * β)) ^ (1 / β) = (m + 2 : ℝ) ^ (2 : ℝ) := by
    intro m
    rw [← Real.rpow_mul (by positivity : 0 ≤ (m + 2 : ℝ))]
    have hmul : (2 * β) * (1 / β) = (2 : ℝ) := by
      field_simp [hβ.ne']
    rw [hmul]
  have hDecay :
      Tendsto
        (fun m : ℕ ↦ (m + 2 : ℝ) ^ (2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * ((m + 2 : ℝ) ^ (2 * β))))
        atTop
        (𝓝 0) := by
    -- Proof comment: specialize the generic decay lemma at the quadratic threshold
    -- `((m + 2)^β)^2 = (m + 2)^(2β)`.
    refine Tendsto.congr' ?_ (hDecayAux.comp hDecayInput)
    exact Filter.Eventually.of_forall fun m ↦ by
      simpa [Function.comp] using
        congrArg
          (fun z : ℝ ↦ z * Real.exp (-(1 / 2 : ℝ) * ((m + 2 : ℝ) ^ (2 * β))))
          (hPowEq m)
  have hsmall :
      ∀ᶠ m : ℕ in atTop,
        (m + 2 : ℝ) ^ (2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * ((m + 2 : ℝ) ^ (2 * β))) < 1 :=
    hDecay.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall] with m hm
  have hpow_pos : 0 < (m + 2 : ℝ) ^ (2 : ℝ) := by
    positivity
  have hdiv :
      Real.exp (-(1 / 2 : ℝ) * ((m + 2 : ℝ) ^ (2 * β))) ≤ 1 / (m + 2 : ℝ) ^ (2 : ℝ) := by
    have hm' :
        Real.exp (-(1 / 2 : ℝ) * ((m + 2 : ℝ) ^ (2 * β))) * (m + 2 : ℝ) ^ (2 : ℝ) < 1 := by
      simpa [mul_comm] using hm
    exact (le_div_iff₀ hpow_pos).2 hm'.le
  have hrewrite :
      1 / (m + 2 : ℝ) ^ (2 : ℝ) = (m + 2 : ℝ) ^ (-2 : ℝ) := by
    simpa [one_div] using
      (Real.rpow_neg (by positivity : 0 ≤ (m + 2 : ℝ)) (2 : ℝ)).symm
  have hexp_rewrite :
      Real.exp (-((((m + 2 : ℝ) ^ β) ^ (2 : ℕ))) / 2) =
        Real.exp (-(1 / 2 : ℝ) * ((m + 2 : ℝ) ^ (2 * β))) := by
    congr 1
    have hpow :
        (((m + 2 : ℝ) ^ β) ^ (2 : ℕ)) = (m + 2 : ℝ) ^ (2 * β) := by
      calc
        (((m + 2 : ℝ) ^ β) ^ (2 : ℕ)) = (((m + 2 : ℝ) ^ β) ^ (2 : ℝ)) := by simp
        _ = (m + 2 : ℝ) ^ (β * 2) := by
              rw [← Real.rpow_mul (by positivity : 0 ≤ (m + 2 : ℝ))]
        _ = (m + 2 : ℝ) ^ (2 * β) := by congr 1; ring
    rw [hpow]
    ring_nf
  rw [hexp_rewrite]
  exact hrewrite ▸ hdiv

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 25.39: a real Brownian motion hits a positive level before time `1` with
probability at most `exp (-(r ^ 2) / 2)`. -/
lemma brownianLevelHittingBeforeOne_toReal_le_expNegHalfSq
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {r : ℝ} (hr : 0 < r) :
    (μ {ω | brownianLevelHittingTime B r ω ≤ 1}).toReal ≤ Real.exp (-(r ^ 2) / 2) := by
  let l : NNReal := ⟨r ^ 2 / 2, by positivity⟩
  let f : Ω → ℝ := fun ω ↦ Real.exp (-((l : ℝ) * (brownianLevelHittingTime B r ω).toReal))
  let A : Set Ω := {ω | brownianLevelHittingTime B r ω ≤ 1}
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hτ_meas :
      AEMeasurable (fun ω ↦ (brownianLevelHittingTime B r ω).toReal) μ :=
    aemeasurable_brownianLevelHittingTime_toReal hB r
  have hExp_meas : Measurable fun x : ℝ ↦ Real.exp (-((l : ℝ) * x)) := by
    fun_prop
  have hf_aemeas : AEMeasurable f μ := by
    exact hExp_meas.aemeasurable.comp_aemeasurable hτ_meas
  have hf_nonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards with ω
    exact (Real.exp_pos _).le
  have hf_int : Integrable f μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hf_aemeas.aestronglyMeasurable ?_
    filter_upwards with ω
    have hτ_nonneg : 0 ≤ (brownianLevelHittingTime B r ω).toReal := ENNReal.toReal_nonneg
    have hl_nonneg : 0 ≤ (l : ℝ) := by positivity
    have hnonpos : -((l : ℝ) * (brownianLevelHittingTime B r ω).toReal) ≤ 0 := by
      nlinarith [mul_nonneg hl_nonneg hτ_nonneg]
    have hExp_le : Real.exp (-((l : ℝ) * (brownianLevelHittingTime B r ω).toReal)) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr hnonpos
    simpa [f, abs_of_nonneg (Real.exp_pos _).le] using hExp_le
  have hA_subset : A ⊆ {ω | Real.exp (-(l : ℝ)) ≤ f ω} := by
    intro ω hω
    have hτ_ne_top : brownianLevelHittingTime B r ω ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt hω (by simp))
    have hτ_le_one :
        (brownianLevelHittingTime B r ω).toReal ≤ 1 := by
      exact (ENNReal.toReal_le_toReal hτ_ne_top ENNReal.one_ne_top).2 hω
    have hmono :
        -(l : ℝ) ≤ -((l : ℝ) * (brownianLevelHittingTime B r ω).toReal) := by
      have hl_nonneg : 0 ≤ (l : ℝ) := by positivity
      nlinarith
    exact Real.exp_le_exp.mpr hmono
  have hA_bound :
      Real.exp (-(l : ℝ)) * (μ A).toReal ≤ ∫ ω, f ω ∂μ := by
    have hmarkov :
        Real.exp (-(l : ℝ)) * μ.real {ω | Real.exp (-(l : ℝ)) ≤ f ω} ≤ ∫ ω, f ω ∂μ := by
      simpa [f] using
        MeasureTheory.mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int (Real.exp (-(l : ℝ)))
    have hA_le :
        (μ A).toReal ≤ μ.real {ω | Real.exp (-(l : ℝ)) ≤ f ω} := by
      simpa [MeasureTheory.Measure.real_def, A] using
        (ENNReal.toReal_mono
          (measure_ne_top μ {ω | Real.exp (-(l : ℝ)) ≤ f ω})
          (measure_mono hA_subset))
    calc
      Real.exp (-(l : ℝ)) * (μ A).toReal
          ≤ Real.exp (-(l : ℝ)) * μ.real {ω | Real.exp (-(l : ℝ)) ≤ f ω} := by
              gcongr
      _ ≤ ∫ ω, f ω ∂μ := hmarkov
  have hInt :
      ∫ ω, f ω ∂μ = Real.exp (-(r ^ 2)) := by
    have hsqrt : Real.sqrt (2 * (l : ℝ)) = r := by
      rw [show 2 * (l : ℝ) = r ^ 2 by
        change 2 * (r ^ 2 / 2) = r ^ 2
        ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hr]
    calc
      ∫ ω, f ω ∂μ
          =
            ∫ x : ℝ,
              Real.exp (-((l : ℝ) * x)) ∂(brownianLevelHittingTimeLaw hB r : Measure ℝ) := by
                symm
                rw [brownianLevelHittingTimeLaw_toMeasure]
                simpa [f] using
                  (MeasureTheory.integral_map hτ_meas
                    (by
                      simpa using hExp_meas.aestronglyMeasurable))
      _ = Real.exp (-r * Real.sqrt (2 * (l : ℝ))) := by
            simpa using brownianLevelHittingTime_laplaceTransform (hB := hB) (hb := hr) (l := l)
      _ = Real.exp (-(r ^ 2)) := by
            rw [hsqrt]
            ring_nf
  have hε_pos : 0 < Real.exp (-(l : ℝ)) := Real.exp_pos _
  have hA_final :
      (μ A).toReal ≤ Real.exp (-(r ^ 2) / 2) := by
    have hdiv :
        (μ A).toReal ≤ Real.exp (-(r ^ 2)) / Real.exp (-(l : ℝ)) := by
      have hA_bound' : (μ A).toReal * Real.exp (-(l : ℝ)) ≤ Real.exp (-(r ^ 2)) := by
        simpa [mul_comm] using hA_bound.trans_eq hInt
      exact (le_div_iff₀ hε_pos).2 hA_bound'
    calc
      (μ A).toReal ≤ Real.exp (-(r ^ 2)) / Real.exp (-(l : ℝ)) := hdiv
      _ = Real.exp (-(r ^ 2) / 2) := by
            rw [← Real.exp_sub]
            congr 1
            change -(r ^ 2) - -(r ^ 2 / 2) = -(r ^ 2) / 2
            ring
  simpa [A] using hA_final

/-- Helper for Theorem 25.39: a real Brownian motion exceeds a positive level somewhere on
`[0, 1]` with probability at most `exp (-(r ^ 2) / 2)`. -/
lemma brownianRunningSupAboveLevelOnUnitInterval_toReal_le_expNegHalfSq
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {r : ℝ} (hr : 0 < r) :
    (μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1, r < B u ω}).toReal ≤ Real.exp (-(r ^ 2) / 2) := by
  let A : Set Ω := {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1, r < B u ω}
  let H : Set Ω := {ω | brownianLevelHittingTime B r ω ≤ 1}
  let C : Set Ω := {ω | Continuous (fun t : NNReal ↦ B t ω)}
  have hsubset : A ⊆ H ∪ Cᶜ := by
    intro ω hω
    by_cases hωcont : Continuous (fun t : NNReal ↦ B t ω)
    · left
      rcases hω with ⟨u, hu, hu_gt⟩
      have hzero : B 0 ω = 0 := by
        simpa using congrFun hB.zero ω
      have hr_mem : r ∈ Set.Icc (B 0 ω) (B u ω) := by
        refine ⟨?_, hu_gt.le⟩
        simpa [hzero] using hr.le
      obtain ⟨s, hsIcc, hs_eq⟩ :=
        (intermediate_value_Icc
          (a := (0 : NNReal))
          (b := u)
          hu.1
          hωcont.continuousOn) hr_mem
      have hτ_le_s : brownianLevelHittingTime B r ω ≤ s :=
        brownianLevelHittingTime_le_of_eq hs_eq
      have hτ_le_one : brownianLevelHittingTime B r ω ≤ (1 : ENNReal) := by
        exact le_trans hτ_le_s (by exact_mod_cast hsIcc.2.trans hu.2)
      simpa [H] using hτ_le_one
    · right
      exact hωcont
  have hC_zero : μ Cᶜ = 0 := by
    simpa [C, HasAlmostSurelyContinuousPaths, processPath] using (ae_iff.1 hB.continuous_paths)
  have hA_le :
      (μ A).toReal ≤ (μ H).toReal := by
    calc
      (μ A).toReal ≤ (μ (H ∪ Cᶜ)).toReal := by
            exact ENNReal.toReal_mono (by simp [measure_ne_top]) (measure_mono hsubset)
      _ ≤ (μ H + μ Cᶜ).toReal := by
            exact ENNReal.toReal_mono (by simp [measure_ne_top]) (measure_union_le _ _)
      _ = (μ H).toReal := by
            simp [hC_zero]
  exact hA_le.trans <|
    brownianLevelHittingBeforeOne_toReal_le_expNegHalfSq (μ := μ) (B := B) hB hr

/-- Helper for Theorem 25.39: on a shifted unit interval, one coordinate increment exceeding a
positive threshold in absolute value has an exponentially small Gaussian tail. -/
lemma coordinateIncrementSupAbs_toReal_le_expNegHalfSq
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (i : Fin d) (m : ℕ) {r : ℝ} (hr : 0 < r) :
    (μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
      r < |W ((m + 1) + u) ω i - W (m + 1) ω i|}).toReal ≤
      2 * Real.exp (-(r ^ 2) / 2) := by
  -- Proof comment: restart the coordinate Brownian motion at time `m + 1`, split the absolute
  -- event into positive and negative branches, and bound each branch through the Brownian
  -- level-hitting-time Laplace transform on `[0, 1]`.
  let B : NNReal → Ω → ℝ := fun t ω ↦ W ((m + 1 : ℕ) + t) ω i - W (m + 1) ω i
  let Eabs : Set Ω := {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1, r < |B u ω|}
  let Eplus : Set Ω := {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1, r < B u ω}
  let Bminus : NNReal → Ω → ℝ := brownianScaling B (-1)
  let Eminus : Set Ω := {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1, r < Bminus u ω}
  have hB : IsBrownianMotion μ B := by
    simpa [B, add_assoc, add_left_comm, add_comm] using
      shiftedIncrement_isBrownianMotion
        (μ := μ) (B := fun t ω ↦ W t ω i) (hB := hW.isBrownianMotion i) (T := (m + 1 : ℕ))
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: the negative branch is the reflected Brownian motion obtained by scaling
    -- with factor `-1`.
    simpa [Bminus, brownianScaling] using
      (IsBrownianMotion.scaling hB (K := (-1 : ℝ)) (by norm_num))
  have hsubset : Eabs ⊆ Eplus ∪ Eminus := by
    intro ω hω
    rcases hω with ⟨u, hu, huabs⟩
    by_cases hnonneg : 0 ≤ B u ω
    · left
      exact ⟨u, hu, by simpa [Eplus, Eabs, abs_of_nonneg hnonneg] using huabs⟩
    · right
      have hltneg : r < -B u ω := by
        simpa [abs_of_neg (lt_of_not_ge hnonneg)] using huabs
      refine ⟨u, hu, ?_⟩
      simpa [Eminus, Bminus, brownianScaling, hscaleTime] using hltneg
  have hplus_tail :
      (μ Eplus).toReal ≤ Real.exp (-(r ^ 2) / 2) := by
    simpa [Eplus] using
      brownianRunningSupAboveLevelOnUnitInterval_toReal_le_expNegHalfSq
        (μ := μ) (B := B) hB hr
  have hminus_tail :
      (μ Eminus).toReal ≤ Real.exp (-(r ^ 2) / 2) := by
    simpa [Eminus] using
      brownianRunningSupAboveLevelOnUnitInterval_toReal_le_expNegHalfSq
        (μ := μ) (B := Bminus) hBminus hr
  have hunion :
      (μ Eabs).toReal ≤ (μ Eplus).toReal + (μ Eminus).toReal := by
    calc
      (μ Eabs).toReal ≤ (μ (Eplus ∪ Eminus)).toReal := by
            exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsubset)
      _ ≤ (μ Eplus + μ Eminus).toReal := by
            exact ENNReal.toReal_mono (by simp [measure_ne_top]) (measure_union_le _ _)
      _ = (μ Eplus).toReal + (μ Eminus).toReal := by
            rw [ENNReal.toReal_add (by simp [measure_ne_top]) (by simp [measure_ne_top])]
  calc
    (μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
      r < |W ((m + 1) + u) ω i - W (m + 1) ω i|}).toReal = (μ Eabs).toReal := by
        simp [Eabs, B]
    _ ≤ (μ Eplus).toReal + (μ Eminus).toReal := hunion
    _ ≤ Real.exp (-(r ^ 2) / 2) + Real.exp (-(r ^ 2) / 2) := by
          gcongr
    _ = 2 * Real.exp (-(r ^ 2) / 2) := by ring

/-- Helper for Theorem 25.39: the norm-increment event on one unit interval is bounded by the
finite union of coordinate increment tails. -/
lemma largeIncrement_probability_term_le_coordinateGaussianTail
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (m : ℕ) :
    let β : ℝ := ((d - 2 : ℝ) / (4 * d))
    let a : ℝ := (m + 2 : ℝ) ^ β
    (μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
      Real.sqrt d * a < ‖W ((m + 1) + u) ω - W (m + 1) ω‖}).toReal ≤
      d * (2 * Real.exp (-(a ^ 2) / 2)) := by
  let β : ℝ := ((d - 2 : ℝ) / (4 * d))
  let a : ℝ := (m + 2 : ℝ) ^ β
  by_cases hd0 : d = 0
  · subst hd0
    -- Proof comment: in dimension `0`, the Euclidean state space is trivial, so the norm event is
    -- empty and the right-hand side is also zero.
    have hempty :
        {ω | ∃ u ≤ (1 : NNReal),
          W ((m + 1) + u) ω - W (m + 1) ω ≠ (0 : EuclideanSpace ℝ (Fin 0))} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, hu, huω⟩
      exact huω (Subsingleton.elim _ _)
    simp [hempty]
  let E : Set Ω :=
    {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
      Real.sqrt d * a < ‖W ((m + 1) + u) ω - W (m + 1) ω‖}
  let Ei : Fin d → Set Ω := fun i ↦
    {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
      a < |W ((m + 1) + u) ω i - W (m + 1) ω i|}
  have hd0_nat : 0 < d := by
    exact Nat.pos_iff_ne_zero.mpr hd0
  have hsqrt_ne : Real.sqrt d ≠ 0 := by
    exact (Real.sqrt_pos.2 (by exact_mod_cast hd0_nat)).ne'
  have ha_pos : 0 < a := by
    exact Real.rpow_pos_of_pos (by positivity : 0 < (m + 2 : ℝ)) β
  have hsubset : E ⊆ ⋃ i : Fin d, Ei i := by
    intro ω hω
    rcases hω with ⟨u, hu, hunorm⟩
    have hcoord :
        ∃ i : Fin d,
          (Real.sqrt d * a) / Real.sqrt d <
            |(W ((m + 1) + u) ω - W (m + 1) ω) i| := by
      exact
        exists_abs_coord_gt_of_norm_gt
          (d := d)
          hd0_nat
          (x := W ((m + 1) + u) ω - W (m + 1) ω)
          (R := Real.sqrt d * a)
          (by positivity)
          hunorm
    rcases hcoord with ⟨i, hi⟩
    have hcancel : (Real.sqrt d * a) / Real.sqrt d = a := by
      field_simp [hsqrt_ne]
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    refine ⟨u, hu, ?_⟩
    simpa [Ei, E, a, hcancel] using hi
  have hunion :
      (μ E).toReal ≤ ∑ i : Fin d, (μ (Ei i)).toReal := by
    calc
      (μ E).toReal ≤ (μ (⋃ i : Fin d, Ei i)).toReal := by
            exact ENNReal.toReal_mono (by simp [measure_ne_top]) (measure_mono hsubset)
      _ ≤ ∑ i : Fin d, (μ (Ei i)).toReal := by
            simpa [MeasureTheory.Measure.real_def, Ei] using
              MeasureTheory.measureReal_iUnion_fintype_le (μ := μ) Ei
  calc
    (μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
      Real.sqrt d * a < ‖W ((m + 1) + u) ω - W (m + 1) ω‖}).toReal
      = (μ E).toReal := by
          rfl
    _ ≤ ∑ i : Fin d, (μ (Ei i)).toReal := hunion
    _ ≤ ∑ i : Fin d, 2 * Real.exp (-(a ^ 2) / 2) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          simpa [Ei, a] using
            coordinateIncrementSupAbs_toReal_le_expNegHalfSq
              (μ := μ) (W := W) hW i m ha_pos
    _ = d * (2 * Real.exp (-(a ^ 2) / 2)) := by
          simp

/-- Helper for Theorem 25.39: the scalar Gaussian tail kernel produced by the coordinate-union
bound is summable when `d > 2`. -/
lemma largeIncrementGaussianTail_summable_ofDimensionGtTwo
    (hd : 2 < d) :
    let β : ℝ := ((d - 2 : ℝ) / (4 * d))
    let a : ℕ → ℝ := fun m ↦ (m + 2 : ℝ) ^ β
    Summable (fun m : ℕ ↦ d * (2 * Real.exp (-((a m) ^ 2) / 2))) := by
  let β : ℝ := ((d - 2 : ℝ) / (4 * d))
  let a : ℕ → ℝ := fun m ↦ (m + 2 : ℝ) ^ β
  let C : ℝ := d * 2
  have hdReal : (2 : ℝ) < d := by
    exact_mod_cast hd
  have hβ : 0 < β := by
    have hnum : 0 < (d : ℝ) - 2 := by
      nlinarith
    have hden : 0 < (4 : ℝ) * d := by
      nlinarith
    exact div_pos hnum hden
  have hkernel :
      Summable (fun m : ℕ ↦ C * (m + 2 : ℝ) ^ (-2 : ℝ)) := by
    have hbase :
        Summable (fun m : ℕ ↦ (m + 2 : ℝ) ^ (-2 : ℝ)) := by
      simpa [one_div, Real.rpow_natCast] using
        ((_root_.summable_nat_add_iff 2).2
          ((Real.summable_nat_rpow_inv).2 (by norm_num : 1 < (2 : ℝ))))
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using hbase.mul_left C
  refine
    Summable.of_norm_bounded_eventually_nat
      (g := fun m ↦ C * (m + 2 : ℝ) ^ (-2 : ℝ)) hkernel ?_
  filter_upwards [expQuadraticTail_eventually_le_inverseSquare (β := β) hβ] with m hm
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have htail :
      d * (2 * Real.exp (-((a m) ^ 2) / 2)) ≤ C * (m + 2 : ℝ) ^ (-2 : ℝ) := by
    calc
      d * (2 * Real.exp (-((a m) ^ 2) / 2))
          = C * Real.exp (-((a m) ^ 2) / 2) := by
              simp [C, mul_assoc]
      _ ≤ C * (m + 2 : ℝ) ^ (-2 : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by simpa [a] using hm) hC_nonneg
  have hnonneg :
      0 ≤ d * (2 * Real.exp (-((a m) ^ 2) / 2)) := by
    positivity
  have hbound :
      ‖d * (2 * Real.exp (-((a m) ^ 2) / 2))‖ ≤ C * (m + 2 : ℝ) ^ (-2 : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using htail
  exact hbound

/-- Helper for Theorem 25.39: in dimensions `d > 2`, the large-increment probabilities on the
shifted unit intervals are summable. -/
lemma largeIncrement_probability_summable_ofDimensionGtTwo
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (hd : 2 < d) :
    let a : ℕ → ℝ := fun m ↦ (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d))
    Summable
      (fun m : ℕ ↦
        (μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
          Real.sqrt d * a m < ‖W ((m + 1) + u) ω - W (m + 1) ω‖}).toReal) := by
  let β : ℝ := ((d - 2 : ℝ) / (4 * d))
  let a : ℕ → ℝ := fun m ↦ (m + 2 : ℝ) ^ β
  let g : ℕ → ℝ := fun m ↦ d * (2 * Real.exp (-(((m + 2 : ℝ) ^ β) ^ 2) / 2))
  have hdom :
      ∀ m : ℕ,
        (μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
          Real.sqrt d * a m < ‖W ((m + 1) + u) ω - W (m + 1) ω‖}).toReal ≤ g m := by
    intro m
    -- Proof comment: reduce the vector event to the finite coordinate union, then use the scalar
    -- reflection-principle bound on each coordinate.
    simpa [a, g, β] using
      largeIncrement_probability_term_le_coordinateGaussianTail
        (μ := μ) (W := W) hW m
  have hsum : Summable g := by
    simpa [g, β] using
      largeIncrementGaussianTail_summable_ofDimensionGtTwo (d := d) hd
  exact Summable.of_nonneg_of_le (fun _ ↦ ENNReal.toReal_nonneg) hdom hsum

/-- Helper for Theorem 25.39: in dimensions `d > 2`, the shifted unit-interval visit events of a
fixed natural ball have summable probabilities. -/
lemma visitNatBallOnUnitInterval_tsum_ne_top_ofDimensionGtTwo
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (n : ℕ) (hd : 2 < d) :
    (∑' m : ℕ, μ (visitNatBallOnUnitIntervalEvent (W := W) n (m + 1))) ≠ ⊤ := by
  -- Route correction: the transience proof is now organized around deterministic unit intervals,
  -- not stopping-time restarts. The remaining missing step is the explicit series estimate on
  -- these visit probabilities.
  let a : ℕ → ℝ := fun m ↦ (m + 2 : ℝ) ^ ((d - 2 : ℝ) / (4 * d))
  have hsplit :
      ∀ m : ℕ,
        visitNatBallOnUnitIntervalEvent (W := W) n (m + 1) ⊆
          {ω | ‖W (m + 1) ω‖ < n + Real.sqrt d * a m} ∪
            {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
                Real.sqrt d * a m < ‖W ((m + 1) + u) ω - W (m + 1) ω‖} := by
    intro m
    simpa [a, add_assoc, add_left_comm, add_comm] using
      visitNatBallOnUnitInterval_subset_smallStart_or_largeIncrement
        (W := W) (n := n) (m := m + 1) (a := a m)
  have hsmall :
      Summable
        (fun m : ℕ ↦
          (μ {ω | ‖W (m + 1) ω‖ < n + Real.sqrt d * a m}).toReal) := by
    -- Proof comment: this is exactly the endpoint small-ball series estimate proved just above.
    simpa [a] using
      smallStart_probability_summable_ofDimensionGtTwo
        (μ := μ) (W := W) (hW := hW) n hd
  have hlarge :
      Summable
        (fun m : ℕ ↦
          (μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
            Real.sqrt d * a m < ‖W ((m + 1) + u) ω - W (m + 1) ω‖}).toReal) := by
    -- Proof comment: the increment series is exactly the one-dimensional reflection-principle
    -- estimate packaged in the dedicated large-increment helper.
    simpa [a] using
      largeIncrement_probability_summable_ofDimensionGtTwo
        (μ := μ) (W := W) (hW := hW) hd
  have hreal :
      Summable
        (fun m ↦ (μ (visitNatBallOnUnitIntervalEvent (W := W) n (m + 1))).toReal) := by
    refine Summable.of_nonneg_of_le (fun m ↦ ENNReal.toReal_nonneg) (fun m ↦ ?_) (hsmall.add hlarge)
    have hmeasure_le :
        μ (visitNatBallOnUnitIntervalEvent (W := W) n (m + 1)) ≤
          μ {ω | ‖W (m + 1) ω‖ < n + Real.sqrt d * a m} +
            μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
              Real.sqrt d * a m < ‖W ((m + 1) + u) ω - W (m + 1) ω‖} := by
      exact le_trans (measure_mono (hsplit m)) (measure_union_le _ _)
    have htoReal_le :
        (μ (visitNatBallOnUnitIntervalEvent (W := W) n (m + 1))).toReal ≤
          (μ {ω | ‖W (m + 1) ω‖ < n + Real.sqrt d * a m} +
            μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
              Real.sqrt d * a m < ‖W ((m + 1) + u) ω - W (m + 1) ω‖}).toReal := by
      exact ENNReal.toReal_mono (by simp [measure_ne_top]) hmeasure_le
    calc
      (μ (visitNatBallOnUnitIntervalEvent (W := W) n (m + 1))).toReal
          ≤ (μ {ω | ‖W (m + 1) ω‖ < n + Real.sqrt d * a m} +
              μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
                Real.sqrt d * a m < ‖W ((m + 1) + u) ω - W (m + 1) ω‖}).toReal :=
            htoReal_le
      _ =
          (μ {ω | ‖W (m + 1) ω‖ < n + Real.sqrt d * a m}).toReal +
            (μ {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
              Real.sqrt d * a m < ‖W ((m + 1) + u) ω - W (m + 1) ω‖}).toReal := by
            simp [ENNReal.toReal_add, measure_ne_top]
  -- Proof comment: convert the real-valued summability of the visit probabilities back to the
  -- finiteness of the ENNReal total mass needed for Borel-Cantelli.
  simpa [ENNReal.ofReal_toReal, measure_ne_top] using hreal.tsum_ofReal_ne_top

/-- Helper for Theorem 25.39: in dimensions `d > 2`, almost every Brownian path is eventually
outside each fixed natural-radius ball around the origin. -/
lemma aeEventuallyOutsideNatBalls_ofDimensionGtTwo
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (hd : 2 < d) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, ∃ T : NNReal, ∀ t : NNReal, T ≤ t → (n : ℝ) ≤ ‖W t ω‖ := by
  -- Proof comment: first Borel-Cantelli turns the summable unit-interval visit probabilities into
  -- eventual absence of visits on all sufficiently late intervals, and then a floor argument
  -- upgrades this to a tail lower bound on the norm.
  rw [ae_all_iff]
  intro n
  let A : ℕ → Set Ω := fun m ↦ visitNatBallOnUnitIntervalEvent (W := W) n (m + 1)
  have hA_tsum : (∑' m : ℕ, μ (A m)) ≠ ⊤ := by
    simpa [A] using
      visitNatBallOnUnitInterval_tsum_ne_top_ofDimensionGtTwo
        (μ := μ) (W := W) (hW := hW) n hd
  have hAevent :
      ∀ᵐ ω ∂μ, ∀ᶠ m : ℕ in atTop, ω ∉ A m := by
    simpa [A] using MeasureTheory.ae_eventually_notMem (μ := μ) (s := A) hA_tsum
  filter_upwards [hAevent] with ω hω
  rcases Filter.eventually_atTop.1 hω with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro t ht
  let k : ℕ := Nat.floor (t : ℝ)
  have hk_ge : N + 1 ≤ k := by
    have hreal : (((N + 1 : ℕ) : ℝ)) ≤ (t : ℝ) := by
      exact_mod_cast ht
    exact Nat.le_floor hreal
  have hk_le_t : (k : NNReal) ≤ t := by
    exact_mod_cast Nat.floor_le t.2
  have ht_lt : t < (k + 1 : ℕ) := by
    simpa [k] using Nat.lt_floor_add_one (t : ℝ)
  by_contra hnorm
  have hk_pos : 0 < k := lt_of_lt_of_le (Nat.succ_pos N) hk_ge
  have hk_prev : N ≤ k - 1 := by
    omega
  have hmem : ω ∈ A (k - 1) := by
    have hk_eq : k - 1 + 1 = k := by
      omega
    refine ⟨t, ?_, lt_of_not_ge hnorm⟩
    constructor
    · simpa [hk_eq] using hk_le_t
    · simpa [hk_eq] using ht_lt.le
  exact hN (k - 1) hk_prev hmem

-- Proof sketch: apply the Brownian hitting-probability formula for balls from the next theorem in
-- the chapter together with the strong Markov property at the exit times of larger balls. For
-- `d ≤ 2` the return probability to every smaller ball is `1`, so every neighborhood of `y` is
-- visited at arbitrarily large times almost surely.
/-- Theorem 25.39 (1): if `d ≤ 2`, then for every `y ∈ ℝ^d`, almost every `d`-dimensional
Brownian path has `y` as a cluster point along `t → ∞`; equivalently, every neighborhood of `y`
is visited at arbitrarily large times. This is the textbook recurrence statement
`liminf_{t→∞} ‖W_t - y‖ = 0` in canonical filter form. -/
theorem brownian_visits_every_ball_frequently_of_dimension_le_two
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (hd : d ≤ 2) (y : State) :
    ∀ᵐ ω ∂μ, MapClusterPt y atTop (fun t ↦ W t ω) := by
  -- Proof comment: isolate the stochastic input in a countable tail-hitting lemma, then convert
  -- that tail-hitting information into the filter-theoretic cluster-point statement.
  filter_upwards [aeTailHitsBasisBalls_ofDimensionLeTwo (W := W) hW hd y] with ω hω
  exact mapClusterPt_ofTailHitsBasisBalls (f := fun t ↦ W t ω) hω

-- Proof sketch: use the preceding recurrent-ball-visiting statement on a countable basis of open
-- balls with rational centers and rational radii. A path that hits every such basis element has
-- dense range in `ℝ^d`.
/-- Helper for Theorem 25.39: in dimensions `d ≤ 2`, the recurrent-ball statement implies that
almost every sample path of the `d`-dimensional Brownian motion has dense range in `ℝ^d`. -/
lemma brownian_denseRange_of_dimension_le_two
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (hd : d ≤ 2) :
    ∀ᵐ ω ∂μ, DenseRange (fun t ↦ W t ω) := by
  -- Proof comment: apply part (1) along the fixed dense sequence of the Euclidean state space.
  have hcluster :
      ∀ᵐ ω ∂μ, ∀ n : ℕ,
        MapClusterPt (TopologicalSpace.denseSeq State n) atTop (fun t ↦ W t ω) := by
    rw [ae_all_iff]
    intro n
    simpa using
      brownian_visits_every_ball_frequently_of_dimension_le_two
        (W := W) hW hd (TopologicalSpace.denseSeq State n)
  -- Proof comment: a range whose cluster set contains a dense sequence is itself dense.
  filter_upwards [hcluster] with ω hω
  exact denseRange_ofDenseSeqClusterPts (f := fun t ↦ W t ω) hω

-- Proof sketch: apply the same strong-Markov reduction to larger and larger spheres. For
-- `d > 2`, the probability of ever re-entering a fixed ball after reaching radius `R` is
-- `(s / R)^(d - 2)`, which tends to `0`; hence the path eventually leaves every bounded set and
-- its norm tends to infinity almost surely.
/-- Helper for Theorem 25.39: in dimensions `d > 2`, the transience estimate upgrades to almost
sure divergence `‖W_t‖ → ∞` as `t → ∞` for the `d`-dimensional Brownian motion. -/
lemma brownian_norm_tendsto_atTop_of_dimension_gt_two
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (hd : 2 < d) :
    ∀ᵐ ω ∂μ, Tendsto (fun t ↦ ‖W t ω‖) atTop atTop := by
  -- Proof comment: countable eventual lower bounds on natural radii are exactly what
  -- `tendsto_atTop.2` needs to prove divergence of the norm to `∞`.
  filter_upwards [aeEventuallyOutsideNatBalls_ofDimensionGtTwo (W := W) hW hd] with ω hω
  refine tendsto_atTop.2 ?_
  intro b
  obtain ⟨n, hbn⟩ : ∃ n : ℕ, b ≤ n := exists_nat_ge b
  rcases hω n with ⟨T, hT⟩
  refine Filter.eventually_atTop.2 ⟨T, fun t ht ↦ ?_⟩
  exact le_trans hbn (hT t ht)

/-- Helper for Theorem 25.39: dividing a positive radius by `n + 2` produces a positive radius
strictly smaller than the original one. -/
lemma div_natCast_add_two_pos_and_lt {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < R / (n + 2 : ℝ) ∧ R / (n + 2 : ℝ) < R := by
  -- Proof comment: the denominator is always larger than `1`, so division both preserves
  -- positivity and strictly contracts the radius.
  have hden : 1 < (n + 2 : ℝ) := by
    nlinarith
  constructor
  · positivity
  · exact div_lt_self hR hden

/-- Helper for Theorem 25.39: cancelling a nonzero radius after dividing by `n + 2` leaves the
expected reciprocal factor. -/
lemma div_natCast_add_two_div_self {R : ℝ} (hR : R ≠ 0) (n : ℕ) :
    (R / (n + 2 : ℝ)) / R = 1 / (n + 2 : ℝ) := by
  -- Proof comment: one denominator-clearing step reduces the identity to a ring computation.
  field_simp [hR]

/-- Helper for Theorem 25.39: in dimensions `d > 2`, the probability that Brownian motion hits
the shrinking ball `Metric.ball y (dist 0 y / (n + 2))` is exactly `((n + 2)⁻¹)^(d - 2)`. -/
lemma shrinkingBallHitProbability_ofDimensionGtTwo
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (hd : 2 < d) (y : State) (hy : y ≠ 0) (n : ℕ) :
    μ {ω | (τ_[W, Metric.ball y (dist (0 : State) y / (n + 2 : ℝ))]) ω < ⊤} =
        ENNReal.ofReal ((1 / (n + 2 : ℝ)) ^ (d - 2)) := by
  have hy0 : (0 : State) ≠ y := by
    simpa using hy.symm
  have hdist : 0 < dist (0 : State) y := dist_pos.2 hy0
  have hdist_ne : dist (0 : State) y ≠ 0 := ne_of_gt hdist
  have hrPos : 0 <
      dist (0 : State) y / (n + 2 : ℝ) := by
    exact (div_natCast_add_two_pos_and_lt (R := dist (0 : State) y) hdist n).1
  have hrLt : dist (0 : State) y / (n + 2 : ℝ) < dist (0 : State) y := by
    exact (div_natCast_add_two_pos_and_lt (R := dist (0 : State) y) hdist n).2
  let hW0 : IsBrownianMotionVectorStartedAt μ W 0 := inferInstance
  have hratio : (dist (0 : State) y / (n + 2 : ℝ)) / dist (0 : State) y = 1 / (n + 2 : ℝ) := by
    simpa using
      div_natCast_add_two_div_self (R := dist (0 : State) y) hdist_ne n
  have hhit :
      μ {ω | (τ_[W, Metric.ball y (dist (0 : State) y / (n + 2 : ℝ))]) ω < ⊤} =
        ENNReal.ofReal (((dist (0 : State) y / (n + 2 : ℝ)) / dist (0 : State) y) ^ (d - 2)) := by
    -- Proof comment: Theorem 25.40 gives the exact ball-hitting probability before the radius
    -- ratio is normalized.
    simpa [if_neg (Nat.not_le_of_lt hd)] using
      brownian_hits_ball_probability
        (μ := ⟨μ, inferInstance⟩) (W := W) (x := 0) (hW := hW0)
        (r := dist (0 : State) y / (n + 2 : ℝ)) (hr := hrPos) (y := y) (hxy := hrLt)
  calc
    μ {ω | (τ_[W, Metric.ball y (dist (0 : State) y / (n + 2 : ℝ))]) ω < ⊤}
        = ENNReal.ofReal (((dist (0 : State) y / (n + 2 : ℝ)) / dist (0 : State) y) ^ (d - 2)) :=
          hhit
    _ = ENNReal.ofReal ((1 / (n + 2 : ℝ)) ^ (d - 2)) := by
          rw [hratio]

-- Proof sketch: fix `y ≠ 0` and combine transience with the ball-hitting formula centered at
-- `y`. In dimensions `d > 2`, the Brownian path hits every sufficiently small ball around `y`
-- with probability strictly less than `1`; iterating after large exit times shows that almost
-- surely the whole path stays outside some positive-radius ball around `y`.
/-- Helper for Theorem 25.39: in dimensions `d > 2`, every nonzero `y ∈ ℝ^d` is almost surely
avoided by a positive distance along the whole Brownian path. This is the textbook clause
`inf {‖W_t - y‖ : t ≥ 0} > 0` written as the existence of a uniform positive lower bound on the
distance to `y`. -/
lemma brownian_avoids_nonzero_points_of_dimension_gt_two
    {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (hd : 2 < d) (y : State) (hy : y ≠ 0) :
    ∀ᵐ ω ∂μ, ∃ ε : ℝ, 0 < ε ∧ ∀ t : NNReal, ε ≤ dist (W t ω) y := by
  letI : IsStandardBrownianMotionVector μ W := hW
  let r : ℕ → ℝ := fun n ↦ dist (0 : State) y / (n + 2 : ℝ)
  let bad : Set Ω := {ω | ∀ n : ℕ, ∃ t : NNReal, dist (W t ω) y < r n}
  have hy0 : (0 : State) ≠ y := by
    simpa using hy.symm
  have hdist : 0 < dist (0 : State) y := dist_pos.2 hy0
  have hdist_ne : dist (0 : State) y ≠ 0 := ne_of_gt hdist
  have hrPos : ∀ n : ℕ, 0 < r n := by
    intro n
    simpa [r] using
      (div_natCast_add_two_pos_and_lt (R := dist (0 : State) y) hdist n).1
  have hrLt : ∀ n : ℕ, r n < dist (0 : State) y := by
    intro n
    simpa [r] using
      (div_natCast_add_two_pos_and_lt (R := dist (0 : State) y) hdist n).2
  have hW0 : ∀ ω : Ω, W 0 ω = 0 := by
    intro ω
    ext i
    simpa using congrFun
      (IsBrownianMotion.zero (μ := μ) (B := fun t ω ↦ W t ω i)) ω
  have hbad_subset : ∀ n : ℕ, bad ⊆ {ω | (τ_[W, Metric.ball y (r n)]) ω < ⊤} := by
    intro n ω hω
    rcases hω n with ⟨t, ht⟩
    have ht_ne_zero : t ≠ 0 := by
      intro ht0
      have : dist (0 : State) y < r n := by
        simpa [ht0, hW0 ω] using ht
      exact not_lt_of_ge (hrLt n).le this
    have ht_pos : 0 < t := pos_iff_ne_zero.2 ht_ne_zero
    have htau_ne_top : (τ_[W, Metric.ball y (r n)]) ω ≠ ⊤ := by
      intro htop
      have havoid :=
        (strictPositiveHittingTime_eq_top_iff W (Metric.ball y (r n)) ω).1 htop
      exact havoid t ht_pos (by simpa [Metric.mem_ball] using ht)
    simpa using lt_top_iff_ne_top.2 htau_ne_top
  have hhit_measure :
      ∀ n : ℕ,
        μ {ω | (τ_[W, Metric.ball y (r n)]) ω < ⊤} =
          ENNReal.ofReal ((1 / (n + 2 : ℝ)) ^ (d - 2)) := by
    -- Proof comment: reuse the dedicated shrinking-ball probability normalization instead of
    -- asking one `simpa` to combine the hit formula with the radius-ratio rewrite.
    intro n
    simpa [r] using
      shrinkingBallHitProbability_ofDimensionGtTwo
        (μ := μ) (W := W) (hW := hW) hd y hy n
  have hpow_tendsto :
      Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((1 / (n + 2 : ℝ)) ^ (d - 2))) atTop (𝓝 0) := by
    have hdiv :
        Tendsto (fun n : ℕ ↦ (1 / (n + 2 : ℝ))) atTop (𝓝 0) := by
      simpa [Nat.cast_add, one_div] using
        (tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop))
    have hpow : 0 < d - 2 := Nat.sub_pos_of_lt hd
    have hreal :
        Tendsto (fun n : ℕ ↦ (1 / (n + 2 : ℝ)) ^ (d - 2)) atTop (𝓝 0) := by
      simpa [zero_pow (Nat.ne_of_gt hpow)] using hdiv.pow (d - 2)
    simpa using ENNReal.tendsto_ofReal hreal
  have hbad_measure : μ bad = 0 := by
    by_contra hbad_ne_zero
    have hbad_pos : 0 < μ bad := pos_iff_ne_zero.mpr hbad_ne_zero
    have hsmall :
        ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((1 / (n + 2 : ℝ)) ^ (d - 2)) < μ bad :=
      hpow_tendsto.eventually (Iio_mem_nhds hbad_pos)
    rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
    have hle :
        μ bad ≤ ENNReal.ofReal ((1 / (N + 2 : ℝ)) ^ (d - 2)) := by
      exact (measure_mono (hbad_subset N)).trans_eq (hhit_measure N)
    exact not_lt_of_ge hle (hN N le_rfl)
  -- Proof comment: the bad event has measure `0`, so almost every path avoids one shrinking ball.
  have hgood :
      ∀ᵐ ω ∂μ, ∃ n : ℕ, ∀ t : NNReal, r n ≤ dist (W t ω) y := by
    rw [ae_iff]
    change μ {ω | ¬ ∃ n : ℕ, ∀ t : NNReal, r n ≤ dist (W t ω) y} = 0
    simpa [bad, not_exists, not_forall, not_le] using hbad_measure
  exact hgood.mono fun ω hω ↦ by
    rcases hω with ⟨n, hn⟩
    exact ⟨r n, hrPos n, hn⟩

end BrownianRecurrenceTransience

end ProbabilityTheory
