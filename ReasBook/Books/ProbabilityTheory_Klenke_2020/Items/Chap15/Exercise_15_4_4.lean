/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Remark_15_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_23

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology ComplexConjugate

universe u

noncomputable section

/- Exercise 15.4.4 is `source-facing`: its public objects are the characteristic function of the
common law and the empirical averages themselves. The owner abstractions are the canonical law map
`charFun` and the chapter's i.i.d. shorthand `IsIID`; the file therefore keeps the textbook
conclusions directly visible while avoiding parallel local wrappers. -/

-- Proof sketch: a characteristic function comes from a probability law, so the derivative criterion
-- for `charFun` at `0` forces the derivative to be purely imaginary; extract the real coefficient.
/-- Part (1) of Exercise 15.4.4: if the characteristic function of a real probability law is
differentiable at `0`, then its derivative at `0` is `i m` for some real `m`. -/
theorem hasDerivAt_charFun_zero_eq_real_mul_I
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {dphi : ℂ}
    (hphi : HasDerivAt (charFun μ) dphi 0) :
    ∃ m : ℝ, dphi = (m : ℂ) * Complex.I := by
  -- Proof comment: differentiate the symmetry `φ(-t) = conj (φ t)` at `0`.
  have hneg : HasDerivAt (fun t : ℝ ↦ charFun μ (-t)) (-dphi) 0 := by
    simpa using
      (HasDerivAt.comp_const_sub
        (f := charFun μ) (f' := dphi) (a := (0 : ℝ)) (x := (0 : ℝ))
        (show HasDerivAt (charFun μ) dphi ((0 : ℝ) - 0) by simpa using hphi))
  have hconj : HasDerivAt (fun t : ℝ ↦ conj (charFun μ t)) (conj dphi) 0 := by
    simpa using hphi.hasFDerivAt.star.hasDerivAt
  have hEq : -dphi = conj dphi := by
    apply HasDerivAt.unique hneg
    simpa [charFun_neg] using hconj
  -- Proof comment: taking real parts forces the derivative to be purely imaginary.
  have hre : dphi.re = 0 := by
    have hEqReal : -dphi.re = dphi.re := by
      simpa using congrArg Complex.re hEq
    linarith
  refine ⟨dphi.im, ?_⟩
  calc
    dphi = (dphi.re : ℂ) + (dphi.im : ℂ) * Complex.I := by
      simp [Complex.re_add_im]
    _ = (dphi.im : ℂ) * Complex.I := by simp [hre]

section IIDAverage

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Exercise 15.4.4: the canonical embedding of `ℝ` into `ℝ¹` along the unique
coordinate axis is continuous. -/
private lemma continuous_single_zero :
    Continuous (fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1)) := by
  -- Proof comment: `EuclideanSpace.single` is the one-dimensional `PiLp` coordinate embedding.
  have hsingle : Continuous fun t : ℝ ↦ (Pi.single (0 : Fin 1) t : Fin 1 → ℝ) := by
    refine continuous_pi ?_
    intro i
    fin_cases i
    simpa using continuous_id
  simpa [EuclideanSpace.single] using
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 1 ↦ ℝ)).comp hsingle

/-- Helper for Exercise 15.4.4: transporting a real probability law to `ℝ¹` preserves the
characteristic function after reading the unique coordinate. -/
private lemma charFun_map_single_zero (μ : ProbabilityMeasure ℝ) (x : E1) :
    charFun
      (Measure.map (fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1)) (μ : Measure ℝ)) x =
      charFun (μ : Measure ℝ) (x (0 : Fin 1)) := by
  -- Proof comment: rewrite the pushforward characteristic function by `integral_map`,
  -- then collapse the one-dimensional inner product to scalar multiplication.
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply_real,
    MeasureTheory.integral_map
      (continuous_single_zero.measurable.aemeasurable :
        AEMeasurable (fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1)) (μ : Measure ℝ))
      (by fun_prop)]
  congr with t
  congr 1
  have hinner : inner ℝ (EuclideanSpace.single (0 : Fin 1) t) x = x 0 * t := by
    simpa [mul_comm] using
      (EuclideanSpace.inner_single_left (i := (0 : Fin 1)) t x)
  exact congrArg (fun z : ℂ ↦ z * Complex.I) (by exact_mod_cast hinner)

/-- Helper for Exercise 15.4.4: the coordinate process on the canonical infinite product
probability space is i.i.d. with common law `μ`. -/
lemma infinitePiCoordinateProcess_isIID
    {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    IsIID (fun n : ℕ ↦ fun ω : ℕ → ℝ ↦ ω n) (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: product measures make the coordinate projections independent.
    simpa using
      (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id) (mX := fun _ ↦ measurable_id))
  · -- Proof comment: every coordinate projection has the same pushforward law `μ`.
    intro i j
    exact
      (HasLaw.identDistrib
        (MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i))
        (MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) j)))

/-- Helper for Exercise 15.4.4: the characteristic function of the `n`th empirical average of an
i.i.d. real sequence is the `n`th power of the common characteristic function evaluated at `t / n`.
-/
lemma charFunAverage_eq_pow
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX_iid : IsIID X P) (n : ℕ) (t : ℝ) :
    charFun (P.map (fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / n)) t =
      (charFun (P.map (X 0)) (t / n)) ^ n := by
  have hX_ae (i : ℕ) : AEMeasurable (X i) P := (hX_iid.identDistrib i 0).aemeasurable_fst
  have hscale :
      (fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / n) =
        fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω := by
    ext ω
    simp [div_eq_mul_inv, mul_comm]
  -- Proof comment: rewrite the average as a scalar multiple of the partial sum and factor the
  -- partial-sum characteristic function using independence and identical distribution.
  rw [hscale, charFun_map_mul_comp]
  · rw [(hX_iid.iIndepFun.restrict (Finset.range n)).charFun_map_fun_finset_sum_eq_prod
      (fun _ _ ↦ hX_ae _)]
    simp [div_eq_mul_inv, mul_comm, fun i ↦ (hX_iid.identDistrib i 0).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ ↦ hX_ae _

/-- Helper for Exercise 15.4.4: weak convergence of the laws of `Y n` to `diracProba m` forces
`Y n` to converge in `P`-measure to the constant `m`. -/
lemma tendstoInMeasure_const_of_tendstoLaw_dirac
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {m : ℝ}
    (hY : ∀ n, AEMeasurable (Y n) P)
    (hLaw :
      Tendsto
        (fun n ↦ ProbabilityMeasure.map ⟨P, inferInstance⟩ (hY n))
        atTop
        (𝓝 (diracProba m))) :
    TendstoInMeasure P Y atTop (fun _ ↦ m) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let E : Set ℝ := {x | ε ≤ dist x m}
  have hClosedE : IsClosed E := by
    -- Proof comment: the distance-to-`m` sublevel sets are closed.
    exact isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hm_not_mem_E : m ∉ E := by
    -- Proof comment: the center `m` is strictly inside the complementary open ball.
    intro hm
    have : ε ≤ 0 := by simpa [E, dist_self] using hm
    exact (not_le_of_gt hε) this
  have hm_not_mem_frontier : m ∉ frontier E := by
    -- Proof comment: a frontier point of a closed set still lies in the set.
    intro hm
    exact hm_not_mem_E (hClosedE.frontier_subset hm)
  have hFrontier :
      (((diracProba m : ProbabilityMeasure ℝ) : Measure ℝ) (frontier E)) = 0 := by
    -- Proof comment: the frontier avoids the atom of the limiting Dirac law.
    rw [diracProba_toMeasure_apply' (x := m) isClosed_frontier.measurableSet]
    simp [hm_not_mem_frontier]
  have hMeasure :
      Tendsto
        (fun n ↦
          (((ProbabilityMeasure.map ⟨P, inferInstance⟩ (hY n) : ProbabilityMeasure ℝ) :
            Measure ℝ) E))
        atTop
        (𝓝 ((((diracProba m : ProbabilityMeasure ℝ) : Measure ℝ) E))) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hLaw hFrontier
  have hZero : (((diracProba m : ProbabilityMeasure ℝ) : Measure ℝ) E) = 0 := by
    -- Proof comment: the closed complement of the `ε`-ball has zero mass under `diracProba m`.
    rw [diracProba_toMeasure_apply' (x := m) hClosedE.measurableSet]
    simp [hm_not_mem_E]
  refine Tendsto.congr' ?_ (hZero ▸ hMeasure)
  filter_upwards with n
  rw [ProbabilityMeasure.map_apply' _ (hY n) hClosedE.measurableSet]
  rfl

/-- Helper for Exercise 15.4.4: differentiability at `0` of the common characteristic function
forces the empirical averages to converge in probability to the derivative coefficient. -/
lemma hasDerivAt_charFun_map_zero_implies_tendstoInMeasure_average
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX_iid : IsIID X P) {m : ℝ}
    (hphi : HasDerivAt (charFun (P.map (X 0))) ((m : ℂ) * Complex.I) 0) :
    TendstoInMeasure P
      (fun n ω ↦ (∑ i ∈ Finset.range n, X i ω) / n)
      atTop
      (fun _ ↦ m) := by
  have hX_ae (i : ℕ) : AEMeasurable (X i) P := (hX_iid.identDistrib i 0).aemeasurable_fst
  haveI hMapProb : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hX_ae 0)
  have hAverage_ae (n : ℕ) :
      AEMeasurable (fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / n) P := by
    -- Proof comment: each empirical average is a scalar multiple of a finite measurable sum.
    have hSum :
        AEMeasurable (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) P :=
      Finset.aemeasurable_fun_sum _ fun i _ ↦ hX_ae i
    simpa [div_eq_mul_inv, mul_comm] using hSum.const_mul ((n : ℝ)⁻¹)
  have hLaw :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map ⟨P, inferInstance⟩ (hAverage_ae n))
        atTop
        (𝓝 (diracProba m)) := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
    intro t
    have hComp :
        HasDerivAt
          (fun s : ℝ ↦ charFun (P.map (X 0)) (s * t))
          (t • ((m : ℂ) * Complex.I)) 0 := by
      -- Proof comment: compose the derivative at `0` with the rescaling `s ↦ s * t`.
      simpa [smul_eq_mul, mul_assoc] using
        hphi.scomp_of_eq 0 (hasDerivAt_mul_const t) (by simp)
    have hInvWithin :
        Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhdsWithin 0 ({0}ᶜ)) := by
      -- Proof comment: the sequence `1 / n` tends to `0` through nonzero points eventually.
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
          (fun n : ℕ ↦ (n : ℝ)⁻¹)
          ?_
          ?_
      · simpa using
          (tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0))
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
        simp [Set.mem_compl_iff, hn0]
    have hLinear :
        Tendsto
          (fun n : ℕ ↦
            ((n : ℝ) : ℂ) * (charFun (P.map (X 0)) ((n : ℝ)⁻¹ * t) - 1))
          atTop
          (𝓝 (t * ((m : ℂ) * Complex.I))) := by
      -- Proof comment: the derivative turns the first-order increment of `φ` along `t / n`
      -- into the linear term `((m : ℂ) * I) * t`.
      have hSlope :
          Tendsto
            (fun n : ℕ ↦
              ((n : ℝ)⁻¹)⁻¹ •
                (charFun (P.map (X 0)) (((0 : ℝ) + (n : ℝ)⁻¹) * t) -
                  charFun (P.map (X 0)) ((0 : ℝ) * t)))
            atTop
            (𝓝 (t * ((m : ℂ) * Complex.I))) :=
        hComp.tendsto_slope_zero.comp hInvWithin
      have hSlopeEq :
          (fun n : ℕ ↦
            ((n : ℝ)⁻¹)⁻¹ •
              (charFun (P.map (X 0)) (((0 : ℝ) + (n : ℝ)⁻¹) * t) -
                charFun (P.map (X 0)) ((0 : ℝ) * t))) =
            fun n : ℕ ↦ ((n : ℝ) : ℂ) * (charFun (P.map (X 0)) ((n : ℝ)⁻¹ * t) - 1) := by
        ext n
        have hCharZero : charFun (P.map (X 0)) ((0 : ℝ) * t) = (1 : ℂ) := by
          simp
        rw [hCharZero]
        simp [mul_comm]
      rw [hSlopeEq] at hSlope
      exact hSlope
    have hPow :
        Tendsto
          (fun n : ℕ ↦ (charFun (P.map (X 0)) ((n : ℝ)⁻¹ * t)) ^ n)
          atTop
          (𝓝 (Complex.exp (t * ((m : ℂ) * Complex.I))) ) := by
      -- Proof comment: exponentiate the linearized increment with the standard complex limit.
      simpa [charFun_zero] using
        (Complex.tendsto_one_add_pow_exp_of_tendsto (g := fun n : ℕ ↦
          charFun (P.map (X 0)) ((n : ℝ)⁻¹ * t) - 1) (t := (t * ((m : ℂ) * Complex.I))) hLinear)
    -- Route correction: package the characteristic-function limit at the law level first,
    -- then use the Portmanteau bridge above instead of repairing the in-measure step inline.
    have hCharEq :
        (fun n : ℕ ↦
          charFun
            (ProbabilityMeasure.map ⟨P, inferInstance⟩ (hAverage_ae n))
            t) =
          fun n : ℕ ↦ (charFun (P.map (X 0)) ((n : ℝ)⁻¹ * t)) ^ n := by
      ext n
      rw [ProbabilityMeasure.toMeasure_map]
      simpa [div_eq_mul_inv, mul_comm] using charFunAverage_eq_pow hX_iid n t
    have hDirac :
        charFun (diracProba m) t = Complex.exp (t * ((m : ℂ) * Complex.I)) := by
      -- Proof comment: the characteristic function of a Dirac law is the exponential phase.
      have hInner : inner ℝ m t = m * t := by
        simpa using (RCLike.inner_apply' (𝕜 := ℝ) m t)
      calc
        charFun (diracProba m) t = Complex.exp (((inner ℝ m t : ℝ) : ℂ) * Complex.I) := by
          simp [MeasureTheory.diracProba]
        _ = Complex.exp (t * ((m : ℂ) * Complex.I)) := by
          simp [hInner, mul_comm, mul_left_comm]
    rw [hCharEq]
    simpa [hDirac] using hPow
  exact tendstoInMeasure_const_of_tendstoLaw_dirac hAverage_ae hLaw

/-- Helper for Exercise 15.4.4: convergence in probability of the empirical averages depends only
on the common law, so one may transport it to the canonical infinite-product realization. -/
-- TODO: normalize the `ProbabilityMeasure.map`/`Measure.map` transport and install the canonical
-- product-measure instances explicitly so the law identity can be rewritten via `Tendsto.congr'`.
lemma tendstoInMeasure_average_iff_tendstoInMeasureInfinitePiAverage
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX_iid : IsIID X P) (m : ℝ) :
    TendstoInMeasure P
      (fun n ω ↦ (∑ i ∈ Finset.range n, X i ω) / n)
      atTop
      (fun _ ↦ m) ↔
        TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ P.map (X 0)))
          (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
          atTop
          (fun _ ↦ m) := by
  let avg : ℕ → Ω → ℝ := fun n ω ↦ (∑ i ∈ Finset.range n, X i ω) / n
  let μ : Measure ℝ := P.map (X 0)
  let cavg : ℕ → (ℕ → ℝ) → ℝ := fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n
  let Pinf : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ ↦ μ)
  have hX_ae (i : ℕ) : AEMeasurable (X i) P := (hX_iid.identDistrib i 0).aemeasurable_fst
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (hX_ae 0)
  have havg_ae (n : ℕ) : AEMeasurable (avg n) P := by
    -- Proof comment: each empirical average is a scalar multiple of a finite measurable sum.
    have hsum :
        AEMeasurable (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) P :=
      Finset.aemeasurable_fun_sum _ fun i _ ↦ hX_ae i
    simpa [avg, div_eq_mul_inv, mul_comm] using hsum.const_mul ((n : ℝ)⁻¹)
  have hcavg_ae (n : ℕ) : AEMeasurable (cavg n) Pinf := by
    -- Proof comment: the canonical averages have the same measurable finite-sum shape.
    have hcoord_ae (i : ℕ) : AEMeasurable (fun ω : ℕ → ℝ ↦ ω i) Pinf := by
      exact ((infinitePiCoordinateProcess_isIID (μ := μ)).identDistrib i 0).aemeasurable_fst
    have hsum :
        AEMeasurable (fun ω ↦ ∑ i ∈ Finset.range n, ω i) Pinf :=
      Finset.aemeasurable_fun_sum _ fun i _ ↦ hcoord_ae i
    simpa [cavg, div_eq_mul_inv, mul_comm] using hsum.const_mul ((n : ℝ)⁻¹)
  have hLawEq (n : ℕ) :
      ProbabilityMeasure.map ⟨P, inferInstance⟩ (havg_ae n) =
        ProbabilityMeasure.map ⟨Pinf, inferInstance⟩ (hcavg_ae n) := by
    -- Proof comment: both average laws have the same characteristic function
    -- `(charFun μ (t / n)) ^ n`, so uniqueness of characteristic functions identifies them.
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_charFun
    ext t
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
    calc
      charFun (P.map (avg n)) t = (charFun μ (t / n)) ^ n := by
        simpa [avg, μ] using charFunAverage_eq_pow hX_iid n t
      _ = charFun (Pinf.map (cavg n)) t := by
        have hCoordMap : Pinf.map (fun ω : ℕ → ℝ ↦ ω 0) = μ := by
          simpa [Pinf] using (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0).map_eq
        have hCoordChar :
            charFun μ (t / n) = charFun (Pinf.map (fun ω : ℕ → ℝ ↦ ω 0)) (t / n) := by
          simpa using congrArg (fun ν : Measure ℝ ↦ charFun ν (t / n)) hCoordMap.symm
        calc
          (charFun μ (t / n)) ^ n = (charFun (Pinf.map (fun ω : ℕ → ℝ ↦ ω 0)) (t / n)) ^ n := by
            rw [hCoordChar]
          _ = charFun (Pinf.map (cavg n)) t := by
            simpa [cavg, Pinf, μ] using
              (charFunAverage_eq_pow (infinitePiCoordinateProcess_isIID (μ := μ)) n t).symm
  constructor
  · intro hAverage
    have hLaw :
        Tendsto
          (fun n ↦ ProbabilityMeasure.map ⟨P, inferInstance⟩ (havg_ae n))
          atTop
          (𝓝 (diracProba m)) := by
      -- Proof comment: the original empirical averages converge in measure, hence their laws
      -- converge weakly to the Dirac mass at `m`.
      have hDist :
          TendstoInDistribution avg atTop (fun _ : Ω ↦ m) (fun _ : ℕ ↦ P) P :=
        hAverage.tendstoInDistribution havg_ae
      have hDirac :
          (⟨P.map (fun _ : Ω ↦ m), Measure.isProbabilityMeasure_map aemeasurable_const⟩ :
            ProbabilityMeasure ℝ) = diracProba m := by
        apply ProbabilityMeasure.toMeasure_injective
        simpa [MeasureTheory.diracProba] using Measure.map_const P m
      simpa [ProbabilityMeasure.map, hDirac] using hDist.tendsto
    have hLawCanon :
        Tendsto
          (fun n ↦ ProbabilityMeasure.map ⟨Pinf, inferInstance⟩ (hcavg_ae n))
          atTop
          (𝓝 (diracProba m)) := by
      refine Tendsto.congr' ?_ hLaw
      filter_upwards with n
      exact hLawEq n
    exact tendstoInMeasure_const_of_tendstoLaw_dirac hcavg_ae hLawCanon
  · intro hAverage
    have hLaw :
        Tendsto
          (fun n ↦ ProbabilityMeasure.map ⟨Pinf, inferInstance⟩ (hcavg_ae n))
          atTop
          (𝓝 (diracProba m)) := by
      -- Proof comment: the canonical empirical averages satisfy the same law-level upgrade.
      have hDist :
          TendstoInDistribution cavg atTop (fun _ : ℕ → ℝ ↦ m) (fun _ : ℕ ↦ Pinf) Pinf :=
        hAverage.tendstoInDistribution hcavg_ae
      have hDirac :
          (⟨Pinf.map (fun _ : ℕ → ℝ ↦ m), Measure.isProbabilityMeasure_map aemeasurable_const⟩ :
            ProbabilityMeasure ℝ) = diracProba m := by
        apply ProbabilityMeasure.toMeasure_injective
        simpa [MeasureTheory.diracProba] using Measure.map_const Pinf m
      simpa [ProbabilityMeasure.map, hDirac] using hDist.tendsto
    have hLawOrig :
        Tendsto
          (fun n ↦ ProbabilityMeasure.map ⟨P, inferInstance⟩ (havg_ae n))
          atTop
          (𝓝 (diracProba m)) := by
      refine Tendsto.congr' ?_ hLaw
      filter_upwards with n
      exact (hLawEq n).symm
    exact tendstoInMeasure_const_of_tendstoLaw_dirac havg_ae hLawOrig

/-- Helper for Exercise 15.4.4: each canonical empirical average is a.e.-measurable on the
infinite-product realization. -/
private lemma canonicalAverage_aemeasurable
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (n : ℕ) :
    AEMeasurable
      (fun ω : ℕ → ℝ ↦ (∑ i ∈ Finset.range n, ω i) / n)
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  -- Proof comment: each canonical average is a scalar multiple of a finite measurable sum of
  -- coordinate projections.
  have hcoord_ae (i : ℕ) :
      AEMeasurable
        (fun ω : ℕ → ℝ ↦ ω i)
        (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
    exact ((infinitePiCoordinateProcess_isIID (μ := μ)).identDistrib i 0).aemeasurable_fst
  have hsum :
      AEMeasurable
        (fun ω ↦ ∑ i ∈ Finset.range n, ω i)
        (Measure.infinitePi (fun _ : ℕ ↦ μ)) :=
    Finset.aemeasurable_fun_sum _ fun i _ ↦ hcoord_ae i
  simpa [div_eq_mul_inv, mul_comm] using hsum.const_mul ((n : ℝ)⁻¹)

/-- Helper for Exercise 15.4.4: the characteristic function of a Dirac probability law is the
expected exponential phase. -/
private lemma charFun_diracProba_eq_phase (m t : ℝ) :
    charFun (diracProba m : ProbabilityMeasure ℝ) t =
      Complex.exp (t * ((m : ℂ) * Complex.I)) := by
  -- Proof comment: expand the definition of the Dirac characteristic function and collapse the
  -- inner product on `ℝ` to ordinary multiplication.
  have hInner : inner ℝ m t = m * t := by
    simpa using (RCLike.inner_apply' (𝕜 := ℝ) m t)
  calc
    charFun (diracProba m : ProbabilityMeasure ℝ) t =
        Complex.exp (((inner ℝ m t : ℝ) : ℂ) * Complex.I) := by
          simp [MeasureTheory.diracProba]
    _ = Complex.exp (t * ((m : ℂ) * Complex.I)) := by
          simp [hInner, mul_comm, mul_left_comm]

/-- Helper for Exercise 15.4.4: at every fixed frequency, the characteristic functions of the
canonical empirical-average laws converge to the corresponding Dirac phase. -/
-- TODO: inline the law-convergence step above and rewrite the pushed-forward characteristic
-- function through `charFunAverage_eq_pow` without depending on a later declaration.
private lemma canonicalAverage_charFunPow_tendsto
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ}
    (hAverage :
      TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
        (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ ↦ m))
    (t : ℝ) :
    Tendsto
      (fun n : ℕ ↦ (charFun μ (t / n)) ^ n)
      atTop
      (𝓝 (Complex.exp (t * ((m : ℂ) * Complex.I)))) := by
  -- Proof comment: upgrade convergence in measure on the canonical product space to weak
  -- convergence of the average laws, then evaluate the resulting characteristic-function limit.
  have hDist :
      TendstoInDistribution
        (fun n (ω : ℕ → ℝ) ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ : ℕ → ℝ ↦ m)
        (fun _ : ℕ ↦ Measure.infinitePi (fun _ : ℕ ↦ μ))
        (Measure.infinitePi (fun _ : ℕ ↦ μ)) :=
    hAverage.tendstoInDistribution fun n ↦ canonicalAverage_aemeasurable (μ := μ) n
  have hDirac :
      (⟨(Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun _ : ℕ → ℝ ↦ m),
          Measure.isProbabilityMeasure_map aemeasurable_const⟩ : ProbabilityMeasure ℝ) =
        diracProba m := by
    -- Proof comment: the constant map on a probability space has Dirac law.
    apply ProbabilityMeasure.toMeasure_injective
    simpa [MeasureTheory.diracProba] using
      (Measure.map_const (Measure.infinitePi (fun _ : ℕ ↦ μ)) m)
  have hChar :
      Tendsto
        (fun n ↦
          charFun
            ((Measure.infinitePi (fun _ : ℕ ↦ μ)).map
              (fun ω : ℕ → ℝ ↦ (∑ i ∈ Finset.range n, ω i) / n))
            t)
        atTop
        (𝓝 (Complex.exp (((inner ℝ m t : ℝ) : ℂ) * Complex.I))) := by
    simpa [hDirac, MeasureTheory.diracProba] using
      (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hDist.tendsto) t
  -- Proof comment: rewrite the canonical average law with the coordinate-process i.i.d. identity.
  convert hChar using 1
  · ext n
    have hCoordMap :
        (Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun ω : ℕ → ℝ ↦ ω 0) = μ := by
      simpa using (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0).map_eq
    have hCoordChar :
        charFun μ (t / n) =
          charFun ((Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun ω : ℕ → ℝ ↦ ω 0)) (t / n) := by
      simpa using congrArg (fun ν : Measure ℝ ↦ charFun ν (t / n)) hCoordMap.symm
    calc
      charFun μ (t / n) ^ n =
          charFun ((Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun ω : ℕ → ℝ ↦ ω 0)) (t / n) ^ n := by
            rw [hCoordChar]
      _ =
          charFun
            ((Measure.infinitePi (fun _ : ℕ ↦ μ)).map
              (fun ω : ℕ → ℝ ↦ (∑ i ∈ Finset.range n, ω i) / n))
            t := by
              simpa using (charFunAverage_eq_pow (infinitePiCoordinateProcess_isIID (μ := μ)) n t).symm
  · have hInner : inner ℝ m t = m * t := by
      simpa using (RCLike.inner_apply' (𝕜 := ℝ) m t)
    simp [hInner, mul_comm, mul_left_comm]

/-- Helper for Exercise 15.4.4: at reciprocal frequencies, the common characteristic function
returns to `1`. -/
private lemma canonicalAverage_reciprocal_charFun_tendsto_one
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (t : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun μ (t / n)) atTop (𝓝 (1 : ℂ)) := by
  -- Proof comment: continuity of `charFun` at the origin and `t / n → 0` force the values back to
  -- the unit value `charFun μ 0 = 1`.
  have hScale :
      Tendsto (fun n : ℕ ↦ t / n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_const_nhds.mul
        (tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0)))
  simpa using ((MeasureTheory.continuous_charFun (μ := μ)).continuousAt.tendsto.comp hScale)

/-- Helper for Exercise 15.4.4: the reciprocal-frequency characteristic-function defects are
eventually uniformly small. -/
-- TODO: rebuild this from `canonicalAverage_reciprocal_charFun_tendsto_one` by first proving the
-- complex difference tends to `0` and only then applying `.norm`.
private lemma canonicalAverage_reciprocal_charFun_eventually_half
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, ‖charFun μ (t / n) - 1‖ < 1 / 2 := by
  -- Proof comment: subtract the limit value `1`, take norms, and use the neighborhood
  -- `(−∞, 1 / 2)` of `0`.
  have hSub :
      Tendsto (fun n : ℕ ↦ charFun μ (t / n) - 1) atTop (𝓝 (0 : ℂ)) := by
    simpa using
      (canonicalAverage_reciprocal_charFun_tendsto_one (μ := μ) t).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (𝓝 (1 : ℂ)))
  have hNorm :
      Tendsto (fun n : ℕ ↦ ‖charFun μ (t / n) - 1‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using hSub.norm
  exact hNorm (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))

/-- Helper for Exercise 15.4.4: on any fixed compact interval around the origin, the reciprocal
characteristic-function values are eventually uniformly contained in the closed half-ball around
`1`. -/
private lemma canonicalAverage_reciprocal_charFun_eventually_halfOn
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {L : ℝ} (hL : 0 < L) :
    ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Set.Icc (-L) L, ‖charFun μ (t / n) - 1‖ ≤ (1 / 2 : ℝ) := by
  have hcont :
      ContinuousAt (fun s : ℝ ↦ charFun μ s - 1) 0 := by
    simpa using
      ((MeasureTheory.continuous_charFun (μ := μ)).continuousAt.sub continuousAt_const)
  have hHalf : Set.Iio (1 / 2 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
  have hcontNorm : ContinuousAt (fun s : ℝ ↦ ‖charFun μ s - 1‖) 0 := hcont.norm
  have hcontNormZero :
      Tendsto (fun s : ℝ ↦ ‖charFun μ s - 1‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
    simpa [ContinuousAt, charFun_zero] using hcontNorm
  have hEventuallySmall :
      ∀ᶠ s : ℝ in 𝓝 0, ‖charFun μ s - 1‖ < (1 / 2 : ℝ) := by
    exact hcontNormZero hHalf
  rcases Metric.mem_nhds_iff.1 hEventuallySmall with ⟨δ, hδpos, hδ⟩
  have hScale :
      Tendsto (fun n : ℕ ↦ L * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_const_nhds.mul
        (tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0)))
  have hEventuallyBound :
      ∀ᶠ n : ℕ in atTop, L * (n : ℝ)⁻¹ < δ := by
    exact hScale (Iio_mem_nhds hδpos)
  filter_upwards [eventually_ge_atTop 1, hEventuallyBound] with n hn hnd t ht
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have htabs : |t| ≤ L := by
    rw [abs_le]
    exact ht
  have htdist : dist (t / n) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_div]
    have hinv_nonneg : 0 ≤ |(n : ℝ)|⁻¹ := inv_nonneg.2 (abs_nonneg _)
    have hmul :
        |t| * |(n : ℝ)|⁻¹ ≤ L * (n : ℝ)⁻¹ := by
      have habs_n : |(n : ℝ)| = n := abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)
      rw [habs_n]
      gcongr
    exact lt_of_le_of_lt hmul hnd
  exact le_of_lt (hδ htdist)

/-- Helper for Exercise 15.4.4: the reciprocal-frequency characteristic-function values eventually
stay inside the principal slit plane near `1`. -/
-- TODO: once the previous half-ball estimate is restored, feed it directly into
-- `Complex.mem_slitPlane_of_norm_lt_one`.
private lemma canonicalAverage_reciprocal_charFun_eventually_mem_slitPlane
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, charFun μ (t / n) ∈ Complex.slitPlane := by
  -- Proof comment: the previous half-ball bound implies membership in the open unit ball around
  -- `1`, and mathlib places that ball inside the principal slit plane.
  filter_upwards [canonicalAverage_reciprocal_charFun_eventually_half (μ := μ) t] with n hn
  have hlt : ‖charFun μ (t / n) - 1‖ < 1 := by
    linarith
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Complex.mem_slitPlane_of_norm_lt_one (z := charFun μ (t / n) - 1) hlt)

/-- Helper for Exercise 15.4.4: on a compact interval, a continuous logarithmic lift is recovered
by applying `Complex.log` to its exponential once that exponential stays in the slit plane. -/
private lemma log_exp_eq_of_mem_slitPlaneOnIcc
    {L : ℝ} (hL : 0 ≤ L)
    (G : C(Set.Icc (-L) L, ℂ))
    (hG0 : G ⟨0, by constructor <;> linarith⟩ = 0)
    (hslit : ∀ x, Complex.exp (G x) ∈ Complex.slitPlane) :
    ∀ x, Complex.log (Complex.exp (G x)) = G x := by
  let A : Set ℝ := Set.Icc (-L) L
  have hA_nonempty : A.Nonempty := ⟨0, by constructor <;> linarith⟩
  letI : ContractibleSpace A := (convex_Icc (-L) L).contractibleSpace hA_nonempty
  letI : LocPathConnectedSpace A := (convex_Icc (-L) L).locPathConnectedSpace
  have hf_cont :
      Continuous fun x : A ↦
        (⟨Complex.exp (G x), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) := by
    exact (Complex.continuous_exp.comp G.continuous).subtype_mk fun x ↦ Complex.exp_ne_zero _
  let f : C(A, {z : ℂ // z ≠ 0}) :=
    ⟨fun x ↦ ⟨Complex.exp (G x), Complex.exp_ne_zero _⟩, hf_cont⟩
  have hH_cont : Continuous fun x : A ↦ Complex.log (Complex.exp (G x)) := by
    exact (Complex.continuous_exp.comp G.continuous).clog hslit
  let H : C(A, ℂ) := ⟨fun x ↦ Complex.log (Complex.exp (G x)), hH_cont⟩
  have hbase :
      (fun z : ℂ ↦ (⟨Complex.exp z, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) 0 =
        f ⟨0, by constructor <;> linarith⟩ := by
    apply Subtype.ext
    simp [f, hG0]
  rcases Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
      f ⟨0, by constructor <;> linarith⟩ 0 hbase with
    ⟨Lift, hLift, hLiftuniq⟩
  have hGlift :
      G ⟨0, by constructor <;> linarith⟩ = 0 ∧
        (fun z : ℂ ↦ (⟨Complex.exp z, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ∘ G = f := by
    refine ⟨hG0, ?_⟩
    funext x
    apply Subtype.ext
    simp [f]
  have hHlift :
      H ⟨0, by constructor <;> linarith⟩ = 0 ∧
        (fun z : ℂ ↦ (⟨Complex.exp z, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) ∘ H = f := by
    refine ⟨by simp [H, hG0], ?_⟩
    funext x
    apply Subtype.ext
    simp [H, f, Complex.exp_log, Complex.exp_ne_zero]
  have hEq : H = G := (hLiftuniq H hHlift).trans ((hLiftuniq G hGlift).symm)
  intro x
  exact congrArg (fun F : C(A, ℂ) ↦ F x) hEq

/-- Helper for Exercise 15.4.4: once both the reciprocal characteristic-function factors and their
`n`th powers stay in the principal half-ball on `Set.Icc (-L) L`, the principal logarithm of the
power is the corresponding multiple of the principal logarithm of the factor. -/
private lemma canonicalAverage_logPow_eq_natMulLogOn
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {L : ℝ} (hL : 0 ≤ L)
    {n : ℕ} (hn : 1 ≤ n)
    (hFactorHalf :
      ∀ t ∈ Set.Icc (-L) L, ‖charFun μ (t / n) - 1‖ ≤ (1 / 2 : ℝ))
    (hPowHalf :
      ∀ t ∈ Set.Icc (-L) L, ‖(charFun μ (t / n)) ^ n - 1‖ ≤ (1 / 2 : ℝ)) :
    ∀ t ∈ Set.Icc (-L) L,
      Complex.log ((charFun μ (t / n)) ^ n) =
        (n : ℂ) * Complex.log (charFun μ (t / n)) := by
  let A : Set ℝ := Set.Icc (-L) L
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hFactorSlit :
      ∀ t ∈ Set.Icc (-L) L, charFun μ (t / n) ∈ Complex.slitPlane := by
    intro t ht
    have hlt : ‖charFun μ (t / n) - 1‖ < 1 := lt_of_le_of_lt (hFactorHalf t ht) (by norm_num)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Complex.mem_slitPlane_of_norm_lt_one (z := charFun μ (t / n) - 1) hlt)
  have hPowSlit :
      ∀ t ∈ Set.Icc (-L) L, (charFun μ (t / n)) ^ n ∈ Complex.slitPlane := by
    intro t ht
    have hlt : ‖(charFun μ (t / n)) ^ n - 1‖ < 1 := lt_of_le_of_lt (hPowHalf t ht) (by norm_num)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Complex.mem_slitPlane_of_norm_lt_one (z := (charFun μ (t / n)) ^ n - 1) hlt)
  have hG_cont :
      Continuous fun x : A ↦ (n : ℂ) * Complex.log (charFun μ ((x : ℝ) / n)) := by
    have hFactorCont : Continuous fun x : A ↦ charFun μ ((x : ℝ) / n) := by
      fun_prop
    exact continuous_const.mul (hFactorCont.clog fun x ↦ hFactorSlit x.1 x.2)
  let G : C(A, ℂ) :=
    ⟨fun x ↦ (n : ℂ) * Complex.log (charFun μ ((x : ℝ) / n)), hG_cont⟩
  have hG0 : G ⟨0, by constructor <;> linarith⟩ = 0 := by
    simp [G, hn0, charFun_zero]
  have hExpSlit : ∀ x, Complex.exp (G x) ∈ Complex.slitPlane := by
    intro x
    have hExpEq :
        Complex.exp (G x) = (charFun μ ((x : ℝ) / n)) ^ n := by
      rw [show G x = (n : ℂ) * Complex.log (charFun μ ((x : ℝ) / n)) by rfl]
      rw [Complex.exp_nat_mul]
      congr 1
      exact Complex.exp_log (Complex.slitPlane_ne_zero (hFactorSlit x.1 x.2))
    rw [hExpEq]
    exact hPowSlit x.1 x.2
  have hLogExp := log_exp_eq_of_mem_slitPlaneOnIcc hL G hG0 hExpSlit
  intro t ht
  have hExpEq :
      Complex.exp (G ⟨t, ht⟩) = (charFun μ (t / n)) ^ n := by
    rw [show G ⟨t, ht⟩ = (n : ℂ) * Complex.log (charFun μ (t / n)) by rfl]
    rw [Complex.exp_nat_mul]
    congr 1
    exact Complex.exp_log (Complex.slitPlane_ne_zero (hFactorSlit t ht))
  calc
    Complex.log ((charFun μ (t / n)) ^ n)
        = Complex.log (Complex.exp (G ⟨t, ht⟩)) := by rw [hExpEq]
    _ = G ⟨t, ht⟩ := hLogExp ⟨t, ht⟩
    _ = (n : ℂ) * Complex.log (charFun μ (t / n)) := rfl


/-- Helper for Exercise 15.4.4: convergence in measure of the canonical empirical averages implies
weak convergence of their pushforward laws to `diracProba m`. -/
-- TODO: this is the intended law-level owner step; finish it via
-- `hAverage.tendstoInDistribution (canonicalAverage_aemeasurable ...)`.
lemma tendstoLaw_canonicalAverage_dirac_of_tendstoInMeasure
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ}
    (hAverage :
      TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
        (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ ↦ m)) :
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map
          ⟨Measure.infinitePi (fun _ : ℕ ↦ μ), inferInstance⟩
          (canonicalAverage_aemeasurable (μ := μ) n))
      atTop
      (𝓝 (diracProba m)) := by
  -- Proof comment: this is precisely the law component of convergence in distribution for the
  -- canonical averages.
  have hDist :
      TendstoInDistribution
        (fun n (ω : ℕ → ℝ) ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ : ℕ → ℝ ↦ m)
        (fun _ : ℕ ↦ Measure.infinitePi (fun _ : ℕ ↦ μ))
        (Measure.infinitePi (fun _ : ℕ ↦ μ)) :=
    hAverage.tendstoInDistribution fun n ↦ canonicalAverage_aemeasurable (μ := μ) n
  have hDirac :
      (⟨(Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun _ : ℕ → ℝ ↦ m),
          Measure.isProbabilityMeasure_map aemeasurable_const⟩ : ProbabilityMeasure ℝ) =
        diracProba m := by
    -- Proof comment: identify the limiting constant law with the Dirac probability measure.
    apply ProbabilityMeasure.toMeasure_injective
    simpa [MeasureTheory.diracProba] using
      (Measure.map_const (Measure.infinitePi (fun _ : ℕ ↦ μ)) m)
  simpa [ProbabilityMeasure.map, hDirac] using hDist.tendsto

/-- Helper for Exercise 15.4.4: weak convergence of real laws upgrades to compact-uniform
convergence of their characteristic functions. -/
private lemma charFun_tendstoUniformlyOn_of_tendstoReal
    {P : ProbabilityMeasure ℝ} {Ps : ℕ → ProbabilityMeasure ℝ}
    (hP : Tendsto Ps atTop (𝓝 P)) :
    ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn
        (fun n t ↦ charFun (Ps n : Measure ℝ) t)
        (charFun (P : Measure ℝ))
        atTop
        K := by
  let Qs : ℕ → ProbabilityMeasure E1 := fun n ↦
    (Ps n).map
      (continuous_single_zero.measurable.aemeasurable :
        AEMeasurable (fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1))
          (Ps n : Measure ℝ))
  let Q : ProbabilityMeasure E1 :=
    P.map
      (continuous_single_zero.measurable.aemeasurable :
        AEMeasurable (fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1))
          (P : Measure ℝ))
  have hQtendsto : Tendsto Qs atTop (𝓝 Q) := by
    -- Proof comment: pushing weakly convergent real laws along the continuous embedding
    -- `ℝ → ℝ¹` preserves weak convergence.
    simpa [Qs, Q] using
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Ps P hP continuous_single_zero)
  intro K hK
  have hKE :
      IsCompact ((fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1)) '' K) :=
    hK.image continuous_single_zero
  have hUniformE :=
    (charFun_tendstoUniformlyOn_of_tendsto (d := 1) (P := Q) hQtendsto)
      ((fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1)) '' K) hKE
  rw [Metric.tendstoUniformlyOn_iff] at hUniformE ⊢
  intro ε hε
  filter_upwards [hUniformE ε hε] with n hn t ht
  have hPsApply :
      charFun (Qs n : Measure E1) (EuclideanSpace.single (0 : Fin 1) t) =
        charFun (Ps n : Measure ℝ) t := by
    -- Proof comment: the one-dimensional Euclidean embedding preserves the real
    -- characteristic-function parameter.
    simpa [Qs] using
      (charFun_map_single_zero (μ := Ps n) (EuclideanSpace.single (0 : Fin 1) t))
  have hPApply :
      charFun (Q : Measure E1) (EuclideanSpace.single (0 : Fin 1) t) =
        charFun (P : Measure ℝ) t := by
    -- Proof comment: the same transport identifies the limit characteristic function.
    simpa [Q] using
      (charFun_map_single_zero (μ := P) (EuclideanSpace.single (0 : Fin 1) t))
  have htE :
      EuclideanSpace.single (0 : Fin 1) t ∈
        (fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1)) '' K := ⟨t, ht, rfl⟩
  simpa [hPsApply, hPApply] using hn (EuclideanSpace.single (0 : Fin 1) t) htE

/-- Helper for Exercise 15.4.4: the characteristic functions of the canonical empirical-average
laws converge compact-uniformly to the Dirac phase. -/
private lemma canonicalAverage_charFunPow_tendstoUniformlyOn
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ}
    (hAverage :
      TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
        (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ ↦ m)) :
    ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn
        (fun n : ℕ ↦ fun t : ℝ ↦ (charFun μ (t / n)) ^ n)
        (fun t : ℝ ↦ Complex.exp (t * ((m : ℂ) * Complex.I)))
        atTop
        K := by
  have hLaw :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map
            ⟨Measure.infinitePi (fun _ : ℕ ↦ μ), inferInstance⟩
            (canonicalAverage_aemeasurable (μ := μ) n))
        atTop
        (𝓝 (diracProba m)) :=
    tendstoLaw_canonicalAverage_dirac_of_tendstoInMeasure hAverage
  intro K hK
  have hUniform :=
    charFun_tendstoUniformlyOn_of_tendstoReal hLaw K hK
  rw [Metric.tendstoUniformlyOn_iff] at hUniform ⊢
  intro ε hε
  filter_upwards [hUniform ε hε] with n hn t ht
  have hCharEq :
      charFun
        ((Measure.infinitePi (fun _ : ℕ ↦ μ)).map
          (fun ω : ℕ → ℝ ↦ (∑ i ∈ Finset.range n, ω i) / n)) t =
        (charFun μ (t / n)) ^ n := by
    -- Proof comment: the canonical coordinate process realizes the empirical-average law whose
    -- characteristic function is the expected `n`th power.
    have hCoordMap :
        (Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun ω : ℕ → ℝ ↦ ω 0) = μ := by
      simpa using (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0).map_eq
    have hCoordChar :
        charFun μ (t / n) =
          charFun ((Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun ω : ℕ → ℝ ↦ ω 0)) (t / n) := by
      simpa using congrArg (fun ν : Measure ℝ ↦ charFun ν (t / n)) hCoordMap.symm
    calc
      charFun
          ((Measure.infinitePi (fun _ : ℕ ↦ μ)).map
            (fun ω : ℕ → ℝ ↦ (∑ i ∈ Finset.range n, ω i) / n)) t
          = (charFun ((Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun ω : ℕ → ℝ ↦ ω 0)) (t / n)) ^ n := by
              simpa [div_eq_mul_inv, mul_comm] using
                (charFunAverage_eq_pow (infinitePiCoordinateProcess_isIID (μ := μ)) n t)
      _ = (charFun μ (t / n)) ^ n := by rw [hCoordChar]
  have hDirac :
      charFun (diracProba m : Measure ℝ) t = Complex.exp (t * ((m : ℂ) * Complex.I)) := by
    simpa using charFun_diracProba_eq_phase m t
  have hraw := hn t ht
  have hraw' :
      ‖charFun
          ((Measure.infinitePi (fun _ : ℕ ↦ μ)).map
            (fun ω : ℕ → ℝ ↦ (∑ i ∈ Finset.range n, ω i) / n)) t -
        Complex.exp (t * ((m : ℂ) * Complex.I))‖ < ε := by
    simpa [hDirac, dist_eq_norm, norm_sub_rev] using hraw
  have hraw'' : ‖(charFun μ (t / n)) ^ n - Complex.exp (t * ((m : ℂ) * Complex.I))‖ < ε := by
    simpa [hCharEq] using hraw'
  simpa [dist_eq_norm, norm_sub_rev] using hraw''

/-- Helper for Exercise 15.4.4: floor rescaling keeps the reciprocal sample in `Set.Icc (-L) L`
and uniformly away from `0`. -/
private lemma floorRescaling_memIcc_and_abs_bounds
    {L h : ℝ} (hL : 0 < L) (hh0 : 0 < |h|) (hh : |h| < L / 2) :
    let N := Nat.floor (L / |h|)
    let t_h := (N : ℝ) * h
    1 ≤ N ∧ t_h ∈ Set.Icc (-L) L ∧ L / 2 ≤ |t_h| ∧ |t_h| ≤ L := by
  dsimp
  set N : ℕ := Nat.floor (L / |h|)
  have hdiv_nonneg : 0 ≤ L / |h| := by positivity
  have hN_le : (N : ℝ) ≤ L / |h| := by
    simpa [N] using (Nat.floor_le hdiv_nonneg)
  have hdiv_gt_one : (1 : ℝ) < L / |h| := by
    have hdiv_gt_two : (2 : ℝ) < L / |h| := by
      rw [lt_div_iff₀ hh0]
      linarith
    linarith
  have hN_pos : 0 < N := Nat.floor_pos.mpr hdiv_gt_one.le
  have hN_one : 1 ≤ N := Nat.succ_le_of_lt hN_pos
  have hN_lower : L / |h| - 1 < (N : ℝ) := by
    have hlt : L / |h| < (N : ℝ) + 1 := by
      simpa [N] using (Nat.lt_floor_add_one (L / |h|))
    linarith
  have hmul_upper : (N : ℝ) * |h| ≤ L := by
    calc
      (N : ℝ) * |h| ≤ (L / |h|) * |h| := by
        exact mul_le_mul_of_nonneg_right hN_le (abs_nonneg h)
      _ = L := by
        field_simp [hh0.ne']
  have hmul_lower : L / 2 < (N : ℝ) * |h| := by
    have hmul :
        (L / |h| - 1) * |h| < (N : ℝ) * |h| := by
      exact mul_lt_mul_of_pos_right hN_lower hh0
    have hrewrite : (L / |h| - 1) * |h| = L - |h| := by
      field_simp [hh0.ne']
    have hhalf_lt : L / 2 < L - |h| := by
      linarith
    rw [hrewrite] at hmul
    linarith
  have habs_eq : |((N : ℝ) * h)| = (N : ℝ) * |h| := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ (N : ℝ) by positivity)]
  have ht_mem : ((N : ℝ) * h) ∈ Set.Icc (-L) L := by
    rw [Set.mem_Icc]
    exact abs_le.mp (by simpa [habs_eq] using hmul_upper)
  have ht_lower : L / 2 ≤ |((N : ℝ) * h)| := by
    rw [habs_eq]
    exact le_of_lt hmul_lower
  have ht_upper : |((N : ℝ) * h)| ≤ L := by
    simpa [habs_eq] using hmul_upper
  exact ⟨hN_one, ht_mem, ht_lower, ht_upper⟩

/-- Helper for Exercise 15.4.4: compact-uniform reciprocal linearization on one interval already
forces differentiability of the characteristic function at `0`. -/
private lemma charFun_hasDerivAt_zero_of_uniformReciprocalLinearizationOn
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℂ} {L : ℝ}
    (hL : 0 < L)
    (hUniform :
      TendstoUniformlyOn
        (fun n : ℕ ↦ fun t : ℝ ↦ (n : ℂ) * (charFun μ (t / n) - 1))
        (fun t : ℝ ↦ t * c)
        atTop
        (Set.Icc (-L) L)) :
    HasDerivAt (charFun μ) c 0 := by
  -- Proof comment: evaluate the compact-uniform estimate at the floor-rescaled sample
  -- `t_h = floor (L / |h|) * h`, then divide by `t_h` to recover the slope at the original `h`.
  rw [hasDerivAt_iff_tendsto_slope_zero]
  rw [Metric.tendsto_nhdsWithin_nhds]
  rw [Metric.tendstoUniformlyOn_iff] at hUniform
  intro ε hε
  rcases eventually_atTop.1 (hUniform (ε * (L / 2)) (by positivity)) with ⟨N0, hN0⟩
  refine ⟨min (L / 2) (L / (N0 + 1 : ℝ)), by positivity, ?_⟩
  intro h hh_ne hhδ
  have hhδ' : |h| < min (L / 2) (L / (N0 + 1 : ℝ)) := by
    simpa [Real.dist_eq] using hhδ
  have hh0 : 0 < |h| := abs_pos.mpr hh_ne
  have hh_half : |h| < L / 2 := lt_of_lt_of_le hhδ' (min_le_left _ _)
  have hh_index : |h| < L / (N0 + 1 : ℝ) := lt_of_lt_of_le hhδ' (min_le_right _ _)
  set N : ℕ := Nat.floor (L / |h|)
  set t_h : ℝ := (N : ℝ) * h
  have hRescale :
      1 ≤ N ∧ t_h ∈ Set.Icc (-L) L ∧ L / 2 ≤ |t_h| ∧ |t_h| ≤ L := by
    simpa [N, t_h] using
      (floorRescaling_memIcc_and_abs_bounds (L := L) (h := h) hL hh0 hh_half)
  rcases hRescale with ⟨hN_one, ht_mem, ht_lower, ht_upper⟩
  have hN_ne : N ≠ 0 := Nat.one_le_iff_ne_zero.mp hN_one
  have hN0_le : N0 ≤ N := by
    apply Nat.le_floor
    have hmul_succ : ((N0 : ℝ) + 1) * |h| < L := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (N0 + 1 : ℝ))] at hh_index
      simpa [mul_comm, mul_left_comm, mul_assoc] using hh_index
    have hmul : (N0 : ℝ) * |h| < L := by
      have hle :
          (N0 : ℝ) * |h| ≤ ((N0 : ℝ) + 1) * |h| := by
        have hstep : (N0 : ℝ) ≤ (N0 : ℝ) + 1 := by linarith
        exact mul_le_mul_of_nonneg_right hstep (abs_nonneg h)
      exact lt_of_le_of_lt hle hmul_succ
    rw [le_div_iff₀ hh0]
    simpa [mul_comm] using hmul.le
  have ht_eq : t_h / N = h := by
    dsimp [t_h]
    field_simp [hN_ne]
  have hApprox :
      ‖((N : ℂ) * (charFun μ h - 1)) - t_h * c‖ < ε * (L / 2) := by
    have hApproxRaw := hN0 N hN0_le t_h ht_mem
    rw [dist_eq_norm] at hApproxRaw
    have hApproxRaw' :
        ‖t_h * c - ((N : ℂ) * (charFun μ h - 1))‖ < ε * (L / 2) := by
      simpa [ht_eq] using hApproxRaw
    simpa [norm_sub_rev] using hApproxRaw'
  have hApproxSmul :
      ‖((N : ℝ) • (charFun μ h - 1)) - t_h • c‖ < ε * (L / 2) := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hApprox
  have ht_ne : t_h ≠ 0 := by
    apply abs_ne_zero.mp
    exact ne_of_gt (lt_of_lt_of_le (by positivity : (0 : ℝ) < L / 2) ht_lower)
  have hratio : t_h⁻¹ * (N : ℝ) = h⁻¹ := by
    dsimp [t_h]
    field_simp [hN_ne, hh_ne]
  have hSlopeCore :
      ((h : ℂ)⁻¹ * (charFun μ h - 1)) - c =
        ((t_h : ℂ)⁻¹ * (((N : ℂ) * (charFun μ h - 1)) - t_h * c)) := by
    calc
      ((h : ℂ)⁻¹ * (charFun μ h - 1)) - c
          = (((t_h : ℂ)⁻¹ * (N : ℂ)) * (charFun μ h - 1)) -
              (((t_h : ℂ)⁻¹ * (t_h : ℂ)) * c) := by
              rw [show ((h : ℂ)⁻¹ : ℂ) = ((t_h : ℂ)⁻¹ * (N : ℂ)) by
                    exact_mod_cast hratio.symm]
              rw [inv_mul_cancel₀ (show (t_h : ℂ) ≠ 0 by exact_mod_cast ht_ne), one_mul]
      _ = ((t_h : ℂ)⁻¹ * (((N : ℂ) * (charFun μ h - 1)) - t_h * c)) := by
            ring
  have hSlopeNorm :
      ‖((h : ℂ)⁻¹ * (charFun μ h - 1)) - c‖ < ε := by
    rw [hSlopeCore]
    have hnorm_inv : ‖((t_h : ℂ)⁻¹)‖ = |t_h|⁻¹ := by
      rw [norm_inv]
      simpa using congrArg Inv.inv (Complex.norm_real t_h)
    calc
      ‖((t_h : ℂ)⁻¹ * (((N : ℂ) * (charFun μ h - 1)) - t_h * c))‖
          = |t_h|⁻¹ * ‖((N : ℂ) * (charFun μ h - 1)) - t_h * c‖ := by
              rw [norm_mul, hnorm_inv]
      _ < |t_h|⁻¹ * (ε * (L / 2)) := by
            exact mul_lt_mul_of_pos_left hApprox (by positivity)
      _ ≤ (L / 2)⁻¹ * (ε * (L / 2)) := by
            have hInv :
                |t_h|⁻¹ ≤ (L / 2)⁻¹ := by
              simpa [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < L / 2)
                ht_lower
            exact mul_le_mul_of_nonneg_right hInv (by positivity)
      _ = ε := by
            field_simp [show (L / 2) ≠ 0 by positivity]
  have hSlopeNormSmul : ‖h⁻¹ • (charFun μ h - 1) - c‖ < ε := by
    have hsmul :
        h⁻¹ • (charFun μ h - 1) = ((h : ℂ)⁻¹ * (charFun μ h - 1)) := by
      show (((h⁻¹ : ℝ) : ℂ) * (charFun μ h - 1)) = ((h : ℂ)⁻¹ * (charFun μ h - 1))
      simp
    rw [hsmul]
    exact hSlopeNorm
  have huniv : (μ.real Set.univ : ℂ) = 1 := by
    simp [Measure.real]
  rw [dist_eq_norm, zero_add, charFun_zero, huniv]
  exact hSlopeNormSmul

/-- Helper for Exercise 15.4.4: on a fixed compact interval, the reciprocal-frequency
characteristic-function defects are eventually uniformly smaller than any prescribed `ε > 0`. -/
private lemma canonicalAverage_reciprocal_charFun_eventually_smallOn
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Set.Icc (-L) L, ‖charFun μ (t / n) - 1‖ ≤ ε := by
  have hcont :
      ContinuousAt (fun s : ℝ ↦ charFun μ s - 1) 0 := by
    simpa using
      ((MeasureTheory.continuous_charFun (μ := μ)).continuousAt.sub continuousAt_const)
  have hSmall : Set.Iio ε ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hε
  have hcontNorm : ContinuousAt (fun s : ℝ ↦ ‖charFun μ s - 1‖) 0 := hcont.norm
  have hcontNormZero :
      Tendsto (fun s : ℝ ↦ ‖charFun μ s - 1‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
    simpa [ContinuousAt, charFun_zero] using hcontNorm
  have hEventuallySmall :
      ∀ᶠ s : ℝ in 𝓝 0, ‖charFun μ s - 1‖ < ε := by
    exact hcontNormZero hSmall
  rcases Metric.mem_nhds_iff.1 hEventuallySmall with ⟨δ, hδpos, hδ⟩
  have hScale :
      Tendsto (fun n : ℕ ↦ L * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_const_nhds.mul
        (tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0)))
  have hEventuallyBound :
      ∀ᶠ n : ℕ in atTop, L * (n : ℝ)⁻¹ < δ := by
    exact hScale (Iio_mem_nhds hδpos)
  filter_upwards [eventually_ge_atTop 1, hEventuallyBound] with n hn hnd t ht
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have htabs : |t| ≤ L := by
    rw [abs_le]
    exact ht
  have htdist : dist (t / n) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_div]
    have hmul :
        |t| * |(n : ℝ)|⁻¹ ≤ L * (n : ℝ)⁻¹ := by
      have habs_n : |(n : ℝ)| = n := abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)
      rw [habs_n]
      gcongr
    exact lt_of_le_of_lt hmul hnd
  exact le_of_lt (hδ htdist)

/-- Helper for Exercise 15.4.4: on one compact interval where the Dirac phase stays in the
principal half-ball, the logarithms of the canonical average characteristic functions converge
uniformly to the linear phase `t ↦ t * ((m : ℂ) * I)`. -/
private lemma canonicalAverage_natMulLogCharFun_tendstoUniformlyOn
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ} {L : ℝ}
    (hAverage :
      TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
        (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ ↦ m))
    (hL : 0 < L)
    (hPhaseQuarter :
      ∀ t ∈ Set.Icc (-L) L,
        ‖Complex.exp (t * ((m : ℂ) * Complex.I)) - 1‖ ≤ (1 / 4 : ℝ)) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun t : ℝ ↦ (n : ℂ) * Complex.log (charFun μ (t / n)))
      (fun t : ℝ ↦ t * ((m : ℂ) * Complex.I))
      atTop
      (Set.Icc (-L) L) := by
  let K : Set ℝ := Set.Icc (-L) L
  let c : ℂ := (m : ℂ) * Complex.I
  let phase : ℝ → ℂ := fun t ↦ Complex.exp (t * c)
  let slitBall : Set ℂ := Metric.closedBall (1 : ℂ) (3 / 4 : ℝ)
  have hPow :
      TendstoUniformlyOn
        (fun n : ℕ ↦ fun t : ℝ ↦ (charFun μ (t / n)) ^ n)
        phase
        atTop
        K :=
    canonicalAverage_charFunPow_tendstoUniformlyOn (μ := μ) (m := m) hAverage K isCompact_Icc
  have hPowMetric := hPow
  rw [Metric.tendstoUniformlyOn_iff] at hPowMetric
  have hPowQuarter :
      ∀ᶠ n : ℕ in atTop,
        ∀ t ∈ K, ‖(charFun μ (t / n)) ^ n - phase t‖ < (1 / 4 : ℝ) := by
    filter_upwards [hPowMetric (1 / 4) (by norm_num)] with n hn t ht
    simpa [phase, K, dist_eq_norm, norm_sub_rev] using hn t ht
  have hEventuallyPowIn :
      ∀ᶠ n : ℕ in atTop, ∀ t ∈ K, (charFun μ (t / n)) ^ n ∈ slitBall := by
    filter_upwards [hPowQuarter] with n hn t ht
    change dist ((charFun μ (t / n)) ^ n) 1 ≤ (3 / 4 : ℝ)
    have hdist :
        dist ((charFun μ (t / n)) ^ n) 1 ≤
          dist ((charFun μ (t / n)) ^ n) (phase t) + dist (phase t) 1 := by
      simpa using dist_triangle ((charFun μ (t / n)) ^ n) (phase t) 1
    have hPhaseDist : dist (phase t) 1 ≤ 1 / 4 := by
      simpa [phase, dist_eq_norm] using hPhaseQuarter t ht
    have hsum_lt :
        dist ((charFun μ (t / n)) ^ n) (phase t) + dist (phase t) 1 < 1 / 2 := by
      have hPowDist : dist ((charFun μ (t / n)) ^ n) (phase t) < 1 / 4 := by
        simpa [dist_eq_norm] using hn t ht
      have hsum :
          dist ((charFun μ (t / n)) ^ n) (phase t) + dist (phase t) 1 < 1 / 4 + 1 / 4 :=
        add_lt_add_of_lt_of_le hPowDist hPhaseDist
      have hhalf : (1 / 4 : ℝ) + 1 / 4 = 1 / 2 := by norm_num
      rw [hhalf] at hsum
      exact hsum
    have hbound : dist ((charFun μ (t / n)) ^ n) 1 < 1 / 2 :=
      lt_of_le_of_lt hdist hsum_lt
    exact le_trans (le_of_lt hbound) (by norm_num)
  have hPhaseIn : ∀ t ∈ K, phase t ∈ slitBall := by
    intro t ht
    change dist (phase t) 1 ≤ (3 / 4 : ℝ)
    have hPhaseDist : dist (phase t) 1 ≤ 1 / 4 := by
      simpa [phase, dist_eq_norm] using hPhaseQuarter t ht
    exact le_trans hPhaseDist (by norm_num)
  have hLogCont : ContinuousOn Complex.log slitBall := by
    refine continuousOn_id.clog ?_
    intro z hz
    have hzball : dist z 1 ≤ (3 / 4 : ℝ) := hz
    have hlt : ‖z - 1‖ < 1 := by
      have hle : ‖z - 1‖ ≤ (3 / 4 : ℝ) := by simpa [dist_eq_norm] using hzball
      exact lt_of_le_of_lt hle (by norm_num)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Complex.mem_slitPlane_of_norm_lt_one (z := z - 1) hlt)
  have hLogUC : UniformContinuousOn Complex.log slitBall :=
    (isCompact_closedBall (1 : ℂ) (3 / 4 : ℝ)).uniformContinuousOn_of_continuous hLogCont
  have hLogPow :
      TendstoUniformlyOn
        (fun n : ℕ ↦ fun t : ℝ ↦ Complex.log ((charFun μ (t / n)) ^ n))
        (fun t : ℝ ↦ Complex.log (phase t))
        atTop
        K :=
    hLogUC.comp_tendstoUniformlyOn_eventually hEventuallyPowIn hPhaseIn hPow
  have hzero_mem : (0 : ℝ) ∈ K := by
    dsimp [K]
    constructor <;> linarith
  let G : C(K, ℂ) := ⟨fun x ↦ (x : ℝ) * c, by fun_prop⟩
  have hG0 : G ⟨0, hzero_mem⟩ = 0 := by
    simp [G, c]
  have hGslit : ∀ x, Complex.exp (G x) ∈ Complex.slitPlane := by
    intro x
    have hlt : ‖Complex.exp ((x : ℝ) * c) - 1‖ < 1 := by
      exact lt_of_le_of_lt (hPhaseQuarter x.1 x.2) (by norm_num)
    simpa [G, c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Complex.mem_slitPlane_of_norm_lt_one (z := Complex.exp ((x : ℝ) * c) - 1) hlt)
  have hLogPhase := log_exp_eq_of_mem_slitPlaneOnIcc (L := L) (hL := le_of_lt hL) G hG0 hGslit
  rw [Metric.tendstoUniformlyOn_iff] at hLogPow ⊢
  intro ε hε
  filter_upwards
      [hLogPow ε hε, eventually_ge_atTop 1, canonicalAverage_reciprocal_charFun_eventually_halfOn
        (μ := μ) hL, hPowQuarter] with n hnLog hn hfHalf hPowQ t ht
  have hLogEq :
      Complex.log ((charFun μ (t / n)) ^ n) =
        (n : ℂ) * Complex.log (charFun μ (t / n)) :=
    canonicalAverage_logPow_eq_natMulLogOn (μ := μ) (L := L) (hL := le_of_lt hL) hn
      (hFactorHalf := hfHalf) (hPowHalf := fun s hs ↦ by
        have hdist :
            dist ((charFun μ (s / n)) ^ n) 1 ≤
              dist ((charFun μ (s / n)) ^ n) (phase s) + dist (phase s) 1 := by
          simpa using dist_triangle ((charFun μ (s / n)) ^ n) (phase s) 1
        have hPhaseDist : dist (phase s) 1 ≤ 1 / 4 := by
          simpa [phase, dist_eq_norm] using hPhaseQuarter s hs
        have hsum_lt :
            dist ((charFun μ (s / n)) ^ n) (phase s) + dist (phase s) 1 < 1 / 2 := by
          have hPowDist : dist ((charFun μ (s / n)) ^ n) (phase s) < 1 / 4 := by
            simpa [dist_eq_norm] using hPowQ s hs
          have hsum :
              dist ((charFun μ (s / n)) ^ n) (phase s) + dist (phase s) 1 < 1 / 4 + 1 / 4 :=
            add_lt_add_of_lt_of_le hPowDist hPhaseDist
          have hhalf : (1 / 4 : ℝ) + 1 / 4 = 1 / 2 := by norm_num
          rw [hhalf] at hsum
          exact hsum
        have hbound : dist ((charFun μ (s / n)) ^ n) 1 < 1 / 2 :=
          lt_of_le_of_lt hdist hsum_lt
        simpa [dist_eq_norm] using le_of_lt hbound) t ht
  have hPhaseLog : Complex.log (phase t) = t * c := by
    simpa [phase, G, c] using hLogPhase ⟨t, ht⟩
  simpa [c, hLogEq, hPhaseLog, dist_eq_norm, norm_sub_rev] using hnLog t ht

/-- Helper for Exercise 15.4.4: the compact-uniform logarithmic convergence gives one eventual
uniform bound for the logarithmic linearization on the same interval. -/
private lemma canonicalAverage_natMulLogCharFun_eventually_boundedOn
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ} {L : ℝ}
    (hAverage :
      TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
        (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ ↦ m))
    (hL : 0 < L)
    (hPhaseQuarter :
      ∀ t ∈ Set.Icc (-L) L,
        ‖Complex.exp (t * ((m : ℂ) * Complex.I)) - 1‖ ≤ (1 / 4 : ℝ)) :
    ∃ B > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ t ∈ Set.Icc (-L) L, ‖(n : ℂ) * Complex.log (charFun μ (t / n))‖ ≤ B := by
  let c : ℂ := (m : ℂ) * Complex.I
  refine ⟨L * ‖c‖ + 1, by positivity, ?_⟩
  have hUniform :=
    canonicalAverage_natMulLogCharFun_tendstoUniformlyOn
      (μ := μ) (m := m) hAverage hL hPhaseQuarter
  rw [Metric.tendstoUniformlyOn_iff] at hUniform
  filter_upwards [hUniform 1 (by norm_num : (0 : ℝ) < 1)] with n hn t ht
  have hBoundPhase : ‖t * c‖ ≤ L * ‖c‖ := by
    have htabs : |t| ≤ L := by
      rw [abs_le]
      exact ht
    calc
      ‖t * c‖ = |t| * ‖c‖ := by
        simpa [Real.norm_eq_abs] using (norm_mul (t : ℂ) c)
      _ ≤ L * ‖c‖ := by
        gcongr
  have hn' : ‖(n : ℂ) * Complex.log (charFun μ (t / n)) - t * c‖ < 1 := by
    simpa [c, dist_eq_norm, dist_comm, norm_sub_rev] using hn t ht
  calc
    ‖(n : ℂ) * Complex.log (charFun μ (t / n))‖
        ≤ ‖(n : ℂ) * Complex.log (charFun μ (t / n)) - t * c‖ + ‖t * c‖ := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            (norm_add_le ((n : ℂ) * Complex.log (charFun μ (t / n)) - t * c) (t * c))
    _ ≤ 1 + L * ‖c‖ := by
          linarith
    _ = L * ‖c‖ + 1 := by ring

/-- Helper for Exercise 15.4.4: after separating the logarithmic transport from its quadratic
remainder, the residual term `n * (log z_n - (z_n - 1))` vanishes uniformly on one compact
interval. -/
private lemma canonicalAverage_natMulLogSubCharFunSubOne_tendstoUniformlyOn_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ} {L : ℝ}
    (hAverage :
      TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
        (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ ↦ m))
    (hL : 0 < L)
    (hPhaseQuarter :
      ∀ t ∈ Set.Icc (-L) L,
        ‖Complex.exp (t * ((m : ℂ) * Complex.I)) - 1‖ ≤ (1 / 4 : ℝ)) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun t : ℝ ↦
        (n : ℂ) * (Complex.log (charFun μ (t / n)) - (charFun μ (t / n) - 1)))
      (fun _ : ℝ ↦ 0)
      atTop
      (Set.Icc (-L) L) := by
  let K : Set ℝ := Set.Icc (-L) L
  obtain ⟨B, hBpos, hBounded⟩ :=
    canonicalAverage_natMulLogCharFun_eventually_boundedOn
      (μ := μ) (m := m) hAverage hL hPhaseQuarter
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hSmall :
      ∀ᶠ n : ℕ in atTop,
        ∀ t ∈ K, ‖charFun μ (t / n) - 1‖ ≤ ε / (4 * B) :=
    canonicalAverage_reciprocal_charFun_eventually_smallOn
      (μ := μ) (L := L) (ε := ε / (4 * B)) hL (by positivity)
  filter_upwards
      [hBounded, canonicalAverage_reciprocal_charFun_eventually_halfOn (μ := μ) hL, hSmall] with
    n hnBound hnHalf hnSmall t ht
  let z : ℂ := charFun μ (t / n) - 1
  have hz_half : ‖z‖ ≤ (1 / 2 : ℝ) := by
    simpa [z, K] using hnHalf t ht
  have hz_small : ‖z‖ ≤ ε / (4 * B) := by
    simpa [z, K] using hnSmall t ht
  have hz_lt_one : ‖z‖ < 1 := lt_of_le_of_lt hz_half (by norm_num)
  have hCharSlit : charFun μ (t / n) ∈ Complex.slitPlane := by
    simpa [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Complex.mem_slitPlane_of_norm_lt_one (z := z) hz_lt_one)
  have hCharNe : charFun μ (t / n) ≠ 0 := Complex.slitPlane_ne_zero hCharSlit
  have hLogNorm :
      ‖Complex.log (charFun μ (t / n))‖ ≤ (3 / 2 : ℝ) * ‖z‖ := by
    simpa [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Complex.norm_log_one_add_half_le_self (z := z) hz_half)
  have hLogUnit : ‖Complex.log (charFun μ (t / n))‖ ≤ 1 := by
    calc
      ‖Complex.log (charFun μ (t / n))‖ ≤ (3 / 2 : ℝ) * ‖z‖ := hLogNorm
      _ ≤ 1 := by
            nlinarith
  have hExpSub :
      ‖z‖ ≤ 2 * ‖Complex.log (charFun μ (t / n))‖ := by
    calc
      ‖z‖ = ‖charFun μ (t / n) - 1‖ := by rfl
      _ = ‖Complex.exp (Complex.log (charFun μ (t / n))) - 1‖ := by
            rw [Complex.exp_log hCharNe]
      _ ≤ 2 * ‖Complex.log (charFun μ (t / n))‖ := by
            exact Complex.norm_exp_sub_one_le hLogUnit
  have hz_eq : charFun μ (t / n) = 1 + z := by
    simp [z]
  have hRemLe :
      ‖Complex.log (charFun μ (t / n)) - (charFun μ (t / n) - 1)‖ ≤ ‖z‖ ^ (2 : ℕ) := by
    calc
      ‖Complex.log (charFun μ (t / n)) - (charFun μ (t / n) - 1)‖
          = ‖Complex.log (1 + z) - z‖ := by
              rw [hz_eq]
              ring_nf
      _ ≤ ‖z‖ ^ (2 : ℕ) * (1 - ‖z‖)⁻¹ / 2 := by
            exact Complex.norm_log_one_add_sub_self_le hz_lt_one
      _ ≤ ‖z‖ ^ (2 : ℕ) := by
            have hInv : (1 - ‖z‖)⁻¹ ≤ 2 := by
              have hge : (1 / 2 : ℝ) ≤ 1 - ‖z‖ := by
                linarith
              have htmp : 1 / (1 - ‖z‖) ≤ 1 / (1 / 2 : ℝ) := by
                exact one_div_le_one_div_of_le (by norm_num : 0 < (1 / 2 : ℝ)) hge
              simpa using htmp
            nlinarith [norm_nonneg z]
  have hScaledLog : (n : ℝ) * ‖Complex.log (charFun μ (t / n))‖ ≤ B := by
    simpa [norm_mul, Complex.norm_natCast, mul_comm, mul_left_comm, mul_assoc] using hnBound t ht
  have hScaledZ : (n : ℝ) * ‖z‖ ≤ 2 * B := by
    calc
      (n : ℝ) * ‖z‖ ≤ (n : ℝ) * (2 * ‖Complex.log (charFun μ (t / n))‖) := by
            gcongr
      _ = 2 * ((n : ℝ) * ‖Complex.log (charFun μ (t / n))‖) := by
            ring
      _ ≤ 2 * B := by
            gcongr
  have hScaledRem : (n : ℝ) * ‖z‖ ^ (2 : ℕ) ≤ ε / 2 := by
    calc
      (n : ℝ) * ‖z‖ ^ (2 : ℕ) = ((n : ℝ) * ‖z‖) * ‖z‖ := by
            ring
      _ ≤ (2 * B) * ‖z‖ := by
            gcongr
      _ ≤ (2 * B) * (ε / (4 * B)) := by
            gcongr
      _ = ε / 2 := by
            field_simp [hBpos.ne']
            ring
  have hCore :
      ‖(n : ℂ) * (Complex.log (charFun μ (t / n)) - (charFun μ (t / n) - 1))‖ ≤ ε / 2 := by
    calc
      ‖(n : ℂ) * (Complex.log (charFun μ (t / n)) - (charFun μ (t / n) - 1))‖
          = (n : ℝ) * ‖Complex.log (charFun μ (t / n)) - (charFun μ (t / n) - 1)‖ := by
              rw [norm_mul, Complex.norm_natCast]
      _ ≤ (n : ℝ) * ‖z‖ ^ (2 : ℕ) := by
            gcongr
      _ ≤ ε / 2 := hScaledRem
  have hhalf_lt : ε / 2 < ε := by linarith
  simpa [dist_eq_norm] using lt_of_le_of_lt hCore hhalf_lt

/-- Exercise 15.4.4: the remaining owner theorem converts canonical average
convergence into the Feller tail condition together with convergence of the canonical truncation
integrals. The transport from canonical truncation integrals to the textbook `Set.Icc` form is
already available locally. -/
private theorem canonicalAverage_hasDerivAtCharFunZero_of_tendstoInMeasure
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ}
    (hAverage :
      TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
        (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ ↦ m)) :
    HasDerivAt (charFun μ) ((m : ℂ) * Complex.I) 0 := by
  -- Route correction: isolate the analytic reverse-WLL step as the single remaining owner lemma,
  -- so the Feller tail/truncation transport below can be discharged by Remark 15.35 immediately.
  let c : ℂ := (m : ℂ) * Complex.I
  have hcontPhase :
      ContinuousAt (fun t : ℝ ↦ Complex.exp (t * c) - 1) 0 := by
    fun_prop
  have hQuarterNhd : Set.Iio (1 / 4 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
  have hcontPhaseNorm : ContinuousAt (fun t : ℝ ↦ ‖Complex.exp (t * c) - 1‖) 0 := hcontPhase.norm
  have hcontPhaseNormZero :
      Tendsto (fun t : ℝ ↦ ‖Complex.exp (t * c) - 1‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
    simpa [ContinuousAt] using hcontPhaseNorm
  have hEventuallyQuarter :
      ∀ᶠ t : ℝ in 𝓝 0, ‖Complex.exp (t * c) - 1‖ < (1 / 4 : ℝ) := by
    exact hcontPhaseNormZero hQuarterNhd
  rcases Metric.mem_nhds_iff.1 hEventuallyQuarter with ⟨δ, hδpos, hδ⟩
  let L : ℝ := δ / 2
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hPhaseQuarter :
      ∀ t ∈ Set.Icc (-L) L, ‖Complex.exp (t * c) - 1‖ ≤ (1 / 4 : ℝ) := by
    intro t ht
    have htabs : |t| ≤ L := by
      rw [abs_le]
      exact ht
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      have hlt : |t| < δ := by
        dsimp [L] at htabs
        linarith
      simpa using hlt
    exact le_of_lt (hδ hdist)
  -- Proof comment: first recover the compact-uniform logarithmic linearization on one small
  -- interval around `0`, then subtract the quadratic log remainder.
  have hLogLinear :=
    canonicalAverage_natMulLogCharFun_tendstoUniformlyOn
      (μ := μ) (m := m) hAverage hL hPhaseQuarter
  have hRemainder :=
    canonicalAverage_natMulLogSubCharFunSubOne_tendstoUniformlyOn_zero
      (μ := μ) (m := m) hAverage hL hPhaseQuarter
  have hLinear :
      TendstoUniformlyOn
        (fun n : ℕ ↦ fun t : ℝ ↦ (n : ℂ) * (charFun μ (t / n) - 1))
        (fun t : ℝ ↦ t * c)
        atTop
        (Set.Icc (-L) L) := by
    rw [Metric.tendstoUniformlyOn_iff] at hLogLinear hRemainder ⊢
    intro ε hε
    filter_upwards [hLogLinear (ε / 2) (by positivity), hRemainder (ε / 2) (by positivity)] with
      n hnLog hnRem t ht
    have hDecomp :
        (n : ℂ) * (charFun μ (t / n) - 1) =
          (n : ℂ) * Complex.log (charFun μ (t / n)) -
            (n : ℂ) * (Complex.log (charFun μ (t / n)) - (charFun μ (t / n) - 1)) := by
      ring
    rw [dist_eq_norm, hDecomp, norm_sub_rev]
    have hnLog' :
        ‖(n : ℂ) * Complex.log (charFun μ (t / n)) - t * c‖ < ε / 2 := by
      simpa [dist_eq_norm, dist_comm, norm_sub_rev, c] using hnLog t ht
    have hnRem' :
        ‖(n : ℂ) * (Complex.log (charFun μ (t / n)) - (charFun μ (t / n) - 1))‖ < ε / 2 := by
      simpa [dist_eq_norm] using hnRem t ht
    let A : ℂ := (n : ℂ) * Complex.log (charFun μ (t / n))
    let B : ℂ := (n : ℂ) * (Complex.log (charFun μ (t / n)) - (charFun μ (t / n) - 1))
    calc
      ‖(A - B) - t * c‖ ≤ ‖A - t * c‖ + ‖B‖ := by
        have htriangle := norm_add_le (A - t * c) (-B)
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, norm_neg] using htriangle
      _ < ε / 2 + ε / 2 := by
            simpa [A, B] using add_lt_add hnLog' hnRem'
      _ = ε := by ring
  -- Proof comment: the assembled first-order asymptotic now matches the existing floor-rescaling
  -- closure lemma exactly, so the derivative follows without further logarithmic transport.
  simpa [c] using charFun_hasDerivAt_zero_of_uniformReciprocalLinearizationOn
    (μ := μ) (c := c) hL hLinear

/-- Helper for Exercise 15.4.4: for the identity on `ℝ`, the canonical truncation integral is the
textbook interval integral on `[-A, A]`. -/
private lemma integralTruncationId_eq_intervalIntegral
    {μ : Measure ℝ} {A : ℝ} (hA : 0 ≤ A) :
    ∫ y, ProbabilityTheory.truncation id A y ∂μ = ∫ y in -A..A, y ∂μ := by
  -- Proof comment: specialize mathlib's truncation-integral identity to `id` and collapse the
  -- pushforward along `id`.
  simpa [Measure.map_id] using
    (ProbabilityTheory.integral_truncation_eq_intervalIntegral
      (μ := μ) (f := id) aestronglyMeasurable_id hA)

/-- Helper for Exercise 15.4.4: if the Feller scaled-tail term tends to `0`, then the bare tail
mass also tends to `0`. -/
private lemma tailMass_tendstoZero_of_scaledTail
    {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    Tendsto (fun x ↦ x * μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) →
      Tendsto (fun x ↦ μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) := by
  intro htail
  -- Proof comment: for `x ≥ 1`, the unscaled tail mass is bounded by the scaled expression.
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg) ?_ htail
  filter_upwards [Ici_mem_atTop (1 : ℝ)] with x hx
  have hx' : 1 ≤ x := hx
  calc
    μ.real {y : ℝ | x < |y|} = 1 * μ.real {y : ℝ | x < |y|} := by ring
    _ ≤ x * μ.real {y : ℝ | x < |y|} := by
          gcongr

/-- Helper for Exercise 15.4.4: the shell between the textbook cutoff `[-x, x]` and the owner
cutoff `[-(x + 1), x + 1]` is controlled by the tail mass. -/
private lemma textbookIccIntegral_sub_truncationIntegral_shift_le_tail
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    ‖(∫ y in Set.Icc (-x) x, y ∂μ) - ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ‖ ≤
      (x + 1) * μ.real {y : ℝ | x < |y|} := by
  let shell : Set ℝ := Set.Ioc (-(x + 1)) (x + 1) \ Set.Icc (-x) x
  have hx1 : 0 ≤ x + 1 := by linarith
  have hsub : Set.Icc (-x) x ⊆ Set.Ioc (-(x + 1)) (x + 1) := by
    intro y hy
    constructor
    · linarith [hy.1]
    · linarith [hy.2]
  have hInt :
      IntegrableOn (fun y : ℝ ↦ y) (Set.Ioc (-(x + 1)) (x + 1)) μ := by
    -- Proof comment: the identity is integrable on the enclosing compact interval.
    exact (continuous_id.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hShellEq :
      (∫ y in Set.Icc (-x) x, y ∂μ) - ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ =
        -∫ y in shell, y ∂μ := by
    -- Proof comment: replacing the truncation integral by the larger interval integral turns the
    -- difference into the integral over the missing outer shell.
    have hTrunc :
        ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ =
          ∫ y in Set.Ioc (-(x + 1)) (x + 1), y ∂μ := by
      calc
        ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ =
            ∫ y in Set.Ioc (-(x + 1)) (x + 1), y ∂μ -
              ∫ y in Set.Ioc (x + 1) (-(x + 1)), y ∂μ := by
                simpa [intervalIntegral] using
                  (integralTruncationId_eq_intervalIntegral (μ := μ) (A := x + 1) hx1)
        _ = ∫ y in Set.Ioc (-(x + 1)) (x + 1), y ∂μ := by
          have hZero : ∫ y in Set.Ioc (x + 1) (-1 + -x), y ∂μ = 0 := by
            have hEmpty : Set.Ioc (x + 1) (-1 + -x) = ∅ := by
              apply Set.Ioc_eq_empty_of_le
              linarith
            rw [hEmpty, MeasureTheory.setIntegral_empty]
          simpa [sub_eq_add_neg] using hZero
    rw [hTrunc]
    have hDiff :
        ∫ y in shell, y ∂μ =
          ∫ y in Set.Ioc (-(x + 1)) (x + 1), y ∂μ - ∫ y in Set.Icc (-x) x, y ∂μ := by
      simpa [shell] using
        (MeasureTheory.setIntegral_diff (μ := μ) (f := fun y : ℝ ↦ y) measurableSet_Icc hInt hsub)
    calc
      (∫ y in Set.Icc (-x) x, y ∂μ) - ∫ y in Set.Ioc (-(x + 1)) (x + 1), y ∂μ
          = -((∫ y in Set.Ioc (-(x + 1)) (x + 1), y ∂μ) - ∫ y in Set.Icc (-x) x, y ∂μ) := by
              ring
      _ = -∫ y in shell, y ∂μ := by rw [hDiff]
  have hShellBound :
      ‖∫ y in shell, y ∂μ‖ ≤ (x + 1) * μ.real shell := by
    -- Proof comment: the shell integral is bounded by the radius times the shell mass.
    refine MeasureTheory.norm_setIntegral_le_of_norm_le_const ?_ ?_
    · simpa using (measure_lt_top μ shell)
    · intro y hy
      have hyIoc : y ∈ Set.Ioc (-(x + 1)) (x + 1) := hy.1
      have hyAbs : |y| ≤ x + 1 := abs_le.2 ⟨by linarith [hyIoc.1], hyIoc.2⟩
      simpa [Real.norm_eq_abs] using hyAbs
  have hShellSubset : shell ⊆ {y : ℝ | x < |y|} := by
    intro y hy
    have hyNot : y ∉ Set.Icc (-x) x := hy.2
    by_cases hle : y ≤ x
    · have hlt : y < -x := by
        by_contra h'
        exact hyNot ⟨le_of_not_gt h', hle⟩
      have hyneg : y < 0 := by linarith
      simpa [abs_of_neg hyneg] using (neg_lt_neg hlt)
    · have hlt : x < y := lt_of_not_ge hle
      have hypos : 0 ≤ y := by linarith [hx, hlt]
      simpa [abs_of_nonneg hypos] using hlt
  calc
    ‖(∫ y in Set.Icc (-x) x, y ∂μ) - ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ‖
        = ‖∫ y in shell, y ∂μ‖ := by rw [hShellEq, norm_neg]
    _ ≤ (x + 1) * μ.real shell := hShellBound
    _ ≤ (x + 1) * μ.real {y : ℝ | x < |y|} := by
      exact mul_le_mul_of_nonneg_left
        (MeasureTheory.measureReal_mono hShellSubset (by finiteness)) hx1

/-- Helper for Exercise 15.4.4: under the scaled-tail hypothesis, the textbook truncated mean on
`Set.Icc (-x) x` converges iff the canonical truncation integral converges. -/
private lemma tendstoTailAndTextbookIccIntegral_iff_tendstoTailAndTruncationIntegral
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ} :
    (Tendsto (fun x ↦ x * μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) ∧
      Tendsto (fun x ↦ ∫ y in Set.Icc (-x) x, y ∂μ) atTop (𝓝 m)) ↔
      (Tendsto (fun x ↦ x * μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) ∧
        Tendsto (fun x ↦ ∫ y, ProbabilityTheory.truncation id x y ∂μ) atTop (𝓝 m)) := by
  have hShift :
      Tendsto (fun x ↦ ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ) atTop (𝓝 m) ↔
        Tendsto (fun x ↦ ∫ y, ProbabilityTheory.truncation id x y ∂μ) atTop (𝓝 m) := by
    constructor
    · intro h
      have hSub : Tendsto (fun x : ℝ ↦ x - 1) atTop atTop := by
        simpa [sub_eq_add_neg] using
          (Filter.tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
      have hComp := h.comp hSub
      convert hComp using 1
      ext x
      simp [Function.comp, sub_eq_add_neg]
    · intro h
      have hAdd : Tendsto (fun x : ℝ ↦ x + 1) atTop atTop := by
        simpa using (Filter.tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
      exact h.comp hAdd
  have hTextbookMinusShifted :
      ∀ {μ : Measure ℝ} [IsProbabilityMeasure μ],
        Tendsto (fun x ↦ x * μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) →
          Tendsto
            (fun x ↦
              (∫ y in Set.Icc (-x) x, y ∂μ) -
                ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ)
            atTop (𝓝 0) := by
    intro μ _ htail
    have hTailMass :
        Tendsto (fun x ↦ μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) := by
      -- Proof comment: first peel off the unscaled tail mass from the scaled-tail hypothesis.
      exact tailMass_tendstoZero_of_scaledTail (μ := μ) htail
    have hShellMass :
        Tendsto (fun x ↦ (x + 1) * μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) := by
      -- Proof comment: the shifted shell term is the scaled-tail term plus the bare tail mass.
      simpa [add_mul, one_mul] using htail.add hTailMass
    refine squeeze_zero_norm' ?_ hShellMass
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with x hx
    exact textbookIccIntegral_sub_truncationIntegral_shift_le_tail (μ := μ) hx
  constructor
  · rintro ⟨htail, hmean⟩
    have hDiffZero := hTextbookMinusShifted (μ := μ) htail
    have hShifted :
        Tendsto (fun x ↦ ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ) atTop (𝓝 m) := by
      have hShifted' :
          Tendsto
            (fun x ↦
              (∫ y in Set.Icc (-x) x, y ∂μ) -
                ((∫ y in Set.Icc (-x) x, y ∂μ) -
                  ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ))
            atTop (𝓝 (m - 0)) := hmean.sub hDiffZero
      convert hShifted' using 1
      · ext x
        ring
      · simp
    exact ⟨htail, hShift.1 hShifted⟩
  · rintro ⟨htail, hmean⟩
    have hDiffZero := hTextbookMinusShifted (μ := μ) htail
    have hShifted :
        Tendsto (fun x ↦ ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ) atTop (𝓝 m) :=
      hShift.2 hmean
    have hTextbook :
        Tendsto
          (fun x ↦
            ((∫ y in Set.Icc (-x) x, y ∂μ) -
                ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ) +
              ∫ y, ProbabilityTheory.truncation id (x + 1) y ∂μ)
          atTop (𝓝 (0 + m)) := hDiffZero.add hShifted
    refine ⟨htail, ?_⟩
    convert hTextbook using 1
    · ext x
      ring
    · simp

/-- Helper for Exercise 15.4.4: once the canonical averages force differentiability of the common
characteristic function at `0`, Remark 15.35 converts that derivative into the Feller tail and
canonical truncation limits. -/
private lemma canonicalAverage_tailAndTruncationIntegral_tendsto
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ}
    (hAverage :
      TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
        (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ ↦ m)) :
    Tendsto (fun x ↦ x * μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) ∧
      Tendsto (fun x ↦ ∫ y, ProbabilityTheory.truncation id x y ∂μ) atTop (𝓝 m) := by
  -- Proof comment: first recover differentiability of the common characteristic function at `0`,
  -- then rewrite the textbook interval criterion from Remark 15.35 into the canonical truncation
  -- form already used in this file.
  have hderiv :
      HasDerivAt (charFun μ) ((m : ℂ) * Complex.I) 0 :=
    canonicalAverage_hasDerivAtCharFunZero_of_tendstoInMeasure hAverage
  exact
    (tendstoTailAndTextbookIccIntegral_iff_tendstoTailAndTruncationIntegral
      (μ := μ) (m := m)).mp
      ((hasDerivAt_charFun_zero_iff_tendsto_tail_and_truncated_mean μ m).1 hderiv)

/-- Helper for Exercise 15.4.4: once the canonical infinite-product empirical averages converge in
measure to `m`, the remaining reverse implication is the law-level weak-law/Feller owner step for
that common law. -/
private theorem hasDerivAtCharFunZero_of_tendstoInMeasureInfinitePiAverage
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {m : ℝ}
    (hAverage :
      TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
        (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ ↦ m)) :
    HasDerivAt (charFun μ) ((m : ℂ) * Complex.I) 0 := by
  -- Proof comment: this declaration is now just the isolated analytic bridge from canonical weak
  -- convergence back to differentiability of the common characteristic function.
  exact canonicalAverage_hasDerivAtCharFunZero_of_tendstoInMeasure hAverage

-- Proof sketch: for the common law `P.map (X 0)`, differentiate the `n`th power relation for the
-- characteristic function of normalized partial sums and combine it with the weak law of large
-- numbers for i.i.d. averages.
/-- Part (2) of Exercise 15.4.4: for a `0`-based Lean i.i.d. sequence `X 0, X 1, ...` representing the
textbook sequence `X₁, X₂, ...`, the common characteristic function has derivative `i m` at `0`
exactly when the empirical averages converge in probability to `m`. -/
-- TODO: restore the reverse implication by first finishing the transport lemma to the canonical
-- product space and then applying the law-level Feller owner theorem above.
theorem hasDerivAt_charFun_map_zero_iff_tendstoInMeasure_average
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX_iid : IsIID X P) (m : ℝ) :
    HasDerivAt (charFun (P.map (X 0))) ((m : ℂ) * Complex.I) 0 ↔
      TendstoInMeasure P
        (fun n ω ↦ (∑ i ∈ Finset.range n, X i ω) / n)
        atTop
        (fun _ ↦ m) := by
  constructor
  · intro hphi
    -- Proof comment: the forward implication is the already established law-level argument for
    -- i.i.d. empirical averages under the original probability space.
    exact hasDerivAt_charFun_map_zero_implies_tendstoInMeasure_average hX_iid hphi
  · intro hAverage
    -- Proof comment: transport convergence in measure to the canonical infinite-product model,
    -- then invoke the remaining owner theorem on that common-law realization.
    have hX0_ae : AEMeasurable (X 0) P := (hX_iid.identDistrib 0 0).aemeasurable_fst
    haveI : IsProbabilityMeasure (P.map (X 0)) := Measure.isProbabilityMeasure_map hX0_ae
    have hCanonical :
        TendstoInMeasure (Measure.infinitePi (fun _ : ℕ ↦ P.map (X 0)))
          (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
          atTop
          (fun _ ↦ m) :=
      (tendstoInMeasure_average_iff_tendstoInMeasureInfinitePiAverage hX_iid m).1 hAverage
    exact hasDerivAtCharFunZero_of_tendstoInMeasureInfinitePiAverage hCanonical

end IIDAverage

/-- Helper for Exercise 15.4.4: after applying `ENNReal.ofReal`, truncating `id` at level `n`
simply keeps the nonnegative window `(0, n]`. -/
private lemma ofReal_truncation_id_eq_indicator (n : ℕ) :
    (fun x : ℝ ↦ ENNReal.ofReal (ProbabilityTheory.truncation id n x)) =
      Set.indicator (Set.Ioc (0 : ℝ) (n : ℝ)) (fun x : ℝ ↦ ENNReal.ofReal x) := by
  -- Proof comment: for nonnegative inputs below the cutoff, truncation is the identity; outside
  -- that window, both sides vanish.
  funext x
  by_cases hx_pos : 0 < x
  · by_cases hx_le : x ≤ n
    · have hmem : x ∈ Set.Ioc (-(n : ℝ)) (n : ℝ) := by
        constructor
        · linarith
        · exact_mod_cast hx_le
      have hmem' : x ∈ Set.Ioc (0 : ℝ) (n : ℝ) := ⟨hx_pos, by exact_mod_cast hx_le⟩
      simp [ProbabilityTheory.truncation, hmem, hmem']
    · have hnotmem : x ∉ Set.Ioc (-(n : ℝ)) (n : ℝ) := by
        simp [hx_le]
      have hnotmem' : x ∉ Set.Ioc (0 : ℝ) (n : ℝ) := by
        simp [hx_le]
      simp [ProbabilityTheory.truncation, hnotmem, hnotmem']
  · have hx_nonpos : x ≤ 0 := le_of_not_gt hx_pos
    have hnotmem' : x ∉ Set.Ioc (0 : ℝ) (n : ℝ) := by
      simp [hx_pos]
    by_cases hmem : x ∈ Set.Ioc (-(n : ℝ)) (n : ℝ)
    · simp [ProbabilityTheory.truncation, hmem, hnotmem', hx_nonpos]
    · simp [ProbabilityTheory.truncation, hmem, hnotmem']

/-- Helper for Exercise 15.4.4: the `ENNReal.ofReal` truncation sequence is monotone in the cutoff
level. -/
private lemma monotone_ofReal_truncation_id :
    Monotone (fun n : ℕ ↦ fun x : ℝ ↦ ENNReal.ofReal (ProbabilityTheory.truncation id n x)) := by
  -- Proof comment: once the cutoff grows, the positive indicator window only enlarges.
  intro n k hnk x
  change
    ENNReal.ofReal (ProbabilityTheory.truncation id n x) ≤
      ENNReal.ofReal (ProbabilityTheory.truncation id k x)
  have hleft := congrArg (fun f : ℝ → ENNReal ↦ f x) (ofReal_truncation_id_eq_indicator n)
  have hright := congrArg (fun f : ℝ → ENNReal ↦ f x) (ofReal_truncation_id_eq_indicator k)
  have hleft' :
      ENNReal.ofReal (ProbabilityTheory.truncation id n x) =
        Set.indicator (Set.Ioc (0 : ℝ) (n : ℝ)) (fun x : ℝ ↦ ENNReal.ofReal x) x := by
    simpa using hleft
  have hright' :
      ENNReal.ofReal (ProbabilityTheory.truncation id k x) =
        Set.indicator (Set.Ioc (0 : ℝ) (k : ℝ)) (fun x : ℝ ↦ ENNReal.ofReal x) x := by
    simpa using hright
  rw [hleft', hright']
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) (n : ℝ)
  · have hx' : x ∈ Set.Ioc (0 : ℝ) (k : ℝ) := by
      refine ⟨hx.1, ?_⟩
      exact le_trans hx.2 (by exact_mod_cast hnk)
    simp [hx, hx']
  · by_cases hx' : x ∈ Set.Ioc (0 : ℝ) (k : ℝ)
    · simp [hx, hx']
    · simp [hx, hx']

/-- Helper for Exercise 15.4.4: for `x ≥ 0`, the nonnegative truncations
`ENNReal.ofReal (ProbabilityTheory.truncation id n x)` increase to `ENNReal.ofReal x`. -/
lemma iSup_ofReal_truncation_id_nat_eq {x : ℝ} (hx : 0 ≤ x) :
    (⨆ n : ℕ, ENNReal.ofReal (ProbabilityTheory.truncation id n x)) = ENNReal.ofReal x := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: every truncation is bounded above by the original nonnegative value.
    refine iSup_le fun n ↦ ?_
    apply ENNReal.ofReal_le_ofReal
    calc
      ProbabilityTheory.truncation id n x ≤ |ProbabilityTheory.truncation id n x| := le_abs_self _
      _ ≤ |x| := ProbabilityTheory.abs_truncation_le_abs_self _ _ _
      _ = x := abs_of_nonneg hx
  · -- Proof comment: once the cutoff exceeds `x`, the truncation agrees exactly with `x`.
    refine le_iSup_of_le (Nat.ceil x + 1) ?_
    have hx_lt : |x| < ((Nat.ceil x + 1 : ℕ) : ℝ) := by
      rw [abs_of_nonneg hx]
      exact lt_of_le_of_lt (Nat.le_ceil x) (by exact_mod_cast Nat.lt_succ_self (Nat.ceil x))
    rw [ProbabilityTheory.truncation_eq_self hx_lt]
    simp

/-- Helper for Exercise 15.4.4: if two real sequences converge in measure to constants and the
first is almost surely bounded above by the second at each index, then the limiting constants are
ordered the same way. -/
lemma le_of_tendstoInMeasure_const_of_ae_le
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y Z : ℕ → Ω → ℝ} {a b : ℝ}
    (hYZ : ∀ n, ∀ᵐ ω ∂P, Y n ω ≤ Z n ω)
    (hY : TendstoInMeasure P Y atTop (fun _ ↦ a))
    (hZ : TendstoInMeasure P Z atTop (fun _ ↦ b)) :
    a ≤ b := by
  by_contra hab
  let ε : ℝ := (a - b) / 3
  have hε : 0 < ε := by
    have hba : b < a := lt_of_not_ge hab
    dsimp [ε]
    linarith
  have hYε :
      Tendsto (fun n ↦ P {ω | ε ≤ dist (Y n ω) a}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.1 hY) ε hε
  have hZε :
      Tendsto (fun n ↦ P {ω | ε ≤ dist (Z n ω) b}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.1 hZ) ε hε
  have hYsmall : ∀ᶠ n in atTop, P {ω | ε ≤ dist (Y n ω) a} < (1 / 2 : ENNReal) := by
    exact hYε (Iio_mem_nhds (by norm_num : (0 : ENNReal) < 1 / 2))
  have hZsmall : ∀ᶠ n in atTop, P {ω | ε ≤ dist (Z n ω) b} < (1 / 2 : ENNReal) := by
    exact hZε (Iio_mem_nhds (by norm_num : (0 : ENNReal) < 1 / 2))
  let A : ℕ → Set Ω := fun n ↦ {ω | ε ≤ dist (Y n ω) a}
  let B : ℕ → Set Ω := fun n ↦ {ω | ε ≤ dist (Z n ω) b}
  let C : ℕ → Set Ω := fun n ↦ {ω | Z n ω < Y n ω}
  have hC_zero (n : ℕ) : P (C n) = 0 := by
    refine measure_mono_null_ae ?_ (by simp : P (∅ : Set Ω) = 0)
    filter_upwards [hYZ n] with ω hω
    intro hC
    exact (not_lt_of_ge hω) (by simpa [C] using hC)
  have hCover (n : ℕ) : Set.univ ⊆ (A n ∪ B n) ∪ C n := by
    intro ω _
    by_contra hω
    have hnotA : ω ∉ A n := by
      intro hA
      exact hω (Or.inl (Or.inl hA))
    have hnotB : ω ∉ B n := by
      intro hB
      exact hω (Or.inl (Or.inr hB))
    have hnotC : ω ∉ C n := by
      intro hC
      exact hω (Or.inr hC)
    have hYdist : dist (Y n ω) a < ε := by
      exact lt_of_not_ge (by simpa [A] using hnotA)
    have hZdist : dist (Z n ω) b < ε := by
      exact lt_of_not_ge (by simpa [B] using hnotB)
    have hYZω : Y n ω ≤ Z n ω := by
      exact le_of_not_gt (by simpa [C] using hnotC)
    have hYabs : |Y n ω - a| < ε := by
      simpa [Real.dist_eq] using hYdist
    have hZabs : |Z n ω - b| < ε := by
      simpa [Real.dist_eq] using hZdist
    have hgap : b + ε < a - ε := by
      dsimp [ε]
      linarith [lt_of_not_ge hab]
    have hYlower : a - ε < Y n ω := by
      linarith [abs_lt.1 hYabs |>.1]
    have hZupper : Z n ω < b + ε := by
      linarith [abs_lt.1 hZabs |>.2]
    have : Z n ω < Y n ω := by
      linarith
    exact (not_lt_of_ge hYZω) this
  have hUnion_ge (n : ℕ) : (1 : ENNReal) ≤ P (A n ∪ B n) := by
    have hBig :
        (1 : ENNReal) ≤ P ((A n ∪ B n) ∪ C n) := by
      simpa using (measure_mono (hCover n) : P Set.univ ≤ P ((A n ∪ B n) ∪ C n))
    have hUpper :
        P ((A n ∪ B n) ∪ C n) ≤ P (A n ∪ B n) := by
      calc
        P ((A n ∪ B n) ∪ C n) ≤ P (A n ∪ B n) + P (C n) := measure_union_le _ _
        _ = P (A n ∪ B n) := by simp [hC_zero n]
    exact hBig.trans hUpper
  have hUnion_lt : ∀ᶠ n in atTop, P (A n ∪ B n) < 1 := by
    filter_upwards [hYsmall, hZsmall] with n hA hB
    calc
      P (A n ∪ B n) ≤ P (A n) + P (B n) := measure_union_le _ _
      _ < (1 / 2 : ENNReal) + 1 / 2 := ENNReal.add_lt_add hA hB
      _ = 1 := by simpa using (ENNReal.add_halves (1 : ENNReal))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hUnion_lt
  exact not_lt_of_ge (hUnion_ge N) (hN N le_rfl)

/-- Helper for Exercise 15.4.4: if a nonnegative probability law has uniformly bounded truncation
integrals, then the identity is integrable. -/
-- TODO: split the monotone-convergence proof into a separate `x = 0` branch and a positive branch
-- so the truncation monotonicity proof no longer gets stuck on the indicator normal form.
lemma integrable_id_of_nonneg_of_boundedTruncationIntegrals
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x) (m : ℝ)
    (hbound : ∀ n : ℕ, ∫ x, ProbabilityTheory.truncation id n x ∂μ ≤ m) :
    Integrable id μ := by
  -- Proof comment: convert the truncation bounds into monotone `lintegral` bounds and then pass
  -- to the supremum, exactly as in the chapter-16 truncation-integrability criterion.
  have hm_nonneg : 0 ≤ m := by
    have hzero := hbound 0
    simpa [ProbabilityTheory.truncation_zero] using hzero
  let f : ℕ → ℝ → ENNReal := fun n x ↦ ENNReal.ofReal (ProbabilityTheory.truncation id n x)
  have hf_meas (n : ℕ) : AEMeasurable (f n) μ := by
    exact (aestronglyMeasurable_id.truncation.aemeasurable.ennreal_ofReal)
  have hf_mono : ∀ᵐ x ∂μ, Monotone (fun n ↦ f n x) := by
    filter_upwards [hnonneg] with x hx
    intro n k hnk
    exact monotone_ofReal_truncation_id hnk x
  have hlin_bound (n : ℕ) : ∫⁻ x, f n x ∂μ ≤ ENNReal.ofReal m := by
    have htrunc_nonneg : 0 ≤ᵐ[μ] fun x ↦ ProbabilityTheory.truncation id n x := by
      filter_upwards [hnonneg] with x hx
      exact ProbabilityTheory.truncation_nonneg (n : ℝ) hx
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (aestronglyMeasurable_id.integrable_truncation) htrunc_nonneg]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hlin_top :
      ∫⁻ x, ENNReal.ofReal x ∂μ ≤ ENNReal.ofReal m := by
    have hiSup_eq :
        (fun x ↦ ENNReal.ofReal x) =ᵐ[μ] fun x ↦ ⨆ n : ℕ, f n x := by
      filter_upwards [hnonneg] with x hx
      simpa [f] using (iSup_ofReal_truncation_id_nat_eq hx).symm
    calc
      ∫⁻ x, ENNReal.ofReal x ∂μ = ∫⁻ x, ⨆ n : ℕ, f n x ∂μ := by
        exact lintegral_congr_ae hiSup_eq
      _ = ⨆ n : ℕ, ∫⁻ x, f n x ∂μ := by
        rw [MeasureTheory.lintegral_iSup' hf_meas hf_mono]
      _ ≤ ENNReal.ofReal m := by
        exact iSup_le hlin_bound
  have hne_top : ∫⁻ x, ENNReal.ofReal (id x) ∂μ ≠ (⊤ : ENNReal) := by
    exact ne_of_lt (lt_of_le_of_lt hlin_top ENNReal.ofReal_lt_top)
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    aestronglyMeasurable_id hnonneg).1 hne_top

/-- Helper for Exercise 15.4.4: the textbook interval-integral limit is equivalent to the canonical
truncation-integral limit along `atTop`. -/
private lemma tendstoTruncationIntegralId_iff_tendstoIntervalIntegral
    {μ : Measure ℝ} {m : ℝ} :
    Tendsto (fun x ↦ ∫ y, ProbabilityTheory.truncation id x y ∂μ) atTop (𝓝 m) ↔
      Tendsto (fun x ↦ ∫ y in -x..x, y ∂μ) atTop (𝓝 m) := by
  have hEventually :
      (fun x ↦ ∫ y, ProbabilityTheory.truncation id x y ∂μ) =ᶠ[atTop]
        fun x ↦ ∫ y in -x..x, y ∂μ := by
    -- Proof comment: once the cutoff is nonnegative, the two normal forms coincide pointwise.
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with x hx
    exact integralTruncationId_eq_intervalIntegral (μ := μ) hx
  constructor
  · intro h
    exact Tendsto.congr' hEventually h
  · intro h
    exact Tendsto.congr' hEventually.symm h

-- Proof sketch: use the derivative-at-zero criterion for characteristic functions together with
-- the nonnegativity assumption, then identify the limiting truncated first moment with the full
-- expectation and conclude integrability of `id`.
/-- Part (3) of Exercise 15.4.4: if a real probability law is supported on `[0, ∞)` and its
characteristic function is differentiable at `0`, then the first moment is finite and the
derivative at `0` equals the expectation multiplied by `i`. Equivalently,
`μ[id] = -Complex.I * φ'(0) < ∞`. -/
-- TODO: keep the strong-law-on-truncations argument above, then finish with `MemLp id 1 μ`
-- and `MeasureTheory.iteratedDeriv_charFun_zero`.
theorem integrable_id_of_nonnegative_hasDerivAt_charFun_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {dphi : ℂ}
    (hphi : HasDerivAt (charFun μ) dphi 0)
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x) :
    Integrable id μ ∧ dphi = (μ[id] : ℂ) * Complex.I := by
  rcases hasDerivAt_charFun_zero_eq_real_mul_I hphi with ⟨m, hmphi⟩
  have hphi' : HasDerivAt (charFun μ) ((m : ℂ) * Complex.I) 0 := by
    simpa [hmphi] using hphi
  let Pinf : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ ↦ μ)
  have hcoordLaw (i : ℕ) : HasLaw (fun ω : ℕ → ℝ ↦ ω i) μ Pinf :=
    MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i)
  have hcoordNonneg (i : ℕ) : ∀ᵐ ω ∂Pinf, 0 ≤ ω i := by
    have hmapNonneg : ∀ᵐ x ∂(Pinf.map (fun ω : ℕ → ℝ ↦ ω i)), 0 ≤ x := by
      simpa [(hcoordLaw i).map_eq] using hnonneg
    exact (ae_map_iff (hcoordLaw i).aemeasurable measurableSet_Ici).1 hmapNonneg
  have hcoordAllNonneg : ∀ᵐ ω ∂Pinf, ∀ i : ℕ, 0 ≤ ω i := by
    rw [ae_all_iff]
    intro i
    exact hcoordNonneg i
  have hcoordMap :
      Pinf.map (fun ω : ℕ → ℝ ↦ ω 0) = μ := by
    simpa [Pinf] using (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0).map_eq
  have hphiCoord :
      HasDerivAt (charFun (Pinf.map (fun ω : ℕ → ℝ ↦ ω 0))) ((m : ℂ) * Complex.I) 0 := by
    simpa [hcoordMap] using hphi'
  have hAverage :
      TendstoInMeasure Pinf
        (fun n ω ↦ (∑ i ∈ Finset.range n, ω i) / n)
        atTop
        (fun _ ↦ m) := by
    -- Proof comment: apply the forward direction of part (ii) to the canonical coordinate process.
    simpa [Pinf] using
      hasDerivAt_charFun_map_zero_implies_tendstoInMeasure_average
        (P := Pinf)
        (X := fun i : ℕ ↦ fun ω : ℕ → ℝ ↦ ω i)
        (hX_iid := infinitePiCoordinateProcess_isIID (μ := μ))
        (m := m)
        hphiCoord
  have hbound :
      ∀ k : ℕ, ∫ x, ProbabilityTheory.truncation id k x ∂μ ≤ m := by
    intro k
    let truncAvg : ℕ → (ℕ → ℝ) → ℝ :=
      fun n ω ↦ (∑ i ∈ Finset.range n, ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω i) k ω) / n
    have htruncInt :
        Integrable (ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω 0) k) Pinf :=
      ((hcoordLaw 0).aemeasurable.aestronglyMeasurable.integrable_truncation)
    have htruncPairwise :
        Pairwise
          (fun i j ↦
            ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω i) k ⟂ᵢ[Pinf]
              ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω j) k) := by
      intro i j hij
      exact
        ((infinitePiCoordinateProcess_isIID (μ := μ)).iIndepFun.indepFun hij).comp
          (measurable_id.indicator measurableSet_Ioc)
          (measurable_id.indicator measurableSet_Ioc)
    have htruncIdent :
        ∀ i,
          IdentDistrib
            (ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω i) k)
            (ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω 0) k)
            Pinf Pinf := by
      intro i
      exact (hcoordLaw i).identDistrib (hcoordLaw 0) |>.truncation
    have htruncIntegralEq :
        ∫ ω, ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω 0) k ω ∂Pinf =
          ∫ x, ProbabilityTheory.truncation id k x ∂μ := by
      simpa [ProbabilityTheory.truncation, Function.comp_def, Pinf] using
        (hcoordLaw 0).integral_comp
          (f := ProbabilityTheory.truncation id k)
          (aestronglyMeasurable_id.truncation)
    have htruncAE :
        ∀ᵐ ω ∂Pinf,
          Tendsto (fun n : ℕ ↦ truncAvg n ω) atTop
            (𝓝 (∫ x, ProbabilityTheory.truncation id k x ∂μ)) := by
      -- Proof comment: the strong law applies to each bounded truncation level.
      simpa [truncAvg, htruncIntegralEq] using
        ProbabilityTheory.strong_law_ae_real
          (fun i ↦ ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω i) k)
          htruncInt htruncPairwise htruncIdent
    have htruncMeas (n : ℕ) : AEStronglyMeasurable (truncAvg n) Pinf := by
      have hsum :
          AEStronglyMeasurable
            (fun ω ↦ ∑ i ∈ Finset.range n, ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω i) k ω)
            Pinf :=
        Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
          ((hcoordLaw i).aemeasurable.aestronglyMeasurable.truncation)
      simpa [truncAvg, div_eq_mul_inv, mul_comm] using hsum.const_mul ((n : ℝ)⁻¹)
    have htruncMeasure :
        TendstoInMeasure Pinf truncAvg atTop
          (fun _ ↦ ∫ x, ProbabilityTheory.truncation id k x ∂μ) :=
      MeasureTheory.tendstoInMeasure_of_tendsto_ae htruncMeas htruncAE
    have hpointwise :
        ∀ n : ℕ, ∀ᵐ ω ∂Pinf, truncAvg n ω ≤ (∑ i ∈ Finset.range n, ω i) / n := by
      intro n
      filter_upwards [hcoordAllNonneg] with ω hω
      have hsumLe :
          ∑ i ∈ Finset.range n, ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω i) k ω ≤
            ∑ i ∈ Finset.range n, ω i := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hiNonneg : 0 ≤ ω i := hω i
        calc
          ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω i) k ω ≤
              |ProbabilityTheory.truncation (fun ω : ℕ → ℝ ↦ ω i) k ω| := le_abs_self _
          _ ≤ |ω i| := ProbabilityTheory.abs_truncation_le_abs_self _ _ _
          _ = ω i := abs_of_nonneg hiNonneg
      exact div_le_div_of_nonneg_right hsumLe (by positivity : 0 ≤ (n : ℝ))
    exact le_of_tendstoInMeasure_const_of_ae_le hpointwise htruncMeasure hAverage
  have hInt : Integrable id μ :=
    integrable_id_of_nonneg_of_boundedTruncationIntegrals hnonneg m hbound
  have hmem : MemLp id 1 μ := by
    simpa using (MeasureTheory.memLp_one_iff_integrable.2 hInt)
  have hderivIntegral :
      deriv (charFun μ) 0 = Complex.I * ((∫ x, x ∂μ : ℝ) : ℂ) := by
    -- Proof comment: once `id` is integrable, the first derivative formula at `0` identifies the
    -- derivative with the expectation multiplied by `I`.
    simpa using
      (MeasureTheory.iteratedDeriv_charFun_zero (μ := μ) (n := 1) (hint := by simpa using hmem))
  refine ⟨hInt, ?_⟩
  calc
    dphi = deriv (charFun μ) 0 := by simpa using hphi.deriv.symm
    _ = Complex.I * ((∫ x, x ∂μ : ℝ) : ℂ) := hderivIntegral
    _ = Complex.I * ∫ x, (x : ℂ) ∂μ := by rw [integral_complex_ofReal]
    _ = (μ[id] : ℂ) * Complex.I := by
      simp [mul_comm]

/-- Helper for Exercise 15.4.4: the positive branch of the explicit heavy-tail witness uses the
normalized masses `((2 * log 2)⁻¹) * (1 / 2)^(n + 1) / (n + 1)`. -/
private def heavyTailSideWeightReal (n : ℕ) : ℝ :=
  ((2 * Real.log 2)⁻¹) * ((1 / 2 : ℝ) ^ (n + 1) / (n + 1))

/-- Helper for Exercise 15.4.4: the heavy-tail side masses are nonnegative. -/
-- TODO: reopen the positivity proof with the logarithmic constant and denominator positivity made
-- explicit so `positivity` can discharge the whole product.
private lemma heavyTailSideWeightReal_nonneg (n : ℕ) :
    0 ≤ heavyTailSideWeightReal n := by
  -- Proof comment: each factor in the explicit weight is nonnegative, and `log 2` is positive.
  refine mul_nonneg ?_ ?_
  · exact inv_nonneg.2 (mul_nonneg (by norm_num) (le_of_lt (Real.log_pos (by norm_num))))
  · exact div_nonneg (by positivity) (by positivity)

/-- Helper for Exercise 15.4.4: one sign of the explicit heavy-tail witness carries total mass
`1 / 2`. -/
-- TODO: rescale `Real.hasSum_pow_div_log_of_abs_lt_one` cleanly and avoid the current `field_simp`
-- instability in the final normalization step.
private lemma heavyTailSideWeightReal_hasSum :
    HasSum heavyTailSideWeightReal (1 / 2 : ℝ) := by
  -- Proof comment: the side weights are a constant multiple of the standard logarithmic series
  -- for `x = 1 / 2`.
  have hseries :
      HasSum (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1) / (n + 1)) (Real.log 2) := by
    have hraw :=
      Real.hasSum_pow_div_log_of_abs_lt_one (x := (1 / 2 : ℝ)) (by norm_num)
    have hlog2 : -Real.log (1 - (1 / 2 : ℝ)) = Real.log 2 := by
      calc
        -Real.log (1 - (1 / 2 : ℝ)) = -Real.log (1 / 2 : ℝ) := by norm_num
        _ = Real.log ((1 / 2 : ℝ)⁻¹) := by
          simpa using (Real.log_inv (1 / 2 : ℝ)).symm
        _ = Real.log 2 := by norm_num
    rw [hlog2] at hraw
    exact hraw
  have hscaled := hseries.mul_left ((2 * Real.log 2)⁻¹)
  have hconst : ((2 * Real.log 2)⁻¹ : ℝ) * Real.log 2 = 1 / 2 := by
    have hlog : Real.log 2 ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by norm_num))
    field_simp [hlog]
  have hscaled' :
      HasSum
        (fun n : ℕ ↦ ((2 * Real.log 2)⁻¹ : ℝ) * ((1 / 2 : ℝ) ^ (n + 1) / (n + 1)))
        (((2 * Real.log 2)⁻¹ : ℝ) * Real.log 2) := hscaled
  have hfun :
      ∀ n : ℕ,
        ((2 * Real.log 2)⁻¹ : ℝ) * ((1 / 2 : ℝ) ^ (n + 1) / (n + 1)) =
          heavyTailSideWeightReal n := by
    intro n
    simp [heavyTailSideWeightReal, mul_assoc, mul_left_comm, mul_comm]
  have hsumHalf :
      HasSum heavyTailSideWeightReal (((2 * Real.log 2)⁻¹ : ℝ) * Real.log 2) :=
    hscaled'.congr_fun fun n ↦ (hfun n).symm
  convert hsumHalf using 1
  · have hlog : Real.log 2 ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by norm_num))
    field_simp [hlog]

/-- Helper for Exercise 15.4.4: the source PMF places the same heavy-tail mass on the positive
and negative power-of-two branches. -/
private def heavyTailSourceWeightReal : ℕ ⊕ ℕ → ℝ :=
  Sum.elim heavyTailSideWeightReal heavyTailSideWeightReal

/-- Helper for Exercise 15.4.4: the explicit source masses sum to `1`. -/
private lemma heavyTailSourceWeightReal_hasSum :
    HasSum heavyTailSourceWeightReal (1 : ℝ) := by
  have hleft : HasSum (fun n : ℕ ↦ heavyTailSourceWeightReal (Sum.inl n)) (1 / 2 : ℝ) := by
    simpa [heavyTailSourceWeightReal] using heavyTailSideWeightReal_hasSum
  have hright : HasSum (fun n : ℕ ↦ heavyTailSourceWeightReal (Sum.inr n)) (1 / 2 : ℝ) := by
    simpa [heavyTailSourceWeightReal] using heavyTailSideWeightReal_hasSum
  -- Proof comment: the two branches are disjoint copies of the same half-mass series.
  convert hleft.sum hright using 1 <;> norm_num

private instance : MeasurableSingletonClass (ℕ ⊕ ℕ) := by
  constructor
  intro x
  cases x with
  | inl n =>
      rw [measurableSet_sum_iff]
      simp
  | inr n =>
      rw [measurableSet_sum_iff]
      simp

/-- Helper for Exercise 15.4.4: the source PMF for the explicit heavy-tail witness. -/
private def heavyTailSourcePMF : PMF (ℕ ⊕ ℕ) :=
  ⟨fun x ↦ ENNReal.ofReal (heavyTailSourceWeightReal x), by
    apply ENNReal.hasSum_coe.mpr
    have hsumNN :
        HasSum (fun x : ℕ ⊕ ℕ ↦ (heavyTailSourceWeightReal x).toNNReal) ((1 : ℝ).toNNReal) :=
      heavyTailSourceWeightReal_hasSum.toNNReal
        (fun x ↦ by
          cases x with
          | inl n => simpa [heavyTailSourceWeightReal] using heavyTailSideWeightReal_nonneg n
          | inr n => simpa [heavyTailSourceWeightReal] using heavyTailSideWeightReal_nonneg n)
    simpa using hsumNN⟩

/-- Helper for Exercise 15.4.4: the explicit source PMF assigns the same mass to the positive and
negative branch at each dyadic index. -/
private lemma heavyTailSourcePMF_branch_eq (n : ℕ) :
    heavyTailSourcePMF (Sum.inl n) = heavyTailSourcePMF (Sum.inr n) := by
  rfl

/-- Helper for Exercise 15.4.4: converting a source PMF atom to `ℝ` recovers the explicit branch
weight. -/
private lemma heavyTailSourcePMF_toReal (s : ℕ ⊕ ℕ) :
    (heavyTailSourcePMF s).toReal = heavyTailSourceWeightReal s := by
  -- Proof comment: the PMF was defined by `ENNReal.ofReal` applied to the explicit nonnegative
  -- branch weights.
  cases s with
  | inl n =>
      change (ENNReal.ofReal (heavyTailSourceWeightReal (Sum.inl n))).toReal =
        heavyTailSourceWeightReal (Sum.inl n)
      simp [heavyTailSourceWeightReal, heavyTailSideWeightReal_nonneg]
  | inr n =>
      change (ENNReal.ofReal (heavyTailSourceWeightReal (Sum.inr n))).toReal =
        heavyTailSourceWeightReal (Sum.inr n)
      simp [heavyTailSourceWeightReal, heavyTailSideWeightReal_nonneg]

/-- Helper for Exercise 15.4.4: the source atoms are sent to the symmetric power-of-two support
`± 2^n`. -/
private def heavyTailPoint : ℕ ⊕ ℕ → ℝ
  | Sum.inl n => (2 : ℝ) ^ n
  | Sum.inr n => -((2 : ℝ) ^ n)

/-- Helper for Exercise 15.4.4: the explicit support map is injective, so integrability may be
transported cleanly across the pushforward. -/
private lemma heavyTailPoint_measurableEmbedding :
    MeasurableEmbedding heavyTailPoint := by
  have hmeas : Measurable heavyTailPoint := measurable_of_countable heavyTailPoint
  refine hmeas.measurableEmbedding ?_
  intro x y hxy
  cases x with
  | inl m =>
      cases y with
      | inl n =>
          -- Proof comment: on the positive branch, equality of powers of `2` forces equality of
          -- the exponents.
          apply congrArg Sum.inl
          have hnatReal : (2 : ℝ) ^ m = (2 : ℝ) ^ n := by
            simpa only [heavyTailPoint] using hxy
          have hnat : (2 : ℕ) ^ m = 2 ^ n := by exact_mod_cast hnatReal
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hnat
      | inr n =>
          -- Proof comment: a positive support atom cannot equal a negative support atom.
          exfalso
          have hm : 0 < (2 : ℝ) ^ m := by positivity
          have hn0 : 0 < (2 : ℝ) ^ n := by positivity
          have hn : -((2 : ℝ) ^ n) < 0 := by linarith
          simp [heavyTailPoint] at hxy
          linarith
  | inr m =>
      cases y with
      | inl n =>
          -- Proof comment: likewise, a negative atom cannot equal a positive one.
          exfalso
          have hm0 : 0 < (2 : ℝ) ^ m := by positivity
          have hm : -((2 : ℝ) ^ m) < 0 := by linarith
          have hn : 0 < (2 : ℝ) ^ n := by positivity
          simp [heavyTailPoint] at hxy
          linarith
      | inr n =>
          -- Proof comment: after cancelling the sign, equality again reduces to equality of
          -- powers.
          apply congrArg Sum.inr
          have hnatReal : (2 : ℝ) ^ m = (2 : ℝ) ^ n := by
            have hneg : -((2 : ℝ) ^ m) = -((2 : ℝ) ^ n) := by
              simpa only [heavyTailPoint] using hxy
            linarith
          have hnat : (2 : ℕ) ^ m = 2 ^ n := by exact_mod_cast hnatReal
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hnat

/-- Helper for Exercise 15.4.4: the dyadic support is odd under swapping the positive and negative
branches. -/
private lemma heavyTailPoint_swap (s : ℕ ⊕ ℕ) :
    heavyTailPoint (Sum.swap s) = -heavyTailPoint s := by
  -- Proof comment: swapping the branch flips the sign while keeping the dyadic magnitude.
  cases s with
  | inl n =>
      simp [heavyTailPoint]
  | inr n =>
      simp [heavyTailPoint]

/-- Helper for Exercise 15.4.4: swapping the two source branches leaves the explicit PMF
unchanged. -/
-- TODO: rewrite `PMF.map_apply` through the branch-swap involution using the already symmetric
-- source weights instead of the current brittle extensional simplifier route.
private lemma heavyTailSourcePMF_map_swap :
    heavyTailSourcePMF.map Sum.swap = heavyTailSourcePMF := by
  -- Proof comment: `Sum.swap` just exchanges the two branches, and the source weights were
  -- defined to be the same on both branches.
  ext s
  cases s with
  | inl n =>
      rw [PMF.map_apply, tsum_eq_single (Sum.inr n)]
      · have htrue : (Sum.inl n : ℕ ⊕ ℕ) = Sum.swap (Sum.inr n : ℕ ⊕ ℕ) := by rfl
        rw [htrue]
        simpa using (heavyTailSourcePMF_branch_eq n).symm
      · intro b hb
        cases b with
        | inl m =>
            simp [heavyTailSourcePMF, heavyTailSourceWeightReal]
        | inr m =>
            have hmn : m ≠ n := by
              intro hmn
              exact hb (by simpa [hmn])
            have hfalse : ¬ ((Sum.inl n : ℕ ⊕ ℕ) = Sum.swap (Sum.inr m : ℕ ⊕ ℕ)) := by
              simpa using fun h : n = m => hmn h.symm
            rw [if_neg hfalse]
  | inr n =>
      rw [PMF.map_apply, tsum_eq_single (Sum.inl n)]
      · have htrue : (Sum.inr n : ℕ ⊕ ℕ) = Sum.swap (Sum.inl n : ℕ ⊕ ℕ) := by rfl
        rw [htrue]
        simpa using heavyTailSourcePMF_branch_eq n
      · intro b hb
        cases b with
        | inl m =>
            have hmn : m ≠ n := by
              intro hmn
              exact hb (by simpa [hmn])
            have hfalse : ¬ ((Sum.inr n : ℕ ⊕ ℕ) = Sum.swap (Sum.inl m : ℕ ⊕ ℕ)) := by
              simpa using fun h : n = m => hmn h.symm
            rw [if_neg hfalse]
        | inr m =>
            simp [heavyTailSourcePMF, heavyTailSourceWeightReal]

/-- Helper for Exercise 15.4.4: the explicit heavy-tail witness law is symmetric under
`y ↦ -y`. -/
-- TODO: once the source PMF swap lemma is restored, transport it through `PMF.map_comp` to obtain
-- invariance of the pushed-forward measure under negation.
private lemma heavyTailWitness_map_neg :
    (((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ).map Neg.neg) =
      ((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ) := by
  -- Proof comment: negating the support values is the same as swapping the source branch before
  -- applying `heavyTailPoint`, so the source swap symmetry descends to the pushed-forward law.
  have hcomp : Neg.neg ∘ heavyTailPoint = heavyTailPoint ∘ Sum.swap := by
    funext s
    simpa [Function.comp_def] using (heavyTailPoint_swap s).symm
  calc
    (((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ).map Neg.neg) =
        ((heavyTailSourcePMF.map heavyTailPoint).map Neg.neg).toMeasure := by
          simpa using
            (PMF.toMeasure_map
              (p := heavyTailSourcePMF.map heavyTailPoint)
              (f := Neg.neg)
              measurable_neg)
    _ = (heavyTailSourcePMF.map (Neg.neg ∘ heavyTailPoint)).toMeasure := by
          rw [PMF.map_comp]
    _ = (heavyTailSourcePMF.map (heavyTailPoint ∘ Sum.swap)).toMeasure := by rw [hcomp]
    _ = ((heavyTailSourcePMF.map Sum.swap).map heavyTailPoint).toMeasure := by
          rw [← PMF.map_comp]
    _ = ((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ) := by
          rw [heavyTailSourcePMF_map_swap]

/-- Helper for Exercise 15.4.4: on symmetric intervals, the explicit heavy-tail witness has zero
truncated first moment. -/
-- TODO: after restoring the negation-invariance transport, prove the indicator cutoff is odd and
-- convert its integral back to the textbook set integral.
private lemma heavyTailWitness_textbookIccIntegral_eq_zero {x : ℝ} (hx : 0 ≤ x) :
    ∫ y in Set.Icc (-x) x, y
      ∂((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ) = 0 := by
  let μ : Measure ℝ := ((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ)
  have hpre :
      Neg.neg ⁻¹' Set.Icc (-x) x = Set.Icc (-x) x := by
    ext y
    constructor
    · intro hy
      constructor <;> linarith [hy.1, hy.2]
    · intro hy
      constructor <;> linarith [hy.1, hy.2]
  have hneg :
      ∫ y in Set.Icc (-x) x, y ∂μ = ∫ y in Set.Icc (-x) x, -y ∂μ := by
    -- Proof comment: map the symmetric interval through `y ↦ -y` and use invariance of `μ`.
    have hmap :=
      measurableEmbedding_neg.setIntegral_map
        (μ := μ)
        (g := fun y : ℝ ↦ y)
        (s := Set.Icc (-x) x)
    rw [heavyTailWitness_map_neg] at hmap
    simpa [μ, hpre, hx] using hmap
  have hself :
      ∫ y in Set.Icc (-x) x, y ∂μ = -∫ y in Set.Icc (-x) x, y ∂μ := by
    calc
      ∫ y in Set.Icc (-x) x, y ∂μ = ∫ y in Set.Icc (-x) x, -y ∂μ := hneg
      _ = -∫ y in Set.Icc (-x) x, y ∂μ := by rw [MeasureTheory.integral_neg]
  linarith

/-- Helper for Exercise 15.4.4: the dyadic powers dominate linear growth. -/
-- TODO: rewrite the induction step with `norm_num` on the casted natural arithmetic before the
-- final `linarith` comparison against `2^n + 2^n`.
private lemma natCast_succ_le_twoPow (n : ℕ) :
    (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero =>
      norm_num
  | succ n ihn =>
      -- Proof comment: double the previous exponential bound and absorb the extra `1`.
      have hstep : ((n + 1 : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ n + (2 : ℝ) ^ n := by
        have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
          exact_mod_cast Nat.one_le_two_pow
        calc
          ((n + 1 : ℕ) : ℝ) + 1 = ((n : ℝ) + 1) + 1 := by norm_num
          _ ≤ (2 : ℝ) ^ n + 1 := by gcongr
          _ ≤ (2 : ℝ) ^ n + (2 : ℝ) ^ n := by gcongr
      have hpow : (2 : ℝ) ^ n + (2 : ℝ) ^ n = (2 : ℝ) ^ (n + 1) := by
        calc
          (2 : ℝ) ^ n + (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ n := by ring
          _ = (2 : ℝ) ^ (n + 1) := by simp [pow_succ, mul_comm]
      calc
        ((n + 1 : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ n + (2 : ℝ) ^ n := hstep
        _ = (2 : ℝ) ^ (n + 1) := hpow

/-- Helper for Exercise 15.4.4: every `x ≥ 1` lies in a dyadic window `[2^N, 2^(N+1))`. -/
-- TODO: rebuild this via the least dyadic index above `x`, using `Nat.find_min'` only after the
-- predecessor inequality is phrased as a natural-number contradiction.
private lemma exists_dyadicWindow {x : ℝ} (hx : 1 ≤ x) :
    ∃ N : ℕ, (2 : ℝ) ^ N ≤ x ∧ x < (2 : ℝ) ^ (N + 1) := by
  -- Proof comment: choose the first dyadic power strictly above `x`; the previous power is then
  -- below or equal to `x` by minimality.
  have hexistsPow : ∃ n : ℕ, x < (2 : ℝ) ^ n := by
    have hEvent :
        ∀ᶠ n : ℕ in atTop, x < (2 : ℝ) ^ n :=
      (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) one_lt_two).eventually_gt_atTop x
    rcases Filter.eventually_atTop.1 hEvent with ⟨N, hN⟩
    exact ⟨N, hN N le_rfl⟩
  let n : ℕ := Nat.find hexistsPow
  have hn : x < (2 : ℝ) ^ n := Nat.find_spec hexistsPow
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    have : x < (1 : ℝ) := by
      simpa [n, hn_zero] using hn
    exact not_lt_of_ge hx this
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_ne_zero
  refine ⟨n - 1, ?_, ?_⟩
  · by_contra hN
    have hxlt : x < (2 : ℝ) ^ (n - 1) := lt_of_not_ge hN
    have hlt : n - 1 < n := Nat.sub_lt hn_pos (by norm_num)
    have hmin : n ≤ n - 1 := by
      simpa [n] using (Nat.find_min' hexistsPow hxlt)
    exact (not_le_of_gt hlt) hmin
  · simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)] using hn

/-- Helper for Exercise 15.4.4: the geometric tail beyond the dyadic level `N` has the expected
boundary value. -/
private lemma heavyTailGeometricTail_tsum (N : ℕ) :
    (∑' n : ℕ, if N + 1 ≤ n then (1 / 2 : ℝ) ^ (n + 1) else 0) = (1 / 2 : ℝ) ^ (N + 1) := by
  have hbase :
      (∑' n : ℕ, if N + 1 ≤ n then ((2 : ℝ)⁻¹) ^ n else 0) =
        2 * ((2 : ℝ)⁻¹) ^ (N + 1) := by
    simpa [one_div] using tsum_geometric_inv_two_ge (N + 1)
  calc
    (∑' n : ℕ, if N + 1 ≤ n then (1 / 2 : ℝ) ^ (n + 1) else 0)
        = ∑' n : ℕ, (1 / 2 : ℝ) * (if N + 1 ≤ n then ((2 : ℝ)⁻¹) ^ n else 0) := by
            refine tsum_congr ?_
            intro n
            by_cases hn : N + 1 ≤ n
            · simp [hn, one_div, pow_succ, mul_assoc, mul_left_comm, mul_comm]
            · simp [hn]
    _ = (1 / 2 : ℝ) * (∑' n : ℕ, if N + 1 ≤ n then ((2 : ℝ)⁻¹) ^ n else 0) := by
          rw [tsum_mul_left]
    _ = (1 / 2 : ℝ) * (2 * ((2 : ℝ)⁻¹) ^ (N + 1)) := by rw [hbase]
    _ = (1 / 2 : ℝ) ^ (N + 1) := by
          simp [one_div, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 15.4.4: the source tail set keeps exactly the two branches with index at
least `N + 1`. -/
private def heavyTailTailSet (N : ℕ) : Set (ℕ ⊕ ℕ) :=
  {s : ℕ ⊕ ℕ | match s with | Sum.inl n => N + 1 ≤ n | Sum.inr n => N + 1 ≤ n}

/-- Helper for Exercise 15.4.4: the tail-event indicator on `ℕ ⊕ ℕ` splits into the two branchwise
indicator series used by `HasSum.sum`. -/
private lemma heavyTailTailSetIndicator_eq_sumElim (N : ℕ) :
    Set.indicator
      (heavyTailTailSet N)
      (fun s ↦ (heavyTailSourcePMF s).toReal) =
      Sum.elim
        (fun n ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inl n)).toReal else 0)
        (fun n ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inr n)).toReal else 0) := by
  -- Proof comment: evaluate the indicator separately on the positive and negative source branches.
  funext s
  cases s with
  | inl n =>
      by_cases hn : N + 1 ≤ n
      · have hmem : Sum.inl n ∈ heavyTailTailSet N := by
          simpa [heavyTailTailSet] using hn
        have hlt : N < n := lt_of_lt_of_le (Nat.lt_succ_self N) hn
        simp [Set.indicator_of_mem, hmem, hn, hlt]
      · have hnotmem : Sum.inl n ∉ heavyTailTailSet N := by
          simpa [heavyTailTailSet] using hn
        have hnotlt : ¬ N < n := fun hlt ↦ hn (Nat.succ_le_of_lt hlt)
        simp [Set.indicator_of_notMem, hnotmem, hn, hnotlt]
  | inr n =>
      by_cases hn : N + 1 ≤ n
      · have hmem : Sum.inr n ∈ heavyTailTailSet N := by
          simpa [heavyTailTailSet] using hn
        have hlt : N < n := lt_of_lt_of_le (Nat.lt_succ_self N) hn
        simp [Set.indicator_of_mem, hmem, hn, hlt]
      · have hnotmem : Sum.inr n ∉ heavyTailTailSet N := by
          simpa [heavyTailTailSet] using hn
        have hnotlt : ¬ N < n := fun hlt ↦ hn (Nat.succ_le_of_lt hlt)
        simp [Set.indicator_of_notMem, hnotmem, hn, hnotlt]

/-- Helper for Exercise 15.4.4: doubling one branch weight removes the factor `2` from the
logarithmic normalization. -/
private lemma two_mul_heavyTailSideWeightReal (n : ℕ) :
    2 * heavyTailSideWeightReal n =
      (Real.log 2)⁻¹ * ((1 / 2 : ℝ) ^ (n + 1) / (n + 1)) := by
  -- Proof comment: this is the explicit algebraic simplification of the side-mass definition.
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold heavyTailSideWeightReal
  field_simp [hlog]

/-- Helper for Exercise 15.4.4: on the positive branch, the weighted absolute atom size is a
constant multiple of the harmonic term `1 / (n + 1)`. -/
private lemma heavyTailSource_leftBranch_term_eq (n : ℕ) :
    (heavyTailSourcePMF (Sum.inl n)).toReal * ‖heavyTailPoint (Sum.inl n)‖ =
      ((4 * Real.log 2)⁻¹) * (1 / (n + 1 : ℝ)) := by
  -- Proof comment: the dyadic size `2^n` cancels all but one factor of `1 / 2` in the branch
  -- mass, leaving a harmonic denominator.
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hpow :
      ((1 / 2 : ℝ) ^ (n + 1)) * (2 : ℝ) ^ n = (1 / 2 : ℝ) := by
    calc
      ((1 / 2 : ℝ) ^ (n + 1)) * (2 : ℝ) ^ n
          = (1 / 2 : ℝ) * (((1 / 2 : ℝ) ^ n) * (2 : ℝ) ^ n) := by
              rw [pow_succ]
              ring
      _ = (1 / 2 : ℝ) * (((1 / 2 : ℝ) * 2) ^ n) := by rw [← mul_pow]
      _ = (1 / 2 : ℝ) := by simp
  calc
    (heavyTailSourcePMF (Sum.inl n)).toReal * ‖heavyTailPoint (Sum.inl n)‖
        = heavyTailSideWeightReal n * (2 : ℝ) ^ n := by
            simp [heavyTailSourcePMF_toReal, heavyTailPoint, heavyTailSourceWeightReal,
              heavyTailSideWeightReal]
    _ = ((2 * Real.log 2)⁻¹) * ((((1 / 2 : ℝ) ^ (n + 1)) * (2 : ℝ) ^ n) / (n + 1)) := by
          rw [heavyTailSideWeightReal]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
    _ = ((2 * Real.log 2)⁻¹) * ((1 / 2 : ℝ) / (n + 1)) := by rw [hpow]
    _ = ((4 * Real.log 2)⁻¹) * (1 / (n + 1 : ℝ)) := by
          field_simp [hlog]
          ring_nf

/-- Helper for Exercise 15.4.4: the one-sided heavy-tail series remains summable after cutting off
the first `N + 1` terms. -/
private lemma heavyTailSideWeightRealTailSummable (N : ℕ) :
    Summable (fun n : ℕ ↦ if N + 1 ≤ n then heavyTailSideWeightReal n else 0) := by
  -- Proof comment: the tail indicator is pointwise dominated by the full side-mass series.
  refine Summable.of_nonneg_of_le ?_ ?_ heavyTailSideWeightReal_hasSum.summable
  · intro n
    by_cases hn : N + 1 ≤ n
    · simpa [hn] using heavyTailSideWeightReal_nonneg n
    · simp [hn]
  · intro n
    by_cases hn : N + 1 ≤ n
    · simp [hn]
    · simp [hn, heavyTailSideWeightReal_nonneg]

/-- Helper for Exercise 15.4.4: adding the two identical tail branches yields the displayed
two-sided tail series. -/
private lemma heavyTailTailDouble_tsum (N : ℕ) :
    ((∑' n : ℕ, if N + 1 ≤ n then heavyTailSideWeightReal n else 0) +
      ∑' n : ℕ, if N + 1 ≤ n then heavyTailSideWeightReal n else 0) =
      ∑' n : ℕ, if N + 1 ≤ n then 2 * heavyTailSideWeightReal n else 0 := by
  let f : ℕ → ℝ := fun n ↦ if N + 1 ≤ n then heavyTailSideWeightReal n else 0
  have hf : Summable f := heavyTailSideWeightRealTailSummable N
  calc
    (∑' n : ℕ, f n) + ∑' n : ℕ, f n = ∑' n : ℕ, (f n + f n) := by
      symm
      exact (hf.hasSum.add hf.hasSum).tsum_eq
    _ = ∑' n : ℕ, if N + 1 ≤ n then 2 * heavyTailSideWeightReal n else 0 := by
      refine tsum_congr ?_
      intro n
      by_cases hn : N + 1 ≤ n
      · have hlt : N < n := lt_of_lt_of_le (Nat.lt_succ_self N) hn
        simp [f, hn, hlt, two_mul]
      · have hnotlt : ¬ N < n := fun hlt ↦ hn (Nat.succ_le_of_lt hlt)
        simp [f, hn, hnotlt]

/-- Helper for Exercise 15.4.4: the source-tail event with branch index at least `N + 1` has the
displayed total mass. -/
private lemma heavyTailSource_tailIndexMass (N : ℕ) :
    (((heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)) (heavyTailTailSet N)).toReal) =
      ∑' n : ℕ, if N + 1 ≤ n then 2 * heavyTailSideWeightReal n else 0 := by
  let tailSet : Set (ℕ ⊕ ℕ) := heavyTailTailSet N
  change (((heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)) tailSet).toReal) =
    ∑' n : ℕ, if N + 1 ≤ n then 2 * heavyTailSideWeightReal n else 0
  have hfinite :
      ∀ s : ℕ ⊕ ℕ, tailSet.indicator (fun s ↦ heavyTailSourcePMF s) s ≠ ⊤ := by
    intro s
    by_cases hs : s ∈ tailSet
    · simpa [Set.indicator_of_mem, hs] using heavyTailSourcePMF.apply_ne_top s
    · simp [Set.indicator_of_notMem, hs]
  have htoRealIndicator :
      (fun s : ℕ ⊕ ℕ ↦ (tailSet.indicator (fun s ↦ heavyTailSourcePMF s) s).toReal) =
        Set.indicator tailSet (fun s ↦ (heavyTailSourcePMF s).toReal) := by
    -- Proof comment: after taking `toReal`, the ENNReal-valued tail indicator becomes the
    -- real-valued indicator of the source atom masses.
    funext s
    by_cases hs : s ∈ tailSet <;> simp [Set.indicator, hs]
  have hsplit :
      (fun s : ℕ ⊕ ℕ ↦ (tailSet.indicator (fun s ↦ heavyTailSourcePMF s) s).toReal) =
        Sum.elim
          (fun n ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inl n)).toReal else 0)
          (fun n ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inr n)).toReal else 0) := by
    rw [htoRealIndicator]
    simpa [tailSet] using (heavyTailTailSetIndicator_eq_sumElim (N := N))
  have hleft :
      HasSum
        (fun n : ℕ ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inl n)).toReal else 0)
        (∑' n : ℕ, if N + 1 ≤ n then heavyTailSideWeightReal n else 0) := by
    -- Proof comment: the positive branch is exactly the truncated one-sided heavy-tail series.
    simpa [heavyTailSourcePMF_toReal, heavyTailSourceWeightReal] using
      (heavyTailSideWeightRealTailSummable N).hasSum
  have hright :
      HasSum
        (fun n : ℕ ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inr n)).toReal else 0)
        (∑' n : ℕ, if N + 1 ≤ n then heavyTailSideWeightReal n else 0) := by
    -- Proof comment: the negative branch carries the same masses.
    simpa [heavyTailSourcePMF_toReal, heavyTailSourceWeightReal] using
      (heavyTailSideWeightRealTailSummable N).hasSum
  have hleftTsum :
      (∑' n : ℕ, if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inl n)).toReal else 0) =
        ∑' n : ℕ, if N + 1 ≤ n then heavyTailSideWeightReal n else 0 :=
    hleft.tsum_eq
  have hrightTsum :
      (∑' n : ℕ, if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inr n)).toReal else 0) =
        ∑' n : ℕ, if N + 1 ≤ n then heavyTailSideWeightReal n else 0 :=
    hright.tsum_eq
  have hsumTsum :
      (∑' s : ℕ ⊕ ℕ,
        (Sum.elim
          (fun n ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inl n)).toReal else 0)
          (fun n ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inr n)).toReal else 0)) s) =
        ((∑' n : ℕ, if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inl n)).toReal else 0) +
          ∑' n : ℕ, if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inr n)).toReal else 0) := by
    exact
      Summable.tsum_sum
        (f :=
          Sum.elim
            (fun n ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inl n)).toReal else 0)
            (fun n ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inr n)).toReal else 0))
        hleft.summable
        hright.summable
  calc
    (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)).real tailSet
        = ((∑' s, tailSet.indicator (fun s ↦ heavyTailSourcePMF s) s)).toReal := by
            rw [Measure.real, PMF.toMeasure_apply_eq_tsum]
    _ = ∑' s : ℕ ⊕ ℕ, (tailSet.indicator (fun s ↦ heavyTailSourcePMF s) s).toReal := by
          rw [ENNReal.tsum_toReal_eq hfinite]
    _ = ∑' s : ℕ ⊕ ℕ,
          (Sum.elim
            (fun n ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inl n)).toReal else 0)
            (fun n ↦ if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inr n)).toReal else 0)) s := by
          rw [hsplit]
    _ = ((∑' n : ℕ, if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inl n)).toReal else 0) +
          ∑' n : ℕ, if N + 1 ≤ n then (heavyTailSourcePMF (Sum.inr n)).toReal else 0) := by
            exact hsumTsum
    _ = ((∑' n : ℕ, if N + 1 ≤ n then heavyTailSideWeightReal n else 0) +
          ∑' n : ℕ, if N + 1 ≤ n then heavyTailSideWeightReal n else 0) := by
            rw [hleftTsum, hrightTsum]
    _ = ∑' n : ℕ, if N + 1 ≤ n then 2 * heavyTailSideWeightReal n else 0 := by
          exact heavyTailTailDouble_tsum N

/-- Helper for Exercise 15.4.4: the one-sided heavy-tail series remains summable after cutting
off the first `N + 1` terms. -/
private lemma heavyTailSideWeightReal_tailSummable (N : ℕ) :
    Summable (fun n : ℕ ↦ if N + 1 ≤ n then heavyTailSideWeightReal n else 0) := by
  simpa using heavyTailSideWeightRealTailSummable N

/-- Helper for Exercise 15.4.4: on a dyadic window, the heavy-tail event on `ℝ` pulls back to the
source branch tail `n ≥ N + 1`. -/
private lemma heavyTailTailSet_preimage_subset {x : ℝ} {N : ℕ}
    (hxLower : (2 : ℝ) ^ N ≤ x) (_hxUpper : x < (2 : ℝ) ^ (N + 1)) :
    heavyTailPoint ⁻¹' {y : ℝ | x < |y|} ⊆
      heavyTailTailSet N := by
  intro s hs
  cases s with
  | inl n =>
      -- Proof comment: if `n ≤ N`, then the `n`th dyadic atom is at most the lower endpoint `x`.
      have hs' : x < (2 : ℝ) ^ n := by simpa [heavyTailPoint] using hs
      change N + 1 ≤ n
      by_contra hn
      have hn' : n ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hn)
      have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ N := by
        exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hn'
      have : x < (2 : ℝ) ^ N := lt_of_lt_of_le hs' hpow
      exact not_lt_of_ge hxLower this
  | inr n =>
      -- Proof comment: the negative branch has the same absolute dyadic magnitudes.
      have hs' : x < (2 : ℝ) ^ n := by simpa [heavyTailPoint] using hs
      change N + 1 ≤ n
      by_contra hn
      have hn' : n ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hn)
      have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ N := by
        exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hn'
      have : x < (2 : ℝ) ^ N := lt_of_lt_of_le hs' hpow
      exact not_lt_of_ge hxLower this

/-- Helper for Exercise 15.4.4: on each dyadic window, the scaled tail of the explicit witness is
bounded by the reciprocal index factor from the heavy-tail weights. -/
-- TODO: rework the dyadic window proof on the discrete source so the geometric majorant and the
-- reciprocal denominator comparison are handled in separate lemmas.
private lemma heavyTailWitness_scaledTail_le_on_dyadicWindow {x : ℝ} {N : ℕ}
    (hxLower : (2 : ℝ) ^ N ≤ x) (hxUpper : x < (2 : ℝ) ^ (N + 1)) :
    x * (((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ).real
      {y : ℝ | x < |y|}) ≤ (Real.log 2)⁻¹ / (N + 2 : ℝ) := by
  let tailSet : Set (ℕ ⊕ ℕ) := heavyTailTailSet N
  have hx_nonneg : 0 ≤ x := le_trans (by positivity : 0 ≤ (2 : ℝ) ^ N) hxLower
  have htail_eq :
      (((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ).real {y : ℝ | x < |y|}) =
        (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)).real
          (heavyTailPoint ⁻¹' {y : ℝ | x < |y|}) := by
    -- Proof comment: rewrite the pushed-forward tail event on `ℝ` back to the discrete source.
    rw [show ((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ) =
        Measure.map heavyTailPoint (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)) by
          simpa using
            (PMF.toMeasure_map (p := heavyTailSourcePMF)
              (hf := measurable_of_countable heavyTailPoint)).symm]
    rw [map_measureReal_apply (μ := (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)))
      (hf := measurable_of_countable heavyTailPoint) (hs := measurableSet_lt measurable_const measurable_abs)]
  have hsubset :
      heavyTailPoint ⁻¹' {y : ℝ | x < |y|} ⊆ tailSet :=
    heavyTailTailSet_preimage_subset (x := x) (N := N) hxLower hxUpper
  have hmass_le :
      (((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ).real {y : ℝ | x < |y|}) ≤
        (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)).real tailSet := by
    rw [htail_eq]
    exact MeasureTheory.measureReal_mono hsubset
  have htail_mass :
      (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)).real tailSet =
        ∑' n : ℕ, if N + 1 ≤ n then 2 * heavyTailSideWeightReal n else 0 :=
    by
      simpa [Measure.real] using heavyTailSource_tailIndexMass N
  have htail_summable :
      Summable (fun n : ℕ ↦ if N + 1 ≤ n then 2 * heavyTailSideWeightReal n else 0) := by
    simpa using (heavyTailSideWeightReal_tailSummable N).mul_left (2 : ℝ)
  have hgeom :
      Summable (fun n : ℕ ↦ if N + 1 ≤ n then (1 / 2 : ℝ) ^ (n + 1) else 0) := by
    have hbase : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) := by
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
        (_root_.summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left
          (1 / 2 : ℝ)
    have hind :
        Summable ({n : ℕ | N + 1 ≤ n}.indicator fun n ↦ (1 / 2 : ℝ) ^ (n + 1)) :=
      Summable.indicator hbase {n : ℕ | N + 1 ≤ n}
    have hindEq :
        ({n : ℕ | N + 1 ≤ n}.indicator fun n ↦ (1 / 2 : ℝ) ^ (n + 1)) =
          (fun n : ℕ ↦ if N + 1 ≤ n then (1 / 2 : ℝ) ^ (n + 1) else 0) := by
      funext n
      by_cases hn : N + 1 ≤ n
      · have hmem : n ∈ {n : ℕ | N + 1 ≤ n} := by simpa [Set.mem_setOf_eq] using hn
        rw [Set.indicator_of_mem hmem]
        simp [hn]
      · have hnot : n ∉ {n : ℕ | N + 1 ≤ n} := by simpa [Set.mem_setOf_eq] using hn
        rw [Set.indicator_of_notMem hnot]
        simp [hn]
    rw [hindEq] at hind
    exact hind
  have hcompareEq :
      (fun n : ℕ ↦
        ((Real.log 2)⁻¹ / (N + 2 : ℝ)) *
          (if N + 1 ≤ n then ((2 : ℝ) ^ (N + 1)) * ((1 / 2 : ℝ) ^ (n + 1)) else 0)) =
        fun n : ℕ ↦
          ((((Real.log 2)⁻¹ / (N + 2 : ℝ)) * (2 : ℝ) ^ (N + 1)) *
            (if N + 1 ≤ n then (1 / 2 : ℝ) ^ (n + 1) else 0)) := by
    funext n
    by_cases hn : N + 1 ≤ n
    · simp [hn, mul_assoc, mul_left_comm, mul_comm]
    · simp [hn]
  have hcompareSummable :
      Summable (fun n : ℕ ↦
        ((Real.log 2)⁻¹ / (N + 2 : ℝ)) *
          (if N + 1 ≤ n then ((2 : ℝ) ^ (N + 1)) * ((1 / 2 : ℝ) ^ (n + 1)) else 0)) := by
    rw [hcompareEq]
    simpa using hgeom.mul_left ((((Real.log 2)⁻¹ / (N + 2 : ℝ)) * (2 : ℝ) ^ (N + 1))
      : ℝ)
  have hterm_le (n : ℕ) :
      x * (if N + 1 ≤ n then 2 * heavyTailSideWeightReal n else 0) ≤
        ((Real.log 2)⁻¹ / (N + 2 : ℝ)) *
          (if N + 1 ≤ n then ((2 : ℝ) ^ (N + 1)) * ((1 / 2 : ℝ) ^ (n + 1)) else 0) := by
    by_cases hn : N + 1 ≤ n
    · have hfrac : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 / (N + 2 : ℝ) := by
        have hcast : (N + 2 : ℝ) ≤ n + 1 := by
          exact_mod_cast Nat.succ_le_succ hn
        exact one_div_le_one_div_of_le (show 0 < (N + 2 : ℝ) by positivity) hcast
      have hterm_nonneg :
          0 ≤ (Real.log 2)⁻¹ * ((1 / 2 : ℝ) ^ (n + 1) / (n + 1)) := by
        positivity
      have hdiv :
          ((1 / 2 : ℝ) ^ (n + 1) / (n + 1)) ≤ ((1 / 2 : ℝ) ^ (n + 1) / (N + 2 : ℝ)) := by
        have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hfrac hpow_nonneg
      have hscaled :
          (Real.log 2)⁻¹ * ((1 / 2 : ℝ) ^ (n + 1) / (n + 1)) ≤
            (Real.log 2)⁻¹ * ((1 / 2 : ℝ) ^ (n + 1) / (N + 2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ (Real.log 2)⁻¹)
      rw [if_pos hn, if_pos hn, two_mul_heavyTailSideWeightReal]
      calc
        x * ((Real.log 2)⁻¹ * ((1 / 2 : ℝ) ^ (n + 1) / (n + 1)))
            ≤ (2 : ℝ) ^ (N + 1) * ((Real.log 2)⁻¹ * ((1 / 2 : ℝ) ^ (n + 1) / (n + 1))) := by
                exact mul_le_mul_of_nonneg_right (le_of_lt hxUpper) hterm_nonneg
        _ ≤ (2 : ℝ) ^ (N + 1) * ((Real.log 2)⁻¹ * ((1 / 2 : ℝ) ^ (n + 1) / (N + 2 : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hscaled (by positivity : 0 ≤ (2 : ℝ) ^ (N + 1))
        _ = ((Real.log 2)⁻¹ / (N + 2 : ℝ)) *
              (((2 : ℝ) ^ (N + 1)) * ((1 / 2 : ℝ) ^ (n + 1))) := by
                ring
    · simp [hn, hx_nonneg]
  have hpow_cancel :
      (2 : ℝ) ^ (N + 1) * (1 / 2 : ℝ) ^ (N + 1) = 1 := by
    calc
      (2 : ℝ) ^ (N + 1) * (1 / 2 : ℝ) ^ (N + 1) = ((2 : ℝ) * (1 / 2 : ℝ)) ^ (N + 1) := by
        rw [← mul_pow]
      _ = 1 := by simp
  calc
    x * (((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ).real {y : ℝ | x < |y|})
        ≤ x * (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)).real tailSet := by
            gcongr
    _ = x * ∑' n : ℕ, if N + 1 ≤ n then 2 * heavyTailSideWeightReal n else 0 := by
          rw [htail_mass]
    _ = ∑' n : ℕ, x * (if N + 1 ≤ n then 2 * heavyTailSideWeightReal n else 0) := by
          symm
          exact Summable.tsum_mul_left x htail_summable
    _ ≤ ∑' n : ℕ,
          ((Real.log 2)⁻¹ / (N + 2 : ℝ)) *
            (if N + 1 ≤ n then ((2 : ℝ) ^ (N + 1)) * ((1 / 2 : ℝ) ^ (n + 1)) else 0) := by
              exact Summable.tsum_le_tsum hterm_le (htail_summable.mul_left x) hcompareSummable
    _ = (((Real.log 2)⁻¹ / (N + 2 : ℝ)) * (2 : ℝ) ^ (N + 1)) *
          (∑' n : ℕ, if N + 1 ≤ n then (1 / 2 : ℝ) ^ (n + 1) else 0) := by
            rw [hcompareEq, hgeom.tsum_mul_left]
    _ = (((Real.log 2)⁻¹ / (N + 2 : ℝ)) * (2 : ℝ) ^ (N + 1)) *
          (1 / 2 : ℝ) ^ (N + 1) := by
            rw [heavyTailGeometricTail_tsum]
    _ = (Real.log 2)⁻¹ / (N + 2 : ℝ) := by
          calc
            (((Real.log 2)⁻¹ / (N + 2 : ℝ)) * (2 : ℝ) ^ (N + 1)) *
                (1 / 2 : ℝ) ^ (N + 1)
                = ((Real.log 2)⁻¹ / (N + 2 : ℝ)) *
                    ((2 : ℝ) ^ (N + 1) * (1 / 2 : ℝ) ^ (N + 1)) := by
                      ring
            _ = ((Real.log 2)⁻¹ / (N + 2 : ℝ)) * 1 := by rw [hpow_cancel]
            _ = (Real.log 2)⁻¹ / (N + 2 : ℝ) := by ring

/-- Helper for Exercise 15.4.4: the scaled tail term for the explicit heavy-tail witness tends to
`0`. -/
-- TODO: combine the dyadic window bound with an eventual choice of `M` large enough that
-- `(Real.log 2)⁻¹ / (M + 2) < ε`.
private lemma heavyTailWitness_scaledTail_tendstoZero :
    Tendsto
      (fun x ↦
        x * (((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ).real
          {y : ℝ | x < |y|}))
      atTop
      (𝓝 0) := by
  let F : ℝ → ℝ :=
    fun x ↦
      x * (((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ).real
        {y : ℝ | x < |y|})
  change Tendsto F atTop (𝓝 0)
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  let c : ℝ := (Real.log 2)⁻¹
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := by
    simpa [c] using inv_pos.mpr hlog2_pos
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (show 0 < ε / c by positivity)
  have hMε : c / (M + 2 : ℝ) < ε := by
    have hInv :
        1 / (M + 2 : ℝ) ≤ 1 / (M + 1 : ℝ) := by
      exact one_div_le_one_div_of_le
        (show 0 < (M + 1 : ℝ) by positivity)
        (show (M + 1 : ℝ) ≤ M + 2 by norm_num)
    have hScaled :
        c * (1 / (M + 1 : ℝ)) < ε := by
      have hmul := mul_lt_mul_of_pos_left hM hc_pos
      have hc_ne : c ≠ 0 := ne_of_gt hc_pos
      calc
        c * (1 / (M + 1 : ℝ)) < c * (ε / c) := hmul
        _ = ε := by field_simp [hc_ne]
    calc
      c / (M + 2 : ℝ) = c * (1 / (M + 2 : ℝ)) := by ring_nf
      _ ≤ c * (1 / (M + 1 : ℝ)) := by gcongr
      _ < ε := hScaled
  filter_upwards [Ici_mem_atTop ((2 : ℝ) ^ (M + 1))] with x hx
  have hxOne : 1 ≤ x := by
    have hpow_one (n : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
      induction n with
      | zero =>
          norm_num
      | succ n ihn =>
          calc
            (1 : ℝ) ≤ (2 : ℝ) ^ n := ihn
            _ ≤ (2 : ℝ) ^ n * 2 := by
                  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
                  nlinarith
            _ = (2 : ℝ) ^ (n + 1) := by simp [pow_succ, mul_comm]
    exact le_trans (hpow_one (M + 1)) hx
  rcases exists_dyadicWindow hxOne with ⟨N, hLower, hUpper⟩
  have hMN : M ≤ N := by
    by_contra hMN
    have hNM : N < M := Nat.lt_of_not_ge hMN
    have hpow_le : (2 : ℝ) ^ (N + 1) ≤ (2 : ℝ) ^ M := by
      exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (Nat.succ_le_of_lt hNM)
    have hpow_lt : (2 : ℝ) ^ M < (2 : ℝ) ^ (M + 1) := by
      have hpow_pos : 0 < (2 : ℝ) ^ M := by positivity
      calc
        (2 : ℝ) ^ M = 1 * (2 : ℝ) ^ M := by ring
        _ < 2 * (2 : ℝ) ^ M := by nlinarith
        _ = (2 : ℝ) ^ (M + 1) := by simp [pow_succ, mul_comm]
    have : x < (2 : ℝ) ^ (M + 1) := lt_of_lt_of_le hUpper (le_trans hpow_le (le_of_lt hpow_lt))
    exact (not_lt_of_ge hx) this
  have hfrac :
      c / (N + 2 : ℝ) ≤ c / (M + 2 : ℝ) := by
    have hInv :
        1 / (N + 2 : ℝ) ≤ 1 / (M + 2 : ℝ) := by
      have hcast : (M + 2 : ℝ) ≤ N + 2 := by
        exact_mod_cast Nat.add_le_add_right hMN 2
      exact one_div_le_one_div_of_le (show 0 < (M + 2 : ℝ) by positivity) hcast
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hInv hc_pos.le
  have hnonneg : 0 ≤ F x := by
    dsimp [F]
    positivity
  have hlt : F x < ε := by
    calc
      F x ≤ c / (N + 2 : ℝ) := by
        simpa [F, c] using heavyTailWitness_scaledTail_le_on_dyadicWindow hLower hUpper
      _ ≤ c / (M + 2 : ℝ) := hfrac
      _ < ε := hMε
  calc
    dist (F x) 0 = |F x| := by rw [Real.dist_eq, sub_zero]
    _ = F x := by rw [abs_of_nonneg hnonneg]
    _ < ε := hlt

/-- Helper for Exercise 15.4.4: the explicit symmetric power-of-two witness has infinite first
absolute moment. -/
-- TODO: push integrability back along the measurable embedding and compare the left branch to the
-- harmonic series through the explicit atom formula.
private theorem heavyTailWitness_not_integrable :
    ¬ Integrable id ((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ) := by
  intro hInt
  have hmap :
      Measure.map heavyTailPoint (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)) =
        ((heavyTailSourcePMF.map heavyTailPoint).toMeasure : Measure ℝ) := by
    simpa using
      (PMF.toMeasure_map (p := heavyTailSourcePMF) (hf := measurable_of_countable heavyTailPoint))
  have hSourceInt :
      Integrable heavyTailPoint (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)) := by
    -- Proof comment: pull the pushed-forward integrability statement back to the discrete source
    -- along the injective support map.
    have hMapped : Integrable id (Measure.map heavyTailPoint (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ))) := by
      simpa [hmap] using hInt
    have hPull :
        Integrable (id ∘ heavyTailPoint) (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)) :=
      (heavyTailPoint_measurableEmbedding.integrable_map_iff
        (μ := (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ))) (g := id)).mp hMapped
    simpa using hPull
  have hsumSource :
      (Measure.sum fun s : ℕ ⊕ ℕ ↦ heavyTailSourcePMF s • Measure.dirac s) =
        (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ)) := by
    -- Proof comment: rewrite the discrete PMF once as the canonical weighted sum of Dirac masses.
    simpa [PMF.toMeasure_apply_singleton, measurableSet_singleton] using
      (Measure.sum_smul_dirac (μ := (heavyTailSourcePMF.toMeasure : Measure (ℕ ⊕ ℕ))))
  have hDiracInt :
      Integrable heavyTailPoint
        (Measure.sum fun s : ℕ ⊕ ℕ ↦ heavyTailSourcePMF s • Measure.dirac s) := by
    simpa [hsumSource] using hSourceInt
  have hSummable :
      Summable (fun s : ℕ ⊕ ℕ ↦ (heavyTailSourcePMF s).toReal * ‖heavyTailPoint s‖) := by
    rw [MeasureTheory.integrable_sum_dirac_iff
      (x := fun s : ℕ ⊕ ℕ ↦ s)
      (c := fun s : ℕ ⊕ ℕ ↦ heavyTailSourcePMF s)
      (f := heavyTailPoint)
      (fun s ↦ heavyTailSourcePMF.apply_ne_top s)] at hDiracInt
    simpa using hDiracInt
  have hLeftSummable :
      Summable
        (fun n : ℕ ↦ (heavyTailSourcePMF (Sum.inl n)).toReal * ‖heavyTailPoint (Sum.inl n)‖) := by
    -- Proof comment: any summable series on the sum type stays summable when restricted to one
    -- injective branch.
    simpa [Function.comp_def] using hSummable.comp_injective Sum.inl_injective
  have hHarmonicShift :
      Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) := by
    have hconst :
        Summable (fun n : ℕ ↦ ((4 * Real.log 2)⁻¹) * (1 / (n + 1 : ℝ))) := by
      have hterms :
          (fun n : ℕ ↦ (heavyTailSourcePMF (Sum.inl n)).toReal * ‖heavyTailPoint (Sum.inl n)‖) =
            fun n : ℕ ↦ ((4 * Real.log 2)⁻¹) * (1 / (n + 1 : ℝ)) := by
        funext n
        exact heavyTailSource_leftBranch_term_eq n
      rw [hterms] at hLeftSummable
      exact hLeftSummable
    have hconst_ne : ((4 * Real.log 2)⁻¹ : ℝ) ≠ 0 := by
      have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      exact inv_ne_zero (mul_ne_zero (by norm_num) hlog)
    exact (summable_mul_left_iff hconst_ne).1 hconst
  have hShiftNot : ¬ Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) := by
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
      mt ((_root_.summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 1).1)
        Real.not_summable_one_div_natCast
  exact hShiftNot hHarmonicShift

-- Proof sketch: choose a heavy-tailed real probability law whose positive and negative tails
-- cancel in the first derivative of the characteristic function, while the absolute first moment
-- remains infinite.
/-- Part (4) of Exercise 15.4.4: there exists a real probability distribution whose characteristic
function is differentiable at `0` although the absolute first moment is infinite. -/
-- TODO: finish this by combining the explicit heavy-tail witness with the restored scaled-tail,
-- symmetry, and non-integrability lemmas above.
theorem exists_probabilityMeasure_differentiableAt_charFun_zero_not_integrable_id :
    ∃ μ : ProbabilityMeasure ℝ,
      DifferentiableAt ℝ (charFun (μ : Measure ℝ)) 0 ∧
        ¬ Integrable id (μ : Measure ℝ) := by
  let μ : ProbabilityMeasure ℝ := ⟨(heavyTailSourcePMF.map heavyTailPoint).toMeasure, inferInstance⟩
  refine ⟨μ, ?_, ?_⟩
  · -- Proof comment: the heavy-tail witness satisfies the Feller tail criterion with `m = 0`,
    -- because its scaled tail vanishes and its symmetric truncated first moments are eventually
    -- identically zero.
    have hTail :
        Tendsto
          (fun x ↦ x * ((μ : Measure ℝ).real {y : ℝ | x < |y|}))
          atTop
          (𝓝 0) := by
      simpa [μ] using heavyTailWitness_scaledTail_tendstoZero
    have hMean :
        Tendsto (fun x ↦ ∫ y in Set.Icc (-x) x, y ∂(μ : Measure ℝ)) atTop (𝓝 (0 : ℝ)) := by
      have hEventually :
          (fun x ↦ ∫ y in Set.Icc (-x) x, y ∂(μ : Measure ℝ)) =ᶠ[atTop]
            fun _ : ℝ ↦ (0 : ℝ) := by
        filter_upwards [Ici_mem_atTop (0 : ℝ)] with x hx
        simpa [μ] using heavyTailWitness_textbookIccIntegral_eq_zero hx
      exact Tendsto.congr' hEventually.symm tendsto_const_nhds
    have hDeriv :
        HasDerivAt (charFun (μ : Measure ℝ)) (((0 : ℝ) : ℂ) * Complex.I) 0 :=
      (hasDerivAt_charFun_zero_iff_tendsto_tail_and_truncated_mean (μ : Measure ℝ) 0).2
        ⟨hTail, hMean⟩
    simpa using hDeriv.differentiableAt
  · -- Proof comment: the explicit witness was designed to have infinite absolute first moment.
    simpa [μ] using heavyTailWitness_not_integrable
