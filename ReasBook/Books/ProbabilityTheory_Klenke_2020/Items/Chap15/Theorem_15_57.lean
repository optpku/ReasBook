/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_54
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_56

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/- Theorem 15.57 is `source-facing`: the main mathematical content is the weak convergence of the
laws of the textbook normalized sums. In this domain the `core/canonical` owners are
`ProbabilityMeasure.map` for laws of measurable random vectors and `multivariateGaussian` for the
limit law. Since the chapter's `partialSum` owner is specialized to real-valued sequences, this
file keeps the vector-valued finite sum only as an internal bridge, not as a parallel public API.
-/

-- Proof sketch: each summand `X (k + 1)` is almost everywhere measurable, finite sums preserve
-- almost everywhere measurability, and multiplication by the constant `(√n)⁻¹` preserves it.
private theorem aemeasurable_multivariateCltNormalizedSum {P : Measure Ω}
    (X : ℕ → Ω → E)
    (hX : ∀ n, AEMeasurable (X (n + 1)) P) (n : ℕ) :
    AEMeasurable (fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, X (k + 1) ω) P := by
  -- Proof comment: finite sums preserve almost everywhere measurability, and so does scalar
  -- multiplication by the constant `(√n)⁻¹`.
  simpa using
    (Finset.aemeasurable_fun_sum _ fun k _ ↦ hX k).const_smul ((Real.sqrt (n : ℝ))⁻¹ : ℝ)

/-- Helper for Theorem 15.57: the variance of the scalar projection `ω ↦ ⟪v, X 1 ω⟫` is the
quadratic form `vᵀ C v`. -/
private theorem scalarProjectionVariance_eq {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (C : Matrix (Fin d) (Fin d) ℝ)
    (hX_meas : AEMeasurable (X 1) P)
    (hX_memLp : MemLp (X 1) 2 P)
    (hX_cov : ∀ i j : Fin d, cov[fun ω ↦ X 1 ω i, fun ω ↦ X 1 ω j; P] = C i j)
    (v : E) :
    Var[fun ω ↦ ⟪v, X 1 ω⟫; P] = dotProduct v (Matrix.mulVec C v) := by
  have hcoord : ∀ i : Fin d, MemLp (fun ω ↦ X 1 ω i) 2 P := fun i ↦ hX_memLp.eval_piLp i
  have hmap_memLp : MemLp id 2 (P.map (X 1)) := by
    simpa using (memLp_map_measure_iff aestronglyMeasurable_id hX_meas).2 hX_memLp
  have hvar_map :
      Var[fun ω ↦ ⟪v, X 1 ω⟫; P] = Var[fun x : E ↦ ⟪v, x⟫; P.map (X 1)] := by
    simpa [Function.comp] using
      (variance_map (X := fun x : E ↦ ⟪v, x⟫) (μ := P) (Y := X 1)
        (aemeasurable_id.const_inner) hX_meas).symm
  -- Proof comment: move to the pushforward law of `X 1`, identify the variance with the
  -- covariance bilinear form, and then evaluate that form using the coordinate covariance data.
  calc
    Var[fun ω ↦ ⟪v, X 1 ω⟫; P]
        = Var[fun x : E ↦ ⟪v, x⟫; P.map (X 1)] := hvar_map
    _ = covarianceBilin (P.map (X 1)) v v := by
      rw [← covarianceBilin_self hmap_memLp]
    _ = ∑ i, ∑ j, v i * v j * cov[fun ω ↦ X 1 ω i, fun ω ↦ X 1 ω j; P] := by
      simpa using covarianceBilin_apply_pi (μ := P) (X := fun i ω ↦ X 1 ω i) hcoord v v
    _ = ∑ i, ∑ j, v i * v j * C i j := by
      simp_rw [hX_cov]
    _ = dotProduct v (Matrix.mulVec C v) := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm, mul_comm]

/-- Helper for Theorem 15.57: the covariance matrix obtained from the coordinate covariances of
`X 1` is positive semidefinite. -/
private theorem covarianceMatrix_posSemidef {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (C : Matrix (Fin d) (Fin d) ℝ)
    (hX_meas : AEMeasurable (X 1) P)
    (hX_memLp : MemLp (X 1) 2 P)
    (hX_cov : ∀ i j : Fin d, cov[fun ω ↦ X 1 ω i, fun ω ↦ X 1 ω j; P] = C i j) :
    C.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · -- Proof comment: covariance is symmetric, so `C` is Hermitian over `ℝ`.
    ext i j
    rw [Matrix.conjTranspose_apply, ← hX_cov j i, ← hX_cov i j, covariance_comm]
    simp
  · -- Proof comment: each quadratic form `vᵀ C v` is a variance, hence nonnegative.
    intro v
    have hnonneg :
        0 ≤ dotProduct (WithLp.toLp 2 v : E) (Matrix.mulVec C (WithLp.toLp 2 v)) := by
      rw [← scalarProjectionVariance_eq (X := X) (C := C) hX_meas hX_memLp hX_cov
        (v := (WithLp.toLp 2 v : E))]
      exact variance_nonneg (fun ω ↦ ⟪(WithLp.toLp 2 v : E), X 1 ω⟫) P
    simpa using hnonneg

-- Proof sketch: for each `v`, apply the one-dimensional CLT to the scalar projections
-- `ω ↦ ⟪v, X n ω⟫`, whose limiting variance is identified from the covariance matrix `C`.
-- Then use the multidimensional convergence criterion from the preceding section
-- (the Cramér--Wold device / Theorem 15.56) to upgrade convergence of all linear forms to weak
-- convergence of the vector laws.
/-- Theorem 15.57: if `X₁, X₂, …` are i.i.d. `ℝ^d`-valued random vectors with mean `0` and
covariance matrix `C`, then the laws of the normalized sums `S_n^*` converge weakly to the
multivariate Gaussian law `N_{0,C}`. -/
theorem multivariate_central_limit_theorem (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (C : Matrix (Fin d) (Fin d) ℝ)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (hX_memLp : MemLp (X 1) 2 P)
    (hX_mean : ∫ ω, X 1 ω ∂P = 0)
    (hX_cov : ∀ i j : Fin d, cov[fun ω ↦ X 1 ω i, fun ω ↦ X 1 ω j; P] = C i j) :
    Tendsto
      (fun n : ℕ ↦
        ProbabilityMeasure.map ⟨P, inferInstance⟩
          (show AEMeasurable
              (fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, X (k + 1) ω) P from
            aemeasurable_multivariateCltNormalizedSum X
              (fun n ↦ (hX_ident n).aemeasurable_fst) n))
      atTop
      (𝓝 ⟨multivariateGaussian 0 C, inferInstance⟩) := by
  let μs : ℕ → ProbabilityMeasure E := fun n ↦
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (show AEMeasurable
          (fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, X (k + 1) ω) P from
        aemeasurable_multivariateCltNormalizedSum X (fun n ↦ (hX_ident n).aemeasurable_fst) n)
  let μlim : ProbabilityMeasure E := ⟨multivariateGaussian 0 C, inferInstance⟩
  have hC_posSemidef : C.PosSemidef :=
    covarianceMatrix_posSemidef (X := X) (C := C) (hX_ident 0).aemeasurable_fst hX_memLp hX_cov
  have hprojLaw :
      ∀ v : E, Tendsto (fun n ↦ scalarProjectionLaw (μs n) v) atTop
        (𝓝
          ((⟨gaussianReal 0
              (Real.toNNReal (dotProduct v (Matrix.mulVec C v))), inferInstance⟩ :
            ProbabilityMeasure ℝ))) := by
    intro v
    have hproj_memLp : MemLp (fun ω ↦ ⟪v, X 1 ω⟫) 2 P := hX_memLp.const_inner v
    have hproj_mean : ∫ ω, ⟪v, X 1 ω⟫ ∂P = 0 := by
      -- Proof comment: the mean of every scalar projection is the inner product against the
      -- vector mean, which is zero by hypothesis.
      rw [integral_inner (hX_memLp.integrable one_le_two), hX_mean]
      simp
    have hproj_indep : iIndepFun (fun n ↦ fun ω ↦ ⟪v, X (n + 1) ω⟫) P :=
      hX_indep.comp (fun _ x ↦ ⟪v, x⟫) (by intro n; fun_prop)
    have hproj_ident :
        ∀ n, IdentDistrib (fun ω ↦ ⟪v, X (n + 1) ω⟫) (fun ω ↦ ⟪v, X 1 ω⟫) P P := by
      intro n
      exact (hX_ident n).comp (u := fun x ↦ ⟪v, x⟫) (by fun_prop)
    have hclt :
        TendstoInDistribution
          (fun (n : ℕ) ω ↦
            (Real.sqrt (n : ℝ))⁻¹ *
              (∑ k ∈ Finset.range n, ⟪v, X (k + 1) ω⟫ - n * P[fun ω ↦ ⟪v, X 1 ω⟫]))
          atTop id (fun _ ↦ P)
          (gaussianReal 0 (Var[fun ω ↦ ⟪v, X 1 ω⟫; P].toNNReal)) := by
      -- Proof comment: this is the one-dimensional CLT applied to the projected i.i.d. sequence.
      exact
        ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
          (P := P) (P' := gaussianReal 0 (Var[fun ω ↦ ⟪v, X 1 ω⟫; P].toNNReal))
          (X := fun n ω ↦ ⟪v, X (n + 1) ω⟫) (Y := id) HasLaw.id
          hproj_memLp hproj_indep hproj_ident
    have hclt' :
        TendstoInDistribution
          (fun (n : ℕ) ω ↦ ⟪v, (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, X (k + 1) ω⟫)
          atTop id (fun _ ↦ P)
          (gaussianReal 0 (Var[fun ω ↦ ⟪v, X 1 ω⟫; P].toNNReal)) := by
      -- Proof comment: rewrite the scalar CLT surface back into the inner product of the
      -- vector-valued normalized sum.
      refine TendstoInDistribution.congr (fun n ↦ ?_) (by simp) hclt
      filter_upwards with ω
      have hsum :
          ⟪v, (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, X (k + 1) ω⟫ =
            (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, ⟪v, X (k + 1) ω⟫ := by
        rw [real_inner_smul_right, inner_sum]
      calc
        (Real.sqrt (n : ℝ))⁻¹ *
            (∑ k ∈ Finset.range n, ⟪v, X (k + 1) ω⟫ - n * P[fun ω ↦ ⟪v, X 1 ω⟫])
            = (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, ⟪v, X (k + 1) ω⟫ := by
                rw [hproj_mean, mul_zero, sub_zero]
        _ = ⟪v, (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, X (k + 1) ω⟫ := by
              rw [← hsum]
    have hproj_eq :
        (fun (n : ℕ) ↦ scalarProjectionLaw (μs n) v) =
          fun (n : ℕ) ↦
            ProbabilityMeasure.map ⟨P, inferInstance⟩
              (show AEMeasurable
                  (fun ω ↦ ⟪v, (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, X (k + 1) ω⟫) P
                from
                  (aemeasurable_multivariateCltNormalizedSum X
                    (fun n ↦ (hX_ident n).aemeasurable_fst) n).const_inner (c := v)) := by
      -- Proof comment: scalar projection of a pushforward law is the pushforward law of the
      -- scalar-projected random variable.
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      ext s hs
      let f : Ω → E := fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, X (k + 1) ω
      have hf : AEMeasurable f P :=
        aemeasurable_multivariateCltNormalizedSum X (fun n ↦ (hX_ident n).aemeasurable_fst) n
      have hg : AEMeasurable (fun x : E ↦ ⟪v, x⟫) (Measure.map f P) := by
        simpa [μs, f] using scalarProjectionAEMeasurable (μs n) v
      -- Proof comment: unfold both pushforwards to the underlying measures and apply the
      -- measure-level composition formula.
      change (Measure.map (fun x : E ↦ ⟪v, x⟫) (Measure.map f P)) s =
        (Measure.map (fun ω ↦ ⟪v, f ω⟫) P) s
      rw [Measure.map_apply_of_aemeasurable hg hs, Measure.map_apply₀ hf (hg.nullMeasurable hs)]
      change P (f ⁻¹' ((fun x : E ↦ ⟪v, x⟫) ⁻¹' s)) =
        (Measure.map ((fun x : E ↦ ⟪v, x⟫) ∘ f) P) s
      rw [Measure.map_apply_of_aemeasurable (hg.comp_aemeasurable hf) hs]
      rfl
    rw [hproj_eq]
    have hlimitVariance :
        Var[fun ω ↦ ⟪v, X 1 ω⟫; P].toNNReal =
          Real.toNNReal (dotProduct v (Matrix.mulVec C v)) := by
      rw [scalarProjectionVariance_eq (X := X) (C := C) (hX_ident 0).aemeasurable_fst
        hX_memLp hX_cov]
    simpa [hlimitVariance]
      using hclt'.tendsto
  have hlimitProj :
      ∀ v : E,
        scalarProjectionLaw μlim v =
          ((⟨gaussianReal 0
              (Real.toNNReal (dotProduct v (Matrix.mulVec C v))), inferInstance⟩ :
            ProbabilityMeasure ℝ)) := by
    intro v
    apply ProbabilityMeasure.toMeasure_injective
    simpa [μlim, scalarProjectionLaw, scalarProjectionAEMeasurable,
      InnerProductSpace.toDualMap_apply_apply] using
      innerMap_multivariateGaussian_eq_gaussianReal (μ := 0) (C := C) hC_posSemidef v
  have hprojLaw_limit :
      ∀ v : E,
        Tendsto (fun n ↦ scalarProjectionLaw (μs n) v) atTop
          (𝓝 (scalarProjectionLaw μlim v)) := by
    intro v
    rw [hlimitProj v]
    exact hprojLaw v
  have hchar :
      ∀ t : E, Tendsto (fun n ↦ charFun (μs n) t) atTop (𝓝 (charFun (μlim : Measure E) t)) := by
    intro t
    -- Proof comment: Theorem 15.56 upgrades convergence of every scalar projection to pointwise
    -- convergence of the vector characteristic functions.
    have hchar' :
        Tendsto (fun n ↦ charFun (μs n) t) atTop
          (𝓝 (charFun (scalarProjectionLaw μlim t : Measure ℝ) (1 : ℝ))) :=
      tendsto_charFun_of_tendsto_all_scalarProjectionLaws (μs := μs)
        (ν := fun v ↦ scalarProjectionLaw μlim v) hprojLaw_limit t
    simpa [charFun_scalarProjection_eq] using hchar'
  -- Proof comment: Levy's continuity theorem on `ℝ^d` identifies the weak limit from the
  -- pointwise characteristic-function convergence.
  have hμs : Tendsto μs atTop (𝓝 μlim) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 hchar
  simpa [μs, μlim] using hμs

end
