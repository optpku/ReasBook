/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_3
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_8
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

public section

noncomputable section

namespace RealL2

/-- Helper for Exercise 2.7: `harmonicDiagonal` is self-adjoint because it is a real diagonal
operator. -/
lemma harmonicDiagonal_isSelfAdjoint : IsSelfAdjoint harmonicDiagonal := by
  -- Rewrite the concrete operator back to the generic diagonal construction.
  have hdiag : harmonicDiagonal = diagonal harmonicWeights := by
    ext f n
    rw [harmonicDiagonal_apply, diagonal_apply, harmonicWeights_apply]
  rw [hdiag]
  exact isSelfAdjoint_diagonal harmonicWeights

/-- Helper for Exercise 2.7: the quadratic form of `harmonicDiagonal` is nonnegative. -/
lemma harmonicDiagonal_reApplyInnerSelf_nonneg (f : lp (fun _ : ℕ ↦ ℝ) 2) :
    0 ≤ harmonicDiagonal.reApplyInnerSelf f := by
  -- Expand the quadratic form into coordinates and show each summand is nonnegative.
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_eq_tsum]
  refine tsum_nonneg fun n ↦ ?_
  have hweight : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hsquare : 0 ≤ f n * f n := by nlinarith [sq_nonneg (f n)]
  simpa [harmonicDiagonal_apply, mul_assoc] using mul_nonneg hweight hsquare

/-- Helper for Exercise 2.7: the quadratic form of `harmonicDiagonal` on the basis vector
`deltaSequence n` is the `n`th harmonic weight. -/
lemma harmonicDiagonal_reApplyInnerSelf_deltaSequence (n : ℕ) :
    harmonicDiagonal.reApplyInnerSelf (deltaSequence n) = 1 / ((n : ℝ) + 1) := by
  -- Reduce the inner product to the unique nonzero coordinate of the basis vector.
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_eq_tsum, harmonicDiagonal_deltaSequence]
  rw [tsum_eq_single n]
  · simp [deltaSequence_apply]
  · intro j hj
    simp [lp.single_apply, deltaSequence_apply, hj]

/-- Helper for Exercise 2.7: the orthogonal complement of the range of `harmonicDiagonal` is
trivial. -/
lemma harmonicDiagonal_rangeOrthogonal_eq_bot : (harmonicDiagonal.range)ᗮ = ⊥ := by
  -- Convert the orthogonal complement of the range into the kernel of the adjoint.
  calc
    (harmonicDiagonal.range)ᗮ = (ContinuousLinearMap.adjoint harmonicDiagonal).ker := by
      simpa using harmonicDiagonal.orthogonal_range
    _ = harmonicDiagonal.ker := by
      rw [harmonicDiagonal_isSelfAdjoint.adjoint_eq]
    _ = ⊥ := harmonicDiagonal_ker_eq_bot

/-- Helper for Exercise 2.7: the carrier set of `harmonicDiagonal.range` is `Set.range
harmonicDiagonal`. -/
lemma harmonicDiagonal_rangeSet_eq :
    (harmonicDiagonal.range : Set (lp (fun _ : ℕ ↦ ℝ) 2)) = Set.range harmonicDiagonal := by
  ext y
  rfl

/-- Exercise 2.7 (1). The Rayleigh-quotient infimum of `harmonicDiagonal` over nonzero vectors is
`0`; equivalently, by scale-invariance, the infimum on the unit sphere is `0`. -/
theorem harmonicDiagonal_iInfRayleighQuotient_eq_zero :
    (⨅ x : {f : lp (fun _ : ℕ ↦ ℝ) 2 // f ≠ 0}, harmonicDiagonal.rayleighQuotient x) = 0 :=
    by
  -- Move to the unit sphere, where the denominator in the Rayleigh quotient is constant.
  rw [harmonicDiagonal.iInf_rayleigh_eq_iInf_rayleigh_sphere zero_lt_one]
  have hdelta_mem (n : ℕ) : deltaSequence n ∈ Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm]
    simpa [deltaSequence_norm]
  -- Local instance justification (inhabited index): `le_ciInf` on the sphere needs an explicit
  -- witness, and `deltaSequence 0` lies on the unit sphere.
  letI : Nonempty (Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1) :=
    ⟨⟨deltaSequence 0, hdelta_mem 0⟩⟩
  have hBddBelow :
      BddBelow
        (Set.range fun x : Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1 ↦
          harmonicDiagonal.rayleighQuotient x) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hxnorm : ‖((x : Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1) :
        lp (fun _ : ℕ ↦ ℝ) 2)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using x.property
    simpa [ContinuousLinearMap.rayleighQuotient, hxnorm] using
      harmonicDiagonal_reApplyInnerSelf_nonneg (x : lp (fun _ : ℕ ↦ ℝ) 2)
  apply le_antisymm
  · -- Basis vectors on the sphere make the Rayleigh quotient arbitrarily small.
    by_contra hgt
    have hgt' : 0 < ⨅ x : Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1,
        harmonicDiagonal.rayleighQuotient x := by
      exact lt_of_not_ge hgt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgt'
    have hdelta_rayleigh :
        harmonicDiagonal.rayleighQuotient (deltaSequence n) = 1 / ((n : ℝ) + 1) := by
      simp [ContinuousLinearMap.rayleighQuotient,
        harmonicDiagonal_reApplyInnerSelf_deltaSequence, deltaSequence_norm]
    have hle :
        (⨅ x : Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1, harmonicDiagonal.rayleighQuotient x) ≤
          1 / ((n : ℝ) + 1) := by
      refine ciInf_le_of_le hBddBelow ⟨deltaSequence n, hdelta_mem n⟩ ?_
      simpa [hdelta_rayleigh]
    exact (not_le_of_gt hn) hle
  · -- Every unit vector gives a nonnegative Rayleigh quotient, so the infimum is nonnegative.
    refine le_ciInf (f := fun x : Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1 ↦
      harmonicDiagonal.rayleighQuotient x) fun x ↦ ?_
    have hxnorm : ‖((x : Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1) :
        lp (fun _ : ℕ ↦ ℝ) 2)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using x.property
    simpa [ContinuousLinearMap.rayleighQuotient, hxnorm] using
      harmonicDiagonal_reApplyInnerSelf_nonneg (x : lp (fun _ : ℕ ↦ ℝ) 2)

/-- Exercise 2.7 (1), equivalent unit-sphere form. -/
theorem harmonicDiagonal_iInfRayleighQuotient_unitSphere_eq_zero :
    (⨅ x : Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1,
      harmonicDiagonal.rayleighQuotient x) = 0 := by
  -- Transfer the already-proved nonzero-vector infimum through scale invariance.
  simpa using
    (harmonicDiagonal.iInf_rayleigh_eq_iInf_rayleigh_sphere zero_lt_one).symm.trans
      harmonicDiagonal_iInfRayleighQuotient_eq_zero

/-- Exercise 2.7 (2). The minimum of `harmonicDiagonal.reApplyInnerSelf` on the unit sphere is not
attained. -/
theorem harmonicDiagonal_noUnitMinimizer :
    ¬ ∃ f : lp (fun _ : ℕ ↦ ℝ) 2,
        f ∈ Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1 ∧
          IsMinOn harmonicDiagonal.reApplyInnerSelf
            (Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1) f :=
    by
  intro h
  rcases h with ⟨f, hf_sphere, hf_min⟩
  -- A unit vector is nonzero, so the minimizer theorem for self-adjoint operators applies.
  have hf_ne : f ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨f, hf_sphere⟩
  have hf_norm : ‖f‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hf_sphere
  have hf_min' :
      IsMinOn harmonicDiagonal.reApplyInnerSelf
        (Metric.sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) ‖f‖) f := by
    simpa [hf_norm] using hf_min
  have hEigen :=
    harmonicDiagonal_isSelfAdjoint.hasEigenvector_of_isMinOn hf_ne hf_min'
  have hker : f ∈ harmonicDiagonal.ker := by
    rw [LinearMap.mem_ker]
    simpa [harmonicDiagonal_iInfRayleighQuotient_eq_zero] using hEigen.apply_eq_smul
  have hf_zero : f = 0 := by
    simpa [harmonicDiagonal_ker_eq_bot] using hker
  exact hf_ne hf_zero

/-- Exercise 2.7 (3). The range of `harmonicDiagonal` is dense in real `ℓ²`. -/
theorem harmonicDiagonal_denseRange : DenseRange harmonicDiagonal := by
  -- Reduce dense range to showing that the closure of the range is the whole space.
  rw [denseRange_iff_closure_range]
  have hclosure : harmonicDiagonal.range.topologicalClosure = ⊤ := by
    exact (Submodule.topologicalClosure_eq_top_iff (K := harmonicDiagonal.range)).2
      harmonicDiagonal_rangeOrthogonal_eq_bot
  have hclosureSet :
      (harmonicDiagonal.range.topologicalClosure : Set (lp (fun _ : ℕ ↦ ℝ) 2)) = Set.univ := by
    simpa [Submodule.topologicalClosure_coe] using
      congrArg
        (fun S : Submodule ℝ (lp (fun _ : ℕ ↦ ℝ) 2) => (S : Set (lp (fun _ : ℕ ↦ ℝ) 2)))
        hclosure
  -- Convert the submodule closure statement back to the set-theoretic `DenseRange` formulation.
  simpa [harmonicDiagonal_rangeSet_eq] using hclosureSet

end RealL2
