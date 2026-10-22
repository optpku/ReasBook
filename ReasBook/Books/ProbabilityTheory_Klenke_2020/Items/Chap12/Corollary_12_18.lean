/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_17

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped symmDiff

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- Helper for Corollary 12.18: exchangeability makes the sample-sequence map a.e.-measurable. -/
private theorem aemeasurableProcessSwap_of_isExchangeable
    {X : ℕ → Ω → E} (hX : IsExchangeable X μ) :
    AEMeasurable (Function.swap X) μ := by
  -- Proof comment: each coordinate of `Function.swap X` has the same law as `X 0`, so the
  -- coordinate maps are a.e.-measurable and hence the whole sequence-valued map is.
  refine aemeasurable_pi_lambda _ fun i ↦ ?_
  simpa [Function.swap] using (hX.identDistrib 0 i).aemeasurable_snd

/-- Helper for Corollary 12.18: finite coordinate-tuples on sequence space are measurable. -/
private theorem measurable_coordinateTuple {n : ℕ} (u : Fin n ↪ ℕ) :
    Measurable (fun x : ℕ → E ↦ fun i : Fin n ↦ x (u i)) := by
  -- Proof comment: a finite tuple of coordinate projections is measurable coordinatewise.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa using (measurable_pi_apply (u i) : Measurable fun x : ℕ → E ↦ x (u i))

omit [IsFiniteMeasure μ] in
/-- Helper for Corollary 12.18: under the pushforward law of the sample-sequence map, the
coordinate process is exchangeable. -/
private theorem coordinateProcess_isExchangeable_map_swap
    {X : ℕ → Ω → E} (hX : IsExchangeable X μ) :
    IsExchangeable (Function.eval : ℕ → (ℕ → E) → E) (μ.map (Function.swap X)) := by
  intro n u σ
  let f : (ℕ → E) → Fin n → E := fun x i ↦ x (u (σ i))
  let g : (ℕ → E) → Fin n → E := fun x i ↦ x (u i)
  have hf_meas : Measurable f := by
    -- Proof comment: the permuted tuple is still a finite family of coordinate projections.
    simpa [f] using
      measurable_coordinateTuple
        ({ toFun := fun i ↦ u (σ i)
           inj' := u.injective.comp σ.injective } : Fin n ↪ ℕ)
  have hg_meas : Measurable g := by
    -- Proof comment: the unpermuted tuple is the same measurable coordinate family.
    simpa [g] using measurable_coordinateTuple u
  have hLaw :
      IdentDistrib (Function.swap X) (id : (ℕ → E) → ℕ → E) μ (μ.map (Function.swap X)) := by
    -- Proof comment: by definition, `μ.map (Function.swap X)` is the law of the sample-sequence
    -- map.
    refine ⟨aemeasurableProcessSwap_of_isExchangeable (μ := μ) (X := X) hX, aemeasurable_id, ?_⟩
    simp
  have hfg :
      IdentDistrib (f ∘ Function.swap X) (g ∘ Function.swap X) μ μ := by
    -- Proof comment: after precomposing with `Function.swap X`, the sequence-space tuple maps
    -- become the corresponding coordinate tuples of `X`, so exchangeability gives the law
    -- invariance.
    simpa [f, g, Function.comp, Function.swap] using hX u σ
  have hf_pull : IdentDistrib (f ∘ Function.swap X) f μ (μ.map (Function.swap X)) :=
    hLaw.comp hf_meas
  have hg_pull : IdentDistrib (g ∘ Function.swap X) g μ (μ.map (Function.swap X)) :=
    hLaw.comp hg_meas
  exact (hf_pull.symm.trans hfg).trans hg_pull

omit [MeasurableSpace Ω] in
/-- Helper for Corollary 12.18: pulling back a coordinate-tail event along the sample-sequence map
produces a tail event for the original process. -/
private theorem measurableSet_preimage_of_coordinateTail
    {X : ℕ → Ω → E} {T : Set (ℕ → E)}
    (hT : MeasurableSet[tailRandomVariableMeasurableSpace
      (Function.eval : ℕ → (ℕ → E) → E)] T) :
    MeasurableSet[tailRandomVariableMeasurableSpace X] ((Function.swap X) ⁻¹' T) := by
  -- Proof comment: tail measurability means measurability in every tail stage; after pulling back
  -- a fixed stage along `Function.swap X`, the coordinate maps become the original process maps.
  rw [tailRandomVariableMeasurableSpace, tailMeasurableSpace_nat_eq_iInf_iSup_Ici,
    MeasurableSpace.measurableSet_iInf] at hT ⊢
  intro n
  have hstage :
      MeasurableSpace.comap (Function.swap X)
        (⨆ i ∈ Set.Ici n, MeasurableSpace.comap (Function.eval i) inferInstance) =
        ⨆ i ∈ Set.Ici n, MeasurableSpace.comap (X i) inferInstance := by
    rw [MeasurableSpace.comap_iSup]
    refine iSup_congr fun i ↦ ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_congr fun hi ↦ ?_
    rw [MeasurableSpace.comap_comp]
    refine congrArg (fun f : Ω → E ↦ MeasurableSpace.comap f inferInstance) ?_
    funext ω
    rfl
  rw [← hstage, MeasurableSpace.measurableSet_comap]
  exact ⟨T, hT n, rfl⟩

/-- Helper for Corollary 12.18: on sequence space, every exchangeable event should admit a
tail-measurable representative. -/
private theorem existsCylinderApproxSeq_of_measurableSet
    {ν : Measure (ℕ → E)} [IsFiniteMeasure ν] {S : Set (ℕ → E)} (hS : MeasurableSet S) :
    ∃ C : ℕ → Set (ℕ → E),
      (∀ n, C n ∈ MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E)) ∧
      ∀ n, ν (S ∆ C n) < ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
  have hdense : ν.MeasureDense (MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E)) := by
    -- Proof comment: finite-coordinate cylinders form a measure-dense set algebra on sequence
    -- space.
    refine Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
        (μ := ν)
        (𝒜 := MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E))
        MeasureTheory.isSetAlgebra_measurableCylinders ?_
    simpa using
      (MeasureTheory.generateFrom_measurableCylinders (α := fun _ : ℕ ↦ E)).symm
  choose C hCmem hCfin hCclose using
    fun n : ℕ ↦
      hdense.fin_meas_approx hS (measure_ne_top ν S) (1 / (n + 1 : ℝ)) (by positivity)
  exact ⟨C, hCmem, hCclose⟩

/-- Helper for Corollary 12.18: every measurable cylinder indicator can be written as a measurable
finite-prefix observable. -/
private theorem measurableCylinderIndicator_asFiniteCoordinateTest
    {C : Set (ℕ → E)} (hC : C ∈ MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E)) :
    ∃ n : ℕ, ∃ φ : (Fin n → E) → ℝ,
      Measurable φ ∧
      C.indicator (fun _ ↦ (1 : ℝ)) = fun x ↦ φ (fun i ↦ x i) := by
  classical
  let s : Finset ℕ := MeasureTheory.measurableCylinders.finset hC
  let S : Set ((i : s) → E) := MeasureTheory.measurableCylinders.set hC
  let n : ℕ := s.sup id + 1
  have hlt : ∀ i : s, (i : ℕ) < n := by
    intro i
    exact Nat.lt_succ_of_le <| by
      simpa [n] using (Finset.le_sup (s := s) (f := id) i.2)
  let embed : s ↪ Fin n :=
    ⟨fun i ↦ ⟨(i : ℕ), hlt i⟩,
      fun i j hij ↦ Subtype.ext <| by simpa using hij⟩
  let restrictPrefix : (Fin n → E) → ((i : s) → E) := fun y i ↦ y (embed i)
  have hS : MeasurableSet S := MeasureTheory.measurableCylinders.measurableSet hC
  have hrestrictPrefix_meas : Measurable restrictPrefix := by
    -- Proof comment: the support restriction is measurable coordinatewise.
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa [restrictPrefix, embed] using
      (measurable_pi_apply (embed i) : Measurable fun y : Fin n → E ↦ y (embed i))
  let φ : (Fin n → E) → ℝ := Set.indicator (restrictPrefix ⁻¹' S) (fun _ ↦ (1 : ℝ))
  refine ⟨n, φ, ?_, ?_⟩
  · -- Proof comment: the prefix test is the indicator of a measurable preimage set.
    exact (measurable_indicator_const_iff (1 : ℝ)).2 (hS.preimage hrestrictPrefix_meas)
  · -- Proof comment: evaluating the prefix test on the first `n` coordinates recovers the
    -- original cylinder membership because every support index lies below `n`.
    have hrestrict :
        ∀ x : ℕ → E, restrictPrefix (fun i : Fin n ↦ x i) = s.restrict x := by
      intro x
      funext i
      rfl
    funext x
    rw [MeasureTheory.measurableCylinders.eq_cylinder hC]
    change ite (s.restrict x ∈ S) (1 : ℝ) 0 =
      ite (restrictPrefix (fun i : Fin n ↦ x i) ∈ S) (1 : ℝ) 0
    rw [hrestrict x]

/-- Helper for Corollary 12.18: Theorem 12.17 identifies the exchangeable and tail conditional
expectations of any cylinder indicator on sequence space. -/
private theorem cylinderIndicator_condExp_exchangeable_eq_tail
    {ν : Measure (ℕ → E)} [IsFiniteMeasure ν]
    (hEval : IsExchangeable (Function.eval : ℕ → (ℕ → E) → E) ν)
    {C : Set (ℕ → E)} (hC : C ∈ MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E)) :
    ν[C.indicator (fun _ ↦ (1 : ℝ)) | exchangeableSequenceSigmaAlgebra] =ᵐ[ν]
      ν[C.indicator (fun _ ↦ (1 : ℝ)) |
        tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] := by
  rcases measurableCylinderIndicator_asFiniteCoordinateTest (E := E) hC with ⟨n, φ, hφ_meas, hφ_eq⟩
  have hC_meas : MeasurableSet C := MeasurableSet.of_mem_measurableCylinders hC
  have hφ_int : Integrable (fun x : ℕ → E ↦ φ (fun i : Fin n ↦ x i)) ν := by
    -- Proof comment: after rewriting by the cylinder representation, the observable is just an
    -- indicator of a measurable set under a finite measure.
    simpa [hφ_eq] using (integrable_const (1 : ℝ)).indicator hC_meas
  have hEval_meas : ∀ i, Measurable (Function.eval i : (ℕ → E) → E) := fun i ↦
    measurable_pi_apply i
  -- Proof comment: Theorem 12.17 applies directly to the coordinate process on sequence space
  -- because the cylinder indicator now has the required finite-prefix normal form.
  simpa [exchangeableSigmaAlgebra, Function.swap, Function.comp, hφ_eq] using
    (exchangeableAverage_limit_of_isExchangeable
      (Ω := ℕ → E) (E := E) (μ := ν) (X := Function.eval) (φ := φ)
      hEval hEval_meas hφ_meas hφ_int).1

/-- Helper for Corollary 12.18: symmetric-difference approximation of events yields `L¹`
approximation of their indicators. -/
private theorem tendsto_eLpNorm_indicatorApprox_sub_indicator
    {ν : Measure (ℕ → E)} [IsFiniteMeasure ν] {S : Set (ℕ → E)}
    (hS : MeasurableSet S) {C : ℕ → Set (ℕ → E)} (hC : ∀ n, MeasurableSet (C n))
    (hApprox : ∀ n, ν (S ∆ C n) < ENNReal.ofReal (1 / (n + 1 : ℝ))) :
    Tendsto
      (fun n ↦
        eLpNorm
          (Set.indicator (C n) (fun _ ↦ (1 : ℝ)) - Set.indicator S (fun _ ↦ (1 : ℝ))) 1 ν)
      atTop (nhds 0) := by
  have hNorm_eq :
      ∀ n,
        eLpNorm
            (Set.indicator (C n) (fun _ ↦ (1 : ℝ)) - Set.indicator S (fun _ ↦ (1 : ℝ))) 1 ν =
          ν (S ∆ C n) := by
    intro n
    have hSymmDiff_meas : MeasurableSet (C n ∆ S) := (hC n).symmDiff hS
    calc
      eLpNorm
          (Set.indicator (C n) (fun _ ↦ (1 : ℝ)) - Set.indicator S (fun _ ↦ (1 : ℝ))) 1 ν =
        eLpNorm (Set.indicator (C n ∆ S) (fun _ ↦ (1 : ℝ))) 1 ν := by
          rw [MeasureTheory.eLpNorm_indicator_sub_indicator]
      _ = ν (C n ∆ S) := by
          rw [MeasureTheory.eLpNorm_indicator_const hSymmDiff_meas one_ne_zero ENNReal.one_ne_top]
          simp
      _ = ν (S ∆ C n) := by rw [symmDiff_comm]
  have hUpper :
      Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (nhds 0) := by
    have hUpperReal : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ)) atTop (nhds 0) := by
      convert ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1))
        using 1
      ext n
      simp
    simpa using ENNReal.tendsto_ofReal hUpperReal
  -- Proof comment: the exact `L¹` norm is squeezed between `0` and the prescribed
  -- `1 / (n + 1)` approximation rate.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper ?_ ?_
  · intro n
    simp [hNorm_eq n]
  · intro n
    simpa [hNorm_eq n] using (le_of_lt (hApprox n))

/-- Helper for Corollary 12.18: a single cylinder-level equality yields the residual `L¹` bound
needed to compare the exchangeable and tail conditional expectations. -/
private theorem exchangeableTailCondexp_residualBound_of_aeEq
    {ν : Measure (ℕ → E)} [IsFiniteMeasure ν] {f fSeq : (ℕ → E) → ℝ}
    (hEq :
      ν[fSeq | exchangeableSequenceSigmaAlgebra] =ᵐ[ν]
        ν[fSeq | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) :
    eLpNorm
        (ν[f | exchangeableSequenceSigmaAlgebra] -
          ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν ≤
      eLpNorm (ν[fSeq | exchangeableSequenceSigmaAlgebra] -
          ν[f | exchangeableSequenceSigmaAlgebra]) 1 ν +
        eLpNorm
          (ν[fSeq | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] -
            ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν := by
  have hDecomp :
      (ν[f | exchangeableSequenceSigmaAlgebra] -
          ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) =ᵐ[ν]
        -(ν[fSeq | exchangeableSequenceSigmaAlgebra] -
            ν[f | exchangeableSequenceSigmaAlgebra]) +
          (ν[fSeq | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] -
            ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) := by
    -- Proof comment: insert the shared conditional expectation of `fSeq` and cancel it using the
    -- exchangeable-versus-tail equality for the approximant.
    filter_upwards [hEq] with x hx
    have hPointwise :
        ν[f | exchangeableSequenceSigmaAlgebra] x -
            ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] x =
          -(ν[fSeq | exchangeableSequenceSigmaAlgebra] x -
              ν[f | exchangeableSequenceSigmaAlgebra] x) +
            (ν[fSeq | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] x -
              ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] x) := by
      rw [hx]
      ring
    simpa using hPointwise
  have hLeftMeas :
      AEStronglyMeasurable
        (-(ν[fSeq | exchangeableSequenceSigmaAlgebra] -
            ν[f | exchangeableSequenceSigmaAlgebra]) : (ℕ → E) → ℝ) ν := by
    exact ((MeasureTheory.integrable_condExp (f := fSeq)).sub
      (MeasureTheory.integrable_condExp (f := f))).aestronglyMeasurable.neg
  have hRightMeas :
      AEStronglyMeasurable
        ((ν[fSeq | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] -
            ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) :
          (ℕ → E) → ℝ) ν := by
    exact ((MeasureTheory.integrable_condExp (f := fSeq)).sub
      (MeasureTheory.integrable_condExp (f := f))).aestronglyMeasurable
  calc
    eLpNorm
        (ν[f | exchangeableSequenceSigmaAlgebra] -
          ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν =
        eLpNorm
          (-(ν[fSeq | exchangeableSequenceSigmaAlgebra] -
              ν[f | exchangeableSequenceSigmaAlgebra]) +
            (ν[fSeq | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] -
              ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)])) 1 ν := by
          exact eLpNorm_congr_ae hDecomp
    _ ≤ eLpNorm
          (-(ν[fSeq | exchangeableSequenceSigmaAlgebra] -
              ν[f | exchangeableSequenceSigmaAlgebra])) 1 ν +
        eLpNorm
          (ν[fSeq | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] -
            ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν := by
          exact eLpNorm_add_le hLeftMeas hRightMeas le_rfl
    _ = eLpNorm (ν[fSeq | exchangeableSequenceSigmaAlgebra] -
          ν[f | exchangeableSequenceSigmaAlgebra]) 1 ν +
        eLpNorm
          (ν[fSeq | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] -
            ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν := by
          rw [eLpNorm_neg]

/-- Helper for Corollary 12.18: on sequence space, exchangeable and tail conditional expectations
agree on the `L¹` limit of any cylinder approximation sequence. -/
private theorem exchangeableTailCondexp_eq_of_tendsto_eLpNorm_of_aeEq
    {ν : Measure (ℕ → E)} [IsFiniteMeasure ν]
    (hmEx : exchangeableSequenceSigmaAlgebra ≤ (inferInstance : MeasurableSpace (ℕ → E)))
    (hmTail :
      tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E) ≤
        (inferInstance : MeasurableSpace (ℕ → E)))
    {f : (ℕ → E) → ℝ} {fSeq : ℕ → (ℕ → E) → ℝ} (hf : MemLp f 1 ν)
    (hfSeq : ∀ n, MemLp (fSeq n) 1 ν)
    (hApprox : Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 ν) atTop (nhds 0))
    (hEq :
      ∀ n,
        ν[fSeq n | exchangeableSequenceSigmaAlgebra] =ᵐ[ν]
          ν[fSeq n | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) :
    ν[f | exchangeableSequenceSigmaAlgebra] =ᵐ[ν]
      ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] := by
  have hf_int : Integrable f ν := memLp_one_iff_integrable.mp hf
  have hfSeq_int : ∀ n, Integrable (fSeq n) ν := fun n ↦ memLp_one_iff_integrable.mp (hfSeq n)
  have hCond₁ :
      Tendsto
        (fun n ↦ eLpNorm (ν[fSeq n | exchangeableSequenceSigmaAlgebra] -
          ν[f | exchangeableSequenceSigmaAlgebra]) 1 ν) atTop (nhds 0) :=
    MeasureTheory.tendsto_eLpNorm_condExp_sub_of_tendsto_eLpNorm hmEx hf hfSeq hApprox
  have hCond₂ :
      Tendsto
        (fun n ↦
          eLpNorm
            (ν[fSeq n | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] -
              ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν)
        atTop (nhds 0) :=
    MeasureTheory.tendsto_eLpNorm_condExp_sub_of_tendsto_eLpNorm hmTail hf hfSeq hApprox
  let residualSeq : ℕ → ENNReal := fun _ ↦
    eLpNorm
      (ν[f | exchangeableSequenceSigmaAlgebra] -
        ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν
  have hResidualBound :
      ∀ n,
        residualSeq n ≤
          eLpNorm (ν[fSeq n | exchangeableSequenceSigmaAlgebra] -
              ν[f | exchangeableSequenceSigmaAlgebra]) 1 ν +
            eLpNorm
              (ν[fSeq n |
                  tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] -
                ν[f |
                  tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν := by
    intro n
    simpa [residualSeq] using
      exchangeableTailCondexp_residualBound_of_aeEq (ν := ν) (hEq n)
  have hResidual :
      Tendsto residualSeq atTop (nhds (0 : ENNReal)) := by
    have hUpper :
        Tendsto
          (fun n ↦
            eLpNorm (ν[fSeq n | exchangeableSequenceSigmaAlgebra] -
                ν[f | exchangeableSequenceSigmaAlgebra]) 1 ν +
              eLpNorm
                (ν[fSeq n | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] -
                  ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν)
          atTop (nhds 0) := by
      simpa using hCond₁.add hCond₂
    -- Proof comment: the residual norm is constant and squeezed between `0` and a sequence that
    -- tends to `0`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
      (fun _ ↦ zero_le _) ?_
    intro n
    exact hResidualBound n
  have hResidualZero :
      eLpNorm
          (ν[f | exchangeableSequenceSigmaAlgebra] -
            ν[f |
              tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν = 0 := by
    have hConst :
        Tendsto residualSeq atTop
          (nhds
            (eLpNorm
              (ν[f | exchangeableSequenceSigmaAlgebra] -
                ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) 1 ν)) :=
      tendsto_const_nhds
    exact tendsto_nhds_unique hConst hResidual
  have hResidualAeZero :
      (ν[f | exchangeableSequenceSigmaAlgebra] -
          ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)]) =ᵐ[ν] 0 := by
    -- Proof comment: vanishing `L¹` norm forces the difference to vanish almost everywhere.
    exact
      (eLpNorm_eq_zero_iff
        ((MeasureTheory.integrable_condExp (f := f)).sub
          (MeasureTheory.integrable_condExp (f := f))).aestronglyMeasurable
        one_ne_zero).1 hResidualZero
  filter_upwards [hResidualAeZero] with x hx
  exact sub_eq_zero.mp hx

/-- Helper for Corollary 12.18: on sequence space, the tail conditional expectation of an
exchangeable event indicator agrees almost surely with the indicator itself. -/
private theorem tailCondexp_indicator_ae_eq_indicator_of_mem_exchangeableSequenceSigmaAlgebra
    {ν : Measure (ℕ → E)} [IsFiniteMeasure ν]
    (hEval : IsExchangeable (Function.eval : ℕ → (ℕ → E) → E) ν) {S : Set (ℕ → E)}
    (hS : MeasurableSet[exchangeableSequenceSigmaAlgebra] S) :
    ν[S.indicator (fun _ ↦ (1 : ℝ)) |
        tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] =ᵐ[ν]
      S.indicator (fun _ ↦ (1 : ℝ)) := by
  let f : (ℕ → E) → ℝ := S.indicator (fun _ ↦ (1 : ℝ))
  have hmEx : exchangeableSequenceSigmaAlgebra ≤ (inferInstance : MeasurableSpace (ℕ → E)) := by
    -- Proof comment: the exchangeable sequence sigma-algebra is a sub-`σ`-algebra of the ambient
    -- product measurable space.
    exact exchangeableSequenceSigmaAlgebra_le
  have hmTail :
      tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E) ≤
        (inferInstance : MeasurableSpace (ℕ → E)) := by
    -- Proof comment: every tail stage comes from ambient coordinate maps, so the tail
    -- `σ`-algebra also sits inside the ambient product measurable space.
    simpa [tailRandomVariableMeasurableSpace, tailMeasurableSpace] using
      (limsup_le_iSup.trans <| iSup_le fun n ↦
        (measurable_pi_apply n : Measurable fun x : ℕ → E ↦ x n).comap_le)
  have hS_meas : MeasurableSet S := hmEx S hS
  have hf_meas : Measurable[exchangeableSequenceSigmaAlgebra] f := by
    -- Proof comment: indicators of exchangeable events are exchangeable-measurable.
    simpa [f] using (measurable_indicator_const_iff (1 : ℝ)).2 hS
  have hf_int : Integrable f ν := by
    -- Proof comment: the indicator of an ambient measurable event is integrable under a finite
    -- measure.
    simpa [f] using ((integrable_const (μ := ν) (1 : ℝ)).indicator hS_meas)
  have hf_memLp : MemLp f 1 ν := memLp_one_iff_integrable.mpr hf_int
  rcases existsCylinderApproxSeq_of_measurableSet (ν := ν) hS_meas with ⟨C, hCmem, hCclose⟩
  let fSeq : ℕ → (ℕ → E) → ℝ := fun n ↦ (C n).indicator (fun _ ↦ (1 : ℝ))
  have hC_meas : ∀ n, MeasurableSet (C n) := fun n ↦
    MeasurableSet.of_mem_measurableCylinders (hCmem n)
  have hfSeq_int : ∀ n, Integrable (fSeq n) ν := by
    intro n
    simpa [fSeq] using ((integrable_const (μ := ν) (1 : ℝ)).indicator (hC_meas n))
  have hfSeq_memLp : ∀ n, MemLp (fSeq n) 1 ν := fun n ↦
    memLp_one_iff_integrable.mpr (hfSeq_int n)
  have hApprox :
      Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 ν) atTop (nhds 0) := by
    -- Proof comment: the cylinder approximants converge to the target indicator in `L¹`.
    simpa [f, fSeq] using
      tendsto_eLpNorm_indicatorApprox_sub_indicator
        (ν := ν) (S := S) hS_meas hC_meas hCclose
  have hCondEq :
      ν[f | exchangeableSequenceSigmaAlgebra] =ᵐ[ν]
        ν[f |
          tailRandomVariableMeasurableSpace
            (Function.eval : ℕ → (ℕ → E) → E)] := by
    -- Proof comment: pass the cylinder-level conditional-expectation equality to the `L¹` limit.
    exact exchangeableTailCondexp_eq_of_tendsto_eLpNorm_of_aeEq
      hmEx hmTail hf_memLp hfSeq_memLp hApprox
      (fun n ↦ by
        simpa [fSeq] using
          cylinderIndicator_condExp_exchangeable_eq_tail (ν := ν) hEval (hCmem n))
  have hExchEq : ν[f | exchangeableSequenceSigmaAlgebra] =ᵐ[ν] f := by
    -- Proof comment: conditioning an exchangeable-measurable indicator on the exchangeable
    -- sigma-algebra leaves it unchanged.
    exact condExp_of_aestronglyMeasurable' (μ := ν) (m := exchangeableSequenceSigmaAlgebra)
      hmEx hf_meas.aestronglyMeasurable hf_int
  calc
    ν[f | tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)] =ᵐ[ν]
        ν[f | exchangeableSequenceSigmaAlgebra] := by
          simpa using hCondEq.symm
    _ =ᵐ[ν] f := hExchEq

/-- Helper for Corollary 12.18: an almost-sure indicator representation of a measurable function
produces an almost-surely equal measurable event. -/
private theorem aeEq_indicator_yields_tailEvent
    {ν : Measure (ℕ → E)} {mTail : MeasurableSpace (ℕ → E)} {S : Set (ℕ → E)}
    {g : (ℕ → E) → ℝ} (hg_meas : Measurable[mTail] g)
    (hg : g =ᵐ[ν] S.indicator (fun _ ↦ (1 : ℝ))) :
    ∃ T : Set (ℕ → E), MeasurableSet[mTail] T ∧ S =ᵐ[ν] T := by
  let T : Set (ℕ → E) := {x | g x = 1}
  have hT : MeasurableSet[mTail] T := by
    -- Proof comment: a level set of an `mTail`-measurable real-valued function is measurable.
    simpa [T] using measurableSet_eq_fun hg_meas measurable_const
  refine ⟨T, hT, ?_⟩
  -- Proof comment: pointwise, the indicator identity says membership in `S` is equivalent to
  -- the condition `g = 1`.
  filter_upwards [hg] with x hx
  by_cases hxS : x ∈ S
  · have hxg : g x = 1 := by
      simpa [hxS] using hx
    exact propext ⟨(fun _ ↦ by simpa [T, hxg]), fun _ ↦ hxS⟩
  · have hxg : g x = 0 := by
      simpa [hxS] using hx
    have hxnotT : x ∉ T := by
      intro hxT
      have hImpossible : g x = 1 := by simpa [T] using hxT
      rw [hxg] at hImpossible
      norm_num at hImpossible
    exact propext ⟨fun hxMem ↦ False.elim (hxS hxMem), fun hxT ↦ False.elim (hxnotT hxT)⟩

/-- Corollary 12.18: on sequence space, every event in
`exchangeableSequenceSigmaAlgebra` agrees almost everywhere with a tail event. -/
private theorem exists_tail_event_ae_eq_of_mem_exchangeableSequenceSigmaAlgebra
    {ν : Measure (ℕ → E)} [IsFiniteMeasure ν]
    (hEval : IsExchangeable (Function.eval : ℕ → (ℕ → E) → E) ν) {S : Set (ℕ → E)}
    (hS : MeasurableSet[exchangeableSequenceSigmaAlgebra] S) :
    ∃ T : Set (ℕ → E),
      MeasurableSet[tailRandomVariableMeasurableSpace
        (Function.eval : ℕ → (ℕ → E) → E)] T ∧
      S =ᵐ[ν] T := by
  -- Route correction: the original monolithic proof timed out. The stable route is to isolate the
  -- `L¹` conditional-expectation bridge and the indicator-to-event extraction separately.
  let f : (ℕ → E) → ℝ := S.indicator (fun _ ↦ (1 : ℝ))
  let mTail : MeasurableSpace (ℕ → E) :=
    tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E)
  let g : (ℕ → E) → ℝ := ν[f | mTail]
  have hg_meas : Measurable[mTail] g := by
    -- Proof comment: conditional expectation is measurable with respect to its conditioning
    -- `σ`-algebra.
    simpa [g, mTail] using (stronglyMeasurable_condExp (μ := ν) (m := mTail) (f := f)).measurable
  have hg_eq_indicator : g =ᵐ[ν] f := by
    -- Proof comment: the previous helper gives the tail conditional expectation of the indicator
    -- itself.
    simpa [g, mTail, f] using
      tailCondexp_indicator_ae_eq_indicator_of_mem_exchangeableSequenceSigmaAlgebra
        (ν := ν) hEval hS
  exact aeEq_indicator_yields_tailEvent (ν := ν) (mTail := mTail) hg_meas hg_eq_indicator

/-
Corollary 12.18 is a `source-facing` event-level statement. Its owner abstractions are the Chapter
12 exchangeable `σ`-algebra `exchangeableSigmaAlgebra (Function.swap X)` and the Chapter 2 tail
`σ`-algebra `tailRandomVariableMeasurableSpace X`. The null-symmetric-difference reformulation is
kept only as a `bridge/view` companion via the canonical mathlib theorem
`measure_symmDiff_eq_zero_iff`.
-/

-- Proof sketch: apply Theorem 12.17 to the indicators of finite-cylinder approximations of `A`
-- to obtain a `tailRandomVariableMeasurableSpace X`-measurable version of `𝟙_A`; then realize
-- that version as the indicator of a tail event `B`, which gives `A =ᵐ[μ] B`.
/-- Source-facing reformulation of Corollary 12.18: for an exchangeable sequence, every event in
the exchangeable
`σ`-algebra over a finite measure space agrees up to a null set with an event in the tail
`σ`-algebra. -/
theorem exists_tail_measurableSet_ae_eq_of_mem_exchangeableSigmaAlgebra
    {X : ℕ → Ω → E} (hX : IsExchangeable X μ) {A : Set Ω}
    (hA : MeasurableSet[exchangeableSigmaAlgebra (Function.swap X)] A) :
    ∃ B : Set Ω, MeasurableSet[tailRandomVariableMeasurableSpace X] B ∧ A =ᵐ[μ] B := by
  rcases (MeasurableSpace.measurableSet_comap.mp hA) with ⟨S, hS, rfl⟩
  -- Proof comment: first solve the event-level problem on sequence space for the law of the
  -- sample-sequence map.
  rcases exists_tail_event_ae_eq_of_mem_exchangeableSequenceSigmaAlgebra
      (ν := μ.map (Function.swap X))
      (coordinateProcess_isExchangeable_map_swap (μ := μ) (X := X) hX) hS with
    ⟨T, hT, hST⟩
  refine ⟨(Function.swap X) ⁻¹' T, ?_, ?_⟩
  · -- Proof comment: pull the tail event on sequence space back to a tail event for `X`.
    exact measurableSet_preimage_of_coordinateTail (X := X) hT
  · -- Proof comment: transport the almost-everywhere event equality back from the pushforward
    -- law of `Function.swap X` to the original measure.
    have hpre :
        (Function.swap X) ⁻¹' S =ᵐ[μ] (Function.swap X) ⁻¹' T :=
      ae_of_ae_map
        (aemeasurableProcessSwap_of_isExchangeable (μ := μ) (X := X) hX) hST
    simpa using hpre

-- Proof sketch: this is the measure-theoretic reformulation of
-- `exists_tail_measurableSet_ae_eq_of_mem_exchangeableSigmaAlgebra` via
-- `measure_symmDiff_eq_zero_iff`.
/-- Bridge companion to Corollary 12.18: the canonical almost-everywhere event equality can be
rewritten as vanishing symmetric-difference measure. -/
theorem exists_tail_measurableSet_symmDiff_null_of_mem_exchangeableSigmaAlgebra
    {X : ℕ → Ω → E} (hX : IsExchangeable X μ) {A : Set Ω}
    (hA : MeasurableSet[exchangeableSigmaAlgebra (Function.swap X)] A) :
    ∃ B : Set Ω, MeasurableSet[tailRandomVariableMeasurableSpace X] B ∧ μ (A ∆ B) = 0 := by
  rcases exists_tail_measurableSet_ae_eq_of_mem_exchangeableSigmaAlgebra hX hA with
    ⟨B, hB, hAB⟩
  exact ⟨B, hB, measure_symmDiff_eq_zero_iff.mpr hAB⟩
