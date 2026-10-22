/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_22

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A complex-valued function on `ℝ^d` is partially continuous at `0` if its restriction to each
coordinate axis is continuous at the origin. -/
def PartiallyContinuousAtZero (f : E → ℂ) : Prop :=
  ∀ i : Fin d, ContinuousAt (fun t : ℝ ↦ f (EuclideanSpace.single i t)) 0

-- Proof sketch: unfold `PartiallyContinuousAtZero`; one of its coordinate-axis continuity clauses
-- is exactly the desired statement.
/-- Partial continuity at `0` yields continuity along each coordinate axis through the origin. -/
theorem PartiallyContinuousAtZero.continuousAt_coordinate
    {f : E → ℂ} (hf : PartiallyContinuousAtZero f) (i : Fin d) :
    ContinuousAt (fun t : ℝ ↦ f (EuclideanSpace.single i t)) 0 :=
  hf i

/-- Helper for Theorem 15.23: the `i`th coordinate projection on `ℝ^d` is almost everywhere
measurable for every probability law. -/
lemma coordinateAEMeasurable (μ : ProbabilityMeasure E) (i : Fin d) :
    AEMeasurable (fun x : E ↦ x i) (μ : Measure E) := by
  -- Proof comment: coordinate evaluation is continuous on Euclidean space, hence measurable.
  have hcont : Continuous (fun x : E ↦ x i) := by
    fun_prop
  exact hcont.aemeasurable

/-- Helper for Theorem 15.23: the `i`th coordinate marginal law of a probability measure on
`ℝ^d`. -/
noncomputable def coordinateLaw (μ : ProbabilityMeasure E) (i : Fin d) : ProbabilityMeasure ℝ :=
  μ.map (coordinateAEMeasurable μ i)

/-- Helper for Theorem 15.23: the characteristic function of the `i`th coordinate marginal is the
ambient characteristic function restricted to the `i`th coordinate axis. -/
lemma charFun_coordinateLaw_eq (μ : ProbabilityMeasure E) (i : Fin d) (u : ℝ) :
    charFun (coordinateLaw μ i : Measure ℝ) u =
      charFun (μ : Measure E) (EuclideanSpace.single i u) := by
  -- Proof comment: normalize the left-hand side to the underlying `Measure.map`, then evaluate
  -- the ambient inner product against the inserted coordinate axis vector.
  change charFun (Measure.map (fun x : E ↦ x i) (μ : Measure E)) u = _
  rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply,
    MeasureTheory.integral_map (coordinateAEMeasurable μ i) (by fun_prop)]
  congr with x
  congr 1
  have hinner : inner ℝ x (EuclideanSpace.single i u) = u * x i := by
    simpa using (EuclideanSpace.inner_single_right (i := i) u x)
  exact congrArg (fun z : ℂ ↦ z * Complex.I) (by exact_mod_cast hinner.symm)

/-- Helper for Theorem 15.23: the coordinate marginal of `μ` measures the coordinate tail event in
the same way as `μ` itself. -/
lemma measure_coordinateLaw_norm_gt_eq (μ : ProbabilityMeasure E) (i : Fin d) (r : ℝ) :
    (coordinateLaw μ i : Measure ℝ) {x : ℝ | r < ‖x‖} =
      (μ : Measure E) {x : E | r < ‖x i‖} := by
  -- Proof comment: apply the defining pushforward formula to the coordinate tail event.
  have htail : MeasurableSet {x : ℝ | r < ‖x‖} := by
    simpa using (isOpen_lt continuous_const continuous_norm).measurableSet
  simpa [coordinateLaw] using
    (ProbabilityMeasure.map_apply' μ (coordinateAEMeasurable μ i) htail)

/-- Helper for Theorem 15.23: the coordinate marginal tail event matches the corresponding
basis-direction tail event in `ℝ^d`. -/
lemma coordinateLaw_tail_eq_basisTail (μ : ProbabilityMeasure E) (i : Fin d) (r : ℝ) :
    (coordinateLaw μ i : Measure ℝ) {x : ℝ | r < ‖x‖} =
      (μ : Measure E) {x : E | r < ‖inner ℝ (EuclideanSpace.single i (1 : ℝ)) x‖} := by
  -- Proof comment: first rewrite the marginal tail by pushforward, then identify the basis inner
  -- product with the `i`th coordinate.
  rw [measure_coordinateLaw_norm_gt_eq]
  congr 1
  ext x
  have hcoord :
      inner ℝ (EuclideanSpace.single i (1 : ℝ)) x = x i := by
    simpa using (EuclideanSpace.inner_single_left (i := i) (1 : ℝ) x)
  simp [hcoord]

/-- Helper for Theorem 15.23: coercing a sequence of probability measures to measures preserves its
range. -/
lemma probabilityMeasure_image_range_eq (Ps : ℕ → ProbabilityMeasure E) :
    (((↑) : ProbabilityMeasure E → Measure E) '' Set.range Ps) =
      Set.range (fun n ↦ ((Ps n : ProbabilityMeasure E) : Measure E)) := by
  ext μ
  constructor
  · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨Ps n, ⟨n, rfl⟩, rfl⟩

/-- Helper for Theorem 15.23: partial continuity of the pointwise characteristic-function limit
makes each coordinate marginal family tight. -/
lemma coordinateLaw_isTightMeasureSet
    (Ps : ℕ → ProbabilityMeasure E) {f : E → ℂ}
    (hφ : ∀ t : E,
      Tendsto (fun n ↦ charFun (Ps n) t) atTop (𝓝 (f t)))
    (hf : PartiallyContinuousAtZero f) (i : Fin d) :
    IsTightMeasureSet (Set.range fun n ↦ (coordinateLaw (Ps n) i : Measure ℝ)) := by
  -- Proof comment: the `i`th marginal characteristic functions converge to the coordinate-axis
  -- restriction of `f`, so the one-dimensional Lévy tightness theorem applies.
  refine isTightMeasureSet_of_tendsto_charFun (hf.continuousAt_coordinate i) ?_
  intro u
  simpa [charFun_coordinateLaw_eq] using hφ (EuclideanSpace.single i u)

/-- Helper for Theorem 15.23: tight coordinate marginals control the tails in the corresponding
orthonormal basis direction. -/
lemma tendsto_basisFun_tail_of_coordinateLaw_isTight
    (Ps : ℕ → ProbabilityMeasure E) (i : Fin d)
    (hcoord_tight : IsTightMeasureSet (Set.range fun n ↦ (coordinateLaw (Ps n) i : Measure ℝ))) :
    Tendsto
      (fun r : ℝ ↦
        ⨆ μ ∈ Set.range fun n ↦ (Ps n : Measure E),
          μ {x : E | r < ‖inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) x‖})
      atTop (𝓝 0) := by
  have htail :
      Tendsto
        (fun r : ℝ ↦
          ⨆ ν ∈ Set.range fun n ↦ (coordinateLaw (Ps n) i : Measure ℝ),
            ν {x : ℝ | r < ‖x‖})
        atTop (𝓝 0) :=
    (isTightMeasureSet_iff_tendsto_measure_norm_gt
      (S := Set.range fun n ↦ (coordinateLaw (Ps n) i : Measure ℝ))).1 hcoord_tight
  have htailCoord :
      Tendsto
        (fun r : ℝ ↦
          ⨆ n, (coordinateLaw (Ps n) i : Measure ℝ) {x : ℝ | r < ‖x‖})
        atTop (𝓝 0) := by
    -- Proof comment: first rewrite the supremum over the range set as a supremum over indices.
    simpa only [iSup_range] using htail
  have htailSingle :
      Tendsto
        (fun r : ℝ ↦
          ⨆ n, (Ps n : Measure E)
            {x : E | r < ‖inner ℝ (EuclideanSpace.single i (1 : ℝ)) x‖})
        atTop (𝓝 0) := by
    -- Proof comment: then transport the coordinate marginal tail back to the `single i 1`
    -- direction in `ℝ^d`.
    have hcoordToSingleEq :
        (fun r : ℝ ↦
          ⨆ n, (coordinateLaw (Ps n) i : Measure ℝ) {x : ℝ | r < ‖x‖}) =
          (fun r : ℝ ↦
            ⨆ n, (Ps n : Measure E)
              {x : E | r < ‖inner ℝ (EuclideanSpace.single i (1 : ℝ)) x‖}) := by
      funext r
      exact iSup_congr fun n ↦ coordinateLaw_tail_eq_basisTail (μ := Ps n) (i := i) (r := r)
    rw [← hcoordToSingleEq]
    exact htailCoord
  have htailBasisFun :
      Tendsto
        (fun r : ℝ ↦
          ⨆ n, (Ps n : Measure E)
            {x : E | r < ‖inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) x‖})
        atTop (𝓝 0) := by
    -- Proof comment: finally rewrite `single i 1` into the orthonormal-basis spelling used by the
    -- tightness API.
    have hsingleToBasis :
        (fun r : ℝ ↦
          ⨆ n, (Ps n : Measure E)
            {x : E | r < ‖inner ℝ (EuclideanSpace.single i (1 : ℝ)) x‖}) =
          (fun r : ℝ ↦
            ⨆ n, (Ps n : Measure E)
              {x : E | r < ‖inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) x‖}) := by
      funext r
      exact iSup_congr fun n ↦ by
        simp [EuclideanSpace.basisFun_apply]
    rw [← hsingleToBasis]
    exact htailSingle
  -- Proof comment: convert the indexed supremum back to the range-set form expected by the
  -- finite-dimensional tightness criterion.
  simpa only [iSup_range] using htailBasisFun

/-- Helper for Theorem 15.23: a pointwise characteristic-function limit that is partially
continuous at `0` forces tightness of the full family on `ℝ^d`. -/
lemma isTightMeasureSet_range_of_partiallyContinuousAtZero
    (Ps : ℕ → ProbabilityMeasure E) {f : E → ℂ}
    (hφ : ∀ t : E,
      Tendsto (fun n ↦ charFun (Ps n) t) atTop (𝓝 (f t)))
    (hf : PartiallyContinuousAtZero f) :
    IsTightMeasureSet (Set.range fun n ↦ (Ps n : Measure E)) := by
  -- Proof comment: tightness of each one-dimensional coordinate marginal upgrades to tightness in
  -- finite-dimensional Euclidean space by the basis-direction criterion.
  refine isTightMeasureSet_of_forall_basis_tendsto (b := EuclideanSpace.basisFun (Fin d) ℝ) ?_
  intro i
  exact tendsto_basisFun_tail_of_coordinateLaw_isTight Ps i
    (coordinateLaw_isTightMeasureSet Ps hφ hf i)

-- Proof sketch: use tightness of the weakly convergent sequence of probability measures, apply the
-- equicontinuity criterion for characteristic functions from Theorem 15.21, and then combine
-- pointwise convergence with equicontinuity via Lemma 15.22 to upgrade to uniform convergence on
-- each compact set.
/-- Part (1) of Theorem 15.23: if probability measures on `ℝ^d` converge weakly to `P`, then their
characteristic functions converge to `charFun P` uniformly on every compact set. -/
theorem charFun_tendstoUniformlyOn_of_tendsto
    {P : ProbabilityMeasure E} {Ps : ℕ → ProbabilityMeasure E}
    (hP : Tendsto Ps atTop (𝓝 P)) :
    ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun n t ↦ charFun (Ps n) t) (charFun P) atTop K := by
  let F : ℕ → E → ℂ := fun n t ↦ charFun (Ps n : Measure E) t
  have h_pointwise :
      ∀ t : E, Tendsto (fun n ↦ charFun (Ps n) t) atTop (𝓝 (charFun P t)) := by
    exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hP
  have h_charFunP_cont : ContinuousAt (charFun (P : Measure E)) 0 := by
    fun_prop
  have h_pointwise_measure :
      ∀ t : E,
        Tendsto (fun n ↦ charFun (((Ps n : ProbabilityMeasure E) : Measure E)) t) atTop
          (𝓝 (charFun (P : Measure E) t)) := by
    simpa using h_pointwise
  have h_tight_range :
      IsTightMeasureSet (Set.range fun n ↦ ((Ps n : ProbabilityMeasure E) : Measure E)) := by
    exact isTightMeasureSet_of_tendsto_charFun h_charFunP_cont h_pointwise_measure
  have h_tight :
      IsTightMeasureSet (((↑) : ProbabilityMeasure E → Measure E) '' Set.range Ps) := by
    rw [probabilityMeasure_image_range_eq]
    exact h_tight_range
  have h_charFuns :
      charFun '' (((↑) : ProbabilityMeasure E → Measure E) '' Set.range Ps) = Set.range F := by
    ext φ
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      rcases hμ with ⟨ν, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(Ps n : Measure E), ⟨Ps n, ⟨n, rfl⟩, rfl⟩, rfl⟩
  have h_eqcont_set : (Set.range F).UniformEquicontinuous := by
    rw [← h_charFuns]
    exact
      tight_probabilityMeasureFamily_charFunSet_uniformEquicontinuous (Set.range Ps) h_tight
  have h_eqcont_range : UniformEquicontinuous ((↑) : Set.range F → E → ℂ) := h_eqcont_set
  have h_eqcont : UniformEquicontinuous F :=
    (uniformEquicontinuous_iff_range.2 h_eqcont_range)
  intro K hK
  let 𝔖 : Set (Set E) := {K}
  have h𝔖 : ⋃₀ 𝔖 = K := by
    simp [𝔖]
  have h_uniform :
      Tendsto (UniformOnFun.ofFun 𝔖 ∘ F) atTop
        (𝓝 <| UniformOnFun.ofFun 𝔖 (charFun (P : Measure E))) := by
    refine
      (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' ?_ ?_ atTop
        (charFun (P : Measure E))).2 ?_
    · intro L hL
      rcases Set.mem_singleton_iff.mp hL with rfl
      simpa using hK
    · intro L hL
      exact (h_eqcont.uniformEquicontinuousOn L).equicontinuousOn
    · rw [h𝔖]
      rw [tendsto_pi_nhds]
      intro x
      simpa [F] using h_pointwise x
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at h_uniform
  simpa [F, 𝔖] using h_uniform K (by simp [𝔖])

-- Proof sketch: first use the coordinate-axis continuity assumption to apply the one-dimensional
-- tightness argument to each marginal and deduce tightness of the sequence on `ℝ^d`. Then extract
-- a weak limit by Prokhorov compactness, identify its characteristic function with `f` by
-- pointwise convergence and Lévy's characterization theorem, and conclude that the whole sequence
-- converges weakly to that probability measure.
/-- Theorem 15.23 (2): if the characteristic functions of `Ps n` converge pointwise to a function
`f` that is partially continuous at `0`, then `f` is the characteristic function of a probability
measure `Q` and `Ps` converges weakly to `Q`. -/
theorem exists_probabilityMeasure_of_tendsto_charFun
    (Ps : ℕ → ProbabilityMeasure E) {f : E → ℂ}
    (hφ : ∀ t : E,
      Tendsto (fun n ↦ charFun (Ps n) t) atTop (𝓝 (f t)))
    (hf : PartiallyContinuousAtZero f) :
    ∃ Q : ProbabilityMeasure E, (∀ t : E, charFun Q t = f t) ∧ Tendsto Ps atTop (𝓝 Q) := by
  -- Proof comment: use tightness to obtain a convergent subsequence, identify its limit by the
  -- common characteristic-function limit, and then invoke Lévy's convergence criterion.
  have h_tight_range : IsTightMeasureSet (Set.range fun n ↦ (Ps n : Measure E)) :=
    isTightMeasureSet_range_of_partiallyContinuousAtZero Ps hφ hf
  have h_tight :
      IsTightMeasureSet (((↑) : ProbabilityMeasure E → Measure E) '' Set.range Ps) := by
    rw [probabilityMeasure_image_range_eq]
    exact h_tight_range
  have hcomp : IsCompact (closure (Set.range Ps)) :=
    isCompact_closure_of_isTightMeasureSet (S := Set.range Ps) h_tight
  -- Proof comment: compact closure gives one convergent subsequence; its limit is forced by the
  -- common pointwise characteristic-function limit.
  obtain ⟨Q, _hQmem, φ, hφmono, hφtendsto⟩ :=
    hcomp.tendsto_subseq (fun n ↦ subset_closure ⟨n, rfl⟩)
  have hcharQ : ∀ t : E, charFun Q t = f t := by
    intro t
    have hQt :
        Tendsto (fun n ↦ charFun (Ps (φ n)) t) atTop (𝓝 (charFun Q t)) :=
      (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hφtendsto) t
    have hft : Tendsto (fun n ↦ charFun (Ps (φ n)) t) atTop (𝓝 (f t)) :=
      (hφ t).comp hφmono.tendsto_atTop
    exact tendsto_nhds_unique hQt hft
  refine ⟨Q, hcharQ, ?_⟩
  have hcharToQ : ∀ t : E, Tendsto (fun n ↦ charFun (Ps n) t) atTop (𝓝 (charFun Q t)) := by
    -- Proof comment: the original pointwise limit becomes a limit to `charFun Q` after the
    -- subsequence identification step.
    intro t
    simpa [hcharQ t] using hφ t
  exact ProbabilityMeasure.tendsto_of_tendsto_charFun hcharToQ

end
