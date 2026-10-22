/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6.DyadicGeometry

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Helper for Theorem 21.6: almost-sure convergence of a dyadic extension identifies it with the
original process once the same approximants also converge in measure to the original path value. -/
lemma aeEq_original_of_dyadicExtension
    {X Y : NNReal → Ω → ℝ} {t : NNReal} {d : ℕ → NNReal}
    (hd_meas : ∀ n, AEStronglyMeasurable (fun ω ↦ X (d n) ω) μ)
    (hd_ae :
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ X (d n) ω) Filter.atTop (nhds (Y t ω)))
    (hd_measure :
      TendstoInMeasure μ (fun n ω ↦ X (d n) ω) Filter.atTop (fun ω ↦ X t ω)) :
    X t =ᵐ[μ] Y t := by
  -- Proof comment: the same dyadic approximation sequence converges in measure to both `X t` and
  -- `Y t`, so uniqueness of the limit in measure forces almost-sure equality.
  have hY_measure :
      TendstoInMeasure μ (fun n ω ↦ X (d n) ω) Filter.atTop (fun ω ↦ Y t ω) :=
    tendstoInMeasure_of_tendsto_ae hd_meas hd_ae
  simpa using tendstoInMeasure_ae_unique hd_measure hY_measure

/-- Helper for Theorem 21.6: summable real-valued event masses imply almost-sure eventual
avoidance by the first Borel--Cantelli lemma. -/
lemma ae_eventually_notMem_of_summable_measureReal
    {s : ℕ → Set Ω}
    (hs : Summable (fun n : ℕ ↦ (μ (s n)).toReal)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, ω ∉ s n := by
  have htsum : (∑' n : ℕ, μ (s n)) ≠ ∞ := by
    -- Proof comment: summability of the real-valued masses upgrades to finiteness of the
    -- `ENNReal` series because every set under a probability measure has finite mass.
    simpa [ENNReal.ofReal_toReal, measure_ne_top] using hs.tsum_ofReal_ne_top
  exact MeasureTheory.ae_eventually_notMem htsum

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.6: convert the ENNReal Markov estimate for a real-valued increment into
the final `measureReal` bound on the strict distance superlevel set. -/
lemma dyadicMarkovMeasureReal_le
    {Y Z : Ω → ℝ} {α δ M : ℝ}
    (hα : 0 < α)
    (hδ : 0 < δ)
    (hM : 0 ≤ M)
    (hmeas : AEMeasurable (fun ω ↦ edist (Y ω) (Z ω) ^ α) μ)
    (hlintegral : ∫⁻ ω, edist (Y ω) (Z ω) ^ α ∂μ ≤ ENNReal.ofReal M) :
    μ.real {ω | δ < dist (Y ω) (Z ω)} ≤ M / δ ^ α := by
  have hδpow_pos : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
  have hδpow_ne0 : ENNReal.ofReal (δ ^ α) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr hδpow_pos).ne'
  have hstrict_subset :
      {ω | δ < dist (Y ω) (Z ω)} ⊆
        {ω | ENNReal.ofReal (δ ^ α) ≤ edist (Y ω) (Z ω) ^ α} := by
    intro ω hω
    -- Proof comment: the strict real threshold becomes the usual ENNReal Markov threshold after
    -- raising both sides to the positive exponent `α`.
    have hωpow : δ ^ α ≤ dist (Y ω) (Z ω) ^ α :=
      Real.rpow_le_rpow hδ.le hω.le hα.le
    simpa [Set.mem_setOf_eq, edist_dist, ENNReal.ofReal_rpow_of_nonneg hδ.le hα.le,
      ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist (Y ω) (Z ω)) hα.le] using
      ENNReal.ofReal_le_ofReal hωpow
  have hmarkov :
      μ {ω | ENNReal.ofReal (δ ^ α) ≤ edist (Y ω) (Z ω) ^ α} ≤
        (∫⁻ ω, edist (Y ω) (Z ω) ^ α ∂μ) / ENNReal.ofReal (δ ^ α) :=
    MeasureTheory.meas_ge_le_lintegral_div hmeas hδpow_ne0 ENNReal.ofReal_ne_top
  have hμ :
      μ {ω | δ < dist (Y ω) (Z ω)} ≤ ENNReal.ofReal (M / δ ^ α) := by
    calc
      μ {ω | δ < dist (Y ω) (Z ω)} ≤
          μ {ω | ENNReal.ofReal (δ ^ α) ≤ edist (Y ω) (Z ω) ^ α} :=
        measure_mono hstrict_subset
      _ ≤ (∫⁻ ω, edist (Y ω) (Z ω) ^ α ∂μ) / ENNReal.ofReal (δ ^ α) := hmarkov
      _ ≤ ENNReal.ofReal M / ENNReal.ofReal (δ ^ α) := by
        simpa using ENNReal.div_le_div_right hlintegral (ENNReal.ofReal (δ ^ α))
      _ = ENNReal.ofReal (M / δ ^ α) := by
            rw [ENNReal.ofReal_div_of_pos hδpow_pos]
  -- Proof comment: only after the ENNReal expression is normalized do we convert the estimate to
  -- the real-valued `measureReal` statement.
  have hdiv_nonneg : 0 ≤ M / δ ^ α := by
    positivity
  exact ENNReal.toReal_le_of_le_ofReal hdiv_nonneg hμ

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.6: for each fixed `t ≤ T`, the clipped dyadic approximant at level `n`
satisfies the Kolmogorov moment bound in real-valued tail-probability form. -/
lemma measureReal_clippedDyadicApprox_dist_ge_le
    {X : NNReal → Ω → ℝ} {T α β C : ℝ≥0} {t : NNReal} {n : ℕ} {ε : ℝ}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (htT : t ≤ T)
    (hε : 0 < ε) :
    μ.real {ω | ε ≤ dist (X (clippedDyadicApprox T t n) ω) (X t ω)} ≤
      C * dist (clippedDyadicApprox T t n) t ^ (1 + (β : ℝ)) / ε ^ (α : ℝ) := by
  let s := clippedDyadicApprox T t n
  have hs_mem : s ∈ Set.Icc (0 : NNReal) T := clippedDyadicApprox_mem_Icc T t n
  have ht_mem : t ∈ Set.Icc (0 : NNReal) T := by
    simpa using htT
  have hαpos : 0 < (α : ℝ) := by
    exact_mod_cast h.alpha_pos
  have hβpow_pos : 0 < 1 + (β : ℝ) := by
    have hβpos : 0 < (β : ℝ) := by
      exact_mod_cast h.beta_pos
    linarith
  have hεpow_pos : 0 < ε ^ (α : ℝ) := Real.rpow_pos_of_pos hε (α : ℝ)
  have hεpow_ne0 : ENNReal.ofReal (ε ^ (α : ℝ)) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr hεpow_pos).ne'
  have hsubset :
      {ω | ε ≤ dist (X s ω) (X t ω)} ⊆
        {ω | ENNReal.ofReal (ε ^ (α : ℝ)) ≤ edist (X s ω) (X t ω) ^ (α : ℝ)} := by
    intro ω hω
    -- Proof comment: positivity of `α` lets us raise the threshold inequality to the power `α`.
    have hωpow : ε ^ (α : ℝ) ≤ dist (X s ω) (X t ω) ^ (α : ℝ) :=
      Real.rpow_le_rpow hε.le hω hαpos.le
    simpa [edist_dist, ENNReal.ofReal_rpow_of_nonneg hε.le hαpos.le,
      ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist (X s ω) (X t ω)) hαpos.le] using
      ENNReal.ofReal_le_ofReal hωpow
  have hmeas :
      AEMeasurable (fun ω ↦ edist (X s ω) (X t ω) ^ (α : ℝ)) μ := by
    -- Proof comment: fixed-time increment distances are measurable by the Kolmogorov process API.
    exact
      ((h.isKolmogorovProcess.measurable_edist
        (s := ⟨s, hs_mem⟩) (t := ⟨t, ht_mem⟩)).aemeasurable).pow_const (α : ℝ)
  have hmarkov :
      μ {ω | ENNReal.ofReal (ε ^ (α : ℝ)) ≤ edist (X s ω) (X t ω) ^ (α : ℝ)} ≤
        (∫⁻ ω, edist (X s ω) (X t ω) ^ (α : ℝ) ∂μ) / ENNReal.ofReal (ε ^ (α : ℝ)) :=
    MeasureTheory.meas_ge_le_lintegral_div hmeas hεpow_ne0 ENNReal.ofReal_ne_top
  have hlintegral :
      ∫⁻ ω, edist (X s ω) (X t ω) ^ (α : ℝ) ∂μ ≤
        ENNReal.ofReal (C * dist s t ^ (1 + (β : ℝ))) := by
    -- Proof comment: the finite-horizon increment estimate applies directly to the clipped time
    -- `s` because both times lie in `[0,T]`.
    calc
      ∫⁻ ω, edist (X s ω) (X t ω) ^ (α : ℝ) ∂μ
          ≤ (C : ℝ≥0∞) * edist s t ^ (1 + (β : ℝ)) := by
            simpa [edist_dist, dist_comm] using
              h.increment_lintegral_le (s := s) (t := t) hs_mem.2 htT
      _ = (C : ℝ≥0∞) * ENNReal.ofReal (dist s t ^ (1 + (β : ℝ))) := by
            rw [edist_dist,
              ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist s t) hβpow_pos.le]
      _ = ENNReal.ofReal (C * dist s t ^ (1 + (β : ℝ))) := by
            simp [ENNReal.ofReal_mul]
  have hμ :
      μ {ω | ε ≤ dist (X s ω) (X t ω)} ≤
        ENNReal.ofReal (C * dist s t ^ (1 + (β : ℝ)) / ε ^ (α : ℝ)) := by
    calc
      μ {ω | ε ≤ dist (X s ω) (X t ω)} ≤
          μ {ω | ENNReal.ofReal (ε ^ (α : ℝ)) ≤ edist (X s ω) (X t ω) ^ (α : ℝ)} :=
        measure_mono hsubset
      _ ≤ (∫⁻ ω, edist (X s ω) (X t ω) ^ (α : ℝ) ∂μ) / ENNReal.ofReal (ε ^ (α : ℝ)) := hmarkov
      _ ≤ ENNReal.ofReal (C * dist s t ^ (1 + (β : ℝ))) / ENNReal.ofReal (ε ^ (α : ℝ)) := by
        simpa using ENNReal.div_le_div_right hlintegral (ENNReal.ofReal (ε ^ (α : ℝ)))
      _ = ENNReal.ofReal (C * dist s t ^ (1 + (β : ℝ)) / ε ^ (α : ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos hεpow_pos]
  -- Proof comment: after normalizing the ENNReal Markov estimate, convert the result to
  -- `measureReal`.
  have hbound_nonneg : 0 ≤ C * dist s t ^ (1 + (β : ℝ)) / ε ^ (α : ℝ) := by
    positivity
  simpa [s] using ENNReal.toReal_le_of_le_ofReal hbound_nonneg hμ

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.6: a single adjacent dyadic-row increment exceeds the threshold
`2^{-q n}` with probability controlled by Markov's inequality and the Kolmogorov moment bound. -/
lemma measureReal_dyadicAdjacentIncrement_gt_threshold_le
    {X : NNReal → Ω → ℝ} {T α β C q : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    {n k : ℕ} (_hk : k < dyadicCutoff T n) :
    μ.real
      {ω | dyadicStepThreshold q n <
        dist (X (dyadicPointUpTo T n (k + 1)) ω) (X (dyadicPointUpTo T n k) ω)} ≤
      C * (((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ))) /
        ((dyadicStepThreshold q n) ^ (α : ℝ)) := by
  let s := dyadicPointUpTo T n k
  let t := dyadicPointUpTo T n (k + 1)
  let M : ℝ := C * (((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ)))
  have hs : s ∈ Set.Icc (0 : NNReal) T := by
    simpa [s] using dyadicPointUpTo_mem_Icc T n k
  have ht : t ∈ Set.Icc (0 : NNReal) T := by
    simpa [t] using dyadicPointUpTo_mem_Icc T n (k + 1)
  have hαpos : 0 < (α : ℝ) := by
    exact_mod_cast h.alpha_pos
  have hβpow_pos : 0 < 1 + (β : ℝ) := by
    have hβpos : 0 < (β : ℝ) := by
      exact_mod_cast h.beta_pos
    linarith
  have hδpos : 0 < dyadicStepThreshold q n := by
    unfold dyadicStepThreshold
    positivity
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hmeas :
      AEMeasurable (fun ω ↦ edist (X t ω) (X s ω) ^ (α : ℝ)) μ := by
    -- Proof comment: measurability comes from the owner API for fixed increments on `[0,T]`.
    exact
      ((h.isKolmogorovProcess.measurable_edist
        (s := ⟨t, ht⟩) (t := ⟨s, hs⟩)).aemeasurable).pow_const (α : ℝ)
  have hmesh :
      edist t s ^ (1 + (β : ℝ)) ≤
        ENNReal.ofReal ((((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ)))) := by
    have hdist : dist t s ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
      simpa [s, t, dist_comm] using dist_dyadicPointUpTo_succ_le_mesh T n k
    have hdist_enn :
        edist t s ≤ ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ n) := by
      simpa [edist_dist] using ENNReal.ofReal_le_ofReal hdist
    have hpow :
        edist t s ^ (1 + (β : ℝ)) ≤
          (ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ n)) ^ (1 + (β : ℝ)) :=
      ENNReal.rpow_le_rpow hdist_enn hβpow_pos.le
    calc
      edist t s ^ (1 + (β : ℝ))
          ≤ (ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ n)) ^ (1 + (β : ℝ)) := hpow
      _ = ENNReal.ofReal (((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ))) := by
            rw [ENNReal.ofReal_rpow_of_nonneg
              (by positivity : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ n) hβpow_pos.le]
  have hlintegral :
      ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤ ENNReal.ofReal M := by
    calc
      ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ
          ≤ (C : ℝ≥0∞) * edist t s ^ (1 + (β : ℝ)) := by
            simpa [s, t] using h.increment_lintegral_le (s := s) (t := t) hs.2 ht.2
      _ ≤ (C : ℝ≥0∞) *
            ENNReal.ofReal ((((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ)))) := by
              gcongr
      _ = ENNReal.ofReal M := by
            simp [M, ENNReal.ofReal_mul]
  -- Proof comment: the adjacent-edge estimate is now a direct application of the extracted
  -- Markov bridge.
  simpa [s, t, M, dist_comm] using
    dyadicMarkovMeasureReal_le
      (μ := μ)
      (Y := fun ω ↦ X t ω)
      (Z := fun ω ↦ X s ω)
      (α := α)
      (δ := dyadicStepThreshold q n)
      (M := M)
      hαpos
      hδpos
      hM_nonneg
      hmeas
      hlintegral

/-- Helper for Theorem 21.6: the bad event on a whole dyadic row is bounded by summing the
adjacent-edge Markov estimates over the finitely many clipped row edges. -/
lemma measureReal_dyadicRowBadEvent_le_unionBound
    {X : NNReal → Ω → ℝ} {T α β C q : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (n : ℕ) :
    μ.real (dyadicRowBadEvent (X := X) T q n) ≤
      (Finset.range (dyadicCutoff T n)).sum (fun _ ↦
        C * (((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ))) /
          ((dyadicStepThreshold q n) ^ (α : ℝ))) := by
  let edgeEvent : ℕ → Set Ω := fun k ↦
    {ω | dyadicStepThreshold q n <
      dist (X (dyadicPointUpTo T n (k + 1)) ω) (X (dyadicPointUpTo T n k) ω)}
  have hunion :
      dyadicRowBadEvent (X := X) T q n = ⋃ k ∈ Finset.range (dyadicCutoff T n), edgeEvent k := by
    ext ω
    simp [dyadicRowBadEvent, edgeEvent]
  -- Proof comment: summing the finitely many adjacent-edge bad events gives the whole row-bad
  -- event.
  rw [hunion]
  calc
    μ.real (⋃ k ∈ Finset.range (dyadicCutoff T n), edgeEvent k)
        ≤ ∑ k ∈ Finset.range (dyadicCutoff T n), μ.real (edgeEvent k) :=
          MeasureTheory.measureReal_biUnion_finset_le (Finset.range (dyadicCutoff T n)) edgeEvent
    _ ≤ ∑ k ∈ Finset.range (dyadicCutoff T n),
          C * (((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ))) /
            ((dyadicStepThreshold q n) ^ (α : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro k hk_range
          exact measureReal_dyadicAdjacentIncrement_gt_threshold_le
            (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q)
            h (_hk := Finset.mem_range.mp hk_range)

/-- Helper for Theorem 21.6: the dyadic step threshold is the geometric ratio
`((2 : ℝ) ^ (-(q : ℝ))) ^ n`. -/
lemma dyadicStepThreshold_eq_geomRatio_pow
    (q : ℝ≥0) (n : ℕ) :
    dyadicStepThreshold q n = ((2 : ℝ) ^ (-(q : ℝ))) ^ n := by
  -- Proof comment: rewrite the row threshold `2^{-q n}` as a genuine geometric sequence in `n`.
  calc
    dyadicStepThreshold q n = (2 : ℝ) ^ (-((q : ℝ) * n)) := rfl
    _ = (2 : ℝ) ^ ((-(q : ℝ)) * n) := by congr 1; ring
    _ = ((2 : ℝ) ^ (-(q : ℝ))) ^ n := by
          rw [← Real.rpow_natCast, Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]

/-- Helper for Theorem 21.6: the dyadic mesh `2^{-n}` is the power `(1 / 2)^n`. -/
lemma dyadicMesh_eq_halfPow (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℝ)) = (1 / 2 : ℝ) ^ n := by
  -- Proof comment: convert the negative real power into an inverse and then back into a nat power.
  rw [Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ))]
  rw [Real.rpow_natCast]
  simp [one_div]

/-- Helper for Theorem 21.6: the `q`-geometric row threshold equals the `q`-th power of the
dyadic mesh. -/
lemma dyadicStepThreshold_eq_meshRpow
    (q : ℝ≥0) (n : ℕ) :
    dyadicStepThreshold q n = ((1 / 2 : ℝ) ^ n) ^ (q : ℝ) := by
  -- Proof comment: both sides are `2^{-q n}` written once as a geometric sequence in the row
  -- threshold and once as the `q`-th power of the dyadic mesh.
  calc
    dyadicStepThreshold q n = ((2 : ℝ) ^ (-(q : ℝ))) ^ n := dyadicStepThreshold_eq_geomRatio_pow q n
    _ = (2 : ℝ) ^ ((-(q : ℝ)) * n) := by
          rw [← Real.rpow_natCast, Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
    _ = (2 : ℝ) ^ ((-(n : ℝ)) * (q : ℝ)) := by congr 1; ring
    _ = ((2 : ℝ) ^ (-(n : ℝ))) ^ (q : ℝ) := by
          rw [← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
    _ = ((1 / 2 : ℝ) ^ n) ^ (q : ℝ) := by rw [dyadicMesh_eq_halfPow]

/-- Helper for Theorem 21.6: the bad-row probability decays geometrically once the admissible gap
`β - α q` is positive. -/
lemma measureReal_dyadicRowBadEvent_le_geometric
    {X : NNReal → Ω → ℝ} {T α β C q : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (_hgap : 0 < (β : ℝ) - (α : ℝ) * q)
    (n : ℕ) :
    μ.real (dyadicRowBadEvent (X := X) T q n) ≤
      ((Nat.ceil (T : ℝ) : ℝ) * C) * ((2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))) ^ n := by
  let mesh : ℝ := (1 : ℝ) / (2 : ℝ) ^ n
  let threshold : ℝ := dyadicStepThreshold q n
  have hbase :
      μ.real (dyadicRowBadEvent (X := X) T q n) ≤
        (dyadicCutoff T n : ℝ) *
          (C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))) := by
    calc
      μ.real (dyadicRowBadEvent (X := X) T q n)
          ≤ (Finset.range (dyadicCutoff T n)).sum (fun _ ↦
              C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))) := by
            simpa [mesh, threshold] using
              measureReal_dyadicRowBadEvent_le_unionBound
                (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q) h n
      _ = (dyadicCutoff T n : ℝ) *
            (C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))) := by
            simp
  have hmesh_eq :
      mesh = (2 : ℝ) ^ (-(n : ℝ)) := by
    calc
      mesh = (1 / 2 : ℝ) ^ n := by
        dsimp [mesh]
        simp [one_div]
      _ = (2 : ℝ) ^ (-(n : ℝ)) := by
        rw [dyadicMesh_eq_halfPow]
  have hratio :
      C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ)) =
        C * ((2 : ℝ) ^ ((α : ℝ) * q - (1 + (β : ℝ)))) ^ n := by
    have hthreshold_eq :
        threshold = (2 : ℝ) ^ (-((q : ℝ) * n)) := by
      rfl
    have hnum :
        mesh ^ (1 + (β : ℝ)) = (2 : ℝ) ^ ((-(n : ℝ)) * (1 + (β : ℝ))) := by
      rw [hmesh_eq, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
    have hden :
        threshold ^ (α : ℝ) = (2 : ℝ) ^ ((-((q : ℝ) * n)) * (α : ℝ)) := by
      rw [hthreshold_eq, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
    have hquot :
        mesh ^ (1 + (β : ℝ)) / (threshold ^ (α : ℝ)) =
          (2 : ℝ) ^ (((-(n : ℝ)) * (1 + (β : ℝ))) - ((-((q : ℝ) * n)) * (α : ℝ))) := by
      rw [hnum, hden, ← Real.rpow_sub zero_lt_two]
    calc
      C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))
          = C * (mesh ^ (1 + (β : ℝ)) / (threshold ^ (α : ℝ))) := by ring
      _ = C *
            (2 : ℝ) ^ (((-(n : ℝ)) * (1 + (β : ℝ))) - ((-((q : ℝ) * n)) * (α : ℝ))) := by
              rw [hquot]
      _ = C * (2 : ℝ) ^ (((α : ℝ) * q - (1 + (β : ℝ))) * n) := by
            congr 2
            ring
      _ = C * ((2 : ℝ) ^ ((α : ℝ) * q - (1 + (β : ℝ)))) ^ n := by
            rw [← Real.rpow_natCast, Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
  have hcutoff :
      (dyadicCutoff T n : ℝ) = (Nat.ceil (T : ℝ) : ℝ) * (2 : ℝ) ^ n := by
    unfold dyadicCutoff
    simp [Nat.cast_mul, Nat.cast_pow]
  have hfinal :
      (dyadicCutoff T n : ℝ) *
          (C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))) =
        ((Nat.ceil (T : ℝ) : ℝ) * C) * ((2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))) ^ n := by
    rw [hcutoff, hratio]
    calc
      ((Nat.ceil (T : ℝ) : ℝ) * (2 : ℝ) ^ n) *
          (C * ((2 : ℝ) ^ ((α : ℝ) * q - (1 + (β : ℝ)))) ^ n)
          = ((Nat.ceil (T : ℝ) : ℝ) * C) *
              ((2 : ℝ) ^ n * ((2 : ℝ) ^ ((α : ℝ) * q - (1 + (β : ℝ)))) ^ n) := by
                ring
      _ = ((Nat.ceil (T : ℝ) : ℝ) * C) *
            ((((2 : ℝ) ^ (1 : ℝ)) *
                (2 : ℝ) ^ ((α : ℝ) * q - (1 + (β : ℝ)))) ^ n) := by
              rw [show (2 : ℝ) ^ n = ((2 : ℝ) ^ (1 : ℝ)) ^ n by simp, ← mul_pow]
      _ = ((Nat.ceil (T : ℝ) : ℝ) * C) *
            (((2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))) ^ n) := by
              congr 2
              rw [← Real.rpow_add zero_lt_two]
              congr 1
              ring
  -- Proof comment: the row union bound collapses to one geometric factor in `n`.
  calc
    μ.real (dyadicRowBadEvent (X := X) T q n)
        ≤ (dyadicCutoff T n : ℝ) *
            (C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))) := hbase
    _ = ((Nat.ceil (T : ℝ) : ℝ) * C) * ((2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))) ^ n := hfinal

/-- Helper for Theorem 21.6: the dyadic bad-row masses are summable whenever `q < β / α`. -/
lemma summable_measureReal_dyadicRowBadEvent
    {X : NNReal → Ω → ℝ} {T α β C q : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (hq : (q : ℝ) < β / α) :
    Summable (fun n : ℕ ↦ μ.real (dyadicRowBadEvent (X := X) T q n)) := by
  have hαpos : 0 < (α : ℝ) := by
    exact_mod_cast h.alpha_pos
  have hgap : 0 < (β : ℝ) - (α : ℝ) * q := by
    have hmul_lt : (q : ℝ) * α < β := by
      exact (lt_div_iff₀ hαpos).mp hq
    nlinarith [hmul_lt]
  let ρ : ℝ := (2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))
  have hρ_nonneg : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt_one : ρ < 1 := by
    dsimp [ρ]
    have hexp_neg : ((α : ℝ) * q - (β : ℝ)) < 0 := by
      linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) hexp_neg
  have hgeom :
      Summable (fun n : ℕ ↦ ((Nat.ceil (T : ℝ) : ℝ) * C) * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left ((Nat.ceil (T : ℝ) : ℝ) * C)
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro n
    exact MeasureTheory.measureReal_nonneg
  · intro n
    simpa [ρ] using
      measureReal_dyadicRowBadEvent_le_geometric
        (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q) h hgap n
