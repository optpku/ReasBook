/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_34
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Corollary_8_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Corollary_8_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open OrderDual
open scoped ProbabilityTheory Topology InnerProductSpace

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕᵒᵈ mΩ}

/-
Theorem 12.14 is `source-facing`: it states backward-martingale convergence to the textbook tail
`σ`-algebra. Its `core/canonical` owner layer is the martingale and conditional-expectation
convergence API, notably `MeasureTheory.Martingale`,
`MeasureTheory.tendsto_ae_condExp`, and `MeasureTheory.tendsto_eLpNorm_condExp`. Its
`bridge/view` ingredient is the chapter-level uniform-integrability bridge
`backward_martingale_uniformIntegrable`, which converts the backward martingale into the owner
convergence setup after identifying `X (toDual n)` with `μ[X 0 | ℱ (toDual n)]`. The only
primitive data here are the backward martingale `X`, the reversed filtration `ℱ`, and the
measure `μ`; the tail conditional expectation is a derived object, so we keep no extra public
wrapper around it.
-/
section BackwardMartingale

variable {X : ℕᵒᵈ → Ω → ℝ}

local notation "𝓕∞" => tailMeasurableSpace (ℱ ∘ toDual)

/-- Helper for Theorem 12.14: the tail `σ`-algebra of the reversed filtration is the infimum of
its stages. -/
lemma tailMeasurableSpace_orderDual_eq_iInfStages :
    tailMeasurableSpace (ℱ ∘ toDual) = ⨅ n : ℕ, ℱ (toDual n) := by
  -- Proof comment: rewrite the tail `σ`-algebra as the intersection of the natural tails and then
  -- collapse each tail stage because `n ↦ ℱ (toDual n)` is decreasing in the ordinary order.
  calc
    tailMeasurableSpace (ℱ ∘ toDual) = ⨅ n : ℕ, ⨆ i ∈ Set.Ici n, ℱ (toDual i) := by
      simpa using tailMeasurableSpace_nat_eq_iInf_iSup_Ici (ℱ ∘ toDual)
    _ = ⨅ n : ℕ, ℱ (toDual n) := by
      refine iInf_congr fun n ↦ ?_
      refine le_antisymm ?_ ?_
      · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
        simpa using ℱ.mono (show (toDual i : ℕᵒᵈ) ≤ toDual n by simpa using hi)
      · have hn : (n : ℕ) ∈ Set.Ici (n : ℕ) := by
          simp [Set.mem_Ici]
        exact
          le_iSup_of_le (n : ℕ) <|
            le_iSup_of_le hn (show ℱ (toDual n) ≤ ℱ (toDual n) from le_rfl)

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 12.14: each stage of a backward martingale is the conditional expectation
of the time-zero variable onto the corresponding backward stage. -/
lemma backwardMartingale_aeEq_condExpAtZero (hX : Martingale X ℱ μ) (n : ℕ) :
    X (toDual n) =ᵐ[μ] μ[X 0 | ℱ (toDual n)] := by
  -- Proof comment: specialize the martingale identity at the earlier reversed time `toDual n`
  -- and the terminal time `0`.
  simpa using
    (hX.2 (toDual n) 0 (show (toDual n : ℕᵒᵈ) ≤ 0 by exact (show 0 ≤ n from Nat.zero_le n))).symm

/-- Helper for Theorem 12.14: the order-dual filtration stages form an antitone family on `ℕ`. -/
lemma orderDualStages_antitone : Antitone (fun n : ℕ ↦ ℱ (toDual n)) := by
  -- Proof comment: convert the ordinary inequality on `ℕ` into the reversed inequality in
  -- `ℕᵒᵈ`, then apply the filtration monotonicity once.
  intro m n hmn
  simpa using ℱ.mono (show (toDual n : ℕᵒᵈ) ≤ toDual m by simpa using hmn)

/-- Helper for Theorem 12.14: the squared `L²` distance between two reverse conditional-
expectation stages is the drop in the corresponding mean-square prediction errors. -/
lemma condExpSqError_diff_eq_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg2 : MemLp g 2 μ)
    {n k : ℕ} (hnk : n ≤ k) :
    ∫ ω, (μ[g | m n] ω - μ[g | m k] ω) ^ 2 ∂μ =
      ∫ ω, (g ω - μ[g | m k] ω) ^ 2 ∂μ -
        ∫ ω, (g ω - μ[g | m n] ω) ^ 2 ∂μ := by
  -- Proof comment: apply the Chapter 8 squared-error decomposition at stage `m n` with
  -- `Y = μ[g | m k]`, which is `m n`-measurable because the family is antitone.
  have hk_lp : MemLp (μ[g | m k]) 2 μ :=
    MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g) (ℱ := m k) hg2 (hm_le k)
  have hk_meas : Measurable[m n] (μ[g | m k]) := by
    exact (stronglyMeasurable_condExp.mono (hm_anti hnk)).measurable
  have hdecomp :=
    condExp_sq_error_decomposition (μ := μ) (hm := hm_le n) (X := g) (Y := μ[g | m k])
      hg2 hk_lp hk_meas
  linarith

/-- Helper for Theorem 12.14: the mean-square conditional-expectation error increases along a
decreasing family of `σ`-algebras. -/
lemma monotone_condExpSqError_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg2 : MemLp g 2 μ) :
    Monotone (fun n ↦ ∫ ω, (g ω - μ[g | m n] ω) ^ 2 ∂μ) := by
  -- Proof comment: the difference identity shows that the increment from stage `n` to `k`
  -- is the integral of a square, hence nonnegative.
  intro n k hnk
  have hdiff :=
    condExpSqError_diff_eq_of_antitone (μ := μ) (m := m) hm_le hm_anti hg2 (n := n) (k := k) hnk
  have hnonneg : 0 ≤ ∫ ω, (μ[g | m n] ω - μ[g | m k] ω) ^ 2 ∂μ := by
    exact integral_nonneg fun ω ↦ sq_nonneg _
  linarith

/-- Helper for Theorem 12.14: every reverse conditional-expectation stage has mean-square error
bounded above by the error at the limiting infimum `σ`-algebra. -/
lemma condExpSqError_le_iInf_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) {g : Ω → ℝ} (hg2 : MemLp g 2 μ) (n : ℕ) :
    ∫ ω, (g ω - μ[g | m n] ω) ^ 2 ∂μ ≤
      ∫ ω, (g ω - μ[g | ⨅ n : ℕ, m n] ω) ^ 2 ∂μ := by
  -- Proof comment: the infimum conditional expectation is still `m n`-measurable, so the
  -- Chapter 8 optimality theorem compares the stage `m n` predictor with the tail predictor.
  have hiInf_le : (⨅ n : ℕ, m n) ≤ mΩ := by
    exact (iInf_le (fun n : ℕ ↦ m n) 0).trans (hm_le 0)
  have hiInf_lp : MemLp (μ[g | ⨅ n : ℕ, m n]) 2 μ :=
    MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g)
      (ℱ := ⨅ n : ℕ, m n) hg2 hiInf_le
  have hiInf_meas : Measurable[m n] (μ[g | ⨅ n : ℕ, m n]) := by
    exact (stronglyMeasurable_condExp.mono (iInf_le (fun n : ℕ ↦ m n) n)).measurable
  exact
    condExp_sq_error_le (μ := μ) (hm := hm_le n) (X := g) (Y := μ[g | ⨅ n : ℕ, m n])
      hg2 hiInf_lp hiInf_meas

/-- Helper for Theorem 12.14: an `L²` reverse conditional-expectation residual is the orthogonal
projection of `g` onto the orthogonal complement of the corresponding `lpMeas` subspace. -/
lemma sub_condExp_ae_eq_starProjectionOrthogonal {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [Fact (m ≤ mΩ)]
    {g : Ω → ℝ} (hg2 : MemLp g 2 μ) :
    (fun ω ↦ g ω - μ[g | m] ω) =ᵐ[μ]
      (((@lpMeas Ω ℝ ℝ _ _ _ m mΩ 2 μ)ᗮ.starProjection hg2.toLp : Lp ℝ 2 μ) : Ω → ℝ) := by
  -- Proof comment: rewrite the orthogonal-complement projection as `id - P`, where `P` is the
  -- `lpMeas` projection, and then identify `P` with `condExpL2`.
  have hstar :
      (((@lpMeas Ω ℝ ℝ _ _ _ m mΩ 2 μ)ᗮ.starProjection hg2.toLp : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ]
        fun ω ↦ (hg2.toLp : Ω → ℝ) ω - (condExpL2 ℝ ℝ hm hg2.toLp : Ω → ℝ) ω := by
    have hstarLp :
        ((@lpMeas Ω ℝ ℝ _ _ _ m mΩ 2 μ)ᗮ.starProjection hg2.toLp : Lp ℝ 2 μ) =
          hg2.toLp - (condExpL2 ℝ ℝ hm hg2.toLp : Lp ℝ 2 μ) := by
      -- Proof comment: `condExpL2` is the orthogonal projection onto `lpMeas`, so the
      -- complementary projection is `id - condExpL2`.
      rw [Submodule.starProjection_orthogonal]
      rfl
    rw [hstarLp]
    exact Lp.coeFn_sub _ _
  have hcond : (condExpL2 ℝ ℝ hm hg2.toLp : Ω → ℝ) =ᵐ[μ] μ[g | m] :=
    hg2.condExpL2_ae_eq_condExp hm
  filter_upwards [hg2.coeFn_toLp, hstar, hcond] with ω hω hstarω hcondω
  simpa [hω, hcondω] using hstarω.symm

omit mΩ [IsFiniteMeasure μ] in
/-- Helper for Theorem 12.14: the limsup of a strict-mono subsequence whose `k`-th term is
measurable with respect to the antitone stage `m (N k)` is measurable with respect to the
infimum `σ`-algebra. -/
lemma measurable_limsup_iInf_of_antitone_subseq {m : ℕ → MeasurableSpace Ω}
    (hm_anti : Antitone m) {N : ℕ → ℕ} (hN : StrictMono N)
    {u : ℕ → Ω → ℝ} (hu : ∀ k, StronglyMeasurable[m (N k)] (u k)) :
    Measurable[⨅ n : ℕ, m n] fun ω ↦ Filter.limsup (fun k ↦ u k ω) atTop := by
  -- Proof comment: for each fixed stage `m n`, every sufficiently far subsequence term is already
  -- `m n`-measurable, so the same holds for the tail limsup; then we intersect over all stages.
  have hstage :
      ∀ n, Measurable[m n] fun ω ↦ Filter.limsup (fun k ↦ u k ω) atTop := by
    intro n
    have htail :
        ∀ k, Measurable[m n] fun ω ↦ u (k + n) ω := by
      intro k
      have hn_le : n ≤ N (k + n) := by
        exact le_trans (Nat.le_add_left n k) (hN.id_le (k + n))
      simpa using (hu (k + n)).measurable.mono (hm_anti hn_le)
    have htail_limsup :
        Measurable[m n] fun ω ↦ Filter.limsup (fun k ↦ u (k + n) ω) atTop :=
      Measurable.limsup htail
    have hshift_eq :
        (fun ω ↦ Filter.limsup (fun k ↦ u (k + n) ω) atTop) =
          fun ω ↦ Filter.limsup (fun k ↦ u k ω) atTop := by
      funext ω
      simpa using (Filter.limsup_nat_add (fun k ↦ u k ω) n)
    rw [hshift_eq] at htail_limsup
    exact htail_limsup
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  exact hstage n hs

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 12.14: an almost-everywhere subsequential limit along an antitone family
is almost everywhere strongly measurable with respect to the infimum `σ`-algebra. -/
lemma aestronglyMeasurable_iInf_of_antitone_subseq_limit {m : ℕ → MeasurableSpace Ω}
    (hm_anti : Antitone m) {N : ℕ → ℕ} (hN : StrictMono N)
    {u : ℕ → Ω → ℝ} {h : Ω → ℝ}
    (hu : ∀ k, StronglyMeasurable[m (N k)] (u k))
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun k ↦ u k ω) atTop (𝓝 (h ω))) :
    AEStronglyMeasurable[⨅ n : ℕ, m n] h μ := by
  -- Proof comment: the measurable representative is the limsup of the subsequence, which agrees
  -- almost everywhere with the pointwise limit on the convergence set.
  let l : Ω → ℝ := fun ω ↦ Filter.limsup (fun k ↦ u k ω) atTop
  have hl_meas : Measurable[⨅ n : ℕ, m n] l :=
    measurable_limsup_iInf_of_antitone_subseq (m := m) hm_anti hN hu
  have hl_ae : l =ᵐ[μ] h := by
    filter_upwards [ht] with ω hω
    simpa [l] using Filter.Tendsto.limsup_eq hω
  exact (hl_meas.stronglyMeasurable.aestronglyMeasurable).congr hl_ae

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 12.14: an antitone family of `σ`-algebras gives an antitone family of
`L²` subspaces of almost everywhere measurable functions. -/
lemma lpMeas_antitone {m : ℕ → MeasurableSpace Ω} (hm_anti : Antitone m) :
    Antitone (fun n : ℕ ↦ @lpMeas Ω ℝ ℝ _ _ _ (m n) mΩ 2 μ) := by
  -- Proof comment: membership in `lpMeas` is exactly `AEStronglyMeasurable`, and that property is
  -- monotone under coarsening of the measurable space.
  intro n k hnk f hf
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  exact hf.mono (hm_anti hnk)

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 12.14: the orthogonal complements of the `L²` stage subspaces form a
monotone family, so projection convergence can run on the reverse filtration after one explicit
instance bridge. -/
lemma lpMeasOrthogonal_monotone {m : ℕ → MeasurableSpace Ω} (hm_anti : Antitone m) :
    Monotone (fun n : ℕ ↦ (@lpMeas Ω ℝ ℝ _ _ _ (m n) mΩ 2 μ)ᗮ) := by
  -- Proof comment: `orthogonal` reverses inclusion, so the antitone `lpMeas` family becomes a
  -- monotone family after taking orthogonal complements.
  intro n k hnk
  exact Submodule.orthogonal_le (lpMeas_antitone (μ := μ) (m := m) hm_anti hnk)

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 12.14: the reverse `L²` residuals fit the monotone orthogonal-projection
template from the Hilbert-space projection API. -/
lemma tendsto_starProjectionOrthogonal_iSup_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg2 : MemLp g 2 μ) :
    Tendsto
      (fun n : ℕ ↦ ((@lpMeas Ω ℝ ℝ _ _ _ (m n) mΩ 2 μ)ᗮ.starProjection hg2.toLp : Lp ℝ 2 μ))
      atTop
      (𝓝
        (((⨆ n : ℕ, (@lpMeas Ω ℝ ℝ _ _ _ (m n) mΩ 2 μ)ᗮ).topologicalClosure).starProjection
          hg2.toLp)) := by
  -- Proof comment: package the stage residuals as star projections onto the increasing family
  -- `(lpMeas (m n))ᗮ`. The local `Fact` family pays the `lpMeas` orthogonal-projection instance
  -- cost once, instead of asking typeclass search to rediscover it at every occurrence.
  letI : ∀ n, Fact (m n ≤ mΩ) := fun n ↦ ⟨hm_le n⟩
  simpa using
    (Submodule.starProjection_tendsto_closure_iSup
      (U := fun n : ℕ ↦ (@lpMeas Ω ℝ ℝ _ _ _ (m n) mΩ 2 μ)ᗮ)
      (hU := lpMeasOrthogonal_monotone (μ := μ) (m := m) hm_anti)
      (x := hg2.toLp))

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 12.14: in `L²`, the squared distance between two bundled representatives
matches the integral of the squared pointwise difference. -/
lemma lpDistSq_eq_integral_sq {f g : Lp ℝ 2 μ} {F G : Ω → ℝ}
    (hf : (f : Ω → ℝ) =ᵐ[μ] F) (hg : (g : Ω → ℝ) =ᵐ[μ] G) :
    dist f g ^ 2 = ∫ ω, (F ω - G ω) ^ 2 ∂μ := by
  -- Proof comment: expand the `L²` distance as the norm of `f - g`, rewrite that norm through
  -- the `L²` inner product, and then replace the bundled representatives by the target functions.
  calc
    dist f g ^ 2 = ‖f - g‖ ^ 2 := by simp [dist_eq_norm]
    _ = ⟪f - g, f - g⟫_ℝ := by simp
    _ = ∫ ω, ⟪(f - g) ω, (f - g) ω⟫_ℝ ∂μ := by rw [MeasureTheory.L2.inner_def]
    _ = ∫ ω, ((f - g) ω) ^ 2 ∂μ := by simp [sq]
    _ = ∫ ω, (F ω - G ω) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hf, hg, Lp.coeFn_sub f g] with ω hfω hgω hsub
      rw [hsub, Pi.sub_apply, hfω, hgω]

/-- Helper for Theorem 12.14: the reverse conditional expectations form a Cauchy sequence in
`L²` along an antitone family of sub-`σ`-algebras. -/
lemma cauchySeq_condExpToLp_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg2 : MemLp g 2 μ) :
    CauchySeq
      (fun n =>
        ((MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g) (ℱ := m n) hg2
          (hm_le n)).toLp (μ[g | m n]))) := by
  let u : ℕ → Lp ℝ 2 μ := fun n =>
    ((MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g) (ℱ := m n) hg2
      (hm_le n)).toLp (μ[g | m n]))
  let err : ℕ → ℝ := fun n => ∫ ω, (g ω - μ[g | m n] ω) ^ 2 ∂μ
  have hmono : Monotone err :=
    monotone_condExpSqError_of_antitone (μ := μ) (m := m) hm_le hm_anti hg2
  have hbdd : BddAbove (Set.range err) := by
    refine ⟨∫ ω, (g ω - μ[g | ⨅ n : ℕ, m n] ω) ^ 2 ∂μ, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact condExpSqError_le_iInf_of_antitone (μ := μ) (m := m) hm_le hg2 n
  have hErr_tendsto : Tendsto err atTop (𝓝 (sSup (Set.range err))) :=
    by
      -- Proof comment: the monotone convergence theorem is stated on `Ici 0`; rewrite that image
      -- back to the ordinary range of the sequence.
      have hErr_tendsto_Ici :
          Tendsto err atTop (𝓝 (sSup (err '' Set.Ici (0 : ℕ)))) :=
        Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici
          (f := err) (k := 0) (hmono.monotoneOn _) (by simpa [Set.range, Set.Ici] using hbdd)
      have hRange : err '' Set.Ici (0 : ℕ) = Set.range err := by
        ext x
        constructor
        · rintro ⟨n, -, rfl⟩
          exact ⟨n, rfl⟩
        · rintro ⟨n, rfl⟩
          exact ⟨n, Nat.zero_le n, rfl⟩
      simpa [hRange] using hErr_tendsto_Ici
  have hGap_tendsto :
      Tendsto (fun N ↦ Real.sqrt (sSup (Set.range err) - err N)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ sSup (Set.range err)) atTop (𝓝 (sSup (Set.range err))) :=
      tendsto_const_nhds
    have hsub_tendsto : Tendsto (fun N ↦ sSup (Set.range err) - err N) atTop (𝓝 0) := by
      simpa using hconst.sub hErr_tendsto
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hsub_tendsto)
  refine
    cauchySeq_of_le_tendsto_0
      (fun N ↦ Real.sqrt (sSup (Set.range err) - err N)) ?_ hGap_tendsto
  intro n k N hNn hNk
  by_cases hnk : n ≤ k
  · have hdist_sq :
        dist (u n) (u k) ^ 2 = err k - err n := by
      -- Proof comment: convert the bundled `L²` distance back to the pointwise conditional-
      -- expectation difference and then invoke the mean-square error identity.
      have hdist_int :=
        lpDistSq_eq_integral_sq (μ := μ)
          (f := u n) (g := u k)
          ((MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g) (ℱ := m n) hg2
            (hm_le n)).coeFn_toLp)
          ((MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g) (ℱ := m k) hg2
            (hm_le k)).coeFn_toLp)
      simpa [u, err] using
        hdist_int.trans
          (condExpSqError_diff_eq_of_antitone (μ := μ) (m := m) hm_le hm_anti
            (n := n) (k := k) hg2 hnk)
    have hgap_nonneg : 0 ≤ sSup (Set.range err) - err N := by
      exact sub_nonneg.mpr <| le_csSup hbdd ⟨N, rfl⟩
    have hdist_sq_le : dist (u n) (u k) ^ 2 ≤ sSup (Set.range err) - err N := by
      have hk_le : err k ≤ sSup (Set.range err) := le_csSup hbdd ⟨k, rfl⟩
      have hN_le : err N ≤ err n := hmono hNn
      linarith
    exact
      (sq_le_sq₀ dist_nonneg
        (Real.sqrt_nonneg (sSup (Set.range err) - err N))).mp <|
        by
          simpa [pow_two, Real.sq_sqrt hgap_nonneg] using hdist_sq_le
  · have hkn : k ≤ n := Nat.le_of_not_ge hnk
    have hdist_sq :
        dist (u n) (u k) ^ 2 = err n - err k := by
      -- Proof comment: the same squared-error identity applies after swapping the indices.
      have hdist_int :=
        lpDistSq_eq_integral_sq (μ := μ)
          (f := u n) (g := u k)
          ((MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g) (ℱ := m n) hg2
            (hm_le n)).coeFn_toLp)
          ((MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g) (ℱ := m k) hg2
            (hm_le k)).coeFn_toLp)
      have hdist_int' :
          dist (u n) (u k) ^ 2 = ∫ ω, (μ[g | m k] ω - μ[g | m n] ω) ^ 2 ∂μ := by
        calc
          dist (u n) (u k) ^ 2 = ∫ ω, (μ[g | m n] ω - μ[g | m k] ω) ^ 2 ∂μ := by
            simpa [u] using hdist_int
          _ = ∫ ω, (μ[g | m k] ω - μ[g | m n] ω) ^ 2 ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [] with ω
            ring
      simpa [err] using
        hdist_int'.trans
          (condExpSqError_diff_eq_of_antitone (μ := μ) (m := m) hm_le hm_anti
            (n := k) (k := n) hg2 hkn)
    have hgap_nonneg : 0 ≤ sSup (Set.range err) - err N := by
      exact sub_nonneg.mpr <| le_csSup hbdd ⟨N, rfl⟩
    have hdist_sq_le : dist (u n) (u k) ^ 2 ≤ sSup (Set.range err) - err N := by
      have hn_le : err n ≤ sSup (Set.range err) := le_csSup hbdd ⟨n, rfl⟩
      have hN_le : err N ≤ err k := hmono hNk
      linarith
    exact
      (sq_le_sq₀ dist_nonneg
        (Real.sqrt_nonneg (sSup (Set.range err) - err N))).mp <|
        by
          simpa [pow_two, Real.sq_sqrt hgap_nonneg] using hdist_sq_le

/-- Helper for Theorem 12.14: along an antitone family, the reverse conditional expectations of
an `L²` function admit an `L²` limit representative which is almost everywhere strongly measurable
for the infimum `σ`-algebra. -/
lemma exists_aestronglyMeasurableLpLimit_condExp_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg2 : MemLp g 2 μ) :
    ∃ h : Ω → ℝ, MemLp h 2 μ ∧ AEStronglyMeasurable[⨅ n : ℕ, m n] h μ ∧
      Tendsto (fun n ↦ eLpNorm (μ[g | m n] - h) 2 μ) atTop (𝓝 0) := by
  let u : ℕ → Lp ℝ 2 μ := fun n =>
    ((MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g) (ℱ := m n) hg2
      (hm_le n)).toLp (μ[g | m n]))
  obtain ⟨uInf, huInf⟩ :=
    cauchySeq_tendsto_of_complete
      (cauchySeq_condExpToLp_of_antitone (μ := μ) (m := m) hm_le hm_anti hg2)
  have hnormLp : Tendsto (fun n ↦ eLpNorm (⇑(u n) - ⇑uInf) 2 μ) atTop (𝓝 0) := by
    -- Proof comment: convert the `Lp` convergence of the bundled stage sequence into function-
    -- level `L²` convergence against the concrete representative of the `Lp` limit.
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' u uInf).1 huInf
  have hnorm : Tendsto (fun n ↦ eLpNorm (μ[g | m n] - (uInf : Ω → ℝ)) 2 μ) atTop (𝓝 0) := by
    -- Proof comment: rewrite the bundled stage representatives back to the conditional-
    -- expectation functions, keeping the limit in the same spelling world.
    have hEq :
        (fun n ↦ eLpNorm (μ[g | m n] - (uInf : Ω → ℝ)) 2 μ) =
          fun n ↦ eLpNorm (⇑(u n) - ⇑uInf) 2 μ := by
      funext n
      exact
        eLpNorm_congr_ae
          (((MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g) (ℱ := m n) hg2
              (hm_le n)).coeFn_toLp).symm.sub EventuallyEq.rfl)
    simpa [hEq] using hnormLp
  have htwo_ne_zero : (2 : ENNReal) ≠ 0 := by
    norm_num
  have hInMeasure :
      TendstoInMeasure μ (fun n ↦ μ[g | m n]) atTop (uInf : Ω → ℝ) :=
    tendstoInMeasure_of_tendsto_eLpNorm htwo_ne_zero
      (fun n ↦ (stronglyMeasurable_condExp.mono (hm_le n)).aestronglyMeasurable)
      (Lp.aestronglyMeasurable uInf) hnorm
  obtain ⟨N, hN, hNae⟩ := MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae hInMeasure
  have hInfMeas : AEStronglyMeasurable[⨅ n : ℕ, m n] (uInf : Ω → ℝ) μ := by
    -- Proof comment: one almost-everywhere convergent subsequence is enough to transport the
    -- stage measurability down to the infimum `σ`-algebra.
    refine aestronglyMeasurable_iInf_of_antitone_subseq_limit (μ := μ) (m := m) hm_anti hN ?_ hNae
    intro k
    exact stronglyMeasurable_condExp
  exact ⟨(uInf : Ω → ℝ), Lp.memLp uInf, hInfMeas, hnorm⟩

/-- Helper for Theorem 12.14: a square-integrable reverse conditional-expectation sequence
converges in `L²` to the canonical conditional expectation onto the infimum `σ`-algebra. -/
lemma tendsto_eLpNorm_two_condExp_iInf_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg2 : MemLp g 2 μ) :
    Tendsto
      (fun n ↦ eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 2 μ)
      atTop (𝓝 0) := by
  obtain ⟨h, hh2, hhMeas, hconv⟩ :=
    exists_aestronglyMeasurableLpLimit_condExp_of_antitone
      (μ := μ) (m := m) hm_le hm_anti hg2
  have hiInf_le : (⨅ n : ℕ, m n) ≤ mΩ := by
    exact (iInf_le (fun n : ℕ ↦ m n) 0).trans (hm_le 0)
  letI : Fact ((⨅ n : ℕ, m n) ≤ mΩ) := ⟨hiInf_le⟩
  let K : Submodule ℝ (Lp ℝ 2 μ) := @lpMeas Ω ℝ ℝ _ _ _ (⨅ n : ℕ, m n) mΩ 2 μ
  letI : K.HasOrthogonalProjection := by
    dsimp [K]
    infer_instance
  let U : ℕ → Submodule ℝ (Lp ℝ 2 μ) :=
    fun n ↦ (@lpMeas Ω ℝ ℝ _ _ _ (m n) mΩ 2 μ)ᗮ
  let r : Ω → ℝ := fun ω ↦ g ω - h ω
  have hiInf_lp : MemLp (μ[g | ⨅ n : ℕ, m n]) 2 μ :=
    MeasureTheory.MemLp.condExp_of_one_le (μ := μ) (p := 2) (X := g)
      (ℱ := ⨅ n : ℕ, m n) hg2 hiInf_le
  have hr2 : MemLp r 2 μ := hg2.sub hh2
  have hres_tendsto :
      Tendsto (fun n : ℕ ↦ ((U n).starProjection hg2.toLp : Lp ℝ 2 μ))
        atTop (𝓝 (hr2.toLp r)) := by
    -- Proof comment: rewrite the orthogonal residuals back to `g - μ[g | m n]`, then compare them
    -- with the target residual `g - h` through the already established `L²` convergence.
    let v : ℕ → Ω → ℝ := fun n ↦ (((U n).starProjection hg2.toLp : Lp ℝ 2 μ) : Ω → ℝ)
    have hv_mem : ∀ n, MemLp (v n) 2 μ := fun _ ↦ Lp.memLp _
    have hEq :
        (fun n : ℕ ↦
          eLpNorm (v n - r) 2 μ) =
          fun n ↦ eLpNorm (μ[g | m n] - h) 2 μ := by
      funext n
      letI : Fact (m n ≤ mΩ) := ⟨hm_le n⟩
      calc
        eLpNorm (v n - r) 2 μ = eLpNorm (r - v n) 2 μ := by
          rw [eLpNorm_sub_comm]
        _ = eLpNorm (μ[g | m n] - h) 2 μ := by
          refine eLpNorm_congr_ae ?_
          filter_upwards
            [sub_condExp_ae_eq_starProjectionOrthogonal
              (μ := μ) (m := m n) (hm := hm_le n) hg2] with ω hω
          have hvω : v n ω = g ω - μ[g | m n] ω := hω.symm
          calc
            r ω - v n ω = (g ω - h ω) - (g ω - μ[g | m n] ω) := by
              simp [r, hvω]
            _ = μ[g | m n] ω - h ω := by ring
    have hv_tendsto :
        Tendsto (fun n ↦ (hv_mem n).toLp (v n)) atTop (𝓝 (hr2.toLp r)) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv_mem r hr2).2 (by simpa [v, hEq] using hconv)
    have hv_toLp :
        (fun n ↦ (hv_mem n).toLp (v n)) =
          fun n ↦ ((U n).starProjection hg2.toLp : Lp ℝ 2 μ) := by
      funext n
      change
        (hv_mem n).toLp ((((U n).starProjection hg2.toLp : Lp ℝ 2 μ) : Ω → ℝ)) =
          ((U n).starProjection hg2.toLp : Lp ℝ 2 μ)
      exact Lp.toLp_coeFn ((U n).starProjection hg2.toLp : Lp ℝ 2 μ) (Lp.memLp _)
    simpa [hv_toLp] using hv_tendsto
  have hstar_tendsto :
      Tendsto (fun n : ℕ ↦ ((U n).starProjection hg2.toLp : Lp ℝ 2 μ))
        atTop
        (𝓝 (((⨆ n : ℕ, U n).topologicalClosure).starProjection hg2.toLp)) :=
    tendsto_starProjectionOrthogonal_iSup_of_antitone (μ := μ) (m := m) hm_le hm_anti hg2
  have hU_le : ∀ n : ℕ, U n ≤ Kᗮ := by
    intro n
    -- Proof comment: every tail-measurable `L²` function is already measurable at each stage, so
    -- the stage orthogonal complements sit inside the tail orthogonal complement.
    exact Submodule.orthogonal_le <| by
      intro f hf
      rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
      exact hf.mono (iInf_le (fun n : ℕ ↦ m n) n)
  have hclosure_le : (⨆ n : ℕ, U n).topologicalClosure ≤ Kᗮ := by
    exact Submodule.topologicalClosure_minimal _ (iSup_le hU_le) K.isClosed_orthogonal
  have hz_mem :
      (((⨆ n : ℕ, U n).topologicalClosure).starProjection hg2.toLp : Lp ℝ 2 μ) ∈ Kᗮ := by
    exact hclosure_le (Submodule.coe_mem _)
  have hz_eq :
      (((⨆ n : ℕ, U n).topologicalClosure).starProjection hg2.toLp : Lp ℝ 2 μ) = hr2.toLp r := by
    exact tendsto_nhds_unique hstar_tendsto hres_tendsto
  have hr_mem : hr2.toLp r ∈ Kᗮ := by
    rw [← hz_eq]
    exact hz_mem
  have hh_mem : hh2.toLp h ∈ K := by
    -- Proof comment: bundle the measurable witness into the canonical `lpMeas` tail subspace.
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    exact hhMeas.congr hh2.coeFn_toLp.symm
  have hsum : hg2.toLp g = hh2.toLp h + hr2.toLp r := by
    -- Proof comment: split the original `L²` class into its tail-measurable part and the
    -- orthogonal residual `g - h`.
    calc
      hg2.toLp g = (hh2.add hr2).toLp (h + r) := by
        refine MemLp.toLp_congr hg2 (hh2.add hr2) ?_
        filter_upwards [] with ω
        simp [r]
      _ = hh2.toLp h + hr2.toLp r := by
        rw [MemLp.toLp_add]
  have hproj :
      K.starProjection (hg2.toLp g) = hh2.toLp h :=
    Submodule.eq_starProjection_of_mem_orthogonal' hh_mem hr_mem hsum
  have hcond_toLp : hh2.toLp h = hiInf_lp.toLp (μ[g | ⨅ n : ℕ, m n]) := by
    -- Proof comment: the orthogonal projection onto the tail subspace is exactly `condExpL2`,
    -- hence the identified projection agrees with the tail conditional expectation.
    have hcondExpL2_toLp :
        (((condExpL2 ℝ ℝ hiInf_le hg2.toLp :
            @lpMeas Ω ℝ ℝ _ _ _ (⨅ n : ℕ, m n) mΩ 2 μ) : Lp ℝ 2 μ)) =
          hiInf_lp.toLp (μ[g | ⨅ n : ℕ, m n]) := by
      apply Lp.ext
      exact
        (hg2.condExpL2_ae_eq_condExp hiInf_le).trans hiInf_lp.coeFn_toLp.symm
    calc
      hh2.toLp h = K.starProjection (hg2.toLp g) := hproj.symm
      _ = (((condExpL2 ℝ ℝ hiInf_le hg2.toLp :
            @lpMeas Ω ℝ ℝ _ _ _ (⨅ n : ℕ, m n) mΩ 2 μ) : Lp ℝ 2 μ)) := rfl
      _ = hiInf_lp.toLp (μ[g | ⨅ n : ℕ, m n]) := hcondExpL2_toLp
  have hh_eq_cond :
      h =ᵐ[μ] μ[g | ⨅ n : ℕ, m n] := by
    exact (MemLp.toLp_eq_toLp_iff hh2 hiInf_lp).mp hcond_toLp
  -- Proof comment: rewrite the owner convergence statement through the identified canonical tail
  -- conditional expectation.
  have hEq :
      (fun n ↦ eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 2 μ) =
        fun n ↦ eLpNorm (μ[g | m n] - h) 2 μ := by
    funext n
    exact eLpNorm_congr_ae (EventuallyEq.rfl.sub hh_eq_cond.symm)
  simpa [hEq] using hconv

/-- Helper for Theorem 12.14: a square-integrable reverse conditional-expectation sequence
already converges in `L¹` to the canonical tail conditional expectation. -/
lemma tendsto_eLpNorm_one_condExp_iInf_of_antitone_memLpTwo {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg2 : MemLp g 2 μ) :
    Tendsto
      (fun n ↦ eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 1 μ)
      atTop (𝓝 0) := by
  let C : ENNReal := μ Set.univ ^ ((1 : ℝ) / 2)
  have hiInf_le : (⨅ n : ℕ, m n) ≤ mΩ := by
    exact (iInf_le (fun n : ℕ ↦ m n) 0).trans (hm_le 0)
  have hbound :
      ∀ n,
        eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 1 μ ≤
          eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 2 μ * C := by
    intro n
    -- Route correction: on a finite measure space, the `L² → L¹` upgrade is just exponent
    -- comparison, so no extra uniform-integrability scaffolding is needed here.
    calc
      eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 1 μ ≤
          eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 2 μ *
            μ Set.univ ^ (1 - (2 : ℝ)⁻¹) := by
              simpa using
                eLpNorm_le_eLpNorm_mul_rpow_measure_univ
                  (μ := μ) (p := (1 : ENNReal)) (q := (2 : ENNReal))
                  (f := μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) one_le_two
                  (((stronglyMeasurable_condExp.mono (hm_le n)).aestronglyMeasurable).sub
                    ((stronglyMeasurable_condExp.mono hiInf_le).aestronglyMeasurable))
      _ = eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 2 μ * C := by
            congr 1
            have hexp : (1 - (2 : ℝ)⁻¹) = (1 : ℝ) / 2 := by norm_num
            simp [C, hexp]
  have hupper :
      Tendsto
        (fun n ↦ eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 2 μ * C)
        atTop (𝓝 0) := by
    have hC_top : C ≠ ⊤ := by
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ Set.univ)
    simpa [zero_mul] using
      (ENNReal.Tendsto.mul_const
        (tendsto_eLpNorm_two_condExp_iInf_of_antitone (μ := μ) (m := m) hm_le hm_anti hg2))
        (Or.inr hC_top)
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n ↦ zero_le _) hbound

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 12.14: truncating an integrable function at the natural levels converges
to the original function in `L¹`. -/
lemma tendsto_eLpNorm_one_truncation_sub {g : Ω → ℝ} (hg : Integrable g μ) :
    Tendsto (fun n : ℕ ↦ eLpNorm (truncation g (n : ℝ) - g) 1 μ) atTop (𝓝 0) := by
  have hMeas :
      ∀ n : ℕ, AEStronglyMeasurable (truncation g (n : ℝ)) μ := by
    intro n
    exact hg.aestronglyMeasurable.truncation
  have hBound :
      ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖truncation g (n : ℝ) ω‖ ≤ |g ω| := by
    intro n
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [Real.norm_eq_abs] using abs_truncation_le_abs_self g (n : ℝ) ω
  have hLim :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ truncation g (n : ℝ) ω) atTop (𝓝 (g ω)) := by
    filter_upwards [] with ω
    have hEventually :
        ∀ᶠ n : ℕ in atTop, truncation g (n : ℝ) ω = g ω := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop |g ω|] with n hn
      exact truncation_eq_self hn
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hEventually] with n hn
    exact hn.symm
  have hLintegral :
      Tendsto
        (fun n : ℕ ↦ ∫⁻ ω, ENNReal.ofReal ‖truncation g (n : ℝ) ω - g ω‖ ∂μ)
        atTop (𝓝 0) :=
    tendsto_lintegral_norm_of_dominated_convergence hMeas hg.norm.hasFiniteIntegral hBound hLim
  have hEq :
      (fun n : ℕ ↦ ∫⁻ ω, ENNReal.ofReal ‖truncation g (n : ℝ) ω - g ω‖ ∂μ) =
        fun n : ℕ ↦ ∫⁻ ω, (↑‖truncation g (n : ℝ) ω - g ω‖₊ : ENNReal) ∂μ := by
    funext n
    refine lintegral_congr_ae ?_
    filter_upwards [] with ω
    rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
    rfl
  have hLintegral' :
      Tendsto
        (fun n : ℕ ↦ ∫⁻ ω, (↑‖truncation g (n : ℝ) ω - g ω‖₊ : ENNReal) ∂μ)
        atTop (𝓝 0) := by
    exact hEq ▸ hLintegral
  simpa [eLpNorm_one_eq_lintegral_enorm, enorm_eq_nnnorm] using hLintegral'

/-- Helper for Theorem 12.14: every bounded truncation of an integrable function is in `L²`. -/
lemma truncation_memLpTwo {g : Ω → ℝ} (hg : Integrable g μ) (n : ℕ) :
    MemLp (truncation g (n : ℝ)) 2 μ := by
  -- Proof comment: on a finite measure space, truncation is uniformly bounded by the cutoff level,
  -- so the generic bounded-function `MemLp` criterion applies directly.
  simpa using
    (hg.aestronglyMeasurable.memLp_truncation (μ := μ) (A := (n : ℝ)) (p := (2 : ENNReal)))

/-- Helper for Theorem 12.14: reverse Lévy `L¹` convergence for an antitone family of
sub-`σ`-algebras. -/
lemma tendsto_eLpNorm_condExp_iInf_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg : Integrable g μ) :
    Tendsto
      (fun n ↦ eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 1 μ)
      atTop (𝓝 0) := by
  -- Proof comment: fix one truncation level, split the target difference into two truncation
  -- errors and one square-integrable middle term, then send the truncation level to infinity.
  have htrunc :
      Tendsto (fun N : ℕ ↦ eLpNorm (g - truncation g (N : ℝ)) 1 μ) atTop (𝓝 0) := by
    -- Proof comment: the previously proved truncation limit already has the right content after
    -- swapping the subtraction order inside the `L¹` norm.
    simpa [eLpNorm_sub_comm] using tendsto_eLpNorm_one_truncation_sub (μ := μ) (g := g) hg
  rw [ENNReal.tendsto_nhds_zero] at htrunc ⊢
  intro ε hε
  by_cases hε_top : ε = ⊤
  · -- Proof comment: the infinite radius neighborhood is automatic.
    simp [hε_top]
  · rcases WithTop.ne_top_iff_exists.mp hε_top with ⟨εr, rfl⟩
    have hεr_pos : (0 : ENNReal) < (εr : ENNReal) := by
      simpa [gt_iff_lt] using hε
    have hquarter :
        ∀ᶠ N : ℕ in atTop, eLpNorm (g - truncation g (N : ℝ)) 1 μ ≤ (εr : ENNReal) / 4 :=
      htrunc ((εr : ENNReal) / 4) (by
        have hquarterPos : (0 : ENNReal) < (εr : ENNReal) / 4 := by
          rw [ENNReal.div_pos_iff]
          exact ⟨hεr_pos.ne', by norm_num⟩
        simpa using hquarterPos)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hquarter
    have hmid :
        Tendsto
          (fun n ↦
            eLpNorm
              (μ[truncation g (N : ℝ) | m n] - μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n])
              1 μ)
          atTop (𝓝 0) :=
      tendsto_eLpNorm_one_condExp_iInf_of_antitone_memLpTwo
        (μ := μ) (m := m) hm_le hm_anti (truncation_memLpTwo (μ := μ) hg N)
    rw [ENNReal.tendsto_nhds_zero] at hmid
    have hhalf :
        ∀ᶠ n : ℕ in atTop,
          eLpNorm
              (μ[truncation g (N : ℝ) | m n] - μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n])
              1 μ ≤
            (εr : ENNReal) / 2 :=
      hmid ((εr : ENNReal) / 2) (by
        have hhalfPos : (0 : ENNReal) < (εr : ENNReal) / 2 := by
          rw [ENNReal.div_pos_iff]
          exact ⟨hεr_pos.ne', by norm_num⟩
        simpa using hhalfPos)
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hhalf
    refine Filter.eventually_atTop.2 ⟨M, ?_⟩
    intro n hn
    have htrunc_int : Integrable (truncation g (N : ℝ)) μ :=
      hg.aestronglyMeasurable.integrable_truncation
    have hiInf_le : (⨅ n : ℕ, m n) ≤ mΩ := by
      exact (iInf_le (fun n : ℕ ↦ m n) 0).trans (hm_le 0)
    have hLeftMeas :
        AEStronglyMeasurable
          (μ[g | m n] - μ[truncation g (N : ℝ) | m n]) μ :=
      ((stronglyMeasurable_condExp.mono (hm_le n)).aestronglyMeasurable).sub
        ((stronglyMeasurable_condExp.mono (hm_le n)).aestronglyMeasurable)
    have hMidMeas :
        AEStronglyMeasurable
          (μ[truncation g (N : ℝ) | m n] -
            μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n]) μ :=
      ((stronglyMeasurable_condExp.mono (hm_le n)).aestronglyMeasurable).sub
        ((stronglyMeasurable_condExp.mono hiInf_le).aestronglyMeasurable)
    have hRightMeas :
        AEStronglyMeasurable
          (μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n] - μ[g | ⨅ n : ℕ, m n]) μ :=
      ((stronglyMeasurable_condExp.mono hiInf_le).aestronglyMeasurable).sub
        ((stronglyMeasurable_condExp.mono hiInf_le).aestronglyMeasurable)
    have hLeftBound :
        eLpNorm (μ[g | m n] - μ[truncation g (N : ℝ) | m n]) 1 μ ≤
          eLpNorm (g - truncation g (N : ℝ)) 1 μ := by
      calc
        eLpNorm (μ[g | m n] - μ[truncation g (N : ℝ) | m n]) 1 μ =
            eLpNorm (μ[g - truncation g (N : ℝ) | m n]) 1 μ := by
              exact eLpNorm_congr_ae (condExp_sub hg htrunc_int (m n)).symm
        _ ≤ eLpNorm (g - truncation g (N : ℝ)) 1 μ :=
            eLpNorm_one_condExp_le_eLpNorm (μ := μ) (m := m n)
              (f := g - truncation g (N : ℝ))
    have hRightBound :
        eLpNorm (μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n] - μ[g | ⨅ n : ℕ, m n]) 1 μ ≤
          eLpNorm (g - truncation g (N : ℝ)) 1 μ := by
      calc
        eLpNorm (μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n] - μ[g | ⨅ n : ℕ, m n]) 1 μ =
            eLpNorm (μ[truncation g (N : ℝ) - g | ⨅ n : ℕ, m n]) 1 μ := by
              exact eLpNorm_congr_ae (condExp_sub htrunc_int hg (⨅ n : ℕ, m n)).symm
        _ ≤ eLpNorm (truncation g (N : ℝ) - g) 1 μ :=
            eLpNorm_one_condExp_le_eLpNorm (μ := μ) (m := ⨅ n : ℕ, m n)
              (f := truncation g (N : ℝ) - g)
        _ = eLpNorm (g - truncation g (N : ℝ)) 1 μ := by
            rw [eLpNorm_sub_comm]
    have hSplit :
        eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 1 μ ≤
          eLpNorm (μ[g | m n] - μ[truncation g (N : ℝ) | m n]) 1 μ +
            (eLpNorm
                (μ[truncation g (N : ℝ) | m n] -
                  μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n])
                1 μ +
              eLpNorm
                (μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n] - μ[g | ⨅ n : ℕ, m n])
                1 μ) := by
      calc
        eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 1 μ =
            eLpNorm
                ((μ[g | m n] - μ[truncation g (N : ℝ) | m n]) +
                  ((μ[truncation g (N : ℝ) | m n] -
                      μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n]) +
                    (μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n] - μ[g | ⨅ n : ℕ, m n])))
                1 μ := by
                  refine eLpNorm_congr_ae ?_
                  filter_upwards [] with ω
                  simp [Pi.sub_apply]
        _ ≤
            eLpNorm (μ[g | m n] - μ[truncation g (N : ℝ) | m n]) 1 μ +
              eLpNorm
                ((μ[truncation g (N : ℝ) | m n] -
                    μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n]) +
                  (μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n] - μ[g | ⨅ n : ℕ, m n]))
                1 μ := by
                  exact eLpNorm_add_le hLeftMeas (hMidMeas.add hRightMeas) le_rfl
        _ ≤
            eLpNorm (μ[g | m n] - μ[truncation g (N : ℝ) | m n]) 1 μ +
              (eLpNorm
                  (μ[truncation g (N : ℝ) | m n] -
                    μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n])
                  1 μ +
                eLpNorm
                  (μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n] - μ[g | ⨅ n : ℕ, m n])
                  1 μ) := by
                    gcongr
                    exact eLpNorm_add_le hMidMeas hRightMeas le_rfl
    have hquarterN :
        eLpNorm (g - truncation g (N : ℝ)) 1 μ ≤ (εr : ENNReal) / 4 :=
      hN N le_rfl
    have hhalfn :
        eLpNorm
            (μ[truncation g (N : ℝ) | m n] - μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n])
            1 μ ≤
          (εr : ENNReal) / 2 :=
      hM n hn
    calc
      eLpNorm (μ[g | m n] - μ[g | ⨅ n : ℕ, m n]) 1 μ ≤
          eLpNorm (μ[g | m n] - μ[truncation g (N : ℝ) | m n]) 1 μ +
            (eLpNorm
                (μ[truncation g (N : ℝ) | m n] -
                  μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n])
                1 μ +
              eLpNorm
                (μ[truncation g (N : ℝ) | ⨅ n : ℕ, m n] - μ[g | ⨅ n : ℕ, m n])
                1 μ) := hSplit
      _ ≤ eLpNorm (g - truncation g (N : ℝ)) 1 μ +
            ((εr : ENNReal) / 2 + eLpNorm (g - truncation g (N : ℝ)) 1 μ) := by
              exact add_le_add hLeftBound (add_le_add hhalfn hRightBound)
      _ ≤ (εr : ENNReal) / 4 + ((εr : ENNReal) / 2 + (εr : ENNReal) / 4) := by
            exact add_le_add hquarterN (add_le_add le_rfl hquarterN)
      _ ≤ εr := by
            have hsumε' : (εr : ℝ) / 4 + ((εr : ℝ) / 2 + (εr : ℝ) / 4) = εr := by
              ring
            have hsumε :
                (εr : ENNReal) / 4 + ((εr : ENNReal) / 2 + (εr : ENNReal) / 4) = εr := by
              exact_mod_cast hsumε'
            exact le_of_eq hsumε

/-- Helper for Theorem 12.14: the antitone reverse conditional-expectation sequence already
converges in measure to the tail conditional expectation. -/
lemma tendstoInMeasure_condExp_iInf_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg : Integrable g μ) :
    TendstoInMeasure μ (fun n ↦ μ[g | m n]) atTop (μ[g | ⨅ n : ℕ, m n]) := by
  -- Proof comment: reuse the already established `L¹` convergence theorem and convert it to
  -- convergence in measure with the standard `eLpNorm → in measure` bridge.
  have hiInf_le : (⨅ n : ℕ, m n) ≤ mΩ := by
    exact (iInf_le (fun n : ℕ ↦ m n) 0).trans (hm_le 0)
  exact
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n ↦ (stronglyMeasurable_condExp.mono (hm_le n)).aestronglyMeasurable)
      ((stronglyMeasurable_condExp.mono hiInf_le).aestronglyMeasurable)
      (tendsto_eLpNorm_condExp_iInf_of_antitone (μ := μ) (m := m) hm_le hm_anti hg)

/-- Helper for Theorem 12.14: convergence in measure of the reverse conditional-expectation
sequence yields an almost-everywhere convergent subsequence to the tail conditional expectation. -/
lemma exists_seq_tendsto_ae_condExp_iInf_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg : Integrable g μ) :
    ∃ N : ℕ → ℕ, StrictMono N ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k ↦ μ[g | m (N k)] ω) atTop (𝓝 (μ[g | ⨅ n : ℕ, m n] ω)) := by
  -- Proof comment: once the whole family converges in measure, the standard subsequence principle
  -- produces a strictly monotone subsequence with almost-everywhere pointwise convergence.
  exact
    MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae
      (tendstoInMeasure_condExp_iInf_of_antitone (μ := μ) (m := m) hm_le hm_anti hg)

/-- Helper for Theorem 12.14: the canonical almost-surely convergent subsequence can be thinned so
that its `L¹` distance to the tail conditional expectation decays geometrically. -/
lemma existsGeometricCondExpSubseq {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg : Integrable g μ) :
    ∃ N : ℕ → ℕ, StrictMono N ∧
      (∀ᵐ ω ∂μ, Tendsto (fun k ↦ μ[g | m (N k)] ω) atTop (𝓝 (μ[g | ⨅ n : ℕ, m n] ω))) ∧
      ∀ k,
        eLpNorm (μ[g | m (N k)] - μ[g | ⨅ n : ℕ, m n]) 1 μ <
          ((((1 : ENNReal) / 8) ^ (k + 2))) := by
  obtain ⟨N₀, hN₀, hN₀ae⟩ :=
    exists_seq_tendsto_ae_condExp_iInf_of_antitone (μ := μ) (m := m) hm_le hm_anti hg
  let a : ℕ → ENNReal := fun k ↦
    eLpNorm (μ[g | m (N₀ k)] - μ[g | ⨅ n : ℕ, m n]) 1 μ
  have ha_tendsto : Tendsto a atTop (𝓝 0) := by
    -- Proof comment: the full-sequence `L¹` convergence theorem is stable under strict-mono
    -- reindexing, so the canonical a.e.-convergent subsequence still tends to the tail in `L¹`.
    simpa [a] using
      (tendsto_eLpNorm_condExp_iInf_of_antitone (μ := μ) (m := m) hm_le hm_anti hg).comp
        hN₀.tendsto_atTop
  have hsmall :
      ∀ k : ℕ, Set.Iio ((((1 : ENNReal) / 8) ^ (k + 2))) ∈ 𝓝 (0 : ENNReal) := by
    intro k
    have hbase : (0 : ENNReal) < (1 : ENNReal) / 8 := by norm_num
    have hpos : (0 : ENNReal) < (((1 : ENNReal) / 8) ^ (k + 2)) := by
      exact ENNReal.pow_pos hbase _
    exact Iio_mem_nhds hpos
  obtain ⟨φ, hφ, hφmem⟩ := Filter.Tendsto.subseq_mem hsmall ha_tendsto
  refine ⟨N₀ ∘ φ, hN₀.comp hφ, ?_, ?_⟩
  · -- Proof comment: composing the already convergent subsequence with the thinning map preserves
    -- its almost-sure pointwise limit.
    filter_upwards [hN₀ae] with ω hω
    exact hω.comp hφ.tendsto_atTop
  · -- Proof comment: the subsequence extractor was chosen so that the `k`-th `L¹` error lies in
    -- the `k`-th shrinking neighborhood of zero.
    intro k
    exact hφmem k

/-- Helper for Theorem 12.14: any almost-everywhere pointwise limit of the reverse
conditional-expectation sequence must agree almost everywhere with the canonical tail conditional
expectation. -/
lemma aeEq_limit_condExp_iInf_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg : Integrable g μ)
    {l : Ω → ℝ}
    (hl : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[g | m n] ω) atTop (𝓝 (l ω))) :
    l =ᵐ[μ] μ[g | ⨅ n : ℕ, m n] := by
  -- Proof comment: convert the assumed almost-everywhere pointwise convergence into convergence in
  -- measure, then use the already proved convergence-in-measure theorem to identify the limit.
  have hInMeasure_l :
      TendstoInMeasure μ (fun n ↦ μ[g | m n]) atTop l :=
    tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (stronglyMeasurable_condExp.mono (hm_le n)).aestronglyMeasurable) hl
  exact
    tendstoInMeasure_ae_unique hInMeasure_l
      (tendstoInMeasure_condExp_iInf_of_antitone (μ := μ) (m := m) hm_le hm_anti hg)

/-- Helper for Theorem 12.14: reversing a finite antitone block produces a forward filtration on
`ℕ`. -/
def reverseBlockFiltration {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) (N K : ℕ) :
    Filtration ℕ mΩ :=
  { seq := fun j ↦ m (K - min j (K - N))
    mono' := fun _ _ hij ↦
      hm_anti (Nat.sub_le_sub_left (min_le_min_right (K - N) hij) K)
    le' := fun j ↦ hm_le (K - min j (K - N)) }

/-- Helper for Theorem 12.14: the conditional-expectation differences on a reversed finite block
form a forward martingale. -/
lemma reverseBlockCondExp_martingale {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (N K : ℕ) :
    Martingale
      (fun j ω ↦ μ[g | m (K - min j (K - N))] ω - μ[g | m K] ω)
      (reverseBlockFiltration (m := m) hm_le hm_anti N K) μ := by
  let Fblk : Filtration ℕ mΩ := reverseBlockFiltration (m := m) hm_le hm_anti N K
  have hcond : Martingale (fun j ↦ μ[g | Fblk j]) Fblk μ :=
    martingale_condExp g Fblk μ
  have hconstMeas : StronglyMeasurable[Fblk 0] (μ[g | m K]) := by
    -- Proof comment: the reversed block starts at stage `m K`, so the endpoint conditional
    -- expectation is measurable at time zero of the block filtration.
    simpa [Fblk, reverseBlockFiltration] using
      (stronglyMeasurable_condExp : StronglyMeasurable[m K] (μ[g | m K]))
  have hconst : Martingale (fun _ ↦ μ[g | m K]) Fblk μ :=
    martingale_const_fun Fblk μ hconstMeas integrable_condExp
  -- Proof comment: subtract the terminal constant stage from the reversed conditional-
  -- expectation martingale to obtain the centered block martingale.
  simpa [Fblk, reverseBlockFiltration] using hcond.sub hconst

/-- Helper for Theorem 12.14: on the normalized reversed block, the truncation `min j (K - N)`
is redundant because every `j ∈ range (K - N + 1)` already lies below `K - N`. -/
lemma reverseBlockIndex_eq_of_mem_range {N K j : ℕ}
    (hj : j ∈ Finset.range (K - N + 1)) :
    K - min j (K - N) = K - j := by
  -- Proof comment: membership in the normalized finite range gives the endpoint inequality
  -- `j ≤ K - N`, so the block index collapses to the direct reversal `K - j`.
  have hj_le : j ≤ K - N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.min_eq_left hj_le]

/-- Helper for Theorem 12.14: the index map `j ↦ K - j` sends the normalized block
`range (K - N + 1)` onto the original interval `Icc N K`. -/
lemma image_range_reverseBlock_eq_Icc {N K : ℕ} (hNK : N ≤ K) :
    (Finset.range (K - N + 1)).image (fun j => K - j) = Finset.Icc N K := by
  -- Proof comment: every reversed index `K - j` stays inside the block, and conversely every
  -- point of `Icc N K` is obtained from the unique preimage `K - n`.
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨j, hj, rfl⟩
    have hj_le : j ≤ K - N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hN_le : N ≤ K - j := by
      omega
    exact Finset.mem_Icc.mpr ⟨hN_le, Nat.sub_le _ _⟩
  · intro hn
    rcases Finset.mem_Icc.mp hn with ⟨hN, hK⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨K - n, Finset.mem_range.mpr ?_, ?_⟩
    · have hle : K - n ≤ K - N := Nat.sub_le_sub_left hN K
      exact Nat.lt_succ_iff.mpr hle
    · omega

omit [IsFiniteMeasure μ] in
/-- Helper for Theorem 12.14: the block oscillation over `Icc N K` is exactly the finite supremum
of the reversed block process indexed by `range (K - N + 1)`. -/
lemma blockSupAbs_eq_reverseBlockSup {m : ℕ → MeasurableSpace Ω}
    {g : Ω → ℝ} {N K : ℕ} (hNK : N ≤ K) (ω : Ω) :
    let u : ℕ → Ω → ℝ := fun n ↦ μ[g | m n]
    (Finset.Icc N K).sup' (Finset.nonempty_Icc.mpr hNK) (fun n => |u n ω - u K ω|) =
      (Finset.range (K - N + 1)).sup' Finset.nonempty_range_add_one
        (fun j => |u (K - min j (K - N)) ω - u K ω|) := by
  classical
  let u : ℕ → Ω → ℝ := fun n ↦ μ[g | m n]
  have hImage :
      (Finset.range (K - N + 1)).image (fun j => K - j) = Finset.Icc N K :=
    image_range_reverseBlock_eq_Icc hNK
  have hImageNonempty :
      ((Finset.range (K - N + 1)).image (fun j => K - j)).Nonempty :=
    Finset.nonempty_range_add_one.image (fun j => K - j)
  -- Proof comment: first rewrite the interval as the image of the reversed finite range, then
  -- collapse the residual `min` in the block index on that range.
  calc
    (Finset.Icc N K).sup' (Finset.nonempty_Icc.mpr hNK) (fun n => |u n ω - u K ω|) =
        ((Finset.range (K - N + 1)).image (fun j => K - j)).sup' hImageNonempty
          (fun n => |u n ω - u K ω|) := by
          simp [hImage]
    _ = (Finset.range (K - N + 1)).sup' Finset.nonempty_range_add_one
          (fun j => |u (K - j) ω - u K ω|) := by
            have hne : hImageNonempty.of_image = Finset.nonempty_range_add_one :=
              Subsingleton.elim _ _
            rw [Finset.sup'_image
              (s := Finset.range (K - N + 1))
              (f := fun j => K - j)
              (hs := hImageNonempty)
              (g := fun n => |u n ω - u K ω|), hne]
            rfl
    _ = (Finset.range (K - N + 1)).sup' Finset.nonempty_range_add_one
          (fun j => |u (K - min j (K - N)) ω - u K ω|) := by
            refine Finset.sup'_congr (s := Finset.range (K - N + 1))
              (H := Finset.nonempty_range_add_one) rfl ?_
            intro j hj
            simp [reverseBlockIndex_eq_of_mem_range (N := N) (K := K) hj]

/-- Helper for Theorem 12.14: the geometric `L¹` errors from the thinned subsequence are small
enough to dominate the reverse-block bad-event measures by a summable geometric sequence. -/
lemma geometricBlockTail_le_square_half (k : ℕ) :
    ((1 / 8 : ℝ) ^ (k + 2) + (1 / 8 : ℝ) ^ (k + 3)) ≤
      (((1 / 2 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ k)) := by
  have hpow : (1 / 8 : ℝ) ^ k ≤ (1 / 4 : ℝ) ^ k := by
    exact pow_le_pow_left₀ (by positivity) (by norm_num) k
  have hquarter :
      (((1 / 2 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ k)) = (1 / 4 : ℝ) ^ k := by
    rw [← pow_add]
    have hk : k + k = 2 * k := by
      omega
    rw [hk, pow_mul]
    norm_num
  calc
    ((1 / 8 : ℝ) ^ (k + 2) + (1 / 8 : ℝ) ^ (k + 3)) ≤ 2 * ((1 / 8 : ℝ) ^ (k + 2)) := by
      have hpow_succ : (1 / 8 : ℝ) ^ (k + 3) ≤ (1 / 8 : ℝ) ^ (k + 2) := by
        rw [pow_succ']
        nlinarith [show 0 ≤ (1 / 8 : ℝ) ^ (k + 2) by positivity]
      nlinarith [show 0 ≤ (1 / 8 : ℝ) ^ (k + 2) by positivity, hpow_succ]
    _ = (1 / 32 : ℝ) * (1 / 8 : ℝ) ^ k := by
      rw [pow_add, pow_two]
      ring
    _ ≤ (1 / 4 : ℝ) ^ k := by
      nlinarith [show 0 ≤ (1 / 8 : ℝ) ^ k by positivity,
        show 0 ≤ (1 / 4 : ℝ) ^ k by positivity, hpow]
    _ = (((1 / 2 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ k)) := hquarter.symm

/-- Helper for Theorem 12.14: Doob's `L¹` tail bound controls the oscillation event on one reverse
block by the `L¹` norm of the endpoint difference. -/
lemma reverseBlockSup_event_le_eLpNormOne {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ}
    {N K : ℕ} (hNK : N ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal ε *
        μ {ω |
          ε ≤ (Finset.Icc N K).sup' (Finset.nonempty_Icc.mpr hNK)
            (fun n => |μ[g | m n] ω - μ[g | m K] ω|)} ≤
      eLpNorm (μ[g | m N] - μ[g | m K]) 1 μ := by
  let Fblk : Filtration ℕ mΩ := reverseBlockFiltration (m := m) hm_le hm_anti N K
  let Y : ℕ → Ω → ℝ :=
    fun j ω ↦ μ[g | m (K - min j (K - N))] ω - μ[g | m K] ω
  have hdoob :=
    doobLp_tail_bound
      (X := Y) (ℱ := Fblk) (μ := μ)
      (Or.inl (by
        -- Proof comment: the reversed block process is already a forward martingale.
        simpa [Fblk, Y] using reverseBlockCondExp_martingale (μ := μ) (m := m) hm_le hm_anti
          (g := g) N K))
      (p := 1) (threshold := ε) (by norm_num) hε (K - N)
  have hnorm :
      (∫⁻ ω, ENNReal.ofReal |μ[g | m N] ω - μ[g | m K] ω| ∂μ) =
        eLpNorm (μ[g | m N] - μ[g | m K]) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr_ae ?_
    filter_upwards [] with ω
    simpa [Pi.sub_apply, Real.norm_eq_abs] using
      (ENNReal.ofReal_eq_coe_nnreal (abs_nonneg (μ[g | m N] ω - μ[g | m K] ω)))
  -- Proof comment: rewrite Doob's running maximum event back to the original block oscillation and
  -- identify the terminal sample with the endpoint difference.
  calc
    ENNReal.ofReal ε *
        μ {ω |
          ε ≤ (Finset.Icc N K).sup' (Finset.nonempty_Icc.mpr hNK)
            (fun n => |μ[g | m n] ω - μ[g | m K] ω|)} ≤
      ∫⁻ ω, ENNReal.ofReal |μ[g | m N] ω - μ[g | m K] ω| ∂μ := by
        simpa [Fblk, Y, Real.rpow_one,
          blockSupAbs_eq_reverseBlockSup (m := m) (g := g) hNK,
          Nat.sub_sub_self hNK] using hdoob
    _ = eLpNorm (μ[g | m N] - μ[g | m K]) 1 μ := hnorm

/-- Helper for Theorem 12.14: after thinning to the geometric subsequence, the reverse-block bad
events have a finite total mass. -/
lemma summableReverseBlockBadEvents {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg : Integrable g μ) :
    ∃ N : ℕ → ℕ, ∃ hN : StrictMono N,
      (∀ᵐ ω ∂μ, Tendsto (fun k ↦ μ[g | m (N k)] ω) atTop (𝓝 (μ[g | ⨅ n : ℕ, m n] ω))) ∧
      ((∑' k : ℕ,
          μ {ω |
            (((1 : ℝ) / 2) ^ k) ≤
              (Finset.Icc (N k) (N (k + 1))).sup'
                (Finset.nonempty_Icc.mpr (Nat.le_of_lt (hN (Nat.lt_succ_self k))))
                (fun n => |μ[g | m n] ω - μ[g | m (N (k + 1))] ω|)}) < (⊤ : ENNReal)) := by
  obtain ⟨N, hN, hNae, hgeom⟩ :=
    existsGeometricCondExpSubseq (μ := μ) (m := m) hm_le hm_anti hg
  let A : ℕ → Set Ω := fun k ↦
    {ω |
      (((1 : ℝ) / 2) ^ k) ≤
        (Finset.Icc (N k) (N (k + 1))).sup'
          (Finset.nonempty_Icc.mpr (Nat.le_of_lt (hN (Nat.lt_succ_self k))))
          (fun n => |μ[g | m n] ω - μ[g | m (N (k + 1))] ω|)}
  have hiInf_le : (⨅ n : ℕ, m n) ≤ mΩ := by
    exact (iInf_le (fun n : ℕ ↦ m n) 0).trans (hm_le 0)
  have hOneEighth : ((1 : ENNReal) / 8) = ENNReal.ofReal (1 / 8 : ℝ) := by
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num]
    rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 8 by norm_num)]
  have hA : ∀ k : ℕ, μ (A k) ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ k) := by
    intro k
    have hNk : N k ≤ N (k + 1) := Nat.le_of_lt (hN (Nat.lt_succ_self k))
    have hleftMeas :
        AEStronglyMeasurable (μ[g | m (N k)] - μ[g | ⨅ n : ℕ, m n]) μ :=
      ((stronglyMeasurable_condExp.mono (hm_le (N k))).aestronglyMeasurable).sub
        ((stronglyMeasurable_condExp.mono hiInf_le).aestronglyMeasurable)
    have hrightMeas :
        AEStronglyMeasurable (μ[g | ⨅ n : ℕ, m n] - μ[g | m (N (k + 1))]) μ :=
      ((stronglyMeasurable_condExp.mono hiInf_le).aestronglyMeasurable).sub
        ((stronglyMeasurable_condExp.mono (hm_le (N (k + 1)))).aestronglyMeasurable)
    have hsplit :
        eLpNorm (μ[g | m (N k)] - μ[g | m (N (k + 1))]) 1 μ ≤
          eLpNorm (μ[g | m (N k)] - μ[g | ⨅ n : ℕ, m n]) 1 μ +
            eLpNorm (μ[g | ⨅ n : ℕ, m n] - μ[g | m (N (k + 1))]) 1 μ := by
      calc
        eLpNorm (μ[g | m (N k)] - μ[g | m (N (k + 1))]) 1 μ =
            eLpNorm
              ((μ[g | m (N k)] - μ[g | ⨅ n : ℕ, m n]) +
                (μ[g | ⨅ n : ℕ, m n] - μ[g | m (N (k + 1))])) 1 μ := by
                  refine eLpNorm_congr_ae ?_
                  filter_upwards [] with ω
                  simp [Pi.sub_apply]
        _ ≤
            eLpNorm (μ[g | m (N k)] - μ[g | ⨅ n : ℕ, m n]) 1 μ +
              eLpNorm (μ[g | ⨅ n : ℕ, m n] - μ[g | m (N (k + 1))]) 1 μ := by
                exact eLpNorm_add_le hleftMeas hrightMeas le_rfl
    have hgeomBound :
        eLpNorm (μ[g | m (N k)] - μ[g | m (N (k + 1))]) 1 μ ≤
          ENNReal.ofReal ((((1 / 2 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ k))) := by
      calc
        eLpNorm (μ[g | m (N k)] - μ[g | m (N (k + 1))]) 1 μ ≤
            eLpNorm (μ[g | m (N k)] - μ[g | ⨅ n : ℕ, m n]) 1 μ +
              eLpNorm (μ[g | ⨅ n : ℕ, m n] - μ[g | m (N (k + 1))]) 1 μ := hsplit
        _ ≤
            ((1 : ENNReal) / 8) ^ (k + 2) + ((1 : ENNReal) / 8) ^ (k + 3) := by
              exact add_le_add (hgeom k).le (by simpa [eLpNorm_sub_comm] using (hgeom (k + 1)).le)
        _ = ENNReal.ofReal (((1 / 8 : ℝ) ^ (k + 2)) + ((1 / 8 : ℝ) ^ (k + 3))) := by
          have hpow1 : ((1 : ENNReal) / 8) ^ (k + 2) = ENNReal.ofReal ((1 / 8 : ℝ) ^ (k + 2)) := by
            rw [hOneEighth, ENNReal.ofReal_pow (by positivity)]
          have hpow2 : ((1 : ENNReal) / 8) ^ (k + 3) = ENNReal.ofReal ((1 / 8 : ℝ) ^ (k + 3)) := by
            rw [hOneEighth, ENNReal.ofReal_pow (by positivity)]
          rw [hpow1, hpow2, ← ENNReal.ofReal_add]
          · positivity
          · positivity
        _ ≤ ENNReal.ofReal ((((1 / 2 : ℝ) ^ k) * ((1 / 2 : ℝ) ^ k))) := by
          exact ENNReal.ofReal_le_ofReal (geometricBlockTail_le_square_half k)
    have hdoob :
        ENNReal.ofReal (((1 : ℝ) / 2) ^ k) * μ (A k) ≤
          eLpNorm (μ[g | m (N k)] - μ[g | m (N (k + 1))]) 1 μ := by
      simpa [A] using
        reverseBlockSup_event_le_eLpNormOne (μ := μ) (m := m) hm_le hm_anti (g := g)
          (N := N k) (K := N (k + 1)) hNk (ε := ((1 : ℝ) / 2) ^ k) (by positivity)
    have hk0 : ENNReal.ofReal (((1 : ℝ) / 2) ^ k) ≠ 0 := by
      positivity
    have hmul :
        ENNReal.ofReal (((1 : ℝ) / 2) ^ k) * μ (A k) ≤
          ENNReal.ofReal (((1 : ℝ) / 2) ^ k) * ENNReal.ofReal (((1 : ℝ) / 2) ^ k) := by
      exact hdoob.trans (by
        simpa [ENNReal.ofReal_mul] using hgeomBound)
    have hmul' :
        μ (A k) * ENNReal.ofReal (((1 : ℝ) / 2) ^ k) ≤
          ENNReal.ofReal (((1 : ℝ) / 2) ^ k) * ENNReal.ofReal (((1 : ℝ) / 2) ^ k) := by
      simpa [mul_comm] using hmul
    exact (ENNReal.mul_le_mul_iff_left hk0 ENNReal.ofReal_ne_top).1 hmul'
  have hgeomSummable : Summable (fun k : ℕ ↦ (((1 : ℝ) / 2) : ℝ) ^ k) :=
    summable_geometric_two
  have hgeom_ne_top :
      (∑' k : ℕ, ENNReal.ofReal ((((1 : ℝ) / 2) : ℝ) ^ k)) ≠ ⊤ := by
    simpa using hgeomSummable.tsum_ofReal_ne_top
  have hsum_lt_top : (∑' k : ℕ, μ (A k)) < (⊤ : ENNReal) := by
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hA) ?_
    exact lt_top_iff_ne_top.mpr hgeom_ne_top
  exact ⟨N, hN, hNae, hsum_lt_top⟩

/-- Helper for Theorem 12.14: on the geometric subsequence, almost every sample path has
eventually small oscillation on each adjacent reverse block. -/
lemma ae_eventually_small_reverseBlocks {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg : Integrable g μ) :
    ∃ N : ℕ → ℕ, ∃ _ : StrictMono N,
      (∀ᵐ ω ∂μ, Tendsto (fun k ↦ μ[g | m (N k)] ω) atTop (𝓝 (μ[g | ⨅ n : ℕ, m n] ω))) ∧
      ∀ᵐ ω ∂μ, ∀ᶠ k in atTop,
        ∀ n ∈ Finset.Icc (N k) (N (k + 1)),
          |μ[g | m n] ω - μ[g | m (N (k + 1))] ω| < (((1 : ℝ) / 2) ^ k) := by
  obtain ⟨N, hN, hNae, hsum⟩ :=
    summableReverseBlockBadEvents (μ := μ) (m := m) hm_le hm_anti hg
  let A : ℕ → Set Ω := fun k ↦
    {ω |
      (((1 : ℝ) / 2) ^ k) ≤
        (Finset.Icc (N k) (N (k + 1))).sup'
          (Finset.nonempty_Icc.mpr (Nat.le_of_lt (hN (Nat.lt_succ_self k))))
          (fun n => |μ[g | m n] ω - μ[g | m (N (k + 1))] ω|)}
  refine ⟨N, hN, hNae, ?_⟩
  filter_upwards [MeasureTheory.ae_eventually_notMem (μ := μ) (s := A) hsum.ne] with ω hω
  refine hω.mono ?_
  intro k hk n hn
  have hsup_lt :
      (Finset.Icc (N k) (N (k + 1))).sup'
          (Finset.nonempty_Icc.mpr (Nat.le_of_lt (hN (Nat.lt_succ_self k))))
          (fun n => |μ[g | m n] ω - μ[g | m (N (k + 1))] ω|) < (((1 : ℝ) / 2) ^ k) := by
    exact not_le.mp hk
  exact
    (Finset.le_sup' (s := Finset.Icc (N k) (N (k + 1)))
      (f := fun j => |μ[g | m j] ω - μ[g | m (N (k + 1))] ω|) hn).trans_lt hsup_lt

/-- Helper for Theorem 12.14: `Nat.findGreatest` places every large index inside the adjacent
strict-mono block determined by the largest stage below it. -/
lemma blockIndex_memIcc_of_strictMono {N : ℕ → ℕ} (hN : StrictMono N) {n : ℕ}
    (hn : N 0 ≤ n) :
    let k := Nat.findGreatest (fun j ↦ N j ≤ n) n
    n ∈ Finset.Icc (N k) (N (k + 1)) := by
  let k := Nat.findGreatest (fun j ↦ N j ≤ n) n
  -- Proof comment: the `findGreatest` index is, by definition, the last stage below `n`.
  change n ∈ Finset.Icc (N k) (N (k + 1))
  rw [Finset.mem_Icc]
  constructor
  · simpa [k] using
      Nat.findGreatest_spec (P := fun j ↦ N j ≤ n) (m := 0) (Nat.zero_le n) hn
  · -- Proof comment: if the next stage were still below `n`, the chosen index would not be
    -- maximal.
    by_contra hUpper
    have hkUpper : N (k + 1) ≤ n := le_of_lt (not_le.mp hUpper)
    have hkLe : k + 1 ≤ n := by
      exact le_trans (StrictMono.id_le hN (k + 1)) hkUpper
    have hnot : ¬ N (k + 1) ≤ n := by
      exact
        Nat.findGreatest_is_greatest (P := fun j ↦ N j ≤ n) (k := k + 1) (n := n)
          (by simp [k]) hkLe
    exact hnot hkUpper

/-- Helper for Theorem 12.14: a convergent strict-mono subsequence plus vanishing oscillation on
the adjacent blocks forces convergence of the whole real sequence. -/
lemma tendsto_of_tendsto_subseq_of_eventuallySmallBlocks
    {u : ℕ → ℝ} {c : ℝ} {N : ℕ → ℕ} (hN : StrictMono N)
    (hsub : Tendsto (fun k ↦ u (N k)) atTop (𝓝 c))
    (hblock :
      ∀ᶠ k in atTop, ∀ n ∈ Finset.Icc (N k) (N (k + 1)),
        |u n - u (N (k + 1))| < (((1 : ℝ) / 2) ^ k)) :
    Tendsto u atTop (𝓝 c) := by
  have hsubShift : Tendsto (fun k ↦ u (N (k + 1))) atTop (𝓝 c) := by
    -- Proof comment: shifting the subsequence by one step keeps the same limit.
    simpa [Function.comp] using hsub.comp (tendsto_add_atTop_nat 1)
  have hgeom : Tendsto (fun k : ℕ ↦ (((1 : ℝ) / 2) ^ k)) atTop (𝓝 0) := by
    -- Proof comment: the geometric block radii shrink to `0`.
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hεhalf : 0 < ε / 2 := by positivity
  have hsubHalf : ∀ᶠ k in atTop, |u (N (k + 1)) - c| < ε / 2 := by
    simpa [Real.dist_eq, abs_sub_comm] using Metric.tendsto_atTop.1 hsubShift (ε / 2) hεhalf
  have hgeomHalf : ∀ᶠ k in atTop, (((1 : ℝ) / 2) ^ k) < ε / 2 := by
    have habs : ∀ᶠ k in atTop, |(((1 : ℝ) / 2) ^ k)| < ε / 2 := by
      simpa [Real.dist_eq] using Metric.tendsto_atTop.1 hgeom (ε / 2) hεhalf
    filter_upwards [habs] with k hk
    have hnonneg : 0 ≤ (((1 : ℝ) / 2) ^ k) := by positivity
    simpa [abs_of_nonneg hnonneg] using hk
  have hAll :
      ∀ᶠ k in atTop,
        (∀ n ∈ Finset.Icc (N k) (N (k + 1)),
            |u n - u (N (k + 1))| < (((1 : ℝ) / 2) ^ k)) ∧
          |u (N (k + 1)) - c| < ε / 2 ∧ (((1 : ℝ) / 2) ^ k) < ε / 2 := by
    filter_upwards [hblock, hsubHalf, hgeomHalf] with k hkBlock hkSub hkGeom
    exact ⟨hkBlock, hkSub, hkGeom⟩
  rcases eventually_atTop.1 hAll with ⟨K, hK⟩
  refine ⟨N K, ?_⟩
  intro n hn
  let k := Nat.findGreatest (fun j ↦ N j ≤ n) n
  have hn0 : N 0 ≤ n := le_trans (hN.monotone (Nat.zero_le K)) hn
  have hkMem : n ∈ Finset.Icc (N k) (N (k + 1)) := by
    -- Proof comment: every large index belongs to the block indexed by its greatest lower stage.
    simpa [k] using blockIndex_memIcc_of_strictMono (N := N) hN hn0
  have hk_ge : K ≤ k := by
    -- Proof comment: the threshold block index is itself admissible for the `findGreatest`
    -- predicate once `n ≥ N K`.
    refine Nat.le_findGreatest ?_ hn
    exact le_trans (StrictMono.id_le hN K) hn
  have hkData := hK k hk_ge
  have hkBlock : |u n - u (N (k + 1))| < (((1 : ℝ) / 2) ^ k) := hkData.1 n hkMem
  have hkSub : |u (N (k + 1)) - c| < ε / 2 := hkData.2.1
  have hkGeom : (((1 : ℝ) / 2) ^ k) < ε / 2 := hkData.2.2
  have htriangle : |u n - c| ≤ |u n - u (N (k + 1))| + |u (N (k + 1)) - c| := by
    -- Proof comment: compare `u n` to the common limit through the right endpoint of its block.
    simpa [abs_sub_comm] using abs_sub_le (u n) (u (N (k + 1))) c
  have hsum : |u n - u (N (k + 1))| + |u (N (k + 1)) - c| < ε := by
    have hmid :
        |u n - u (N (k + 1))| + |u (N (k + 1)) - c| <
          (((1 : ℝ) / 2) ^ k) + ε / 2 :=
      add_lt_add hkBlock hkSub
    have hsmall : (((1 : ℝ) / 2) ^ k) + ε / 2 < ε := by
      calc
        (((1 : ℝ) / 2) ^ k) + ε / 2 < ε / 2 + ε / 2 := by
          simpa [add_comm] using add_lt_add_right hkGeom (ε / 2)
        _ = ε := by ring
    exact lt_trans hmid hsmall
  -- Proof comment: the triangle bound and the two `ε / 2` estimates close the metric criterion.
  simpa [Real.dist_eq] using lt_of_le_of_lt htriangle hsum

/-- Helper for Theorem 12.14: the reverse conditional-expectation sequence admits an almost-
everywhere pointwise limit along the full antitone family. -/
private lemma aeExistsPointwiseLimit_condExp_iInf_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg : Integrable g μ) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n ↦ μ[g | m n] ω) atTop (𝓝 c) := by
  -- Route correction: the reverse-block Doob estimate and Borel-Cantelli bridge are now in place.
  obtain ⟨N, hN, hNae, hBlockAe⟩ :=
    ae_eventually_small_reverseBlocks (μ := μ) (m := m) hm_le hm_anti hg
  -- Proof comment: on the full-measure event where both the subsequence convergence and the block
  -- oscillation control hold, the generic sequence lemma upgrades the geometric subsequence to the
  -- whole reverse conditional-expectation sequence.
  filter_upwards [hNae, hBlockAe] with ω hωsub hωblock
  refine ⟨μ[g | ⨅ n : ℕ, m n] ω, ?_⟩
  exact
    tendsto_of_tendsto_subseq_of_eventuallySmallBlocks (N := N) hN hωsub hωblock

/-- Helper for Theorem 12.14: reverse Lévy almost-sure convergence for an antitone family of
sub-`σ`-algebras. -/
lemma tendsto_ae_condExp_iInf_of_antitone {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m) {g : Ω → ℝ} (hg : Integrable g μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[g | m n] ω) atTop (𝓝 (μ[g | ⨅ n : ℕ, m n] ω)) := by
  classical
  -- Route correction: package the eventual pointwise limit as a theorem-local function first, then
  -- identify it with the canonical tail conditional expectation by uniqueness in measure.
  let l : Ω → ℝ := fun ω =>
    if h : ∃ c, Tendsto (fun n ↦ μ[g | m n] ω) atTop (𝓝 c) then h.choose else 0
  have hExists :
      ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n ↦ μ[g | m n] ω) atTop (𝓝 c) :=
    aeExistsPointwiseLimit_condExp_iInf_of_antitone (μ := μ) (m := m) hm_le hm_anti hg
  have hTendsto_l :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[g | m n] ω) atTop (𝓝 (l ω)) := by
    -- Proof comment: on the full-measure event where a limit exists, `l ω` is defined to be that
    -- chosen limit, so the sequence converges to `l ω` by construction.
    filter_upwards [hExists] with ω hω
    simp [l, hω, hω.choose_spec]
  have hl_eq :
      l =ᵐ[μ] μ[g | ⨅ n : ℕ, m n] :=
    aeEq_limit_condExp_iInf_of_antitone (μ := μ) (m := m) hm_le hm_anti hg hTendsto_l
  -- Proof comment: rewrite the chosen pointwise limit by the canonical tail conditional
  -- expectation, which gives the announced almost-sure convergence statement.
  filter_upwards [hTendsto_l, hl_eq] with ω hωt hωeq
  simpa [hωeq] using hωt

/-- Helper for Theorem 12.14: reverse Lévy almost-sure convergence for the decreasing family
`n ↦ ℱ (toDual n)`. -/
lemma tendsto_ae_condExp_tail_orderDual {g : Ω → ℝ} (hg : Integrable g μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[g | ℱ (toDual n)] ω) atTop (𝓝 (μ[g | 𝓕∞] ω)) := by
  -- Proof comment: reduce the order-dual statement to the generic antitone-family theorem and
  -- rewrite the limit `σ`-algebra using the tail/intersection identity proved above.
  have htail : 𝓕∞ = ⨅ n : ℕ, ℱ (toDual n) := tailMeasurableSpace_orderDual_eq_iInfStages (ℱ := ℱ)
  simpa [htail] using
    tendsto_ae_condExp_iInf_of_antitone (μ := μ) (m := fun n : ℕ ↦ ℱ (toDual n))
      (hm_le := fun n ↦ ℱ.le (toDual n)) orderDualStages_antitone hg

/-- Helper for Theorem 12.14: reverse Lévy `L¹` convergence for the decreasing family
`n ↦ ℱ (toDual n)`. -/
lemma tendsto_eLpNorm_condExp_tail_orderDual {g : Ω → ℝ} (hg : Integrable g μ) :
    Tendsto
      (fun n ↦ eLpNorm (μ[g | ℱ (toDual n)] - μ[g | 𝓕∞]) 1 μ)
      atTop (𝓝 0) := by
  -- Proof comment: the backward `L¹` theorem is the same antitone-family statement after the
  -- order-dual tail algebra is rewritten as an infimum of stages.
  have htail : 𝓕∞ = ⨅ n : ℕ, ℱ (toDual n) := tailMeasurableSpace_orderDual_eq_iInfStages (ℱ := ℱ)
  simpa [htail] using
    tendsto_eLpNorm_condExp_iInf_of_antitone (μ := μ) (m := fun n : ℕ ↦ ℱ (toDual n))
      (hm_le := fun n ↦ ℱ.le (toDual n)) orderDualStages_antitone hg

-- Proof sketch: use the martingale identity on `ℕᵒᵈ` to rewrite `X (toDual n)` as the
-- conditional expectation of `X 0` with respect to the decreasing σ-algebra `ℱ (toDual n)`, then
-- apply the owner-level Lévy conditional-expectation convergence theorem for the resulting tail
-- `σ`-algebra.
/-- Theorem 12.14 (1): a real-valued backward martingale converges almost surely to the canonical
tail conditional expectation `𝔼[X₀ | 𝓕_{-∞}]`. -/
theorem backward_martingale_ae_tendsto_limit (hX : Martingale X ℱ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (toDual n) ω) atTop
      (𝓝 (μ[X 0 | 𝓕∞] ω)) := by
  -- Proof comment: rewrite the backward martingale stages as conditional expectations of `X 0`
  -- and then invoke the reverse Lévy helper.
  have hcond :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ μ[X 0 | ℱ (toDual n)] ω) atTop (𝓝 (μ[X 0 | 𝓕∞] ω)) :=
    tendsto_ae_condExp_tail_orderDual (ℱ := ℱ) (μ := μ) (g := X 0) (hX.integrable 0)
  have hstage :
      ∀ᵐ ω ∂μ, ∀ n, X (toDual n) ω = μ[X 0 | ℱ (toDual n)] ω := by
    rw [ae_all_iff]
    intro n
    exact backwardMartingale_aeEq_condExpAtZero (μ := μ) (ℱ := ℱ) (X := X) hX n
  filter_upwards [hstage, hcond] with ω hω hcondω
  have hfun : (fun n ↦ X (toDual n) ω) = fun n ↦ μ[X 0 | ℱ (toDual n)] ω := by
    funext n
    exact hω n
  simpa [hfun] using hcondω

-- Proof sketch: after identifying `X (toDual n)` with `𝔼[X₀ | ℱ (toDual n)]`, apply the
-- `L¹` owner theorem for conditional expectations along the decreasing tail family.
/-- Theorem 12.14 (2): the same backward martingale converges in `L¹` to the canonical tail
conditional expectation `𝔼[X₀ | 𝓕_{-∞}]`. -/
theorem backward_martingale_tendsto_eLpNorm_one_limit (hX : Martingale X ℱ μ) :
    Tendsto
      (fun n ↦ eLpNorm (X (toDual n) - μ[X 0 | 𝓕∞]) 1 μ)
      atTop (𝓝 0) := by
  -- Proof comment: move the process inside the norm onto the canonical conditional-expectation
  -- family by almost-everywhere congruence, then apply the reverse Lévy `L¹` helper.
  have hcond :
      Tendsto
        (fun n ↦ eLpNorm (μ[X 0 | ℱ (toDual n)] - μ[X 0 | 𝓕∞]) 1 μ)
        atTop (𝓝 0) :=
    tendsto_eLpNorm_condExp_tail_orderDual (ℱ := ℱ) (μ := μ) (g := X 0) (hX.integrable 0)
  have hnorm :
      (fun n ↦ eLpNorm (X (toDual n) - μ[X 0 | 𝓕∞]) 1 μ) =
        fun n ↦ eLpNorm (μ[X 0 | ℱ (toDual n)] - μ[X 0 | 𝓕∞]) 1 μ := by
    funext n
    refine eLpNorm_congr_ae ?_
    filter_upwards [backwardMartingale_aeEq_condExpAtZero (μ := μ) (ℱ := ℱ) (X := X) hX n] with
      ω hω
    simp [hω]
  simpa [hnorm] using hcond

end BackwardMartingale
