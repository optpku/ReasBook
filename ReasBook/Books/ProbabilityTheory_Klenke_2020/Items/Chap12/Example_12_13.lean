/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open OrderDual
open scoped BigOperators

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The zero-based Cesàro average of the first `n + 1` coordinates of a real-valued process. -/
noncomputable def exchangeableCesaroAverage (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), X i ω

section

omit [MeasurableSpace Ω]

-- Proof sketch: unfold `exchangeableCesaroAverage`; this is its defining formula.
/-- Unfolding `exchangeableCesaroAverage` gives the average over the first `n + 1` coordinates. -/
theorem exchangeableCesaroAverage_def (X : ℕ → Ω → ℝ) (n : ℕ) :
    exchangeableCesaroAverage X n =
      fun ω ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), X i ω := rfl

end

/-- The backwards empirical-mean process on `ℕᵒᵈ`, using zero-based indexing to formalize the
textbook variables `Y_{-n}` by `n ↦ (n + 1)⁻¹ ∑_{i = 0}^n Xᵢ`. -/
noncomputable abbrev exchangeableBackwardAverageProcess (X : ℕ → Ω → ℝ) :
    ℕᵒᵈ → Ω → ℝ :=
  fun n ↦ exchangeableCesaroAverage X (ofDual n)

-- Proof sketch: measurability into the countable product `ℝ^ℕ` is equivalent to coordinatewise
-- measurability, and each coordinate map is one of the given strongly measurable random variables.
private theorem measurable_processSwap {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n)) :
    Measurable (Function.swap X) := by
  rw [measurable_pi_iff]
  intro n
  simpa [Function.swap] using hX_meas n

omit [MeasurableSpace Ω] in
/-- Local helper: on the first `n` coordinates, `permutePrefix n ρ` acts by `ρ`. -/
private theorem permutePrefix_apply_finLocal {n : ℕ} (ρ : Equiv.Perm (Fin n)) (x : ℕ → ℝ)
    (i : Fin n) :
    permutePrefix n ρ x i = x (ρ i) := by
  simp [permutePrefix, Equiv.Perm.extendDomain_apply_subtype]

omit [MeasurableSpace Ω] in
/-- Local helper: extending a finite prefix permutation along `Fin.castLEEmb`
preserves the induced action on sequence space. -/
private theorem permutePrefix_viaFintypeEmbeddingLocal {m n : ℕ} (hmn : m ≤ n)
    (ρ : Equiv.Perm (Fin m)) (x : ℕ → ℝ) :
    permutePrefix n (ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) x = permutePrefix m ρ x := by
  funext i
  by_cases hin : i < n
  · by_cases him : i < m
    · let im : Fin m := ⟨i, him⟩
      let in' : Fin n := ⟨i, hin⟩
      have hin_eq : Fin.castLEEmb hmn im = in' := by
        ext
        rfl
      -- On the shared prefix, the embedded permutation acts exactly like `ρ`.
      have hleft :
          permutePrefix n (ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) x i =
            x ((ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) in') := by
        simpa [in'] using
          (permutePrefix_apply_finLocal (ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) x in')
      have hmid :
          x ((ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) in') = x (Fin.castLEEmb hmn (ρ im)) := by
        rw [← hin_eq]
        simpa using
          congrArg (fun j : Fin n ↦ x j)
            (Equiv.Perm.viaFintypeEmbedding_apply_image ρ (Fin.castLEEmb hmn) im)
      have hright :
          permutePrefix m ρ x i = x (ρ im) := by
        simpa [im] using (permutePrefix_apply_finLocal ρ x im)
      calc
        permutePrefix n (ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) x i =
            x ((ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) in') := hleft
        _ = x (Fin.castLEEmb hmn (ρ im)) := hmid
        _ = x (ρ im) := by
              rfl
        _ = permutePrefix m ρ x i := hright.symm
    · let in' : Fin n := ⟨i, hin⟩
      have hnotRange : in' ∉ Set.range (Fin.castLEEmb hmn) := by
        intro hmem
        rcases hmem with ⟨j, hj⟩
        have hji : (j : ℕ) = i := by
          simpa [in'] using congrArg Fin.val hj
        exact him (by simpa [hji] using j.2)
      have hfix :
          (ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) in' = in' :=
        Equiv.Perm.viaFintypeEmbedding_apply_notMem_range ρ (Fin.castLEEmb hmn) hnotRange
      have hleft :
          permutePrefix n (ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) x i =
            x ((ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) in') := by
        simpa [in'] using
          (permutePrefix_apply_finLocal (ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) x in')
      have hright : permutePrefix m ρ x i = x i := by
        have hfixm :
            (ρ.extendDomain Fin.equivSubtype) i = i :=
          Equiv.Perm.extendDomain_apply_not_subtype ρ Fin.equivSubtype
            (Nat.not_lt_of_ge (le_of_not_gt him))
        simpa [permutePrefix] using congrArg x hfixm
      -- Outside the shorter prefix, the extension fixes the index.
      calc
        permutePrefix n (ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) x i =
            x ((ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) in') := hleft
        _ = x i := by
              rw [hfix]
        _ = permutePrefix m ρ x i := hright.symm
  · have hmn' : m ≤ i := le_trans hmn (le_of_not_gt hin)
    have hleft :
        permutePrefix n (ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) x i = x i := by
      have hfixn :
          ((ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)).extendDomain Fin.equivSubtype) i = i :=
        Equiv.Perm.extendDomain_apply_not_subtype
          (ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)) Fin.equivSubtype
          (Nat.not_lt_of_ge (le_of_not_gt hin))
      simpa [permutePrefix] using congrArg x hfixn
    have hright : permutePrefix m ρ x i = x i := by
      have hfixm :
          (ρ.extendDomain Fin.equivSubtype) i = i :=
        Equiv.Perm.extendDomain_apply_not_subtype ρ Fin.equivSubtype
          (Nat.not_lt_of_ge hmn')
      simpa [permutePrefix] using congrArg x hfixm
    rw [hleft, hright]

omit [MeasurableSpace Ω] in
/-- Local helper: the sequence-space finite symmetric `σ`-algebras are antitone in
the prefix length. -/
private theorem nSymmetricSequenceSigmaAlgebra_antitoneLocal :
    Antitone (fun n : ℕ ↦ (nSymmetricSequenceSigmaAlgebra n : MeasurableSpace (ℕ → ℝ))) := by
  intro m n hmn s hs
  rw [measurableSet_nSymmetricSequenceSigmaAlgebra_iff] at hs ⊢
  rcases hs with ⟨hs_meas, hs_symm⟩
  refine ⟨hs_meas, ?_⟩
  intro ρ
  let ρ' : Equiv.Perm (Fin n) := ρ.viaFintypeEmbedding (Fin.castLEEmb hmn)
  -- Extend a permutation of the shorter prefix to compare the two invariance conditions.
  have hpre :
      permutePrefix m ρ ⁻¹' s = permutePrefix n ρ' ⁻¹' s := by
    ext x
    simp [ρ', permutePrefix_viaFintypeEmbeddingLocal hmn ρ x]
  simpa [hpre] using hs_symm ρ'

-- Proof sketch: enlarging the number of coordinates that may be permuted imposes more symmetry,
-- so the corresponding exchangeable stage `σ`-algebras form a decreasing family in `n`.
omit [MeasurableSpace Ω] in
/-- Local helper: the finite exchangeable stage `σ`-algebras decrease with the prefix length. -/
private theorem exchangeableStage_antitone (X : ℕ → Ω → ℝ) :
    Antitone fun n : ℕ ↦ nExchangeableSigmaAlgebra (Function.swap X) n := by
  intro m n hmn
  -- Pull the sequence-space antitonicity statement back along the sample-sequence map.
  exact MeasurableSpace.comap_mono (nSymmetricSequenceSigmaAlgebra_antitoneLocal hmn)

-- Proof sketch: reverse the order on `ℕ+`; the previous antitonicity statement becomes the
-- monotonicity condition required for a filtration indexed by `OrderDual ℕ`.
omit [MeasurableSpace Ω] in
/-- Local helper: the reversed exchangeable stages form a monotone filtration on
`ℕᵒᵈ`. -/
private theorem exchangeableBackwardStage_mono (X : ℕ → Ω → ℝ) :
    Monotone fun n : ℕᵒᵈ ↦
      nExchangeableSigmaAlgebra (Function.swap X) (ofDual n + 1) := by
  intro i j hij
  -- Reversing the index order turns the previous antitone family into a monotone filtration.
  simpa using
    (exchangeableStage_antitone X (Nat.succ_le_succ hij))

-- Proof sketch: this is the canonical stage-inclusion theorem `nExchangeableSigmaAlgebra_le`
-- from Definition 12.6, specialized to the measurable sample-sequence map of `X`.
private theorem exchangeableBackwardStage_le (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, Measurable (X n)) (n : ℕᵒᵈ) :
    nExchangeableSigmaAlgebra (Function.swap X) (ofDual n + 1) ≤
      ‹MeasurableSpace Ω› := by
  exact nExchangeableSigmaAlgebra_le (measurable_processSwap hX_meas) (ofDual n + 1)

/-- The backwards filtration `ℱ_{-n} = ℰ_{n + 1}` associated with an exchangeable real sequence
in the canonical zero-based `ℕᵒᵈ` indexing. -/
abbrev exchangeableBackwardFiltration (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, Measurable (X n)) :
    Filtration ℕᵒᵈ ‹MeasurableSpace Ω› where
  seq n := nExchangeableSigmaAlgebra (Function.swap X) (ofDual n + 1)
  mono' := exchangeableBackwardStage_mono X
  le' := exchangeableBackwardStage_le X hX_meas

omit [MeasurableSpace Ω] in
/-- Local helper: the owner exchangeable average of the first coordinate agrees with the local
Cesàro-average notation after composing with `Function.swap X`. -/
private theorem exchangeableAverageApplyZero_comp_swap_eq_exchangeableCesaroAverage
    (X : ℕ → Ω → ℝ) (n : ℕ) :
    exchangeableAverage (n + 1) (fun x ↦ x 0) ∘ Function.swap X =
      exchangeableCesaroAverage X n := by
  funext ω
  -- Rewrite the owner average by its explicit first-coordinate formula.
  have h_average :=
    congrArg (fun f ↦ f (Function.swap X ω))
      (exchangeableAverage_apply_zero ⟨n + 1, Nat.succ_pos n⟩)
  have h_sum :
      (∑ i : Fin (n + 1), X i ω) = ∑ i ∈ Finset.range (n + 1), X i ω := by
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) (n + 1))
  have h_cesaro := congrArg (fun f ↦ f ω) (exchangeableCesaroAverage_def X n)
  calc
    exchangeableAverage (n + 1) (fun x ↦ x 0) (Function.swap X ω) =
        (∑ i : Fin (n + 1), X i ω) / ((n + 1 : ℕ) : ℝ) := by
          simpa [Function.swap] using h_average
    _ = (∑ i ∈ Finset.range (n + 1), X i ω) / ((n + 1 : ℕ) : ℝ) := by rw [h_sum]
    _ = (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), X i ω) := by
          rw [div_eq_mul_inv, mul_comm]
    _ = exchangeableCesaroAverage X n ω := by
          simpa using h_cesaro.symm

-- Proof sketch: each time `n`, `exchangeableCesaroAverage X n` is a finite linear combination of
-- the strongly measurable coordinates `X 0, …, X n`.
/-- The backwards empirical-mean process is strongly measurable at every reversed time index. -/
theorem exchangeableBackwardAverageProcess_stronglyMeasurable {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n)) (n : ℕᵒᵈ) :
    StronglyMeasurable (exchangeableBackwardAverageProcess X n) := by
  change StronglyMeasurable (exchangeableCesaroAverage X (ofDual n))
  rw [exchangeableCesaroAverage_def]
  -- Rewrite the Cesàro average as a constant multiple of a finite sum of measurable coordinates.
  have hsum :
      Measurable (fun ω ↦ ∑ i ∈ Finset.range (ofDual n + 1), X i ω) := by
    exact Finset.measurable_sum (Finset.range (ofDual n + 1))
      (fun i hi ↦ hX_meas i)
  exact (measurable_const.mul hsum).stronglyMeasurable

omit [MeasurableSpace Ω] in
/-- Helper for Example 12.13: prefix permutations act measurably on real sequence space. -/
private theorem measurable_permutePrefixLocal (n : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Measurable (permutePrefix n ρ : (ℕ → ℝ) → ℕ → ℝ) := by
  -- Proof comment: each output coordinate is evaluation at the extended permutation of the index.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [permutePrefix, Function.comp] using
    (measurable_pi_apply ((ρ.extendDomain Fin.equivSubtype) i) :
      Measurable fun x : ℕ → ℝ ↦ x ((ρ.extendDomain Fin.equivSubtype) i))

/-- Helper for Example 12.13: each backward empirical mean is strongly measurable with respect to
its reversed exchangeable stage. -/
private theorem exchangeableBackwardAverageProcess_stageStronglyMeasurable {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n)) (n : ℕᵒᵈ) :
    StronglyMeasurable[(exchangeableBackwardFiltration X hX_meas) n]
      (exchangeableBackwardAverageProcess X n) := by
  let φ : (ℕ → ℝ) → ℝ := fun x ↦ x 0
  have hφ_meas : Measurable φ := measurable_pi_apply 0
  -- Proof comment: first place the owner average in the symmetric sequence `σ`-algebra.
  have havg_stage :
      Measurable[nSymmetricSequenceSigmaAlgebra (ofDual n + 1)]
        (exchangeableAverage (ofDual n + 1) φ : (ℕ → ℝ) → ℝ) := by
    have havg_meas : Measurable (exchangeableAverage (ofDual n + 1) φ : (ℕ → ℝ) → ℝ) := by
      have hsum :
          Measurable (fun x : ℕ → ℝ ↦
            (∑ ρ : Equiv.Perm (Fin (ofDual n + 1)),
              φ (permutePrefix (ofDual n + 1) ρ x) : ℝ)) := by
        simpa [φ] using
          (Finset.measurable_sum (Finset.univ : Finset (Equiv.Perm (Fin (ofDual n + 1))))
            fun ρ hρ ↦ hφ_meas.comp (measurable_permutePrefixLocal (ofDual n + 1) ρ))
      simpa [exchangeableAverage] using hsum.div_const (Nat.factorial (ofDual n + 1) : ℝ)
    let f : {g : (ℕ → ℝ) → ℝ // Measurable g ∧ IsNSymmetricSequenceMap (ofDual n + 1) g} :=
      ⟨exchangeableAverage (ofDual n + 1) φ, havg_meas,
        exchangeableAverage_isNSymmetric (ofDual n + 1) φ⟩
    rw [measurable_iff_comap_le]
    exact le_iSup_of_le f le_rfl
  -- Proof comment: then pull that measurability back along the sample-sequence map of `X`.
  have havg_pullback :
      Measurable[(exchangeableBackwardFiltration X hX_meas) n]
        (exchangeableAverage (ofDual n + 1) φ ∘ Function.swap X) := by
    simpa [exchangeableBackwardFiltration] using
      havg_stage.comp (comap_measurable (Function.swap X))
  -- Proof comment: identify the pulled-back owner average with the local Cesàro average.
  have hprocess :
      exchangeableAverage (ofDual n + 1) φ ∘ Function.swap X =
        exchangeableBackwardAverageProcess X n := by
    simpa [exchangeableBackwardAverageProcess, φ] using
      exchangeableAverageApplyZero_comp_swap_eq_exchangeableCesaroAverage X (ofDual n)
  rw [← hprocess]
  exact havg_pullback.stronglyMeasurable

/-- Helper for Example 12.13: each backward empirical mean is a version of the conditional
expectation of `X 0` onto the corresponding reversed exchangeable stage. -/
private theorem exchangeableBackwardAverageProcess_aeEq_condExpFirst {X : ℕ → Ω → ℝ}
    [IsProbabilityMeasure μ] (hX : IsExchangeable X μ)
    (hX_meas : ∀ n, Measurable (X n))
    (hX_int : Integrable (X 0) μ) (n : ℕᵒᵈ) :
    exchangeableBackwardAverageProcess X n =ᵐ[μ]
      μ[X 0 | exchangeableBackwardFiltration X hX_meas n] := by
  let φ : (ℕ → ℝ) → ℝ := fun x ↦ x 0
  have hφ_meas : Measurable φ := measurable_pi_apply 0
  -- Proof comment: specialize Theorem 12.10 to the first-coordinate functional on sequence space.
  symm
  calc
    μ[X 0 | exchangeableBackwardFiltration X hX_meas n]
      =ᵐ[μ] exchangeableAverage (ofDual n + 1) φ ∘ Function.swap X := by
          simpa [exchangeableBackwardFiltration, Function.comp, Function.swap, φ] using
            condExp_eq_exchangeableAverage_of_isExchangeable hX hX_meas hφ_meas
              (by simpa [Function.comp, Function.swap, φ] using hX_int) (ofDual n + 1)
    _ = exchangeableBackwardAverageProcess X n := by
          simpa [exchangeableBackwardAverageProcess, φ] using
            exchangeableAverageApplyZero_comp_swap_eq_exchangeableCesaroAverage X (ofDual n)

-- Proof sketch: apply Theorem 12.10 to the averaging functional on the first `n` coordinates to
-- obtain the displayed conditional-expectation identity, then rewrite the family in the canonical
-- zero-based `ℕᵒᵈ` indexing as a martingale for the reversed exchangeable filtration
-- `ℱ_{-n} = ℰ_{n + 1}`.
/-- Example 12.13 (1): for an exchangeable real sequence with one integrable coordinate, the
backward empirical-mean process is a martingale on `ℕᵒᵈ` with respect to the reversed
exchangeable filtration `ℱ_{-n} = ℰ_{n + 1}`. -/
theorem exchangeableBackwardAverageProcess_martingale {X : ℕ → Ω → ℝ}
    [IsProbabilityMeasure μ] (hX : IsExchangeable X μ)
    (hX_meas : ∀ n, Measurable (X n))
    (hX_int : Integrable (X 0) μ) :
    Martingale (exchangeableBackwardAverageProcess X)
      (exchangeableBackwardFiltration X hX_meas) μ := by
  refine ⟨exchangeableBackwardAverageProcess_stageStronglyMeasurable hX_meas, ?_⟩
  intro i j hij
  -- Proof comment: rewrite both stages as conditional expectations of `X 0` and apply the tower
  -- property along the reversed filtration.
  calc
    μ[exchangeableBackwardAverageProcess X j | exchangeableBackwardFiltration X hX_meas i]
      =ᵐ[μ] μ[μ[X 0 | exchangeableBackwardFiltration X hX_meas j] |
          exchangeableBackwardFiltration X hX_meas i] := by
            exact condExp_congr_ae
              (exchangeableBackwardAverageProcess_aeEq_condExpFirst hX hX_meas hX_int j)
    _ =ᵐ[μ] μ[X 0 | exchangeableBackwardFiltration X hX_meas i] := by
          exact condExp_condExp_of_le
            ((exchangeableBackwardFiltration X hX_meas).mono hij)
            ((exchangeableBackwardFiltration X hX_meas).le j)
    _ =ᵐ[μ] exchangeableBackwardAverageProcess X i := by
          exact
            (exchangeableBackwardAverageProcess_aeEq_condExpFirst hX hX_meas hX_int i).symm

-- Proof sketch: the previous theorem gives a martingale for the larger exchangeable backwards
-- filtration, and Chapter 9 says every martingale is again a martingale for its own natural
-- filtration.
/-- Example 12.13 (2): the same backward empirical-mean process is also a martingale for the smaller
backwards filtration generated by `Y` itself. -/
theorem exchangeableBackwardAverageProcess_martingale_naturalFiltration
    {X : ℕ → Ω → ℝ} [IsProbabilityMeasure μ] (hX : IsExchangeable X μ)
    (hX_meas : ∀ n, Measurable (X n))
    (hX_int : Integrable (X 0) μ) :
    Martingale (exchangeableBackwardAverageProcess X)
      (Filtration.natural (exchangeableBackwardAverageProcess X)
        (exchangeableBackwardAverageProcess_stronglyMeasurable hX_meas)) μ := by
  have hM := exchangeableBackwardAverageProcess_martingale hX hX_meas hX_int
  have hnat := martingale_natural_filtration hM
  have hwitness :
      (fun n ↦ (hM.stronglyAdapted n).mono ((exchangeableBackwardFiltration X hX_meas).le n)) =
        exchangeableBackwardAverageProcess_stronglyMeasurable hX_meas := by
    funext n
    exact Subsingleton.elim _ _
  -- Proof comment: the Chapter 9 transfer theorem already gives the natural-filtration martingale;
  -- only the strong-measurability witness needs normalization.
  simpa [hwitness] using hnat
