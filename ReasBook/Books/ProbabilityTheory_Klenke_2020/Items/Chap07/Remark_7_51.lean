/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Filter ContinuousLinearMap lp
open scoped ENNReal lp Topology

noncomputable section

local notation "countℕ" => (Measure.count : Measure ℕ)

private theorem l1SequenceMemLp_count
    (b : lp (fun _ : ℕ ↦ ℝ) 1) :
    MemLp b 1 countℕ := by
  rw [memLp_one_iff_integrable, integrable_count_iff]
  simpa using (lp.hasSum_norm (show 0 < (1 : ℝ≥0∞).toReal by norm_num) b).summable

private def l1SequenceToCountLp
    (b : lp (fun _ : ℕ ↦ ℝ) 1) :
    Lp ℝ 1 countℕ :=
  (l1SequenceMemLp_count b).toLp b

private theorem l1SequenceToCountLp_apply
    (b : lp (fun _ : ℕ ↦ ℝ) 1) (n : ℕ) :
    l1SequenceToCountLp b n = b n := by
  exact
    ae_iff_of_countable.mp (MemLp.coeFn_toLp (l1SequenceMemLp_count b)) n (by simp)

private theorem l1SequenceToCountLp_norm
    (b : lp (fun _ : ℕ ↦ ℝ) 1) :
    ‖l1SequenceToCountLp b‖ = ‖b‖ := by
  rw [l1SequenceToCountLp, Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm, lintegral_count]
  rw [ENNReal.tsum_toReal_eq fun _ ↦ by simp]
  simpa using (lp.hasSum_norm (show 0 < (1 : ℝ≥0∞).toReal by norm_num) b).tsum_eq

private def l1SequenceToCountLpCLM :
    lp (fun _ : ℕ ↦ ℝ) 1 →L[ℝ] Lp ℝ 1 countℕ :=
  (LinearMap.mkContinuous
      { toFun := l1SequenceToCountLp
        map_add' := fun b₁ b₂ ↦ by
          rw [l1SequenceToCountLp]
          exact (MemLp.toLp_congr (l1SequenceMemLp_count (b₁ + b₂))
            ((l1SequenceMemLp_count b₁).add (l1SequenceMemLp_count b₂)) Filter.EventuallyEq.rfl).trans
            (MemLp.toLp_add (l1SequenceMemLp_count b₁) (l1SequenceMemLp_count b₂))
        map_smul' := fun c b ↦ by
          rw [l1SequenceToCountLp]
          exact (MemLp.toLp_congr (l1SequenceMemLp_count (c • b))
            ((l1SequenceMemLp_count b).const_smul c) Filter.EventuallyEq.rfl).trans
            (MemLp.toLp_const_smul c (l1SequenceMemLp_count b)) }
      1 fun b ↦ by
        simpa [one_mul] using le_of_eq (l1SequenceToCountLp_norm b))

private theorem boundedSequenceMemLp_count
    (x : ℓ^∞(ℕ)) :
    MemLp x ∞ countℕ := by
  refine memLp_top_of_bound (measurable_of_countable fun n : ℕ ↦ x n).aestronglyMeasurable ‖x‖ ?_
  exact Filter.Eventually.of_forall fun n ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero x n

private def boundedSequenceToCountLp
    (x : ℓ^∞(ℕ)) :
    Lp ℝ ∞ countℕ :=
  (boundedSequenceMemLp_count x).toLp x

private theorem boundedSequenceToCountLp_apply
    (x : ℓ^∞(ℕ)) (n : ℕ) :
    boundedSequenceToCountLp x n = x n := by
  exact
    ae_iff_of_countable.mp (MemLp.coeFn_toLp (boundedSequenceMemLp_count x)) n (by simp)

private theorem boundedSequenceToCountLp_norm_le
    (x : ℓ^∞(ℕ)) :
    ‖boundedSequenceToCountLp x‖ ≤ ‖x‖ := by
  rw [boundedSequenceToCountLp, Lp.norm_toLp, eLpNorm_exponent_top]
  calc
    ENNReal.toReal (eLpNormEssSup x countℕ)
      ≤ ENNReal.toReal (ENNReal.ofReal ‖x‖) := by
          apply ENNReal.toReal_mono (by simp)
          exact eLpNormEssSup_le_of_ae_bound <|
            Filter.Eventually.of_forall fun n ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero x n
    _ = ‖x‖ := by simp

private def boundedSequenceToCountLpCLM :
    ℓ^∞(ℕ) →L[ℝ] Lp ℝ ∞ countℕ :=
  (LinearMap.mkContinuous
      { toFun := boundedSequenceToCountLp
        map_add' := fun x y ↦ by
          rw [boundedSequenceToCountLp]
          exact (MemLp.toLp_congr (boundedSequenceMemLp_count (x + y))
            ((boundedSequenceMemLp_count x).add (boundedSequenceMemLp_count y))
            Filter.EventuallyEq.rfl).trans
            (MemLp.toLp_add (boundedSequenceMemLp_count x) (boundedSequenceMemLp_count y))
        map_smul' := fun c x ↦ by
          rw [boundedSequenceToCountLp]
          exact (MemLp.toLp_congr (boundedSequenceMemLp_count (c • x))
            ((boundedSequenceMemLp_count x).const_smul c) Filter.EventuallyEq.rfl).trans
            (MemLp.toLp_const_smul c (boundedSequenceMemLp_count x)) }
      1 fun x ↦ by
        simpa [one_mul] using boundedSequenceToCountLp_norm_le x)

/-- The canonical pairing map sending an `ℓ¹` sequence to the corresponding continuous linear
functional on `ℓ^∞(ℕ)` given by coefficientwise summation. -/
def l1BoundedSequenceDualityMap :
    lp (fun _ : ℕ ↦ ℝ) 1 →L[ℝ] StrongDual ℝ (ℓ^∞(ℕ)) :=
  ((precompL (ℓ^∞(ℕ)) (((mul ℝ ℝ).lpPairing countℕ 1 ∞).flip)) boundedSequenceToCountLpCLM).comp
    l1SequenceToCountLpCLM

/-- Evaluating the canonical `ℓ¹`-pairing functional on a bounded sequence gives the expected
coefficientwise sum. -/
theorem l1BoundedSequenceDualityMap_apply
    (b : lp (fun _ : ℕ ↦ ℝ) 1) (x : ℓ^∞(ℕ)) :
    l1BoundedSequenceDualityMap b x = ∑' n, x n * b n := by
  have h_integrable :
      Integrable (fun n : ℕ ↦ l1SequenceToCountLp b n * boundedSequenceToCountLp x n)
        countℕ := by
    rw [← memLp_one_iff_integrable]
    exact (mul ℝ ℝ).memLp_of_bilin 1 (Lp.memLp (l1SequenceToCountLp b))
      (Lp.memLp (boundedSequenceToCountLp x))
  rw [l1BoundedSequenceDualityMap]
  change
    (((precompL (ℓ^∞(ℕ)) (((mul ℝ ℝ).lpPairing countℕ 1 ∞).flip)) boundedSequenceToCountLpCLM)
      (l1SequenceToCountLpCLM b)) x = ∑' n, x n * b n
  rw [ContinuousLinearMap.precompL_apply]
  rw [ContinuousLinearMap.flip_apply]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  change ∫ n : ℕ, l1SequenceToCountLp b n * boundedSequenceToCountLp x n ∂countℕ =
    ∑' n, x n * b n
  rw [integral_countable h_integrable]
  simp [l1SequenceToCountLp_apply, boundedSequenceToCountLp_apply, smul_eq_mul, mul_comm]

/-- Helper for Remark 7.51: the zero bounded sequence converges to `0`. -/
private theorem convergentBoundedSequence_zero :
    ∃ l : ℝ, Tendsto (fun n ↦ (0 : ℓ^∞(ℕ)) n) atTop (𝓝 l) := by
  -- The zero bounded sequence is the constant zero sequence.
  refine ⟨0, ?_⟩
  change Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)
  exact tendsto_const_nhds

/-- Helper for Remark 7.51: the sum of two convergent bounded sequences is convergent. -/
private theorem convergentBoundedSequence_add
    {x y : ℓ^∞(ℕ)}
    (hx : ∃ l : ℝ, Tendsto (fun n ↦ x n) atTop (𝓝 l))
    (hy : ∃ l : ℝ, Tendsto (fun n ↦ y n) atTop (𝓝 l)) :
    ∃ l : ℝ, Tendsto (fun n ↦ (x + y) n) atTop (𝓝 l) := by
  rcases hx with ⟨lx, hx⟩
  rcases hy with ⟨ly, hy⟩
  -- Limits add pointwise, so the bounded sum converges to `lx + ly`.
  exact ⟨lx + ly, by simpa using hx.add hy⟩

/-- Helper for Remark 7.51: scalar multiples of convergent bounded sequences remain convergent. -/
private theorem convergentBoundedSequence_smul
    (c : ℝ) {x : ℓ^∞(ℕ)}
    (hx : ∃ l : ℝ, Tendsto (fun n ↦ x n) atTop (𝓝 l)) :
    ∃ l : ℝ, Tendsto (fun n ↦ (c • x) n) atTop (𝓝 l) := by
  rcases hx with ⟨l, hx⟩
  -- Scalar multiplication is continuous, so the scalar multiple converges to `c • l`.
  exact ⟨c • l, by simpa using hx.const_smul c⟩

/-- Helper for Remark 7.51: the subspace of convergent bounded real sequences inside `ℓ^∞(ℕ)`. -/
private def convergentBoundedSequenceSubmodule : Submodule ℝ (ℓ^∞(ℕ)) where
  carrier := {x | ∃ l : ℝ, Tendsto (fun n ↦ x n) atTop (𝓝 l)}
  zero_mem' := convergentBoundedSequence_zero
  add_mem' := fun {_} {_} hx hy ↦ convergentBoundedSequence_add hx hy
  smul_mem' := fun c {_} hx ↦ convergentBoundedSequence_smul c hx

/-- Helper for Remark 7.51: the chosen ordinary limit of a convergent bounded sequence. -/
private def convergentLimit
    (x : convergentBoundedSequenceSubmodule) : ℝ :=
  Classical.choose (show ∃ l : ℝ, Tendsto (fun n ↦ (x : ℓ^∞(ℕ)) n) atTop (𝓝 l) from x.2)

/-- Helper for Remark 7.51: the chosen limit really is a limit of the underlying sequence. -/
private theorem convergentLimit_spec
    (x : convergentBoundedSequenceSubmodule) :
    Tendsto (fun n ↦ (x : ℓ^∞(ℕ)) n) atTop (𝓝 (convergentLimit x)) :=
  Classical.choose_spec
    (show ∃ l : ℝ, Tendsto (fun n ↦ (x : ℓ^∞(ℕ)) n) atTop (𝓝 l) from x.2)

/-- Helper for Remark 7.51: any other proven limit agrees with the chosen one. -/
private theorem convergentLimit_eq_of_tendsto
    (x : convergentBoundedSequenceSubmodule) {l : ℝ}
    (hx : Tendsto (fun n ↦ (x : ℓ^∞(ℕ)) n) atTop (𝓝 l)) :
    convergentLimit x = l := by
  -- Limits in `ℝ` are unique, so the chosen limit must equal `l`.
  exact tendsto_nhds_unique (convergentLimit_spec x) hx

/-- Helper for Remark 7.51: the chosen limit is additive on convergent bounded sequences. -/
private theorem convergentLimit_add
    (x y : convergentBoundedSequenceSubmodule) :
    convergentLimit (x + y) = convergentLimit x + convergentLimit y := by
  -- The sum sequence converges to the sum of the chosen limits.
  apply convergentLimit_eq_of_tendsto
  simpa using (convergentLimit_spec x).add (convergentLimit_spec y)

/-- Helper for Remark 7.51: the chosen limit is homogeneous on convergent bounded sequences. -/
private theorem convergentLimit_smul
    (c : ℝ) (x : convergentBoundedSequenceSubmodule) :
    convergentLimit (c • x) = c • convergentLimit x := by
  -- Scalar multiplication commutes with taking the limit.
  apply convergentLimit_eq_of_tendsto
  simpa using (convergentLimit_spec x).const_smul c

/-- Helper for Remark 7.51: the limit of a convergent bounded sequence is bounded by its `ℓ^∞`
norm. -/
private theorem convergentLimitNormLe
    (x : convergentBoundedSequenceSubmodule) :
    ‖convergentLimit x‖ ≤ ‖(x : ℓ^∞(ℕ))‖ := by
  -- Each coordinate is bounded by the `ℓ^∞` norm, and the inequality survives the limit.
  exact le_of_tendsto' (convergentLimit_spec x).norm fun n ↦
    lp.norm_apply_le_norm ENNReal.top_ne_zero (x : ℓ^∞(ℕ)) n

/-- Helper for Remark 7.51: the continuous linear functional sending a convergent bounded
sequence to its limit. -/
private def limitOnConvergentBoundedSequenceSubmodule :
    StrongDual ℝ convergentBoundedSequenceSubmodule :=
  LinearMap.mkContinuous
    { toFun := convergentLimit
      map_add' := convergentLimit_add
      map_smul' := convergentLimit_smul }
    1
    fun x ↦ by
      -- The operator norm is controlled by the sup norm estimate on the limit.
      simpa [one_mul] using convergentLimitNormLe x

/-- Helper for Remark 7.51: evaluating the limit functional returns the chosen limit. -/
private theorem limitOnConvergentBoundedSequenceSubmodule_apply
    (x : convergentBoundedSequenceSubmodule) :
    limitOnConvergentBoundedSequenceSubmodule x = convergentLimit x :=
  rfl

/-- Helper for Remark 7.51: the `ℓ¹` pairing reads off coordinates on the standard basis vectors
of `ℓ^∞(ℕ)`. -/
private theorem l1BoundedSequenceDualityMap_apply_single
    (b : lp (fun _ : ℕ ↦ ℝ) 1) (n : ℕ) :
    l1BoundedSequenceDualityMap b (lp.single (E := fun _ : ℕ ↦ ℝ) ∞ n (1 : ℝ)) = b n := by
  have hsum :
      HasSum (fun m : ℕ ↦ (lp.single (E := fun _ : ℕ ↦ ℝ) ∞ n (1 : ℝ)) m * b m) (b n) := by
    -- The standard basis vector leaves only the `n`th summand alive.
    convert (hasSum_ite_eq n (b n)) using 1
    ext m
    by_cases hm : m = n
    · subst hm
      simp [lp.single_apply]
    · simp [lp.single_apply, hm]
  rw [l1BoundedSequenceDualityMap_apply]
  exact hsum.tsum_eq

/-- Helper for Remark 7.51: each standard basis vector in `ℓ^∞(ℕ)` converges pointwise to `0`. -/
private theorem standardBasisSequence_tendsto_zero
    (n : ℕ) :
    Tendsto (fun m ↦ (lp.single (E := fun _ : ℕ ↦ ℝ) ∞ n (1 : ℝ)) m) atTop (𝓝 0) := by
  have h_eventually :
      (fun m ↦ (lp.single (E := fun _ : ℕ ↦ ℝ) ∞ n (1 : ℝ)) m) =ᶠ[atTop] fun _ ↦ (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop (n + 1)] with m hm
    have hmn : m ≠ n := by
      exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self n) hm)
    simp [lp.single_apply, hmn]
  -- Beyond the index `n`, the standard basis vector is identically zero.
  exact (tendsto_congr' h_eventually).2 tendsto_const_nhds

-- Proof sketch: extend the limit functional on the subspace of convergent bounded sequences to all
-- of `ℓ^∞(ℕ)` by Hahn--Banach, then test the extension on standard bounded sequences to show that
-- no coefficient sequence in `ℓ¹` can represent it by coordinatewise summation.
/-- Remark 7.51: there exists a continuous linear functional on `ℓ^∞(ℕ)` which agrees with the
ordinary limit on every convergent bounded sequence but does not lie in the range of the canonical
pairing map `ℓ¹(ℕ) → (ℓ^∞(ℕ))'`. Equivalently, it is not given by pairing with any `ℓ¹`
sequence. -/
theorem exists_non_l1_representable_limit_extension_on_bounded_sequences :
    ∃ F : StrongDual ℝ (ℓ^∞(ℕ)),
      (∀ ⦃x : ℓ^∞(ℕ)⦄ ⦃l : ℝ⦄, Tendsto (fun n ↦ x n) atTop (𝓝 l) → F x = l) ∧
      F ∉ Set.range l1BoundedSequenceDualityMap := by
  obtain ⟨F, hF_extends, _⟩ :=
    exists_extension_norm_eq convergentBoundedSequenceSubmodule
      limitOnConvergentBoundedSequenceSubmodule
  have hF_limit :
      ∀ ⦃x : ℓ^∞(ℕ)⦄ ⦃l : ℝ⦄, Tendsto (fun n ↦ x n) atTop (𝓝 l) → F x = l := by
    intro x l hx
    have hx_mem : x ∈ convergentBoundedSequenceSubmodule := ⟨l, hx⟩
    let xConv : convergentBoundedSequenceSubmodule := ⟨x, hx_mem⟩
    have h_extension :
        F xConv = limitOnConvergentBoundedSequenceSubmodule xConv :=
      hF_extends xConv
    have h_limit : convergentLimit xConv = l :=
      convergentLimit_eq_of_tendsto xConv hx
    -- The extension agrees with the limit functional on the convergent subspace.
    simpa [limitOnConvergentBoundedSequenceSubmodule_apply] using h_extension.trans h_limit
  refine ⟨F, hF_limit, ?_⟩
  · rintro ⟨b, rfl⟩
    have hb_zero : ∀ n : ℕ, b n = 0 := by
      intro n
      have h_basis :
          l1BoundedSequenceDualityMap b
              (lp.single (E := fun _ : ℕ ↦ ℝ) ∞ n (1 : ℝ)) = 0 :=
        hF_limit (standardBasisSequence_tendsto_zero n)
      -- Applying the extension property to the `n`th basis vector kills the `n`th coefficient.
      simpa [l1BoundedSequenceDualityMap_apply_single] using h_basis
    have hb : b = 0 := by
      ext n
      exact hb_zero n
    have h_const :
        l1BoundedSequenceDualityMap b (1 : ℓ^∞(ℕ)) = 1 :=
      hF_limit (by
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)))
    have h_zero :
        l1BoundedSequenceDualityMap b (1 : ℓ^∞(ℕ)) = 0 := by
      -- Once all coefficients vanish, the representing functional is the zero functional.
      rw [hb]
      simp
    have : (1 : ℝ) = 0 := h_const.symm.trans h_zero
    exact one_ne_zero this
