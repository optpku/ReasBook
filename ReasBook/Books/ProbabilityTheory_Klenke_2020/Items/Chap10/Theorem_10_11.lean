/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Centering
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

/-
Theorem 10.11 mixes two owner abstractions from mathlib's martingale API:

- `core/canonical`: `Martingale.stoppedValue_ae_eq_condExp_of_le` in optional sampling and
  `Submartingale.expected_stoppedValue_mono` in optional stopping.
- `bridge/view`: item (3), which is exactly the owner optional-sampling theorem and is therefore
  recalled directly.
- `source-facing`: the supermartingale reformulations, the nonnegative almost-surely finite
  extensions, and the martingale characterization by bounded stopping times.

The file keeps only those genuinely source-facing companions beyond the exact owner statement.
-/
variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X : ℕ → Ω → ℝ} {σ τ : Ω → ℕ∞}

section BoundedSupermartingale

/-- Helper for Theorem 10.11: the predictable part in Doob's decomposition of a supermartingale
is almost surely antitone in deterministic time. -/
lemma supermartingale_ae_antitone_predictablePart
    (hX : Supermartingale X ℱ μ) :
    ∀ᵐ ω ∂μ, Antitone (fun n ↦ predictablePart X ℱ μ n ω) := by
  have hstep :
      ∀ n, predictablePart X ℱ μ (n + 1) ≤ᵐ[μ] predictablePart X ℱ μ n := by
    intro n
    -- Each one-step increment of the predictable part is the conditional expectation of a
    -- supermartingale increment, hence it is almost surely nonpositive.
    have hstep_condExp : μ[X (n + 1) | ℱ n] ≤ᵐ[μ] X n :=
      hX.condExp_ae_le (Nat.le_succ n)
    have hstep_diff : μ[X (n + 1) - X n | ℱ n] ≤ᵐ[μ] 0 := by
      refine (condExp_sub (hX.integrable (n + 1)) (hX.integrable n) (ℱ n)).trans_le ?_
      filter_upwards [hstep_condExp] with ω hω
      simpa [condExp_of_stronglyMeasurable (ℱ.le n) (hX.stronglyAdapted n) (hX.integrable n)]
        using sub_nonpos.2 hω
    -- Rewriting the predictable part as a range-sum isolates exactly that last increment.
    filter_upwards [hstep_diff] with ω hω
    simpa [predictablePart, Finset.sum_apply, Finset.sum_range_succ] using
      add_le_add_left hω (∑ i ∈ Finset.range n, μ[X (i + 1) - X i | ℱ i] ω)
  -- Succ-step monotonicity upgrades to an antitone deterministic-time path.
  filter_upwards [ae_all_iff.2 hstep] with ω hω
  exact antitone_nat_of_succ_le hω

/-- Helper for Theorem 10.11: the predictable part of a supermartingale decreases after stopping
at bounded times `σ ≤ τ`. -/
lemma predictablePart_stoppedValue_ae_le_of_le_of_bounded
    (hX : Supermartingale X ℱ μ) (hστ : σ ≤ τ) {N : ℕ} (hτ_le : ∀ ω, τ ω ≤ N) :
    stoppedValue (predictablePart X ℱ μ) τ ≤ᵐ[μ] stoppedValue (predictablePart X ℱ μ) σ := by
  -- The boundedness hypothesis lets us compare the deterministic indices selected by the two
  -- stopping times pathwise.
  filter_upwards [supermartingale_ae_antitone_predictablePart (X := X) (μ := μ) (ℱ := ℱ) hX] with
    ω hω
  have hτ_top : τ ω ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (hτ_le ω)
  have hσ_idx_le_τ_idx : (σ ω).untopA ≤ (τ ω).untopA :=
    WithTop.untopA_mono hτ_top (hστ ω)
  simpa [stoppedValue] using hω hσ_idx_le_τ_idx

-- Proof sketch: apply the martingale optional sampling theorem to the martingale part of the Doob
-- decomposition of `X`, combine it with the monotonicity of the predictable part, and use the
-- monotonicity of conditional expectation.
/-- Companion to Theorem 10.11 (1): Part (i), if a supermartingale is sampled
at bounded stopping times `σ ≤ τ`, then the conditional expectation of the
later stopped value is almost surely bounded above by the earlier stopped
value. -/
theorem supermartingale_condExp_stoppedValue_le_of_le_of_bounded
    (hX : Supermartingale X ℱ μ) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {N : ℕ} (hτ_le : ∀ ω, τ ω ≤ N)
    :
    μ[stoppedValue X τ | hσ.measurableSpace] ≤ᵐ[μ] stoppedValue X σ := by
  let M := martingalePart X ℱ μ
  let A := predictablePart X ℱ μ
  -- Route correction: keep the owner martingale theorem on the martingale part, and isolate the
  -- predictable-part monotonicity behind a standalone bridge lemma instead of normalizing it
  -- inside the main theorem.
  have hM : Martingale M ℱ μ := martingale_martingalePart hX.stronglyAdapted hX.integrable
  have hMτ_int : Integrable (stoppedValue M τ) μ := by
    exact integrable_stoppedValue ℕ hτ hM.integrable hτ_le
  have hA_int : ∀ n, Integrable (A n) μ := by
    intro n
    dsimp [A, predictablePart]
    rw [show (∑ i ∈ Finset.range n, μ[X (i + 1) - X i | ℱ i]) =
        (fun ω ↦ ∑ i ∈ Finset.range n, μ[X (i + 1) - X i | ℱ i] ω) by
      ext ω
      simp [Finset.sum_apply]]
    exact integrable_finset_sum (Finset.range n) fun i _ => (integrable_condExp : Integrable
      (μ[X (i + 1) - X i | ℱ i]) μ)
  have hAτ_int : Integrable (stoppedValue A τ) μ := by
    exact integrable_stoppedValue ℕ hτ hA_int hτ_le
  have hσ_le : ∀ ω, σ ω ≤ N := fun ω ↦ (hστ ω).trans (hτ_le ω)
  have hAσ_int : Integrable (stoppedValue A σ) μ := by
    exact integrable_stoppedValue ℕ hσ hA_int hσ_le
  have hM_stop :
      μ[stoppedValue M τ | hσ.measurableSpace] =ᵐ[μ] stoppedValue M σ :=
    (hM.stoppedValue_ae_eq_condExp_of_le hτ hσ hστ hτ_le).symm
  have hA_stop :
      μ[stoppedValue A τ | hσ.measurableSpace] ≤ᵐ[μ] stoppedValue A σ := by
    have hmono :
        μ[stoppedValue A τ | hσ.measurableSpace] ≤ᵐ[μ]
          μ[stoppedValue A σ | hσ.measurableSpace] :=
      condExp_mono hAτ_int hAσ_int
        (predictablePart_stoppedValue_ae_le_of_le_of_bounded
          (X := X) (μ := μ) (ℱ := ℱ) hX hστ hτ_le)
    have hmeas :
        μ[stoppedValue A σ | hσ.measurableSpace] = stoppedValue A σ := by
      refine condExp_of_stronglyMeasurable hσ.measurableSpace_le ?_ hAσ_int
      exact
        (measurable_stoppedValue
          stronglyAdapted_predictablePart'.progMeasurable_of_discrete hσ).stronglyMeasurable
    filter_upwards [hmono] with ω hω
    simpa [hmeas] using hω
  have hMA : M + A = X := by
    simpa [M, A] using martingalePart_add_predictablePart ℱ μ X
  have hτ_split : stoppedValue X τ = stoppedValue M τ + stoppedValue A τ := by
    ext ω
    simpa [stoppedValue, Pi.add_apply] using
      (congrFun (congrFun hMA ((τ ω).untopA)) ω).symm
  have hσ_split : stoppedValue X σ = stoppedValue M σ + stoppedValue A σ := by
    ext ω
    simpa [stoppedValue, Pi.add_apply] using
      (congrFun (congrFun hMA ((σ ω).untopA)) ω).symm
  -- Split the stopped value into its martingale and predictable pieces, then compare the two
  -- pieces separately under conditional expectation.
  calc
    μ[stoppedValue X τ | hσ.measurableSpace]
        =ᵐ[μ] μ[stoppedValue M τ | hσ.measurableSpace] +
            μ[stoppedValue A τ | hσ.measurableSpace] := by
          exact (condExp_congr_ae (Filter.EventuallyEq.of_eq hτ_split)).trans
            (condExp_add hMτ_int hAτ_int hσ.measurableSpace)
    _ ≤ᵐ[μ] stoppedValue M σ + stoppedValue A σ := by
      filter_upwards [hM_stop, hA_stop] with ω hωM hωA
      exact add_le_add (by simp [hωM]) hωA
    _ =ᵐ[μ] stoppedValue X σ := Filter.EventuallyEq.of_eq hσ_split.symm

-- Proof sketch: apply the optional stopping theorem for submartingales to `-X`, using
-- `Supermartingale.neg` to turn the supermartingale into a submartingale and then simplify the
-- stopped values of the negated process.
/-- Companion to Theorem 10.11 (2): Part (i), if a supermartingale is sampled
at bounded stopping times `σ ≤ τ`, then the expected stopped value is
decreasing: `𝔼[X_τ] ≤ 𝔼[X_σ]`. -/
theorem supermartingale_expected_stoppedValue_mono_of_le_of_bounded
    (hX : Supermartingale X ℱ μ) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {N : ℕ} (hτ_le : ∀ ω, τ ω ≤ N)
    :
    μ[stoppedValue X τ] ≤ μ[stoppedValue X σ] := by
  -- Turn the supermartingale into a submartingale by negating it, then use optional stopping.
  have hneg :
      μ[stoppedValue (-X) σ] ≤ μ[stoppedValue (-X) τ] :=
    Submartingale.expected_stoppedValue_mono (μ := μ) (𝒢 := ℱ) (f := -X) hX.neg hσ hτ hστ hτ_le
  simpa [stoppedValue, integral_neg, Pi.neg_apply, neg_le_neg_iff] using hneg

end BoundedSupermartingale

/- Canonical recall for the martingale identity appearing in Theorem 10.11 (3): if `X` is a
martingale and `σ ≤ τ` with `τ` bounded, then the
stopped value at `σ` is almost surely the conditional expectation of the stopped value at `τ`
with respect to `𝓕_σ`. This is exactly the canonical owner theorem
`Martingale.stoppedValue_ae_eq_condExp_of_le`. -/
recall Martingale.stoppedValue_ae_eq_condExp_of_le

section BoundedMartingale

-- Proof sketch: integrate the almost-sure identity from the martingale optional sampling theorem,
-- or equivalently apply the stopped-value expectation monotonicity to both `X` and `-X`.
/-- Companion to Theorem 10.11 (3): Part (i), if `X` is a martingale and
`σ ≤ τ` with `τ` bounded, then the expected stopped values at `σ` and `τ`
agree. -/
theorem martingale_expected_stoppedValue_eq_of_le_of_bounded
    (hX : Martingale X ℱ μ) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {N : ℕ} (hτ_le : ∀ ω, τ ω ≤ N)
    :
    μ[stoppedValue X τ] = μ[stoppedValue X σ] := by
  -- Compare the martingale both as a supermartingale and after negation.
  refine le_antisymm
    (supermartingale_expected_stoppedValue_mono_of_le_of_bounded hX.supermartingale hσ hτ hστ hτ_le)
    ?_
  have hneg :
      μ[stoppedValue (-X) τ] ≤ μ[stoppedValue (-X) σ] :=
    supermartingale_expected_stoppedValue_mono_of_le_of_bounded
      (X := -X) (μ := μ) (ℱ := ℱ) hX.neg.supermartingale hσ hτ hστ hτ_le
  simpa [stoppedValue, integral_neg, Pi.neg_apply, neg_le_neg_iff] using hneg

end BoundedMartingale

section NonnegativeSupermartingale

omit mΩ in
/-- Helper for Theorem 10.11: along a fixed path where `τ ω` is finite, the bounded truncations
eventually stop at the same index as `τ`. -/
lemma stoppedValue_truncation_eventuallyEq_of_ne_top {X : ℕ → Ω → ℝ} (ω : Ω)
    (hω : τ ω ≠ ⊤) :
    ∀ᶠ n : ℕ in Filter.atTop,
      stoppedValue X (fun x ↦ min (τ x) (n : ℕ∞)) ω = stoppedValue X τ ω := by
  -- Once the deterministic cutoff `n` reaches `τ ω`, the minimum `min (τ ω) n` is exactly `τ ω`.
  refine Filter.eventually_atTop.2 ?_
  refine ⟨(τ ω).untop hω, fun n hn ↦ ?_⟩
  have hτ_le_n : τ ω ≤ (n : ℕ∞) := by
    exact (WithTop.untop_le_iff hω).1 (by simpa [ge_iff_le] using hn)
  have hmin : min (τ ω) (n : ℕ∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hleft : (min (τ ω) (n : ℕ∞)).untopA = (min (τ ω) (n : ℕ∞)).untop hmin :=
    WithTop.untopA_eq_untop hmin
  have hright : (τ ω).untopA = (τ ω).untop hω := WithTop.untopA_eq_untop hω
  have hidx : (min (τ ω) (n : ℕ∞)).untopA = (τ ω).untopA := by
    rw [hleft, hright]
    apply WithTop.coe_injective
    rw [WithTop.coe_untop, WithTop.coe_untop]
    exact min_eq_left hτ_le_n
  -- Once the stopping indices agree, the stopped values agree definitionally.
  simpa [stoppedValue] using congrArg (fun k ↦ X k ω) hidx

/-- Helper for Theorem 10.11: if a stopping time is almost surely finite, then the bounded
truncations `ω ↦ min (τ ω) n` eventually stop at exactly the same value as `τ`. -/
lemma stoppedValue_truncation_ae_eventuallyEq {X : ℕ → Ω → ℝ}
    (hτ_ae_ne_top : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in Filter.atTop,
      stoppedValue X (fun x ↦ min (τ x) (n : ℕ∞)) ω = stoppedValue X τ ω := by
  -- Lift the pointwise stabilization lemma to an almost-sure statement using the a.s.-finite
  -- hypothesis on `τ`.
  filter_upwards [hτ_ae_ne_top] with ω hω
  exact stoppedValue_truncation_eventuallyEq_of_ne_top (X := X) ω hω

-- Proof sketch: approximate `τ` from below by the bounded stopping times
-- `fun ω ↦ min (τ ω) n`, apply the bounded optional stopping inequality, use
-- nonnegativity and Fatou's lemma to obtain integrability of the stopped
-- value, and then conclude the expectation bound.
/-- Companion to Theorem 10.11 (4): Part (ii), for a nonnegative
supermartingale and an almost surely finite stopping time `τ`, the stopped
value at `τ` is integrable and its expectation is bounded above by the initial
expectation. -/
theorem supermartingale_expected_stoppedValue_le_initial_of_nonneg_of_ae_ne_top
    (hX : Supermartingale X ℱ μ) (hX_nonneg : ∀ n ω, 0 ≤ X n ω)
    (hτ : IsStoppingTime ℱ τ)
    (hτ_ae_ne_top : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Integrable (stoppedValue X τ) μ ∧
      μ[stoppedValue X τ] ≤ μ[X 0] := by
  let τtrunc : ℕ → Ω → ℕ∞ := fun n ω ↦ min (τ ω) (n : ℕ∞)
  have hτtrunc : ∀ n, IsStoppingTime ℱ (τtrunc n) := fun n ↦ hτ.min_const n
  have hτtrunc_le : ∀ n ω, τtrunc n ω ≤ n := fun n ω ↦ min_le_right _ _
  have hτtrunc_int : ∀ n, Integrable (stoppedValue X (τtrunc n)) μ := by
    intro n
    exact integrable_stoppedValue ℕ (hτtrunc n) hX.integrable (hτtrunc_le n)
  have hτ_nonneg : 0 ≤ᵐ[μ] stoppedValue X τ := by
    -- Evaluate the pathwise nonnegativity of `X` at the random stopping index.
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    simpa [stoppedValue] using hX_nonneg (τ ω).untopA ω
  have hτtrunc_nonneg : ∀ n, 0 ≤ᵐ[μ] stoppedValue X (τtrunc n) := by
    intro n
    -- The same pathwise nonnegativity applies to each bounded truncation.
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    simpa [τtrunc, stoppedValue] using hX_nonneg (min (τ ω) (n : ℕ∞)).untopA ω
  have hτtrunc_bound : ∀ n, μ[stoppedValue X (τtrunc n)] ≤ μ[X 0] := by
    intro n
    -- Apply the bounded optional stopping inequality between time `0` and `τ ∧ n`.
    simpa [τtrunc, stoppedValue_const] using
      (supermartingale_expected_stoppedValue_mono_of_le_of_bounded
        (X := X) (μ := μ) (ℱ := ℱ) hX (isStoppingTime_const ℱ 0) (hτtrunc n)
        (fun _ ↦ bot_le) (hτtrunc_le n))
  have hτ_lintegral_le :
      ∫⁻ ω, ENNReal.ofReal (stoppedValue X τ ω) ∂μ ≤ ENNReal.ofReal (μ[X 0]) := by
    have hτtrunc_meas :
        ∀ n, AEMeasurable (fun ω ↦ ENNReal.ofReal (stoppedValue X (τtrunc n) ω)) μ := by
      intro n
      exact (hτtrunc_int n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hτtrunc_tendsto :
        ∀ᵐ ω ∂μ,
          Filter.Tendsto (fun n ↦ ENNReal.ofReal (stoppedValue X (τtrunc n) ω)) Filter.atTop
            (nhds (ENNReal.ofReal (stoppedValue X τ ω))) := by
      -- The truncations are eventually constant along almost every path, so they converge to the
      -- full stopped value.
      filter_upwards [stoppedValue_truncation_ae_eventuallyEq (X := X) (μ := μ) (τ := τ)
        hτ_ae_ne_top] with ω hω
      have hEq :
          (fun n ↦ ENNReal.ofReal (stoppedValue X (τtrunc n) ω)) =ᶠ[Filter.atTop]
            fun _ ↦ ENNReal.ofReal (stoppedValue X τ ω) := by
        filter_upwards [hω] with n hn
        simpa [τtrunc] using congrArg ENNReal.ofReal hn
      refine Filter.Tendsto.congr' hEq.symm ?_
      exact
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ ↦ ENNReal.ofReal (stoppedValue X τ ω)) Filter.atTop
            (nhds (ENNReal.ofReal (stoppedValue X τ ω))))
    have hFatou :
        ∫⁻ ω, ENNReal.ofReal (stoppedValue X τ ω) ∂μ ≤
          Filter.liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (stoppedValue X (τtrunc n) ω) ∂μ)
            Filter.atTop := by
      calc
        ∫⁻ ω, ENNReal.ofReal (stoppedValue X τ ω) ∂μ
            =
              ∫⁻ ω,
                Filter.liminf
                  (fun n ↦ ENNReal.ofReal (stoppedValue X (τtrunc n) ω)) Filter.atTop ∂μ := by
                refine lintegral_congr_ae ?_
                filter_upwards [hτtrunc_tendsto] with ω hω
                exact hω.liminf_eq.symm
        _ ≤
            Filter.liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (stoppedValue X (τtrunc n) ω) ∂μ)
              Filter.atTop := MeasureTheory.lintegral_liminf_le' hτtrunc_meas
    have hτtrunc_lintegral_bound :
        ∀ n,
          ∫⁻ ω, ENNReal.ofReal (stoppedValue X (τtrunc n) ω) ∂μ ≤ ENNReal.ofReal (μ[X 0]) := by
      intro n
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hτtrunc_int n) (hτtrunc_nonneg n)]
      exact ENNReal.ofReal_le_ofReal (hτtrunc_bound n)
    have hLiminfBound :
        Filter.liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (stoppedValue X (τtrunc n) ω) ∂μ)
          Filter.atTop ≤ ENNReal.ofReal (μ[X 0]) := by
      exact Filter.liminf_le_of_frequently_le
        (Filter.Frequently.of_forall hτtrunc_lintegral_bound)
    exact hFatou.trans hLiminfBound
  have hτ_lintegral_ne_top :
      ∫⁻ ω, ENNReal.ofReal (stoppedValue X τ ω) ∂μ ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hτ_lintegral_le ENNReal.ofReal_lt_top)
  have hτ_meas_hτ : Measurable[hτ.measurableSpace] (stoppedValue X τ) :=
    measurable_stoppedValue hX.stronglyAdapted.progMeasurable_of_discrete hτ
  have hτ_meas : Measurable (stoppedValue X τ) := by
    intro s hs
    exact hτ.measurableSpace_le _ (hτ_meas_hτ hs)
  have hτ_int : Integrable (stoppedValue X τ) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (μ := μ)
      hτ_meas.aestronglyMeasurable
      hτ_nonneg).1 hτ_lintegral_ne_top
  have hX0_nonneg : 0 ≤ μ[X 0] := integral_nonneg fun ω ↦ hX_nonneg 0 ω
  have hτ_integral_le : μ[stoppedValue X τ] ≤ μ[X 0] := by
    -- Convert the lintegral bound back to a real integral using the integrability of the stopped
    -- value and its nonnegativity.
    rw [← ENNReal.ofReal_le_ofReal_iff hX0_nonneg,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hτ_int hτ_nonneg]
    exact hτ_lintegral_le
  exact ⟨hτ_int, hτ_integral_le⟩

-- Proof sketch: deduce that `σ` is almost surely finite from `σ ≤ τ`, apply the preceding bound
-- to `σ`, and use nonnegativity of the supermartingale.
/-- Companion to Theorem 10.11 (4): under the same nonnegativity and almost-sure finiteness
hypotheses, the stopped value at the earlier stopping time `σ` is integrable and its expectation
is also bounded by the initial expectation. -/
theorem supermartingale_expected_stoppedValue_left_le_initial_of_nonneg_of_ae_ne_top
    (hX : Supermartingale X ℱ μ) (hX_nonneg : ∀ n ω, 0 ≤ X n ω)
    (hσ : IsStoppingTime ℱ σ)
    (hστ : σ ≤ τ) (hτ_ae_ne_top : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Integrable (stoppedValue X σ) μ ∧
      μ[stoppedValue X σ] ≤ μ[X 0] := by
  have hσ_ae_ne_top : ∀ᵐ ω ∂μ, σ ω ≠ ⊤ := by
    -- The earlier stopping time is finite whenever the later one is finite.
    filter_upwards [hτ_ae_ne_top] with ω hω
    exact ne_top_of_le_ne_top hω (hστ ω)
  -- Reuse the full almost-surely finite bound at the earlier stopping time.
  exact supermartingale_expected_stoppedValue_le_initial_of_nonneg_of_ae_ne_top
    (X := X) (μ := μ) (ℱ := ℱ) hX hX_nonneg hσ hσ_ae_ne_top

omit mΩ in
/-- Helper for Theorem 10.11: on the event `{σ ≤ n}`, truncating `σ` by `n` does not change the
stopped value. -/
lemma stoppedValue_min_const_eqOn_le_const {X : ℕ → Ω → ℝ} (n : ℕ) :
    Set.EqOn (stoppedValue X (fun ω ↦ min (σ ω) (n : ℕ∞))) (stoppedValue X σ)
      {ω | σ ω ≤ n} := by
  intro ω hω
  -- On `{σ ≤ n}`, the minimum selects the original stopping time.
  have hω_le : σ ω ≤ n := by
    simpa using hω
  have hω_ne_top : σ ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) hω_le
  have hmin_ne_top : min (σ ω) (n : ℕ∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hidx : (min (σ ω) (n : ℕ∞)).untopA = (σ ω).untopA := by
    rw [WithTop.untopA_eq_untop hmin_ne_top, WithTop.untopA_eq_untop hω_ne_top]
    apply WithTop.coe_injective
    rw [WithTop.coe_untop, WithTop.coe_untop, min_eq_left hω_le]
  simpa [stoppedValue] using congrArg (fun k ↦ X k ω) hidx

/-- Helper for Theorem 10.11: the bounded optional-sampling inequality on the truncated test set
`s ∩ {σ ≤ n}`. -/
lemma setIntegral_stoppedValue_trunc_le_of_le_const
    (hX : Supermartingale X ℱ μ) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {n m : ℕ} (hnm : n ≤ m) {s : Set Ω}
    (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫ ω in s ∩ {ω | σ ω ≤ n}, stoppedValue X (fun x ↦ min (τ x) (m : ℕ∞)) ω ∂μ
      ≤ ∫ ω in s ∩ {ω | σ ω ≤ n}, stoppedValue X σ ω ∂μ := by
  let σn : Ω → ℕ∞ := fun ω ↦ min (σ ω) (n : ℕ∞)
  let τm : Ω → ℕ∞ := fun ω ↦ min (τ ω) (m : ℕ∞)
  let t : Set Ω := s ∩ {ω | σ ω ≤ n}
  have hσn : IsStoppingTime ℱ σn := hσ.min_const n
  have hτm : IsStoppingTime ℱ τm := hτ.min_const m
  have hnm_top : (n : ℕ∞) ≤ m := by
    exact_mod_cast hnm
  have hσn_le_τm : σn ≤ τm := by
    intro ω
    exact min_le_min (hστ ω) hnm_top
  have ht_hσ : MeasurableSet[hσ.measurableSpace] t := by
    simpa [t] using hs.inter (hσ.measurableSet_le' n)
  have ht_hσn : MeasurableSet[hσn.measurableSpace] t := by
    simpa [t] using (hσ.measurableSet_inter_le_const_iff s n).1 ht_hσ
  have hτm_int : Integrable (stoppedValue X τm) μ := by
    exact integrable_stoppedValue ℕ hτm hX.integrable fun ω ↦ min_le_right _ _
  have hσn_int : Integrable (stoppedValue X σn) μ := by
    exact integrable_stoppedValue ℕ hσn hX.integrable fun ω ↦ min_le_right _ _
  have hbounded :
      μ[stoppedValue X τm | hσn.measurableSpace] ≤ᵐ[μ] stoppedValue X σn := by
    -- Apply the bounded optional-sampling inequality to `σ ∧ n ≤ τ ∧ m`.
    exact supermartingale_condExp_stoppedValue_le_of_le_of_bounded
      (X := X) (μ := μ) (ℱ := ℱ) hX hσn hτm hσn_le_τm fun ω ↦ min_le_right _ _
  have hset :
      ∫ ω in t, stoppedValue X τm ω ∂μ ≤ ∫ ω in t, stoppedValue X σn ω ∂μ := by
    -- Integrating the conditional-expectation inequality over a `σ ∧ n`-measurable set removes
    -- the conditional expectation from the left-hand side.
    rw [← MeasureTheory.setIntegral_condExp hσn.measurableSpace_le hτm_int ht_hσn]
    exact MeasureTheory.setIntegral_mono_ae
      integrable_condExp.integrableOn hσn_int.integrableOn hbounded
  calc
    ∫ ω in t, stoppedValue X τm ω ∂μ ≤ ∫ ω in t, stoppedValue X σn ω ∂μ := hset
    _ = ∫ ω in t, stoppedValue X σ ω ∂μ := by
      -- On `t ⊆ {σ ≤ n}`, the stopped value for `σ ∧ n` coincides pointwise with the one for `σ`.
      refine MeasureTheory.setIntegral_congr_fun (hσ.measurableSpace_le _ ht_hσ) ?_
      intro ω hω
      have hω_mem : ω ∈ s ∩ {ω | σ ω ≤ n} := by
        simpa [t] using hω
      exact (stoppedValue_min_const_eqOn_le_const (X := X) (n := n)) hω_mem.2

/-- Helper for Theorem 10.11: for every `σ`-measurable test set, the later stopped value has
smaller set integral than the earlier one under the nonnegative a.s.-finite hypotheses. -/
lemma setIntegral_stoppedValue_le_of_nonneg_of_ae_ne_top
    (hX : Supermartingale X ℱ μ) (hX_nonneg : ∀ n ω, 0 ≤ X n ω)
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) (hτ_ae_ne_top : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {s : Set Ω} (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫ ω in s, stoppedValue X τ ω ∂μ ≤ ∫ ω in s, stoppedValue X σ ω ∂μ := by
  let τtrunc : ℕ → Ω → ℕ∞ := fun m ω ↦ min (τ ω) (m : ℕ∞)
  let t : ℕ → Set Ω := fun n ↦ s ∩ {ω | σ ω ≤ n}
  have hs_meas : MeasurableSet s := hσ.measurableSpace_le _ hs
  have hσ_ae_ne_top : ∀ᵐ ω ∂μ, σ ω ≠ ⊤ := by
    -- The earlier stopping time is finite whenever the later one is finite.
    filter_upwards [hτ_ae_ne_top] with ω hω
    exact ne_top_of_le_ne_top hω (hστ ω)
  obtain ⟨hτ_int, _⟩ :=
    supermartingale_expected_stoppedValue_le_initial_of_nonneg_of_ae_ne_top
      (X := X) (μ := μ) (ℱ := ℱ) hX hX_nonneg hτ hτ_ae_ne_top
  obtain ⟨hσ_int, _⟩ :=
    supermartingale_expected_stoppedValue_left_le_initial_of_nonneg_of_ae_ne_top
      (X := X) (μ := μ) (ℱ := ℱ) hX hX_nonneg hσ hστ hτ_ae_ne_top
  have hτ_nonneg : 0 ≤ᵐ[μ] stoppedValue X τ := by
    -- Evaluate the nonnegativity of `X` at the random index selected by `τ`.
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [stoppedValue] using hX_nonneg (τ ω).untopA ω
  have hσ_nonneg : 0 ≤ᵐ[μ] stoppedValue X σ := by
    -- The same argument works for `σ`.
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [stoppedValue] using hX_nonneg (σ ω).untopA ω
  have hτtrunc_int : ∀ m, Integrable (stoppedValue X (τtrunc m)) μ := by
    intro m
    exact integrable_stoppedValue ℕ (hτ.min_const m) hX.integrable fun ω ↦ min_le_right _ _
  have hτtrunc_nonneg : ∀ m, 0 ≤ᵐ[μ] stoppedValue X (τtrunc m) := by
    intro m
    -- Each bounded truncation is still obtained by evaluating `X` at a random index.
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [τtrunc, stoppedValue] using hX_nonneg (min (τ ω) (m : ℕ∞)).untopA ω
  have ht_meas : ∀ n, MeasurableSet (t n) := by
    intro n
    exact hσ.measurableSpace_le _ (hs.inter (hσ.measurableSet_le' n))
  have ht_mono : Monotone t := by
    intro n m hnm ω hω
    have hω_mem : ω ∈ s ∩ {ω | σ ω ≤ n} := by
      simpa [t] using hω
    exact ⟨hω_mem.1, by simpa using hω_mem.2.trans (by exact_mod_cast hnm)⟩
  have hUnion_subset : (⋃ n, t n) ⊆ s := by
    intro ω hω
    rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
    exact hn.1
  have hUnion_ae : (⋃ n, t n) =ᵐ[μ] s := by
    -- Almost-sure finiteness of `σ` identifies the increasing union of `{σ ≤ n}` with the whole
    -- test set `s`.
    filter_upwards [hσ_ae_ne_top] with ω hω
    apply propext
    constructor
    · intro hmem
      rcases Set.mem_iUnion.1 hmem with ⟨n, hn⟩
      exact hn.1
    · intro hsω
      refine Set.mem_iUnion.2 ?_
      refine ⟨(σ ω).untop hω, ⟨hsω, by
        have hcoe : ((σ ω).untop hω : ℕ∞) = σ ω := WithTop.coe_untop _ _
        exact hcoe.symm.le⟩⟩
  have hfixed :
      ∀ n, ∫ ω in t n, stoppedValue X τ ω ∂μ ≤ ∫ ω in t n, stoppedValue X σ ω ∂μ := by
    intro n
    have hτ_nonneg_t : 0 ≤ᵐ[μ.restrict (t n)] stoppedValue X τ := ae_restrict_of_ae hτ_nonneg
    have hσ_nonneg_t : 0 ≤ᵐ[μ.restrict (t n)] stoppedValue X σ := ae_restrict_of_ae hσ_nonneg
    have hτtrunc_meas :
        ∀ m, AEMeasurable (fun ω ↦ ENNReal.ofReal (stoppedValue X (τtrunc m) ω))
          (μ.restrict (t n)) := by
      intro m
      have hmeas :
          AEStronglyMeasurable (stoppedValue X (τtrunc m)) (μ.restrict (t n)) :=
        ((hτtrunc_int m).mono_measure Measure.restrict_le_self).aestronglyMeasurable
      exact hmeas.aemeasurable.ennreal_ofReal
    have hτtrunc_tendsto :
        ∀ᵐ ω ∂(μ.restrict (t n)),
          Filter.Tendsto (fun m ↦ ENNReal.ofReal (stoppedValue X (τtrunc m) ω)) Filter.atTop
            (nhds (ENNReal.ofReal (stoppedValue X τ ω))) := by
      -- The truncations are eventually constant along every a.s.-finite path.
      refine ae_restrict_of_ae ?_
      filter_upwards [stoppedValue_truncation_ae_eventuallyEq (X := X) (μ := μ) (τ := τ)
        hτ_ae_ne_top] with ω hω
      have hEq :
          (fun m ↦ ENNReal.ofReal (stoppedValue X (τtrunc m) ω)) =ᶠ[Filter.atTop]
            fun _ ↦ ENNReal.ofReal (stoppedValue X τ ω) := by
        filter_upwards [hω] with m hm
        simpa [τtrunc] using congrArg ENNReal.ofReal hm
      refine Filter.Tendsto.congr' hEq.symm ?_
      exact
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ ↦ ENNReal.ofReal (stoppedValue X τ ω)) Filter.atTop
            (nhds (ENNReal.ofReal (stoppedValue X τ ω))))
    have hFatou :
        ∫⁻ ω, ENNReal.ofReal (stoppedValue X τ ω) ∂(μ.restrict (t n)) ≤
          Filter.liminf
            (fun m ↦ ∫⁻ ω, ENNReal.ofReal (stoppedValue X (τtrunc m) ω) ∂(μ.restrict (t n)))
            Filter.atTop := by
      -- Fatou turns the pointwise stabilization into a lower bound for the full stopped value.
      calc
        ∫⁻ ω, ENNReal.ofReal (stoppedValue X τ ω) ∂(μ.restrict (t n))
            = ∫⁻ ω,
                Filter.liminf
                  (fun m ↦ ENNReal.ofReal (stoppedValue X (τtrunc m) ω)) Filter.atTop
                ∂(μ.restrict (t n)) := by
              refine lintegral_congr_ae ?_
              filter_upwards [hτtrunc_tendsto] with ω hω
              exact hω.liminf_eq.symm
        _ ≤ Filter.liminf
              (fun m ↦ ∫⁻ ω, ENNReal.ofReal (stoppedValue X (τtrunc m) ω) ∂(μ.restrict (t n)))
              Filter.atTop := MeasureTheory.lintegral_liminf_le' hτtrunc_meas
    have hτtrunc_lintegral_bound :
        ∀ᶠ m in Filter.atTop,
          ∫⁻ ω, ENNReal.ofReal (stoppedValue X (τtrunc m) ω) ∂(μ.restrict (t n))
            ≤ ENNReal.ofReal (∫ ω in t n, stoppedValue X σ ω ∂μ) := by
      -- For large enough truncation levels, the bounded theorem applies on `t n`.
      filter_upwards [Filter.eventually_ge_atTop n] with m hm
      have hbound :
          ∫ ω in t n, stoppedValue X (τtrunc m) ω ∂μ ≤ ∫ ω in t n, stoppedValue X σ ω ∂μ := by
        simpa [t, τtrunc] using
          setIntegral_stoppedValue_trunc_le_of_le_const
            (X := X) (μ := μ) (ℱ := ℱ) hX hσ hτ hστ hm hs
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            ((hτtrunc_int m).mono_measure Measure.restrict_le_self)
            (ae_restrict_of_ae (hτtrunc_nonneg m))]
      exact ENNReal.ofReal_le_ofReal hbound
    have hLiminfBound :
        Filter.liminf
            (fun m ↦ ∫⁻ ω, ENNReal.ofReal (stoppedValue X (τtrunc m) ω) ∂(μ.restrict (t n)))
            Filter.atTop
          ≤ ENNReal.ofReal (∫ ω in t n, stoppedValue X σ ω ∂μ) := by
      exact Filter.liminf_le_of_frequently_le hτtrunc_lintegral_bound.frequently
    have hσ_t_nonneg_real : 0 ≤ ∫ ω in t n, stoppedValue X σ ω ∂μ := by
      exact integral_nonneg_of_ae hσ_nonneg_t
    have hσ_lintegral_eq :
        ∫⁻ ω, ENNReal.ofReal (stoppedValue X σ ω) ∂(μ.restrict (t n))
          = ENNReal.ofReal (∫ ω in t n, stoppedValue X σ ω ∂μ) := by
      exact
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (hσ_int.mono_measure Measure.restrict_le_self) hσ_nonneg_t).symm
    have hLiminfBound' :
        Filter.liminf
            (fun m ↦ ∫⁻ ω, ENNReal.ofReal (stoppedValue X (τtrunc m) ω) ∂(μ.restrict (t n)))
            Filter.atTop
          ≤ ∫⁻ ω, ENNReal.ofReal (stoppedValue X σ ω) ∂(μ.restrict (t n)) := by
      simpa [hσ_lintegral_eq] using hLiminfBound
    rw [← ENNReal.ofReal_le_ofReal_iff hσ_t_nonneg_real,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hτ_int.mono_measure Measure.restrict_le_self) hτ_nonneg_t,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hσ_int.mono_measure Measure.restrict_le_self) hσ_nonneg_t]
    exact hFatou.trans hLiminfBound'
  have hτ_tendsto :
      Filter.Tendsto (fun n ↦ ∫ ω in t n, stoppedValue X τ ω ∂μ) Filter.atTop
        (nhds (∫ ω in ⋃ n, t n, stoppedValue X τ ω ∂μ)) := by
    -- The increasing sets `t n` exhaust `s` up to a null set.
    refine MeasureTheory.tendsto_setIntegral_of_monotone ht_meas ht_mono ?_
    exact hτ_int.integrableOn.mono_set hUnion_subset
  have hσ_tendsto :
      Filter.Tendsto (fun n ↦ ∫ ω in t n, stoppedValue X σ ω ∂μ) Filter.atTop
        (nhds (∫ ω in ⋃ n, t n, stoppedValue X σ ω ∂μ)) := by
    refine MeasureTheory.tendsto_setIntegral_of_monotone ht_meas ht_mono ?_
    exact hσ_int.integrableOn.mono_set hUnion_subset
  have hUnion_le :
      ∫ ω in ⋃ n, t n, stoppedValue X τ ω ∂μ
        ≤ ∫ ω in ⋃ n, t n, stoppedValue X σ ω ∂μ := by
    exact le_of_tendsto_of_tendsto' hτ_tendsto hσ_tendsto hfixed
  have hτ_union :
      ∫ ω in ⋃ n, t n, stoppedValue X τ ω ∂μ = ∫ ω in s, stoppedValue X τ ω ∂μ := by
    exact MeasureTheory.setIntegral_congr_set hUnion_ae
  have hσ_union :
      ∫ ω in ⋃ n, t n, stoppedValue X σ ω ∂μ = ∫ ω in s, stoppedValue X σ ω ∂μ := by
    exact MeasureTheory.setIntegral_congr_set hUnion_ae
  -- Passing `n → ∞` upgrades the truncated inequalities to the full test-set inequality.
  calc
    ∫ ω in s, stoppedValue X τ ω ∂μ = ∫ ω in ⋃ n, t n, stoppedValue X τ ω ∂μ := hτ_union.symm
    _ ≤ ∫ ω in ⋃ n, t n, stoppedValue X σ ω ∂μ := hUnion_le
    _ = ∫ ω in s, stoppedValue X σ ω ∂μ := hσ_union

-- Proof sketch: truncate `σ` and `τ` by deterministic bounds, apply the bounded optional
-- sampling inequality, use Fatou's lemma to retain integrability of the later stopped value, and
-- then pass to the limit in the conditional-expectation inequality.
/-- Theorem 10.11 (5): Part (ii), for a nonnegative supermartingale and almost surely finite
stopping times `σ ≤ τ`, the optional sampling inequality still holds without a deterministic bound
on `τ`; moreover the later stopped value remains integrable. -/
theorem supermartingale_condExp_stoppedValue_le_of_nonneg_of_ae_ne_top
    (hX : Supermartingale X ℱ μ) (hX_nonneg : ∀ n ω, 0 ≤ X n ω)
    (hσ : IsStoppingTime ℱ σ)
    (hτ : IsStoppingTime ℱ τ) (hστ : σ ≤ τ) (hτ_ae_ne_top : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Integrable (stoppedValue X τ) μ ∧
      μ[stoppedValue X τ | hσ.measurableSpace] ≤ᵐ[μ] stoppedValue X σ := by
  obtain ⟨hτ_int, _⟩ :=
    supermartingale_expected_stoppedValue_le_initial_of_nonneg_of_ae_ne_top
      (X := X) (μ := μ) (ℱ := ℱ) hX hX_nonneg hτ hτ_ae_ne_top
  obtain ⟨hσ_int, _⟩ :=
    supermartingale_expected_stoppedValue_left_le_initial_of_nonneg_of_ae_ne_top
      (X := X) (μ := μ) (ℱ := ℱ) hX hX_nonneg hσ hστ hτ_ae_ne_top
  have hσ_measurable :
      Measurable[hσ.measurableSpace] (stoppedValue X σ) :=
    measurable_stoppedValue hX.stronglyAdapted.progMeasurable_of_discrete hσ
  have hσ_meas :
      StronglyMeasurable[hσ.measurableSpace] (stoppedValue X σ) := by
    exact hσ_measurable.stronglyMeasurable
  have hcond_le :
      μ[stoppedValue X τ | hσ.measurableSpace] ≤ᵐ[μ] stoppedValue X σ := by
    -- Route correction: instead of transporting the same set through two stopping-time
    -- measurable spaces, prove the comparison on `s ∩ {σ ≤ n}`, pass to the trimmed measure on
    -- `hσ.measurableSpace`, and transport the resulting a.e. inequality back to `μ`.
    have hdiff_trim :
        0 ≤ᵐ[μ.trim hσ.measurableSpace_le]
          fun ω ↦ stoppedValue X σ ω - μ[stoppedValue X τ | hσ.measurableSpace] ω := by
      refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
      · intro s hs hμs
        refine @Integrable.integrableOn _ _ hσ.measurableSpace _ _ _ _ _ ?_
        refine Integrable.trim hσ.measurableSpace_le ?_
          (hσ_meas.sub stronglyMeasurable_condExp)
        exact hσ_int.sub integrable_condExp
      · intro s hs _
        have htrim :
            ∫ x in s,
                (stoppedValue X σ x - μ[stoppedValue X τ | hσ.measurableSpace] x)
                ∂μ.trim hσ.measurableSpace_le
              =
              ∫ x in s,
                (stoppedValue X σ x - μ[stoppedValue X τ | hσ.measurableSpace] x) ∂μ := by
          simpa using
            (MeasureTheory.setIntegral_trim hσ.measurableSpace_le
              (hσ_meas.sub stronglyMeasurable_condExp) hs).symm
        rw [htrim]
        change 0 ≤ ∫ x in s, stoppedValue X σ x - μ[stoppedValue X τ | hσ.measurableSpace] x ∂μ
        have hsub :
            ∫ x in s, (stoppedValue X σ - μ[stoppedValue X τ | hσ.measurableSpace]) x ∂μ
              =
              ∫ x in s, stoppedValue X σ x ∂μ
                - ∫ x in s, μ[stoppedValue X τ | hσ.measurableSpace] x ∂μ :=
          MeasureTheory.integral_sub' hσ_int.integrableOn integrable_condExp.integrableOn
        rw [show
            (∫ x in s, stoppedValue X σ x - μ[stoppedValue X τ | hσ.measurableSpace] x ∂μ)
              = ∫ x in s, (stoppedValue X σ - μ[stoppedValue X τ | hσ.measurableSpace]) x ∂μ by
            rfl,
          hsub, sub_nonneg, MeasureTheory.setIntegral_condExp hσ.measurableSpace_le hτ_int hs]
        exact setIntegral_stoppedValue_le_of_nonneg_of_ae_ne_top
          (X := X) (μ := μ) (ℱ := ℱ) hX hX_nonneg hσ hτ hστ hτ_ae_ne_top hs
    have hdiff :
        0 ≤ᵐ[μ] fun ω ↦ stoppedValue X σ ω - μ[stoppedValue X τ | hσ.measurableSpace] ω :=
      ae_le_of_ae_le_trim (hm := hσ.measurableSpace_le) hdiff_trim
    filter_upwards [hdiff] with ω hω
    exact sub_nonneg.mp hω
  exact ⟨hτ_int, hcond_le⟩

end NonnegativeSupermartingale

section Characterization

-- Proof sketch: the forward implication follows from the martingale case of optional stopping.
-- For the converse, test the stopping-time expectation identity on piecewise
-- constant bounded stopping times built from events in `𝓕_s` to recover the
-- martingale conditional expectation identity at deterministic times.
/-- Companion to Theorem 10.11 (6): Part (iii), an adapted integrable
real-valued process is a martingale if and only if every bounded stopping time
preserves the initial expectation. -/
theorem martingale_iff_expected_stoppedValue_eq_initial_of_bounded_stopping_times
    (hX_adapted : Adapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ)
    :
    Martingale X ℱ μ ↔
      ∀ τ : Ω → ℕ∞, IsStoppingTime ℱ τ → (∃ N : ℕ, ∀ ω, τ ω ≤ N) →
        μ[stoppedValue X τ] = μ[X 0] := by
  constructor
  · intro hX τ hτ hτ_bdd
    rcases hτ_bdd with ⟨N, hτ_le⟩
    -- Sample the martingale between time `0` and the bounded stopping time `τ`.
    simpa [stoppedValue_const] using
      (martingale_expected_stoppedValue_eq_of_le_of_bounded
        (X := X) (μ := μ) (ℱ := ℱ) hX (isStoppingTime_const ℱ 0) hτ
        (fun _ ↦ bot_le) hτ_le)
  · intro hstopped
    have hX_stronglyAdapted : StronglyAdapted ℱ X := hX_adapted.stronglyAdapted
    have hstopped_neg :
        ∀ τ : Ω → ℕ∞, IsStoppingTime ℱ τ → (∃ N : ℕ, ∀ ω, τ ω ≤ N) →
          μ[stoppedValue (-X) τ] = μ[(-X) 0] := by
      intro τ hτ hτ_bdd
      -- Rewrite the stopped-value identity through negation so that the same hypothesis applies.
      simpa [stoppedValue, integral_neg, Pi.neg_apply] using congrArg Neg.neg (hstopped τ hτ hτ_bdd)
    -- Route correction: instead of rebuilding the source's piecewise-event argument directly,
    -- invoke mathlib's bounded-stopping-time characterization on `X` and on `-X`.
    have hSub : Submartingale X ℱ μ := by
      rw [submartingale_iff_expected_stoppedValue_mono]
      · intro σ τ hσ hτ hστ hτ_bdd
        rcases hτ_bdd with ⟨N, hτ_le⟩
        have hσ_le : ∀ ω, σ ω ≤ N := fun ω ↦ (hστ ω).trans (hτ_le ω)
        exact le_of_eq ((hstopped σ hσ ⟨N, hσ_le⟩).trans (hstopped τ hτ ⟨N, hτ_le⟩).symm)
      · exact hX_stronglyAdapted
      · exact hX_int
    have hSuper : Supermartingale X ℱ μ := by
      have hSubNeg : Submartingale (-X) ℱ μ := by
        rw [submartingale_iff_expected_stoppedValue_mono]
        · intro σ τ hσ hτ hστ hτ_bdd
          rcases hτ_bdd with ⟨N, hτ_le⟩
          have hσ_le : ∀ ω, σ ω ≤ N := fun ω ↦ (hστ ω).trans (hτ_le ω)
          exact le_of_eq ((hstopped_neg σ hσ ⟨N, hσ_le⟩).trans (hstopped_neg τ hτ ⟨N, hτ_le⟩).symm)
        · exact hX_stronglyAdapted.neg
        · intro n
          exact (hX_int n).neg
      simpa using hSubNeg.neg
    exact (martingale_iff).2 ⟨hSuper, hSub⟩

end Characterization
