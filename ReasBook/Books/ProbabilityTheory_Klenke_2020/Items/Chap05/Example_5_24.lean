/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u v

variable {Ω : Type u} {E : Type v}

noncomputable section

/-- The Shannon information of a symbol with respect to the source law `p`, valued in `EReal` so
zero-probability symbols have infinite information content. -/
def shannonInformation (p : PMF E) : E → EReal :=
  fun e ↦ -ENNReal.log (p e)

/-- The Shannon information is the negative logarithm of the probability of the observed
symbol in `EReal`. -/
@[simp]
theorem shannonInformation_apply (p : PMF E) (e : E) :
    shannonInformation p e = -ENNReal.log (p e) := rfl

/-- On symbols in the support of `p`, the extended-real information content agrees with the usual
real-valued logarithm. -/
theorem shannonInformation_toReal_eq (p : PMF E) {e : E} (he : e ∈ p.support) :
    (shannonInformation p e).toReal = -Real.log ((p e).toReal) := by
  -- Proof comment: support membership removes the zero branch of `ENNReal.log`.
  rw [shannonInformation]
  rw [ENNReal.log_pos_real ((p.mem_support_iff e).1 he) (p.apply_ne_top e)]
  simp

/-- The probability of the initial word `X₁(ω), …, Xₙ(ω)` under the i.i.d. source law `p`, valued
in `ENNReal`. -/
def shannonPathProbability (p : PMF E) (X : ℕ → Ω → E) (n : ℕ) : Ω → ENNReal :=
  fun ω ↦ ∏ i : Fin n, p (X (i + 1) ω)

/-- The path probability is the product of the probabilities of the first `n` observed symbols. -/
@[simp]
theorem shannonPathProbability_apply (p : PMF E) (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    shannonPathProbability p X n ω = ∏ i : Fin n, p (X (i + 1) ω) := rfl

-- Proof sketch: expand `shannonPathProbability` and `shannonInformation`, then use
-- `ENNReal.log_mul_add` to convert the logarithm of the product into a sum of logarithms in
-- `EReal`.
/-- The negative logarithm of the path probability is the sum of the information contents of the
first `n` observed symbols. This remains valid pointwise because zero-probability symbols contribute
`⊤` information content. -/
theorem neg_log_shannonPathProbability_eq_sum_shannonInformation
    (p : PMF E) (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    -ENNReal.log (shannonPathProbability p X n ω) =
      ∑ i : Fin n, shannonInformation p (X (i + 1) ω) := by
  rw [shannonPathProbability, Fin.prod_univ_eq_prod_range (fun i ↦ p (X (i + 1) ω)),
    Fin.sum_univ_eq_sum_range (fun i ↦ shannonInformation p (X (i + 1) ω))]
  induction n with
  | zero =>
      -- Proof comment: the empty word has probability `1`, so both sides are `0`.
      simp
  | succ n ih =>
      -- Proof comment: split off the final symbol and convert the product logarithm into a sum.
      rw [Finset.prod_range_succ, ENNReal.log_mul_add, Finset.sum_range_succ]
      calc
        -((∏ x ∈ Finset.range n, p (X (x + 1) ω)).log + (p (X (n + 1) ω)).log) =
            -(∏ x ∈ Finset.range n, p (X (x + 1) ω)).log + -(p (X (n + 1) ω)).log := by
              simpa using
                EReal.neg_add
                  (Or.inr (by simpa using p.apply_ne_top (X (n + 1) ω)))
                  (Or.inl (by
                    simp [ENNReal.prod_ne_top fun x hx ↦ p.apply_ne_top (X (x + 1) ω)]))
        _ = (∑ i ∈ Finset.range n, shannonInformation p (X (i + 1) ω)) +
              -(p (X (n + 1) ω)).log := by
              rw [ih]
        _ = (∑ i ∈ Finset.range n, shannonInformation p (X (i + 1) ω)) +
              shannonInformation p (X (n + 1) ω) := by
              simp [shannonInformation]

-- Proof sketch: apply `EReal.toReal` to
-- `neg_log_shannonPathProbability_eq_sum_shannonInformation`, using the support assumptions to
-- rule out zero-probability symbols and hence `⊤` summands.
/-- On words whose letters all lie in the support of `p`, the extended-real path-information
identity reduces to the usual real-valued logarithmic identity. -/
theorem neg_log_shannonPathProbability_toReal_eq_sum_shannonInformation
    (p : PMF E) (X : ℕ → Ω → E) (n : ℕ) (ω : Ω)
    (hsupport : ∀ i : Fin n, X (i + 1) ω ∈ p.support) :
    -Real.log ((shannonPathProbability p X n ω).toReal) =
      ∑ i : Fin n, (shannonInformation p (X (i + 1) ω)).toReal := by
  -- Proof comment: on the support branch every factor is positive, so the `EReal` identity
  -- becomes an ordinary real logarithm identity.
  rw [shannonPathProbability, Fin.prod_univ_eq_prod_range (fun i ↦ p (X (i + 1) ω)),
    Fin.sum_univ_eq_sum_range (fun i ↦ (shannonInformation p (X (i + 1) ω)).toReal),
    ENNReal.toReal_prod, Real.log_prod]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa using (shannonInformation_toReal_eq p (hsupport ⟨i, by simpa using hi⟩)).symm
  · intro i hi
    exact ENNReal.toReal_ne_zero.2
      ⟨(p.mem_support_iff _).1 (hsupport ⟨i, by simpa using hi⟩), p.apply_ne_top _⟩

variable [Finite E] [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]

section ShannonTheorem

variable (P : Measure Ω) [IsProbabilityMeasure P] (p : PMF E) (X : ℕ → Ω → E)

/-- Helper for Example 5.24: integrating the real-valued information content against the source
law recovers the Shannon entropy. -/
private theorem integral_shannonInformation_toReal_eq_entropy :
    ∫ e, (shannonInformation p e).toReal ∂p.toMeasure = (entropy p).toReal := by
  letI : Fintype E := Fintype.ofFinite E
  have hterm :
      ∀ e : E,
        (p e).toReal * (shannonInformation p e).toReal =
          -((p e).toReal * Real.log ((p e).toReal)) := by
    intro e
    by_cases he : e ∈ p.support
    · -- Proof comment: on the support, the information content is the ordinary negative log.
      rw [shannonInformation_toReal_eq p he]
      ring
    · -- Proof comment: outside the support, the probability weight vanishes, so both sides are `0`.
      have hp : p e = 0 := by
        simpa [PMF.mem_support_iff] using he
      simp [hp, shannonInformation]
  -- Proof comment: expand the `PMF` integral into a finite weighted sum and rewrite each term.
  rw [PMF.integral_eq_sum, entropy_toReal_eq_sum]
  simp_rw [smul_eq_mul, hterm]
  rw [← Finset.sum_neg_distrib]

/-- Helper for Example 5.24: every coordinate of the i.i.d. source lies in the support of `p`
almost surely. -/
private theorem ae_all_mem_support_of_isIID_hasLaw
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_law : HasLaw (X 1) p.toMeasure P) :
    ∀ᵐ ω ∂P, ∀ n, X (n + 1) ω ∈ p.support := by
  let _ : IsProbabilityMeasure P := inferInstance
  have hsupport_meas : MeasurableSet p.support := p.support_countable.measurableSet
  have hsupport_ae : ∀ᵐ e ∂p.toMeasure, e ∈ p.support := by
    -- Proof comment: the support has full `p.toMeasure`-mass.
    change p.support ∈ ae p.toMeasure
    rw [mem_ae_iff_prob_eq_one hsupport_meas]
    exact (p.toMeasure_apply_eq_one_iff hsupport_meas).2 Set.Subset.rfl
  refine ae_all_iff.2 fun n ↦ ?_
  have hXn_law : HasLaw (X (n + 1)) p.toMeasure P := by
    -- Proof comment: identical distribution transports the common source law to every coordinate.
    simpa using (hX_iid.identDistrib 0 n).hasLaw hX_law
  have hsupport_pred_meas : Measurable fun e : E ↦ e ∈ p.support := by
    exact measurable_of_finite _
  exact
    (hXn_law.ae_iff (p := fun e : E ↦ e ∈ p.support) hsupport_pred_meas).2 hsupport_ae

-- Proof sketch: apply `ProbabilityTheory.strong_law_ae_real` to the real-valued sequence
-- `fun n ↦ fun ω ↦ (shannonInformation p (X (n + 1) ω)).toReal`; independence follows from
-- `hX_iid` by composing with the measurable information-content map on the finite alphabet,
-- identical distribution comes from `hX_iid`, the common law `p` is anchored by `hX_law`, and
-- the expectation is computed as `(entropy p).toReal` using `HasLaw.integral_eq` together with a
-- local `Fintype.ofFinite E`, `PMF.integral_eq_sum`, and `entropy_toReal_eq_sum`.
/-- Auxiliary information-content form of Shannon's theorem: for i.i.d. `E`-valued random variables
with common law `p`, the empirical mean of `-log p(X_n)` converges almost surely
to the entropy of `p`
(compare Definition 5.25). -/
theorem shannon_theorem_informationContent_ae_tendsto
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_law : HasLaw (X 1) p.toMeasure P)
    :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ ↦
          (∑ i ∈ Finset.range n, (shannonInformation p (X (i + 1) ω)).toReal) / n)
        atTop (𝓝 ((entropy p).toReal)) := by
  let _ : IsProbabilityMeasure P := inferInstance
  let F : E → ℝ := fun e ↦ (shannonInformation p e).toReal
  let Y : ℕ → Ω → ℝ := fun n ω ↦ (shannonInformation p (X (n + 1) ω)).toReal
  have hF_meas : Measurable F := by
    -- Proof comment: every function on the finite alphabet is measurable.
    exact measurable_of_finite F
  have hF_law : HasLaw F (Measure.map F p.toMeasure) p.toMeasure := by
    exact
      (show MeasurePreserving F p.toMeasure (Measure.map F p.toMeasure) from
        ⟨hF_meas, rfl⟩).hasLaw
  have hF_integrable : Integrable F p.toMeasure := by
    -- Proof comment: finite alphabets make every real-valued observable integrable.
    exact Integrable.of_finite
  have hY_iIndep : iIndepFun Y P := by
    -- Proof comment: measurable postcomposition preserves independence.
    simpa [Y, F] using hX_iid.iIndepFun.comp (fun _ ↦ F) (fun _ ↦ hF_meas)
  have hY_pairwise : Pairwise fun i j ↦ Y i ⟂ᵢ[P] Y j := by
    -- Proof comment: pairwise independence is the two-coordinate shadow of the i.i.d. family.
    intro i j hij
    exact hY_iIndep.indepFun hij
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) P P := by
    -- Proof comment: all transformed coordinates share the same distribution.
    intro n
    simpa [Y, F] using (hX_iid.identDistrib n 0).comp hF_meas
  have hY0_ident : IdentDistrib (Y 0) F P p.toMeasure := by
    have hY0_law : HasLaw (Y 0) (Measure.map F p.toMeasure) P := by
      -- Proof comment: the law of `X 1` pushes forward through the information map.
      simpa [Y, F] using hF_law.fun_comp hX_law
    exact hY0_law.identDistrib hF_law
  have hY0_integrable : Integrable (Y 0) P := by
    -- Proof comment: integrability transfers across equality in distribution.
    exact hY0_ident.integrable_iff.2 hF_integrable
  have hY0_expectation : P[Y 0] = (entropy p).toReal := by
    -- Proof comment: the mean information content of one symbol is the Shannon entropy.
    calc
      P[Y 0] = ∫ e, F e ∂p.toMeasure := by
        simpa [Y, F] using hX_law.integral_comp hF_meas.aestronglyMeasurable
      _ = (entropy p).toReal := by
        simpa [F] using integral_shannonInformation_toReal_eq_entropy (p := p)
  have hY_limit :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Y i ω) / n) atTop (𝓝 (P[Y 0])) := by
    -- Proof comment: this is the strong law for the real-valued information-content sequence.
    exact ProbabilityTheory.strong_law_ae_real Y hY0_integrable hY_pairwise hY_ident
  -- Proof comment: the strong law now applies to the real-valued i.i.d. information sequence.
  filter_upwards [hY_limit] with ω hω
  exact hY0_expectation ▸ (by simpa [Y] using hω)

-- Proof sketch: combine `shannon_theorem_informationContent_ae_tendsto` with
-- `neg_log_shannonPathProbability_toReal_eq_sum_shannonInformation` on the full-measure event where
-- every observed symbol lies in the support of `p`, so the normalized negative log-likelihood of
-- the observed word is the empirical mean of the real-valued information contents.
/-- Example 5.24: Shannon's theorem says that for an i.i.d. `E`-valued source with law `p`, the
normalized negative logarithm of the path probability `pi_n` converges almost surely to the Shannon
entropy of `p` (compare Definition 5.25). -/
theorem shannon_theorem_ae_tendsto
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_law : HasLaw (X 1) p.toMeasure P)
    :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ (-Real.log ((shannonPathProbability p X n ω).toReal)) / n) atTop
        (𝓝 ((entropy p).toReal)) := by
  filter_upwards
      [ae_all_mem_support_of_isIID_hasLaw (P := P) (p := p) (X := X) hX_iid hX_law,
        shannon_theorem_informationContent_ae_tendsto (P := P) (p := p) (X := X) hX_iid hX_law]
      with ω hsupport hlimit
  have hseq :
      (fun n : ℕ ↦ (-Real.log ((shannonPathProbability p X n ω).toReal)) / n) =
        fun n : ℕ ↦
          (∑ i ∈ Finset.range n, (shannonInformation p (X (i + 1) ω)).toReal) / n := by
    funext n
    congr 1
    -- Proof comment: on the full-support event, path information equals the sum of symbol
    -- information contents.
    rw [neg_log_shannonPathProbability_toReal_eq_sum_shannonInformation
      (p := p) (X := X) (n := n) (ω := ω) (hsupport := fun i ↦ hsupport i)]
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ (shannonInformation p (X (i + 1) ω)).toReal) n)
  -- Proof comment: rewrite the target sequence pointwise on the full-measure support event.
  simpa only [hseq] using hlimit

end ShannonTheorem
