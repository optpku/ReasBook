module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Operations

public section

open scoped BigOperators

universe u v w

namespace FiniteTaylorJet

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Subtracting a jet's constant coefficient leaves exactly its positive-degree
formal-series partial sum. -/
lemma eval_sub_constantCoeff_eq_sum_Ico {m : ℕ} (J : FiniteTaylorJet ℝ E F m)
    (h : E) :
    J.eval h - J.constantCoeff =
      ∑ n ∈ Finset.Ico 1 (m + 1), J.toFormalMultilinearSeries n (fun _ ↦ h) := by
  -- Write both evaluations as partial sums and remove the unique degree-zero term.
  rw [constantCoeff_eq_coeff_zero, eval_eq_partialSum,
    FormalMultilinearSeries.partialSum,
    Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ (Nat.zero_le m))]
  simp only [Finset.sum_range_one]
  rw [toFormalMultilinearSeries_coeff_of_le J (Nat.zero_le m)]
  congr
  funext i
  exact Fin.elim0 i

/-- The partial sum of a formal-series composition is the portion of the
finite composition index set whose total degree is below the cutoff. -/
lemma comp_partialSum_eq_sum_filter {G : Type w} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {m : ℕ} (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) (h : E) :
    (q.comp p).partialSum (m + 1) h =
      ∑ d ∈ (FormalMultilinearSeries.compPartialSumTarget 0 (m + 1) (m + 1)).filter
        (fun d ↦ d.1 < m + 1), q.compAlongComposition p d.2 (fun _ ↦ h) := by
  classical
  have hindex :
      (Finset.range (m + 1)).sigma
          (fun n ↦ (Finset.univ : Finset (Composition n))) =
        (FormalMultilinearSeries.compPartialSumTarget 0 (m + 1) (m + 1)).filter
          (fun d ↦ d.1 < m + 1) := by
    -- Below the cutoff, every composition automatically satisfies the target bounds.
    ext d
    rcases d with ⟨n, c⟩
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_univ, and_true,
      Finset.mem_filter, FormalMultilinearSeries.mem_compPartialSumTarget_iff]
    constructor
    · intro hn
      exact ⟨⟨Nat.zero_le _, c.length_le.trans_lt hn,
        fun j ↦ (c.blocksFun_le j).trans_lt hn⟩, hn⟩
    · exact fun hd ↦ hd.2
  -- Expand the composed coefficient and merge the degree/composition sums.
  rw [FormalMultilinearSeries.partialSum]
  simp only [FormalMultilinearSeries.comp, _root_.sum_apply]
  rw [Finset.sum_sigma', hindex]

/-- Evaluation of a truncated composition is the corresponding low-degree
partial sum of the untruncated formal-series composition. -/
lemma eval_comp_eq_partialSum_comp {G : Type w} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {m : ℕ} (Q : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m) (h : E) :
    (comp Q P).eval h =
      (Q.toFormalMultilinearSeries.comp P.toFormalMultilinearSeries).partialSum
        (m + 1) h := by
  -- Both sides are the same sum over degrees zero through `m`.
  rw [eval_eq_sum, FormalMultilinearSeries.partialSum, ← Fin.sum_univ_eq_sum_range]
  congr with n
  rw [coeff_comp]

/-- The discrepancy between nested jet evaluation and truncated composition is
the finite sum of composition terms whose total degree exceeds the cutoff. -/
lemma comp_eval_sub_eval_eq_highDegreeSum {G : Type w} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {m : ℕ} (Q : FiniteTaylorJet ℝ F G m)
    (P : FiniteTaylorJet ℝ E F m) (h : E) :
    Q.eval (P.eval h - P.constantCoeff) - (comp Q P).eval h =
      ∑ d ∈ (FormalMultilinearSeries.compPartialSumTarget 0 (m + 1) (m + 1)).filter
        (fun d ↦ m + 1 ≤ d.1),
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries d.2 (fun _ ↦ h) := by
  classical
  let target := FormalMultilinearSeries.compPartialSumTarget 0 (m + 1) (m + 1)
  let term : (Σ n, Composition n) → G := fun d ↦
    Q.toFormalMultilinearSeries.compAlongComposition
      P.toFormalMultilinearSeries d.2 (fun _ ↦ h)
  have hfilter : target.filter (fun d ↦ ¬ d.1 < m + 1) =
      target.filter (fun d ↦ m + 1 ≤ d.1) := by
    -- Negating the low-degree predicate gives the complementary high degrees.
    ext d
    simp only [Finset.mem_filter, not_lt]
  -- Expand nested evaluation over the common composition target and remove its low degrees.
  rw [eval_eq_partialSum, eval_sub_constantCoeff_eq_sum_Ico,
    FormalMultilinearSeries.comp_partialSum, eval_comp_eq_partialSum_comp,
    comp_partialSum_eq_sum_filter]
  change (∑ d ∈ target, term d) -
      ∑ d ∈ target.filter (fun d ↦ d.1 < m + 1), term d =
        ∑ d ∈ target.filter (fun d ↦ m + 1 ≤ d.1), term d
  rw [← hfilter]
  have hsplit := Finset.sum_filter_add_sum_filter_not target
    (fun d ↦ d.1 < m + 1) term
  rw [← hsplit]
  abel

/-- A degreewise bound on a finite jet also bounds every retained coefficient
of its zero-extended formal multilinear series. -/
lemma norm_toFormalMultilinearSeries_le {m : ℕ} (J : FiniteTaylorJet ℝ E F m)
    {B : ℝ} (hJ : ∀ n : Fin (m + 1), ‖J.coeff n‖ ≤ B)
    {n : ℕ} (hn : n < m + 1) : ‖J.toFormalMultilinearSeries n‖ ≤ B := by
  -- In a retained degree, the formal series stores the original jet coefficient.
  rw [toFormalMultilinearSeries_coeff_of_le J (Nat.le_of_lt_succ hn)]
  exact hJ ⟨n, hn⟩

/-- Uniform bounds for the coefficients of two jets bound each coefficient of
their truncated formal-series composition by an explicit finite sum. -/
lemma norm_coeff_comp_le {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ} (P : FiniteTaylorJet ℝ E F m) (Q : FiniteTaylorJet ℝ F G m)
    {BP BQ : ℝ} (hP : ∀ n, ‖P.coeff n‖ ≤ BP)
    (hQ : ∀ n, ‖Q.coeff n‖ ≤ BQ) (n : Fin (m + 1)) :
    ‖(comp Q P).coeff n‖ ≤
      ∑ c : Composition (n : ℕ), BQ * BP ^ c.length := by
  classical
  have hBQ : 0 ≤ BQ := (norm_nonneg (Q.coeff 0)).trans (hQ 0)
  rw [coeff_comp, FormalMultilinearSeries.comp]
  calc
    ‖∑ c : Composition (n : ℕ),
        Q.toFormalMultilinearSeries.compAlongComposition
          P.toFormalMultilinearSeries c‖ ≤
        ∑ c : Composition (n : ℕ),
          ‖Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : Composition (n : ℕ), BQ * BP ^ c.length := by
      apply Finset.sum_le_sum
      intro c _
      calc
        ‖Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries c‖ ≤
            ‖Q.toFormalMultilinearSeries c.length‖ *
              ∏ i, ‖P.toFormalMultilinearSeries (c.blocksFun i)‖ :=
          FormalMultilinearSeries.compAlongComposition_norm _ _ _
        _ ≤ BQ * ∏ _i : Fin c.length, BP := by
          apply mul_le_mul
          · exact norm_toFormalMultilinearSeries_le Q hQ
              (c.length_le.trans_lt n.isLt)
          · exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
              (fun i _ ↦ norm_toFormalMultilinearSeries_le P hP
                ((c.blocksFun_le i).trans_lt n.isLt))
          · exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
          · exact hBQ
        _ = BQ * BP ^ c.length := by
          simp only [Finset.prod_const, Finset.card_fin]

/-- Uniform coefficient bounds give a uniform order-`m+1` bound for the
high-degree tail discarded by finite-jet composition on the unit ball. -/
lemma exists_compEvalTailBound {G : Type w} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (m : ℕ) (BP BQ : ℝ) (hBP : 0 ≤ BP) (hBQ : 0 ≤ BQ) :
    ∃ D ≥ 0, ∀ (P : FiniteTaylorJet ℝ E F m) (Q : FiniteTaylorJet ℝ F G m),
      (∀ n, ‖P.coeff n‖ ≤ BP) → (∀ n, ‖Q.coeff n‖ ≤ BQ) →
        ∀ h : E, ‖h‖ ≤ 1 →
          ‖Q.eval (P.eval h - P.constantCoeff) - (comp Q P).eval h‖ ≤
            D * ‖h‖ ^ (m + 1) := by
  classical
  let target := FormalMultilinearSeries.compPartialSumTarget 0 (m + 1) (m + 1)
  let high := target.filter (fun d ↦ m + 1 ≤ d.1)
  let weight : (Σ n, Composition n) → ℝ := fun d ↦ BQ * BP ^ d.2.length
  refine ⟨∑ d ∈ high, weight d, ?_, ?_⟩
  · -- Every summand in the chosen tail constant is nonnegative.
    exact Finset.sum_nonneg fun d _ ↦ mul_nonneg hBQ (pow_nonneg hBP _)
  · intro P Q hP hQ h hunit
    have hterm (d : Σ n, Composition n) (hd : d ∈ high) :
        ‖Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries d.2 (fun _ ↦ h)‖ ≤
          weight d * ‖h‖ ^ (m + 1) := by
      have hdTarget : d ∈ target := (Finset.mem_filter.mp hd).1
      have hdHigh : m + 1 ≤ d.1 := (Finset.mem_filter.mp hd).2
      have hdBounds :=
        (FormalMultilinearSeries.mem_compPartialSumTarget_iff.mp hdTarget)
      have hQcoeff : ‖Q.toFormalMultilinearSeries d.2.length‖ ≤ BQ :=
        norm_toFormalMultilinearSeries_le Q hQ hdBounds.2.1
      have hPcoeff (i : Fin d.2.length) :
          ‖P.toFormalMultilinearSeries (d.2.blocksFun i)‖ ≤ BP :=
        norm_toFormalMultilinearSeries_le P hP (hdBounds.2.2 i)
      have hpower : ‖h‖ ^ d.1 ≤ ‖h‖ ^ (m + 1) :=
        pow_le_pow_of_le_one (norm_nonneg h) hunit hdHigh
      calc
        ‖Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries d.2 (fun _ ↦ h)‖ ≤
            (‖Q.toFormalMultilinearSeries d.2.length‖ *
              ∏ i, ‖P.toFormalMultilinearSeries (d.2.blocksFun i)‖) *
                ∏ _i : Fin d.1, ‖h‖ :=
          FormalMultilinearSeries.compAlongComposition_bound
            P.toFormalMultilinearSeries d.2
              (Q.toFormalMultilinearSeries d.2.length) (fun _ ↦ h)
        _ ≤ (BQ * ∏ _i : Fin d.2.length, BP) * ∏ _i : Fin d.1, ‖h‖ := by
          gcongr with i
          exact hPcoeff i
        _ = weight d * ‖h‖ ^ d.1 := by
          simp only [weight, Finset.prod_const, Finset.card_fin]
        _ ≤ weight d * ‖h‖ ^ (m + 1) :=
          mul_le_mul_of_nonneg_left hpower (mul_nonneg hBQ (pow_nonneg hBP _))
    rw [comp_eval_sub_eval_eq_highDegreeSum]
    change ‖∑ d ∈ high,
      Q.toFormalMultilinearSeries.compAlongComposition
        P.toFormalMultilinearSeries d.2 (fun _ ↦ h)‖ ≤
        (∑ d ∈ high, weight d) * ‖h‖ ^ (m + 1)
    calc
      ‖∑ d ∈ high,
          Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries d.2 (fun _ ↦ h)‖ ≤
          ∑ d ∈ high, ‖Q.toFormalMultilinearSeries.compAlongComposition
            P.toFormalMultilinearSeries d.2 (fun _ ↦ h)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ d ∈ high, weight d * ‖h‖ ^ (m + 1) := by
        exact Finset.sum_le_sum fun d hd ↦ hterm d hd
      _ = (∑ d ∈ high, weight d) * ‖h‖ ^ (m + 1) := by
        rw [Finset.sum_mul]

/-- The change in a finite jet evaluation is bounded by its coefficient norms
and the distance between the two inputs. -/
lemma norm_eval_sub_eval_le {m : ℕ} (J : FiniteTaylorJet ℝ E F m)
    (u v : E) (R : ℝ) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖J.eval u - J.eval v‖ ≤
      ‖u - v‖ * ∑ n : Fin (m + 1),
        ‖J.coeff n‖ * (n : ℕ) * R ^ ((n : ℕ) - 1) := by
  -- Expand the two evaluations and estimate the finite sum degree by degree.
  rw [eval_eq_sum, eval_eq_sum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ n : Fin (m + 1),
        (J.coeff n (fun _ ↦ u) - J.coeff n (fun _ ↦ v))‖ ≤
        ∑ n : Fin (m + 1),
          ‖J.coeff n (fun _ ↦ u) - J.coeff n (fun _ ↦ v)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n : Fin (m + 1),
        ‖J.coeff n‖ * (n : ℕ) * R ^ ((n : ℕ) - 1) * ‖u - v‖ := by
      gcongr with n
      have hu' : ‖(fun _ : Fin (n : ℕ) ↦ u)‖ ≤ R :=
        (pi_norm_const_le u).trans hu
      have hv' : ‖(fun _ : Fin (n : ℕ) ↦ v)‖ ≤ R :=
        (pi_norm_const_le v).trans hv
      have hR : 0 ≤ R := (norm_nonneg u).trans hu
      have huv : ‖(fun _ : Fin (n : ℕ) ↦ u) - (fun _ ↦ v)‖ ≤ ‖u - v‖ := by
        calc
          ‖(fun _ : Fin (n : ℕ) ↦ u) - (fun _ ↦ v)‖ =
              ‖fun _ : Fin (n : ℕ) ↦ u - v‖ := by
            congr 1
          _ ≤ ‖u - v‖ := pi_norm_const_le (u - v)
      calc
        ‖J.coeff n (fun _i : Fin (n : ℕ) ↦ u) -
            J.coeff n (fun _i : Fin (n : ℕ) ↦ v)‖ ≤
            ‖J.coeff n‖ * (n : ℕ) *
              max ‖(fun _i : Fin (n : ℕ) ↦ u)‖
                  ‖(fun _i : Fin (n : ℕ) ↦ v)‖ ^ ((n : ℕ) - 1) *
                ‖(fun _i : Fin (n : ℕ) ↦ u) - (fun _i : Fin (n : ℕ) ↦ v)‖ :=
          by
            simpa only [Fintype.card_fin] using
              ContinuousMultilinearMap.norm_image_sub_le
                (J.coeff n) (fun _i : Fin (n : ℕ) ↦ u) (fun _i : Fin (n : ℕ) ↦ v)
        _ ≤ ‖J.coeff n‖ * (n : ℕ) * R ^ ((n : ℕ) - 1) * ‖u - v‖ := by
          have hcore :
              ‖J.coeff n‖ * (n : ℕ) *
                  max ‖(fun _i : Fin (n : ℕ) ↦ u)‖
                    ‖(fun _i : Fin (n : ℕ) ↦ v)‖ ^ ((n : ℕ) - 1) ≤
                ‖J.coeff n‖ * (n : ℕ) * R ^ ((n : ℕ) - 1) := by
            gcongr
            exact max_le hu' hv'
          exact mul_le_mul hcore huv (norm_nonneg _)
            (mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hR _))
    _ = ‖u - v‖ * ∑ n : Fin (m + 1),
        ‖J.coeff n‖ * (n : ℕ) * R ^ ((n : ℕ) - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring

end FiniteTaylorJet
