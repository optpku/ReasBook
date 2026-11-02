import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_1.ch3_sec3_1_theorem_3_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_1.ch3_sec3_1_remark_3_2

open scoped BigOperators Matrix

-- Declarations for this item will be appended below by the statement pipeline.

variable {𝕜 : Type*}

section CertificateData

variable [Preorder 𝕜] [NonUnitalNonAssocSemiring 𝕜]

/-- A Farkas certificate for infeasibility of `A *ᵥ x ≤ b`. -/
class IsFarkasCertificate
    {m n : Type*} [Fintype m]
    (A : Matrix m n 𝕜) (b : m → 𝕜) (u : m → 𝕜) : Prop where
  /-- The multiplier vector is componentwise nonnegative. -/
  nonneg : 0 ≤ u
  /-- The multiplier annihilates the coefficient matrix. -/
  annihilates : u ᵥ* A = 0
  /-- The multiplier evaluates negatively on the right-hand side. -/
  negative_rhs : u ⬝ᵥ b < 0

/-- Helper for Theorem 3.4: reindexing rows and columns along equivalences preserves feasibility
of a finite linear system. -/
lemma exists_solution_reindex_iff
    {m l n o : Type*} [Fintype n] [Fintype o]
    (em : m ≃ l) (en : n ≃ o) (A : Matrix m n 𝕜) (b : m → 𝕜) :
    (∃ x : o → 𝕜, A.reindex em en *ᵥ x ≤ b ∘ em.symm) ↔ ∃ x : n → 𝕜, A *ᵥ x ≤ b := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x ∘ en, ?_⟩
    intro i
    have hmul :
        (A.reindex em en *ᵥ x) (em i) = (A *ᵥ (x ∘ en)) i := by
      simpa [Matrix.reindex_apply] using
        congrFun (Matrix.submatrix_mulVec_equiv A x em.symm en.symm) (em i)
    exact hmul ▸ by simpa using hx (em i)
  · rintro ⟨x, hx⟩
    refine ⟨x ∘ en.symm, ?_⟩
    intro i
    have hmul :
        (A.reindex em en *ᵥ (x ∘ en.symm)) i = (A *ᵥ x) (em.symm i) := by
      calc
        (A.reindex em en *ᵥ (x ∘ en.symm)) i
            = (A *ᵥ ((x ∘ en.symm) ∘ en)) (em.symm i) := by
                simpa [Matrix.reindex_apply] using
                  congrFun (Matrix.submatrix_mulVec_equiv A (x ∘ en.symm) em.symm en.symm) i
        _ = (A *ᵥ x) (em.symm i) := by
              rw [show (x ∘ en.symm) ∘ en = x by
                funext j
                simp]
    exact hmul.symm ▸ by simpa using hx (em.symm i)

/-- Helper for Theorem 3.4: reindexing rows and columns along equivalences preserves Farkas
certificates. -/
lemma isFarkasCertificate_reindex
    {m l n o : Type*} [Fintype m] [Fintype l]
    (em : m ≃ l) (en : n ≃ o) {A : Matrix m n 𝕜} {b : m → 𝕜} {u : m → 𝕜}
    (hu : IsFarkasCertificate A b u) :
    IsFarkasCertificate (A.reindex em en) (b ∘ em.symm) (u ∘ em.symm) where
  nonneg i := hu.nonneg (em.symm i)
  annihilates := by
    ext j
    have hmul :
        ((u ∘ em.symm) ᵥ* A.reindex em en) j = (u ᵥ* A) (en.symm j) := by
      calc
        ((u ∘ em.symm) ᵥ* A.reindex em en) j
            = (((u ∘ em.symm) ∘ em) ᵥ* A) (en.symm j) := by
                simpa [Matrix.reindex_apply] using
                  congrFun (Matrix.submatrix_vecMul_equiv A (u ∘ em.symm) em.symm en.symm) j
        _ = (u ᵥ* A) (en.symm j) := by
              rw [show (u ∘ em.symm) ∘ em = u by
                funext i
                simp]
    exact hmul.trans <| by simpa using congrFun hu.annihilates (en.symm j)
  negative_rhs := by
    have hdot : (u ∘ em.symm) ⬝ᵥ (b ∘ em.symm) = u ⬝ᵥ b := by
      change ∑ x, u (em.symm x) * b (em.symm x) = ∑ i, u i * b i
      simpa using (em.symm.sum_comp fun i ↦ u i * b i)
    rw [hdot]
    exact hu.negative_rhs

/-- Helper for Theorem 3.4: Farkas certificates descend along matrix reindexing equivalences. -/
lemma isFarkasCertificate_of_reindex
    {m l n o : Type*} [Fintype m] [Fintype l]
    (em : m ≃ l) (en : n ≃ o) {A : Matrix m n 𝕜} {b : m → 𝕜} {u : l → 𝕜}
    (hu : IsFarkasCertificate (A.reindex em en) (b ∘ em.symm) u) :
    IsFarkasCertificate A b (u ∘ em) := by
  refine
    { nonneg := fun i ↦ hu.nonneg (em i)
      annihilates := ?_
      negative_rhs := ?_ }
  · ext j
    have hmul : (u ᵥ* A.reindex em en) (en j) = ((u ∘ em) ᵥ* A) j := by
      simpa [Function.comp, Equiv.symm_apply_apply, Matrix.reindex_apply] using
        congrFun (Matrix.submatrix_vecMul_equiv A u em.symm en.symm) (en j)
    exact hmul.symm.trans <| by simpa using congrFun hu.annihilates (en j)
  · have hdot : (u ∘ em) ⬝ᵥ b = u ⬝ᵥ (b ∘ em.symm) := by
      change ∑ i, u (em i) * b i = ∑ x, u x * b (em.symm x)
      simpa using (em.sum_comp fun x ↦ u x * b (em.symm x))
    rw [hdot]
    exact hu.negative_rhs

/-- Helper for Theorem 3.4: existence of a Farkas certificate is invariant under matrix
reindexing along equivalences. -/
lemma exists_isFarkasCertificate_reindex_iff
    {m l n o : Type*} [Fintype m] [Fintype l]
    (em : m ≃ l) (en : n ≃ o) (A : Matrix m n 𝕜) (b : m → 𝕜) :
    (∃ u : l → 𝕜, IsFarkasCertificate (A.reindex em en) (b ∘ em.symm) u) ↔
      ∃ u : m → 𝕜, IsFarkasCertificate A b u := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u ∘ em, isFarkasCertificate_of_reindex em en hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u ∘ em.symm, isFarkasCertificate_reindex em en hu⟩

end CertificateData

section OrderedRing

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Helper for Theorem 3.4: any Farkas certificate rules out a feasible solution. -/
lemma farkas_certificate_excludes_solution
    {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m n 𝕜} {b u : m → 𝕜} (hu : IsFarkasCertificate A b u) :
    ¬ ∃ x : n → 𝕜, A *ᵥ x ≤ b := by
  -- Compare the weighted left-hand side against the weighted right-hand side.
  intro hx
  rcases hx with ⟨x, hx⟩
  have hle : u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b :=
    dotProduct_le_dotProduct_of_nonneg_left hx hu.nonneg
  -- Rewrite the weighted left-hand side using the annihilation hypothesis.
  have hzero : u ⬝ᵥ (A *ᵥ x) = 0 := by
    rw [Matrix.dotProduct_mulVec, hu.annihilates, zero_dotProduct]
  have hnonneg : 0 ≤ u ⬝ᵥ b := by
    simpa [hzero] using hle
  exact (not_lt_of_ge hnonneg) hu.negative_rhs

end OrderedRing

section OrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Helper for Theorem 3.4: an infeasible zero-dimensional system must contain a row
`0 ≤ b i` with negative right-hand side. -/
lemma exists_negative_rhs_of_infeasible_zero_dim
    {m : ℕ} (A : Matrix (Fin m) (Fin 0) 𝕜) (b : Fin m → 𝕜)
    (h_infeasible : ¬ ∃ x : Fin 0 → 𝕜, A *ᵥ x ≤ b) :
    ∃ i : Fin m, b i < 0 := by
  classical
  -- If every right-hand side were nonnegative, the unique `Fin 0` vector would be feasible.
  by_contra hneg
  have hb_nonneg : 0 ≤ b := by
    intro i
    by_contra hbi
    exact hneg ⟨i, lt_of_not_ge hbi⟩
  apply h_infeasible
  refine ⟨Fin.elim0, ?_⟩
  simpa using hb_nonneg

/-- Helper for Theorem 3.4: a negative zero-dimensional row yields the single-support Farkas
certificate. -/
lemma single_support_farkas_certificate_of_negative_rhs
    {m : ℕ} (A : Matrix (Fin m) (Fin 0) 𝕜) (b : Fin m → 𝕜) {i : Fin m}
    (hi : b i < 0) :
    IsFarkasCertificate A b (Pi.single i 1) := by
  refine
    { nonneg := ?_
      annihilates := ?_
      negative_rhs := ?_ }
  · -- The single-support multiplier is nonnegative coordinatewise.
    intro j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  · -- There are no columns in dimension zero, so annihilation is automatic.
    ext j
    exact Fin.elim0 j
  · -- Evaluating the single-support multiplier picks out the negative right-hand side.
    rw [single_dotProduct, one_mul]
    exact hi

/-- Helper for Theorem 3.4: a certificate on the step system lifts to a certificate on the original
system by summing the nonnegative row-combination weights. -/
lemma lift_farkas_certificate_from_fourier_step
    {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) 𝕜) (b : Fin m → 𝕜)
    {v : FourierStepIndex A → 𝕜}
    (hv : IsFarkasCertificate (fourier_step_matrix A) (fourier_step_rhs A b) v) :
    ∃ u : Fin m → 𝕜, IsFarkasCertificate A b u := by
  let u : Fin m → 𝕜 := ∑ s, v s • fourier_step_row_multiplier A s
  refine ⟨u, ?_⟩
  refine
    { nonneg := ?_
      annihilates := ?_
      negative_rhs := ?_ }
  · -- Each step-row multiplier is nonnegative, so their `v`-weighted sum stays nonnegative.
    intro i
    simpa [u, Fintype.sum_sum_type] using
      add_nonneg
        (Finset.sum_nonneg
          (fun s _ ↦
            mul_nonneg (hv.nonneg (Sum.inl s))
              ((fourier_step_row_multiplier_nonneg A (Sum.inl s)) i)))
        (Finset.sum_nonneg
          (fun s _ ↦
            mul_nonneg (hv.nonneg (Sum.inr s))
              ((fourier_step_row_multiplier_nonneg A (Sum.inr s)) i)))
  · -- The summed multiplier annihilates `A` because each step row reproduces a row of the
    -- eliminated system with zero last coordinate.
    have hu_vecMul :
        u ᵥ* A =
          ∑ s, v s •
            ((Fin.lastCases (0 : 𝕜) (fourier_step_matrix A s) : Fin (n + 1) → 𝕜)) := by
      calc
        u ᵥ* A = ∑ s, (v s • fourier_step_row_multiplier A s) ᵥ* A := by
          dsimp [u]
          rw [Matrix.sum_vecMul]
        _ = ∑ s, v s • (fourier_step_row_multiplier A s ᵥ* A) := by
          congr with s
          rw [Matrix.smul_vecMul]
        _ = ∑ s, v s •
            ((Fin.lastCases (0 : 𝕜) (fourier_step_matrix A s) : Fin (n + 1) → 𝕜)) := by
          congr with s
          rw [fourier_step_row_multiplier_vecMul]
    ext j
    rw [hu_vecMul]
    refine Fin.lastCases ?_ ?_ j
    · simp
    · intro j'
      have hcoord :
          (∑ s, v s •
              ((Fin.lastCases (0 : 𝕜) (fourier_step_matrix A s) : Fin (n + 1) → 𝕜)))
              (Fin.castSucc j') =
            (v ᵥ* fourier_step_matrix A) j' := by
        simp [Matrix.vecMul, dotProduct, Fin.lastCases_castSucc]
      exact hcoord.trans <| by simpa using congrFun hv.annihilates j'
  · -- The weighted right-hand side is preserved by the canonical step-row multipliers.
    have hu_rhs : u ⬝ᵥ b = v ⬝ᵥ fourier_step_rhs A b := by
      calc
        u ⬝ᵥ b = ∑ s, (v s • fourier_step_row_multiplier A s) ⬝ᵥ b := by
          dsimp [u]
          rw [sum_dotProduct]
        _ = ∑ s, v s • (fourier_step_row_multiplier A s ⬝ᵥ b) := by
          congr with s
          rw [smul_dotProduct]
        _ = ∑ s, v s • fourier_step_rhs A b s := by
          congr with s
          rw [fourier_step_row_multiplier_dot_rhs]
        _ = v ⬝ᵥ fourier_step_rhs A b := by
          rfl
    rw [hu_rhs]
    exact hv.negative_rhs

/-- Helper for Theorem 3.4: every infeasible finite system of linear inequalities admits a Farkas
certificate. -/
lemma exists_farkas_certificate_of_infeasible_fin
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) (b : Fin m → 𝕜)
    (h_infeasible : ¬ ∃ x : Fin n → 𝕜, A *ᵥ x ≤ b) :
    ∃ u : Fin m → 𝕜, IsFarkasCertificate A b u := by
  induction n generalizing m b with
  | zero =>
      -- In dimension zero, infeasibility means that some residual inequality is `0 ≤ b i < 0`.
      rcases exists_negative_rhs_of_infeasible_zero_dim A b h_infeasible with ⟨i, hi⟩
      exact ⟨Pi.single i 1, single_support_farkas_certificate_of_negative_rhs A b hi⟩
  | succ n ih =>
      classical
      -- Any feasible point for the step system would extend to a feasible point for the original
      -- system, contradicting the induction hypothesis.
      have h_step_infeasible :
          ¬ ∃ x : Fin n → 𝕜, fourier_step_matrix A *ᵥ x ≤ fourier_step_rhs A b := by
        intro hx
        rcases hx with ⟨x, hx⟩
        rcases (fourier_motzkin_step_iff_exists_last_coordinate A b x).1 hx with ⟨x_last, hx_last⟩
        exact h_infeasible ⟨Fin.snoc x x_last, hx_last⟩
      let e : FourierStepIndex A ≃ Fin (Fintype.card (FourierStepIndex A)) :=
        Fintype.equivFin (FourierStepIndex A)
      let A' : Matrix (Fin (Fintype.card (FourierStepIndex A))) (Fin n) 𝕜 :=
        (fourier_step_matrix A).reindex e (Equiv.refl _)
      let b' : Fin (Fintype.card (FourierStepIndex A)) → 𝕜 := fourier_step_rhs A b ∘ e.symm
      have h_reindex_solution :
          (∃ x : Fin n → 𝕜, A' *ᵥ x ≤ b') ↔
            ∃ x : Fin n → 𝕜, fourier_step_matrix A *ᵥ x ≤ fourier_step_rhs A b := by
        simpa [A', b', e] using
          exists_solution_reindex_iff e (Equiv.refl (Fin n))
            (fourier_step_matrix A) (fourier_step_rhs A b)
      have h_reindex_certificate :
          (∃ u : Fin (Fintype.card (FourierStepIndex A)) → 𝕜, IsFarkasCertificate A' b' u) ↔
            ∃ u : FourierStepIndex A → 𝕜,
              IsFarkasCertificate (fourier_step_matrix A) (fourier_step_rhs A b) u := by
        simpa [A', b', e] using
          exists_isFarkasCertificate_reindex_iff e (Equiv.refl (Fin n))
            (fourier_step_matrix A) (fourier_step_rhs A b)
      have hA'_infeasible : ¬ ∃ x : Fin n → 𝕜, A' *ᵥ x ≤ b' := by
        intro hx
        exact h_step_infeasible (h_reindex_solution.mp hx)
      rcases ih A' b' hA'_infeasible with ⟨u', hu'⟩
      rcases h_reindex_certificate.mp ⟨u', hu'⟩ with ⟨v, hv⟩
      exact lift_farkas_certificate_from_fourier_step A b hv

/-- Helper for Theorem 3.4: the `Fin`-indexed Fourier-Motzkin induction proving Farkas' Lemma. -/
theorem farkas_lemma_linear_inequalities_fin
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) (b : Fin m → 𝕜) :
    (¬ ∃ x : Fin n → 𝕜, A *ᵥ x ≤ b) ↔
      ∃ u : Fin m → 𝕜, IsFarkasCertificate A b u := by
  constructor
  · -- The hard direction is the inductive Fourier-Motzkin construction of a certificate.
    intro h_infeasible
    exact exists_farkas_certificate_of_infeasible_fin A b h_infeasible
  · -- The easy direction is the standard weighted-inequality contradiction.
    rintro ⟨u, hu⟩
    exact farkas_certificate_excludes_solution hu

/-- Theorem 3.4 (Farkas’ Lemma). A finite system of linear inequalities `A *ᵥ x ≤ b` is
infeasible if and only if there is a nonnegative multiplier vector `u` such that `u ᵥ* A = 0`
and `u ⬝ᵥ b < 0`. -/
theorem farkas_lemma_linear_inequalities
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n 𝕜) (b : m → 𝕜) :
    (¬ ∃ x : n → 𝕜, A *ᵥ x ≤ b) ↔ ∃ u : m → 𝕜, IsFarkasCertificate A b u := by
  classical
  let em : m ≃ Fin (Fintype.card m) := Fintype.equivFin m
  let en : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  let A' : Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) 𝕜 := A.reindex em en
  let b' : Fin (Fintype.card m) → 𝕜 := b ∘ em.symm
  have hfeasible :
      (∃ x : Fin (Fintype.card n) → 𝕜, A' *ᵥ x ≤ b') ↔ ∃ x : n → 𝕜, A *ᵥ x ≤ b := by
    simpa [A', b', em, en] using exists_solution_reindex_iff em en A b
  have hcertificate :
      (∃ u : Fin (Fintype.card m) → 𝕜, IsFarkasCertificate A' b' u) ↔
        ∃ u : m → 𝕜, IsFarkasCertificate A b u := by
    simpa [A', b', em, en] using exists_isFarkasCertificate_reindex_iff em en A b
  exact
    (not_congr hfeasible).symm.trans <|
      (farkas_lemma_linear_inequalities_fin A' b').trans hcertificate

end OrderedField
