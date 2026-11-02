import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

open InnerProductSpace Module Set Submodule

universe u

section Lemma93

variable {n : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Lemma 9.3: a Step 1 update keeps each updated earlier basis vector inside the
corresponding original prefix span. -/
lemma updatedBasisVectorMemOriginalPrefixSpan
    (B B' : Basis (Fin n) ℝ E)
    (hstep : ∀ j, B' j - B j ∈ span ℝ (B '' Iio j))
    {i j : Fin n} (hij : i < j) :
    B' i ∈ span ℝ (B '' Iio j) := by
  -- The update error already lies in an earlier prefix, so the updated vector stays in the
  -- larger original prefix span.
  have hdiff : B' i - B i ∈ span ℝ (B '' Iio j) := by
    exact (span_mono (image_mono <| Iio_subset_Iio hij.le)) (hstep i)
  have hbase : B i ∈ span ℝ (B '' Iio j) := subset_span ⟨i, hij, rfl⟩
  -- Reassemble the updated vector from its original part and the Step 1 correction.
  simpa [add_comm] using Submodule.add_mem (span ℝ (B '' Iio j)) hdiff hbase

/-- Helper for Lemma 9.3: each original earlier basis vector lies in the updated prefix span
after a Step 1 update. -/
lemma originalBasisVectorMemUpdatedPrefixSpan
    (B B' : Basis (Fin n) ℝ E)
    (hstep : ∀ j, B' j - B j ∈ span ℝ (B '' Iio j))
    {i j : Fin n} (hij : i < j) :
    B i ∈ span ℝ (B' '' Iio j) := by
  -- Use well-founded induction on the index to transport each original generator into the
  -- updated prefix span.
  let P : Fin n → Prop := fun i => ∀ j : Fin n, i < j → B i ∈ span ℝ (B' '' Iio j)
  have haux : ∀ i : Fin n, P i := by
    intro i
    refine wellFounded_lt.induction i ?_
    intro i ih j hij
    have hbase : B' i ∈ span ℝ (B' '' Iio j) := subset_span ⟨i, hij, rfl⟩
    have hcorr : B' i - B i ∈ span ℝ (B' '' Iio j) := by
      refine (span_le.2 ?_) (hstep i)
      intro x hx
      rcases hx with ⟨k, hk, rfl⟩
      exact ih k hk j (hk.trans hij)
    -- Recover the original vector by subtracting the earlier-prefix correction from the
    -- updated vector.
    simpa using Submodule.sub_mem (span ℝ (B' '' Iio j)) hbase hcorr
  exact haux i j hij

/-- Helper for Lemma 9.3: the original and updated earlier prefix spans agree at every index. -/
lemma prefixSpanEqOfStepOneUpdate
    (B B' : Basis (Fin n) ℝ E)
    (hstep : ∀ j, B' j - B j ∈ span ℝ (B '' Iio j))
    (j : Fin n) :
    span ℝ (B '' Iio j) = span ℝ (B' '' Iio j) := by
  -- Compare the two spans by transporting each family of generators to the other prefix span.
  apply le_antisymm
  · refine span_le.2 ?_
    intro x hx
    rcases hx with ⟨i, hij, rfl⟩
    exact originalBasisVectorMemUpdatedPrefixSpan B B' hstep hij
  · refine span_le.2 ?_
    intro x hx
    rcases hx with ⟨i, hij, rfl⟩
    exact updatedBasisVectorMemOriginalPrefixSpan B B' hstep hij

/-- Helper for Lemma 9.3: the correction term in the Gram-Schmidt decomposition of a basis
vector uses only earlier prefix directions. -/
lemma basisVectorSubGramSchmidtMemPrefixSpan
    (C : Basis (Fin n) ℝ E) (j : Fin n) :
    C j - gramSchmidt ℝ C j ∈ span ℝ (C '' Iio j) := by
  have hsum :
      ∑ i ∈ Iio j, (ℝ ∙ gramSchmidt ℝ C i).starProjection (C j) ∈
        span ℝ (gramSchmidt ℝ C '' Iio j) := by
    -- Each projection term lands in the line of an earlier Gram-Schmidt vector, hence in the
    -- span of the earlier Gram-Schmidt family.
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hgen : gramSchmidt ℝ C i ∈ span ℝ (gramSchmidt ℝ C '' Iio j) := by
      exact subset_span ⟨i, by simpa using hi, rfl⟩
    have hle : ℝ ∙ gramSchmidt ℝ C i ≤ span ℝ (gramSchmidt ℝ C '' Iio j) := by
      exact (Submodule.span_singleton_le_iff_mem _ _).2 hgen
    exact hle <| Submodule.starProjection_apply_mem (ℝ ∙ gramSchmidt ℝ C i) (C j)
  have hdecomp :
      C j - gramSchmidt ℝ C j =
        ∑ i ∈ Iio j, (ℝ ∙ gramSchmidt ℝ C i).starProjection (C j) := by
    -- Rewrite the standard Gram-Schmidt decomposition into a correction-term identity.
    rw [sub_eq_iff_eq_add']
    simpa [add_comm, add_left_comm, add_assoc] using gramSchmidt_def' ℝ C j
  have hmem : C j - gramSchmidt ℝ C j ∈ span ℝ (gramSchmidt ℝ C '' Iio j) := by
    rw [hdecomp]
    exact hsum
  -- Transport the correction term from the Gram-Schmidt prefix span back to the original basis
  -- prefix span.
  rwa [span_gramSchmidt_Iio ℝ C j] at hmem

/-- Helper for Lemma 9.3: each Gram-Schmidt vector is orthogonal to the span of the earlier
input basis vectors. -/
lemma gramSchmidtMemPrefixOrthogonal
    (C : Basis (Fin n) ℝ E) (j : Fin n) :
    gramSchmidt ℝ C j ∈ (span ℝ (C '' Iio j))ᗮ := by
  -- Move the earlier span to the Gram-Schmidt family, where orthogonality is checked on
  -- generators and extended by span induction.
  rw [Submodule.mem_orthogonal']
  intro u hu
  rw [← span_gramSchmidt_Iio ℝ C j] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, hi, rfl⟩
      rw [inner_eq_zero_symm]
      exact gramSchmidt_orthogonal ℝ C hi.ne
  | zero =>
      simp
  | add x y hx hy hx0 hy0 =>
      simp [inner_add_right, hx0, hy0]
  | smul a x hx hx0 =>
      simp [inner_smul_right, hx0]

/-- Lemma 9.3. If a Step 1 size-reduction update changes each basis vector only by a linear
combination of earlier basis vectors, then the Gram-Schmidt basis is unchanged. -/
theorem basis_reduction_step_one_preserves_gram_schmidt_basis
    {n : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B B' : Basis (Fin n) ℝ E)
    (hstep : ∀ j, B' j - B j ∈ span ℝ (B '' Iio j)) :
    gramSchmidtBasis B = gramSchmidtBasis B' := by
  -- Route correction: prove pointwise equality of the Gram-Schmidt vectors by showing their
  -- difference lies both in the common earlier prefix span and in its orthogonal complement.
  ext j
  let K : Submodule ℝ E := span ℝ (B '' Iio j)
  have hprefix : span ℝ (B '' Iio j) = span ℝ (B' '' Iio j) :=
    prefixSpanEqOfStepOneUpdate B B' hstep j
  have hstepj : B' j - B j ∈ K := by
    simpa [K] using hstep j
  have hcorrB : B j - gramSchmidt ℝ B j ∈ K := by
    -- The original Gram-Schmidt correction already belongs to the common prefix span.
    simpa [K] using basisVectorSubGramSchmidtMemPrefixSpan B j
  have hcorrB' : B' j - gramSchmidt ℝ B' j ∈ K := by
    -- Transport the updated correction term across the prefix-span equality.
    dsimp [K]
    rw [hprefix]
    exact basisVectorSubGramSchmidtMemPrefixSpan B' j
  have horthB : gramSchmidt ℝ B j ∈ Kᗮ := by
    -- The original Gram-Schmidt vector is orthogonal to the earlier prefix span.
    simpa [K] using gramSchmidtMemPrefixOrthogonal B j
  have horthB' : gramSchmidt ℝ B' j ∈ Kᗮ := by
    -- Transport the updated orthogonality statement across the same common-prefix equality.
    dsimp [K]
    rw [hprefix]
    exact gramSchmidtMemPrefixOrthogonal B' j
  have hspan :
      gramSchmidt ℝ B' j - gramSchmidt ℝ B j ∈ K := by
    -- Subtract the two decomposition formulas and insert the Step 1 correction term.
    have hrewrite :
        gramSchmidt ℝ B' j - gramSchmidt ℝ B j =
          (B' j - B j) - (B' j - gramSchmidt ℝ B' j) + (B j - gramSchmidt ℝ B j) := by
      abel_nf
    rw [hrewrite]
    exact Submodule.add_mem K (Submodule.sub_mem K hstepj hcorrB') hcorrB
  have horth :
      gramSchmidt ℝ B' j - gramSchmidt ℝ B j ∈ Kᗮ := by
    -- The same difference stays orthogonal because both Gram-Schmidt vectors are.
    exact Submodule.sub_mem Kᗮ horthB' horthB
  have hzero : gramSchmidt ℝ B' j - gramSchmidt ℝ B j = 0 := by
    -- The common prefix span has trivial intersection with its orthogonal complement.
    have hmem : gramSchmidt ℝ B' j - gramSchmidt ℝ B j ∈ K ⊓ Kᗮ := ⟨hspan, horth⟩
    simpa [K.inf_orthogonal_eq_bot] using hmem
  simpa [coe_gramSchmidtBasis] using (sub_eq_zero.mp hzero).symm

/-- The Step 1 update from Lemma 9.3 also leaves the underlying Gram-Schmidt vector family
unchanged. -/
theorem gram_schmidt_eq_of_step_one
    {n : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B B' : Basis (Fin n) ℝ E)
    (hstep : ∀ j, B' j - B j ∈ span ℝ (B '' Iio j)) :
    gramSchmidt ℝ B = gramSchmidt ℝ B' := by
  simpa [coe_gramSchmidtBasis] using
    congrArg (fun b : Basis (Fin n) ℝ E ↦ (b : Fin n → E))
      (basis_reduction_step_one_preserves_gram_schmidt_basis B B' hstep)

end Lemma93
