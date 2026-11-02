import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_definition_3_15_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix NonnegativeRankNotation

universe u v w

/-- Helper for Theorem 4.51: a face of `P` is facet-like when it is a proper face that is maximal
among proper faces of `P`. This local wrapper keeps only the face API that Theorem 4.51 uses,
without importing the heavier Section 3.8 development. -/
class maximalProperFace {n : ℕ} (P F : Set (Fin n → ℝ)) : Prop where
  /-- A maximal proper face is, in particular, a proper face. -/
  isProper : is_proper_face P F
  /-- Any proper face of `P` containing `F` must equal `F`. -/
  maximal (G : Set (Fin n → ℝ)) (hG : is_proper_face P G) (hFG : F ⊆ G) : G = F

/-- Helper for Theorem 4.51: every maximal proper face is a proper face. -/
theorem maximalProperFace_to_isProperFace {n : ℕ} {P F : Set (Fin n → ℝ)}
    (hF : maximalProperFace P F) : is_proper_face P F :=
  hF.isProper

/-- Helper for Theorem 4.51: an inequality is facet-like when it is valid on `P` and its equality
face is a maximal proper face. -/
class maximalProperFaceInequality {n : ℕ}
    (P : Set (Fin n → ℝ)) (c : Fin n → ℝ) (δ : ℝ) : Prop where
  /-- The inequality is valid on all of `P`. -/
  valid : is_valid_inequality P c δ
  /-- The induced equality face is maximal among proper faces. -/
  facet : maximalProperFace P (face_set P c δ)

/-- Helper for Theorem 4.51: a maximal-proper-face inequality is valid on `P`. -/
theorem maximalProperFaceInequality_valid {n : ℕ} {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ} {δ : ℝ} (h : maximalProperFaceInequality P c δ) :
    is_valid_inequality P c δ :=
  h.valid

/-- Helper for Theorem 4.51: the equality face of a maximal-proper-face inequality is a maximal
proper face. -/
theorem maximalProperFaceInequality_isFacet {n : ℕ} {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ} {δ : ℝ} (h : maximalProperFaceInequality P c δ) :
    maximalProperFace P (face_set P c δ) :=
  h.facet

/-- If `P` is both the convex hull of the listed vertices and the polyhedron `A x ≤ b`, then each
listed vertex satisfies `A x ≤ b`. -/
theorem vertices_feasible_of_polytope_description
    {m n p : ℕ}
    (P : Set (Fin n → ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (vertices : Fin p → Fin n → ℝ)
    (hP_vertices : P = convexHull ℝ (Set.range vertices))
    (hP_system : P = polyhedron_le_set A b) :
    ∀ j, A *ᵥ vertices j ≤ b := by
  have hvertices : ∀ j, A *ᵥ vertices j ≤ b := by
    intro j
    have hj : vertices j ∈ convexHull ℝ (Set.range vertices) :=
      (subset_convexHull ℝ (Set.range vertices)) (Set.mem_range_self j)
    rw [← hP_vertices, hP_system] at hj
    exact mem_polyhedron_le_set_iff.mp hj
  exact hvertices

/-- A purely inequality-based lifted feasible set `Aineq x + Bineq z ≤ bineq`. This auxiliary
owner remains available for inequality-only special cases of linear extended formulations. -/
def linear_inequality_extended_system
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (Aineq : Matrix σ ι ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ) : Set ((ι → ℝ) × (κ → ℝ)) :=
  {xz | Aineq.mulVec xz.1 + Bineq.mulVec xz.2 ≤ bineq}

/-- Helper for Theorem 4.51: on a nonempty raw system `{x | A *ᵥ x ≤ b}` indexed by arbitrary
finite types, validity of `c ⬝ᵥ x ≤ δ` is equivalent to a nonnegative row multiplier
certificate. -/
lemma valid_inequality_iff_exists_nonneg_row_multiplier_raw
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ)
    (b : m → ℝ)
    (c : n → ℝ)
    (δ : ℝ)
    (hP_nonempty : Set.Nonempty {x : n → ℝ | A *ᵥ x ≤ b}) :
    is_valid_inequality {x : n → ℝ | A *ᵥ x ≤ b} c δ ↔
      ∃ u : m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ := by
  let M : Matrix (n ⊕ Unit) (m ⊕ Unit) ℝ :=
    Matrix.fromBlocks A.transpose 0 (fun _ i ↦ b i) (1 : Matrix Unit Unit ℝ)
  let d : (n ⊕ Unit) → ℝ := Sum.elim c fun _ ↦ δ
  have htranspose_mulVec (u : m → ℝ) : A.transpose *ᵥ u = u ᵥ* A := by
    simpa using (Matrix.vecMul_transpose A.transpose u).symm
  have hbottom_block_mulVec (u : m → ℝ) :
      ((fun _ i ↦ b i : Matrix Unit m ℝ) *ᵥ u) () = u ⬝ᵥ b := by
    change ∑ i, b i * u i = u ⬝ᵥ b
    simpa [dotProduct] using dotProduct_comm b u
  have hrow_eval (w : (n ⊕ Unit) → ℝ) (i : m) :
      (w ᵥ* M) (Sum.inl i) = (A *ᵥ (w ∘ Sum.inl)) i + w (Sum.inr ()) * b i := by
    have htop : ((w ∘ Sum.inl) ᵥ* A.transpose) i = (A *ᵥ (w ∘ Sum.inl)) i := by
      simpa using congrFun (Matrix.vecMul_transpose A (w ∘ Sum.inl)) i
    calc
      (w ᵥ* M) (Sum.inl i)
          = ((w ∘ Sum.inl) ᵥ* A.transpose) i + ((w ∘ Sum.inr) ᵥ* (fun _ j ↦ b j)) i := by
              simp [M, Matrix.vecMul_fromBlocks]
      _ = (A *ᵥ (w ∘ Sum.inl)) i + ((w ∘ Sum.inr) ᵥ* (fun _ j ↦ b j)) i := by
            rw [htop]
      _ = (A *ᵥ (w ∘ Sum.inl)) i + w (Sum.inr ()) * b i := by
            simp [Matrix.vecMul, dotProduct]
  have hslack_eval (w : (n ⊕ Unit) → ℝ) :
      (w ᵥ* M) (Sum.inr ()) = w (Sum.inr ()) := by
    simp [M, Matrix.vecMul_fromBlocks]
  have hdual_eval (w : (n ⊕ Unit) → ℝ) :
      w ⬝ᵥ d = c ⬝ᵥ (w ∘ Sum.inl) + w (Sum.inr ()) * δ := by
    have hw : w = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) := by
      funext s
      rcases s with j | u
      · rfl
      · cases u
        rfl
    calc
      w ⬝ᵥ d = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) ⬝ᵥ Sum.elim c (fun _ ↦ δ) := by
        simpa [d] using congrArg (fun z => z ⬝ᵥ d) hw
      _ = (w ∘ Sum.inl) ⬝ᵥ c + (w ∘ Sum.inr) ⬝ᵥ (fun _ ↦ δ) := by
        simpa using
          sumElim_dotProduct_sumElim (w ∘ Sum.inl) c ((w ∘ Sum.inr) : Unit → ℝ)
            (fun _ : Unit ↦ δ)
      _ = c ⬝ᵥ (w ∘ Sum.inl) + w (Sum.inr ()) * δ := by
        simp [dotProduct_comm]
  have hfeasible :
      (∃ z : m ⊕ Unit → ℝ, M *ᵥ z = d ∧ 0 ≤ z) ↔
        ∃ u : m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ := by
    constructor
    · rintro ⟨z, hz, hz_nonneg⟩
      let u : m → ℝ := z ∘ Sum.inl
      have hu_row : u ᵥ* A = c := by
        ext j
        have hj : (M *ᵥ z) (Sum.inl j) = d (Sum.inl j) :=
          congrFun hz (Sum.inl j)
        simpa [M, d, u, Matrix.fromBlocks_mulVec, htranspose_mulVec u] using hj
      have hu_eval_le : u ⬝ᵥ b ≤ δ := by
        have hbottom : (M *ᵥ z) (Sum.inr ()) = d (Sum.inr ()) :=
          congrFun hz (Sum.inr ())
        have hs_nonneg : 0 ≤ z (Sum.inr ()) := hz_nonneg (Sum.inr ())
        have hbottom' : u ⬝ᵥ b + z (Sum.inr ()) = δ := by
          simpa [M, d, u, Matrix.fromBlocks_mulVec, hbottom_block_mulVec] using hbottom
        linarith
      exact ⟨u, fun i ↦ hz_nonneg (Sum.inl i), hu_row, hu_eval_le⟩
    · rintro ⟨u, hu_nonneg, hu_row, hu_eval_le⟩
      let z : m ⊕ Unit → ℝ := Sum.elim u fun _ ↦ δ - u ⬝ᵥ b
      refine ⟨z, ?_, ?_⟩
      · ext s
        rcases s with j | u'
        · simpa [M, d, z, Matrix.fromBlocks_mulVec, htranspose_mulVec u] using congrFun hu_row j
        · cases u'
          have hbottom : u ⬝ᵥ b + (δ - u ⬝ᵥ b) = δ := by ring
          simp [M, d, z, Matrix.fromBlocks_mulVec, hbottom_block_mulVec, hbottom]
      · intro s
        rcases s with i | u'
        · exact hu_nonneg i
        · cases u'
          exact sub_nonneg.mpr hu_eval_le
  have hdual :
      (∀ w : (n ⊕ Unit) → ℝ, w ᵥ* M ≤ 0 → w ⬝ᵥ d ≤ 0) ↔
        ∀ ⦃x : n → ℝ⦄, x ∈ {x : n → ℝ | A *ᵥ x ≤ b} → c ⬝ᵥ x ≤ δ := by
    constructor
    · intro h x hx
      let w : (n ⊕ Unit) → ℝ := Sum.elim x fun _ ↦ (-1 : ℝ)
      have hw : w ᵥ* M ≤ 0 := by
        intro s
        rcases s with i | u
        · have hi : (A *ᵥ x) i + w (Sum.inr ()) * b i ≤ 0 := by
            simpa [w, sub_eq_add_neg] using sub_nonpos.mpr (hx i)
          simpa [hrow_eval, w] using hi
        · cases u
          have hneg : (-1 : ℝ) ≤ 0 := neg_nonpos.mpr zero_le_one
          simpa [hslack_eval, w, hneg] using hneg
      have hwd : w ⬝ᵥ d ≤ 0 := h w hw
      have hsub : c ⬝ᵥ x - δ ≤ 0 := by
        simpa [hdual_eval, w, sub_eq_add_neg] using hwd
      exact sub_nonpos.mp hsub
    · intro hvalid w hw
      let x : n → ℝ := w ∘ Sum.inl
      let α : ℝ := w (Sum.inr ())
      have hα_nonpos : α ≤ 0 := by
        simpa [α, hslack_eval] using hw (Sum.inr ())
      rcases lt_or_eq_of_le hα_nonpos with hα_neg | hα_zero
      · let t : ℝ := -α
        have ht_pos : 0 < t := by
          simpa [t] using neg_pos.mpr hα_neg
        let y : n → ℝ := t⁻¹ • x
        have hy : y ∈ {x : n → ℝ | A *ᵥ x ≤ b} := by
          intro i
          have hi : (A *ᵥ x) i + α * b i ≤ 0 := by
            simpa [x, α, hrow_eval] using hw (Sum.inl i)
          have hbound : (A *ᵥ x) i ≤ t * b i := by
            have hsub : (A *ᵥ x) i - t * b i ≤ 0 := by
              simpa [t, sub_eq_add_neg] using hi
            exact sub_nonpos.mp hsub
          calc
            (A *ᵥ y) i = t⁻¹ * (A *ᵥ x) i := by
              simp [y, Matrix.mulVec_smul]
            _ ≤ t⁻¹ * (t * b i) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr ht_pos.le)
            _ = b i := by
              rw [← mul_assoc, inv_mul_cancel₀ ht_pos.ne', one_mul]
        have hy_valid : c ⬝ᵥ y ≤ δ := hvalid hy
        have hx_eq : x = t • y := by
          ext j
          dsimp [y]
          calc
            x j = (t * t⁻¹) * x j := by rw [mul_inv_cancel₀ ht_pos.ne', one_mul]
            _ = t * (t⁻¹ * x j) := by ring
        have hwd_eq : w ⬝ᵥ d = t * (c ⬝ᵥ y - δ) := by
          calc
            w ⬝ᵥ d = c ⬝ᵥ x + α * δ := by
              simp [x, α, hdual_eval]
            _ = c ⬝ᵥ (t • y) - t * δ := by
              simp [hx_eq, t, α]
            _ = t * (c ⬝ᵥ y) - t * δ := by
              rw [dotProduct_smul, smul_eq_mul]
            _ = t * (c ⬝ᵥ y - δ) := by ring
        rw [hwd_eq]
        exact mul_nonpos_of_nonneg_of_nonpos ht_pos.le (sub_nonpos.mpr hy_valid)
      · have hdir : A *ᵥ x ≤ 0 := by
          intro i
          have hi : (A *ᵥ x) i + α * b i ≤ 0 := by
            simpa [x, α, hrow_eval] using hw (Sum.inl i)
          simpa [hα_zero] using hi
        obtain ⟨x₀, hx₀⟩ := hP_nonempty
        have hcx_nonpos : c ⬝ᵥ x ≤ 0 := by
          by_contra hcx
          have hcx_pos : 0 < c ⬝ᵥ x := lt_of_not_ge hcx
          let t : ℝ := (δ - c ⬝ᵥ x₀ + 1) / (c ⬝ᵥ x)
          have ht_nonneg : 0 ≤ t := by
            dsimp [t]
            refine div_nonneg ?_ hcx_pos.le
            linarith [hvalid hx₀]
          have hxt : x₀ + t • x ∈ {x : n → ℝ | A *ᵥ x ≤ b} := by
            intro i
            have hmuli : t * (A *ᵥ x) i ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos ht_nonneg (hdir i)
            have hsum : (A *ᵥ x₀) i + t * (A *ᵥ x) i ≤ b i := by
              linarith [hx₀ i]
            simpa [Matrix.mulVec_add, Matrix.mulVec_smul] using hsum
          have hxt_valid : c ⬝ᵥ (x₀ + t • x) ≤ δ := hvalid hxt
          have ht_mul : t * (c ⬝ᵥ x) = δ - c ⬝ᵥ x₀ + 1 := by
            dsimp [t]
            field_simp [hcx_pos.ne']
          have : δ + 1 ≤ δ := by
            calc
              δ + 1 = c ⬝ᵥ x₀ + t * (c ⬝ᵥ x) := by
                linarith
              _ = c ⬝ᵥ (x₀ + t • x) := by
                rw [dotProduct_add, dotProduct_smul]
                simp [smul_eq_mul]
              _ ≤ δ := hxt_valid
          linarith
        simpa [x, α, hα_zero, hdual_eval] using hcx_nonpos
  have hcertificate :
      (∃ u : m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ) ↔
        ∀ w : (n ⊕ Unit) → ℝ, w ᵥ* M ≤ 0 → w ⬝ᵥ d ≤ 0 :=
    hfeasible.symm.trans <|
      feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers M d
  exact hdual.symm.trans hcertificate.symm

-- Semantic search note: no existing canonical owner for a polytope's intrinsic nonnegative rank
-- was found in the current environment, so Theorem 4.51 uses a same-file source-faithful witness:
-- either `P` is a singleton, or `t` is the nonnegative rank of a slack matrix built from a
-- facet presentation of `P`.
/-- Auxiliary witness that `t` is the intrinsic nonnegative rank of `P`: either `P` is a
singleton, or `t` is realized by the slack matrix of a facet-based description of `P`. -/
def IsNonnegativeRankOfPolytope
    {n : ℕ}
    (P : Set (Fin n → ℝ))
    (t : ℕ) : Prop :=
  (∃ x : Fin n → ℝ, P = {x} ∧ t = 0) ∨
    ∃ m p : ℕ,
      ∃ A : Matrix (Fin m) (Fin n) ℝ,
        ∃ b : Fin m → ℝ,
          ∃ vertices : Fin p → Fin n → ℝ,
              ∃ hP_vertices : P = convexHull ℝ (Set.range vertices),
              ∃ hP_system : P = polyhedron_le_set A b,
                (∀ i : Fin m, maximalProperFaceInequality P (A i) (b i)) ∧
                  let hvertices :=
                    vertices_feasible_of_polytope_description P A b vertices hP_vertices hP_system
                  let S : Matrix.Nonnegative (Fin m) (Fin p) ℝ :=
                    ⟨slack_matrix A b vertices, slack_matrix_nonneg hvertices⟩
                  rank₊ S = t

/-- Helper for Theorem 4.51: stacking the equality block with its negation turns
`linear_extended_system Aeq Beq beq Aineq Bineq bineq` into one pure inequality system on the
combined coordinates `Sum.elim x z`. -/
lemma mem_stackedLinearExtendedSystem_iff
    {n : ℕ}
    {ρ : Type u} {σ : Type v} {κ : Type w}
    [Fintype ρ] [Fintype σ] [Fintype κ]
    (Aeq : Matrix ρ (Fin n) ℝ)
    (Beq : Matrix ρ κ ℝ)
    (beq : ρ → ℝ)
    (Aineq : Matrix σ (Fin n) ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ)
    (x : Fin n → ℝ)
    (z : κ → ℝ) :
    Matrix.fromRows
        (Matrix.fromRows (Matrix.fromCols Aineq Bineq) (Matrix.fromCols Aeq Beq))
        (-Matrix.fromCols Aeq Beq) *ᵥ
          Sum.elim x z ≤
      Sum.elim (Sum.elim bineq beq) (-beq) ↔
        (x, z) ∈ linear_extended_system Aeq Beq beq Aineq Bineq bineq := by
  constructor
  · intro hx
    rw [mem_linear_extended_system_iff]
    constructor
    · apply le_antisymm
      · intro i
        -- The middle block recovers the forward equality inequality.
        have hi :
            (Matrix.fromRows
                (Matrix.fromRows (Matrix.fromCols Aineq Bineq) (Matrix.fromCols Aeq Beq))
                (-Matrix.fromCols Aeq Beq) *ᵥ
                  Sum.elim x z) (Sum.inl (Sum.inr i)) ≤
              Sum.elim (Sum.elim bineq beq) (-beq) (Sum.inl (Sum.inr i)) :=
          hx (Sum.inl (Sum.inr i))
        simpa [Matrix.fromRows_mulVec, Matrix.fromRows_fromCols_eq_fromBlocks,
          Matrix.fromBlocks_mulVec, Pi.add_apply] using hi
      · intro i
        -- The bottom block supplies the reverse inequality after removing the minus signs.
        have hi :
            (Matrix.fromRows
                (Matrix.fromRows (Matrix.fromCols Aineq Bineq) (Matrix.fromCols Aeq Beq))
                (-Matrix.fromCols Aeq Beq) *ᵥ
                  Sum.elim x z) (Sum.inr i) ≤
              Sum.elim (Sum.elim bineq beq) (-beq) (Sum.inr i) :=
          hx (Sum.inr i)
        have hi' : -((Aeq *ᵥ x + Beq *ᵥ z) i) ≤ (-beq) i := by
          simpa [Matrix.fromRows_mulVec, Matrix.fromRows_fromCols_eq_fromBlocks,
            Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, Pi.add_apply, add_comm] using hi
        simpa [add_comm] using (neg_le_neg_iff.mp hi')
    · intro i
      -- The top block is exactly the original inequality system.
      have hi :
          (Matrix.fromRows
              (Matrix.fromRows (Matrix.fromCols Aineq Bineq) (Matrix.fromCols Aeq Beq))
              (-Matrix.fromCols Aeq Beq) *ᵥ
                Sum.elim x z) (Sum.inl (Sum.inl i)) ≤
            Sum.elim (Sum.elim bineq beq) (-beq) (Sum.inl (Sum.inl i)) :=
        hx (Sum.inl (Sum.inl i))
      simpa [Matrix.fromRows_mulVec, Matrix.fromRows_fromCols_eq_fromBlocks,
        Matrix.fromBlocks_mulVec, Pi.add_apply] using hi
  · intro hx
    rw [mem_linear_extended_system_iff] at hx
    intro s
    rcases s with (i | i) | i
    · -- The inequality block is supplied directly by the membership certificate.
      simpa [Matrix.fromRows_mulVec, Matrix.fromRows_fromCols_eq_fromBlocks,
        Matrix.fromBlocks_mulVec, Pi.add_apply] using hx.2 i
    · -- Equality constraints contribute the forward inequality on the middle block.
      have hi : (Aeq *ᵥ x + Beq *ᵥ z) i ≤ beq i := le_of_eq (congrFun hx.1 i)
      simpa [Matrix.fromRows_mulVec, Matrix.fromRows_fromCols_eq_fromBlocks,
        Matrix.fromBlocks_mulVec, Pi.add_apply] using hi
    · -- The reverse equality block is the negation of the same equality.
      have hi : -((Aeq *ᵥ x + Beq *ᵥ z) i) ≤ (-beq) i := by
        simp [congrFun hx.1 i]
      simpa [Matrix.fromRows_mulVec, Matrix.fromRows_fromCols_eq_fromBlocks,
        Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, Pi.add_apply, add_comm] using hi

/-- Helper for Theorem 4.51: a nonnegative multiplier for the stacked pure-inequality encoding of
`Aineq x + Bineq z ≤ bineq`, `Aeq x + Beq z = beq` compresses to mixed multipliers on the original
inequality and equality blocks. -/
lemma existsMixedRowMultiplierOfStackedMultiplier
    {n : ℕ}
    {ρ : Type u} {σ : Type v} {κ : Type w}
    [Fintype ρ] [Fintype σ] [Fintype κ]
    (Aeq : Matrix ρ (Fin n) ℝ)
    (Beq : Matrix ρ κ ℝ)
    (beq : ρ → ℝ)
    (Aineq : Matrix σ (Fin n) ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ)
    (cₓ : Fin n → ℝ)
    (c_z : κ → ℝ)
    (δ : ℝ)
    (w : ((σ ⊕ ρ) ⊕ ρ) → ℝ)
    (hw_nonneg : 0 ≤ w)
    (hrow :
      w ᵥ*
        Matrix.fromRows
          (Matrix.fromRows (Matrix.fromCols Aineq Bineq) (Matrix.fromCols Aeq Beq))
          (-Matrix.fromCols Aeq Beq) =
        Sum.elim cₓ c_z)
    (hδ :
      w ⬝ᵥ Sum.elim (Sum.elim bineq beq) (-beq) ≤ δ) :
    ∃ u : σ → ℝ, ∃ v : ρ → ℝ,
      0 ≤ u ∧
        u ᵥ* Aineq + v ᵥ* Aeq = cₓ ∧
          u ᵥ* Bineq + v ᵥ* Beq = c_z ∧
            u ⬝ᵥ bineq + v ⬝ᵥ beq ≤ δ := by
  let u : σ → ℝ := (w ∘ Sum.inl) ∘ Sum.inl
  let v₁ : ρ → ℝ := (w ∘ Sum.inl) ∘ Sum.inr
  let v₂ : ρ → ℝ := w ∘ Sum.inr
  let v : ρ → ℝ := v₁ - v₂
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · -- Only the original inequality block inherits the nonnegativity requirement.
    intro s
    exact hw_nonneg (Sum.inl (Sum.inl s))
  · -- Evaluate the stacked row equation on the `x` coordinates.
    ext j
    have hj :
        (u ᵥ* Aineq) j + (v₁ ᵥ* Aeq) j - (v₂ ᵥ* Aeq) j = cₓ j := by
      simpa [Function.comp, u, v₁, v₂, Matrix.vecMul_fromRows,
        Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.vecMul_fromBlocks, Matrix.vecMul_neg,
        Pi.add_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        congrFun hrow (Sum.inl j)
    have hvj : (v ᵥ* Aeq) j = (v₁ ᵥ* Aeq) j - (v₂ ᵥ* Aeq) j := by
      simpa [v] using congrFun (Matrix.sub_vecMul Aeq v₁ v₂) j
    simpa [Pi.add_apply, hvj, sub_eq_add_neg, add_assoc] using hj
  · -- The same split on the `z` coordinates yields the second block equation.
    ext k
    have hk :
        (u ᵥ* Bineq) k + (v₁ ᵥ* Beq) k - (v₂ ᵥ* Beq) k = c_z k := by
      simpa [Function.comp, u, v₁, v₂, Matrix.vecMul_fromRows,
        Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.vecMul_fromBlocks, Matrix.vecMul_neg,
        Pi.add_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        congrFun hrow (Sum.inr k)
    have hvk : (v ᵥ* Beq) k = (v₁ ᵥ* Beq) k - (v₂ ᵥ* Beq) k := by
      simpa [v] using congrFun (Matrix.sub_vecMul Beq v₁ v₂) k
    simpa [Pi.add_apply, hvk, sub_eq_add_neg, add_assoc] using hk
  · -- The right-hand-side certificate splits across the three row blocks in the same way.
    have hw_split : w = Sum.elim (Sum.elim u v₁) v₂ := by
      funext r
      rcases r with (s | r) | r <;> rfl
    have hrhs :
        w ⬝ᵥ Sum.elim (Sum.elim bineq beq) (-beq) = u ⬝ᵥ bineq + v ⬝ᵥ beq := by
      calc
        w ⬝ᵥ Sum.elim (Sum.elim bineq beq) (-beq)
            = Sum.elim (Sum.elim u v₁) v₂ ⬝ᵥ Sum.elim (Sum.elim bineq beq) (-beq) := by
                rw [hw_split]
        _ = (Sum.elim u v₁) ⬝ᵥ Sum.elim bineq beq + v₂ ⬝ᵥ (-beq) := by
              rw [sumElim_dotProduct_sumElim]
        _ = (u ⬝ᵥ bineq + v₁ ⬝ᵥ beq) + v₂ ⬝ᵥ (-beq) := by
              rw [sumElim_dotProduct_sumElim]
        _ = u ⬝ᵥ bineq + v ⬝ᵥ beq := by
              simp [v, sub_eq_add_neg, add_assoc]
    rw [hrhs] at hδ
    exact hδ

/-- Helper for Theorem 4.51: every facet row of `P` admits an exact mixed multiplier certificate
with respect to any linear extended formulation of `P`. -/
lemma facetMultiplierExactOfExtendedFormulation
    {m n : ℕ}
    {ρ : Type u} {σ : Type v} {κ : Type w}
    [Fintype ρ] [Fintype σ] [Fintype κ]
    (P : Set (Fin n → ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (Aeq : Matrix ρ (Fin n) ℝ)
    (Beq : Matrix ρ κ ℝ)
    (beq : ρ → ℝ)
    (Aineq : Matrix σ (Fin n) ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ)
    (hfacets : ∀ i : Fin m, maximalProperFaceInequality P (A i) (b i))
    (hEF : P = Prod.fst '' linear_extended_system Aeq Beq beq Aineq Bineq bineq)
    (i : Fin m) :
    ∃ u : σ → ℝ, ∃ v : ρ → ℝ,
      0 ≤ u ∧
        u ᵥ* Aineq + v ᵥ* Aeq = A i ∧
          u ᵥ* Bineq + v ᵥ* Beq = 0 ∧
            u ⬝ᵥ bineq + v ⬝ᵥ beq = b i := by
  classical
  let M :
      Matrix ((σ ⊕ ρ) ⊕ ρ) (Fin n ⊕ κ) ℝ :=
    Matrix.fromRows
      (Matrix.fromRows (Matrix.fromCols Aineq Bineq) (Matrix.fromCols Aeq Beq))
      (-Matrix.fromCols Aeq Beq)
  let rhs : ((σ ⊕ ρ) ⊕ ρ) → ℝ := Sum.elim (Sum.elim bineq beq) (-beq)
  let c : Fin n ⊕ κ → ℝ := Sum.elim (A i) 0
  have hvalidFacet : is_valid_inequality P (A i) (b i) :=
    maximalProperFaceInequality_valid (hfacets i)
  have hface_nonempty : (face_set P (A i) (b i)).Nonempty := by
    have hproper :
        is_proper_face P (face_set P (A i) (b i)) := by
      exact maximalProperFace_to_isProperFace (maximalProperFaceInequality_isFacet (hfacets i))
    exact (is_proper_face_iff.mp hproper).2.1
  rcases hface_nonempty with ⟨x₀, hx₀_face⟩
  have hx₀P : x₀ ∈ P := (mem_face_set_iff.mp hx₀_face).1
  have hx₀_eq : A i ⬝ᵥ x₀ = b i := (mem_face_set_iff.mp hx₀_face).2
  rw [hEF] at hx₀P
  rcases hx₀P with ⟨⟨xLift, z₀⟩, hz₀, hxLift⟩
  have hxLift_eq : xLift = x₀ := by simpa using hxLift
  subst xLift
  have hstack_nonempty : Set.Nonempty {y : Fin n ⊕ κ → ℝ | M *ᵥ y ≤ rhs} := by
    refine ⟨Sum.elim x₀ z₀, ?_⟩
    -- The lifted facet point is feasible for the stacked pure-inequality encoding.
    simpa [M, rhs] using
      (mem_stackedLinearExtendedSystem_iff Aeq Beq beq Aineq Bineq bineq x₀ z₀).2 hz₀
  have hvalid_stacked :
      ∀ ⦃y : Fin n ⊕ κ → ℝ⦄, y ∈ {y : Fin n ⊕ κ → ℝ | M *ᵥ y ≤ rhs} → c ⬝ᵥ y ≤ b i := by
    intro y hy
    have hyEF :
        ((fun j ↦ y (Sum.inl j)), fun k ↦ y (Sum.inr k)) ∈
          linear_extended_system Aeq Beq beq Aineq Bineq bineq := by
      have hySplit :
          Sum.elim (fun j ↦ y (Sum.inl j)) (fun k ↦ y (Sum.inr k)) = y := by
        funext s
        rcases s with j | k <;> rfl
      exact
        (mem_stackedLinearExtendedSystem_iff Aeq Beq beq Aineq Bineq bineq
          (fun j ↦ y (Sum.inl j)) (fun k ↦ y (Sum.inr k))).1 <| by
            simpa [M, rhs, hySplit] using hy
    have hyP : (fun j ↦ y (Sum.inl j)) ∈ P := by
      rw [hEF]
      exact ⟨((fun j ↦ y (Sum.inl j)), fun k ↦ y (Sum.inr k)), hyEF, rfl⟩
    have hyFacet := hvalidFacet hyP
    simpa [c, dotProduct, Finset.sum_sumElim] using hyFacet
  obtain ⟨w, hw_nonneg, hw_row, hw_rhs⟩ :=
    (valid_inequality_iff_exists_nonneg_row_multiplier_raw M rhs c (b i) hstack_nonempty).mp
      hvalid_stacked
  obtain ⟨u, v, hu_nonneg, huA, huB, hu_rhs_le⟩ :=
    existsMixedRowMultiplierOfStackedMultiplier
      Aeq Beq beq Aineq Bineq bineq (A i) 0 (b i) w hw_nonneg hw_row hw_rhs
  have hz₀_eq := (mem_linear_extended_system_iff.mp hz₀).1
  have hz₀_le := (mem_linear_extended_system_iff.mp hz₀).2
  have hu_rhs_ge : b i ≤ u ⬝ᵥ bineq + v ⬝ᵥ beq := by
    -- Route correction: exactness is recovered by evaluating the mixed certificate at the lifted
    -- point where the facet inequality is tight.
    have hu_eval :
        u ⬝ᵥ (Aineq *ᵥ x₀ + Bineq *ᵥ z₀) =
          (u ᵥ* Aineq) ⬝ᵥ x₀ + (u ᵥ* Bineq) ⬝ᵥ z₀ := by
      rw [dotProduct_add, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
    have hv_eval :
        v ⬝ᵥ (Aeq *ᵥ x₀ + Beq *ᵥ z₀) =
          (v ᵥ* Aeq) ⬝ᵥ x₀ + (v ᵥ* Beq) ⬝ᵥ z₀ := by
      rw [dotProduct_add, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
    have hA_split :
        (u ᵥ* Aineq + v ᵥ* Aeq) ⬝ᵥ x₀ =
          (u ᵥ* Aineq) ⬝ᵥ x₀ + (v ᵥ* Aeq) ⬝ᵥ x₀ := by
      rw [add_dotProduct]
    have hB_split :
        (u ᵥ* Bineq + v ᵥ* Beq) ⬝ᵥ z₀ =
          (u ᵥ* Bineq) ⬝ᵥ z₀ + (v ᵥ* Beq) ⬝ᵥ z₀ := by
      rw [add_dotProduct]
    calc
      b i = (A i) ⬝ᵥ x₀ := hx₀_eq.symm
      _ = ((u ᵥ* Aineq + v ᵥ* Aeq) ⬝ᵥ x₀) + ((u ᵥ* Bineq + v ᵥ* Beq) ⬝ᵥ z₀) := by
            rw [huA, huB]
            simp
      _ = ((u ᵥ* Aineq) ⬝ᵥ x₀ + (v ᵥ* Aeq) ⬝ᵥ x₀) +
            ((u ᵥ* Bineq) ⬝ᵥ z₀ + (v ᵥ* Beq) ⬝ᵥ z₀) := by
            rw [hA_split, hB_split]
      _ = u ⬝ᵥ (Aineq *ᵥ x₀ + Bineq *ᵥ z₀) + v ⬝ᵥ (Aeq *ᵥ x₀ + Beq *ᵥ z₀) := by
            rw [hu_eval, hv_eval]
            ring
      _ ≤ u ⬝ᵥ bineq + v ⬝ᵥ beq := by
            gcongr
            exact dotProduct_le_dotProduct_of_nonneg_left hz₀_le hu_nonneg
            rw [hz₀_eq]
      _ = u ⬝ᵥ bineq + v ⬝ᵥ beq := rfl
  refine ⟨u, v, hu_nonneg, huA, huB, le_antisymm hu_rhs_le hu_rhs_ge⟩
/-
  classical
  let M :
      Matrix ((σ ⊕ ρ) ⊕ ρ) (Fin n ⊕ κ) ℝ :=
    Matrix.fromRows
      (Matrix.fromRows (Matrix.fromCols Aineq Bineq) (Matrix.fromCols Aeq Beq))
      (-Matrix.fromCols Aeq Beq)
  let rhs : ((σ ⊕ ρ) ⊕ ρ) → ℝ := Sum.elim (Sum.elim bineq beq) (-beq)
  let c : Fin n ⊕ κ → ℝ := Sum.elim (A i) 0
  have hvalidFacet : is_valid_inequality P (A i) (b i) :=
    maximalProperFaceInequality_valid (hfacets i)
  have hface_nonempty : (face_set P (A i) (b i)).Nonempty := by
    have hproper :
        is_proper_face P (face_set P (A i) (b i)) := by
      exact maximalProperFace_to_isProperFace (maximalProperFaceInequality_isFacet (hfacets i))
    exact (is_proper_face_iff.mp hproper).2.1
  rcases hface_nonempty with ⟨x₀, hx₀_face⟩
  have hx₀P : x₀ ∈ P := (mem_face_set_iff.mp hx₀_face).1
  have hx₀_eq : A i ⬝ᵥ x₀ = b i := (mem_face_set_iff.mp hx₀_face).2
  rw [hEF] at hx₀P
  rcases hx₀P with ⟨⟨xLift, z₀⟩, hz₀, hxLift⟩
  have hxLift_eq : xLift = x₀ := by simpa using hxLift
  subst xLift
  have hstack_nonempty : Set.Nonempty {y : Fin n ⊕ κ → ℝ | M *ᵥ y ≤ rhs} := by
    refine ⟨Sum.elim x₀ z₀, ?_⟩
    -- The lifted facet point is feasible for the stacked pure-inequality encoding.
    simpa [M, rhs] using
      (mem_stackedLinearExtendedSystem_iff Aeq Beq beq Aineq Bineq bineq x₀ z₀).2 hz₀
  have hvalid_stacked :
      ∀ ⦃y : Fin n ⊕ κ → ℝ⦄, y ∈ {y : Fin n ⊕ κ → ℝ | M *ᵥ y ≤ rhs} → c ⬝ᵥ y ≤ b i := by
    intro y hy
    have hyEF :
        ((fun j ↦ y (Sum.inl j)), fun k ↦ y (Sum.inr k)) ∈
          linear_extended_system Aeq Beq beq Aineq Bineq bineq := by
      have hySplit :
          Sum.elim (fun j ↦ y (Sum.inl j)) (fun k ↦ y (Sum.inr k)) = y := by
        funext s
        rcases s with j | k <;> rfl
      exact
        (mem_stackedLinearExtendedSystem_iff Aeq Beq beq Aineq Bineq bineq
          (fun j ↦ y (Sum.inl j)) (fun k ↦ y (Sum.inr k))).1 <| by
            simpa [M, rhs, hySplit] using hy
    have hyP : (fun j ↦ y (Sum.inl j)) ∈ P := by
      rw [hEF]
      exact ⟨((fun j ↦ y (Sum.inl j)), fun k ↦ y (Sum.inr k)), hyEF, rfl⟩
    have hyFacet := hvalidFacet hyP
    simpa [c, dotProduct, Finset.sum_sumElim] using hyFacet
  obtain ⟨w, hw_nonneg, hw_row, hw_rhs⟩ :=
    (valid_inequality_iff_exists_nonneg_row_multiplier_raw M rhs c (b i) hstack_nonempty).mp
      hvalid_stacked
  obtain ⟨u, v, hu_nonneg, huA, huB, hu_rhs_le⟩ :=
    existsMixedRowMultiplierOfStackedMultiplier
      Aeq Beq beq Aineq Bineq bineq (A i) 0 (b i) w hw_nonneg hw_row hw_rhs
  have hz₀_eq := (mem_linear_extended_system_iff.mp hz₀).1
  have hz₀_le := (mem_linear_extended_system_iff.mp hz₀).2
  have hu_rhs_ge : b i ≤ u ⬝ᵥ bineq + v ⬝ᵥ beq := by
    -- Route correction: exactness is recovered by evaluating the mixed certificate at the lifted
    -- point where the facet inequality is tight.
    calc
      b i = (A i) ⬝ᵥ x₀ := hx₀_eq.symm
      _ = ((u ᵥ* Aineq + v ᵥ* Aeq) ⬝ᵥ x₀) + ((u ᵥ* Bineq + v ᵥ* Beq) ⬝ᵥ z₀) := by
            rw [huA, huB]
            simp
      _ = u ⬝ᵥ (Aineq *ᵥ x₀ + Bineq *ᵥ z₀) + v ⬝ᵥ (Aeq *ᵥ x₀ + Beq *ᵥ z₀) := by
            rw [add_dotProduct, add_dotProduct, dotProduct_add]
            rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
              Matrix.dotProduct_mulVec]
            ring
      _ ≤ u ⬝ᵥ bineq + v ⬝ᵥ beq := by
            gcongr
            exact dotProduct_le_dotProduct_of_nonneg_left hz₀_le hu_nonneg
            rw [hz₀_eq]
      _ = u ⬝ᵥ bineq + v ⬝ᵥ beq := rfl
  refine ⟨u, v, hu_nonneg, huA, huB, le_antisymm hu_rhs_le hu_rhs_ge⟩
-/

/-- Auxiliary lower-bound clause for Theorem 4.51. Assume `P` is given both by the displayed
system `A x ≤ b` and by the convex hull of the displayed finite family `vertices`, and assume the
rows of `A x ≤ b` are facet-defining inequalities for `P`. Let `S` be the associated nonnegative
slack matrix of this chosen presentation. Then every extended formulation of `P` has at least
`rank₊ S` total constraints. -/
theorem nonnegative_rank_le_extended_formulation_constraint_count
    {m n p : ℕ}
    {ρ : Type u} {σ : Type v} {κ : Type w}
    [Fintype ρ] [Fintype σ] [Fintype κ]
    (P : Set (Fin n → ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (vertices : Fin p → Fin n → ℝ)
    (Aeq : Matrix ρ (Fin n) ℝ)
    (Beq : Matrix ρ κ ℝ)
    (beq : ρ → ℝ)
    (Aineq : Matrix σ (Fin n) ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ)
    (hP_vertices : P = convexHull ℝ (Set.range vertices))
    (hP_system : P = polyhedron_le_set A b)
    (hfacets : ∀ i : Fin m, maximalProperFaceInequality P (A i) (b i))
    (hEF : P = Prod.fst '' linear_extended_system Aeq Beq beq Aineq Bineq bineq) :
    let hvertices := vertices_feasible_of_polytope_description P A b vertices hP_vertices hP_system
    let S : Matrix.Nonnegative (Fin m) (Fin p) ℝ :=
      ⟨slack_matrix A b vertices, slack_matrix_nonneg hvertices⟩
    rank₊ S ≤ Fintype.card ρ + Fintype.card σ := by
  classical
  let hvertices := vertices_feasible_of_polytope_description P A b vertices hP_vertices hP_system
  let S : Matrix.Nonnegative (Fin m) (Fin p) ℝ :=
    ⟨slack_matrix A b vertices, slack_matrix_nonneg hvertices⟩
  let eσ : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hvertex_lifts :
      ∀ j : Fin p, ∃ z : κ → ℝ,
        (vertices j, z) ∈ linear_extended_system Aeq Beq beq Aineq Bineq bineq := by
    intro j
    have hjP : vertices j ∈ P := by
      rw [hP_vertices]
      exact (subset_convexHull ℝ (Set.range vertices)) (Set.mem_range_self j)
    rw [hEF] at hjP
    rcases hjP with ⟨⟨x, z⟩, hxz, hx⟩
    have hx_eq : x = vertices j := by simpa using hx
    subst hx_eq
    exact ⟨z, hxz⟩
  choose zLift hzLift using hvertex_lifts
  have hmult :
      ∀ i : Fin m, ∃ u : σ → ℝ, ∃ v : ρ → ℝ,
        0 ≤ u ∧
          u ᵥ* Aineq + v ᵥ* Aeq = A i ∧
            u ᵥ* Bineq + v ᵥ* Beq = 0 ∧
              u ⬝ᵥ bineq + v ⬝ᵥ beq = b i := by
    intro i
    exact
      facetMultiplierExactOfExtendedFormulation
        P A b Aeq Beq beq Aineq Bineq bineq hfacets hEF i
  choose U V hU_nonneg hU_A hU_B hU_rhs using hmult
  let inequalitySlack : Matrix σ (Fin p) ℝ :=
    fun s j ↦ bineq s - (Aineq *ᵥ vertices j + Bineq *ᵥ zLift j) s
  have hInequalitySlack_nonneg : 0 ≤ inequalitySlack := by
    intro s j
    have hs := (mem_linear_extended_system_iff.mp (hzLift j)).2 s
    exact sub_nonneg.mpr hs
  let Fσ : Matrix (Fin m) (Fin (Fintype.card σ)) ℝ := fun i h ↦ U i (eσ.symm h)
  let Wσ : Matrix (Fin (Fintype.card σ)) (Fin p) ℝ := fun h j ↦ inequalitySlack (eσ.symm h) j
  have hFσ_nonneg : 0 ≤ Fσ := by
    intro i h
    exact hU_nonneg i (eσ.symm h)
  have hWσ_nonneg : 0 ≤ Wσ := by
    intro h j
    exact hInequalitySlack_nonneg (eσ.symm h) j
  have hFactor :
      slack_matrix A b vertices = Fσ * Wσ := by
    ext i j
    have hVeq :
        V i ⬝ᵥ beq =
          (V i ᵥ* Aeq) ⬝ᵥ vertices j + (V i ᵥ* Beq) ⬝ᵥ zLift j := by
      calc
        V i ⬝ᵥ beq = V i ⬝ᵥ (Aeq *ᵥ vertices j + Beq *ᵥ zLift j) := by
          rw [(mem_linear_extended_system_iff.mp (hzLift j)).1]
        _ = (V i ᵥ* Aeq) ⬝ᵥ vertices j + (V i ᵥ* Beq) ⬝ᵥ zLift j := by
          rw [dotProduct_add, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
    have hSlack_eval :
        U i ⬝ᵥ (fun s ↦ inequalitySlack s j) = slack_matrix A b vertices i j := by
      have hslack_fun :
          (fun s ↦ inequalitySlack s j) =
            bineq - fun s ↦ (Aineq *ᵥ vertices j + Bineq *ᵥ zLift j) s := by
        funext s
        simp [inequalitySlack]
      have hA_split :
          (U i ᵥ* Aineq + V i ᵥ* Aeq) ⬝ᵥ vertices j =
            (U i ᵥ* Aineq) ⬝ᵥ vertices j + (V i ᵥ* Aeq) ⬝ᵥ vertices j := by
        rw [add_dotProduct]
      have hB_split :
          (U i ᵥ* Bineq + V i ᵥ* Beq) ⬝ᵥ zLift j =
            (U i ᵥ* Bineq) ⬝ᵥ zLift j + (V i ᵥ* Beq) ⬝ᵥ zLift j := by
        rw [add_dotProduct]
      calc
        U i ⬝ᵥ (fun s ↦ inequalitySlack s j)
            = U i ⬝ᵥ bineq - U i ⬝ᵥ (fun s ↦ (Aineq *ᵥ vertices j + Bineq *ᵥ zLift j) s) := by
                rw [hslack_fun, dotProduct_sub]
        _ = U i ⬝ᵥ bineq - (U i ᵥ* Aineq) ⬝ᵥ vertices j - (U i ᵥ* Bineq) ⬝ᵥ zLift j := by
              rw [dotProduct_add, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
              ring
        _ = U i ⬝ᵥ bineq + V i ⬝ᵥ beq -
              ((U i ᵥ* Aineq + V i ᵥ* Aeq) ⬝ᵥ vertices j) -
              ((U i ᵥ* Bineq + V i ᵥ* Beq) ⬝ᵥ zLift j) := by
              rw [hVeq, hA_split, hB_split]
              ring
        _ = b i - (A i) ⬝ᵥ vertices j := by
              rw [hU_rhs i, hU_A i, hU_B i]
              simp
        _ = slack_matrix A b vertices i j := by
              rfl
    calc
      slack_matrix A b vertices i j = U i ⬝ᵥ (fun s ↦ inequalitySlack s j) := hSlack_eval.symm
      _ = ∑ h : Fin (Fintype.card σ), Fσ i h * Wσ h j := by
            change ∑ s : σ, U i s * inequalitySlack s j =
                ∑ h : Fin (Fintype.card σ), Fσ i h * Wσ h j
            simpa [dotProduct, Fσ, Wσ] using
              (Fintype.sum_equiv eσ
                (fun s : σ ↦ U i s * inequalitySlack s j)
                (fun h : Fin (Fintype.card σ) ↦ Fσ i h * Wσ h j)
                (fun s ↦ by simp [Fσ, Wσ]))
      _ = (Fσ * Wσ) i j := by rw [Matrix.mul_apply]
  have hfact :
      has_nonnegative_rank_factorization (S : Matrix (Fin m) (Fin p) ℝ) (Fintype.card σ) := by
    refine (has_nonnegative_rank_factorization_iff).2 ⟨Fσ, Wσ, hFσ_nonneg, hWσ_nonneg, ?_⟩
    exact hFactor
  have hstrong : rank₊ S ≤ Fintype.card σ :=
    nonnegative_rank_le_of_has_nonnegative_rank_factorization hfact
  have hσ_le : Fintype.card σ ≤ Fintype.card ρ + Fintype.card σ := by
    omega
  exact hstrong.trans hσ_le
/-
  classical
  let hvertices := vertices_feasible_of_polytope_description P A b vertices hP_vertices hP_system
  let S : Matrix.Nonnegative (Fin m) (Fin p) ℝ :=
    ⟨slack_matrix A b vertices, slack_matrix_nonneg hvertices⟩
  let eσ : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hvertex_lifts :
      ∀ j : Fin p, ∃ z : κ → ℝ, (vertices j, z) ∈ linear_extended_system Aeq Beq beq Aineq Bineq bineq := by
    intro j
    have hjP : vertices j ∈ P := by
      rw [hP_vertices]
      exact (subset_convexHull ℝ (Set.range vertices)) (Set.mem_range_self j)
    rw [hEF] at hjP
    rcases hjP with ⟨⟨x, z⟩, hxz, hx⟩
    have hx_eq : x = vertices j := by simpa using hx
    subst hx_eq
    exact ⟨z, hxz⟩
  choose zLift hzLift using hvertex_lifts
  have hmult :
      ∀ i : Fin m, ∃ u : σ → ℝ, ∃ v : ρ → ℝ,
        0 ≤ u ∧
          u ᵥ* Aineq + v ᵥ* Aeq = A i ∧
            u ᵥ* Bineq + v ᵥ* Beq = 0 ∧
              u ⬝ᵥ bineq + v ⬝ᵥ beq = b i := by
    intro i
    exact
      facetMultiplierExactOfExtendedFormulation
        P A b Aeq Beq beq Aineq Bineq bineq hfacets hEF i
  choose U V hU_nonneg hU_A hU_B hU_rhs using hmult
  let inequalitySlack : Matrix σ (Fin p) ℝ :=
    fun s j ↦ bineq s - (Aineq *ᵥ vertices j + Bineq *ᵥ zLift j) s
  have hInequalitySlack_nonneg : 0 ≤ inequalitySlack := by
    intro s j
    have hs := (mem_linear_extended_system_iff.mp (hzLift j)).2 s
    exact sub_nonneg.mpr hs
  let Fσ : Matrix (Fin m) (Fin (Fintype.card σ)) ℝ := fun i h ↦ U i (eσ.symm h)
  let Wσ : Matrix (Fin (Fintype.card σ)) (Fin p) ℝ := fun h j ↦ inequalitySlack (eσ.symm h) j
  have hFσ_nonneg : 0 ≤ Fσ := by
    intro i h
    exact hU_nonneg i (eσ.symm h)
  have hWσ_nonneg : 0 ≤ Wσ := by
    intro h j
    exact hInequalitySlack_nonneg (eσ.symm h) j
  have hFactor :
      slack_matrix A b vertices = Fσ * Wσ := by
    ext i j
    have hVeq :
        V i ⬝ᵥ beq =
          (V i ᵥ* Aeq) ⬝ᵥ vertices j + (V i ᵥ* Beq) ⬝ᵥ zLift j := by
      calc
        V i ⬝ᵥ beq = V i ⬝ᵥ (Aeq *ᵥ vertices j + Beq *ᵥ zLift j) := by
          rw [(mem_linear_extended_system_iff.mp (hzLift j)).1]
        _ = (V i ᵥ* Aeq) ⬝ᵥ vertices j + (V i ᵥ* Beq) ⬝ᵥ zLift j := by
          rw [dotProduct_add, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  have hSlack_eval :
      U i ⬝ᵥ (fun s ↦ inequalitySlack s j) = slack_matrix A b vertices i j := by
      calc
        U i ⬝ᵥ (fun s ↦ inequalitySlack s j)
            = U i ⬝ᵥ bineq - U i ⬝ᵥ (fun s ↦ (Aineq *ᵥ vertices j + Bineq *ᵥ zLift j) s) := by
                simpa [inequalitySlack] using
                  dotProduct_sub (U i) bineq (fun s ↦ (Aineq *ᵥ vertices j + Bineq *ᵥ zLift j) s)
        _ = U i ⬝ᵥ bineq - (U i ᵥ* Aineq) ⬝ᵥ vertices j - (U i ᵥ* Bineq) ⬝ᵥ zLift j := by
              rw [dotProduct_add, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
              ring
        _ = U i ⬝ᵥ bineq + V i ⬝ᵥ beq -
              ((U i ᵥ* Aineq + V i ᵥ* Aeq) ⬝ᵥ vertices j) -
              ((U i ᵥ* Bineq + V i ᵥ* Beq) ⬝ᵥ zLift j) := by
              rw [hVeq]
              ring
        _ = b i - (A i) ⬝ᵥ vertices j := by
              rw [hU_rhs i, hU_A i, hU_B i]
              simp
        _ = slack_matrix A b vertices i j := by
              rfl
      calc
        slack_matrix A b vertices i j = U i ⬝ᵥ (fun s ↦ inequalitySlack s j) := hSlack_eval.symm
        _ = ∑ h : Fin (Fintype.card σ), Fσ i h * Wσ h j := by
              change ∑ s : σ, U i s * inequalitySlack s j =
                  ∑ h : Fin (Fintype.card σ), Fσ i h * Wσ h j
              simpa [dotProduct, Fσ, Wσ] using
                (Fintype.sum_equiv eσ
                  (fun s : σ ↦ U i s * inequalitySlack s j)
                  (fun h : Fin (Fintype.card σ) ↦ Fσ i h * Wσ h j)
                  (fun s ↦ by simp [Fσ, Wσ]))
        _ = (Fσ * Wσ) i j := by rw [Matrix.mul_apply]
  have hfact :
      has_nonnegative_rank_factorization (S : Matrix (Fin m) (Fin p) ℝ) (Fintype.card σ) := by
    refine (has_nonnegative_rank_factorization_iff).2 ⟨Fσ, Wσ, hFσ_nonneg, hWσ_nonneg, ?_⟩
    exact hFactor
  have hstrong : rank₊ S ≤ Fintype.card σ :=
    nonnegative_rank_le_of_has_nonnegative_rank_factorization hfact
  have hσ_le : Fintype.card σ ≤ Fintype.card ρ + Fintype.card σ := by
    omega
  exact hstrong.trans hσ_le
-/

/-- Helper for Theorem 4.51: a slack factorization `slack_matrix A b vertices = F * W` yields the
standard raw Yannakakis lift whose `x`-projection is exactly `P`. -/
lemma rawYannakakisLiftProjection_eq
    {m n p nr : ℕ}
    (P : Set (Fin n → ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (vertices : Fin p → Fin n → ℝ)
    (F : Matrix (Fin m) (Fin nr) ℝ)
    (W : Matrix (Fin nr) (Fin p) ℝ)
    (hF : 0 ≤ F)
    (hW : 0 ≤ W)
    (hFW : slack_matrix A b vertices = F * W)
    (hP_vertices : P = convexHull ℝ (Set.range vertices))
    (hP_system : P = polyhedron_le_set A b) :
    P = Prod.fst '' linear_extended_system A F b
      (0 : Matrix (Fin nr) (Fin n) ℝ) (-1) 0 := by
  let Q :=
    Prod.fst '' linear_extended_system A F b
      (0 : Matrix (Fin nr) (Fin n) ℝ) (-1) 0
  have hQ_convex : Convex ℝ Q := by
    intro x hx y hy a b' ha hb hab
    rcases hx with ⟨⟨x, z₁⟩, hxz, rfl⟩
    rcases hy with ⟨⟨y, z₂⟩, hyz, rfl⟩
    refine ⟨(a • x + b' • y, a • z₁ + b' • z₂), ?_, rfl⟩
    rw [mem_linear_extended_system_iff] at hxz hyz ⊢
    constructor
    · ext i
      have hxEq : (A *ᵥ x) i + (F *ᵥ z₁) i = b i := by
        simpa [Pi.add_apply] using congrFun hxz.1 i
      have hyEq : (A *ᵥ y) i + (F *ᵥ z₂) i = b i := by
        simpa [Pi.add_apply] using congrFun hyz.1 i
      calc
        (A *ᵥ (a • x + b' • y) + F *ᵥ (a • z₁ + b' • z₂)) i
            = a * ((A *ᵥ x) i + (F *ᵥ z₁) i) + b' * ((A *ᵥ y) i + (F *ᵥ z₂) i) := by
                simp [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, mul_add]
                ring
        _ = a * b i + b' * b i := by rw [hxEq, hyEq]
        _ = b i := by
              calc
                a * b i + b' * b i = (a + b') * b i := by ring
                _ = b i := by rw [hab, one_mul]
    · intro h
      have hz₁_nonneg : 0 ≤ z₁ h := by
        have hh := hxz.2 h
        have hh' : -(z₁ h) ≤ 0 := by
          simpa [Matrix.neg_mulVec] using hh
        linarith
      have hz₂_nonneg : 0 ≤ z₂ h := by
        have hh := hyz.2 h
        have hh' : -(z₂ h) ≤ 0 := by
          simpa [Matrix.neg_mulVec] using hh
        linarith
      have hz_nonneg : 0 ≤ a * z₁ h + b' * z₂ h :=
        add_nonneg (mul_nonneg ha hz₁_nonneg) (mul_nonneg hb hz₂_nonneg)
      simpa [Matrix.neg_mulVec] using neg_nonpos.mpr hz_nonneg
  have hvertices_subset : Set.range vertices ⊆ Q := by
    intro x hx
    rcases hx with ⟨j, rfl⟩
    let z : Fin nr → ℝ := fun h ↦ W h j
    refine ⟨(vertices j, z), ?_, rfl⟩
    rw [mem_linear_extended_system_iff]
    constructor
    · ext i
      have hij : slack_matrix A b vertices i j = (F * W) i j := by
        simpa [hFW] using congrFun (congrFun hFW i) j
      have hmul : (F *ᵥ z) i = (F * W) i j := by
        simpa [z, Matrix.mulVec, dotProduct, Matrix.mul_apply]
      calc
        (A *ᵥ vertices j + F *ᵥ z) i = (A *ᵥ vertices j) i + (F * W) i j := by
              rw [Pi.add_apply, hmul]
        _ = b i := by
              rw [← hij, slack_matrix_apply]
              ring
    · intro h
      simpa [z, Matrix.neg_mulVec] using neg_nonpos.mpr (hW h j)
  have hP_subset : P ⊆ Q := by
    rw [hP_vertices]
    exact convexHull_min hvertices_subset hQ_convex
  ext x
  constructor
  · intro hxP
    exact hP_subset hxP
  · rintro ⟨⟨x, z⟩, hxz, rfl⟩
    rcases (mem_linear_extended_system_iff.mp hxz) with ⟨hxEq, hzLe⟩
    rw [hP_system, mem_polyhedron_le_set_iff]
    intro i
    have hz_nonneg : ∀ h : Fin nr, 0 ≤ z h := by
      intro h
      have hh := hzLe h
      have hh' : -(z h) ≤ 0 := by
        simpa [Matrix.neg_mulVec] using hh
      linarith
    have hFz_nonneg : 0 ≤ (F *ᵥ z) i := by
      simpa [Matrix.mulVec, dotProduct] using
        Finset.sum_nonneg (fun h _ ↦ mul_nonneg (hF i h) (hz_nonneg h))
    have hiEq : (A *ᵥ x) i + (F *ᵥ z) i = b i := by
      simpa [Pi.add_apply] using congrFun hxEq i
    have hAx_le : (A *ᵥ x) i ≤ b i := by
      nlinarith [hiEq, hFz_nonneg]
    exact hAx_le
/-
  let Q :=
    Prod.fst '' linear_extended_system A F b
      (0 : Matrix (Fin nr) (Fin n) ℝ) (-1) 0
  have hQ_convex : Convex ℝ Q := by
    intro x hx y hy a b' ha hb hab
    rcases hx with ⟨⟨x, z₁⟩, hxz, rfl⟩
    rcases hy with ⟨⟨y, z₂⟩, hyz, rfl⟩
    refine ⟨(a • x + b' • y, a • z₁ + b' • z₂), ?_, rfl⟩
    rw [mem_linear_extended_system_iff] at hxz hyz ⊢
    constructor
    · ext i
      have hxEq := congrFun hxz.1 i
      have hyEq := congrFun hyz.1 i
      calc
        (A *ᵥ (a • x + b' • y) + F *ᵥ (a • z₁ + b' • z₂)) i
            = a * ((A *ᵥ x) i + (F *ᵥ z₁) i) + b' * ((A *ᵥ y) i + (F *ᵥ z₂) i) := by
                simp [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, mul_add, add_mul]
        _ = a * b i + b' * b i := by rw [hxEq, hyEq]
        _ = b i := by linarith
    · intro h
      have hz₁_nonneg : 0 ≤ z₁ h := by
        have hh := hxz.2 h
        have hh' : -(z₁ h) ≤ 0 := by
          simpa [Matrix.neg_mulVec] using hh
        linarith
      have hz₂_nonneg : 0 ≤ z₂ h := by
        have hh := hyz.2 h
        have hh' : -(z₂ h) ≤ 0 := by
          simpa [Matrix.neg_mulVec] using hh
        linarith
      have hz_nonneg : 0 ≤ a * z₁ h + b' * z₂ h :=
        add_nonneg (mul_nonneg ha hz₁_nonneg) (mul_nonneg hb hz₂_nonneg)
      simpa [Matrix.neg_mulVec] using neg_nonpos.mpr hz_nonneg
  have hvertices_subset : Set.range vertices ⊆ Q := by
    intro x hx
    rcases hx with ⟨j, rfl⟩
    let z : Fin nr → ℝ := fun h ↦ W h j
    refine ⟨(vertices j, z), ?_, rfl⟩
    rw [mem_linear_extended_system_iff]
    constructor
    · ext i
      have hij : slack_matrix A b vertices i j = (F * W) i j := by
        simpa [hFW] using congrFun (congrFun hFW i) j
      have hmul : (F *ᵥ z) i = (F * W) i j := by
        simpa [z, Matrix.mulVec, dotProduct, Matrix.mul_apply]
      calc
        (A *ᵥ vertices j + F *ᵥ z) i = (A *ᵥ vertices j) i + (F * W) i j := by
              rw [Pi.add_apply, hmul]
        _ = b i := by
              rw [← hij, slack_matrix_apply]
              ring
    · intro h
      simpa [z, Matrix.neg_mulVec] using neg_nonpos.mpr (hW h j)
  have hP_subset : P ⊆ Q := by
    rw [hP_vertices]
    exact convexHull_min hvertices_subset hQ_convex
  ext x
  constructor
  · intro hxP
    exact hP_subset hxP
  · rintro ⟨⟨x, z⟩, hxz, rfl⟩
    rcases (mem_linear_extended_system_iff.mp hxz) with ⟨hxEq, hzLe⟩
    rw [hP_system, mem_polyhedron_le_set_iff]
    intro i
    have hz_nonneg : ∀ h : Fin nr, 0 ≤ z h := by
      intro h
      have hh := hzLe h
      have hh' : -(z h) ≤ 0 := by
        simpa [Matrix.neg_mulVec] using hh
      linarith
    have hFz_nonneg : 0 ≤ (F *ᵥ z) i := by
      simpa [Matrix.mulVec, dotProduct] using
        Finset.sum_nonneg (fun h _ ↦ mul_nonneg (hF i h) (hz_nonneg h))
    have hiEq := congrFun hxEq i
    have hAx_le : (A *ᵥ x) i ≤ b i := by
      linarith
    exact (not_lt_of_ge hAx_le) a✝
-/

/-- Helper for Theorem 4.51: every row-span vector annihilates a vector already annihilated by all
rows of `M`. -/
lemma dotProduct_eq_zero_of_mem_rowSpan
    {μ ν : Type*}
    [Fintype μ] [Fintype ν]
    (M : Matrix μ ν ℝ)
    {y : ν → ℝ}
    (hy : M *ᵥ y = 0) :
    ∀ v ∈ Submodule.span ℝ (Set.range M.row), v ⬝ᵥ y = 0 := by
  intro v hv
  -- Extend the vanishing dot-product relation from the matrix rows to their span.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · intro w hw
    rcases hw with ⟨i, rfl⟩
    simpa [Matrix.mulVec, dotProduct] using congrFun hy i
  · simp
  · intro u w hu hw hu_zero hw_zero
    rw [add_dotProduct, hu_zero, hw_zero]
    simp
  · intro a w hw hw_zero
    rw [smul_dotProduct, hw_zero]
    simp

/-- Helper for Theorem 4.51: if the row span of `N` lies in the row span of `M`, then every
kernel vector of `M.mulVecLin` is also a kernel vector of `N.mulVecLin`. -/
lemma mulVec_eq_zero_of_rowSpan_le
    {μ ρ ν : Type*}
    [Fintype μ] [Fintype ρ] [Fintype ν]
    (M : Matrix μ ν ℝ)
    (N : Matrix ρ ν ℝ)
    (hrows : Submodule.span ℝ (Set.range N.row) ≤ Submodule.span ℝ (Set.range M.row))
    {y : ν → ℝ}
    (hy : M *ᵥ y = 0) :
    N *ᵥ y = 0 := by
  ext i
  -- Each row of `N` lies in the row span of `M`, so it also annihilates `y`.
  have hi :
      N.row i ∈ Submodule.span ℝ (Set.range M.row) := by
    exact hrows (Submodule.subset_span (Set.mem_range_self i))
  simpa [Matrix.mulVec, dotProduct] using
    dotProduct_eq_zero_of_mem_rowSpan M hy (N.row i) hi

/-- Helper for Theorem 4.51: two affine equality systems with the same row span and the same base
point cut out the same solution set. -/
lemma equalitySolutionSet_eq_of_rowSpan_eq_and_feasiblePoint
    {μ ρ ν : Type*}
    [Fintype μ] [Fintype ρ] [Fintype ν]
    (M : Matrix μ ν ℝ)
    (d : μ → ℝ)
    (N : Matrix ρ ν ℝ)
    (e : ρ → ℝ)
    (y₀ : ν → ℝ)
    (hy₀M : M *ᵥ y₀ = d)
    (hy₀N : N *ᵥ y₀ = e)
    (hspan : Submodule.span ℝ (Set.range M.row) = Submodule.span ℝ (Set.range N.row)) :
    {y : ν → ℝ | M *ᵥ y = d} = {y : ν → ℝ | N *ᵥ y = e} := by
  ext y
  constructor
  · intro hy
    -- Translate to the homogeneous kernels and transport across the row-span equality.
    have hdiffM : M *ᵥ (y - y₀) = 0 := by
      rw [Matrix.mulVec_sub, hy, hy₀M, sub_self]
    have hdiffN : N *ᵥ (y - y₀) = 0 := by
      exact mulVec_eq_zero_of_rowSpan_le M N hspan.symm.le hdiffM
    have hsub : N *ᵥ y - N *ᵥ y₀ = 0 := by
      simpa [Matrix.mulVec_sub] using hdiffN
    calc
      N *ᵥ y = N *ᵥ y₀ := sub_eq_zero.mp hsub
      _ = e := hy₀N
  · intro hy
    -- The reverse direction uses the symmetric row-span transport.
    have hdiffN : N *ᵥ (y - y₀) = 0 := by
      rw [Matrix.mulVec_sub, hy, hy₀N, sub_self]
    have hdiffM : M *ᵥ (y - y₀) = 0 := by
      exact mulVec_eq_zero_of_rowSpan_le N M hspan.le hdiffN
    have hsub : M *ᵥ y - M *ᵥ y₀ = 0 := by
      simpa [Matrix.mulVec_sub] using hdiffM
    calc
      M *ᵥ y = M *ᵥ y₀ := sub_eq_zero.mp hsub
      _ = d := hy₀M

/-- Helper for Theorem 4.51: any affine equality system admits a row-basis presentation with at
most the ambient number of coordinates, and the retained rows are linearly independent. -/
lemma existsAffineEqualitySubsystem_le_ambient
    {μ ν : Type*}
    [Fintype μ] [Fintype ν]
    (M : Matrix μ ν ℝ)
    (d : μ → ℝ)
    (y₀ : ν → ℝ)
    (hy₀ : M *ᵥ y₀ = d) :
    ∃ r : ℕ,
      r ≤ Fintype.card ν ∧
        ∃ N : Matrix (Fin r) ν ℝ,
          ∃ e : Fin r → ℝ,
            LinearIndependent ℝ N.row ∧
              {y : ν → ℝ | M *ᵥ y = d} = {y : ν → ℝ | N *ᵥ y = e} := by
  let rowSpace : Submodule ℝ (ν → ℝ) := Submodule.span ℝ (Set.range M.row)
  let r : ℕ := Module.finrank ℝ rowSpace
  obtain ⟨rows, hrows_mem, hrows_span, hrows_linear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range M.row)
  let N : Matrix (Fin r) ν ℝ := fun i j ↦ rows i j
  let e : Fin r → ℝ := N *ᵥ y₀
  have hr_le : r ≤ Fintype.card ν := by
    -- The row space lives inside the ambient `ν → ℝ`, so its finrank is bounded by `|ν|`.
    calc
      r = Module.finrank ℝ rowSpace := rfl
      _ ≤ Module.finrank ℝ (ν → ℝ) := Submodule.finrank_le rowSpace
      _ = Fintype.card ν := Module.finrank_fintype_fun_eq_card ℝ
  have hspan :
      Submodule.span ℝ (Set.range M.row) = Submodule.span ℝ (Set.range N.row) := by
    -- The selected rows span exactly the original row space.
    simpa [rowSpace, r, N] using hrows_span.symm
  have hy₀N : N *ᵥ y₀ = e := by
    rfl
  have _hlinear : LinearIndependent ℝ N.row := by
    -- The basis rows are linearly independent, so the compressed system has no redundant rows.
    simpa [r, N] using hrows_linear
  refine ⟨r, hr_le, N, e, _hlinear, ?_⟩
  -- The same feasible base point transports equality of row spans to equality of affine systems.
  exact equalitySolutionSet_eq_of_rowSpan_eq_and_feasiblePoint M d N e y₀ hy₀ hy₀N hspan

/-- Helper for Theorem 4.51: a full-row-rank matrix contains an invertible square submatrix on
some choice of columns. -/
lemma fullRowRankColumnBasis
    {r : ℕ} {c : Type*} [Fintype c]
    (N : Matrix (Fin r) c ℝ)
    (hrows : LinearIndependent ℝ N.row) :
    ∃ J : Fin r ↪ c, IsUnit (N.submatrix id J) := by
  let colSpace : Submodule ℝ (Fin r → ℝ) := Submodule.span ℝ (Set.range N.col)
  have hrank : N.rank = r := by
    simpa using LinearIndependent.rank_matrix hrows
  have hcol_finrank : Module.finrank ℝ colSpace = r := by
    calc
      Module.finrank ℝ colSpace = N.rank := by
        simpa [colSpace] using (Matrix.rank_eq_finrank_span_cols (A := N)).symm
      _ = r := hrank
  obtain ⟨cols, hcols_mem, hcols_span, hcols_linear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range N.col)
  let e : Fin (Module.finrank ℝ colSpace) ≃ Fin r :=
    Fintype.equivOfCardEq (by simp [hcol_finrank])
  let picked : Fin r → c := fun i ↦ Classical.choose (hcols_mem (e.symm i))
  have hpicked_eq : ∀ i : Fin r, N.col (picked i) = cols (e.symm i) := by
    intro i
    exact Classical.choose_spec (hcols_mem (e.symm i))
  have hpicked_linear : LinearIndependent ℝ (fun i : Fin r ↦ N.col (picked i)) := by
    -- Reindex the selected spanning columns to `Fin r`, then rewrite them back to actual columns
    -- of `N`.
    have hcols_reindexed : LinearIndependent ℝ (fun i : Fin r ↦ cols (e.symm i)) := by
      exact (linearIndependent_equiv e.symm).2 hcols_linear
    have hEq :
        (fun i : Fin r ↦ N.col (picked i)) = fun i : Fin r ↦ cols (e.symm i) := by
      funext i
      exact hpicked_eq i
    exact hEq ▸ hcols_reindexed
  have hpicked_injective : Function.Injective picked := by
    intro i j hij
    apply hpicked_linear.injective
    simpa [hij]
  let J : Fin r ↪ c := ⟨picked, hpicked_injective⟩
  have hsub_cols : LinearIndependent ℝ (N.submatrix id J).col := by
    -- The chosen square submatrix has exactly the selected independent columns.
    simpa [J, Matrix.col, Matrix.submatrix_apply] using hpicked_linear
  exact ⟨J, (Matrix.linearIndependent_cols_iff_isUnit).1 hsub_cols⟩

/-- Helper for Theorem 4.51: an invertible left block solves the basic coordinates of a
partitioned linear system `B u + C w = e`. -/
lemma basicBlockMulVec_eq_iff
    {β γ : Type*}
    [Fintype β] [Fintype γ] [DecidableEq β]
    (B : Matrix β β ℝ)
    (C : Matrix β γ ℝ)
    (e : β → ℝ)
    (u : β → ℝ)
    (w : γ → ℝ)
    (hB : IsUnit B) :
    Matrix.fromCols B C *ᵥ Sum.elim u w = e ↔
      u = B⁻¹ *ᵥ (e - C *ᵥ w) := by
  constructor
  · intro hEq
    -- Move the free-coordinate contribution to the right-hand side before inverting `B`.
    have hBasic : B *ᵥ u = e - C *ᵥ w := by
      ext i
      have hi : (B *ᵥ u + C *ᵥ w) i = e i := by
        simpa [Matrix.fromCols_mulVec_sumElim] using congrFun hEq i
      have hi' := congrArg (fun t : ℝ => t - (C *ᵥ w) i) hi
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hi'
    letI : Invertible B := hB.invertible
    -- Apply the inverse of `B` to solve explicitly for the basic coordinates.
    have hmul :
        B⁻¹ *ᵥ (B *ᵥ u) = B⁻¹ *ᵥ (e - C *ᵥ w) := by
      simpa [hBasic]
    have hu : B⁻¹ *ᵥ (B *ᵥ u) = u := by
      calc
        B⁻¹ *ᵥ (B *ᵥ u) = (B⁻¹ * B) *ᵥ u := by
              simpa using (Matrix.mulVec_mulVec B⁻¹ B u).symm
        _ = u := by
              rw [Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
    simpa [hu] using hmul
  · intro hU
    -- Substitute the solved expression for `u` back into the block system.
    rw [Matrix.fromCols_mulVec_sumElim]
    calc
      B *ᵥ u + C *ᵥ w = B *ᵥ (B⁻¹ *ᵥ (e - C *ᵥ w)) + C *ᵥ w := by
            rw [hU]
      _ = e - C *ᵥ w + C *ᵥ w := by
            letI : Invertible B := hB.invertible
            calc
              B *ᵥ (B⁻¹ *ᵥ (e - C *ᵥ w)) + C *ᵥ w
                  = (B * B⁻¹) *ᵥ (e - C *ᵥ w) + C *ᵥ w := by
                      simp [Matrix.mulVec_mulVec]
              _ = e - C *ᵥ w + C *ᵥ w := by
                    rw [Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
      _ = e := by
            ext i
            simp
/-
  constructor
  · intro hEq
    -- Move the free-coordinate contribution to the right-hand side before inverting `B`.
    have hBasic : B *ᵥ u = e - C *ᵥ w := by
      ext i
      have hi : (B *ᵥ u + C *ᵥ w) i = e i := by
        simpa [Matrix.fromCols_mulVec_sumElim] using congrFun hEq i
      have hi' : (B *ᵥ u) i = (e - C *ᵥ w) i := by
        linarith
      exact hi'
    letI := hB.invertible
    -- Apply the inverse of `B` to recover the basic coordinates explicitly.
    have hmul :
        B⁻¹ *ᵥ (B *ᵥ u) = B⁻¹ *ᵥ (e - C *ᵥ w) := by
      simpa [hBasic]
    have hu : B⁻¹ *ᵥ (B *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
    simpa [hu] using hmul
  · intro hU
    -- Substitute the explicit basic-coordinate formula back into the block system.
    rw [Matrix.fromCols_mulVec_sumElim]
    calc
      B *ᵥ u + C *ᵥ w = B *ᵥ (B⁻¹ *ᵥ (e - C *ᵥ w)) + C *ᵥ w := by rw [hU]
      _ = e - C *ᵥ w + C *ᵥ w := by
        letI := hB.invertible
        change B *ᵥ (B⁻¹ *ᵥ (e - C *ᵥ w)) + C *ᵥ w = e - C *ᵥ w + C *ᵥ w
        rw [← Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
      _ = e := by
        ext i
        simp
-/

/-- Helper for Theorem 4.51: reorder the combined coordinate owner so that the chosen basis
columns appear first in their `Fin r` order, followed by the free visible and free auxiliary
coordinates. -/
lemma existsBasisOrderedColumnEquiv
    {n nr r : ℕ}
    (J : Fin r ↪ Fin n ⊕ Fin nr) :
    ∃ e :
        Fin n ⊕ Fin nr ≃
          Fin r ⊕
            ({j : Fin n // Sum.inl j ∉ Set.range J} ⊕
              {k : Fin nr // Sum.inr k ∉ Set.range J}),
      (∀ i : Fin r, e (J i) = Sum.inl i) ∧
        (∀ j : {j : Fin n // Sum.inl j ∉ Set.range J},
          e (Sum.inl j.1) = Sum.inr (Sum.inl j)) ∧
          (∀ k : {k : Fin nr // Sum.inr k ∉ Set.range J},
            e (Sum.inr k.1) = Sum.inr (Sum.inr k)) := by
  classical
  let freeEquiv :
      {c : Fin n ⊕ Fin nr // c ∉ Set.range J} ≃
        ({j : Fin n // Sum.inl j ∉ Set.range J} ⊕
          {k : Fin nr // Sum.inr k ∉ Set.range J}) :=
    { toFun := fun c =>
        match c with
        | ⟨Sum.inl j, hj⟩ => Sum.inl ⟨j, hj⟩
        | ⟨Sum.inr k, hk⟩ => Sum.inr ⟨k, hk⟩
      invFun := fun u =>
        match u with
        | Sum.inl j => ⟨Sum.inl j.1, j.2⟩
        | Sum.inr k => ⟨Sum.inr k.1, k.2⟩
      left_inv := by
        intro c
        cases c with
        | mk c hc =>
            cases c <;> rfl
      right_inv := by
        intro u
        cases u <;> rfl }
  let e :
      Fin n ⊕ Fin nr ≃
        Fin r ⊕
          ({j : Fin n // Sum.inl j ∉ Set.range J} ⊕
            {k : Fin nr // Sum.inr k ∉ Set.range J}) :=
    (Equiv.sumCompl fun c : Fin n ⊕ Fin nr ↦ c ∈ Set.range J).symm.trans
      (Equiv.sumCongr J.toEquivRange.symm freeEquiv)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i
    -- The chosen basis column `J i` lands in the leading `Fin r` block by construction.
    simp [e, freeEquiv]
  · intro j
    -- A visible coordinate outside the chosen basis lands in the free visible block.
    simp [e, freeEquiv, j.2]
  · intro k
    -- An auxiliary coordinate outside the chosen basis lands in the free auxiliary block.
    simp [e, freeEquiv, k.2]

/-- Helper for Theorem 4.51: after reordering the stacked coordinates by a basis-first column
equivalence, the split basic/free coordinate vector is exactly the original stacked vector
precomposed with the inverse ordering. -/
lemma basisOrderCoordinates_eq_split
    {n nr r : ℕ}
    (J : Fin r ↪ Fin n ⊕ Fin nr)
    (basisOrder :
      Fin n ⊕ Fin nr ≃
        Fin r ⊕
          ({j : Fin n // Sum.inl j ∉ Set.range J} ⊕
            {k : Fin nr // Sum.inr k ∉ Set.range J}))
    (hbasisOrder : ∀ i : Fin r, basisOrder (J i) = Sum.inl i)
    (hbasisOrderXFree :
      ∀ j : {j : Fin n // Sum.inl j ∉ Set.range J},
        basisOrder (Sum.inl j.1) = Sum.inr (Sum.inl j))
    (hbasisOrderZFree :
      ∀ k : {k : Fin nr // Sum.inr k ∉ Set.range J},
        basisOrder (Sum.inr k.1) = Sum.inr (Sum.inr k))
    (x : Fin n → ℝ)
    (z : Fin nr → ℝ) :
    Sum.elim
        (fun i : Fin r ↦ Sum.elim x z (J i))
        (Sum.elim
          (fun j : {j : Fin n // Sum.inl j ∉ Set.range J} ↦ x j.1)
          (fun k : {k : Fin nr // Sum.inr k ∉ Set.range J} ↦ z k.1)) =
      fun s ↦ Sum.elim x z (basisOrder.symm s) := by
  -- Evaluate the split coordinate vector on each branch of the basis-first sum type.
  ext s
  rcases s with i | s
  · simpa using
      congrArg (fun t : Fin n ⊕ Fin nr ↦ Sum.elim x z t)
        ((congrArg basisOrder.symm (hbasisOrder i)).symm).symm
  · rcases s with j | k
    · simpa using
        congrArg (fun t : Fin n ⊕ Fin nr ↦ Sum.elim x z t)
          ((congrArg basisOrder.symm (hbasisOrderXFree j)).symm).symm
    · simpa using
        congrArg (fun t : Fin n ⊕ Fin nr ↦ Sum.elim x z t)
          ((congrArg basisOrder.symm (hbasisOrderZFree k)).symm).symm

/-- Helper for Theorem 4.51: extending a matrix indexed by a subtype by zero outside that subtype
does not change its action on ambient vectors. -/
lemma subtypeLift_mulVec
    {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    (p : β → Prop)
    [DecidablePred p]
    (D : Matrix α {b : β // p b} ℝ)
    (x : β → ℝ) :
    (fun i j ↦ if h : p j then D i ⟨j, h⟩ else 0 : Matrix α β ℝ) *ᵥ x =
      D *ᵥ (fun j : {b : β // p b} ↦ x j.1) := by
  -- Rewrite the subtype-indexed sum over the ambient owner with an indicator function.
  classical
  ext i
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  calc
    ∑ j, (if h : p j then D i ⟨j, h⟩ else 0) * x j
        = Finset.sum (Finset.univ.filter p)
            (fun j ↦ (if h : p j then D i ⟨j, h⟩ else 0) * x j) := by
              symm
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hp : p j <;> simp [hp]
    _ = ∑ j : {b : β // p b}, (if h : p j.1 then D i ⟨j.1, h⟩ else 0) * x j.1 := by
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := Finset.univ)
              (p := p)
              (f := fun j : β ↦ (if h : p j then D i ⟨j, h⟩ else 0) * x j)).symm
    _ = ∑ j : {b : β // p b}, D i j * x j.1 := by
          have hsubfun :
              (fun j : {b : β // p b} ↦
                (if h : p j.1 then D i ⟨j.1, h⟩ else 0) * x j.1) =
                fun j : {b : β // p b} ↦ D i j * x j.1 := by
            funext j
            have hj : p j.1 := j.2
            simp [hj]
          rw [hsubfun]

/-- Helper for Theorem 4.51: the basis indices that point to visible coordinates inject into the
visible coordinate owner, so there are at most `n` such indices. -/
lemma basicVisibleIndexCard_le
    {n nr r : ℕ}
    (J : Fin r ↪ Fin n ⊕ Fin nr) :
    Fintype.card {i : Fin r // ∃ j : Fin n, J i = Sum.inl j} ≤ n := by
  classical
  -- Send a visible basis index to the unique visible coordinate it selects.
  let visibleCoord : {i : Fin r // ∃ j : Fin n, J i = Sum.inl j} → Fin n :=
    fun i => Classical.choose i.2
  have hvisibleCoord_injective : Function.Injective visibleCoord := by
    intro i₁ i₂ hij
    apply Subtype.ext
    apply J.injective
    calc
      J i₁.1 = Sum.inl (visibleCoord i₁) := by
            exact Classical.choose_spec i₁.2
      _ = Sum.inl (visibleCoord i₂) := by
            rw [hij]
      _ = J i₂.1 := by
            exact (Classical.choose_spec i₂.2).symm
  simpa [visibleCoord] using Fintype.card_le_of_injective visibleCoord hvisibleCoord_injective
/-
  classical
  simpa using Fintype.card_le_of_injective
    (fun i : {i : Fin r // ∃ j : Fin n, J i = Sum.inl j} => Classical.choose i.2) ?_
  intro i₁ i₂ hij
  apply Subtype.ext
  apply J.injective
  simpa [Classical.choose_spec i₁.2, Classical.choose_spec i₂.2, hij]
-/

/-- Helper for Theorem 4.51: the auxiliary coordinates split into chosen basis coordinates and free
coordinates, so their combined cardinality is exactly `nr`. -/
lemma auxiliaryBasicAndFree_card_eq
    {n nr r : ℕ}
    (J : Fin r ↪ Fin n ⊕ Fin nr) :
    Fintype.card
        ({i : Fin r // ∃ k : Fin nr, J i = Sum.inr k} ⊕
          {k : Fin nr // Sum.inr k ∉ Set.range J}) = nr := by
  classical
  let auxBasic : Type :=
    {k : Fin nr // Sum.inr k ∈ Set.range J}
  let basicAuxEquiv :
      {i : Fin r // ∃ k : Fin nr, J i = Sum.inr k} ≃ auxBasic :=
    { toFun := fun i =>
        ⟨Classical.choose i.2, ⟨i.1, Classical.choose_spec i.2⟩⟩
      invFun := fun k =>
        ⟨Classical.choose k.2, ⟨k.1, Classical.choose_spec k.2⟩⟩
      left_inv := by
        intro i
        apply Subtype.ext
        have hk :
            Sum.inr (Classical.choose i.2) ∈ Set.range J := ⟨i.1, Classical.choose_spec i.2⟩
        exact J.injective ((Classical.choose_spec hk).trans (Classical.choose_spec i.2).symm)
      right_inv := by
        intro k
        apply Subtype.ext
        have hk :
            ∃ t : Fin nr, J (Classical.choose k.2) = Sum.inr t := ⟨k.1, Classical.choose_spec k.2⟩
        exact Sum.inr.inj ((Classical.choose_spec hk).symm.trans (Classical.choose_spec k.2)) }
  let p : Fin nr → Prop := fun k => Sum.inr k ∈ Set.range J
  calc
    Fintype.card
        ({i : Fin r // ∃ k : Fin nr, J i = Sum.inr k} ⊕
          {k : Fin nr // Sum.inr k ∉ Set.range J})
        = Fintype.card {i : Fin r // ∃ k : Fin nr, J i = Sum.inr k} +
            Fintype.card {k : Fin nr // Sum.inr k ∉ Set.range J} := by
            rw [Fintype.card_sum]
    _ = Fintype.card auxBasic + Fintype.card {k : Fin nr // Sum.inr k ∉ Set.range J} := by
          rw [Fintype.card_congr basicAuxEquiv]
    _ = nr := by
          simpa [auxBasic, p, Fintype.card_sum] using
            (Fintype.card_congr (Equiv.sumCompl p))

/-- Helper for Theorem 4.51: reindexing rows and visible/auxiliary coordinates along finite
equivalences commutes with matrix-vector multiplication. -/
private theorem reindexedMulVecApply
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : Matrix α β ℝ)
    (eα : α ≃ γ)
    (eβ : β ≃ δ)
    (x : δ → ℝ) :
    Matrix.reindex eα eβ A *ᵥ x =
      fun i ↦ (A *ᵥ ((LinearEquiv.funCongrLeft ℝ ℝ eβ) x)) (eα.symm i) := by
  -- Evaluate the standard `mulVec` reindexing identity on the chosen vector.
  have hlin :=
    congrArg
      (fun T :
          (δ → ℝ) →ₗ[ℝ] γ → ℝ ↦
        T x)
      (Matrix.mulVecLin_reindex (R := ℝ) eα eβ A)
  simpa using hlin

/-- Helper for Theorem 4.51: the complement branch of `Equiv.sumCompl` evaluates to the
underlying carrier element. -/
private theorem sumCompl_applyInrVal
    {α : Type*} (p : α → Prop) [DecidablePred p] (x : {a : α // ¬ p a}) :
    (Equiv.sumCompl p) (Sum.inr x) = x.1 := by
  simpa using (Equiv.sumCompl_apply_inr (p := p) x)

/-- Helper for Theorem 4.51: reindexing the visible coordinates of a linear extended formulation
to `Fin` preserves the projected set, while simultaneously reindexing the equality rows,
inequality rows, and auxiliary coordinates. -/
private theorem reindexVisibleCoordinates_image_linear_extended_formulation
    {n : ℕ}
    {α : Type*} [Fintype α]
    (eα : α ≃ Fin n)
    {κ ρ σ : Type*}
    [Fintype κ] [Fintype ρ] [Fintype σ]
    (Aeq : Matrix ρ α ℝ)
    (Beq : Matrix ρ κ ℝ)
    (beq : ρ → ℝ)
    (Aineq : Matrix σ α ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ) :
    ((LinearEquiv.funCongrLeft ℝ ℝ eα).symm '' (
        Prod.fst '' linear_extended_system Aeq Beq beq Aineq Bineq bineq)) =
      Prod.fst ''
        linear_extended_system
          (Matrix.reindex (Fintype.equivFin ρ) eα Aeq)
          (Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq)
          (fun i ↦ beq ((Fintype.equivFin ρ).symm i))
          (Matrix.reindex (Fintype.equivFin σ) eα Aineq)
          (Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq)
          (fun i ↦ bineq ((Fintype.equivFin σ).symm i)) := by
  -- Transport witnesses through the visible-coordinate equivalence and the canonical `Fin`
  -- reindexings on the row and auxiliary owners.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_image_fst_iff] at hy
    rcases hy with ⟨z, hz⟩
    rcases (mem_linear_extended_system_iff.mp hz) with ⟨hzEq, hzLe⟩
    let zFin := (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)).symm z
    have hyTransport :
        (LinearEquiv.funCongrLeft ℝ ℝ eα)
            ((LinearEquiv.funCongrLeft ℝ ℝ eα).symm y) = y := by
      simpa using (LinearEquiv.funCongrLeft ℝ ℝ eα).apply_symm_apply y
    have hzTransport :
        (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)) zFin = z := by
      simpa [zFin] using
        (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)).apply_symm_apply z
    have hAeq :
        Matrix.reindex (Fintype.equivFin ρ) eα Aeq *ᵥ
            ((LinearEquiv.funCongrLeft ℝ ℝ eα).symm y) =
          fun i ↦ (Aeq *ᵥ y) ((Fintype.equivFin ρ).symm i) := by
      calc
        Matrix.reindex (Fintype.equivFin ρ) eα Aeq *ᵥ
            ((LinearEquiv.funCongrLeft ℝ ℝ eα).symm y) =
          fun i ↦
            (Aeq *ᵥ
              ((LinearEquiv.funCongrLeft ℝ ℝ eα)
                ((LinearEquiv.funCongrLeft ℝ ℝ eα).symm y)))
              ((Fintype.equivFin ρ).symm i) := by
            exact reindexedMulVecApply Aeq (Fintype.equivFin ρ) eα
              ((LinearEquiv.funCongrLeft ℝ ℝ eα).symm y)
        _ = fun i ↦ (Aeq *ᵥ y) ((Fintype.equivFin ρ).symm i) := by
            rw [hyTransport]
    have hBeq :
        Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq *ᵥ zFin =
          fun i ↦ (Beq *ᵥ z) ((Fintype.equivFin ρ).symm i) := by
      calc
        Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq *ᵥ zFin =
          fun i ↦
            (Beq *ᵥ
              ((LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)) zFin))
              ((Fintype.equivFin ρ).symm i) := by
            exact reindexedMulVecApply Beq (Fintype.equivFin ρ) (Fintype.equivFin κ) zFin
        _ = fun i ↦ (Beq *ᵥ z) ((Fintype.equivFin ρ).symm i) := by
            rw [hzTransport]
    have hAineq :
        Matrix.reindex (Fintype.equivFin σ) eα Aineq *ᵥ
            ((LinearEquiv.funCongrLeft ℝ ℝ eα).symm y) =
          fun i ↦ (Aineq *ᵥ y) ((Fintype.equivFin σ).symm i) := by
      calc
        Matrix.reindex (Fintype.equivFin σ) eα Aineq *ᵥ
            ((LinearEquiv.funCongrLeft ℝ ℝ eα).symm y) =
          fun i ↦
            (Aineq *ᵥ
              ((LinearEquiv.funCongrLeft ℝ ℝ eα)
                ((LinearEquiv.funCongrLeft ℝ ℝ eα).symm y)))
              ((Fintype.equivFin σ).symm i) := by
            exact reindexedMulVecApply Aineq (Fintype.equivFin σ) eα
              ((LinearEquiv.funCongrLeft ℝ ℝ eα).symm y)
        _ = fun i ↦ (Aineq *ᵥ y) ((Fintype.equivFin σ).symm i) := by
            rw [hyTransport]
    have hBineq :
        Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq *ᵥ zFin =
          fun i ↦ (Bineq *ᵥ z) ((Fintype.equivFin σ).symm i) := by
      calc
        Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq *ᵥ zFin =
          fun i ↦
            (Bineq *ᵥ
              ((LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)) zFin))
              ((Fintype.equivFin σ).symm i) := by
            exact reindexedMulVecApply Bineq (Fintype.equivFin σ) (Fintype.equivFin κ) zFin
        _ = fun i ↦ (Bineq *ᵥ z) ((Fintype.equivFin σ).symm i) := by
            rw [hzTransport]
    rw [mem_image_fst_iff]
    refine ⟨zFin, ?_⟩
    refine mem_linear_extended_system_iff.mpr ?_
    constructor
    · -- The equality block is just the original one, read at the matching `Fin` row.
      ext i
      simp only [Pi.add_apply, hAeq, hBeq]
      exact congrFun hzEq ((Fintype.equivFin ρ).symm i)
    · -- The inequality block transports pointwise in exactly the same way.
      intro i
      simp only [Pi.add_apply, hAineq, hBineq]
      exact hzLe ((Fintype.equivFin σ).symm i)
  · intro hx
    rw [mem_image_fst_iff] at hx
    rcases hx with ⟨zFin, hz⟩
    rcases (mem_linear_extended_system_iff.mp hz) with ⟨hzEq, hzLe⟩
    let y := (LinearEquiv.funCongrLeft ℝ ℝ eα) x
    let z := (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)) zFin
    have hyx :
        (LinearEquiv.funCongrLeft ℝ ℝ eα).symm y = x := by
      simpa [y] using
        (LinearEquiv.funCongrLeft ℝ ℝ eα).symm_apply_apply x
    have hAeq :
        ∀ i : ρ,
          (Aeq *ᵥ y) i =
            (Matrix.reindex (Fintype.equivFin ρ) eα Aeq *ᵥ x)
              ((Fintype.equivFin ρ) i) := by
      intro i
      have h :=
        congrFun
          (reindexedMulVecApply Aeq (Fintype.equivFin ρ) eα x)
          ((Fintype.equivFin ρ) i)
      simpa [y] using h.symm
    have hBeq :
        ∀ i : ρ,
          (Beq *ᵥ z) i =
            (Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq *ᵥ zFin)
              ((Fintype.equivFin ρ) i) := by
      intro i
      have h :=
        congrFun
          (reindexedMulVecApply Beq (Fintype.equivFin ρ) (Fintype.equivFin κ) zFin)
          ((Fintype.equivFin ρ) i)
      simpa [z] using h.symm
    have hAineq :
        ∀ i : σ,
          (Aineq *ᵥ y) i =
            (Matrix.reindex (Fintype.equivFin σ) eα Aineq *ᵥ x)
              ((Fintype.equivFin σ) i) := by
      intro i
      have h :=
        congrFun
          (reindexedMulVecApply Aineq (Fintype.equivFin σ) eα x)
          ((Fintype.equivFin σ) i)
      simpa [y] using h.symm
    have hBineq :
        ∀ i : σ,
          (Bineq *ᵥ z) i =
            (Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq *ᵥ zFin)
              ((Fintype.equivFin σ) i) := by
      intro i
      have h :=
        congrFun
          (reindexedMulVecApply Bineq (Fintype.equivFin σ) (Fintype.equivFin κ) zFin)
          ((Fintype.equivFin σ) i)
      simpa [z] using h.symm
    refine ⟨y, ?_, hyx⟩
    rw [mem_image_fst_iff]
    refine ⟨z, ?_⟩
    refine mem_linear_extended_system_iff.mpr ?_
    constructor
    · -- Evaluating the reindexed equality system at the original row indices recovers `hzEq`.
      ext i
      rw [Pi.add_apply, hAeq i, hBeq i]
      simpa using congrFun hzEq ((Fintype.equivFin ρ) i)
    · -- The transported inequalities specialize rowwise to the original formulation.
      intro i
      rw [Pi.add_apply, hAineq i, hBineq i]
      simpa using hzLe ((Fintype.equivFin σ) i)

/-- Helper for Theorem 4.51: compress the raw lift `A x + F z = b`, `z ≥ 0` to at most `n`
equality rows while keeping the same `x`-projection. -/
lemma existsCompressedRawYannakakisLift
    {m n nr : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (F : Matrix (Fin m) (Fin nr) ℝ)
    (b : Fin m → ℝ)
    (hraw_nonempty :
      Set.Nonempty
        (Prod.fst '' linear_extended_system A F b
          (0 : Matrix (Fin nr) (Fin n) ℝ) (-1) 0)) :
    ∃ r s k : ℕ,
      ∃ hconstraints : r + s ≤ n + nr,
        ∃ hvariables : n + k ≤ n + nr,
          ∃ Aeq : Matrix (Fin r) (Fin n) ℝ,
            ∃ Beq : Matrix (Fin r) (Fin k) ℝ,
              ∃ beq : Fin r → ℝ,
                ∃ Aineq : Matrix (Fin s) (Fin n) ℝ,
                  ∃ Bineq : Matrix (Fin s) (Fin k) ℝ,
                    ∃ bineq : Fin s → ℝ,
                      Prod.fst '' linear_extended_system A F b
                          (0 : Matrix (Fin nr) (Fin n) ℝ) (-1) 0 =
                        Prod.fst '' linear_extended_system Aeq Beq beq Aineq Bineq bineq := by
  -- Route correction: the old same-shape target was false in the empty case and over-specified
  -- the final normal form. The intended compression first keeps a nonempty raw lift, then allows
  -- basic `z` equalities to be rewritten into general inequality rows.
  rcases hraw_nonempty with ⟨x₀, ⟨⟨x₀', z₀⟩, hz₀, hx₀⟩⟩
  have hx₀' : x₀' = x₀ := by simpa using hx₀
  subst x₀'
  let y₀ : Fin n ⊕ Fin nr → ℝ := Sum.elim x₀ z₀
  let M : Matrix (Fin m) (Fin n ⊕ Fin nr) ℝ := Matrix.fromCols A F
  have hy₀ : M *ᵥ y₀ = b := by
    -- Read the raw lift equality block as one equation system on the stacked coordinates.
    simpa [M, y₀, Matrix.fromCols_mulVec_sumElim] using
      (mem_linear_extended_system_iff.mp hz₀).1
  obtain ⟨r₀, hr₀_le, N₀, e₀, hN₀_linear, hEqSet⟩ :=
    existsAffineEqualitySubsystem_le_ambient M b y₀ hy₀
  obtain ⟨basicCols₀, hbasicCols₀_unit⟩ := fullRowRankColumnBasis N₀ hN₀_linear
  let Aeq₀ : Matrix (Fin r₀) (Fin n) ℝ := fun i j ↦ N₀ i (Sum.inl j)
  let Beq₀ : Matrix (Fin r₀) (Fin nr) ℝ := fun i k ↦ N₀ i (Sum.inr k)
  have hsplitN₀ : Matrix.fromCols Aeq₀ Beq₀ = N₀ := by
    ext i j
    rcases j with j | k <;> rfl
  have hproj₀ :
      Prod.fst '' linear_extended_system A F b
          (0 : Matrix (Fin nr) (Fin n) ℝ) (-1) 0 =
        Prod.fst '' linear_extended_system Aeq₀ Beq₀ e₀
          (0 : Matrix (Fin nr) (Fin n) ℝ) (-1) 0 := by
    ext x
    constructor
    · rintro ⟨⟨x, z⟩, hxz, rfl⟩
      refine ⟨(x, z), ?_, rfl⟩
      rw [mem_linear_extended_system_iff] at hxz ⊢
      constructor
      · have hxM : M *ᵥ Sum.elim x z = b := by
          simpa [M, Matrix.fromCols_mulVec_sumElim] using hxz.1
        have hxN : N₀ *ᵥ Sum.elim x z = e₀ := by
          have hxMem :
              Sum.elim x z ∈ ({y : Fin n ⊕ Fin nr → ℝ | M *ᵥ y = b} : Set (Fin n ⊕ Fin nr → ℝ)) :=
            hxM
          rw [hEqSet] at hxMem
          exact hxMem
        simpa [← hsplitN₀, Matrix.fromCols_mulVec_sumElim] using hxN
      · exact hxz.2
    · rintro ⟨⟨x, z⟩, hxz, rfl⟩
      refine ⟨(x, z), ?_, rfl⟩
      rw [mem_linear_extended_system_iff] at hxz ⊢
      constructor
      · have hxN : N₀ *ᵥ Sum.elim x z = e₀ := by
          simpa [← hsplitN₀, Matrix.fromCols_mulVec_sumElim] using hxz.1
        have hxM : M *ᵥ Sum.elim x z = b := by
          have hxMem :
              Sum.elim x z ∈ ({y : Fin n ⊕ Fin nr → ℝ | N₀ *ᵥ y = e₀} : Set (Fin n ⊕ Fin nr → ℝ)) :=
            hxN
          rw [← hEqSet] at hxMem
          exact hxMem
        simpa [M, Matrix.fromCols_mulVec_sumElim] using hxM
      · exact hxz.2
  -- TODO: the row-basis step is now verified, including a concrete invertible column basis
  -- `basicCols₀` for the compressed equality block `N₀`. The remaining blocker is the
  -- source-faithful pivot elimination. The remaining work is to convert the compressed raw lift
  -- into a mixed system with the same `x`-projection by splitting basis columns into visible and
  -- auxiliary coordinates and then substituting the solved basic auxiliary variables.
  classical
  let B : Matrix (Fin r₀) (Fin r₀) ℝ := N₀.submatrix id basicCols₀
  let basicXIdx : Type := {i : Fin r₀ // ∃ j : Fin n, basicCols₀ i = Sum.inl j}
  let basicZIdx : Type := {i : Fin r₀ // ∃ k : Fin nr, basicCols₀ i = Sum.inr k}
  let xFree : Type := {j : Fin n // Sum.inl j ∉ Set.range basicCols₀}
  let zFree : Type := {k : Fin nr // Sum.inr k ∉ Set.range basicCols₀}
  let basicXCoord : basicXIdx → Fin n := fun i ↦ Classical.choose i.2
  let basicZCoord : basicZIdx → Fin nr := fun i ↦ Classical.choose i.2
  have hbasicXCoord :
      ∀ i : basicXIdx, basicCols₀ i.1 = Sum.inl (basicXCoord i) := by
    intro i
    exact Classical.choose_spec i.2
  have hbasicZCoord :
      ∀ i : basicZIdx, basicCols₀ i.1 = Sum.inr (basicZCoord i) := by
    intro i
    exact Classical.choose_spec i.2
  obtain ⟨basisOrder, hbasisOrder, hbasisOrderXFree, hbasisOrderZFree⟩ :=
    existsBasisOrderedColumnEquiv basicCols₀
  have hbasisOrder_symm :
      ∀ i : Fin r₀, basisOrder.symm (Sum.inl i) = basicCols₀ i := by
    intro i
    simpa using (congrArg basisOrder.symm (hbasisOrder i)).symm
  have hbasisOrderXFree_symm :
      ∀ j : xFree, basisOrder.symm (Sum.inr (Sum.inl j)) = Sum.inl j.1 := by
    intro j
    simpa using (congrArg basisOrder.symm (hbasisOrderXFree j)).symm
  have hbasisOrderZFree_symm :
      ∀ k : zFree, basisOrder.symm (Sum.inr (Sum.inr k)) = Sum.inr k.1 := by
    intro k
    simpa using (congrArg basisOrder.symm (hbasisOrderZFree k)).symm
  let N₁ : Matrix (Fin r₀) (Fin r₀ ⊕ (xFree ⊕ zFree)) ℝ :=
    Matrix.reindex (Equiv.refl _) basisOrder N₀
  let C : Matrix (Fin r₀) (xFree ⊕ zFree) ℝ := fun i j ↦ N₁ i (Sum.inr j)
  have hN₁_split : Matrix.fromCols B C = N₁ := by
    ext i j
    rcases j with j | j
    · simp [B, C, N₁, hbasisOrder_symm]
    · rfl
  let rhs : Fin r₀ → ℝ := B⁻¹ *ᵥ e₀
  let D : Matrix (Fin r₀) (xFree ⊕ zFree) ℝ := B⁻¹ * C
  let Dx : Matrix (Fin r₀) xFree ℝ := fun i j ↦ D i (Sum.inl j)
  let Dz : Matrix (Fin r₀) zFree ℝ := fun i k ↦ D i (Sum.inr k)
  have hD_split : Matrix.fromCols Dx Dz = D := by
    ext i j
    rcases j with j | k <;> rfl
  let visibleBasicMatrix : Matrix basicXIdx (Fin n) ℝ :=
    fun i j ↦ if j = basicXCoord i then 1 else 0
  let visibleFreeEqMatrix : Matrix basicXIdx (Fin n) ℝ :=
    fun i j ↦ if h : Sum.inl j ∉ Set.range basicCols₀ then Dx i.1 ⟨j, h⟩ else 0
  let visibleFreeIneqMatrix : Matrix basicZIdx (Fin n) ℝ :=
    fun i j ↦ if h : Sum.inl j ∉ Set.range basicCols₀ then Dx i.1 ⟨j, h⟩ else 0
  let Aeq₁ : Matrix basicXIdx (Fin n) ℝ := visibleBasicMatrix + visibleFreeEqMatrix
  let Beq₁ : Matrix basicXIdx zFree ℝ := fun i k ↦ Dz i.1 k
  let beq₁ : basicXIdx → ℝ := fun i ↦ rhs i.1
  let Aineq₁ : Matrix (basicZIdx ⊕ zFree) (Fin n) ℝ :=
    Matrix.fromRows visibleFreeIneqMatrix 0
  let Bineq₁ : Matrix (basicZIdx ⊕ zFree) zFree ℝ :=
    Matrix.fromRows (fun i k ↦ Dz i.1 k) (-1)
  let bineq₁ : basicZIdx ⊕ zFree → ℝ := Sum.elim (fun i ↦ rhs i.1) 0
  -- TODO: the remaining blocker is the projection bridge from the compressed raw lift
  -- `Aeq₀ x + Beq₀ z = e₀`, `z ≥ 0` to the direct mixed system on `zFree`. The stable frontier is:
  -- the row-basis compression `hproj₀`, the basis-first ordering `basisOrder`, the basic block
  -- solve API `basicBlockMulVec_eq_iff`, and the final reindex/count wrapper below. The missing
  -- step is to prove that solving the basis block yields exactly the equality rows on `basicXIdx`
  -- and inequality rows on `basicZIdx ⊕ zFree`, with unchanged `x`-projection.
  have hprojection_decomp :
      Prod.fst '' linear_extended_system Aeq₀ Beq₀ e₀
          (0 : Matrix (Fin nr) (Fin n) ℝ) (-1) 0 =
        Prod.fst '' linear_extended_system Aeq₁ Beq₁ beq₁ Aineq₁ Bineq₁ bineq₁ := by
    ext x
    rw [mem_image_fst_iff, mem_image_fst_iff]
    constructor
    · rintro ⟨z, hz⟩
      rcases (mem_linear_extended_system_iff.mp hz) with ⟨hzEq, hzLe⟩
      let u : Fin r₀ → ℝ := fun i ↦ Sum.elim x z (basicCols₀ i)
      let xFreeVal : xFree → ℝ := fun j ↦ x j.1
      let zFreeVal : zFree → ℝ := fun k ↦ z k.1
      let w : xFree ⊕ zFree → ℝ := Sum.elim xFreeVal zFreeVal
      let orderedCoords : Fin r₀ ⊕ (xFree ⊕ zFree) → ℝ := Sum.elim u w
      -- Normalize the compressed witness to the basis-first coordinate order.
      have hsplitCoords :
          orderedCoords = fun s ↦ Sum.elim x z (basisOrder.symm s) := by
        simpa [u, xFreeVal, zFreeVal, w, orderedCoords] using
          basisOrderCoordinates_eq_split
            basicCols₀
            basisOrder
            hbasisOrder
            hbasisOrderXFree
            hbasisOrderZFree
            x
            z
      have hcoordTransport :
          (LinearEquiv.funCongrLeft ℝ ℝ basisOrder) orderedCoords = Sum.elim x z := by
        funext s
        simpa using congrFun hsplitCoords (basisOrder s)
      have hN₀eq : N₀ *ᵥ Sum.elim x z = e₀ := by
        simpa [← hsplitN₀, Matrix.fromCols_mulVec_sumElim] using hzEq
      have hN₁eq : N₁ *ᵥ orderedCoords = e₀ := by
        -- Reindexing the columns only permutes the ambient stacked coordinates.
        calc
          N₁ *ᵥ orderedCoords =
              fun i ↦
                (N₀ *ᵥ
                  ((LinearEquiv.funCongrLeft ℝ ℝ basisOrder) orderedCoords)) i := by
                simpa [N₁] using
                  reindexedMulVecApply N₀ (Equiv.refl _) basisOrder orderedCoords
          _ = N₀ *ᵥ Sum.elim x z := by rw [hcoordTransport]
          _ = e₀ := hN₀eq
      have huSolve :
          u = B⁻¹ *ᵥ (e₀ - C *ᵥ w) := by
        -- Solve the leading basic block once after the basis-first normalization.
        exact
          (basicBlockMulVec_eq_iff B C e₀ u w hbasicCols₀_unit).mp <|
            by simpa [orderedCoords, hN₁_split] using hN₁eq
      have hDw :
          D *ᵥ w = Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal := by
        simpa [D, hD_split, w] using
          (Matrix.fromCols_mulVec_sumElim Dx Dz xFreeVal zFreeVal)
      have huFormula :
          u = rhs - (Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) := by
        calc
          u = B⁻¹ *ᵥ (e₀ - C *ᵥ w) := huSolve
          _ = B⁻¹ *ᵥ e₀ - B⁻¹ *ᵥ (C *ᵥ w) := by rw [Matrix.mulVec_sub]
          _ = rhs - (B⁻¹ * C) *ᵥ w := by rw [← Matrix.mulVec_mulVec]
          _ = rhs - D *ᵥ w := by rfl
          _ = rhs - (Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) := by rw [hDw]
      have hvisibleBasicMul :
          visibleBasicMatrix *ᵥ x = fun i ↦ x (basicXCoord i) := by
        ext i
        change (fun j : Fin n ↦ if j = basicXCoord i then (1 : ℝ) else 0) ⬝ᵥ x =
          x (basicXCoord i)
        have hrow :
            (fun j : Fin n ↦ if j = basicXCoord i then (1 : ℝ) else 0) =
              Pi.single (basicXCoord i) (1 : ℝ) := by
          funext j
          by_cases h : j = basicXCoord i
          · subst h
            simp [Pi.single]
          · simp [Pi.single, h]
        rw [hrow]
        simpa using (single_one_dotProduct (basicXCoord i) x)
      let DxBasicX : Matrix basicXIdx xFree ℝ := fun i j ↦ Dx i.1 j
      let DxBasicZ : Matrix basicZIdx xFree ℝ := fun i j ↦ Dx i.1 j
      have hvisibleFreeEqMul :
          visibleFreeEqMatrix *ᵥ x = DxBasicX *ᵥ xFreeVal := by
        simpa [visibleFreeEqMatrix, xFreeVal, DxBasicX] using
          (subtypeLift_mulVec
            (p := fun j : Fin n ↦ Sum.inl j ∉ Set.range basicCols₀)
            DxBasicX
            x)
      have hvisibleFreeIneqMul :
          visibleFreeIneqMatrix *ᵥ x = DxBasicZ *ᵥ xFreeVal := by
        simpa [visibleFreeIneqMatrix, xFreeVal, DxBasicZ] using
          (subtypeLift_mulVec
            (p := fun j : Fin n ↦ Sum.inl j ∉ Set.range basicCols₀)
            DxBasicZ
            x)
      refine ⟨zFreeVal, ?_⟩
      refine mem_linear_extended_system_iff.mpr ?_
      constructor
      · -- Basic visible coordinates become equality rows after solving the basic block.
        ext i
        have huBasic : u i.1 = x (basicXCoord i) := by
          simpa [u, hbasicXCoord i] using rfl
        have hui :
            u i.1 = rhs i.1 - (Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) i.1 := by
          simpa [hDw] using congrFun huFormula i.1
        have hBasicRow : (visibleBasicMatrix *ᵥ x) i = x (basicXCoord i) := by
          exact congrFun hvisibleBasicMul i
        have hFreeRow : (visibleFreeEqMatrix *ᵥ x) i = (Dx *ᵥ xFreeVal) i.1 := by
          simpa [DxBasicX] using congrFun hvisibleFreeEqMul i
        have hBeqRow : (Beq₁ *ᵥ zFreeVal) i = (Dz *ᵥ zFreeVal) i.1 := by
          rfl
        have hAeqDecomp :
            Aeq₁ *ᵥ x = visibleBasicMatrix *ᵥ x + visibleFreeEqMatrix *ᵥ x := by
          simpa [Aeq₁] using (Matrix.add_mulVec visibleBasicMatrix visibleFreeEqMatrix x)
        have hAeqRow :
            (Aeq₁ *ᵥ x) i = x (basicXCoord i) + (Dx *ᵥ xFreeVal) i.1 := by
          rw [show Aeq₁ *ᵥ x = visibleBasicMatrix *ᵥ x + visibleFreeEqMatrix *ᵥ x by
            exact hAeqDecomp]
          rw [Pi.add_apply, hBasicRow, hFreeRow]
        have hrow :
            (Aeq₁ *ᵥ x + Beq₁ *ᵥ zFreeVal) i =
              x (basicXCoord i) + ((Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) i.1) := by
          rw [Pi.add_apply, hAeqRow, hBeqRow, Pi.add_apply]
          ring
        calc
          (Aeq₁ *ᵥ x + Beq₁ *ᵥ zFreeVal) i
              = x (basicXCoord i) + ((Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) i.1) := hrow
          _ = rhs i.1 := by linarith [huBasic, hui]
          _ = beq₁ i := rfl
      · intro s
        rcases s with i | k
        · -- Basic auxiliary coordinates become substituted inequality rows.
          have huBasic : u i.1 = z (basicZCoord i) := by
            simpa [u, hbasicZCoord i] using rfl
          have hzBasic_nonneg : 0 ≤ u i.1 := by
            have hk : -(z (basicZCoord i)) ≤ 0 := by
              simpa [Matrix.neg_mulVec] using hzLe (basicZCoord i)
            linarith [huBasic, hk]
          have hui :
              u i.1 = rhs i.1 - (Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) i.1 := by
            simpa [hDw] using congrFun huFormula i.1
          have hFreeRow : (visibleFreeIneqMatrix *ᵥ x) i = (Dx *ᵥ xFreeVal) i.1 := by
            simpa [DxBasicZ] using congrFun hvisibleFreeIneqMul i
          have hAineqRow :
              (Aineq₁ *ᵥ x) (Sum.inl i) = (Dx *ᵥ xFreeVal) i.1 := by
            simpa [Aineq₁, Matrix.fromRows_mulVec] using hFreeRow
          have hBineqRow :
              (Bineq₁ *ᵥ zFreeVal) (Sum.inl i) = (Dz *ᵥ zFreeVal) i.1 := by
            simpa [Bineq₁, Matrix.mulVec, dotProduct]
          have hrow :
              (Aineq₁ *ᵥ x + Bineq₁ *ᵥ zFreeVal) (Sum.inl i) =
                (Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) i.1 := by
            rw [Pi.add_apply, hAineqRow, hBineqRow, Pi.add_apply]
          calc
            (Aineq₁ *ᵥ x + Bineq₁ *ᵥ zFreeVal) (Sum.inl i)
                = (Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) i.1 := hrow
            _ ≤ rhs i.1 := by linarith [hzBasic_nonneg, hui]
            _ = bineq₁ (Sum.inl i) := rfl
        · -- Free auxiliary coordinates remain nonnegative rows.
          have hzFree_nonneg : 0 ≤ zFreeVal k := by
            have hk : -(z k.1) ≤ 0 := by
              simpa [zFreeVal, Matrix.neg_mulVec] using hzLe k.1
            linarith
          have hkLe : -zFreeVal k ≤ 0 := by linarith
          simpa [Aineq₁, Bineq₁, bineq₁, Matrix.fromRows_mulVec, Matrix.neg_mulVec,
            Pi.add_apply] using hkLe
    · rintro ⟨zFreeVal, hz⟩
      rcases (mem_linear_extended_system_iff.mp hz) with ⟨hzEq, hzLe⟩
      let xFreeVal : xFree → ℝ := fun j ↦ x j.1
      let w : xFree ⊕ zFree → ℝ := Sum.elim xFreeVal zFreeVal
      let u : Fin r₀ → ℝ := rhs - D *ᵥ w
      let orderedCoords : Fin r₀ ⊕ (xFree ⊕ zFree) → ℝ := Sum.elim u w
      let z : Fin nr → ℝ := fun k ↦ orderedCoords (basisOrder (Sum.inr k))
      -- Read the packaged direct system back into the same solved basic-block normal form.
      have hDw :
          D *ᵥ w = Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal := by
        simpa [D, hD_split, w] using
          (Matrix.fromCols_mulVec_sumElim Dx Dz xFreeVal zFreeVal)
      have hvisibleBasicMul :
          visibleBasicMatrix *ᵥ x = fun i ↦ x (basicXCoord i) := by
        ext i
        change (fun j : Fin n ↦ if j = basicXCoord i then (1 : ℝ) else 0) ⬝ᵥ x =
          x (basicXCoord i)
        have hrow :
            (fun j : Fin n ↦ if j = basicXCoord i then (1 : ℝ) else 0) =
              Pi.single (basicXCoord i) (1 : ℝ) := by
          funext j
          by_cases h : j = basicXCoord i
          · subst h
            simp [Pi.single]
          · simp [Pi.single, h]
        rw [hrow]
        simpa using (single_one_dotProduct (basicXCoord i) x)
      let DxBasicX : Matrix basicXIdx xFree ℝ := fun i j ↦ Dx i.1 j
      let DxBasicZ : Matrix basicZIdx xFree ℝ := fun i j ↦ Dx i.1 j
      have hvisibleFreeEqMul :
          visibleFreeEqMatrix *ᵥ x = DxBasicX *ᵥ xFreeVal := by
        simpa [visibleFreeEqMatrix, xFreeVal, DxBasicX] using
          (subtypeLift_mulVec
            (p := fun j : Fin n ↦ Sum.inl j ∉ Set.range basicCols₀)
            DxBasicX
            x)
      have hvisibleFreeIneqMul :
          visibleFreeIneqMatrix *ᵥ x = DxBasicZ *ᵥ xFreeVal := by
        simpa [visibleFreeIneqMatrix, xFreeVal, DxBasicZ] using
          (subtypeLift_mulVec
            (p := fun j : Fin n ↦ Sum.inl j ∉ Set.range basicCols₀)
            DxBasicZ
            x)
      have huBasicX :
          ∀ i : basicXIdx, u i.1 = x (basicXCoord i) := by
        intro i
        have hBasicRow : (visibleBasicMatrix *ᵥ x) i = x (basicXCoord i) := by
          exact congrFun hvisibleBasicMul i
        have hFreeRow : (visibleFreeEqMatrix *ᵥ x) i = (Dx *ᵥ xFreeVal) i.1 := by
          simpa [DxBasicX] using congrFun hvisibleFreeEqMul i
        have hBeqRow : (Beq₁ *ᵥ zFreeVal) i = (Dz *ᵥ zFreeVal) i.1 := by
          rfl
        have hAeqDecomp :
            Aeq₁ *ᵥ x = visibleBasicMatrix *ᵥ x + visibleFreeEqMatrix *ᵥ x := by
          simpa [Aeq₁] using (Matrix.add_mulVec visibleBasicMatrix visibleFreeEqMatrix x)
        have hAeqRow :
            (Aeq₁ *ᵥ x) i = x (basicXCoord i) + (Dx *ᵥ xFreeVal) i.1 := by
          rw [show Aeq₁ *ᵥ x = visibleBasicMatrix *ᵥ x + visibleFreeEqMatrix *ᵥ x by
            exact hAeqDecomp]
          rw [Pi.add_apply, hBasicRow, hFreeRow]
        have hrow :
            (Aeq₁ *ᵥ x + Beq₁ *ᵥ zFreeVal) i =
              x (basicXCoord i) + ((Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) i.1) := by
          rw [Pi.add_apply, hAeqRow, hBeqRow, Pi.add_apply]
          ring
        have hui :
            u i.1 = rhs i.1 - (Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) i.1 := by
          simpa [u, hDw] using rfl
        have hiEq :
            (Aeq₁ *ᵥ x + Beq₁ *ᵥ zFreeVal) i = rhs i.1 := by
          simpa [beq₁] using congrFun hzEq i
        linarith [hrow, hui, hiEq]
      have huBasicZ_nonneg :
          ∀ i : basicZIdx, 0 ≤ u i.1 := by
        intro i
        have hFreeRow : (visibleFreeIneqMatrix *ᵥ x) i = (Dx *ᵥ xFreeVal) i.1 := by
          simpa [DxBasicZ] using congrFun hvisibleFreeIneqMul i
        have hAineqRow :
            (Aineq₁ *ᵥ x) (Sum.inl i) = (Dx *ᵥ xFreeVal) i.1 := by
          simpa [Aineq₁, Matrix.fromRows_mulVec] using hFreeRow
        have hBineqRow :
            (Bineq₁ *ᵥ zFreeVal) (Sum.inl i) = (Dz *ᵥ zFreeVal) i.1 := by
          simpa [Bineq₁, Matrix.mulVec, dotProduct]
        have hrow :
            (Aineq₁ *ᵥ x + Bineq₁ *ᵥ zFreeVal) (Sum.inl i) =
              (Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) i.1 := by
          rw [Pi.add_apply, hAineqRow, hBineqRow, Pi.add_apply]
        have hui :
            u i.1 = rhs i.1 - (Dx *ᵥ xFreeVal + Dz *ᵥ zFreeVal) i.1 := by
          simpa [u, hDw] using rfl
        have hiLe :
            (Aineq₁ *ᵥ x + Bineq₁ *ᵥ zFreeVal) (Sum.inl i) ≤ rhs i.1 := by
          simpa [bineq₁] using hzLe (Sum.inl i)
        linarith [hrow, hui, hiLe]
      have hzFree_nonneg :
          ∀ k : zFree, 0 ≤ zFreeVal k := by
        intro k
        have hk : -zFreeVal k ≤ 0 := by
          simpa [Aineq₁, Bineq₁, bineq₁, Matrix.fromRows_mulVec, Matrix.neg_mulVec,
            Pi.add_apply] using hzLe (Sum.inr k)
        linarith
      have huSolve :
          u = B⁻¹ *ᵥ (e₀ - C *ᵥ w) := by
        calc
          u = rhs - D *ᵥ w := by rfl
          _ = B⁻¹ *ᵥ e₀ - (B⁻¹ * C) *ᵥ w := by rfl
          _ = B⁻¹ *ᵥ e₀ - B⁻¹ *ᵥ (C *ᵥ w) := by rw [← Matrix.mulVec_mulVec]
          _ = B⁻¹ *ᵥ (e₀ - C *ᵥ w) := by rw [Matrix.mulVec_sub]
      have hN₁eq : N₁ *ᵥ orderedCoords = e₀ := by
        simpa [orderedCoords, hN₁_split] using
          (basicBlockMulVec_eq_iff B C e₀ u w hbasicCols₀_unit).mpr huSolve
      have hcoordTransport :
          (LinearEquiv.funCongrLeft ℝ ℝ basisOrder) orderedCoords = Sum.elim x z := by
        funext s
        rcases s with j | k
        · by_cases hj : Sum.inl j ∈ Set.range basicCols₀
          · rcases hj with ⟨i, hi⟩
            let ibasic : basicXIdx := ⟨i, ⟨j, hi⟩⟩
            have hibasicOrder : basisOrder (Sum.inl j) = Sum.inl i := by
              simpa [hi] using hbasisOrder i
            have hcoordEq : basicXCoord ibasic = j := by
              apply Sum.inl.inj
              calc
                Sum.inl (basicXCoord ibasic) = basicCols₀ ibasic.1 := by
                  simpa [ibasic] using (hbasicXCoord ibasic).symm
                _ = Sum.inl j := hi
            calc
              (LinearEquiv.funCongrLeft ℝ ℝ basisOrder) orderedCoords (Sum.inl j)
                  = orderedCoords (basisOrder (Sum.inl j)) := rfl
              _ = orderedCoords (Sum.inl i) := by rw [hibasicOrder]
              _ = u i := rfl
              _ = x (basicXCoord ibasic) := by simpa [ibasic] using huBasicX ibasic
              _ = x j := by rw [hcoordEq]
              _ = Sum.elim x z (Sum.inl j) := rfl
          · let jFree : xFree := ⟨j, hj⟩
            calc
              (LinearEquiv.funCongrLeft ℝ ℝ basisOrder) orderedCoords (Sum.inl j)
                  = orderedCoords (basisOrder (Sum.inl j)) := rfl
              _ = orderedCoords (Sum.inr (Sum.inl jFree)) := by
                    rw [show basisOrder (Sum.inl j) = Sum.inr (Sum.inl jFree) by
                      simpa [jFree] using hbasisOrderXFree jFree]
              _ = w (Sum.inl jFree) := rfl
              _ = x j := rfl
              _ = Sum.elim x z (Sum.inl j) := rfl
        · calc
            (LinearEquiv.funCongrLeft ℝ ℝ basisOrder) orderedCoords (Sum.inr k)
                = orderedCoords (basisOrder (Sum.inr k)) := rfl
            _ = z k := rfl
            _ = Sum.elim x z (Sum.inr k) := rfl
      have hN₀eq : N₀ *ᵥ Sum.elim x z = e₀ := by
        -- Undo the basis-first reindexing after solving the leading block.
        calc
          N₀ *ᵥ Sum.elim x z =
              fun i ↦
                (N₀ *ᵥ
                  ((LinearEquiv.funCongrLeft ℝ ℝ basisOrder) orderedCoords)) i := by
                rw [hcoordTransport]
          _ = N₁ *ᵥ orderedCoords := by
                symm
                simpa [N₁] using
                  reindexedMulVecApply N₀ (Equiv.refl _) basisOrder orderedCoords
          _ = e₀ := hN₁eq
      refine ⟨z, ?_⟩
      refine mem_linear_extended_system_iff.mpr ?_
      constructor
      · -- The reconstructed stacked coordinates satisfy the compressed equality block.
        simpa [← hsplitN₀, Matrix.fromCols_mulVec_sumElim] using hN₀eq
      · intro k
        by_cases hk : Sum.inr k ∈ Set.range basicCols₀
        · rcases hk with ⟨i, hi⟩
          let ibasic : basicZIdx := ⟨i, ⟨k, hi⟩⟩
          have hkval : z k = u i := by
            calc
              z k = orderedCoords (basisOrder (Sum.inr k)) := rfl
              _ = orderedCoords (Sum.inl i) := by
                    rw [show basisOrder (Sum.inr k) = Sum.inl i by simpa [hi] using hbasisOrder i]
              _ = u i := rfl
          have hu_nonneg : 0 ≤ u i := by
            simpa [ibasic] using huBasicZ_nonneg ibasic
          have hz_nonneg : 0 ≤ z k := by
            rw [hkval]
            exact hu_nonneg
          simpa [Matrix.neg_mulVec] using neg_nonpos.mpr hz_nonneg
        · let kFree : zFree := ⟨k, hk⟩
          have hkval : z k = zFreeVal kFree := by
            calc
              z k = orderedCoords (basisOrder (Sum.inr k)) := rfl
              _ = orderedCoords (Sum.inr (Sum.inr kFree)) := by
                    rw [show basisOrder (Sum.inr k) = Sum.inr (Sum.inr kFree) by
                      simpa [kFree] using hbasisOrderZFree kFree]
              _ = w (Sum.inr kFree) := rfl
              _ = zFreeVal kFree := rfl
          have hz_nonneg : 0 ≤ z k := by
            rw [hkval]
            exact hzFree_nonneg kFree
          simpa [Matrix.neg_mulVec] using neg_nonpos.mpr hz_nonneg
  have hprojection_reindex :
      Prod.fst '' linear_extended_system Aeq₁ Beq₁ beq₁ Aineq₁ Bineq₁ bineq₁ =
        Prod.fst ''
          linear_extended_system
            (Matrix.reindex (Fintype.equivFin basicXIdx) (Equiv.refl _) Aeq₁)
            (Matrix.reindex (Fintype.equivFin basicXIdx) (Fintype.equivFin zFree) Beq₁)
            (fun i ↦ beq₁ ((Fintype.equivFin basicXIdx).symm i))
            (Matrix.reindex (Fintype.equivFin (basicZIdx ⊕ zFree)) (Equiv.refl _) Aineq₁)
            (Matrix.reindex (Fintype.equivFin (basicZIdx ⊕ zFree)) (Fintype.equivFin zFree) Bineq₁)
            (fun i ↦ bineq₁ ((Fintype.equivFin (basicZIdx ⊕ zFree)).symm i)) := by
    -- Only the row and auxiliary owners are reindexed to `Fin`; the visible owner stays fixed.
    simpa using
      (reindexVisibleCoordinates_image_linear_extended_formulation
        (n := n)
        (eα := Equiv.refl (Fin n))
        Aeq₁ Beq₁ beq₁ Aineq₁ Bineq₁ bineq₁)
  have hconstraints :
      Fintype.card basicXIdx + Fintype.card (basicZIdx ⊕ zFree) ≤ n + nr := by
    have hbasicX_le : Fintype.card basicXIdx ≤ n := basicVisibleIndexCard_le basicCols₀
    have haux_card : Fintype.card (basicZIdx ⊕ zFree) = nr :=
      auxiliaryBasicAndFree_card_eq basicCols₀
    omega
  have hvariables : n + Fintype.card zFree ≤ n + nr := by
    have hzFree_le : Fintype.card zFree ≤ nr := by
      simpa using
        (Fintype.card_le_of_injective (fun k : zFree ↦ k.1)
          fun _ _ h => Subtype.ext h)
    omega
  refine ⟨Fintype.card basicXIdx, Fintype.card (basicZIdx ⊕ zFree), Fintype.card zFree,
    hconstraints, hvariables,
    Matrix.reindex (Fintype.equivFin basicXIdx) (Equiv.refl _) Aeq₁,
    Matrix.reindex (Fintype.equivFin basicXIdx) (Fintype.equivFin zFree) Beq₁,
    (fun i ↦ beq₁ ((Fintype.equivFin basicXIdx).symm i)),
    Matrix.reindex (Fintype.equivFin (basicZIdx ⊕ zFree)) (Equiv.refl _) Aineq₁,
    Matrix.reindex (Fintype.equivFin (basicZIdx ⊕ zFree)) (Fintype.equivFin zFree) Bineq₁,
    (fun i ↦ bineq₁ ((Fintype.equivFin (basicZIdx ⊕ zFree)).symm i)), ?_⟩
  exact hproj₀.trans (hprojection_decomp.trans hprojection_reindex)

/-- Auxiliary existence clause for Theorem 4.51. Assume `P` is nonempty, is given by the
displayed system `A x ≤ b`, and is the convex hull of the displayed finite family `vertices`.
Let `S` be the associated nonnegative slack matrix of this chosen presentation. Then `P` admits
a linear extended formulation with at most `rank₊ S + n` total constraints and at most
`rank₊ S + n` total variables. -/
theorem
    exists_extended_formulation_with_constraints_and_variables_le_nonnegative_rank_add_ambient_dim
    {m n p : ℕ}
    (P : Set (Fin n → ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (vertices : Fin p → Fin n → ℝ)
    (hP_nonempty : P.Nonempty)
    (hP_vertices : P = convexHull ℝ (Set.range vertices))
    (hP_system : P = polyhedron_le_set A b) :
    let hvertices := vertices_feasible_of_polytope_description P A b vertices hP_vertices hP_system
    let S : Matrix.Nonnegative (Fin m) (Fin p) ℝ :=
      ⟨slack_matrix A b vertices, slack_matrix_nonneg hvertices⟩
    let nr := rank₊ S
    ∃ r s k : ℕ,
      ∃ hconstraints : r + s ≤ nr + n,
        ∃ hvariables : n + k ≤ nr + n,
          ∃ Aeq : Matrix (Fin r) (Fin n) ℝ,
            ∃ Beq : Matrix (Fin r) (Fin k) ℝ,
                ∃ beq : Fin r → ℝ,
                  ∃ Aineq : Matrix (Fin s) (Fin n) ℝ,
                    ∃ Bineq : Matrix (Fin s) (Fin k) ℝ,
                      ∃ bineq : Fin s → ℝ,
                      P = Prod.fst '' linear_extended_system Aeq Beq beq Aineq Bineq bineq := by
  classical
  let hvertices := vertices_feasible_of_polytope_description P A b vertices hP_vertices hP_system
  let S : Matrix.Nonnegative (Fin m) (Fin p) ℝ :=
    ⟨slack_matrix A b vertices, slack_matrix_nonneg hvertices⟩
  let nr := rank₊ S
  have hleast := nonnegative_rank_isLeast S
  rcases (has_nonnegative_rank_factorization_iff.mp hleast.1) with ⟨F, W, hF, hW, hFW⟩
  have hraw :
      P = Prod.fst '' linear_extended_system A F b
        (0 : Matrix (Fin nr) (Fin n) ℝ) (-1) 0 := by
    -- Route correction: prove the raw lift directly from barycentric coordinates before trying to
    -- compress its equality block.
    exact rawYannakakisLiftProjection_eq P A b vertices F W hF hW hFW hP_vertices hP_system
  have hraw_nonempty :
      Set.Nonempty
        (Prod.fst '' linear_extended_system A F b
          (0 : Matrix (Fin nr) (Fin n) ℝ) (-1) 0) := by
    rw [← hraw]
    exact hP_nonempty
  rcases existsCompressedRawYannakakisLift A F b hraw_nonempty with
    ⟨r, s, k, hconstraints, hvariables, Aeq', Beq', beq', Aineq', Bineq', bineq', hcompress⟩
  refine ⟨r, s, k, ?_, ?_, Aeq', Beq', beq', Aineq', Bineq', bineq', ?_⟩
  · simpa [nr, Nat.add_comm] using hconstraints
  · simpa [nr, Nat.add_comm] using hvariables
  · exact hraw.trans hcompress

/-- Theorem 4.51 (Yannakakis). Let `P ⊆ ℝ^n` be a polytope, and let `t` be its
nonnegative rank, encoded here by the source-faithful witness `IsNonnegativeRankOfPolytope P t`
that separates the singleton case from the positive-dimensional facet-slack case. Then every
extended formulation of `P` has at least `t` constraints, where "constraints" counts equality
rows plus inequality rows. Moreover, `P` admits an extended formulation with at most `t + n`
constraints and `t + n` variables. -/
theorem compressRawYannakakisLift
    {n : ℕ}
    (P : Set (Fin n → ℝ))
    (t : ℕ)
    (ht : IsNonnegativeRankOfPolytope P t) :
    (∀ {ρ : Type u} {σ : Type v} {κ : Type w} [Fintype ρ] [Fintype σ] [Fintype κ]
      (Aeq : Matrix ρ (Fin n) ℝ)
      (Beq : Matrix ρ κ ℝ)
      (beq : ρ → ℝ)
      (Aineq : Matrix σ (Fin n) ℝ)
      (Bineq : Matrix σ κ ℝ)
      (bineq : σ → ℝ),
        P = Prod.fst '' linear_extended_system Aeq Beq beq Aineq Bineq bineq →
          t ≤ Fintype.card ρ + Fintype.card σ) ∧
      ∃ r s k : ℕ,
        ∃ hconstraints : r + s ≤ t + n,
          ∃ hvariables : n + k ≤ t + n,
            ∃ Aeq : Matrix (Fin r) (Fin n) ℝ,
              ∃ Beq : Matrix (Fin r) (Fin k) ℝ,
                ∃ beq : Fin r → ℝ,
                  ∃ Aineq : Matrix (Fin s) (Fin n) ℝ,
                    ∃ Bineq : Matrix (Fin s) (Fin k) ℝ,
                      ∃ bineq : Fin s → ℝ,
                        P = Prod.fst ''
                          linear_extended_system Aeq Beq beq Aineq Bineq bineq := by
  classical
  rcases ht with ⟨x₀, hP_singleton, rfl⟩ | ⟨m, p, A, b, vertices, hP_vertices, hP_system, hfacets, ht⟩
  · constructor
    · intro ρ σ κ _ _ _ Aeq Beq beq Aineq Bineq bineq hEF
      exact Nat.zero_le _
    · -- The singleton case uses the equality-only lift `x = x₀`.
      refine ⟨n, 0, 0, by simpa, by simpa,
        (1 : Matrix (Fin n) (Fin n) ℝ), (0 : Matrix (Fin n) (Fin 0) ℝ), x₀,
        (0 : Matrix (Fin 0) (Fin n) ℝ), (0 : Matrix (Fin 0) (Fin 0) ℝ), (0 : Fin 0 → ℝ), ?_⟩
      ext x
      constructor
      · intro hx
        rw [hP_singleton] at hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        refine ⟨(x₀, fun j ↦ Fin.elim0 j), ?_, rfl⟩
        rw [mem_linear_extended_system_iff]
        constructor
        · ext i
          simp
        · intro i
          exact Fin.elim0 i
      · rintro ⟨⟨x', z⟩, hxz, rfl⟩
        rw [hP_singleton, Set.mem_singleton_iff]
        have hxEq := (mem_linear_extended_system_iff.mp hxz).1
        simpa using hxEq
  · constructor
    · intro ρ σ κ _ _ _ Aeq Beq beq Aineq Bineq bineq hEF
      -- Route correction: the lower bound only uses the facet presentation encoded in `ht`.
      let hvertices := vertices_feasible_of_polytope_description P A b vertices hP_vertices hP_system
      let S : Matrix.Nonnegative (Fin m) (Fin p) ℝ :=
        ⟨slack_matrix A b vertices, slack_matrix_nonneg hvertices⟩
      have htS : rank₊ S = t := by
        simpa [hvertices, S] using ht
      simpa [htS, hvertices, S] using
        nonnegative_rank_le_extended_formulation_constraint_count
          P A b vertices Aeq Beq beq Aineq Bineq bineq hP_vertices hP_system hfacets hEF
    · have hP_nonempty : P.Nonempty := by
        by_cases hm : m = 0
        · subst hm
          refine ⟨0, ?_⟩
          rw [hP_system, mem_polyhedron_le_set_iff]
          intro i
          exact Fin.elim0 i
        · let i : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
          have hface_nonempty : (face_set P (A i) (b i)).Nonempty := by
            have hproper :
                is_proper_face P (face_set P (A i) (b i)) := by
              exact
                maximalProperFace_to_isProperFace
                  (maximalProperFaceInequality_isFacet (hfacets i))
            exact (is_proper_face_iff.mp hproper).2.1
          rcases hface_nonempty with ⟨x, hxface⟩
          exact ⟨x, (mem_face_set_iff.mp hxface).1⟩
      -- The existence clause reduces directly to the factorization-based upper helper theorem.
      let hvertices := vertices_feasible_of_polytope_description P A b vertices hP_vertices hP_system
      let S : Matrix.Nonnegative (Fin m) (Fin p) ℝ :=
        ⟨slack_matrix A b vertices, slack_matrix_nonneg hvertices⟩
      have htS : rank₊ S = t := by
        simpa [hvertices, S] using ht
      simpa [htS, hvertices, S] using
        exists_extended_formulation_with_constraints_and_variables_le_nonnegative_rank_add_ambient_dim
          P A b vertices hP_nonempty hP_vertices hP_system
