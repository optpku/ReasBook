import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_definition_3_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_theorem_3_40

open scoped BigOperators Matrix

section Theorem460

variable {m n : ℕ}

namespace RationalFamily

variable {ι : Type*}

/-- A rational family is a Hilbert basis when every integral vector in its rational cone is a
nonnegative integral combination of family members. -/
def IsHilbertBasis (a : ι → Fin n → ℚ) : Prop :=
  ∀ z : Fin n → ℤ,
    (fun i ↦ (z i : ℚ)) ∈ (PointedCone.hull ℚ (Set.range a) : Set (Fin n → ℚ)) →
      ∃ u : ι →₀ ℕ,
        (fun i ↦ (z i : ℚ)) = u.sum (fun i c ↦ c • a i)

end RationalFamily

/-- An integral family is a Hilbert basis when its canonical rational realization is a rational
Hilbert basis. -/
abbrev IsHilbertBasisFamily {ι : Type*} (a : ι → Fin n → ℤ) : Prop :=
  RationalFamily.IsHilbertBasis (fun i ↦ fun j ↦ (a i j : ℚ))

/-- Definition 4.6-extra-1, localized for Theorem 4.60: the dual feasible region of the rational
system `A x ≤ b` for the integral objective `c`. -/
def rational_dual_feasible_region
    (A : Matrix (Fin m) (Fin n) ℚ) (c : Fin n → ℤ) : Set (Fin m → ℝ) :=
  {y | y ᵥ* (A.map (Rat.castHom ℝ)) = (fun j ↦ (c j : ℝ)) ∧ 0 ≤ y}

/-- Helper for Theorem 4.60: membership in the localized rational dual feasible region is exactly
the system `y A = c, y ≥ 0` after casting the data to `ℝ`. -/
theorem mem_rational_dual_feasible_region_iff
    {A : Matrix (Fin m) (Fin n) ℚ} {c : Fin n → ℤ} {y : Fin m → ℝ} :
    y ∈ rational_dual_feasible_region A c ↔
      y ᵥ* (A.map (Rat.castHom ℝ)) = (fun j ↦ (c j : ℝ)) ∧ 0 ≤ y :=
  Iff.rfl

/-- Definition 4.6-extra-1, localized for Theorem 4.60: the primal linear program `max {c x :
A x ≤ b}` has a finite optimum when some feasible point attains the greatest objective value. -/
def rational_primal_has_finite_optimum
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℤ) : Prop :=
  ∃ xStar ∈ rational_matrix_polyhedron A b,
    IsGreatest
      ((fun x : Fin n → ℝ ↦ (fun j ↦ (c j : ℝ)) ⬝ᵥ x) ''
        rational_matrix_polyhedron A b)
      ((fun j ↦ (c j : ℝ)) ⬝ᵥ xStar)

/-- Definition 4.6-extra-1, localized for Theorem 4.60: the dual linear program has an integral
optimal solution when some feasible dual point in `integerVectors m` attains the least dual
objective value. -/
def rational_dual_has_integral_optimal_solution
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℤ) : Prop :=
  ∃ yStar ∈ rational_dual_feasible_region A c,
    yStar ∈ integerVectors m ∧
      IsLeast
        ((fun y : Fin m → ℝ ↦ y ⬝ᵥ (fun i ↦ (b i : ℝ))) ''
          rational_dual_feasible_region A c)
        (yStar ⬝ᵥ (fun i ↦ (b i : ℝ)))

/-- Definition 4.6-extra-1, localized for Theorem 4.60: a rational system is totally dual
integral when every integral objective with finite primal optimum has an integral dual optimum. -/
def totally_dual_integral
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) : Prop :=
  ∀ c : Fin n → ℤ,
    rational_primal_has_finite_optimum A b c →
      rational_dual_has_integral_optimal_solution A b c

namespace RationalMatrixPolyhedron

/-- The row indices active on a face `F` of the rational system `A x ≤ b`. -/
def activeRowIndices
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (F : Set (Fin n → ℝ)) : Set (Fin m) :=
  {i | ∀ ⦃x : Fin n → ℝ⦄, x ∈ F → ((A.map (Rat.castHom ℝ)) *ᵥ x) i = (b i : ℝ)}

/-- The active rows of the rational system `A x ≤ b` along `F`, viewed as a rational family
indexed by the active inequalities. -/
def activeRows
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (F : Set (Fin n → ℝ)) :
    activeRowIndices A b F → Fin n → ℚ :=
  fun i ↦ A i.1

end RationalMatrixPolyhedron

/-- Helper for Theorem 4.60: every valid inequality on a nonempty polyhedron comes from a
nonnegative row multiplier. This is the dependency-closed core of Theorem 3.22. -/
private theorem valid_inequality_iff_exists_nonneg_row_multiplier_raw
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ)
    (b : m → ℝ)
    (c : n → ℝ)
    (δ : ℝ)
    (hP_nonempty : Set.Nonempty {x : n → ℝ | A *ᵥ x ≤ b}) :
    (∀ ⦃x : n → ℝ⦄, x ∈ {x : n → ℝ | A *ᵥ x ≤ b} → c ⬝ᵥ x ≤ δ) ↔
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
        rw [hw]
        rfl
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
          simpa [hslack_eval, w, hneg]
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

/-- Helper for Theorem 4.60: a valid inequality on a nonempty rational matrix polyhedron yields a
nonnegative real row multiplier. -/
lemma exists_nonneg_row_multiplier_of_valid_rational_inequality
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (cR : Fin n → ℝ)
    (δ : ℝ)
    (hP_nonempty : (rational_matrix_polyhedron A b).Nonempty)
    (hvalid : is_valid_inequality (rational_matrix_polyhedron A b) cR δ) :
    ∃ y : Fin m → ℝ,
      0 ≤ y ∧
        y ᵥ* (A.map (Rat.castHom ℝ)) = cR ∧
          (y ⬝ᵥ (fun i ↦ (b i : ℝ))) ≤ δ := by
  simpa [rational_matrix_polyhedron] using
    (valid_inequality_iff_exists_nonneg_row_multiplier_raw
      (A.map (Rat.castHom ℝ))
      (fun i ↦ (b i : ℝ))
      cR
      δ
      hP_nonempty).mp hvalid

/-- Helper for Theorem 4.60: if a valid inequality is attained on its equality face, then the
corresponding row multiplier attains the same objective value. -/
lemma exists_nonneg_row_multiplier_of_attained_valid_rational_inequality
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (cR : Fin n → ℝ)
    (δ : ℝ)
    (hvalid : is_valid_inequality (rational_matrix_polyhedron A b) cR δ)
    (hattained : (face_set (rational_matrix_polyhedron A b) cR δ).Nonempty) :
    ∃ y : Fin m → ℝ,
      0 ≤ y ∧
        y ᵥ* (A.map (Rat.castHom ℝ)) = cR ∧
          (y ⬝ᵥ (fun i ↦ (b i : ℝ))) = δ := by
  obtain ⟨x₀, hx₀_face⟩ := hattained
  have hx₀P : x₀ ∈ rational_matrix_polyhedron A b := (mem_face_set_iff.mp hx₀_face).1
  have hx₀_eq : cR ⬝ᵥ x₀ = δ := (mem_face_set_iff.mp hx₀_face).2
  obtain ⟨y, hy_nonneg, hy_row, hy_le⟩ :=
    exists_nonneg_row_multiplier_of_valid_rational_inequality A b cR δ ⟨x₀, hx₀P⟩ hvalid
  have hδ_le : δ ≤ y ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
    -- Evaluate the certificate at a point where the valid inequality is tight.
    calc
      δ = cR ⬝ᵥ x₀ := hx₀_eq.symm
      _ = (y ᵥ* (A.map (Rat.castHom ℝ))) ⬝ᵥ x₀ := by
            rw [← hy_row]
      _ = y ⬝ᵥ ((A.map (Rat.castHom ℝ)) *ᵥ x₀) := by
            rw [Matrix.dotProduct_mulVec]
      _ ≤ y ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
            exact dotProduct_le_dotProduct_of_nonneg_left
              ((mem_rational_matrix_polyhedron A b x₀).mp hx₀P) hy_nonneg
  have hy_eq : y ⬝ᵥ (fun i ↦ (b i : ℝ)) = δ := le_antisymm hy_le hδ_le
  exact ⟨y, hy_nonneg, hy_row, hy_eq⟩

/-- Helper for Theorem 4.60: the optimal equality face of a finite attained linear maximum is a
nonempty extreme face. -/
lemma optimal_face_is_extreme
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (cR : Fin n → ℝ)
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ rational_matrix_polyhedron A b)
    (hopt :
      IsGreatest
        ((fun x : Fin n → ℝ ↦ cR ⬝ᵥ x) '' rational_matrix_polyhedron A b)
        (cR ⬝ᵥ xStar)) :
    let F := face_set (rational_matrix_polyhedron A b) cR (cR ⬝ᵥ xStar)
    F.Nonempty ∧ IsExtreme ℝ (rational_matrix_polyhedron A b) F := by
  dsimp
  have hvalid : is_valid_inequality (rational_matrix_polyhedron A b) cR (cR ⬝ᵥ xStar) := by
    intro x hxP
    exact hopt.2 ⟨x, hxP, rfl⟩
  have hxStar_face :
      xStar ∈ face_set (rational_matrix_polyhedron A b) cR (cR ⬝ᵥ xStar) := by
    exact (mem_face_set_iff).2 ⟨hxStar, rfl⟩
  have hface_exposed :
      IsExposed ℝ
        (rational_matrix_polyhedron A b)
        (face_set (rational_matrix_polyhedron A b) cR (cR ⬝ᵥ xStar)) := by
    rw [face_set_eq_toExposed_of_mem hvalid hxStar_face]
    exact ContinuousLinearMap.toExposed.isExposed
  refine ⟨⟨xStar, hxStar_face⟩, ?_⟩
  exact hface_exposed.isExtreme

/-- Helper for Theorem 4.60: a real nonnegative solution of a rational linear system can be
rationalized without changing feasibility. -/
lemma exists_rat_nonnegative_solution_of_real_cast_feasible
    {ι : Type*} [Fintype ι]
    (M : Matrix ι (Fin n) ℚ)
    (d : Fin n → ℚ)
    (hreal :
      ∃ xR : ι → ℝ,
        (xR ᵥ* (M.map (Rat.castHom ℝ)) = fun j ↦ (d j : ℝ)) ∧ 0 ≤ xR) :
    ∃ xQ : ι → ℚ, xQ ᵥ* M = d ∧ 0 ≤ xQ := by
  rcases hreal with ⟨xR, hxR_row, hxR_nonneg⟩
  have hreal_transpose :
      ∃ xR : ι → ℝ,
        (M.transpose.map (Rat.castHom ℝ)) *ᵥ xR = (fun j ↦ (d j : ℝ)) ∧ 0 ≤ xR := by
    refine ⟨xR, ?_, hxR_nonneg⟩
    -- Rewrite the row-vector equation as the transpose-column system needed for Theorem 3.5.
    simpa [Matrix.transpose_map] using
      (Matrix.mulVec_transpose (M.map (Rat.castHom ℝ)) xR).trans hxR_row
  have hreal_multipliers :
      ∀ u : Fin n → ℝ,
        u ᵥ* (M.transpose.map (Rat.castHom ℝ)) ≤ 0 →
          u ⬝ᵥ (fun j ↦ (d j : ℝ)) ≤ 0 :=
    (feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers
      (M.transpose.map (Rat.castHom ℝ))
      (fun j ↦ (d j : ℝ))).mp hreal_transpose
  have hrat_multipliers :
      ∀ u : Fin n → ℚ, u ᵥ* M.transpose ≤ 0 → u ⬝ᵥ d ≤ 0 := by
    intro u hu
    let uR : Fin n → ℝ := fun j ↦ (u j : ℝ)
    have huR :
        uR ᵥ* (M.transpose.map (Rat.castHom ℝ)) ≤ 0 := by
      intro i
      -- Cast the rational multiplier inequality componentwise to `ℝ`.
      have hi : (u ᵥ* M.transpose) i ≤ 0 := hu i
      have hiR : ((u ᵥ* M.transpose) i : ℝ) ≤ 0 := by
        exact_mod_cast hi
      simpa [uR, Matrix.vecMul, dotProduct] using hiR
    have huR_dot : uR ⬝ᵥ (fun j ↦ (d j : ℝ)) ≤ 0 := hreal_multipliers uR huR
    have hu_dot_cast : (((u ⬝ᵥ d : ℚ) : ℝ)) ≤ 0 := by
      simpa [uR, dotProduct] using huR_dot
    exact_mod_cast hu_dot_cast
  obtain ⟨xQ, hxQ, hxQ_nonneg⟩ :=
    (feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers M.transpose d).mpr
      hrat_multipliers
  refine ⟨xQ, ?_, hxQ_nonneg⟩
  -- Return from the transpose-column system to the original row-vector equation.
  simpa [Matrix.mulVec_transpose] using hxQ

/-- Helper for Theorem 4.60: under nonnegativity, a coordinate outside the active-row set must
vanish once every positive coordinate is active. -/
lemma dual_coordinate_eq_zero_of_not_active
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (F : Set (Fin n → ℝ))
    {y : Fin m → ℝ}
    (hy_nonneg : 0 ≤ y)
    (hsupport :
      ∀ ⦃i : Fin m⦄, 0 < y i → i ∈ RationalMatrixPolyhedron.activeRowIndices A b F)
    {i : Fin m}
    (hi : i ∉ RationalMatrixPolyhedron.activeRowIndices A b F) :
    y i = 0 := by
  -- Inactive coordinates cannot be positive, so nonnegativity collapses them to zero.
  have hnot_pos : ¬ 0 < y i := by
    intro hpos
    exact hi (hsupport hpos)
  exact le_antisymm (le_of_not_gt hnot_pos) (hy_nonneg i)

/-- Helper for Theorem 4.60: after reindexing the active-row subtype by `Fin`, the real active-row
vecMul becomes the canonical finite sum over that enumeration. -/
lemma active_rows_real_vecMul_coordinate_eq_equivFin_sum
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (F : Set (Fin n → ℝ)) :
    let α := RationalMatrixPolyhedron.activeRowIndices A b F
    let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
    ∀ (yF : α → ℝ) (j : Fin n),
      ((yF ᵥ* Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) =
        ∑ k : Fin (Fintype.card α), yF (e.symm k) *
          (((RationalMatrixPolyhedron.activeRows A b F) (e.symm k) j : ℚ) : ℝ) := by
  intro α e yF j
  -- Expand the subtype-indexed vecMul and transport the sum to the canonical `Fin` enumeration.
  calc
    ((yF ᵥ* Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j)
        = ∑ i : α, yF i *
            (((RationalMatrixPolyhedron.activeRows A b F) i j : ℚ) : ℝ) := by
            simp [Matrix.vecMul, dotProduct]
    _ = ∑ k : Fin (Fintype.card α), yF (e.symm k) *
          (((RationalMatrixPolyhedron.activeRows A b F) (e.symm k) j : ℚ) : ℝ) := by
          exact Fintype.sum_equiv e
            (fun i : α ↦ yF i *
              (((RationalMatrixPolyhedron.activeRows A b F) i j : ℚ) : ℝ))
            (fun k : Fin (Fintype.card α) ↦ yF (e.symm k) *
              (((RationalMatrixPolyhedron.activeRows A b F) (e.symm k) j : ℚ) : ℝ))
            (fun i ↦ by simp)

/-- Helper for Theorem 4.60: once inactive dual coordinates vanish, the full dual row equation
collapses to the active-row subsystem. -/
lemma full_dual_row_eq_active_rows_reindexed_of_zero_off_active
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (F : Set (Fin n → ℝ)) :
    let α := RationalMatrixPolyhedron.activeRowIndices A b F
    ∀ {y : Fin m → ℝ}
      (hzero : ∀ i : Fin m, i ∉ α → y i = 0) (j : Fin n),
      ((y ᵥ* (A.map (Rat.castHom ℝ))) j) =
        (((fun i : α ↦ y i.1) ᵥ*
          Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) := by
  intro α y hzero j
  classical
  -- Pin the active-row subtype to the canonical finite instance used by the statement.
  letI : Fintype α := CategoryTheory.FinCategory.fintypeObj
  have hfull :
      ((y ᵥ* (A.map (Rat.castHom ℝ))) j) =
        ∑ i : Fin m, y i * (((A i j : ℚ) : ℝ)) := by
    -- Expand the full-row vecMul coordinate into a finite sum over all rows.
    simp [Matrix.vecMul, dotProduct]
  have hfilter :
      Finset.sum (Finset.univ.filter (fun i : Fin m ↦ i ∈ α))
        (fun i ↦ y i * (((A i j : ℚ) : ℝ))) =
        ∑ i : Fin m, y i * (((A i j : ℚ) : ℝ)) := by
    -- Inactive rows contribute `0`, so the full sum collapses to the active filter.
    exact Finset.sum_filter_of_ne (s := Finset.univ)
      (f := fun i : Fin m ↦ y i * (((A i j : ℚ) : ℝ)))
      (p := fun i : Fin m ↦ i ∈ α) <| by
        intro i _ hi_ne
        by_contra hi_active
        have hy_zero : y i = 0 := hzero i hi_active
        apply hi_ne
        simp [hy_zero]
  have hsubtype :
      (∑ i : α, y i.1 * (((A i.1 j : ℚ) : ℝ))) =
        Finset.sum (Finset.univ.filter (fun i : Fin m ↦ i ∈ α))
          (fun i ↦ y i * (((A i j : ℚ) : ℝ))) := by
    -- Rewrite the filtered active-row sum as a sum over the active-row subtype itself.
    simpa using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m ↦ i ∈ α)
        (f := fun i : Fin m ↦ y i * (((A i j : ℚ) : ℝ))))
  have hactive :
      (((fun i : α ↦ y i.1) ᵥ*
        Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) =
        ∑ i : α, y i.1 * (((A i.1 j : ℚ) : ℝ)) := by
    -- Expanding the active-row vecMul gives the subtype-indexed sum directly.
    rfl
  have hcollapse :
      ((y ᵥ* (A.map (Rat.castHom ℝ))) j) =
        (((fun i : α ↦ y i.1) ᵥ*
          Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) := by
    calc
      ((y ᵥ* (A.map (Rat.castHom ℝ))) j)
          = ∑ i : Fin m, y i * (((A i j : ℚ) : ℝ)) := hfull
      _ = Finset.sum (Finset.univ.filter (fun i : Fin m ↦ i ∈ α))
            (fun i ↦ y i * (((A i j : ℚ) : ℝ))) := hfilter.symm
      _ = ∑ i : α, y i.1 * (((A i.1 j : ℚ) : ℝ)) := hsubtype.symm
      _ = (((fun i : α ↦ y i.1) ᵥ*
            Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) := hactive.symm
  exact hcollapse

/-- Helper for Theorem 4.60: a `Fin`-indexed nonnegative rational combination of vectors from a
family lies in the cone generated by that family. -/
lemma mem_hull_of_equivFin_nonnegative_family
    {q : ℕ}
    (r : Fin q → Fin n → ℚ)
    (coeff : Fin q → ℚ)
    (v : Fin n → ℚ)
    (hcoeff_nonneg : ∀ k, 0 ≤ coeff k)
    (hv : v = ∑ k : Fin q, coeff k • r k) :
    v ∈
      (PointedCone.hull ℚ (Set.range r) : Set (Fin n → ℚ)) := by
  -- Package the given finite conic-combination data directly through `mem_hull_iff`.
  refine (mem_hull_iff).2 ?_
  refine ⟨q, r, ?_, coeff, hcoeff_nonneg, hv⟩
  · intro k
    exact ⟨k, rfl⟩

/-- Helper for Theorem 4.60: a dual multiplier whose positive support is active on `F` restricts
to a real nonnegative solution on the active-row system of `F`. -/
lemma restricted_real_solution_on_active_rows
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    (F : Set (Fin n → ℝ))
    {y : Fin m → ℝ}
    (hy : y ∈ rational_dual_feasible_region A c)
    (hsupport :
      ∀ ⦃i : Fin m⦄, 0 < y i → i ∈ RationalMatrixPolyhedron.activeRowIndices A b F) :
    ∃ yF : RationalMatrixPolyhedron.activeRowIndices A b F → ℝ,
      yF ᵥ* Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ) =
          (fun j ↦ (c j : ℝ)) ∧
        0 ≤ yF := by
  -- Route correction: the shared subtype-to-`Fin` normalization is now isolated in
  -- `active_rows_real_vecMul_coordinate_eq_equivFin_sum`; the remaining work is the coordinatewise
  -- collapse from the full-row equation to the active-row subsystem after zeroing inactive rows.
  rcases (mem_rational_dual_feasible_region_iff.mp hy) with ⟨hy_row, hy_nonneg⟩
  let α := RationalMatrixPolyhedron.activeRowIndices A b F
  let yF : α → ℝ := fun i ↦ y i.1
  refine ⟨yF, ?_, ?_⟩
  · -- Compare the active-row vecMul and the full dual row equation against the same `Fin`-indexed
    -- active-row subsystem after the inactive coordinates are forced to vanish.
    ext j
    have hzero : ∀ i : Fin m, i ∉ α → y i = 0 := by
      intro i hi
      exact dual_coordinate_eq_zero_of_not_active A b F hy_nonneg hsupport hi
    calc
      (yF ᵥ* Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j
          = ((y ᵥ* (A.map (Rat.castHom ℝ))) j) := by
            symm
            simpa [α] using
              (full_dual_row_eq_active_rows_reindexed_of_zero_off_active
                (A := A) (b := b) (F := F) hzero j)
      _ = (c j : ℝ) := congrFun hy_row j
  · -- Restricting a nonnegative full multiplier preserves nonnegativity on the active subsystem.
    change ∀ i, 0 ≤ yF i
    intro i
    simpa [yF] using hy_nonneg i.1

/-- Helper for Theorem 4.60: a rational nonnegative solution to the active-row system gives cone
membership of the objective vector in the rational cone of the active rows. -/
lemma mem_hull_active_rows_of_nonnegative_solution
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    (F : Set (Fin n → ℝ))
    {q : RationalMatrixPolyhedron.activeRowIndices A b F → ℚ}
    (hq_row :
      q ᵥ* RationalMatrixPolyhedron.activeRows A b F = fun j ↦ (c j : ℚ))
    (hq_nonneg : 0 ≤ q) :
    (fun j ↦ (c j : ℚ)) ∈
      (PointedCone.hull ℚ (Set.range (RationalMatrixPolyhedron.activeRows A b F)) :
        Set (Fin n → ℚ)) := by
  let α := RationalMatrixPolyhedron.activeRowIndices A b F
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let r : Fin (Fintype.card α) → Fin n → ℚ :=
    fun k ↦ RationalMatrixPolyhedron.activeRows A b F (e.symm k)
  let coeff : Fin (Fintype.card α) → ℚ := fun k ↦ q (e.symm k)
  have hrange :
      Set.range r = Set.range (RationalMatrixPolyhedron.activeRows A b F) := by
    ext v
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨e.symm k, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp [r]⟩
  rw [← hrange]
  refine mem_hull_of_equivFin_nonnegative_family r coeff (fun j ↦ (c j : ℚ)) ?_ ?_
  · -- Reindexed coefficients preserve the original nonnegativity hypothesis.
    intro k
    exact hq_nonneg (e.symm k)
  · -- Evaluate the active-row equation coordinatewise and transport its subtype sum to `Fin`.
    ext j
    have hj : (q ᵥ* RationalMatrixPolyhedron.activeRows A b F) j = (c j : ℚ) := congrFun hq_row j
    calc
      (fun t ↦ (c t : ℚ)) j = (q ᵥ* RationalMatrixPolyhedron.activeRows A b F) j := by
        simpa using hj.symm
      _ = ∑ i : α, q i * RationalMatrixPolyhedron.activeRows A b F i j := by
            rfl
      _ = ∑ k : Fin (Fintype.card α), q (e.symm k) *
            RationalMatrixPolyhedron.activeRows A b F (e.symm k) j := by
            exact Fintype.sum_equiv e
              (fun i : α ↦ q i * RationalMatrixPolyhedron.activeRows A b F i j)
              (fun k : Fin (Fintype.card α) ↦
                q (e.symm k) * RationalMatrixPolyhedron.activeRows A b F (e.symm k) j)
              (fun i ↦ by simp)
      _ = (∑ k : Fin (Fintype.card α), coeff k • r k) j := by
            simp [coeff, r, Finset.sum_apply, Pi.smul_apply]

/-- Helper for Theorem 4.60: if a dual-feasible vector attains the same objective value on every
point of a face, then every positive dual coordinate comes from a row active along the whole face.
-/
lemma positive_dual_support_subset_activeRowIndices
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    (F : Set (Fin n → ℝ))
    {y : Fin m → ℝ}
    (hy : y ∈ rational_dual_feasible_region A c)
    (hF_subset : F ⊆ rational_matrix_polyhedron A b)
    (hvalue :
      ∀ ⦃x : Fin n → ℝ⦄, x ∈ F →
        (fun j ↦ (c j : ℝ)) ⬝ᵥ x = y ⬝ᵥ (fun i ↦ (b i : ℝ))) :
    ∀ ⦃i : Fin m⦄, 0 < y i → i ∈ RationalMatrixPolyhedron.activeRowIndices A b F := by
  rcases (mem_rational_dual_feasible_region_iff.mp hy) with ⟨hy_row, hy_nonneg⟩
  intro i hi x hxF
  have hxP : x ∈ rational_matrix_polyhedron A b := hF_subset hxF
  have hx_feas :
      (A.map (Rat.castHom ℝ)) *ᵥ x ≤ fun k ↦ (b k : ℝ) :=
    (mem_rational_matrix_polyhedron A b x).mp hxP
  -- Compare the primal and dual values at `x`; equality forces the weighted slack sum to vanish.
  have hslack_dot_zero :
      y ⬝ᵥ ((fun k ↦ (b k : ℝ)) - (A.map (Rat.castHom ℝ)) *ᵥ x) = 0 := by
    calc
      y ⬝ᵥ ((fun k ↦ (b k : ℝ)) - (A.map (Rat.castHom ℝ)) *ᵥ x)
          = y ⬝ᵥ (fun k ↦ (b k : ℝ)) -
              y ⬝ᵥ ((A.map (Rat.castHom ℝ)) *ᵥ x) := by
              rw [dotProduct_sub]
      _ = y ⬝ᵥ (fun k ↦ (b k : ℝ)) - (fun j ↦ (c j : ℝ)) ⬝ᵥ x := by
            rw [Matrix.dotProduct_mulVec, hy_row]
      _ = 0 := by
            calc
              y ⬝ᵥ (fun k ↦ (b k : ℝ)) - (fun j ↦ (c j : ℝ)) ⬝ᵥ x
                  = y ⬝ᵥ (fun k ↦ (b k : ℝ)) - (y ⬝ᵥ (fun i ↦ (b i : ℝ))) := by
                      rw [← hvalue hxF]
              _ = 0 := by ring
  have hsum_zero :
      ∑ k : Fin m, y k * (((fun t ↦ (b t : ℝ)) - (A.map (Rat.castHom ℝ)) *ᵥ x) k) = 0 := by
    simpa [dotProduct] using hslack_dot_zero
  have hterm_zero :
      y i * (((fun t ↦ (b t : ℝ)) - (A.map (Rat.castHom ℝ)) *ᵥ x) i) = 0 := by
    have hzero_on_univ :
        ∀ k ∈ (Finset.univ : Finset (Fin m)),
          y k * (((fun t ↦ (b t : ℝ)) - (A.map (Rat.castHom ℝ)) *ᵥ x) k) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ ↦ mul_nonneg (hy_nonneg k) (sub_nonneg.mpr (hx_feas k)))).1 hsum_zero
    exact hzero_on_univ i (Finset.mem_univ i)
  have hslack_zero :
      ((fun t ↦ (b t : ℝ)) - (A.map (Rat.castHom ℝ)) *ᵥ x) i = 0 := by
    exact (mul_eq_zero.mp hterm_zero).resolve_left (ne_of_gt hi)
  exact (sub_eq_zero.mp hslack_zero).symm

/-- Helper for Theorem 4.60: every active row is tight on every point of the face. -/
lemma active_rows_mulVec_eq_face_rhs
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (F : Set (Fin n → ℝ))
    {xStar : Fin n → ℝ}
    (hxStarF : xStar ∈ F) :
    (Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) *ᵥ xStar =
      (fun i : RationalMatrixPolyhedron.activeRowIndices A b F ↦ (b i.1 : ℝ)) := by
  -- Membership in the active-row index set is exactly the face equality needed here.
  ext i
  simpa [RationalMatrixPolyhedron.activeRows] using i.2 hxStarF

/-- Helper for Theorem 4.60: casting a natural-valued `Finsupp` combination of active rows to
`ℝ` gives the corresponding active-row dual equation. -/
lemma active_rows_real_vecMul_eq_of_nat_finsupp_sum
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    (F : Set (Fin n → ℝ))
    {u : RationalMatrixPolyhedron.activeRowIndices A b F →₀ ℕ}
    (hu :
      (fun j ↦ (c j : ℚ)) =
        u.sum (fun i k ↦ k • RationalMatrixPolyhedron.activeRows A b F i)) :
    (fun i : RationalMatrixPolyhedron.activeRowIndices A b F ↦ (u i : ℝ)) ᵥ*
        Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ) =
      (fun j ↦ (c j : ℝ)) := by
  -- Evaluate both sides coordinatewise and rewrite the active-row `vecMul` as the same
  -- finite-support sum appearing in the witness `hu`.
  ext j
  have hqj :
      (((fun i : RationalMatrixPolyhedron.activeRowIndices A b F ↦ (u i : ℚ)) ᵥ*
          RationalMatrixPolyhedron.activeRows A b F) j) = (c j : ℚ) := by
    calc
      (((fun i : RationalMatrixPolyhedron.activeRowIndices A b F ↦ (u i : ℚ)) ᵥ*
          RationalMatrixPolyhedron.activeRows A b F) j)
          = ∑ i : RationalMatrixPolyhedron.activeRowIndices A b F,
              (u i : ℚ) * RationalMatrixPolyhedron.activeRows A b F i j := by
              simp [Matrix.vecMul, dotProduct]
      _ = u.sum
            (fun i k ↦ (k : ℚ) * RationalMatrixPolyhedron.activeRows A b F i j) := by
            symm
            rw [Finsupp.sum_fintype]
            intro i
            simp
      _ = (u.sum (fun i k ↦ k • RationalMatrixPolyhedron.activeRows A b F i)) j := by
            simpa [Finsupp.sum, Pi.smul_apply, smul_eq_mul]
      _ = (c j : ℚ) := by
            simpa using (congrFun hu j).symm
  have hqjR :
      ((((fun i : RationalMatrixPolyhedron.activeRowIndices A b F ↦ (u i : ℚ)) ᵥ*
          RationalMatrixPolyhedron.activeRows A b F) j : ℚ) : ℝ) = (c j : ℝ) := by
    exact_mod_cast hqj
  simpa [Matrix.vecMul, dotProduct] using hqjR

/-- Helper for Theorem 4.60: a vector supported on the active rows has the same dual objective
whether computed in the full row space or on the active-row subtype. -/
lemma zero_extension_dotProduct_eq_subtype
    (α : Set (Fin m))
    {y w : Fin m → ℝ}
    (hzero : ∀ i : Fin m, i ∉ α → y i = 0) :
    y ⬝ᵥ w = (fun i : α ↦ y i.1) ⬝ᵥ (fun i : α ↦ w i.1) := by
  classical
  -- Pin the active-row subtype to the canonical finite instance used by the statement.
  letI : Fintype α := CategoryTheory.FinCategory.fintypeObj
  have hfilter :
      Finset.sum (Finset.univ.filter (fun i : Fin m ↦ i ∈ α)) (fun i ↦ y i * w i) =
        ∑ i : Fin m, y i * w i := by
    -- Inactive rows contribute zero, so the full dot product collapses to the active filter.
    exact Finset.sum_filter_of_ne (s := Finset.univ)
      (f := fun i : Fin m ↦ y i * w i)
      (p := fun i : Fin m ↦ i ∈ α) <| by
        intro i _ hi_ne
        by_contra hi_active
        have hy_zero : y i = 0 := hzero i hi_active
        apply hi_ne
        simp [hy_zero]
  have hsubtype :
      (∑ i : α, y i.1 * w i.1) =
        Finset.sum (Finset.univ.filter (fun i : Fin m ↦ i ∈ α))
          (fun i ↦ y i * w i) := by
    -- Rewrite the active filter as a sum over the active-row subtype itself.
    simpa using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m ↦ i ∈ α)
        (f := fun i : Fin m ↦ y i * w i))
  have hdot :
      Finset.sum (Finset.univ.filter (fun i : Fin m ↦ i ∈ α))
        (fun i ↦ y i * w i) =
      (fun i : α ↦ y i.1) ⬝ᵥ (fun i : α ↦ w i.1) := by
    simpa [dotProduct] using hsubtype.symm
  have hfull :
      y ⬝ᵥ w =
        Finset.sum (Finset.univ.filter (fun i : Fin m ↦ i ∈ α))
          (fun i ↦ y i * w i) := by
    calc
      y ⬝ᵥ w = ∑ i : Fin m, y i * w i := by
        simp [dotProduct]
      _ = Finset.sum (Finset.univ.filter (fun i : Fin m ↦ i ∈ α))
            (fun i ↦ y i * w i) := hfilter.symm
  exact hfull.trans hdot

/-- Helper for Theorem 4.60: zero-extending an active-row natural combination produces the full
dual row equation. -/
lemma zero_extension_row_eq_of_active_finsupp_sum
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    (F : Set (Fin n → ℝ))
    {u : RationalMatrixPolyhedron.activeRowIndices A b F →₀ ℕ}
    {yStar : Fin m → ℝ}
    (hzero :
      ∀ i : Fin m,
        i ∉ RationalMatrixPolyhedron.activeRowIndices A b F → yStar i = 0)
    (hyStar_restrict :
      (fun i : RationalMatrixPolyhedron.activeRowIndices A b F ↦ yStar i.1) =
        fun i : RationalMatrixPolyhedron.activeRowIndices A b F ↦ (u i : ℝ))
    (hu :
      (fun j ↦ (c j : ℚ)) =
        u.sum (fun i k ↦ k • RationalMatrixPolyhedron.activeRows A b F i)) :
    yStar ᵥ* (A.map (Rat.castHom ℝ)) = (fun j ↦ (c j : ℝ)) := by
  let α := RationalMatrixPolyhedron.activeRowIndices A b F
  have hactive_row :
      (fun i : α ↦ (u i : ℝ)) ᵥ*
          Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ) =
        (fun j ↦ (c j : ℝ)) := by
    simpa [α] using active_rows_real_vecMul_eq_of_nat_finsupp_sum
      (A := A) (b := b) (c := c) (F := F) hu
  -- Collapse the full-row equation to the active subsystem and then use the casted witness `hu`.
  ext j
  calc
    ((yStar ᵥ* (A.map (Rat.castHom ℝ))) j)
        = (((fun i : α ↦ yStar i.1) ᵥ*
            Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) := by
            simpa [α] using
              (full_dual_row_eq_active_rows_reindexed_of_zero_off_active
                (A := A) (b := b) (F := F) (by
                  simpa [α] using hzero) j)
    _ = (((fun i : α ↦ (u i : ℝ)) ᵥ*
          Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) := by
          rw [hyStar_restrict]
    _ = (c j : ℝ) := congrFun hactive_row j

/-- Helper for Theorem 4.60: the zero extension of an active-row natural combination has dual
objective equal to the face value at any point of the face. -/
lemma zero_extension_dual_objective_eq_face_value
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    (F : Set (Fin n → ℝ))
    {xStar : Fin n → ℝ}
    (hxStarF : xStar ∈ F)
    {u : RationalMatrixPolyhedron.activeRowIndices A b F →₀ ℕ}
    {yStar : Fin m → ℝ}
    (hzero :
      ∀ i : Fin m,
        i ∉ RationalMatrixPolyhedron.activeRowIndices A b F → yStar i = 0)
    (hyStar_restrict :
      (fun i : RationalMatrixPolyhedron.activeRowIndices A b F ↦ yStar i.1) =
        fun i : RationalMatrixPolyhedron.activeRowIndices A b F ↦ (u i : ℝ))
    (hu :
      (fun j ↦ (c j : ℚ)) =
        u.sum (fun i k ↦ k • RationalMatrixPolyhedron.activeRows A b F i)) :
    yStar ⬝ᵥ (fun i ↦ (b i : ℝ)) = (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar := by
  let α := RationalMatrixPolyhedron.activeRowIndices A b F
  have hactive_rows_eval :
      (Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) *ᵥ xStar =
        (fun i : α ↦ (b i.1 : ℝ)) := by
    simpa [α] using active_rows_mulVec_eq_face_rhs (A := A) (b := b) (F := F) hxStarF
  have hactive_row :
      (fun i : α ↦ (u i : ℝ)) ᵥ*
          Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ) =
        (fun j ↦ (c j : ℝ)) := by
    simpa [α] using active_rows_real_vecMul_eq_of_nat_finsupp_sum
      (A := A) (b := b) (c := c) (F := F) hu
  -- Rewrite the full dual objective to the active subtype, evaluate the active rows on `xStar`,
  -- and finish with the casted active-row equation.
  calc
    yStar ⬝ᵥ (fun i ↦ (b i : ℝ))
        = (fun i : α ↦ yStar i.1) ⬝ᵥ (fun i : α ↦ (b i.1 : ℝ)) := by
            simpa [α] using
              zero_extension_dotProduct_eq_subtype
                (α := α) (y := yStar) (w := fun i ↦ (b i : ℝ)) (by
                  simpa [α] using hzero)
    _ = (fun i : α ↦ (u i : ℝ)) ⬝ᵥ (fun i : α ↦ (b i.1 : ℝ)) := by
          rw [hyStar_restrict]
    _ = (fun i : α ↦ (u i : ℝ)) ⬝ᵥ
          ((Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) *ᵥ xStar) := by
          rw [hactive_rows_eval]
    _ = (((fun i : α ↦ (u i : ℝ)) ᵥ*
          Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) ⬝ᵥ xStar) := by
          rw [Matrix.dotProduct_mulVec]
    _ = (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar := by
          rw [hactive_row]

/-- Helper for Theorem 4.60: an integral active-row combination extends by zero to an integral
optimal solution of the full dual system. -/
lemma active_row_nat_combination_gives_integral_dual_optimum
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    (F : Set (Fin n → ℝ))
    {xStar : Fin n → ℝ}
    (hxStarP : xStar ∈ rational_matrix_polyhedron A b)
    (hxStarF : xStar ∈ F)
    {u : RationalMatrixPolyhedron.activeRowIndices A b F →₀ ℕ}
    (hu :
      (fun j ↦ (c j : ℚ)) =
        u.sum (fun i k ↦ k • RationalMatrixPolyhedron.activeRows A b F i)) :
    rational_dual_has_integral_optimal_solution A b c := by
  classical
  let α := RationalMatrixPolyhedron.activeRowIndices A b F
  let yStar : Fin m → ℝ := fun i ↦ if hi : i ∈ α then (u ⟨i, hi⟩ : ℝ) else 0
  have hzero : ∀ i : Fin m, i ∉ α → yStar i = 0 := by
    intro i hi
    simp [yStar, hi]
  have hyStar_restrict :
      (fun i : α ↦ yStar i.1) = fun i : α ↦ (u i : ℝ) := by
    -- On an active row, the zero extension reads back the original coefficient.
    funext i
    simp [yStar]
  have hyStar_feasible : yStar ∈ rational_dual_feasible_region A c := by
    -- The zero extension satisfies the full dual row equation and is coordinatewise nonnegative.
    refine (mem_rational_dual_feasible_region_iff).2 ?_
    refine ⟨?_, ?_⟩
    · simpa using zero_extension_row_eq_of_active_finsupp_sum
        (A := A) (b := b) (c := c) (F := F) (yStar := yStar) hzero hyStar_restrict hu
    · intro i
      by_cases hi : i ∈ α
      · simp [yStar, hi]
      · simp [yStar, hi]
  have hyStar_integer : yStar ∈ integerVectors m := by
    -- Every active coordinate is a natural number, while the inactive coordinates are zero.
    rw [mem_integerVectors_iff_forall]
    intro i
    by_cases hi : i ∈ α
    · refine ⟨Int.ofNat (u ⟨i, hi⟩), ?_⟩
      simp [yStar, hi]
    · refine ⟨0, ?_⟩
      simp [yStar, hi]
  have hyStar_value :
      yStar ⬝ᵥ (fun i ↦ (b i : ℝ)) = (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar := by
    -- On the face, the active rows evaluate to `b`, so the zero-extended dual objective matches
    -- the primal objective value at `xStar`.
    simpa using zero_extension_dual_objective_eq_face_value
      (A := A) (b := b) (c := c) (F := F) (xStar := xStar) hxStarF
      (yStar := yStar) hzero hyStar_restrict hu
  refine ⟨yStar, hyStar_feasible, hyStar_integer, ?_⟩
  refine ⟨⟨yStar, hyStar_feasible, rfl⟩, ?_⟩
  intro r hr
  rcases hr with ⟨y, hy_feasible, rfl⟩
  rcases (mem_rational_dual_feasible_region_iff.mp hy_feasible) with ⟨hy_row, hy_nonneg⟩
  have hxStar_primal :
      xStar ∈ primal_feasible_region (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) := by
    simpa [primal_feasible_region, rational_matrix_polyhedron] using hxStarP
  have hy_dual :
      y ∈ dual_feasible_region (A.map (Rat.castHom ℝ)) (fun j ↦ (c j : ℝ)) := by
    exact (mem_dual_feasible_region_iff
      (A.map (Rat.castHom ℝ)) (fun j ↦ (c j : ℝ)) y).2 ⟨hy_row, hy_nonneg⟩
  -- Weak duality gives the lower bound for every feasible dual objective value.
  calc
    yStar ⬝ᵥ (fun i ↦ (b i : ℝ)) = (fun j ↦ (c j : ℝ)) ⬝ᵥ xStar := hyStar_value
    _ ≤ y ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
          exact weak_duality_feasible_pair
            (A := A.map (Rat.castHom ℝ))
            (b := fun i ↦ (b i : ℝ))
            (c := fun j ↦ (c j : ℝ))
            hxStar_primal hy_dual

/-- Helper for Theorem 4.60: cone membership in the active rows can be rewritten as a
nonnegative coefficient function on the active-row subtype itself. -/
lemma exists_nonnegative_active_rows_solution_of_mem_hull
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    (F : Set (Fin n → ℝ))
    (hc :
      (fun j ↦ (c j : ℚ)) ∈
        (PointedCone.hull ℚ (Set.range (RationalMatrixPolyhedron.activeRows A b F)) :
          Set (Fin n → ℚ))) :
    ∃ q : RationalMatrixPolyhedron.activeRowIndices A b F → ℚ,
      q ᵥ* RationalMatrixPolyhedron.activeRows A b F = (fun j ↦ (c j : ℚ)) ∧
        0 ≤ q := by
  classical
  let α := RationalMatrixPolyhedron.activeRowIndices A b F
  letI : Fintype α := CategoryTheory.FinCategory.fintypeObj
  rcases (mem_hull_iff.mp hc) with ⟨s, r, hr_mem, coeff, hcoeff_nonneg, hc_eq⟩
  let idx : Fin s → α := fun k ↦ Classical.choose (hr_mem k)
  have hidx : ∀ k : Fin s, RationalMatrixPolyhedron.activeRows A b F (idx k) = r k := by
    intro k
    exact Classical.choose_spec (hr_mem k)
  let q : α → ℚ := fun i ↦ ∑ k : Fin s, if idx k = i then coeff k else 0
  refine ⟨q, ?_, ?_⟩
  · -- Aggregate the original finite conic witness by the actual active-row index it selects.
    ext j
    calc
      (q ᵥ* RationalMatrixPolyhedron.activeRows A b F) j
          = ∑ i : α, q i * RationalMatrixPolyhedron.activeRows A b F i j := by
              rfl
      _ = ∑ i : α,
            (∑ k : Fin s, if idx k = i then coeff k else 0) *
              RationalMatrixPolyhedron.activeRows A b F i j := by
              simp [q]
      _ = ∑ i : α, ∑ k : Fin s,
            (if idx k = i then coeff k else 0) *
              RationalMatrixPolyhedron.activeRows A b F i j := by
              simp_rw [Finset.sum_mul]
      _ = ∑ k : Fin s, ∑ i : α,
            (if idx k = i then coeff k else 0) *
              RationalMatrixPolyhedron.activeRows A b F i j := by
              rw [Finset.sum_comm]
      _ = ∑ k : Fin s, coeff k * r k j := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simpa [hidx k] using
              (by
                simp :
                  (∑ i : α,
                    (if idx k = i then coeff k else 0) *
                      RationalMatrixPolyhedron.activeRows A b F i j) =
                    coeff k * RationalMatrixPolyhedron.activeRows A b F (idx k) j)
      _ = (∑ k : Fin s, coeff k • r k) j := by
            simp [Finset.sum_apply, Pi.smul_apply]
      _ = (c j : ℚ) := by
            simpa using congrFun hc_eq.symm j
  · -- Each aggregated coordinate is a sum of nonnegative coefficients.
    intro i
    simp [q]
    exact Finset.sum_nonneg fun k _ ↦ by
      by_cases hk : idx k = i
      · simp [hk, hcoeff_nonneg k]
      · simp [hk]

/-- Helper for Theorem 4.60: a nonnegative active-row solution turns any face point into a finite
primal optimum for the corresponding integral objective. -/
lemma rational_primal_has_finite_optimum_of_active_rows_solution
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    (F : Set (Fin n → ℝ))
    {xStar : Fin n → ℝ}
    (hxStarF : xStar ∈ F)
    (hF_subset : F ⊆ rational_matrix_polyhedron A b)
    {q : RationalMatrixPolyhedron.activeRowIndices A b F → ℚ}
    (hq_row :
      q ᵥ* RationalMatrixPolyhedron.activeRows A b F = fun j ↦ (c j : ℚ))
    (hq_nonneg : 0 ≤ q) :
    rational_primal_has_finite_optimum A b c := by
  classical
  let α := RationalMatrixPolyhedron.activeRowIndices A b F
  letI : Fintype α := CategoryTheory.FinCategory.fintypeObj
  let y0 : Fin m → ℝ := fun i ↦ if hi : i ∈ α then (q ⟨i, hi⟩ : ℝ) else 0
  let cR : Fin n → ℝ := fun j ↦ (c j : ℝ)
  have hxStarP : xStar ∈ rational_matrix_polyhedron A b := hF_subset hxStarF
  have hzero : ∀ i : Fin m, i ∉ α → y0 i = 0 := by
    intro i hi
    simp [y0, hi]
  have hy0_restrict :
      (fun i : α ↦ y0 i.1) = fun i : α ↦ (q i : ℝ) := by
    -- On active rows, zero extension reads back the original coefficient function.
    funext i
    simp [y0]
  have hq_row_real :
      (fun i : α ↦ (q i : ℝ)) ᵥ*
          Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ) =
        cR := by
    -- Cast the rational active-row equation coordinatewise to `ℝ`.
    ext j
    have hqj :
        (q ᵥ* RationalMatrixPolyhedron.activeRows A b F) j = (c j : ℚ) := congrFun hq_row j
    have hqjR :
        ((((q ᵥ* RationalMatrixPolyhedron.activeRows A b F) j : ℚ) : ℝ)) = (c j : ℝ) := by
      exact_mod_cast hqj
    simpa [cR, Matrix.vecMul, dotProduct] using hqjR
  have hy0_feasible : y0 ∈ rational_dual_feasible_region A c := by
    -- The zero extension satisfies the full dual row equation and preserves nonnegativity.
    refine (mem_rational_dual_feasible_region_iff).2 ?_
    refine ⟨?_, ?_⟩
    · ext j
      calc
        (y0 ᵥ* (A.map (Rat.castHom ℝ))) j
            = (((fun i : α ↦ y0 i.1) ᵥ*
                Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) := by
                  simpa [α] using
                    (full_dual_row_eq_active_rows_reindexed_of_zero_off_active
                      (A := A) (b := b) (F := F) hzero j)
        _ = (((fun i : α ↦ (q i : ℝ)) ᵥ*
              Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) := by
              rw [hy0_restrict]
        _ = (cR j) := congrFun hq_row_real j
    · intro i
      by_cases hi : i ∈ α
      · simpa [y0, hi] using hq_nonneg ⟨i, hi⟩
      · simp [y0, hi]
  have hy0_dual :
      y0 ∈ dual_feasible_region (A.map (Rat.castHom ℝ)) cR := by
    rcases (mem_rational_dual_feasible_region_iff.mp hy0_feasible) with ⟨hy0_row, hy0_nonneg⟩
    exact (mem_dual_feasible_region_iff (A.map (Rat.castHom ℝ)) cR y0).2
      ⟨hy0_row, hy0_nonneg⟩
  have hy0_value :
      y0 ⬝ᵥ (fun i ↦ (b i : ℝ)) = cR ⬝ᵥ xStar := by
    have hactive_rows_eval :
        (Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) *ᵥ xStar =
          (fun i : α ↦ (b i.1 : ℝ)) := by
      simpa [α] using active_rows_mulVec_eq_face_rhs (A := A) (b := b) (F := F) hxStarF
    -- Evaluate the active rows at `xStar`, then collapse the zero extension back to the face.
    calc
      y0 ⬝ᵥ (fun i ↦ (b i : ℝ))
          = (fun i : α ↦ y0 i.1) ⬝ᵥ (fun i : α ↦ (b i.1 : ℝ)) := by
              simpa [α] using
                zero_extension_dotProduct_eq_subtype
                  (α := α) (y := y0) (w := fun i ↦ (b i : ℝ)) hzero
      _ = (fun i : α ↦ (q i : ℝ)) ⬝ᵥ (fun i : α ↦ (b i.1 : ℝ)) := by
            rw [hy0_restrict]
      _ = (fun i : α ↦ (q i : ℝ)) ⬝ᵥ
            ((Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) *ᵥ xStar) := by
            rw [hactive_rows_eval]
      _ = (((fun i : α ↦ (q i : ℝ)) ᵥ*
            Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) ⬝ᵥ xStar) := by
            rw [Matrix.dotProduct_mulVec]
      _ = cR ⬝ᵥ xStar := by
            rw [hq_row_real]
  refine ⟨xStar, hxStarP, ?_⟩
  refine ⟨⟨xStar, hxStarP, rfl⟩, ?_⟩
  intro r hr
  rcases hr with ⟨x, hxP, rfl⟩
  have hx_primal :
      x ∈ primal_feasible_region (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) := by
    simpa [primal_feasible_region, rational_matrix_polyhedron] using hxP
  -- Weak duality against the zero extension shows that `xStar` attains the greatest value.
  calc
    cR ⬝ᵥ x ≤ y0 ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
      exact weak_duality_feasible_pair
        (A := A.map (Rat.castHom ℝ))
        (b := fun i ↦ (b i : ℝ))
        (c := cR)
        hx_primal hy0_dual
    _ = cR ⬝ᵥ xStar := hy0_value

/-- Helper for Theorem 4.60: an integral dual optimum whose value is constant on a face gives an
`ℕ`-valued active-row `Finsupp` witness for that objective. -/
lemma active_row_nat_finsupp_of_integral_dual_value_on_face
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℤ)
    (F : Set (Fin n → ℝ))
    {y : Fin m → ℝ}
    (hy : y ∈ rational_dual_feasible_region A c)
    (hy_integer : y ∈ integerVectors m)
    (hF_subset : F ⊆ rational_matrix_polyhedron A b)
    (hvalue :
      ∀ ⦃x : Fin n → ℝ⦄, x ∈ F →
        (fun j ↦ (c j : ℝ)) ⬝ᵥ x = y ⬝ᵥ (fun i ↦ (b i : ℝ))) :
    ∃ u : RationalMatrixPolyhedron.activeRowIndices A b F →₀ ℕ,
      (fun j ↦ (c j : ℚ)) =
        u.sum (fun i k ↦ k • RationalMatrixPolyhedron.activeRows A b F i) := by
  classical
  let α := RationalMatrixPolyhedron.activeRowIndices A b F
  letI : Fintype α := CategoryTheory.FinCategory.fintypeObj
  rcases (mem_rational_dual_feasible_region_iff.mp hy) with ⟨hy_row, hy_nonneg⟩
  obtain ⟨z, hz⟩ := (mem_integerVectors_iff.mp hy_integer)
  have hsupport :
      ∀ ⦃i : Fin m⦄, 0 < y i → i ∈ α :=
    positive_dual_support_subset_activeRowIndices
      (A := A) (b := b) (c := c) (F := F) hy hF_subset hvalue
  have hzero : ∀ i : Fin m, i ∉ α → y i = 0 := by
    intro i hi
    exact dual_coordinate_eq_zero_of_not_active A b F hy_nonneg hsupport hi
  let u : α →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i : α ↦ Int.toNat (z i.1))
  have hy_restrict :
      (fun i : α ↦ y i.1) = fun i : α ↦ (u i : ℝ) := by
    -- Integer-valued nonnegative coordinates become natural-number coefficients on the face.
    funext i
    have hyi_eq : y i.1 = (z i.1 : ℝ) := by
      simpa [Function.comp] using congrFun hz i.1
    have hzi_nonneg : 0 ≤ z i.1 := by
      have hyi_nonneg : 0 ≤ y i.1 := hy_nonneg i.1
      rw [hyi_eq] at hyi_nonneg
      exact_mod_cast hyi_nonneg
    have htoNat_cast : ((Int.toNat (z i.1) : ℕ) : ℝ) = (z i.1 : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hzi_nonneg)
    calc
      y i.1 = (z i.1 : ℝ) := hyi_eq
      _ = (Int.toNat (z i.1) : ℝ) := by symm; exact htoNat_cast
      _ = (u i : ℝ) := by simp [u]
  have hy_row_active :
      (fun i : α ↦ y i.1) ᵥ*
          Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ) =
        (fun j ↦ (c j : ℝ)) := by
    -- Zero off the inactive rows and then collapse the full dual system to the active subsystem.
    ext j
    calc
      ((fun i : α ↦ y i.1) ᵥ*
          Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j
          = (y ᵥ* (A.map (Rat.castHom ℝ))) j := by
              symm
              simpa [α] using
                (full_dual_row_eq_active_rows_reindexed_of_zero_off_active
                  (A := A) (b := b) (F := F) hzero j)
      _ = (c j : ℝ) := congrFun hy_row j
  have hu_row_real :
      (fun i : α ↦ (u i : ℝ)) ᵥ*
          Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ) =
        (fun j ↦ (c j : ℝ)) := by
    rw [← hy_restrict]
    exact hy_row_active
  refine ⟨u, ?_⟩
  ext j
  have hujR :
      ((((fun i : α ↦ (u i : ℚ)) ᵥ* RationalMatrixPolyhedron.activeRows A b F) j : ℚ) : ℝ) =
        (c j : ℝ) := by
    calc
      ((((fun i : α ↦ (u i : ℚ)) ᵥ* RationalMatrixPolyhedron.activeRows A b F) j : ℚ) : ℝ)
          = (((fun i : α ↦ (u i : ℝ)) ᵥ*
              Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) := by
                simp [Matrix.vecMul, dotProduct]
      _ = (c j : ℝ) := congrFun hu_row_real j
  have huj :
      ((fun i : α ↦ (u i : ℚ)) ᵥ* RationalMatrixPolyhedron.activeRows A b F) j = (c j : ℚ) := by
    exact_mod_cast hujR
  calc
    (fun t ↦ (c t : ℚ)) j
        = ((fun i : α ↦ (u i : ℚ)) ᵥ* RationalMatrixPolyhedron.activeRows A b F) j := by
            simpa using huj.symm
    _ = ∑ i : α, (u i : ℚ) * RationalMatrixPolyhedron.activeRows A b F i j := by
          rfl
    _ = (u.sum (fun i k ↦ k • RationalMatrixPolyhedron.activeRows A b F i)) j := by
          symm
          rw [Finsupp.sum_fintype]
          · simp [Pi.smul_apply, smul_eq_mul]
          · intro i
            simp

/-- Helper for Theorem 4.60: facewise Hilbert bases on all nonempty extreme faces imply total dual
integrality of the system. -/
lemma totally_dual_integral_of_active_rows_form_hilbert_basis_on_each_face
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hfaces :
      ∀ (F : Set (Fin n → ℝ))
        (_hF_nonempty : F.Nonempty)
        (_hF_extreme : IsExtreme ℝ (rational_matrix_polyhedron A b) F),
          RationalFamily.IsHilbertBasis (RationalMatrixPolyhedron.activeRows A b F)) :
    totally_dual_integral A b := by
  intro c hc
  rcases hc with ⟨xStar, hxStarP, hopt⟩
  let cR : Fin n → ℝ := fun j ↦ (c j : ℝ)
  let F := face_set (rational_matrix_polyhedron A b) cR (cR ⬝ᵥ xStar)
  have hF_data :
      F.Nonempty ∧ IsExtreme ℝ (rational_matrix_polyhedron A b) F := by
    -- The optimal equality face is the source-faithful face to which the Hilbert-basis
    -- hypothesis applies.
    simpa [F, cR] using optimal_face_is_extreme A b cR hxStarP hopt
  rcases hF_data with ⟨hF_nonempty, hF_extreme⟩
  have hxStarF : xStar ∈ F := by
    simpa [F, cR] using (mem_face_set_iff).2 ⟨hxStarP, rfl⟩
  have hvalid : is_valid_inequality (rational_matrix_polyhedron A b) cR (cR ⬝ᵥ xStar) := by
    -- The attained primal optimum makes the objective hyperplane through `xStar` valid.
    intro x hxP
    exact hopt.2 ⟨x, hxP, rfl⟩
  obtain ⟨y, hy_nonneg, hy_row, hy_value⟩ :=
    exists_nonneg_row_multiplier_of_attained_valid_rational_inequality
      A b cR (cR ⬝ᵥ xStar) hvalid (by simpa [F, cR] using hF_nonempty)
  have hy : y ∈ rational_dual_feasible_region A c := by
    exact (mem_rational_dual_feasible_region_iff).2 ⟨by simpa [cR] using hy_row, hy_nonneg⟩
  have hvalue_on_face :
      ∀ ⦃x : Fin n → ℝ⦄, x ∈ F →
        (fun j ↦ (c j : ℝ)) ⬝ᵥ x = y ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
    intro x hxF
    have hx_eq : cR ⬝ᵥ x = cR ⬝ᵥ xStar := by
      simpa [F] using (mem_face_set_iff.mp hxF).2
    calc
      (fun j ↦ (c j : ℝ)) ⬝ᵥ x = cR ⬝ᵥ x := by rfl
      _ = cR ⬝ᵥ xStar := hx_eq
      _ = y ⬝ᵥ (fun i ↦ (b i : ℝ)) := hy_value.symm
  have hsupport :
      ∀ ⦃i : Fin m⦄, 0 < y i → i ∈ RationalMatrixPolyhedron.activeRowIndices A b F :=
    positive_dual_support_subset_activeRowIndices
      (A := A) (b := b) (c := c) (F := F) hy hF_extreme.subset hvalue_on_face
  obtain ⟨yF, hyF_row, hyF_nonneg⟩ :=
    restricted_real_solution_on_active_rows (A := A) (b := b) (c := c) (F := F) hy hsupport
  obtain ⟨q, hq_row, hq_nonneg⟩ :=
    exists_rat_nonnegative_solution_of_real_cast_feasible
      (M := RationalMatrixPolyhedron.activeRows A b F)
      (d := fun j ↦ (c j : ℚ))
      ⟨yF, hyF_row, hyF_nonneg⟩
  obtain ⟨u, hu⟩ :=
    hfaces F hF_nonempty hF_extreme c
      (mem_hull_active_rows_of_nonnegative_solution
        (A := A) (b := b) (c := c) (F := F) hq_row hq_nonneg)
  -- Route correction: the reverse implication now stays on the active-row `Finsupp` witness `u`
  -- all the way through the zero-extension closure.
  exact active_row_nat_combination_gives_integral_dual_optimum
    (A := A) (b := b) (c := c) (F := F) hxStarP hxStarF hu

/-- Theorem 4.60. The rational system `A x ≤ b` is totally dual integral if and only if for each
nonempty face `F` of `{x ∈ ℝ^n | A x ≤ b}`, the active-row family is a Hilbert basis. -/
theorem totally_dual_integral_iff_active_rows_form_hilbert_basis_on_each_face
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    totally_dual_integral A b ↔
      ∀ (F : Set (Fin n → ℝ))
        (_hF_nonempty : F.Nonempty)
        (_hF_extreme : IsExtreme ℝ (rational_matrix_polyhedron A b) F),
          RationalFamily.IsHilbertBasis (RationalMatrixPolyhedron.activeRows A b F) := by
  constructor
  · intro hTDI
    intro F hF_nonempty hF_extreme c hc
    classical
    let α := RationalMatrixPolyhedron.activeRowIndices A b F
    letI : Fintype α := CategoryTheory.FinCategory.fintypeObj
    let cR : Fin n → ℝ := fun j ↦ (c j : ℝ)
    obtain ⟨xStar, hxStarF⟩ := hF_nonempty
    have hF_subset : F ⊆ rational_matrix_polyhedron A b := hF_extreme.subset
    obtain ⟨q, hq_row, hq_nonneg⟩ :=
      exists_nonnegative_active_rows_solution_of_mem_hull
        (A := A) (b := b) (c := c) (F := F) hc
    have hfinite :
        rational_primal_has_finite_optimum A b c :=
      rational_primal_has_finite_optimum_of_active_rows_solution
        (A := A) (b := b) (c := c) (F := F) hxStarF hF_subset hq_row hq_nonneg
    obtain ⟨yStar, hyStar, hyStar_integer, hyStar_opt⟩ := hTDI c hfinite
    let y0 : Fin m → ℝ := fun i ↦ if hi : i ∈ α then (q ⟨i, hi⟩ : ℝ) else 0
    have hzero : ∀ i : Fin m, i ∉ α → y0 i = 0 := by
      intro i hi
      simp [y0, hi]
    have hy0_restrict :
        (fun i : α ↦ y0 i.1) = fun i : α ↦ (q i : ℝ) := by
      -- On active rows, the zero extension reads back the original face multiplier.
      funext i
      simp [y0]
    have hq_row_real :
        (fun i : α ↦ (q i : ℝ)) ᵥ*
            Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ) =
          cR := by
      -- Cast the active-row equation from `ℚ` to `ℝ` coordinatewise.
      ext j
      have hqj :
          (q ᵥ* RationalMatrixPolyhedron.activeRows A b F) j = (c j : ℚ) := congrFun hq_row j
      have hqjR :
          ((((q ᵥ* RationalMatrixPolyhedron.activeRows A b F) j : ℚ) : ℝ)) = (c j : ℝ) := by
        exact_mod_cast hqj
      simpa [cR, Matrix.vecMul, dotProduct] using hqjR
    have hy0_feasible : y0 ∈ rational_dual_feasible_region A c := by
      -- The cone witness becomes a full dual-feasible vector by zero extension off the face.
      refine (mem_rational_dual_feasible_region_iff).2 ?_
      refine ⟨?_, ?_⟩
      · ext j
        calc
          (y0 ᵥ* (A.map (Rat.castHom ℝ))) j
              = (((fun i : α ↦ y0 i.1) ᵥ*
                  Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) := by
                    simpa [α] using
                      (full_dual_row_eq_active_rows_reindexed_of_zero_off_active
                        (A := A) (b := b) (F := F) hzero j)
          _ = (((fun i : α ↦ (q i : ℝ)) ᵥ*
                Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) j) := by
                rw [hy0_restrict]
          _ = (cR j) := congrFun hq_row_real j
      · intro i
        by_cases hi : i ∈ α
        · simpa [y0, hi] using hq_nonneg ⟨i, hi⟩
        · simp [y0, hi]
    have hy0_dual :
        y0 ∈ dual_feasible_region (A.map (Rat.castHom ℝ)) cR := by
      rcases (mem_rational_dual_feasible_region_iff.mp hy0_feasible) with ⟨hy0_row, hy0_nonneg⟩
      exact (mem_dual_feasible_region_iff (A.map (Rat.castHom ℝ)) cR y0).2
        ⟨hy0_row, hy0_nonneg⟩
    have hy0_value_on_face :
        ∀ ⦃x : Fin n → ℝ⦄, x ∈ F → cR ⬝ᵥ x = y0 ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
      intro x hxF
      have hactive_rows_eval :
          (Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) *ᵥ x =
            (fun i : α ↦ (b i.1 : ℝ)) := by
        simpa [α] using active_rows_mulVec_eq_face_rhs (A := A) (b := b) (F := F) hxF
      -- Every point of the face satisfies the same active-row equalities, so the dual value is
      -- constant on the whole face.
      calc
        cR ⬝ᵥ x
            = (((fun i : α ↦ (q i : ℝ)) ᵥ*
                Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) ⬝ᵥ x) := by
                  rw [hq_row_real]
        _ = (fun i : α ↦ (q i : ℝ)) ⬝ᵥ
              ((Matrix.map (RationalMatrixPolyhedron.activeRows A b F) (Rat.castHom ℝ)) *ᵥ x) := by
              rw [Matrix.dotProduct_mulVec]
        _ = (fun i : α ↦ (q i : ℝ)) ⬝ᵥ (fun i : α ↦ (b i.1 : ℝ)) := by
              rw [hactive_rows_eval]
        _ = (fun i : α ↦ y0 i.1) ⬝ᵥ (fun i : α ↦ (b i.1 : ℝ)) := by
              rw [hy0_restrict]
        _ = y0 ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
              symm
              simpa [α] using
                zero_extension_dotProduct_eq_subtype
                  (α := α) (y := y0) (w := fun i ↦ (b i : ℝ)) hzero
    have hxStarP : xStar ∈ rational_matrix_polyhedron A b := hF_subset hxStarF
    have hyStar_dual :
        yStar ∈ dual_feasible_region (A.map (Rat.castHom ℝ)) cR := by
      rcases (mem_rational_dual_feasible_region_iff.mp hyStar) with ⟨hyStar_row, hyStar_nonneg⟩
      exact (mem_dual_feasible_region_iff (A.map (Rat.castHom ℝ)) cR yStar).2
        ⟨hyStar_row, hyStar_nonneg⟩
    have hyStar_obj_le : yStar ⬝ᵥ (fun i ↦ (b i : ℝ)) ≤ y0 ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
      exact hyStar_opt.2 ⟨y0, hy0_feasible, rfl⟩
    have hyStar_obj_ge :
        cR ⬝ᵥ xStar ≤ yStar ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
      have hxStar_primal :
          xStar ∈ primal_feasible_region (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) := by
        simpa [primal_feasible_region, rational_matrix_polyhedron] using hxStarP
      exact weak_duality_feasible_pair
        (A := A.map (Rat.castHom ℝ))
        (b := fun i ↦ (b i : ℝ))
        (c := cR)
        hxStar_primal hyStar_dual
    have hy0_value_xStar : cR ⬝ᵥ xStar = y0 ⬝ᵥ (fun i ↦ (b i : ℝ)) :=
      hy0_value_on_face hxStarF
    have hyStar_value_xStar :
        yStar ⬝ᵥ (fun i ↦ (b i : ℝ)) = cR ⬝ᵥ xStar := by
      refine le_antisymm ?_ hyStar_obj_ge
      calc
        yStar ⬝ᵥ (fun i ↦ (b i : ℝ)) ≤ y0 ⬝ᵥ (fun i ↦ (b i : ℝ)) := hyStar_obj_le
        _ = cR ⬝ᵥ xStar := hy0_value_xStar.symm
    have hyStar_value_on_face :
        ∀ ⦃x : Fin n → ℝ⦄, x ∈ F →
          (fun j ↦ (c j : ℝ)) ⬝ᵥ x = yStar ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
      intro x hxF
      calc
        (fun j ↦ (c j : ℝ)) ⬝ᵥ x = cR ⬝ᵥ x := by rfl
        _ = y0 ⬝ᵥ (fun i ↦ (b i : ℝ)) := hy0_value_on_face hxF
        _ = cR ⬝ᵥ xStar := hy0_value_xStar.symm
        _ = yStar ⬝ᵥ (fun i ↦ (b i : ℝ)) := hyStar_value_xStar.symm
    -- The integral optimal dual multiplier is supported on the active rows, so its active
    -- restriction is the required Hilbert-basis witness.
    exact active_row_nat_finsupp_of_integral_dual_value_on_face
      (A := A) (b := b) (c := c) (F := F) hyStar hyStar_integer hF_subset hyStar_value_on_face
  · intro hfaces
    exact totally_dual_integral_of_active_rows_form_hilbert_basis_on_each_face
      (A := A) (b := b) hfaces

end Theorem460
