/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the statements
-- below are written on the Chapter 3 owner surface `polyhedron_le_set`, `polyhedronDim`,
-- `recessionConeDim`, and `is_valid_inequality`.

section

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Helper for Exercise 3.14: the raw system `{x | A *ᵥ x ≤ b}` admits the standard
nonnegative row-multiplier certificate for valid inequalities. -/
private theorem valid_inequality_iff_exists_nonneg_row_multiplier_raw
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜)
    (b : m → 𝕜)
    (c : n → 𝕜)
    (δ : 𝕜)
    (hP_nonempty : Set.Nonempty {x : n → 𝕜 | A *ᵥ x ≤ b}) :
    (∀ ⦃x : n → 𝕜⦄, x ∈ {x : n → 𝕜 | A *ᵥ x ≤ b} → c ⬝ᵥ x ≤ δ) ↔
      ∃ u : m → 𝕜, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ := by
  let M : Matrix (n ⊕ Unit) (m ⊕ Unit) 𝕜 :=
    Matrix.fromBlocks A.transpose 0 (fun _ i ↦ b i) (1 : Matrix Unit Unit 𝕜)
  let d : (n ⊕ Unit) → 𝕜 := Sum.elim c fun _ ↦ δ
  have htranspose_mulVec (u : m → 𝕜) : A.transpose *ᵥ u = u ᵥ* A := by
    -- The transpose converts the column-side multiplication into the row-side certificate.
    simpa using (Matrix.vecMul_transpose A.transpose u).symm
  have hbottom_block_mulVec (u : m → 𝕜) :
      ((fun _ i ↦ b i : Matrix Unit m 𝕜) *ᵥ u) () = u ⬝ᵥ b := by
    -- The bottom block is exactly the objective row `b`.
    change ∑ i, b i * u i = u ⬝ᵥ b
    simpa [dotProduct] using dotProduct_comm b u
  have hrow_eval (w : (n ⊕ Unit) → 𝕜) (i : m) :
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
  have hslack_eval (w : (n ⊕ Unit) → 𝕜) :
      (w ᵥ* M) (Sum.inr ()) = w (Sum.inr ()) := by
    -- The final coordinate records the slack variable unchanged.
    simp [M, Matrix.vecMul_fromBlocks]
  have hdual_eval (w : (n ⊕ Unit) → 𝕜) :
      w ⬝ᵥ d = c ⬝ᵥ (w ∘ Sum.inl) + w (Sum.inr ()) * δ := by
    have hw : w = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) := by
      funext s
      rcases s with j | _
      · rfl
      · rfl
    calc
      w ⬝ᵥ d = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) ⬝ᵥ Sum.elim c (fun _ ↦ δ) := by
        rw [hw]
        rfl
      _ = (w ∘ Sum.inl) ⬝ᵥ c + (w ∘ Sum.inr) ⬝ᵥ (fun _ ↦ δ) := by
        simpa using
          sumElim_dotProduct_sumElim (w ∘ Sum.inl) c ((w ∘ Sum.inr) : Unit → 𝕜)
            (fun _ : Unit ↦ δ)
      _ = c ⬝ᵥ (w ∘ Sum.inl) + w (Sum.inr ()) * δ := by
        simp [dotProduct_comm]
  have hfeasible :
      (∃ z : m ⊕ Unit → 𝕜, M *ᵥ z = d ∧ 0 ≤ z) ↔
        ∃ u : m → 𝕜, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ := by
    constructor
    · rintro ⟨z, hz, hz_nonneg⟩
      let u : m → 𝕜 := z ∘ Sum.inl
      have hu_row : u ᵥ* A = c := by
        -- The top block enforces the desired row equation.
        ext j
        have hj : (M *ᵥ z) (Sum.inl j) = d (Sum.inl j) :=
          congrFun hz (Sum.inl j)
        simpa [M, d, u, Matrix.fromBlocks_mulVec, htranspose_mulVec u] using hj
      have hu_eval_le : u ⬝ᵥ b ≤ δ := by
        -- The bottom coordinate records the remaining nonnegative slack.
        have hbottom : (M *ᵥ z) (Sum.inr ()) = d (Sum.inr ()) :=
          congrFun hz (Sum.inr ())
        have hs_nonneg : 0 ≤ z (Sum.inr ()) := hz_nonneg (Sum.inr ())
        have hbottom' : u ⬝ᵥ b + z (Sum.inr ()) = δ := by
          simpa [M, d, u, Matrix.fromBlocks_mulVec, hbottom_block_mulVec] using hbottom
        have hub : u ⬝ᵥ b + z (Sum.inr ()) = δ := hbottom'
        linarith
      exact ⟨u, fun i ↦ hz_nonneg (Sum.inl i), hu_row, hu_eval_le⟩
    · rintro ⟨u, hu_nonneg, hu_row, hu_eval_le⟩
      let z : m ⊕ Unit → 𝕜 := Sum.elim u fun _ ↦ δ - u ⬝ᵥ b
      refine ⟨z, ?_, ?_⟩
      · -- Build the primal witness by appending the nonnegative slack.
        ext s
        rcases s with j | _
        · simpa [M, d, z, Matrix.fromBlocks_mulVec, htranspose_mulVec u] using congrFun hu_row j
        · have hbottom : u ⬝ᵥ b + (δ - u ⬝ᵥ b) = δ := by
            ring
          simp [M, d, z, Matrix.fromBlocks_mulVec, hbottom_block_mulVec, hbottom]
      · -- Nonnegativity is coordinatewise obvious from the hypothesis.
        intro s
        rcases s with i | _
        · exact hu_nonneg i
        · exact sub_nonneg.mpr hu_eval_le
  have hdual :
      (∀ w : (n ⊕ Unit) → 𝕜, w ᵥ* M ≤ 0 → w ⬝ᵥ d ≤ 0) ↔
        ∀ ⦃x : n → 𝕜⦄, x ∈ {x : n → 𝕜 | A *ᵥ x ≤ b} → c ⬝ᵥ x ≤ δ := by
    constructor
    · intro h x hx
      let w : (n ⊕ Unit) → 𝕜 := Sum.elim x fun _ ↦ (-1 : 𝕜)
      have hw : w ᵥ* M ≤ 0 := by
        -- Insert `x` with slack `-1` to read the primal inequality as a dual row condition.
        intro s
        rcases s with i | _
        · have hi : (A *ᵥ x) i + w (Sum.inr ()) * b i ≤ 0 := by
            simpa [w, sub_eq_add_neg] using sub_nonpos.mpr (hx i)
          simpa [hrow_eval, w] using hi
        · have hneg : (-1 : 𝕜) ≤ 0 := neg_nonpos.mpr zero_le_one
          simp [hslack_eval, w, hneg]
      have hwd : w ⬝ᵥ d ≤ 0 := h w hw
      have hsub : c ⬝ᵥ x - δ ≤ 0 := by
        simpa [hdual_eval, w, sub_eq_add_neg] using hwd
      exact sub_nonpos.mp hsub
    · intro hvalid w hw
      let x : n → 𝕜 := w ∘ Sum.inl
      let α : 𝕜 := w (Sum.inr ())
      have hα_nonpos : α ≤ 0 := by
        -- The slack coordinate is nonpositive because the last row of `M` is the identity.
        simpa [α, hslack_eval] using hw (Sum.inr ())
      rcases lt_or_eq_of_le hα_nonpos with hα_neg | hα_zero
      · let t : 𝕜 := -α
        have ht_pos : 0 < t := by
          simpa [t] using neg_pos.mpr hα_neg
        let y : n → 𝕜 := t⁻¹ • x
        have hy : y ∈ {x : n → 𝕜 | A *ᵥ x ≤ b} := by
          -- When `α < 0`, rescale to a feasible primal point and apply validity there.
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
          -- The rescaling is invertible because `t > 0`.
          ext j
          dsimp [y]
          calc
            x j = (t * t⁻¹) * x j := by rw [mul_inv_cancel₀ ht_pos.ne', one_mul]
            _ = t * (t⁻¹ * x j) := by ring
        have hwd_eq : w ⬝ᵥ d = t * (c ⬝ᵥ y - δ) := by
          -- Rewrite the dual objective in terms of the feasible point `y`.
          calc
            w ⬝ᵥ d = c ⬝ᵥ x + α * δ := by
              simp [x, α, hdual_eval]
            _ = c ⬝ᵥ (t • y) - t * δ := by
              simp [hx_eq, t, α]
            _ = t * (c ⬝ᵥ y) - t * δ := by
              rw [dotProduct_smul, smul_eq_mul]
            _ = t * (c ⬝ᵥ y - δ) := by
              ring
        rw [hwd_eq]
        exact mul_nonpos_of_nonneg_of_nonpos ht_pos.le (sub_nonpos.mpr hy_valid)
      · have hdir : A *ᵥ x ≤ 0 := by
          -- When the slack vanishes, `x` is a recession direction for the system.
          intro i
          have hi : (A *ᵥ x) i + α * b i ≤ 0 := by
            simpa [x, α, hrow_eval] using hw (Sum.inl i)
          simpa [hα_zero] using hi
        obtain ⟨x₀, hx₀⟩ := hP_nonempty
        have hcx_nonpos : c ⬝ᵥ x ≤ 0 := by
          by_contra hcx
          have hcx_pos : 0 < c ⬝ᵥ x := lt_of_not_ge hcx
          let t : 𝕜 := (δ - c ⬝ᵥ x₀ + 1) / (c ⬝ᵥ x)
          have ht_nonneg : 0 ≤ t := by
            -- Choose `t` so that the translated feasible point would violate validity otherwise.
            dsimp [t]
            refine div_nonneg ?_ hcx_pos.le
            linarith [hvalid hx₀]
          have hxt : x₀ + t • x ∈ {x : n → 𝕜 | A *ᵥ x ≤ b} := by
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
      (∃ u : m → 𝕜, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ) ↔
        ∀ w : (n ⊕ Unit) → 𝕜, w ᵥ* M ≤ 0 → w ⬝ᵥ d ≤ 0 :=
    hfeasible.symm.trans <|
      feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers M d
  exact hdual.symm.trans hcertificate.symm

end

/-- Helper for Exercise 3.14: if a linear functional is constant on a nonempty set, then it
vanishes on the direction of that set's affine span. -/
lemma constant_dotProduct_on_affine_span_direction_eq_zero
    {n : ℕ}
    {S : Set (Fin n → ℝ)}
    (hS : Set.Nonempty S)
    {e : Fin n → ℝ}
    (hconst : ∃ δ : ℝ, ∀ x ∈ S, e ⬝ᵥ x = δ) :
    ∀ z ∈ (affineSpan ℝ S).direction, e ⬝ᵥ z = 0 := by
  rcases hS with ⟨x₀, hx₀⟩
  rcases hconst with ⟨δ, hδ⟩
  let φ : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductEquiv ℝ (Fin n)) e
  have hspan :
      Submodule.span ℝ ((fun x : Fin n → ℝ ↦ x - x₀) '' S) ≤ LinearMap.ker φ := by
    -- It suffices to check the generators `x - x₀`, where constancy makes the dot product vanish.
    rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    change φ (x - x₀) = 0
    simp [φ, dotProduct_sub, hδ x hx, hδ x₀ hx₀]
  intro z hz
  have hz' : z ∈ LinearMap.ker φ := by
    -- Rewrite the affine-span direction to the span of displacement vectors from `x₀`.
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hx₀] at hz
    exact hspan hz
  simpa [φ] using hz'

/-- Helper for Exercise 3.14: the strict dimension gap rules out the empty polyhedron. -/
lemma polyhedron_nonempty_of_dim_gt_dim_recession
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hdim : polyhedronDim (polyhedron_le_set A b) > recessionConeDim (polyhedron_le_set A b)) :
    (polyhedron_le_set A b).Nonempty := by
  by_contra h_empty
  have hpoly_dim :
      polyhedronDim (polyhedron_le_set A b) = 0 := by
    -- The affine span of the empty set has zero-dimensional direction.
    simp [polyhedronDim, Set.not_nonempty_iff_eq_empty.mp h_empty]
  have hrec_dim :
      recessionConeDim (polyhedron_le_set A b) = n := by
    -- The recession cone of the empty set is all of `ℝ^n`.
    have hrec_univ : recessionCone (polyhedron_le_set A b) = Set.univ := by
      ext r
      rw [mem_recessionCone_iff]
      simp [Set.not_nonempty_iff_eq_empty.mp h_empty]
    calc
      recessionConeDim (polyhedron_le_set A b)
          = Module.finrank ℝ (Submodule.span ℝ (Set.univ : Set (Fin n → ℝ))) := by
              rw [recessionConeDim, hrec_univ]
      _ = Module.finrank ℝ (⊤ : Submodule ℝ (Fin n → ℝ)) := by
            rw [Submodule.span_univ]
      _ = n := by
            simp
  rw [hpoly_dim, hrec_dim] at hdim
  exact (Nat.not_lt_zero n) hdim

/-- Helper for Exercise 3.14: every recession direction is a difference of two points in the
affine hull of the polyhedron. -/
lemma recessionCone_subset_affineSpan_direction
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty) :
    recessionCone (polyhedron_le_set A b) ⊆
      (affineSpan ℝ (polyhedron_le_set A b)).direction := by
  intro r hr
  obtain ⟨x₀, hx₀P⟩ := hP_nonempty
  have hx₀_aff :
      x₀ ∈ affineSpan ℝ (polyhedron_le_set A b) :=
    mem_affineSpan ℝ hx₀P
  have hx₀rP :
      x₀ + r ∈ polyhedron_le_set A b := by
    -- A recession direction keeps the chosen feasible base point feasible.
    rw [mem_recessionCone_iff] at hr
    simpa using hr hx₀P 1 zero_le_one
  have hx₀r_aff :
      x₀ + r ∈ affineSpan ℝ (polyhedron_le_set A b) :=
    mem_affineSpan ℝ hx₀rP
  -- The direction vector is the difference of two points in the affine span.
  simpa using AffineSubspace.vsub_mem_direction hx₀r_aff hx₀_aff

/-- Helper for Exercise 3.14: the recession span is a proper subspace of the affine-span
direction under the stated dimension gap. -/
lemma recession_cone_span_lt_affineSpan_direction
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hdim : polyhedronDim (polyhedron_le_set A b) > recessionConeDim (polyhedron_le_set A b)) :
    Submodule.span ℝ (recessionCone (polyhedron_le_set A b)) <
      (affineSpan ℝ (polyhedron_le_set A b)).direction := by
  have hP_nonempty :
      (polyhedron_le_set A b).Nonempty :=
    polyhedron_nonempty_of_dim_gt_dim_recession A b hdim
  have hle :
      Submodule.span ℝ (recessionCone (polyhedron_le_set A b)) ≤
        (affineSpan ℝ (polyhedron_le_set A b)).direction := by
    -- Span membership reduces to the pointwise recession-direction inclusion.
    rw [Submodule.span_le]
    intro r hr
    exact recessionCone_subset_affineSpan_direction A b hP_nonempty hr
  have hfinrank_lt :
      Module.finrank ℝ (Submodule.span ℝ (recessionCone (polyhedron_le_set A b))) <
        Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
    simpa [polyhedronDim, recessionConeDim] using hdim
  have hne :
      Submodule.span ℝ (recessionCone (polyhedron_le_set A b)) ≠
        (affineSpan ℝ (polyhedron_le_set A b)).direction := by
    -- Equal finite-dimensional subspaces would have equal finrank.
    intro hEq
    rw [hEq] at hfinrank_lt
    exact lt_irrefl _ hfinrank_lt
  exact lt_of_le_of_ne hle hne

/-- Helper for Exercise 3.14: the dimension gap yields a linear functional that vanishes on the
recession cone but is not constant on the polyhedron. -/
lemma exists_nonconstant_functional_vanishing_on_recession_cone
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hdim : polyhedronDim (polyhedron_le_set A b) > recessionConeDim (polyhedron_le_set A b)) :
    ∃ e : Fin n → ℝ,
      (∀ r ∈ recessionCone (polyhedron_le_set A b), e ⬝ᵥ r = 0) ∧
      ¬ ∃ δ : ℝ, ∀ x ∈ polyhedron_le_set A b, e ⬝ᵥ x = δ := by
  let P := polyhedron_le_set A b
  let L : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (recessionCone P)
  let D : Submodule ℝ (Fin n → ℝ) := (affineSpan ℝ P).direction
  have hlt : L < D := by
    -- Convert the dimension gap into a strict subspace inclusion.
    simpa [L, D, P] using recession_cone_span_lt_affineSpan_direction A b hdim
  obtain ⟨v, hvD, hvL⟩ := SetLike.exists_of_lt hlt
  obtain ⟨φ, hφv, hLker⟩ := Submodule.exists_le_ker_of_notMem hvL
  let e : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm φ
  have he_apply (z : Fin n → ℝ) : e ⬝ᵥ z = φ z := by
    -- `dotProductEquiv` identifies linear forms with row vectors.
    have hphi : (dotProductEquiv ℝ (Fin n)) e = φ := by
      simp [e]
    simpa using congrArg (fun ψ => ψ z) hphi
  refine ⟨e, ?_, ?_⟩
  · intro r hr
    have hrL : r ∈ L := Submodule.subset_span hr
    have hrker : r ∈ LinearMap.ker φ := hLker hrL
    simpa [he_apply r] using hrker
  · intro hconst
    have hP_nonempty :
        P.Nonempty :=
      polyhedron_nonempty_of_dim_gt_dim_recession A b hdim
    have hzero_on_D :
        ∀ z ∈ D, e ⬝ᵥ z = 0 := by
      -- Constancy on `P` annihilates every vector in the affine-span direction of `P`.
      simpa [D, P] using
        constant_dotProduct_on_affine_span_direction_eq_zero hP_nonempty hconst
    have hvzero : e ⬝ᵥ v = 0 := hzero_on_D v hvD
    have hφv_zero : φ v = 0 := by
      simpa [he_apply v] using hvzero
    exact hφv hφv_zero

/-- Helper for Exercise 3.14: the dimension gap provides a nonnegative multiplier that annihilates
the rows of `A` while having strictly positive value on `b`. -/
lemma exists_positive_zero_row_multiplier_of_dim_gap
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hdim : polyhedronDim (polyhedron_le_set A b) > recessionConeDim (polyhedron_le_set A b)) :
    ∃ w : Fin m → ℝ, 0 ≤ w ∧ w ᵥ* A = 0 ∧ 0 < w ⬝ᵥ b := by
  let P := polyhedron_le_set A b
  have hP_nonempty :
      P.Nonempty :=
    polyhedron_nonempty_of_dim_gt_dim_recession A b hdim
  obtain ⟨e, he_recession, he_nonconstant⟩ :=
    exists_nonconstant_functional_vanishing_on_recession_cone A b hdim
  have hhom_nonempty :
      (polyhedron_le_set A (0 : Fin m → ℝ)).Nonempty := by
    -- The homogeneous system always contains the zero vector.
    refine ⟨0, ?_⟩
    simp [polyhedron_le_set]
  have hvalid_e :
      is_valid_inequality (polyhedron_le_set A (0 : Fin m → ℝ)) e 0 := by
    intro r hr
    have hr_rec : r ∈ recessionCone P := by
      rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
      exact hr
    have hzero : e ⬝ᵥ r = 0 := he_recession r hr_rec
    simp [hzero]
  have hvalid_neg_e :
      is_valid_inequality (polyhedron_le_set A (0 : Fin m → ℝ)) (-e) 0 := by
    intro r hr
    have hr_rec : r ∈ recessionCone P := by
      rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b hP_nonempty]
      exact hr
    have hzero : e ⬝ᵥ r = 0 := he_recession r hr_rec
    simp [hzero]
  obtain ⟨uPlus, huPlus_nonneg, huPlus_row, huPlus_eval⟩ :=
    (valid_inequality_iff_exists_nonneg_row_multiplier A (0 : Fin m → ℝ) e 0
      hhom_nonempty).mp hvalid_e
  obtain ⟨uMinus, huMinus_nonneg, huMinus_row, huMinus_eval⟩ :=
    (valid_inequality_iff_exists_nonneg_row_multiplier A (0 : Fin m → ℝ) (-e) 0
      hhom_nonempty).mp hvalid_neg_e
  have hpair_ne :
      ∃ x y : Fin n → ℝ,
        x ∈ P ∧ y ∈ P ∧ e ⬝ᵥ x ≠ e ⬝ᵥ y := by
    by_contra hpair_ne
    push Not at hpair_ne
    obtain ⟨x₀, hx₀⟩ := hP_nonempty
    exact he_nonconstant ⟨e ⬝ᵥ x₀, fun x hx ↦ hpair_ne x x₀ hx hx₀⟩
  have hpair_lt :
      ∃ x y : Fin n → ℝ,
        x ∈ P ∧ y ∈ P ∧ e ⬝ᵥ x < e ⬝ᵥ y := by
    obtain ⟨x, y, hx, hy, hxy_ne⟩ := hpair_ne
    rcases lt_or_gt_of_ne hxy_ne with hxy_lt | hyx_lt
    · exact ⟨x, y, hx, hy, hxy_lt⟩
    · exact ⟨y, x, hy, hx, hyx_lt⟩
  obtain ⟨x, y, hxP, hyP, hxy_lt⟩ := hpair_lt
  have hy_upper : e ⬝ᵥ y ≤ uPlus ⬝ᵥ b := by
    -- The `uPlus` certificate bounds `e` from above on all feasible points of `P`.
    calc
      e ⬝ᵥ y = uPlus ⬝ᵥ (A *ᵥ y) := by
        rw [← huPlus_row, Matrix.dotProduct_mulVec]
      _ ≤ uPlus ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hyP huPlus_nonneg
  have hx_lower : -(e ⬝ᵥ x) ≤ uMinus ⬝ᵥ b := by
    -- The `uMinus` certificate bounds `-e` from above, hence `e` from below.
    calc
      -(e ⬝ᵥ x) = (-e) ⬝ᵥ x := by simp
      _ = uMinus ⬝ᵥ (A *ᵥ x) := by
        rw [← huMinus_row, Matrix.dotProduct_mulVec]
      _ ≤ uMinus ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hxP huMinus_nonneg
  let w : Fin m → ℝ := uPlus + uMinus
  have hw_eval_pos : 0 < w ⬝ᵥ b := by
    have hgap_pos : 0 < e ⬝ᵥ y - e ⬝ᵥ x := sub_pos.mpr hxy_lt
    have hgap_le : e ⬝ᵥ y - e ⬝ᵥ x ≤ w ⬝ᵥ b := by
      -- Adding the upper and lower bounds produces a positive right-hand-side slack.
      calc
        e ⬝ᵥ y - e ⬝ᵥ x = e ⬝ᵥ y + -(e ⬝ᵥ x) := by ring
        _ ≤ uPlus ⬝ᵥ b + uMinus ⬝ᵥ b := add_le_add hy_upper hx_lower
        _ = w ⬝ᵥ b := by
          dsimp [w]
          rw [add_dotProduct]
    exact lt_of_lt_of_le hgap_pos hgap_le
  refine ⟨w, ?_, ?_, hw_eval_pos⟩
  · intro i
    -- Sum the two nonnegative row multipliers coordinatewise.
    dsimp [w]
    exact add_nonneg (huPlus_nonneg i) (huMinus_nonneg i)
  · -- The row images cancel because `uPlus` and `uMinus` certify `e` and `-e`.
    calc
      w ᵥ* A = uPlus ᵥ* A + uMinus ᵥ* A := by
        dsimp [w]
        rw [Matrix.add_vecMul]
      _ = e + (-e) := by rw [huPlus_row, huMinus_row]
      _ = 0 := by simp

/-- Exercise 3.14 (1). Let `P := polyhedron_le_set A b`. If `dim(P) > dim(rec(P))`, then the
inequality `c ⬝ᵥ x ≤ δ` is valid for `P` if and only if there exists a nonnegative row multiplier
`u` for `A *ᵥ x ≤ b` that certifies the same inequality and is exact on the right-hand side. -/
theorem valid_inequality_iff_exists_nonneg_row_multiplier_of_dim_gt_dim_recession
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (δ : ℝ)
    (hdim : polyhedronDim (polyhedron_le_set A b) > recessionConeDim (polyhedron_le_set A b)) :
    is_valid_inequality (polyhedron_le_set A b) c δ ↔
      ∃ u : Fin m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b = δ := by
  have hP_nonempty :
      (polyhedron_le_set A b).Nonempty :=
    polyhedron_nonempty_of_dim_gt_dim_recession A b hdim
  constructor
  · intro hvalid
    obtain ⟨u, hu_nonneg, hu_row, hu_eval_le⟩ :=
      (valid_inequality_iff_exists_nonneg_row_multiplier A b c δ hP_nonempty).mp hvalid
    obtain ⟨w, hw_nonneg, hw_row, hw_eval_pos⟩ :=
      exists_positive_zero_row_multiplier_of_dim_gap A b hdim
    let t : ℝ := (δ - u ⬝ᵥ b) / (w ⬝ᵥ b)
    have ht_nonneg : 0 ≤ t := by
      -- The correcting scalar is nonnegative because `u ⬝ᵥ b ≤ δ` and `w ⬝ᵥ b > 0`.
      dsimp [t]
      exact div_nonneg (sub_nonneg.mpr hu_eval_le) hw_eval_pos.le
    have ht_mul :
        t * (w ⬝ᵥ b) = δ - u ⬝ᵥ b := by
      -- Clearing the positive denominator computes the exact slack correction.
      dsimp [t]
      field_simp [hw_eval_pos.ne']
    refine ⟨u + t • w, ?_, ?_, ?_⟩
    · intro i
      -- Coordinatewise nonnegativity is preserved by adding a nonnegative multiple of `w`.
      dsimp [t]
      exact add_nonneg (hu_nonneg i) (mul_nonneg ht_nonneg (hw_nonneg i))
    · -- The correction multiplier lies in the left kernel of `A`, so the row equation is unchanged.
      calc
        (u + t • w) ᵥ* A = u ᵥ* A + (t • w) ᵥ* A := by
          rw [Matrix.add_vecMul]
        _ = c + t • (w ᵥ* A) := by
          rw [hu_row, Matrix.smul_vecMul]
        _ = c := by simp [hw_row]
    · -- The positive zero-row multiplier adjusts the right-hand side from `u ⬝ᵥ b` up to `δ`.
      have hsum :
          u ⬝ᵥ b + t * (w ⬝ᵥ b) = δ := by
        linarith
      calc
        (u + t • w) ⬝ᵥ b = u ⬝ᵥ b + t * (w ⬝ᵥ b) := by
          rw [add_dotProduct, smul_dotProduct]
          simp [smul_eq_mul]
        _ = δ := hsum
  · rintro ⟨u, hu_nonneg, hu_row, hu_eval⟩
    intro x hx
    -- Weak duality closes the reverse implication directly from the exact row certificate.
    calc
      c ⬝ᵥ x = (u ᵥ* A) ⬝ᵥ x := by rw [← hu_row]
      _ = u ⬝ᵥ (A *ᵥ x) := by rw [Matrix.dotProduct_mulVec]
      _ ≤ u ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx hu_nonneg
      _ = δ := hu_eval

/-- Exercise 3.14 (2). Replacing `dim(P) > dim(rec(P))` by nonemptiness does not suffice: for the
nonempty polyhedron `P := polyhedron_le_set 0 0`, the valid inequality `0 ⬝ᵥ x ≤ 1` has no exact
row-multiplier certificate on the Chapter 3 surface. -/
theorem nonempty_polyhedron_not_sufficient_for_exact_row_multiplier_representation :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let b : Fin 1 → ℝ := 0
    let P := polyhedron_le_set A b
    is_valid_inequality P (0 : Fin 1 → ℝ) 1 ∧
      Set.Nonempty P ∧
      ¬ ∃ u : Fin 1 → ℝ, 0 ≤ u ∧ u ᵥ* A = (0 : Fin 1 → ℝ) ∧ u ⬝ᵥ b = 1 :=
  by
  dsimp [is_valid_inequality, polyhedron_le_set]
  constructor
  · intro x hx
    simp
  constructor
  · -- The zero vector is feasible for the homogeneous zero system.
    refine ⟨0, ?_⟩
    simp
  · rintro ⟨u, hu_nonneg, hu_row, hu_eval⟩
    -- Any multiplier against `b = 0` has objective value `0`, never `1`.
    simp at hu_eval
