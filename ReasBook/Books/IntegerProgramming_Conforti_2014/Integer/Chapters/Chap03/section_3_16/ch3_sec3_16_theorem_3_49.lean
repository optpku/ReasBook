/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_16.ch3_sec3_16_definition_3_16_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_4.ch3_sec3_4_4_definition_3_4_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1

open WithLp
open scoped BigOperators Matrix Pointwise Polar

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Helper for Theorem 3.49: the homogeneous Farkas bridge on the raw matrix polyhedron
`{x | A *ᵥ x ≤ b}`. -/
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
  -- Route correction: keep the Theorem 3.22 block-matrix certificate proof, but work directly on
  -- the local raw owner `{x | A *ᵥ x ≤ b}` instead of importing the upstream owner file.
  have htranspose_mulVec (u : m → 𝕜) : A.transpose *ᵥ u = u ᵥ* A := by
    simpa using (Matrix.vecMul_transpose A.transpose u).symm
  have hbottom_block_mulVec (u : m → 𝕜) :
      ((fun _ i ↦ b i : Matrix Unit m 𝕜) *ᵥ u) () = u ⬝ᵥ b := by
    change (∑ i, (b i) * (u i)) = u ⬝ᵥ b
    simpa [dotProduct] using dotProduct_comm b u
  have hrow_eval (w : (n ⊕ Unit) → 𝕜) (i : m) :
      (w ᵥ* M) (Sum.inl i) = (A *ᵥ (w ∘ Sum.inl)) i + (w (Sum.inr ())) * (b i) := by
    have htop : ((w ∘ Sum.inl) ᵥ* A.transpose) i = (A *ᵥ (w ∘ Sum.inl)) i := by
      simpa using congrFun (Matrix.vecMul_transpose A (w ∘ Sum.inl)) i
    calc
      (w ᵥ* M) (Sum.inl i)
          = ((w ∘ Sum.inl) ᵥ* A.transpose) i + ((w ∘ Sum.inr) ᵥ* (fun _ j ↦ b j)) i := by
              simp [M, Matrix.vecMul_fromBlocks]
      _ = (A *ᵥ (w ∘ Sum.inl)) i + ((w ∘ Sum.inr) ᵥ* (fun _ j ↦ b j)) i := by
            rw [htop]
      _ = (A *ᵥ (w ∘ Sum.inl)) i + (w (Sum.inr ())) * (b i) := by
            simp [Matrix.vecMul, dotProduct]
  have hslack_eval (w : (n ⊕ Unit) → 𝕜) :
      (w ᵥ* M) (Sum.inr ()) = w (Sum.inr ()) := by
    simp [M, Matrix.vecMul_fromBlocks]
  have hdual_eval (w : (n ⊕ Unit) → 𝕜) :
      w ⬝ᵥ d = c ⬝ᵥ (w ∘ Sum.inl) + (w (Sum.inr ())) * δ := by
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
      _ = c ⬝ᵥ (w ∘ Sum.inl) + (w (Sum.inr ())) * δ := by
        simp [dotProduct_comm]
  have hfeasible :
      (∃ z : m ⊕ Unit → 𝕜, M *ᵥ z = d ∧ 0 ≤ z) ↔
        ∃ u : m → 𝕜, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ := by
    constructor
    · rintro ⟨z, hz, hz_nonneg⟩
      let u : m → 𝕜 := z ∘ Sum.inl
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
        have hub : u ⬝ᵥ b + z (Sum.inr ()) = δ := hbottom'
        linarith
      exact ⟨u, fun i ↦ hz_nonneg (Sum.inl i), hu_row, hu_eval_le⟩
    · rintro ⟨u, hu_nonneg, hu_row, hu_eval_le⟩
      let z : m ⊕ Unit → 𝕜 := Sum.elim u fun _ ↦ δ - u ⬝ᵥ b
      refine ⟨z, ?_, ?_⟩
      · ext s
        rcases s with j | _
        · simpa [M, d, z, Matrix.fromBlocks_mulVec, htranspose_mulVec u] using congrFun hu_row j
        · have hbottom : u ⬝ᵥ b + (δ - u ⬝ᵥ b) = δ := by
            ring
          simp [M, d, z, Matrix.fromBlocks_mulVec, hbottom_block_mulVec, hbottom]
      · intro s
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
        intro s
        rcases s with i | _
        · have hi : (A *ᵥ x) i + (w (Sum.inr ())) * (b i) ≤ 0 := by
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
        simpa [α, hslack_eval] using hw (Sum.inr ())
      rcases lt_or_eq_of_le hα_nonpos with hα_neg | hα_zero
      · let t : 𝕜 := -α
        have ht_pos : 0 < t := by
          simpa [t] using neg_pos.mpr hα_neg
        let y : n → 𝕜 := t⁻¹ • x
        have hy : y ∈ {x : n → 𝕜 | A *ᵥ x ≤ b} := by
          intro i
          have hi : (A *ᵥ x) i + α * (b i) ≤ 0 := by
            simpa [x, α, hrow_eval] using hw (Sum.inl i)
          have hbound : (A *ᵥ x) i ≤ t * (b i) := by
            have hsub : (A *ᵥ x) i - t * (b i) ≤ 0 := by
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
            _ = t * (c ⬝ᵥ y - δ) := by
              ring
        rw [hwd_eq]
        exact mul_nonpos_of_nonneg_of_nonpos ht_pos.le (sub_nonpos.mpr hy_valid)
      · have hdir : A *ᵥ x ≤ 0 := by
          intro i
          have hi : (A *ᵥ x) i + α * (b i) ≤ 0 := by
            simpa [x, α, hrow_eval] using hw (Sum.inl i)
          simpa [hα_zero] using hi
        obtain ⟨x₀, hx₀⟩ := hP_nonempty
        have hcx_nonpos : c ⬝ᵥ x ≤ 0 := by
          by_contra hcx
          have hcx_pos : 0 < c ⬝ᵥ x := lt_of_not_ge hcx
          let t : 𝕜 := (δ - c ⬝ᵥ x₀ + 1) / (c ⬝ᵥ x)
          have ht_nonneg : 0 ≤ t := by
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

/-- Helper for Theorem 3.49: the Farkas certificate characterization of valid inequalities for the
matrix polyhedron `polyhedron_le_set A b`. -/
theorem valid_inequality_iff_exists_nonneg_row_multiplier
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (δ : ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty) :
    is_valid_inequality (polyhedron_le_set A b) c δ ↔
      ∃ u : Fin m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ δ := by
  -- Unfold validity on `polyhedron_le_set` and reuse the raw matrix-level Farkas bridge.
  simpa [is_valid_inequality, polyhedron_le_set] using
    valid_inequality_iff_exists_nonneg_row_multiplier_raw A b c δ hP_nonempty

/-- Helper for Theorem 3.49: membership in the polar of the Euclidean image of a polyhedron is
exactly validity of the corresponding dot-product inequality on the raw polyhedron. -/
lemma mem_polar_image_polyhedron_iff_valid_inequality
    {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ ((toLp 2) '' polyhedron_le_set a b)* ↔
      is_valid_inequality (polyhedron_le_set a b) (WithLp.ofLp y) 1 := by
  -- Rewrite polar membership into the source-space inequality defining validity.
  rw [Set.mem_polar_iff, is_valid_inequality_iff]
  constructor
  · intro hy x hx
    have hy' := hy (toLp 2 x) ⟨x, hx, rfl⟩
    simpa [WithLp.toLp_ofLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using hy'
  · intro hy z hz
    rcases hz with ⟨x, hx, rfl⟩
    simpa [WithLp.toLp_ofLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using hy hx

/-- Helper for Theorem 3.49: the mixed right-hand-side dot product is the sum of the early
coefficients. -/
lemma dotProduct_mixed_rhs_eq_sum_early
    {m : ℕ} (k : ℕ) (u : Fin m → ℝ) :
    u ⬝ᵥ (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0) =
      ∑ i : {j : Fin m // j.1 < k}, u i.1 := by
  let s : Finset (Fin m) := Finset.univ.filter (fun i : Fin m ↦ i.1 < k)
  let e : {x // x ∈ s} ≃ {j : Fin m // j.1 < k} :=
    { toFun := fun x ↦ ⟨x.1, by
        have hx : x.1 ∈ s := x.2
        simpa [s] using (Finset.mem_filter.mp hx).2⟩
      invFun := fun x ↦ ⟨x.1, by simp [s, x.2]⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl }
  -- Rewrite the mixed right-hand side to the filtered early-index sum.
  calc
    u ⬝ᵥ (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0)
        = ∑ i : Fin m, if i.1 < k then u i else 0 := by
            simp [dotProduct]
    _ = Finset.sum s u := by
          simp [s, Finset.sum_filter]
    _ = ∑ i : {x // x ∈ s}, u i.1 := by
          rw [← Finset.sum_attach, Finset.attach_eq_univ]
    _ = ∑ i : {j : Fin m // j.1 < k}, u i.1 := by
          exact Fintype.sum_equiv e _ _ (fun i ↦ rfl)

/-- Helper for Theorem 3.49: splitting a row combination into the early and late rows gives a
pointwise sum decomposition of the resulting vector. -/
lemma vecMul_split_lt_ge
    {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) (u : Fin m → ℝ) :
    u ᵥ* a =
      (fun j : Fin n ↦ ∑ i : {r : Fin m // r.1 < k}, ((u i.1) * (a i.1 j))) +
        (fun j : Fin n ↦ ∑ i : {r : Fin m // k ≤ r.1}, ((u i.1) * (a i.1 j))) := by
  let sLt : Finset (Fin m) := Finset.univ.filter (fun r : Fin m ↦ r.1 < k)
  let sGe : Finset (Fin m) := Finset.univ.filter (fun r : Fin m ↦ ¬ r.1 < k)
  let eLt : {x // x ∈ sLt} ≃ {r : Fin m // r.1 < k} :=
    { toFun := fun x ↦ ⟨x.1, by
        have hx : x.1 ∈ sLt := x.2
        simpa [sLt] using (Finset.mem_filter.mp hx).2⟩
      invFun := fun x ↦ ⟨x.1, by simp [sLt, x.2]⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl }
  let eGe : {x // x ∈ sGe} ≃ {r : Fin m // k ≤ r.1} :=
    { toFun := fun x ↦ ⟨x.1, by
        have hx : x.1 ∈ sGe := x.2
        have hx' : ¬ x.1.1 < k := by
          simpa [sGe] using (Finset.mem_filter.mp hx).2
        exact Nat.le_of_not_gt hx'⟩
      invFun := fun x ↦ ⟨x.1, by
        simp [sGe, x.2]⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl }
  funext j
  let f : Fin m → ℝ := fun i ↦ (u i) * (a i j)
  have hLt :
      Finset.sum sLt f = ∑ i : {r : Fin m // r.1 < k}, f i.1 := by
    calc
      Finset.sum sLt f = ∑ i : {x // x ∈ sLt}, f i.1 := by
        rw [← Finset.sum_attach, Finset.attach_eq_univ]
      _ = ∑ i : {r : Fin m // r.1 < k}, f i.1 := by
        exact Fintype.sum_equiv eLt _ _ (fun i ↦ rfl)
  have hGe :
      Finset.sum sGe f = ∑ i : {r : Fin m // k ≤ r.1}, f i.1 := by
    calc
      Finset.sum sGe f = ∑ i : {x // x ∈ sGe}, f i.1 := by
        rw [← Finset.sum_attach, Finset.attach_eq_univ]
      _ = ∑ i : {r : Fin m // k ≤ r.1}, f i.1 := by
        exact Fintype.sum_equiv eGe _ _ (fun i ↦ rfl)
  -- Split the full row sum into the early and late filters, then transport each filter to the
  -- corresponding subtype-indexed family.
  calc
    (u ᵥ* a) j = ∑ i : Fin m, f i := by
      simp [Matrix.vecMul, dotProduct, f]
    _ = Finset.sum sLt f + Finset.sum sGe f := by
          simpa [sLt, sGe, f] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ
              (fun r : Fin m ↦ r.1 < k) f).symm
    _ = ∑ i : {r : Fin m // r.1 < k}, f i.1 +
          ∑ i : {r : Fin m // k ≤ r.1}, f i.1 := by
            rw [hLt, hGe]
    _ =
        (fun j : Fin n ↦ ∑ i : {r : Fin m // r.1 < k}, (u i.1) * (a i.1 j)) j +
          (fun j : Fin n ↦ ∑ i : {r : Fin m // k ≤ r.1}, (u i.1) * (a i.1 j)) j := by
            rfl

/-- Helper for Theorem 3.49: a nonnegative combination of the early rows with total weight at most
`1` lies in the convex hull of `0` and those rows. -/
lemma early_row_combination_mem_convexHull
    {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    (u : {j : Fin m // j.1 < k} → ℝ)
    (hu_nonneg : ∀ i, 0 ≤ u i)
    (hu_sum_le : ∑ i, u i ≤ 1) :
    toLp 2 (fun j : Fin n ↦ ∑ i : {l : Fin m // l.1 < k}, ((u i) * (a i.1 j))) ∈
      convexHull ℝ ({0} ∪ Set.range (fun i : {j : Fin m // j.1 < k} ↦ toLp 2 (a i.1))) := by
  let w : Option {j : Fin m // j.1 < k} → ℝ
    | none => 1 - ∑ i, u i
    | some i => u i
  let z : Option {j : Fin m // j.1 < k} → EuclideanSpace ℝ (Fin n)
    | none => 0
    | some i => toLp 2 (a i.1)
  -- Add the missing slack as the weight of the origin and package the resulting family as a
  -- finite convex combination.
  refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ ?_
  · intro o
    cases o with
    | none =>
        exact sub_nonneg.mpr hu_sum_le
    | some i =>
        exact hu_nonneg i
  · calc
      ∑ o, w o = w none + ∑ i, w (some i) := by
        rw [Fintype.sum_option]
      _ = (1 - ∑ i, u i) + ∑ i, u i := by
        simp [w]
      _ = 1 := by
        ring
  · intro o
    cases o with
    | none =>
        simp [z]
    | some i =>
        exact Or.inr (Set.mem_range_self i)
  · ext j
    -- Evaluating the convex combination coordinatewise recovers exactly the prescribed early-row
    -- linear combination.
    calc
      (∑ o, w o • z o) j = (w none • z none + ∑ i, w (some i) • z (some i)) j := by
        rw [Fintype.sum_option]
      _ = (∑ i : {l : Fin m // l.1 < k}, u i • toLp 2 (a i.1)) j := by
        simp [w, z]
      _ = ∑ i : {l : Fin m // l.1 < k}, (u i) * (a i.1 j) := by
        simp [smul_eq_mul]

/-- Helper for Theorem 3.49: a finite nonnegative weighted sum of a family lies in the cone
generated by that family. -/
lemma finite_weighted_sum_mem_cone_range
    {ι : Type*} [Fintype ι] {n : ℕ}
    (r : ι → Fin n → ℝ)
    (u : ι → ℝ)
    (hu_nonneg : ∀ i, 0 ≤ u i) :
    (fun t : Fin n ↦ ∑ i : ι, (u i) * (r i t)) ∈ cone (Set.range r) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  -- Route correction: normalize the finite family through `equivFin` once so the cone witness
  -- lives on the canonical `Fin` index type expected by `mem_cone_iff`.
  refine (mem_cone_iff).2 ?_
  refine ⟨Fintype.card ι, fun j ↦ r (e.symm j), ?_, ?_⟩
  · intro j
    exact Set.mem_range_self (e.symm j)
  · refine ⟨fun j ↦ u (e.symm j), ?_, ?_⟩
    · intro j
      exact hu_nonneg (e.symm j)
    · ext t
      -- Reindex the coordinate sum along `equivFin` and rewrite scalar multiplication as
      -- coordinatewise multiplication.
      calc
        (fun t : Fin n ↦ ∑ i : ι, (u i) * (r i t)) t = ∑ i : ι, (u i) * (r i t) := by
          rfl
        _ = ∑ j : Fin (Fintype.card ι), (u (e.symm j)) * (r (e.symm j) t) := by
              exact
                Fintype.sum_equiv e
                  (fun i : ι ↦ (u i) * (r i t))
                  (fun j : Fin (Fintype.card ι) ↦ (u (e.symm j)) * (r (e.symm j) t))
                  (fun i ↦ by simp)
        _ = (∑ j : Fin (Fintype.card ι), (u (e.symm j)) • r (e.symm j)) t := by
              simp [smul_eq_mul]

/-- Helper for Theorem 3.49: a conic combination of vectors that all pair nonpositively with `x`
still pairs nonpositively with `x`. -/
lemma dotProduct_nonpos_of_isConicCombination
    {n q : ℕ} {x y : Fin n → ℝ} {r : Fin q → Fin n → ℝ}
    (hcomb : IsConicCombination y r)
    (hr_nonpos : ∀ j, r j ⬝ᵥ x ≤ 0) :
    y ⬝ᵥ x ≤ 0 := by
  rcases hcomb with ⟨coeff, hcoeff_nonneg, hsum⟩
  -- Expand the conic combination and estimate each summand coefficientwise.
  calc
    y ⬝ᵥ x = (∑ j, coeff j • r j) ⬝ᵥ x := by
      simp [hsum]
    _ = ∑ j, (coeff j • r j) ⬝ᵥ x := by
          simpa using
            (sum_dotProduct Finset.univ (fun j : Fin q ↦ coeff j • r j) x)
    _ = ∑ j : Fin q, (coeff j) * (r j ⬝ᵥ x) := by
          simp [smul_eq_mul]
    _ ≤ 0 := by
          refine Finset.sum_nonpos ?_
          intro j hj
          exact mul_nonpos_of_nonneg_of_nonpos (hcoeff_nonneg j) (hr_nonpos j)

/-- Helper for Theorem 3.49: a nonnegative combination of the late rows lies in the cone image of
those rows. -/
lemma late_row_combination_mem_cone_image
    {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    (u : {j : Fin m // k ≤ j.1} → ℝ)
    (hu_nonneg : ∀ i, 0 ≤ u i) :
    toLp 2 (fun j : Fin n ↦ ∑ i : {l : Fin m // k ≤ l.1}, ((u i) * (a i.1 j))) ∈
      (toLp 2 '' cone (Set.range (fun i : {j : Fin m // k ≤ j.1} ↦ a i.1))) := by
  let r : Fin n → ℝ := fun j : Fin n ↦ ∑ i : {l : Fin m // k ≤ l.1}, ((u i) * (a i.1 j))
  have hr : r ∈ cone (Set.range (fun i : {j : Fin m // k ≤ j.1} ↦ a i.1)) := by
    -- Use the normalized finite-family cone adapter on the late-row subtype family.
    simpa [r] using
      finite_weighted_sum_mem_cone_range (fun i : {j : Fin m // k ≤ j.1} ↦ a i.1) u hu_nonneg
  exact ⟨r, hr, rfl⟩

/-- Helper for Theorem 3.49: every cone combination of the late rows has nonpositive pairing with
every point of the mixed-right-hand-side polyhedron. -/
lemma late_cone_dotProduct_nonpos
    {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    {x r : Fin n → ℝ}
    (hx : x ∈ polyhedron_le_set a (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0))
    (hr : r ∈ cone (Set.range (fun i : {j : Fin m // k ≤ j.1} ↦ a i.1))) :
    r ⬝ᵥ x ≤ 0 := by
  rcases (mem_cone_iff).1 hr with ⟨q, s, hs_source, hs_comb⟩
  -- Every late generator already satisfies the homogeneous inequality, so the whole cone
  -- combination does as well.
  refine dotProduct_nonpos_of_isConicCombination hs_comb ?_
  intro j
  rcases hs_source j with ⟨i, hi_eq⟩
  have hrow : (a *ᵥ x) i.1 ≤ if i.1.1 < k then (1 : ℝ) else 0 := hx i.1
  have hlate : ¬ i.1.1 < k := Nat.not_lt.mpr i.2
  have hsj : s j = a i.1 := by
    simpa using hi_eq.symm
  rw [hsj]
  simpa [Matrix.mulVec, hlate] using hrow

/-- Helper for Theorem 3.49: the mixed-hull side always pairs with a point of the mixed-right-hand
side polyhedron by at most `1`. -/
lemma mixed_hull_pairing_le_one_of_mem_mixed_rhs_polyhedron
    {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    {x : Fin n → ℝ}
    {y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ polyhedron_le_set a (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0))
    (hy :
      y ∈ convexHull ℝ ({0} ∪ Set.range (fun i : {j : Fin m // j.1 < k} ↦ toLp 2 (a i.1))) +
        (toLp 2 '' cone (Set.range (fun i : {j : Fin m // k ≤ j.1} ↦ a i.1)))) :
    inner ℝ y (toLp 2 x) ≤ 1 := by
  let H : Set (EuclideanSpace ℝ (Fin n)) := {z | inner ℝ z (toLp 2 x) ≤ 1}
  rcases Set.mem_add.mp hy with ⟨y₀, hy₀, r, hr, rfl⟩
  have hsource_subset :
      ({0} ∪ Set.range (fun i : {j : Fin m // j.1 < k} ↦ toLp 2 (a i.1))) ⊆ H := by
    intro z hz
    rcases hz with rfl | hz
    · simp [H]
    · rcases hz with ⟨i, rfl⟩
      have hrow : (a *ᵥ x) i.1 ≤ if i.1.1 < k then (1 : ℝ) else 0 := hx i.1
      -- The early generators satisfy the inhomogeneous bound `≤ 1` from the polyhedron
      -- definition.
      simpa [H, polyhedron_le_set, Matrix.mulVec, EuclideanSpace.inner_toLp_toLp, dotProduct_comm,
        i.2] using hrow
  have hH_convex : Convex ℝ H := by
    -- Identify the controlling halfspace with the polar of the singleton `{toLp 2 x}`.
    simpa [H, Set.polar] using
      Set.convex_polar ({toLp 2 x} : Set (EuclideanSpace ℝ (Fin n)))
  have hy₀_le : inner ℝ y₀ (toLp 2 x) ≤ 1 := by
    exact (convexHull_min hsource_subset hH_convex hy₀)
  have hr_le : inner ℝ r (toLp 2 x) ≤ 0 := by
    rcases hr with ⟨r', hr', rfl⟩
    -- The cone part is homogeneous, so the late-row lemma gives the needed nonpositive bound.
    simpa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using
      late_cone_dotProduct_nonpos a k hx hr'
  -- Add the convex-hull and cone estimates to obtain the final pairing bound.
  calc
    inner ℝ (y₀ + r) (toLp 2 x) = inner ℝ y₀ (toLp 2 x) + inner ℝ r (toLp 2 x) := by
      rw [inner_add_left]
    _ ≤ 1 := by
      linarith

/-- Helper for Theorem 3.49: if every nonnegative multiple of `t` is bounded above by `1`, then
`t` is nonpositive. -/
lemma nonpos_of_forall_nonneg_smul_le_one
    (t : ℝ)
    (h : ∀ l : ℝ, 0 ≤ l → l * t ≤ 1) :
    t ≤ 0 := by
  -- A positive `t` would be contradicted by testing the inequality at `λ = 2 / t`.
  by_contra ht
  have ht_pos : 0 < t := lt_of_not_ge ht
  have htest : (2 / t) * t ≤ 1 := h (2 / t) (by positivity)
  have hcalc : (2 / t) * t = (2 : ℝ) := by
    field_simp [ht_pos.ne']
  linarith [hcalc, htest]

/-- Helper for Theorem 3.49: a Farkas multiplier with the mixed right-hand side produces a point of
the convex-hull-plus-cone description. -/
lemma row_multiplier_mem_mixed_hull
    {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    (u : Fin m → ℝ)
    (hu_nonneg : 0 ≤ u)
    (hu_bound : u ⬝ᵥ (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0) ≤ 1) :
    toLp 2 (u ᵥ* a) ∈
      convexHull ℝ ({0} ∪ Set.range (fun i : {j : Fin m // j.1 < k} ↦ toLp 2 (a i.1))) +
        (toLp 2 '' cone (Set.range (fun i : {j : Fin m // k ≤ j.1} ↦ a i.1))) := by
  let early : Fin n → ℝ := fun j : Fin n ↦
    ∑ i : {l : Fin m // l.1 < k}, ((u i.1) * (a i.1 j))
  let late : Fin n → ℝ := fun j : Fin n ↦
    ∑ i : {l : Fin m // k ≤ l.1}, ((u i.1) * (a i.1 j))
  have hsplit : u ᵥ* a = early + late := by
    -- Split the row combination into the early and late index blocks.
    simpa [early, late, Pi.add_apply] using vecMul_split_lt_ge a k u
  have hu_early_bound : ∑ i : {j : Fin m // j.1 < k}, u i.1 ≤ 1 := by
    rw [← dotProduct_mixed_rhs_eq_sum_early k u]
    exact hu_bound
  have hearly :
      toLp 2 early ∈
        convexHull ℝ ({0} ∪ Set.range (fun i : {j : Fin m // j.1 < k} ↦ toLp 2 (a i.1))) := by
    -- The early rows form a convex combination after adding the origin slack.
    exact
      early_row_combination_mem_convexHull a k (fun i ↦ u i.1)
        (fun i ↦ hu_nonneg i.1) hu_early_bound
  have hlate :
      toLp 2 late ∈
        (toLp 2 '' cone (Set.range (fun i : {j : Fin m // k ≤ j.1} ↦ a i.1))) := by
    -- The late rows contribute only a conic combination.
    exact late_row_combination_mem_cone_image a k (fun i ↦ u i.1) (fun i ↦ hu_nonneg i.1)
  refine Set.mem_add.mpr ⟨toLp 2 early, hearly, toLp 2 late, hlate, ?_⟩
  -- Reassemble the early and late pieces into the original multiplier row combination.
  simpa [early, late] using (congrArg (toLp 2) hsplit).symm

/-- Theorem 3.49 (1). For the polyhedron `P` cut out by the inequalities `aⁱ x ≤ 1` for
`i < k` and `aⁱ x ≤ 0` for `i ≥ k`, the one-sided polar `P*` is the convex hull of
`0, a¹, …, aᵏ` plus the cone hull of `aᵏ⁺¹, …, aᵐ`, after the canonical realization of
`ℝ^n` as `EuclideanSpace ℝ (Fin n)`. -/
theorem polar_mixed_rhs_polyhedron_eq_convexHull_add_cone
    {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    ((toLp 2) '' polyhedron_le_set a (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0))* =
      convexHull ℝ ({0} ∪ Set.range (fun i : {j : Fin m // j.1 < k} ↦ toLp 2 (a i.1))) +
        (toLp 2 '' cone (Set.range (fun i : {j : Fin m // k ≤ j.1} ↦ a i.1))) := by
  ext y
  constructor
  · intro hy
    have hvalid :
        is_valid_inequality
          (polyhedron_le_set a (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0))
          (WithLp.ofLp y) 1 := by
      exact
        (mem_polar_image_polyhedron_iff_valid_inequality
          a (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0) y).1 hy
    have hP_nonempty :
        (polyhedron_le_set a (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0)).Nonempty := by
      refine ⟨0, ?_⟩
      intro i
      -- The origin satisfies both the `≤ 1` early inequalities and the `≤ 0` late inequalities.
      by_cases hi : i.1 < k
      · simp [Matrix.mulVec, hi]
      · simp [Matrix.mulVec, hi]
    rcases
        (valid_inequality_iff_exists_nonneg_row_multiplier
          a (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0)
          (WithLp.ofLp y) 1 hP_nonempty).1 hvalid with
      ⟨u, hu_nonneg, hu_eq, hu_bound⟩
    have hu_mem := row_multiplier_mem_mixed_hull a k u hu_nonneg hu_bound
    have hy_eq : toLp 2 (u ᵥ* a) = y := by
      -- The Farkas certificate identifies `y` with the row combination `u ᵥ* a`.
      simpa [WithLp.toLp_ofLp] using congrArg (toLp 2) hu_eq
    simpa [hy_eq] using hu_mem
  · intro hy
    rw [Set.mem_polar_iff]
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    -- The direct pairing estimate proves the reverse inclusion `Q ⊆ P*`.
    exact mixed_hull_pairing_le_one_of_mem_mixed_rhs_polyhedron a k hx hy

/-- Theorem 3.49 (2). For the same sets `P` and `Q`, the one-sided polar `Q*` is the original
polyhedron `P`, again under the canonical Euclidean realization. -/
theorem polar_convexHull_add_cone_eq_mixed_rhs_polyhedron
    {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    (convexHull ℝ ({0} ∪ Set.range (fun i : {j : Fin m // j.1 < k} ↦ toLp 2 (a i.1))) +
        (toLp 2 '' cone (Set.range (fun i : {j : Fin m // k ≤ j.1} ↦ a i.1))))* =
      (toLp 2 '' polyhedron_le_set a (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0)) := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_polar_iff] at hy
    refine ⟨WithLp.ofLp y, ?_, by simp⟩
    intro i
    by_cases hi : i.1 < k
    · have hrow_mem :
          toLp 2 (a i) ∈
            convexHull ℝ ({0} ∪ Set.range (fun j : {l : Fin m // l.1 < k} ↦ toLp 2 (a j.1))) +
              (toLp 2 '' cone (Set.range (fun j : {l : Fin m // k ≤ l.1} ↦ a j.1))) := by
        refine Set.mem_add.mpr ⟨toLp 2 (a i), ?_, 0, ?_, by simp⟩
        · exact
            subset_convexHull ℝ ({0} ∪ Set.range (fun j : {l : Fin m // l.1 < k} ↦ toLp 2 (a j.1)))
              (Or.inr (Set.mem_range_self (⟨i, hi⟩ : {l : Fin m // l.1 < k})))
        · refine ⟨(0 : Fin n → ℝ), cone_zero_mem, ?_⟩
          simp
      have hineq : inner ℝ y (toLp 2 (a i)) ≤ 1 := hy (toLp 2 (a i)) hrow_mem
      -- Testing the early generators recovers the inhomogeneous inequalities `aⁱ x ≤ 1`.
      have hineq_toLp : inner ℝ (toLp 2 (WithLp.ofLp y)) (toLp 2 (a i)) ≤ 1 := by
        simpa using hineq
      have hrow_eval : a i ⬝ᵥ WithLp.ofLp y ≤ 1 := by
        simpa [EuclideanSpace.inner_toLp_toLp] using hineq_toLp
      simpa [Matrix.mulVec, hi] using hrow_eval
    · have hi_ge : k ≤ i.1 := Nat.le_of_not_gt hi
      have hnonpos : (a *ᵥ WithLp.ofLp y) i ≤ 0 := by
        -- Testing every nonnegative scaling of a late generator forces the homogeneous bound
        -- `aⁱ x ≤ 0`.
        apply nonpos_of_forall_nonneg_smul_le_one
        intro l hl
        have hscaled_mem :
            l • toLp 2 (a i) ∈
              convexHull ℝ ({0} ∪ Set.range (fun j : {r : Fin m // r.1 < k} ↦ toLp 2 (a j.1))) +
                (toLp 2 '' cone (Set.range (fun j : {r : Fin m // k ≤ r.1} ↦ a j.1))) := by
          refine Set.mem_add.mpr ⟨0, ?_, l • toLp 2 (a i), ?_, by simp⟩
          · exact
              subset_convexHull ℝ
                ({0} ∪ Set.range (fun j : {r : Fin m // r.1 < k} ↦ toLp 2 (a j.1)))
                (Or.inl rfl)
          · have hbase :
                a i ∈ cone (Set.range (fun j : {r : Fin m // k ≤ r.1} ↦ a j.1)) := by
              exact subset_cone _ (Set.mem_range_self (⟨i, hi_ge⟩ : {r : Fin m // k ≤ r.1}))
            refine ⟨l • a i, cone_smul_mem hbase hl, ?_⟩
            simp
        have hineq : inner ℝ y (l • toLp 2 (a i)) ≤ 1 := hy (l • toLp 2 (a i)) hscaled_mem
        have hineq_toLp : inner ℝ (toLp 2 (WithLp.ofLp y)) (toLp 2 (l • a i)) ≤ 1 := by
          simpa using hineq
        have hscaled_eval₀ : (l • a i) ⬝ᵥ WithLp.ofLp y ≤ 1 := by
          simpa only [EuclideanSpace.inner_toLp_toLp] using hineq_toLp
        have hscaled_eval : l * (a i ⬝ᵥ WithLp.ofLp y) ≤ 1 := by
          simpa [dotProduct, smul_eq_mul, Finset.mul_sum, mul_assoc] using hscaled_eval₀
        simpa [Matrix.mulVec] using hscaled_eval
      simpa [polyhedron_le_set, hi] using hnonpos
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_polar_iff]
    intro z hz
    -- The same pairing estimate also gives the inclusion `P ⊆ Q*`.
    simpa [real_inner_comm] using
      mixed_hull_pairing_le_one_of_mem_mixed_rhs_polyhedron a k hx hz
