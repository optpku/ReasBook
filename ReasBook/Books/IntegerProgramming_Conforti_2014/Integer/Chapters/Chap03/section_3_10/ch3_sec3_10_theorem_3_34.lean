/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_33

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- This file is source-facing, but its owner abstractions are already present earlier in Chapter 3:
-- `polyhedron_le_set`, `linealitySpace`, and `is_pointed` come from the Section 3.6 owner layer,
-- while vertices use mathlib's canonical `Set.extremePoints ℝ`.

section Theorem334

variable {m n : ℕ}

/-- Helper for Theorem 3.34: an extreme point determines a singleton minimal face. -/
lemma singleton_minimalFace_of_mem_extremePoints
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {xbar : Fin n → ℝ}
    (hxext : xbar ∈ (polyhedron_le_set A b).extremePoints ℝ) :
    IsMinimalFaceOf ℝ (polyhedron_le_set A b) ({xbar} : Set (Fin n → ℝ)) := by
  rw [isMinimalFaceOf_iff]
  refine ⟨⟨xbar, rfl⟩, ?_, ?_⟩
  · -- A singleton is an extreme face exactly when its point is an extreme point.
    simpa using (isExtreme_singleton.2 hxext)
  · intro G hG_nonempty _hG_extreme hG_subset
    obtain ⟨z, hzG⟩ := hG_nonempty
    have hzbar : z = xbar := by
      simpa using (hG_subset hzG)
    -- Any nonempty subset of a singleton is the whole singleton.
    intro y hy
    have hybar : y = xbar := by
      simpa using hy
    simpa [hybar, hzbar] using hzG

/-- Helper for Theorem 3.34: a family of `n` linearly independent rows in `ℝ^n` annihilates only
the zero vector. -/
lemma eq_zero_of_linearIndependent_rows_annihilate
    {rows : Fin n → Fin n → ℝ}
    {x : Fin n → ℝ}
    (hrows : LinearIndependent ℝ rows)
    (hann : ∀ i : Fin n, rows i ⬝ᵥ x = 0) :
    x = 0 := by
  by_cases hn : n = 0
  · subst hn
    ext i
    exact Fin.elim0 i
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    have hspan : Submodule.span ℝ (Set.range rows) = ⊤ := by
      -- `n` independent vectors in `ℝ^n` already span the ambient space.
      exact
        hrows.span_eq_top_of_card_eq_finrank
          (by simpa using (Module.finrank_fin_fun ℝ (n := n)).symm)
    have hdot_zero :
        ∀ v ∈ Submodule.span ℝ (Set.range rows), v ⬝ᵥ x = 0 := by
      intro v hv
      -- Extend the rowwise vanishing from the generators to their whole span.
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
      · intro y hy
        rcases hy with ⟨i, rfl⟩
        exact hann i
      · simp
      · intro u w _ _ hu hw
        rw [add_dotProduct, hu, hw]
        simp
      · intro a v _ hv
        rw [smul_dotProduct, hv]
        simp
    ext i
    have hi_mem : Pi.single i (1 : ℝ) ∈ Submodule.span ℝ (Set.range rows) := by
      rw [hspan]
      exact Submodule.mem_top
    -- Testing against the `i`th coordinate vector recovers the `i`th coordinate of `x`.
    have hi_dot : (Pi.single i (1 : ℝ)) ⬝ᵥ x = 0 := hdot_zero (Pi.single i (1 : ℝ)) hi_mem
    have hi_single : (Pi.single i (1 : ℝ)) ⬝ᵥ x = x i := by
      rw [dotProduct, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    exact hi_single.symm.trans hi_dot

/-- Helper for Theorem 3.34: Theorem 3.33 turns the singleton minimal face at a vertex into `n`
active linearly independent rows. -/
lemma exists_active_linearlyIndependent_rows_of_singleton_minimalFace
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {xbar : Fin n → ℝ}
    (hmin : IsMinimalFaceOf ℝ (polyhedron_le_set A b) ({xbar} : Set (Fin n → ℝ))) :
    ∃ I : Fin n ↪ Fin m,
      (∀ i : Fin n, (A *ᵥ xbar) (I i) = b (I i)) ∧
        LinearIndependent ℝ (fun i : Fin n ↦ A (I i)) := by
  classical
  have hface :
      IsExposed ℝ (polyhedron_le_set A b) ({xbar} : Set (Fin n → ℝ)) :=
    minimal_face_isExposed_of_polyhedron A b ({xbar} : Set (Fin n → ℝ)) hmin
  obtain ⟨U, hU_eq, _hU_rank⟩ :=
    (isMinimalFaceOf_iff_exists_eq_submatrix_solution_set_and_rank
      A b ({xbar} : Set (Fin n → ℝ)) hface ⟨xbar, rfl⟩).mp hmin
  let AU : Matrix {i // i ∈ U} (Fin n) ℝ :=
    A.submatrix (Subtype.val : {i // i ∈ U} → Fin m) id
  have hxbar_AU :
      AU *ᵥ xbar = b ∘ (Subtype.val : {i // i ∈ U} → Fin m) := by
    change xbar ∈ {x : Fin n → ℝ | AU *ᵥ x = b ∘ (Subtype.val : {i // i ∈ U} → Fin m)}
    rw [← hU_eq]
    simp
  have hsingleton_eq_translate :
      ({xbar} : Set (Fin n → ℝ)) =
        (AffineSubspace.mk' xbar AU.mulVecLin.ker : Set (Fin n → ℝ)) := by
    -- The singleton equality slice from Theorem 3.33 is exactly the translate of the restricted
    -- kernel through `xbar`.
    calc
      ({xbar} : Set (Fin n → ℝ))
          = {x : Fin n → ℝ | AU *ᵥ x = b ∘ (Subtype.val : {i // i ∈ U} → Fin m)} := hU_eq
      _ = (AffineSubspace.mk' xbar AU.mulVecLin.ker : Set (Fin n → ℝ)) := by
            exact
              matrix_solution_set_eq_translate_ker
                AU
                (b ∘ (Subtype.val : {i // i ∈ U} → Fin m))
                xbar
                hxbar_AU
  have hker_bot : AU.mulVecLin.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro r hr
    have hx_translate :
        xbar + r ∈ (AffineSubspace.mk' xbar AU.mulVecLin.ker : Set (Fin n → ℝ)) := by
      change xbar + r - xbar ∈ AU.mulVecLin.ker
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hr
    have hx_singleton : xbar + r ∈ ({xbar} : Set (Fin n → ℝ)) := by
      simpa [hsingleton_eq_translate] using hx_translate
    have hsum : xbar + r = xbar := by
      simpa using hx_singleton
    have hr_zero : r = 0 := by
      have hsub := congrArg (fun u : Fin n → ℝ ↦ u - xbar) hsum
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    exact hr_zero
  have hAU_rank : AU.rank = n := by
    have hnullity : n - AU.rank = 0 := by
      calc
        n - AU.rank = Module.finrank ℝ AU.mulVecLin.ker := by
          symm
          simpa using finrank_matrix_kernel_eq_card_sub_rank AU
        _ = 0 := by rw [hker_bot]; simp
    have hrank_le : AU.rank ≤ n := by
      simpa using Matrix.rank_le_card_width AU
    omega
  have hspan_top : Submodule.span ℝ (Set.range AU.row) = ⊤ := by
    -- Full row rank upgrades the selected rows to a spanning family of `ℝ^n`.
    apply Submodule.eq_top_of_finrank_eq
    rw [← AU.rank_eq_finrank_span_row, hAU_rank]
    simpa using (Module.finrank_fin_fun ℝ (n := n))
  have hdim : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range AU.row)) = n := by
    rw [hspan_top]
    simpa using (Module.finrank_fin_fun ℝ (n := n))
  obtain ⟨g, hg_mem, _hg_span, hg_linear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range AU.row)
  let e : Fin (Module.finrank ℝ ↥(Submodule.span ℝ (Set.range AU.row))) ≃ Fin n :=
    (Fin.castOrderIso hdim).toEquiv
  let rows : Fin n → Fin n → ℝ := fun i ↦ g (e.symm i)
  have hrows_mem : ∀ i : Fin n, rows i ∈ Set.range AU.row := by
    intro i
    exact hg_mem (e.symm i)
  have hrows_linear : LinearIndependent ℝ rows := by
    exact (linearIndependent_equiv e.symm).2 hg_linear
  have hrows_mem' :
      ∀ i : Fin n, ∃ j : {j // j ∈ U}, AU.row j = rows i := by
    intro i
    simpa [rows] using hrows_mem i
  let chosen : Fin n → {j // j ∈ U} := fun i ↦ Classical.choose (hrows_mem' i)
  have hchosen_row : ∀ i : Fin n, AU.row (chosen i) = rows i := by
    intro i
    exact Classical.choose_spec (hrows_mem' i)
  have hchosen_injective : Function.Injective fun i : Fin n ↦ (chosen i).1 := by
    intro i j hij
    apply hrows_linear.injective
    calc
      rows i = AU.row (chosen i) := (hchosen_row i).symm
      _ = AU.row (chosen j) := by
            have hchosen_eq : chosen i = chosen j := Subtype.ext hij
            simpa [hchosen_eq]
      _ = rows j := hchosen_row j
  let I : Fin n ↪ Fin m := ⟨fun i ↦ (chosen i).1, hchosen_injective⟩
  refine ⟨I, ?_, ?_⟩
  · intro i
    -- Each selected row comes from the equality subsystem defining the singleton face.
    have hi_eq := congrArg (fun v ↦ v (chosen i)) hxbar_AU
    simpa [I, AU, Matrix.mulVec] using hi_eq
  · have hrows :
        (fun i : Fin n ↦ A (I i)) = rows := by
        funext i
        simpa [I, AU, Matrix.row] using hchosen_row i
    simpa [hrows] using hrows_linear

/-- Theorem 3.34 (1). For `P = {x ∈ ℝ^n | A x ≤ b}` and `x̄ ∈ P`, `x̄` is a vertex of `P` if and
only if there are `n` distinct inequalities of `A x ≤ b` that are satisfied at equality by `x̄`
and whose row vectors are linearly independent. In this polyhedral specialization, pointedness is
forced by either side of the equivalence, so it need not be an explicit hypothesis. -/
theorem mem_extremePoints_iff_exists_active_linearlyIndependent_rows
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ polyhedron_le_set A b) :
    xbar ∈ (polyhedron_le_set A b).extremePoints ℝ ↔
      ∃ I : Fin n ↪ Fin m,
        (∀ i : Fin n, (A *ᵥ xbar) (I i) = b (I i)) ∧
          LinearIndependent ℝ (fun i : Fin n ↦ A (I i)) := by
  constructor
  · intro hxext
    have hmin :
        IsMinimalFaceOf ℝ (polyhedron_le_set A b) ({xbar} : Set (Fin n → ℝ)) :=
      singleton_minimalFace_of_mem_extremePoints A b hxext
    -- Theorem 3.33 identifies a singleton minimal face with a full-rank active subsystem.
    exact exists_active_linearlyIndependent_rows_of_singleton_minimalFace A b hmin
  · rintro ⟨I, hactive, hlin⟩
    refine (mem_extremePoints_iff_left).2 ?_
    refine ⟨hxbar, ?_⟩
    intro x hx y hy hseg
    rcases mem_openSegment_iff_div.mp hseg with ⟨a, c, ha, hc, hcomb⟩
    let α : ℝ := a / (a + c)
    let β : ℝ := c / (a + c)
    have hα_pos : 0 < α := by
      dsimp [α]
      positivity
    have hβ_pos : 0 < β := by
      dsimp [β]
      positivity
    have hαβ : α + β = 1 := by
      dsimp [α, β]
      have hden : a + c ≠ 0 := by
        linarith
      field_simp [hden]
    have hx_active_rows : ∀ i : Fin n, (A *ᵥ x) (I i) = b (I i) := by
      intro i
      have hweighted := congrArg (fun z : Fin n → ℝ ↦ (A *ᵥ z) (I i)) hcomb
      have hweighted' :
          α * (A *ᵥ x) (I i) + β * (A *ᵥ y) (I i) = b (I i) := by
        simpa [α, β, hactive i, Matrix.mulVec_add, Matrix.mulVec_smul, mul_comm, mul_left_comm,
          mul_assoc] using hweighted
      -- Feasibility and positivity force equality on every selected active row.
      by_cases hstrict : (A *ᵥ x) (I i) < b (I i)
      · have hx_lt : α * (A *ᵥ x) (I i) < α * b (I i) := by
          exact mul_lt_mul_of_pos_left hstrict hα_pos
        have hy_le : β * (A *ᵥ y) (I i) ≤ β * b (I i) := by
          exact mul_le_mul_of_nonneg_left (hy (I i)) hβ_pos.le
        have hsum_eq : α * b (I i) + β * b (I i) = b (I i) := by
          calc
            α * b (I i) + β * b (I i) = (α + β) * b (I i) := by ring
            _ = b (I i) := by rw [hαβ, one_mul]
        have hlt :
            α * (A *ᵥ x) (I i) + β * (A *ᵥ y) (I i) < b (I i) := by
          calc
            α * (A *ᵥ x) (I i) + β * (A *ᵥ y) (I i)
                < α * b (I i) + β * b (I i) := add_lt_add_of_lt_of_le hx_lt hy_le
            _ = b (I i) := hsum_eq
        linarith
      · exact le_antisymm (hx (I i)) (le_of_not_gt hstrict)
    have hdiff_zero : ∀ i : Fin n, A (I i) ⬝ᵥ (x - xbar) = 0 := by
      intro i
      have hrow :
          (A *ᵥ (x - xbar)) (I i) = 0 := by
        rw [Matrix.mulVec_sub, Pi.sub_apply, hx_active_rows i, hactive i, sub_self]
      simpa [Matrix.mulVec, dotProduct] using hrow
    -- The selected independent rows kill the displacement from `xbar`, so the segment endpoint
    -- must equal `xbar`.
    have hsub_zero : x - xbar = 0 :=
      eq_zero_of_linearIndependent_rows_annihilate hlin hdiff_zero
    exact sub_eq_zero.mp hsub_zero

/-- Theorem 3.34 (2). For `P = {x ∈ ℝ^n | A x ≤ b}` and `x̄ ∈ P`, `x̄` is a vertex of `P` if and
only if `x̄` is not a proper convex combination of two distinct points of `P`. This is the
canonical `Set.mem_extremePoints_iff_left` criterion specialized to `polyhedron_le_set A b`, so no
separate pointedness hypothesis is needed. -/
theorem mem_extremePoints_iff_not_exists_eq_smul_add_smul_of_ne
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ polyhedron_le_set A b) :
    xbar ∈ (polyhedron_le_set A b).extremePoints ℝ ↔
      ¬ ∃ x' ∈ polyhedron_le_set A b, ∃ x'' ∈ polyhedron_le_set A b,
          x' ≠ x'' ∧ xbar ∈ openSegment ℝ x' x'' := by
  constructor
  · intro hxext
    intro hbad
    rcases hbad with ⟨x', hx', x'', hx'', hne, hseg⟩
    have hx'_eq : x' = xbar :=
      (mem_extremePoints_iff_left.mp hxext).2 x' hx' x'' hx'' hseg
    have hx''_eq : x'' = xbar := by
      -- Swapping the segment endpoints gives the symmetric endpoint equality.
      have hseg' : xbar ∈ openSegment ℝ x'' x' := by
        simpa [openSegment_symm] using hseg
      exact (mem_extremePoints_iff_left.mp hxext).2 x'' hx'' x' hx' hseg'
    exact hne (hx'_eq.trans hx''_eq.symm)
  · intro hno
    refine (mem_extremePoints_iff_left).2 ?_
    refine ⟨hxbar, ?_⟩
    intro x hx y hy hseg
    by_contra hx_ne
    have hxy_ne : x ≠ y := by
      intro hxy
      -- If the endpoints coincided, the open segment would collapse to the singleton `{x}`.
      have hxbar_eq_x : xbar = x := by
        simpa [hxy, openSegment_same] using hseg
      exact hx_ne hxbar_eq_x.symm
    exact hno ⟨x, hx, y, hy, hxy_ne, hseg⟩

end Theorem334
