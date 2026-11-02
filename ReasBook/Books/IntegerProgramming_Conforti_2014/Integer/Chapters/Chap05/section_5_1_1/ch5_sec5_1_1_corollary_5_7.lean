import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_1.ch5_sec5_1_1_corollary_5_7.BasisFamily
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_1.ch5_sec5_1_1_theorem_5_5

open scoped Matrix SplitHullNotation
open scoped SplitBasisNotation

section Corollary57

variable {m n : ℕ}

/-!
The reusable restricted-row polyhedron and split-basis family API for Corollary 5.7 lives in the
item-local foundation module imported above. This file remains the source-facing labeled theorem.
-/

/-- Helper for ch5_sec5_1_1_corollary_5_7: the pure split attached to the nonzero coefficient
vector `π` uses all coordinates as integer coordinates, so the continuous-side vanishing condition
is vacuous. -/
lemma pureSplit_zeroOnContinuous
    (π : {π : Fin n → ℤ // π ≠ 0})
    (_π0 : ℤ) :
    ∀ j ∈ (Finset.univ : Finset (Fin n))ᶜ, π.1 j = 0 := by
  -- The complement of `Finset.univ` is empty, so there are no coordinates to check.
  intro j hj
  simp at hj

/-- Helper for ch5_sec5_1_1_corollary_5_7: package a nonzero pure split vector as a Chapter 5
`Split` over all coordinates. -/
def pureSplit
    (π : {π : Fin n → ℤ // π ≠ 0})
    (π0 : ℤ) :
    Split (Finset.univ : Finset (Fin n)) where
  π := π.1
  π0 := π0
  nonzero := π.2
  zero_on_continuous := pureSplit_zeroOnContinuous π π0

/-- Helper for ch5_sec5_1_1_corollary_5_7: after reindexing the restricted-row system `P_B`
along `Finset.equivFin B`, it is a standard matrix polyhedron. -/
lemma P_B_is_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m)) :
    is_polyhedron (P_B A b B) := by
  -- Reindex the restricted rows to `Fin B.card` so the result matches `polyhedron_le_set`.
  refine ⟨B.card, (basis_row_matrix A B).reindex (Finset.equivFin B) (Equiv.refl _),
    basis_row_rhs b B ∘ (Finset.equivFin B).symm, ?_⟩
  ext x
  constructor
  · intro hx
    change
      (basis_row_matrix A B).reindex (Finset.equivFin B) (Equiv.refl _) *ᵥ x ≤
        basis_row_rhs b B ∘ (Finset.equivFin B).symm
    intro k
    exact (mem_P_B_rows_iff A b B x).mp hx ((Finset.equivFin B).symm k).1
      ((Finset.equivFin B).symm k).2
  · intro hx
    rw [mem_P_B_rows_iff]
    intro i hi
    have hk := hx ((Finset.equivFin B) ⟨i, hi⟩)
    simpa [basis_row_matrix, basis_row_rhs, Matrix.reindex_apply, Matrix.mulVec, dotProduct]
      using hk

/-- Helper for ch5_sec5_1_1_corollary_5_7: split hulls are monotone with respect to the ambient
set. -/
lemma splitHull_mono
    {P Q : Set (Fin n → ℝ)}
    {π : Fin n → ℤ}
    {π0 : ℤ}
    (hPQ : P ⊆ Q) :
    P^(π, π0) ⊆ Q^(π, π0) := by
  -- Lift branch membership through `hPQ`, then apply `convexHull_mono`.
  rw [split_hull, split_hull]
  refine convexHull_mono ?_
  intro x hx
  rcases hx with hx | hx
  · left
    exact (mem_split_branch_lower_iff).2
      ⟨hPQ (mem_split_branch_lower_iff.mp hx).1, (mem_split_branch_lower_iff.mp hx).2⟩
  · right
    exact (mem_split_branch_upper_iff).2
      ⟨hPQ (mem_split_branch_upper_iff.mp hx).1, (mem_split_branch_upper_iff.mp hx).2⟩

/-- Helper for ch5_sec5_1_1_corollary_5_7: every split hull of a polyhedron is contained in the
ambient polyhedron. This is the local specialization of Proposition 5.2 needed for `P_B`. -/
lemma splitHull_subset_of_polyhedron
    (P : Set (Fin n → ℝ))
    (hP : is_polyhedron P)
    (π : Fin n → ℤ)
    (π0 : ℤ) :
    P^(π, π0) ⊆ P := by
  have hP_convex : Convex ℝ P := convex_of_is_polyhedron hP
  rw [split_hull]
  refine convexHull_min ?_ hP_convex
  intro x hx
  rcases hx with hx | hx
  · exact (mem_split_branch_lower_iff.mp hx).1
  · exact (mem_split_branch_upper_iff.mp hx).1

/-- Helper for ch5_sec5_1_1_corollary_5_7: every ambient feasible point stays feasible after
restricting the row system to `B`. -/
lemma polyhedron_subset_P_B
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m)) :
    polyhedron_le_set A b ⊆ P_B A b B := by
  -- A point satisfying every row inequality certainly satisfies the subfamily indexed by `B`.
  intro x hx
  rw [mem_P_B_rows_iff]
  intro i _hi
  exact hx i

/-- Helper for ch5_sec5_1_1_corollary_5_7: a singleton row set belongs to `𝓑[A]` exactly when
its unique row is nonzero. -/
lemma singleton_mem_𝓑_of_row_ne_zero
    (A : Matrix (Fin m) (Fin n) ℝ)
    {i : Fin m}
    (hi : A i ≠ 0) :
    ({i} : Finset (Fin m)) ∈ 𝓑[A] := by
  -- A singleton family is linearly independent as soon as its only vector is nonzero.
  rw [mem_𝓑_split_iff]
  refine (linearIndependent_subsingleton_index_iff (R := ℝ)
    (f := fun j : {j // j ∈ ({i} : Finset (Fin m))} ↦ A j.1)).2 ?_
  intro j
  have hj : j.1 = i := Finset.mem_singleton.mp j.2
  simpa [hj] using hi

/-- Helper for ch5_sec5_1_1_corollary_5_7: if `x` lies in every basis-indexed split hull, then
the singleton-basis rows force `x` back into the ambient polyhedron. -/
lemma memPolyhedron_of_memAllBasisSplitHulls
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP : (polyhedron_le_set A b).Nonempty)
    (π : Fin n → ℤ)
    (π0 : ℤ)
    {x : Fin n → ℝ}
    (hx :
      ∀ B : Finset (Fin m), B ∈ 𝓑[A] → x ∈ (P_B A b B)^(π, π0)) :
    x ∈ polyhedron_le_set A b := by
  -- Check the ambient row inequalities one row at a time.
  intro i
  by_cases hi : A i = 0
  · rcases hP with ⟨y, hy⟩
    have hyi : 0 ≤ b i := by
      simpa [Matrix.mulVec, dotProduct, hi] using hy i
    simpa [Matrix.mulVec, dotProduct, hi] using hyi
  · have hB : ({i} : Finset (Fin m)) ∈ 𝓑[A] := singleton_mem_𝓑_of_row_ne_zero A hi
    have hxB := hx {i} hB
    have hxPB :
        x ∈ P_B A b ({i} : Finset (Fin m)) := by
      -- Strip the split hull down to the underlying singleton-row polyhedron.
      exact splitHull_subset_of_polyhedron (P_B A b ({i} : Finset (Fin m)))
        (P_B_is_polyhedron A b ({i} : Finset (Fin m))) π π0 hxB
    have hrow := (mem_P_B_rows_iff A b ({i} : Finset (Fin m)) x).mp hxPB i (by simp)
    simpa using hrow

/-- Helper for ch5_sec5_1_1_corollary_5_7: the support of a basic row multiplier is a basis row
set and the multiplier is supported there in the explicit `P_B` sense. -/
lemma supportBasisData_of_basicRowMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (π : {π : Fin n → ℤ // π ≠ 0})
    (u : Fin m → ℝ)
    (huBasic : u ∈ basic_row_multiplier_set A π.1) :
    row_multiplier_support u ∈ 𝓑[A] ∧
      IsSupportedSplitRowMultiplier A π.1 (row_multiplier_support u) u := by
  rcases (mem_basic_row_multiplier_set_iff A π.1 u).mp huBasic with ⟨huRow, huIndep⟩
  refine ⟨?_, ?_⟩
  · -- The basic multiplier hypothesis already records linear independence on the support rows.
    simpa [RowMultiplierHasIndependentSupportRows] using huIndep
  · -- Unfold the support package into the row equation and vanishing-off-support statement.
    refine (isSupportedSplitRowMultiplier_iff A π.1 (row_multiplier_support u) u).2 ?_
    refine ⟨huRow, ?_⟩
    intro i hi
    by_contra hu_ne_zero
    exact hi ((mem_row_multiplier_support_iff u i).2 hu_ne_zero)

/-- Helper for ch5_sec5_1_1_corollary_5_7: reindexing the actual support of `u` preserves a
weighted dot product whenever the coefficient vector vanishes off that support. -/
lemma reindexedSupportDot_eq
    (u w g : Fin m → ℝ)
    (hw_zero : ∀ i : Fin m, i ∉ row_multiplier_support u → w i = 0) :
    let B : Finset (Fin m) := row_multiplier_support u
    let e : {i // i ∈ B} ≃ Fin B.card := Finset.equivFin B
    (fun k : Fin B.card ↦ w (e.symm k).1) ⬝ᵥ
        (fun k : Fin B.card ↦ g (e.symm k).1) =
      w ⬝ᵥ g := by
  -- First undo the `Finset.equivFin` reindexing, then restore the dropped zero coordinates.
  dsimp
  change
    Finset.sum Finset.univ
      (fun k : Fin (row_multiplier_support u).card ↦
        w ((Finset.equivFin (row_multiplier_support u)).symm k).1 *
          g ((Finset.equivFin (row_multiplier_support u)).symm k).1) =
      Finset.sum Finset.univ (fun i : Fin m ↦ w i * g i)
  calc
    _ = Finset.sum (row_multiplier_support u).attach (fun i ↦ w i.1 * g i.1) := by
          simpa using (Finset.equivFin (row_multiplier_support u)).symm.sum_comp
            (fun i : {i // i ∈ row_multiplier_support u} ↦ w i.1 * g i.1)
    _ = Finset.sum (row_multiplier_support u) (fun i : Fin m ↦ w i * g i) := by
          simpa using
            Finset.sum_attach (row_multiplier_support u) (fun i : Fin m ↦ w i * g i)
    _ = Finset.sum Finset.univ (fun i : Fin m ↦ if u i ≠ 0 then w i * g i else 0) := by
          rw [row_multiplier_support, Finset.sum_filter]
    _ = Finset.sum Finset.univ (fun i : Fin m ↦ w i * g i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases hiu : u i ≠ 0
          · simp [hiu]
          · have hi_support : i ∉ row_multiplier_support u := by
              simp [row_multiplier_support, hiu]
            simp [hiu, hw_zero i hi_support]
    _ = Finset.sum Finset.univ (fun i : Fin m ↦ w i * g i) := by
          rfl

/-- Corollary 5.7. If `P = {x ∈ ℝ^n | A x ≤ b}` is nonempty, then its split closure is the
intersection of the split closures of the restricted polyhedra `P_B` over all
`B ∈ 𝓑[A]`. -/
theorem split_polyhedron_eq_iInter_P_B
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP : (polyhedron_le_set A b).Nonempty) :
    (polyhedron_le_set A b)^split =
      ⋂ B ∈ 𝓑[A], (P_B A b B)^split := by
  ext x
  constructor
  · intro hx
    have hxSplit :
        ∀ B : Finset (Fin m), B ∈ 𝓑[A] → x ∈ (P_B A b B)^split := by
      intro B hB
      rw [mem_split_closure_iff]
      intro π π0
      -- The easy inclusion uses only `polyhedron_le_set A b ⊆ P_B A b B`.
      exact splitHull_mono (polyhedron_subset_P_B A b B)
        ((mem_split_closure_iff (polyhedron_le_set A b) x).mp hx π π0)
    simpa [Set.mem_iInter] using hxSplit
  · intro hx
    rw [mem_split_closure_iff]
    intro π π0
    have hxInter :
        ∀ B : Finset (Fin m), B ∈ 𝓑[A] → x ∈ (P_B A b B)^split := by
      simpa [Set.mem_iInter] using hx
    have hxAll :
        ∀ B : Finset (Fin m), B ∈ 𝓑[A] → x ∈ (P_B A b B)^(π.1, π0) := by
      intro B hB
      have hxB : x ∈ (P_B A b B)^split := hxInter B hB
      exact (mem_split_closure_iff (P_B A b B) x).mp hxB π π0
    have hxPoly : x ∈ polyhedron_le_set A b :=
      memPolyhedron_of_memAllBasisSplitHulls A b hP π.1 π0 hxAll
    -- Route correction: prove the ambient cut inequality by transporting the fixed split to the
    -- support-restricted system of the chosen basic multiplier and applying Theorem 5.5 there.
    let s := pureSplit π π0
    have hxSplit : x ∈ split_polyhedron A b s := by
      rw [split_polyhedron_eq_basic_split_cut_system A b s]
      refine (mem_basic_split_cut_system_iff A b s s.π0 x).2 ?_
      refine ⟨hxPoly, ?_⟩
      intro u huBasic hub_left hub_right
      let B : Finset (Fin m) := row_multiplier_support u
      have hBasisData := supportBasisData_of_basicRowMultiplier A π u huBasic
      have hB : B ∈ 𝓑[A] := by
        simpa [B] using hBasisData.1
      let e : {i // i ∈ B} ≃ Fin B.card := Finset.equivFin B
      let A_B : Matrix (Fin B.card) (Fin n) ℝ :=
        (basis_row_matrix A B).reindex e (Equiv.refl _)
      let b_B : Fin B.card → ℝ := basis_row_rhs b B ∘ e.symm
      let u_B : Fin B.card → ℝ := fun k ↦ u (e.symm k).1
      have hPB_eq : P_B A b B = polyhedron_le_set A_B b_B := by
        -- Reindex the restricted rows to `Fin B.card` once so the Chapter 5 matrix API applies.
        ext y
        constructor
        · intro hy k
          exact (mem_P_B_rows_iff A b B y).mp hy ((e.symm k).1) ((e.symm k).2)
        · intro hy
          rw [mem_P_B_rows_iff]
          intro i hi
          have hk := hy (e ⟨i, hi⟩)
          simpa [A_B, b_B, e, basis_row_matrix, basis_row_rhs, Matrix.reindex_apply,
            Matrix.mulVec, dotProduct] using hk
      have hxRestricted :
          x ∈ split_polyhedron A_B b_B s := by
        refine (mem_split_polyhedron_iff).2 ?_
        simpa [s, pureSplit, hPB_eq] using hxAll B hB
      have huB_basic :
          u_B ∈ basic_row_multiplier_set A_B s := by
        -- The support-restricted multiplier keeps the same split row and now has full support.
        refine (mem_basic_row_multiplier_set_iff A_B s u_B).2 ?_
        constructor
        · -- The left multiplication is just the ambient row equation summed over the true support.
          ext j
          have huRow : u ᵥ* A = fun j : Fin n ↦ (π.1 j : ℝ) := hBasisData.2.1
          have huB_row :
              (u_B ᵥ* A_B) j = (u ᵥ* A) j := by
            simpa [u_B, A_B, e, basis_row_matrix, dotProduct, Matrix.reindex_apply] using
              reindexedSupportDot_eq u u (fun i : Fin m ↦ A i j) (fun i hi ↦ hBasisData.2.2 i hi)
          exact huB_row.trans (congrFun huRow j)
        · have hRows :
              LinearIndependent ℝ (fun i : {i // i ∈ B} ↦ basis_row_matrix A B i) := by
            simpa [basis_row_matrix] using (mem_𝓑_split_iff A B).mp hB
          have hRows_reindexed :
              LinearIndependent ℝ (fun k : Fin B.card ↦ A_B k) := by
            simpa [A_B, e, Matrix.reindex_apply] using hRows.comp e.symm e.symm.injective
          have huB_nonzero : ∀ k : Fin B.card, u_B k ≠ 0 := by
            intro k
            simpa [u_B] using (mem_row_multiplier_support_iff u ((e.symm k).1)).1 ((e.symm k).2)
          have huB_support :
              row_multiplier_support u_B = Finset.univ := by
            ext k
            simp [row_multiplier_support, u_B, huB_nonzero k]
          rw [RowMultiplierHasIndependentSupportRows, huB_support]
          exact hRows_reindexed.comp (fun i : {k // k ∈ (Finset.univ : Finset (Fin B.card))} ↦ i.1)
            (fun _ _ h => Subtype.ext h)
      have huB_dot :
          u_B ⬝ᵥ b_B = u ⬝ᵥ b := by
        -- The restricted right-hand side is just the ambient one summed over the support of `u`.
        change
          (fun k : Fin B.card ↦ u (e.symm k).1) ⬝ᵥ (fun k : Fin B.card ↦ b (e.symm k).1) =
            u ⬝ᵥ b
        simpa [B, e] using
          reindexedSupportDot_eq u u b (fun i hi ↦ hBasisData.2.2 i (by simpa [B] using hi))
      have hcutRestricted :
          split_cut_value A_B b_B u_B s.π0 x =
            split_cut_value A b u s.π0 x := by
        -- Both normalized slack terms are unchanged by restricting to the actual support of `u`.
        have hslack :
            b_B - A_B *ᵥ x = fun k : Fin B.card ↦ (b - A *ᵥ x) ((e.symm k).1) := by
          funext k
          simp [b_B, A_B, e, basis_row_rhs, basis_row_matrix, Matrix.reindex_apply,
            Matrix.mulVec, dotProduct]
        have hpos_zero :
            ∀ i : Fin m, i ∉ row_multiplier_support u → row_multiplier_pos u i = 0 := by
          intro i hi
          have hui : u i = 0 := hBasisData.2.2 i hi
          simp [row_multiplier_pos, hui]
        have hneg_zero :
            ∀ i : Fin m, i ∉ row_multiplier_support u → row_multiplier_neg u i = 0 := by
          intro i hi
          have hui : u i = 0 := hBasisData.2.2 i hi
          simp [row_multiplier_neg, hui]
        have hpos_dot :
            row_multiplier_pos u_B ⬝ᵥ (b_B - A_B *ᵥ x) =
              row_multiplier_pos u ⬝ᵥ (b - A *ᵥ x) := by
          rw [hslack]
          simpa [u_B, e, row_multiplier_pos] using
            reindexedSupportDot_eq u (row_multiplier_pos u) (b - A *ᵥ x) hpos_zero
        have hneg_dot :
            row_multiplier_neg u_B ⬝ᵥ (b_B - A_B *ᵥ x) =
              row_multiplier_neg u ⬝ᵥ (b - A *ᵥ x) := by
          rw [hslack]
          simpa [u_B, e, row_multiplier_neg] using
            reindexedSupportDot_eq u (row_multiplier_neg u) (b - A *ᵥ x) hneg_zero
        simp [split_cut_value, hpos_dot, hneg_dot, huB_dot]
      have hcutB :
          1 ≤ split_cut_value A_B b_B u_B s.π0 x := by
        have hub_left_B : (s.π0 : ℝ) < u_B ⬝ᵥ b_B := by
          simpa [s, pureSplit, huB_dot] using hub_left
        have hub_right_B : u_B ⬝ᵥ b_B < (s.π0 : ℝ) + 1 := by
          simpa [s, pureSplit, huB_dot] using hub_right
        exact validSplitCutValue_of_memSplitPolyhedron
          A_B b_B s hxRestricted u_B huB_basic hub_left_B hub_right_B
      have hcutAmbient : 1 ≤ split_cut_value A b u π0 x := by
        calc
          1 ≤ split_cut_value A_B b_B u_B s.π0 x := hcutB
          _ = split_cut_value A b u π0 x := by
              simpa [s, pureSplit] using hcutRestricted
      exact hcutAmbient
    have hxSplit' : x ∈ (polyhedron_le_set A b)^(s, s.π0) :=
      (mem_split_polyhedron_iff).1 hxSplit
    simpa [s, pureSplit] using hxSplit'

end Corollary57
