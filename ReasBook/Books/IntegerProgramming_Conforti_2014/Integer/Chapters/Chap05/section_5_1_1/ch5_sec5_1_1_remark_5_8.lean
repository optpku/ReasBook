/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_remark_5_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_1.ch5_sec5_1_1_corollary_5_7

open scoped Matrix SplitHullNotation
open scoped SplitBasisNotation

section Remark58

variable {m n : ℕ}

/-- Helper for high delta sorry cleanup ch5 remark 5 8: extending
coefficients on `B` by zero preserves their left matrix product. -/
lemma supportedBasisVecMul
    (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Finset (Fin m))
    (v : {i // i ∈ B} → ℝ) :
    (fun i : Fin m ↦ if hi : i ∈ B then v ⟨i, hi⟩ else 0) ᵥ* A =
      v ᵥ* basis_row_matrix A B := by
  -- Expand the ambient sum, discard the zero coefficients, and identify the attached sum.
  ext j
  simp only [Matrix.vecMul, dotProduct, basis_row_matrix, Matrix.submatrix_apply, id_eq]
  simpa only [dite_mul, zero_mul] using
    (Finset.sum_attach_eq_sum_dite B (fun i : {i // i ∈ B} ↦ v i * A i.1 j)).symm

/-- Helper for high delta sorry cleanup ch5 remark 5 8: the canonical
reindexing of the rows in `B` presents `P_B` as a standard matrix polyhedron. -/
lemma P_B_eq_reindexedPolyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m)) :
    P_B A b B =
      polyhedron_le_set
        ((basis_row_matrix A B).reindex (Finset.equivFin B) (Equiv.refl _))
        (basis_row_rhs b B ∘ (Finset.equivFin B).symm) := by
  -- Compare the two systems row by row through the canonical finite equivalence.
  ext x
  constructor
  · intro hx k
    exact (mem_P_B_rows_iff A b B x).mp hx
      (((Finset.equivFin B).symm k).1) (((Finset.equivFin B).symm k).2)
  · intro hx
    rw [mem_P_B_rows_iff]
    intro i hi
    have hk := hx ((Finset.equivFin B) ⟨i, hi⟩)
    simpa [basis_row_matrix, basis_row_rhs, Matrix.reindex_apply, Matrix.mulVec, dotProduct]
      using hk

/-- Helper for high delta sorry cleanup ch5 remark 5 8: restricting a
weighted sum to `B` and canonically reindexing it preserves the sum when the weights vanish off
`B`. -/
lemma reindexedBasisDot_eq
    (B : Finset (Fin m))
    (w g : Fin m → ℝ)
    (hw_zero : ∀ i : Fin m, i ∉ B → w i = 0) :
    (fun k : Fin B.card ↦ w ((Finset.equivFin B).symm k).1) ⬝ᵥ
        (fun k : Fin B.card ↦ g ((Finset.equivFin B).symm k).1) =
      w ⬝ᵥ g := by
  -- Undo the equivalence, then restore the omitted zero summands outside `B`.
  change
    Finset.sum Finset.univ
      (fun k : Fin B.card ↦
        w ((Finset.equivFin B).symm k).1 * g ((Finset.equivFin B).symm k).1) =
      Finset.sum Finset.univ (fun i : Fin m ↦ w i * g i)
  calc
    _ = Finset.sum B.attach (fun i ↦ w i.1 * g i.1) := by
          simpa using (Finset.equivFin B).symm.sum_comp
            (fun i : {i // i ∈ B} ↦ w i.1 * g i.1)
    _ = Finset.sum B (fun i : Fin m ↦ w i * g i) := by
          simpa using Finset.sum_attach B (fun i : Fin m ↦ w i * g i)
    _ = Finset.sum Finset.univ (fun i : Fin m ↦ w i * g i) := by
          refine Finset.sum_subset (Finset.subset_univ B) ?_
          intro i _hi hiB
          rw [hw_zero i hiB, zero_mul]

/-- Helper for high delta sorry cleanup ch5 remark 5 8: uniqueness of a row
multiplier supported on `B` forces the rows indexed by `B` to be linearly independent. -/
lemma basisRows_linearIndependent_of_mem_splitBasisFamily
    (A : Matrix (Fin m) (Fin n) ℝ)
    (π : Fin n → ℤ)
    (B : Finset (Fin m))
    (hB : B ∈ 𝓑[A, π]) :
    LinearIndependent ℝ (fun i : {i // i ∈ B} ↦ A i.1) := by
  -- It suffices to show that the restricted left-multiplication map is injective.
  change LinearIndependent ℝ (basis_row_matrix A B).row
  apply (Matrix.vecMul_injective_iff).1
  intro v w hvw
  rcases (mem_𝓑_iff A π B).mp hB with ⟨u, hu, hu_unique⟩
  let d : Fin m → ℝ :=
    fun i ↦ if hi : i ∈ B then v ⟨i, hi⟩ - w ⟨i, hi⟩ else 0
  have hdA : d ᵥ* A = 0 := by
    calc
      d ᵥ* A = (v - w) ᵥ* basis_row_matrix A B := by
        simpa [d] using supportedBasisVecMul A B (v - w)
      _ = v ᵥ* basis_row_matrix A B - w ᵥ* basis_row_matrix A B := by
        rw [Matrix.sub_vecMul]
      _ = 0 := sub_eq_zero.mpr hvw
  have hu_add_d : IsSupportedSplitRowMultiplier A π B (u + d) := by
    -- Adding the restricted kernel vector preserves both the row equation and the support.
    rw [isSupportedSplitRowMultiplier_iff]
    constructor
    · calc
        (u + d) ᵥ* A = u ᵥ* A + d ᵥ* A := by rw [Matrix.add_vecMul]
        _ = (fun j : Fin n ↦ (π j : ℝ)) + 0 := by rw [hu.1, hdA]
        _ = fun j : Fin n ↦ (π j : ℝ) := add_zero _
    · intro i hi
      simp [hu.2 i hi, d, hi]
  have hu_kernel : u + d = u := hu_unique (u + d) hu_add_d
  -- Equality of the extended coefficients recovers equality on every index of `B`.
  funext i
  have hi := congrFun hu_kernel i.1
  simp [d, i.2] at hi
  linarith

/-- Helper for high delta sorry cleanup ch5 remark 5 8: the split-cut value is
unchanged after canonically reindexing a multiplier supported on `B`. -/
lemma splitCutValue_reindexedBasis
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m))
    (u : Fin m → ℝ)
    (π0 : ℤ)
    (x : Fin n → ℝ)
    (hu_zero : ∀ i : Fin m, i ∉ B → u i = 0) :
    split_cut_value
        ((basis_row_matrix A B).reindex (Finset.equivFin B) (Equiv.refl _))
        (basis_row_rhs b B ∘ (Finset.equivFin B).symm)
        (fun k : Fin B.card ↦ u ((Finset.equivFin B).symm k).1) π0 x =
      split_cut_value A b u π0 x := by
  -- First identify the reindexed slack vector and all three dot products in the formula.
  have hslack :
      (basis_row_rhs b B ∘ (Finset.equivFin B).symm) -
          (basis_row_matrix A B).reindex (Finset.equivFin B) (Equiv.refl _) *ᵥ x =
        fun k : Fin B.card ↦ (b - A *ᵥ x) ((Finset.equivFin B).symm k).1 := by
    funext k
    simp [basis_row_rhs, basis_row_matrix, Matrix.reindex_apply, Matrix.mulVec, dotProduct]
  have hpos_zero : ∀ i : Fin m, i ∉ B → row_multiplier_pos u i = 0 := by
    intro i hi
    simp [row_multiplier_pos, hu_zero i hi]
  have hneg_zero : ∀ i : Fin m, i ∉ B → row_multiplier_neg u i = 0 := by
    intro i hi
    simp [row_multiplier_neg, hu_zero i hi]
  have hu_dot :
      (fun k : Fin B.card ↦ u ((Finset.equivFin B).symm k).1) ⬝ᵥ
          (basis_row_rhs b B ∘ (Finset.equivFin B).symm) =
        u ⬝ᵥ b := by
    simpa only [basis_row_rhs, Function.comp_apply] using
      reindexedBasisDot_eq B u b hu_zero
  have hpos_dot :
      row_multiplier_pos (fun k : Fin B.card ↦ u ((Finset.equivFin B).symm k).1) ⬝ᵥ
          ((basis_row_rhs b B ∘ (Finset.equivFin B).symm) -
            (basis_row_matrix A B).reindex (Finset.equivFin B) (Equiv.refl _) *ᵥ x) =
        row_multiplier_pos u ⬝ᵥ (b - A *ᵥ x) := by
    rw [hslack]
    simpa [row_multiplier_pos] using
      reindexedBasisDot_eq B (row_multiplier_pos u) (b - A *ᵥ x) hpos_zero
  have hneg_dot :
      row_multiplier_neg (fun k : Fin B.card ↦ u ((Finset.equivFin B).symm k).1) ⬝ᵥ
          ((basis_row_rhs b B ∘ (Finset.equivFin B).symm) -
            (basis_row_matrix A B).reindex (Finset.equivFin B) (Equiv.refl _) *ᵥ x) =
        row_multiplier_neg u ⬝ᵥ (b - A *ᵥ x) := by
    rw [hslack]
    simpa [row_multiplier_neg] using
      reindexedBasisDot_eq B (row_multiplier_neg u) (b - A *ᵥ x) hneg_zero
  -- Substitution into the two normalized slack terms now closes definitionally.
  unfold split_cut_value
  rw [hpos_dot, hneg_dot, hu_dot]

/-- Helper for high delta sorry cleanup ch5 remark 5 8: when a basic row
multiplier is unique, the basic split-cut system is either its single cut or the ambient
polyhedron, according to whether its right-hand side lies strictly between consecutive integers. -/
lemma basicSplitCutSystem_eq_ite_of_uniqueBasicRowMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (u : Fin m → ℝ)
    (hu_basic : u ∈ basic_row_multiplier_set A π)
    (hu_unique : ∀ v : Fin m → ℝ, v ∈ basic_row_multiplier_set A π → v = u) :
    basic_split_cut_system A b π π0 =
      if (π0 : ℝ) < u ⬝ᵥ b ∧ u ⬝ᵥ b < (π0 : ℝ) + 1 then
        polyhedron_le_set A b ∩
          Set.preimage (split_cut_value A b u π0) (Set.Ici (1 : ℝ))
      else
        polyhedron_le_set A b := by
  by_cases hgap : (π0 : ℝ) < u ⬝ᵥ b ∧ u ⬝ᵥ b < (π0 : ℝ) + 1
  · rw [if_pos hgap]
    ext x
    rw [mem_basic_split_cut_system_iff]
    constructor
    · rintro ⟨hx, hcuts⟩
      exact ⟨hx, hcuts u hu_basic hgap.1 hgap.2⟩
    · rintro ⟨hx, hcut⟩
      refine ⟨hx, ?_⟩
      intro v hv _hleft _hright
      rw [hu_unique v hv]
      exact hcut
  · rw [if_neg hgap]
    ext x
    rw [mem_basic_split_cut_system_iff]
    constructor
    · exact And.left
    · intro hx
      refine ⟨hx, ?_⟩
      intro v hv hleft hright
      have hv_eq : v = u := hu_unique v hv
      rw [hv_eq] at hleft hright
      exact (hgap ⟨hleft, hright⟩).elim

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap05/section_5_1_1/ch5_sec5_1_1_remark_5_8.lean.
Remark 5.8. Let `(π, π₀)` be a split. For a row set `B`, assume `B ∈ 𝓑[A, π]`
and that `ū` is
the supported row multiplier for `B`, so uniqueness is supplied by `𝓑[A, π]`. If
`P_B^(π, π₀) ≠ P_B`, then `P_B^(π, π₀)` is exactly `P_B` intersected with
the split-cut halfspace
defined by `ū`. -/
theorem split_P_B_eq_inter_split_cut
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m))
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (ubar : Fin m → ℝ)
    (hubar : IsSupportedSplitRowMultiplier A π B ubar)
    (hB : B ∈ 𝓑[A, π])
    (hproper : (P_B A b B)^(π, π0) ≠ P_B A b B) :
    (P_B A b B)^(π, π0) =
      P_B A b B ∩
        (split_cut_value A b ubar π0) ⁻¹' Set.Ici (1 : ℝ) := by
  -- Properness first rules out the degenerate zero split on the convex polyhedron `P_B`.
  have hπ : π ≠ 0 := by
    intro hzero
    apply hproper
    calc
      (P_B A b B)^(π, π0) = convexHull ℝ (P_B A b B) := by
        simpa only [hzero, Pi.zero_apply] using
          zero_split_hull_eq_convexHull (P_B A b B) π0
      _ = P_B A b B :=
        convexHull_eq_self.2 (convex_of_is_polyhedron (P_B_is_polyhedron A b B))
  let e : {i // i ∈ B} ≃ Fin B.card := Finset.equivFin B
  let A_B : Matrix (Fin B.card) (Fin n) ℝ :=
    (basis_row_matrix A B).reindex e (Equiv.refl _)
  let b_B : Fin B.card → ℝ := basis_row_rhs b B ∘ e.symm
  let u_B : Fin B.card → ℝ := fun k ↦ ubar (e.symm k).1
  let s := pureSplit ⟨π, hπ⟩ π0
  have hPB_eq : P_B A b B = polyhedron_le_set A_B b_B := by
    simpa [A_B, b_B, e] using P_B_eq_reindexedPolyhedron A b B
  have hRows : LinearIndependent ℝ (fun i : {i // i ∈ B} ↦ A i.1) :=
    basisRows_linearIndependent_of_mem_splitBasisFamily A π B hB
  have hRows_reindexed : LinearIndependent ℝ (fun k : Fin B.card ↦ A_B k) := by
    simpa [A_B, e, basis_row_matrix, Matrix.reindex_apply] using
      hRows.comp e.symm e.symm.injective
  have huB_row : u_B ᵥ* A_B = fun j : Fin n ↦ (π j : ℝ) := by
    -- The supported ambient multiplier retains its row equation after restriction and reindexing.
    ext j
    have hdot := reindexedBasisDot_eq B ubar (fun i : Fin m ↦ A i j) hubar.2
    calc
      (u_B ᵥ* A_B) j = (ubar ᵥ* A) j := by
        simpa [u_B, A_B, e, basis_row_matrix, Matrix.vecMul, dotProduct,
          Matrix.reindex_apply] using hdot
      _ = (π j : ℝ) := congrFun hubar.1 j
  have huB_basic : u_B ∈ basic_row_multiplier_set A_B π := by
    refine (mem_basic_row_multiplier_set_iff A_B π u_B).2 ⟨huB_row, ?_⟩
    -- Independence of all reindexed rows passes to the subfamily on the support of `u_B`.
    rw [RowMultiplierHasIndependentSupportRows]
    exact hRows_reindexed.comp
      (fun i : {k // k ∈ row_multiplier_support u_B} ↦ i.1)
      (fun _ _ h ↦ Subtype.ext h)
  have huB_unique :
      ∀ v : Fin B.card → ℝ, v ∈ basic_row_multiplier_set A_B π → v = u_B := by
    intro v hv
    have hinjective : Function.Injective A_B.vecMul :=
      (Matrix.vecMul_injective_iff).2 hRows_reindexed
    apply hinjective
    exact ((mem_basic_row_multiplier_set_iff A_B π v).mp hv).1.trans huB_row.symm
  have huB_dot : u_B ⬝ᵥ b_B = ubar ⬝ᵥ b := by
    simpa only [u_B, b_B, e, basis_row_rhs, Function.comp_apply] using
      reindexedBasisDot_eq B ubar b hubar.2
  have hcut_eq :
      split_cut_value A_B b_B u_B π0 = split_cut_value A b ubar π0 := by
    -- Package the pointwise finite-sum calculation as equality of the two cut functions.
    funext x
    simpa [A_B, b_B, u_B, e] using
      splitCutValue_reindexedBasis A b B ubar π0 x hubar.2
  have hsplit_eq :
      (P_B A b B)^(π, π0) = basic_split_cut_system A_B b_B π π0 := by
    -- Rewrite `P_B` once and apply Theorem 5.5 to the corresponding pure split.
    rw [hPB_eq]
    simpa [s, pureSplit] using split_polyhedron_eq_basic_split_cut_system A_B b_B s
  have hsystem :=
    basicSplitCutSystem_eq_ite_of_uniqueBasicRowMultiplier
      A_B b_B π π0 u_B huB_basic huB_unique
  have hgap : (π0 : ℝ) < u_B ⬝ᵥ b_B ∧ u_B ⬝ᵥ b_B < (π0 : ℝ) + 1 := by
    -- If the unique multiplier were inactive, Theorem 5.5 would make the split hull all of `P_B`.
    by_contra hnot_gap
    rw [if_neg hnot_gap] at hsystem
    apply hproper
    calc
      (P_B A b B)^(π, π0) = basic_split_cut_system A_B b_B π π0 := hsplit_eq
      _ = polyhedron_le_set A_B b_B := hsystem
      _ = P_B A b B := hPB_eq.symm
  -- The active branch is the desired single halfspace; transport it back to the ambient rows.
  rw [if_pos hgap] at hsystem
  calc
    (P_B A b B)^(π, π0) = basic_split_cut_system A_B b_B π π0 := hsplit_eq
    _ = polyhedron_le_set A_B b_B ∩
        (split_cut_value A_B b_B u_B π0) ⁻¹' Set.Ici (1 : ℝ) := hsystem
    _ = P_B A b B ∩
        (split_cut_value A b ubar π0) ⁻¹' Set.Ici (1 : ℝ) := by
      rw [← hPB_eq, hcut_eq]

/-- A point lies in `P_B^(π, π₀)` exactly when it lies in `P_B` and satisfies the split-cut
inequality defined by the supported row multiplier `ū`. -/
theorem mem_split_P_B_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m))
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (ubar : Fin m → ℝ)
    (hubar : IsSupportedSplitRowMultiplier A π B ubar)
    (hB : B ∈ 𝓑[A, π])
    (hproper : (P_B A b B)^(π, π0) ≠ P_B A b B)
    (x : Fin n → ℝ) :
    x ∈ (P_B A b B)^(π, π0) ↔
      x ∈ P_B A b B ∧ 1 ≤ split_cut_value A b ubar π0 x := by
  rw [split_P_B_eq_inter_split_cut A b B π π0 ubar hubar hB hproper]
  simp

end Remark58
