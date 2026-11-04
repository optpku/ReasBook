/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_example_3_36
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_definition_3_15_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_26
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10_1.ch4_sec4_10_1_lemma_4_53
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10_1.ch4_sec4_10_1_theorem_4_54
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10_2.ch4_sec4_10_2_lemma_4_55
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_corollary_4_44
import Mathlib.Data.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix
open scoped Matrix UniqueDisjointnessMatrixNotation

noncomputable section

/-- Helper for Theorem 4.57: the canonical reindexing from `Fin`-indexed cut coordinates to the
edge-coordinate model of `K_{n+1}`. -/
private noncomputable abbrev cut_coordinate_reindex (n : ℕ) :
    (Fin (Fintype.card (complete_graph_edges (n + 1))) → ℝ) ≃ₗ[ℝ]
      (complete_graph_edges (n + 1) → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (complete_graph_edges (n + 1)))

/-- Helper for Theorem 4.57: the forward cut-coordinate reindexing evaluates at the corresponding
edge coordinate. -/
@[simp] private theorem cut_coordinate_reindex_apply
    (n : ℕ) (x : Fin (Fintype.card (complete_graph_edges (n + 1))) → ℝ)
    (e : complete_graph_edges (n + 1)) :
    cut_coordinate_reindex n x e = x ((Fintype.equivFin (complete_graph_edges (n + 1))) e) := by
  -- The coordinate change is the standard `funCongrLeft` evaluation formula.
  simp [cut_coordinate_reindex]

/-- Helper for Theorem 4.57: the inverse cut-coordinate reindexing recovers the original edge
coordinate at the corresponding `Fin` index. -/
@[simp] private theorem cut_coordinate_reindex_symm_apply
    (n : ℕ) (x : complete_graph_edges (n + 1) → ℝ)
    (j : Fin (Fintype.card (complete_graph_edges (n + 1)))) :
    (cut_coordinate_reindex n).symm x j =
      x ((Fintype.equivFin (complete_graph_edges (n + 1))).symm j) := by
  -- This is the inverse evaluation formula for the same `funCongrLeft` equivalence.
  simp [cut_coordinate_reindex]

/-- Helper for Theorem 4.57: reindexing rows and columns along finite equivalences commutes with
matrix-vector multiplication. -/
private theorem reindexed_mulVec_apply
    {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ)
    (eα : α ≃ Fin (Fintype.card α))
    (eβ : β ≃ Fin (Fintype.card β))
    (x : Fin (Fintype.card β) → ℝ) :
    Matrix.reindex eα eβ A *ᵥ x =
      fun i ↦ (A *ᵥ ((LinearEquiv.funCongrLeft ℝ ℝ eβ) x)) (eα.symm i) := by
  -- Evaluate the canonical `mulVec` reindexing identity on the given vector.
  have hlin :=
    congrArg
      (fun T :
          (Fin (Fintype.card β) → ℝ) →ₗ[ℝ] Fin (Fintype.card α) → ℝ ↦
        T x)
      (Matrix.mulVecLin_reindex (R := ℝ) eα eβ A)
  simpa using hlin

/-- Helper for Theorem 4.57: reindexing the ambient cut coordinates transports a linear extended
formulation to the canonical `Fin`-coordinate model with the same row counts. -/
private theorem cut_coordinate_reindex_image_linear_extended_formulation
    (n : ℕ)
    {κ ρ σ : Type*}
    [Fintype κ] [Fintype ρ] [Fintype σ]
    (Aeq : Matrix ρ (complete_graph_edges (n + 1)) ℝ)
    (Beq : Matrix ρ κ ℝ)
    (beq : ρ → ℝ)
    (Aineq : Matrix σ (complete_graph_edges (n + 1)) ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ) :
    (cut_coordinate_reindex n).symm ''
        (Prod.fst '' linear_extended_system Aeq Beq beq Aineq Bineq bineq) =
      Prod.fst ''
        linear_extended_system
          (Matrix.reindex (Fintype.equivFin ρ)
            (Fintype.equivFin (complete_graph_edges (n + 1))) Aeq)
          (Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq)
          (fun i ↦ beq ((Fintype.equivFin ρ).symm i))
          (Matrix.reindex (Fintype.equivFin σ)
            (Fintype.equivFin (complete_graph_edges (n + 1))) Aineq)
          (Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq)
          (fun i ↦ bineq ((Fintype.equivFin σ).symm i)) := by
  -- Unfold both formulations and transport the auxiliary witness through the canonical `Fin`
  -- reindexings on the ambient and auxiliary coordinates.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_image_fst_iff] at hy
    rcases hy with ⟨z, hz⟩
    rcases (mem_linear_extended_system_iff.mp hz) with ⟨hzEq, hzLe⟩
    let zFin :=
      (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)).symm z
    have hyTransport :
        (LinearEquiv.funCongrLeft ℝ ℝ
            (Fintype.equivFin (complete_graph_edges (n + 1))))
          ((cut_coordinate_reindex n).symm y) = y := by
      -- The ambient cut-coordinate equivalence cancels with its inverse.
      simpa [cut_coordinate_reindex] using
        (cut_coordinate_reindex n).apply_symm_apply y
    have hzTransport :
        (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)) zFin = z := by
      -- The auxiliary-coordinate equivalence cancels in the same way.
      simpa [zFin] using
        (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)).apply_symm_apply z
    have hAeq :
        Matrix.reindex (Fintype.equivFin ρ)
            (Fintype.equivFin (complete_graph_edges (n + 1))) Aeq *ᵥ
            ((cut_coordinate_reindex n).symm y) =
          fun i ↦ (Aeq *ᵥ y) ((Fintype.equivFin ρ).symm i) := by
      -- Reindexing the cut coordinates only permutes the ambient variables.
      calc
        Matrix.reindex (Fintype.equivFin ρ)
            (Fintype.equivFin (complete_graph_edges (n + 1))) Aeq *ᵥ
            ((cut_coordinate_reindex n).symm y) =
          fun i ↦
            (Aeq *ᵥ
              ((LinearEquiv.funCongrLeft ℝ ℝ
                (Fintype.equivFin (complete_graph_edges (n + 1))))
                  ((cut_coordinate_reindex n).symm y)))
              ((Fintype.equivFin ρ).symm i) := by
            exact reindexed_mulVec_apply
              Aeq
              (Fintype.equivFin ρ)
              (Fintype.equivFin (complete_graph_edges (n + 1)))
              ((cut_coordinate_reindex n).symm y)
        _ = fun i ↦ (Aeq *ᵥ y) ((Fintype.equivFin ρ).symm i) := by
            rw [hyTransport]
    have hBeq :
        Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq *ᵥ zFin =
          fun i ↦ (Beq *ᵥ z) ((Fintype.equivFin ρ).symm i) := by
      -- The same reindexing identity transports the auxiliary witness.
      calc
        Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq *ᵥ zFin =
          fun i ↦
            (Beq *ᵥ
              ((LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)) zFin))
              ((Fintype.equivFin ρ).symm i) := by
            exact reindexed_mulVec_apply Beq (Fintype.equivFin ρ) (Fintype.equivFin κ) zFin
        _ = fun i ↦ (Beq *ᵥ z) ((Fintype.equivFin ρ).symm i) := by
            rw [hzTransport]
    have hAineq :
        Matrix.reindex (Fintype.equivFin σ)
            (Fintype.equivFin (complete_graph_edges (n + 1))) Aineq *ᵥ
            ((cut_coordinate_reindex n).symm y) =
          fun i ↦ (Aineq *ᵥ y) ((Fintype.equivFin σ).symm i) := by
      -- The inequality block behaves identically under the ambient reindexing.
      calc
        Matrix.reindex (Fintype.equivFin σ)
            (Fintype.equivFin (complete_graph_edges (n + 1))) Aineq *ᵥ
            ((cut_coordinate_reindex n).symm y) =
          fun i ↦
            (Aineq *ᵥ
              ((LinearEquiv.funCongrLeft ℝ ℝ
                (Fintype.equivFin (complete_graph_edges (n + 1))))
                  ((cut_coordinate_reindex n).symm y)))
              ((Fintype.equivFin σ).symm i) := by
            exact reindexed_mulVec_apply
              Aineq
              (Fintype.equivFin σ)
              (Fintype.equivFin (complete_graph_edges (n + 1)))
              ((cut_coordinate_reindex n).symm y)
        _ = fun i ↦ (Aineq *ᵥ y) ((Fintype.equivFin σ).symm i) := by
            rw [hyTransport]
    have hBineq :
        Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq *ᵥ zFin =
          fun i ↦ (Bineq *ᵥ z) ((Fintype.equivFin σ).symm i) := by
      -- Reindexing the auxiliary coordinates also preserves the inequality rows.
      calc
        Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq *ᵥ zFin =
          fun i ↦
            (Bineq *ᵥ
              ((LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)) zFin))
              ((Fintype.equivFin σ).symm i) := by
            exact reindexed_mulVec_apply Bineq (Fintype.equivFin σ) (Fintype.equivFin κ) zFin
        _ = fun i ↦ (Bineq *ᵥ z) ((Fintype.equivFin σ).symm i) := by
            rw [hzTransport]
    rw [mem_image_fst_iff]
    refine ⟨zFin, ?_⟩
    have hzFin_mem :
        Matrix.reindex (Fintype.equivFin ρ)
            (Fintype.equivFin (complete_graph_edges (n + 1))) Aeq *ᵥ
            ((cut_coordinate_reindex n).symm y) +
          Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq *ᵥ zFin =
            (fun i ↦ beq ((Fintype.equivFin ρ).symm i)) ∧
        Matrix.reindex (Fintype.equivFin σ)
            (Fintype.equivFin (complete_graph_edges (n + 1))) Aineq *ᵥ
            ((cut_coordinate_reindex n).symm y) +
          Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq *ᵥ zFin ≤
            fun i ↦ bineq ((Fintype.equivFin σ).symm i) := by
      constructor
      · -- The equality rows are just the original ones, read through the row equivalence.
        ext i
        simp only [Pi.add_apply, hAeq, hBeq]
        exact congrFun hzEq ((Fintype.equivFin ρ).symm i)
      · -- The inequality rows are transported in the same way.
        intro i
        simp only [Pi.add_apply, hAineq, hBineq]
        exact hzLe ((Fintype.equivFin σ).symm i)
    exact mem_linear_extended_system_iff.mpr hzFin_mem
  · intro hx
    rw [mem_image_fst_iff] at hx
    rcases hx with ⟨zFin, hz⟩
    rcases (mem_linear_extended_system_iff.mp hz) with ⟨hzEq, hzLe⟩
    let y := cut_coordinate_reindex n x
    let z := (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin κ)) zFin
    have hyx : (cut_coordinate_reindex n).symm y = x := by
      -- The chosen image witness maps back to the original `Fin`-indexed point.
      simpa [y, cut_coordinate_reindex] using
        (cut_coordinate_reindex n).symm_apply_apply x
    have hAeq :
        ∀ i : ρ,
          (Aeq *ᵥ y) i =
            (Matrix.reindex (Fintype.equivFin ρ)
              (Fintype.equivFin (complete_graph_edges (n + 1))) Aeq *ᵥ x)
              ((Fintype.equivFin ρ) i) := by
      -- Reading the reindexed equality system at the corresponding row recovers the original row.
      intro i
      have h :=
        congrFun
          (reindexed_mulVec_apply
            Aeq
            (Fintype.equivFin ρ)
            (Fintype.equivFin (complete_graph_edges (n + 1)))
            x)
          ((Fintype.equivFin ρ) i)
      simpa [y, cut_coordinate_reindex] using h.symm
    have hBeq :
        ∀ i : ρ,
          (Beq *ᵥ z) i =
            (Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq *ᵥ zFin)
              ((Fintype.equivFin ρ) i) := by
      -- The same pointwise recovery works for the auxiliary equality block.
      intro i
      have h :=
        congrFun
          (reindexed_mulVec_apply Beq (Fintype.equivFin ρ) (Fintype.equivFin κ) zFin)
          ((Fintype.equivFin ρ) i)
      simpa [z] using h.symm
    have hAineq :
        ∀ i : σ,
          (Aineq *ᵥ y) i =
            (Matrix.reindex (Fintype.equivFin σ)
              (Fintype.equivFin (complete_graph_edges (n + 1))) Aineq *ᵥ x)
              ((Fintype.equivFin σ) i) := by
      -- Reading the reindexed inequality system at the matching row gives back the original row.
      intro i
      have h :=
        congrFun
          (reindexed_mulVec_apply
            Aineq
            (Fintype.equivFin σ)
            (Fintype.equivFin (complete_graph_edges (n + 1)))
            x)
          ((Fintype.equivFin σ) i)
      simpa [y, cut_coordinate_reindex] using h.symm
    have hBineq :
        ∀ i : σ,
          (Bineq *ᵥ z) i =
            (Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq *ᵥ zFin)
              ((Fintype.equivFin σ) i) := by
      -- The auxiliary inequality block is recovered pointwise in exactly the same way.
      intro i
      have h :=
        congrFun
          (reindexed_mulVec_apply Bineq (Fintype.equivFin σ) (Fintype.equivFin κ) zFin)
          ((Fintype.equivFin σ) i)
      simpa [z] using h.symm
    refine ⟨y, ?_, hyx⟩
    rw [mem_image_fst_iff]
    refine ⟨z, ?_⟩
    have hz_mem :
        Aeq *ᵥ y + Beq *ᵥ z = beq ∧
          Aineq *ᵥ y + Bineq *ᵥ z ≤ bineq := by
      constructor
      · -- Evaluating the transported equality system at the original row indices recovers `hzEq`.
        ext i
        rw [Pi.add_apply, hAeq i, hBeq i]
        simpa using congrFun hzEq ((Fintype.equivFin ρ) i)
      · -- The transported inequalities specialize to the original inequality system rowwise.
        intro i
        rw [Pi.add_apply, hAineq i, hBineq i]
        simpa using hzLe ((Fintype.equivFin σ) i)
    exact mem_linear_extended_system_iff.mpr hz_mem

/-- Helper for Theorem 4.57: the `0/1` indicator vector of a finite subset of `Fin n`. -/
private noncomputable def finset_indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i ↦ if i ∈ S then (1 : ℝ) else 0

/-- Helper for Theorem 4.57: the correlation inequality matrix `2 Diag(a) - aaᵀ`. -/
private def correlation_cut_matrix {n : ℕ} (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ) • Matrix.diagonal a - Matrix.vecMulVec a a

/-- Helper for Theorem 4.57: rowizing a linear functional by evaluating it on the coordinate basis
recovers the original functional after taking a dot product. -/
private theorem functional_row_dot_eq
    {d : ℕ} (ℓ : (Fin d → ℝ) →ₗ[ℝ] ℝ) (x : Fin d → ℝ) :
    (fun j ↦ ℓ (Pi.single j (1 : ℝ))) ⬝ᵥ x = ℓ x := by
  have hx :
      x = ∑ j : Fin d, x j • Pi.single j (1 : ℝ) := by
    -- Expand the vector in the standard basis of coordinate vectors.
    ext i
    simp [Pi.single_apply]
  -- Linearize the coordinate expansion term by term.
  have hx' :
      (∑ j : Fin d, x j • Pi.single j (1 : ℝ)) = x := by
    exact hx.symm
  have hlin : ∑ j : Fin d, x j * ℓ (Pi.single j (1 : ℝ)) = ℓ x := by
    calc
      ∑ j : Fin d, x j * ℓ (Pi.single j (1 : ℝ))
          = ℓ (∑ j : Fin d, x j • Pi.single j (1 : ℝ)) := by
            rw [map_sum]
            simp [smul_eq_mul]
      _ = ℓ x := by rw [hx']
  calc
    (fun j ↦ ℓ (Pi.single j (1 : ℝ))) ⬝ᵥ x
        = ∑ j : Fin d, x j * ℓ (Pi.single j (1 : ℝ)) := by
            simp [dotProduct, mul_comm]
    _ = ℓ x := hlin

/-- Helper for Theorem 4.57: each coordinate of a `0/1` vector is idempotent. -/
private theorem zero_one_vector_sq_eq_self
    {n : ℕ} {b : Fin n → ℝ} (hb : is_zero_one_vector b) (i : Fin n) :
    b i ^ 2 = b i := by
  -- Every coordinate is either `0` or `1`, so squaring leaves it unchanged.
  rcases hb i with hbi | hbi
  · rw [hbi]
    norm_num
  · rw [hbi]
    norm_num

/-- Helper for Theorem 4.57: the diagonal part of `2 Diag(a) - aaᵀ` pairs with `bbᵀ`
as `aᵀb` when `b` is `0/1`. -/
private theorem diagonal_vecMulVec_trace_eq_dotProduct
    {n : ℕ} (a b : Fin n → ℝ) (hb : is_zero_one_vector b) :
    Matrix.trace (Matrix.diagonal a * Matrix.vecMulVec b b) = a ⬝ᵥ b := by
  -- Rewrite the trace of the diagonal-times-rank-one product as a coordinate sum.
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  unfold dotProduct
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Matrix.mulVec_diagonal, mul_assoc]
  calc
    a i * (b i * b i) = a i * b i ^ 2 := by rw [pow_two]
    _ = a i * b i := by rw [zero_one_vector_sq_eq_self hb i]

/-- Helper for Theorem 4.57: the trace of `aaᵀbbᵀ` is `(aᵀb)^2`. -/
private theorem vecMulVec_mul_vecMulVec_trace_eq_dotProduct_sq
    {n : ℕ} (a b : Fin n → ℝ) :
    Matrix.trace (Matrix.vecMulVec a a * Matrix.vecMulVec b b) = (a ⬝ᵥ b) ^ 2 := by
  -- Rank-one multiplication collapses to the square of the scalar pairing.
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul, smul_eq_mul,
    pow_two]

/-- Helper for Theorem 4.57: the indicator of a finite subset is a `0/1` vector. -/
private theorem finset_indicator_is_zero_one_vector
    {n : ℕ} (S : Finset (Fin n)) :
    is_zero_one_vector (finset_indicator S) := by
  -- Each indicator coordinate is definitionally `0` or `1`.
  intro i
  by_cases hi : i ∈ S
  · right
    simp [finset_indicator, hi]
  · left
    simp [finset_indicator, hi]

/-- Helper for Theorem 4.57: a correlation vertex matrix is the rank-one matrix of its indicator
vector. -/
private theorem correlation_vertex_matrix_eq_vecMulVec_indicator
    {n : ℕ} (S : Finset (Fin n)) :
    (correlation_vertex S).toMatrix =
      Matrix.vecMulVec (finset_indicator S) (finset_indicator S) := by
  -- Both sides have the same entrywise indicator-product formula.
  ext i j
  simp [correlationSpace.toMatrix, correlation_vertex, correlation_vertex_matrix, finset_indicator,
    Matrix.vecMulVec]

/-- Helper for Theorem 4.57: every correlation-space point satisfying the vertex hull description
also satisfies the transported correlation-cut inequality. -/
private theorem correlation_cut_inequality_valid
    {n : ℕ} (a : Fin n → ℝ) {Y : correlationSpace n} (hY : Y ∈ correlationPolytope n) :
    Matrix.trace (correlation_cut_matrix a * Y.toMatrix) ≤ 1 := by
  have hHull : Y ∈ convexHull ℝ (correlationVertices n) := by
    -- The correlation polytope is defined as the convex hull of its rank-one vertices.
    simpa [correlationPolytope_eq_convexHull] using hY
  have hvertices :
      correlationVertices n ⊆
        {Z : correlationSpace n |
          Matrix.trace (correlation_cut_matrix a * Z.toMatrix) ≤ 1} := by
    -- It is enough to check the inequality on the generating vertices.
    rintro _ ⟨S, rfl⟩
    let b : Fin n → ℝ := finset_indicator S
    have hb : is_zero_one_vector b := finset_indicator_is_zero_one_vector S
    have hmatrix :
        (correlation_vertex S).toMatrix = Matrix.vecMulVec b b :=
      correlation_vertex_matrix_eq_vecMulVec_indicator S
    have hslack :
        1 - Matrix.trace (correlation_cut_matrix a * (correlation_vertex S).toMatrix) =
          (1 - a ⬝ᵥ b) ^ 2 := by
      -- The source slack computation specializes to the indicator vector of `S`.
      rw [hmatrix]
      simp only [correlation_cut_matrix]
      rw [sub_mul, Matrix.trace_sub, smul_mul_assoc, Matrix.trace_smul,
        diagonal_vecMulVec_trace_eq_dotProduct a b hb,
        vecMulVec_mul_vecMulVec_trace_eq_dotProduct_sq]
      ring
    have hsq : 0 ≤ (1 - a ⬝ᵥ b) ^ 2 := sq_nonneg (1 - a ⬝ᵥ b)
    -- Nonnegativity of the slack rearranges to the desired upper bound.
    have hineq :
        Matrix.trace (correlation_cut_matrix a * (correlation_vertex S).toMatrix) ≤ 1 := by
      nlinarith [hslack, hsq]
    exact hineq
  -- Convexity of the halfspace lifts the inequality from the vertices to the whole hull.
  exact (convexHull_min hvertices <|
    by
      let traceLinear : correlationSpace n →ₗ[ℝ] ℝ :=
        { toFun := fun Z ↦ Matrix.trace (correlation_cut_matrix a * Z.toMatrix)
          map_add' := by
            -- The trace pairing is linear in the correlation-space argument.
            intro Z W
            simp [correlationSpace.toMatrix, Matrix.mul_add, Matrix.trace_add]
          map_smul' := by
            -- Scalar multiplication passes through multiplication and trace.
            intro c Z
            simp [correlationSpace.toMatrix, Matrix.trace_smul] }
      have hsublevel :
          {Z : correlationSpace n |
              Matrix.trace (correlation_cut_matrix a * Z.toMatrix) ≤ 1} =
            traceLinear ⁻¹' Set.Iic (1 : ℝ) := by
        -- Rewrite the inequality set as a linear preimage of a convex interval.
        ext Z
        simp [traceLinear, Set.mem_Iic]
      rw [hsublevel]
      exact (convex_Iic (1 : ℝ)).linear_preimage traceLinear) hHull

/-- Helper for Theorem 4.57: the slack of the correlation-cut inequality at a `0/1` rank-one
matrix is exactly `(1 - aᵀb)^2`. -/
private theorem correlation_cut_inequality_slack_at_vertex
    {n : ℕ} (a b : Fin n → ℝ) (hb : is_zero_one_vector b) :
    1 - Matrix.trace (correlation_cut_matrix a * Matrix.vecMulVec b b) =
      (1 - a ⬝ᵥ b) ^ 2 := by
  -- This is the textbook trace computation from Lemma 4.56.
  simp only [correlation_cut_matrix]
  rw [sub_mul, Matrix.trace_sub, smul_mul_assoc, Matrix.trace_smul,
    diagonal_vecMulVec_trace_eq_dotProduct a b hb,
    vecMulVec_mul_vecMulVec_trace_eq_dotProduct_sq]
  ring

/-- Helper for Theorem 4.57: the transported copy of inequality `(4.38)` as a linear functional on
the reindexed cut-coordinate space. -/
private noncomputable def transported_correlation_cut_functional
    (n : ℕ) (a : Finset (Fin n)) :
    (Fin (Fintype.card (complete_graph_edges (n + 1))) → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun x ↦
      Matrix.trace
        (correlation_cut_matrix (finset_indicator a) *
          (((correlation_cut_linear_equiv n).symm (cut_coordinate_reindex n x)).toMatrix))
    map_add' := by
      -- The transported correlation trace is linear in the cut-coordinate vector.
      intro x y
      simp [correlationSpace.toMatrix, Matrix.mul_add, Matrix.trace_add]
    map_smul' := by
      -- Scalar multiplication also passes through the transport and the trace.
      intro c x
      simp [correlationSpace.toMatrix, Matrix.trace_smul] }

/-- Helper for Theorem 4.57: the row-vector incarnation of the transported correlation-cut
functional. -/
private noncomputable def transported_correlation_cut_row
    (n : ℕ) (a : Finset (Fin n)) :
    Fin (Fintype.card (complete_graph_edges (n + 1))) → ℝ :=
  fun j ↦ transported_correlation_cut_functional n a (Pi.single j (1 : ℝ))

/-- Helper for Theorem 4.57: each transported `(4.38)` row is valid on the reindexed cut polytope.
-/
private theorem transported_correlation_cut_row_valid_on_reindexed_cut_polytope
    (n : ℕ) (a : Finset (Fin n))
    {x : Fin (Fintype.card (complete_graph_edges (n + 1))) → ℝ}
    (hx : x ∈ (cut_coordinate_reindex n).symm '' cutPolytope (n + 1)) :
    transported_correlation_cut_row n a ⬝ᵥ x ≤ 1 := by
  rcases hx with ⟨y, hy, rfl⟩
  rw [← correlation_cut_linear_equiv_image_correlationPolytope n] at hy
  rcases hy with ⟨Y, hY, hYeq⟩
  have hsymm :
      (correlation_cut_linear_equiv n).symm y = Y := by
    -- The inverse of the explicit correlation-cut equivalence recovers the preimage point.
    apply (correlation_cut_linear_equiv n).injective
    simpa using hYeq.symm
  have hdot :
      transported_correlation_cut_row n a ⬝ᵥ (cut_coordinate_reindex n).symm y =
        transported_correlation_cut_functional n a ((cut_coordinate_reindex n).symm y) := by
    simpa [transported_correlation_cut_row] using
      functional_row_dot_eq (transported_correlation_cut_functional n a)
        ((cut_coordinate_reindex n).symm y)
  -- Evaluate the row via the transported functional and apply the valid correlation inequality.
  rw [hdot]
  change Matrix.trace
      (correlation_cut_matrix (finset_indicator a) *
        (((correlation_cut_linear_equiv n).symm
            (cut_coordinate_reindex n ((cut_coordinate_reindex n).symm y))).toMatrix)) ≤ 1
  have hytransport :
      cut_coordinate_reindex n ((cut_coordinate_reindex n).symm y) = y := by
    -- The ambient coordinate equivalence cancels with its inverse.
    simpa [cut_coordinate_reindex] using (cut_coordinate_reindex n).apply_symm_apply y
  rw [hytransport, hsymm]
  exact correlation_cut_inequality_valid (finset_indicator a) hY

/-- Helper for Theorem 4.57: the inverse correlation map sends the normalized cut vertex back to
the corresponding correlation vertex. -/
private theorem correlation_cut_inverse_normalized_cut_vertex
    (n : ℕ) (S : Finset (Fin n)) :
    (correlation_cut_linear_equiv n).symm (cutIncidenceVector (S.map Fin.castSuccEmb)) =
      correlation_vertex S := by
  -- The source inverse formulas reconstruct the normalized cut vertex entrywise.
  apply Subtype.ext
  ext i j
  have hlast0 : Fin.last n ∉ S.map Fin.castSuccEmb := by
    intro hmem
    rcases Finset.mem_map.mp hmem with ⟨k, hk, hkLast⟩
    exact Fin.castSucc_ne_last k hkLast
  by_cases hij : i = j
  · subst hij
    rw [correlation_cut_linear_equiv_symm_apply_diag, correlation_vertex_apply_diag]
    rw [edge_to_last]
    rw [cutIncidenceVector_apply_pair (S.map Fin.castSuccEmb) i.castSucc (Fin.last n)
      (edge_to_last_not_isDiag n i)]
    by_cases hi : i.castSucc ∈ S.map Fin.castSuccEmb
    · have hi' : i ∈ S := by simpa using hi
      simp [hlast0, hi, hi']
    · have hi' : i ∉ S := by simpa using hi
      simp [hlast0, hi, hi']
  · rw [correlation_cut_linear_equiv_symm_apply_offdiag n
      (cutIncidenceVector (S.map Fin.castSuccEmb)) i j hij, correlation_vertex_apply_offdiag]
    rw [edge_to_last]
    rw [cutIncidenceVector_apply_pair (S.map Fin.castSuccEmb) i.castSucc (Fin.last n)
      (edge_to_last_not_isDiag n i)]
    rw [edge_to_last]
    rw [cutIncidenceVector_apply_pair (S.map Fin.castSuccEmb) j.castSucc (Fin.last n)
      (edge_to_last_not_isDiag n j)]
    rw [internal_edge]
    rw [cutIncidenceVector_apply_pair (S.map Fin.castSuccEmb) i.castSucc j.castSucc
      (internal_edge_not_isDiag hij)]
    by_cases hi : i.castSucc ∈ S.map Fin.castSuccEmb
    · by_cases hj : j.castSucc ∈ S.map Fin.castSuccEmb
      · have hi' : i ∈ S := by simpa using hi
        have hj' : j ∈ S := by simpa using hj
        norm_num [hlast0, hi, hj, hi', hj']
      · have hi' : i ∈ S := by simpa using hi
        have hj' : j ∉ S := by simpa using hj
        simp [hlast0, hi, hj, hi', hj']
    · by_cases hj : j.castSucc ∈ S.map Fin.castSuccEmb
      · have hi' : i ∉ S := by simpa using hi
        have hj' : j ∈ S := by simpa using hj
        simp [hlast0, hi, hj, hi', hj']
      · have hi' : i ∉ S := by simpa using hi
        have hj' : j ∉ S := by simpa using hj
        simp [hlast0, hi, hj, hi', hj']

/-- Helper for Theorem 4.57: the indicator vectors of two finite subsets pair to the size of their
intersection. -/
private theorem finset_indicator_dotProduct_eq_card_inter
    {n : ℕ} (a S : Finset (Fin n)) :
    finset_indicator a ⬝ᵥ finset_indicator S = ((a ∩ S).card : ℝ) := by
  -- The dot product is the sum of the common `1` coordinates.
  classical
  unfold dotProduct finset_indicator
  simpa [Finset.inter_comm] using
    (by simp [Finset.mem_inter] :
      (∑ i, (if i ∈ a then (1 : ℝ) else 0) * if i ∈ S then (1 : ℝ) else 0) =
        ((S ∩ a).card : ℝ))

/-- Helper for Theorem 4.57: the slack of a transported `(4.38)` row at a normalized cut vertex is
the textbook quantity `(1 - |a ∩ S|)^2`. -/
private theorem transported_correlation_cut_slack_at_normalized_vertex
    (n : ℕ) (a S : Finset (Fin n)) :
    1 -
        transported_correlation_cut_row n a ⬝ᵥ
          ((cut_coordinate_reindex n).symm (cutIncidenceVector (S.map Fin.castSuccEmb))) =
      (1 - ((a ∩ S).card : ℝ)) ^ 2 := by
  let b : Fin n → ℝ := finset_indicator S
  have hb : is_zero_one_vector b := finset_indicator_is_zero_one_vector S
  have hvertex :
      ((correlation_cut_linear_equiv n).symm (cutIncidenceVector (S.map Fin.castSuccEmb))).toMatrix =
        Matrix.vecMulVec b b := by
    -- After identifying the inverse image of the normalized cut vertex, rewrite it as the
    -- corresponding rank-one correlation vertex.
    rw [correlation_cut_inverse_normalized_cut_vertex n S,
      correlation_vertex_matrix_eq_vecMulVec_indicator]
  -- Evaluate the transported row by the functional and invoke the source slack formula.
  have hdot :
      transported_correlation_cut_row n a ⬝ᵥ
          ((cut_coordinate_reindex n).symm (cutIncidenceVector (S.map Fin.castSuccEmb))) =
        transported_correlation_cut_functional n a
          ((cut_coordinate_reindex n).symm (cutIncidenceVector (S.map Fin.castSuccEmb))) := by
    simpa [transported_correlation_cut_row] using
      functional_row_dot_eq (transported_correlation_cut_functional n a)
        ((cut_coordinate_reindex n).symm (cutIncidenceVector (S.map Fin.castSuccEmb)))
  rw [hdot]
  change 1 -
      Matrix.trace
        (correlation_cut_matrix (finset_indicator a) *
          (((correlation_cut_linear_equiv n).symm
              (cut_coordinate_reindex n
                ((cut_coordinate_reindex n).symm
                  (cutIncidenceVector (S.map Fin.castSuccEmb))))).toMatrix)) =
    (1 - ((a ∩ S).card : ℝ)) ^ 2
  have htransport :
      cut_coordinate_reindex n
          ((cut_coordinate_reindex n).symm (cutIncidenceVector (S.map Fin.castSuccEmb))) =
        cutIncidenceVector (S.map Fin.castSuccEmb) := by
    -- The cut-coordinate equivalence cancels on the normalized cut vertex.
    simpa [cut_coordinate_reindex] using
      (cut_coordinate_reindex n).apply_symm_apply (cutIncidenceVector (S.map Fin.castSuccEmb))
  rw [htransport, hvertex, correlation_cut_inequality_slack_at_vertex (finset_indicator a) b hb,
    finset_indicator_dotProduct_eq_card_inter]

/-- Helper for Theorem 4.57: a singleton subset of `ℝ^d` is a polyhedron via the coordinatewise
upper and lower bounds cutting out that point. -/
private theorem singleton_is_polyhedron
    {d : ℕ} (x : Fin d → ℝ) :
    is_polyhedron ({x} : Set (Fin d → ℝ)) := by
  let A : Matrix (Fin (d + d)) (Fin d) ℝ := fun i j ↦
    match finSumFinEquiv.symm i with
    | Sum.inl k => if j = k then 1 else 0
    | Sum.inr k => if j = k then -1 else 0
  let b : Fin (d + d) → ℝ := fun i ↦
    match finSumFinEquiv.symm i with
    | Sum.inl k => x k
    | Sum.inr k => -x k
  refine ⟨d + d, A, b, ?_⟩
  ext y
  constructor
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    -- The defining point satisfies each upper and lower bound with equality.
    intro i
    cases h : finSumFinEquiv.symm i with
    | inl k =>
        simp [A, b, h, Matrix.mulVec, dotProduct]
    | inr k =>
        simp [A, b, h, Matrix.mulVec, dotProduct]
  · intro hy
    rw [Set.mem_singleton_iff]
    ext k
    have hUpper : y k ≤ x k := by
      -- The positive row corresponding to `k` enforces the upper bound `y_k ≤ x_k`.
      simpa [A, b, Matrix.mulVec, dotProduct] using hy (Fin.castAdd d k)
    have hLower : x k ≤ y k := by
      -- The negative row corresponding to `k` enforces the lower bound `x_k ≤ y_k`.
      have hk : finSumFinEquiv.symm (k.addNat d) = Sum.inr k := by
        simpa using (finSumFinEquiv_symm_apply_natAdd (m := d) k)
      have hrow := hy (Fin.natAdd d k)
      simp [A, b, Matrix.mulVec, dotProduct, hk] at hrow
      exact hrow
    linarith

/-- Helper for Theorem 4.57: the recession cone of a singleton subset of `ℝ^d` is trivial. -/
private theorem recessionCone_singleton_eq_zero
    {d : ℕ} (x : Fin d → ℝ) :
    recessionCone ({x} : Set (Fin d → ℝ)) = ({0} : Set (Fin d → ℝ)) := by
  ext r
  constructor
  · intro hr
    -- Translating the singleton point by `r` with scalar `1` must keep it fixed, so `r = 0`.
    have htranslate : x + (1 : ℝ) • r = x := by
      rw [mem_recessionCone_iff] at hr
      have hmem : x + (1 : ℝ) • r ∈ ({x} : Set (Fin d → ℝ)) := hr (by simp) 1 (by norm_num)
      simpa using hmem
    have hrzero : r = 0 := by
      ext i
      have hi := congrFun htranslate i
      have hi' : x i + r i = x i := by
        simpa using hi
      have hr_i : r i = 0 := by
        linarith
      simpa using hr_i
    simpa [Set.mem_singleton_iff] using hrzero
  · intro hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    -- The zero direction obviously preserves the singleton under every nonnegative translation.
    rw [mem_recessionCone_iff]
    intro y hy a ha
    simp at hy
    subst hy
    simp

/-- Helper for Theorem 4.57: every finite vertex hull in `ℝ^d` admits a finite matrix-inequality
description. -/
private theorem finite_vertex_hull_has_inequality_description
    {τ : Type*} [Fintype τ] {d : ℕ} (v : τ → Fin d → ℝ) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin d) ℝ, ∃ b : Fin m → ℝ,
      convexHull ℝ (Set.range v) = polyhedron_le_set A b := by
  let P : τ → Set (Fin d → ℝ) := fun t ↦ {v t}
  have hP_polyhedron : ∀ t ∈ (Finset.univ : Finset τ), is_polyhedron (P t) := by
    -- Each singleton member of the finite family is already a polyhedron.
    intro t ht
    exact singleton_is_polyhedron (v t)
  have hP_recession :
      ∀ t ∈ (Finset.univ : Finset τ), ∀ u ∈ (Finset.univ : Finset τ),
        recessionCone (P t) = recessionCone (P u) := by
    -- All singleton recession cones coincide with `{0}`.
    intro t ht u hu
    simp [P, recessionCone_singleton_eq_zero]
  have hPolyhedron :
      is_polyhedron (convexHull ℝ (⋃ t ∈ (Finset.univ : Finset τ), P t)) := by
    -- Corollary 4.44 turns the finite family of singleton polyhedra into a polyhedron again.
    exact convexHull_iUnion_polyhedra_is_polyhedron_of_identical_recessionCone
      (Finset.univ : Finset τ) P hP_polyhedron hP_recession
  have hHull :
      is_polyhedron (convexHull ℝ (Set.range v)) := by
    -- The union over the universal finite family is exactly the range of the vertex map.
    simpa [P] using hPolyhedron
  rcases is_polyhedron_iff.mp hHull with ⟨m, A, b, hEq⟩
  exact ⟨m, A, b, hEq⟩

/-- Helper for Theorem 4.57: every cut vector can be normalized so that the last vertex is omitted
without changing the cut-incidence coordinates. -/
private theorem cutVertices_eq_normalized_cutVertices (n : ℕ) :
    cutVertices (n + 1) =
      Set.range fun S : Finset (Fin n) ↦ cutIncidenceVector (S.map Fin.castSuccEmb) := by
  ext y
  constructor
  · rintro ⟨W, rfl⟩
    let W0 : Finset (Fin (n + 1)) :=
      if Fin.last n ∈ W then Finset.univ \ W else W
    let S : Finset (Fin n) := Finset.univ.filter fun i ↦ i.castSucc ∈ W0
    have hcut : cutIncidenceVector W0 = cutIncidenceVector W := by
      -- Complementing a cut removes the last vertex while preserving the cut-incidence vector.
      by_cases hlast : Fin.last n ∈ W
      · simp [W0, hlast, cutIncidenceVector_compl_eq]
      · simp [W0, hlast]
    have hlast0 : Fin.last n ∉ W0 := by
      -- By construction the normalized representative avoids the last vertex.
      by_cases hlast : Fin.last n ∈ W
      · simp [W0, hlast]
      · simp [W0, hlast]
    have hSmap : S.map Fin.castSuccEmb = W0 := by
      -- Every normalized vertex is either `i.castSucc` for a unique `i`, or it is excluded.
      ext v
      rcases Fin.eq_castSucc_or_eq_last v with ⟨i, rfl⟩ | rfl
      · simp [S]
      · simp [hlast0]
    refine ⟨S, ?_⟩
    -- Replacing `W` by the normalized `W0` leaves the cut-incidence vector unchanged.
    simpa [hSmap] using hcut
  · rintro ⟨S, rfl⟩
    exact ⟨S.map Fin.castSuccEmb, rfl⟩

/-- Helper for Theorem 4.57: the cut polytope of `K_{n+1}` is the convex hull of the normalized
cut vertices indexed by subsets of `Fin n`. -/
private theorem cutPolytope_eq_convexHull_normalized_cutVertices (n : ℕ) :
    cutPolytope (n + 1) =
      convexHull ℝ
        (Set.range fun S : Finset (Fin n) ↦ cutIncidenceVector (S.map Fin.castSuccEmb)) := by
  -- Replace the full vertex set by the normalized one and keep the same convex hull.
  rw [cutPolytope, cutVertices_eq_normalized_cutVertices]

/-- Helper for Theorem 4.57: after reindexing the ambient cut coordinates to `Fin`, the normalized
cut vertices still generate the whole cut polytope. -/
private theorem normalized_cut_vertices_hull_eq_reindexed_cut_polytope (n : ℕ) :
    (cut_coordinate_reindex n).symm '' cutPolytope (n + 1) =
      convexHull ℝ
        (Set.range fun S : Finset (Fin n) ↦
          (cut_coordinate_reindex n).symm (cutIncidenceVector (S.map Fin.castSuccEmb))) := by
  -- Linear images commute with convex hull, so we just transport the normalized vertex model.
  have hRange :
      (cut_coordinate_reindex n).symm ''
          (Set.range fun S : Finset (Fin n) ↦
            cutIncidenceVector (S.map Fin.castSuccEmb)) =
        Set.range (fun S : Finset (Fin n) ↦
          (cut_coordinate_reindex n).symm
            (cutIncidenceVector (S.map Fin.castSuccEmb))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨S, rfl⟩
      exact ⟨S, rfl⟩
    · rintro ⟨S, rfl⟩
      exact ⟨cutIncidenceVector (S.map Fin.castSuccEmb), ⟨S, rfl⟩, rfl⟩
  calc
    (cut_coordinate_reindex n).symm '' cutPolytope (n + 1)
        = (cut_coordinate_reindex n).symm ''
            convexHull ℝ
              (Set.range fun S : Finset (Fin n) ↦
                cutIncidenceVector (S.map Fin.castSuccEmb)) := by
            rw [cutPolytope_eq_convexHull_normalized_cutVertices]
    _ = convexHull ℝ
          ((cut_coordinate_reindex n).symm ''
            (Set.range fun S : Finset (Fin n) ↦
              cutIncidenceVector (S.map Fin.castSuccEmb))) := by
            simpa using
              (cut_coordinate_reindex n).symm.toLinearMap.image_convexHull
                (Set.range fun S : Finset (Fin n) ↦
                  cutIncidenceVector (S.map Fin.castSuccEmb))
    _ = convexHull ℝ
          (Set.range fun S : Finset (Fin n) ↦
            (cut_coordinate_reindex n).symm
              (cutIncidenceVector (S.map Fin.castSuccEmb))) := by
            rw [hRange]

/-- Helper for Theorem 4.57: rectangle covering number depends only on the zero pattern of the
matrix, so equal supports transfer any cover bound across codomains. -/
private theorem rectangle_covering_number_le_of_matrix_support_eq
    {m : Type*} {n : Type*} {α : Type*} {β : Type*}
    [Finite m] [Finite n]
    [Zero α] [One α] [NeZero (1 : α)]
    [Zero β] [One β] [NeZero (1 : β)]
    (S : Matrix m n α) (T : Matrix m n β)
    (hSupport : matrix_support S = matrix_support T) :
    rectangle_covering_number S ≤ rectangle_covering_number T := by
  classical
  obtain ⟨R, hR⟩ := rectangle_covering_number_spec T
  choose I J hI hJ hRectSupport using fun t ↦ (hR.rectangles t).support_eq
  let R' : Fin (rectangle_covering_number T) → Matrix m n α :=
    fun t ↦ rectangle_indicator (I t) (J t)
  have hR' : is_rectangle_cover S R' := by
    refine (is_rectangle_cover_iff).mpr ?_
    refine ⟨?_, ?_⟩
    · -- Rebuild each covering rectangle in the codomain of `S` using the same support product.
      intro t
      exact rectangle_indicator_is_rectangle_matrix (hI t) (hJ t)
    · -- The reconstructed rectangles have exactly the same support union as the original cover.
      calc
        matrix_support S = matrix_support T := hSupport
        _ = ⋃ t, matrix_support (R t) := hR.support_eq
        _ = ⋃ t, (I t).prod (J t) := by
              ext p
              rcases p with ⟨i, j⟩
              simp [hRectSupport]
        _ = ⋃ t, matrix_support (R' t) := by
              ext p
              rcases p with ⟨i, j⟩
              simp [R']
  exact rectangle_covering_number_le hR'

/-- Helper for Theorem 4.57: passing to a row submatrix cannot increase the rectangle covering
number. -/
private theorem rectangle_covering_number_row_submatrix_le
    {m : Type*} {l : Type*} {n : Type*} {α : Type*}
    [Finite m] [Finite l] [Finite n]
    [Zero α] [One α] [NeZero (1 : α)]
    (S : Matrix l n α) (row : m ↪ l) :
    rectangle_covering_number (S.submatrix row id) ≤ rectangle_covering_number S := by
  classical
  obtain ⟨R, hR⟩ := rectangle_covering_number_spec S
  choose I J hI hJ hRectSupport using fun t ↦ (hR.rectangles t).support_eq
  let T : Type _ := {t : Fin (rectangle_covering_number S) // Set.Nonempty (row ⁻¹' I t)}
  let eT : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let Rsub : Fin (Fintype.card T) → Matrix m n α := fun u ↦
    rectangle_indicator (row ⁻¹' I ((eT.symm u).1)) (J ((eT.symm u).1))
  have hRsub : is_rectangle_cover (S.submatrix row id) Rsub := by
    refine (is_rectangle_cover_iff).mpr ?_
    refine ⟨?_, ?_⟩
    · -- Keep only the rectangles whose row support meets the embedded image.
      intro u
      exact rectangle_indicator_is_rectangle_matrix (eT.symm u).2 (hJ ((eT.symm u).1))
    · ext p
      rcases p with ⟨i, j⟩
      constructor
      · intro hp
        have hpS : (row i, j) ∈ matrix_support S := by
          simpa [Matrix.submatrix_apply] using hp
        rw [hR.support_eq] at hpS
        rcases Set.mem_iUnion.1 hpS with ⟨t, ht⟩
        have htProd : (row i, j) ∈ (I t).prod (J t) := by
          simpa [hRectSupport t] using ht
        have hrowMem : row i ∈ I t := by
          exact htProd.1
        have hcolMem : j ∈ J t := by
          exact htProd.2
        refine Set.mem_iUnion.2 ⟨eT ⟨t, ⟨i, hrowMem⟩⟩, ?_⟩
        simpa [Rsub]
      · intro hp
        rcases Set.mem_iUnion.1 hp with ⟨u, hu⟩
        let t : Fin (rectangle_covering_number S) := (eT.symm u).1
        have huProd :
            (i, j) ∈ (row ⁻¹' I t).prod (J t) := by
          simpa [Rsub, t] using hu
        have hrowMem : row i ∈ I t := by
          exact huProd.1
        have hcolMem : j ∈ J t := by
          exact huProd.2
        have hpS : (row i, j) ∈ matrix_support (R t) := by
          simpa [hRectSupport] using And.intro hrowMem hcolMem
        have hcover : (row i, j) ∈ matrix_support S := by
          rw [hR.support_eq]
          exact Set.mem_iUnion.2 ⟨t, hpS⟩
        simpa [Matrix.submatrix_apply] using hcover
  -- Compare the filtered cover size to the original one via the subtype-cardinality bound.
  calc
    rectangle_covering_number (S.submatrix row id) ≤ Fintype.card T := by
      simpa [eT, T] using rectangle_covering_number_le hRsub
    _ ≤ rectangle_covering_number S := by
      simpa [T] using
        (Fintype.card_subtype_le
          (fun t : Fin (rectangle_covering_number S) ↦ Set.Nonempty (row ⁻¹' I t)))

/-- Helper for Theorem 4.57: adjoining the transported copies of `(4.38)` to a finite base system
for the reindexed cut polytope does not change the feasible set. -/
private theorem augmented_reindexed_cut_system_eq_polyhedron
    (n m0 : ℕ)
    (A0 : Matrix (Fin m0) (Fin (Fintype.card (complete_graph_edges (n + 1)))) ℝ)
    (b0 : Fin m0 → ℝ)
    (hReindexedSystem :
      (cut_coordinate_reindex n).symm '' cutPolytope (n + 1) = polyhedron_le_set A0 b0) :
    let rowEquiv : (Fin m0 ⊕ Finset (Fin n)) ≃ Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) :=
      Fintype.equivFin (Fin m0 ⊕ Finset (Fin n))
    let AaugSum :=
      Matrix.fromRows A0 (fun a : Finset (Fin n) ↦ transported_correlation_cut_row n a)
    let baugSum : Fin m0 ⊕ Finset (Fin n) → ℝ := Sum.elim b0 (fun _ ↦ (1 : ℝ))
    let Aaug :=
      Matrix.reindex rowEquiv (Equiv.refl _) AaugSum
    let baug : Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) → ℝ := baugSum ∘ rowEquiv.symm
    (cut_coordinate_reindex n).symm '' cutPolytope (n + 1) =
      polyhedron_le_set Aaug baug := by
  let rowEquiv : (Fin m0 ⊕ Finset (Fin n)) ≃ Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) :=
    Fintype.equivFin (Fin m0 ⊕ Finset (Fin n))
  let AaugSum :=
    Matrix.fromRows A0 (fun a : Finset (Fin n) ↦ transported_correlation_cut_row n a)
  let baugSum : Fin m0 ⊕ Finset (Fin n) → ℝ := Sum.elim b0 (fun _ ↦ (1 : ℝ))
  let Aaug :=
    Matrix.reindex rowEquiv (Equiv.refl _) AaugSum
  let baug : Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) → ℝ := baugSum ∘ rowEquiv.symm
  have hAaugMul :
      ∀ x : Fin (Fintype.card (complete_graph_edges (n + 1))) → ℝ,
        Aaug *ᵥ x = fun i ↦ (AaugSum *ᵥ x) (rowEquiv.symm i) := by
    -- The `Fin` row model just reindexes the stacked row system.
    intro x
    ext i
    simp [Aaug, AaugSum, Matrix.mulVec, dotProduct, Matrix.reindex_apply]
  ext x
  constructor
  · intro hx
    have hxBase : x ∈ polyhedron_le_set A0 b0 := by
      rw [← hReindexedSystem]
      exact hx
    have hxSum : AaugSum *ᵥ x ≤ baugSum := by
      -- The stacked sum-indexed system contains the base rows and the valid transported rows.
      intro i
      cases i with
      | inl i =>
          simpa [AaugSum, baugSum] using hxBase i
      | inr a =>
          simpa [AaugSum, baugSum] using
            transported_correlation_cut_row_valid_on_reindexed_cut_polytope n a hx
    -- Reindex the stacked system to the canonical `Fin` row owner.
    change Aaug *ᵥ x ≤ baug
    intro i
    rw [congrFun (hAaugMul x) i]
    simpa [baug] using hxSum (rowEquiv.symm i)
  · intro hx
    have hxBase : x ∈ polyhedron_le_set A0 b0 := by
      have hxFin : Aaug *ᵥ x ≤ baug := by
        simpa [polyhedron_le_set] using hx
      -- Reading only the `Sum.inl` rows recovers the base system.
      intro i
      have hi := hxFin (rowEquiv (Sum.inl i))
      rw [congrFun (hAaugMul x) (rowEquiv (Sum.inl i))] at hi
      simpa [AaugSum, baug, baugSum] using hi
    rw [hReindexedSystem]
    exact hxBase

/-- Helper for Theorem 4.57: the appended transported rows in the augmented slack matrix have the
same support as the unique disjointness matrix `U^n`. -/
private theorem transported_row_block_support_eq_unique_disjointness
    (n m0 : ℕ)
    (A0 : Matrix (Fin m0) (Fin (Fintype.card (complete_graph_edges (n + 1)))) ℝ)
    (b0 : Fin m0 → ℝ) :
    let rowEquiv : (Fin m0 ⊕ Finset (Fin n)) ≃ Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) :=
      Fintype.equivFin (Fin m0 ⊕ Finset (Fin n))
    let colEquiv : Finset (Fin n) ≃ Fin (Fintype.card (Finset (Fin n))) :=
      Fintype.equivFin (Finset (Fin n))
    let appendedRow : Finset (Fin n) ↪ Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) :=
      { toFun := fun a ↦ rowEquiv (Sum.inr a)
        inj' := by
          intro a b hab
          exact Sum.inr.inj (rowEquiv.injective hab) }
    let AaugSum :=
      Matrix.fromRows A0 (fun a : Finset (Fin n) ↦ transported_correlation_cut_row n a)
    let baugSum : Fin m0 ⊕ Finset (Fin n) → ℝ := Sum.elim b0 (fun _ ↦ (1 : ℝ))
    let Aaug :=
      Matrix.reindex rowEquiv (Equiv.refl _) AaugSum
    let baug : Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) → ℝ := baugSum ∘ rowEquiv.symm
    let vFin :
        Fin (Fintype.card (Finset (Fin n))) →
          Fin (Fintype.card (complete_graph_edges (n + 1))) → ℝ :=
      fun j ↦
        (cut_coordinate_reindex n).symm
          (cutIncidenceVector ((colEquiv.symm j).map Fin.castSuccEmb))
    matrix_support ((slack_matrix Aaug baug vFin).submatrix appendedRow colEquiv) =
      matrix_support (U^n) := by
  classical
  let rowEquiv : (Fin m0 ⊕ Finset (Fin n)) ≃ Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) :=
    Fintype.equivFin (Fin m0 ⊕ Finset (Fin n))
  let colEquiv : Finset (Fin n) ≃ Fin (Fintype.card (Finset (Fin n))) :=
    Fintype.equivFin (Finset (Fin n))
  let appendedRow : Finset (Fin n) ↪ Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) :=
    { toFun := fun a ↦ rowEquiv (Sum.inr a)
      inj' := by
        intro a b hab
        exact Sum.inr.inj (rowEquiv.injective hab) }
  let AaugSum :=
    Matrix.fromRows A0 (fun a : Finset (Fin n) ↦ transported_correlation_cut_row n a)
  let baugSum : Fin m0 ⊕ Finset (Fin n) → ℝ := Sum.elim b0 (fun _ ↦ (1 : ℝ))
  let Aaug :=
    Matrix.reindex rowEquiv (Equiv.refl _) AaugSum
  let baug : Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) → ℝ := baugSum ∘ rowEquiv.symm
  let vFin :
      Fin (Fintype.card (Finset (Fin n))) →
        Fin (Fintype.card (complete_graph_edges (n + 1))) → ℝ :=
    fun j ↦
      (cut_coordinate_reindex n).symm
        (cutIncidenceVector ((colEquiv.symm j).map Fin.castSuccEmb))
  have hAaugMul :
      ∀ x : Fin (Fintype.card (complete_graph_edges (n + 1))) → ℝ,
        Aaug *ᵥ x = fun i ↦ (AaugSum *ᵥ x) (rowEquiv.symm i) := by
    -- The augmented `Fin`-indexed rows are just the reindexed stacked rows.
    intro x
    ext i
    simp [Aaug, AaugSum, Matrix.mulVec, dotProduct, Matrix.reindex_apply]
  ext p
  rcases p with ⟨a, S⟩
  have hBlock :
      ((slack_matrix
            Aaug
            baug
            vFin).submatrix appendedRow colEquiv) a S =
        (1 - ((a ∩ S).card : ℝ)) ^ 2 := by
    -- The appended slack block is exactly the transported `(4.38)` slack on normalized cut
    -- vertices.
    have hmul : (Aaug *ᵥ vFin (colEquiv S)) (appendedRow a) =
        (AaugSum *ᵥ vFin (colEquiv S)) (Sum.inr a) := by
      simpa [appendedRow] using congrFun (hAaugMul (vFin (colEquiv S))) (appendedRow a)
    rw [Matrix.submatrix_apply, slack_matrix_apply, hmul]
    simp only [AaugSum, Matrix.fromRows_mulVec, Sum.elim_inr]
    simp [baug, baugSum, appendedRow, colEquiv, vFin]
    exact transported_correlation_cut_slack_at_normalized_vertex n a S
  have hBlockZero :
      ((slack_matrix
            Aaug
            baug
            vFin).submatrix appendedRow colEquiv) a S = 0 ↔
        (a ∩ S).card = 1 := by
    -- The transported slack vanishes exactly in the unique-disjointness case.
    rw [hBlock, sq_eq_zero_iff]
    constructor
    · intro h
      have hCast : ((a ∩ S).card : ℝ) = 1 := by
        linarith
      exact_mod_cast hCast
    · intro h
      norm_num [h]
  rw [mem_matrix_support_iff, mem_matrix_support_iff]
  constructor
  · intro hNonzero
    intro hZero
    exact hNonzero ((hBlockZero).2 ((unique_disjointness_matrix_eq_zero_iff).1 hZero))
  · intro hNonzero
    intro hZero
    exact hNonzero ((unique_disjointness_matrix_eq_zero_iff).2 ((hBlockZero).1 hZero))

/-- Theorem 4.57. Via the index shift in Lemma 4.55, every linear extended formulation of the cut
polytope `P_{n+1}^{cut}` has at least `(3 / 2)^n` total constraints. -/
theorem cut_polytope_extended_formulation_constraint_lower_bound
    (n : ℕ)
    {κ ρ σ : Type*}
    [Fintype κ] [Fintype ρ] [Fintype σ]
    (Aeq : Matrix ρ (complete_graph_edges (n + 1)) ℝ)
    (Beq : Matrix ρ κ ℝ)
    (beq : ρ → ℝ)
    (Aineq : Matrix σ (complete_graph_edges (n + 1)) ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ)
    (hEF :
      cutPolytope (n + 1) =
        Prod.fst '' linear_extended_system Aeq Beq beq Aineq Bineq bineq) :
    ((3 : ℚ) / 2) ^ n ≤ (Fintype.card ρ + Fintype.card σ : ℚ) := by
  -- Route correction: the proof follows the textbook source route through a reindexed
  -- cut-polytope description and a transported `U^n` support block, rather than switching to a
  -- different extension-complexity argument.
  have hEFfin :
      (cut_coordinate_reindex n).symm '' cutPolytope (n + 1) =
        Prod.fst ''
          linear_extended_system
            (Matrix.reindex (Fintype.equivFin ρ)
              (Fintype.equivFin (complete_graph_edges (n + 1))) Aeq)
            (Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq)
            (fun i ↦ beq ((Fintype.equivFin ρ).symm i))
            (Matrix.reindex (Fintype.equivFin σ)
              (Fintype.equivFin (complete_graph_edges (n + 1))) Aineq)
            (Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq)
            (fun i ↦ bineq ((Fintype.equivFin σ).symm i)) := by
    -- The ambient coordinate reindexing simply transports the given extended formulation.
    rw [hEF]
    exact cut_coordinate_reindex_image_linear_extended_formulation
      n Aeq Beq beq Aineq Bineq bineq
  have hVertices :
      (cut_coordinate_reindex n).symm '' cutPolytope (n + 1) =
        convexHull ℝ
          (Set.range fun S : Finset (Fin n) ↦
            (cut_coordinate_reindex n).symm
              (cutIncidenceVector (S.map Fin.castSuccEmb))) :=
    normalized_cut_vertices_hull_eq_reindexed_cut_polytope n
  rcases finite_vertex_hull_has_inequality_description
      (fun S : Finset (Fin n) ↦
        (cut_coordinate_reindex n).symm
          (cutIncidenceVector (S.map Fin.castSuccEmb))) with
    ⟨m0, A0, b0, hBaseSystem⟩
  have hReindexedSystem :
      (cut_coordinate_reindex n).symm '' cutPolytope (n + 1) = polyhedron_le_set A0 b0 := by
    -- The reindexed cut polytope is now presented both as a finite hull and as a finite system.
    calc
      (cut_coordinate_reindex n).symm '' cutPolytope (n + 1)
          = convexHull ℝ
              (Set.range fun S : Finset (Fin n) ↦
              (cut_coordinate_reindex n).symm
                  (cutIncidenceVector (S.map Fin.castSuccEmb))) := hVertices
      _ = polyhedron_le_set A0 b0 := hBaseSystem
  let rowEquiv : (Fin m0 ⊕ Finset (Fin n)) ≃ Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) :=
    Fintype.equivFin (Fin m0 ⊕ Finset (Fin n))
  let colEquiv : Finset (Fin n) ≃ Fin (Fintype.card (Finset (Fin n))) :=
    Fintype.equivFin (Finset (Fin n))
  let appendedRow : Finset (Fin n) ↪ Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) :=
    { toFun := fun a ↦ rowEquiv (Sum.inr a)
      inj' := by
        intro a b hab
        exact Sum.inr.inj (rowEquiv.injective hab) }
  let AaugSum :=
    Matrix.fromRows A0 (fun a : Finset (Fin n) ↦ transported_correlation_cut_row n a)
  let baugSum : Fin m0 ⊕ Finset (Fin n) → ℝ := Sum.elim b0 (fun _ ↦ (1 : ℝ))
  let Aaug :
      Matrix (Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))))
        (Fin (Fintype.card (complete_graph_edges (n + 1)))) ℝ :=
    Matrix.reindex rowEquiv (Equiv.refl _) AaugSum
  let baug : Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))) → ℝ := baugSum ∘ rowEquiv.symm
  let vFin :
      Fin (Fintype.card (Finset (Fin n))) →
        Fin (Fintype.card (complete_graph_edges (n + 1))) → ℝ :=
    fun j ↦
      (cut_coordinate_reindex n).symm
        (cutIncidenceVector ((colEquiv.symm j).map Fin.castSuccEmb))
  have hAugSystem :
      (cut_coordinate_reindex n).symm '' cutPolytope (n + 1) = polyhedron_le_set Aaug baug := by
    -- Source step: append the transported `(4.38)` rows to the finite base system.
    simpa [rowEquiv, AaugSum, baugSum, Aaug, baug] using
      augmented_reindexed_cut_system_eq_polyhedron n m0 A0 b0 hReindexedSystem
  let fullSlack :
      Matrix (Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n))))
        (Fin (Fintype.card (Finset (Fin n)))) ℝ :=
    slack_matrix Aaug baug vFin
  have hBlockSupport :
      matrix_support (fullSlack.submatrix appendedRow colEquiv) =
        matrix_support (U^n) := by
    -- The appended row block has the zero pattern of `U^n`.
    simpa [rowEquiv, colEquiv, appendedRow, AaugSum, baugSum, Aaug, baug, vFin, fullSlack] using
      transported_row_block_support_eq_unique_disjointness n m0 A0 b0
  have hFullSlackBound :
      rectangle_covering_number fullSlack ≤ Fintype.card ρ + Fintype.card σ := by
    have hRangeV : Set.range vFin =
        Set.range (fun S : Finset (Fin n) ↦
          (cut_coordinate_reindex n).symm (cutIncidenceVector (S.map Fin.castSuccEmb))) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨colEquiv.symm j, by simp [vFin]⟩
      · rintro ⟨S, rfl⟩
        exact ⟨colEquiv S, by simp [vFin]⟩
    have hVerticesFin :
        (cut_coordinate_reindex n).symm '' cutPolytope (n + 1) =
          convexHull ℝ (Set.range vFin) := by
      -- Reindex the normalized vertex family to `Fin` only at the theorem-4.53 boundary.
      calc
        (cut_coordinate_reindex n).symm '' cutPolytope (n + 1) =
            convexHull ℝ
              (Set.range fun S : Finset (Fin n) ↦
                (cut_coordinate_reindex n).symm
                  (cutIncidenceVector (S.map Fin.castSuccEmb))) := hVertices
        _ = convexHull ℝ (Set.range vFin) := by rw [hRangeV.symm]
    have hFinBound :
        rectangle_covering_number fullSlack ≤
          Fintype.card ρ + Fintype.card σ := by
      -- Lemma 4.53 applies to the finite reindexing of the augmented system.
      simpa using
        (rectangle_covering_number_le_extended_formulation_constraint_count
          ((cut_coordinate_reindex n).symm '' cutPolytope (n + 1))
          Aaug baug vFin
          (Matrix.reindex (Fintype.equivFin ρ)
            (Fintype.equivFin (complete_graph_edges (n + 1))) Aeq)
          (Matrix.reindex (Fintype.equivFin ρ) (Fintype.equivFin κ) Beq)
          (fun i ↦ beq ((Fintype.equivFin ρ).symm i))
          (Matrix.reindex (Fintype.equivFin σ)
            (Fintype.equivFin (complete_graph_edges (n + 1))) Aineq)
          (Matrix.reindex (Fintype.equivFin σ) (Fintype.equivFin κ) Bineq)
          (fun i ↦ bineq ((Fintype.equivFin σ).symm i))
          hVerticesFin hAugSystem hEFfin)
    exact hFinBound
  have hUniqueToBlock :
      rectangle_covering_number (U^n) ≤
        rectangle_covering_number (fullSlack.submatrix appendedRow colEquiv) := by
    -- The support-identification step transfers the rectangle covering number from `U^n`.
    exact rectangle_covering_number_le_of_matrix_support_eq
      (U^n) (fullSlack.submatrix appendedRow colEquiv) hBlockSupport.symm
  have hBlockToFull :
      rectangle_covering_number (fullSlack.submatrix appendedRow colEquiv) ≤
        rectangle_covering_number fullSlack := by
    let fullSlackOnSets :
        Matrix (Fin (Fintype.card (Fin m0 ⊕ Finset (Fin n)))) (Finset (Fin n)) ℝ :=
      Matrix.reindex (Equiv.refl _) colEquiv.symm fullSlack
    have hCols :
        rectangle_covering_number fullSlackOnSets ≤ rectangle_covering_number fullSlack := by
      obtain ⟨R, hR⟩ := rectangle_covering_number_spec fullSlack
      have hR' :
          is_rectangle_cover fullSlackOnSets
            (fun t ↦ Matrix.reindex (Equiv.refl _) colEquiv.symm (R t)) := by
        simpa [fullSlackOnSets] using hR.reindex (Equiv.refl _) colEquiv.symm
      exact rectangle_covering_number_le hR'
    have hBlockEq :
        fullSlack.submatrix appendedRow colEquiv = fullSlackOnSets.submatrix appendedRow id := by
      ext a j
      simp [fullSlackOnSets, Matrix.submatrix_apply]
    -- First transport the column indices back to subsets, then restrict to the appended rows.
    calc
      rectangle_covering_number (fullSlack.submatrix appendedRow colEquiv)
          = rectangle_covering_number (fullSlackOnSets.submatrix appendedRow id) := by
              rw [hBlockEq]
      _ ≤ rectangle_covering_number fullSlackOnSets := by
            exact rectangle_covering_number_row_submatrix_le fullSlackOnSets appendedRow
      _ ≤ rectangle_covering_number fullSlack := hCols
  have hUniqueNat :
      rectangle_covering_number (U^n) ≤
        Fintype.card ρ + Fintype.card σ := by
    exact hUniqueToBlock.trans (hBlockToFull.trans hFullSlackBound)
  have hUniqueQ :
      (rectangle_covering_number (U^n) : ℚ) ≤
        (Fintype.card ρ + Fintype.card σ : ℚ) := by
    exact_mod_cast hUniqueNat
  -- Finish with the lower bound from Theorem 4.54 on the rectangle covering number of `U^n`.
  exact (unique_disjointness_matrix_rectangle_covering_number_lower_bound n).trans hUniqueQ
