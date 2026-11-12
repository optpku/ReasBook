/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_1.ch3_sec3_1_theorem_3_1

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

variable {𝕜 : Type*}

section LinearOrderRing

variable [Ring 𝕜] [LinearOrder 𝕜]

private structure FourierStageMatrixData (𝕜 : Type*) (n : ℕ) where
  Row : Type
  [fintype_Row : Fintype Row]
  matrix : Matrix Row (Fin n) 𝕜

attribute [instance] FourierStageMatrixData.fintype_Row

private def initial_fourier_stage_matrix_data {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) :
    FourierStageMatrixData 𝕜 n where
  Row := Fin m
  matrix := A

private noncomputable def fourier_step_matrix_data {n : ℕ}
    (S : FourierStageMatrixData 𝕜 (n + 1)) : FourierStageMatrixData 𝕜 n where
  Row := FourierStepIndex S.matrix
  matrix := fourier_step_matrix S.matrix

private noncomputable def next_fourier_stage_matrix_data :
    (Σ n : ℕ, FourierStageMatrixData 𝕜 n) → Σ n : ℕ, FourierStageMatrixData 𝕜 n
  | ⟨0, S⟩ => ⟨0, S⟩
  | ⟨n + 1, S⟩ => ⟨n, fourier_step_matrix_data S⟩

private noncomputable def fourier_stage_matrix_data {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) : ℕ → Σ r : ℕ, FourierStageMatrixData 𝕜 r
  | 0 => ⟨n, initial_fourier_stage_matrix_data A⟩
  | k + 1 => next_fourier_stage_matrix_data (fourier_stage_matrix_data A k)

/-- The ambient dimension of the `k`th Fourier-Motzkin stage. -/
noncomputable abbrev fourier_stage_dim {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) : ℕ :=
  (fourier_stage_matrix_data A k).1

/-- The row-index family of the `k`th Fourier-Motzkin stage. -/
noncomputable abbrev fourier_stage_row {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) : Type :=
  (fourier_stage_matrix_data A k).2.Row

noncomputable instance fourier_stage_row_fintype {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) : Fintype (fourier_stage_row A k) :=
  (fourier_stage_matrix_data A k).2.fintype_Row

/-- The coefficient matrix of the `k`th Fourier-Motzkin stage. -/
noncomputable abbrev fourier_stage_matrix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    Matrix (fourier_stage_row A k) (Fin (fourier_stage_dim A k)) 𝕜 :=
  (fourier_stage_matrix_data A k).2.matrix

/-- The row count of the `k`th Fourier-Motzkin stage. -/
noncomputable abbrev fourier_stage_rows {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) : ℕ :=
  Fintype.card (fourier_stage_row A k)

private noncomputable def next_fourier_stage_rhs
    (S : Σ r : ℕ, FourierStageMatrixData 𝕜 r) (rhs : S.2.Row → 𝕜) :
    (next_fourier_stage_matrix_data S).2.Row → 𝕜 :=
  match S with
  | ⟨0, _⟩ => rhs
  | ⟨_ + 1, T⟩ => fourier_step_rhs T.matrix rhs

private noncomputable def fourier_stage_rhs_data {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (b : Fin m → 𝕜) :
    (k : ℕ) → (fourier_stage_matrix_data A k).2.Row → 𝕜
  | 0 => b
  | k + 1 => next_fourier_stage_rhs (fourier_stage_matrix_data A k) (fourier_stage_rhs_data A b k)

/-- Algorithm 3.1-extra-1: the iterated Fourier-Motzkin right-hand sides obtained from `A x ≤ b`.
The stage `k` is the system after `k` elimination steps. -/
noncomputable abbrev fourier_stage_rhs {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (b : Fin m → 𝕜) (k : ℕ) :
    fourier_stage_row A k → 𝕜 :=
  fourier_stage_rhs_data A b k

@[simp] theorem fourier_stage_dim_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) :
    fourier_stage_dim A 0 = n :=
  rfl

@[simp] theorem fourier_stage_matrix_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) :
    fourier_stage_matrix A 0 = A :=
  rfl

@[simp] theorem fourier_stage_rows_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) :
    fourier_stage_rows A 0 = m := by
  change Fintype.card (Fin m) = m
  exact Fintype.card_fin m

@[simp] theorem fourier_stage_rhs_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) (b : Fin m → 𝕜) :
    fourier_stage_rhs A b 0 = b :=
  rfl

@[simp] private theorem next_fourier_stage_matrix_data_dim
    (S : Σ n : ℕ, FourierStageMatrixData 𝕜 n) :
    (next_fourier_stage_matrix_data S).1 = S.1 - 1 := by
  rcases S with ⟨n, S⟩
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

/-- Advancing one Fourier-Motzkin stage lowers the ambient dimension by one, unless it is already
zero. -/
theorem fourier_stage_dim_succ {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    fourier_stage_dim A (k + 1) = fourier_stage_dim A k - 1 := by
  exact (next_fourier_stage_matrix_data_dim (fourier_stage_matrix_data A k)).trans <|
    by simp [fourier_stage_dim]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap03/section_3_1/ch3_sec3_1_algorithm_3_1_extra_1.lean`: a stage-data
package of dimension zero is unchanged by the matrix successor operation. -/
private theorem next_fourier_stage_matrix_of_dim_eq_zero
    (S : Σ d : ℕ, FourierStageMatrixData 𝕜 d) (h : S.1 = 0) :
    let S0 : Matrix S.2.Row (Fin 0) 𝕜 :=
      cast (congrArg (fun d ↦ Matrix S.2.Row (Fin d) 𝕜) h) S.2.matrix
    HEq (next_fourier_stage_matrix_data S).2.matrix S0 := by
  -- Split on the package dimension so the successor definition selects its stationary branch.
  rcases S with ⟨d, T⟩
  dsimp at h ⊢
  cases d with
  | zero =>
      cases h
      rfl
  | succ d =>
      cases h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap03/section_3_1/ch3_sec3_1_algorithm_3_1_extra_1.lean`: a stage-data
package of dimension zero preserves its right-hand side at the successor stage. -/
private theorem next_fourier_stage_rhs_of_dim_eq_zero
    (S : Σ d : ℕ, FourierStageMatrixData 𝕜 d) (rhs : S.2.Row → 𝕜) (h : S.1 = 0) :
    HEq (next_fourier_stage_rhs S rhs) rhs := by
  -- The zero-dimensional constructor returns the supplied right-hand side unchanged.
  rcases S with ⟨d, T⟩
  dsimp at h ⊢
  cases d with
  | zero =>
      cases h
      rfl
  | succ d =>
      cases h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap03/section_3_1/ch3_sec3_1_algorithm_3_1_extra_1.lean`: a positive-dimensional
stage-data package computes to the canonical one-step successor matrix. -/
private theorem next_fourier_stage_matrix_of_dim_eq_succ {r : ℕ}
    (S : Σ d : ℕ, FourierStageMatrixData 𝕜 d) (h : S.1 = r + 1) :
    let Sr : Matrix S.2.Row (Fin (r + 1)) 𝕜 :=
      cast (congrArg (fun d ↦ Matrix S.2.Row (Fin d) 𝕜) h) S.2.matrix
    HEq (next_fourier_stage_matrix_data S).2.matrix (fourier_step_matrix Sr) := by
  -- Split on the stored dimension and use `h` to normalize the positive branch and its cast.
  rcases S with ⟨d, T⟩
  dsimp at h ⊢
  cases d with
  | zero =>
      cases h
  | succ d =>
      cases h
      rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap03/section_3_1/ch3_sec3_1_algorithm_3_1_extra_1.lean`: a positive-dimensional
stage-data package computes to the canonical one-step successor right-hand side. -/
private theorem next_fourier_stage_rhs_of_dim_eq_succ {r : ℕ}
    (S : Σ d : ℕ, FourierStageMatrixData 𝕜 d) (rhs : S.2.Row → 𝕜) (h : S.1 = r + 1) :
    let Sr : Matrix S.2.Row (Fin (r + 1)) 𝕜 :=
      cast (congrArg (fun d ↦ Matrix S.2.Row (Fin d) 𝕜) h) S.2.matrix
    HEq (next_fourier_stage_rhs S rhs) (fourier_step_rhs Sr rhs) := by
  -- The positive constructor reduces both the matrix cast and the right-hand-side update.
  rcases S with ⟨d, T⟩
  dsimp at h ⊢
  cases d with
  | zero =>
      cases h
  | succ d =>
      cases h
      rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap03/section_3_1/ch3_sec3_1_algorithm_3_1_extra_1.lean`: successor stage data
admits the canonical one-step row reindexing after both dimension transports are fixed. -/
private theorem next_fourier_stage_reindex_data {r : ℕ}
    (S : Σ d : ℕ, FourierStageMatrixData 𝕜 d) (rhs : S.2.Row → 𝕜)
    (h : S.1 = r + 1) (hNext : (next_fourier_stage_matrix_data S).1 = r) :
    ∃ e : (next_fourier_stage_matrix_data S).2.Row ≃
        FourierStepIndex
          (cast (congrArg (fun d ↦ Matrix S.2.Row (Fin d) 𝕜) h) S.2.matrix),
      (next_fourier_stage_matrix_data S).2.matrix =
        cast
          (congrArg
            (fun d ↦ Matrix (next_fourier_stage_matrix_data S).2.Row (Fin d) 𝕜) hNext.symm)
          ((fourier_step_matrix
              (cast (congrArg (fun d ↦ Matrix S.2.Row (Fin d) 𝕜) h) S.2.matrix)).reindex
            e.symm (Equiv.refl _)) ∧
        next_fourier_stage_rhs S rhs =
          fun i ↦
            fourier_step_rhs
              (cast (congrArg (fun d ↦ Matrix S.2.Row (Fin d) 𝕜) h) S.2.matrix)
              rhs (e i) := by
  -- Split the package and normalize both dimension equalities before choosing the row equivalence.
  rcases S with ⟨d, T⟩
  dsimp at h hNext ⊢
  cases d with
  | zero =>
      cases h
  | succ d =>
      cases h
      cases hNext
      -- Both successor presentations now have the same row type, so the identity equivalence works.
      refine ⟨Equiv.refl _, ?_, ?_⟩
      · rfl
      · rfl

/-- If the current stage has no variables left, advancing one stage leaves the coefficient matrix
unchanged. -/
theorem fourier_stage_matrix_succ_of_dim_eq_zero {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (h : fourier_stage_dim A k = 0) :
    let Ak0 : Matrix (fourier_stage_row A k) (Fin 0) 𝕜 :=
      cast
        (congrArg (fun d ↦ Matrix (fourier_stage_row A k) (Fin d) 𝕜) h)
        (fourier_stage_matrix A k)
    HEq (fourier_stage_matrix A (k + 1)) Ak0 := by
  -- Apply the package-level computation rule to the current stage and unfold only projections.
  simpa [fourier_stage_dim, fourier_stage_matrix, fourier_stage_row,
    fourier_stage_matrix_data] using
    next_fourier_stage_matrix_of_dim_eq_zero (fourier_stage_matrix_data A k) h

/-- If the current stage has no variables left, advancing one stage leaves the right-hand side
unchanged. -/
theorem fourier_stage_rhs_succ_of_dim_eq_zero {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (b : Fin m → 𝕜) (h : fourier_stage_dim A k = 0) :
    HEq (fourier_stage_rhs A b (k + 1)) (fourier_stage_rhs A b k) := by
  -- Apply the package-level stationary computation rule to the stored stage right-hand side.
  simpa [fourier_stage_dim, fourier_stage_rhs, fourier_stage_rhs_data,
    fourier_stage_matrix_data] using
    next_fourier_stage_rhs_of_dim_eq_zero
      (fourier_stage_matrix_data A k) (fourier_stage_rhs_data A b k) h

/-- If the current stage has one more coordinate to eliminate, the next coefficient matrix is the
canonical one-step Fourier-Motzkin elimination of the current stage. -/
theorem fourier_stage_matrix_succ_of_dim_eq_succ {m n r k : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (h : fourier_stage_dim A k = r + 1) :
    let Ak : Matrix (fourier_stage_row A k) (Fin (r + 1)) 𝕜 :=
      cast
        (congrArg (fun d ↦ Matrix (fourier_stage_row A k) (Fin d) 𝕜) h)
        (fourier_stage_matrix A k)
    HEq (fourier_stage_matrix A (k + 1)) (fourier_step_matrix Ak) := by
  -- Bridge the public stage projections to the positive package-level computation rule.
  simpa [fourier_stage_dim, fourier_stage_matrix, fourier_stage_row,
    fourier_stage_matrix_data] using
    next_fourier_stage_matrix_of_dim_eq_succ (fourier_stage_matrix_data A k) h

/-- If the current stage has one more coordinate to eliminate, the next right-hand side is the
canonical one-step Fourier-Motzkin elimination of the current stage. -/
theorem fourier_stage_rhs_succ_of_dim_eq_succ {m n r k : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (b : Fin m → 𝕜) (h : fourier_stage_dim A k = r + 1) :
    let Ak : Matrix (fourier_stage_row A k) (Fin (r + 1)) 𝕜 :=
      cast
        (congrArg (fun d ↦ Matrix (fourier_stage_row A k) (Fin d) 𝕜) h)
        (fourier_stage_matrix A k)
    HEq (fourier_stage_rhs A b (k + 1)) (fourier_step_rhs Ak (fourier_stage_rhs A b k)) := by
  -- Bridge the stored matrix and right-hand side to the package-level successor computation.
  simpa [fourier_stage_dim, fourier_stage_rhs, fourier_stage_rhs_data,
    fourier_stage_matrix, fourier_stage_row, fourier_stage_matrix_data] using
    next_fourier_stage_rhs_of_dim_eq_succ
      (fourier_stage_matrix_data A k) (fourier_stage_rhs_data A b k) h

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap03/section_3_1/ch3_sec3_1_algorithm_3_1_extra_1.lean

Helper for the Fourier-Motzkin stage API: when stage `k` still has one coordinate to eliminate,
the successor stage is exactly the one-step Fourier-Motzkin system after reindexing the row type
and transporting the visible columns back to `Fin r`. -/
theorem fourier_stage_succ_reindex_data {m n r k : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (b : Fin m → 𝕜)
    (h : fourier_stage_dim A k = r + 1)
    (hNext : fourier_stage_dim A (k + 1) = r) :
    ∃ e : fourier_stage_row A (k + 1) ≃
        FourierStepIndex
          (cast
            (congrArg (fun d ↦ Matrix (fourier_stage_row A k) (Fin d) 𝕜) h)
            (fourier_stage_matrix A k)),
      fourier_stage_matrix A (k + 1) =
        cast
          (congrArg (fun d ↦ Matrix (fourier_stage_row A (k + 1)) (Fin d) 𝕜) hNext.symm)
          ((fourier_step_matrix
              (cast
                (congrArg (fun d ↦ Matrix (fourier_stage_row A k) (Fin d) 𝕜) h)
                (fourier_stage_matrix A k))).reindex e.symm (Equiv.refl _)) ∧
        fourier_stage_rhs A b (k + 1) =
          fun i ↦
            fourier_step_rhs
              (cast
                (congrArg (fun d ↦ Matrix (fourier_stage_row A k) (Fin d) 𝕜) h)
                (fourier_stage_matrix A k))
              (fourier_stage_rhs A b k)
              (e i) := by
  -- Instantiate the package-level reindexing interface at the stored stage and right-hand side.
  simpa [fourier_stage_dim, fourier_stage_matrix, fourier_stage_row, fourier_stage_rhs,
    fourier_stage_rhs_data, fourier_stage_matrix_data] using
    next_fourier_stage_reindex_data
      (fourier_stage_matrix_data A k) (fourier_stage_rhs_data A b k) h hNext

/-- For an explicit stage-data package with successor ambient dimension, the next-stage
feasibility proposition is definitionally the ordinary one-step Fourier-Motzkin feasibility
proposition. -/
private theorem next_fourier_stage_feasibility_iff
    {r : ℕ}
    (S : Σ d : ℕ, FourierStageMatrixData 𝕜 d)
    (rhs : S.2.Row → 𝕜)
    (h : S.1 = r + 1)
    (hNext : (next_fourier_stage_matrix_data S).1 = r)
    (x : Fin r → 𝕜) :
    let Ak : Matrix S.2.Row (Fin (r + 1)) 𝕜 :=
      cast (congrArg (fun d ↦ Matrix S.2.Row (Fin d) 𝕜) h) S.2.matrix
    let xNext : Fin ((next_fourier_stage_matrix_data S).1) → 𝕜 :=
      cast (congrArg (fun d ↦ Fin d → 𝕜) hNext.symm) x
    (next_fourier_stage_matrix_data S).2.matrix *ᵥ xNext ≤ next_fourier_stage_rhs S rhs ↔
      fourier_step_matrix Ak *ᵥ x ≤ fourier_step_rhs Ak rhs := by
  -- Unfold the sigma package once: when its dimension is `r + 1`, the successor stage is
  -- literally the one-step Fourier-Motzkin stage on the packaged matrix and right-hand side.
  cases S with
  | mk dim T =>
      dsimp at h hNext ⊢
      cases dim with
      | zero =>
          cases h
      | succ dim =>
          cases h
          cases hNext
          rfl

/-- If the current stage still has one last coordinate to eliminate, then successor-stage
feasibility is exactly the ordinary one-step Fourier-Motzkin feasibility condition after the
canonical column cast. -/
theorem fourier_stage_succ_feasibility_iff {m n r k : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) (b : Fin m → 𝕜)
    (h : fourier_stage_dim A k = r + 1)
    (hNext : fourier_stage_dim A (k + 1) = r) (x : Fin r → 𝕜) :
    let Ak : Matrix (fourier_stage_row A k) (Fin (r + 1)) 𝕜 :=
      cast
        (congrArg (fun d ↦ Matrix (fourier_stage_row A k) (Fin d) 𝕜) h)
        (fourier_stage_matrix A k)
    let xNext : Fin (fourier_stage_dim A (k + 1)) → 𝕜 :=
      cast (congrArg (fun d ↦ Fin d → 𝕜) hNext.symm) x
    fourier_stage_matrix A (k + 1) *ᵥ xNext ≤ fourier_stage_rhs A b (k + 1) ↔
      fourier_step_matrix Ak *ᵥ x ≤ fourier_step_rhs Ak (fourier_stage_rhs A b k) := by
  -- Route correction: turn the public successor-stage `HEq` API into one ordinary proposition
  -- equality here in the canonical owner file by unfolding the private stage-data constructors
  -- until the successor stage is literally the one-step Fourier-Motzkin data.
  let S : Σ d : ℕ, FourierStageMatrixData 𝕜 d := fourier_stage_matrix_data A k
  have hS : S.1 = r + 1 := h
  have hNextS : (next_fourier_stage_matrix_data S).1 = r := by
    simpa [S, fourier_stage_dim, fourier_stage_matrix_data] using hNext
  -- Instantiate the explicit stage-data lemma with the owner-stage sigma package at step `k`.
  simpa [S, fourier_stage_dim, fourier_stage_matrix, fourier_stage_rhs, fourier_stage_matrix_data,
    fourier_stage_rhs_data]
    using next_fourier_stage_feasibility_iff S (fourier_stage_rhs A b k) hS hNextS x

/-- After `k` elimination steps, the ambient dimension is `n - k`. -/
theorem fourier_stage_dim_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    fourier_stage_dim A k = n - k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      calc
        fourier_stage_dim A (k + 1) = fourier_stage_dim A k - 1 := fourier_stage_dim_succ A k
        _ = (n - k) - 1 := by rw [ih]
        _ = n - (k + 1) := by omega

end LinearOrderRing

#print axioms fourier_stage_succ_reindex_data
