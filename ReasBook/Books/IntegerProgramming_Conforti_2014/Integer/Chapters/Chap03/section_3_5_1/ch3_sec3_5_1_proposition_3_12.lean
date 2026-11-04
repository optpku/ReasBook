/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_1.ch3_sec3_1_remark_3_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_theorem_3_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- This proposition lives in the same source-facing matrix-cone / matrix-polyhedral-cone domain as
-- Theorem 3.11. The rational input is only a coefficient restriction, so the public statements are
-- phrased directly using those owners after applying `Rat.castHom ℝ`.

/-- Helper for Proposition 3.12: a real `Fin`-indexed matrix whose entries are all rational casts
comes from an actual rational matrix. -/
lemma matrix_eq_rat_cast_of_entrywise_rational
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : ∀ i j, ∃ q : ℚ, A i j = (q : ℝ)) :
    ∃ Aℚ : Matrix (Fin m) (Fin n) ℚ, A = Aℚ.map (Rat.castHom ℝ) := by
  classical
  let Aℚ : Matrix (Fin m) (Fin n) ℚ := fun i j ↦ Classical.choose (hA i j)
  -- Choose the rational witness entrywise and then reassemble the matrix by extensionality.
  refine ⟨Aℚ, ?_⟩
  ext i j
  simpa [Aℚ] using Classical.choose_spec (hA i j)

/-- Helper for Proposition 3.12: the basis vector on a visible coordinate in `Fin (n + k)` is the
append of the visible basis vector with a zero coefficient tail. -/
lemma single_castAdd_eq_append_single_zero
    {n k : ℕ} (j : Fin n) :
    (Pi.single (Fin.castAdd k j) (1 : ℝ) : Fin (n + k) → ℝ) =
      Fin.append (Pi.single j 1) 0 := by
  -- Split the ambient coordinates into the visible block and the coefficient block.
  ext l
  cases l using Fin.addCases with
  | left l =>
      by_cases hl : l = j
      · subst hl
        simp [Pi.single_apply]
      · have hneq : Fin.castAdd k j ≠ Fin.castAdd k l := by
          simpa [Fin.castAdd_inj, eq_comm] using hl
        simp [Pi.single_apply, hl, hneq]
  | right l =>
      have hneq : Fin.castAdd k j ≠ Fin.natAdd n l := by
        intro hEq
        have hval : (j : ℕ) = n + (l : ℕ) := by
          simpa using congrArg Fin.val hEq
        omega
      simp [Pi.single_apply, hneq]

/-- Helper for Proposition 3.12: the basis vector on a coefficient coordinate in `Fin (n + k)` is
the append of a zero visible block with the corresponding coefficient basis vector. -/
lemma single_natAdd_eq_append_zero_single
    {n k : ℕ} (j : Fin k) :
    (Pi.single (Fin.natAdd n j) (1 : ℝ) : Fin (n + k) → ℝ) =
      Fin.append 0 (Pi.single j 1) := by
  -- Split the ambient coordinates into the visible block and the coefficient block.
  ext l
  cases l using Fin.addCases with
  | left l =>
      have hneq : Fin.natAdd n j ≠ Fin.castAdd k l := by
        intro hEq
        have hval : n + (j : ℕ) = (l : ℕ) := by
          simpa using congrArg Fin.val hEq
        omega
      simp [Pi.single_apply, hneq]
  | right l =>
      by_cases hl : l = j
      · subst hl
        simp [Pi.single_apply]
      · have hneq : Fin.natAdd n j ≠ Fin.natAdd n l := by
          simpa [Fin.ext_iff, eq_comm] using hl
        simp [Pi.single_apply, hl, hneq]

-- Route correction: Proposition 3.12 needs a rational witness, so the remaining proof must replay
-- the lifted Fourier-Motzkin construction from Theorem 3.11 instead of using only existential
-- polyhedrality.
/-- Helper for Proposition 3.12: the terminal Fourier stage of the lifted cone system, reindexed
back to an explicit `Fin`-indexed real matrix. -/
noncomputable abbrev terminal_lifted_matrix
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℚ) :
    Matrix (Fin (fourier_stage_rows (liftedConeMatrix (R.map (Rat.castHom ℝ))) k)) (Fin n) ℝ :=
  let rowEquiv :
      fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) k ≃
        Fin (fourier_stage_rows (liftedConeMatrix (R.map (Rat.castHom ℝ))) k) :=
    Fintype.equivFin (fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) k)
  let colEquiv :
      Fin (fourier_stage_dim (liftedConeMatrix (R.map (Rat.castHom ℝ))) k) ≃ Fin n :=
    Equiv.cast (congrArg Fin (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))))
  (fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) k).reindex rowEquiv colEquiv

/-- Helper for Proposition 3.12: casting a `Fin`-indexed function across a dimension equality is
the same as precomposing with the inverse `Fin.cast`. -/
lemma cast_fin_fn_eq_comp_rat
    {α : Sort*} {p q : ℕ} (h : p = q) (x : Fin p → α) :
    cast (congrArg (fun t ↦ Fin t → α) h) x = x ∘ Fin.cast h.symm := by
  -- Eliminate the equality proof so that the cast becomes definitional.
  cases h
  rfl

/-- Helper for Proposition 3.12: transporting a fixed-row matrix across a column-dimension
equality evaluates by transporting the column index back with `Fin.cast`. -/
lemma cast_matrix_entry_eq_rat
    {ι : Type*} {p q : ℕ}
    (h : p = q)
    (A : Matrix ι (Fin p) ℝ)
    (i : ι)
    (j : Fin q) :
    cast (congrArg (fun t ↦ Matrix ι (Fin t) ℝ) h) A i j = A i (Fin.cast h.symm j) := by
  -- Eliminate the equality proof so the transported matrix entry becomes definitional.
  cases h
  rfl

/-- Helper for Proposition 3.12: when one more coefficient coordinate remains, its tail length is
the previous tail length minus one. -/
lemma lifted_tail_succ_eq_rat
    {k t : ℕ} (ht : t < k) :
    k - t = (k - (t + 1)) + 1 := by
  -- This is the arithmetic normalization needed to decompose the stage-`t` witness by `Fin.snoc`.
  omega

/-- Helper for Proposition 3.12: rewriting the stage-`t` feasibility witness by decomposing the
surviving coefficient block as a casted `Fin.snoc`. -/
lemma append_snoc_stage_feasibility_iff_rat
    {n k t : ℕ}
    (R : Matrix (Fin n) (Fin k) ℚ)
    {ht : t < k}
    (x : Fin n → ℝ)
    (z : Fin (k - (t + 1)) → ℝ)
    (last : ℝ) :
    fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) t *ᵥ
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            (lifted_fourier_stage_dim_eq_tail
              (R.map (Rat.castHom ℝ)) t (Nat.le_of_lt ht)).symm)
          (Fin.append x
            (cast
              (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq_rat ht).symm)
              (Fin.snoc z last))) ≤
      fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 t
    ↔
    fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) t *ᵥ
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            (lifted_fourier_stage_dim_tail_succ (R.map (Rat.castHom ℝ)) ht).1.symm)
          (Fin.snoc (Fin.append x z) last) ≤
      fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 t := by
  have hvec :
      cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            (lifted_fourier_stage_dim_eq_tail
              (R.map (Rat.castHom ℝ)) t (Nat.le_of_lt ht)).symm)
          (Fin.append x
            (cast
              (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq_rat ht).symm)
              (Fin.snoc z last))) =
      cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            (lifted_fourier_stage_dim_tail_succ (R.map (Rat.castHom ℝ)) ht).1.symm)
          (Fin.snoc (Fin.append x z) last) := by
    let hEqTail :=
      lifted_fourier_stage_dim_eq_tail (R.map (Rat.castHom ℝ)) t (Nat.le_of_lt ht)
    let htail : k - t = (k - (t + 1)) + 1 :=
      lifted_tail_succ_eq_rat ht
    let hsum : n + (k - t) = (n + (k - (t + 1))) + 1 := by
      simp [htail, Nat.add_assoc]
    let hDim := (lifted_fourier_stage_dim_tail_succ (R.map (Rat.castHom ℝ)) ht).1
    have hDimEq : hDim = hEqTail.trans hsum := by
      -- The two public dimension equalities describe the same arithmetic normalization.
      apply Subsingleton.elim
    -- Normalize both casts to `Fin.cast` composition and then use `Fin.append_snoc`.
    calc
      cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hEqTail.symm)
          (Fin.append x
            (cast
              (congrArg (fun q ↦ Fin q → ℝ) htail.symm)
              (Fin.snoc z last)))
          = (Fin.append x
              (cast
                (congrArg (fun q ↦ Fin q → ℝ) htail.symm)
                (Fin.snoc z last))) ∘ Fin.cast hEqTail := by
                rw [cast_fin_fn_eq_comp_rat (h := hEqTail.symm)]
      _ = (Fin.append x (Fin.snoc z last) ∘ Fin.cast (by rw [htail])) ∘ Fin.cast hEqTail := by
            simp [cast_fin_fn_eq_comp_rat, htail, Fin.append_cast_right]
      _ = Fin.snoc (Fin.append x z) last ∘ Fin.cast (hEqTail.trans hsum) := by
            ext i
            simp [Function.comp, Fin.append_snoc, Fin.cast_cast]
      _ = Fin.snoc (Fin.append x z) last ∘ Fin.cast hDim := by
            rw [hDimEq]
      _ = cast
            (congrArg
              (fun q ↦ Fin q → ℝ)
              hDim.symm)
            (Fin.snoc (Fin.append x z) last) := by
            symm
            rw [cast_fin_fn_eq_comp_rat (h := hDim.symm)]
  constructor
  · intro h
    -- Rewrite the casted witness into the `Fin.snoc` form expected by one elimination step.
    rw [hvec] at h
    exact h
  · intro h
    -- Undo the same cast normalization when rebuilding the stage-`t` witness.
    rw [hvec]
    exact h

/-- Helper for Proposition 3.12: the type `Fin (k - k)` is empty. -/
lemma fin_sub_self_false_rat
    {k : ℕ} (i : Fin (k - k)) : False := by
  -- The defining inequality for `i` simplifies to a contradiction.
  simpa using i.2

/-- Helper for Proposition 3.12: after eliminating `t` coefficient coordinates from the lifted cone
system, the remaining feasibility problem keeps the visible vector `x` fixed in the first `n`
coordinates and remembers only the surviving coefficient coordinates. -/
lemma matrix_cone_iff_exists_stage_feasible_rat
    {n k t : ℕ}
    (R : Matrix (Fin n) (Fin k) ℚ)
    (x : Fin n → ℝ)
    (ht : t ≤ k) :
    x ∈ matrix_cone (R.map (Rat.castHom ℝ)) ↔
      ∃ z : Fin (k - t) → ℝ,
        fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) t *ᵥ
            cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                (lifted_fourier_stage_dim_eq_tail (R.map (Rat.castHom ℝ)) t ht).symm)
              (Fin.append x z) ≤
          fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 t := by
  induction t generalizing x with
  | zero =>
      -- Stage `0` is exactly the original lifted feasibility formulation of cone membership.
      simpa using
        (mem_matrix_cone_iff_exists_lifted_feasible
          (R := R.map (Rat.castHom ℝ)) (x := x))
  | succ t ih =>
      have htlt : t < k := Nat.lt_of_succ_le ht
      have htle : t ≤ k := Nat.le_of_lt htlt
      constructor
      · intro hx
        rcases (ih x htle).mp hx with ⟨w, hw⟩
        let w' : Fin ((k - (t + 1)) + 1) → ℝ :=
          cast (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq_rat htlt)) w
        let z : Fin (k - (t + 1)) → ℝ := fun i ↦ w' i.castSucc
        let last : ℝ := w' (Fin.last (k - (t + 1)))
        have hsnoc : Fin.snoc z last = w' := by
          -- Decompose the casted stage-`t` tail witness into its tail and last coordinate.
          simpa [z, last] using fin_snoc_castSucc_last_eq_self w'
        have hw_tail :
            cast
              (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq_rat htlt).symm)
              (Fin.snoc z last) = w := by
          -- Casting the reconstructed `Fin.snoc` tuple back recovers the original witness `w`.
          simpa [w'] using congrArg
            (cast (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq_rat htlt).symm))
            hsnoc
        have hw_cast :
            fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) t *ᵥ
                cast
                  (congrArg
                    (fun q ↦ Fin q → ℝ)
                    (lifted_fourier_stage_dim_eq_tail
                      (R.map (Rat.castHom ℝ)) t htle).symm)
                  (Fin.append x
                    (cast
                      (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq_rat htlt).symm)
                      (Fin.snoc z last))) ≤
              fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 t := by
          -- Rewrite the old witness `w` into the casted `Fin.snoc` form needed for the step lemma.
          simpa [hw_tail] using hw
        have hw_snoc :
            fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) t *ᵥ
                cast
                  (congrArg
                    (fun q ↦ Fin q → ℝ)
                    (lifted_fourier_stage_dim_tail_succ (R.map (Rat.castHom ℝ)) htlt).1.symm)
                  (Fin.snoc (Fin.append x z) last) ≤
              fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 t := by
          -- The adapter removes the remaining cast mismatch between `Fin.append` and `Fin.snoc`.
          exact
            (append_snoc_stage_feasibility_iff_rat (R := R) (ht := htlt) x z last).mp hw_cast
        have hnext :
            fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) (t + 1) *ᵥ
                cast
                  (congrArg
                    (fun q ↦ Fin q → ℝ)
                    (lifted_fourier_stage_dim_tail_succ (R.map (Rat.castHom ℝ)) htlt).2.symm)
                  (Fin.append x z) ≤
              fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 (t + 1) := by
          -- One Fourier-Motzkin elimination step removes the last surviving coefficient coordinate.
          exact
            (lifted_fourier_stage_succ_iff_exists_last
              (R := R.map (Rat.castHom ℝ)) htlt (Fin.append x z)).2 ⟨last, hw_snoc⟩
        refine ⟨z, ?_⟩
        simpa using hnext
      · rintro ⟨z, hz⟩
        have hz' :
            fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) (t + 1) *ᵥ
                cast
                  (congrArg
                    (fun q ↦ Fin q → ℝ)
                    (lifted_fourier_stage_dim_tail_succ (R.map (Rat.castHom ℝ)) htlt).2.symm)
                  (Fin.append x z) ≤
              fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 (t + 1) := by
          -- Reexpress the successor-stage feasibility proposition in the public step-lemma shape.
          simpa using hz
        rcases
          (lifted_fourier_stage_succ_iff_exists_last
            (R := R.map (Rat.castHom ℝ)) htlt (Fin.append x z)).1 hz'
          with ⟨last, hlast⟩
        have hw_cast :
            fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) t *ᵥ
                cast
                  (congrArg
                    (fun q ↦ Fin q → ℝ)
                    (lifted_fourier_stage_dim_eq_tail
                      (R.map (Rat.castHom ℝ)) t htle).symm)
                  (Fin.append x
                    (cast
                      (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq_rat htlt).symm)
                      (Fin.snoc z last))) ≤
              fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 t := by
          -- Undo the adapter to recover the stage-`t` witness in the theorem statement.
          exact
            (append_snoc_stage_feasibility_iff_rat (R := R) (ht := htlt) x z last).mpr hlast
        refine (ih x htle).mpr ?_
        refine ⟨
          cast
            (congrArg (fun q ↦ Fin q → ℝ) (lifted_tail_succ_eq_rat htlt).symm)
            (Fin.snoc z last),
          ?_⟩
        simpa using hw_cast

/-- Helper for Proposition 3.12: after all coefficient coordinates are eliminated, cone membership
is exactly feasibility of the terminal lifted Fourier stage. -/
lemma matrix_cone_iff_terminal_lifted_feasible_rat
    {n k : ℕ}
    (R : Matrix (Fin n) (Fin k) ℚ)
    (x : Fin n → ℝ) :
    x ∈ matrix_cone (R.map (Rat.castHom ℝ)) ↔
      fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) k *ᵥ
          cast
            (congrArg
              (fun q ↦ Fin q → ℝ)
              (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))).symm)
            x ≤
        fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 k := by
  constructor
  · intro hx
    rcases
      (matrix_cone_iff_exists_stage_feasible_rat (R := R) (x := x) (t := k) le_rfl).mp hx
      with ⟨z, hz⟩
    let hEqTail :=
      lifted_fourier_stage_dim_eq_tail (R.map (Rat.castHom ℝ)) k le_rfl
    let hZero : n + (k - k) = n := by
      simp
    let hTerminal := lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))
    have happend : Fin.append x z = x ∘ Fin.cast hZero := by
      -- The terminal coefficient block is indexed by `Fin (k - k)`, so it has no coordinates.
      ext i
      cases i using Fin.addCases with
      | left i =>
          have hi : Fin.cast hZero (Fin.castAdd (k - k) i) = i := by
            ext
            simp
          simpa [Function.comp, hi]
      | right i =>
          exfalso
          exact fin_sub_self_false_rat i
    have hTerminalEq : hTerminal = hEqTail.trans hZero := by
      -- The terminal-stage dimension equality is the stage-tail equality with `k - k = 0`.
      apply Subsingleton.elim
    have hcast :
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hEqTail.symm)
          (Fin.append x z) =
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hTerminal.symm)
          x := by
      -- Rewrite the unique terminal witness away and identify the two public dimension casts.
      calc
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hEqTail.symm)
          (Fin.append x z)
            = Fin.append x z ∘ Fin.cast hEqTail := by
                rw [cast_fin_fn_eq_comp_rat (h := hEqTail.symm)]
        _ = (x ∘ Fin.cast hZero) ∘ Fin.cast hEqTail := by
              rw [happend]
        _ = x ∘ Fin.cast (hEqTail.trans hZero) := by
              ext i
              simp [Function.comp, Fin.cast_cast]
        _ = x ∘ Fin.cast hTerminal := by
              rw [hTerminalEq]
        _ = cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                hTerminal.symm)
              x := by
              symm
              rw [cast_fin_fn_eq_comp_rat (h := hTerminal.symm)]
    rw [hcast] at hz
    exact hz
  · intro hx
    refine
      (matrix_cone_iff_exists_stage_feasible_rat (R := R) (x := x) (t := k) le_rfl).mpr ?_
    let z0 : Fin (k - k) → ℝ := fun i ↦ False.elim (fin_sub_self_false_rat i)
    refine ⟨z0, ?_⟩
    let hEqTail :=
      lifted_fourier_stage_dim_eq_tail (R.map (Rat.castHom ℝ)) k le_rfl
    let hZero : n + (k - k) = n := by
      simp
    let hTerminal := lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))
    have happend :
        Fin.append x z0 = x ∘ Fin.cast hZero := by
      -- Use the unique `Fin 0` witness in the reverse direction as well.
      ext i
      cases i using Fin.addCases with
      | left i =>
          have hi : Fin.cast hZero (Fin.castAdd (k - k) i) = i := by
            ext
            simp
          simpa [Function.comp, hi]
      | right i =>
          exfalso
          exact fin_sub_self_false_rat i
    have hTerminalEq : hTerminal = hEqTail.trans hZero := by
      apply Subsingleton.elim
    have hcast :
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hEqTail.symm)
          (Fin.append x z0) =
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hTerminal.symm)
          x := by
      -- The same terminal cast normalization works for the canonical empty witness.
      calc
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            hEqTail.symm)
          (Fin.append x z0)
            = Fin.append x z0 ∘ Fin.cast hEqTail := by
                rw [cast_fin_fn_eq_comp_rat (h := hEqTail.symm)]
        _ = (x ∘ Fin.cast hZero) ∘ Fin.cast hEqTail := by
              rw [happend]
        _ = x ∘ Fin.cast (hEqTail.trans hZero) := by
              ext i
              simp [Function.comp, Fin.cast_cast]
        _ = x ∘ Fin.cast hTerminal := by
              rw [hTerminalEq]
        _ = cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                hTerminal.symm)
              x := by
              symm
              rw [cast_fin_fn_eq_comp_rat (h := hTerminal.symm)]
    rwa [hcast]

/-- Helper for Proposition 3.12: one Fourier-Motzkin elimination step preserves a pointwise zero
right-hand side. -/
lemma fourier_step_rhs_zero_of_pointwise_zero_rat
    {ι : Type*} {n : ℕ}
    (A : Matrix ι (Fin (n + 1)) ℝ)
    {b : ι → ℝ}
    (hb : ∀ i, b i = 0) :
    ∀ s : FourierStepIndex A, fourier_step_rhs A b s = 0 := by
  intro s
  -- Split the new inequality row according to the explicit Fourier-step rhs formula.
  rcases s with ⟨i, k⟩ | i
  · simp [fourier_step_rhs, hb i.1, hb k.1]
  · simp [fourier_step_rhs, hb i.1]

/-- Helper for Proposition 3.12: one Fourier-Motzkin elimination step preserves entrywise
rational-cast coefficients. -/
lemma fourier_step_matrix_entry_rat_of_entrywise_rat
    {ι : Type*} {n : ℕ}
    (A : Matrix ι (Fin (n + 1)) ℝ)
    (hA : ∀ i j, ∃ q : ℚ, A i j = (q : ℝ)) :
    ∀ s : FourierStepIndex A, ∀ j : Fin n,
      ∃ q : ℚ, fourier_step_matrix A s j = (q : ℝ) := by
  intro s j
  -- Read the explicit step-row formula and combine the rational witnesses by rational arithmetic.
  rcases s with ⟨i, k⟩ | i
  · rcases hA i.1 (Fin.last n) with ⟨qiLast, hqiLast⟩
    rcases hA k.1 (Fin.last n) with ⟨qkLast, hqkLast⟩
    rcases hA i.1 j.castSucc with ⟨qij, hqij⟩
    rcases hA k.1 j.castSucc with ⟨qkj, hqkj⟩
    refine ⟨qiLast * qkj - qkLast * qij, ?_⟩
    calc
      fourier_step_matrix A (Sum.inl (i, k)) j
          = (qiLast : ℝ) * (qkj : ℝ) - (qkLast : ℝ) * (qij : ℝ) := by
              simp [fourier_step_matrix, hqiLast, hqkLast, hqij, hqkj]
      _ = ((qiLast * qkj : ℚ) : ℝ) - ((qkLast * qij : ℚ) : ℝ) := by
            rw [Rat.cast_mul, Rat.cast_mul]
      _ = ((qiLast * qkj - qkLast * qij : ℚ) : ℝ) := by
            rw [← Rat.cast_sub]
  · simpa [fourier_step_matrix] using hA i.1 j.castSucc

/-- Helper for Proposition 3.12: the iterated Fourier-Motzkin right-hand side stays identically
zero when the lifted cone system starts with zero right-hand side. -/
lemma lifted_fourier_stage_rhs_eq_zero_rat
    {n k t : ℕ}
    (R : Matrix (Fin n) (Fin k) ℚ)
    (ht : t ≤ k) :
    ∀ i : fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) t,
      fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 t i = 0 := by
  induction t with
  | zero =>
      intro i
      -- At stage `0` the right-hand side is literally the zero function.
      rfl
  | succ t ih =>
      intro i
      let M : Matrix (Fin (n + (n + k))) (Fin (n + k)) ℝ :=
        liftedConeMatrix (R.map (Rat.castHom ℝ))
      have htlt : t < k := Nat.lt_of_succ_le ht
      have htle : t ≤ k := Nat.le_of_lt htlt
      let r : ℕ := n + (k - (t + 1))
      have hDim : fourier_stage_dim M t = r + 1 := by
        simpa [M, r] using (lifted_fourier_stage_dim_tail_succ (R.map (Rat.castHom ℝ)) htlt).1
      have hNext : fourier_stage_dim M (t + 1) = r := by
        simpa [M, r] using (lifted_fourier_stage_dim_tail_succ (R.map (Rat.castHom ℝ)) htlt).2
      let Mk : Matrix (fourier_stage_row M t) (Fin (r + 1)) ℝ :=
        cast
          (congrArg (fun q ↦ Matrix (fourier_stage_row M t) (Fin q) ℝ) hDim)
          (fourier_stage_matrix M t)
      rcases fourier_stage_succ_reindex_data M 0 hDim hNext with ⟨e, _, hRhsEq⟩
      have hPrev :
          ∀ j : fourier_stage_row M t, fourier_stage_rhs M 0 t j = 0 := by
        simpa [M] using ih htle
      -- Rewrite the successor-stage rhs through the one-step rhs and invoke the zero-rhs closure.
      calc
        fourier_stage_rhs M 0 (t + 1) i
            = fourier_step_rhs Mk (fourier_stage_rhs M 0 t) (e i) := by
                simpa [Mk] using congrFun hRhsEq i
        _ = 0 := fourier_step_rhs_zero_of_pointwise_zero_rat Mk hPrev (e i)

/-- Helper for Proposition 3.12: multiplying by the terminal reindexed matrix is the same as
evaluating the terminal Fourier-stage matrix on the casted visible vector. -/
lemma terminal_lifted_matrix_mulVec_apply
    {n k : ℕ}
    (R : Matrix (Fin n) (Fin k) ℚ)
    (x : Fin n → ℝ)
    (i : Fin (fourier_stage_rows (liftedConeMatrix (R.map (Rat.castHom ℝ))) k)) :
    ((terminal_lifted_matrix R) *ᵥ x) i =
      (fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) k *ᵥ
          cast
            (congrArg
              (fun q ↦ Fin q → ℝ)
              (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))).symm)
            x)
        ((Fintype.equivFin (fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) k)).symm i) := by
  let rowEquiv :
      fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) k ≃
        Fin (fourier_stage_rows (liftedConeMatrix (R.map (Rat.castHom ℝ))) k) :=
    Fintype.equivFin (fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) k)
  let colEquiv :
      Fin (fourier_stage_dim (liftedConeMatrix (R.map (Rat.castHom ℝ))) k) ≃ Fin n :=
    Equiv.cast (congrArg Fin (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))))
  have hcastVec :
      x ∘ colEquiv =
        cast
          (congrArg
            (fun q ↦ Fin q → ℝ)
            (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))).symm)
          x := by
    -- The terminal column equivalence is exactly the visible `Fin.cast` transport.
    have hcol :
        (colEquiv : Fin (fourier_stage_dim (liftedConeMatrix (R.map (Rat.castHom ℝ))) k) → Fin n) =
          Fin.cast (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))) := by
      simpa [colEquiv] using
        (Fin.cast_eq_cast'
          (congrArg Fin (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ)))))
    rw [hcol]
    rw [cast_fin_fn_eq_comp_rat
      (h := (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))).symm)]
  have hmul :
      terminal_lifted_matrix R *ᵥ x =
        (fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) k *ᵥ
            cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))).symm)
              x) ∘
          rowEquiv.symm := by
    -- Reindexing only renames rows and transports the visible columns back to `Fin n`.
    calc
      terminal_lifted_matrix R *ᵥ x =
          (fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) k *ᵥ
              (x ∘ colEquiv)) ∘
            rowEquiv.symm := by
              simpa [terminal_lifted_matrix, rowEquiv, colEquiv] using
                (Matrix.submatrix_mulVec_equiv
                  (fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) k)
                  x
                  rowEquiv.symm
                  colEquiv.symm)
      _ =
          (fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) k *ᵥ
              cast
                (congrArg
                  (fun q ↦ Fin q → ℝ)
                  (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))).symm)
                x) ∘
            rowEquiv.symm := by
              rw [hcastVec]
  -- Evaluate the reindexed product on the chosen terminal row.
  simpa [rowEquiv] using congrFun hmul i

/-- Helper for Proposition 3.12: the terminal lifted Fourier stage gives an explicit homogeneous
matrix presentation of the cone generated by the rational columns of `R`. -/
lemma matrix_cone_eq_terminal_lifted_polyhedral_cone
    {n k : ℕ}
    (R : Matrix (Fin n) (Fin k) ℚ) :
    (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin n → ℝ)) =
      matrix_polyhedral_cone (terminal_lifted_matrix R) := by
  let rowEquiv :
      fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) k ≃
        Fin (fourier_stage_rows (liftedConeMatrix (R.map (Rat.castHom ℝ))) k) :=
    Fintype.equivFin (fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) k)
  ext x
  constructor
  · intro hx
    have hxStage := (matrix_cone_iff_terminal_lifted_feasible_rat (R := R) (x := x)).1 hx
    refine (mem_matrix_polyhedral_cone (terminal_lifted_matrix R) x).2 ?_
    intro i
    change ((terminal_lifted_matrix R) *ᵥ x) i ≤ 0
    -- Rewrite the visible terminal matrix inequality back to the terminal Fourier-stage system.
    rw [terminal_lifted_matrix_mulVec_apply (R := R) (x := x) (i := i)]
    have hzero :
        fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 k (rowEquiv.symm i) = 0 :=
      lifted_fourier_stage_rhs_eq_zero_rat (R := R) (t := k) le_rfl (rowEquiv.symm i)
    have hstage := hxStage (rowEquiv.symm i)
    rw [hzero] at hstage
    exact hstage
  · intro hx
    have hxPoly := (mem_matrix_polyhedral_cone (terminal_lifted_matrix R) x).1 hx
    refine (matrix_cone_iff_terminal_lifted_feasible_rat (R := R) (x := x)).2 ?_
    intro i
    have hxi := hxPoly (rowEquiv i)
    -- Evaluate the reindexed terminal inequality on the corresponding visible row.
    rw [terminal_lifted_matrix_mulVec_apply (R := R) (x := x) (i := rowEquiv i)] at hxi
    have happly : rowEquiv.symm (rowEquiv i) = i := by
      exact rowEquiv.symm_apply_apply i
    have hxi' :
        (fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) k *ᵥ
            cast
              (congrArg
                (fun q ↦ Fin q → ℝ)
                (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))).symm)
              x)
            i ≤
          0 := by
      rw [happly] at hxi
      exact hxi
    have hzero :
        fourier_stage_rhs (liftedConeMatrix (R.map (Rat.castHom ℝ))) 0 k i = 0 :=
      lifted_fourier_stage_rhs_eq_zero_rat (R := R) (t := k) le_rfl i
    rw [hzero]
    exact hxi'

/-- Helper for Proposition 3.12: every entry of the lifted cone matrix is a rational cast. -/
lemma lifted_cone_matrix_entries_are_rational
    {n k : ℕ}
    (R : Matrix (Fin n) (Fin k) ℚ) :
    ∀ i : Fin (n + (n + k)), ∀ j : Fin (n + k),
      ∃ q : ℚ, liftedConeMatrix (R.map (Rat.castHom ℝ)) i j = (q : ℝ) := by
  intro i j
  cases j using Fin.addCases with
  | left jx =>
      cases i using Fin.addCases with
      | left ix =>
          -- Read an `x`-column through the first lifted block by testing against the
          -- corresponding standard basis vector in the visible coordinates.
          by_cases hix : ix = jx
          · refine ⟨1, ?_⟩
            have hvec := single_castAdd_eq_append_single_zero (k := k) jx
            have hentry :
                liftedConeMatrix (R.map (Rat.castHom ℝ)) (Fin.castAdd (n + k) ix)
                    (Fin.castAdd k jx) =
                  (liftedConeMatrix (R.map (Rat.castHom ℝ)) *ᵥ
                      Fin.append (Pi.single jx 1) 0) (Fin.castAdd (n + k) ix) := by
              simpa [Matrix.col, hvec] using
                (congrFun
                  (Matrix.mulVec_single_one
                    (liftedConeMatrix (R.map (Rat.castHom ℝ)))
                    (Fin.castAdd k jx))
                  (Fin.castAdd (n + k) ix)).symm
            rw [hentry, liftedConeMatrix_first_block]
            simp [Pi.single_apply, hix, eq_comm]
          · refine ⟨0, ?_⟩
            have hvec := single_castAdd_eq_append_single_zero (k := k) jx
            have hentry :
                liftedConeMatrix (R.map (Rat.castHom ℝ)) (Fin.castAdd (n + k) ix)
                    (Fin.castAdd k jx) =
                  (liftedConeMatrix (R.map (Rat.castHom ℝ)) *ᵥ
                      Fin.append (Pi.single jx 1) 0) (Fin.castAdd (n + k) ix) := by
              simpa [Matrix.col, hvec] using
                (congrFun
                  (Matrix.mulVec_single_one
                    (liftedConeMatrix (R.map (Rat.castHom ℝ)))
                    (Fin.castAdd k jx))
                  (Fin.castAdd (n + k) ix)).symm
            rw [hentry, liftedConeMatrix_first_block]
            simp [Pi.single_apply, hix, eq_comm]
      | right irest =>
          cases irest using Fin.addCases with
          | left ix =>
              -- The second lifted block contributes the negated visible standard basis row.
              by_cases hix : ix = jx
              · refine ⟨-1, ?_⟩
                have hvec := single_castAdd_eq_append_single_zero (k := k) jx
                have hentry :
                    liftedConeMatrix (R.map (Rat.castHom ℝ))
                        (Fin.natAdd n (Fin.castAdd k ix))
                        (Fin.castAdd k jx) =
                      (liftedConeMatrix (R.map (Rat.castHom ℝ)) *ᵥ
                          Fin.append (Pi.single jx 1) 0) (Fin.natAdd n (Fin.castAdd k ix)) := by
                  simpa [Matrix.col, hvec] using
                    (congrFun
                      (Matrix.mulVec_single_one
                        (liftedConeMatrix (R.map (Rat.castHom ℝ)))
                        (Fin.castAdd k jx))
                      (Fin.natAdd n (Fin.castAdd k ix))).symm
                rw [hentry, liftedConeMatrix_second_block]
                simp [Pi.single_apply, hix, eq_comm]
              · refine ⟨0, ?_⟩
                have hvec := single_castAdd_eq_append_single_zero (k := k) jx
                have hentry :
                    liftedConeMatrix (R.map (Rat.castHom ℝ))
                        (Fin.natAdd n (Fin.castAdd k ix))
                        (Fin.castAdd k jx) =
                      (liftedConeMatrix (R.map (Rat.castHom ℝ)) *ᵥ
                          Fin.append (Pi.single jx 1) 0) (Fin.natAdd n (Fin.castAdd k ix)) := by
                  simpa [Matrix.col, hvec] using
                    (congrFun
                      (Matrix.mulVec_single_one
                        (liftedConeMatrix (R.map (Rat.castHom ℝ)))
                        (Fin.castAdd k jx))
                      (Fin.natAdd n (Fin.castAdd k ix))).symm
                rw [hentry, liftedConeMatrix_second_block]
                simp [Pi.single_apply, hix, eq_comm]
          | right ik =>
              -- The trailing nonnegativity block has zero coefficients on the visible columns.
              refine ⟨0, ?_⟩
              have hvec := single_castAdd_eq_append_single_zero (k := k) jx
              have hentry :
                  liftedConeMatrix (R.map (Rat.castHom ℝ))
                      (Fin.natAdd n (Fin.natAdd n ik))
                      (Fin.castAdd k jx) =
                    (liftedConeMatrix (R.map (Rat.castHom ℝ)) *ᵥ
                        Fin.append (Pi.single jx 1) 0) (Fin.natAdd n (Fin.natAdd n ik)) := by
                simpa [Matrix.col, hvec] using
                  (congrFun
                    (Matrix.mulVec_single_one
                      (liftedConeMatrix (R.map (Rat.castHom ℝ)))
                      (Fin.castAdd k jx))
                    (Fin.natAdd n (Fin.natAdd n ik))).symm
              rw [hentry, liftedConeMatrix_third_block]
              simp
  | right jμ =>
      cases i using Fin.addCases with
      | left ix =>
          -- A coefficient-column in the first block is the negated corresponding column of `R`.
          refine ⟨-R ix jμ, ?_⟩
          have hvec := single_natAdd_eq_append_zero_single (n := n) jμ
          have hentry :
              liftedConeMatrix (R.map (Rat.castHom ℝ)) (Fin.castAdd (n + k) ix)
                  (Fin.natAdd n jμ) =
                (liftedConeMatrix (R.map (Rat.castHom ℝ)) *ᵥ
                    Fin.append 0 (Pi.single jμ 1)) (Fin.castAdd (n + k) ix) := by
            simpa [Matrix.col, hvec] using
              (congrFun
                (Matrix.mulVec_single_one
                  (liftedConeMatrix (R.map (Rat.castHom ℝ)))
                  (Fin.natAdd n jμ))
                (Fin.castAdd (n + k) ix)).symm
          rw [hentry, liftedConeMatrix_first_block]
          simp
      | right irest =>
          cases irest using Fin.addCases with
          | left ix =>
              -- A coefficient-column in the second block is the corresponding column of `R`.
              refine ⟨R ix jμ, ?_⟩
              have hvec := single_natAdd_eq_append_zero_single (n := n) jμ
              have hentry :
                  liftedConeMatrix (R.map (Rat.castHom ℝ))
                      (Fin.natAdd n (Fin.castAdd k ix))
                      (Fin.natAdd n jμ) =
                    (liftedConeMatrix (R.map (Rat.castHom ℝ)) *ᵥ
                        Fin.append 0 (Pi.single jμ 1)) (Fin.natAdd n (Fin.castAdd k ix)) := by
                simpa [Matrix.col, hvec] using
                  (congrFun
                    (Matrix.mulVec_single_one
                      (liftedConeMatrix (R.map (Rat.castHom ℝ)))
                      (Fin.natAdd n jμ))
                    (Fin.natAdd n (Fin.castAdd k ix))).symm
              rw [hentry, liftedConeMatrix_second_block]
              simp
          | right ik =>
              -- In the trailing block the coefficient columns form `-I_k`.
              by_cases hik : ik = jμ
              · refine ⟨-1, ?_⟩
                have hvec := single_natAdd_eq_append_zero_single (n := n) jμ
                have hentry :
                    liftedConeMatrix (R.map (Rat.castHom ℝ))
                        (Fin.natAdd n (Fin.natAdd n ik))
                        (Fin.natAdd n jμ) =
                      (liftedConeMatrix (R.map (Rat.castHom ℝ)) *ᵥ
                          Fin.append 0 (Pi.single jμ 1)) (Fin.natAdd n (Fin.natAdd n ik)) := by
                  simpa [Matrix.col, hvec] using
                    (congrFun
                      (Matrix.mulVec_single_one
                        (liftedConeMatrix (R.map (Rat.castHom ℝ)))
                        (Fin.natAdd n jμ))
                      (Fin.natAdd n (Fin.natAdd n ik))).symm
                rw [hentry, liftedConeMatrix_third_block]
                simp [Pi.single_apply, hik, eq_comm]
              · refine ⟨0, ?_⟩
                have hvec := single_natAdd_eq_append_zero_single (n := n) jμ
                have hentry :
                    liftedConeMatrix (R.map (Rat.castHom ℝ))
                        (Fin.natAdd n (Fin.natAdd n ik))
                        (Fin.natAdd n jμ) =
                      (liftedConeMatrix (R.map (Rat.castHom ℝ)) *ᵥ
                          Fin.append 0 (Pi.single jμ 1)) (Fin.natAdd n (Fin.natAdd n ik)) := by
                  simpa [Matrix.col, hvec] using
                    (congrFun
                      (Matrix.mulVec_single_one
                        (liftedConeMatrix (R.map (Rat.castHom ℝ)))
                        (Fin.natAdd n jμ))
                      (Fin.natAdd n (Fin.natAdd n ik))).symm
                rw [hentry, liftedConeMatrix_third_block]
                simp [Pi.single_apply, hik, eq_comm]

/-- Helper for Proposition 3.12: every Fourier stage of the lifted cone matrix still has rational
entries, because one elimination step uses only addition, subtraction, and multiplication. -/
lemma lifted_fourier_stage_matrix_entries_are_rational
    {n k t : ℕ}
    (R : Matrix (Fin n) (Fin k) ℚ)
    (ht : t ≤ k)
    (i : fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) t)
    (j : Fin (fourier_stage_dim (liftedConeMatrix (R.map (Rat.castHom ℝ))) t)) :
    ∃ q : ℚ,
      fourier_stage_matrix (liftedConeMatrix (R.map (Rat.castHom ℝ))) t i j = (q : ℝ) := by
  induction t with
  | zero =>
      -- Stage `0` is the lifted cone matrix itself.
      simpa using lifted_cone_matrix_entries_are_rational (R := R) i j
  | succ t ih =>
      let M : Matrix (Fin (n + (n + k))) (Fin (n + k)) ℝ :=
        liftedConeMatrix (R.map (Rat.castHom ℝ))
      have htlt : t < k := Nat.lt_of_succ_le ht
      have htle : t ≤ k := Nat.le_of_lt htlt
      let r : ℕ := n + (k - (t + 1))
      have hDim : fourier_stage_dim M t = r + 1 := by
        simpa [M, r] using (lifted_fourier_stage_dim_tail_succ (R.map (Rat.castHom ℝ)) htlt).1
      let Mk : Matrix (fourier_stage_row M t) (Fin (r + 1)) ℝ :=
        cast
          (congrArg (fun q ↦ Matrix (fourier_stage_row M t) (Fin q) ℝ) hDim)
          (fourier_stage_matrix M t)
      have hMk :
          ∀ a : fourier_stage_row M t, ∀ b : Fin (r + 1), ∃ q : ℚ, Mk a b = (q : ℝ) := by
        intro a b
        rcases ih htle a (Fin.cast hDim.symm b) with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        -- Read the casted predecessor-stage entry by transporting the column index back.
        rw [show Mk a b = fourier_stage_matrix M t a (Fin.cast hDim.symm b) by
          simpa [Mk] using cast_matrix_entry_eq_rat hDim (fourier_stage_matrix M t) a b]
        simpa [M] using hq
      have hNext : fourier_stage_dim M (t + 1) = r := by
        simpa [M, r] using (lifted_fourier_stage_dim_tail_succ (R.map (Rat.castHom ℝ)) htlt).2
      rcases fourier_stage_succ_reindex_data M 0 hDim hNext with ⟨e, hMatrixEq, _⟩
      -- Normalize the successor-stage columns so the reindexed step matrix can be read entrywise.
      have hEntry :
          fourier_stage_matrix M (t + 1) i j =
            fourier_step_matrix Mk (e i) (Fin.cast hNext j) := by
        -- Read the successor-stage casted entry through the reindexing equivalence from one step.
        have hEntry0 := congrFun (congrFun hMatrixEq i) j
        have hCastEntry :=
          cast_matrix_entry_eq_rat
            (h := hNext.symm)
            (((fourier_step_matrix Mk).reindex e.symm (Equiv.refl _)))
            i
            j
        rw [hCastEntry] at hEntry0
        simpa [Matrix.reindex_apply] using hEntry0
      rcases
        fourier_step_matrix_entry_rat_of_entrywise_rat Mk hMk (e i) (Fin.cast hNext j)
        with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      rw [hEntry, hq]

/-- Helper for Proposition 3.12: the explicit terminal witness matrix has rational entries. -/
lemma terminal_lifted_matrix_entries_are_rational
    {n k : ℕ}
    (R : Matrix (Fin n) (Fin k) ℚ) :
    ∀ i j, ∃ q : ℚ, terminal_lifted_matrix R i j = (q : ℝ) := by
  intro i j
  let rowEquiv :
      fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) k ≃
        Fin (fourier_stage_rows (liftedConeMatrix (R.map (Rat.castHom ℝ))) k) :=
    Fintype.equivFin (fourier_stage_row (liftedConeMatrix (R.map (Rat.castHom ℝ))) k)
  let colEquiv :
      Fin (fourier_stage_dim (liftedConeMatrix (R.map (Rat.castHom ℝ))) k) ≃ Fin n :=
    Equiv.cast (congrArg Fin (lifted_fourier_stage_dim_terminal (R.map (Rat.castHom ℝ))))
  -- The terminal witness is only a row/column reindexing of the terminal Fourier stage.
  simpa [terminal_lifted_matrix, rowEquiv, colEquiv] using
    lifted_fourier_stage_matrix_entries_are_rational
      (R := R)
      (t := k)
      le_rfl
      (rowEquiv.symm i)
      (colEquiv.symm j)

lemma exists_rational_polyhedral_presentation_of_matrix_cone
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℚ) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℚ,
      (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin n → ℝ)) =
        matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) := by
  -- Use the explicit terminal lifted matrix from Theorem 3.11 and then descend its rational
  -- entries back to a genuine rational matrix.
  let Aterm := terminal_lifted_matrix R
  have hAterm : ∀ i j, ∃ q : ℚ, Aterm i j = (q : ℝ) :=
    terminal_lifted_matrix_entries_are_rational (R := R)
  rcases matrix_eq_rat_cast_of_entrywise_rational hAterm with ⟨Aℚ, hAℚ⟩
  refine ⟨fourier_stage_rows (liftedConeMatrix (R.map (Rat.castHom ℝ))) k, Aℚ, ?_⟩
  -- Replace the explicit real terminal matrix by the equal rational cast matrix.
  calc
    (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin n → ℝ)) =
        matrix_polyhedral_cone Aterm := by
          simpa [Aterm] using matrix_cone_eq_terminal_lifted_polyhedral_cone (R := R)
    _ = matrix_polyhedral_cone (Aℚ.map (Rat.castHom ℝ)) := by
          simpa [Aterm] using congrArg matrix_polyhedral_cone hAℚ

/-- Proposition 3.12 (1). Given a rational matrix `A`, the cone `{x : ℝ^n | A x ≤ 0}` is generated
by finitely many rational vectors, represented here as the columns of a rational matrix `R`. -/
theorem exists_rational_matrix_cone_of_rational_matrix_polyhedral_cone
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    ∃ k : ℕ, ∃ R : Matrix (Fin n) (Fin k) ℚ,
      matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) =
        (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin n → ℝ)) := by
  -- Apply the rational forward half to the row cone of `A`, exactly as in Theorem 3.11.
  rcases exists_rational_polyhedral_presentation_of_matrix_cone A.transpose with ⟨k, B, hdual⟩
  refine ⟨k, B.transpose, ?_⟩
  have hdual' :
      (matrix_cone (A.map (Rat.castHom ℝ)).transpose : Set (Fin n → ℝ)) =
        matrix_polyhedral_cone (B.map (Rat.castHom ℝ)) := by
    -- Reinterpret the helper equality as a presentation of the dual row cone of `A`.
    simpa [Matrix.transpose_map] using hdual
  ext x
  constructor
  · intro hx
    -- The dual presentation of the row cone converts the homogeneous system into row generators.
    simpa [Matrix.transpose_map] using
      matrix_polyhedral_cone_subset_matrix_cone_transpose_of_dual_presentation hdual' hx
  · intro hx
    -- The converse inclusion is the matching dual-cone implication from Theorem 3.11.
    simpa [Matrix.transpose_map] using
      matrix_cone_transpose_subset_matrix_polyhedral_of_dual_presentation hdual' hx

/-- Proposition 3.12 (2). Given finitely many rational vectors, represented here as the columns of
a rational matrix `R`, the cone they generate is the solution set of a homogeneous rational matrix
inequality system. -/
theorem exists_rational_matrix_polyhedral_cone_of_rational_matrix_cone
    {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℚ) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℚ,
      (matrix_cone (R.map (Rat.castHom ℝ)) : Set (Fin n → ℝ)) =
        matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) := by
  -- This is exactly the rational forward helper isolated above.
  simpa using exists_rational_polyhedral_presentation_of_matrix_cone R
