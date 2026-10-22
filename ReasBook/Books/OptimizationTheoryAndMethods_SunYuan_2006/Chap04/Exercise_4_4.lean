/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_2_9
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_1_3

open Matrix

noncomputable section

-- Domain sampling:
-- * primary domain: nonlinear conjugate-gradient methods on quadratic objectives in `ℝ^n`;
-- * inspected project declarations:
--   `ConjugateGradientRun`,
--   `PolakRibierePolyakConjugateGradientMethod`,
--   `ConjugateGradientRun.DaiYuan`,
--   `IsQuadraticConjugateDirectionMethod.conjugateFamily`;
-- * owner choice:
--   `ConjugateGradientRun` is the primitive Chapter 4 owner for iterate/gradient/direction/step
--   data, so Dixon data belongs as a `bridge/view` on that owner rather than as a second
--   standalone run owner;
-- * primitive data vs derived API:
--   the run data is primitive in `ConjugateGradientRun`, while the Dixon coefficient and
--   direction recurrence are the only new method-specific fields here.

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Dixon coefficient `β_k = -⟪g_(k + 1), g_(k + 1)⟫ / ⟪d_k, g_k⟫`. -/
def dixonBeta (gPrev gNext dPrev : E) : ℝ :=
  -inner ℝ gNext gNext / inner ℝ dPrev gPrev

end

section

variable {n : ℕ}

local notation "Point" => ConjugateGradientPoint n

/-- Helper for Chapter04 Exercise 4.4: positive definiteness makes the quadratic bilinear pairing
`uᵀ G v` symmetric. -/
private theorem dotProduct_mulVec_comm_of_posDef
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (u v : Point) :
    dotProduct u (G.mulVec v) = dotProduct v (G.mulVec u) := by
  -- Symmetry of `G` turns the matrix pairing into a symmetric bilinear form.
  have hsymm : G.IsSymm := posDef_isSymm hG
  simpa [hsymm.eq] using Matrix.dotProduct_transpose_mulVec G u v

/-- Helper for Chapter04 Exercise 4.4: a nonzero Euclidean vector has positive self dot product. -/
private theorem dotProduct_self_pos_of_ne_zero {v : Point} (hv : v ≠ 0) :
    0 < dotProduct v v := by
  have hnorm_sq : dotProduct v v = ‖v‖ ^ 2 := by
    have h := EuclideanSpace.inner_eq_star_dotProduct v v
    simpa [real_inner_self_eq_norm_sq] using h.symm
  rw [hnorm_sq]
  exact sq_pos_iff.mpr (norm_ne_zero_iff.mpr hv)

/-- Helper for Chapter04 Exercise 4.4: every accepted quadratic step updates the gradient by the
Hessian action on the accepted displacement. -/
private theorem run_quadratic_gradient_step_eq
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {b : Point} {c : ℝ}
    {method : ConjugateGradientRun Point (quadraticObjective G b c)}
    {k : ℕ} (_ : method.g k ≠ 0)
    (hUpdate : method.x (k + 1) = method.x k + method.α k • method.d k) :
    method.g (k + 1) = method.g k + method.α k • Matrix.toEuclideanLin G (method.d k) := by
  have hGsymm : G.IsSymm := posDef_isSymm hG
  have hgk : method.g k = Matrix.toEuclideanLin G (method.x k) + b := by
    -- Identify the recorded gradient with the explicit quadratic gradient at the current iterate.
    calc
      method.g k = gradient (quadraticObjective G b c) (method.x k) := by
        symm
        exact method.gradient_eq k
      _ = Matrix.toEuclideanLin G (method.x k) + b :=
        gradient_quadraticObjective G b c hGsymm (method.x k)
  have hgk1 : method.g (k + 1) = Matrix.toEuclideanLin G (method.x (k + 1)) + b := by
    -- The same explicit quadratic-gradient formula holds at the next iterate.
    calc
      method.g (k + 1) = gradient (quadraticObjective G b c) (method.x (k + 1)) := by
        symm
        exact method.gradient_eq (k + 1)
      _ = Matrix.toEuclideanLin G (method.x (k + 1)) + b :=
        gradient_quadraticObjective G b c hGsymm (method.x (k + 1))
  -- Substituting the iterate update reduces the claim to linearity of `toEuclideanLin`.
  calc
    method.g (k + 1) = Matrix.toEuclideanLin G (method.x (k + 1)) + b := hgk1
    _ = Matrix.toEuclideanLin G (method.x k + method.α k • method.d k) + b := by
      rw [hUpdate]
    _ = Matrix.toEuclideanLin G (method.x k) +
          method.α k • Matrix.toEuclideanLin G (method.d k) + b := by
      simp
    _ = method.g k + method.α k • Matrix.toEuclideanLin G (method.d k) := by
      rw [hgk]
      abel

/-- Helper for Chapter04 Exercise 4.4: for any exact-line-search two-term recurrence whose
coefficient satisfies the textbook scalar identity
`β_k * ⟪d_k, g_k⟫ = -‖g_(k + 1)‖²`, the standard orthogonality and conjugacy invariants propagate
inductively on a positive-definite quadratic objective. -/
private theorem recurrence_step_invariants
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {b : Point} {c : ℝ}
    {method : ConjugateGradientRun Point (quadraticObjective G b c)} {β : ℕ → ℝ}
    (h_direction_zero : method.d 0 = -method.g 0)
    (h_exactLineSearch :
      ∀ k : ℕ, k < n → method.g k ≠ 0 →
        IsExactLineSearchStepOnNonnegativeRay
          (quadraticObjective G b c) (method.x k) (method.d k) (method.α k))
    (h_iterate_eq :
      ∀ k : ℕ, k < n → method.g k ≠ 0 →
        method.x (k + 1) = method.x k + method.α k • method.d k)
    (h_beta_mul :
      ∀ k : ℕ, k < n → (hk : method.g k ≠ 0) → (hkNext : method.g (k + 1) ≠ 0) →
        dotProduct (method.g (k + 1)) (method.g k) = 0 →
        dotProduct (method.d k) (method.g k) = -dotProduct (method.g k) (method.g k) →
        β k * dotProduct (method.d k) (method.g k) =
          -dotProduct (method.g (k + 1)) (method.g (k + 1)))
    (h_direction_eq :
      ∀ k : ℕ, k < n → method.g k ≠ 0 → method.g (k + 1) ≠ 0 →
        method.d (k + 1) = -method.g (k + 1) + β k • method.d k)
    (h_nonstationary : ∀ k : ℕ, k < n → method.g k ≠ 0) :
    ∀ {k : ℕ}, k < n →
      (∀ j : ℕ, j ≤ k → dotProduct (method.g (k + 1)) (method.d j) = 0) ∧
      (∀ j : ℕ, j ≤ k → dotProduct (method.g (k + 1)) (method.g j) = 0) ∧
      dotProduct (method.d k) (method.g k) = -dotProduct (method.g k) (method.g k) ∧
      (∀ j : ℕ, j < k →
        dotProduct (method.d k) (method.g j) = -dotProduct (method.g k) (method.g k)) ∧
      (∀ j : ℕ, j < k → dotProduct (method.d k) (G.mulVec (method.d j)) = 0) := by
  intro k hk
  refine Nat.strong_induction_on k ?_ hk
  intro k ih hk
  cases k with
  | zero =>
      have h0 : method.g 0 ≠ 0 := h_nonstationary 0 hk
      have hdir_grad :
          dotProduct (method.d 0) (method.g 0) = -dotProduct (method.g 0) (method.g 0) := by
        -- The initial direction is the steepest-descent direction `-g₀`.
        simp [h_direction_zero]
      have hdescent :
          IsDescentDirectionAt
            (quadraticObjective G b c) (method.x 0) (method.d 0) := by
        have hdot :
            dotProduct (method.g 0) (method.d 0) =
              -dotProduct (method.g 0) (method.g 0) := by
          simpa [dotProduct_comm] using hdir_grad
        have hinner :
            inner ℝ (gradient (quadraticObjective G b c) (method.x 0)) (method.d 0) =
              -dotProduct (method.g 0) (method.g 0) := by
          simpa [method.gradient_eq 0, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
            using hdot
        have hgg_pos : 0 < dotProduct (method.g 0) (method.g 0) := by
          exact dotProduct_self_pos_of_ne_zero h0
        have hneg :
            inner ℝ (gradient (quadraticObjective G b c) (method.x 0)) (method.d 0) < 0 := by
          rw [hinner]
          linarith
        simpa [IsDescentDirectionAt, method.gradient_eq 0,
          EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hneg
      have hAlphaPos : 0 < method.α 0 :=
        exactLineSearchStep_pos_of_descent
          (quadraticObjective G b c) (method.x 0) (method.d 0) (method.α 0)
          hdescent (h_exactLineSearch 0 hk h0)
      have hUpdate : method.x 1 = method.x 0 + method.α 0 • method.d 0 := h_iterate_eq 0 hk h0
      have hgrad_dir :
          dotProduct (method.g 1) (method.d 0) = 0 := by
        -- A positive exact line-search step is stationary in the search direction.
        have hstationary :
            inner ℝ (gradient (quadraticObjective G b c) (method.x 0 + method.α 0 • method.d 0))
              (method.d 0) = 0 :=
          exactLineSearch_stationary_inner_eq_zero_of_pos
            (quadraticObjective G b c) (method.x 0) (method.d 0) (method.α 0)
            hAlphaPos (h_exactLineSearch 0 hk h0)
            (fun x ↦ by
              simpa [gradient_quadraticObjective G b c (posDef_isSymm hG) x] using
                hasGradientAt_quadraticObjective G b c (posDef_isSymm hG) x)
        have hgrad :
            gradient (quadraticObjective G b c) (method.x 0 + method.α 0 • method.d 0) =
              method.g 1 := by
          calc
            gradient (quadraticObjective G b c) (method.x 0 + method.α 0 • method.d 0)
                = gradient (quadraticObjective G b c) (method.x 1) := by rw [← hUpdate]
            _ = method.g 1 := method.gradient_eq 1
        simpa [hgrad, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hstationary
      have hgrad_grad : dotProduct (method.g 1) (method.g 0) = 0 := by
        -- The first exact line search makes `g₁` orthogonal to `g₀ = -d₀`.
        simpa [h_direction_zero, dotProduct_comm] using hgrad_dir
      refine ⟨?_, ?_, hdir_grad, ?_, ?_⟩
      · intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        simpa [hj0] using hgrad_dir
      · intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        simpa [hj0] using hgrad_grad
      · intro j hj
        exact (Nat.not_lt_zero _ hj).elim
      · intro j hj
        exact (Nat.not_lt_zero _ hj).elim
  | succ k =>
      have hk_lt_n : k < n := Nat.lt_of_succ_lt hk
      have hk_nonzero : method.g k ≠ 0 := h_nonstationary k hk_lt_n
      have hk1_nonzero : method.g (k + 1) ≠ 0 := h_nonstationary (k + 1) hk
      have hPrev := ih k (Nat.lt_succ_self k) hk_lt_n
      rcases hPrev with ⟨hPrevGradDir, hPrevGradGrad, hPrevDirGrad, hPrevDirPrevGrad, hPrevConj⟩
      have hdir_eq :
          method.d (k + 1) = -method.g (k + 1) + β k • method.d k :=
        h_direction_eq k hk_lt_n hk_nonzero hk1_nonzero
      have hdir_grad :
          dotProduct (method.d (k + 1)) (method.g (k + 1)) =
            -dotProduct (method.g (k + 1)) (method.g (k + 1)) := by
        -- The current recurrence and the previous line-search orthogonality kill the carry term.
        calc
          dotProduct (method.d (k + 1)) (method.g (k + 1)) =
              dotProduct (-method.g (k + 1) + β k • method.d k) (method.g (k + 1)) := by
                rw [hdir_eq]
          _ = -dotProduct (method.g (k + 1)) (method.g (k + 1)) +
                β k * dotProduct (method.d k) (method.g (k + 1)) := by
                simp
          _ = -dotProduct (method.g (k + 1)) (method.g (k + 1)) := by
                simp [hPrevGradDir k le_rfl, dotProduct_comm]
      have hdir_pair_prev :
          ∀ j : ℕ, j < k + 1 →
            dotProduct (method.d (k + 1)) (method.g j) =
              -dotProduct (method.g (k + 1)) (method.g (k + 1)) := by
        intro j hj
        have hj_le : j ≤ k := Nat.le_of_lt_succ hj
        have hPrevPair :
            dotProduct (method.d k) (method.g j) =
              dotProduct (method.d k) (method.g k) := by
          rcases Nat.eq_or_lt_of_le hj_le with rfl | hj_lt
          · rfl
          · rw [hPrevDirPrevGrad j hj_lt, hPrevDirGrad]
        have hbetaMul :
            β k * dotProduct (method.d k) (method.g k) =
              -dotProduct (method.g (k + 1)) (method.g (k + 1)) :=
          h_beta_mul k hk_lt_n hk_nonzero hk1_nonzero (hPrevGradGrad k le_rfl) hPrevDirGrad
        -- Every previous gradient pairs with `d_(k+1)` by the same carried value.
        calc
          dotProduct (method.d (k + 1)) (method.g j) =
              dotProduct (-method.g (k + 1) + β k • method.d k) (method.g j) := by
                rw [hdir_eq]
          _ = -dotProduct (method.g (k + 1)) (method.g j) +
                β k * dotProduct (method.d k) (method.g j) := by
                simp
          _ = β k * dotProduct (method.d k) (method.g k) := by
                rw [hPrevGradGrad j hj_le, hPrevPair]
                ring
          _ = -dotProduct (method.g (k + 1)) (method.g (k + 1)) := hbetaMul
      have hconj :
          ∀ j : ℕ, j < k + 1 →
            dotProduct (method.d (k + 1)) (G.mulVec (method.d j)) = 0 := by
        intro j hj
        have hj_lt_n : j < n := Nat.lt_trans hj hk
        have hj_nonzero : method.g j ≠ 0 := h_nonstationary j hj_lt_n
        have hstep_j :=
          run_quadratic_gradient_step_eq hG (k := j) hj_nonzero
            (h_iterate_eq j hj_lt_n hj_nonzero)
        have hdescent_j :
            IsDescentDirectionAt
              (quadraticObjective G b c) (method.x j) (method.d j) := by
          have hInv_j := ih j hj hj_lt_n
          have hdir_grad_j := hInv_j.2.2.1
          have hdot :
              dotProduct (method.g j) (method.d j) =
                -dotProduct (method.g j) (method.g j) := by
            simpa [dotProduct_comm] using hdir_grad_j
          have hinner :
              inner ℝ (gradient (quadraticObjective G b c) (method.x j)) (method.d j) =
                -dotProduct (method.g j) (method.g j) := by
            simpa [method.gradient_eq j, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
              using hdot
          have hgg_pos : 0 < dotProduct (method.g j) (method.g j) := by
            exact dotProduct_self_pos_of_ne_zero hj_nonzero
          have hneg :
              inner ℝ (gradient (quadraticObjective G b c) (method.x j)) (method.d j) < 0 := by
            rw [hinner]
            linarith
          simpa [IsDescentDirectionAt, method.gradient_eq j,
            EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hneg
        have hAlphaPos_j : 0 < method.α j :=
          exactLineSearchStep_pos_of_descent
            (quadraticObjective G b c) (method.x j) (method.d j) (method.α j)
            hdescent_j (h_exactLineSearch j hj_lt_n hj_nonzero)
        have hstep_pair :
            dotProduct (method.d (k + 1)) (method.g (j + 1)) =
              dotProduct (method.d (k + 1)) (method.g j) := by
          rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with hEq | hj_lt_k
          · rw [hEq, hdir_grad]
            simpa [hEq] using (hdir_pair_prev j hj).symm
          · rw [hdir_pair_prev (j + 1) (Nat.succ_lt_succ hj_lt_k), hdir_pair_prev j hj]
        have hrewrite :
            dotProduct (method.d (k + 1)) (method.g (j + 1)) =
              dotProduct (method.d (k + 1)) (method.g j) +
                method.α j * dotProduct (method.d (k + 1)) (G.mulVec (method.d j)) := by
          have hrewrite' := congrArg (fun v : Point ↦ dotProduct (method.d (k + 1)) v) hstep_j
          simpa [dotProduct_add, dotProduct_smul] using hrewrite'
        have hmul_zero :
            method.α j * dotProduct (method.d (k + 1)) (G.mulVec (method.d j)) = 0 := by
          linarith [hrewrite, hstep_pair]
        exact (mul_eq_zero.mp hmul_zero).resolve_left hAlphaPos_j.ne'
      have hdescent :
          IsDescentDirectionAt
            (quadraticObjective G b c) (method.x (k + 1)) (method.d (k + 1)) := by
        have hdot :
            dotProduct (method.g (k + 1)) (method.d (k + 1)) =
              -dotProduct (method.g (k + 1)) (method.g (k + 1)) := by
          simpa [dotProduct_comm] using hdir_grad
        have hinner :
            inner ℝ (gradient (quadraticObjective G b c) (method.x (k + 1))) (method.d (k + 1)) =
              -dotProduct (method.g (k + 1)) (method.g (k + 1)) := by
          simpa [method.gradient_eq (k + 1), EuclideanSpace.inner_eq_star_dotProduct,
            dotProduct_comm] using hdot
        have hgg_pos : 0 < dotProduct (method.g (k + 1)) (method.g (k + 1)) := by
          exact dotProduct_self_pos_of_ne_zero hk1_nonzero
        have hneg :
            inner ℝ
              (gradient (quadraticObjective G b c) (method.x (k + 1)))
              (method.d (k + 1)) < 0 := by
          rw [hinner]
          linarith
        simpa [IsDescentDirectionAt, method.gradient_eq (k + 1),
          EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hneg
      have hAlphaPos : 0 < method.α (k + 1) :=
        exactLineSearchStep_pos_of_descent
          (quadraticObjective G b c) (method.x (k + 1)) (method.d (k + 1)) (method.α (k + 1))
          hdescent (h_exactLineSearch (k + 1) hk hk1_nonzero)
      have hUpdate : method.x (k + 2) = method.x (k + 1) + method.α (k + 1) • method.d (k + 1) :=
        h_iterate_eq (k + 1) hk hk1_nonzero
      have hgrad_dir :
          dotProduct (method.g (k + 2)) (method.d (k + 1)) = 0 := by
        -- The next accepted step is again stationary in the accepted search direction.
        have hstationary :
            inner ℝ
              (gradient (quadraticObjective G b c)
                (method.x (k + 1) + method.α (k + 1) • method.d (k + 1)))
              (method.d (k + 1)) = 0 :=
          exactLineSearch_stationary_inner_eq_zero_of_pos
            (quadraticObjective G b c) (method.x (k + 1)) (method.d (k + 1)) (method.α (k + 1))
            hAlphaPos (h_exactLineSearch (k + 1) hk hk1_nonzero)
            (fun x ↦ by
              simpa [gradient_quadraticObjective G b c (posDef_isSymm hG) x] using
                hasGradientAt_quadraticObjective G b c (posDef_isSymm hG) x)
        have hgrad :
            gradient (quadraticObjective G b c)
                (method.x (k + 1) + method.α (k + 1) • method.d (k + 1)) =
              method.g (k + 2) := by
          calc
            gradient (quadraticObjective G b c)
                (method.x (k + 1) + method.α (k + 1) • method.d (k + 1))
                = gradient (quadraticObjective G b c) (method.x (k + 2)) := by rw [← hUpdate]
            _ = method.g (k + 2) := method.gradient_eq (k + 2)
        simpa [hgrad, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hstationary
      have hstep_next :
          method.g (k + 2) =
            method.g (k + 1) + method.α (k + 1) • Matrix.toEuclideanLin G (method.d (k + 1)) :=
        run_quadratic_gradient_step_eq hG (k := k + 1) hk1_nonzero
          (h_iterate_eq (k + 1) hk hk1_nonzero)
      have hgrad_dir_all :
          ∀ j : ℕ, j ≤ k + 1 → dotProduct (method.g (k + 2)) (method.d j) = 0 := by
        intro j hj
        rcases Nat.eq_or_lt_of_le hj with rfl | hj_lt
        · simpa using hgrad_dir
        · -- The gradient update preserves orthogonality to earlier directions by current conjugacy.
          calc
            dotProduct (method.g (k + 2)) (method.d j) =
                dotProduct
                  (method.g (k + 1) + method.α (k + 1) • Matrix.toEuclideanLin G (method.d (k + 1)))
                  (method.d j) := by
                    rw [hstep_next]
            _ = dotProduct (method.g (k + 1)) (method.d j) +
                  method.α (k + 1) *
                    dotProduct (method.d j) (G.mulVec (method.d (k + 1))) := by
                    simp [dotProduct_add, dotProduct_smul, dotProduct_comm]
            _ = dotProduct (method.g (k + 1)) (method.d j) +
                  method.α (k + 1) *
                    dotProduct (method.d (k + 1)) (G.mulVec (method.d j)) := by
                    rw [dotProduct_mulVec_comm_of_posDef hG (method.d j) (method.d (k + 1))]
            _ = 0 := by simp [hPrevGradDir j (Nat.le_of_lt_succ hj_lt), hconj j hj_lt]
      have hgrad_grad_all :
          ∀ j : ℕ, j ≤ k + 1 → dotProduct (method.g (k + 2)) (method.g j) = 0 := by
        intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hj_pos
        · -- The zero-th direction is `-g₀`, so the first gradient orthogonality gives
          -- `g_(k+2) ⟂ g₀`.
          simpa [h_direction_zero, dotProduct_comm] using hgrad_dir_all 0 (Nat.zero_le _)
        · have hdir_j :
            method.d j = -method.g j + β (j - 1) • method.d (j - 1) := by
            have hj_lt_n : j < n := Nat.lt_of_le_of_lt hj hk
            have hj_prev_lt_n : j - 1 < n := lt_of_le_of_lt (Nat.sub_le _ _) hj_lt_n
            have hj_prev_nonzero : method.g (j - 1) ≠ 0 := h_nonstationary (j - 1) hj_prev_lt_n
            have hj_nonzero : method.g j ≠ 0 := h_nonstationary j hj_lt_n
            simpa [Nat.sub_add_cancel hj_pos] using
              h_direction_eq (j - 1) hj_prev_lt_n hj_prev_nonzero
                (by simpa [Nat.sub_add_cancel hj_pos] using hj_nonzero)
          have hprev_dir : dotProduct (method.g (k + 2)) (method.d (j - 1)) = 0 :=
            hgrad_dir_all (j - 1) (le_trans (Nat.sub_le _ _) hj)
          have hthis : dotProduct (method.g (k + 2)) (method.g j) = 0 := by
            have hcalc :
                -dotProduct (method.g (k + 2)) (method.g j) +
                    β (j - 1) * dotProduct (method.g (k + 2)) (method.d (j - 1)) = 0 := by
              simpa [hdir_j, dotProduct_add, dotProduct_smul] using hgrad_dir_all j hj
            have hcalc' : -dotProduct (method.g (k + 2)) (method.g j) = 0 := by
              simpa [hprev_dir] using hcalc
            linarith
          exact hthis
      exact ⟨hgrad_dir_all, hgrad_grad_all, hdir_grad, hdir_pair_prev, hconj⟩

namespace ConjugateGradientRun

/-- A nonlinear conjugate-gradient run is a Dixon run when it starts in the steepest-descent
direction, every nonstationary step is an exact line search with the recorded iterate update,
and each Dixon coefficient and direction update obeys the textbook recurrence whenever two
consecutive stages are nonstationary. This is a `bridge/view` on the Chapter 4 owner
`ConjugateGradientRun`, not a second standalone run owner. -/
structure Dixon {f : Point → ℝ} (method : ConjugateGradientRun Point f) where
  β : ℕ → ℝ
  direction_zero : method.d 0 = -method.g 0
  exactLineSearch (k : ℕ) (hk : k < n) :
    method.g k ≠ 0 →
      IsExactLineSearchStepOnNonnegativeRay f (method.x k) (method.d k) (method.α k)
  iterate_eq (k : ℕ) (hk : k < n) :
    method.g k ≠ 0 →
      method.x (k + 1) = method.x k + method.α k • method.d k
  beta_eq (k : ℕ) (hk : k < n) :
    method.g k ≠ 0 → method.g (k + 1) ≠ 0 →
      β k = dixonBeta (method.g k) (method.g (k + 1)) (method.d k)
  direction_eq (k : ℕ) (hk : k < n) :
    method.g k ≠ 0 → method.g (k + 1) ≠ 0 →
      method.d (k + 1) = -method.g (k + 1) + β k • method.d k

end ConjugateGradientRun

namespace PolakRibierePolyakConjugateGradientMethod

/-- Helper for Chapter04 Exercise 4.4: the PRP coefficient satisfies the scalar identity
`β_k * ⟪d_k, g_k⟫ = -‖g_(k + 1)‖²` once exact line search has made `g_(k + 1)` orthogonal to
`g_k`. -/
private theorem prp_beta_mul
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Point} {c : ℝ}
    (method :
      PolakRibierePolyakConjugateGradientMethod n (quadraticObjective G b c))
    {k : ℕ} (hk : method.g k ≠ 0) (hkNext : method.g (k + 1) ≠ 0)
    (horth : dotProduct (method.g (k + 1)) (method.g k) = 0)
    (hdirgrad :
      dotProduct (method.d k) (method.g k) = -dotProduct (method.g k) (method.g k)) :
    method.β k * dotProduct (method.d k) (method.g k) =
      -dotProduct (method.g (k + 1)) (method.g (k + 1)) := by
  have hgg_ne : dotProduct (method.g k) (method.g k) ≠ 0 := by
    intro hzero
    exact hk (by simpa using dotProduct_self_eq_zero.mp hzero)
  have hbeta :
      method.β k =
        (method.g (k + 1)).ofLp ⬝ᵥ (method.g (k + 1) - method.g k).ofLp /
          ((method.g k).ofLp ⬝ᵥ (method.g k).ofLp) := by
    -- Rewrite the PRP coefficient into dot-product form on `ℝ^n`.
    simpa only [polakRibierePolyakBeta, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct_comm] using method.beta_eq k hk hkNext
  -- Orthogonality collapses the PRP numerator to `‖g_(k + 1)‖²`.
  calc
    method.β k * dotProduct (method.d k) (method.g k) =
        (dotProduct (method.g (k + 1)) (method.g (k + 1) - method.g k) /
            dotProduct (method.g k) (method.g k)) *
          dotProduct (method.d k) (method.g k) := by
            rw [hbeta]
            simp [WithLp.ofLp_sub]
    _ = (dotProduct (method.g (k + 1)) (method.g (k + 1)) /
          dotProduct (method.g k) (method.g k)) *
          dotProduct (method.d k) (method.g k) := by
            rw [dotProduct_sub, horth, sub_zero]
    _ = -dotProduct (method.g (k + 1)) (method.g (k + 1)) := by
            rw [hdirgrad]
            field_simp [hgg_ne]

/-- Helper for Chapter04 Exercise 4.4: on a quadratic objective, the PRP coefficient agrees with
the Dixon coefficient after the shared exact-line-search orthogonality invariants are unfolded. -/
theorem beta_eq_dixonBeta
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {b : Point} {c : ℝ}
    (method :
      PolakRibierePolyakConjugateGradientMethod n (quadraticObjective G b c))
    (h_nonstationary : ∀ t : ℕ, t < n → method.g t ≠ 0)
    {k : ℕ} (hk : k < n) (hkNext_nonzero : method.g (k + 1) ≠ 0) :
    method.β k = dixonBeta (method.g k) (method.g (k + 1)) (method.d k) := by
  have hk_nonzero : method.g k ≠ 0 := h_nonstationary k hk
  have hInv :=
    recurrence_step_invariants
      (G := G) (b := b) (c := c) (method := method.toConjugateGradientRun) (β := method.β)
      hG
      method.direction_zero (fun t _ ht ↦ method.exactLineSearch t ht)
      (fun t _ ht ↦ method.iterate_eq t ht)
      (fun t _ ht htNext horth hdirgrad ↦ prp_beta_mul method ht htNext horth hdirgrad)
      (fun t ht ht0 ht1 ↦ method.direction_eq t ht0 ht1) h_nonstationary (k := k) hk
  rcases hInv with ⟨_, hgradGrad, hdirgrad, _, _⟩
  have horth : dotProduct (method.g (k + 1)) (method.g k) = 0 := hgradGrad k le_rfl
  have hdenom_ne : dotProduct (method.d k) (method.g k) ≠ 0 := by
    rw [hdirgrad]
    exact neg_ne_zero.mpr fun hzero ↦ hk_nonzero (by simpa using dotProduct_self_eq_zero.mp hzero)
  -- The scalar identity above is exactly the Dixon quotient after rewriting the denominator.
  have hbeta :
      method.β k =
        -dotProduct (method.g (k + 1)) (method.g (k + 1)) /
          dotProduct (method.d k) (method.g k) :=
    (eq_div_iff hdenom_ne).2 <| prp_beta_mul method hk_nonzero hkNext_nonzero horth hdirgrad
  simpa only [dixonBeta, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    using hbeta

/-- Helper for Chapter04 Exercise 4.4: once the coefficients agree, the PRP direction recurrence
is literally the Dixon recurrence on the same underlying run. -/
theorem direction_eq_dixon
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {b : Point} {c : ℝ}
    (method :
      PolakRibierePolyakConjugateGradientMethod n (quadraticObjective G b c))
    (h_nonstationary : ∀ t : ℕ, t < n → method.g t ≠ 0)
    {k : ℕ} (hk : k < n) (hkNext_nonzero : method.g (k + 1) ≠ 0) :
    method.d (k + 1) =
      -method.g (k + 1) + dixonBeta (method.g k) (method.g (k + 1)) (method.d k) • method.d k := by
  -- Route correction: the `toDixon` structure field must reference a named theorem, not an
  -- inline proof term inside the `def`.
  have hk_nonzero : method.g k ≠ 0 := h_nonstationary k hk
  rw [method.direction_eq k hk_nonzero hkNext_nonzero,
    method.beta_eq_dixonBeta hG h_nonstationary hk hkNext_nonzero]

/-- On a quadratic objective, the PRP update formulas recover the Dixon run bridge on the same
underlying nonlinear conjugate-gradient owner. This is the `bridge/view` from the source-facing
PRP owner to the exercise's generic Dixon owner. -/
def toDixon (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point) (c : ℝ)
    (method :
      PolakRibierePolyakConjugateGradientMethod n
        (quadraticObjective G b c))
    (h_nonstationary : ∀ t : ℕ, t < n → method.g t ≠ 0) :
    method.toConjugateGradientRun.Dixon where
  β := method.β
  direction_zero := method.direction_zero
  exactLineSearch k _ := method.exactLineSearch k
  iterate_eq k _ := method.iterate_eq k
  beta_eq k hk _ hkNext_nonzero := by
    simpa using method.beta_eq_dixonBeta hG h_nonstationary (k := k) hk hkNext_nonzero
  direction_eq k hk _ hkNext_nonzero := by
    simpa using method.direction_eq k (h_nonstationary k hk) hkNext_nonzero

end PolakRibierePolyakConjugateGradientMethod

namespace ConjugateGradientRun.Dixon

/-- Chapter04 Exercise 4.4 (2): for a quadratic objective with positive-definite
Hessian `G`, if the first `n` stages of a Dixon-CG run are nonstationary, then
the first `n` search directions form a `G`-conjugate family. -/
theorem quadraticDirections_isConjugateFamily
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {b : Point} {c : ℝ}
    {method : ConjugateGradientRun Point (quadraticObjective G b c)}
    (hDixon : method.Dixon)
    (h_nonstationary : ∀ k : ℕ, k < n → method.g k ≠ 0) :
    G.IsConjugateFamily (fun i : Fin n ↦ method.d i) := by
  have hBetaMul :
      ∀ k : ℕ, k < n → (hk : method.g k ≠ 0) → (hkNext : method.g (k + 1) ≠ 0) →
        dotProduct (method.g (k + 1)) (method.g k) = 0 →
        dotProduct (method.d k) (method.g k) = -dotProduct (method.g k) (method.g k) →
        hDixon.β k * dotProduct (method.d k) (method.g k) =
          -dotProduct (method.g (k + 1)) (method.g (k + 1)) := by
    intro k hk_lt_n hk hkNext _ hdirgrad
    have hdenom_ne : dotProduct (method.d k) (method.g k) ≠ 0 := by
      rw [hdirgrad]
      exact neg_ne_zero.mpr fun hzero ↦ hk (by simpa using dotProduct_self_eq_zero.mp hzero)
    -- The Dixon coefficient identity is already exactly the needed scalar multiplier.
    have hbeta :
        hDixon.β k =
          -dotProduct (method.g (k + 1)) (method.g (k + 1)) /
            dotProduct (method.d k) (method.g k) := by
      simpa only [dixonBeta, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
        dotProduct_comm] using hDixon.beta_eq k hk_lt_n hk hkNext
    exact (eq_div_iff hdenom_ne).mp hbeta
  have hInv (k : ℕ) (hk : k < n) :
      (∀ j : ℕ, j ≤ k → dotProduct (method.g (k + 1)) (method.d j) = 0) ∧
        (∀ j : ℕ, j ≤ k → dotProduct (method.g (k + 1)) (method.g j) = 0) ∧
          dotProduct (method.d k) (method.g k) = -dotProduct (method.g k) (method.g k) ∧
            (∀ j : ℕ, j < k →
              dotProduct (method.d k) (method.g j) = -dotProduct (method.g k) (method.g k)) ∧
              (∀ j : ℕ, j < k → dotProduct (method.d k) (G.mulVec (method.d j)) = 0) :=
    recurrence_step_invariants
      (G := G) (b := b) (c := c) (method := method) (β := hDixon.β) hG
      hDixon.direction_zero hDixon.exactLineSearch hDixon.iterate_eq hBetaMul hDixon.direction_eq
      h_nonstationary (k := k) hk
  rw [Matrix.isConjugateFamily_iff]
  constructor
  · intro i
    have hStep := hInv i.1 i.2
    have hdirgrad := hStep.2.2.1
    -- A nonzero current gradient forces the current direction to be nonzero as well.
    intro hd
    have hzero : dotProduct (method.g i) (method.g i) = 0 := by
      simpa [hd] using hdirgrad
    exact h_nonstationary i.1 i.2 (by simpa using dotProduct_self_eq_zero.mp hzero)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
    · have hStep := hInv j.1 j.2
      have hconj : dotProduct (method.d j) (G.mulVec (method.d i)) = 0 :=
        hStep.2.2.2.2 i.1 hij_lt
      simpa [dotProduct_mulVec_comm_of_posDef hG (method.d i) (method.d j)] using hconj
    · have hStep := hInv i.1 i.2
      simpa using hStep.2.2.2.2 j.1 hij_gt

end ConjugateGradientRun.Dixon

/-- Chapter04 Exercise 4.4 (1): for a quadratic objective with positive-definite
Hessian `G`, if the first `n` stages of a PRP-CG run are nonstationary, then the
first `n` search directions form a `G`-conjugate family. -/
theorem polakRibierePolyakQuadraticDirections_isConjugateFamily
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (b : Point) (c : ℝ)
    (method :
      PolakRibierePolyakConjugateGradientMethod n
        (quadraticObjective G b c))
    (h_nonstationary : ∀ k : ℕ, k < n → method.g k ≠ 0) :
    G.IsConjugateFamily (fun i : Fin n ↦ method.d i) := by
  simpa using
    (method.toDixon G hG b c h_nonstationary).quadraticDirections_isConjugateFamily hG
      h_nonstationary

end
