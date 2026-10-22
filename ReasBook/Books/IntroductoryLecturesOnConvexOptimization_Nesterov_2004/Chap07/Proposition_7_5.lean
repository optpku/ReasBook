/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

variable {p n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 7.5 lies in the chapter's Frobenius-Gram / dense arithmetic-cost domain.

Sampled owner-style declarations:
- `Matrix.gram` in mathlib, the canonical Frobenius Gram-matrix owner for a family of
  coefficient matrices;
- `matrix_gram_apply_eq_entrywise_sum` in `Chap07/Definition_7_21`, the Chapter 7 bridge from
  that owner to the textbook Frobenius double sum;
- `linearMatrixGramOperator_toMatrixOrthonormal` in `Chap07/Definition_7_21`, the bridge from the
  source-facing operator `G = L†L` to its Gram matrix;
- `gramMatrix` in `Chap07/Proposition_7_24`, another use of the same canonical Gram owner.

Best owner abstraction:
- source-facing: the preliminary arithmetic-work bound for forming the Frobenius Gram matrix and
  inverting it;
- core/canonical: `Matrix.gram ℝ` on matrix-entry coordinates;
- bridge/view: `matrix_gram_apply_eq_entrywise_sum`.

Primitive data:
- `n`, `p : ℕ`.

Derived API:
- the canonical Frobenius Gram owner `Matrix.gram ℝ`;
- the parameter-only arithmetic-work expression
  `frobeniusGramPreliminaryArithmeticWorkBound n p`;
- its explicit expansion and regime-specific quadratic bound.

Source/core/bridge triage:
- source-facing: the arithmetic complexity statement of Proposition 7.5;
- core/canonical: `Matrix.gram ℝ`;
- bridge/view: the entrywise identity `matrix_gram_apply_eq_entrywise_sum`.

The previous file kept local raw-matrix inner-product scaffolding just to mention the Gram owner.
This refinement deletes that scaffolding and reuses the Chapter 7 Frobenius Gram owner directly,
leaving this file to own only the new arithmetic-work model and its asymptotic consequence.
-/

section

variable (p n)

/- Proposition 7.5 uses the canonical Frobenius Gram-matrix owner. -/
set_option linter.hashCommand false in
#check (Matrix.gram ℝ : (Fin p → Mₙ) → Matrix (Fin p) (Fin p) ℝ)

end

/-- A dimension-only arithmetic upper bound for the preliminary computation that first forms the
Frobenius Gram matrix of a family of coefficient matrices and then computes its inverse. -/
def frobeniusGramPreliminaryArithmeticWorkBound (n p : ℕ) : ℕ :=
  p ^ 2 * n ^ 2 + p ^ 3

/-- Expanding `frobeniusGramPreliminaryArithmeticWorkBound n p` recovers the sum of the
Gram-matrix formation cost `p^2 n^2` and the matrix-inversion cost `p^3`. -/
-- Proof sketch: unfold `frobeniusGramPreliminaryArithmeticWorkBound`.
theorem frobeniusGramPreliminaryArithmeticWorkBound_eq
    (n p : ℕ) :
    frobeniusGramPreliminaryArithmeticWorkBound n p = p ^ 2 * n ^ 2 + p ^ 3 :=
  rfl

/-- Helper for Proposition 7.5: the admissible regime `p < n (n + 1) / 2` forces the
dimension count `p` to lie below the ambient square dimension `n^2`. -/
lemma lt_triangular_half_implies_le_square
    {n p : ℕ} (hpn : p < n * (n + 1) / 2) :
    p ≤ n ^ 2 := by
  -- The triangular-number hypothesis rules out the degenerate case `n = 0`.
  have hn : 1 ≤ n := by
    by_cases h0 : n = 0
    · subst h0
      simp at hpn
    · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
  -- Replace `n + 1` by the larger factor `2n`, then cancel the division by `2`.
  calc
    p ≤ n * (n + 1) / 2 := Nat.le_of_lt hpn
    _ ≤ n * (2 * n) / 2 := by
      have hn_two : n + 1 ≤ 2 * n := by
        nlinarith [hn]
      gcongr
    _ = n ^ 2 := by
      simpa [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        (Nat.mul_div_right (n * n) (show 0 < 2 by decide))

/-- Helper for Proposition 7.5: once `p ≤ n^2`, the cubic inversion cost `p^3` is absorbed by
the quadratic Gram-formation scale `p^2 n^2`. -/
lemma cube_term_le_quadratic_term_of_le_square
    {n p : ℕ} (hp : p ≤ n ^ 2) :
    p ^ 3 ≤ p ^ 2 * n ^ 2 := by
  -- Cast to `ℚ` so the absorption step becomes a polynomial inequality.
  have hpQ : (p : ℚ) ≤ n ^ 2 := by
    exact_mod_cast hp
  have hp_sq_nonnegQ : 0 ≤ (p : ℚ) ^ 2 := by
    positivity
  exact_mod_cast (show (p : ℚ) ^ 3 ≤ p ^ 2 * n ^ 2 by
    nlinarith [hpQ, hp_sq_nonnegQ])

-- Proof sketch: use `hpn` to deduce `p < n^2`, hence `p^3 ≤ p^2 n^2`, and then absorb the
-- inversion term into the explicit preliminary-work expression
-- `p^2 n^2 + p^3`.
/-- The preliminary arithmetic-work model is bounded by `2 p^2 n^2` on the admissible regime
`p < n (n + 1) / 2`. -/
theorem frobeniusGramPreliminaryArithmeticWorkBound_le_two_mul
    {n p : ℕ} (hpn : p < n * (n + 1) / 2) :
    frobeniusGramPreliminaryArithmeticWorkBound n p ≤ 2 * (p ^ 2 * n ^ 2) := by
  -- Expand the cost model to isolate the quadratic and cubic contributions.
  rw [frobeniusGramPreliminaryArithmeticWorkBound_eq]
  -- The admissible regime bounds `p` by `n^2`, so the cubic term can be absorbed.
  have hp_sq : p ≤ n ^ 2 := lt_triangular_half_implies_le_square hpn
  have hcubic : p ^ 3 ≤ p ^ 2 * n ^ 2 := cube_term_le_quadratic_term_of_le_square hp_sq
  -- After replacing `p^3` by the same quadratic scale, only a factor `2` remains.
  calc
    p ^ 2 * n ^ 2 + p ^ 3 ≤ p ^ 2 * n ^ 2 + p ^ 2 * n ^ 2 := by
      simpa [Nat.add_comm] using add_le_add_left hcubic (p ^ 2 * n ^ 2)
    _ = 2 * (p ^ 2 * n ^ 2) := by rw [two_mul]

-- Proof sketch: take the constant witness `C = 2` and apply the explicit upper bound above.
/-- Proposition 7.5 [Chapter7_2.json:38]: if `A₁, …, Aₚ ∈ ℝ^(n × n)` and `G` is the Frobenius
Gram matrix with entries `G^(i,j) = ⟪Aᵢ, Aⱼ⟫_F`, then under the size condition
`p < n(n + 1) / 2` the preliminary computation modeled by
`frobeniusGramPreliminaryArithmeticWorkBound n p` has total arithmetic work bounded by a constant
multiple of `p^2 n^2`, i.e. of order `O(p^2 n^2)`. -/
theorem frobeniusGramPreliminaryArithmeticWork_has_quadratic_bound
    {n p : ℕ} (hpn : p < n * (n + 1) / 2) :
    ∃ C : ℕ,
      frobeniusGramPreliminaryArithmeticWorkBound n p ≤ C * (p ^ 2 * n ^ 2) := by
  -- Package the explicit quadratic bound with the witness constant `C = 2`.
  refine ⟨2, ?_⟩
  exact frobeniusGramPreliminaryArithmeticWorkBound_le_two_mul hpn

end
