/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_9_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped CubicRegularizedDiagonalInvariants

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.9 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Definition_4_1_14`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedDiagonalMinimum`, `cubicRegularizedMinimalDiagonalIndices`, and
  `cubicRegularizedMinimalDiagonalGradientSquare` in `Definition_4_1_15`, the diagonal owners of
  `H_min`, `I*`, and `G²`;
* `quadraticObjective` in `Chap01/Definition_1_9_1` and
  `UnconstrainedQuadraticMinimizationProblem.minimizer_unique` in
  `Chap01/Proposition_1_9_11`, the core owner / uniqueness API for the shifted quadratic
  subproblem.

Best owner abstraction:
* source-facing: the diagonal nondegenerate `G² > 0` closed-form dual formula and the resolvent
  minimizer statements from the source;
* core/canonical: `cubicRegularizedQuadraticDualFunction`, `cubicRegularizedQuadraticDualDomain`,
  `quadraticObjective`, and `IsMinOn`;
* bridge/view: the specialization `H = Matrix.diagonal Hdiag` together with the diagonal
  invariants `H_min`, `I*`, and `G²`.

Primitive data:
* the gradient `g`, diagonal data `Hdiag`, cubic parameter `M`, and the diagonal matrix
  `H = Matrix.diagonal Hdiag`;
* the canonical diagonal invariants `H_min`, `I*`, and `G²`.

Derived API:
* the dual-domain identity for `dom ψ`;
* the closed formula for `ψ(λ)` on that domain;
* the owner-level minimizer theorem for the shifted diagonal quadratic;
* the uniqueness corollary identifying every minimizer with the same resolvent point.

This file therefore keeps the source-facing Proposition 4.1.9 statements, but states them
directly in terms of the chapter owners `ψ` and `dom ψ` rather than forcing the long raw owner
names on the theorem surface. It also exposes the shifted-quadratic minimizer statement here as
the canonical upstream owner, with uniqueness kept only as the thin corollary attached to that
owner. -/

section

variable (g : EuclideanSpace ℝ (Fin n)) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "Irest" => Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag]

/-- Helper for Proposition 4.1.9: the shifted diagonal matrix `H + λ I`. -/
abbrev shiftedDiagonalMatrix (lam : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Helper for Proposition 4.1.9: the shifted quadratic objective `q_λ`. -/
abbrev shiftedQuadraticObjective (lam : ℝ) : E → ℝ :=
  quadraticObjective 0 g (shiftedDiagonalMatrix (Hdiag := Hdiag) lam)

/-- Helper for Proposition 4.1.9: the canonical diagonal resolvent point `-(H + λ I)⁻¹ g`. -/
abbrev diagonalResolventPoint (lam : ℝ) : E :=
  (-Matrix.toEuclideanLin ((shiftedDiagonalMatrix (Hdiag := Hdiag) lam)⁻¹) g : E)

local notation "Ashift" => shiftedDiagonalMatrix (Hdiag := Hdiag)
local notation "qShift" => shiftedQuadraticObjective (g := g) (Hdiag := Hdiag)
local notation "ψ" => cubicRegularizedQuadraticDualFunction g H M
local notation "dom " "ψ" => cubicRegularizedQuadraticDualDomain g H M
local notation "resolventPoint" => diagonalResolventPoint (g := g) (Hdiag := Hdiag)

/-- Helper for Proposition 4.1.9: shifting the diagonal matrix by `λ I` is still diagonal, with
entries `H_i + λ`. -/
lemma diagonal_shift_eq_diagonal_add_scalar
    (lam : ℝ) :
    Ashift lam = Matrix.diagonal (fun i ↦ Hdiag i + lam) := by
  -- Compare entries directly: diagonal entries gain `λ`, off-diagonal entries stay zero.
  ext i j
  by_cases hij : i = j
  · subst hij
    dsimp [shiftedDiagonalMatrix]
    simp [Matrix.diagonal]
  · dsimp [shiftedDiagonalMatrix]
    simp [Matrix.diagonal, hij]

/-- Helper for Proposition 4.1.9: every diagonal entry lies above the minimum diagonal value
`H_min`. -/
lemma diagonalMinimum_le_entry
    (i : Fin n) :
    H_min[Hdiag] ≤ Hdiag i := by
  -- `H_min` was defined as the infimum of the finite range of `Hdiag`.
  exact csInf_le (Set.Finite.bddBelow (Set.finite_range Hdiag))
    (show Hdiag i ∈ Set.range Hdiag from ⟨i, rfl⟩)

/-- Helper for Proposition 4.1.9: if `G² > 0`, then some active index carries a nonzero
gradient coordinate. -/
lemma active_index_exists_of_activeGradientSquare_pos
    (hGpos : 0 < G²[g;Hdiag]) :
    ∃ i, i ∈ I*[Hdiag] ∧ g i ≠ 0 := by
  -- A positive finite sum of squares must contain a nonzero summand.
  have hsum_ne : G²[g;Hdiag] ≠ 0 := by
    linarith
  rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_ne with ⟨i, hi, hineq⟩
  refine ⟨i, hi, ?_⟩
  intro hgi
  simp [hgi] at hineq

/-- Helper for Proposition 4.1.9: restricting `q_λ` to a coordinate line gives the displayed
one-variable quadratic. -/
lemma quadraticObjective_single_eq
    (lam t : ℝ) (k : Fin n) :
    qShift lam (EuclideanSpace.single k t) =
      g k * t + (1 / 2 : ℝ) * (Hdiag k + lam) * t ^ (2 : ℕ) := by
  -- Rewrite the shifted quadratic into its coordinate `dotProduct` form first.
  change quadraticObjective 0 g (Ashift lam) (EuclideanSpace.single k t) =
    g k * t + (1 / 2 : ℝ) * (Hdiag k + lam) * t ^ (2 : ℕ)
  rw [quadraticObjective_zero_eq_dotProduct, diagonal_shift_eq_diagonal_add_scalar]
  have hlin : dotProduct g (EuclideanSpace.single k t) = g k * t := by
    -- The linear term only sees the single nonzero coordinate.
    rw [dotProduct, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [EuclideanSpace.single, hj]
    · simp
  have hquad :
      dotProduct
          ((Matrix.diagonal fun i ↦ Hdiag i + lam).mulVec (EuclideanSpace.single k t))
          (EuclideanSpace.single k t) =
        (Hdiag k + lam) * t ^ (2 : ℕ) := by
    -- The diagonal quadratic term also collapses to the same coordinate.
    simp [dotProduct, Matrix.mulVec, pow_two]
    ring
  rw [hlin, hquad]
  ring

/-- Helper for Proposition 4.1.9: a one-variable quadratic with negative leading coefficient is
unbounded below. -/
lemma not_bddBelow_negative_quadratic_line
    (a b : ℝ) (ha : a < 0) :
    ¬BddBelow (Set.range fun t : ℝ ↦ (1 / 2 : ℝ) * a * t ^ (2 : ℕ) + b * t) := by
  -- Choose a large positive `t` so that the negative quadratic term dominates the linear term.
  intro hbb
  rcases hbb with ⟨m, hm⟩
  let t : ℝ := 2 * (|b| + |m| + 1) / (-a) + 1
  have hta : 0 < -a := by
    linarith
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_one : 1 ≤ t := by
    dsimp [t]
    have : 0 ≤ 2 * (|b| + |m| + 1) / (-a) := by
      positivity
    linarith
  have hdom : |b| + |m| + 1 < (-a / 2) * t := by
    dsimp [t]
    field_simp [ha.ne]
    nlinarith [abs_nonneg b, abs_nonneg m]
  have hb : b * t ≤ |b| * t := by
    have habs : |b * t| = |b| * |t| := by
      rw [abs_mul]
    rw [abs_of_pos ht_pos] at habs
    have hbt : b * t ≤ |b * t| := le_abs_self _
    nlinarith
  have hm' : -(|m| + 1) * t < m := by
    have hnonneg : 0 ≤ |m| + 1 := by
      positivity
    have h1 : -(|m| + 1) * t ≤ -(|m| + 1) := by
      nlinarith [ht_one]
    have h2 : -(|m| + 1) < -|m| := by
      nlinarith
    have h3 : -|m| ≤ m := by
      simpa using neg_abs_le m
    linarith
  have hvalue :
      (1 / 2 : ℝ) * a * t ^ (2 : ℕ) + b * t < m := by
    have hmain :
        (1 / 2 : ℝ) * a * t ^ (2 : ℕ) + |b| * t < -(|m| + 1) * t := by
      nlinarith [hdom, ht_pos]
    linarith
  have hq := hm ⟨t, rfl⟩
  linarith

/-- Helper for Proposition 4.1.9: a nonzero linear function on `ℝ` is unbounded below. -/
lemma not_bddBelow_nonzero_linear_line
    (b : ℝ) (hb : b ≠ 0) :
    ¬BddBelow (Set.range fun t : ℝ ↦ b * t) := by
  -- Evaluate the line at `t = -( |m| + 1 ) / b` to force the value below any lower bound `m`.
  intro hbb
  rcases hbb with ⟨m, hm⟩
  let t : ℝ := -(|m| + 1) / b
  have hvalue : b * t < m := by
    dsimp [t]
    have h1 : b * (-(|m| + 1) / b) = -(|m| + 1) := by
      field_simp [hb]
    rw [h1]
    have h2 : -(|m| + 1) < -|m| := by
      nlinarith
    have h3 : -|m| ≤ m := by
      simpa using neg_abs_le m
    linarith
  have hq := hm ⟨t, rfl⟩
  linarith

/-- Helper for Proposition 4.1.9: the diagonal resolvent point has coordinates
`-g_i / (H_i + λ)` on the interior domain `λ > -H_min`. -/
lemma diagonalResolventPoint_apply
    (lam : ℝ) (hlam : -H_min[Hdiag] < lam) (i : Fin n) :
    resolventPoint lam i = -g i / (Hdiag i + lam) := by
  -- Interior multipliers make every shifted diagonal entry invertible.
  have hpos : 0 < Hdiag i + lam := by
    have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
      diagonalMinimum_le_entry (Hdiag := Hdiag) i
    linarith
  have hne : Hdiag i + lam ≠ 0 := ne_of_gt hpos
  -- Expand the diagonal inverse and evaluate the diagonal matrix-vector product coordinatewise.
  rw [diagonalResolventPoint, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  change (-(((Ashift lam)⁻¹).mulVec g) i) = -g i / (Hdiag i + lam)
  rw [diagonal_shift_eq_diagonal_add_scalar (Hdiag := Hdiag) lam, Matrix.inv_diagonal]
  rw [Matrix.mulVec_diagonal]
  have hunit : IsUnit (fun j : Fin n ↦ Hdiag j + lam) := by
    rw [Pi.isUnit_iff]
    intro j
    have hposj : 0 < Hdiag j + lam := by
      have hmin_le : H_min[Hdiag] ≤ Hdiag j :=
        diagonalMinimum_le_entry (Hdiag := Hdiag) j
      linarith
    exact isUnit_iff_ne_zero.mpr (ne_of_gt hposj)
  have hinv : Ring.inverse (fun j ↦ Hdiag j + lam) i = (Hdiag i + lam)⁻¹ := by
    calc
      Ring.inverse (fun j : Fin n ↦ Hdiag j + lam) i
          = (((hunit.unit⁻¹ : (Fin n → ℝ)ˣ) : Fin n → ℝ) i) := by
              simpa using congrArg (fun f : Fin n → ℝ ↦ f i) (Ring.inverse_of_isUnit hunit)
      _ = (((hunit.apply i).unit⁻¹ : ℝˣ) : ℝ) := by
            exact IsUnit.val_inv_apply (x := fun j : Fin n ↦ Hdiag j + lam) hunit i
      _ = (Hdiag i + lam)⁻¹ := by
            rw [← Ring.inverse_unit ((hunit.apply i).unit), Ring.inverse_eq_inv,
              IsUnit.unit_spec]
  rw [hinv, div_eq_mul_inv, mul_comm, neg_mul]

/-- Helper for Proposition 4.1.9: applying the shifted diagonal matrix to the resolvent point
recovers `-g`. -/
lemma shiftedDiagonal_mulVec_resolventPoint
    (lam : ℝ) (hlam : -H_min[Hdiag] < lam) :
    (Ashift lam).mulVec (resolventPoint lam) = -g := by
  -- After the coordinate formula for the resolvent, every diagonal entry cancels directly.
  ext i
  have hpos : 0 < Hdiag i + lam := by
    have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
      diagonalMinimum_le_entry (Hdiag := Hdiag) i
    linarith
  have hne : Hdiag i + lam ≠ 0 := ne_of_gt hpos
  rw [diagonal_shift_eq_diagonal_add_scalar (Hdiag := Hdiag) lam, Matrix.mulVec_diagonal]
  change (Hdiag i + lam) * resolventPoint lam i = -g i
  rw [diagonalResolventPoint_apply (g := g) (Hdiag := Hdiag) lam hlam i]
  field_simp [hne]

/-- Helper for Proposition 4.1.9: the value of `q_λ` at the diagonal resolvent is the full
diagonal reciprocal sum. -/
lemma quadraticObjective_resolvent_eq_diagonal_sum
    (lam : ℝ) (hlam : -H_min[Hdiag] < lam) :
    qShift lam (resolventPoint lam) =
      -((1 / 2 : ℝ) * Finset.sum Finset.univ
        (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam))) := by
  -- First replace the quadratic term by the action of the shifted matrix on the resolvent.
  change quadraticObjective 0 g (Ashift lam) (resolventPoint lam) =
    -((1 / 2 : ℝ) * Finset.sum Finset.univ
      (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)))
  rw [quadraticObjective_zero_eq_dotProduct,
    shiftedDiagonal_mulVec_resolventPoint (g := g) (Hdiag := Hdiag) lam hlam]
  have hdot_neg :
      dotProduct (-g) (resolventPoint lam) = -dotProduct g (resolventPoint lam) := by
    -- The second `dotProduct` differs only by a global minus sign.
    simp [dotProduct]
  have hdot_eval :
      dotProduct g (resolventPoint lam) =
        -Finset.sum Finset.univ (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) := by
    -- Evaluate the resolvent coordinates and simplify each term of the finite sum.
    calc
      dotProduct g (resolventPoint lam)
          = Finset.sum Finset.univ (fun i ↦ g i * resolventPoint lam i) := by
              rw [dotProduct]
      _ = Finset.sum Finset.univ (fun i ↦ -((g i) ^ (2 : ℕ) / (Hdiag i + lam))) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            have hpos : 0 < Hdiag i + lam := by
              have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
                diagonalMinimum_le_entry (Hdiag := Hdiag) i
              linarith
            have hne : Hdiag i + lam ≠ 0 := ne_of_gt hpos
            rw [diagonalResolventPoint_apply (g := g) (Hdiag := Hdiag) lam hlam i]
            field_simp [hne]
      _ = -Finset.sum Finset.univ (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) := by
            rw [Finset.sum_neg_distrib]
  calc
    dotProduct g (resolventPoint lam) + (1 / 2 : ℝ) * dotProduct (-g) (resolventPoint lam)
        = (1 / 2 : ℝ) * dotProduct g (resolventPoint lam) := by
            nlinarith [hdot_neg]
    _ = -((1 / 2 : ℝ) * Finset.sum Finset.univ
          (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam))) := by
            rw [hdot_eval]
            ring

/-- Helper for Proposition 4.1.9: the active part of the diagonal reciprocal sum collapses to
`G² / (H_min + λ)`. -/
lemma active_diagonal_sum_eq_minimalGradientSquare_div
    (lam : ℝ) :
    Finset.sum (I*[Hdiag]) (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) =
      G²[g;Hdiag] / (H_min[Hdiag] + lam) := by
  -- On `I*`, every denominator is the same because `Hdiag i = H_min`.
  unfold cubicRegularizedMinimalDiagonalGradientSquare
  calc
    Finset.sum (I*[Hdiag]) (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam))
        =
          Finset.sum (I*[Hdiag])
            (fun i ↦ (g i) ^ (2 : ℕ) / (H_min[Hdiag] + lam)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi' : Hdiag i = H_min[Hdiag] :=
              (mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag i).mp hi
            simp [hi']
    _ = Finset.sum (I*[Hdiag]) (fun i ↦ (g i) ^ (2 : ℕ)) / (H_min[Hdiag] + lam) := by
          rw [Finset.sum_div]

/-- Helper for Proposition 4.1.9: eliminating `τ` rewrites the scalar dual value as the infimum
of the shifted quadratic minus the cubic penalty. -/
lemma cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic_local
    (hM : 0 < M) (lam : ℝ) :
    ψ lam =
      sInf (Set.range fun h : E ↦
        ((qShift lam h - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal)) := by
  -- Introduce the explicit scalar minimizer so the `τ`-fiber minimum is available globally.
  rw [cubicRegularizedQuadraticDualFunction_eq_sInf]
  let τ := cubicRegularizedQuadraticTauMinimizer M lam
  have hτvalue :
      (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ =
        -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) := by
    -- The owner-side scalar minimizer theorem gives the exact cubic penalty value.
    simpa [τ] using cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM
  apply le_antisymm
  · refine le_sInf ?_
    rintro y ⟨h, rfl⟩
    have hsInf :
        sInf
            (Set.range
              (fun z : E × ℝ ↦
                (cubicRegularizedQuadraticScalarLagrangian g H M z.1 z.2 lam : EReal))) ≤
          (cubicRegularizedQuadraticScalarLagrangian g H M h τ lam : EReal) := by
      -- Insert the explicit minimizing slack value into the product-space infimum.
      exact sInf_le ⟨(h, τ), rfl⟩
    have hvalue :
        cubicRegularizedQuadraticScalarLagrangian g H M h τ lam =
          qShift lam h - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
      -- Evaluating the scalar minimizer leaves exactly the shifted quadratic minus the penalty.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term, hτvalue]
      ring
    simpa [shiftedQuadraticObjective, hvalue] using hsInf
  · refine le_sInf ?_
    rintro y ⟨⟨h, τ'⟩, rfl⟩
    have hsInf :
        sInf
            (Set.range
              (fun h : E ↦
                ((qShift lam h - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal))) ≤
          ((qShift lam h - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) : ℝ) : EReal) := by
      -- The reduced infimum is bounded above by the value on the current `h`-fiber.
      exact sInf_le ⟨h, rfl⟩
    have hvalue :
        cubicRegularizedQuadraticScalarLagrangian g H M h τ lam =
          qShift lam h - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
      -- Reuse the same minimizer value once when converting the chosen fiber minimum.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term, hτvalue]
      ring
    have hscalar :
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ ≤
          (M / 6 : ℝ) * |τ'| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ' := by
      -- The scalar minimizer theorem compares the chosen slack with every competitor.
      simpa [τ] using
        (isMinOn_univ_iff.mp (cubicRegularizedQuadraticTauMinimizer_isMinOn M hM lam)) τ'
    have hmin_real :
        cubicRegularizedQuadraticScalarLagrangian g H M h τ lam ≤
          cubicRegularizedQuadraticScalarLagrangian g H M h τ' lam := by
      -- Adding the constant quadratic term preserves the scalar-fiber minimum.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term,
        cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term]
      nlinarith
    have hmin :
        ((qShift lam h - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) : ℝ) : EReal) ≤
          (cubicRegularizedQuadraticScalarLagrangian g H M h τ' lam : EReal) := by
      -- Rewrite the minimizing fiber value into the reduced quadratic expression before coercing.
      rw [hvalue] at hmin_real
      exact EReal.coe_le_coe_iff.2 hmin_real
    exact le_trans hsInf hmin

/-- Helper for Proposition 4.1.9: when `λ > -H_min`, the diagonal resolvent is the global
minimizer of the shifted quadratic. -/
lemma diagonalResolvent_isMinOn_aux
    (lam : ℝ) (hlam : -H_min[Hdiag] < lam) :
    IsMinOn (qShift lam) Set.univ (resolventPoint lam) := by
  let problem : UnconstrainedQuadraticMinimizationProblem n :=
    { α := 0
      a := g
      A := Ashift lam
      posDef := by
        -- Positivity of every shifted diagonal entry gives positive definiteness.
        rw [diagonal_shift_eq_diagonal_add_scalar (Hdiag := Hdiag) lam]
        exact Matrix.PosDef.diagonal (n := Fin n) (R := ℝ)
          (d := fun i ↦ Hdiag i + lam) (by
            intro i
            have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
              diagonalMinimum_le_entry (Hdiag := Hdiag) i
            linarith) }
  -- The quadratic owner theorem identifies the canonical minimizer with the resolvent.
  simpa [problem, UnconstrainedQuadraticMinimizationProblem.minimizer] using
    (UnconstrainedQuadraticMinimizationProblem.minimizer_isMinOn problem)

-- Proof sketch: under `G² > 0`, the singular direction corresponding to `H_min` makes the dual
-- value equal to `-∞` exactly when `λ ≤ -H_min`, while `hGpos` forces `I*` nonempty and hence
-- rules out the vacuous `n = 0` case. Therefore `λ > -H_min` makes `H + λ I` positive definite
-- and the infimum finite.
/-- If `G² > 0`, then the dual domain is exactly the open half-line `(-H_min, ∞)`. -/
theorem cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
      (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) :
    dom ψ = Set.Ioi (-H_min[Hdiag]) := by
  -- Rewrite `dom ψ` into boundedness below of the shifted quadratic owner.
  rw [cubicRegularizedQuadraticScalarDualDomain_eq g H hM]
  ext lam
  constructor
  · intro hbb
    -- A global minimizer on the interior point gives an explicit lower bound.
    have hbb' : BddBelow (Set.range (qShift lam)) := by
      simpa [shiftedQuadraticObjective] using hbb
    by_contra hnot
    have hle : lam ≤ -H_min[Hdiag] := not_lt.mp hnot
    rcases active_index_exists_of_activeGradientSquare_pos (g := g) (Hdiag := Hdiag) hGpos with
      ⟨i, hi, hgi⟩
    have hi_min : Hdiag i = H_min[Hdiag] :=
      (mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag i).mp hi
    have hline : BddBelow (Set.range fun t : ℝ ↦ qShift lam (EuclideanSpace.single i t)) := by
      -- Any lower bound on the whole quadratic restricts to the active coordinate line.
      rcases hbb' with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rintro y ⟨t, rfl⟩
      exact hm ⟨EuclideanSpace.single i t, rfl⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hneg : Hdiag i + lam < 0 := by
        linarith
      have hline' :
          BddBelow
            (Set.range fun t : ℝ ↦
              (1 / 2 : ℝ) * (Hdiag i + lam) * t ^ (2 : ℕ) + g i * t) := by
        -- Reordering the coordinate-line formula matches the negative-quadratic obstruction.
        have hline_eq :
            (fun t : ℝ ↦ qShift lam (EuclideanSpace.single i t)) =
              fun t : ℝ ↦ (1 / 2 : ℝ) * (Hdiag i + lam) * t ^ (2 : ℕ) + g i * t := by
          funext t
          rw [quadraticObjective_single_eq (g := g) (Hdiag := Hdiag) (lam := lam) t i]
          ring
        simpa [hline_eq] using hline
      exact (not_bddBelow_negative_quadratic_line (a := Hdiag i + lam) (b := g i) hneg) hline'
    · have hline' : BddBelow (Set.range fun t : ℝ ↦ g i * t) := by
        -- At the boundary `λ = -H_min`, the quadratic coefficient vanishes on active indices.
        have hline_eq :
            (fun t : ℝ ↦ qShift lam (EuclideanSpace.single i t)) =
              fun t : ℝ ↦ g i * t := by
          funext t
          rw [quadraticObjective_single_eq (g := g) (Hdiag := Hdiag) (lam := lam) t i]
          simp [hi_min, heq]
        simpa [hline_eq] using hline
      exact (not_bddBelow_nonzero_linear_line (b := g i) hgi) hline'
  · intro hlam
    -- Interior multipliers admit the global resolvent minimizer, hence a lower bound.
    have hlt : -H_min[Hdiag] < lam := by
      simpa [Set.mem_Ioi] using hlam
    refine ⟨qShift lam (resolventPoint lam), ?_⟩
    rintro y ⟨h, rfl⟩
    exact (isMinOn_univ_iff.mp
      (diagonalResolvent_isMinOn_aux (g := g) (Hdiag := Hdiag) lam hlt)) h

-- Proof sketch: combine the `τ`-elimination formula from
-- `cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic` with the domain
-- characterization from `cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos`
-- to identify the admissible `λ`, evaluate the unique minimizer of `q_λ` at
-- `-(H + λ I)⁻¹ g`, and split the sum into the active part `G² / (H_min + λ)` and the inactive
-- complementary sum.
/-- Proposition 4 1 9: if `M > 0` and `G² > 0`, then for every `λ` in
`dom ψ = {μ : ℝ | μ > -H_min}` the dual
function has the closed form
`ψ(λ) = -(1 / 2) G² / (H_min + λ) - (1 / 2) ∑_{i ∉ I*} (g^(i))² / (H_i + λ) - (2 / (3 M²)) |λ|³`.
The companion statements around it record the domain identity, expose the owner-level minimizer
theorem for `q_λ`, and add the matching owner-level uniqueness statement. -/
theorem cubicRegularizedQuadraticDualFunction_eq_closedForm_of_activeGradientSquare_pos
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) (lam : ℝ)
    (hlam : lam ∈ dom ψ) :
    ψ lam =
      ((-(1 / 2 : ℝ) * G²[g;Hdiag] / (H_min[Hdiag] + lam) -
        (1 / 2 : ℝ) * Finset.sum Irest (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) -
        (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) : ℝ) : EReal) := by
  -- Convert domain membership into the strict interior inequality needed by the resolvent API.
  have hlam' : -H_min[Hdiag] < lam := by
    simpa [Set.mem_Ioi,
      cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
        (g := g) (Hdiag := Hdiag) (M := M) hM hGpos] using hlam
  let κ : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)
  have hsInf_eq :
      sInf (Set.range fun h : E ↦ ((qShift lam h - κ) : EReal)) =
        ((qShift lam (resolventPoint lam) - κ : ℝ) : EReal) := by
    apply le_antisymm
    · -- The infimum is at most the value at the explicit resolvent point.
      exact sInf_le ⟨resolventPoint lam, rfl⟩
    · refine le_sInf ?_
      rintro y ⟨h, rfl⟩
      -- The resolvent minimizes `q_λ`, so subtracting the constant penalty preserves the order.
      exact EReal.coe_le_coe_iff.2 <|
        sub_le_sub_right ((isMinOn_univ_iff.mp
          (diagonalResolvent_isMinOn_aux (g := g) (Hdiag := Hdiag) lam hlam')) h) κ
  have hsInf_eq' :
      sInf
          (Set.range
            fun h : E ↦
              ((qShift lam h - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal)) =
        ((qShift lam (resolventPoint lam) -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) : ℝ) : EReal) := by
    simpa [κ] using hsInf_eq
  have hsplit :
      Finset.sum (I*[Hdiag]) (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) +
          Finset.sum (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
            (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) =
        Finset.sum Finset.univ (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) := by
    -- Split the full finite sum into the active and inactive diagonal indices.
    simpa using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun i : Fin n ↦ i ∈ I*[Hdiag])
        (f := fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)))
  rw [cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic_local
    (g := g) (Hdiag := Hdiag) (M := M) hM lam, hsInf_eq']
  apply EReal.coe_eq_coe_iff.2
  -- Evaluate the minimized shifted quadratic and then isolate the active contribution.
  calc
    qShift lam (resolventPoint lam) - κ
        = -((1 / 2 : ℝ) * Finset.sum Finset.univ
            (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam))) - κ := by
          rw [quadraticObjective_resolvent_eq_diagonal_sum
            (g := g) (Hdiag := Hdiag) lam hlam']
    _ = -((1 / 2 : ℝ) *
          (Finset.sum (I*[Hdiag]) (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) +
            Finset.sum Irest (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)))) - κ := by
          rw [← hsplit]
    _ = (-(1 / 2 : ℝ) *
          Finset.sum (I*[Hdiag]) (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) -
          (1 / 2 : ℝ) * Finset.sum Irest (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) - κ) := by
          ring
    _ = (-(1 / 2 : ℝ) * G²[g;Hdiag] / (H_min[Hdiag] + lam) -
          (1 / 2 : ℝ) * Finset.sum Irest (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) - κ) := by
          rw [active_diagonal_sum_eq_minimalGradientSquare_div (g := g) (Hdiag := Hdiag) lam,
            div_eq_mul_inv]
          ring
    _ = (-(1 / 2 : ℝ) * G²[g;Hdiag] / (H_min[Hdiag] + lam) -
          (1 / 2 : ℝ) * Finset.sum Irest (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lam)) -
          (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) := by
          simp [κ]

-- Proof sketch: `-H_min < λ` is exactly the intrinsic diagonal positivity condition for
-- `H + λ I`. The shifted quadratic owner `q_λ` then has the canonical Euclidean-space
-- resolvent minimizer `resolvent λ`, whose coordinate formula is recorded downstream in
-- `Proposition_4_1_10`.
/-- If `λ > -H_min`, then the canonical diagonal resolvent point `resolvent λ` minimizes the
shifted quadratic `q_λ`. -/
theorem cubicRegularizedDiagonalResolvent_isMinOn
    (lam : ℝ) (hlam : -H_min[Hdiag] < lam) :
    IsMinOn (qShift lam) Set.univ (resolventPoint lam) := by
  -- This source-facing theorem is the public wrapper around the earlier owner-level helper.
  exact diagonalResolvent_isMinOn_aux (g := g) (Hdiag := Hdiag) lam hlam

-- Proof sketch: package `q_λ` as an `UnconstrainedQuadraticMinimizationProblem`, use the
-- Chapter 1 owner theorem `minimizer_unique`, and compare the given minimizer with the canonical
-- resolvent minimizer above.
/-- If `λ > -H_min`, then every global minimizer of the shifted diagonal quadratic `q_λ`
coincides with the canonical diagonal resolvent point `resolvent λ`. -/
theorem cubicRegularizedDiagonalResolvent_unique
    (lam : ℝ) (hlam : -H_min[Hdiag] < lam)
    (h : E)
    (hh : IsMinOn (qShift lam) Set.univ h) :
    h = resolventPoint lam := by
  let problem : UnconstrainedQuadraticMinimizationProblem n :=
    { α := 0
      a := g
      A := Ashift lam
      posDef := by
        -- This is the same positive-definite shifted quadratic packaged in owner form.
        rw [diagonal_shift_eq_diagonal_add_scalar (Hdiag := Hdiag) lam]
        exact Matrix.PosDef.diagonal (n := Fin n) (R := ℝ)
          (d := fun i ↦ Hdiag i + lam) (by
            intro i
            have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
              diagonalMinimum_le_entry (Hdiag := Hdiag) i
            linarith) }
  -- The Chapter 1 uniqueness theorem identifies every minimizer with `problem.minimizer`.
  simpa [problem, UnconstrainedQuadraticMinimizationProblem.minimizer, shiftedQuadraticObjective,
    diagonalResolventPoint] using
    (UnconstrainedQuadraticMinimizationProblem.minimizer_unique problem hh)

end

end
