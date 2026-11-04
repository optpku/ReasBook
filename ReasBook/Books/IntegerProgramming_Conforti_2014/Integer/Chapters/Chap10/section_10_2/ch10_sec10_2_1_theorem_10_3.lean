/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_4

/- Theorem 10.3 is source-facing at the complete-graph matrix level, while Exercise 10.4 already
owns the repository's canonical `SimpleGraph`/`Sym2` weighted max-cut API. This file keeps the
matrix model primary and uses `Matrix.toSym2Weight` as the bridge to that canonical owner. -/

open scoped ENNReal InnerProductSpace MatrixOrder NNReal

section Theorem103

variable {n : ℕ}

namespace Matrix

/-- Convert a complete-graph weight matrix into the repository's canonical `Sym2`-indexed edge
weight on unordered vertex pairs by symmetrizing the matrix entries. On symmetric matrices, this
recovers the original off-diagonal weights, while diagonal terms are harmless because the complete
graph edge set contains no loops. -/
noncomputable def toSym2Weight (w : Matrix (Fin n) (Fin n) ℝ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j ↦ (w i j + w j i) / 2, by
    intro i j
    ring⟩

/-- On the unordered pair `s(i, j)`, `toSym2Weight w` is the average of the two matrix
orientations. -/
@[simp] theorem toSym2Weight_apply
    (w : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    toSym2Weight w s(i, j) = (w i j + w j i) / 2 := rfl

/-- For a symmetric weight matrix, `toSym2Weight` agrees with the original matrix entries. -/
theorem toSym2Weight_apply_of_isSymm
    (w : Matrix (Fin n) (Fin n) ℝ) (h_symm : w.IsSymm) (i j : Fin n) :
    toSym2Weight w s(i, j) = w i j := by
  rw [toSym2Weight_apply]
  have hij : w j i = w i j := h_symm.apply i j
  rw [hij]
  ring

/-- For a symmetric nonnegative weight matrix, the induced `Sym2`-indexed edge weight is
entrywise nonnegative. -/
theorem toSym2Weight_nonneg_of_isSymm
    (w : Matrix (Fin n) (Fin n) ℝ) (h_symm : w.IsSymm)
    (h_nonneg : ∀ i j, 0 ≤ w i j) (e : Sym2 (Fin n)) :
    0 ≤ toSym2Weight w e := by
  refine Sym2.ind ?_ e
  intro i j
  rw [toSym2Weight_apply_of_isSymm w h_symm i j]
  exact h_nonneg i j

/-- Entrywise nonnegativity of the matrix entries transfers to the canonical `Sym2`-indexed weight
function. -/
theorem toSym2Weight_nonneg
    (w : Matrix (Fin n) (Fin n) ℝ) (h_nonneg : ∀ i j, 0 ≤ w i j) (e : Sym2 (Fin n)) :
    0 ≤ toSym2Weight w e := by
  refine Sym2.ind ?_ e
  intro i j
  rw [toSym2Weight_apply]
  exact div_nonneg (add_nonneg (h_nonneg i j) (h_nonneg j i)) (by norm_num)

end Matrix

/-- Helper for Theorem 10.3: the Goemans-Williamson attainable-value set is nonempty because the
identity matrix is a feasible witness. -/
lemma goemansWilliamsonObjectiveValues_nonempty
    (w : Sym2 (Fin n) → ℝ) :
    (goemans_williamson_objective_values (⊤ : SimpleGraph (Fin n)) w).Nonempty := by
  -- Register the identity matrix as an explicit feasible point of the relaxation.
  refine ⟨goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w
    (1 : Matrix (Fin n) (Fin n) ℝ), ?_⟩
  refine ⟨(1 : Matrix (Fin n) (Fin n) ℝ), ?_, rfl⟩
  refine goemans_williamson_feasible.mk ?_ ?_
  · simpa using (Matrix.PosSemidef.one : Matrix.PosSemidef (1 : Matrix (Fin n) (Fin n) ℝ))
  · intro v
    simp

/-- Helper for Theorem 10.3: a pointwise approximation factor on every feasible
Goemans-Williamson witness upgrades directly to the ratio bound on the optimal values. -/
lemma goemansWilliamsonRatioLowerBound_of_pointwiseApprox
    (w : Sym2 (Fin n) → ℝ)
    {β : ℝ}
    (hβ : (87856 : ℝ) / 100000 < β)
    (hScaled :
      ∀ {X : Matrix (Fin n) (Fin n) ℝ}, goemans_williamson_feasible X →
        β * goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X ≤
          max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w)
    (hsdp_pos : 0 < goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w) :
    max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w /
        goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w >
      (87856 : ℝ) / 100000 := by
  have hβ_pos : 0 < β := by
    -- The target constant is positive, so any strict improvement is also positive.
    exact lt_trans (by norm_num : (0 : ℝ) < (87856 : ℝ) / 100000) hβ
  have hValueLe :
      goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w ≤
        max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w / β := by
    -- Bound the supremum by checking the scaled inequality on each feasible witness.
    rw [goemans_williamson_value_eq_sSup]
    refine csSup_le (goemansWilliamsonObjectiveValues_nonempty (n := n) w) ?_
    intro r hr
    rcases hr with ⟨X, hX, rfl⟩
    have hScaled' :
        goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X * β ≤
          max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
      simpa [mul_comm] using hScaled hX
    exact (le_div_iff₀ hβ_pos).2 hScaled'
  have hScaledValue :
      β * goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w ≤
        max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
    -- Multiply the supremum bound by `β` and simplify the right-hand side.
    calc
      β * goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w ≤
          β * (max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w / β) :=
        mul_le_mul_of_nonneg_left hValueLe hβ_pos.le
      _ = β * (max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w * β⁻¹) := by
        rw [div_eq_mul_inv]
      _ = max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w * (β * β⁻¹) := by
        ring
      _ = max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
        simp [hβ_pos.ne']
  have hRatio : β ≤
      max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w /
        goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w := by
    -- Divide by the positive semidefinite optimum to recover the ratio lower bound.
    exact (le_div_iff₀ hsdp_pos).2 hScaledValue
  exact lt_of_lt_of_le hβ hRatio

/-- Helper for Theorem 10.3: a feasible Goemans-Williamson matrix is the Gram matrix of a unit
family of column vectors in `ℝ^n`. -/
lemma existsUnitVectorFamilyOfGoemansWilliamsonFeasible
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : goemans_williamson_feasible X) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, dotProduct (fun k ↦ U k i) (fun k ↦ U k j) = X i j) ∧
      (∀ i, dotProduct (fun k ↦ U k i) (fun k ↦ U k i) = 1) := by
  -- Factor the feasible PSD matrix as `Uᵀ * U`, then read the columns of `U`.
  obtain ⟨U, hGram⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (goemans_williamson_feasible.posSemidef hX).nonneg
  have hDot :
      ∀ i j, dotProduct (fun k ↦ U k i) (fun k ↦ U k j) = X i j := by
    intro i j
    -- Expanding one matrix entry turns the factorization into a dot product identity.
    calc
      dotProduct (fun k ↦ U k i) (fun k ↦ U k j) = (star U * U) i j := by
        simp [Matrix.mul_apply, dotProduct]
      _ = X i j := by
        simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hGram.symm
  refine ⟨U, hDot, ?_⟩
  intro i
  -- The diagonal constraint identifies each self-dot-product with `1`.
  calc
    dotProduct (fun k ↦ U k i) (fun k ↦ U k i) = X i i := hDot i i
    _ = 1 := goemans_williamson_feasible.diag_eq_one hX i

/-- Helper for Theorem 10.3: after choosing Gram columns for a feasible matrix, the
Goemans-Williamson objective is the edge sum of the textbook dot-gap terms `(1 - u_i · u_j) / 2`.
-/
lemma goemansWilliamsonObjective_eq_sum_dotGap
    (w : Sym2 (Fin n) → ℝ)
    {X U : Matrix (Fin n) (Fin n) ℝ}
    (hDot : ∀ i j, dotProduct (fun k ↦ U k i) (fun k ↦ U k j) = X i j) :
    goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X =
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun i j : Fin n ↦ (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2, by
              intro i j
              simp [dotProduct_comm]
            ⟩
            e := by
  -- Normalize the complete-graph objective once so the final comparison can be done edgewise.
  classical
  have hedgeFinset :
      (letI : DecidableRel (⊤ : SimpleGraph (Fin n)).Adj :=
        Classical.decRel (⊤ : SimpleGraph (Fin n)).Adj
       (⊤ : SimpleGraph (Fin n)).edgeFinset) =
        (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  rw [goemans_williamson_objective_eq_sum, hedgeFinset]
  refine Finset.sum_congr rfl ?_
  intro e _
  refine Sym2.ind ?_ e
  intro i j
  have hSymm : X j i = X i j := by
    calc
      X j i = dotProduct (fun k ↦ U k j) (fun k ↦ U k i) := by symm; exact hDot j i
      _ = dotProduct (fun k ↦ U k i) (fun k ↦ U k j) := by rw [dotProduct_comm]
      _ = X i j := hDot i j
  -- On each unordered edge, the symmetric matrix term collapses to a single dot product.
  change
    w s(i, j) * (((2 : ℝ) - X i j - X j i) / 4) =
      w s(i, j) * ((1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2)
  rw [hSymm, hDot i j]
  ring

/-- Helper for Theorem 10.3: the Gram dot products attached to a feasible witness lie in `[-1, 1]`.
-/
lemma goemansWilliamsonDot_mem_Icc_of_unitColumnFamily
    {X U : Matrix (Fin n) (Fin n) ℝ}
    (hX : goemans_williamson_feasible X)
    (hDot : ∀ i j, dotProduct (fun k ↦ U k i) (fun k ↦ U k j) = X i j)
    (i j : Fin n) :
    dotProduct (fun k ↦ U k i) (fun k ↦ U k j) ∈ Set.Icc (-1 : ℝ) 1 := by
  -- Transport the interval control from the existing Chapter 10.6 feasible edge-term lemma.
  have hSymm : X j i = X i j := by
    calc
      X j i = dotProduct (fun k ↦ U k j) (fun k ↦ U k i) := by symm; exact hDot j i
      _ = dotProduct (fun k ↦ U k i) (fun k ↦ U k j) := by rw [dotProduct_comm]
      _ = X i j := hDot i j
  have hEdge := goemansWilliamsonEdgeTerm_mem_Icc_zero_one (hX := hX) i j
  have hLower : 0 ≤ (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 := by
    have hLower' : 0 ≤ (2 - X i j - X i j) / 4 := by
      simpa [hSymm] using hEdge.1
    have hRewrite :
        (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 =
          (2 - X i j - X i j) / 4 := by
      rw [hDot i j]
      ring
    calc
      0 ≤ (2 - X i j - X i j) / 4 := hLower'
      _ = (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 := by
        symm
        exact hRewrite
  have hUpper : (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 ≤ 1 := by
    have hUpper' : (2 - X i j - X i j) / 4 ≤ 1 := by
      simpa [hSymm] using hEdge.2
    have hRewrite :
        (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 =
          (2 - X i j - X i j) / 4 := by
      rw [hDot i j]
      ring
    calc
      (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 =
          (2 - X i j - X i j) / 4 := hRewrite
      _ ≤ 1 := hUpper'
  constructor <;> nlinarith

/-- Helper for Theorem 10.3: a Boolean sign pattern contributes `1` exactly on unordered pairs
whose endpoint signs disagree. -/
lemma boolPattern_maxCutNodeObjective_eq_disagreementSum
    (w : Sym2 (Fin n) → ℝ) (σ : Fin n → Bool) :
    max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
        (fun i ↦ if σ i then (1 : ℝ) else 0) =
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun i j : Fin n ↦ if σ i = σ j then 0 else 1, by
                intro i j
                by_cases hij : σ i = σ j <;> simp [hij, eq_comm]
            ⟩
            e := by
  -- Expand the node objective once and compute the `0/1` edge term by cases on the two signs.
  classical
  have hedgeFinset :
      (letI : DecidableRel (⊤ : SimpleGraph (Fin n)).Adj :=
        Classical.decRel (⊤ : SimpleGraph (Fin n)).Adj
       (⊤ : SimpleGraph (Fin n)).edgeFinset) =
        (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  rw [max_cut_node_objective_eq_sum, hedgeFinset]
  refine Finset.sum_congr rfl ?_
  intro e _
  refine Sym2.ind ?_ e
  intro i j
  change
    w s(i, j) *
        ((if σ i then (1 : ℝ) else 0) + (if σ j then 1 else 0) -
          2 * (if σ i then 1 else 0) * (if σ j then 1 else 0)) =
      w s(i, j) * (if σ i = σ j then 0 else 1)
  by_cases hi : σ i
  · by_cases hj : σ j
    · norm_num [hi, hj]
    · norm_num [hi, hj]
  · by_cases hj : σ j
    · norm_num [hi, hj]
    · norm_num [hi, hj]

/-- Helper for Theorem 10.3: every Boolean sign pattern defines a feasible `0/1` max-cut point. -/
lemma boolPattern_maxCutNodeObjective_mem_values
    (w : Sym2 (Fin n) → ℝ) (σ : Fin n → Bool) :
    max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
        (fun i ↦ if σ i then (1 : ℝ) else 0) ∈
      max_cut_node_objective_values (⊤ : SimpleGraph (Fin n)) w := by
  -- Register the Boolean indicator assignment as an explicit feasible point of the node model.
  refine ⟨fun i ↦ if σ i then (1 : ℝ) else 0, ?_, rfl⟩
  intro i
  by_cases hi : σ i <;> simp [hi]

/-- Helper for Theorem 10.3: on the finite vertex set `Fin n`, the attainable integral max-cut
values form a finite set because every feasible `0/1` assignment comes from a Boolean pattern. -/
lemma maxCutNodeObjectiveValues_finite
    (w : Sym2 (Fin n) → ℝ) :
    (max_cut_node_objective_values (⊤ : SimpleGraph (Fin n)) w).Finite := by
  classical
  let F : (Fin n → Bool) → ℝ := fun σ ↦
    max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
      (fun i ↦ if σ i then (1 : ℝ) else 0)
  refine (Set.finite_range F).subset ?_
  intro r hr
  rcases hr with ⟨χ, hχ, rfl⟩
  let σ : Fin n → Bool := fun i ↦ if χ i = 1 then true else false
  refine ⟨σ, ?_⟩
  -- Recover the original feasible assignment by remembering whether each coordinate is `1`.
  have hχ_bool :
      (fun i ↦ if σ i then (1 : ℝ) else 0) = χ := by
    funext i
    rcases hχ i with h0 | h1
    · simp [σ, h0]
    · simp [σ, h1]
  simp [F, hχ_bool]

/-- Helper for Theorem 10.3: averaging Boolean cuts against any probability measure stays below
the integer optimum `z_I`. -/
lemma averageBooleanCut_le_maxCutIntegerValue
    (w : Sym2 (Fin n) → ℝ) (μ : MeasureTheory.Measure (Fin n → Bool))
    (hμ : μ Set.univ = 1) :
    MeasureTheory.integral μ
        (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
          (fun i ↦ if σ i then (1 : ℝ) else 0)) ≤
      max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
  classical
  letI : MeasureTheory.IsFiniteMeasure μ := ⟨by simp [hμ]⟩
  let f : (Fin n → Bool) → ℝ := fun σ ↦
    max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
      (fun i ↦ if σ i then (1 : ℝ) else 0)
  have hf : MeasureTheory.Integrable f μ := by
    -- The Boolean codomain is finite, so every real-valued function on it is integrable.
    exact MeasureTheory.Integrable.of_finite
  have hpointwise :
      ∀ σ, f σ ≤ max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
    intro σ
    -- Each Boolean cut value belongs to the finite attainable-value set, so it is below `sSup`.
    rw [max_cut_integer_value_eq_sSup]
    exact le_csSup
      (maxCutNodeObjectiveValues_finite (n := n) w).bddAbove
      (boolPattern_maxCutNodeObjective_mem_values (n := n) w σ)
  calc
    MeasureTheory.integral μ f = (∑ σ, μ.real {σ} • f σ) := by
      rw [MeasureTheory.integral_fintype hf]
    _ = (∑ σ, μ.real {σ} * f σ) := by
      simp [smul_eq_mul]
    _ ≤ (∑ σ, μ.real {σ} * max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w) := by
      refine Finset.sum_le_sum ?_
      intro σ _
      exact mul_le_mul_of_nonneg_left (hpointwise σ) ENNReal.toReal_nonneg
    _ = MeasureTheory.integral μ (fun _ : Fin n → Bool ↦
          max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w) := by
      symm
      rw [MeasureTheory.integral_fintype (MeasureTheory.integrable_const
        (max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w))]
      simp [smul_eq_mul]
    _ = max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
      rw [MeasureTheory.integral_const]
      have hμ_real : μ.real Set.univ = 1 := by
        simp [MeasureTheory.measureReal_def, hμ]
      rw [hμ_real]
      simp

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the two inner products with `u` and `v`, bundled as a continuous linear map into two-dimensional
Euclidean space. -/
noncomputable def stdGaussianInnerPairCLM
    (u v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![innerSL ℝ u, innerSL ℝ v])

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the inner-pair map has the expected two coordinates. -/
@[simp] lemma stdGaussianInnerPairCLM_apply
    (u v g : EuclideanSpace ℝ (Fin n)) :
    stdGaussianInnerPairCLM u v g =
      WithLp.toLp 2 ![dotProduct g u, dotProduct g v] := by
  -- Evaluate the two inner-product functionals coordinatewise.
  ext i
  fin_cases i <;>
    simp [stdGaussianInnerPairCLM, innerSL_apply_apply, PiLp.inner_apply,
      dotProduct, mul_comm]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the canonical correlated pair with correlation `ρ`, obtained from two independent standard
coordinates. -/
noncomputable def stdGaussianCorrelatedPairCLM (ρ : ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      ![EuclideanSpace.proj 0,
        ρ • EuclideanSpace.proj 0 + Real.sqrt (1 - ρ ^ 2) • EuclideanSpace.proj 1])

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the correlated-pair map has its defining coordinate formula. -/
@[simp] lemma stdGaussianCorrelatedPairCLM_apply
    (ρ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    stdGaussianCorrelatedPairCLM ρ z =
      WithLp.toLp 2 ![z 0, ρ * z 0 + Real.sqrt (1 - ρ ^ 2) * z 1] := by
  -- Evaluate the coordinate projections and scalar linear combinations.
  ext i
  fin_cases i <;> simp [stdGaussianCorrelatedPairCLM]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the adjoint of the inner-pair map sends the first coordinate vector to `u`. -/
lemma stdGaussianInnerPairCLM_adjoint_basis_zero
    (u v : EuclideanSpace ℝ (Fin n)) :
    (stdGaussianInnerPairCLM u v).adjoint
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0) = u := by
  -- Test the adjoint identity against an arbitrary ambient vector.
  apply ext_inner_left ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [stdGaussianInnerPairCLM_apply, PiLp.inner_apply, dotProduct, mul_comm]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the adjoint of the inner-pair map sends the second coordinate vector to `v`. -/
lemma stdGaussianInnerPairCLM_adjoint_basis_one
    (u v : EuclideanSpace ℝ (Fin n)) :
    (stdGaussianInnerPairCLM u v).adjoint
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1) = v := by
  -- Test the adjoint identity against an arbitrary ambient vector.
  apply ext_inner_left ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [stdGaussianInnerPairCLM_apply, PiLp.inner_apply, dotProduct, mul_comm]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the first coordinate vector is fixed by the adjoint of the correlated-pair map. -/
lemma stdGaussianCorrelatedPairCLM_adjoint_basis_zero (ρ : ℝ) :
    (stdGaussianCorrelatedPairCLM ρ).adjoint
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0) =
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0 := by
  -- The first output coordinate is exactly the first input coordinate.
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [stdGaussianCorrelatedPairCLM_apply, PiLp.inner_apply]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the second coordinate vector pulls back to the correlation vector
`ρ e₀ + √(1 - ρ²) e₁`. -/
lemma stdGaussianCorrelatedPairCLM_adjoint_basis_one (ρ : ℝ) :
    (stdGaussianCorrelatedPairCLM ρ).adjoint
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1) =
      ρ • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0 +
        Real.sqrt (1 - ρ ^ 2) • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 := by
  -- The second output coordinate is the stated linear combination.
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [stdGaussianCorrelatedPairCLM_apply, PiLp.inner_apply, mul_comm]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the Gaussian inner pair of two unit vectors has the same law as the canonical correlated
two-coordinate Gaussian pair. -/
lemma stdGaussianInnerPair_map_eq_correlatedPair
    (u v : EuclideanSpace ℝ (Fin n))
    (hu : dotProduct u u = 1) (hv : dotProduct v v = 1) :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map
        (stdGaussianInnerPairCLM u v) =
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))).map
        (stdGaussianCorrelatedPairCLM (dotProduct u v)) := by
  let ρ : ℝ := dotProduct u v
  have hu_inner : ⟪u, u⟫_ℝ = 1 := by
    rw [PiLp.inner_apply]
    simpa [dotProduct, pow_two] using hu
  have hv_inner : ⟪v, v⟫_ℝ = 1 := by
    rw [PiLp.inner_apply]
    simpa [dotProduct, pow_two] using hv
  have hu_norm : ‖u‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hu_inner
    nlinarith [norm_nonneg u]
  have hv_norm : ‖v‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hv_inner
    nlinarith [norm_nonneg v]
  have hρ : ρ ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [ρ, PiLp.inner_apply, dotProduct, mul_comm] using
      (real_inner_mem_Icc_of_norm_eq_one hu_norm hv_norm)
  have hsquare : Real.sqrt (1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith [hρ.1, hρ.2]
  have hmean_left :
      ∫ z, z ∂((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map
        (stdGaussianInnerPairCLM u v)) = 0 := by
    rw [(stdGaussianInnerPairCLM u v).integral_id_map
      ProbabilityTheory.IsGaussian.integrable_id,
      ProbabilityTheory.integral_id_stdGaussian, map_zero]
  have hmean_right :
      ∫ z, z ∂((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))).map
        (stdGaussianCorrelatedPairCLM ρ)) = 0 := by
    rw [(stdGaussianCorrelatedPairCLM ρ).integral_id_map
      ProbabilityTheory.IsGaussian.integrable_id,
      ProbabilityTheory.integral_id_stdGaussian, map_zero]
  -- Gaussian uniqueness now reduces the law equality to its four covariance entries.
  apply ProbabilityTheory.IsGaussian.ext
  · simpa only [id_eq] using hmean_left.trans hmean_right.symm
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis fun i j ↦ ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      ProbabilityTheory.covarianceBilin_map ProbabilityTheory.IsGaussian.memLp_two_id,
      ProbabilityTheory.covarianceBilin_map ProbabilityTheory.IsGaussian.memLp_two_id,
      ProbabilityTheory.covarianceBilin_stdGaussian,
      ProbabilityTheory.covarianceBilin_stdGaussian]
    have hleftAdj (i : Fin 2) :
        (stdGaussianInnerPairCLM u v).adjoint
            ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i) = ![u, v] i := by
      fin_cases i
      · simpa using stdGaussianInnerPairCLM_adjoint_basis_zero u v
      · simpa using stdGaussianInnerPairCLM_adjoint_basis_one u v
    have hrightAdj (i : Fin 2) :
        (stdGaussianCorrelatedPairCLM ρ).adjoint
            ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i) =
          ![(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0,
            ρ • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0 +
              Real.sqrt (1 - ρ ^ 2) • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1] i := by
      fin_cases i
      · simpa using stdGaussianCorrelatedPairCLM_adjoint_basis_zero ρ
      · simpa using stdGaussianCorrelatedPairCLM_adjoint_basis_one ρ
    have huv_inner : ⟪u, v⟫_ℝ = ρ := by
      rw [PiLp.inner_apply]
      simp [ρ, dotProduct, mul_comm]
    have hvu_inner : ⟪v, u⟫_ℝ = ρ := by
      exact (real_inner_comm u v).trans huv_inner
    have hu_innerSL : ((innerSL ℝ) u) u = 1 := hu_inner
    have hv_innerSL : ((innerSL ℝ) v) v = 1 := hv_inner
    have huv_innerSL : ((innerSL ℝ) u) v = ρ := huv_inner
    have hvu_innerSL : ((innerSL ℝ) v) u = ρ := hvu_inner
    have hright00 :
        ((innerSL ℝ) ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0))
            ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0) = 1 := by
      simp
    have hright01 :
        ((innerSL ℝ) ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0))
            (ρ • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0 +
              Real.sqrt (1 - ρ ^ 2) • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1) = ρ := by
      simp [PiLp.inner_apply]
    have hright10 :
        ((innerSL ℝ)
            (ρ • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0 +
              Real.sqrt (1 - ρ ^ 2) • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1))
            ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0) = ρ := by
      simp [PiLp.inner_apply]
    have hright11 :
        ((innerSL ℝ)
            (ρ • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0 +
              Real.sqrt (1 - ρ ^ 2) • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1))
            (ρ • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0 +
              Real.sqrt (1 - ρ ^ 2) • (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1) = 1 := by
      simp [PiLp.inner_apply]
      nlinarith [hsquare]
    rw [hleftAdj i, hleftAdj j, hrightAdj i, hrightAdj j]
    fin_cases i <;> fin_cases j
    · simpa only [Matrix.cons_val] using hu_innerSL.trans hright00.symm
    · simpa only [Matrix.cons_val] using huv_innerSL.trans hright01.symm
    · simpa only [Matrix.cons_val] using hvu_innerSL.trans hright10.symm
    · simpa only [Matrix.cons_val] using hv_innerSL.trans hright11.symm

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the product of two standard real Gaussian measures has the usual radial density on `ℝ × ℝ`. -/
lemma gaussianRealProd_eq_radialDensity :
    (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1) =
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).withDensity
        (fun z ↦ ENNReal.ofReal
          ((2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2))) := by
  -- Multiply the two one-dimensional Gaussian densities and combine their exponentials.
  have hone_ne : (1 : ℝ≥0) ≠ 0 := by norm_num
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hone_ne,
    MeasureTheory.prod_withDensity
      (ProbabilityTheory.measurable_gaussianPDF 0 1)
      (ProbabilityTheory.measurable_gaussianPDF 0 1),
    ← MeasureTheory.Measure.volume_eq_prod]
  · congr 1
    funext z
    simp only [ProbabilityTheory.gaussianPDF, ProbabilityTheory.gaussianPDFReal,
      NNReal.coe_one, sub_zero, mul_one]
    have hfirst_nonneg :
        0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z.1 ^ 2 / 2) := by
      positivity
    rw [← ENNReal.ofReal_mul hfirst_nonneg]
    congr 1
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have hsqrt_sq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := by
      rw [Real.sq_sqrt]
      positivity
    have hnormalization :
        (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ =
          (2 * Real.pi)⁻¹ := by
      calc
        (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ =
            (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi))⁻¹ := by
              rw [mul_inv]
        _ = (2 * Real.pi)⁻¹ := by rw [← pow_two, hsqrt_sq]
    calc
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z.1 ^ 2 / 2)) *
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z.2 ^ 2 / 2)) =
          ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹) *
            (Real.exp (-z.1 ^ 2 / 2) * Real.exp (-z.2 ^ 2 / 2)) := by ring
      _ = (2 * Real.pi)⁻¹ *
            Real.exp ((-z.1 ^ 2 / 2) + (-z.2 ^ 2 / 2)) := by
          rw [hnormalization, Real.exp_add]
      _ = (2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) := by
          congr 1
          ring
/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
on the fundamental interval `(-π, π)`, cosine is positive exactly on
`(-π / 2, π / 2)`. -/
lemma cos_pos_iff_of_mem_Ioo_neg_pi_pi
    {theta : ℝ} (htheta : theta ∈ Set.Ioo (-Real.pi) Real.pi) :
    0 < Real.cos theta ↔ theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  constructor
  · intro hcos
    constructor
    · by_contra hleft
      have htheta_le : theta ≤ -(Real.pi / 2) := le_of_not_gt hleft
      have hneg_mem : -theta ∈ Set.Icc (Real.pi / 2) (Real.pi + Real.pi / 2) := by
        constructor <;> linarith [htheta.1, Real.pi_pos]
      have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le hneg_mem.1 hneg_mem.2
      rw [Real.cos_neg] at hnonpos
      linarith
    · by_contra hright
      have htheta_ge : Real.pi / 2 ≤ theta := le_of_not_gt hright
      have hupper : theta ≤ Real.pi + Real.pi / 2 := by
        linarith [htheta.2, Real.pi_pos]
      have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le htheta_ge hupper
      linarith
  · exact Real.cos_pos_of_mem_Ioo

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
on `(-2π, π)`, positivity of cosine is the union of its two relevant positive arcs. -/
lemma cos_pos_iff_of_mem_Ioo_neg_two_pi_pi
    {theta : ℝ} (htheta : theta ∈ Set.Ioo (-(2 * Real.pi)) Real.pi) :
    0 < Real.cos theta ↔
      theta < -(3 * Real.pi / 2) ∨ theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  constructor
  · intro hcos
    by_cases hfar : theta < -(3 * Real.pi / 2)
    · exact Or.inl hfar
    · right
      constructor
      · by_contra hleft
        have htheta_le : theta ≤ -(Real.pi / 2) := le_of_not_gt hleft
        have hneg_mem : -theta ∈ Set.Icc (Real.pi / 2) (Real.pi + Real.pi / 2) := by
          constructor <;> linarith
        have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le hneg_mem.1 hneg_mem.2
        rw [Real.cos_neg] at hnonpos
        linarith
      · by_contra hright
        have htheta_ge : Real.pi / 2 ≤ theta := le_of_not_gt hright
        have hupper : theta ≤ Real.pi + Real.pi / 2 := by
          linarith [htheta.2, Real.pi_pos]
        have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le htheta_ge hupper
        linarith
  · intro htheta_pos
    rcases htheta_pos with hfar | hcentral
    · have hshift : theta + 2 * Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [htheta.1]
      rw [← Real.cos_add_two_pi theta]
      exact Real.cos_pos_of_mem_Ioo hshift
    · exact Real.cos_pos_of_mem_Ioo hcentral

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
two half-plane signs whose normals make an angle `phi ∈ [0, π]` disagree on angular arcs of
total Lebesgue length `2 * phi`. -/
lemma angularCosSignDisagreement_volume
    {phi : ℝ} (hphi : phi ∈ Set.Icc (0 : ℝ) Real.pi) :
    MeasureTheory.volume
        {theta : ℝ | theta ∈ Set.Ioo (-Real.pi) Real.pi ∧
          ((0 < Real.cos theta) ≠ (0 < Real.cos (theta - phi)))} =
      ENNReal.ofReal (2 * phi) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  by_cases hphi_half : phi ≤ Real.pi / 2
  · have hset :
        {theta : ℝ | theta ∈ Set.Ioo (-Real.pi) Real.pi ∧
          ((0 < Real.cos theta) ≠ (0 < Real.cos (theta - phi)))} =
        Set.Ioc (-(Real.pi / 2)) (phi - Real.pi / 2) ∪
          Set.Ico (Real.pi / 2) (phi + Real.pi / 2) := by
      ext theta
      by_cases htheta : theta ∈ Set.Ioo (-Real.pi) Real.pi
      · have hshift : theta - phi ∈ Set.Ioo (-(2 * Real.pi)) Real.pi := by
          constructor <;> linarith [htheta.1, htheta.2, hphi.1, hphi.2]
        rw [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioc, Set.mem_Ico,
          cos_pos_iff_of_mem_Ioo_neg_pi_pi htheta,
          cos_pos_iff_of_mem_Ioo_neg_two_pi_pi hshift]
        simp only [htheta, true_and, Set.mem_Ioo]
        grind
      · have hright_false :
            theta ∉ Set.Ioc (-(Real.pi / 2)) (phi - Real.pi / 2) ∪
              Set.Ico (Real.pi / 2) (phi + Real.pi / 2) := by
          intro hright
          apply htheta
          rcases hright with hright | hright
          · constructor <;> linarith [hright.1, hright.2, hphi.1]
          · constructor <;> linarith [hright.1, hright.2, hphi_half]
        constructor
        · intro hleft
          exact False.elim (htheta hleft.1)
        · intro hright
          exact False.elim (hright_false hright)
    rw [hset, MeasureTheory.measure_union]
    · rw [Real.volume_Ioc, Real.volume_Ico]
      have hleft : phi - Real.pi / 2 - -(Real.pi / 2) = phi := by ring
      have hright : phi + Real.pi / 2 - Real.pi / 2 = phi := by ring
      rw [hleft, hright, ← ENNReal.ofReal_add hphi.1 hphi.1]
      congr 1
      ring
    · refine Set.disjoint_left.2 ?_
      intro theta hleft hright
      simp only [Set.mem_Ioc] at hleft
      simp only [Set.mem_Ico] at hright
      linarith [hleft.2, hright.1, hphi_half]
    · exact measurableSet_Ico
  · have hphi_gt_half : Real.pi / 2 < phi := lt_of_not_ge hphi_half
    by_cases hphi_pi : phi = Real.pi
    · subst phi
      have hset :
          {theta : ℝ | theta ∈ Set.Ioo (-Real.pi) Real.pi ∧
            ((0 < Real.cos theta) ≠ (0 < Real.cos (theta - Real.pi)))} =
          Set.Ioo (-Real.pi) (-(Real.pi / 2)) ∪
            (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∪
              Set.Ioo (Real.pi / 2) Real.pi) := by
        ext theta
        by_cases htheta : theta ∈ Set.Ioo (-Real.pi) Real.pi
        · have hshift : theta - Real.pi ∈ Set.Ioo (-(2 * Real.pi)) Real.pi := by
            constructor <;> linarith [htheta.1, htheta.2]
          rw [Set.mem_setOf_eq, Set.mem_union, Set.mem_union, Set.mem_Ioo,
            Set.mem_Ioo, Set.mem_Ioo, cos_pos_iff_of_mem_Ioo_neg_pi_pi htheta,
            cos_pos_iff_of_mem_Ioo_neg_two_pi_pi hshift]
          grind
        · have hright_false :
              theta ∉ Set.Ioo (-Real.pi) (-(Real.pi / 2)) ∪
                (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∪
                  Set.Ioo (Real.pi / 2) Real.pi) := by
            intro hright
            apply htheta
            rcases hright with hright | hright
            · constructor
              · exact hright.1
              · linarith [hright.2]
            · rcases hright with hright | hright
              · constructor
                · linarith [hright.1]
                · linarith [hright.2]
              · constructor
                · linarith [hright.1]
                · exact hright.2
          constructor
          · intro hleft
            exact False.elim (htheta hleft.1)
          · intro hright
            exact False.elim (hright_false hright)
      rw [hset, MeasureTheory.measure_union]
      · rw [MeasureTheory.measure_union]
        · simp only [Real.volume_Ioo]
          rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_add]
          · congr 1
            ring
          all_goals nlinarith [Real.pi_pos]
        · refine Set.disjoint_left.2 ?_
          intro theta hleft hright
          simp only [Set.mem_Ioo] at hleft hright
          linarith
        · exact measurableSet_Ioo
      · refine Set.disjoint_left.2 ?_
        intro theta hleft hright
        simp only [Set.mem_Ioo] at hleft
        rcases hright with hright | hright
        · simp only [Set.mem_Ioo] at hright
          linarith
        · simp only [Set.mem_Ioo] at hright
          linarith
      · exact measurableSet_Ioo.union measurableSet_Ioo
    · have hphi_lt_pi : phi < Real.pi := lt_of_le_of_ne hphi.2 hphi_pi
      have hset :
          {theta : ℝ | theta ∈ Set.Ioo (-Real.pi) Real.pi ∧
            ((0 < Real.cos theta) ≠ (0 < Real.cos (theta - phi)))} =
          Set.Ioo (-Real.pi) (phi - 3 * Real.pi / 2) ∪
            (Set.Ioc (-(Real.pi / 2)) (phi - Real.pi / 2) ∪
              Set.Ico (Real.pi / 2) Real.pi) := by
        ext theta
        by_cases htheta : theta ∈ Set.Ioo (-Real.pi) Real.pi
        · have hshift : theta - phi ∈ Set.Ioo (-(2 * Real.pi)) Real.pi := by
            constructor <;> linarith [htheta.1, htheta.2, hphi.1, hphi.2]
          rw [Set.mem_setOf_eq, Set.mem_union, Set.mem_union, Set.mem_Ioo,
            Set.mem_Ioc, Set.mem_Ico, cos_pos_iff_of_mem_Ioo_neg_pi_pi htheta,
            cos_pos_iff_of_mem_Ioo_neg_two_pi_pi hshift]
          grind
        · have hright_false :
              theta ∉ Set.Ioo (-Real.pi) (phi - 3 * Real.pi / 2) ∪
                (Set.Ioc (-(Real.pi / 2)) (phi - Real.pi / 2) ∪
                  Set.Ico (Real.pi / 2) Real.pi) := by
            intro hright
            apply htheta
            rcases hright with hright | hright
            · constructor <;> linarith [hright.1, hright.2, hphi.2]
            · rcases hright with hright | hright
              · constructor <;> linarith [hright.1, hright.2, hphi.1, hphi.2]
              · constructor <;> linarith [hright.1, hright.2]
          constructor
          · intro hleft
            exact False.elim (htheta hleft.1)
          · intro hright
            exact False.elim (hright_false hright)
      rw [hset, MeasureTheory.measure_union]
      · rw [MeasureTheory.measure_union]
        · simp only [Real.volume_Ioo, Real.volume_Ioc, Real.volume_Ico]
          rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_add]
          · congr 1
            ring
          all_goals nlinarith [hphi.1, hphi.2]
        · refine Set.disjoint_left.2 ?_
          intro theta hleft hright
          simp only [Set.mem_Ioc] at hleft
          simp only [Set.mem_Ico] at hright
          linarith [hleft.2, hright.1, hphi_lt_pi]
        · exact measurableSet_Ico
      · refine Set.disjoint_left.2 ?_
        intro theta hleft hright
        simp only [Set.mem_Ioo] at hleft
        rcases hright with hright | hright
        · simp only [Set.mem_Ioc] at hright
          linarith [hleft.2, hright.1, hphi_gt_half]
        · simp only [Set.mem_Ico] at hright
          linarith [hleft.2, hright.1, hphi.2]
      · exact measurableSet_Ioc.union measurableSet_Ico

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the nonnegative radial factor appearing in the polar form of the planar standard Gaussian. -/
noncomputable def stdGaussianRadialFactor (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal r * ENNReal.ofReal
    ((2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the angular sign-disagreement set for a separation angle `phi`. -/
def angularCosSignDisagreement (phi : ℝ) : Set ℝ :=
  {theta : ℝ | theta ∈ Set.Ioo (-Real.pi) Real.pi ∧
    ((0 < Real.cos theta) ≠ (0 < Real.cos (theta - phi)))}

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the planar standard Gaussian mass of a correlated sign-disagreement cone factors as its radial
mass times the length of the corresponding angular arcs. -/
lemma gaussianRealProd_disagreement_eq_radial_mul_angle
    {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    ((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1))
        {z : ℝ × ℝ |
          (0 < z.1) ≠ (0 < ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2)} =
      (∫⁻ r in Set.Ioi (0 : ℝ), stdGaussianRadialFactor r) *
        ENNReal.ofReal (2 * Real.arccos ρ) := by
  let phi : ℝ := Real.arccos ρ
  let planeEvent : Set (ℝ × ℝ) :=
    {z | (0 < z.1) ≠ (0 < ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2)}
  have hphi : phi ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg ρ, Real.arccos_le_pi ρ⟩
  have hsin : Real.sqrt (1 - ρ ^ 2) = Real.sin phi := by
    dsimp [phi]
    exact (Real.sin_arccos ρ).symm
  have hcos : Real.cos phi = ρ := by
    dsimp [phi]
    exact Real.cos_arccos hρ.1 hρ.2
  have hplane_measurable : MeasurableSet planeEvent := by
    dsimp [planeEvent]
    have hfirst : MeasurableSet {z : ℝ × ℝ | 0 < z.1} :=
      (isOpen_lt continuous_const continuous_fst).measurableSet
    have hsecond : MeasurableSet
        {z : ℝ × ℝ | 0 < ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2} :=
      (isOpen_lt continuous_const
      (continuous_const.mul continuous_fst |>.add
        (continuous_const.mul continuous_snd))).measurableSet
    have hsymm : MeasurableSet
        (({z : ℝ × ℝ | 0 < z.1} \
            {z : ℝ × ℝ | 0 < ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2}) ∪
          ({z : ℝ × ℝ | 0 < ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2} \
            {z : ℝ × ℝ | 0 < z.1})) :=
      (hfirst.diff hsecond).union (hsecond.diff hfirst)
    convert hsymm using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_diff]
    tauto
  have hangle_measurable : MeasurableSet (angularCosSignDisagreement phi) := by
    dsimp [angularCosSignDisagreement]
    have hfirst : MeasurableSet {theta : ℝ | 0 < Real.cos theta} :=
      (isOpen_Ioi.preimage Real.continuous_cos).measurableSet
    have hsecond : MeasurableSet {theta : ℝ | 0 < Real.cos (theta - phi)} :=
      (isOpen_Ioi.preimage
        (Real.continuous_cos.comp (continuous_id.sub continuous_const))).measurableSet
    have hsymm : MeasurableSet
        (({theta : ℝ | 0 < Real.cos theta} \
            {theta : ℝ | 0 < Real.cos (theta - phi)}) ∪
          ({theta : ℝ | 0 < Real.cos (theta - phi)} \
            {theta : ℝ | 0 < Real.cos theta})) :=
      (hfirst.diff hsecond).union (hsecond.diff hfirst)
    refine measurableSet_Ioo.inter ?_
    convert hsymm using 1
    ext theta
    change ((0 < Real.cos theta) ≠ (0 < Real.cos (theta - phi))) ↔
      (0 < Real.cos theta ∧ ¬0 < Real.cos (theta - phi)) ∨
        (0 < Real.cos (theta - phi) ∧ ¬0 < Real.cos theta)
    tauto
  have hpolar_point : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 •
          planeEvent.indicator
            (fun z ↦ ENNReal.ofReal
              ((2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)))
            (polarCoord.symm p) =
        stdGaussianRadialFactor p.1 *
          (angularCosSignDisagreement phi).indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2 := by
    intro p hp
    rcases p with ⟨r, theta⟩
    have hr : 0 < r := hp.1
    have htheta : theta ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
    have hsecond :
        ρ * (polarCoord.symm (r, theta)).1 +
            Real.sqrt (1 - ρ ^ 2) * (polarCoord.symm (r, theta)).2 =
          r * Real.cos (theta - phi) := by
      rw [polarCoord_symm_apply, hsin, Real.cos_sub, hcos]
      ring
    have hsecond' :
        ρ * (r * Real.cos theta) + Real.sqrt (1 - ρ ^ 2) * (r * Real.sin theta) =
          r * Real.cos (theta - phi) := by
      simpa only [polarCoord_symm_apply] using hsecond
    have hradius :
        (polarCoord.symm (r, theta)).1 ^ 2 + (polarCoord.symm (r, theta)).2 ^ 2 = r ^ 2 := by
      rw [polarCoord_symm_apply]
      nlinarith [Real.sin_sq_add_cos_sq theta]
    by_cases hdisagree : (0 < Real.cos theta) ≠ (0 < Real.cos (theta - phi))
    · have hplane : polarCoord.symm (r, theta) ∈ planeEvent := by
        dsimp [planeEvent]
        rw [hsecond']
        simpa [mul_pos_iff, hr.ne', hr] using hdisagree
      have hangle : theta ∈ angularCosSignDisagreement phi := ⟨htheta, hdisagree⟩
      simp only [Set.indicator_of_mem hplane, Set.indicator_of_mem hangle, mul_one,
        smul_eq_mul]
      rw [hradius]
      rfl
    · have hplane : polarCoord.symm (r, theta) ∉ planeEvent := by
        dsimp [planeEvent]
        rw [hsecond']
        simpa [mul_pos_iff, hr.ne', hr] using hdisagree
      have hangle : theta ∉ angularCosSignDisagreement phi := by
        intro hangle
        exact hdisagree hangle.2
      have hplane' : (r * Real.cos theta, r * Real.sin theta) ∉ planeEvent := by
        simpa only [polarCoord_symm_apply] using hplane
      rw [polarCoord_symm_apply, Set.indicator_of_notMem hplane',
        Set.indicator_of_notMem hangle]
      simp
  calc
    ((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)) planeEvent =
        ∫⁻ z in planeEvent, ENNReal.ofReal
          ((2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)) := by
      rw [gaussianRealProd_eq_radialDensity,
        MeasureTheory.withDensity_apply _ hplane_measurable]
    _ = ∫⁻ z, planeEvent.indicator
          (fun z ↦ ENNReal.ofReal
            ((2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2))) z := by
      rw [MeasureTheory.lintegral_indicator hplane_measurable]
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
          planeEvent.indicator
            (fun z ↦ ENNReal.ofReal
              ((2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)))
            (polarCoord.symm p) := by
      symm
      exact lintegral_comp_polarCoord_symm _
    _ = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          stdGaussianRadialFactor p.1 *
            (angularCosSignDisagreement phi).indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2 := by
      rw [polarCoord_target]
      exact MeasureTheory.setLIntegral_congr_fun
        (measurableSet_Ioi.prod measurableSet_Ioo) hpolar_point
    _ = (∫⁻ r in Set.Ioi (0 : ℝ), stdGaussianRadialFactor r) *
          ∫⁻ theta in Set.Ioo (-Real.pi) Real.pi,
            (angularCosSignDisagreement phi).indicator (fun _ ↦ (1 : ℝ≥0∞)) theta := by
      have hradial_measurable : Measurable stdGaussianRadialFactor := by
        unfold stdGaussianRadialFactor
        fun_prop
      have hangular_indicator : Measurable
          ((angularCosSignDisagreement phi).indicator (fun _ ↦ (1 : ℝ≥0∞))) :=
        measurable_const.indicator hangle_measurable
      rw [MeasureTheory.Measure.volume_eq_prod]
      rw [MeasureTheory.setLIntegral_prod]
      · simp_rw [MeasureTheory.lintegral_const_mul _ hangular_indicator]
        rw [MeasureTheory.lintegral_mul_const _ hradial_measurable]
      · exact ((hradial_measurable.comp measurable_fst).mul
          (hangular_indicator.comp measurable_snd)).aemeasurable
    _ = (∫⁻ r in Set.Ioi (0 : ℝ), stdGaussianRadialFactor r) *
          MeasureTheory.volume (angularCosSignDisagreement phi) := by
      congr 1
      calc
        ∫⁻ theta in Set.Ioo (-Real.pi) Real.pi,
            (angularCosSignDisagreement phi).indicator (fun _ ↦ (1 : ℝ≥0∞)) theta =
            ∫⁻ theta,
              (angularCosSignDisagreement phi).indicator (fun _ ↦ (1 : ℝ≥0∞)) theta := by
          exact MeasureTheory.setLIntegral_eq_of_support_subset (by
            intro theta hsupport
            by_contra htheta
            have hangle : theta ∉ angularCosSignDisagreement phi := by
              intro hmem
              exact htheta hmem.1
            exact hsupport (Set.indicator_of_notMem hangle _))
        _ = MeasureTheory.volume (angularCosSignDisagreement phi) := by
          rw [MeasureTheory.lintegral_indicator_const hangle_measurable]
          simp
    _ = (∫⁻ r in Set.Ioi (0 : ℝ), stdGaussianRadialFactor r) *
          ENNReal.ofReal (2 * phi) := by
      have hangle_volume :
          MeasureTheory.volume (angularCosSignDisagreement phi) = ENNReal.ofReal (2 * phi) := by
        simpa only [angularCosSignDisagreement] using angularCosSignDisagreement_volume hphi
      rw [hangle_volume]
    _ = (∫⁻ r in Set.Ioi (0 : ℝ), stdGaussianRadialFactor r) *
          ENNReal.ofReal (2 * Real.arccos ρ) := by
      rfl

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
opposite planar Gaussian coordinates disagree in sign almost surely. -/
lemma gaussianRealProd_oppositeSignDisagreement :
    ((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1))
        {z : ℝ × ℝ | (0 < z.1) ≠ (0 < -(1 : ℝ) * z.1 + Real.sqrt (1 - (-1) ^ 2) * z.2)} =
      1 := by
  have hset :
      {z : ℝ × ℝ | (0 < z.1) ≠ (0 < -(1 : ℝ) * z.1 + Real.sqrt (1 - (-1) ^ 2) * z.2)} =
        ({0} : Set ℝ)ᶜ ×ˢ Set.univ := by
    ext z
    rcases z with ⟨x, y⟩
    simp only [Set.mem_setOf_eq, neg_mul, one_mul, Set.mem_prod, Set.mem_compl_iff,
      Set.mem_singleton_iff, Set.mem_univ, and_true]
    norm_num
    by_cases hzero : x = 0
    · subst x
      simp
    · rcases lt_or_gt_of_ne hzero with hneg | hpos
      · simpa [hneg, hneg.le] using hzero
      · simpa [hpos, hpos.le] using hzero
  have hvariance_ne : (1 : ℝ≥0) ≠ 0 := by norm_num
  have hnoAtoms := ProbabilityTheory.noAtoms_gaussianReal (μ := (0 : ℝ))
    (v := (1 : ℝ≥0)) hvariance_ne
  have hsingleton : ProbabilityTheory.gaussianReal 0 1 ({0} : Set ℝ) = 0 :=
    hnoAtoms.measure_singleton 0
  rw [hset, MeasureTheory.Measure.prod_prod]
  simp [MeasureTheory.measure_compl, hsingleton]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the radial factor in the planar standard Gaussian has mass `(2π)⁻¹`. -/
lemma lintegral_stdGaussianRadialFactor :
    ∫⁻ r in Set.Ioi (0 : ℝ), stdGaussianRadialFactor r =
      ENNReal.ofReal (2 * Real.pi)⁻¹ := by
  have hneg_one : (-(1 : ℝ)) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hfactor := gaussianRealProd_disagreement_eq_radial_mul_angle hneg_one
  rw [gaussianRealProd_oppositeSignDisagreement, Real.arccos_neg_one] at hfactor
  have htwo_pi_pos : 0 < 2 * Real.pi := by positivity
  have hfactor_zero : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr htwo_pi_pos
  have hfactor_top : ENNReal.ofReal (2 * Real.pi) ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    ∫⁻ r in Set.Ioi (0 : ℝ), stdGaussianRadialFactor r =
        (∫⁻ r in Set.Ioi (0 : ℝ), stdGaussianRadialFactor r) *
          ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal (2 * Real.pi))⁻¹ := by
      symm
      exact ENNReal.mul_inv_cancel_right hfactor_zero hfactor_top
    _ = (ENNReal.ofReal (2 * Real.pi))⁻¹ := by rw [← hfactor, one_mul]
    _ = ENNReal.ofReal (2 * Real.pi)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos htwo_pi_pos]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the standard planar Gaussian assigns a correlated sign-disagreement cone the normalized angular
mass `arccos ρ / π`. -/
lemma gaussianRealProd_signDisagreement
    {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    ((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1))
        {z : ℝ × ℝ |
          (0 < z.1) ≠ (0 < ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2)} =
      ENNReal.ofReal (Real.arccos ρ / Real.pi) := by
  rw [gaussianRealProd_disagreement_eq_radial_mul_angle hρ,
    lintegral_stdGaussianRadialFactor]
  have hphi_nonneg : 0 ≤ Real.arccos ρ := Real.arccos_nonneg ρ
  have htwo_pi_nonneg : 0 ≤ 2 * Real.pi := by positivity
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr htwo_pi_nonneg)]
  congr 1
  field_simp [Real.pi_ne_zero]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the two-coordinate standard Gaussian has correlated sign-disagreement probability
`arccos ρ / π`. -/
lemma stdGaussianFinTwo_signDisagreement
    {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))).real
        {z | (0 < z 0) ≠
          (0 < ρ * z 0 + Real.sqrt (1 - ρ ^ 2) * z 1)} =
      Real.arccos ρ / Real.pi := by
  let euclideanEvent : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | (0 < z 0) ≠ (0 < ρ * z 0 + Real.sqrt (1 - ρ ^ 2) * z 1)}
  let functionEvent : Set (Fin 2 → ℝ) :=
    {z | (0 < z 0) ≠ (0 < ρ * z 0 + Real.sqrt (1 - ρ ^ 2) * z 1)}
  let productEvent : Set (ℝ × ℝ) :=
    {z | (0 < z.1) ≠ (0 < ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2)}
  have heuclidean_measurable : MeasurableSet euclideanEvent := by
    dsimp [euclideanEvent]
    have hfirst : MeasurableSet {z : EuclideanSpace ℝ (Fin 2) | 0 < z 0} := by
      exact (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).measurableSet
    have hsecond : MeasurableSet
        {z : EuclideanSpace ℝ (Fin 2) |
          0 < ρ * z 0 + Real.sqrt (1 - ρ ^ 2) * z 1} := by
      exact (isOpen_lt continuous_const
        ((EuclideanSpace.proj 0).continuous.const_mul ρ |>.add
          ((EuclideanSpace.proj 1).continuous.const_mul (Real.sqrt (1 - ρ ^ 2))))).measurableSet
    have hsymm : MeasurableSet
        (({z : EuclideanSpace ℝ (Fin 2) | 0 < z 0} \
            {z : EuclideanSpace ℝ (Fin 2) |
              0 < ρ * z 0 + Real.sqrt (1 - ρ ^ 2) * z 1}) ∪
          ({z : EuclideanSpace ℝ (Fin 2) |
              0 < ρ * z 0 + Real.sqrt (1 - ρ ^ 2) * z 1} \
            {z : EuclideanSpace ℝ (Fin 2) | 0 < z 0})) :=
      (hfirst.diff hsecond).union (hsecond.diff hfirst)
    convert hsymm using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_diff]
    tauto
  have hproduct_measurable : MeasurableSet productEvent := by
    dsimp [productEvent]
    have hfirst : MeasurableSet {z : ℝ × ℝ | 0 < z.1} :=
      (isOpen_Ioi.preimage continuous_fst).measurableSet
    have hsecond : MeasurableSet
        {z : ℝ × ℝ | 0 < ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2} :=
      (isOpen_Ioi.preimage
        (continuous_const.mul continuous_fst |>.add
          (continuous_const.mul continuous_snd))).measurableSet
    have hsymm : MeasurableSet
        (({z : ℝ × ℝ | 0 < z.1} \
            {z : ℝ × ℝ | 0 < ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2}) ∪
          ({z : ℝ × ℝ | 0 < ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2} \
            {z : ℝ × ℝ | 0 < z.1})) :=
      (hfirst.diff hsecond).union (hsecond.diff hfirst)
    convert hsymm using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_diff]
    tauto
  have hpreimage_toLp :
      WithLp.toLp 2 ⁻¹' euclideanEvent = functionEvent := by
    ext z
    simp [euclideanEvent, functionEvent]
  have hpreimage_pair :
      MeasurableEquiv.finTwoArrow ⁻¹' productEvent = functionEvent := by
    ext z
    simp [productEvent, functionEvent, MeasurableEquiv.finTwoArrow]
  have hmeasure :
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)) euclideanEvent =
        ENNReal.ofReal (Real.arccos ρ / Real.pi) := by
    calc
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)) euclideanEvent =
          ((MeasureTheory.Measure.pi fun _ : Fin 2 ↦ ProbabilityTheory.gaussianReal 0 1).map
            (WithLp.toLp 2)) euclideanEvent := by
        rw [ProbabilityTheory.map_pi_eq_stdGaussian]
      _ = (MeasureTheory.Measure.pi fun _ : Fin 2 ↦ ProbabilityTheory.gaussianReal 0 1)
            (WithLp.toLp 2 ⁻¹' euclideanEvent) := by
        rw [MeasureTheory.Measure.map_apply]
        · fun_prop
        · exact heuclidean_measurable
      _ = (MeasureTheory.Measure.pi fun _ : Fin 2 ↦ ProbabilityTheory.gaussianReal 0 1)
            functionEvent := by rw [hpreimage_toLp]
      _ = (MeasureTheory.Measure.pi fun _ : Fin 2 ↦ ProbabilityTheory.gaussianReal 0 1)
            (MeasurableEquiv.finTwoArrow ⁻¹' productEvent) := by rw [hpreimage_pair]
      _ = ((MeasureTheory.Measure.pi fun _ : Fin 2 ↦ ProbabilityTheory.gaussianReal 0 1).map
            MeasurableEquiv.finTwoArrow) productEvent := by
        symm
        rw [MeasureTheory.Measure.map_apply]
        · fun_prop
        · exact hproduct_measurable
      _ = ((ProbabilityTheory.gaussianReal 0 1).prod
            (ProbabilityTheory.gaussianReal 0 1)) productEvent := by
        rw [(MeasureTheory.measurePreserving_finTwoArrow
          (ProbabilityTheory.gaussianReal 0 1)).map_eq]
      _ = ENNReal.ofReal (Real.arccos ρ / Real.pi) := by
        exact gaussianRealProd_signDisagreement hρ
  change (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2)) euclideanEvent).toReal = _
  rw [hmeasure, ENNReal.toReal_ofReal]
  exact div_nonneg (Real.arccos_nonneg ρ) Real.pi_pos.le

/-- Helper for Theorem 10.3: the remaining Gaussian geometry frontier is the pairwise
sign-disagreement probability for two unit columns. -/
lemma gaussianDisagreementProb_eq_arccos_div_pi_of_unitColumns
    (u v : EuclideanSpace ℝ (Fin n))
    (hu : dotProduct u u = 1)
    (hv : dotProduct v v = 1) :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {g | (0 < dotProduct g u) ≠ (0 < dotProduct g v)} =
      Real.arccos (dotProduct u v) / Real.pi := by
  let rho : ℝ := dotProduct u v
  let outputEvent : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | (0 < z 0) ≠ (0 < z 1)}
  let sourceEvent : Set (EuclideanSpace ℝ (Fin n)) :=
    {g | (0 < dotProduct g u) ≠ (0 < dotProduct g v)}
  let correlatedEvent : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | (0 < z 0) ≠
      (0 < rho * z 0 + Real.sqrt (1 - rho ^ 2) * z 1)}
  have houtput_measurable : MeasurableSet outputEvent := by
    dsimp [outputEvent]
    have hfirst : MeasurableSet {z : EuclideanSpace ℝ (Fin 2) | 0 < z 0} := by
      exact (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).measurableSet
    have hsecond : MeasurableSet {z : EuclideanSpace ℝ (Fin 2) | 0 < z 1} := by
      exact (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
    have hsymm : MeasurableSet
        (({z : EuclideanSpace ℝ (Fin 2) | 0 < z 0} \
            {z : EuclideanSpace ℝ (Fin 2) | 0 < z 1}) ∪
          ({z : EuclideanSpace ℝ (Fin 2) | 0 < z 1} \
            {z : EuclideanSpace ℝ (Fin 2) | 0 < z 0})) :=
      (hfirst.diff hsecond).union (hsecond.diff hfirst)
    convert hsymm using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_diff]
    tauto
  have hsource_preimage :
      stdGaussianInnerPairCLM u v ⁻¹' outputEvent = sourceEvent := by
    ext g
    simp [outputEvent, sourceEvent]
  have hcorrelated_preimage :
      stdGaussianCorrelatedPairCLM rho ⁻¹' outputEvent = correlatedEvent := by
    ext z
    simp [outputEvent, correlatedEvent]
  have hu_inner : ⟪u, u⟫_ℝ = 1 := by
    rw [PiLp.inner_apply]
    simpa [dotProduct, pow_two] using hu
  have hv_inner : ⟪v, v⟫_ℝ = 1 := by
    rw [PiLp.inner_apply]
    simpa [dotProduct, pow_two] using hv
  have hu_norm : ‖u‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hu_inner
    nlinarith [norm_nonneg u]
  have hv_norm : ‖v‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hv_inner
    nlinarith [norm_nonneg v]
  have hrho : rho ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [rho, PiLp.inner_apply, dotProduct, mul_comm] using
      (real_inner_mem_Icc_of_norm_eq_one hu_norm hv_norm)
  have hlaw := stdGaussianInnerPair_map_eq_correlatedPair u v hu hv
  -- Push the measurable output event through the equal two-dimensional Gaussian laws.
  calc
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).real sourceEvent =
        ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map
          (stdGaussianInnerPairCLM u v)).real outputEvent := by
      symm
      rw [MeasureTheory.map_measureReal_apply]
      · rw [hsource_preimage]
      · fun_prop
      · exact houtput_measurable
    _ = ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))).map
          (stdGaussianCorrelatedPairCLM rho)).real outputEvent := by
      rw [hlaw]
    _ = (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))).real
          correlatedEvent := by
      rw [MeasureTheory.map_measureReal_apply]
      · rw [hcorrelated_preimage]
      · fun_prop
      · exact houtput_measurable
    _ = Real.arccos rho / Real.pi := stdGaussianFinTwo_signDisagreement hrho
    _ = Real.arccos (dotProduct u v) / Real.pi := by rfl

/-- Helper for Theorem 10.3: after pushing the Gaussian through the sign map, the expected cut
value is an edgewise sum of Boolean disagreement probabilities. -/
lemma gaussianRoundedCutIntegral_eq_weightedDisagreementProbSum
    (w : Sym2 (Fin n) → ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) :
    let signPattern :
        EuclideanSpace ℝ (Fin n) → Fin n → Bool :=
      fun g v ↦ 0 < dotProduct g (fun k ↦ U k v)
    let μ : MeasureTheory.Measure (Fin n → Bool) :=
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map signPattern
    MeasureTheory.integral μ
        (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
          (fun i ↦ if σ i then (1 : ℝ) else 0)) =
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun i j : Fin n ↦
                μ.real {σ | σ i ≠ σ j}, by
                  intro i j
                  change μ.real ({σ : Fin n → Bool | σ i ≠ σ j}) =
                    μ.real {σ : Fin n → Bool | σ j ≠ σ i}
                  congr 1
                  ext σ
                  simp [ne_comm]
            ⟩
            e := by
  classical
  let signPattern :
      EuclideanSpace ℝ (Fin n) → Fin n → Bool :=
    fun g v ↦ 0 < dotProduct g (fun k ↦ U k v)
  let μ : MeasureTheory.Measure (Fin n → Bool) :=
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map signPattern
  let disagreementTerm : Sym2 (Fin n) → ℝ :=
    Sym2.lift
      ⟨fun i j : Fin n ↦ μ.real {σ | σ i ≠ σ j}, by
          intro i j
          change μ.real ({σ : Fin n → Bool | σ i ≠ σ j}) =
            μ.real {σ : Fin n → Bool | σ j ≠ σ i}
          congr 1
          ext σ
          simp [ne_comm]
      ⟩
  have hmain :
      MeasureTheory.integral μ
          (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
            (fun i ↦ if σ i then (1 : ℝ) else 0)) =
        Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
          w e * disagreementTerm e := by
    letI : MeasureTheory.IsFiniteMeasure μ := by infer_instance
    have hInt :
        MeasureTheory.Integrable
          (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
            (fun i ↦ if σ i then (1 : ℝ) else 0)) μ := by
      -- The Boolean codomain is finite, so the rounded-cut value is automatically integrable.
      exact MeasureTheory.Integrable.of_finite
    rw [MeasureTheory.integral_fintype hInt]
    simp_rw [boolPattern_maxCutNodeObjective_eq_disagreementSum, smul_eq_mul]
    -- Exchange the finite sum over sign patterns with the finite sum over edges.
    calc
      Finset.sum Finset.univ (fun σ : Fin n → Bool ↦
          μ.real {σ} *
            Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset
              (fun e ↦
                w e *
                  Sym2.lift
                    ⟨fun i j : Fin n ↦ if σ i = σ j then 0 else 1, by
                        intro i j
                        by_cases hij : σ i = σ j <;> simp [hij, eq_comm]
                    ⟩
                    e)) =
          Finset.sum Finset.univ (fun σ : Fin n → Bool ↦
            Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset (fun e ↦
              μ.real {σ} *
                (w e *
                  Sym2.lift
                    ⟨fun i j : Fin n ↦ if σ i = σ j then 0 else 1, by
                        intro i j
                        by_cases hij : σ i = σ j <;> simp [hij, eq_comm]
                    ⟩
                    e))) := by
        refine Finset.sum_congr rfl ?_
        intro σ _
        rw [Finset.mul_sum]
      _ =
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            Finset.sum Finset.univ (fun σ : Fin n → Bool ↦
              μ.real {σ} *
                (w e *
                  Sym2.lift
                    ⟨fun i j : Fin n ↦ if σ i = σ j then 0 else 1, by
                        intro i j
                        by_cases hij : σ i = σ j <;> simp [hij, eq_comm]
                    ⟩
                    e)) := by
        rw [Finset.sum_comm]
      _ =
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e * Finset.sum Finset.univ (fun σ : Fin n → Bool ↦
                μ.real {σ} *
                  Sym2.lift
                    ⟨fun i j : Fin n ↦ if σ i = σ j then 0 else 1, by
                        intro i j
                        by_cases hij : σ i = σ j <;> simp [hij, eq_comm]
                    ⟩
                    e) := by
        refine Finset.sum_congr rfl ?_
        intro e _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro σ _
        ring
      _ = Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset (fun e ↦
            w e * disagreementTerm e) := by
        refine Finset.sum_congr rfl ?_
        intro e _
        refine Sym2.ind ?_ e
        intro i j
        change
          w s(i, j) *
              (∑ σ : Fin n → Bool, μ.real {σ} * (if σ i = σ j then 0 else 1)) =
            w s(i, j) * μ.real {σ : Fin n → Bool | σ i ≠ σ j}
        congr 1
        -- Collapse the finite Boolean sum back to the pushed-forward disagreement measure.
        calc
          ∑ σ : Fin n → Bool, μ.real {σ} * (if σ i = σ j then 0 else 1) =
              ∑ σ : Fin n → Bool,
                {σ : Fin n → Bool | σ i ≠ σ j}.indicator (fun τ ↦ μ.real {τ}) σ := by
            refine Finset.sum_congr rfl ?_
            intro σ _
            by_cases hij : σ i = σ j <;> simp [Set.indicator, hij]
          _ =
              ∑' σ : Fin n → Bool,
                {σ : Fin n → Bool | σ i ≠ σ j}.indicator (fun τ ↦ μ.real {τ}) σ := by
            rw [tsum_fintype]
          _ = μ.real {σ : Fin n → Bool | σ i ≠ σ j} := by
            have hindicator :
                (∑ σ : Fin n → Bool,
                    {σ : Fin n → Bool | σ i ≠ σ j}.indicator (fun τ ↦ μ.real {τ}) σ) =
                  Finset.sum (Finset.univ.filter fun σ : Fin n → Bool ↦ σ i ≠ σ j)
                    (fun σ ↦ μ.real {σ}) := by
              symm
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl ?_
              intro σ _
              by_cases hij : σ i ≠ σ j <;> simp [Set.indicator, hij]
            have hdisagreement_measurable :
                MeasurableSet {σ : Fin n → Bool | σ i ≠ σ j} := by
              exact (Set.toFinite {σ : Fin n → Bool | σ i ≠ σ j}).measurableSet
            calc
              ∑' σ : Fin n → Bool,
                  {σ : Fin n → Bool | σ i ≠ σ j}.indicator (fun τ ↦ μ.real {τ}) σ =
                  Finset.sum (Finset.univ.filter fun σ : Fin n → Bool ↦ σ i ≠ σ j)
                    (fun σ ↦ μ.real {σ}) := by
                rw [tsum_fintype]
                exact hindicator
              _ = μ.real ((Finset.univ.filter fun σ : Fin n → Bool ↦ σ i ≠ σ j) :
                    Set (Fin n → Bool)) := by
                exact MeasureTheory.sum_measureReal_singleton (μ := μ) _
              _ = μ.real {σ : Fin n → Bool | σ i ≠ σ j} := by
                congr 1
                ext σ
                simp
  change MeasureTheory.integral μ
      (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
        (fun i ↦ if σ i then (1 : ℝ) else 0)) =
    Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
      w e *
        Sym2.lift
          ⟨fun i j : Fin n ↦ μ.real {σ | σ i ≠ σ j}, by
              intro i j
              change μ.real ({σ : Fin n → Bool | σ i ≠ σ j}) =
                μ.real {σ : Fin n → Bool | σ j ≠ σ i}
              congr 1
              ext σ
              simp [ne_comm]
          ⟩
          e
  simpa [disagreementTerm] using hmain

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the expected cut value from Gaussian sign rounding is the weighted `arccos / π` edge sum. -/
lemma gaussianRoundedCutIntegral_eq_weightedArccosSum
    (w : Sym2 (Fin n) → ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ)
    (hUnit : ∀ i, dotProduct (fun k ↦ U k i) (fun k ↦ U k i) = 1) :
    let signPattern :
        EuclideanSpace ℝ (Fin n) → Fin n → Bool :=
      fun g v ↦ 0 < dotProduct g (fun k ↦ U k v)
    let μ : MeasureTheory.Measure (Fin n → Bool) :=
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map signPattern
    MeasureTheory.integral μ
        (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
          (fun i ↦ if σ i then (1 : ℝ) else 0)) =
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun i j : Fin n ↦
                Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
                  intro i j
                  simp [dotProduct_comm]
            ⟩
            e := by
  classical
  let signPattern :
      EuclideanSpace ℝ (Fin n) → Fin n → Bool :=
    fun g v ↦ 0 < dotProduct g (fun k ↦ U k v)
  let μ : MeasureTheory.Measure (Fin n → Bool) :=
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map signPattern
  have hsignPattern_measurable : Measurable signPattern := by
    -- Each Boolean coordinate is the indicator of a measurable half-space.
    refine measurable_pi_lambda _ ?_
    intro v
    refine measurable_to_bool ?_
    have hdot_continuous :
        Continuous (fun g : EuclideanSpace ℝ (Fin n) ↦
          dotProduct g (fun k ↦ U k v)) := by
      fun_prop
    simpa [signPattern, Set.preimage] using
      (isOpen_lt continuous_const hdot_continuous).measurableSet
  have hmain :
      MeasureTheory.integral μ
          (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
            (fun i ↦ if σ i then (1 : ℝ) else 0)) =
        Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
          w e *
            Sym2.lift
              ⟨fun i j : Fin n ↦
                  Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
                    intro i j
                    simp [dotProduct_comm]
              ⟩
              e := by
    calc
      MeasureTheory.integral μ
          (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
            (fun i ↦ if σ i then (1 : ℝ) else 0)) =
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e *
              Sym2.lift
                ⟨fun i j : Fin n ↦
                    μ.real {σ | σ i ≠ σ j}, by
                      intro i j
                      change μ.real ({σ : Fin n → Bool | σ i ≠ σ j}) =
                        μ.real {σ : Fin n → Bool | σ j ≠ σ i}
                      congr 1
                      ext σ
                      simp [ne_comm]
                ⟩
                e := by
        exact gaussianRoundedCutIntegral_eq_weightedDisagreementProbSum (n := n) w U
      _ =
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e *
              Sym2.lift
                ⟨fun i j : Fin n ↦
                    Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
                      intro i j
                      simp [dotProduct_comm]
                ⟩
                e := by
        refine Finset.sum_congr rfl ?_
        intro e _
        refine Sym2.ind ?_ e
        intro i j
        change
          w s(i, j) * μ.real {σ : Fin n → Bool | σ i ≠ σ j} =
            w s(i, j) *
              (Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi)
        congr 1
        let uCol : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun k ↦ U k i)
        let vCol : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun k ↦ U k j)
        have hdisagreement_measurable :
            MeasurableSet {σ : Fin n → Bool | σ i ≠ σ j} := by
          exact (Set.toFinite {σ : Fin n → Bool | σ i ≠ σ j}).measurableSet
        have huCol : dotProduct uCol uCol = 1 := by
          simpa [uCol] using hUnit i
        have hvCol : dotProduct vCol vCol = 1 := by
          simpa [vCol] using hUnit j
        have hpreimage :
            signPattern ⁻¹' {σ : Fin n → Bool | σ i ≠ σ j} =
              {g : EuclideanSpace ℝ (Fin n) |
                (0 < dotProduct g (fun k ↦ U k i)) ≠
                  (0 < dotProduct g (fun k ↦ U k j))} := by
          ext g
          simp [signPattern]
        -- Push the disagreement event back through the sign map and invoke the pairwise lemma.
        calc
          μ.real {σ : Fin n → Bool | σ i ≠ σ j} =
              (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).real
                (signPattern ⁻¹' {σ : Fin n → Bool | σ i ≠ σ j}) := by
            simpa [μ] using
              (MeasureTheory.map_measureReal_apply
                (μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)))
                hsignPattern_measurable
                (s := {σ : Fin n → Bool | σ i ≠ σ j}) hdisagreement_measurable)
          _ =
              (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).real
                {g : EuclideanSpace ℝ (Fin n) |
                  (0 < dotProduct g (fun k ↦ U k i)) ≠
                    (0 < dotProduct g (fun k ↦ U k j))} := by
            rw [hpreimage]
          _ =
              Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi := by
            simpa [uCol, vCol] using
              (gaussianDisagreementProb_eq_arccos_div_pi_of_unitColumns
                (n := n) uCol vCol huCol hvCol)
  change MeasureTheory.integral μ
      (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
        (fun i ↦ if σ i then (1 : ℝ) else 0)) =
    Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
      w e *
        Sym2.lift
          ⟨fun i j : Fin n ↦
              Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
                intro i j
                simp [dotProduct_comm]
          ⟩
          e
  exact hmain

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the weighted `arccos / π` sum for unit columns is bounded by the maximum cut value. -/
lemma weightedArccosSum_le_maxCutIntegerValue_of_unitColumnFamily
    (w : Sym2 (Fin n) → ℝ) (U : Matrix (Fin n) (Fin n) ℝ)
    (hUnit : ∀ i, dotProduct (fun k ↦ U k i) (fun k ↦ U k i) = 1) :
    (Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
      w e *
        Sym2.lift
          ⟨fun i j : Fin n ↦
              Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
                intro i j
                simp [dotProduct_comm]
          ⟩
          e) ≤
      max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
  -- Package the Gaussian sign rounding into a probability measure on Boolean cuts.
  let signPattern :
      EuclideanSpace ℝ (Fin n) → Fin n → Bool :=
    fun g v ↦ 0 < dotProduct g (fun k ↦ U k v)
  let μ : MeasureTheory.Measure (Fin n → Bool) :=
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map signPattern
  have hsignPattern_measurable : Measurable signPattern := by
    refine measurable_pi_lambda _ ?_
    intro v
    refine measurable_to_bool ?_
    have hdot_continuous :
        Continuous (fun g : EuclideanSpace ℝ (Fin n) ↦
          dotProduct g (fun k ↦ U k v)) := by
      fun_prop
    simpa [signPattern, Set.preimage] using
      (isOpen_lt continuous_const hdot_continuous).measurableSet
  have hμ : μ Set.univ = 1 := by
    -- The pushforward of the standard Gaussian is still a probability measure.
    dsimp [μ]
    rw [MeasureTheory.Measure.map_apply hsignPattern_measurable MeasurableSet.univ]
    simp
  have hAverage :
      MeasureTheory.integral μ
          (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
            (fun i ↦ if σ i then (1 : ℝ) else 0)) ≤
        max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w :=
    averageBooleanCut_le_maxCutIntegerValue (n := n) w μ hμ
  -- Rewrite the rounded-cut expectation as the weighted `arccos / π` sum.
  simpa [μ, signPattern] using
    (gaussianRoundedCutIntegral_eq_weightedArccosSum (n := n) w U hUnit).symm.le.trans hAverage

/-- Helper for Theorem 10.3: the normalized value of `arccos (-1 / 2)` is `2 / 3`. -/
lemma arccos_neg_half_div_pi_eq_two_thirds :
    Real.arccos (-(1 : ℝ) / 2) / Real.pi = (2 : ℝ) / 3 := by
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 : ℝ) / 2 := by
    calc
      Real.cos (2 * Real.pi / 3) = Real.cos (Real.pi - Real.pi / 3) := by congr 1; ring
      _ = -Real.cos (Real.pi / 3) := by rw [Real.cos_pi_sub]
      _ = -(1 : ℝ) / 2 := by rw [Real.cos_pi_div_three]; norm_num
  have harccos :
      Real.arccos (-(1 : ℝ) / 2) = 2 * Real.pi / 3 := by
    refine Real.arccos_eq_of_eq_cos ?_ ?_ hcos.symm
    · positivity
    · have hpi_pos : 0 < Real.pi := Real.pi_pos
      nlinarith
  rw [harccos]
  field_simp [Real.pi_ne_zero]

/-- Helper for Theorem 10.3: the normalized value of `arccos (1 / 2)` is `1 / 3`. -/
lemma arccos_half_div_pi_eq_one_third :
    Real.arccos ((1 : ℝ) / 2) / Real.pi = (1 : ℝ) / 3 := by
  have harccos :
      Real.arccos ((1 : ℝ) / 2) = Real.pi / 3 := by
    refine Real.arccos_eq_of_eq_cos ?_ ?_ ?_
    · positivity
    · have hpi_pos : 0 < Real.pi := Real.pi_pos
      nlinarith
    · simp
  rw [harccos]
  field_simp [Real.pi_ne_zero]

/-- Helper for Theorem 10.3: on `[0, π / 2]`, the cosine graph lies above the chord from
`(0, 1)` to `(π / 2, 0)`. -/
lemma cos_ge_one_sub_two_mul_div_pi
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    1 - 2 * θ / Real.pi ≤ Real.cos θ := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    Real.one_sub_mul_le_cos hθ.1 hθ.2

/-- Helper for Theorem 10.3: on `[0, π / 3]`, the cosine graph lies above the chord from
`(0, 1)` to `(π / 3, 1 / 2)`. -/
lemma cos_ge_one_sub_three_mul_div_two_pi
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 3)) :
    1 - 3 * θ / (2 * Real.pi) ≤ Real.cos θ := by
  have hconcave :
      ConcaveOn ℝ (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) Real.cos :=
    strictConcaveOn_cos_Icc.concaveOn
  have hzero : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hthird : Real.pi / 3 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hb_nonneg : 0 ≤ 3 * θ / Real.pi := by
    exact div_nonneg (by nlinarith [hθ.1]) Real.pi_pos.le
  have ha_nonneg : 0 ≤ 1 - 3 * θ / Real.pi := by
    have hratio_le : 3 * θ / Real.pi ≤ 1 := by
      refine (div_le_iff₀ Real.pi_pos).2 ?_
      nlinarith [hθ.2]
    linarith
  have hab : (1 - 3 * θ / Real.pi) + 3 * θ / Real.pi = 1 := by
    ring
  have hcos :=
    hconcave.2 hzero hthird ha_nonneg hb_nonneg hab
  have hpoint :
      (1 - 3 * θ / Real.pi) * (0 : ℝ) +
          (3 * θ / Real.pi) * (Real.pi / 3) =
        θ := by
    field_simp [Real.pi_ne_zero]
    ring
  have hline :
      (1 - 3 * θ / Real.pi) * Real.cos 0 +
          (3 * θ / Real.pi) * Real.cos (Real.pi / 3) =
        1 - 3 * θ / (2 * Real.pi) := by
    rw [Real.cos_zero, Real.cos_pi_div_three]
    field_simp [Real.pi_ne_zero]
    ring
  -- The concavity inequality is exactly the chord bound after identifying the affine parameter.
  calc
    1 - 3 * θ / (2 * Real.pi) =
        (1 - 3 * θ / Real.pi) * Real.cos 0 +
          (3 * θ / Real.pi) * Real.cos (Real.pi / 3) := by
      symm
      exact hline
    _ ≤ Real.cos ((1 - 3 * θ / Real.pi) * (0 : ℝ) +
          (3 * θ / Real.pi) * (Real.pi / 3)) := hcos
    _ = Real.cos θ := by rw [hpoint]

/-- Helper for Theorem 10.3: `Real.arccos` is convex on the left half-interval `[-1, 0]`. -/
lemma arccos_convexOn_nonpos : ConvexOn ℝ (Set.Icc (-1 : ℝ) 0) Real.arccos := by
  -- Promote monotonicity of the explicit derivative on `(-1, 0)` to convexity on `[-1, 0]`.
  refine MonotoneOn.convexOn_of_deriv (D := Set.Icc (-1 : ℝ) 0) (convex_Icc (-1 : ℝ) 0)
    Real.continuous_arccos.continuousOn ?_ ?_
  · intro x hx
    have hx' : x ∈ Set.Ioo (-1 : ℝ) 0 := by simpa using hx
    have hdiff : DifferentiableAt ℝ Real.arccos x := by
      exact Real.differentiableAt_arccos.2 ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    exact hdiff.differentiableWithinAt
  · intro x hx y hy hxy
    have hx' : x ∈ Set.Ioo (-1 : ℝ) 0 := by simpa using hx
    have hy' : y ∈ Set.Ioo (-1 : ℝ) 0 := by simpa using hy
    have hsub : 1 - x ^ 2 ≤ 1 - y ^ 2 := by
      nlinarith [hx'.2, hy'.2, hxy]
    have hx_pos : 0 < 1 - x ^ 2 := by
      nlinarith [hx'.1, hx'.2]
    have hy_pos : 0 < 1 - y ^ 2 := by
      nlinarith [hy'.1, hy'.2]
    have hsqrt :
        Real.sqrt (1 - x ^ 2) ≤ Real.sqrt (1 - y ^ 2) := by
      exact Real.sqrt_le_sqrt hsub
    have hsqrt_pos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hx_pos
    have hrecip :
        1 / Real.sqrt (1 - y ^ 2) ≤ 1 / Real.sqrt (1 - x ^ 2) := by
      exact one_div_le_one_div_of_le hsqrt_pos hsqrt
    simpa [Real.deriv_arccos] using neg_le_neg hrecip

/-- Helper for Theorem 10.3: on `[-1, 0]`, every tangent line to `Real.arccos` at an interior
point is a global lower bound. -/
lemma arccos_tangentLowerBound_nonpos
    {x₀ t : ℝ} (hx₀ : x₀ ∈ Set.Ioo (-1 : ℝ) 0) (ht : t ∈ Set.Icc (-1 : ℝ) 0) :
    Real.arccos x₀ - (1 / Real.sqrt (1 - x₀ ^ 2)) * (t - x₀) ≤
      Real.arccos t := by
  let S : Set ℝ := Set.Icc (-1 : ℝ) 0
  have hx₀S : x₀ ∈ S := ⟨hx₀.1.le, hx₀.2.le⟩
  have hderiv : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - x₀ ^ 2))) x₀ := by
    exact Real.hasDerivAt_arccos (by linarith [hx₀.1]) (by linarith [hx₀.2])
  rcases lt_trichotomy t x₀ with htlt | rfl | hxt
  · have hslope :
        slope Real.arccos t x₀ ≤ -(1 / Real.sqrt (1 - x₀ ^ 2)) := by
      exact arccos_convexOn_nonpos.slope_le_of_hasDerivAt
        (x := t) (y := x₀) ht hx₀S htlt hderiv
    have hmul :
        (Real.arccos x₀ - Real.arccos t) / (x₀ - t) ≤
          -(1 / Real.sqrt (1 - x₀ ^ 2)) := by
      simpa [slope_def_field] using hslope
    have hpos : 0 < x₀ - t := sub_pos.mpr htlt
    have hmul' := mul_le_mul_of_nonneg_right hmul hpos.le
    have hmain :
        Real.arccos x₀ - Real.arccos t ≤
          (-(1 / Real.sqrt (1 - x₀ ^ 2))) * (x₀ - t) := by
      simpa [div_eq_mul_inv, hpos.ne', mul_comm, mul_left_comm, mul_assoc] using hmul'
    linarith
  · simp
  · have hslope :
        -(1 / Real.sqrt (1 - x₀ ^ 2)) ≤ slope Real.arccos x₀ t := by
      exact arccos_convexOn_nonpos.le_slope_of_hasDerivAt
        (x := x₀) (y := t) hx₀S ht hxt hderiv
    have hmul :
        -(1 / Real.sqrt (1 - x₀ ^ 2)) ≤
          (Real.arccos t - Real.arccos x₀) / (t - x₀) := by
      simpa [slope_def_field] using hslope
    have hpos : 0 < t - x₀ := sub_pos.mpr hxt
    have hmul' := mul_le_mul_of_nonneg_right hmul hpos.le
    have hmain :
        (-(1 / Real.sqrt (1 - x₀ ^ 2))) * (t - x₀) ≤
          Real.arccos t - Real.arccos x₀ := by
      simpa [div_eq_mul_inv, hpos.ne', mul_comm, mul_left_comm, mul_assoc] using hmul'
    linarith

/-- Helper for Theorem 10.3: on `[-1 / 2, 0]`, the tangent line at `t = -1 / 2` already gives a
strict lower bound stronger than the textbook coefficient. -/
lemma gwArccosMiddleNegativeStrictBaseBound
    {t : ℝ} (ht : t ∈ Set.Icc (-(1 : ℝ) / 2) 0) :
    ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
      Real.arccos t / Real.pi := by
  have ht_nonpos : t ∈ Set.Icc (-1 : ℝ) 0 := ⟨by nlinarith [ht.1], ht.2⟩
  have htan :=
    arccos_tangentLowerBound_nonpos
      (x₀ := -(1 : ℝ) / 2)
      (by constructor <;> norm_num)
      ht_nonpos
  have hsqrt_three :
      Real.sqrt (1 - (-(1 : ℝ) / 2) ^ 2) = Real.sqrt 3 / 2 := by
    rw [show 1 - (-(1 : ℝ) / 2) ^ 2 = (3 : ℝ) / 4 by norm_num]
    rw [Real.sqrt_div (by positivity)]
    have hsqrt_four : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    rw [hsqrt_four]
  have hline :
      (Real.arccos (-(1 : ℝ) / 2) -
          (1 / Real.sqrt (1 - (-(1 : ℝ) / 2) ^ 2)) * (t - (-(1 : ℝ) / 2))) / Real.pi =
        (2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * (t + (1 : ℝ) / 2) := by
    have hsqrt_three_ne : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.2 (by positivity)
    rw [sub_div, arccos_neg_half_div_pi_eq_two_thirds, hsqrt_three]
    field_simp [Real.pi_ne_zero, hsqrt_three_ne]
    ring
  have hline_lt :
      ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
        (2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * (t + (1 : ℝ) / 2) := by
    have hslope_nonneg :
        0 ≤ ((87856 : ℝ) / 100000) / 2 - 2 / (Real.pi * Real.sqrt 3) := by
      have hsqrt_three_gt : (5 : ℝ) / 3 < Real.sqrt 3 := by
        have hsq : ((5 : ℝ) / 3) ^ 2 < 3 := by norm_num
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity), Real.sqrt_nonneg 3]
      have hden_gt : (5 : ℝ) < Real.pi * Real.sqrt 3 := by
        nlinarith [Real.pi_gt_three, hsqrt_three_gt]
      have hden_pos : 0 < Real.pi * Real.sqrt 3 := by positivity
      have hfrac_lt : 2 / (Real.pi * Real.sqrt 3) < (2 : ℝ) / 5 := by
        refine (div_lt_iff₀ hden_pos).2 ?_
        nlinarith
      nlinarith
    have hleft :
        ((87856 : ℝ) / 100000) * ((1 - (-(1 : ℝ) / 2)) / 2) <
          (2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * ((-(1 : ℝ) / 2) + (1 : ℝ) / 2) := by
      norm_num
    have hmono :
        ((87856 : ℝ) / 100000) * ((1 - t) / 2) -
            ((2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * (t + (1 : ℝ) / 2)) ≤
          ((87856 : ℝ) / 100000) * ((1 - (-(1 : ℝ) / 2)) / 2) -
            ((2 : ℝ) / 3 -
              (2 / (Real.pi * Real.sqrt 3)) * ((-(1 : ℝ) / 2) + (1 : ℝ) / 2)) := by
      have ht' : -(1 : ℝ) / 2 ≤ t := ht.1
      nlinarith
    linarith
  -- Divide the tangent inequality by `π` and compare it to the target linear form.
  have htan_div :
      (Real.arccos (-(1 : ℝ) / 2) -
          (1 / Real.sqrt (1 - (-(1 : ℝ) / 2) ^ 2)) * (t - (-(1 : ℝ) / 2))) / Real.pi ≤
        Real.arccos t / Real.pi := by
    exact div_le_div_of_nonneg_right htan Real.pi_pos.le
  calc
    ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
        (2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * (t + (1 : ℝ) / 2) := hline_lt
    _ =
        (Real.arccos (-(1 : ℝ) / 2) -
          (1 / Real.sqrt (1 - (-(1 : ℝ) / 2) ^ 2)) * (t - (-(1 : ℝ) / 2))) / Real.pi := by
      symm
      exact hline
    _ ≤ Real.arccos t / Real.pi := htan_div

/-- Helper for Theorem 10.3: on the right interval `[1 / 2, 1]`, the normalized arccos value
dominates the stronger coefficient `4 / 3`. -/
lemma gwArccosRightInterval_margin
    {t : ℝ} (ht : t ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    ((4 : ℝ) / 3) * ((1 - t) / 2) ≤ Real.arccos t / Real.pi := by
  have ht_mem : t ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · nlinarith [ht.1]
    · exact ht.2
  have harccos_half :
      Real.arccos ((1 : ℝ) / 2) = Real.pi / 3 := by
    refine Real.arccos_eq_of_eq_cos ?_ ?_ ?_
    · positivity
    · nlinarith [Real.pi_pos]
    · simp
  have hθ :
      Real.arccos t ∈ Set.Icc (0 : ℝ) (Real.pi / 3) := by
    constructor
    · exact Real.arccos_nonneg t
    · calc
        Real.arccos t ≤ Real.arccos ((1 : ℝ) / 2) := Real.arccos_le_arccos ht.1
        _ = Real.pi / 3 := harccos_half
  have hChord :
      1 - 3 * Real.arccos t / (2 * Real.pi) ≤ t := by
    -- Route correction: rewrite through `θ := arccos t` and use the chord bound for `cos`.
    simpa [Real.cos_arccos ht_mem.1 ht_mem.2] using
      (cos_ge_one_sub_three_mul_div_two_pi (θ := Real.arccos t) hθ)
  -- Rearranging the chord inequality gives the strengthened right-end coefficient `4 / 3`.
  have hscaled : 2 * (1 - t) ≤ (3 * Real.arccos t) / Real.pi := by
    have hstep : 1 - t ≤ (3 * Real.arccos t) / (2 * Real.pi) := by
      linarith [hChord]
    calc
      2 * (1 - t) ≤ 2 * ((3 * Real.arccos t) / (2 * Real.pi)) := by
        gcongr
      _ = (3 * Real.arccos t) / Real.pi := by
        field_simp [Real.pi_ne_zero]
  have hmain : (2 * (1 - t)) / 3 ≤ Real.arccos t / Real.pi := by
    refine (div_le_iff₀ (show (0 : ℝ) < 3 by norm_num)).2 ?_
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  convert hmain using 1
  all_goals ring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the rational quartic controlling the tight central part of the scalar arccos estimate is positive
on `[1 / 2, 442 / 625]`. -/
lemma gwArccosCentralPolynomial_pos
    {x : ℝ} (hx : x ∈ Set.Icc ((1 : ℝ) / 2) (442 / 625)) :
    let p : ℝ := 3141592 / 1000000
    let A : ℝ := 3 / 4 - ((87856 : ℝ) / 100000) * (1 + x) / 2
    0 < (1 + p * A) ^ 2 * x ^ 2 - (1 - p * A) ^ 2 * (1 - x ^ 2) := by
  -- On each short interval, use the positive Bernstein coefficients of the quartic.
  dsimp
  by_cases hx_two_thirds : x ≤ (2 : ℝ) / 3
  · let y : ℝ := 6 * (x - 1 / 2)
    have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [y]
      constructor <;> nlinarith [hx.1]
    have hbernstein :
      (1 + (3141592 / 1000000 : ℝ) *
          (3 / 4 - (87856 / 100000 : ℝ) * (1 + x) / 2)) ^ 2 * x ^ 2 -
          (1 - (3141592 / 1000000 : ℝ) *
          (3 / 4 - (87856 / 100000 : ℝ) * (1 + x) / 2)) ^ 2 * (1 - x ^ 2) =
        (612020242732561871 / 19531250000000000000 : ℝ) * (1 - y) ^ 4 +
        4 * (1344238859713322281 / 58593750000000000000 : ℝ) * y * (1 - y) ^ 3 +
        6 * (752584837299763039 / 58593750000000000000 : ℝ) * y ^ 2 * (1 - y) ^ 2 +
        4 * (95533239753748261 / 26367187500000000000 : ℝ) * y ^ 3 * (1 - y) +
        (1578831004346111 / 1977539062500000000 : ℝ) * y ^ 4 := by
      dsimp [y]
      ring
    rw [hbernstein]
    by_cases hy_one : y = 1
    · simp [hy_one]
    · have hy_lt_one : y < 1 := lt_of_le_of_ne hy.2 hy_one
      have hy_gap_pos : 0 < 1 - y := sub_pos.mpr hy_lt_one
      have hy_nonneg : 0 ≤ y := hy.1
      positivity
  · by_cases hx_sixty_nine : x ≤ (69 : ℝ) / 100
    · let y : ℝ := (300 / 7 : ℝ) * (x - 2 / 3)
      have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
        dsimp [y]
        constructor <;> nlinarith [hx_two_thirds]
      have hbernstein :
        (1 + (3141592 / 1000000 : ℝ) *
            (3 / 4 - (87856 / 100000 : ℝ) * (1 + x) / 2)) ^ 2 * x ^ 2 -
            (1 - (3141592 / 1000000 : ℝ) *
            (3 / 4 - (87856 / 100000 : ℝ) * (1 + x) / 2)) ^ 2 * (1 - x ^ 2) =
          (1578831004346111 / 1977539062500000000 : ℝ) * (1 - y) ^ 4 +
          4 * (531178885026806533 / 1318359375000000000000 : ℝ) * y * (1 - y) ^ 3 +
          6 * (19453176549427091671 / 146484375000000000000000 : ℝ) * y ^ 2 * (1 - y) ^ 2 +
          4 * (3907683072952317963 / 1220703125000000000000000 : ℝ) * y ^ 3 * (1 - y) +
          (3709232403887551848201 / 122070312500000000000000000 : ℝ) * y ^ 4 := by
        dsimp [y]
        ring
      rw [hbernstein]
      by_cases hy_one : y = 1
      · simp [hy_one]
      · have hy_lt_one : y < 1 := lt_of_le_of_ne hy.2 hy_one
        have hy_gap_pos : 0 < 1 - y := sub_pos.mpr hy_lt_one
        have hy_nonneg : 0 ≤ y := hy.1
        positivity
    · let y : ℝ := (62500 / 1075 : ℝ) * (x - 69 / 100)
      have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
        dsimp [y]
        constructor <;> nlinarith [hx_sixty_nine, hx.2]
      have hbernstein :
        (1 + (3141592 / 1000000 : ℝ) *
            (3 / 4 - (87856 / 100000 : ℝ) * (1 + x) / 2)) ^ 2 * x ^ 2 -
            (1 - (3141592 / 1000000 : ℝ) *
            (3 / 4 - (87856 / 100000 : ℝ) * (1 + x) / 2)) ^ 2 * (1 - x ^ 2) =
          (3709232403887551848201 / 122070312500000000000000000 : ℝ) * (1 - y) ^ 4 +
          4 * (38471340683597530718943 / 762939453125000000000000000 : ℝ) * y * (1 - y) ^ 3 +
          6 * (2968931672240166148487421 / 19073486328125000000000000000 : ℝ) *
              y ^ 2 * (1 - y) ^ 2 +
          4 * (21016709926537112587857889 / 59604644775390625000000000000 : ℝ) * y ^ 3 * (1 - y) +
          (60359979010941260269813263 / 93132257461547851562500000000 : ℝ) * y ^ 4 := by
        dsimp [y]
        ring
      rw [hbernstein]
      by_cases hy_one : y = 1
      · simp [hy_one]
      · have hy_lt_one : y < 1 := lt_of_le_of_ne hy.2 hy_one
        have hy_gap_pos : 0 < 1 - y := sub_pos.mpr hy_lt_one
        have hy_nonneg : 0 ≤ y := hy.1
        positivity

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean:
the far-left subinterval satisfies the strict scalar arccos bound by the tangent line at
`-√2 / 2`. -/
lemma gwArccosFarLeftIntervalStrictBaseBound
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) (-(1 : ℝ) / 2))
    (hfar : Real.sqrt 2 / 2 < -t) :
    ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
      Real.arccos t / Real.pi := by
  let x : ℝ := -t
  have hx_lower : Real.sqrt 2 / 2 < x := by simpa [x] using hfar
  have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  have hsqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 htwo_pos
  have hsqrt_two_nonneg : 0 ≤ Real.sqrt 2 := hsqrt_two_pos.le
  have hsqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt htwo_nonneg
  have hx₀ : -(Real.sqrt 2 / 2) ∈ Set.Ioo (-1 : ℝ) 0 := by
    have hsqrt_two_lt_two : Real.sqrt 2 < 2 := by
      nlinarith only [hsqrt_two_sq, hsqrt_two_nonneg]
    constructor
    · nlinarith only [hsqrt_two_lt_two]
    · exact neg_neg_of_pos (div_pos hsqrt_two_pos htwo_pos)
  have hneg_half_nonpos : (-(1 : ℝ) / 2) ≤ 0 := by norm_num
  have ht_nonpos : t ∈ Set.Icc (-1 : ℝ) 0 :=
    ⟨ht.1, ht.2.trans hneg_half_nonpos⟩
  have htan := arccos_tangentLowerBound_nonpos hx₀ ht_nonpos
  have hsqrt_half :
      Real.sqrt (1 - (-(Real.sqrt 2 / 2)) ^ 2) = Real.sqrt 2 / 2 := by
    have hinside : 1 - (-(Real.sqrt 2 / 2)) ^ 2 = (1 : ℝ) / 2 := by
      nlinarith only [hsqrt_two_sq]
    have hhalf_sq : (1 : ℝ) / 2 = (Real.sqrt 2 / 2) ^ 2 := by
      nlinarith only [hsqrt_two_sq]
    have hhalf_nonneg : 0 ≤ Real.sqrt 2 / 2 := by positivity
    rw [hinside, hhalf_sq, Real.sqrt_sq hhalf_nonneg]
  have harccos_sqrt :
      Real.arccos (-(Real.sqrt 2 / 2)) = 3 * Real.pi / 4 := by
    rw [Real.arccos_neg]
    have hsqrt_mem : Real.sqrt 2 / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> nlinarith
    have hbase : Real.arccos (Real.sqrt 2 / 2) = Real.pi / 4 := by
      have hangle_nonneg : 0 ≤ Real.pi / 4 := by positivity
      have hangle_le_pi : Real.pi / 4 ≤ Real.pi := by nlinarith [Real.pi_pos]
      refine Real.arccos_eq_of_eq_cos hangle_nonneg hangle_le_pi ?_
      simp
    rw [hbase]
    ring
  have hsqrt_two_lower : (1414213 : ℝ) / 1000000 < Real.sqrt 2 := by
    nlinarith
  have hpi_upper := Real.pi_lt_d6
  have hpi_upper' : Real.pi < (3141593 : ℝ) / 1000000 := by
    norm_num at hpi_upper ⊢
    exact hpi_upper
  have hsqrt_two_upper : Real.sqrt 2 < (1414214 : ℝ) / 1000000 := by
    nlinarith only [hsqrt_two_sq, hsqrt_two_nonneg]
  have hpi_sqrt_upper :
      Real.pi * Real.sqrt 2 <
        ((3141593 : ℝ) / 1000000) * ((1414214 : ℝ) / 1000000) := by
    have hfirst :
        Real.pi * Real.sqrt 2 <
          ((3141593 : ℝ) / 1000000) * Real.sqrt 2 :=
      mul_lt_mul_of_pos_right hpi_upper' hsqrt_two_pos
    have hsecond :
        ((3141593 : ℝ) / 1000000) * Real.sqrt 2 <
          ((3141593 : ℝ) / 1000000) * ((1414214 : ℝ) / 1000000) := by
      have hpi_rational_pos : (0 : ℝ) < 3141593 / 1000000 := by norm_num
      exact mul_lt_mul_of_pos_left hsqrt_two_upper hpi_rational_pos
    exact hfirst.trans hsecond
  have hcoefficient_neg :
      (351424 : ℝ) * Real.pi * Real.sqrt 2 - 1600000 < 0 := by
    nlinarith only [hpi_sqrt_upper]
  have ht_lt : t < -(Real.sqrt 2 / 2) := by linarith only [hx_lower]
  have hlinear_gain :
      (-(Real.sqrt 2 / 2)) *
          ((351424 : ℝ) * Real.pi * Real.sqrt 2 - 1600000) <
        t * ((351424 : ℝ) * Real.pi * Real.sqrt 2 - 1600000) :=
    mul_lt_mul_of_neg_right ht_lt hcoefficient_neg
  have hbase_factor_pos :
      0 < (248576 : ℝ) * Real.sqrt 2 - 351424 := by
    nlinarith only [hsqrt_two_lower]
  have hbase_product_pos :
      0 < Real.pi * ((248576 : ℝ) * Real.sqrt 2 - 351424) :=
    mul_pos Real.pi_pos hbase_factor_pos
  have hsqrt_two_sq_pi :
      Real.pi * (Real.sqrt 2) ^ 2 = Real.pi * 2 :=
    congrArg (fun y : ℝ ↦ Real.pi * y) hsqrt_two_sq
  have hscaled_eq :
      100000 * 2 *
            (3 * Real.pi * Real.sqrt 2 - 4 * (t * 2 - -Real.sqrt 2)) -
          87856 * (1 - t) * Real.pi * 4 * Real.sqrt 2 =
        Real.pi * ((248576 : ℝ) * Real.sqrt 2 - 351424) +
          (t * ((351424 : ℝ) * Real.pi * Real.sqrt 2 - 1600000) -
            (-(Real.sqrt 2 / 2)) *
              ((351424 : ℝ) * Real.pi * Real.sqrt 2 - 1600000)) := by
    nlinarith only [hsqrt_two_sq_pi]
  have hscaled_pos :
      0 <
        100000 * 2 *
            (3 * Real.pi * Real.sqrt 2 - 4 * (t * 2 - -Real.sqrt 2)) -
          87856 * (1 - t) * Real.pi * 4 * Real.sqrt 2 := by
    rw [hscaled_eq]
    exact add_pos hbase_product_pos (sub_pos.mpr hlinear_gain)
  have hline_strict :
      ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
        (Real.arccos (-(Real.sqrt 2 / 2)) -
          (1 / Real.sqrt (1 - (-(Real.sqrt 2 / 2)) ^ 2)) *
            (t - (-(Real.sqrt 2 / 2)))) / Real.pi := by
    rw [harccos_sqrt, hsqrt_half]
    have hpi_pos := Real.pi_pos
    field_simp [Real.pi_ne_zero, ne_of_gt hsqrt_two_pos]
    nlinarith only [hscaled_pos]
  have htan_div :
      (Real.arccos (-(Real.sqrt 2 / 2)) -
          (1 / Real.sqrt (1 - (-(Real.sqrt 2 / 2)) ^ 2)) *
            (t - (-(Real.sqrt 2 / 2)))) / Real.pi ≤ Real.arccos t / Real.pi :=
    div_le_div_of_nonneg_right htan Real.pi_pos.le
  exact hline_strict.trans_le htan_div

/-- Helper for Theorem 10.3: the numerically tight left interval `[-1, -1 / 2]` still satisfies
the textbook scalar lower bound. -/
lemma gwArccosLeftIntervalStrictBaseBound
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) (-(1 : ℝ) / 2)) :
    ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
      Real.arccos t / Real.pi := by
  -- Write `x = -t`; the central and far-left ranges use different stable lower bounds.
  let x : ℝ := -t
  have hx : x ∈ Set.Icc ((1 : ℝ) / 2) 1 := by
    dsimp [x]
    constructor <;> linarith [ht.1, ht.2]
  by_cases hx_central : x ≤ Real.sqrt 2 / 2
  · let s : ℝ := Real.sqrt (1 - x ^ 2)
    let q : ℝ := (s - x) / (s + x)
    let p : ℝ := 3141592 / 1000000
    let A : ℝ := 3 / 4 - ((87856 : ℝ) / 100000) * (1 + x) / 2
    have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
    have hsqrt_two_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt htwo_nonneg
    have hx_lt_one : x < 1 := by
      have hsqrt_two_lt_two : Real.sqrt 2 < 2 := by
        nlinarith
      nlinarith
    have hx_pos : 0 < x := by linarith [hx.1]
    have hs_sq : s ^ 2 = 1 - x ^ 2 := by
      dsimp [s]
      rw [Real.sq_sqrt]
      nlinarith [hx.1, hx.2]
    have hs_pos : 0 < s := by
      dsimp [s]
      refine Real.sqrt_pos.mpr ?_
      nlinarith [hx.1, hx_lt_one]
    have hx_le_s : x ≤ s := by
      have hx_nonneg : 0 ≤ x := by linarith [hx.1]
      nlinarith [hs_sq, Real.sqrt_nonneg (1 - x ^ 2)]
    have hs_plus_x_pos : 0 < s + x := by positivity
    have hs_plus_x_nonneg : 0 ≤ s + x := hs_plus_x_pos.le
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact div_nonneg (sub_nonneg.mpr hx_le_s) hs_plus_x_nonneg
    have harctan_le : Real.arctan q ≤ q := by
      have harctan_nonneg : 0 ≤ Real.arctan q := Real.arctan_nonneg.mpr hq_nonneg
      have harctan_lt : Real.arctan q < Real.pi / 2 := Real.arctan_lt_pi_div_two q
      have htan := Real.le_tan harctan_nonneg harctan_lt
      simpa using htan
    have harcsin : Real.arcsin x = Real.pi / 4 - Real.arctan q := by
      have hx_Ioo : x ∈ Set.Ioo (-(1 : ℝ)) 1 := by
        constructor
        · linarith [hx.1]
        · exact hx_lt_one
      have harcsin_arctan := Real.arcsin_eq_arctan hx_Ioo
      have hsqrt : Real.sqrt (1 - x ^ 2) = s := rfl
      have hratio : x / s = (1 - q) / (1 + q) := by
        dsimp [q]
        field_simp [ne_of_gt hs_pos, ne_of_gt hs_plus_x_pos]
        nlinarith [hs_sq]
      have hq_lt_one : q < 1 := by
        dsimp [q]
        refine (div_lt_one hs_plus_x_pos).2 ?_
        nlinarith [hx.1]
      have hnegq_mul_one_lt : (-q) * 1 < 1 := by
        nlinarith
      have hadd := Real.arctan_add (x := -q) (y := 1) hnegq_mul_one_lt
      rw [Real.arctan_one, Real.arctan_neg] at hadd
      calc
        Real.arcsin x = Real.arctan (x / s) := by
          rw [harcsin_arctan, hsqrt]
        _ = Real.arctan ((1 - q) / (1 + q)) := congrArg Real.arctan hratio
        _ = -Real.arctan q + Real.pi / 4 := by
          simpa [sub_eq_add_neg, add_comm] using hadd.symm
        _ = Real.pi / 4 - Real.arctan q := by ring
    have hsqrt_two_lt : Real.sqrt 2 / 2 < (442 : ℝ) / 625 := by
      nlinarith
    have hx_poly : x ∈ Set.Icc ((1 : ℝ) / 2) (442 / 625) :=
      ⟨hx.1, hx_central.trans_lt hsqrt_two_lt |>.le⟩
    have hpoly := gwArccosCentralPolynomial_pos hx_poly
    have hA_pos : 0 < A := by
      dsimp [A]
      nlinarith [hx.2]
    have hp_pos : 0 < p := by norm_num [p]
    have hp_lt_pi : p < Real.pi := by
      have hpi_lower := Real.pi_gt_d6
      norm_num [p] at hpi_lower ⊢
      exact hpi_lower
    have hpA_lt_one : p * A < 1 := by
      dsimp [p, A]
      nlinarith [hx.1]
    have hright_pos : 0 < (1 + p * A) * x := by
      exact mul_pos (by nlinarith [hp_pos, hA_pos]) hx_pos
    have hleft_nonneg : 0 ≤ (1 - p * A) * s := by
      exact mul_nonneg (by linarith) hs_pos.le
    have hsquare_lt : ((1 - p * A) * s) ^ 2 < ((1 + p * A) * x) ^ 2 := by
      have hpoly' :
          0 < (1 + p * A) ^ 2 * x ^ 2 - (1 - p * A) ^ 2 * (1 - x ^ 2) := by
        simpa [p, A] using hpoly
      nlinarith [hs_sq]
    have hratio_lt : q < p * A := by
      have hlinear : (1 - p * A) * s < (1 + p * A) * x := by
        exact (sq_lt_sq₀ hleft_nonneg hright_pos.le).mp hsquare_lt
      dsimp [q]
      refine (div_lt_iff₀ hs_plus_x_pos).2 ?_
      nlinarith
    have harctan_lt_piA : Real.arctan q < Real.pi * A := by
      have hpA_lt_piA : p * A < Real.pi * A :=
        mul_lt_mul_of_pos_right hp_lt_pi hA_pos
      exact harctan_le.trans_lt (hratio_lt.trans hpA_lt_piA)
    have harccos_neg : Real.arccos (-x) = Real.pi / 2 + Real.arcsin x := by
      rw [Real.arccos, Real.arcsin_neg]
      ring
    have hcentral :
        ((87856 : ℝ) / 100000) * ((1 + x) / 2) < Real.arccos (-x) / Real.pi := by
      rw [harccos_neg, harcsin]
      have hpi_pos := Real.pi_pos
      dsimp [A] at harctan_lt_piA
      refine (lt_div_iff₀ hpi_pos).2 ?_
      nlinarith
    simpa [x] using hcentral
  · exact gwArccosFarLeftIntervalStrictBaseBound ht (by simpa [x] using lt_of_not_ge hx_central)

/-- Helper for Theorem 10.3: the textbook constant `0.87856` already satisfies the scalar
Goemans-Williamson inequality pointwise on `[-1, 1)`. -/
-- Route correction: the old closed-interval strict statement was false at `t = 1`.
-- Assemble the corrected statement from the cosine chord and the two negative subintervals.
lemma gwArccosStrictBaseBound :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, t ≠ 1 →
      ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
        Real.arccos t / Real.pi := by
  intro t ht ht_ne_one
  by_cases ht_nonneg : 0 ≤ t
  · have hθ : Real.arccos t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      constructor
      · exact Real.arccos_nonneg t
      · exact (Real.arccos_le_pi_div_two).2 ht_nonneg
    have hcos :
        1 - 2 * Real.arccos t / Real.pi ≤ t := by
      -- On the nonnegative half-interval, the basic cosine chord already gives coefficient `1`.
      simpa [Real.cos_arccos ht.1 ht.2] using
        (cos_ge_one_sub_two_mul_div_pi (θ := Real.arccos t) hθ)
    have hgap_le : (1 - t) / 2 ≤ Real.arccos t / Real.pi := by
      have hstep : 1 - t ≤ 2 * (Real.arccos t / Real.pi) := by
        have htmp := sub_le_sub_left hcos 1
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
      exact (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
        (by simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hstep)
    have hgap_pos : 0 < (1 - t) / 2 := by
      have ht_lt_one : t < 1 := lt_of_le_of_ne ht.2 ht_ne_one
      nlinarith
    have hconst : ((87856 : ℝ) / 100000) < 1 := by norm_num
    calc
      ((87856 : ℝ) / 100000) * ((1 - t) / 2) < (1 : ℝ) * ((1 - t) / 2) := by
        simpa using mul_lt_mul_of_pos_right hconst hgap_pos
      _ = (1 - t) / 2 := by ring
      _ ≤ Real.arccos t / Real.pi := hgap_le
  · have ht_mid_or_left :
        t ∈ Set.Icc (-1 : ℝ) (-(1 : ℝ) / 2) ∨
          t ∈ Set.Icc (-(1 : ℝ) / 2) 0 := by
      by_cases ht_left : t ≤ -(1 : ℝ) / 2
      · exact Or.inl ⟨ht.1, ht_left⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
    rcases ht_mid_or_left with ht_left | ht_mid
    · exact gwArccosLeftIntervalStrictBaseBound ht_left
    · exact gwArccosMiddleNegativeStrictBaseBound ht_mid

-- Compactness on the negative half-interval upgrades the strict pointwise estimate to a
-- uniform positive gap; the cosine chord supplies the nonnegative half-interval.
lemma gwArccosGap_pos :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        (((87856 : ℝ) / 100000) + ε) * ((1 - t) / 2) ≤
          Real.arccos t / Real.pi := by
  let gap : ℝ → ℝ := fun t ↦
    Real.arccos t / Real.pi -
      ((87856 : ℝ) / 100000) * ((1 - t) / 2)
  have hgap_cont : ContinuousOn gap (Set.Icc (-1 : ℝ) 0) := by
    -- The left-half compactness argument only needs continuity of the scalar gap function.
    have hbase : Continuous fun t : ℝ =>
        ((87856 : ℝ) / 100000) * ((1 - t) / 2) := by
      exact continuous_const.mul ((continuous_const.sub continuous_id).div_const (2 : ℝ))
    exact ((Real.continuous_arccos.div_const Real.pi).sub hbase).continuousOn
  obtain ⟨t₀, ht₀, hmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 0)).exists_isMinOn
      ⟨0, by norm_num, by norm_num⟩ hgap_cont
  have hgap_min_pos : 0 < gap t₀ := by
    -- The compact minimum is positive because the strict left-half bound already holds everywhere.
    have ht₀_ne_one : t₀ ≠ 1 := by
      linarith [ht₀.2]
    have hstrict := gwArccosStrictBaseBound t₀ ⟨ht₀.1, by linarith [ht₀.2]⟩ ht₀_ne_one
    simpa [gap] using hstrict
  let ε : ℝ := min (gap t₀) (1 - (87856 : ℝ) / 100000)
  have hε_pos : 0 < ε := by
    have hconst : 0 < 1 - (87856 : ℝ) / 100000 := by norm_num
    exact lt_min hgap_min_pos hconst
  refine ⟨ε, ?_, ?_⟩
  · exact hε_pos
  · intro t ht
    by_cases ht_nonneg : 0 ≤ t
    · have hgap_le : (1 - t) / 2 ≤ Real.arccos t / Real.pi := by
        have hθ : Real.arccos t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
          constructor
          · exact Real.arccos_nonneg t
          · exact (Real.arccos_le_pi_div_two).2 ht_nonneg
        have hcos :
            1 - 2 * Real.arccos t / Real.pi ≤ t := by
          -- The nonnegative interval keeps the stronger coefficient `1`.
          simpa [Real.cos_arccos ht.1 ht.2] using
            (cos_ge_one_sub_two_mul_div_pi (θ := Real.arccos t) hθ)
        have hstep : 1 - t ≤ 2 * (Real.arccos t / Real.pi) := by
          have htmp := sub_le_sub_left hcos 1
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
        exact (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
          (by simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hstep)
      have hε_le : ε ≤ 1 - (87856 : ℝ) / 100000 := min_le_right _ _
      have hcoeff_le : (87856 : ℝ) / 100000 + ε ≤ 1 := by
        linarith
      have hgap_nonneg : 0 ≤ (1 - t) / 2 := by
        nlinarith [ht.2]
      calc
        (((87856 : ℝ) / 100000) + ε) * ((1 - t) / 2) ≤
            (1 : ℝ) * ((1 - t) / 2) := by
          exact mul_le_mul_of_nonneg_right hcoeff_le hgap_nonneg
        _ = (1 - t) / 2 := by ring
        _ ≤ Real.arccos t / Real.pi := hgap_le
    · have ht_left : t ∈ Set.Icc (-1 : ℝ) 0 := ⟨ht.1, by linarith⟩
      have hmin_le : gap t₀ ≤ gap t := isMinOn_iff.mp hmin t ht_left
      have hε_le_gap : ε ≤ gap t := le_trans (min_le_left _ _) hmin_le
      have hgap_nonneg : 0 ≤ (1 - t) / 2 := by
        nlinarith
      have hgap_le_one : (1 - t) / 2 ≤ 1 := by
        nlinarith [ht_left.1, ht_left.2]
      have hε_mul :
          ε * ((1 - t) / 2) ≤ gap t := by
        calc
          ε * ((1 - t) / 2) ≤ ε * 1 := by
            exact mul_le_mul_of_nonneg_left hgap_le_one hε_pos.le
          _ = ε := by ring
          _ ≤ gap t := hε_le_gap
      have hmain :
          (((87856 : ℝ) / 100000) + ε) * ((1 - t) / 2) ≤
            Real.arccos t / Real.pi := by
        have hsplit :
            (((87856 : ℝ) / 100000) + ε) * ((1 - t) / 2) =
              ((87856 : ℝ) / 100000) * ((1 - t) / 2) + ε * ((1 - t) / 2) := by
          ring
        rw [hsplit]
        have hgap_def :
            ((87856 : ℝ) / 100000) * ((1 - t) / 2) + gap t =
              Real.arccos t / Real.pi := by
          simp [gap]
        linarith
      exact hmain

/-- Helper for Theorem 10.3: the remaining source-facing ingredient is a strict pointwise
approximation factor coming from the Goemans-Williamson rounding argument. -/
lemma existsStrictApproximationFactorForGoemansWilliamsonObjective
    (w : Sym2 (Fin n) → ℝ)
    (h_nonneg : ∀ e, 0 ≤ w e) :
    ∃ β : ℝ,
      (87856 : ℝ) / 100000 < β ∧
        ∀ {X : Matrix (Fin n) (Fin n) ℝ}, goemans_williamson_feasible X →
          β * goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X ≤
            max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
  -- Route correction: the averaging layer is now separated from the geometric and scalar frontiers.
  -- This proof only assembles the already established Gram bridge and objective normalization with
  -- the two remaining source-facing ingredients `weightedArccosSum_le_maxCutIntegerValue...` and
  -- `gwArccosGap_pos`.
  rcases gwArccosGap_pos with ⟨ε, hε_pos, hGap⟩
  let β : ℝ := (87856 : ℝ) / 100000 + ε
  refine ⟨β, ?_, ?_⟩
  · -- The positive gap supplies a strict improvement over the textbook constant.
    dsimp [β]
    linarith
  · intro X hX
    rcases existsUnitVectorFamilyOfGoemansWilliamsonFeasible (n := n) hX with ⟨U, hDot, hUnit⟩
    let gapTerm : Sym2 (Fin n) → ℝ :=
      Sym2.lift
        ⟨fun i j : Fin n ↦ (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2, by
            intro i j
            simp [dotProduct_comm]
        ⟩
    let arccosTerm : Sym2 (Fin n) → ℝ :=
      Sym2.lift
        ⟨fun i j : Fin n ↦
            Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
              intro i j
              simp [dotProduct_comm]
        ⟩
    have hObj :
        goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X =
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e * gapTerm e := by
      -- Re-express the SDP objective using the Gram columns of the feasible witness.
      simpa [gapTerm] using goemansWilliamsonObjective_eq_sum_dotGap (n := n) w hDot
    have hArccos :
        (Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e * arccosTerm e) ≤
          max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
      -- The geometric rounding package should bound the weighted `arccos` sum by `z_I`.
      simpa [arccosTerm] using
        weightedArccosSum_le_maxCutIntegerValue_of_unitColumnFamily (n := n) w U hUnit
    have hCompare :
        β * goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X ≤
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e * arccosTerm e := by
      -- Apply the scalar gap edgewise and sum against the nonnegative weights.
      rw [hObj]
      calc
        β * Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset (fun e ↦ w e * gapTerm e) =
            Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦ β * (w e * gapTerm e) := by
              rw [Finset.mul_sum]
        _ = Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦ w e * (β * gapTerm e) := by
              refine Finset.sum_congr rfl ?_
              intro e _
              ring
        _ ≤ Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦ w e * arccosTerm e := by
              refine Finset.sum_le_sum ?_
              intro e _
              refine Sym2.ind ?_ e
              intro i j
              have hDotMem :
                  dotProduct (fun k ↦ U k i) (fun k ↦ U k j) ∈ Set.Icc (-1 : ℝ) 1 :=
                goemansWilliamsonDot_mem_Icc_of_unitColumnFamily (n := n) hX hDot i j
              have hScalar :
                  β * ((1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2) ≤
                    Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi := by
                simpa [β] using hGap
                  (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) hDotMem
              have hw : 0 ≤ w s(i, j) := h_nonneg _
              -- Push the scalar comparison through the edge weight.
              simpa [gapTerm, arccosTerm, β, mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hScalar hw
    exact hCompare.trans hArccos

/-- Canonical `Sym2`-weight companion for Theorem 10.3. The source-facing matrix formulation is
`goemans_williamson_max_cut_ratio_gt`, and this theorem is the direct reusable bridge to the
repository's `SimpleGraph`/`Sym2` max-cut API. -/
theorem goemans_williamson_max_cut_ratio_gt_of_sym2_nonneg
    (w : Sym2 (Fin n) → ℝ)
    (h_nonneg : ∀ e, 0 ≤ w e)
    (hsdp_pos : 0 < goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w) :
    max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w /
        goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w >
      (87856 : ℝ) / 100000 := by
  -- Reduce the theorem to the missing pointwise rounding estimate from the source proof.
  rcases existsStrictApproximationFactorForGoemansWilliamsonObjective
      (n := n) w h_nonneg with ⟨β, hβ, hScaled⟩
  exact goemansWilliamsonRatioLowerBound_of_pointwiseApprox
    (n := n) w hβ (fun {X} hX ↦ hScaled hX) hsdp_pos

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap10/section_10_2/ch10_sec10_2_1_theorem_10_3.lean.
Theorem 10.3 (Goemans and Williamson [173]). For a symmetric nonnegative complete-graph weight
matrix `w`, if the Goemans-Williamson optimum of the induced unordered-edge weight
`Matrix.toSym2Weight w` is positive, then the ratio of the integer optimum `z_I` to the
semidefinite optimum `z_sdp` is strictly larger than `0.87856`. The companion bridge
`goemans_williamson_max_cut_ratio_gt_of_sym2_nonneg` is the reusable `Sym2`-indexed form, and
`Matrix.toSym2Weight_apply_of_isSymm` identifies the bridge weight with the original matrix
entries on graph edges. -/
theorem goemans_williamson_max_cut_ratio_gt
    (w : Matrix (Fin n) (Fin n) ℝ)
    (h_symm : w.IsSymm)
    (h_nonneg : ∀ i j, 0 ≤ w i j)
    (hsdp_pos :
      0 < goemans_williamson_value (⊤ : SimpleGraph (Fin n)) (Matrix.toSym2Weight w)) :
    max_cut_integer_value (⊤ : SimpleGraph (Fin n)) (Matrix.toSym2Weight w) /
        goemans_williamson_value (⊤ : SimpleGraph (Fin n)) (Matrix.toSym2Weight w) >
      (87856 : ℝ) / 100000 := by
  exact goemans_williamson_max_cut_ratio_gt_of_sym2_nonneg
    (Matrix.toSym2Weight w) (Matrix.toSym2Weight_nonneg_of_isSymm w h_symm h_nonneg) hsdp_pos

end Theorem103
