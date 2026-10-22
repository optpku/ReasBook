/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped StandardSimplex

section

variable (m : ℕ+)

local notation "E" => EuclideanSpace ℝ (Fin (m : ℕ))

/- Lemma 6.4 lies in the finite simplex / entropy-smoothing domain.

Sampled owner declarations:
* `normalizedEntropyProxFunction` and `normalizedEntropyProxFunction_apply` in
  `Chap06/Definition_6_14`;
* `η` and `eta_apply` via the recall surface in `Chap06/Definition_6_27`;
* `smoothMaximand` in `Chap06/Definition_6_20`;
* `smoothedDualObjectiveMinimand` in `Chap06/Definition_6_32`.

Best owner abstraction:
* source-facing: the entropy-regularized simplex objective and its canonical softmax maximizer for
  a positive temperature parameter;
* core/canonical: the simplex owner `Δ[m]`, the entropy owner `normalizedEntropyProxFunction`, the
  positive smoothing-parameter owner `{μ : ℝ // 0 < μ}`, and `η`;
* bridge/view: the coordinate formulas for the objective and the softmax point.

Primitive data:
* the simplex dimension `m : ℕ+`;
* the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
* the score vector `s : EuclideanSpace ℝ (Fin (m : ℕ))`.

Derived API:
* the pointwise objective expansion;
* the softmax denominator and its positivity;
* the simplex-membership and coordinate formulas for the canonical softmax point;
* the maximality and value characterizations.

Source/core/bridge triage:
* source-facing: `entropyRegularizedSimplexObjective` and `entropySimplexSoftmax`;
* core/canonical: `Δ[m]`, `normalizedEntropyProxFunction`, `{μ : ℝ // 0 < μ}`, and
  `η`;
* bridge/view: the coordinate expansion lemmas in this file.
-/

/-- The entropy-regularized linear functional on the standard simplex `Δ_m` for a positive
smoothing parameter `μ`. The entropy term is carried by the canonical prox owner
`normalizedEntropyProxFunction`; the convention `0 \log 0 = 0` is realized by `Real.log 0 = 0`. -/
def entropyRegularizedSimplexObjective (μ : {μ : ℝ // 0 < μ}) (s : E) : Δ[m] → ℝ :=
  fun u ↦
    ∑ j : Fin (m : ℕ), u j * s j -
      (μ : ℝ) * normalizedEntropyProxFunction m u + (μ : ℝ) * Real.log (m : ℝ)

-- Proof sketch: unfold `entropyRegularizedSimplexObjective`.
/-- Evaluating `entropyRegularizedSimplexObjective m μ s` gives the coordinate formula
`∑_j u_j s_j - μ ∑_j u_j log u_j`. -/
theorem entropyRegularizedSimplexObjective_apply (μ : {μ : ℝ // 0 < μ}) (s : E) (u : Δ[m]) :
    entropyRegularizedSimplexObjective m μ s u =
      ∑ j : Fin (m : ℕ), u j * s j - (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (u j) := by
  rw [entropyRegularizedSimplexObjective, normalizedEntropyProxFunction_apply]
  ring

/-- The exponential denominator appearing in the positive-temperature softmax formula. -/
def entropySimplexSoftmaxDenominator (μ : {μ : ℝ // 0 < μ}) (s : E) : ℝ :=
  ∑ i : Fin (m : ℕ), Real.exp (s i / (μ : ℝ))

-- Proof sketch: every summand `Real.exp (s i / μ)` is strictly positive, and the finite index type
-- `Fin (m : ℕ)` is nonempty because `m : ℕ+`.
/-- The softmax denominator is strictly positive. -/
theorem entropySimplexSoftmaxDenominator_pos (μ : {μ : ℝ // 0 < μ}) (s : E) :
    0 < entropySimplexSoftmaxDenominator m μ s := by
  -- Reuse the chapter's log-sum-exp positivity owner for the same exponential denominator.
  simpa [entropySimplexSoftmaxDenominator] using
    (eta_sum_exp_pos (m := (m : ℕ)) (μ := μ) (x := s))

-- Proof sketch: each coordinate of the displayed function is nonnegative because `Real.exp` is
-- positive, and the normalization by the denominator makes the coordinate sum equal to `1`.
/-- The normalized exponential weights define a point of the standard simplex. -/
theorem entropySimplexSoftmax_mem_stdSimplex (μ : {μ : ℝ // 0 < μ}) (s : E) :
    (fun j : Fin (m : ℕ) ↦
      Real.exp (s j / (μ : ℝ)) / entropySimplexSoftmaxDenominator m μ s) ∈
        Δ[m] := by
  refine ⟨?_, ?_⟩
  · -- Every normalized exponential weight is nonnegative.
    intro j
    exact div_nonneg (Real.exp_nonneg _) <|
      le_of_lt (entropySimplexSoftmaxDenominator_pos (m := m) μ s)
  · -- The denominator is exactly the coordinate sum, so the weights add up to `1`.
    rw [← Finset.sum_div, entropySimplexSoftmaxDenominator]
    exact div_self (entropySimplexSoftmaxDenominator_pos (m := m) μ s).ne'

/-- The canonical softmax point in `Δ_m` associated to `s` and the positive smoothing parameter
`μ`. -/
def entropySimplexSoftmax (μ : {μ : ℝ // 0 < μ}) (s : E) : Δ[m] :=
  ⟨fun j : Fin (m : ℕ) ↦
      Real.exp (s j / (μ : ℝ)) / entropySimplexSoftmaxDenominator m μ s,
    entropySimplexSoftmax_mem_stdSimplex m μ s⟩

-- Proof sketch: unfold `entropySimplexSoftmax`.
/-- The coordinates of `entropySimplexSoftmax m μ s` are the normalized exponentials
`exp (s_j / μ) / \sum_i exp (s_i / μ)`. -/
theorem entropySimplexSoftmax_apply (μ : {μ : ℝ // 0 < μ}) (s : E) (j : Fin (m : ℕ)) :
    entropySimplexSoftmax m μ s j =
      Real.exp (s j / (μ : ℝ)) / entropySimplexSoftmaxDenominator m μ s := rfl

/-- Helper for Lemma 6.4: every coordinate of the simplex softmax point is strictly positive. -/
theorem entropySimplexSoftmax_pos
    (μ : {μ : ℝ // 0 < μ}) (s : E) (j : Fin (m : ℕ)) :
    0 < entropySimplexSoftmax m μ s j := by
  -- The numerator is a positive exponential, and the denominator is positive as well.
  rw [entropySimplexSoftmax_apply]
  exact div_pos (Real.exp_pos _) (entropySimplexSoftmaxDenominator_pos (m := m) μ s)

/-- Helper for Lemma 6.4: the gap from the log-sum-exp value to the entropy-regularized simplex
objective is the softmax-weighted Kullback-Leibler sum. -/
theorem eta_sub_entropyRegularizedSimplexObjective_eq_softmax_weighted_kl
    (μ : {μ : ℝ // 0 < μ}) (s : E) (u : Δ[m]) :
    η μ s - entropyRegularizedSimplexObjective m μ s u =
      (μ : ℝ) * ∑ j : Fin (m : ℕ), entropySimplexSoftmax m μ s j *
        InformationTheory.klFun (u j / entropySimplexSoftmax m μ s j) := by
  let p : Δ[m] := entropySimplexSoftmax m μ s
  let Z : ℝ := entropySimplexSoftmaxDenominator m μ s
  have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt μ.property
  have hsum_p : ∑ j : Fin (m : ℕ), p j = 1 := stdSimplex.sum_eq_one p
  have hsum_u : ∑ j : Fin (m : ℕ), u j = 1 := stdSimplex.sum_eq_one u
  have hp : ∀ j : Fin (m : ℕ), 0 < p j := by
    -- This is the positivity bridge needed for divisions and logarithms.
    intro j
    simpa [p] using entropySimplexSoftmax_pos (m := m) μ s j
  have hweighted_kl :
      (μ : ℝ) * ∑ j : Fin (m : ℕ), p j * InformationTheory.klFun (u j / p j) =
        (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (u j / p j) := by
    have hsplit :
        ∑ j : Fin (m : ℕ), (u j * Real.log (u j / p j) + p j - u j) =
          ∑ j : Fin (m : ℕ), u j * Real.log (u j / p j) +
            ∑ j : Fin (m : ℕ), p j - ∑ j : Fin (m : ℕ), u j := by
      -- Split the weighted KL sum into the logarithmic part and the affine correction.
      calc
        ∑ j : Fin (m : ℕ), (u j * Real.log (u j / p j) + p j - u j)
            = ∑ j : Fin (m : ℕ), (u j * Real.log (u j / p j) + (p j - u j)) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                ring
        _ = (∑ j : Fin (m : ℕ), u j * Real.log (u j / p j)) +
              ∑ j : Fin (m : ℕ), (p j - u j) := by
              rw [Finset.sum_add_distrib]
        _ = ∑ j : Fin (m : ℕ), u j * Real.log (u j / p j) +
              ∑ j : Fin (m : ℕ), p j - ∑ j : Fin (m : ℕ), u j := by
              rw [Finset.sum_sub_distrib]
              ring
    -- Expand `klFun` and cancel the simplex affine terms using the sum-to-one constraints.
    calc
      (μ : ℝ) * ∑ j : Fin (m : ℕ), p j * InformationTheory.klFun (u j / p j)
          = (μ : ℝ) * ∑ j : Fin (m : ℕ), (u j * Real.log (u j / p j) + p j - u j) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [InformationTheory.klFun_apply]
              have hp_ne : p j ≠ 0 := (hp j).ne'
              field_simp [hp_ne]
      _ = (μ : ℝ) * (∑ j : Fin (m : ℕ), u j * Real.log (u j / p j) +
            ∑ j : Fin (m : ℕ), p j - ∑ j : Fin (m : ℕ), u j) := by
            rw [hsplit]
      _ = (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (u j / p j) := by
            rw [hsum_p, hsum_u]
            ring
  have hlog_ratio :
      ∀ j : Fin (m : ℕ),
        u j * Real.log (u j / p j) = u j * Real.log (u j) - u j * Real.log (p j) := by
    -- Move the logarithm of the quotient into a difference of logarithms.
    intro j
    by_cases huj : u j = 0
    · simp [huj]
    · rw [Real.log_div huj (hp j).ne']
      ring
  have hratio_sum :
      ∑ j : Fin (m : ℕ), u j * Real.log (u j / p j) =
        ∑ j : Fin (m : ℕ), u j * Real.log (u j) -
          ∑ j : Fin (m : ℕ), u j * Real.log (p j) := by
    -- Summing the pointwise quotient identity isolates the entropy term and the softmax term.
    calc
      ∑ j : Fin (m : ℕ), u j * Real.log (u j / p j)
          = ∑ j : Fin (m : ℕ), (u j * Real.log (u j) - u j * Real.log (p j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              exact hlog_ratio j
      _ = ∑ j : Fin (m : ℕ), u j * Real.log (u j) -
            ∑ j : Fin (m : ℕ), u j * Real.log (p j) := by
            rw [Finset.sum_sub_distrib]
  have hlog_p :
      ∀ j : Fin (m : ℕ), Real.log (p j) = s j / (μ : ℝ) - Real.log Z := by
    -- The softmax logarithm is the score divided by `μ` minus the log denominator.
    intro j
    dsimp [p, Z]
    rw [entropySimplexSoftmax_apply]
    rw [Real.log_div (Real.exp_pos _).ne'
      (entropySimplexSoftmaxDenominator_pos (m := m) μ s).ne']
    rw [Real.log_exp]
  have hscaled_sum :
      (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * (s j / (μ : ℝ)) =
        ∑ j : Fin (m : ℕ), u j * s j := by
    -- Multiplying by `μ` clears the softmax scaling factor.
    calc
      (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * (s j / (μ : ℝ))
          = ∑ j : Fin (m : ℕ), (μ : ℝ) * (u j * (s j / (μ : ℝ))) := by
              rw [Finset.mul_sum]
      _ = ∑ j : Fin (m : ℕ), u j * s j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            field_simp [hμ_ne]
  have hconst_sum :
      ∑ j : Fin (m : ℕ), u j * Real.log Z =
        Real.log Z * ∑ j : Fin (m : ℕ), u j := by
    -- The denominator log is a constant across the finite sum.
    calc
      ∑ j : Fin (m : ℕ), u j * Real.log Z
          = ∑ j : Fin (m : ℕ), Real.log Z * u j := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = Real.log Z * ∑ j : Fin (m : ℕ), u j := by
            rw [Finset.mul_sum]
  have hsum_log_p :
      (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (p j) =
        ∑ j : Fin (m : ℕ), u j * s j - (μ : ℝ) * Real.log Z := by
    -- Substitute the explicit logarithm of the softmax coordinates and simplify.
    calc
      (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (p j)
          = (μ : ℝ) * ∑ j : Fin (m : ℕ), (u j * (s j / (μ : ℝ)) - u j * Real.log Z) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [hlog_p j]
              ring
      _ = (μ : ℝ) * (∑ j : Fin (m : ℕ), u j * (s j / (μ : ℝ)) -
            ∑ j : Fin (m : ℕ), u j * Real.log Z) := by
            rw [Finset.sum_sub_distrib]
      _ = (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * (s j / (μ : ℝ)) -
            (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log Z := by
            ring
      _ = ∑ j : Fin (m : ℕ), u j * s j -
            (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log Z := by
            rw [hscaled_sum]
      _ = ∑ j : Fin (m : ℕ), u j * s j -
            (μ : ℝ) * (Real.log Z * ∑ j : Fin (m : ℕ), u j) := by
            rw [hconst_sum]
      _ = ∑ j : Fin (m : ℕ), u j * s j - (μ : ℝ) * Real.log Z := by
            rw [hsum_u]
            ring
  have hratio_gap :
      (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (u j / p j) =
        η μ s - entropyRegularizedSimplexObjective m μ s u := by
    -- Replace the softmax logarithm by the score data and compare with the objective formula.
    calc
      (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (u j / p j)
          = (μ : ℝ) * (∑ j : Fin (m : ℕ), u j * Real.log (u j) -
              ∑ j : Fin (m : ℕ), u j * Real.log (p j)) := by
              rw [hratio_sum]
      _ = (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (u j) -
            (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (p j) := by
            ring
      _ = (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (u j) -
            (∑ j : Fin (m : ℕ), u j * s j - (μ : ℝ) * Real.log Z) := by
            rw [hsum_log_p]
      _ = η μ s - entropyRegularizedSimplexObjective m μ s u := by
            rw [eta_apply, entropyRegularizedSimplexObjective_apply]
            simp [Z, entropySimplexSoftmaxDenominator, div_eq_mul_inv]
            ring
  -- Combine the quotient rewrite with the weighted-KL expansion to obtain the source identity.
  calc
    η μ s - entropyRegularizedSimplexObjective m μ s u
        = (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (u j / p j) := by
            rw [← hratio_gap]
    _ = (μ : ℝ) * ∑ j : Fin (m : ℕ), p j * InformationTheory.klFun (u j / p j) := by
          rw [hweighted_kl]
    _ = (μ : ℝ) * ∑ j : Fin (m : ℕ), entropySimplexSoftmax m μ s j *
          InformationTheory.klFun (u j / entropySimplexSoftmax m μ s j) := by
          rfl

/-- Helper for Lemma 6.4: the softmax-weighted Kullback-Leibler sum vanishes exactly at the
softmax point. -/
theorem softmax_weighted_kl_eq_zero_iff
    (μ : {μ : ℝ // 0 < μ}) (s : E) (u : Δ[m]) :
    (∑ j : Fin (m : ℕ), entropySimplexSoftmax m μ s j *
        InformationTheory.klFun (u j / entropySimplexSoftmax m μ s j) = 0) ↔
      u = entropySimplexSoftmax m μ s := by
  let p : Δ[m] := entropySimplexSoftmax m μ s
  have hp : ∀ j : Fin (m : ℕ), 0 < p j := by
    -- The simplex softmax is strictly positive coordinatewise.
    intro j
    simpa [p] using entropySimplexSoftmax_pos (m := m) μ s j
  constructor
  · intro hsum
    apply Subtype.ext
    funext j
    have hnonneg :
        ∀ i ∈ Finset.univ, 0 ≤ p i * InformationTheory.klFun (u i / p i) := by
      -- Every KL term is nonnegative, and the weights are positive.
      intro i hi
      refine mul_nonneg (le_of_lt (hp i)) ?_
      refine InformationTheory.klFun_nonneg ?_
      exact div_nonneg (stdSimplex.zero_le u i) (le_of_lt (hp i))
    have hterm : p j * InformationTheory.klFun (u j / p j) = 0 := by
      -- A sum of nonnegative terms can be zero only if each summand is zero.
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum j (Finset.mem_univ j)
    have hkl : InformationTheory.klFun (u j / p j) = 0 := by
      exact (mul_eq_zero.mp hterm).resolve_left (hp j).ne'
    have hratio : u j / p j = 1 := by
      refine (InformationTheory.klFun_eq_zero_iff ?_).1 hkl
      exact div_nonneg (stdSimplex.zero_le u j) (le_of_lt (hp j))
    have hp_ne : p j ≠ 0 := (hp j).ne'
    -- Multiply the ratio identity back by `p j` to recover equality of coordinates.
    have hcoord := congrArg (fun t : ℝ ↦ t * p j) hratio
    simpa [hp_ne] using hcoord
  · intro hu
    subst hu
    -- At the softmax point every KL term is `klFun 1 = 0`.
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hpj_ne : p j ≠ 0 := (hp j).ne'
    simp [p, hpj_ne, InformationTheory.klFun_one]

-- Proof sketch: use strict concavity of `u ↦ ∑_j u_j s_j - μ ∑_j u_j log u_j` on the simplex,
-- derive the first-order optimality equations with the simplex constraint, and solve them to get
-- the normalized exponential formula.
/-- Lemma 6.4: a simplex point maximizes the entropy-regularized linear functional exactly when it
is the canonical softmax point `u_μ(s)`. -/
lemma entropyRegularizedSimplexObjective_isMaxOn_iff
    (μ : {μ : ℝ // 0 < μ}) (s : E) (u : Δ[m]) :
    IsMaxOn (entropyRegularizedSimplexObjective m μ s) Set.univ u ↔
      u = entropySimplexSoftmax m μ s := by
  let p : Δ[m] := entropySimplexSoftmax m μ s
  have hupper :
      ∀ v : Δ[m], entropyRegularizedSimplexObjective m μ s v ≤ η μ s := by
    intro v
    -- The KL decomposition gives a nonnegative gap between `η μ s` and the objective.
    have hgap_nonneg :
        0 ≤ η μ s - entropyRegularizedSimplexObjective m μ s v := by
      rw [eta_sub_entropyRegularizedSimplexObjective_eq_softmax_weighted_kl (m := m)
        (μ := μ) (s := s) (u := v)]
      refine mul_nonneg μ.property.le ?_
      refine Finset.sum_nonneg ?_
      intro j hj
      refine mul_nonneg (le_of_lt (entropySimplexSoftmax_pos (m := m) μ s j)) ?_
      refine InformationTheory.klFun_nonneg ?_
      exact div_nonneg (stdSimplex.zero_le v j) <|
        le_of_lt (entropySimplexSoftmax_pos (m := m) μ s j)
    linarith
  have hsoftmax_value :
      entropyRegularizedSimplexObjective m μ s p = η μ s := by
    -- Specializing the KL identity at the softmax point makes every term equal `klFun 1 = 0`.
    have hgap :
        η μ s - entropyRegularizedSimplexObjective m μ s p = 0 := by
      rw [eta_sub_entropyRegularizedSimplexObjective_eq_softmax_weighted_kl (m := m)
        (μ := μ) (s := s) (u := p)]
      have hsum_zero :
          ∑ j : Fin (m : ℕ), p j * InformationTheory.klFun (p j / p j) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        have hpj_ne : p j ≠ 0 := (entropySimplexSoftmax_pos (m := m) μ s j).ne'
        simp [p, hpj_ne, InformationTheory.klFun_one]
      have hsum_zero' :
          ∑ j : Fin (m : ℕ), entropySimplexSoftmax m μ s j *
            InformationTheory.klFun (p j / entropySimplexSoftmax m μ s j) = 0 := by
        simpa [p] using hsum_zero
      rw [hsum_zero']
      ring
    exact (sub_eq_zero.mp hgap).symm
  constructor
  · intro huMax
    rw [isMaxOn_iff] at huMax
    -- Compare the current maximizer with the softmax value and force equality in the KL gap.
    have hp_le : entropyRegularizedSimplexObjective m μ s p ≤
        entropyRegularizedSimplexObjective m μ s u :=
      huMax p (by simp)
    have hη_le :
        η μ s ≤ entropyRegularizedSimplexObjective m μ s u := by
      simpa [hsoftmax_value] using hp_le
    have hgap_zero :
        η μ s - entropyRegularizedSimplexObjective m μ s u = 0 := by
      linarith [hupper u, hη_le]
    rw [eta_sub_entropyRegularizedSimplexObjective_eq_softmax_weighted_kl (m := m)
      (μ := μ) (s := s) (u := u)] at hgap_zero
    have hsum_zero :
        ∑ j : Fin (m : ℕ), entropySimplexSoftmax m μ s j *
          InformationTheory.klFun (u j / entropySimplexSoftmax m μ s j) = 0 := by
      exact (mul_eq_zero.mp hgap_zero).resolve_left (show (μ : ℝ) ≠ 0 from ne_of_gt μ.property)
    simpa [p] using
      (softmax_weighted_kl_eq_zero_iff (m := m) (μ := μ) (s := s) (u := u)).1 hsum_zero
  · intro hu
    subst hu
    rw [isMaxOn_iff]
    intro v hv
    -- Every feasible point is bounded above by `η μ s`, and the softmax attains that value.
    calc
      entropyRegularizedSimplexObjective m μ s v ≤ η μ s := hupper v
      _ = entropyRegularizedSimplexObjective m μ s p := hsoftmax_value.symm
      _ = entropyRegularizedSimplexObjective m μ s (entropySimplexSoftmax m μ s) := by
            simp [p]

-- Proof sketch: substitute the explicit softmax coordinates into the entropy term, rewrite
-- `log u_j = s_j / μ - log (∑_i exp (s_i / μ))`, and simplify.
/-- The softmax maximizer attains the log-sum-exp value
`μ \log (\sum_i \exp (s_i / μ))`. -/
theorem entropyRegularizedSimplexObjective_softmax_eq_value
    (μ : {μ : ℝ // 0 < μ}) (s : E) :
    entropyRegularizedSimplexObjective m μ s (entropySimplexSoftmax m μ s) =
      η μ s := by
  let p : Δ[m] := entropySimplexSoftmax m μ s
  -- Specializing the KL decomposition at the softmax point collapses the whole gap to zero.
  have hgap :
      η μ s - entropyRegularizedSimplexObjective m μ s p = 0 := by
    rw [eta_sub_entropyRegularizedSimplexObjective_eq_softmax_weighted_kl (m := m)
      (μ := μ) (s := s) (u := p)]
    have hsum_zero :
        ∑ j : Fin (m : ℕ), p j * InformationTheory.klFun (p j / p j) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hpj_ne : p j ≠ 0 := (entropySimplexSoftmax_pos (m := m) μ s j).ne'
      simp [p, hpj_ne, InformationTheory.klFun_one]
    have hsum_zero' :
        ∑ j : Fin (m : ℕ), entropySimplexSoftmax m μ s j *
          InformationTheory.klFun (p j / entropySimplexSoftmax m μ s j) = 0 := by
      simpa [p] using hsum_zero
    rw [hsum_zero']
    ring
  simpa [p] using (sub_eq_zero.mp hgap).symm

end

end
